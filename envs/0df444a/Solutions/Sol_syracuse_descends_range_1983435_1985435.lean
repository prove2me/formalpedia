-- Prove2me | solution 1 for syracuse_descends_range_1983435_1985435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:16.037006+00:00
-- url     : https://prove2.me/submissions/152d1cc6-0edc-46a9-9e3c-0340b247cbc4

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

theorem B2231365 : Blo 1983435 2231365 := bbase (se 4 (by rfl) ⟨209190, by rfl⟩ : syracuseStep 2231365 = 418381) (by norm_num)
theorem B2975153 : Blo 1983435 2975153 := bstep (se 2 (by rfl) ⟨1115682, by rfl⟩ : syracuseStep 2975153 = 2231365) B2231365
theorem B1983435 : Blo 1983435 1983435 := bstep (se 1 (by rfl) ⟨1487576, by rfl⟩ : syracuseStep 1983435 = 2975153) B2975153
theorem B3765437 : Blo 1983435 3765437 := bbase (se 3 (by rfl) ⟨706019, by rfl⟩ : syracuseStep 3765437 = 1412039) (by norm_num)
theorem B2510291 : Blo 1983435 2510291 := bstep (se 1 (by rfl) ⟨1882718, by rfl⟩ : syracuseStep 2510291 = 3765437) B3765437
theorem B6694109 : Blo 1983435 6694109 := bstep (se 3 (by rfl) ⟨1255145, by rfl⟩ : syracuseStep 6694109 = 2510291) B2510291
theorem B4462739 : Blo 1983435 4462739 := bstep (se 1 (by rfl) ⟨3347054, by rfl⟩ : syracuseStep 4462739 = 6694109) B6694109
theorem B2975159 : Blo 1983435 2975159 := bstep (se 1 (by rfl) ⟨2231369, by rfl⟩ : syracuseStep 2975159 = 4462739) B4462739
theorem B1983439 : Blo 1983435 1983439 := bstep (se 1 (by rfl) ⟨1487579, by rfl⟩ : syracuseStep 1983439 = 2975159) B2975159
theorem B2975165 : Blo 1983435 2975165 := bbase (se 3 (by rfl) ⟨557843, by rfl⟩ : syracuseStep 2975165 = 1115687) (by norm_num)
theorem B1983443 : Blo 1983435 1983443 := bstep (se 1 (by rfl) ⟨1487582, by rfl⟩ : syracuseStep 1983443 = 2975165) B2975165
theorem B4462757 : Blo 1983435 4462757 := bbase (se 4 (by rfl) ⟨418383, by rfl⟩ : syracuseStep 4462757 = 836767) (by norm_num)
theorem B2975171 : Blo 1983435 2975171 := bstep (se 1 (by rfl) ⟨2231378, by rfl⟩ : syracuseStep 2975171 = 4462757) B4462757
theorem B1983447 : Blo 1983435 1983447 := bstep (se 1 (by rfl) ⟨1487585, by rfl⟩ : syracuseStep 1983447 = 2975171) B2975171
theorem B5020613 : Blo 1983435 5020613 := bbase (se 4 (by rfl) ⟨470682, by rfl⟩ : syracuseStep 5020613 = 941365) (by norm_num)
theorem B3347075 : Blo 1983435 3347075 := bstep (se 1 (by rfl) ⟨2510306, by rfl⟩ : syracuseStep 3347075 = 5020613) B5020613
theorem B2231383 : Blo 1983435 2231383 := bstep (se 1 (by rfl) ⟨1673537, by rfl⟩ : syracuseStep 2231383 = 3347075) B3347075
theorem B2975177 : Blo 1983435 2975177 := bstep (se 2 (by rfl) ⟨1115691, by rfl⟩ : syracuseStep 2975177 = 2231383) B2231383
theorem B1983451 : Blo 1983435 1983451 := bstep (se 1 (by rfl) ⟨1487588, by rfl⟩ : syracuseStep 1983451 = 2975177) B2975177
theorem B3574253 : Blo 1983435 3574253 := bbase (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) (by norm_num)
theorem B9531341 : Blo 1983435 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B6354227 : Blo 1983435 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B4236151 : Blo 1983435 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B5648201 : Blo 1983435 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B3765467 : Blo 1983435 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B10041245 : Blo 1983435 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B6694163 : Blo 1983435 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B4462775 : Blo 1983435 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B2975183 : Blo 1983435 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B1983455 : Blo 1983435 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B2975189 : Blo 1983435 2975189 := bbase (se 7 (by rfl) ⟨34865, by rfl⟩ : syracuseStep 2975189 = 69731) (by norm_num)
theorem B1983459 : Blo 1983435 1983459 := bstep (se 1 (by rfl) ⟨1487594, by rfl⟩ : syracuseStep 1983459 = 2975189) B2975189
theorem B7530965 : Blo 1983435 7530965 := bbase (se 7 (by rfl) ⟨88253, by rfl⟩ : syracuseStep 7530965 = 176507) (by norm_num)
theorem B5020643 : Blo 1983435 5020643 := bstep (se 1 (by rfl) ⟨3765482, by rfl⟩ : syracuseStep 5020643 = 7530965) B7530965
theorem B3347095 : Blo 1983435 3347095 := bstep (se 1 (by rfl) ⟨2510321, by rfl⟩ : syracuseStep 3347095 = 5020643) B5020643
theorem B4462793 : Blo 1983435 4462793 := bstep (se 2 (by rfl) ⟨1673547, by rfl⟩ : syracuseStep 4462793 = 3347095) B3347095
theorem B2975195 : Blo 1983435 2975195 := bstep (se 1 (by rfl) ⟨2231396, by rfl⟩ : syracuseStep 2975195 = 4462793) B4462793
theorem B1983463 : Blo 1983435 1983463 := bstep (se 1 (by rfl) ⟨1487597, by rfl⟩ : syracuseStep 1983463 = 2975195) B2975195
theorem B2231401 : Blo 1983435 2231401 := bbase (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) (by norm_num)
theorem B2975201 : Blo 1983435 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B1983467 : Blo 1983435 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B4765709 : Blo 1983435 4765709 := bbase (se 3 (by rfl) ⟨893570, by rfl⟩ : syracuseStep 4765709 = 1787141) (by norm_num)
theorem B3177139 : Blo 1983435 3177139 := bstep (se 1 (by rfl) ⟨2382854, by rfl⟩ : syracuseStep 3177139 = 4765709) B4765709
theorem B4236185 : Blo 1983435 4236185 := bstep (se 2 (by rfl) ⟨1588569, by rfl⟩ : syracuseStep 4236185 = 3177139) B3177139
theorem B11296493 : Blo 1983435 11296493 := bstep (se 3 (by rfl) ⟨2118092, by rfl⟩ : syracuseStep 11296493 = 4236185) B4236185
theorem B7530995 : Blo 1983435 7530995 := bstep (se 1 (by rfl) ⟨5648246, by rfl⟩ : syracuseStep 7530995 = 11296493) B11296493
theorem B5020663 : Blo 1983435 5020663 := bstep (se 1 (by rfl) ⟨3765497, by rfl⟩ : syracuseStep 5020663 = 7530995) B7530995
theorem B6694217 : Blo 1983435 6694217 := bstep (se 2 (by rfl) ⟨2510331, by rfl⟩ : syracuseStep 6694217 = 5020663) B5020663
theorem B4462811 : Blo 1983435 4462811 := bstep (se 1 (by rfl) ⟨3347108, by rfl⟩ : syracuseStep 4462811 = 6694217) B6694217
theorem B2975207 : Blo 1983435 2975207 := bstep (se 1 (by rfl) ⟨2231405, by rfl⟩ : syracuseStep 2975207 = 4462811) B4462811
theorem B1983471 : Blo 1983435 1983471 := bstep (se 1 (by rfl) ⟨1487603, by rfl⟩ : syracuseStep 1983471 = 2975207) B2975207
theorem B2975213 : Blo 1983435 2975213 := bbase (se 3 (by rfl) ⟨557852, by rfl⟩ : syracuseStep 2975213 = 1115705) (by norm_num)
theorem B1983475 : Blo 1983435 1983475 := bstep (se 1 (by rfl) ⟨1487606, by rfl⟩ : syracuseStep 1983475 = 2975213) B2975213
theorem B4462829 : Blo 1983435 4462829 := bbase (se 3 (by rfl) ⟨836780, by rfl⟩ : syracuseStep 4462829 = 1673561) (by norm_num)
theorem B2975219 : Blo 1983435 2975219 := bstep (se 1 (by rfl) ⟨2231414, by rfl⟩ : syracuseStep 2975219 = 4462829) B4462829
theorem B1983479 : Blo 1983435 1983479 := bstep (se 1 (by rfl) ⟨1487609, by rfl⟩ : syracuseStep 1983479 = 2975219) B2975219
theorem B2824141 : Blo 1983435 2824141 := bbase (se 3 (by rfl) ⟨529526, by rfl⟩ : syracuseStep 2824141 = 1059053) (by norm_num)
theorem B3765521 : Blo 1983435 3765521 := bstep (se 2 (by rfl) ⟨1412070, by rfl⟩ : syracuseStep 3765521 = 2824141) B2824141
theorem B2510347 : Blo 1983435 2510347 := bstep (se 1 (by rfl) ⟨1882760, by rfl⟩ : syracuseStep 2510347 = 3765521) B3765521
theorem B3347129 : Blo 1983435 3347129 := bstep (se 2 (by rfl) ⟨1255173, by rfl⟩ : syracuseStep 3347129 = 2510347) B2510347
theorem B2231419 : Blo 1983435 2231419 := bstep (se 1 (by rfl) ⟨1673564, by rfl⟩ : syracuseStep 2231419 = 3347129) B3347129
theorem B2975225 : Blo 1983435 2975225 := bstep (se 2 (by rfl) ⟨1115709, by rfl⟩ : syracuseStep 2975225 = 2231419) B2231419
theorem B1983483 : Blo 1983435 1983483 := bstep (se 1 (by rfl) ⟨1487612, by rfl⟩ : syracuseStep 1983483 = 2975225) B2975225
theorem B32168789 : Blo 1983435 32168789 := bbase (se 9 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 32168789 = 188489) (by norm_num)
theorem B21445859 : Blo 1983435 21445859 := bstep (se 1 (by rfl) ⟨16084394, by rfl⟩ : syracuseStep 21445859 = 32168789) B32168789
theorem B14297239 : Blo 1983435 14297239 := bstep (se 1 (by rfl) ⟨10722929, by rfl⟩ : syracuseStep 14297239 = 21445859) B21445859
theorem B76251941 : Blo 1983435 76251941 := bstep (se 4 (by rfl) ⟨7148619, by rfl⟩ : syracuseStep 76251941 = 14297239) B14297239
theorem B50834627 : Blo 1983435 50834627 := bstep (se 1 (by rfl) ⟨38125970, by rfl⟩ : syracuseStep 50834627 = 76251941) B76251941
theorem B33889751 : Blo 1983435 33889751 := bstep (se 1 (by rfl) ⟨25417313, by rfl⟩ : syracuseStep 33889751 = 50834627) B50834627
theorem B22593167 : Blo 1983435 22593167 := bstep (se 1 (by rfl) ⟨16944875, by rfl⟩ : syracuseStep 22593167 = 33889751) B33889751
theorem B15062111 : Blo 1983435 15062111 := bstep (se 1 (by rfl) ⟨11296583, by rfl⟩ : syracuseStep 15062111 = 22593167) B22593167
theorem B10041407 : Blo 1983435 10041407 := bstep (se 1 (by rfl) ⟨7531055, by rfl⟩ : syracuseStep 10041407 = 15062111) B15062111
theorem B6694271 : Blo 1983435 6694271 := bstep (se 1 (by rfl) ⟨5020703, by rfl⟩ : syracuseStep 6694271 = 10041407) B10041407
theorem B4462847 : Blo 1983435 4462847 := bstep (se 1 (by rfl) ⟨3347135, by rfl⟩ : syracuseStep 4462847 = 6694271) B6694271
theorem B2975231 : Blo 1983435 2975231 := bstep (se 1 (by rfl) ⟨2231423, by rfl⟩ : syracuseStep 2975231 = 4462847) B4462847
theorem B1983487 : Blo 1983435 1983487 := bstep (se 1 (by rfl) ⟨1487615, by rfl⟩ : syracuseStep 1983487 = 2975231) B2975231
theorem B2975237 : Blo 1983435 2975237 := bbase (se 4 (by rfl) ⟨278928, by rfl⟩ : syracuseStep 2975237 = 557857) (by norm_num)
theorem B1983491 : Blo 1983435 1983491 := bstep (se 1 (by rfl) ⟨1487618, by rfl⟩ : syracuseStep 1983491 = 2975237) B2975237
theorem B3347149 : Blo 1983435 3347149 := bbase (se 3 (by rfl) ⟨627590, by rfl⟩ : syracuseStep 3347149 = 1255181) (by norm_num)
theorem B4462865 : Blo 1983435 4462865 := bstep (se 2 (by rfl) ⟨1673574, by rfl⟩ : syracuseStep 4462865 = 3347149) B3347149
theorem B2975243 : Blo 1983435 2975243 := bstep (se 1 (by rfl) ⟨2231432, by rfl⟩ : syracuseStep 2975243 = 4462865) B4462865
theorem B1983495 : Blo 1983435 1983495 := bstep (se 1 (by rfl) ⟨1487621, by rfl⟩ : syracuseStep 1983495 = 2975243) B2975243
theorem B2231437 : Blo 1983435 2231437 := bbase (se 3 (by rfl) ⟨418394, by rfl⟩ : syracuseStep 2231437 = 836789) (by norm_num)
theorem B2975249 : Blo 1983435 2975249 := bstep (se 2 (by rfl) ⟨1115718, by rfl⟩ : syracuseStep 2975249 = 2231437) B2231437
theorem B1983499 : Blo 1983435 1983499 := bstep (se 1 (by rfl) ⟨1487624, by rfl⟩ : syracuseStep 1983499 = 2975249) B2975249
theorem B6694325 : Blo 1983435 6694325 := bbase (se 5 (by rfl) ⟨313796, by rfl⟩ : syracuseStep 6694325 = 627593) (by norm_num)
theorem B4462883 : Blo 1983435 4462883 := bstep (se 1 (by rfl) ⟨3347162, by rfl⟩ : syracuseStep 4462883 = 6694325) B6694325
theorem B2975255 : Blo 1983435 2975255 := bstep (se 1 (by rfl) ⟨2231441, by rfl⟩ : syracuseStep 2975255 = 4462883) B4462883
theorem B1983503 : Blo 1983435 1983503 := bstep (se 1 (by rfl) ⟨1487627, by rfl⟩ : syracuseStep 1983503 = 2975255) B2975255
theorem B2975261 : Blo 1983435 2975261 := bbase (se 3 (by rfl) ⟨557861, by rfl⟩ : syracuseStep 2975261 = 1115723) (by norm_num)
theorem B1983507 : Blo 1983435 1983507 := bstep (se 1 (by rfl) ⟨1487630, by rfl⟩ : syracuseStep 1983507 = 2975261) B2975261
theorem B4462901 : Blo 1983435 4462901 := bbase (se 5 (by rfl) ⟨209198, by rfl⟩ : syracuseStep 4462901 = 418397) (by norm_num)
theorem B2975267 : Blo 1983435 2975267 := bstep (se 1 (by rfl) ⟨2231450, by rfl⟩ : syracuseStep 2975267 = 4462901) B4462901
theorem B1983511 : Blo 1983435 1983511 := bstep (se 1 (by rfl) ⟨1487633, by rfl⟩ : syracuseStep 1983511 = 2975267) B2975267
theorem B5089277 : Blo 1983435 5089277 := bbase (se 3 (by rfl) ⟨954239, by rfl⟩ : syracuseStep 5089277 = 1908479) (by norm_num)
theorem B3392851 : Blo 1983435 3392851 := bstep (se 1 (by rfl) ⟨2544638, by rfl⟩ : syracuseStep 3392851 = 5089277) B5089277
theorem B4523801 : Blo 1983435 4523801 := bstep (se 2 (by rfl) ⟨1696425, by rfl⟩ : syracuseStep 4523801 = 3392851) B3392851
theorem B48253877 : Blo 1983435 48253877 := bstep (se 5 (by rfl) ⟨2261900, by rfl⟩ : syracuseStep 48253877 = 4523801) B4523801
theorem B32169251 : Blo 1983435 32169251 := bstep (se 1 (by rfl) ⟨24126938, by rfl⟩ : syracuseStep 32169251 = 48253877) B48253877
theorem B21446167 : Blo 1983435 21446167 := bstep (se 1 (by rfl) ⟨16084625, by rfl⟩ : syracuseStep 21446167 = 32169251) B32169251
theorem B28594889 : Blo 1983435 28594889 := bstep (se 2 (by rfl) ⟨10723083, by rfl⟩ : syracuseStep 28594889 = 21446167) B21446167
theorem B19063259 : Blo 1983435 19063259 := bstep (se 1 (by rfl) ⟨14297444, by rfl⟩ : syracuseStep 19063259 = 28594889) B28594889
theorem B12708839 : Blo 1983435 12708839 := bstep (se 1 (by rfl) ⟨9531629, by rfl⟩ : syracuseStep 12708839 = 19063259) B19063259
theorem B8472559 : Blo 1983435 8472559 := bstep (se 1 (by rfl) ⟨6354419, by rfl⟩ : syracuseStep 8472559 = 12708839) B12708839
theorem B11296745 : Blo 1983435 11296745 := bstep (se 2 (by rfl) ⟨4236279, by rfl⟩ : syracuseStep 11296745 = 8472559) B8472559
theorem B7531163 : Blo 1983435 7531163 := bstep (se 1 (by rfl) ⟨5648372, by rfl⟩ : syracuseStep 7531163 = 11296745) B11296745
theorem B5020775 : Blo 1983435 5020775 := bstep (se 1 (by rfl) ⟨3765581, by rfl⟩ : syracuseStep 5020775 = 7531163) B7531163
theorem B3347183 : Blo 1983435 3347183 := bstep (se 1 (by rfl) ⟨2510387, by rfl⟩ : syracuseStep 3347183 = 5020775) B5020775
theorem B2231455 : Blo 1983435 2231455 := bstep (se 1 (by rfl) ⟨1673591, by rfl⟩ : syracuseStep 2231455 = 3347183) B3347183
theorem B2975273 : Blo 1983435 2975273 := bstep (se 2 (by rfl) ⟨1115727, by rfl⟩ : syracuseStep 2975273 = 2231455) B2231455
theorem B1983515 : Blo 1983435 1983515 := bstep (se 1 (by rfl) ⟨1487636, by rfl⟩ : syracuseStep 1983515 = 2975273) B2975273
theorem B2941373 : Blo 1983435 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B7843661 : Blo 1983435 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B5229107 : Blo 1983435 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B3486071 : Blo 1983435 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B2324047 : Blo 1983435 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B3098729 : Blo 1983435 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B2065819 : Blo 1983435 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B2754425 : Blo 1983435 2754425 := bstep (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) B2065819
theorem B7345133 : Blo 1983435 7345133 := bstep (se 3 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 7345133 = 2754425) B2754425
theorem B4896755 : Blo 1983435 4896755 := bstep (se 1 (by rfl) ⟨3672566, by rfl⟩ : syracuseStep 4896755 = 7345133) B7345133
theorem B3264503 : Blo 1983435 3264503 := bstep (se 1 (by rfl) ⟨2448377, by rfl⟩ : syracuseStep 3264503 = 4896755) B4896755
theorem B8705341 : Blo 1983435 8705341 := bstep (se 3 (by rfl) ⟨1632251, by rfl⟩ : syracuseStep 8705341 = 3264503) B3264503
theorem B11607121 : Blo 1983435 11607121 := bstep (se 2 (by rfl) ⟨4352670, by rfl⟩ : syracuseStep 11607121 = 8705341) B8705341
theorem B61904645 : Blo 1983435 61904645 := bstep (se 4 (by rfl) ⟨5803560, by rfl⟩ : syracuseStep 61904645 = 11607121) B11607121
theorem B41269763 : Blo 1983435 41269763 := bstep (se 1 (by rfl) ⟨30952322, by rfl⟩ : syracuseStep 41269763 = 61904645) B61904645
theorem B110052701 : Blo 1983435 110052701 := bstep (se 3 (by rfl) ⟨20634881, by rfl⟩ : syracuseStep 110052701 = 41269763) B41269763
theorem B73368467 : Blo 1983435 73368467 := bstep (se 1 (by rfl) ⟨55026350, by rfl⟩ : syracuseStep 73368467 = 110052701) B110052701
theorem B48912311 : Blo 1983435 48912311 := bstep (se 1 (by rfl) ⟨36684233, by rfl⟩ : syracuseStep 48912311 = 73368467) B73368467
theorem B32608207 : Blo 1983435 32608207 := bstep (se 1 (by rfl) ⟨24456155, by rfl⟩ : syracuseStep 32608207 = 48912311) B48912311
theorem B43477609 : Blo 1983435 43477609 := bstep (se 2 (by rfl) ⟨16304103, by rfl⟩ : syracuseStep 43477609 = 32608207) B32608207
theorem B57970145 : Blo 1983435 57970145 := bstep (se 2 (by rfl) ⟨21738804, by rfl⟩ : syracuseStep 57970145 = 43477609) B43477609
theorem B154587053 : Blo 1983435 154587053 := bstep (se 3 (by rfl) ⟨28985072, by rfl⟩ : syracuseStep 154587053 = 57970145) B57970145
theorem B412232141 : Blo 1983435 412232141 := bstep (se 3 (by rfl) ⟨77293526, by rfl⟩ : syracuseStep 412232141 = 154587053) B154587053
theorem B274821427 : Blo 1983435 274821427 := bstep (se 1 (by rfl) ⟨206116070, by rfl⟩ : syracuseStep 274821427 = 412232141) B412232141
theorem B366428569 : Blo 1983435 366428569 := bstep (se 2 (by rfl) ⟨137410713, by rfl⟩ : syracuseStep 366428569 = 274821427) B274821427
theorem B488571425 : Blo 1983435 488571425 := bstep (se 2 (by rfl) ⟨183214284, by rfl⟩ : syracuseStep 488571425 = 366428569) B366428569
theorem B325714283 : Blo 1983435 325714283 := bstep (se 1 (by rfl) ⟨244285712, by rfl⟩ : syracuseStep 325714283 = 488571425) B488571425
theorem B217142855 : Blo 1983435 217142855 := bstep (se 1 (by rfl) ⟨162857141, by rfl⟩ : syracuseStep 217142855 = 325714283) B325714283
theorem B144761903 : Blo 1983435 144761903 := bstep (se 1 (by rfl) ⟨108571427, by rfl⟩ : syracuseStep 144761903 = 217142855) B217142855
theorem B96507935 : Blo 1983435 96507935 := bstep (se 1 (by rfl) ⟨72380951, by rfl⟩ : syracuseStep 96507935 = 144761903) B144761903
theorem B64338623 : Blo 1983435 64338623 := bstep (se 1 (by rfl) ⟨48253967, by rfl⟩ : syracuseStep 64338623 = 96507935) B96507935
theorem B42892415 : Blo 1983435 42892415 := bstep (se 1 (by rfl) ⟨32169311, by rfl⟩ : syracuseStep 42892415 = 64338623) B64338623
theorem B28594943 : Blo 1983435 28594943 := bstep (se 1 (by rfl) ⟨21446207, by rfl⟩ : syracuseStep 28594943 = 42892415) B42892415
theorem B19063295 : Blo 1983435 19063295 := bstep (se 1 (by rfl) ⟨14297471, by rfl⟩ : syracuseStep 19063295 = 28594943) B28594943
theorem B12708863 : Blo 1983435 12708863 := bstep (se 1 (by rfl) ⟨9531647, by rfl⟩ : syracuseStep 12708863 = 19063295) B19063295
theorem B8472575 : Blo 1983435 8472575 := bstep (se 1 (by rfl) ⟨6354431, by rfl⟩ : syracuseStep 8472575 = 12708863) B12708863
theorem B5648383 : Blo 1983435 5648383 := bstep (se 1 (by rfl) ⟨4236287, by rfl⟩ : syracuseStep 5648383 = 8472575) B8472575
theorem B7531177 : Blo 1983435 7531177 := bstep (se 2 (by rfl) ⟨2824191, by rfl⟩ : syracuseStep 7531177 = 5648383) B5648383
theorem B10041569 : Blo 1983435 10041569 := bstep (se 2 (by rfl) ⟨3765588, by rfl⟩ : syracuseStep 10041569 = 7531177) B7531177
theorem B6694379 : Blo 1983435 6694379 := bstep (se 1 (by rfl) ⟨5020784, by rfl⟩ : syracuseStep 6694379 = 10041569) B10041569
theorem B4462919 : Blo 1983435 4462919 := bstep (se 1 (by rfl) ⟨3347189, by rfl⟩ : syracuseStep 4462919 = 6694379) B6694379
theorem B2975279 : Blo 1983435 2975279 := bstep (se 1 (by rfl) ⟨2231459, by rfl⟩ : syracuseStep 2975279 = 4462919) B4462919
theorem B1983519 : Blo 1983435 1983519 := bstep (se 1 (by rfl) ⟨1487639, by rfl⟩ : syracuseStep 1983519 = 2975279) B2975279
theorem B2975285 : Blo 1983435 2975285 := bbase (se 5 (by rfl) ⟨139466, by rfl⟩ : syracuseStep 2975285 = 278933) (by norm_num)
theorem B1983523 : Blo 1983435 1983523 := bstep (se 1 (by rfl) ⟨1487642, by rfl⟩ : syracuseStep 1983523 = 2975285) B2975285
theorem B5020805 : Blo 1983435 5020805 := bbase (se 4 (by rfl) ⟨470700, by rfl⟩ : syracuseStep 5020805 = 941401) (by norm_num)
theorem B3347203 : Blo 1983435 3347203 := bstep (se 1 (by rfl) ⟨2510402, by rfl⟩ : syracuseStep 3347203 = 5020805) B5020805
theorem B4462937 : Blo 1983435 4462937 := bstep (se 2 (by rfl) ⟨1673601, by rfl⟩ : syracuseStep 4462937 = 3347203) B3347203
theorem B2975291 : Blo 1983435 2975291 := bstep (se 1 (by rfl) ⟨2231468, by rfl⟩ : syracuseStep 2975291 = 4462937) B4462937
theorem B1983527 : Blo 1983435 1983527 := bstep (se 1 (by rfl) ⟨1487645, by rfl⟩ : syracuseStep 1983527 = 2975291) B2975291
theorem B2231473 : Blo 1983435 2231473 := bbase (se 2 (by rfl) ⟨836802, by rfl⟩ : syracuseStep 2231473 = 1673605) (by norm_num)
theorem B2975297 : Blo 1983435 2975297 := bstep (se 2 (by rfl) ⟨1115736, by rfl⟩ : syracuseStep 2975297 = 2231473) B2231473
theorem B1983531 : Blo 1983435 1983531 := bstep (se 1 (by rfl) ⟨1487648, by rfl⟩ : syracuseStep 1983531 = 2975297) B2975297
theorem B2118161 : Blo 1983435 2118161 := bbase (se 2 (by rfl) ⟨794310, by rfl⟩ : syracuseStep 2118161 = 1588621) (by norm_num)
theorem B5648429 : Blo 1983435 5648429 := bstep (se 3 (by rfl) ⟨1059080, by rfl⟩ : syracuseStep 5648429 = 2118161) B2118161
theorem B3765619 : Blo 1983435 3765619 := bstep (se 1 (by rfl) ⟨2824214, by rfl⟩ : syracuseStep 3765619 = 5648429) B5648429
theorem B5020825 : Blo 1983435 5020825 := bstep (se 2 (by rfl) ⟨1882809, by rfl⟩ : syracuseStep 5020825 = 3765619) B3765619
theorem B6694433 : Blo 1983435 6694433 := bstep (se 2 (by rfl) ⟨2510412, by rfl⟩ : syracuseStep 6694433 = 5020825) B5020825
theorem B4462955 : Blo 1983435 4462955 := bstep (se 1 (by rfl) ⟨3347216, by rfl⟩ : syracuseStep 4462955 = 6694433) B6694433
theorem B2975303 : Blo 1983435 2975303 := bstep (se 1 (by rfl) ⟨2231477, by rfl⟩ : syracuseStep 2975303 = 4462955) B4462955
theorem B1983535 : Blo 1983435 1983535 := bstep (se 1 (by rfl) ⟨1487651, by rfl⟩ : syracuseStep 1983535 = 2975303) B2975303
theorem B2975309 : Blo 1983435 2975309 := bbase (se 3 (by rfl) ⟨557870, by rfl⟩ : syracuseStep 2975309 = 1115741) (by norm_num)
theorem B1983539 : Blo 1983435 1983539 := bstep (se 1 (by rfl) ⟨1487654, by rfl⟩ : syracuseStep 1983539 = 2975309) B2975309
theorem B4462973 : Blo 1983435 4462973 := bbase (se 3 (by rfl) ⟨836807, by rfl⟩ : syracuseStep 4462973 = 1673615) (by norm_num)
theorem B2975315 : Blo 1983435 2975315 := bstep (se 1 (by rfl) ⟨2231486, by rfl⟩ : syracuseStep 2975315 = 4462973) B4462973
theorem B1983543 : Blo 1983435 1983543 := bstep (se 1 (by rfl) ⟨1487657, by rfl⟩ : syracuseStep 1983543 = 2975315) B2975315
theorem B3347237 : Blo 1983435 3347237 := bbase (se 4 (by rfl) ⟨313803, by rfl⟩ : syracuseStep 3347237 = 627607) (by norm_num)
theorem B2231491 : Blo 1983435 2231491 := bstep (se 1 (by rfl) ⟨1673618, by rfl⟩ : syracuseStep 2231491 = 3347237) B3347237
theorem B2975321 : Blo 1983435 2975321 := bstep (se 2 (by rfl) ⟨1115745, by rfl⟩ : syracuseStep 2975321 = 2231491) B2231491
theorem B1983547 : Blo 1983435 1983547 := bstep (se 1 (by rfl) ⟨1487660, by rfl⟩ : syracuseStep 1983547 = 2975321) B2975321
theorem B2824237 : Blo 1983435 2824237 := bbase (se 3 (by rfl) ⟨529544, by rfl⟩ : syracuseStep 2824237 = 1059089) (by norm_num)
theorem B15062597 : Blo 1983435 15062597 := bstep (se 4 (by rfl) ⟨1412118, by rfl⟩ : syracuseStep 15062597 = 2824237) B2824237
theorem B10041731 : Blo 1983435 10041731 := bstep (se 1 (by rfl) ⟨7531298, by rfl⟩ : syracuseStep 10041731 = 15062597) B15062597
theorem B6694487 : Blo 1983435 6694487 := bstep (se 1 (by rfl) ⟨5020865, by rfl⟩ : syracuseStep 6694487 = 10041731) B10041731
theorem B4462991 : Blo 1983435 4462991 := bstep (se 1 (by rfl) ⟨3347243, by rfl⟩ : syracuseStep 4462991 = 6694487) B6694487
theorem B2975327 : Blo 1983435 2975327 := bstep (se 1 (by rfl) ⟨2231495, by rfl⟩ : syracuseStep 2975327 = 4462991) B4462991
theorem B1983551 : Blo 1983435 1983551 := bstep (se 1 (by rfl) ⟨1487663, by rfl⟩ : syracuseStep 1983551 = 2975327) B2975327
theorem B2975333 : Blo 1983435 2975333 := bbase (se 4 (by rfl) ⟨278937, by rfl⟩ : syracuseStep 2975333 = 557875) (by norm_num)
theorem B1983555 : Blo 1983435 1983555 := bstep (se 1 (by rfl) ⟨1487666, by rfl⟩ : syracuseStep 1983555 = 2975333) B2975333
theorem B2382961 : Blo 1983435 2382961 := bbase (se 2 (by rfl) ⟨893610, by rfl⟩ : syracuseStep 2382961 = 1787221) (by norm_num)
theorem B3177281 : Blo 1983435 3177281 := bstep (se 2 (by rfl) ⟨1191480, by rfl⟩ : syracuseStep 3177281 = 2382961) B2382961
theorem B2118187 : Blo 1983435 2118187 := bstep (se 1 (by rfl) ⟨1588640, by rfl⟩ : syracuseStep 2118187 = 3177281) B3177281
theorem B2824249 : Blo 1983435 2824249 := bstep (se 2 (by rfl) ⟨1059093, by rfl⟩ : syracuseStep 2824249 = 2118187) B2118187
theorem B3765665 : Blo 1983435 3765665 := bstep (se 2 (by rfl) ⟨1412124, by rfl⟩ : syracuseStep 3765665 = 2824249) B2824249
theorem B2510443 : Blo 1983435 2510443 := bstep (se 1 (by rfl) ⟨1882832, by rfl⟩ : syracuseStep 2510443 = 3765665) B3765665
theorem B3347257 : Blo 1983435 3347257 := bstep (se 2 (by rfl) ⟨1255221, by rfl⟩ : syracuseStep 3347257 = 2510443) B2510443
theorem B4463009 : Blo 1983435 4463009 := bstep (se 2 (by rfl) ⟨1673628, by rfl⟩ : syracuseStep 4463009 = 3347257) B3347257
theorem B2975339 : Blo 1983435 2975339 := bstep (se 1 (by rfl) ⟨2231504, by rfl⟩ : syracuseStep 2975339 = 4463009) B4463009
theorem B1983559 : Blo 1983435 1983559 := bstep (se 1 (by rfl) ⟨1487669, by rfl⟩ : syracuseStep 1983559 = 2975339) B2975339
theorem B2231509 : Blo 1983435 2231509 := bbase (se 7 (by rfl) ⟨26150, by rfl⟩ : syracuseStep 2231509 = 52301) (by norm_num)
theorem B2975345 : Blo 1983435 2975345 := bstep (se 2 (by rfl) ⟨1115754, by rfl⟩ : syracuseStep 2975345 = 2231509) B2231509
theorem B1983563 : Blo 1983435 1983563 := bstep (se 1 (by rfl) ⟨1487672, by rfl⟩ : syracuseStep 1983563 = 2975345) B2975345
theorem B2510453 : Blo 1983435 2510453 := bbase (se 5 (by rfl) ⟨117677, by rfl⟩ : syracuseStep 2510453 = 235355) (by norm_num)
theorem B6694541 : Blo 1983435 6694541 := bstep (se 3 (by rfl) ⟨1255226, by rfl⟩ : syracuseStep 6694541 = 2510453) B2510453
theorem B4463027 : Blo 1983435 4463027 := bstep (se 1 (by rfl) ⟨3347270, by rfl⟩ : syracuseStep 4463027 = 6694541) B6694541
theorem B2975351 : Blo 1983435 2975351 := bstep (se 1 (by rfl) ⟨2231513, by rfl⟩ : syracuseStep 2975351 = 4463027) B4463027
theorem B1983567 : Blo 1983435 1983567 := bstep (se 1 (by rfl) ⟨1487675, by rfl⟩ : syracuseStep 1983567 = 2975351) B2975351
theorem B2975357 : Blo 1983435 2975357 := bbase (se 3 (by rfl) ⟨557879, by rfl⟩ : syracuseStep 2975357 = 1115759) (by norm_num)
theorem B1983571 : Blo 1983435 1983571 := bstep (se 1 (by rfl) ⟨1487678, by rfl⟩ : syracuseStep 1983571 = 2975357) B2975357
theorem B4463045 : Blo 1983435 4463045 := bbase (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) (by norm_num)
theorem B2975363 : Blo 1983435 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B1983575 : Blo 1983435 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B3574477 : Blo 1983435 3574477 := bbase (se 3 (by rfl) ⟨670214, by rfl⟩ : syracuseStep 3574477 = 1340429) (by norm_num)
theorem B4765969 : Blo 1983435 4765969 := bstep (se 2 (by rfl) ⟨1787238, by rfl⟩ : syracuseStep 4765969 = 3574477) B3574477
theorem B6354625 : Blo 1983435 6354625 := bstep (se 2 (by rfl) ⟨2382984, by rfl⟩ : syracuseStep 6354625 = 4765969) B4765969
theorem B8472833 : Blo 1983435 8472833 := bstep (se 2 (by rfl) ⟨3177312, by rfl⟩ : syracuseStep 8472833 = 6354625) B6354625
theorem B5648555 : Blo 1983435 5648555 := bstep (se 1 (by rfl) ⟨4236416, by rfl⟩ : syracuseStep 5648555 = 8472833) B8472833
theorem B3765703 : Blo 1983435 3765703 := bstep (se 1 (by rfl) ⟨2824277, by rfl⟩ : syracuseStep 3765703 = 5648555) B5648555
theorem B5020937 : Blo 1983435 5020937 := bstep (se 2 (by rfl) ⟨1882851, by rfl⟩ : syracuseStep 5020937 = 3765703) B3765703
theorem B3347291 : Blo 1983435 3347291 := bstep (se 1 (by rfl) ⟨2510468, by rfl⟩ : syracuseStep 3347291 = 5020937) B5020937
theorem B2231527 : Blo 1983435 2231527 := bstep (se 1 (by rfl) ⟨1673645, by rfl⟩ : syracuseStep 2231527 = 3347291) B3347291
theorem B2975369 : Blo 1983435 2975369 := bstep (se 2 (by rfl) ⟨1115763, by rfl⟩ : syracuseStep 2975369 = 2231527) B2231527
theorem B1983579 : Blo 1983435 1983579 := bstep (se 1 (by rfl) ⟨1487684, by rfl⟩ : syracuseStep 1983579 = 2975369) B2975369
theorem B10041893 : Blo 1983435 10041893 := bbase (se 4 (by rfl) ⟨941427, by rfl⟩ : syracuseStep 10041893 = 1882855) (by norm_num)
theorem B6694595 : Blo 1983435 6694595 := bstep (se 1 (by rfl) ⟨5020946, by rfl⟩ : syracuseStep 6694595 = 10041893) B10041893
theorem B4463063 : Blo 1983435 4463063 := bstep (se 1 (by rfl) ⟨3347297, by rfl⟩ : syracuseStep 4463063 = 6694595) B6694595
theorem B2975375 : Blo 1983435 2975375 := bstep (se 1 (by rfl) ⟨2231531, by rfl⟩ : syracuseStep 2975375 = 4463063) B4463063
theorem B1983583 : Blo 1983435 1983583 := bstep (se 1 (by rfl) ⟨1487687, by rfl⟩ : syracuseStep 1983583 = 2975375) B2975375
theorem B2975381 : Blo 1983435 2975381 := bbase (se 6 (by rfl) ⟨69735, by rfl⟩ : syracuseStep 2975381 = 139471) (by norm_num)
theorem B1983587 : Blo 1983435 1983587 := bstep (se 1 (by rfl) ⟨1487690, by rfl⟩ : syracuseStep 1983587 = 2975381) B2975381
theorem B4765997 : Blo 1983435 4765997 := bbase (se 3 (by rfl) ⟨893624, by rfl⟩ : syracuseStep 4765997 = 1787249) (by norm_num)
theorem B12709325 : Blo 1983435 12709325 := bstep (se 3 (by rfl) ⟨2382998, by rfl⟩ : syracuseStep 12709325 = 4765997) B4765997
theorem B8472883 : Blo 1983435 8472883 := bstep (se 1 (by rfl) ⟨6354662, by rfl⟩ : syracuseStep 8472883 = 12709325) B12709325
theorem B11297177 : Blo 1983435 11297177 := bstep (se 2 (by rfl) ⟨4236441, by rfl⟩ : syracuseStep 11297177 = 8472883) B8472883
theorem B7531451 : Blo 1983435 7531451 := bstep (se 1 (by rfl) ⟨5648588, by rfl⟩ : syracuseStep 7531451 = 11297177) B11297177
theorem B5020967 : Blo 1983435 5020967 := bstep (se 1 (by rfl) ⟨3765725, by rfl⟩ : syracuseStep 5020967 = 7531451) B7531451
theorem B3347311 : Blo 1983435 3347311 := bstep (se 1 (by rfl) ⟨2510483, by rfl⟩ : syracuseStep 3347311 = 5020967) B5020967
theorem B4463081 : Blo 1983435 4463081 := bstep (se 2 (by rfl) ⟨1673655, by rfl⟩ : syracuseStep 4463081 = 3347311) B3347311
theorem B2975387 : Blo 1983435 2975387 := bstep (se 1 (by rfl) ⟨2231540, by rfl⟩ : syracuseStep 2975387 = 4463081) B4463081
theorem B1983591 : Blo 1983435 1983591 := bstep (se 1 (by rfl) ⟨1487693, by rfl⟩ : syracuseStep 1983591 = 2975387) B2975387
theorem B2231545 : Blo 1983435 2231545 := bbase (se 2 (by rfl) ⟨836829, by rfl⟩ : syracuseStep 2231545 = 1673659) (by norm_num)
theorem B2975393 : Blo 1983435 2975393 := bstep (se 2 (by rfl) ⟨1115772, by rfl⟩ : syracuseStep 2975393 = 2231545) B2231545
theorem B1983595 : Blo 1983435 1983595 := bstep (se 1 (by rfl) ⟨1487696, by rfl⟩ : syracuseStep 1983595 = 2975393) B2975393
theorem B8472917 : Blo 1983435 8472917 := bbase (se 10 (by rfl) ⟨12411, by rfl⟩ : syracuseStep 8472917 = 24823) (by norm_num)
theorem B5648611 : Blo 1983435 5648611 := bstep (se 1 (by rfl) ⟨4236458, by rfl⟩ : syracuseStep 5648611 = 8472917) B8472917
theorem B7531481 : Blo 1983435 7531481 := bstep (se 2 (by rfl) ⟨2824305, by rfl⟩ : syracuseStep 7531481 = 5648611) B5648611
theorem B5020987 : Blo 1983435 5020987 := bstep (se 1 (by rfl) ⟨3765740, by rfl⟩ : syracuseStep 5020987 = 7531481) B7531481
theorem B6694649 : Blo 1983435 6694649 := bstep (se 2 (by rfl) ⟨2510493, by rfl⟩ : syracuseStep 6694649 = 5020987) B5020987
theorem B4463099 : Blo 1983435 4463099 := bstep (se 1 (by rfl) ⟨3347324, by rfl⟩ : syracuseStep 4463099 = 6694649) B6694649
theorem B2975399 : Blo 1983435 2975399 := bstep (se 1 (by rfl) ⟨2231549, by rfl⟩ : syracuseStep 2975399 = 4463099) B4463099
theorem B1983599 : Blo 1983435 1983599 := bstep (se 1 (by rfl) ⟨1487699, by rfl⟩ : syracuseStep 1983599 = 2975399) B2975399
theorem B2975405 : Blo 1983435 2975405 := bbase (se 3 (by rfl) ⟨557888, by rfl⟩ : syracuseStep 2975405 = 1115777) (by norm_num)
theorem B1983603 : Blo 1983435 1983603 := bstep (se 1 (by rfl) ⟨1487702, by rfl⟩ : syracuseStep 1983603 = 2975405) B2975405
theorem B4463117 : Blo 1983435 4463117 := bbase (se 3 (by rfl) ⟨836834, by rfl⟩ : syracuseStep 4463117 = 1673669) (by norm_num)
theorem B2975411 : Blo 1983435 2975411 := bstep (se 1 (by rfl) ⟨2231558, by rfl⟩ : syracuseStep 2975411 = 4463117) B4463117
theorem B1983607 : Blo 1983435 1983607 := bstep (se 1 (by rfl) ⟨1487705, by rfl⟩ : syracuseStep 1983607 = 2975411) B2975411
theorem B2510509 : Blo 1983435 2510509 := bbase (se 3 (by rfl) ⟨470720, by rfl⟩ : syracuseStep 2510509 = 941441) (by norm_num)
theorem B3347345 : Blo 1983435 3347345 := bstep (se 2 (by rfl) ⟨1255254, by rfl⟩ : syracuseStep 3347345 = 2510509) B2510509
theorem B2231563 : Blo 1983435 2231563 := bstep (se 1 (by rfl) ⟨1673672, by rfl⟩ : syracuseStep 2231563 = 3347345) B3347345
theorem B2975417 : Blo 1983435 2975417 := bstep (se 2 (by rfl) ⟨1115781, by rfl⟩ : syracuseStep 2975417 = 2231563) B2231563
theorem B1983611 : Blo 1983435 1983611 := bstep (se 1 (by rfl) ⟨1487708, by rfl⟩ : syracuseStep 1983611 = 2975417) B2975417
theorem B3574541 : Blo 1983435 3574541 := bbase (se 3 (by rfl) ⟨670226, by rfl⟩ : syracuseStep 3574541 = 1340453) (by norm_num)
theorem B2383027 : Blo 1983435 2383027 := bstep (se 1 (by rfl) ⟨1787270, by rfl⟩ : syracuseStep 2383027 = 3574541) B3574541
theorem B12709477 : Blo 1983435 12709477 := bstep (se 4 (by rfl) ⟨1191513, by rfl⟩ : syracuseStep 12709477 = 2383027) B2383027
theorem B16945969 : Blo 1983435 16945969 := bstep (se 2 (by rfl) ⟨6354738, by rfl⟩ : syracuseStep 16945969 = 12709477) B12709477
theorem B22594625 : Blo 1983435 22594625 := bstep (se 2 (by rfl) ⟨8472984, by rfl⟩ : syracuseStep 22594625 = 16945969) B16945969
theorem B15063083 : Blo 1983435 15063083 := bstep (se 1 (by rfl) ⟨11297312, by rfl⟩ : syracuseStep 15063083 = 22594625) B22594625
theorem B10042055 : Blo 1983435 10042055 := bstep (se 1 (by rfl) ⟨7531541, by rfl⟩ : syracuseStep 10042055 = 15063083) B15063083
theorem B6694703 : Blo 1983435 6694703 := bstep (se 1 (by rfl) ⟨5021027, by rfl⟩ : syracuseStep 6694703 = 10042055) B10042055
theorem B4463135 : Blo 1983435 4463135 := bstep (se 1 (by rfl) ⟨3347351, by rfl⟩ : syracuseStep 4463135 = 6694703) B6694703
theorem B2975423 : Blo 1983435 2975423 := bstep (se 1 (by rfl) ⟨2231567, by rfl⟩ : syracuseStep 2975423 = 4463135) B4463135
theorem B1983615 : Blo 1983435 1983615 := bstep (se 1 (by rfl) ⟨1487711, by rfl⟩ : syracuseStep 1983615 = 2975423) B2975423
theorem B2975429 : Blo 1983435 2975429 := bbase (se 4 (by rfl) ⟨278946, by rfl⟩ : syracuseStep 2975429 = 557893) (by norm_num)
theorem B1983619 : Blo 1983435 1983619 := bstep (se 1 (by rfl) ⟨1487714, by rfl⟩ : syracuseStep 1983619 = 2975429) B2975429
theorem B3347365 : Blo 1983435 3347365 := bbase (se 4 (by rfl) ⟨313815, by rfl⟩ : syracuseStep 3347365 = 627631) (by norm_num)
theorem B4463153 : Blo 1983435 4463153 := bstep (se 2 (by rfl) ⟨1673682, by rfl⟩ : syracuseStep 4463153 = 3347365) B3347365
theorem B2975435 : Blo 1983435 2975435 := bstep (se 1 (by rfl) ⟨2231576, by rfl⟩ : syracuseStep 2975435 = 4463153) B4463153
theorem B1983623 : Blo 1983435 1983623 := bstep (se 1 (by rfl) ⟨1487717, by rfl⟩ : syracuseStep 1983623 = 2975435) B2975435
theorem B2231581 : Blo 1983435 2231581 := bbase (se 3 (by rfl) ⟨418421, by rfl⟩ : syracuseStep 2231581 = 836843) (by norm_num)
theorem B2975441 : Blo 1983435 2975441 := bstep (se 2 (by rfl) ⟨1115790, by rfl⟩ : syracuseStep 2975441 = 2231581) B2231581
theorem B1983627 : Blo 1983435 1983627 := bstep (se 1 (by rfl) ⟨1487720, by rfl⟩ : syracuseStep 1983627 = 2975441) B2975441
theorem B6694757 : Blo 1983435 6694757 := bbase (se 4 (by rfl) ⟨627633, by rfl⟩ : syracuseStep 6694757 = 1255267) (by norm_num)
theorem B4463171 : Blo 1983435 4463171 := bstep (se 1 (by rfl) ⟨3347378, by rfl⟩ : syracuseStep 4463171 = 6694757) B6694757
theorem B2975447 : Blo 1983435 2975447 := bstep (se 1 (by rfl) ⟨2231585, by rfl⟩ : syracuseStep 2975447 = 4463171) B4463171
theorem B1983631 : Blo 1983435 1983631 := bstep (se 1 (by rfl) ⟨1487723, by rfl⟩ : syracuseStep 1983631 = 2975447) B2975447
theorem B2975453 : Blo 1983435 2975453 := bbase (se 3 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 2975453 = 1115795) (by norm_num)
theorem B1983635 : Blo 1983435 1983635 := bstep (se 1 (by rfl) ⟨1487726, by rfl⟩ : syracuseStep 1983635 = 2975453) B2975453
theorem B4463189 : Blo 1983435 4463189 := bbase (se 8 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 4463189 = 52303) (by norm_num)
theorem B2975459 : Blo 1983435 2975459 := bstep (se 1 (by rfl) ⟨2231594, by rfl⟩ : syracuseStep 2975459 = 4463189) B4463189
theorem B1983639 : Blo 1983435 1983639 := bstep (se 1 (by rfl) ⟨1487729, by rfl⟩ : syracuseStep 1983639 = 2975459) B2975459
theorem B48915413 : Blo 1983435 48915413 := bbase (se 7 (by rfl) ⟨573227, by rfl⟩ : syracuseStep 48915413 = 1146455) (by norm_num)
theorem B32610275 : Blo 1983435 32610275 := bstep (se 1 (by rfl) ⟨24457706, by rfl⟩ : syracuseStep 32610275 = 48915413) B48915413
theorem B21740183 : Blo 1983435 21740183 := bstep (se 1 (by rfl) ⟨16305137, by rfl⟩ : syracuseStep 21740183 = 32610275) B32610275
theorem B14493455 : Blo 1983435 14493455 := bstep (se 1 (by rfl) ⟨10870091, by rfl⟩ : syracuseStep 14493455 = 21740183) B21740183
theorem B9662303 : Blo 1983435 9662303 := bstep (se 1 (by rfl) ⟨7246727, by rfl⟩ : syracuseStep 9662303 = 14493455) B14493455
theorem B6441535 : Blo 1983435 6441535 := bstep (se 1 (by rfl) ⟨4831151, by rfl⟩ : syracuseStep 6441535 = 9662303) B9662303
theorem B34354853 : Blo 1983435 34354853 := bstep (se 4 (by rfl) ⟨3220767, by rfl⟩ : syracuseStep 34354853 = 6441535) B6441535
theorem B22903235 : Blo 1983435 22903235 := bstep (se 1 (by rfl) ⟨17177426, by rfl⟩ : syracuseStep 22903235 = 34354853) B34354853
theorem B15268823 : Blo 1983435 15268823 := bstep (se 1 (by rfl) ⟨11451617, by rfl⟩ : syracuseStep 15268823 = 22903235) B22903235
theorem B10179215 : Blo 1983435 10179215 := bstep (se 1 (by rfl) ⟨7634411, by rfl⟩ : syracuseStep 10179215 = 15268823) B15268823
theorem B6786143 : Blo 1983435 6786143 := bstep (se 1 (by rfl) ⟨5089607, by rfl⟩ : syracuseStep 6786143 = 10179215) B10179215
theorem B4524095 : Blo 1983435 4524095 := bstep (se 1 (by rfl) ⟨3393071, by rfl⟩ : syracuseStep 4524095 = 6786143) B6786143
theorem B3016063 : Blo 1983435 3016063 := bstep (se 1 (by rfl) ⟨2262047, by rfl⟩ : syracuseStep 3016063 = 4524095) B4524095
theorem B4021417 : Blo 1983435 4021417 := bstep (se 2 (by rfl) ⟨1508031, by rfl⟩ : syracuseStep 4021417 = 3016063) B3016063
theorem B5361889 : Blo 1983435 5361889 := bstep (se 2 (by rfl) ⟨2010708, by rfl⟩ : syracuseStep 5361889 = 4021417) B4021417
theorem B7149185 : Blo 1983435 7149185 := bstep (se 2 (by rfl) ⟨2680944, by rfl⟩ : syracuseStep 7149185 = 5361889) B5361889
theorem B4766123 : Blo 1983435 4766123 := bstep (se 1 (by rfl) ⟨3574592, by rfl⟩ : syracuseStep 4766123 = 7149185) B7149185
theorem B3177415 : Blo 1983435 3177415 := bstep (se 1 (by rfl) ⟨2383061, by rfl⟩ : syracuseStep 3177415 = 4766123) B4766123
theorem B4236553 : Blo 1983435 4236553 := bstep (se 2 (by rfl) ⟨1588707, by rfl⟩ : syracuseStep 4236553 = 3177415) B3177415
theorem B5648737 : Blo 1983435 5648737 := bstep (se 2 (by rfl) ⟨2118276, by rfl⟩ : syracuseStep 5648737 = 4236553) B4236553
theorem B7531649 : Blo 1983435 7531649 := bstep (se 2 (by rfl) ⟨2824368, by rfl⟩ : syracuseStep 7531649 = 5648737) B5648737
theorem B5021099 : Blo 1983435 5021099 := bstep (se 1 (by rfl) ⟨3765824, by rfl⟩ : syracuseStep 5021099 = 7531649) B7531649
theorem B3347399 : Blo 1983435 3347399 := bstep (se 1 (by rfl) ⟨2510549, by rfl⟩ : syracuseStep 3347399 = 5021099) B5021099
theorem B2231599 : Blo 1983435 2231599 := bstep (se 1 (by rfl) ⟨1673699, by rfl⟩ : syracuseStep 2231599 = 3347399) B3347399
theorem B2975465 : Blo 1983435 2975465 := bstep (se 2 (by rfl) ⟨1115799, by rfl⟩ : syracuseStep 2975465 = 2231599) B2231599
theorem B1983643 : Blo 1983435 1983643 := bstep (se 1 (by rfl) ⟨1487732, by rfl⟩ : syracuseStep 1983643 = 2975465) B2975465
theorem B2680949 : Blo 1983435 2680949 := bbase (se 5 (by rfl) ⟨125669, by rfl⟩ : syracuseStep 2680949 = 251339) (by norm_num)
theorem B7149197 : Blo 1983435 7149197 := bstep (se 3 (by rfl) ⟨1340474, by rfl⟩ : syracuseStep 7149197 = 2680949) B2680949
theorem B4766131 : Blo 1983435 4766131 := bstep (se 1 (by rfl) ⟨3574598, by rfl⟩ : syracuseStep 4766131 = 7149197) B7149197
theorem B25419365 : Blo 1983435 25419365 := bstep (se 4 (by rfl) ⟨2383065, by rfl⟩ : syracuseStep 25419365 = 4766131) B4766131
theorem B16946243 : Blo 1983435 16946243 := bstep (se 1 (by rfl) ⟨12709682, by rfl⟩ : syracuseStep 16946243 = 25419365) B25419365
theorem B11297495 : Blo 1983435 11297495 := bstep (se 1 (by rfl) ⟨8473121, by rfl⟩ : syracuseStep 11297495 = 16946243) B16946243
theorem B7531663 : Blo 1983435 7531663 := bstep (se 1 (by rfl) ⟨5648747, by rfl⟩ : syracuseStep 7531663 = 11297495) B11297495
theorem B10042217 : Blo 1983435 10042217 := bstep (se 2 (by rfl) ⟨3765831, by rfl⟩ : syracuseStep 10042217 = 7531663) B7531663
theorem B6694811 : Blo 1983435 6694811 := bstep (se 1 (by rfl) ⟨5021108, by rfl⟩ : syracuseStep 6694811 = 10042217) B10042217
theorem B4463207 : Blo 1983435 4463207 := bstep (se 1 (by rfl) ⟨3347405, by rfl⟩ : syracuseStep 4463207 = 6694811) B6694811
theorem B2975471 : Blo 1983435 2975471 := bstep (se 1 (by rfl) ⟨2231603, by rfl⟩ : syracuseStep 2975471 = 4463207) B4463207
theorem B1983647 : Blo 1983435 1983647 := bstep (se 1 (by rfl) ⟨1487735, by rfl⟩ : syracuseStep 1983647 = 2975471) B2975471
theorem B2975477 : Blo 1983435 2975477 := bbase (se 5 (by rfl) ⟨139475, by rfl⟩ : syracuseStep 2975477 = 278951) (by norm_num)
theorem B1983651 : Blo 1983435 1983651 := bstep (se 1 (by rfl) ⟨1487738, by rfl⟩ : syracuseStep 1983651 = 2975477) B2975477
theorem B8473157 : Blo 1983435 8473157 := bbase (se 4 (by rfl) ⟨794358, by rfl⟩ : syracuseStep 8473157 = 1588717) (by norm_num)
theorem B5648771 : Blo 1983435 5648771 := bstep (se 1 (by rfl) ⟨4236578, by rfl⟩ : syracuseStep 5648771 = 8473157) B8473157
theorem B3765847 : Blo 1983435 3765847 := bstep (se 1 (by rfl) ⟨2824385, by rfl⟩ : syracuseStep 3765847 = 5648771) B5648771
theorem B5021129 : Blo 1983435 5021129 := bstep (se 2 (by rfl) ⟨1882923, by rfl⟩ : syracuseStep 5021129 = 3765847) B3765847
theorem B3347419 : Blo 1983435 3347419 := bstep (se 1 (by rfl) ⟨2510564, by rfl⟩ : syracuseStep 3347419 = 5021129) B5021129
theorem B4463225 : Blo 1983435 4463225 := bstep (se 2 (by rfl) ⟨1673709, by rfl⟩ : syracuseStep 4463225 = 3347419) B3347419
theorem B2975483 : Blo 1983435 2975483 := bstep (se 1 (by rfl) ⟨2231612, by rfl⟩ : syracuseStep 2975483 = 4463225) B4463225
theorem B1983655 : Blo 1983435 1983655 := bstep (se 1 (by rfl) ⟨1487741, by rfl⟩ : syracuseStep 1983655 = 2975483) B2975483
theorem B2231617 : Blo 1983435 2231617 := bbase (se 2 (by rfl) ⟨836856, by rfl⟩ : syracuseStep 2231617 = 1673713) (by norm_num)
theorem B2975489 : Blo 1983435 2975489 := bstep (se 2 (by rfl) ⟨1115808, by rfl⟩ : syracuseStep 2975489 = 2231617) B2231617
theorem B1983659 : Blo 1983435 1983659 := bstep (se 1 (by rfl) ⟨1487744, by rfl⟩ : syracuseStep 1983659 = 2975489) B2975489
theorem B5021149 : Blo 1983435 5021149 := bbase (se 3 (by rfl) ⟨941465, by rfl⟩ : syracuseStep 5021149 = 1882931) (by norm_num)
theorem B6694865 : Blo 1983435 6694865 := bstep (se 2 (by rfl) ⟨2510574, by rfl⟩ : syracuseStep 6694865 = 5021149) B5021149
theorem B4463243 : Blo 1983435 4463243 := bstep (se 1 (by rfl) ⟨3347432, by rfl⟩ : syracuseStep 4463243 = 6694865) B6694865
theorem B2975495 : Blo 1983435 2975495 := bstep (se 1 (by rfl) ⟨2231621, by rfl⟩ : syracuseStep 2975495 = 4463243) B4463243
theorem B1983663 : Blo 1983435 1983663 := bstep (se 1 (by rfl) ⟨1487747, by rfl⟩ : syracuseStep 1983663 = 2975495) B2975495
theorem B2975501 : Blo 1983435 2975501 := bbase (se 3 (by rfl) ⟨557906, by rfl⟩ : syracuseStep 2975501 = 1115813) (by norm_num)
theorem B1983667 : Blo 1983435 1983667 := bstep (se 1 (by rfl) ⟨1487750, by rfl⟩ : syracuseStep 1983667 = 2975501) B2975501
theorem B4463261 : Blo 1983435 4463261 := bbase (se 3 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 4463261 = 1673723) (by norm_num)
theorem B2975507 : Blo 1983435 2975507 := bstep (se 1 (by rfl) ⟨2231630, by rfl⟩ : syracuseStep 2975507 = 4463261) B4463261
theorem B1983671 : Blo 1983435 1983671 := bstep (se 1 (by rfl) ⟨1487753, by rfl⟩ : syracuseStep 1983671 = 2975507) B2975507
theorem B3347453 : Blo 1983435 3347453 := bbase (se 3 (by rfl) ⟨627647, by rfl⟩ : syracuseStep 3347453 = 1255295) (by norm_num)
theorem B2231635 : Blo 1983435 2231635 := bstep (se 1 (by rfl) ⟨1673726, by rfl⟩ : syracuseStep 2231635 = 3347453) B3347453
theorem B2975513 : Blo 1983435 2975513 := bstep (se 2 (by rfl) ⟨1115817, by rfl⟩ : syracuseStep 2975513 = 2231635) B2231635
theorem B1983675 : Blo 1983435 1983675 := bstep (se 1 (by rfl) ⟨1487756, by rfl⟩ : syracuseStep 1983675 = 2975513) B2975513
theorem B4236629 : Blo 1983435 4236629 := bbase (se 12 (by rfl) ⟨1551, by rfl⟩ : syracuseStep 4236629 = 3103) (by norm_num)
theorem B11297677 : Blo 1983435 11297677 := bstep (se 3 (by rfl) ⟨2118314, by rfl⟩ : syracuseStep 11297677 = 4236629) B4236629
theorem B15063569 : Blo 1983435 15063569 := bstep (se 2 (by rfl) ⟨5648838, by rfl⟩ : syracuseStep 15063569 = 11297677) B11297677
theorem B10042379 : Blo 1983435 10042379 := bstep (se 1 (by rfl) ⟨7531784, by rfl⟩ : syracuseStep 10042379 = 15063569) B15063569
theorem B6694919 : Blo 1983435 6694919 := bstep (se 1 (by rfl) ⟨5021189, by rfl⟩ : syracuseStep 6694919 = 10042379) B10042379
theorem B4463279 : Blo 1983435 4463279 := bstep (se 1 (by rfl) ⟨3347459, by rfl⟩ : syracuseStep 4463279 = 6694919) B6694919
theorem B2975519 : Blo 1983435 2975519 := bstep (se 1 (by rfl) ⟨2231639, by rfl⟩ : syracuseStep 2975519 = 4463279) B4463279
theorem B1983679 : Blo 1983435 1983679 := bstep (se 1 (by rfl) ⟨1487759, by rfl⟩ : syracuseStep 1983679 = 2975519) B2975519
theorem B2975525 : Blo 1983435 2975525 := bbase (se 4 (by rfl) ⟨278955, by rfl⟩ : syracuseStep 2975525 = 557911) (by norm_num)
theorem B1983683 : Blo 1983435 1983683 := bstep (se 1 (by rfl) ⟨1487762, by rfl⟩ : syracuseStep 1983683 = 2975525) B2975525
theorem B2510605 : Blo 1983435 2510605 := bbase (se 3 (by rfl) ⟨470738, by rfl⟩ : syracuseStep 2510605 = 941477) (by norm_num)
theorem B3347473 : Blo 1983435 3347473 := bstep (se 2 (by rfl) ⟨1255302, by rfl⟩ : syracuseStep 3347473 = 2510605) B2510605
theorem B4463297 : Blo 1983435 4463297 := bstep (se 2 (by rfl) ⟨1673736, by rfl⟩ : syracuseStep 4463297 = 3347473) B3347473
theorem B2975531 : Blo 1983435 2975531 := bstep (se 1 (by rfl) ⟨2231648, by rfl⟩ : syracuseStep 2975531 = 4463297) B4463297
theorem B1983687 : Blo 1983435 1983687 := bstep (se 1 (by rfl) ⟨1487765, by rfl⟩ : syracuseStep 1983687 = 2975531) B2975531
theorem B2231653 : Blo 1983435 2231653 := bbase (se 4 (by rfl) ⟨209217, by rfl⟩ : syracuseStep 2231653 = 418435) (by norm_num)
theorem B2975537 : Blo 1983435 2975537 := bstep (se 2 (by rfl) ⟨1115826, by rfl⟩ : syracuseStep 2975537 = 2231653) B2231653
theorem B1983691 : Blo 1983435 1983691 := bstep (se 1 (by rfl) ⟨1487768, by rfl⟩ : syracuseStep 1983691 = 2975537) B2975537
theorem B5648885 : Blo 1983435 5648885 := bbase (se 5 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 5648885 = 529583) (by norm_num)
theorem B3765923 : Blo 1983435 3765923 := bstep (se 1 (by rfl) ⟨2824442, by rfl⟩ : syracuseStep 3765923 = 5648885) B5648885
theorem B2510615 : Blo 1983435 2510615 := bstep (se 1 (by rfl) ⟨1882961, by rfl⟩ : syracuseStep 2510615 = 3765923) B3765923
theorem B6694973 : Blo 1983435 6694973 := bstep (se 3 (by rfl) ⟨1255307, by rfl⟩ : syracuseStep 6694973 = 2510615) B2510615
theorem B4463315 : Blo 1983435 4463315 := bstep (se 1 (by rfl) ⟨3347486, by rfl⟩ : syracuseStep 4463315 = 6694973) B6694973
theorem B2975543 : Blo 1983435 2975543 := bstep (se 1 (by rfl) ⟨2231657, by rfl⟩ : syracuseStep 2975543 = 4463315) B4463315
theorem B1983695 : Blo 1983435 1983695 := bstep (se 1 (by rfl) ⟨1487771, by rfl⟩ : syracuseStep 1983695 = 2975543) B2975543
theorem B2975549 : Blo 1983435 2975549 := bbase (se 3 (by rfl) ⟨557915, by rfl⟩ : syracuseStep 2975549 = 1115831) (by norm_num)
theorem B1983699 : Blo 1983435 1983699 := bstep (se 1 (by rfl) ⟨1487774, by rfl⟩ : syracuseStep 1983699 = 2975549) B2975549
theorem B4463333 : Blo 1983435 4463333 := bbase (se 4 (by rfl) ⟨418437, by rfl⟩ : syracuseStep 4463333 = 836875) (by norm_num)
theorem B2975555 : Blo 1983435 2975555 := bstep (se 1 (by rfl) ⟨2231666, by rfl⟩ : syracuseStep 2975555 = 4463333) B4463333
theorem B1983703 : Blo 1983435 1983703 := bstep (se 1 (by rfl) ⟨1487777, by rfl⟩ : syracuseStep 1983703 = 2975555) B2975555
theorem B5021261 : Blo 1983435 5021261 := bbase (se 3 (by rfl) ⟨941486, by rfl⟩ : syracuseStep 5021261 = 1882973) (by norm_num)
theorem B3347507 : Blo 1983435 3347507 := bstep (se 1 (by rfl) ⟨2510630, by rfl⟩ : syracuseStep 3347507 = 5021261) B5021261
theorem B2231671 : Blo 1983435 2231671 := bstep (se 1 (by rfl) ⟨1673753, by rfl⟩ : syracuseStep 2231671 = 3347507) B3347507
theorem B2975561 : Blo 1983435 2975561 := bstep (se 2 (by rfl) ⟨1115835, by rfl⟩ : syracuseStep 2975561 = 2231671) B2231671
theorem B1983707 : Blo 1983435 1983707 := bstep (se 1 (by rfl) ⟨1487780, by rfl⟩ : syracuseStep 1983707 = 2975561) B2975561
theorem B2118349 : Blo 1983435 2118349 := bbase (se 3 (by rfl) ⟨397190, by rfl⟩ : syracuseStep 2118349 = 794381) (by norm_num)
theorem B2824465 : Blo 1983435 2824465 := bstep (se 2 (by rfl) ⟨1059174, by rfl⟩ : syracuseStep 2824465 = 2118349) B2118349
theorem B3765953 : Blo 1983435 3765953 := bstep (se 2 (by rfl) ⟨1412232, by rfl⟩ : syracuseStep 3765953 = 2824465) B2824465
theorem B10042541 : Blo 1983435 10042541 := bstep (se 3 (by rfl) ⟨1882976, by rfl⟩ : syracuseStep 10042541 = 3765953) B3765953
theorem B6695027 : Blo 1983435 6695027 := bstep (se 1 (by rfl) ⟨5021270, by rfl⟩ : syracuseStep 6695027 = 10042541) B10042541
theorem B4463351 : Blo 1983435 4463351 := bstep (se 1 (by rfl) ⟨3347513, by rfl⟩ : syracuseStep 4463351 = 6695027) B6695027
theorem B2975567 : Blo 1983435 2975567 := bstep (se 1 (by rfl) ⟨2231675, by rfl⟩ : syracuseStep 2975567 = 4463351) B4463351
theorem B1983711 : Blo 1983435 1983711 := bstep (se 1 (by rfl) ⟨1487783, by rfl⟩ : syracuseStep 1983711 = 2975567) B2975567
theorem B2975573 : Blo 1983435 2975573 := bbase (se 9 (by rfl) ⟨8717, by rfl⟩ : syracuseStep 2975573 = 17435) (by norm_num)
theorem B1983715 : Blo 1983435 1983715 := bstep (se 1 (by rfl) ⟨1487786, by rfl⟩ : syracuseStep 1983715 = 2975573) B2975573
theorem B6032357 : Blo 1983435 6032357 := bbase (se 4 (by rfl) ⟨565533, by rfl⟩ : syracuseStep 6032357 = 1131067) (by norm_num)
theorem B4021571 : Blo 1983435 4021571 := bstep (se 1 (by rfl) ⟨3016178, by rfl⟩ : syracuseStep 4021571 = 6032357) B6032357
theorem B2681047 : Blo 1983435 2681047 := bstep (se 1 (by rfl) ⟨2010785, by rfl⟩ : syracuseStep 2681047 = 4021571) B4021571
theorem B3574729 : Blo 1983435 3574729 := bstep (se 2 (by rfl) ⟨1340523, by rfl⟩ : syracuseStep 3574729 = 2681047) B2681047
theorem B4766305 : Blo 1983435 4766305 := bstep (se 2 (by rfl) ⟨1787364, by rfl⟩ : syracuseStep 4766305 = 3574729) B3574729
theorem B6355073 : Blo 1983435 6355073 := bstep (se 2 (by rfl) ⟨2383152, by rfl⟩ : syracuseStep 6355073 = 4766305) B4766305
theorem B4236715 : Blo 1983435 4236715 := bstep (se 1 (by rfl) ⟨3177536, by rfl⟩ : syracuseStep 4236715 = 6355073) B6355073
theorem B5648953 : Blo 1983435 5648953 := bstep (se 2 (by rfl) ⟨2118357, by rfl⟩ : syracuseStep 5648953 = 4236715) B4236715
theorem B7531937 : Blo 1983435 7531937 := bstep (se 2 (by rfl) ⟨2824476, by rfl⟩ : syracuseStep 7531937 = 5648953) B5648953
theorem B5021291 : Blo 1983435 5021291 := bstep (se 1 (by rfl) ⟨3765968, by rfl⟩ : syracuseStep 5021291 = 7531937) B7531937
theorem B3347527 : Blo 1983435 3347527 := bstep (se 1 (by rfl) ⟨2510645, by rfl⟩ : syracuseStep 3347527 = 5021291) B5021291
theorem B4463369 : Blo 1983435 4463369 := bstep (se 2 (by rfl) ⟨1673763, by rfl⟩ : syracuseStep 4463369 = 3347527) B3347527
theorem B2975579 : Blo 1983435 2975579 := bstep (se 1 (by rfl) ⟨2231684, by rfl⟩ : syracuseStep 2975579 = 4463369) B4463369
theorem B1983719 : Blo 1983435 1983719 := bstep (se 1 (by rfl) ⟨1487789, by rfl⟩ : syracuseStep 1983719 = 2975579) B2975579
theorem B2231689 : Blo 1983435 2231689 := bbase (se 2 (by rfl) ⟨836883, by rfl⟩ : syracuseStep 2231689 = 1673767) (by norm_num)
theorem B2975585 : Blo 1983435 2975585 := bstep (se 2 (by rfl) ⟨1115844, by rfl⟩ : syracuseStep 2975585 = 2231689) B2231689
theorem B1983723 : Blo 1983435 1983723 := bstep (se 1 (by rfl) ⟨1487792, by rfl⟩ : syracuseStep 1983723 = 2975585) B2975585
theorem B28988117 : Blo 1983435 28988117 := bbase (se 7 (by rfl) ⟨339704, by rfl⟩ : syracuseStep 28988117 = 679409) (by norm_num)
theorem B19325411 : Blo 1983435 19325411 := bstep (se 1 (by rfl) ⟨14494058, by rfl⟩ : syracuseStep 19325411 = 28988117) B28988117
theorem B12883607 : Blo 1983435 12883607 := bstep (se 1 (by rfl) ⟨9662705, by rfl⟩ : syracuseStep 12883607 = 19325411) B19325411
theorem B8589071 : Blo 1983435 8589071 := bstep (se 1 (by rfl) ⟨6441803, by rfl⟩ : syracuseStep 8589071 = 12883607) B12883607
theorem B5726047 : Blo 1983435 5726047 := bstep (se 1 (by rfl) ⟨4294535, by rfl⟩ : syracuseStep 5726047 = 8589071) B8589071
theorem B7634729 : Blo 1983435 7634729 := bstep (se 2 (by rfl) ⟨2863023, by rfl⟩ : syracuseStep 7634729 = 5726047) B5726047
theorem B20359277 : Blo 1983435 20359277 := bstep (se 3 (by rfl) ⟨3817364, by rfl⟩ : syracuseStep 20359277 = 7634729) B7634729
theorem B13572851 : Blo 1983435 13572851 := bstep (se 1 (by rfl) ⟨10179638, by rfl⟩ : syracuseStep 13572851 = 20359277) B20359277
theorem B144777077 : Blo 1983435 144777077 := bstep (se 5 (by rfl) ⟨6786425, by rfl⟩ : syracuseStep 144777077 = 13572851) B13572851
theorem B96518051 : Blo 1983435 96518051 := bstep (se 1 (by rfl) ⟨72388538, by rfl⟩ : syracuseStep 96518051 = 144777077) B144777077
theorem B64345367 : Blo 1983435 64345367 := bstep (se 1 (by rfl) ⟨48259025, by rfl⟩ : syracuseStep 64345367 = 96518051) B96518051
theorem B42896911 : Blo 1983435 42896911 := bstep (se 1 (by rfl) ⟨32172683, by rfl⟩ : syracuseStep 42896911 = 64345367) B64345367
theorem B57195881 : Blo 1983435 57195881 := bstep (se 2 (by rfl) ⟨21448455, by rfl⟩ : syracuseStep 57195881 = 42896911) B42896911
theorem B38130587 : Blo 1983435 38130587 := bstep (se 1 (by rfl) ⟨28597940, by rfl⟩ : syracuseStep 38130587 = 57195881) B57195881
theorem B25420391 : Blo 1983435 25420391 := bstep (se 1 (by rfl) ⟨19065293, by rfl⟩ : syracuseStep 25420391 = 38130587) B38130587
theorem B16946927 : Blo 1983435 16946927 := bstep (se 1 (by rfl) ⟨12710195, by rfl⟩ : syracuseStep 16946927 = 25420391) B25420391
theorem B11297951 : Blo 1983435 11297951 := bstep (se 1 (by rfl) ⟨8473463, by rfl⟩ : syracuseStep 11297951 = 16946927) B16946927
theorem B7531967 : Blo 1983435 7531967 := bstep (se 1 (by rfl) ⟨5648975, by rfl⟩ : syracuseStep 7531967 = 11297951) B11297951
theorem B5021311 : Blo 1983435 5021311 := bstep (se 1 (by rfl) ⟨3765983, by rfl⟩ : syracuseStep 5021311 = 7531967) B7531967
theorem B6695081 : Blo 1983435 6695081 := bstep (se 2 (by rfl) ⟨2510655, by rfl⟩ : syracuseStep 6695081 = 5021311) B5021311
theorem B4463387 : Blo 1983435 4463387 := bstep (se 1 (by rfl) ⟨3347540, by rfl⟩ : syracuseStep 4463387 = 6695081) B6695081
theorem B2975591 : Blo 1983435 2975591 := bstep (se 1 (by rfl) ⟨2231693, by rfl⟩ : syracuseStep 2975591 = 4463387) B4463387
theorem B1983727 : Blo 1983435 1983727 := bstep (se 1 (by rfl) ⟨1487795, by rfl⟩ : syracuseStep 1983727 = 2975591) B2975591
theorem B2975597 : Blo 1983435 2975597 := bbase (se 3 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 2975597 = 1115849) (by norm_num)
theorem B1983731 : Blo 1983435 1983731 := bstep (se 1 (by rfl) ⟨1487798, by rfl⟩ : syracuseStep 1983731 = 2975597) B2975597
theorem B4463405 : Blo 1983435 4463405 := bbase (se 3 (by rfl) ⟨836888, by rfl⟩ : syracuseStep 4463405 = 1673777) (by norm_num)
theorem B2975603 : Blo 1983435 2975603 := bstep (se 1 (by rfl) ⟨2231702, by rfl⟩ : syracuseStep 2975603 = 4463405) B4463405
theorem B1983735 : Blo 1983435 1983735 := bstep (se 1 (by rfl) ⟨1487801, by rfl⟩ : syracuseStep 1983735 = 2975603) B2975603
theorem B2383177 : Blo 1983435 2383177 := bbase (se 2 (by rfl) ⟨893691, by rfl⟩ : syracuseStep 2383177 = 1787383) (by norm_num)
theorem B3177569 : Blo 1983435 3177569 := bstep (se 2 (by rfl) ⟨1191588, by rfl⟩ : syracuseStep 3177569 = 2383177) B2383177
theorem B8473517 : Blo 1983435 8473517 := bstep (se 3 (by rfl) ⟨1588784, by rfl⟩ : syracuseStep 8473517 = 3177569) B3177569
theorem B5649011 : Blo 1983435 5649011 := bstep (se 1 (by rfl) ⟨4236758, by rfl⟩ : syracuseStep 5649011 = 8473517) B8473517
theorem B3766007 : Blo 1983435 3766007 := bstep (se 1 (by rfl) ⟨2824505, by rfl⟩ : syracuseStep 3766007 = 5649011) B5649011
theorem B2510671 : Blo 1983435 2510671 := bstep (se 1 (by rfl) ⟨1883003, by rfl⟩ : syracuseStep 2510671 = 3766007) B3766007
theorem B3347561 : Blo 1983435 3347561 := bstep (se 2 (by rfl) ⟨1255335, by rfl⟩ : syracuseStep 3347561 = 2510671) B2510671
theorem B2231707 : Blo 1983435 2231707 := bstep (se 1 (by rfl) ⟨1673780, by rfl⟩ : syracuseStep 2231707 = 3347561) B3347561
theorem B2975609 : Blo 1983435 2975609 := bstep (se 2 (by rfl) ⟨1115853, by rfl⟩ : syracuseStep 2975609 = 2231707) B2231707
theorem B1983739 : Blo 1983435 1983739 := bstep (se 1 (by rfl) ⟨1487804, by rfl⟩ : syracuseStep 1983739 = 2975609) B2975609
theorem B2010809 : Blo 1983435 2010809 := bbase (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) (by norm_num)
theorem B5362157 : Blo 1983435 5362157 := bstep (se 3 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 5362157 = 2010809) B2010809
theorem B14299085 : Blo 1983435 14299085 := bstep (se 3 (by rfl) ⟨2681078, by rfl⟩ : syracuseStep 14299085 = 5362157) B5362157
theorem B9532723 : Blo 1983435 9532723 := bstep (se 1 (by rfl) ⟨7149542, by rfl⟩ : syracuseStep 9532723 = 14299085) B14299085
theorem B12710297 : Blo 1983435 12710297 := bstep (se 2 (by rfl) ⟨4766361, by rfl⟩ : syracuseStep 12710297 = 9532723) B9532723
theorem B33894125 : Blo 1983435 33894125 := bstep (se 3 (by rfl) ⟨6355148, by rfl⟩ : syracuseStep 33894125 = 12710297) B12710297
theorem B22596083 : Blo 1983435 22596083 := bstep (se 1 (by rfl) ⟨16947062, by rfl⟩ : syracuseStep 22596083 = 33894125) B33894125
theorem B15064055 : Blo 1983435 15064055 := bstep (se 1 (by rfl) ⟨11298041, by rfl⟩ : syracuseStep 15064055 = 22596083) B22596083
theorem B10042703 : Blo 1983435 10042703 := bstep (se 1 (by rfl) ⟨7532027, by rfl⟩ : syracuseStep 10042703 = 15064055) B15064055
theorem B6695135 : Blo 1983435 6695135 := bstep (se 1 (by rfl) ⟨5021351, by rfl⟩ : syracuseStep 6695135 = 10042703) B10042703
theorem B4463423 : Blo 1983435 4463423 := bstep (se 1 (by rfl) ⟨3347567, by rfl⟩ : syracuseStep 4463423 = 6695135) B6695135
theorem B2975615 : Blo 1983435 2975615 := bstep (se 1 (by rfl) ⟨2231711, by rfl⟩ : syracuseStep 2975615 = 4463423) B4463423
theorem B1983743 : Blo 1983435 1983743 := bstep (se 1 (by rfl) ⟨1487807, by rfl⟩ : syracuseStep 1983743 = 2975615) B2975615
theorem B2975621 : Blo 1983435 2975621 := bbase (se 4 (by rfl) ⟨278964, by rfl⟩ : syracuseStep 2975621 = 557929) (by norm_num)
theorem B1983747 : Blo 1983435 1983747 := bstep (se 1 (by rfl) ⟨1487810, by rfl⟩ : syracuseStep 1983747 = 2975621) B2975621
theorem B3347581 : Blo 1983435 3347581 := bbase (se 3 (by rfl) ⟨627671, by rfl⟩ : syracuseStep 3347581 = 1255343) (by norm_num)
theorem B4463441 : Blo 1983435 4463441 := bstep (se 2 (by rfl) ⟨1673790, by rfl⟩ : syracuseStep 4463441 = 3347581) B3347581
theorem B2975627 : Blo 1983435 2975627 := bstep (se 1 (by rfl) ⟨2231720, by rfl⟩ : syracuseStep 2975627 = 4463441) B4463441
theorem B1983751 : Blo 1983435 1983751 := bstep (se 1 (by rfl) ⟨1487813, by rfl⟩ : syracuseStep 1983751 = 2975627) B2975627
theorem B2231725 : Blo 1983435 2231725 := bbase (se 3 (by rfl) ⟨418448, by rfl⟩ : syracuseStep 2231725 = 836897) (by norm_num)
theorem B2975633 : Blo 1983435 2975633 := bstep (se 2 (by rfl) ⟨1115862, by rfl⟩ : syracuseStep 2975633 = 2231725) B2231725
theorem B1983755 : Blo 1983435 1983755 := bstep (se 1 (by rfl) ⟨1487816, by rfl⟩ : syracuseStep 1983755 = 2975633) B2975633
theorem B6695189 : Blo 1983435 6695189 := bbase (se 6 (by rfl) ⟨156918, by rfl⟩ : syracuseStep 6695189 = 313837) (by norm_num)
theorem B4463459 : Blo 1983435 4463459 := bstep (se 1 (by rfl) ⟨3347594, by rfl⟩ : syracuseStep 4463459 = 6695189) B6695189
theorem B2975639 : Blo 1983435 2975639 := bstep (se 1 (by rfl) ⟨2231729, by rfl⟩ : syracuseStep 2975639 = 4463459) B4463459
theorem B1983759 : Blo 1983435 1983759 := bstep (se 1 (by rfl) ⟨1487819, by rfl⟩ : syracuseStep 1983759 = 2975639) B2975639
theorem B2975645 : Blo 1983435 2975645 := bbase (se 3 (by rfl) ⟨557933, by rfl⟩ : syracuseStep 2975645 = 1115867) (by norm_num)
theorem B1983763 : Blo 1983435 1983763 := bstep (se 1 (by rfl) ⟨1487822, by rfl⟩ : syracuseStep 1983763 = 2975645) B2975645
theorem B4463477 : Blo 1983435 4463477 := bbase (se 5 (by rfl) ⟨209225, by rfl⟩ : syracuseStep 4463477 = 418451) (by norm_num)
theorem B2975651 : Blo 1983435 2975651 := bstep (se 1 (by rfl) ⟨2231738, by rfl⟩ : syracuseStep 2975651 = 4463477) B4463477
theorem B1983767 : Blo 1983435 1983767 := bstep (se 1 (by rfl) ⟨1487825, by rfl⟩ : syracuseStep 1983767 = 2975651) B2975651
theorem B5159381 : Blo 1983435 5159381 := bbase (se 7 (by rfl) ⟨60461, by rfl⟩ : syracuseStep 5159381 = 120923) (by norm_num)
theorem B13758349 : Blo 1983435 13758349 := bstep (se 3 (by rfl) ⟨2579690, by rfl⟩ : syracuseStep 13758349 = 5159381) B5159381
theorem B18344465 : Blo 1983435 18344465 := bstep (se 2 (by rfl) ⟨6879174, by rfl⟩ : syracuseStep 18344465 = 13758349) B13758349
theorem B12229643 : Blo 1983435 12229643 := bstep (se 1 (by rfl) ⟨9172232, by rfl⟩ : syracuseStep 12229643 = 18344465) B18344465
theorem B8153095 : Blo 1983435 8153095 := bstep (se 1 (by rfl) ⟨6114821, by rfl⟩ : syracuseStep 8153095 = 12229643) B12229643
theorem B10870793 : Blo 1983435 10870793 := bstep (se 2 (by rfl) ⟨4076547, by rfl⟩ : syracuseStep 10870793 = 8153095) B8153095
theorem B7247195 : Blo 1983435 7247195 := bstep (se 1 (by rfl) ⟨5435396, by rfl⟩ : syracuseStep 7247195 = 10870793) B10870793
theorem B4831463 : Blo 1983435 4831463 := bstep (se 1 (by rfl) ⟨3623597, by rfl⟩ : syracuseStep 4831463 = 7247195) B7247195
theorem B3220975 : Blo 1983435 3220975 := bstep (se 1 (by rfl) ⟨2415731, by rfl⟩ : syracuseStep 3220975 = 4831463) B4831463
theorem B4294633 : Blo 1983435 4294633 := bstep (se 2 (by rfl) ⟨1610487, by rfl⟩ : syracuseStep 4294633 = 3220975) B3220975
theorem B5726177 : Blo 1983435 5726177 := bstep (se 2 (by rfl) ⟨2147316, by rfl⟩ : syracuseStep 5726177 = 4294633) B4294633
theorem B3817451 : Blo 1983435 3817451 := bstep (se 1 (by rfl) ⟨2863088, by rfl⟩ : syracuseStep 3817451 = 5726177) B5726177
theorem B2544967 : Blo 1983435 2544967 := bstep (se 1 (by rfl) ⟨1908725, by rfl⟩ : syracuseStep 2544967 = 3817451) B3817451
theorem B3393289 : Blo 1983435 3393289 := bstep (se 2 (by rfl) ⟨1272483, by rfl⟩ : syracuseStep 3393289 = 2544967) B2544967
theorem B4524385 : Blo 1983435 4524385 := bstep (se 2 (by rfl) ⟨1696644, by rfl⟩ : syracuseStep 4524385 = 3393289) B3393289
theorem B6032513 : Blo 1983435 6032513 := bstep (se 2 (by rfl) ⟨2262192, by rfl⟩ : syracuseStep 6032513 = 4524385) B4524385
theorem B16086701 : Blo 1983435 16086701 := bstep (se 3 (by rfl) ⟨3016256, by rfl⟩ : syracuseStep 16086701 = 6032513) B6032513
theorem B42897869 : Blo 1983435 42897869 := bstep (se 3 (by rfl) ⟨8043350, by rfl⟩ : syracuseStep 42897869 = 16086701) B16086701
theorem B28598579 : Blo 1983435 28598579 := bstep (se 1 (by rfl) ⟨21448934, by rfl⟩ : syracuseStep 28598579 = 42897869) B42897869
theorem B19065719 : Blo 1983435 19065719 := bstep (se 1 (by rfl) ⟨14299289, by rfl⟩ : syracuseStep 19065719 = 28598579) B28598579
theorem B12710479 : Blo 1983435 12710479 := bstep (se 1 (by rfl) ⟨9532859, by rfl⟩ : syracuseStep 12710479 = 19065719) B19065719
theorem B16947305 : Blo 1983435 16947305 := bstep (se 2 (by rfl) ⟨6355239, by rfl⟩ : syracuseStep 16947305 = 12710479) B12710479
theorem B11298203 : Blo 1983435 11298203 := bstep (se 1 (by rfl) ⟨8473652, by rfl⟩ : syracuseStep 11298203 = 16947305) B16947305
theorem B7532135 : Blo 1983435 7532135 := bstep (se 1 (by rfl) ⟨5649101, by rfl⟩ : syracuseStep 7532135 = 11298203) B11298203
theorem B5021423 : Blo 1983435 5021423 := bstep (se 1 (by rfl) ⟨3766067, by rfl⟩ : syracuseStep 5021423 = 7532135) B7532135
theorem B3347615 : Blo 1983435 3347615 := bstep (se 1 (by rfl) ⟨2510711, by rfl⟩ : syracuseStep 3347615 = 5021423) B5021423
theorem B2231743 : Blo 1983435 2231743 := bstep (se 1 (by rfl) ⟨1673807, by rfl⟩ : syracuseStep 2231743 = 3347615) B3347615
theorem B2975657 : Blo 1983435 2975657 := bstep (se 2 (by rfl) ⟨1115871, by rfl⟩ : syracuseStep 2975657 = 2231743) B2231743
theorem B1983771 : Blo 1983435 1983771 := bstep (se 1 (by rfl) ⟨1487828, by rfl⟩ : syracuseStep 1983771 = 2975657) B2975657
theorem B7532149 : Blo 1983435 7532149 := bbase (se 5 (by rfl) ⟨353069, by rfl⟩ : syracuseStep 7532149 = 706139) (by norm_num)
theorem B10042865 : Blo 1983435 10042865 := bstep (se 2 (by rfl) ⟨3766074, by rfl⟩ : syracuseStep 10042865 = 7532149) B7532149
theorem B6695243 : Blo 1983435 6695243 := bstep (se 1 (by rfl) ⟨5021432, by rfl⟩ : syracuseStep 6695243 = 10042865) B10042865
theorem B4463495 : Blo 1983435 4463495 := bstep (se 1 (by rfl) ⟨3347621, by rfl⟩ : syracuseStep 4463495 = 6695243) B6695243
theorem B2975663 : Blo 1983435 2975663 := bstep (se 1 (by rfl) ⟨2231747, by rfl⟩ : syracuseStep 2975663 = 4463495) B4463495
theorem B1983775 : Blo 1983435 1983775 := bstep (se 1 (by rfl) ⟨1487831, by rfl⟩ : syracuseStep 1983775 = 2975663) B2975663
theorem B2975669 : Blo 1983435 2975669 := bbase (se 5 (by rfl) ⟨139484, by rfl⟩ : syracuseStep 2975669 = 278969) (by norm_num)
theorem B1983779 : Blo 1983435 1983779 := bstep (se 1 (by rfl) ⟨1487834, by rfl⟩ : syracuseStep 1983779 = 2975669) B2975669
theorem B5021453 : Blo 1983435 5021453 := bbase (se 3 (by rfl) ⟨941522, by rfl⟩ : syracuseStep 5021453 = 1883045) (by norm_num)
theorem B3347635 : Blo 1983435 3347635 := bstep (se 1 (by rfl) ⟨2510726, by rfl⟩ : syracuseStep 3347635 = 5021453) B5021453
theorem B4463513 : Blo 1983435 4463513 := bstep (se 2 (by rfl) ⟨1673817, by rfl⟩ : syracuseStep 4463513 = 3347635) B3347635
theorem B2975675 : Blo 1983435 2975675 := bstep (se 1 (by rfl) ⟨2231756, by rfl⟩ : syracuseStep 2975675 = 4463513) B4463513
theorem B1983783 : Blo 1983435 1983783 := bstep (se 1 (by rfl) ⟨1487837, by rfl⟩ : syracuseStep 1983783 = 2975675) B2975675
theorem B2231761 : Blo 1983435 2231761 := bbase (se 2 (by rfl) ⟨836910, by rfl⟩ : syracuseStep 2231761 = 1673821) (by norm_num)
theorem B2975681 : Blo 1983435 2975681 := bstep (se 2 (by rfl) ⟨1115880, by rfl⟩ : syracuseStep 2975681 = 2231761) B2231761
theorem B1983787 : Blo 1983435 1983787 := bstep (se 1 (by rfl) ⟨1487840, by rfl⟩ : syracuseStep 1983787 = 2975681) B2975681
theorem B4236869 : Blo 1983435 4236869 := bbase (se 4 (by rfl) ⟨397206, by rfl⟩ : syracuseStep 4236869 = 794413) (by norm_num)
theorem B2824579 : Blo 1983435 2824579 := bstep (se 1 (by rfl) ⟨2118434, by rfl⟩ : syracuseStep 2824579 = 4236869) B4236869
theorem B3766105 : Blo 1983435 3766105 := bstep (se 2 (by rfl) ⟨1412289, by rfl⟩ : syracuseStep 3766105 = 2824579) B2824579
theorem B5021473 : Blo 1983435 5021473 := bstep (se 2 (by rfl) ⟨1883052, by rfl⟩ : syracuseStep 5021473 = 3766105) B3766105
theorem B6695297 : Blo 1983435 6695297 := bstep (se 2 (by rfl) ⟨2510736, by rfl⟩ : syracuseStep 6695297 = 5021473) B5021473
theorem B4463531 : Blo 1983435 4463531 := bstep (se 1 (by rfl) ⟨3347648, by rfl⟩ : syracuseStep 4463531 = 6695297) B6695297
theorem B2975687 : Blo 1983435 2975687 := bstep (se 1 (by rfl) ⟨2231765, by rfl⟩ : syracuseStep 2975687 = 4463531) B4463531
theorem B1983791 : Blo 1983435 1983791 := bstep (se 1 (by rfl) ⟨1487843, by rfl⟩ : syracuseStep 1983791 = 2975687) B2975687
theorem B2975693 : Blo 1983435 2975693 := bbase (se 3 (by rfl) ⟨557942, by rfl⟩ : syracuseStep 2975693 = 1115885) (by norm_num)
theorem B1983795 : Blo 1983435 1983795 := bstep (se 1 (by rfl) ⟨1487846, by rfl⟩ : syracuseStep 1983795 = 2975693) B2975693
theorem B4463549 : Blo 1983435 4463549 := bbase (se 3 (by rfl) ⟨836915, by rfl⟩ : syracuseStep 4463549 = 1673831) (by norm_num)
theorem B2975699 : Blo 1983435 2975699 := bstep (se 1 (by rfl) ⟨2231774, by rfl⟩ : syracuseStep 2975699 = 4463549) B4463549
theorem B1983799 : Blo 1983435 1983799 := bstep (se 1 (by rfl) ⟨1487849, by rfl⟩ : syracuseStep 1983799 = 2975699) B2975699
theorem B3347669 : Blo 1983435 3347669 := bbase (se 7 (by rfl) ⟨39230, by rfl⟩ : syracuseStep 3347669 = 78461) (by norm_num)
theorem B2231779 : Blo 1983435 2231779 := bstep (se 1 (by rfl) ⟨1673834, by rfl⟩ : syracuseStep 2231779 = 3347669) B3347669
theorem B2975705 : Blo 1983435 2975705 := bstep (se 2 (by rfl) ⟨1115889, by rfl⟩ : syracuseStep 2975705 = 2231779) B2231779
theorem B1983803 : Blo 1983435 1983803 := bstep (se 1 (by rfl) ⟨1487852, by rfl⟩ : syracuseStep 1983803 = 2975705) B2975705
theorem B3177677 : Blo 1983435 3177677 := bbase (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) (by norm_num)
theorem B8473805 : Blo 1983435 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B5649203 : Blo 1983435 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B15064541 : Blo 1983435 15064541 := bstep (se 3 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 15064541 = 5649203) B5649203
theorem B10043027 : Blo 1983435 10043027 := bstep (se 1 (by rfl) ⟨7532270, by rfl⟩ : syracuseStep 10043027 = 15064541) B15064541
theorem B6695351 : Blo 1983435 6695351 := bstep (se 1 (by rfl) ⟨5021513, by rfl⟩ : syracuseStep 6695351 = 10043027) B10043027
theorem B4463567 : Blo 1983435 4463567 := bstep (se 1 (by rfl) ⟨3347675, by rfl⟩ : syracuseStep 4463567 = 6695351) B6695351
theorem B2975711 : Blo 1983435 2975711 := bstep (se 1 (by rfl) ⟨2231783, by rfl⟩ : syracuseStep 2975711 = 4463567) B4463567
theorem B1983807 : Blo 1983435 1983807 := bstep (se 1 (by rfl) ⟨1487855, by rfl⟩ : syracuseStep 1983807 = 2975711) B2975711
theorem B2975717 : Blo 1983435 2975717 := bbase (se 4 (by rfl) ⟨278973, by rfl⟩ : syracuseStep 2975717 = 557947) (by norm_num)
theorem B1983811 : Blo 1983435 1983811 := bstep (se 1 (by rfl) ⟨1487858, by rfl⟩ : syracuseStep 1983811 = 2975717) B2975717
theorem B6355381 : Blo 1983435 6355381 := bbase (se 5 (by rfl) ⟨297908, by rfl⟩ : syracuseStep 6355381 = 595817) (by norm_num)
theorem B8473841 : Blo 1983435 8473841 := bstep (se 2 (by rfl) ⟨3177690, by rfl⟩ : syracuseStep 8473841 = 6355381) B6355381
theorem B5649227 : Blo 1983435 5649227 := bstep (se 1 (by rfl) ⟨4236920, by rfl⟩ : syracuseStep 5649227 = 8473841) B8473841
theorem B3766151 : Blo 1983435 3766151 := bstep (se 1 (by rfl) ⟨2824613, by rfl⟩ : syracuseStep 3766151 = 5649227) B5649227
theorem B2510767 : Blo 1983435 2510767 := bstep (se 1 (by rfl) ⟨1883075, by rfl⟩ : syracuseStep 2510767 = 3766151) B3766151
theorem B3347689 : Blo 1983435 3347689 := bstep (se 2 (by rfl) ⟨1255383, by rfl⟩ : syracuseStep 3347689 = 2510767) B2510767
theorem B4463585 : Blo 1983435 4463585 := bstep (se 2 (by rfl) ⟨1673844, by rfl⟩ : syracuseStep 4463585 = 3347689) B3347689
theorem B2975723 : Blo 1983435 2975723 := bstep (se 1 (by rfl) ⟨2231792, by rfl⟩ : syracuseStep 2975723 = 4463585) B4463585
theorem B1983815 : Blo 1983435 1983815 := bstep (se 1 (by rfl) ⟨1487861, by rfl⟩ : syracuseStep 1983815 = 2975723) B2975723
theorem B2231797 : Blo 1983435 2231797 := bbase (se 5 (by rfl) ⟨104615, by rfl⟩ : syracuseStep 2231797 = 209231) (by norm_num)
theorem B2975729 : Blo 1983435 2975729 := bstep (se 2 (by rfl) ⟨1115898, by rfl⟩ : syracuseStep 2975729 = 2231797) B2231797
theorem B1983819 : Blo 1983435 1983819 := bstep (se 1 (by rfl) ⟨1487864, by rfl⟩ : syracuseStep 1983819 = 2975729) B2975729
theorem B2510777 : Blo 1983435 2510777 := bbase (se 2 (by rfl) ⟨941541, by rfl⟩ : syracuseStep 2510777 = 1883083) (by norm_num)
theorem B6695405 : Blo 1983435 6695405 := bstep (se 3 (by rfl) ⟨1255388, by rfl⟩ : syracuseStep 6695405 = 2510777) B2510777
theorem B4463603 : Blo 1983435 4463603 := bstep (se 1 (by rfl) ⟨3347702, by rfl⟩ : syracuseStep 4463603 = 6695405) B6695405
theorem B2975735 : Blo 1983435 2975735 := bstep (se 1 (by rfl) ⟨2231801, by rfl⟩ : syracuseStep 2975735 = 4463603) B4463603
theorem B1983823 : Blo 1983435 1983823 := bstep (se 1 (by rfl) ⟨1487867, by rfl⟩ : syracuseStep 1983823 = 2975735) B2975735
theorem B2975741 : Blo 1983435 2975741 := bbase (se 3 (by rfl) ⟨557951, by rfl⟩ : syracuseStep 2975741 = 1115903) (by norm_num)
theorem B1983827 : Blo 1983435 1983827 := bstep (se 1 (by rfl) ⟨1487870, by rfl⟩ : syracuseStep 1983827 = 2975741) B2975741
theorem B4463621 : Blo 1983435 4463621 := bbase (se 4 (by rfl) ⟨418464, by rfl⟩ : syracuseStep 4463621 = 836929) (by norm_num)
theorem B2975747 : Blo 1983435 2975747 := bstep (se 1 (by rfl) ⟨2231810, by rfl⟩ : syracuseStep 2975747 = 4463621) B4463621
theorem B1983831 : Blo 1983435 1983831 := bstep (se 1 (by rfl) ⟨1487873, by rfl⟩ : syracuseStep 1983831 = 2975747) B2975747
theorem B3766189 : Blo 1983435 3766189 := bbase (se 3 (by rfl) ⟨706160, by rfl⟩ : syracuseStep 3766189 = 1412321) (by norm_num)
theorem B5021585 : Blo 1983435 5021585 := bstep (se 2 (by rfl) ⟨1883094, by rfl⟩ : syracuseStep 5021585 = 3766189) B3766189
theorem B3347723 : Blo 1983435 3347723 := bstep (se 1 (by rfl) ⟨2510792, by rfl⟩ : syracuseStep 3347723 = 5021585) B5021585
theorem B2231815 : Blo 1983435 2231815 := bstep (se 1 (by rfl) ⟨1673861, by rfl⟩ : syracuseStep 2231815 = 3347723) B3347723
theorem B2975753 : Blo 1983435 2975753 := bstep (se 2 (by rfl) ⟨1115907, by rfl⟩ : syracuseStep 2975753 = 2231815) B2231815
theorem B1983835 : Blo 1983435 1983835 := bstep (se 1 (by rfl) ⟨1487876, by rfl⟩ : syracuseStep 1983835 = 2975753) B2975753
theorem B10043189 : Blo 1983435 10043189 := bbase (se 5 (by rfl) ⟨470774, by rfl⟩ : syracuseStep 10043189 = 941549) (by norm_num)
theorem B6695459 : Blo 1983435 6695459 := bstep (se 1 (by rfl) ⟨5021594, by rfl⟩ : syracuseStep 6695459 = 10043189) B10043189
theorem B4463639 : Blo 1983435 4463639 := bstep (se 1 (by rfl) ⟨3347729, by rfl⟩ : syracuseStep 4463639 = 6695459) B6695459
theorem B2975759 : Blo 1983435 2975759 := bstep (se 1 (by rfl) ⟨2231819, by rfl⟩ : syracuseStep 2975759 = 4463639) B4463639
theorem B1983839 : Blo 1983435 1983839 := bstep (se 1 (by rfl) ⟨1487879, by rfl⟩ : syracuseStep 1983839 = 2975759) B2975759
theorem B2975765 : Blo 1983435 2975765 := bbase (se 6 (by rfl) ⟨69744, by rfl⟩ : syracuseStep 2975765 = 139489) (by norm_num)
theorem B1983843 : Blo 1983435 1983843 := bstep (se 1 (by rfl) ⟨1487882, by rfl⟩ : syracuseStep 1983843 = 2975765) B2975765
theorem B12710965 : Blo 1983435 12710965 := bbase (se 5 (by rfl) ⟨595826, by rfl⟩ : syracuseStep 12710965 = 1191653) (by norm_num)
theorem B16947953 : Blo 1983435 16947953 := bstep (se 2 (by rfl) ⟨6355482, by rfl⟩ : syracuseStep 16947953 = 12710965) B12710965
theorem B11298635 : Blo 1983435 11298635 := bstep (se 1 (by rfl) ⟨8473976, by rfl⟩ : syracuseStep 11298635 = 16947953) B16947953
theorem B7532423 : Blo 1983435 7532423 := bstep (se 1 (by rfl) ⟨5649317, by rfl⟩ : syracuseStep 7532423 = 11298635) B11298635
theorem B5021615 : Blo 1983435 5021615 := bstep (se 1 (by rfl) ⟨3766211, by rfl⟩ : syracuseStep 5021615 = 7532423) B7532423
theorem B3347743 : Blo 1983435 3347743 := bstep (se 1 (by rfl) ⟨2510807, by rfl⟩ : syracuseStep 3347743 = 5021615) B5021615
theorem B4463657 : Blo 1983435 4463657 := bstep (se 2 (by rfl) ⟨1673871, by rfl⟩ : syracuseStep 4463657 = 3347743) B3347743
theorem B2975771 : Blo 1983435 2975771 := bstep (se 1 (by rfl) ⟨2231828, by rfl⟩ : syracuseStep 2975771 = 4463657) B4463657
theorem B1983847 : Blo 1983435 1983847 := bstep (se 1 (by rfl) ⟨1487885, by rfl⟩ : syracuseStep 1983847 = 2975771) B2975771
theorem B2231833 : Blo 1983435 2231833 := bbase (se 2 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 2231833 = 1673875) (by norm_num)
theorem B2975777 : Blo 1983435 2975777 := bstep (se 2 (by rfl) ⟨1115916, by rfl⟩ : syracuseStep 2975777 = 2231833) B2231833
theorem B1983851 : Blo 1983435 1983851 := bstep (se 1 (by rfl) ⟨1487888, by rfl⟩ : syracuseStep 1983851 = 2975777) B2975777
theorem B7532453 : Blo 1983435 7532453 := bbase (se 4 (by rfl) ⟨706167, by rfl⟩ : syracuseStep 7532453 = 1412335) (by norm_num)
theorem B5021635 : Blo 1983435 5021635 := bstep (se 1 (by rfl) ⟨3766226, by rfl⟩ : syracuseStep 5021635 = 7532453) B7532453
theorem B6695513 : Blo 1983435 6695513 := bstep (se 2 (by rfl) ⟨2510817, by rfl⟩ : syracuseStep 6695513 = 5021635) B5021635
theorem B4463675 : Blo 1983435 4463675 := bstep (se 1 (by rfl) ⟨3347756, by rfl⟩ : syracuseStep 4463675 = 6695513) B6695513
theorem B2975783 : Blo 1983435 2975783 := bstep (se 1 (by rfl) ⟨2231837, by rfl⟩ : syracuseStep 2975783 = 4463675) B4463675
theorem B1983855 : Blo 1983435 1983855 := bstep (se 1 (by rfl) ⟨1487891, by rfl⟩ : syracuseStep 1983855 = 2975783) B2975783
theorem B2975789 : Blo 1983435 2975789 := bbase (se 3 (by rfl) ⟨557960, by rfl⟩ : syracuseStep 2975789 = 1115921) (by norm_num)
theorem B1983859 : Blo 1983435 1983859 := bstep (se 1 (by rfl) ⟨1487894, by rfl⟩ : syracuseStep 1983859 = 2975789) B2975789
theorem B4463693 : Blo 1983435 4463693 := bbase (se 3 (by rfl) ⟨836942, by rfl⟩ : syracuseStep 4463693 = 1673885) (by norm_num)
theorem B2975795 : Blo 1983435 2975795 := bstep (se 1 (by rfl) ⟨2231846, by rfl⟩ : syracuseStep 2975795 = 4463693) B4463693
theorem B1983863 : Blo 1983435 1983863 := bstep (se 1 (by rfl) ⟨1487897, by rfl⟩ : syracuseStep 1983863 = 2975795) B2975795
theorem B2510833 : Blo 1983435 2510833 := bbase (se 2 (by rfl) ⟨941562, by rfl⟩ : syracuseStep 2510833 = 1883125) (by norm_num)
theorem B3347777 : Blo 1983435 3347777 := bstep (se 2 (by rfl) ⟨1255416, by rfl⟩ : syracuseStep 3347777 = 2510833) B2510833
theorem B2231851 : Blo 1983435 2231851 := bstep (se 1 (by rfl) ⟨1673888, by rfl⟩ : syracuseStep 2231851 = 3347777) B3347777
theorem B2975801 : Blo 1983435 2975801 := bstep (se 2 (by rfl) ⟨1115925, by rfl⟩ : syracuseStep 2975801 = 2231851) B2231851
theorem B1983867 : Blo 1983435 1983867 := bstep (se 1 (by rfl) ⟨1487900, by rfl⟩ : syracuseStep 1983867 = 2975801) B2975801
theorem B4303829 : Blo 1983435 4303829 := bbase (se 7 (by rfl) ⟨50435, by rfl⟩ : syracuseStep 4303829 = 100871) (by norm_num)
theorem B2869219 : Blo 1983435 2869219 := bstep (se 1 (by rfl) ⟨2151914, by rfl⟩ : syracuseStep 2869219 = 4303829) B4303829
theorem B3825625 : Blo 1983435 3825625 := bstep (se 2 (by rfl) ⟨1434609, by rfl⟩ : syracuseStep 3825625 = 2869219) B2869219
theorem B5100833 : Blo 1983435 5100833 := bstep (se 2 (by rfl) ⟨1912812, by rfl⟩ : syracuseStep 5100833 = 3825625) B3825625
theorem B3400555 : Blo 1983435 3400555 := bstep (se 1 (by rfl) ⟨2550416, by rfl⟩ : syracuseStep 3400555 = 5100833) B5100833
theorem B4534073 : Blo 1983435 4534073 := bstep (se 2 (by rfl) ⟨1700277, by rfl⟩ : syracuseStep 4534073 = 3400555) B3400555
theorem B3022715 : Blo 1983435 3022715 := bstep (se 1 (by rfl) ⟨2267036, by rfl⟩ : syracuseStep 3022715 = 4534073) B4534073
theorem B2015143 : Blo 1983435 2015143 := bstep (se 1 (by rfl) ⟨1511357, by rfl⟩ : syracuseStep 2015143 = 3022715) B3022715
theorem B10747429 : Blo 1983435 10747429 := bstep (se 4 (by rfl) ⟨1007571, by rfl⟩ : syracuseStep 10747429 = 2015143) B2015143
theorem B229278485 : Blo 1983435 229278485 := bstep (se 6 (by rfl) ⟨5373714, by rfl⟩ : syracuseStep 229278485 = 10747429) B10747429
theorem B611409293 : Blo 1983435 611409293 := bstep (se 3 (by rfl) ⟨114639242, by rfl⟩ : syracuseStep 611409293 = 229278485) B229278485
theorem B407606195 : Blo 1983435 407606195 := bstep (se 1 (by rfl) ⟨305704646, by rfl⟩ : syracuseStep 407606195 = 611409293) B611409293
theorem B1086949853 : Blo 1983435 1086949853 := bstep (se 3 (by rfl) ⟨203803097, by rfl⟩ : syracuseStep 1086949853 = 407606195) B407606195
theorem B724633235 : Blo 1983435 724633235 := bstep (se 1 (by rfl) ⟨543474926, by rfl⟩ : syracuseStep 724633235 = 1086949853) B1086949853
theorem B483088823 : Blo 1983435 483088823 := bstep (se 1 (by rfl) ⟨362316617, by rfl⟩ : syracuseStep 483088823 = 724633235) B724633235
theorem B322059215 : Blo 1983435 322059215 := bstep (se 1 (by rfl) ⟨241544411, by rfl⟩ : syracuseStep 322059215 = 483088823) B483088823
theorem B214706143 : Blo 1983435 214706143 := bstep (se 1 (by rfl) ⟨161029607, by rfl⟩ : syracuseStep 214706143 = 322059215) B322059215
theorem B286274857 : Blo 1983435 286274857 := bstep (se 2 (by rfl) ⟨107353071, by rfl⟩ : syracuseStep 286274857 = 214706143) B214706143
theorem B381699809 : Blo 1983435 381699809 := bstep (se 2 (by rfl) ⟨143137428, by rfl⟩ : syracuseStep 381699809 = 286274857) B286274857
theorem B254466539 : Blo 1983435 254466539 := bstep (se 1 (by rfl) ⟨190849904, by rfl⟩ : syracuseStep 254466539 = 381699809) B381699809
theorem B169644359 : Blo 1983435 169644359 := bstep (se 1 (by rfl) ⟨127233269, by rfl⟩ : syracuseStep 169644359 = 254466539) B254466539
theorem B452384957 : Blo 1983435 452384957 := bstep (se 3 (by rfl) ⟨84822179, by rfl⟩ : syracuseStep 452384957 = 169644359) B169644359
theorem B1206359885 : Blo 1983435 1206359885 := bstep (se 3 (by rfl) ⟨226192478, by rfl⟩ : syracuseStep 1206359885 = 452384957) B452384957
theorem B804239923 : Blo 1983435 804239923 := bstep (se 1 (by rfl) ⟨603179942, by rfl⟩ : syracuseStep 804239923 = 1206359885) B1206359885
theorem B1072319897 : Blo 1983435 1072319897 := bstep (se 2 (by rfl) ⟨402119961, by rfl⟩ : syracuseStep 1072319897 = 804239923) B804239923
theorem B714879931 : Blo 1983435 714879931 := bstep (se 1 (by rfl) ⟨536159948, by rfl⟩ : syracuseStep 714879931 = 1072319897) B1072319897
theorem B953173241 : Blo 1983435 953173241 := bstep (se 2 (by rfl) ⟨357439965, by rfl⟩ : syracuseStep 953173241 = 714879931) B714879931
theorem B635448827 : Blo 1983435 635448827 := bstep (se 1 (by rfl) ⟨476586620, by rfl⟩ : syracuseStep 635448827 = 953173241) B953173241
theorem B423632551 : Blo 1983435 423632551 := bstep (se 1 (by rfl) ⟨317724413, by rfl⟩ : syracuseStep 423632551 = 635448827) B635448827
theorem B564843401 : Blo 1983435 564843401 := bstep (se 2 (by rfl) ⟨211816275, by rfl⟩ : syracuseStep 564843401 = 423632551) B423632551
theorem B376562267 : Blo 1983435 376562267 := bstep (se 1 (by rfl) ⟨282421700, by rfl⟩ : syracuseStep 376562267 = 564843401) B564843401
theorem B251041511 : Blo 1983435 251041511 := bstep (se 1 (by rfl) ⟨188281133, by rfl⟩ : syracuseStep 251041511 = 376562267) B376562267
theorem B167361007 : Blo 1983435 167361007 := bstep (se 1 (by rfl) ⟨125520755, by rfl⟩ : syracuseStep 167361007 = 251041511) B251041511
theorem B223148009 : Blo 1983435 223148009 := bstep (se 2 (by rfl) ⟨83680503, by rfl⟩ : syracuseStep 223148009 = 167361007) B167361007
theorem B148765339 : Blo 1983435 148765339 := bstep (se 1 (by rfl) ⟨111574004, by rfl⟩ : syracuseStep 148765339 = 223148009) B223148009
theorem B198353785 : Blo 1983435 198353785 := bstep (se 2 (by rfl) ⟨74382669, by rfl⟩ : syracuseStep 198353785 = 148765339) B148765339
theorem B264471713 : Blo 1983435 264471713 := bstep (se 2 (by rfl) ⟨99176892, by rfl⟩ : syracuseStep 264471713 = 198353785) B198353785
theorem B176314475 : Blo 1983435 176314475 := bstep (se 1 (by rfl) ⟨132235856, by rfl⟩ : syracuseStep 176314475 = 264471713) B264471713
theorem B117542983 : Blo 1983435 117542983 := bstep (se 1 (by rfl) ⟨88157237, by rfl⟩ : syracuseStep 117542983 = 176314475) B176314475
theorem B156723977 : Blo 1983435 156723977 := bstep (se 2 (by rfl) ⟨58771491, by rfl⟩ : syracuseStep 156723977 = 117542983) B117542983
theorem B104482651 : Blo 1983435 104482651 := bstep (se 1 (by rfl) ⟨78361988, by rfl⟩ : syracuseStep 104482651 = 156723977) B156723977
theorem B139310201 : Blo 1983435 139310201 := bstep (se 2 (by rfl) ⟨52241325, by rfl⟩ : syracuseStep 139310201 = 104482651) B104482651
theorem B92873467 : Blo 1983435 92873467 := bstep (se 1 (by rfl) ⟨69655100, by rfl⟩ : syracuseStep 92873467 = 139310201) B139310201
theorem B123831289 : Blo 1983435 123831289 := bstep (se 2 (by rfl) ⟨46436733, by rfl⟩ : syracuseStep 123831289 = 92873467) B92873467
theorem B165108385 : Blo 1983435 165108385 := bstep (se 2 (by rfl) ⟨61915644, by rfl⟩ : syracuseStep 165108385 = 123831289) B123831289
theorem B220144513 : Blo 1983435 220144513 := bstep (se 2 (by rfl) ⟨82554192, by rfl⟩ : syracuseStep 220144513 = 165108385) B165108385
theorem B293526017 : Blo 1983435 293526017 := bstep (se 2 (by rfl) ⟨110072256, by rfl⟩ : syracuseStep 293526017 = 220144513) B220144513
theorem B195684011 : Blo 1983435 195684011 := bstep (se 1 (by rfl) ⟨146763008, by rfl⟩ : syracuseStep 195684011 = 293526017) B293526017
theorem B130456007 : Blo 1983435 130456007 := bstep (se 1 (by rfl) ⟨97842005, by rfl⟩ : syracuseStep 130456007 = 195684011) B195684011
theorem B86970671 : Blo 1983435 86970671 := bstep (se 1 (by rfl) ⟨65228003, by rfl⟩ : syracuseStep 86970671 = 130456007) B130456007
theorem B57980447 : Blo 1983435 57980447 := bstep (se 1 (by rfl) ⟨43485335, by rfl⟩ : syracuseStep 57980447 = 86970671) B86970671
theorem B38653631 : Blo 1983435 38653631 := bstep (se 1 (by rfl) ⟨28990223, by rfl⟩ : syracuseStep 38653631 = 57980447) B57980447
theorem B25769087 : Blo 1983435 25769087 := bstep (se 1 (by rfl) ⟨19326815, by rfl⟩ : syracuseStep 25769087 = 38653631) B38653631
theorem B17179391 : Blo 1983435 17179391 := bstep (se 1 (by rfl) ⟨12884543, by rfl⟩ : syracuseStep 17179391 = 25769087) B25769087
theorem B11452927 : Blo 1983435 11452927 := bstep (se 1 (by rfl) ⟨8589695, by rfl⟩ : syracuseStep 11452927 = 17179391) B17179391
theorem B15270569 : Blo 1983435 15270569 := bstep (se 2 (by rfl) ⟨5726463, by rfl⟩ : syracuseStep 15270569 = 11452927) B11452927
theorem B10180379 : Blo 1983435 10180379 := bstep (se 1 (by rfl) ⟨7635284, by rfl⟩ : syracuseStep 10180379 = 15270569) B15270569
theorem B6786919 : Blo 1983435 6786919 := bstep (se 1 (by rfl) ⟨5090189, by rfl⟩ : syracuseStep 6786919 = 10180379) B10180379
theorem B36196901 : Blo 1983435 36196901 := bstep (se 4 (by rfl) ⟨3393459, by rfl⟩ : syracuseStep 36196901 = 6786919) B6786919
theorem B24131267 : Blo 1983435 24131267 := bstep (se 1 (by rfl) ⟨18098450, by rfl⟩ : syracuseStep 24131267 = 36196901) B36196901
theorem B16087511 : Blo 1983435 16087511 := bstep (se 1 (by rfl) ⟨12065633, by rfl⟩ : syracuseStep 16087511 = 24131267) B24131267
theorem B10725007 : Blo 1983435 10725007 := bstep (se 1 (by rfl) ⟨8043755, by rfl⟩ : syracuseStep 10725007 = 16087511) B16087511
theorem B14300009 : Blo 1983435 14300009 := bstep (se 2 (by rfl) ⟨5362503, by rfl⟩ : syracuseStep 14300009 = 10725007) B10725007
theorem B9533339 : Blo 1983435 9533339 := bstep (se 1 (by rfl) ⟨7150004, by rfl⟩ : syracuseStep 9533339 = 14300009) B14300009
theorem B6355559 : Blo 1983435 6355559 := bstep (se 1 (by rfl) ⟨4766669, by rfl⟩ : syracuseStep 6355559 = 9533339) B9533339
theorem B4237039 : Blo 1983435 4237039 := bstep (se 1 (by rfl) ⟨3177779, by rfl⟩ : syracuseStep 4237039 = 6355559) B6355559
theorem B22597541 : Blo 1983435 22597541 := bstep (se 4 (by rfl) ⟨2118519, by rfl⟩ : syracuseStep 22597541 = 4237039) B4237039
theorem B15065027 : Blo 1983435 15065027 := bstep (se 1 (by rfl) ⟨11298770, by rfl⟩ : syracuseStep 15065027 = 22597541) B22597541
theorem B10043351 : Blo 1983435 10043351 := bstep (se 1 (by rfl) ⟨7532513, by rfl⟩ : syracuseStep 10043351 = 15065027) B15065027
theorem B6695567 : Blo 1983435 6695567 := bstep (se 1 (by rfl) ⟨5021675, by rfl⟩ : syracuseStep 6695567 = 10043351) B10043351
theorem B4463711 : Blo 1983435 4463711 := bstep (se 1 (by rfl) ⟨3347783, by rfl⟩ : syracuseStep 4463711 = 6695567) B6695567
theorem B2975807 : Blo 1983435 2975807 := bstep (se 1 (by rfl) ⟨2231855, by rfl⟩ : syracuseStep 2975807 = 4463711) B4463711
theorem B1983871 : Blo 1983435 1983871 := bstep (se 1 (by rfl) ⟨1487903, by rfl⟩ : syracuseStep 1983871 = 2975807) B2975807
theorem B2975813 : Blo 1983435 2975813 := bbase (se 4 (by rfl) ⟨278982, by rfl⟩ : syracuseStep 2975813 = 557965) (by norm_num)
theorem B1983875 : Blo 1983435 1983875 := bstep (se 1 (by rfl) ⟨1487906, by rfl⟩ : syracuseStep 1983875 = 2975813) B2975813
theorem B3347797 : Blo 1983435 3347797 := bbase (se 14 (by rfl) ⟨306, by rfl⟩ : syracuseStep 3347797 = 613) (by norm_num)
theorem B4463729 : Blo 1983435 4463729 := bstep (se 2 (by rfl) ⟨1673898, by rfl⟩ : syracuseStep 4463729 = 3347797) B3347797
theorem B2975819 : Blo 1983435 2975819 := bstep (se 1 (by rfl) ⟨2231864, by rfl⟩ : syracuseStep 2975819 = 4463729) B4463729
theorem B1983879 : Blo 1983435 1983879 := bstep (se 1 (by rfl) ⟨1487909, by rfl⟩ : syracuseStep 1983879 = 2975819) B2975819
theorem B2231869 : Blo 1983435 2231869 := bbase (se 3 (by rfl) ⟨418475, by rfl⟩ : syracuseStep 2231869 = 836951) (by norm_num)
theorem B2975825 : Blo 1983435 2975825 := bstep (se 2 (by rfl) ⟨1115934, by rfl⟩ : syracuseStep 2975825 = 2231869) B2231869
theorem B1983883 : Blo 1983435 1983883 := bstep (se 1 (by rfl) ⟨1487912, by rfl⟩ : syracuseStep 1983883 = 2975825) B2975825
theorem B6695621 : Blo 1983435 6695621 := bbase (se 4 (by rfl) ⟨627714, by rfl⟩ : syracuseStep 6695621 = 1255429) (by norm_num)
theorem B4463747 : Blo 1983435 4463747 := bstep (se 1 (by rfl) ⟨3347810, by rfl⟩ : syracuseStep 4463747 = 6695621) B6695621
theorem B2975831 : Blo 1983435 2975831 := bstep (se 1 (by rfl) ⟨2231873, by rfl⟩ : syracuseStep 2975831 = 4463747) B4463747
theorem B1983887 : Blo 1983435 1983887 := bstep (se 1 (by rfl) ⟨1487915, by rfl⟩ : syracuseStep 1983887 = 2975831) B2975831
theorem B2975837 : Blo 1983435 2975837 := bbase (se 3 (by rfl) ⟨557969, by rfl⟩ : syracuseStep 2975837 = 1115939) (by norm_num)
theorem B1983891 : Blo 1983435 1983891 := bstep (se 1 (by rfl) ⟨1487918, by rfl⟩ : syracuseStep 1983891 = 2975837) B2975837
theorem B4463765 : Blo 1983435 4463765 := bbase (se 6 (by rfl) ⟨104619, by rfl⟩ : syracuseStep 4463765 = 209239) (by norm_num)
theorem B2975843 : Blo 1983435 2975843 := bstep (se 1 (by rfl) ⟨2231882, by rfl⟩ : syracuseStep 2975843 = 4463765) B4463765
theorem B1983895 : Blo 1983435 1983895 := bstep (se 1 (by rfl) ⟨1487921, by rfl⟩ : syracuseStep 1983895 = 2975843) B2975843
theorem B2824733 : Blo 1983435 2824733 := bbase (se 3 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 2824733 = 1059275) (by norm_num)
theorem B7532621 : Blo 1983435 7532621 := bstep (se 3 (by rfl) ⟨1412366, by rfl⟩ : syracuseStep 7532621 = 2824733) B2824733
theorem B5021747 : Blo 1983435 5021747 := bstep (se 1 (by rfl) ⟨3766310, by rfl⟩ : syracuseStep 5021747 = 7532621) B7532621
theorem B3347831 : Blo 1983435 3347831 := bstep (se 1 (by rfl) ⟨2510873, by rfl⟩ : syracuseStep 3347831 = 5021747) B5021747
theorem B2231887 : Blo 1983435 2231887 := bstep (se 1 (by rfl) ⟨1673915, by rfl⟩ : syracuseStep 2231887 = 3347831) B3347831
theorem B2975849 : Blo 1983435 2975849 := bstep (se 2 (by rfl) ⟨1115943, by rfl⟩ : syracuseStep 2975849 = 2231887) B2231887
theorem B1983899 : Blo 1983435 1983899 := bstep (se 1 (by rfl) ⟨1487924, by rfl⟩ : syracuseStep 1983899 = 2975849) B2975849
theorem B18098741 : Blo 1983435 18098741 := bbase (se 5 (by rfl) ⟨848378, by rfl⟩ : syracuseStep 18098741 = 1696757) (by norm_num)
theorem B48263309 : Blo 1983435 48263309 := bstep (se 3 (by rfl) ⟨9049370, by rfl⟩ : syracuseStep 48263309 = 18098741) B18098741
theorem B32175539 : Blo 1983435 32175539 := bstep (se 1 (by rfl) ⟨24131654, by rfl⟩ : syracuseStep 32175539 = 48263309) B48263309
theorem B21450359 : Blo 1983435 21450359 := bstep (se 1 (by rfl) ⟨16087769, by rfl⟩ : syracuseStep 21450359 = 32175539) B32175539
theorem B14300239 : Blo 1983435 14300239 := bstep (se 1 (by rfl) ⟨10725179, by rfl⟩ : syracuseStep 14300239 = 21450359) B21450359
theorem B19066985 : Blo 1983435 19066985 := bstep (se 2 (by rfl) ⟨7150119, by rfl⟩ : syracuseStep 19066985 = 14300239) B14300239
theorem B12711323 : Blo 1983435 12711323 := bstep (se 1 (by rfl) ⟨9533492, by rfl⟩ : syracuseStep 12711323 = 19066985) B19066985
theorem B8474215 : Blo 1983435 8474215 := bstep (se 1 (by rfl) ⟨6355661, by rfl⟩ : syracuseStep 8474215 = 12711323) B12711323
theorem B11298953 : Blo 1983435 11298953 := bstep (se 2 (by rfl) ⟨4237107, by rfl⟩ : syracuseStep 11298953 = 8474215) B8474215
theorem B7532635 : Blo 1983435 7532635 := bstep (se 1 (by rfl) ⟨5649476, by rfl⟩ : syracuseStep 7532635 = 11298953) B11298953
theorem B10043513 : Blo 1983435 10043513 := bstep (se 2 (by rfl) ⟨3766317, by rfl⟩ : syracuseStep 10043513 = 7532635) B7532635
theorem B6695675 : Blo 1983435 6695675 := bstep (se 1 (by rfl) ⟨5021756, by rfl⟩ : syracuseStep 6695675 = 10043513) B10043513
theorem B4463783 : Blo 1983435 4463783 := bstep (se 1 (by rfl) ⟨3347837, by rfl⟩ : syracuseStep 4463783 = 6695675) B6695675
theorem B2975855 : Blo 1983435 2975855 := bstep (se 1 (by rfl) ⟨2231891, by rfl⟩ : syracuseStep 2975855 = 4463783) B4463783
theorem B1983903 : Blo 1983435 1983903 := bstep (se 1 (by rfl) ⟨1487927, by rfl⟩ : syracuseStep 1983903 = 2975855) B2975855
theorem B2975861 : Blo 1983435 2975861 := bbase (se 5 (by rfl) ⟨139493, by rfl⟩ : syracuseStep 2975861 = 278987) (by norm_num)
theorem B1983907 : Blo 1983435 1983907 := bstep (se 1 (by rfl) ⟨1487930, by rfl⟩ : syracuseStep 1983907 = 2975861) B2975861
theorem B3766333 : Blo 1983435 3766333 := bbase (se 3 (by rfl) ⟨706187, by rfl⟩ : syracuseStep 3766333 = 1412375) (by norm_num)
theorem B5021777 : Blo 1983435 5021777 := bstep (se 2 (by rfl) ⟨1883166, by rfl⟩ : syracuseStep 5021777 = 3766333) B3766333
theorem B3347851 : Blo 1983435 3347851 := bstep (se 1 (by rfl) ⟨2510888, by rfl⟩ : syracuseStep 3347851 = 5021777) B5021777
theorem B4463801 : Blo 1983435 4463801 := bstep (se 2 (by rfl) ⟨1673925, by rfl⟩ : syracuseStep 4463801 = 3347851) B3347851
theorem B2975867 : Blo 1983435 2975867 := bstep (se 1 (by rfl) ⟨2231900, by rfl⟩ : syracuseStep 2975867 = 4463801) B4463801
theorem B1983911 : Blo 1983435 1983911 := bstep (se 1 (by rfl) ⟨1487933, by rfl⟩ : syracuseStep 1983911 = 2975867) B2975867
theorem B2231905 : Blo 1983435 2231905 := bbase (se 2 (by rfl) ⟨836964, by rfl⟩ : syracuseStep 2231905 = 1673929) (by norm_num)
theorem B2975873 : Blo 1983435 2975873 := bstep (se 2 (by rfl) ⟨1115952, by rfl⟩ : syracuseStep 2975873 = 2231905) B2231905
theorem B1983915 : Blo 1983435 1983915 := bstep (se 1 (by rfl) ⟨1487936, by rfl⟩ : syracuseStep 1983915 = 2975873) B2975873
theorem B5021797 : Blo 1983435 5021797 := bbase (se 4 (by rfl) ⟨470793, by rfl⟩ : syracuseStep 5021797 = 941587) (by norm_num)
theorem B6695729 : Blo 1983435 6695729 := bstep (se 2 (by rfl) ⟨2510898, by rfl⟩ : syracuseStep 6695729 = 5021797) B5021797
theorem B4463819 : Blo 1983435 4463819 := bstep (se 1 (by rfl) ⟨3347864, by rfl⟩ : syracuseStep 4463819 = 6695729) B6695729
theorem B2975879 : Blo 1983435 2975879 := bstep (se 1 (by rfl) ⟨2231909, by rfl⟩ : syracuseStep 2975879 = 4463819) B4463819
theorem B1983919 : Blo 1983435 1983919 := bstep (se 1 (by rfl) ⟨1487939, by rfl⟩ : syracuseStep 1983919 = 2975879) B2975879
theorem B2975885 : Blo 1983435 2975885 := bbase (se 3 (by rfl) ⟨557978, by rfl⟩ : syracuseStep 2975885 = 1115957) (by norm_num)
theorem B1983923 : Blo 1983435 1983923 := bstep (se 1 (by rfl) ⟨1487942, by rfl⟩ : syracuseStep 1983923 = 2975885) B2975885
theorem B4463837 : Blo 1983435 4463837 := bbase (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) (by norm_num)
theorem B2975891 : Blo 1983435 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B1983927 : Blo 1983435 1983927 := bstep (se 1 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 1983927 = 2975891) B2975891
theorem B3347885 : Blo 1983435 3347885 := bbase (se 3 (by rfl) ⟨627728, by rfl⟩ : syracuseStep 3347885 = 1255457) (by norm_num)
theorem B2231923 : Blo 1983435 2231923 := bstep (se 1 (by rfl) ⟨1673942, by rfl⟩ : syracuseStep 2231923 = 3347885) B3347885
theorem B2975897 : Blo 1983435 2975897 := bstep (se 2 (by rfl) ⟨1115961, by rfl⟩ : syracuseStep 2975897 = 2231923) B2231923
theorem B1983931 : Blo 1983435 1983931 := bstep (se 1 (by rfl) ⟨1487948, by rfl⟩ : syracuseStep 1983931 = 2975897) B2975897
theorem B2038441 : Blo 1983435 2038441 := bbase (se 2 (by rfl) ⟨764415, by rfl⟩ : syracuseStep 2038441 = 1528831) (by norm_num)
theorem B2717921 : Blo 1983435 2717921 := bstep (se 2 (by rfl) ⟨1019220, by rfl⟩ : syracuseStep 2717921 = 2038441) B2038441
theorem B7247789 : Blo 1983435 7247789 := bstep (se 3 (by rfl) ⟨1358960, by rfl⟩ : syracuseStep 7247789 = 2717921) B2717921
theorem B4831859 : Blo 1983435 4831859 := bstep (se 1 (by rfl) ⟨3623894, by rfl⟩ : syracuseStep 4831859 = 7247789) B7247789
theorem B12884957 : Blo 1983435 12884957 := bstep (se 3 (by rfl) ⟨2415929, by rfl⟩ : syracuseStep 12884957 = 4831859) B4831859
theorem B8589971 : Blo 1983435 8589971 := bstep (se 1 (by rfl) ⟨6442478, by rfl⟩ : syracuseStep 8589971 = 12884957) B12884957
theorem B5726647 : Blo 1983435 5726647 := bstep (se 1 (by rfl) ⟨4294985, by rfl⟩ : syracuseStep 5726647 = 8589971) B8589971
theorem B7635529 : Blo 1983435 7635529 := bstep (se 2 (by rfl) ⟨2863323, by rfl⟩ : syracuseStep 7635529 = 5726647) B5726647
theorem B40722821 : Blo 1983435 40722821 := bstep (se 4 (by rfl) ⟨3817764, by rfl⟩ : syracuseStep 40722821 = 7635529) B7635529
theorem B27148547 : Blo 1983435 27148547 := bstep (se 1 (by rfl) ⟨20361410, by rfl⟩ : syracuseStep 27148547 = 40722821) B40722821
theorem B72396125 : Blo 1983435 72396125 := bstep (se 3 (by rfl) ⟨13574273, by rfl⟩ : syracuseStep 72396125 = 27148547) B27148547
theorem B48264083 : Blo 1983435 48264083 := bstep (se 1 (by rfl) ⟨36198062, by rfl⟩ : syracuseStep 48264083 = 72396125) B72396125
theorem B32176055 : Blo 1983435 32176055 := bstep (se 1 (by rfl) ⟨24132041, by rfl⟩ : syracuseStep 32176055 = 48264083) B48264083
theorem B85802813 : Blo 1983435 85802813 := bstep (se 3 (by rfl) ⟨16088027, by rfl⟩ : syracuseStep 85802813 = 32176055) B32176055
theorem B57201875 : Blo 1983435 57201875 := bstep (se 1 (by rfl) ⟨42901406, by rfl⟩ : syracuseStep 57201875 = 85802813) B85802813
theorem B38134583 : Blo 1983435 38134583 := bstep (se 1 (by rfl) ⟨28600937, by rfl⟩ : syracuseStep 38134583 = 57201875) B57201875
theorem B25423055 : Blo 1983435 25423055 := bstep (se 1 (by rfl) ⟨19067291, by rfl⟩ : syracuseStep 25423055 = 38134583) B38134583
theorem B16948703 : Blo 1983435 16948703 := bstep (se 1 (by rfl) ⟨12711527, by rfl⟩ : syracuseStep 16948703 = 25423055) B25423055
theorem B11299135 : Blo 1983435 11299135 := bstep (se 1 (by rfl) ⟨8474351, by rfl⟩ : syracuseStep 11299135 = 16948703) B16948703
theorem B15065513 : Blo 1983435 15065513 := bstep (se 2 (by rfl) ⟨5649567, by rfl⟩ : syracuseStep 15065513 = 11299135) B11299135
theorem B10043675 : Blo 1983435 10043675 := bstep (se 1 (by rfl) ⟨7532756, by rfl⟩ : syracuseStep 10043675 = 15065513) B15065513
theorem B6695783 : Blo 1983435 6695783 := bstep (se 1 (by rfl) ⟨5021837, by rfl⟩ : syracuseStep 6695783 = 10043675) B10043675
theorem B4463855 : Blo 1983435 4463855 := bstep (se 1 (by rfl) ⟨3347891, by rfl⟩ : syracuseStep 4463855 = 6695783) B6695783
theorem B2975903 : Blo 1983435 2975903 := bstep (se 1 (by rfl) ⟨2231927, by rfl⟩ : syracuseStep 2975903 = 4463855) B4463855
theorem B1983935 : Blo 1983435 1983935 := bstep (se 1 (by rfl) ⟨1487951, by rfl⟩ : syracuseStep 1983935 = 2975903) B2975903
theorem B2975909 : Blo 1983435 2975909 := bbase (se 4 (by rfl) ⟨278991, by rfl⟩ : syracuseStep 2975909 = 557983) (by norm_num)
theorem B1983939 : Blo 1983435 1983939 := bstep (se 1 (by rfl) ⟨1487954, by rfl⟩ : syracuseStep 1983939 = 2975909) B2975909
theorem B2510929 : Blo 1983435 2510929 := bbase (se 2 (by rfl) ⟨941598, by rfl⟩ : syracuseStep 2510929 = 1883197) (by norm_num)
theorem B3347905 : Blo 1983435 3347905 := bstep (se 2 (by rfl) ⟨1255464, by rfl⟩ : syracuseStep 3347905 = 2510929) B2510929
theorem B4463873 : Blo 1983435 4463873 := bstep (se 2 (by rfl) ⟨1673952, by rfl⟩ : syracuseStep 4463873 = 3347905) B3347905
theorem B2975915 : Blo 1983435 2975915 := bstep (se 1 (by rfl) ⟨2231936, by rfl⟩ : syracuseStep 2975915 = 4463873) B4463873
theorem B1983943 : Blo 1983435 1983943 := bstep (se 1 (by rfl) ⟨1487957, by rfl⟩ : syracuseStep 1983943 = 2975915) B2975915
theorem B2231941 : Blo 1983435 2231941 := bbase (se 4 (by rfl) ⟨209244, by rfl⟩ : syracuseStep 2231941 = 418489) (by norm_num)
theorem B2975921 : Blo 1983435 2975921 := bstep (se 2 (by rfl) ⟨1115970, by rfl⟩ : syracuseStep 2975921 = 2231941) B2231941
theorem B1983947 : Blo 1983435 1983947 := bstep (se 1 (by rfl) ⟨1487960, by rfl⟩ : syracuseStep 1983947 = 2975921) B2975921
theorem B4524797 : Blo 1983435 4524797 := bbase (se 3 (by rfl) ⟨848399, by rfl⟩ : syracuseStep 4524797 = 1696799) (by norm_num)
theorem B3016531 : Blo 1983435 3016531 := bstep (se 1 (by rfl) ⟨2262398, by rfl⟩ : syracuseStep 3016531 = 4524797) B4524797
theorem B16088165 : Blo 1983435 16088165 := bstep (se 4 (by rfl) ⟨1508265, by rfl⟩ : syracuseStep 16088165 = 3016531) B3016531
theorem B10725443 : Blo 1983435 10725443 := bstep (se 1 (by rfl) ⟨8044082, by rfl⟩ : syracuseStep 10725443 = 16088165) B16088165
theorem B7150295 : Blo 1983435 7150295 := bstep (se 1 (by rfl) ⟨5362721, by rfl⟩ : syracuseStep 7150295 = 10725443) B10725443
theorem B4766863 : Blo 1983435 4766863 := bstep (se 1 (by rfl) ⟨3575147, by rfl⟩ : syracuseStep 4766863 = 7150295) B7150295
theorem B6355817 : Blo 1983435 6355817 := bstep (se 2 (by rfl) ⟨2383431, by rfl⟩ : syracuseStep 6355817 = 4766863) B4766863
theorem B4237211 : Blo 1983435 4237211 := bstep (se 1 (by rfl) ⟨3177908, by rfl⟩ : syracuseStep 4237211 = 6355817) B6355817
theorem B2824807 : Blo 1983435 2824807 := bstep (se 1 (by rfl) ⟨2118605, by rfl⟩ : syracuseStep 2824807 = 4237211) B4237211
theorem B3766409 : Blo 1983435 3766409 := bstep (se 2 (by rfl) ⟨1412403, by rfl⟩ : syracuseStep 3766409 = 2824807) B2824807
theorem B2510939 : Blo 1983435 2510939 := bstep (se 1 (by rfl) ⟨1883204, by rfl⟩ : syracuseStep 2510939 = 3766409) B3766409
theorem B6695837 : Blo 1983435 6695837 := bstep (se 3 (by rfl) ⟨1255469, by rfl⟩ : syracuseStep 6695837 = 2510939) B2510939
theorem B4463891 : Blo 1983435 4463891 := bstep (se 1 (by rfl) ⟨3347918, by rfl⟩ : syracuseStep 4463891 = 6695837) B6695837
theorem B2975927 : Blo 1983435 2975927 := bstep (se 1 (by rfl) ⟨2231945, by rfl⟩ : syracuseStep 2975927 = 4463891) B4463891
theorem B1983951 : Blo 1983435 1983951 := bstep (se 1 (by rfl) ⟨1487963, by rfl⟩ : syracuseStep 1983951 = 2975927) B2975927
theorem B2975933 : Blo 1983435 2975933 := bbase (se 3 (by rfl) ⟨557987, by rfl⟩ : syracuseStep 2975933 = 1115975) (by norm_num)
theorem B1983955 : Blo 1983435 1983955 := bstep (se 1 (by rfl) ⟨1487966, by rfl⟩ : syracuseStep 1983955 = 2975933) B2975933
theorem B4463909 : Blo 1983435 4463909 := bbase (se 4 (by rfl) ⟨418491, by rfl⟩ : syracuseStep 4463909 = 836983) (by norm_num)
theorem B2975939 : Blo 1983435 2975939 := bstep (se 1 (by rfl) ⟨2231954, by rfl⟩ : syracuseStep 2975939 = 4463909) B4463909
theorem B1983959 : Blo 1983435 1983959 := bstep (se 1 (by rfl) ⟨1487969, by rfl⟩ : syracuseStep 1983959 = 2975939) B2975939
theorem B5021909 : Blo 1983435 5021909 := bbase (se 7 (by rfl) ⟨58850, by rfl⟩ : syracuseStep 5021909 = 117701) (by norm_num)
theorem B3347939 : Blo 1983435 3347939 := bstep (se 1 (by rfl) ⟨2510954, by rfl⟩ : syracuseStep 3347939 = 5021909) B5021909
theorem B2231959 : Blo 1983435 2231959 := bstep (se 1 (by rfl) ⟨1673969, by rfl⟩ : syracuseStep 2231959 = 3347939) B3347939
theorem B2975945 : Blo 1983435 2975945 := bstep (se 2 (by rfl) ⟨1115979, by rfl⟩ : syracuseStep 2975945 = 2231959) B2231959
theorem B1983963 : Blo 1983435 1983963 := bstep (se 1 (by rfl) ⟨1487972, by rfl⟩ : syracuseStep 1983963 = 2975945) B2975945
theorem B24132437 : Blo 1983435 24132437 := bbase (se 9 (by rfl) ⟨70700, by rfl⟩ : syracuseStep 24132437 = 141401) (by norm_num)
theorem B16088291 : Blo 1983435 16088291 := bstep (se 1 (by rfl) ⟨12066218, by rfl⟩ : syracuseStep 16088291 = 24132437) B24132437
theorem B10725527 : Blo 1983435 10725527 := bstep (se 1 (by rfl) ⟨8044145, by rfl⟩ : syracuseStep 10725527 = 16088291) B16088291
theorem B7150351 : Blo 1983435 7150351 := bstep (se 1 (by rfl) ⟨5362763, by rfl⟩ : syracuseStep 7150351 = 10725527) B10725527
theorem B9533801 : Blo 1983435 9533801 := bstep (se 2 (by rfl) ⟨3575175, by rfl⟩ : syracuseStep 9533801 = 7150351) B7150351
theorem B6355867 : Blo 1983435 6355867 := bstep (se 1 (by rfl) ⟨4766900, by rfl⟩ : syracuseStep 6355867 = 9533801) B9533801
theorem B8474489 : Blo 1983435 8474489 := bstep (se 2 (by rfl) ⟨3177933, by rfl⟩ : syracuseStep 8474489 = 6355867) B6355867
theorem B5649659 : Blo 1983435 5649659 := bstep (se 1 (by rfl) ⟨4237244, by rfl⟩ : syracuseStep 5649659 = 8474489) B8474489
theorem B3766439 : Blo 1983435 3766439 := bstep (se 1 (by rfl) ⟨2824829, by rfl⟩ : syracuseStep 3766439 = 5649659) B5649659
theorem B10043837 : Blo 1983435 10043837 := bstep (se 3 (by rfl) ⟨1883219, by rfl⟩ : syracuseStep 10043837 = 3766439) B3766439
theorem B6695891 : Blo 1983435 6695891 := bstep (se 1 (by rfl) ⟨5021918, by rfl⟩ : syracuseStep 6695891 = 10043837) B10043837
theorem B4463927 : Blo 1983435 4463927 := bstep (se 1 (by rfl) ⟨3347945, by rfl⟩ : syracuseStep 4463927 = 6695891) B6695891
theorem B2975951 : Blo 1983435 2975951 := bstep (se 1 (by rfl) ⟨2231963, by rfl⟩ : syracuseStep 2975951 = 4463927) B4463927
theorem B1983967 : Blo 1983435 1983967 := bstep (se 1 (by rfl) ⟨1487975, by rfl⟩ : syracuseStep 1983967 = 2975951) B2975951
theorem B2975957 : Blo 1983435 2975957 := bbase (se 7 (by rfl) ⟨34874, by rfl⟩ : syracuseStep 2975957 = 69749) (by norm_num)
theorem B1983971 : Blo 1983435 1983971 := bstep (se 1 (by rfl) ⟨1487978, by rfl⟩ : syracuseStep 1983971 = 2975957) B2975957
theorem B8044181 : Blo 1983435 8044181 := bbase (se 6 (by rfl) ⟨188535, by rfl⟩ : syracuseStep 8044181 = 377071) (by norm_num)
theorem B5362787 : Blo 1983435 5362787 := bstep (se 1 (by rfl) ⟨4022090, by rfl⟩ : syracuseStep 5362787 = 8044181) B8044181
theorem B3575191 : Blo 1983435 3575191 := bstep (se 1 (by rfl) ⟨2681393, by rfl⟩ : syracuseStep 3575191 = 5362787) B5362787
theorem B4766921 : Blo 1983435 4766921 := bstep (se 2 (by rfl) ⟨1787595, by rfl⟩ : syracuseStep 4766921 = 3575191) B3575191
theorem B3177947 : Blo 1983435 3177947 := bstep (se 1 (by rfl) ⟨2383460, by rfl⟩ : syracuseStep 3177947 = 4766921) B4766921
theorem B2118631 : Blo 1983435 2118631 := bstep (se 1 (by rfl) ⟨1588973, by rfl⟩ : syracuseStep 2118631 = 3177947) B3177947
theorem B2824841 : Blo 1983435 2824841 := bstep (se 2 (by rfl) ⟨1059315, by rfl⟩ : syracuseStep 2824841 = 2118631) B2118631
theorem B7532909 : Blo 1983435 7532909 := bstep (se 3 (by rfl) ⟨1412420, by rfl⟩ : syracuseStep 7532909 = 2824841) B2824841
theorem B5021939 : Blo 1983435 5021939 := bstep (se 1 (by rfl) ⟨3766454, by rfl⟩ : syracuseStep 5021939 = 7532909) B7532909
theorem B3347959 : Blo 1983435 3347959 := bstep (se 1 (by rfl) ⟨2510969, by rfl⟩ : syracuseStep 3347959 = 5021939) B5021939
theorem B4463945 : Blo 1983435 4463945 := bstep (se 2 (by rfl) ⟨1673979, by rfl⟩ : syracuseStep 4463945 = 3347959) B3347959
theorem B2975963 : Blo 1983435 2975963 := bstep (se 1 (by rfl) ⟨2231972, by rfl⟩ : syracuseStep 2975963 = 4463945) B4463945
theorem B1983975 : Blo 1983435 1983975 := bstep (se 1 (by rfl) ⟨1487981, by rfl⟩ : syracuseStep 1983975 = 2975963) B2975963
theorem B2231977 : Blo 1983435 2231977 := bbase (se 2 (by rfl) ⟨836991, by rfl⟩ : syracuseStep 2231977 = 1673983) (by norm_num)
theorem B2975969 : Blo 1983435 2975969 := bstep (se 2 (by rfl) ⟨1115988, by rfl⟩ : syracuseStep 2975969 = 2231977) B2231977
theorem B1983979 : Blo 1983435 1983979 := bstep (se 1 (by rfl) ⟨1487984, by rfl⟩ : syracuseStep 1983979 = 2975969) B2975969
theorem B4524869 : Blo 1983435 4524869 := bbase (se 4 (by rfl) ⟨424206, by rfl⟩ : syracuseStep 4524869 = 848413) (by norm_num)
theorem B12066317 : Blo 1983435 12066317 := bstep (se 3 (by rfl) ⟨2262434, by rfl⟩ : syracuseStep 12066317 = 4524869) B4524869
theorem B8044211 : Blo 1983435 8044211 := bstep (se 1 (by rfl) ⟨6033158, by rfl⟩ : syracuseStep 8044211 = 12066317) B12066317
theorem B5362807 : Blo 1983435 5362807 := bstep (se 1 (by rfl) ⟨4022105, by rfl⟩ : syracuseStep 5362807 = 8044211) B8044211
theorem B7150409 : Blo 1983435 7150409 := bstep (se 2 (by rfl) ⟨2681403, by rfl⟩ : syracuseStep 7150409 = 5362807) B5362807
theorem B4766939 : Blo 1983435 4766939 := bstep (se 1 (by rfl) ⟨3575204, by rfl⟩ : syracuseStep 4766939 = 7150409) B7150409
theorem B3177959 : Blo 1983435 3177959 := bstep (se 1 (by rfl) ⟨2383469, by rfl⟩ : syracuseStep 3177959 = 4766939) B4766939
theorem B8474557 : Blo 1983435 8474557 := bstep (se 3 (by rfl) ⟨1588979, by rfl⟩ : syracuseStep 8474557 = 3177959) B3177959
theorem B11299409 : Blo 1983435 11299409 := bstep (se 2 (by rfl) ⟨4237278, by rfl⟩ : syracuseStep 11299409 = 8474557) B8474557
theorem B7532939 : Blo 1983435 7532939 := bstep (se 1 (by rfl) ⟨5649704, by rfl⟩ : syracuseStep 7532939 = 11299409) B11299409
theorem B5021959 : Blo 1983435 5021959 := bstep (se 1 (by rfl) ⟨3766469, by rfl⟩ : syracuseStep 5021959 = 7532939) B7532939
theorem B6695945 : Blo 1983435 6695945 := bstep (se 2 (by rfl) ⟨2510979, by rfl⟩ : syracuseStep 6695945 = 5021959) B5021959
theorem B4463963 : Blo 1983435 4463963 := bstep (se 1 (by rfl) ⟨3347972, by rfl⟩ : syracuseStep 4463963 = 6695945) B6695945
theorem B2975975 : Blo 1983435 2975975 := bstep (se 1 (by rfl) ⟨2231981, by rfl⟩ : syracuseStep 2975975 = 4463963) B4463963
theorem B1983983 : Blo 1983435 1983983 := bstep (se 1 (by rfl) ⟨1487987, by rfl⟩ : syracuseStep 1983983 = 2975975) B2975975
theorem B2975981 : Blo 1983435 2975981 := bbase (se 3 (by rfl) ⟨557996, by rfl⟩ : syracuseStep 2975981 = 1115993) (by norm_num)
theorem B1983987 : Blo 1983435 1983987 := bstep (se 1 (by rfl) ⟨1487990, by rfl⟩ : syracuseStep 1983987 = 2975981) B2975981
theorem B4463981 : Blo 1983435 4463981 := bbase (se 3 (by rfl) ⟨836996, by rfl⟩ : syracuseStep 4463981 = 1673993) (by norm_num)
theorem B2975987 : Blo 1983435 2975987 := bstep (se 1 (by rfl) ⟨2231990, by rfl⟩ : syracuseStep 2975987 = 4463981) B4463981
theorem B1983991 : Blo 1983435 1983991 := bstep (se 1 (by rfl) ⟨1487993, by rfl⟩ : syracuseStep 1983991 = 2975987) B2975987
theorem B3766493 : Blo 1983435 3766493 := bbase (se 3 (by rfl) ⟨706217, by rfl⟩ : syracuseStep 3766493 = 1412435) (by norm_num)
theorem B2510995 : Blo 1983435 2510995 := bstep (se 1 (by rfl) ⟨1883246, by rfl⟩ : syracuseStep 2510995 = 3766493) B3766493
theorem B3347993 : Blo 1983435 3347993 := bstep (se 2 (by rfl) ⟨1255497, by rfl⟩ : syracuseStep 3347993 = 2510995) B2510995
theorem B2231995 : Blo 1983435 2231995 := bstep (se 1 (by rfl) ⟨1673996, by rfl⟩ : syracuseStep 2231995 = 3347993) B3347993
theorem B2975993 : Blo 1983435 2975993 := bstep (se 2 (by rfl) ⟨1115997, by rfl⟩ : syracuseStep 2975993 = 2231995) B2231995
theorem B1983995 : Blo 1983435 1983995 := bstep (se 1 (by rfl) ⟨1487996, by rfl⟩ : syracuseStep 1983995 = 2975993) B2975993
theorem B2416009 : Blo 1983435 2416009 := bbase (se 2 (by rfl) ⟨906003, by rfl⟩ : syracuseStep 2416009 = 1812007) (by norm_num)
theorem B3221345 : Blo 1983435 3221345 := bstep (se 2 (by rfl) ⟨1208004, by rfl⟩ : syracuseStep 3221345 = 2416009) B2416009
theorem B2147563 : Blo 1983435 2147563 := bstep (se 1 (by rfl) ⟨1610672, by rfl⟩ : syracuseStep 2147563 = 3221345) B3221345
theorem B11453669 : Blo 1983435 11453669 := bstep (se 4 (by rfl) ⟨1073781, by rfl⟩ : syracuseStep 11453669 = 2147563) B2147563
theorem B7635779 : Blo 1983435 7635779 := bstep (se 1 (by rfl) ⟨5726834, by rfl⟩ : syracuseStep 7635779 = 11453669) B11453669
theorem B5090519 : Blo 1983435 5090519 := bstep (se 1 (by rfl) ⟨3817889, by rfl⟩ : syracuseStep 5090519 = 7635779) B7635779
theorem B3393679 : Blo 1983435 3393679 := bstep (se 1 (by rfl) ⟨2545259, by rfl⟩ : syracuseStep 3393679 = 5090519) B5090519
theorem B4524905 : Blo 1983435 4524905 := bstep (se 2 (by rfl) ⟨1696839, by rfl⟩ : syracuseStep 4524905 = 3393679) B3393679
theorem B3016603 : Blo 1983435 3016603 := bstep (se 1 (by rfl) ⟨2262452, by rfl⟩ : syracuseStep 3016603 = 4524905) B4524905
theorem B4022137 : Blo 1983435 4022137 := bstep (se 2 (by rfl) ⟨1508301, by rfl⟩ : syracuseStep 4022137 = 3016603) B3016603
theorem B5362849 : Blo 1983435 5362849 := bstep (se 2 (by rfl) ⟨2011068, by rfl⟩ : syracuseStep 5362849 = 4022137) B4022137
theorem B7150465 : Blo 1983435 7150465 := bstep (se 2 (by rfl) ⟨2681424, by rfl⟩ : syracuseStep 7150465 = 5362849) B5362849
theorem B9533953 : Blo 1983435 9533953 := bstep (se 2 (by rfl) ⟨3575232, by rfl⟩ : syracuseStep 9533953 = 7150465) B7150465
theorem B50847749 : Blo 1983435 50847749 := bstep (se 4 (by rfl) ⟨4766976, by rfl⟩ : syracuseStep 50847749 = 9533953) B9533953
theorem B33898499 : Blo 1983435 33898499 := bstep (se 1 (by rfl) ⟨25423874, by rfl⟩ : syracuseStep 33898499 = 50847749) B50847749
theorem B22598999 : Blo 1983435 22598999 := bstep (se 1 (by rfl) ⟨16949249, by rfl⟩ : syracuseStep 22598999 = 33898499) B33898499
theorem B15065999 : Blo 1983435 15065999 := bstep (se 1 (by rfl) ⟨11299499, by rfl⟩ : syracuseStep 15065999 = 22598999) B22598999
theorem B10043999 : Blo 1983435 10043999 := bstep (se 1 (by rfl) ⟨7532999, by rfl⟩ : syracuseStep 10043999 = 15065999) B15065999
theorem B6695999 : Blo 1983435 6695999 := bstep (se 1 (by rfl) ⟨5021999, by rfl⟩ : syracuseStep 6695999 = 10043999) B10043999
theorem B4463999 : Blo 1983435 4463999 := bstep (se 1 (by rfl) ⟨3347999, by rfl⟩ : syracuseStep 4463999 = 6695999) B6695999
theorem B2975999 : Blo 1983435 2975999 := bstep (se 1 (by rfl) ⟨2231999, by rfl⟩ : syracuseStep 2975999 = 4463999) B4463999
theorem B1983999 : Blo 1983435 1983999 := bstep (se 1 (by rfl) ⟨1487999, by rfl⟩ : syracuseStep 1983999 = 2975999) B2975999
theorem B2976005 : Blo 1983435 2976005 := bbase (se 4 (by rfl) ⟨279000, by rfl⟩ : syracuseStep 2976005 = 558001) (by norm_num)
theorem B1984003 : Blo 1983435 1984003 := bstep (se 1 (by rfl) ⟨1488002, by rfl⟩ : syracuseStep 1984003 = 2976005) B2976005
theorem B3348013 : Blo 1983435 3348013 := bbase (se 3 (by rfl) ⟨627752, by rfl⟩ : syracuseStep 3348013 = 1255505) (by norm_num)
theorem B4464017 : Blo 1983435 4464017 := bstep (se 2 (by rfl) ⟨1674006, by rfl⟩ : syracuseStep 4464017 = 3348013) B3348013
theorem B2976011 : Blo 1983435 2976011 := bstep (se 1 (by rfl) ⟨2232008, by rfl⟩ : syracuseStep 2976011 = 4464017) B4464017
theorem B1984007 : Blo 1983435 1984007 := bstep (se 1 (by rfl) ⟨1488005, by rfl⟩ : syracuseStep 1984007 = 2976011) B2976011
theorem B2232013 : Blo 1983435 2232013 := bbase (se 3 (by rfl) ⟨418502, by rfl⟩ : syracuseStep 2232013 = 837005) (by norm_num)
theorem B2976017 : Blo 1983435 2976017 := bstep (se 2 (by rfl) ⟨1116006, by rfl⟩ : syracuseStep 2976017 = 2232013) B2232013
theorem B1984011 : Blo 1983435 1984011 := bstep (se 1 (by rfl) ⟨1488008, by rfl⟩ : syracuseStep 1984011 = 2976017) B2976017
theorem B6696053 : Blo 1983435 6696053 := bbase (se 5 (by rfl) ⟨313877, by rfl⟩ : syracuseStep 6696053 = 627755) (by norm_num)
theorem B4464035 : Blo 1983435 4464035 := bstep (se 1 (by rfl) ⟨3348026, by rfl⟩ : syracuseStep 4464035 = 6696053) B6696053
theorem B2976023 : Blo 1983435 2976023 := bstep (se 1 (by rfl) ⟨2232017, by rfl⟩ : syracuseStep 2976023 = 4464035) B4464035
theorem B1984015 : Blo 1983435 1984015 := bstep (se 1 (by rfl) ⟨1488011, by rfl⟩ : syracuseStep 1984015 = 2976023) B2976023
theorem B2976029 : Blo 1983435 2976029 := bbase (se 3 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 2976029 = 1116011) (by norm_num)
theorem B1984019 : Blo 1983435 1984019 := bstep (se 1 (by rfl) ⟨1488014, by rfl⟩ : syracuseStep 1984019 = 2976029) B2976029
theorem B4464053 : Blo 1983435 4464053 := bbase (se 5 (by rfl) ⟨209252, by rfl⟩ : syracuseStep 4464053 = 418505) (by norm_num)
theorem B2976035 : Blo 1983435 2976035 := bstep (se 1 (by rfl) ⟨2232026, by rfl⟩ : syracuseStep 2976035 = 4464053) B4464053
theorem B1984023 : Blo 1983435 1984023 := bstep (se 1 (by rfl) ⟨1488017, by rfl⟩ : syracuseStep 1984023 = 2976035) B2976035
theorem B4237373 : Blo 1983435 4237373 := bbase (se 3 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 4237373 = 1589015) (by norm_num)
theorem B11299661 : Blo 1983435 11299661 := bstep (se 3 (by rfl) ⟨2118686, by rfl⟩ : syracuseStep 11299661 = 4237373) B4237373
theorem B7533107 : Blo 1983435 7533107 := bstep (se 1 (by rfl) ⟨5649830, by rfl⟩ : syracuseStep 7533107 = 11299661) B11299661
theorem B5022071 : Blo 1983435 5022071 := bstep (se 1 (by rfl) ⟨3766553, by rfl⟩ : syracuseStep 5022071 = 7533107) B7533107
theorem B3348047 : Blo 1983435 3348047 := bstep (se 1 (by rfl) ⟨2511035, by rfl⟩ : syracuseStep 3348047 = 5022071) B5022071
theorem B2232031 : Blo 1983435 2232031 := bstep (se 1 (by rfl) ⟨1674023, by rfl⟩ : syracuseStep 2232031 = 3348047) B3348047
theorem B2976041 : Blo 1983435 2976041 := bstep (se 2 (by rfl) ⟨1116015, by rfl⟩ : syracuseStep 2976041 = 2232031) B2232031
theorem B1984027 : Blo 1983435 1984027 := bstep (se 1 (by rfl) ⟨1488020, by rfl⟩ : syracuseStep 1984027 = 2976041) B2976041
theorem B4237381 : Blo 1983435 4237381 := bbase (se 4 (by rfl) ⟨397254, by rfl⟩ : syracuseStep 4237381 = 794509) (by norm_num)
theorem B5649841 : Blo 1983435 5649841 := bstep (se 2 (by rfl) ⟨2118690, by rfl⟩ : syracuseStep 5649841 = 4237381) B4237381
theorem B7533121 : Blo 1983435 7533121 := bstep (se 2 (by rfl) ⟨2824920, by rfl⟩ : syracuseStep 7533121 = 5649841) B5649841
theorem B10044161 : Blo 1983435 10044161 := bstep (se 2 (by rfl) ⟨3766560, by rfl⟩ : syracuseStep 10044161 = 7533121) B7533121
theorem B6696107 : Blo 1983435 6696107 := bstep (se 1 (by rfl) ⟨5022080, by rfl⟩ : syracuseStep 6696107 = 10044161) B10044161
theorem B4464071 : Blo 1983435 4464071 := bstep (se 1 (by rfl) ⟨3348053, by rfl⟩ : syracuseStep 4464071 = 6696107) B6696107
theorem B2976047 : Blo 1983435 2976047 := bstep (se 1 (by rfl) ⟨2232035, by rfl⟩ : syracuseStep 2976047 = 4464071) B4464071
theorem B1984031 : Blo 1983435 1984031 := bstep (se 1 (by rfl) ⟨1488023, by rfl⟩ : syracuseStep 1984031 = 2976047) B2976047
theorem B2976053 : Blo 1983435 2976053 := bbase (se 5 (by rfl) ⟨139502, by rfl⟩ : syracuseStep 2976053 = 279005) (by norm_num)
theorem B1984035 : Blo 1983435 1984035 := bstep (se 1 (by rfl) ⟨1488026, by rfl⟩ : syracuseStep 1984035 = 2976053) B2976053
theorem B5022101 : Blo 1983435 5022101 := bbase (se 6 (by rfl) ⟨117705, by rfl⟩ : syracuseStep 5022101 = 235411) (by norm_num)
theorem B3348067 : Blo 1983435 3348067 := bstep (se 1 (by rfl) ⟨2511050, by rfl⟩ : syracuseStep 3348067 = 5022101) B5022101
theorem B4464089 : Blo 1983435 4464089 := bstep (se 2 (by rfl) ⟨1674033, by rfl⟩ : syracuseStep 4464089 = 3348067) B3348067
theorem B2976059 : Blo 1983435 2976059 := bstep (se 1 (by rfl) ⟨2232044, by rfl⟩ : syracuseStep 2976059 = 4464089) B4464089
theorem B1984039 : Blo 1983435 1984039 := bstep (se 1 (by rfl) ⟨1488029, by rfl⟩ : syracuseStep 1984039 = 2976059) B2976059
theorem B2232049 : Blo 1983435 2232049 := bbase (se 2 (by rfl) ⟨837018, by rfl⟩ : syracuseStep 2232049 = 1674037) (by norm_num)
theorem B2976065 : Blo 1983435 2976065 := bstep (se 2 (by rfl) ⟨1116024, by rfl⟩ : syracuseStep 2976065 = 2232049) B2232049
theorem B1984043 : Blo 1983435 1984043 := bstep (se 1 (by rfl) ⟨1488032, by rfl⟩ : syracuseStep 1984043 = 2976065) B2976065
theorem B3817981 : Blo 1983435 3817981 := bbase (se 3 (by rfl) ⟨715871, by rfl⟩ : syracuseStep 3817981 = 1431743) (by norm_num)
theorem B20362565 : Blo 1983435 20362565 := bstep (se 4 (by rfl) ⟨1908990, by rfl⟩ : syracuseStep 20362565 = 3817981) B3817981
theorem B13575043 : Blo 1983435 13575043 := bstep (se 1 (by rfl) ⟨10181282, by rfl⟩ : syracuseStep 13575043 = 20362565) B20362565
theorem B18100057 : Blo 1983435 18100057 := bstep (se 2 (by rfl) ⟨6787521, by rfl⟩ : syracuseStep 18100057 = 13575043) B13575043
theorem B24133409 : Blo 1983435 24133409 := bstep (se 2 (by rfl) ⟨9050028, by rfl⟩ : syracuseStep 24133409 = 18100057) B18100057
theorem B16088939 : Blo 1983435 16088939 := bstep (se 1 (by rfl) ⟨12066704, by rfl⟩ : syracuseStep 16088939 = 24133409) B24133409
theorem B10725959 : Blo 1983435 10725959 := bstep (se 1 (by rfl) ⟨8044469, by rfl⟩ : syracuseStep 10725959 = 16088939) B16088939
theorem B28602557 : Blo 1983435 28602557 := bstep (se 3 (by rfl) ⟨5362979, by rfl⟩ : syracuseStep 28602557 = 10725959) B10725959
theorem B19068371 : Blo 1983435 19068371 := bstep (se 1 (by rfl) ⟨14301278, by rfl⟩ : syracuseStep 19068371 = 28602557) B28602557
theorem B12712247 : Blo 1983435 12712247 := bstep (se 1 (by rfl) ⟨9534185, by rfl⟩ : syracuseStep 12712247 = 19068371) B19068371
theorem B8474831 : Blo 1983435 8474831 := bstep (se 1 (by rfl) ⟨6356123, by rfl⟩ : syracuseStep 8474831 = 12712247) B12712247
theorem B5649887 : Blo 1983435 5649887 := bstep (se 1 (by rfl) ⟨4237415, by rfl⟩ : syracuseStep 5649887 = 8474831) B8474831
theorem B3766591 : Blo 1983435 3766591 := bstep (se 1 (by rfl) ⟨2824943, by rfl⟩ : syracuseStep 3766591 = 5649887) B5649887
theorem B5022121 : Blo 1983435 5022121 := bstep (se 2 (by rfl) ⟨1883295, by rfl⟩ : syracuseStep 5022121 = 3766591) B3766591
theorem B6696161 : Blo 1983435 6696161 := bstep (se 2 (by rfl) ⟨2511060, by rfl⟩ : syracuseStep 6696161 = 5022121) B5022121
theorem B4464107 : Blo 1983435 4464107 := bstep (se 1 (by rfl) ⟨3348080, by rfl⟩ : syracuseStep 4464107 = 6696161) B6696161
theorem B2976071 : Blo 1983435 2976071 := bstep (se 1 (by rfl) ⟨2232053, by rfl⟩ : syracuseStep 2976071 = 4464107) B4464107
theorem B1984047 : Blo 1983435 1984047 := bstep (se 1 (by rfl) ⟨1488035, by rfl⟩ : syracuseStep 1984047 = 2976071) B2976071
theorem B2976077 : Blo 1983435 2976077 := bbase (se 3 (by rfl) ⟨558014, by rfl⟩ : syracuseStep 2976077 = 1116029) (by norm_num)
theorem B1984051 : Blo 1983435 1984051 := bstep (se 1 (by rfl) ⟨1488038, by rfl⟩ : syracuseStep 1984051 = 2976077) B2976077
theorem B4464125 : Blo 1983435 4464125 := bbase (se 3 (by rfl) ⟨837023, by rfl⟩ : syracuseStep 4464125 = 1674047) (by norm_num)
theorem B2976083 : Blo 1983435 2976083 := bstep (se 1 (by rfl) ⟨2232062, by rfl⟩ : syracuseStep 2976083 = 4464125) B4464125
theorem B1984055 : Blo 1983435 1984055 := bstep (se 1 (by rfl) ⟨1488041, by rfl⟩ : syracuseStep 1984055 = 2976083) B2976083
theorem B3348101 : Blo 1983435 3348101 := bbase (se 4 (by rfl) ⟨313884, by rfl⟩ : syracuseStep 3348101 = 627769) (by norm_num)
theorem B2232067 : Blo 1983435 2232067 := bstep (se 1 (by rfl) ⟨1674050, by rfl⟩ : syracuseStep 2232067 = 3348101) B3348101
theorem B2976089 : Blo 1983435 2976089 := bstep (se 2 (by rfl) ⟨1116033, by rfl⟩ : syracuseStep 2976089 = 2232067) B2232067
theorem B1984059 : Blo 1983435 1984059 := bstep (se 1 (by rfl) ⟨1488044, by rfl⟩ : syracuseStep 1984059 = 2976089) B2976089
theorem B15066485 : Blo 1983435 15066485 := bbase (se 5 (by rfl) ⟨706241, by rfl⟩ : syracuseStep 15066485 = 1412483) (by norm_num)
theorem B10044323 : Blo 1983435 10044323 := bstep (se 1 (by rfl) ⟨7533242, by rfl⟩ : syracuseStep 10044323 = 15066485) B15066485
theorem B6696215 : Blo 1983435 6696215 := bstep (se 1 (by rfl) ⟨5022161, by rfl⟩ : syracuseStep 6696215 = 10044323) B10044323
theorem B4464143 : Blo 1983435 4464143 := bstep (se 1 (by rfl) ⟨3348107, by rfl⟩ : syracuseStep 4464143 = 6696215) B6696215
theorem B2976095 : Blo 1983435 2976095 := bstep (se 1 (by rfl) ⟨2232071, by rfl⟩ : syracuseStep 2976095 = 4464143) B4464143
theorem B1984063 : Blo 1983435 1984063 := bstep (se 1 (by rfl) ⟨1488047, by rfl⟩ : syracuseStep 1984063 = 2976095) B2976095
theorem B2976101 : Blo 1983435 2976101 := bbase (se 4 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 2976101 = 558019) (by norm_num)
theorem B1984067 : Blo 1983435 1984067 := bstep (se 1 (by rfl) ⟨1488050, by rfl⟩ : syracuseStep 1984067 = 2976101) B2976101
theorem B3766637 : Blo 1983435 3766637 := bbase (se 3 (by rfl) ⟨706244, by rfl⟩ : syracuseStep 3766637 = 1412489) (by norm_num)
theorem B2511091 : Blo 1983435 2511091 := bstep (se 1 (by rfl) ⟨1883318, by rfl⟩ : syracuseStep 2511091 = 3766637) B3766637
theorem B3348121 : Blo 1983435 3348121 := bstep (se 2 (by rfl) ⟨1255545, by rfl⟩ : syracuseStep 3348121 = 2511091) B2511091
theorem B4464161 : Blo 1983435 4464161 := bstep (se 2 (by rfl) ⟨1674060, by rfl⟩ : syracuseStep 4464161 = 3348121) B3348121
theorem B2976107 : Blo 1983435 2976107 := bstep (se 1 (by rfl) ⟨2232080, by rfl⟩ : syracuseStep 2976107 = 4464161) B4464161
theorem B1984071 : Blo 1983435 1984071 := bstep (se 1 (by rfl) ⟨1488053, by rfl⟩ : syracuseStep 1984071 = 2976107) B2976107
theorem B2232085 : Blo 1983435 2232085 := bbase (se 6 (by rfl) ⟨52314, by rfl⟩ : syracuseStep 2232085 = 104629) (by norm_num)
theorem B2976113 : Blo 1983435 2976113 := bstep (se 2 (by rfl) ⟨1116042, by rfl⟩ : syracuseStep 2976113 = 2232085) B2232085
theorem B1984075 : Blo 1983435 1984075 := bstep (se 1 (by rfl) ⟨1488056, by rfl⟩ : syracuseStep 1984075 = 2976113) B2976113
theorem B2511101 : Blo 1983435 2511101 := bbase (se 3 (by rfl) ⟨470831, by rfl⟩ : syracuseStep 2511101 = 941663) (by norm_num)
theorem B6696269 : Blo 1983435 6696269 := bstep (se 3 (by rfl) ⟨1255550, by rfl⟩ : syracuseStep 6696269 = 2511101) B2511101
theorem B4464179 : Blo 1983435 4464179 := bstep (se 1 (by rfl) ⟨3348134, by rfl⟩ : syracuseStep 4464179 = 6696269) B6696269
theorem B2976119 : Blo 1983435 2976119 := bstep (se 1 (by rfl) ⟨2232089, by rfl⟩ : syracuseStep 2976119 = 4464179) B4464179
theorem B1984079 : Blo 1983435 1984079 := bstep (se 1 (by rfl) ⟨1488059, by rfl⟩ : syracuseStep 1984079 = 2976119) B2976119
theorem B2976125 : Blo 1983435 2976125 := bbase (se 3 (by rfl) ⟨558023, by rfl⟩ : syracuseStep 2976125 = 1116047) (by norm_num)
theorem B1984083 : Blo 1983435 1984083 := bstep (se 1 (by rfl) ⟨1488062, by rfl⟩ : syracuseStep 1984083 = 2976125) B2976125
theorem B4464197 : Blo 1983435 4464197 := bbase (se 4 (by rfl) ⟨418518, by rfl⟩ : syracuseStep 4464197 = 837037) (by norm_num)
theorem B2976131 : Blo 1983435 2976131 := bstep (se 1 (by rfl) ⟨2232098, by rfl⟩ : syracuseStep 2976131 = 4464197) B4464197
theorem B1984087 : Blo 1983435 1984087 := bstep (se 1 (by rfl) ⟨1488065, by rfl⟩ : syracuseStep 1984087 = 2976131) B2976131
theorem B3178133 : Blo 1983435 3178133 := bbase (se 6 (by rfl) ⟨74487, by rfl⟩ : syracuseStep 3178133 = 148975) (by norm_num)
theorem B2118755 : Blo 1983435 2118755 := bstep (se 1 (by rfl) ⟨1589066, by rfl⟩ : syracuseStep 2118755 = 3178133) B3178133
theorem B5650013 : Blo 1983435 5650013 := bstep (se 3 (by rfl) ⟨1059377, by rfl⟩ : syracuseStep 5650013 = 2118755) B2118755
theorem B3766675 : Blo 1983435 3766675 := bstep (se 1 (by rfl) ⟨2825006, by rfl⟩ : syracuseStep 3766675 = 5650013) B5650013
theorem B5022233 : Blo 1983435 5022233 := bstep (se 2 (by rfl) ⟨1883337, by rfl⟩ : syracuseStep 5022233 = 3766675) B3766675
theorem B3348155 : Blo 1983435 3348155 := bstep (se 1 (by rfl) ⟨2511116, by rfl⟩ : syracuseStep 3348155 = 5022233) B5022233
theorem B2232103 : Blo 1983435 2232103 := bstep (se 1 (by rfl) ⟨1674077, by rfl⟩ : syracuseStep 2232103 = 3348155) B3348155
theorem B2976137 : Blo 1983435 2976137 := bstep (se 2 (by rfl) ⟨1116051, by rfl⟩ : syracuseStep 2976137 = 2232103) B2232103
theorem B1984091 : Blo 1983435 1984091 := bstep (se 1 (by rfl) ⟨1488068, by rfl⟩ : syracuseStep 1984091 = 2976137) B2976137
theorem B10044485 : Blo 1983435 10044485 := bbase (se 4 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 10044485 = 1883341) (by norm_num)
theorem B6696323 : Blo 1983435 6696323 := bstep (se 1 (by rfl) ⟨5022242, by rfl⟩ : syracuseStep 6696323 = 10044485) B10044485
theorem B4464215 : Blo 1983435 4464215 := bstep (se 1 (by rfl) ⟨3348161, by rfl⟩ : syracuseStep 4464215 = 6696323) B6696323
theorem B2976143 : Blo 1983435 2976143 := bstep (se 1 (by rfl) ⟨2232107, by rfl⟩ : syracuseStep 2976143 = 4464215) B4464215
theorem B1984095 : Blo 1983435 1984095 := bstep (se 1 (by rfl) ⟨1488071, by rfl⟩ : syracuseStep 1984095 = 2976143) B2976143
theorem B2976149 : Blo 1983435 2976149 := bbase (se 6 (by rfl) ⟨69753, by rfl⟩ : syracuseStep 2976149 = 139507) (by norm_num)
theorem B1984099 : Blo 1983435 1984099 := bstep (se 1 (by rfl) ⟨1488074, by rfl⟩ : syracuseStep 1984099 = 2976149) B2976149
theorem B2545393 : Blo 1983435 2545393 := bbase (se 2 (by rfl) ⟨954522, by rfl⟩ : syracuseStep 2545393 = 1909045) (by norm_num)
theorem B3393857 : Blo 1983435 3393857 := bstep (se 2 (by rfl) ⟨1272696, by rfl⟩ : syracuseStep 3393857 = 2545393) B2545393
theorem B9050285 : Blo 1983435 9050285 := bstep (se 3 (by rfl) ⟨1696928, by rfl⟩ : syracuseStep 9050285 = 3393857) B3393857
theorem B6033523 : Blo 1983435 6033523 := bstep (se 1 (by rfl) ⟨4525142, by rfl⟩ : syracuseStep 6033523 = 9050285) B9050285
theorem B8044697 : Blo 1983435 8044697 := bstep (se 2 (by rfl) ⟨3016761, by rfl⟩ : syracuseStep 8044697 = 6033523) B6033523
theorem B21452525 : Blo 1983435 21452525 := bstep (se 3 (by rfl) ⟨4022348, by rfl⟩ : syracuseStep 21452525 = 8044697) B8044697
theorem B14301683 : Blo 1983435 14301683 := bstep (se 1 (by rfl) ⟨10726262, by rfl⟩ : syracuseStep 14301683 = 21452525) B21452525
theorem B9534455 : Blo 1983435 9534455 := bstep (se 1 (by rfl) ⟨7150841, by rfl⟩ : syracuseStep 9534455 = 14301683) B14301683
theorem B6356303 : Blo 1983435 6356303 := bstep (se 1 (by rfl) ⟨4767227, by rfl⟩ : syracuseStep 6356303 = 9534455) B9534455
theorem B4237535 : Blo 1983435 4237535 := bstep (se 1 (by rfl) ⟨3178151, by rfl⟩ : syracuseStep 4237535 = 6356303) B6356303
theorem B11300093 : Blo 1983435 11300093 := bstep (se 3 (by rfl) ⟨2118767, by rfl⟩ : syracuseStep 11300093 = 4237535) B4237535
theorem B7533395 : Blo 1983435 7533395 := bstep (se 1 (by rfl) ⟨5650046, by rfl⟩ : syracuseStep 7533395 = 11300093) B11300093
theorem B5022263 : Blo 1983435 5022263 := bstep (se 1 (by rfl) ⟨3766697, by rfl⟩ : syracuseStep 5022263 = 7533395) B7533395
theorem B3348175 : Blo 1983435 3348175 := bstep (se 1 (by rfl) ⟨2511131, by rfl⟩ : syracuseStep 3348175 = 5022263) B5022263
theorem B4464233 : Blo 1983435 4464233 := bstep (se 2 (by rfl) ⟨1674087, by rfl⟩ : syracuseStep 4464233 = 3348175) B3348175
theorem B2976155 : Blo 1983435 2976155 := bstep (se 1 (by rfl) ⟨2232116, by rfl⟩ : syracuseStep 2976155 = 4464233) B4464233
theorem B1984103 : Blo 1983435 1984103 := bstep (se 1 (by rfl) ⟨1488077, by rfl⟩ : syracuseStep 1984103 = 2976155) B2976155
theorem B2232121 : Blo 1983435 2232121 := bbase (se 2 (by rfl) ⟨837045, by rfl⟩ : syracuseStep 2232121 = 1674091) (by norm_num)
theorem B2976161 : Blo 1983435 2976161 := bstep (se 2 (by rfl) ⟨1116060, by rfl⟩ : syracuseStep 2976161 = 2232121) B2232121
theorem B1984107 : Blo 1983435 1984107 := bstep (se 1 (by rfl) ⟨1488080, by rfl⟩ : syracuseStep 1984107 = 2976161) B2976161
theorem B5650069 : Blo 1983435 5650069 := bbase (se 6 (by rfl) ⟨132423, by rfl⟩ : syracuseStep 5650069 = 264847) (by norm_num)
theorem B7533425 : Blo 1983435 7533425 := bstep (se 2 (by rfl) ⟨2825034, by rfl⟩ : syracuseStep 7533425 = 5650069) B5650069
theorem B5022283 : Blo 1983435 5022283 := bstep (se 1 (by rfl) ⟨3766712, by rfl⟩ : syracuseStep 5022283 = 7533425) B7533425
theorem B6696377 : Blo 1983435 6696377 := bstep (se 2 (by rfl) ⟨2511141, by rfl⟩ : syracuseStep 6696377 = 5022283) B5022283
theorem B4464251 : Blo 1983435 4464251 := bstep (se 1 (by rfl) ⟨3348188, by rfl⟩ : syracuseStep 4464251 = 6696377) B6696377
theorem B2976167 : Blo 1983435 2976167 := bstep (se 1 (by rfl) ⟨2232125, by rfl⟩ : syracuseStep 2976167 = 4464251) B4464251
theorem B1984111 : Blo 1983435 1984111 := bstep (se 1 (by rfl) ⟨1488083, by rfl⟩ : syracuseStep 1984111 = 2976167) B2976167
theorem B2976173 : Blo 1983435 2976173 := bbase (se 3 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 2976173 = 1116065) (by norm_num)
theorem B1984115 : Blo 1983435 1984115 := bstep (se 1 (by rfl) ⟨1488086, by rfl⟩ : syracuseStep 1984115 = 2976173) B2976173
theorem B4464269 : Blo 1983435 4464269 := bbase (se 3 (by rfl) ⟨837050, by rfl⟩ : syracuseStep 4464269 = 1674101) (by norm_num)
theorem B2976179 : Blo 1983435 2976179 := bstep (se 1 (by rfl) ⟨2232134, by rfl⟩ : syracuseStep 2976179 = 4464269) B4464269
theorem B1984119 : Blo 1983435 1984119 := bstep (se 1 (by rfl) ⟨1488089, by rfl⟩ : syracuseStep 1984119 = 2976179) B2976179
theorem B2511157 : Blo 1983435 2511157 := bbase (se 5 (by rfl) ⟨117710, by rfl⟩ : syracuseStep 2511157 = 235421) (by norm_num)
theorem B3348209 : Blo 1983435 3348209 := bstep (se 2 (by rfl) ⟨1255578, by rfl⟩ : syracuseStep 3348209 = 2511157) B2511157
theorem B2232139 : Blo 1983435 2232139 := bstep (se 1 (by rfl) ⟨1674104, by rfl⟩ : syracuseStep 2232139 = 3348209) B3348209
theorem B2976185 : Blo 1983435 2976185 := bstep (se 2 (by rfl) ⟨1116069, by rfl⟩ : syracuseStep 2976185 = 2232139) B2232139
theorem B1984123 : Blo 1983435 1984123 := bstep (se 1 (by rfl) ⟨1488092, by rfl⟩ : syracuseStep 1984123 = 2976185) B2976185
theorem B2449129 : Blo 1983435 2449129 := bbase (se 2 (by rfl) ⟨918423, by rfl⟩ : syracuseStep 2449129 = 1836847) (by norm_num)
theorem B3265505 : Blo 1983435 3265505 := bstep (se 2 (by rfl) ⟨1224564, by rfl⟩ : syracuseStep 3265505 = 2449129) B2449129
theorem B2177003 : Blo 1983435 2177003 := bstep (se 1 (by rfl) ⟨1632752, by rfl⟩ : syracuseStep 2177003 = 3265505) B3265505
theorem B5805341 : Blo 1983435 5805341 := bstep (se 3 (by rfl) ⟨1088501, by rfl⟩ : syracuseStep 5805341 = 2177003) B2177003
theorem B3870227 : Blo 1983435 3870227 := bstep (se 1 (by rfl) ⟨2902670, by rfl⟩ : syracuseStep 3870227 = 5805341) B5805341
theorem B2580151 : Blo 1983435 2580151 := bstep (se 1 (by rfl) ⟨1935113, by rfl⟩ : syracuseStep 2580151 = 3870227) B3870227
theorem B3440201 : Blo 1983435 3440201 := bstep (se 2 (by rfl) ⟨1290075, by rfl⟩ : syracuseStep 3440201 = 2580151) B2580151
theorem B36695477 : Blo 1983435 36695477 := bstep (se 5 (by rfl) ⟨1720100, by rfl⟩ : syracuseStep 36695477 = 3440201) B3440201
theorem B97854605 : Blo 1983435 97854605 := bstep (se 3 (by rfl) ⟨18347738, by rfl⟩ : syracuseStep 97854605 = 36695477) B36695477
theorem B65236403 : Blo 1983435 65236403 := bstep (se 1 (by rfl) ⟨48927302, by rfl⟩ : syracuseStep 65236403 = 97854605) B97854605
theorem B43490935 : Blo 1983435 43490935 := bstep (se 1 (by rfl) ⟨32618201, by rfl⟩ : syracuseStep 43490935 = 65236403) B65236403
theorem B57987913 : Blo 1983435 57987913 := bstep (se 2 (by rfl) ⟨21745467, by rfl⟩ : syracuseStep 57987913 = 43490935) B43490935
theorem B77317217 : Blo 1983435 77317217 := bstep (se 2 (by rfl) ⟨28993956, by rfl⟩ : syracuseStep 77317217 = 57987913) B57987913
theorem B51544811 : Blo 1983435 51544811 := bstep (se 1 (by rfl) ⟨38658608, by rfl⟩ : syracuseStep 51544811 = 77317217) B77317217
theorem B34363207 : Blo 1983435 34363207 := bstep (se 1 (by rfl) ⟨25772405, by rfl⟩ : syracuseStep 34363207 = 51544811) B51544811
theorem B45817609 : Blo 1983435 45817609 := bstep (se 2 (by rfl) ⟨17181603, by rfl⟩ : syracuseStep 45817609 = 34363207) B34363207
theorem B61090145 : Blo 1983435 61090145 := bstep (se 2 (by rfl) ⟨22908804, by rfl⟩ : syracuseStep 61090145 = 45817609) B45817609
theorem B40726763 : Blo 1983435 40726763 := bstep (se 1 (by rfl) ⟨30545072, by rfl⟩ : syracuseStep 40726763 = 61090145) B61090145
theorem B27151175 : Blo 1983435 27151175 := bstep (se 1 (by rfl) ⟨20363381, by rfl⟩ : syracuseStep 27151175 = 40726763) B40726763
theorem B18100783 : Blo 1983435 18100783 := bstep (se 1 (by rfl) ⟨13575587, by rfl⟩ : syracuseStep 18100783 = 27151175) B27151175
theorem B24134377 : Blo 1983435 24134377 := bstep (se 2 (by rfl) ⟨9050391, by rfl⟩ : syracuseStep 24134377 = 18100783) B18100783
theorem B32179169 : Blo 1983435 32179169 := bstep (se 2 (by rfl) ⟨12067188, by rfl⟩ : syracuseStep 32179169 = 24134377) B24134377
theorem B21452779 : Blo 1983435 21452779 := bstep (se 1 (by rfl) ⟨16089584, by rfl⟩ : syracuseStep 21452779 = 32179169) B32179169
theorem B28603705 : Blo 1983435 28603705 := bstep (se 2 (by rfl) ⟨10726389, by rfl⟩ : syracuseStep 28603705 = 21452779) B21452779
theorem B38138273 : Blo 1983435 38138273 := bstep (se 2 (by rfl) ⟨14301852, by rfl⟩ : syracuseStep 38138273 = 28603705) B28603705
theorem B25425515 : Blo 1983435 25425515 := bstep (se 1 (by rfl) ⟨19069136, by rfl⟩ : syracuseStep 25425515 = 38138273) B38138273
theorem B16950343 : Blo 1983435 16950343 := bstep (se 1 (by rfl) ⟨12712757, by rfl⟩ : syracuseStep 16950343 = 25425515) B25425515
theorem B22600457 : Blo 1983435 22600457 := bstep (se 2 (by rfl) ⟨8475171, by rfl⟩ : syracuseStep 22600457 = 16950343) B16950343
theorem B15066971 : Blo 1983435 15066971 := bstep (se 1 (by rfl) ⟨11300228, by rfl⟩ : syracuseStep 15066971 = 22600457) B22600457
theorem B10044647 : Blo 1983435 10044647 := bstep (se 1 (by rfl) ⟨7533485, by rfl⟩ : syracuseStep 10044647 = 15066971) B15066971
theorem B6696431 : Blo 1983435 6696431 := bstep (se 1 (by rfl) ⟨5022323, by rfl⟩ : syracuseStep 6696431 = 10044647) B10044647
theorem B4464287 : Blo 1983435 4464287 := bstep (se 1 (by rfl) ⟨3348215, by rfl⟩ : syracuseStep 4464287 = 6696431) B6696431
theorem B2976191 : Blo 1983435 2976191 := bstep (se 1 (by rfl) ⟨2232143, by rfl⟩ : syracuseStep 2976191 = 4464287) B4464287
theorem B1984127 : Blo 1983435 1984127 := bstep (se 1 (by rfl) ⟨1488095, by rfl⟩ : syracuseStep 1984127 = 2976191) B2976191
theorem B2976197 : Blo 1983435 2976197 := bbase (se 4 (by rfl) ⟨279018, by rfl⟩ : syracuseStep 2976197 = 558037) (by norm_num)
theorem B1984131 : Blo 1983435 1984131 := bstep (se 1 (by rfl) ⟨1488098, by rfl⟩ : syracuseStep 1984131 = 2976197) B2976197
theorem B3348229 : Blo 1983435 3348229 := bbase (se 4 (by rfl) ⟨313896, by rfl⟩ : syracuseStep 3348229 = 627793) (by norm_num)
theorem B4464305 : Blo 1983435 4464305 := bstep (se 2 (by rfl) ⟨1674114, by rfl⟩ : syracuseStep 4464305 = 3348229) B3348229
theorem B2976203 : Blo 1983435 2976203 := bstep (se 1 (by rfl) ⟨2232152, by rfl⟩ : syracuseStep 2976203 = 4464305) B4464305
theorem B1984135 : Blo 1983435 1984135 := bstep (se 1 (by rfl) ⟨1488101, by rfl⟩ : syracuseStep 1984135 = 2976203) B2976203
theorem B2232157 : Blo 1983435 2232157 := bbase (se 3 (by rfl) ⟨418529, by rfl⟩ : syracuseStep 2232157 = 837059) (by norm_num)
theorem B2976209 : Blo 1983435 2976209 := bstep (se 2 (by rfl) ⟨1116078, by rfl⟩ : syracuseStep 2976209 = 2232157) B2232157
theorem B1984139 : Blo 1983435 1984139 := bstep (se 1 (by rfl) ⟨1488104, by rfl⟩ : syracuseStep 1984139 = 2976209) B2976209
theorem B6696485 : Blo 1983435 6696485 := bbase (se 4 (by rfl) ⟨627795, by rfl⟩ : syracuseStep 6696485 = 1255591) (by norm_num)
theorem B4464323 : Blo 1983435 4464323 := bstep (se 1 (by rfl) ⟨3348242, by rfl⟩ : syracuseStep 4464323 = 6696485) B6696485
theorem B2976215 : Blo 1983435 2976215 := bstep (se 1 (by rfl) ⟨2232161, by rfl⟩ : syracuseStep 2976215 = 4464323) B4464323
theorem B1984143 : Blo 1983435 1984143 := bstep (se 1 (by rfl) ⟨1488107, by rfl⟩ : syracuseStep 1984143 = 2976215) B2976215
theorem B2976221 : Blo 1983435 2976221 := bbase (se 3 (by rfl) ⟨558041, by rfl⟩ : syracuseStep 2976221 = 1116083) (by norm_num)
theorem B1984147 : Blo 1983435 1984147 := bstep (se 1 (by rfl) ⟨1488110, by rfl⟩ : syracuseStep 1984147 = 2976221) B2976221
theorem B4464341 : Blo 1983435 4464341 := bbase (se 7 (by rfl) ⟨52316, by rfl⟩ : syracuseStep 4464341 = 104633) (by norm_num)
theorem B2976227 : Blo 1983435 2976227 := bstep (se 1 (by rfl) ⟨2232170, by rfl⟩ : syracuseStep 2976227 = 4464341) B4464341
theorem B1984151 : Blo 1983435 1984151 := bstep (se 1 (by rfl) ⟨1488113, by rfl⟩ : syracuseStep 1984151 = 2976227) B2976227
theorem B4587005 : Blo 1983435 4587005 := bbase (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) (by norm_num)
theorem B3058003 : Blo 1983435 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B16309349 : Blo 1983435 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B10872899 : Blo 1983435 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B7248599 : Blo 1983435 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B4832399 : Blo 1983435 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B12886397 : Blo 1983435 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B8590931 : Blo 1983435 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B5727287 : Blo 1983435 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3818191 : Blo 1983435 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B5090921 : Blo 1983435 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B3393947 : Blo 1983435 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B9050525 : Blo 1983435 9050525 := bstep (se 3 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 9050525 = 3393947) B3393947
theorem B6033683 : Blo 1983435 6033683 := bstep (se 1 (by rfl) ⟨4525262, by rfl⟩ : syracuseStep 6033683 = 9050525) B9050525
theorem B4022455 : Blo 1983435 4022455 := bstep (se 1 (by rfl) ⟨3016841, by rfl⟩ : syracuseStep 4022455 = 6033683) B6033683
theorem B5363273 : Blo 1983435 5363273 := bstep (se 2 (by rfl) ⟨2011227, by rfl⟩ : syracuseStep 5363273 = 4022455) B4022455
theorem B3575515 : Blo 1983435 3575515 := bstep (se 1 (by rfl) ⟨2681636, by rfl⟩ : syracuseStep 3575515 = 5363273) B5363273
theorem B4767353 : Blo 1983435 4767353 := bstep (se 2 (by rfl) ⟨1787757, by rfl⟩ : syracuseStep 4767353 = 3575515) B3575515
theorem B3178235 : Blo 1983435 3178235 := bstep (se 1 (by rfl) ⟨2383676, by rfl⟩ : syracuseStep 3178235 = 4767353) B4767353
theorem B8475293 : Blo 1983435 8475293 := bstep (se 3 (by rfl) ⟨1589117, by rfl⟩ : syracuseStep 8475293 = 3178235) B3178235
theorem B5650195 : Blo 1983435 5650195 := bstep (se 1 (by rfl) ⟨4237646, by rfl⟩ : syracuseStep 5650195 = 8475293) B8475293
theorem B7533593 : Blo 1983435 7533593 := bstep (se 2 (by rfl) ⟨2825097, by rfl⟩ : syracuseStep 7533593 = 5650195) B5650195
theorem B5022395 : Blo 1983435 5022395 := bstep (se 1 (by rfl) ⟨3766796, by rfl⟩ : syracuseStep 5022395 = 7533593) B7533593
theorem B3348263 : Blo 1983435 3348263 := bstep (se 1 (by rfl) ⟨2511197, by rfl⟩ : syracuseStep 3348263 = 5022395) B5022395
theorem B2232175 : Blo 1983435 2232175 := bstep (se 1 (by rfl) ⟨1674131, by rfl⟩ : syracuseStep 2232175 = 3348263) B3348263
theorem B2976233 : Blo 1983435 2976233 := bstep (se 2 (by rfl) ⟨1116087, by rfl⟩ : syracuseStep 2976233 = 2232175) B2232175
theorem B1984155 : Blo 1983435 1984155 := bstep (se 1 (by rfl) ⟨1488116, by rfl⟩ : syracuseStep 1984155 = 2976233) B2976233
theorem B10181861 : Blo 1983435 10181861 := bbase (se 4 (by rfl) ⟨954549, by rfl⟩ : syracuseStep 10181861 = 1909099) (by norm_num)
theorem B6787907 : Blo 1983435 6787907 := bstep (se 1 (by rfl) ⟨5090930, by rfl⟩ : syracuseStep 6787907 = 10181861) B10181861
theorem B4525271 : Blo 1983435 4525271 := bstep (se 1 (by rfl) ⟨3393953, by rfl⟩ : syracuseStep 4525271 = 6787907) B6787907
theorem B3016847 : Blo 1983435 3016847 := bstep (se 1 (by rfl) ⟨2262635, by rfl⟩ : syracuseStep 3016847 = 4525271) B4525271
theorem B2011231 : Blo 1983435 2011231 := bstep (se 1 (by rfl) ⟨1508423, by rfl⟩ : syracuseStep 2011231 = 3016847) B3016847
theorem B2681641 : Blo 1983435 2681641 := bstep (se 2 (by rfl) ⟨1005615, by rfl⟩ : syracuseStep 2681641 = 2011231) B2011231
theorem B3575521 : Blo 1983435 3575521 := bstep (se 2 (by rfl) ⟨1340820, by rfl⟩ : syracuseStep 3575521 = 2681641) B2681641
theorem B19069445 : Blo 1983435 19069445 := bstep (se 4 (by rfl) ⟨1787760, by rfl⟩ : syracuseStep 19069445 = 3575521) B3575521
theorem B12712963 : Blo 1983435 12712963 := bstep (se 1 (by rfl) ⟨9534722, by rfl⟩ : syracuseStep 12712963 = 19069445) B19069445
theorem B16950617 : Blo 1983435 16950617 := bstep (se 2 (by rfl) ⟨6356481, by rfl⟩ : syracuseStep 16950617 = 12712963) B12712963
theorem B11300411 : Blo 1983435 11300411 := bstep (se 1 (by rfl) ⟨8475308, by rfl⟩ : syracuseStep 11300411 = 16950617) B16950617
theorem B7533607 : Blo 1983435 7533607 := bstep (se 1 (by rfl) ⟨5650205, by rfl⟩ : syracuseStep 7533607 = 11300411) B11300411
theorem B10044809 : Blo 1983435 10044809 := bstep (se 2 (by rfl) ⟨3766803, by rfl⟩ : syracuseStep 10044809 = 7533607) B7533607
theorem B6696539 : Blo 1983435 6696539 := bstep (se 1 (by rfl) ⟨5022404, by rfl⟩ : syracuseStep 6696539 = 10044809) B10044809
theorem B4464359 : Blo 1983435 4464359 := bstep (se 1 (by rfl) ⟨3348269, by rfl⟩ : syracuseStep 4464359 = 6696539) B6696539
theorem B2976239 : Blo 1983435 2976239 := bstep (se 1 (by rfl) ⟨2232179, by rfl⟩ : syracuseStep 2976239 = 4464359) B4464359
theorem B1984159 : Blo 1983435 1984159 := bstep (se 1 (by rfl) ⟨1488119, by rfl⟩ : syracuseStep 1984159 = 2976239) B2976239
theorem B2976245 : Blo 1983435 2976245 := bbase (se 5 (by rfl) ⟨139511, by rfl⟩ : syracuseStep 2976245 = 279023) (by norm_num)
theorem B1984163 : Blo 1983435 1984163 := bstep (se 1 (by rfl) ⟨1488122, by rfl⟩ : syracuseStep 1984163 = 2976245) B2976245
theorem B5650229 : Blo 1983435 5650229 := bbase (se 5 (by rfl) ⟨264854, by rfl⟩ : syracuseStep 5650229 = 529709) (by norm_num)
theorem B3766819 : Blo 1983435 3766819 := bstep (se 1 (by rfl) ⟨2825114, by rfl⟩ : syracuseStep 3766819 = 5650229) B5650229
theorem B5022425 : Blo 1983435 5022425 := bstep (se 2 (by rfl) ⟨1883409, by rfl⟩ : syracuseStep 5022425 = 3766819) B3766819
theorem B3348283 : Blo 1983435 3348283 := bstep (se 1 (by rfl) ⟨2511212, by rfl⟩ : syracuseStep 3348283 = 5022425) B5022425
theorem B4464377 : Blo 1983435 4464377 := bstep (se 2 (by rfl) ⟨1674141, by rfl⟩ : syracuseStep 4464377 = 3348283) B3348283
theorem B2976251 : Blo 1983435 2976251 := bstep (se 1 (by rfl) ⟨2232188, by rfl⟩ : syracuseStep 2976251 = 4464377) B4464377
theorem B1984167 : Blo 1983435 1984167 := bstep (se 1 (by rfl) ⟨1488125, by rfl⟩ : syracuseStep 1984167 = 2976251) B2976251
theorem B2232193 : Blo 1983435 2232193 := bbase (se 2 (by rfl) ⟨837072, by rfl⟩ : syracuseStep 2232193 = 1674145) (by norm_num)
theorem B2976257 : Blo 1983435 2976257 := bstep (se 2 (by rfl) ⟨1116096, by rfl⟩ : syracuseStep 2976257 = 2232193) B2232193
theorem B1984171 : Blo 1983435 1984171 := bstep (se 1 (by rfl) ⟨1488128, by rfl⟩ : syracuseStep 1984171 = 2976257) B2976257
theorem B5022445 : Blo 1983435 5022445 := bbase (se 3 (by rfl) ⟨941708, by rfl⟩ : syracuseStep 5022445 = 1883417) (by norm_num)
theorem B6696593 : Blo 1983435 6696593 := bstep (se 2 (by rfl) ⟨2511222, by rfl⟩ : syracuseStep 6696593 = 5022445) B5022445
theorem B4464395 : Blo 1983435 4464395 := bstep (se 1 (by rfl) ⟨3348296, by rfl⟩ : syracuseStep 4464395 = 6696593) B6696593
theorem B2976263 : Blo 1983435 2976263 := bstep (se 1 (by rfl) ⟨2232197, by rfl⟩ : syracuseStep 2976263 = 4464395) B4464395
theorem B1984175 : Blo 1983435 1984175 := bstep (se 1 (by rfl) ⟨1488131, by rfl⟩ : syracuseStep 1984175 = 2976263) B2976263
theorem B2976269 : Blo 1983435 2976269 := bbase (se 3 (by rfl) ⟨558050, by rfl⟩ : syracuseStep 2976269 = 1116101) (by norm_num)
theorem B1984179 : Blo 1983435 1984179 := bstep (se 1 (by rfl) ⟨1488134, by rfl⟩ : syracuseStep 1984179 = 2976269) B2976269
theorem B4464413 : Blo 1983435 4464413 := bbase (se 3 (by rfl) ⟨837077, by rfl⟩ : syracuseStep 4464413 = 1674155) (by norm_num)
theorem B2976275 : Blo 1983435 2976275 := bstep (se 1 (by rfl) ⟨2232206, by rfl⟩ : syracuseStep 2976275 = 4464413) B4464413
theorem B1984183 : Blo 1983435 1984183 := bstep (se 1 (by rfl) ⟨1488137, by rfl⟩ : syracuseStep 1984183 = 2976275) B2976275
theorem B3348317 : Blo 1983435 3348317 := bbase (se 3 (by rfl) ⟨627809, by rfl⟩ : syracuseStep 3348317 = 1255619) (by norm_num)
theorem B2232211 : Blo 1983435 2232211 := bstep (se 1 (by rfl) ⟨1674158, by rfl⟩ : syracuseStep 2232211 = 3348317) B3348317
theorem B2976281 : Blo 1983435 2976281 := bstep (se 2 (by rfl) ⟨1116105, by rfl⟩ : syracuseStep 2976281 = 2232211) B2232211
theorem B1984187 : Blo 1983435 1984187 := bstep (se 1 (by rfl) ⟨1488140, by rfl⟩ : syracuseStep 1984187 = 2976281) B2976281
theorem B8475445 : Blo 1983435 8475445 := bbase (se 5 (by rfl) ⟨397286, by rfl⟩ : syracuseStep 8475445 = 794573) (by norm_num)
theorem B11300593 : Blo 1983435 11300593 := bstep (se 2 (by rfl) ⟨4237722, by rfl⟩ : syracuseStep 11300593 = 8475445) B8475445
theorem B15067457 : Blo 1983435 15067457 := bstep (se 2 (by rfl) ⟨5650296, by rfl⟩ : syracuseStep 15067457 = 11300593) B11300593
theorem B10044971 : Blo 1983435 10044971 := bstep (se 1 (by rfl) ⟨7533728, by rfl⟩ : syracuseStep 10044971 = 15067457) B15067457
theorem B6696647 : Blo 1983435 6696647 := bstep (se 1 (by rfl) ⟨5022485, by rfl⟩ : syracuseStep 6696647 = 10044971) B10044971
theorem B4464431 : Blo 1983435 4464431 := bstep (se 1 (by rfl) ⟨3348323, by rfl⟩ : syracuseStep 4464431 = 6696647) B6696647
theorem B2976287 : Blo 1983435 2976287 := bstep (se 1 (by rfl) ⟨2232215, by rfl⟩ : syracuseStep 2976287 = 4464431) B4464431
theorem B1984191 : Blo 1983435 1984191 := bstep (se 1 (by rfl) ⟨1488143, by rfl⟩ : syracuseStep 1984191 = 2976287) B2976287
theorem B2976293 : Blo 1983435 2976293 := bbase (se 4 (by rfl) ⟨279027, by rfl⟩ : syracuseStep 2976293 = 558055) (by norm_num)
theorem B1984195 : Blo 1983435 1984195 := bstep (se 1 (by rfl) ⟨1488146, by rfl⟩ : syracuseStep 1984195 = 2976293) B2976293
theorem B2511253 : Blo 1983435 2511253 := bbase (se 6 (by rfl) ⟨58857, by rfl⟩ : syracuseStep 2511253 = 117715) (by norm_num)
theorem B3348337 : Blo 1983435 3348337 := bstep (se 2 (by rfl) ⟨1255626, by rfl⟩ : syracuseStep 3348337 = 2511253) B2511253
theorem B4464449 : Blo 1983435 4464449 := bstep (se 2 (by rfl) ⟨1674168, by rfl⟩ : syracuseStep 4464449 = 3348337) B3348337
theorem B2976299 : Blo 1983435 2976299 := bstep (se 1 (by rfl) ⟨2232224, by rfl⟩ : syracuseStep 2976299 = 4464449) B4464449
theorem B1984199 : Blo 1983435 1984199 := bstep (se 1 (by rfl) ⟨1488149, by rfl⟩ : syracuseStep 1984199 = 2976299) B2976299
theorem B2232229 : Blo 1983435 2232229 := bbase (se 4 (by rfl) ⟨209271, by rfl⟩ : syracuseStep 2232229 = 418543) (by norm_num)
theorem B2976305 : Blo 1983435 2976305 := bstep (se 2 (by rfl) ⟨1116114, by rfl⟩ : syracuseStep 2976305 = 2232229) B2232229
theorem B1984203 : Blo 1983435 1984203 := bstep (se 1 (by rfl) ⟨1488152, by rfl⟩ : syracuseStep 1984203 = 2976305) B2976305
theorem B2863717 : Blo 1983435 2863717 := bbase (se 4 (by rfl) ⟨268473, by rfl⟩ : syracuseStep 2863717 = 536947) (by norm_num)
theorem B61092629 : Blo 1983435 61092629 := bstep (se 6 (by rfl) ⟨1431858, by rfl⟩ : syracuseStep 61092629 = 2863717) B2863717
theorem B40728419 : Blo 1983435 40728419 := bstep (se 1 (by rfl) ⟨30546314, by rfl⟩ : syracuseStep 40728419 = 61092629) B61092629
theorem B27152279 : Blo 1983435 27152279 := bstep (se 1 (by rfl) ⟨20364209, by rfl⟩ : syracuseStep 27152279 = 40728419) B40728419
theorem B18101519 : Blo 1983435 18101519 := bstep (se 1 (by rfl) ⟨13576139, by rfl⟩ : syracuseStep 18101519 = 27152279) B27152279
theorem B12067679 : Blo 1983435 12067679 := bstep (se 1 (by rfl) ⟨9050759, by rfl⟩ : syracuseStep 12067679 = 18101519) B18101519
theorem B8045119 : Blo 1983435 8045119 := bstep (se 1 (by rfl) ⟨6033839, by rfl⟩ : syracuseStep 8045119 = 12067679) B12067679
theorem B10726825 : Blo 1983435 10726825 := bstep (se 2 (by rfl) ⟨4022559, by rfl⟩ : syracuseStep 10726825 = 8045119) B8045119
theorem B14302433 : Blo 1983435 14302433 := bstep (se 2 (by rfl) ⟨5363412, by rfl⟩ : syracuseStep 14302433 = 10726825) B10726825
theorem B9534955 : Blo 1983435 9534955 := bstep (se 1 (by rfl) ⟨7151216, by rfl⟩ : syracuseStep 9534955 = 14302433) B14302433
theorem B12713273 : Blo 1983435 12713273 := bstep (se 2 (by rfl) ⟨4767477, by rfl⟩ : syracuseStep 12713273 = 9534955) B9534955
theorem B8475515 : Blo 1983435 8475515 := bstep (se 1 (by rfl) ⟨6356636, by rfl⟩ : syracuseStep 8475515 = 12713273) B12713273
theorem B5650343 : Blo 1983435 5650343 := bstep (se 1 (by rfl) ⟨4237757, by rfl⟩ : syracuseStep 5650343 = 8475515) B8475515
theorem B3766895 : Blo 1983435 3766895 := bstep (se 1 (by rfl) ⟨2825171, by rfl⟩ : syracuseStep 3766895 = 5650343) B5650343
theorem B2511263 : Blo 1983435 2511263 := bstep (se 1 (by rfl) ⟨1883447, by rfl⟩ : syracuseStep 2511263 = 3766895) B3766895
theorem B6696701 : Blo 1983435 6696701 := bstep (se 3 (by rfl) ⟨1255631, by rfl⟩ : syracuseStep 6696701 = 2511263) B2511263
theorem B4464467 : Blo 1983435 4464467 := bstep (se 1 (by rfl) ⟨3348350, by rfl⟩ : syracuseStep 4464467 = 6696701) B6696701
theorem B2976311 : Blo 1983435 2976311 := bstep (se 1 (by rfl) ⟨2232233, by rfl⟩ : syracuseStep 2976311 = 4464467) B4464467
theorem B1984207 : Blo 1983435 1984207 := bstep (se 1 (by rfl) ⟨1488155, by rfl⟩ : syracuseStep 1984207 = 2976311) B2976311
theorem B2976317 : Blo 1983435 2976317 := bbase (se 3 (by rfl) ⟨558059, by rfl⟩ : syracuseStep 2976317 = 1116119) (by norm_num)
theorem B1984211 : Blo 1983435 1984211 := bstep (se 1 (by rfl) ⟨1488158, by rfl⟩ : syracuseStep 1984211 = 2976317) B2976317
theorem B4464485 : Blo 1983435 4464485 := bbase (se 4 (by rfl) ⟨418545, by rfl⟩ : syracuseStep 4464485 = 837091) (by norm_num)
theorem B2976323 : Blo 1983435 2976323 := bstep (se 1 (by rfl) ⟨2232242, by rfl⟩ : syracuseStep 2976323 = 4464485) B4464485
theorem B1984215 : Blo 1983435 1984215 := bstep (se 1 (by rfl) ⟨1488161, by rfl⟩ : syracuseStep 1984215 = 2976323) B2976323
theorem B5022557 : Blo 1983435 5022557 := bbase (se 3 (by rfl) ⟨941729, by rfl⟩ : syracuseStep 5022557 = 1883459) (by norm_num)
theorem B3348371 : Blo 1983435 3348371 := bstep (se 1 (by rfl) ⟨2511278, by rfl⟩ : syracuseStep 3348371 = 5022557) B5022557
theorem B2232247 : Blo 1983435 2232247 := bstep (se 1 (by rfl) ⟨1674185, by rfl⟩ : syracuseStep 2232247 = 3348371) B3348371
theorem B2976329 : Blo 1983435 2976329 := bstep (se 2 (by rfl) ⟨1116123, by rfl⟩ : syracuseStep 2976329 = 2232247) B2232247
theorem B1984219 : Blo 1983435 1984219 := bstep (se 1 (by rfl) ⟨1488164, by rfl⟩ : syracuseStep 1984219 = 2976329) B2976329
theorem B3766925 : Blo 1983435 3766925 := bbase (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) (by norm_num)
theorem B10045133 : Blo 1983435 10045133 := bstep (se 3 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 10045133 = 3766925) B3766925
theorem B6696755 : Blo 1983435 6696755 := bstep (se 1 (by rfl) ⟨5022566, by rfl⟩ : syracuseStep 6696755 = 10045133) B10045133
theorem B4464503 : Blo 1983435 4464503 := bstep (se 1 (by rfl) ⟨3348377, by rfl⟩ : syracuseStep 4464503 = 6696755) B6696755
theorem B2976335 : Blo 1983435 2976335 := bstep (se 1 (by rfl) ⟨2232251, by rfl⟩ : syracuseStep 2976335 = 4464503) B4464503
theorem B1984223 : Blo 1983435 1984223 := bstep (se 1 (by rfl) ⟨1488167, by rfl⟩ : syracuseStep 1984223 = 2976335) B2976335
theorem B2976341 : Blo 1983435 2976341 := bbase (se 8 (by rfl) ⟨17439, by rfl⟩ : syracuseStep 2976341 = 34879) (by norm_num)
theorem B1984227 : Blo 1983435 1984227 := bstep (se 1 (by rfl) ⟨1488170, by rfl⟩ : syracuseStep 1984227 = 2976341) B2976341
theorem B9050869 : Blo 1983435 9050869 := bbase (se 5 (by rfl) ⟨424259, by rfl⟩ : syracuseStep 9050869 = 848519) (by norm_num)
theorem B12067825 : Blo 1983435 12067825 := bstep (se 2 (by rfl) ⟨4525434, by rfl⟩ : syracuseStep 12067825 = 9050869) B9050869
theorem B16090433 : Blo 1983435 16090433 := bstep (se 2 (by rfl) ⟨6033912, by rfl⟩ : syracuseStep 16090433 = 12067825) B12067825
theorem B10726955 : Blo 1983435 10726955 := bstep (se 1 (by rfl) ⟨8045216, by rfl⟩ : syracuseStep 10726955 = 16090433) B16090433
theorem B7151303 : Blo 1983435 7151303 := bstep (se 1 (by rfl) ⟨5363477, by rfl⟩ : syracuseStep 7151303 = 10726955) B10726955
theorem B4767535 : Blo 1983435 4767535 := bstep (se 1 (by rfl) ⟨3575651, by rfl⟩ : syracuseStep 4767535 = 7151303) B7151303
theorem B6356713 : Blo 1983435 6356713 := bstep (se 2 (by rfl) ⟨2383767, by rfl⟩ : syracuseStep 6356713 = 4767535) B4767535
theorem B8475617 : Blo 1983435 8475617 := bstep (se 2 (by rfl) ⟨3178356, by rfl⟩ : syracuseStep 8475617 = 6356713) B6356713
theorem B5650411 : Blo 1983435 5650411 := bstep (se 1 (by rfl) ⟨4237808, by rfl⟩ : syracuseStep 5650411 = 8475617) B8475617
theorem B7533881 : Blo 1983435 7533881 := bstep (se 2 (by rfl) ⟨2825205, by rfl⟩ : syracuseStep 7533881 = 5650411) B5650411
theorem B5022587 : Blo 1983435 5022587 := bstep (se 1 (by rfl) ⟨3766940, by rfl⟩ : syracuseStep 5022587 = 7533881) B7533881
theorem B3348391 : Blo 1983435 3348391 := bstep (se 1 (by rfl) ⟨2511293, by rfl⟩ : syracuseStep 3348391 = 5022587) B5022587
theorem B4464521 : Blo 1983435 4464521 := bstep (se 2 (by rfl) ⟨1674195, by rfl⟩ : syracuseStep 4464521 = 3348391) B3348391
theorem B2976347 : Blo 1983435 2976347 := bstep (se 1 (by rfl) ⟨2232260, by rfl⟩ : syracuseStep 2976347 = 4464521) B4464521
theorem B1984231 : Blo 1983435 1984231 := bstep (se 1 (by rfl) ⟨1488173, by rfl⟩ : syracuseStep 1984231 = 2976347) B2976347
theorem B2232265 : Blo 1983435 2232265 := bbase (se 2 (by rfl) ⟨837099, by rfl⟩ : syracuseStep 2232265 = 1674199) (by norm_num)
theorem B2976353 : Blo 1983435 2976353 := bstep (se 2 (by rfl) ⟨1116132, by rfl⟩ : syracuseStep 2976353 = 2232265) B2232265
theorem B1984235 : Blo 1983435 1984235 := bstep (se 1 (by rfl) ⟨1488176, by rfl⟩ : syracuseStep 1984235 = 2976353) B2976353
theorem B2383777 : Blo 1983435 2383777 := bbase (se 2 (by rfl) ⟨893916, by rfl⟩ : syracuseStep 2383777 = 1787833) (by norm_num)
theorem B3178369 : Blo 1983435 3178369 := bstep (se 2 (by rfl) ⟨1191888, by rfl⟩ : syracuseStep 3178369 = 2383777) B2383777
theorem B16951301 : Blo 1983435 16951301 := bstep (se 4 (by rfl) ⟨1589184, by rfl⟩ : syracuseStep 16951301 = 3178369) B3178369
theorem B11300867 : Blo 1983435 11300867 := bstep (se 1 (by rfl) ⟨8475650, by rfl⟩ : syracuseStep 11300867 = 16951301) B16951301
theorem B7533911 : Blo 1983435 7533911 := bstep (se 1 (by rfl) ⟨5650433, by rfl⟩ : syracuseStep 7533911 = 11300867) B11300867
theorem B5022607 : Blo 1983435 5022607 := bstep (se 1 (by rfl) ⟨3766955, by rfl⟩ : syracuseStep 5022607 = 7533911) B7533911
theorem B6696809 : Blo 1983435 6696809 := bstep (se 2 (by rfl) ⟨2511303, by rfl⟩ : syracuseStep 6696809 = 5022607) B5022607
theorem B4464539 : Blo 1983435 4464539 := bstep (se 1 (by rfl) ⟨3348404, by rfl⟩ : syracuseStep 4464539 = 6696809) B6696809
theorem B2976359 : Blo 1983435 2976359 := bstep (se 1 (by rfl) ⟨2232269, by rfl⟩ : syracuseStep 2976359 = 4464539) B4464539
theorem B1984239 : Blo 1983435 1984239 := bstep (se 1 (by rfl) ⟨1488179, by rfl⟩ : syracuseStep 1984239 = 2976359) B2976359
theorem B2976365 : Blo 1983435 2976365 := bbase (se 3 (by rfl) ⟨558068, by rfl⟩ : syracuseStep 2976365 = 1116137) (by norm_num)
theorem B1984243 : Blo 1983435 1984243 := bstep (se 1 (by rfl) ⟨1488182, by rfl⟩ : syracuseStep 1984243 = 2976365) B2976365
theorem B4464557 : Blo 1983435 4464557 := bbase (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) (by norm_num)
theorem B2976371 : Blo 1983435 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B1984247 : Blo 1983435 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B5650469 : Blo 1983435 5650469 := bbase (se 4 (by rfl) ⟨529731, by rfl⟩ : syracuseStep 5650469 = 1059463) (by norm_num)
theorem B3766979 : Blo 1983435 3766979 := bstep (se 1 (by rfl) ⟨2825234, by rfl⟩ : syracuseStep 3766979 = 5650469) B5650469
theorem B2511319 : Blo 1983435 2511319 := bstep (se 1 (by rfl) ⟨1883489, by rfl⟩ : syracuseStep 2511319 = 3766979) B3766979
theorem B3348425 : Blo 1983435 3348425 := bstep (se 2 (by rfl) ⟨1255659, by rfl⟩ : syracuseStep 3348425 = 2511319) B2511319
theorem B2232283 : Blo 1983435 2232283 := bstep (se 1 (by rfl) ⟨1674212, by rfl⟩ : syracuseStep 2232283 = 3348425) B3348425
theorem B2976377 : Blo 1983435 2976377 := bstep (se 2 (by rfl) ⟨1116141, by rfl⟩ : syracuseStep 2976377 = 2232283) B2232283
theorem B1984251 : Blo 1983435 1984251 := bstep (se 1 (by rfl) ⟨1488188, by rfl⟩ : syracuseStep 1984251 = 2976377) B2976377
theorem B2066585 : Blo 1983435 2066585 := bbase (se 2 (by rfl) ⟨774969, by rfl⟩ : syracuseStep 2066585 = 1549939) (by norm_num)
theorem B22043573 : Blo 1983435 22043573 := bstep (se 5 (by rfl) ⟨1033292, by rfl⟩ : syracuseStep 22043573 = 2066585) B2066585
theorem B14695715 : Blo 1983435 14695715 := bstep (se 1 (by rfl) ⟨11021786, by rfl⟩ : syracuseStep 14695715 = 22043573) B22043573
theorem B39188573 : Blo 1983435 39188573 := bstep (se 3 (by rfl) ⟨7347857, by rfl⟩ : syracuseStep 39188573 = 14695715) B14695715
theorem B26125715 : Blo 1983435 26125715 := bstep (se 1 (by rfl) ⟨19594286, by rfl⟩ : syracuseStep 26125715 = 39188573) B39188573
theorem B17417143 : Blo 1983435 17417143 := bstep (se 1 (by rfl) ⟨13062857, by rfl⟩ : syracuseStep 17417143 = 26125715) B26125715
theorem B23222857 : Blo 1983435 23222857 := bstep (se 2 (by rfl) ⟨8708571, by rfl⟩ : syracuseStep 23222857 = 17417143) B17417143
theorem B30963809 : Blo 1983435 30963809 := bstep (se 2 (by rfl) ⟨11611428, by rfl⟩ : syracuseStep 30963809 = 23222857) B23222857
theorem B20642539 : Blo 1983435 20642539 := bstep (se 1 (by rfl) ⟨15481904, by rfl⟩ : syracuseStep 20642539 = 30963809) B30963809
theorem B27523385 : Blo 1983435 27523385 := bstep (se 2 (by rfl) ⟨10321269, by rfl⟩ : syracuseStep 27523385 = 20642539) B20642539
theorem B18348923 : Blo 1983435 18348923 := bstep (se 1 (by rfl) ⟨13761692, by rfl⟩ : syracuseStep 18348923 = 27523385) B27523385
theorem B12232615 : Blo 1983435 12232615 := bstep (se 1 (by rfl) ⟨9174461, by rfl⟩ : syracuseStep 12232615 = 18348923) B18348923
theorem B16310153 : Blo 1983435 16310153 := bstep (se 2 (by rfl) ⟨6116307, by rfl⟩ : syracuseStep 16310153 = 12232615) B12232615
theorem B43493741 : Blo 1983435 43493741 := bstep (se 3 (by rfl) ⟨8155076, by rfl⟩ : syracuseStep 43493741 = 16310153) B16310153
theorem B28995827 : Blo 1983435 28995827 := bstep (se 1 (by rfl) ⟨21746870, by rfl⟩ : syracuseStep 28995827 = 43493741) B43493741
theorem B77322205 : Blo 1983435 77322205 := bstep (se 3 (by rfl) ⟨14497913, by rfl⟩ : syracuseStep 77322205 = 28995827) B28995827
theorem B103096273 : Blo 1983435 103096273 := bstep (se 2 (by rfl) ⟨38661102, by rfl⟩ : syracuseStep 103096273 = 77322205) B77322205
theorem B137461697 : Blo 1983435 137461697 := bstep (se 2 (by rfl) ⟨51548136, by rfl⟩ : syracuseStep 137461697 = 103096273) B103096273
theorem B91641131 : Blo 1983435 91641131 := bstep (se 1 (by rfl) ⟨68730848, by rfl⟩ : syracuseStep 91641131 = 137461697) B137461697
theorem B61094087 : Blo 1983435 61094087 := bstep (se 1 (by rfl) ⟨45820565, by rfl⟩ : syracuseStep 61094087 = 91641131) B91641131
theorem B40729391 : Blo 1983435 40729391 := bstep (se 1 (by rfl) ⟨30547043, by rfl⟩ : syracuseStep 40729391 = 61094087) B61094087
theorem B27152927 : Blo 1983435 27152927 := bstep (se 1 (by rfl) ⟨20364695, by rfl⟩ : syracuseStep 27152927 = 40729391) B40729391
theorem B18101951 : Blo 1983435 18101951 := bstep (se 1 (by rfl) ⟨13576463, by rfl⟩ : syracuseStep 18101951 = 27152927) B27152927
theorem B12067967 : Blo 1983435 12067967 := bstep (se 1 (by rfl) ⟨9050975, by rfl⟩ : syracuseStep 12067967 = 18101951) B18101951
theorem B32181245 : Blo 1983435 32181245 := bstep (se 3 (by rfl) ⟨6033983, by rfl⟩ : syracuseStep 32181245 = 12067967) B12067967
theorem B21454163 : Blo 1983435 21454163 := bstep (se 1 (by rfl) ⟨16090622, by rfl⟩ : syracuseStep 21454163 = 32181245) B32181245
theorem B14302775 : Blo 1983435 14302775 := bstep (se 1 (by rfl) ⟨10727081, by rfl⟩ : syracuseStep 14302775 = 21454163) B21454163
theorem B38140733 : Blo 1983435 38140733 := bstep (se 3 (by rfl) ⟨7151387, by rfl⟩ : syracuseStep 38140733 = 14302775) B14302775
theorem B25427155 : Blo 1983435 25427155 := bstep (se 1 (by rfl) ⟨19070366, by rfl⟩ : syracuseStep 25427155 = 38140733) B38140733
theorem B33902873 : Blo 1983435 33902873 := bstep (se 2 (by rfl) ⟨12713577, by rfl⟩ : syracuseStep 33902873 = 25427155) B25427155
theorem B22601915 : Blo 1983435 22601915 := bstep (se 1 (by rfl) ⟨16951436, by rfl⟩ : syracuseStep 22601915 = 33902873) B33902873
theorem B15067943 : Blo 1983435 15067943 := bstep (se 1 (by rfl) ⟨11300957, by rfl⟩ : syracuseStep 15067943 = 22601915) B22601915
theorem B10045295 : Blo 1983435 10045295 := bstep (se 1 (by rfl) ⟨7533971, by rfl⟩ : syracuseStep 10045295 = 15067943) B15067943
theorem B6696863 : Blo 1983435 6696863 := bstep (se 1 (by rfl) ⟨5022647, by rfl⟩ : syracuseStep 6696863 = 10045295) B10045295
theorem B4464575 : Blo 1983435 4464575 := bstep (se 1 (by rfl) ⟨3348431, by rfl⟩ : syracuseStep 4464575 = 6696863) B6696863
theorem B2976383 : Blo 1983435 2976383 := bstep (se 1 (by rfl) ⟨2232287, by rfl⟩ : syracuseStep 2976383 = 4464575) B4464575
theorem B1984255 : Blo 1983435 1984255 := bstep (se 1 (by rfl) ⟨1488191, by rfl⟩ : syracuseStep 1984255 = 2976383) B2976383
theorem B2976389 : Blo 1983435 2976389 := bbase (se 4 (by rfl) ⟨279036, by rfl⟩ : syracuseStep 2976389 = 558073) (by norm_num)
theorem B1984259 : Blo 1983435 1984259 := bstep (se 1 (by rfl) ⟨1488194, by rfl⟩ : syracuseStep 1984259 = 2976389) B2976389
theorem B3348445 : Blo 1983435 3348445 := bbase (se 3 (by rfl) ⟨627833, by rfl⟩ : syracuseStep 3348445 = 1255667) (by norm_num)
theorem B4464593 : Blo 1983435 4464593 := bstep (se 2 (by rfl) ⟨1674222, by rfl⟩ : syracuseStep 4464593 = 3348445) B3348445
theorem B2976395 : Blo 1983435 2976395 := bstep (se 1 (by rfl) ⟨2232296, by rfl⟩ : syracuseStep 2976395 = 4464593) B4464593
theorem B1984263 : Blo 1983435 1984263 := bstep (se 1 (by rfl) ⟨1488197, by rfl⟩ : syracuseStep 1984263 = 2976395) B2976395
theorem B2232301 : Blo 1983435 2232301 := bbase (se 3 (by rfl) ⟨418556, by rfl⟩ : syracuseStep 2232301 = 837113) (by norm_num)
theorem B2976401 : Blo 1983435 2976401 := bstep (se 2 (by rfl) ⟨1116150, by rfl⟩ : syracuseStep 2976401 = 2232301) B2232301
theorem B1984267 : Blo 1983435 1984267 := bstep (se 1 (by rfl) ⟨1488200, by rfl⟩ : syracuseStep 1984267 = 2976401) B2976401
theorem B6696917 : Blo 1983435 6696917 := bbase (se 7 (by rfl) ⟨78479, by rfl⟩ : syracuseStep 6696917 = 156959) (by norm_num)
theorem B4464611 : Blo 1983435 4464611 := bstep (se 1 (by rfl) ⟨3348458, by rfl⟩ : syracuseStep 4464611 = 6696917) B6696917
theorem B2976407 : Blo 1983435 2976407 := bstep (se 1 (by rfl) ⟨2232305, by rfl⟩ : syracuseStep 2976407 = 4464611) B4464611
theorem B1984271 : Blo 1983435 1984271 := bstep (se 1 (by rfl) ⟨1488203, by rfl⟩ : syracuseStep 1984271 = 2976407) B2976407
theorem B2976413 : Blo 1983435 2976413 := bbase (se 3 (by rfl) ⟨558077, by rfl⟩ : syracuseStep 2976413 = 1116155) (by norm_num)
theorem B1984275 : Blo 1983435 1984275 := bstep (se 1 (by rfl) ⟨1488206, by rfl⟩ : syracuseStep 1984275 = 2976413) B2976413
theorem B4464629 : Blo 1983435 4464629 := bbase (se 5 (by rfl) ⟨209279, by rfl⟩ : syracuseStep 4464629 = 418559) (by norm_num)
theorem B2976419 : Blo 1983435 2976419 := bstep (se 1 (by rfl) ⟨2232314, by rfl⟩ : syracuseStep 2976419 = 4464629) B4464629
theorem B1984279 : Blo 1983435 1984279 := bstep (se 1 (by rfl) ⟨1488209, by rfl⟩ : syracuseStep 1984279 = 2976419) B2976419
theorem B5727653 : Blo 1983435 5727653 := bbase (se 4 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 5727653 = 1073935) (by norm_num)
theorem B3818435 : Blo 1983435 3818435 := bstep (se 1 (by rfl) ⟨2863826, by rfl⟩ : syracuseStep 3818435 = 5727653) B5727653
theorem B10182493 : Blo 1983435 10182493 := bstep (se 3 (by rfl) ⟨1909217, by rfl⟩ : syracuseStep 10182493 = 3818435) B3818435
theorem B13576657 : Blo 1983435 13576657 := bstep (se 2 (by rfl) ⟨5091246, by rfl⟩ : syracuseStep 13576657 = 10182493) B10182493
theorem B18102209 : Blo 1983435 18102209 := bstep (se 2 (by rfl) ⟨6788328, by rfl⟩ : syracuseStep 18102209 = 13576657) B13576657
theorem B193090229 : Blo 1983435 193090229 := bstep (se 5 (by rfl) ⟨9051104, by rfl⟩ : syracuseStep 193090229 = 18102209) B18102209
theorem B128726819 : Blo 1983435 128726819 := bstep (se 1 (by rfl) ⟨96545114, by rfl⟩ : syracuseStep 128726819 = 193090229) B193090229
theorem B85817879 : Blo 1983435 85817879 := bstep (se 1 (by rfl) ⟨64363409, by rfl⟩ : syracuseStep 85817879 = 128726819) B128726819
theorem B57211919 : Blo 1983435 57211919 := bstep (se 1 (by rfl) ⟨42908939, by rfl⟩ : syracuseStep 57211919 = 85817879) B85817879
theorem B38141279 : Blo 1983435 38141279 := bstep (se 1 (by rfl) ⟨28605959, by rfl⟩ : syracuseStep 38141279 = 57211919) B57211919
theorem B25427519 : Blo 1983435 25427519 := bstep (se 1 (by rfl) ⟨19070639, by rfl⟩ : syracuseStep 25427519 = 38141279) B38141279
theorem B16951679 : Blo 1983435 16951679 := bstep (se 1 (by rfl) ⟨12713759, by rfl⟩ : syracuseStep 16951679 = 25427519) B25427519
theorem B11301119 : Blo 1983435 11301119 := bstep (se 1 (by rfl) ⟨8475839, by rfl⟩ : syracuseStep 11301119 = 16951679) B16951679
theorem B7534079 : Blo 1983435 7534079 := bstep (se 1 (by rfl) ⟨5650559, by rfl⟩ : syracuseStep 7534079 = 11301119) B11301119
theorem B5022719 : Blo 1983435 5022719 := bstep (se 1 (by rfl) ⟨3767039, by rfl⟩ : syracuseStep 5022719 = 7534079) B7534079
theorem B3348479 : Blo 1983435 3348479 := bstep (se 1 (by rfl) ⟨2511359, by rfl⟩ : syracuseStep 3348479 = 5022719) B5022719
theorem B2232319 : Blo 1983435 2232319 := bstep (se 1 (by rfl) ⟨1674239, by rfl⟩ : syracuseStep 2232319 = 3348479) B3348479
theorem B2976425 : Blo 1983435 2976425 := bstep (se 2 (by rfl) ⟨1116159, by rfl⟩ : syracuseStep 2976425 = 2232319) B2232319
theorem B1984283 : Blo 1983435 1984283 := bstep (se 1 (by rfl) ⟨1488212, by rfl⟩ : syracuseStep 1984283 = 2976425) B2976425
theorem B2825285 : Blo 1983435 2825285 := bbase (se 4 (by rfl) ⟨264870, by rfl⟩ : syracuseStep 2825285 = 529741) (by norm_num)
theorem B7534093 : Blo 1983435 7534093 := bstep (se 3 (by rfl) ⟨1412642, by rfl⟩ : syracuseStep 7534093 = 2825285) B2825285
theorem B10045457 : Blo 1983435 10045457 := bstep (se 2 (by rfl) ⟨3767046, by rfl⟩ : syracuseStep 10045457 = 7534093) B7534093
theorem B6696971 : Blo 1983435 6696971 := bstep (se 1 (by rfl) ⟨5022728, by rfl⟩ : syracuseStep 6696971 = 10045457) B10045457
theorem B4464647 : Blo 1983435 4464647 := bstep (se 1 (by rfl) ⟨3348485, by rfl⟩ : syracuseStep 4464647 = 6696971) B6696971
theorem B2976431 : Blo 1983435 2976431 := bstep (se 1 (by rfl) ⟨2232323, by rfl⟩ : syracuseStep 2976431 = 4464647) B4464647
theorem B1984287 : Blo 1983435 1984287 := bstep (se 1 (by rfl) ⟨1488215, by rfl⟩ : syracuseStep 1984287 = 2976431) B2976431
theorem B2976437 : Blo 1983435 2976437 := bbase (se 5 (by rfl) ⟨139520, by rfl⟩ : syracuseStep 2976437 = 279041) (by norm_num)
theorem B1984291 : Blo 1983435 1984291 := bstep (se 1 (by rfl) ⟨1488218, by rfl⟩ : syracuseStep 1984291 = 2976437) B2976437
theorem B5022749 : Blo 1983435 5022749 := bbase (se 3 (by rfl) ⟨941765, by rfl⟩ : syracuseStep 5022749 = 1883531) (by norm_num)
theorem B3348499 : Blo 1983435 3348499 := bstep (se 1 (by rfl) ⟨2511374, by rfl⟩ : syracuseStep 3348499 = 5022749) B5022749
theorem B4464665 : Blo 1983435 4464665 := bstep (se 2 (by rfl) ⟨1674249, by rfl⟩ : syracuseStep 4464665 = 3348499) B3348499
theorem B2976443 : Blo 1983435 2976443 := bstep (se 1 (by rfl) ⟨2232332, by rfl⟩ : syracuseStep 2976443 = 4464665) B4464665
theorem B1984295 : Blo 1983435 1984295 := bstep (se 1 (by rfl) ⟨1488221, by rfl⟩ : syracuseStep 1984295 = 2976443) B2976443
theorem B2232337 : Blo 1983435 2232337 := bbase (se 2 (by rfl) ⟨837126, by rfl⟩ : syracuseStep 2232337 = 1674253) (by norm_num)
theorem B2976449 : Blo 1983435 2976449 := bstep (se 2 (by rfl) ⟨1116168, by rfl⟩ : syracuseStep 2976449 = 2232337) B2232337
theorem B1984299 : Blo 1983435 1984299 := bstep (se 1 (by rfl) ⟨1488224, by rfl⟩ : syracuseStep 1984299 = 2976449) B2976449
theorem B3767077 : Blo 1983435 3767077 := bbase (se 4 (by rfl) ⟨353163, by rfl⟩ : syracuseStep 3767077 = 706327) (by norm_num)
theorem B5022769 : Blo 1983435 5022769 := bstep (se 2 (by rfl) ⟨1883538, by rfl⟩ : syracuseStep 5022769 = 3767077) B3767077
theorem B6697025 : Blo 1983435 6697025 := bstep (se 2 (by rfl) ⟨2511384, by rfl⟩ : syracuseStep 6697025 = 5022769) B5022769
theorem B4464683 : Blo 1983435 4464683 := bstep (se 1 (by rfl) ⟨3348512, by rfl⟩ : syracuseStep 4464683 = 6697025) B6697025
theorem B2976455 : Blo 1983435 2976455 := bstep (se 1 (by rfl) ⟨2232341, by rfl⟩ : syracuseStep 2976455 = 4464683) B4464683
theorem B1984303 : Blo 1983435 1984303 := bstep (se 1 (by rfl) ⟨1488227, by rfl⟩ : syracuseStep 1984303 = 2976455) B2976455
theorem B2976461 : Blo 1983435 2976461 := bbase (se 3 (by rfl) ⟨558086, by rfl⟩ : syracuseStep 2976461 = 1116173) (by norm_num)
theorem B1984307 : Blo 1983435 1984307 := bstep (se 1 (by rfl) ⟨1488230, by rfl⟩ : syracuseStep 1984307 = 2976461) B2976461
theorem B4464701 : Blo 1983435 4464701 := bbase (se 3 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 4464701 = 1674263) (by norm_num)
theorem B2976467 : Blo 1983435 2976467 := bstep (se 1 (by rfl) ⟨2232350, by rfl⟩ : syracuseStep 2976467 = 4464701) B4464701
theorem B1984311 : Blo 1983435 1984311 := bstep (se 1 (by rfl) ⟨1488233, by rfl⟩ : syracuseStep 1984311 = 2976467) B2976467
theorem B3348533 : Blo 1983435 3348533 := bbase (se 5 (by rfl) ⟨156962, by rfl⟩ : syracuseStep 3348533 = 313925) (by norm_num)
theorem B2232355 : Blo 1983435 2232355 := bstep (se 1 (by rfl) ⟨1674266, by rfl⟩ : syracuseStep 2232355 = 3348533) B3348533
theorem B2976473 : Blo 1983435 2976473 := bstep (se 2 (by rfl) ⟨1116177, by rfl⟩ : syracuseStep 2976473 = 2232355) B2232355
theorem B1984315 : Blo 1983435 1984315 := bstep (se 1 (by rfl) ⟨1488236, by rfl⟩ : syracuseStep 1984315 = 2976473) B2976473
theorem B5650661 : Blo 1983435 5650661 := bbase (se 4 (by rfl) ⟨529749, by rfl⟩ : syracuseStep 5650661 = 1059499) (by norm_num)
theorem B15068429 : Blo 1983435 15068429 := bstep (se 3 (by rfl) ⟨2825330, by rfl⟩ : syracuseStep 15068429 = 5650661) B5650661
theorem B10045619 : Blo 1983435 10045619 := bstep (se 1 (by rfl) ⟨7534214, by rfl⟩ : syracuseStep 10045619 = 15068429) B15068429
theorem B6697079 : Blo 1983435 6697079 := bstep (se 1 (by rfl) ⟨5022809, by rfl⟩ : syracuseStep 6697079 = 10045619) B10045619
theorem B4464719 : Blo 1983435 4464719 := bstep (se 1 (by rfl) ⟨3348539, by rfl⟩ : syracuseStep 4464719 = 6697079) B6697079
theorem B2976479 : Blo 1983435 2976479 := bstep (se 1 (by rfl) ⟨2232359, by rfl⟩ : syracuseStep 2976479 = 4464719) B4464719
theorem B1984319 : Blo 1983435 1984319 := bstep (se 1 (by rfl) ⟨1488239, by rfl⟩ : syracuseStep 1984319 = 2976479) B2976479
theorem B2976485 : Blo 1983435 2976485 := bbase (se 4 (by rfl) ⟨279045, by rfl⟩ : syracuseStep 2976485 = 558091) (by norm_num)
theorem B1984323 : Blo 1983435 1984323 := bstep (se 1 (by rfl) ⟨1488242, by rfl⟩ : syracuseStep 1984323 = 2976485) B2976485
theorem B10727477 : Blo 1983435 10727477 := bbase (se 5 (by rfl) ⟨502850, by rfl⟩ : syracuseStep 10727477 = 1005701) (by norm_num)
theorem B7151651 : Blo 1983435 7151651 := bstep (se 1 (by rfl) ⟨5363738, by rfl⟩ : syracuseStep 7151651 = 10727477) B10727477
theorem B4767767 : Blo 1983435 4767767 := bstep (se 1 (by rfl) ⟨3575825, by rfl⟩ : syracuseStep 4767767 = 7151651) B7151651
theorem B3178511 : Blo 1983435 3178511 := bstep (se 1 (by rfl) ⟨2383883, by rfl⟩ : syracuseStep 3178511 = 4767767) B4767767
theorem B2119007 : Blo 1983435 2119007 := bstep (se 1 (by rfl) ⟨1589255, by rfl⟩ : syracuseStep 2119007 = 3178511) B3178511
theorem B5650685 : Blo 1983435 5650685 := bstep (se 3 (by rfl) ⟨1059503, by rfl⟩ : syracuseStep 5650685 = 2119007) B2119007
theorem B3767123 : Blo 1983435 3767123 := bstep (se 1 (by rfl) ⟨2825342, by rfl⟩ : syracuseStep 3767123 = 5650685) B5650685
theorem B2511415 : Blo 1983435 2511415 := bstep (se 1 (by rfl) ⟨1883561, by rfl⟩ : syracuseStep 2511415 = 3767123) B3767123
theorem B3348553 : Blo 1983435 3348553 := bstep (se 2 (by rfl) ⟨1255707, by rfl⟩ : syracuseStep 3348553 = 2511415) B2511415
theorem B4464737 : Blo 1983435 4464737 := bstep (se 2 (by rfl) ⟨1674276, by rfl⟩ : syracuseStep 4464737 = 3348553) B3348553
theorem B2976491 : Blo 1983435 2976491 := bstep (se 1 (by rfl) ⟨2232368, by rfl⟩ : syracuseStep 2976491 = 4464737) B4464737
theorem B1984327 : Blo 1983435 1984327 := bstep (se 1 (by rfl) ⟨1488245, by rfl⟩ : syracuseStep 1984327 = 2976491) B2976491
theorem B2232373 : Blo 1983435 2232373 := bbase (se 5 (by rfl) ⟨104642, by rfl⟩ : syracuseStep 2232373 = 209285) (by norm_num)
theorem B2976497 : Blo 1983435 2976497 := bstep (se 2 (by rfl) ⟨1116186, by rfl⟩ : syracuseStep 2976497 = 2232373) B2232373
theorem B1984331 : Blo 1983435 1984331 := bstep (se 1 (by rfl) ⟨1488248, by rfl⟩ : syracuseStep 1984331 = 2976497) B2976497
theorem B2511425 : Blo 1983435 2511425 := bbase (se 2 (by rfl) ⟨941784, by rfl⟩ : syracuseStep 2511425 = 1883569) (by norm_num)
theorem B6697133 : Blo 1983435 6697133 := bstep (se 3 (by rfl) ⟨1255712, by rfl⟩ : syracuseStep 6697133 = 2511425) B2511425
theorem B4464755 : Blo 1983435 4464755 := bstep (se 1 (by rfl) ⟨3348566, by rfl⟩ : syracuseStep 4464755 = 6697133) B6697133
theorem B2976503 : Blo 1983435 2976503 := bstep (se 1 (by rfl) ⟨2232377, by rfl⟩ : syracuseStep 2976503 = 4464755) B4464755
theorem B1984335 : Blo 1983435 1984335 := bstep (se 1 (by rfl) ⟨1488251, by rfl⟩ : syracuseStep 1984335 = 2976503) B2976503
theorem B2976509 : Blo 1983435 2976509 := bbase (se 3 (by rfl) ⟨558095, by rfl⟩ : syracuseStep 2976509 = 1116191) (by norm_num)
theorem B1984339 : Blo 1983435 1984339 := bstep (se 1 (by rfl) ⟨1488254, by rfl⟩ : syracuseStep 1984339 = 2976509) B2976509
theorem B4464773 : Blo 1983435 4464773 := bbase (se 4 (by rfl) ⟨418572, by rfl⟩ : syracuseStep 4464773 = 837145) (by norm_num)
theorem B2976515 : Blo 1983435 2976515 := bstep (se 1 (by rfl) ⟨2232386, by rfl⟩ : syracuseStep 2976515 = 4464773) B4464773
theorem B1984343 : Blo 1983435 1984343 := bstep (se 1 (by rfl) ⟨1488257, by rfl⟩ : syracuseStep 1984343 = 2976515) B2976515
theorem B2416433 : Blo 1983435 2416433 := bbase (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) (by norm_num)
theorem B6443821 : Blo 1983435 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B8591761 : Blo 1983435 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B11455681 : Blo 1983435 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B15274241 : Blo 1983435 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B10182827 : Blo 1983435 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B6788551 : Blo 1983435 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B9051401 : Blo 1983435 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B6034267 : Blo 1983435 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B8045689 : Blo 1983435 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B10727585 : Blo 1983435 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B7151723 : Blo 1983435 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B4767815 : Blo 1983435 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B3178543 : Blo 1983435 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B4238057 : Blo 1983435 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B2825371 : Blo 1983435 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B3767161 : Blo 1983435 3767161 := bstep (se 2 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 3767161 = 2825371) B2825371
theorem B5022881 : Blo 1983435 5022881 := bstep (se 2 (by rfl) ⟨1883580, by rfl⟩ : syracuseStep 5022881 = 3767161) B3767161
theorem B3348587 : Blo 1983435 3348587 := bstep (se 1 (by rfl) ⟨2511440, by rfl⟩ : syracuseStep 3348587 = 5022881) B5022881
theorem B2232391 : Blo 1983435 2232391 := bstep (se 1 (by rfl) ⟨1674293, by rfl⟩ : syracuseStep 2232391 = 3348587) B3348587
theorem B2976521 : Blo 1983435 2976521 := bstep (se 2 (by rfl) ⟨1116195, by rfl⟩ : syracuseStep 2976521 = 2232391) B2232391
theorem B1984347 : Blo 1983435 1984347 := bstep (se 1 (by rfl) ⟨1488260, by rfl⟩ : syracuseStep 1984347 = 2976521) B2976521
theorem B10045781 : Blo 1983435 10045781 := bbase (se 10 (by rfl) ⟨14715, by rfl⟩ : syracuseStep 10045781 = 29431) (by norm_num)
theorem B6697187 : Blo 1983435 6697187 := bstep (se 1 (by rfl) ⟨5022890, by rfl⟩ : syracuseStep 6697187 = 10045781) B10045781
theorem B4464791 : Blo 1983435 4464791 := bstep (se 1 (by rfl) ⟨3348593, by rfl⟩ : syracuseStep 4464791 = 6697187) B6697187
theorem B2976527 : Blo 1983435 2976527 := bstep (se 1 (by rfl) ⟨2232395, by rfl⟩ : syracuseStep 2976527 = 4464791) B4464791
theorem B1984351 : Blo 1983435 1984351 := bstep (se 1 (by rfl) ⟨1488263, by rfl⟩ : syracuseStep 1984351 = 2976527) B2976527
theorem B2976533 : Blo 1983435 2976533 := bbase (se 6 (by rfl) ⟨69762, by rfl⟩ : syracuseStep 2976533 = 139525) (by norm_num)
theorem B1984355 : Blo 1983435 1984355 := bstep (se 1 (by rfl) ⟨1488266, by rfl⟩ : syracuseStep 1984355 = 2976533) B2976533
theorem B2147953 : Blo 1983435 2147953 := bbase (se 2 (by rfl) ⟨805482, by rfl⟩ : syracuseStep 2147953 = 1610965) (by norm_num)
theorem B2863937 : Blo 1983435 2863937 := bstep (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) B2147953
theorem B7637165 : Blo 1983435 7637165 := bstep (se 3 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 7637165 = 2863937) B2863937
theorem B5091443 : Blo 1983435 5091443 := bstep (se 1 (by rfl) ⟨3818582, by rfl⟩ : syracuseStep 5091443 = 7637165) B7637165
theorem B3394295 : Blo 1983435 3394295 := bstep (se 1 (by rfl) ⟨2545721, by rfl⟩ : syracuseStep 3394295 = 5091443) B5091443
theorem B2262863 : Blo 1983435 2262863 := bstep (se 1 (by rfl) ⟨1697147, by rfl⟩ : syracuseStep 2262863 = 3394295) B3394295
theorem B6034301 : Blo 1983435 6034301 := bstep (se 3 (by rfl) ⟨1131431, by rfl⟩ : syracuseStep 6034301 = 2262863) B2262863
theorem B4022867 : Blo 1983435 4022867 := bstep (se 1 (by rfl) ⟨3017150, by rfl⟩ : syracuseStep 4022867 = 6034301) B6034301
theorem B10727645 : Blo 1983435 10727645 := bstep (se 3 (by rfl) ⟨2011433, by rfl⟩ : syracuseStep 10727645 = 4022867) B4022867
theorem B28607053 : Blo 1983435 28607053 := bstep (se 3 (by rfl) ⟨5363822, by rfl⟩ : syracuseStep 28607053 = 10727645) B10727645
theorem B38142737 : Blo 1983435 38142737 := bstep (se 2 (by rfl) ⟨14303526, by rfl⟩ : syracuseStep 38142737 = 28607053) B28607053
theorem B25428491 : Blo 1983435 25428491 := bstep (se 1 (by rfl) ⟨19071368, by rfl⟩ : syracuseStep 25428491 = 38142737) B38142737
theorem B16952327 : Blo 1983435 16952327 := bstep (se 1 (by rfl) ⟨12714245, by rfl⟩ : syracuseStep 16952327 = 25428491) B25428491
theorem B11301551 : Blo 1983435 11301551 := bstep (se 1 (by rfl) ⟨8476163, by rfl⟩ : syracuseStep 11301551 = 16952327) B16952327
theorem B7534367 : Blo 1983435 7534367 := bstep (se 1 (by rfl) ⟨5650775, by rfl⟩ : syracuseStep 7534367 = 11301551) B11301551
theorem B5022911 : Blo 1983435 5022911 := bstep (se 1 (by rfl) ⟨3767183, by rfl⟩ : syracuseStep 5022911 = 7534367) B7534367
theorem B3348607 : Blo 1983435 3348607 := bstep (se 1 (by rfl) ⟨2511455, by rfl⟩ : syracuseStep 3348607 = 5022911) B5022911
theorem B4464809 : Blo 1983435 4464809 := bstep (se 2 (by rfl) ⟨1674303, by rfl⟩ : syracuseStep 4464809 = 3348607) B3348607
theorem B2976539 : Blo 1983435 2976539 := bstep (se 1 (by rfl) ⟨2232404, by rfl⟩ : syracuseStep 2976539 = 4464809) B4464809
theorem B1984359 : Blo 1983435 1984359 := bstep (se 1 (by rfl) ⟨1488269, by rfl⟩ : syracuseStep 1984359 = 2976539) B2976539
theorem B2232409 : Blo 1983435 2232409 := bbase (se 2 (by rfl) ⟨837153, by rfl⟩ : syracuseStep 2232409 = 1674307) (by norm_num)
theorem B2976545 : Blo 1983435 2976545 := bstep (se 2 (by rfl) ⟨1116204, by rfl⟩ : syracuseStep 2976545 = 2232409) B2232409
theorem B1984363 : Blo 1983435 1984363 := bstep (se 1 (by rfl) ⟨1488272, by rfl⟩ : syracuseStep 1984363 = 2976545) B2976545
theorem B4022885 : Blo 1983435 4022885 := bbase (se 4 (by rfl) ⟨377145, by rfl⟩ : syracuseStep 4022885 = 754291) (by norm_num)
theorem B2681923 : Blo 1983435 2681923 := bstep (se 1 (by rfl) ⟨2011442, by rfl⟩ : syracuseStep 2681923 = 4022885) B4022885
theorem B3575897 : Blo 1983435 3575897 := bstep (se 2 (by rfl) ⟨1340961, by rfl⟩ : syracuseStep 3575897 = 2681923) B2681923
theorem B2383931 : Blo 1983435 2383931 := bstep (se 1 (by rfl) ⟨1787948, by rfl⟩ : syracuseStep 2383931 = 3575897) B3575897
theorem B6357149 : Blo 1983435 6357149 := bstep (se 3 (by rfl) ⟨1191965, by rfl⟩ : syracuseStep 6357149 = 2383931) B2383931
theorem B4238099 : Blo 1983435 4238099 := bstep (se 1 (by rfl) ⟨3178574, by rfl⟩ : syracuseStep 4238099 = 6357149) B6357149
theorem B2825399 : Blo 1983435 2825399 := bstep (se 1 (by rfl) ⟨2119049, by rfl⟩ : syracuseStep 2825399 = 4238099) B4238099
theorem B7534397 : Blo 1983435 7534397 := bstep (se 3 (by rfl) ⟨1412699, by rfl⟩ : syracuseStep 7534397 = 2825399) B2825399
theorem B5022931 : Blo 1983435 5022931 := bstep (se 1 (by rfl) ⟨3767198, by rfl⟩ : syracuseStep 5022931 = 7534397) B7534397
theorem B6697241 : Blo 1983435 6697241 := bstep (se 2 (by rfl) ⟨2511465, by rfl⟩ : syracuseStep 6697241 = 5022931) B5022931
theorem B4464827 : Blo 1983435 4464827 := bstep (se 1 (by rfl) ⟨3348620, by rfl⟩ : syracuseStep 4464827 = 6697241) B6697241
theorem B2976551 : Blo 1983435 2976551 := bstep (se 1 (by rfl) ⟨2232413, by rfl⟩ : syracuseStep 2976551 = 4464827) B4464827
theorem B1984367 : Blo 1983435 1984367 := bstep (se 1 (by rfl) ⟨1488275, by rfl⟩ : syracuseStep 1984367 = 2976551) B2976551
theorem B2976557 : Blo 1983435 2976557 := bbase (se 3 (by rfl) ⟨558104, by rfl⟩ : syracuseStep 2976557 = 1116209) (by norm_num)
theorem B1984371 : Blo 1983435 1984371 := bstep (se 1 (by rfl) ⟨1488278, by rfl⟩ : syracuseStep 1984371 = 2976557) B2976557
theorem B4464845 : Blo 1983435 4464845 := bbase (se 3 (by rfl) ⟨837158, by rfl⟩ : syracuseStep 4464845 = 1674317) (by norm_num)
theorem B2976563 : Blo 1983435 2976563 := bstep (se 1 (by rfl) ⟨2232422, by rfl⟩ : syracuseStep 2976563 = 4464845) B4464845
theorem B1984375 : Blo 1983435 1984375 := bstep (se 1 (by rfl) ⟨1488281, by rfl⟩ : syracuseStep 1984375 = 2976563) B2976563
theorem B2511481 : Blo 1983435 2511481 := bbase (se 2 (by rfl) ⟨941805, by rfl⟩ : syracuseStep 2511481 = 1883611) (by norm_num)
theorem B3348641 : Blo 1983435 3348641 := bstep (se 2 (by rfl) ⟨1255740, by rfl⟩ : syracuseStep 3348641 = 2511481) B2511481
theorem B2232427 : Blo 1983435 2232427 := bstep (se 1 (by rfl) ⟨1674320, by rfl⟩ : syracuseStep 2232427 = 3348641) B3348641
theorem B2976569 : Blo 1983435 2976569 := bstep (se 2 (by rfl) ⟨1116213, by rfl⟩ : syracuseStep 2976569 = 2232427) B2232427
theorem B1984379 : Blo 1983435 1984379 := bstep (se 1 (by rfl) ⟨1488284, by rfl⟩ : syracuseStep 1984379 = 2976569) B2976569
theorem B2177285 : Blo 1983435 2177285 := bbase (se 4 (by rfl) ⟨204120, by rfl⟩ : syracuseStep 2177285 = 408241) (by norm_num)
theorem B5806093 : Blo 1983435 5806093 := bstep (se 3 (by rfl) ⟨1088642, by rfl⟩ : syracuseStep 5806093 = 2177285) B2177285
theorem B7741457 : Blo 1983435 7741457 := bstep (se 2 (by rfl) ⟨2903046, by rfl⟩ : syracuseStep 7741457 = 5806093) B5806093
theorem B5160971 : Blo 1983435 5160971 := bstep (se 1 (by rfl) ⟨3870728, by rfl⟩ : syracuseStep 5160971 = 7741457) B7741457
theorem B3440647 : Blo 1983435 3440647 := bstep (se 1 (by rfl) ⟨2580485, by rfl⟩ : syracuseStep 3440647 = 5160971) B5160971
theorem B4587529 : Blo 1983435 4587529 := bstep (se 2 (by rfl) ⟨1720323, by rfl⟩ : syracuseStep 4587529 = 3440647) B3440647
theorem B6116705 : Blo 1983435 6116705 := bstep (se 2 (by rfl) ⟨2293764, by rfl⟩ : syracuseStep 6116705 = 4587529) B4587529
theorem B4077803 : Blo 1983435 4077803 := bstep (se 1 (by rfl) ⟨3058352, by rfl⟩ : syracuseStep 4077803 = 6116705) B6116705
theorem B10874141 : Blo 1983435 10874141 := bstep (se 3 (by rfl) ⟨2038901, by rfl⟩ : syracuseStep 10874141 = 4077803) B4077803
theorem B7249427 : Blo 1983435 7249427 := bstep (se 1 (by rfl) ⟨5437070, by rfl⟩ : syracuseStep 7249427 = 10874141) B10874141
theorem B4832951 : Blo 1983435 4832951 := bstep (se 1 (by rfl) ⟨3624713, by rfl⟩ : syracuseStep 4832951 = 7249427) B7249427
theorem B12887869 : Blo 1983435 12887869 := bstep (se 3 (by rfl) ⟨2416475, by rfl⟩ : syracuseStep 12887869 = 4832951) B4832951
theorem B17183825 : Blo 1983435 17183825 := bstep (se 2 (by rfl) ⟨6443934, by rfl⟩ : syracuseStep 17183825 = 12887869) B12887869
theorem B11455883 : Blo 1983435 11455883 := bstep (se 1 (by rfl) ⟨8591912, by rfl⟩ : syracuseStep 11455883 = 17183825) B17183825
theorem B7637255 : Blo 1983435 7637255 := bstep (se 1 (by rfl) ⟨5727941, by rfl⟩ : syracuseStep 7637255 = 11455883) B11455883
theorem B5091503 : Blo 1983435 5091503 := bstep (se 1 (by rfl) ⟨3818627, by rfl⟩ : syracuseStep 5091503 = 7637255) B7637255
theorem B13577341 : Blo 1983435 13577341 := bstep (se 3 (by rfl) ⟨2545751, by rfl⟩ : syracuseStep 13577341 = 5091503) B5091503
theorem B18103121 : Blo 1983435 18103121 := bstep (se 2 (by rfl) ⟨6788670, by rfl⟩ : syracuseStep 18103121 = 13577341) B13577341
theorem B12068747 : Blo 1983435 12068747 := bstep (se 1 (by rfl) ⟨9051560, by rfl⟩ : syracuseStep 12068747 = 18103121) B18103121
theorem B8045831 : Blo 1983435 8045831 := bstep (se 1 (by rfl) ⟨6034373, by rfl⟩ : syracuseStep 8045831 = 12068747) B12068747
theorem B21455549 : Blo 1983435 21455549 := bstep (se 3 (by rfl) ⟨4022915, by rfl⟩ : syracuseStep 21455549 = 8045831) B8045831
theorem B14303699 : Blo 1983435 14303699 := bstep (se 1 (by rfl) ⟨10727774, by rfl⟩ : syracuseStep 14303699 = 21455549) B21455549
theorem B9535799 : Blo 1983435 9535799 := bstep (se 1 (by rfl) ⟨7151849, by rfl⟩ : syracuseStep 9535799 = 14303699) B14303699
theorem B6357199 : Blo 1983435 6357199 := bstep (se 1 (by rfl) ⟨4767899, by rfl⟩ : syracuseStep 6357199 = 9535799) B9535799
theorem B8476265 : Blo 1983435 8476265 := bstep (se 2 (by rfl) ⟨3178599, by rfl⟩ : syracuseStep 8476265 = 6357199) B6357199
theorem B22603373 : Blo 1983435 22603373 := bstep (se 3 (by rfl) ⟨4238132, by rfl⟩ : syracuseStep 22603373 = 8476265) B8476265
theorem B15068915 : Blo 1983435 15068915 := bstep (se 1 (by rfl) ⟨11301686, by rfl⟩ : syracuseStep 15068915 = 22603373) B22603373
theorem B10045943 : Blo 1983435 10045943 := bstep (se 1 (by rfl) ⟨7534457, by rfl⟩ : syracuseStep 10045943 = 15068915) B15068915
theorem B6697295 : Blo 1983435 6697295 := bstep (se 1 (by rfl) ⟨5022971, by rfl⟩ : syracuseStep 6697295 = 10045943) B10045943
theorem B4464863 : Blo 1983435 4464863 := bstep (se 1 (by rfl) ⟨3348647, by rfl⟩ : syracuseStep 4464863 = 6697295) B6697295
theorem B2976575 : Blo 1983435 2976575 := bstep (se 1 (by rfl) ⟨2232431, by rfl⟩ : syracuseStep 2976575 = 4464863) B4464863
theorem B1984383 : Blo 1983435 1984383 := bstep (se 1 (by rfl) ⟨1488287, by rfl⟩ : syracuseStep 1984383 = 2976575) B2976575
theorem B2976581 : Blo 1983435 2976581 := bbase (se 4 (by rfl) ⟨279054, by rfl⟩ : syracuseStep 2976581 = 558109) (by norm_num)
theorem B1984387 : Blo 1983435 1984387 := bstep (se 1 (by rfl) ⟨1488290, by rfl⟩ : syracuseStep 1984387 = 2976581) B2976581
theorem B3348661 : Blo 1983435 3348661 := bbase (se 5 (by rfl) ⟨156968, by rfl⟩ : syracuseStep 3348661 = 313937) (by norm_num)
theorem B4464881 : Blo 1983435 4464881 := bstep (se 2 (by rfl) ⟨1674330, by rfl⟩ : syracuseStep 4464881 = 3348661) B3348661
theorem B2976587 : Blo 1983435 2976587 := bstep (se 1 (by rfl) ⟨2232440, by rfl⟩ : syracuseStep 2976587 = 4464881) B4464881
theorem B1984391 : Blo 1983435 1984391 := bstep (se 1 (by rfl) ⟨1488293, by rfl⟩ : syracuseStep 1984391 = 2976587) B2976587
theorem B2232445 : Blo 1983435 2232445 := bbase (se 3 (by rfl) ⟨418583, by rfl⟩ : syracuseStep 2232445 = 837167) (by norm_num)
theorem B2976593 : Blo 1983435 2976593 := bstep (se 2 (by rfl) ⟨1116222, by rfl⟩ : syracuseStep 2976593 = 2232445) B2232445
theorem B1984395 : Blo 1983435 1984395 := bstep (se 1 (by rfl) ⟨1488296, by rfl⟩ : syracuseStep 1984395 = 2976593) B2976593
theorem B6697349 : Blo 1983435 6697349 := bbase (se 4 (by rfl) ⟨627876, by rfl⟩ : syracuseStep 6697349 = 1255753) (by norm_num)
theorem B4464899 : Blo 1983435 4464899 := bstep (se 1 (by rfl) ⟨3348674, by rfl⟩ : syracuseStep 4464899 = 6697349) B6697349
theorem B2976599 : Blo 1983435 2976599 := bstep (se 1 (by rfl) ⟨2232449, by rfl⟩ : syracuseStep 2976599 = 4464899) B4464899
theorem B1984399 : Blo 1983435 1984399 := bstep (se 1 (by rfl) ⟨1488299, by rfl⟩ : syracuseStep 1984399 = 2976599) B2976599
theorem B2976605 : Blo 1983435 2976605 := bbase (se 3 (by rfl) ⟨558113, by rfl⟩ : syracuseStep 2976605 = 1116227) (by norm_num)
theorem B1984403 : Blo 1983435 1984403 := bstep (se 1 (by rfl) ⟨1488302, by rfl⟩ : syracuseStep 1984403 = 2976605) B2976605
theorem B4464917 : Blo 1983435 4464917 := bbase (se 6 (by rfl) ⟨104646, by rfl⟩ : syracuseStep 4464917 = 209293) (by norm_num)
theorem B2976611 : Blo 1983435 2976611 := bstep (se 1 (by rfl) ⟨2232458, by rfl⟩ : syracuseStep 2976611 = 4464917) B4464917
theorem B1984407 : Blo 1983435 1984407 := bstep (se 1 (by rfl) ⟨1488305, by rfl⟩ : syracuseStep 1984407 = 2976611) B2976611
theorem B7534565 : Blo 1983435 7534565 := bbase (se 4 (by rfl) ⟨706365, by rfl⟩ : syracuseStep 7534565 = 1412731) (by norm_num)
theorem B5023043 : Blo 1983435 5023043 := bstep (se 1 (by rfl) ⟨3767282, by rfl⟩ : syracuseStep 5023043 = 7534565) B7534565
theorem B3348695 : Blo 1983435 3348695 := bstep (se 1 (by rfl) ⟨2511521, by rfl⟩ : syracuseStep 3348695 = 5023043) B5023043
theorem B2232463 : Blo 1983435 2232463 := bstep (se 1 (by rfl) ⟨1674347, by rfl⟩ : syracuseStep 2232463 = 3348695) B3348695
theorem B2976617 : Blo 1983435 2976617 := bstep (se 2 (by rfl) ⟨1116231, by rfl⟩ : syracuseStep 2976617 = 2232463) B2232463
theorem B1984411 : Blo 1983435 1984411 := bstep (se 1 (by rfl) ⟨1488308, by rfl⟩ : syracuseStep 1984411 = 2976617) B2976617
theorem B7637381 : Blo 1983435 7637381 := bbase (se 4 (by rfl) ⟨716004, by rfl⟩ : syracuseStep 7637381 = 1432009) (by norm_num)
theorem B5091587 : Blo 1983435 5091587 := bstep (se 1 (by rfl) ⟨3818690, by rfl⟩ : syracuseStep 5091587 = 7637381) B7637381
theorem B3394391 : Blo 1983435 3394391 := bstep (se 1 (by rfl) ⟨2545793, by rfl⟩ : syracuseStep 3394391 = 5091587) B5091587
theorem B9051709 : Blo 1983435 9051709 := bstep (se 3 (by rfl) ⟨1697195, by rfl⟩ : syracuseStep 9051709 = 3394391) B3394391
theorem B12068945 : Blo 1983435 12068945 := bstep (se 2 (by rfl) ⟨4525854, by rfl⟩ : syracuseStep 12068945 = 9051709) B9051709
theorem B8045963 : Blo 1983435 8045963 := bstep (se 1 (by rfl) ⟨6034472, by rfl⟩ : syracuseStep 8045963 = 12068945) B12068945
theorem B5363975 : Blo 1983435 5363975 := bstep (se 1 (by rfl) ⟨4022981, by rfl⟩ : syracuseStep 5363975 = 8045963) B8045963
theorem B3575983 : Blo 1983435 3575983 := bstep (se 1 (by rfl) ⟨2681987, by rfl⟩ : syracuseStep 3575983 = 5363975) B5363975
theorem B4767977 : Blo 1983435 4767977 := bstep (se 2 (by rfl) ⟨1787991, by rfl⟩ : syracuseStep 4767977 = 3575983) B3575983
theorem B3178651 : Blo 1983435 3178651 := bstep (se 1 (by rfl) ⟨2383988, by rfl⟩ : syracuseStep 3178651 = 4767977) B4767977
theorem B4238201 : Blo 1983435 4238201 := bstep (se 2 (by rfl) ⟨1589325, by rfl⟩ : syracuseStep 4238201 = 3178651) B3178651
theorem B11301869 : Blo 1983435 11301869 := bstep (se 3 (by rfl) ⟨2119100, by rfl⟩ : syracuseStep 11301869 = 4238201) B4238201
theorem B7534579 : Blo 1983435 7534579 := bstep (se 1 (by rfl) ⟨5650934, by rfl⟩ : syracuseStep 7534579 = 11301869) B11301869
theorem B10046105 : Blo 1983435 10046105 := bstep (se 2 (by rfl) ⟨3767289, by rfl⟩ : syracuseStep 10046105 = 7534579) B7534579
theorem B6697403 : Blo 1983435 6697403 := bstep (se 1 (by rfl) ⟨5023052, by rfl⟩ : syracuseStep 6697403 = 10046105) B10046105
theorem B4464935 : Blo 1983435 4464935 := bstep (se 1 (by rfl) ⟨3348701, by rfl⟩ : syracuseStep 4464935 = 6697403) B6697403
theorem B2976623 : Blo 1983435 2976623 := bstep (se 1 (by rfl) ⟨2232467, by rfl⟩ : syracuseStep 2976623 = 4464935) B4464935
theorem B1984415 : Blo 1983435 1984415 := bstep (se 1 (by rfl) ⟨1488311, by rfl⟩ : syracuseStep 1984415 = 2976623) B2976623
theorem B2976629 : Blo 1983435 2976629 := bbase (se 5 (by rfl) ⟨139529, by rfl⟩ : syracuseStep 2976629 = 279059) (by norm_num)
theorem B1984419 : Blo 1983435 1984419 := bstep (se 1 (by rfl) ⟨1488314, by rfl⟩ : syracuseStep 1984419 = 2976629) B2976629
theorem B4767997 : Blo 1983435 4767997 := bbase (se 3 (by rfl) ⟨893999, by rfl⟩ : syracuseStep 4767997 = 1787999) (by norm_num)
theorem B6357329 : Blo 1983435 6357329 := bstep (se 2 (by rfl) ⟨2383998, by rfl⟩ : syracuseStep 6357329 = 4767997) B4767997
theorem B4238219 : Blo 1983435 4238219 := bstep (se 1 (by rfl) ⟨3178664, by rfl⟩ : syracuseStep 4238219 = 6357329) B6357329
theorem B2825479 : Blo 1983435 2825479 := bstep (se 1 (by rfl) ⟨2119109, by rfl⟩ : syracuseStep 2825479 = 4238219) B4238219
theorem B3767305 : Blo 1983435 3767305 := bstep (se 2 (by rfl) ⟨1412739, by rfl⟩ : syracuseStep 3767305 = 2825479) B2825479
theorem B5023073 : Blo 1983435 5023073 := bstep (se 2 (by rfl) ⟨1883652, by rfl⟩ : syracuseStep 5023073 = 3767305) B3767305
theorem B3348715 : Blo 1983435 3348715 := bstep (se 1 (by rfl) ⟨2511536, by rfl⟩ : syracuseStep 3348715 = 5023073) B5023073
theorem B4464953 : Blo 1983435 4464953 := bstep (se 2 (by rfl) ⟨1674357, by rfl⟩ : syracuseStep 4464953 = 3348715) B3348715
theorem B2976635 : Blo 1983435 2976635 := bstep (se 1 (by rfl) ⟨2232476, by rfl⟩ : syracuseStep 2976635 = 4464953) B4464953
theorem B1984423 : Blo 1983435 1984423 := bstep (se 1 (by rfl) ⟨1488317, by rfl⟩ : syracuseStep 1984423 = 2976635) B2976635
theorem B2232481 : Blo 1983435 2232481 := bbase (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) (by norm_num)
theorem B2976641 : Blo 1983435 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B1984427 : Blo 1983435 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B5023093 : Blo 1983435 5023093 := bbase (se 5 (by rfl) ⟨235457, by rfl⟩ : syracuseStep 5023093 = 470915) (by norm_num)
theorem B6697457 : Blo 1983435 6697457 := bstep (se 2 (by rfl) ⟨2511546, by rfl⟩ : syracuseStep 6697457 = 5023093) B5023093
theorem B4464971 : Blo 1983435 4464971 := bstep (se 1 (by rfl) ⟨3348728, by rfl⟩ : syracuseStep 4464971 = 6697457) B6697457
theorem B2976647 : Blo 1983435 2976647 := bstep (se 1 (by rfl) ⟨2232485, by rfl⟩ : syracuseStep 2976647 = 4464971) B4464971
theorem B1984431 : Blo 1983435 1984431 := bstep (se 1 (by rfl) ⟨1488323, by rfl⟩ : syracuseStep 1984431 = 2976647) B2976647
theorem B2976653 : Blo 1983435 2976653 := bbase (se 3 (by rfl) ⟨558122, by rfl⟩ : syracuseStep 2976653 = 1116245) (by norm_num)
theorem B1984435 : Blo 1983435 1984435 := bstep (se 1 (by rfl) ⟨1488326, by rfl⟩ : syracuseStep 1984435 = 2976653) B2976653
theorem B4464989 : Blo 1983435 4464989 := bbase (se 3 (by rfl) ⟨837185, by rfl⟩ : syracuseStep 4464989 = 1674371) (by norm_num)
theorem B2976659 : Blo 1983435 2976659 := bstep (se 1 (by rfl) ⟨2232494, by rfl⟩ : syracuseStep 2976659 = 4464989) B4464989
theorem B1984439 : Blo 1983435 1984439 := bstep (se 1 (by rfl) ⟨1488329, by rfl⟩ : syracuseStep 1984439 = 2976659) B2976659
theorem B3348749 : Blo 1983435 3348749 := bbase (se 3 (by rfl) ⟨627890, by rfl⟩ : syracuseStep 3348749 = 1255781) (by norm_num)
theorem B2232499 : Blo 1983435 2232499 := bstep (se 1 (by rfl) ⟨1674374, by rfl⟩ : syracuseStep 2232499 = 3348749) B3348749
theorem B2976665 : Blo 1983435 2976665 := bstep (se 2 (by rfl) ⟨1116249, by rfl⟩ : syracuseStep 2976665 = 2232499) B2232499
theorem B1984443 : Blo 1983435 1984443 := bstep (se 1 (by rfl) ⟨1488332, by rfl⟩ : syracuseStep 1984443 = 2976665) B2976665
theorem B16953077 : Blo 1983435 16953077 := bbase (se 5 (by rfl) ⟨794675, by rfl⟩ : syracuseStep 16953077 = 1589351) (by norm_num)
theorem B11302051 : Blo 1983435 11302051 := bstep (se 1 (by rfl) ⟨8476538, by rfl⟩ : syracuseStep 11302051 = 16953077) B16953077
theorem B15069401 : Blo 1983435 15069401 := bstep (se 2 (by rfl) ⟨5651025, by rfl⟩ : syracuseStep 15069401 = 11302051) B11302051
theorem B10046267 : Blo 1983435 10046267 := bstep (se 1 (by rfl) ⟨7534700, by rfl⟩ : syracuseStep 10046267 = 15069401) B15069401
theorem B6697511 : Blo 1983435 6697511 := bstep (se 1 (by rfl) ⟨5023133, by rfl⟩ : syracuseStep 6697511 = 10046267) B10046267
theorem B4465007 : Blo 1983435 4465007 := bstep (se 1 (by rfl) ⟨3348755, by rfl⟩ : syracuseStep 4465007 = 6697511) B6697511
theorem B2976671 : Blo 1983435 2976671 := bstep (se 1 (by rfl) ⟨2232503, by rfl⟩ : syracuseStep 2976671 = 4465007) B4465007
theorem B1984447 : Blo 1983435 1984447 := bstep (se 1 (by rfl) ⟨1488335, by rfl⟩ : syracuseStep 1984447 = 2976671) B2976671
theorem B2976677 : Blo 1983435 2976677 := bbase (se 4 (by rfl) ⟨279063, by rfl⟩ : syracuseStep 2976677 = 558127) (by norm_num)
theorem B1984451 : Blo 1983435 1984451 := bstep (se 1 (by rfl) ⟨1488338, by rfl⟩ : syracuseStep 1984451 = 2976677) B2976677
theorem B2511577 : Blo 1983435 2511577 := bbase (se 2 (by rfl) ⟨941841, by rfl⟩ : syracuseStep 2511577 = 1883683) (by norm_num)
theorem B3348769 : Blo 1983435 3348769 := bstep (se 2 (by rfl) ⟨1255788, by rfl⟩ : syracuseStep 3348769 = 2511577) B2511577
theorem B4465025 : Blo 1983435 4465025 := bstep (se 2 (by rfl) ⟨1674384, by rfl⟩ : syracuseStep 4465025 = 3348769) B3348769
theorem B2976683 : Blo 1983435 2976683 := bstep (se 1 (by rfl) ⟨2232512, by rfl⟩ : syracuseStep 2976683 = 4465025) B4465025
theorem B1984455 : Blo 1983435 1984455 := bstep (se 1 (by rfl) ⟨1488341, by rfl⟩ : syracuseStep 1984455 = 2976683) B2976683
theorem B2232517 : Blo 1983435 2232517 := bbase (se 4 (by rfl) ⟨209298, by rfl⟩ : syracuseStep 2232517 = 418597) (by norm_num)
theorem B2976689 : Blo 1983435 2976689 := bstep (se 2 (by rfl) ⟨1116258, by rfl⟩ : syracuseStep 2976689 = 2232517) B2232517
theorem B1984459 : Blo 1983435 1984459 := bstep (se 1 (by rfl) ⟨1488344, by rfl⟩ : syracuseStep 1984459 = 2976689) B2976689
theorem B3767381 : Blo 1983435 3767381 := bbase (se 8 (by rfl) ⟨22074, by rfl⟩ : syracuseStep 3767381 = 44149) (by norm_num)
theorem B2511587 : Blo 1983435 2511587 := bstep (se 1 (by rfl) ⟨1883690, by rfl⟩ : syracuseStep 2511587 = 3767381) B3767381
theorem B6697565 : Blo 1983435 6697565 := bstep (se 3 (by rfl) ⟨1255793, by rfl⟩ : syracuseStep 6697565 = 2511587) B2511587
theorem B4465043 : Blo 1983435 4465043 := bstep (se 1 (by rfl) ⟨3348782, by rfl⟩ : syracuseStep 4465043 = 6697565) B6697565
theorem B2976695 : Blo 1983435 2976695 := bstep (se 1 (by rfl) ⟨2232521, by rfl⟩ : syracuseStep 2976695 = 4465043) B4465043
theorem B1984463 : Blo 1983435 1984463 := bstep (se 1 (by rfl) ⟨1488347, by rfl⟩ : syracuseStep 1984463 = 2976695) B2976695
theorem B2976701 : Blo 1983435 2976701 := bbase (se 3 (by rfl) ⟨558131, by rfl⟩ : syracuseStep 2976701 = 1116263) (by norm_num)
theorem B1984467 : Blo 1983435 1984467 := bstep (se 1 (by rfl) ⟨1488350, by rfl⟩ : syracuseStep 1984467 = 2976701) B2976701
theorem B4465061 : Blo 1983435 4465061 := bbase (se 4 (by rfl) ⟨418599, by rfl⟩ : syracuseStep 4465061 = 837199) (by norm_num)
theorem B2976707 : Blo 1983435 2976707 := bstep (se 1 (by rfl) ⟨2232530, by rfl⟩ : syracuseStep 2976707 = 4465061) B4465061
theorem B1984471 : Blo 1983435 1984471 := bstep (se 1 (by rfl) ⟨1488353, by rfl⟩ : syracuseStep 1984471 = 2976707) B2976707
theorem B5023205 : Blo 1983435 5023205 := bbase (se 4 (by rfl) ⟨470925, by rfl⟩ : syracuseStep 5023205 = 941851) (by norm_num)
theorem B3348803 : Blo 1983435 3348803 := bstep (se 1 (by rfl) ⟨2511602, by rfl⟩ : syracuseStep 3348803 = 5023205) B5023205
theorem B2232535 : Blo 1983435 2232535 := bstep (se 1 (by rfl) ⟨1674401, by rfl⟩ : syracuseStep 2232535 = 3348803) B3348803
theorem B2976713 : Blo 1983435 2976713 := bstep (se 2 (by rfl) ⟨1116267, by rfl⟩ : syracuseStep 2976713 = 2232535) B2232535
theorem B1984475 : Blo 1983435 1984475 := bstep (se 1 (by rfl) ⟨1488356, by rfl⟩ : syracuseStep 1984475 = 2976713) B2976713
theorem B2119169 : Blo 1983435 2119169 := bbase (se 2 (by rfl) ⟨794688, by rfl⟩ : syracuseStep 2119169 = 1589377) (by norm_num)
theorem B5651117 : Blo 1983435 5651117 := bstep (se 3 (by rfl) ⟨1059584, by rfl⟩ : syracuseStep 5651117 = 2119169) B2119169
theorem B3767411 : Blo 1983435 3767411 := bstep (se 1 (by rfl) ⟨2825558, by rfl⟩ : syracuseStep 3767411 = 5651117) B5651117
theorem B10046429 : Blo 1983435 10046429 := bstep (se 3 (by rfl) ⟨1883705, by rfl⟩ : syracuseStep 10046429 = 3767411) B3767411
theorem B6697619 : Blo 1983435 6697619 := bstep (se 1 (by rfl) ⟨5023214, by rfl⟩ : syracuseStep 6697619 = 10046429) B10046429
theorem B4465079 : Blo 1983435 4465079 := bstep (se 1 (by rfl) ⟨3348809, by rfl⟩ : syracuseStep 4465079 = 6697619) B6697619
theorem B2976719 : Blo 1983435 2976719 := bstep (se 1 (by rfl) ⟨2232539, by rfl⟩ : syracuseStep 2976719 = 4465079) B4465079
theorem B1984479 : Blo 1983435 1984479 := bstep (se 1 (by rfl) ⟨1488359, by rfl⟩ : syracuseStep 1984479 = 2976719) B2976719
theorem B2976725 : Blo 1983435 2976725 := bbase (se 7 (by rfl) ⟨34883, by rfl⟩ : syracuseStep 2976725 = 69767) (by norm_num)
theorem B1984483 : Blo 1983435 1984483 := bstep (se 1 (by rfl) ⟨1488362, by rfl⟩ : syracuseStep 1984483 = 2976725) B2976725
theorem B7534853 : Blo 1983435 7534853 := bbase (se 4 (by rfl) ⟨706392, by rfl⟩ : syracuseStep 7534853 = 1412785) (by norm_num)
theorem B5023235 : Blo 1983435 5023235 := bstep (se 1 (by rfl) ⟨3767426, by rfl⟩ : syracuseStep 5023235 = 7534853) B7534853
theorem B3348823 : Blo 1983435 3348823 := bstep (se 1 (by rfl) ⟨2511617, by rfl⟩ : syracuseStep 3348823 = 5023235) B5023235
theorem B4465097 : Blo 1983435 4465097 := bstep (se 2 (by rfl) ⟨1674411, by rfl⟩ : syracuseStep 4465097 = 3348823) B3348823
theorem B2976731 : Blo 1983435 2976731 := bstep (se 1 (by rfl) ⟨2232548, by rfl⟩ : syracuseStep 2976731 = 4465097) B4465097
theorem B1984487 : Blo 1983435 1984487 := bstep (se 1 (by rfl) ⟨1488365, by rfl⟩ : syracuseStep 1984487 = 2976731) B2976731
theorem B2232553 : Blo 1983435 2232553 := bbase (se 2 (by rfl) ⟨837207, by rfl⟩ : syracuseStep 2232553 = 1674415) (by norm_num)
theorem B2976737 : Blo 1983435 2976737 := bstep (se 2 (by rfl) ⟨1116276, by rfl⟩ : syracuseStep 2976737 = 2232553) B2232553
theorem B1984491 : Blo 1983435 1984491 := bstep (se 1 (by rfl) ⟨1488368, by rfl⟩ : syracuseStep 1984491 = 2976737) B2976737
theorem B11302325 : Blo 1983435 11302325 := bbase (se 5 (by rfl) ⟨529796, by rfl⟩ : syracuseStep 11302325 = 1059593) (by norm_num)
theorem B7534883 : Blo 1983435 7534883 := bstep (se 1 (by rfl) ⟨5651162, by rfl⟩ : syracuseStep 7534883 = 11302325) B11302325
theorem B5023255 : Blo 1983435 5023255 := bstep (se 1 (by rfl) ⟨3767441, by rfl⟩ : syracuseStep 5023255 = 7534883) B7534883
theorem B6697673 : Blo 1983435 6697673 := bstep (se 2 (by rfl) ⟨2511627, by rfl⟩ : syracuseStep 6697673 = 5023255) B5023255
theorem B4465115 : Blo 1983435 4465115 := bstep (se 1 (by rfl) ⟨3348836, by rfl⟩ : syracuseStep 4465115 = 6697673) B6697673
theorem B2976743 : Blo 1983435 2976743 := bstep (se 1 (by rfl) ⟨2232557, by rfl⟩ : syracuseStep 2976743 = 4465115) B4465115
theorem B1984495 : Blo 1983435 1984495 := bstep (se 1 (by rfl) ⟨1488371, by rfl⟩ : syracuseStep 1984495 = 2976743) B2976743
theorem B2976749 : Blo 1983435 2976749 := bbase (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) (by norm_num)
theorem B1984499 : Blo 1983435 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B4465133 : Blo 1983435 4465133 := bbase (se 3 (by rfl) ⟨837212, by rfl⟩ : syracuseStep 4465133 = 1674425) (by norm_num)
theorem B2976755 : Blo 1983435 2976755 := bstep (se 1 (by rfl) ⟨2232566, by rfl⟩ : syracuseStep 2976755 = 4465133) B4465133
theorem B1984503 : Blo 1983435 1984503 := bstep (se 1 (by rfl) ⟨1488377, by rfl⟩ : syracuseStep 1984503 = 2976755) B2976755
theorem B3394549 : Blo 1983435 3394549 := bbase (se 5 (by rfl) ⟨159119, by rfl⟩ : syracuseStep 3394549 = 318239) (by norm_num)
theorem B4526065 : Blo 1983435 4526065 := bstep (se 2 (by rfl) ⟨1697274, by rfl⟩ : syracuseStep 4526065 = 3394549) B3394549
theorem B6034753 : Blo 1983435 6034753 := bstep (se 2 (by rfl) ⟨2263032, by rfl⟩ : syracuseStep 6034753 = 4526065) B4526065
theorem B32185349 : Blo 1983435 32185349 := bstep (se 4 (by rfl) ⟨3017376, by rfl⟩ : syracuseStep 32185349 = 6034753) B6034753
theorem B21456899 : Blo 1983435 21456899 := bstep (se 1 (by rfl) ⟨16092674, by rfl⟩ : syracuseStep 21456899 = 32185349) B32185349
theorem B14304599 : Blo 1983435 14304599 := bstep (se 1 (by rfl) ⟨10728449, by rfl⟩ : syracuseStep 14304599 = 21456899) B21456899
theorem B9536399 : Blo 1983435 9536399 := bstep (se 1 (by rfl) ⟨7152299, by rfl⟩ : syracuseStep 9536399 = 14304599) B14304599
theorem B6357599 : Blo 1983435 6357599 := bstep (se 1 (by rfl) ⟨4768199, by rfl⟩ : syracuseStep 6357599 = 9536399) B9536399
theorem B4238399 : Blo 1983435 4238399 := bstep (se 1 (by rfl) ⟨3178799, by rfl⟩ : syracuseStep 4238399 = 6357599) B6357599
theorem B2825599 : Blo 1983435 2825599 := bstep (se 1 (by rfl) ⟨2119199, by rfl⟩ : syracuseStep 2825599 = 4238399) B4238399
theorem B3767465 : Blo 1983435 3767465 := bstep (se 2 (by rfl) ⟨1412799, by rfl⟩ : syracuseStep 3767465 = 2825599) B2825599
theorem B2511643 : Blo 1983435 2511643 := bstep (se 1 (by rfl) ⟨1883732, by rfl⟩ : syracuseStep 2511643 = 3767465) B3767465
theorem B3348857 : Blo 1983435 3348857 := bstep (se 2 (by rfl) ⟨1255821, by rfl⟩ : syracuseStep 3348857 = 2511643) B2511643
theorem B2232571 : Blo 1983435 2232571 := bstep (se 1 (by rfl) ⟨1674428, by rfl⟩ : syracuseStep 2232571 = 3348857) B3348857
theorem B2976761 : Blo 1983435 2976761 := bstep (se 2 (by rfl) ⟨1116285, by rfl⟩ : syracuseStep 2976761 = 2232571) B2232571
theorem B1984507 : Blo 1983435 1984507 := bstep (se 1 (by rfl) ⟨1488380, by rfl⟩ : syracuseStep 1984507 = 2976761) B2976761
theorem B10874837 : Blo 1983435 10874837 := bbase (se 7 (by rfl) ⟨127439, by rfl⟩ : syracuseStep 10874837 = 254879) (by norm_num)
theorem B28999565 : Blo 1983435 28999565 := bstep (se 3 (by rfl) ⟨5437418, by rfl⟩ : syracuseStep 28999565 = 10874837) B10874837
theorem B19333043 : Blo 1983435 19333043 := bstep (se 1 (by rfl) ⟨14499782, by rfl⟩ : syracuseStep 19333043 = 28999565) B28999565
theorem B206219125 : Blo 1983435 206219125 := bstep (se 5 (by rfl) ⟨9666521, by rfl⟩ : syracuseStep 206219125 = 19333043) B19333043
theorem B274958833 : Blo 1983435 274958833 := bstep (se 2 (by rfl) ⟨103109562, by rfl⟩ : syracuseStep 274958833 = 206219125) B206219125
theorem B366611777 : Blo 1983435 366611777 := bstep (se 2 (by rfl) ⟨137479416, by rfl⟩ : syracuseStep 366611777 = 274958833) B274958833
theorem B244407851 : Blo 1983435 244407851 := bstep (se 1 (by rfl) ⟨183305888, by rfl⟩ : syracuseStep 244407851 = 366611777) B366611777
theorem B162938567 : Blo 1983435 162938567 := bstep (se 1 (by rfl) ⟨122203925, by rfl⟩ : syracuseStep 162938567 = 244407851) B244407851
theorem B108625711 : Blo 1983435 108625711 := bstep (se 1 (by rfl) ⟨81469283, by rfl⟩ : syracuseStep 108625711 = 162938567) B162938567
theorem B144834281 : Blo 1983435 144834281 := bstep (se 2 (by rfl) ⟨54312855, by rfl⟩ : syracuseStep 144834281 = 108625711) B108625711
theorem B96556187 : Blo 1983435 96556187 := bstep (se 1 (by rfl) ⟨72417140, by rfl⟩ : syracuseStep 96556187 = 144834281) B144834281
theorem B64370791 : Blo 1983435 64370791 := bstep (se 1 (by rfl) ⟨48278093, by rfl⟩ : syracuseStep 64370791 = 96556187) B96556187
theorem B85827721 : Blo 1983435 85827721 := bstep (se 2 (by rfl) ⟨32185395, by rfl⟩ : syracuseStep 85827721 = 64370791) B64370791
theorem B114436961 : Blo 1983435 114436961 := bstep (se 2 (by rfl) ⟨42913860, by rfl⟩ : syracuseStep 114436961 = 85827721) B85827721
theorem B76291307 : Blo 1983435 76291307 := bstep (se 1 (by rfl) ⟨57218480, by rfl⟩ : syracuseStep 76291307 = 114436961) B114436961
theorem B50860871 : Blo 1983435 50860871 := bstep (se 1 (by rfl) ⟨38145653, by rfl⟩ : syracuseStep 50860871 = 76291307) B76291307
theorem B33907247 : Blo 1983435 33907247 := bstep (se 1 (by rfl) ⟨25430435, by rfl⟩ : syracuseStep 33907247 = 50860871) B50860871
theorem B22604831 : Blo 1983435 22604831 := bstep (se 1 (by rfl) ⟨16953623, by rfl⟩ : syracuseStep 22604831 = 33907247) B33907247
theorem B15069887 : Blo 1983435 15069887 := bstep (se 1 (by rfl) ⟨11302415, by rfl⟩ : syracuseStep 15069887 = 22604831) B22604831
theorem B10046591 : Blo 1983435 10046591 := bstep (se 1 (by rfl) ⟨7534943, by rfl⟩ : syracuseStep 10046591 = 15069887) B15069887
theorem B6697727 : Blo 1983435 6697727 := bstep (se 1 (by rfl) ⟨5023295, by rfl⟩ : syracuseStep 6697727 = 10046591) B10046591
theorem B4465151 : Blo 1983435 4465151 := bstep (se 1 (by rfl) ⟨3348863, by rfl⟩ : syracuseStep 4465151 = 6697727) B6697727
theorem B2976767 : Blo 1983435 2976767 := bstep (se 1 (by rfl) ⟨2232575, by rfl⟩ : syracuseStep 2976767 = 4465151) B4465151
theorem B1984511 : Blo 1983435 1984511 := bstep (se 1 (by rfl) ⟨1488383, by rfl⟩ : syracuseStep 1984511 = 2976767) B2976767
theorem B2976773 : Blo 1983435 2976773 := bbase (se 4 (by rfl) ⟨279072, by rfl⟩ : syracuseStep 2976773 = 558145) (by norm_num)
theorem B1984515 : Blo 1983435 1984515 := bstep (se 1 (by rfl) ⟨1488386, by rfl⟩ : syracuseStep 1984515 = 2976773) B2976773
theorem B3348877 : Blo 1983435 3348877 := bbase (se 3 (by rfl) ⟨627914, by rfl⟩ : syracuseStep 3348877 = 1255829) (by norm_num)
theorem B4465169 : Blo 1983435 4465169 := bstep (se 2 (by rfl) ⟨1674438, by rfl⟩ : syracuseStep 4465169 = 3348877) B3348877
theorem B2976779 : Blo 1983435 2976779 := bstep (se 1 (by rfl) ⟨2232584, by rfl⟩ : syracuseStep 2976779 = 4465169) B4465169
theorem B1984519 : Blo 1983435 1984519 := bstep (se 1 (by rfl) ⟨1488389, by rfl⟩ : syracuseStep 1984519 = 2976779) B2976779
theorem B2232589 : Blo 1983435 2232589 := bbase (se 3 (by rfl) ⟨418610, by rfl⟩ : syracuseStep 2232589 = 837221) (by norm_num)
theorem B2976785 : Blo 1983435 2976785 := bstep (se 2 (by rfl) ⟨1116294, by rfl⟩ : syracuseStep 2976785 = 2232589) B2232589
theorem B1984523 : Blo 1983435 1984523 := bstep (se 1 (by rfl) ⟨1488392, by rfl⟩ : syracuseStep 1984523 = 2976785) B2976785
theorem B6697781 : Blo 1983435 6697781 := bbase (se 5 (by rfl) ⟨313958, by rfl⟩ : syracuseStep 6697781 = 627917) (by norm_num)
theorem B4465187 : Blo 1983435 4465187 := bstep (se 1 (by rfl) ⟨3348890, by rfl⟩ : syracuseStep 4465187 = 6697781) B6697781
theorem B2976791 : Blo 1983435 2976791 := bstep (se 1 (by rfl) ⟨2232593, by rfl⟩ : syracuseStep 2976791 = 4465187) B4465187
theorem B1984527 : Blo 1983435 1984527 := bstep (se 1 (by rfl) ⟨1488395, by rfl⟩ : syracuseStep 1984527 = 2976791) B2976791
theorem B2976797 : Blo 1983435 2976797 := bbase (se 3 (by rfl) ⟨558149, by rfl⟩ : syracuseStep 2976797 = 1116299) (by norm_num)
theorem B1984531 : Blo 1983435 1984531 := bstep (se 1 (by rfl) ⟨1488398, by rfl⟩ : syracuseStep 1984531 = 2976797) B2976797
theorem B4465205 : Blo 1983435 4465205 := bbase (se 5 (by rfl) ⟨209306, by rfl⟩ : syracuseStep 4465205 = 418613) (by norm_num)
theorem B2976803 : Blo 1983435 2976803 := bstep (se 1 (by rfl) ⟨2232602, by rfl⟩ : syracuseStep 2976803 = 4465205) B4465205
theorem B1984535 : Blo 1983435 1984535 := bstep (se 1 (by rfl) ⟨1488401, by rfl⟩ : syracuseStep 1984535 = 2976803) B2976803
theorem B8476933 : Blo 1983435 8476933 := bbase (se 4 (by rfl) ⟨794712, by rfl⟩ : syracuseStep 8476933 = 1589425) (by norm_num)
theorem B11302577 : Blo 1983435 11302577 := bstep (se 2 (by rfl) ⟨4238466, by rfl⟩ : syracuseStep 11302577 = 8476933) B8476933
theorem B7535051 : Blo 1983435 7535051 := bstep (se 1 (by rfl) ⟨5651288, by rfl⟩ : syracuseStep 7535051 = 11302577) B11302577
theorem B5023367 : Blo 1983435 5023367 := bstep (se 1 (by rfl) ⟨3767525, by rfl⟩ : syracuseStep 5023367 = 7535051) B7535051
theorem B3348911 : Blo 1983435 3348911 := bstep (se 1 (by rfl) ⟨2511683, by rfl⟩ : syracuseStep 3348911 = 5023367) B5023367
theorem B2232607 : Blo 1983435 2232607 := bstep (se 1 (by rfl) ⟨1674455, by rfl⟩ : syracuseStep 2232607 = 3348911) B3348911
theorem B2976809 : Blo 1983435 2976809 := bstep (se 2 (by rfl) ⟨1116303, by rfl⟩ : syracuseStep 2976809 = 2232607) B2232607
theorem B1984539 : Blo 1983435 1984539 := bstep (se 1 (by rfl) ⟨1488404, by rfl⟩ : syracuseStep 1984539 = 2976809) B2976809
theorem B8476949 : Blo 1983435 8476949 := bbase (se 6 (by rfl) ⟨198678, by rfl⟩ : syracuseStep 8476949 = 397357) (by norm_num)
theorem B5651299 : Blo 1983435 5651299 := bstep (se 1 (by rfl) ⟨4238474, by rfl⟩ : syracuseStep 5651299 = 8476949) B8476949
theorem B7535065 : Blo 1983435 7535065 := bstep (se 2 (by rfl) ⟨2825649, by rfl⟩ : syracuseStep 7535065 = 5651299) B5651299
theorem B10046753 : Blo 1983435 10046753 := bstep (se 2 (by rfl) ⟨3767532, by rfl⟩ : syracuseStep 10046753 = 7535065) B7535065
theorem B6697835 : Blo 1983435 6697835 := bstep (se 1 (by rfl) ⟨5023376, by rfl⟩ : syracuseStep 6697835 = 10046753) B10046753
theorem B4465223 : Blo 1983435 4465223 := bstep (se 1 (by rfl) ⟨3348917, by rfl⟩ : syracuseStep 4465223 = 6697835) B6697835
theorem B2976815 : Blo 1983435 2976815 := bstep (se 1 (by rfl) ⟨2232611, by rfl⟩ : syracuseStep 2976815 = 4465223) B4465223
theorem B1984543 : Blo 1983435 1984543 := bstep (se 1 (by rfl) ⟨1488407, by rfl⟩ : syracuseStep 1984543 = 2976815) B2976815
theorem B2976821 : Blo 1983435 2976821 := bbase (se 5 (by rfl) ⟨139538, by rfl⟩ : syracuseStep 2976821 = 279077) (by norm_num)
theorem B1984547 : Blo 1983435 1984547 := bstep (se 1 (by rfl) ⟨1488410, by rfl⟩ : syracuseStep 1984547 = 2976821) B2976821
theorem B5023397 : Blo 1983435 5023397 := bbase (se 4 (by rfl) ⟨470943, by rfl⟩ : syracuseStep 5023397 = 941887) (by norm_num)
theorem B3348931 : Blo 1983435 3348931 := bstep (se 1 (by rfl) ⟨2511698, by rfl⟩ : syracuseStep 3348931 = 5023397) B5023397
theorem B4465241 : Blo 1983435 4465241 := bstep (se 2 (by rfl) ⟨1674465, by rfl⟩ : syracuseStep 4465241 = 3348931) B3348931
theorem B2976827 : Blo 1983435 2976827 := bstep (se 1 (by rfl) ⟨2232620, by rfl⟩ : syracuseStep 2976827 = 4465241) B4465241
theorem B1984551 : Blo 1983435 1984551 := bstep (se 1 (by rfl) ⟨1488413, by rfl⟩ : syracuseStep 1984551 = 2976827) B2976827
theorem B2232625 : Blo 1983435 2232625 := bbase (se 2 (by rfl) ⟨837234, by rfl⟩ : syracuseStep 2232625 = 1674469) (by norm_num)
theorem B2976833 : Blo 1983435 2976833 := bstep (se 2 (by rfl) ⟨1116312, by rfl⟩ : syracuseStep 2976833 = 2232625) B2232625
theorem B1984555 : Blo 1983435 1984555 := bstep (se 1 (by rfl) ⟨1488416, by rfl⟩ : syracuseStep 1984555 = 2976833) B2976833
theorem B4238509 : Blo 1983435 4238509 := bbase (se 3 (by rfl) ⟨794720, by rfl⟩ : syracuseStep 4238509 = 1589441) (by norm_num)
theorem B5651345 : Blo 1983435 5651345 := bstep (se 2 (by rfl) ⟨2119254, by rfl⟩ : syracuseStep 5651345 = 4238509) B4238509
theorem B3767563 : Blo 1983435 3767563 := bstep (se 1 (by rfl) ⟨2825672, by rfl⟩ : syracuseStep 3767563 = 5651345) B5651345
theorem B5023417 : Blo 1983435 5023417 := bstep (se 2 (by rfl) ⟨1883781, by rfl⟩ : syracuseStep 5023417 = 3767563) B3767563
theorem B6697889 : Blo 1983435 6697889 := bstep (se 2 (by rfl) ⟨2511708, by rfl⟩ : syracuseStep 6697889 = 5023417) B5023417
theorem B4465259 : Blo 1983435 4465259 := bstep (se 1 (by rfl) ⟨3348944, by rfl⟩ : syracuseStep 4465259 = 6697889) B6697889
theorem B2976839 : Blo 1983435 2976839 := bstep (se 1 (by rfl) ⟨2232629, by rfl⟩ : syracuseStep 2976839 = 4465259) B4465259
theorem B1984559 : Blo 1983435 1984559 := bstep (se 1 (by rfl) ⟨1488419, by rfl⟩ : syracuseStep 1984559 = 2976839) B2976839
theorem B2976845 : Blo 1983435 2976845 := bbase (se 3 (by rfl) ⟨558158, by rfl⟩ : syracuseStep 2976845 = 1116317) (by norm_num)
theorem B1984563 : Blo 1983435 1984563 := bstep (se 1 (by rfl) ⟨1488422, by rfl⟩ : syracuseStep 1984563 = 2976845) B2976845
theorem B4465277 : Blo 1983435 4465277 := bbase (se 3 (by rfl) ⟨837239, by rfl⟩ : syracuseStep 4465277 = 1674479) (by norm_num)
theorem B2976851 : Blo 1983435 2976851 := bstep (se 1 (by rfl) ⟨2232638, by rfl⟩ : syracuseStep 2976851 = 4465277) B4465277
theorem B1984567 : Blo 1983435 1984567 := bstep (se 1 (by rfl) ⟨1488425, by rfl⟩ : syracuseStep 1984567 = 2976851) B2976851
theorem B3348965 : Blo 1983435 3348965 := bbase (se 4 (by rfl) ⟨313965, by rfl⟩ : syracuseStep 3348965 = 627931) (by norm_num)
theorem B2232643 : Blo 1983435 2232643 := bstep (se 1 (by rfl) ⟨1674482, by rfl⟩ : syracuseStep 2232643 = 3348965) B3348965
theorem B2976857 : Blo 1983435 2976857 := bstep (se 2 (by rfl) ⟨1116321, by rfl⟩ : syracuseStep 2976857 = 2232643) B2232643
theorem B1984571 : Blo 1983435 1984571 := bstep (se 1 (by rfl) ⟨1488428, by rfl⟩ : syracuseStep 1984571 = 2976857) B2976857
theorem B5091997 : Blo 1983435 5091997 := bbase (se 3 (by rfl) ⟨954749, by rfl⟩ : syracuseStep 5091997 = 1909499) (by norm_num)
theorem B6789329 : Blo 1983435 6789329 := bstep (se 2 (by rfl) ⟨2545998, by rfl⟩ : syracuseStep 6789329 = 5091997) B5091997
theorem B4526219 : Blo 1983435 4526219 := bstep (se 1 (by rfl) ⟨3394664, by rfl⟩ : syracuseStep 4526219 = 6789329) B6789329
theorem B12069917 : Blo 1983435 12069917 := bstep (se 3 (by rfl) ⟨2263109, by rfl⟩ : syracuseStep 12069917 = 4526219) B4526219
theorem B8046611 : Blo 1983435 8046611 := bstep (se 1 (by rfl) ⟨6034958, by rfl⟩ : syracuseStep 8046611 = 12069917) B12069917
theorem B5364407 : Blo 1983435 5364407 := bstep (se 1 (by rfl) ⟨4023305, by rfl⟩ : syracuseStep 5364407 = 8046611) B8046611
theorem B14305085 : Blo 1983435 14305085 := bstep (se 3 (by rfl) ⟨2682203, by rfl⟩ : syracuseStep 14305085 = 5364407) B5364407
theorem B9536723 : Blo 1983435 9536723 := bstep (se 1 (by rfl) ⟨7152542, by rfl⟩ : syracuseStep 9536723 = 14305085) B14305085
theorem B6357815 : Blo 1983435 6357815 := bstep (se 1 (by rfl) ⟨4768361, by rfl⟩ : syracuseStep 6357815 = 9536723) B9536723
theorem B4238543 : Blo 1983435 4238543 := bstep (se 1 (by rfl) ⟨3178907, by rfl⟩ : syracuseStep 4238543 = 6357815) B6357815
theorem B2825695 : Blo 1983435 2825695 := bstep (se 1 (by rfl) ⟨2119271, by rfl⟩ : syracuseStep 2825695 = 4238543) B4238543
theorem B15070373 : Blo 1983435 15070373 := bstep (se 4 (by rfl) ⟨1412847, by rfl⟩ : syracuseStep 15070373 = 2825695) B2825695
theorem B10046915 : Blo 1983435 10046915 := bstep (se 1 (by rfl) ⟨7535186, by rfl⟩ : syracuseStep 10046915 = 15070373) B15070373
theorem B6697943 : Blo 1983435 6697943 := bstep (se 1 (by rfl) ⟨5023457, by rfl⟩ : syracuseStep 6697943 = 10046915) B10046915
theorem B4465295 : Blo 1983435 4465295 := bstep (se 1 (by rfl) ⟨3348971, by rfl⟩ : syracuseStep 4465295 = 6697943) B6697943
theorem B2976863 : Blo 1983435 2976863 := bstep (se 1 (by rfl) ⟨2232647, by rfl⟩ : syracuseStep 2976863 = 4465295) B4465295
theorem B1984575 : Blo 1983435 1984575 := bstep (se 1 (by rfl) ⟨1488431, by rfl⟩ : syracuseStep 1984575 = 2976863) B2976863
theorem B2976869 : Blo 1983435 2976869 := bbase (se 4 (by rfl) ⟨279081, by rfl⟩ : syracuseStep 2976869 = 558163) (by norm_num)
theorem B1984579 : Blo 1983435 1984579 := bstep (se 1 (by rfl) ⟨1488434, by rfl⟩ : syracuseStep 1984579 = 2976869) B2976869
theorem B2449693 : Blo 1983435 2449693 := bbase (se 3 (by rfl) ⟨459317, by rfl⟩ : syracuseStep 2449693 = 918635) (by norm_num)
theorem B3266257 : Blo 1983435 3266257 := bstep (se 2 (by rfl) ⟨1224846, by rfl⟩ : syracuseStep 3266257 = 2449693) B2449693
theorem B4355009 : Blo 1983435 4355009 := bstep (se 2 (by rfl) ⟨1633128, by rfl⟩ : syracuseStep 4355009 = 3266257) B3266257
theorem B46453429 : Blo 1983435 46453429 := bstep (se 5 (by rfl) ⟨2177504, by rfl⟩ : syracuseStep 46453429 = 4355009) B4355009
theorem B61937905 : Blo 1983435 61937905 := bstep (se 2 (by rfl) ⟨23226714, by rfl⟩ : syracuseStep 61937905 = 46453429) B46453429
theorem B82583873 : Blo 1983435 82583873 := bstep (se 2 (by rfl) ⟨30968952, by rfl⟩ : syracuseStep 82583873 = 61937905) B61937905
theorem B55055915 : Blo 1983435 55055915 := bstep (se 1 (by rfl) ⟨41291936, by rfl⟩ : syracuseStep 55055915 = 82583873) B82583873
theorem B36703943 : Blo 1983435 36703943 := bstep (se 1 (by rfl) ⟨27527957, by rfl⟩ : syracuseStep 36703943 = 55055915) B55055915
theorem B24469295 : Blo 1983435 24469295 := bstep (se 1 (by rfl) ⟨18351971, by rfl⟩ : syracuseStep 24469295 = 36703943) B36703943
theorem B65251453 : Blo 1983435 65251453 := bstep (se 3 (by rfl) ⟨12234647, by rfl⟩ : syracuseStep 65251453 = 24469295) B24469295
theorem B87001937 : Blo 1983435 87001937 := bstep (se 2 (by rfl) ⟨32625726, by rfl⟩ : syracuseStep 87001937 = 65251453) B65251453
theorem B58001291 : Blo 1983435 58001291 := bstep (se 1 (by rfl) ⟨43500968, by rfl⟩ : syracuseStep 58001291 = 87001937) B87001937
theorem B38667527 : Blo 1983435 38667527 := bstep (se 1 (by rfl) ⟨29000645, by rfl⟩ : syracuseStep 38667527 = 58001291) B58001291
theorem B25778351 : Blo 1983435 25778351 := bstep (se 1 (by rfl) ⟨19333763, by rfl⟩ : syracuseStep 25778351 = 38667527) B38667527
theorem B17185567 : Blo 1983435 17185567 := bstep (se 1 (by rfl) ⟨12889175, by rfl⟩ : syracuseStep 17185567 = 25778351) B25778351
theorem B22914089 : Blo 1983435 22914089 := bstep (se 2 (by rfl) ⟨8592783, by rfl⟩ : syracuseStep 22914089 = 17185567) B17185567
theorem B15276059 : Blo 1983435 15276059 := bstep (se 1 (by rfl) ⟨11457044, by rfl⟩ : syracuseStep 15276059 = 22914089) B22914089
theorem B10184039 : Blo 1983435 10184039 := bstep (se 1 (by rfl) ⟨7638029, by rfl⟩ : syracuseStep 10184039 = 15276059) B15276059
theorem B6789359 : Blo 1983435 6789359 := bstep (se 1 (by rfl) ⟨5092019, by rfl⟩ : syracuseStep 6789359 = 10184039) B10184039
theorem B18104957 : Blo 1983435 18104957 := bstep (se 3 (by rfl) ⟨3394679, by rfl⟩ : syracuseStep 18104957 = 6789359) B6789359
theorem B12069971 : Blo 1983435 12069971 := bstep (se 1 (by rfl) ⟨9052478, by rfl⟩ : syracuseStep 12069971 = 18104957) B18104957
theorem B8046647 : Blo 1983435 8046647 := bstep (se 1 (by rfl) ⟨6034985, by rfl⟩ : syracuseStep 8046647 = 12069971) B12069971
theorem B5364431 : Blo 1983435 5364431 := bstep (se 1 (by rfl) ⟨4023323, by rfl⟩ : syracuseStep 5364431 = 8046647) B8046647
theorem B3576287 : Blo 1983435 3576287 := bstep (se 1 (by rfl) ⟨2682215, by rfl⟩ : syracuseStep 3576287 = 5364431) B5364431
theorem B2384191 : Blo 1983435 2384191 := bstep (se 1 (by rfl) ⟨1788143, by rfl⟩ : syracuseStep 2384191 = 3576287) B3576287
theorem B3178921 : Blo 1983435 3178921 := bstep (se 2 (by rfl) ⟨1192095, by rfl⟩ : syracuseStep 3178921 = 2384191) B2384191
theorem B4238561 : Blo 1983435 4238561 := bstep (se 2 (by rfl) ⟨1589460, by rfl⟩ : syracuseStep 4238561 = 3178921) B3178921
theorem B2825707 : Blo 1983435 2825707 := bstep (se 1 (by rfl) ⟨2119280, by rfl⟩ : syracuseStep 2825707 = 4238561) B4238561
theorem B3767609 : Blo 1983435 3767609 := bstep (se 2 (by rfl) ⟨1412853, by rfl⟩ : syracuseStep 3767609 = 2825707) B2825707
theorem B2511739 : Blo 1983435 2511739 := bstep (se 1 (by rfl) ⟨1883804, by rfl⟩ : syracuseStep 2511739 = 3767609) B3767609
theorem B3348985 : Blo 1983435 3348985 := bstep (se 2 (by rfl) ⟨1255869, by rfl⟩ : syracuseStep 3348985 = 2511739) B2511739
theorem B4465313 : Blo 1983435 4465313 := bstep (se 2 (by rfl) ⟨1674492, by rfl⟩ : syracuseStep 4465313 = 3348985) B3348985
theorem B2976875 : Blo 1983435 2976875 := bstep (se 1 (by rfl) ⟨2232656, by rfl⟩ : syracuseStep 2976875 = 4465313) B4465313
theorem B1984583 : Blo 1983435 1984583 := bstep (se 1 (by rfl) ⟨1488437, by rfl⟩ : syracuseStep 1984583 = 2976875) B2976875
theorem B2232661 : Blo 1983435 2232661 := bbase (se 10 (by rfl) ⟨3270, by rfl⟩ : syracuseStep 2232661 = 6541) (by norm_num)
theorem B2976881 : Blo 1983435 2976881 := bstep (se 2 (by rfl) ⟨1116330, by rfl⟩ : syracuseStep 2976881 = 2232661) B2232661
theorem B1984587 : Blo 1983435 1984587 := bstep (se 1 (by rfl) ⟨1488440, by rfl⟩ : syracuseStep 1984587 = 2976881) B2976881
theorem B2511749 : Blo 1983435 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B6697997 : Blo 1983435 6697997 := bstep (se 3 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 6697997 = 2511749) B2511749
theorem B4465331 : Blo 1983435 4465331 := bstep (se 1 (by rfl) ⟨3348998, by rfl⟩ : syracuseStep 4465331 = 6697997) B6697997
theorem B2976887 : Blo 1983435 2976887 := bstep (se 1 (by rfl) ⟨2232665, by rfl⟩ : syracuseStep 2976887 = 4465331) B4465331
theorem B1984591 : Blo 1983435 1984591 := bstep (se 1 (by rfl) ⟨1488443, by rfl⟩ : syracuseStep 1984591 = 2976887) B2976887
theorem B2976893 : Blo 1983435 2976893 := bbase (se 3 (by rfl) ⟨558167, by rfl⟩ : syracuseStep 2976893 = 1116335) (by norm_num)
theorem B1984595 : Blo 1983435 1984595 := bstep (se 1 (by rfl) ⟨1488446, by rfl⟩ : syracuseStep 1984595 = 2976893) B2976893
theorem B4465349 : Blo 1983435 4465349 := bbase (se 4 (by rfl) ⟨418626, by rfl⟩ : syracuseStep 4465349 = 837253) (by norm_num)
theorem B2976899 : Blo 1983435 2976899 := bstep (se 1 (by rfl) ⟨2232674, by rfl⟩ : syracuseStep 2976899 = 4465349) B4465349
theorem B1984599 : Blo 1983435 1984599 := bstep (se 1 (by rfl) ⟨1488449, by rfl⟩ : syracuseStep 1984599 = 2976899) B2976899
theorem B19073717 : Blo 1983435 19073717 := bbase (se 5 (by rfl) ⟨894080, by rfl⟩ : syracuseStep 19073717 = 1788161) (by norm_num)
theorem B12715811 : Blo 1983435 12715811 := bstep (se 1 (by rfl) ⟨9536858, by rfl⟩ : syracuseStep 12715811 = 19073717) B19073717
theorem B8477207 : Blo 1983435 8477207 := bstep (se 1 (by rfl) ⟨6357905, by rfl⟩ : syracuseStep 8477207 = 12715811) B12715811
theorem B5651471 : Blo 1983435 5651471 := bstep (se 1 (by rfl) ⟨4238603, by rfl⟩ : syracuseStep 5651471 = 8477207) B8477207
theorem B3767647 : Blo 1983435 3767647 := bstep (se 1 (by rfl) ⟨2825735, by rfl⟩ : syracuseStep 3767647 = 5651471) B5651471
theorem B5023529 : Blo 1983435 5023529 := bstep (se 2 (by rfl) ⟨1883823, by rfl⟩ : syracuseStep 5023529 = 3767647) B3767647
theorem B3349019 : Blo 1983435 3349019 := bstep (se 1 (by rfl) ⟨2511764, by rfl⟩ : syracuseStep 3349019 = 5023529) B5023529
theorem B2232679 : Blo 1983435 2232679 := bstep (se 1 (by rfl) ⟨1674509, by rfl⟩ : syracuseStep 2232679 = 3349019) B3349019
theorem B2976905 : Blo 1983435 2976905 := bstep (se 2 (by rfl) ⟨1116339, by rfl⟩ : syracuseStep 2976905 = 2232679) B2232679
theorem B1984603 : Blo 1983435 1984603 := bstep (se 1 (by rfl) ⟨1488452, by rfl⟩ : syracuseStep 1984603 = 2976905) B2976905
theorem B10047077 : Blo 1983435 10047077 := bbase (se 4 (by rfl) ⟨941913, by rfl⟩ : syracuseStep 10047077 = 1883827) (by norm_num)
theorem B6698051 : Blo 1983435 6698051 := bstep (se 1 (by rfl) ⟨5023538, by rfl⟩ : syracuseStep 6698051 = 10047077) B10047077
theorem B4465367 : Blo 1983435 4465367 := bstep (se 1 (by rfl) ⟨3349025, by rfl⟩ : syracuseStep 4465367 = 6698051) B6698051
theorem B2976911 : Blo 1983435 2976911 := bstep (se 1 (by rfl) ⟨2232683, by rfl⟩ : syracuseStep 2976911 = 4465367) B4465367
theorem B1984607 : Blo 1983435 1984607 := bstep (se 1 (by rfl) ⟨1488455, by rfl⟩ : syracuseStep 1984607 = 2976911) B2976911
theorem B2976917 : Blo 1983435 2976917 := bbase (se 6 (by rfl) ⟨69771, by rfl⟩ : syracuseStep 2976917 = 139543) (by norm_num)
theorem B1984611 : Blo 1983435 1984611 := bstep (se 1 (by rfl) ⟨1488458, by rfl⟩ : syracuseStep 1984611 = 2976917) B2976917
theorem B8046773 : Blo 1983435 8046773 := bbase (se 5 (by rfl) ⟨377192, by rfl⟩ : syracuseStep 8046773 = 754385) (by norm_num)
theorem B5364515 : Blo 1983435 5364515 := bstep (se 1 (by rfl) ⟨4023386, by rfl⟩ : syracuseStep 5364515 = 8046773) B8046773
theorem B14305373 : Blo 1983435 14305373 := bstep (se 3 (by rfl) ⟨2682257, by rfl⟩ : syracuseStep 14305373 = 5364515) B5364515
theorem B9536915 : Blo 1983435 9536915 := bstep (se 1 (by rfl) ⟨7152686, by rfl⟩ : syracuseStep 9536915 = 14305373) B14305373
theorem B6357943 : Blo 1983435 6357943 := bstep (se 1 (by rfl) ⟨4768457, by rfl⟩ : syracuseStep 6357943 = 9536915) B9536915
theorem B8477257 : Blo 1983435 8477257 := bstep (se 2 (by rfl) ⟨3178971, by rfl⟩ : syracuseStep 8477257 = 6357943) B6357943
theorem B11303009 : Blo 1983435 11303009 := bstep (se 2 (by rfl) ⟨4238628, by rfl⟩ : syracuseStep 11303009 = 8477257) B8477257
theorem B7535339 : Blo 1983435 7535339 := bstep (se 1 (by rfl) ⟨5651504, by rfl⟩ : syracuseStep 7535339 = 11303009) B11303009
theorem B5023559 : Blo 1983435 5023559 := bstep (se 1 (by rfl) ⟨3767669, by rfl⟩ : syracuseStep 5023559 = 7535339) B7535339
theorem B3349039 : Blo 1983435 3349039 := bstep (se 1 (by rfl) ⟨2511779, by rfl⟩ : syracuseStep 3349039 = 5023559) B5023559
theorem B4465385 : Blo 1983435 4465385 := bstep (se 2 (by rfl) ⟨1674519, by rfl⟩ : syracuseStep 4465385 = 3349039) B3349039
theorem B2976923 : Blo 1983435 2976923 := bstep (se 1 (by rfl) ⟨2232692, by rfl⟩ : syracuseStep 2976923 = 4465385) B4465385
theorem B1984615 : Blo 1983435 1984615 := bstep (se 1 (by rfl) ⟨1488461, by rfl⟩ : syracuseStep 1984615 = 2976923) B2976923
theorem B2232697 : Blo 1983435 2232697 := bbase (se 2 (by rfl) ⟨837261, by rfl⟩ : syracuseStep 2232697 = 1674523) (by norm_num)
theorem B2976929 : Blo 1983435 2976929 := bstep (se 2 (by rfl) ⟨1116348, by rfl⟩ : syracuseStep 2976929 = 2232697) B2232697
theorem B1984619 : Blo 1983435 1984619 := bstep (se 1 (by rfl) ⟨1488464, by rfl⟩ : syracuseStep 1984619 = 2976929) B2976929
theorem B8046805 : Blo 1983435 8046805 := bbase (se 7 (by rfl) ⟨94298, by rfl⟩ : syracuseStep 8046805 = 188597) (by norm_num)
theorem B10729073 : Blo 1983435 10729073 := bstep (se 2 (by rfl) ⟨4023402, by rfl⟩ : syracuseStep 10729073 = 8046805) B8046805
theorem B7152715 : Blo 1983435 7152715 := bstep (se 1 (by rfl) ⟨5364536, by rfl⟩ : syracuseStep 7152715 = 10729073) B10729073
theorem B9536953 : Blo 1983435 9536953 := bstep (se 2 (by rfl) ⟨3576357, by rfl⟩ : syracuseStep 9536953 = 7152715) B7152715
theorem B12715937 : Blo 1983435 12715937 := bstep (se 2 (by rfl) ⟨4768476, by rfl⟩ : syracuseStep 12715937 = 9536953) B9536953
theorem B8477291 : Blo 1983435 8477291 := bstep (se 1 (by rfl) ⟨6357968, by rfl⟩ : syracuseStep 8477291 = 12715937) B12715937
theorem B5651527 : Blo 1983435 5651527 := bstep (se 1 (by rfl) ⟨4238645, by rfl⟩ : syracuseStep 5651527 = 8477291) B8477291
theorem B7535369 : Blo 1983435 7535369 := bstep (se 2 (by rfl) ⟨2825763, by rfl⟩ : syracuseStep 7535369 = 5651527) B5651527
theorem B5023579 : Blo 1983435 5023579 := bstep (se 1 (by rfl) ⟨3767684, by rfl⟩ : syracuseStep 5023579 = 7535369) B7535369
theorem B6698105 : Blo 1983435 6698105 := bstep (se 2 (by rfl) ⟨2511789, by rfl⟩ : syracuseStep 6698105 = 5023579) B5023579
theorem B4465403 : Blo 1983435 4465403 := bstep (se 1 (by rfl) ⟨3349052, by rfl⟩ : syracuseStep 4465403 = 6698105) B6698105
theorem B2976935 : Blo 1983435 2976935 := bstep (se 1 (by rfl) ⟨2232701, by rfl⟩ : syracuseStep 2976935 = 4465403) B4465403
theorem B1984623 : Blo 1983435 1984623 := bstep (se 1 (by rfl) ⟨1488467, by rfl⟩ : syracuseStep 1984623 = 2976935) B2976935
theorem B2976941 : Blo 1983435 2976941 := bbase (se 3 (by rfl) ⟨558176, by rfl⟩ : syracuseStep 2976941 = 1116353) (by norm_num)
theorem B1984627 : Blo 1983435 1984627 := bstep (se 1 (by rfl) ⟨1488470, by rfl⟩ : syracuseStep 1984627 = 2976941) B2976941
theorem B4465421 : Blo 1983435 4465421 := bbase (se 3 (by rfl) ⟨837266, by rfl⟩ : syracuseStep 4465421 = 1674533) (by norm_num)
theorem B2976947 : Blo 1983435 2976947 := bstep (se 1 (by rfl) ⟨2232710, by rfl⟩ : syracuseStep 2976947 = 4465421) B4465421
theorem B1984631 : Blo 1983435 1984631 := bstep (se 1 (by rfl) ⟨1488473, by rfl⟩ : syracuseStep 1984631 = 2976947) B2976947
theorem B2511805 : Blo 1983435 2511805 := bbase (se 3 (by rfl) ⟨470963, by rfl⟩ : syracuseStep 2511805 = 941927) (by norm_num)
theorem B3349073 : Blo 1983435 3349073 := bstep (se 2 (by rfl) ⟨1255902, by rfl⟩ : syracuseStep 3349073 = 2511805) B2511805
theorem B2232715 : Blo 1983435 2232715 := bstep (se 1 (by rfl) ⟨1674536, by rfl⟩ : syracuseStep 2232715 = 3349073) B3349073
theorem B2976953 : Blo 1983435 2976953 := bstep (se 2 (by rfl) ⟨1116357, by rfl⟩ : syracuseStep 2976953 = 2232715) B2232715
theorem B1984635 : Blo 1983435 1984635 := bstep (se 1 (by rfl) ⟨1488476, by rfl⟩ : syracuseStep 1984635 = 2976953) B2976953
theorem B9537029 : Blo 1983435 9537029 := bbase (se 4 (by rfl) ⟨894096, by rfl⟩ : syracuseStep 9537029 = 1788193) (by norm_num)
theorem B6358019 : Blo 1983435 6358019 := bstep (se 1 (by rfl) ⟨4768514, by rfl⟩ : syracuseStep 6358019 = 9537029) B9537029
theorem B16954717 : Blo 1983435 16954717 := bstep (se 3 (by rfl) ⟨3179009, by rfl⟩ : syracuseStep 16954717 = 6358019) B6358019
theorem B22606289 : Blo 1983435 22606289 := bstep (se 2 (by rfl) ⟨8477358, by rfl⟩ : syracuseStep 22606289 = 16954717) B16954717
theorem B15070859 : Blo 1983435 15070859 := bstep (se 1 (by rfl) ⟨11303144, by rfl⟩ : syracuseStep 15070859 = 22606289) B22606289
theorem B10047239 : Blo 1983435 10047239 := bstep (se 1 (by rfl) ⟨7535429, by rfl⟩ : syracuseStep 10047239 = 15070859) B15070859
theorem B6698159 : Blo 1983435 6698159 := bstep (se 1 (by rfl) ⟨5023619, by rfl⟩ : syracuseStep 6698159 = 10047239) B10047239
theorem B4465439 : Blo 1983435 4465439 := bstep (se 1 (by rfl) ⟨3349079, by rfl⟩ : syracuseStep 4465439 = 6698159) B6698159
theorem B2976959 : Blo 1983435 2976959 := bstep (se 1 (by rfl) ⟨2232719, by rfl⟩ : syracuseStep 2976959 = 4465439) B4465439
theorem B1984639 : Blo 1983435 1984639 := bstep (se 1 (by rfl) ⟨1488479, by rfl⟩ : syracuseStep 1984639 = 2976959) B2976959
theorem B2976965 : Blo 1983435 2976965 := bbase (se 4 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 2976965 = 558181) (by norm_num)
theorem B1984643 : Blo 1983435 1984643 := bstep (se 1 (by rfl) ⟨1488482, by rfl⟩ : syracuseStep 1984643 = 2976965) B2976965
theorem B3349093 : Blo 1983435 3349093 := bbase (se 4 (by rfl) ⟨313977, by rfl⟩ : syracuseStep 3349093 = 627955) (by norm_num)
theorem B4465457 : Blo 1983435 4465457 := bstep (se 2 (by rfl) ⟨1674546, by rfl⟩ : syracuseStep 4465457 = 3349093) B3349093
theorem B2976971 : Blo 1983435 2976971 := bstep (se 1 (by rfl) ⟨2232728, by rfl⟩ : syracuseStep 2976971 = 4465457) B4465457
theorem B1984647 : Blo 1983435 1984647 := bstep (se 1 (by rfl) ⟨1488485, by rfl⟩ : syracuseStep 1984647 = 2976971) B2976971
theorem B2232733 : Blo 1983435 2232733 := bbase (se 3 (by rfl) ⟨418637, by rfl⟩ : syracuseStep 2232733 = 837275) (by norm_num)
theorem B2976977 : Blo 1983435 2976977 := bstep (se 2 (by rfl) ⟨1116366, by rfl⟩ : syracuseStep 2976977 = 2232733) B2232733
theorem B1984651 : Blo 1983435 1984651 := bstep (se 1 (by rfl) ⟨1488488, by rfl⟩ : syracuseStep 1984651 = 2976977) B2976977
theorem B6698213 : Blo 1983435 6698213 := bbase (se 4 (by rfl) ⟨627957, by rfl⟩ : syracuseStep 6698213 = 1255915) (by norm_num)
theorem B4465475 : Blo 1983435 4465475 := bstep (se 1 (by rfl) ⟨3349106, by rfl⟩ : syracuseStep 4465475 = 6698213) B6698213
theorem B2976983 : Blo 1983435 2976983 := bstep (se 1 (by rfl) ⟨2232737, by rfl⟩ : syracuseStep 2976983 = 4465475) B4465475
theorem B1984655 : Blo 1983435 1984655 := bstep (se 1 (by rfl) ⟨1488491, by rfl⟩ : syracuseStep 1984655 = 2976983) B2976983
theorem B2976989 : Blo 1983435 2976989 := bbase (se 3 (by rfl) ⟨558185, by rfl⟩ : syracuseStep 2976989 = 1116371) (by norm_num)
theorem B1984659 : Blo 1983435 1984659 := bstep (se 1 (by rfl) ⟨1488494, by rfl⟩ : syracuseStep 1984659 = 2976989) B2976989
theorem B4465493 : Blo 1983435 4465493 := bbase (se 9 (by rfl) ⟨13082, by rfl⟩ : syracuseStep 4465493 = 26165) (by norm_num)
theorem B2976995 : Blo 1983435 2976995 := bstep (se 1 (by rfl) ⟨2232746, by rfl⟩ : syracuseStep 2976995 = 4465493) B4465493
theorem B1984663 : Blo 1983435 1984663 := bstep (se 1 (by rfl) ⟨1488497, by rfl⟩ : syracuseStep 1984663 = 2976995) B2976995
theorem B5651653 : Blo 1983435 5651653 := bbase (se 4 (by rfl) ⟨529842, by rfl⟩ : syracuseStep 5651653 = 1059685) (by norm_num)
theorem B7535537 : Blo 1983435 7535537 := bstep (se 2 (by rfl) ⟨2825826, by rfl⟩ : syracuseStep 7535537 = 5651653) B5651653
theorem B5023691 : Blo 1983435 5023691 := bstep (se 1 (by rfl) ⟨3767768, by rfl⟩ : syracuseStep 5023691 = 7535537) B7535537
theorem B3349127 : Blo 1983435 3349127 := bstep (se 1 (by rfl) ⟨2511845, by rfl⟩ : syracuseStep 3349127 = 5023691) B5023691
theorem B2232751 : Blo 1983435 2232751 := bstep (se 1 (by rfl) ⟨1674563, by rfl⟩ : syracuseStep 2232751 = 3349127) B3349127
theorem B2977001 : Blo 1983435 2977001 := bstep (se 2 (by rfl) ⟨1116375, by rfl⟩ : syracuseStep 2977001 = 2232751) B2232751
theorem B1984667 : Blo 1983435 1984667 := bstep (se 1 (by rfl) ⟨1488500, by rfl⟩ : syracuseStep 1984667 = 2977001) B2977001
theorem B15276725 : Blo 1983435 15276725 := bbase (se 5 (by rfl) ⟨716096, by rfl⟩ : syracuseStep 15276725 = 1432193) (by norm_num)
theorem B10184483 : Blo 1983435 10184483 := bstep (se 1 (by rfl) ⟨7638362, by rfl⟩ : syracuseStep 10184483 = 15276725) B15276725
theorem B6789655 : Blo 1983435 6789655 := bstep (se 1 (by rfl) ⟨5092241, by rfl⟩ : syracuseStep 6789655 = 10184483) B10184483
theorem B9052873 : Blo 1983435 9052873 := bstep (se 2 (by rfl) ⟨3394827, by rfl⟩ : syracuseStep 9052873 = 6789655) B6789655
theorem B48281989 : Blo 1983435 48281989 := bstep (se 4 (by rfl) ⟨4526436, by rfl⟩ : syracuseStep 48281989 = 9052873) B9052873
theorem B64375985 : Blo 1983435 64375985 := bstep (se 2 (by rfl) ⟨24140994, by rfl⟩ : syracuseStep 64375985 = 48281989) B48281989
theorem B42917323 : Blo 1983435 42917323 := bstep (se 1 (by rfl) ⟨32187992, by rfl⟩ : syracuseStep 42917323 = 64375985) B64375985
theorem B57223097 : Blo 1983435 57223097 := bstep (se 2 (by rfl) ⟨21458661, by rfl⟩ : syracuseStep 57223097 = 42917323) B42917323
theorem B38148731 : Blo 1983435 38148731 := bstep (se 1 (by rfl) ⟨28611548, by rfl⟩ : syracuseStep 38148731 = 57223097) B57223097
theorem B25432487 : Blo 1983435 25432487 := bstep (se 1 (by rfl) ⟨19074365, by rfl⟩ : syracuseStep 25432487 = 38148731) B38148731
theorem B16954991 : Blo 1983435 16954991 := bstep (se 1 (by rfl) ⟨12716243, by rfl⟩ : syracuseStep 16954991 = 25432487) B25432487
theorem B11303327 : Blo 1983435 11303327 := bstep (se 1 (by rfl) ⟨8477495, by rfl⟩ : syracuseStep 11303327 = 16954991) B16954991
theorem B7535551 : Blo 1983435 7535551 := bstep (se 1 (by rfl) ⟨5651663, by rfl⟩ : syracuseStep 7535551 = 11303327) B11303327
theorem B10047401 : Blo 1983435 10047401 := bstep (se 2 (by rfl) ⟨3767775, by rfl⟩ : syracuseStep 10047401 = 7535551) B7535551
theorem B6698267 : Blo 1983435 6698267 := bstep (se 1 (by rfl) ⟨5023700, by rfl⟩ : syracuseStep 6698267 = 10047401) B10047401
theorem B4465511 : Blo 1983435 4465511 := bstep (se 1 (by rfl) ⟨3349133, by rfl⟩ : syracuseStep 4465511 = 6698267) B6698267
theorem B2977007 : Blo 1983435 2977007 := bstep (se 1 (by rfl) ⟨2232755, by rfl⟩ : syracuseStep 2977007 = 4465511) B4465511
theorem B1984671 : Blo 1983435 1984671 := bstep (se 1 (by rfl) ⟨1488503, by rfl⟩ : syracuseStep 1984671 = 2977007) B2977007
theorem B2977013 : Blo 1983435 2977013 := bbase (se 5 (by rfl) ⟨139547, by rfl⟩ : syracuseStep 2977013 = 279095) (by norm_num)
theorem B1984675 : Blo 1983435 1984675 := bstep (se 1 (by rfl) ⟨1488506, by rfl⟩ : syracuseStep 1984675 = 2977013) B2977013
theorem B12070549 : Blo 1983435 12070549 := bbase (se 6 (by rfl) ⟨282903, by rfl⟩ : syracuseStep 12070549 = 565807) (by norm_num)
theorem B16094065 : Blo 1983435 16094065 := bstep (se 2 (by rfl) ⟨6035274, by rfl⟩ : syracuseStep 16094065 = 12070549) B12070549
theorem B21458753 : Blo 1983435 21458753 := bstep (se 2 (by rfl) ⟨8047032, by rfl⟩ : syracuseStep 21458753 = 16094065) B16094065
theorem B14305835 : Blo 1983435 14305835 := bstep (se 1 (by rfl) ⟨10729376, by rfl⟩ : syracuseStep 14305835 = 21458753) B21458753
theorem B9537223 : Blo 1983435 9537223 := bstep (se 1 (by rfl) ⟨7152917, by rfl⟩ : syracuseStep 9537223 = 14305835) B14305835
theorem B12716297 : Blo 1983435 12716297 := bstep (se 2 (by rfl) ⟨4768611, by rfl⟩ : syracuseStep 12716297 = 9537223) B9537223
theorem B8477531 : Blo 1983435 8477531 := bstep (se 1 (by rfl) ⟨6358148, by rfl⟩ : syracuseStep 8477531 = 12716297) B12716297
theorem B5651687 : Blo 1983435 5651687 := bstep (se 1 (by rfl) ⟨4238765, by rfl⟩ : syracuseStep 5651687 = 8477531) B8477531
theorem B3767791 : Blo 1983435 3767791 := bstep (se 1 (by rfl) ⟨2825843, by rfl⟩ : syracuseStep 3767791 = 5651687) B5651687
theorem B5023721 : Blo 1983435 5023721 := bstep (se 2 (by rfl) ⟨1883895, by rfl⟩ : syracuseStep 5023721 = 3767791) B3767791
theorem B3349147 : Blo 1983435 3349147 := bstep (se 1 (by rfl) ⟨2511860, by rfl⟩ : syracuseStep 3349147 = 5023721) B5023721
theorem B4465529 : Blo 1983435 4465529 := bstep (se 2 (by rfl) ⟨1674573, by rfl⟩ : syracuseStep 4465529 = 3349147) B3349147
theorem B2977019 : Blo 1983435 2977019 := bstep (se 1 (by rfl) ⟨2232764, by rfl⟩ : syracuseStep 2977019 = 4465529) B4465529
theorem B1984679 : Blo 1983435 1984679 := bstep (se 1 (by rfl) ⟨1488509, by rfl⟩ : syracuseStep 1984679 = 2977019) B2977019
theorem B2232769 : Blo 1983435 2232769 := bbase (se 2 (by rfl) ⟨837288, by rfl⟩ : syracuseStep 2232769 = 1674577) (by norm_num)
theorem B2977025 : Blo 1983435 2977025 := bstep (se 2 (by rfl) ⟨1116384, by rfl⟩ : syracuseStep 2977025 = 2232769) B2232769
theorem B1984683 : Blo 1983435 1984683 := bstep (se 1 (by rfl) ⟨1488512, by rfl⟩ : syracuseStep 1984683 = 2977025) B2977025
theorem B5023741 : Blo 1983435 5023741 := bbase (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) (by norm_num)
theorem B6698321 : Blo 1983435 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B4465547 : Blo 1983435 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B2977031 : Blo 1983435 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B1984687 : Blo 1983435 1984687 := bstep (se 1 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 1984687 = 2977031) B2977031
theorem B2977037 : Blo 1983435 2977037 := bbase (se 3 (by rfl) ⟨558194, by rfl⟩ : syracuseStep 2977037 = 1116389) (by norm_num)
theorem B1984691 : Blo 1983435 1984691 := bstep (se 1 (by rfl) ⟨1488518, by rfl⟩ : syracuseStep 1984691 = 2977037) B2977037
theorem B4465565 : Blo 1983435 4465565 := bbase (se 3 (by rfl) ⟨837293, by rfl⟩ : syracuseStep 4465565 = 1674587) (by norm_num)
theorem B2977043 : Blo 1983435 2977043 := bstep (se 1 (by rfl) ⟨2232782, by rfl⟩ : syracuseStep 2977043 = 4465565) B4465565
theorem B1984695 : Blo 1983435 1984695 := bstep (se 1 (by rfl) ⟨1488521, by rfl⟩ : syracuseStep 1984695 = 2977043) B2977043
theorem B3349181 : Blo 1983435 3349181 := bbase (se 3 (by rfl) ⟨627971, by rfl⟩ : syracuseStep 3349181 = 1255943) (by norm_num)
theorem B2232787 : Blo 1983435 2232787 := bstep (se 1 (by rfl) ⟨1674590, by rfl⟩ : syracuseStep 2232787 = 3349181) B3349181
theorem B2977049 : Blo 1983435 2977049 := bstep (se 2 (by rfl) ⟨1116393, by rfl⟩ : syracuseStep 2977049 = 2232787) B2232787
theorem B1984699 : Blo 1983435 1984699 := bstep (se 1 (by rfl) ⟨1488524, by rfl⟩ : syracuseStep 1984699 = 2977049) B2977049
theorem B11303509 : Blo 1983435 11303509 := bbase (se 8 (by rfl) ⟨66231, by rfl⟩ : syracuseStep 11303509 = 132463) (by norm_num)
theorem B15071345 : Blo 1983435 15071345 := bstep (se 2 (by rfl) ⟨5651754, by rfl⟩ : syracuseStep 15071345 = 11303509) B11303509
theorem B10047563 : Blo 1983435 10047563 := bstep (se 1 (by rfl) ⟨7535672, by rfl⟩ : syracuseStep 10047563 = 15071345) B15071345
theorem B6698375 : Blo 1983435 6698375 := bstep (se 1 (by rfl) ⟨5023781, by rfl⟩ : syracuseStep 6698375 = 10047563) B10047563
theorem B4465583 : Blo 1983435 4465583 := bstep (se 1 (by rfl) ⟨3349187, by rfl⟩ : syracuseStep 4465583 = 6698375) B6698375
theorem B2977055 : Blo 1983435 2977055 := bstep (se 1 (by rfl) ⟨2232791, by rfl⟩ : syracuseStep 2977055 = 4465583) B4465583
theorem B1984703 : Blo 1983435 1984703 := bstep (se 1 (by rfl) ⟨1488527, by rfl⟩ : syracuseStep 1984703 = 2977055) B2977055
theorem B2977061 : Blo 1983435 2977061 := bbase (se 4 (by rfl) ⟨279099, by rfl⟩ : syracuseStep 2977061 = 558199) (by norm_num)
theorem B1984707 : Blo 1983435 1984707 := bstep (se 1 (by rfl) ⟨1488530, by rfl⟩ : syracuseStep 1984707 = 2977061) B2977061
theorem B2511901 : Blo 1983435 2511901 := bbase (se 3 (by rfl) ⟨470981, by rfl⟩ : syracuseStep 2511901 = 941963) (by norm_num)
theorem B3349201 : Blo 1983435 3349201 := bstep (se 2 (by rfl) ⟨1255950, by rfl⟩ : syracuseStep 3349201 = 2511901) B2511901
theorem B4465601 : Blo 1983435 4465601 := bstep (se 2 (by rfl) ⟨1674600, by rfl⟩ : syracuseStep 4465601 = 3349201) B3349201
theorem B2977067 : Blo 1983435 2977067 := bstep (se 1 (by rfl) ⟨2232800, by rfl⟩ : syracuseStep 2977067 = 4465601) B4465601
theorem B1984711 : Blo 1983435 1984711 := bstep (se 1 (by rfl) ⟨1488533, by rfl⟩ : syracuseStep 1984711 = 2977067) B2977067
theorem B2232805 : Blo 1983435 2232805 := bbase (se 4 (by rfl) ⟨209325, by rfl⟩ : syracuseStep 2232805 = 418651) (by norm_num)
theorem B2977073 : Blo 1983435 2977073 := bstep (se 2 (by rfl) ⟨1116402, by rfl⟩ : syracuseStep 2977073 = 2232805) B2232805
theorem B1984715 : Blo 1983435 1984715 := bstep (se 1 (by rfl) ⟨1488536, by rfl⟩ : syracuseStep 1984715 = 2977073) B2977073
theorem B6358277 : Blo 1983435 6358277 := bbase (se 4 (by rfl) ⟨596088, by rfl⟩ : syracuseStep 6358277 = 1192177) (by norm_num)
theorem B4238851 : Blo 1983435 4238851 := bstep (se 1 (by rfl) ⟨3179138, by rfl⟩ : syracuseStep 4238851 = 6358277) B6358277
theorem B5651801 : Blo 1983435 5651801 := bstep (se 2 (by rfl) ⟨2119425, by rfl⟩ : syracuseStep 5651801 = 4238851) B4238851
theorem B3767867 : Blo 1983435 3767867 := bstep (se 1 (by rfl) ⟨2825900, by rfl⟩ : syracuseStep 3767867 = 5651801) B5651801
theorem B2511911 : Blo 1983435 2511911 := bstep (se 1 (by rfl) ⟨1883933, by rfl⟩ : syracuseStep 2511911 = 3767867) B3767867
theorem B6698429 : Blo 1983435 6698429 := bstep (se 3 (by rfl) ⟨1255955, by rfl⟩ : syracuseStep 6698429 = 2511911) B2511911
theorem B4465619 : Blo 1983435 4465619 := bstep (se 1 (by rfl) ⟨3349214, by rfl⟩ : syracuseStep 4465619 = 6698429) B6698429
theorem B2977079 : Blo 1983435 2977079 := bstep (se 1 (by rfl) ⟨2232809, by rfl⟩ : syracuseStep 2977079 = 4465619) B4465619
theorem B1984719 : Blo 1983435 1984719 := bstep (se 1 (by rfl) ⟨1488539, by rfl⟩ : syracuseStep 1984719 = 2977079) B2977079
theorem B2977085 : Blo 1983435 2977085 := bbase (se 3 (by rfl) ⟨558203, by rfl⟩ : syracuseStep 2977085 = 1116407) (by norm_num)
theorem B1984723 : Blo 1983435 1984723 := bstep (se 1 (by rfl) ⟨1488542, by rfl⟩ : syracuseStep 1984723 = 2977085) B2977085
theorem B4465637 : Blo 1983435 4465637 := bbase (se 4 (by rfl) ⟨418653, by rfl⟩ : syracuseStep 4465637 = 837307) (by norm_num)
theorem B2977091 : Blo 1983435 2977091 := bstep (se 1 (by rfl) ⟨2232818, by rfl⟩ : syracuseStep 2977091 = 4465637) B4465637
theorem B1984727 : Blo 1983435 1984727 := bstep (se 1 (by rfl) ⟨1488545, by rfl⟩ : syracuseStep 1984727 = 2977091) B2977091
theorem B5023853 : Blo 1983435 5023853 := bbase (se 3 (by rfl) ⟨941972, by rfl⟩ : syracuseStep 5023853 = 1883945) (by norm_num)
theorem B3349235 : Blo 1983435 3349235 := bstep (se 1 (by rfl) ⟨2511926, by rfl⟩ : syracuseStep 3349235 = 5023853) B5023853
theorem B2232823 : Blo 1983435 2232823 := bstep (se 1 (by rfl) ⟨1674617, by rfl⟩ : syracuseStep 2232823 = 3349235) B3349235
theorem B2977097 : Blo 1983435 2977097 := bstep (se 2 (by rfl) ⟨1116411, by rfl⟩ : syracuseStep 2977097 = 2232823) B2232823
theorem B1984731 : Blo 1983435 1984731 := bstep (se 1 (by rfl) ⟨1488548, by rfl⟩ : syracuseStep 1984731 = 2977097) B2977097
theorem B4238885 : Blo 1983435 4238885 := bbase (se 4 (by rfl) ⟨397395, by rfl⟩ : syracuseStep 4238885 = 794791) (by norm_num)
theorem B2825923 : Blo 1983435 2825923 := bstep (se 1 (by rfl) ⟨2119442, by rfl⟩ : syracuseStep 2825923 = 4238885) B4238885
theorem B3767897 : Blo 1983435 3767897 := bstep (se 2 (by rfl) ⟨1412961, by rfl⟩ : syracuseStep 3767897 = 2825923) B2825923
theorem B10047725 : Blo 1983435 10047725 := bstep (se 3 (by rfl) ⟨1883948, by rfl⟩ : syracuseStep 10047725 = 3767897) B3767897
theorem B6698483 : Blo 1983435 6698483 := bstep (se 1 (by rfl) ⟨5023862, by rfl⟩ : syracuseStep 6698483 = 10047725) B10047725
theorem B4465655 : Blo 1983435 4465655 := bstep (se 1 (by rfl) ⟨3349241, by rfl⟩ : syracuseStep 4465655 = 6698483) B6698483
theorem B2977103 : Blo 1983435 2977103 := bstep (se 1 (by rfl) ⟨2232827, by rfl⟩ : syracuseStep 2977103 = 4465655) B4465655
theorem B1984735 : Blo 1983435 1984735 := bstep (se 1 (by rfl) ⟨1488551, by rfl⟩ : syracuseStep 1984735 = 2977103) B2977103
theorem B2977109 : Blo 1983435 2977109 := bbase (se 11 (by rfl) ⟨2180, by rfl⟩ : syracuseStep 2977109 = 4361) (by norm_num)
theorem B1984739 : Blo 1983435 1984739 := bstep (se 1 (by rfl) ⟨1488554, by rfl⟩ : syracuseStep 1984739 = 2977109) B2977109
theorem B10876117 : Blo 1983435 10876117 := bbase (se 7 (by rfl) ⟨127454, by rfl⟩ : syracuseStep 10876117 = 254909) (by norm_num)
theorem B14501489 : Blo 1983435 14501489 := bstep (se 2 (by rfl) ⟨5438058, by rfl⟩ : syracuseStep 14501489 = 10876117) B10876117
theorem B38670637 : Blo 1983435 38670637 := bstep (se 3 (by rfl) ⟨7250744, by rfl⟩ : syracuseStep 38670637 = 14501489) B14501489
theorem B51560849 : Blo 1983435 51560849 := bstep (se 2 (by rfl) ⟨19335318, by rfl⟩ : syracuseStep 51560849 = 38670637) B38670637
theorem B34373899 : Blo 1983435 34373899 := bstep (se 1 (by rfl) ⟨25780424, by rfl⟩ : syracuseStep 34373899 = 51560849) B51560849
theorem B45831865 : Blo 1983435 45831865 := bstep (se 2 (by rfl) ⟨17186949, by rfl⟩ : syracuseStep 45831865 = 34373899) B34373899
theorem B61109153 : Blo 1983435 61109153 := bstep (se 2 (by rfl) ⟨22915932, by rfl⟩ : syracuseStep 61109153 = 45831865) B45831865
theorem B40739435 : Blo 1983435 40739435 := bstep (se 1 (by rfl) ⟨30554576, by rfl⟩ : syracuseStep 40739435 = 61109153) B61109153
theorem B27159623 : Blo 1983435 27159623 := bstep (se 1 (by rfl) ⟨20369717, by rfl⟩ : syracuseStep 27159623 = 40739435) B40739435
theorem B18106415 : Blo 1983435 18106415 := bstep (se 1 (by rfl) ⟨13579811, by rfl⟩ : syracuseStep 18106415 = 27159623) B27159623
theorem B12070943 : Blo 1983435 12070943 := bstep (se 1 (by rfl) ⟨9053207, by rfl⟩ : syracuseStep 12070943 = 18106415) B18106415
theorem B8047295 : Blo 1983435 8047295 := bstep (se 1 (by rfl) ⟨6035471, by rfl⟩ : syracuseStep 8047295 = 12070943) B12070943
theorem B5364863 : Blo 1983435 5364863 := bstep (se 1 (by rfl) ⟨4023647, by rfl⟩ : syracuseStep 5364863 = 8047295) B8047295
theorem B3576575 : Blo 1983435 3576575 := bstep (se 1 (by rfl) ⟨2682431, by rfl⟩ : syracuseStep 3576575 = 5364863) B5364863
theorem B2384383 : Blo 1983435 2384383 := bstep (se 1 (by rfl) ⟨1788287, by rfl⟩ : syracuseStep 2384383 = 3576575) B3576575
theorem B3179177 : Blo 1983435 3179177 := bstep (se 2 (by rfl) ⟨1192191, by rfl⟩ : syracuseStep 3179177 = 2384383) B2384383
theorem B2119451 : Blo 1983435 2119451 := bstep (se 1 (by rfl) ⟨1589588, by rfl⟩ : syracuseStep 2119451 = 3179177) B3179177
theorem B5651869 : Blo 1983435 5651869 := bstep (se 3 (by rfl) ⟨1059725, by rfl⟩ : syracuseStep 5651869 = 2119451) B2119451
theorem B7535825 : Blo 1983435 7535825 := bstep (se 2 (by rfl) ⟨2825934, by rfl⟩ : syracuseStep 7535825 = 5651869) B5651869
theorem B5023883 : Blo 1983435 5023883 := bstep (se 1 (by rfl) ⟨3767912, by rfl⟩ : syracuseStep 5023883 = 7535825) B7535825
theorem B3349255 : Blo 1983435 3349255 := bstep (se 1 (by rfl) ⟨2511941, by rfl⟩ : syracuseStep 3349255 = 5023883) B5023883
theorem B4465673 : Blo 1983435 4465673 := bstep (se 2 (by rfl) ⟨1674627, by rfl⟩ : syracuseStep 4465673 = 3349255) B3349255
theorem B2977115 : Blo 1983435 2977115 := bstep (se 1 (by rfl) ⟨2232836, by rfl⟩ : syracuseStep 2977115 = 4465673) B4465673
theorem B1984743 : Blo 1983435 1984743 := bstep (se 1 (by rfl) ⟨1488557, by rfl⟩ : syracuseStep 1984743 = 2977115) B2977115
theorem B2232841 : Blo 1983435 2232841 := bbase (se 2 (by rfl) ⟨837315, by rfl⟩ : syracuseStep 2232841 = 1674631) (by norm_num)
theorem B2977121 : Blo 1983435 2977121 := bstep (se 2 (by rfl) ⟨1116420, by rfl⟩ : syracuseStep 2977121 = 2232841) B2232841
theorem B1984747 : Blo 1983435 1984747 := bstep (se 1 (by rfl) ⟨1488560, by rfl⟩ : syracuseStep 1984747 = 2977121) B2977121
theorem B3311101 : Blo 1983435 3311101 := bbase (se 3 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 3311101 = 1241663) (by norm_num)
theorem B17659205 : Blo 1983435 17659205 := bstep (se 4 (by rfl) ⟨1655550, by rfl⟩ : syracuseStep 17659205 = 3311101) B3311101
theorem B11772803 : Blo 1983435 11772803 := bstep (se 1 (by rfl) ⟨8829602, by rfl⟩ : syracuseStep 11772803 = 17659205) B17659205
theorem B7848535 : Blo 1983435 7848535 := bstep (se 1 (by rfl) ⟨5886401, by rfl⟩ : syracuseStep 7848535 = 11772803) B11772803
theorem B10464713 : Blo 1983435 10464713 := bstep (se 2 (by rfl) ⟨3924267, by rfl⟩ : syracuseStep 10464713 = 7848535) B7848535
theorem B6976475 : Blo 1983435 6976475 := bstep (se 1 (by rfl) ⟨5232356, by rfl⟩ : syracuseStep 6976475 = 10464713) B10464713
theorem B4650983 : Blo 1983435 4650983 := bstep (se 1 (by rfl) ⟨3488237, by rfl⟩ : syracuseStep 4650983 = 6976475) B6976475
theorem B3100655 : Blo 1983435 3100655 := bstep (se 1 (by rfl) ⟨2325491, by rfl⟩ : syracuseStep 3100655 = 4650983) B4650983
theorem B2067103 : Blo 1983435 2067103 := bstep (se 1 (by rfl) ⟨1550327, by rfl⟩ : syracuseStep 2067103 = 3100655) B3100655
theorem B11024549 : Blo 1983435 11024549 := bstep (se 4 (by rfl) ⟨1033551, by rfl⟩ : syracuseStep 11024549 = 2067103) B2067103
theorem B7349699 : Blo 1983435 7349699 := bstep (se 1 (by rfl) ⟨5512274, by rfl⟩ : syracuseStep 7349699 = 11024549) B11024549
theorem B4899799 : Blo 1983435 4899799 := bstep (se 1 (by rfl) ⟨3674849, by rfl⟩ : syracuseStep 4899799 = 7349699) B7349699
theorem B6533065 : Blo 1983435 6533065 := bstep (se 2 (by rfl) ⟨2449899, by rfl⟩ : syracuseStep 6533065 = 4899799) B4899799
theorem B8710753 : Blo 1983435 8710753 := bstep (se 2 (by rfl) ⟨3266532, by rfl⟩ : syracuseStep 8710753 = 6533065) B6533065
theorem B11614337 : Blo 1983435 11614337 := bstep (se 2 (by rfl) ⟨4355376, by rfl⟩ : syracuseStep 11614337 = 8710753) B8710753
theorem B7742891 : Blo 1983435 7742891 := bstep (se 1 (by rfl) ⟨5807168, by rfl⟩ : syracuseStep 7742891 = 11614337) B11614337
theorem B20647709 : Blo 1983435 20647709 := bstep (se 3 (by rfl) ⟨3871445, by rfl⟩ : syracuseStep 20647709 = 7742891) B7742891
theorem B13765139 : Blo 1983435 13765139 := bstep (se 1 (by rfl) ⟨10323854, by rfl⟩ : syracuseStep 13765139 = 20647709) B20647709
theorem B9176759 : Blo 1983435 9176759 := bstep (se 1 (by rfl) ⟨6882569, by rfl⟩ : syracuseStep 9176759 = 13765139) B13765139
theorem B6117839 : Blo 1983435 6117839 := bstep (se 1 (by rfl) ⟨4588379, by rfl⟩ : syracuseStep 6117839 = 9176759) B9176759
theorem B4078559 : Blo 1983435 4078559 := bstep (se 1 (by rfl) ⟨3058919, by rfl⟩ : syracuseStep 4078559 = 6117839) B6117839
theorem B10876157 : Blo 1983435 10876157 := bstep (se 3 (by rfl) ⟨2039279, by rfl⟩ : syracuseStep 10876157 = 4078559) B4078559
theorem B7250771 : Blo 1983435 7250771 := bstep (se 1 (by rfl) ⟨5438078, by rfl⟩ : syracuseStep 7250771 = 10876157) B10876157
theorem B4833847 : Blo 1983435 4833847 := bstep (se 1 (by rfl) ⟨3625385, by rfl⟩ : syracuseStep 4833847 = 7250771) B7250771
theorem B6445129 : Blo 1983435 6445129 := bstep (se 2 (by rfl) ⟨2416923, by rfl⟩ : syracuseStep 6445129 = 4833847) B4833847
theorem B8593505 : Blo 1983435 8593505 := bstep (se 2 (by rfl) ⟨3222564, by rfl⟩ : syracuseStep 8593505 = 6445129) B6445129
theorem B5729003 : Blo 1983435 5729003 := bstep (se 1 (by rfl) ⟨4296752, by rfl⟩ : syracuseStep 5729003 = 8593505) B8593505
theorem B3819335 : Blo 1983435 3819335 := bstep (se 1 (by rfl) ⟨2864501, by rfl⟩ : syracuseStep 3819335 = 5729003) B5729003
theorem B40739573 : Blo 1983435 40739573 := bstep (se 5 (by rfl) ⟨1909667, by rfl⟩ : syracuseStep 40739573 = 3819335) B3819335
theorem B27159715 : Blo 1983435 27159715 := bstep (se 1 (by rfl) ⟨20369786, by rfl⟩ : syracuseStep 27159715 = 40739573) B40739573
theorem B144851813 : Blo 1983435 144851813 := bstep (se 4 (by rfl) ⟨13579857, by rfl⟩ : syracuseStep 144851813 = 27159715) B27159715
theorem B96567875 : Blo 1983435 96567875 := bstep (se 1 (by rfl) ⟨72425906, by rfl⟩ : syracuseStep 96567875 = 144851813) B144851813
theorem B64378583 : Blo 1983435 64378583 := bstep (se 1 (by rfl) ⟨48283937, by rfl⟩ : syracuseStep 64378583 = 96567875) B96567875
theorem B42919055 : Blo 1983435 42919055 := bstep (se 1 (by rfl) ⟨32189291, by rfl⟩ : syracuseStep 42919055 = 64378583) B64378583
theorem B28612703 : Blo 1983435 28612703 := bstep (se 1 (by rfl) ⟨21459527, by rfl⟩ : syracuseStep 28612703 = 42919055) B42919055
theorem B19075135 : Blo 1983435 19075135 := bstep (se 1 (by rfl) ⟨14306351, by rfl⟩ : syracuseStep 19075135 = 28612703) B28612703
theorem B25433513 : Blo 1983435 25433513 := bstep (se 2 (by rfl) ⟨9537567, by rfl⟩ : syracuseStep 25433513 = 19075135) B19075135
theorem B16955675 : Blo 1983435 16955675 := bstep (se 1 (by rfl) ⟨12716756, by rfl⟩ : syracuseStep 16955675 = 25433513) B25433513
theorem B11303783 : Blo 1983435 11303783 := bstep (se 1 (by rfl) ⟨8477837, by rfl⟩ : syracuseStep 11303783 = 16955675) B16955675
theorem B7535855 : Blo 1983435 7535855 := bstep (se 1 (by rfl) ⟨5651891, by rfl⟩ : syracuseStep 7535855 = 11303783) B11303783
theorem B5023903 : Blo 1983435 5023903 := bstep (se 1 (by rfl) ⟨3767927, by rfl⟩ : syracuseStep 5023903 = 7535855) B7535855
theorem B6698537 : Blo 1983435 6698537 := bstep (se 2 (by rfl) ⟨2511951, by rfl⟩ : syracuseStep 6698537 = 5023903) B5023903
theorem B4465691 : Blo 1983435 4465691 := bstep (se 1 (by rfl) ⟨3349268, by rfl⟩ : syracuseStep 4465691 = 6698537) B6698537
theorem B2977127 : Blo 1983435 2977127 := bstep (se 1 (by rfl) ⟨2232845, by rfl⟩ : syracuseStep 2977127 = 4465691) B4465691
theorem B1984751 : Blo 1983435 1984751 := bstep (se 1 (by rfl) ⟨1488563, by rfl⟩ : syracuseStep 1984751 = 2977127) B2977127
theorem B2977133 : Blo 1983435 2977133 := bbase (se 3 (by rfl) ⟨558212, by rfl⟩ : syracuseStep 2977133 = 1116425) (by norm_num)
theorem B1984755 : Blo 1983435 1984755 := bstep (se 1 (by rfl) ⟨1488566, by rfl⟩ : syracuseStep 1984755 = 2977133) B2977133
theorem B4465709 : Blo 1983435 4465709 := bbase (se 3 (by rfl) ⟨837320, by rfl⟩ : syracuseStep 4465709 = 1674641) (by norm_num)
theorem B2977139 : Blo 1983435 2977139 := bstep (se 1 (by rfl) ⟨2232854, by rfl⟩ : syracuseStep 2977139 = 4465709) B4465709
theorem B1984759 : Blo 1983435 1984759 := bstep (se 1 (by rfl) ⟨1488569, by rfl⟩ : syracuseStep 1984759 = 2977139) B2977139
theorem B5364917 : Blo 1983435 5364917 := bbase (se 5 (by rfl) ⟨251480, by rfl⟩ : syracuseStep 5364917 = 502961) (by norm_num)
theorem B3576611 : Blo 1983435 3576611 := bstep (se 1 (by rfl) ⟨2682458, by rfl⟩ : syracuseStep 3576611 = 5364917) B5364917
theorem B2384407 : Blo 1983435 2384407 := bstep (se 1 (by rfl) ⟨1788305, by rfl⟩ : syracuseStep 2384407 = 3576611) B3576611
theorem B12716837 : Blo 1983435 12716837 := bstep (se 4 (by rfl) ⟨1192203, by rfl⟩ : syracuseStep 12716837 = 2384407) B2384407
theorem B8477891 : Blo 1983435 8477891 := bstep (se 1 (by rfl) ⟨6358418, by rfl⟩ : syracuseStep 8477891 = 12716837) B12716837
theorem B5651927 : Blo 1983435 5651927 := bstep (se 1 (by rfl) ⟨4238945, by rfl⟩ : syracuseStep 5651927 = 8477891) B8477891
theorem B3767951 : Blo 1983435 3767951 := bstep (se 1 (by rfl) ⟨2825963, by rfl⟩ : syracuseStep 3767951 = 5651927) B5651927
theorem B2511967 : Blo 1983435 2511967 := bstep (se 1 (by rfl) ⟨1883975, by rfl⟩ : syracuseStep 2511967 = 3767951) B3767951
theorem B3349289 : Blo 1983435 3349289 := bstep (se 2 (by rfl) ⟨1255983, by rfl⟩ : syracuseStep 3349289 = 2511967) B2511967
theorem B2232859 : Blo 1983435 2232859 := bstep (se 1 (by rfl) ⟨1674644, by rfl⟩ : syracuseStep 2232859 = 3349289) B3349289
theorem B2977145 : Blo 1983435 2977145 := bstep (se 2 (by rfl) ⟨1116429, by rfl⟩ : syracuseStep 2977145 = 2232859) B2232859
theorem B1984763 : Blo 1983435 1984763 := bstep (se 1 (by rfl) ⟨1488572, by rfl⟩ : syracuseStep 1984763 = 2977145) B2977145
theorem B2546245 : Blo 1983435 2546245 := bbase (se 4 (by rfl) ⟨238710, by rfl⟩ : syracuseStep 2546245 = 477421) (by norm_num)
theorem B13579973 : Blo 1983435 13579973 := bstep (se 4 (by rfl) ⟨1273122, by rfl⟩ : syracuseStep 13579973 = 2546245) B2546245
theorem B9053315 : Blo 1983435 9053315 := bstep (se 1 (by rfl) ⟨6789986, by rfl⟩ : syracuseStep 9053315 = 13579973) B13579973
theorem B6035543 : Blo 1983435 6035543 := bstep (se 1 (by rfl) ⟨4526657, by rfl⟩ : syracuseStep 6035543 = 9053315) B9053315
theorem B4023695 : Blo 1983435 4023695 := bstep (se 1 (by rfl) ⟨3017771, by rfl⟩ : syracuseStep 4023695 = 6035543) B6035543
theorem B2682463 : Blo 1983435 2682463 := bstep (se 1 (by rfl) ⟨2011847, by rfl⟩ : syracuseStep 2682463 = 4023695) B4023695
theorem B3576617 : Blo 1983435 3576617 := bstep (se 2 (by rfl) ⟨1341231, by rfl⟩ : syracuseStep 3576617 = 2682463) B2682463
theorem B2384411 : Blo 1983435 2384411 := bstep (se 1 (by rfl) ⟨1788308, by rfl⟩ : syracuseStep 2384411 = 3576617) B3576617
theorem B6358429 : Blo 1983435 6358429 := bstep (se 3 (by rfl) ⟨1192205, by rfl⟩ : syracuseStep 6358429 = 2384411) B2384411
theorem B33911621 : Blo 1983435 33911621 := bstep (se 4 (by rfl) ⟨3179214, by rfl⟩ : syracuseStep 33911621 = 6358429) B6358429
theorem B22607747 : Blo 1983435 22607747 := bstep (se 1 (by rfl) ⟨16955810, by rfl⟩ : syracuseStep 22607747 = 33911621) B33911621
theorem B15071831 : Blo 1983435 15071831 := bstep (se 1 (by rfl) ⟨11303873, by rfl⟩ : syracuseStep 15071831 = 22607747) B22607747
theorem B10047887 : Blo 1983435 10047887 := bstep (se 1 (by rfl) ⟨7535915, by rfl⟩ : syracuseStep 10047887 = 15071831) B15071831
theorem B6698591 : Blo 1983435 6698591 := bstep (se 1 (by rfl) ⟨5023943, by rfl⟩ : syracuseStep 6698591 = 10047887) B10047887
theorem B4465727 : Blo 1983435 4465727 := bstep (se 1 (by rfl) ⟨3349295, by rfl⟩ : syracuseStep 4465727 = 6698591) B6698591
theorem B2977151 : Blo 1983435 2977151 := bstep (se 1 (by rfl) ⟨2232863, by rfl⟩ : syracuseStep 2977151 = 4465727) B4465727
theorem B1984767 : Blo 1983435 1984767 := bstep (se 1 (by rfl) ⟨1488575, by rfl⟩ : syracuseStep 1984767 = 2977151) B2977151
theorem B2977157 : Blo 1983435 2977157 := bbase (se 4 (by rfl) ⟨279108, by rfl⟩ : syracuseStep 2977157 = 558217) (by norm_num)
theorem B1984771 : Blo 1983435 1984771 := bstep (se 1 (by rfl) ⟨1488578, by rfl⟩ : syracuseStep 1984771 = 2977157) B2977157
theorem B3349309 : Blo 1983435 3349309 := bbase (se 3 (by rfl) ⟨627995, by rfl⟩ : syracuseStep 3349309 = 1255991) (by norm_num)
theorem B4465745 : Blo 1983435 4465745 := bstep (se 2 (by rfl) ⟨1674654, by rfl⟩ : syracuseStep 4465745 = 3349309) B3349309
theorem B2977163 : Blo 1983435 2977163 := bstep (se 1 (by rfl) ⟨2232872, by rfl⟩ : syracuseStep 2977163 = 4465745) B4465745
theorem B1984775 : Blo 1983435 1984775 := bstep (se 1 (by rfl) ⟨1488581, by rfl⟩ : syracuseStep 1984775 = 2977163) B2977163
theorem B2232877 : Blo 1983435 2232877 := bbase (se 3 (by rfl) ⟨418664, by rfl⟩ : syracuseStep 2232877 = 837329) (by norm_num)
theorem B2977169 : Blo 1983435 2977169 := bstep (se 2 (by rfl) ⟨1116438, by rfl⟩ : syracuseStep 2977169 = 2232877) B2232877
theorem B1984779 : Blo 1983435 1984779 := bstep (se 1 (by rfl) ⟨1488584, by rfl⟩ : syracuseStep 1984779 = 2977169) B2977169
theorem B6698645 : Blo 1983435 6698645 := bbase (se 6 (by rfl) ⟨156999, by rfl⟩ : syracuseStep 6698645 = 313999) (by norm_num)
theorem B4465763 : Blo 1983435 4465763 := bstep (se 1 (by rfl) ⟨3349322, by rfl⟩ : syracuseStep 4465763 = 6698645) B6698645
theorem B2977175 : Blo 1983435 2977175 := bstep (se 1 (by rfl) ⟨2232881, by rfl⟩ : syracuseStep 2977175 = 4465763) B4465763
theorem B1984783 : Blo 1983435 1984783 := bstep (se 1 (by rfl) ⟨1488587, by rfl⟩ : syracuseStep 1984783 = 2977175) B2977175
theorem B2977181 : Blo 1983435 2977181 := bbase (se 3 (by rfl) ⟨558221, by rfl⟩ : syracuseStep 2977181 = 1116443) (by norm_num)
theorem B1984787 : Blo 1983435 1984787 := bstep (se 1 (by rfl) ⟨1488590, by rfl⟩ : syracuseStep 1984787 = 2977181) B2977181
theorem B4465781 : Blo 1983435 4465781 := bbase (se 5 (by rfl) ⟨209333, by rfl⟩ : syracuseStep 4465781 = 418667) (by norm_num)
theorem B2977187 : Blo 1983435 2977187 := bstep (se 1 (by rfl) ⟨2232890, by rfl⟩ : syracuseStep 2977187 = 4465781) B4465781
theorem B1984791 : Blo 1983435 1984791 := bstep (se 1 (by rfl) ⟨1488593, by rfl⟩ : syracuseStep 1984791 = 2977187) B2977187
theorem B16956053 : Blo 1983435 16956053 := bbase (se 6 (by rfl) ⟨397407, by rfl⟩ : syracuseStep 16956053 = 794815) (by norm_num)
theorem B11304035 : Blo 1983435 11304035 := bstep (se 1 (by rfl) ⟨8478026, by rfl⟩ : syracuseStep 11304035 = 16956053) B16956053
theorem B7536023 : Blo 1983435 7536023 := bstep (se 1 (by rfl) ⟨5652017, by rfl⟩ : syracuseStep 7536023 = 11304035) B11304035
theorem B5024015 : Blo 1983435 5024015 := bstep (se 1 (by rfl) ⟨3768011, by rfl⟩ : syracuseStep 5024015 = 7536023) B7536023
theorem B3349343 : Blo 1983435 3349343 := bstep (se 1 (by rfl) ⟨2512007, by rfl⟩ : syracuseStep 3349343 = 5024015) B5024015
theorem B2232895 : Blo 1983435 2232895 := bstep (se 1 (by rfl) ⟨1674671, by rfl⟩ : syracuseStep 2232895 = 3349343) B3349343
theorem B2977193 : Blo 1983435 2977193 := bstep (se 2 (by rfl) ⟨1116447, by rfl⟩ : syracuseStep 2977193 = 2232895) B2232895
theorem B1984795 : Blo 1983435 1984795 := bstep (se 1 (by rfl) ⟨1488596, by rfl⟩ : syracuseStep 1984795 = 2977193) B2977193
theorem B7536037 : Blo 1983435 7536037 := bbase (se 4 (by rfl) ⟨706503, by rfl⟩ : syracuseStep 7536037 = 1413007) (by norm_num)
theorem B10048049 : Blo 1983435 10048049 := bstep (se 2 (by rfl) ⟨3768018, by rfl⟩ : syracuseStep 10048049 = 7536037) B7536037
theorem B6698699 : Blo 1983435 6698699 := bstep (se 1 (by rfl) ⟨5024024, by rfl⟩ : syracuseStep 6698699 = 10048049) B10048049
theorem B4465799 : Blo 1983435 4465799 := bstep (se 1 (by rfl) ⟨3349349, by rfl⟩ : syracuseStep 4465799 = 6698699) B6698699
theorem B2977199 : Blo 1983435 2977199 := bstep (se 1 (by rfl) ⟨2232899, by rfl⟩ : syracuseStep 2977199 = 4465799) B4465799
theorem B1984799 : Blo 1983435 1984799 := bstep (se 1 (by rfl) ⟨1488599, by rfl⟩ : syracuseStep 1984799 = 2977199) B2977199
theorem B2977205 : Blo 1983435 2977205 := bbase (se 5 (by rfl) ⟨139556, by rfl⟩ : syracuseStep 2977205 = 279113) (by norm_num)
theorem B1984803 : Blo 1983435 1984803 := bstep (se 1 (by rfl) ⟨1488602, by rfl⟩ : syracuseStep 1984803 = 2977205) B2977205
theorem B5024045 : Blo 1983435 5024045 := bbase (se 3 (by rfl) ⟨942008, by rfl⟩ : syracuseStep 5024045 = 1884017) (by norm_num)
theorem B3349363 : Blo 1983435 3349363 := bstep (se 1 (by rfl) ⟨2512022, by rfl⟩ : syracuseStep 3349363 = 5024045) B5024045
theorem B4465817 : Blo 1983435 4465817 := bstep (se 2 (by rfl) ⟨1674681, by rfl⟩ : syracuseStep 4465817 = 3349363) B3349363
theorem B2977211 : Blo 1983435 2977211 := bstep (se 1 (by rfl) ⟨2232908, by rfl⟩ : syracuseStep 2977211 = 4465817) B4465817
theorem B1984807 : Blo 1983435 1984807 := bstep (se 1 (by rfl) ⟨1488605, by rfl⟩ : syracuseStep 1984807 = 2977211) B2977211
theorem B2232913 : Blo 1983435 2232913 := bbase (se 2 (by rfl) ⟨837342, by rfl⟩ : syracuseStep 2232913 = 1674685) (by norm_num)
theorem B2977217 : Blo 1983435 2977217 := bstep (se 2 (by rfl) ⟨1116456, by rfl⟩ : syracuseStep 2977217 = 2232913) B2232913
theorem B1984811 : Blo 1983435 1984811 := bstep (se 1 (by rfl) ⟨1488608, by rfl⟩ : syracuseStep 1984811 = 2977217) B2977217
theorem B2826037 : Blo 1983435 2826037 := bbase (se 5 (by rfl) ⟨132470, by rfl⟩ : syracuseStep 2826037 = 264941) (by norm_num)
theorem B3768049 : Blo 1983435 3768049 := bstep (se 2 (by rfl) ⟨1413018, by rfl⟩ : syracuseStep 3768049 = 2826037) B2826037
theorem B5024065 : Blo 1983435 5024065 := bstep (se 2 (by rfl) ⟨1884024, by rfl⟩ : syracuseStep 5024065 = 3768049) B3768049
theorem B6698753 : Blo 1983435 6698753 := bstep (se 2 (by rfl) ⟨2512032, by rfl⟩ : syracuseStep 6698753 = 5024065) B5024065
theorem B4465835 : Blo 1983435 4465835 := bstep (se 1 (by rfl) ⟨3349376, by rfl⟩ : syracuseStep 4465835 = 6698753) B6698753
theorem B2977223 : Blo 1983435 2977223 := bstep (se 1 (by rfl) ⟨2232917, by rfl⟩ : syracuseStep 2977223 = 4465835) B4465835
theorem B1984815 : Blo 1983435 1984815 := bstep (se 1 (by rfl) ⟨1488611, by rfl⟩ : syracuseStep 1984815 = 2977223) B2977223
theorem B2977229 : Blo 1983435 2977229 := bbase (se 3 (by rfl) ⟨558230, by rfl⟩ : syracuseStep 2977229 = 1116461) (by norm_num)
theorem B1984819 : Blo 1983435 1984819 := bstep (se 1 (by rfl) ⟨1488614, by rfl⟩ : syracuseStep 1984819 = 2977229) B2977229
theorem B4465853 : Blo 1983435 4465853 := bbase (se 3 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 4465853 = 1674695) (by norm_num)
theorem B2977235 : Blo 1983435 2977235 := bstep (se 1 (by rfl) ⟨2232926, by rfl⟩ : syracuseStep 2977235 = 4465853) B4465853
theorem B1984823 : Blo 1983435 1984823 := bstep (se 1 (by rfl) ⟨1488617, by rfl⟩ : syracuseStep 1984823 = 2977235) B2977235
theorem B3349397 : Blo 1983435 3349397 := bbase (se 6 (by rfl) ⟨78501, by rfl⟩ : syracuseStep 3349397 = 157003) (by norm_num)
theorem B2232931 : Blo 1983435 2232931 := bstep (se 1 (by rfl) ⟨1674698, by rfl⟩ : syracuseStep 2232931 = 3349397) B3349397
theorem B2977241 : Blo 1983435 2977241 := bstep (se 2 (by rfl) ⟨1116465, by rfl⟩ : syracuseStep 2977241 = 2232931) B2232931
theorem B1984827 : Blo 1983435 1984827 := bstep (se 1 (by rfl) ⟨1488620, by rfl⟩ : syracuseStep 1984827 = 2977241) B2977241
theorem B12717269 : Blo 1983435 12717269 := bbase (se 7 (by rfl) ⟨149030, by rfl⟩ : syracuseStep 12717269 = 298061) (by norm_num)
theorem B8478179 : Blo 1983435 8478179 := bstep (se 1 (by rfl) ⟨6358634, by rfl⟩ : syracuseStep 8478179 = 12717269) B12717269
theorem B5652119 : Blo 1983435 5652119 := bstep (se 1 (by rfl) ⟨4239089, by rfl⟩ : syracuseStep 5652119 = 8478179) B8478179
theorem B15072317 : Blo 1983435 15072317 := bstep (se 3 (by rfl) ⟨2826059, by rfl⟩ : syracuseStep 15072317 = 5652119) B5652119
theorem B10048211 : Blo 1983435 10048211 := bstep (se 1 (by rfl) ⟨7536158, by rfl⟩ : syracuseStep 10048211 = 15072317) B15072317
theorem B6698807 : Blo 1983435 6698807 := bstep (se 1 (by rfl) ⟨5024105, by rfl⟩ : syracuseStep 6698807 = 10048211) B10048211
theorem B4465871 : Blo 1983435 4465871 := bstep (se 1 (by rfl) ⟨3349403, by rfl⟩ : syracuseStep 4465871 = 6698807) B6698807
theorem B2977247 : Blo 1983435 2977247 := bstep (se 1 (by rfl) ⟨2232935, by rfl⟩ : syracuseStep 2977247 = 4465871) B4465871
theorem B1984831 : Blo 1983435 1984831 := bstep (se 1 (by rfl) ⟨1488623, by rfl⟩ : syracuseStep 1984831 = 2977247) B2977247
theorem B2977253 : Blo 1983435 2977253 := bbase (se 4 (by rfl) ⟨279117, by rfl⟩ : syracuseStep 2977253 = 558235) (by norm_num)
theorem B1984835 : Blo 1983435 1984835 := bstep (se 1 (by rfl) ⟨1488626, by rfl⟩ : syracuseStep 1984835 = 2977253) B2977253
theorem B3395117 : Blo 1983435 3395117 := bbase (se 3 (by rfl) ⟨636584, by rfl⟩ : syracuseStep 3395117 = 1273169) (by norm_num)
theorem B2263411 : Blo 1983435 2263411 := bstep (se 1 (by rfl) ⟨1697558, by rfl⟩ : syracuseStep 2263411 = 3395117) B3395117
theorem B3017881 : Blo 1983435 3017881 := bstep (se 2 (by rfl) ⟨1131705, by rfl⟩ : syracuseStep 3017881 = 2263411) B2263411
theorem B4023841 : Blo 1983435 4023841 := bstep (se 2 (by rfl) ⟨1508940, by rfl⟩ : syracuseStep 4023841 = 3017881) B3017881
theorem B5365121 : Blo 1983435 5365121 := bstep (se 2 (by rfl) ⟨2011920, by rfl⟩ : syracuseStep 5365121 = 4023841) B4023841
theorem B14306989 : Blo 1983435 14306989 := bstep (se 3 (by rfl) ⟨2682560, by rfl⟩ : syracuseStep 14306989 = 5365121) B5365121
theorem B19075985 : Blo 1983435 19075985 := bstep (se 2 (by rfl) ⟨7153494, by rfl⟩ : syracuseStep 19075985 = 14306989) B14306989
theorem B12717323 : Blo 1983435 12717323 := bstep (se 1 (by rfl) ⟨9537992, by rfl⟩ : syracuseStep 12717323 = 19075985) B19075985
theorem B8478215 : Blo 1983435 8478215 := bstep (se 1 (by rfl) ⟨6358661, by rfl⟩ : syracuseStep 8478215 = 12717323) B12717323
theorem B5652143 : Blo 1983435 5652143 := bstep (se 1 (by rfl) ⟨4239107, by rfl⟩ : syracuseStep 5652143 = 8478215) B8478215
theorem B3768095 : Blo 1983435 3768095 := bstep (se 1 (by rfl) ⟨2826071, by rfl⟩ : syracuseStep 3768095 = 5652143) B5652143
theorem B2512063 : Blo 1983435 2512063 := bstep (se 1 (by rfl) ⟨1884047, by rfl⟩ : syracuseStep 2512063 = 3768095) B3768095
theorem B3349417 : Blo 1983435 3349417 := bstep (se 2 (by rfl) ⟨1256031, by rfl⟩ : syracuseStep 3349417 = 2512063) B2512063
theorem B4465889 : Blo 1983435 4465889 := bstep (se 2 (by rfl) ⟨1674708, by rfl⟩ : syracuseStep 4465889 = 3349417) B3349417
theorem B2977259 : Blo 1983435 2977259 := bstep (se 1 (by rfl) ⟨2232944, by rfl⟩ : syracuseStep 2977259 = 4465889) B4465889
theorem B1984839 : Blo 1983435 1984839 := bstep (se 1 (by rfl) ⟨1488629, by rfl⟩ : syracuseStep 1984839 = 2977259) B2977259
theorem B2232949 : Blo 1983435 2232949 := bbase (se 5 (by rfl) ⟨104669, by rfl⟩ : syracuseStep 2232949 = 209339) (by norm_num)
theorem B2977265 : Blo 1983435 2977265 := bstep (se 2 (by rfl) ⟨1116474, by rfl⟩ : syracuseStep 2977265 = 2232949) B2232949
theorem B1984843 : Blo 1983435 1984843 := bstep (se 1 (by rfl) ⟨1488632, by rfl⟩ : syracuseStep 1984843 = 2977265) B2977265
theorem B2512073 : Blo 1983435 2512073 := bbase (se 2 (by rfl) ⟨942027, by rfl⟩ : syracuseStep 2512073 = 1884055) (by norm_num)
theorem B6698861 : Blo 1983435 6698861 := bstep (se 3 (by rfl) ⟨1256036, by rfl⟩ : syracuseStep 6698861 = 2512073) B2512073
theorem B4465907 : Blo 1983435 4465907 := bstep (se 1 (by rfl) ⟨3349430, by rfl⟩ : syracuseStep 4465907 = 6698861) B6698861
theorem B2977271 : Blo 1983435 2977271 := bstep (se 1 (by rfl) ⟨2232953, by rfl⟩ : syracuseStep 2977271 = 4465907) B4465907
theorem B1984847 : Blo 1983435 1984847 := bstep (se 1 (by rfl) ⟨1488635, by rfl⟩ : syracuseStep 1984847 = 2977271) B2977271
theorem B2977277 : Blo 1983435 2977277 := bbase (se 3 (by rfl) ⟨558239, by rfl⟩ : syracuseStep 2977277 = 1116479) (by norm_num)
theorem B1984851 : Blo 1983435 1984851 := bstep (se 1 (by rfl) ⟨1488638, by rfl⟩ : syracuseStep 1984851 = 2977277) B2977277
theorem B4465925 : Blo 1983435 4465925 := bbase (se 4 (by rfl) ⟨418680, by rfl⟩ : syracuseStep 4465925 = 837361) (by norm_num)
theorem B2977283 : Blo 1983435 2977283 := bstep (se 1 (by rfl) ⟨2232962, by rfl⟩ : syracuseStep 2977283 = 4465925) B4465925
theorem B1984855 : Blo 1983435 1984855 := bstep (se 1 (by rfl) ⟨1488641, by rfl⟩ : syracuseStep 1984855 = 2977283) B2977283
theorem B3768133 : Blo 1983435 3768133 := bbase (se 4 (by rfl) ⟨353262, by rfl⟩ : syracuseStep 3768133 = 706525) (by norm_num)
theorem B5024177 : Blo 1983435 5024177 := bstep (se 2 (by rfl) ⟨1884066, by rfl⟩ : syracuseStep 5024177 = 3768133) B3768133
theorem B3349451 : Blo 1983435 3349451 := bstep (se 1 (by rfl) ⟨2512088, by rfl⟩ : syracuseStep 3349451 = 5024177) B5024177
theorem B2232967 : Blo 1983435 2232967 := bstep (se 1 (by rfl) ⟨1674725, by rfl⟩ : syracuseStep 2232967 = 3349451) B3349451
theorem B2977289 : Blo 1983435 2977289 := bstep (se 2 (by rfl) ⟨1116483, by rfl⟩ : syracuseStep 2977289 = 2232967) B2232967
theorem B1984859 : Blo 1983435 1984859 := bstep (se 1 (by rfl) ⟨1488644, by rfl⟩ : syracuseStep 1984859 = 2977289) B2977289
theorem B10048373 : Blo 1983435 10048373 := bbase (se 5 (by rfl) ⟨471017, by rfl⟩ : syracuseStep 10048373 = 942035) (by norm_num)
theorem B6698915 : Blo 1983435 6698915 := bstep (se 1 (by rfl) ⟨5024186, by rfl⟩ : syracuseStep 6698915 = 10048373) B10048373
theorem B4465943 : Blo 1983435 4465943 := bstep (se 1 (by rfl) ⟨3349457, by rfl⟩ : syracuseStep 4465943 = 6698915) B6698915
theorem B2977295 : Blo 1983435 2977295 := bstep (se 1 (by rfl) ⟨2232971, by rfl⟩ : syracuseStep 2977295 = 4465943) B4465943
theorem B1984863 : Blo 1983435 1984863 := bstep (se 1 (by rfl) ⟨1488647, by rfl⟩ : syracuseStep 1984863 = 2977295) B2977295
theorem B2977301 : Blo 1983435 2977301 := bbase (se 6 (by rfl) ⟨69780, by rfl⟩ : syracuseStep 2977301 = 139561) (by norm_num)
theorem B1984867 : Blo 1983435 1984867 := bstep (se 1 (by rfl) ⟨1488650, by rfl⟩ : syracuseStep 1984867 = 2977301) B2977301
theorem B5092757 : Blo 1983435 5092757 := bbase (se 6 (by rfl) ⟨119361, by rfl⟩ : syracuseStep 5092757 = 238723) (by norm_num)
theorem B3395171 : Blo 1983435 3395171 := bstep (se 1 (by rfl) ⟨2546378, by rfl⟩ : syracuseStep 3395171 = 5092757) B5092757
theorem B2263447 : Blo 1983435 2263447 := bstep (se 1 (by rfl) ⟨1697585, by rfl⟩ : syracuseStep 2263447 = 3395171) B3395171
theorem B12071717 : Blo 1983435 12071717 := bstep (se 4 (by rfl) ⟨1131723, by rfl⟩ : syracuseStep 12071717 = 2263447) B2263447
theorem B8047811 : Blo 1983435 8047811 := bstep (se 1 (by rfl) ⟨6035858, by rfl⟩ : syracuseStep 8047811 = 12071717) B12071717
theorem B5365207 : Blo 1983435 5365207 := bstep (se 1 (by rfl) ⟨4023905, by rfl⟩ : syracuseStep 5365207 = 8047811) B8047811
theorem B7153609 : Blo 1983435 7153609 := bstep (se 2 (by rfl) ⟨2682603, by rfl⟩ : syracuseStep 7153609 = 5365207) B5365207
theorem B9538145 : Blo 1983435 9538145 := bstep (se 2 (by rfl) ⟨3576804, by rfl⟩ : syracuseStep 9538145 = 7153609) B7153609
theorem B6358763 : Blo 1983435 6358763 := bstep (se 1 (by rfl) ⟨4769072, by rfl⟩ : syracuseStep 6358763 = 9538145) B9538145
theorem B16956701 : Blo 1983435 16956701 := bstep (se 3 (by rfl) ⟨3179381, by rfl⟩ : syracuseStep 16956701 = 6358763) B6358763
theorem B11304467 : Blo 1983435 11304467 := bstep (se 1 (by rfl) ⟨8478350, by rfl⟩ : syracuseStep 11304467 = 16956701) B16956701
theorem B7536311 : Blo 1983435 7536311 := bstep (se 1 (by rfl) ⟨5652233, by rfl⟩ : syracuseStep 7536311 = 11304467) B11304467
theorem B5024207 : Blo 1983435 5024207 := bstep (se 1 (by rfl) ⟨3768155, by rfl⟩ : syracuseStep 5024207 = 7536311) B7536311
theorem B3349471 : Blo 1983435 3349471 := bstep (se 1 (by rfl) ⟨2512103, by rfl⟩ : syracuseStep 3349471 = 5024207) B5024207
theorem B4465961 : Blo 1983435 4465961 := bstep (se 2 (by rfl) ⟨1674735, by rfl⟩ : syracuseStep 4465961 = 3349471) B3349471
theorem B2977307 : Blo 1983435 2977307 := bstep (se 1 (by rfl) ⟨2232980, by rfl⟩ : syracuseStep 2977307 = 4465961) B4465961
theorem B1984871 : Blo 1983435 1984871 := bstep (se 1 (by rfl) ⟨1488653, by rfl⟩ : syracuseStep 1984871 = 2977307) B2977307
theorem B2232985 : Blo 1983435 2232985 := bbase (se 2 (by rfl) ⟨837369, by rfl⟩ : syracuseStep 2232985 = 1674739) (by norm_num)
theorem B2977313 : Blo 1983435 2977313 := bstep (se 2 (by rfl) ⟨1116492, by rfl⟩ : syracuseStep 2977313 = 2232985) B2232985
theorem B1984875 : Blo 1983435 1984875 := bstep (se 1 (by rfl) ⟨1488656, by rfl⟩ : syracuseStep 1984875 = 2977313) B2977313
theorem B7536341 : Blo 1983435 7536341 := bbase (se 7 (by rfl) ⟨88316, by rfl⟩ : syracuseStep 7536341 = 176633) (by norm_num)
theorem B5024227 : Blo 1983435 5024227 := bstep (se 1 (by rfl) ⟨3768170, by rfl⟩ : syracuseStep 5024227 = 7536341) B7536341
theorem B6698969 : Blo 1983435 6698969 := bstep (se 2 (by rfl) ⟨2512113, by rfl⟩ : syracuseStep 6698969 = 5024227) B5024227
theorem B4465979 : Blo 1983435 4465979 := bstep (se 1 (by rfl) ⟨3349484, by rfl⟩ : syracuseStep 4465979 = 6698969) B6698969
theorem B2977319 : Blo 1983435 2977319 := bstep (se 1 (by rfl) ⟨2232989, by rfl⟩ : syracuseStep 2977319 = 4465979) B4465979
theorem B1984879 : Blo 1983435 1984879 := bstep (se 1 (by rfl) ⟨1488659, by rfl⟩ : syracuseStep 1984879 = 2977319) B2977319
theorem B2977325 : Blo 1983435 2977325 := bbase (se 3 (by rfl) ⟨558248, by rfl⟩ : syracuseStep 2977325 = 1116497) (by norm_num)
theorem B1984883 : Blo 1983435 1984883 := bstep (se 1 (by rfl) ⟨1488662, by rfl⟩ : syracuseStep 1984883 = 2977325) B2977325
theorem B4465997 : Blo 1983435 4465997 := bbase (se 3 (by rfl) ⟨837374, by rfl⟩ : syracuseStep 4465997 = 1674749) (by norm_num)
theorem B2977331 : Blo 1983435 2977331 := bstep (se 1 (by rfl) ⟨2232998, by rfl⟩ : syracuseStep 2977331 = 4465997) B4465997
theorem B1984887 : Blo 1983435 1984887 := bstep (se 1 (by rfl) ⟨1488665, by rfl⟩ : syracuseStep 1984887 = 2977331) B2977331
theorem B2512129 : Blo 1983435 2512129 := bbase (se 2 (by rfl) ⟨942048, by rfl⟩ : syracuseStep 2512129 = 1884097) (by norm_num)
theorem B3349505 : Blo 1983435 3349505 := bstep (se 2 (by rfl) ⟨1256064, by rfl⟩ : syracuseStep 3349505 = 2512129) B2512129
theorem B2233003 : Blo 1983435 2233003 := bstep (se 1 (by rfl) ⟨1674752, by rfl⟩ : syracuseStep 2233003 = 3349505) B3349505
theorem B2977337 : Blo 1983435 2977337 := bstep (se 2 (by rfl) ⟨1116501, by rfl⟩ : syracuseStep 2977337 = 2233003) B2233003
theorem B1984891 : Blo 1983435 1984891 := bstep (se 1 (by rfl) ⟨1488668, by rfl⟩ : syracuseStep 1984891 = 2977337) B2977337
theorem B2119613 : Blo 1983435 2119613 := bbase (se 3 (by rfl) ⟨397427, by rfl⟩ : syracuseStep 2119613 = 794855) (by norm_num)
theorem B22609205 : Blo 1983435 22609205 := bstep (se 5 (by rfl) ⟨1059806, by rfl⟩ : syracuseStep 22609205 = 2119613) B2119613
theorem B15072803 : Blo 1983435 15072803 := bstep (se 1 (by rfl) ⟨11304602, by rfl⟩ : syracuseStep 15072803 = 22609205) B22609205
theorem B10048535 : Blo 1983435 10048535 := bstep (se 1 (by rfl) ⟨7536401, by rfl⟩ : syracuseStep 10048535 = 15072803) B15072803
theorem B6699023 : Blo 1983435 6699023 := bstep (se 1 (by rfl) ⟨5024267, by rfl⟩ : syracuseStep 6699023 = 10048535) B10048535
theorem B4466015 : Blo 1983435 4466015 := bstep (se 1 (by rfl) ⟨3349511, by rfl⟩ : syracuseStep 4466015 = 6699023) B6699023
theorem B2977343 : Blo 1983435 2977343 := bstep (se 1 (by rfl) ⟨2233007, by rfl⟩ : syracuseStep 2977343 = 4466015) B4466015
theorem B1984895 : Blo 1983435 1984895 := bstep (se 1 (by rfl) ⟨1488671, by rfl⟩ : syracuseStep 1984895 = 2977343) B2977343
theorem B2977349 : Blo 1983435 2977349 := bbase (se 4 (by rfl) ⟨279126, by rfl⟩ : syracuseStep 2977349 = 558253) (by norm_num)
theorem B1984899 : Blo 1983435 1984899 := bstep (se 1 (by rfl) ⟨1488674, by rfl⟩ : syracuseStep 1984899 = 2977349) B2977349
theorem B3349525 : Blo 1983435 3349525 := bbase (se 6 (by rfl) ⟨78504, by rfl⟩ : syracuseStep 3349525 = 157009) (by norm_num)
theorem B4466033 : Blo 1983435 4466033 := bstep (se 2 (by rfl) ⟨1674762, by rfl⟩ : syracuseStep 4466033 = 3349525) B3349525
theorem B2977355 : Blo 1983435 2977355 := bstep (se 1 (by rfl) ⟨2233016, by rfl⟩ : syracuseStep 2977355 = 4466033) B4466033
theorem B1984903 : Blo 1983435 1984903 := bstep (se 1 (by rfl) ⟨1488677, by rfl⟩ : syracuseStep 1984903 = 2977355) B2977355
theorem B2233021 : Blo 1983435 2233021 := bbase (se 3 (by rfl) ⟨418691, by rfl⟩ : syracuseStep 2233021 = 837383) (by norm_num)
theorem B2977361 : Blo 1983435 2977361 := bstep (se 2 (by rfl) ⟨1116510, by rfl⟩ : syracuseStep 2977361 = 2233021) B2233021
theorem B1984907 : Blo 1983435 1984907 := bstep (se 1 (by rfl) ⟨1488680, by rfl⟩ : syracuseStep 1984907 = 2977361) B2977361
theorem B6699077 : Blo 1983435 6699077 := bbase (se 4 (by rfl) ⟨628038, by rfl⟩ : syracuseStep 6699077 = 1256077) (by norm_num)
theorem B4466051 : Blo 1983435 4466051 := bstep (se 1 (by rfl) ⟨3349538, by rfl⟩ : syracuseStep 4466051 = 6699077) B6699077
theorem B2977367 : Blo 1983435 2977367 := bstep (se 1 (by rfl) ⟨2233025, by rfl⟩ : syracuseStep 2977367 = 4466051) B4466051
theorem B1984911 : Blo 1983435 1984911 := bstep (se 1 (by rfl) ⟨1488683, by rfl⟩ : syracuseStep 1984911 = 2977367) B2977367
theorem B2977373 : Blo 1983435 2977373 := bbase (se 3 (by rfl) ⟨558257, by rfl⟩ : syracuseStep 2977373 = 1116515) (by norm_num)
theorem B1984915 : Blo 1983435 1984915 := bstep (se 1 (by rfl) ⟨1488686, by rfl⟩ : syracuseStep 1984915 = 2977373) B2977373
theorem B4466069 : Blo 1983435 4466069 := bbase (se 6 (by rfl) ⟨104673, by rfl⟩ : syracuseStep 4466069 = 209347) (by norm_num)
theorem B2977379 : Blo 1983435 2977379 := bstep (se 1 (by rfl) ⟨2233034, by rfl⟩ : syracuseStep 2977379 = 4466069) B4466069
theorem B1984919 : Blo 1983435 1984919 := bstep (se 1 (by rfl) ⟨1488689, by rfl⟩ : syracuseStep 1984919 = 2977379) B2977379
theorem B5365349 : Blo 1983435 5365349 := bbase (se 4 (by rfl) ⟨503001, by rfl⟩ : syracuseStep 5365349 = 1006003) (by norm_num)
theorem B3576899 : Blo 1983435 3576899 := bstep (se 1 (by rfl) ⟨2682674, by rfl⟩ : syracuseStep 3576899 = 5365349) B5365349
theorem B9538397 : Blo 1983435 9538397 := bstep (se 3 (by rfl) ⟨1788449, by rfl⟩ : syracuseStep 9538397 = 3576899) B3576899
theorem B6358931 : Blo 1983435 6358931 := bstep (se 1 (by rfl) ⟨4769198, by rfl⟩ : syracuseStep 6358931 = 9538397) B9538397
theorem B4239287 : Blo 1983435 4239287 := bstep (se 1 (by rfl) ⟨3179465, by rfl⟩ : syracuseStep 4239287 = 6358931) B6358931
theorem B2826191 : Blo 1983435 2826191 := bstep (se 1 (by rfl) ⟨2119643, by rfl⟩ : syracuseStep 2826191 = 4239287) B4239287
theorem B7536509 : Blo 1983435 7536509 := bstep (se 3 (by rfl) ⟨1413095, by rfl⟩ : syracuseStep 7536509 = 2826191) B2826191
theorem B5024339 : Blo 1983435 5024339 := bstep (se 1 (by rfl) ⟨3768254, by rfl⟩ : syracuseStep 5024339 = 7536509) B7536509
theorem B3349559 : Blo 1983435 3349559 := bstep (se 1 (by rfl) ⟨2512169, by rfl⟩ : syracuseStep 3349559 = 5024339) B5024339
theorem B2233039 : Blo 1983435 2233039 := bstep (se 1 (by rfl) ⟨1674779, by rfl⟩ : syracuseStep 2233039 = 3349559) B3349559
theorem B2977385 : Blo 1983435 2977385 := bstep (se 2 (by rfl) ⟨1116519, by rfl⟩ : syracuseStep 2977385 = 2233039) B2233039
theorem B1984923 : Blo 1983435 1984923 := bstep (se 1 (by rfl) ⟨1488692, by rfl⟩ : syracuseStep 1984923 = 2977385) B2977385
theorem B5092901 : Blo 1983435 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B3395267 : Blo 1983435 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B2263511 : Blo 1983435 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B6036029 : Blo 1983435 6036029 := bstep (se 3 (by rfl) ⟨1131755, by rfl⟩ : syracuseStep 6036029 = 2263511) B2263511
theorem B4024019 : Blo 1983435 4024019 := bstep (se 1 (by rfl) ⟨3018014, by rfl⟩ : syracuseStep 4024019 = 6036029) B6036029
theorem B10730717 : Blo 1983435 10730717 := bstep (se 3 (by rfl) ⟨2012009, by rfl⟩ : syracuseStep 10730717 = 4024019) B4024019
theorem B7153811 : Blo 1983435 7153811 := bstep (se 1 (by rfl) ⟨5365358, by rfl⟩ : syracuseStep 7153811 = 10730717) B10730717
theorem B4769207 : Blo 1983435 4769207 := bstep (se 1 (by rfl) ⟨3576905, by rfl⟩ : syracuseStep 4769207 = 7153811) B7153811
theorem B3179471 : Blo 1983435 3179471 := bstep (se 1 (by rfl) ⟨2384603, by rfl⟩ : syracuseStep 3179471 = 4769207) B4769207
theorem B8478589 : Blo 1983435 8478589 := bstep (se 3 (by rfl) ⟨1589735, by rfl⟩ : syracuseStep 8478589 = 3179471) B3179471
theorem B11304785 : Blo 1983435 11304785 := bstep (se 2 (by rfl) ⟨4239294, by rfl⟩ : syracuseStep 11304785 = 8478589) B8478589
theorem B7536523 : Blo 1983435 7536523 := bstep (se 1 (by rfl) ⟨5652392, by rfl⟩ : syracuseStep 7536523 = 11304785) B11304785
theorem B10048697 : Blo 1983435 10048697 := bstep (se 2 (by rfl) ⟨3768261, by rfl⟩ : syracuseStep 10048697 = 7536523) B7536523
theorem B6699131 : Blo 1983435 6699131 := bstep (se 1 (by rfl) ⟨5024348, by rfl⟩ : syracuseStep 6699131 = 10048697) B10048697
theorem B4466087 : Blo 1983435 4466087 := bstep (se 1 (by rfl) ⟨3349565, by rfl⟩ : syracuseStep 4466087 = 6699131) B6699131
theorem B2977391 : Blo 1983435 2977391 := bstep (se 1 (by rfl) ⟨2233043, by rfl⟩ : syracuseStep 2977391 = 4466087) B4466087
theorem B1984927 : Blo 1983435 1984927 := bstep (se 1 (by rfl) ⟨1488695, by rfl⟩ : syracuseStep 1984927 = 2977391) B2977391
theorem B2977397 : Blo 1983435 2977397 := bbase (se 5 (by rfl) ⟨139565, by rfl⟩ : syracuseStep 2977397 = 279131) (by norm_num)
theorem B1984931 : Blo 1983435 1984931 := bstep (se 1 (by rfl) ⟨1488698, by rfl⟩ : syracuseStep 1984931 = 2977397) B2977397
theorem B3768277 : Blo 1983435 3768277 := bbase (se 7 (by rfl) ⟨44159, by rfl⟩ : syracuseStep 3768277 = 88319) (by norm_num)
theorem B5024369 : Blo 1983435 5024369 := bstep (se 2 (by rfl) ⟨1884138, by rfl⟩ : syracuseStep 5024369 = 3768277) B3768277
theorem B3349579 : Blo 1983435 3349579 := bstep (se 1 (by rfl) ⟨2512184, by rfl⟩ : syracuseStep 3349579 = 5024369) B5024369
theorem B4466105 : Blo 1983435 4466105 := bstep (se 2 (by rfl) ⟨1674789, by rfl⟩ : syracuseStep 4466105 = 3349579) B3349579
theorem B2977403 : Blo 1983435 2977403 := bstep (se 1 (by rfl) ⟨2233052, by rfl⟩ : syracuseStep 2977403 = 4466105) B4466105
theorem B1984935 : Blo 1983435 1984935 := bstep (se 1 (by rfl) ⟨1488701, by rfl⟩ : syracuseStep 1984935 = 2977403) B2977403
theorem B2233057 : Blo 1983435 2233057 := bbase (se 2 (by rfl) ⟨837396, by rfl⟩ : syracuseStep 2233057 = 1674793) (by norm_num)
theorem B2977409 : Blo 1983435 2977409 := bstep (se 2 (by rfl) ⟨1116528, by rfl⟩ : syracuseStep 2977409 = 2233057) B2233057
theorem B1984939 : Blo 1983435 1984939 := bstep (se 1 (by rfl) ⟨1488704, by rfl⟩ : syracuseStep 1984939 = 2977409) B2977409
theorem B5024389 : Blo 1983435 5024389 := bbase (se 4 (by rfl) ⟨471036, by rfl⟩ : syracuseStep 5024389 = 942073) (by norm_num)
theorem B6699185 : Blo 1983435 6699185 := bstep (se 2 (by rfl) ⟨2512194, by rfl⟩ : syracuseStep 6699185 = 5024389) B5024389
theorem B4466123 : Blo 1983435 4466123 := bstep (se 1 (by rfl) ⟨3349592, by rfl⟩ : syracuseStep 4466123 = 6699185) B6699185
theorem B2977415 : Blo 1983435 2977415 := bstep (se 1 (by rfl) ⟨2233061, by rfl⟩ : syracuseStep 2977415 = 4466123) B4466123
theorem B1984943 : Blo 1983435 1984943 := bstep (se 1 (by rfl) ⟨1488707, by rfl⟩ : syracuseStep 1984943 = 2977415) B2977415
theorem B2977421 : Blo 1983435 2977421 := bbase (se 3 (by rfl) ⟨558266, by rfl⟩ : syracuseStep 2977421 = 1116533) (by norm_num)
theorem B1984947 : Blo 1983435 1984947 := bstep (se 1 (by rfl) ⟨1488710, by rfl⟩ : syracuseStep 1984947 = 2977421) B2977421
theorem B4466141 : Blo 1983435 4466141 := bbase (se 3 (by rfl) ⟨837401, by rfl⟩ : syracuseStep 4466141 = 1674803) (by norm_num)
theorem B2977427 : Blo 1983435 2977427 := bstep (se 1 (by rfl) ⟨2233070, by rfl⟩ : syracuseStep 2977427 = 4466141) B4466141
theorem B1984951 : Blo 1983435 1984951 := bstep (se 1 (by rfl) ⟨1488713, by rfl⟩ : syracuseStep 1984951 = 2977427) B2977427
theorem B3349613 : Blo 1983435 3349613 := bbase (se 3 (by rfl) ⟨628052, by rfl⟩ : syracuseStep 3349613 = 1256105) (by norm_num)
theorem B2233075 : Blo 1983435 2233075 := bstep (se 1 (by rfl) ⟨1674806, by rfl⟩ : syracuseStep 2233075 = 3349613) B3349613
theorem B2977433 : Blo 1983435 2977433 := bstep (se 2 (by rfl) ⟨1116537, by rfl⟩ : syracuseStep 2977433 = 2233075) B2233075
theorem B1984955 : Blo 1983435 1984955 := bstep (se 1 (by rfl) ⟨1488716, by rfl⟩ : syracuseStep 1984955 = 2977433) B2977433
theorem B7153925 : Blo 1983435 7153925 := bbase (se 4 (by rfl) ⟨670680, by rfl⟩ : syracuseStep 7153925 = 1341361) (by norm_num)
theorem B19077133 : Blo 1983435 19077133 := bstep (se 3 (by rfl) ⟨3576962, by rfl⟩ : syracuseStep 19077133 = 7153925) B7153925
theorem B25436177 : Blo 1983435 25436177 := bstep (se 2 (by rfl) ⟨9538566, by rfl⟩ : syracuseStep 25436177 = 19077133) B19077133
theorem B16957451 : Blo 1983435 16957451 := bstep (se 1 (by rfl) ⟨12718088, by rfl⟩ : syracuseStep 16957451 = 25436177) B25436177
theorem B11304967 : Blo 1983435 11304967 := bstep (se 1 (by rfl) ⟨8478725, by rfl⟩ : syracuseStep 11304967 = 16957451) B16957451
theorem B15073289 : Blo 1983435 15073289 := bstep (se 2 (by rfl) ⟨5652483, by rfl⟩ : syracuseStep 15073289 = 11304967) B11304967
theorem B10048859 : Blo 1983435 10048859 := bstep (se 1 (by rfl) ⟨7536644, by rfl⟩ : syracuseStep 10048859 = 15073289) B15073289
theorem B6699239 : Blo 1983435 6699239 := bstep (se 1 (by rfl) ⟨5024429, by rfl⟩ : syracuseStep 6699239 = 10048859) B10048859
theorem B4466159 : Blo 1983435 4466159 := bstep (se 1 (by rfl) ⟨3349619, by rfl⟩ : syracuseStep 4466159 = 6699239) B6699239
theorem B2977439 : Blo 1983435 2977439 := bstep (se 1 (by rfl) ⟨2233079, by rfl⟩ : syracuseStep 2977439 = 4466159) B4466159
theorem B1984959 : Blo 1983435 1984959 := bstep (se 1 (by rfl) ⟨1488719, by rfl⟩ : syracuseStep 1984959 = 2977439) B2977439
theorem B2977445 : Blo 1983435 2977445 := bbase (se 4 (by rfl) ⟨279135, by rfl⟩ : syracuseStep 2977445 = 558271) (by norm_num)
theorem B1984963 : Blo 1983435 1984963 := bstep (se 1 (by rfl) ⟨1488722, by rfl⟩ : syracuseStep 1984963 = 2977445) B2977445
theorem B2512225 : Blo 1983435 2512225 := bbase (se 2 (by rfl) ⟨942084, by rfl⟩ : syracuseStep 2512225 = 1884169) (by norm_num)
theorem B3349633 : Blo 1983435 3349633 := bstep (se 2 (by rfl) ⟨1256112, by rfl⟩ : syracuseStep 3349633 = 2512225) B2512225
theorem B4466177 : Blo 1983435 4466177 := bstep (se 2 (by rfl) ⟨1674816, by rfl⟩ : syracuseStep 4466177 = 3349633) B3349633
theorem B2977451 : Blo 1983435 2977451 := bstep (se 1 (by rfl) ⟨2233088, by rfl⟩ : syracuseStep 2977451 = 4466177) B4466177
theorem B1984967 : Blo 1983435 1984967 := bstep (se 1 (by rfl) ⟨1488725, by rfl⟩ : syracuseStep 1984967 = 2977451) B2977451
theorem B2233093 : Blo 1983435 2233093 := bbase (se 4 (by rfl) ⟨209352, by rfl⟩ : syracuseStep 2233093 = 418705) (by norm_num)
theorem B2977457 : Blo 1983435 2977457 := bstep (se 2 (by rfl) ⟨1116546, by rfl⟩ : syracuseStep 2977457 = 2233093) B2233093
theorem B1984971 : Blo 1983435 1984971 := bstep (se 1 (by rfl) ⟨1488728, by rfl⟩ : syracuseStep 1984971 = 2977457) B2977457
theorem B3179549 : Blo 1983435 3179549 := bbase (se 3 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 3179549 = 1192331) (by norm_num)
theorem B2119699 : Blo 1983435 2119699 := bstep (se 1 (by rfl) ⟨1589774, by rfl⟩ : syracuseStep 2119699 = 3179549) B3179549
theorem B2826265 : Blo 1983435 2826265 := bstep (se 2 (by rfl) ⟨1059849, by rfl⟩ : syracuseStep 2826265 = 2119699) B2119699
theorem B3768353 : Blo 1983435 3768353 := bstep (se 2 (by rfl) ⟨1413132, by rfl⟩ : syracuseStep 3768353 = 2826265) B2826265
theorem B2512235 : Blo 1983435 2512235 := bstep (se 1 (by rfl) ⟨1884176, by rfl⟩ : syracuseStep 2512235 = 3768353) B3768353
theorem B6699293 : Blo 1983435 6699293 := bstep (se 3 (by rfl) ⟨1256117, by rfl⟩ : syracuseStep 6699293 = 2512235) B2512235
theorem B4466195 : Blo 1983435 4466195 := bstep (se 1 (by rfl) ⟨3349646, by rfl⟩ : syracuseStep 4466195 = 6699293) B6699293
theorem B2977463 : Blo 1983435 2977463 := bstep (se 1 (by rfl) ⟨2233097, by rfl⟩ : syracuseStep 2977463 = 4466195) B4466195
theorem B1984975 : Blo 1983435 1984975 := bstep (se 1 (by rfl) ⟨1488731, by rfl⟩ : syracuseStep 1984975 = 2977463) B2977463
theorem B2977469 : Blo 1983435 2977469 := bbase (se 3 (by rfl) ⟨558275, by rfl⟩ : syracuseStep 2977469 = 1116551) (by norm_num)
theorem B1984979 : Blo 1983435 1984979 := bstep (se 1 (by rfl) ⟨1488734, by rfl⟩ : syracuseStep 1984979 = 2977469) B2977469
theorem B4466213 : Blo 1983435 4466213 := bbase (se 4 (by rfl) ⟨418707, by rfl⟩ : syracuseStep 4466213 = 837415) (by norm_num)
theorem B2977475 : Blo 1983435 2977475 := bstep (se 1 (by rfl) ⟨2233106, by rfl⟩ : syracuseStep 2977475 = 4466213) B4466213
theorem B1984983 : Blo 1983435 1984983 := bstep (se 1 (by rfl) ⟨1488737, by rfl⟩ : syracuseStep 1984983 = 2977475) B2977475
theorem B5024501 : Blo 1983435 5024501 := bbase (se 5 (by rfl) ⟨235523, by rfl⟩ : syracuseStep 5024501 = 471047) (by norm_num)
theorem B3349667 : Blo 1983435 3349667 := bstep (se 1 (by rfl) ⟨2512250, by rfl⟩ : syracuseStep 3349667 = 5024501) B5024501
theorem B2233111 : Blo 1983435 2233111 := bstep (se 1 (by rfl) ⟨1674833, by rfl⟩ : syracuseStep 2233111 = 3349667) B3349667
theorem B2977481 : Blo 1983435 2977481 := bstep (se 2 (by rfl) ⟨1116555, by rfl⟩ : syracuseStep 2977481 = 2233111) B2233111
theorem B1984987 : Blo 1983435 1984987 := bstep (se 1 (by rfl) ⟨1488740, by rfl⟩ : syracuseStep 1984987 = 2977481) B2977481
theorem B7849477 : Blo 1983435 7849477 := bbase (se 4 (by rfl) ⟨735888, by rfl⟩ : syracuseStep 7849477 = 1471777) (by norm_num)
theorem B41863877 : Blo 1983435 41863877 := bstep (se 4 (by rfl) ⟨3924738, by rfl⟩ : syracuseStep 41863877 = 7849477) B7849477
theorem B27909251 : Blo 1983435 27909251 := bstep (se 1 (by rfl) ⟨20931938, by rfl⟩ : syracuseStep 27909251 = 41863877) B41863877
theorem B18606167 : Blo 1983435 18606167 := bstep (se 1 (by rfl) ⟨13954625, by rfl⟩ : syracuseStep 18606167 = 27909251) B27909251
theorem B12404111 : Blo 1983435 12404111 := bstep (se 1 (by rfl) ⟨9303083, by rfl⟩ : syracuseStep 12404111 = 18606167) B18606167
theorem B33077629 : Blo 1983435 33077629 := bstep (se 3 (by rfl) ⟨6202055, by rfl⟩ : syracuseStep 33077629 = 12404111) B12404111
theorem B176414021 : Blo 1983435 176414021 := bstep (se 4 (by rfl) ⟨16538814, by rfl⟩ : syracuseStep 176414021 = 33077629) B33077629
theorem B117609347 : Blo 1983435 117609347 := bstep (se 1 (by rfl) ⟨88207010, by rfl⟩ : syracuseStep 117609347 = 176414021) B176414021
theorem B313624925 : Blo 1983435 313624925 := bstep (se 3 (by rfl) ⟨58804673, by rfl⟩ : syracuseStep 313624925 = 117609347) B117609347
theorem B209083283 : Blo 1983435 209083283 := bstep (se 1 (by rfl) ⟨156812462, by rfl⟩ : syracuseStep 209083283 = 313624925) B313624925
theorem B139388855 : Blo 1983435 139388855 := bstep (se 1 (by rfl) ⟨104541641, by rfl⟩ : syracuseStep 139388855 = 209083283) B209083283
theorem B371703613 : Blo 1983435 371703613 := bstep (se 3 (by rfl) ⟨69694427, by rfl⟩ : syracuseStep 371703613 = 139388855) B139388855
theorem B495604817 : Blo 1983435 495604817 := bstep (se 2 (by rfl) ⟨185851806, by rfl⟩ : syracuseStep 495604817 = 371703613) B371703613
theorem B330403211 : Blo 1983435 330403211 := bstep (se 1 (by rfl) ⟨247802408, by rfl⟩ : syracuseStep 330403211 = 495604817) B495604817
theorem B220268807 : Blo 1983435 220268807 := bstep (se 1 (by rfl) ⟨165201605, by rfl⟩ : syracuseStep 220268807 = 330403211) B330403211
theorem B146845871 : Blo 1983435 146845871 := bstep (se 1 (by rfl) ⟨110134403, by rfl⟩ : syracuseStep 146845871 = 220268807) B220268807
theorem B97897247 : Blo 1983435 97897247 := bstep (se 1 (by rfl) ⟨73422935, by rfl⟩ : syracuseStep 97897247 = 146845871) B146845871
theorem B65264831 : Blo 1983435 65264831 := bstep (se 1 (by rfl) ⟨48948623, by rfl⟩ : syracuseStep 65264831 = 97897247) B97897247
theorem B43509887 : Blo 1983435 43509887 := bstep (se 1 (by rfl) ⟨32632415, by rfl⟩ : syracuseStep 43509887 = 65264831) B65264831
theorem B29006591 : Blo 1983435 29006591 := bstep (se 1 (by rfl) ⟨21754943, by rfl⟩ : syracuseStep 29006591 = 43509887) B43509887
theorem B77350909 : Blo 1983435 77350909 := bstep (se 3 (by rfl) ⟨14503295, by rfl⟩ : syracuseStep 77350909 = 29006591) B29006591
theorem B103134545 : Blo 1983435 103134545 := bstep (se 2 (by rfl) ⟨38675454, by rfl⟩ : syracuseStep 103134545 = 77350909) B77350909
theorem B68756363 : Blo 1983435 68756363 := bstep (se 1 (by rfl) ⟨51567272, by rfl⟩ : syracuseStep 68756363 = 103134545) B103134545
theorem B45837575 : Blo 1983435 45837575 := bstep (se 1 (by rfl) ⟨34378181, by rfl⟩ : syracuseStep 45837575 = 68756363) B68756363
theorem B30558383 : Blo 1983435 30558383 := bstep (se 1 (by rfl) ⟨22918787, by rfl⟩ : syracuseStep 30558383 = 45837575) B45837575
theorem B20372255 : Blo 1983435 20372255 := bstep (se 1 (by rfl) ⟨15279191, by rfl⟩ : syracuseStep 20372255 = 30558383) B30558383
theorem B13581503 : Blo 1983435 13581503 := bstep (se 1 (by rfl) ⟨10186127, by rfl⟩ : syracuseStep 13581503 = 20372255) B20372255
theorem B9054335 : Blo 1983435 9054335 := bstep (se 1 (by rfl) ⟨6790751, by rfl⟩ : syracuseStep 9054335 = 13581503) B13581503
theorem B6036223 : Blo 1983435 6036223 := bstep (se 1 (by rfl) ⟨4527167, by rfl⟩ : syracuseStep 6036223 = 9054335) B9054335
theorem B8048297 : Blo 1983435 8048297 := bstep (se 2 (by rfl) ⟨3018111, by rfl⟩ : syracuseStep 8048297 = 6036223) B6036223
theorem B5365531 : Blo 1983435 5365531 := bstep (se 1 (by rfl) ⟨4024148, by rfl⟩ : syracuseStep 5365531 = 8048297) B8048297
theorem B28616165 : Blo 1983435 28616165 := bstep (se 4 (by rfl) ⟨2682765, by rfl⟩ : syracuseStep 28616165 = 5365531) B5365531
theorem B19077443 : Blo 1983435 19077443 := bstep (se 1 (by rfl) ⟨14308082, by rfl⟩ : syracuseStep 19077443 = 28616165) B28616165
theorem B12718295 : Blo 1983435 12718295 := bstep (se 1 (by rfl) ⟨9538721, by rfl⟩ : syracuseStep 12718295 = 19077443) B19077443
theorem B8478863 : Blo 1983435 8478863 := bstep (se 1 (by rfl) ⟨6359147, by rfl⟩ : syracuseStep 8478863 = 12718295) B12718295
theorem B5652575 : Blo 1983435 5652575 := bstep (se 1 (by rfl) ⟨4239431, by rfl⟩ : syracuseStep 5652575 = 8478863) B8478863
theorem B3768383 : Blo 1983435 3768383 := bstep (se 1 (by rfl) ⟨2826287, by rfl⟩ : syracuseStep 3768383 = 5652575) B5652575
theorem B10049021 : Blo 1983435 10049021 := bstep (se 3 (by rfl) ⟨1884191, by rfl⟩ : syracuseStep 10049021 = 3768383) B3768383
theorem B6699347 : Blo 1983435 6699347 := bstep (se 1 (by rfl) ⟨5024510, by rfl⟩ : syracuseStep 6699347 = 10049021) B10049021
theorem B4466231 : Blo 1983435 4466231 := bstep (se 1 (by rfl) ⟨3349673, by rfl⟩ : syracuseStep 4466231 = 6699347) B6699347
theorem B2977487 : Blo 1983435 2977487 := bstep (se 1 (by rfl) ⟨2233115, by rfl⟩ : syracuseStep 2977487 = 4466231) B4466231
theorem B1984991 : Blo 1983435 1984991 := bstep (se 1 (by rfl) ⟨1488743, by rfl⟩ : syracuseStep 1984991 = 2977487) B2977487
theorem B2977493 : Blo 1983435 2977493 := bbase (se 7 (by rfl) ⟨34892, by rfl⟩ : syracuseStep 2977493 = 69785) (by norm_num)
theorem B1984995 : Blo 1983435 1984995 := bstep (se 1 (by rfl) ⟨1488746, by rfl⟩ : syracuseStep 1984995 = 2977493) B2977493
theorem B4769381 : Blo 1983435 4769381 := bbase (se 4 (by rfl) ⟨447129, by rfl⟩ : syracuseStep 4769381 = 894259) (by norm_num)
theorem B3179587 : Blo 1983435 3179587 := bstep (se 1 (by rfl) ⟨2384690, by rfl⟩ : syracuseStep 3179587 = 4769381) B4769381
theorem B4239449 : Blo 1983435 4239449 := bstep (se 2 (by rfl) ⟨1589793, by rfl⟩ : syracuseStep 4239449 = 3179587) B3179587
theorem B2826299 : Blo 1983435 2826299 := bstep (se 1 (by rfl) ⟨2119724, by rfl⟩ : syracuseStep 2826299 = 4239449) B4239449
theorem B7536797 : Blo 1983435 7536797 := bstep (se 3 (by rfl) ⟨1413149, by rfl⟩ : syracuseStep 7536797 = 2826299) B2826299
theorem B5024531 : Blo 1983435 5024531 := bstep (se 1 (by rfl) ⟨3768398, by rfl⟩ : syracuseStep 5024531 = 7536797) B7536797
theorem B3349687 : Blo 1983435 3349687 := bstep (se 1 (by rfl) ⟨2512265, by rfl⟩ : syracuseStep 3349687 = 5024531) B5024531
theorem B4466249 : Blo 1983435 4466249 := bstep (se 2 (by rfl) ⟨1674843, by rfl⟩ : syracuseStep 4466249 = 3349687) B3349687
theorem B2977499 : Blo 1983435 2977499 := bstep (se 1 (by rfl) ⟨2233124, by rfl⟩ : syracuseStep 2977499 = 4466249) B4466249
theorem B1984999 : Blo 1983435 1984999 := bstep (se 1 (by rfl) ⟨1488749, by rfl⟩ : syracuseStep 1984999 = 2977499) B2977499
theorem B2233129 : Blo 1983435 2233129 := bbase (se 2 (by rfl) ⟨837423, by rfl⟩ : syracuseStep 2233129 = 1674847) (by norm_num)
theorem B2977505 : Blo 1983435 2977505 := bstep (se 2 (by rfl) ⟨1116564, by rfl⟩ : syracuseStep 2977505 = 2233129) B2233129
theorem B1985003 : Blo 1983435 1985003 := bstep (se 1 (by rfl) ⟨1488752, by rfl⟩ : syracuseStep 1985003 = 2977505) B2977505
theorem B4024181 : Blo 1983435 4024181 := bbase (se 5 (by rfl) ⟨188633, by rfl⟩ : syracuseStep 4024181 = 377267) (by norm_num)
theorem B10731149 : Blo 1983435 10731149 := bstep (se 3 (by rfl) ⟨2012090, by rfl⟩ : syracuseStep 10731149 = 4024181) B4024181
theorem B7154099 : Blo 1983435 7154099 := bstep (se 1 (by rfl) ⟨5365574, by rfl⟩ : syracuseStep 7154099 = 10731149) B10731149
theorem B4769399 : Blo 1983435 4769399 := bstep (se 1 (by rfl) ⟨3577049, by rfl⟩ : syracuseStep 4769399 = 7154099) B7154099
theorem B12718397 : Blo 1983435 12718397 := bstep (se 3 (by rfl) ⟨2384699, by rfl⟩ : syracuseStep 12718397 = 4769399) B4769399
theorem B8478931 : Blo 1983435 8478931 := bstep (se 1 (by rfl) ⟨6359198, by rfl⟩ : syracuseStep 8478931 = 12718397) B12718397
theorem B11305241 : Blo 1983435 11305241 := bstep (se 2 (by rfl) ⟨4239465, by rfl⟩ : syracuseStep 11305241 = 8478931) B8478931
theorem B7536827 : Blo 1983435 7536827 := bstep (se 1 (by rfl) ⟨5652620, by rfl⟩ : syracuseStep 7536827 = 11305241) B11305241
theorem B5024551 : Blo 1983435 5024551 := bstep (se 1 (by rfl) ⟨3768413, by rfl⟩ : syracuseStep 5024551 = 7536827) B7536827
theorem B6699401 : Blo 1983435 6699401 := bstep (se 2 (by rfl) ⟨2512275, by rfl⟩ : syracuseStep 6699401 = 5024551) B5024551
theorem B4466267 : Blo 1983435 4466267 := bstep (se 1 (by rfl) ⟨3349700, by rfl⟩ : syracuseStep 4466267 = 6699401) B6699401
theorem B2977511 : Blo 1983435 2977511 := bstep (se 1 (by rfl) ⟨2233133, by rfl⟩ : syracuseStep 2977511 = 4466267) B4466267
theorem B1985007 : Blo 1983435 1985007 := bstep (se 1 (by rfl) ⟨1488755, by rfl⟩ : syracuseStep 1985007 = 2977511) B2977511
theorem B2977517 : Blo 1983435 2977517 := bbase (se 3 (by rfl) ⟨558284, by rfl⟩ : syracuseStep 2977517 = 1116569) (by norm_num)
theorem B1985011 : Blo 1983435 1985011 := bstep (se 1 (by rfl) ⟨1488758, by rfl⟩ : syracuseStep 1985011 = 2977517) B2977517
theorem B4466285 : Blo 1983435 4466285 := bbase (se 3 (by rfl) ⟨837428, by rfl⟩ : syracuseStep 4466285 = 1674857) (by norm_num)
theorem B2977523 : Blo 1983435 2977523 := bstep (se 1 (by rfl) ⟨2233142, by rfl⟩ : syracuseStep 2977523 = 4466285) B4466285
theorem B1985015 : Blo 1983435 1985015 := bstep (se 1 (by rfl) ⟨1488761, by rfl⟩ : syracuseStep 1985015 = 2977523) B2977523
theorem B3768437 : Blo 1983435 3768437 := bbase (se 5 (by rfl) ⟨176645, by rfl⟩ : syracuseStep 3768437 = 353291) (by norm_num)
theorem B2512291 : Blo 1983435 2512291 := bstep (se 1 (by rfl) ⟨1884218, by rfl⟩ : syracuseStep 2512291 = 3768437) B3768437
theorem B3349721 : Blo 1983435 3349721 := bstep (se 2 (by rfl) ⟨1256145, by rfl⟩ : syracuseStep 3349721 = 2512291) B2512291
theorem B2233147 : Blo 1983435 2233147 := bstep (se 1 (by rfl) ⟨1674860, by rfl⟩ : syracuseStep 2233147 = 3349721) B3349721
theorem B2977529 : Blo 1983435 2977529 := bstep (se 2 (by rfl) ⟨1116573, by rfl⟩ : syracuseStep 2977529 = 2233147) B2233147
theorem B1985019 : Blo 1983435 1985019 := bstep (se 1 (by rfl) ⟨1488764, by rfl⟩ : syracuseStep 1985019 = 2977529) B2977529
theorem B21755285 : Blo 1983435 21755285 := bbase (se 6 (by rfl) ⟨509889, by rfl⟩ : syracuseStep 21755285 = 1019779) (by norm_num)
theorem B928225493 : Blo 1983435 928225493 := bstep (se 7 (by rfl) ⟨10877642, by rfl⟩ : syracuseStep 928225493 = 21755285) B21755285
theorem B618816995 : Blo 1983435 618816995 := bstep (se 1 (by rfl) ⟨464112746, by rfl⟩ : syracuseStep 618816995 = 928225493) B928225493
theorem B412544663 : Blo 1983435 412544663 := bstep (se 1 (by rfl) ⟨309408497, by rfl⟩ : syracuseStep 412544663 = 618816995) B618816995
theorem B275029775 : Blo 1983435 275029775 := bstep (se 1 (by rfl) ⟨206272331, by rfl⟩ : syracuseStep 275029775 = 412544663) B412544663
theorem B183353183 : Blo 1983435 183353183 := bstep (se 1 (by rfl) ⟨137514887, by rfl⟩ : syracuseStep 183353183 = 275029775) B275029775
theorem B122235455 : Blo 1983435 122235455 := bstep (se 1 (by rfl) ⟨91676591, by rfl⟩ : syracuseStep 122235455 = 183353183) B183353183
theorem B81490303 : Blo 1983435 81490303 := bstep (se 1 (by rfl) ⟨61117727, by rfl⟩ : syracuseStep 81490303 = 122235455) B122235455
theorem B108653737 : Blo 1983435 108653737 := bstep (se 2 (by rfl) ⟨40745151, by rfl⟩ : syracuseStep 108653737 = 81490303) B81490303
theorem B144871649 : Blo 1983435 144871649 := bstep (se 2 (by rfl) ⟨54326868, by rfl⟩ : syracuseStep 144871649 = 108653737) B108653737
theorem B96581099 : Blo 1983435 96581099 := bstep (se 1 (by rfl) ⟨72435824, by rfl⟩ : syracuseStep 96581099 = 144871649) B144871649
theorem B64387399 : Blo 1983435 64387399 := bstep (se 1 (by rfl) ⟨48290549, by rfl⟩ : syracuseStep 64387399 = 96581099) B96581099
theorem B85849865 : Blo 1983435 85849865 := bstep (se 2 (by rfl) ⟨32193699, by rfl⟩ : syracuseStep 85849865 = 64387399) B64387399
theorem B57233243 : Blo 1983435 57233243 := bstep (se 1 (by rfl) ⟨42924932, by rfl⟩ : syracuseStep 57233243 = 85849865) B85849865
theorem B38155495 : Blo 1983435 38155495 := bstep (se 1 (by rfl) ⟨28616621, by rfl⟩ : syracuseStep 38155495 = 57233243) B57233243
theorem B50873993 : Blo 1983435 50873993 := bstep (se 2 (by rfl) ⟨19077747, by rfl⟩ : syracuseStep 50873993 = 38155495) B38155495
theorem B33915995 : Blo 1983435 33915995 := bstep (se 1 (by rfl) ⟨25436996, by rfl⟩ : syracuseStep 33915995 = 50873993) B50873993
theorem B22610663 : Blo 1983435 22610663 := bstep (se 1 (by rfl) ⟨16957997, by rfl⟩ : syracuseStep 22610663 = 33915995) B33915995
theorem B15073775 : Blo 1983435 15073775 := bstep (se 1 (by rfl) ⟨11305331, by rfl⟩ : syracuseStep 15073775 = 22610663) B22610663
theorem B10049183 : Blo 1983435 10049183 := bstep (se 1 (by rfl) ⟨7536887, by rfl⟩ : syracuseStep 10049183 = 15073775) B15073775
theorem B6699455 : Blo 1983435 6699455 := bstep (se 1 (by rfl) ⟨5024591, by rfl⟩ : syracuseStep 6699455 = 10049183) B10049183
theorem B4466303 : Blo 1983435 4466303 := bstep (se 1 (by rfl) ⟨3349727, by rfl⟩ : syracuseStep 4466303 = 6699455) B6699455
theorem B2977535 : Blo 1983435 2977535 := bstep (se 1 (by rfl) ⟨2233151, by rfl⟩ : syracuseStep 2977535 = 4466303) B4466303
theorem B1985023 : Blo 1983435 1985023 := bstep (se 1 (by rfl) ⟨1488767, by rfl⟩ : syracuseStep 1985023 = 2977535) B2977535
theorem B2977541 : Blo 1983435 2977541 := bbase (se 4 (by rfl) ⟨279144, by rfl⟩ : syracuseStep 2977541 = 558289) (by norm_num)
theorem B1985027 : Blo 1983435 1985027 := bstep (se 1 (by rfl) ⟨1488770, by rfl⟩ : syracuseStep 1985027 = 2977541) B2977541
theorem B3349741 : Blo 1983435 3349741 := bbase (se 3 (by rfl) ⟨628076, by rfl⟩ : syracuseStep 3349741 = 1256153) (by norm_num)
theorem B4466321 : Blo 1983435 4466321 := bstep (se 2 (by rfl) ⟨1674870, by rfl⟩ : syracuseStep 4466321 = 3349741) B3349741
theorem B2977547 : Blo 1983435 2977547 := bstep (se 1 (by rfl) ⟨2233160, by rfl⟩ : syracuseStep 2977547 = 4466321) B4466321
theorem B1985031 : Blo 1983435 1985031 := bstep (se 1 (by rfl) ⟨1488773, by rfl⟩ : syracuseStep 1985031 = 2977547) B2977547
theorem B2233165 : Blo 1983435 2233165 := bbase (se 3 (by rfl) ⟨418718, by rfl⟩ : syracuseStep 2233165 = 837437) (by norm_num)
theorem B2977553 : Blo 1983435 2977553 := bstep (se 2 (by rfl) ⟨1116582, by rfl⟩ : syracuseStep 2977553 = 2233165) B2233165
theorem B1985035 : Blo 1983435 1985035 := bstep (se 1 (by rfl) ⟨1488776, by rfl⟩ : syracuseStep 1985035 = 2977553) B2977553
theorem B6699509 : Blo 1983435 6699509 := bbase (se 5 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 6699509 = 628079) (by norm_num)
theorem B4466339 : Blo 1983435 4466339 := bstep (se 1 (by rfl) ⟨3349754, by rfl⟩ : syracuseStep 4466339 = 6699509) B6699509
theorem B2977559 : Blo 1983435 2977559 := bstep (se 1 (by rfl) ⟨2233169, by rfl⟩ : syracuseStep 2977559 = 4466339) B4466339
theorem B1985039 : Blo 1983435 1985039 := bstep (se 1 (by rfl) ⟨1488779, by rfl⟩ : syracuseStep 1985039 = 2977559) B2977559
theorem B2977565 : Blo 1983435 2977565 := bbase (se 3 (by rfl) ⟨558293, by rfl⟩ : syracuseStep 2977565 = 1116587) (by norm_num)
theorem B1985043 : Blo 1983435 1985043 := bstep (se 1 (by rfl) ⟨1488782, by rfl⟩ : syracuseStep 1985043 = 2977565) B2977565
theorem B4466357 : Blo 1983435 4466357 := bbase (se 5 (by rfl) ⟨209360, by rfl⟩ : syracuseStep 4466357 = 418721) (by norm_num)
theorem B2977571 : Blo 1983435 2977571 := bstep (se 1 (by rfl) ⟨2233178, by rfl⟩ : syracuseStep 2977571 = 4466357) B4466357
theorem B1985047 : Blo 1983435 1985047 := bstep (se 1 (by rfl) ⟨1488785, by rfl⟩ : syracuseStep 1985047 = 2977571) B2977571
theorem B11305493 : Blo 1983435 11305493 := bbase (se 6 (by rfl) ⟨264972, by rfl⟩ : syracuseStep 11305493 = 529945) (by norm_num)
theorem B7536995 : Blo 1983435 7536995 := bstep (se 1 (by rfl) ⟨5652746, by rfl⟩ : syracuseStep 7536995 = 11305493) B11305493
theorem B5024663 : Blo 1983435 5024663 := bstep (se 1 (by rfl) ⟨3768497, by rfl⟩ : syracuseStep 5024663 = 7536995) B7536995
theorem B3349775 : Blo 1983435 3349775 := bstep (se 1 (by rfl) ⟨2512331, by rfl⟩ : syracuseStep 3349775 = 5024663) B5024663
theorem B2233183 : Blo 1983435 2233183 := bstep (se 1 (by rfl) ⟨1674887, by rfl⟩ : syracuseStep 2233183 = 3349775) B3349775
theorem B2977577 : Blo 1983435 2977577 := bstep (se 2 (by rfl) ⟨1116591, by rfl⟩ : syracuseStep 2977577 = 2233183) B2233183
theorem B1985051 : Blo 1983435 1985051 := bstep (se 1 (by rfl) ⟨1488788, by rfl⟩ : syracuseStep 1985051 = 2977577) B2977577
theorem B5652757 : Blo 1983435 5652757 := bbase (se 6 (by rfl) ⟨132486, by rfl⟩ : syracuseStep 5652757 = 264973) (by norm_num)
theorem B7537009 : Blo 1983435 7537009 := bstep (se 2 (by rfl) ⟨2826378, by rfl⟩ : syracuseStep 7537009 = 5652757) B5652757
theorem B10049345 : Blo 1983435 10049345 := bstep (se 2 (by rfl) ⟨3768504, by rfl⟩ : syracuseStep 10049345 = 7537009) B7537009
theorem B6699563 : Blo 1983435 6699563 := bstep (se 1 (by rfl) ⟨5024672, by rfl⟩ : syracuseStep 6699563 = 10049345) B10049345
theorem B4466375 : Blo 1983435 4466375 := bstep (se 1 (by rfl) ⟨3349781, by rfl⟩ : syracuseStep 4466375 = 6699563) B6699563
theorem B2977583 : Blo 1983435 2977583 := bstep (se 1 (by rfl) ⟨2233187, by rfl⟩ : syracuseStep 2977583 = 4466375) B4466375
theorem B1985055 : Blo 1983435 1985055 := bstep (se 1 (by rfl) ⟨1488791, by rfl⟩ : syracuseStep 1985055 = 2977583) B2977583
theorem B2977589 : Blo 1983435 2977589 := bbase (se 5 (by rfl) ⟨139574, by rfl⟩ : syracuseStep 2977589 = 279149) (by norm_num)
theorem B1985059 : Blo 1983435 1985059 := bstep (se 1 (by rfl) ⟨1488794, by rfl⟩ : syracuseStep 1985059 = 2977589) B2977589
theorem B5024693 : Blo 1983435 5024693 := bbase (se 5 (by rfl) ⟨235532, by rfl⟩ : syracuseStep 5024693 = 471065) (by norm_num)
theorem B3349795 : Blo 1983435 3349795 := bstep (se 1 (by rfl) ⟨2512346, by rfl⟩ : syracuseStep 3349795 = 5024693) B5024693
theorem B4466393 : Blo 1983435 4466393 := bstep (se 2 (by rfl) ⟨1674897, by rfl⟩ : syracuseStep 4466393 = 3349795) B3349795
theorem B2977595 : Blo 1983435 2977595 := bstep (se 1 (by rfl) ⟨2233196, by rfl⟩ : syracuseStep 2977595 = 4466393) B4466393
theorem B1985063 : Blo 1983435 1985063 := bstep (se 1 (by rfl) ⟨1488797, by rfl⟩ : syracuseStep 1985063 = 2977595) B2977595
theorem B2233201 : Blo 1983435 2233201 := bbase (se 2 (by rfl) ⟨837450, by rfl⟩ : syracuseStep 2233201 = 1674901) (by norm_num)
theorem B2977601 : Blo 1983435 2977601 := bstep (se 2 (by rfl) ⟨1116600, by rfl⟩ : syracuseStep 2977601 = 2233201) B2233201
theorem B1985067 : Blo 1983435 1985067 := bstep (se 1 (by rfl) ⟨1488800, by rfl⟩ : syracuseStep 1985067 = 2977601) B2977601
theorem B8479205 : Blo 1983435 8479205 := bbase (se 4 (by rfl) ⟨794925, by rfl⟩ : syracuseStep 8479205 = 1589851) (by norm_num)
theorem B5652803 : Blo 1983435 5652803 := bstep (se 1 (by rfl) ⟨4239602, by rfl⟩ : syracuseStep 5652803 = 8479205) B8479205
theorem B3768535 : Blo 1983435 3768535 := bstep (se 1 (by rfl) ⟨2826401, by rfl⟩ : syracuseStep 3768535 = 5652803) B5652803
theorem B5024713 : Blo 1983435 5024713 := bstep (se 2 (by rfl) ⟨1884267, by rfl⟩ : syracuseStep 5024713 = 3768535) B3768535
theorem B6699617 : Blo 1983435 6699617 := bstep (se 2 (by rfl) ⟨2512356, by rfl⟩ : syracuseStep 6699617 = 5024713) B5024713
theorem B4466411 : Blo 1983435 4466411 := bstep (se 1 (by rfl) ⟨3349808, by rfl⟩ : syracuseStep 4466411 = 6699617) B6699617
theorem B2977607 : Blo 1983435 2977607 := bstep (se 1 (by rfl) ⟨2233205, by rfl⟩ : syracuseStep 2977607 = 4466411) B4466411
theorem B1985071 : Blo 1983435 1985071 := bstep (se 1 (by rfl) ⟨1488803, by rfl⟩ : syracuseStep 1985071 = 2977607) B2977607
theorem B2977613 : Blo 1983435 2977613 := bbase (se 3 (by rfl) ⟨558302, by rfl⟩ : syracuseStep 2977613 = 1116605) (by norm_num)
theorem B1985075 : Blo 1983435 1985075 := bstep (se 1 (by rfl) ⟨1488806, by rfl⟩ : syracuseStep 1985075 = 2977613) B2977613
theorem B4466429 : Blo 1983435 4466429 := bbase (se 3 (by rfl) ⟨837455, by rfl⟩ : syracuseStep 4466429 = 1674911) (by norm_num)
theorem B2977619 : Blo 1983435 2977619 := bstep (se 1 (by rfl) ⟨2233214, by rfl⟩ : syracuseStep 2977619 = 4466429) B4466429
theorem B1985079 : Blo 1983435 1985079 := bstep (se 1 (by rfl) ⟨1488809, by rfl⟩ : syracuseStep 1985079 = 2977619) B2977619
theorem B3349829 : Blo 1983435 3349829 := bbase (se 4 (by rfl) ⟨314046, by rfl⟩ : syracuseStep 3349829 = 628093) (by norm_num)
theorem B2233219 : Blo 1983435 2233219 := bstep (se 1 (by rfl) ⟨1674914, by rfl⟩ : syracuseStep 2233219 = 3349829) B3349829
theorem B2977625 : Blo 1983435 2977625 := bstep (se 2 (by rfl) ⟨1116609, by rfl⟩ : syracuseStep 2977625 = 2233219) B2233219
theorem B1985083 : Blo 1983435 1985083 := bstep (se 1 (by rfl) ⟨1488812, by rfl⟩ : syracuseStep 1985083 = 2977625) B2977625
theorem B15074261 : Blo 1983435 15074261 := bbase (se 7 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 15074261 = 353303) (by norm_num)
theorem B10049507 : Blo 1983435 10049507 := bstep (se 1 (by rfl) ⟨7537130, by rfl⟩ : syracuseStep 10049507 = 15074261) B15074261
theorem B6699671 : Blo 1983435 6699671 := bstep (se 1 (by rfl) ⟨5024753, by rfl⟩ : syracuseStep 6699671 = 10049507) B10049507
theorem B4466447 : Blo 1983435 4466447 := bstep (se 1 (by rfl) ⟨3349835, by rfl⟩ : syracuseStep 4466447 = 6699671) B6699671
theorem B2977631 : Blo 1983435 2977631 := bstep (se 1 (by rfl) ⟨2233223, by rfl⟩ : syracuseStep 2977631 = 4466447) B4466447
theorem B1985087 : Blo 1983435 1985087 := bstep (se 1 (by rfl) ⟨1488815, by rfl⟩ : syracuseStep 1985087 = 2977631) B2977631
theorem B2977637 : Blo 1983435 2977637 := bbase (se 4 (by rfl) ⟨279153, by rfl⟩ : syracuseStep 2977637 = 558307) (by norm_num)
theorem B1985091 : Blo 1983435 1985091 := bstep (se 1 (by rfl) ⟨1488818, by rfl⟩ : syracuseStep 1985091 = 2977637) B2977637
theorem B3768581 : Blo 1983435 3768581 := bbase (se 4 (by rfl) ⟨353304, by rfl⟩ : syracuseStep 3768581 = 706609) (by norm_num)
theorem B2512387 : Blo 1983435 2512387 := bstep (se 1 (by rfl) ⟨1884290, by rfl⟩ : syracuseStep 2512387 = 3768581) B3768581
theorem B3349849 : Blo 1983435 3349849 := bstep (se 2 (by rfl) ⟨1256193, by rfl⟩ : syracuseStep 3349849 = 2512387) B2512387
theorem B4466465 : Blo 1983435 4466465 := bstep (se 2 (by rfl) ⟨1674924, by rfl⟩ : syracuseStep 4466465 = 3349849) B3349849
theorem B2977643 : Blo 1983435 2977643 := bstep (se 1 (by rfl) ⟨2233232, by rfl⟩ : syracuseStep 2977643 = 4466465) B4466465
theorem B1985095 : Blo 1983435 1985095 := bstep (se 1 (by rfl) ⟨1488821, by rfl⟩ : syracuseStep 1985095 = 2977643) B2977643
theorem B2233237 : Blo 1983435 2233237 := bbase (se 6 (by rfl) ⟨52341, by rfl⟩ : syracuseStep 2233237 = 104683) (by norm_num)
theorem B2977649 : Blo 1983435 2977649 := bstep (se 2 (by rfl) ⟨1116618, by rfl⟩ : syracuseStep 2977649 = 2233237) B2233237
theorem B1985099 : Blo 1983435 1985099 := bstep (se 1 (by rfl) ⟨1488824, by rfl⟩ : syracuseStep 1985099 = 2977649) B2977649
theorem B2512397 : Blo 1983435 2512397 := bbase (se 3 (by rfl) ⟨471074, by rfl⟩ : syracuseStep 2512397 = 942149) (by norm_num)
theorem B6699725 : Blo 1983435 6699725 := bstep (se 3 (by rfl) ⟨1256198, by rfl⟩ : syracuseStep 6699725 = 2512397) B2512397
theorem B4466483 : Blo 1983435 4466483 := bstep (se 1 (by rfl) ⟨3349862, by rfl⟩ : syracuseStep 4466483 = 6699725) B6699725
theorem B2977655 : Blo 1983435 2977655 := bstep (se 1 (by rfl) ⟨2233241, by rfl⟩ : syracuseStep 2977655 = 4466483) B4466483
theorem B1985103 : Blo 1983435 1985103 := bstep (se 1 (by rfl) ⟨1488827, by rfl⟩ : syracuseStep 1985103 = 2977655) B2977655
theorem B2977661 : Blo 1983435 2977661 := bbase (se 3 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 2977661 = 1116623) (by norm_num)
theorem B1985107 : Blo 1983435 1985107 := bstep (se 1 (by rfl) ⟨1488830, by rfl⟩ : syracuseStep 1985107 = 2977661) B2977661
theorem B4466501 : Blo 1983435 4466501 := bbase (se 4 (by rfl) ⟨418734, by rfl⟩ : syracuseStep 4466501 = 837469) (by norm_num)
theorem B2977667 : Blo 1983435 2977667 := bstep (se 1 (by rfl) ⟨2233250, by rfl⟩ : syracuseStep 2977667 = 4466501) B4466501
theorem B1985111 : Blo 1983435 1985111 := bstep (se 1 (by rfl) ⟨1488833, by rfl⟩ : syracuseStep 1985111 = 2977667) B2977667
theorem B3179773 : Blo 1983435 3179773 := bbase (se 3 (by rfl) ⟨596207, by rfl⟩ : syracuseStep 3179773 = 1192415) (by norm_num)
theorem B4239697 : Blo 1983435 4239697 := bstep (se 2 (by rfl) ⟨1589886, by rfl⟩ : syracuseStep 4239697 = 3179773) B3179773
theorem B5652929 : Blo 1983435 5652929 := bstep (se 2 (by rfl) ⟨2119848, by rfl⟩ : syracuseStep 5652929 = 4239697) B4239697
theorem B3768619 : Blo 1983435 3768619 := bstep (se 1 (by rfl) ⟨2826464, by rfl⟩ : syracuseStep 3768619 = 5652929) B5652929
theorem B5024825 : Blo 1983435 5024825 := bstep (se 2 (by rfl) ⟨1884309, by rfl⟩ : syracuseStep 5024825 = 3768619) B3768619
theorem B3349883 : Blo 1983435 3349883 := bstep (se 1 (by rfl) ⟨2512412, by rfl⟩ : syracuseStep 3349883 = 5024825) B5024825
theorem B2233255 : Blo 1983435 2233255 := bstep (se 1 (by rfl) ⟨1674941, by rfl⟩ : syracuseStep 2233255 = 3349883) B3349883
theorem B2977673 : Blo 1983435 2977673 := bstep (se 2 (by rfl) ⟨1116627, by rfl⟩ : syracuseStep 2977673 = 2233255) B2233255
theorem B1985115 : Blo 1983435 1985115 := bstep (se 1 (by rfl) ⟨1488836, by rfl⟩ : syracuseStep 1985115 = 2977673) B2977673
theorem B10049669 : Blo 1983435 10049669 := bbase (se 4 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 10049669 = 1884313) (by norm_num)
theorem B6699779 : Blo 1983435 6699779 := bstep (se 1 (by rfl) ⟨5024834, by rfl⟩ : syracuseStep 6699779 = 10049669) B10049669
theorem B4466519 : Blo 1983435 4466519 := bstep (se 1 (by rfl) ⟨3349889, by rfl⟩ : syracuseStep 4466519 = 6699779) B6699779
theorem B2977679 : Blo 1983435 2977679 := bstep (se 1 (by rfl) ⟨2233259, by rfl⟩ : syracuseStep 2977679 = 4466519) B4466519
theorem B1985119 : Blo 1983435 1985119 := bstep (se 1 (by rfl) ⟨1488839, by rfl⟩ : syracuseStep 1985119 = 2977679) B2977679
theorem B2977685 : Blo 1983435 2977685 := bbase (se 6 (by rfl) ⟨69789, by rfl⟩ : syracuseStep 2977685 = 139579) (by norm_num)
theorem B1985123 : Blo 1983435 1985123 := bstep (se 1 (by rfl) ⟨1488842, by rfl⟩ : syracuseStep 1985123 = 2977685) B2977685
theorem B2119861 : Blo 1983435 2119861 := bbase (se 5 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 2119861 = 198737) (by norm_num)
theorem B11305925 : Blo 1983435 11305925 := bstep (se 4 (by rfl) ⟨1059930, by rfl⟩ : syracuseStep 11305925 = 2119861) B2119861
theorem B7537283 : Blo 1983435 7537283 := bstep (se 1 (by rfl) ⟨5652962, by rfl⟩ : syracuseStep 7537283 = 11305925) B11305925
theorem B5024855 : Blo 1983435 5024855 := bstep (se 1 (by rfl) ⟨3768641, by rfl⟩ : syracuseStep 5024855 = 7537283) B7537283
theorem B3349903 : Blo 1983435 3349903 := bstep (se 1 (by rfl) ⟨2512427, by rfl⟩ : syracuseStep 3349903 = 5024855) B5024855
theorem B4466537 : Blo 1983435 4466537 := bstep (se 2 (by rfl) ⟨1674951, by rfl⟩ : syracuseStep 4466537 = 3349903) B3349903
theorem B2977691 : Blo 1983435 2977691 := bstep (se 1 (by rfl) ⟨2233268, by rfl⟩ : syracuseStep 2977691 = 4466537) B4466537
theorem B1985127 : Blo 1983435 1985127 := bstep (se 1 (by rfl) ⟨1488845, by rfl⟩ : syracuseStep 1985127 = 2977691) B2977691
theorem B2233273 : Blo 1983435 2233273 := bbase (se 2 (by rfl) ⟨837477, by rfl⟩ : syracuseStep 2233273 = 1674955) (by norm_num)
theorem B2977697 : Blo 1983435 2977697 := bstep (se 2 (by rfl) ⟨1116636, by rfl⟩ : syracuseStep 2977697 = 2233273) B2233273
theorem B1985131 : Blo 1983435 1985131 := bstep (se 1 (by rfl) ⟨1488848, by rfl⟩ : syracuseStep 1985131 = 2977697) B2977697
theorem B8595173 : Blo 1983435 8595173 := bbase (se 4 (by rfl) ⟨805797, by rfl⟩ : syracuseStep 8595173 = 1611595) (by norm_num)
theorem B5730115 : Blo 1983435 5730115 := bstep (se 1 (by rfl) ⟨4297586, by rfl⟩ : syracuseStep 5730115 = 8595173) B8595173
theorem B7640153 : Blo 1983435 7640153 := bstep (se 2 (by rfl) ⟨2865057, by rfl⟩ : syracuseStep 7640153 = 5730115) B5730115
theorem B5093435 : Blo 1983435 5093435 := bstep (se 1 (by rfl) ⟨3820076, by rfl⟩ : syracuseStep 5093435 = 7640153) B7640153
theorem B3395623 : Blo 1983435 3395623 := bstep (se 1 (by rfl) ⟨2546717, by rfl⟩ : syracuseStep 3395623 = 5093435) B5093435
theorem B4527497 : Blo 1983435 4527497 := bstep (se 2 (by rfl) ⟨1697811, by rfl⟩ : syracuseStep 4527497 = 3395623) B3395623
theorem B3018331 : Blo 1983435 3018331 := bstep (se 1 (by rfl) ⟨2263748, by rfl⟩ : syracuseStep 3018331 = 4527497) B4527497
theorem B4024441 : Blo 1983435 4024441 := bstep (se 2 (by rfl) ⟨1509165, by rfl⟩ : syracuseStep 4024441 = 3018331) B3018331
theorem B5365921 : Blo 1983435 5365921 := bstep (se 2 (by rfl) ⟨2012220, by rfl⟩ : syracuseStep 5365921 = 4024441) B4024441
theorem B7154561 : Blo 1983435 7154561 := bstep (se 2 (by rfl) ⟨2682960, by rfl⟩ : syracuseStep 7154561 = 5365921) B5365921
theorem B4769707 : Blo 1983435 4769707 := bstep (se 1 (by rfl) ⟨3577280, by rfl⟩ : syracuseStep 4769707 = 7154561) B7154561
theorem B6359609 : Blo 1983435 6359609 := bstep (se 2 (by rfl) ⟨2384853, by rfl⟩ : syracuseStep 6359609 = 4769707) B4769707
theorem B4239739 : Blo 1983435 4239739 := bstep (se 1 (by rfl) ⟨3179804, by rfl⟩ : syracuseStep 4239739 = 6359609) B6359609
theorem B5652985 : Blo 1983435 5652985 := bstep (se 2 (by rfl) ⟨2119869, by rfl⟩ : syracuseStep 5652985 = 4239739) B4239739
theorem B7537313 : Blo 1983435 7537313 := bstep (se 2 (by rfl) ⟨2826492, by rfl⟩ : syracuseStep 7537313 = 5652985) B5652985
theorem B5024875 : Blo 1983435 5024875 := bstep (se 1 (by rfl) ⟨3768656, by rfl⟩ : syracuseStep 5024875 = 7537313) B7537313
theorem B6699833 : Blo 1983435 6699833 := bstep (se 2 (by rfl) ⟨2512437, by rfl⟩ : syracuseStep 6699833 = 5024875) B5024875
theorem B4466555 : Blo 1983435 4466555 := bstep (se 1 (by rfl) ⟨3349916, by rfl⟩ : syracuseStep 4466555 = 6699833) B6699833
theorem B2977703 : Blo 1983435 2977703 := bstep (se 1 (by rfl) ⟨2233277, by rfl⟩ : syracuseStep 2977703 = 4466555) B4466555
theorem B1985135 : Blo 1983435 1985135 := bstep (se 1 (by rfl) ⟨1488851, by rfl⟩ : syracuseStep 1985135 = 2977703) B2977703
theorem B2977709 : Blo 1983435 2977709 := bbase (se 3 (by rfl) ⟨558320, by rfl⟩ : syracuseStep 2977709 = 1116641) (by norm_num)
theorem B1985139 : Blo 1983435 1985139 := bstep (se 1 (by rfl) ⟨1488854, by rfl⟩ : syracuseStep 1985139 = 2977709) B2977709
theorem B4466573 : Blo 1983435 4466573 := bbase (se 3 (by rfl) ⟨837482, by rfl⟩ : syracuseStep 4466573 = 1674965) (by norm_num)
theorem B2977715 : Blo 1983435 2977715 := bstep (se 1 (by rfl) ⟨2233286, by rfl⟩ : syracuseStep 2977715 = 4466573) B4466573
theorem B1985143 : Blo 1983435 1985143 := bstep (se 1 (by rfl) ⟨1488857, by rfl⟩ : syracuseStep 1985143 = 2977715) B2977715
theorem B2512453 : Blo 1983435 2512453 := bbase (se 4 (by rfl) ⟨235542, by rfl⟩ : syracuseStep 2512453 = 471085) (by norm_num)
theorem B3349937 : Blo 1983435 3349937 := bstep (se 2 (by rfl) ⟨1256226, by rfl⟩ : syracuseStep 3349937 = 2512453) B2512453
theorem B2233291 : Blo 1983435 2233291 := bstep (se 1 (by rfl) ⟨1674968, by rfl⟩ : syracuseStep 2233291 = 3349937) B3349937
theorem B2977721 : Blo 1983435 2977721 := bstep (se 2 (by rfl) ⟨1116645, by rfl⟩ : syracuseStep 2977721 = 2233291) B2233291
theorem B1985147 : Blo 1983435 1985147 := bstep (se 1 (by rfl) ⟨1488860, by rfl⟩ : syracuseStep 1985147 = 2977721) B2977721
theorem B6036709 : Blo 1983435 6036709 := bbase (se 4 (by rfl) ⟨565941, by rfl⟩ : syracuseStep 6036709 = 1131883) (by norm_num)
theorem B8048945 : Blo 1983435 8048945 := bstep (se 2 (by rfl) ⟨3018354, by rfl⟩ : syracuseStep 8048945 = 6036709) B6036709
theorem B5365963 : Blo 1983435 5365963 := bstep (se 1 (by rfl) ⟨4024472, by rfl⟩ : syracuseStep 5365963 = 8048945) B8048945
theorem B7154617 : Blo 1983435 7154617 := bstep (se 2 (by rfl) ⟨2682981, by rfl⟩ : syracuseStep 7154617 = 5365963) B5365963
theorem B9539489 : Blo 1983435 9539489 := bstep (se 2 (by rfl) ⟨3577308, by rfl⟩ : syracuseStep 9539489 = 7154617) B7154617
theorem B25438637 : Blo 1983435 25438637 := bstep (se 3 (by rfl) ⟨4769744, by rfl⟩ : syracuseStep 25438637 = 9539489) B9539489
theorem B16959091 : Blo 1983435 16959091 := bstep (se 1 (by rfl) ⟨12719318, by rfl⟩ : syracuseStep 16959091 = 25438637) B25438637
theorem B22612121 : Blo 1983435 22612121 := bstep (se 2 (by rfl) ⟨8479545, by rfl⟩ : syracuseStep 22612121 = 16959091) B16959091
theorem B15074747 : Blo 1983435 15074747 := bstep (se 1 (by rfl) ⟨11306060, by rfl⟩ : syracuseStep 15074747 = 22612121) B22612121
theorem B10049831 : Blo 1983435 10049831 := bstep (se 1 (by rfl) ⟨7537373, by rfl⟩ : syracuseStep 10049831 = 15074747) B15074747
theorem B6699887 : Blo 1983435 6699887 := bstep (se 1 (by rfl) ⟨5024915, by rfl⟩ : syracuseStep 6699887 = 10049831) B10049831
theorem B4466591 : Blo 1983435 4466591 := bstep (se 1 (by rfl) ⟨3349943, by rfl⟩ : syracuseStep 4466591 = 6699887) B6699887
theorem B2977727 : Blo 1983435 2977727 := bstep (se 1 (by rfl) ⟨2233295, by rfl⟩ : syracuseStep 2977727 = 4466591) B4466591
theorem B1985151 : Blo 1983435 1985151 := bstep (se 1 (by rfl) ⟨1488863, by rfl⟩ : syracuseStep 1985151 = 2977727) B2977727
theorem B2977733 : Blo 1983435 2977733 := bbase (se 4 (by rfl) ⟨279162, by rfl⟩ : syracuseStep 2977733 = 558325) (by norm_num)
theorem B1985155 : Blo 1983435 1985155 := bstep (se 1 (by rfl) ⟨1488866, by rfl⟩ : syracuseStep 1985155 = 2977733) B2977733
theorem B3349957 : Blo 1983435 3349957 := bbase (se 4 (by rfl) ⟨314058, by rfl⟩ : syracuseStep 3349957 = 628117) (by norm_num)
theorem B4466609 : Blo 1983435 4466609 := bstep (se 2 (by rfl) ⟨1674978, by rfl⟩ : syracuseStep 4466609 = 3349957) B3349957
theorem B2977739 : Blo 1983435 2977739 := bstep (se 1 (by rfl) ⟨2233304, by rfl⟩ : syracuseStep 2977739 = 4466609) B4466609
theorem B1985159 : Blo 1983435 1985159 := bstep (se 1 (by rfl) ⟨1488869, by rfl⟩ : syracuseStep 1985159 = 2977739) B2977739
theorem B2233309 : Blo 1983435 2233309 := bbase (se 3 (by rfl) ⟨418745, by rfl⟩ : syracuseStep 2233309 = 837491) (by norm_num)
theorem B2977745 : Blo 1983435 2977745 := bstep (se 2 (by rfl) ⟨1116654, by rfl⟩ : syracuseStep 2977745 = 2233309) B2233309
theorem B1985163 : Blo 1983435 1985163 := bstep (se 1 (by rfl) ⟨1488872, by rfl⟩ : syracuseStep 1985163 = 2977745) B2977745
theorem B6699941 : Blo 1983435 6699941 := bbase (se 4 (by rfl) ⟨628119, by rfl⟩ : syracuseStep 6699941 = 1256239) (by norm_num)
theorem B4466627 : Blo 1983435 4466627 := bstep (se 1 (by rfl) ⟨3349970, by rfl⟩ : syracuseStep 4466627 = 6699941) B6699941
theorem B2977751 : Blo 1983435 2977751 := bstep (se 1 (by rfl) ⟨2233313, by rfl⟩ : syracuseStep 2977751 = 4466627) B4466627
theorem B1985167 : Blo 1983435 1985167 := bstep (se 1 (by rfl) ⟨1488875, by rfl⟩ : syracuseStep 1985167 = 2977751) B2977751
theorem B2977757 : Blo 1983435 2977757 := bbase (se 3 (by rfl) ⟨558329, by rfl⟩ : syracuseStep 2977757 = 1116659) (by norm_num)
theorem B1985171 : Blo 1983435 1985171 := bstep (se 1 (by rfl) ⟨1488878, by rfl⟩ : syracuseStep 1985171 = 2977757) B2977757
theorem B4466645 : Blo 1983435 4466645 := bbase (se 7 (by rfl) ⟨52343, by rfl⟩ : syracuseStep 4466645 = 104687) (by norm_num)
theorem B2977763 : Blo 1983435 2977763 := bstep (se 1 (by rfl) ⟨2233322, by rfl⟩ : syracuseStep 2977763 = 4466645) B4466645
theorem B1985175 : Blo 1983435 1985175 := bstep (se 1 (by rfl) ⟨1488881, by rfl⟩ : syracuseStep 1985175 = 2977763) B2977763
theorem B4769813 : Blo 1983435 4769813 := bbase (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) (by norm_num)
theorem B12719501 : Blo 1983435 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B8479667 : Blo 1983435 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B5653111 : Blo 1983435 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B7537481 : Blo 1983435 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B5024987 : Blo 1983435 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B3349991 : Blo 1983435 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B2233327 : Blo 1983435 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B2977769 : Blo 1983435 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B1985179 : Blo 1983435 1985179 := bstep (se 1 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 1985179 = 2977769) B2977769
theorem B8049077 : Blo 1983435 8049077 := bbase (se 5 (by rfl) ⟨377300, by rfl⟩ : syracuseStep 8049077 = 754601) (by norm_num)
theorem B5366051 : Blo 1983435 5366051 := bstep (se 1 (by rfl) ⟨4024538, by rfl⟩ : syracuseStep 5366051 = 8049077) B8049077
theorem B3577367 : Blo 1983435 3577367 := bstep (se 1 (by rfl) ⟨2683025, by rfl⟩ : syracuseStep 3577367 = 5366051) B5366051
theorem B2384911 : Blo 1983435 2384911 := bstep (se 1 (by rfl) ⟨1788683, by rfl⟩ : syracuseStep 2384911 = 3577367) B3577367
theorem B3179881 : Blo 1983435 3179881 := bstep (se 2 (by rfl) ⟨1192455, by rfl⟩ : syracuseStep 3179881 = 2384911) B2384911
theorem B16959365 : Blo 1983435 16959365 := bstep (se 4 (by rfl) ⟨1589940, by rfl⟩ : syracuseStep 16959365 = 3179881) B3179881
theorem B11306243 : Blo 1983435 11306243 := bstep (se 1 (by rfl) ⟨8479682, by rfl⟩ : syracuseStep 11306243 = 16959365) B16959365
theorem B7537495 : Blo 1983435 7537495 := bstep (se 1 (by rfl) ⟨5653121, by rfl⟩ : syracuseStep 7537495 = 11306243) B11306243
theorem B10049993 : Blo 1983435 10049993 := bstep (se 2 (by rfl) ⟨3768747, by rfl⟩ : syracuseStep 10049993 = 7537495) B7537495
theorem B6699995 : Blo 1983435 6699995 := bstep (se 1 (by rfl) ⟨5024996, by rfl⟩ : syracuseStep 6699995 = 10049993) B10049993
theorem B4466663 : Blo 1983435 4466663 := bstep (se 1 (by rfl) ⟨3349997, by rfl⟩ : syracuseStep 4466663 = 6699995) B6699995
theorem B2977775 : Blo 1983435 2977775 := bstep (se 1 (by rfl) ⟨2233331, by rfl⟩ : syracuseStep 2977775 = 4466663) B4466663
theorem B1985183 : Blo 1983435 1985183 := bstep (se 1 (by rfl) ⟨1488887, by rfl⟩ : syracuseStep 1985183 = 2977775) B2977775
theorem B2977781 : Blo 1983435 2977781 := bbase (se 5 (by rfl) ⟨139583, by rfl⟩ : syracuseStep 2977781 = 279167) (by norm_num)
theorem B1985187 : Blo 1983435 1985187 := bstep (se 1 (by rfl) ⟨1488890, by rfl⟩ : syracuseStep 1985187 = 2977781) B2977781
theorem B2384921 : Blo 1983435 2384921 := bbase (se 2 (by rfl) ⟨894345, by rfl⟩ : syracuseStep 2384921 = 1788691) (by norm_num)
theorem B6359789 : Blo 1983435 6359789 := bstep (se 3 (by rfl) ⟨1192460, by rfl⟩ : syracuseStep 6359789 = 2384921) B2384921
theorem B4239859 : Blo 1983435 4239859 := bstep (se 1 (by rfl) ⟨3179894, by rfl⟩ : syracuseStep 4239859 = 6359789) B6359789
theorem B5653145 : Blo 1983435 5653145 := bstep (se 2 (by rfl) ⟨2119929, by rfl⟩ : syracuseStep 5653145 = 4239859) B4239859
theorem B3768763 : Blo 1983435 3768763 := bstep (se 1 (by rfl) ⟨2826572, by rfl⟩ : syracuseStep 3768763 = 5653145) B5653145
theorem B5025017 : Blo 1983435 5025017 := bstep (se 2 (by rfl) ⟨1884381, by rfl⟩ : syracuseStep 5025017 = 3768763) B3768763
theorem B3350011 : Blo 1983435 3350011 := bstep (se 1 (by rfl) ⟨2512508, by rfl⟩ : syracuseStep 3350011 = 5025017) B5025017
theorem B4466681 : Blo 1983435 4466681 := bstep (se 2 (by rfl) ⟨1675005, by rfl⟩ : syracuseStep 4466681 = 3350011) B3350011
theorem B2977787 : Blo 1983435 2977787 := bstep (se 1 (by rfl) ⟨2233340, by rfl⟩ : syracuseStep 2977787 = 4466681) B4466681
theorem B1985191 : Blo 1983435 1985191 := bstep (se 1 (by rfl) ⟨1488893, by rfl⟩ : syracuseStep 1985191 = 2977787) B2977787
theorem B2233345 : Blo 1983435 2233345 := bbase (se 2 (by rfl) ⟨837504, by rfl⟩ : syracuseStep 2233345 = 1675009) (by norm_num)
theorem B2977793 : Blo 1983435 2977793 := bstep (se 2 (by rfl) ⟨1116672, by rfl⟩ : syracuseStep 2977793 = 2233345) B2233345
theorem B1985195 : Blo 1983435 1985195 := bstep (se 1 (by rfl) ⟨1488896, by rfl⟩ : syracuseStep 1985195 = 2977793) B2977793
theorem B5025037 : Blo 1983435 5025037 := bbase (se 3 (by rfl) ⟨942194, by rfl⟩ : syracuseStep 5025037 = 1884389) (by norm_num)
theorem B6700049 : Blo 1983435 6700049 := bstep (se 2 (by rfl) ⟨2512518, by rfl⟩ : syracuseStep 6700049 = 5025037) B5025037
theorem B4466699 : Blo 1983435 4466699 := bstep (se 1 (by rfl) ⟨3350024, by rfl⟩ : syracuseStep 4466699 = 6700049) B6700049
theorem B2977799 : Blo 1983435 2977799 := bstep (se 1 (by rfl) ⟨2233349, by rfl⟩ : syracuseStep 2977799 = 4466699) B4466699
theorem B1985199 : Blo 1983435 1985199 := bstep (se 1 (by rfl) ⟨1488899, by rfl⟩ : syracuseStep 1985199 = 2977799) B2977799
theorem B2977805 : Blo 1983435 2977805 := bbase (se 3 (by rfl) ⟨558338, by rfl⟩ : syracuseStep 2977805 = 1116677) (by norm_num)
theorem B1985203 : Blo 1983435 1985203 := bstep (se 1 (by rfl) ⟨1488902, by rfl⟩ : syracuseStep 1985203 = 2977805) B2977805
theorem B4466717 : Blo 1983435 4466717 := bbase (se 3 (by rfl) ⟨837509, by rfl⟩ : syracuseStep 4466717 = 1675019) (by norm_num)
theorem B2977811 : Blo 1983435 2977811 := bstep (se 1 (by rfl) ⟨2233358, by rfl⟩ : syracuseStep 2977811 = 4466717) B4466717
theorem B1985207 : Blo 1983435 1985207 := bstep (se 1 (by rfl) ⟨1488905, by rfl⟩ : syracuseStep 1985207 = 2977811) B2977811
theorem B3350045 : Blo 1983435 3350045 := bbase (se 3 (by rfl) ⟨628133, by rfl⟩ : syracuseStep 3350045 = 1256267) (by norm_num)
theorem B2233363 : Blo 1983435 2233363 := bstep (se 1 (by rfl) ⟨1675022, by rfl⟩ : syracuseStep 2233363 = 3350045) B3350045
theorem B2977817 : Blo 1983435 2977817 := bstep (se 2 (by rfl) ⟨1116681, by rfl⟩ : syracuseStep 2977817 = 2233363) B2233363
theorem B1985211 : Blo 1983435 1985211 := bstep (se 1 (by rfl) ⟨1488908, by rfl⟩ : syracuseStep 1985211 = 2977817) B2977817
theorem B9539797 : Blo 1983435 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B12719729 : Blo 1983435 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B8479819 : Blo 1983435 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B11306425 : Blo 1983435 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B15075233 : Blo 1983435 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B10050155 : Blo 1983435 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B6700103 : Blo 1983435 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B4466735 : Blo 1983435 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B2977823 : Blo 1983435 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B1985215 : Blo 1983435 1985215 := bstep (se 1 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 1985215 = 2977823) B2977823
theorem B2977829 : Blo 1983435 2977829 := bbase (se 4 (by rfl) ⟨279171, by rfl⟩ : syracuseStep 2977829 = 558343) (by norm_num)
theorem B1985219 : Blo 1983435 1985219 := bstep (se 1 (by rfl) ⟨1488914, by rfl⟩ : syracuseStep 1985219 = 2977829) B2977829
theorem B2512549 : Blo 1983435 2512549 := bbase (se 4 (by rfl) ⟨235551, by rfl⟩ : syracuseStep 2512549 = 471103) (by norm_num)
theorem B3350065 : Blo 1983435 3350065 := bstep (se 2 (by rfl) ⟨1256274, by rfl⟩ : syracuseStep 3350065 = 2512549) B2512549
theorem B4466753 : Blo 1983435 4466753 := bstep (se 2 (by rfl) ⟨1675032, by rfl⟩ : syracuseStep 4466753 = 3350065) B3350065
theorem B2977835 : Blo 1983435 2977835 := bstep (se 1 (by rfl) ⟨2233376, by rfl⟩ : syracuseStep 2977835 = 4466753) B4466753
theorem B1985223 : Blo 1983435 1985223 := bstep (se 1 (by rfl) ⟨1488917, by rfl⟩ : syracuseStep 1985223 = 2977835) B2977835
theorem B2233381 : Blo 1983435 2233381 := bbase (se 4 (by rfl) ⟨209379, by rfl⟩ : syracuseStep 2233381 = 418759) (by norm_num)
theorem B2977841 : Blo 1983435 2977841 := bstep (se 2 (by rfl) ⟨1116690, by rfl⟩ : syracuseStep 2977841 = 2233381) B2233381
theorem B1985227 : Blo 1983435 1985227 := bstep (se 1 (by rfl) ⟨1488920, by rfl⟩ : syracuseStep 1985227 = 2977841) B2977841
theorem B2384969 : Blo 1983435 2384969 := bbase (se 2 (by rfl) ⟨894363, by rfl⟩ : syracuseStep 2384969 = 1788727) (by norm_num)
theorem B6359917 : Blo 1983435 6359917 := bstep (se 3 (by rfl) ⟨1192484, by rfl⟩ : syracuseStep 6359917 = 2384969) B2384969
theorem B8479889 : Blo 1983435 8479889 := bstep (se 2 (by rfl) ⟨3179958, by rfl⟩ : syracuseStep 8479889 = 6359917) B6359917
theorem B5653259 : Blo 1983435 5653259 := bstep (se 1 (by rfl) ⟨4239944, by rfl⟩ : syracuseStep 5653259 = 8479889) B8479889
theorem B3768839 : Blo 1983435 3768839 := bstep (se 1 (by rfl) ⟨2826629, by rfl⟩ : syracuseStep 3768839 = 5653259) B5653259
theorem B2512559 : Blo 1983435 2512559 := bstep (se 1 (by rfl) ⟨1884419, by rfl⟩ : syracuseStep 2512559 = 3768839) B3768839
theorem B6700157 : Blo 1983435 6700157 := bstep (se 3 (by rfl) ⟨1256279, by rfl⟩ : syracuseStep 6700157 = 2512559) B2512559
theorem B4466771 : Blo 1983435 4466771 := bstep (se 1 (by rfl) ⟨3350078, by rfl⟩ : syracuseStep 4466771 = 6700157) B6700157
theorem B2977847 : Blo 1983435 2977847 := bstep (se 1 (by rfl) ⟨2233385, by rfl⟩ : syracuseStep 2977847 = 4466771) B4466771
theorem B1985231 : Blo 1983435 1985231 := bstep (se 1 (by rfl) ⟨1488923, by rfl⟩ : syracuseStep 1985231 = 2977847) B2977847
theorem B2977853 : Blo 1983435 2977853 := bbase (se 3 (by rfl) ⟨558347, by rfl⟩ : syracuseStep 2977853 = 1116695) (by norm_num)
theorem B1985235 : Blo 1983435 1985235 := bstep (se 1 (by rfl) ⟨1488926, by rfl⟩ : syracuseStep 1985235 = 2977853) B2977853
theorem B4466789 : Blo 1983435 4466789 := bbase (se 4 (by rfl) ⟨418761, by rfl⟩ : syracuseStep 4466789 = 837523) (by norm_num)
theorem B2977859 : Blo 1983435 2977859 := bstep (se 1 (by rfl) ⟨2233394, by rfl⟩ : syracuseStep 2977859 = 4466789) B4466789
theorem B1985239 : Blo 1983435 1985239 := bstep (se 1 (by rfl) ⟨1488929, by rfl⟩ : syracuseStep 1985239 = 2977859) B2977859
theorem B5025149 : Blo 1983435 5025149 := bbase (se 3 (by rfl) ⟨942215, by rfl⟩ : syracuseStep 5025149 = 1884431) (by norm_num)
theorem B3350099 : Blo 1983435 3350099 := bstep (se 1 (by rfl) ⟨2512574, by rfl⟩ : syracuseStep 3350099 = 5025149) B5025149
theorem B2233399 : Blo 1983435 2233399 := bstep (se 1 (by rfl) ⟨1675049, by rfl⟩ : syracuseStep 2233399 = 3350099) B3350099
theorem B2977865 : Blo 1983435 2977865 := bstep (se 2 (by rfl) ⟨1116699, by rfl⟩ : syracuseStep 2977865 = 2233399) B2233399
theorem B1985243 : Blo 1983435 1985243 := bstep (se 1 (by rfl) ⟨1488932, by rfl⟩ : syracuseStep 1985243 = 2977865) B2977865
theorem B3768869 : Blo 1983435 3768869 := bbase (se 4 (by rfl) ⟨353331, by rfl⟩ : syracuseStep 3768869 = 706663) (by norm_num)
theorem B10050317 : Blo 1983435 10050317 := bstep (se 3 (by rfl) ⟨1884434, by rfl⟩ : syracuseStep 10050317 = 3768869) B3768869
theorem B6700211 : Blo 1983435 6700211 := bstep (se 1 (by rfl) ⟨5025158, by rfl⟩ : syracuseStep 6700211 = 10050317) B10050317
theorem B4466807 : Blo 1983435 4466807 := bstep (se 1 (by rfl) ⟨3350105, by rfl⟩ : syracuseStep 4466807 = 6700211) B6700211
theorem B2977871 : Blo 1983435 2977871 := bstep (se 1 (by rfl) ⟨2233403, by rfl⟩ : syracuseStep 2977871 = 4466807) B4466807
theorem B1985247 : Blo 1983435 1985247 := bstep (se 1 (by rfl) ⟨1488935, by rfl⟩ : syracuseStep 1985247 = 2977871) B2977871
theorem B2977877 : Blo 1983435 2977877 := bbase (se 8 (by rfl) ⟨17448, by rfl⟩ : syracuseStep 2977877 = 34897) (by norm_num)
theorem B1985251 : Blo 1983435 1985251 := bstep (se 1 (by rfl) ⟨1488938, by rfl⟩ : syracuseStep 1985251 = 2977877) B2977877
theorem B5366245 : Blo 1983435 5366245 := bbase (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) (by norm_num)
theorem B7154993 : Blo 1983435 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B19079981 : Blo 1983435 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B12719987 : Blo 1983435 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B8479991 : Blo 1983435 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B5653327 : Blo 1983435 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B7537769 : Blo 1983435 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B5025179 : Blo 1983435 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B3350119 : Blo 1983435 3350119 := bstep (se 1 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 3350119 = 5025179) B5025179
theorem B4466825 : Blo 1983435 4466825 := bstep (se 2 (by rfl) ⟨1675059, by rfl⟩ : syracuseStep 4466825 = 3350119) B3350119
theorem B2977883 : Blo 1983435 2977883 := bstep (se 1 (by rfl) ⟨2233412, by rfl⟩ : syracuseStep 2977883 = 4466825) B4466825
theorem B1985255 : Blo 1983435 1985255 := bstep (se 1 (by rfl) ⟨1488941, by rfl⟩ : syracuseStep 1985255 = 2977883) B2977883
theorem B2233417 : Blo 1983435 2233417 := bbase (se 2 (by rfl) ⟨837531, by rfl⟩ : syracuseStep 2233417 = 1675063) (by norm_num)
theorem B2977889 : Blo 1983435 2977889 := bstep (se 2 (by rfl) ⟨1116708, by rfl⟩ : syracuseStep 2977889 = 2233417) B2233417
theorem B1985259 : Blo 1983435 1985259 := bstep (se 1 (by rfl) ⟨1488944, by rfl⟩ : syracuseStep 1985259 = 2977889) B2977889
theorem B10187525 : Blo 1983435 10187525 := bbase (se 4 (by rfl) ⟨955080, by rfl⟩ : syracuseStep 10187525 = 1910161) (by norm_num)
theorem B6791683 : Blo 1983435 6791683 := bstep (se 1 (by rfl) ⟨5093762, by rfl⟩ : syracuseStep 6791683 = 10187525) B10187525
theorem B9055577 : Blo 1983435 9055577 := bstep (se 2 (by rfl) ⟨3395841, by rfl⟩ : syracuseStep 9055577 = 6791683) B6791683
theorem B6037051 : Blo 1983435 6037051 := bstep (se 1 (by rfl) ⟨4527788, by rfl⟩ : syracuseStep 6037051 = 9055577) B9055577
theorem B8049401 : Blo 1983435 8049401 := bstep (se 2 (by rfl) ⟨3018525, by rfl⟩ : syracuseStep 8049401 = 6037051) B6037051
theorem B5366267 : Blo 1983435 5366267 := bstep (se 1 (by rfl) ⟨4024700, by rfl⟩ : syracuseStep 5366267 = 8049401) B8049401
theorem B3577511 : Blo 1983435 3577511 := bstep (se 1 (by rfl) ⟨2683133, by rfl⟩ : syracuseStep 3577511 = 5366267) B5366267
theorem B2385007 : Blo 1983435 2385007 := bstep (se 1 (by rfl) ⟨1788755, by rfl⟩ : syracuseStep 2385007 = 3577511) B3577511
theorem B12720037 : Blo 1983435 12720037 := bstep (se 4 (by rfl) ⟨1192503, by rfl⟩ : syracuseStep 12720037 = 2385007) B2385007
theorem B16960049 : Blo 1983435 16960049 := bstep (se 2 (by rfl) ⟨6360018, by rfl⟩ : syracuseStep 16960049 = 12720037) B12720037
theorem B11306699 : Blo 1983435 11306699 := bstep (se 1 (by rfl) ⟨8480024, by rfl⟩ : syracuseStep 11306699 = 16960049) B16960049
theorem B7537799 : Blo 1983435 7537799 := bstep (se 1 (by rfl) ⟨5653349, by rfl⟩ : syracuseStep 7537799 = 11306699) B11306699
theorem B5025199 : Blo 1983435 5025199 := bstep (se 1 (by rfl) ⟨3768899, by rfl⟩ : syracuseStep 5025199 = 7537799) B7537799
theorem B6700265 : Blo 1983435 6700265 := bstep (se 2 (by rfl) ⟨2512599, by rfl⟩ : syracuseStep 6700265 = 5025199) B5025199
theorem B4466843 : Blo 1983435 4466843 := bstep (se 1 (by rfl) ⟨3350132, by rfl⟩ : syracuseStep 4466843 = 6700265) B6700265
theorem B2977895 : Blo 1983435 2977895 := bstep (se 1 (by rfl) ⟨2233421, by rfl⟩ : syracuseStep 2977895 = 4466843) B4466843
theorem B1985263 : Blo 1983435 1985263 := bstep (se 1 (by rfl) ⟨1488947, by rfl⟩ : syracuseStep 1985263 = 2977895) B2977895
theorem B2977901 : Blo 1983435 2977901 := bbase (se 3 (by rfl) ⟨558356, by rfl⟩ : syracuseStep 2977901 = 1116713) (by norm_num)
theorem B1985267 : Blo 1983435 1985267 := bstep (se 1 (by rfl) ⟨1488950, by rfl⟩ : syracuseStep 1985267 = 2977901) B2977901
theorem B4466861 : Blo 1983435 4466861 := bbase (se 3 (by rfl) ⟨837536, by rfl⟩ : syracuseStep 4466861 = 1675073) (by norm_num)
theorem B2977907 : Blo 1983435 2977907 := bstep (se 1 (by rfl) ⟨2233430, by rfl⟩ : syracuseStep 2977907 = 4466861) B4466861
theorem B1985271 : Blo 1983435 1985271 := bstep (se 1 (by rfl) ⟨1488953, by rfl⟩ : syracuseStep 1985271 = 2977907) B2977907
theorem B2546897 : Blo 1983435 2546897 := bbase (se 2 (by rfl) ⟨955086, by rfl⟩ : syracuseStep 2546897 = 1910173) (by norm_num)
theorem B6791725 : Blo 1983435 6791725 := bstep (se 3 (by rfl) ⟨1273448, by rfl⟩ : syracuseStep 6791725 = 2546897) B2546897
theorem B9055633 : Blo 1983435 9055633 := bstep (se 2 (by rfl) ⟨3395862, by rfl⟩ : syracuseStep 9055633 = 6791725) B6791725
theorem B12074177 : Blo 1983435 12074177 := bstep (se 2 (by rfl) ⟨4527816, by rfl⟩ : syracuseStep 12074177 = 9055633) B9055633
theorem B8049451 : Blo 1983435 8049451 := bstep (se 1 (by rfl) ⟨6037088, by rfl⟩ : syracuseStep 8049451 = 12074177) B12074177
theorem B10732601 : Blo 1983435 10732601 := bstep (se 2 (by rfl) ⟨4024725, by rfl⟩ : syracuseStep 10732601 = 8049451) B8049451
theorem B7155067 : Blo 1983435 7155067 := bstep (se 1 (by rfl) ⟨5366300, by rfl⟩ : syracuseStep 7155067 = 10732601) B10732601
theorem B9540089 : Blo 1983435 9540089 := bstep (se 2 (by rfl) ⟨3577533, by rfl⟩ : syracuseStep 9540089 = 7155067) B7155067
theorem B6360059 : Blo 1983435 6360059 := bstep (se 1 (by rfl) ⟨4770044, by rfl⟩ : syracuseStep 6360059 = 9540089) B9540089
theorem B4240039 : Blo 1983435 4240039 := bstep (se 1 (by rfl) ⟨3180029, by rfl⟩ : syracuseStep 4240039 = 6360059) B6360059
theorem B5653385 : Blo 1983435 5653385 := bstep (se 2 (by rfl) ⟨2120019, by rfl⟩ : syracuseStep 5653385 = 4240039) B4240039
theorem B3768923 : Blo 1983435 3768923 := bstep (se 1 (by rfl) ⟨2826692, by rfl⟩ : syracuseStep 3768923 = 5653385) B5653385
theorem B2512615 : Blo 1983435 2512615 := bstep (se 1 (by rfl) ⟨1884461, by rfl⟩ : syracuseStep 2512615 = 3768923) B3768923
theorem B3350153 : Blo 1983435 3350153 := bstep (se 2 (by rfl) ⟨1256307, by rfl⟩ : syracuseStep 3350153 = 2512615) B2512615
theorem B2233435 : Blo 1983435 2233435 := bstep (se 1 (by rfl) ⟨1675076, by rfl⟩ : syracuseStep 2233435 = 3350153) B3350153
theorem B2977913 : Blo 1983435 2977913 := bstep (se 2 (by rfl) ⟨1116717, by rfl⟩ : syracuseStep 2977913 = 2233435) B2233435
theorem B1985275 : Blo 1983435 1985275 := bstep (se 1 (by rfl) ⟨1488956, by rfl⟩ : syracuseStep 1985275 = 2977913) B2977913
theorem B25440277 : Blo 1983435 25440277 := bbase (se 6 (by rfl) ⟨596256, by rfl⟩ : syracuseStep 25440277 = 1192513) (by norm_num)
theorem B33920369 : Blo 1983435 33920369 := bstep (se 2 (by rfl) ⟨12720138, by rfl⟩ : syracuseStep 33920369 = 25440277) B25440277
theorem B22613579 : Blo 1983435 22613579 := bstep (se 1 (by rfl) ⟨16960184, by rfl⟩ : syracuseStep 22613579 = 33920369) B33920369
theorem B15075719 : Blo 1983435 15075719 := bstep (se 1 (by rfl) ⟨11306789, by rfl⟩ : syracuseStep 15075719 = 22613579) B22613579
theorem B10050479 : Blo 1983435 10050479 := bstep (se 1 (by rfl) ⟨7537859, by rfl⟩ : syracuseStep 10050479 = 15075719) B15075719
theorem B6700319 : Blo 1983435 6700319 := bstep (se 1 (by rfl) ⟨5025239, by rfl⟩ : syracuseStep 6700319 = 10050479) B10050479
theorem B4466879 : Blo 1983435 4466879 := bstep (se 1 (by rfl) ⟨3350159, by rfl⟩ : syracuseStep 4466879 = 6700319) B6700319
theorem B2977919 : Blo 1983435 2977919 := bstep (se 1 (by rfl) ⟨2233439, by rfl⟩ : syracuseStep 2977919 = 4466879) B4466879
theorem B1985279 : Blo 1983435 1985279 := bstep (se 1 (by rfl) ⟨1488959, by rfl⟩ : syracuseStep 1985279 = 2977919) B2977919
theorem B2977925 : Blo 1983435 2977925 := bbase (se 4 (by rfl) ⟨279180, by rfl⟩ : syracuseStep 2977925 = 558361) (by norm_num)
theorem B1985283 : Blo 1983435 1985283 := bstep (se 1 (by rfl) ⟨1488962, by rfl⟩ : syracuseStep 1985283 = 2977925) B2977925
theorem B3350173 : Blo 1983435 3350173 := bbase (se 3 (by rfl) ⟨628157, by rfl⟩ : syracuseStep 3350173 = 1256315) (by norm_num)
theorem B4466897 : Blo 1983435 4466897 := bstep (se 2 (by rfl) ⟨1675086, by rfl⟩ : syracuseStep 4466897 = 3350173) B3350173
theorem B2977931 : Blo 1983435 2977931 := bstep (se 1 (by rfl) ⟨2233448, by rfl⟩ : syracuseStep 2977931 = 4466897) B4466897
theorem B1985287 : Blo 1983435 1985287 := bstep (se 1 (by rfl) ⟨1488965, by rfl⟩ : syracuseStep 1985287 = 2977931) B2977931
theorem B2233453 : Blo 1983435 2233453 := bbase (se 3 (by rfl) ⟨418772, by rfl⟩ : syracuseStep 2233453 = 837545) (by norm_num)
theorem B2977937 : Blo 1983435 2977937 := bstep (se 2 (by rfl) ⟨1116726, by rfl⟩ : syracuseStep 2977937 = 2233453) B2233453
theorem B1985291 : Blo 1983435 1985291 := bstep (se 1 (by rfl) ⟨1488968, by rfl⟩ : syracuseStep 1985291 = 2977937) B2977937
theorem B6700373 : Blo 1983435 6700373 := bbase (se 11 (by rfl) ⟨4907, by rfl⟩ : syracuseStep 6700373 = 9815) (by norm_num)
theorem B4466915 : Blo 1983435 4466915 := bstep (se 1 (by rfl) ⟨3350186, by rfl⟩ : syracuseStep 4466915 = 6700373) B6700373
theorem B2977943 : Blo 1983435 2977943 := bstep (se 1 (by rfl) ⟨2233457, by rfl⟩ : syracuseStep 2977943 = 4466915) B4466915
theorem B1985295 : Blo 1983435 1985295 := bstep (se 1 (by rfl) ⟨1488971, by rfl⟩ : syracuseStep 1985295 = 2977943) B2977943
theorem B2977949 : Blo 1983435 2977949 := bbase (se 3 (by rfl) ⟨558365, by rfl⟩ : syracuseStep 2977949 = 1116731) (by norm_num)
theorem B1985299 : Blo 1983435 1985299 := bstep (se 1 (by rfl) ⟨1488974, by rfl⟩ : syracuseStep 1985299 = 2977949) B2977949
theorem B4466933 : Blo 1983435 4466933 := bbase (se 5 (by rfl) ⟨209387, by rfl⟩ : syracuseStep 4466933 = 418775) (by norm_num)
theorem B2977955 : Blo 1983435 2977955 := bstep (se 1 (by rfl) ⟨2233466, by rfl⟩ : syracuseStep 2977955 = 4466933) B4466933
theorem B1985303 : Blo 1983435 1985303 := bstep (se 1 (by rfl) ⟨1488977, by rfl⟩ : syracuseStep 1985303 = 2977955) B2977955
theorem B16099157 : Blo 1983435 16099157 := bbase (se 9 (by rfl) ⟨47165, by rfl⟩ : syracuseStep 16099157 = 94331) (by norm_num)
theorem B10732771 : Blo 1983435 10732771 := bstep (se 1 (by rfl) ⟨8049578, by rfl⟩ : syracuseStep 10732771 = 16099157) B16099157
theorem B14310361 : Blo 1983435 14310361 := bstep (se 2 (by rfl) ⟨5366385, by rfl⟩ : syracuseStep 14310361 = 10732771) B10732771
theorem B19080481 : Blo 1983435 19080481 := bstep (se 2 (by rfl) ⟨7155180, by rfl⟩ : syracuseStep 19080481 = 14310361) B14310361
theorem B25440641 : Blo 1983435 25440641 := bstep (se 2 (by rfl) ⟨9540240, by rfl⟩ : syracuseStep 25440641 = 19080481) B19080481
theorem B16960427 : Blo 1983435 16960427 := bstep (se 1 (by rfl) ⟨12720320, by rfl⟩ : syracuseStep 16960427 = 25440641) B25440641
theorem B11306951 : Blo 1983435 11306951 := bstep (se 1 (by rfl) ⟨8480213, by rfl⟩ : syracuseStep 11306951 = 16960427) B16960427
theorem B7537967 : Blo 1983435 7537967 := bstep (se 1 (by rfl) ⟨5653475, by rfl⟩ : syracuseStep 7537967 = 11306951) B11306951
theorem B5025311 : Blo 1983435 5025311 := bstep (se 1 (by rfl) ⟨3768983, by rfl⟩ : syracuseStep 5025311 = 7537967) B7537967
theorem B3350207 : Blo 1983435 3350207 := bstep (se 1 (by rfl) ⟨2512655, by rfl⟩ : syracuseStep 3350207 = 5025311) B5025311
theorem B2233471 : Blo 1983435 2233471 := bstep (se 1 (by rfl) ⟨1675103, by rfl⟩ : syracuseStep 2233471 = 3350207) B3350207
theorem B2977961 : Blo 1983435 2977961 := bstep (se 2 (by rfl) ⟨1116735, by rfl⟩ : syracuseStep 2977961 = 2233471) B2233471
theorem B1985307 : Blo 1983435 1985307 := bstep (se 1 (by rfl) ⟨1488980, by rfl⟩ : syracuseStep 1985307 = 2977961) B2977961
theorem B2385065 : Blo 1983435 2385065 := bbase (se 2 (by rfl) ⟨894399, by rfl⟩ : syracuseStep 2385065 = 1788799) (by norm_num)
theorem B6360173 : Blo 1983435 6360173 := bstep (se 3 (by rfl) ⟨1192532, by rfl⟩ : syracuseStep 6360173 = 2385065) B2385065
theorem B4240115 : Blo 1983435 4240115 := bstep (se 1 (by rfl) ⟨3180086, by rfl⟩ : syracuseStep 4240115 = 6360173) B6360173
theorem B2826743 : Blo 1983435 2826743 := bstep (se 1 (by rfl) ⟨2120057, by rfl⟩ : syracuseStep 2826743 = 4240115) B4240115
theorem B7537981 : Blo 1983435 7537981 := bstep (se 3 (by rfl) ⟨1413371, by rfl⟩ : syracuseStep 7537981 = 2826743) B2826743
theorem B10050641 : Blo 1983435 10050641 := bstep (se 2 (by rfl) ⟨3768990, by rfl⟩ : syracuseStep 10050641 = 7537981) B7537981
theorem B6700427 : Blo 1983435 6700427 := bstep (se 1 (by rfl) ⟨5025320, by rfl⟩ : syracuseStep 6700427 = 10050641) B10050641
theorem B4466951 : Blo 1983435 4466951 := bstep (se 1 (by rfl) ⟨3350213, by rfl⟩ : syracuseStep 4466951 = 6700427) B6700427
theorem B2977967 : Blo 1983435 2977967 := bstep (se 1 (by rfl) ⟨2233475, by rfl⟩ : syracuseStep 2977967 = 4466951) B4466951
theorem B1985311 : Blo 1983435 1985311 := bstep (se 1 (by rfl) ⟨1488983, by rfl⟩ : syracuseStep 1985311 = 2977967) B2977967
theorem B2977973 : Blo 1983435 2977973 := bbase (se 5 (by rfl) ⟨139592, by rfl⟩ : syracuseStep 2977973 = 279185) (by norm_num)
theorem B1985315 : Blo 1983435 1985315 := bstep (se 1 (by rfl) ⟨1488986, by rfl⟩ : syracuseStep 1985315 = 2977973) B2977973
theorem B5025341 : Blo 1983435 5025341 := bbase (se 3 (by rfl) ⟨942251, by rfl⟩ : syracuseStep 5025341 = 1884503) (by norm_num)
theorem B3350227 : Blo 1983435 3350227 := bstep (se 1 (by rfl) ⟨2512670, by rfl⟩ : syracuseStep 3350227 = 5025341) B5025341
theorem B4466969 : Blo 1983435 4466969 := bstep (se 2 (by rfl) ⟨1675113, by rfl⟩ : syracuseStep 4466969 = 3350227) B3350227
theorem B2977979 : Blo 1983435 2977979 := bstep (se 1 (by rfl) ⟨2233484, by rfl⟩ : syracuseStep 2977979 = 4466969) B4466969
theorem B1985319 : Blo 1983435 1985319 := bstep (se 1 (by rfl) ⟨1488989, by rfl⟩ : syracuseStep 1985319 = 2977979) B2977979
theorem B2233489 : Blo 1983435 2233489 := bbase (se 2 (by rfl) ⟨837558, by rfl⟩ : syracuseStep 2233489 = 1675117) (by norm_num)
theorem B2977985 : Blo 1983435 2977985 := bstep (se 2 (by rfl) ⟨1116744, by rfl⟩ : syracuseStep 2977985 = 2233489) B2233489
theorem B1985323 : Blo 1983435 1985323 := bstep (se 1 (by rfl) ⟨1488992, by rfl⟩ : syracuseStep 1985323 = 2977985) B2977985
theorem B3769021 : Blo 1983435 3769021 := bbase (se 3 (by rfl) ⟨706691, by rfl⟩ : syracuseStep 3769021 = 1413383) (by norm_num)
theorem B5025361 : Blo 1983435 5025361 := bstep (se 2 (by rfl) ⟨1884510, by rfl⟩ : syracuseStep 5025361 = 3769021) B3769021
theorem B6700481 : Blo 1983435 6700481 := bstep (se 2 (by rfl) ⟨2512680, by rfl⟩ : syracuseStep 6700481 = 5025361) B5025361
theorem B4466987 : Blo 1983435 4466987 := bstep (se 1 (by rfl) ⟨3350240, by rfl⟩ : syracuseStep 4466987 = 6700481) B6700481
theorem B2977991 : Blo 1983435 2977991 := bstep (se 1 (by rfl) ⟨2233493, by rfl⟩ : syracuseStep 2977991 = 4466987) B4466987
theorem B1985327 : Blo 1983435 1985327 := bstep (se 1 (by rfl) ⟨1488995, by rfl⟩ : syracuseStep 1985327 = 2977991) B2977991
theorem B2977997 : Blo 1983435 2977997 := bbase (se 3 (by rfl) ⟨558374, by rfl⟩ : syracuseStep 2977997 = 1116749) (by norm_num)
theorem B1985331 : Blo 1983435 1985331 := bstep (se 1 (by rfl) ⟨1488998, by rfl⟩ : syracuseStep 1985331 = 2977997) B2977997
theorem B4467005 : Blo 1983435 4467005 := bbase (se 3 (by rfl) ⟨837563, by rfl⟩ : syracuseStep 4467005 = 1675127) (by norm_num)
theorem B2978003 : Blo 1983435 2978003 := bstep (se 1 (by rfl) ⟨2233502, by rfl⟩ : syracuseStep 2978003 = 4467005) B4467005
theorem B1985335 : Blo 1983435 1985335 := bstep (se 1 (by rfl) ⟨1489001, by rfl⟩ : syracuseStep 1985335 = 2978003) B2978003
theorem B3350261 : Blo 1983435 3350261 := bbase (se 5 (by rfl) ⟨157043, by rfl⟩ : syracuseStep 3350261 = 314087) (by norm_num)
theorem B2233507 : Blo 1983435 2233507 := bstep (se 1 (by rfl) ⟨1675130, by rfl⟩ : syracuseStep 2233507 = 3350261) B3350261
theorem B2978009 : Blo 1983435 2978009 := bstep (se 2 (by rfl) ⟨1116753, by rfl⟩ : syracuseStep 2978009 = 2233507) B2233507
theorem B1985339 : Blo 1983435 1985339 := bstep (se 1 (by rfl) ⟨1489004, by rfl⟩ : syracuseStep 1985339 = 2978009) B2978009
theorem B6791957 : Blo 1983435 6791957 := bbase (se 6 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 6791957 = 318373) (by norm_num)
theorem B4527971 : Blo 1983435 4527971 := bstep (se 1 (by rfl) ⟨3395978, by rfl⟩ : syracuseStep 4527971 = 6791957) B6791957
theorem B3018647 : Blo 1983435 3018647 := bstep (se 1 (by rfl) ⟨2263985, by rfl⟩ : syracuseStep 3018647 = 4527971) B4527971
theorem B8049725 : Blo 1983435 8049725 := bstep (se 3 (by rfl) ⟨1509323, by rfl⟩ : syracuseStep 8049725 = 3018647) B3018647
theorem B5366483 : Blo 1983435 5366483 := bstep (se 1 (by rfl) ⟨4024862, by rfl⟩ : syracuseStep 5366483 = 8049725) B8049725
theorem B3577655 : Blo 1983435 3577655 := bstep (se 1 (by rfl) ⟨2683241, by rfl⟩ : syracuseStep 3577655 = 5366483) B5366483
theorem B9540413 : Blo 1983435 9540413 := bstep (se 3 (by rfl) ⟨1788827, by rfl⟩ : syracuseStep 9540413 = 3577655) B3577655
theorem B6360275 : Blo 1983435 6360275 := bstep (se 1 (by rfl) ⟨4770206, by rfl⟩ : syracuseStep 6360275 = 9540413) B9540413
theorem B4240183 : Blo 1983435 4240183 := bstep (se 1 (by rfl) ⟨3180137, by rfl⟩ : syracuseStep 4240183 = 6360275) B6360275
theorem B5653577 : Blo 1983435 5653577 := bstep (se 2 (by rfl) ⟨2120091, by rfl⟩ : syracuseStep 5653577 = 4240183) B4240183
theorem B15076205 : Blo 1983435 15076205 := bstep (se 3 (by rfl) ⟨2826788, by rfl⟩ : syracuseStep 15076205 = 5653577) B5653577
theorem B10050803 : Blo 1983435 10050803 := bstep (se 1 (by rfl) ⟨7538102, by rfl⟩ : syracuseStep 10050803 = 15076205) B15076205
theorem B6700535 : Blo 1983435 6700535 := bstep (se 1 (by rfl) ⟨5025401, by rfl⟩ : syracuseStep 6700535 = 10050803) B10050803
theorem B4467023 : Blo 1983435 4467023 := bstep (se 1 (by rfl) ⟨3350267, by rfl⟩ : syracuseStep 4467023 = 6700535) B6700535
theorem B2978015 : Blo 1983435 2978015 := bstep (se 1 (by rfl) ⟨2233511, by rfl⟩ : syracuseStep 2978015 = 4467023) B4467023
theorem B1985343 : Blo 1983435 1985343 := bstep (se 1 (by rfl) ⟨1489007, by rfl⟩ : syracuseStep 1985343 = 2978015) B2978015
theorem B2978021 : Blo 1983435 2978021 := bbase (se 4 (by rfl) ⟨279189, by rfl⟩ : syracuseStep 2978021 = 558379) (by norm_num)
theorem B1985347 : Blo 1983435 1985347 := bstep (se 1 (by rfl) ⟨1489010, by rfl⟩ : syracuseStep 1985347 = 2978021) B2978021
theorem B2683253 : Blo 1983435 2683253 := bbase (se 5 (by rfl) ⟨125777, by rfl⟩ : syracuseStep 2683253 = 251555) (by norm_num)
theorem B7155341 : Blo 1983435 7155341 := bstep (se 3 (by rfl) ⟨1341626, by rfl⟩ : syracuseStep 7155341 = 2683253) B2683253
theorem B4770227 : Blo 1983435 4770227 := bstep (se 1 (by rfl) ⟨3577670, by rfl⟩ : syracuseStep 4770227 = 7155341) B7155341
theorem B3180151 : Blo 1983435 3180151 := bstep (se 1 (by rfl) ⟨2385113, by rfl⟩ : syracuseStep 3180151 = 4770227) B4770227
theorem B4240201 : Blo 1983435 4240201 := bstep (se 2 (by rfl) ⟨1590075, by rfl⟩ : syracuseStep 4240201 = 3180151) B3180151
theorem B5653601 : Blo 1983435 5653601 := bstep (se 2 (by rfl) ⟨2120100, by rfl⟩ : syracuseStep 5653601 = 4240201) B4240201
theorem B3769067 : Blo 1983435 3769067 := bstep (se 1 (by rfl) ⟨2826800, by rfl⟩ : syracuseStep 3769067 = 5653601) B5653601
theorem B2512711 : Blo 1983435 2512711 := bstep (se 1 (by rfl) ⟨1884533, by rfl⟩ : syracuseStep 2512711 = 3769067) B3769067
theorem B3350281 : Blo 1983435 3350281 := bstep (se 2 (by rfl) ⟨1256355, by rfl⟩ : syracuseStep 3350281 = 2512711) B2512711
theorem B4467041 : Blo 1983435 4467041 := bstep (se 2 (by rfl) ⟨1675140, by rfl⟩ : syracuseStep 4467041 = 3350281) B3350281
theorem B2978027 : Blo 1983435 2978027 := bstep (se 1 (by rfl) ⟨2233520, by rfl⟩ : syracuseStep 2978027 = 4467041) B4467041
theorem B1985351 : Blo 1983435 1985351 := bstep (se 1 (by rfl) ⟨1489013, by rfl⟩ : syracuseStep 1985351 = 2978027) B2978027
theorem B2233525 : Blo 1983435 2233525 := bbase (se 5 (by rfl) ⟨104696, by rfl⟩ : syracuseStep 2233525 = 209393) (by norm_num)
theorem B2978033 : Blo 1983435 2978033 := bstep (se 2 (by rfl) ⟨1116762, by rfl⟩ : syracuseStep 2978033 = 2233525) B2233525
theorem B1985355 : Blo 1983435 1985355 := bstep (se 1 (by rfl) ⟨1489016, by rfl⟩ : syracuseStep 1985355 = 2978033) B2978033
theorem B2512721 : Blo 1983435 2512721 := bbase (se 2 (by rfl) ⟨942270, by rfl⟩ : syracuseStep 2512721 = 1884541) (by norm_num)
theorem B6700589 : Blo 1983435 6700589 := bstep (se 3 (by rfl) ⟨1256360, by rfl⟩ : syracuseStep 6700589 = 2512721) B2512721
theorem B4467059 : Blo 1983435 4467059 := bstep (se 1 (by rfl) ⟨3350294, by rfl⟩ : syracuseStep 4467059 = 6700589) B6700589
theorem B2978039 : Blo 1983435 2978039 := bstep (se 1 (by rfl) ⟨2233529, by rfl⟩ : syracuseStep 2978039 = 4467059) B4467059
theorem B1985359 : Blo 1983435 1985359 := bstep (se 1 (by rfl) ⟨1489019, by rfl⟩ : syracuseStep 1985359 = 2978039) B2978039
theorem B2978045 : Blo 1983435 2978045 := bbase (se 3 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 2978045 = 1116767) (by norm_num)
theorem B1985363 : Blo 1983435 1985363 := bstep (se 1 (by rfl) ⟨1489022, by rfl⟩ : syracuseStep 1985363 = 2978045) B2978045
theorem B4467077 : Blo 1983435 4467077 := bbase (se 4 (by rfl) ⟨418788, by rfl⟩ : syracuseStep 4467077 = 837577) (by norm_num)
theorem B2978051 : Blo 1983435 2978051 := bstep (se 1 (by rfl) ⟨2233538, by rfl⟩ : syracuseStep 2978051 = 4467077) B4467077
theorem B1985367 : Blo 1983435 1985367 := bstep (se 1 (by rfl) ⟨1489025, by rfl⟩ : syracuseStep 1985367 = 2978051) B2978051
theorem B2826829 : Blo 1983435 2826829 := bbase (se 3 (by rfl) ⟨530030, by rfl⟩ : syracuseStep 2826829 = 1060061) (by norm_num)
theorem B3769105 : Blo 1983435 3769105 := bstep (se 2 (by rfl) ⟨1413414, by rfl⟩ : syracuseStep 3769105 = 2826829) B2826829
theorem B5025473 : Blo 1983435 5025473 := bstep (se 2 (by rfl) ⟨1884552, by rfl⟩ : syracuseStep 5025473 = 3769105) B3769105
theorem B3350315 : Blo 1983435 3350315 := bstep (se 1 (by rfl) ⟨2512736, by rfl⟩ : syracuseStep 3350315 = 5025473) B5025473
theorem B2233543 : Blo 1983435 2233543 := bstep (se 1 (by rfl) ⟨1675157, by rfl⟩ : syracuseStep 2233543 = 3350315) B3350315
theorem B2978057 : Blo 1983435 2978057 := bstep (se 2 (by rfl) ⟨1116771, by rfl⟩ : syracuseStep 2978057 = 2233543) B2233543
theorem B1985371 : Blo 1983435 1985371 := bstep (se 1 (by rfl) ⟨1489028, by rfl⟩ : syracuseStep 1985371 = 2978057) B2978057
theorem B10050965 : Blo 1983435 10050965 := bbase (se 6 (by rfl) ⟨235569, by rfl⟩ : syracuseStep 10050965 = 471139) (by norm_num)
theorem B6700643 : Blo 1983435 6700643 := bstep (se 1 (by rfl) ⟨5025482, by rfl⟩ : syracuseStep 6700643 = 10050965) B10050965
theorem B4467095 : Blo 1983435 4467095 := bstep (se 1 (by rfl) ⟨3350321, by rfl⟩ : syracuseStep 4467095 = 6700643) B6700643
theorem B2978063 : Blo 1983435 2978063 := bstep (se 1 (by rfl) ⟨2233547, by rfl⟩ : syracuseStep 2978063 = 4467095) B4467095
theorem B1985375 : Blo 1983435 1985375 := bstep (se 1 (by rfl) ⟨1489031, by rfl⟩ : syracuseStep 1985375 = 2978063) B2978063
theorem B2978069 : Blo 1983435 2978069 := bbase (se 6 (by rfl) ⟨69798, by rfl⟩ : syracuseStep 2978069 = 139597) (by norm_num)
theorem B1985379 : Blo 1983435 1985379 := bstep (se 1 (by rfl) ⟨1489034, by rfl⟩ : syracuseStep 1985379 = 2978069) B2978069
theorem B8159717 : Blo 1983435 8159717 := bbase (se 4 (by rfl) ⟨764973, by rfl⟩ : syracuseStep 8159717 = 1529947) (by norm_num)
theorem B5439811 : Blo 1983435 5439811 := bstep (se 1 (by rfl) ⟨4079858, by rfl⟩ : syracuseStep 5439811 = 8159717) B8159717
theorem B7253081 : Blo 1983435 7253081 := bstep (se 2 (by rfl) ⟨2719905, by rfl⟩ : syracuseStep 7253081 = 5439811) B5439811
theorem B4835387 : Blo 1983435 4835387 := bstep (se 1 (by rfl) ⟨3626540, by rfl⟩ : syracuseStep 4835387 = 7253081) B7253081
theorem B12894365 : Blo 1983435 12894365 := bstep (se 3 (by rfl) ⟨2417693, by rfl⟩ : syracuseStep 12894365 = 4835387) B4835387
theorem B8596243 : Blo 1983435 8596243 := bstep (se 1 (by rfl) ⟨6447182, by rfl⟩ : syracuseStep 8596243 = 12894365) B12894365
theorem B11461657 : Blo 1983435 11461657 := bstep (se 2 (by rfl) ⟨4298121, by rfl⟩ : syracuseStep 11461657 = 8596243) B8596243
theorem B15282209 : Blo 1983435 15282209 := bstep (se 2 (by rfl) ⟨5730828, by rfl⟩ : syracuseStep 15282209 = 11461657) B11461657
theorem B40752557 : Blo 1983435 40752557 := bstep (se 3 (by rfl) ⟨7641104, by rfl⟩ : syracuseStep 40752557 = 15282209) B15282209
theorem B27168371 : Blo 1983435 27168371 := bstep (se 1 (by rfl) ⟨20376278, by rfl⟩ : syracuseStep 27168371 = 40752557) B40752557
theorem B18112247 : Blo 1983435 18112247 := bstep (se 1 (by rfl) ⟨13584185, by rfl⟩ : syracuseStep 18112247 = 27168371) B27168371
theorem B12074831 : Blo 1983435 12074831 := bstep (se 1 (by rfl) ⟨9056123, by rfl⟩ : syracuseStep 12074831 = 18112247) B18112247
theorem B8049887 : Blo 1983435 8049887 := bstep (se 1 (by rfl) ⟨6037415, by rfl⟩ : syracuseStep 8049887 = 12074831) B12074831
theorem B5366591 : Blo 1983435 5366591 := bstep (se 1 (by rfl) ⟨4024943, by rfl⟩ : syracuseStep 5366591 = 8049887) B8049887
theorem B3577727 : Blo 1983435 3577727 := bstep (se 1 (by rfl) ⟨2683295, by rfl⟩ : syracuseStep 3577727 = 5366591) B5366591
theorem B9540605 : Blo 1983435 9540605 := bstep (se 3 (by rfl) ⟨1788863, by rfl⟩ : syracuseStep 9540605 = 3577727) B3577727
theorem B25441613 : Blo 1983435 25441613 := bstep (se 3 (by rfl) ⟨4770302, by rfl⟩ : syracuseStep 25441613 = 9540605) B9540605
theorem B16961075 : Blo 1983435 16961075 := bstep (se 1 (by rfl) ⟨12720806, by rfl⟩ : syracuseStep 16961075 = 25441613) B25441613
theorem B11307383 : Blo 1983435 11307383 := bstep (se 1 (by rfl) ⟨8480537, by rfl⟩ : syracuseStep 11307383 = 16961075) B16961075
theorem B7538255 : Blo 1983435 7538255 := bstep (se 1 (by rfl) ⟨5653691, by rfl⟩ : syracuseStep 7538255 = 11307383) B11307383
theorem B5025503 : Blo 1983435 5025503 := bstep (se 1 (by rfl) ⟨3769127, by rfl⟩ : syracuseStep 5025503 = 7538255) B7538255
theorem B3350335 : Blo 1983435 3350335 := bstep (se 1 (by rfl) ⟨2512751, by rfl⟩ : syracuseStep 3350335 = 5025503) B5025503
theorem B4467113 : Blo 1983435 4467113 := bstep (se 2 (by rfl) ⟨1675167, by rfl⟩ : syracuseStep 4467113 = 3350335) B3350335
theorem B2978075 : Blo 1983435 2978075 := bstep (se 1 (by rfl) ⟨2233556, by rfl⟩ : syracuseStep 2978075 = 4467113) B4467113
theorem B1985383 : Blo 1983435 1985383 := bstep (se 1 (by rfl) ⟨1489037, by rfl⟩ : syracuseStep 1985383 = 2978075) B2978075
theorem B2233561 : Blo 1983435 2233561 := bbase (se 2 (by rfl) ⟨837585, by rfl⟩ : syracuseStep 2233561 = 1675171) (by norm_num)
theorem B2978081 : Blo 1983435 2978081 := bstep (se 2 (by rfl) ⟨1116780, by rfl⟩ : syracuseStep 2978081 = 2233561) B2233561
theorem B1985387 : Blo 1983435 1985387 := bstep (se 1 (by rfl) ⟨1489040, by rfl⟩ : syracuseStep 1985387 = 2978081) B2978081
theorem B2264041 : Blo 1983435 2264041 := bbase (se 2 (by rfl) ⟨849015, by rfl⟩ : syracuseStep 2264041 = 1698031) (by norm_num)
theorem B3018721 : Blo 1983435 3018721 := bstep (se 2 (by rfl) ⟨1132020, by rfl⟩ : syracuseStep 3018721 = 2264041) B2264041
theorem B4024961 : Blo 1983435 4024961 := bstep (se 2 (by rfl) ⟨1509360, by rfl⟩ : syracuseStep 4024961 = 3018721) B3018721
theorem B2683307 : Blo 1983435 2683307 := bstep (se 1 (by rfl) ⟨2012480, by rfl⟩ : syracuseStep 2683307 = 4024961) B4024961
theorem B7155485 : Blo 1983435 7155485 := bstep (se 3 (by rfl) ⟨1341653, by rfl⟩ : syracuseStep 7155485 = 2683307) B2683307
theorem B4770323 : Blo 1983435 4770323 := bstep (se 1 (by rfl) ⟨3577742, by rfl⟩ : syracuseStep 4770323 = 7155485) B7155485
theorem B3180215 : Blo 1983435 3180215 := bstep (se 1 (by rfl) ⟨2385161, by rfl⟩ : syracuseStep 3180215 = 4770323) B4770323
theorem B2120143 : Blo 1983435 2120143 := bstep (se 1 (by rfl) ⟨1590107, by rfl⟩ : syracuseStep 2120143 = 3180215) B3180215
theorem B2826857 : Blo 1983435 2826857 := bstep (se 2 (by rfl) ⟨1060071, by rfl⟩ : syracuseStep 2826857 = 2120143) B2120143
theorem B7538285 : Blo 1983435 7538285 := bstep (se 3 (by rfl) ⟨1413428, by rfl⟩ : syracuseStep 7538285 = 2826857) B2826857
theorem B5025523 : Blo 1983435 5025523 := bstep (se 1 (by rfl) ⟨3769142, by rfl⟩ : syracuseStep 5025523 = 7538285) B7538285
theorem B6700697 : Blo 1983435 6700697 := bstep (se 2 (by rfl) ⟨2512761, by rfl⟩ : syracuseStep 6700697 = 5025523) B5025523
theorem B4467131 : Blo 1983435 4467131 := bstep (se 1 (by rfl) ⟨3350348, by rfl⟩ : syracuseStep 4467131 = 6700697) B6700697
theorem B2978087 : Blo 1983435 2978087 := bstep (se 1 (by rfl) ⟨2233565, by rfl⟩ : syracuseStep 2978087 = 4467131) B4467131
theorem B1985391 : Blo 1983435 1985391 := bstep (se 1 (by rfl) ⟨1489043, by rfl⟩ : syracuseStep 1985391 = 2978087) B2978087
theorem B2978093 : Blo 1983435 2978093 := bbase (se 3 (by rfl) ⟨558392, by rfl⟩ : syracuseStep 2978093 = 1116785) (by norm_num)
theorem B1985395 : Blo 1983435 1985395 := bstep (se 1 (by rfl) ⟨1489046, by rfl⟩ : syracuseStep 1985395 = 2978093) B2978093
theorem B4467149 : Blo 1983435 4467149 := bbase (se 3 (by rfl) ⟨837590, by rfl⟩ : syracuseStep 4467149 = 1675181) (by norm_num)
theorem B2978099 : Blo 1983435 2978099 := bstep (se 1 (by rfl) ⟨2233574, by rfl⟩ : syracuseStep 2978099 = 4467149) B4467149
theorem B1985399 : Blo 1983435 1985399 := bstep (se 1 (by rfl) ⟨1489049, by rfl⟩ : syracuseStep 1985399 = 2978099) B2978099
theorem B2512777 : Blo 1983435 2512777 := bbase (se 2 (by rfl) ⟨942291, by rfl⟩ : syracuseStep 2512777 = 1884583) (by norm_num)
theorem B3350369 : Blo 1983435 3350369 := bstep (se 2 (by rfl) ⟨1256388, by rfl⟩ : syracuseStep 3350369 = 2512777) B2512777
theorem B2233579 : Blo 1983435 2233579 := bstep (se 1 (by rfl) ⟨1675184, by rfl⟩ : syracuseStep 2233579 = 3350369) B3350369
theorem B2978105 : Blo 1983435 2978105 := bstep (se 2 (by rfl) ⟨1116789, by rfl⟩ : syracuseStep 2978105 = 2233579) B2233579
theorem B1985403 : Blo 1983435 1985403 := bstep (se 1 (by rfl) ⟨1489052, by rfl⟩ : syracuseStep 1985403 = 2978105) B2978105
theorem B15282389 : Blo 1983435 15282389 := bbase (se 7 (by rfl) ⟨179090, by rfl⟩ : syracuseStep 15282389 = 358181) (by norm_num)
theorem B40753037 : Blo 1983435 40753037 := bstep (se 3 (by rfl) ⟨7641194, by rfl⟩ : syracuseStep 40753037 = 15282389) B15282389
theorem B27168691 : Blo 1983435 27168691 := bstep (se 1 (by rfl) ⟨20376518, by rfl⟩ : syracuseStep 27168691 = 40753037) B40753037
theorem B36224921 : Blo 1983435 36224921 := bstep (se 2 (by rfl) ⟨13584345, by rfl⟩ : syracuseStep 36224921 = 27168691) B27168691
theorem B96599789 : Blo 1983435 96599789 := bstep (se 3 (by rfl) ⟨18112460, by rfl⟩ : syracuseStep 96599789 = 36224921) B36224921
theorem B64399859 : Blo 1983435 64399859 := bstep (se 1 (by rfl) ⟨48299894, by rfl⟩ : syracuseStep 64399859 = 96599789) B96599789
theorem B42933239 : Blo 1983435 42933239 := bstep (se 1 (by rfl) ⟨32199929, by rfl⟩ : syracuseStep 42933239 = 64399859) B64399859
theorem B28622159 : Blo 1983435 28622159 := bstep (se 1 (by rfl) ⟨21466619, by rfl⟩ : syracuseStep 28622159 = 42933239) B42933239
theorem B19081439 : Blo 1983435 19081439 := bstep (se 1 (by rfl) ⟨14311079, by rfl⟩ : syracuseStep 19081439 = 28622159) B28622159
theorem B12720959 : Blo 1983435 12720959 := bstep (se 1 (by rfl) ⟨9540719, by rfl⟩ : syracuseStep 12720959 = 19081439) B19081439
theorem B8480639 : Blo 1983435 8480639 := bstep (se 1 (by rfl) ⟨6360479, by rfl⟩ : syracuseStep 8480639 = 12720959) B12720959
theorem B22615037 : Blo 1983435 22615037 := bstep (se 3 (by rfl) ⟨4240319, by rfl⟩ : syracuseStep 22615037 = 8480639) B8480639
theorem B15076691 : Blo 1983435 15076691 := bstep (se 1 (by rfl) ⟨11307518, by rfl⟩ : syracuseStep 15076691 = 22615037) B22615037
theorem B10051127 : Blo 1983435 10051127 := bstep (se 1 (by rfl) ⟨7538345, by rfl⟩ : syracuseStep 10051127 = 15076691) B15076691
theorem B6700751 : Blo 1983435 6700751 := bstep (se 1 (by rfl) ⟨5025563, by rfl⟩ : syracuseStep 6700751 = 10051127) B10051127
theorem B4467167 : Blo 1983435 4467167 := bstep (se 1 (by rfl) ⟨3350375, by rfl⟩ : syracuseStep 4467167 = 6700751) B6700751
theorem B2978111 : Blo 1983435 2978111 := bstep (se 1 (by rfl) ⟨2233583, by rfl⟩ : syracuseStep 2978111 = 4467167) B4467167
theorem B1985407 : Blo 1983435 1985407 := bstep (se 1 (by rfl) ⟨1489055, by rfl⟩ : syracuseStep 1985407 = 2978111) B2978111
theorem B2978117 : Blo 1983435 2978117 := bbase (se 4 (by rfl) ⟨279198, by rfl⟩ : syracuseStep 2978117 = 558397) (by norm_num)
theorem B1985411 : Blo 1983435 1985411 := bstep (se 1 (by rfl) ⟨1489058, by rfl⟩ : syracuseStep 1985411 = 2978117) B2978117
theorem B3350389 : Blo 1983435 3350389 := bbase (se 5 (by rfl) ⟨157049, by rfl⟩ : syracuseStep 3350389 = 314099) (by norm_num)
theorem B4467185 : Blo 1983435 4467185 := bstep (se 2 (by rfl) ⟨1675194, by rfl⟩ : syracuseStep 4467185 = 3350389) B3350389
theorem B2978123 : Blo 1983435 2978123 := bstep (se 1 (by rfl) ⟨2233592, by rfl⟩ : syracuseStep 2978123 = 4467185) B4467185
theorem B1985415 : Blo 1983435 1985415 := bstep (se 1 (by rfl) ⟨1489061, by rfl⟩ : syracuseStep 1985415 = 2978123) B2978123
theorem B2233597 : Blo 1983435 2233597 := bbase (se 3 (by rfl) ⟨418799, by rfl⟩ : syracuseStep 2233597 = 837599) (by norm_num)
theorem B2978129 : Blo 1983435 2978129 := bstep (se 2 (by rfl) ⟨1116798, by rfl⟩ : syracuseStep 2978129 = 2233597) B2233597
theorem B1985419 : Blo 1983435 1985419 := bstep (se 1 (by rfl) ⟨1489064, by rfl⟩ : syracuseStep 1985419 = 2978129) B2978129
theorem B6700805 : Blo 1983435 6700805 := bbase (se 4 (by rfl) ⟨628200, by rfl⟩ : syracuseStep 6700805 = 1256401) (by norm_num)
theorem B4467203 : Blo 1983435 4467203 := bstep (se 1 (by rfl) ⟨3350402, by rfl⟩ : syracuseStep 4467203 = 6700805) B6700805
theorem B2978135 : Blo 1983435 2978135 := bstep (se 1 (by rfl) ⟨2233601, by rfl⟩ : syracuseStep 2978135 = 4467203) B4467203
theorem B1985423 : Blo 1983435 1985423 := bstep (se 1 (by rfl) ⟨1489067, by rfl⟩ : syracuseStep 1985423 = 2978135) B2978135
theorem B2978141 : Blo 1983435 2978141 := bbase (se 3 (by rfl) ⟨558401, by rfl⟩ : syracuseStep 2978141 = 1116803) (by norm_num)
theorem B1985427 : Blo 1983435 1985427 := bstep (se 1 (by rfl) ⟨1489070, by rfl⟩ : syracuseStep 1985427 = 2978141) B2978141
theorem B4467221 : Blo 1983435 4467221 := bbase (se 6 (by rfl) ⟨104700, by rfl⟩ : syracuseStep 4467221 = 209401) (by norm_num)
theorem B2978147 : Blo 1983435 2978147 := bstep (se 1 (by rfl) ⟨2233610, by rfl⟩ : syracuseStep 2978147 = 4467221) B4467221
theorem B1985431 : Blo 1983435 1985431 := bstep (se 1 (by rfl) ⟨1489073, by rfl⟩ : syracuseStep 1985431 = 2978147) B2978147
theorem B7538453 : Blo 1983435 7538453 := bbase (se 6 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 7538453 = 353365) (by norm_num)
theorem B5025635 : Blo 1983435 5025635 := bstep (se 1 (by rfl) ⟨3769226, by rfl⟩ : syracuseStep 5025635 = 7538453) B7538453
theorem B3350423 : Blo 1983435 3350423 := bstep (se 1 (by rfl) ⟨2512817, by rfl⟩ : syracuseStep 3350423 = 5025635) B5025635
theorem B2233615 : Blo 1983435 2233615 := bstep (se 1 (by rfl) ⟨1675211, by rfl⟩ : syracuseStep 2233615 = 3350423) B3350423
theorem B2978153 : Blo 1983435 2978153 := bstep (se 2 (by rfl) ⟨1116807, by rfl⟩ : syracuseStep 2978153 = 2233615) B2233615
theorem B1985435 : Blo 1983435 1985435 := bstep (se 1 (by rfl) ⟨1489076, by rfl⟩ : syracuseStep 1985435 = 2978153) B2978153
theorem C0 (j : ℕ) (h1 : 495858 ≤ j) (h2 : j ≤ 496358) : Blo 1983435 (4 * j + 3) := by
  interval_cases j
  · exact B1983435
  · exact B1983439
  · exact B1983443
  · exact B1983447
  · exact B1983451
  · exact B1983455
  · exact B1983459
  · exact B1983463
  · exact B1983467
  · exact B1983471
  · exact B1983475
  · exact B1983479
  · exact B1983483
  · exact B1983487
  · exact B1983491
  · exact B1983495
  · exact B1983499
  · exact B1983503
  · exact B1983507
  · exact B1983511
  · exact B1983515
  · exact B1983519
  · exact B1983523
  · exact B1983527
  · exact B1983531
  · exact B1983535
  · exact B1983539
  · exact B1983543
  · exact B1983547
  · exact B1983551
  · exact B1983555
  · exact B1983559
  · exact B1983563
  · exact B1983567
  · exact B1983571
  · exact B1983575
  · exact B1983579
  · exact B1983583
  · exact B1983587
  · exact B1983591
  · exact B1983595
  · exact B1983599
  · exact B1983603
  · exact B1983607
  · exact B1983611
  · exact B1983615
  · exact B1983619
  · exact B1983623
  · exact B1983627
  · exact B1983631
  · exact B1983635
  · exact B1983639
  · exact B1983643
  · exact B1983647
  · exact B1983651
  · exact B1983655
  · exact B1983659
  · exact B1983663
  · exact B1983667
  · exact B1983671
  · exact B1983675
  · exact B1983679
  · exact B1983683
  · exact B1983687
  · exact B1983691
  · exact B1983695
  · exact B1983699
  · exact B1983703
  · exact B1983707
  · exact B1983711
  · exact B1983715
  · exact B1983719
  · exact B1983723
  · exact B1983727
  · exact B1983731
  · exact B1983735
  · exact B1983739
  · exact B1983743
  · exact B1983747
  · exact B1983751
  · exact B1983755
  · exact B1983759
  · exact B1983763
  · exact B1983767
  · exact B1983771
  · exact B1983775
  · exact B1983779
  · exact B1983783
  · exact B1983787
  · exact B1983791
  · exact B1983795
  · exact B1983799
  · exact B1983803
  · exact B1983807
  · exact B1983811
  · exact B1983815
  · exact B1983819
  · exact B1983823
  · exact B1983827
  · exact B1983831
  · exact B1983835
  · exact B1983839
  · exact B1983843
  · exact B1983847
  · exact B1983851
  · exact B1983855
  · exact B1983859
  · exact B1983863
  · exact B1983867
  · exact B1983871
  · exact B1983875
  · exact B1983879
  · exact B1983883
  · exact B1983887
  · exact B1983891
  · exact B1983895
  · exact B1983899
  · exact B1983903
  · exact B1983907
  · exact B1983911
  · exact B1983915
  · exact B1983919
  · exact B1983923
  · exact B1983927
  · exact B1983931
  · exact B1983935
  · exact B1983939
  · exact B1983943
  · exact B1983947
  · exact B1983951
  · exact B1983955
  · exact B1983959
  · exact B1983963
  · exact B1983967
  · exact B1983971
  · exact B1983975
  · exact B1983979
  · exact B1983983
  · exact B1983987
  · exact B1983991
  · exact B1983995
  · exact B1983999
  · exact B1984003
  · exact B1984007
  · exact B1984011
  · exact B1984015
  · exact B1984019
  · exact B1984023
  · exact B1984027
  · exact B1984031
  · exact B1984035
  · exact B1984039
  · exact B1984043
  · exact B1984047
  · exact B1984051
  · exact B1984055
  · exact B1984059
  · exact B1984063
  · exact B1984067
  · exact B1984071
  · exact B1984075
  · exact B1984079
  · exact B1984083
  · exact B1984087
  · exact B1984091
  · exact B1984095
  · exact B1984099
  · exact B1984103
  · exact B1984107
  · exact B1984111
  · exact B1984115
  · exact B1984119
  · exact B1984123
  · exact B1984127
  · exact B1984131
  · exact B1984135
  · exact B1984139
  · exact B1984143
  · exact B1984147
  · exact B1984151
  · exact B1984155
  · exact B1984159
  · exact B1984163
  · exact B1984167
  · exact B1984171
  · exact B1984175
  · exact B1984179
  · exact B1984183
  · exact B1984187
  · exact B1984191
  · exact B1984195
  · exact B1984199
  · exact B1984203
  · exact B1984207
  · exact B1984211
  · exact B1984215
  · exact B1984219
  · exact B1984223
  · exact B1984227
  · exact B1984231
  · exact B1984235
  · exact B1984239
  · exact B1984243
  · exact B1984247
  · exact B1984251
  · exact B1984255
  · exact B1984259
  · exact B1984263
  · exact B1984267
  · exact B1984271
  · exact B1984275
  · exact B1984279
  · exact B1984283
  · exact B1984287
  · exact B1984291
  · exact B1984295
  · exact B1984299
  · exact B1984303
  · exact B1984307
  · exact B1984311
  · exact B1984315
  · exact B1984319
  · exact B1984323
  · exact B1984327
  · exact B1984331
  · exact B1984335
  · exact B1984339
  · exact B1984343
  · exact B1984347
  · exact B1984351
  · exact B1984355
  · exact B1984359
  · exact B1984363
  · exact B1984367
  · exact B1984371
  · exact B1984375
  · exact B1984379
  · exact B1984383
  · exact B1984387
  · exact B1984391
  · exact B1984395
  · exact B1984399
  · exact B1984403
  · exact B1984407
  · exact B1984411
  · exact B1984415
  · exact B1984419
  · exact B1984423
  · exact B1984427
  · exact B1984431
  · exact B1984435
  · exact B1984439
  · exact B1984443
  · exact B1984447
  · exact B1984451
  · exact B1984455
  · exact B1984459
  · exact B1984463
  · exact B1984467
  · exact B1984471
  · exact B1984475
  · exact B1984479
  · exact B1984483
  · exact B1984487
  · exact B1984491
  · exact B1984495
  · exact B1984499
  · exact B1984503
  · exact B1984507
  · exact B1984511
  · exact B1984515
  · exact B1984519
  · exact B1984523
  · exact B1984527
  · exact B1984531
  · exact B1984535
  · exact B1984539
  · exact B1984543
  · exact B1984547
  · exact B1984551
  · exact B1984555
  · exact B1984559
  · exact B1984563
  · exact B1984567
  · exact B1984571
  · exact B1984575
  · exact B1984579
  · exact B1984583
  · exact B1984587
  · exact B1984591
  · exact B1984595
  · exact B1984599
  · exact B1984603
  · exact B1984607
  · exact B1984611
  · exact B1984615
  · exact B1984619
  · exact B1984623
  · exact B1984627
  · exact B1984631
  · exact B1984635
  · exact B1984639
  · exact B1984643
  · exact B1984647
  · exact B1984651
  · exact B1984655
  · exact B1984659
  · exact B1984663
  · exact B1984667
  · exact B1984671
  · exact B1984675
  · exact B1984679
  · exact B1984683
  · exact B1984687
  · exact B1984691
  · exact B1984695
  · exact B1984699
  · exact B1984703
  · exact B1984707
  · exact B1984711
  · exact B1984715
  · exact B1984719
  · exact B1984723
  · exact B1984727
  · exact B1984731
  · exact B1984735
  · exact B1984739
  · exact B1984743
  · exact B1984747
  · exact B1984751
  · exact B1984755
  · exact B1984759
  · exact B1984763
  · exact B1984767
  · exact B1984771
  · exact B1984775
  · exact B1984779
  · exact B1984783
  · exact B1984787
  · exact B1984791
  · exact B1984795
  · exact B1984799
  · exact B1984803
  · exact B1984807
  · exact B1984811
  · exact B1984815
  · exact B1984819
  · exact B1984823
  · exact B1984827
  · exact B1984831
  · exact B1984835
  · exact B1984839
  · exact B1984843
  · exact B1984847
  · exact B1984851
  · exact B1984855
  · exact B1984859
  · exact B1984863
  · exact B1984867
  · exact B1984871
  · exact B1984875
  · exact B1984879
  · exact B1984883
  · exact B1984887
  · exact B1984891
  · exact B1984895
  · exact B1984899
  · exact B1984903
  · exact B1984907
  · exact B1984911
  · exact B1984915
  · exact B1984919
  · exact B1984923
  · exact B1984927
  · exact B1984931
  · exact B1984935
  · exact B1984939
  · exact B1984943
  · exact B1984947
  · exact B1984951
  · exact B1984955
  · exact B1984959
  · exact B1984963
  · exact B1984967
  · exact B1984971
  · exact B1984975
  · exact B1984979
  · exact B1984983
  · exact B1984987
  · exact B1984991
  · exact B1984995
  · exact B1984999
  · exact B1985003
  · exact B1985007
  · exact B1985011
  · exact B1985015
  · exact B1985019
  · exact B1985023
  · exact B1985027
  · exact B1985031
  · exact B1985035
  · exact B1985039
  · exact B1985043
  · exact B1985047
  · exact B1985051
  · exact B1985055
  · exact B1985059
  · exact B1985063
  · exact B1985067
  · exact B1985071
  · exact B1985075
  · exact B1985079
  · exact B1985083
  · exact B1985087
  · exact B1985091
  · exact B1985095
  · exact B1985099
  · exact B1985103
  · exact B1985107
  · exact B1985111
  · exact B1985115
  · exact B1985119
  · exact B1985123
  · exact B1985127
  · exact B1985131
  · exact B1985135
  · exact B1985139
  · exact B1985143
  · exact B1985147
  · exact B1985151
  · exact B1985155
  · exact B1985159
  · exact B1985163
  · exact B1985167
  · exact B1985171
  · exact B1985175
  · exact B1985179
  · exact B1985183
  · exact B1985187
  · exact B1985191
  · exact B1985195
  · exact B1985199
  · exact B1985203
  · exact B1985207
  · exact B1985211
  · exact B1985215
  · exact B1985219
  · exact B1985223
  · exact B1985227
  · exact B1985231
  · exact B1985235
  · exact B1985239
  · exact B1985243
  · exact B1985247
  · exact B1985251
  · exact B1985255
  · exact B1985259
  · exact B1985263
  · exact B1985267
  · exact B1985271
  · exact B1985275
  · exact B1985279
  · exact B1985283
  · exact B1985287
  · exact B1985291
  · exact B1985295
  · exact B1985299
  · exact B1985303
  · exact B1985307
  · exact B1985311
  · exact B1985315
  · exact B1985319
  · exact B1985323
  · exact B1985327
  · exact B1985331
  · exact B1985335
  · exact B1985339
  · exact B1985343
  · exact B1985347
  · exact B1985351
  · exact B1985355
  · exact B1985359
  · exact B1985363
  · exact B1985367
  · exact B1985371
  · exact B1985375
  · exact B1985379
  · exact B1985383
  · exact B1985387
  · exact B1985391
  · exact B1985395
  · exact B1985399
  · exact B1985403
  · exact B1985407
  · exact B1985411
  · exact B1985415
  · exact B1985419
  · exact B1985423
  · exact B1985427
  · exact B1985431
  · exact B1985435
theorem solution (m : ℕ) (hlo : 1983435 ≤ m) (hhi : m ≤ 1985435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 495858 ≤ j := by omega
    have hj2 : j ≤ 496358 := by omega
    have hb : Blo 1983435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
