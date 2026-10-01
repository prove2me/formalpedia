-- Prove2me | solution 1 for syracuse_descends_range_1903435_1905435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:53.662101+00:00
-- url     : https://prove2.me/submissions/e62be950-8e47-46f7-baed-fa81687f6f2a

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

theorem B2141365 : Blo 1903435 2141365 := bbase (se 5 (by rfl) ⟨100376, by rfl⟩ : syracuseStep 2141365 = 200753) (by norm_num)
theorem B2855153 : Blo 1903435 2855153 := bstep (se 2 (by rfl) ⟨1070682, by rfl⟩ : syracuseStep 2855153 = 2141365) B2141365
theorem B1903435 : Blo 1903435 1903435 := bstep (se 1 (by rfl) ⟨1427576, by rfl⟩ : syracuseStep 1903435 = 2855153) B2855153
theorem B2409041 : Blo 1903435 2409041 := bbase (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) (by norm_num)
theorem B6424109 : Blo 1903435 6424109 := bstep (se 3 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 6424109 = 2409041) B2409041
theorem B4282739 : Blo 1903435 4282739 := bstep (se 1 (by rfl) ⟨3212054, by rfl⟩ : syracuseStep 4282739 = 6424109) B6424109
theorem B2855159 : Blo 1903435 2855159 := bstep (se 1 (by rfl) ⟨2141369, by rfl⟩ : syracuseStep 2855159 = 4282739) B4282739
theorem B1903439 : Blo 1903435 1903439 := bstep (se 1 (by rfl) ⟨1427579, by rfl⟩ : syracuseStep 1903439 = 2855159) B2855159
theorem B2855165 : Blo 1903435 2855165 := bbase (se 3 (by rfl) ⟨535343, by rfl⟩ : syracuseStep 2855165 = 1070687) (by norm_num)
theorem B1903443 : Blo 1903435 1903443 := bstep (se 1 (by rfl) ⟨1427582, by rfl⟩ : syracuseStep 1903443 = 2855165) B2855165
theorem B4282757 : Blo 1903435 4282757 := bbase (se 4 (by rfl) ⟨401508, by rfl⟩ : syracuseStep 4282757 = 803017) (by norm_num)
theorem B2855171 : Blo 1903435 2855171 := bstep (se 1 (by rfl) ⟨2141378, by rfl⟩ : syracuseStep 2855171 = 4282757) B4282757
theorem B1903447 : Blo 1903435 1903447 := bstep (se 1 (by rfl) ⟨1427585, by rfl⟩ : syracuseStep 1903447 = 2855171) B2855171
theorem B2710189 : Blo 1903435 2710189 := bbase (se 3 (by rfl) ⟨508160, by rfl⟩ : syracuseStep 2710189 = 1016321) (by norm_num)
theorem B3613585 : Blo 1903435 3613585 := bstep (se 2 (by rfl) ⟨1355094, by rfl⟩ : syracuseStep 3613585 = 2710189) B2710189
theorem B4818113 : Blo 1903435 4818113 := bstep (se 2 (by rfl) ⟨1806792, by rfl⟩ : syracuseStep 4818113 = 3613585) B3613585
theorem B3212075 : Blo 1903435 3212075 := bstep (se 1 (by rfl) ⟨2409056, by rfl⟩ : syracuseStep 3212075 = 4818113) B4818113
theorem B2141383 : Blo 1903435 2141383 := bstep (se 1 (by rfl) ⟨1606037, by rfl⟩ : syracuseStep 2141383 = 3212075) B3212075
theorem B2855177 : Blo 1903435 2855177 := bstep (se 2 (by rfl) ⟨1070691, by rfl⟩ : syracuseStep 2855177 = 2141383) B2141383
theorem B1903451 : Blo 1903435 1903451 := bstep (se 1 (by rfl) ⟨1427588, by rfl⟩ : syracuseStep 1903451 = 2855177) B2855177
theorem B9636245 : Blo 1903435 9636245 := bbase (se 6 (by rfl) ⟨225849, by rfl⟩ : syracuseStep 9636245 = 451699) (by norm_num)
theorem B6424163 : Blo 1903435 6424163 := bstep (se 1 (by rfl) ⟨4818122, by rfl⟩ : syracuseStep 6424163 = 9636245) B9636245
theorem B4282775 : Blo 1903435 4282775 := bstep (se 1 (by rfl) ⟨3212081, by rfl⟩ : syracuseStep 4282775 = 6424163) B6424163
theorem B2855183 : Blo 1903435 2855183 := bstep (se 1 (by rfl) ⟨2141387, by rfl⟩ : syracuseStep 2855183 = 4282775) B4282775
theorem B1903455 : Blo 1903435 1903455 := bstep (se 1 (by rfl) ⟨1427591, by rfl⟩ : syracuseStep 1903455 = 2855183) B2855183
theorem B2855189 : Blo 1903435 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B1903459 : Blo 1903435 1903459 := bstep (se 1 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 1903459 = 2855189) B2855189
theorem B5145157 : Blo 1903435 5145157 := bbase (se 4 (by rfl) ⟨482358, by rfl⟩ : syracuseStep 5145157 = 964717) (by norm_num)
theorem B6860209 : Blo 1903435 6860209 := bstep (se 2 (by rfl) ⟨2572578, by rfl⟩ : syracuseStep 6860209 = 5145157) B5145157
theorem B9146945 : Blo 1903435 9146945 := bstep (se 2 (by rfl) ⟨3430104, by rfl⟩ : syracuseStep 9146945 = 6860209) B6860209
theorem B24391853 : Blo 1903435 24391853 := bstep (se 3 (by rfl) ⟨4573472, by rfl⟩ : syracuseStep 24391853 = 9146945) B9146945
theorem B16261235 : Blo 1903435 16261235 := bstep (se 1 (by rfl) ⟨12195926, by rfl⟩ : syracuseStep 16261235 = 24391853) B24391853
theorem B10840823 : Blo 1903435 10840823 := bstep (se 1 (by rfl) ⟨8130617, by rfl⟩ : syracuseStep 10840823 = 16261235) B16261235
theorem B7227215 : Blo 1903435 7227215 := bstep (se 1 (by rfl) ⟨5420411, by rfl⟩ : syracuseStep 7227215 = 10840823) B10840823
theorem B4818143 : Blo 1903435 4818143 := bstep (se 1 (by rfl) ⟨3613607, by rfl⟩ : syracuseStep 4818143 = 7227215) B7227215
theorem B3212095 : Blo 1903435 3212095 := bstep (se 1 (by rfl) ⟨2409071, by rfl⟩ : syracuseStep 3212095 = 4818143) B4818143
theorem B4282793 : Blo 1903435 4282793 := bstep (se 2 (by rfl) ⟨1606047, by rfl⟩ : syracuseStep 4282793 = 3212095) B3212095
theorem B2855195 : Blo 1903435 2855195 := bstep (se 1 (by rfl) ⟨2141396, by rfl⟩ : syracuseStep 2855195 = 4282793) B4282793
theorem B1903463 : Blo 1903435 1903463 := bstep (se 1 (by rfl) ⟨1427597, by rfl⟩ : syracuseStep 1903463 = 2855195) B2855195
theorem B2141401 : Blo 1903435 2141401 := bbase (se 2 (by rfl) ⟨803025, by rfl⟩ : syracuseStep 2141401 = 1606051) (by norm_num)
theorem B2855201 : Blo 1903435 2855201 := bstep (se 2 (by rfl) ⟨1070700, by rfl⟩ : syracuseStep 2855201 = 2141401) B2141401
theorem B1903467 : Blo 1903435 1903467 := bstep (se 1 (by rfl) ⟨1427600, by rfl⟩ : syracuseStep 1903467 = 2855201) B2855201
theorem B4573493 : Blo 1903435 4573493 := bbase (se 5 (by rfl) ⟨214382, by rfl⟩ : syracuseStep 4573493 = 428765) (by norm_num)
theorem B3048995 : Blo 1903435 3048995 := bstep (se 1 (by rfl) ⟨2286746, by rfl⟩ : syracuseStep 3048995 = 4573493) B4573493
theorem B2032663 : Blo 1903435 2032663 := bstep (se 1 (by rfl) ⟨1524497, by rfl⟩ : syracuseStep 2032663 = 3048995) B3048995
theorem B2710217 : Blo 1903435 2710217 := bstep (se 2 (by rfl) ⟨1016331, by rfl⟩ : syracuseStep 2710217 = 2032663) B2032663
theorem B7227245 : Blo 1903435 7227245 := bstep (se 3 (by rfl) ⟨1355108, by rfl⟩ : syracuseStep 7227245 = 2710217) B2710217
theorem B4818163 : Blo 1903435 4818163 := bstep (se 1 (by rfl) ⟨3613622, by rfl⟩ : syracuseStep 4818163 = 7227245) B7227245
theorem B6424217 : Blo 1903435 6424217 := bstep (se 2 (by rfl) ⟨2409081, by rfl⟩ : syracuseStep 6424217 = 4818163) B4818163
theorem B4282811 : Blo 1903435 4282811 := bstep (se 1 (by rfl) ⟨3212108, by rfl⟩ : syracuseStep 4282811 = 6424217) B6424217
theorem B2855207 : Blo 1903435 2855207 := bstep (se 1 (by rfl) ⟨2141405, by rfl⟩ : syracuseStep 2855207 = 4282811) B4282811
theorem B1903471 : Blo 1903435 1903471 := bstep (se 1 (by rfl) ⟨1427603, by rfl⟩ : syracuseStep 1903471 = 2855207) B2855207
theorem B2855213 : Blo 1903435 2855213 := bbase (se 3 (by rfl) ⟨535352, by rfl⟩ : syracuseStep 2855213 = 1070705) (by norm_num)
theorem B1903475 : Blo 1903435 1903475 := bstep (se 1 (by rfl) ⟨1427606, by rfl⟩ : syracuseStep 1903475 = 2855213) B2855213
theorem B4282829 : Blo 1903435 4282829 := bbase (se 3 (by rfl) ⟨803030, by rfl⟩ : syracuseStep 4282829 = 1606061) (by norm_num)
theorem B2855219 : Blo 1903435 2855219 := bstep (se 1 (by rfl) ⟨2141414, by rfl⟩ : syracuseStep 2855219 = 4282829) B4282829
theorem B1903479 : Blo 1903435 1903479 := bstep (se 1 (by rfl) ⟨1427609, by rfl⟩ : syracuseStep 1903479 = 2855219) B2855219
theorem B2409097 : Blo 1903435 2409097 := bbase (se 2 (by rfl) ⟨903411, by rfl⟩ : syracuseStep 2409097 = 1806823) (by norm_num)
theorem B3212129 : Blo 1903435 3212129 := bstep (se 2 (by rfl) ⟨1204548, by rfl⟩ : syracuseStep 3212129 = 2409097) B2409097
theorem B2141419 : Blo 1903435 2141419 := bstep (se 1 (by rfl) ⟨1606064, by rfl⟩ : syracuseStep 2141419 = 3212129) B3212129
theorem B2855225 : Blo 1903435 2855225 := bstep (se 2 (by rfl) ⟨1070709, by rfl⟩ : syracuseStep 2855225 = 2141419) B2141419
theorem B1903483 : Blo 1903435 1903483 := bstep (se 1 (by rfl) ⟨1427612, by rfl⟩ : syracuseStep 1903483 = 2855225) B2855225
theorem B3964933 : Blo 1903435 3964933 := bbase (se 4 (by rfl) ⟨371712, by rfl⟩ : syracuseStep 3964933 = 743425) (by norm_num)
theorem B21146309 : Blo 1903435 21146309 := bstep (se 4 (by rfl) ⟨1982466, by rfl⟩ : syracuseStep 21146309 = 3964933) B3964933
theorem B14097539 : Blo 1903435 14097539 := bstep (se 1 (by rfl) ⟨10573154, by rfl⟩ : syracuseStep 14097539 = 21146309) B21146309
theorem B9398359 : Blo 1903435 9398359 := bstep (se 1 (by rfl) ⟨7048769, by rfl⟩ : syracuseStep 9398359 = 14097539) B14097539
theorem B12531145 : Blo 1903435 12531145 := bstep (se 2 (by rfl) ⟨4699179, by rfl⟩ : syracuseStep 12531145 = 9398359) B9398359
theorem B16708193 : Blo 1903435 16708193 := bstep (se 2 (by rfl) ⟨6265572, by rfl⟩ : syracuseStep 16708193 = 12531145) B12531145
theorem B11138795 : Blo 1903435 11138795 := bstep (se 1 (by rfl) ⟨8354096, by rfl⟩ : syracuseStep 11138795 = 16708193) B16708193
theorem B7425863 : Blo 1903435 7425863 := bstep (se 1 (by rfl) ⟨5569397, by rfl⟩ : syracuseStep 7425863 = 11138795) B11138795
theorem B4950575 : Blo 1903435 4950575 := bstep (se 1 (by rfl) ⟨3712931, by rfl⟩ : syracuseStep 4950575 = 7425863) B7425863
theorem B3300383 : Blo 1903435 3300383 := bstep (se 1 (by rfl) ⟨2475287, by rfl⟩ : syracuseStep 3300383 = 4950575) B4950575
theorem B2200255 : Blo 1903435 2200255 := bstep (se 1 (by rfl) ⟨1650191, by rfl⟩ : syracuseStep 2200255 = 3300383) B3300383
theorem B46938773 : Blo 1903435 46938773 := bstep (se 6 (by rfl) ⟨1100127, by rfl⟩ : syracuseStep 46938773 = 2200255) B2200255
theorem B31292515 : Blo 1903435 31292515 := bstep (se 1 (by rfl) ⟨23469386, by rfl⟩ : syracuseStep 31292515 = 46938773) B46938773
theorem B41723353 : Blo 1903435 41723353 := bstep (se 2 (by rfl) ⟨15646257, by rfl⟩ : syracuseStep 41723353 = 31292515) B31292515
theorem B55631137 : Blo 1903435 55631137 := bstep (se 2 (by rfl) ⟨20861676, by rfl⟩ : syracuseStep 55631137 = 41723353) B41723353
theorem B74174849 : Blo 1903435 74174849 := bstep (se 2 (by rfl) ⟨27815568, by rfl⟩ : syracuseStep 74174849 = 55631137) B55631137
theorem B49449899 : Blo 1903435 49449899 := bstep (se 1 (by rfl) ⟨37087424, by rfl⟩ : syracuseStep 49449899 = 74174849) B74174849
theorem B32966599 : Blo 1903435 32966599 := bstep (se 1 (by rfl) ⟨24724949, by rfl⟩ : syracuseStep 32966599 = 49449899) B49449899
theorem B43955465 : Blo 1903435 43955465 := bstep (se 2 (by rfl) ⟨16483299, by rfl⟩ : syracuseStep 43955465 = 32966599) B32966599
theorem B117214573 : Blo 1903435 117214573 := bstep (se 3 (by rfl) ⟨21977732, by rfl⟩ : syracuseStep 117214573 = 43955465) B43955465
theorem B156286097 : Blo 1903435 156286097 := bstep (se 2 (by rfl) ⟨58607286, by rfl⟩ : syracuseStep 156286097 = 117214573) B117214573
theorem B104190731 : Blo 1903435 104190731 := bstep (se 1 (by rfl) ⟨78143048, by rfl⟩ : syracuseStep 104190731 = 156286097) B156286097
theorem B69460487 : Blo 1903435 69460487 := bstep (se 1 (by rfl) ⟨52095365, by rfl⟩ : syracuseStep 69460487 = 104190731) B104190731
theorem B46306991 : Blo 1903435 46306991 := bstep (se 1 (by rfl) ⟨34730243, by rfl⟩ : syracuseStep 46306991 = 69460487) B69460487
theorem B30871327 : Blo 1903435 30871327 := bstep (se 1 (by rfl) ⟨23153495, by rfl⟩ : syracuseStep 30871327 = 46306991) B46306991
theorem B41161769 : Blo 1903435 41161769 := bstep (se 2 (by rfl) ⟨15435663, by rfl⟩ : syracuseStep 41161769 = 30871327) B30871327
theorem B27441179 : Blo 1903435 27441179 := bstep (se 1 (by rfl) ⟨20580884, by rfl⟩ : syracuseStep 27441179 = 41161769) B41161769
theorem B18294119 : Blo 1903435 18294119 := bstep (se 1 (by rfl) ⟨13720589, by rfl⟩ : syracuseStep 18294119 = 27441179) B27441179
theorem B12196079 : Blo 1903435 12196079 := bstep (se 1 (by rfl) ⟨9147059, by rfl⟩ : syracuseStep 12196079 = 18294119) B18294119
theorem B8130719 : Blo 1903435 8130719 := bstep (se 1 (by rfl) ⟨6098039, by rfl⟩ : syracuseStep 8130719 = 12196079) B12196079
theorem B21681917 : Blo 1903435 21681917 := bstep (se 3 (by rfl) ⟨4065359, by rfl⟩ : syracuseStep 21681917 = 8130719) B8130719
theorem B14454611 : Blo 1903435 14454611 := bstep (se 1 (by rfl) ⟨10840958, by rfl⟩ : syracuseStep 14454611 = 21681917) B21681917
theorem B9636407 : Blo 1903435 9636407 := bstep (se 1 (by rfl) ⟨7227305, by rfl⟩ : syracuseStep 9636407 = 14454611) B14454611
theorem B6424271 : Blo 1903435 6424271 := bstep (se 1 (by rfl) ⟨4818203, by rfl⟩ : syracuseStep 6424271 = 9636407) B9636407
theorem B4282847 : Blo 1903435 4282847 := bstep (se 1 (by rfl) ⟨3212135, by rfl⟩ : syracuseStep 4282847 = 6424271) B6424271
theorem B2855231 : Blo 1903435 2855231 := bstep (se 1 (by rfl) ⟨2141423, by rfl⟩ : syracuseStep 2855231 = 4282847) B4282847
theorem B1903487 : Blo 1903435 1903487 := bstep (se 1 (by rfl) ⟨1427615, by rfl⟩ : syracuseStep 1903487 = 2855231) B2855231
theorem B2855237 : Blo 1903435 2855237 := bbase (se 4 (by rfl) ⟨267678, by rfl⟩ : syracuseStep 2855237 = 535357) (by norm_num)
theorem B1903491 : Blo 1903435 1903491 := bstep (se 1 (by rfl) ⟨1427618, by rfl⟩ : syracuseStep 1903491 = 2855237) B2855237
theorem B3212149 : Blo 1903435 3212149 := bbase (se 5 (by rfl) ⟨150569, by rfl⟩ : syracuseStep 3212149 = 301139) (by norm_num)
theorem B4282865 : Blo 1903435 4282865 := bstep (se 2 (by rfl) ⟨1606074, by rfl⟩ : syracuseStep 4282865 = 3212149) B3212149
theorem B2855243 : Blo 1903435 2855243 := bstep (se 1 (by rfl) ⟨2141432, by rfl⟩ : syracuseStep 2855243 = 4282865) B4282865
theorem B1903495 : Blo 1903435 1903495 := bstep (se 1 (by rfl) ⟨1427621, by rfl⟩ : syracuseStep 1903495 = 2855243) B2855243
theorem B2141437 : Blo 1903435 2141437 := bbase (se 3 (by rfl) ⟨401519, by rfl⟩ : syracuseStep 2141437 = 803039) (by norm_num)
theorem B2855249 : Blo 1903435 2855249 := bstep (se 2 (by rfl) ⟨1070718, by rfl⟩ : syracuseStep 2855249 = 2141437) B2141437
theorem B1903499 : Blo 1903435 1903499 := bstep (se 1 (by rfl) ⟨1427624, by rfl⟩ : syracuseStep 1903499 = 2855249) B2855249
theorem B6424325 : Blo 1903435 6424325 := bbase (se 4 (by rfl) ⟨602280, by rfl⟩ : syracuseStep 6424325 = 1204561) (by norm_num)
theorem B4282883 : Blo 1903435 4282883 := bstep (se 1 (by rfl) ⟨3212162, by rfl⟩ : syracuseStep 4282883 = 6424325) B6424325
theorem B2855255 : Blo 1903435 2855255 := bstep (se 1 (by rfl) ⟨2141441, by rfl⟩ : syracuseStep 2855255 = 4282883) B4282883
theorem B1903503 : Blo 1903435 1903503 := bstep (se 1 (by rfl) ⟨1427627, by rfl⟩ : syracuseStep 1903503 = 2855255) B2855255
theorem B2855261 : Blo 1903435 2855261 := bbase (se 3 (by rfl) ⟨535361, by rfl⟩ : syracuseStep 2855261 = 1070723) (by norm_num)
theorem B1903507 : Blo 1903435 1903507 := bstep (se 1 (by rfl) ⟨1427630, by rfl⟩ : syracuseStep 1903507 = 2855261) B2855261
theorem B4282901 : Blo 1903435 4282901 := bbase (se 6 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 4282901 = 200761) (by norm_num)
theorem B2855267 : Blo 1903435 2855267 := bstep (se 1 (by rfl) ⟨2141450, by rfl⟩ : syracuseStep 2855267 = 4282901) B4282901
theorem B1903511 : Blo 1903435 1903511 := bstep (se 1 (by rfl) ⟨1427633, by rfl⟩ : syracuseStep 1903511 = 2855267) B2855267
theorem B7227413 : Blo 1903435 7227413 := bbase (se 6 (by rfl) ⟨169392, by rfl⟩ : syracuseStep 7227413 = 338785) (by norm_num)
theorem B4818275 : Blo 1903435 4818275 := bstep (se 1 (by rfl) ⟨3613706, by rfl⟩ : syracuseStep 4818275 = 7227413) B7227413
theorem B3212183 : Blo 1903435 3212183 := bstep (se 1 (by rfl) ⟨2409137, by rfl⟩ : syracuseStep 3212183 = 4818275) B4818275
theorem B2141455 : Blo 1903435 2141455 := bstep (se 1 (by rfl) ⟨1606091, by rfl⟩ : syracuseStep 2141455 = 3212183) B3212183
theorem B2855273 : Blo 1903435 2855273 := bstep (se 2 (by rfl) ⟨1070727, by rfl⟩ : syracuseStep 2855273 = 2141455) B2141455
theorem B1903515 : Blo 1903435 1903515 := bstep (se 1 (by rfl) ⟨1427636, by rfl⟩ : syracuseStep 1903515 = 2855273) B2855273
theorem B10841141 : Blo 1903435 10841141 := bbase (se 5 (by rfl) ⟨508178, by rfl⟩ : syracuseStep 10841141 = 1016357) (by norm_num)
theorem B7227427 : Blo 1903435 7227427 := bstep (se 1 (by rfl) ⟨5420570, by rfl⟩ : syracuseStep 7227427 = 10841141) B10841141
theorem B9636569 : Blo 1903435 9636569 := bstep (se 2 (by rfl) ⟨3613713, by rfl⟩ : syracuseStep 9636569 = 7227427) B7227427
theorem B6424379 : Blo 1903435 6424379 := bstep (se 1 (by rfl) ⟨4818284, by rfl⟩ : syracuseStep 6424379 = 9636569) B9636569
theorem B4282919 : Blo 1903435 4282919 := bstep (se 1 (by rfl) ⟨3212189, by rfl⟩ : syracuseStep 4282919 = 6424379) B6424379
theorem B2855279 : Blo 1903435 2855279 := bstep (se 1 (by rfl) ⟨2141459, by rfl⟩ : syracuseStep 2855279 = 4282919) B4282919
theorem B1903519 : Blo 1903435 1903519 := bstep (se 1 (by rfl) ⟨1427639, by rfl⟩ : syracuseStep 1903519 = 2855279) B2855279
theorem B2855285 : Blo 1903435 2855285 := bbase (se 5 (by rfl) ⟨133841, by rfl⟩ : syracuseStep 2855285 = 267683) (by norm_num)
theorem B1903523 : Blo 1903435 1903523 := bstep (se 1 (by rfl) ⟨1427642, by rfl⟩ : syracuseStep 1903523 = 2855285) B2855285
theorem B3049085 : Blo 1903435 3049085 := bbase (se 3 (by rfl) ⟨571703, by rfl⟩ : syracuseStep 3049085 = 1143407) (by norm_num)
theorem B2032723 : Blo 1903435 2032723 := bstep (se 1 (by rfl) ⟨1524542, by rfl⟩ : syracuseStep 2032723 = 3049085) B3049085
theorem B2710297 : Blo 1903435 2710297 := bstep (se 2 (by rfl) ⟨1016361, by rfl⟩ : syracuseStep 2710297 = 2032723) B2032723
theorem B3613729 : Blo 1903435 3613729 := bstep (se 2 (by rfl) ⟨1355148, by rfl⟩ : syracuseStep 3613729 = 2710297) B2710297
theorem B4818305 : Blo 1903435 4818305 := bstep (se 2 (by rfl) ⟨1806864, by rfl⟩ : syracuseStep 4818305 = 3613729) B3613729
theorem B3212203 : Blo 1903435 3212203 := bstep (se 1 (by rfl) ⟨2409152, by rfl⟩ : syracuseStep 3212203 = 4818305) B4818305
theorem B4282937 : Blo 1903435 4282937 := bstep (se 2 (by rfl) ⟨1606101, by rfl⟩ : syracuseStep 4282937 = 3212203) B3212203
theorem B2855291 : Blo 1903435 2855291 := bstep (se 1 (by rfl) ⟨2141468, by rfl⟩ : syracuseStep 2855291 = 4282937) B4282937
theorem B1903527 : Blo 1903435 1903527 := bstep (se 1 (by rfl) ⟨1427645, by rfl⟩ : syracuseStep 1903527 = 2855291) B2855291
theorem B2141473 : Blo 1903435 2141473 := bbase (se 2 (by rfl) ⟨803052, by rfl⟩ : syracuseStep 2141473 = 1606105) (by norm_num)
theorem B2855297 : Blo 1903435 2855297 := bstep (se 2 (by rfl) ⟨1070736, by rfl⟩ : syracuseStep 2855297 = 2141473) B2141473
theorem B1903531 : Blo 1903435 1903531 := bstep (se 1 (by rfl) ⟨1427648, by rfl⟩ : syracuseStep 1903531 = 2855297) B2855297
theorem B4818325 : Blo 1903435 4818325 := bbase (se 6 (by rfl) ⟨112929, by rfl⟩ : syracuseStep 4818325 = 225859) (by norm_num)
theorem B6424433 : Blo 1903435 6424433 := bstep (se 2 (by rfl) ⟨2409162, by rfl⟩ : syracuseStep 6424433 = 4818325) B4818325
theorem B4282955 : Blo 1903435 4282955 := bstep (se 1 (by rfl) ⟨3212216, by rfl⟩ : syracuseStep 4282955 = 6424433) B6424433
theorem B2855303 : Blo 1903435 2855303 := bstep (se 1 (by rfl) ⟨2141477, by rfl⟩ : syracuseStep 2855303 = 4282955) B4282955
theorem B1903535 : Blo 1903435 1903535 := bstep (se 1 (by rfl) ⟨1427651, by rfl⟩ : syracuseStep 1903535 = 2855303) B2855303
theorem B2855309 : Blo 1903435 2855309 := bbase (se 3 (by rfl) ⟨535370, by rfl⟩ : syracuseStep 2855309 = 1070741) (by norm_num)
theorem B1903539 : Blo 1903435 1903539 := bstep (se 1 (by rfl) ⟨1427654, by rfl⟩ : syracuseStep 1903539 = 2855309) B2855309
theorem B4282973 : Blo 1903435 4282973 := bbase (se 3 (by rfl) ⟨803057, by rfl⟩ : syracuseStep 4282973 = 1606115) (by norm_num)
theorem B2855315 : Blo 1903435 2855315 := bstep (se 1 (by rfl) ⟨2141486, by rfl⟩ : syracuseStep 2855315 = 4282973) B4282973
theorem B1903543 : Blo 1903435 1903543 := bstep (se 1 (by rfl) ⟨1427657, by rfl⟩ : syracuseStep 1903543 = 2855315) B2855315
theorem B3212237 : Blo 1903435 3212237 := bbase (se 3 (by rfl) ⟨602294, by rfl⟩ : syracuseStep 3212237 = 1204589) (by norm_num)
theorem B2141491 : Blo 1903435 2141491 := bstep (se 1 (by rfl) ⟨1606118, by rfl⟩ : syracuseStep 2141491 = 3212237) B3212237
theorem B2855321 : Blo 1903435 2855321 := bstep (se 2 (by rfl) ⟨1070745, by rfl⟩ : syracuseStep 2855321 = 2141491) B2141491
theorem B1903547 : Blo 1903435 1903547 := bstep (se 1 (by rfl) ⟨1427660, by rfl⟩ : syracuseStep 1903547 = 2855321) B2855321
theorem B34731413 : Blo 1903435 34731413 := bbase (se 6 (by rfl) ⟨814017, by rfl⟩ : syracuseStep 34731413 = 1628035) (by norm_num)
theorem B23154275 : Blo 1903435 23154275 := bstep (se 1 (by rfl) ⟨17365706, by rfl⟩ : syracuseStep 23154275 = 34731413) B34731413
theorem B15436183 : Blo 1903435 15436183 := bstep (se 1 (by rfl) ⟨11577137, by rfl⟩ : syracuseStep 15436183 = 23154275) B23154275
theorem B20581577 : Blo 1903435 20581577 := bstep (se 2 (by rfl) ⟨7718091, by rfl⟩ : syracuseStep 20581577 = 15436183) B15436183
theorem B13721051 : Blo 1903435 13721051 := bstep (se 1 (by rfl) ⟨10290788, by rfl⟩ : syracuseStep 13721051 = 20581577) B20581577
theorem B9147367 : Blo 1903435 9147367 := bstep (se 1 (by rfl) ⟨6860525, by rfl⟩ : syracuseStep 9147367 = 13721051) B13721051
theorem B12196489 : Blo 1903435 12196489 := bstep (se 2 (by rfl) ⟨4573683, by rfl⟩ : syracuseStep 12196489 = 9147367) B9147367
theorem B16261985 : Blo 1903435 16261985 := bstep (se 2 (by rfl) ⟨6098244, by rfl⟩ : syracuseStep 16261985 = 12196489) B12196489
theorem B10841323 : Blo 1903435 10841323 := bstep (se 1 (by rfl) ⟨8130992, by rfl⟩ : syracuseStep 10841323 = 16261985) B16261985
theorem B14455097 : Blo 1903435 14455097 := bstep (se 2 (by rfl) ⟨5420661, by rfl⟩ : syracuseStep 14455097 = 10841323) B10841323
theorem B9636731 : Blo 1903435 9636731 := bstep (se 1 (by rfl) ⟨7227548, by rfl⟩ : syracuseStep 9636731 = 14455097) B14455097
theorem B6424487 : Blo 1903435 6424487 := bstep (se 1 (by rfl) ⟨4818365, by rfl⟩ : syracuseStep 6424487 = 9636731) B9636731
theorem B4282991 : Blo 1903435 4282991 := bstep (se 1 (by rfl) ⟨3212243, by rfl⟩ : syracuseStep 4282991 = 6424487) B6424487
theorem B2855327 : Blo 1903435 2855327 := bstep (se 1 (by rfl) ⟨2141495, by rfl⟩ : syracuseStep 2855327 = 4282991) B4282991
theorem B1903551 : Blo 1903435 1903551 := bstep (se 1 (by rfl) ⟨1427663, by rfl⟩ : syracuseStep 1903551 = 2855327) B2855327
theorem B2855333 : Blo 1903435 2855333 := bbase (se 4 (by rfl) ⟨267687, by rfl⟩ : syracuseStep 2855333 = 535375) (by norm_num)
theorem B1903555 : Blo 1903435 1903555 := bstep (se 1 (by rfl) ⟨1427666, by rfl⟩ : syracuseStep 1903555 = 2855333) B2855333
theorem B2409193 : Blo 1903435 2409193 := bbase (se 2 (by rfl) ⟨903447, by rfl⟩ : syracuseStep 2409193 = 1806895) (by norm_num)
theorem B3212257 : Blo 1903435 3212257 := bstep (se 2 (by rfl) ⟨1204596, by rfl⟩ : syracuseStep 3212257 = 2409193) B2409193
theorem B4283009 : Blo 1903435 4283009 := bstep (se 2 (by rfl) ⟨1606128, by rfl⟩ : syracuseStep 4283009 = 3212257) B3212257
theorem B2855339 : Blo 1903435 2855339 := bstep (se 1 (by rfl) ⟨2141504, by rfl⟩ : syracuseStep 2855339 = 4283009) B4283009
theorem B1903559 : Blo 1903435 1903559 := bstep (se 1 (by rfl) ⟨1427669, by rfl⟩ : syracuseStep 1903559 = 2855339) B2855339
theorem B2141509 : Blo 1903435 2141509 := bbase (se 4 (by rfl) ⟨200766, by rfl⟩ : syracuseStep 2141509 = 401533) (by norm_num)
theorem B2855345 : Blo 1903435 2855345 := bstep (se 2 (by rfl) ⟨1070754, by rfl⟩ : syracuseStep 2855345 = 2141509) B2141509
theorem B1903563 : Blo 1903435 1903563 := bstep (se 1 (by rfl) ⟨1427672, by rfl⟩ : syracuseStep 1903563 = 2855345) B2855345
theorem B3613805 : Blo 1903435 3613805 := bbase (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) (by norm_num)
theorem B2409203 : Blo 1903435 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B6424541 : Blo 1903435 6424541 := bstep (se 3 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 6424541 = 2409203) B2409203
theorem B4283027 : Blo 1903435 4283027 := bstep (se 1 (by rfl) ⟨3212270, by rfl⟩ : syracuseStep 4283027 = 6424541) B6424541
theorem B2855351 : Blo 1903435 2855351 := bstep (se 1 (by rfl) ⟨2141513, by rfl⟩ : syracuseStep 2855351 = 4283027) B4283027
theorem B1903567 : Blo 1903435 1903567 := bstep (se 1 (by rfl) ⟨1427675, by rfl⟩ : syracuseStep 1903567 = 2855351) B2855351
theorem B2855357 : Blo 1903435 2855357 := bbase (se 3 (by rfl) ⟨535379, by rfl⟩ : syracuseStep 2855357 = 1070759) (by norm_num)
theorem B1903571 : Blo 1903435 1903571 := bstep (se 1 (by rfl) ⟨1427678, by rfl⟩ : syracuseStep 1903571 = 2855357) B2855357
theorem B4283045 : Blo 1903435 4283045 := bbase (se 4 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 4283045 = 803071) (by norm_num)
theorem B2855363 : Blo 1903435 2855363 := bstep (se 1 (by rfl) ⟨2141522, by rfl⟩ : syracuseStep 2855363 = 4283045) B4283045
theorem B1903575 : Blo 1903435 1903575 := bstep (se 1 (by rfl) ⟨1427681, by rfl⟩ : syracuseStep 1903575 = 2855363) B2855363
theorem B4818437 : Blo 1903435 4818437 := bbase (se 4 (by rfl) ⟨451728, by rfl⟩ : syracuseStep 4818437 = 903457) (by norm_num)
theorem B3212291 : Blo 1903435 3212291 := bstep (se 1 (by rfl) ⟨2409218, by rfl⟩ : syracuseStep 3212291 = 4818437) B4818437
theorem B2141527 : Blo 1903435 2141527 := bstep (se 1 (by rfl) ⟨1606145, by rfl⟩ : syracuseStep 2141527 = 3212291) B3212291
theorem B2855369 : Blo 1903435 2855369 := bstep (se 2 (by rfl) ⟨1070763, by rfl⟩ : syracuseStep 2855369 = 2141527) B2141527
theorem B1903579 : Blo 1903435 1903579 := bstep (se 1 (by rfl) ⟨1427684, by rfl⟩ : syracuseStep 1903579 = 2855369) B2855369
theorem B4065565 : Blo 1903435 4065565 := bbase (se 3 (by rfl) ⟨762293, by rfl⟩ : syracuseStep 4065565 = 1524587) (by norm_num)
theorem B5420753 : Blo 1903435 5420753 := bstep (se 2 (by rfl) ⟨2032782, by rfl⟩ : syracuseStep 5420753 = 4065565) B4065565
theorem B3613835 : Blo 1903435 3613835 := bstep (se 1 (by rfl) ⟨2710376, by rfl⟩ : syracuseStep 3613835 = 5420753) B5420753
theorem B9636893 : Blo 1903435 9636893 := bstep (se 3 (by rfl) ⟨1806917, by rfl⟩ : syracuseStep 9636893 = 3613835) B3613835
theorem B6424595 : Blo 1903435 6424595 := bstep (se 1 (by rfl) ⟨4818446, by rfl⟩ : syracuseStep 6424595 = 9636893) B9636893
theorem B4283063 : Blo 1903435 4283063 := bstep (se 1 (by rfl) ⟨3212297, by rfl⟩ : syracuseStep 4283063 = 6424595) B6424595
theorem B2855375 : Blo 1903435 2855375 := bstep (se 1 (by rfl) ⟨2141531, by rfl⟩ : syracuseStep 2855375 = 4283063) B4283063
theorem B1903583 : Blo 1903435 1903583 := bstep (se 1 (by rfl) ⟨1427687, by rfl⟩ : syracuseStep 1903583 = 2855375) B2855375
theorem B2855381 : Blo 1903435 2855381 := bbase (se 7 (by rfl) ⟨33461, by rfl⟩ : syracuseStep 2855381 = 66923) (by norm_num)
theorem B1903587 : Blo 1903435 1903587 := bstep (se 1 (by rfl) ⟨1427690, by rfl⟩ : syracuseStep 1903587 = 2855381) B2855381
theorem B7227701 : Blo 1903435 7227701 := bbase (se 5 (by rfl) ⟨338798, by rfl⟩ : syracuseStep 7227701 = 677597) (by norm_num)
theorem B4818467 : Blo 1903435 4818467 := bstep (se 1 (by rfl) ⟨3613850, by rfl⟩ : syracuseStep 4818467 = 7227701) B7227701
theorem B3212311 : Blo 1903435 3212311 := bstep (se 1 (by rfl) ⟨2409233, by rfl⟩ : syracuseStep 3212311 = 4818467) B4818467
theorem B4283081 : Blo 1903435 4283081 := bstep (se 2 (by rfl) ⟨1606155, by rfl⟩ : syracuseStep 4283081 = 3212311) B3212311
theorem B2855387 : Blo 1903435 2855387 := bstep (se 1 (by rfl) ⟨2141540, by rfl⟩ : syracuseStep 2855387 = 4283081) B4283081
theorem B1903591 : Blo 1903435 1903591 := bstep (se 1 (by rfl) ⟨1427693, by rfl⟩ : syracuseStep 1903591 = 2855387) B2855387
theorem B2141545 : Blo 1903435 2141545 := bbase (se 2 (by rfl) ⟨803079, by rfl⟩ : syracuseStep 2141545 = 1606159) (by norm_num)
theorem B2855393 : Blo 1903435 2855393 := bstep (se 2 (by rfl) ⟨1070772, by rfl⟩ : syracuseStep 2855393 = 2141545) B2141545
theorem B1903595 : Blo 1903435 1903595 := bstep (se 1 (by rfl) ⟨1427696, by rfl⟩ : syracuseStep 1903595 = 2855393) B2855393
theorem B4884229 : Blo 1903435 4884229 := bbase (se 4 (by rfl) ⟨457896, by rfl⟩ : syracuseStep 4884229 = 915793) (by norm_num)
theorem B26049221 : Blo 1903435 26049221 := bstep (se 4 (by rfl) ⟨2442114, by rfl⟩ : syracuseStep 26049221 = 4884229) B4884229
theorem B17366147 : Blo 1903435 17366147 := bstep (se 1 (by rfl) ⟨13024610, by rfl⟩ : syracuseStep 17366147 = 26049221) B26049221
theorem B11577431 : Blo 1903435 11577431 := bstep (se 1 (by rfl) ⟨8683073, by rfl⟩ : syracuseStep 11577431 = 17366147) B17366147
theorem B30873149 : Blo 1903435 30873149 := bstep (se 3 (by rfl) ⟨5788715, by rfl⟩ : syracuseStep 30873149 = 11577431) B11577431
theorem B20582099 : Blo 1903435 20582099 := bstep (se 1 (by rfl) ⟨15436574, by rfl⟩ : syracuseStep 20582099 = 30873149) B30873149
theorem B13721399 : Blo 1903435 13721399 := bstep (se 1 (by rfl) ⟨10291049, by rfl⟩ : syracuseStep 13721399 = 20582099) B20582099
theorem B9147599 : Blo 1903435 9147599 := bstep (se 1 (by rfl) ⟨6860699, by rfl⟩ : syracuseStep 9147599 = 13721399) B13721399
theorem B6098399 : Blo 1903435 6098399 := bstep (se 1 (by rfl) ⟨4573799, by rfl⟩ : syracuseStep 6098399 = 9147599) B9147599
theorem B4065599 : Blo 1903435 4065599 := bstep (se 1 (by rfl) ⟨3049199, by rfl⟩ : syracuseStep 4065599 = 6098399) B6098399
theorem B10841597 : Blo 1903435 10841597 := bstep (se 3 (by rfl) ⟨2032799, by rfl⟩ : syracuseStep 10841597 = 4065599) B4065599
theorem B7227731 : Blo 1903435 7227731 := bstep (se 1 (by rfl) ⟨5420798, by rfl⟩ : syracuseStep 7227731 = 10841597) B10841597
theorem B4818487 : Blo 1903435 4818487 := bstep (se 1 (by rfl) ⟨3613865, by rfl⟩ : syracuseStep 4818487 = 7227731) B7227731
theorem B6424649 : Blo 1903435 6424649 := bstep (se 2 (by rfl) ⟨2409243, by rfl⟩ : syracuseStep 6424649 = 4818487) B4818487
theorem B4283099 : Blo 1903435 4283099 := bstep (se 1 (by rfl) ⟨3212324, by rfl⟩ : syracuseStep 4283099 = 6424649) B6424649
theorem B2855399 : Blo 1903435 2855399 := bstep (se 1 (by rfl) ⟨2141549, by rfl⟩ : syracuseStep 2855399 = 4283099) B4283099
theorem B1903599 : Blo 1903435 1903599 := bstep (se 1 (by rfl) ⟨1427699, by rfl⟩ : syracuseStep 1903599 = 2855399) B2855399
theorem B2855405 : Blo 1903435 2855405 := bbase (se 3 (by rfl) ⟨535388, by rfl⟩ : syracuseStep 2855405 = 1070777) (by norm_num)
theorem B1903603 : Blo 1903435 1903603 := bstep (se 1 (by rfl) ⟨1427702, by rfl⟩ : syracuseStep 1903603 = 2855405) B2855405
theorem B4283117 : Blo 1903435 4283117 := bbase (se 3 (by rfl) ⟨803084, by rfl⟩ : syracuseStep 4283117 = 1606169) (by norm_num)
theorem B2855411 : Blo 1903435 2855411 := bstep (se 1 (by rfl) ⟨2141558, by rfl⟩ : syracuseStep 2855411 = 4283117) B4283117
theorem B1903607 : Blo 1903435 1903607 := bstep (se 1 (by rfl) ⟨1427705, by rfl⟩ : syracuseStep 1903607 = 2855411) B2855411
theorem B2032813 : Blo 1903435 2032813 := bbase (se 3 (by rfl) ⟨381152, by rfl⟩ : syracuseStep 2032813 = 762305) (by norm_num)
theorem B2710417 : Blo 1903435 2710417 := bstep (se 2 (by rfl) ⟨1016406, by rfl⟩ : syracuseStep 2710417 = 2032813) B2032813
theorem B3613889 : Blo 1903435 3613889 := bstep (se 2 (by rfl) ⟨1355208, by rfl⟩ : syracuseStep 3613889 = 2710417) B2710417
theorem B2409259 : Blo 1903435 2409259 := bstep (se 1 (by rfl) ⟨1806944, by rfl⟩ : syracuseStep 2409259 = 3613889) B3613889
theorem B3212345 : Blo 1903435 3212345 := bstep (se 2 (by rfl) ⟨1204629, by rfl⟩ : syracuseStep 3212345 = 2409259) B2409259
theorem B2141563 : Blo 1903435 2141563 := bstep (se 1 (by rfl) ⟨1606172, by rfl⟩ : syracuseStep 2141563 = 3212345) B3212345
theorem B2855417 : Blo 1903435 2855417 := bstep (se 2 (by rfl) ⟨1070781, by rfl⟩ : syracuseStep 2855417 = 2141563) B2141563
theorem B1903611 : Blo 1903435 1903611 := bstep (se 1 (by rfl) ⟨1427708, by rfl⟩ : syracuseStep 1903611 = 2855417) B2855417
theorem B3477181 : Blo 1903435 3477181 := bbase (se 3 (by rfl) ⟨651971, by rfl⟩ : syracuseStep 3477181 = 1303943) (by norm_num)
theorem B4636241 : Blo 1903435 4636241 := bstep (se 2 (by rfl) ⟨1738590, by rfl⟩ : syracuseStep 4636241 = 3477181) B3477181
theorem B3090827 : Blo 1903435 3090827 := bstep (se 1 (by rfl) ⟨2318120, by rfl⟩ : syracuseStep 3090827 = 4636241) B4636241
theorem B2060551 : Blo 1903435 2060551 := bstep (se 1 (by rfl) ⟨1545413, by rfl⟩ : syracuseStep 2060551 = 3090827) B3090827
theorem B10989605 : Blo 1903435 10989605 := bstep (se 4 (by rfl) ⟨1030275, by rfl⟩ : syracuseStep 10989605 = 2060551) B2060551
theorem B29305613 : Blo 1903435 29305613 := bstep (se 3 (by rfl) ⟨5494802, by rfl⟩ : syracuseStep 29305613 = 10989605) B10989605
theorem B19537075 : Blo 1903435 19537075 := bstep (se 1 (by rfl) ⟨14652806, by rfl⟩ : syracuseStep 19537075 = 29305613) B29305613
theorem B26049433 : Blo 1903435 26049433 := bstep (se 2 (by rfl) ⟨9768537, by rfl⟩ : syracuseStep 26049433 = 19537075) B19537075
theorem B34732577 : Blo 1903435 34732577 := bstep (se 2 (by rfl) ⟨13024716, by rfl⟩ : syracuseStep 34732577 = 26049433) B26049433
theorem B23155051 : Blo 1903435 23155051 := bstep (se 1 (by rfl) ⟨17366288, by rfl⟩ : syracuseStep 23155051 = 34732577) B34732577
theorem B30873401 : Blo 1903435 30873401 := bstep (se 2 (by rfl) ⟨11577525, by rfl⟩ : syracuseStep 30873401 = 23155051) B23155051
theorem B20582267 : Blo 1903435 20582267 := bstep (se 1 (by rfl) ⟨15436700, by rfl⟩ : syracuseStep 20582267 = 30873401) B30873401
theorem B54886045 : Blo 1903435 54886045 := bstep (se 3 (by rfl) ⟨10291133, by rfl⟩ : syracuseStep 54886045 = 20582267) B20582267
theorem B73181393 : Blo 1903435 73181393 := bstep (se 2 (by rfl) ⟨27443022, by rfl⟩ : syracuseStep 73181393 = 54886045) B54886045
theorem B48787595 : Blo 1903435 48787595 := bstep (se 1 (by rfl) ⟨36590696, by rfl⟩ : syracuseStep 48787595 = 73181393) B73181393
theorem B32525063 : Blo 1903435 32525063 := bstep (se 1 (by rfl) ⟨24393797, by rfl⟩ : syracuseStep 32525063 = 48787595) B48787595
theorem B21683375 : Blo 1903435 21683375 := bstep (se 1 (by rfl) ⟨16262531, by rfl⟩ : syracuseStep 21683375 = 32525063) B32525063
theorem B14455583 : Blo 1903435 14455583 := bstep (se 1 (by rfl) ⟨10841687, by rfl⟩ : syracuseStep 14455583 = 21683375) B21683375
theorem B9637055 : Blo 1903435 9637055 := bstep (se 1 (by rfl) ⟨7227791, by rfl⟩ : syracuseStep 9637055 = 14455583) B14455583
theorem B6424703 : Blo 1903435 6424703 := bstep (se 1 (by rfl) ⟨4818527, by rfl⟩ : syracuseStep 6424703 = 9637055) B9637055
theorem B4283135 : Blo 1903435 4283135 := bstep (se 1 (by rfl) ⟨3212351, by rfl⟩ : syracuseStep 4283135 = 6424703) B6424703
theorem B2855423 : Blo 1903435 2855423 := bstep (se 1 (by rfl) ⟨2141567, by rfl⟩ : syracuseStep 2855423 = 4283135) B4283135
theorem B1903615 : Blo 1903435 1903615 := bstep (se 1 (by rfl) ⟨1427711, by rfl⟩ : syracuseStep 1903615 = 2855423) B2855423
theorem B2855429 : Blo 1903435 2855429 := bbase (se 4 (by rfl) ⟨267696, by rfl⟩ : syracuseStep 2855429 = 535393) (by norm_num)
theorem B1903619 : Blo 1903435 1903619 := bstep (se 1 (by rfl) ⟨1427714, by rfl⟩ : syracuseStep 1903619 = 2855429) B2855429
theorem B3212365 : Blo 1903435 3212365 := bbase (se 3 (by rfl) ⟨602318, by rfl⟩ : syracuseStep 3212365 = 1204637) (by norm_num)
theorem B4283153 : Blo 1903435 4283153 := bstep (se 2 (by rfl) ⟨1606182, by rfl⟩ : syracuseStep 4283153 = 3212365) B3212365
theorem B2855435 : Blo 1903435 2855435 := bstep (se 1 (by rfl) ⟨2141576, by rfl⟩ : syracuseStep 2855435 = 4283153) B4283153
theorem B1903623 : Blo 1903435 1903623 := bstep (se 1 (by rfl) ⟨1427717, by rfl⟩ : syracuseStep 1903623 = 2855435) B2855435
theorem B2141581 : Blo 1903435 2141581 := bbase (se 3 (by rfl) ⟨401546, by rfl⟩ : syracuseStep 2141581 = 803093) (by norm_num)
theorem B2855441 : Blo 1903435 2855441 := bstep (se 2 (by rfl) ⟨1070790, by rfl⟩ : syracuseStep 2855441 = 2141581) B2141581
theorem B1903627 : Blo 1903435 1903627 := bstep (se 1 (by rfl) ⟨1427720, by rfl⟩ : syracuseStep 1903627 = 2855441) B2855441
theorem B6424757 : Blo 1903435 6424757 := bbase (se 5 (by rfl) ⟨301160, by rfl⟩ : syracuseStep 6424757 = 602321) (by norm_num)
theorem B4283171 : Blo 1903435 4283171 := bstep (se 1 (by rfl) ⟨3212378, by rfl⟩ : syracuseStep 4283171 = 6424757) B6424757
theorem B2855447 : Blo 1903435 2855447 := bstep (se 1 (by rfl) ⟨2141585, by rfl⟩ : syracuseStep 2855447 = 4283171) B4283171
theorem B1903631 : Blo 1903435 1903631 := bstep (se 1 (by rfl) ⟨1427723, by rfl⟩ : syracuseStep 1903631 = 2855447) B2855447
theorem B2855453 : Blo 1903435 2855453 := bbase (se 3 (by rfl) ⟨535397, by rfl⟩ : syracuseStep 2855453 = 1070795) (by norm_num)
theorem B1903635 : Blo 1903435 1903635 := bstep (se 1 (by rfl) ⟨1427726, by rfl⟩ : syracuseStep 1903635 = 2855453) B2855453
theorem B4283189 : Blo 1903435 4283189 := bbase (se 5 (by rfl) ⟨200774, by rfl⟩ : syracuseStep 4283189 = 401549) (by norm_num)
theorem B2855459 : Blo 1903435 2855459 := bstep (se 1 (by rfl) ⟨2141594, by rfl⟩ : syracuseStep 2855459 = 4283189) B4283189
theorem B1903639 : Blo 1903435 1903639 := bstep (se 1 (by rfl) ⟨1427729, by rfl⟩ : syracuseStep 1903639 = 2855459) B2855459
theorem B13721717 : Blo 1903435 13721717 := bbase (se 5 (by rfl) ⟨643205, by rfl⟩ : syracuseStep 13721717 = 1286411) (by norm_num)
theorem B9147811 : Blo 1903435 9147811 := bstep (se 1 (by rfl) ⟨6860858, by rfl⟩ : syracuseStep 9147811 = 13721717) B13721717
theorem B12197081 : Blo 1903435 12197081 := bstep (se 2 (by rfl) ⟨4573905, by rfl⟩ : syracuseStep 12197081 = 9147811) B9147811
theorem B8131387 : Blo 1903435 8131387 := bstep (se 1 (by rfl) ⟨6098540, by rfl⟩ : syracuseStep 8131387 = 12197081) B12197081
theorem B10841849 : Blo 1903435 10841849 := bstep (se 2 (by rfl) ⟨4065693, by rfl⟩ : syracuseStep 10841849 = 8131387) B8131387
theorem B7227899 : Blo 1903435 7227899 := bstep (se 1 (by rfl) ⟨5420924, by rfl⟩ : syracuseStep 7227899 = 10841849) B10841849
theorem B4818599 : Blo 1903435 4818599 := bstep (se 1 (by rfl) ⟨3613949, by rfl⟩ : syracuseStep 4818599 = 7227899) B7227899
theorem B3212399 : Blo 1903435 3212399 := bstep (se 1 (by rfl) ⟨2409299, by rfl⟩ : syracuseStep 3212399 = 4818599) B4818599
theorem B2141599 : Blo 1903435 2141599 := bstep (se 1 (by rfl) ⟨1606199, by rfl⟩ : syracuseStep 2141599 = 3212399) B3212399
theorem B2855465 : Blo 1903435 2855465 := bstep (se 2 (by rfl) ⟨1070799, by rfl⟩ : syracuseStep 2855465 = 2141599) B2141599
theorem B1903643 : Blo 1903435 1903643 := bstep (se 1 (by rfl) ⟨1427732, by rfl⟩ : syracuseStep 1903643 = 2855465) B2855465
theorem B9147829 : Blo 1903435 9147829 := bbase (se 5 (by rfl) ⟨428804, by rfl⟩ : syracuseStep 9147829 = 857609) (by norm_num)
theorem B12197105 : Blo 1903435 12197105 := bstep (se 2 (by rfl) ⟨4573914, by rfl⟩ : syracuseStep 12197105 = 9147829) B9147829
theorem B8131403 : Blo 1903435 8131403 := bstep (se 1 (by rfl) ⟨6098552, by rfl⟩ : syracuseStep 8131403 = 12197105) B12197105
theorem B5420935 : Blo 1903435 5420935 := bstep (se 1 (by rfl) ⟨4065701, by rfl⟩ : syracuseStep 5420935 = 8131403) B8131403
theorem B7227913 : Blo 1903435 7227913 := bstep (se 2 (by rfl) ⟨2710467, by rfl⟩ : syracuseStep 7227913 = 5420935) B5420935
theorem B9637217 : Blo 1903435 9637217 := bstep (se 2 (by rfl) ⟨3613956, by rfl⟩ : syracuseStep 9637217 = 7227913) B7227913
theorem B6424811 : Blo 1903435 6424811 := bstep (se 1 (by rfl) ⟨4818608, by rfl⟩ : syracuseStep 6424811 = 9637217) B9637217
theorem B4283207 : Blo 1903435 4283207 := bstep (se 1 (by rfl) ⟨3212405, by rfl⟩ : syracuseStep 4283207 = 6424811) B6424811
theorem B2855471 : Blo 1903435 2855471 := bstep (se 1 (by rfl) ⟨2141603, by rfl⟩ : syracuseStep 2855471 = 4283207) B4283207
theorem B1903647 : Blo 1903435 1903647 := bstep (se 1 (by rfl) ⟨1427735, by rfl⟩ : syracuseStep 1903647 = 2855471) B2855471
theorem B2855477 : Blo 1903435 2855477 := bbase (se 5 (by rfl) ⟨133850, by rfl⟩ : syracuseStep 2855477 = 267701) (by norm_num)
theorem B1903651 : Blo 1903435 1903651 := bstep (se 1 (by rfl) ⟨1427738, by rfl⟩ : syracuseStep 1903651 = 2855477) B2855477
theorem B4818629 : Blo 1903435 4818629 := bbase (se 4 (by rfl) ⟨451746, by rfl⟩ : syracuseStep 4818629 = 903493) (by norm_num)
theorem B3212419 : Blo 1903435 3212419 := bstep (se 1 (by rfl) ⟨2409314, by rfl⟩ : syracuseStep 3212419 = 4818629) B4818629
theorem B4283225 : Blo 1903435 4283225 := bstep (se 2 (by rfl) ⟨1606209, by rfl⟩ : syracuseStep 4283225 = 3212419) B3212419
theorem B2855483 : Blo 1903435 2855483 := bstep (se 1 (by rfl) ⟨2141612, by rfl⟩ : syracuseStep 2855483 = 4283225) B4283225
theorem B1903655 : Blo 1903435 1903655 := bstep (se 1 (by rfl) ⟨1427741, by rfl⟩ : syracuseStep 1903655 = 2855483) B2855483
theorem B2141617 : Blo 1903435 2141617 := bbase (se 2 (by rfl) ⟨803106, by rfl⟩ : syracuseStep 2141617 = 1606213) (by norm_num)
theorem B2855489 : Blo 1903435 2855489 := bstep (se 2 (by rfl) ⟨1070808, by rfl⟩ : syracuseStep 2855489 = 2141617) B2141617
theorem B1903659 : Blo 1903435 1903659 := bstep (se 1 (by rfl) ⟨1427744, by rfl⟩ : syracuseStep 1903659 = 2855489) B2855489
theorem B5420981 : Blo 1903435 5420981 := bbase (se 5 (by rfl) ⟨254108, by rfl⟩ : syracuseStep 5420981 = 508217) (by norm_num)
theorem B3613987 : Blo 1903435 3613987 := bstep (se 1 (by rfl) ⟨2710490, by rfl⟩ : syracuseStep 3613987 = 5420981) B5420981
theorem B4818649 : Blo 1903435 4818649 := bstep (se 2 (by rfl) ⟨1806993, by rfl⟩ : syracuseStep 4818649 = 3613987) B3613987
theorem B6424865 : Blo 1903435 6424865 := bstep (se 2 (by rfl) ⟨2409324, by rfl⟩ : syracuseStep 6424865 = 4818649) B4818649
theorem B4283243 : Blo 1903435 4283243 := bstep (se 1 (by rfl) ⟨3212432, by rfl⟩ : syracuseStep 4283243 = 6424865) B6424865
theorem B2855495 : Blo 1903435 2855495 := bstep (se 1 (by rfl) ⟨2141621, by rfl⟩ : syracuseStep 2855495 = 4283243) B4283243
theorem B1903663 : Blo 1903435 1903663 := bstep (se 1 (by rfl) ⟨1427747, by rfl⟩ : syracuseStep 1903663 = 2855495) B2855495
theorem B2855501 : Blo 1903435 2855501 := bbase (se 3 (by rfl) ⟨535406, by rfl⟩ : syracuseStep 2855501 = 1070813) (by norm_num)
theorem B1903667 : Blo 1903435 1903667 := bstep (se 1 (by rfl) ⟨1427750, by rfl⟩ : syracuseStep 1903667 = 2855501) B2855501
theorem B4283261 : Blo 1903435 4283261 := bbase (se 3 (by rfl) ⟨803111, by rfl⟩ : syracuseStep 4283261 = 1606223) (by norm_num)
theorem B2855507 : Blo 1903435 2855507 := bstep (se 1 (by rfl) ⟨2141630, by rfl⟩ : syracuseStep 2855507 = 4283261) B4283261
theorem B1903671 : Blo 1903435 1903671 := bstep (se 1 (by rfl) ⟨1427753, by rfl⟩ : syracuseStep 1903671 = 2855507) B2855507
theorem B3212453 : Blo 1903435 3212453 := bbase (se 4 (by rfl) ⟨301167, by rfl⟩ : syracuseStep 3212453 = 602335) (by norm_num)
theorem B2141635 : Blo 1903435 2141635 := bstep (se 1 (by rfl) ⟨1606226, by rfl⟩ : syracuseStep 2141635 = 3212453) B3212453
theorem B2855513 : Blo 1903435 2855513 := bstep (se 2 (by rfl) ⟨1070817, by rfl⟩ : syracuseStep 2855513 = 2141635) B2141635
theorem B1903675 : Blo 1903435 1903675 := bstep (se 1 (by rfl) ⟨1427756, by rfl⟩ : syracuseStep 1903675 = 2855513) B2855513
theorem B2032885 : Blo 1903435 2032885 := bbase (se 5 (by rfl) ⟨95291, by rfl⟩ : syracuseStep 2032885 = 190583) (by norm_num)
theorem B2710513 : Blo 1903435 2710513 := bstep (se 2 (by rfl) ⟨1016442, by rfl⟩ : syracuseStep 2710513 = 2032885) B2032885
theorem B14456069 : Blo 1903435 14456069 := bstep (se 4 (by rfl) ⟨1355256, by rfl⟩ : syracuseStep 14456069 = 2710513) B2710513
theorem B9637379 : Blo 1903435 9637379 := bstep (se 1 (by rfl) ⟨7228034, by rfl⟩ : syracuseStep 9637379 = 14456069) B14456069
theorem B6424919 : Blo 1903435 6424919 := bstep (se 1 (by rfl) ⟨4818689, by rfl⟩ : syracuseStep 6424919 = 9637379) B9637379
theorem B4283279 : Blo 1903435 4283279 := bstep (se 1 (by rfl) ⟨3212459, by rfl⟩ : syracuseStep 4283279 = 6424919) B6424919
theorem B2855519 : Blo 1903435 2855519 := bstep (se 1 (by rfl) ⟨2141639, by rfl⟩ : syracuseStep 2855519 = 4283279) B4283279
theorem B1903679 : Blo 1903435 1903679 := bstep (se 1 (by rfl) ⟨1427759, by rfl⟩ : syracuseStep 1903679 = 2855519) B2855519
theorem B2855525 : Blo 1903435 2855525 := bbase (se 4 (by rfl) ⟨267705, by rfl⟩ : syracuseStep 2855525 = 535411) (by norm_num)
theorem B1903683 : Blo 1903435 1903683 := bstep (se 1 (by rfl) ⟨1427762, by rfl⟩ : syracuseStep 1903683 = 2855525) B2855525
theorem B2710525 : Blo 1903435 2710525 := bbase (se 3 (by rfl) ⟨508223, by rfl⟩ : syracuseStep 2710525 = 1016447) (by norm_num)
theorem B3614033 : Blo 1903435 3614033 := bstep (se 2 (by rfl) ⟨1355262, by rfl⟩ : syracuseStep 3614033 = 2710525) B2710525
theorem B2409355 : Blo 1903435 2409355 := bstep (se 1 (by rfl) ⟨1807016, by rfl⟩ : syracuseStep 2409355 = 3614033) B3614033
theorem B3212473 : Blo 1903435 3212473 := bstep (se 2 (by rfl) ⟨1204677, by rfl⟩ : syracuseStep 3212473 = 2409355) B2409355
theorem B4283297 : Blo 1903435 4283297 := bstep (se 2 (by rfl) ⟨1606236, by rfl⟩ : syracuseStep 4283297 = 3212473) B3212473
theorem B2855531 : Blo 1903435 2855531 := bstep (se 1 (by rfl) ⟨2141648, by rfl⟩ : syracuseStep 2855531 = 4283297) B4283297
theorem B1903687 : Blo 1903435 1903687 := bstep (se 1 (by rfl) ⟨1427765, by rfl⟩ : syracuseStep 1903687 = 2855531) B2855531
theorem B2141653 : Blo 1903435 2141653 := bbase (se 7 (by rfl) ⟨25097, by rfl⟩ : syracuseStep 2141653 = 50195) (by norm_num)
theorem B2855537 : Blo 1903435 2855537 := bstep (se 2 (by rfl) ⟨1070826, by rfl⟩ : syracuseStep 2855537 = 2141653) B2141653
theorem B1903691 : Blo 1903435 1903691 := bstep (se 1 (by rfl) ⟨1427768, by rfl⟩ : syracuseStep 1903691 = 2855537) B2855537
theorem B2409365 : Blo 1903435 2409365 := bbase (se 6 (by rfl) ⟨56469, by rfl⟩ : syracuseStep 2409365 = 112939) (by norm_num)
theorem B6424973 : Blo 1903435 6424973 := bstep (se 3 (by rfl) ⟨1204682, by rfl⟩ : syracuseStep 6424973 = 2409365) B2409365
theorem B4283315 : Blo 1903435 4283315 := bstep (se 1 (by rfl) ⟨3212486, by rfl⟩ : syracuseStep 4283315 = 6424973) B6424973
theorem B2855543 : Blo 1903435 2855543 := bstep (se 1 (by rfl) ⟨2141657, by rfl⟩ : syracuseStep 2855543 = 4283315) B4283315
theorem B1903695 : Blo 1903435 1903695 := bstep (se 1 (by rfl) ⟨1427771, by rfl⟩ : syracuseStep 1903695 = 2855543) B2855543
theorem B2855549 : Blo 1903435 2855549 := bbase (se 3 (by rfl) ⟨535415, by rfl⟩ : syracuseStep 2855549 = 1070831) (by norm_num)
theorem B1903699 : Blo 1903435 1903699 := bstep (se 1 (by rfl) ⟨1427774, by rfl⟩ : syracuseStep 1903699 = 2855549) B2855549
theorem B4283333 : Blo 1903435 4283333 := bbase (se 4 (by rfl) ⟨401562, by rfl⟩ : syracuseStep 4283333 = 803125) (by norm_num)
theorem B2855555 : Blo 1903435 2855555 := bstep (se 1 (by rfl) ⟨2141666, by rfl⟩ : syracuseStep 2855555 = 4283333) B4283333
theorem B1903703 : Blo 1903435 1903703 := bstep (se 1 (by rfl) ⟨1427777, by rfl⟩ : syracuseStep 1903703 = 2855555) B2855555
theorem B3049373 : Blo 1903435 3049373 := bbase (se 3 (by rfl) ⟨571757, by rfl⟩ : syracuseStep 3049373 = 1143515) (by norm_num)
theorem B8131661 : Blo 1903435 8131661 := bstep (se 3 (by rfl) ⟨1524686, by rfl⟩ : syracuseStep 8131661 = 3049373) B3049373
theorem B5421107 : Blo 1903435 5421107 := bstep (se 1 (by rfl) ⟨4065830, by rfl⟩ : syracuseStep 5421107 = 8131661) B8131661
theorem B3614071 : Blo 1903435 3614071 := bstep (se 1 (by rfl) ⟨2710553, by rfl⟩ : syracuseStep 3614071 = 5421107) B5421107
theorem B4818761 : Blo 1903435 4818761 := bstep (se 2 (by rfl) ⟨1807035, by rfl⟩ : syracuseStep 4818761 = 3614071) B3614071
theorem B3212507 : Blo 1903435 3212507 := bstep (se 1 (by rfl) ⟨2409380, by rfl⟩ : syracuseStep 3212507 = 4818761) B4818761
theorem B2141671 : Blo 1903435 2141671 := bstep (se 1 (by rfl) ⟨1606253, by rfl⟩ : syracuseStep 2141671 = 3212507) B3212507
theorem B2855561 : Blo 1903435 2855561 := bstep (se 2 (by rfl) ⟨1070835, by rfl⟩ : syracuseStep 2855561 = 2141671) B2141671
theorem B1903707 : Blo 1903435 1903707 := bstep (se 1 (by rfl) ⟨1427780, by rfl⟩ : syracuseStep 1903707 = 2855561) B2855561
theorem B9637541 : Blo 1903435 9637541 := bbase (se 4 (by rfl) ⟨903519, by rfl⟩ : syracuseStep 9637541 = 1807039) (by norm_num)
theorem B6425027 : Blo 1903435 6425027 := bstep (se 1 (by rfl) ⟨4818770, by rfl⟩ : syracuseStep 6425027 = 9637541) B9637541
theorem B4283351 : Blo 1903435 4283351 := bstep (se 1 (by rfl) ⟨3212513, by rfl⟩ : syracuseStep 4283351 = 6425027) B6425027
theorem B2855567 : Blo 1903435 2855567 := bstep (se 1 (by rfl) ⟨2141675, by rfl⟩ : syracuseStep 2855567 = 4283351) B4283351
theorem B1903711 : Blo 1903435 1903711 := bstep (se 1 (by rfl) ⟨1427783, by rfl⟩ : syracuseStep 1903711 = 2855567) B2855567
theorem B2855573 : Blo 1903435 2855573 := bbase (se 6 (by rfl) ⟨66927, by rfl⟩ : syracuseStep 2855573 = 133855) (by norm_num)
theorem B1903715 : Blo 1903435 1903715 := bstep (se 1 (by rfl) ⟨1427786, by rfl⟩ : syracuseStep 1903715 = 2855573) B2855573
theorem B3771917 : Blo 1903435 3771917 := bbase (se 3 (by rfl) ⟨707234, by rfl⟩ : syracuseStep 3771917 = 1414469) (by norm_num)
theorem B2514611 : Blo 1903435 2514611 := bstep (se 1 (by rfl) ⟨1885958, by rfl⟩ : syracuseStep 2514611 = 3771917) B3771917
theorem B6705629 : Blo 1903435 6705629 := bstep (se 3 (by rfl) ⟨1257305, by rfl⟩ : syracuseStep 6705629 = 2514611) B2514611
theorem B4470419 : Blo 1903435 4470419 := bstep (se 1 (by rfl) ⟨3352814, by rfl⟩ : syracuseStep 4470419 = 6705629) B6705629
theorem B2980279 : Blo 1903435 2980279 := bstep (se 1 (by rfl) ⟨2235209, by rfl⟩ : syracuseStep 2980279 = 4470419) B4470419
theorem B15894821 : Blo 1903435 15894821 := bstep (se 4 (by rfl) ⟨1490139, by rfl⟩ : syracuseStep 15894821 = 2980279) B2980279
theorem B10596547 : Blo 1903435 10596547 := bstep (se 1 (by rfl) ⟨7947410, by rfl⟩ : syracuseStep 10596547 = 15894821) B15894821
theorem B56514917 : Blo 1903435 56514917 := bstep (se 4 (by rfl) ⟨5298273, by rfl⟩ : syracuseStep 56514917 = 10596547) B10596547
theorem B37676611 : Blo 1903435 37676611 := bstep (se 1 (by rfl) ⟨28257458, by rfl⟩ : syracuseStep 37676611 = 56514917) B56514917
theorem B50235481 : Blo 1903435 50235481 := bstep (se 2 (by rfl) ⟨18838305, by rfl⟩ : syracuseStep 50235481 = 37676611) B37676611
theorem B66980641 : Blo 1903435 66980641 := bstep (se 2 (by rfl) ⟨25117740, by rfl⟩ : syracuseStep 66980641 = 50235481) B50235481
theorem B89307521 : Blo 1903435 89307521 := bstep (se 2 (by rfl) ⟨33490320, by rfl⟩ : syracuseStep 89307521 = 66980641) B66980641
theorem B59538347 : Blo 1903435 59538347 := bstep (se 1 (by rfl) ⟨44653760, by rfl⟩ : syracuseStep 59538347 = 89307521) B89307521
theorem B39692231 : Blo 1903435 39692231 := bstep (se 1 (by rfl) ⟨29769173, by rfl⟩ : syracuseStep 39692231 = 59538347) B59538347
theorem B26461487 : Blo 1903435 26461487 := bstep (se 1 (by rfl) ⟨19846115, by rfl⟩ : syracuseStep 26461487 = 39692231) B39692231
theorem B70563965 : Blo 1903435 70563965 := bstep (se 3 (by rfl) ⟨13230743, by rfl⟩ : syracuseStep 70563965 = 26461487) B26461487
theorem B188170573 : Blo 1903435 188170573 := bstep (se 3 (by rfl) ⟨35281982, by rfl⟩ : syracuseStep 188170573 = 70563965) B70563965
theorem B250894097 : Blo 1903435 250894097 := bstep (se 2 (by rfl) ⟨94085286, by rfl⟩ : syracuseStep 250894097 = 188170573) B188170573
theorem B167262731 : Blo 1903435 167262731 := bstep (se 1 (by rfl) ⟨125447048, by rfl⟩ : syracuseStep 167262731 = 250894097) B250894097
theorem B111508487 : Blo 1903435 111508487 := bstep (se 1 (by rfl) ⟨83631365, by rfl⟩ : syracuseStep 111508487 = 167262731) B167262731
theorem B74338991 : Blo 1903435 74338991 := bstep (se 1 (by rfl) ⟨55754243, by rfl⟩ : syracuseStep 74338991 = 111508487) B111508487
theorem B49559327 : Blo 1903435 49559327 := bstep (se 1 (by rfl) ⟨37169495, by rfl⟩ : syracuseStep 49559327 = 74338991) B74338991
theorem B33039551 : Blo 1903435 33039551 := bstep (se 1 (by rfl) ⟨24779663, by rfl⟩ : syracuseStep 33039551 = 49559327) B49559327
theorem B22026367 : Blo 1903435 22026367 := bstep (se 1 (by rfl) ⟨16519775, by rfl⟩ : syracuseStep 22026367 = 33039551) B33039551
theorem B29368489 : Blo 1903435 29368489 := bstep (se 2 (by rfl) ⟨11013183, by rfl⟩ : syracuseStep 29368489 = 22026367) B22026367
theorem B39157985 : Blo 1903435 39157985 := bstep (se 2 (by rfl) ⟨14684244, by rfl⟩ : syracuseStep 39157985 = 29368489) B29368489
theorem B26105323 : Blo 1903435 26105323 := bstep (se 1 (by rfl) ⟨19578992, by rfl⟩ : syracuseStep 26105323 = 39157985) B39157985
theorem B34807097 : Blo 1903435 34807097 := bstep (se 2 (by rfl) ⟨13052661, by rfl⟩ : syracuseStep 34807097 = 26105323) B26105323
theorem B23204731 : Blo 1903435 23204731 := bstep (se 1 (by rfl) ⟨17403548, by rfl⟩ : syracuseStep 23204731 = 34807097) B34807097
theorem B30939641 : Blo 1903435 30939641 := bstep (se 2 (by rfl) ⟨11602365, by rfl⟩ : syracuseStep 30939641 = 23204731) B23204731
theorem B20626427 : Blo 1903435 20626427 := bstep (se 1 (by rfl) ⟨15469820, by rfl⟩ : syracuseStep 20626427 = 30939641) B30939641
theorem B13750951 : Blo 1903435 13750951 := bstep (se 1 (by rfl) ⟨10313213, by rfl⟩ : syracuseStep 13750951 = 20626427) B20626427
theorem B18334601 : Blo 1903435 18334601 := bstep (se 2 (by rfl) ⟨6875475, by rfl⟩ : syracuseStep 18334601 = 13750951) B13750951
theorem B12223067 : Blo 1903435 12223067 := bstep (se 1 (by rfl) ⟨9167300, by rfl⟩ : syracuseStep 12223067 = 18334601) B18334601
theorem B130379381 : Blo 1903435 130379381 := bstep (se 5 (by rfl) ⟨6111533, by rfl⟩ : syracuseStep 130379381 = 12223067) B12223067
theorem B86919587 : Blo 1903435 86919587 := bstep (se 1 (by rfl) ⟨65189690, by rfl⟩ : syracuseStep 86919587 = 130379381) B130379381
theorem B57946391 : Blo 1903435 57946391 := bstep (se 1 (by rfl) ⟨43459793, by rfl⟩ : syracuseStep 57946391 = 86919587) B86919587
theorem B38630927 : Blo 1903435 38630927 := bstep (se 1 (by rfl) ⟨28973195, by rfl⟩ : syracuseStep 38630927 = 57946391) B57946391
theorem B25753951 : Blo 1903435 25753951 := bstep (se 1 (by rfl) ⟨19315463, by rfl⟩ : syracuseStep 25753951 = 38630927) B38630927
theorem B34338601 : Blo 1903435 34338601 := bstep (se 2 (by rfl) ⟨12876975, by rfl⟩ : syracuseStep 34338601 = 25753951) B25753951
theorem B45784801 : Blo 1903435 45784801 := bstep (se 2 (by rfl) ⟨17169300, by rfl⟩ : syracuseStep 45784801 = 34338601) B34338601
theorem B244185605 : Blo 1903435 244185605 := bstep (se 4 (by rfl) ⟨22892400, by rfl⟩ : syracuseStep 244185605 = 45784801) B45784801
theorem B162790403 : Blo 1903435 162790403 := bstep (se 1 (by rfl) ⟨122092802, by rfl⟩ : syracuseStep 162790403 = 244185605) B244185605
theorem B1736430965 : Blo 1903435 1736430965 := bstep (se 5 (by rfl) ⟨81395201, by rfl⟩ : syracuseStep 1736430965 = 162790403) B162790403
theorem B1157620643 : Blo 1903435 1157620643 := bstep (se 1 (by rfl) ⟨868215482, by rfl⟩ : syracuseStep 1157620643 = 1736430965) B1736430965
theorem B771747095 : Blo 1903435 771747095 := bstep (se 1 (by rfl) ⟨578810321, by rfl⟩ : syracuseStep 771747095 = 1157620643) B1157620643
theorem B514498063 : Blo 1903435 514498063 := bstep (se 1 (by rfl) ⟨385873547, by rfl⟩ : syracuseStep 514498063 = 771747095) B771747095
theorem B685997417 : Blo 1903435 685997417 := bstep (se 2 (by rfl) ⟨257249031, by rfl⟩ : syracuseStep 685997417 = 514498063) B514498063
theorem B1829326445 : Blo 1903435 1829326445 := bstep (se 3 (by rfl) ⟨342998708, by rfl⟩ : syracuseStep 1829326445 = 685997417) B685997417
theorem B1219550963 : Blo 1903435 1219550963 := bstep (se 1 (by rfl) ⟨914663222, by rfl⟩ : syracuseStep 1219550963 = 1829326445) B1829326445
theorem B3252135901 : Blo 1903435 3252135901 := bstep (se 3 (by rfl) ⟨609775481, by rfl⟩ : syracuseStep 3252135901 = 1219550963) B1219550963
theorem B4336181201 : Blo 1903435 4336181201 := bstep (se 2 (by rfl) ⟨1626067950, by rfl⟩ : syracuseStep 4336181201 = 3252135901) B3252135901
theorem B2890787467 : Blo 1903435 2890787467 := bstep (se 1 (by rfl) ⟨2168090600, by rfl⟩ : syracuseStep 2890787467 = 4336181201) B4336181201
theorem B3854383289 : Blo 1903435 3854383289 := bstep (se 2 (by rfl) ⟨1445393733, by rfl⟩ : syracuseStep 3854383289 = 2890787467) B2890787467
theorem B2569588859 : Blo 1903435 2569588859 := bstep (se 1 (by rfl) ⟨1927191644, by rfl⟩ : syracuseStep 2569588859 = 3854383289) B3854383289
theorem B1713059239 : Blo 1903435 1713059239 := bstep (se 1 (by rfl) ⟨1284794429, by rfl⟩ : syracuseStep 1713059239 = 2569588859) B2569588859
theorem B2284078985 : Blo 1903435 2284078985 := bstep (se 2 (by rfl) ⟨856529619, by rfl⟩ : syracuseStep 2284078985 = 1713059239) B1713059239
theorem B1522719323 : Blo 1903435 1522719323 := bstep (se 1 (by rfl) ⟨1142039492, by rfl⟩ : syracuseStep 1522719323 = 2284078985) B2284078985
theorem B1015146215 : Blo 1903435 1015146215 := bstep (se 1 (by rfl) ⟨761359661, by rfl⟩ : syracuseStep 1015146215 = 1522719323) B1522719323
theorem B676764143 : Blo 1903435 676764143 := bstep (se 1 (by rfl) ⟨507573107, by rfl⟩ : syracuseStep 676764143 = 1015146215) B1015146215
theorem B451176095 : Blo 1903435 451176095 := bstep (se 1 (by rfl) ⟨338382071, by rfl⟩ : syracuseStep 451176095 = 676764143) B676764143
theorem B300784063 : Blo 1903435 300784063 := bstep (se 1 (by rfl) ⟨225588047, by rfl⟩ : syracuseStep 300784063 = 451176095) B451176095
theorem B401045417 : Blo 1903435 401045417 := bstep (se 2 (by rfl) ⟨150392031, by rfl⟩ : syracuseStep 401045417 = 300784063) B300784063
theorem B267363611 : Blo 1903435 267363611 := bstep (se 1 (by rfl) ⟨200522708, by rfl⟩ : syracuseStep 267363611 = 401045417) B401045417
theorem B178242407 : Blo 1903435 178242407 := bstep (se 1 (by rfl) ⟨133681805, by rfl⟩ : syracuseStep 178242407 = 267363611) B267363611
theorem B118828271 : Blo 1903435 118828271 := bstep (se 1 (by rfl) ⟨89121203, by rfl⟩ : syracuseStep 118828271 = 178242407) B178242407
theorem B79218847 : Blo 1903435 79218847 := bstep (se 1 (by rfl) ⟨59414135, by rfl⟩ : syracuseStep 79218847 = 118828271) B118828271
theorem B105625129 : Blo 1903435 105625129 := bstep (se 2 (by rfl) ⟨39609423, by rfl⟩ : syracuseStep 105625129 = 79218847) B79218847
theorem B140833505 : Blo 1903435 140833505 := bstep (se 2 (by rfl) ⟨52812564, by rfl⟩ : syracuseStep 140833505 = 105625129) B105625129
theorem B93889003 : Blo 1903435 93889003 := bstep (se 1 (by rfl) ⟨70416752, by rfl⟩ : syracuseStep 93889003 = 140833505) B140833505
theorem B125185337 : Blo 1903435 125185337 := bstep (se 2 (by rfl) ⟨46944501, by rfl⟩ : syracuseStep 125185337 = 93889003) B93889003
theorem B83456891 : Blo 1903435 83456891 := bstep (se 1 (by rfl) ⟨62592668, by rfl⟩ : syracuseStep 83456891 = 125185337) B125185337
theorem B55637927 : Blo 1903435 55637927 := bstep (se 1 (by rfl) ⟨41728445, by rfl⟩ : syracuseStep 55637927 = 83456891) B83456891
theorem B37091951 : Blo 1903435 37091951 := bstep (se 1 (by rfl) ⟨27818963, by rfl⟩ : syracuseStep 37091951 = 55637927) B55637927
theorem B24727967 : Blo 1903435 24727967 := bstep (se 1 (by rfl) ⟨18545975, by rfl⟩ : syracuseStep 24727967 = 37091951) B37091951
theorem B16485311 : Blo 1903435 16485311 := bstep (se 1 (by rfl) ⟨12363983, by rfl⟩ : syracuseStep 16485311 = 24727967) B24727967
theorem B10990207 : Blo 1903435 10990207 := bstep (se 1 (by rfl) ⟨8242655, by rfl⟩ : syracuseStep 10990207 = 16485311) B16485311
theorem B58614437 : Blo 1903435 58614437 := bstep (se 4 (by rfl) ⟨5495103, by rfl⟩ : syracuseStep 58614437 = 10990207) B10990207
theorem B39076291 : Blo 1903435 39076291 := bstep (se 1 (by rfl) ⟨29307218, by rfl⟩ : syracuseStep 39076291 = 58614437) B58614437
theorem B52101721 : Blo 1903435 52101721 := bstep (se 2 (by rfl) ⟨19538145, by rfl⟩ : syracuseStep 52101721 = 39076291) B39076291
theorem B69468961 : Blo 1903435 69468961 := bstep (se 2 (by rfl) ⟨26050860, by rfl⟩ : syracuseStep 69468961 = 52101721) B52101721
theorem B92625281 : Blo 1903435 92625281 := bstep (se 2 (by rfl) ⟨34734480, by rfl⟩ : syracuseStep 92625281 = 69468961) B69468961
theorem B61750187 : Blo 1903435 61750187 := bstep (se 1 (by rfl) ⟨46312640, by rfl⟩ : syracuseStep 61750187 = 92625281) B92625281
theorem B41166791 : Blo 1903435 41166791 := bstep (se 1 (by rfl) ⟨30875093, by rfl⟩ : syracuseStep 41166791 = 61750187) B61750187
theorem B27444527 : Blo 1903435 27444527 := bstep (se 1 (by rfl) ⟨20583395, by rfl⟩ : syracuseStep 27444527 = 41166791) B41166791
theorem B18296351 : Blo 1903435 18296351 := bstep (se 1 (by rfl) ⟨13722263, by rfl⟩ : syracuseStep 18296351 = 27444527) B27444527
theorem B12197567 : Blo 1903435 12197567 := bstep (se 1 (by rfl) ⟨9148175, by rfl⟩ : syracuseStep 12197567 = 18296351) B18296351
theorem B8131711 : Blo 1903435 8131711 := bstep (se 1 (by rfl) ⟨6098783, by rfl⟩ : syracuseStep 8131711 = 12197567) B12197567
theorem B10842281 : Blo 1903435 10842281 := bstep (se 2 (by rfl) ⟨4065855, by rfl⟩ : syracuseStep 10842281 = 8131711) B8131711
theorem B7228187 : Blo 1903435 7228187 := bstep (se 1 (by rfl) ⟨5421140, by rfl⟩ : syracuseStep 7228187 = 10842281) B10842281
theorem B4818791 : Blo 1903435 4818791 := bstep (se 1 (by rfl) ⟨3614093, by rfl⟩ : syracuseStep 4818791 = 7228187) B7228187
theorem B3212527 : Blo 1903435 3212527 := bstep (se 1 (by rfl) ⟨2409395, by rfl⟩ : syracuseStep 3212527 = 4818791) B4818791
theorem B4283369 : Blo 1903435 4283369 := bstep (se 2 (by rfl) ⟨1606263, by rfl⟩ : syracuseStep 4283369 = 3212527) B3212527
theorem B2855579 : Blo 1903435 2855579 := bstep (se 1 (by rfl) ⟨2141684, by rfl⟩ : syracuseStep 2855579 = 4283369) B4283369
theorem B1903719 : Blo 1903435 1903719 := bstep (se 1 (by rfl) ⟨1427789, by rfl⟩ : syracuseStep 1903719 = 2855579) B2855579
theorem B2141689 : Blo 1903435 2141689 := bbase (se 2 (by rfl) ⟨803133, by rfl⟩ : syracuseStep 2141689 = 1606267) (by norm_num)
theorem B2855585 : Blo 1903435 2855585 := bstep (se 2 (by rfl) ⟨1070844, by rfl⟩ : syracuseStep 2855585 = 2141689) B2141689
theorem B1903723 : Blo 1903435 1903723 := bstep (se 1 (by rfl) ⟨1427792, by rfl⟩ : syracuseStep 1903723 = 2855585) B2855585
theorem B17367317 : Blo 1903435 17367317 := bbase (se 6 (by rfl) ⟨407046, by rfl⟩ : syracuseStep 17367317 = 814093) (by norm_num)
theorem B11578211 : Blo 1903435 11578211 := bstep (se 1 (by rfl) ⟨8683658, by rfl⟩ : syracuseStep 11578211 = 17367317) B17367317
theorem B7718807 : Blo 1903435 7718807 := bstep (se 1 (by rfl) ⟨5789105, by rfl⟩ : syracuseStep 7718807 = 11578211) B11578211
theorem B5145871 : Blo 1903435 5145871 := bstep (se 1 (by rfl) ⟨3859403, by rfl⟩ : syracuseStep 5145871 = 7718807) B7718807
theorem B6861161 : Blo 1903435 6861161 := bstep (se 2 (by rfl) ⟨2572935, by rfl⟩ : syracuseStep 6861161 = 5145871) B5145871
theorem B4574107 : Blo 1903435 4574107 := bstep (se 1 (by rfl) ⟨3430580, by rfl⟩ : syracuseStep 4574107 = 6861161) B6861161
theorem B6098809 : Blo 1903435 6098809 := bstep (se 2 (by rfl) ⟨2287053, by rfl⟩ : syracuseStep 6098809 = 4574107) B4574107
theorem B8131745 : Blo 1903435 8131745 := bstep (se 2 (by rfl) ⟨3049404, by rfl⟩ : syracuseStep 8131745 = 6098809) B6098809
theorem B5421163 : Blo 1903435 5421163 := bstep (se 1 (by rfl) ⟨4065872, by rfl⟩ : syracuseStep 5421163 = 8131745) B8131745
theorem B7228217 : Blo 1903435 7228217 := bstep (se 2 (by rfl) ⟨2710581, by rfl⟩ : syracuseStep 7228217 = 5421163) B5421163
theorem B4818811 : Blo 1903435 4818811 := bstep (se 1 (by rfl) ⟨3614108, by rfl⟩ : syracuseStep 4818811 = 7228217) B7228217
theorem B6425081 : Blo 1903435 6425081 := bstep (se 2 (by rfl) ⟨2409405, by rfl⟩ : syracuseStep 6425081 = 4818811) B4818811
theorem B4283387 : Blo 1903435 4283387 := bstep (se 1 (by rfl) ⟨3212540, by rfl⟩ : syracuseStep 4283387 = 6425081) B6425081
theorem B2855591 : Blo 1903435 2855591 := bstep (se 1 (by rfl) ⟨2141693, by rfl⟩ : syracuseStep 2855591 = 4283387) B4283387
theorem B1903727 : Blo 1903435 1903727 := bstep (se 1 (by rfl) ⟨1427795, by rfl⟩ : syracuseStep 1903727 = 2855591) B2855591
theorem B2855597 : Blo 1903435 2855597 := bbase (se 3 (by rfl) ⟨535424, by rfl⟩ : syracuseStep 2855597 = 1070849) (by norm_num)
theorem B1903731 : Blo 1903435 1903731 := bstep (se 1 (by rfl) ⟨1427798, by rfl⟩ : syracuseStep 1903731 = 2855597) B2855597
theorem B4283405 : Blo 1903435 4283405 := bbase (se 3 (by rfl) ⟨803138, by rfl⟩ : syracuseStep 4283405 = 1606277) (by norm_num)
theorem B2855603 : Blo 1903435 2855603 := bstep (se 1 (by rfl) ⟨2141702, by rfl⟩ : syracuseStep 2855603 = 4283405) B4283405
theorem B1903735 : Blo 1903435 1903735 := bstep (se 1 (by rfl) ⟨1427801, by rfl⟩ : syracuseStep 1903735 = 2855603) B2855603
theorem B2409421 : Blo 1903435 2409421 := bbase (se 3 (by rfl) ⟨451766, by rfl⟩ : syracuseStep 2409421 = 903533) (by norm_num)
theorem B3212561 : Blo 1903435 3212561 := bstep (se 2 (by rfl) ⟨1204710, by rfl⟩ : syracuseStep 3212561 = 2409421) B2409421
theorem B2141707 : Blo 1903435 2141707 := bstep (se 1 (by rfl) ⟨1606280, by rfl⟩ : syracuseStep 2141707 = 3212561) B3212561
theorem B2855609 : Blo 1903435 2855609 := bstep (se 2 (by rfl) ⟨1070853, by rfl⟩ : syracuseStep 2855609 = 2141707) B2141707
theorem B1903739 : Blo 1903435 1903739 := bstep (se 1 (by rfl) ⟨1427804, by rfl⟩ : syracuseStep 1903739 = 2855609) B2855609
theorem B4121381 : Blo 1903435 4121381 := bbase (se 4 (by rfl) ⟨386379, by rfl⟩ : syracuseStep 4121381 = 772759) (by norm_num)
theorem B10990349 : Blo 1903435 10990349 := bstep (se 3 (by rfl) ⟨2060690, by rfl⟩ : syracuseStep 10990349 = 4121381) B4121381
theorem B7326899 : Blo 1903435 7326899 := bstep (se 1 (by rfl) ⟨5495174, by rfl⟩ : syracuseStep 7326899 = 10990349) B10990349
theorem B4884599 : Blo 1903435 4884599 := bstep (se 1 (by rfl) ⟨3663449, by rfl⟩ : syracuseStep 4884599 = 7326899) B7326899
theorem B3256399 : Blo 1903435 3256399 := bstep (se 1 (by rfl) ⟨2442299, by rfl⟩ : syracuseStep 3256399 = 4884599) B4884599
theorem B4341865 : Blo 1903435 4341865 := bstep (se 2 (by rfl) ⟨1628199, by rfl⟩ : syracuseStep 4341865 = 3256399) B3256399
theorem B5789153 : Blo 1903435 5789153 := bstep (se 2 (by rfl) ⟨2170932, by rfl⟩ : syracuseStep 5789153 = 4341865) B4341865
theorem B3859435 : Blo 1903435 3859435 := bstep (se 1 (by rfl) ⟨2894576, by rfl⟩ : syracuseStep 3859435 = 5789153) B5789153
theorem B5145913 : Blo 1903435 5145913 := bstep (se 2 (by rfl) ⟨1929717, by rfl⟩ : syracuseStep 5145913 = 3859435) B3859435
theorem B27444869 : Blo 1903435 27444869 := bstep (se 4 (by rfl) ⟨2572956, by rfl⟩ : syracuseStep 27444869 = 5145913) B5145913
theorem B18296579 : Blo 1903435 18296579 := bstep (se 1 (by rfl) ⟨13722434, by rfl⟩ : syracuseStep 18296579 = 27444869) B27444869
theorem B12197719 : Blo 1903435 12197719 := bstep (se 1 (by rfl) ⟨9148289, by rfl⟩ : syracuseStep 12197719 = 18296579) B18296579
theorem B16263625 : Blo 1903435 16263625 := bstep (se 2 (by rfl) ⟨6098859, by rfl⟩ : syracuseStep 16263625 = 12197719) B12197719
theorem B21684833 : Blo 1903435 21684833 := bstep (se 2 (by rfl) ⟨8131812, by rfl⟩ : syracuseStep 21684833 = 16263625) B16263625
theorem B14456555 : Blo 1903435 14456555 := bstep (se 1 (by rfl) ⟨10842416, by rfl⟩ : syracuseStep 14456555 = 21684833) B21684833
theorem B9637703 : Blo 1903435 9637703 := bstep (se 1 (by rfl) ⟨7228277, by rfl⟩ : syracuseStep 9637703 = 14456555) B14456555
theorem B6425135 : Blo 1903435 6425135 := bstep (se 1 (by rfl) ⟨4818851, by rfl⟩ : syracuseStep 6425135 = 9637703) B9637703
theorem B4283423 : Blo 1903435 4283423 := bstep (se 1 (by rfl) ⟨3212567, by rfl⟩ : syracuseStep 4283423 = 6425135) B6425135
theorem B2855615 : Blo 1903435 2855615 := bstep (se 1 (by rfl) ⟨2141711, by rfl⟩ : syracuseStep 2855615 = 4283423) B4283423
theorem B1903743 : Blo 1903435 1903743 := bstep (se 1 (by rfl) ⟨1427807, by rfl⟩ : syracuseStep 1903743 = 2855615) B2855615
theorem B2855621 : Blo 1903435 2855621 := bbase (se 4 (by rfl) ⟨267714, by rfl⟩ : syracuseStep 2855621 = 535429) (by norm_num)
theorem B1903747 : Blo 1903435 1903747 := bstep (se 1 (by rfl) ⟨1427810, by rfl⟩ : syracuseStep 1903747 = 2855621) B2855621
theorem B3212581 : Blo 1903435 3212581 := bbase (se 4 (by rfl) ⟨301179, by rfl⟩ : syracuseStep 3212581 = 602359) (by norm_num)
theorem B4283441 : Blo 1903435 4283441 := bstep (se 2 (by rfl) ⟨1606290, by rfl⟩ : syracuseStep 4283441 = 3212581) B3212581
theorem B2855627 : Blo 1903435 2855627 := bstep (se 1 (by rfl) ⟨2141720, by rfl⟩ : syracuseStep 2855627 = 4283441) B4283441
theorem B1903751 : Blo 1903435 1903751 := bstep (se 1 (by rfl) ⟨1427813, by rfl⟩ : syracuseStep 1903751 = 2855627) B2855627
theorem B2141725 : Blo 1903435 2141725 := bbase (se 3 (by rfl) ⟨401573, by rfl⟩ : syracuseStep 2141725 = 803147) (by norm_num)
theorem B2855633 : Blo 1903435 2855633 := bstep (se 2 (by rfl) ⟨1070862, by rfl⟩ : syracuseStep 2855633 = 2141725) B2141725
theorem B1903755 : Blo 1903435 1903755 := bstep (se 1 (by rfl) ⟨1427816, by rfl⟩ : syracuseStep 1903755 = 2855633) B2855633
theorem B6425189 : Blo 1903435 6425189 := bbase (se 4 (by rfl) ⟨602361, by rfl⟩ : syracuseStep 6425189 = 1204723) (by norm_num)
theorem B4283459 : Blo 1903435 4283459 := bstep (se 1 (by rfl) ⟨3212594, by rfl⟩ : syracuseStep 4283459 = 6425189) B6425189
theorem B2855639 : Blo 1903435 2855639 := bstep (se 1 (by rfl) ⟨2141729, by rfl⟩ : syracuseStep 2855639 = 4283459) B4283459
theorem B1903759 : Blo 1903435 1903759 := bstep (se 1 (by rfl) ⟨1427819, by rfl⟩ : syracuseStep 1903759 = 2855639) B2855639
theorem B2855645 : Blo 1903435 2855645 := bbase (se 3 (by rfl) ⟨535433, by rfl⟩ : syracuseStep 2855645 = 1070867) (by norm_num)
theorem B1903763 : Blo 1903435 1903763 := bstep (se 1 (by rfl) ⟨1427822, by rfl⟩ : syracuseStep 1903763 = 2855645) B2855645
theorem B4283477 : Blo 1903435 4283477 := bbase (se 8 (by rfl) ⟨25098, by rfl⟩ : syracuseStep 4283477 = 50197) (by norm_num)
theorem B2855651 : Blo 1903435 2855651 := bstep (se 1 (by rfl) ⟨2141738, by rfl⟩ : syracuseStep 2855651 = 4283477) B4283477
theorem B1903767 : Blo 1903435 1903767 := bstep (se 1 (by rfl) ⟨1427825, by rfl⟩ : syracuseStep 1903767 = 2855651) B2855651
theorem B3859493 : Blo 1903435 3859493 := bbase (se 4 (by rfl) ⟨361827, by rfl⟩ : syracuseStep 3859493 = 723655) (by norm_num)
theorem B10291981 : Blo 1903435 10291981 := bstep (se 3 (by rfl) ⟨1929746, by rfl⟩ : syracuseStep 10291981 = 3859493) B3859493
theorem B13722641 : Blo 1903435 13722641 := bstep (se 2 (by rfl) ⟨5145990, by rfl⟩ : syracuseStep 13722641 = 10291981) B10291981
theorem B9148427 : Blo 1903435 9148427 := bstep (se 1 (by rfl) ⟨6861320, by rfl⟩ : syracuseStep 9148427 = 13722641) B13722641
theorem B6098951 : Blo 1903435 6098951 := bstep (se 1 (by rfl) ⟨4574213, by rfl⟩ : syracuseStep 6098951 = 9148427) B9148427
theorem B4065967 : Blo 1903435 4065967 := bstep (se 1 (by rfl) ⟨3049475, by rfl⟩ : syracuseStep 4065967 = 6098951) B6098951
theorem B5421289 : Blo 1903435 5421289 := bstep (se 2 (by rfl) ⟨2032983, by rfl⟩ : syracuseStep 5421289 = 4065967) B4065967
theorem B7228385 : Blo 1903435 7228385 := bstep (se 2 (by rfl) ⟨2710644, by rfl⟩ : syracuseStep 7228385 = 5421289) B5421289
theorem B4818923 : Blo 1903435 4818923 := bstep (se 1 (by rfl) ⟨3614192, by rfl⟩ : syracuseStep 4818923 = 7228385) B7228385
theorem B3212615 : Blo 1903435 3212615 := bstep (se 1 (by rfl) ⟨2409461, by rfl⟩ : syracuseStep 3212615 = 4818923) B4818923
theorem B2141743 : Blo 1903435 2141743 := bstep (se 1 (by rfl) ⟨1606307, by rfl⟩ : syracuseStep 2141743 = 3212615) B3212615
theorem B2855657 : Blo 1903435 2855657 := bstep (se 2 (by rfl) ⟨1070871, by rfl⟩ : syracuseStep 2855657 = 2141743) B2141743
theorem B1903771 : Blo 1903435 1903771 := bstep (se 1 (by rfl) ⟨1427828, by rfl⟩ : syracuseStep 1903771 = 2855657) B2855657
theorem B18799573 : Blo 1903435 18799573 := bbase (se 7 (by rfl) ⟨220307, by rfl⟩ : syracuseStep 18799573 = 440615) (by norm_num)
theorem B25066097 : Blo 1903435 25066097 := bstep (se 2 (by rfl) ⟨9399786, by rfl⟩ : syracuseStep 25066097 = 18799573) B18799573
theorem B16710731 : Blo 1903435 16710731 := bstep (se 1 (by rfl) ⟨12533048, by rfl⟩ : syracuseStep 16710731 = 25066097) B25066097
theorem B11140487 : Blo 1903435 11140487 := bstep (se 1 (by rfl) ⟨8355365, by rfl⟩ : syracuseStep 11140487 = 16710731) B16710731
theorem B7426991 : Blo 1903435 7426991 := bstep (se 1 (by rfl) ⟨5570243, by rfl⟩ : syracuseStep 7426991 = 11140487) B11140487
theorem B4951327 : Blo 1903435 4951327 := bstep (se 1 (by rfl) ⟨3713495, by rfl⟩ : syracuseStep 4951327 = 7426991) B7426991
theorem B6601769 : Blo 1903435 6601769 := bstep (se 2 (by rfl) ⟨2475663, by rfl⟩ : syracuseStep 6601769 = 4951327) B4951327
theorem B4401179 : Blo 1903435 4401179 := bstep (se 1 (by rfl) ⟨3300884, by rfl⟩ : syracuseStep 4401179 = 6601769) B6601769
theorem B2934119 : Blo 1903435 2934119 := bstep (se 1 (by rfl) ⟨2200589, by rfl⟩ : syracuseStep 2934119 = 4401179) B4401179
theorem B1956079 : Blo 1903435 1956079 := bstep (se 1 (by rfl) ⟨1467059, by rfl⟩ : syracuseStep 1956079 = 2934119) B2934119
theorem B2608105 : Blo 1903435 2608105 := bstep (se 2 (by rfl) ⟨978039, by rfl⟩ : syracuseStep 2608105 = 1956079) B1956079
theorem B3477473 : Blo 1903435 3477473 := bstep (se 2 (by rfl) ⟨1304052, by rfl⟩ : syracuseStep 3477473 = 2608105) B2608105
theorem B2318315 : Blo 1903435 2318315 := bstep (se 1 (by rfl) ⟨1738736, by rfl⟩ : syracuseStep 2318315 = 3477473) B3477473
theorem B6182173 : Blo 1903435 6182173 := bstep (se 3 (by rfl) ⟨1159157, by rfl⟩ : syracuseStep 6182173 = 2318315) B2318315
theorem B32971589 : Blo 1903435 32971589 := bstep (se 4 (by rfl) ⟨3091086, by rfl⟩ : syracuseStep 32971589 = 6182173) B6182173
theorem B21981059 : Blo 1903435 21981059 := bstep (se 1 (by rfl) ⟨16485794, by rfl⟩ : syracuseStep 21981059 = 32971589) B32971589
theorem B14654039 : Blo 1903435 14654039 := bstep (se 1 (by rfl) ⟨10990529, by rfl⟩ : syracuseStep 14654039 = 21981059) B21981059
theorem B39077437 : Blo 1903435 39077437 := bstep (se 3 (by rfl) ⟨7327019, by rfl⟩ : syracuseStep 39077437 = 14654039) B14654039
theorem B52103249 : Blo 1903435 52103249 := bstep (se 2 (by rfl) ⟨19538718, by rfl⟩ : syracuseStep 52103249 = 39077437) B39077437
theorem B34735499 : Blo 1903435 34735499 := bstep (se 1 (by rfl) ⟨26051624, by rfl⟩ : syracuseStep 34735499 = 52103249) B52103249
theorem B23156999 : Blo 1903435 23156999 := bstep (se 1 (by rfl) ⟨17367749, by rfl⟩ : syracuseStep 23156999 = 34735499) B34735499
theorem B15437999 : Blo 1903435 15437999 := bstep (se 1 (by rfl) ⟨11578499, by rfl⟩ : syracuseStep 15437999 = 23156999) B23156999
theorem B41167997 : Blo 1903435 41167997 := bstep (se 3 (by rfl) ⟨7718999, by rfl⟩ : syracuseStep 41167997 = 15437999) B15437999
theorem B27445331 : Blo 1903435 27445331 := bstep (se 1 (by rfl) ⟨20583998, by rfl⟩ : syracuseStep 27445331 = 41167997) B41167997
theorem B18296887 : Blo 1903435 18296887 := bstep (se 1 (by rfl) ⟨13722665, by rfl⟩ : syracuseStep 18296887 = 27445331) B27445331
theorem B24395849 : Blo 1903435 24395849 := bstep (se 2 (by rfl) ⟨9148443, by rfl⟩ : syracuseStep 24395849 = 18296887) B18296887
theorem B16263899 : Blo 1903435 16263899 := bstep (se 1 (by rfl) ⟨12197924, by rfl⟩ : syracuseStep 16263899 = 24395849) B24395849
theorem B10842599 : Blo 1903435 10842599 := bstep (se 1 (by rfl) ⟨8131949, by rfl⟩ : syracuseStep 10842599 = 16263899) B16263899
theorem B7228399 : Blo 1903435 7228399 := bstep (se 1 (by rfl) ⟨5421299, by rfl⟩ : syracuseStep 7228399 = 10842599) B10842599
theorem B9637865 : Blo 1903435 9637865 := bstep (se 2 (by rfl) ⟨3614199, by rfl⟩ : syracuseStep 9637865 = 7228399) B7228399
theorem B6425243 : Blo 1903435 6425243 := bstep (se 1 (by rfl) ⟨4818932, by rfl⟩ : syracuseStep 6425243 = 9637865) B9637865
theorem B4283495 : Blo 1903435 4283495 := bstep (se 1 (by rfl) ⟨3212621, by rfl⟩ : syracuseStep 4283495 = 6425243) B6425243
theorem B2855663 : Blo 1903435 2855663 := bstep (se 1 (by rfl) ⟨2141747, by rfl⟩ : syracuseStep 2855663 = 4283495) B4283495
theorem B1903775 : Blo 1903435 1903775 := bstep (se 1 (by rfl) ⟨1427831, by rfl⟩ : syracuseStep 1903775 = 2855663) B2855663
theorem B2855669 : Blo 1903435 2855669 := bbase (se 5 (by rfl) ⟨133859, by rfl⟩ : syracuseStep 2855669 = 267719) (by norm_num)
theorem B1903779 : Blo 1903435 1903779 := bstep (se 1 (by rfl) ⟨1427834, by rfl⟩ : syracuseStep 1903779 = 2855669) B2855669
theorem B2287121 : Blo 1903435 2287121 := bbase (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) (by norm_num)
theorem B6098989 : Blo 1903435 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B8131985 : Blo 1903435 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B5421323 : Blo 1903435 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B3614215 : Blo 1903435 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B4818953 : Blo 1903435 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B3212635 : Blo 1903435 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B4283513 : Blo 1903435 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B2855675 : Blo 1903435 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B1903783 : Blo 1903435 1903783 := bstep (se 1 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 1903783 = 2855675) B2855675
theorem B2141761 : Blo 1903435 2141761 := bbase (se 2 (by rfl) ⟨803160, by rfl⟩ : syracuseStep 2141761 = 1606321) (by norm_num)
theorem B2855681 : Blo 1903435 2855681 := bstep (se 2 (by rfl) ⟨1070880, by rfl⟩ : syracuseStep 2855681 = 2141761) B2141761
theorem B1903787 : Blo 1903435 1903787 := bstep (se 1 (by rfl) ⟨1427840, by rfl⟩ : syracuseStep 1903787 = 2855681) B2855681
theorem B4818973 : Blo 1903435 4818973 := bbase (se 3 (by rfl) ⟨903557, by rfl⟩ : syracuseStep 4818973 = 1807115) (by norm_num)
theorem B6425297 : Blo 1903435 6425297 := bstep (se 2 (by rfl) ⟨2409486, by rfl⟩ : syracuseStep 6425297 = 4818973) B4818973
theorem B4283531 : Blo 1903435 4283531 := bstep (se 1 (by rfl) ⟨3212648, by rfl⟩ : syracuseStep 4283531 = 6425297) B6425297
theorem B2855687 : Blo 1903435 2855687 := bstep (se 1 (by rfl) ⟨2141765, by rfl⟩ : syracuseStep 2855687 = 4283531) B4283531
theorem B1903791 : Blo 1903435 1903791 := bstep (se 1 (by rfl) ⟨1427843, by rfl⟩ : syracuseStep 1903791 = 2855687) B2855687
theorem B2855693 : Blo 1903435 2855693 := bbase (se 3 (by rfl) ⟨535442, by rfl⟩ : syracuseStep 2855693 = 1070885) (by norm_num)
theorem B1903795 : Blo 1903435 1903795 := bstep (se 1 (by rfl) ⟨1427846, by rfl⟩ : syracuseStep 1903795 = 2855693) B2855693
theorem B4283549 : Blo 1903435 4283549 := bbase (se 3 (by rfl) ⟨803165, by rfl⟩ : syracuseStep 4283549 = 1606331) (by norm_num)
theorem B2855699 : Blo 1903435 2855699 := bstep (se 1 (by rfl) ⟨2141774, by rfl⟩ : syracuseStep 2855699 = 4283549) B4283549
theorem B1903799 : Blo 1903435 1903799 := bstep (se 1 (by rfl) ⟨1427849, by rfl⟩ : syracuseStep 1903799 = 2855699) B2855699
theorem B3212669 : Blo 1903435 3212669 := bbase (se 3 (by rfl) ⟨602375, by rfl⟩ : syracuseStep 3212669 = 1204751) (by norm_num)
theorem B2141779 : Blo 1903435 2141779 := bstep (se 1 (by rfl) ⟨1606334, by rfl⟩ : syracuseStep 2141779 = 3212669) B3212669
theorem B2855705 : Blo 1903435 2855705 := bstep (se 2 (by rfl) ⟨1070889, by rfl⟩ : syracuseStep 2855705 = 2141779) B2141779
theorem B1903803 : Blo 1903435 1903803 := bstep (se 1 (by rfl) ⟨1427852, by rfl⟩ : syracuseStep 1903803 = 2855705) B2855705
theorem B41730389 : Blo 1903435 41730389 := bbase (se 10 (by rfl) ⟨61128, by rfl⟩ : syracuseStep 41730389 = 122257) (by norm_num)
theorem B27820259 : Blo 1903435 27820259 := bstep (se 1 (by rfl) ⟨20865194, by rfl⟩ : syracuseStep 27820259 = 41730389) B41730389
theorem B18546839 : Blo 1903435 18546839 := bstep (se 1 (by rfl) ⟨13910129, by rfl⟩ : syracuseStep 18546839 = 27820259) B27820259
theorem B12364559 : Blo 1903435 12364559 := bstep (se 1 (by rfl) ⟨9273419, by rfl⟩ : syracuseStep 12364559 = 18546839) B18546839
theorem B8243039 : Blo 1903435 8243039 := bstep (se 1 (by rfl) ⟨6182279, by rfl⟩ : syracuseStep 8243039 = 12364559) B12364559
theorem B5495359 : Blo 1903435 5495359 := bstep (se 1 (by rfl) ⟨4121519, by rfl⟩ : syracuseStep 5495359 = 8243039) B8243039
theorem B7327145 : Blo 1903435 7327145 := bstep (se 2 (by rfl) ⟨2747679, by rfl⟩ : syracuseStep 7327145 = 5495359) B5495359
theorem B19539053 : Blo 1903435 19539053 := bstep (se 3 (by rfl) ⟨3663572, by rfl⟩ : syracuseStep 19539053 = 7327145) B7327145
theorem B13026035 : Blo 1903435 13026035 := bstep (se 1 (by rfl) ⟨9769526, by rfl⟩ : syracuseStep 13026035 = 19539053) B19539053
theorem B8684023 : Blo 1903435 8684023 := bstep (se 1 (by rfl) ⟨6513017, by rfl⟩ : syracuseStep 8684023 = 13026035) B13026035
theorem B11578697 : Blo 1903435 11578697 := bstep (se 2 (by rfl) ⟨4342011, by rfl⟩ : syracuseStep 11578697 = 8684023) B8684023
theorem B7719131 : Blo 1903435 7719131 := bstep (se 1 (by rfl) ⟨5789348, by rfl⟩ : syracuseStep 7719131 = 11578697) B11578697
theorem B5146087 : Blo 1903435 5146087 := bstep (se 1 (by rfl) ⟨3859565, by rfl⟩ : syracuseStep 5146087 = 7719131) B7719131
theorem B6861449 : Blo 1903435 6861449 := bstep (se 2 (by rfl) ⟨2573043, by rfl⟩ : syracuseStep 6861449 = 5146087) B5146087
theorem B4574299 : Blo 1903435 4574299 := bstep (se 1 (by rfl) ⟨3430724, by rfl⟩ : syracuseStep 4574299 = 6861449) B6861449
theorem B6099065 : Blo 1903435 6099065 := bstep (se 2 (by rfl) ⟨2287149, by rfl⟩ : syracuseStep 6099065 = 4574299) B4574299
theorem B4066043 : Blo 1903435 4066043 := bstep (se 1 (by rfl) ⟨3049532, by rfl⟩ : syracuseStep 4066043 = 6099065) B6099065
theorem B10842781 : Blo 1903435 10842781 := bstep (se 3 (by rfl) ⟨2033021, by rfl⟩ : syracuseStep 10842781 = 4066043) B4066043
theorem B14457041 : Blo 1903435 14457041 := bstep (se 2 (by rfl) ⟨5421390, by rfl⟩ : syracuseStep 14457041 = 10842781) B10842781
theorem B9638027 : Blo 1903435 9638027 := bstep (se 1 (by rfl) ⟨7228520, by rfl⟩ : syracuseStep 9638027 = 14457041) B14457041
theorem B6425351 : Blo 1903435 6425351 := bstep (se 1 (by rfl) ⟨4819013, by rfl⟩ : syracuseStep 6425351 = 9638027) B9638027
theorem B4283567 : Blo 1903435 4283567 := bstep (se 1 (by rfl) ⟨3212675, by rfl⟩ : syracuseStep 4283567 = 6425351) B6425351
theorem B2855711 : Blo 1903435 2855711 := bstep (se 1 (by rfl) ⟨2141783, by rfl⟩ : syracuseStep 2855711 = 4283567) B4283567
theorem B1903807 : Blo 1903435 1903807 := bstep (se 1 (by rfl) ⟨1427855, by rfl⟩ : syracuseStep 1903807 = 2855711) B2855711
theorem B2855717 : Blo 1903435 2855717 := bbase (se 4 (by rfl) ⟨267723, by rfl⟩ : syracuseStep 2855717 = 535447) (by norm_num)
theorem B1903811 : Blo 1903435 1903811 := bstep (se 1 (by rfl) ⟨1427858, by rfl⟩ : syracuseStep 1903811 = 2855717) B2855717
theorem B2409517 : Blo 1903435 2409517 := bbase (se 3 (by rfl) ⟨451784, by rfl⟩ : syracuseStep 2409517 = 903569) (by norm_num)
theorem B3212689 : Blo 1903435 3212689 := bstep (se 2 (by rfl) ⟨1204758, by rfl⟩ : syracuseStep 3212689 = 2409517) B2409517
theorem B4283585 : Blo 1903435 4283585 := bstep (se 2 (by rfl) ⟨1606344, by rfl⟩ : syracuseStep 4283585 = 3212689) B3212689
theorem B2855723 : Blo 1903435 2855723 := bstep (se 1 (by rfl) ⟨2141792, by rfl⟩ : syracuseStep 2855723 = 4283585) B4283585
theorem B1903815 : Blo 1903435 1903815 := bstep (se 1 (by rfl) ⟨1427861, by rfl⟩ : syracuseStep 1903815 = 2855723) B2855723
theorem B2141797 : Blo 1903435 2141797 := bbase (se 4 (by rfl) ⟨200793, by rfl⟩ : syracuseStep 2141797 = 401587) (by norm_num)
theorem B2855729 : Blo 1903435 2855729 := bstep (se 2 (by rfl) ⟨1070898, by rfl⟩ : syracuseStep 2855729 = 2141797) B2141797
theorem B1903819 : Blo 1903435 1903819 := bstep (se 1 (by rfl) ⟨1427864, by rfl⟩ : syracuseStep 1903819 = 2855729) B2855729
theorem B6861509 : Blo 1903435 6861509 := bbase (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) (by norm_num)
theorem B4574339 : Blo 1903435 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B3049559 : Blo 1903435 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B2033039 : Blo 1903435 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B5421437 : Blo 1903435 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B3614291 : Blo 1903435 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B2409527 : Blo 1903435 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B6425405 : Blo 1903435 6425405 := bstep (se 3 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 6425405 = 2409527) B2409527
theorem B4283603 : Blo 1903435 4283603 := bstep (se 1 (by rfl) ⟨3212702, by rfl⟩ : syracuseStep 4283603 = 6425405) B6425405
theorem B2855735 : Blo 1903435 2855735 := bstep (se 1 (by rfl) ⟨2141801, by rfl⟩ : syracuseStep 2855735 = 4283603) B4283603
theorem B1903823 : Blo 1903435 1903823 := bstep (se 1 (by rfl) ⟨1427867, by rfl⟩ : syracuseStep 1903823 = 2855735) B2855735
theorem B2855741 : Blo 1903435 2855741 := bbase (se 3 (by rfl) ⟨535451, by rfl⟩ : syracuseStep 2855741 = 1070903) (by norm_num)
theorem B1903827 : Blo 1903435 1903827 := bstep (se 1 (by rfl) ⟨1427870, by rfl⟩ : syracuseStep 1903827 = 2855741) B2855741
theorem B4283621 : Blo 1903435 4283621 := bbase (se 4 (by rfl) ⟨401589, by rfl⟩ : syracuseStep 4283621 = 803179) (by norm_num)
theorem B2855747 : Blo 1903435 2855747 := bstep (se 1 (by rfl) ⟨2141810, by rfl⟩ : syracuseStep 2855747 = 4283621) B4283621
theorem B1903831 : Blo 1903435 1903831 := bstep (se 1 (by rfl) ⟨1427873, by rfl⟩ : syracuseStep 1903831 = 2855747) B2855747
theorem B4819085 : Blo 1903435 4819085 := bbase (se 3 (by rfl) ⟨903578, by rfl⟩ : syracuseStep 4819085 = 1807157) (by norm_num)
theorem B3212723 : Blo 1903435 3212723 := bstep (se 1 (by rfl) ⟨2409542, by rfl⟩ : syracuseStep 3212723 = 4819085) B4819085
theorem B2141815 : Blo 1903435 2141815 := bstep (se 1 (by rfl) ⟨1606361, by rfl⟩ : syracuseStep 2141815 = 3212723) B3212723
theorem B2855753 : Blo 1903435 2855753 := bstep (se 2 (by rfl) ⟨1070907, by rfl⟩ : syracuseStep 2855753 = 2141815) B2141815
theorem B1903835 : Blo 1903435 1903835 := bstep (se 1 (by rfl) ⟨1427876, by rfl⟩ : syracuseStep 1903835 = 2855753) B2855753
theorem B2710741 : Blo 1903435 2710741 := bbase (se 7 (by rfl) ⟨31766, by rfl⟩ : syracuseStep 2710741 = 63533) (by norm_num)
theorem B3614321 : Blo 1903435 3614321 := bstep (se 2 (by rfl) ⟨1355370, by rfl⟩ : syracuseStep 3614321 = 2710741) B2710741
theorem B9638189 : Blo 1903435 9638189 := bstep (se 3 (by rfl) ⟨1807160, by rfl⟩ : syracuseStep 9638189 = 3614321) B3614321
theorem B6425459 : Blo 1903435 6425459 := bstep (se 1 (by rfl) ⟨4819094, by rfl⟩ : syracuseStep 6425459 = 9638189) B9638189
theorem B4283639 : Blo 1903435 4283639 := bstep (se 1 (by rfl) ⟨3212729, by rfl⟩ : syracuseStep 4283639 = 6425459) B6425459
theorem B2855759 : Blo 1903435 2855759 := bstep (se 1 (by rfl) ⟨2141819, by rfl⟩ : syracuseStep 2855759 = 4283639) B4283639
theorem B1903839 : Blo 1903435 1903839 := bstep (se 1 (by rfl) ⟨1427879, by rfl⟩ : syracuseStep 1903839 = 2855759) B2855759
theorem B2855765 : Blo 1903435 2855765 := bbase (se 9 (by rfl) ⟨8366, by rfl⟩ : syracuseStep 2855765 = 16733) (by norm_num)
theorem B1903843 : Blo 1903435 1903843 := bstep (se 1 (by rfl) ⟨1427882, by rfl⟩ : syracuseStep 1903843 = 2855765) B2855765
theorem B3049597 : Blo 1903435 3049597 := bbase (se 3 (by rfl) ⟨571799, by rfl⟩ : syracuseStep 3049597 = 1143599) (by norm_num)
theorem B4066129 : Blo 1903435 4066129 := bstep (se 2 (by rfl) ⟨1524798, by rfl⟩ : syracuseStep 4066129 = 3049597) B3049597
theorem B5421505 : Blo 1903435 5421505 := bstep (se 2 (by rfl) ⟨2033064, by rfl⟩ : syracuseStep 5421505 = 4066129) B4066129
theorem B7228673 : Blo 1903435 7228673 := bstep (se 2 (by rfl) ⟨2710752, by rfl⟩ : syracuseStep 7228673 = 5421505) B5421505
theorem B4819115 : Blo 1903435 4819115 := bstep (se 1 (by rfl) ⟨3614336, by rfl⟩ : syracuseStep 4819115 = 7228673) B7228673
theorem B3212743 : Blo 1903435 3212743 := bstep (se 1 (by rfl) ⟨2409557, by rfl⟩ : syracuseStep 3212743 = 4819115) B4819115
theorem B4283657 : Blo 1903435 4283657 := bstep (se 2 (by rfl) ⟨1606371, by rfl⟩ : syracuseStep 4283657 = 3212743) B3212743
theorem B2855771 : Blo 1903435 2855771 := bstep (se 1 (by rfl) ⟨2141828, by rfl⟩ : syracuseStep 2855771 = 4283657) B4283657
theorem B1903847 : Blo 1903435 1903847 := bstep (se 1 (by rfl) ⟨1427885, by rfl⟩ : syracuseStep 1903847 = 2855771) B2855771
theorem B2141833 : Blo 1903435 2141833 := bbase (se 2 (by rfl) ⟨803187, by rfl⟩ : syracuseStep 2141833 = 1606375) (by norm_num)
theorem B2855777 : Blo 1903435 2855777 := bstep (se 2 (by rfl) ⟨1070916, by rfl⟩ : syracuseStep 2855777 = 2141833) B2141833
theorem B1903851 : Blo 1903435 1903851 := bstep (se 1 (by rfl) ⟨1427888, by rfl⟩ : syracuseStep 1903851 = 2855777) B2855777
theorem B27446485 : Blo 1903435 27446485 := bbase (se 7 (by rfl) ⟨321638, by rfl⟩ : syracuseStep 27446485 = 643277) (by norm_num)
theorem B36595313 : Blo 1903435 36595313 := bstep (se 2 (by rfl) ⟨13723242, by rfl⟩ : syracuseStep 36595313 = 27446485) B27446485
theorem B24396875 : Blo 1903435 24396875 := bstep (se 1 (by rfl) ⟨18297656, by rfl⟩ : syracuseStep 24396875 = 36595313) B36595313
theorem B16264583 : Blo 1903435 16264583 := bstep (se 1 (by rfl) ⟨12198437, by rfl⟩ : syracuseStep 16264583 = 24396875) B24396875
theorem B10843055 : Blo 1903435 10843055 := bstep (se 1 (by rfl) ⟨8132291, by rfl⟩ : syracuseStep 10843055 = 16264583) B16264583
theorem B7228703 : Blo 1903435 7228703 := bstep (se 1 (by rfl) ⟨5421527, by rfl⟩ : syracuseStep 7228703 = 10843055) B10843055
theorem B4819135 : Blo 1903435 4819135 := bstep (se 1 (by rfl) ⟨3614351, by rfl⟩ : syracuseStep 4819135 = 7228703) B7228703
theorem B6425513 : Blo 1903435 6425513 := bstep (se 2 (by rfl) ⟨2409567, by rfl⟩ : syracuseStep 6425513 = 4819135) B4819135
theorem B4283675 : Blo 1903435 4283675 := bstep (se 1 (by rfl) ⟨3212756, by rfl⟩ : syracuseStep 4283675 = 6425513) B6425513
theorem B2855783 : Blo 1903435 2855783 := bstep (se 1 (by rfl) ⟨2141837, by rfl⟩ : syracuseStep 2855783 = 4283675) B4283675
theorem B1903855 : Blo 1903435 1903855 := bstep (se 1 (by rfl) ⟨1427891, by rfl⟩ : syracuseStep 1903855 = 2855783) B2855783
theorem B2855789 : Blo 1903435 2855789 := bbase (se 3 (by rfl) ⟨535460, by rfl⟩ : syracuseStep 2855789 = 1070921) (by norm_num)
theorem B1903859 : Blo 1903435 1903859 := bstep (se 1 (by rfl) ⟨1427894, by rfl⟩ : syracuseStep 1903859 = 2855789) B2855789
theorem B4283693 : Blo 1903435 4283693 := bbase (se 3 (by rfl) ⟨803192, by rfl⟩ : syracuseStep 4283693 = 1606385) (by norm_num)
theorem B2855795 : Blo 1903435 2855795 := bstep (se 1 (by rfl) ⟨2141846, by rfl⟩ : syracuseStep 2855795 = 4283693) B4283693
theorem B1903863 : Blo 1903435 1903863 := bstep (se 1 (by rfl) ⟨1427897, by rfl⟩ : syracuseStep 1903863 = 2855795) B2855795
theorem B10292501 : Blo 1903435 10292501 := bbase (se 6 (by rfl) ⟨241230, by rfl⟩ : syracuseStep 10292501 = 482461) (by norm_num)
theorem B6861667 : Blo 1903435 6861667 := bstep (se 1 (by rfl) ⟨5146250, by rfl⟩ : syracuseStep 6861667 = 10292501) B10292501
theorem B9148889 : Blo 1903435 9148889 := bstep (se 2 (by rfl) ⟨3430833, by rfl⟩ : syracuseStep 9148889 = 6861667) B6861667
theorem B6099259 : Blo 1903435 6099259 := bstep (se 1 (by rfl) ⟨4574444, by rfl⟩ : syracuseStep 6099259 = 9148889) B9148889
theorem B8132345 : Blo 1903435 8132345 := bstep (se 2 (by rfl) ⟨3049629, by rfl⟩ : syracuseStep 8132345 = 6099259) B6099259
theorem B5421563 : Blo 1903435 5421563 := bstep (se 1 (by rfl) ⟨4066172, by rfl⟩ : syracuseStep 5421563 = 8132345) B8132345
theorem B3614375 : Blo 1903435 3614375 := bstep (se 1 (by rfl) ⟨2710781, by rfl⟩ : syracuseStep 3614375 = 5421563) B5421563
theorem B2409583 : Blo 1903435 2409583 := bstep (se 1 (by rfl) ⟨1807187, by rfl⟩ : syracuseStep 2409583 = 3614375) B3614375
theorem B3212777 : Blo 1903435 3212777 := bstep (se 2 (by rfl) ⟨1204791, by rfl⟩ : syracuseStep 3212777 = 2409583) B2409583
theorem B2141851 : Blo 1903435 2141851 := bstep (se 1 (by rfl) ⟨1606388, by rfl⟩ : syracuseStep 2141851 = 3212777) B3212777
theorem B2855801 : Blo 1903435 2855801 := bstep (se 2 (by rfl) ⟨1070925, by rfl⟩ : syracuseStep 2855801 = 2141851) B2141851
theorem B1903867 : Blo 1903435 1903867 := bstep (se 1 (by rfl) ⟨1427900, by rfl⟩ : syracuseStep 1903867 = 2855801) B2855801
theorem B4342157 : Blo 1903435 4342157 := bbase (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) (by norm_num)
theorem B2894771 : Blo 1903435 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B7719389 : Blo 1903435 7719389 := bstep (se 3 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 7719389 = 2894771) B2894771
theorem B5146259 : Blo 1903435 5146259 := bstep (se 1 (by rfl) ⟨3859694, by rfl⟩ : syracuseStep 5146259 = 7719389) B7719389
theorem B13723357 : Blo 1903435 13723357 := bstep (se 3 (by rfl) ⟨2573129, by rfl⟩ : syracuseStep 13723357 = 5146259) B5146259
theorem B18297809 : Blo 1903435 18297809 := bstep (se 2 (by rfl) ⟨6861678, by rfl⟩ : syracuseStep 18297809 = 13723357) B13723357
theorem B12198539 : Blo 1903435 12198539 := bstep (se 1 (by rfl) ⟨9148904, by rfl⟩ : syracuseStep 12198539 = 18297809) B18297809
theorem B32529437 : Blo 1903435 32529437 := bstep (se 3 (by rfl) ⟨6099269, by rfl⟩ : syracuseStep 32529437 = 12198539) B12198539
theorem B21686291 : Blo 1903435 21686291 := bstep (se 1 (by rfl) ⟨16264718, by rfl⟩ : syracuseStep 21686291 = 32529437) B32529437
theorem B14457527 : Blo 1903435 14457527 := bstep (se 1 (by rfl) ⟨10843145, by rfl⟩ : syracuseStep 14457527 = 21686291) B21686291
theorem B9638351 : Blo 1903435 9638351 := bstep (se 1 (by rfl) ⟨7228763, by rfl⟩ : syracuseStep 9638351 = 14457527) B14457527
theorem B6425567 : Blo 1903435 6425567 := bstep (se 1 (by rfl) ⟨4819175, by rfl⟩ : syracuseStep 6425567 = 9638351) B9638351
theorem B4283711 : Blo 1903435 4283711 := bstep (se 1 (by rfl) ⟨3212783, by rfl⟩ : syracuseStep 4283711 = 6425567) B6425567
theorem B2855807 : Blo 1903435 2855807 := bstep (se 1 (by rfl) ⟨2141855, by rfl⟩ : syracuseStep 2855807 = 4283711) B4283711
theorem B1903871 : Blo 1903435 1903871 := bstep (se 1 (by rfl) ⟨1427903, by rfl⟩ : syracuseStep 1903871 = 2855807) B2855807
theorem B2855813 : Blo 1903435 2855813 := bbase (se 4 (by rfl) ⟨267732, by rfl⟩ : syracuseStep 2855813 = 535465) (by norm_num)
theorem B1903875 : Blo 1903435 1903875 := bstep (se 1 (by rfl) ⟨1427906, by rfl⟩ : syracuseStep 1903875 = 2855813) B2855813
theorem B3212797 : Blo 1903435 3212797 := bbase (se 3 (by rfl) ⟨602399, by rfl⟩ : syracuseStep 3212797 = 1204799) (by norm_num)
theorem B4283729 : Blo 1903435 4283729 := bstep (se 2 (by rfl) ⟨1606398, by rfl⟩ : syracuseStep 4283729 = 3212797) B3212797
theorem B2855819 : Blo 1903435 2855819 := bstep (se 1 (by rfl) ⟨2141864, by rfl⟩ : syracuseStep 2855819 = 4283729) B4283729
theorem B1903879 : Blo 1903435 1903879 := bstep (se 1 (by rfl) ⟨1427909, by rfl⟩ : syracuseStep 1903879 = 2855819) B2855819
theorem B2141869 : Blo 1903435 2141869 := bbase (se 3 (by rfl) ⟨401600, by rfl⟩ : syracuseStep 2141869 = 803201) (by norm_num)
theorem B2855825 : Blo 1903435 2855825 := bstep (se 2 (by rfl) ⟨1070934, by rfl⟩ : syracuseStep 2855825 = 2141869) B2141869
theorem B1903883 : Blo 1903435 1903883 := bstep (se 1 (by rfl) ⟨1427912, by rfl⟩ : syracuseStep 1903883 = 2855825) B2855825
theorem B6425621 : Blo 1903435 6425621 := bbase (se 6 (by rfl) ⟨150600, by rfl⟩ : syracuseStep 6425621 = 301201) (by norm_num)
theorem B4283747 : Blo 1903435 4283747 := bstep (se 1 (by rfl) ⟨3212810, by rfl⟩ : syracuseStep 4283747 = 6425621) B6425621
theorem B2855831 : Blo 1903435 2855831 := bstep (se 1 (by rfl) ⟨2141873, by rfl⟩ : syracuseStep 2855831 = 4283747) B4283747
theorem B1903887 : Blo 1903435 1903887 := bstep (se 1 (by rfl) ⟨1427915, by rfl⟩ : syracuseStep 1903887 = 2855831) B2855831
theorem B2855837 : Blo 1903435 2855837 := bbase (se 3 (by rfl) ⟨535469, by rfl⟩ : syracuseStep 2855837 = 1070939) (by norm_num)
theorem B1903891 : Blo 1903435 1903891 := bstep (se 1 (by rfl) ⟨1427918, by rfl⟩ : syracuseStep 1903891 = 2855837) B2855837
theorem B4283765 : Blo 1903435 4283765 := bbase (se 5 (by rfl) ⟨200801, by rfl⟩ : syracuseStep 4283765 = 401603) (by norm_num)
theorem B2855843 : Blo 1903435 2855843 := bstep (se 1 (by rfl) ⟨2141882, by rfl⟩ : syracuseStep 2855843 = 4283765) B4283765
theorem B1903895 : Blo 1903435 1903895 := bstep (se 1 (by rfl) ⟨1427921, by rfl⟩ : syracuseStep 1903895 = 2855843) B2855843
theorem B6861781 : Blo 1903435 6861781 := bbase (se 7 (by rfl) ⟨80411, by rfl⟩ : syracuseStep 6861781 = 160823) (by norm_num)
theorem B9149041 : Blo 1903435 9149041 := bstep (se 2 (by rfl) ⟨3430890, by rfl⟩ : syracuseStep 9149041 = 6861781) B6861781
theorem B12198721 : Blo 1903435 12198721 := bstep (se 2 (by rfl) ⟨4574520, by rfl⟩ : syracuseStep 12198721 = 9149041) B9149041
theorem B16264961 : Blo 1903435 16264961 := bstep (se 2 (by rfl) ⟨6099360, by rfl⟩ : syracuseStep 16264961 = 12198721) B12198721
theorem B10843307 : Blo 1903435 10843307 := bstep (se 1 (by rfl) ⟨8132480, by rfl⟩ : syracuseStep 10843307 = 16264961) B16264961
theorem B7228871 : Blo 1903435 7228871 := bstep (se 1 (by rfl) ⟨5421653, by rfl⟩ : syracuseStep 7228871 = 10843307) B10843307
theorem B4819247 : Blo 1903435 4819247 := bstep (se 1 (by rfl) ⟨3614435, by rfl⟩ : syracuseStep 4819247 = 7228871) B7228871
theorem B3212831 : Blo 1903435 3212831 := bstep (se 1 (by rfl) ⟨2409623, by rfl⟩ : syracuseStep 3212831 = 4819247) B4819247
theorem B2141887 : Blo 1903435 2141887 := bstep (se 1 (by rfl) ⟨1606415, by rfl⟩ : syracuseStep 2141887 = 3212831) B3212831
theorem B2855849 : Blo 1903435 2855849 := bstep (se 2 (by rfl) ⟨1070943, by rfl⟩ : syracuseStep 2855849 = 2141887) B2141887
theorem B1903899 : Blo 1903435 1903899 := bstep (se 1 (by rfl) ⟨1427924, by rfl⟩ : syracuseStep 1903899 = 2855849) B2855849
theorem B7228885 : Blo 1903435 7228885 := bbase (se 7 (by rfl) ⟨84713, by rfl⟩ : syracuseStep 7228885 = 169427) (by norm_num)
theorem B9638513 : Blo 1903435 9638513 := bstep (se 2 (by rfl) ⟨3614442, by rfl⟩ : syracuseStep 9638513 = 7228885) B7228885
theorem B6425675 : Blo 1903435 6425675 := bstep (se 1 (by rfl) ⟨4819256, by rfl⟩ : syracuseStep 6425675 = 9638513) B9638513
theorem B4283783 : Blo 1903435 4283783 := bstep (se 1 (by rfl) ⟨3212837, by rfl⟩ : syracuseStep 4283783 = 6425675) B6425675
theorem B2855855 : Blo 1903435 2855855 := bstep (se 1 (by rfl) ⟨2141891, by rfl⟩ : syracuseStep 2855855 = 4283783) B4283783
theorem B1903903 : Blo 1903435 1903903 := bstep (se 1 (by rfl) ⟨1427927, by rfl⟩ : syracuseStep 1903903 = 2855855) B2855855
theorem B2855861 : Blo 1903435 2855861 := bbase (se 5 (by rfl) ⟨133868, by rfl⟩ : syracuseStep 2855861 = 267737) (by norm_num)
theorem B1903907 : Blo 1903435 1903907 := bstep (se 1 (by rfl) ⟨1427930, by rfl⟩ : syracuseStep 1903907 = 2855861) B2855861
theorem B4819277 : Blo 1903435 4819277 := bbase (se 3 (by rfl) ⟨903614, by rfl⟩ : syracuseStep 4819277 = 1807229) (by norm_num)
theorem B3212851 : Blo 1903435 3212851 := bstep (se 1 (by rfl) ⟨2409638, by rfl⟩ : syracuseStep 3212851 = 4819277) B4819277
theorem B4283801 : Blo 1903435 4283801 := bstep (se 2 (by rfl) ⟨1606425, by rfl⟩ : syracuseStep 4283801 = 3212851) B3212851
theorem B2855867 : Blo 1903435 2855867 := bstep (se 1 (by rfl) ⟨2141900, by rfl⟩ : syracuseStep 2855867 = 4283801) B4283801
theorem B1903911 : Blo 1903435 1903911 := bstep (se 1 (by rfl) ⟨1427933, by rfl⟩ : syracuseStep 1903911 = 2855867) B2855867
theorem B2141905 : Blo 1903435 2141905 := bbase (se 2 (by rfl) ⟨803214, by rfl⟩ : syracuseStep 2141905 = 1606429) (by norm_num)
theorem B2855873 : Blo 1903435 2855873 := bstep (se 2 (by rfl) ⟨1070952, by rfl⟩ : syracuseStep 2855873 = 2141905) B2141905
theorem B1903915 : Blo 1903435 1903915 := bstep (se 1 (by rfl) ⟨1427936, by rfl⟩ : syracuseStep 1903915 = 2855873) B2855873
theorem B11579381 : Blo 1903435 11579381 := bbase (se 5 (by rfl) ⟨542783, by rfl⟩ : syracuseStep 11579381 = 1085567) (by norm_num)
theorem B7719587 : Blo 1903435 7719587 := bstep (se 1 (by rfl) ⟨5789690, by rfl⟩ : syracuseStep 7719587 = 11579381) B11579381
theorem B5146391 : Blo 1903435 5146391 := bstep (se 1 (by rfl) ⟨3859793, by rfl⟩ : syracuseStep 5146391 = 7719587) B7719587
theorem B3430927 : Blo 1903435 3430927 := bstep (se 1 (by rfl) ⟨2573195, by rfl⟩ : syracuseStep 3430927 = 5146391) B5146391
theorem B4574569 : Blo 1903435 4574569 := bstep (se 2 (by rfl) ⟨1715463, by rfl⟩ : syracuseStep 4574569 = 3430927) B3430927
theorem B6099425 : Blo 1903435 6099425 := bstep (se 2 (by rfl) ⟨2287284, by rfl⟩ : syracuseStep 6099425 = 4574569) B4574569
theorem B4066283 : Blo 1903435 4066283 := bstep (se 1 (by rfl) ⟨3049712, by rfl⟩ : syracuseStep 4066283 = 6099425) B6099425
theorem B2710855 : Blo 1903435 2710855 := bstep (se 1 (by rfl) ⟨2033141, by rfl⟩ : syracuseStep 2710855 = 4066283) B4066283
theorem B3614473 : Blo 1903435 3614473 := bstep (se 2 (by rfl) ⟨1355427, by rfl⟩ : syracuseStep 3614473 = 2710855) B2710855
theorem B4819297 : Blo 1903435 4819297 := bstep (se 2 (by rfl) ⟨1807236, by rfl⟩ : syracuseStep 4819297 = 3614473) B3614473
theorem B6425729 : Blo 1903435 6425729 := bstep (se 2 (by rfl) ⟨2409648, by rfl⟩ : syracuseStep 6425729 = 4819297) B4819297
theorem B4283819 : Blo 1903435 4283819 := bstep (se 1 (by rfl) ⟨3212864, by rfl⟩ : syracuseStep 4283819 = 6425729) B6425729
theorem B2855879 : Blo 1903435 2855879 := bstep (se 1 (by rfl) ⟨2141909, by rfl⟩ : syracuseStep 2855879 = 4283819) B4283819
theorem B1903919 : Blo 1903435 1903919 := bstep (se 1 (by rfl) ⟨1427939, by rfl⟩ : syracuseStep 1903919 = 2855879) B2855879
theorem B2855885 : Blo 1903435 2855885 := bbase (se 3 (by rfl) ⟨535478, by rfl⟩ : syracuseStep 2855885 = 1070957) (by norm_num)
theorem B1903923 : Blo 1903435 1903923 := bstep (se 1 (by rfl) ⟨1427942, by rfl⟩ : syracuseStep 1903923 = 2855885) B2855885
theorem B4283837 : Blo 1903435 4283837 := bbase (se 3 (by rfl) ⟨803219, by rfl⟩ : syracuseStep 4283837 = 1606439) (by norm_num)
theorem B2855891 : Blo 1903435 2855891 := bstep (se 1 (by rfl) ⟨2141918, by rfl⟩ : syracuseStep 2855891 = 4283837) B4283837
theorem B1903927 : Blo 1903435 1903927 := bstep (se 1 (by rfl) ⟨1427945, by rfl⟩ : syracuseStep 1903927 = 2855891) B2855891
theorem B3212885 : Blo 1903435 3212885 := bbase (se 8 (by rfl) ⟨18825, by rfl⟩ : syracuseStep 3212885 = 37651) (by norm_num)
theorem B2141923 : Blo 1903435 2141923 := bstep (se 1 (by rfl) ⟨1606442, by rfl⟩ : syracuseStep 2141923 = 3212885) B3212885
theorem B2855897 : Blo 1903435 2855897 := bstep (se 2 (by rfl) ⟨1070961, by rfl⟩ : syracuseStep 2855897 = 2141923) B2141923
theorem B1903931 : Blo 1903435 1903931 := bstep (se 1 (by rfl) ⟨1427948, by rfl⟩ : syracuseStep 1903931 = 2855897) B2855897
theorem B2894869 : Blo 1903435 2894869 := bbase (se 6 (by rfl) ⟨67848, by rfl⟩ : syracuseStep 2894869 = 135697) (by norm_num)
theorem B3859825 : Blo 1903435 3859825 := bstep (se 2 (by rfl) ⟨1447434, by rfl⟩ : syracuseStep 3859825 = 2894869) B2894869
theorem B5146433 : Blo 1903435 5146433 := bstep (se 2 (by rfl) ⟨1929912, by rfl⟩ : syracuseStep 5146433 = 3859825) B3859825
theorem B3430955 : Blo 1903435 3430955 := bstep (se 1 (by rfl) ⟨2573216, by rfl⟩ : syracuseStep 3430955 = 5146433) B5146433
theorem B9149213 : Blo 1903435 9149213 := bstep (se 3 (by rfl) ⟨1715477, by rfl⟩ : syracuseStep 9149213 = 3430955) B3430955
theorem B6099475 : Blo 1903435 6099475 := bstep (se 1 (by rfl) ⟨4574606, by rfl⟩ : syracuseStep 6099475 = 9149213) B9149213
theorem B8132633 : Blo 1903435 8132633 := bstep (se 2 (by rfl) ⟨3049737, by rfl⟩ : syracuseStep 8132633 = 6099475) B6099475
theorem B5421755 : Blo 1903435 5421755 := bstep (se 1 (by rfl) ⟨4066316, by rfl⟩ : syracuseStep 5421755 = 8132633) B8132633
theorem B14458013 : Blo 1903435 14458013 := bstep (se 3 (by rfl) ⟨2710877, by rfl⟩ : syracuseStep 14458013 = 5421755) B5421755
theorem B9638675 : Blo 1903435 9638675 := bstep (se 1 (by rfl) ⟨7229006, by rfl⟩ : syracuseStep 9638675 = 14458013) B14458013
theorem B6425783 : Blo 1903435 6425783 := bstep (se 1 (by rfl) ⟨4819337, by rfl⟩ : syracuseStep 6425783 = 9638675) B9638675
theorem B4283855 : Blo 1903435 4283855 := bstep (se 1 (by rfl) ⟨3212891, by rfl⟩ : syracuseStep 4283855 = 6425783) B6425783
theorem B2855903 : Blo 1903435 2855903 := bstep (se 1 (by rfl) ⟨2141927, by rfl⟩ : syracuseStep 2855903 = 4283855) B4283855
theorem B1903935 : Blo 1903435 1903935 := bstep (se 1 (by rfl) ⟨1427951, by rfl⟩ : syracuseStep 1903935 = 2855903) B2855903
theorem B2855909 : Blo 1903435 2855909 := bbase (se 4 (by rfl) ⟨267741, by rfl⟩ : syracuseStep 2855909 = 535483) (by norm_num)
theorem B1903939 : Blo 1903435 1903939 := bstep (se 1 (by rfl) ⟨1427954, by rfl⟩ : syracuseStep 1903939 = 2855909) B2855909
theorem B6861941 : Blo 1903435 6861941 := bbase (se 5 (by rfl) ⟨321653, by rfl⟩ : syracuseStep 6861941 = 643307) (by norm_num)
theorem B4574627 : Blo 1903435 4574627 := bstep (se 1 (by rfl) ⟨3430970, by rfl⟩ : syracuseStep 4574627 = 6861941) B6861941
theorem B3049751 : Blo 1903435 3049751 := bstep (se 1 (by rfl) ⟨2287313, by rfl⟩ : syracuseStep 3049751 = 4574627) B4574627
theorem B8132669 : Blo 1903435 8132669 := bstep (se 3 (by rfl) ⟨1524875, by rfl⟩ : syracuseStep 8132669 = 3049751) B3049751
theorem B5421779 : Blo 1903435 5421779 := bstep (se 1 (by rfl) ⟨4066334, by rfl⟩ : syracuseStep 5421779 = 8132669) B8132669
theorem B3614519 : Blo 1903435 3614519 := bstep (se 1 (by rfl) ⟨2710889, by rfl⟩ : syracuseStep 3614519 = 5421779) B5421779
theorem B2409679 : Blo 1903435 2409679 := bstep (se 1 (by rfl) ⟨1807259, by rfl⟩ : syracuseStep 2409679 = 3614519) B3614519
theorem B3212905 : Blo 1903435 3212905 := bstep (se 2 (by rfl) ⟨1204839, by rfl⟩ : syracuseStep 3212905 = 2409679) B2409679
theorem B4283873 : Blo 1903435 4283873 := bstep (se 2 (by rfl) ⟨1606452, by rfl⟩ : syracuseStep 4283873 = 3212905) B3212905
theorem B2855915 : Blo 1903435 2855915 := bstep (se 1 (by rfl) ⟨2141936, by rfl⟩ : syracuseStep 2855915 = 4283873) B4283873
theorem B1903943 : Blo 1903435 1903943 := bstep (se 1 (by rfl) ⟨1427957, by rfl⟩ : syracuseStep 1903943 = 2855915) B2855915
theorem B2141941 : Blo 1903435 2141941 := bbase (se 5 (by rfl) ⟨100403, by rfl⟩ : syracuseStep 2141941 = 200807) (by norm_num)
theorem B2855921 : Blo 1903435 2855921 := bstep (se 2 (by rfl) ⟨1070970, by rfl⟩ : syracuseStep 2855921 = 2141941) B2141941
theorem B1903947 : Blo 1903435 1903947 := bstep (se 1 (by rfl) ⟨1427960, by rfl⟩ : syracuseStep 1903947 = 2855921) B2855921
theorem B2409689 : Blo 1903435 2409689 := bbase (se 2 (by rfl) ⟨903633, by rfl⟩ : syracuseStep 2409689 = 1807267) (by norm_num)
theorem B6425837 : Blo 1903435 6425837 := bstep (se 3 (by rfl) ⟨1204844, by rfl⟩ : syracuseStep 6425837 = 2409689) B2409689
theorem B4283891 : Blo 1903435 4283891 := bstep (se 1 (by rfl) ⟨3212918, by rfl⟩ : syracuseStep 4283891 = 6425837) B6425837
theorem B2855927 : Blo 1903435 2855927 := bstep (se 1 (by rfl) ⟨2141945, by rfl⟩ : syracuseStep 2855927 = 4283891) B4283891
theorem B1903951 : Blo 1903435 1903951 := bstep (se 1 (by rfl) ⟨1427963, by rfl⟩ : syracuseStep 1903951 = 2855927) B2855927
theorem B2855933 : Blo 1903435 2855933 := bbase (se 3 (by rfl) ⟨535487, by rfl⟩ : syracuseStep 2855933 = 1070975) (by norm_num)
theorem B1903955 : Blo 1903435 1903955 := bstep (se 1 (by rfl) ⟨1427966, by rfl⟩ : syracuseStep 1903955 = 2855933) B2855933
theorem B4283909 : Blo 1903435 4283909 := bbase (se 4 (by rfl) ⟨401616, by rfl⟩ : syracuseStep 4283909 = 803233) (by norm_num)
theorem B2855939 : Blo 1903435 2855939 := bstep (se 1 (by rfl) ⟨2141954, by rfl⟩ : syracuseStep 2855939 = 4283909) B4283909
theorem B1903959 : Blo 1903435 1903959 := bstep (se 1 (by rfl) ⟨1427969, by rfl⟩ : syracuseStep 1903959 = 2855939) B2855939
theorem B3614557 : Blo 1903435 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B4819409 : Blo 1903435 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B3212939 : Blo 1903435 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B2141959 : Blo 1903435 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B2855945 : Blo 1903435 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B1903963 : Blo 1903435 1903963 := bstep (se 1 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 1903963 = 2855945) B2855945
theorem B9638837 : Blo 1903435 9638837 := bbase (se 5 (by rfl) ⟨451820, by rfl⟩ : syracuseStep 9638837 = 903641) (by norm_num)
theorem B6425891 : Blo 1903435 6425891 := bstep (se 1 (by rfl) ⟨4819418, by rfl⟩ : syracuseStep 6425891 = 9638837) B9638837
theorem B4283927 : Blo 1903435 4283927 := bstep (se 1 (by rfl) ⟨3212945, by rfl⟩ : syracuseStep 4283927 = 6425891) B6425891
theorem B2855951 : Blo 1903435 2855951 := bstep (se 1 (by rfl) ⟨2141963, by rfl⟩ : syracuseStep 2855951 = 4283927) B4283927
theorem B1903967 : Blo 1903435 1903967 := bstep (se 1 (by rfl) ⟨1427975, by rfl⟩ : syracuseStep 1903967 = 2855951) B2855951
theorem B2855957 : Blo 1903435 2855957 := bbase (se 6 (by rfl) ⟨66936, by rfl⟩ : syracuseStep 2855957 = 133873) (by norm_num)
theorem B1903971 : Blo 1903435 1903971 := bstep (se 1 (by rfl) ⟨1427978, by rfl⟩ : syracuseStep 1903971 = 2855957) B2855957
theorem B2171197 : Blo 1903435 2171197 := bbase (se 3 (by rfl) ⟨407099, by rfl⟩ : syracuseStep 2171197 = 814199) (by norm_num)
theorem B11579717 : Blo 1903435 11579717 := bstep (se 4 (by rfl) ⟨1085598, by rfl⟩ : syracuseStep 11579717 = 2171197) B2171197
theorem B30879245 : Blo 1903435 30879245 := bstep (se 3 (by rfl) ⟨5789858, by rfl⟩ : syracuseStep 30879245 = 11579717) B11579717
theorem B20586163 : Blo 1903435 20586163 := bstep (se 1 (by rfl) ⟨15439622, by rfl⟩ : syracuseStep 20586163 = 30879245) B30879245
theorem B27448217 : Blo 1903435 27448217 := bstep (se 2 (by rfl) ⟨10293081, by rfl⟩ : syracuseStep 27448217 = 20586163) B20586163
theorem B18298811 : Blo 1903435 18298811 := bstep (se 1 (by rfl) ⟨13724108, by rfl⟩ : syracuseStep 18298811 = 27448217) B27448217
theorem B12199207 : Blo 1903435 12199207 := bstep (se 1 (by rfl) ⟨9149405, by rfl⟩ : syracuseStep 12199207 = 18298811) B18298811
theorem B16265609 : Blo 1903435 16265609 := bstep (se 2 (by rfl) ⟨6099603, by rfl⟩ : syracuseStep 16265609 = 12199207) B12199207
theorem B10843739 : Blo 1903435 10843739 := bstep (se 1 (by rfl) ⟨8132804, by rfl⟩ : syracuseStep 10843739 = 16265609) B16265609
theorem B7229159 : Blo 1903435 7229159 := bstep (se 1 (by rfl) ⟨5421869, by rfl⟩ : syracuseStep 7229159 = 10843739) B10843739
theorem B4819439 : Blo 1903435 4819439 := bstep (se 1 (by rfl) ⟨3614579, by rfl⟩ : syracuseStep 4819439 = 7229159) B7229159
theorem B3212959 : Blo 1903435 3212959 := bstep (se 1 (by rfl) ⟨2409719, by rfl⟩ : syracuseStep 3212959 = 4819439) B4819439
theorem B4283945 : Blo 1903435 4283945 := bstep (se 2 (by rfl) ⟨1606479, by rfl⟩ : syracuseStep 4283945 = 3212959) B3212959
theorem B2855963 : Blo 1903435 2855963 := bstep (se 1 (by rfl) ⟨2141972, by rfl⟩ : syracuseStep 2855963 = 4283945) B4283945
theorem B1903975 : Blo 1903435 1903975 := bstep (se 1 (by rfl) ⟨1427981, by rfl⟩ : syracuseStep 1903975 = 2855963) B2855963
theorem B2141977 : Blo 1903435 2141977 := bbase (se 2 (by rfl) ⟨803241, by rfl⟩ : syracuseStep 2141977 = 1606483) (by norm_num)
theorem B2855969 : Blo 1903435 2855969 := bstep (se 2 (by rfl) ⟨1070988, by rfl⟩ : syracuseStep 2855969 = 2141977) B2141977
theorem B1903979 : Blo 1903435 1903979 := bstep (se 1 (by rfl) ⟨1427984, by rfl⟩ : syracuseStep 1903979 = 2855969) B2855969
theorem B7229189 : Blo 1903435 7229189 := bbase (se 4 (by rfl) ⟨677736, by rfl⟩ : syracuseStep 7229189 = 1355473) (by norm_num)
theorem B4819459 : Blo 1903435 4819459 := bstep (se 1 (by rfl) ⟨3614594, by rfl⟩ : syracuseStep 4819459 = 7229189) B7229189
theorem B6425945 : Blo 1903435 6425945 := bstep (se 2 (by rfl) ⟨2409729, by rfl⟩ : syracuseStep 6425945 = 4819459) B4819459
theorem B4283963 : Blo 1903435 4283963 := bstep (se 1 (by rfl) ⟨3212972, by rfl⟩ : syracuseStep 4283963 = 6425945) B6425945
theorem B2855975 : Blo 1903435 2855975 := bstep (se 1 (by rfl) ⟨2141981, by rfl⟩ : syracuseStep 2855975 = 4283963) B4283963
theorem B1903983 : Blo 1903435 1903983 := bstep (se 1 (by rfl) ⟨1427987, by rfl⟩ : syracuseStep 1903983 = 2855975) B2855975
theorem B2855981 : Blo 1903435 2855981 := bbase (se 3 (by rfl) ⟨535496, by rfl⟩ : syracuseStep 2855981 = 1070993) (by norm_num)
theorem B1903987 : Blo 1903435 1903987 := bstep (se 1 (by rfl) ⟨1427990, by rfl⟩ : syracuseStep 1903987 = 2855981) B2855981
theorem B4283981 : Blo 1903435 4283981 := bbase (se 3 (by rfl) ⟨803246, by rfl⟩ : syracuseStep 4283981 = 1606493) (by norm_num)
theorem B2855987 : Blo 1903435 2855987 := bstep (se 1 (by rfl) ⟨2141990, by rfl⟩ : syracuseStep 2855987 = 4283981) B4283981
theorem B1903991 : Blo 1903435 1903991 := bstep (se 1 (by rfl) ⟨1427993, by rfl⟩ : syracuseStep 1903991 = 2855987) B2855987
theorem B2409745 : Blo 1903435 2409745 := bbase (se 2 (by rfl) ⟨903654, by rfl⟩ : syracuseStep 2409745 = 1807309) (by norm_num)
theorem B3212993 : Blo 1903435 3212993 := bstep (se 2 (by rfl) ⟨1204872, by rfl⟩ : syracuseStep 3212993 = 2409745) B2409745
theorem B2141995 : Blo 1903435 2141995 := bstep (se 1 (by rfl) ⟨1606496, by rfl⟩ : syracuseStep 2141995 = 3212993) B3212993
theorem B2855993 : Blo 1903435 2855993 := bstep (se 2 (by rfl) ⟨1070997, by rfl⟩ : syracuseStep 2855993 = 2141995) B2141995
theorem B1903995 : Blo 1903435 1903995 := bstep (se 1 (by rfl) ⟨1427996, by rfl⟩ : syracuseStep 1903995 = 2855993) B2855993
theorem B4066453 : Blo 1903435 4066453 := bbase (se 6 (by rfl) ⟨95307, by rfl⟩ : syracuseStep 4066453 = 190615) (by norm_num)
theorem B21687749 : Blo 1903435 21687749 := bstep (se 4 (by rfl) ⟨2033226, by rfl⟩ : syracuseStep 21687749 = 4066453) B4066453
theorem B14458499 : Blo 1903435 14458499 := bstep (se 1 (by rfl) ⟨10843874, by rfl⟩ : syracuseStep 14458499 = 21687749) B21687749
theorem B9638999 : Blo 1903435 9638999 := bstep (se 1 (by rfl) ⟨7229249, by rfl⟩ : syracuseStep 9638999 = 14458499) B14458499
theorem B6425999 : Blo 1903435 6425999 := bstep (se 1 (by rfl) ⟨4819499, by rfl⟩ : syracuseStep 6425999 = 9638999) B9638999
theorem B4283999 : Blo 1903435 4283999 := bstep (se 1 (by rfl) ⟨3212999, by rfl⟩ : syracuseStep 4283999 = 6425999) B6425999
theorem B2855999 : Blo 1903435 2855999 := bstep (se 1 (by rfl) ⟨2141999, by rfl⟩ : syracuseStep 2855999 = 4283999) B4283999
theorem B1903999 : Blo 1903435 1903999 := bstep (se 1 (by rfl) ⟨1427999, by rfl⟩ : syracuseStep 1903999 = 2855999) B2855999
theorem B2856005 : Blo 1903435 2856005 := bbase (se 4 (by rfl) ⟨267750, by rfl⟩ : syracuseStep 2856005 = 535501) (by norm_num)
theorem B1904003 : Blo 1903435 1904003 := bstep (se 1 (by rfl) ⟨1428002, by rfl⟩ : syracuseStep 1904003 = 2856005) B2856005
theorem B3213013 : Blo 1903435 3213013 := bbase (se 7 (by rfl) ⟨37652, by rfl⟩ : syracuseStep 3213013 = 75305) (by norm_num)
theorem B4284017 : Blo 1903435 4284017 := bstep (se 2 (by rfl) ⟨1606506, by rfl⟩ : syracuseStep 4284017 = 3213013) B3213013
theorem B2856011 : Blo 1903435 2856011 := bstep (se 1 (by rfl) ⟨2142008, by rfl⟩ : syracuseStep 2856011 = 4284017) B4284017
theorem B1904007 : Blo 1903435 1904007 := bstep (se 1 (by rfl) ⟨1428005, by rfl⟩ : syracuseStep 1904007 = 2856011) B2856011
theorem B2142013 : Blo 1903435 2142013 := bbase (se 3 (by rfl) ⟨401627, by rfl⟩ : syracuseStep 2142013 = 803255) (by norm_num)
theorem B2856017 : Blo 1903435 2856017 := bstep (se 2 (by rfl) ⟨1071006, by rfl⟩ : syracuseStep 2856017 = 2142013) B2142013
theorem B1904011 : Blo 1903435 1904011 := bstep (se 1 (by rfl) ⟨1428008, by rfl⟩ : syracuseStep 1904011 = 2856017) B2856017
theorem B6426053 : Blo 1903435 6426053 := bbase (se 4 (by rfl) ⟨602442, by rfl⟩ : syracuseStep 6426053 = 1204885) (by norm_num)
theorem B4284035 : Blo 1903435 4284035 := bstep (se 1 (by rfl) ⟨3213026, by rfl⟩ : syracuseStep 4284035 = 6426053) B6426053
theorem B2856023 : Blo 1903435 2856023 := bstep (se 1 (by rfl) ⟨2142017, by rfl⟩ : syracuseStep 2856023 = 4284035) B4284035
theorem B1904015 : Blo 1903435 1904015 := bstep (se 1 (by rfl) ⟨1428011, by rfl⟩ : syracuseStep 1904015 = 2856023) B2856023
theorem B2856029 : Blo 1903435 2856029 := bbase (se 3 (by rfl) ⟨535505, by rfl⟩ : syracuseStep 2856029 = 1071011) (by norm_num)
theorem B1904019 : Blo 1903435 1904019 := bstep (se 1 (by rfl) ⟨1428014, by rfl⟩ : syracuseStep 1904019 = 2856029) B2856029
theorem B4284053 : Blo 1903435 4284053 := bbase (se 6 (by rfl) ⟨100407, by rfl⟩ : syracuseStep 4284053 = 200815) (by norm_num)
theorem B2856035 : Blo 1903435 2856035 := bstep (se 1 (by rfl) ⟨2142026, by rfl⟩ : syracuseStep 2856035 = 4284053) B4284053
theorem B1904023 : Blo 1903435 1904023 := bstep (se 1 (by rfl) ⟨1428017, by rfl⟩ : syracuseStep 1904023 = 2856035) B2856035
theorem B2033257 : Blo 1903435 2033257 := bbase (se 2 (by rfl) ⟨762471, by rfl⟩ : syracuseStep 2033257 = 1524943) (by norm_num)
theorem B2711009 : Blo 1903435 2711009 := bstep (se 2 (by rfl) ⟨1016628, by rfl⟩ : syracuseStep 2711009 = 2033257) B2033257
theorem B7229357 : Blo 1903435 7229357 := bstep (se 3 (by rfl) ⟨1355504, by rfl⟩ : syracuseStep 7229357 = 2711009) B2711009
theorem B4819571 : Blo 1903435 4819571 := bstep (se 1 (by rfl) ⟨3614678, by rfl⟩ : syracuseStep 4819571 = 7229357) B7229357
theorem B3213047 : Blo 1903435 3213047 := bstep (se 1 (by rfl) ⟨2409785, by rfl⟩ : syracuseStep 3213047 = 4819571) B4819571
theorem B2142031 : Blo 1903435 2142031 := bstep (se 1 (by rfl) ⟨1606523, by rfl⟩ : syracuseStep 2142031 = 3213047) B3213047
theorem B2856041 : Blo 1903435 2856041 := bstep (se 2 (by rfl) ⟨1071015, by rfl⟩ : syracuseStep 2856041 = 2142031) B2142031
theorem B1904027 : Blo 1903435 1904027 := bstep (se 1 (by rfl) ⟨1428020, by rfl⟩ : syracuseStep 1904027 = 2856041) B2856041
theorem B4574837 : Blo 1903435 4574837 := bbase (se 5 (by rfl) ⟨214445, by rfl⟩ : syracuseStep 4574837 = 428891) (by norm_num)
theorem B12199565 : Blo 1903435 12199565 := bstep (se 3 (by rfl) ⟨2287418, by rfl⟩ : syracuseStep 12199565 = 4574837) B4574837
theorem B8133043 : Blo 1903435 8133043 := bstep (se 1 (by rfl) ⟨6099782, by rfl⟩ : syracuseStep 8133043 = 12199565) B12199565
theorem B10844057 : Blo 1903435 10844057 := bstep (se 2 (by rfl) ⟨4066521, by rfl⟩ : syracuseStep 10844057 = 8133043) B8133043
theorem B7229371 : Blo 1903435 7229371 := bstep (se 1 (by rfl) ⟨5422028, by rfl⟩ : syracuseStep 7229371 = 10844057) B10844057
theorem B9639161 : Blo 1903435 9639161 := bstep (se 2 (by rfl) ⟨3614685, by rfl⟩ : syracuseStep 9639161 = 7229371) B7229371
theorem B6426107 : Blo 1903435 6426107 := bstep (se 1 (by rfl) ⟨4819580, by rfl⟩ : syracuseStep 6426107 = 9639161) B9639161
theorem B4284071 : Blo 1903435 4284071 := bstep (se 1 (by rfl) ⟨3213053, by rfl⟩ : syracuseStep 4284071 = 6426107) B6426107
theorem B2856047 : Blo 1903435 2856047 := bstep (se 1 (by rfl) ⟨2142035, by rfl⟩ : syracuseStep 2856047 = 4284071) B4284071
theorem B1904031 : Blo 1903435 1904031 := bstep (se 1 (by rfl) ⟨1428023, by rfl⟩ : syracuseStep 1904031 = 2856047) B2856047
theorem B2856053 : Blo 1903435 2856053 := bbase (se 5 (by rfl) ⟨133877, by rfl⟩ : syracuseStep 2856053 = 267755) (by norm_num)
theorem B1904035 : Blo 1903435 1904035 := bstep (se 1 (by rfl) ⟨1428026, by rfl⟩ : syracuseStep 1904035 = 2856053) B2856053
theorem B3614701 : Blo 1903435 3614701 := bbase (se 3 (by rfl) ⟨677756, by rfl⟩ : syracuseStep 3614701 = 1355513) (by norm_num)
theorem B4819601 : Blo 1903435 4819601 := bstep (se 2 (by rfl) ⟨1807350, by rfl⟩ : syracuseStep 4819601 = 3614701) B3614701
theorem B3213067 : Blo 1903435 3213067 := bstep (se 1 (by rfl) ⟨2409800, by rfl⟩ : syracuseStep 3213067 = 4819601) B4819601
theorem B4284089 : Blo 1903435 4284089 := bstep (se 2 (by rfl) ⟨1606533, by rfl⟩ : syracuseStep 4284089 = 3213067) B3213067
theorem B2856059 : Blo 1903435 2856059 := bstep (se 1 (by rfl) ⟨2142044, by rfl⟩ : syracuseStep 2856059 = 4284089) B4284089
theorem B1904039 : Blo 1903435 1904039 := bstep (se 1 (by rfl) ⟨1428029, by rfl⟩ : syracuseStep 1904039 = 2856059) B2856059
theorem B2142049 : Blo 1903435 2142049 := bbase (se 2 (by rfl) ⟨803268, by rfl⟩ : syracuseStep 2142049 = 1606537) (by norm_num)
theorem B2856065 : Blo 1903435 2856065 := bstep (se 2 (by rfl) ⟨1071024, by rfl⟩ : syracuseStep 2856065 = 2142049) B2142049
theorem B1904043 : Blo 1903435 1904043 := bstep (se 1 (by rfl) ⟨1428032, by rfl⟩ : syracuseStep 1904043 = 2856065) B2856065
theorem B4819621 : Blo 1903435 4819621 := bbase (se 4 (by rfl) ⟨451839, by rfl⟩ : syracuseStep 4819621 = 903679) (by norm_num)
theorem B6426161 : Blo 1903435 6426161 := bstep (se 2 (by rfl) ⟨2409810, by rfl⟩ : syracuseStep 6426161 = 4819621) B4819621
theorem B4284107 : Blo 1903435 4284107 := bstep (se 1 (by rfl) ⟨3213080, by rfl⟩ : syracuseStep 4284107 = 6426161) B6426161
theorem B2856071 : Blo 1903435 2856071 := bstep (se 1 (by rfl) ⟨2142053, by rfl⟩ : syracuseStep 2856071 = 4284107) B4284107
theorem B1904047 : Blo 1903435 1904047 := bstep (se 1 (by rfl) ⟨1428035, by rfl⟩ : syracuseStep 1904047 = 2856071) B2856071
theorem B2856077 : Blo 1903435 2856077 := bbase (se 3 (by rfl) ⟨535514, by rfl⟩ : syracuseStep 2856077 = 1071029) (by norm_num)
theorem B1904051 : Blo 1903435 1904051 := bstep (se 1 (by rfl) ⟨1428038, by rfl⟩ : syracuseStep 1904051 = 2856077) B2856077
theorem B4284125 : Blo 1903435 4284125 := bbase (se 3 (by rfl) ⟨803273, by rfl⟩ : syracuseStep 4284125 = 1606547) (by norm_num)
theorem B2856083 : Blo 1903435 2856083 := bstep (se 1 (by rfl) ⟨2142062, by rfl⟩ : syracuseStep 2856083 = 4284125) B4284125
theorem B1904055 : Blo 1903435 1904055 := bstep (se 1 (by rfl) ⟨1428041, by rfl⟩ : syracuseStep 1904055 = 2856083) B2856083
theorem B3213101 : Blo 1903435 3213101 := bbase (se 3 (by rfl) ⟨602456, by rfl⟩ : syracuseStep 3213101 = 1204913) (by norm_num)
theorem B2142067 : Blo 1903435 2142067 := bstep (se 1 (by rfl) ⟨1606550, by rfl⟩ : syracuseStep 2142067 = 3213101) B3213101
theorem B2856089 : Blo 1903435 2856089 := bstep (se 2 (by rfl) ⟨1071033, by rfl⟩ : syracuseStep 2856089 = 2142067) B2142067
theorem B1904059 : Blo 1903435 1904059 := bstep (se 1 (by rfl) ⟨1428044, by rfl⟩ : syracuseStep 1904059 = 2856089) B2856089
theorem B2573389 : Blo 1903435 2573389 := bbase (se 3 (by rfl) ⟨482510, by rfl⟩ : syracuseStep 2573389 = 965021) (by norm_num)
theorem B13724741 : Blo 1903435 13724741 := bstep (se 4 (by rfl) ⟨1286694, by rfl⟩ : syracuseStep 13724741 = 2573389) B2573389
theorem B36599309 : Blo 1903435 36599309 := bstep (se 3 (by rfl) ⟨6862370, by rfl⟩ : syracuseStep 36599309 = 13724741) B13724741
theorem B24399539 : Blo 1903435 24399539 := bstep (se 1 (by rfl) ⟨18299654, by rfl⟩ : syracuseStep 24399539 = 36599309) B36599309
theorem B16266359 : Blo 1903435 16266359 := bstep (se 1 (by rfl) ⟨12199769, by rfl⟩ : syracuseStep 16266359 = 24399539) B24399539
theorem B10844239 : Blo 1903435 10844239 := bstep (se 1 (by rfl) ⟨8133179, by rfl⟩ : syracuseStep 10844239 = 16266359) B16266359
theorem B14458985 : Blo 1903435 14458985 := bstep (se 2 (by rfl) ⟨5422119, by rfl⟩ : syracuseStep 14458985 = 10844239) B10844239
theorem B9639323 : Blo 1903435 9639323 := bstep (se 1 (by rfl) ⟨7229492, by rfl⟩ : syracuseStep 9639323 = 14458985) B14458985
theorem B6426215 : Blo 1903435 6426215 := bstep (se 1 (by rfl) ⟨4819661, by rfl⟩ : syracuseStep 6426215 = 9639323) B9639323
theorem B4284143 : Blo 1903435 4284143 := bstep (se 1 (by rfl) ⟨3213107, by rfl⟩ : syracuseStep 4284143 = 6426215) B6426215
theorem B2856095 : Blo 1903435 2856095 := bstep (se 1 (by rfl) ⟨2142071, by rfl⟩ : syracuseStep 2856095 = 4284143) B4284143
theorem B1904063 : Blo 1903435 1904063 := bstep (se 1 (by rfl) ⟨1428047, by rfl⟩ : syracuseStep 1904063 = 2856095) B2856095
theorem B2856101 : Blo 1903435 2856101 := bbase (se 4 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 2856101 = 535519) (by norm_num)
theorem B1904067 : Blo 1903435 1904067 := bstep (se 1 (by rfl) ⟨1428050, by rfl⟩ : syracuseStep 1904067 = 2856101) B2856101
theorem B2409841 : Blo 1903435 2409841 := bbase (se 2 (by rfl) ⟨903690, by rfl⟩ : syracuseStep 2409841 = 1807381) (by norm_num)
theorem B3213121 : Blo 1903435 3213121 := bstep (se 2 (by rfl) ⟨1204920, by rfl⟩ : syracuseStep 3213121 = 2409841) B2409841
theorem B4284161 : Blo 1903435 4284161 := bstep (se 2 (by rfl) ⟨1606560, by rfl⟩ : syracuseStep 4284161 = 3213121) B3213121
theorem B2856107 : Blo 1903435 2856107 := bstep (se 1 (by rfl) ⟨2142080, by rfl⟩ : syracuseStep 2856107 = 4284161) B4284161
theorem B1904071 : Blo 1903435 1904071 := bstep (se 1 (by rfl) ⟨1428053, by rfl⟩ : syracuseStep 1904071 = 2856107) B2856107
theorem B2142085 : Blo 1903435 2142085 := bbase (se 4 (by rfl) ⟨200820, by rfl⟩ : syracuseStep 2142085 = 401641) (by norm_num)
theorem B2856113 : Blo 1903435 2856113 := bstep (se 2 (by rfl) ⟨1071042, by rfl⟩ : syracuseStep 2856113 = 2142085) B2142085
theorem B1904075 : Blo 1903435 1904075 := bstep (se 1 (by rfl) ⟨1428056, by rfl⟩ : syracuseStep 1904075 = 2856113) B2856113
theorem B2287477 : Blo 1903435 2287477 := bbase (se 5 (by rfl) ⟨107225, by rfl⟩ : syracuseStep 2287477 = 214451) (by norm_num)
theorem B3049969 : Blo 1903435 3049969 := bstep (se 2 (by rfl) ⟨1143738, by rfl⟩ : syracuseStep 3049969 = 2287477) B2287477
theorem B4066625 : Blo 1903435 4066625 := bstep (se 2 (by rfl) ⟨1524984, by rfl⟩ : syracuseStep 4066625 = 3049969) B3049969
theorem B2711083 : Blo 1903435 2711083 := bstep (se 1 (by rfl) ⟨2033312, by rfl⟩ : syracuseStep 2711083 = 4066625) B4066625
theorem B3614777 : Blo 1903435 3614777 := bstep (se 2 (by rfl) ⟨1355541, by rfl⟩ : syracuseStep 3614777 = 2711083) B2711083
theorem B2409851 : Blo 1903435 2409851 := bstep (se 1 (by rfl) ⟨1807388, by rfl⟩ : syracuseStep 2409851 = 3614777) B3614777
theorem B6426269 : Blo 1903435 6426269 := bstep (se 3 (by rfl) ⟨1204925, by rfl⟩ : syracuseStep 6426269 = 2409851) B2409851
theorem B4284179 : Blo 1903435 4284179 := bstep (se 1 (by rfl) ⟨3213134, by rfl⟩ : syracuseStep 4284179 = 6426269) B6426269
theorem B2856119 : Blo 1903435 2856119 := bstep (se 1 (by rfl) ⟨2142089, by rfl⟩ : syracuseStep 2856119 = 4284179) B4284179
theorem B1904079 : Blo 1903435 1904079 := bstep (se 1 (by rfl) ⟨1428059, by rfl⟩ : syracuseStep 1904079 = 2856119) B2856119
theorem B2856125 : Blo 1903435 2856125 := bbase (se 3 (by rfl) ⟨535523, by rfl⟩ : syracuseStep 2856125 = 1071047) (by norm_num)
theorem B1904083 : Blo 1903435 1904083 := bstep (se 1 (by rfl) ⟨1428062, by rfl⟩ : syracuseStep 1904083 = 2856125) B2856125
theorem B4284197 : Blo 1903435 4284197 := bbase (se 4 (by rfl) ⟨401643, by rfl⟩ : syracuseStep 4284197 = 803287) (by norm_num)
theorem B2856131 : Blo 1903435 2856131 := bstep (se 1 (by rfl) ⟨2142098, by rfl⟩ : syracuseStep 2856131 = 4284197) B4284197
theorem B1904087 : Blo 1903435 1904087 := bstep (se 1 (by rfl) ⟨1428065, by rfl⟩ : syracuseStep 1904087 = 2856131) B2856131
theorem B4819733 : Blo 1903435 4819733 := bbase (se 6 (by rfl) ⟨112962, by rfl⟩ : syracuseStep 4819733 = 225925) (by norm_num)
theorem B3213155 : Blo 1903435 3213155 := bstep (se 1 (by rfl) ⟨2409866, by rfl⟩ : syracuseStep 3213155 = 4819733) B4819733
theorem B2142103 : Blo 1903435 2142103 := bstep (se 1 (by rfl) ⟨1606577, by rfl⟩ : syracuseStep 2142103 = 3213155) B3213155
theorem B2856137 : Blo 1903435 2856137 := bstep (se 2 (by rfl) ⟨1071051, by rfl⟩ : syracuseStep 2856137 = 2142103) B2142103
theorem B1904091 : Blo 1903435 1904091 := bstep (se 1 (by rfl) ⟨1428068, by rfl⟩ : syracuseStep 1904091 = 2856137) B2856137
theorem B8133317 : Blo 1903435 8133317 := bbase (se 4 (by rfl) ⟨762498, by rfl⟩ : syracuseStep 8133317 = 1524997) (by norm_num)
theorem B5422211 : Blo 1903435 5422211 := bstep (se 1 (by rfl) ⟨4066658, by rfl⟩ : syracuseStep 5422211 = 8133317) B8133317
theorem B3614807 : Blo 1903435 3614807 := bstep (se 1 (by rfl) ⟨2711105, by rfl⟩ : syracuseStep 3614807 = 5422211) B5422211
theorem B9639485 : Blo 1903435 9639485 := bstep (se 3 (by rfl) ⟨1807403, by rfl⟩ : syracuseStep 9639485 = 3614807) B3614807
theorem B6426323 : Blo 1903435 6426323 := bstep (se 1 (by rfl) ⟨4819742, by rfl⟩ : syracuseStep 6426323 = 9639485) B9639485
theorem B4284215 : Blo 1903435 4284215 := bstep (se 1 (by rfl) ⟨3213161, by rfl⟩ : syracuseStep 4284215 = 6426323) B6426323
theorem B2856143 : Blo 1903435 2856143 := bstep (se 1 (by rfl) ⟨2142107, by rfl⟩ : syracuseStep 2856143 = 4284215) B4284215
theorem B1904095 : Blo 1903435 1904095 := bstep (se 1 (by rfl) ⟨1428071, by rfl⟩ : syracuseStep 1904095 = 2856143) B2856143
theorem B2856149 : Blo 1903435 2856149 := bbase (se 7 (by rfl) ⟨33470, by rfl⟩ : syracuseStep 2856149 = 66941) (by norm_num)
theorem B1904099 : Blo 1903435 1904099 := bstep (se 1 (by rfl) ⟨1428074, by rfl⟩ : syracuseStep 1904099 = 2856149) B2856149
theorem B2711117 : Blo 1903435 2711117 := bbase (se 3 (by rfl) ⟨508334, by rfl⟩ : syracuseStep 2711117 = 1016669) (by norm_num)
theorem B7229645 : Blo 1903435 7229645 := bstep (se 3 (by rfl) ⟨1355558, by rfl⟩ : syracuseStep 7229645 = 2711117) B2711117
theorem B4819763 : Blo 1903435 4819763 := bstep (se 1 (by rfl) ⟨3614822, by rfl⟩ : syracuseStep 4819763 = 7229645) B7229645
theorem B3213175 : Blo 1903435 3213175 := bstep (se 1 (by rfl) ⟨2409881, by rfl⟩ : syracuseStep 3213175 = 4819763) B4819763
theorem B4284233 : Blo 1903435 4284233 := bstep (se 2 (by rfl) ⟨1606587, by rfl⟩ : syracuseStep 4284233 = 3213175) B3213175
theorem B2856155 : Blo 1903435 2856155 := bstep (se 1 (by rfl) ⟨2142116, by rfl⟩ : syracuseStep 2856155 = 4284233) B4284233
theorem B1904103 : Blo 1903435 1904103 := bstep (se 1 (by rfl) ⟨1428077, by rfl⟩ : syracuseStep 1904103 = 2856155) B2856155
theorem B2142121 : Blo 1903435 2142121 := bbase (se 2 (by rfl) ⟨803295, by rfl⟩ : syracuseStep 2142121 = 1606591) (by norm_num)
theorem B2856161 : Blo 1903435 2856161 := bstep (se 2 (by rfl) ⟨1071060, by rfl⟩ : syracuseStep 2856161 = 2142121) B2142121
theorem B1904107 : Blo 1903435 1904107 := bstep (se 1 (by rfl) ⟨1428080, by rfl⟩ : syracuseStep 1904107 = 2856161) B2856161
theorem B2318725 : Blo 1903435 2318725 := bbase (se 4 (by rfl) ⟨217380, by rfl⟩ : syracuseStep 2318725 = 434761) (by norm_num)
theorem B12366533 : Blo 1903435 12366533 := bstep (se 4 (by rfl) ⟨1159362, by rfl⟩ : syracuseStep 12366533 = 2318725) B2318725
theorem B8244355 : Blo 1903435 8244355 := bstep (se 1 (by rfl) ⟨6183266, by rfl⟩ : syracuseStep 8244355 = 12366533) B12366533
theorem B10992473 : Blo 1903435 10992473 := bstep (se 2 (by rfl) ⟨4122177, by rfl⟩ : syracuseStep 10992473 = 8244355) B8244355
theorem B7328315 : Blo 1903435 7328315 := bstep (se 1 (by rfl) ⟨5496236, by rfl⟩ : syracuseStep 7328315 = 10992473) B10992473
theorem B4885543 : Blo 1903435 4885543 := bstep (se 1 (by rfl) ⟨3664157, by rfl⟩ : syracuseStep 4885543 = 7328315) B7328315
theorem B6514057 : Blo 1903435 6514057 := bstep (se 2 (by rfl) ⟨2442771, by rfl⟩ : syracuseStep 6514057 = 4885543) B4885543
theorem B8685409 : Blo 1903435 8685409 := bstep (se 2 (by rfl) ⟨3257028, by rfl⟩ : syracuseStep 8685409 = 6514057) B6514057
theorem B11580545 : Blo 1903435 11580545 := bstep (se 2 (by rfl) ⟨4342704, by rfl⟩ : syracuseStep 11580545 = 8685409) B8685409
theorem B7720363 : Blo 1903435 7720363 := bstep (se 1 (by rfl) ⟨5790272, by rfl⟩ : syracuseStep 7720363 = 11580545) B11580545
theorem B10293817 : Blo 1903435 10293817 := bstep (se 2 (by rfl) ⟨3860181, by rfl⟩ : syracuseStep 10293817 = 7720363) B7720363
theorem B13725089 : Blo 1903435 13725089 := bstep (se 2 (by rfl) ⟨5146908, by rfl⟩ : syracuseStep 13725089 = 10293817) B10293817
theorem B9150059 : Blo 1903435 9150059 := bstep (se 1 (by rfl) ⟨6862544, by rfl⟩ : syracuseStep 9150059 = 13725089) B13725089
theorem B6100039 : Blo 1903435 6100039 := bstep (se 1 (by rfl) ⟨4575029, by rfl⟩ : syracuseStep 6100039 = 9150059) B9150059
theorem B8133385 : Blo 1903435 8133385 := bstep (se 2 (by rfl) ⟨3050019, by rfl⟩ : syracuseStep 8133385 = 6100039) B6100039
theorem B10844513 : Blo 1903435 10844513 := bstep (se 2 (by rfl) ⟨4066692, by rfl⟩ : syracuseStep 10844513 = 8133385) B8133385
theorem B7229675 : Blo 1903435 7229675 := bstep (se 1 (by rfl) ⟨5422256, by rfl⟩ : syracuseStep 7229675 = 10844513) B10844513
theorem B4819783 : Blo 1903435 4819783 := bstep (se 1 (by rfl) ⟨3614837, by rfl⟩ : syracuseStep 4819783 = 7229675) B7229675
theorem B6426377 : Blo 1903435 6426377 := bstep (se 2 (by rfl) ⟨2409891, by rfl⟩ : syracuseStep 6426377 = 4819783) B4819783
theorem B4284251 : Blo 1903435 4284251 := bstep (se 1 (by rfl) ⟨3213188, by rfl⟩ : syracuseStep 4284251 = 6426377) B6426377
theorem B2856167 : Blo 1903435 2856167 := bstep (se 1 (by rfl) ⟨2142125, by rfl⟩ : syracuseStep 2856167 = 4284251) B4284251
theorem B1904111 : Blo 1903435 1904111 := bstep (se 1 (by rfl) ⟨1428083, by rfl⟩ : syracuseStep 1904111 = 2856167) B2856167
theorem B2856173 : Blo 1903435 2856173 := bbase (se 3 (by rfl) ⟨535532, by rfl⟩ : syracuseStep 2856173 = 1071065) (by norm_num)
theorem B1904115 : Blo 1903435 1904115 := bstep (se 1 (by rfl) ⟨1428086, by rfl⟩ : syracuseStep 1904115 = 2856173) B2856173
theorem B4284269 : Blo 1903435 4284269 := bbase (se 3 (by rfl) ⟨803300, by rfl⟩ : syracuseStep 4284269 = 1606601) (by norm_num)
theorem B2856179 : Blo 1903435 2856179 := bstep (se 1 (by rfl) ⟨2142134, by rfl⟩ : syracuseStep 2856179 = 4284269) B4284269
theorem B1904119 : Blo 1903435 1904119 := bstep (se 1 (by rfl) ⟨1428089, by rfl⟩ : syracuseStep 1904119 = 2856179) B2856179
theorem B3614861 : Blo 1903435 3614861 := bbase (se 3 (by rfl) ⟨677786, by rfl⟩ : syracuseStep 3614861 = 1355573) (by norm_num)
theorem B2409907 : Blo 1903435 2409907 := bstep (se 1 (by rfl) ⟨1807430, by rfl⟩ : syracuseStep 2409907 = 3614861) B3614861
theorem B3213209 : Blo 1903435 3213209 := bstep (se 2 (by rfl) ⟨1204953, by rfl⟩ : syracuseStep 3213209 = 2409907) B2409907
theorem B2142139 : Blo 1903435 2142139 := bstep (se 1 (by rfl) ⟨1606604, by rfl⟩ : syracuseStep 2142139 = 3213209) B3213209
theorem B2856185 : Blo 1903435 2856185 := bstep (se 2 (by rfl) ⟨1071069, by rfl⟩ : syracuseStep 2856185 = 2142139) B2142139
theorem B1904123 : Blo 1903435 1904123 := bstep (se 1 (by rfl) ⟨1428092, by rfl⟩ : syracuseStep 1904123 = 2856185) B2856185
theorem B1983133 : Blo 1903435 1983133 := bbase (se 3 (by rfl) ⟨371837, by rfl⟩ : syracuseStep 1983133 = 743675) (by norm_num)
theorem B2644177 : Blo 1903435 2644177 := bstep (se 2 (by rfl) ⟨991566, by rfl⟩ : syracuseStep 2644177 = 1983133) B1983133
theorem B3525569 : Blo 1903435 3525569 := bstep (se 2 (by rfl) ⟨1322088, by rfl⟩ : syracuseStep 3525569 = 2644177) B2644177
theorem B37606069 : Blo 1903435 37606069 := bstep (se 5 (by rfl) ⟨1762784, by rfl⟩ : syracuseStep 37606069 = 3525569) B3525569
theorem B50141425 : Blo 1903435 50141425 := bstep (se 2 (by rfl) ⟨18803034, by rfl⟩ : syracuseStep 50141425 = 37606069) B37606069
theorem B66855233 : Blo 1903435 66855233 := bstep (se 2 (by rfl) ⟨25070712, by rfl⟩ : syracuseStep 66855233 = 50141425) B50141425
theorem B44570155 : Blo 1903435 44570155 := bstep (se 1 (by rfl) ⟨33427616, by rfl⟩ : syracuseStep 44570155 = 66855233) B66855233
theorem B59426873 : Blo 1903435 59426873 := bstep (se 2 (by rfl) ⟨22285077, by rfl⟩ : syracuseStep 59426873 = 44570155) B44570155
theorem B39617915 : Blo 1903435 39617915 := bstep (se 1 (by rfl) ⟨29713436, by rfl⟩ : syracuseStep 39617915 = 59426873) B59426873
theorem B422591093 : Blo 1903435 422591093 := bstep (se 5 (by rfl) ⟨19808957, by rfl⟩ : syracuseStep 422591093 = 39617915) B39617915
theorem B281727395 : Blo 1903435 281727395 := bstep (se 1 (by rfl) ⟨211295546, by rfl⟩ : syracuseStep 281727395 = 422591093) B422591093
theorem B187818263 : Blo 1903435 187818263 := bstep (se 1 (by rfl) ⟨140863697, by rfl⟩ : syracuseStep 187818263 = 281727395) B281727395
theorem B125212175 : Blo 1903435 125212175 := bstep (se 1 (by rfl) ⟨93909131, by rfl⟩ : syracuseStep 125212175 = 187818263) B187818263
theorem B83474783 : Blo 1903435 83474783 := bstep (se 1 (by rfl) ⟨62606087, by rfl⟩ : syracuseStep 83474783 = 125212175) B125212175
theorem B55649855 : Blo 1903435 55649855 := bstep (se 1 (by rfl) ⟨41737391, by rfl⟩ : syracuseStep 55649855 = 83474783) B83474783
theorem B37099903 : Blo 1903435 37099903 := bstep (se 1 (by rfl) ⟨27824927, by rfl⟩ : syracuseStep 37099903 = 55649855) B55649855
theorem B49466537 : Blo 1903435 49466537 := bstep (se 2 (by rfl) ⟨18549951, by rfl⟩ : syracuseStep 49466537 = 37099903) B37099903
theorem B32977691 : Blo 1903435 32977691 := bstep (se 1 (by rfl) ⟨24733268, by rfl⟩ : syracuseStep 32977691 = 49466537) B49466537
theorem B21985127 : Blo 1903435 21985127 := bstep (se 1 (by rfl) ⟨16488845, by rfl⟩ : syracuseStep 21985127 = 32977691) B32977691
theorem B14656751 : Blo 1903435 14656751 := bstep (se 1 (by rfl) ⟨10992563, by rfl⟩ : syracuseStep 14656751 = 21985127) B21985127
theorem B9771167 : Blo 1903435 9771167 := bstep (se 1 (by rfl) ⟨7328375, by rfl⟩ : syracuseStep 9771167 = 14656751) B14656751
theorem B6514111 : Blo 1903435 6514111 := bstep (se 1 (by rfl) ⟨4885583, by rfl⟩ : syracuseStep 6514111 = 9771167) B9771167
theorem B8685481 : Blo 1903435 8685481 := bstep (se 2 (by rfl) ⟨3257055, by rfl⟩ : syracuseStep 8685481 = 6514111) B6514111
theorem B11580641 : Blo 1903435 11580641 := bstep (se 2 (by rfl) ⟨4342740, by rfl⟩ : syracuseStep 11580641 = 8685481) B8685481
theorem B7720427 : Blo 1903435 7720427 := bstep (se 1 (by rfl) ⟨5790320, by rfl⟩ : syracuseStep 7720427 = 11580641) B11580641
theorem B5146951 : Blo 1903435 5146951 := bstep (se 1 (by rfl) ⟨3860213, by rfl⟩ : syracuseStep 5146951 = 7720427) B7720427
theorem B6862601 : Blo 1903435 6862601 := bstep (se 2 (by rfl) ⟨2573475, by rfl⟩ : syracuseStep 6862601 = 5146951) B5146951
theorem B18300269 : Blo 1903435 18300269 := bstep (se 3 (by rfl) ⟨3431300, by rfl⟩ : syracuseStep 18300269 = 6862601) B6862601
theorem B48800717 : Blo 1903435 48800717 := bstep (se 3 (by rfl) ⟨9150134, by rfl⟩ : syracuseStep 48800717 = 18300269) B18300269
theorem B32533811 : Blo 1903435 32533811 := bstep (se 1 (by rfl) ⟨24400358, by rfl⟩ : syracuseStep 32533811 = 48800717) B48800717
theorem B21689207 : Blo 1903435 21689207 := bstep (se 1 (by rfl) ⟨16266905, by rfl⟩ : syracuseStep 21689207 = 32533811) B32533811
theorem B14459471 : Blo 1903435 14459471 := bstep (se 1 (by rfl) ⟨10844603, by rfl⟩ : syracuseStep 14459471 = 21689207) B21689207
theorem B9639647 : Blo 1903435 9639647 := bstep (se 1 (by rfl) ⟨7229735, by rfl⟩ : syracuseStep 9639647 = 14459471) B14459471
theorem B6426431 : Blo 1903435 6426431 := bstep (se 1 (by rfl) ⟨4819823, by rfl⟩ : syracuseStep 6426431 = 9639647) B9639647
theorem B4284287 : Blo 1903435 4284287 := bstep (se 1 (by rfl) ⟨3213215, by rfl⟩ : syracuseStep 4284287 = 6426431) B6426431
theorem B2856191 : Blo 1903435 2856191 := bstep (se 1 (by rfl) ⟨2142143, by rfl⟩ : syracuseStep 2856191 = 4284287) B4284287
theorem B1904127 : Blo 1903435 1904127 := bstep (se 1 (by rfl) ⟨1428095, by rfl⟩ : syracuseStep 1904127 = 2856191) B2856191
theorem B2856197 : Blo 1903435 2856197 := bbase (se 4 (by rfl) ⟨267768, by rfl⟩ : syracuseStep 2856197 = 535537) (by norm_num)
theorem B1904131 : Blo 1903435 1904131 := bstep (se 1 (by rfl) ⟨1428098, by rfl⟩ : syracuseStep 1904131 = 2856197) B2856197
theorem B3213229 : Blo 1903435 3213229 := bbase (se 3 (by rfl) ⟨602480, by rfl⟩ : syracuseStep 3213229 = 1204961) (by norm_num)
theorem B4284305 : Blo 1903435 4284305 := bstep (se 2 (by rfl) ⟨1606614, by rfl⟩ : syracuseStep 4284305 = 3213229) B3213229
theorem B2856203 : Blo 1903435 2856203 := bstep (se 1 (by rfl) ⟨2142152, by rfl⟩ : syracuseStep 2856203 = 4284305) B4284305
theorem B1904135 : Blo 1903435 1904135 := bstep (se 1 (by rfl) ⟨1428101, by rfl⟩ : syracuseStep 1904135 = 2856203) B2856203
theorem B2142157 : Blo 1903435 2142157 := bbase (se 3 (by rfl) ⟨401654, by rfl⟩ : syracuseStep 2142157 = 803309) (by norm_num)
theorem B2856209 : Blo 1903435 2856209 := bstep (se 2 (by rfl) ⟨1071078, by rfl⟩ : syracuseStep 2856209 = 2142157) B2142157
theorem B1904139 : Blo 1903435 1904139 := bstep (se 1 (by rfl) ⟨1428104, by rfl⟩ : syracuseStep 1904139 = 2856209) B2856209
theorem B6426485 : Blo 1903435 6426485 := bbase (se 5 (by rfl) ⟨301241, by rfl⟩ : syracuseStep 6426485 = 602483) (by norm_num)
theorem B4284323 : Blo 1903435 4284323 := bstep (se 1 (by rfl) ⟨3213242, by rfl⟩ : syracuseStep 4284323 = 6426485) B6426485
theorem B2856215 : Blo 1903435 2856215 := bstep (se 1 (by rfl) ⟨2142161, by rfl⟩ : syracuseStep 2856215 = 4284323) B4284323
theorem B1904143 : Blo 1903435 1904143 := bstep (se 1 (by rfl) ⟨1428107, by rfl⟩ : syracuseStep 1904143 = 2856215) B2856215
theorem B2856221 : Blo 1903435 2856221 := bbase (se 3 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 2856221 = 1071083) (by norm_num)
theorem B1904147 : Blo 1903435 1904147 := bstep (se 1 (by rfl) ⟨1428110, by rfl⟩ : syracuseStep 1904147 = 2856221) B2856221
theorem B4284341 : Blo 1903435 4284341 := bbase (se 5 (by rfl) ⟨200828, by rfl⟩ : syracuseStep 4284341 = 401657) (by norm_num)
theorem B2856227 : Blo 1903435 2856227 := bstep (se 1 (by rfl) ⟨2142170, by rfl⟩ : syracuseStep 2856227 = 4284341) B4284341
theorem B1904151 : Blo 1903435 1904151 := bstep (se 1 (by rfl) ⟨1428113, by rfl⟩ : syracuseStep 1904151 = 2856227) B2856227
theorem B6100181 : Blo 1903435 6100181 := bbase (se 7 (by rfl) ⟨71486, by rfl⟩ : syracuseStep 6100181 = 142973) (by norm_num)
theorem B4066787 : Blo 1903435 4066787 := bstep (se 1 (by rfl) ⟨3050090, by rfl⟩ : syracuseStep 4066787 = 6100181) B6100181
theorem B10844765 : Blo 1903435 10844765 := bstep (se 3 (by rfl) ⟨2033393, by rfl⟩ : syracuseStep 10844765 = 4066787) B4066787
theorem B7229843 : Blo 1903435 7229843 := bstep (se 1 (by rfl) ⟨5422382, by rfl⟩ : syracuseStep 7229843 = 10844765) B10844765
theorem B4819895 : Blo 1903435 4819895 := bstep (se 1 (by rfl) ⟨3614921, by rfl⟩ : syracuseStep 4819895 = 7229843) B7229843
theorem B3213263 : Blo 1903435 3213263 := bstep (se 1 (by rfl) ⟨2409947, by rfl⟩ : syracuseStep 3213263 = 4819895) B4819895
theorem B2142175 : Blo 1903435 2142175 := bstep (se 1 (by rfl) ⟨1606631, by rfl⟩ : syracuseStep 2142175 = 3213263) B3213263
theorem B2856233 : Blo 1903435 2856233 := bstep (se 2 (by rfl) ⟨1071087, by rfl⟩ : syracuseStep 2856233 = 2142175) B2142175
theorem B1904155 : Blo 1903435 1904155 := bstep (se 1 (by rfl) ⟨1428116, by rfl⟩ : syracuseStep 1904155 = 2856233) B2856233
theorem B12535573 : Blo 1903435 12535573 := bbase (se 6 (by rfl) ⟨293802, by rfl⟩ : syracuseStep 12535573 = 587605) (by norm_num)
theorem B16714097 : Blo 1903435 16714097 := bstep (se 2 (by rfl) ⟨6267786, by rfl⟩ : syracuseStep 16714097 = 12535573) B12535573
theorem B11142731 : Blo 1903435 11142731 := bstep (se 1 (by rfl) ⟨8357048, by rfl⟩ : syracuseStep 11142731 = 16714097) B16714097
theorem B29713949 : Blo 1903435 29713949 := bstep (se 3 (by rfl) ⟨5571365, by rfl⟩ : syracuseStep 29713949 = 11142731) B11142731
theorem B19809299 : Blo 1903435 19809299 := bstep (se 1 (by rfl) ⟨14856974, by rfl⟩ : syracuseStep 19809299 = 29713949) B29713949
theorem B52824797 : Blo 1903435 52824797 := bstep (se 3 (by rfl) ⟨9904649, by rfl⟩ : syracuseStep 52824797 = 19809299) B19809299
theorem B35216531 : Blo 1903435 35216531 := bstep (se 1 (by rfl) ⟨26412398, by rfl⟩ : syracuseStep 35216531 = 52824797) B52824797
theorem B23477687 : Blo 1903435 23477687 := bstep (se 1 (by rfl) ⟨17608265, by rfl⟩ : syracuseStep 23477687 = 35216531) B35216531
theorem B15651791 : Blo 1903435 15651791 := bstep (se 1 (by rfl) ⟨11738843, by rfl⟩ : syracuseStep 15651791 = 23477687) B23477687
theorem B10434527 : Blo 1903435 10434527 := bstep (se 1 (by rfl) ⟨7825895, by rfl⟩ : syracuseStep 10434527 = 15651791) B15651791
theorem B6956351 : Blo 1903435 6956351 := bstep (se 1 (by rfl) ⟨5217263, by rfl⟩ : syracuseStep 6956351 = 10434527) B10434527
theorem B4637567 : Blo 1903435 4637567 := bstep (se 1 (by rfl) ⟨3478175, by rfl⟩ : syracuseStep 4637567 = 6956351) B6956351
theorem B12366845 : Blo 1903435 12366845 := bstep (se 3 (by rfl) ⟨2318783, by rfl⟩ : syracuseStep 12366845 = 4637567) B4637567
theorem B8244563 : Blo 1903435 8244563 := bstep (se 1 (by rfl) ⟨6183422, by rfl⟩ : syracuseStep 8244563 = 12366845) B12366845
theorem B21985501 : Blo 1903435 21985501 := bstep (se 3 (by rfl) ⟨4122281, by rfl⟩ : syracuseStep 21985501 = 8244563) B8244563
theorem B29314001 : Blo 1903435 29314001 := bstep (se 2 (by rfl) ⟨10992750, by rfl⟩ : syracuseStep 29314001 = 21985501) B21985501
theorem B19542667 : Blo 1903435 19542667 := bstep (se 1 (by rfl) ⟨14657000, by rfl⟩ : syracuseStep 19542667 = 29314001) B29314001
theorem B26056889 : Blo 1903435 26056889 := bstep (se 2 (by rfl) ⟨9771333, by rfl⟩ : syracuseStep 26056889 = 19542667) B19542667
theorem B17371259 : Blo 1903435 17371259 := bstep (se 1 (by rfl) ⟨13028444, by rfl⟩ : syracuseStep 17371259 = 26056889) B26056889
theorem B11580839 : Blo 1903435 11580839 := bstep (se 1 (by rfl) ⟨8685629, by rfl⟩ : syracuseStep 11580839 = 17371259) B17371259
theorem B7720559 : Blo 1903435 7720559 := bstep (se 1 (by rfl) ⟨5790419, by rfl⟩ : syracuseStep 7720559 = 11580839) B11580839
theorem B5147039 : Blo 1903435 5147039 := bstep (se 1 (by rfl) ⟨3860279, by rfl⟩ : syracuseStep 5147039 = 7720559) B7720559
theorem B3431359 : Blo 1903435 3431359 := bstep (se 1 (by rfl) ⟨2573519, by rfl⟩ : syracuseStep 3431359 = 5147039) B5147039
theorem B4575145 : Blo 1903435 4575145 := bstep (se 2 (by rfl) ⟨1715679, by rfl⟩ : syracuseStep 4575145 = 3431359) B3431359
theorem B6100193 : Blo 1903435 6100193 := bstep (se 2 (by rfl) ⟨2287572, by rfl⟩ : syracuseStep 6100193 = 4575145) B4575145
theorem B4066795 : Blo 1903435 4066795 := bstep (se 1 (by rfl) ⟨3050096, by rfl⟩ : syracuseStep 4066795 = 6100193) B6100193
theorem B5422393 : Blo 1903435 5422393 := bstep (se 2 (by rfl) ⟨2033397, by rfl⟩ : syracuseStep 5422393 = 4066795) B4066795
theorem B7229857 : Blo 1903435 7229857 := bstep (se 2 (by rfl) ⟨2711196, by rfl⟩ : syracuseStep 7229857 = 5422393) B5422393
theorem B9639809 : Blo 1903435 9639809 := bstep (se 2 (by rfl) ⟨3614928, by rfl⟩ : syracuseStep 9639809 = 7229857) B7229857
theorem B6426539 : Blo 1903435 6426539 := bstep (se 1 (by rfl) ⟨4819904, by rfl⟩ : syracuseStep 6426539 = 9639809) B9639809
theorem B4284359 : Blo 1903435 4284359 := bstep (se 1 (by rfl) ⟨3213269, by rfl⟩ : syracuseStep 4284359 = 6426539) B6426539
theorem B2856239 : Blo 1903435 2856239 := bstep (se 1 (by rfl) ⟨2142179, by rfl⟩ : syracuseStep 2856239 = 4284359) B4284359
theorem B1904159 : Blo 1903435 1904159 := bstep (se 1 (by rfl) ⟨1428119, by rfl⟩ : syracuseStep 1904159 = 2856239) B2856239
theorem B2856245 : Blo 1903435 2856245 := bbase (se 5 (by rfl) ⟨133886, by rfl⟩ : syracuseStep 2856245 = 267773) (by norm_num)
theorem B1904163 : Blo 1903435 1904163 := bstep (se 1 (by rfl) ⟨1428122, by rfl⟩ : syracuseStep 1904163 = 2856245) B2856245
theorem B4819925 : Blo 1903435 4819925 := bbase (se 7 (by rfl) ⟨56483, by rfl⟩ : syracuseStep 4819925 = 112967) (by norm_num)
theorem B3213283 : Blo 1903435 3213283 := bstep (se 1 (by rfl) ⟨2409962, by rfl⟩ : syracuseStep 3213283 = 4819925) B4819925
theorem B4284377 : Blo 1903435 4284377 := bstep (se 2 (by rfl) ⟨1606641, by rfl⟩ : syracuseStep 4284377 = 3213283) B3213283
theorem B2856251 : Blo 1903435 2856251 := bstep (se 1 (by rfl) ⟨2142188, by rfl⟩ : syracuseStep 2856251 = 4284377) B4284377
theorem B1904167 : Blo 1903435 1904167 := bstep (se 1 (by rfl) ⟨1428125, by rfl⟩ : syracuseStep 1904167 = 2856251) B2856251
theorem B2142193 : Blo 1903435 2142193 := bbase (se 2 (by rfl) ⟨803322, by rfl⟩ : syracuseStep 2142193 = 1606645) (by norm_num)
theorem B2856257 : Blo 1903435 2856257 := bstep (se 2 (by rfl) ⟨1071096, by rfl⟩ : syracuseStep 2856257 = 2142193) B2142193
theorem B1904171 : Blo 1903435 1904171 := bstep (se 1 (by rfl) ⟨1428128, by rfl⟩ : syracuseStep 1904171 = 2856257) B2856257
theorem B4637605 : Blo 1903435 4637605 := bbase (se 4 (by rfl) ⟨434775, by rfl⟩ : syracuseStep 4637605 = 869551) (by norm_num)
theorem B6183473 : Blo 1903435 6183473 := bstep (se 2 (by rfl) ⟨2318802, by rfl⟩ : syracuseStep 6183473 = 4637605) B4637605
theorem B16489261 : Blo 1903435 16489261 := bstep (se 3 (by rfl) ⟨3091736, by rfl⟩ : syracuseStep 16489261 = 6183473) B6183473
theorem B21985681 : Blo 1903435 21985681 := bstep (se 2 (by rfl) ⟨8244630, by rfl⟩ : syracuseStep 21985681 = 16489261) B16489261
theorem B29314241 : Blo 1903435 29314241 := bstep (se 2 (by rfl) ⟨10992840, by rfl⟩ : syracuseStep 29314241 = 21985681) B21985681
theorem B19542827 : Blo 1903435 19542827 := bstep (se 1 (by rfl) ⟨14657120, by rfl⟩ : syracuseStep 19542827 = 29314241) B29314241
theorem B52114205 : Blo 1903435 52114205 := bstep (se 3 (by rfl) ⟨9771413, by rfl⟩ : syracuseStep 52114205 = 19542827) B19542827
theorem B34742803 : Blo 1903435 34742803 := bstep (se 1 (by rfl) ⟨26057102, by rfl⟩ : syracuseStep 34742803 = 52114205) B52114205
theorem B46323737 : Blo 1903435 46323737 := bstep (se 2 (by rfl) ⟨17371401, by rfl⟩ : syracuseStep 46323737 = 34742803) B34742803
theorem B30882491 : Blo 1903435 30882491 := bstep (se 1 (by rfl) ⟨23161868, by rfl⟩ : syracuseStep 30882491 = 46323737) B46323737
theorem B20588327 : Blo 1903435 20588327 := bstep (se 1 (by rfl) ⟨15441245, by rfl⟩ : syracuseStep 20588327 = 30882491) B30882491
theorem B13725551 : Blo 1903435 13725551 := bstep (se 1 (by rfl) ⟨10294163, by rfl⟩ : syracuseStep 13725551 = 20588327) B20588327
theorem B9150367 : Blo 1903435 9150367 := bstep (se 1 (by rfl) ⟨6862775, by rfl⟩ : syracuseStep 9150367 = 13725551) B13725551
theorem B12200489 : Blo 1903435 12200489 := bstep (se 2 (by rfl) ⟨4575183, by rfl⟩ : syracuseStep 12200489 = 9150367) B9150367
theorem B8133659 : Blo 1903435 8133659 := bstep (se 1 (by rfl) ⟨6100244, by rfl⟩ : syracuseStep 8133659 = 12200489) B12200489
theorem B5422439 : Blo 1903435 5422439 := bstep (se 1 (by rfl) ⟨4066829, by rfl⟩ : syracuseStep 5422439 = 8133659) B8133659
theorem B3614959 : Blo 1903435 3614959 := bstep (se 1 (by rfl) ⟨2711219, by rfl⟩ : syracuseStep 3614959 = 5422439) B5422439
theorem B4819945 : Blo 1903435 4819945 := bstep (se 2 (by rfl) ⟨1807479, by rfl⟩ : syracuseStep 4819945 = 3614959) B3614959
theorem B6426593 : Blo 1903435 6426593 := bstep (se 2 (by rfl) ⟨2409972, by rfl⟩ : syracuseStep 6426593 = 4819945) B4819945
theorem B4284395 : Blo 1903435 4284395 := bstep (se 1 (by rfl) ⟨3213296, by rfl⟩ : syracuseStep 4284395 = 6426593) B6426593
theorem B2856263 : Blo 1903435 2856263 := bstep (se 1 (by rfl) ⟨2142197, by rfl⟩ : syracuseStep 2856263 = 4284395) B4284395
theorem B1904175 : Blo 1903435 1904175 := bstep (se 1 (by rfl) ⟨1428131, by rfl⟩ : syracuseStep 1904175 = 2856263) B2856263
theorem B2856269 : Blo 1903435 2856269 := bbase (se 3 (by rfl) ⟨535550, by rfl⟩ : syracuseStep 2856269 = 1071101) (by norm_num)
theorem B1904179 : Blo 1903435 1904179 := bstep (se 1 (by rfl) ⟨1428134, by rfl⟩ : syracuseStep 1904179 = 2856269) B2856269
theorem B4284413 : Blo 1903435 4284413 := bbase (se 3 (by rfl) ⟨803327, by rfl⟩ : syracuseStep 4284413 = 1606655) (by norm_num)
theorem B2856275 : Blo 1903435 2856275 := bstep (se 1 (by rfl) ⟨2142206, by rfl⟩ : syracuseStep 2856275 = 4284413) B4284413
theorem B1904183 : Blo 1903435 1904183 := bstep (se 1 (by rfl) ⟨1428137, by rfl⟩ : syracuseStep 1904183 = 2856275) B2856275
theorem B3213317 : Blo 1903435 3213317 := bbase (se 4 (by rfl) ⟨301248, by rfl⟩ : syracuseStep 3213317 = 602497) (by norm_num)
theorem B2142211 : Blo 1903435 2142211 := bstep (se 1 (by rfl) ⟨1606658, by rfl⟩ : syracuseStep 2142211 = 3213317) B3213317
theorem B2856281 : Blo 1903435 2856281 := bstep (se 2 (by rfl) ⟨1071105, by rfl⟩ : syracuseStep 2856281 = 2142211) B2142211
theorem B1904187 : Blo 1903435 1904187 := bstep (se 1 (by rfl) ⟨1428140, by rfl⟩ : syracuseStep 1904187 = 2856281) B2856281
theorem B14459957 : Blo 1903435 14459957 := bbase (se 5 (by rfl) ⟨677810, by rfl⟩ : syracuseStep 14459957 = 1355621) (by norm_num)
theorem B9639971 : Blo 1903435 9639971 := bstep (se 1 (by rfl) ⟨7229978, by rfl⟩ : syracuseStep 9639971 = 14459957) B14459957
theorem B6426647 : Blo 1903435 6426647 := bstep (se 1 (by rfl) ⟨4819985, by rfl⟩ : syracuseStep 6426647 = 9639971) B9639971
theorem B4284431 : Blo 1903435 4284431 := bstep (se 1 (by rfl) ⟨3213323, by rfl⟩ : syracuseStep 4284431 = 6426647) B6426647
theorem B2856287 : Blo 1903435 2856287 := bstep (se 1 (by rfl) ⟨2142215, by rfl⟩ : syracuseStep 2856287 = 4284431) B4284431
theorem B1904191 : Blo 1903435 1904191 := bstep (se 1 (by rfl) ⟨1428143, by rfl⟩ : syracuseStep 1904191 = 2856287) B2856287
theorem B2856293 : Blo 1903435 2856293 := bbase (se 4 (by rfl) ⟨267777, by rfl⟩ : syracuseStep 2856293 = 535555) (by norm_num)
theorem B1904195 : Blo 1903435 1904195 := bstep (se 1 (by rfl) ⟨1428146, by rfl⟩ : syracuseStep 1904195 = 2856293) B2856293
theorem B3615005 : Blo 1903435 3615005 := bbase (se 3 (by rfl) ⟨677813, by rfl⟩ : syracuseStep 3615005 = 1355627) (by norm_num)
theorem B2410003 : Blo 1903435 2410003 := bstep (se 1 (by rfl) ⟨1807502, by rfl⟩ : syracuseStep 2410003 = 3615005) B3615005
theorem B3213337 : Blo 1903435 3213337 := bstep (se 2 (by rfl) ⟨1205001, by rfl⟩ : syracuseStep 3213337 = 2410003) B2410003
theorem B4284449 : Blo 1903435 4284449 := bstep (se 2 (by rfl) ⟨1606668, by rfl⟩ : syracuseStep 4284449 = 3213337) B3213337
theorem B2856299 : Blo 1903435 2856299 := bstep (se 1 (by rfl) ⟨2142224, by rfl⟩ : syracuseStep 2856299 = 4284449) B4284449
theorem B1904199 : Blo 1903435 1904199 := bstep (se 1 (by rfl) ⟨1428149, by rfl⟩ : syracuseStep 1904199 = 2856299) B2856299
theorem B2142229 : Blo 1903435 2142229 := bbase (se 6 (by rfl) ⟨50208, by rfl⟩ : syracuseStep 2142229 = 100417) (by norm_num)
theorem B2856305 : Blo 1903435 2856305 := bstep (se 2 (by rfl) ⟨1071114, by rfl⟩ : syracuseStep 2856305 = 2142229) B2142229
theorem B1904203 : Blo 1903435 1904203 := bstep (se 1 (by rfl) ⟨1428152, by rfl⟩ : syracuseStep 1904203 = 2856305) B2856305
theorem B2410013 : Blo 1903435 2410013 := bbase (se 3 (by rfl) ⟨451877, by rfl⟩ : syracuseStep 2410013 = 903755) (by norm_num)
theorem B6426701 : Blo 1903435 6426701 := bstep (se 3 (by rfl) ⟨1205006, by rfl⟩ : syracuseStep 6426701 = 2410013) B2410013
theorem B4284467 : Blo 1903435 4284467 := bstep (se 1 (by rfl) ⟨3213350, by rfl⟩ : syracuseStep 4284467 = 6426701) B6426701
theorem B2856311 : Blo 1903435 2856311 := bstep (se 1 (by rfl) ⟨2142233, by rfl⟩ : syracuseStep 2856311 = 4284467) B4284467
theorem B1904207 : Blo 1903435 1904207 := bstep (se 1 (by rfl) ⟨1428155, by rfl⟩ : syracuseStep 1904207 = 2856311) B2856311
theorem B2856317 : Blo 1903435 2856317 := bbase (se 3 (by rfl) ⟨535559, by rfl⟩ : syracuseStep 2856317 = 1071119) (by norm_num)
theorem B1904211 : Blo 1903435 1904211 := bstep (se 1 (by rfl) ⟨1428158, by rfl⟩ : syracuseStep 1904211 = 2856317) B2856317
theorem B4284485 : Blo 1903435 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B2856323 : Blo 1903435 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B1904215 : Blo 1903435 1904215 := bstep (se 1 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 1904215 = 2856323) B2856323
theorem B5422565 : Blo 1903435 5422565 := bbase (se 4 (by rfl) ⟨508365, by rfl⟩ : syracuseStep 5422565 = 1016731) (by norm_num)
theorem B3615043 : Blo 1903435 3615043 := bstep (se 1 (by rfl) ⟨2711282, by rfl⟩ : syracuseStep 3615043 = 5422565) B5422565
theorem B4820057 : Blo 1903435 4820057 := bstep (se 2 (by rfl) ⟨1807521, by rfl⟩ : syracuseStep 4820057 = 3615043) B3615043
theorem B3213371 : Blo 1903435 3213371 := bstep (se 1 (by rfl) ⟨2410028, by rfl⟩ : syracuseStep 3213371 = 4820057) B4820057
theorem B2142247 : Blo 1903435 2142247 := bstep (se 1 (by rfl) ⟨1606685, by rfl⟩ : syracuseStep 2142247 = 3213371) B3213371
theorem B2856329 : Blo 1903435 2856329 := bstep (se 2 (by rfl) ⟨1071123, by rfl⟩ : syracuseStep 2856329 = 2142247) B2142247
theorem B1904219 : Blo 1903435 1904219 := bstep (se 1 (by rfl) ⟨1428164, by rfl⟩ : syracuseStep 1904219 = 2856329) B2856329
theorem B9640133 : Blo 1903435 9640133 := bbase (se 4 (by rfl) ⟨903762, by rfl⟩ : syracuseStep 9640133 = 1807525) (by norm_num)
theorem B6426755 : Blo 1903435 6426755 := bstep (se 1 (by rfl) ⟨4820066, by rfl⟩ : syracuseStep 6426755 = 9640133) B9640133
theorem B4284503 : Blo 1903435 4284503 := bstep (se 1 (by rfl) ⟨3213377, by rfl⟩ : syracuseStep 4284503 = 6426755) B6426755
theorem B2856335 : Blo 1903435 2856335 := bstep (se 1 (by rfl) ⟨2142251, by rfl⟩ : syracuseStep 2856335 = 4284503) B4284503
theorem B1904223 : Blo 1903435 1904223 := bstep (se 1 (by rfl) ⟨1428167, by rfl⟩ : syracuseStep 1904223 = 2856335) B2856335
theorem B2856341 : Blo 1903435 2856341 := bbase (se 6 (by rfl) ⟨66945, by rfl⟩ : syracuseStep 2856341 = 133891) (by norm_num)
theorem B1904227 : Blo 1903435 1904227 := bstep (se 1 (by rfl) ⟨1428170, by rfl⟩ : syracuseStep 1904227 = 2856341) B2856341
theorem B4066949 : Blo 1903435 4066949 := bbase (se 4 (by rfl) ⟨381276, by rfl⟩ : syracuseStep 4066949 = 762553) (by norm_num)
theorem B10845197 : Blo 1903435 10845197 := bstep (se 3 (by rfl) ⟨2033474, by rfl⟩ : syracuseStep 10845197 = 4066949) B4066949
theorem B7230131 : Blo 1903435 7230131 := bstep (se 1 (by rfl) ⟨5422598, by rfl⟩ : syracuseStep 7230131 = 10845197) B10845197
theorem B4820087 : Blo 1903435 4820087 := bstep (se 1 (by rfl) ⟨3615065, by rfl⟩ : syracuseStep 4820087 = 7230131) B7230131
theorem B3213391 : Blo 1903435 3213391 := bstep (se 1 (by rfl) ⟨2410043, by rfl⟩ : syracuseStep 3213391 = 4820087) B4820087
theorem B4284521 : Blo 1903435 4284521 := bstep (se 2 (by rfl) ⟨1606695, by rfl⟩ : syracuseStep 4284521 = 3213391) B3213391
theorem B2856347 : Blo 1903435 2856347 := bstep (se 1 (by rfl) ⟨2142260, by rfl⟩ : syracuseStep 2856347 = 4284521) B4284521
theorem B1904231 : Blo 1903435 1904231 := bstep (se 1 (by rfl) ⟨1428173, by rfl⟩ : syracuseStep 1904231 = 2856347) B2856347
theorem B2142265 : Blo 1903435 2142265 := bbase (se 2 (by rfl) ⟨803349, by rfl⟩ : syracuseStep 2142265 = 1606699) (by norm_num)
theorem B2856353 : Blo 1903435 2856353 := bstep (se 2 (by rfl) ⟨1071132, by rfl⟩ : syracuseStep 2856353 = 2142265) B2142265
theorem B1904235 : Blo 1903435 1904235 := bstep (se 1 (by rfl) ⟨1428176, by rfl⟩ : syracuseStep 1904235 = 2856353) B2856353
theorem B2287669 : Blo 1903435 2287669 := bbase (se 5 (by rfl) ⟨107234, by rfl⟩ : syracuseStep 2287669 = 214469) (by norm_num)
theorem B3050225 : Blo 1903435 3050225 := bstep (se 2 (by rfl) ⟨1143834, by rfl⟩ : syracuseStep 3050225 = 2287669) B2287669
theorem B2033483 : Blo 1903435 2033483 := bstep (se 1 (by rfl) ⟨1525112, by rfl⟩ : syracuseStep 2033483 = 3050225) B3050225
theorem B5422621 : Blo 1903435 5422621 := bstep (se 3 (by rfl) ⟨1016741, by rfl⟩ : syracuseStep 5422621 = 2033483) B2033483
theorem B7230161 : Blo 1903435 7230161 := bstep (se 2 (by rfl) ⟨2711310, by rfl⟩ : syracuseStep 7230161 = 5422621) B5422621
theorem B4820107 : Blo 1903435 4820107 := bstep (se 1 (by rfl) ⟨3615080, by rfl⟩ : syracuseStep 4820107 = 7230161) B7230161
theorem B6426809 : Blo 1903435 6426809 := bstep (se 2 (by rfl) ⟨2410053, by rfl⟩ : syracuseStep 6426809 = 4820107) B4820107
theorem B4284539 : Blo 1903435 4284539 := bstep (se 1 (by rfl) ⟨3213404, by rfl⟩ : syracuseStep 4284539 = 6426809) B6426809
theorem B2856359 : Blo 1903435 2856359 := bstep (se 1 (by rfl) ⟨2142269, by rfl⟩ : syracuseStep 2856359 = 4284539) B4284539
theorem B1904239 : Blo 1903435 1904239 := bstep (se 1 (by rfl) ⟨1428179, by rfl⟩ : syracuseStep 1904239 = 2856359) B2856359
theorem B2856365 : Blo 1903435 2856365 := bbase (se 3 (by rfl) ⟨535568, by rfl⟩ : syracuseStep 2856365 = 1071137) (by norm_num)
theorem B1904243 : Blo 1903435 1904243 := bstep (se 1 (by rfl) ⟨1428182, by rfl⟩ : syracuseStep 1904243 = 2856365) B2856365
theorem B4284557 : Blo 1903435 4284557 := bbase (se 3 (by rfl) ⟨803354, by rfl⟩ : syracuseStep 4284557 = 1606709) (by norm_num)
theorem B2856371 : Blo 1903435 2856371 := bstep (se 1 (by rfl) ⟨2142278, by rfl⟩ : syracuseStep 2856371 = 4284557) B4284557
theorem B1904247 : Blo 1903435 1904247 := bstep (se 1 (by rfl) ⟨1428185, by rfl⟩ : syracuseStep 1904247 = 2856371) B2856371
theorem B2410069 : Blo 1903435 2410069 := bbase (se 8 (by rfl) ⟨14121, by rfl⟩ : syracuseStep 2410069 = 28243) (by norm_num)
theorem B3213425 : Blo 1903435 3213425 := bstep (se 2 (by rfl) ⟨1205034, by rfl⟩ : syracuseStep 3213425 = 2410069) B2410069
theorem B2142283 : Blo 1903435 2142283 := bstep (se 1 (by rfl) ⟨1606712, by rfl⟩ : syracuseStep 2142283 = 3213425) B3213425
theorem B2856377 : Blo 1903435 2856377 := bstep (se 2 (by rfl) ⟨1071141, by rfl⟩ : syracuseStep 2856377 = 2142283) B2142283
theorem B1904251 : Blo 1903435 1904251 := bstep (se 1 (by rfl) ⟨1428188, by rfl⟩ : syracuseStep 1904251 = 2856377) B2856377
theorem B5790709 : Blo 1903435 5790709 := bbase (se 5 (by rfl) ⟨271439, by rfl⟩ : syracuseStep 5790709 = 542879) (by norm_num)
theorem B30883781 : Blo 1903435 30883781 := bstep (se 4 (by rfl) ⟨2895354, by rfl⟩ : syracuseStep 30883781 = 5790709) B5790709
theorem B82356749 : Blo 1903435 82356749 := bstep (se 3 (by rfl) ⟨15441890, by rfl⟩ : syracuseStep 82356749 = 30883781) B30883781
theorem B54904499 : Blo 1903435 54904499 := bstep (se 1 (by rfl) ⟨41178374, by rfl⟩ : syracuseStep 54904499 = 82356749) B82356749
theorem B36602999 : Blo 1903435 36602999 := bstep (se 1 (by rfl) ⟨27452249, by rfl⟩ : syracuseStep 36602999 = 54904499) B54904499
theorem B24401999 : Blo 1903435 24401999 := bstep (se 1 (by rfl) ⟨18301499, by rfl⟩ : syracuseStep 24401999 = 36602999) B36602999
theorem B16267999 : Blo 1903435 16267999 := bstep (se 1 (by rfl) ⟨12200999, by rfl⟩ : syracuseStep 16267999 = 24401999) B24401999
theorem B21690665 : Blo 1903435 21690665 := bstep (se 2 (by rfl) ⟨8133999, by rfl⟩ : syracuseStep 21690665 = 16267999) B16267999
theorem B14460443 : Blo 1903435 14460443 := bstep (se 1 (by rfl) ⟨10845332, by rfl⟩ : syracuseStep 14460443 = 21690665) B21690665
theorem B9640295 : Blo 1903435 9640295 := bstep (se 1 (by rfl) ⟨7230221, by rfl⟩ : syracuseStep 9640295 = 14460443) B14460443
theorem B6426863 : Blo 1903435 6426863 := bstep (se 1 (by rfl) ⟨4820147, by rfl⟩ : syracuseStep 6426863 = 9640295) B9640295
theorem B4284575 : Blo 1903435 4284575 := bstep (se 1 (by rfl) ⟨3213431, by rfl⟩ : syracuseStep 4284575 = 6426863) B6426863
theorem B2856383 : Blo 1903435 2856383 := bstep (se 1 (by rfl) ⟨2142287, by rfl⟩ : syracuseStep 2856383 = 4284575) B4284575
theorem B1904255 : Blo 1903435 1904255 := bstep (se 1 (by rfl) ⟨1428191, by rfl⟩ : syracuseStep 1904255 = 2856383) B2856383
theorem B2856389 : Blo 1903435 2856389 := bbase (se 4 (by rfl) ⟨267786, by rfl⟩ : syracuseStep 2856389 = 535573) (by norm_num)
theorem B1904259 : Blo 1903435 1904259 := bstep (se 1 (by rfl) ⟨1428194, by rfl⟩ : syracuseStep 1904259 = 2856389) B2856389
theorem B3213445 : Blo 1903435 3213445 := bbase (se 4 (by rfl) ⟨301260, by rfl⟩ : syracuseStep 3213445 = 602521) (by norm_num)
theorem B4284593 : Blo 1903435 4284593 := bstep (se 2 (by rfl) ⟨1606722, by rfl⟩ : syracuseStep 4284593 = 3213445) B3213445
theorem B2856395 : Blo 1903435 2856395 := bstep (se 1 (by rfl) ⟨2142296, by rfl⟩ : syracuseStep 2856395 = 4284593) B4284593
theorem B1904263 : Blo 1903435 1904263 := bstep (se 1 (by rfl) ⟨1428197, by rfl⟩ : syracuseStep 1904263 = 2856395) B2856395
theorem B2142301 : Blo 1903435 2142301 := bbase (se 3 (by rfl) ⟨401681, by rfl⟩ : syracuseStep 2142301 = 803363) (by norm_num)
theorem B2856401 : Blo 1903435 2856401 := bstep (se 2 (by rfl) ⟨1071150, by rfl⟩ : syracuseStep 2856401 = 2142301) B2142301
theorem B1904267 : Blo 1903435 1904267 := bstep (se 1 (by rfl) ⟨1428200, by rfl⟩ : syracuseStep 1904267 = 2856401) B2856401
theorem B6426917 : Blo 1903435 6426917 := bbase (se 4 (by rfl) ⟨602523, by rfl⟩ : syracuseStep 6426917 = 1205047) (by norm_num)
theorem B4284611 : Blo 1903435 4284611 := bstep (se 1 (by rfl) ⟨3213458, by rfl⟩ : syracuseStep 4284611 = 6426917) B6426917
theorem B2856407 : Blo 1903435 2856407 := bstep (se 1 (by rfl) ⟨2142305, by rfl⟩ : syracuseStep 2856407 = 4284611) B4284611
theorem B1904271 : Blo 1903435 1904271 := bstep (se 1 (by rfl) ⟨1428203, by rfl⟩ : syracuseStep 1904271 = 2856407) B2856407
theorem B2856413 : Blo 1903435 2856413 := bbase (se 3 (by rfl) ⟨535577, by rfl⟩ : syracuseStep 2856413 = 1071155) (by norm_num)
theorem B1904275 : Blo 1903435 1904275 := bstep (se 1 (by rfl) ⟨1428206, by rfl⟩ : syracuseStep 1904275 = 2856413) B2856413
theorem B4284629 : Blo 1903435 4284629 := bbase (se 7 (by rfl) ⟨50210, by rfl⟩ : syracuseStep 4284629 = 100421) (by norm_num)
theorem B2856419 : Blo 1903435 2856419 := bstep (se 1 (by rfl) ⟨2142314, by rfl⟩ : syracuseStep 2856419 = 4284629) B4284629
theorem B1904279 : Blo 1903435 1904279 := bstep (se 1 (by rfl) ⟨1428209, by rfl⟩ : syracuseStep 1904279 = 2856419) B2856419
theorem B5217605 : Blo 1903435 5217605 := bbase (se 4 (by rfl) ⟨489150, by rfl⟩ : syracuseStep 5217605 = 978301) (by norm_num)
theorem B3478403 : Blo 1903435 3478403 := bstep (se 1 (by rfl) ⟨2608802, by rfl⟩ : syracuseStep 3478403 = 5217605) B5217605
theorem B9275741 : Blo 1903435 9275741 := bstep (se 3 (by rfl) ⟨1739201, by rfl⟩ : syracuseStep 9275741 = 3478403) B3478403
theorem B6183827 : Blo 1903435 6183827 := bstep (se 1 (by rfl) ⟨4637870, by rfl⟩ : syracuseStep 6183827 = 9275741) B9275741
theorem B4122551 : Blo 1903435 4122551 := bstep (se 1 (by rfl) ⟨3091913, by rfl⟩ : syracuseStep 4122551 = 6183827) B6183827
theorem B2748367 : Blo 1903435 2748367 := bstep (se 1 (by rfl) ⟨2061275, by rfl⟩ : syracuseStep 2748367 = 4122551) B4122551
theorem B3664489 : Blo 1903435 3664489 := bstep (se 2 (by rfl) ⟨1374183, by rfl⟩ : syracuseStep 3664489 = 2748367) B2748367
theorem B4885985 : Blo 1903435 4885985 := bstep (se 2 (by rfl) ⟨1832244, by rfl⟩ : syracuseStep 4885985 = 3664489) B3664489
theorem B3257323 : Blo 1903435 3257323 := bstep (se 1 (by rfl) ⟨2442992, by rfl⟩ : syracuseStep 3257323 = 4885985) B4885985
theorem B17372389 : Blo 1903435 17372389 := bstep (se 4 (by rfl) ⟨1628661, by rfl⟩ : syracuseStep 17372389 = 3257323) B3257323
theorem B23163185 : Blo 1903435 23163185 := bstep (se 2 (by rfl) ⟨8686194, by rfl⟩ : syracuseStep 23163185 = 17372389) B17372389
theorem B15442123 : Blo 1903435 15442123 := bstep (se 1 (by rfl) ⟨11581592, by rfl⟩ : syracuseStep 15442123 = 23163185) B23163185
theorem B20589497 : Blo 1903435 20589497 := bstep (se 2 (by rfl) ⟨7721061, by rfl⟩ : syracuseStep 20589497 = 15442123) B15442123
theorem B13726331 : Blo 1903435 13726331 := bstep (se 1 (by rfl) ⟨10294748, by rfl⟩ : syracuseStep 13726331 = 20589497) B20589497
theorem B9150887 : Blo 1903435 9150887 := bstep (se 1 (by rfl) ⟨6863165, by rfl⟩ : syracuseStep 9150887 = 13726331) B13726331
theorem B6100591 : Blo 1903435 6100591 := bstep (se 1 (by rfl) ⟨4575443, by rfl⟩ : syracuseStep 6100591 = 9150887) B9150887
theorem B8134121 : Blo 1903435 8134121 := bstep (se 2 (by rfl) ⟨3050295, by rfl⟩ : syracuseStep 8134121 = 6100591) B6100591
theorem B5422747 : Blo 1903435 5422747 := bstep (se 1 (by rfl) ⟨4067060, by rfl⟩ : syracuseStep 5422747 = 8134121) B8134121
theorem B7230329 : Blo 1903435 7230329 := bstep (se 2 (by rfl) ⟨2711373, by rfl⟩ : syracuseStep 7230329 = 5422747) B5422747
theorem B4820219 : Blo 1903435 4820219 := bstep (se 1 (by rfl) ⟨3615164, by rfl⟩ : syracuseStep 4820219 = 7230329) B7230329
theorem B3213479 : Blo 1903435 3213479 := bstep (se 1 (by rfl) ⟨2410109, by rfl⟩ : syracuseStep 3213479 = 4820219) B4820219
theorem B2142319 : Blo 1903435 2142319 := bstep (se 1 (by rfl) ⟨1606739, by rfl⟩ : syracuseStep 2142319 = 3213479) B3213479
theorem B2856425 : Blo 1903435 2856425 := bstep (se 2 (by rfl) ⟨1071159, by rfl⟩ : syracuseStep 2856425 = 2142319) B2142319
theorem B1904283 : Blo 1903435 1904283 := bstep (se 1 (by rfl) ⟨1428212, by rfl⟩ : syracuseStep 1904283 = 2856425) B2856425
theorem B12201205 : Blo 1903435 12201205 := bbase (se 5 (by rfl) ⟨571931, by rfl⟩ : syracuseStep 12201205 = 1143863) (by norm_num)
theorem B16268273 : Blo 1903435 16268273 := bstep (se 2 (by rfl) ⟨6100602, by rfl⟩ : syracuseStep 16268273 = 12201205) B12201205
theorem B10845515 : Blo 1903435 10845515 := bstep (se 1 (by rfl) ⟨8134136, by rfl⟩ : syracuseStep 10845515 = 16268273) B16268273
theorem B7230343 : Blo 1903435 7230343 := bstep (se 1 (by rfl) ⟨5422757, by rfl⟩ : syracuseStep 7230343 = 10845515) B10845515
theorem B9640457 : Blo 1903435 9640457 := bstep (se 2 (by rfl) ⟨3615171, by rfl⟩ : syracuseStep 9640457 = 7230343) B7230343
theorem B6426971 : Blo 1903435 6426971 := bstep (se 1 (by rfl) ⟨4820228, by rfl⟩ : syracuseStep 6426971 = 9640457) B9640457
theorem B4284647 : Blo 1903435 4284647 := bstep (se 1 (by rfl) ⟨3213485, by rfl⟩ : syracuseStep 4284647 = 6426971) B6426971
theorem B2856431 : Blo 1903435 2856431 := bstep (se 1 (by rfl) ⟨2142323, by rfl⟩ : syracuseStep 2856431 = 4284647) B4284647
theorem B1904287 : Blo 1903435 1904287 := bstep (se 1 (by rfl) ⟨1428215, by rfl⟩ : syracuseStep 1904287 = 2856431) B2856431
theorem B2856437 : Blo 1903435 2856437 := bbase (se 5 (by rfl) ⟨133895, by rfl⟩ : syracuseStep 2856437 = 267791) (by norm_num)
theorem B1904291 : Blo 1903435 1904291 := bstep (se 1 (by rfl) ⟨1428218, by rfl⟩ : syracuseStep 1904291 = 2856437) B2856437
theorem B3431605 : Blo 1903435 3431605 := bbase (se 5 (by rfl) ⟨160856, by rfl⟩ : syracuseStep 3431605 = 321713) (by norm_num)
theorem B4575473 : Blo 1903435 4575473 := bstep (se 2 (by rfl) ⟨1715802, by rfl⟩ : syracuseStep 4575473 = 3431605) B3431605
theorem B3050315 : Blo 1903435 3050315 := bstep (se 1 (by rfl) ⟨2287736, by rfl⟩ : syracuseStep 3050315 = 4575473) B4575473
theorem B2033543 : Blo 1903435 2033543 := bstep (se 1 (by rfl) ⟨1525157, by rfl⟩ : syracuseStep 2033543 = 3050315) B3050315
theorem B5422781 : Blo 1903435 5422781 := bstep (se 3 (by rfl) ⟨1016771, by rfl⟩ : syracuseStep 5422781 = 2033543) B2033543
theorem B3615187 : Blo 1903435 3615187 := bstep (se 1 (by rfl) ⟨2711390, by rfl⟩ : syracuseStep 3615187 = 5422781) B5422781
theorem B4820249 : Blo 1903435 4820249 := bstep (se 2 (by rfl) ⟨1807593, by rfl⟩ : syracuseStep 4820249 = 3615187) B3615187
theorem B3213499 : Blo 1903435 3213499 := bstep (se 1 (by rfl) ⟨2410124, by rfl⟩ : syracuseStep 3213499 = 4820249) B4820249
theorem B4284665 : Blo 1903435 4284665 := bstep (se 2 (by rfl) ⟨1606749, by rfl⟩ : syracuseStep 4284665 = 3213499) B3213499
theorem B2856443 : Blo 1903435 2856443 := bstep (se 1 (by rfl) ⟨2142332, by rfl⟩ : syracuseStep 2856443 = 4284665) B4284665
theorem B1904295 : Blo 1903435 1904295 := bstep (se 1 (by rfl) ⟨1428221, by rfl⟩ : syracuseStep 1904295 = 2856443) B2856443
theorem B2142337 : Blo 1903435 2142337 := bbase (se 2 (by rfl) ⟨803376, by rfl⟩ : syracuseStep 2142337 = 1606753) (by norm_num)
theorem B2856449 : Blo 1903435 2856449 := bstep (se 2 (by rfl) ⟨1071168, by rfl⟩ : syracuseStep 2856449 = 2142337) B2142337
theorem B1904299 : Blo 1903435 1904299 := bstep (se 1 (by rfl) ⟨1428224, by rfl⟩ : syracuseStep 1904299 = 2856449) B2856449
theorem B4820269 : Blo 1903435 4820269 := bbase (se 3 (by rfl) ⟨903800, by rfl⟩ : syracuseStep 4820269 = 1807601) (by norm_num)
theorem B6427025 : Blo 1903435 6427025 := bstep (se 2 (by rfl) ⟨2410134, by rfl⟩ : syracuseStep 6427025 = 4820269) B4820269
theorem B4284683 : Blo 1903435 4284683 := bstep (se 1 (by rfl) ⟨3213512, by rfl⟩ : syracuseStep 4284683 = 6427025) B6427025
theorem B2856455 : Blo 1903435 2856455 := bstep (se 1 (by rfl) ⟨2142341, by rfl⟩ : syracuseStep 2856455 = 4284683) B4284683
theorem B1904303 : Blo 1903435 1904303 := bstep (se 1 (by rfl) ⟨1428227, by rfl⟩ : syracuseStep 1904303 = 2856455) B2856455
theorem B2856461 : Blo 1903435 2856461 := bbase (se 3 (by rfl) ⟨535586, by rfl⟩ : syracuseStep 2856461 = 1071173) (by norm_num)
theorem B1904307 : Blo 1903435 1904307 := bstep (se 1 (by rfl) ⟨1428230, by rfl⟩ : syracuseStep 1904307 = 2856461) B2856461
theorem B4284701 : Blo 1903435 4284701 := bbase (se 3 (by rfl) ⟨803381, by rfl⟩ : syracuseStep 4284701 = 1606763) (by norm_num)
theorem B2856467 : Blo 1903435 2856467 := bstep (se 1 (by rfl) ⟨2142350, by rfl⟩ : syracuseStep 2856467 = 4284701) B4284701
theorem B1904311 : Blo 1903435 1904311 := bstep (se 1 (by rfl) ⟨1428233, by rfl⟩ : syracuseStep 1904311 = 2856467) B2856467
theorem B3213533 : Blo 1903435 3213533 := bbase (se 3 (by rfl) ⟨602537, by rfl⟩ : syracuseStep 3213533 = 1205075) (by norm_num)
theorem B2142355 : Blo 1903435 2142355 := bstep (se 1 (by rfl) ⟨1606766, by rfl⟩ : syracuseStep 2142355 = 3213533) B3213533
theorem B2856473 : Blo 1903435 2856473 := bstep (se 2 (by rfl) ⟨1071177, by rfl⟩ : syracuseStep 2856473 = 2142355) B2142355
theorem B1904315 : Blo 1903435 1904315 := bstep (se 1 (by rfl) ⟨1428236, by rfl⟩ : syracuseStep 1904315 = 2856473) B2856473
theorem B4886077 : Blo 1903435 4886077 := bbase (se 3 (by rfl) ⟨916139, by rfl⟩ : syracuseStep 4886077 = 1832279) (by norm_num)
theorem B6514769 : Blo 1903435 6514769 := bstep (se 2 (by rfl) ⟨2443038, by rfl⟩ : syracuseStep 6514769 = 4886077) B4886077
theorem B17372717 : Blo 1903435 17372717 := bstep (se 3 (by rfl) ⟨3257384, by rfl⟩ : syracuseStep 17372717 = 6514769) B6514769
theorem B11581811 : Blo 1903435 11581811 := bstep (se 1 (by rfl) ⟨8686358, by rfl⟩ : syracuseStep 11581811 = 17372717) B17372717
theorem B7721207 : Blo 1903435 7721207 := bstep (se 1 (by rfl) ⟨5790905, by rfl⟩ : syracuseStep 7721207 = 11581811) B11581811
theorem B5147471 : Blo 1903435 5147471 := bstep (se 1 (by rfl) ⟨3860603, by rfl⟩ : syracuseStep 5147471 = 7721207) B7721207
theorem B3431647 : Blo 1903435 3431647 := bstep (se 1 (by rfl) ⟨2573735, by rfl⟩ : syracuseStep 3431647 = 5147471) B5147471
theorem B4575529 : Blo 1903435 4575529 := bstep (se 2 (by rfl) ⟨1715823, by rfl⟩ : syracuseStep 4575529 = 3431647) B3431647
theorem B6100705 : Blo 1903435 6100705 := bstep (se 2 (by rfl) ⟨2287764, by rfl⟩ : syracuseStep 6100705 = 4575529) B4575529
theorem B8134273 : Blo 1903435 8134273 := bstep (se 2 (by rfl) ⟨3050352, by rfl⟩ : syracuseStep 8134273 = 6100705) B6100705
theorem B10845697 : Blo 1903435 10845697 := bstep (se 2 (by rfl) ⟨4067136, by rfl⟩ : syracuseStep 10845697 = 8134273) B8134273
theorem B14460929 : Blo 1903435 14460929 := bstep (se 2 (by rfl) ⟨5422848, by rfl⟩ : syracuseStep 14460929 = 10845697) B10845697
theorem B9640619 : Blo 1903435 9640619 := bstep (se 1 (by rfl) ⟨7230464, by rfl⟩ : syracuseStep 9640619 = 14460929) B14460929
theorem B6427079 : Blo 1903435 6427079 := bstep (se 1 (by rfl) ⟨4820309, by rfl⟩ : syracuseStep 6427079 = 9640619) B9640619
theorem B4284719 : Blo 1903435 4284719 := bstep (se 1 (by rfl) ⟨3213539, by rfl⟩ : syracuseStep 4284719 = 6427079) B6427079
theorem B2856479 : Blo 1903435 2856479 := bstep (se 1 (by rfl) ⟨2142359, by rfl⟩ : syracuseStep 2856479 = 4284719) B4284719
theorem B1904319 : Blo 1903435 1904319 := bstep (se 1 (by rfl) ⟨1428239, by rfl⟩ : syracuseStep 1904319 = 2856479) B2856479
theorem B2856485 : Blo 1903435 2856485 := bbase (se 4 (by rfl) ⟨267795, by rfl⟩ : syracuseStep 2856485 = 535591) (by norm_num)
theorem B1904323 : Blo 1903435 1904323 := bstep (se 1 (by rfl) ⟨1428242, by rfl⟩ : syracuseStep 1904323 = 2856485) B2856485
theorem B2410165 : Blo 1903435 2410165 := bbase (se 5 (by rfl) ⟨112976, by rfl⟩ : syracuseStep 2410165 = 225953) (by norm_num)
theorem B3213553 : Blo 1903435 3213553 := bstep (se 2 (by rfl) ⟨1205082, by rfl⟩ : syracuseStep 3213553 = 2410165) B2410165
theorem B4284737 : Blo 1903435 4284737 := bstep (se 2 (by rfl) ⟨1606776, by rfl⟩ : syracuseStep 4284737 = 3213553) B3213553
theorem B2856491 : Blo 1903435 2856491 := bstep (se 1 (by rfl) ⟨2142368, by rfl⟩ : syracuseStep 2856491 = 4284737) B4284737
theorem B1904327 : Blo 1903435 1904327 := bstep (se 1 (by rfl) ⟨1428245, by rfl⟩ : syracuseStep 1904327 = 2856491) B2856491
theorem B2142373 : Blo 1903435 2142373 := bbase (se 4 (by rfl) ⟨200847, by rfl⟩ : syracuseStep 2142373 = 401695) (by norm_num)
theorem B2856497 : Blo 1903435 2856497 := bstep (se 2 (by rfl) ⟨1071186, by rfl⟩ : syracuseStep 2856497 = 2142373) B2142373
theorem B1904331 : Blo 1903435 1904331 := bstep (se 1 (by rfl) ⟨1428248, by rfl⟩ : syracuseStep 1904331 = 2856497) B2856497
theorem B10295029 : Blo 1903435 10295029 := bbase (se 5 (by rfl) ⟨482579, by rfl⟩ : syracuseStep 10295029 = 965159) (by norm_num)
theorem B13726705 : Blo 1903435 13726705 := bstep (se 2 (by rfl) ⟨5147514, by rfl⟩ : syracuseStep 13726705 = 10295029) B10295029
theorem B18302273 : Blo 1903435 18302273 := bstep (se 2 (by rfl) ⟨6863352, by rfl⟩ : syracuseStep 18302273 = 13726705) B13726705
theorem B12201515 : Blo 1903435 12201515 := bstep (se 1 (by rfl) ⟨9151136, by rfl⟩ : syracuseStep 12201515 = 18302273) B18302273
theorem B8134343 : Blo 1903435 8134343 := bstep (se 1 (by rfl) ⟨6100757, by rfl⟩ : syracuseStep 8134343 = 12201515) B12201515
theorem B5422895 : Blo 1903435 5422895 := bstep (se 1 (by rfl) ⟨4067171, by rfl⟩ : syracuseStep 5422895 = 8134343) B8134343
theorem B3615263 : Blo 1903435 3615263 := bstep (se 1 (by rfl) ⟨2711447, by rfl⟩ : syracuseStep 3615263 = 5422895) B5422895
theorem B2410175 : Blo 1903435 2410175 := bstep (se 1 (by rfl) ⟨1807631, by rfl⟩ : syracuseStep 2410175 = 3615263) B3615263
theorem B6427133 : Blo 1903435 6427133 := bstep (se 3 (by rfl) ⟨1205087, by rfl⟩ : syracuseStep 6427133 = 2410175) B2410175
theorem B4284755 : Blo 1903435 4284755 := bstep (se 1 (by rfl) ⟨3213566, by rfl⟩ : syracuseStep 4284755 = 6427133) B6427133
theorem B2856503 : Blo 1903435 2856503 := bstep (se 1 (by rfl) ⟨2142377, by rfl⟩ : syracuseStep 2856503 = 4284755) B4284755
theorem B1904335 : Blo 1903435 1904335 := bstep (se 1 (by rfl) ⟨1428251, by rfl⟩ : syracuseStep 1904335 = 2856503) B2856503
theorem B2856509 : Blo 1903435 2856509 := bbase (se 3 (by rfl) ⟨535595, by rfl⟩ : syracuseStep 2856509 = 1071191) (by norm_num)
theorem B1904339 : Blo 1903435 1904339 := bstep (se 1 (by rfl) ⟨1428254, by rfl⟩ : syracuseStep 1904339 = 2856509) B2856509
theorem B4284773 : Blo 1903435 4284773 := bbase (se 4 (by rfl) ⟨401697, by rfl⟩ : syracuseStep 4284773 = 803395) (by norm_num)
theorem B2856515 : Blo 1903435 2856515 := bstep (se 1 (by rfl) ⟨2142386, by rfl⟩ : syracuseStep 2856515 = 4284773) B4284773
theorem B1904343 : Blo 1903435 1904343 := bstep (se 1 (by rfl) ⟨1428257, by rfl⟩ : syracuseStep 1904343 = 2856515) B2856515
theorem B4820381 : Blo 1903435 4820381 := bbase (se 3 (by rfl) ⟨903821, by rfl⟩ : syracuseStep 4820381 = 1807643) (by norm_num)
theorem B3213587 : Blo 1903435 3213587 := bstep (se 1 (by rfl) ⟨2410190, by rfl⟩ : syracuseStep 3213587 = 4820381) B4820381
theorem B2142391 : Blo 1903435 2142391 := bstep (se 1 (by rfl) ⟨1606793, by rfl⟩ : syracuseStep 2142391 = 3213587) B3213587
theorem B2856521 : Blo 1903435 2856521 := bstep (se 2 (by rfl) ⟨1071195, by rfl⟩ : syracuseStep 2856521 = 2142391) B2142391
theorem B1904347 : Blo 1903435 1904347 := bstep (se 1 (by rfl) ⟨1428260, by rfl⟩ : syracuseStep 1904347 = 2856521) B2856521
theorem B3615293 : Blo 1903435 3615293 := bbase (se 3 (by rfl) ⟨677867, by rfl⟩ : syracuseStep 3615293 = 1355735) (by norm_num)
theorem B9640781 : Blo 1903435 9640781 := bstep (se 3 (by rfl) ⟨1807646, by rfl⟩ : syracuseStep 9640781 = 3615293) B3615293
theorem B6427187 : Blo 1903435 6427187 := bstep (se 1 (by rfl) ⟨4820390, by rfl⟩ : syracuseStep 6427187 = 9640781) B9640781
theorem B4284791 : Blo 1903435 4284791 := bstep (se 1 (by rfl) ⟨3213593, by rfl⟩ : syracuseStep 4284791 = 6427187) B6427187
theorem B2856527 : Blo 1903435 2856527 := bstep (se 1 (by rfl) ⟨2142395, by rfl⟩ : syracuseStep 2856527 = 4284791) B4284791
theorem B1904351 : Blo 1903435 1904351 := bstep (se 1 (by rfl) ⟨1428263, by rfl⟩ : syracuseStep 1904351 = 2856527) B2856527
theorem B2856533 : Blo 1903435 2856533 := bbase (se 8 (by rfl) ⟨16737, by rfl⟩ : syracuseStep 2856533 = 33475) (by norm_num)
theorem B1904355 : Blo 1903435 1904355 := bstep (se 1 (by rfl) ⟨1428266, by rfl⟩ : syracuseStep 1904355 = 2856533) B2856533
theorem B2287813 : Blo 1903435 2287813 := bbase (se 4 (by rfl) ⟨214482, by rfl⟩ : syracuseStep 2287813 = 428965) (by norm_num)
theorem B3050417 : Blo 1903435 3050417 := bstep (se 2 (by rfl) ⟨1143906, by rfl⟩ : syracuseStep 3050417 = 2287813) B2287813
theorem B8134445 : Blo 1903435 8134445 := bstep (se 3 (by rfl) ⟨1525208, by rfl⟩ : syracuseStep 8134445 = 3050417) B3050417
theorem B5422963 : Blo 1903435 5422963 := bstep (se 1 (by rfl) ⟨4067222, by rfl⟩ : syracuseStep 5422963 = 8134445) B8134445
theorem B7230617 : Blo 1903435 7230617 := bstep (se 2 (by rfl) ⟨2711481, by rfl⟩ : syracuseStep 7230617 = 5422963) B5422963
theorem B4820411 : Blo 1903435 4820411 := bstep (se 1 (by rfl) ⟨3615308, by rfl⟩ : syracuseStep 4820411 = 7230617) B7230617
theorem B3213607 : Blo 1903435 3213607 := bstep (se 1 (by rfl) ⟨2410205, by rfl⟩ : syracuseStep 3213607 = 4820411) B4820411
theorem B4284809 : Blo 1903435 4284809 := bstep (se 2 (by rfl) ⟨1606803, by rfl⟩ : syracuseStep 4284809 = 3213607) B3213607
theorem B2856539 : Blo 1903435 2856539 := bstep (se 1 (by rfl) ⟨2142404, by rfl⟩ : syracuseStep 2856539 = 4284809) B4284809
theorem B1904359 : Blo 1903435 1904359 := bstep (se 1 (by rfl) ⟨1428269, by rfl⟩ : syracuseStep 1904359 = 2856539) B2856539
theorem B2142409 : Blo 1903435 2142409 := bbase (se 2 (by rfl) ⟨803403, by rfl⟩ : syracuseStep 2142409 = 1606807) (by norm_num)
theorem B2856545 : Blo 1903435 2856545 := bstep (se 2 (by rfl) ⟨1071204, by rfl⟩ : syracuseStep 2856545 = 2142409) B2142409
theorem B1904363 : Blo 1903435 1904363 := bstep (se 1 (by rfl) ⟨1428272, by rfl⟩ : syracuseStep 1904363 = 2856545) B2856545
theorem B6514933 : Blo 1903435 6514933 := bbase (se 5 (by rfl) ⟨305387, by rfl⟩ : syracuseStep 6514933 = 610775) (by norm_num)
theorem B8686577 : Blo 1903435 8686577 := bstep (se 2 (by rfl) ⟨3257466, by rfl⟩ : syracuseStep 8686577 = 6514933) B6514933
theorem B5791051 : Blo 1903435 5791051 := bstep (se 1 (by rfl) ⟨4343288, by rfl⟩ : syracuseStep 5791051 = 8686577) B8686577
theorem B7721401 : Blo 1903435 7721401 := bstep (se 2 (by rfl) ⟨2895525, by rfl⟩ : syracuseStep 7721401 = 5791051) B5791051
theorem B10295201 : Blo 1903435 10295201 := bstep (se 2 (by rfl) ⟨3860700, by rfl⟩ : syracuseStep 10295201 = 7721401) B7721401
theorem B6863467 : Blo 1903435 6863467 := bstep (se 1 (by rfl) ⟨5147600, by rfl⟩ : syracuseStep 6863467 = 10295201) B10295201
theorem B9151289 : Blo 1903435 9151289 := bstep (se 2 (by rfl) ⟨3431733, by rfl⟩ : syracuseStep 9151289 = 6863467) B6863467
theorem B6100859 : Blo 1903435 6100859 := bstep (se 1 (by rfl) ⟨4575644, by rfl⟩ : syracuseStep 6100859 = 9151289) B9151289
theorem B16268957 : Blo 1903435 16268957 := bstep (se 3 (by rfl) ⟨3050429, by rfl⟩ : syracuseStep 16268957 = 6100859) B6100859
theorem B10845971 : Blo 1903435 10845971 := bstep (se 1 (by rfl) ⟨8134478, by rfl⟩ : syracuseStep 10845971 = 16268957) B16268957
theorem B7230647 : Blo 1903435 7230647 := bstep (se 1 (by rfl) ⟨5422985, by rfl⟩ : syracuseStep 7230647 = 10845971) B10845971
theorem B4820431 : Blo 1903435 4820431 := bstep (se 1 (by rfl) ⟨3615323, by rfl⟩ : syracuseStep 4820431 = 7230647) B7230647
theorem B6427241 : Blo 1903435 6427241 := bstep (se 2 (by rfl) ⟨2410215, by rfl⟩ : syracuseStep 6427241 = 4820431) B4820431
theorem B4284827 : Blo 1903435 4284827 := bstep (se 1 (by rfl) ⟨3213620, by rfl⟩ : syracuseStep 4284827 = 6427241) B6427241
theorem B2856551 : Blo 1903435 2856551 := bstep (se 1 (by rfl) ⟨2142413, by rfl⟩ : syracuseStep 2856551 = 4284827) B4284827
theorem B1904367 : Blo 1903435 1904367 := bstep (se 1 (by rfl) ⟨1428275, by rfl⟩ : syracuseStep 1904367 = 2856551) B2856551
theorem B2856557 : Blo 1903435 2856557 := bbase (se 3 (by rfl) ⟨535604, by rfl⟩ : syracuseStep 2856557 = 1071209) (by norm_num)
theorem B1904371 : Blo 1903435 1904371 := bstep (se 1 (by rfl) ⟨1428278, by rfl⟩ : syracuseStep 1904371 = 2856557) B2856557
theorem B4284845 : Blo 1903435 4284845 := bbase (se 3 (by rfl) ⟨803408, by rfl⟩ : syracuseStep 4284845 = 1606817) (by norm_num)
theorem B2856563 : Blo 1903435 2856563 := bstep (se 1 (by rfl) ⟨2142422, by rfl⟩ : syracuseStep 2856563 = 4284845) B4284845
theorem B1904375 : Blo 1903435 1904375 := bstep (se 1 (by rfl) ⟨1428281, by rfl⟩ : syracuseStep 1904375 = 2856563) B2856563
theorem B2033633 : Blo 1903435 2033633 := bbase (se 2 (by rfl) ⟨762612, by rfl⟩ : syracuseStep 2033633 = 1525225) (by norm_num)
theorem B5423021 : Blo 1903435 5423021 := bstep (se 3 (by rfl) ⟨1016816, by rfl⟩ : syracuseStep 5423021 = 2033633) B2033633
theorem B3615347 : Blo 1903435 3615347 := bstep (se 1 (by rfl) ⟨2711510, by rfl⟩ : syracuseStep 3615347 = 5423021) B5423021
theorem B2410231 : Blo 1903435 2410231 := bstep (se 1 (by rfl) ⟨1807673, by rfl⟩ : syracuseStep 2410231 = 3615347) B3615347
theorem B3213641 : Blo 1903435 3213641 := bstep (se 2 (by rfl) ⟨1205115, by rfl⟩ : syracuseStep 3213641 = 2410231) B2410231
theorem B2142427 : Blo 1903435 2142427 := bstep (se 1 (by rfl) ⟨1606820, by rfl⟩ : syracuseStep 2142427 = 3213641) B3213641
theorem B2856569 : Blo 1903435 2856569 := bstep (se 2 (by rfl) ⟨1071213, by rfl⟩ : syracuseStep 2856569 = 2142427) B2142427
theorem B1904379 : Blo 1903435 1904379 := bstep (se 1 (by rfl) ⟨1428284, by rfl⟩ : syracuseStep 1904379 = 2856569) B2856569
theorem B9905813 : Blo 1903435 9905813 := bbase (se 6 (by rfl) ⟨232167, by rfl⟩ : syracuseStep 9905813 = 464335) (by norm_num)
theorem B6603875 : Blo 1903435 6603875 := bstep (se 1 (by rfl) ⟨4952906, by rfl⟩ : syracuseStep 6603875 = 9905813) B9905813
theorem B4402583 : Blo 1903435 4402583 := bstep (se 1 (by rfl) ⟨3301937, by rfl⟩ : syracuseStep 4402583 = 6603875) B6603875
theorem B2935055 : Blo 1903435 2935055 := bstep (se 1 (by rfl) ⟨2201291, by rfl⟩ : syracuseStep 2935055 = 4402583) B4402583
theorem B1956703 : Blo 1903435 1956703 := bstep (se 1 (by rfl) ⟨1467527, by rfl⟩ : syracuseStep 1956703 = 2935055) B2935055
theorem B2608937 : Blo 1903435 2608937 := bstep (se 2 (by rfl) ⟨978351, by rfl⟩ : syracuseStep 2608937 = 1956703) B1956703
theorem B111314645 : Blo 1903435 111314645 := bstep (se 7 (by rfl) ⟨1304468, by rfl⟩ : syracuseStep 111314645 = 2608937) B2608937
theorem B74209763 : Blo 1903435 74209763 := bstep (se 1 (by rfl) ⟨55657322, by rfl⟩ : syracuseStep 74209763 = 111314645) B111314645
theorem B49473175 : Blo 1903435 49473175 := bstep (se 1 (by rfl) ⟨37104881, by rfl⟩ : syracuseStep 49473175 = 74209763) B74209763
theorem B65964233 : Blo 1903435 65964233 := bstep (se 2 (by rfl) ⟨24736587, by rfl⟩ : syracuseStep 65964233 = 49473175) B49473175
theorem B43976155 : Blo 1903435 43976155 := bstep (se 1 (by rfl) ⟨32982116, by rfl⟩ : syracuseStep 43976155 = 65964233) B65964233
theorem B58634873 : Blo 1903435 58634873 := bstep (se 2 (by rfl) ⟨21988077, by rfl⟩ : syracuseStep 58634873 = 43976155) B43976155
theorem B39089915 : Blo 1903435 39089915 := bstep (se 1 (by rfl) ⟨29317436, by rfl⟩ : syracuseStep 39089915 = 58634873) B58634873
theorem B26059943 : Blo 1903435 26059943 := bstep (se 1 (by rfl) ⟨19544957, by rfl⟩ : syracuseStep 26059943 = 39089915) B39089915
theorem B17373295 : Blo 1903435 17373295 := bstep (se 1 (by rfl) ⟨13029971, by rfl⟩ : syracuseStep 17373295 = 26059943) B26059943
theorem B23164393 : Blo 1903435 23164393 := bstep (se 2 (by rfl) ⟨8686647, by rfl⟩ : syracuseStep 23164393 = 17373295) B17373295
theorem B30885857 : Blo 1903435 30885857 := bstep (se 2 (by rfl) ⟨11582196, by rfl⟩ : syracuseStep 30885857 = 23164393) B23164393
theorem B20590571 : Blo 1903435 20590571 := bstep (se 1 (by rfl) ⟨15442928, by rfl⟩ : syracuseStep 20590571 = 30885857) B30885857
theorem B54908189 : Blo 1903435 54908189 := bstep (se 3 (by rfl) ⟨10295285, by rfl⟩ : syracuseStep 54908189 = 20590571) B20590571
theorem B36605459 : Blo 1903435 36605459 := bstep (se 1 (by rfl) ⟨27454094, by rfl⟩ : syracuseStep 36605459 = 54908189) B54908189
theorem B24403639 : Blo 1903435 24403639 := bstep (se 1 (by rfl) ⟨18302729, by rfl⟩ : syracuseStep 24403639 = 36605459) B36605459
theorem B32538185 : Blo 1903435 32538185 := bstep (se 2 (by rfl) ⟨12201819, by rfl⟩ : syracuseStep 32538185 = 24403639) B24403639
theorem B21692123 : Blo 1903435 21692123 := bstep (se 1 (by rfl) ⟨16269092, by rfl⟩ : syracuseStep 21692123 = 32538185) B32538185
theorem B14461415 : Blo 1903435 14461415 := bstep (se 1 (by rfl) ⟨10846061, by rfl⟩ : syracuseStep 14461415 = 21692123) B21692123
theorem B9640943 : Blo 1903435 9640943 := bstep (se 1 (by rfl) ⟨7230707, by rfl⟩ : syracuseStep 9640943 = 14461415) B14461415
theorem B6427295 : Blo 1903435 6427295 := bstep (se 1 (by rfl) ⟨4820471, by rfl⟩ : syracuseStep 6427295 = 9640943) B9640943
theorem B4284863 : Blo 1903435 4284863 := bstep (se 1 (by rfl) ⟨3213647, by rfl⟩ : syracuseStep 4284863 = 6427295) B6427295
theorem B2856575 : Blo 1903435 2856575 := bstep (se 1 (by rfl) ⟨2142431, by rfl⟩ : syracuseStep 2856575 = 4284863) B4284863
theorem B1904383 : Blo 1903435 1904383 := bstep (se 1 (by rfl) ⟨1428287, by rfl⟩ : syracuseStep 1904383 = 2856575) B2856575
theorem B2856581 : Blo 1903435 2856581 := bbase (se 4 (by rfl) ⟨267804, by rfl⟩ : syracuseStep 2856581 = 535609) (by norm_num)
theorem B1904387 : Blo 1903435 1904387 := bstep (se 1 (by rfl) ⟨1428290, by rfl⟩ : syracuseStep 1904387 = 2856581) B2856581
theorem B3213661 : Blo 1903435 3213661 := bbase (se 3 (by rfl) ⟨602561, by rfl⟩ : syracuseStep 3213661 = 1205123) (by norm_num)
theorem B4284881 : Blo 1903435 4284881 := bstep (se 2 (by rfl) ⟨1606830, by rfl⟩ : syracuseStep 4284881 = 3213661) B3213661
theorem B2856587 : Blo 1903435 2856587 := bstep (se 1 (by rfl) ⟨2142440, by rfl⟩ : syracuseStep 2856587 = 4284881) B4284881
theorem B1904391 : Blo 1903435 1904391 := bstep (se 1 (by rfl) ⟨1428293, by rfl⟩ : syracuseStep 1904391 = 2856587) B2856587
theorem B2142445 : Blo 1903435 2142445 := bbase (se 3 (by rfl) ⟨401708, by rfl⟩ : syracuseStep 2142445 = 803417) (by norm_num)
theorem B2856593 : Blo 1903435 2856593 := bstep (se 2 (by rfl) ⟨1071222, by rfl⟩ : syracuseStep 2856593 = 2142445) B2142445
theorem B1904395 : Blo 1903435 1904395 := bstep (se 1 (by rfl) ⟨1428296, by rfl⟩ : syracuseStep 1904395 = 2856593) B2856593
theorem B6427349 : Blo 1903435 6427349 := bbase (se 7 (by rfl) ⟨75320, by rfl⟩ : syracuseStep 6427349 = 150641) (by norm_num)
theorem B4284899 : Blo 1903435 4284899 := bstep (se 1 (by rfl) ⟨3213674, by rfl⟩ : syracuseStep 4284899 = 6427349) B6427349
theorem B2856599 : Blo 1903435 2856599 := bstep (se 1 (by rfl) ⟨2142449, by rfl⟩ : syracuseStep 2856599 = 4284899) B4284899
theorem B1904399 : Blo 1903435 1904399 := bstep (se 1 (by rfl) ⟨1428299, by rfl⟩ : syracuseStep 1904399 = 2856599) B2856599
theorem B2856605 : Blo 1903435 2856605 := bbase (se 3 (by rfl) ⟨535613, by rfl⟩ : syracuseStep 2856605 = 1071227) (by norm_num)
theorem B1904403 : Blo 1903435 1904403 := bstep (se 1 (by rfl) ⟨1428302, by rfl⟩ : syracuseStep 1904403 = 2856605) B2856605
theorem B4284917 : Blo 1903435 4284917 := bbase (se 5 (by rfl) ⟨200855, by rfl⟩ : syracuseStep 4284917 = 401711) (by norm_num)
theorem B2856611 : Blo 1903435 2856611 := bstep (se 1 (by rfl) ⟨2142458, by rfl⟩ : syracuseStep 2856611 = 4284917) B4284917
theorem B1904407 : Blo 1903435 1904407 := bstep (se 1 (by rfl) ⟨1428305, by rfl⟩ : syracuseStep 1904407 = 2856611) B2856611
theorem B3431813 : Blo 1903435 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B36606005 : Blo 1903435 36606005 := bstep (se 5 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 36606005 = 3431813) B3431813
theorem B24404003 : Blo 1903435 24404003 := bstep (se 1 (by rfl) ⟨18303002, by rfl⟩ : syracuseStep 24404003 = 36606005) B36606005
theorem B16269335 : Blo 1903435 16269335 := bstep (se 1 (by rfl) ⟨12202001, by rfl⟩ : syracuseStep 16269335 = 24404003) B24404003
theorem B10846223 : Blo 1903435 10846223 := bstep (se 1 (by rfl) ⟨8134667, by rfl⟩ : syracuseStep 10846223 = 16269335) B16269335
theorem B7230815 : Blo 1903435 7230815 := bstep (se 1 (by rfl) ⟨5423111, by rfl⟩ : syracuseStep 7230815 = 10846223) B10846223
theorem B4820543 : Blo 1903435 4820543 := bstep (se 1 (by rfl) ⟨3615407, by rfl⟩ : syracuseStep 4820543 = 7230815) B7230815
theorem B3213695 : Blo 1903435 3213695 := bstep (se 1 (by rfl) ⟨2410271, by rfl⟩ : syracuseStep 3213695 = 4820543) B4820543
theorem B2142463 : Blo 1903435 2142463 := bstep (se 1 (by rfl) ⟨1606847, by rfl⟩ : syracuseStep 2142463 = 3213695) B3213695
theorem B2856617 : Blo 1903435 2856617 := bstep (se 2 (by rfl) ⟨1071231, by rfl⟩ : syracuseStep 2856617 = 2142463) B2142463
theorem B1904411 : Blo 1903435 1904411 := bstep (se 1 (by rfl) ⟨1428308, by rfl⟩ : syracuseStep 1904411 = 2856617) B2856617
theorem B3431821 : Blo 1903435 3431821 := bbase (se 3 (by rfl) ⟨643466, by rfl⟩ : syracuseStep 3431821 = 1286933) (by norm_num)
theorem B4575761 : Blo 1903435 4575761 := bstep (se 2 (by rfl) ⟨1715910, by rfl⟩ : syracuseStep 4575761 = 3431821) B3431821
theorem B3050507 : Blo 1903435 3050507 := bstep (se 1 (by rfl) ⟨2287880, by rfl⟩ : syracuseStep 3050507 = 4575761) B4575761
theorem B2033671 : Blo 1903435 2033671 := bstep (se 1 (by rfl) ⟨1525253, by rfl⟩ : syracuseStep 2033671 = 3050507) B3050507
theorem B2711561 : Blo 1903435 2711561 := bstep (se 2 (by rfl) ⟨1016835, by rfl⟩ : syracuseStep 2711561 = 2033671) B2033671
theorem B7230829 : Blo 1903435 7230829 := bstep (se 3 (by rfl) ⟨1355780, by rfl⟩ : syracuseStep 7230829 = 2711561) B2711561
theorem B9641105 : Blo 1903435 9641105 := bstep (se 2 (by rfl) ⟨3615414, by rfl⟩ : syracuseStep 9641105 = 7230829) B7230829
theorem B6427403 : Blo 1903435 6427403 := bstep (se 1 (by rfl) ⟨4820552, by rfl⟩ : syracuseStep 6427403 = 9641105) B9641105
theorem B4284935 : Blo 1903435 4284935 := bstep (se 1 (by rfl) ⟨3213701, by rfl⟩ : syracuseStep 4284935 = 6427403) B6427403
theorem B2856623 : Blo 1903435 2856623 := bstep (se 1 (by rfl) ⟨2142467, by rfl⟩ : syracuseStep 2856623 = 4284935) B4284935
theorem B1904415 : Blo 1903435 1904415 := bstep (se 1 (by rfl) ⟨1428311, by rfl⟩ : syracuseStep 1904415 = 2856623) B2856623
theorem B2856629 : Blo 1903435 2856629 := bbase (se 5 (by rfl) ⟨133904, by rfl⟩ : syracuseStep 2856629 = 267809) (by norm_num)
theorem B1904419 : Blo 1903435 1904419 := bstep (se 1 (by rfl) ⟨1428314, by rfl⟩ : syracuseStep 1904419 = 2856629) B2856629
theorem B4820573 : Blo 1903435 4820573 := bbase (se 3 (by rfl) ⟨903857, by rfl⟩ : syracuseStep 4820573 = 1807715) (by norm_num)
theorem B3213715 : Blo 1903435 3213715 := bstep (se 1 (by rfl) ⟨2410286, by rfl⟩ : syracuseStep 3213715 = 4820573) B4820573
theorem B4284953 : Blo 1903435 4284953 := bstep (se 2 (by rfl) ⟨1606857, by rfl⟩ : syracuseStep 4284953 = 3213715) B3213715
theorem B2856635 : Blo 1903435 2856635 := bstep (se 1 (by rfl) ⟨2142476, by rfl⟩ : syracuseStep 2856635 = 4284953) B4284953
theorem B1904423 : Blo 1903435 1904423 := bstep (se 1 (by rfl) ⟨1428317, by rfl⟩ : syracuseStep 1904423 = 2856635) B2856635
theorem B2142481 : Blo 1903435 2142481 := bbase (se 2 (by rfl) ⟨803430, by rfl⟩ : syracuseStep 2142481 = 1606861) (by norm_num)
theorem B2856641 : Blo 1903435 2856641 := bstep (se 2 (by rfl) ⟨1071240, by rfl⟩ : syracuseStep 2856641 = 2142481) B2142481
theorem B1904427 : Blo 1903435 1904427 := bstep (se 1 (by rfl) ⟨1428320, by rfl⟩ : syracuseStep 1904427 = 2856641) B2856641
theorem B3615445 : Blo 1903435 3615445 := bbase (se 7 (by rfl) ⟨42368, by rfl⟩ : syracuseStep 3615445 = 84737) (by norm_num)
theorem B4820593 : Blo 1903435 4820593 := bstep (se 2 (by rfl) ⟨1807722, by rfl⟩ : syracuseStep 4820593 = 3615445) B3615445
theorem B6427457 : Blo 1903435 6427457 := bstep (se 2 (by rfl) ⟨2410296, by rfl⟩ : syracuseStep 6427457 = 4820593) B4820593
theorem B4284971 : Blo 1903435 4284971 := bstep (se 1 (by rfl) ⟨3213728, by rfl⟩ : syracuseStep 4284971 = 6427457) B6427457
theorem B2856647 : Blo 1903435 2856647 := bstep (se 1 (by rfl) ⟨2142485, by rfl⟩ : syracuseStep 2856647 = 4284971) B4284971
theorem B1904431 : Blo 1903435 1904431 := bstep (se 1 (by rfl) ⟨1428323, by rfl⟩ : syracuseStep 1904431 = 2856647) B2856647
theorem B2856653 : Blo 1903435 2856653 := bbase (se 3 (by rfl) ⟨535622, by rfl⟩ : syracuseStep 2856653 = 1071245) (by norm_num)
theorem B1904435 : Blo 1903435 1904435 := bstep (se 1 (by rfl) ⟨1428326, by rfl⟩ : syracuseStep 1904435 = 2856653) B2856653
theorem B4284989 : Blo 1903435 4284989 := bbase (se 3 (by rfl) ⟨803435, by rfl⟩ : syracuseStep 4284989 = 1606871) (by norm_num)
theorem B2856659 : Blo 1903435 2856659 := bstep (se 1 (by rfl) ⟨2142494, by rfl⟩ : syracuseStep 2856659 = 4284989) B4284989
theorem B1904439 : Blo 1903435 1904439 := bstep (se 1 (by rfl) ⟨1428329, by rfl⟩ : syracuseStep 1904439 = 2856659) B2856659
theorem B3213749 : Blo 1903435 3213749 := bbase (se 5 (by rfl) ⟨150644, by rfl⟩ : syracuseStep 3213749 = 301289) (by norm_num)
theorem B2142499 : Blo 1903435 2142499 := bstep (se 1 (by rfl) ⟨1606874, by rfl⟩ : syracuseStep 2142499 = 3213749) B3213749
theorem B2856665 : Blo 1903435 2856665 := bstep (se 2 (by rfl) ⟨1071249, by rfl⟩ : syracuseStep 2856665 = 2142499) B2142499
theorem B1904443 : Blo 1903435 1904443 := bstep (se 1 (by rfl) ⟨1428332, by rfl⟩ : syracuseStep 1904443 = 2856665) B2856665
theorem B2033705 : Blo 1903435 2033705 := bbase (se 2 (by rfl) ⟨762639, by rfl⟩ : syracuseStep 2033705 = 1525279) (by norm_num)
theorem B5423213 : Blo 1903435 5423213 := bstep (se 3 (by rfl) ⟨1016852, by rfl⟩ : syracuseStep 5423213 = 2033705) B2033705
theorem B14461901 : Blo 1903435 14461901 := bstep (se 3 (by rfl) ⟨2711606, by rfl⟩ : syracuseStep 14461901 = 5423213) B5423213
theorem B9641267 : Blo 1903435 9641267 := bstep (se 1 (by rfl) ⟨7230950, by rfl⟩ : syracuseStep 9641267 = 14461901) B14461901
theorem B6427511 : Blo 1903435 6427511 := bstep (se 1 (by rfl) ⟨4820633, by rfl⟩ : syracuseStep 6427511 = 9641267) B9641267
theorem B4285007 : Blo 1903435 4285007 := bstep (se 1 (by rfl) ⟨3213755, by rfl⟩ : syracuseStep 4285007 = 6427511) B6427511
theorem B2856671 : Blo 1903435 2856671 := bstep (se 1 (by rfl) ⟨2142503, by rfl⟩ : syracuseStep 2856671 = 4285007) B4285007
theorem B1904447 : Blo 1903435 1904447 := bstep (se 1 (by rfl) ⟨1428335, by rfl⟩ : syracuseStep 1904447 = 2856671) B2856671
theorem B2856677 : Blo 1903435 2856677 := bbase (se 4 (by rfl) ⟨267813, by rfl⟩ : syracuseStep 2856677 = 535627) (by norm_num)
theorem B1904451 : Blo 1903435 1904451 := bstep (se 1 (by rfl) ⟨1428338, by rfl⟩ : syracuseStep 1904451 = 2856677) B2856677
theorem B5423237 : Blo 1903435 5423237 := bbase (se 4 (by rfl) ⟨508428, by rfl⟩ : syracuseStep 5423237 = 1016857) (by norm_num)
theorem B3615491 : Blo 1903435 3615491 := bstep (se 1 (by rfl) ⟨2711618, by rfl⟩ : syracuseStep 3615491 = 5423237) B5423237
theorem B2410327 : Blo 1903435 2410327 := bstep (se 1 (by rfl) ⟨1807745, by rfl⟩ : syracuseStep 2410327 = 3615491) B3615491
theorem B3213769 : Blo 1903435 3213769 := bstep (se 2 (by rfl) ⟨1205163, by rfl⟩ : syracuseStep 3213769 = 2410327) B2410327
theorem B4285025 : Blo 1903435 4285025 := bstep (se 2 (by rfl) ⟨1606884, by rfl⟩ : syracuseStep 4285025 = 3213769) B3213769
theorem B2856683 : Blo 1903435 2856683 := bstep (se 1 (by rfl) ⟨2142512, by rfl⟩ : syracuseStep 2856683 = 4285025) B4285025
theorem B1904455 : Blo 1903435 1904455 := bstep (se 1 (by rfl) ⟨1428341, by rfl⟩ : syracuseStep 1904455 = 2856683) B2856683
theorem B2142517 : Blo 1903435 2142517 := bbase (se 5 (by rfl) ⟨100430, by rfl⟩ : syracuseStep 2142517 = 200861) (by norm_num)
theorem B2856689 : Blo 1903435 2856689 := bstep (se 2 (by rfl) ⟨1071258, by rfl⟩ : syracuseStep 2856689 = 2142517) B2142517
theorem B1904459 : Blo 1903435 1904459 := bstep (se 1 (by rfl) ⟨1428344, by rfl⟩ : syracuseStep 1904459 = 2856689) B2856689
theorem B2410337 : Blo 1903435 2410337 := bbase (se 2 (by rfl) ⟨903876, by rfl⟩ : syracuseStep 2410337 = 1807753) (by norm_num)
theorem B6427565 : Blo 1903435 6427565 := bstep (se 3 (by rfl) ⟨1205168, by rfl⟩ : syracuseStep 6427565 = 2410337) B2410337
theorem B4285043 : Blo 1903435 4285043 := bstep (se 1 (by rfl) ⟨3213782, by rfl⟩ : syracuseStep 4285043 = 6427565) B6427565
theorem B2856695 : Blo 1903435 2856695 := bstep (se 1 (by rfl) ⟨2142521, by rfl⟩ : syracuseStep 2856695 = 4285043) B4285043
theorem B1904463 : Blo 1903435 1904463 := bstep (se 1 (by rfl) ⟨1428347, by rfl⟩ : syracuseStep 1904463 = 2856695) B2856695
theorem B2856701 : Blo 1903435 2856701 := bbase (se 3 (by rfl) ⟨535631, by rfl⟩ : syracuseStep 2856701 = 1071263) (by norm_num)
theorem B1904467 : Blo 1903435 1904467 := bstep (se 1 (by rfl) ⟨1428350, by rfl⟩ : syracuseStep 1904467 = 2856701) B2856701
theorem B4285061 : Blo 1903435 4285061 := bbase (se 4 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 4285061 = 803449) (by norm_num)
theorem B2856707 : Blo 1903435 2856707 := bstep (se 1 (by rfl) ⟨2142530, by rfl⟩ : syracuseStep 2856707 = 4285061) B4285061
theorem B1904471 : Blo 1903435 1904471 := bstep (se 1 (by rfl) ⟨1428353, by rfl⟩ : syracuseStep 1904471 = 2856707) B2856707
theorem B3257653 : Blo 1903435 3257653 := bbase (se 5 (by rfl) ⟨152702, by rfl⟩ : syracuseStep 3257653 = 305405) (by norm_num)
theorem B4343537 : Blo 1903435 4343537 := bstep (se 2 (by rfl) ⟨1628826, by rfl⟩ : syracuseStep 4343537 = 3257653) B3257653
theorem B2895691 : Blo 1903435 2895691 := bstep (se 1 (by rfl) ⟨2171768, by rfl⟩ : syracuseStep 2895691 = 4343537) B4343537
theorem B3860921 : Blo 1903435 3860921 := bstep (se 2 (by rfl) ⟨1447845, by rfl⟩ : syracuseStep 3860921 = 2895691) B2895691
theorem B2573947 : Blo 1903435 2573947 := bstep (se 1 (by rfl) ⟨1930460, by rfl⟩ : syracuseStep 2573947 = 3860921) B3860921
theorem B13727717 : Blo 1903435 13727717 := bstep (se 4 (by rfl) ⟨1286973, by rfl⟩ : syracuseStep 13727717 = 2573947) B2573947
theorem B9151811 : Blo 1903435 9151811 := bstep (se 1 (by rfl) ⟨6863858, by rfl⟩ : syracuseStep 9151811 = 13727717) B13727717
theorem B6101207 : Blo 1903435 6101207 := bstep (se 1 (by rfl) ⟨4575905, by rfl⟩ : syracuseStep 6101207 = 9151811) B9151811
theorem B4067471 : Blo 1903435 4067471 := bstep (se 1 (by rfl) ⟨3050603, by rfl⟩ : syracuseStep 4067471 = 6101207) B6101207
theorem B2711647 : Blo 1903435 2711647 := bstep (se 1 (by rfl) ⟨2033735, by rfl⟩ : syracuseStep 2711647 = 4067471) B4067471
theorem B3615529 : Blo 1903435 3615529 := bstep (se 2 (by rfl) ⟨1355823, by rfl⟩ : syracuseStep 3615529 = 2711647) B2711647
theorem B4820705 : Blo 1903435 4820705 := bstep (se 2 (by rfl) ⟨1807764, by rfl⟩ : syracuseStep 4820705 = 3615529) B3615529
theorem B3213803 : Blo 1903435 3213803 := bstep (se 1 (by rfl) ⟨2410352, by rfl⟩ : syracuseStep 3213803 = 4820705) B4820705
theorem B2142535 : Blo 1903435 2142535 := bstep (se 1 (by rfl) ⟨1606901, by rfl⟩ : syracuseStep 2142535 = 3213803) B3213803
theorem B2856713 : Blo 1903435 2856713 := bstep (se 2 (by rfl) ⟨1071267, by rfl⟩ : syracuseStep 2856713 = 2142535) B2142535
theorem B1904475 : Blo 1903435 1904475 := bstep (se 1 (by rfl) ⟨1428356, by rfl⟩ : syracuseStep 1904475 = 2856713) B2856713
theorem B9641429 : Blo 1903435 9641429 := bbase (se 7 (by rfl) ⟨112985, by rfl⟩ : syracuseStep 9641429 = 225971) (by norm_num)
theorem B6427619 : Blo 1903435 6427619 := bstep (se 1 (by rfl) ⟨4820714, by rfl⟩ : syracuseStep 6427619 = 9641429) B9641429
theorem B4285079 : Blo 1903435 4285079 := bstep (se 1 (by rfl) ⟨3213809, by rfl⟩ : syracuseStep 4285079 = 6427619) B6427619
theorem B2856719 : Blo 1903435 2856719 := bstep (se 1 (by rfl) ⟨2142539, by rfl⟩ : syracuseStep 2856719 = 4285079) B4285079
theorem B1904479 : Blo 1903435 1904479 := bstep (se 1 (by rfl) ⟨1428359, by rfl⟩ : syracuseStep 1904479 = 2856719) B2856719
theorem B2856725 : Blo 1903435 2856725 := bbase (se 6 (by rfl) ⟨66954, by rfl⟩ : syracuseStep 2856725 = 133909) (by norm_num)
theorem B1904483 : Blo 1903435 1904483 := bstep (se 1 (by rfl) ⟨1428362, by rfl⟩ : syracuseStep 1904483 = 2856725) B2856725
theorem B39092053 : Blo 1903435 39092053 := bbase (se 9 (by rfl) ⟨114527, by rfl⟩ : syracuseStep 39092053 = 229055) (by norm_num)
theorem B52122737 : Blo 1903435 52122737 := bstep (se 2 (by rfl) ⟨19546026, by rfl⟩ : syracuseStep 52122737 = 39092053) B39092053
theorem B138993965 : Blo 1903435 138993965 := bstep (se 3 (by rfl) ⟨26061368, by rfl⟩ : syracuseStep 138993965 = 52122737) B52122737
theorem B92662643 : Blo 1903435 92662643 := bstep (se 1 (by rfl) ⟨69496982, by rfl⟩ : syracuseStep 92662643 = 138993965) B138993965
theorem B61775095 : Blo 1903435 61775095 := bstep (se 1 (by rfl) ⟨46331321, by rfl⟩ : syracuseStep 61775095 = 92662643) B92662643
theorem B82366793 : Blo 1903435 82366793 := bstep (se 2 (by rfl) ⟨30887547, by rfl⟩ : syracuseStep 82366793 = 61775095) B61775095
theorem B54911195 : Blo 1903435 54911195 := bstep (se 1 (by rfl) ⟨41183396, by rfl⟩ : syracuseStep 54911195 = 82366793) B82366793
theorem B36607463 : Blo 1903435 36607463 := bstep (se 1 (by rfl) ⟨27455597, by rfl⟩ : syracuseStep 36607463 = 54911195) B54911195
theorem B24404975 : Blo 1903435 24404975 := bstep (se 1 (by rfl) ⟨18303731, by rfl⟩ : syracuseStep 24404975 = 36607463) B36607463
theorem B16269983 : Blo 1903435 16269983 := bstep (se 1 (by rfl) ⟨12202487, by rfl⟩ : syracuseStep 16269983 = 24404975) B24404975
theorem B10846655 : Blo 1903435 10846655 := bstep (se 1 (by rfl) ⟨8134991, by rfl⟩ : syracuseStep 10846655 = 16269983) B16269983
theorem B7231103 : Blo 1903435 7231103 := bstep (se 1 (by rfl) ⟨5423327, by rfl⟩ : syracuseStep 7231103 = 10846655) B10846655
theorem B4820735 : Blo 1903435 4820735 := bstep (se 1 (by rfl) ⟨3615551, by rfl⟩ : syracuseStep 4820735 = 7231103) B7231103
theorem B3213823 : Blo 1903435 3213823 := bstep (se 1 (by rfl) ⟨2410367, by rfl⟩ : syracuseStep 3213823 = 4820735) B4820735
theorem B4285097 : Blo 1903435 4285097 := bstep (se 2 (by rfl) ⟨1606911, by rfl⟩ : syracuseStep 4285097 = 3213823) B3213823
theorem B2856731 : Blo 1903435 2856731 := bstep (se 1 (by rfl) ⟨2142548, by rfl⟩ : syracuseStep 2856731 = 4285097) B4285097
theorem B1904487 : Blo 1903435 1904487 := bstep (se 1 (by rfl) ⟨1428365, by rfl⟩ : syracuseStep 1904487 = 2856731) B2856731
theorem B2142553 : Blo 1903435 2142553 := bbase (se 2 (by rfl) ⟨803457, by rfl⟩ : syracuseStep 2142553 = 1606915) (by norm_num)
theorem B2856737 : Blo 1903435 2856737 := bstep (se 2 (by rfl) ⟨1071276, by rfl⟩ : syracuseStep 2856737 = 2142553) B2142553
theorem B1904491 : Blo 1903435 1904491 := bstep (se 1 (by rfl) ⟨1428368, by rfl⟩ : syracuseStep 1904491 = 2856737) B2856737
theorem B3431965 : Blo 1903435 3431965 := bbase (se 3 (by rfl) ⟨643493, by rfl⟩ : syracuseStep 3431965 = 1286987) (by norm_num)
theorem B4575953 : Blo 1903435 4575953 := bstep (se 2 (by rfl) ⟨1715982, by rfl⟩ : syracuseStep 4575953 = 3431965) B3431965
theorem B3050635 : Blo 1903435 3050635 := bstep (se 1 (by rfl) ⟨2287976, by rfl⟩ : syracuseStep 3050635 = 4575953) B4575953
theorem B4067513 : Blo 1903435 4067513 := bstep (se 2 (by rfl) ⟨1525317, by rfl⟩ : syracuseStep 4067513 = 3050635) B3050635
theorem B2711675 : Blo 1903435 2711675 := bstep (se 1 (by rfl) ⟨2033756, by rfl⟩ : syracuseStep 2711675 = 4067513) B4067513
theorem B7231133 : Blo 1903435 7231133 := bstep (se 3 (by rfl) ⟨1355837, by rfl⟩ : syracuseStep 7231133 = 2711675) B2711675
theorem B4820755 : Blo 1903435 4820755 := bstep (se 1 (by rfl) ⟨3615566, by rfl⟩ : syracuseStep 4820755 = 7231133) B7231133
theorem B6427673 : Blo 1903435 6427673 := bstep (se 2 (by rfl) ⟨2410377, by rfl⟩ : syracuseStep 6427673 = 4820755) B4820755
theorem B4285115 : Blo 1903435 4285115 := bstep (se 1 (by rfl) ⟨3213836, by rfl⟩ : syracuseStep 4285115 = 6427673) B6427673
theorem B2856743 : Blo 1903435 2856743 := bstep (se 1 (by rfl) ⟨2142557, by rfl⟩ : syracuseStep 2856743 = 4285115) B4285115
theorem B1904495 : Blo 1903435 1904495 := bstep (se 1 (by rfl) ⟨1428371, by rfl⟩ : syracuseStep 1904495 = 2856743) B2856743
theorem B2856749 : Blo 1903435 2856749 := bbase (se 3 (by rfl) ⟨535640, by rfl⟩ : syracuseStep 2856749 = 1071281) (by norm_num)
theorem B1904499 : Blo 1903435 1904499 := bstep (se 1 (by rfl) ⟨1428374, by rfl⟩ : syracuseStep 1904499 = 2856749) B2856749
theorem B4285133 : Blo 1903435 4285133 := bbase (se 3 (by rfl) ⟨803462, by rfl⟩ : syracuseStep 4285133 = 1606925) (by norm_num)
theorem B2856755 : Blo 1903435 2856755 := bstep (se 1 (by rfl) ⟨2142566, by rfl⟩ : syracuseStep 2856755 = 4285133) B4285133
theorem B1904503 : Blo 1903435 1904503 := bstep (se 1 (by rfl) ⟨1428377, by rfl⟩ : syracuseStep 1904503 = 2856755) B2856755
theorem B2410393 : Blo 1903435 2410393 := bbase (se 2 (by rfl) ⟨903897, by rfl⟩ : syracuseStep 2410393 = 1807795) (by norm_num)
theorem B3213857 : Blo 1903435 3213857 := bstep (se 2 (by rfl) ⟨1205196, by rfl⟩ : syracuseStep 3213857 = 2410393) B2410393
theorem B2142571 : Blo 1903435 2142571 := bstep (se 1 (by rfl) ⟨1606928, by rfl⟩ : syracuseStep 2142571 = 3213857) B3213857
theorem B2856761 : Blo 1903435 2856761 := bstep (se 2 (by rfl) ⟨1071285, by rfl⟩ : syracuseStep 2856761 = 2142571) B2142571
theorem B1904507 : Blo 1903435 1904507 := bstep (se 1 (by rfl) ⟨1428380, by rfl⟩ : syracuseStep 1904507 = 2856761) B2856761
theorem B8135093 : Blo 1903435 8135093 := bbase (se 5 (by rfl) ⟨381332, by rfl⟩ : syracuseStep 8135093 = 762665) (by norm_num)
theorem B21693581 : Blo 1903435 21693581 := bstep (se 3 (by rfl) ⟨4067546, by rfl⟩ : syracuseStep 21693581 = 8135093) B8135093
theorem B14462387 : Blo 1903435 14462387 := bstep (se 1 (by rfl) ⟨10846790, by rfl⟩ : syracuseStep 14462387 = 21693581) B21693581
theorem B9641591 : Blo 1903435 9641591 := bstep (se 1 (by rfl) ⟨7231193, by rfl⟩ : syracuseStep 9641591 = 14462387) B14462387
theorem B6427727 : Blo 1903435 6427727 := bstep (se 1 (by rfl) ⟨4820795, by rfl⟩ : syracuseStep 6427727 = 9641591) B9641591
theorem B4285151 : Blo 1903435 4285151 := bstep (se 1 (by rfl) ⟨3213863, by rfl⟩ : syracuseStep 4285151 = 6427727) B6427727
theorem B2856767 : Blo 1903435 2856767 := bstep (se 1 (by rfl) ⟨2142575, by rfl⟩ : syracuseStep 2856767 = 4285151) B4285151
theorem B1904511 : Blo 1903435 1904511 := bstep (se 1 (by rfl) ⟨1428383, by rfl⟩ : syracuseStep 1904511 = 2856767) B2856767
theorem B2856773 : Blo 1903435 2856773 := bbase (se 4 (by rfl) ⟨267822, by rfl⟩ : syracuseStep 2856773 = 535645) (by norm_num)
theorem B1904515 : Blo 1903435 1904515 := bstep (se 1 (by rfl) ⟨1428386, by rfl⟩ : syracuseStep 1904515 = 2856773) B2856773
theorem B3213877 : Blo 1903435 3213877 := bbase (se 5 (by rfl) ⟨150650, by rfl⟩ : syracuseStep 3213877 = 301301) (by norm_num)
theorem B4285169 : Blo 1903435 4285169 := bstep (se 2 (by rfl) ⟨1606938, by rfl⟩ : syracuseStep 4285169 = 3213877) B3213877
theorem B2856779 : Blo 1903435 2856779 := bstep (se 1 (by rfl) ⟨2142584, by rfl⟩ : syracuseStep 2856779 = 4285169) B4285169
theorem B1904519 : Blo 1903435 1904519 := bstep (se 1 (by rfl) ⟨1428389, by rfl⟩ : syracuseStep 1904519 = 2856779) B2856779
theorem B2142589 : Blo 1903435 2142589 := bbase (se 3 (by rfl) ⟨401735, by rfl⟩ : syracuseStep 2142589 = 803471) (by norm_num)
theorem B2856785 : Blo 1903435 2856785 := bstep (se 2 (by rfl) ⟨1071294, by rfl⟩ : syracuseStep 2856785 = 2142589) B2142589
theorem B1904523 : Blo 1903435 1904523 := bstep (se 1 (by rfl) ⟨1428392, by rfl⟩ : syracuseStep 1904523 = 2856785) B2856785
theorem B6427781 : Blo 1903435 6427781 := bbase (se 4 (by rfl) ⟨602604, by rfl⟩ : syracuseStep 6427781 = 1205209) (by norm_num)
theorem B4285187 : Blo 1903435 4285187 := bstep (se 1 (by rfl) ⟨3213890, by rfl⟩ : syracuseStep 4285187 = 6427781) B6427781
theorem B2856791 : Blo 1903435 2856791 := bstep (se 1 (by rfl) ⟨2142593, by rfl⟩ : syracuseStep 2856791 = 4285187) B4285187
theorem B1904527 : Blo 1903435 1904527 := bstep (se 1 (by rfl) ⟨1428395, by rfl⟩ : syracuseStep 1904527 = 2856791) B2856791
theorem B2856797 : Blo 1903435 2856797 := bbase (se 3 (by rfl) ⟨535649, by rfl⟩ : syracuseStep 2856797 = 1071299) (by norm_num)
theorem B1904531 : Blo 1903435 1904531 := bstep (se 1 (by rfl) ⟨1428398, by rfl⟩ : syracuseStep 1904531 = 2856797) B2856797
theorem B4285205 : Blo 1903435 4285205 := bbase (se 6 (by rfl) ⟨100434, by rfl⟩ : syracuseStep 4285205 = 200869) (by norm_num)
theorem B2856803 : Blo 1903435 2856803 := bstep (se 1 (by rfl) ⟨2142602, by rfl⟩ : syracuseStep 2856803 = 4285205) B4285205
theorem B1904535 : Blo 1903435 1904535 := bstep (se 1 (by rfl) ⟨1428401, by rfl⟩ : syracuseStep 1904535 = 2856803) B2856803
theorem B7231301 : Blo 1903435 7231301 := bbase (se 4 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 7231301 = 1355869) (by norm_num)
theorem B4820867 : Blo 1903435 4820867 := bstep (se 1 (by rfl) ⟨3615650, by rfl⟩ : syracuseStep 4820867 = 7231301) B7231301
theorem B3213911 : Blo 1903435 3213911 := bstep (se 1 (by rfl) ⟨2410433, by rfl⟩ : syracuseStep 3213911 = 4820867) B4820867
theorem B2142607 : Blo 1903435 2142607 := bstep (se 1 (by rfl) ⟨1606955, by rfl⟩ : syracuseStep 2142607 = 3213911) B3213911
theorem B2856809 : Blo 1903435 2856809 := bstep (se 2 (by rfl) ⟨1071303, by rfl⟩ : syracuseStep 2856809 = 2142607) B2142607
theorem B1904539 : Blo 1903435 1904539 := bstep (se 1 (by rfl) ⟨1428404, by rfl⟩ : syracuseStep 1904539 = 2856809) B2856809
theorem B2171845 : Blo 1903435 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B2895793 : Blo 1903435 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B15444229 : Blo 1903435 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B20592305 : Blo 1903435 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B13728203 : Blo 1903435 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B9152135 : Blo 1903435 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B6101423 : Blo 1903435 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B4067615 : Blo 1903435 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B10846973 : Blo 1903435 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B7231315 : Blo 1903435 7231315 := bstep (se 1 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 7231315 = 10846973) B10846973
theorem B9641753 : Blo 1903435 9641753 := bstep (se 2 (by rfl) ⟨3615657, by rfl⟩ : syracuseStep 9641753 = 7231315) B7231315
theorem B6427835 : Blo 1903435 6427835 := bstep (se 1 (by rfl) ⟨4820876, by rfl⟩ : syracuseStep 6427835 = 9641753) B9641753
theorem B4285223 : Blo 1903435 4285223 := bstep (se 1 (by rfl) ⟨3213917, by rfl⟩ : syracuseStep 4285223 = 6427835) B6427835
theorem B2856815 : Blo 1903435 2856815 := bstep (se 1 (by rfl) ⟨2142611, by rfl⟩ : syracuseStep 2856815 = 4285223) B4285223
theorem B1904543 : Blo 1903435 1904543 := bstep (se 1 (by rfl) ⟨1428407, by rfl⟩ : syracuseStep 1904543 = 2856815) B2856815
theorem B2856821 : Blo 1903435 2856821 := bbase (se 5 (by rfl) ⟨133913, by rfl⟩ : syracuseStep 2856821 = 267827) (by norm_num)
theorem B1904547 : Blo 1903435 1904547 := bstep (se 1 (by rfl) ⟨1428410, by rfl⟩ : syracuseStep 1904547 = 2856821) B2856821
theorem B3050725 : Blo 1903435 3050725 := bbase (se 4 (by rfl) ⟨286005, by rfl⟩ : syracuseStep 3050725 = 572011) (by norm_num)
theorem B4067633 : Blo 1903435 4067633 := bstep (se 2 (by rfl) ⟨1525362, by rfl⟩ : syracuseStep 4067633 = 3050725) B3050725
theorem B2711755 : Blo 1903435 2711755 := bstep (se 1 (by rfl) ⟨2033816, by rfl⟩ : syracuseStep 2711755 = 4067633) B4067633
theorem B3615673 : Blo 1903435 3615673 := bstep (se 2 (by rfl) ⟨1355877, by rfl⟩ : syracuseStep 3615673 = 2711755) B2711755
theorem B4820897 : Blo 1903435 4820897 := bstep (se 2 (by rfl) ⟨1807836, by rfl⟩ : syracuseStep 4820897 = 3615673) B3615673
theorem B3213931 : Blo 1903435 3213931 := bstep (se 1 (by rfl) ⟨2410448, by rfl⟩ : syracuseStep 3213931 = 4820897) B4820897
theorem B4285241 : Blo 1903435 4285241 := bstep (se 2 (by rfl) ⟨1606965, by rfl⟩ : syracuseStep 4285241 = 3213931) B3213931
theorem B2856827 : Blo 1903435 2856827 := bstep (se 1 (by rfl) ⟨2142620, by rfl⟩ : syracuseStep 2856827 = 4285241) B4285241
theorem B1904551 : Blo 1903435 1904551 := bstep (se 1 (by rfl) ⟨1428413, by rfl⟩ : syracuseStep 1904551 = 2856827) B2856827
theorem B2142625 : Blo 1903435 2142625 := bbase (se 2 (by rfl) ⟨803484, by rfl⟩ : syracuseStep 2142625 = 1606969) (by norm_num)
theorem B2856833 : Blo 1903435 2856833 := bstep (se 2 (by rfl) ⟨1071312, by rfl⟩ : syracuseStep 2856833 = 2142625) B2142625
theorem B1904555 : Blo 1903435 1904555 := bstep (se 1 (by rfl) ⟨1428416, by rfl⟩ : syracuseStep 1904555 = 2856833) B2856833
theorem B4820917 : Blo 1903435 4820917 := bbase (se 5 (by rfl) ⟨225980, by rfl⟩ : syracuseStep 4820917 = 451961) (by norm_num)
theorem B6427889 : Blo 1903435 6427889 := bstep (se 2 (by rfl) ⟨2410458, by rfl⟩ : syracuseStep 6427889 = 4820917) B4820917
theorem B4285259 : Blo 1903435 4285259 := bstep (se 1 (by rfl) ⟨3213944, by rfl⟩ : syracuseStep 4285259 = 6427889) B6427889
theorem B2856839 : Blo 1903435 2856839 := bstep (se 1 (by rfl) ⟨2142629, by rfl⟩ : syracuseStep 2856839 = 4285259) B4285259
theorem B1904559 : Blo 1903435 1904559 := bstep (se 1 (by rfl) ⟨1428419, by rfl⟩ : syracuseStep 1904559 = 2856839) B2856839
theorem B2856845 : Blo 1903435 2856845 := bbase (se 3 (by rfl) ⟨535658, by rfl⟩ : syracuseStep 2856845 = 1071317) (by norm_num)
theorem B1904563 : Blo 1903435 1904563 := bstep (se 1 (by rfl) ⟨1428422, by rfl⟩ : syracuseStep 1904563 = 2856845) B2856845
theorem B4285277 : Blo 1903435 4285277 := bbase (se 3 (by rfl) ⟨803489, by rfl⟩ : syracuseStep 4285277 = 1606979) (by norm_num)
theorem B2856851 : Blo 1903435 2856851 := bstep (se 1 (by rfl) ⟨2142638, by rfl⟩ : syracuseStep 2856851 = 4285277) B4285277
theorem B1904567 : Blo 1903435 1904567 := bstep (se 1 (by rfl) ⟨1428425, by rfl⟩ : syracuseStep 1904567 = 2856851) B2856851
theorem B3213965 : Blo 1903435 3213965 := bbase (se 3 (by rfl) ⟨602618, by rfl⟩ : syracuseStep 3213965 = 1205237) (by norm_num)
theorem B2142643 : Blo 1903435 2142643 := bstep (se 1 (by rfl) ⟨1606982, by rfl⟩ : syracuseStep 2142643 = 3213965) B3213965
theorem B2856857 : Blo 1903435 2856857 := bstep (se 2 (by rfl) ⟨1071321, by rfl⟩ : syracuseStep 2856857 = 2142643) B2142643
theorem B1904571 : Blo 1903435 1904571 := bstep (se 1 (by rfl) ⟨1428428, by rfl⟩ : syracuseStep 1904571 = 2856857) B2856857
theorem B6101525 : Blo 1903435 6101525 := bbase (se 6 (by rfl) ⟨143004, by rfl⟩ : syracuseStep 6101525 = 286009) (by norm_num)
theorem B16270733 : Blo 1903435 16270733 := bstep (se 3 (by rfl) ⟨3050762, by rfl⟩ : syracuseStep 16270733 = 6101525) B6101525
theorem B10847155 : Blo 1903435 10847155 := bstep (se 1 (by rfl) ⟨8135366, by rfl⟩ : syracuseStep 10847155 = 16270733) B16270733
theorem B14462873 : Blo 1903435 14462873 := bstep (se 2 (by rfl) ⟨5423577, by rfl⟩ : syracuseStep 14462873 = 10847155) B10847155
theorem B9641915 : Blo 1903435 9641915 := bstep (se 1 (by rfl) ⟨7231436, by rfl⟩ : syracuseStep 9641915 = 14462873) B14462873
theorem B6427943 : Blo 1903435 6427943 := bstep (se 1 (by rfl) ⟨4820957, by rfl⟩ : syracuseStep 6427943 = 9641915) B9641915
theorem B4285295 : Blo 1903435 4285295 := bstep (se 1 (by rfl) ⟨3213971, by rfl⟩ : syracuseStep 4285295 = 6427943) B6427943
theorem B2856863 : Blo 1903435 2856863 := bstep (se 1 (by rfl) ⟨2142647, by rfl⟩ : syracuseStep 2856863 = 4285295) B4285295
theorem B1904575 : Blo 1903435 1904575 := bstep (se 1 (by rfl) ⟨1428431, by rfl⟩ : syracuseStep 1904575 = 2856863) B2856863
theorem B2856869 : Blo 1903435 2856869 := bbase (se 4 (by rfl) ⟨267831, by rfl⟩ : syracuseStep 2856869 = 535663) (by norm_num)
theorem B1904579 : Blo 1903435 1904579 := bstep (se 1 (by rfl) ⟨1428434, by rfl⟩ : syracuseStep 1904579 = 2856869) B2856869
theorem B2410489 : Blo 1903435 2410489 := bbase (se 2 (by rfl) ⟨903933, by rfl⟩ : syracuseStep 2410489 = 1807867) (by norm_num)
theorem B3213985 : Blo 1903435 3213985 := bstep (se 2 (by rfl) ⟨1205244, by rfl⟩ : syracuseStep 3213985 = 2410489) B2410489
theorem B4285313 : Blo 1903435 4285313 := bstep (se 2 (by rfl) ⟨1606992, by rfl⟩ : syracuseStep 4285313 = 3213985) B3213985
theorem B2856875 : Blo 1903435 2856875 := bstep (se 1 (by rfl) ⟨2142656, by rfl⟩ : syracuseStep 2856875 = 4285313) B4285313
theorem B1904583 : Blo 1903435 1904583 := bstep (se 1 (by rfl) ⟨1428437, by rfl⟩ : syracuseStep 1904583 = 2856875) B2856875
theorem B2142661 : Blo 1903435 2142661 := bbase (se 4 (by rfl) ⟨200874, by rfl⟩ : syracuseStep 2142661 = 401749) (by norm_num)
theorem B2856881 : Blo 1903435 2856881 := bstep (se 2 (by rfl) ⟨1071330, by rfl⟩ : syracuseStep 2856881 = 2142661) B2142661
theorem B1904587 : Blo 1903435 1904587 := bstep (se 1 (by rfl) ⟨1428440, by rfl⟩ : syracuseStep 1904587 = 2856881) B2856881
theorem B3615749 : Blo 1903435 3615749 := bbase (se 4 (by rfl) ⟨338976, by rfl⟩ : syracuseStep 3615749 = 677953) (by norm_num)
theorem B2410499 : Blo 1903435 2410499 := bstep (se 1 (by rfl) ⟨1807874, by rfl⟩ : syracuseStep 2410499 = 3615749) B3615749
theorem B6427997 : Blo 1903435 6427997 := bstep (se 3 (by rfl) ⟨1205249, by rfl⟩ : syracuseStep 6427997 = 2410499) B2410499
theorem B4285331 : Blo 1903435 4285331 := bstep (se 1 (by rfl) ⟨3213998, by rfl⟩ : syracuseStep 4285331 = 6427997) B6427997
theorem B2856887 : Blo 1903435 2856887 := bstep (se 1 (by rfl) ⟨2142665, by rfl⟩ : syracuseStep 2856887 = 4285331) B4285331
theorem B1904591 : Blo 1903435 1904591 := bstep (se 1 (by rfl) ⟨1428443, by rfl⟩ : syracuseStep 1904591 = 2856887) B2856887
theorem B2856893 : Blo 1903435 2856893 := bbase (se 3 (by rfl) ⟨535667, by rfl⟩ : syracuseStep 2856893 = 1071335) (by norm_num)
theorem B1904595 : Blo 1903435 1904595 := bstep (se 1 (by rfl) ⟨1428446, by rfl⟩ : syracuseStep 1904595 = 2856893) B2856893
theorem B4285349 : Blo 1903435 4285349 := bbase (se 4 (by rfl) ⟨401751, by rfl⟩ : syracuseStep 4285349 = 803503) (by norm_num)
theorem B2856899 : Blo 1903435 2856899 := bstep (se 1 (by rfl) ⟨2142674, by rfl⟩ : syracuseStep 2856899 = 4285349) B4285349
theorem B1904599 : Blo 1903435 1904599 := bstep (se 1 (by rfl) ⟨1428449, by rfl⟩ : syracuseStep 1904599 = 2856899) B2856899
theorem B4821029 : Blo 1903435 4821029 := bbase (se 4 (by rfl) ⟨451971, by rfl⟩ : syracuseStep 4821029 = 903943) (by norm_num)
theorem B3214019 : Blo 1903435 3214019 := bstep (se 1 (by rfl) ⟨2410514, by rfl⟩ : syracuseStep 3214019 = 4821029) B4821029
theorem B2142679 : Blo 1903435 2142679 := bstep (se 1 (by rfl) ⟨1607009, by rfl⟩ : syracuseStep 2142679 = 3214019) B3214019
theorem B2856905 : Blo 1903435 2856905 := bstep (se 2 (by rfl) ⟨1071339, by rfl⟩ : syracuseStep 2856905 = 2142679) B2142679
theorem B1904603 : Blo 1903435 1904603 := bstep (se 1 (by rfl) ⟨1428452, by rfl⟩ : syracuseStep 1904603 = 2856905) B2856905
theorem B5423669 : Blo 1903435 5423669 := bbase (se 5 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 5423669 = 508469) (by norm_num)
theorem B3615779 : Blo 1903435 3615779 := bstep (se 1 (by rfl) ⟨2711834, by rfl⟩ : syracuseStep 3615779 = 5423669) B5423669
theorem B9642077 : Blo 1903435 9642077 := bstep (se 3 (by rfl) ⟨1807889, by rfl⟩ : syracuseStep 9642077 = 3615779) B3615779
theorem B6428051 : Blo 1903435 6428051 := bstep (se 1 (by rfl) ⟨4821038, by rfl⟩ : syracuseStep 6428051 = 9642077) B9642077
theorem B4285367 : Blo 1903435 4285367 := bstep (se 1 (by rfl) ⟨3214025, by rfl⟩ : syracuseStep 4285367 = 6428051) B6428051
theorem B2856911 : Blo 1903435 2856911 := bstep (se 1 (by rfl) ⟨2142683, by rfl⟩ : syracuseStep 2856911 = 4285367) B4285367
theorem B1904607 : Blo 1903435 1904607 := bstep (se 1 (by rfl) ⟨1428455, by rfl⟩ : syracuseStep 1904607 = 2856911) B2856911
theorem B2856917 : Blo 1903435 2856917 := bbase (se 7 (by rfl) ⟨33479, by rfl⟩ : syracuseStep 2856917 = 66959) (by norm_num)
theorem B1904611 : Blo 1903435 1904611 := bstep (se 1 (by rfl) ⟨1428458, by rfl⟩ : syracuseStep 1904611 = 2856917) B2856917
theorem B7231589 : Blo 1903435 7231589 := bbase (se 4 (by rfl) ⟨677961, by rfl⟩ : syracuseStep 7231589 = 1355923) (by norm_num)
theorem B4821059 : Blo 1903435 4821059 := bstep (se 1 (by rfl) ⟨3615794, by rfl⟩ : syracuseStep 4821059 = 7231589) B7231589
theorem B3214039 : Blo 1903435 3214039 := bstep (se 1 (by rfl) ⟨2410529, by rfl⟩ : syracuseStep 3214039 = 4821059) B4821059
theorem B4285385 : Blo 1903435 4285385 := bstep (se 2 (by rfl) ⟨1607019, by rfl⟩ : syracuseStep 4285385 = 3214039) B3214039
theorem B2856923 : Blo 1903435 2856923 := bstep (se 1 (by rfl) ⟨2142692, by rfl⟩ : syracuseStep 2856923 = 4285385) B4285385
theorem B1904615 : Blo 1903435 1904615 := bstep (se 1 (by rfl) ⟨1428461, by rfl⟩ : syracuseStep 1904615 = 2856923) B2856923
theorem B2142697 : Blo 1903435 2142697 := bbase (se 2 (by rfl) ⟨803511, by rfl⟩ : syracuseStep 2142697 = 1607023) (by norm_num)
theorem B2856929 : Blo 1903435 2856929 := bstep (se 2 (by rfl) ⟨1071348, by rfl⟩ : syracuseStep 2856929 = 2142697) B2142697
theorem B1904619 : Blo 1903435 1904619 := bstep (se 1 (by rfl) ⟨1428464, by rfl⟩ : syracuseStep 1904619 = 2856929) B2856929
theorem B2033893 : Blo 1903435 2033893 := bbase (se 4 (by rfl) ⟨190677, by rfl⟩ : syracuseStep 2033893 = 381355) (by norm_num)
theorem B10847429 : Blo 1903435 10847429 := bstep (se 4 (by rfl) ⟨1016946, by rfl⟩ : syracuseStep 10847429 = 2033893) B2033893
theorem B7231619 : Blo 1903435 7231619 := bstep (se 1 (by rfl) ⟨5423714, by rfl⟩ : syracuseStep 7231619 = 10847429) B10847429
theorem B4821079 : Blo 1903435 4821079 := bstep (se 1 (by rfl) ⟨3615809, by rfl⟩ : syracuseStep 4821079 = 7231619) B7231619
theorem B6428105 : Blo 1903435 6428105 := bstep (se 2 (by rfl) ⟨2410539, by rfl⟩ : syracuseStep 6428105 = 4821079) B4821079
theorem B4285403 : Blo 1903435 4285403 := bstep (se 1 (by rfl) ⟨3214052, by rfl⟩ : syracuseStep 4285403 = 6428105) B6428105
theorem B2856935 : Blo 1903435 2856935 := bstep (se 1 (by rfl) ⟨2142701, by rfl⟩ : syracuseStep 2856935 = 4285403) B4285403
theorem B1904623 : Blo 1903435 1904623 := bstep (se 1 (by rfl) ⟨1428467, by rfl⟩ : syracuseStep 1904623 = 2856935) B2856935
theorem B2856941 : Blo 1903435 2856941 := bbase (se 3 (by rfl) ⟨535676, by rfl⟩ : syracuseStep 2856941 = 1071353) (by norm_num)
theorem B1904627 : Blo 1903435 1904627 := bstep (se 1 (by rfl) ⟨1428470, by rfl⟩ : syracuseStep 1904627 = 2856941) B2856941
theorem B4285421 : Blo 1903435 4285421 := bbase (se 3 (by rfl) ⟨803516, by rfl⟩ : syracuseStep 4285421 = 1607033) (by norm_num)
theorem B2856947 : Blo 1903435 2856947 := bstep (se 1 (by rfl) ⟨2142710, by rfl⟩ : syracuseStep 2856947 = 4285421) B4285421
theorem B1904631 : Blo 1903435 1904631 := bstep (se 1 (by rfl) ⟨1428473, by rfl⟩ : syracuseStep 1904631 = 2856947) B2856947
theorem B4067813 : Blo 1903435 4067813 := bbase (se 4 (by rfl) ⟨381357, by rfl⟩ : syracuseStep 4067813 = 762715) (by norm_num)
theorem B2711875 : Blo 1903435 2711875 := bstep (se 1 (by rfl) ⟨2033906, by rfl⟩ : syracuseStep 2711875 = 4067813) B4067813
theorem B3615833 : Blo 1903435 3615833 := bstep (se 2 (by rfl) ⟨1355937, by rfl⟩ : syracuseStep 3615833 = 2711875) B2711875
theorem B2410555 : Blo 1903435 2410555 := bstep (se 1 (by rfl) ⟨1807916, by rfl⟩ : syracuseStep 2410555 = 3615833) B3615833
theorem B3214073 : Blo 1903435 3214073 := bstep (se 2 (by rfl) ⟨1205277, by rfl⟩ : syracuseStep 3214073 = 2410555) B2410555
theorem B2142715 : Blo 1903435 2142715 := bstep (se 1 (by rfl) ⟨1607036, by rfl⟩ : syracuseStep 2142715 = 3214073) B3214073
theorem B2856953 : Blo 1903435 2856953 := bstep (se 2 (by rfl) ⟨1071357, by rfl⟩ : syracuseStep 2856953 = 2142715) B2142715
theorem B1904635 : Blo 1903435 1904635 := bstep (se 1 (by rfl) ⟨1428476, by rfl⟩ : syracuseStep 1904635 = 2856953) B2856953
theorem B5791877 : Blo 1903435 5791877 := bbase (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) (by norm_num)
theorem B3861251 : Blo 1903435 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B164746709 : Blo 1903435 164746709 := bstep (se 7 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 164746709 = 3861251) B3861251
theorem B109831139 : Blo 1903435 109831139 := bstep (se 1 (by rfl) ⟨82373354, by rfl⟩ : syracuseStep 109831139 = 164746709) B164746709
theorem B73220759 : Blo 1903435 73220759 := bstep (se 1 (by rfl) ⟨54915569, by rfl⟩ : syracuseStep 73220759 = 109831139) B109831139
theorem B48813839 : Blo 1903435 48813839 := bstep (se 1 (by rfl) ⟨36610379, by rfl⟩ : syracuseStep 48813839 = 73220759) B73220759
theorem B32542559 : Blo 1903435 32542559 := bstep (se 1 (by rfl) ⟨24406919, by rfl⟩ : syracuseStep 32542559 = 48813839) B48813839
theorem B21695039 : Blo 1903435 21695039 := bstep (se 1 (by rfl) ⟨16271279, by rfl⟩ : syracuseStep 21695039 = 32542559) B32542559
theorem B14463359 : Blo 1903435 14463359 := bstep (se 1 (by rfl) ⟨10847519, by rfl⟩ : syracuseStep 14463359 = 21695039) B21695039
theorem B9642239 : Blo 1903435 9642239 := bstep (se 1 (by rfl) ⟨7231679, by rfl⟩ : syracuseStep 9642239 = 14463359) B14463359
theorem B6428159 : Blo 1903435 6428159 := bstep (se 1 (by rfl) ⟨4821119, by rfl⟩ : syracuseStep 6428159 = 9642239) B9642239
theorem B4285439 : Blo 1903435 4285439 := bstep (se 1 (by rfl) ⟨3214079, by rfl⟩ : syracuseStep 4285439 = 6428159) B6428159
theorem B2856959 : Blo 1903435 2856959 := bstep (se 1 (by rfl) ⟨2142719, by rfl⟩ : syracuseStep 2856959 = 4285439) B4285439
theorem B1904639 : Blo 1903435 1904639 := bstep (se 1 (by rfl) ⟨1428479, by rfl⟩ : syracuseStep 1904639 = 2856959) B2856959
theorem B2856965 : Blo 1903435 2856965 := bbase (se 4 (by rfl) ⟨267840, by rfl⟩ : syracuseStep 2856965 = 535681) (by norm_num)
theorem B1904643 : Blo 1903435 1904643 := bstep (se 1 (by rfl) ⟨1428482, by rfl⟩ : syracuseStep 1904643 = 2856965) B2856965
theorem B3214093 : Blo 1903435 3214093 := bbase (se 3 (by rfl) ⟨602642, by rfl⟩ : syracuseStep 3214093 = 1205285) (by norm_num)
theorem B4285457 : Blo 1903435 4285457 := bstep (se 2 (by rfl) ⟨1607046, by rfl⟩ : syracuseStep 4285457 = 3214093) B3214093
theorem B2856971 : Blo 1903435 2856971 := bstep (se 1 (by rfl) ⟨2142728, by rfl⟩ : syracuseStep 2856971 = 4285457) B4285457
theorem B1904647 : Blo 1903435 1904647 := bstep (se 1 (by rfl) ⟨1428485, by rfl⟩ : syracuseStep 1904647 = 2856971) B2856971
theorem B2142733 : Blo 1903435 2142733 := bbase (se 3 (by rfl) ⟨401762, by rfl⟩ : syracuseStep 2142733 = 803525) (by norm_num)
theorem B2856977 : Blo 1903435 2856977 := bstep (se 2 (by rfl) ⟨1071366, by rfl⟩ : syracuseStep 2856977 = 2142733) B2142733
theorem B1904651 : Blo 1903435 1904651 := bstep (se 1 (by rfl) ⟨1428488, by rfl⟩ : syracuseStep 1904651 = 2856977) B2856977
theorem B6428213 : Blo 1903435 6428213 := bbase (se 5 (by rfl) ⟨301322, by rfl⟩ : syracuseStep 6428213 = 602645) (by norm_num)
theorem B4285475 : Blo 1903435 4285475 := bstep (se 1 (by rfl) ⟨3214106, by rfl⟩ : syracuseStep 4285475 = 6428213) B6428213
theorem B2856983 : Blo 1903435 2856983 := bstep (se 1 (by rfl) ⟨2142737, by rfl⟩ : syracuseStep 2856983 = 4285475) B4285475
theorem B1904655 : Blo 1903435 1904655 := bstep (se 1 (by rfl) ⟨1428491, by rfl⟩ : syracuseStep 1904655 = 2856983) B2856983
theorem B2856989 : Blo 1903435 2856989 := bbase (se 3 (by rfl) ⟨535685, by rfl⟩ : syracuseStep 2856989 = 1071371) (by norm_num)
theorem B1904659 : Blo 1903435 1904659 := bstep (se 1 (by rfl) ⟨1428494, by rfl⟩ : syracuseStep 1904659 = 2856989) B2856989
theorem B4285493 : Blo 1903435 4285493 := bbase (se 5 (by rfl) ⟨200882, by rfl⟩ : syracuseStep 4285493 = 401765) (by norm_num)
theorem B2856995 : Blo 1903435 2856995 := bstep (se 1 (by rfl) ⟨2142746, by rfl⟩ : syracuseStep 2856995 = 4285493) B4285493
theorem B1904663 : Blo 1903435 1904663 := bstep (se 1 (by rfl) ⟨1428497, by rfl⟩ : syracuseStep 1904663 = 2856995) B2856995
theorem B35225941 : Blo 1903435 35225941 := bbase (se 10 (by rfl) ⟨51600, by rfl⟩ : syracuseStep 35225941 = 103201) (by norm_num)
theorem B46967921 : Blo 1903435 46967921 := bstep (se 2 (by rfl) ⟨17612970, by rfl⟩ : syracuseStep 46967921 = 35225941) B35225941
theorem B31311947 : Blo 1903435 31311947 := bstep (se 1 (by rfl) ⟨23483960, by rfl⟩ : syracuseStep 31311947 = 46967921) B46967921
theorem B20874631 : Blo 1903435 20874631 := bstep (se 1 (by rfl) ⟨15655973, by rfl⟩ : syracuseStep 20874631 = 31311947) B31311947
theorem B27832841 : Blo 1903435 27832841 := bstep (se 2 (by rfl) ⟨10437315, by rfl⟩ : syracuseStep 27832841 = 20874631) B20874631
theorem B18555227 : Blo 1903435 18555227 := bstep (se 1 (by rfl) ⟨13916420, by rfl⟩ : syracuseStep 18555227 = 27832841) B27832841
theorem B12370151 : Blo 1903435 12370151 := bstep (se 1 (by rfl) ⟨9277613, by rfl⟩ : syracuseStep 12370151 = 18555227) B18555227
theorem B8246767 : Blo 1903435 8246767 := bstep (se 1 (by rfl) ⟨6185075, by rfl⟩ : syracuseStep 8246767 = 12370151) B12370151
theorem B10995689 : Blo 1903435 10995689 := bstep (se 2 (by rfl) ⟨4123383, by rfl⟩ : syracuseStep 10995689 = 8246767) B8246767
theorem B7330459 : Blo 1903435 7330459 := bstep (se 1 (by rfl) ⟨5497844, by rfl⟩ : syracuseStep 7330459 = 10995689) B10995689
theorem B9773945 : Blo 1903435 9773945 := bstep (se 2 (by rfl) ⟨3665229, by rfl⟩ : syracuseStep 9773945 = 7330459) B7330459
theorem B6515963 : Blo 1903435 6515963 := bstep (se 1 (by rfl) ⟨4886972, by rfl⟩ : syracuseStep 6515963 = 9773945) B9773945
theorem B4343975 : Blo 1903435 4343975 := bstep (se 1 (by rfl) ⟨3257981, by rfl⟩ : syracuseStep 4343975 = 6515963) B6515963
theorem B2895983 : Blo 1903435 2895983 := bstep (se 1 (by rfl) ⟨2171987, by rfl⟩ : syracuseStep 2895983 = 4343975) B4343975
theorem B1930655 : Blo 1903435 1930655 := bstep (se 1 (by rfl) ⟨1447991, by rfl⟩ : syracuseStep 1930655 = 2895983) B2895983
theorem B5148413 : Blo 1903435 5148413 := bstep (se 3 (by rfl) ⟨965327, by rfl⟩ : syracuseStep 5148413 = 1930655) B1930655
theorem B3432275 : Blo 1903435 3432275 := bstep (se 1 (by rfl) ⟨2574206, by rfl⟩ : syracuseStep 3432275 = 5148413) B5148413
theorem B2288183 : Blo 1903435 2288183 := bstep (se 1 (by rfl) ⟨1716137, by rfl⟩ : syracuseStep 2288183 = 3432275) B3432275
theorem B6101821 : Blo 1903435 6101821 := bstep (se 3 (by rfl) ⟨1144091, by rfl⟩ : syracuseStep 6101821 = 2288183) B2288183
theorem B8135761 : Blo 1903435 8135761 := bstep (se 2 (by rfl) ⟨3050910, by rfl⟩ : syracuseStep 8135761 = 6101821) B6101821
theorem B10847681 : Blo 1903435 10847681 := bstep (se 2 (by rfl) ⟨4067880, by rfl⟩ : syracuseStep 10847681 = 8135761) B8135761
theorem B7231787 : Blo 1903435 7231787 := bstep (se 1 (by rfl) ⟨5423840, by rfl⟩ : syracuseStep 7231787 = 10847681) B10847681
theorem B4821191 : Blo 1903435 4821191 := bstep (se 1 (by rfl) ⟨3615893, by rfl⟩ : syracuseStep 4821191 = 7231787) B7231787
theorem B3214127 : Blo 1903435 3214127 := bstep (se 1 (by rfl) ⟨2410595, by rfl⟩ : syracuseStep 3214127 = 4821191) B4821191
theorem B2142751 : Blo 1903435 2142751 := bstep (se 1 (by rfl) ⟨1607063, by rfl⟩ : syracuseStep 2142751 = 3214127) B3214127
theorem B2857001 : Blo 1903435 2857001 := bstep (se 2 (by rfl) ⟨1071375, by rfl⟩ : syracuseStep 2857001 = 2142751) B2142751
theorem B1904667 : Blo 1903435 1904667 := bstep (se 1 (by rfl) ⟨1428500, by rfl⟩ : syracuseStep 1904667 = 2857001) B2857001
theorem B3861317 : Blo 1903435 3861317 := bbase (se 4 (by rfl) ⟨361998, by rfl⟩ : syracuseStep 3861317 = 723997) (by norm_num)
theorem B10296845 : Blo 1903435 10296845 := bstep (se 3 (by rfl) ⟨1930658, by rfl⟩ : syracuseStep 10296845 = 3861317) B3861317
theorem B6864563 : Blo 1903435 6864563 := bstep (se 1 (by rfl) ⟨5148422, by rfl⟩ : syracuseStep 6864563 = 10296845) B10296845
theorem B4576375 : Blo 1903435 4576375 := bstep (se 1 (by rfl) ⟨3432281, by rfl⟩ : syracuseStep 4576375 = 6864563) B6864563
theorem B6101833 : Blo 1903435 6101833 := bstep (se 2 (by rfl) ⟨2288187, by rfl⟩ : syracuseStep 6101833 = 4576375) B4576375
theorem B8135777 : Blo 1903435 8135777 := bstep (se 2 (by rfl) ⟨3050916, by rfl⟩ : syracuseStep 8135777 = 6101833) B6101833
theorem B5423851 : Blo 1903435 5423851 := bstep (se 1 (by rfl) ⟨4067888, by rfl⟩ : syracuseStep 5423851 = 8135777) B8135777
theorem B7231801 : Blo 1903435 7231801 := bstep (se 2 (by rfl) ⟨2711925, by rfl⟩ : syracuseStep 7231801 = 5423851) B5423851
theorem B9642401 : Blo 1903435 9642401 := bstep (se 2 (by rfl) ⟨3615900, by rfl⟩ : syracuseStep 9642401 = 7231801) B7231801
theorem B6428267 : Blo 1903435 6428267 := bstep (se 1 (by rfl) ⟨4821200, by rfl⟩ : syracuseStep 6428267 = 9642401) B9642401
theorem B4285511 : Blo 1903435 4285511 := bstep (se 1 (by rfl) ⟨3214133, by rfl⟩ : syracuseStep 4285511 = 6428267) B6428267
theorem B2857007 : Blo 1903435 2857007 := bstep (se 1 (by rfl) ⟨2142755, by rfl⟩ : syracuseStep 2857007 = 4285511) B4285511
theorem B1904671 : Blo 1903435 1904671 := bstep (se 1 (by rfl) ⟨1428503, by rfl⟩ : syracuseStep 1904671 = 2857007) B2857007
theorem B2857013 : Blo 1903435 2857013 := bbase (se 5 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 2857013 = 267845) (by norm_num)
theorem B1904675 : Blo 1903435 1904675 := bstep (se 1 (by rfl) ⟨1428506, by rfl⟩ : syracuseStep 1904675 = 2857013) B2857013
theorem B4821221 : Blo 1903435 4821221 := bbase (se 4 (by rfl) ⟨451989, by rfl⟩ : syracuseStep 4821221 = 903979) (by norm_num)
theorem B3214147 : Blo 1903435 3214147 := bstep (se 1 (by rfl) ⟨2410610, by rfl⟩ : syracuseStep 3214147 = 4821221) B4821221
theorem B4285529 : Blo 1903435 4285529 := bstep (se 2 (by rfl) ⟨1607073, by rfl⟩ : syracuseStep 4285529 = 3214147) B3214147
theorem B2857019 : Blo 1903435 2857019 := bstep (se 1 (by rfl) ⟨2142764, by rfl⟩ : syracuseStep 2857019 = 4285529) B4285529
theorem B1904679 : Blo 1903435 1904679 := bstep (se 1 (by rfl) ⟨1428509, by rfl⟩ : syracuseStep 1904679 = 2857019) B2857019
theorem B2142769 : Blo 1903435 2142769 := bbase (se 2 (by rfl) ⟨803538, by rfl⟩ : syracuseStep 2142769 = 1607077) (by norm_num)
theorem B2857025 : Blo 1903435 2857025 := bstep (se 2 (by rfl) ⟨1071384, by rfl⟩ : syracuseStep 2857025 = 2142769) B2142769
theorem B1904683 : Blo 1903435 1904683 := bstep (se 1 (by rfl) ⟨1428512, by rfl⟩ : syracuseStep 1904683 = 2857025) B2857025
theorem B2896013 : Blo 1903435 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B7722701 : Blo 1903435 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B5148467 : Blo 1903435 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B3432311 : Blo 1903435 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B2288207 : Blo 1903435 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B6101885 : Blo 1903435 6101885 := bstep (se 3 (by rfl) ⟨1144103, by rfl⟩ : syracuseStep 6101885 = 2288207) B2288207
theorem B4067923 : Blo 1903435 4067923 := bstep (se 1 (by rfl) ⟨3050942, by rfl⟩ : syracuseStep 4067923 = 6101885) B6101885
theorem B5423897 : Blo 1903435 5423897 := bstep (se 2 (by rfl) ⟨2033961, by rfl⟩ : syracuseStep 5423897 = 4067923) B4067923
theorem B3615931 : Blo 1903435 3615931 := bstep (se 1 (by rfl) ⟨2711948, by rfl⟩ : syracuseStep 3615931 = 5423897) B5423897
theorem B4821241 : Blo 1903435 4821241 := bstep (se 2 (by rfl) ⟨1807965, by rfl⟩ : syracuseStep 4821241 = 3615931) B3615931
theorem B6428321 : Blo 1903435 6428321 := bstep (se 2 (by rfl) ⟨2410620, by rfl⟩ : syracuseStep 6428321 = 4821241) B4821241
theorem B4285547 : Blo 1903435 4285547 := bstep (se 1 (by rfl) ⟨3214160, by rfl⟩ : syracuseStep 4285547 = 6428321) B6428321
theorem B2857031 : Blo 1903435 2857031 := bstep (se 1 (by rfl) ⟨2142773, by rfl⟩ : syracuseStep 2857031 = 4285547) B4285547
theorem B1904687 : Blo 1903435 1904687 := bstep (se 1 (by rfl) ⟨1428515, by rfl⟩ : syracuseStep 1904687 = 2857031) B2857031
theorem B2857037 : Blo 1903435 2857037 := bbase (se 3 (by rfl) ⟨535694, by rfl⟩ : syracuseStep 2857037 = 1071389) (by norm_num)
theorem B1904691 : Blo 1903435 1904691 := bstep (se 1 (by rfl) ⟨1428518, by rfl⟩ : syracuseStep 1904691 = 2857037) B2857037
theorem B4285565 : Blo 1903435 4285565 := bbase (se 3 (by rfl) ⟨803543, by rfl⟩ : syracuseStep 4285565 = 1607087) (by norm_num)
theorem B2857043 : Blo 1903435 2857043 := bstep (se 1 (by rfl) ⟨2142782, by rfl⟩ : syracuseStep 2857043 = 4285565) B4285565
theorem B1904695 : Blo 1903435 1904695 := bstep (se 1 (by rfl) ⟨1428521, by rfl⟩ : syracuseStep 1904695 = 2857043) B2857043
theorem B3214181 : Blo 1903435 3214181 := bbase (se 4 (by rfl) ⟨301329, by rfl⟩ : syracuseStep 3214181 = 602659) (by norm_num)
theorem B2142787 : Blo 1903435 2142787 := bstep (se 1 (by rfl) ⟨1607090, by rfl⟩ : syracuseStep 2142787 = 3214181) B3214181
theorem B2857049 : Blo 1903435 2857049 := bstep (se 2 (by rfl) ⟨1071393, by rfl⟩ : syracuseStep 2857049 = 2142787) B2142787
theorem B1904699 : Blo 1903435 1904699 := bstep (se 1 (by rfl) ⟨1428524, by rfl⟩ : syracuseStep 1904699 = 2857049) B2857049
theorem B4067957 : Blo 1903435 4067957 := bbase (se 5 (by rfl) ⟨190685, by rfl⟩ : syracuseStep 4067957 = 381371) (by norm_num)
theorem B2711971 : Blo 1903435 2711971 := bstep (se 1 (by rfl) ⟨2033978, by rfl⟩ : syracuseStep 2711971 = 4067957) B4067957
theorem B14463845 : Blo 1903435 14463845 := bstep (se 4 (by rfl) ⟨1355985, by rfl⟩ : syracuseStep 14463845 = 2711971) B2711971
theorem B9642563 : Blo 1903435 9642563 := bstep (se 1 (by rfl) ⟨7231922, by rfl⟩ : syracuseStep 9642563 = 14463845) B14463845
theorem B6428375 : Blo 1903435 6428375 := bstep (se 1 (by rfl) ⟨4821281, by rfl⟩ : syracuseStep 6428375 = 9642563) B9642563
theorem B4285583 : Blo 1903435 4285583 := bstep (se 1 (by rfl) ⟨3214187, by rfl⟩ : syracuseStep 4285583 = 6428375) B6428375
theorem B2857055 : Blo 1903435 2857055 := bstep (se 1 (by rfl) ⟨2142791, by rfl⟩ : syracuseStep 2857055 = 4285583) B4285583
theorem B1904703 : Blo 1903435 1904703 := bstep (se 1 (by rfl) ⟨1428527, by rfl⟩ : syracuseStep 1904703 = 2857055) B2857055
theorem B2857061 : Blo 1903435 2857061 := bbase (se 4 (by rfl) ⟨267849, by rfl⟩ : syracuseStep 2857061 = 535699) (by norm_num)
theorem B1904707 : Blo 1903435 1904707 := bstep (se 1 (by rfl) ⟨1428530, by rfl⟩ : syracuseStep 1904707 = 2857061) B2857061
theorem B6864709 : Blo 1903435 6864709 := bbase (se 4 (by rfl) ⟨643566, by rfl⟩ : syracuseStep 6864709 = 1287133) (by norm_num)
theorem B9152945 : Blo 1903435 9152945 := bstep (se 2 (by rfl) ⟨3432354, by rfl⟩ : syracuseStep 9152945 = 6864709) B6864709
theorem B6101963 : Blo 1903435 6101963 := bstep (se 1 (by rfl) ⟨4576472, by rfl⟩ : syracuseStep 6101963 = 9152945) B9152945
theorem B4067975 : Blo 1903435 4067975 := bstep (se 1 (by rfl) ⟨3050981, by rfl⟩ : syracuseStep 4067975 = 6101963) B6101963
theorem B2711983 : Blo 1903435 2711983 := bstep (se 1 (by rfl) ⟨2033987, by rfl⟩ : syracuseStep 2711983 = 4067975) B4067975
theorem B3615977 : Blo 1903435 3615977 := bstep (se 2 (by rfl) ⟨1355991, by rfl⟩ : syracuseStep 3615977 = 2711983) B2711983
theorem B2410651 : Blo 1903435 2410651 := bstep (se 1 (by rfl) ⟨1807988, by rfl⟩ : syracuseStep 2410651 = 3615977) B3615977
theorem B3214201 : Blo 1903435 3214201 := bstep (se 2 (by rfl) ⟨1205325, by rfl⟩ : syracuseStep 3214201 = 2410651) B2410651
theorem B4285601 : Blo 1903435 4285601 := bstep (se 2 (by rfl) ⟨1607100, by rfl⟩ : syracuseStep 4285601 = 3214201) B3214201
theorem B2857067 : Blo 1903435 2857067 := bstep (se 1 (by rfl) ⟨2142800, by rfl⟩ : syracuseStep 2857067 = 4285601) B4285601
theorem B1904711 : Blo 1903435 1904711 := bstep (se 1 (by rfl) ⟨1428533, by rfl⟩ : syracuseStep 1904711 = 2857067) B2857067
theorem B2142805 : Blo 1903435 2142805 := bbase (se 8 (by rfl) ⟨12555, by rfl⟩ : syracuseStep 2142805 = 25111) (by norm_num)
theorem B2857073 : Blo 1903435 2857073 := bstep (se 2 (by rfl) ⟨1071402, by rfl⟩ : syracuseStep 2857073 = 2142805) B2142805
theorem B1904715 : Blo 1903435 1904715 := bstep (se 1 (by rfl) ⟨1428536, by rfl⟩ : syracuseStep 1904715 = 2857073) B2857073
theorem B2410661 : Blo 1903435 2410661 := bbase (se 4 (by rfl) ⟨225999, by rfl⟩ : syracuseStep 2410661 = 451999) (by norm_num)
theorem B6428429 : Blo 1903435 6428429 := bstep (se 3 (by rfl) ⟨1205330, by rfl⟩ : syracuseStep 6428429 = 2410661) B2410661
theorem B4285619 : Blo 1903435 4285619 := bstep (se 1 (by rfl) ⟨3214214, by rfl⟩ : syracuseStep 4285619 = 6428429) B6428429
theorem B2857079 : Blo 1903435 2857079 := bstep (se 1 (by rfl) ⟨2142809, by rfl⟩ : syracuseStep 2857079 = 4285619) B4285619
theorem B1904719 : Blo 1903435 1904719 := bstep (se 1 (by rfl) ⟨1428539, by rfl⟩ : syracuseStep 1904719 = 2857079) B2857079
theorem B2857085 : Blo 1903435 2857085 := bbase (se 3 (by rfl) ⟨535703, by rfl⟩ : syracuseStep 2857085 = 1071407) (by norm_num)
theorem B1904723 : Blo 1903435 1904723 := bstep (se 1 (by rfl) ⟨1428542, by rfl⟩ : syracuseStep 1904723 = 2857085) B2857085
theorem B4285637 : Blo 1903435 4285637 := bbase (se 4 (by rfl) ⟨401778, by rfl⟩ : syracuseStep 4285637 = 803557) (by norm_num)
theorem B2857091 : Blo 1903435 2857091 := bstep (se 1 (by rfl) ⟨2142818, by rfl⟩ : syracuseStep 2857091 = 4285637) B4285637
theorem B1904727 : Blo 1903435 1904727 := bstep (se 1 (by rfl) ⟨1428545, by rfl⟩ : syracuseStep 1904727 = 2857091) B2857091
theorem B12204053 : Blo 1903435 12204053 := bbase (se 6 (by rfl) ⟨286032, by rfl⟩ : syracuseStep 12204053 = 572065) (by norm_num)
theorem B8136035 : Blo 1903435 8136035 := bstep (se 1 (by rfl) ⟨6102026, by rfl⟩ : syracuseStep 8136035 = 12204053) B12204053
theorem B5424023 : Blo 1903435 5424023 := bstep (se 1 (by rfl) ⟨4068017, by rfl⟩ : syracuseStep 5424023 = 8136035) B8136035
theorem B3616015 : Blo 1903435 3616015 := bstep (se 1 (by rfl) ⟨2712011, by rfl⟩ : syracuseStep 3616015 = 5424023) B5424023
theorem B4821353 : Blo 1903435 4821353 := bstep (se 2 (by rfl) ⟨1808007, by rfl⟩ : syracuseStep 4821353 = 3616015) B3616015
theorem B3214235 : Blo 1903435 3214235 := bstep (se 1 (by rfl) ⟨2410676, by rfl⟩ : syracuseStep 3214235 = 4821353) B4821353
theorem B2142823 : Blo 1903435 2142823 := bstep (se 1 (by rfl) ⟨1607117, by rfl⟩ : syracuseStep 2142823 = 3214235) B3214235
theorem B2857097 : Blo 1903435 2857097 := bstep (se 2 (by rfl) ⟨1071411, by rfl⟩ : syracuseStep 2857097 = 2142823) B2142823
theorem B1904731 : Blo 1903435 1904731 := bstep (se 1 (by rfl) ⟨1428548, by rfl⟩ : syracuseStep 1904731 = 2857097) B2857097
theorem B9642725 : Blo 1903435 9642725 := bbase (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) (by norm_num)
theorem B6428483 : Blo 1903435 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B4285655 : Blo 1903435 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B2857103 : Blo 1903435 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B1904735 : Blo 1903435 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B2857109 : Blo 1903435 2857109 := bbase (se 6 (by rfl) ⟨66963, by rfl⟩ : syracuseStep 2857109 = 133927) (by norm_num)
theorem B1904739 : Blo 1903435 1904739 := bstep (se 1 (by rfl) ⟨1428554, by rfl⟩ : syracuseStep 1904739 = 2857109) B2857109
theorem B8136085 : Blo 1903435 8136085 := bbase (se 6 (by rfl) ⟨190689, by rfl⟩ : syracuseStep 8136085 = 381379) (by norm_num)
theorem B10848113 : Blo 1903435 10848113 := bstep (se 2 (by rfl) ⟨4068042, by rfl⟩ : syracuseStep 10848113 = 8136085) B8136085
theorem B7232075 : Blo 1903435 7232075 := bstep (se 1 (by rfl) ⟨5424056, by rfl⟩ : syracuseStep 7232075 = 10848113) B10848113
theorem B4821383 : Blo 1903435 4821383 := bstep (se 1 (by rfl) ⟨3616037, by rfl⟩ : syracuseStep 4821383 = 7232075) B7232075
theorem B3214255 : Blo 1903435 3214255 := bstep (se 1 (by rfl) ⟨2410691, by rfl⟩ : syracuseStep 3214255 = 4821383) B4821383
theorem B4285673 : Blo 1903435 4285673 := bstep (se 2 (by rfl) ⟨1607127, by rfl⟩ : syracuseStep 4285673 = 3214255) B3214255
theorem B2857115 : Blo 1903435 2857115 := bstep (se 1 (by rfl) ⟨2142836, by rfl⟩ : syracuseStep 2857115 = 4285673) B4285673
theorem B1904743 : Blo 1903435 1904743 := bstep (se 1 (by rfl) ⟨1428557, by rfl⟩ : syracuseStep 1904743 = 2857115) B2857115
theorem B2142841 : Blo 1903435 2142841 := bbase (se 2 (by rfl) ⟨803565, by rfl⟩ : syracuseStep 2142841 = 1607131) (by norm_num)
theorem B2857121 : Blo 1903435 2857121 := bstep (se 2 (by rfl) ⟨1071420, by rfl⟩ : syracuseStep 2857121 = 2142841) B2142841
theorem B1904747 : Blo 1903435 1904747 := bstep (se 1 (by rfl) ⟨1428560, by rfl⟩ : syracuseStep 1904747 = 2857121) B2857121
theorem B14661557 : Blo 1903435 14661557 := bbase (se 5 (by rfl) ⟨687260, by rfl⟩ : syracuseStep 14661557 = 1374521) (by norm_num)
theorem B9774371 : Blo 1903435 9774371 := bstep (se 1 (by rfl) ⟨7330778, by rfl⟩ : syracuseStep 9774371 = 14661557) B14661557
theorem B6516247 : Blo 1903435 6516247 := bstep (se 1 (by rfl) ⟨4887185, by rfl⟩ : syracuseStep 6516247 = 9774371) B9774371
theorem B8688329 : Blo 1903435 8688329 := bstep (se 2 (by rfl) ⟨3258123, by rfl⟩ : syracuseStep 8688329 = 6516247) B6516247
theorem B5792219 : Blo 1903435 5792219 := bstep (se 1 (by rfl) ⟨4344164, by rfl⟩ : syracuseStep 5792219 = 8688329) B8688329
theorem B3861479 : Blo 1903435 3861479 := bstep (se 1 (by rfl) ⟨2896109, by rfl⟩ : syracuseStep 3861479 = 5792219) B5792219
theorem B10297277 : Blo 1903435 10297277 := bstep (se 3 (by rfl) ⟨1930739, by rfl⟩ : syracuseStep 10297277 = 3861479) B3861479
theorem B6864851 : Blo 1903435 6864851 := bstep (se 1 (by rfl) ⟨5148638, by rfl⟩ : syracuseStep 6864851 = 10297277) B10297277
theorem B18306269 : Blo 1903435 18306269 := bstep (se 3 (by rfl) ⟨3432425, by rfl⟩ : syracuseStep 18306269 = 6864851) B6864851
theorem B12204179 : Blo 1903435 12204179 := bstep (se 1 (by rfl) ⟨9153134, by rfl⟩ : syracuseStep 12204179 = 18306269) B18306269
theorem B8136119 : Blo 1903435 8136119 := bstep (se 1 (by rfl) ⟨6102089, by rfl⟩ : syracuseStep 8136119 = 12204179) B12204179
theorem B5424079 : Blo 1903435 5424079 := bstep (se 1 (by rfl) ⟨4068059, by rfl⟩ : syracuseStep 5424079 = 8136119) B8136119
theorem B7232105 : Blo 1903435 7232105 := bstep (se 2 (by rfl) ⟨2712039, by rfl⟩ : syracuseStep 7232105 = 5424079) B5424079
theorem B4821403 : Blo 1903435 4821403 := bstep (se 1 (by rfl) ⟨3616052, by rfl⟩ : syracuseStep 4821403 = 7232105) B7232105
theorem B6428537 : Blo 1903435 6428537 := bstep (se 2 (by rfl) ⟨2410701, by rfl⟩ : syracuseStep 6428537 = 4821403) B4821403
theorem B4285691 : Blo 1903435 4285691 := bstep (se 1 (by rfl) ⟨3214268, by rfl⟩ : syracuseStep 4285691 = 6428537) B6428537
theorem B2857127 : Blo 1903435 2857127 := bstep (se 1 (by rfl) ⟨2142845, by rfl⟩ : syracuseStep 2857127 = 4285691) B4285691
theorem B1904751 : Blo 1903435 1904751 := bstep (se 1 (by rfl) ⟨1428563, by rfl⟩ : syracuseStep 1904751 = 2857127) B2857127
theorem B2857133 : Blo 1903435 2857133 := bbase (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) (by norm_num)
theorem B1904755 : Blo 1903435 1904755 := bstep (se 1 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 1904755 = 2857133) B2857133
theorem B4285709 : Blo 1903435 4285709 := bbase (se 3 (by rfl) ⟨803570, by rfl⟩ : syracuseStep 4285709 = 1607141) (by norm_num)
theorem B2857139 : Blo 1903435 2857139 := bstep (se 1 (by rfl) ⟨2142854, by rfl⟩ : syracuseStep 2857139 = 4285709) B4285709
theorem B1904759 : Blo 1903435 1904759 := bstep (se 1 (by rfl) ⟨1428569, by rfl⟩ : syracuseStep 1904759 = 2857139) B2857139
theorem B2410717 : Blo 1903435 2410717 := bbase (se 3 (by rfl) ⟨452009, by rfl⟩ : syracuseStep 2410717 = 904019) (by norm_num)
theorem B3214289 : Blo 1903435 3214289 := bstep (se 2 (by rfl) ⟨1205358, by rfl⟩ : syracuseStep 3214289 = 2410717) B2410717
theorem B2142859 : Blo 1903435 2142859 := bstep (se 1 (by rfl) ⟨1607144, by rfl⟩ : syracuseStep 2142859 = 3214289) B3214289
theorem B2857145 : Blo 1903435 2857145 := bstep (se 2 (by rfl) ⟨1071429, by rfl⟩ : syracuseStep 2857145 = 2142859) B2142859
theorem B1904763 : Blo 1903435 1904763 := bstep (se 1 (by rfl) ⟨1428572, by rfl⟩ : syracuseStep 1904763 = 2857145) B2857145
theorem B16272373 : Blo 1903435 16272373 := bbase (se 5 (by rfl) ⟨762767, by rfl⟩ : syracuseStep 16272373 = 1525535) (by norm_num)
theorem B21696497 : Blo 1903435 21696497 := bstep (se 2 (by rfl) ⟨8136186, by rfl⟩ : syracuseStep 21696497 = 16272373) B16272373
theorem B14464331 : Blo 1903435 14464331 := bstep (se 1 (by rfl) ⟨10848248, by rfl⟩ : syracuseStep 14464331 = 21696497) B21696497
theorem B9642887 : Blo 1903435 9642887 := bstep (se 1 (by rfl) ⟨7232165, by rfl⟩ : syracuseStep 9642887 = 14464331) B14464331
theorem B6428591 : Blo 1903435 6428591 := bstep (se 1 (by rfl) ⟨4821443, by rfl⟩ : syracuseStep 6428591 = 9642887) B9642887
theorem B4285727 : Blo 1903435 4285727 := bstep (se 1 (by rfl) ⟨3214295, by rfl⟩ : syracuseStep 4285727 = 6428591) B6428591
theorem B2857151 : Blo 1903435 2857151 := bstep (se 1 (by rfl) ⟨2142863, by rfl⟩ : syracuseStep 2857151 = 4285727) B4285727
theorem B1904767 : Blo 1903435 1904767 := bstep (se 1 (by rfl) ⟨1428575, by rfl⟩ : syracuseStep 1904767 = 2857151) B2857151
theorem B2857157 : Blo 1903435 2857157 := bbase (se 4 (by rfl) ⟨267858, by rfl⟩ : syracuseStep 2857157 = 535717) (by norm_num)
theorem B1904771 : Blo 1903435 1904771 := bstep (se 1 (by rfl) ⟨1428578, by rfl⟩ : syracuseStep 1904771 = 2857157) B2857157
theorem B3214309 : Blo 1903435 3214309 := bbase (se 4 (by rfl) ⟨301341, by rfl⟩ : syracuseStep 3214309 = 602683) (by norm_num)
theorem B4285745 : Blo 1903435 4285745 := bstep (se 2 (by rfl) ⟨1607154, by rfl⟩ : syracuseStep 4285745 = 3214309) B3214309
theorem B2857163 : Blo 1903435 2857163 := bstep (se 1 (by rfl) ⟨2142872, by rfl⟩ : syracuseStep 2857163 = 4285745) B4285745
theorem B1904775 : Blo 1903435 1904775 := bstep (se 1 (by rfl) ⟨1428581, by rfl⟩ : syracuseStep 1904775 = 2857163) B2857163
theorem B2142877 : Blo 1903435 2142877 := bbase (se 3 (by rfl) ⟨401789, by rfl⟩ : syracuseStep 2142877 = 803579) (by norm_num)
theorem B2857169 : Blo 1903435 2857169 := bstep (se 2 (by rfl) ⟨1071438, by rfl⟩ : syracuseStep 2857169 = 2142877) B2142877
theorem B1904779 : Blo 1903435 1904779 := bstep (se 1 (by rfl) ⟨1428584, by rfl⟩ : syracuseStep 1904779 = 2857169) B2857169
theorem B6428645 : Blo 1903435 6428645 := bbase (se 4 (by rfl) ⟨602685, by rfl⟩ : syracuseStep 6428645 = 1205371) (by norm_num)
theorem B4285763 : Blo 1903435 4285763 := bstep (se 1 (by rfl) ⟨3214322, by rfl⟩ : syracuseStep 4285763 = 6428645) B6428645
theorem B2857175 : Blo 1903435 2857175 := bstep (se 1 (by rfl) ⟨2142881, by rfl⟩ : syracuseStep 2857175 = 4285763) B4285763
theorem B1904783 : Blo 1903435 1904783 := bstep (se 1 (by rfl) ⟨1428587, by rfl⟩ : syracuseStep 1904783 = 2857175) B2857175
theorem B2857181 : Blo 1903435 2857181 := bbase (se 3 (by rfl) ⟨535721, by rfl⟩ : syracuseStep 2857181 = 1071443) (by norm_num)
theorem B1904787 : Blo 1903435 1904787 := bstep (se 1 (by rfl) ⟨1428590, by rfl⟩ : syracuseStep 1904787 = 2857181) B2857181
theorem B4285781 : Blo 1903435 4285781 := bbase (se 12 (by rfl) ⟨1569, by rfl⟩ : syracuseStep 4285781 = 3139) (by norm_num)
theorem B2857187 : Blo 1903435 2857187 := bstep (se 1 (by rfl) ⟨2142890, by rfl⟩ : syracuseStep 2857187 = 4285781) B4285781
theorem B1904791 : Blo 1903435 1904791 := bstep (se 1 (by rfl) ⟨1428593, by rfl⟩ : syracuseStep 1904791 = 2857187) B2857187
theorem B2034077 : Blo 1903435 2034077 := bbase (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) (by norm_num)
theorem B5424205 : Blo 1903435 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B7232273 : Blo 1903435 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B4821515 : Blo 1903435 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B3214343 : Blo 1903435 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B2142895 : Blo 1903435 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B2857193 : Blo 1903435 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B1904795 : Blo 1903435 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B12370997 : Blo 1903435 12370997 := bbase (se 5 (by rfl) ⟨579890, by rfl⟩ : syracuseStep 12370997 = 1159781) (by norm_num)
theorem B8247331 : Blo 1903435 8247331 := bstep (se 1 (by rfl) ⟨6185498, by rfl⟩ : syracuseStep 8247331 = 12370997) B12370997
theorem B10996441 : Blo 1903435 10996441 := bstep (se 2 (by rfl) ⟨4123665, by rfl⟩ : syracuseStep 10996441 = 8247331) B8247331
theorem B58647685 : Blo 1903435 58647685 := bstep (se 4 (by rfl) ⟨5498220, by rfl⟩ : syracuseStep 58647685 = 10996441) B10996441
theorem B78196913 : Blo 1903435 78196913 := bstep (se 2 (by rfl) ⟨29323842, by rfl⟩ : syracuseStep 78196913 = 58647685) B58647685
theorem B52131275 : Blo 1903435 52131275 := bstep (se 1 (by rfl) ⟨39098456, by rfl⟩ : syracuseStep 52131275 = 78196913) B78196913
theorem B34754183 : Blo 1903435 34754183 := bstep (se 1 (by rfl) ⟨26065637, by rfl⟩ : syracuseStep 34754183 = 52131275) B52131275
theorem B23169455 : Blo 1903435 23169455 := bstep (se 1 (by rfl) ⟨17377091, by rfl⟩ : syracuseStep 23169455 = 34754183) B34754183
theorem B15446303 : Blo 1903435 15446303 := bstep (se 1 (by rfl) ⟨11584727, by rfl⟩ : syracuseStep 15446303 = 23169455) B23169455
theorem B10297535 : Blo 1903435 10297535 := bstep (se 1 (by rfl) ⟨7723151, by rfl⟩ : syracuseStep 10297535 = 15446303) B15446303
theorem B27460093 : Blo 1903435 27460093 := bstep (se 3 (by rfl) ⟨5148767, by rfl⟩ : syracuseStep 27460093 = 10297535) B10297535
theorem B36613457 : Blo 1903435 36613457 := bstep (se 2 (by rfl) ⟨13730046, by rfl⟩ : syracuseStep 36613457 = 27460093) B27460093
theorem B24408971 : Blo 1903435 24408971 := bstep (se 1 (by rfl) ⟨18306728, by rfl⟩ : syracuseStep 24408971 = 36613457) B36613457
theorem B16272647 : Blo 1903435 16272647 := bstep (se 1 (by rfl) ⟨12204485, by rfl⟩ : syracuseStep 16272647 = 24408971) B24408971
theorem B10848431 : Blo 1903435 10848431 := bstep (se 1 (by rfl) ⟨8136323, by rfl⟩ : syracuseStep 10848431 = 16272647) B16272647
theorem B7232287 : Blo 1903435 7232287 := bstep (se 1 (by rfl) ⟨5424215, by rfl⟩ : syracuseStep 7232287 = 10848431) B10848431
theorem B9643049 : Blo 1903435 9643049 := bstep (se 2 (by rfl) ⟨3616143, by rfl⟩ : syracuseStep 9643049 = 7232287) B7232287
theorem B6428699 : Blo 1903435 6428699 := bstep (se 1 (by rfl) ⟨4821524, by rfl⟩ : syracuseStep 6428699 = 9643049) B9643049
theorem B4285799 : Blo 1903435 4285799 := bstep (se 1 (by rfl) ⟨3214349, by rfl⟩ : syracuseStep 4285799 = 6428699) B6428699
theorem B2857199 : Blo 1903435 2857199 := bstep (se 1 (by rfl) ⟨2142899, by rfl⟩ : syracuseStep 2857199 = 4285799) B4285799
theorem B1904799 : Blo 1903435 1904799 := bstep (se 1 (by rfl) ⟨1428599, by rfl⟩ : syracuseStep 1904799 = 2857199) B2857199
theorem B2857205 : Blo 1903435 2857205 := bbase (se 5 (by rfl) ⟨133931, by rfl⟩ : syracuseStep 2857205 = 267863) (by norm_num)
theorem B1904803 : Blo 1903435 1904803 := bstep (se 1 (by rfl) ⟨1428602, by rfl⟩ : syracuseStep 1904803 = 2857205) B2857205
theorem B23169557 : Blo 1903435 23169557 := bbase (se 6 (by rfl) ⟨543036, by rfl⟩ : syracuseStep 23169557 = 1086073) (by norm_num)
theorem B15446371 : Blo 1903435 15446371 := bstep (se 1 (by rfl) ⟨11584778, by rfl⟩ : syracuseStep 15446371 = 23169557) B23169557
theorem B20595161 : Blo 1903435 20595161 := bstep (se 2 (by rfl) ⟨7723185, by rfl⟩ : syracuseStep 20595161 = 15446371) B15446371
theorem B13730107 : Blo 1903435 13730107 := bstep (se 1 (by rfl) ⟨10297580, by rfl⟩ : syracuseStep 13730107 = 20595161) B20595161
theorem B18306809 : Blo 1903435 18306809 := bstep (se 2 (by rfl) ⟨6865053, by rfl⟩ : syracuseStep 18306809 = 13730107) B13730107
theorem B12204539 : Blo 1903435 12204539 := bstep (se 1 (by rfl) ⟨9153404, by rfl⟩ : syracuseStep 12204539 = 18306809) B18306809
theorem B8136359 : Blo 1903435 8136359 := bstep (se 1 (by rfl) ⟨6102269, by rfl⟩ : syracuseStep 8136359 = 12204539) B12204539
theorem B5424239 : Blo 1903435 5424239 := bstep (se 1 (by rfl) ⟨4068179, by rfl⟩ : syracuseStep 5424239 = 8136359) B8136359
theorem B3616159 : Blo 1903435 3616159 := bstep (se 1 (by rfl) ⟨2712119, by rfl⟩ : syracuseStep 3616159 = 5424239) B5424239
theorem B4821545 : Blo 1903435 4821545 := bstep (se 2 (by rfl) ⟨1808079, by rfl⟩ : syracuseStep 4821545 = 3616159) B3616159
theorem B3214363 : Blo 1903435 3214363 := bstep (se 1 (by rfl) ⟨2410772, by rfl⟩ : syracuseStep 3214363 = 4821545) B4821545
theorem B4285817 : Blo 1903435 4285817 := bstep (se 2 (by rfl) ⟨1607181, by rfl⟩ : syracuseStep 4285817 = 3214363) B3214363
theorem B2857211 : Blo 1903435 2857211 := bstep (se 1 (by rfl) ⟨2142908, by rfl⟩ : syracuseStep 2857211 = 4285817) B4285817
theorem B1904807 : Blo 1903435 1904807 := bstep (se 1 (by rfl) ⟨1428605, by rfl⟩ : syracuseStep 1904807 = 2857211) B2857211
theorem B2142913 : Blo 1903435 2142913 := bbase (se 2 (by rfl) ⟨803592, by rfl⟩ : syracuseStep 2142913 = 1607185) (by norm_num)
theorem B2857217 : Blo 1903435 2857217 := bstep (se 2 (by rfl) ⟨1071456, by rfl⟩ : syracuseStep 2857217 = 2142913) B2142913
theorem B1904811 : Blo 1903435 1904811 := bstep (se 1 (by rfl) ⟨1428608, by rfl⟩ : syracuseStep 1904811 = 2857217) B2857217
theorem B4821565 : Blo 1903435 4821565 := bbase (se 3 (by rfl) ⟨904043, by rfl⟩ : syracuseStep 4821565 = 1808087) (by norm_num)
theorem B6428753 : Blo 1903435 6428753 := bstep (se 2 (by rfl) ⟨2410782, by rfl⟩ : syracuseStep 6428753 = 4821565) B4821565
theorem B4285835 : Blo 1903435 4285835 := bstep (se 1 (by rfl) ⟨3214376, by rfl⟩ : syracuseStep 4285835 = 6428753) B6428753
theorem B2857223 : Blo 1903435 2857223 := bstep (se 1 (by rfl) ⟨2142917, by rfl⟩ : syracuseStep 2857223 = 4285835) B4285835
theorem B1904815 : Blo 1903435 1904815 := bstep (se 1 (by rfl) ⟨1428611, by rfl⟩ : syracuseStep 1904815 = 2857223) B2857223
theorem B2857229 : Blo 1903435 2857229 := bbase (se 3 (by rfl) ⟨535730, by rfl⟩ : syracuseStep 2857229 = 1071461) (by norm_num)
theorem B1904819 : Blo 1903435 1904819 := bstep (se 1 (by rfl) ⟨1428614, by rfl⟩ : syracuseStep 1904819 = 2857229) B2857229
theorem B4285853 : Blo 1903435 4285853 := bbase (se 3 (by rfl) ⟨803597, by rfl⟩ : syracuseStep 4285853 = 1607195) (by norm_num)
theorem B2857235 : Blo 1903435 2857235 := bstep (se 1 (by rfl) ⟨2142926, by rfl⟩ : syracuseStep 2857235 = 4285853) B4285853
theorem B1904823 : Blo 1903435 1904823 := bstep (se 1 (by rfl) ⟨1428617, by rfl⟩ : syracuseStep 1904823 = 2857235) B2857235
theorem B3214397 : Blo 1903435 3214397 := bbase (se 3 (by rfl) ⟨602699, by rfl⟩ : syracuseStep 3214397 = 1205399) (by norm_num)
theorem B2142931 : Blo 1903435 2142931 := bstep (se 1 (by rfl) ⟨1607198, by rfl⟩ : syracuseStep 2142931 = 3214397) B3214397
theorem B2857241 : Blo 1903435 2857241 := bstep (se 2 (by rfl) ⟨1071465, by rfl⟩ : syracuseStep 2857241 = 2142931) B2142931
theorem B1904827 : Blo 1903435 1904827 := bstep (se 1 (by rfl) ⟨1428620, by rfl⟩ : syracuseStep 1904827 = 2857241) B2857241
theorem B3051173 : Blo 1903435 3051173 := bbase (se 4 (by rfl) ⟨286047, by rfl⟩ : syracuseStep 3051173 = 572095) (by norm_num)
theorem B2034115 : Blo 1903435 2034115 := bstep (se 1 (by rfl) ⟨1525586, by rfl⟩ : syracuseStep 2034115 = 3051173) B3051173
theorem B10848613 : Blo 1903435 10848613 := bstep (se 4 (by rfl) ⟨1017057, by rfl⟩ : syracuseStep 10848613 = 2034115) B2034115
theorem B14464817 : Blo 1903435 14464817 := bstep (se 2 (by rfl) ⟨5424306, by rfl⟩ : syracuseStep 14464817 = 10848613) B10848613
theorem B9643211 : Blo 1903435 9643211 := bstep (se 1 (by rfl) ⟨7232408, by rfl⟩ : syracuseStep 9643211 = 14464817) B14464817
theorem B6428807 : Blo 1903435 6428807 := bstep (se 1 (by rfl) ⟨4821605, by rfl⟩ : syracuseStep 6428807 = 9643211) B9643211
theorem B4285871 : Blo 1903435 4285871 := bstep (se 1 (by rfl) ⟨3214403, by rfl⟩ : syracuseStep 4285871 = 6428807) B6428807
theorem B2857247 : Blo 1903435 2857247 := bstep (se 1 (by rfl) ⟨2142935, by rfl⟩ : syracuseStep 2857247 = 4285871) B4285871
theorem B1904831 : Blo 1903435 1904831 := bstep (se 1 (by rfl) ⟨1428623, by rfl⟩ : syracuseStep 1904831 = 2857247) B2857247
theorem B2857253 : Blo 1903435 2857253 := bbase (se 4 (by rfl) ⟨267867, by rfl⟩ : syracuseStep 2857253 = 535735) (by norm_num)
theorem B1904835 : Blo 1903435 1904835 := bstep (se 1 (by rfl) ⟨1428626, by rfl⟩ : syracuseStep 1904835 = 2857253) B2857253
theorem B2410813 : Blo 1903435 2410813 := bbase (se 3 (by rfl) ⟨452027, by rfl⟩ : syracuseStep 2410813 = 904055) (by norm_num)
theorem B3214417 : Blo 1903435 3214417 := bstep (se 2 (by rfl) ⟨1205406, by rfl⟩ : syracuseStep 3214417 = 2410813) B2410813
theorem B4285889 : Blo 1903435 4285889 := bstep (se 2 (by rfl) ⟨1607208, by rfl⟩ : syracuseStep 4285889 = 3214417) B3214417
theorem B2857259 : Blo 1903435 2857259 := bstep (se 1 (by rfl) ⟨2142944, by rfl⟩ : syracuseStep 2857259 = 4285889) B4285889
theorem B1904839 : Blo 1903435 1904839 := bstep (se 1 (by rfl) ⟨1428629, by rfl⟩ : syracuseStep 1904839 = 2857259) B2857259
theorem B2142949 : Blo 1903435 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B2857265 : Blo 1903435 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B1904843 : Blo 1903435 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B2749181 : Blo 1903435 2749181 := bbase (se 3 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 2749181 = 1030943) (by norm_num)
theorem B7331149 : Blo 1903435 7331149 := bstep (se 3 (by rfl) ⟨1374590, by rfl⟩ : syracuseStep 7331149 = 2749181) B2749181
theorem B9774865 : Blo 1903435 9774865 := bstep (se 2 (by rfl) ⟨3665574, by rfl⟩ : syracuseStep 9774865 = 7331149) B7331149
theorem B13033153 : Blo 1903435 13033153 := bstep (se 2 (by rfl) ⟨4887432, by rfl⟩ : syracuseStep 13033153 = 9774865) B9774865
theorem B17377537 : Blo 1903435 17377537 := bstep (se 2 (by rfl) ⟨6516576, by rfl⟩ : syracuseStep 17377537 = 13033153) B13033153
theorem B23170049 : Blo 1903435 23170049 := bstep (se 2 (by rfl) ⟨8688768, by rfl⟩ : syracuseStep 23170049 = 17377537) B17377537
theorem B15446699 : Blo 1903435 15446699 := bstep (se 1 (by rfl) ⟨11585024, by rfl⟩ : syracuseStep 15446699 = 23170049) B23170049
theorem B10297799 : Blo 1903435 10297799 := bstep (se 1 (by rfl) ⟨7723349, by rfl⟩ : syracuseStep 10297799 = 15446699) B15446699
theorem B6865199 : Blo 1903435 6865199 := bstep (se 1 (by rfl) ⟨5148899, by rfl⟩ : syracuseStep 6865199 = 10297799) B10297799
theorem B4576799 : Blo 1903435 4576799 := bstep (se 1 (by rfl) ⟨3432599, by rfl⟩ : syracuseStep 4576799 = 6865199) B6865199
theorem B3051199 : Blo 1903435 3051199 := bstep (se 1 (by rfl) ⟨2288399, by rfl⟩ : syracuseStep 3051199 = 4576799) B4576799
theorem B4068265 : Blo 1903435 4068265 := bstep (se 2 (by rfl) ⟨1525599, by rfl⟩ : syracuseStep 4068265 = 3051199) B3051199
theorem B5424353 : Blo 1903435 5424353 := bstep (se 2 (by rfl) ⟨2034132, by rfl⟩ : syracuseStep 5424353 = 4068265) B4068265
theorem B3616235 : Blo 1903435 3616235 := bstep (se 1 (by rfl) ⟨2712176, by rfl⟩ : syracuseStep 3616235 = 5424353) B5424353
theorem B2410823 : Blo 1903435 2410823 := bstep (se 1 (by rfl) ⟨1808117, by rfl⟩ : syracuseStep 2410823 = 3616235) B3616235
theorem B6428861 : Blo 1903435 6428861 := bstep (se 3 (by rfl) ⟨1205411, by rfl⟩ : syracuseStep 6428861 = 2410823) B2410823
theorem B4285907 : Blo 1903435 4285907 := bstep (se 1 (by rfl) ⟨3214430, by rfl⟩ : syracuseStep 4285907 = 6428861) B6428861
theorem B2857271 : Blo 1903435 2857271 := bstep (se 1 (by rfl) ⟨2142953, by rfl⟩ : syracuseStep 2857271 = 4285907) B4285907
theorem B1904847 : Blo 1903435 1904847 := bstep (se 1 (by rfl) ⟨1428635, by rfl⟩ : syracuseStep 1904847 = 2857271) B2857271
theorem B2857277 : Blo 1903435 2857277 := bbase (se 3 (by rfl) ⟨535739, by rfl⟩ : syracuseStep 2857277 = 1071479) (by norm_num)
theorem B1904851 : Blo 1903435 1904851 := bstep (se 1 (by rfl) ⟨1428638, by rfl⟩ : syracuseStep 1904851 = 2857277) B2857277
theorem B4285925 : Blo 1903435 4285925 := bbase (se 4 (by rfl) ⟨401805, by rfl⟩ : syracuseStep 4285925 = 803611) (by norm_num)
theorem B2857283 : Blo 1903435 2857283 := bstep (se 1 (by rfl) ⟨2142962, by rfl⟩ : syracuseStep 2857283 = 4285925) B4285925
theorem B1904855 : Blo 1903435 1904855 := bstep (se 1 (by rfl) ⟨1428641, by rfl⟩ : syracuseStep 1904855 = 2857283) B2857283
theorem B4821677 : Blo 1903435 4821677 := bbase (se 3 (by rfl) ⟨904064, by rfl⟩ : syracuseStep 4821677 = 1808129) (by norm_num)
theorem B3214451 : Blo 1903435 3214451 := bstep (se 1 (by rfl) ⟨2410838, by rfl⟩ : syracuseStep 3214451 = 4821677) B4821677
theorem B2142967 : Blo 1903435 2142967 := bstep (se 1 (by rfl) ⟨1607225, by rfl⟩ : syracuseStep 2142967 = 3214451) B3214451
theorem B2857289 : Blo 1903435 2857289 := bstep (se 2 (by rfl) ⟨1071483, by rfl⟩ : syracuseStep 2857289 = 2142967) B2142967
theorem B1904859 : Blo 1903435 1904859 := bstep (se 1 (by rfl) ⟨1428644, by rfl⟩ : syracuseStep 1904859 = 2857289) B2857289
theorem B4576837 : Blo 1903435 4576837 := bbase (se 4 (by rfl) ⟨429078, by rfl⟩ : syracuseStep 4576837 = 858157) (by norm_num)
theorem B6102449 : Blo 1903435 6102449 := bstep (se 2 (by rfl) ⟨2288418, by rfl⟩ : syracuseStep 6102449 = 4576837) B4576837
theorem B4068299 : Blo 1903435 4068299 := bstep (se 1 (by rfl) ⟨3051224, by rfl⟩ : syracuseStep 4068299 = 6102449) B6102449
theorem B2712199 : Blo 1903435 2712199 := bstep (se 1 (by rfl) ⟨2034149, by rfl⟩ : syracuseStep 2712199 = 4068299) B4068299
theorem B3616265 : Blo 1903435 3616265 := bstep (se 2 (by rfl) ⟨1356099, by rfl⟩ : syracuseStep 3616265 = 2712199) B2712199
theorem B9643373 : Blo 1903435 9643373 := bstep (se 3 (by rfl) ⟨1808132, by rfl⟩ : syracuseStep 9643373 = 3616265) B3616265
theorem B6428915 : Blo 1903435 6428915 := bstep (se 1 (by rfl) ⟨4821686, by rfl⟩ : syracuseStep 6428915 = 9643373) B9643373
theorem B4285943 : Blo 1903435 4285943 := bstep (se 1 (by rfl) ⟨3214457, by rfl⟩ : syracuseStep 4285943 = 6428915) B6428915
theorem B2857295 : Blo 1903435 2857295 := bstep (se 1 (by rfl) ⟨2142971, by rfl⟩ : syracuseStep 2857295 = 4285943) B4285943
theorem B1904863 : Blo 1903435 1904863 := bstep (se 1 (by rfl) ⟨1428647, by rfl⟩ : syracuseStep 1904863 = 2857295) B2857295
theorem B2857301 : Blo 1903435 2857301 := bbase (se 10 (by rfl) ⟨4185, by rfl⟩ : syracuseStep 2857301 = 8371) (by norm_num)
theorem B1904867 : Blo 1903435 1904867 := bstep (se 1 (by rfl) ⟨1428650, by rfl⟩ : syracuseStep 1904867 = 2857301) B2857301
theorem B5424421 : Blo 1903435 5424421 := bbase (se 4 (by rfl) ⟨508539, by rfl⟩ : syracuseStep 5424421 = 1017079) (by norm_num)
theorem B7232561 : Blo 1903435 7232561 := bstep (se 2 (by rfl) ⟨2712210, by rfl⟩ : syracuseStep 7232561 = 5424421) B5424421
theorem B4821707 : Blo 1903435 4821707 := bstep (se 1 (by rfl) ⟨3616280, by rfl⟩ : syracuseStep 4821707 = 7232561) B7232561
theorem B3214471 : Blo 1903435 3214471 := bstep (se 1 (by rfl) ⟨2410853, by rfl⟩ : syracuseStep 3214471 = 4821707) B4821707
theorem B4285961 : Blo 1903435 4285961 := bstep (se 2 (by rfl) ⟨1607235, by rfl⟩ : syracuseStep 4285961 = 3214471) B3214471
theorem B2857307 : Blo 1903435 2857307 := bstep (se 1 (by rfl) ⟨2142980, by rfl⟩ : syracuseStep 2857307 = 4285961) B4285961
theorem B1904871 : Blo 1903435 1904871 := bstep (se 1 (by rfl) ⟨1428653, by rfl⟩ : syracuseStep 1904871 = 2857307) B2857307
theorem B2142985 : Blo 1903435 2142985 := bbase (se 2 (by rfl) ⟨803619, by rfl⟩ : syracuseStep 2142985 = 1607239) (by norm_num)
theorem B2857313 : Blo 1903435 2857313 := bstep (se 2 (by rfl) ⟨1071492, by rfl⟩ : syracuseStep 2857313 = 2142985) B2142985
theorem B1904875 : Blo 1903435 1904875 := bstep (se 1 (by rfl) ⟨1428656, by rfl⟩ : syracuseStep 1904875 = 2857313) B2857313
theorem B9153749 : Blo 1903435 9153749 := bbase (se 7 (by rfl) ⟨107270, by rfl⟩ : syracuseStep 9153749 = 214541) (by norm_num)
theorem B24409997 : Blo 1903435 24409997 := bstep (se 3 (by rfl) ⟨4576874, by rfl⟩ : syracuseStep 24409997 = 9153749) B9153749
theorem B16273331 : Blo 1903435 16273331 := bstep (se 1 (by rfl) ⟨12204998, by rfl⟩ : syracuseStep 16273331 = 24409997) B24409997
theorem B10848887 : Blo 1903435 10848887 := bstep (se 1 (by rfl) ⟨8136665, by rfl⟩ : syracuseStep 10848887 = 16273331) B16273331
theorem B7232591 : Blo 1903435 7232591 := bstep (se 1 (by rfl) ⟨5424443, by rfl⟩ : syracuseStep 7232591 = 10848887) B10848887
theorem B4821727 : Blo 1903435 4821727 := bstep (se 1 (by rfl) ⟨3616295, by rfl⟩ : syracuseStep 4821727 = 7232591) B7232591
theorem B6428969 : Blo 1903435 6428969 := bstep (se 2 (by rfl) ⟨2410863, by rfl⟩ : syracuseStep 6428969 = 4821727) B4821727
theorem B4285979 : Blo 1903435 4285979 := bstep (se 1 (by rfl) ⟨3214484, by rfl⟩ : syracuseStep 4285979 = 6428969) B6428969
theorem B2857319 : Blo 1903435 2857319 := bstep (se 1 (by rfl) ⟨2142989, by rfl⟩ : syracuseStep 2857319 = 4285979) B4285979
theorem B1904879 : Blo 1903435 1904879 := bstep (se 1 (by rfl) ⟨1428659, by rfl⟩ : syracuseStep 1904879 = 2857319) B2857319
theorem B2857325 : Blo 1903435 2857325 := bbase (se 3 (by rfl) ⟨535748, by rfl⟩ : syracuseStep 2857325 = 1071497) (by norm_num)
theorem B1904883 : Blo 1903435 1904883 := bstep (se 1 (by rfl) ⟨1428662, by rfl⟩ : syracuseStep 1904883 = 2857325) B2857325
theorem B4285997 : Blo 1903435 4285997 := bbase (se 3 (by rfl) ⟨803624, by rfl⟩ : syracuseStep 4285997 = 1607249) (by norm_num)
theorem B2857331 : Blo 1903435 2857331 := bstep (se 1 (by rfl) ⟨2142998, by rfl⟩ : syracuseStep 2857331 = 4285997) B4285997
theorem B1904887 : Blo 1903435 1904887 := bstep (se 1 (by rfl) ⟨1428665, by rfl⟩ : syracuseStep 1904887 = 2857331) B2857331
theorem B2574509 : Blo 1903435 2574509 := bbase (se 3 (by rfl) ⟨482720, by rfl⟩ : syracuseStep 2574509 = 965441) (by norm_num)
theorem B27461429 : Blo 1903435 27461429 := bstep (se 5 (by rfl) ⟨1287254, by rfl⟩ : syracuseStep 27461429 = 2574509) B2574509
theorem B18307619 : Blo 1903435 18307619 := bstep (se 1 (by rfl) ⟨13730714, by rfl⟩ : syracuseStep 18307619 = 27461429) B27461429
theorem B12205079 : Blo 1903435 12205079 := bstep (se 1 (by rfl) ⟨9153809, by rfl⟩ : syracuseStep 12205079 = 18307619) B18307619
theorem B8136719 : Blo 1903435 8136719 := bstep (se 1 (by rfl) ⟨6102539, by rfl⟩ : syracuseStep 8136719 = 12205079) B12205079
theorem B5424479 : Blo 1903435 5424479 := bstep (se 1 (by rfl) ⟨4068359, by rfl⟩ : syracuseStep 5424479 = 8136719) B8136719
theorem B3616319 : Blo 1903435 3616319 := bstep (se 1 (by rfl) ⟨2712239, by rfl⟩ : syracuseStep 3616319 = 5424479) B5424479
theorem B2410879 : Blo 1903435 2410879 := bstep (se 1 (by rfl) ⟨1808159, by rfl⟩ : syracuseStep 2410879 = 3616319) B3616319
theorem B3214505 : Blo 1903435 3214505 := bstep (se 2 (by rfl) ⟨1205439, by rfl⟩ : syracuseStep 3214505 = 2410879) B2410879
theorem B2143003 : Blo 1903435 2143003 := bstep (se 1 (by rfl) ⟨1607252, by rfl⟩ : syracuseStep 2143003 = 3214505) B3214505
theorem B2857337 : Blo 1903435 2857337 := bstep (se 2 (by rfl) ⟨1071501, by rfl⟩ : syracuseStep 2857337 = 2143003) B2143003
theorem B1904891 : Blo 1903435 1904891 := bstep (se 1 (by rfl) ⟨1428668, by rfl⟩ : syracuseStep 1904891 = 2857337) B2857337
theorem B3432685 : Blo 1903435 3432685 := bbase (se 3 (by rfl) ⟨643628, by rfl⟩ : syracuseStep 3432685 = 1287257) (by norm_num)
theorem B4576913 : Blo 1903435 4576913 := bstep (se 2 (by rfl) ⟨1716342, by rfl⟩ : syracuseStep 4576913 = 3432685) B3432685
theorem B3051275 : Blo 1903435 3051275 := bstep (se 1 (by rfl) ⟨2288456, by rfl⟩ : syracuseStep 3051275 = 4576913) B4576913
theorem B32546933 : Blo 1903435 32546933 := bstep (se 5 (by rfl) ⟨1525637, by rfl⟩ : syracuseStep 32546933 = 3051275) B3051275
theorem B21697955 : Blo 1903435 21697955 := bstep (se 1 (by rfl) ⟨16273466, by rfl⟩ : syracuseStep 21697955 = 32546933) B32546933
theorem B14465303 : Blo 1903435 14465303 := bstep (se 1 (by rfl) ⟨10848977, by rfl⟩ : syracuseStep 14465303 = 21697955) B21697955
theorem B9643535 : Blo 1903435 9643535 := bstep (se 1 (by rfl) ⟨7232651, by rfl⟩ : syracuseStep 9643535 = 14465303) B14465303
theorem B6429023 : Blo 1903435 6429023 := bstep (se 1 (by rfl) ⟨4821767, by rfl⟩ : syracuseStep 6429023 = 9643535) B9643535
theorem B4286015 : Blo 1903435 4286015 := bstep (se 1 (by rfl) ⟨3214511, by rfl⟩ : syracuseStep 4286015 = 6429023) B6429023
theorem B2857343 : Blo 1903435 2857343 := bstep (se 1 (by rfl) ⟨2143007, by rfl⟩ : syracuseStep 2857343 = 4286015) B4286015
theorem B1904895 : Blo 1903435 1904895 := bstep (se 1 (by rfl) ⟨1428671, by rfl⟩ : syracuseStep 1904895 = 2857343) B2857343
theorem B2857349 : Blo 1903435 2857349 := bbase (se 4 (by rfl) ⟨267876, by rfl⟩ : syracuseStep 2857349 = 535753) (by norm_num)
theorem B1904899 : Blo 1903435 1904899 := bstep (se 1 (by rfl) ⟨1428674, by rfl⟩ : syracuseStep 1904899 = 2857349) B2857349
theorem B3214525 : Blo 1903435 3214525 := bbase (se 3 (by rfl) ⟨602723, by rfl⟩ : syracuseStep 3214525 = 1205447) (by norm_num)
theorem B4286033 : Blo 1903435 4286033 := bstep (se 2 (by rfl) ⟨1607262, by rfl⟩ : syracuseStep 4286033 = 3214525) B3214525
theorem B2857355 : Blo 1903435 2857355 := bstep (se 1 (by rfl) ⟨2143016, by rfl⟩ : syracuseStep 2857355 = 4286033) B4286033
theorem B1904903 : Blo 1903435 1904903 := bstep (se 1 (by rfl) ⟨1428677, by rfl⟩ : syracuseStep 1904903 = 2857355) B2857355
theorem B2143021 : Blo 1903435 2143021 := bbase (se 3 (by rfl) ⟨401816, by rfl⟩ : syracuseStep 2143021 = 803633) (by norm_num)
theorem B2857361 : Blo 1903435 2857361 := bstep (se 2 (by rfl) ⟨1071510, by rfl⟩ : syracuseStep 2857361 = 2143021) B2143021
theorem B1904907 : Blo 1903435 1904907 := bstep (se 1 (by rfl) ⟨1428680, by rfl⟩ : syracuseStep 1904907 = 2857361) B2857361
theorem B6429077 : Blo 1903435 6429077 := bbase (se 6 (by rfl) ⟨150681, by rfl⟩ : syracuseStep 6429077 = 301363) (by norm_num)
theorem B4286051 : Blo 1903435 4286051 := bstep (se 1 (by rfl) ⟨3214538, by rfl⟩ : syracuseStep 4286051 = 6429077) B6429077
theorem B2857367 : Blo 1903435 2857367 := bstep (se 1 (by rfl) ⟨2143025, by rfl⟩ : syracuseStep 2857367 = 4286051) B4286051
theorem B1904911 : Blo 1903435 1904911 := bstep (se 1 (by rfl) ⟨1428683, by rfl⟩ : syracuseStep 1904911 = 2857367) B2857367
theorem B2857373 : Blo 1903435 2857373 := bbase (se 3 (by rfl) ⟨535757, by rfl⟩ : syracuseStep 2857373 = 1071515) (by norm_num)
theorem B1904915 : Blo 1903435 1904915 := bstep (se 1 (by rfl) ⟨1428686, by rfl⟩ : syracuseStep 1904915 = 2857373) B2857373
theorem B4286069 : Blo 1903435 4286069 := bbase (se 5 (by rfl) ⟨200909, by rfl⟩ : syracuseStep 4286069 = 401819) (by norm_num)
theorem B2857379 : Blo 1903435 2857379 := bstep (se 1 (by rfl) ⟨2143034, by rfl⟩ : syracuseStep 2857379 = 4286069) B4286069
theorem B1904919 : Blo 1903435 1904919 := bstep (se 1 (by rfl) ⟨1428689, by rfl⟩ : syracuseStep 1904919 = 2857379) B2857379
theorem B4576981 : Blo 1903435 4576981 := bbase (se 7 (by rfl) ⟨53636, by rfl⟩ : syracuseStep 4576981 = 107273) (by norm_num)
theorem B6102641 : Blo 1903435 6102641 := bstep (se 2 (by rfl) ⟨2288490, by rfl⟩ : syracuseStep 6102641 = 4576981) B4576981
theorem B16273709 : Blo 1903435 16273709 := bstep (se 3 (by rfl) ⟨3051320, by rfl⟩ : syracuseStep 16273709 = 6102641) B6102641
theorem B10849139 : Blo 1903435 10849139 := bstep (se 1 (by rfl) ⟨8136854, by rfl⟩ : syracuseStep 10849139 = 16273709) B16273709
theorem B7232759 : Blo 1903435 7232759 := bstep (se 1 (by rfl) ⟨5424569, by rfl⟩ : syracuseStep 7232759 = 10849139) B10849139
theorem B4821839 : Blo 1903435 4821839 := bstep (se 1 (by rfl) ⟨3616379, by rfl⟩ : syracuseStep 4821839 = 7232759) B7232759
theorem B3214559 : Blo 1903435 3214559 := bstep (se 1 (by rfl) ⟨2410919, by rfl⟩ : syracuseStep 3214559 = 4821839) B4821839
theorem B2143039 : Blo 1903435 2143039 := bstep (se 1 (by rfl) ⟨1607279, by rfl⟩ : syracuseStep 2143039 = 3214559) B3214559
theorem B2857385 : Blo 1903435 2857385 := bstep (se 2 (by rfl) ⟨1071519, by rfl⟩ : syracuseStep 2857385 = 2143039) B2143039
theorem B1904923 : Blo 1903435 1904923 := bstep (se 1 (by rfl) ⟨1428692, by rfl⟩ : syracuseStep 1904923 = 2857385) B2857385
theorem B7232773 : Blo 1903435 7232773 := bbase (se 4 (by rfl) ⟨678072, by rfl⟩ : syracuseStep 7232773 = 1356145) (by norm_num)
theorem B9643697 : Blo 1903435 9643697 := bstep (se 2 (by rfl) ⟨3616386, by rfl⟩ : syracuseStep 9643697 = 7232773) B7232773
theorem B6429131 : Blo 1903435 6429131 := bstep (se 1 (by rfl) ⟨4821848, by rfl⟩ : syracuseStep 6429131 = 9643697) B9643697
theorem B4286087 : Blo 1903435 4286087 := bstep (se 1 (by rfl) ⟨3214565, by rfl⟩ : syracuseStep 4286087 = 6429131) B6429131
theorem B2857391 : Blo 1903435 2857391 := bstep (se 1 (by rfl) ⟨2143043, by rfl⟩ : syracuseStep 2857391 = 4286087) B4286087
theorem B1904927 : Blo 1903435 1904927 := bstep (se 1 (by rfl) ⟨1428695, by rfl⟩ : syracuseStep 1904927 = 2857391) B2857391
theorem B2857397 : Blo 1903435 2857397 := bbase (se 5 (by rfl) ⟨133940, by rfl⟩ : syracuseStep 2857397 = 267881) (by norm_num)
theorem B1904931 : Blo 1903435 1904931 := bstep (se 1 (by rfl) ⟨1428698, by rfl⟩ : syracuseStep 1904931 = 2857397) B2857397
theorem B4821869 : Blo 1903435 4821869 := bbase (se 3 (by rfl) ⟨904100, by rfl⟩ : syracuseStep 4821869 = 1808201) (by norm_num)
theorem B3214579 : Blo 1903435 3214579 := bstep (se 1 (by rfl) ⟨2410934, by rfl⟩ : syracuseStep 3214579 = 4821869) B4821869
theorem B4286105 : Blo 1903435 4286105 := bstep (se 2 (by rfl) ⟨1607289, by rfl⟩ : syracuseStep 4286105 = 3214579) B3214579
theorem B2857403 : Blo 1903435 2857403 := bstep (se 1 (by rfl) ⟨2143052, by rfl⟩ : syracuseStep 2857403 = 4286105) B4286105
theorem B1904935 : Blo 1903435 1904935 := bstep (se 1 (by rfl) ⟨1428701, by rfl⟩ : syracuseStep 1904935 = 2857403) B2857403
theorem B2143057 : Blo 1903435 2143057 := bbase (se 2 (by rfl) ⟨803646, by rfl⟩ : syracuseStep 2143057 = 1607293) (by norm_num)
theorem B2857409 : Blo 1903435 2857409 := bstep (se 2 (by rfl) ⟨1071528, by rfl⟩ : syracuseStep 2857409 = 2143057) B2143057
theorem B1904939 : Blo 1903435 1904939 := bstep (se 1 (by rfl) ⟨1428704, by rfl⟩ : syracuseStep 1904939 = 2857409) B2857409
theorem B3432773 : Blo 1903435 3432773 := bbase (se 4 (by rfl) ⟨321822, by rfl⟩ : syracuseStep 3432773 = 643645) (by norm_num)
theorem B2288515 : Blo 1903435 2288515 := bstep (se 1 (by rfl) ⟨1716386, by rfl⟩ : syracuseStep 2288515 = 3432773) B3432773
theorem B3051353 : Blo 1903435 3051353 := bstep (se 2 (by rfl) ⟨1144257, by rfl⟩ : syracuseStep 3051353 = 2288515) B2288515
theorem B2034235 : Blo 1903435 2034235 := bstep (se 1 (by rfl) ⟨1525676, by rfl⟩ : syracuseStep 2034235 = 3051353) B3051353
theorem B2712313 : Blo 1903435 2712313 := bstep (se 2 (by rfl) ⟨1017117, by rfl⟩ : syracuseStep 2712313 = 2034235) B2034235
theorem B3616417 : Blo 1903435 3616417 := bstep (se 2 (by rfl) ⟨1356156, by rfl⟩ : syracuseStep 3616417 = 2712313) B2712313
theorem B4821889 : Blo 1903435 4821889 := bstep (se 2 (by rfl) ⟨1808208, by rfl⟩ : syracuseStep 4821889 = 3616417) B3616417
theorem B6429185 : Blo 1903435 6429185 := bstep (se 2 (by rfl) ⟨2410944, by rfl⟩ : syracuseStep 6429185 = 4821889) B4821889
theorem B4286123 : Blo 1903435 4286123 := bstep (se 1 (by rfl) ⟨3214592, by rfl⟩ : syracuseStep 4286123 = 6429185) B6429185
theorem B2857415 : Blo 1903435 2857415 := bstep (se 1 (by rfl) ⟨2143061, by rfl⟩ : syracuseStep 2857415 = 4286123) B4286123
theorem B1904943 : Blo 1903435 1904943 := bstep (se 1 (by rfl) ⟨1428707, by rfl⟩ : syracuseStep 1904943 = 2857415) B2857415
theorem B2857421 : Blo 1903435 2857421 := bbase (se 3 (by rfl) ⟨535766, by rfl⟩ : syracuseStep 2857421 = 1071533) (by norm_num)
theorem B1904947 : Blo 1903435 1904947 := bstep (se 1 (by rfl) ⟨1428710, by rfl⟩ : syracuseStep 1904947 = 2857421) B2857421
theorem B4286141 : Blo 1903435 4286141 := bbase (se 3 (by rfl) ⟨803651, by rfl⟩ : syracuseStep 4286141 = 1607303) (by norm_num)
theorem B2857427 : Blo 1903435 2857427 := bstep (se 1 (by rfl) ⟨2143070, by rfl⟩ : syracuseStep 2857427 = 4286141) B4286141
theorem B1904951 : Blo 1903435 1904951 := bstep (se 1 (by rfl) ⟨1428713, by rfl⟩ : syracuseStep 1904951 = 2857427) B2857427
theorem B3214613 : Blo 1903435 3214613 := bbase (se 6 (by rfl) ⟨75342, by rfl⟩ : syracuseStep 3214613 = 150685) (by norm_num)
theorem B2143075 : Blo 1903435 2143075 := bstep (se 1 (by rfl) ⟨1607306, by rfl⟩ : syracuseStep 2143075 = 3214613) B3214613
theorem B2857433 : Blo 1903435 2857433 := bstep (se 2 (by rfl) ⟨1071537, by rfl⟩ : syracuseStep 2857433 = 2143075) B2143075
theorem B1904955 : Blo 1903435 1904955 := bstep (se 1 (by rfl) ⟨1428716, by rfl⟩ : syracuseStep 1904955 = 2857433) B2857433
theorem B2383489 : Blo 1903435 2383489 := bbase (se 2 (by rfl) ⟨893808, by rfl⟩ : syracuseStep 2383489 = 1787617) (by norm_num)
theorem B12711941 : Blo 1903435 12711941 := bstep (se 4 (by rfl) ⟨1191744, by rfl⟩ : syracuseStep 12711941 = 2383489) B2383489
theorem B8474627 : Blo 1903435 8474627 := bstep (se 1 (by rfl) ⟨6355970, by rfl⟩ : syracuseStep 8474627 = 12711941) B12711941
theorem B5649751 : Blo 1903435 5649751 := bstep (se 1 (by rfl) ⟨4237313, by rfl⟩ : syracuseStep 5649751 = 8474627) B8474627
theorem B7533001 : Blo 1903435 7533001 := bstep (se 2 (by rfl) ⟨2824875, by rfl⟩ : syracuseStep 7533001 = 5649751) B5649751
theorem B10044001 : Blo 1903435 10044001 := bstep (se 2 (by rfl) ⟨3766500, by rfl⟩ : syracuseStep 10044001 = 7533001) B7533001
theorem B13392001 : Blo 1903435 13392001 := bstep (se 2 (by rfl) ⟨5022000, by rfl⟩ : syracuseStep 13392001 = 10044001) B10044001
theorem B17856001 : Blo 1903435 17856001 := bstep (se 2 (by rfl) ⟨6696000, by rfl⟩ : syracuseStep 17856001 = 13392001) B13392001
theorem B23808001 : Blo 1903435 23808001 := bstep (se 2 (by rfl) ⟨8928000, by rfl⟩ : syracuseStep 23808001 = 17856001) B17856001
theorem B31744001 : Blo 1903435 31744001 := bstep (se 2 (by rfl) ⟨11904000, by rfl⟩ : syracuseStep 31744001 = 23808001) B23808001
theorem B21162667 : Blo 1903435 21162667 := bstep (se 1 (by rfl) ⟨15872000, by rfl⟩ : syracuseStep 21162667 = 31744001) B31744001
theorem B28216889 : Blo 1903435 28216889 := bstep (se 2 (by rfl) ⟨10581333, by rfl⟩ : syracuseStep 28216889 = 21162667) B21162667
theorem B18811259 : Blo 1903435 18811259 := bstep (se 1 (by rfl) ⟨14108444, by rfl⟩ : syracuseStep 18811259 = 28216889) B28216889
theorem B12540839 : Blo 1903435 12540839 := bstep (se 1 (by rfl) ⟨9405629, by rfl⟩ : syracuseStep 12540839 = 18811259) B18811259
theorem B33442237 : Blo 1903435 33442237 := bstep (se 3 (by rfl) ⟨6270419, by rfl⟩ : syracuseStep 33442237 = 12540839) B12540839
theorem B44589649 : Blo 1903435 44589649 := bstep (se 2 (by rfl) ⟨16721118, by rfl⟩ : syracuseStep 44589649 = 33442237) B33442237
theorem B59452865 : Blo 1903435 59452865 := bstep (se 2 (by rfl) ⟨22294824, by rfl⟩ : syracuseStep 59452865 = 44589649) B44589649
theorem B39635243 : Blo 1903435 39635243 := bstep (se 1 (by rfl) ⟨29726432, by rfl⟩ : syracuseStep 39635243 = 59452865) B59452865
theorem B26423495 : Blo 1903435 26423495 := bstep (se 1 (by rfl) ⟨19817621, by rfl⟩ : syracuseStep 26423495 = 39635243) B39635243
theorem B17615663 : Blo 1903435 17615663 := bstep (se 1 (by rfl) ⟨13211747, by rfl⟩ : syracuseStep 17615663 = 26423495) B26423495
theorem B11743775 : Blo 1903435 11743775 := bstep (se 1 (by rfl) ⟨8807831, by rfl⟩ : syracuseStep 11743775 = 17615663) B17615663
theorem B7829183 : Blo 1903435 7829183 := bstep (se 1 (by rfl) ⟨5871887, by rfl⟩ : syracuseStep 7829183 = 11743775) B11743775
theorem B20877821 : Blo 1903435 20877821 := bstep (se 3 (by rfl) ⟨3914591, by rfl⟩ : syracuseStep 20877821 = 7829183) B7829183
theorem B13918547 : Blo 1903435 13918547 := bstep (se 1 (by rfl) ⟨10438910, by rfl⟩ : syracuseStep 13918547 = 20877821) B20877821
theorem B9279031 : Blo 1903435 9279031 := bstep (se 1 (by rfl) ⟨6959273, by rfl⟩ : syracuseStep 9279031 = 13918547) B13918547
theorem B12372041 : Blo 1903435 12372041 := bstep (se 2 (by rfl) ⟨4639515, by rfl⟩ : syracuseStep 12372041 = 9279031) B9279031
theorem B8248027 : Blo 1903435 8248027 := bstep (se 1 (by rfl) ⟨6186020, by rfl⟩ : syracuseStep 8248027 = 12372041) B12372041
theorem B10997369 : Blo 1903435 10997369 := bstep (se 2 (by rfl) ⟨4124013, by rfl⟩ : syracuseStep 10997369 = 8248027) B8248027
theorem B7331579 : Blo 1903435 7331579 := bstep (se 1 (by rfl) ⟨5498684, by rfl⟩ : syracuseStep 7331579 = 10997369) B10997369
theorem B4887719 : Blo 1903435 4887719 := bstep (se 1 (by rfl) ⟨3665789, by rfl⟩ : syracuseStep 4887719 = 7331579) B7331579
theorem B3258479 : Blo 1903435 3258479 := bstep (se 1 (by rfl) ⟨2443859, by rfl⟩ : syracuseStep 3258479 = 4887719) B4887719
theorem B2172319 : Blo 1903435 2172319 := bstep (se 1 (by rfl) ⟨1629239, by rfl⟩ : syracuseStep 2172319 = 3258479) B3258479
theorem B11585701 : Blo 1903435 11585701 := bstep (se 4 (by rfl) ⟨1086159, by rfl⟩ : syracuseStep 11585701 = 2172319) B2172319
theorem B15447601 : Blo 1903435 15447601 := bstep (se 2 (by rfl) ⟨5792850, by rfl⟩ : syracuseStep 15447601 = 11585701) B11585701
theorem B20596801 : Blo 1903435 20596801 := bstep (se 2 (by rfl) ⟨7723800, by rfl⟩ : syracuseStep 20596801 = 15447601) B15447601
theorem B27462401 : Blo 1903435 27462401 := bstep (se 2 (by rfl) ⟨10298400, by rfl⟩ : syracuseStep 27462401 = 20596801) B20596801
theorem B18308267 : Blo 1903435 18308267 := bstep (se 1 (by rfl) ⟨13731200, by rfl⟩ : syracuseStep 18308267 = 27462401) B27462401
theorem B12205511 : Blo 1903435 12205511 := bstep (se 1 (by rfl) ⟨9154133, by rfl⟩ : syracuseStep 12205511 = 18308267) B18308267
theorem B8137007 : Blo 1903435 8137007 := bstep (se 1 (by rfl) ⟨6102755, by rfl⟩ : syracuseStep 8137007 = 12205511) B12205511
theorem B5424671 : Blo 1903435 5424671 := bstep (se 1 (by rfl) ⟨4068503, by rfl⟩ : syracuseStep 5424671 = 8137007) B8137007
theorem B14465789 : Blo 1903435 14465789 := bstep (se 3 (by rfl) ⟨2712335, by rfl⟩ : syracuseStep 14465789 = 5424671) B5424671
theorem B9643859 : Blo 1903435 9643859 := bstep (se 1 (by rfl) ⟨7232894, by rfl⟩ : syracuseStep 9643859 = 14465789) B14465789
theorem B6429239 : Blo 1903435 6429239 := bstep (se 1 (by rfl) ⟨4821929, by rfl⟩ : syracuseStep 6429239 = 9643859) B9643859
theorem B4286159 : Blo 1903435 4286159 := bstep (se 1 (by rfl) ⟨3214619, by rfl⟩ : syracuseStep 4286159 = 6429239) B6429239
theorem B2857439 : Blo 1903435 2857439 := bstep (se 1 (by rfl) ⟨2143079, by rfl⟩ : syracuseStep 2857439 = 4286159) B4286159
theorem B1904959 : Blo 1903435 1904959 := bstep (se 1 (by rfl) ⟨1428719, by rfl⟩ : syracuseStep 1904959 = 2857439) B2857439
theorem B2857445 : Blo 1903435 2857445 := bbase (se 4 (by rfl) ⟨267885, by rfl⟩ : syracuseStep 2857445 = 535771) (by norm_num)
theorem B1904963 : Blo 1903435 1904963 := bstep (se 1 (by rfl) ⟨1428722, by rfl⟩ : syracuseStep 1904963 = 2857445) B2857445
theorem B13033973 : Blo 1903435 13033973 := bbase (se 5 (by rfl) ⟨610967, by rfl⟩ : syracuseStep 13033973 = 1221935) (by norm_num)
theorem B34757261 : Blo 1903435 34757261 := bstep (se 3 (by rfl) ⟨6516986, by rfl⟩ : syracuseStep 34757261 = 13033973) B13033973
theorem B23171507 : Blo 1903435 23171507 := bstep (se 1 (by rfl) ⟨17378630, by rfl⟩ : syracuseStep 23171507 = 34757261) B34757261
theorem B15447671 : Blo 1903435 15447671 := bstep (se 1 (by rfl) ⟨11585753, by rfl⟩ : syracuseStep 15447671 = 23171507) B23171507
theorem B10298447 : Blo 1903435 10298447 := bstep (se 1 (by rfl) ⟨7723835, by rfl⟩ : syracuseStep 10298447 = 15447671) B15447671
theorem B6865631 : Blo 1903435 6865631 := bstep (se 1 (by rfl) ⟨5149223, by rfl⟩ : syracuseStep 6865631 = 10298447) B10298447
theorem B4577087 : Blo 1903435 4577087 := bstep (se 1 (by rfl) ⟨3432815, by rfl⟩ : syracuseStep 4577087 = 6865631) B6865631
theorem B12205565 : Blo 1903435 12205565 := bstep (se 3 (by rfl) ⟨2288543, by rfl⟩ : syracuseStep 12205565 = 4577087) B4577087
theorem B8137043 : Blo 1903435 8137043 := bstep (se 1 (by rfl) ⟨6102782, by rfl⟩ : syracuseStep 8137043 = 12205565) B12205565
theorem B5424695 : Blo 1903435 5424695 := bstep (se 1 (by rfl) ⟨4068521, by rfl⟩ : syracuseStep 5424695 = 8137043) B8137043
theorem B3616463 : Blo 1903435 3616463 := bstep (se 1 (by rfl) ⟨2712347, by rfl⟩ : syracuseStep 3616463 = 5424695) B5424695
theorem B2410975 : Blo 1903435 2410975 := bstep (se 1 (by rfl) ⟨1808231, by rfl⟩ : syracuseStep 2410975 = 3616463) B3616463
theorem B3214633 : Blo 1903435 3214633 := bstep (se 2 (by rfl) ⟨1205487, by rfl⟩ : syracuseStep 3214633 = 2410975) B2410975
theorem B4286177 : Blo 1903435 4286177 := bstep (se 2 (by rfl) ⟨1607316, by rfl⟩ : syracuseStep 4286177 = 3214633) B3214633
theorem B2857451 : Blo 1903435 2857451 := bstep (se 1 (by rfl) ⟨2143088, by rfl⟩ : syracuseStep 2857451 = 4286177) B4286177
theorem B1904967 : Blo 1903435 1904967 := bstep (se 1 (by rfl) ⟨1428725, by rfl⟩ : syracuseStep 1904967 = 2857451) B2857451
theorem B2143093 : Blo 1903435 2143093 := bbase (se 5 (by rfl) ⟨100457, by rfl⟩ : syracuseStep 2143093 = 200915) (by norm_num)
theorem B2857457 : Blo 1903435 2857457 := bstep (se 2 (by rfl) ⟨1071546, by rfl⟩ : syracuseStep 2857457 = 2143093) B2143093
theorem B1904971 : Blo 1903435 1904971 := bstep (se 1 (by rfl) ⟨1428728, by rfl⟩ : syracuseStep 1904971 = 2857457) B2857457
theorem B2410985 : Blo 1903435 2410985 := bbase (se 2 (by rfl) ⟨904119, by rfl⟩ : syracuseStep 2410985 = 1808239) (by norm_num)
theorem B6429293 : Blo 1903435 6429293 := bstep (se 3 (by rfl) ⟨1205492, by rfl⟩ : syracuseStep 6429293 = 2410985) B2410985
theorem B4286195 : Blo 1903435 4286195 := bstep (se 1 (by rfl) ⟨3214646, by rfl⟩ : syracuseStep 4286195 = 6429293) B6429293
theorem B2857463 : Blo 1903435 2857463 := bstep (se 1 (by rfl) ⟨2143097, by rfl⟩ : syracuseStep 2857463 = 4286195) B4286195
theorem B1904975 : Blo 1903435 1904975 := bstep (se 1 (by rfl) ⟨1428731, by rfl⟩ : syracuseStep 1904975 = 2857463) B2857463
theorem B2857469 : Blo 1903435 2857469 := bbase (se 3 (by rfl) ⟨535775, by rfl⟩ : syracuseStep 2857469 = 1071551) (by norm_num)
theorem B1904979 : Blo 1903435 1904979 := bstep (se 1 (by rfl) ⟨1428734, by rfl⟩ : syracuseStep 1904979 = 2857469) B2857469
theorem B4286213 : Blo 1903435 4286213 := bbase (se 4 (by rfl) ⟨401832, by rfl⟩ : syracuseStep 4286213 = 803665) (by norm_num)
theorem B2857475 : Blo 1903435 2857475 := bstep (se 1 (by rfl) ⟨2143106, by rfl⟩ : syracuseStep 2857475 = 4286213) B4286213
theorem B1904983 : Blo 1903435 1904983 := bstep (se 1 (by rfl) ⟨1428737, by rfl⟩ : syracuseStep 1904983 = 2857475) B2857475
theorem B3616501 : Blo 1903435 3616501 := bbase (se 5 (by rfl) ⟨169523, by rfl⟩ : syracuseStep 3616501 = 339047) (by norm_num)
theorem B4822001 : Blo 1903435 4822001 := bstep (se 2 (by rfl) ⟨1808250, by rfl⟩ : syracuseStep 4822001 = 3616501) B3616501
theorem B3214667 : Blo 1903435 3214667 := bstep (se 1 (by rfl) ⟨2411000, by rfl⟩ : syracuseStep 3214667 = 4822001) B4822001
theorem B2143111 : Blo 1903435 2143111 := bstep (se 1 (by rfl) ⟨1607333, by rfl⟩ : syracuseStep 2143111 = 3214667) B3214667
theorem B2857481 : Blo 1903435 2857481 := bstep (se 2 (by rfl) ⟨1071555, by rfl⟩ : syracuseStep 2857481 = 2143111) B2143111
theorem B1904987 : Blo 1903435 1904987 := bstep (se 1 (by rfl) ⟨1428740, by rfl⟩ : syracuseStep 1904987 = 2857481) B2857481
theorem B9644021 : Blo 1903435 9644021 := bbase (se 5 (by rfl) ⟨452063, by rfl⟩ : syracuseStep 9644021 = 904127) (by norm_num)
theorem B6429347 : Blo 1903435 6429347 := bstep (se 1 (by rfl) ⟨4822010, by rfl⟩ : syracuseStep 6429347 = 9644021) B9644021
theorem B4286231 : Blo 1903435 4286231 := bstep (se 1 (by rfl) ⟨3214673, by rfl⟩ : syracuseStep 4286231 = 6429347) B6429347
theorem B2857487 : Blo 1903435 2857487 := bstep (se 1 (by rfl) ⟨2143115, by rfl⟩ : syracuseStep 2857487 = 4286231) B4286231
theorem B1904991 : Blo 1903435 1904991 := bstep (se 1 (by rfl) ⟨1428743, by rfl⟩ : syracuseStep 1904991 = 2857487) B2857487
theorem B2857493 : Blo 1903435 2857493 := bbase (se 6 (by rfl) ⟨66972, by rfl⟩ : syracuseStep 2857493 = 133945) (by norm_num)
theorem B1904995 : Blo 1903435 1904995 := bstep (se 1 (by rfl) ⟨1428746, by rfl⟩ : syracuseStep 1904995 = 2857493) B2857493
theorem B16274357 : Blo 1903435 16274357 := bbase (se 5 (by rfl) ⟨762860, by rfl⟩ : syracuseStep 16274357 = 1525721) (by norm_num)
theorem B10849571 : Blo 1903435 10849571 := bstep (se 1 (by rfl) ⟨8137178, by rfl⟩ : syracuseStep 10849571 = 16274357) B16274357
theorem B7233047 : Blo 1903435 7233047 := bstep (se 1 (by rfl) ⟨5424785, by rfl⟩ : syracuseStep 7233047 = 10849571) B10849571
theorem B4822031 : Blo 1903435 4822031 := bstep (se 1 (by rfl) ⟨3616523, by rfl⟩ : syracuseStep 4822031 = 7233047) B7233047
theorem B3214687 : Blo 1903435 3214687 := bstep (se 1 (by rfl) ⟨2411015, by rfl⟩ : syracuseStep 3214687 = 4822031) B4822031
theorem B4286249 : Blo 1903435 4286249 := bstep (se 2 (by rfl) ⟨1607343, by rfl⟩ : syracuseStep 4286249 = 3214687) B3214687
theorem B2857499 : Blo 1903435 2857499 := bstep (se 1 (by rfl) ⟨2143124, by rfl⟩ : syracuseStep 2857499 = 4286249) B4286249
theorem B1904999 : Blo 1903435 1904999 := bstep (se 1 (by rfl) ⟨1428749, by rfl⟩ : syracuseStep 1904999 = 2857499) B2857499
theorem B2143129 : Blo 1903435 2143129 := bbase (se 2 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 2143129 = 1607347) (by norm_num)
theorem B2857505 : Blo 1903435 2857505 := bstep (se 2 (by rfl) ⟨1071564, by rfl⟩ : syracuseStep 2857505 = 2143129) B2143129
theorem B1905003 : Blo 1903435 1905003 := bstep (se 1 (by rfl) ⟨1428752, by rfl⟩ : syracuseStep 1905003 = 2857505) B2857505
theorem B7233077 : Blo 1903435 7233077 := bbase (se 5 (by rfl) ⟨339050, by rfl⟩ : syracuseStep 7233077 = 678101) (by norm_num)
theorem B4822051 : Blo 1903435 4822051 := bstep (se 1 (by rfl) ⟨3616538, by rfl⟩ : syracuseStep 4822051 = 7233077) B7233077
theorem B6429401 : Blo 1903435 6429401 := bstep (se 2 (by rfl) ⟨2411025, by rfl⟩ : syracuseStep 6429401 = 4822051) B4822051
theorem B4286267 : Blo 1903435 4286267 := bstep (se 1 (by rfl) ⟨3214700, by rfl⟩ : syracuseStep 4286267 = 6429401) B6429401
theorem B2857511 : Blo 1903435 2857511 := bstep (se 1 (by rfl) ⟨2143133, by rfl⟩ : syracuseStep 2857511 = 4286267) B4286267
theorem B1905007 : Blo 1903435 1905007 := bstep (se 1 (by rfl) ⟨1428755, by rfl⟩ : syracuseStep 1905007 = 2857511) B2857511
theorem B2857517 : Blo 1903435 2857517 := bbase (se 3 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 2857517 = 1071569) (by norm_num)
theorem B1905011 : Blo 1903435 1905011 := bstep (se 1 (by rfl) ⟨1428758, by rfl⟩ : syracuseStep 1905011 = 2857517) B2857517
theorem B4286285 : Blo 1903435 4286285 := bbase (se 3 (by rfl) ⟨803678, by rfl⟩ : syracuseStep 4286285 = 1607357) (by norm_num)
theorem B2857523 : Blo 1903435 2857523 := bstep (se 1 (by rfl) ⟨2143142, by rfl⟩ : syracuseStep 2857523 = 4286285) B4286285
theorem B1905015 : Blo 1903435 1905015 := bstep (se 1 (by rfl) ⟨1428761, by rfl⟩ : syracuseStep 1905015 = 2857523) B2857523
theorem B2411041 : Blo 1903435 2411041 := bbase (se 2 (by rfl) ⟨904140, by rfl⟩ : syracuseStep 2411041 = 1808281) (by norm_num)
theorem B3214721 : Blo 1903435 3214721 := bstep (se 2 (by rfl) ⟨1205520, by rfl⟩ : syracuseStep 3214721 = 2411041) B2411041
theorem B2143147 : Blo 1903435 2143147 := bstep (se 1 (by rfl) ⟨1607360, by rfl⟩ : syracuseStep 2143147 = 3214721) B3214721
theorem B2857529 : Blo 1903435 2857529 := bstep (se 2 (by rfl) ⟨1071573, by rfl⟩ : syracuseStep 2857529 = 2143147) B2143147
theorem B1905019 : Blo 1903435 1905019 := bstep (se 1 (by rfl) ⟨1428764, by rfl⟩ : syracuseStep 1905019 = 2857529) B2857529
theorem B21699413 : Blo 1903435 21699413 := bbase (se 9 (by rfl) ⟨63572, by rfl⟩ : syracuseStep 21699413 = 127145) (by norm_num)
theorem B14466275 : Blo 1903435 14466275 := bstep (se 1 (by rfl) ⟨10849706, by rfl⟩ : syracuseStep 14466275 = 21699413) B21699413
theorem B9644183 : Blo 1903435 9644183 := bstep (se 1 (by rfl) ⟨7233137, by rfl⟩ : syracuseStep 9644183 = 14466275) B14466275
theorem B6429455 : Blo 1903435 6429455 := bstep (se 1 (by rfl) ⟨4822091, by rfl⟩ : syracuseStep 6429455 = 9644183) B9644183
theorem B4286303 : Blo 1903435 4286303 := bstep (se 1 (by rfl) ⟨3214727, by rfl⟩ : syracuseStep 4286303 = 6429455) B6429455
theorem B2857535 : Blo 1903435 2857535 := bstep (se 1 (by rfl) ⟨2143151, by rfl⟩ : syracuseStep 2857535 = 4286303) B4286303
theorem B1905023 : Blo 1903435 1905023 := bstep (se 1 (by rfl) ⟨1428767, by rfl⟩ : syracuseStep 1905023 = 2857535) B2857535
theorem B2857541 : Blo 1903435 2857541 := bbase (se 4 (by rfl) ⟨267894, by rfl⟩ : syracuseStep 2857541 = 535789) (by norm_num)
theorem B1905027 : Blo 1903435 1905027 := bstep (se 1 (by rfl) ⟨1428770, by rfl⟩ : syracuseStep 1905027 = 2857541) B2857541
theorem B3214741 : Blo 1903435 3214741 := bbase (se 6 (by rfl) ⟨75345, by rfl⟩ : syracuseStep 3214741 = 150691) (by norm_num)
theorem B4286321 : Blo 1903435 4286321 := bstep (se 2 (by rfl) ⟨1607370, by rfl⟩ : syracuseStep 4286321 = 3214741) B3214741
theorem B2857547 : Blo 1903435 2857547 := bstep (se 1 (by rfl) ⟨2143160, by rfl⟩ : syracuseStep 2857547 = 4286321) B4286321
theorem B1905031 : Blo 1903435 1905031 := bstep (se 1 (by rfl) ⟨1428773, by rfl⟩ : syracuseStep 1905031 = 2857547) B2857547
theorem B2143165 : Blo 1903435 2143165 := bbase (se 3 (by rfl) ⟨401843, by rfl⟩ : syracuseStep 2143165 = 803687) (by norm_num)
theorem B2857553 : Blo 1903435 2857553 := bstep (se 2 (by rfl) ⟨1071582, by rfl⟩ : syracuseStep 2857553 = 2143165) B2143165
theorem B1905035 : Blo 1903435 1905035 := bstep (se 1 (by rfl) ⟨1428776, by rfl⟩ : syracuseStep 1905035 = 2857553) B2857553
theorem B6429509 : Blo 1903435 6429509 := bbase (se 4 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 6429509 = 1205533) (by norm_num)
theorem B4286339 : Blo 1903435 4286339 := bstep (se 1 (by rfl) ⟨3214754, by rfl⟩ : syracuseStep 4286339 = 6429509) B6429509
theorem B2857559 : Blo 1903435 2857559 := bstep (se 1 (by rfl) ⟨2143169, by rfl⟩ : syracuseStep 2857559 = 4286339) B4286339
theorem B1905039 : Blo 1903435 1905039 := bstep (se 1 (by rfl) ⟨1428779, by rfl⟩ : syracuseStep 1905039 = 2857559) B2857559
theorem B2857565 : Blo 1903435 2857565 := bbase (se 3 (by rfl) ⟨535793, by rfl⟩ : syracuseStep 2857565 = 1071587) (by norm_num)
theorem B1905043 : Blo 1903435 1905043 := bstep (se 1 (by rfl) ⟨1428782, by rfl⟩ : syracuseStep 1905043 = 2857565) B2857565
theorem B4286357 : Blo 1903435 4286357 := bbase (se 6 (by rfl) ⟨100461, by rfl⟩ : syracuseStep 4286357 = 200923) (by norm_num)
theorem B2857571 : Blo 1903435 2857571 := bstep (se 1 (by rfl) ⟨2143178, by rfl⟩ : syracuseStep 2857571 = 4286357) B4286357
theorem B1905047 : Blo 1903435 1905047 := bstep (se 1 (by rfl) ⟨1428785, by rfl⟩ : syracuseStep 1905047 = 2857571) B2857571
theorem B4068701 : Blo 1903435 4068701 := bbase (se 3 (by rfl) ⟨762881, by rfl⟩ : syracuseStep 4068701 = 1525763) (by norm_num)
theorem B2712467 : Blo 1903435 2712467 := bstep (se 1 (by rfl) ⟨2034350, by rfl⟩ : syracuseStep 2712467 = 4068701) B4068701
theorem B7233245 : Blo 1903435 7233245 := bstep (se 3 (by rfl) ⟨1356233, by rfl⟩ : syracuseStep 7233245 = 2712467) B2712467
theorem B4822163 : Blo 1903435 4822163 := bstep (se 1 (by rfl) ⟨3616622, by rfl⟩ : syracuseStep 4822163 = 7233245) B7233245
theorem B3214775 : Blo 1903435 3214775 := bstep (se 1 (by rfl) ⟨2411081, by rfl⟩ : syracuseStep 3214775 = 4822163) B4822163
theorem B2143183 : Blo 1903435 2143183 := bstep (se 1 (by rfl) ⟨1607387, by rfl⟩ : syracuseStep 2143183 = 3214775) B3214775
theorem B2857577 : Blo 1903435 2857577 := bstep (se 2 (by rfl) ⟨1071591, by rfl⟩ : syracuseStep 2857577 = 2143183) B2143183
theorem B1905051 : Blo 1903435 1905051 := bstep (se 1 (by rfl) ⟨1428788, by rfl⟩ : syracuseStep 1905051 = 2857577) B2857577
theorem B13731893 : Blo 1903435 13731893 := bbase (se 5 (by rfl) ⟨643682, by rfl⟩ : syracuseStep 13731893 = 1287365) (by norm_num)
theorem B9154595 : Blo 1903435 9154595 := bstep (se 1 (by rfl) ⟨6865946, by rfl⟩ : syracuseStep 9154595 = 13731893) B13731893
theorem B6103063 : Blo 1903435 6103063 := bstep (se 1 (by rfl) ⟨4577297, by rfl⟩ : syracuseStep 6103063 = 9154595) B9154595
theorem B8137417 : Blo 1903435 8137417 := bstep (se 2 (by rfl) ⟨3051531, by rfl⟩ : syracuseStep 8137417 = 6103063) B6103063
theorem B10849889 : Blo 1903435 10849889 := bstep (se 2 (by rfl) ⟨4068708, by rfl⟩ : syracuseStep 10849889 = 8137417) B8137417
theorem B7233259 : Blo 1903435 7233259 := bstep (se 1 (by rfl) ⟨5424944, by rfl⟩ : syracuseStep 7233259 = 10849889) B10849889
theorem B9644345 : Blo 1903435 9644345 := bstep (se 2 (by rfl) ⟨3616629, by rfl⟩ : syracuseStep 9644345 = 7233259) B7233259
theorem B6429563 : Blo 1903435 6429563 := bstep (se 1 (by rfl) ⟨4822172, by rfl⟩ : syracuseStep 6429563 = 9644345) B9644345
theorem B4286375 : Blo 1903435 4286375 := bstep (se 1 (by rfl) ⟨3214781, by rfl⟩ : syracuseStep 4286375 = 6429563) B6429563
theorem B2857583 : Blo 1903435 2857583 := bstep (se 1 (by rfl) ⟨2143187, by rfl⟩ : syracuseStep 2857583 = 4286375) B4286375
theorem B1905055 : Blo 1903435 1905055 := bstep (se 1 (by rfl) ⟨1428791, by rfl⟩ : syracuseStep 1905055 = 2857583) B2857583
theorem B2857589 : Blo 1903435 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B1905059 : Blo 1903435 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B3616645 : Blo 1903435 3616645 := bbase (se 4 (by rfl) ⟨339060, by rfl⟩ : syracuseStep 3616645 = 678121) (by norm_num)
theorem B4822193 : Blo 1903435 4822193 := bstep (se 2 (by rfl) ⟨1808322, by rfl⟩ : syracuseStep 4822193 = 3616645) B3616645
theorem B3214795 : Blo 1903435 3214795 := bstep (se 1 (by rfl) ⟨2411096, by rfl⟩ : syracuseStep 3214795 = 4822193) B4822193
theorem B4286393 : Blo 1903435 4286393 := bstep (se 2 (by rfl) ⟨1607397, by rfl⟩ : syracuseStep 4286393 = 3214795) B3214795
theorem B2857595 : Blo 1903435 2857595 := bstep (se 1 (by rfl) ⟨2143196, by rfl⟩ : syracuseStep 2857595 = 4286393) B4286393
theorem B1905063 : Blo 1903435 1905063 := bstep (se 1 (by rfl) ⟨1428797, by rfl⟩ : syracuseStep 1905063 = 2857595) B2857595
theorem B2143201 : Blo 1903435 2143201 := bbase (se 2 (by rfl) ⟨803700, by rfl⟩ : syracuseStep 2143201 = 1607401) (by norm_num)
theorem B2857601 : Blo 1903435 2857601 := bstep (se 2 (by rfl) ⟨1071600, by rfl⟩ : syracuseStep 2857601 = 2143201) B2143201
theorem B1905067 : Blo 1903435 1905067 := bstep (se 1 (by rfl) ⟨1428800, by rfl⟩ : syracuseStep 1905067 = 2857601) B2857601
theorem B4822213 : Blo 1903435 4822213 := bbase (se 4 (by rfl) ⟨452082, by rfl⟩ : syracuseStep 4822213 = 904165) (by norm_num)
theorem B6429617 : Blo 1903435 6429617 := bstep (se 2 (by rfl) ⟨2411106, by rfl⟩ : syracuseStep 6429617 = 4822213) B4822213
theorem B4286411 : Blo 1903435 4286411 := bstep (se 1 (by rfl) ⟨3214808, by rfl⟩ : syracuseStep 4286411 = 6429617) B6429617
theorem B2857607 : Blo 1903435 2857607 := bstep (se 1 (by rfl) ⟨2143205, by rfl⟩ : syracuseStep 2857607 = 4286411) B4286411
theorem B1905071 : Blo 1903435 1905071 := bstep (se 1 (by rfl) ⟨1428803, by rfl⟩ : syracuseStep 1905071 = 2857607) B2857607
theorem B2857613 : Blo 1903435 2857613 := bbase (se 3 (by rfl) ⟨535802, by rfl⟩ : syracuseStep 2857613 = 1071605) (by norm_num)
theorem B1905075 : Blo 1903435 1905075 := bstep (se 1 (by rfl) ⟨1428806, by rfl⟩ : syracuseStep 1905075 = 2857613) B2857613
theorem B4286429 : Blo 1903435 4286429 := bbase (se 3 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 4286429 = 1607411) (by norm_num)
theorem B2857619 : Blo 1903435 2857619 := bstep (se 1 (by rfl) ⟨2143214, by rfl⟩ : syracuseStep 2857619 = 4286429) B4286429
theorem B1905079 : Blo 1903435 1905079 := bstep (se 1 (by rfl) ⟨1428809, by rfl⟩ : syracuseStep 1905079 = 2857619) B2857619
theorem B3214829 : Blo 1903435 3214829 := bbase (se 3 (by rfl) ⟨602780, by rfl⟩ : syracuseStep 3214829 = 1205561) (by norm_num)
theorem B2143219 : Blo 1903435 2143219 := bstep (se 1 (by rfl) ⟨1607414, by rfl⟩ : syracuseStep 2143219 = 3214829) B3214829
theorem B2857625 : Blo 1903435 2857625 := bstep (se 2 (by rfl) ⟨1071609, by rfl⟩ : syracuseStep 2857625 = 2143219) B2143219
theorem B1905083 : Blo 1903435 1905083 := bstep (se 1 (by rfl) ⟨1428812, by rfl⟩ : syracuseStep 1905083 = 2857625) B2857625
theorem B6517397 : Blo 1903435 6517397 := bbase (se 6 (by rfl) ⟨152751, by rfl⟩ : syracuseStep 6517397 = 305503) (by norm_num)
theorem B4344931 : Blo 1903435 4344931 := bstep (se 1 (by rfl) ⟨3258698, by rfl⟩ : syracuseStep 4344931 = 6517397) B6517397
theorem B5793241 : Blo 1903435 5793241 := bstep (se 2 (by rfl) ⟨2172465, by rfl⟩ : syracuseStep 5793241 = 4344931) B4344931
theorem B7724321 : Blo 1903435 7724321 := bstep (se 2 (by rfl) ⟨2896620, by rfl⟩ : syracuseStep 7724321 = 5793241) B5793241
theorem B5149547 : Blo 1903435 5149547 := bstep (se 1 (by rfl) ⟨3862160, by rfl⟩ : syracuseStep 5149547 = 7724321) B7724321
theorem B3433031 : Blo 1903435 3433031 := bstep (se 1 (by rfl) ⟨2574773, by rfl⟩ : syracuseStep 3433031 = 5149547) B5149547
theorem B2288687 : Blo 1903435 2288687 := bstep (se 1 (by rfl) ⟨1716515, by rfl⟩ : syracuseStep 2288687 = 3433031) B3433031
theorem B24412661 : Blo 1903435 24412661 := bstep (se 5 (by rfl) ⟨1144343, by rfl⟩ : syracuseStep 24412661 = 2288687) B2288687
theorem B16275107 : Blo 1903435 16275107 := bstep (se 1 (by rfl) ⟨12206330, by rfl⟩ : syracuseStep 16275107 = 24412661) B24412661
theorem B10850071 : Blo 1903435 10850071 := bstep (se 1 (by rfl) ⟨8137553, by rfl⟩ : syracuseStep 10850071 = 16275107) B16275107
theorem B14466761 : Blo 1903435 14466761 := bstep (se 2 (by rfl) ⟨5425035, by rfl⟩ : syracuseStep 14466761 = 10850071) B10850071
theorem B9644507 : Blo 1903435 9644507 := bstep (se 1 (by rfl) ⟨7233380, by rfl⟩ : syracuseStep 9644507 = 14466761) B14466761
theorem B6429671 : Blo 1903435 6429671 := bstep (se 1 (by rfl) ⟨4822253, by rfl⟩ : syracuseStep 6429671 = 9644507) B9644507
theorem B4286447 : Blo 1903435 4286447 := bstep (se 1 (by rfl) ⟨3214835, by rfl⟩ : syracuseStep 4286447 = 6429671) B6429671
theorem B2857631 : Blo 1903435 2857631 := bstep (se 1 (by rfl) ⟨2143223, by rfl⟩ : syracuseStep 2857631 = 4286447) B4286447
theorem B1905087 : Blo 1903435 1905087 := bstep (se 1 (by rfl) ⟨1428815, by rfl⟩ : syracuseStep 1905087 = 2857631) B2857631
theorem B2857637 : Blo 1903435 2857637 := bbase (se 4 (by rfl) ⟨267903, by rfl⟩ : syracuseStep 2857637 = 535807) (by norm_num)
theorem B1905091 : Blo 1903435 1905091 := bstep (se 1 (by rfl) ⟨1428818, by rfl⟩ : syracuseStep 1905091 = 2857637) B2857637
theorem B2411137 : Blo 1903435 2411137 := bbase (se 2 (by rfl) ⟨904176, by rfl⟩ : syracuseStep 2411137 = 1808353) (by norm_num)
theorem B3214849 : Blo 1903435 3214849 := bstep (se 2 (by rfl) ⟨1205568, by rfl⟩ : syracuseStep 3214849 = 2411137) B2411137
theorem B4286465 : Blo 1903435 4286465 := bstep (se 2 (by rfl) ⟨1607424, by rfl⟩ : syracuseStep 4286465 = 3214849) B3214849
theorem B2857643 : Blo 1903435 2857643 := bstep (se 1 (by rfl) ⟨2143232, by rfl⟩ : syracuseStep 2857643 = 4286465) B4286465
theorem B1905095 : Blo 1903435 1905095 := bstep (se 1 (by rfl) ⟨1428821, by rfl⟩ : syracuseStep 1905095 = 2857643) B2857643
theorem B2143237 : Blo 1903435 2143237 := bbase (se 4 (by rfl) ⟨200928, by rfl⟩ : syracuseStep 2143237 = 401857) (by norm_num)
theorem B2857649 : Blo 1903435 2857649 := bstep (se 2 (by rfl) ⟨1071618, by rfl⟩ : syracuseStep 2857649 = 2143237) B2143237
theorem B1905099 : Blo 1903435 1905099 := bstep (se 1 (by rfl) ⟨1428824, by rfl⟩ : syracuseStep 1905099 = 2857649) B2857649
theorem B2712541 : Blo 1903435 2712541 := bbase (se 3 (by rfl) ⟨508601, by rfl⟩ : syracuseStep 2712541 = 1017203) (by norm_num)
theorem B3616721 : Blo 1903435 3616721 := bstep (se 2 (by rfl) ⟨1356270, by rfl⟩ : syracuseStep 3616721 = 2712541) B2712541
theorem B2411147 : Blo 1903435 2411147 := bstep (se 1 (by rfl) ⟨1808360, by rfl⟩ : syracuseStep 2411147 = 3616721) B3616721
theorem B6429725 : Blo 1903435 6429725 := bstep (se 3 (by rfl) ⟨1205573, by rfl⟩ : syracuseStep 6429725 = 2411147) B2411147
theorem B4286483 : Blo 1903435 4286483 := bstep (se 1 (by rfl) ⟨3214862, by rfl⟩ : syracuseStep 4286483 = 6429725) B6429725
theorem B2857655 : Blo 1903435 2857655 := bstep (se 1 (by rfl) ⟨2143241, by rfl⟩ : syracuseStep 2857655 = 4286483) B4286483
theorem B1905103 : Blo 1903435 1905103 := bstep (se 1 (by rfl) ⟨1428827, by rfl⟩ : syracuseStep 1905103 = 2857655) B2857655
theorem B2857661 : Blo 1903435 2857661 := bbase (se 3 (by rfl) ⟨535811, by rfl⟩ : syracuseStep 2857661 = 1071623) (by norm_num)
theorem B1905107 : Blo 1903435 1905107 := bstep (se 1 (by rfl) ⟨1428830, by rfl⟩ : syracuseStep 1905107 = 2857661) B2857661
theorem B4286501 : Blo 1903435 4286501 := bbase (se 4 (by rfl) ⟨401859, by rfl⟩ : syracuseStep 4286501 = 803719) (by norm_num)
theorem B2857667 : Blo 1903435 2857667 := bstep (se 1 (by rfl) ⟨2143250, by rfl⟩ : syracuseStep 2857667 = 4286501) B4286501
theorem B1905111 : Blo 1903435 1905111 := bstep (se 1 (by rfl) ⟨1428833, by rfl⟩ : syracuseStep 1905111 = 2857667) B2857667
theorem B4822325 : Blo 1903435 4822325 := bbase (se 5 (by rfl) ⟨226046, by rfl⟩ : syracuseStep 4822325 = 452093) (by norm_num)
theorem B3214883 : Blo 1903435 3214883 := bstep (se 1 (by rfl) ⟨2411162, by rfl⟩ : syracuseStep 3214883 = 4822325) B4822325
theorem B2143255 : Blo 1903435 2143255 := bstep (se 1 (by rfl) ⟨1607441, by rfl⟩ : syracuseStep 2143255 = 3214883) B3214883
theorem B2857673 : Blo 1903435 2857673 := bstep (se 2 (by rfl) ⟨1071627, by rfl⟩ : syracuseStep 2857673 = 2143255) B2143255
theorem B1905115 : Blo 1903435 1905115 := bstep (se 1 (by rfl) ⟨1428836, by rfl⟩ : syracuseStep 1905115 = 2857673) B2857673
theorem B2896669 : Blo 1903435 2896669 := bbase (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) (by norm_num)
theorem B3862225 : Blo 1903435 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B20598533 : Blo 1903435 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B13732355 : Blo 1903435 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B9154903 : Blo 1903435 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B12206537 : Blo 1903435 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B8137691 : Blo 1903435 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B5425127 : Blo 1903435 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B3616751 : Blo 1903435 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B9644669 : Blo 1903435 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B6429779 : Blo 1903435 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B4286519 : Blo 1903435 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B2857679 : Blo 1903435 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B1905119 : Blo 1903435 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B2857685 : Blo 1903435 2857685 := bbase (se 7 (by rfl) ⟨33488, by rfl⟩ : syracuseStep 2857685 = 66977) (by norm_num)
theorem B1905123 : Blo 1903435 1905123 := bstep (se 1 (by rfl) ⟨1428842, by rfl⟩ : syracuseStep 1905123 = 2857685) B2857685
theorem B2062189 : Blo 1903435 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B2749585 : Blo 1903435 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B3666113 : Blo 1903435 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B2444075 : Blo 1903435 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B104280533 : Blo 1903435 104280533 := bstep (se 7 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 104280533 = 2444075) B2444075
theorem B69520355 : Blo 1903435 69520355 := bstep (se 1 (by rfl) ⟨52140266, by rfl⟩ : syracuseStep 69520355 = 104280533) B104280533
theorem B46346903 : Blo 1903435 46346903 := bstep (se 1 (by rfl) ⟨34760177, by rfl⟩ : syracuseStep 46346903 = 69520355) B69520355
theorem B30897935 : Blo 1903435 30897935 := bstep (se 1 (by rfl) ⟨23173451, by rfl⟩ : syracuseStep 30897935 = 46346903) B46346903
theorem B20598623 : Blo 1903435 20598623 := bstep (se 1 (by rfl) ⟨15448967, by rfl⟩ : syracuseStep 20598623 = 30897935) B30897935
theorem B13732415 : Blo 1903435 13732415 := bstep (se 1 (by rfl) ⟨10299311, by rfl⟩ : syracuseStep 13732415 = 20598623) B20598623
theorem B9154943 : Blo 1903435 9154943 := bstep (se 1 (by rfl) ⟨6866207, by rfl⟩ : syracuseStep 9154943 = 13732415) B13732415
theorem B6103295 : Blo 1903435 6103295 := bstep (se 1 (by rfl) ⟨4577471, by rfl⟩ : syracuseStep 6103295 = 9154943) B9154943
theorem B4068863 : Blo 1903435 4068863 := bstep (se 1 (by rfl) ⟨3051647, by rfl⟩ : syracuseStep 4068863 = 6103295) B6103295
theorem B2712575 : Blo 1903435 2712575 := bstep (se 1 (by rfl) ⟨2034431, by rfl⟩ : syracuseStep 2712575 = 4068863) B4068863
theorem B7233533 : Blo 1903435 7233533 := bstep (se 3 (by rfl) ⟨1356287, by rfl⟩ : syracuseStep 7233533 = 2712575) B2712575
theorem B4822355 : Blo 1903435 4822355 := bstep (se 1 (by rfl) ⟨3616766, by rfl⟩ : syracuseStep 4822355 = 7233533) B7233533
theorem B3214903 : Blo 1903435 3214903 := bstep (se 1 (by rfl) ⟨2411177, by rfl⟩ : syracuseStep 3214903 = 4822355) B4822355
theorem B4286537 : Blo 1903435 4286537 := bstep (se 2 (by rfl) ⟨1607451, by rfl⟩ : syracuseStep 4286537 = 3214903) B3214903
theorem B2857691 : Blo 1903435 2857691 := bstep (se 1 (by rfl) ⟨2143268, by rfl⟩ : syracuseStep 2857691 = 4286537) B4286537
theorem B1905127 : Blo 1903435 1905127 := bstep (se 1 (by rfl) ⟨1428845, by rfl⟩ : syracuseStep 1905127 = 2857691) B2857691
theorem B2143273 : Blo 1903435 2143273 := bbase (se 2 (by rfl) ⟨803727, by rfl⟩ : syracuseStep 2143273 = 1607455) (by norm_num)
theorem B2857697 : Blo 1903435 2857697 := bstep (se 2 (by rfl) ⟨1071636, by rfl⟩ : syracuseStep 2857697 = 2143273) B2143273
theorem B1905131 : Blo 1903435 1905131 := bstep (se 1 (by rfl) ⟨1428848, by rfl⟩ : syracuseStep 1905131 = 2857697) B2857697
theorem B2202161 : Blo 1903435 2202161 := bbase (se 2 (by rfl) ⟨825810, by rfl⟩ : syracuseStep 2202161 = 1651621) (by norm_num)
theorem B5872429 : Blo 1903435 5872429 := bstep (se 3 (by rfl) ⟨1101080, by rfl⟩ : syracuseStep 5872429 = 2202161) B2202161
theorem B7829905 : Blo 1903435 7829905 := bstep (se 2 (by rfl) ⟨2936214, by rfl⟩ : syracuseStep 7829905 = 5872429) B5872429
theorem B10439873 : Blo 1903435 10439873 := bstep (se 2 (by rfl) ⟨3914952, by rfl⟩ : syracuseStep 10439873 = 7829905) B7829905
theorem B6959915 : Blo 1903435 6959915 := bstep (se 1 (by rfl) ⟨5219936, by rfl⟩ : syracuseStep 6959915 = 10439873) B10439873
theorem B4639943 : Blo 1903435 4639943 := bstep (se 1 (by rfl) ⟨3479957, by rfl⟩ : syracuseStep 4639943 = 6959915) B6959915
theorem B3093295 : Blo 1903435 3093295 := bstep (se 1 (by rfl) ⟨2319971, by rfl⟩ : syracuseStep 3093295 = 4639943) B4639943
theorem B4124393 : Blo 1903435 4124393 := bstep (se 2 (by rfl) ⟨1546647, by rfl⟩ : syracuseStep 4124393 = 3093295) B3093295
theorem B43993525 : Blo 1903435 43993525 := bstep (se 5 (by rfl) ⟨2062196, by rfl⟩ : syracuseStep 43993525 = 4124393) B4124393
theorem B58658033 : Blo 1903435 58658033 := bstep (se 2 (by rfl) ⟨21996762, by rfl⟩ : syracuseStep 58658033 = 43993525) B43993525
theorem B39105355 : Blo 1903435 39105355 := bstep (se 1 (by rfl) ⟨29329016, by rfl⟩ : syracuseStep 39105355 = 58658033) B58658033
theorem B52140473 : Blo 1903435 52140473 := bstep (se 2 (by rfl) ⟨19552677, by rfl⟩ : syracuseStep 52140473 = 39105355) B39105355
theorem B34760315 : Blo 1903435 34760315 := bstep (se 1 (by rfl) ⟨26070236, by rfl⟩ : syracuseStep 34760315 = 52140473) B52140473
theorem B23173543 : Blo 1903435 23173543 := bstep (se 1 (by rfl) ⟨17380157, by rfl⟩ : syracuseStep 23173543 = 34760315) B34760315
theorem B30898057 : Blo 1903435 30898057 := bstep (se 2 (by rfl) ⟨11586771, by rfl⟩ : syracuseStep 30898057 = 23173543) B23173543
theorem B41197409 : Blo 1903435 41197409 := bstep (se 2 (by rfl) ⟨15449028, by rfl⟩ : syracuseStep 41197409 = 30898057) B30898057
theorem B27464939 : Blo 1903435 27464939 := bstep (se 1 (by rfl) ⟨20598704, by rfl⟩ : syracuseStep 27464939 = 41197409) B41197409
theorem B18309959 : Blo 1903435 18309959 := bstep (se 1 (by rfl) ⟨13732469, by rfl⟩ : syracuseStep 18309959 = 27464939) B27464939
theorem B12206639 : Blo 1903435 12206639 := bstep (se 1 (by rfl) ⟨9154979, by rfl⟩ : syracuseStep 12206639 = 18309959) B18309959
theorem B8137759 : Blo 1903435 8137759 := bstep (se 1 (by rfl) ⟨6103319, by rfl⟩ : syracuseStep 8137759 = 12206639) B12206639
theorem B10850345 : Blo 1903435 10850345 := bstep (se 2 (by rfl) ⟨4068879, by rfl⟩ : syracuseStep 10850345 = 8137759) B8137759
theorem B7233563 : Blo 1903435 7233563 := bstep (se 1 (by rfl) ⟨5425172, by rfl⟩ : syracuseStep 7233563 = 10850345) B10850345
theorem B4822375 : Blo 1903435 4822375 := bstep (se 1 (by rfl) ⟨3616781, by rfl⟩ : syracuseStep 4822375 = 7233563) B7233563
theorem B6429833 : Blo 1903435 6429833 := bstep (se 2 (by rfl) ⟨2411187, by rfl⟩ : syracuseStep 6429833 = 4822375) B4822375
theorem B4286555 : Blo 1903435 4286555 := bstep (se 1 (by rfl) ⟨3214916, by rfl⟩ : syracuseStep 4286555 = 6429833) B6429833
theorem B2857703 : Blo 1903435 2857703 := bstep (se 1 (by rfl) ⟨2143277, by rfl⟩ : syracuseStep 2857703 = 4286555) B4286555
theorem B1905135 : Blo 1903435 1905135 := bstep (se 1 (by rfl) ⟨1428851, by rfl⟩ : syracuseStep 1905135 = 2857703) B2857703
theorem B2857709 : Blo 1903435 2857709 := bbase (se 3 (by rfl) ⟨535820, by rfl⟩ : syracuseStep 2857709 = 1071641) (by norm_num)
theorem B1905139 : Blo 1903435 1905139 := bstep (se 1 (by rfl) ⟨1428854, by rfl⟩ : syracuseStep 1905139 = 2857709) B2857709
theorem B4286573 : Blo 1903435 4286573 := bbase (se 3 (by rfl) ⟨803732, by rfl⟩ : syracuseStep 4286573 = 1607465) (by norm_num)
theorem B2857715 : Blo 1903435 2857715 := bstep (se 1 (by rfl) ⟨2143286, by rfl⟩ : syracuseStep 2857715 = 4286573) B4286573
theorem B1905143 : Blo 1903435 1905143 := bstep (se 1 (by rfl) ⟨1428857, by rfl⟩ : syracuseStep 1905143 = 2857715) B2857715
theorem B3616805 : Blo 1903435 3616805 := bbase (se 4 (by rfl) ⟨339075, by rfl⟩ : syracuseStep 3616805 = 678151) (by norm_num)
theorem B2411203 : Blo 1903435 2411203 := bstep (se 1 (by rfl) ⟨1808402, by rfl⟩ : syracuseStep 2411203 = 3616805) B3616805
theorem B3214937 : Blo 1903435 3214937 := bstep (se 2 (by rfl) ⟨1205601, by rfl⟩ : syracuseStep 3214937 = 2411203) B2411203
theorem B2143291 : Blo 1903435 2143291 := bstep (se 1 (by rfl) ⟨1607468, by rfl⟩ : syracuseStep 2143291 = 3214937) B3214937
theorem B2857721 : Blo 1903435 2857721 := bstep (se 2 (by rfl) ⟨1071645, by rfl⟩ : syracuseStep 2857721 = 2143291) B2143291
theorem B1905147 : Blo 1903435 1905147 := bstep (se 1 (by rfl) ⟨1428860, by rfl⟩ : syracuseStep 1905147 = 2857721) B2857721
theorem B10439957 : Blo 1903435 10439957 := bbase (se 6 (by rfl) ⟨244686, by rfl⟩ : syracuseStep 10439957 = 489373) (by norm_num)
theorem B6959971 : Blo 1903435 6959971 := bstep (se 1 (by rfl) ⟨5219978, by rfl⟩ : syracuseStep 6959971 = 10439957) B10439957
theorem B37119845 : Blo 1903435 37119845 := bstep (se 4 (by rfl) ⟨3479985, by rfl⟩ : syracuseStep 37119845 = 6959971) B6959971
theorem B24746563 : Blo 1903435 24746563 := bstep (se 1 (by rfl) ⟨18559922, by rfl⟩ : syracuseStep 24746563 = 37119845) B37119845
theorem B131981669 : Blo 1903435 131981669 := bstep (se 4 (by rfl) ⟨12373281, by rfl⟩ : syracuseStep 131981669 = 24746563) B24746563
theorem B87987779 : Blo 1903435 87987779 := bstep (se 1 (by rfl) ⟨65990834, by rfl⟩ : syracuseStep 87987779 = 131981669) B131981669
theorem B58658519 : Blo 1903435 58658519 := bstep (se 1 (by rfl) ⟨43993889, by rfl⟩ : syracuseStep 58658519 = 87987779) B87987779
theorem B39105679 : Blo 1903435 39105679 := bstep (se 1 (by rfl) ⟨29329259, by rfl⟩ : syracuseStep 39105679 = 58658519) B58658519
theorem B52140905 : Blo 1903435 52140905 := bstep (se 2 (by rfl) ⟨19552839, by rfl⟩ : syracuseStep 52140905 = 39105679) B39105679
theorem B34760603 : Blo 1903435 34760603 := bstep (se 1 (by rfl) ⟨26070452, by rfl⟩ : syracuseStep 34760603 = 52140905) B52140905
theorem B23173735 : Blo 1903435 23173735 := bstep (se 1 (by rfl) ⟨17380301, by rfl⟩ : syracuseStep 23173735 = 34760603) B34760603
theorem B30898313 : Blo 1903435 30898313 := bstep (se 2 (by rfl) ⟨11586867, by rfl⟩ : syracuseStep 30898313 = 23173735) B23173735
theorem B20598875 : Blo 1903435 20598875 := bstep (se 1 (by rfl) ⟨15449156, by rfl⟩ : syracuseStep 20598875 = 30898313) B30898313
theorem B13732583 : Blo 1903435 13732583 := bstep (se 1 (by rfl) ⟨10299437, by rfl⟩ : syracuseStep 13732583 = 20598875) B20598875
theorem B36620221 : Blo 1903435 36620221 := bstep (se 3 (by rfl) ⟨6866291, by rfl⟩ : syracuseStep 36620221 = 13732583) B13732583
theorem B48826961 : Blo 1903435 48826961 := bstep (se 2 (by rfl) ⟨18310110, by rfl⟩ : syracuseStep 48826961 = 36620221) B36620221
theorem B32551307 : Blo 1903435 32551307 := bstep (se 1 (by rfl) ⟨24413480, by rfl⟩ : syracuseStep 32551307 = 48826961) B48826961
theorem B21700871 : Blo 1903435 21700871 := bstep (se 1 (by rfl) ⟨16275653, by rfl⟩ : syracuseStep 21700871 = 32551307) B32551307
theorem B14467247 : Blo 1903435 14467247 := bstep (se 1 (by rfl) ⟨10850435, by rfl⟩ : syracuseStep 14467247 = 21700871) B21700871
theorem B9644831 : Blo 1903435 9644831 := bstep (se 1 (by rfl) ⟨7233623, by rfl⟩ : syracuseStep 9644831 = 14467247) B14467247
theorem B6429887 : Blo 1903435 6429887 := bstep (se 1 (by rfl) ⟨4822415, by rfl⟩ : syracuseStep 6429887 = 9644831) B9644831
theorem B4286591 : Blo 1903435 4286591 := bstep (se 1 (by rfl) ⟨3214943, by rfl⟩ : syracuseStep 4286591 = 6429887) B6429887
theorem B2857727 : Blo 1903435 2857727 := bstep (se 1 (by rfl) ⟨2143295, by rfl⟩ : syracuseStep 2857727 = 4286591) B4286591
theorem B1905151 : Blo 1903435 1905151 := bstep (se 1 (by rfl) ⟨1428863, by rfl⟩ : syracuseStep 1905151 = 2857727) B2857727
theorem B2857733 : Blo 1903435 2857733 := bbase (se 4 (by rfl) ⟨267912, by rfl⟩ : syracuseStep 2857733 = 535825) (by norm_num)
theorem B1905155 : Blo 1903435 1905155 := bstep (se 1 (by rfl) ⟨1428866, by rfl⟩ : syracuseStep 1905155 = 2857733) B2857733
theorem B3214957 : Blo 1903435 3214957 := bbase (se 3 (by rfl) ⟨602804, by rfl⟩ : syracuseStep 3214957 = 1205609) (by norm_num)
theorem B4286609 : Blo 1903435 4286609 := bstep (se 2 (by rfl) ⟨1607478, by rfl⟩ : syracuseStep 4286609 = 3214957) B3214957
theorem B2857739 : Blo 1903435 2857739 := bstep (se 1 (by rfl) ⟨2143304, by rfl⟩ : syracuseStep 2857739 = 4286609) B4286609
theorem B1905159 : Blo 1903435 1905159 := bstep (se 1 (by rfl) ⟨1428869, by rfl⟩ : syracuseStep 1905159 = 2857739) B2857739
theorem B2143309 : Blo 1903435 2143309 := bbase (se 3 (by rfl) ⟨401870, by rfl⟩ : syracuseStep 2143309 = 803741) (by norm_num)
theorem B2857745 : Blo 1903435 2857745 := bstep (se 2 (by rfl) ⟨1071654, by rfl⟩ : syracuseStep 2857745 = 2143309) B2143309
theorem B1905163 : Blo 1903435 1905163 := bstep (se 1 (by rfl) ⟨1428872, by rfl⟩ : syracuseStep 1905163 = 2857745) B2857745
theorem B6429941 : Blo 1903435 6429941 := bbase (se 5 (by rfl) ⟨301403, by rfl⟩ : syracuseStep 6429941 = 602807) (by norm_num)
theorem B4286627 : Blo 1903435 4286627 := bstep (se 1 (by rfl) ⟨3214970, by rfl⟩ : syracuseStep 4286627 = 6429941) B6429941
theorem B2857751 : Blo 1903435 2857751 := bstep (se 1 (by rfl) ⟨2143313, by rfl⟩ : syracuseStep 2857751 = 4286627) B4286627
theorem B1905167 : Blo 1903435 1905167 := bstep (se 1 (by rfl) ⟨1428875, by rfl⟩ : syracuseStep 1905167 = 2857751) B2857751
theorem B2857757 : Blo 1903435 2857757 := bbase (se 3 (by rfl) ⟨535829, by rfl⟩ : syracuseStep 2857757 = 1071659) (by norm_num)
theorem B1905171 : Blo 1903435 1905171 := bstep (se 1 (by rfl) ⟨1428878, by rfl⟩ : syracuseStep 1905171 = 2857757) B2857757
theorem B4286645 : Blo 1903435 4286645 := bbase (se 5 (by rfl) ⟨200936, by rfl⟩ : syracuseStep 4286645 = 401873) (by norm_num)
theorem B2857763 : Blo 1903435 2857763 := bstep (se 1 (by rfl) ⟨2143322, by rfl⟩ : syracuseStep 2857763 = 4286645) B4286645
theorem B1905175 : Blo 1903435 1905175 := bstep (se 1 (by rfl) ⟨1428881, by rfl⟩ : syracuseStep 1905175 = 2857763) B2857763
theorem B4577597 : Blo 1903435 4577597 := bbase (se 3 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 4577597 = 1716599) (by norm_num)
theorem B3051731 : Blo 1903435 3051731 := bstep (se 1 (by rfl) ⟨2288798, by rfl⟩ : syracuseStep 3051731 = 4577597) B4577597
theorem B2034487 : Blo 1903435 2034487 := bstep (se 1 (by rfl) ⟨1525865, by rfl⟩ : syracuseStep 2034487 = 3051731) B3051731
theorem B10850597 : Blo 1903435 10850597 := bstep (se 4 (by rfl) ⟨1017243, by rfl⟩ : syracuseStep 10850597 = 2034487) B2034487
theorem B7233731 : Blo 1903435 7233731 := bstep (se 1 (by rfl) ⟨5425298, by rfl⟩ : syracuseStep 7233731 = 10850597) B10850597
theorem B4822487 : Blo 1903435 4822487 := bstep (se 1 (by rfl) ⟨3616865, by rfl⟩ : syracuseStep 4822487 = 7233731) B7233731
theorem B3214991 : Blo 1903435 3214991 := bstep (se 1 (by rfl) ⟨2411243, by rfl⟩ : syracuseStep 3214991 = 4822487) B4822487
theorem B2143327 : Blo 1903435 2143327 := bstep (se 1 (by rfl) ⟨1607495, by rfl⟩ : syracuseStep 2143327 = 3214991) B3214991
theorem B2857769 : Blo 1903435 2857769 := bstep (se 2 (by rfl) ⟨1071663, by rfl⟩ : syracuseStep 2857769 = 2143327) B2143327
theorem B1905179 : Blo 1903435 1905179 := bstep (se 1 (by rfl) ⟨1428884, by rfl⟩ : syracuseStep 1905179 = 2857769) B2857769
theorem B3433205 : Blo 1903435 3433205 := bbase (se 5 (by rfl) ⟨160931, by rfl⟩ : syracuseStep 3433205 = 321863) (by norm_num)
theorem B2288803 : Blo 1903435 2288803 := bstep (se 1 (by rfl) ⟨1716602, by rfl⟩ : syracuseStep 2288803 = 3433205) B3433205
theorem B3051737 : Blo 1903435 3051737 := bstep (se 2 (by rfl) ⟨1144401, by rfl⟩ : syracuseStep 3051737 = 2288803) B2288803
theorem B2034491 : Blo 1903435 2034491 := bstep (se 1 (by rfl) ⟨1525868, by rfl⟩ : syracuseStep 2034491 = 3051737) B3051737
theorem B5425309 : Blo 1903435 5425309 := bstep (se 3 (by rfl) ⟨1017245, by rfl⟩ : syracuseStep 5425309 = 2034491) B2034491
theorem B7233745 : Blo 1903435 7233745 := bstep (se 2 (by rfl) ⟨2712654, by rfl⟩ : syracuseStep 7233745 = 5425309) B5425309
theorem B9644993 : Blo 1903435 9644993 := bstep (se 2 (by rfl) ⟨3616872, by rfl⟩ : syracuseStep 9644993 = 7233745) B7233745
theorem B6429995 : Blo 1903435 6429995 := bstep (se 1 (by rfl) ⟨4822496, by rfl⟩ : syracuseStep 6429995 = 9644993) B9644993
theorem B4286663 : Blo 1903435 4286663 := bstep (se 1 (by rfl) ⟨3214997, by rfl⟩ : syracuseStep 4286663 = 6429995) B6429995
theorem B2857775 : Blo 1903435 2857775 := bstep (se 1 (by rfl) ⟨2143331, by rfl⟩ : syracuseStep 2857775 = 4286663) B4286663
theorem B1905183 : Blo 1903435 1905183 := bstep (se 1 (by rfl) ⟨1428887, by rfl⟩ : syracuseStep 1905183 = 2857775) B2857775
theorem B2857781 : Blo 1903435 2857781 := bbase (se 5 (by rfl) ⟨133958, by rfl⟩ : syracuseStep 2857781 = 267917) (by norm_num)
theorem B1905187 : Blo 1903435 1905187 := bstep (se 1 (by rfl) ⟨1428890, by rfl⟩ : syracuseStep 1905187 = 2857781) B2857781
theorem B4822517 : Blo 1903435 4822517 := bbase (se 5 (by rfl) ⟨226055, by rfl⟩ : syracuseStep 4822517 = 452111) (by norm_num)
theorem B3215011 : Blo 1903435 3215011 := bstep (se 1 (by rfl) ⟨2411258, by rfl⟩ : syracuseStep 3215011 = 4822517) B4822517
theorem B4286681 : Blo 1903435 4286681 := bstep (se 2 (by rfl) ⟨1607505, by rfl⟩ : syracuseStep 4286681 = 3215011) B3215011
theorem B2857787 : Blo 1903435 2857787 := bstep (se 1 (by rfl) ⟨2143340, by rfl⟩ : syracuseStep 2857787 = 4286681) B4286681
theorem B1905191 : Blo 1903435 1905191 := bstep (se 1 (by rfl) ⟨1428893, by rfl⟩ : syracuseStep 1905191 = 2857787) B2857787
theorem B2143345 : Blo 1903435 2143345 := bbase (se 2 (by rfl) ⟨803754, by rfl⟩ : syracuseStep 2143345 = 1607509) (by norm_num)
theorem B2857793 : Blo 1903435 2857793 := bstep (se 2 (by rfl) ⟨1071672, by rfl⟩ : syracuseStep 2857793 = 2143345) B2143345
theorem B1905195 : Blo 1903435 1905195 := bstep (se 1 (by rfl) ⟨1428896, by rfl⟩ : syracuseStep 1905195 = 2857793) B2857793
theorem B6103525 : Blo 1903435 6103525 := bbase (se 4 (by rfl) ⟨572205, by rfl⟩ : syracuseStep 6103525 = 1144411) (by norm_num)
theorem B8138033 : Blo 1903435 8138033 := bstep (se 2 (by rfl) ⟨3051762, by rfl⟩ : syracuseStep 8138033 = 6103525) B6103525
theorem B5425355 : Blo 1903435 5425355 := bstep (se 1 (by rfl) ⟨4069016, by rfl⟩ : syracuseStep 5425355 = 8138033) B8138033
theorem B3616903 : Blo 1903435 3616903 := bstep (se 1 (by rfl) ⟨2712677, by rfl⟩ : syracuseStep 3616903 = 5425355) B5425355
theorem B4822537 : Blo 1903435 4822537 := bstep (se 2 (by rfl) ⟨1808451, by rfl⟩ : syracuseStep 4822537 = 3616903) B3616903
theorem B6430049 : Blo 1903435 6430049 := bstep (se 2 (by rfl) ⟨2411268, by rfl⟩ : syracuseStep 6430049 = 4822537) B4822537
theorem B4286699 : Blo 1903435 4286699 := bstep (se 1 (by rfl) ⟨3215024, by rfl⟩ : syracuseStep 4286699 = 6430049) B6430049
theorem B2857799 : Blo 1903435 2857799 := bstep (se 1 (by rfl) ⟨2143349, by rfl⟩ : syracuseStep 2857799 = 4286699) B4286699
theorem B1905199 : Blo 1903435 1905199 := bstep (se 1 (by rfl) ⟨1428899, by rfl⟩ : syracuseStep 1905199 = 2857799) B2857799
theorem B2857805 : Blo 1903435 2857805 := bbase (se 3 (by rfl) ⟨535838, by rfl⟩ : syracuseStep 2857805 = 1071677) (by norm_num)
theorem B1905203 : Blo 1903435 1905203 := bstep (se 1 (by rfl) ⟨1428902, by rfl⟩ : syracuseStep 1905203 = 2857805) B2857805
theorem B4286717 : Blo 1903435 4286717 := bbase (se 3 (by rfl) ⟨803759, by rfl⟩ : syracuseStep 4286717 = 1607519) (by norm_num)
theorem B2857811 : Blo 1903435 2857811 := bstep (se 1 (by rfl) ⟨2143358, by rfl⟩ : syracuseStep 2857811 = 4286717) B4286717
theorem B1905207 : Blo 1903435 1905207 := bstep (se 1 (by rfl) ⟨1428905, by rfl⟩ : syracuseStep 1905207 = 2857811) B2857811
theorem B3215045 : Blo 1903435 3215045 := bbase (se 4 (by rfl) ⟨301410, by rfl⟩ : syracuseStep 3215045 = 602821) (by norm_num)
theorem B2143363 : Blo 1903435 2143363 := bstep (se 1 (by rfl) ⟨1607522, by rfl⟩ : syracuseStep 2143363 = 3215045) B3215045
theorem B2857817 : Blo 1903435 2857817 := bstep (se 2 (by rfl) ⟨1071681, by rfl⟩ : syracuseStep 2857817 = 2143363) B2143363
theorem B1905211 : Blo 1903435 1905211 := bstep (se 1 (by rfl) ⟨1428908, by rfl⟩ : syracuseStep 1905211 = 2857817) B2857817
theorem B14467733 : Blo 1903435 14467733 := bbase (se 6 (by rfl) ⟨339087, by rfl⟩ : syracuseStep 14467733 = 678175) (by norm_num)
theorem B9645155 : Blo 1903435 9645155 := bstep (se 1 (by rfl) ⟨7233866, by rfl⟩ : syracuseStep 9645155 = 14467733) B14467733
theorem B6430103 : Blo 1903435 6430103 := bstep (se 1 (by rfl) ⟨4822577, by rfl⟩ : syracuseStep 6430103 = 9645155) B9645155
theorem B4286735 : Blo 1903435 4286735 := bstep (se 1 (by rfl) ⟨3215051, by rfl⟩ : syracuseStep 4286735 = 6430103) B6430103
theorem B2857823 : Blo 1903435 2857823 := bstep (se 1 (by rfl) ⟨2143367, by rfl⟩ : syracuseStep 2857823 = 4286735) B4286735
theorem B1905215 : Blo 1903435 1905215 := bstep (se 1 (by rfl) ⟨1428911, by rfl⟩ : syracuseStep 1905215 = 2857823) B2857823
theorem B2857829 : Blo 1903435 2857829 := bbase (se 4 (by rfl) ⟨267921, by rfl⟩ : syracuseStep 2857829 = 535843) (by norm_num)
theorem B1905219 : Blo 1903435 1905219 := bstep (se 1 (by rfl) ⟨1428914, by rfl⟩ : syracuseStep 1905219 = 2857829) B2857829
theorem B3616949 : Blo 1903435 3616949 := bbase (se 5 (by rfl) ⟨169544, by rfl⟩ : syracuseStep 3616949 = 339089) (by norm_num)
theorem B2411299 : Blo 1903435 2411299 := bstep (se 1 (by rfl) ⟨1808474, by rfl⟩ : syracuseStep 2411299 = 3616949) B3616949
theorem B3215065 : Blo 1903435 3215065 := bstep (se 2 (by rfl) ⟨1205649, by rfl⟩ : syracuseStep 3215065 = 2411299) B2411299
theorem B4286753 : Blo 1903435 4286753 := bstep (se 2 (by rfl) ⟨1607532, by rfl⟩ : syracuseStep 4286753 = 3215065) B3215065
theorem B2857835 : Blo 1903435 2857835 := bstep (se 1 (by rfl) ⟨2143376, by rfl⟩ : syracuseStep 2857835 = 4286753) B4286753
theorem B1905223 : Blo 1903435 1905223 := bstep (se 1 (by rfl) ⟨1428917, by rfl⟩ : syracuseStep 1905223 = 2857835) B2857835
theorem B2143381 : Blo 1903435 2143381 := bbase (se 6 (by rfl) ⟨50235, by rfl⟩ : syracuseStep 2143381 = 100471) (by norm_num)
theorem B2857841 : Blo 1903435 2857841 := bstep (se 2 (by rfl) ⟨1071690, by rfl⟩ : syracuseStep 2857841 = 2143381) B2143381
theorem B1905227 : Blo 1903435 1905227 := bstep (se 1 (by rfl) ⟨1428920, by rfl⟩ : syracuseStep 1905227 = 2857841) B2857841
theorem B2411309 : Blo 1903435 2411309 := bbase (se 3 (by rfl) ⟨452120, by rfl⟩ : syracuseStep 2411309 = 904241) (by norm_num)
theorem B6430157 : Blo 1903435 6430157 := bstep (se 3 (by rfl) ⟨1205654, by rfl⟩ : syracuseStep 6430157 = 2411309) B2411309
theorem B4286771 : Blo 1903435 4286771 := bstep (se 1 (by rfl) ⟨3215078, by rfl⟩ : syracuseStep 4286771 = 6430157) B6430157
theorem B2857847 : Blo 1903435 2857847 := bstep (se 1 (by rfl) ⟨2143385, by rfl⟩ : syracuseStep 2857847 = 4286771) B4286771
theorem B1905231 : Blo 1903435 1905231 := bstep (se 1 (by rfl) ⟨1428923, by rfl⟩ : syracuseStep 1905231 = 2857847) B2857847
theorem B2857853 : Blo 1903435 2857853 := bbase (se 3 (by rfl) ⟨535847, by rfl⟩ : syracuseStep 2857853 = 1071695) (by norm_num)
theorem B1905235 : Blo 1903435 1905235 := bstep (se 1 (by rfl) ⟨1428926, by rfl⟩ : syracuseStep 1905235 = 2857853) B2857853
theorem B4286789 : Blo 1903435 4286789 := bbase (se 4 (by rfl) ⟨401886, by rfl⟩ : syracuseStep 4286789 = 803773) (by norm_num)
theorem B2857859 : Blo 1903435 2857859 := bstep (se 1 (by rfl) ⟨2143394, by rfl⟩ : syracuseStep 2857859 = 4286789) B4286789
theorem B1905239 : Blo 1903435 1905239 := bstep (se 1 (by rfl) ⟨1428929, by rfl⟩ : syracuseStep 1905239 = 2857859) B2857859
theorem B7332677 : Blo 1903435 7332677 := bbase (se 4 (by rfl) ⟨687438, by rfl⟩ : syracuseStep 7332677 = 1374877) (by norm_num)
theorem B4888451 : Blo 1903435 4888451 := bstep (se 1 (by rfl) ⟨3666338, by rfl⟩ : syracuseStep 4888451 = 7332677) B7332677
theorem B3258967 : Blo 1903435 3258967 := bstep (se 1 (by rfl) ⟨2444225, by rfl⟩ : syracuseStep 3258967 = 4888451) B4888451
theorem B4345289 : Blo 1903435 4345289 := bstep (se 2 (by rfl) ⟨1629483, by rfl⟩ : syracuseStep 4345289 = 3258967) B3258967
theorem B2896859 : Blo 1903435 2896859 := bstep (se 1 (by rfl) ⟨2172644, by rfl⟩ : syracuseStep 2896859 = 4345289) B4345289
theorem B1931239 : Blo 1903435 1931239 := bstep (se 1 (by rfl) ⟨1448429, by rfl⟩ : syracuseStep 1931239 = 2896859) B2896859
theorem B2574985 : Blo 1903435 2574985 := bstep (se 2 (by rfl) ⟨965619, by rfl⟩ : syracuseStep 2574985 = 1931239) B1931239
theorem B3433313 : Blo 1903435 3433313 := bstep (se 2 (by rfl) ⟨1287492, by rfl⟩ : syracuseStep 3433313 = 2574985) B2574985
theorem B9155501 : Blo 1903435 9155501 := bstep (se 3 (by rfl) ⟨1716656, by rfl⟩ : syracuseStep 9155501 = 3433313) B3433313
theorem B6103667 : Blo 1903435 6103667 := bstep (se 1 (by rfl) ⟨4577750, by rfl⟩ : syracuseStep 6103667 = 9155501) B9155501
theorem B4069111 : Blo 1903435 4069111 := bstep (se 1 (by rfl) ⟨3051833, by rfl⟩ : syracuseStep 4069111 = 6103667) B6103667
theorem B5425481 : Blo 1903435 5425481 := bstep (se 2 (by rfl) ⟨2034555, by rfl⟩ : syracuseStep 5425481 = 4069111) B4069111
theorem B3616987 : Blo 1903435 3616987 := bstep (se 1 (by rfl) ⟨2712740, by rfl⟩ : syracuseStep 3616987 = 5425481) B5425481
theorem B4822649 : Blo 1903435 4822649 := bstep (se 2 (by rfl) ⟨1808493, by rfl⟩ : syracuseStep 4822649 = 3616987) B3616987
theorem B3215099 : Blo 1903435 3215099 := bstep (se 1 (by rfl) ⟨2411324, by rfl⟩ : syracuseStep 3215099 = 4822649) B4822649
theorem B2143399 : Blo 1903435 2143399 := bstep (se 1 (by rfl) ⟨1607549, by rfl⟩ : syracuseStep 2143399 = 3215099) B3215099
theorem B2857865 : Blo 1903435 2857865 := bstep (se 2 (by rfl) ⟨1071699, by rfl⟩ : syracuseStep 2857865 = 2143399) B2143399
theorem B1905243 : Blo 1903435 1905243 := bstep (se 1 (by rfl) ⟨1428932, by rfl⟩ : syracuseStep 1905243 = 2857865) B2857865
theorem B9645317 : Blo 1903435 9645317 := bbase (se 4 (by rfl) ⟨904248, by rfl⟩ : syracuseStep 9645317 = 1808497) (by norm_num)
theorem B6430211 : Blo 1903435 6430211 := bstep (se 1 (by rfl) ⟨4822658, by rfl⟩ : syracuseStep 6430211 = 9645317) B9645317
theorem B4286807 : Blo 1903435 4286807 := bstep (se 1 (by rfl) ⟨3215105, by rfl⟩ : syracuseStep 4286807 = 6430211) B6430211
theorem B2857871 : Blo 1903435 2857871 := bstep (se 1 (by rfl) ⟨2143403, by rfl⟩ : syracuseStep 2857871 = 4286807) B4286807
theorem B1905247 : Blo 1903435 1905247 := bstep (se 1 (by rfl) ⟨1428935, by rfl⟩ : syracuseStep 1905247 = 2857871) B2857871
theorem B2857877 : Blo 1903435 2857877 := bbase (se 6 (by rfl) ⟨66981, by rfl⟩ : syracuseStep 2857877 = 133963) (by norm_num)
theorem B1905251 : Blo 1903435 1905251 := bstep (se 1 (by rfl) ⟨1428938, by rfl⟩ : syracuseStep 1905251 = 2857877) B2857877
theorem B10851029 : Blo 1903435 10851029 := bbase (se 7 (by rfl) ⟨127160, by rfl⟩ : syracuseStep 10851029 = 254321) (by norm_num)
theorem B7234019 : Blo 1903435 7234019 := bstep (se 1 (by rfl) ⟨5425514, by rfl⟩ : syracuseStep 7234019 = 10851029) B10851029
theorem B4822679 : Blo 1903435 4822679 := bstep (se 1 (by rfl) ⟨3617009, by rfl⟩ : syracuseStep 4822679 = 7234019) B7234019
theorem B3215119 : Blo 1903435 3215119 := bstep (se 1 (by rfl) ⟨2411339, by rfl⟩ : syracuseStep 3215119 = 4822679) B4822679
theorem B4286825 : Blo 1903435 4286825 := bstep (se 2 (by rfl) ⟨1607559, by rfl⟩ : syracuseStep 4286825 = 3215119) B3215119
theorem B2857883 : Blo 1903435 2857883 := bstep (se 1 (by rfl) ⟨2143412, by rfl⟩ : syracuseStep 2857883 = 4286825) B4286825
theorem B1905255 : Blo 1903435 1905255 := bstep (se 1 (by rfl) ⟨1428941, by rfl⟩ : syracuseStep 1905255 = 2857883) B2857883
theorem B2143417 : Blo 1903435 2143417 := bbase (se 2 (by rfl) ⟨803781, by rfl⟩ : syracuseStep 2143417 = 1607563) (by norm_num)
theorem B2857889 : Blo 1903435 2857889 := bstep (se 2 (by rfl) ⟨1071708, by rfl⟩ : syracuseStep 2857889 = 2143417) B2143417
theorem B1905259 : Blo 1903435 1905259 := bstep (se 1 (by rfl) ⟨1428944, by rfl⟩ : syracuseStep 1905259 = 2857889) B2857889
theorem B3433349 : Blo 1903435 3433349 := bbase (se 4 (by rfl) ⟨321876, by rfl⟩ : syracuseStep 3433349 = 643753) (by norm_num)
theorem B2288899 : Blo 1903435 2288899 := bstep (se 1 (by rfl) ⟨1716674, by rfl⟩ : syracuseStep 2288899 = 3433349) B3433349
theorem B3051865 : Blo 1903435 3051865 := bstep (se 2 (by rfl) ⟨1144449, by rfl⟩ : syracuseStep 3051865 = 2288899) B2288899
theorem B4069153 : Blo 1903435 4069153 := bstep (se 2 (by rfl) ⟨1525932, by rfl⟩ : syracuseStep 4069153 = 3051865) B3051865
theorem B5425537 : Blo 1903435 5425537 := bstep (se 2 (by rfl) ⟨2034576, by rfl⟩ : syracuseStep 5425537 = 4069153) B4069153
theorem B7234049 : Blo 1903435 7234049 := bstep (se 2 (by rfl) ⟨2712768, by rfl⟩ : syracuseStep 7234049 = 5425537) B5425537
theorem B4822699 : Blo 1903435 4822699 := bstep (se 1 (by rfl) ⟨3617024, by rfl⟩ : syracuseStep 4822699 = 7234049) B7234049
theorem B6430265 : Blo 1903435 6430265 := bstep (se 2 (by rfl) ⟨2411349, by rfl⟩ : syracuseStep 6430265 = 4822699) B4822699
theorem B4286843 : Blo 1903435 4286843 := bstep (se 1 (by rfl) ⟨3215132, by rfl⟩ : syracuseStep 4286843 = 6430265) B6430265
theorem B2857895 : Blo 1903435 2857895 := bstep (se 1 (by rfl) ⟨2143421, by rfl⟩ : syracuseStep 2857895 = 4286843) B4286843
theorem B1905263 : Blo 1903435 1905263 := bstep (se 1 (by rfl) ⟨1428947, by rfl⟩ : syracuseStep 1905263 = 2857895) B2857895
theorem B2857901 : Blo 1903435 2857901 := bbase (se 3 (by rfl) ⟨535856, by rfl⟩ : syracuseStep 2857901 = 1071713) (by norm_num)
theorem B1905267 : Blo 1903435 1905267 := bstep (se 1 (by rfl) ⟨1428950, by rfl⟩ : syracuseStep 1905267 = 2857901) B2857901
theorem B4286861 : Blo 1903435 4286861 := bbase (se 3 (by rfl) ⟨803786, by rfl⟩ : syracuseStep 4286861 = 1607573) (by norm_num)
theorem B2857907 : Blo 1903435 2857907 := bstep (se 1 (by rfl) ⟨2143430, by rfl⟩ : syracuseStep 2857907 = 4286861) B4286861
theorem B1905271 : Blo 1903435 1905271 := bstep (se 1 (by rfl) ⟨1428953, by rfl⟩ : syracuseStep 1905271 = 2857907) B2857907
theorem B2411365 : Blo 1903435 2411365 := bbase (se 4 (by rfl) ⟨226065, by rfl⟩ : syracuseStep 2411365 = 452131) (by norm_num)
theorem B3215153 : Blo 1903435 3215153 := bstep (se 2 (by rfl) ⟨1205682, by rfl⟩ : syracuseStep 3215153 = 2411365) B2411365
theorem B2143435 : Blo 1903435 2143435 := bstep (se 1 (by rfl) ⟨1607576, by rfl⟩ : syracuseStep 2143435 = 3215153) B3215153
theorem B2857913 : Blo 1903435 2857913 := bstep (se 2 (by rfl) ⟨1071717, by rfl⟩ : syracuseStep 2857913 = 2143435) B2143435
theorem B1905275 : Blo 1903435 1905275 := bstep (se 1 (by rfl) ⟨1428956, by rfl⟩ : syracuseStep 1905275 = 2857913) B2857913
theorem B3862549 : Blo 1903435 3862549 := bbase (se 6 (by rfl) ⟨90528, by rfl⟩ : syracuseStep 3862549 = 181057) (by norm_num)
theorem B5150065 : Blo 1903435 5150065 := bstep (se 2 (by rfl) ⟨1931274, by rfl⟩ : syracuseStep 5150065 = 3862549) B3862549
theorem B6866753 : Blo 1903435 6866753 := bstep (se 2 (by rfl) ⟨2575032, by rfl⟩ : syracuseStep 6866753 = 5150065) B5150065
theorem B18311341 : Blo 1903435 18311341 := bstep (se 3 (by rfl) ⟨3433376, by rfl⟩ : syracuseStep 18311341 = 6866753) B6866753
theorem B24415121 : Blo 1903435 24415121 := bstep (se 2 (by rfl) ⟨9155670, by rfl⟩ : syracuseStep 24415121 = 18311341) B18311341
theorem B16276747 : Blo 1903435 16276747 := bstep (se 1 (by rfl) ⟨12207560, by rfl⟩ : syracuseStep 16276747 = 24415121) B24415121
theorem B21702329 : Blo 1903435 21702329 := bstep (se 2 (by rfl) ⟨8138373, by rfl⟩ : syracuseStep 21702329 = 16276747) B16276747
theorem B14468219 : Blo 1903435 14468219 := bstep (se 1 (by rfl) ⟨10851164, by rfl⟩ : syracuseStep 14468219 = 21702329) B21702329
theorem B9645479 : Blo 1903435 9645479 := bstep (se 1 (by rfl) ⟨7234109, by rfl⟩ : syracuseStep 9645479 = 14468219) B14468219
theorem B6430319 : Blo 1903435 6430319 := bstep (se 1 (by rfl) ⟨4822739, by rfl⟩ : syracuseStep 6430319 = 9645479) B9645479
theorem B4286879 : Blo 1903435 4286879 := bstep (se 1 (by rfl) ⟨3215159, by rfl⟩ : syracuseStep 4286879 = 6430319) B6430319
theorem B2857919 : Blo 1903435 2857919 := bstep (se 1 (by rfl) ⟨2143439, by rfl⟩ : syracuseStep 2857919 = 4286879) B4286879
theorem B1905279 : Blo 1903435 1905279 := bstep (se 1 (by rfl) ⟨1428959, by rfl⟩ : syracuseStep 1905279 = 2857919) B2857919
theorem B2857925 : Blo 1903435 2857925 := bbase (se 4 (by rfl) ⟨267930, by rfl⟩ : syracuseStep 2857925 = 535861) (by norm_num)
theorem B1905283 : Blo 1903435 1905283 := bstep (se 1 (by rfl) ⟨1428962, by rfl⟩ : syracuseStep 1905283 = 2857925) B2857925
theorem B3215173 : Blo 1903435 3215173 := bbase (se 4 (by rfl) ⟨301422, by rfl⟩ : syracuseStep 3215173 = 602845) (by norm_num)
theorem B4286897 : Blo 1903435 4286897 := bstep (se 2 (by rfl) ⟨1607586, by rfl⟩ : syracuseStep 4286897 = 3215173) B3215173
theorem B2857931 : Blo 1903435 2857931 := bstep (se 1 (by rfl) ⟨2143448, by rfl⟩ : syracuseStep 2857931 = 4286897) B4286897
theorem B1905287 : Blo 1903435 1905287 := bstep (se 1 (by rfl) ⟨1428965, by rfl⟩ : syracuseStep 1905287 = 2857931) B2857931
theorem B2143453 : Blo 1903435 2143453 := bbase (se 3 (by rfl) ⟨401897, by rfl⟩ : syracuseStep 2143453 = 803795) (by norm_num)
theorem B2857937 : Blo 1903435 2857937 := bstep (se 2 (by rfl) ⟨1071726, by rfl⟩ : syracuseStep 2857937 = 2143453) B2143453
theorem B1905291 : Blo 1903435 1905291 := bstep (se 1 (by rfl) ⟨1428968, by rfl⟩ : syracuseStep 1905291 = 2857937) B2857937
theorem B6430373 : Blo 1903435 6430373 := bbase (se 4 (by rfl) ⟨602847, by rfl⟩ : syracuseStep 6430373 = 1205695) (by norm_num)
theorem B4286915 : Blo 1903435 4286915 := bstep (se 1 (by rfl) ⟨3215186, by rfl⟩ : syracuseStep 4286915 = 6430373) B6430373
theorem B2857943 : Blo 1903435 2857943 := bstep (se 1 (by rfl) ⟨2143457, by rfl⟩ : syracuseStep 2857943 = 4286915) B4286915
theorem B1905295 : Blo 1903435 1905295 := bstep (se 1 (by rfl) ⟨1428971, by rfl⟩ : syracuseStep 1905295 = 2857943) B2857943
theorem B2857949 : Blo 1903435 2857949 := bbase (se 3 (by rfl) ⟨535865, by rfl⟩ : syracuseStep 2857949 = 1071731) (by norm_num)
theorem B1905299 : Blo 1903435 1905299 := bstep (se 1 (by rfl) ⟨1428974, by rfl⟩ : syracuseStep 1905299 = 2857949) B2857949
theorem B4286933 : Blo 1903435 4286933 := bbase (se 7 (by rfl) ⟨50237, by rfl⟩ : syracuseStep 4286933 = 100475) (by norm_num)
theorem B2857955 : Blo 1903435 2857955 := bstep (se 1 (by rfl) ⟨2143466, by rfl⟩ : syracuseStep 2857955 = 4286933) B4286933
theorem B1905303 : Blo 1903435 1905303 := bstep (se 1 (by rfl) ⟨1428977, by rfl⟩ : syracuseStep 1905303 = 2857955) B2857955
theorem B2090521 : Blo 1903435 2090521 := bbase (se 2 (by rfl) ⟨783945, by rfl⟩ : syracuseStep 2090521 = 1567891) (by norm_num)
theorem B2787361 : Blo 1903435 2787361 := bstep (se 2 (by rfl) ⟨1045260, by rfl⟩ : syracuseStep 2787361 = 2090521) B2090521
theorem B14865925 : Blo 1903435 14865925 := bstep (se 4 (by rfl) ⟨1393680, by rfl⟩ : syracuseStep 14865925 = 2787361) B2787361
theorem B19821233 : Blo 1903435 19821233 := bstep (se 2 (by rfl) ⟨7432962, by rfl⟩ : syracuseStep 19821233 = 14865925) B14865925
theorem B52856621 : Blo 1903435 52856621 := bstep (se 3 (by rfl) ⟨9910616, by rfl⟩ : syracuseStep 52856621 = 19821233) B19821233
theorem B35237747 : Blo 1903435 35237747 := bstep (se 1 (by rfl) ⟨26428310, by rfl⟩ : syracuseStep 35237747 = 52856621) B52856621
theorem B23491831 : Blo 1903435 23491831 := bstep (se 1 (by rfl) ⟨17618873, by rfl⟩ : syracuseStep 23491831 = 35237747) B35237747
theorem B31322441 : Blo 1903435 31322441 := bstep (se 2 (by rfl) ⟨11745915, by rfl⟩ : syracuseStep 31322441 = 23491831) B23491831
theorem B83526509 : Blo 1903435 83526509 := bstep (se 3 (by rfl) ⟨15661220, by rfl⟩ : syracuseStep 83526509 = 31322441) B31322441
theorem B222737357 : Blo 1903435 222737357 := bstep (se 3 (by rfl) ⟨41763254, by rfl⟩ : syracuseStep 222737357 = 83526509) B83526509
theorem B148491571 : Blo 1903435 148491571 := bstep (se 1 (by rfl) ⟨111368678, by rfl⟩ : syracuseStep 148491571 = 222737357) B222737357
theorem B197988761 : Blo 1903435 197988761 := bstep (se 2 (by rfl) ⟨74245785, by rfl⟩ : syracuseStep 197988761 = 148491571) B148491571
theorem B131992507 : Blo 1903435 131992507 := bstep (se 1 (by rfl) ⟨98994380, by rfl⟩ : syracuseStep 131992507 = 197988761) B197988761
theorem B175990009 : Blo 1903435 175990009 := bstep (se 2 (by rfl) ⟨65996253, by rfl⟩ : syracuseStep 175990009 = 131992507) B131992507
theorem B234653345 : Blo 1903435 234653345 := bstep (se 2 (by rfl) ⟨87995004, by rfl⟩ : syracuseStep 234653345 = 175990009) B175990009
theorem B156435563 : Blo 1903435 156435563 := bstep (se 1 (by rfl) ⟨117326672, by rfl⟩ : syracuseStep 156435563 = 234653345) B234653345
theorem B104290375 : Blo 1903435 104290375 := bstep (se 1 (by rfl) ⟨78217781, by rfl⟩ : syracuseStep 104290375 = 156435563) B156435563
theorem B139053833 : Blo 1903435 139053833 := bstep (se 2 (by rfl) ⟨52145187, by rfl⟩ : syracuseStep 139053833 = 104290375) B104290375
theorem B92702555 : Blo 1903435 92702555 := bstep (se 1 (by rfl) ⟨69526916, by rfl⟩ : syracuseStep 92702555 = 139053833) B139053833
theorem B61801703 : Blo 1903435 61801703 := bstep (se 1 (by rfl) ⟨46351277, by rfl⟩ : syracuseStep 61801703 = 92702555) B92702555
theorem B41201135 : Blo 1903435 41201135 := bstep (se 1 (by rfl) ⟨30900851, by rfl⟩ : syracuseStep 41201135 = 61801703) B61801703
theorem B27467423 : Blo 1903435 27467423 := bstep (se 1 (by rfl) ⟨20600567, by rfl⟩ : syracuseStep 27467423 = 41201135) B41201135
theorem B18311615 : Blo 1903435 18311615 := bstep (se 1 (by rfl) ⟨13733711, by rfl⟩ : syracuseStep 18311615 = 27467423) B27467423
theorem B12207743 : Blo 1903435 12207743 := bstep (se 1 (by rfl) ⟨9155807, by rfl⟩ : syracuseStep 12207743 = 18311615) B18311615
theorem B8138495 : Blo 1903435 8138495 := bstep (se 1 (by rfl) ⟨6103871, by rfl⟩ : syracuseStep 8138495 = 12207743) B12207743
theorem B5425663 : Blo 1903435 5425663 := bstep (se 1 (by rfl) ⟨4069247, by rfl⟩ : syracuseStep 5425663 = 8138495) B8138495
theorem B7234217 : Blo 1903435 7234217 := bstep (se 2 (by rfl) ⟨2712831, by rfl⟩ : syracuseStep 7234217 = 5425663) B5425663
theorem B4822811 : Blo 1903435 4822811 := bstep (se 1 (by rfl) ⟨3617108, by rfl⟩ : syracuseStep 4822811 = 7234217) B7234217
theorem B3215207 : Blo 1903435 3215207 := bstep (se 1 (by rfl) ⟨2411405, by rfl⟩ : syracuseStep 3215207 = 4822811) B4822811
theorem B2143471 : Blo 1903435 2143471 := bstep (se 1 (by rfl) ⟨1607603, by rfl⟩ : syracuseStep 2143471 = 3215207) B3215207
theorem B2857961 : Blo 1903435 2857961 := bstep (se 2 (by rfl) ⟨1071735, by rfl⟩ : syracuseStep 2857961 = 2143471) B2143471
theorem B1905307 : Blo 1903435 1905307 := bstep (se 1 (by rfl) ⟨1428980, by rfl⟩ : syracuseStep 1905307 = 2857961) B2857961
theorem B6866869 : Blo 1903435 6866869 := bbase (se 5 (by rfl) ⟨321884, by rfl⟩ : syracuseStep 6866869 = 643769) (by norm_num)
theorem B9155825 : Blo 1903435 9155825 := bstep (se 2 (by rfl) ⟨3433434, by rfl⟩ : syracuseStep 9155825 = 6866869) B6866869
theorem B6103883 : Blo 1903435 6103883 := bstep (se 1 (by rfl) ⟨4577912, by rfl⟩ : syracuseStep 6103883 = 9155825) B9155825
theorem B16277021 : Blo 1903435 16277021 := bstep (se 3 (by rfl) ⟨3051941, by rfl⟩ : syracuseStep 16277021 = 6103883) B6103883
theorem B10851347 : Blo 1903435 10851347 := bstep (se 1 (by rfl) ⟨8138510, by rfl⟩ : syracuseStep 10851347 = 16277021) B16277021
theorem B7234231 : Blo 1903435 7234231 := bstep (se 1 (by rfl) ⟨5425673, by rfl⟩ : syracuseStep 7234231 = 10851347) B10851347
theorem B9645641 : Blo 1903435 9645641 := bstep (se 2 (by rfl) ⟨3617115, by rfl⟩ : syracuseStep 9645641 = 7234231) B7234231
theorem B6430427 : Blo 1903435 6430427 := bstep (se 1 (by rfl) ⟨4822820, by rfl⟩ : syracuseStep 6430427 = 9645641) B9645641
theorem B4286951 : Blo 1903435 4286951 := bstep (se 1 (by rfl) ⟨3215213, by rfl⟩ : syracuseStep 4286951 = 6430427) B6430427
theorem B2857967 : Blo 1903435 2857967 := bstep (se 1 (by rfl) ⟨2143475, by rfl⟩ : syracuseStep 2857967 = 4286951) B4286951
theorem B1905311 : Blo 1903435 1905311 := bstep (se 1 (by rfl) ⟨1428983, by rfl⟩ : syracuseStep 1905311 = 2857967) B2857967
theorem B2857973 : Blo 1903435 2857973 := bbase (se 5 (by rfl) ⟨133967, by rfl⟩ : syracuseStep 2857973 = 267935) (by norm_num)
theorem B1905315 : Blo 1903435 1905315 := bstep (se 1 (by rfl) ⟨1428986, by rfl⟩ : syracuseStep 1905315 = 2857973) B2857973
theorem B4577933 : Blo 1903435 4577933 := bbase (se 3 (by rfl) ⟨858362, by rfl⟩ : syracuseStep 4577933 = 1716725) (by norm_num)
theorem B3051955 : Blo 1903435 3051955 := bstep (se 1 (by rfl) ⟨2288966, by rfl⟩ : syracuseStep 3051955 = 4577933) B4577933
theorem B4069273 : Blo 1903435 4069273 := bstep (se 2 (by rfl) ⟨1525977, by rfl⟩ : syracuseStep 4069273 = 3051955) B3051955
theorem B5425697 : Blo 1903435 5425697 := bstep (se 2 (by rfl) ⟨2034636, by rfl⟩ : syracuseStep 5425697 = 4069273) B4069273
theorem B3617131 : Blo 1903435 3617131 := bstep (se 1 (by rfl) ⟨2712848, by rfl⟩ : syracuseStep 3617131 = 5425697) B5425697
theorem B4822841 : Blo 1903435 4822841 := bstep (se 2 (by rfl) ⟨1808565, by rfl⟩ : syracuseStep 4822841 = 3617131) B3617131
theorem B3215227 : Blo 1903435 3215227 := bstep (se 1 (by rfl) ⟨2411420, by rfl⟩ : syracuseStep 3215227 = 4822841) B4822841
theorem B4286969 : Blo 1903435 4286969 := bstep (se 2 (by rfl) ⟨1607613, by rfl⟩ : syracuseStep 4286969 = 3215227) B3215227
theorem B2857979 : Blo 1903435 2857979 := bstep (se 1 (by rfl) ⟨2143484, by rfl⟩ : syracuseStep 2857979 = 4286969) B4286969
theorem B1905319 : Blo 1903435 1905319 := bstep (se 1 (by rfl) ⟨1428989, by rfl⟩ : syracuseStep 1905319 = 2857979) B2857979
theorem B2143489 : Blo 1903435 2143489 := bbase (se 2 (by rfl) ⟨803808, by rfl⟩ : syracuseStep 2143489 = 1607617) (by norm_num)
theorem B2857985 : Blo 1903435 2857985 := bstep (se 2 (by rfl) ⟨1071744, by rfl⟩ : syracuseStep 2857985 = 2143489) B2143489
theorem B1905323 : Blo 1903435 1905323 := bstep (se 1 (by rfl) ⟨1428992, by rfl⟩ : syracuseStep 1905323 = 2857985) B2857985
theorem B4822861 : Blo 1903435 4822861 := bbase (se 3 (by rfl) ⟨904286, by rfl⟩ : syracuseStep 4822861 = 1808573) (by norm_num)
theorem B6430481 : Blo 1903435 6430481 := bstep (se 2 (by rfl) ⟨2411430, by rfl⟩ : syracuseStep 6430481 = 4822861) B4822861
theorem B4286987 : Blo 1903435 4286987 := bstep (se 1 (by rfl) ⟨3215240, by rfl⟩ : syracuseStep 4286987 = 6430481) B6430481
theorem B2857991 : Blo 1903435 2857991 := bstep (se 1 (by rfl) ⟨2143493, by rfl⟩ : syracuseStep 2857991 = 4286987) B4286987
theorem B1905327 : Blo 1903435 1905327 := bstep (se 1 (by rfl) ⟨1428995, by rfl⟩ : syracuseStep 1905327 = 2857991) B2857991
theorem B2857997 : Blo 1903435 2857997 := bbase (se 3 (by rfl) ⟨535874, by rfl⟩ : syracuseStep 2857997 = 1071749) (by norm_num)
theorem B1905331 : Blo 1903435 1905331 := bstep (se 1 (by rfl) ⟨1428998, by rfl⟩ : syracuseStep 1905331 = 2857997) B2857997
theorem B4287005 : Blo 1903435 4287005 := bbase (se 3 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 4287005 = 1607627) (by norm_num)
theorem B2858003 : Blo 1903435 2858003 := bstep (se 1 (by rfl) ⟨2143502, by rfl⟩ : syracuseStep 2858003 = 4287005) B4287005
theorem B1905335 : Blo 1903435 1905335 := bstep (se 1 (by rfl) ⟨1429001, by rfl⟩ : syracuseStep 1905335 = 2858003) B2858003
theorem B3215261 : Blo 1903435 3215261 := bbase (se 3 (by rfl) ⟨602861, by rfl⟩ : syracuseStep 3215261 = 1205723) (by norm_num)
theorem B2143507 : Blo 1903435 2143507 := bstep (se 1 (by rfl) ⟨1607630, by rfl⟩ : syracuseStep 2143507 = 3215261) B3215261
theorem B2858009 : Blo 1903435 2858009 := bstep (se 2 (by rfl) ⟨1071753, by rfl⟩ : syracuseStep 2858009 = 2143507) B2143507
theorem B1905339 : Blo 1903435 1905339 := bstep (se 1 (by rfl) ⟨1429004, by rfl⟩ : syracuseStep 1905339 = 2858009) B2858009
theorem B18311957 : Blo 1903435 18311957 := bbase (se 6 (by rfl) ⟨429186, by rfl⟩ : syracuseStep 18311957 = 858373) (by norm_num)
theorem B12207971 : Blo 1903435 12207971 := bstep (se 1 (by rfl) ⟨9155978, by rfl⟩ : syracuseStep 12207971 = 18311957) B18311957
theorem B8138647 : Blo 1903435 8138647 := bstep (se 1 (by rfl) ⟨6103985, by rfl⟩ : syracuseStep 8138647 = 12207971) B12207971
theorem B10851529 : Blo 1903435 10851529 := bstep (se 2 (by rfl) ⟨4069323, by rfl⟩ : syracuseStep 10851529 = 8138647) B8138647
theorem B14468705 : Blo 1903435 14468705 := bstep (se 2 (by rfl) ⟨5425764, by rfl⟩ : syracuseStep 14468705 = 10851529) B10851529
theorem B9645803 : Blo 1903435 9645803 := bstep (se 1 (by rfl) ⟨7234352, by rfl⟩ : syracuseStep 9645803 = 14468705) B14468705
theorem B6430535 : Blo 1903435 6430535 := bstep (se 1 (by rfl) ⟨4822901, by rfl⟩ : syracuseStep 6430535 = 9645803) B9645803
theorem B4287023 : Blo 1903435 4287023 := bstep (se 1 (by rfl) ⟨3215267, by rfl⟩ : syracuseStep 4287023 = 6430535) B6430535
theorem B2858015 : Blo 1903435 2858015 := bstep (se 1 (by rfl) ⟨2143511, by rfl⟩ : syracuseStep 2858015 = 4287023) B4287023
theorem B1905343 : Blo 1903435 1905343 := bstep (se 1 (by rfl) ⟨1429007, by rfl⟩ : syracuseStep 1905343 = 2858015) B2858015
theorem B2858021 : Blo 1903435 2858021 := bbase (se 4 (by rfl) ⟨267939, by rfl⟩ : syracuseStep 2858021 = 535879) (by norm_num)
theorem B1905347 : Blo 1903435 1905347 := bstep (se 1 (by rfl) ⟨1429010, by rfl⟩ : syracuseStep 1905347 = 2858021) B2858021
theorem B2411461 : Blo 1903435 2411461 := bbase (se 4 (by rfl) ⟨226074, by rfl⟩ : syracuseStep 2411461 = 452149) (by norm_num)
theorem B3215281 : Blo 1903435 3215281 := bstep (se 2 (by rfl) ⟨1205730, by rfl⟩ : syracuseStep 3215281 = 2411461) B2411461
theorem B4287041 : Blo 1903435 4287041 := bstep (se 2 (by rfl) ⟨1607640, by rfl⟩ : syracuseStep 4287041 = 3215281) B3215281
theorem B2858027 : Blo 1903435 2858027 := bstep (se 1 (by rfl) ⟨2143520, by rfl⟩ : syracuseStep 2858027 = 4287041) B4287041
theorem B1905351 : Blo 1903435 1905351 := bstep (se 1 (by rfl) ⟨1429013, by rfl⟩ : syracuseStep 1905351 = 2858027) B2858027
theorem B2143525 : Blo 1903435 2143525 := bbase (se 4 (by rfl) ⟨200955, by rfl⟩ : syracuseStep 2143525 = 401911) (by norm_num)
theorem B2858033 : Blo 1903435 2858033 := bstep (se 2 (by rfl) ⟨1071762, by rfl⟩ : syracuseStep 2858033 = 2143525) B2143525
theorem B1905355 : Blo 1903435 1905355 := bstep (se 1 (by rfl) ⟨1429016, by rfl⟩ : syracuseStep 1905355 = 2858033) B2858033
theorem B4578029 : Blo 1903435 4578029 := bbase (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) (by norm_num)
theorem B3052019 : Blo 1903435 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B8138717 : Blo 1903435 8138717 := bstep (se 3 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 8138717 = 3052019) B3052019
theorem B5425811 : Blo 1903435 5425811 := bstep (se 1 (by rfl) ⟨4069358, by rfl⟩ : syracuseStep 5425811 = 8138717) B8138717
theorem B3617207 : Blo 1903435 3617207 := bstep (se 1 (by rfl) ⟨2712905, by rfl⟩ : syracuseStep 3617207 = 5425811) B5425811
theorem B2411471 : Blo 1903435 2411471 := bstep (se 1 (by rfl) ⟨1808603, by rfl⟩ : syracuseStep 2411471 = 3617207) B3617207
theorem B6430589 : Blo 1903435 6430589 := bstep (se 3 (by rfl) ⟨1205735, by rfl⟩ : syracuseStep 6430589 = 2411471) B2411471
theorem B4287059 : Blo 1903435 4287059 := bstep (se 1 (by rfl) ⟨3215294, by rfl⟩ : syracuseStep 4287059 = 6430589) B6430589
theorem B2858039 : Blo 1903435 2858039 := bstep (se 1 (by rfl) ⟨2143529, by rfl⟩ : syracuseStep 2858039 = 4287059) B4287059
theorem B1905359 : Blo 1903435 1905359 := bstep (se 1 (by rfl) ⟨1429019, by rfl⟩ : syracuseStep 1905359 = 2858039) B2858039
theorem B2858045 : Blo 1903435 2858045 := bbase (se 3 (by rfl) ⟨535883, by rfl⟩ : syracuseStep 2858045 = 1071767) (by norm_num)
theorem B1905363 : Blo 1903435 1905363 := bstep (se 1 (by rfl) ⟨1429022, by rfl⟩ : syracuseStep 1905363 = 2858045) B2858045
theorem B4287077 : Blo 1903435 4287077 := bbase (se 4 (by rfl) ⟨401913, by rfl⟩ : syracuseStep 4287077 = 803827) (by norm_num)
theorem B2858051 : Blo 1903435 2858051 := bstep (se 1 (by rfl) ⟨2143538, by rfl⟩ : syracuseStep 2858051 = 4287077) B4287077
theorem B1905367 : Blo 1903435 1905367 := bstep (se 1 (by rfl) ⟨1429025, by rfl⟩ : syracuseStep 1905367 = 2858051) B2858051
theorem B4822973 : Blo 1903435 4822973 := bbase (se 3 (by rfl) ⟨904307, by rfl⟩ : syracuseStep 4822973 = 1808615) (by norm_num)
theorem B3215315 : Blo 1903435 3215315 := bstep (se 1 (by rfl) ⟨2411486, by rfl⟩ : syracuseStep 3215315 = 4822973) B4822973
theorem B2143543 : Blo 1903435 2143543 := bstep (se 1 (by rfl) ⟨1607657, by rfl⟩ : syracuseStep 2143543 = 3215315) B3215315
theorem B2858057 : Blo 1903435 2858057 := bstep (se 2 (by rfl) ⟨1071771, by rfl⟩ : syracuseStep 2858057 = 2143543) B2143543
theorem B1905371 : Blo 1903435 1905371 := bstep (se 1 (by rfl) ⟨1429028, by rfl⟩ : syracuseStep 1905371 = 2858057) B2858057
theorem B3617237 : Blo 1903435 3617237 := bbase (se 7 (by rfl) ⟨42389, by rfl⟩ : syracuseStep 3617237 = 84779) (by norm_num)
theorem B9645965 : Blo 1903435 9645965 := bstep (se 3 (by rfl) ⟨1808618, by rfl⟩ : syracuseStep 9645965 = 3617237) B3617237
theorem B6430643 : Blo 1903435 6430643 := bstep (se 1 (by rfl) ⟨4822982, by rfl⟩ : syracuseStep 6430643 = 9645965) B9645965
theorem B4287095 : Blo 1903435 4287095 := bstep (se 1 (by rfl) ⟨3215321, by rfl⟩ : syracuseStep 4287095 = 6430643) B6430643
theorem B2858063 : Blo 1903435 2858063 := bstep (se 1 (by rfl) ⟨2143547, by rfl⟩ : syracuseStep 2858063 = 4287095) B4287095
theorem B1905375 : Blo 1903435 1905375 := bstep (se 1 (by rfl) ⟨1429031, by rfl⟩ : syracuseStep 1905375 = 2858063) B2858063
theorem B2858069 : Blo 1903435 2858069 := bbase (se 8 (by rfl) ⟨16746, by rfl⟩ : syracuseStep 2858069 = 33493) (by norm_num)
theorem B1905379 : Blo 1903435 1905379 := bstep (se 1 (by rfl) ⟨1429034, by rfl⟩ : syracuseStep 1905379 = 2858069) B2858069
theorem B3433565 : Blo 1903435 3433565 := bbase (se 3 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 3433565 = 1287587) (by norm_num)
theorem B2289043 : Blo 1903435 2289043 := bstep (se 1 (by rfl) ⟨1716782, by rfl⟩ : syracuseStep 2289043 = 3433565) B3433565
theorem B12208229 : Blo 1903435 12208229 := bstep (se 4 (by rfl) ⟨1144521, by rfl⟩ : syracuseStep 12208229 = 2289043) B2289043
theorem B8138819 : Blo 1903435 8138819 := bstep (se 1 (by rfl) ⟨6104114, by rfl⟩ : syracuseStep 8138819 = 12208229) B12208229
theorem B5425879 : Blo 1903435 5425879 := bstep (se 1 (by rfl) ⟨4069409, by rfl⟩ : syracuseStep 5425879 = 8138819) B8138819
theorem B7234505 : Blo 1903435 7234505 := bstep (se 2 (by rfl) ⟨2712939, by rfl⟩ : syracuseStep 7234505 = 5425879) B5425879
theorem B4823003 : Blo 1903435 4823003 := bstep (se 1 (by rfl) ⟨3617252, by rfl⟩ : syracuseStep 4823003 = 7234505) B7234505
theorem B3215335 : Blo 1903435 3215335 := bstep (se 1 (by rfl) ⟨2411501, by rfl⟩ : syracuseStep 3215335 = 4823003) B4823003
theorem B4287113 : Blo 1903435 4287113 := bstep (se 2 (by rfl) ⟨1607667, by rfl⟩ : syracuseStep 4287113 = 3215335) B3215335
theorem B2858075 : Blo 1903435 2858075 := bstep (se 1 (by rfl) ⟨2143556, by rfl⟩ : syracuseStep 2858075 = 4287113) B4287113
theorem B1905383 : Blo 1903435 1905383 := bstep (se 1 (by rfl) ⟨1429037, by rfl⟩ : syracuseStep 1905383 = 2858075) B2858075
theorem B2143561 : Blo 1903435 2143561 := bbase (se 2 (by rfl) ⟨803835, by rfl⟩ : syracuseStep 2143561 = 1607671) (by norm_num)
theorem B2858081 : Blo 1903435 2858081 := bstep (se 2 (by rfl) ⟨1071780, by rfl⟩ : syracuseStep 2858081 = 2143561) B2143561
theorem B1905387 : Blo 1903435 1905387 := bstep (se 1 (by rfl) ⟨1429040, by rfl⟩ : syracuseStep 1905387 = 2858081) B2858081
theorem B27468629 : Blo 1903435 27468629 := bbase (se 9 (by rfl) ⟨80474, by rfl⟩ : syracuseStep 27468629 = 160949) (by norm_num)
theorem B18312419 : Blo 1903435 18312419 := bstep (se 1 (by rfl) ⟨13734314, by rfl⟩ : syracuseStep 18312419 = 27468629) B27468629
theorem B12208279 : Blo 1903435 12208279 := bstep (se 1 (by rfl) ⟨9156209, by rfl⟩ : syracuseStep 12208279 = 18312419) B18312419
theorem B16277705 : Blo 1903435 16277705 := bstep (se 2 (by rfl) ⟨6104139, by rfl⟩ : syracuseStep 16277705 = 12208279) B12208279
theorem B10851803 : Blo 1903435 10851803 := bstep (se 1 (by rfl) ⟨8138852, by rfl⟩ : syracuseStep 10851803 = 16277705) B16277705
theorem B7234535 : Blo 1903435 7234535 := bstep (se 1 (by rfl) ⟨5425901, by rfl⟩ : syracuseStep 7234535 = 10851803) B10851803
theorem B4823023 : Blo 1903435 4823023 := bstep (se 1 (by rfl) ⟨3617267, by rfl⟩ : syracuseStep 4823023 = 7234535) B7234535
theorem B6430697 : Blo 1903435 6430697 := bstep (se 2 (by rfl) ⟨2411511, by rfl⟩ : syracuseStep 6430697 = 4823023) B4823023
theorem B4287131 : Blo 1903435 4287131 := bstep (se 1 (by rfl) ⟨3215348, by rfl⟩ : syracuseStep 4287131 = 6430697) B6430697
theorem B2858087 : Blo 1903435 2858087 := bstep (se 1 (by rfl) ⟨2143565, by rfl⟩ : syracuseStep 2858087 = 4287131) B4287131
theorem B1905391 : Blo 1903435 1905391 := bstep (se 1 (by rfl) ⟨1429043, by rfl⟩ : syracuseStep 1905391 = 2858087) B2858087
theorem B2858093 : Blo 1903435 2858093 := bbase (se 3 (by rfl) ⟨535892, by rfl⟩ : syracuseStep 2858093 = 1071785) (by norm_num)
theorem B1905395 : Blo 1903435 1905395 := bstep (se 1 (by rfl) ⟨1429046, by rfl⟩ : syracuseStep 1905395 = 2858093) B2858093
theorem B4287149 : Blo 1903435 4287149 := bbase (se 3 (by rfl) ⟨803840, by rfl⟩ : syracuseStep 4287149 = 1607681) (by norm_num)
theorem B2858099 : Blo 1903435 2858099 := bstep (se 1 (by rfl) ⟨2143574, by rfl⟩ : syracuseStep 2858099 = 4287149) B4287149
theorem B1905399 : Blo 1903435 1905399 := bstep (se 1 (by rfl) ⟨1429049, by rfl⟩ : syracuseStep 1905399 = 2858099) B2858099
theorem B4069453 : Blo 1903435 4069453 := bbase (se 3 (by rfl) ⟨763022, by rfl⟩ : syracuseStep 4069453 = 1526045) (by norm_num)
theorem B5425937 : Blo 1903435 5425937 := bstep (se 2 (by rfl) ⟨2034726, by rfl⟩ : syracuseStep 5425937 = 4069453) B4069453
theorem B3617291 : Blo 1903435 3617291 := bstep (se 1 (by rfl) ⟨2712968, by rfl⟩ : syracuseStep 3617291 = 5425937) B5425937
theorem B2411527 : Blo 1903435 2411527 := bstep (se 1 (by rfl) ⟨1808645, by rfl⟩ : syracuseStep 2411527 = 3617291) B3617291
theorem B3215369 : Blo 1903435 3215369 := bstep (se 2 (by rfl) ⟨1205763, by rfl⟩ : syracuseStep 3215369 = 2411527) B2411527
theorem B2143579 : Blo 1903435 2143579 := bstep (se 1 (by rfl) ⟨1607684, by rfl⟩ : syracuseStep 2143579 = 3215369) B3215369
theorem B2858105 : Blo 1903435 2858105 := bstep (se 2 (by rfl) ⟨1071789, by rfl⟩ : syracuseStep 2858105 = 2143579) B2143579
theorem B1905403 : Blo 1903435 1905403 := bstep (se 1 (by rfl) ⟨1429052, by rfl⟩ : syracuseStep 1905403 = 2858105) B2858105
theorem B7333301 : Blo 1903435 7333301 := bbase (se 5 (by rfl) ⟨343748, by rfl⟩ : syracuseStep 7333301 = 687497) (by norm_num)
theorem B4888867 : Blo 1903435 4888867 := bstep (se 1 (by rfl) ⟨3666650, by rfl⟩ : syracuseStep 4888867 = 7333301) B7333301
theorem B6518489 : Blo 1903435 6518489 := bstep (se 2 (by rfl) ⟨2444433, by rfl⟩ : syracuseStep 6518489 = 4888867) B4888867
theorem B17382637 : Blo 1903435 17382637 := bstep (se 3 (by rfl) ⟨3259244, by rfl⟩ : syracuseStep 17382637 = 6518489) B6518489
theorem B23176849 : Blo 1903435 23176849 := bstep (se 2 (by rfl) ⟨8691318, by rfl⟩ : syracuseStep 23176849 = 17382637) B17382637
theorem B30902465 : Blo 1903435 30902465 := bstep (se 2 (by rfl) ⟨11588424, by rfl⟩ : syracuseStep 30902465 = 23176849) B23176849
theorem B20601643 : Blo 1903435 20601643 := bstep (se 1 (by rfl) ⟨15451232, by rfl⟩ : syracuseStep 20601643 = 30902465) B30902465
theorem B27468857 : Blo 1903435 27468857 := bstep (se 2 (by rfl) ⟨10300821, by rfl⟩ : syracuseStep 27468857 = 20601643) B20601643
theorem B18312571 : Blo 1903435 18312571 := bstep (se 1 (by rfl) ⟨13734428, by rfl⟩ : syracuseStep 18312571 = 27468857) B27468857
theorem B24416761 : Blo 1903435 24416761 := bstep (se 2 (by rfl) ⟨9156285, by rfl⟩ : syracuseStep 24416761 = 18312571) B18312571
theorem B32555681 : Blo 1903435 32555681 := bstep (se 2 (by rfl) ⟨12208380, by rfl⟩ : syracuseStep 32555681 = 24416761) B24416761
theorem B21703787 : Blo 1903435 21703787 := bstep (se 1 (by rfl) ⟨16277840, by rfl⟩ : syracuseStep 21703787 = 32555681) B32555681
theorem B14469191 : Blo 1903435 14469191 := bstep (se 1 (by rfl) ⟨10851893, by rfl⟩ : syracuseStep 14469191 = 21703787) B21703787
theorem B9646127 : Blo 1903435 9646127 := bstep (se 1 (by rfl) ⟨7234595, by rfl⟩ : syracuseStep 9646127 = 14469191) B14469191
theorem B6430751 : Blo 1903435 6430751 := bstep (se 1 (by rfl) ⟨4823063, by rfl⟩ : syracuseStep 6430751 = 9646127) B9646127
theorem B4287167 : Blo 1903435 4287167 := bstep (se 1 (by rfl) ⟨3215375, by rfl⟩ : syracuseStep 4287167 = 6430751) B6430751
theorem B2858111 : Blo 1903435 2858111 := bstep (se 1 (by rfl) ⟨2143583, by rfl⟩ : syracuseStep 2858111 = 4287167) B4287167
theorem B1905407 : Blo 1903435 1905407 := bstep (se 1 (by rfl) ⟨1429055, by rfl⟩ : syracuseStep 1905407 = 2858111) B2858111
theorem B2858117 : Blo 1903435 2858117 := bbase (se 4 (by rfl) ⟨267948, by rfl⟩ : syracuseStep 2858117 = 535897) (by norm_num)
theorem B1905411 : Blo 1903435 1905411 := bstep (se 1 (by rfl) ⟨1429058, by rfl⟩ : syracuseStep 1905411 = 2858117) B2858117
theorem B3215389 : Blo 1903435 3215389 := bbase (se 3 (by rfl) ⟨602885, by rfl⟩ : syracuseStep 3215389 = 1205771) (by norm_num)
theorem B4287185 : Blo 1903435 4287185 := bstep (se 2 (by rfl) ⟨1607694, by rfl⟩ : syracuseStep 4287185 = 3215389) B3215389
theorem B2858123 : Blo 1903435 2858123 := bstep (se 1 (by rfl) ⟨2143592, by rfl⟩ : syracuseStep 2858123 = 4287185) B4287185
theorem B1905415 : Blo 1903435 1905415 := bstep (se 1 (by rfl) ⟨1429061, by rfl⟩ : syracuseStep 1905415 = 2858123) B2858123
theorem B2143597 : Blo 1903435 2143597 := bbase (se 3 (by rfl) ⟨401924, by rfl⟩ : syracuseStep 2143597 = 803849) (by norm_num)
theorem B2858129 : Blo 1903435 2858129 := bstep (se 2 (by rfl) ⟨1071798, by rfl⟩ : syracuseStep 2858129 = 2143597) B2143597
theorem B1905419 : Blo 1903435 1905419 := bstep (se 1 (by rfl) ⟨1429064, by rfl⟩ : syracuseStep 1905419 = 2858129) B2858129
theorem B6430805 : Blo 1903435 6430805 := bbase (se 8 (by rfl) ⟨37680, by rfl⟩ : syracuseStep 6430805 = 75361) (by norm_num)
theorem B4287203 : Blo 1903435 4287203 := bstep (se 1 (by rfl) ⟨3215402, by rfl⟩ : syracuseStep 4287203 = 6430805) B6430805
theorem B2858135 : Blo 1903435 2858135 := bstep (se 1 (by rfl) ⟨2143601, by rfl⟩ : syracuseStep 2858135 = 4287203) B4287203
theorem B1905423 : Blo 1903435 1905423 := bstep (se 1 (by rfl) ⟨1429067, by rfl⟩ : syracuseStep 1905423 = 2858135) B2858135
theorem B2858141 : Blo 1903435 2858141 := bbase (se 3 (by rfl) ⟨535901, by rfl⟩ : syracuseStep 2858141 = 1071803) (by norm_num)
theorem B1905427 : Blo 1903435 1905427 := bstep (se 1 (by rfl) ⟨1429070, by rfl⟩ : syracuseStep 1905427 = 2858141) B2858141
theorem B4287221 : Blo 1903435 4287221 := bbase (se 5 (by rfl) ⟨200963, by rfl⟩ : syracuseStep 4287221 = 401927) (by norm_num)
theorem B2858147 : Blo 1903435 2858147 := bstep (se 1 (by rfl) ⟨2143610, by rfl⟩ : syracuseStep 2858147 = 4287221) B4287221
theorem B1905431 : Blo 1903435 1905431 := bstep (se 1 (by rfl) ⟨1429073, by rfl⟩ : syracuseStep 1905431 = 2858147) B2858147
theorem B6867317 : Blo 1903435 6867317 := bbase (se 5 (by rfl) ⟨321905, by rfl⟩ : syracuseStep 6867317 = 643811) (by norm_num)
theorem B4578211 : Blo 1903435 4578211 := bstep (se 1 (by rfl) ⟨3433658, by rfl⟩ : syracuseStep 4578211 = 6867317) B6867317
theorem B24417125 : Blo 1903435 24417125 := bstep (se 4 (by rfl) ⟨2289105, by rfl⟩ : syracuseStep 24417125 = 4578211) B4578211
theorem B16278083 : Blo 1903435 16278083 := bstep (se 1 (by rfl) ⟨12208562, by rfl⟩ : syracuseStep 16278083 = 24417125) B24417125
theorem B10852055 : Blo 1903435 10852055 := bstep (se 1 (by rfl) ⟨8139041, by rfl⟩ : syracuseStep 10852055 = 16278083) B16278083
theorem B7234703 : Blo 1903435 7234703 := bstep (se 1 (by rfl) ⟨5426027, by rfl⟩ : syracuseStep 7234703 = 10852055) B10852055
theorem B4823135 : Blo 1903435 4823135 := bstep (se 1 (by rfl) ⟨3617351, by rfl⟩ : syracuseStep 4823135 = 7234703) B7234703
theorem B3215423 : Blo 1903435 3215423 := bstep (se 1 (by rfl) ⟨2411567, by rfl⟩ : syracuseStep 3215423 = 4823135) B4823135
theorem B2143615 : Blo 1903435 2143615 := bstep (se 1 (by rfl) ⟨1607711, by rfl⟩ : syracuseStep 2143615 = 3215423) B3215423
theorem B2858153 : Blo 1903435 2858153 := bstep (se 2 (by rfl) ⟨1071807, by rfl⟩ : syracuseStep 2858153 = 2143615) B2143615
theorem B1905435 : Blo 1903435 1905435 := bstep (se 1 (by rfl) ⟨1429076, by rfl⟩ : syracuseStep 1905435 = 2858153) B2858153
theorem C0 (j : ℕ) (h1 : 475858 ≤ j) (h2 : j ≤ 476358) : Blo 1903435 (4 * j + 3) := by
  interval_cases j
  · exact B1903435
  · exact B1903439
  · exact B1903443
  · exact B1903447
  · exact B1903451
  · exact B1903455
  · exact B1903459
  · exact B1903463
  · exact B1903467
  · exact B1903471
  · exact B1903475
  · exact B1903479
  · exact B1903483
  · exact B1903487
  · exact B1903491
  · exact B1903495
  · exact B1903499
  · exact B1903503
  · exact B1903507
  · exact B1903511
  · exact B1903515
  · exact B1903519
  · exact B1903523
  · exact B1903527
  · exact B1903531
  · exact B1903535
  · exact B1903539
  · exact B1903543
  · exact B1903547
  · exact B1903551
  · exact B1903555
  · exact B1903559
  · exact B1903563
  · exact B1903567
  · exact B1903571
  · exact B1903575
  · exact B1903579
  · exact B1903583
  · exact B1903587
  · exact B1903591
  · exact B1903595
  · exact B1903599
  · exact B1903603
  · exact B1903607
  · exact B1903611
  · exact B1903615
  · exact B1903619
  · exact B1903623
  · exact B1903627
  · exact B1903631
  · exact B1903635
  · exact B1903639
  · exact B1903643
  · exact B1903647
  · exact B1903651
  · exact B1903655
  · exact B1903659
  · exact B1903663
  · exact B1903667
  · exact B1903671
  · exact B1903675
  · exact B1903679
  · exact B1903683
  · exact B1903687
  · exact B1903691
  · exact B1903695
  · exact B1903699
  · exact B1903703
  · exact B1903707
  · exact B1903711
  · exact B1903715
  · exact B1903719
  · exact B1903723
  · exact B1903727
  · exact B1903731
  · exact B1903735
  · exact B1903739
  · exact B1903743
  · exact B1903747
  · exact B1903751
  · exact B1903755
  · exact B1903759
  · exact B1903763
  · exact B1903767
  · exact B1903771
  · exact B1903775
  · exact B1903779
  · exact B1903783
  · exact B1903787
  · exact B1903791
  · exact B1903795
  · exact B1903799
  · exact B1903803
  · exact B1903807
  · exact B1903811
  · exact B1903815
  · exact B1903819
  · exact B1903823
  · exact B1903827
  · exact B1903831
  · exact B1903835
  · exact B1903839
  · exact B1903843
  · exact B1903847
  · exact B1903851
  · exact B1903855
  · exact B1903859
  · exact B1903863
  · exact B1903867
  · exact B1903871
  · exact B1903875
  · exact B1903879
  · exact B1903883
  · exact B1903887
  · exact B1903891
  · exact B1903895
  · exact B1903899
  · exact B1903903
  · exact B1903907
  · exact B1903911
  · exact B1903915
  · exact B1903919
  · exact B1903923
  · exact B1903927
  · exact B1903931
  · exact B1903935
  · exact B1903939
  · exact B1903943
  · exact B1903947
  · exact B1903951
  · exact B1903955
  · exact B1903959
  · exact B1903963
  · exact B1903967
  · exact B1903971
  · exact B1903975
  · exact B1903979
  · exact B1903983
  · exact B1903987
  · exact B1903991
  · exact B1903995
  · exact B1903999
  · exact B1904003
  · exact B1904007
  · exact B1904011
  · exact B1904015
  · exact B1904019
  · exact B1904023
  · exact B1904027
  · exact B1904031
  · exact B1904035
  · exact B1904039
  · exact B1904043
  · exact B1904047
  · exact B1904051
  · exact B1904055
  · exact B1904059
  · exact B1904063
  · exact B1904067
  · exact B1904071
  · exact B1904075
  · exact B1904079
  · exact B1904083
  · exact B1904087
  · exact B1904091
  · exact B1904095
  · exact B1904099
  · exact B1904103
  · exact B1904107
  · exact B1904111
  · exact B1904115
  · exact B1904119
  · exact B1904123
  · exact B1904127
  · exact B1904131
  · exact B1904135
  · exact B1904139
  · exact B1904143
  · exact B1904147
  · exact B1904151
  · exact B1904155
  · exact B1904159
  · exact B1904163
  · exact B1904167
  · exact B1904171
  · exact B1904175
  · exact B1904179
  · exact B1904183
  · exact B1904187
  · exact B1904191
  · exact B1904195
  · exact B1904199
  · exact B1904203
  · exact B1904207
  · exact B1904211
  · exact B1904215
  · exact B1904219
  · exact B1904223
  · exact B1904227
  · exact B1904231
  · exact B1904235
  · exact B1904239
  · exact B1904243
  · exact B1904247
  · exact B1904251
  · exact B1904255
  · exact B1904259
  · exact B1904263
  · exact B1904267
  · exact B1904271
  · exact B1904275
  · exact B1904279
  · exact B1904283
  · exact B1904287
  · exact B1904291
  · exact B1904295
  · exact B1904299
  · exact B1904303
  · exact B1904307
  · exact B1904311
  · exact B1904315
  · exact B1904319
  · exact B1904323
  · exact B1904327
  · exact B1904331
  · exact B1904335
  · exact B1904339
  · exact B1904343
  · exact B1904347
  · exact B1904351
  · exact B1904355
  · exact B1904359
  · exact B1904363
  · exact B1904367
  · exact B1904371
  · exact B1904375
  · exact B1904379
  · exact B1904383
  · exact B1904387
  · exact B1904391
  · exact B1904395
  · exact B1904399
  · exact B1904403
  · exact B1904407
  · exact B1904411
  · exact B1904415
  · exact B1904419
  · exact B1904423
  · exact B1904427
  · exact B1904431
  · exact B1904435
  · exact B1904439
  · exact B1904443
  · exact B1904447
  · exact B1904451
  · exact B1904455
  · exact B1904459
  · exact B1904463
  · exact B1904467
  · exact B1904471
  · exact B1904475
  · exact B1904479
  · exact B1904483
  · exact B1904487
  · exact B1904491
  · exact B1904495
  · exact B1904499
  · exact B1904503
  · exact B1904507
  · exact B1904511
  · exact B1904515
  · exact B1904519
  · exact B1904523
  · exact B1904527
  · exact B1904531
  · exact B1904535
  · exact B1904539
  · exact B1904543
  · exact B1904547
  · exact B1904551
  · exact B1904555
  · exact B1904559
  · exact B1904563
  · exact B1904567
  · exact B1904571
  · exact B1904575
  · exact B1904579
  · exact B1904583
  · exact B1904587
  · exact B1904591
  · exact B1904595
  · exact B1904599
  · exact B1904603
  · exact B1904607
  · exact B1904611
  · exact B1904615
  · exact B1904619
  · exact B1904623
  · exact B1904627
  · exact B1904631
  · exact B1904635
  · exact B1904639
  · exact B1904643
  · exact B1904647
  · exact B1904651
  · exact B1904655
  · exact B1904659
  · exact B1904663
  · exact B1904667
  · exact B1904671
  · exact B1904675
  · exact B1904679
  · exact B1904683
  · exact B1904687
  · exact B1904691
  · exact B1904695
  · exact B1904699
  · exact B1904703
  · exact B1904707
  · exact B1904711
  · exact B1904715
  · exact B1904719
  · exact B1904723
  · exact B1904727
  · exact B1904731
  · exact B1904735
  · exact B1904739
  · exact B1904743
  · exact B1904747
  · exact B1904751
  · exact B1904755
  · exact B1904759
  · exact B1904763
  · exact B1904767
  · exact B1904771
  · exact B1904775
  · exact B1904779
  · exact B1904783
  · exact B1904787
  · exact B1904791
  · exact B1904795
  · exact B1904799
  · exact B1904803
  · exact B1904807
  · exact B1904811
  · exact B1904815
  · exact B1904819
  · exact B1904823
  · exact B1904827
  · exact B1904831
  · exact B1904835
  · exact B1904839
  · exact B1904843
  · exact B1904847
  · exact B1904851
  · exact B1904855
  · exact B1904859
  · exact B1904863
  · exact B1904867
  · exact B1904871
  · exact B1904875
  · exact B1904879
  · exact B1904883
  · exact B1904887
  · exact B1904891
  · exact B1904895
  · exact B1904899
  · exact B1904903
  · exact B1904907
  · exact B1904911
  · exact B1904915
  · exact B1904919
  · exact B1904923
  · exact B1904927
  · exact B1904931
  · exact B1904935
  · exact B1904939
  · exact B1904943
  · exact B1904947
  · exact B1904951
  · exact B1904955
  · exact B1904959
  · exact B1904963
  · exact B1904967
  · exact B1904971
  · exact B1904975
  · exact B1904979
  · exact B1904983
  · exact B1904987
  · exact B1904991
  · exact B1904995
  · exact B1904999
  · exact B1905003
  · exact B1905007
  · exact B1905011
  · exact B1905015
  · exact B1905019
  · exact B1905023
  · exact B1905027
  · exact B1905031
  · exact B1905035
  · exact B1905039
  · exact B1905043
  · exact B1905047
  · exact B1905051
  · exact B1905055
  · exact B1905059
  · exact B1905063
  · exact B1905067
  · exact B1905071
  · exact B1905075
  · exact B1905079
  · exact B1905083
  · exact B1905087
  · exact B1905091
  · exact B1905095
  · exact B1905099
  · exact B1905103
  · exact B1905107
  · exact B1905111
  · exact B1905115
  · exact B1905119
  · exact B1905123
  · exact B1905127
  · exact B1905131
  · exact B1905135
  · exact B1905139
  · exact B1905143
  · exact B1905147
  · exact B1905151
  · exact B1905155
  · exact B1905159
  · exact B1905163
  · exact B1905167
  · exact B1905171
  · exact B1905175
  · exact B1905179
  · exact B1905183
  · exact B1905187
  · exact B1905191
  · exact B1905195
  · exact B1905199
  · exact B1905203
  · exact B1905207
  · exact B1905211
  · exact B1905215
  · exact B1905219
  · exact B1905223
  · exact B1905227
  · exact B1905231
  · exact B1905235
  · exact B1905239
  · exact B1905243
  · exact B1905247
  · exact B1905251
  · exact B1905255
  · exact B1905259
  · exact B1905263
  · exact B1905267
  · exact B1905271
  · exact B1905275
  · exact B1905279
  · exact B1905283
  · exact B1905287
  · exact B1905291
  · exact B1905295
  · exact B1905299
  · exact B1905303
  · exact B1905307
  · exact B1905311
  · exact B1905315
  · exact B1905319
  · exact B1905323
  · exact B1905327
  · exact B1905331
  · exact B1905335
  · exact B1905339
  · exact B1905343
  · exact B1905347
  · exact B1905351
  · exact B1905355
  · exact B1905359
  · exact B1905363
  · exact B1905367
  · exact B1905371
  · exact B1905375
  · exact B1905379
  · exact B1905383
  · exact B1905387
  · exact B1905391
  · exact B1905395
  · exact B1905399
  · exact B1905403
  · exact B1905407
  · exact B1905411
  · exact B1905415
  · exact B1905419
  · exact B1905423
  · exact B1905427
  · exact B1905431
  · exact B1905435
theorem solution (m : ℕ) (hlo : 1903435 ≤ m) (hhi : m ≤ 1905435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 475858 ≤ j := by omega
    have hj2 : j ≤ 476358 := by omega
    have hb : Blo 1903435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
