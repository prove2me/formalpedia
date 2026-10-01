-- Prove2me | solution 1 for syracuse_descends_range_2009435_2011435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:41.359327+00:00
-- url     : https://prove2.me/submissions/81c45eab-eacd-4e30-9c5c-9b3d8e38c0df

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

theorem B3814789 : Blo 2009435 3814789 := bbase (se 4 (by rfl) ⟨357636, by rfl⟩ : syracuseStep 3814789 = 715273) (by norm_num)
theorem B5086385 : Blo 2009435 5086385 := bstep (se 2 (by rfl) ⟨1907394, by rfl⟩ : syracuseStep 5086385 = 3814789) B3814789
theorem B3390923 : Blo 2009435 3390923 := bstep (se 1 (by rfl) ⟨2543192, by rfl⟩ : syracuseStep 3390923 = 5086385) B5086385
theorem B2260615 : Blo 2009435 2260615 := bstep (se 1 (by rfl) ⟨1695461, by rfl⟩ : syracuseStep 2260615 = 3390923) B3390923
theorem B3014153 : Blo 2009435 3014153 := bstep (se 2 (by rfl) ⟨1130307, by rfl⟩ : syracuseStep 3014153 = 2260615) B2260615
theorem B2009435 : Blo 2009435 2009435 := bstep (se 1 (by rfl) ⟨1507076, by rfl⟩ : syracuseStep 2009435 = 3014153) B3014153
theorem B10172789 : Blo 2009435 10172789 := bbase (se 5 (by rfl) ⟨476849, by rfl⟩ : syracuseStep 10172789 = 953699) (by norm_num)
theorem B6781859 : Blo 2009435 6781859 := bstep (se 1 (by rfl) ⟨5086394, by rfl⟩ : syracuseStep 6781859 = 10172789) B10172789
theorem B4521239 : Blo 2009435 4521239 := bstep (se 1 (by rfl) ⟨3390929, by rfl⟩ : syracuseStep 4521239 = 6781859) B6781859
theorem B3014159 : Blo 2009435 3014159 := bstep (se 1 (by rfl) ⟨2260619, by rfl⟩ : syracuseStep 3014159 = 4521239) B4521239
theorem B2009439 : Blo 2009435 2009439 := bstep (se 1 (by rfl) ⟨1507079, by rfl⟩ : syracuseStep 2009439 = 3014159) B3014159
theorem B3014165 : Blo 2009435 3014165 := bbase (se 6 (by rfl) ⟨70644, by rfl⟩ : syracuseStep 3014165 = 141289) (by norm_num)
theorem B2009443 : Blo 2009435 2009443 := bstep (se 1 (by rfl) ⟨1507082, by rfl⟩ : syracuseStep 2009443 = 3014165) B3014165
theorem B5431637 : Blo 2009435 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B14484365 : Blo 2009435 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B9656243 : Blo 2009435 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B6437495 : Blo 2009435 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B17166653 : Blo 2009435 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B11444435 : Blo 2009435 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B7629623 : Blo 2009435 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B5086415 : Blo 2009435 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B3390943 : Blo 2009435 3390943 := bstep (se 1 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 3390943 = 5086415) B5086415
theorem B4521257 : Blo 2009435 4521257 := bstep (se 2 (by rfl) ⟨1695471, by rfl⟩ : syracuseStep 4521257 = 3390943) B3390943
theorem B3014171 : Blo 2009435 3014171 := bstep (se 1 (by rfl) ⟨2260628, by rfl⟩ : syracuseStep 3014171 = 4521257) B4521257
theorem B2009447 : Blo 2009435 2009447 := bstep (se 1 (by rfl) ⟨1507085, by rfl⟩ : syracuseStep 2009447 = 3014171) B3014171
theorem B2260633 : Blo 2009435 2260633 := bbase (se 2 (by rfl) ⟨847737, by rfl⟩ : syracuseStep 2260633 = 1695475) (by norm_num)
theorem B3014177 : Blo 2009435 3014177 := bstep (se 2 (by rfl) ⟨1130316, by rfl⟩ : syracuseStep 3014177 = 2260633) B2260633
theorem B2009451 : Blo 2009435 2009451 := bstep (se 1 (by rfl) ⟨1507088, by rfl⟩ : syracuseStep 2009451 = 3014177) B3014177
theorem B7629653 : Blo 2009435 7629653 := bbase (se 9 (by rfl) ⟨22352, by rfl⟩ : syracuseStep 7629653 = 44705) (by norm_num)
theorem B5086435 : Blo 2009435 5086435 := bstep (se 1 (by rfl) ⟨3814826, by rfl⟩ : syracuseStep 5086435 = 7629653) B7629653
theorem B6781913 : Blo 2009435 6781913 := bstep (se 2 (by rfl) ⟨2543217, by rfl⟩ : syracuseStep 6781913 = 5086435) B5086435
theorem B4521275 : Blo 2009435 4521275 := bstep (se 1 (by rfl) ⟨3390956, by rfl⟩ : syracuseStep 4521275 = 6781913) B6781913
theorem B3014183 : Blo 2009435 3014183 := bstep (se 1 (by rfl) ⟨2260637, by rfl⟩ : syracuseStep 3014183 = 4521275) B4521275
theorem B2009455 : Blo 2009435 2009455 := bstep (se 1 (by rfl) ⟨1507091, by rfl⟩ : syracuseStep 2009455 = 3014183) B3014183
theorem B3014189 : Blo 2009435 3014189 := bbase (se 3 (by rfl) ⟨565160, by rfl⟩ : syracuseStep 3014189 = 1130321) (by norm_num)
theorem B2009459 : Blo 2009435 2009459 := bstep (se 1 (by rfl) ⟨1507094, by rfl⟩ : syracuseStep 2009459 = 3014189) B3014189
theorem B4521293 : Blo 2009435 4521293 := bbase (se 3 (by rfl) ⟨847742, by rfl⟩ : syracuseStep 4521293 = 1695485) (by norm_num)
theorem B3014195 : Blo 2009435 3014195 := bstep (se 1 (by rfl) ⟨2260646, by rfl⟩ : syracuseStep 3014195 = 4521293) B4521293
theorem B2009463 : Blo 2009435 2009463 := bstep (se 1 (by rfl) ⟨1507097, by rfl⟩ : syracuseStep 2009463 = 3014195) B3014195
theorem B2543233 : Blo 2009435 2543233 := bbase (se 2 (by rfl) ⟨953712, by rfl⟩ : syracuseStep 2543233 = 1907425) (by norm_num)
theorem B3390977 : Blo 2009435 3390977 := bstep (se 2 (by rfl) ⟨1271616, by rfl⟩ : syracuseStep 3390977 = 2543233) B2543233
theorem B2260651 : Blo 2009435 2260651 := bstep (se 1 (by rfl) ⟨1695488, by rfl⟩ : syracuseStep 2260651 = 3390977) B3390977
theorem B3014201 : Blo 2009435 3014201 := bstep (se 2 (by rfl) ⟨1130325, by rfl⟩ : syracuseStep 3014201 = 2260651) B2260651
theorem B2009467 : Blo 2009435 2009467 := bstep (se 1 (by rfl) ⟨1507100, by rfl⟩ : syracuseStep 2009467 = 3014201) B3014201
theorem B2145857 : Blo 2009435 2145857 := bbase (se 2 (by rfl) ⟨804696, by rfl⟩ : syracuseStep 2145857 = 1609393) (by norm_num)
theorem B22889141 : Blo 2009435 22889141 := bstep (se 5 (by rfl) ⟨1072928, by rfl⟩ : syracuseStep 22889141 = 2145857) B2145857
theorem B15259427 : Blo 2009435 15259427 := bstep (se 1 (by rfl) ⟨11444570, by rfl⟩ : syracuseStep 15259427 = 22889141) B22889141
theorem B10172951 : Blo 2009435 10172951 := bstep (se 1 (by rfl) ⟨7629713, by rfl⟩ : syracuseStep 10172951 = 15259427) B15259427
theorem B6781967 : Blo 2009435 6781967 := bstep (se 1 (by rfl) ⟨5086475, by rfl⟩ : syracuseStep 6781967 = 10172951) B10172951
theorem B4521311 : Blo 2009435 4521311 := bstep (se 1 (by rfl) ⟨3390983, by rfl⟩ : syracuseStep 4521311 = 6781967) B6781967
theorem B3014207 : Blo 2009435 3014207 := bstep (se 1 (by rfl) ⟨2260655, by rfl⟩ : syracuseStep 3014207 = 4521311) B4521311
theorem B2009471 : Blo 2009435 2009471 := bstep (se 1 (by rfl) ⟨1507103, by rfl⟩ : syracuseStep 2009471 = 3014207) B3014207
theorem B3014213 : Blo 2009435 3014213 := bbase (se 4 (by rfl) ⟨282582, by rfl⟩ : syracuseStep 3014213 = 565165) (by norm_num)
theorem B2009475 : Blo 2009435 2009475 := bstep (se 1 (by rfl) ⟨1507106, by rfl⟩ : syracuseStep 2009475 = 3014213) B3014213
theorem B3390997 : Blo 2009435 3390997 := bbase (se 6 (by rfl) ⟨79476, by rfl⟩ : syracuseStep 3390997 = 158953) (by norm_num)
theorem B4521329 : Blo 2009435 4521329 := bstep (se 2 (by rfl) ⟨1695498, by rfl⟩ : syracuseStep 4521329 = 3390997) B3390997
theorem B3014219 : Blo 2009435 3014219 := bstep (se 1 (by rfl) ⟨2260664, by rfl⟩ : syracuseStep 3014219 = 4521329) B4521329
theorem B2009479 : Blo 2009435 2009479 := bstep (se 1 (by rfl) ⟨1507109, by rfl⟩ : syracuseStep 2009479 = 3014219) B3014219
theorem B2260669 : Blo 2009435 2260669 := bbase (se 3 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 2260669 = 847751) (by norm_num)
theorem B3014225 : Blo 2009435 3014225 := bstep (se 2 (by rfl) ⟨1130334, by rfl⟩ : syracuseStep 3014225 = 2260669) B2260669
theorem B2009483 : Blo 2009435 2009483 := bstep (se 1 (by rfl) ⟨1507112, by rfl⟩ : syracuseStep 2009483 = 3014225) B3014225
theorem B6782021 : Blo 2009435 6782021 := bbase (se 4 (by rfl) ⟨635814, by rfl⟩ : syracuseStep 6782021 = 1271629) (by norm_num)
theorem B4521347 : Blo 2009435 4521347 := bstep (se 1 (by rfl) ⟨3391010, by rfl⟩ : syracuseStep 4521347 = 6782021) B6782021
theorem B3014231 : Blo 2009435 3014231 := bstep (se 1 (by rfl) ⟨2260673, by rfl⟩ : syracuseStep 3014231 = 4521347) B4521347
theorem B2009487 : Blo 2009435 2009487 := bstep (se 1 (by rfl) ⟨1507115, by rfl⟩ : syracuseStep 2009487 = 3014231) B3014231
theorem B3014237 : Blo 2009435 3014237 := bbase (se 3 (by rfl) ⟨565169, by rfl⟩ : syracuseStep 3014237 = 1130339) (by norm_num)
theorem B2009491 : Blo 2009435 2009491 := bstep (se 1 (by rfl) ⟨1507118, by rfl⟩ : syracuseStep 2009491 = 3014237) B3014237
theorem B4521365 : Blo 2009435 4521365 := bbase (se 6 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 4521365 = 211939) (by norm_num)
theorem B3014243 : Blo 2009435 3014243 := bstep (se 1 (by rfl) ⟨2260682, by rfl⟩ : syracuseStep 3014243 = 4521365) B4521365
theorem B2009495 : Blo 2009435 2009495 := bstep (se 1 (by rfl) ⟨1507121, by rfl⟩ : syracuseStep 2009495 = 3014243) B3014243
theorem B15892789 : Blo 2009435 15892789 := bbase (se 5 (by rfl) ⟨744974, by rfl⟩ : syracuseStep 15892789 = 1489949) (by norm_num)
theorem B21190385 : Blo 2009435 21190385 := bstep (se 2 (by rfl) ⟨7946394, by rfl⟩ : syracuseStep 21190385 = 15892789) B15892789
theorem B14126923 : Blo 2009435 14126923 := bstep (se 1 (by rfl) ⟨10595192, by rfl⟩ : syracuseStep 14126923 = 21190385) B21190385
theorem B18835897 : Blo 2009435 18835897 := bstep (se 2 (by rfl) ⟨7063461, by rfl⟩ : syracuseStep 18835897 = 14126923) B14126923
theorem B25114529 : Blo 2009435 25114529 := bstep (se 2 (by rfl) ⟨9417948, by rfl⟩ : syracuseStep 25114529 = 18835897) B18835897
theorem B16743019 : Blo 2009435 16743019 := bstep (se 1 (by rfl) ⟨12557264, by rfl⟩ : syracuseStep 16743019 = 25114529) B25114529
theorem B22324025 : Blo 2009435 22324025 := bstep (se 2 (by rfl) ⟨8371509, by rfl⟩ : syracuseStep 22324025 = 16743019) B16743019
theorem B59530733 : Blo 2009435 59530733 := bstep (se 3 (by rfl) ⟨11162012, by rfl⟩ : syracuseStep 59530733 = 22324025) B22324025
theorem B39687155 : Blo 2009435 39687155 := bstep (se 1 (by rfl) ⟨29765366, by rfl⟩ : syracuseStep 39687155 = 59530733) B59530733
theorem B26458103 : Blo 2009435 26458103 := bstep (se 1 (by rfl) ⟨19843577, by rfl⟩ : syracuseStep 26458103 = 39687155) B39687155
theorem B17638735 : Blo 2009435 17638735 := bstep (se 1 (by rfl) ⟨13229051, by rfl⟩ : syracuseStep 17638735 = 26458103) B26458103
theorem B23518313 : Blo 2009435 23518313 := bstep (se 2 (by rfl) ⟨8819367, by rfl⟩ : syracuseStep 23518313 = 17638735) B17638735
theorem B15678875 : Blo 2009435 15678875 := bstep (se 1 (by rfl) ⟨11759156, by rfl⟩ : syracuseStep 15678875 = 23518313) B23518313
theorem B10452583 : Blo 2009435 10452583 := bstep (se 1 (by rfl) ⟨7839437, by rfl⟩ : syracuseStep 10452583 = 15678875) B15678875
theorem B55747109 : Blo 2009435 55747109 := bstep (se 4 (by rfl) ⟨5226291, by rfl⟩ : syracuseStep 55747109 = 10452583) B10452583
theorem B37164739 : Blo 2009435 37164739 := bstep (se 1 (by rfl) ⟨27873554, by rfl⟩ : syracuseStep 37164739 = 55747109) B55747109
theorem B49552985 : Blo 2009435 49552985 := bstep (se 2 (by rfl) ⟨18582369, by rfl⟩ : syracuseStep 49552985 = 37164739) B37164739
theorem B33035323 : Blo 2009435 33035323 := bstep (se 1 (by rfl) ⟨24776492, by rfl⟩ : syracuseStep 33035323 = 49552985) B49552985
theorem B44047097 : Blo 2009435 44047097 := bstep (se 2 (by rfl) ⟨16517661, by rfl⟩ : syracuseStep 44047097 = 33035323) B33035323
theorem B29364731 : Blo 2009435 29364731 := bstep (se 1 (by rfl) ⟨22023548, by rfl⟩ : syracuseStep 29364731 = 44047097) B44047097
theorem B19576487 : Blo 2009435 19576487 := bstep (se 1 (by rfl) ⟨14682365, by rfl⟩ : syracuseStep 19576487 = 29364731) B29364731
theorem B13050991 : Blo 2009435 13050991 := bstep (se 1 (by rfl) ⟨9788243, by rfl⟩ : syracuseStep 13050991 = 19576487) B19576487
theorem B17401321 : Blo 2009435 17401321 := bstep (se 2 (by rfl) ⟨6525495, by rfl⟩ : syracuseStep 17401321 = 13050991) B13050991
theorem B23201761 : Blo 2009435 23201761 := bstep (se 2 (by rfl) ⟨8700660, by rfl⟩ : syracuseStep 23201761 = 17401321) B17401321
theorem B30935681 : Blo 2009435 30935681 := bstep (se 2 (by rfl) ⟨11600880, by rfl⟩ : syracuseStep 30935681 = 23201761) B23201761
theorem B20623787 : Blo 2009435 20623787 := bstep (se 1 (by rfl) ⟨15467840, by rfl⟩ : syracuseStep 20623787 = 30935681) B30935681
theorem B13749191 : Blo 2009435 13749191 := bstep (se 1 (by rfl) ⟨10311893, by rfl⟩ : syracuseStep 13749191 = 20623787) B20623787
theorem B9166127 : Blo 2009435 9166127 := bstep (se 1 (by rfl) ⟨6874595, by rfl⟩ : syracuseStep 9166127 = 13749191) B13749191
theorem B24443005 : Blo 2009435 24443005 := bstep (se 3 (by rfl) ⟨4583063, by rfl⟩ : syracuseStep 24443005 = 9166127) B9166127
theorem B32590673 : Blo 2009435 32590673 := bstep (se 2 (by rfl) ⟨12221502, by rfl⟩ : syracuseStep 32590673 = 24443005) B24443005
theorem B21727115 : Blo 2009435 21727115 := bstep (se 1 (by rfl) ⟨16295336, by rfl⟩ : syracuseStep 21727115 = 32590673) B32590673
theorem B14484743 : Blo 2009435 14484743 := bstep (se 1 (by rfl) ⟨10863557, by rfl⟩ : syracuseStep 14484743 = 21727115) B21727115
theorem B9656495 : Blo 2009435 9656495 := bstep (se 1 (by rfl) ⟨7242371, by rfl⟩ : syracuseStep 9656495 = 14484743) B14484743
theorem B6437663 : Blo 2009435 6437663 := bstep (se 1 (by rfl) ⟨4828247, by rfl⟩ : syracuseStep 6437663 = 9656495) B9656495
theorem B4291775 : Blo 2009435 4291775 := bstep (se 1 (by rfl) ⟨3218831, by rfl⟩ : syracuseStep 4291775 = 6437663) B6437663
theorem B2861183 : Blo 2009435 2861183 := bstep (se 1 (by rfl) ⟨2145887, by rfl⟩ : syracuseStep 2861183 = 4291775) B4291775
theorem B7629821 : Blo 2009435 7629821 := bstep (se 3 (by rfl) ⟨1430591, by rfl⟩ : syracuseStep 7629821 = 2861183) B2861183
theorem B5086547 : Blo 2009435 5086547 := bstep (se 1 (by rfl) ⟨3814910, by rfl⟩ : syracuseStep 5086547 = 7629821) B7629821
theorem B3391031 : Blo 2009435 3391031 := bstep (se 1 (by rfl) ⟨2543273, by rfl⟩ : syracuseStep 3391031 = 5086547) B5086547
theorem B2260687 : Blo 2009435 2260687 := bstep (se 1 (by rfl) ⟨1695515, by rfl⟩ : syracuseStep 2260687 = 3391031) B3391031
theorem B3014249 : Blo 2009435 3014249 := bstep (se 2 (by rfl) ⟨1130343, by rfl⟩ : syracuseStep 3014249 = 2260687) B2260687
theorem B2009499 : Blo 2009435 2009499 := bstep (se 1 (by rfl) ⟨1507124, by rfl⟩ : syracuseStep 2009499 = 3014249) B3014249
theorem B3218837 : Blo 2009435 3218837 := bbase (se 6 (by rfl) ⟨75441, by rfl⟩ : syracuseStep 3218837 = 150883) (by norm_num)
theorem B8583565 : Blo 2009435 8583565 := bstep (se 3 (by rfl) ⟨1609418, by rfl⟩ : syracuseStep 8583565 = 3218837) B3218837
theorem B11444753 : Blo 2009435 11444753 := bstep (se 2 (by rfl) ⟨4291782, by rfl⟩ : syracuseStep 11444753 = 8583565) B8583565
theorem B7629835 : Blo 2009435 7629835 := bstep (se 1 (by rfl) ⟨5722376, by rfl⟩ : syracuseStep 7629835 = 11444753) B11444753
theorem B10173113 : Blo 2009435 10173113 := bstep (se 2 (by rfl) ⟨3814917, by rfl⟩ : syracuseStep 10173113 = 7629835) B7629835
theorem B6782075 : Blo 2009435 6782075 := bstep (se 1 (by rfl) ⟨5086556, by rfl⟩ : syracuseStep 6782075 = 10173113) B10173113
theorem B4521383 : Blo 2009435 4521383 := bstep (se 1 (by rfl) ⟨3391037, by rfl⟩ : syracuseStep 4521383 = 6782075) B6782075
theorem B3014255 : Blo 2009435 3014255 := bstep (se 1 (by rfl) ⟨2260691, by rfl⟩ : syracuseStep 3014255 = 4521383) B4521383
theorem B2009503 : Blo 2009435 2009503 := bstep (se 1 (by rfl) ⟨1507127, by rfl⟩ : syracuseStep 2009503 = 3014255) B3014255
theorem B3014261 : Blo 2009435 3014261 := bbase (se 5 (by rfl) ⟨141293, by rfl⟩ : syracuseStep 3014261 = 282587) (by norm_num)
theorem B2009507 : Blo 2009435 2009507 := bstep (se 1 (by rfl) ⟨1507130, by rfl⟩ : syracuseStep 2009507 = 3014261) B3014261
theorem B3814933 : Blo 2009435 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B5086577 : Blo 2009435 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B3391051 : Blo 2009435 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B4521401 : Blo 2009435 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B3014267 : Blo 2009435 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B2009511 : Blo 2009435 2009511 := bstep (se 1 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 2009511 = 3014267) B3014267
theorem B2260705 : Blo 2009435 2260705 := bbase (se 2 (by rfl) ⟨847764, by rfl⟩ : syracuseStep 2260705 = 1695529) (by norm_num)
theorem B3014273 : Blo 2009435 3014273 := bstep (se 2 (by rfl) ⟨1130352, by rfl⟩ : syracuseStep 3014273 = 2260705) B2260705
theorem B2009515 : Blo 2009435 2009515 := bstep (se 1 (by rfl) ⟨1507136, by rfl⟩ : syracuseStep 2009515 = 3014273) B3014273
theorem B5086597 : Blo 2009435 5086597 := bbase (se 4 (by rfl) ⟨476868, by rfl⟩ : syracuseStep 5086597 = 953737) (by norm_num)
theorem B6782129 : Blo 2009435 6782129 := bstep (se 2 (by rfl) ⟨2543298, by rfl⟩ : syracuseStep 6782129 = 5086597) B5086597
theorem B4521419 : Blo 2009435 4521419 := bstep (se 1 (by rfl) ⟨3391064, by rfl⟩ : syracuseStep 4521419 = 6782129) B6782129
theorem B3014279 : Blo 2009435 3014279 := bstep (se 1 (by rfl) ⟨2260709, by rfl⟩ : syracuseStep 3014279 = 4521419) B4521419
theorem B2009519 : Blo 2009435 2009519 := bstep (se 1 (by rfl) ⟨1507139, by rfl⟩ : syracuseStep 2009519 = 3014279) B3014279
theorem B3014285 : Blo 2009435 3014285 := bbase (se 3 (by rfl) ⟨565178, by rfl⟩ : syracuseStep 3014285 = 1130357) (by norm_num)
theorem B2009523 : Blo 2009435 2009523 := bstep (se 1 (by rfl) ⟨1507142, by rfl⟩ : syracuseStep 2009523 = 3014285) B3014285
theorem B4521437 : Blo 2009435 4521437 := bbase (se 3 (by rfl) ⟨847769, by rfl⟩ : syracuseStep 4521437 = 1695539) (by norm_num)
theorem B3014291 : Blo 2009435 3014291 := bstep (se 1 (by rfl) ⟨2260718, by rfl⟩ : syracuseStep 3014291 = 4521437) B4521437
theorem B2009527 : Blo 2009435 2009527 := bstep (se 1 (by rfl) ⟨1507145, by rfl⟩ : syracuseStep 2009527 = 3014291) B3014291
theorem B3391085 : Blo 2009435 3391085 := bbase (se 3 (by rfl) ⟨635828, by rfl⟩ : syracuseStep 3391085 = 1271657) (by norm_num)
theorem B2260723 : Blo 2009435 2260723 := bstep (se 1 (by rfl) ⟨1695542, by rfl⟩ : syracuseStep 2260723 = 3391085) B3391085
theorem B3014297 : Blo 2009435 3014297 := bstep (se 2 (by rfl) ⟨1130361, by rfl⟩ : syracuseStep 3014297 = 2260723) B2260723
theorem B2009531 : Blo 2009435 2009531 := bstep (se 1 (by rfl) ⟨1507148, by rfl⟩ : syracuseStep 2009531 = 3014297) B3014297
theorem B2036953 : Blo 2009435 2036953 := bbase (se 2 (by rfl) ⟨763857, by rfl⟩ : syracuseStep 2036953 = 1527715) (by norm_num)
theorem B2715937 : Blo 2009435 2715937 := bstep (se 2 (by rfl) ⟨1018476, by rfl⟩ : syracuseStep 2715937 = 2036953) B2036953
theorem B14484997 : Blo 2009435 14484997 := bstep (se 4 (by rfl) ⟨1357968, by rfl⟩ : syracuseStep 14484997 = 2715937) B2715937
theorem B19313329 : Blo 2009435 19313329 := bstep (se 2 (by rfl) ⟨7242498, by rfl⟩ : syracuseStep 19313329 = 14484997) B14484997
theorem B25751105 : Blo 2009435 25751105 := bstep (se 2 (by rfl) ⟨9656664, by rfl⟩ : syracuseStep 25751105 = 19313329) B19313329
theorem B17167403 : Blo 2009435 17167403 := bstep (se 1 (by rfl) ⟨12875552, by rfl⟩ : syracuseStep 17167403 = 25751105) B25751105
theorem B11444935 : Blo 2009435 11444935 := bstep (se 1 (by rfl) ⟨8583701, by rfl⟩ : syracuseStep 11444935 = 17167403) B17167403
theorem B15259913 : Blo 2009435 15259913 := bstep (se 2 (by rfl) ⟨5722467, by rfl⟩ : syracuseStep 15259913 = 11444935) B11444935
theorem B10173275 : Blo 2009435 10173275 := bstep (se 1 (by rfl) ⟨7629956, by rfl⟩ : syracuseStep 10173275 = 15259913) B15259913
theorem B6782183 : Blo 2009435 6782183 := bstep (se 1 (by rfl) ⟨5086637, by rfl⟩ : syracuseStep 6782183 = 10173275) B10173275
theorem B4521455 : Blo 2009435 4521455 := bstep (se 1 (by rfl) ⟨3391091, by rfl⟩ : syracuseStep 4521455 = 6782183) B6782183
theorem B3014303 : Blo 2009435 3014303 := bstep (se 1 (by rfl) ⟨2260727, by rfl⟩ : syracuseStep 3014303 = 4521455) B4521455
theorem B2009535 : Blo 2009435 2009535 := bstep (se 1 (by rfl) ⟨1507151, by rfl⟩ : syracuseStep 2009535 = 3014303) B3014303
theorem B3014309 : Blo 2009435 3014309 := bbase (se 4 (by rfl) ⟨282591, by rfl⟩ : syracuseStep 3014309 = 565183) (by norm_num)
theorem B2009539 : Blo 2009435 2009539 := bstep (se 1 (by rfl) ⟨1507154, by rfl⟩ : syracuseStep 2009539 = 3014309) B3014309
theorem B2543329 : Blo 2009435 2543329 := bbase (se 2 (by rfl) ⟨953748, by rfl⟩ : syracuseStep 2543329 = 1907497) (by norm_num)
theorem B3391105 : Blo 2009435 3391105 := bstep (se 2 (by rfl) ⟨1271664, by rfl⟩ : syracuseStep 3391105 = 2543329) B2543329
theorem B4521473 : Blo 2009435 4521473 := bstep (se 2 (by rfl) ⟨1695552, by rfl⟩ : syracuseStep 4521473 = 3391105) B3391105
theorem B3014315 : Blo 2009435 3014315 := bstep (se 1 (by rfl) ⟨2260736, by rfl⟩ : syracuseStep 3014315 = 4521473) B4521473
theorem B2009543 : Blo 2009435 2009543 := bstep (se 1 (by rfl) ⟨1507157, by rfl⟩ : syracuseStep 2009543 = 3014315) B3014315
theorem B2260741 : Blo 2009435 2260741 := bbase (se 4 (by rfl) ⟨211944, by rfl⟩ : syracuseStep 2260741 = 423889) (by norm_num)
theorem B3014321 : Blo 2009435 3014321 := bstep (se 2 (by rfl) ⟨1130370, by rfl⟩ : syracuseStep 3014321 = 2260741) B2260741
theorem B2009547 : Blo 2009435 2009547 := bstep (se 1 (by rfl) ⟨1507160, by rfl⟩ : syracuseStep 2009547 = 3014321) B3014321
theorem B4828373 : Blo 2009435 4828373 := bbase (se 7 (by rfl) ⟨56582, by rfl⟩ : syracuseStep 4828373 = 113165) (by norm_num)
theorem B3218915 : Blo 2009435 3218915 := bstep (se 1 (by rfl) ⟨2414186, by rfl⟩ : syracuseStep 3218915 = 4828373) B4828373
theorem B2145943 : Blo 2009435 2145943 := bstep (se 1 (by rfl) ⟨1609457, by rfl⟩ : syracuseStep 2145943 = 3218915) B3218915
theorem B2861257 : Blo 2009435 2861257 := bstep (se 2 (by rfl) ⟨1072971, by rfl⟩ : syracuseStep 2861257 = 2145943) B2145943
theorem B3815009 : Blo 2009435 3815009 := bstep (se 2 (by rfl) ⟨1430628, by rfl⟩ : syracuseStep 3815009 = 2861257) B2861257
theorem B2543339 : Blo 2009435 2543339 := bstep (se 1 (by rfl) ⟨1907504, by rfl⟩ : syracuseStep 2543339 = 3815009) B3815009
theorem B6782237 : Blo 2009435 6782237 := bstep (se 3 (by rfl) ⟨1271669, by rfl⟩ : syracuseStep 6782237 = 2543339) B2543339
theorem B4521491 : Blo 2009435 4521491 := bstep (se 1 (by rfl) ⟨3391118, by rfl⟩ : syracuseStep 4521491 = 6782237) B6782237
theorem B3014327 : Blo 2009435 3014327 := bstep (se 1 (by rfl) ⟨2260745, by rfl⟩ : syracuseStep 3014327 = 4521491) B4521491
theorem B2009551 : Blo 2009435 2009551 := bstep (se 1 (by rfl) ⟨1507163, by rfl⟩ : syracuseStep 2009551 = 3014327) B3014327
theorem B3014333 : Blo 2009435 3014333 := bbase (se 3 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 3014333 = 1130375) (by norm_num)
theorem B2009555 : Blo 2009435 2009555 := bstep (se 1 (by rfl) ⟨1507166, by rfl⟩ : syracuseStep 2009555 = 3014333) B3014333
theorem B4521509 : Blo 2009435 4521509 := bbase (se 4 (by rfl) ⟨423891, by rfl⟩ : syracuseStep 4521509 = 847783) (by norm_num)
theorem B3014339 : Blo 2009435 3014339 := bstep (se 1 (by rfl) ⟨2260754, by rfl⟩ : syracuseStep 3014339 = 4521509) B4521509
theorem B2009559 : Blo 2009435 2009559 := bstep (se 1 (by rfl) ⟨1507169, by rfl⟩ : syracuseStep 2009559 = 3014339) B3014339
theorem B5086709 : Blo 2009435 5086709 := bbase (se 5 (by rfl) ⟨238439, by rfl⟩ : syracuseStep 5086709 = 476879) (by norm_num)
theorem B3391139 : Blo 2009435 3391139 := bstep (se 1 (by rfl) ⟨2543354, by rfl⟩ : syracuseStep 3391139 = 5086709) B5086709
theorem B2260759 : Blo 2009435 2260759 := bstep (se 1 (by rfl) ⟨1695569, by rfl⟩ : syracuseStep 2260759 = 3391139) B3391139
theorem B3014345 : Blo 2009435 3014345 := bstep (se 2 (by rfl) ⟨1130379, by rfl⟩ : syracuseStep 3014345 = 2260759) B2260759
theorem B2009563 : Blo 2009435 2009563 := bstep (se 1 (by rfl) ⟨1507172, by rfl⟩ : syracuseStep 2009563 = 3014345) B3014345
theorem B3437413 : Blo 2009435 3437413 := bbase (se 4 (by rfl) ⟨322257, by rfl⟩ : syracuseStep 3437413 = 644515) (by norm_num)
theorem B73331477 : Blo 2009435 73331477 := bstep (se 6 (by rfl) ⟨1718706, by rfl⟩ : syracuseStep 73331477 = 3437413) B3437413
theorem B48887651 : Blo 2009435 48887651 := bstep (se 1 (by rfl) ⟨36665738, by rfl⟩ : syracuseStep 48887651 = 73331477) B73331477
theorem B32591767 : Blo 2009435 32591767 := bstep (se 1 (by rfl) ⟨24443825, by rfl⟩ : syracuseStep 32591767 = 48887651) B48887651
theorem B43455689 : Blo 2009435 43455689 := bstep (se 2 (by rfl) ⟨16295883, by rfl⟩ : syracuseStep 43455689 = 32591767) B32591767
theorem B28970459 : Blo 2009435 28970459 := bstep (se 1 (by rfl) ⟨21727844, by rfl⟩ : syracuseStep 28970459 = 43455689) B43455689
theorem B19313639 : Blo 2009435 19313639 := bstep (se 1 (by rfl) ⟨14485229, by rfl⟩ : syracuseStep 19313639 = 28970459) B28970459
theorem B12875759 : Blo 2009435 12875759 := bstep (se 1 (by rfl) ⟨9656819, by rfl⟩ : syracuseStep 12875759 = 19313639) B19313639
theorem B8583839 : Blo 2009435 8583839 := bstep (se 1 (by rfl) ⟨6437879, by rfl⟩ : syracuseStep 8583839 = 12875759) B12875759
theorem B5722559 : Blo 2009435 5722559 := bstep (se 1 (by rfl) ⟨4291919, by rfl⟩ : syracuseStep 5722559 = 8583839) B8583839
theorem B3815039 : Blo 2009435 3815039 := bstep (se 1 (by rfl) ⟨2861279, by rfl⟩ : syracuseStep 3815039 = 5722559) B5722559
theorem B10173437 : Blo 2009435 10173437 := bstep (se 3 (by rfl) ⟨1907519, by rfl⟩ : syracuseStep 10173437 = 3815039) B3815039
theorem B6782291 : Blo 2009435 6782291 := bstep (se 1 (by rfl) ⟨5086718, by rfl⟩ : syracuseStep 6782291 = 10173437) B10173437
theorem B4521527 : Blo 2009435 4521527 := bstep (se 1 (by rfl) ⟨3391145, by rfl⟩ : syracuseStep 4521527 = 6782291) B6782291
theorem B3014351 : Blo 2009435 3014351 := bstep (se 1 (by rfl) ⟨2260763, by rfl⟩ : syracuseStep 3014351 = 4521527) B4521527
theorem B2009567 : Blo 2009435 2009567 := bstep (se 1 (by rfl) ⟨1507175, by rfl⟩ : syracuseStep 2009567 = 3014351) B3014351
theorem B3014357 : Blo 2009435 3014357 := bbase (se 7 (by rfl) ⟨35324, by rfl⟩ : syracuseStep 3014357 = 70649) (by norm_num)
theorem B2009571 : Blo 2009435 2009571 := bstep (se 1 (by rfl) ⟨1507178, by rfl⟩ : syracuseStep 2009571 = 3014357) B3014357
theorem B4073989 : Blo 2009435 4073989 := bbase (se 4 (by rfl) ⟨381936, by rfl⟩ : syracuseStep 4073989 = 763873) (by norm_num)
theorem B5431985 : Blo 2009435 5431985 := bstep (se 2 (by rfl) ⟨2036994, by rfl⟩ : syracuseStep 5431985 = 4073989) B4073989
theorem B3621323 : Blo 2009435 3621323 := bstep (se 1 (by rfl) ⟨2715992, by rfl⟩ : syracuseStep 3621323 = 5431985) B5431985
theorem B2414215 : Blo 2009435 2414215 := bstep (se 1 (by rfl) ⟨1810661, by rfl⟩ : syracuseStep 2414215 = 3621323) B3621323
theorem B3218953 : Blo 2009435 3218953 := bstep (se 2 (by rfl) ⟨1207107, by rfl⟩ : syracuseStep 3218953 = 2414215) B2414215
theorem B4291937 : Blo 2009435 4291937 := bstep (se 2 (by rfl) ⟨1609476, by rfl⟩ : syracuseStep 4291937 = 3218953) B3218953
theorem B2861291 : Blo 2009435 2861291 := bstep (se 1 (by rfl) ⟨2145968, by rfl⟩ : syracuseStep 2861291 = 4291937) B4291937
theorem B7630109 : Blo 2009435 7630109 := bstep (se 3 (by rfl) ⟨1430645, by rfl⟩ : syracuseStep 7630109 = 2861291) B2861291
theorem B5086739 : Blo 2009435 5086739 := bstep (se 1 (by rfl) ⟨3815054, by rfl⟩ : syracuseStep 5086739 = 7630109) B7630109
theorem B3391159 : Blo 2009435 3391159 := bstep (se 1 (by rfl) ⟨2543369, by rfl⟩ : syracuseStep 3391159 = 5086739) B5086739
theorem B4521545 : Blo 2009435 4521545 := bstep (se 2 (by rfl) ⟨1695579, by rfl⟩ : syracuseStep 4521545 = 3391159) B3391159
theorem B3014363 : Blo 2009435 3014363 := bstep (se 1 (by rfl) ⟨2260772, by rfl⟩ : syracuseStep 3014363 = 4521545) B4521545
theorem B2009575 : Blo 2009435 2009575 := bstep (se 1 (by rfl) ⟨1507181, by rfl⟩ : syracuseStep 2009575 = 3014363) B3014363
theorem B2260777 : Blo 2009435 2260777 := bbase (se 2 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 2260777 = 1695583) (by norm_num)
theorem B3014369 : Blo 2009435 3014369 := bstep (se 2 (by rfl) ⟨1130388, by rfl⟩ : syracuseStep 3014369 = 2260777) B2260777
theorem B2009579 : Blo 2009435 2009579 := bstep (se 1 (by rfl) ⟨1507184, by rfl⟩ : syracuseStep 2009579 = 3014369) B3014369
theorem B12875861 : Blo 2009435 12875861 := bbase (se 8 (by rfl) ⟨75444, by rfl⟩ : syracuseStep 12875861 = 150889) (by norm_num)
theorem B8583907 : Blo 2009435 8583907 := bstep (se 1 (by rfl) ⟨6437930, by rfl⟩ : syracuseStep 8583907 = 12875861) B12875861
theorem B11445209 : Blo 2009435 11445209 := bstep (se 2 (by rfl) ⟨4291953, by rfl⟩ : syracuseStep 11445209 = 8583907) B8583907
theorem B7630139 : Blo 2009435 7630139 := bstep (se 1 (by rfl) ⟨5722604, by rfl⟩ : syracuseStep 7630139 = 11445209) B11445209
theorem B5086759 : Blo 2009435 5086759 := bstep (se 1 (by rfl) ⟨3815069, by rfl⟩ : syracuseStep 5086759 = 7630139) B7630139
theorem B6782345 : Blo 2009435 6782345 := bstep (se 2 (by rfl) ⟨2543379, by rfl⟩ : syracuseStep 6782345 = 5086759) B5086759
theorem B4521563 : Blo 2009435 4521563 := bstep (se 1 (by rfl) ⟨3391172, by rfl⟩ : syracuseStep 4521563 = 6782345) B6782345
theorem B3014375 : Blo 2009435 3014375 := bstep (se 1 (by rfl) ⟨2260781, by rfl⟩ : syracuseStep 3014375 = 4521563) B4521563
theorem B2009583 : Blo 2009435 2009583 := bstep (se 1 (by rfl) ⟨1507187, by rfl⟩ : syracuseStep 2009583 = 3014375) B3014375
theorem B3014381 : Blo 2009435 3014381 := bbase (se 3 (by rfl) ⟨565196, by rfl⟩ : syracuseStep 3014381 = 1130393) (by norm_num)
theorem B2009587 : Blo 2009435 2009587 := bstep (se 1 (by rfl) ⟨1507190, by rfl⟩ : syracuseStep 2009587 = 3014381) B3014381
theorem B4521581 : Blo 2009435 4521581 := bbase (se 3 (by rfl) ⟨847796, by rfl⟩ : syracuseStep 4521581 = 1695593) (by norm_num)
theorem B3014387 : Blo 2009435 3014387 := bstep (se 1 (by rfl) ⟨2260790, by rfl⟩ : syracuseStep 3014387 = 4521581) B4521581
theorem B2009591 : Blo 2009435 2009591 := bstep (se 1 (by rfl) ⟨1507193, by rfl⟩ : syracuseStep 2009591 = 3014387) B3014387
theorem B3815093 : Blo 2009435 3815093 := bbase (se 5 (by rfl) ⟨178832, by rfl⟩ : syracuseStep 3815093 = 357665) (by norm_num)
theorem B2543395 : Blo 2009435 2543395 := bstep (se 1 (by rfl) ⟨1907546, by rfl⟩ : syracuseStep 2543395 = 3815093) B3815093
theorem B3391193 : Blo 2009435 3391193 := bstep (se 2 (by rfl) ⟨1271697, by rfl⟩ : syracuseStep 3391193 = 2543395) B2543395
theorem B2260795 : Blo 2009435 2260795 := bstep (se 1 (by rfl) ⟨1695596, by rfl⟩ : syracuseStep 2260795 = 3391193) B3391193
theorem B3014393 : Blo 2009435 3014393 := bstep (se 2 (by rfl) ⟨1130397, by rfl⟩ : syracuseStep 3014393 = 2260795) B2260795
theorem B2009595 : Blo 2009435 2009595 := bstep (se 1 (by rfl) ⟨1507196, by rfl⟩ : syracuseStep 2009595 = 3014393) B3014393
theorem B3262909 : Blo 2009435 3262909 := bbase (se 3 (by rfl) ⟨611795, by rfl⟩ : syracuseStep 3262909 = 1223591) (by norm_num)
theorem B4350545 : Blo 2009435 4350545 := bstep (se 2 (by rfl) ⟨1631454, by rfl⟩ : syracuseStep 4350545 = 3262909) B3262909
theorem B2900363 : Blo 2009435 2900363 := bstep (se 1 (by rfl) ⟨2175272, by rfl⟩ : syracuseStep 2900363 = 4350545) B4350545
theorem B7734301 : Blo 2009435 7734301 := bstep (se 3 (by rfl) ⟨1450181, by rfl⟩ : syracuseStep 7734301 = 2900363) B2900363
theorem B164998421 : Blo 2009435 164998421 := bstep (se 6 (by rfl) ⟨3867150, by rfl⟩ : syracuseStep 164998421 = 7734301) B7734301
theorem B109998947 : Blo 2009435 109998947 := bstep (se 1 (by rfl) ⟨82499210, by rfl⟩ : syracuseStep 109998947 = 164998421) B164998421
theorem B73332631 : Blo 2009435 73332631 := bstep (se 1 (by rfl) ⟨54999473, by rfl⟩ : syracuseStep 73332631 = 109998947) B109998947
theorem B97776841 : Blo 2009435 97776841 := bstep (se 2 (by rfl) ⟨36666315, by rfl⟩ : syracuseStep 97776841 = 73332631) B73332631
theorem B130369121 : Blo 2009435 130369121 := bstep (se 2 (by rfl) ⟨48888420, by rfl⟩ : syracuseStep 130369121 = 97776841) B97776841
theorem B86912747 : Blo 2009435 86912747 := bstep (se 1 (by rfl) ⟨65184560, by rfl⟩ : syracuseStep 86912747 = 130369121) B130369121
theorem B57941831 : Blo 2009435 57941831 := bstep (se 1 (by rfl) ⟨43456373, by rfl⟩ : syracuseStep 57941831 = 86912747) B86912747
theorem B38627887 : Blo 2009435 38627887 := bstep (se 1 (by rfl) ⟨28970915, by rfl⟩ : syracuseStep 38627887 = 57941831) B57941831
theorem B51503849 : Blo 2009435 51503849 := bstep (se 2 (by rfl) ⟨19313943, by rfl⟩ : syracuseStep 51503849 = 38627887) B38627887
theorem B34335899 : Blo 2009435 34335899 := bstep (se 1 (by rfl) ⟨25751924, by rfl⟩ : syracuseStep 34335899 = 51503849) B51503849
theorem B22890599 : Blo 2009435 22890599 := bstep (se 1 (by rfl) ⟨17167949, by rfl⟩ : syracuseStep 22890599 = 34335899) B34335899
theorem B15260399 : Blo 2009435 15260399 := bstep (se 1 (by rfl) ⟨11445299, by rfl⟩ : syracuseStep 15260399 = 22890599) B22890599
theorem B10173599 : Blo 2009435 10173599 := bstep (se 1 (by rfl) ⟨7630199, by rfl⟩ : syracuseStep 10173599 = 15260399) B15260399
theorem B6782399 : Blo 2009435 6782399 := bstep (se 1 (by rfl) ⟨5086799, by rfl⟩ : syracuseStep 6782399 = 10173599) B10173599
theorem B4521599 : Blo 2009435 4521599 := bstep (se 1 (by rfl) ⟨3391199, by rfl⟩ : syracuseStep 4521599 = 6782399) B6782399
theorem B3014399 : Blo 2009435 3014399 := bstep (se 1 (by rfl) ⟨2260799, by rfl⟩ : syracuseStep 3014399 = 4521599) B4521599
theorem B2009599 : Blo 2009435 2009599 := bstep (se 1 (by rfl) ⟨1507199, by rfl⟩ : syracuseStep 2009599 = 3014399) B3014399
theorem B3014405 : Blo 2009435 3014405 := bbase (se 4 (by rfl) ⟨282600, by rfl⟩ : syracuseStep 3014405 = 565201) (by norm_num)
theorem B2009603 : Blo 2009435 2009603 := bstep (se 1 (by rfl) ⟨1507202, by rfl⟩ : syracuseStep 2009603 = 3014405) B3014405
theorem B3391213 : Blo 2009435 3391213 := bbase (se 3 (by rfl) ⟨635852, by rfl⟩ : syracuseStep 3391213 = 1271705) (by norm_num)
theorem B4521617 : Blo 2009435 4521617 := bstep (se 2 (by rfl) ⟨1695606, by rfl⟩ : syracuseStep 4521617 = 3391213) B3391213
theorem B3014411 : Blo 2009435 3014411 := bstep (se 1 (by rfl) ⟨2260808, by rfl⟩ : syracuseStep 3014411 = 4521617) B4521617
theorem B2009607 : Blo 2009435 2009607 := bstep (se 1 (by rfl) ⟨1507205, by rfl⟩ : syracuseStep 2009607 = 3014411) B3014411
theorem B2260813 : Blo 2009435 2260813 := bbase (se 3 (by rfl) ⟨423902, by rfl⟩ : syracuseStep 2260813 = 847805) (by norm_num)
theorem B3014417 : Blo 2009435 3014417 := bstep (se 2 (by rfl) ⟨1130406, by rfl⟩ : syracuseStep 3014417 = 2260813) B2260813
theorem B2009611 : Blo 2009435 2009611 := bstep (se 1 (by rfl) ⟨1507208, by rfl⟩ : syracuseStep 2009611 = 3014417) B3014417
theorem B6782453 : Blo 2009435 6782453 := bbase (se 5 (by rfl) ⟨317927, by rfl⟩ : syracuseStep 6782453 = 635855) (by norm_num)
theorem B4521635 : Blo 2009435 4521635 := bstep (se 1 (by rfl) ⟨3391226, by rfl⟩ : syracuseStep 4521635 = 6782453) B6782453
theorem B3014423 : Blo 2009435 3014423 := bstep (se 1 (by rfl) ⟨2260817, by rfl⟩ : syracuseStep 3014423 = 4521635) B4521635
theorem B2009615 : Blo 2009435 2009615 := bstep (se 1 (by rfl) ⟨1507211, by rfl⟩ : syracuseStep 2009615 = 3014423) B3014423
theorem B3014429 : Blo 2009435 3014429 := bbase (se 3 (by rfl) ⟨565205, by rfl⟩ : syracuseStep 3014429 = 1130411) (by norm_num)
theorem B2009619 : Blo 2009435 2009619 := bstep (se 1 (by rfl) ⟨1507214, by rfl⟩ : syracuseStep 2009619 = 3014429) B3014429
theorem B4521653 : Blo 2009435 4521653 := bbase (se 5 (by rfl) ⟨211952, by rfl⟩ : syracuseStep 4521653 = 423905) (by norm_num)
theorem B3014435 : Blo 2009435 3014435 := bstep (se 1 (by rfl) ⟨2260826, by rfl⟩ : syracuseStep 3014435 = 4521653) B4521653
theorem B2009623 : Blo 2009435 2009623 := bstep (se 1 (by rfl) ⟨1507217, by rfl⟩ : syracuseStep 2009623 = 3014435) B3014435
theorem B11445461 : Blo 2009435 11445461 := bbase (se 7 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 11445461 = 268253) (by norm_num)
theorem B7630307 : Blo 2009435 7630307 := bstep (se 1 (by rfl) ⟨5722730, by rfl⟩ : syracuseStep 7630307 = 11445461) B11445461
theorem B5086871 : Blo 2009435 5086871 := bstep (se 1 (by rfl) ⟨3815153, by rfl⟩ : syracuseStep 5086871 = 7630307) B7630307
theorem B3391247 : Blo 2009435 3391247 := bstep (se 1 (by rfl) ⟨2543435, by rfl⟩ : syracuseStep 3391247 = 5086871) B5086871
theorem B2260831 : Blo 2009435 2260831 := bstep (se 1 (by rfl) ⟨1695623, by rfl⟩ : syracuseStep 2260831 = 3391247) B3391247
theorem B3014441 : Blo 2009435 3014441 := bstep (se 2 (by rfl) ⟨1130415, by rfl⟩ : syracuseStep 3014441 = 2260831) B2260831
theorem B2009627 : Blo 2009435 2009627 := bstep (se 1 (by rfl) ⟨1507220, by rfl⟩ : syracuseStep 2009627 = 3014441) B3014441
theorem B5722741 : Blo 2009435 5722741 := bbase (se 5 (by rfl) ⟨268253, by rfl⟩ : syracuseStep 5722741 = 536507) (by norm_num)
theorem B7630321 : Blo 2009435 7630321 := bstep (se 2 (by rfl) ⟨2861370, by rfl⟩ : syracuseStep 7630321 = 5722741) B5722741
theorem B10173761 : Blo 2009435 10173761 := bstep (se 2 (by rfl) ⟨3815160, by rfl⟩ : syracuseStep 10173761 = 7630321) B7630321
theorem B6782507 : Blo 2009435 6782507 := bstep (se 1 (by rfl) ⟨5086880, by rfl⟩ : syracuseStep 6782507 = 10173761) B10173761
theorem B4521671 : Blo 2009435 4521671 := bstep (se 1 (by rfl) ⟨3391253, by rfl⟩ : syracuseStep 4521671 = 6782507) B6782507
theorem B3014447 : Blo 2009435 3014447 := bstep (se 1 (by rfl) ⟨2260835, by rfl⟩ : syracuseStep 3014447 = 4521671) B4521671
theorem B2009631 : Blo 2009435 2009631 := bstep (se 1 (by rfl) ⟨1507223, by rfl⟩ : syracuseStep 2009631 = 3014447) B3014447
theorem B3014453 : Blo 2009435 3014453 := bbase (se 5 (by rfl) ⟨141302, by rfl⟩ : syracuseStep 3014453 = 282605) (by norm_num)
theorem B2009635 : Blo 2009435 2009635 := bstep (se 1 (by rfl) ⟨1507226, by rfl⟩ : syracuseStep 2009635 = 3014453) B3014453
theorem B5086901 : Blo 2009435 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B3391267 : Blo 2009435 3391267 := bstep (se 1 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 3391267 = 5086901) B5086901
theorem B4521689 : Blo 2009435 4521689 := bstep (se 2 (by rfl) ⟨1695633, by rfl⟩ : syracuseStep 4521689 = 3391267) B3391267
theorem B3014459 : Blo 2009435 3014459 := bstep (se 1 (by rfl) ⟨2260844, by rfl⟩ : syracuseStep 3014459 = 4521689) B4521689
theorem B2009639 : Blo 2009435 2009639 := bstep (se 1 (by rfl) ⟨1507229, by rfl⟩ : syracuseStep 2009639 = 3014459) B3014459
theorem B2260849 : Blo 2009435 2260849 := bbase (se 2 (by rfl) ⟨847818, by rfl⟩ : syracuseStep 2260849 = 1695637) (by norm_num)
theorem B3014465 : Blo 2009435 3014465 := bstep (se 2 (by rfl) ⟨1130424, by rfl⟩ : syracuseStep 3014465 = 2260849) B2260849
theorem B2009643 : Blo 2009435 2009643 := bstep (se 1 (by rfl) ⟨1507232, by rfl⟩ : syracuseStep 2009643 = 3014465) B3014465
theorem B8584181 : Blo 2009435 8584181 := bbase (se 5 (by rfl) ⟨402383, by rfl⟩ : syracuseStep 8584181 = 804767) (by norm_num)
theorem B5722787 : Blo 2009435 5722787 := bstep (se 1 (by rfl) ⟨4292090, by rfl⟩ : syracuseStep 5722787 = 8584181) B8584181
theorem B3815191 : Blo 2009435 3815191 := bstep (se 1 (by rfl) ⟨2861393, by rfl⟩ : syracuseStep 3815191 = 5722787) B5722787
theorem B5086921 : Blo 2009435 5086921 := bstep (se 2 (by rfl) ⟨1907595, by rfl⟩ : syracuseStep 5086921 = 3815191) B3815191
theorem B6782561 : Blo 2009435 6782561 := bstep (se 2 (by rfl) ⟨2543460, by rfl⟩ : syracuseStep 6782561 = 5086921) B5086921
theorem B4521707 : Blo 2009435 4521707 := bstep (se 1 (by rfl) ⟨3391280, by rfl⟩ : syracuseStep 4521707 = 6782561) B6782561
theorem B3014471 : Blo 2009435 3014471 := bstep (se 1 (by rfl) ⟨2260853, by rfl⟩ : syracuseStep 3014471 = 4521707) B4521707
theorem B2009647 : Blo 2009435 2009647 := bstep (se 1 (by rfl) ⟨1507235, by rfl⟩ : syracuseStep 2009647 = 3014471) B3014471
theorem B3014477 : Blo 2009435 3014477 := bbase (se 3 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 3014477 = 1130429) (by norm_num)
theorem B2009651 : Blo 2009435 2009651 := bstep (se 1 (by rfl) ⟨1507238, by rfl⟩ : syracuseStep 2009651 = 3014477) B3014477
theorem B4521725 : Blo 2009435 4521725 := bbase (se 3 (by rfl) ⟨847823, by rfl⟩ : syracuseStep 4521725 = 1695647) (by norm_num)
theorem B3014483 : Blo 2009435 3014483 := bstep (se 1 (by rfl) ⟨2260862, by rfl⟩ : syracuseStep 3014483 = 4521725) B4521725
theorem B2009655 : Blo 2009435 2009655 := bstep (se 1 (by rfl) ⟨1507241, by rfl⟩ : syracuseStep 2009655 = 3014483) B3014483
theorem B3391301 : Blo 2009435 3391301 := bbase (se 4 (by rfl) ⟨317934, by rfl⟩ : syracuseStep 3391301 = 635869) (by norm_num)
theorem B2260867 : Blo 2009435 2260867 := bstep (se 1 (by rfl) ⟨1695650, by rfl⟩ : syracuseStep 2260867 = 3391301) B3391301
theorem B3014489 : Blo 2009435 3014489 := bstep (se 2 (by rfl) ⟨1130433, by rfl⟩ : syracuseStep 3014489 = 2260867) B2260867
theorem B2009659 : Blo 2009435 2009659 := bstep (se 1 (by rfl) ⟨1507244, by rfl⟩ : syracuseStep 2009659 = 3014489) B3014489
theorem B15260885 : Blo 2009435 15260885 := bbase (se 7 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 15260885 = 357677) (by norm_num)
theorem B10173923 : Blo 2009435 10173923 := bstep (se 1 (by rfl) ⟨7630442, by rfl⟩ : syracuseStep 10173923 = 15260885) B15260885
theorem B6782615 : Blo 2009435 6782615 := bstep (se 1 (by rfl) ⟨5086961, by rfl⟩ : syracuseStep 6782615 = 10173923) B10173923
theorem B4521743 : Blo 2009435 4521743 := bstep (se 1 (by rfl) ⟨3391307, by rfl⟩ : syracuseStep 4521743 = 6782615) B6782615
theorem B3014495 : Blo 2009435 3014495 := bstep (se 1 (by rfl) ⟨2260871, by rfl⟩ : syracuseStep 3014495 = 4521743) B4521743
theorem B2009663 : Blo 2009435 2009663 := bstep (se 1 (by rfl) ⟨1507247, by rfl⟩ : syracuseStep 2009663 = 3014495) B3014495
theorem B3014501 : Blo 2009435 3014501 := bbase (se 4 (by rfl) ⟨282609, by rfl⟩ : syracuseStep 3014501 = 565219) (by norm_num)
theorem B2009667 : Blo 2009435 2009667 := bstep (se 1 (by rfl) ⟨1507250, by rfl⟩ : syracuseStep 2009667 = 3014501) B3014501
theorem B3815237 : Blo 2009435 3815237 := bbase (se 4 (by rfl) ⟨357678, by rfl⟩ : syracuseStep 3815237 = 715357) (by norm_num)
theorem B2543491 : Blo 2009435 2543491 := bstep (se 1 (by rfl) ⟨1907618, by rfl⟩ : syracuseStep 2543491 = 3815237) B3815237
theorem B3391321 : Blo 2009435 3391321 := bstep (se 2 (by rfl) ⟨1271745, by rfl⟩ : syracuseStep 3391321 = 2543491) B2543491
theorem B4521761 : Blo 2009435 4521761 := bstep (se 2 (by rfl) ⟨1695660, by rfl⟩ : syracuseStep 4521761 = 3391321) B3391321
theorem B3014507 : Blo 2009435 3014507 := bstep (se 1 (by rfl) ⟨2260880, by rfl⟩ : syracuseStep 3014507 = 4521761) B4521761
theorem B2009671 : Blo 2009435 2009671 := bstep (se 1 (by rfl) ⟨1507253, by rfl⟩ : syracuseStep 2009671 = 3014507) B3014507
theorem B2260885 : Blo 2009435 2260885 := bbase (se 6 (by rfl) ⟨52989, by rfl⟩ : syracuseStep 2260885 = 105979) (by norm_num)
theorem B3014513 : Blo 2009435 3014513 := bstep (se 2 (by rfl) ⟨1130442, by rfl⟩ : syracuseStep 3014513 = 2260885) B2260885
theorem B2009675 : Blo 2009435 2009675 := bstep (se 1 (by rfl) ⟨1507256, by rfl⟩ : syracuseStep 2009675 = 3014513) B3014513
theorem B2543501 : Blo 2009435 2543501 := bbase (se 3 (by rfl) ⟨476906, by rfl⟩ : syracuseStep 2543501 = 953813) (by norm_num)
theorem B6782669 : Blo 2009435 6782669 := bstep (se 3 (by rfl) ⟨1271750, by rfl⟩ : syracuseStep 6782669 = 2543501) B2543501
theorem B4521779 : Blo 2009435 4521779 := bstep (se 1 (by rfl) ⟨3391334, by rfl⟩ : syracuseStep 4521779 = 6782669) B6782669
theorem B3014519 : Blo 2009435 3014519 := bstep (se 1 (by rfl) ⟨2260889, by rfl⟩ : syracuseStep 3014519 = 4521779) B4521779
theorem B2009679 : Blo 2009435 2009679 := bstep (se 1 (by rfl) ⟨1507259, by rfl⟩ : syracuseStep 2009679 = 3014519) B3014519
theorem B3014525 : Blo 2009435 3014525 := bbase (se 3 (by rfl) ⟨565223, by rfl⟩ : syracuseStep 3014525 = 1130447) (by norm_num)
theorem B2009683 : Blo 2009435 2009683 := bstep (se 1 (by rfl) ⟨1507262, by rfl⟩ : syracuseStep 2009683 = 3014525) B3014525
theorem B4521797 : Blo 2009435 4521797 := bbase (se 4 (by rfl) ⟨423918, by rfl⟩ : syracuseStep 4521797 = 847837) (by norm_num)
theorem B3014531 : Blo 2009435 3014531 := bstep (se 1 (by rfl) ⟨2260898, by rfl⟩ : syracuseStep 3014531 = 4521797) B4521797
theorem B2009687 : Blo 2009435 2009687 := bstep (se 1 (by rfl) ⟨1507265, by rfl⟩ : syracuseStep 2009687 = 3014531) B3014531
theorem B4828709 : Blo 2009435 4828709 := bbase (se 4 (by rfl) ⟨452691, by rfl⟩ : syracuseStep 4828709 = 905383) (by norm_num)
theorem B3219139 : Blo 2009435 3219139 := bstep (se 1 (by rfl) ⟨2414354, by rfl⟩ : syracuseStep 3219139 = 4828709) B4828709
theorem B4292185 : Blo 2009435 4292185 := bstep (se 2 (by rfl) ⟨1609569, by rfl⟩ : syracuseStep 4292185 = 3219139) B3219139
theorem B5722913 : Blo 2009435 5722913 := bstep (se 2 (by rfl) ⟨2146092, by rfl⟩ : syracuseStep 5722913 = 4292185) B4292185
theorem B3815275 : Blo 2009435 3815275 := bstep (se 1 (by rfl) ⟨2861456, by rfl⟩ : syracuseStep 3815275 = 5722913) B5722913
theorem B5087033 : Blo 2009435 5087033 := bstep (se 2 (by rfl) ⟨1907637, by rfl⟩ : syracuseStep 5087033 = 3815275) B3815275
theorem B3391355 : Blo 2009435 3391355 := bstep (se 1 (by rfl) ⟨2543516, by rfl⟩ : syracuseStep 3391355 = 5087033) B5087033
theorem B2260903 : Blo 2009435 2260903 := bstep (se 1 (by rfl) ⟨1695677, by rfl⟩ : syracuseStep 2260903 = 3391355) B3391355
theorem B3014537 : Blo 2009435 3014537 := bstep (se 2 (by rfl) ⟨1130451, by rfl⟩ : syracuseStep 3014537 = 2260903) B2260903
theorem B2009691 : Blo 2009435 2009691 := bstep (se 1 (by rfl) ⟨1507268, by rfl⟩ : syracuseStep 2009691 = 3014537) B3014537
theorem B10174085 : Blo 2009435 10174085 := bbase (se 4 (by rfl) ⟨953820, by rfl⟩ : syracuseStep 10174085 = 1907641) (by norm_num)
theorem B6782723 : Blo 2009435 6782723 := bstep (se 1 (by rfl) ⟨5087042, by rfl⟩ : syracuseStep 6782723 = 10174085) B10174085
theorem B4521815 : Blo 2009435 4521815 := bstep (se 1 (by rfl) ⟨3391361, by rfl⟩ : syracuseStep 4521815 = 6782723) B6782723
theorem B3014543 : Blo 2009435 3014543 := bstep (se 1 (by rfl) ⟨2260907, by rfl⟩ : syracuseStep 3014543 = 4521815) B4521815
theorem B2009695 : Blo 2009435 2009695 := bstep (se 1 (by rfl) ⟨1507271, by rfl⟩ : syracuseStep 2009695 = 3014543) B3014543
theorem B3014549 : Blo 2009435 3014549 := bbase (se 6 (by rfl) ⟨70653, by rfl⟩ : syracuseStep 3014549 = 141307) (by norm_num)
theorem B2009699 : Blo 2009435 2009699 := bstep (se 1 (by rfl) ⟨1507274, by rfl⟩ : syracuseStep 2009699 = 3014549) B3014549
theorem B2146105 : Blo 2009435 2146105 := bbase (se 2 (by rfl) ⟨804789, by rfl⟩ : syracuseStep 2146105 = 1609579) (by norm_num)
theorem B11445893 : Blo 2009435 11445893 := bstep (se 4 (by rfl) ⟨1073052, by rfl⟩ : syracuseStep 11445893 = 2146105) B2146105
theorem B7630595 : Blo 2009435 7630595 := bstep (se 1 (by rfl) ⟨5722946, by rfl⟩ : syracuseStep 7630595 = 11445893) B11445893
theorem B5087063 : Blo 2009435 5087063 := bstep (se 1 (by rfl) ⟨3815297, by rfl⟩ : syracuseStep 5087063 = 7630595) B7630595
theorem B3391375 : Blo 2009435 3391375 := bstep (se 1 (by rfl) ⟨2543531, by rfl⟩ : syracuseStep 3391375 = 5087063) B5087063
theorem B4521833 : Blo 2009435 4521833 := bstep (se 2 (by rfl) ⟨1695687, by rfl⟩ : syracuseStep 4521833 = 3391375) B3391375
theorem B3014555 : Blo 2009435 3014555 := bstep (se 1 (by rfl) ⟨2260916, by rfl⟩ : syracuseStep 3014555 = 4521833) B4521833
theorem B2009703 : Blo 2009435 2009703 := bstep (se 1 (by rfl) ⟨1507277, by rfl⟩ : syracuseStep 2009703 = 3014555) B3014555
theorem B2260921 : Blo 2009435 2260921 := bbase (se 2 (by rfl) ⟨847845, by rfl⟩ : syracuseStep 2260921 = 1695691) (by norm_num)
theorem B3014561 : Blo 2009435 3014561 := bstep (se 2 (by rfl) ⟨1130460, by rfl⟩ : syracuseStep 3014561 = 2260921) B2260921
theorem B2009707 : Blo 2009435 2009707 := bstep (se 1 (by rfl) ⟨1507280, by rfl⟩ : syracuseStep 2009707 = 3014561) B3014561
theorem B6438341 : Blo 2009435 6438341 := bbase (se 4 (by rfl) ⟨603594, by rfl⟩ : syracuseStep 6438341 = 1207189) (by norm_num)
theorem B4292227 : Blo 2009435 4292227 := bstep (se 1 (by rfl) ⟨3219170, by rfl⟩ : syracuseStep 4292227 = 6438341) B6438341
theorem B5722969 : Blo 2009435 5722969 := bstep (se 2 (by rfl) ⟨2146113, by rfl⟩ : syracuseStep 5722969 = 4292227) B4292227
theorem B7630625 : Blo 2009435 7630625 := bstep (se 2 (by rfl) ⟨2861484, by rfl⟩ : syracuseStep 7630625 = 5722969) B5722969
theorem B5087083 : Blo 2009435 5087083 := bstep (se 1 (by rfl) ⟨3815312, by rfl⟩ : syracuseStep 5087083 = 7630625) B7630625
theorem B6782777 : Blo 2009435 6782777 := bstep (se 2 (by rfl) ⟨2543541, by rfl⟩ : syracuseStep 6782777 = 5087083) B5087083
theorem B4521851 : Blo 2009435 4521851 := bstep (se 1 (by rfl) ⟨3391388, by rfl⟩ : syracuseStep 4521851 = 6782777) B6782777
theorem B3014567 : Blo 2009435 3014567 := bstep (se 1 (by rfl) ⟨2260925, by rfl⟩ : syracuseStep 3014567 = 4521851) B4521851
theorem B2009711 : Blo 2009435 2009711 := bstep (se 1 (by rfl) ⟨1507283, by rfl⟩ : syracuseStep 2009711 = 3014567) B3014567
theorem B3014573 : Blo 2009435 3014573 := bbase (se 3 (by rfl) ⟨565232, by rfl⟩ : syracuseStep 3014573 = 1130465) (by norm_num)
theorem B2009715 : Blo 2009435 2009715 := bstep (se 1 (by rfl) ⟨1507286, by rfl⟩ : syracuseStep 2009715 = 3014573) B3014573
theorem B4521869 : Blo 2009435 4521869 := bbase (se 3 (by rfl) ⟨847850, by rfl⟩ : syracuseStep 4521869 = 1695701) (by norm_num)
theorem B3014579 : Blo 2009435 3014579 := bstep (se 1 (by rfl) ⟨2260934, by rfl⟩ : syracuseStep 3014579 = 4521869) B4521869
theorem B2009719 : Blo 2009435 2009719 := bstep (se 1 (by rfl) ⟨1507289, by rfl⟩ : syracuseStep 2009719 = 3014579) B3014579
theorem B2543557 : Blo 2009435 2543557 := bbase (se 4 (by rfl) ⟨238458, by rfl⟩ : syracuseStep 2543557 = 476917) (by norm_num)
theorem B3391409 : Blo 2009435 3391409 := bstep (se 2 (by rfl) ⟨1271778, by rfl⟩ : syracuseStep 3391409 = 2543557) B2543557
theorem B2260939 : Blo 2009435 2260939 := bstep (se 1 (by rfl) ⟨1695704, by rfl⟩ : syracuseStep 2260939 = 3391409) B3391409
theorem B3014585 : Blo 2009435 3014585 := bstep (se 2 (by rfl) ⟨1130469, by rfl⟩ : syracuseStep 3014585 = 2260939) B2260939
theorem B2009723 : Blo 2009435 2009723 := bstep (se 1 (by rfl) ⟨1507292, by rfl⟩ : syracuseStep 2009723 = 3014585) B3014585
theorem B2900549 : Blo 2009435 2900549 := bbase (se 4 (by rfl) ⟨271926, by rfl⟩ : syracuseStep 2900549 = 543853) (by norm_num)
theorem B7734797 : Blo 2009435 7734797 := bstep (se 3 (by rfl) ⟨1450274, by rfl⟩ : syracuseStep 7734797 = 2900549) B2900549
theorem B5156531 : Blo 2009435 5156531 := bstep (se 1 (by rfl) ⟨3867398, by rfl⟩ : syracuseStep 5156531 = 7734797) B7734797
theorem B3437687 : Blo 2009435 3437687 := bstep (se 1 (by rfl) ⟨2578265, by rfl⟩ : syracuseStep 3437687 = 5156531) B5156531
theorem B9167165 : Blo 2009435 9167165 := bstep (se 3 (by rfl) ⟨1718843, by rfl⟩ : syracuseStep 9167165 = 3437687) B3437687
theorem B6111443 : Blo 2009435 6111443 := bstep (se 1 (by rfl) ⟨4583582, by rfl⟩ : syracuseStep 6111443 = 9167165) B9167165
theorem B4074295 : Blo 2009435 4074295 := bstep (se 1 (by rfl) ⟨3055721, by rfl⟩ : syracuseStep 4074295 = 6111443) B6111443
theorem B5432393 : Blo 2009435 5432393 := bstep (se 2 (by rfl) ⟨2037147, by rfl⟩ : syracuseStep 5432393 = 4074295) B4074295
theorem B14486381 : Blo 2009435 14486381 := bstep (se 3 (by rfl) ⟨2716196, by rfl⟩ : syracuseStep 14486381 = 5432393) B5432393
theorem B9657587 : Blo 2009435 9657587 := bstep (se 1 (by rfl) ⟨7243190, by rfl⟩ : syracuseStep 9657587 = 14486381) B14486381
theorem B25753565 : Blo 2009435 25753565 := bstep (se 3 (by rfl) ⟨4828793, by rfl⟩ : syracuseStep 25753565 = 9657587) B9657587
theorem B17169043 : Blo 2009435 17169043 := bstep (se 1 (by rfl) ⟨12876782, by rfl⟩ : syracuseStep 17169043 = 25753565) B25753565
theorem B22892057 : Blo 2009435 22892057 := bstep (se 2 (by rfl) ⟨8584521, by rfl⟩ : syracuseStep 22892057 = 17169043) B17169043
theorem B15261371 : Blo 2009435 15261371 := bstep (se 1 (by rfl) ⟨11446028, by rfl⟩ : syracuseStep 15261371 = 22892057) B22892057
theorem B10174247 : Blo 2009435 10174247 := bstep (se 1 (by rfl) ⟨7630685, by rfl⟩ : syracuseStep 10174247 = 15261371) B15261371
theorem B6782831 : Blo 2009435 6782831 := bstep (se 1 (by rfl) ⟨5087123, by rfl⟩ : syracuseStep 6782831 = 10174247) B10174247
theorem B4521887 : Blo 2009435 4521887 := bstep (se 1 (by rfl) ⟨3391415, by rfl⟩ : syracuseStep 4521887 = 6782831) B6782831
theorem B3014591 : Blo 2009435 3014591 := bstep (se 1 (by rfl) ⟨2260943, by rfl⟩ : syracuseStep 3014591 = 4521887) B4521887
theorem B2009727 : Blo 2009435 2009727 := bstep (se 1 (by rfl) ⟨1507295, by rfl⟩ : syracuseStep 2009727 = 3014591) B3014591
theorem B3014597 : Blo 2009435 3014597 := bbase (se 4 (by rfl) ⟨282618, by rfl⟩ : syracuseStep 3014597 = 565237) (by norm_num)
theorem B2009731 : Blo 2009435 2009731 := bstep (se 1 (by rfl) ⟨1507298, by rfl⟩ : syracuseStep 2009731 = 3014597) B3014597
theorem B3391429 : Blo 2009435 3391429 := bbase (se 4 (by rfl) ⟨317946, by rfl⟩ : syracuseStep 3391429 = 635893) (by norm_num)
theorem B4521905 : Blo 2009435 4521905 := bstep (se 2 (by rfl) ⟨1695714, by rfl⟩ : syracuseStep 4521905 = 3391429) B3391429
theorem B3014603 : Blo 2009435 3014603 := bstep (se 1 (by rfl) ⟨2260952, by rfl⟩ : syracuseStep 3014603 = 4521905) B4521905
theorem B2009735 : Blo 2009435 2009735 := bstep (se 1 (by rfl) ⟨1507301, by rfl⟩ : syracuseStep 2009735 = 3014603) B3014603
theorem B2260957 : Blo 2009435 2260957 := bbase (se 3 (by rfl) ⟨423929, by rfl⟩ : syracuseStep 2260957 = 847859) (by norm_num)
theorem B3014609 : Blo 2009435 3014609 := bstep (se 2 (by rfl) ⟨1130478, by rfl⟩ : syracuseStep 3014609 = 2260957) B2260957
theorem B2009739 : Blo 2009435 2009739 := bstep (se 1 (by rfl) ⟨1507304, by rfl⟩ : syracuseStep 2009739 = 3014609) B3014609
theorem B6782885 : Blo 2009435 6782885 := bbase (se 4 (by rfl) ⟨635895, by rfl⟩ : syracuseStep 6782885 = 1271791) (by norm_num)
theorem B4521923 : Blo 2009435 4521923 := bstep (se 1 (by rfl) ⟨3391442, by rfl⟩ : syracuseStep 4521923 = 6782885) B6782885
theorem B3014615 : Blo 2009435 3014615 := bstep (se 1 (by rfl) ⟨2260961, by rfl⟩ : syracuseStep 3014615 = 4521923) B4521923
theorem B2009743 : Blo 2009435 2009743 := bstep (se 1 (by rfl) ⟨1507307, by rfl⟩ : syracuseStep 2009743 = 3014615) B3014615
theorem B3014621 : Blo 2009435 3014621 := bbase (se 3 (by rfl) ⟨565241, by rfl⟩ : syracuseStep 3014621 = 1130483) (by norm_num)
theorem B2009747 : Blo 2009435 2009747 := bstep (se 1 (by rfl) ⟨1507310, by rfl⟩ : syracuseStep 2009747 = 3014621) B3014621
theorem B4521941 : Blo 2009435 4521941 := bbase (se 7 (by rfl) ⟨52991, by rfl⟩ : syracuseStep 4521941 = 105983) (by norm_num)
theorem B3014627 : Blo 2009435 3014627 := bstep (se 1 (by rfl) ⟨2260970, by rfl⟩ : syracuseStep 3014627 = 4521941) B4521941
theorem B2009751 : Blo 2009435 2009751 := bstep (se 1 (by rfl) ⟨1507313, by rfl⟩ : syracuseStep 2009751 = 3014627) B3014627
theorem B12223061 : Blo 2009435 12223061 := bbase (se 8 (by rfl) ⟨71619, by rfl⟩ : syracuseStep 12223061 = 143239) (by norm_num)
theorem B8148707 : Blo 2009435 8148707 := bstep (se 1 (by rfl) ⟨6111530, by rfl⟩ : syracuseStep 8148707 = 12223061) B12223061
theorem B5432471 : Blo 2009435 5432471 := bstep (se 1 (by rfl) ⟨4074353, by rfl⟩ : syracuseStep 5432471 = 8148707) B8148707
theorem B3621647 : Blo 2009435 3621647 := bstep (se 1 (by rfl) ⟨2716235, by rfl⟩ : syracuseStep 3621647 = 5432471) B5432471
theorem B2414431 : Blo 2009435 2414431 := bstep (se 1 (by rfl) ⟨1810823, by rfl⟩ : syracuseStep 2414431 = 3621647) B3621647
theorem B12876965 : Blo 2009435 12876965 := bstep (se 4 (by rfl) ⟨1207215, by rfl⟩ : syracuseStep 12876965 = 2414431) B2414431
theorem B8584643 : Blo 2009435 8584643 := bstep (se 1 (by rfl) ⟨6438482, by rfl⟩ : syracuseStep 8584643 = 12876965) B12876965
theorem B5723095 : Blo 2009435 5723095 := bstep (se 1 (by rfl) ⟨4292321, by rfl⟩ : syracuseStep 5723095 = 8584643) B8584643
theorem B7630793 : Blo 2009435 7630793 := bstep (se 2 (by rfl) ⟨2861547, by rfl⟩ : syracuseStep 7630793 = 5723095) B5723095
theorem B5087195 : Blo 2009435 5087195 := bstep (se 1 (by rfl) ⟨3815396, by rfl⟩ : syracuseStep 5087195 = 7630793) B7630793
theorem B3391463 : Blo 2009435 3391463 := bstep (se 1 (by rfl) ⟨2543597, by rfl⟩ : syracuseStep 3391463 = 5087195) B5087195
theorem B2260975 : Blo 2009435 2260975 := bstep (se 1 (by rfl) ⟨1695731, by rfl⟩ : syracuseStep 2260975 = 3391463) B3391463
theorem B3014633 : Blo 2009435 3014633 := bstep (se 2 (by rfl) ⟨1130487, by rfl⟩ : syracuseStep 3014633 = 2260975) B2260975
theorem B2009755 : Blo 2009435 2009755 := bstep (se 1 (by rfl) ⟨1507316, by rfl⟩ : syracuseStep 2009755 = 3014633) B3014633
theorem B6111541 : Blo 2009435 6111541 := bbase (se 5 (by rfl) ⟨286478, by rfl⟩ : syracuseStep 6111541 = 572957) (by norm_num)
theorem B8148721 : Blo 2009435 8148721 := bstep (se 2 (by rfl) ⟨3055770, by rfl⟩ : syracuseStep 8148721 = 6111541) B6111541
theorem B10864961 : Blo 2009435 10864961 := bstep (se 2 (by rfl) ⟨4074360, by rfl⟩ : syracuseStep 10864961 = 8148721) B8148721
theorem B7243307 : Blo 2009435 7243307 := bstep (se 1 (by rfl) ⟨5432480, by rfl⟩ : syracuseStep 7243307 = 10864961) B10864961
theorem B4828871 : Blo 2009435 4828871 := bstep (se 1 (by rfl) ⟨3621653, by rfl⟩ : syracuseStep 4828871 = 7243307) B7243307
theorem B3219247 : Blo 2009435 3219247 := bstep (se 1 (by rfl) ⟨2414435, by rfl⟩ : syracuseStep 3219247 = 4828871) B4828871
theorem B17169317 : Blo 2009435 17169317 := bstep (se 4 (by rfl) ⟨1609623, by rfl⟩ : syracuseStep 17169317 = 3219247) B3219247
theorem B11446211 : Blo 2009435 11446211 := bstep (se 1 (by rfl) ⟨8584658, by rfl⟩ : syracuseStep 11446211 = 17169317) B17169317
theorem B7630807 : Blo 2009435 7630807 := bstep (se 1 (by rfl) ⟨5723105, by rfl⟩ : syracuseStep 7630807 = 11446211) B11446211
theorem B10174409 : Blo 2009435 10174409 := bstep (se 2 (by rfl) ⟨3815403, by rfl⟩ : syracuseStep 10174409 = 7630807) B7630807
theorem B6782939 : Blo 2009435 6782939 := bstep (se 1 (by rfl) ⟨5087204, by rfl⟩ : syracuseStep 6782939 = 10174409) B10174409
theorem B4521959 : Blo 2009435 4521959 := bstep (se 1 (by rfl) ⟨3391469, by rfl⟩ : syracuseStep 4521959 = 6782939) B6782939
theorem B3014639 : Blo 2009435 3014639 := bstep (se 1 (by rfl) ⟨2260979, by rfl⟩ : syracuseStep 3014639 = 4521959) B4521959
theorem B2009759 : Blo 2009435 2009759 := bstep (se 1 (by rfl) ⟨1507319, by rfl⟩ : syracuseStep 2009759 = 3014639) B3014639
theorem B3014645 : Blo 2009435 3014645 := bbase (se 5 (by rfl) ⟨141311, by rfl⟩ : syracuseStep 3014645 = 282623) (by norm_num)
theorem B2009763 : Blo 2009435 2009763 := bstep (se 1 (by rfl) ⟨1507322, by rfl⟩ : syracuseStep 2009763 = 3014645) B3014645
theorem B5167421 : Blo 2009435 5167421 := bbase (se 3 (by rfl) ⟨968891, by rfl⟩ : syracuseStep 5167421 = 1937783) (by norm_num)
theorem B3444947 : Blo 2009435 3444947 := bstep (se 1 (by rfl) ⟨2583710, by rfl⟩ : syracuseStep 3444947 = 5167421) B5167421
theorem B2296631 : Blo 2009435 2296631 := bstep (se 1 (by rfl) ⟨1722473, by rfl⟩ : syracuseStep 2296631 = 3444947) B3444947
theorem B6124349 : Blo 2009435 6124349 := bstep (se 3 (by rfl) ⟨1148315, by rfl⟩ : syracuseStep 6124349 = 2296631) B2296631
theorem B4082899 : Blo 2009435 4082899 := bstep (se 1 (by rfl) ⟨3062174, by rfl⟩ : syracuseStep 4082899 = 6124349) B6124349
theorem B5443865 : Blo 2009435 5443865 := bstep (se 2 (by rfl) ⟨2041449, by rfl⟩ : syracuseStep 5443865 = 4082899) B4082899
theorem B3629243 : Blo 2009435 3629243 := bstep (se 1 (by rfl) ⟨2721932, by rfl⟩ : syracuseStep 3629243 = 5443865) B5443865
theorem B9677981 : Blo 2009435 9677981 := bstep (se 3 (by rfl) ⟨1814621, by rfl⟩ : syracuseStep 9677981 = 3629243) B3629243
theorem B6451987 : Blo 2009435 6451987 := bstep (se 1 (by rfl) ⟨4838990, by rfl⟩ : syracuseStep 6451987 = 9677981) B9677981
theorem B8602649 : Blo 2009435 8602649 := bstep (se 2 (by rfl) ⟨3225993, by rfl⟩ : syracuseStep 8602649 = 6451987) B6451987
theorem B5735099 : Blo 2009435 5735099 := bstep (se 1 (by rfl) ⟨4301324, by rfl⟩ : syracuseStep 5735099 = 8602649) B8602649
theorem B3823399 : Blo 2009435 3823399 := bstep (se 1 (by rfl) ⟨2867549, by rfl⟩ : syracuseStep 3823399 = 5735099) B5735099
theorem B5097865 : Blo 2009435 5097865 := bstep (se 2 (by rfl) ⟨1911699, by rfl⟩ : syracuseStep 5097865 = 3823399) B3823399
theorem B6797153 : Blo 2009435 6797153 := bstep (se 2 (by rfl) ⟨2548932, by rfl⟩ : syracuseStep 6797153 = 5097865) B5097865
theorem B18125741 : Blo 2009435 18125741 := bstep (se 3 (by rfl) ⟨3398576, by rfl⟩ : syracuseStep 18125741 = 6797153) B6797153
theorem B12083827 : Blo 2009435 12083827 := bstep (se 1 (by rfl) ⟨9062870, by rfl⟩ : syracuseStep 12083827 = 18125741) B18125741
theorem B16111769 : Blo 2009435 16111769 := bstep (se 2 (by rfl) ⟨6041913, by rfl⟩ : syracuseStep 16111769 = 12083827) B12083827
theorem B42964717 : Blo 2009435 42964717 := bstep (se 3 (by rfl) ⟨8055884, by rfl⟩ : syracuseStep 42964717 = 16111769) B16111769
theorem B57286289 : Blo 2009435 57286289 := bstep (se 2 (by rfl) ⟨21482358, by rfl⟩ : syracuseStep 57286289 = 42964717) B42964717
theorem B152763437 : Blo 2009435 152763437 := bstep (se 3 (by rfl) ⟨28643144, by rfl⟩ : syracuseStep 152763437 = 57286289) B57286289
theorem B101842291 : Blo 2009435 101842291 := bstep (se 1 (by rfl) ⟨76381718, by rfl⟩ : syracuseStep 101842291 = 152763437) B152763437
theorem B543158885 : Blo 2009435 543158885 := bstep (se 4 (by rfl) ⟨50921145, by rfl⟩ : syracuseStep 543158885 = 101842291) B101842291
theorem B362105923 : Blo 2009435 362105923 := bstep (se 1 (by rfl) ⟨271579442, by rfl⟩ : syracuseStep 362105923 = 543158885) B543158885
theorem B482807897 : Blo 2009435 482807897 := bstep (se 2 (by rfl) ⟨181052961, by rfl⟩ : syracuseStep 482807897 = 362105923) B362105923
theorem B321871931 : Blo 2009435 321871931 := bstep (se 1 (by rfl) ⟨241403948, by rfl⟩ : syracuseStep 321871931 = 482807897) B482807897
theorem B214581287 : Blo 2009435 214581287 := bstep (se 1 (by rfl) ⟨160935965, by rfl⟩ : syracuseStep 214581287 = 321871931) B321871931
theorem B143054191 : Blo 2009435 143054191 := bstep (se 1 (by rfl) ⟨107290643, by rfl⟩ : syracuseStep 143054191 = 214581287) B214581287
theorem B190738921 : Blo 2009435 190738921 := bstep (se 2 (by rfl) ⟨71527095, by rfl⟩ : syracuseStep 190738921 = 143054191) B143054191
theorem B254318561 : Blo 2009435 254318561 := bstep (se 2 (by rfl) ⟨95369460, by rfl⟩ : syracuseStep 254318561 = 190738921) B190738921
theorem B169545707 : Blo 2009435 169545707 := bstep (se 1 (by rfl) ⟨127159280, by rfl⟩ : syracuseStep 169545707 = 254318561) B254318561
theorem B113030471 : Blo 2009435 113030471 := bstep (se 1 (by rfl) ⟨84772853, by rfl⟩ : syracuseStep 113030471 = 169545707) B169545707
theorem B75353647 : Blo 2009435 75353647 := bstep (se 1 (by rfl) ⟨56515235, by rfl⟩ : syracuseStep 75353647 = 113030471) B113030471
theorem B100471529 : Blo 2009435 100471529 := bstep (se 2 (by rfl) ⟨37676823, by rfl⟩ : syracuseStep 100471529 = 75353647) B75353647
theorem B66981019 : Blo 2009435 66981019 := bstep (se 1 (by rfl) ⟨50235764, by rfl⟩ : syracuseStep 66981019 = 100471529) B100471529
theorem B89308025 : Blo 2009435 89308025 := bstep (se 2 (by rfl) ⟨33490509, by rfl⟩ : syracuseStep 89308025 = 66981019) B66981019
theorem B59538683 : Blo 2009435 59538683 := bstep (se 1 (by rfl) ⟨44654012, by rfl⟩ : syracuseStep 59538683 = 89308025) B89308025
theorem B158769821 : Blo 2009435 158769821 := bstep (se 3 (by rfl) ⟨29769341, by rfl⟩ : syracuseStep 158769821 = 59538683) B59538683
theorem B105846547 : Blo 2009435 105846547 := bstep (se 1 (by rfl) ⟨79384910, by rfl⟩ : syracuseStep 105846547 = 158769821) B158769821
theorem B141128729 : Blo 2009435 141128729 := bstep (se 2 (by rfl) ⟨52923273, by rfl⟩ : syracuseStep 141128729 = 105846547) B105846547
theorem B94085819 : Blo 2009435 94085819 := bstep (se 1 (by rfl) ⟨70564364, by rfl⟩ : syracuseStep 94085819 = 141128729) B141128729
theorem B62723879 : Blo 2009435 62723879 := bstep (se 1 (by rfl) ⟨47042909, by rfl⟩ : syracuseStep 62723879 = 94085819) B94085819
theorem B41815919 : Blo 2009435 41815919 := bstep (se 1 (by rfl) ⟨31361939, by rfl⟩ : syracuseStep 41815919 = 62723879) B62723879
theorem B27877279 : Blo 2009435 27877279 := bstep (se 1 (by rfl) ⟨20907959, by rfl⟩ : syracuseStep 27877279 = 41815919) B41815919
theorem B37169705 : Blo 2009435 37169705 := bstep (se 2 (by rfl) ⟨13938639, by rfl⟩ : syracuseStep 37169705 = 27877279) B27877279
theorem B99119213 : Blo 2009435 99119213 := bstep (se 3 (by rfl) ⟨18584852, by rfl⟩ : syracuseStep 99119213 = 37169705) B37169705
theorem B66079475 : Blo 2009435 66079475 := bstep (se 1 (by rfl) ⟨49559606, by rfl⟩ : syracuseStep 66079475 = 99119213) B99119213
theorem B44052983 : Blo 2009435 44052983 := bstep (se 1 (by rfl) ⟨33039737, by rfl⟩ : syracuseStep 44052983 = 66079475) B66079475
theorem B29368655 : Blo 2009435 29368655 := bstep (se 1 (by rfl) ⟨22026491, by rfl⟩ : syracuseStep 29368655 = 44052983) B44052983
theorem B19579103 : Blo 2009435 19579103 := bstep (se 1 (by rfl) ⟨14684327, by rfl⟩ : syracuseStep 19579103 = 29368655) B29368655
theorem B13052735 : Blo 2009435 13052735 := bstep (se 1 (by rfl) ⟨9789551, by rfl⟩ : syracuseStep 13052735 = 19579103) B19579103
theorem B8701823 : Blo 2009435 8701823 := bstep (se 1 (by rfl) ⟨6526367, by rfl⟩ : syracuseStep 8701823 = 13052735) B13052735
theorem B5801215 : Blo 2009435 5801215 := bstep (se 1 (by rfl) ⟨4350911, by rfl⟩ : syracuseStep 5801215 = 8701823) B8701823
theorem B7734953 : Blo 2009435 7734953 := bstep (se 2 (by rfl) ⟨2900607, by rfl⟩ : syracuseStep 7734953 = 5801215) B5801215
theorem B5156635 : Blo 2009435 5156635 := bstep (se 1 (by rfl) ⟨3867476, by rfl⟩ : syracuseStep 5156635 = 7734953) B7734953
theorem B6875513 : Blo 2009435 6875513 := bstep (se 2 (by rfl) ⟨2578317, by rfl⟩ : syracuseStep 6875513 = 5156635) B5156635
theorem B4583675 : Blo 2009435 4583675 := bstep (se 1 (by rfl) ⟨3437756, by rfl⟩ : syracuseStep 4583675 = 6875513) B6875513
theorem B12223133 : Blo 2009435 12223133 := bstep (se 3 (by rfl) ⟨2291837, by rfl⟩ : syracuseStep 12223133 = 4583675) B4583675
theorem B8148755 : Blo 2009435 8148755 := bstep (se 1 (by rfl) ⟨6111566, by rfl⟩ : syracuseStep 8148755 = 12223133) B12223133
theorem B5432503 : Blo 2009435 5432503 := bstep (se 1 (by rfl) ⟨4074377, by rfl⟩ : syracuseStep 5432503 = 8148755) B8148755
theorem B7243337 : Blo 2009435 7243337 := bstep (se 2 (by rfl) ⟨2716251, by rfl⟩ : syracuseStep 7243337 = 5432503) B5432503
theorem B4828891 : Blo 2009435 4828891 := bstep (se 1 (by rfl) ⟨3621668, by rfl⟩ : syracuseStep 4828891 = 7243337) B7243337
theorem B6438521 : Blo 2009435 6438521 := bstep (se 2 (by rfl) ⟨2414445, by rfl⟩ : syracuseStep 6438521 = 4828891) B4828891
theorem B4292347 : Blo 2009435 4292347 := bstep (se 1 (by rfl) ⟨3219260, by rfl⟩ : syracuseStep 4292347 = 6438521) B6438521
theorem B5723129 : Blo 2009435 5723129 := bstep (se 2 (by rfl) ⟨2146173, by rfl⟩ : syracuseStep 5723129 = 4292347) B4292347
theorem B3815419 : Blo 2009435 3815419 := bstep (se 1 (by rfl) ⟨2861564, by rfl⟩ : syracuseStep 3815419 = 5723129) B5723129
theorem B5087225 : Blo 2009435 5087225 := bstep (se 2 (by rfl) ⟨1907709, by rfl⟩ : syracuseStep 5087225 = 3815419) B3815419
theorem B3391483 : Blo 2009435 3391483 := bstep (se 1 (by rfl) ⟨2543612, by rfl⟩ : syracuseStep 3391483 = 5087225) B5087225
theorem B4521977 : Blo 2009435 4521977 := bstep (se 2 (by rfl) ⟨1695741, by rfl⟩ : syracuseStep 4521977 = 3391483) B3391483
theorem B3014651 : Blo 2009435 3014651 := bstep (se 1 (by rfl) ⟨2260988, by rfl⟩ : syracuseStep 3014651 = 4521977) B4521977
theorem B2009767 : Blo 2009435 2009767 := bstep (se 1 (by rfl) ⟨1507325, by rfl⟩ : syracuseStep 2009767 = 3014651) B3014651
theorem B2260993 : Blo 2009435 2260993 := bbase (se 2 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 2260993 = 1695745) (by norm_num)
theorem B3014657 : Blo 2009435 3014657 := bstep (se 2 (by rfl) ⟨1130496, by rfl⟩ : syracuseStep 3014657 = 2260993) B2260993
theorem B2009771 : Blo 2009435 2009771 := bstep (se 1 (by rfl) ⟨1507328, by rfl⟩ : syracuseStep 2009771 = 3014657) B3014657
theorem B5087245 : Blo 2009435 5087245 := bbase (se 3 (by rfl) ⟨953858, by rfl⟩ : syracuseStep 5087245 = 1907717) (by norm_num)
theorem B6782993 : Blo 2009435 6782993 := bstep (se 2 (by rfl) ⟨2543622, by rfl⟩ : syracuseStep 6782993 = 5087245) B5087245
theorem B4521995 : Blo 2009435 4521995 := bstep (se 1 (by rfl) ⟨3391496, by rfl⟩ : syracuseStep 4521995 = 6782993) B6782993
theorem B3014663 : Blo 2009435 3014663 := bstep (se 1 (by rfl) ⟨2260997, by rfl⟩ : syracuseStep 3014663 = 4521995) B4521995
theorem B2009775 : Blo 2009435 2009775 := bstep (se 1 (by rfl) ⟨1507331, by rfl⟩ : syracuseStep 2009775 = 3014663) B3014663
theorem B3014669 : Blo 2009435 3014669 := bbase (se 3 (by rfl) ⟨565250, by rfl⟩ : syracuseStep 3014669 = 1130501) (by norm_num)
theorem B2009779 : Blo 2009435 2009779 := bstep (se 1 (by rfl) ⟨1507334, by rfl⟩ : syracuseStep 2009779 = 3014669) B3014669
theorem B4522013 : Blo 2009435 4522013 := bbase (se 3 (by rfl) ⟨847877, by rfl⟩ : syracuseStep 4522013 = 1695755) (by norm_num)
theorem B3014675 : Blo 2009435 3014675 := bstep (se 1 (by rfl) ⟨2261006, by rfl⟩ : syracuseStep 3014675 = 4522013) B4522013
theorem B2009783 : Blo 2009435 2009783 := bstep (se 1 (by rfl) ⟨1507337, by rfl⟩ : syracuseStep 2009783 = 3014675) B3014675
theorem B3391517 : Blo 2009435 3391517 := bbase (se 3 (by rfl) ⟨635909, by rfl⟩ : syracuseStep 3391517 = 1271819) (by norm_num)
theorem B2261011 : Blo 2009435 2261011 := bstep (se 1 (by rfl) ⟨1695758, by rfl⟩ : syracuseStep 2261011 = 3391517) B3391517
theorem B3014681 : Blo 2009435 3014681 := bstep (se 2 (by rfl) ⟨1130505, by rfl⟩ : syracuseStep 3014681 = 2261011) B2261011
theorem B2009787 : Blo 2009435 2009787 := bstep (se 1 (by rfl) ⟨1507340, by rfl⟩ : syracuseStep 2009787 = 3014681) B3014681
theorem B24446549 : Blo 2009435 24446549 := bbase (se 8 (by rfl) ⟨143241, by rfl⟩ : syracuseStep 24446549 = 286483) (by norm_num)
theorem B16297699 : Blo 2009435 16297699 := bstep (se 1 (by rfl) ⟨12223274, by rfl⟩ : syracuseStep 16297699 = 24446549) B24446549
theorem B21730265 : Blo 2009435 21730265 := bstep (se 2 (by rfl) ⟨8148849, by rfl⟩ : syracuseStep 21730265 = 16297699) B16297699
theorem B14486843 : Blo 2009435 14486843 := bstep (se 1 (by rfl) ⟨10865132, by rfl⟩ : syracuseStep 14486843 = 21730265) B21730265
theorem B9657895 : Blo 2009435 9657895 := bstep (se 1 (by rfl) ⟨7243421, by rfl⟩ : syracuseStep 9657895 = 14486843) B14486843
theorem B12877193 : Blo 2009435 12877193 := bstep (se 2 (by rfl) ⟨4828947, by rfl⟩ : syracuseStep 12877193 = 9657895) B9657895
theorem B8584795 : Blo 2009435 8584795 := bstep (se 1 (by rfl) ⟨6438596, by rfl⟩ : syracuseStep 8584795 = 12877193) B12877193
theorem B11446393 : Blo 2009435 11446393 := bstep (se 2 (by rfl) ⟨4292397, by rfl⟩ : syracuseStep 11446393 = 8584795) B8584795
theorem B15261857 : Blo 2009435 15261857 := bstep (se 2 (by rfl) ⟨5723196, by rfl⟩ : syracuseStep 15261857 = 11446393) B11446393
theorem B10174571 : Blo 2009435 10174571 := bstep (se 1 (by rfl) ⟨7630928, by rfl⟩ : syracuseStep 10174571 = 15261857) B15261857
theorem B6783047 : Blo 2009435 6783047 := bstep (se 1 (by rfl) ⟨5087285, by rfl⟩ : syracuseStep 6783047 = 10174571) B10174571
theorem B4522031 : Blo 2009435 4522031 := bstep (se 1 (by rfl) ⟨3391523, by rfl⟩ : syracuseStep 4522031 = 6783047) B6783047
theorem B3014687 : Blo 2009435 3014687 := bstep (se 1 (by rfl) ⟨2261015, by rfl⟩ : syracuseStep 3014687 = 4522031) B4522031
theorem B2009791 : Blo 2009435 2009791 := bstep (se 1 (by rfl) ⟨1507343, by rfl⟩ : syracuseStep 2009791 = 3014687) B3014687
theorem B3014693 : Blo 2009435 3014693 := bbase (se 4 (by rfl) ⟨282627, by rfl⟩ : syracuseStep 3014693 = 565255) (by norm_num)
theorem B2009795 : Blo 2009435 2009795 := bstep (se 1 (by rfl) ⟨1507346, by rfl⟩ : syracuseStep 2009795 = 3014693) B3014693
theorem B2543653 : Blo 2009435 2543653 := bbase (se 4 (by rfl) ⟨238467, by rfl⟩ : syracuseStep 2543653 = 476935) (by norm_num)
theorem B3391537 : Blo 2009435 3391537 := bstep (se 2 (by rfl) ⟨1271826, by rfl⟩ : syracuseStep 3391537 = 2543653) B2543653
theorem B4522049 : Blo 2009435 4522049 := bstep (se 2 (by rfl) ⟨1695768, by rfl⟩ : syracuseStep 4522049 = 3391537) B3391537
theorem B3014699 : Blo 2009435 3014699 := bstep (se 1 (by rfl) ⟨2261024, by rfl⟩ : syracuseStep 3014699 = 4522049) B4522049
theorem B2009799 : Blo 2009435 2009799 := bstep (se 1 (by rfl) ⟨1507349, by rfl⟩ : syracuseStep 2009799 = 3014699) B3014699
theorem B2261029 : Blo 2009435 2261029 := bbase (se 4 (by rfl) ⟨211971, by rfl⟩ : syracuseStep 2261029 = 423943) (by norm_num)
theorem B3014705 : Blo 2009435 3014705 := bstep (se 2 (by rfl) ⟨1130514, by rfl⟩ : syracuseStep 3014705 = 2261029) B2261029
theorem B2009803 : Blo 2009435 2009803 := bstep (se 1 (by rfl) ⟨1507352, by rfl⟩ : syracuseStep 2009803 = 3014705) B3014705
theorem B8148917 : Blo 2009435 8148917 := bbase (se 5 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 8148917 = 763961) (by norm_num)
theorem B5432611 : Blo 2009435 5432611 := bstep (se 1 (by rfl) ⟨4074458, by rfl⟩ : syracuseStep 5432611 = 8148917) B8148917
theorem B7243481 : Blo 2009435 7243481 := bstep (se 2 (by rfl) ⟨2716305, by rfl⟩ : syracuseStep 7243481 = 5432611) B5432611
theorem B4828987 : Blo 2009435 4828987 := bstep (se 1 (by rfl) ⟨3621740, by rfl⟩ : syracuseStep 4828987 = 7243481) B7243481
theorem B6438649 : Blo 2009435 6438649 := bstep (se 2 (by rfl) ⟨2414493, by rfl⟩ : syracuseStep 6438649 = 4828987) B4828987
theorem B8584865 : Blo 2009435 8584865 := bstep (se 2 (by rfl) ⟨3219324, by rfl⟩ : syracuseStep 8584865 = 6438649) B6438649
theorem B5723243 : Blo 2009435 5723243 := bstep (se 1 (by rfl) ⟨4292432, by rfl⟩ : syracuseStep 5723243 = 8584865) B8584865
theorem B3815495 : Blo 2009435 3815495 := bstep (se 1 (by rfl) ⟨2861621, by rfl⟩ : syracuseStep 3815495 = 5723243) B5723243
theorem B2543663 : Blo 2009435 2543663 := bstep (se 1 (by rfl) ⟨1907747, by rfl⟩ : syracuseStep 2543663 = 3815495) B3815495
theorem B6783101 : Blo 2009435 6783101 := bstep (se 3 (by rfl) ⟨1271831, by rfl⟩ : syracuseStep 6783101 = 2543663) B2543663
theorem B4522067 : Blo 2009435 4522067 := bstep (se 1 (by rfl) ⟨3391550, by rfl⟩ : syracuseStep 4522067 = 6783101) B6783101
theorem B3014711 : Blo 2009435 3014711 := bstep (se 1 (by rfl) ⟨2261033, by rfl⟩ : syracuseStep 3014711 = 4522067) B4522067
theorem B2009807 : Blo 2009435 2009807 := bstep (se 1 (by rfl) ⟨1507355, by rfl⟩ : syracuseStep 2009807 = 3014711) B3014711
theorem B3014717 : Blo 2009435 3014717 := bbase (se 3 (by rfl) ⟨565259, by rfl⟩ : syracuseStep 3014717 = 1130519) (by norm_num)
theorem B2009811 : Blo 2009435 2009811 := bstep (se 1 (by rfl) ⟨1507358, by rfl⟩ : syracuseStep 2009811 = 3014717) B3014717
theorem B4522085 : Blo 2009435 4522085 := bbase (se 4 (by rfl) ⟨423945, by rfl⟩ : syracuseStep 4522085 = 847891) (by norm_num)
theorem B3014723 : Blo 2009435 3014723 := bstep (se 1 (by rfl) ⟨2261042, by rfl⟩ : syracuseStep 3014723 = 4522085) B4522085
theorem B2009815 : Blo 2009435 2009815 := bstep (se 1 (by rfl) ⟨1507361, by rfl⟩ : syracuseStep 2009815 = 3014723) B3014723
theorem B5087357 : Blo 2009435 5087357 := bbase (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) (by norm_num)
theorem B3391571 : Blo 2009435 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B2261047 : Blo 2009435 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B3014729 : Blo 2009435 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B2009819 : Blo 2009435 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B3815525 : Blo 2009435 3815525 := bbase (se 4 (by rfl) ⟨357705, by rfl⟩ : syracuseStep 3815525 = 715411) (by norm_num)
theorem B10174733 : Blo 2009435 10174733 := bstep (se 3 (by rfl) ⟨1907762, by rfl⟩ : syracuseStep 10174733 = 3815525) B3815525
theorem B6783155 : Blo 2009435 6783155 := bstep (se 1 (by rfl) ⟨5087366, by rfl⟩ : syracuseStep 6783155 = 10174733) B10174733
theorem B4522103 : Blo 2009435 4522103 := bstep (se 1 (by rfl) ⟨3391577, by rfl⟩ : syracuseStep 4522103 = 6783155) B6783155
theorem B3014735 : Blo 2009435 3014735 := bstep (se 1 (by rfl) ⟨2261051, by rfl⟩ : syracuseStep 3014735 = 4522103) B4522103
theorem B2009823 : Blo 2009435 2009823 := bstep (se 1 (by rfl) ⟨1507367, by rfl⟩ : syracuseStep 2009823 = 3014735) B3014735
theorem B3014741 : Blo 2009435 3014741 := bbase (se 8 (by rfl) ⟨17664, by rfl⟩ : syracuseStep 3014741 = 35329) (by norm_num)
theorem B2009827 : Blo 2009435 2009827 := bstep (se 1 (by rfl) ⟨1507370, by rfl⟩ : syracuseStep 2009827 = 3014741) B3014741
theorem B8149013 : Blo 2009435 8149013 := bbase (se 6 (by rfl) ⟨190992, by rfl⟩ : syracuseStep 8149013 = 381985) (by norm_num)
theorem B5432675 : Blo 2009435 5432675 := bstep (se 1 (by rfl) ⟨4074506, by rfl⟩ : syracuseStep 5432675 = 8149013) B8149013
theorem B14487133 : Blo 2009435 14487133 := bstep (se 3 (by rfl) ⟨2716337, by rfl⟩ : syracuseStep 14487133 = 5432675) B5432675
theorem B19316177 : Blo 2009435 19316177 := bstep (se 2 (by rfl) ⟨7243566, by rfl⟩ : syracuseStep 19316177 = 14487133) B14487133
theorem B12877451 : Blo 2009435 12877451 := bstep (se 1 (by rfl) ⟨9658088, by rfl⟩ : syracuseStep 12877451 = 19316177) B19316177
theorem B8584967 : Blo 2009435 8584967 := bstep (se 1 (by rfl) ⟨6438725, by rfl⟩ : syracuseStep 8584967 = 12877451) B12877451
theorem B5723311 : Blo 2009435 5723311 := bstep (se 1 (by rfl) ⟨4292483, by rfl⟩ : syracuseStep 5723311 = 8584967) B8584967
theorem B7631081 : Blo 2009435 7631081 := bstep (se 2 (by rfl) ⟨2861655, by rfl⟩ : syracuseStep 7631081 = 5723311) B5723311
theorem B5087387 : Blo 2009435 5087387 := bstep (se 1 (by rfl) ⟨3815540, by rfl⟩ : syracuseStep 5087387 = 7631081) B7631081
theorem B3391591 : Blo 2009435 3391591 := bstep (se 1 (by rfl) ⟨2543693, by rfl⟩ : syracuseStep 3391591 = 5087387) B5087387
theorem B4522121 : Blo 2009435 4522121 := bstep (se 2 (by rfl) ⟨1695795, by rfl⟩ : syracuseStep 4522121 = 3391591) B3391591
theorem B3014747 : Blo 2009435 3014747 := bstep (se 1 (by rfl) ⟨2261060, by rfl⟩ : syracuseStep 3014747 = 4522121) B4522121
theorem B2009831 : Blo 2009435 2009831 := bstep (se 1 (by rfl) ⟨1507373, by rfl⟩ : syracuseStep 2009831 = 3014747) B3014747
theorem B2261065 : Blo 2009435 2261065 := bbase (se 2 (by rfl) ⟨847899, by rfl⟩ : syracuseStep 2261065 = 1695799) (by norm_num)
theorem B3014753 : Blo 2009435 3014753 := bstep (se 2 (by rfl) ⟨1130532, by rfl⟩ : syracuseStep 3014753 = 2261065) B2261065
theorem B2009835 : Blo 2009435 2009835 := bstep (se 1 (by rfl) ⟨1507376, by rfl⟩ : syracuseStep 2009835 = 3014753) B3014753
theorem B8149045 : Blo 2009435 8149045 := bbase (se 5 (by rfl) ⟨381986, by rfl⟩ : syracuseStep 8149045 = 763973) (by norm_num)
theorem B10865393 : Blo 2009435 10865393 := bstep (se 2 (by rfl) ⟨4074522, by rfl⟩ : syracuseStep 10865393 = 8149045) B8149045
theorem B7243595 : Blo 2009435 7243595 := bstep (se 1 (by rfl) ⟨5432696, by rfl⟩ : syracuseStep 7243595 = 10865393) B10865393
theorem B4829063 : Blo 2009435 4829063 := bstep (se 1 (by rfl) ⟨3621797, by rfl⟩ : syracuseStep 4829063 = 7243595) B7243595
theorem B12877501 : Blo 2009435 12877501 := bstep (se 3 (by rfl) ⟨2414531, by rfl⟩ : syracuseStep 12877501 = 4829063) B4829063
theorem B17170001 : Blo 2009435 17170001 := bstep (se 2 (by rfl) ⟨6438750, by rfl⟩ : syracuseStep 17170001 = 12877501) B12877501
theorem B11446667 : Blo 2009435 11446667 := bstep (se 1 (by rfl) ⟨8585000, by rfl⟩ : syracuseStep 11446667 = 17170001) B17170001
theorem B7631111 : Blo 2009435 7631111 := bstep (se 1 (by rfl) ⟨5723333, by rfl⟩ : syracuseStep 7631111 = 11446667) B11446667
theorem B5087407 : Blo 2009435 5087407 := bstep (se 1 (by rfl) ⟨3815555, by rfl⟩ : syracuseStep 5087407 = 7631111) B7631111
theorem B6783209 : Blo 2009435 6783209 := bstep (se 2 (by rfl) ⟨2543703, by rfl⟩ : syracuseStep 6783209 = 5087407) B5087407
theorem B4522139 : Blo 2009435 4522139 := bstep (se 1 (by rfl) ⟨3391604, by rfl⟩ : syracuseStep 4522139 = 6783209) B6783209
theorem B3014759 : Blo 2009435 3014759 := bstep (se 1 (by rfl) ⟨2261069, by rfl⟩ : syracuseStep 3014759 = 4522139) B4522139
theorem B2009839 : Blo 2009435 2009839 := bstep (se 1 (by rfl) ⟨1507379, by rfl⟩ : syracuseStep 2009839 = 3014759) B3014759
theorem B3014765 : Blo 2009435 3014765 := bbase (se 3 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 3014765 = 1130537) (by norm_num)
theorem B2009843 : Blo 2009435 2009843 := bstep (se 1 (by rfl) ⟨1507382, by rfl⟩ : syracuseStep 2009843 = 3014765) B3014765
theorem B4522157 : Blo 2009435 4522157 := bbase (se 3 (by rfl) ⟨847904, by rfl⟩ : syracuseStep 4522157 = 1695809) (by norm_num)
theorem B3014771 : Blo 2009435 3014771 := bstep (se 1 (by rfl) ⟨2261078, by rfl⟩ : syracuseStep 3014771 = 4522157) B4522157
theorem B2009847 : Blo 2009435 2009847 := bstep (se 1 (by rfl) ⟨1507385, by rfl⟩ : syracuseStep 2009847 = 3014771) B3014771
theorem B10865461 : Blo 2009435 10865461 := bbase (se 5 (by rfl) ⟨509318, by rfl⟩ : syracuseStep 10865461 = 1018637) (by norm_num)
theorem B14487281 : Blo 2009435 14487281 := bstep (se 2 (by rfl) ⟨5432730, by rfl⟩ : syracuseStep 14487281 = 10865461) B10865461
theorem B9658187 : Blo 2009435 9658187 := bstep (se 1 (by rfl) ⟨7243640, by rfl⟩ : syracuseStep 9658187 = 14487281) B14487281
theorem B6438791 : Blo 2009435 6438791 := bstep (se 1 (by rfl) ⟨4829093, by rfl⟩ : syracuseStep 6438791 = 9658187) B9658187
theorem B4292527 : Blo 2009435 4292527 := bstep (se 1 (by rfl) ⟨3219395, by rfl⟩ : syracuseStep 4292527 = 6438791) B6438791
theorem B5723369 : Blo 2009435 5723369 := bstep (se 2 (by rfl) ⟨2146263, by rfl⟩ : syracuseStep 5723369 = 4292527) B4292527
theorem B3815579 : Blo 2009435 3815579 := bstep (se 1 (by rfl) ⟨2861684, by rfl⟩ : syracuseStep 3815579 = 5723369) B5723369
theorem B2543719 : Blo 2009435 2543719 := bstep (se 1 (by rfl) ⟨1907789, by rfl⟩ : syracuseStep 2543719 = 3815579) B3815579
theorem B3391625 : Blo 2009435 3391625 := bstep (se 2 (by rfl) ⟨1271859, by rfl⟩ : syracuseStep 3391625 = 2543719) B2543719
theorem B2261083 : Blo 2009435 2261083 := bstep (se 1 (by rfl) ⟨1695812, by rfl⟩ : syracuseStep 2261083 = 3391625) B3391625
theorem B3014777 : Blo 2009435 3014777 := bstep (se 2 (by rfl) ⟨1130541, by rfl⟩ : syracuseStep 3014777 = 2261083) B2261083
theorem B2009851 : Blo 2009435 2009851 := bstep (se 1 (by rfl) ⟨1507388, by rfl⟩ : syracuseStep 2009851 = 3014777) B3014777
theorem B4829101 : Blo 2009435 4829101 := bbase (se 3 (by rfl) ⟨905456, by rfl⟩ : syracuseStep 4829101 = 1810913) (by norm_num)
theorem B25755205 : Blo 2009435 25755205 := bstep (se 4 (by rfl) ⟨2414550, by rfl⟩ : syracuseStep 25755205 = 4829101) B4829101
theorem B34340273 : Blo 2009435 34340273 := bstep (se 2 (by rfl) ⟨12877602, by rfl⟩ : syracuseStep 34340273 = 25755205) B25755205
theorem B22893515 : Blo 2009435 22893515 := bstep (se 1 (by rfl) ⟨17170136, by rfl⟩ : syracuseStep 22893515 = 34340273) B34340273
theorem B15262343 : Blo 2009435 15262343 := bstep (se 1 (by rfl) ⟨11446757, by rfl⟩ : syracuseStep 15262343 = 22893515) B22893515
theorem B10174895 : Blo 2009435 10174895 := bstep (se 1 (by rfl) ⟨7631171, by rfl⟩ : syracuseStep 10174895 = 15262343) B15262343
theorem B6783263 : Blo 2009435 6783263 := bstep (se 1 (by rfl) ⟨5087447, by rfl⟩ : syracuseStep 6783263 = 10174895) B10174895
theorem B4522175 : Blo 2009435 4522175 := bstep (se 1 (by rfl) ⟨3391631, by rfl⟩ : syracuseStep 4522175 = 6783263) B6783263
theorem B3014783 : Blo 2009435 3014783 := bstep (se 1 (by rfl) ⟨2261087, by rfl⟩ : syracuseStep 3014783 = 4522175) B4522175
theorem B2009855 : Blo 2009435 2009855 := bstep (se 1 (by rfl) ⟨1507391, by rfl⟩ : syracuseStep 2009855 = 3014783) B3014783
theorem B3014789 : Blo 2009435 3014789 := bbase (se 4 (by rfl) ⟨282636, by rfl⟩ : syracuseStep 3014789 = 565273) (by norm_num)
theorem B2009859 : Blo 2009435 2009859 := bstep (se 1 (by rfl) ⟨1507394, by rfl⟩ : syracuseStep 2009859 = 3014789) B3014789
theorem B3391645 : Blo 2009435 3391645 := bbase (se 3 (by rfl) ⟨635933, by rfl⟩ : syracuseStep 3391645 = 1271867) (by norm_num)
theorem B4522193 : Blo 2009435 4522193 := bstep (se 2 (by rfl) ⟨1695822, by rfl⟩ : syracuseStep 4522193 = 3391645) B3391645
theorem B3014795 : Blo 2009435 3014795 := bstep (se 1 (by rfl) ⟨2261096, by rfl⟩ : syracuseStep 3014795 = 4522193) B4522193
theorem B2009863 : Blo 2009435 2009863 := bstep (se 1 (by rfl) ⟨1507397, by rfl⟩ : syracuseStep 2009863 = 3014795) B3014795
theorem B2261101 : Blo 2009435 2261101 := bbase (se 3 (by rfl) ⟨423956, by rfl⟩ : syracuseStep 2261101 = 847913) (by norm_num)
theorem B3014801 : Blo 2009435 3014801 := bstep (se 2 (by rfl) ⟨1130550, by rfl⟩ : syracuseStep 3014801 = 2261101) B2261101
theorem B2009867 : Blo 2009435 2009867 := bstep (se 1 (by rfl) ⟨1507400, by rfl⟩ : syracuseStep 2009867 = 3014801) B3014801
theorem B6783317 : Blo 2009435 6783317 := bbase (se 10 (by rfl) ⟨9936, by rfl⟩ : syracuseStep 6783317 = 19873) (by norm_num)
theorem B4522211 : Blo 2009435 4522211 := bstep (se 1 (by rfl) ⟨3391658, by rfl⟩ : syracuseStep 4522211 = 6783317) B6783317
theorem B3014807 : Blo 2009435 3014807 := bstep (se 1 (by rfl) ⟨2261105, by rfl⟩ : syracuseStep 3014807 = 4522211) B4522211
theorem B2009871 : Blo 2009435 2009871 := bstep (se 1 (by rfl) ⟨1507403, by rfl⟩ : syracuseStep 2009871 = 3014807) B3014807
theorem B3014813 : Blo 2009435 3014813 := bbase (se 3 (by rfl) ⟨565277, by rfl⟩ : syracuseStep 3014813 = 1130555) (by norm_num)
theorem B2009875 : Blo 2009435 2009875 := bstep (se 1 (by rfl) ⟨1507406, by rfl⟩ : syracuseStep 2009875 = 3014813) B3014813
theorem B4522229 : Blo 2009435 4522229 := bbase (se 5 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 4522229 = 423959) (by norm_num)
theorem B3014819 : Blo 2009435 3014819 := bstep (se 1 (by rfl) ⟨2261114, by rfl⟩ : syracuseStep 3014819 = 4522229) B4522229
theorem B2009879 : Blo 2009435 2009879 := bstep (se 1 (by rfl) ⟨1507409, by rfl⟩ : syracuseStep 2009879 = 3014819) B3014819
theorem B3621877 : Blo 2009435 3621877 := bbase (se 5 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 3621877 = 339551) (by norm_num)
theorem B19316677 : Blo 2009435 19316677 := bstep (se 4 (by rfl) ⟨1810938, by rfl⟩ : syracuseStep 19316677 = 3621877) B3621877
theorem B25755569 : Blo 2009435 25755569 := bstep (se 2 (by rfl) ⟨9658338, by rfl⟩ : syracuseStep 25755569 = 19316677) B19316677
theorem B17170379 : Blo 2009435 17170379 := bstep (se 1 (by rfl) ⟨12877784, by rfl⟩ : syracuseStep 17170379 = 25755569) B25755569
theorem B11446919 : Blo 2009435 11446919 := bstep (se 1 (by rfl) ⟨8585189, by rfl⟩ : syracuseStep 11446919 = 17170379) B17170379
theorem B7631279 : Blo 2009435 7631279 := bstep (se 1 (by rfl) ⟨5723459, by rfl⟩ : syracuseStep 7631279 = 11446919) B11446919
theorem B5087519 : Blo 2009435 5087519 := bstep (se 1 (by rfl) ⟨3815639, by rfl⟩ : syracuseStep 5087519 = 7631279) B7631279
theorem B3391679 : Blo 2009435 3391679 := bstep (se 1 (by rfl) ⟨2543759, by rfl⟩ : syracuseStep 3391679 = 5087519) B5087519
theorem B2261119 : Blo 2009435 2261119 := bstep (se 1 (by rfl) ⟨1695839, by rfl⟩ : syracuseStep 2261119 = 3391679) B3391679
theorem B3014825 : Blo 2009435 3014825 := bstep (se 2 (by rfl) ⟨1130559, by rfl⟩ : syracuseStep 3014825 = 2261119) B2261119
theorem B2009883 : Blo 2009435 2009883 := bstep (se 1 (by rfl) ⟨1507412, by rfl⟩ : syracuseStep 2009883 = 3014825) B3014825
theorem B6526757 : Blo 2009435 6526757 := bbase (se 4 (by rfl) ⟨611883, by rfl⟩ : syracuseStep 6526757 = 1223767) (by norm_num)
theorem B4351171 : Blo 2009435 4351171 := bstep (se 1 (by rfl) ⟨3263378, by rfl⟩ : syracuseStep 4351171 = 6526757) B6526757
theorem B5801561 : Blo 2009435 5801561 := bstep (se 2 (by rfl) ⟨2175585, by rfl⟩ : syracuseStep 5801561 = 4351171) B4351171
theorem B3867707 : Blo 2009435 3867707 := bstep (se 1 (by rfl) ⟨2900780, by rfl⟩ : syracuseStep 3867707 = 5801561) B5801561
theorem B10313885 : Blo 2009435 10313885 := bstep (se 3 (by rfl) ⟨1933853, by rfl⟩ : syracuseStep 10313885 = 3867707) B3867707
theorem B6875923 : Blo 2009435 6875923 := bstep (se 1 (by rfl) ⟨5156942, by rfl⟩ : syracuseStep 6875923 = 10313885) B10313885
theorem B9167897 : Blo 2009435 9167897 := bstep (se 2 (by rfl) ⟨3437961, by rfl⟩ : syracuseStep 9167897 = 6875923) B6875923
theorem B6111931 : Blo 2009435 6111931 := bstep (se 1 (by rfl) ⟨4583948, by rfl⟩ : syracuseStep 6111931 = 9167897) B9167897
theorem B8149241 : Blo 2009435 8149241 := bstep (se 2 (by rfl) ⟨3055965, by rfl⟩ : syracuseStep 8149241 = 6111931) B6111931
theorem B5432827 : Blo 2009435 5432827 := bstep (se 1 (by rfl) ⟨4074620, by rfl⟩ : syracuseStep 5432827 = 8149241) B8149241
theorem B7243769 : Blo 2009435 7243769 := bstep (se 2 (by rfl) ⟨2716413, by rfl⟩ : syracuseStep 7243769 = 5432827) B5432827
theorem B4829179 : Blo 2009435 4829179 := bstep (se 1 (by rfl) ⟨3621884, by rfl⟩ : syracuseStep 4829179 = 7243769) B7243769
theorem B6438905 : Blo 2009435 6438905 := bstep (se 2 (by rfl) ⟨2414589, by rfl⟩ : syracuseStep 6438905 = 4829179) B4829179
theorem B4292603 : Blo 2009435 4292603 := bstep (se 1 (by rfl) ⟨3219452, by rfl⟩ : syracuseStep 4292603 = 6438905) B6438905
theorem B2861735 : Blo 2009435 2861735 := bstep (se 1 (by rfl) ⟨2146301, by rfl⟩ : syracuseStep 2861735 = 4292603) B4292603
theorem B7631293 : Blo 2009435 7631293 := bstep (se 3 (by rfl) ⟨1430867, by rfl⟩ : syracuseStep 7631293 = 2861735) B2861735
theorem B10175057 : Blo 2009435 10175057 := bstep (se 2 (by rfl) ⟨3815646, by rfl⟩ : syracuseStep 10175057 = 7631293) B7631293
theorem B6783371 : Blo 2009435 6783371 := bstep (se 1 (by rfl) ⟨5087528, by rfl⟩ : syracuseStep 6783371 = 10175057) B10175057
theorem B4522247 : Blo 2009435 4522247 := bstep (se 1 (by rfl) ⟨3391685, by rfl⟩ : syracuseStep 4522247 = 6783371) B6783371
theorem B3014831 : Blo 2009435 3014831 := bstep (se 1 (by rfl) ⟨2261123, by rfl⟩ : syracuseStep 3014831 = 4522247) B4522247
theorem B2009887 : Blo 2009435 2009887 := bstep (se 1 (by rfl) ⟨1507415, by rfl⟩ : syracuseStep 2009887 = 3014831) B3014831
theorem B3014837 : Blo 2009435 3014837 := bbase (se 5 (by rfl) ⟨141320, by rfl⟩ : syracuseStep 3014837 = 282641) (by norm_num)
theorem B2009891 : Blo 2009435 2009891 := bstep (se 1 (by rfl) ⟨1507418, by rfl⟩ : syracuseStep 2009891 = 3014837) B3014837
theorem B5087549 : Blo 2009435 5087549 := bbase (se 3 (by rfl) ⟨953915, by rfl⟩ : syracuseStep 5087549 = 1907831) (by norm_num)
theorem B3391699 : Blo 2009435 3391699 := bstep (se 1 (by rfl) ⟨2543774, by rfl⟩ : syracuseStep 3391699 = 5087549) B5087549
theorem B4522265 : Blo 2009435 4522265 := bstep (se 2 (by rfl) ⟨1695849, by rfl⟩ : syracuseStep 4522265 = 3391699) B3391699
theorem B3014843 : Blo 2009435 3014843 := bstep (se 1 (by rfl) ⟨2261132, by rfl⟩ : syracuseStep 3014843 = 4522265) B4522265
theorem B2009895 : Blo 2009435 2009895 := bstep (se 1 (by rfl) ⟨1507421, by rfl⟩ : syracuseStep 2009895 = 3014843) B3014843
theorem B2261137 : Blo 2009435 2261137 := bbase (se 2 (by rfl) ⟨847926, by rfl⟩ : syracuseStep 2261137 = 1695853) (by norm_num)
theorem B3014849 : Blo 2009435 3014849 := bstep (se 2 (by rfl) ⟨1130568, by rfl⟩ : syracuseStep 3014849 = 2261137) B2261137
theorem B2009899 : Blo 2009435 2009899 := bstep (se 1 (by rfl) ⟨1507424, by rfl⟩ : syracuseStep 2009899 = 3014849) B3014849
theorem B3815677 : Blo 2009435 3815677 := bbase (se 3 (by rfl) ⟨715439, by rfl⟩ : syracuseStep 3815677 = 1430879) (by norm_num)
theorem B5087569 : Blo 2009435 5087569 := bstep (se 2 (by rfl) ⟨1907838, by rfl⟩ : syracuseStep 5087569 = 3815677) B3815677
theorem B6783425 : Blo 2009435 6783425 := bstep (se 2 (by rfl) ⟨2543784, by rfl⟩ : syracuseStep 6783425 = 5087569) B5087569
theorem B4522283 : Blo 2009435 4522283 := bstep (se 1 (by rfl) ⟨3391712, by rfl⟩ : syracuseStep 4522283 = 6783425) B6783425
theorem B3014855 : Blo 2009435 3014855 := bstep (se 1 (by rfl) ⟨2261141, by rfl⟩ : syracuseStep 3014855 = 4522283) B4522283
theorem B2009903 : Blo 2009435 2009903 := bstep (se 1 (by rfl) ⟨1507427, by rfl⟩ : syracuseStep 2009903 = 3014855) B3014855
theorem B3014861 : Blo 2009435 3014861 := bbase (se 3 (by rfl) ⟨565286, by rfl⟩ : syracuseStep 3014861 = 1130573) (by norm_num)
theorem B2009907 : Blo 2009435 2009907 := bstep (se 1 (by rfl) ⟨1507430, by rfl⟩ : syracuseStep 2009907 = 3014861) B3014861
theorem B4522301 : Blo 2009435 4522301 := bbase (se 3 (by rfl) ⟨847931, by rfl⟩ : syracuseStep 4522301 = 1695863) (by norm_num)
theorem B3014867 : Blo 2009435 3014867 := bstep (se 1 (by rfl) ⟨2261150, by rfl⟩ : syracuseStep 3014867 = 4522301) B4522301
theorem B2009911 : Blo 2009435 2009911 := bstep (se 1 (by rfl) ⟨1507433, by rfl⟩ : syracuseStep 2009911 = 3014867) B3014867
theorem B3391733 : Blo 2009435 3391733 := bbase (se 5 (by rfl) ⟨158987, by rfl⟩ : syracuseStep 3391733 = 317975) (by norm_num)
theorem B2261155 : Blo 2009435 2261155 := bstep (se 1 (by rfl) ⟨1695866, by rfl⟩ : syracuseStep 2261155 = 3391733) B3391733
theorem B3014873 : Blo 2009435 3014873 := bstep (se 2 (by rfl) ⟨1130577, by rfl⟩ : syracuseStep 3014873 = 2261155) B2261155
theorem B2009915 : Blo 2009435 2009915 := bstep (se 1 (by rfl) ⟨1507436, by rfl⟩ : syracuseStep 2009915 = 3014873) B3014873
theorem B2480965 : Blo 2009435 2480965 := bbase (se 4 (by rfl) ⟨232590, by rfl⟩ : syracuseStep 2480965 = 465181) (by norm_num)
theorem B13231813 : Blo 2009435 13231813 := bstep (se 4 (by rfl) ⟨1240482, by rfl⟩ : syracuseStep 13231813 = 2480965) B2480965
theorem B17642417 : Blo 2009435 17642417 := bstep (se 2 (by rfl) ⟨6615906, by rfl⟩ : syracuseStep 17642417 = 13231813) B13231813
theorem B188185781 : Blo 2009435 188185781 := bstep (se 5 (by rfl) ⟨8821208, by rfl⟩ : syracuseStep 188185781 = 17642417) B17642417
theorem B125457187 : Blo 2009435 125457187 := bstep (se 1 (by rfl) ⟨94092890, by rfl⟩ : syracuseStep 125457187 = 188185781) B188185781
theorem B167276249 : Blo 2009435 167276249 := bstep (se 2 (by rfl) ⟨62728593, by rfl⟩ : syracuseStep 167276249 = 125457187) B125457187
theorem B111517499 : Blo 2009435 111517499 := bstep (se 1 (by rfl) ⟨83638124, by rfl⟩ : syracuseStep 111517499 = 167276249) B167276249
theorem B74344999 : Blo 2009435 74344999 := bstep (se 1 (by rfl) ⟨55758749, by rfl⟩ : syracuseStep 74344999 = 111517499) B111517499
theorem B99126665 : Blo 2009435 99126665 := bstep (se 2 (by rfl) ⟨37172499, by rfl⟩ : syracuseStep 99126665 = 74344999) B74344999
theorem B66084443 : Blo 2009435 66084443 := bstep (se 1 (by rfl) ⟨49563332, by rfl⟩ : syracuseStep 66084443 = 99126665) B99126665
theorem B44056295 : Blo 2009435 44056295 := bstep (se 1 (by rfl) ⟨33042221, by rfl⟩ : syracuseStep 44056295 = 66084443) B66084443
theorem B29370863 : Blo 2009435 29370863 := bstep (se 1 (by rfl) ⟨22028147, by rfl⟩ : syracuseStep 29370863 = 44056295) B44056295
theorem B78322301 : Blo 2009435 78322301 := bstep (se 3 (by rfl) ⟨14685431, by rfl⟩ : syracuseStep 78322301 = 29370863) B29370863
theorem B52214867 : Blo 2009435 52214867 := bstep (se 1 (by rfl) ⟨39161150, by rfl⟩ : syracuseStep 52214867 = 78322301) B78322301
theorem B34809911 : Blo 2009435 34809911 := bstep (se 1 (by rfl) ⟨26107433, by rfl⟩ : syracuseStep 34809911 = 52214867) B52214867
theorem B23206607 : Blo 2009435 23206607 := bstep (se 1 (by rfl) ⟨17404955, by rfl⟩ : syracuseStep 23206607 = 34809911) B34809911
theorem B15471071 : Blo 2009435 15471071 := bstep (se 1 (by rfl) ⟨11603303, by rfl⟩ : syracuseStep 15471071 = 23206607) B23206607
theorem B10314047 : Blo 2009435 10314047 := bstep (se 1 (by rfl) ⟨7735535, by rfl⟩ : syracuseStep 10314047 = 15471071) B15471071
theorem B6876031 : Blo 2009435 6876031 := bstep (se 1 (by rfl) ⟨5157023, by rfl⟩ : syracuseStep 6876031 = 10314047) B10314047
theorem B9168041 : Blo 2009435 9168041 := bstep (se 2 (by rfl) ⟨3438015, by rfl⟩ : syracuseStep 9168041 = 6876031) B6876031
theorem B6112027 : Blo 2009435 6112027 := bstep (se 1 (by rfl) ⟨4584020, by rfl⟩ : syracuseStep 6112027 = 9168041) B9168041
theorem B32597477 : Blo 2009435 32597477 := bstep (se 4 (by rfl) ⟨3056013, by rfl⟩ : syracuseStep 32597477 = 6112027) B6112027
theorem B21731651 : Blo 2009435 21731651 := bstep (se 1 (by rfl) ⟨16298738, by rfl⟩ : syracuseStep 21731651 = 32597477) B32597477
theorem B14487767 : Blo 2009435 14487767 := bstep (se 1 (by rfl) ⟨10865825, by rfl⟩ : syracuseStep 14487767 = 21731651) B21731651
theorem B9658511 : Blo 2009435 9658511 := bstep (se 1 (by rfl) ⟨7243883, by rfl⟩ : syracuseStep 9658511 = 14487767) B14487767
theorem B6439007 : Blo 2009435 6439007 := bstep (se 1 (by rfl) ⟨4829255, by rfl⟩ : syracuseStep 6439007 = 9658511) B9658511
theorem B4292671 : Blo 2009435 4292671 := bstep (se 1 (by rfl) ⟨3219503, by rfl⟩ : syracuseStep 4292671 = 6439007) B6439007
theorem B5723561 : Blo 2009435 5723561 := bstep (se 2 (by rfl) ⟨2146335, by rfl⟩ : syracuseStep 5723561 = 4292671) B4292671
theorem B15262829 : Blo 2009435 15262829 := bstep (se 3 (by rfl) ⟨2861780, by rfl⟩ : syracuseStep 15262829 = 5723561) B5723561
theorem B10175219 : Blo 2009435 10175219 := bstep (se 1 (by rfl) ⟨7631414, by rfl⟩ : syracuseStep 10175219 = 15262829) B15262829
theorem B6783479 : Blo 2009435 6783479 := bstep (se 1 (by rfl) ⟨5087609, by rfl⟩ : syracuseStep 6783479 = 10175219) B10175219
theorem B4522319 : Blo 2009435 4522319 := bstep (se 1 (by rfl) ⟨3391739, by rfl⟩ : syracuseStep 4522319 = 6783479) B6783479
theorem B3014879 : Blo 2009435 3014879 := bstep (se 1 (by rfl) ⟨2261159, by rfl⟩ : syracuseStep 3014879 = 4522319) B4522319
theorem B2009919 : Blo 2009435 2009919 := bstep (se 1 (by rfl) ⟨1507439, by rfl⟩ : syracuseStep 2009919 = 3014879) B3014879
theorem B3014885 : Blo 2009435 3014885 := bbase (se 4 (by rfl) ⟨282645, by rfl⟩ : syracuseStep 3014885 = 565291) (by norm_num)
theorem B2009923 : Blo 2009435 2009923 := bstep (se 1 (by rfl) ⟨1507442, by rfl⟩ : syracuseStep 2009923 = 3014885) B3014885
theorem B3219517 : Blo 2009435 3219517 := bbase (se 3 (by rfl) ⟨603659, by rfl⟩ : syracuseStep 3219517 = 1207319) (by norm_num)
theorem B4292689 : Blo 2009435 4292689 := bstep (se 2 (by rfl) ⟨1609758, by rfl⟩ : syracuseStep 4292689 = 3219517) B3219517
theorem B5723585 : Blo 2009435 5723585 := bstep (se 2 (by rfl) ⟨2146344, by rfl⟩ : syracuseStep 5723585 = 4292689) B4292689
theorem B3815723 : Blo 2009435 3815723 := bstep (se 1 (by rfl) ⟨2861792, by rfl⟩ : syracuseStep 3815723 = 5723585) B5723585
theorem B2543815 : Blo 2009435 2543815 := bstep (se 1 (by rfl) ⟨1907861, by rfl⟩ : syracuseStep 2543815 = 3815723) B3815723
theorem B3391753 : Blo 2009435 3391753 := bstep (se 2 (by rfl) ⟨1271907, by rfl⟩ : syracuseStep 3391753 = 2543815) B2543815
theorem B4522337 : Blo 2009435 4522337 := bstep (se 2 (by rfl) ⟨1695876, by rfl⟩ : syracuseStep 4522337 = 3391753) B3391753
theorem B3014891 : Blo 2009435 3014891 := bstep (se 1 (by rfl) ⟨2261168, by rfl⟩ : syracuseStep 3014891 = 4522337) B4522337
theorem B2009927 : Blo 2009435 2009927 := bstep (se 1 (by rfl) ⟨1507445, by rfl⟩ : syracuseStep 2009927 = 3014891) B3014891
theorem B2261173 : Blo 2009435 2261173 := bbase (se 5 (by rfl) ⟨105992, by rfl⟩ : syracuseStep 2261173 = 211985) (by norm_num)
theorem B3014897 : Blo 2009435 3014897 := bstep (se 2 (by rfl) ⟨1130586, by rfl⟩ : syracuseStep 3014897 = 2261173) B2261173
theorem B2009931 : Blo 2009435 2009931 := bstep (se 1 (by rfl) ⟨1507448, by rfl⟩ : syracuseStep 2009931 = 3014897) B3014897
theorem B2543825 : Blo 2009435 2543825 := bbase (se 2 (by rfl) ⟨953934, by rfl⟩ : syracuseStep 2543825 = 1907869) (by norm_num)
theorem B6783533 : Blo 2009435 6783533 := bstep (se 3 (by rfl) ⟨1271912, by rfl⟩ : syracuseStep 6783533 = 2543825) B2543825
theorem B4522355 : Blo 2009435 4522355 := bstep (se 1 (by rfl) ⟨3391766, by rfl⟩ : syracuseStep 4522355 = 6783533) B6783533
theorem B3014903 : Blo 2009435 3014903 := bstep (se 1 (by rfl) ⟨2261177, by rfl⟩ : syracuseStep 3014903 = 4522355) B4522355
theorem B2009935 : Blo 2009435 2009935 := bstep (se 1 (by rfl) ⟨1507451, by rfl⟩ : syracuseStep 2009935 = 3014903) B3014903
theorem B3014909 : Blo 2009435 3014909 := bbase (se 3 (by rfl) ⟨565295, by rfl⟩ : syracuseStep 3014909 = 1130591) (by norm_num)
theorem B2009939 : Blo 2009435 2009939 := bstep (se 1 (by rfl) ⟨1507454, by rfl⟩ : syracuseStep 2009939 = 3014909) B3014909
theorem B4522373 : Blo 2009435 4522373 := bbase (se 4 (by rfl) ⟨423972, by rfl⟩ : syracuseStep 4522373 = 847945) (by norm_num)
theorem B3014915 : Blo 2009435 3014915 := bstep (se 1 (by rfl) ⟨2261186, by rfl⟩ : syracuseStep 3014915 = 4522373) B4522373
theorem B2009943 : Blo 2009435 2009943 := bstep (se 1 (by rfl) ⟨1507457, by rfl⟩ : syracuseStep 2009943 = 3014915) B3014915
theorem B2861821 : Blo 2009435 2861821 := bbase (se 3 (by rfl) ⟨536591, by rfl⟩ : syracuseStep 2861821 = 1073183) (by norm_num)
theorem B3815761 : Blo 2009435 3815761 := bstep (se 2 (by rfl) ⟨1430910, by rfl⟩ : syracuseStep 3815761 = 2861821) B2861821
theorem B5087681 : Blo 2009435 5087681 := bstep (se 2 (by rfl) ⟨1907880, by rfl⟩ : syracuseStep 5087681 = 3815761) B3815761
theorem B3391787 : Blo 2009435 3391787 := bstep (se 1 (by rfl) ⟨2543840, by rfl⟩ : syracuseStep 3391787 = 5087681) B5087681
theorem B2261191 : Blo 2009435 2261191 := bstep (se 1 (by rfl) ⟨1695893, by rfl⟩ : syracuseStep 2261191 = 3391787) B3391787
theorem B3014921 : Blo 2009435 3014921 := bstep (se 2 (by rfl) ⟨1130595, by rfl⟩ : syracuseStep 3014921 = 2261191) B2261191
theorem B2009947 : Blo 2009435 2009947 := bstep (se 1 (by rfl) ⟨1507460, by rfl⟩ : syracuseStep 2009947 = 3014921) B3014921
theorem B10175381 : Blo 2009435 10175381 := bbase (se 6 (by rfl) ⟨238485, by rfl⟩ : syracuseStep 10175381 = 476971) (by norm_num)
theorem B6783587 : Blo 2009435 6783587 := bstep (se 1 (by rfl) ⟨5087690, by rfl⟩ : syracuseStep 6783587 = 10175381) B10175381
theorem B4522391 : Blo 2009435 4522391 := bstep (se 1 (by rfl) ⟨3391793, by rfl⟩ : syracuseStep 4522391 = 6783587) B6783587
theorem B3014927 : Blo 2009435 3014927 := bstep (se 1 (by rfl) ⟨2261195, by rfl⟩ : syracuseStep 3014927 = 4522391) B4522391
theorem B2009951 : Blo 2009435 2009951 := bstep (se 1 (by rfl) ⟨1507463, by rfl⟩ : syracuseStep 2009951 = 3014927) B3014927
theorem B3014933 : Blo 2009435 3014933 := bbase (se 6 (by rfl) ⟨70662, by rfl⟩ : syracuseStep 3014933 = 141325) (by norm_num)
theorem B2009955 : Blo 2009435 2009955 := bstep (se 1 (by rfl) ⟨1507466, by rfl⟩ : syracuseStep 2009955 = 3014933) B3014933
theorem B4351325 : Blo 2009435 4351325 := bbase (se 3 (by rfl) ⟨815873, by rfl⟩ : syracuseStep 4351325 = 1631747) (by norm_num)
theorem B46414133 : Blo 2009435 46414133 := bstep (se 5 (by rfl) ⟨2175662, by rfl⟩ : syracuseStep 46414133 = 4351325) B4351325
theorem B30942755 : Blo 2009435 30942755 := bstep (se 1 (by rfl) ⟨23207066, by rfl⟩ : syracuseStep 30942755 = 46414133) B46414133
theorem B20628503 : Blo 2009435 20628503 := bstep (se 1 (by rfl) ⟨15471377, by rfl⟩ : syracuseStep 20628503 = 30942755) B30942755
theorem B13752335 : Blo 2009435 13752335 := bstep (se 1 (by rfl) ⟨10314251, by rfl⟩ : syracuseStep 13752335 = 20628503) B20628503
theorem B9168223 : Blo 2009435 9168223 := bstep (se 1 (by rfl) ⟨6876167, by rfl⟩ : syracuseStep 9168223 = 13752335) B13752335
theorem B12224297 : Blo 2009435 12224297 := bstep (se 2 (by rfl) ⟨4584111, by rfl⟩ : syracuseStep 12224297 = 9168223) B9168223
theorem B32598125 : Blo 2009435 32598125 := bstep (se 3 (by rfl) ⟨6112148, by rfl⟩ : syracuseStep 32598125 = 12224297) B12224297
theorem B21732083 : Blo 2009435 21732083 := bstep (se 1 (by rfl) ⟨16299062, by rfl⟩ : syracuseStep 21732083 = 32598125) B32598125
theorem B14488055 : Blo 2009435 14488055 := bstep (se 1 (by rfl) ⟨10866041, by rfl⟩ : syracuseStep 14488055 = 21732083) B21732083
theorem B9658703 : Blo 2009435 9658703 := bstep (se 1 (by rfl) ⟨7244027, by rfl⟩ : syracuseStep 9658703 = 14488055) B14488055
theorem B25756541 : Blo 2009435 25756541 := bstep (se 3 (by rfl) ⟨4829351, by rfl⟩ : syracuseStep 25756541 = 9658703) B9658703
theorem B17171027 : Blo 2009435 17171027 := bstep (se 1 (by rfl) ⟨12878270, by rfl⟩ : syracuseStep 17171027 = 25756541) B25756541
theorem B11447351 : Blo 2009435 11447351 := bstep (se 1 (by rfl) ⟨8585513, by rfl⟩ : syracuseStep 11447351 = 17171027) B17171027
theorem B7631567 : Blo 2009435 7631567 := bstep (se 1 (by rfl) ⟨5723675, by rfl⟩ : syracuseStep 7631567 = 11447351) B11447351
theorem B5087711 : Blo 2009435 5087711 := bstep (se 1 (by rfl) ⟨3815783, by rfl⟩ : syracuseStep 5087711 = 7631567) B7631567
theorem B3391807 : Blo 2009435 3391807 := bstep (se 1 (by rfl) ⟨2543855, by rfl⟩ : syracuseStep 3391807 = 5087711) B5087711
theorem B4522409 : Blo 2009435 4522409 := bstep (se 2 (by rfl) ⟨1695903, by rfl⟩ : syracuseStep 4522409 = 3391807) B3391807
theorem B3014939 : Blo 2009435 3014939 := bstep (se 1 (by rfl) ⟨2261204, by rfl⟩ : syracuseStep 3014939 = 4522409) B4522409
theorem B2009959 : Blo 2009435 2009959 := bstep (se 1 (by rfl) ⟨1507469, by rfl⟩ : syracuseStep 2009959 = 3014939) B3014939
theorem B2261209 : Blo 2009435 2261209 := bbase (se 2 (by rfl) ⟨847953, by rfl⟩ : syracuseStep 2261209 = 1695907) (by norm_num)
theorem B3014945 : Blo 2009435 3014945 := bstep (se 2 (by rfl) ⟨1130604, by rfl⟩ : syracuseStep 3014945 = 2261209) B2261209
theorem B2009963 : Blo 2009435 2009963 := bstep (se 1 (by rfl) ⟨1507472, by rfl⟩ : syracuseStep 2009963 = 3014945) B3014945
theorem B3219581 : Blo 2009435 3219581 := bbase (se 3 (by rfl) ⟨603671, by rfl⟩ : syracuseStep 3219581 = 1207343) (by norm_num)
theorem B2146387 : Blo 2009435 2146387 := bstep (se 1 (by rfl) ⟨1609790, by rfl⟩ : syracuseStep 2146387 = 3219581) B3219581
theorem B2861849 : Blo 2009435 2861849 := bstep (se 2 (by rfl) ⟨1073193, by rfl⟩ : syracuseStep 2861849 = 2146387) B2146387
theorem B7631597 : Blo 2009435 7631597 := bstep (se 3 (by rfl) ⟨1430924, by rfl⟩ : syracuseStep 7631597 = 2861849) B2861849
theorem B5087731 : Blo 2009435 5087731 := bstep (se 1 (by rfl) ⟨3815798, by rfl⟩ : syracuseStep 5087731 = 7631597) B7631597
theorem B6783641 : Blo 2009435 6783641 := bstep (se 2 (by rfl) ⟨2543865, by rfl⟩ : syracuseStep 6783641 = 5087731) B5087731
theorem B4522427 : Blo 2009435 4522427 := bstep (se 1 (by rfl) ⟨3391820, by rfl⟩ : syracuseStep 4522427 = 6783641) B6783641
theorem B3014951 : Blo 2009435 3014951 := bstep (se 1 (by rfl) ⟨2261213, by rfl⟩ : syracuseStep 3014951 = 4522427) B4522427
theorem B2009967 : Blo 2009435 2009967 := bstep (se 1 (by rfl) ⟨1507475, by rfl⟩ : syracuseStep 2009967 = 3014951) B3014951
theorem B3014957 : Blo 2009435 3014957 := bbase (se 3 (by rfl) ⟨565304, by rfl⟩ : syracuseStep 3014957 = 1130609) (by norm_num)
theorem B2009971 : Blo 2009435 2009971 := bstep (se 1 (by rfl) ⟨1507478, by rfl⟩ : syracuseStep 2009971 = 3014957) B3014957
theorem B4522445 : Blo 2009435 4522445 := bbase (se 3 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 4522445 = 1695917) (by norm_num)
theorem B3014963 : Blo 2009435 3014963 := bstep (se 1 (by rfl) ⟨2261222, by rfl⟩ : syracuseStep 3014963 = 4522445) B4522445
theorem B2009975 : Blo 2009435 2009975 := bstep (se 1 (by rfl) ⟨1507481, by rfl⟩ : syracuseStep 2009975 = 3014963) B3014963
theorem B2543881 : Blo 2009435 2543881 := bbase (se 2 (by rfl) ⟨953955, by rfl⟩ : syracuseStep 2543881 = 1907911) (by norm_num)
theorem B3391841 : Blo 2009435 3391841 := bstep (se 2 (by rfl) ⟨1271940, by rfl⟩ : syracuseStep 3391841 = 2543881) B2543881
theorem B2261227 : Blo 2009435 2261227 := bstep (se 1 (by rfl) ⟨1695920, by rfl⟩ : syracuseStep 2261227 = 3391841) B3391841
theorem B3014969 : Blo 2009435 3014969 := bstep (se 2 (by rfl) ⟨1130613, by rfl⟩ : syracuseStep 3014969 = 2261227) B2261227
theorem B2009979 : Blo 2009435 2009979 := bstep (se 1 (by rfl) ⟨1507484, by rfl⟩ : syracuseStep 2009979 = 3014969) B3014969
theorem B18840437 : Blo 2009435 18840437 := bbase (se 5 (by rfl) ⟨883145, by rfl⟩ : syracuseStep 18840437 = 1766291) (by norm_num)
theorem B12560291 : Blo 2009435 12560291 := bstep (se 1 (by rfl) ⟨9420218, by rfl⟩ : syracuseStep 12560291 = 18840437) B18840437
theorem B8373527 : Blo 2009435 8373527 := bstep (se 1 (by rfl) ⟨6280145, by rfl⟩ : syracuseStep 8373527 = 12560291) B12560291
theorem B5582351 : Blo 2009435 5582351 := bstep (se 1 (by rfl) ⟨4186763, by rfl⟩ : syracuseStep 5582351 = 8373527) B8373527
theorem B14886269 : Blo 2009435 14886269 := bstep (se 3 (by rfl) ⟨2791175, by rfl⟩ : syracuseStep 14886269 = 5582351) B5582351
theorem B9924179 : Blo 2009435 9924179 := bstep (se 1 (by rfl) ⟨7443134, by rfl⟩ : syracuseStep 9924179 = 14886269) B14886269
theorem B26464477 : Blo 2009435 26464477 := bstep (se 3 (by rfl) ⟨4962089, by rfl⟩ : syracuseStep 26464477 = 9924179) B9924179
theorem B35285969 : Blo 2009435 35285969 := bstep (se 2 (by rfl) ⟨13232238, by rfl⟩ : syracuseStep 35285969 = 26464477) B26464477
theorem B94095917 : Blo 2009435 94095917 := bstep (se 3 (by rfl) ⟨17642984, by rfl⟩ : syracuseStep 94095917 = 35285969) B35285969
theorem B62730611 : Blo 2009435 62730611 := bstep (se 1 (by rfl) ⟨47047958, by rfl⟩ : syracuseStep 62730611 = 94095917) B94095917
theorem B41820407 : Blo 2009435 41820407 := bstep (se 1 (by rfl) ⟨31365305, by rfl⟩ : syracuseStep 41820407 = 62730611) B62730611
theorem B27880271 : Blo 2009435 27880271 := bstep (se 1 (by rfl) ⟨20910203, by rfl⟩ : syracuseStep 27880271 = 41820407) B41820407
theorem B18586847 : Blo 2009435 18586847 := bstep (se 1 (by rfl) ⟨13940135, by rfl⟩ : syracuseStep 18586847 = 27880271) B27880271
theorem B12391231 : Blo 2009435 12391231 := bstep (se 1 (by rfl) ⟨9293423, by rfl⟩ : syracuseStep 12391231 = 18586847) B18586847
theorem B16521641 : Blo 2009435 16521641 := bstep (se 2 (by rfl) ⟨6195615, by rfl⟩ : syracuseStep 16521641 = 12391231) B12391231
theorem B11014427 : Blo 2009435 11014427 := bstep (se 1 (by rfl) ⟨8260820, by rfl⟩ : syracuseStep 11014427 = 16521641) B16521641
theorem B29371805 : Blo 2009435 29371805 := bstep (se 3 (by rfl) ⟨5507213, by rfl⟩ : syracuseStep 29371805 = 11014427) B11014427
theorem B19581203 : Blo 2009435 19581203 := bstep (se 1 (by rfl) ⟨14685902, by rfl⟩ : syracuseStep 19581203 = 29371805) B29371805
theorem B13054135 : Blo 2009435 13054135 := bstep (se 1 (by rfl) ⟨9790601, by rfl⟩ : syracuseStep 13054135 = 19581203) B19581203
theorem B17405513 : Blo 2009435 17405513 := bstep (se 2 (by rfl) ⟨6527067, by rfl⟩ : syracuseStep 17405513 = 13054135) B13054135
theorem B11603675 : Blo 2009435 11603675 := bstep (se 1 (by rfl) ⟨8702756, by rfl⟩ : syracuseStep 11603675 = 17405513) B17405513
theorem B7735783 : Blo 2009435 7735783 := bstep (se 1 (by rfl) ⟨5801837, by rfl⟩ : syracuseStep 7735783 = 11603675) B11603675
theorem B10314377 : Blo 2009435 10314377 := bstep (se 2 (by rfl) ⟨3867891, by rfl⟩ : syracuseStep 10314377 = 7735783) B7735783
theorem B6876251 : Blo 2009435 6876251 := bstep (se 1 (by rfl) ⟨5157188, by rfl⟩ : syracuseStep 6876251 = 10314377) B10314377
theorem B4584167 : Blo 2009435 4584167 := bstep (se 1 (by rfl) ⟨3438125, by rfl⟩ : syracuseStep 4584167 = 6876251) B6876251
theorem B3056111 : Blo 2009435 3056111 := bstep (se 1 (by rfl) ⟨2292083, by rfl⟩ : syracuseStep 3056111 = 4584167) B4584167
theorem B2037407 : Blo 2009435 2037407 := bstep (se 1 (by rfl) ⟨1528055, by rfl⟩ : syracuseStep 2037407 = 3056111) B3056111
theorem B5433085 : Blo 2009435 5433085 := bstep (se 3 (by rfl) ⟨1018703, by rfl⟩ : syracuseStep 5433085 = 2037407) B2037407
theorem B28976453 : Blo 2009435 28976453 := bstep (se 4 (by rfl) ⟨2716542, by rfl⟩ : syracuseStep 28976453 = 5433085) B5433085
theorem B19317635 : Blo 2009435 19317635 := bstep (se 1 (by rfl) ⟨14488226, by rfl⟩ : syracuseStep 19317635 = 28976453) B28976453
theorem B12878423 : Blo 2009435 12878423 := bstep (se 1 (by rfl) ⟨9658817, by rfl⟩ : syracuseStep 12878423 = 19317635) B19317635
theorem B8585615 : Blo 2009435 8585615 := bstep (se 1 (by rfl) ⟨6439211, by rfl⟩ : syracuseStep 8585615 = 12878423) B12878423
theorem B22894973 : Blo 2009435 22894973 := bstep (se 3 (by rfl) ⟨4292807, by rfl⟩ : syracuseStep 22894973 = 8585615) B8585615
theorem B15263315 : Blo 2009435 15263315 := bstep (se 1 (by rfl) ⟨11447486, by rfl⟩ : syracuseStep 15263315 = 22894973) B22894973
theorem B10175543 : Blo 2009435 10175543 := bstep (se 1 (by rfl) ⟨7631657, by rfl⟩ : syracuseStep 10175543 = 15263315) B15263315
theorem B6783695 : Blo 2009435 6783695 := bstep (se 1 (by rfl) ⟨5087771, by rfl⟩ : syracuseStep 6783695 = 10175543) B10175543
theorem B4522463 : Blo 2009435 4522463 := bstep (se 1 (by rfl) ⟨3391847, by rfl⟩ : syracuseStep 4522463 = 6783695) B6783695
theorem B3014975 : Blo 2009435 3014975 := bstep (se 1 (by rfl) ⟨2261231, by rfl⟩ : syracuseStep 3014975 = 4522463) B4522463
theorem B2009983 : Blo 2009435 2009983 := bstep (se 1 (by rfl) ⟨1507487, by rfl⟩ : syracuseStep 2009983 = 3014975) B3014975
theorem B3014981 : Blo 2009435 3014981 := bbase (se 4 (by rfl) ⟨282654, by rfl⟩ : syracuseStep 3014981 = 565309) (by norm_num)
theorem B2009987 : Blo 2009435 2009987 := bstep (se 1 (by rfl) ⟨1507490, by rfl⟩ : syracuseStep 2009987 = 3014981) B3014981
theorem B3391861 : Blo 2009435 3391861 := bbase (se 5 (by rfl) ⟨158993, by rfl⟩ : syracuseStep 3391861 = 317987) (by norm_num)
theorem B4522481 : Blo 2009435 4522481 := bstep (se 2 (by rfl) ⟨1695930, by rfl⟩ : syracuseStep 4522481 = 3391861) B3391861
theorem B3014987 : Blo 2009435 3014987 := bstep (se 1 (by rfl) ⟨2261240, by rfl⟩ : syracuseStep 3014987 = 4522481) B4522481
theorem B2009991 : Blo 2009435 2009991 := bstep (se 1 (by rfl) ⟨1507493, by rfl⟩ : syracuseStep 2009991 = 3014987) B3014987
theorem B2261245 : Blo 2009435 2261245 := bbase (se 3 (by rfl) ⟨423983, by rfl⟩ : syracuseStep 2261245 = 847967) (by norm_num)
theorem B3014993 : Blo 2009435 3014993 := bstep (se 2 (by rfl) ⟨1130622, by rfl⟩ : syracuseStep 3014993 = 2261245) B2261245
theorem B2009995 : Blo 2009435 2009995 := bstep (se 1 (by rfl) ⟨1507496, by rfl⟩ : syracuseStep 2009995 = 3014993) B3014993
theorem B6783749 : Blo 2009435 6783749 := bbase (se 4 (by rfl) ⟨635976, by rfl⟩ : syracuseStep 6783749 = 1271953) (by norm_num)
theorem B4522499 : Blo 2009435 4522499 := bstep (se 1 (by rfl) ⟨3391874, by rfl⟩ : syracuseStep 4522499 = 6783749) B6783749
theorem B3014999 : Blo 2009435 3014999 := bstep (se 1 (by rfl) ⟨2261249, by rfl⟩ : syracuseStep 3014999 = 4522499) B4522499
theorem B2009999 : Blo 2009435 2009999 := bstep (se 1 (by rfl) ⟨1507499, by rfl⟩ : syracuseStep 2009999 = 3014999) B3014999
theorem B3015005 : Blo 2009435 3015005 := bbase (se 3 (by rfl) ⟨565313, by rfl⟩ : syracuseStep 3015005 = 1130627) (by norm_num)
theorem B2010003 : Blo 2009435 2010003 := bstep (se 1 (by rfl) ⟨1507502, by rfl⟩ : syracuseStep 2010003 = 3015005) B3015005
theorem B4522517 : Blo 2009435 4522517 := bbase (se 6 (by rfl) ⟨105996, by rfl⟩ : syracuseStep 4522517 = 211993) (by norm_num)
theorem B3015011 : Blo 2009435 3015011 := bstep (se 1 (by rfl) ⟨2261258, by rfl⟩ : syracuseStep 3015011 = 4522517) B4522517
theorem B2010007 : Blo 2009435 2010007 := bstep (se 1 (by rfl) ⟨1507505, by rfl⟩ : syracuseStep 2010007 = 3015011) B3015011
theorem B7631765 : Blo 2009435 7631765 := bbase (se 6 (by rfl) ⟨178869, by rfl⟩ : syracuseStep 7631765 = 357739) (by norm_num)
theorem B5087843 : Blo 2009435 5087843 := bstep (se 1 (by rfl) ⟨3815882, by rfl⟩ : syracuseStep 5087843 = 7631765) B7631765
theorem B3391895 : Blo 2009435 3391895 := bstep (se 1 (by rfl) ⟨2543921, by rfl⟩ : syracuseStep 3391895 = 5087843) B5087843
theorem B2261263 : Blo 2009435 2261263 := bstep (se 1 (by rfl) ⟨1695947, by rfl⟩ : syracuseStep 2261263 = 3391895) B3391895
theorem B3015017 : Blo 2009435 3015017 := bstep (se 2 (by rfl) ⟨1130631, by rfl⟩ : syracuseStep 3015017 = 2261263) B2261263
theorem B2010011 : Blo 2009435 2010011 := bstep (se 1 (by rfl) ⟨1507508, by rfl⟩ : syracuseStep 2010011 = 3015017) B3015017
theorem B11447669 : Blo 2009435 11447669 := bbase (se 5 (by rfl) ⟨536609, by rfl⟩ : syracuseStep 11447669 = 1073219) (by norm_num)
theorem B7631779 : Blo 2009435 7631779 := bstep (se 1 (by rfl) ⟨5723834, by rfl⟩ : syracuseStep 7631779 = 11447669) B11447669
theorem B10175705 : Blo 2009435 10175705 := bstep (se 2 (by rfl) ⟨3815889, by rfl⟩ : syracuseStep 10175705 = 7631779) B7631779
theorem B6783803 : Blo 2009435 6783803 := bstep (se 1 (by rfl) ⟨5087852, by rfl⟩ : syracuseStep 6783803 = 10175705) B10175705
theorem B4522535 : Blo 2009435 4522535 := bstep (se 1 (by rfl) ⟨3391901, by rfl⟩ : syracuseStep 4522535 = 6783803) B6783803
theorem B3015023 : Blo 2009435 3015023 := bstep (se 1 (by rfl) ⟨2261267, by rfl⟩ : syracuseStep 3015023 = 4522535) B4522535
theorem B2010015 : Blo 2009435 2010015 := bstep (se 1 (by rfl) ⟨1507511, by rfl⟩ : syracuseStep 2010015 = 3015023) B3015023
theorem B3015029 : Blo 2009435 3015029 := bbase (se 5 (by rfl) ⟨141329, by rfl⟩ : syracuseStep 3015029 = 282659) (by norm_num)
theorem B2010019 : Blo 2009435 2010019 := bstep (se 1 (by rfl) ⟨1507514, by rfl⟩ : syracuseStep 2010019 = 3015029) B3015029
theorem B7244261 : Blo 2009435 7244261 := bbase (se 4 (by rfl) ⟨679149, by rfl⟩ : syracuseStep 7244261 = 1358299) (by norm_num)
theorem B4829507 : Blo 2009435 4829507 := bstep (se 1 (by rfl) ⟨3622130, by rfl⟩ : syracuseStep 4829507 = 7244261) B7244261
theorem B3219671 : Blo 2009435 3219671 := bstep (se 1 (by rfl) ⟨2414753, by rfl⟩ : syracuseStep 3219671 = 4829507) B4829507
theorem B2146447 : Blo 2009435 2146447 := bstep (se 1 (by rfl) ⟨1609835, by rfl⟩ : syracuseStep 2146447 = 3219671) B3219671
theorem B2861929 : Blo 2009435 2861929 := bstep (se 2 (by rfl) ⟨1073223, by rfl⟩ : syracuseStep 2861929 = 2146447) B2146447
theorem B3815905 : Blo 2009435 3815905 := bstep (se 2 (by rfl) ⟨1430964, by rfl⟩ : syracuseStep 3815905 = 2861929) B2861929
theorem B5087873 : Blo 2009435 5087873 := bstep (se 2 (by rfl) ⟨1907952, by rfl⟩ : syracuseStep 5087873 = 3815905) B3815905
theorem B3391915 : Blo 2009435 3391915 := bstep (se 1 (by rfl) ⟨2543936, by rfl⟩ : syracuseStep 3391915 = 5087873) B5087873
theorem B4522553 : Blo 2009435 4522553 := bstep (se 2 (by rfl) ⟨1695957, by rfl⟩ : syracuseStep 4522553 = 3391915) B3391915
theorem B3015035 : Blo 2009435 3015035 := bstep (se 1 (by rfl) ⟨2261276, by rfl⟩ : syracuseStep 3015035 = 4522553) B4522553
theorem B2010023 : Blo 2009435 2010023 := bstep (se 1 (by rfl) ⟨1507517, by rfl⟩ : syracuseStep 2010023 = 3015035) B3015035
theorem B2261281 : Blo 2009435 2261281 := bbase (se 2 (by rfl) ⟨847980, by rfl⟩ : syracuseStep 2261281 = 1695961) (by norm_num)
theorem B3015041 : Blo 2009435 3015041 := bstep (se 2 (by rfl) ⟨1130640, by rfl⟩ : syracuseStep 3015041 = 2261281) B2261281
theorem B2010027 : Blo 2009435 2010027 := bstep (se 1 (by rfl) ⟨1507520, by rfl⟩ : syracuseStep 2010027 = 3015041) B3015041
theorem B5087893 : Blo 2009435 5087893 := bbase (se 6 (by rfl) ⟨119247, by rfl⟩ : syracuseStep 5087893 = 238495) (by norm_num)
theorem B6783857 : Blo 2009435 6783857 := bstep (se 2 (by rfl) ⟨2543946, by rfl⟩ : syracuseStep 6783857 = 5087893) B5087893
theorem B4522571 : Blo 2009435 4522571 := bstep (se 1 (by rfl) ⟨3391928, by rfl⟩ : syracuseStep 4522571 = 6783857) B6783857
theorem B3015047 : Blo 2009435 3015047 := bstep (se 1 (by rfl) ⟨2261285, by rfl⟩ : syracuseStep 3015047 = 4522571) B4522571
theorem B2010031 : Blo 2009435 2010031 := bstep (se 1 (by rfl) ⟨1507523, by rfl⟩ : syracuseStep 2010031 = 3015047) B3015047
theorem B3015053 : Blo 2009435 3015053 := bbase (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) (by norm_num)
theorem B2010035 : Blo 2009435 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B4522589 : Blo 2009435 4522589 := bbase (se 3 (by rfl) ⟨847985, by rfl⟩ : syracuseStep 4522589 = 1695971) (by norm_num)
theorem B3015059 : Blo 2009435 3015059 := bstep (se 1 (by rfl) ⟨2261294, by rfl⟩ : syracuseStep 3015059 = 4522589) B4522589
theorem B2010039 : Blo 2009435 2010039 := bstep (se 1 (by rfl) ⟨1507529, by rfl⟩ : syracuseStep 2010039 = 3015059) B3015059
theorem B3391949 : Blo 2009435 3391949 := bbase (se 3 (by rfl) ⟨635990, by rfl⟩ : syracuseStep 3391949 = 1271981) (by norm_num)
theorem B2261299 : Blo 2009435 2261299 := bstep (se 1 (by rfl) ⟨1695974, by rfl⟩ : syracuseStep 2261299 = 3391949) B3391949
theorem B3015065 : Blo 2009435 3015065 := bstep (se 2 (by rfl) ⟨1130649, by rfl⟩ : syracuseStep 3015065 = 2261299) B2261299
theorem B2010043 : Blo 2009435 2010043 := bstep (se 1 (by rfl) ⟨1507532, by rfl⟩ : syracuseStep 2010043 = 3015065) B3015065
theorem B9659125 : Blo 2009435 9659125 := bbase (se 5 (by rfl) ⟨452771, by rfl⟩ : syracuseStep 9659125 = 905543) (by norm_num)
theorem B12878833 : Blo 2009435 12878833 := bstep (se 2 (by rfl) ⟨4829562, by rfl⟩ : syracuseStep 12878833 = 9659125) B9659125
theorem B17171777 : Blo 2009435 17171777 := bstep (se 2 (by rfl) ⟨6439416, by rfl⟩ : syracuseStep 17171777 = 12878833) B12878833
theorem B11447851 : Blo 2009435 11447851 := bstep (se 1 (by rfl) ⟨8585888, by rfl⟩ : syracuseStep 11447851 = 17171777) B17171777
theorem B15263801 : Blo 2009435 15263801 := bstep (se 2 (by rfl) ⟨5723925, by rfl⟩ : syracuseStep 15263801 = 11447851) B11447851
theorem B10175867 : Blo 2009435 10175867 := bstep (se 1 (by rfl) ⟨7631900, by rfl⟩ : syracuseStep 10175867 = 15263801) B15263801
theorem B6783911 : Blo 2009435 6783911 := bstep (se 1 (by rfl) ⟨5087933, by rfl⟩ : syracuseStep 6783911 = 10175867) B10175867
theorem B4522607 : Blo 2009435 4522607 := bstep (se 1 (by rfl) ⟨3391955, by rfl⟩ : syracuseStep 4522607 = 6783911) B6783911
theorem B3015071 : Blo 2009435 3015071 := bstep (se 1 (by rfl) ⟨2261303, by rfl⟩ : syracuseStep 3015071 = 4522607) B4522607
theorem B2010047 : Blo 2009435 2010047 := bstep (se 1 (by rfl) ⟨1507535, by rfl⟩ : syracuseStep 2010047 = 3015071) B3015071
theorem B3015077 : Blo 2009435 3015077 := bbase (se 4 (by rfl) ⟨282663, by rfl⟩ : syracuseStep 3015077 = 565327) (by norm_num)
theorem B2010051 : Blo 2009435 2010051 := bstep (se 1 (by rfl) ⟨1507538, by rfl⟩ : syracuseStep 2010051 = 3015077) B3015077
theorem B2543977 : Blo 2009435 2543977 := bbase (se 2 (by rfl) ⟨953991, by rfl⟩ : syracuseStep 2543977 = 1907983) (by norm_num)
theorem B3391969 : Blo 2009435 3391969 := bstep (se 2 (by rfl) ⟨1271988, by rfl⟩ : syracuseStep 3391969 = 2543977) B2543977
theorem B4522625 : Blo 2009435 4522625 := bstep (se 2 (by rfl) ⟨1695984, by rfl⟩ : syracuseStep 4522625 = 3391969) B3391969
theorem B3015083 : Blo 2009435 3015083 := bstep (se 1 (by rfl) ⟨2261312, by rfl⟩ : syracuseStep 3015083 = 4522625) B4522625
theorem B2010055 : Blo 2009435 2010055 := bstep (se 1 (by rfl) ⟨1507541, by rfl⟩ : syracuseStep 2010055 = 3015083) B3015083
theorem B2261317 : Blo 2009435 2261317 := bbase (se 4 (by rfl) ⟨211998, by rfl⟩ : syracuseStep 2261317 = 423997) (by norm_num)
theorem B3015089 : Blo 2009435 3015089 := bstep (se 2 (by rfl) ⟨1130658, by rfl⟩ : syracuseStep 3015089 = 2261317) B2261317
theorem B2010059 : Blo 2009435 2010059 := bstep (se 1 (by rfl) ⟨1507544, by rfl⟩ : syracuseStep 2010059 = 3015089) B3015089
theorem B3815981 : Blo 2009435 3815981 := bbase (se 3 (by rfl) ⟨715496, by rfl⟩ : syracuseStep 3815981 = 1430993) (by norm_num)
theorem B2543987 : Blo 2009435 2543987 := bstep (se 1 (by rfl) ⟨1907990, by rfl⟩ : syracuseStep 2543987 = 3815981) B3815981
theorem B6783965 : Blo 2009435 6783965 := bstep (se 3 (by rfl) ⟨1271993, by rfl⟩ : syracuseStep 6783965 = 2543987) B2543987
theorem B4522643 : Blo 2009435 4522643 := bstep (se 1 (by rfl) ⟨3391982, by rfl⟩ : syracuseStep 4522643 = 6783965) B6783965
theorem B3015095 : Blo 2009435 3015095 := bstep (se 1 (by rfl) ⟨2261321, by rfl⟩ : syracuseStep 3015095 = 4522643) B4522643
theorem B2010063 : Blo 2009435 2010063 := bstep (se 1 (by rfl) ⟨1507547, by rfl⟩ : syracuseStep 2010063 = 3015095) B3015095
theorem B3015101 : Blo 2009435 3015101 := bbase (se 3 (by rfl) ⟨565331, by rfl⟩ : syracuseStep 3015101 = 1130663) (by norm_num)
theorem B2010067 : Blo 2009435 2010067 := bstep (se 1 (by rfl) ⟨1507550, by rfl⟩ : syracuseStep 2010067 = 3015101) B3015101
theorem B4522661 : Blo 2009435 4522661 := bbase (se 4 (by rfl) ⟨423999, by rfl⟩ : syracuseStep 4522661 = 847999) (by norm_num)
theorem B3015107 : Blo 2009435 3015107 := bstep (se 1 (by rfl) ⟨2261330, by rfl⟩ : syracuseStep 3015107 = 4522661) B4522661
theorem B2010071 : Blo 2009435 2010071 := bstep (se 1 (by rfl) ⟨1507553, by rfl⟩ : syracuseStep 2010071 = 3015107) B3015107
theorem B5088005 : Blo 2009435 5088005 := bbase (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) (by norm_num)
theorem B3392003 : Blo 2009435 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B2261335 : Blo 2009435 2261335 := bstep (se 1 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 2261335 = 3392003) B3392003
theorem B3015113 : Blo 2009435 3015113 := bstep (se 2 (by rfl) ⟨1130667, by rfl⟩ : syracuseStep 3015113 = 2261335) B2261335
theorem B2010075 : Blo 2009435 2010075 := bstep (se 1 (by rfl) ⟨1507556, by rfl⟩ : syracuseStep 2010075 = 3015113) B3015113
theorem B4293013 : Blo 2009435 4293013 := bbase (se 6 (by rfl) ⟨100617, by rfl⟩ : syracuseStep 4293013 = 201235) (by norm_num)
theorem B5724017 : Blo 2009435 5724017 := bstep (se 2 (by rfl) ⟨2146506, by rfl⟩ : syracuseStep 5724017 = 4293013) B4293013
theorem B3816011 : Blo 2009435 3816011 := bstep (se 1 (by rfl) ⟨2862008, by rfl⟩ : syracuseStep 3816011 = 5724017) B5724017
theorem B10176029 : Blo 2009435 10176029 := bstep (se 3 (by rfl) ⟨1908005, by rfl⟩ : syracuseStep 10176029 = 3816011) B3816011
theorem B6784019 : Blo 2009435 6784019 := bstep (se 1 (by rfl) ⟨5088014, by rfl⟩ : syracuseStep 6784019 = 10176029) B10176029
theorem B4522679 : Blo 2009435 4522679 := bstep (se 1 (by rfl) ⟨3392009, by rfl⟩ : syracuseStep 4522679 = 6784019) B6784019
theorem B3015119 : Blo 2009435 3015119 := bstep (se 1 (by rfl) ⟨2261339, by rfl⟩ : syracuseStep 3015119 = 4522679) B4522679
theorem B2010079 : Blo 2009435 2010079 := bstep (se 1 (by rfl) ⟨1507559, by rfl⟩ : syracuseStep 2010079 = 3015119) B3015119
theorem B3015125 : Blo 2009435 3015125 := bbase (se 7 (by rfl) ⟨35333, by rfl⟩ : syracuseStep 3015125 = 70667) (by norm_num)
theorem B2010083 : Blo 2009435 2010083 := bstep (se 1 (by rfl) ⟨1507562, by rfl⟩ : syracuseStep 2010083 = 3015125) B3015125
theorem B7632053 : Blo 2009435 7632053 := bbase (se 5 (by rfl) ⟨357752, by rfl⟩ : syracuseStep 7632053 = 715505) (by norm_num)
theorem B5088035 : Blo 2009435 5088035 := bstep (se 1 (by rfl) ⟨3816026, by rfl⟩ : syracuseStep 5088035 = 7632053) B7632053
theorem B3392023 : Blo 2009435 3392023 := bstep (se 1 (by rfl) ⟨2544017, by rfl⟩ : syracuseStep 3392023 = 5088035) B5088035
theorem B4522697 : Blo 2009435 4522697 := bstep (se 2 (by rfl) ⟨1696011, by rfl⟩ : syracuseStep 4522697 = 3392023) B3392023
theorem B3015131 : Blo 2009435 3015131 := bstep (se 1 (by rfl) ⟨2261348, by rfl⟩ : syracuseStep 3015131 = 4522697) B4522697
theorem B2010087 : Blo 2009435 2010087 := bstep (se 1 (by rfl) ⟨1507565, by rfl⟩ : syracuseStep 2010087 = 3015131) B3015131
theorem B2261353 : Blo 2009435 2261353 := bbase (se 2 (by rfl) ⟨848007, by rfl⟩ : syracuseStep 2261353 = 1696015) (by norm_num)
theorem B3015137 : Blo 2009435 3015137 := bstep (se 2 (by rfl) ⟨1130676, by rfl⟩ : syracuseStep 3015137 = 2261353) B2261353
theorem B2010091 : Blo 2009435 2010091 := bstep (se 1 (by rfl) ⟨1507568, by rfl⟩ : syracuseStep 2010091 = 3015137) B3015137
theorem B2037521 : Blo 2009435 2037521 := bbase (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) (by norm_num)
theorem B5433389 : Blo 2009435 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B3622259 : Blo 2009435 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B9659357 : Blo 2009435 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B6439571 : Blo 2009435 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B4293047 : Blo 2009435 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B11448125 : Blo 2009435 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B7632083 : Blo 2009435 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B5088055 : Blo 2009435 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B6784073 : Blo 2009435 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B4522715 : Blo 2009435 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B3015143 : Blo 2009435 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B2010095 : Blo 2009435 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B3015149 : Blo 2009435 3015149 := bbase (se 3 (by rfl) ⟨565340, by rfl⟩ : syracuseStep 3015149 = 1130681) (by norm_num)
theorem B2010099 : Blo 2009435 2010099 := bstep (se 1 (by rfl) ⟨1507574, by rfl⟩ : syracuseStep 2010099 = 3015149) B3015149
theorem B4522733 : Blo 2009435 4522733 := bbase (se 3 (by rfl) ⟨848012, by rfl⟩ : syracuseStep 4522733 = 1696025) (by norm_num)
theorem B3015155 : Blo 2009435 3015155 := bstep (se 1 (by rfl) ⟨2261366, by rfl⟩ : syracuseStep 3015155 = 4522733) B4522733
theorem B2010103 : Blo 2009435 2010103 := bstep (se 1 (by rfl) ⟨1507577, by rfl⟩ : syracuseStep 2010103 = 3015155) B3015155
theorem B2146537 : Blo 2009435 2146537 := bbase (se 2 (by rfl) ⟨804951, by rfl⟩ : syracuseStep 2146537 = 1609903) (by norm_num)
theorem B2862049 : Blo 2009435 2862049 := bstep (se 2 (by rfl) ⟨1073268, by rfl⟩ : syracuseStep 2862049 = 2146537) B2146537
theorem B3816065 : Blo 2009435 3816065 := bstep (se 2 (by rfl) ⟨1431024, by rfl⟩ : syracuseStep 3816065 = 2862049) B2862049
theorem B2544043 : Blo 2009435 2544043 := bstep (se 1 (by rfl) ⟨1908032, by rfl⟩ : syracuseStep 2544043 = 3816065) B3816065
theorem B3392057 : Blo 2009435 3392057 := bstep (se 2 (by rfl) ⟨1272021, by rfl⟩ : syracuseStep 3392057 = 2544043) B2544043
theorem B2261371 : Blo 2009435 2261371 := bstep (se 1 (by rfl) ⟨1696028, by rfl⟩ : syracuseStep 2261371 = 3392057) B3392057
theorem B3015161 : Blo 2009435 3015161 := bstep (se 2 (by rfl) ⟨1130685, by rfl⟩ : syracuseStep 3015161 = 2261371) B2261371
theorem B2010107 : Blo 2009435 2010107 := bstep (se 1 (by rfl) ⟨1507580, by rfl⟩ : syracuseStep 2010107 = 3015161) B3015161
theorem B2292229 : Blo 2009435 2292229 := bbase (se 4 (by rfl) ⟨214896, by rfl⟩ : syracuseStep 2292229 = 429793) (by norm_num)
theorem B3056305 : Blo 2009435 3056305 := bstep (se 2 (by rfl) ⟨1146114, by rfl⟩ : syracuseStep 3056305 = 2292229) B2292229
theorem B4075073 : Blo 2009435 4075073 := bstep (se 2 (by rfl) ⟨1528152, by rfl⟩ : syracuseStep 4075073 = 3056305) B3056305
theorem B43467445 : Blo 2009435 43467445 := bstep (se 5 (by rfl) ⟨2037536, by rfl⟩ : syracuseStep 43467445 = 4075073) B4075073
theorem B57956593 : Blo 2009435 57956593 := bstep (se 2 (by rfl) ⟨21733722, by rfl⟩ : syracuseStep 57956593 = 43467445) B43467445
theorem B77275457 : Blo 2009435 77275457 := bstep (se 2 (by rfl) ⟨28978296, by rfl⟩ : syracuseStep 77275457 = 57956593) B57956593
theorem B51516971 : Blo 2009435 51516971 := bstep (se 1 (by rfl) ⟨38637728, by rfl⟩ : syracuseStep 51516971 = 77275457) B77275457
theorem B34344647 : Blo 2009435 34344647 := bstep (se 1 (by rfl) ⟨25758485, by rfl⟩ : syracuseStep 34344647 = 51516971) B51516971
theorem B22896431 : Blo 2009435 22896431 := bstep (se 1 (by rfl) ⟨17172323, by rfl⟩ : syracuseStep 22896431 = 34344647) B34344647
theorem B15264287 : Blo 2009435 15264287 := bstep (se 1 (by rfl) ⟨11448215, by rfl⟩ : syracuseStep 15264287 = 22896431) B22896431
theorem B10176191 : Blo 2009435 10176191 := bstep (se 1 (by rfl) ⟨7632143, by rfl⟩ : syracuseStep 10176191 = 15264287) B15264287
theorem B6784127 : Blo 2009435 6784127 := bstep (se 1 (by rfl) ⟨5088095, by rfl⟩ : syracuseStep 6784127 = 10176191) B10176191
theorem B4522751 : Blo 2009435 4522751 := bstep (se 1 (by rfl) ⟨3392063, by rfl⟩ : syracuseStep 4522751 = 6784127) B6784127
theorem B3015167 : Blo 2009435 3015167 := bstep (se 1 (by rfl) ⟨2261375, by rfl⟩ : syracuseStep 3015167 = 4522751) B4522751
theorem B2010111 : Blo 2009435 2010111 := bstep (se 1 (by rfl) ⟨1507583, by rfl⟩ : syracuseStep 2010111 = 3015167) B3015167
theorem B3015173 : Blo 2009435 3015173 := bbase (se 4 (by rfl) ⟨282672, by rfl⟩ : syracuseStep 3015173 = 565345) (by norm_num)
theorem B2010115 : Blo 2009435 2010115 := bstep (se 1 (by rfl) ⟨1507586, by rfl⟩ : syracuseStep 2010115 = 3015173) B3015173
theorem B3392077 : Blo 2009435 3392077 := bbase (se 3 (by rfl) ⟨636014, by rfl⟩ : syracuseStep 3392077 = 1272029) (by norm_num)
theorem B4522769 : Blo 2009435 4522769 := bstep (se 2 (by rfl) ⟨1696038, by rfl⟩ : syracuseStep 4522769 = 3392077) B3392077
theorem B3015179 : Blo 2009435 3015179 := bstep (se 1 (by rfl) ⟨2261384, by rfl⟩ : syracuseStep 3015179 = 4522769) B4522769
theorem B2010119 : Blo 2009435 2010119 := bstep (se 1 (by rfl) ⟨1507589, by rfl⟩ : syracuseStep 2010119 = 3015179) B3015179
theorem B2261389 : Blo 2009435 2261389 := bbase (se 3 (by rfl) ⟨424010, by rfl⟩ : syracuseStep 2261389 = 848021) (by norm_num)
theorem B3015185 : Blo 2009435 3015185 := bstep (se 2 (by rfl) ⟨1130694, by rfl⟩ : syracuseStep 3015185 = 2261389) B2261389
theorem B2010123 : Blo 2009435 2010123 := bstep (se 1 (by rfl) ⟨1507592, by rfl⟩ : syracuseStep 2010123 = 3015185) B3015185
theorem B6784181 : Blo 2009435 6784181 := bbase (se 5 (by rfl) ⟨318008, by rfl⟩ : syracuseStep 6784181 = 636017) (by norm_num)
theorem B4522787 : Blo 2009435 4522787 := bstep (se 1 (by rfl) ⟨3392090, by rfl⟩ : syracuseStep 4522787 = 6784181) B6784181
theorem B3015191 : Blo 2009435 3015191 := bstep (se 1 (by rfl) ⟨2261393, by rfl⟩ : syracuseStep 3015191 = 4522787) B4522787
theorem B2010127 : Blo 2009435 2010127 := bstep (se 1 (by rfl) ⟨1507595, by rfl⟩ : syracuseStep 2010127 = 3015191) B3015191
theorem B3015197 : Blo 2009435 3015197 := bbase (se 3 (by rfl) ⟨565349, by rfl⟩ : syracuseStep 3015197 = 1130699) (by norm_num)
theorem B2010131 : Blo 2009435 2010131 := bstep (se 1 (by rfl) ⟨1507598, by rfl⟩ : syracuseStep 2010131 = 3015197) B3015197
theorem B4522805 : Blo 2009435 4522805 := bbase (se 5 (by rfl) ⟨212006, by rfl⟩ : syracuseStep 4522805 = 424013) (by norm_num)
theorem B3015203 : Blo 2009435 3015203 := bstep (se 1 (by rfl) ⟨2261402, by rfl⟩ : syracuseStep 3015203 = 4522805) B4522805
theorem B2010135 : Blo 2009435 2010135 := bstep (se 1 (by rfl) ⟨1507601, by rfl⟩ : syracuseStep 2010135 = 3015203) B3015203
theorem B7244677 : Blo 2009435 7244677 := bbase (se 4 (by rfl) ⟨679188, by rfl⟩ : syracuseStep 7244677 = 1358377) (by norm_num)
theorem B9659569 : Blo 2009435 9659569 := bstep (se 2 (by rfl) ⟨3622338, by rfl⟩ : syracuseStep 9659569 = 7244677) B7244677
theorem B12879425 : Blo 2009435 12879425 := bstep (se 2 (by rfl) ⟨4829784, by rfl⟩ : syracuseStep 12879425 = 9659569) B9659569
theorem B8586283 : Blo 2009435 8586283 := bstep (se 1 (by rfl) ⟨6439712, by rfl⟩ : syracuseStep 8586283 = 12879425) B12879425
theorem B11448377 : Blo 2009435 11448377 := bstep (se 2 (by rfl) ⟨4293141, by rfl⟩ : syracuseStep 11448377 = 8586283) B8586283
theorem B7632251 : Blo 2009435 7632251 := bstep (se 1 (by rfl) ⟨5724188, by rfl⟩ : syracuseStep 7632251 = 11448377) B11448377
theorem B5088167 : Blo 2009435 5088167 := bstep (se 1 (by rfl) ⟨3816125, by rfl⟩ : syracuseStep 5088167 = 7632251) B7632251
theorem B3392111 : Blo 2009435 3392111 := bstep (se 1 (by rfl) ⟨2544083, by rfl⟩ : syracuseStep 3392111 = 5088167) B5088167
theorem B2261407 : Blo 2009435 2261407 := bstep (se 1 (by rfl) ⟨1696055, by rfl⟩ : syracuseStep 2261407 = 3392111) B3392111
theorem B3015209 : Blo 2009435 3015209 := bstep (se 2 (by rfl) ⟨1130703, by rfl⟩ : syracuseStep 3015209 = 2261407) B2261407
theorem B2010139 : Blo 2009435 2010139 := bstep (se 1 (by rfl) ⟨1507604, by rfl⟩ : syracuseStep 2010139 = 3015209) B3015209
theorem B6112709 : Blo 2009435 6112709 := bbase (se 4 (by rfl) ⟨573066, by rfl⟩ : syracuseStep 6112709 = 1146133) (by norm_num)
theorem B4075139 : Blo 2009435 4075139 := bstep (se 1 (by rfl) ⟨3056354, by rfl⟩ : syracuseStep 4075139 = 6112709) B6112709
theorem B2716759 : Blo 2009435 2716759 := bstep (se 1 (by rfl) ⟨2037569, by rfl⟩ : syracuseStep 2716759 = 4075139) B4075139
theorem B14489381 : Blo 2009435 14489381 := bstep (se 4 (by rfl) ⟨1358379, by rfl⟩ : syracuseStep 14489381 = 2716759) B2716759
theorem B9659587 : Blo 2009435 9659587 := bstep (se 1 (by rfl) ⟨7244690, by rfl⟩ : syracuseStep 9659587 = 14489381) B14489381
theorem B12879449 : Blo 2009435 12879449 := bstep (se 2 (by rfl) ⟨4829793, by rfl⟩ : syracuseStep 12879449 = 9659587) B9659587
theorem B8586299 : Blo 2009435 8586299 := bstep (se 1 (by rfl) ⟨6439724, by rfl⟩ : syracuseStep 8586299 = 12879449) B12879449
theorem B5724199 : Blo 2009435 5724199 := bstep (se 1 (by rfl) ⟨4293149, by rfl⟩ : syracuseStep 5724199 = 8586299) B8586299
theorem B7632265 : Blo 2009435 7632265 := bstep (se 2 (by rfl) ⟨2862099, by rfl⟩ : syracuseStep 7632265 = 5724199) B5724199
theorem B10176353 : Blo 2009435 10176353 := bstep (se 2 (by rfl) ⟨3816132, by rfl⟩ : syracuseStep 10176353 = 7632265) B7632265
theorem B6784235 : Blo 2009435 6784235 := bstep (se 1 (by rfl) ⟨5088176, by rfl⟩ : syracuseStep 6784235 = 10176353) B10176353
theorem B4522823 : Blo 2009435 4522823 := bstep (se 1 (by rfl) ⟨3392117, by rfl⟩ : syracuseStep 4522823 = 6784235) B6784235
theorem B3015215 : Blo 2009435 3015215 := bstep (se 1 (by rfl) ⟨2261411, by rfl⟩ : syracuseStep 3015215 = 4522823) B4522823
theorem B2010143 : Blo 2009435 2010143 := bstep (se 1 (by rfl) ⟨1507607, by rfl⟩ : syracuseStep 2010143 = 3015215) B3015215
theorem B3015221 : Blo 2009435 3015221 := bbase (se 5 (by rfl) ⟨141338, by rfl⟩ : syracuseStep 3015221 = 282677) (by norm_num)
theorem B2010147 : Blo 2009435 2010147 := bstep (se 1 (by rfl) ⟨1507610, by rfl⟩ : syracuseStep 2010147 = 3015221) B3015221
theorem B5088197 : Blo 2009435 5088197 := bbase (se 4 (by rfl) ⟨477018, by rfl⟩ : syracuseStep 5088197 = 954037) (by norm_num)
theorem B3392131 : Blo 2009435 3392131 := bstep (se 1 (by rfl) ⟨2544098, by rfl⟩ : syracuseStep 3392131 = 5088197) B5088197
theorem B4522841 : Blo 2009435 4522841 := bstep (se 2 (by rfl) ⟨1696065, by rfl⟩ : syracuseStep 4522841 = 3392131) B3392131
theorem B3015227 : Blo 2009435 3015227 := bstep (se 1 (by rfl) ⟨2261420, by rfl⟩ : syracuseStep 3015227 = 4522841) B4522841
theorem B2010151 : Blo 2009435 2010151 := bstep (se 1 (by rfl) ⟨1507613, by rfl⟩ : syracuseStep 2010151 = 3015227) B3015227
theorem B2261425 : Blo 2009435 2261425 := bbase (se 2 (by rfl) ⟨848034, by rfl⟩ : syracuseStep 2261425 = 1696069) (by norm_num)
theorem B3015233 : Blo 2009435 3015233 := bstep (se 2 (by rfl) ⟨1130712, by rfl⟩ : syracuseStep 3015233 = 2261425) B2261425
theorem B2010155 : Blo 2009435 2010155 := bstep (se 1 (by rfl) ⟨1507616, by rfl⟩ : syracuseStep 2010155 = 3015233) B3015233
theorem B5724245 : Blo 2009435 5724245 := bbase (se 8 (by rfl) ⟨33540, by rfl⟩ : syracuseStep 5724245 = 67081) (by norm_num)
theorem B3816163 : Blo 2009435 3816163 := bstep (se 1 (by rfl) ⟨2862122, by rfl⟩ : syracuseStep 3816163 = 5724245) B5724245
theorem B5088217 : Blo 2009435 5088217 := bstep (se 2 (by rfl) ⟨1908081, by rfl⟩ : syracuseStep 5088217 = 3816163) B3816163
theorem B6784289 : Blo 2009435 6784289 := bstep (se 2 (by rfl) ⟨2544108, by rfl⟩ : syracuseStep 6784289 = 5088217) B5088217
theorem B4522859 : Blo 2009435 4522859 := bstep (se 1 (by rfl) ⟨3392144, by rfl⟩ : syracuseStep 4522859 = 6784289) B6784289
theorem B3015239 : Blo 2009435 3015239 := bstep (se 1 (by rfl) ⟨2261429, by rfl⟩ : syracuseStep 3015239 = 4522859) B4522859
theorem B2010159 : Blo 2009435 2010159 := bstep (se 1 (by rfl) ⟨1507619, by rfl⟩ : syracuseStep 2010159 = 3015239) B3015239
theorem B3015245 : Blo 2009435 3015245 := bbase (se 3 (by rfl) ⟨565358, by rfl⟩ : syracuseStep 3015245 = 1130717) (by norm_num)
theorem B2010163 : Blo 2009435 2010163 := bstep (se 1 (by rfl) ⟨1507622, by rfl⟩ : syracuseStep 2010163 = 3015245) B3015245
theorem B4522877 : Blo 2009435 4522877 := bbase (se 3 (by rfl) ⟨848039, by rfl⟩ : syracuseStep 4522877 = 1696079) (by norm_num)
theorem B3015251 : Blo 2009435 3015251 := bstep (se 1 (by rfl) ⟨2261438, by rfl⟩ : syracuseStep 3015251 = 4522877) B4522877
theorem B2010167 : Blo 2009435 2010167 := bstep (se 1 (by rfl) ⟨1507625, by rfl⟩ : syracuseStep 2010167 = 3015251) B3015251
theorem B3392165 : Blo 2009435 3392165 := bbase (se 4 (by rfl) ⟨318015, by rfl⟩ : syracuseStep 3392165 = 636031) (by norm_num)
theorem B2261443 : Blo 2009435 2261443 := bstep (se 1 (by rfl) ⟨1696082, by rfl⟩ : syracuseStep 2261443 = 3392165) B3392165
theorem B3015257 : Blo 2009435 3015257 := bstep (se 2 (by rfl) ⟨1130721, by rfl⟩ : syracuseStep 3015257 = 2261443) B2261443
theorem B2010171 : Blo 2009435 2010171 := bstep (se 1 (by rfl) ⟨1507628, by rfl⟩ : syracuseStep 2010171 = 3015257) B3015257
theorem B2146609 : Blo 2009435 2146609 := bbase (se 2 (by rfl) ⟨804978, by rfl⟩ : syracuseStep 2146609 = 1609957) (by norm_num)
theorem B2862145 : Blo 2009435 2862145 := bstep (se 2 (by rfl) ⟨1073304, by rfl⟩ : syracuseStep 2862145 = 2146609) B2146609
theorem B15264773 : Blo 2009435 15264773 := bstep (se 4 (by rfl) ⟨1431072, by rfl⟩ : syracuseStep 15264773 = 2862145) B2862145
theorem B10176515 : Blo 2009435 10176515 := bstep (se 1 (by rfl) ⟨7632386, by rfl⟩ : syracuseStep 10176515 = 15264773) B15264773
theorem B6784343 : Blo 2009435 6784343 := bstep (se 1 (by rfl) ⟨5088257, by rfl⟩ : syracuseStep 6784343 = 10176515) B10176515
theorem B4522895 : Blo 2009435 4522895 := bstep (se 1 (by rfl) ⟨3392171, by rfl⟩ : syracuseStep 4522895 = 6784343) B6784343
theorem B3015263 : Blo 2009435 3015263 := bstep (se 1 (by rfl) ⟨2261447, by rfl⟩ : syracuseStep 3015263 = 4522895) B4522895
theorem B2010175 : Blo 2009435 2010175 := bstep (se 1 (by rfl) ⟨1507631, by rfl⟩ : syracuseStep 2010175 = 3015263) B3015263
theorem B3015269 : Blo 2009435 3015269 := bbase (se 4 (by rfl) ⟨282681, by rfl⟩ : syracuseStep 3015269 = 565363) (by norm_num)
theorem B2010179 : Blo 2009435 2010179 := bstep (se 1 (by rfl) ⟨1507634, by rfl⟩ : syracuseStep 2010179 = 3015269) B3015269
theorem B2862157 : Blo 2009435 2862157 := bbase (se 3 (by rfl) ⟨536654, by rfl⟩ : syracuseStep 2862157 = 1073309) (by norm_num)
theorem B3816209 : Blo 2009435 3816209 := bstep (se 2 (by rfl) ⟨1431078, by rfl⟩ : syracuseStep 3816209 = 2862157) B2862157
theorem B2544139 : Blo 2009435 2544139 := bstep (se 1 (by rfl) ⟨1908104, by rfl⟩ : syracuseStep 2544139 = 3816209) B3816209
theorem B3392185 : Blo 2009435 3392185 := bstep (se 2 (by rfl) ⟨1272069, by rfl⟩ : syracuseStep 3392185 = 2544139) B2544139
theorem B4522913 : Blo 2009435 4522913 := bstep (se 2 (by rfl) ⟨1696092, by rfl⟩ : syracuseStep 4522913 = 3392185) B3392185
theorem B3015275 : Blo 2009435 3015275 := bstep (se 1 (by rfl) ⟨2261456, by rfl⟩ : syracuseStep 3015275 = 4522913) B4522913
theorem B2010183 : Blo 2009435 2010183 := bstep (se 1 (by rfl) ⟨1507637, by rfl⟩ : syracuseStep 2010183 = 3015275) B3015275
theorem B2261461 : Blo 2009435 2261461 := bbase (se 7 (by rfl) ⟨26501, by rfl⟩ : syracuseStep 2261461 = 53003) (by norm_num)
theorem B3015281 : Blo 2009435 3015281 := bstep (se 2 (by rfl) ⟨1130730, by rfl⟩ : syracuseStep 3015281 = 2261461) B2261461
theorem B2010187 : Blo 2009435 2010187 := bstep (se 1 (by rfl) ⟨1507640, by rfl⟩ : syracuseStep 2010187 = 3015281) B3015281
theorem B2544149 : Blo 2009435 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B6784397 : Blo 2009435 6784397 := bstep (se 3 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 6784397 = 2544149) B2544149
theorem B4522931 : Blo 2009435 4522931 := bstep (se 1 (by rfl) ⟨3392198, by rfl⟩ : syracuseStep 4522931 = 6784397) B6784397
theorem B3015287 : Blo 2009435 3015287 := bstep (se 1 (by rfl) ⟨2261465, by rfl⟩ : syracuseStep 3015287 = 4522931) B4522931
theorem B2010191 : Blo 2009435 2010191 := bstep (se 1 (by rfl) ⟨1507643, by rfl⟩ : syracuseStep 2010191 = 3015287) B3015287
theorem B3015293 : Blo 2009435 3015293 := bbase (se 3 (by rfl) ⟨565367, by rfl⟩ : syracuseStep 3015293 = 1130735) (by norm_num)
theorem B2010195 : Blo 2009435 2010195 := bstep (se 1 (by rfl) ⟨1507646, by rfl⟩ : syracuseStep 2010195 = 3015293) B3015293
theorem B4522949 : Blo 2009435 4522949 := bbase (se 4 (by rfl) ⟨424026, by rfl⟩ : syracuseStep 4522949 = 848053) (by norm_num)
theorem B3015299 : Blo 2009435 3015299 := bstep (se 1 (by rfl) ⟨2261474, by rfl⟩ : syracuseStep 3015299 = 4522949) B4522949
theorem B2010199 : Blo 2009435 2010199 := bstep (se 1 (by rfl) ⟨1507649, by rfl⟩ : syracuseStep 2010199 = 3015299) B3015299
theorem B4962637 : Blo 2009435 4962637 := bbase (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) (by norm_num)
theorem B6616849 : Blo 2009435 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B8822465 : Blo 2009435 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B5881643 : Blo 2009435 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3921095 : Blo 2009435 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B10456253 : Blo 2009435 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B6970835 : Blo 2009435 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4647223 : Blo 2009435 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B24785189 : Blo 2009435 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B16523459 : Blo 2009435 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B11015639 : Blo 2009435 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B7343759 : Blo 2009435 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B4895839 : Blo 2009435 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B6527785 : Blo 2009435 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B8703713 : Blo 2009435 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B23209901 : Blo 2009435 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B15473267 : Blo 2009435 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B10315511 : Blo 2009435 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B6877007 : Blo 2009435 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B4584671 : Blo 2009435 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B3056447 : Blo 2009435 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B2037631 : Blo 2009435 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B2716841 : Blo 2009435 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B7244909 : Blo 2009435 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B4829939 : Blo 2009435 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B3219959 : Blo 2009435 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B8586557 : Blo 2009435 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B5724371 : Blo 2009435 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B3816247 : Blo 2009435 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B5088329 : Blo 2009435 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B3392219 : Blo 2009435 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B2261479 : Blo 2009435 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B3015305 : Blo 2009435 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B2010203 : Blo 2009435 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B10176677 : Blo 2009435 10176677 := bbase (se 4 (by rfl) ⟨954063, by rfl⟩ : syracuseStep 10176677 = 1908127) (by norm_num)
theorem B6784451 : Blo 2009435 6784451 := bstep (se 1 (by rfl) ⟨5088338, by rfl⟩ : syracuseStep 6784451 = 10176677) B10176677
theorem B4522967 : Blo 2009435 4522967 := bstep (se 1 (by rfl) ⟨3392225, by rfl⟩ : syracuseStep 4522967 = 6784451) B6784451
theorem B3015311 : Blo 2009435 3015311 := bstep (se 1 (by rfl) ⟨2261483, by rfl⟩ : syracuseStep 3015311 = 4522967) B4522967
theorem B2010207 : Blo 2009435 2010207 := bstep (se 1 (by rfl) ⟨1507655, by rfl⟩ : syracuseStep 2010207 = 3015311) B3015311
theorem B3015317 : Blo 2009435 3015317 := bbase (se 6 (by rfl) ⟨70671, by rfl⟩ : syracuseStep 3015317 = 141343) (by norm_num)
theorem B2010211 : Blo 2009435 2010211 := bstep (se 1 (by rfl) ⟨1507658, by rfl⟩ : syracuseStep 2010211 = 3015317) B3015317
theorem B3721997 : Blo 2009435 3721997 := bbase (se 3 (by rfl) ⟨697874, by rfl⟩ : syracuseStep 3721997 = 1395749) (by norm_num)
theorem B9925325 : Blo 2009435 9925325 := bstep (se 3 (by rfl) ⟨1860998, by rfl⟩ : syracuseStep 9925325 = 3721997) B3721997
theorem B6616883 : Blo 2009435 6616883 := bstep (se 1 (by rfl) ⟨4962662, by rfl⟩ : syracuseStep 6616883 = 9925325) B9925325
theorem B4411255 : Blo 2009435 4411255 := bstep (se 1 (by rfl) ⟨3308441, by rfl⟩ : syracuseStep 4411255 = 6616883) B6616883
theorem B5881673 : Blo 2009435 5881673 := bstep (se 2 (by rfl) ⟨2205627, by rfl⟩ : syracuseStep 5881673 = 4411255) B4411255
theorem B3921115 : Blo 2009435 3921115 := bstep (se 1 (by rfl) ⟨2940836, by rfl⟩ : syracuseStep 3921115 = 5881673) B5881673
theorem B5228153 : Blo 2009435 5228153 := bstep (se 2 (by rfl) ⟨1960557, by rfl⟩ : syracuseStep 5228153 = 3921115) B3921115
theorem B3485435 : Blo 2009435 3485435 := bstep (se 1 (by rfl) ⟨2614076, by rfl⟩ : syracuseStep 3485435 = 5228153) B5228153
theorem B37177973 : Blo 2009435 37177973 := bstep (se 5 (by rfl) ⟨1742717, by rfl⟩ : syracuseStep 37177973 = 3485435) B3485435
theorem B24785315 : Blo 2009435 24785315 := bstep (se 1 (by rfl) ⟨18588986, by rfl⟩ : syracuseStep 24785315 = 37177973) B37177973
theorem B16523543 : Blo 2009435 16523543 := bstep (se 1 (by rfl) ⟨12392657, by rfl⟩ : syracuseStep 16523543 = 24785315) B24785315
theorem B11015695 : Blo 2009435 11015695 := bstep (se 1 (by rfl) ⟨8261771, by rfl⟩ : syracuseStep 11015695 = 16523543) B16523543
theorem B58750373 : Blo 2009435 58750373 := bstep (se 4 (by rfl) ⟨5507847, by rfl⟩ : syracuseStep 58750373 = 11015695) B11015695
theorem B39166915 : Blo 2009435 39166915 := bstep (se 1 (by rfl) ⟨29375186, by rfl⟩ : syracuseStep 39166915 = 58750373) B58750373
theorem B52222553 : Blo 2009435 52222553 := bstep (se 2 (by rfl) ⟨19583457, by rfl⟩ : syracuseStep 52222553 = 39166915) B39166915
theorem B34815035 : Blo 2009435 34815035 := bstep (se 1 (by rfl) ⟨26111276, by rfl⟩ : syracuseStep 34815035 = 52222553) B52222553
theorem B23210023 : Blo 2009435 23210023 := bstep (se 1 (by rfl) ⟨17407517, by rfl⟩ : syracuseStep 23210023 = 34815035) B34815035
theorem B30946697 : Blo 2009435 30946697 := bstep (se 2 (by rfl) ⟨11605011, by rfl⟩ : syracuseStep 30946697 = 23210023) B23210023
theorem B20631131 : Blo 2009435 20631131 := bstep (se 1 (by rfl) ⟨15473348, by rfl⟩ : syracuseStep 20631131 = 30946697) B30946697
theorem B13754087 : Blo 2009435 13754087 := bstep (se 1 (by rfl) ⟨10315565, by rfl⟩ : syracuseStep 13754087 = 20631131) B20631131
theorem B9169391 : Blo 2009435 9169391 := bstep (se 1 (by rfl) ⟨6877043, by rfl⟩ : syracuseStep 9169391 = 13754087) B13754087
theorem B6112927 : Blo 2009435 6112927 := bstep (se 1 (by rfl) ⟨4584695, by rfl⟩ : syracuseStep 6112927 = 9169391) B9169391
theorem B32602277 : Blo 2009435 32602277 := bstep (se 4 (by rfl) ⟨3056463, by rfl⟩ : syracuseStep 32602277 = 6112927) B6112927
theorem B21734851 : Blo 2009435 21734851 := bstep (se 1 (by rfl) ⟨16301138, by rfl⟩ : syracuseStep 21734851 = 32602277) B32602277
theorem B28979801 : Blo 2009435 28979801 := bstep (se 2 (by rfl) ⟨10867425, by rfl⟩ : syracuseStep 28979801 = 21734851) B21734851
theorem B19319867 : Blo 2009435 19319867 := bstep (se 1 (by rfl) ⟨14489900, by rfl⟩ : syracuseStep 19319867 = 28979801) B28979801
theorem B12879911 : Blo 2009435 12879911 := bstep (se 1 (by rfl) ⟨9659933, by rfl⟩ : syracuseStep 12879911 = 19319867) B19319867
theorem B8586607 : Blo 2009435 8586607 := bstep (se 1 (by rfl) ⟨6439955, by rfl⟩ : syracuseStep 8586607 = 12879911) B12879911
theorem B11448809 : Blo 2009435 11448809 := bstep (se 2 (by rfl) ⟨4293303, by rfl⟩ : syracuseStep 11448809 = 8586607) B8586607
theorem B7632539 : Blo 2009435 7632539 := bstep (se 1 (by rfl) ⟨5724404, by rfl⟩ : syracuseStep 7632539 = 11448809) B11448809
theorem B5088359 : Blo 2009435 5088359 := bstep (se 1 (by rfl) ⟨3816269, by rfl⟩ : syracuseStep 5088359 = 7632539) B7632539
theorem B3392239 : Blo 2009435 3392239 := bstep (se 1 (by rfl) ⟨2544179, by rfl⟩ : syracuseStep 3392239 = 5088359) B5088359
theorem B4522985 : Blo 2009435 4522985 := bstep (se 2 (by rfl) ⟨1696119, by rfl⟩ : syracuseStep 4522985 = 3392239) B3392239
theorem B3015323 : Blo 2009435 3015323 := bstep (se 1 (by rfl) ⟨2261492, by rfl⟩ : syracuseStep 3015323 = 4522985) B4522985
theorem B2010215 : Blo 2009435 2010215 := bstep (se 1 (by rfl) ⟨1507661, by rfl⟩ : syracuseStep 2010215 = 3015323) B3015323
theorem B2261497 : Blo 2009435 2261497 := bbase (se 2 (by rfl) ⟨848061, by rfl⟩ : syracuseStep 2261497 = 1696123) (by norm_num)
theorem B3015329 : Blo 2009435 3015329 := bstep (se 2 (by rfl) ⟨1130748, by rfl⟩ : syracuseStep 3015329 = 2261497) B2261497
theorem B2010219 : Blo 2009435 2010219 := bstep (se 1 (by rfl) ⟨1507664, by rfl⟩ : syracuseStep 2010219 = 3015329) B3015329
theorem B2414993 : Blo 2009435 2414993 := bbase (se 2 (by rfl) ⟨905622, by rfl⟩ : syracuseStep 2414993 = 1811245) (by norm_num)
theorem B6439981 : Blo 2009435 6439981 := bstep (se 3 (by rfl) ⟨1207496, by rfl⟩ : syracuseStep 6439981 = 2414993) B2414993
theorem B8586641 : Blo 2009435 8586641 := bstep (se 2 (by rfl) ⟨3219990, by rfl⟩ : syracuseStep 8586641 = 6439981) B6439981
theorem B5724427 : Blo 2009435 5724427 := bstep (se 1 (by rfl) ⟨4293320, by rfl⟩ : syracuseStep 5724427 = 8586641) B8586641
theorem B7632569 : Blo 2009435 7632569 := bstep (se 2 (by rfl) ⟨2862213, by rfl⟩ : syracuseStep 7632569 = 5724427) B5724427
theorem B5088379 : Blo 2009435 5088379 := bstep (se 1 (by rfl) ⟨3816284, by rfl⟩ : syracuseStep 5088379 = 7632569) B7632569
theorem B6784505 : Blo 2009435 6784505 := bstep (se 2 (by rfl) ⟨2544189, by rfl⟩ : syracuseStep 6784505 = 5088379) B5088379
theorem B4523003 : Blo 2009435 4523003 := bstep (se 1 (by rfl) ⟨3392252, by rfl⟩ : syracuseStep 4523003 = 6784505) B6784505
theorem B3015335 : Blo 2009435 3015335 := bstep (se 1 (by rfl) ⟨2261501, by rfl⟩ : syracuseStep 3015335 = 4523003) B4523003
theorem B2010223 : Blo 2009435 2010223 := bstep (se 1 (by rfl) ⟨1507667, by rfl⟩ : syracuseStep 2010223 = 3015335) B3015335
theorem B3015341 : Blo 2009435 3015341 := bbase (se 3 (by rfl) ⟨565376, by rfl⟩ : syracuseStep 3015341 = 1130753) (by norm_num)
theorem B2010227 : Blo 2009435 2010227 := bstep (se 1 (by rfl) ⟨1507670, by rfl⟩ : syracuseStep 2010227 = 3015341) B3015341
theorem B4523021 : Blo 2009435 4523021 := bbase (se 3 (by rfl) ⟨848066, by rfl⟩ : syracuseStep 4523021 = 1696133) (by norm_num)
theorem B3015347 : Blo 2009435 3015347 := bstep (se 1 (by rfl) ⟨2261510, by rfl⟩ : syracuseStep 3015347 = 4523021) B4523021
theorem B2010231 : Blo 2009435 2010231 := bstep (se 1 (by rfl) ⟨1507673, by rfl⟩ : syracuseStep 2010231 = 3015347) B3015347
theorem B2544205 : Blo 2009435 2544205 := bbase (se 3 (by rfl) ⟨477038, by rfl⟩ : syracuseStep 2544205 = 954077) (by norm_num)
theorem B3392273 : Blo 2009435 3392273 := bstep (se 2 (by rfl) ⟨1272102, by rfl⟩ : syracuseStep 3392273 = 2544205) B2544205
theorem B2261515 : Blo 2009435 2261515 := bstep (se 1 (by rfl) ⟨1696136, by rfl⟩ : syracuseStep 2261515 = 3392273) B3392273
theorem B3015353 : Blo 2009435 3015353 := bstep (se 2 (by rfl) ⟨1130757, by rfl⟩ : syracuseStep 3015353 = 2261515) B2261515
theorem B2010235 : Blo 2009435 2010235 := bstep (se 1 (by rfl) ⟨1507676, by rfl⟩ : syracuseStep 2010235 = 3015353) B3015353
theorem B73355989 : Blo 2009435 73355989 := bbase (se 7 (by rfl) ⟨859640, by rfl⟩ : syracuseStep 73355989 = 1719281) (by norm_num)
theorem B97807985 : Blo 2009435 97807985 := bstep (se 2 (by rfl) ⟨36677994, by rfl⟩ : syracuseStep 97807985 = 73355989) B73355989
theorem B65205323 : Blo 2009435 65205323 := bstep (se 1 (by rfl) ⟨48903992, by rfl⟩ : syracuseStep 65205323 = 97807985) B97807985
theorem B43470215 : Blo 2009435 43470215 := bstep (se 1 (by rfl) ⟨32602661, by rfl⟩ : syracuseStep 43470215 = 65205323) B65205323
theorem B28980143 : Blo 2009435 28980143 := bstep (se 1 (by rfl) ⟨21735107, by rfl⟩ : syracuseStep 28980143 = 43470215) B43470215
theorem B19320095 : Blo 2009435 19320095 := bstep (se 1 (by rfl) ⟨14490071, by rfl⟩ : syracuseStep 19320095 = 28980143) B28980143
theorem B12880063 : Blo 2009435 12880063 := bstep (se 1 (by rfl) ⟨9660047, by rfl⟩ : syracuseStep 12880063 = 19320095) B19320095
theorem B17173417 : Blo 2009435 17173417 := bstep (se 2 (by rfl) ⟨6440031, by rfl⟩ : syracuseStep 17173417 = 12880063) B12880063
theorem B22897889 : Blo 2009435 22897889 := bstep (se 2 (by rfl) ⟨8586708, by rfl⟩ : syracuseStep 22897889 = 17173417) B17173417
theorem B15265259 : Blo 2009435 15265259 := bstep (se 1 (by rfl) ⟨11448944, by rfl⟩ : syracuseStep 15265259 = 22897889) B22897889
theorem B10176839 : Blo 2009435 10176839 := bstep (se 1 (by rfl) ⟨7632629, by rfl⟩ : syracuseStep 10176839 = 15265259) B15265259
theorem B6784559 : Blo 2009435 6784559 := bstep (se 1 (by rfl) ⟨5088419, by rfl⟩ : syracuseStep 6784559 = 10176839) B10176839
theorem B4523039 : Blo 2009435 4523039 := bstep (se 1 (by rfl) ⟨3392279, by rfl⟩ : syracuseStep 4523039 = 6784559) B6784559
theorem B3015359 : Blo 2009435 3015359 := bstep (se 1 (by rfl) ⟨2261519, by rfl⟩ : syracuseStep 3015359 = 4523039) B4523039
theorem B2010239 : Blo 2009435 2010239 := bstep (se 1 (by rfl) ⟨1507679, by rfl⟩ : syracuseStep 2010239 = 3015359) B3015359
theorem B3015365 : Blo 2009435 3015365 := bbase (se 4 (by rfl) ⟨282690, by rfl⟩ : syracuseStep 3015365 = 565381) (by norm_num)
theorem B2010243 : Blo 2009435 2010243 := bstep (se 1 (by rfl) ⟨1507682, by rfl⟩ : syracuseStep 2010243 = 3015365) B3015365
theorem B3392293 : Blo 2009435 3392293 := bbase (se 4 (by rfl) ⟨318027, by rfl⟩ : syracuseStep 3392293 = 636055) (by norm_num)
theorem B4523057 : Blo 2009435 4523057 := bstep (se 2 (by rfl) ⟨1696146, by rfl⟩ : syracuseStep 4523057 = 3392293) B3392293
theorem B3015371 : Blo 2009435 3015371 := bstep (se 1 (by rfl) ⟨2261528, by rfl⟩ : syracuseStep 3015371 = 4523057) B4523057
theorem B2010247 : Blo 2009435 2010247 := bstep (se 1 (by rfl) ⟨1507685, by rfl⟩ : syracuseStep 2010247 = 3015371) B3015371
theorem B2261533 : Blo 2009435 2261533 := bbase (se 3 (by rfl) ⟨424037, by rfl⟩ : syracuseStep 2261533 = 848075) (by norm_num)
theorem B3015377 : Blo 2009435 3015377 := bstep (se 2 (by rfl) ⟨1130766, by rfl⟩ : syracuseStep 3015377 = 2261533) B2261533
theorem B2010251 : Blo 2009435 2010251 := bstep (se 1 (by rfl) ⟨1507688, by rfl⟩ : syracuseStep 2010251 = 3015377) B3015377
theorem B6784613 : Blo 2009435 6784613 := bbase (se 4 (by rfl) ⟨636057, by rfl⟩ : syracuseStep 6784613 = 1272115) (by norm_num)
theorem B4523075 : Blo 2009435 4523075 := bstep (se 1 (by rfl) ⟨3392306, by rfl⟩ : syracuseStep 4523075 = 6784613) B6784613
theorem B3015383 : Blo 2009435 3015383 := bstep (se 1 (by rfl) ⟨2261537, by rfl⟩ : syracuseStep 3015383 = 4523075) B4523075
theorem B2010255 : Blo 2009435 2010255 := bstep (se 1 (by rfl) ⟨1507691, by rfl⟩ : syracuseStep 2010255 = 3015383) B3015383
theorem B3015389 : Blo 2009435 3015389 := bbase (se 3 (by rfl) ⟨565385, by rfl⟩ : syracuseStep 3015389 = 1130771) (by norm_num)
theorem B2010259 : Blo 2009435 2010259 := bstep (se 1 (by rfl) ⟨1507694, by rfl⟩ : syracuseStep 2010259 = 3015389) B3015389
theorem B4523093 : Blo 2009435 4523093 := bbase (se 8 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 4523093 = 53005) (by norm_num)
theorem B3015395 : Blo 2009435 3015395 := bstep (se 1 (by rfl) ⟨2261546, by rfl⟩ : syracuseStep 3015395 = 4523093) B4523093
theorem B2010263 : Blo 2009435 2010263 := bstep (se 1 (by rfl) ⟨1507697, by rfl⟩ : syracuseStep 2010263 = 3015395) B3015395
theorem B2323685 : Blo 2009435 2323685 := bbase (se 4 (by rfl) ⟨217845, by rfl⟩ : syracuseStep 2323685 = 435691) (by norm_num)
theorem B6196493 : Blo 2009435 6196493 := bstep (se 3 (by rfl) ⟨1161842, by rfl⟩ : syracuseStep 6196493 = 2323685) B2323685
theorem B4130995 : Blo 2009435 4130995 := bstep (se 1 (by rfl) ⟨3098246, by rfl⟩ : syracuseStep 4130995 = 6196493) B6196493
theorem B5507993 : Blo 2009435 5507993 := bstep (se 2 (by rfl) ⟨2065497, by rfl⟩ : syracuseStep 5507993 = 4130995) B4130995
theorem B3671995 : Blo 2009435 3671995 := bstep (se 1 (by rfl) ⟨2753996, by rfl⟩ : syracuseStep 3671995 = 5507993) B5507993
theorem B4895993 : Blo 2009435 4895993 := bstep (se 2 (by rfl) ⟨1835997, by rfl⟩ : syracuseStep 4895993 = 3671995) B3671995
theorem B3263995 : Blo 2009435 3263995 := bstep (se 1 (by rfl) ⟨2447996, by rfl⟩ : syracuseStep 3263995 = 4895993) B4895993
theorem B17407973 : Blo 2009435 17407973 := bstep (se 4 (by rfl) ⟨1631997, by rfl⟩ : syracuseStep 17407973 = 3263995) B3263995
theorem B46421261 : Blo 2009435 46421261 := bstep (se 3 (by rfl) ⟨8703986, by rfl⟩ : syracuseStep 46421261 = 17407973) B17407973
theorem B30947507 : Blo 2009435 30947507 := bstep (se 1 (by rfl) ⟨23210630, by rfl⟩ : syracuseStep 30947507 = 46421261) B46421261
theorem B20631671 : Blo 2009435 20631671 := bstep (se 1 (by rfl) ⟨15473753, by rfl⟩ : syracuseStep 20631671 = 30947507) B30947507
theorem B13754447 : Blo 2009435 13754447 := bstep (se 1 (by rfl) ⟨10315835, by rfl⟩ : syracuseStep 13754447 = 20631671) B20631671
theorem B9169631 : Blo 2009435 9169631 := bstep (se 1 (by rfl) ⟨6877223, by rfl⟩ : syracuseStep 9169631 = 13754447) B13754447
theorem B6113087 : Blo 2009435 6113087 := bstep (se 1 (by rfl) ⟨4584815, by rfl⟩ : syracuseStep 6113087 = 9169631) B9169631
theorem B4075391 : Blo 2009435 4075391 := bstep (se 1 (by rfl) ⟨3056543, by rfl⟩ : syracuseStep 4075391 = 6113087) B6113087
theorem B10867709 : Blo 2009435 10867709 := bstep (se 3 (by rfl) ⟨2037695, by rfl⟩ : syracuseStep 10867709 = 4075391) B4075391
theorem B7245139 : Blo 2009435 7245139 := bstep (se 1 (by rfl) ⟨5433854, by rfl⟩ : syracuseStep 7245139 = 10867709) B10867709
theorem B9660185 : Blo 2009435 9660185 := bstep (se 2 (by rfl) ⟨3622569, by rfl⟩ : syracuseStep 9660185 = 7245139) B7245139
theorem B6440123 : Blo 2009435 6440123 := bstep (se 1 (by rfl) ⟨4830092, by rfl⟩ : syracuseStep 6440123 = 9660185) B9660185
theorem B4293415 : Blo 2009435 4293415 := bstep (se 1 (by rfl) ⟨3220061, by rfl⟩ : syracuseStep 4293415 = 6440123) B6440123
theorem B5724553 : Blo 2009435 5724553 := bstep (se 2 (by rfl) ⟨2146707, by rfl⟩ : syracuseStep 5724553 = 4293415) B4293415
theorem B7632737 : Blo 2009435 7632737 := bstep (se 2 (by rfl) ⟨2862276, by rfl⟩ : syracuseStep 7632737 = 5724553) B5724553
theorem B5088491 : Blo 2009435 5088491 := bstep (se 1 (by rfl) ⟨3816368, by rfl⟩ : syracuseStep 5088491 = 7632737) B7632737
theorem B3392327 : Blo 2009435 3392327 := bstep (se 1 (by rfl) ⟨2544245, by rfl⟩ : syracuseStep 3392327 = 5088491) B5088491
theorem B2261551 : Blo 2009435 2261551 := bstep (se 1 (by rfl) ⟨1696163, by rfl⟩ : syracuseStep 2261551 = 3392327) B3392327
theorem B3015401 : Blo 2009435 3015401 := bstep (se 2 (by rfl) ⟨1130775, by rfl⟩ : syracuseStep 3015401 = 2261551) B2261551
theorem B2010267 : Blo 2009435 2010267 := bstep (se 1 (by rfl) ⟨1507700, by rfl⟩ : syracuseStep 2010267 = 3015401) B3015401
theorem B3868445 : Blo 2009435 3868445 := bbase (se 3 (by rfl) ⟨725333, by rfl⟩ : syracuseStep 3868445 = 1450667) (by norm_num)
theorem B2578963 : Blo 2009435 2578963 := bstep (se 1 (by rfl) ⟨1934222, by rfl⟩ : syracuseStep 2578963 = 3868445) B3868445
theorem B3438617 : Blo 2009435 3438617 := bstep (se 2 (by rfl) ⟨1289481, by rfl⟩ : syracuseStep 3438617 = 2578963) B2578963
theorem B36678581 : Blo 2009435 36678581 := bstep (se 5 (by rfl) ⟨1719308, by rfl⟩ : syracuseStep 36678581 = 3438617) B3438617
theorem B24452387 : Blo 2009435 24452387 := bstep (se 1 (by rfl) ⟨18339290, by rfl⟩ : syracuseStep 24452387 = 36678581) B36678581
theorem B16301591 : Blo 2009435 16301591 := bstep (se 1 (by rfl) ⟨12226193, by rfl⟩ : syracuseStep 16301591 = 24452387) B24452387
theorem B10867727 : Blo 2009435 10867727 := bstep (se 1 (by rfl) ⟨8150795, by rfl⟩ : syracuseStep 10867727 = 16301591) B16301591
theorem B28980605 : Blo 2009435 28980605 := bstep (se 3 (by rfl) ⟨5433863, by rfl⟩ : syracuseStep 28980605 = 10867727) B10867727
theorem B19320403 : Blo 2009435 19320403 := bstep (se 1 (by rfl) ⟨14490302, by rfl⟩ : syracuseStep 19320403 = 28980605) B28980605
theorem B25760537 : Blo 2009435 25760537 := bstep (se 2 (by rfl) ⟨9660201, by rfl⟩ : syracuseStep 25760537 = 19320403) B19320403
theorem B17173691 : Blo 2009435 17173691 := bstep (se 1 (by rfl) ⟨12880268, by rfl⟩ : syracuseStep 17173691 = 25760537) B25760537
theorem B11449127 : Blo 2009435 11449127 := bstep (se 1 (by rfl) ⟨8586845, by rfl⟩ : syracuseStep 11449127 = 17173691) B17173691
theorem B7632751 : Blo 2009435 7632751 := bstep (se 1 (by rfl) ⟨5724563, by rfl⟩ : syracuseStep 7632751 = 11449127) B11449127
theorem B10177001 : Blo 2009435 10177001 := bstep (se 2 (by rfl) ⟨3816375, by rfl⟩ : syracuseStep 10177001 = 7632751) B7632751
theorem B6784667 : Blo 2009435 6784667 := bstep (se 1 (by rfl) ⟨5088500, by rfl⟩ : syracuseStep 6784667 = 10177001) B10177001
theorem B4523111 : Blo 2009435 4523111 := bstep (se 1 (by rfl) ⟨3392333, by rfl⟩ : syracuseStep 4523111 = 6784667) B6784667
theorem B3015407 : Blo 2009435 3015407 := bstep (se 1 (by rfl) ⟨2261555, by rfl⟩ : syracuseStep 3015407 = 4523111) B4523111
theorem B2010271 : Blo 2009435 2010271 := bstep (se 1 (by rfl) ⟨1507703, by rfl⟩ : syracuseStep 2010271 = 3015407) B3015407
theorem B3015413 : Blo 2009435 3015413 := bbase (se 5 (by rfl) ⟨141347, by rfl⟩ : syracuseStep 3015413 = 282695) (by norm_num)
theorem B2010275 : Blo 2009435 2010275 := bstep (se 1 (by rfl) ⟨1507706, by rfl⟩ : syracuseStep 2010275 = 3015413) B3015413
theorem B15473845 : Blo 2009435 15473845 := bbase (se 5 (by rfl) ⟨725336, by rfl⟩ : syracuseStep 15473845 = 1450673) (by norm_num)
theorem B20631793 : Blo 2009435 20631793 := bstep (se 2 (by rfl) ⟨7736922, by rfl⟩ : syracuseStep 20631793 = 15473845) B15473845
theorem B27509057 : Blo 2009435 27509057 := bstep (se 2 (by rfl) ⟨10315896, by rfl⟩ : syracuseStep 27509057 = 20631793) B20631793
theorem B18339371 : Blo 2009435 18339371 := bstep (se 1 (by rfl) ⟨13754528, by rfl⟩ : syracuseStep 18339371 = 27509057) B27509057
theorem B12226247 : Blo 2009435 12226247 := bstep (se 1 (by rfl) ⟨9169685, by rfl⟩ : syracuseStep 12226247 = 18339371) B18339371
theorem B8150831 : Blo 2009435 8150831 := bstep (se 1 (by rfl) ⟨6113123, by rfl⟩ : syracuseStep 8150831 = 12226247) B12226247
theorem B5433887 : Blo 2009435 5433887 := bstep (se 1 (by rfl) ⟨4075415, by rfl⟩ : syracuseStep 5433887 = 8150831) B8150831
theorem B3622591 : Blo 2009435 3622591 := bstep (se 1 (by rfl) ⟨2716943, by rfl⟩ : syracuseStep 3622591 = 5433887) B5433887
theorem B4830121 : Blo 2009435 4830121 := bstep (se 2 (by rfl) ⟨1811295, by rfl⟩ : syracuseStep 4830121 = 3622591) B3622591
theorem B6440161 : Blo 2009435 6440161 := bstep (se 2 (by rfl) ⟨2415060, by rfl⟩ : syracuseStep 6440161 = 4830121) B4830121
theorem B8586881 : Blo 2009435 8586881 := bstep (se 2 (by rfl) ⟨3220080, by rfl⟩ : syracuseStep 8586881 = 6440161) B6440161
theorem B5724587 : Blo 2009435 5724587 := bstep (se 1 (by rfl) ⟨4293440, by rfl⟩ : syracuseStep 5724587 = 8586881) B8586881
theorem B3816391 : Blo 2009435 3816391 := bstep (se 1 (by rfl) ⟨2862293, by rfl⟩ : syracuseStep 3816391 = 5724587) B5724587
theorem B5088521 : Blo 2009435 5088521 := bstep (se 2 (by rfl) ⟨1908195, by rfl⟩ : syracuseStep 5088521 = 3816391) B3816391
theorem B3392347 : Blo 2009435 3392347 := bstep (se 1 (by rfl) ⟨2544260, by rfl⟩ : syracuseStep 3392347 = 5088521) B5088521
theorem B4523129 : Blo 2009435 4523129 := bstep (se 2 (by rfl) ⟨1696173, by rfl⟩ : syracuseStep 4523129 = 3392347) B3392347
theorem B3015419 : Blo 2009435 3015419 := bstep (se 1 (by rfl) ⟨2261564, by rfl⟩ : syracuseStep 3015419 = 4523129) B4523129
theorem B2010279 : Blo 2009435 2010279 := bstep (se 1 (by rfl) ⟨1507709, by rfl⟩ : syracuseStep 2010279 = 3015419) B3015419
theorem B2261569 : Blo 2009435 2261569 := bbase (se 2 (by rfl) ⟨848088, by rfl⟩ : syracuseStep 2261569 = 1696177) (by norm_num)
theorem B3015425 : Blo 2009435 3015425 := bstep (se 2 (by rfl) ⟨1130784, by rfl⟩ : syracuseStep 3015425 = 2261569) B2261569
theorem B2010283 : Blo 2009435 2010283 := bstep (se 1 (by rfl) ⟨1507712, by rfl⟩ : syracuseStep 2010283 = 3015425) B3015425
theorem B5088541 : Blo 2009435 5088541 := bbase (se 3 (by rfl) ⟨954101, by rfl⟩ : syracuseStep 5088541 = 1908203) (by norm_num)
theorem B6784721 : Blo 2009435 6784721 := bstep (se 2 (by rfl) ⟨2544270, by rfl⟩ : syracuseStep 6784721 = 5088541) B5088541
theorem B4523147 : Blo 2009435 4523147 := bstep (se 1 (by rfl) ⟨3392360, by rfl⟩ : syracuseStep 4523147 = 6784721) B6784721
theorem B3015431 : Blo 2009435 3015431 := bstep (se 1 (by rfl) ⟨2261573, by rfl⟩ : syracuseStep 3015431 = 4523147) B4523147
theorem B2010287 : Blo 2009435 2010287 := bstep (se 1 (by rfl) ⟨1507715, by rfl⟩ : syracuseStep 2010287 = 3015431) B3015431
theorem B3015437 : Blo 2009435 3015437 := bbase (se 3 (by rfl) ⟨565394, by rfl⟩ : syracuseStep 3015437 = 1130789) (by norm_num)
theorem B2010291 : Blo 2009435 2010291 := bstep (se 1 (by rfl) ⟨1507718, by rfl⟩ : syracuseStep 2010291 = 3015437) B3015437
theorem B4523165 : Blo 2009435 4523165 := bbase (se 3 (by rfl) ⟨848093, by rfl⟩ : syracuseStep 4523165 = 1696187) (by norm_num)
theorem B3015443 : Blo 2009435 3015443 := bstep (se 1 (by rfl) ⟨2261582, by rfl⟩ : syracuseStep 3015443 = 4523165) B4523165
theorem B2010295 : Blo 2009435 2010295 := bstep (se 1 (by rfl) ⟨1507721, by rfl⟩ : syracuseStep 2010295 = 3015443) B3015443
theorem B3392381 : Blo 2009435 3392381 := bbase (se 3 (by rfl) ⟨636071, by rfl⟩ : syracuseStep 3392381 = 1272143) (by norm_num)
theorem B2261587 : Blo 2009435 2261587 := bstep (se 1 (by rfl) ⟨1696190, by rfl⟩ : syracuseStep 2261587 = 3392381) B3392381
theorem B3015449 : Blo 2009435 3015449 := bstep (se 2 (by rfl) ⟨1130793, by rfl⟩ : syracuseStep 3015449 = 2261587) B2261587
theorem B2010299 : Blo 2009435 2010299 := bstep (se 1 (by rfl) ⟨1507724, by rfl⟩ : syracuseStep 2010299 = 3015449) B3015449
theorem B2415089 : Blo 2009435 2415089 := bbase (se 2 (by rfl) ⟨905658, by rfl⟩ : syracuseStep 2415089 = 1811317) (by norm_num)
theorem B6440237 : Blo 2009435 6440237 := bstep (se 3 (by rfl) ⟨1207544, by rfl⟩ : syracuseStep 6440237 = 2415089) B2415089
theorem B4293491 : Blo 2009435 4293491 := bstep (se 1 (by rfl) ⟨3220118, by rfl⟩ : syracuseStep 4293491 = 6440237) B6440237
theorem B11449309 : Blo 2009435 11449309 := bstep (se 3 (by rfl) ⟨2146745, by rfl⟩ : syracuseStep 11449309 = 4293491) B4293491
theorem B15265745 : Blo 2009435 15265745 := bstep (se 2 (by rfl) ⟨5724654, by rfl⟩ : syracuseStep 15265745 = 11449309) B11449309
theorem B10177163 : Blo 2009435 10177163 := bstep (se 1 (by rfl) ⟨7632872, by rfl⟩ : syracuseStep 10177163 = 15265745) B15265745
theorem B6784775 : Blo 2009435 6784775 := bstep (se 1 (by rfl) ⟨5088581, by rfl⟩ : syracuseStep 6784775 = 10177163) B10177163
theorem B4523183 : Blo 2009435 4523183 := bstep (se 1 (by rfl) ⟨3392387, by rfl⟩ : syracuseStep 4523183 = 6784775) B6784775
theorem B3015455 : Blo 2009435 3015455 := bstep (se 1 (by rfl) ⟨2261591, by rfl⟩ : syracuseStep 3015455 = 4523183) B4523183
theorem B2010303 : Blo 2009435 2010303 := bstep (se 1 (by rfl) ⟨1507727, by rfl⟩ : syracuseStep 2010303 = 3015455) B3015455
theorem B3015461 : Blo 2009435 3015461 := bbase (se 4 (by rfl) ⟨282699, by rfl⟩ : syracuseStep 3015461 = 565399) (by norm_num)
theorem B2010307 : Blo 2009435 2010307 := bstep (se 1 (by rfl) ⟨1507730, by rfl⟩ : syracuseStep 2010307 = 3015461) B3015461
theorem B2544301 : Blo 2009435 2544301 := bbase (se 3 (by rfl) ⟨477056, by rfl⟩ : syracuseStep 2544301 = 954113) (by norm_num)
theorem B3392401 : Blo 2009435 3392401 := bstep (se 2 (by rfl) ⟨1272150, by rfl⟩ : syracuseStep 3392401 = 2544301) B2544301
theorem B4523201 : Blo 2009435 4523201 := bstep (se 2 (by rfl) ⟨1696200, by rfl⟩ : syracuseStep 4523201 = 3392401) B3392401
theorem B3015467 : Blo 2009435 3015467 := bstep (se 1 (by rfl) ⟨2261600, by rfl⟩ : syracuseStep 3015467 = 4523201) B4523201
theorem B2010311 : Blo 2009435 2010311 := bstep (se 1 (by rfl) ⟨1507733, by rfl⟩ : syracuseStep 2010311 = 3015467) B3015467
theorem B2261605 : Blo 2009435 2261605 := bbase (se 4 (by rfl) ⟨212025, by rfl⟩ : syracuseStep 2261605 = 424051) (by norm_num)
theorem B3015473 : Blo 2009435 3015473 := bstep (se 2 (by rfl) ⟨1130802, by rfl⟩ : syracuseStep 3015473 = 2261605) B2261605
theorem B2010315 : Blo 2009435 2010315 := bstep (se 1 (by rfl) ⟨1507736, by rfl⟩ : syracuseStep 2010315 = 3015473) B3015473
theorem B2415109 : Blo 2009435 2415109 := bbase (se 4 (by rfl) ⟨226416, by rfl⟩ : syracuseStep 2415109 = 452833) (by norm_num)
theorem B3220145 : Blo 2009435 3220145 := bstep (se 2 (by rfl) ⟨1207554, by rfl⟩ : syracuseStep 3220145 = 2415109) B2415109
theorem B2146763 : Blo 2009435 2146763 := bstep (se 1 (by rfl) ⟨1610072, by rfl⟩ : syracuseStep 2146763 = 3220145) B3220145
theorem B5724701 : Blo 2009435 5724701 := bstep (se 3 (by rfl) ⟨1073381, by rfl⟩ : syracuseStep 5724701 = 2146763) B2146763
theorem B3816467 : Blo 2009435 3816467 := bstep (se 1 (by rfl) ⟨2862350, by rfl⟩ : syracuseStep 3816467 = 5724701) B5724701
theorem B2544311 : Blo 2009435 2544311 := bstep (se 1 (by rfl) ⟨1908233, by rfl⟩ : syracuseStep 2544311 = 3816467) B3816467
theorem B6784829 : Blo 2009435 6784829 := bstep (se 3 (by rfl) ⟨1272155, by rfl⟩ : syracuseStep 6784829 = 2544311) B2544311
theorem B4523219 : Blo 2009435 4523219 := bstep (se 1 (by rfl) ⟨3392414, by rfl⟩ : syracuseStep 4523219 = 6784829) B6784829
theorem B3015479 : Blo 2009435 3015479 := bstep (se 1 (by rfl) ⟨2261609, by rfl⟩ : syracuseStep 3015479 = 4523219) B4523219
theorem B2010319 : Blo 2009435 2010319 := bstep (se 1 (by rfl) ⟨1507739, by rfl⟩ : syracuseStep 2010319 = 3015479) B3015479
theorem B3015485 : Blo 2009435 3015485 := bbase (se 3 (by rfl) ⟨565403, by rfl⟩ : syracuseStep 3015485 = 1130807) (by norm_num)
theorem B2010323 : Blo 2009435 2010323 := bstep (se 1 (by rfl) ⟨1507742, by rfl⟩ : syracuseStep 2010323 = 3015485) B3015485
theorem B4523237 : Blo 2009435 4523237 := bbase (se 4 (by rfl) ⟨424053, by rfl⟩ : syracuseStep 4523237 = 848107) (by norm_num)
theorem B3015491 : Blo 2009435 3015491 := bstep (se 1 (by rfl) ⟨2261618, by rfl⟩ : syracuseStep 3015491 = 4523237) B4523237
theorem B2010327 : Blo 2009435 2010327 := bstep (se 1 (by rfl) ⟨1507745, by rfl⟩ : syracuseStep 2010327 = 3015491) B3015491
theorem B5088653 : Blo 2009435 5088653 := bbase (se 3 (by rfl) ⟨954122, by rfl⟩ : syracuseStep 5088653 = 1908245) (by norm_num)
theorem B3392435 : Blo 2009435 3392435 := bstep (se 1 (by rfl) ⟨2544326, by rfl⟩ : syracuseStep 3392435 = 5088653) B5088653
theorem B2261623 : Blo 2009435 2261623 := bstep (se 1 (by rfl) ⟨1696217, by rfl⟩ : syracuseStep 2261623 = 3392435) B3392435
theorem B3015497 : Blo 2009435 3015497 := bstep (se 2 (by rfl) ⟨1130811, by rfl⟩ : syracuseStep 3015497 = 2261623) B2261623
theorem B2010331 : Blo 2009435 2010331 := bstep (se 1 (by rfl) ⟨1507748, by rfl⟩ : syracuseStep 2010331 = 3015497) B3015497
theorem B2862373 : Blo 2009435 2862373 := bbase (se 4 (by rfl) ⟨268347, by rfl⟩ : syracuseStep 2862373 = 536695) (by norm_num)
theorem B3816497 : Blo 2009435 3816497 := bstep (se 2 (by rfl) ⟨1431186, by rfl⟩ : syracuseStep 3816497 = 2862373) B2862373
theorem B10177325 : Blo 2009435 10177325 := bstep (se 3 (by rfl) ⟨1908248, by rfl⟩ : syracuseStep 10177325 = 3816497) B3816497
theorem B6784883 : Blo 2009435 6784883 := bstep (se 1 (by rfl) ⟨5088662, by rfl⟩ : syracuseStep 6784883 = 10177325) B10177325
theorem B4523255 : Blo 2009435 4523255 := bstep (se 1 (by rfl) ⟨3392441, by rfl⟩ : syracuseStep 4523255 = 6784883) B6784883
theorem B3015503 : Blo 2009435 3015503 := bstep (se 1 (by rfl) ⟨2261627, by rfl⟩ : syracuseStep 3015503 = 4523255) B4523255
theorem B2010335 : Blo 2009435 2010335 := bstep (se 1 (by rfl) ⟨1507751, by rfl⟩ : syracuseStep 2010335 = 3015503) B3015503
theorem B3015509 : Blo 2009435 3015509 := bbase (se 9 (by rfl) ⟨8834, by rfl⟩ : syracuseStep 3015509 = 17669) (by norm_num)
theorem B2010339 : Blo 2009435 2010339 := bstep (se 1 (by rfl) ⟨1507754, by rfl⟩ : syracuseStep 2010339 = 3015509) B3015509
theorem B7245413 : Blo 2009435 7245413 := bbase (se 4 (by rfl) ⟨679257, by rfl⟩ : syracuseStep 7245413 = 1358515) (by norm_num)
theorem B4830275 : Blo 2009435 4830275 := bstep (se 1 (by rfl) ⟨3622706, by rfl⟩ : syracuseStep 4830275 = 7245413) B7245413
theorem B3220183 : Blo 2009435 3220183 := bstep (se 1 (by rfl) ⟨2415137, by rfl⟩ : syracuseStep 3220183 = 4830275) B4830275
theorem B4293577 : Blo 2009435 4293577 := bstep (se 2 (by rfl) ⟨1610091, by rfl⟩ : syracuseStep 4293577 = 3220183) B3220183
theorem B5724769 : Blo 2009435 5724769 := bstep (se 2 (by rfl) ⟨2146788, by rfl⟩ : syracuseStep 5724769 = 4293577) B4293577
theorem B7633025 : Blo 2009435 7633025 := bstep (se 2 (by rfl) ⟨2862384, by rfl⟩ : syracuseStep 7633025 = 5724769) B5724769
theorem B5088683 : Blo 2009435 5088683 := bstep (se 1 (by rfl) ⟨3816512, by rfl⟩ : syracuseStep 5088683 = 7633025) B7633025
theorem B3392455 : Blo 2009435 3392455 := bstep (se 1 (by rfl) ⟨2544341, by rfl⟩ : syracuseStep 3392455 = 5088683) B5088683
theorem B4523273 : Blo 2009435 4523273 := bstep (se 2 (by rfl) ⟨1696227, by rfl⟩ : syracuseStep 4523273 = 3392455) B3392455
theorem B3015515 : Blo 2009435 3015515 := bstep (se 1 (by rfl) ⟨2261636, by rfl⟩ : syracuseStep 3015515 = 4523273) B4523273
theorem B2010343 : Blo 2009435 2010343 := bstep (se 1 (by rfl) ⟨1507757, by rfl⟩ : syracuseStep 2010343 = 3015515) B3015515
theorem B2261641 : Blo 2009435 2261641 := bbase (se 2 (by rfl) ⟨848115, by rfl⟩ : syracuseStep 2261641 = 1696231) (by norm_num)
theorem B3015521 : Blo 2009435 3015521 := bstep (se 2 (by rfl) ⟨1130820, by rfl⟩ : syracuseStep 3015521 = 2261641) B2261641
theorem B2010347 : Blo 2009435 2010347 := bstep (se 1 (by rfl) ⟨1507760, by rfl⟩ : syracuseStep 2010347 = 3015521) B3015521
theorem B33957269 : Blo 2009435 33957269 := bbase (se 6 (by rfl) ⟨795873, by rfl⟩ : syracuseStep 33957269 = 1591747) (by norm_num)
theorem B22638179 : Blo 2009435 22638179 := bstep (se 1 (by rfl) ⟨16978634, by rfl⟩ : syracuseStep 22638179 = 33957269) B33957269
theorem B15092119 : Blo 2009435 15092119 := bstep (se 1 (by rfl) ⟨11319089, by rfl⟩ : syracuseStep 15092119 = 22638179) B22638179
theorem B20122825 : Blo 2009435 20122825 := bstep (se 2 (by rfl) ⟨7546059, by rfl⟩ : syracuseStep 20122825 = 15092119) B15092119
theorem B26830433 : Blo 2009435 26830433 := bstep (se 2 (by rfl) ⟨10061412, by rfl⟩ : syracuseStep 26830433 = 20122825) B20122825
theorem B17886955 : Blo 2009435 17886955 := bstep (se 1 (by rfl) ⟨13415216, by rfl⟩ : syracuseStep 17886955 = 26830433) B26830433
theorem B23849273 : Blo 2009435 23849273 := bstep (se 2 (by rfl) ⟨8943477, by rfl⟩ : syracuseStep 23849273 = 17886955) B17886955
theorem B63598061 : Blo 2009435 63598061 := bstep (se 3 (by rfl) ⟨11924636, by rfl⟩ : syracuseStep 63598061 = 23849273) B23849273
theorem B169594829 : Blo 2009435 169594829 := bstep (se 3 (by rfl) ⟨31799030, by rfl⟩ : syracuseStep 169594829 = 63598061) B63598061
theorem B113063219 : Blo 2009435 113063219 := bstep (se 1 (by rfl) ⟨84797414, by rfl⟩ : syracuseStep 113063219 = 169594829) B169594829
theorem B75375479 : Blo 2009435 75375479 := bstep (se 1 (by rfl) ⟨56531609, by rfl⟩ : syracuseStep 75375479 = 113063219) B113063219
theorem B201001277 : Blo 2009435 201001277 := bstep (se 3 (by rfl) ⟨37687739, by rfl⟩ : syracuseStep 201001277 = 75375479) B75375479
theorem B134000851 : Blo 2009435 134000851 := bstep (se 1 (by rfl) ⟨100500638, by rfl⟩ : syracuseStep 134000851 = 201001277) B201001277
theorem B178667801 : Blo 2009435 178667801 := bstep (se 2 (by rfl) ⟨67000425, by rfl⟩ : syracuseStep 178667801 = 134000851) B134000851
theorem B119111867 : Blo 2009435 119111867 := bstep (se 1 (by rfl) ⟨89333900, by rfl⟩ : syracuseStep 119111867 = 178667801) B178667801
theorem B79407911 : Blo 2009435 79407911 := bstep (se 1 (by rfl) ⟨59555933, by rfl⟩ : syracuseStep 79407911 = 119111867) B119111867
theorem B211754429 : Blo 2009435 211754429 := bstep (se 3 (by rfl) ⟨39703955, by rfl⟩ : syracuseStep 211754429 = 79407911) B79407911
theorem B141169619 : Blo 2009435 141169619 := bstep (se 1 (by rfl) ⟨105877214, by rfl⟩ : syracuseStep 141169619 = 211754429) B211754429
theorem B94113079 : Blo 2009435 94113079 := bstep (se 1 (by rfl) ⟨70584809, by rfl⟩ : syracuseStep 94113079 = 141169619) B141169619
theorem B501936421 : Blo 2009435 501936421 := bstep (se 4 (by rfl) ⟨47056539, by rfl⟩ : syracuseStep 501936421 = 94113079) B94113079
theorem B669248561 : Blo 2009435 669248561 := bstep (se 2 (by rfl) ⟨250968210, by rfl⟩ : syracuseStep 669248561 = 501936421) B501936421
theorem B446165707 : Blo 2009435 446165707 := bstep (se 1 (by rfl) ⟨334624280, by rfl⟩ : syracuseStep 446165707 = 669248561) B669248561
theorem B594887609 : Blo 2009435 594887609 := bstep (se 2 (by rfl) ⟨223082853, by rfl⟩ : syracuseStep 594887609 = 446165707) B446165707
theorem B1586366957 : Blo 2009435 1586366957 := bstep (se 3 (by rfl) ⟨297443804, by rfl⟩ : syracuseStep 1586366957 = 594887609) B594887609
theorem B1057577971 : Blo 2009435 1057577971 := bstep (se 1 (by rfl) ⟨793183478, by rfl⟩ : syracuseStep 1057577971 = 1586366957) B1586366957
theorem B1410103961 : Blo 2009435 1410103961 := bstep (se 2 (by rfl) ⟨528788985, by rfl⟩ : syracuseStep 1410103961 = 1057577971) B1057577971
theorem B940069307 : Blo 2009435 940069307 := bstep (se 1 (by rfl) ⟨705051980, by rfl⟩ : syracuseStep 940069307 = 1410103961) B1410103961
theorem B626712871 : Blo 2009435 626712871 := bstep (se 1 (by rfl) ⟨470034653, by rfl⟩ : syracuseStep 626712871 = 940069307) B940069307
theorem B835617161 : Blo 2009435 835617161 := bstep (se 2 (by rfl) ⟨313356435, by rfl⟩ : syracuseStep 835617161 = 626712871) B626712871
theorem B557078107 : Blo 2009435 557078107 := bstep (se 1 (by rfl) ⟨417808580, by rfl⟩ : syracuseStep 557078107 = 835617161) B835617161
theorem B742770809 : Blo 2009435 742770809 := bstep (se 2 (by rfl) ⟨278539053, by rfl⟩ : syracuseStep 742770809 = 557078107) B557078107
theorem B495180539 : Blo 2009435 495180539 := bstep (se 1 (by rfl) ⟨371385404, by rfl⟩ : syracuseStep 495180539 = 742770809) B742770809
theorem B330120359 : Blo 2009435 330120359 := bstep (se 1 (by rfl) ⟨247590269, by rfl⟩ : syracuseStep 330120359 = 495180539) B495180539
theorem B220080239 : Blo 2009435 220080239 := bstep (se 1 (by rfl) ⟨165060179, by rfl⟩ : syracuseStep 220080239 = 330120359) B330120359
theorem B146720159 : Blo 2009435 146720159 := bstep (se 1 (by rfl) ⟨110040119, by rfl⟩ : syracuseStep 146720159 = 220080239) B220080239
theorem B97813439 : Blo 2009435 97813439 := bstep (se 1 (by rfl) ⟨73360079, by rfl⟩ : syracuseStep 97813439 = 146720159) B146720159
theorem B65208959 : Blo 2009435 65208959 := bstep (se 1 (by rfl) ⟨48906719, by rfl⟩ : syracuseStep 65208959 = 97813439) B97813439
theorem B43472639 : Blo 2009435 43472639 := bstep (se 1 (by rfl) ⟨32604479, by rfl⟩ : syracuseStep 43472639 = 65208959) B65208959
theorem B28981759 : Blo 2009435 28981759 := bstep (se 1 (by rfl) ⟨21736319, by rfl⟩ : syracuseStep 28981759 = 43472639) B43472639
theorem B38642345 : Blo 2009435 38642345 := bstep (se 2 (by rfl) ⟨14490879, by rfl⟩ : syracuseStep 38642345 = 28981759) B28981759
theorem B25761563 : Blo 2009435 25761563 := bstep (se 1 (by rfl) ⟨19321172, by rfl⟩ : syracuseStep 25761563 = 38642345) B38642345
theorem B17174375 : Blo 2009435 17174375 := bstep (se 1 (by rfl) ⟨12880781, by rfl⟩ : syracuseStep 17174375 = 25761563) B25761563
theorem B11449583 : Blo 2009435 11449583 := bstep (se 1 (by rfl) ⟨8587187, by rfl⟩ : syracuseStep 11449583 = 17174375) B17174375
theorem B7633055 : Blo 2009435 7633055 := bstep (se 1 (by rfl) ⟨5724791, by rfl⟩ : syracuseStep 7633055 = 11449583) B11449583
theorem B5088703 : Blo 2009435 5088703 := bstep (se 1 (by rfl) ⟨3816527, by rfl⟩ : syracuseStep 5088703 = 7633055) B7633055
theorem B6784937 : Blo 2009435 6784937 := bstep (se 2 (by rfl) ⟨2544351, by rfl⟩ : syracuseStep 6784937 = 5088703) B5088703
theorem B4523291 : Blo 2009435 4523291 := bstep (se 1 (by rfl) ⟨3392468, by rfl⟩ : syracuseStep 4523291 = 6784937) B6784937
theorem B3015527 : Blo 2009435 3015527 := bstep (se 1 (by rfl) ⟨2261645, by rfl⟩ : syracuseStep 3015527 = 4523291) B4523291
theorem B2010351 : Blo 2009435 2010351 := bstep (se 1 (by rfl) ⟨1507763, by rfl⟩ : syracuseStep 2010351 = 3015527) B3015527
theorem B3015533 : Blo 2009435 3015533 := bbase (se 3 (by rfl) ⟨565412, by rfl⟩ : syracuseStep 3015533 = 1130825) (by norm_num)
theorem B2010355 : Blo 2009435 2010355 := bstep (se 1 (by rfl) ⟨1507766, by rfl⟩ : syracuseStep 2010355 = 3015533) B3015533
theorem B4523309 : Blo 2009435 4523309 := bbase (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) (by norm_num)
theorem B3015539 : Blo 2009435 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B2010359 : Blo 2009435 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B2448113 : Blo 2009435 2448113 := bbase (se 2 (by rfl) ⟨918042, by rfl⟩ : syracuseStep 2448113 = 1836085) (by norm_num)
theorem B26113205 : Blo 2009435 26113205 := bstep (se 5 (by rfl) ⟨1224056, by rfl⟩ : syracuseStep 26113205 = 2448113) B2448113
theorem B17408803 : Blo 2009435 17408803 := bstep (se 1 (by rfl) ⟨13056602, by rfl⟩ : syracuseStep 17408803 = 26113205) B26113205
theorem B23211737 : Blo 2009435 23211737 := bstep (se 2 (by rfl) ⟨8704401, by rfl⟩ : syracuseStep 23211737 = 17408803) B17408803
theorem B15474491 : Blo 2009435 15474491 := bstep (se 1 (by rfl) ⟨11605868, by rfl⟩ : syracuseStep 15474491 = 23211737) B23211737
theorem B10316327 : Blo 2009435 10316327 := bstep (se 1 (by rfl) ⟨7737245, by rfl⟩ : syracuseStep 10316327 = 15474491) B15474491
theorem B27510205 : Blo 2009435 27510205 := bstep (se 3 (by rfl) ⟨5158163, by rfl⟩ : syracuseStep 27510205 = 10316327) B10316327
theorem B36680273 : Blo 2009435 36680273 := bstep (se 2 (by rfl) ⟨13755102, by rfl⟩ : syracuseStep 36680273 = 27510205) B27510205
theorem B24453515 : Blo 2009435 24453515 := bstep (se 1 (by rfl) ⟨18340136, by rfl⟩ : syracuseStep 24453515 = 36680273) B36680273
theorem B16302343 : Blo 2009435 16302343 := bstep (se 1 (by rfl) ⟨12226757, by rfl⟩ : syracuseStep 16302343 = 24453515) B24453515
theorem B21736457 : Blo 2009435 21736457 := bstep (se 2 (by rfl) ⟨8151171, by rfl⟩ : syracuseStep 21736457 = 16302343) B16302343
theorem B14490971 : Blo 2009435 14490971 := bstep (se 1 (by rfl) ⟨10868228, by rfl⟩ : syracuseStep 14490971 = 21736457) B21736457
theorem B9660647 : Blo 2009435 9660647 := bstep (se 1 (by rfl) ⟨7245485, by rfl⟩ : syracuseStep 9660647 = 14490971) B14490971
theorem B6440431 : Blo 2009435 6440431 := bstep (se 1 (by rfl) ⟨4830323, by rfl⟩ : syracuseStep 6440431 = 9660647) B9660647
theorem B8587241 : Blo 2009435 8587241 := bstep (se 2 (by rfl) ⟨3220215, by rfl⟩ : syracuseStep 8587241 = 6440431) B6440431
theorem B5724827 : Blo 2009435 5724827 := bstep (se 1 (by rfl) ⟨4293620, by rfl⟩ : syracuseStep 5724827 = 8587241) B8587241
theorem B3816551 : Blo 2009435 3816551 := bstep (se 1 (by rfl) ⟨2862413, by rfl⟩ : syracuseStep 3816551 = 5724827) B5724827
theorem B2544367 : Blo 2009435 2544367 := bstep (se 1 (by rfl) ⟨1908275, by rfl⟩ : syracuseStep 2544367 = 3816551) B3816551
theorem B3392489 : Blo 2009435 3392489 := bstep (se 2 (by rfl) ⟨1272183, by rfl⟩ : syracuseStep 3392489 = 2544367) B2544367
theorem B2261659 : Blo 2009435 2261659 := bstep (se 1 (by rfl) ⟨1696244, by rfl⟩ : syracuseStep 2261659 = 3392489) B3392489
theorem B3015545 : Blo 2009435 3015545 := bstep (se 2 (by rfl) ⟨1130829, by rfl⟩ : syracuseStep 3015545 = 2261659) B2261659
theorem B2010363 : Blo 2009435 2010363 := bstep (se 1 (by rfl) ⟨1507772, by rfl⟩ : syracuseStep 2010363 = 3015545) B3015545
theorem B2292521 : Blo 2009435 2292521 := bbase (se 2 (by rfl) ⟨859695, by rfl⟩ : syracuseStep 2292521 = 1719391) (by norm_num)
theorem B6113389 : Blo 2009435 6113389 := bstep (se 3 (by rfl) ⟨1146260, by rfl⟩ : syracuseStep 6113389 = 2292521) B2292521
theorem B8151185 : Blo 2009435 8151185 := bstep (se 2 (by rfl) ⟨3056694, by rfl⟩ : syracuseStep 8151185 = 6113389) B6113389
theorem B5434123 : Blo 2009435 5434123 := bstep (se 1 (by rfl) ⟨4075592, by rfl⟩ : syracuseStep 5434123 = 8151185) B8151185
theorem B7245497 : Blo 2009435 7245497 := bstep (se 2 (by rfl) ⟨2717061, by rfl⟩ : syracuseStep 7245497 = 5434123) B5434123
theorem B19321325 : Blo 2009435 19321325 := bstep (se 3 (by rfl) ⟨3622748, by rfl⟩ : syracuseStep 19321325 = 7245497) B7245497
theorem B12880883 : Blo 2009435 12880883 := bstep (se 1 (by rfl) ⟨9660662, by rfl⟩ : syracuseStep 12880883 = 19321325) B19321325
theorem B34349021 : Blo 2009435 34349021 := bstep (se 3 (by rfl) ⟨6440441, by rfl⟩ : syracuseStep 34349021 = 12880883) B12880883
theorem B22899347 : Blo 2009435 22899347 := bstep (se 1 (by rfl) ⟨17174510, by rfl⟩ : syracuseStep 22899347 = 34349021) B34349021
theorem B15266231 : Blo 2009435 15266231 := bstep (se 1 (by rfl) ⟨11449673, by rfl⟩ : syracuseStep 15266231 = 22899347) B22899347
theorem B10177487 : Blo 2009435 10177487 := bstep (se 1 (by rfl) ⟨7633115, by rfl⟩ : syracuseStep 10177487 = 15266231) B15266231
theorem B6784991 : Blo 2009435 6784991 := bstep (se 1 (by rfl) ⟨5088743, by rfl⟩ : syracuseStep 6784991 = 10177487) B10177487
theorem B4523327 : Blo 2009435 4523327 := bstep (se 1 (by rfl) ⟨3392495, by rfl⟩ : syracuseStep 4523327 = 6784991) B6784991
theorem B3015551 : Blo 2009435 3015551 := bstep (se 1 (by rfl) ⟨2261663, by rfl⟩ : syracuseStep 3015551 = 4523327) B4523327
theorem B2010367 : Blo 2009435 2010367 := bstep (se 1 (by rfl) ⟨1507775, by rfl⟩ : syracuseStep 2010367 = 3015551) B3015551
theorem B3015557 : Blo 2009435 3015557 := bbase (se 4 (by rfl) ⟨282708, by rfl⟩ : syracuseStep 3015557 = 565417) (by norm_num)
theorem B2010371 : Blo 2009435 2010371 := bstep (se 1 (by rfl) ⟨1507778, by rfl⟩ : syracuseStep 2010371 = 3015557) B3015557
theorem B3392509 : Blo 2009435 3392509 := bbase (se 3 (by rfl) ⟨636095, by rfl⟩ : syracuseStep 3392509 = 1272191) (by norm_num)
theorem B4523345 : Blo 2009435 4523345 := bstep (se 2 (by rfl) ⟨1696254, by rfl⟩ : syracuseStep 4523345 = 3392509) B3392509
theorem B3015563 : Blo 2009435 3015563 := bstep (se 1 (by rfl) ⟨2261672, by rfl⟩ : syracuseStep 3015563 = 4523345) B4523345
theorem B2010375 : Blo 2009435 2010375 := bstep (se 1 (by rfl) ⟨1507781, by rfl⟩ : syracuseStep 2010375 = 3015563) B3015563
theorem B2261677 : Blo 2009435 2261677 := bbase (se 3 (by rfl) ⟨424064, by rfl⟩ : syracuseStep 2261677 = 848129) (by norm_num)
theorem B3015569 : Blo 2009435 3015569 := bstep (se 2 (by rfl) ⟨1130838, by rfl⟩ : syracuseStep 3015569 = 2261677) B2261677
theorem B2010379 : Blo 2009435 2010379 := bstep (se 1 (by rfl) ⟨1507784, by rfl⟩ : syracuseStep 2010379 = 3015569) B3015569
theorem B6785045 : Blo 2009435 6785045 := bbase (se 6 (by rfl) ⟨159024, by rfl⟩ : syracuseStep 6785045 = 318049) (by norm_num)
theorem B4523363 : Blo 2009435 4523363 := bstep (se 1 (by rfl) ⟨3392522, by rfl⟩ : syracuseStep 4523363 = 6785045) B6785045
theorem B3015575 : Blo 2009435 3015575 := bstep (se 1 (by rfl) ⟨2261681, by rfl⟩ : syracuseStep 3015575 = 4523363) B4523363
theorem B2010383 : Blo 2009435 2010383 := bstep (se 1 (by rfl) ⟨1507787, by rfl⟩ : syracuseStep 2010383 = 3015575) B3015575
theorem B3015581 : Blo 2009435 3015581 := bbase (se 3 (by rfl) ⟨565421, by rfl⟩ : syracuseStep 3015581 = 1130843) (by norm_num)
theorem B2010387 : Blo 2009435 2010387 := bstep (se 1 (by rfl) ⟨1507790, by rfl⟩ : syracuseStep 2010387 = 3015581) B3015581
theorem B4523381 : Blo 2009435 4523381 := bbase (se 5 (by rfl) ⟨212033, by rfl⟩ : syracuseStep 4523381 = 424067) (by norm_num)
theorem B3015587 : Blo 2009435 3015587 := bstep (se 1 (by rfl) ⟨2261690, by rfl⟩ : syracuseStep 3015587 = 4523381) B4523381
theorem B2010391 : Blo 2009435 2010391 := bstep (se 1 (by rfl) ⟨1507793, by rfl⟩ : syracuseStep 2010391 = 3015587) B3015587
theorem B17409077 : Blo 2009435 17409077 := bbase (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) (by norm_num)
theorem B11606051 : Blo 2009435 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B7737367 : Blo 2009435 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B10316489 : Blo 2009435 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B110042549 : Blo 2009435 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B73361699 : Blo 2009435 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B48907799 : Blo 2009435 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B32605199 : Blo 2009435 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B21736799 : Blo 2009435 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B14491199 : Blo 2009435 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B9660799 : Blo 2009435 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B12881065 : Blo 2009435 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B17174753 : Blo 2009435 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B11449835 : Blo 2009435 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B7633223 : Blo 2009435 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B5088815 : Blo 2009435 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B3392543 : Blo 2009435 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B2261695 : Blo 2009435 2261695 := bstep (se 1 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 2261695 = 3392543) B3392543
theorem B3015593 : Blo 2009435 3015593 := bstep (se 2 (by rfl) ⟨1130847, by rfl⟩ : syracuseStep 3015593 = 2261695) B2261695
theorem B2010395 : Blo 2009435 2010395 := bstep (se 1 (by rfl) ⟨1507796, by rfl⟩ : syracuseStep 2010395 = 3015593) B3015593
theorem B7633237 : Blo 2009435 7633237 := bbase (se 10 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 7633237 = 22363) (by norm_num)
theorem B10177649 : Blo 2009435 10177649 := bstep (se 2 (by rfl) ⟨3816618, by rfl⟩ : syracuseStep 10177649 = 7633237) B7633237
theorem B6785099 : Blo 2009435 6785099 := bstep (se 1 (by rfl) ⟨5088824, by rfl⟩ : syracuseStep 6785099 = 10177649) B10177649
theorem B4523399 : Blo 2009435 4523399 := bstep (se 1 (by rfl) ⟨3392549, by rfl⟩ : syracuseStep 4523399 = 6785099) B6785099
theorem B3015599 : Blo 2009435 3015599 := bstep (se 1 (by rfl) ⟨2261699, by rfl⟩ : syracuseStep 3015599 = 4523399) B4523399
theorem B2010399 : Blo 2009435 2010399 := bstep (se 1 (by rfl) ⟨1507799, by rfl⟩ : syracuseStep 2010399 = 3015599) B3015599
theorem B3015605 : Blo 2009435 3015605 := bbase (se 5 (by rfl) ⟨141356, by rfl⟩ : syracuseStep 3015605 = 282713) (by norm_num)
theorem B2010403 : Blo 2009435 2010403 := bstep (se 1 (by rfl) ⟨1507802, by rfl⟩ : syracuseStep 2010403 = 3015605) B3015605
theorem B5088845 : Blo 2009435 5088845 := bbase (se 3 (by rfl) ⟨954158, by rfl⟩ : syracuseStep 5088845 = 1908317) (by norm_num)
theorem B3392563 : Blo 2009435 3392563 := bstep (se 1 (by rfl) ⟨2544422, by rfl⟩ : syracuseStep 3392563 = 5088845) B5088845
theorem B4523417 : Blo 2009435 4523417 := bstep (se 2 (by rfl) ⟨1696281, by rfl⟩ : syracuseStep 4523417 = 3392563) B3392563
theorem B3015611 : Blo 2009435 3015611 := bstep (se 1 (by rfl) ⟨2261708, by rfl⟩ : syracuseStep 3015611 = 4523417) B4523417
theorem B2010407 : Blo 2009435 2010407 := bstep (se 1 (by rfl) ⟨1507805, by rfl⟩ : syracuseStep 2010407 = 3015611) B3015611
theorem B2261713 : Blo 2009435 2261713 := bbase (se 2 (by rfl) ⟨848142, by rfl⟩ : syracuseStep 2261713 = 1696285) (by norm_num)
theorem B3015617 : Blo 2009435 3015617 := bstep (se 2 (by rfl) ⟨1130856, by rfl⟩ : syracuseStep 3015617 = 2261713) B2261713
theorem B2010411 : Blo 2009435 2010411 := bstep (se 1 (by rfl) ⟨1507808, by rfl⟩ : syracuseStep 2010411 = 3015617) B3015617
theorem B6440597 : Blo 2009435 6440597 := bbase (se 6 (by rfl) ⟨150951, by rfl⟩ : syracuseStep 6440597 = 301903) (by norm_num)
theorem B4293731 : Blo 2009435 4293731 := bstep (se 1 (by rfl) ⟨3220298, by rfl⟩ : syracuseStep 4293731 = 6440597) B6440597
theorem B2862487 : Blo 2009435 2862487 := bstep (se 1 (by rfl) ⟨2146865, by rfl⟩ : syracuseStep 2862487 = 4293731) B4293731
theorem B3816649 : Blo 2009435 3816649 := bstep (se 2 (by rfl) ⟨1431243, by rfl⟩ : syracuseStep 3816649 = 2862487) B2862487
theorem B5088865 : Blo 2009435 5088865 := bstep (se 2 (by rfl) ⟨1908324, by rfl⟩ : syracuseStep 5088865 = 3816649) B3816649
theorem B6785153 : Blo 2009435 6785153 := bstep (se 2 (by rfl) ⟨2544432, by rfl⟩ : syracuseStep 6785153 = 5088865) B5088865
theorem B4523435 : Blo 2009435 4523435 := bstep (se 1 (by rfl) ⟨3392576, by rfl⟩ : syracuseStep 4523435 = 6785153) B6785153
theorem B3015623 : Blo 2009435 3015623 := bstep (se 1 (by rfl) ⟨2261717, by rfl⟩ : syracuseStep 3015623 = 4523435) B4523435
theorem B2010415 : Blo 2009435 2010415 := bstep (se 1 (by rfl) ⟨1507811, by rfl⟩ : syracuseStep 2010415 = 3015623) B3015623
theorem B3015629 : Blo 2009435 3015629 := bbase (se 3 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 3015629 = 1130861) (by norm_num)
theorem B2010419 : Blo 2009435 2010419 := bstep (se 1 (by rfl) ⟨1507814, by rfl⟩ : syracuseStep 2010419 = 3015629) B3015629
theorem B4523453 : Blo 2009435 4523453 := bbase (se 3 (by rfl) ⟨848147, by rfl⟩ : syracuseStep 4523453 = 1696295) (by norm_num)
theorem B3015635 : Blo 2009435 3015635 := bstep (se 1 (by rfl) ⟨2261726, by rfl⟩ : syracuseStep 3015635 = 4523453) B4523453
theorem B2010423 : Blo 2009435 2010423 := bstep (se 1 (by rfl) ⟨1507817, by rfl⟩ : syracuseStep 2010423 = 3015635) B3015635
theorem B3392597 : Blo 2009435 3392597 := bbase (se 8 (by rfl) ⟨19878, by rfl⟩ : syracuseStep 3392597 = 39757) (by norm_num)
theorem B2261731 : Blo 2009435 2261731 := bstep (se 1 (by rfl) ⟨1696298, by rfl⟩ : syracuseStep 2261731 = 3392597) B3392597
theorem B3015641 : Blo 2009435 3015641 := bstep (se 2 (by rfl) ⟨1130865, by rfl⟩ : syracuseStep 3015641 = 2261731) B2261731
theorem B2010427 : Blo 2009435 2010427 := bstep (se 1 (by rfl) ⟨1507820, by rfl⟩ : syracuseStep 2010427 = 3015641) B3015641
theorem B8151445 : Blo 2009435 8151445 := bbase (se 6 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 8151445 = 382099) (by norm_num)
theorem B10868593 : Blo 2009435 10868593 := bstep (se 2 (by rfl) ⟨4075722, by rfl⟩ : syracuseStep 10868593 = 8151445) B8151445
theorem B14491457 : Blo 2009435 14491457 := bstep (se 2 (by rfl) ⟨5434296, by rfl⟩ : syracuseStep 14491457 = 10868593) B10868593
theorem B9660971 : Blo 2009435 9660971 := bstep (se 1 (by rfl) ⟨7245728, by rfl⟩ : syracuseStep 9660971 = 14491457) B14491457
theorem B6440647 : Blo 2009435 6440647 := bstep (se 1 (by rfl) ⟨4830485, by rfl⟩ : syracuseStep 6440647 = 9660971) B9660971
theorem B8587529 : Blo 2009435 8587529 := bstep (se 2 (by rfl) ⟨3220323, by rfl⟩ : syracuseStep 8587529 = 6440647) B6440647
theorem B5725019 : Blo 2009435 5725019 := bstep (se 1 (by rfl) ⟨4293764, by rfl⟩ : syracuseStep 5725019 = 8587529) B8587529
theorem B15266717 : Blo 2009435 15266717 := bstep (se 3 (by rfl) ⟨2862509, by rfl⟩ : syracuseStep 15266717 = 5725019) B5725019
theorem B10177811 : Blo 2009435 10177811 := bstep (se 1 (by rfl) ⟨7633358, by rfl⟩ : syracuseStep 10177811 = 15266717) B15266717
theorem B6785207 : Blo 2009435 6785207 := bstep (se 1 (by rfl) ⟨5088905, by rfl⟩ : syracuseStep 6785207 = 10177811) B10177811
theorem B4523471 : Blo 2009435 4523471 := bstep (se 1 (by rfl) ⟨3392603, by rfl⟩ : syracuseStep 4523471 = 6785207) B6785207
theorem B3015647 : Blo 2009435 3015647 := bstep (se 1 (by rfl) ⟨2261735, by rfl⟩ : syracuseStep 3015647 = 4523471) B4523471
theorem B2010431 : Blo 2009435 2010431 := bstep (se 1 (by rfl) ⟨1507823, by rfl⟩ : syracuseStep 2010431 = 3015647) B3015647
theorem B3015653 : Blo 2009435 3015653 := bbase (se 4 (by rfl) ⟨282717, by rfl⟩ : syracuseStep 3015653 = 565435) (by norm_num)
theorem B2010435 : Blo 2009435 2010435 := bstep (se 1 (by rfl) ⟨1507826, by rfl⟩ : syracuseStep 2010435 = 3015653) B3015653
theorem B2415253 : Blo 2009435 2415253 := bbase (se 6 (by rfl) ⟨56607, by rfl⟩ : syracuseStep 2415253 = 113215) (by norm_num)
theorem B3220337 : Blo 2009435 3220337 := bstep (se 2 (by rfl) ⟨1207626, by rfl⟩ : syracuseStep 3220337 = 2415253) B2415253
theorem B8587565 : Blo 2009435 8587565 := bstep (se 3 (by rfl) ⟨1610168, by rfl⟩ : syracuseStep 8587565 = 3220337) B3220337
theorem B5725043 : Blo 2009435 5725043 := bstep (se 1 (by rfl) ⟨4293782, by rfl⟩ : syracuseStep 5725043 = 8587565) B8587565
theorem B3816695 : Blo 2009435 3816695 := bstep (se 1 (by rfl) ⟨2862521, by rfl⟩ : syracuseStep 3816695 = 5725043) B5725043
theorem B2544463 : Blo 2009435 2544463 := bstep (se 1 (by rfl) ⟨1908347, by rfl⟩ : syracuseStep 2544463 = 3816695) B3816695
theorem B3392617 : Blo 2009435 3392617 := bstep (se 2 (by rfl) ⟨1272231, by rfl⟩ : syracuseStep 3392617 = 2544463) B2544463
theorem B4523489 : Blo 2009435 4523489 := bstep (se 2 (by rfl) ⟨1696308, by rfl⟩ : syracuseStep 4523489 = 3392617) B3392617
theorem B3015659 : Blo 2009435 3015659 := bstep (se 1 (by rfl) ⟨2261744, by rfl⟩ : syracuseStep 3015659 = 4523489) B4523489
theorem B2010439 : Blo 2009435 2010439 := bstep (se 1 (by rfl) ⟨1507829, by rfl⟩ : syracuseStep 2010439 = 3015659) B3015659
theorem B2261749 : Blo 2009435 2261749 := bbase (se 5 (by rfl) ⟨106019, by rfl⟩ : syracuseStep 2261749 = 212039) (by norm_num)
theorem B3015665 : Blo 2009435 3015665 := bstep (se 2 (by rfl) ⟨1130874, by rfl⟩ : syracuseStep 3015665 = 2261749) B2261749
theorem B2010443 : Blo 2009435 2010443 := bstep (se 1 (by rfl) ⟨1507832, by rfl⟩ : syracuseStep 2010443 = 3015665) B3015665
theorem B2544473 : Blo 2009435 2544473 := bbase (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) (by norm_num)
theorem B6785261 : Blo 2009435 6785261 := bstep (se 3 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 6785261 = 2544473) B2544473
theorem B4523507 : Blo 2009435 4523507 := bstep (se 1 (by rfl) ⟨3392630, by rfl⟩ : syracuseStep 4523507 = 6785261) B6785261
theorem B3015671 : Blo 2009435 3015671 := bstep (se 1 (by rfl) ⟨2261753, by rfl⟩ : syracuseStep 3015671 = 4523507) B4523507
theorem B2010447 : Blo 2009435 2010447 := bstep (se 1 (by rfl) ⟨1507835, by rfl⟩ : syracuseStep 2010447 = 3015671) B3015671
theorem B3015677 : Blo 2009435 3015677 := bbase (se 3 (by rfl) ⟨565439, by rfl⟩ : syracuseStep 3015677 = 1130879) (by norm_num)
theorem B2010451 : Blo 2009435 2010451 := bstep (se 1 (by rfl) ⟨1507838, by rfl⟩ : syracuseStep 2010451 = 3015677) B3015677
theorem B4523525 : Blo 2009435 4523525 := bbase (se 4 (by rfl) ⟨424080, by rfl⟩ : syracuseStep 4523525 = 848161) (by norm_num)
theorem B3015683 : Blo 2009435 3015683 := bstep (se 1 (by rfl) ⟨2261762, by rfl⟩ : syracuseStep 3015683 = 4523525) B4523525
theorem B2010455 : Blo 2009435 2010455 := bstep (se 1 (by rfl) ⟨1507841, by rfl⟩ : syracuseStep 2010455 = 3015683) B3015683
theorem B3816733 : Blo 2009435 3816733 := bbase (se 3 (by rfl) ⟨715637, by rfl⟩ : syracuseStep 3816733 = 1431275) (by norm_num)
theorem B5088977 : Blo 2009435 5088977 := bstep (se 2 (by rfl) ⟨1908366, by rfl⟩ : syracuseStep 5088977 = 3816733) B3816733
theorem B3392651 : Blo 2009435 3392651 := bstep (se 1 (by rfl) ⟨2544488, by rfl⟩ : syracuseStep 3392651 = 5088977) B5088977
theorem B2261767 : Blo 2009435 2261767 := bstep (se 1 (by rfl) ⟨1696325, by rfl⟩ : syracuseStep 2261767 = 3392651) B3392651
theorem B3015689 : Blo 2009435 3015689 := bstep (se 2 (by rfl) ⟨1130883, by rfl⟩ : syracuseStep 3015689 = 2261767) B2261767
theorem B2010459 : Blo 2009435 2010459 := bstep (se 1 (by rfl) ⟨1507844, by rfl⟩ : syracuseStep 2010459 = 3015689) B3015689
theorem B10177973 : Blo 2009435 10177973 := bbase (se 5 (by rfl) ⟨477092, by rfl⟩ : syracuseStep 10177973 = 954185) (by norm_num)
theorem B6785315 : Blo 2009435 6785315 := bstep (se 1 (by rfl) ⟨5088986, by rfl⟩ : syracuseStep 6785315 = 10177973) B10177973
theorem B4523543 : Blo 2009435 4523543 := bstep (se 1 (by rfl) ⟨3392657, by rfl⟩ : syracuseStep 4523543 = 6785315) B6785315
theorem B3015695 : Blo 2009435 3015695 := bstep (se 1 (by rfl) ⟨2261771, by rfl⟩ : syracuseStep 3015695 = 4523543) B4523543
theorem B2010463 : Blo 2009435 2010463 := bstep (se 1 (by rfl) ⟨1507847, by rfl⟩ : syracuseStep 2010463 = 3015695) B3015695
theorem B3015701 : Blo 2009435 3015701 := bbase (se 6 (by rfl) ⟨70680, by rfl⟩ : syracuseStep 3015701 = 141361) (by norm_num)
theorem B2010467 : Blo 2009435 2010467 := bstep (se 1 (by rfl) ⟨1507850, by rfl⟩ : syracuseStep 2010467 = 3015701) B3015701
theorem B13057301 : Blo 2009435 13057301 := bbase (se 6 (by rfl) ⟨306030, by rfl⟩ : syracuseStep 13057301 = 612061) (by norm_num)
theorem B34819469 : Blo 2009435 34819469 := bstep (se 3 (by rfl) ⟨6528650, by rfl⟩ : syracuseStep 34819469 = 13057301) B13057301
theorem B23212979 : Blo 2009435 23212979 := bstep (se 1 (by rfl) ⟨17409734, by rfl⟩ : syracuseStep 23212979 = 34819469) B34819469
theorem B15475319 : Blo 2009435 15475319 := bstep (se 1 (by rfl) ⟨11606489, by rfl⟩ : syracuseStep 15475319 = 23212979) B23212979
theorem B10316879 : Blo 2009435 10316879 := bstep (se 1 (by rfl) ⟨7737659, by rfl⟩ : syracuseStep 10316879 = 15475319) B15475319
theorem B6877919 : Blo 2009435 6877919 := bstep (se 1 (by rfl) ⟨5158439, by rfl⟩ : syracuseStep 6877919 = 10316879) B10316879
theorem B18341117 : Blo 2009435 18341117 := bstep (se 3 (by rfl) ⟨3438959, by rfl⟩ : syracuseStep 18341117 = 6877919) B6877919
theorem B12227411 : Blo 2009435 12227411 := bstep (se 1 (by rfl) ⟨9170558, by rfl⟩ : syracuseStep 12227411 = 18341117) B18341117
theorem B8151607 : Blo 2009435 8151607 := bstep (se 1 (by rfl) ⟨6113705, by rfl⟩ : syracuseStep 8151607 = 12227411) B12227411
theorem B43475237 : Blo 2009435 43475237 := bstep (se 4 (by rfl) ⟨4075803, by rfl⟩ : syracuseStep 43475237 = 8151607) B8151607
theorem B28983491 : Blo 2009435 28983491 := bstep (se 1 (by rfl) ⟨21737618, by rfl⟩ : syracuseStep 28983491 = 43475237) B43475237
theorem B19322327 : Blo 2009435 19322327 := bstep (se 1 (by rfl) ⟨14491745, by rfl⟩ : syracuseStep 19322327 = 28983491) B28983491
theorem B12881551 : Blo 2009435 12881551 := bstep (se 1 (by rfl) ⟨9661163, by rfl⟩ : syracuseStep 12881551 = 19322327) B19322327
theorem B17175401 : Blo 2009435 17175401 := bstep (se 2 (by rfl) ⟨6440775, by rfl⟩ : syracuseStep 17175401 = 12881551) B12881551
theorem B11450267 : Blo 2009435 11450267 := bstep (se 1 (by rfl) ⟨8587700, by rfl⟩ : syracuseStep 11450267 = 17175401) B17175401
theorem B7633511 : Blo 2009435 7633511 := bstep (se 1 (by rfl) ⟨5725133, by rfl⟩ : syracuseStep 7633511 = 11450267) B11450267
theorem B5089007 : Blo 2009435 5089007 := bstep (se 1 (by rfl) ⟨3816755, by rfl⟩ : syracuseStep 5089007 = 7633511) B7633511
theorem B3392671 : Blo 2009435 3392671 := bstep (se 1 (by rfl) ⟨2544503, by rfl⟩ : syracuseStep 3392671 = 5089007) B5089007
theorem B4523561 : Blo 2009435 4523561 := bstep (se 2 (by rfl) ⟨1696335, by rfl⟩ : syracuseStep 4523561 = 3392671) B3392671
theorem B3015707 : Blo 2009435 3015707 := bstep (se 1 (by rfl) ⟨2261780, by rfl⟩ : syracuseStep 3015707 = 4523561) B4523561
theorem B2010471 : Blo 2009435 2010471 := bstep (se 1 (by rfl) ⟨1507853, by rfl⟩ : syracuseStep 2010471 = 3015707) B3015707
theorem B2261785 : Blo 2009435 2261785 := bbase (se 2 (by rfl) ⟨848169, by rfl⟩ : syracuseStep 2261785 = 1696339) (by norm_num)
theorem B3015713 : Blo 2009435 3015713 := bstep (se 2 (by rfl) ⟨1130892, by rfl⟩ : syracuseStep 3015713 = 2261785) B2261785
theorem B2010475 : Blo 2009435 2010475 := bstep (se 1 (by rfl) ⟨1507856, by rfl⟩ : syracuseStep 2010475 = 3015713) B3015713
theorem B7633541 : Blo 2009435 7633541 := bbase (se 4 (by rfl) ⟨715644, by rfl⟩ : syracuseStep 7633541 = 1431289) (by norm_num)
theorem B5089027 : Blo 2009435 5089027 := bstep (se 1 (by rfl) ⟨3816770, by rfl⟩ : syracuseStep 5089027 = 7633541) B7633541
theorem B6785369 : Blo 2009435 6785369 := bstep (se 2 (by rfl) ⟨2544513, by rfl⟩ : syracuseStep 6785369 = 5089027) B5089027
theorem B4523579 : Blo 2009435 4523579 := bstep (se 1 (by rfl) ⟨3392684, by rfl⟩ : syracuseStep 4523579 = 6785369) B6785369
theorem B3015719 : Blo 2009435 3015719 := bstep (se 1 (by rfl) ⟨2261789, by rfl⟩ : syracuseStep 3015719 = 4523579) B4523579
theorem B2010479 : Blo 2009435 2010479 := bstep (se 1 (by rfl) ⟨1507859, by rfl⟩ : syracuseStep 2010479 = 3015719) B3015719
theorem B3015725 : Blo 2009435 3015725 := bbase (se 3 (by rfl) ⟨565448, by rfl⟩ : syracuseStep 3015725 = 1130897) (by norm_num)
theorem B2010483 : Blo 2009435 2010483 := bstep (se 1 (by rfl) ⟨1507862, by rfl⟩ : syracuseStep 2010483 = 3015725) B3015725
theorem B4523597 : Blo 2009435 4523597 := bbase (se 3 (by rfl) ⟨848174, by rfl⟩ : syracuseStep 4523597 = 1696349) (by norm_num)
theorem B3015731 : Blo 2009435 3015731 := bstep (se 1 (by rfl) ⟨2261798, by rfl⟩ : syracuseStep 3015731 = 4523597) B4523597
theorem B2010487 : Blo 2009435 2010487 := bstep (se 1 (by rfl) ⟨1507865, by rfl⟩ : syracuseStep 2010487 = 3015731) B3015731
theorem B2544529 : Blo 2009435 2544529 := bbase (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) (by norm_num)
theorem B3392705 : Blo 2009435 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B2261803 : Blo 2009435 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B3015737 : Blo 2009435 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B2010491 : Blo 2009435 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B4293901 : Blo 2009435 4293901 := bbase (se 3 (by rfl) ⟨805106, by rfl⟩ : syracuseStep 4293901 = 1610213) (by norm_num)
theorem B22900805 : Blo 2009435 22900805 := bstep (se 4 (by rfl) ⟨2146950, by rfl⟩ : syracuseStep 22900805 = 4293901) B4293901
theorem B15267203 : Blo 2009435 15267203 := bstep (se 1 (by rfl) ⟨11450402, by rfl⟩ : syracuseStep 15267203 = 22900805) B22900805
theorem B10178135 : Blo 2009435 10178135 := bstep (se 1 (by rfl) ⟨7633601, by rfl⟩ : syracuseStep 10178135 = 15267203) B15267203
theorem B6785423 : Blo 2009435 6785423 := bstep (se 1 (by rfl) ⟨5089067, by rfl⟩ : syracuseStep 6785423 = 10178135) B10178135
theorem B4523615 : Blo 2009435 4523615 := bstep (se 1 (by rfl) ⟨3392711, by rfl⟩ : syracuseStep 4523615 = 6785423) B6785423
theorem B3015743 : Blo 2009435 3015743 := bstep (se 1 (by rfl) ⟨2261807, by rfl⟩ : syracuseStep 3015743 = 4523615) B4523615
theorem B2010495 : Blo 2009435 2010495 := bstep (se 1 (by rfl) ⟨1507871, by rfl⟩ : syracuseStep 2010495 = 3015743) B3015743
theorem B3015749 : Blo 2009435 3015749 := bbase (se 4 (by rfl) ⟨282726, by rfl⟩ : syracuseStep 3015749 = 565453) (by norm_num)
theorem B2010499 : Blo 2009435 2010499 := bstep (se 1 (by rfl) ⟨1507874, by rfl⟩ : syracuseStep 2010499 = 3015749) B3015749
theorem B3392725 : Blo 2009435 3392725 := bbase (se 7 (by rfl) ⟨39758, by rfl⟩ : syracuseStep 3392725 = 79517) (by norm_num)
theorem B4523633 : Blo 2009435 4523633 := bstep (se 2 (by rfl) ⟨1696362, by rfl⟩ : syracuseStep 4523633 = 3392725) B3392725
theorem B3015755 : Blo 2009435 3015755 := bstep (se 1 (by rfl) ⟨2261816, by rfl⟩ : syracuseStep 3015755 = 4523633) B4523633
theorem B2010503 : Blo 2009435 2010503 := bstep (se 1 (by rfl) ⟨1507877, by rfl⟩ : syracuseStep 2010503 = 3015755) B3015755
theorem B2261821 : Blo 2009435 2261821 := bbase (se 3 (by rfl) ⟨424091, by rfl⟩ : syracuseStep 2261821 = 848183) (by norm_num)
theorem B3015761 : Blo 2009435 3015761 := bstep (se 2 (by rfl) ⟨1130910, by rfl⟩ : syracuseStep 3015761 = 2261821) B2261821
theorem B2010507 : Blo 2009435 2010507 := bstep (se 1 (by rfl) ⟨1507880, by rfl⟩ : syracuseStep 2010507 = 3015761) B3015761
theorem B6785477 : Blo 2009435 6785477 := bbase (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) (by norm_num)
theorem B4523651 : Blo 2009435 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B3015767 : Blo 2009435 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B2010511 : Blo 2009435 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B3015773 : Blo 2009435 3015773 := bbase (se 3 (by rfl) ⟨565457, by rfl⟩ : syracuseStep 3015773 = 1130915) (by norm_num)
theorem B2010515 : Blo 2009435 2010515 := bstep (se 1 (by rfl) ⟨1507886, by rfl⟩ : syracuseStep 2010515 = 3015773) B3015773
theorem B4523669 : Blo 2009435 4523669 := bbase (se 6 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 4523669 = 212047) (by norm_num)
theorem B3015779 : Blo 2009435 3015779 := bstep (se 1 (by rfl) ⟨2261834, by rfl⟩ : syracuseStep 3015779 = 4523669) B4523669
theorem B2010519 : Blo 2009435 2010519 := bstep (se 1 (by rfl) ⟨1507889, by rfl⟩ : syracuseStep 2010519 = 3015779) B3015779
theorem B2146981 : Blo 2009435 2146981 := bbase (se 4 (by rfl) ⟨201279, by rfl⟩ : syracuseStep 2146981 = 402559) (by norm_num)
theorem B2862641 : Blo 2009435 2862641 := bstep (se 2 (by rfl) ⟨1073490, by rfl⟩ : syracuseStep 2862641 = 2146981) B2146981
theorem B7633709 : Blo 2009435 7633709 := bstep (se 3 (by rfl) ⟨1431320, by rfl⟩ : syracuseStep 7633709 = 2862641) B2862641
theorem B5089139 : Blo 2009435 5089139 := bstep (se 1 (by rfl) ⟨3816854, by rfl⟩ : syracuseStep 5089139 = 7633709) B7633709
theorem B3392759 : Blo 2009435 3392759 := bstep (se 1 (by rfl) ⟨2544569, by rfl⟩ : syracuseStep 3392759 = 5089139) B5089139
theorem B2261839 : Blo 2009435 2261839 := bstep (se 1 (by rfl) ⟨1696379, by rfl⟩ : syracuseStep 2261839 = 3392759) B3392759
theorem B3015785 : Blo 2009435 3015785 := bstep (se 2 (by rfl) ⟨1130919, by rfl⟩ : syracuseStep 3015785 = 2261839) B2261839
theorem B2010523 : Blo 2009435 2010523 := bstep (se 1 (by rfl) ⟨1507892, by rfl⟩ : syracuseStep 2010523 = 3015785) B3015785
theorem B12881909 : Blo 2009435 12881909 := bbase (se 5 (by rfl) ⟨603839, by rfl⟩ : syracuseStep 12881909 = 1207679) (by norm_num)
theorem B8587939 : Blo 2009435 8587939 := bstep (se 1 (by rfl) ⟨6440954, by rfl⟩ : syracuseStep 8587939 = 12881909) B12881909
theorem B11450585 : Blo 2009435 11450585 := bstep (se 2 (by rfl) ⟨4293969, by rfl⟩ : syracuseStep 11450585 = 8587939) B8587939
theorem B7633723 : Blo 2009435 7633723 := bstep (se 1 (by rfl) ⟨5725292, by rfl⟩ : syracuseStep 7633723 = 11450585) B11450585
theorem B10178297 : Blo 2009435 10178297 := bstep (se 2 (by rfl) ⟨3816861, by rfl⟩ : syracuseStep 10178297 = 7633723) B7633723
theorem B6785531 : Blo 2009435 6785531 := bstep (se 1 (by rfl) ⟨5089148, by rfl⟩ : syracuseStep 6785531 = 10178297) B10178297
theorem B4523687 : Blo 2009435 4523687 := bstep (se 1 (by rfl) ⟨3392765, by rfl⟩ : syracuseStep 4523687 = 6785531) B6785531
theorem B3015791 : Blo 2009435 3015791 := bstep (se 1 (by rfl) ⟨2261843, by rfl⟩ : syracuseStep 3015791 = 4523687) B4523687
theorem B2010527 : Blo 2009435 2010527 := bstep (se 1 (by rfl) ⟨1507895, by rfl⟩ : syracuseStep 2010527 = 3015791) B3015791
theorem B3015797 : Blo 2009435 3015797 := bbase (se 5 (by rfl) ⟨141365, by rfl⟩ : syracuseStep 3015797 = 282731) (by norm_num)
theorem B2010531 : Blo 2009435 2010531 := bstep (se 1 (by rfl) ⟨1507898, by rfl⟩ : syracuseStep 2010531 = 3015797) B3015797
theorem B3816877 : Blo 2009435 3816877 := bbase (se 3 (by rfl) ⟨715664, by rfl⟩ : syracuseStep 3816877 = 1431329) (by norm_num)
theorem B5089169 : Blo 2009435 5089169 := bstep (se 2 (by rfl) ⟨1908438, by rfl⟩ : syracuseStep 5089169 = 3816877) B3816877
theorem B3392779 : Blo 2009435 3392779 := bstep (se 1 (by rfl) ⟨2544584, by rfl⟩ : syracuseStep 3392779 = 5089169) B5089169
theorem B4523705 : Blo 2009435 4523705 := bstep (se 2 (by rfl) ⟨1696389, by rfl⟩ : syracuseStep 4523705 = 3392779) B3392779
theorem B3015803 : Blo 2009435 3015803 := bstep (se 1 (by rfl) ⟨2261852, by rfl⟩ : syracuseStep 3015803 = 4523705) B4523705
theorem B2010535 : Blo 2009435 2010535 := bstep (se 1 (by rfl) ⟨1507901, by rfl⟩ : syracuseStep 2010535 = 3015803) B3015803
theorem B2261857 : Blo 2009435 2261857 := bbase (se 2 (by rfl) ⟨848196, by rfl⟩ : syracuseStep 2261857 = 1696393) (by norm_num)
theorem B3015809 : Blo 2009435 3015809 := bstep (se 2 (by rfl) ⟨1130928, by rfl⟩ : syracuseStep 3015809 = 2261857) B2261857
theorem B2010539 : Blo 2009435 2010539 := bstep (se 1 (by rfl) ⟨1507904, by rfl⟩ : syracuseStep 2010539 = 3015809) B3015809
theorem B5089189 : Blo 2009435 5089189 := bbase (se 4 (by rfl) ⟨477111, by rfl⟩ : syracuseStep 5089189 = 954223) (by norm_num)
theorem B6785585 : Blo 2009435 6785585 := bstep (se 2 (by rfl) ⟨2544594, by rfl⟩ : syracuseStep 6785585 = 5089189) B5089189
theorem B4523723 : Blo 2009435 4523723 := bstep (se 1 (by rfl) ⟨3392792, by rfl⟩ : syracuseStep 4523723 = 6785585) B6785585
theorem B3015815 : Blo 2009435 3015815 := bstep (se 1 (by rfl) ⟨2261861, by rfl⟩ : syracuseStep 3015815 = 4523723) B4523723
theorem B2010543 : Blo 2009435 2010543 := bstep (se 1 (by rfl) ⟨1507907, by rfl⟩ : syracuseStep 2010543 = 3015815) B3015815
theorem B3015821 : Blo 2009435 3015821 := bbase (se 3 (by rfl) ⟨565466, by rfl⟩ : syracuseStep 3015821 = 1130933) (by norm_num)
theorem B2010547 : Blo 2009435 2010547 := bstep (se 1 (by rfl) ⟨1507910, by rfl⟩ : syracuseStep 2010547 = 3015821) B3015821
theorem B4523741 : Blo 2009435 4523741 := bbase (se 3 (by rfl) ⟨848201, by rfl⟩ : syracuseStep 4523741 = 1696403) (by norm_num)
theorem B3015827 : Blo 2009435 3015827 := bstep (se 1 (by rfl) ⟨2261870, by rfl⟩ : syracuseStep 3015827 = 4523741) B4523741
theorem B2010551 : Blo 2009435 2010551 := bstep (se 1 (by rfl) ⟨1507913, by rfl⟩ : syracuseStep 2010551 = 3015827) B3015827
theorem B3392813 : Blo 2009435 3392813 := bbase (se 3 (by rfl) ⟨636152, by rfl⟩ : syracuseStep 3392813 = 1272305) (by norm_num)
theorem B2261875 : Blo 2009435 2261875 := bstep (se 1 (by rfl) ⟨1696406, by rfl⟩ : syracuseStep 2261875 = 3392813) B3392813
theorem B3015833 : Blo 2009435 3015833 := bstep (se 2 (by rfl) ⟨1130937, by rfl⟩ : syracuseStep 3015833 = 2261875) B2261875
theorem B2010555 : Blo 2009435 2010555 := bstep (se 1 (by rfl) ⟨1507916, by rfl⟩ : syracuseStep 2010555 = 3015833) B3015833
theorem B2176313 : Blo 2009435 2176313 := bbase (se 2 (by rfl) ⟨816117, by rfl⟩ : syracuseStep 2176313 = 1632235) (by norm_num)
theorem B5803501 : Blo 2009435 5803501 := bstep (se 3 (by rfl) ⟨1088156, by rfl⟩ : syracuseStep 5803501 = 2176313) B2176313
theorem B7738001 : Blo 2009435 7738001 := bstep (se 2 (by rfl) ⟨2901750, by rfl⟩ : syracuseStep 7738001 = 5803501) B5803501
theorem B5158667 : Blo 2009435 5158667 := bstep (se 1 (by rfl) ⟨3869000, by rfl⟩ : syracuseStep 5158667 = 7738001) B7738001
theorem B3439111 : Blo 2009435 3439111 := bstep (se 1 (by rfl) ⟨2579333, by rfl⟩ : syracuseStep 3439111 = 5158667) B5158667
theorem B4585481 : Blo 2009435 4585481 := bstep (se 2 (by rfl) ⟨1719555, by rfl⟩ : syracuseStep 4585481 = 3439111) B3439111
theorem B3056987 : Blo 2009435 3056987 := bstep (se 1 (by rfl) ⟨2292740, by rfl⟩ : syracuseStep 3056987 = 4585481) B4585481
theorem B2037991 : Blo 2009435 2037991 := bstep (se 1 (by rfl) ⟨1528493, by rfl⟩ : syracuseStep 2037991 = 3056987) B3056987
theorem B2717321 : Blo 2009435 2717321 := bstep (se 2 (by rfl) ⟨1018995, by rfl⟩ : syracuseStep 2717321 = 2037991) B2037991
theorem B7246189 : Blo 2009435 7246189 := bstep (se 3 (by rfl) ⟨1358660, by rfl⟩ : syracuseStep 7246189 = 2717321) B2717321
theorem B38646341 : Blo 2009435 38646341 := bstep (se 4 (by rfl) ⟨3623094, by rfl⟩ : syracuseStep 38646341 = 7246189) B7246189
theorem B25764227 : Blo 2009435 25764227 := bstep (se 1 (by rfl) ⟨19323170, by rfl⟩ : syracuseStep 25764227 = 38646341) B38646341
theorem B17176151 : Blo 2009435 17176151 := bstep (se 1 (by rfl) ⟨12882113, by rfl⟩ : syracuseStep 17176151 = 25764227) B25764227
theorem B11450767 : Blo 2009435 11450767 := bstep (se 1 (by rfl) ⟨8588075, by rfl⟩ : syracuseStep 11450767 = 17176151) B17176151
theorem B15267689 : Blo 2009435 15267689 := bstep (se 2 (by rfl) ⟨5725383, by rfl⟩ : syracuseStep 15267689 = 11450767) B11450767
theorem B10178459 : Blo 2009435 10178459 := bstep (se 1 (by rfl) ⟨7633844, by rfl⟩ : syracuseStep 10178459 = 15267689) B15267689
theorem B6785639 : Blo 2009435 6785639 := bstep (se 1 (by rfl) ⟨5089229, by rfl⟩ : syracuseStep 6785639 = 10178459) B10178459
theorem B4523759 : Blo 2009435 4523759 := bstep (se 1 (by rfl) ⟨3392819, by rfl⟩ : syracuseStep 4523759 = 6785639) B6785639
theorem B3015839 : Blo 2009435 3015839 := bstep (se 1 (by rfl) ⟨2261879, by rfl⟩ : syracuseStep 3015839 = 4523759) B4523759
theorem B2010559 : Blo 2009435 2010559 := bstep (se 1 (by rfl) ⟨1507919, by rfl⟩ : syracuseStep 2010559 = 3015839) B3015839
theorem B3015845 : Blo 2009435 3015845 := bbase (se 4 (by rfl) ⟨282735, by rfl⟩ : syracuseStep 3015845 = 565471) (by norm_num)
theorem B2010563 : Blo 2009435 2010563 := bstep (se 1 (by rfl) ⟨1507922, by rfl⟩ : syracuseStep 2010563 = 3015845) B3015845
theorem B2544625 : Blo 2009435 2544625 := bbase (se 2 (by rfl) ⟨954234, by rfl⟩ : syracuseStep 2544625 = 1908469) (by norm_num)
theorem B3392833 : Blo 2009435 3392833 := bstep (se 2 (by rfl) ⟨1272312, by rfl⟩ : syracuseStep 3392833 = 2544625) B2544625
theorem B4523777 : Blo 2009435 4523777 := bstep (se 2 (by rfl) ⟨1696416, by rfl⟩ : syracuseStep 4523777 = 3392833) B3392833
theorem B3015851 : Blo 2009435 3015851 := bstep (se 1 (by rfl) ⟨2261888, by rfl⟩ : syracuseStep 3015851 = 4523777) B4523777
theorem B2010567 : Blo 2009435 2010567 := bstep (se 1 (by rfl) ⟨1507925, by rfl⟩ : syracuseStep 2010567 = 3015851) B3015851
theorem B2261893 : Blo 2009435 2261893 := bbase (se 4 (by rfl) ⟨212052, by rfl⟩ : syracuseStep 2261893 = 424105) (by norm_num)
theorem B3015857 : Blo 2009435 3015857 := bstep (se 2 (by rfl) ⟨1130946, by rfl⟩ : syracuseStep 3015857 = 2261893) B2261893
theorem B2010571 : Blo 2009435 2010571 := bstep (se 1 (by rfl) ⟨1507928, by rfl⟩ : syracuseStep 2010571 = 3015857) B3015857
theorem B3623125 : Blo 2009435 3623125 := bbase (se 7 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 3623125 = 84917) (by norm_num)
theorem B4830833 : Blo 2009435 4830833 := bstep (se 2 (by rfl) ⟨1811562, by rfl⟩ : syracuseStep 4830833 = 3623125) B3623125
theorem B3220555 : Blo 2009435 3220555 := bstep (se 1 (by rfl) ⟨2415416, by rfl⟩ : syracuseStep 3220555 = 4830833) B4830833
theorem B4294073 : Blo 2009435 4294073 := bstep (se 2 (by rfl) ⟨1610277, by rfl⟩ : syracuseStep 4294073 = 3220555) B3220555
theorem B2862715 : Blo 2009435 2862715 := bstep (se 1 (by rfl) ⟨2147036, by rfl⟩ : syracuseStep 2862715 = 4294073) B4294073
theorem B3816953 : Blo 2009435 3816953 := bstep (se 2 (by rfl) ⟨1431357, by rfl⟩ : syracuseStep 3816953 = 2862715) B2862715
theorem B2544635 : Blo 2009435 2544635 := bstep (se 1 (by rfl) ⟨1908476, by rfl⟩ : syracuseStep 2544635 = 3816953) B3816953
theorem B6785693 : Blo 2009435 6785693 := bstep (se 3 (by rfl) ⟨1272317, by rfl⟩ : syracuseStep 6785693 = 2544635) B2544635
theorem B4523795 : Blo 2009435 4523795 := bstep (se 1 (by rfl) ⟨3392846, by rfl⟩ : syracuseStep 4523795 = 6785693) B6785693
theorem B3015863 : Blo 2009435 3015863 := bstep (se 1 (by rfl) ⟨2261897, by rfl⟩ : syracuseStep 3015863 = 4523795) B4523795
theorem B2010575 : Blo 2009435 2010575 := bstep (se 1 (by rfl) ⟨1507931, by rfl⟩ : syracuseStep 2010575 = 3015863) B3015863
theorem B3015869 : Blo 2009435 3015869 := bbase (se 3 (by rfl) ⟨565475, by rfl⟩ : syracuseStep 3015869 = 1130951) (by norm_num)
theorem B2010579 : Blo 2009435 2010579 := bstep (se 1 (by rfl) ⟨1507934, by rfl⟩ : syracuseStep 2010579 = 3015869) B3015869
theorem B4523813 : Blo 2009435 4523813 := bbase (se 4 (by rfl) ⟨424107, by rfl⟩ : syracuseStep 4523813 = 848215) (by norm_num)
theorem B3015875 : Blo 2009435 3015875 := bstep (se 1 (by rfl) ⟨2261906, by rfl⟩ : syracuseStep 3015875 = 4523813) B4523813
theorem B2010583 : Blo 2009435 2010583 := bstep (se 1 (by rfl) ⟨1507937, by rfl⟩ : syracuseStep 2010583 = 3015875) B3015875
theorem B5089301 : Blo 2009435 5089301 := bbase (se 6 (by rfl) ⟨119280, by rfl⟩ : syracuseStep 5089301 = 238561) (by norm_num)
theorem B3392867 : Blo 2009435 3392867 := bstep (se 1 (by rfl) ⟨2544650, by rfl⟩ : syracuseStep 3392867 = 5089301) B5089301
theorem B2261911 : Blo 2009435 2261911 := bstep (se 1 (by rfl) ⟨1696433, by rfl⟩ : syracuseStep 2261911 = 3392867) B3392867
theorem B3015881 : Blo 2009435 3015881 := bstep (se 2 (by rfl) ⟨1130955, by rfl⟩ : syracuseStep 3015881 = 2261911) B2261911
theorem B2010587 : Blo 2009435 2010587 := bstep (se 1 (by rfl) ⟨1507940, by rfl⟩ : syracuseStep 2010587 = 3015881) B3015881
theorem B8588213 : Blo 2009435 8588213 := bbase (se 5 (by rfl) ⟨402572, by rfl⟩ : syracuseStep 8588213 = 805145) (by norm_num)
theorem B5725475 : Blo 2009435 5725475 := bstep (se 1 (by rfl) ⟨4294106, by rfl⟩ : syracuseStep 5725475 = 8588213) B8588213
theorem B3816983 : Blo 2009435 3816983 := bstep (se 1 (by rfl) ⟨2862737, by rfl⟩ : syracuseStep 3816983 = 5725475) B5725475
theorem B10178621 : Blo 2009435 10178621 := bstep (se 3 (by rfl) ⟨1908491, by rfl⟩ : syracuseStep 10178621 = 3816983) B3816983
theorem B6785747 : Blo 2009435 6785747 := bstep (se 1 (by rfl) ⟨5089310, by rfl⟩ : syracuseStep 6785747 = 10178621) B10178621
theorem B4523831 : Blo 2009435 4523831 := bstep (se 1 (by rfl) ⟨3392873, by rfl⟩ : syracuseStep 4523831 = 6785747) B6785747
theorem B3015887 : Blo 2009435 3015887 := bstep (se 1 (by rfl) ⟨2261915, by rfl⟩ : syracuseStep 3015887 = 4523831) B4523831
theorem B2010591 : Blo 2009435 2010591 := bstep (se 1 (by rfl) ⟨1507943, by rfl⟩ : syracuseStep 2010591 = 3015887) B3015887
theorem B3015893 : Blo 2009435 3015893 := bbase (se 7 (by rfl) ⟨35342, by rfl⟩ : syracuseStep 3015893 = 70685) (by norm_num)
theorem B2010595 : Blo 2009435 2010595 := bstep (se 1 (by rfl) ⟨1507946, by rfl⟩ : syracuseStep 2010595 = 3015893) B3015893
theorem B2862749 : Blo 2009435 2862749 := bbase (se 3 (by rfl) ⟨536765, by rfl⟩ : syracuseStep 2862749 = 1073531) (by norm_num)
theorem B7633997 : Blo 2009435 7633997 := bstep (se 3 (by rfl) ⟨1431374, by rfl⟩ : syracuseStep 7633997 = 2862749) B2862749
theorem B5089331 : Blo 2009435 5089331 := bstep (se 1 (by rfl) ⟨3816998, by rfl⟩ : syracuseStep 5089331 = 7633997) B7633997
theorem B3392887 : Blo 2009435 3392887 := bstep (se 1 (by rfl) ⟨2544665, by rfl⟩ : syracuseStep 3392887 = 5089331) B5089331
theorem B4523849 : Blo 2009435 4523849 := bstep (se 2 (by rfl) ⟨1696443, by rfl⟩ : syracuseStep 4523849 = 3392887) B3392887
theorem B3015899 : Blo 2009435 3015899 := bstep (se 1 (by rfl) ⟨2261924, by rfl⟩ : syracuseStep 3015899 = 4523849) B4523849
theorem B2010599 : Blo 2009435 2010599 := bstep (se 1 (by rfl) ⟨1507949, by rfl⟩ : syracuseStep 2010599 = 3015899) B3015899
theorem B2261929 : Blo 2009435 2261929 := bbase (se 2 (by rfl) ⟨848223, by rfl⟩ : syracuseStep 2261929 = 1696447) (by norm_num)
theorem B3015905 : Blo 2009435 3015905 := bstep (se 2 (by rfl) ⟨1130964, by rfl⟩ : syracuseStep 3015905 = 2261929) B2261929
theorem B2010603 : Blo 2009435 2010603 := bstep (se 1 (by rfl) ⟨1507952, by rfl⟩ : syracuseStep 2010603 = 3015905) B3015905
theorem B19854517 : Blo 2009435 19854517 := bbase (se 5 (by rfl) ⟨930680, by rfl⟩ : syracuseStep 19854517 = 1861361) (by norm_num)
theorem B26472689 : Blo 2009435 26472689 := bstep (se 2 (by rfl) ⟨9927258, by rfl⟩ : syracuseStep 26472689 = 19854517) B19854517
theorem B17648459 : Blo 2009435 17648459 := bstep (se 1 (by rfl) ⟨13236344, by rfl⟩ : syracuseStep 17648459 = 26472689) B26472689
theorem B11765639 : Blo 2009435 11765639 := bstep (se 1 (by rfl) ⟨8824229, by rfl⟩ : syracuseStep 11765639 = 17648459) B17648459
theorem B7843759 : Blo 2009435 7843759 := bstep (se 1 (by rfl) ⟨5882819, by rfl⟩ : syracuseStep 7843759 = 11765639) B11765639
theorem B41833381 : Blo 2009435 41833381 := bstep (se 4 (by rfl) ⟨3921879, by rfl⟩ : syracuseStep 41833381 = 7843759) B7843759
theorem B55777841 : Blo 2009435 55777841 := bstep (se 2 (by rfl) ⟨20916690, by rfl⟩ : syracuseStep 55777841 = 41833381) B41833381
theorem B37185227 : Blo 2009435 37185227 := bstep (se 1 (by rfl) ⟨27888920, by rfl⟩ : syracuseStep 37185227 = 55777841) B55777841
theorem B24790151 : Blo 2009435 24790151 := bstep (se 1 (by rfl) ⟨18592613, by rfl⟩ : syracuseStep 24790151 = 37185227) B37185227
theorem B16526767 : Blo 2009435 16526767 := bstep (se 1 (by rfl) ⟨12395075, by rfl⟩ : syracuseStep 16526767 = 24790151) B24790151
theorem B22035689 : Blo 2009435 22035689 := bstep (se 2 (by rfl) ⟨8263383, by rfl⟩ : syracuseStep 22035689 = 16526767) B16526767
theorem B14690459 : Blo 2009435 14690459 := bstep (se 1 (by rfl) ⟨11017844, by rfl⟩ : syracuseStep 14690459 = 22035689) B22035689
theorem B9793639 : Blo 2009435 9793639 := bstep (se 1 (by rfl) ⟨7345229, by rfl⟩ : syracuseStep 9793639 = 14690459) B14690459
theorem B13058185 : Blo 2009435 13058185 := bstep (se 2 (by rfl) ⟨4896819, by rfl⟩ : syracuseStep 13058185 = 9793639) B9793639
theorem B17410913 : Blo 2009435 17410913 := bstep (se 2 (by rfl) ⟨6529092, by rfl⟩ : syracuseStep 17410913 = 13058185) B13058185
theorem B11607275 : Blo 2009435 11607275 := bstep (se 1 (by rfl) ⟨8705456, by rfl⟩ : syracuseStep 11607275 = 17410913) B17410913
theorem B7738183 : Blo 2009435 7738183 := bstep (se 1 (by rfl) ⟨5803637, by rfl⟩ : syracuseStep 7738183 = 11607275) B11607275
theorem B41270309 : Blo 2009435 41270309 := bstep (se 4 (by rfl) ⟨3869091, by rfl⟩ : syracuseStep 41270309 = 7738183) B7738183
theorem B27513539 : Blo 2009435 27513539 := bstep (se 1 (by rfl) ⟨20635154, by rfl⟩ : syracuseStep 27513539 = 41270309) B41270309
theorem B18342359 : Blo 2009435 18342359 := bstep (se 1 (by rfl) ⟨13756769, by rfl⟩ : syracuseStep 18342359 = 27513539) B27513539
theorem B12228239 : Blo 2009435 12228239 := bstep (se 1 (by rfl) ⟨9171179, by rfl⟩ : syracuseStep 12228239 = 18342359) B18342359
theorem B8152159 : Blo 2009435 8152159 := bstep (se 1 (by rfl) ⟨6114119, by rfl⟩ : syracuseStep 8152159 = 12228239) B12228239
theorem B10869545 : Blo 2009435 10869545 := bstep (se 2 (by rfl) ⟨4076079, by rfl⟩ : syracuseStep 10869545 = 8152159) B8152159
theorem B7246363 : Blo 2009435 7246363 := bstep (se 1 (by rfl) ⟨5434772, by rfl⟩ : syracuseStep 7246363 = 10869545) B10869545
theorem B9661817 : Blo 2009435 9661817 := bstep (se 2 (by rfl) ⟨3623181, by rfl⟩ : syracuseStep 9661817 = 7246363) B7246363
theorem B6441211 : Blo 2009435 6441211 := bstep (se 1 (by rfl) ⟨4830908, by rfl⟩ : syracuseStep 6441211 = 9661817) B9661817
theorem B8588281 : Blo 2009435 8588281 := bstep (se 2 (by rfl) ⟨3220605, by rfl⟩ : syracuseStep 8588281 = 6441211) B6441211
theorem B11451041 : Blo 2009435 11451041 := bstep (se 2 (by rfl) ⟨4294140, by rfl⟩ : syracuseStep 11451041 = 8588281) B8588281
theorem B7634027 : Blo 2009435 7634027 := bstep (se 1 (by rfl) ⟨5725520, by rfl⟩ : syracuseStep 7634027 = 11451041) B11451041
theorem B5089351 : Blo 2009435 5089351 := bstep (se 1 (by rfl) ⟨3817013, by rfl⟩ : syracuseStep 5089351 = 7634027) B7634027
theorem B6785801 : Blo 2009435 6785801 := bstep (se 2 (by rfl) ⟨2544675, by rfl⟩ : syracuseStep 6785801 = 5089351) B5089351
theorem B4523867 : Blo 2009435 4523867 := bstep (se 1 (by rfl) ⟨3392900, by rfl⟩ : syracuseStep 4523867 = 6785801) B6785801
theorem B3015911 : Blo 2009435 3015911 := bstep (se 1 (by rfl) ⟨2261933, by rfl⟩ : syracuseStep 3015911 = 4523867) B4523867
theorem B2010607 : Blo 2009435 2010607 := bstep (se 1 (by rfl) ⟨1507955, by rfl⟩ : syracuseStep 2010607 = 3015911) B3015911
theorem B3015917 : Blo 2009435 3015917 := bbase (se 3 (by rfl) ⟨565484, by rfl⟩ : syracuseStep 3015917 = 1130969) (by norm_num)
theorem B2010611 : Blo 2009435 2010611 := bstep (se 1 (by rfl) ⟨1507958, by rfl⟩ : syracuseStep 2010611 = 3015917) B3015917
theorem B4523885 : Blo 2009435 4523885 := bbase (se 3 (by rfl) ⟨848228, by rfl⟩ : syracuseStep 4523885 = 1696457) (by norm_num)
theorem B3015923 : Blo 2009435 3015923 := bstep (se 1 (by rfl) ⟨2261942, by rfl⟩ : syracuseStep 3015923 = 4523885) B4523885
theorem B2010615 : Blo 2009435 2010615 := bstep (se 1 (by rfl) ⟨1507961, by rfl⟩ : syracuseStep 2010615 = 3015923) B3015923
theorem B3817037 : Blo 2009435 3817037 := bbase (se 3 (by rfl) ⟨715694, by rfl⟩ : syracuseStep 3817037 = 1431389) (by norm_num)
theorem B2544691 : Blo 2009435 2544691 := bstep (se 1 (by rfl) ⟨1908518, by rfl⟩ : syracuseStep 2544691 = 3817037) B3817037
theorem B3392921 : Blo 2009435 3392921 := bstep (se 2 (by rfl) ⟨1272345, by rfl⟩ : syracuseStep 3392921 = 2544691) B2544691
theorem B2261947 : Blo 2009435 2261947 := bstep (se 1 (by rfl) ⟨1696460, by rfl⟩ : syracuseStep 2261947 = 3392921) B3392921
theorem B3015929 : Blo 2009435 3015929 := bstep (se 2 (by rfl) ⟨1130973, by rfl⟩ : syracuseStep 3015929 = 2261947) B2261947
theorem B2010619 : Blo 2009435 2010619 := bstep (se 1 (by rfl) ⟨1507964, by rfl⟩ : syracuseStep 2010619 = 3015929) B3015929
theorem B2176381 : Blo 2009435 2176381 := bbase (se 3 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 2176381 = 816143) (by norm_num)
theorem B2901841 : Blo 2009435 2901841 := bstep (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) B2176381
theorem B61905941 : Blo 2009435 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B41270627 : Blo 2009435 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B27513751 : Blo 2009435 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B36685001 : Blo 2009435 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B24456667 : Blo 2009435 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B32608889 : Blo 2009435 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B21739259 : Blo 2009435 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B14492839 : Blo 2009435 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B19323785 : Blo 2009435 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B51530093 : Blo 2009435 51530093 := bstep (se 3 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 51530093 = 19323785) B19323785
theorem B34353395 : Blo 2009435 34353395 := bstep (se 1 (by rfl) ⟨25765046, by rfl⟩ : syracuseStep 34353395 = 51530093) B51530093
theorem B22902263 : Blo 2009435 22902263 := bstep (se 1 (by rfl) ⟨17176697, by rfl⟩ : syracuseStep 22902263 = 34353395) B34353395
theorem B15268175 : Blo 2009435 15268175 := bstep (se 1 (by rfl) ⟨11451131, by rfl⟩ : syracuseStep 15268175 = 22902263) B22902263
theorem B10178783 : Blo 2009435 10178783 := bstep (se 1 (by rfl) ⟨7634087, by rfl⟩ : syracuseStep 10178783 = 15268175) B15268175
theorem B6785855 : Blo 2009435 6785855 := bstep (se 1 (by rfl) ⟨5089391, by rfl⟩ : syracuseStep 6785855 = 10178783) B10178783
theorem B4523903 : Blo 2009435 4523903 := bstep (se 1 (by rfl) ⟨3392927, by rfl⟩ : syracuseStep 4523903 = 6785855) B6785855
theorem B3015935 : Blo 2009435 3015935 := bstep (se 1 (by rfl) ⟨2261951, by rfl⟩ : syracuseStep 3015935 = 4523903) B4523903
theorem B2010623 : Blo 2009435 2010623 := bstep (se 1 (by rfl) ⟨1507967, by rfl⟩ : syracuseStep 2010623 = 3015935) B3015935
theorem B3015941 : Blo 2009435 3015941 := bbase (se 4 (by rfl) ⟨282744, by rfl⟩ : syracuseStep 3015941 = 565489) (by norm_num)
theorem B2010627 : Blo 2009435 2010627 := bstep (se 1 (by rfl) ⟨1507970, by rfl⟩ : syracuseStep 2010627 = 3015941) B3015941
theorem B3392941 : Blo 2009435 3392941 := bbase (se 3 (by rfl) ⟨636176, by rfl⟩ : syracuseStep 3392941 = 1272353) (by norm_num)
theorem B4523921 : Blo 2009435 4523921 := bstep (se 2 (by rfl) ⟨1696470, by rfl⟩ : syracuseStep 4523921 = 3392941) B3392941
theorem B3015947 : Blo 2009435 3015947 := bstep (se 1 (by rfl) ⟨2261960, by rfl⟩ : syracuseStep 3015947 = 4523921) B4523921
theorem B2010631 : Blo 2009435 2010631 := bstep (se 1 (by rfl) ⟨1507973, by rfl⟩ : syracuseStep 2010631 = 3015947) B3015947
theorem B2261965 : Blo 2009435 2261965 := bbase (se 3 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 2261965 = 848237) (by norm_num)
theorem B3015953 : Blo 2009435 3015953 := bstep (se 2 (by rfl) ⟨1130982, by rfl⟩ : syracuseStep 3015953 = 2261965) B2261965
theorem B2010635 : Blo 2009435 2010635 := bstep (se 1 (by rfl) ⟨1507976, by rfl⟩ : syracuseStep 2010635 = 3015953) B3015953
theorem B6785909 : Blo 2009435 6785909 := bbase (se 5 (by rfl) ⟨318089, by rfl⟩ : syracuseStep 6785909 = 636179) (by norm_num)
theorem B4523939 : Blo 2009435 4523939 := bstep (se 1 (by rfl) ⟨3392954, by rfl⟩ : syracuseStep 4523939 = 6785909) B6785909
theorem B3015959 : Blo 2009435 3015959 := bstep (se 1 (by rfl) ⟨2261969, by rfl⟩ : syracuseStep 3015959 = 4523939) B4523939
theorem B2010639 : Blo 2009435 2010639 := bstep (se 1 (by rfl) ⟨1507979, by rfl⟩ : syracuseStep 2010639 = 3015959) B3015959
theorem B3015965 : Blo 2009435 3015965 := bbase (se 3 (by rfl) ⟨565493, by rfl⟩ : syracuseStep 3015965 = 1130987) (by norm_num)
theorem B2010643 : Blo 2009435 2010643 := bstep (se 1 (by rfl) ⟨1507982, by rfl⟩ : syracuseStep 2010643 = 3015965) B3015965
theorem B4523957 : Blo 2009435 4523957 := bbase (se 5 (by rfl) ⟨212060, by rfl⟩ : syracuseStep 4523957 = 424121) (by norm_num)
theorem B3015971 : Blo 2009435 3015971 := bstep (se 1 (by rfl) ⟨2261978, by rfl⟩ : syracuseStep 3015971 = 4523957) B4523957
theorem B2010647 : Blo 2009435 2010647 := bstep (se 1 (by rfl) ⟨1507985, by rfl⟩ : syracuseStep 2010647 = 3015971) B3015971
theorem B6972389 : Blo 2009435 6972389 := bbase (se 4 (by rfl) ⟨653661, by rfl⟩ : syracuseStep 6972389 = 1307323) (by norm_num)
theorem B4648259 : Blo 2009435 4648259 := bstep (se 1 (by rfl) ⟨3486194, by rfl⟩ : syracuseStep 4648259 = 6972389) B6972389
theorem B3098839 : Blo 2009435 3098839 := bstep (se 1 (by rfl) ⟨2324129, by rfl⟩ : syracuseStep 3098839 = 4648259) B4648259
theorem B4131785 : Blo 2009435 4131785 := bstep (se 2 (by rfl) ⟨1549419, by rfl⟩ : syracuseStep 4131785 = 3098839) B3098839
theorem B2754523 : Blo 2009435 2754523 := bstep (se 1 (by rfl) ⟨2065892, by rfl⟩ : syracuseStep 2754523 = 4131785) B4131785
theorem B3672697 : Blo 2009435 3672697 := bstep (se 2 (by rfl) ⟨1377261, by rfl⟩ : syracuseStep 3672697 = 2754523) B2754523
theorem B4896929 : Blo 2009435 4896929 := bstep (se 2 (by rfl) ⟨1836348, by rfl⟩ : syracuseStep 4896929 = 3672697) B3672697
theorem B3264619 : Blo 2009435 3264619 := bstep (se 1 (by rfl) ⟨2448464, by rfl⟩ : syracuseStep 3264619 = 4896929) B4896929
theorem B4352825 : Blo 2009435 4352825 := bstep (se 2 (by rfl) ⟨1632309, by rfl⟩ : syracuseStep 4352825 = 3264619) B3264619
theorem B11607533 : Blo 2009435 11607533 := bstep (se 3 (by rfl) ⟨2176412, by rfl⟩ : syracuseStep 11607533 = 4352825) B4352825
theorem B7738355 : Blo 2009435 7738355 := bstep (se 1 (by rfl) ⟨5803766, by rfl⟩ : syracuseStep 7738355 = 11607533) B11607533
theorem B5158903 : Blo 2009435 5158903 := bstep (se 1 (by rfl) ⟨3869177, by rfl⟩ : syracuseStep 5158903 = 7738355) B7738355
theorem B6878537 : Blo 2009435 6878537 := bstep (se 2 (by rfl) ⟨2579451, by rfl⟩ : syracuseStep 6878537 = 5158903) B5158903
theorem B4585691 : Blo 2009435 4585691 := bstep (se 1 (by rfl) ⟨3439268, by rfl⟩ : syracuseStep 4585691 = 6878537) B6878537
theorem B12228509 : Blo 2009435 12228509 := bstep (se 3 (by rfl) ⟨2292845, by rfl⟩ : syracuseStep 12228509 = 4585691) B4585691
theorem B8152339 : Blo 2009435 8152339 := bstep (se 1 (by rfl) ⟨6114254, by rfl⟩ : syracuseStep 8152339 = 12228509) B12228509
theorem B10869785 : Blo 2009435 10869785 := bstep (se 2 (by rfl) ⟨4076169, by rfl⟩ : syracuseStep 10869785 = 8152339) B8152339
theorem B7246523 : Blo 2009435 7246523 := bstep (se 1 (by rfl) ⟨5434892, by rfl⟩ : syracuseStep 7246523 = 10869785) B10869785
theorem B4831015 : Blo 2009435 4831015 := bstep (se 1 (by rfl) ⟨3623261, by rfl⟩ : syracuseStep 4831015 = 7246523) B7246523
theorem B6441353 : Blo 2009435 6441353 := bstep (se 2 (by rfl) ⟨2415507, by rfl⟩ : syracuseStep 6441353 = 4831015) B4831015
theorem B4294235 : Blo 2009435 4294235 := bstep (se 1 (by rfl) ⟨3220676, by rfl⟩ : syracuseStep 4294235 = 6441353) B6441353
theorem B11451293 : Blo 2009435 11451293 := bstep (se 3 (by rfl) ⟨2147117, by rfl⟩ : syracuseStep 11451293 = 4294235) B4294235
theorem B7634195 : Blo 2009435 7634195 := bstep (se 1 (by rfl) ⟨5725646, by rfl⟩ : syracuseStep 7634195 = 11451293) B11451293
theorem B5089463 : Blo 2009435 5089463 := bstep (se 1 (by rfl) ⟨3817097, by rfl⟩ : syracuseStep 5089463 = 7634195) B7634195
theorem B3392975 : Blo 2009435 3392975 := bstep (se 1 (by rfl) ⟨2544731, by rfl⟩ : syracuseStep 3392975 = 5089463) B5089463
theorem B2261983 : Blo 2009435 2261983 := bstep (se 1 (by rfl) ⟨1696487, by rfl⟩ : syracuseStep 2261983 = 3392975) B3392975
theorem B3015977 : Blo 2009435 3015977 := bstep (se 2 (by rfl) ⟨1130991, by rfl⟩ : syracuseStep 3015977 = 2261983) B2261983
theorem B2010651 : Blo 2009435 2010651 := bstep (se 1 (by rfl) ⟨1507988, by rfl⟩ : syracuseStep 2010651 = 3015977) B3015977
theorem B6441365 : Blo 2009435 6441365 := bbase (se 6 (by rfl) ⟨150969, by rfl⟩ : syracuseStep 6441365 = 301939) (by norm_num)
theorem B4294243 : Blo 2009435 4294243 := bstep (se 1 (by rfl) ⟨3220682, by rfl⟩ : syracuseStep 4294243 = 6441365) B6441365
theorem B5725657 : Blo 2009435 5725657 := bstep (se 2 (by rfl) ⟨2147121, by rfl⟩ : syracuseStep 5725657 = 4294243) B4294243
theorem B7634209 : Blo 2009435 7634209 := bstep (se 2 (by rfl) ⟨2862828, by rfl⟩ : syracuseStep 7634209 = 5725657) B5725657
theorem B10178945 : Blo 2009435 10178945 := bstep (se 2 (by rfl) ⟨3817104, by rfl⟩ : syracuseStep 10178945 = 7634209) B7634209
theorem B6785963 : Blo 2009435 6785963 := bstep (se 1 (by rfl) ⟨5089472, by rfl⟩ : syracuseStep 6785963 = 10178945) B10178945
theorem B4523975 : Blo 2009435 4523975 := bstep (se 1 (by rfl) ⟨3392981, by rfl⟩ : syracuseStep 4523975 = 6785963) B6785963
theorem B3015983 : Blo 2009435 3015983 := bstep (se 1 (by rfl) ⟨2261987, by rfl⟩ : syracuseStep 3015983 = 4523975) B4523975
theorem B2010655 : Blo 2009435 2010655 := bstep (se 1 (by rfl) ⟨1507991, by rfl⟩ : syracuseStep 2010655 = 3015983) B3015983
theorem B3015989 : Blo 2009435 3015989 := bbase (se 5 (by rfl) ⟨141374, by rfl⟩ : syracuseStep 3015989 = 282749) (by norm_num)
theorem B2010659 : Blo 2009435 2010659 := bstep (se 1 (by rfl) ⟨1507994, by rfl⟩ : syracuseStep 2010659 = 3015989) B3015989
theorem B5089493 : Blo 2009435 5089493 := bbase (se 7 (by rfl) ⟨59642, by rfl⟩ : syracuseStep 5089493 = 119285) (by norm_num)
theorem B3392995 : Blo 2009435 3392995 := bstep (se 1 (by rfl) ⟨2544746, by rfl⟩ : syracuseStep 3392995 = 5089493) B5089493
theorem B4523993 : Blo 2009435 4523993 := bstep (se 2 (by rfl) ⟨1696497, by rfl⟩ : syracuseStep 4523993 = 3392995) B3392995
theorem B3015995 : Blo 2009435 3015995 := bstep (se 1 (by rfl) ⟨2261996, by rfl⟩ : syracuseStep 3015995 = 4523993) B4523993
theorem B2010663 : Blo 2009435 2010663 := bstep (se 1 (by rfl) ⟨1507997, by rfl⟩ : syracuseStep 2010663 = 3015995) B3015995
theorem B2262001 : Blo 2009435 2262001 := bbase (se 2 (by rfl) ⟨848250, by rfl⟩ : syracuseStep 2262001 = 1696501) (by norm_num)
theorem B3016001 : Blo 2009435 3016001 := bstep (se 2 (by rfl) ⟨1131000, by rfl⟩ : syracuseStep 3016001 = 2262001) B2262001
theorem B2010667 : Blo 2009435 2010667 := bstep (se 1 (by rfl) ⟨1508000, by rfl⟩ : syracuseStep 2010667 = 3016001) B3016001
theorem B2038105 : Blo 2009435 2038105 := bbase (se 2 (by rfl) ⟨764289, by rfl⟩ : syracuseStep 2038105 = 1528579) (by norm_num)
theorem B2717473 : Blo 2009435 2717473 := bstep (se 2 (by rfl) ⟨1019052, by rfl⟩ : syracuseStep 2717473 = 2038105) B2038105
theorem B3623297 : Blo 2009435 3623297 := bstep (se 2 (by rfl) ⟨1358736, by rfl⟩ : syracuseStep 3623297 = 2717473) B2717473
theorem B9662125 : Blo 2009435 9662125 := bstep (se 3 (by rfl) ⟨1811648, by rfl⟩ : syracuseStep 9662125 = 3623297) B3623297
theorem B12882833 : Blo 2009435 12882833 := bstep (se 2 (by rfl) ⟨4831062, by rfl⟩ : syracuseStep 12882833 = 9662125) B9662125
theorem B8588555 : Blo 2009435 8588555 := bstep (se 1 (by rfl) ⟨6441416, by rfl⟩ : syracuseStep 8588555 = 12882833) B12882833
theorem B5725703 : Blo 2009435 5725703 := bstep (se 1 (by rfl) ⟨4294277, by rfl⟩ : syracuseStep 5725703 = 8588555) B8588555
theorem B3817135 : Blo 2009435 3817135 := bstep (se 1 (by rfl) ⟨2862851, by rfl⟩ : syracuseStep 3817135 = 5725703) B5725703
theorem B5089513 : Blo 2009435 5089513 := bstep (se 2 (by rfl) ⟨1908567, by rfl⟩ : syracuseStep 5089513 = 3817135) B3817135
theorem B6786017 : Blo 2009435 6786017 := bstep (se 2 (by rfl) ⟨2544756, by rfl⟩ : syracuseStep 6786017 = 5089513) B5089513
theorem B4524011 : Blo 2009435 4524011 := bstep (se 1 (by rfl) ⟨3393008, by rfl⟩ : syracuseStep 4524011 = 6786017) B6786017
theorem B3016007 : Blo 2009435 3016007 := bstep (se 1 (by rfl) ⟨2262005, by rfl⟩ : syracuseStep 3016007 = 4524011) B4524011
theorem B2010671 : Blo 2009435 2010671 := bstep (se 1 (by rfl) ⟨1508003, by rfl⟩ : syracuseStep 2010671 = 3016007) B3016007
theorem B3016013 : Blo 2009435 3016013 := bbase (se 3 (by rfl) ⟨565502, by rfl⟩ : syracuseStep 3016013 = 1131005) (by norm_num)
theorem B2010675 : Blo 2009435 2010675 := bstep (se 1 (by rfl) ⟨1508006, by rfl⟩ : syracuseStep 2010675 = 3016013) B3016013
theorem B4524029 : Blo 2009435 4524029 := bbase (se 3 (by rfl) ⟨848255, by rfl⟩ : syracuseStep 4524029 = 1696511) (by norm_num)
theorem B3016019 : Blo 2009435 3016019 := bstep (se 1 (by rfl) ⟨2262014, by rfl⟩ : syracuseStep 3016019 = 4524029) B4524029
theorem B2010679 : Blo 2009435 2010679 := bstep (se 1 (by rfl) ⟨1508009, by rfl⟩ : syracuseStep 2010679 = 3016019) B3016019
theorem B3393029 : Blo 2009435 3393029 := bbase (se 4 (by rfl) ⟨318096, by rfl⟩ : syracuseStep 3393029 = 636193) (by norm_num)
theorem B2262019 : Blo 2009435 2262019 := bstep (se 1 (by rfl) ⟨1696514, by rfl⟩ : syracuseStep 2262019 = 3393029) B3393029
theorem B3016025 : Blo 2009435 3016025 := bstep (se 2 (by rfl) ⟨1131009, by rfl⟩ : syracuseStep 3016025 = 2262019) B2262019
theorem B2010683 : Blo 2009435 2010683 := bstep (se 1 (by rfl) ⟨1508012, by rfl⟩ : syracuseStep 2010683 = 3016025) B3016025
theorem B15268661 : Blo 2009435 15268661 := bbase (se 5 (by rfl) ⟨715718, by rfl⟩ : syracuseStep 15268661 = 1431437) (by norm_num)
theorem B10179107 : Blo 2009435 10179107 := bstep (se 1 (by rfl) ⟨7634330, by rfl⟩ : syracuseStep 10179107 = 15268661) B15268661
theorem B6786071 : Blo 2009435 6786071 := bstep (se 1 (by rfl) ⟨5089553, by rfl⟩ : syracuseStep 6786071 = 10179107) B10179107
theorem B4524047 : Blo 2009435 4524047 := bstep (se 1 (by rfl) ⟨3393035, by rfl⟩ : syracuseStep 4524047 = 6786071) B6786071
theorem B3016031 : Blo 2009435 3016031 := bstep (se 1 (by rfl) ⟨2262023, by rfl⟩ : syracuseStep 3016031 = 4524047) B4524047
theorem B2010687 : Blo 2009435 2010687 := bstep (se 1 (by rfl) ⟨1508015, by rfl⟩ : syracuseStep 2010687 = 3016031) B3016031
theorem B3016037 : Blo 2009435 3016037 := bbase (se 4 (by rfl) ⟨282753, by rfl⟩ : syracuseStep 3016037 = 565507) (by norm_num)
theorem B2010691 : Blo 2009435 2010691 := bstep (se 1 (by rfl) ⟨1508018, by rfl⟩ : syracuseStep 2010691 = 3016037) B3016037
theorem B3817181 : Blo 2009435 3817181 := bbase (se 3 (by rfl) ⟨715721, by rfl⟩ : syracuseStep 3817181 = 1431443) (by norm_num)
theorem B2544787 : Blo 2009435 2544787 := bstep (se 1 (by rfl) ⟨1908590, by rfl⟩ : syracuseStep 2544787 = 3817181) B3817181
theorem B3393049 : Blo 2009435 3393049 := bstep (se 2 (by rfl) ⟨1272393, by rfl⟩ : syracuseStep 3393049 = 2544787) B2544787
theorem B4524065 : Blo 2009435 4524065 := bstep (se 2 (by rfl) ⟨1696524, by rfl⟩ : syracuseStep 4524065 = 3393049) B3393049
theorem B3016043 : Blo 2009435 3016043 := bstep (se 1 (by rfl) ⟨2262032, by rfl⟩ : syracuseStep 3016043 = 4524065) B4524065
theorem B2010695 : Blo 2009435 2010695 := bstep (se 1 (by rfl) ⟨1508021, by rfl⟩ : syracuseStep 2010695 = 3016043) B3016043
theorem B2262037 : Blo 2009435 2262037 := bbase (se 6 (by rfl) ⟨53016, by rfl⟩ : syracuseStep 2262037 = 106033) (by norm_num)
theorem B3016049 : Blo 2009435 3016049 := bstep (se 2 (by rfl) ⟨1131018, by rfl⟩ : syracuseStep 3016049 = 2262037) B2262037
theorem B2010699 : Blo 2009435 2010699 := bstep (se 1 (by rfl) ⟨1508024, by rfl⟩ : syracuseStep 2010699 = 3016049) B3016049
theorem B2544797 : Blo 2009435 2544797 := bbase (se 3 (by rfl) ⟨477149, by rfl⟩ : syracuseStep 2544797 = 954299) (by norm_num)
theorem B6786125 : Blo 2009435 6786125 := bstep (se 3 (by rfl) ⟨1272398, by rfl⟩ : syracuseStep 6786125 = 2544797) B2544797
theorem B4524083 : Blo 2009435 4524083 := bstep (se 1 (by rfl) ⟨3393062, by rfl⟩ : syracuseStep 4524083 = 6786125) B6786125
theorem B3016055 : Blo 2009435 3016055 := bstep (se 1 (by rfl) ⟨2262041, by rfl⟩ : syracuseStep 3016055 = 4524083) B4524083
theorem B2010703 : Blo 2009435 2010703 := bstep (se 1 (by rfl) ⟨1508027, by rfl⟩ : syracuseStep 2010703 = 3016055) B3016055
theorem B3016061 : Blo 2009435 3016061 := bbase (se 3 (by rfl) ⟨565511, by rfl⟩ : syracuseStep 3016061 = 1131023) (by norm_num)
theorem B2010707 : Blo 2009435 2010707 := bstep (se 1 (by rfl) ⟨1508030, by rfl⟩ : syracuseStep 2010707 = 3016061) B3016061
theorem B4524101 : Blo 2009435 4524101 := bbase (se 4 (by rfl) ⟨424134, by rfl⟩ : syracuseStep 4524101 = 848269) (by norm_num)
theorem B3016067 : Blo 2009435 3016067 := bstep (se 1 (by rfl) ⟨2262050, by rfl⟩ : syracuseStep 3016067 = 4524101) B4524101
theorem B2010711 : Blo 2009435 2010711 := bstep (se 1 (by rfl) ⟨1508033, by rfl⟩ : syracuseStep 2010711 = 3016067) B3016067
theorem B5725829 : Blo 2009435 5725829 := bbase (se 4 (by rfl) ⟨536796, by rfl⟩ : syracuseStep 5725829 = 1073593) (by norm_num)
theorem B3817219 : Blo 2009435 3817219 := bstep (se 1 (by rfl) ⟨2862914, by rfl⟩ : syracuseStep 3817219 = 5725829) B5725829
theorem B5089625 : Blo 2009435 5089625 := bstep (se 2 (by rfl) ⟨1908609, by rfl⟩ : syracuseStep 5089625 = 3817219) B3817219
theorem B3393083 : Blo 2009435 3393083 := bstep (se 1 (by rfl) ⟨2544812, by rfl⟩ : syracuseStep 3393083 = 5089625) B5089625
theorem B2262055 : Blo 2009435 2262055 := bstep (se 1 (by rfl) ⟨1696541, by rfl⟩ : syracuseStep 2262055 = 3393083) B3393083
theorem B3016073 : Blo 2009435 3016073 := bstep (se 2 (by rfl) ⟨1131027, by rfl⟩ : syracuseStep 3016073 = 2262055) B2262055
theorem B2010715 : Blo 2009435 2010715 := bstep (se 1 (by rfl) ⟨1508036, by rfl⟩ : syracuseStep 2010715 = 3016073) B3016073
theorem B10179269 : Blo 2009435 10179269 := bbase (se 4 (by rfl) ⟨954306, by rfl⟩ : syracuseStep 10179269 = 1908613) (by norm_num)
theorem B6786179 : Blo 2009435 6786179 := bstep (se 1 (by rfl) ⟨5089634, by rfl⟩ : syracuseStep 6786179 = 10179269) B10179269
theorem B4524119 : Blo 2009435 4524119 := bstep (se 1 (by rfl) ⟨3393089, by rfl⟩ : syracuseStep 4524119 = 6786179) B6786179
theorem B3016079 : Blo 2009435 3016079 := bstep (se 1 (by rfl) ⟨2262059, by rfl⟩ : syracuseStep 3016079 = 4524119) B4524119
theorem B2010719 : Blo 2009435 2010719 := bstep (se 1 (by rfl) ⟨1508039, by rfl⟩ : syracuseStep 2010719 = 3016079) B3016079
theorem B3016085 : Blo 2009435 3016085 := bbase (se 6 (by rfl) ⟨70689, by rfl⟩ : syracuseStep 3016085 = 141379) (by norm_num)
theorem B2010723 : Blo 2009435 2010723 := bstep (se 1 (by rfl) ⟨1508042, by rfl⟩ : syracuseStep 2010723 = 3016085) B3016085
theorem B4294397 : Blo 2009435 4294397 := bbase (se 3 (by rfl) ⟨805199, by rfl⟩ : syracuseStep 4294397 = 1610399) (by norm_num)
theorem B11451725 : Blo 2009435 11451725 := bstep (se 3 (by rfl) ⟨2147198, by rfl⟩ : syracuseStep 11451725 = 4294397) B4294397
theorem B7634483 : Blo 2009435 7634483 := bstep (se 1 (by rfl) ⟨5725862, by rfl⟩ : syracuseStep 7634483 = 11451725) B11451725
theorem B5089655 : Blo 2009435 5089655 := bstep (se 1 (by rfl) ⟨3817241, by rfl⟩ : syracuseStep 5089655 = 7634483) B7634483
theorem B3393103 : Blo 2009435 3393103 := bstep (se 1 (by rfl) ⟨2544827, by rfl⟩ : syracuseStep 3393103 = 5089655) B5089655
theorem B4524137 : Blo 2009435 4524137 := bstep (se 2 (by rfl) ⟨1696551, by rfl⟩ : syracuseStep 4524137 = 3393103) B3393103
theorem B3016091 : Blo 2009435 3016091 := bstep (se 1 (by rfl) ⟨2262068, by rfl⟩ : syracuseStep 3016091 = 4524137) B4524137
theorem B2010727 : Blo 2009435 2010727 := bstep (se 1 (by rfl) ⟨1508045, by rfl⟩ : syracuseStep 2010727 = 3016091) B3016091
theorem B2262073 : Blo 2009435 2262073 := bbase (se 2 (by rfl) ⟨848277, by rfl⟩ : syracuseStep 2262073 = 1696555) (by norm_num)
theorem B3016097 : Blo 2009435 3016097 := bstep (se 2 (by rfl) ⟨1131036, by rfl⟩ : syracuseStep 3016097 = 2262073) B2262073
theorem B2010731 : Blo 2009435 2010731 := bstep (se 1 (by rfl) ⟨1508048, by rfl⟩ : syracuseStep 2010731 = 3016097) B3016097
theorem B3623413 : Blo 2009435 3623413 := bbase (se 5 (by rfl) ⟨169847, by rfl⟩ : syracuseStep 3623413 = 339695) (by norm_num)
theorem B4831217 : Blo 2009435 4831217 := bstep (se 2 (by rfl) ⟨1811706, by rfl⟩ : syracuseStep 4831217 = 3623413) B3623413
theorem B3220811 : Blo 2009435 3220811 := bstep (se 1 (by rfl) ⟨2415608, by rfl⟩ : syracuseStep 3220811 = 4831217) B4831217
theorem B2147207 : Blo 2009435 2147207 := bstep (se 1 (by rfl) ⟨1610405, by rfl⟩ : syracuseStep 2147207 = 3220811) B3220811
theorem B5725885 : Blo 2009435 5725885 := bstep (se 3 (by rfl) ⟨1073603, by rfl⟩ : syracuseStep 5725885 = 2147207) B2147207
theorem B7634513 : Blo 2009435 7634513 := bstep (se 2 (by rfl) ⟨2862942, by rfl⟩ : syracuseStep 7634513 = 5725885) B5725885
theorem B5089675 : Blo 2009435 5089675 := bstep (se 1 (by rfl) ⟨3817256, by rfl⟩ : syracuseStep 5089675 = 7634513) B7634513
theorem B6786233 : Blo 2009435 6786233 := bstep (se 2 (by rfl) ⟨2544837, by rfl⟩ : syracuseStep 6786233 = 5089675) B5089675
theorem B4524155 : Blo 2009435 4524155 := bstep (se 1 (by rfl) ⟨3393116, by rfl⟩ : syracuseStep 4524155 = 6786233) B6786233
theorem B3016103 : Blo 2009435 3016103 := bstep (se 1 (by rfl) ⟨2262077, by rfl⟩ : syracuseStep 3016103 = 4524155) B4524155
theorem B2010735 : Blo 2009435 2010735 := bstep (se 1 (by rfl) ⟨1508051, by rfl⟩ : syracuseStep 2010735 = 3016103) B3016103
theorem B3016109 : Blo 2009435 3016109 := bbase (se 3 (by rfl) ⟨565520, by rfl⟩ : syracuseStep 3016109 = 1131041) (by norm_num)
theorem B2010739 : Blo 2009435 2010739 := bstep (se 1 (by rfl) ⟨1508054, by rfl⟩ : syracuseStep 2010739 = 3016109) B3016109
theorem B4524173 : Blo 2009435 4524173 := bbase (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) (by norm_num)
theorem B3016115 : Blo 2009435 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B2010743 : Blo 2009435 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B2544853 : Blo 2009435 2544853 := bbase (se 7 (by rfl) ⟨29822, by rfl⟩ : syracuseStep 2544853 = 59645) (by norm_num)
theorem B3393137 : Blo 2009435 3393137 := bstep (se 2 (by rfl) ⟨1272426, by rfl⟩ : syracuseStep 3393137 = 2544853) B2544853
theorem B2262091 : Blo 2009435 2262091 := bstep (se 1 (by rfl) ⟨1696568, by rfl⟩ : syracuseStep 2262091 = 3393137) B3393137
theorem B3016121 : Blo 2009435 3016121 := bstep (se 2 (by rfl) ⟨1131045, by rfl⟩ : syracuseStep 3016121 = 2262091) B2262091
theorem B2010747 : Blo 2009435 2010747 := bstep (se 1 (by rfl) ⟨1508060, by rfl⟩ : syracuseStep 2010747 = 3016121) B3016121
theorem B2065993 : Blo 2009435 2065993 := bbase (se 2 (by rfl) ⟨774747, by rfl⟩ : syracuseStep 2065993 = 1549495) (by norm_num)
theorem B11018629 : Blo 2009435 11018629 := bstep (se 4 (by rfl) ⟨1032996, by rfl⟩ : syracuseStep 11018629 = 2065993) B2065993
theorem B14691505 : Blo 2009435 14691505 := bstep (se 2 (by rfl) ⟨5509314, by rfl⟩ : syracuseStep 14691505 = 11018629) B11018629
theorem B19588673 : Blo 2009435 19588673 := bstep (se 2 (by rfl) ⟨7345752, by rfl⟩ : syracuseStep 19588673 = 14691505) B14691505
theorem B52236461 : Blo 2009435 52236461 := bstep (se 3 (by rfl) ⟨9794336, by rfl⟩ : syracuseStep 52236461 = 19588673) B19588673
theorem B139297229 : Blo 2009435 139297229 := bstep (se 3 (by rfl) ⟨26118230, by rfl⟩ : syracuseStep 139297229 = 52236461) B52236461
theorem B92864819 : Blo 2009435 92864819 := bstep (se 1 (by rfl) ⟨69648614, by rfl⟩ : syracuseStep 92864819 = 139297229) B139297229
theorem B61909879 : Blo 2009435 61909879 := bstep (se 1 (by rfl) ⟨46432409, by rfl⟩ : syracuseStep 61909879 = 92864819) B92864819
theorem B82546505 : Blo 2009435 82546505 := bstep (se 2 (by rfl) ⟨30954939, by rfl⟩ : syracuseStep 82546505 = 61909879) B61909879
theorem B55031003 : Blo 2009435 55031003 := bstep (se 1 (by rfl) ⟨41273252, by rfl⟩ : syracuseStep 55031003 = 82546505) B82546505
theorem B36687335 : Blo 2009435 36687335 := bstep (se 1 (by rfl) ⟨27515501, by rfl⟩ : syracuseStep 36687335 = 55031003) B55031003
theorem B97832893 : Blo 2009435 97832893 := bstep (se 3 (by rfl) ⟨18343667, by rfl⟩ : syracuseStep 97832893 = 36687335) B36687335
theorem B130443857 : Blo 2009435 130443857 := bstep (se 2 (by rfl) ⟨48916446, by rfl⟩ : syracuseStep 130443857 = 97832893) B97832893
theorem B86962571 : Blo 2009435 86962571 := bstep (se 1 (by rfl) ⟨65221928, by rfl⟩ : syracuseStep 86962571 = 130443857) B130443857
theorem B57975047 : Blo 2009435 57975047 := bstep (se 1 (by rfl) ⟨43481285, by rfl⟩ : syracuseStep 57975047 = 86962571) B86962571
theorem B38650031 : Blo 2009435 38650031 := bstep (se 1 (by rfl) ⟨28987523, by rfl⟩ : syracuseStep 38650031 = 57975047) B57975047
theorem B25766687 : Blo 2009435 25766687 := bstep (se 1 (by rfl) ⟨19325015, by rfl⟩ : syracuseStep 25766687 = 38650031) B38650031
theorem B17177791 : Blo 2009435 17177791 := bstep (se 1 (by rfl) ⟨12883343, by rfl⟩ : syracuseStep 17177791 = 25766687) B25766687
theorem B22903721 : Blo 2009435 22903721 := bstep (se 2 (by rfl) ⟨8588895, by rfl⟩ : syracuseStep 22903721 = 17177791) B17177791
theorem B15269147 : Blo 2009435 15269147 := bstep (se 1 (by rfl) ⟨11451860, by rfl⟩ : syracuseStep 15269147 = 22903721) B22903721
theorem B10179431 : Blo 2009435 10179431 := bstep (se 1 (by rfl) ⟨7634573, by rfl⟩ : syracuseStep 10179431 = 15269147) B15269147
theorem B6786287 : Blo 2009435 6786287 := bstep (se 1 (by rfl) ⟨5089715, by rfl⟩ : syracuseStep 6786287 = 10179431) B10179431
theorem B4524191 : Blo 2009435 4524191 := bstep (se 1 (by rfl) ⟨3393143, by rfl⟩ : syracuseStep 4524191 = 6786287) B6786287
theorem B3016127 : Blo 2009435 3016127 := bstep (se 1 (by rfl) ⟨2262095, by rfl⟩ : syracuseStep 3016127 = 4524191) B4524191
theorem B2010751 : Blo 2009435 2010751 := bstep (se 1 (by rfl) ⟨1508063, by rfl⟩ : syracuseStep 2010751 = 3016127) B3016127
theorem B3016133 : Blo 2009435 3016133 := bbase (se 4 (by rfl) ⟨282762, by rfl⟩ : syracuseStep 3016133 = 565525) (by norm_num)
theorem B2010755 : Blo 2009435 2010755 := bstep (se 1 (by rfl) ⟨1508066, by rfl⟩ : syracuseStep 2010755 = 3016133) B3016133
theorem B3393157 : Blo 2009435 3393157 := bbase (se 4 (by rfl) ⟨318108, by rfl⟩ : syracuseStep 3393157 = 636217) (by norm_num)
theorem B4524209 : Blo 2009435 4524209 := bstep (se 2 (by rfl) ⟨1696578, by rfl⟩ : syracuseStep 4524209 = 3393157) B3393157
theorem B3016139 : Blo 2009435 3016139 := bstep (se 1 (by rfl) ⟨2262104, by rfl⟩ : syracuseStep 3016139 = 4524209) B4524209
theorem B2010759 : Blo 2009435 2010759 := bstep (se 1 (by rfl) ⟨1508069, by rfl⟩ : syracuseStep 2010759 = 3016139) B3016139
theorem B2262109 : Blo 2009435 2262109 := bbase (se 3 (by rfl) ⟨424145, by rfl⟩ : syracuseStep 2262109 = 848291) (by norm_num)
theorem B3016145 : Blo 2009435 3016145 := bstep (se 2 (by rfl) ⟨1131054, by rfl⟩ : syracuseStep 3016145 = 2262109) B2262109
theorem B2010763 : Blo 2009435 2010763 := bstep (se 1 (by rfl) ⟨1508072, by rfl⟩ : syracuseStep 2010763 = 3016145) B3016145
theorem B6786341 : Blo 2009435 6786341 := bbase (se 4 (by rfl) ⟨636219, by rfl⟩ : syracuseStep 6786341 = 1272439) (by norm_num)
theorem B4524227 : Blo 2009435 4524227 := bstep (se 1 (by rfl) ⟨3393170, by rfl⟩ : syracuseStep 4524227 = 6786341) B6786341
theorem B3016151 : Blo 2009435 3016151 := bstep (se 1 (by rfl) ⟨2262113, by rfl⟩ : syracuseStep 3016151 = 4524227) B4524227
theorem B2010767 : Blo 2009435 2010767 := bstep (se 1 (by rfl) ⟨1508075, by rfl⟩ : syracuseStep 2010767 = 3016151) B3016151
theorem B3016157 : Blo 2009435 3016157 := bbase (se 3 (by rfl) ⟨565529, by rfl⟩ : syracuseStep 3016157 = 1131059) (by norm_num)
theorem B2010771 : Blo 2009435 2010771 := bstep (se 1 (by rfl) ⟨1508078, by rfl⟩ : syracuseStep 2010771 = 3016157) B3016157
theorem B4524245 : Blo 2009435 4524245 := bbase (se 7 (by rfl) ⟨53018, by rfl⟩ : syracuseStep 4524245 = 106037) (by norm_num)
theorem B3016163 : Blo 2009435 3016163 := bstep (se 1 (by rfl) ⟨2262122, by rfl⟩ : syracuseStep 3016163 = 4524245) B4524245
theorem B2010775 : Blo 2009435 2010775 := bstep (se 1 (by rfl) ⟨1508081, by rfl⟩ : syracuseStep 2010775 = 3016163) B3016163
theorem B9662645 : Blo 2009435 9662645 := bbase (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) (by norm_num)
theorem B6441763 : Blo 2009435 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B8589017 : Blo 2009435 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B5726011 : Blo 2009435 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B7634681 : Blo 2009435 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B5089787 : Blo 2009435 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B3393191 : Blo 2009435 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B2262127 : Blo 2009435 2262127 := bstep (se 1 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 2262127 = 3393191) B3393191
theorem B3016169 : Blo 2009435 3016169 := bstep (se 2 (by rfl) ⟨1131063, by rfl⟩ : syracuseStep 3016169 = 2262127) B2262127
theorem B2010779 : Blo 2009435 2010779 := bstep (se 1 (by rfl) ⟨1508084, by rfl⟩ : syracuseStep 2010779 = 3016169) B3016169
theorem B7246997 : Blo 2009435 7246997 := bbase (se 6 (by rfl) ⟨169851, by rfl⟩ : syracuseStep 7246997 = 339703) (by norm_num)
theorem B4831331 : Blo 2009435 4831331 := bstep (se 1 (by rfl) ⟨3623498, by rfl⟩ : syracuseStep 4831331 = 7246997) B7246997
theorem B12883549 : Blo 2009435 12883549 := bstep (se 3 (by rfl) ⟨2415665, by rfl⟩ : syracuseStep 12883549 = 4831331) B4831331
theorem B17178065 : Blo 2009435 17178065 := bstep (se 2 (by rfl) ⟨6441774, by rfl⟩ : syracuseStep 17178065 = 12883549) B12883549
theorem B11452043 : Blo 2009435 11452043 := bstep (se 1 (by rfl) ⟨8589032, by rfl⟩ : syracuseStep 11452043 = 17178065) B17178065
theorem B7634695 : Blo 2009435 7634695 := bstep (se 1 (by rfl) ⟨5726021, by rfl⟩ : syracuseStep 7634695 = 11452043) B11452043
theorem B10179593 : Blo 2009435 10179593 := bstep (se 2 (by rfl) ⟨3817347, by rfl⟩ : syracuseStep 10179593 = 7634695) B7634695
theorem B6786395 : Blo 2009435 6786395 := bstep (se 1 (by rfl) ⟨5089796, by rfl⟩ : syracuseStep 6786395 = 10179593) B10179593
theorem B4524263 : Blo 2009435 4524263 := bstep (se 1 (by rfl) ⟨3393197, by rfl⟩ : syracuseStep 4524263 = 6786395) B6786395
theorem B3016175 : Blo 2009435 3016175 := bstep (se 1 (by rfl) ⟨2262131, by rfl⟩ : syracuseStep 3016175 = 4524263) B4524263
theorem B2010783 : Blo 2009435 2010783 := bstep (se 1 (by rfl) ⟨1508087, by rfl⟩ : syracuseStep 2010783 = 3016175) B3016175
theorem B3016181 : Blo 2009435 3016181 := bbase (se 5 (by rfl) ⟨141383, by rfl⟩ : syracuseStep 3016181 = 282767) (by norm_num)
theorem B2010787 : Blo 2009435 2010787 := bstep (se 1 (by rfl) ⟨1508090, by rfl⟩ : syracuseStep 2010787 = 3016181) B3016181
theorem B3220901 : Blo 2009435 3220901 := bbase (se 4 (by rfl) ⟨301959, by rfl⟩ : syracuseStep 3220901 = 603919) (by norm_num)
theorem B2147267 : Blo 2009435 2147267 := bstep (se 1 (by rfl) ⟨1610450, by rfl⟩ : syracuseStep 2147267 = 3220901) B3220901
theorem B5726045 : Blo 2009435 5726045 := bstep (se 3 (by rfl) ⟨1073633, by rfl⟩ : syracuseStep 5726045 = 2147267) B2147267
theorem B3817363 : Blo 2009435 3817363 := bstep (se 1 (by rfl) ⟨2863022, by rfl⟩ : syracuseStep 3817363 = 5726045) B5726045
theorem B5089817 : Blo 2009435 5089817 := bstep (se 2 (by rfl) ⟨1908681, by rfl⟩ : syracuseStep 5089817 = 3817363) B3817363
theorem B3393211 : Blo 2009435 3393211 := bstep (se 1 (by rfl) ⟨2544908, by rfl⟩ : syracuseStep 3393211 = 5089817) B5089817
theorem B4524281 : Blo 2009435 4524281 := bstep (se 2 (by rfl) ⟨1696605, by rfl⟩ : syracuseStep 4524281 = 3393211) B3393211
theorem B3016187 : Blo 2009435 3016187 := bstep (se 1 (by rfl) ⟨2262140, by rfl⟩ : syracuseStep 3016187 = 4524281) B4524281
theorem B2010791 : Blo 2009435 2010791 := bstep (se 1 (by rfl) ⟨1508093, by rfl⟩ : syracuseStep 2010791 = 3016187) B3016187
theorem B2262145 : Blo 2009435 2262145 := bbase (se 2 (by rfl) ⟨848304, by rfl⟩ : syracuseStep 2262145 = 1696609) (by norm_num)
theorem B3016193 : Blo 2009435 3016193 := bstep (se 2 (by rfl) ⟨1131072, by rfl⟩ : syracuseStep 3016193 = 2262145) B2262145
theorem B2010795 : Blo 2009435 2010795 := bstep (se 1 (by rfl) ⟨1508096, by rfl⟩ : syracuseStep 2010795 = 3016193) B3016193
theorem B5089837 : Blo 2009435 5089837 := bbase (se 3 (by rfl) ⟨954344, by rfl⟩ : syracuseStep 5089837 = 1908689) (by norm_num)
theorem B6786449 : Blo 2009435 6786449 := bstep (se 2 (by rfl) ⟨2544918, by rfl⟩ : syracuseStep 6786449 = 5089837) B5089837
theorem B4524299 : Blo 2009435 4524299 := bstep (se 1 (by rfl) ⟨3393224, by rfl⟩ : syracuseStep 4524299 = 6786449) B6786449
theorem B3016199 : Blo 2009435 3016199 := bstep (se 1 (by rfl) ⟨2262149, by rfl⟩ : syracuseStep 3016199 = 4524299) B4524299
theorem B2010799 : Blo 2009435 2010799 := bstep (se 1 (by rfl) ⟨1508099, by rfl⟩ : syracuseStep 2010799 = 3016199) B3016199
theorem B3016205 : Blo 2009435 3016205 := bbase (se 3 (by rfl) ⟨565538, by rfl⟩ : syracuseStep 3016205 = 1131077) (by norm_num)
theorem B2010803 : Blo 2009435 2010803 := bstep (se 1 (by rfl) ⟨1508102, by rfl⟩ : syracuseStep 2010803 = 3016205) B3016205
theorem B4524317 : Blo 2009435 4524317 := bbase (se 3 (by rfl) ⟨848309, by rfl⟩ : syracuseStep 4524317 = 1696619) (by norm_num)
theorem B3016211 : Blo 2009435 3016211 := bstep (se 1 (by rfl) ⟨2262158, by rfl⟩ : syracuseStep 3016211 = 4524317) B4524317
theorem B2010807 : Blo 2009435 2010807 := bstep (se 1 (by rfl) ⟨1508105, by rfl⟩ : syracuseStep 2010807 = 3016211) B3016211
theorem B3393245 : Blo 2009435 3393245 := bbase (se 3 (by rfl) ⟨636233, by rfl⟩ : syracuseStep 3393245 = 1272467) (by norm_num)
theorem B2262163 : Blo 2009435 2262163 := bstep (se 1 (by rfl) ⟨1696622, by rfl⟩ : syracuseStep 2262163 = 3393245) B3393245
theorem B3016217 : Blo 2009435 3016217 := bstep (se 2 (by rfl) ⟨1131081, by rfl⟩ : syracuseStep 3016217 = 2262163) B2262163
theorem B2010811 : Blo 2009435 2010811 := bstep (se 1 (by rfl) ⟨1508108, by rfl⟩ : syracuseStep 2010811 = 3016217) B3016217
theorem B6441877 : Blo 2009435 6441877 := bbase (se 6 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 6441877 = 301963) (by norm_num)
theorem B8589169 : Blo 2009435 8589169 := bstep (se 2 (by rfl) ⟨3220938, by rfl⟩ : syracuseStep 8589169 = 6441877) B6441877
theorem B11452225 : Blo 2009435 11452225 := bstep (se 2 (by rfl) ⟨4294584, by rfl⟩ : syracuseStep 11452225 = 8589169) B8589169
theorem B15269633 : Blo 2009435 15269633 := bstep (se 2 (by rfl) ⟨5726112, by rfl⟩ : syracuseStep 15269633 = 11452225) B11452225
theorem B10179755 : Blo 2009435 10179755 := bstep (se 1 (by rfl) ⟨7634816, by rfl⟩ : syracuseStep 10179755 = 15269633) B15269633
theorem B6786503 : Blo 2009435 6786503 := bstep (se 1 (by rfl) ⟨5089877, by rfl⟩ : syracuseStep 6786503 = 10179755) B10179755
theorem B4524335 : Blo 2009435 4524335 := bstep (se 1 (by rfl) ⟨3393251, by rfl⟩ : syracuseStep 4524335 = 6786503) B6786503
theorem B3016223 : Blo 2009435 3016223 := bstep (se 1 (by rfl) ⟨2262167, by rfl⟩ : syracuseStep 3016223 = 4524335) B4524335
theorem B2010815 : Blo 2009435 2010815 := bstep (se 1 (by rfl) ⟨1508111, by rfl⟩ : syracuseStep 2010815 = 3016223) B3016223
theorem B3016229 : Blo 2009435 3016229 := bbase (se 4 (by rfl) ⟨282771, by rfl⟩ : syracuseStep 3016229 = 565543) (by norm_num)
theorem B2010819 : Blo 2009435 2010819 := bstep (se 1 (by rfl) ⟨1508114, by rfl⟩ : syracuseStep 2010819 = 3016229) B3016229
theorem B2544949 : Blo 2009435 2544949 := bbase (se 5 (by rfl) ⟨119294, by rfl⟩ : syracuseStep 2544949 = 238589) (by norm_num)
theorem B3393265 : Blo 2009435 3393265 := bstep (se 2 (by rfl) ⟨1272474, by rfl⟩ : syracuseStep 3393265 = 2544949) B2544949
theorem B4524353 : Blo 2009435 4524353 := bstep (se 2 (by rfl) ⟨1696632, by rfl⟩ : syracuseStep 4524353 = 3393265) B3393265
theorem B3016235 : Blo 2009435 3016235 := bstep (se 1 (by rfl) ⟨2262176, by rfl⟩ : syracuseStep 3016235 = 4524353) B4524353
theorem B2010823 : Blo 2009435 2010823 := bstep (se 1 (by rfl) ⟨1508117, by rfl⟩ : syracuseStep 2010823 = 3016235) B3016235
theorem B2262181 : Blo 2009435 2262181 := bbase (se 4 (by rfl) ⟨212079, by rfl⟩ : syracuseStep 2262181 = 424159) (by norm_num)
theorem B3016241 : Blo 2009435 3016241 := bstep (se 2 (by rfl) ⟨1131090, by rfl⟩ : syracuseStep 3016241 = 2262181) B2262181
theorem B2010827 : Blo 2009435 2010827 := bstep (se 1 (by rfl) ⟨1508120, by rfl⟩ : syracuseStep 2010827 = 3016241) B3016241
theorem B3869525 : Blo 2009435 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B2579683 : Blo 2009435 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B3439577 : Blo 2009435 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B2293051 : Blo 2009435 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B3057401 : Blo 2009435 3057401 := bstep (se 2 (by rfl) ⟨1146525, by rfl⟩ : syracuseStep 3057401 = 2293051) B2293051
theorem B2038267 : Blo 2009435 2038267 := bstep (se 1 (by rfl) ⟨1528700, by rfl⟩ : syracuseStep 2038267 = 3057401) B3057401
theorem B10870757 : Blo 2009435 10870757 := bstep (se 4 (by rfl) ⟨1019133, by rfl⟩ : syracuseStep 10870757 = 2038267) B2038267
theorem B7247171 : Blo 2009435 7247171 := bstep (se 1 (by rfl) ⟨5435378, by rfl⟩ : syracuseStep 7247171 = 10870757) B10870757
theorem B19325789 : Blo 2009435 19325789 := bstep (se 3 (by rfl) ⟨3623585, by rfl⟩ : syracuseStep 19325789 = 7247171) B7247171
theorem B12883859 : Blo 2009435 12883859 := bstep (se 1 (by rfl) ⟨9662894, by rfl⟩ : syracuseStep 12883859 = 19325789) B19325789
theorem B8589239 : Blo 2009435 8589239 := bstep (se 1 (by rfl) ⟨6441929, by rfl⟩ : syracuseStep 8589239 = 12883859) B12883859
theorem B5726159 : Blo 2009435 5726159 := bstep (se 1 (by rfl) ⟨4294619, by rfl⟩ : syracuseStep 5726159 = 8589239) B8589239
theorem B3817439 : Blo 2009435 3817439 := bstep (se 1 (by rfl) ⟨2863079, by rfl⟩ : syracuseStep 3817439 = 5726159) B5726159
theorem B2544959 : Blo 2009435 2544959 := bstep (se 1 (by rfl) ⟨1908719, by rfl⟩ : syracuseStep 2544959 = 3817439) B3817439
theorem B6786557 : Blo 2009435 6786557 := bstep (se 3 (by rfl) ⟨1272479, by rfl⟩ : syracuseStep 6786557 = 2544959) B2544959
theorem B4524371 : Blo 2009435 4524371 := bstep (se 1 (by rfl) ⟨3393278, by rfl⟩ : syracuseStep 4524371 = 6786557) B6786557
theorem B3016247 : Blo 2009435 3016247 := bstep (se 1 (by rfl) ⟨2262185, by rfl⟩ : syracuseStep 3016247 = 4524371) B4524371
theorem B2010831 : Blo 2009435 2010831 := bstep (se 1 (by rfl) ⟨1508123, by rfl⟩ : syracuseStep 2010831 = 3016247) B3016247
theorem B3016253 : Blo 2009435 3016253 := bbase (se 3 (by rfl) ⟨565547, by rfl⟩ : syracuseStep 3016253 = 1131095) (by norm_num)
theorem B2010835 : Blo 2009435 2010835 := bstep (se 1 (by rfl) ⟨1508126, by rfl⟩ : syracuseStep 2010835 = 3016253) B3016253
theorem B4524389 : Blo 2009435 4524389 := bbase (se 4 (by rfl) ⟨424161, by rfl⟩ : syracuseStep 4524389 = 848323) (by norm_num)
theorem B3016259 : Blo 2009435 3016259 := bstep (se 1 (by rfl) ⟨2262194, by rfl⟩ : syracuseStep 3016259 = 4524389) B4524389
theorem B2010839 : Blo 2009435 2010839 := bstep (se 1 (by rfl) ⟨1508129, by rfl⟩ : syracuseStep 2010839 = 3016259) B3016259
theorem B5089949 : Blo 2009435 5089949 := bbase (se 3 (by rfl) ⟨954365, by rfl⟩ : syracuseStep 5089949 = 1908731) (by norm_num)
theorem B3393299 : Blo 2009435 3393299 := bstep (se 1 (by rfl) ⟨2544974, by rfl⟩ : syracuseStep 3393299 = 5089949) B5089949
theorem B2262199 : Blo 2009435 2262199 := bstep (se 1 (by rfl) ⟨1696649, by rfl⟩ : syracuseStep 2262199 = 3393299) B3393299
theorem B3016265 : Blo 2009435 3016265 := bstep (se 2 (by rfl) ⟨1131099, by rfl⟩ : syracuseStep 3016265 = 2262199) B2262199
theorem B2010843 : Blo 2009435 2010843 := bstep (se 1 (by rfl) ⟨1508132, by rfl⟩ : syracuseStep 2010843 = 3016265) B3016265
theorem B3817469 : Blo 2009435 3817469 := bbase (se 3 (by rfl) ⟨715775, by rfl⟩ : syracuseStep 3817469 = 1431551) (by norm_num)
theorem B10179917 : Blo 2009435 10179917 := bstep (se 3 (by rfl) ⟨1908734, by rfl⟩ : syracuseStep 10179917 = 3817469) B3817469
theorem B6786611 : Blo 2009435 6786611 := bstep (se 1 (by rfl) ⟨5089958, by rfl⟩ : syracuseStep 6786611 = 10179917) B10179917
theorem B4524407 : Blo 2009435 4524407 := bstep (se 1 (by rfl) ⟨3393305, by rfl⟩ : syracuseStep 4524407 = 6786611) B6786611
theorem B3016271 : Blo 2009435 3016271 := bstep (se 1 (by rfl) ⟨2262203, by rfl⟩ : syracuseStep 3016271 = 4524407) B4524407
theorem B2010847 : Blo 2009435 2010847 := bstep (se 1 (by rfl) ⟨1508135, by rfl⟩ : syracuseStep 2010847 = 3016271) B3016271
theorem B3016277 : Blo 2009435 3016277 := bbase (se 8 (by rfl) ⟨17673, by rfl⟩ : syracuseStep 3016277 = 35347) (by norm_num)
theorem B2010851 : Blo 2009435 2010851 := bstep (se 1 (by rfl) ⟨1508138, by rfl⟩ : syracuseStep 2010851 = 3016277) B3016277
theorem B3623629 : Blo 2009435 3623629 := bbase (se 3 (by rfl) ⟨679430, by rfl⟩ : syracuseStep 3623629 = 1358861) (by norm_num)
theorem B4831505 : Blo 2009435 4831505 := bstep (se 2 (by rfl) ⟨1811814, by rfl⟩ : syracuseStep 4831505 = 3623629) B3623629
theorem B3221003 : Blo 2009435 3221003 := bstep (se 1 (by rfl) ⟨2415752, by rfl⟩ : syracuseStep 3221003 = 4831505) B4831505
theorem B8589341 : Blo 2009435 8589341 := bstep (se 3 (by rfl) ⟨1610501, by rfl⟩ : syracuseStep 8589341 = 3221003) B3221003
theorem B5726227 : Blo 2009435 5726227 := bstep (se 1 (by rfl) ⟨4294670, by rfl⟩ : syracuseStep 5726227 = 8589341) B8589341
theorem B7634969 : Blo 2009435 7634969 := bstep (se 2 (by rfl) ⟨2863113, by rfl⟩ : syracuseStep 7634969 = 5726227) B5726227
theorem B5089979 : Blo 2009435 5089979 := bstep (se 1 (by rfl) ⟨3817484, by rfl⟩ : syracuseStep 5089979 = 7634969) B7634969
theorem B3393319 : Blo 2009435 3393319 := bstep (se 1 (by rfl) ⟨2544989, by rfl⟩ : syracuseStep 3393319 = 5089979) B5089979
theorem B4524425 : Blo 2009435 4524425 := bstep (se 2 (by rfl) ⟨1696659, by rfl⟩ : syracuseStep 4524425 = 3393319) B3393319
theorem B3016283 : Blo 2009435 3016283 := bstep (se 1 (by rfl) ⟨2262212, by rfl⟩ : syracuseStep 3016283 = 4524425) B4524425
theorem B2010855 : Blo 2009435 2010855 := bstep (se 1 (by rfl) ⟨1508141, by rfl⟩ : syracuseStep 2010855 = 3016283) B3016283
theorem B2262217 : Blo 2009435 2262217 := bbase (se 2 (by rfl) ⟨848331, by rfl⟩ : syracuseStep 2262217 = 1696663) (by norm_num)
theorem B3016289 : Blo 2009435 3016289 := bstep (se 2 (by rfl) ⟨1131108, by rfl⟩ : syracuseStep 3016289 = 2262217) B2262217
theorem B2010859 : Blo 2009435 2010859 := bstep (se 1 (by rfl) ⟨1508144, by rfl⟩ : syracuseStep 2010859 = 3016289) B3016289
theorem B18344693 : Blo 2009435 18344693 := bbase (se 5 (by rfl) ⟨859907, by rfl⟩ : syracuseStep 18344693 = 1719815) (by norm_num)
theorem B12229795 : Blo 2009435 12229795 := bstep (se 1 (by rfl) ⟨9172346, by rfl⟩ : syracuseStep 12229795 = 18344693) B18344693
theorem B16306393 : Blo 2009435 16306393 := bstep (se 2 (by rfl) ⟨6114897, by rfl⟩ : syracuseStep 16306393 = 12229795) B12229795
theorem B21741857 : Blo 2009435 21741857 := bstep (se 2 (by rfl) ⟨8153196, by rfl⟩ : syracuseStep 21741857 = 16306393) B16306393
theorem B14494571 : Blo 2009435 14494571 := bstep (se 1 (by rfl) ⟨10870928, by rfl⟩ : syracuseStep 14494571 = 21741857) B21741857
theorem B9663047 : Blo 2009435 9663047 := bstep (se 1 (by rfl) ⟨7247285, by rfl⟩ : syracuseStep 9663047 = 14494571) B14494571
theorem B6442031 : Blo 2009435 6442031 := bstep (se 1 (by rfl) ⟨4831523, by rfl⟩ : syracuseStep 6442031 = 9663047) B9663047
theorem B17178749 : Blo 2009435 17178749 := bstep (se 3 (by rfl) ⟨3221015, by rfl⟩ : syracuseStep 17178749 = 6442031) B6442031
theorem B11452499 : Blo 2009435 11452499 := bstep (se 1 (by rfl) ⟨8589374, by rfl⟩ : syracuseStep 11452499 = 17178749) B17178749
theorem B7634999 : Blo 2009435 7634999 := bstep (se 1 (by rfl) ⟨5726249, by rfl⟩ : syracuseStep 7634999 = 11452499) B11452499
theorem B5089999 : Blo 2009435 5089999 := bstep (se 1 (by rfl) ⟨3817499, by rfl⟩ : syracuseStep 5089999 = 7634999) B7634999
theorem B6786665 : Blo 2009435 6786665 := bstep (se 2 (by rfl) ⟨2544999, by rfl⟩ : syracuseStep 6786665 = 5089999) B5089999
theorem B4524443 : Blo 2009435 4524443 := bstep (se 1 (by rfl) ⟨3393332, by rfl⟩ : syracuseStep 4524443 = 6786665) B6786665
theorem B3016295 : Blo 2009435 3016295 := bstep (se 1 (by rfl) ⟨2262221, by rfl⟩ : syracuseStep 3016295 = 4524443) B4524443
theorem B2010863 : Blo 2009435 2010863 := bstep (se 1 (by rfl) ⟨1508147, by rfl⟩ : syracuseStep 2010863 = 3016295) B3016295
theorem B3016301 : Blo 2009435 3016301 := bbase (se 3 (by rfl) ⟨565556, by rfl⟩ : syracuseStep 3016301 = 1131113) (by norm_num)
theorem B2010867 : Blo 2009435 2010867 := bstep (se 1 (by rfl) ⟨1508150, by rfl⟩ : syracuseStep 2010867 = 3016301) B3016301
theorem B4524461 : Blo 2009435 4524461 := bbase (se 3 (by rfl) ⟨848336, by rfl⟩ : syracuseStep 4524461 = 1696673) (by norm_num)
theorem B3016307 : Blo 2009435 3016307 := bstep (se 1 (by rfl) ⟨2262230, by rfl⟩ : syracuseStep 3016307 = 4524461) B4524461
theorem B2010871 : Blo 2009435 2010871 := bstep (se 1 (by rfl) ⟨1508153, by rfl⟩ : syracuseStep 2010871 = 3016307) B3016307
theorem B2147357 : Blo 2009435 2147357 := bbase (se 3 (by rfl) ⟨402629, by rfl⟩ : syracuseStep 2147357 = 805259) (by norm_num)
theorem B5726285 : Blo 2009435 5726285 := bstep (se 3 (by rfl) ⟨1073678, by rfl⟩ : syracuseStep 5726285 = 2147357) B2147357
theorem B3817523 : Blo 2009435 3817523 := bstep (se 1 (by rfl) ⟨2863142, by rfl⟩ : syracuseStep 3817523 = 5726285) B5726285
theorem B2545015 : Blo 2009435 2545015 := bstep (se 1 (by rfl) ⟨1908761, by rfl⟩ : syracuseStep 2545015 = 3817523) B3817523
theorem B3393353 : Blo 2009435 3393353 := bstep (se 2 (by rfl) ⟨1272507, by rfl⟩ : syracuseStep 3393353 = 2545015) B2545015
theorem B2262235 : Blo 2009435 2262235 := bstep (se 1 (by rfl) ⟨1696676, by rfl⟩ : syracuseStep 2262235 = 3393353) B3393353
theorem B3016313 : Blo 2009435 3016313 := bstep (se 2 (by rfl) ⟨1131117, by rfl⟩ : syracuseStep 3016313 = 2262235) B2262235
theorem B2010875 : Blo 2009435 2010875 := bstep (se 1 (by rfl) ⟨1508156, by rfl⟩ : syracuseStep 2010875 = 3016313) B3016313
theorem B2293105 : Blo 2009435 2293105 := bbase (se 2 (by rfl) ⟨859914, by rfl⟩ : syracuseStep 2293105 = 1719829) (by norm_num)
theorem B3057473 : Blo 2009435 3057473 := bstep (se 2 (by rfl) ⟨1146552, by rfl⟩ : syracuseStep 3057473 = 2293105) B2293105
theorem B2038315 : Blo 2009435 2038315 := bstep (se 1 (by rfl) ⟨1528736, by rfl⟩ : syracuseStep 2038315 = 3057473) B3057473
theorem B43484053 : Blo 2009435 43484053 := bstep (se 6 (by rfl) ⟨1019157, by rfl⟩ : syracuseStep 43484053 = 2038315) B2038315
theorem B57978737 : Blo 2009435 57978737 := bstep (se 2 (by rfl) ⟨21742026, by rfl⟩ : syracuseStep 57978737 = 43484053) B43484053
theorem B38652491 : Blo 2009435 38652491 := bstep (se 1 (by rfl) ⟨28989368, by rfl⟩ : syracuseStep 38652491 = 57978737) B57978737
theorem B25768327 : Blo 2009435 25768327 := bstep (se 1 (by rfl) ⟨19326245, by rfl⟩ : syracuseStep 25768327 = 38652491) B38652491
theorem B34357769 : Blo 2009435 34357769 := bstep (se 2 (by rfl) ⟨12884163, by rfl⟩ : syracuseStep 34357769 = 25768327) B25768327
theorem B22905179 : Blo 2009435 22905179 := bstep (se 1 (by rfl) ⟨17178884, by rfl⟩ : syracuseStep 22905179 = 34357769) B34357769
theorem B15270119 : Blo 2009435 15270119 := bstep (se 1 (by rfl) ⟨11452589, by rfl⟩ : syracuseStep 15270119 = 22905179) B22905179
theorem B10180079 : Blo 2009435 10180079 := bstep (se 1 (by rfl) ⟨7635059, by rfl⟩ : syracuseStep 10180079 = 15270119) B15270119
theorem B6786719 : Blo 2009435 6786719 := bstep (se 1 (by rfl) ⟨5090039, by rfl⟩ : syracuseStep 6786719 = 10180079) B10180079
theorem B4524479 : Blo 2009435 4524479 := bstep (se 1 (by rfl) ⟨3393359, by rfl⟩ : syracuseStep 4524479 = 6786719) B6786719
theorem B3016319 : Blo 2009435 3016319 := bstep (se 1 (by rfl) ⟨2262239, by rfl⟩ : syracuseStep 3016319 = 4524479) B4524479
theorem B2010879 : Blo 2009435 2010879 := bstep (se 1 (by rfl) ⟨1508159, by rfl⟩ : syracuseStep 2010879 = 3016319) B3016319
theorem B3016325 : Blo 2009435 3016325 := bbase (se 4 (by rfl) ⟨282780, by rfl⟩ : syracuseStep 3016325 = 565561) (by norm_num)
theorem B2010883 : Blo 2009435 2010883 := bstep (se 1 (by rfl) ⟨1508162, by rfl⟩ : syracuseStep 2010883 = 3016325) B3016325
theorem B3393373 : Blo 2009435 3393373 := bbase (se 3 (by rfl) ⟨636257, by rfl⟩ : syracuseStep 3393373 = 1272515) (by norm_num)
theorem B4524497 : Blo 2009435 4524497 := bstep (se 2 (by rfl) ⟨1696686, by rfl⟩ : syracuseStep 4524497 = 3393373) B3393373
theorem B3016331 : Blo 2009435 3016331 := bstep (se 1 (by rfl) ⟨2262248, by rfl⟩ : syracuseStep 3016331 = 4524497) B4524497
theorem B2010887 : Blo 2009435 2010887 := bstep (se 1 (by rfl) ⟨1508165, by rfl⟩ : syracuseStep 2010887 = 3016331) B3016331
theorem B2262253 : Blo 2009435 2262253 := bbase (se 3 (by rfl) ⟨424172, by rfl⟩ : syracuseStep 2262253 = 848345) (by norm_num)
theorem B3016337 : Blo 2009435 3016337 := bstep (se 2 (by rfl) ⟨1131126, by rfl⟩ : syracuseStep 3016337 = 2262253) B2262253
theorem B2010891 : Blo 2009435 2010891 := bstep (se 1 (by rfl) ⟨1508168, by rfl⟩ : syracuseStep 2010891 = 3016337) B3016337
theorem B6786773 : Blo 2009435 6786773 := bbase (se 7 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 6786773 = 159065) (by norm_num)
theorem B4524515 : Blo 2009435 4524515 := bstep (se 1 (by rfl) ⟨3393386, by rfl⟩ : syracuseStep 4524515 = 6786773) B6786773
theorem B3016343 : Blo 2009435 3016343 := bstep (se 1 (by rfl) ⟨2262257, by rfl⟩ : syracuseStep 3016343 = 4524515) B4524515
theorem B2010895 : Blo 2009435 2010895 := bstep (se 1 (by rfl) ⟨1508171, by rfl⟩ : syracuseStep 2010895 = 3016343) B3016343
theorem B3016349 : Blo 2009435 3016349 := bbase (se 3 (by rfl) ⟨565565, by rfl⟩ : syracuseStep 3016349 = 1131131) (by norm_num)
theorem B2010899 : Blo 2009435 2010899 := bstep (se 1 (by rfl) ⟨1508174, by rfl⟩ : syracuseStep 2010899 = 3016349) B3016349
theorem B4524533 : Blo 2009435 4524533 := bbase (se 5 (by rfl) ⟨212087, by rfl⟩ : syracuseStep 4524533 = 424175) (by norm_num)
theorem B3016355 : Blo 2009435 3016355 := bstep (se 1 (by rfl) ⟨2262266, by rfl⟩ : syracuseStep 3016355 = 4524533) B4524533
theorem B2010903 : Blo 2009435 2010903 := bstep (se 1 (by rfl) ⟨1508177, by rfl⟩ : syracuseStep 2010903 = 3016355) B3016355
theorem B4132309 : Blo 2009435 4132309 := bbase (se 7 (by rfl) ⟨48425, by rfl⟩ : syracuseStep 4132309 = 96851) (by norm_num)
theorem B5509745 : Blo 2009435 5509745 := bstep (se 2 (by rfl) ⟨2066154, by rfl⟩ : syracuseStep 5509745 = 4132309) B4132309
theorem B3673163 : Blo 2009435 3673163 := bstep (se 1 (by rfl) ⟨2754872, by rfl⟩ : syracuseStep 3673163 = 5509745) B5509745
theorem B2448775 : Blo 2009435 2448775 := bstep (se 1 (by rfl) ⟨1836581, by rfl⟩ : syracuseStep 2448775 = 3673163) B3673163
theorem B13060133 : Blo 2009435 13060133 := bstep (se 4 (by rfl) ⟨1224387, by rfl⟩ : syracuseStep 13060133 = 2448775) B2448775
theorem B8706755 : Blo 2009435 8706755 := bstep (se 1 (by rfl) ⟨6530066, by rfl⟩ : syracuseStep 8706755 = 13060133) B13060133
theorem B5804503 : Blo 2009435 5804503 := bstep (se 1 (by rfl) ⟨4353377, by rfl⟩ : syracuseStep 5804503 = 8706755) B8706755
theorem B123829397 : Blo 2009435 123829397 := bstep (se 6 (by rfl) ⟨2902251, by rfl⟩ : syracuseStep 123829397 = 5804503) B5804503
theorem B82552931 : Blo 2009435 82552931 := bstep (se 1 (by rfl) ⟨61914698, by rfl⟩ : syracuseStep 82552931 = 123829397) B123829397
theorem B55035287 : Blo 2009435 55035287 := bstep (se 1 (by rfl) ⟨41276465, by rfl⟩ : syracuseStep 55035287 = 82552931) B82552931
theorem B36690191 : Blo 2009435 36690191 := bstep (se 1 (by rfl) ⟨27517643, by rfl⟩ : syracuseStep 36690191 = 55035287) B55035287
theorem B24460127 : Blo 2009435 24460127 := bstep (se 1 (by rfl) ⟨18345095, by rfl⟩ : syracuseStep 24460127 = 36690191) B36690191
theorem B16306751 : Blo 2009435 16306751 := bstep (se 1 (by rfl) ⟨12230063, by rfl⟩ : syracuseStep 16306751 = 24460127) B24460127
theorem B10871167 : Blo 2009435 10871167 := bstep (se 1 (by rfl) ⟨8153375, by rfl⟩ : syracuseStep 10871167 = 16306751) B16306751
theorem B14494889 : Blo 2009435 14494889 := bstep (se 2 (by rfl) ⟨5435583, by rfl⟩ : syracuseStep 14494889 = 10871167) B10871167
theorem B38653037 : Blo 2009435 38653037 := bstep (se 3 (by rfl) ⟨7247444, by rfl⟩ : syracuseStep 38653037 = 14494889) B14494889
theorem B25768691 : Blo 2009435 25768691 := bstep (se 1 (by rfl) ⟨19326518, by rfl⟩ : syracuseStep 25768691 = 38653037) B38653037
theorem B17179127 : Blo 2009435 17179127 := bstep (se 1 (by rfl) ⟨12884345, by rfl⟩ : syracuseStep 17179127 = 25768691) B25768691
theorem B11452751 : Blo 2009435 11452751 := bstep (se 1 (by rfl) ⟨8589563, by rfl⟩ : syracuseStep 11452751 = 17179127) B17179127
theorem B7635167 : Blo 2009435 7635167 := bstep (se 1 (by rfl) ⟨5726375, by rfl⟩ : syracuseStep 7635167 = 11452751) B11452751
theorem B5090111 : Blo 2009435 5090111 := bstep (se 1 (by rfl) ⟨3817583, by rfl⟩ : syracuseStep 5090111 = 7635167) B7635167
theorem B3393407 : Blo 2009435 3393407 := bstep (se 1 (by rfl) ⟨2545055, by rfl⟩ : syracuseStep 3393407 = 5090111) B5090111
theorem B2262271 : Blo 2009435 2262271 := bstep (se 1 (by rfl) ⟨1696703, by rfl⟩ : syracuseStep 2262271 = 3393407) B3393407
theorem B3016361 : Blo 2009435 3016361 := bstep (se 2 (by rfl) ⟨1131135, by rfl⟩ : syracuseStep 3016361 = 2262271) B2262271
theorem B2010907 : Blo 2009435 2010907 := bstep (se 1 (by rfl) ⟨1508180, by rfl⟩ : syracuseStep 2010907 = 3016361) B3016361
theorem B3221093 : Blo 2009435 3221093 := bbase (se 4 (by rfl) ⟨301977, by rfl⟩ : syracuseStep 3221093 = 603955) (by norm_num)
theorem B2147395 : Blo 2009435 2147395 := bstep (se 1 (by rfl) ⟨1610546, by rfl⟩ : syracuseStep 2147395 = 3221093) B3221093
theorem B2863193 : Blo 2009435 2863193 := bstep (se 2 (by rfl) ⟨1073697, by rfl⟩ : syracuseStep 2863193 = 2147395) B2147395
theorem B7635181 : Blo 2009435 7635181 := bstep (se 3 (by rfl) ⟨1431596, by rfl⟩ : syracuseStep 7635181 = 2863193) B2863193
theorem B10180241 : Blo 2009435 10180241 := bstep (se 2 (by rfl) ⟨3817590, by rfl⟩ : syracuseStep 10180241 = 7635181) B7635181
theorem B6786827 : Blo 2009435 6786827 := bstep (se 1 (by rfl) ⟨5090120, by rfl⟩ : syracuseStep 6786827 = 10180241) B10180241
theorem B4524551 : Blo 2009435 4524551 := bstep (se 1 (by rfl) ⟨3393413, by rfl⟩ : syracuseStep 4524551 = 6786827) B6786827
theorem B3016367 : Blo 2009435 3016367 := bstep (se 1 (by rfl) ⟨2262275, by rfl⟩ : syracuseStep 3016367 = 4524551) B4524551
theorem B2010911 : Blo 2009435 2010911 := bstep (se 1 (by rfl) ⟨1508183, by rfl⟩ : syracuseStep 2010911 = 3016367) B3016367
theorem B3016373 : Blo 2009435 3016373 := bbase (se 5 (by rfl) ⟨141392, by rfl⟩ : syracuseStep 3016373 = 282785) (by norm_num)
theorem B2010915 : Blo 2009435 2010915 := bstep (se 1 (by rfl) ⟨1508186, by rfl⟩ : syracuseStep 2010915 = 3016373) B3016373
theorem B5090141 : Blo 2009435 5090141 := bbase (se 3 (by rfl) ⟨954401, by rfl⟩ : syracuseStep 5090141 = 1908803) (by norm_num)
theorem B3393427 : Blo 2009435 3393427 := bstep (se 1 (by rfl) ⟨2545070, by rfl⟩ : syracuseStep 3393427 = 5090141) B5090141
theorem B4524569 : Blo 2009435 4524569 := bstep (se 2 (by rfl) ⟨1696713, by rfl⟩ : syracuseStep 4524569 = 3393427) B3393427
theorem B3016379 : Blo 2009435 3016379 := bstep (se 1 (by rfl) ⟨2262284, by rfl⟩ : syracuseStep 3016379 = 4524569) B4524569
theorem B2010919 : Blo 2009435 2010919 := bstep (se 1 (by rfl) ⟨1508189, by rfl⟩ : syracuseStep 2010919 = 3016379) B3016379
theorem B2262289 : Blo 2009435 2262289 := bbase (se 2 (by rfl) ⟨848358, by rfl⟩ : syracuseStep 2262289 = 1696717) (by norm_num)
theorem B3016385 : Blo 2009435 3016385 := bstep (se 2 (by rfl) ⟨1131144, by rfl⟩ : syracuseStep 3016385 = 2262289) B2262289
theorem B2010923 : Blo 2009435 2010923 := bstep (se 1 (by rfl) ⟨1508192, by rfl⟩ : syracuseStep 2010923 = 3016385) B3016385
theorem B3817621 : Blo 2009435 3817621 := bbase (se 6 (by rfl) ⟨89475, by rfl⟩ : syracuseStep 3817621 = 178951) (by norm_num)
theorem B5090161 : Blo 2009435 5090161 := bstep (se 2 (by rfl) ⟨1908810, by rfl⟩ : syracuseStep 5090161 = 3817621) B3817621
theorem B6786881 : Blo 2009435 6786881 := bstep (se 2 (by rfl) ⟨2545080, by rfl⟩ : syracuseStep 6786881 = 5090161) B5090161
theorem B4524587 : Blo 2009435 4524587 := bstep (se 1 (by rfl) ⟨3393440, by rfl⟩ : syracuseStep 4524587 = 6786881) B6786881
theorem B3016391 : Blo 2009435 3016391 := bstep (se 1 (by rfl) ⟨2262293, by rfl⟩ : syracuseStep 3016391 = 4524587) B4524587
theorem B2010927 : Blo 2009435 2010927 := bstep (se 1 (by rfl) ⟨1508195, by rfl⟩ : syracuseStep 2010927 = 3016391) B3016391
theorem B3016397 : Blo 2009435 3016397 := bbase (se 3 (by rfl) ⟨565574, by rfl⟩ : syracuseStep 3016397 = 1131149) (by norm_num)
theorem B2010931 : Blo 2009435 2010931 := bstep (se 1 (by rfl) ⟨1508198, by rfl⟩ : syracuseStep 2010931 = 3016397) B3016397
theorem B4524605 : Blo 2009435 4524605 := bbase (se 3 (by rfl) ⟨848363, by rfl⟩ : syracuseStep 4524605 = 1696727) (by norm_num)
theorem B3016403 : Blo 2009435 3016403 := bstep (se 1 (by rfl) ⟨2262302, by rfl⟩ : syracuseStep 3016403 = 4524605) B4524605
theorem B2010935 : Blo 2009435 2010935 := bstep (se 1 (by rfl) ⟨1508201, by rfl⟩ : syracuseStep 2010935 = 3016403) B3016403
theorem B3393461 : Blo 2009435 3393461 := bbase (se 5 (by rfl) ⟨159068, by rfl⟩ : syracuseStep 3393461 = 318137) (by norm_num)
theorem B2262307 : Blo 2009435 2262307 := bstep (se 1 (by rfl) ⟨1696730, by rfl⟩ : syracuseStep 2262307 = 3393461) B3393461
theorem B3016409 : Blo 2009435 3016409 := bstep (se 2 (by rfl) ⟨1131153, by rfl⟩ : syracuseStep 3016409 = 2262307) B2262307
theorem B2010939 : Blo 2009435 2010939 := bstep (se 1 (by rfl) ⟨1508204, by rfl⟩ : syracuseStep 2010939 = 3016409) B3016409
theorem B2147429 : Blo 2009435 2147429 := bbase (se 4 (by rfl) ⟨201321, by rfl⟩ : syracuseStep 2147429 = 402643) (by norm_num)
theorem B5726477 : Blo 2009435 5726477 := bstep (se 3 (by rfl) ⟨1073714, by rfl⟩ : syracuseStep 5726477 = 2147429) B2147429
theorem B15270605 : Blo 2009435 15270605 := bstep (se 3 (by rfl) ⟨2863238, by rfl⟩ : syracuseStep 15270605 = 5726477) B5726477
theorem B10180403 : Blo 2009435 10180403 := bstep (se 1 (by rfl) ⟨7635302, by rfl⟩ : syracuseStep 10180403 = 15270605) B15270605
theorem B6786935 : Blo 2009435 6786935 := bstep (se 1 (by rfl) ⟨5090201, by rfl⟩ : syracuseStep 6786935 = 10180403) B10180403
theorem B4524623 : Blo 2009435 4524623 := bstep (se 1 (by rfl) ⟨3393467, by rfl⟩ : syracuseStep 4524623 = 6786935) B6786935
theorem B3016415 : Blo 2009435 3016415 := bstep (se 1 (by rfl) ⟨2262311, by rfl⟩ : syracuseStep 3016415 = 4524623) B4524623
theorem B2010943 : Blo 2009435 2010943 := bstep (se 1 (by rfl) ⟨1508207, by rfl⟩ : syracuseStep 2010943 = 3016415) B3016415
theorem B3016421 : Blo 2009435 3016421 := bbase (se 4 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 3016421 = 565579) (by norm_num)
theorem B2010947 : Blo 2009435 2010947 := bstep (se 1 (by rfl) ⟨1508210, by rfl⟩ : syracuseStep 2010947 = 3016421) B3016421
theorem B5726501 : Blo 2009435 5726501 := bbase (se 4 (by rfl) ⟨536859, by rfl⟩ : syracuseStep 5726501 = 1073719) (by norm_num)
theorem B3817667 : Blo 2009435 3817667 := bstep (se 1 (by rfl) ⟨2863250, by rfl⟩ : syracuseStep 3817667 = 5726501) B5726501
theorem B2545111 : Blo 2009435 2545111 := bstep (se 1 (by rfl) ⟨1908833, by rfl⟩ : syracuseStep 2545111 = 3817667) B3817667
theorem B3393481 : Blo 2009435 3393481 := bstep (se 2 (by rfl) ⟨1272555, by rfl⟩ : syracuseStep 3393481 = 2545111) B2545111
theorem B4524641 : Blo 2009435 4524641 := bstep (se 2 (by rfl) ⟨1696740, by rfl⟩ : syracuseStep 4524641 = 3393481) B3393481
theorem B3016427 : Blo 2009435 3016427 := bstep (se 1 (by rfl) ⟨2262320, by rfl⟩ : syracuseStep 3016427 = 4524641) B4524641
theorem B2010951 : Blo 2009435 2010951 := bstep (se 1 (by rfl) ⟨1508213, by rfl⟩ : syracuseStep 2010951 = 3016427) B3016427
theorem B2262325 : Blo 2009435 2262325 := bbase (se 5 (by rfl) ⟨106046, by rfl⟩ : syracuseStep 2262325 = 212093) (by norm_num)
theorem B3016433 : Blo 2009435 3016433 := bstep (se 2 (by rfl) ⟨1131162, by rfl⟩ : syracuseStep 3016433 = 2262325) B2262325
theorem B2010955 : Blo 2009435 2010955 := bstep (se 1 (by rfl) ⟨1508216, by rfl⟩ : syracuseStep 2010955 = 3016433) B3016433
theorem B2545121 : Blo 2009435 2545121 := bbase (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) (by norm_num)
theorem B6786989 : Blo 2009435 6786989 := bstep (se 3 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 6786989 = 2545121) B2545121
theorem B4524659 : Blo 2009435 4524659 := bstep (se 1 (by rfl) ⟨3393494, by rfl⟩ : syracuseStep 4524659 = 6786989) B6786989
theorem B3016439 : Blo 2009435 3016439 := bstep (se 1 (by rfl) ⟨2262329, by rfl⟩ : syracuseStep 3016439 = 4524659) B4524659
theorem B2010959 : Blo 2009435 2010959 := bstep (se 1 (by rfl) ⟨1508219, by rfl⟩ : syracuseStep 2010959 = 3016439) B3016439
theorem B3016445 : Blo 2009435 3016445 := bbase (se 3 (by rfl) ⟨565583, by rfl⟩ : syracuseStep 3016445 = 1131167) (by norm_num)
theorem B2010963 : Blo 2009435 2010963 := bstep (se 1 (by rfl) ⟨1508222, by rfl⟩ : syracuseStep 2010963 = 3016445) B3016445
theorem B4524677 : Blo 2009435 4524677 := bbase (se 4 (by rfl) ⟨424188, by rfl⟩ : syracuseStep 4524677 = 848377) (by norm_num)
theorem B3016451 : Blo 2009435 3016451 := bstep (se 1 (by rfl) ⟨2262338, by rfl⟩ : syracuseStep 3016451 = 4524677) B4524677
theorem B2010967 : Blo 2009435 2010967 := bstep (se 1 (by rfl) ⟨1508225, by rfl⟩ : syracuseStep 2010967 = 3016451) B3016451
theorem B5804693 : Blo 2009435 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B3869795 : Blo 2009435 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B2579863 : Blo 2009435 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B3439817 : Blo 2009435 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B2293211 : Blo 2009435 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B6115229 : Blo 2009435 6115229 := bstep (se 3 (by rfl) ⟨1146605, by rfl⟩ : syracuseStep 6115229 = 2293211) B2293211
theorem B4076819 : Blo 2009435 4076819 := bstep (se 1 (by rfl) ⟨3057614, by rfl⟩ : syracuseStep 4076819 = 6115229) B6115229
theorem B2717879 : Blo 2009435 2717879 := bstep (se 1 (by rfl) ⟨2038409, by rfl⟩ : syracuseStep 2717879 = 4076819) B4076819
theorem B7247677 : Blo 2009435 7247677 := bstep (se 3 (by rfl) ⟨1358939, by rfl⟩ : syracuseStep 7247677 = 2717879) B2717879
theorem B9663569 : Blo 2009435 9663569 := bstep (se 2 (by rfl) ⟨3623838, by rfl⟩ : syracuseStep 9663569 = 7247677) B7247677
theorem B6442379 : Blo 2009435 6442379 := bstep (se 1 (by rfl) ⟨4831784, by rfl⟩ : syracuseStep 6442379 = 9663569) B9663569
theorem B4294919 : Blo 2009435 4294919 := bstep (se 1 (by rfl) ⟨3221189, by rfl⟩ : syracuseStep 4294919 = 6442379) B6442379
theorem B2863279 : Blo 2009435 2863279 := bstep (se 1 (by rfl) ⟨2147459, by rfl⟩ : syracuseStep 2863279 = 4294919) B4294919
theorem B3817705 : Blo 2009435 3817705 := bstep (se 2 (by rfl) ⟨1431639, by rfl⟩ : syracuseStep 3817705 = 2863279) B2863279
theorem B5090273 : Blo 2009435 5090273 := bstep (se 2 (by rfl) ⟨1908852, by rfl⟩ : syracuseStep 5090273 = 3817705) B3817705
theorem B3393515 : Blo 2009435 3393515 := bstep (se 1 (by rfl) ⟨2545136, by rfl⟩ : syracuseStep 3393515 = 5090273) B5090273
theorem B2262343 : Blo 2009435 2262343 := bstep (se 1 (by rfl) ⟨1696757, by rfl⟩ : syracuseStep 2262343 = 3393515) B3393515
theorem B3016457 : Blo 2009435 3016457 := bstep (se 2 (by rfl) ⟨1131171, by rfl⟩ : syracuseStep 3016457 = 2262343) B2262343
theorem B2010971 : Blo 2009435 2010971 := bstep (se 1 (by rfl) ⟨1508228, by rfl⟩ : syracuseStep 2010971 = 3016457) B3016457
theorem B10180565 : Blo 2009435 10180565 := bbase (se 7 (by rfl) ⟨119303, by rfl⟩ : syracuseStep 10180565 = 238607) (by norm_num)
theorem B6787043 : Blo 2009435 6787043 := bstep (se 1 (by rfl) ⟨5090282, by rfl⟩ : syracuseStep 6787043 = 10180565) B10180565
theorem B4524695 : Blo 2009435 4524695 := bstep (se 1 (by rfl) ⟨3393521, by rfl⟩ : syracuseStep 4524695 = 6787043) B6787043
theorem B3016463 : Blo 2009435 3016463 := bstep (se 1 (by rfl) ⟨2262347, by rfl⟩ : syracuseStep 3016463 = 4524695) B4524695
theorem B2010975 : Blo 2009435 2010975 := bstep (se 1 (by rfl) ⟨1508231, by rfl⟩ : syracuseStep 2010975 = 3016463) B3016463
theorem B3016469 : Blo 2009435 3016469 := bbase (se 6 (by rfl) ⟨70698, by rfl⟩ : syracuseStep 3016469 = 141397) (by norm_num)
theorem B2010979 : Blo 2009435 2010979 := bstep (se 1 (by rfl) ⟨1508234, by rfl⟩ : syracuseStep 2010979 = 3016469) B3016469
theorem B17414165 : Blo 2009435 17414165 := bbase (se 6 (by rfl) ⟨408144, by rfl⟩ : syracuseStep 17414165 = 816289) (by norm_num)
theorem B11609443 : Blo 2009435 11609443 := bstep (se 1 (by rfl) ⟨8707082, by rfl⟩ : syracuseStep 11609443 = 17414165) B17414165
theorem B61917029 : Blo 2009435 61917029 := bstep (se 4 (by rfl) ⟨5804721, by rfl⟩ : syracuseStep 61917029 = 11609443) B11609443
theorem B41278019 : Blo 2009435 41278019 := bstep (se 1 (by rfl) ⟨30958514, by rfl⟩ : syracuseStep 41278019 = 61917029) B61917029
theorem B110074717 : Blo 2009435 110074717 := bstep (se 3 (by rfl) ⟨20639009, by rfl⟩ : syracuseStep 110074717 = 41278019) B41278019
theorem B146766289 : Blo 2009435 146766289 := bstep (se 2 (by rfl) ⟨55037358, by rfl⟩ : syracuseStep 146766289 = 110074717) B110074717
theorem B195688385 : Blo 2009435 195688385 := bstep (se 2 (by rfl) ⟨73383144, by rfl⟩ : syracuseStep 195688385 = 146766289) B146766289
theorem B130458923 : Blo 2009435 130458923 := bstep (se 1 (by rfl) ⟨97844192, by rfl⟩ : syracuseStep 130458923 = 195688385) B195688385
theorem B86972615 : Blo 2009435 86972615 := bstep (se 1 (by rfl) ⟨65229461, by rfl⟩ : syracuseStep 86972615 = 130458923) B130458923
theorem B57981743 : Blo 2009435 57981743 := bstep (se 1 (by rfl) ⟨43486307, by rfl⟩ : syracuseStep 57981743 = 86972615) B86972615
theorem B38654495 : Blo 2009435 38654495 := bstep (se 1 (by rfl) ⟨28990871, by rfl⟩ : syracuseStep 38654495 = 57981743) B57981743
theorem B25769663 : Blo 2009435 25769663 := bstep (se 1 (by rfl) ⟨19327247, by rfl⟩ : syracuseStep 25769663 = 38654495) B38654495
theorem B17179775 : Blo 2009435 17179775 := bstep (se 1 (by rfl) ⟨12884831, by rfl⟩ : syracuseStep 17179775 = 25769663) B25769663
theorem B11453183 : Blo 2009435 11453183 := bstep (se 1 (by rfl) ⟨8589887, by rfl⟩ : syracuseStep 11453183 = 17179775) B17179775
theorem B7635455 : Blo 2009435 7635455 := bstep (se 1 (by rfl) ⟨5726591, by rfl⟩ : syracuseStep 7635455 = 11453183) B11453183
theorem B5090303 : Blo 2009435 5090303 := bstep (se 1 (by rfl) ⟨3817727, by rfl⟩ : syracuseStep 5090303 = 7635455) B7635455
theorem B3393535 : Blo 2009435 3393535 := bstep (se 1 (by rfl) ⟨2545151, by rfl⟩ : syracuseStep 3393535 = 5090303) B5090303
theorem B4524713 : Blo 2009435 4524713 := bstep (se 2 (by rfl) ⟨1696767, by rfl⟩ : syracuseStep 4524713 = 3393535) B3393535
theorem B3016475 : Blo 2009435 3016475 := bstep (se 1 (by rfl) ⟨2262356, by rfl⟩ : syracuseStep 3016475 = 4524713) B4524713
theorem B2010983 : Blo 2009435 2010983 := bstep (se 1 (by rfl) ⟨1508237, by rfl⟩ : syracuseStep 2010983 = 3016475) B3016475
theorem B2262361 : Blo 2009435 2262361 := bbase (se 2 (by rfl) ⟨848385, by rfl⟩ : syracuseStep 2262361 = 1696771) (by norm_num)
theorem B3016481 : Blo 2009435 3016481 := bstep (se 2 (by rfl) ⟨1131180, by rfl⟩ : syracuseStep 3016481 = 2262361) B2262361
theorem B2010987 : Blo 2009435 2010987 := bstep (se 1 (by rfl) ⟨1508240, by rfl⟩ : syracuseStep 2010987 = 3016481) B3016481
theorem B3221221 : Blo 2009435 3221221 := bbase (se 4 (by rfl) ⟨301989, by rfl⟩ : syracuseStep 3221221 = 603979) (by norm_num)
theorem B4294961 : Blo 2009435 4294961 := bstep (se 2 (by rfl) ⟨1610610, by rfl⟩ : syracuseStep 4294961 = 3221221) B3221221
theorem B2863307 : Blo 2009435 2863307 := bstep (se 1 (by rfl) ⟨2147480, by rfl⟩ : syracuseStep 2863307 = 4294961) B4294961
theorem B7635485 : Blo 2009435 7635485 := bstep (se 3 (by rfl) ⟨1431653, by rfl⟩ : syracuseStep 7635485 = 2863307) B2863307
theorem B5090323 : Blo 2009435 5090323 := bstep (se 1 (by rfl) ⟨3817742, by rfl⟩ : syracuseStep 5090323 = 7635485) B7635485
theorem B6787097 : Blo 2009435 6787097 := bstep (se 2 (by rfl) ⟨2545161, by rfl⟩ : syracuseStep 6787097 = 5090323) B5090323
theorem B4524731 : Blo 2009435 4524731 := bstep (se 1 (by rfl) ⟨3393548, by rfl⟩ : syracuseStep 4524731 = 6787097) B6787097
theorem B3016487 : Blo 2009435 3016487 := bstep (se 1 (by rfl) ⟨2262365, by rfl⟩ : syracuseStep 3016487 = 4524731) B4524731
theorem B2010991 : Blo 2009435 2010991 := bstep (se 1 (by rfl) ⟨1508243, by rfl⟩ : syracuseStep 2010991 = 3016487) B3016487
theorem B3016493 : Blo 2009435 3016493 := bbase (se 3 (by rfl) ⟨565592, by rfl⟩ : syracuseStep 3016493 = 1131185) (by norm_num)
theorem B2010995 : Blo 2009435 2010995 := bstep (se 1 (by rfl) ⟨1508246, by rfl⟩ : syracuseStep 2010995 = 3016493) B3016493
theorem B4524749 : Blo 2009435 4524749 := bbase (se 3 (by rfl) ⟨848390, by rfl⟩ : syracuseStep 4524749 = 1696781) (by norm_num)
theorem B3016499 : Blo 2009435 3016499 := bstep (se 1 (by rfl) ⟨2262374, by rfl⟩ : syracuseStep 3016499 = 4524749) B4524749
theorem B2010999 : Blo 2009435 2010999 := bstep (se 1 (by rfl) ⟨1508249, by rfl⟩ : syracuseStep 2010999 = 3016499) B3016499
theorem B2545177 : Blo 2009435 2545177 := bbase (se 2 (by rfl) ⟨954441, by rfl⟩ : syracuseStep 2545177 = 1908883) (by norm_num)
theorem B3393569 : Blo 2009435 3393569 := bstep (se 2 (by rfl) ⟨1272588, by rfl⟩ : syracuseStep 3393569 = 2545177) B2545177
theorem B2262379 : Blo 2009435 2262379 := bstep (se 1 (by rfl) ⟨1696784, by rfl⟩ : syracuseStep 2262379 = 3393569) B3393569
theorem B3016505 : Blo 2009435 3016505 := bstep (se 2 (by rfl) ⟨1131189, by rfl⟩ : syracuseStep 3016505 = 2262379) B2262379
theorem B2011003 : Blo 2009435 2011003 := bstep (se 1 (by rfl) ⟨1508252, by rfl⟩ : syracuseStep 2011003 = 3016505) B3016505
theorem B8589989 : Blo 2009435 8589989 := bbase (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) (by norm_num)
theorem B22906637 : Blo 2009435 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B15271091 : Blo 2009435 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B10180727 : Blo 2009435 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B6787151 : Blo 2009435 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B4524767 : Blo 2009435 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B3016511 : Blo 2009435 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B2011007 : Blo 2009435 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B3016517 : Blo 2009435 3016517 := bbase (se 4 (by rfl) ⟨282798, by rfl⟩ : syracuseStep 3016517 = 565597) (by norm_num)
theorem B2011011 : Blo 2009435 2011011 := bstep (se 1 (by rfl) ⟨1508258, by rfl⟩ : syracuseStep 2011011 = 3016517) B3016517
theorem B3393589 : Blo 2009435 3393589 := bbase (se 5 (by rfl) ⟨159074, by rfl⟩ : syracuseStep 3393589 = 318149) (by norm_num)
theorem B4524785 : Blo 2009435 4524785 := bstep (se 2 (by rfl) ⟨1696794, by rfl⟩ : syracuseStep 4524785 = 3393589) B3393589
theorem B3016523 : Blo 2009435 3016523 := bstep (se 1 (by rfl) ⟨2262392, by rfl⟩ : syracuseStep 3016523 = 4524785) B4524785
theorem B2011015 : Blo 2009435 2011015 := bstep (se 1 (by rfl) ⟨1508261, by rfl⟩ : syracuseStep 2011015 = 3016523) B3016523
theorem B2262397 : Blo 2009435 2262397 := bbase (se 3 (by rfl) ⟨424199, by rfl⟩ : syracuseStep 2262397 = 848399) (by norm_num)
theorem B3016529 : Blo 2009435 3016529 := bstep (se 2 (by rfl) ⟨1131198, by rfl⟩ : syracuseStep 3016529 = 2262397) B2262397
theorem B2011019 : Blo 2009435 2011019 := bstep (se 1 (by rfl) ⟨1508264, by rfl⟩ : syracuseStep 2011019 = 3016529) B3016529
theorem B6787205 : Blo 2009435 6787205 := bbase (se 4 (by rfl) ⟨636300, by rfl⟩ : syracuseStep 6787205 = 1272601) (by norm_num)
theorem B4524803 : Blo 2009435 4524803 := bstep (se 1 (by rfl) ⟨3393602, by rfl⟩ : syracuseStep 4524803 = 6787205) B6787205
theorem B3016535 : Blo 2009435 3016535 := bstep (se 1 (by rfl) ⟨2262401, by rfl⟩ : syracuseStep 3016535 = 4524803) B4524803
theorem B2011023 : Blo 2009435 2011023 := bstep (se 1 (by rfl) ⟨1508267, by rfl⟩ : syracuseStep 2011023 = 3016535) B3016535
theorem B3016541 : Blo 2009435 3016541 := bbase (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) (by norm_num)
theorem B2011027 : Blo 2009435 2011027 := bstep (se 1 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 2011027 = 3016541) B3016541
theorem B4524821 : Blo 2009435 4524821 := bbase (se 6 (by rfl) ⟨106050, by rfl⟩ : syracuseStep 4524821 = 212101) (by norm_num)
theorem B3016547 : Blo 2009435 3016547 := bstep (se 1 (by rfl) ⟨2262410, by rfl⟩ : syracuseStep 3016547 = 4524821) B4524821
theorem B2011031 : Blo 2009435 2011031 := bstep (se 1 (by rfl) ⟨1508273, by rfl⟩ : syracuseStep 2011031 = 3016547) B3016547
theorem B7635653 : Blo 2009435 7635653 := bbase (se 4 (by rfl) ⟨715842, by rfl⟩ : syracuseStep 7635653 = 1431685) (by norm_num)
theorem B5090435 : Blo 2009435 5090435 := bstep (se 1 (by rfl) ⟨3817826, by rfl⟩ : syracuseStep 5090435 = 7635653) B7635653
theorem B3393623 : Blo 2009435 3393623 := bstep (se 1 (by rfl) ⟨2545217, by rfl⟩ : syracuseStep 3393623 = 5090435) B5090435
theorem B2262415 : Blo 2009435 2262415 := bstep (se 1 (by rfl) ⟨1696811, by rfl⟩ : syracuseStep 2262415 = 3393623) B3393623
theorem B3016553 : Blo 2009435 3016553 := bstep (se 2 (by rfl) ⟨1131207, by rfl⟩ : syracuseStep 3016553 = 2262415) B2262415
theorem B2011035 : Blo 2009435 2011035 := bstep (se 1 (by rfl) ⟨1508276, by rfl⟩ : syracuseStep 2011035 = 3016553) B3016553
theorem B9663893 : Blo 2009435 9663893 := bbase (se 6 (by rfl) ⟨226497, by rfl⟩ : syracuseStep 9663893 = 452995) (by norm_num)
theorem B6442595 : Blo 2009435 6442595 := bstep (se 1 (by rfl) ⟨4831946, by rfl⟩ : syracuseStep 6442595 = 9663893) B9663893
theorem B4295063 : Blo 2009435 4295063 := bstep (se 1 (by rfl) ⟨3221297, by rfl⟩ : syracuseStep 4295063 = 6442595) B6442595
theorem B11453501 : Blo 2009435 11453501 := bstep (se 3 (by rfl) ⟨2147531, by rfl⟩ : syracuseStep 11453501 = 4295063) B4295063
theorem B7635667 : Blo 2009435 7635667 := bstep (se 1 (by rfl) ⟨5726750, by rfl⟩ : syracuseStep 7635667 = 11453501) B11453501
theorem B10180889 : Blo 2009435 10180889 := bstep (se 2 (by rfl) ⟨3817833, by rfl⟩ : syracuseStep 10180889 = 7635667) B7635667
theorem B6787259 : Blo 2009435 6787259 := bstep (se 1 (by rfl) ⟨5090444, by rfl⟩ : syracuseStep 6787259 = 10180889) B10180889
theorem B4524839 : Blo 2009435 4524839 := bstep (se 1 (by rfl) ⟨3393629, by rfl⟩ : syracuseStep 4524839 = 6787259) B6787259
theorem B3016559 : Blo 2009435 3016559 := bstep (se 1 (by rfl) ⟨2262419, by rfl⟩ : syracuseStep 3016559 = 4524839) B4524839
theorem B2011039 : Blo 2009435 2011039 := bstep (se 1 (by rfl) ⟨1508279, by rfl⟩ : syracuseStep 2011039 = 3016559) B3016559
theorem B3016565 : Blo 2009435 3016565 := bbase (se 5 (by rfl) ⟨141401, by rfl⟩ : syracuseStep 3016565 = 282803) (by norm_num)
theorem B2011043 : Blo 2009435 2011043 := bstep (se 1 (by rfl) ⟨1508282, by rfl⟩ : syracuseStep 2011043 = 3016565) B3016565
theorem B9173189 : Blo 2009435 9173189 := bbase (se 4 (by rfl) ⟨859986, by rfl⟩ : syracuseStep 9173189 = 1719973) (by norm_num)
theorem B24461837 : Blo 2009435 24461837 := bstep (se 3 (by rfl) ⟨4586594, by rfl⟩ : syracuseStep 24461837 = 9173189) B9173189
theorem B16307891 : Blo 2009435 16307891 := bstep (se 1 (by rfl) ⟨12230918, by rfl⟩ : syracuseStep 16307891 = 24461837) B24461837
theorem B10871927 : Blo 2009435 10871927 := bstep (se 1 (by rfl) ⟨8153945, by rfl⟩ : syracuseStep 10871927 = 16307891) B16307891
theorem B7247951 : Blo 2009435 7247951 := bstep (se 1 (by rfl) ⟨5435963, by rfl⟩ : syracuseStep 7247951 = 10871927) B10871927
theorem B4831967 : Blo 2009435 4831967 := bstep (se 1 (by rfl) ⟨3623975, by rfl⟩ : syracuseStep 4831967 = 7247951) B7247951
theorem B3221311 : Blo 2009435 3221311 := bstep (se 1 (by rfl) ⟨2415983, by rfl⟩ : syracuseStep 3221311 = 4831967) B4831967
theorem B4295081 : Blo 2009435 4295081 := bstep (se 2 (by rfl) ⟨1610655, by rfl⟩ : syracuseStep 4295081 = 3221311) B3221311
theorem B2863387 : Blo 2009435 2863387 := bstep (se 1 (by rfl) ⟨2147540, by rfl⟩ : syracuseStep 2863387 = 4295081) B4295081
theorem B3817849 : Blo 2009435 3817849 := bstep (se 2 (by rfl) ⟨1431693, by rfl⟩ : syracuseStep 3817849 = 2863387) B2863387
theorem B5090465 : Blo 2009435 5090465 := bstep (se 2 (by rfl) ⟨1908924, by rfl⟩ : syracuseStep 5090465 = 3817849) B3817849
theorem B3393643 : Blo 2009435 3393643 := bstep (se 1 (by rfl) ⟨2545232, by rfl⟩ : syracuseStep 3393643 = 5090465) B5090465
theorem B4524857 : Blo 2009435 4524857 := bstep (se 2 (by rfl) ⟨1696821, by rfl⟩ : syracuseStep 4524857 = 3393643) B3393643
theorem B3016571 : Blo 2009435 3016571 := bstep (se 1 (by rfl) ⟨2262428, by rfl⟩ : syracuseStep 3016571 = 4524857) B4524857
theorem B2011047 : Blo 2009435 2011047 := bstep (se 1 (by rfl) ⟨1508285, by rfl⟩ : syracuseStep 2011047 = 3016571) B3016571
theorem B2262433 : Blo 2009435 2262433 := bbase (se 2 (by rfl) ⟨848412, by rfl⟩ : syracuseStep 2262433 = 1696825) (by norm_num)
theorem B3016577 : Blo 2009435 3016577 := bstep (se 2 (by rfl) ⟨1131216, by rfl⟩ : syracuseStep 3016577 = 2262433) B2262433
theorem B2011051 : Blo 2009435 2011051 := bstep (se 1 (by rfl) ⟨1508288, by rfl⟩ : syracuseStep 2011051 = 3016577) B3016577
theorem B5090485 : Blo 2009435 5090485 := bbase (se 5 (by rfl) ⟨238616, by rfl⟩ : syracuseStep 5090485 = 477233) (by norm_num)
theorem B6787313 : Blo 2009435 6787313 := bstep (se 2 (by rfl) ⟨2545242, by rfl⟩ : syracuseStep 6787313 = 5090485) B5090485
theorem B4524875 : Blo 2009435 4524875 := bstep (se 1 (by rfl) ⟨3393656, by rfl⟩ : syracuseStep 4524875 = 6787313) B6787313
theorem B3016583 : Blo 2009435 3016583 := bstep (se 1 (by rfl) ⟨2262437, by rfl⟩ : syracuseStep 3016583 = 4524875) B4524875
theorem B2011055 : Blo 2009435 2011055 := bstep (se 1 (by rfl) ⟨1508291, by rfl⟩ : syracuseStep 2011055 = 3016583) B3016583
theorem B3016589 : Blo 2009435 3016589 := bbase (se 3 (by rfl) ⟨565610, by rfl⟩ : syracuseStep 3016589 = 1131221) (by norm_num)
theorem B2011059 : Blo 2009435 2011059 := bstep (se 1 (by rfl) ⟨1508294, by rfl⟩ : syracuseStep 2011059 = 3016589) B3016589
theorem B4524893 : Blo 2009435 4524893 := bbase (se 3 (by rfl) ⟨848417, by rfl⟩ : syracuseStep 4524893 = 1696835) (by norm_num)
theorem B3016595 : Blo 2009435 3016595 := bstep (se 1 (by rfl) ⟨2262446, by rfl⟩ : syracuseStep 3016595 = 4524893) B4524893
theorem B2011063 : Blo 2009435 2011063 := bstep (se 1 (by rfl) ⟨1508297, by rfl⟩ : syracuseStep 2011063 = 3016595) B3016595
theorem B3393677 : Blo 2009435 3393677 := bbase (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) (by norm_num)
theorem B2262451 : Blo 2009435 2262451 := bstep (se 1 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 2262451 = 3393677) B3393677
theorem B3016601 : Blo 2009435 3016601 := bstep (se 2 (by rfl) ⟨1131225, by rfl⟩ : syracuseStep 3016601 = 2262451) B2262451
theorem B2011067 : Blo 2009435 2011067 := bstep (se 1 (by rfl) ⟨1508300, by rfl⟩ : syracuseStep 2011067 = 3016601) B3016601
theorem B10872053 : Blo 2009435 10872053 := bbase (se 5 (by rfl) ⟨509627, by rfl⟩ : syracuseStep 10872053 = 1019255) (by norm_num)
theorem B7248035 : Blo 2009435 7248035 := bstep (se 1 (by rfl) ⟨5436026, by rfl⟩ : syracuseStep 7248035 = 10872053) B10872053
theorem B4832023 : Blo 2009435 4832023 := bstep (se 1 (by rfl) ⟨3624017, by rfl⟩ : syracuseStep 4832023 = 7248035) B7248035
theorem B6442697 : Blo 2009435 6442697 := bstep (se 2 (by rfl) ⟨2416011, by rfl⟩ : syracuseStep 6442697 = 4832023) B4832023
theorem B17180525 : Blo 2009435 17180525 := bstep (se 3 (by rfl) ⟨3221348, by rfl⟩ : syracuseStep 17180525 = 6442697) B6442697
theorem B11453683 : Blo 2009435 11453683 := bstep (se 1 (by rfl) ⟨8590262, by rfl⟩ : syracuseStep 11453683 = 17180525) B17180525
theorem B15271577 : Blo 2009435 15271577 := bstep (se 2 (by rfl) ⟨5726841, by rfl⟩ : syracuseStep 15271577 = 11453683) B11453683
theorem B10181051 : Blo 2009435 10181051 := bstep (se 1 (by rfl) ⟨7635788, by rfl⟩ : syracuseStep 10181051 = 15271577) B15271577
theorem B6787367 : Blo 2009435 6787367 := bstep (se 1 (by rfl) ⟨5090525, by rfl⟩ : syracuseStep 6787367 = 10181051) B10181051
theorem B4524911 : Blo 2009435 4524911 := bstep (se 1 (by rfl) ⟨3393683, by rfl⟩ : syracuseStep 4524911 = 6787367) B6787367
theorem B3016607 : Blo 2009435 3016607 := bstep (se 1 (by rfl) ⟨2262455, by rfl⟩ : syracuseStep 3016607 = 4524911) B4524911
theorem B2011071 : Blo 2009435 2011071 := bstep (se 1 (by rfl) ⟨1508303, by rfl⟩ : syracuseStep 2011071 = 3016607) B3016607
theorem B3016613 : Blo 2009435 3016613 := bbase (se 4 (by rfl) ⟨282807, by rfl⟩ : syracuseStep 3016613 = 565615) (by norm_num)
theorem B2011075 : Blo 2009435 2011075 := bstep (se 1 (by rfl) ⟨1508306, by rfl⟩ : syracuseStep 2011075 = 3016613) B3016613
theorem B2545273 : Blo 2009435 2545273 := bbase (se 2 (by rfl) ⟨954477, by rfl⟩ : syracuseStep 2545273 = 1908955) (by norm_num)
theorem B3393697 : Blo 2009435 3393697 := bstep (se 2 (by rfl) ⟨1272636, by rfl⟩ : syracuseStep 3393697 = 2545273) B2545273
theorem B4524929 : Blo 2009435 4524929 := bstep (se 2 (by rfl) ⟨1696848, by rfl⟩ : syracuseStep 4524929 = 3393697) B3393697
theorem B3016619 : Blo 2009435 3016619 := bstep (se 1 (by rfl) ⟨2262464, by rfl⟩ : syracuseStep 3016619 = 4524929) B4524929
theorem B2011079 : Blo 2009435 2011079 := bstep (se 1 (by rfl) ⟨1508309, by rfl⟩ : syracuseStep 2011079 = 3016619) B3016619
theorem B2262469 : Blo 2009435 2262469 := bbase (se 4 (by rfl) ⟨212106, by rfl⟩ : syracuseStep 2262469 = 424213) (by norm_num)
theorem B3016625 : Blo 2009435 3016625 := bstep (se 2 (by rfl) ⟨1131234, by rfl⟩ : syracuseStep 3016625 = 2262469) B2262469
theorem B2011083 : Blo 2009435 2011083 := bstep (se 1 (by rfl) ⟨1508312, by rfl⟩ : syracuseStep 2011083 = 3016625) B3016625
theorem B3817925 : Blo 2009435 3817925 := bbase (se 4 (by rfl) ⟨357930, by rfl⟩ : syracuseStep 3817925 = 715861) (by norm_num)
theorem B2545283 : Blo 2009435 2545283 := bstep (se 1 (by rfl) ⟨1908962, by rfl⟩ : syracuseStep 2545283 = 3817925) B3817925
theorem B6787421 : Blo 2009435 6787421 := bstep (se 3 (by rfl) ⟨1272641, by rfl⟩ : syracuseStep 6787421 = 2545283) B2545283
theorem B4524947 : Blo 2009435 4524947 := bstep (se 1 (by rfl) ⟨3393710, by rfl⟩ : syracuseStep 4524947 = 6787421) B6787421
theorem B3016631 : Blo 2009435 3016631 := bstep (se 1 (by rfl) ⟨2262473, by rfl⟩ : syracuseStep 3016631 = 4524947) B4524947
theorem B2011087 : Blo 2009435 2011087 := bstep (se 1 (by rfl) ⟨1508315, by rfl⟩ : syracuseStep 2011087 = 3016631) B3016631
theorem B3016637 : Blo 2009435 3016637 := bbase (se 3 (by rfl) ⟨565619, by rfl⟩ : syracuseStep 3016637 = 1131239) (by norm_num)
theorem B2011091 : Blo 2009435 2011091 := bstep (se 1 (by rfl) ⟨1508318, by rfl⟩ : syracuseStep 2011091 = 3016637) B3016637
theorem B4524965 : Blo 2009435 4524965 := bbase (se 4 (by rfl) ⟨424215, by rfl⟩ : syracuseStep 4524965 = 848431) (by norm_num)
theorem B3016643 : Blo 2009435 3016643 := bstep (se 1 (by rfl) ⟨2262482, by rfl⟩ : syracuseStep 3016643 = 4524965) B4524965
theorem B2011095 : Blo 2009435 2011095 := bstep (se 1 (by rfl) ⟨1508321, by rfl⟩ : syracuseStep 2011095 = 3016643) B3016643
theorem B5090597 : Blo 2009435 5090597 := bbase (se 4 (by rfl) ⟨477243, by rfl⟩ : syracuseStep 5090597 = 954487) (by norm_num)
theorem B3393731 : Blo 2009435 3393731 := bstep (se 1 (by rfl) ⟨2545298, by rfl⟩ : syracuseStep 3393731 = 5090597) B5090597
theorem B2262487 : Blo 2009435 2262487 := bstep (se 1 (by rfl) ⟨1696865, by rfl⟩ : syracuseStep 2262487 = 3393731) B3393731
theorem B3016649 : Blo 2009435 3016649 := bstep (se 2 (by rfl) ⟨1131243, by rfl⟩ : syracuseStep 3016649 = 2262487) B2262487
theorem B2011099 : Blo 2009435 2011099 := bstep (se 1 (by rfl) ⟨1508324, by rfl⟩ : syracuseStep 2011099 = 3016649) B3016649
theorem B5726933 : Blo 2009435 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B3817955 : Blo 2009435 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B10181213 : Blo 2009435 10181213 := bstep (se 3 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 10181213 = 3817955) B3817955
theorem B6787475 : Blo 2009435 6787475 := bstep (se 1 (by rfl) ⟨5090606, by rfl⟩ : syracuseStep 6787475 = 10181213) B10181213
theorem B4524983 : Blo 2009435 4524983 := bstep (se 1 (by rfl) ⟨3393737, by rfl⟩ : syracuseStep 4524983 = 6787475) B6787475
theorem B3016655 : Blo 2009435 3016655 := bstep (se 1 (by rfl) ⟨2262491, by rfl⟩ : syracuseStep 3016655 = 4524983) B4524983
theorem B2011103 : Blo 2009435 2011103 := bstep (se 1 (by rfl) ⟨1508327, by rfl⟩ : syracuseStep 2011103 = 3016655) B3016655
theorem B3016661 : Blo 2009435 3016661 := bbase (se 7 (by rfl) ⟨35351, by rfl⟩ : syracuseStep 3016661 = 70703) (by norm_num)
theorem B2011107 : Blo 2009435 2011107 := bstep (se 1 (by rfl) ⟨1508330, by rfl⟩ : syracuseStep 2011107 = 3016661) B3016661
theorem B7635941 : Blo 2009435 7635941 := bbase (se 4 (by rfl) ⟨715869, by rfl⟩ : syracuseStep 7635941 = 1431739) (by norm_num)
theorem B5090627 : Blo 2009435 5090627 := bstep (se 1 (by rfl) ⟨3817970, by rfl⟩ : syracuseStep 5090627 = 7635941) B7635941
theorem B3393751 : Blo 2009435 3393751 := bstep (se 1 (by rfl) ⟨2545313, by rfl⟩ : syracuseStep 3393751 = 5090627) B5090627
theorem B4525001 : Blo 2009435 4525001 := bstep (se 2 (by rfl) ⟨1696875, by rfl⟩ : syracuseStep 4525001 = 3393751) B3393751
theorem B3016667 : Blo 2009435 3016667 := bstep (se 1 (by rfl) ⟨2262500, by rfl⟩ : syracuseStep 3016667 = 4525001) B4525001
theorem B2011111 : Blo 2009435 2011111 := bstep (se 1 (by rfl) ⟨1508333, by rfl⟩ : syracuseStep 2011111 = 3016667) B3016667
theorem B2262505 : Blo 2009435 2262505 := bbase (se 2 (by rfl) ⟨848439, by rfl⟩ : syracuseStep 2262505 = 1696879) (by norm_num)
theorem B3016673 : Blo 2009435 3016673 := bstep (se 2 (by rfl) ⟨1131252, by rfl⟩ : syracuseStep 3016673 = 2262505) B2262505
theorem B2011115 : Blo 2009435 2011115 := bstep (se 1 (by rfl) ⟨1508336, by rfl⟩ : syracuseStep 2011115 = 3016673) B3016673
theorem B2147617 : Blo 2009435 2147617 := bbase (se 2 (by rfl) ⟨805356, by rfl⟩ : syracuseStep 2147617 = 1610713) (by norm_num)
theorem B11453957 : Blo 2009435 11453957 := bstep (se 4 (by rfl) ⟨1073808, by rfl⟩ : syracuseStep 11453957 = 2147617) B2147617
theorem B7635971 : Blo 2009435 7635971 := bstep (se 1 (by rfl) ⟨5726978, by rfl⟩ : syracuseStep 7635971 = 11453957) B11453957
theorem B5090647 : Blo 2009435 5090647 := bstep (se 1 (by rfl) ⟨3817985, by rfl⟩ : syracuseStep 5090647 = 7635971) B7635971
theorem B6787529 : Blo 2009435 6787529 := bstep (se 2 (by rfl) ⟨2545323, by rfl⟩ : syracuseStep 6787529 = 5090647) B5090647
theorem B4525019 : Blo 2009435 4525019 := bstep (se 1 (by rfl) ⟨3393764, by rfl⟩ : syracuseStep 4525019 = 6787529) B6787529
theorem B3016679 : Blo 2009435 3016679 := bstep (se 1 (by rfl) ⟨2262509, by rfl⟩ : syracuseStep 3016679 = 4525019) B4525019
theorem B2011119 : Blo 2009435 2011119 := bstep (se 1 (by rfl) ⟨1508339, by rfl⟩ : syracuseStep 2011119 = 3016679) B3016679
theorem B3016685 : Blo 2009435 3016685 := bbase (se 3 (by rfl) ⟨565628, by rfl⟩ : syracuseStep 3016685 = 1131257) (by norm_num)
theorem B2011123 : Blo 2009435 2011123 := bstep (se 1 (by rfl) ⟨1508342, by rfl⟩ : syracuseStep 2011123 = 3016685) B3016685
theorem B4525037 : Blo 2009435 4525037 := bbase (se 3 (by rfl) ⟨848444, by rfl⟩ : syracuseStep 4525037 = 1696889) (by norm_num)
theorem B3016691 : Blo 2009435 3016691 := bstep (se 1 (by rfl) ⟨2262518, by rfl⟩ : syracuseStep 3016691 = 4525037) B4525037
theorem B2011127 : Blo 2009435 2011127 := bstep (se 1 (by rfl) ⟨1508345, by rfl⟩ : syracuseStep 2011127 = 3016691) B3016691
theorem B4295261 : Blo 2009435 4295261 := bbase (se 3 (by rfl) ⟨805361, by rfl⟩ : syracuseStep 4295261 = 1610723) (by norm_num)
theorem B2863507 : Blo 2009435 2863507 := bstep (se 1 (by rfl) ⟨2147630, by rfl⟩ : syracuseStep 2863507 = 4295261) B4295261
theorem B3818009 : Blo 2009435 3818009 := bstep (se 2 (by rfl) ⟨1431753, by rfl⟩ : syracuseStep 3818009 = 2863507) B2863507
theorem B2545339 : Blo 2009435 2545339 := bstep (se 1 (by rfl) ⟨1909004, by rfl⟩ : syracuseStep 2545339 = 3818009) B3818009
theorem B3393785 : Blo 2009435 3393785 := bstep (se 2 (by rfl) ⟨1272669, by rfl⟩ : syracuseStep 3393785 = 2545339) B2545339
theorem B2262523 : Blo 2009435 2262523 := bstep (se 1 (by rfl) ⟨1696892, by rfl⟩ : syracuseStep 2262523 = 3393785) B3393785
theorem B3016697 : Blo 2009435 3016697 := bstep (se 2 (by rfl) ⟨1131261, by rfl⟩ : syracuseStep 3016697 = 2262523) B2262523
theorem B2011131 : Blo 2009435 2011131 := bstep (se 1 (by rfl) ⟨1508348, by rfl⟩ : syracuseStep 2011131 = 3016697) B3016697
theorem B6619909 : Blo 2009435 6619909 := bbase (se 4 (by rfl) ⟨620616, by rfl⟩ : syracuseStep 6619909 = 1241233) (by norm_num)
theorem B8826545 : Blo 2009435 8826545 := bstep (se 2 (by rfl) ⟨3309954, by rfl⟩ : syracuseStep 8826545 = 6619909) B6619909
theorem B5884363 : Blo 2009435 5884363 := bstep (se 1 (by rfl) ⟨4413272, by rfl⟩ : syracuseStep 5884363 = 8826545) B8826545
theorem B7845817 : Blo 2009435 7845817 := bstep (se 2 (by rfl) ⟨2942181, by rfl⟩ : syracuseStep 7845817 = 5884363) B5884363
theorem B10461089 : Blo 2009435 10461089 := bstep (se 2 (by rfl) ⟨3922908, by rfl⟩ : syracuseStep 10461089 = 7845817) B7845817
theorem B6974059 : Blo 2009435 6974059 := bstep (se 1 (by rfl) ⟨5230544, by rfl⟩ : syracuseStep 6974059 = 10461089) B10461089
theorem B9298745 : Blo 2009435 9298745 := bstep (se 2 (by rfl) ⟨3487029, by rfl⟩ : syracuseStep 9298745 = 6974059) B6974059
theorem B6199163 : Blo 2009435 6199163 := bstep (se 1 (by rfl) ⟨4649372, by rfl⟩ : syracuseStep 6199163 = 9298745) B9298745
theorem B4132775 : Blo 2009435 4132775 := bstep (se 1 (by rfl) ⟨3099581, by rfl⟩ : syracuseStep 4132775 = 6199163) B6199163
theorem B11020733 : Blo 2009435 11020733 := bstep (se 3 (by rfl) ⟨2066387, by rfl⟩ : syracuseStep 11020733 = 4132775) B4132775
theorem B7347155 : Blo 2009435 7347155 := bstep (se 1 (by rfl) ⟨5510366, by rfl⟩ : syracuseStep 7347155 = 11020733) B11020733
theorem B78369653 : Blo 2009435 78369653 := bstep (se 5 (by rfl) ⟨3673577, by rfl⟩ : syracuseStep 78369653 = 7347155) B7347155
theorem B208985741 : Blo 2009435 208985741 := bstep (se 3 (by rfl) ⟨39184826, by rfl⟩ : syracuseStep 208985741 = 78369653) B78369653
theorem B139323827 : Blo 2009435 139323827 := bstep (se 1 (by rfl) ⟨104492870, by rfl⟩ : syracuseStep 139323827 = 208985741) B208985741
theorem B92882551 : Blo 2009435 92882551 := bstep (se 1 (by rfl) ⟨69661913, by rfl⟩ : syracuseStep 92882551 = 139323827) B139323827
theorem B123843401 : Blo 2009435 123843401 := bstep (se 2 (by rfl) ⟨46441275, by rfl⟩ : syracuseStep 123843401 = 92882551) B92882551
theorem B82562267 : Blo 2009435 82562267 := bstep (se 1 (by rfl) ⟨61921700, by rfl⟩ : syracuseStep 82562267 = 123843401) B123843401
theorem B55041511 : Blo 2009435 55041511 := bstep (se 1 (by rfl) ⟨41281133, by rfl⟩ : syracuseStep 55041511 = 82562267) B82562267
theorem B73388681 : Blo 2009435 73388681 := bstep (se 2 (by rfl) ⟨27520755, by rfl⟩ : syracuseStep 73388681 = 55041511) B55041511
theorem B48925787 : Blo 2009435 48925787 := bstep (se 1 (by rfl) ⟨36694340, by rfl⟩ : syracuseStep 48925787 = 73388681) B73388681
theorem B130468765 : Blo 2009435 130468765 := bstep (se 3 (by rfl) ⟨24462893, by rfl⟩ : syracuseStep 130468765 = 48925787) B48925787
theorem B173958353 : Blo 2009435 173958353 := bstep (se 2 (by rfl) ⟨65234382, by rfl⟩ : syracuseStep 173958353 = 130468765) B130468765
theorem B115972235 : Blo 2009435 115972235 := bstep (se 1 (by rfl) ⟨86979176, by rfl⟩ : syracuseStep 115972235 = 173958353) B173958353
theorem B77314823 : Blo 2009435 77314823 := bstep (se 1 (by rfl) ⟨57986117, by rfl⟩ : syracuseStep 77314823 = 115972235) B115972235
theorem B51543215 : Blo 2009435 51543215 := bstep (se 1 (by rfl) ⟨38657411, by rfl⟩ : syracuseStep 51543215 = 77314823) B77314823
theorem B34362143 : Blo 2009435 34362143 := bstep (se 1 (by rfl) ⟨25771607, by rfl⟩ : syracuseStep 34362143 = 51543215) B51543215
theorem B22908095 : Blo 2009435 22908095 := bstep (se 1 (by rfl) ⟨17181071, by rfl⟩ : syracuseStep 22908095 = 34362143) B34362143
theorem B15272063 : Blo 2009435 15272063 := bstep (se 1 (by rfl) ⟨11454047, by rfl⟩ : syracuseStep 15272063 = 22908095) B22908095
theorem B10181375 : Blo 2009435 10181375 := bstep (se 1 (by rfl) ⟨7636031, by rfl⟩ : syracuseStep 10181375 = 15272063) B15272063
theorem B6787583 : Blo 2009435 6787583 := bstep (se 1 (by rfl) ⟨5090687, by rfl⟩ : syracuseStep 6787583 = 10181375) B10181375
theorem B4525055 : Blo 2009435 4525055 := bstep (se 1 (by rfl) ⟨3393791, by rfl⟩ : syracuseStep 4525055 = 6787583) B6787583
theorem B3016703 : Blo 2009435 3016703 := bstep (se 1 (by rfl) ⟨2262527, by rfl⟩ : syracuseStep 3016703 = 4525055) B4525055
theorem B2011135 : Blo 2009435 2011135 := bstep (se 1 (by rfl) ⟨1508351, by rfl⟩ : syracuseStep 2011135 = 3016703) B3016703
theorem B3016709 : Blo 2009435 3016709 := bbase (se 4 (by rfl) ⟨282816, by rfl⟩ : syracuseStep 3016709 = 565633) (by norm_num)
theorem B2011139 : Blo 2009435 2011139 := bstep (se 1 (by rfl) ⟨1508354, by rfl⟩ : syracuseStep 2011139 = 3016709) B3016709
theorem B3393805 : Blo 2009435 3393805 := bbase (se 3 (by rfl) ⟨636338, by rfl⟩ : syracuseStep 3393805 = 1272677) (by norm_num)
theorem B4525073 : Blo 2009435 4525073 := bstep (se 2 (by rfl) ⟨1696902, by rfl⟩ : syracuseStep 4525073 = 3393805) B3393805
theorem B3016715 : Blo 2009435 3016715 := bstep (se 1 (by rfl) ⟨2262536, by rfl⟩ : syracuseStep 3016715 = 4525073) B4525073
theorem B2011143 : Blo 2009435 2011143 := bstep (se 1 (by rfl) ⟨1508357, by rfl⟩ : syracuseStep 2011143 = 3016715) B3016715
theorem B2262541 : Blo 2009435 2262541 := bbase (se 3 (by rfl) ⟨424226, by rfl⟩ : syracuseStep 2262541 = 848453) (by norm_num)
theorem B3016721 : Blo 2009435 3016721 := bstep (se 2 (by rfl) ⟨1131270, by rfl⟩ : syracuseStep 3016721 = 2262541) B2262541
theorem B2011147 : Blo 2009435 2011147 := bstep (se 1 (by rfl) ⟨1508360, by rfl⟩ : syracuseStep 2011147 = 3016721) B3016721
theorem B6787637 : Blo 2009435 6787637 := bbase (se 5 (by rfl) ⟨318170, by rfl⟩ : syracuseStep 6787637 = 636341) (by norm_num)
theorem B4525091 : Blo 2009435 4525091 := bstep (se 1 (by rfl) ⟨3393818, by rfl⟩ : syracuseStep 4525091 = 6787637) B6787637
theorem B3016727 : Blo 2009435 3016727 := bstep (se 1 (by rfl) ⟨2262545, by rfl⟩ : syracuseStep 3016727 = 4525091) B4525091
theorem B2011151 : Blo 2009435 2011151 := bstep (se 1 (by rfl) ⟨1508363, by rfl⟩ : syracuseStep 2011151 = 3016727) B3016727
theorem B3016733 : Blo 2009435 3016733 := bbase (se 3 (by rfl) ⟨565637, by rfl⟩ : syracuseStep 3016733 = 1131275) (by norm_num)
theorem B2011155 : Blo 2009435 2011155 := bstep (se 1 (by rfl) ⟨1508366, by rfl⟩ : syracuseStep 2011155 = 3016733) B3016733
theorem B4525109 : Blo 2009435 4525109 := bbase (se 5 (by rfl) ⟨212114, by rfl⟩ : syracuseStep 4525109 = 424229) (by norm_num)
theorem B3016739 : Blo 2009435 3016739 := bstep (se 1 (by rfl) ⟨2262554, by rfl⟩ : syracuseStep 3016739 = 4525109) B4525109
theorem B2011159 : Blo 2009435 2011159 := bstep (se 1 (by rfl) ⟨1508369, by rfl⟩ : syracuseStep 2011159 = 3016739) B3016739
theorem B4832245 : Blo 2009435 4832245 := bbase (se 5 (by rfl) ⟨226511, by rfl⟩ : syracuseStep 4832245 = 453023) (by norm_num)
theorem B6442993 : Blo 2009435 6442993 := bstep (se 2 (by rfl) ⟨2416122, by rfl⟩ : syracuseStep 6442993 = 4832245) B4832245
theorem B8590657 : Blo 2009435 8590657 := bstep (se 2 (by rfl) ⟨3221496, by rfl⟩ : syracuseStep 8590657 = 6442993) B6442993
theorem B11454209 : Blo 2009435 11454209 := bstep (se 2 (by rfl) ⟨4295328, by rfl⟩ : syracuseStep 11454209 = 8590657) B8590657
theorem B7636139 : Blo 2009435 7636139 := bstep (se 1 (by rfl) ⟨5727104, by rfl⟩ : syracuseStep 7636139 = 11454209) B11454209
theorem B5090759 : Blo 2009435 5090759 := bstep (se 1 (by rfl) ⟨3818069, by rfl⟩ : syracuseStep 5090759 = 7636139) B7636139
theorem B3393839 : Blo 2009435 3393839 := bstep (se 1 (by rfl) ⟨2545379, by rfl⟩ : syracuseStep 3393839 = 5090759) B5090759
theorem B2262559 : Blo 2009435 2262559 := bstep (se 1 (by rfl) ⟨1696919, by rfl⟩ : syracuseStep 2262559 = 3393839) B3393839
theorem B3016745 : Blo 2009435 3016745 := bstep (se 2 (by rfl) ⟨1131279, by rfl⟩ : syracuseStep 3016745 = 2262559) B2262559
theorem B2011163 : Blo 2009435 2011163 := bstep (se 1 (by rfl) ⟨1508372, by rfl⟩ : syracuseStep 2011163 = 3016745) B3016745
theorem B2421181 : Blo 2009435 2421181 := bbase (se 3 (by rfl) ⟨453971, by rfl⟩ : syracuseStep 2421181 = 907943) (by norm_num)
theorem B12912965 : Blo 2009435 12912965 := bstep (se 4 (by rfl) ⟨1210590, by rfl⟩ : syracuseStep 12912965 = 2421181) B2421181
theorem B8608643 : Blo 2009435 8608643 := bstep (se 1 (by rfl) ⟨6456482, by rfl⟩ : syracuseStep 8608643 = 12912965) B12912965
theorem B5739095 : Blo 2009435 5739095 := bstep (se 1 (by rfl) ⟨4304321, by rfl⟩ : syracuseStep 5739095 = 8608643) B8608643
theorem B3826063 : Blo 2009435 3826063 := bstep (se 1 (by rfl) ⟨2869547, by rfl⟩ : syracuseStep 3826063 = 5739095) B5739095
theorem B5101417 : Blo 2009435 5101417 := bstep (se 2 (by rfl) ⟨1913031, by rfl⟩ : syracuseStep 5101417 = 3826063) B3826063
theorem B6801889 : Blo 2009435 6801889 := bstep (se 2 (by rfl) ⟨2550708, by rfl⟩ : syracuseStep 6801889 = 5101417) B5101417
theorem B9069185 : Blo 2009435 9069185 := bstep (se 2 (by rfl) ⟨3400944, by rfl⟩ : syracuseStep 9069185 = 6801889) B6801889
theorem B6046123 : Blo 2009435 6046123 := bstep (se 1 (by rfl) ⟨4534592, by rfl⟩ : syracuseStep 6046123 = 9069185) B9069185
theorem B8061497 : Blo 2009435 8061497 := bstep (se 2 (by rfl) ⟨3023061, by rfl⟩ : syracuseStep 8061497 = 6046123) B6046123
theorem B5374331 : Blo 2009435 5374331 := bstep (se 1 (by rfl) ⟨4030748, by rfl⟩ : syracuseStep 5374331 = 8061497) B8061497
theorem B3582887 : Blo 2009435 3582887 := bstep (se 1 (by rfl) ⟨2687165, by rfl⟩ : syracuseStep 3582887 = 5374331) B5374331
theorem B9554365 : Blo 2009435 9554365 := bstep (se 3 (by rfl) ⟨1791443, by rfl⟩ : syracuseStep 9554365 = 3582887) B3582887
theorem B12739153 : Blo 2009435 12739153 := bstep (se 2 (by rfl) ⟨4777182, by rfl⟩ : syracuseStep 12739153 = 9554365) B9554365
theorem B16985537 : Blo 2009435 16985537 := bstep (se 2 (by rfl) ⟨6369576, by rfl⟩ : syracuseStep 16985537 = 12739153) B12739153
theorem B11323691 : Blo 2009435 11323691 := bstep (se 1 (by rfl) ⟨8492768, by rfl⟩ : syracuseStep 11323691 = 16985537) B16985537
theorem B7549127 : Blo 2009435 7549127 := bstep (se 1 (by rfl) ⟨5661845, by rfl⟩ : syracuseStep 7549127 = 11323691) B11323691
theorem B5032751 : Blo 2009435 5032751 := bstep (se 1 (by rfl) ⟨3774563, by rfl⟩ : syracuseStep 5032751 = 7549127) B7549127
theorem B13420669 : Blo 2009435 13420669 := bstep (se 3 (by rfl) ⟨2516375, by rfl⟩ : syracuseStep 13420669 = 5032751) B5032751
theorem B17894225 : Blo 2009435 17894225 := bstep (se 2 (by rfl) ⟨6710334, by rfl⟩ : syracuseStep 17894225 = 13420669) B13420669
theorem B11929483 : Blo 2009435 11929483 := bstep (se 1 (by rfl) ⟨8947112, by rfl⟩ : syracuseStep 11929483 = 17894225) B17894225
theorem B15905977 : Blo 2009435 15905977 := bstep (se 2 (by rfl) ⟨5964741, by rfl⟩ : syracuseStep 15905977 = 11929483) B11929483
theorem B84831877 : Blo 2009435 84831877 := bstep (se 4 (by rfl) ⟨7952988, by rfl⟩ : syracuseStep 84831877 = 15905977) B15905977
theorem B113109169 : Blo 2009435 113109169 := bstep (se 2 (by rfl) ⟨42415938, by rfl⟩ : syracuseStep 113109169 = 84831877) B84831877
theorem B150812225 : Blo 2009435 150812225 := bstep (se 2 (by rfl) ⟨56554584, by rfl⟩ : syracuseStep 150812225 = 113109169) B113109169
theorem B100541483 : Blo 2009435 100541483 := bstep (se 1 (by rfl) ⟨75406112, by rfl⟩ : syracuseStep 100541483 = 150812225) B150812225
theorem B67027655 : Blo 2009435 67027655 := bstep (se 1 (by rfl) ⟨50270741, by rfl⟩ : syracuseStep 67027655 = 100541483) B100541483
theorem B44685103 : Blo 2009435 44685103 := bstep (se 1 (by rfl) ⟨33513827, by rfl⟩ : syracuseStep 44685103 = 67027655) B67027655
theorem B59580137 : Blo 2009435 59580137 := bstep (se 2 (by rfl) ⟨22342551, by rfl⟩ : syracuseStep 59580137 = 44685103) B44685103
theorem B158880365 : Blo 2009435 158880365 := bstep (se 3 (by rfl) ⟨29790068, by rfl⟩ : syracuseStep 158880365 = 59580137) B59580137
theorem B105920243 : Blo 2009435 105920243 := bstep (se 1 (by rfl) ⟨79440182, by rfl⟩ : syracuseStep 105920243 = 158880365) B158880365
theorem B70613495 : Blo 2009435 70613495 := bstep (se 1 (by rfl) ⟨52960121, by rfl⟩ : syracuseStep 70613495 = 105920243) B105920243
theorem B47075663 : Blo 2009435 47075663 := bstep (se 1 (by rfl) ⟨35306747, by rfl⟩ : syracuseStep 47075663 = 70613495) B70613495
theorem B31383775 : Blo 2009435 31383775 := bstep (se 1 (by rfl) ⟨23537831, by rfl⟩ : syracuseStep 31383775 = 47075663) B47075663
theorem B41845033 : Blo 2009435 41845033 := bstep (se 2 (by rfl) ⟨15691887, by rfl⟩ : syracuseStep 41845033 = 31383775) B31383775
theorem B55793377 : Blo 2009435 55793377 := bstep (se 2 (by rfl) ⟨20922516, by rfl⟩ : syracuseStep 55793377 = 41845033) B41845033
theorem B297564677 : Blo 2009435 297564677 := bstep (se 4 (by rfl) ⟨27896688, by rfl⟩ : syracuseStep 297564677 = 55793377) B55793377
theorem B198376451 : Blo 2009435 198376451 := bstep (se 1 (by rfl) ⟨148782338, by rfl⟩ : syracuseStep 198376451 = 297564677) B297564677
theorem B132250967 : Blo 2009435 132250967 := bstep (se 1 (by rfl) ⟨99188225, by rfl⟩ : syracuseStep 132250967 = 198376451) B198376451
theorem B88167311 : Blo 2009435 88167311 := bstep (se 1 (by rfl) ⟨66125483, by rfl⟩ : syracuseStep 88167311 = 132250967) B132250967
theorem B58778207 : Blo 2009435 58778207 := bstep (se 1 (by rfl) ⟨44083655, by rfl⟩ : syracuseStep 58778207 = 88167311) B88167311
theorem B39185471 : Blo 2009435 39185471 := bstep (se 1 (by rfl) ⟨29389103, by rfl⟩ : syracuseStep 39185471 = 58778207) B58778207
theorem B26123647 : Blo 2009435 26123647 := bstep (se 1 (by rfl) ⟨19592735, by rfl⟩ : syracuseStep 26123647 = 39185471) B39185471
theorem B34831529 : Blo 2009435 34831529 := bstep (se 2 (by rfl) ⟨13061823, by rfl⟩ : syracuseStep 34831529 = 26123647) B26123647
theorem B23221019 : Blo 2009435 23221019 := bstep (se 1 (by rfl) ⟨17415764, by rfl⟩ : syracuseStep 23221019 = 34831529) B34831529
theorem B61922717 : Blo 2009435 61922717 := bstep (se 3 (by rfl) ⟨11610509, by rfl⟩ : syracuseStep 61922717 = 23221019) B23221019
theorem B41281811 : Blo 2009435 41281811 := bstep (se 1 (by rfl) ⟨30961358, by rfl⟩ : syracuseStep 41281811 = 61922717) B61922717
theorem B27521207 : Blo 2009435 27521207 := bstep (se 1 (by rfl) ⟨20640905, by rfl⟩ : syracuseStep 27521207 = 41281811) B41281811
theorem B18347471 : Blo 2009435 18347471 := bstep (se 1 (by rfl) ⟨13760603, by rfl⟩ : syracuseStep 18347471 = 27521207) B27521207
theorem B12231647 : Blo 2009435 12231647 := bstep (se 1 (by rfl) ⟨9173735, by rfl⟩ : syracuseStep 12231647 = 18347471) B18347471
theorem B8154431 : Blo 2009435 8154431 := bstep (se 1 (by rfl) ⟨6115823, by rfl⟩ : syracuseStep 8154431 = 12231647) B12231647
theorem B5436287 : Blo 2009435 5436287 := bstep (se 1 (by rfl) ⟨4077215, by rfl⟩ : syracuseStep 5436287 = 8154431) B8154431
theorem B3624191 : Blo 2009435 3624191 := bstep (se 1 (by rfl) ⟨2718143, by rfl⟩ : syracuseStep 3624191 = 5436287) B5436287
theorem B2416127 : Blo 2009435 2416127 := bstep (se 1 (by rfl) ⟨1812095, by rfl⟩ : syracuseStep 2416127 = 3624191) B3624191
theorem B6443005 : Blo 2009435 6443005 := bstep (se 3 (by rfl) ⟨1208063, by rfl⟩ : syracuseStep 6443005 = 2416127) B2416127
theorem B8590673 : Blo 2009435 8590673 := bstep (se 2 (by rfl) ⟨3221502, by rfl⟩ : syracuseStep 8590673 = 6443005) B6443005
theorem B5727115 : Blo 2009435 5727115 := bstep (se 1 (by rfl) ⟨4295336, by rfl⟩ : syracuseStep 5727115 = 8590673) B8590673
theorem B7636153 : Blo 2009435 7636153 := bstep (se 2 (by rfl) ⟨2863557, by rfl⟩ : syracuseStep 7636153 = 5727115) B5727115
theorem B10181537 : Blo 2009435 10181537 := bstep (se 2 (by rfl) ⟨3818076, by rfl⟩ : syracuseStep 10181537 = 7636153) B7636153
theorem B6787691 : Blo 2009435 6787691 := bstep (se 1 (by rfl) ⟨5090768, by rfl⟩ : syracuseStep 6787691 = 10181537) B10181537
theorem B4525127 : Blo 2009435 4525127 := bstep (se 1 (by rfl) ⟨3393845, by rfl⟩ : syracuseStep 4525127 = 6787691) B6787691
theorem B3016751 : Blo 2009435 3016751 := bstep (se 1 (by rfl) ⟨2262563, by rfl⟩ : syracuseStep 3016751 = 4525127) B4525127
theorem B2011167 : Blo 2009435 2011167 := bstep (se 1 (by rfl) ⟨1508375, by rfl⟩ : syracuseStep 2011167 = 3016751) B3016751
theorem B3016757 : Blo 2009435 3016757 := bbase (se 5 (by rfl) ⟨141410, by rfl⟩ : syracuseStep 3016757 = 282821) (by norm_num)
theorem B2011171 : Blo 2009435 2011171 := bstep (se 1 (by rfl) ⟨1508378, by rfl⟩ : syracuseStep 2011171 = 3016757) B3016757
theorem B5090789 : Blo 2009435 5090789 := bbase (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) (by norm_num)
theorem B3393859 : Blo 2009435 3393859 := bstep (se 1 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 3393859 = 5090789) B5090789
theorem B4525145 : Blo 2009435 4525145 := bstep (se 2 (by rfl) ⟨1696929, by rfl⟩ : syracuseStep 4525145 = 3393859) B3393859
theorem B3016763 : Blo 2009435 3016763 := bstep (se 1 (by rfl) ⟨2262572, by rfl⟩ : syracuseStep 3016763 = 4525145) B4525145
theorem B2011175 : Blo 2009435 2011175 := bstep (se 1 (by rfl) ⟨1508381, by rfl⟩ : syracuseStep 2011175 = 3016763) B3016763
theorem B2262577 : Blo 2009435 2262577 := bbase (se 2 (by rfl) ⟨848466, by rfl⟩ : syracuseStep 2262577 = 1696933) (by norm_num)
theorem B3016769 : Blo 2009435 3016769 := bstep (se 2 (by rfl) ⟨1131288, by rfl⟩ : syracuseStep 3016769 = 2262577) B2262577
theorem B2011179 : Blo 2009435 2011179 := bstep (se 1 (by rfl) ⟨1508384, by rfl⟩ : syracuseStep 2011179 = 3016769) B3016769
theorem B4832293 : Blo 2009435 4832293 := bbase (se 4 (by rfl) ⟨453027, by rfl⟩ : syracuseStep 4832293 = 906055) (by norm_num)
theorem B6443057 : Blo 2009435 6443057 := bstep (se 2 (by rfl) ⟨2416146, by rfl⟩ : syracuseStep 6443057 = 4832293) B4832293
theorem B4295371 : Blo 2009435 4295371 := bstep (se 1 (by rfl) ⟨3221528, by rfl⟩ : syracuseStep 4295371 = 6443057) B6443057
theorem B5727161 : Blo 2009435 5727161 := bstep (se 2 (by rfl) ⟨2147685, by rfl⟩ : syracuseStep 5727161 = 4295371) B4295371
theorem B3818107 : Blo 2009435 3818107 := bstep (se 1 (by rfl) ⟨2863580, by rfl⟩ : syracuseStep 3818107 = 5727161) B5727161
theorem B5090809 : Blo 2009435 5090809 := bstep (se 2 (by rfl) ⟨1909053, by rfl⟩ : syracuseStep 5090809 = 3818107) B3818107
theorem B6787745 : Blo 2009435 6787745 := bstep (se 2 (by rfl) ⟨2545404, by rfl⟩ : syracuseStep 6787745 = 5090809) B5090809
theorem B4525163 : Blo 2009435 4525163 := bstep (se 1 (by rfl) ⟨3393872, by rfl⟩ : syracuseStep 4525163 = 6787745) B6787745
theorem B3016775 : Blo 2009435 3016775 := bstep (se 1 (by rfl) ⟨2262581, by rfl⟩ : syracuseStep 3016775 = 4525163) B4525163
theorem B2011183 : Blo 2009435 2011183 := bstep (se 1 (by rfl) ⟨1508387, by rfl⟩ : syracuseStep 2011183 = 3016775) B3016775
theorem B3016781 : Blo 2009435 3016781 := bbase (se 3 (by rfl) ⟨565646, by rfl⟩ : syracuseStep 3016781 = 1131293) (by norm_num)
theorem B2011187 : Blo 2009435 2011187 := bstep (se 1 (by rfl) ⟨1508390, by rfl⟩ : syracuseStep 2011187 = 3016781) B3016781
theorem B4525181 : Blo 2009435 4525181 := bbase (se 3 (by rfl) ⟨848471, by rfl⟩ : syracuseStep 4525181 = 1696943) (by norm_num)
theorem B3016787 : Blo 2009435 3016787 := bstep (se 1 (by rfl) ⟨2262590, by rfl⟩ : syracuseStep 3016787 = 4525181) B4525181
theorem B2011191 : Blo 2009435 2011191 := bstep (se 1 (by rfl) ⟨1508393, by rfl⟩ : syracuseStep 2011191 = 3016787) B3016787
theorem B3393893 : Blo 2009435 3393893 := bbase (se 4 (by rfl) ⟨318177, by rfl⟩ : syracuseStep 3393893 = 636355) (by norm_num)
theorem B2262595 : Blo 2009435 2262595 := bstep (se 1 (by rfl) ⟨1696946, by rfl⟩ : syracuseStep 2262595 = 3393893) B3393893
theorem B3016793 : Blo 2009435 3016793 := bstep (se 2 (by rfl) ⟨1131297, by rfl⟩ : syracuseStep 3016793 = 2262595) B2262595
theorem B2011195 : Blo 2009435 2011195 := bstep (se 1 (by rfl) ⟨1508396, by rfl⟩ : syracuseStep 2011195 = 3016793) B3016793
theorem B4295405 : Blo 2009435 4295405 := bbase (se 3 (by rfl) ⟨805388, by rfl⟩ : syracuseStep 4295405 = 1610777) (by norm_num)
theorem B2863603 : Blo 2009435 2863603 := bstep (se 1 (by rfl) ⟨2147702, by rfl⟩ : syracuseStep 2863603 = 4295405) B4295405
theorem B15272549 : Blo 2009435 15272549 := bstep (se 4 (by rfl) ⟨1431801, by rfl⟩ : syracuseStep 15272549 = 2863603) B2863603
theorem B10181699 : Blo 2009435 10181699 := bstep (se 1 (by rfl) ⟨7636274, by rfl⟩ : syracuseStep 10181699 = 15272549) B15272549
theorem B6787799 : Blo 2009435 6787799 := bstep (se 1 (by rfl) ⟨5090849, by rfl⟩ : syracuseStep 6787799 = 10181699) B10181699
theorem B4525199 : Blo 2009435 4525199 := bstep (se 1 (by rfl) ⟨3393899, by rfl⟩ : syracuseStep 4525199 = 6787799) B6787799
theorem B3016799 : Blo 2009435 3016799 := bstep (se 1 (by rfl) ⟨2262599, by rfl⟩ : syracuseStep 3016799 = 4525199) B4525199
theorem B2011199 : Blo 2009435 2011199 := bstep (se 1 (by rfl) ⟨1508399, by rfl⟩ : syracuseStep 2011199 = 3016799) B3016799
theorem B3016805 : Blo 2009435 3016805 := bbase (se 4 (by rfl) ⟨282825, by rfl⟩ : syracuseStep 3016805 = 565651) (by norm_num)
theorem B2011203 : Blo 2009435 2011203 := bstep (se 1 (by rfl) ⟨1508402, by rfl⟩ : syracuseStep 2011203 = 3016805) B3016805
theorem B9796565 : Blo 2009435 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B6531043 : Blo 2009435 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B8708057 : Blo 2009435 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B5805371 : Blo 2009435 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B3870247 : Blo 2009435 3870247 := bstep (se 1 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 3870247 = 5805371) B5805371
theorem B5160329 : Blo 2009435 5160329 := bstep (se 2 (by rfl) ⟨1935123, by rfl⟩ : syracuseStep 5160329 = 3870247) B3870247
theorem B55043509 : Blo 2009435 55043509 := bstep (se 5 (by rfl) ⟨2580164, by rfl⟩ : syracuseStep 55043509 = 5160329) B5160329
theorem B73391345 : Blo 2009435 73391345 := bstep (se 2 (by rfl) ⟨27521754, by rfl⟩ : syracuseStep 73391345 = 55043509) B55043509
theorem B48927563 : Blo 2009435 48927563 := bstep (se 1 (by rfl) ⟨36695672, by rfl⟩ : syracuseStep 48927563 = 73391345) B73391345
theorem B32618375 : Blo 2009435 32618375 := bstep (se 1 (by rfl) ⟨24463781, by rfl⟩ : syracuseStep 32618375 = 48927563) B48927563
theorem B21745583 : Blo 2009435 21745583 := bstep (se 1 (by rfl) ⟨16309187, by rfl⟩ : syracuseStep 21745583 = 32618375) B32618375
theorem B14497055 : Blo 2009435 14497055 := bstep (se 1 (by rfl) ⟨10872791, by rfl⟩ : syracuseStep 14497055 = 21745583) B21745583
theorem B9664703 : Blo 2009435 9664703 := bstep (se 1 (by rfl) ⟨7248527, by rfl⟩ : syracuseStep 9664703 = 14497055) B14497055
theorem B6443135 : Blo 2009435 6443135 := bstep (se 1 (by rfl) ⟨4832351, by rfl⟩ : syracuseStep 6443135 = 9664703) B9664703
theorem B4295423 : Blo 2009435 4295423 := bstep (se 1 (by rfl) ⟨3221567, by rfl⟩ : syracuseStep 4295423 = 6443135) B6443135
theorem B2863615 : Blo 2009435 2863615 := bstep (se 1 (by rfl) ⟨2147711, by rfl⟩ : syracuseStep 2863615 = 4295423) B4295423
theorem B3818153 : Blo 2009435 3818153 := bstep (se 2 (by rfl) ⟨1431807, by rfl⟩ : syracuseStep 3818153 = 2863615) B2863615
theorem B2545435 : Blo 2009435 2545435 := bstep (se 1 (by rfl) ⟨1909076, by rfl⟩ : syracuseStep 2545435 = 3818153) B3818153
theorem B3393913 : Blo 2009435 3393913 := bstep (se 2 (by rfl) ⟨1272717, by rfl⟩ : syracuseStep 3393913 = 2545435) B2545435
theorem B4525217 : Blo 2009435 4525217 := bstep (se 2 (by rfl) ⟨1696956, by rfl⟩ : syracuseStep 4525217 = 3393913) B3393913
theorem B3016811 : Blo 2009435 3016811 := bstep (se 1 (by rfl) ⟨2262608, by rfl⟩ : syracuseStep 3016811 = 4525217) B4525217
theorem B2011207 : Blo 2009435 2011207 := bstep (se 1 (by rfl) ⟨1508405, by rfl⟩ : syracuseStep 2011207 = 3016811) B3016811
theorem B2262613 : Blo 2009435 2262613 := bbase (se 8 (by rfl) ⟨13257, by rfl⟩ : syracuseStep 2262613 = 26515) (by norm_num)
theorem B3016817 : Blo 2009435 3016817 := bstep (se 2 (by rfl) ⟨1131306, by rfl⟩ : syracuseStep 3016817 = 2262613) B2262613
theorem B2011211 : Blo 2009435 2011211 := bstep (se 1 (by rfl) ⟨1508408, by rfl⟩ : syracuseStep 2011211 = 3016817) B3016817
theorem B2545445 : Blo 2009435 2545445 := bbase (se 4 (by rfl) ⟨238635, by rfl⟩ : syracuseStep 2545445 = 477271) (by norm_num)
theorem B6787853 : Blo 2009435 6787853 := bstep (se 3 (by rfl) ⟨1272722, by rfl⟩ : syracuseStep 6787853 = 2545445) B2545445
theorem B4525235 : Blo 2009435 4525235 := bstep (se 1 (by rfl) ⟨3393926, by rfl⟩ : syracuseStep 4525235 = 6787853) B6787853
theorem B3016823 : Blo 2009435 3016823 := bstep (se 1 (by rfl) ⟨2262617, by rfl⟩ : syracuseStep 3016823 = 4525235) B4525235
theorem B2011215 : Blo 2009435 2011215 := bstep (se 1 (by rfl) ⟨1508411, by rfl⟩ : syracuseStep 2011215 = 3016823) B3016823
theorem B3016829 : Blo 2009435 3016829 := bbase (se 3 (by rfl) ⟨565655, by rfl⟩ : syracuseStep 3016829 = 1131311) (by norm_num)
theorem B2011219 : Blo 2009435 2011219 := bstep (se 1 (by rfl) ⟨1508414, by rfl⟩ : syracuseStep 2011219 = 3016829) B3016829
theorem B4525253 : Blo 2009435 4525253 := bbase (se 4 (by rfl) ⟨424242, by rfl⟩ : syracuseStep 4525253 = 848485) (by norm_num)
theorem B3016835 : Blo 2009435 3016835 := bstep (se 1 (by rfl) ⟨2262626, by rfl⟩ : syracuseStep 3016835 = 4525253) B4525253
theorem B2011223 : Blo 2009435 2011223 := bstep (se 1 (by rfl) ⟨1508417, by rfl⟩ : syracuseStep 2011223 = 3016835) B3016835
theorem B4587005 : Blo 2009435 4587005 := bbase (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) (by norm_num)
theorem B3058003 : Blo 2009435 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B16309349 : Blo 2009435 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B10872899 : Blo 2009435 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B7248599 : Blo 2009435 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B4832399 : Blo 2009435 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B12886397 : Blo 2009435 12886397 := bstep (se 3 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 12886397 = 4832399) B4832399
theorem B8590931 : Blo 2009435 8590931 := bstep (se 1 (by rfl) ⟨6443198, by rfl⟩ : syracuseStep 8590931 = 12886397) B12886397
theorem B5727287 : Blo 2009435 5727287 := bstep (se 1 (by rfl) ⟨4295465, by rfl⟩ : syracuseStep 5727287 = 8590931) B8590931
theorem B3818191 : Blo 2009435 3818191 := bstep (se 1 (by rfl) ⟨2863643, by rfl⟩ : syracuseStep 3818191 = 5727287) B5727287
theorem B5090921 : Blo 2009435 5090921 := bstep (se 2 (by rfl) ⟨1909095, by rfl⟩ : syracuseStep 5090921 = 3818191) B3818191
theorem B3393947 : Blo 2009435 3393947 := bstep (se 1 (by rfl) ⟨2545460, by rfl⟩ : syracuseStep 3393947 = 5090921) B5090921
theorem B2262631 : Blo 2009435 2262631 := bstep (se 1 (by rfl) ⟨1696973, by rfl⟩ : syracuseStep 2262631 = 3393947) B3393947
theorem B3016841 : Blo 2009435 3016841 := bstep (se 2 (by rfl) ⟨1131315, by rfl⟩ : syracuseStep 3016841 = 2262631) B2262631
theorem B2011227 : Blo 2009435 2011227 := bstep (se 1 (by rfl) ⟨1508420, by rfl⟩ : syracuseStep 2011227 = 3016841) B3016841
theorem B10181861 : Blo 2009435 10181861 := bbase (se 4 (by rfl) ⟨954549, by rfl⟩ : syracuseStep 10181861 = 1909099) (by norm_num)
theorem B6787907 : Blo 2009435 6787907 := bstep (se 1 (by rfl) ⟨5090930, by rfl⟩ : syracuseStep 6787907 = 10181861) B10181861
theorem B4525271 : Blo 2009435 4525271 := bstep (se 1 (by rfl) ⟨3393953, by rfl⟩ : syracuseStep 4525271 = 6787907) B6787907
theorem B3016847 : Blo 2009435 3016847 := bstep (se 1 (by rfl) ⟨2262635, by rfl⟩ : syracuseStep 3016847 = 4525271) B4525271
theorem B2011231 : Blo 2009435 2011231 := bstep (se 1 (by rfl) ⟨1508423, by rfl⟩ : syracuseStep 2011231 = 3016847) B3016847
theorem B3016853 : Blo 2009435 3016853 := bbase (se 6 (by rfl) ⟨70707, by rfl⟩ : syracuseStep 3016853 = 141415) (by norm_num)
theorem B2011235 : Blo 2009435 2011235 := bstep (se 1 (by rfl) ⟨1508426, by rfl⟩ : syracuseStep 2011235 = 3016853) B3016853
theorem B8590981 : Blo 2009435 8590981 := bbase (se 4 (by rfl) ⟨805404, by rfl⟩ : syracuseStep 8590981 = 1610809) (by norm_num)
theorem B11454641 : Blo 2009435 11454641 := bstep (se 2 (by rfl) ⟨4295490, by rfl⟩ : syracuseStep 11454641 = 8590981) B8590981
theorem B7636427 : Blo 2009435 7636427 := bstep (se 1 (by rfl) ⟨5727320, by rfl⟩ : syracuseStep 7636427 = 11454641) B11454641
theorem B5090951 : Blo 2009435 5090951 := bstep (se 1 (by rfl) ⟨3818213, by rfl⟩ : syracuseStep 5090951 = 7636427) B7636427
theorem B3393967 : Blo 2009435 3393967 := bstep (se 1 (by rfl) ⟨2545475, by rfl⟩ : syracuseStep 3393967 = 5090951) B5090951
theorem B4525289 : Blo 2009435 4525289 := bstep (se 2 (by rfl) ⟨1696983, by rfl⟩ : syracuseStep 4525289 = 3393967) B3393967
theorem B3016859 : Blo 2009435 3016859 := bstep (se 1 (by rfl) ⟨2262644, by rfl⟩ : syracuseStep 3016859 = 4525289) B4525289
theorem B2011239 : Blo 2009435 2011239 := bstep (se 1 (by rfl) ⟨1508429, by rfl⟩ : syracuseStep 2011239 = 3016859) B3016859
theorem B2262649 : Blo 2009435 2262649 := bbase (se 2 (by rfl) ⟨848493, by rfl⟩ : syracuseStep 2262649 = 1696987) (by norm_num)
theorem B3016865 : Blo 2009435 3016865 := bstep (se 2 (by rfl) ⟨1131324, by rfl⟩ : syracuseStep 3016865 = 2262649) B2262649
theorem B2011243 : Blo 2009435 2011243 := bstep (se 1 (by rfl) ⟨1508432, by rfl⟩ : syracuseStep 2011243 = 3016865) B3016865
theorem B3310141 : Blo 2009435 3310141 := bbase (se 3 (by rfl) ⟨620651, by rfl⟩ : syracuseStep 3310141 = 1241303) (by norm_num)
theorem B4413521 : Blo 2009435 4413521 := bstep (se 2 (by rfl) ⟨1655070, by rfl⟩ : syracuseStep 4413521 = 3310141) B3310141
theorem B2942347 : Blo 2009435 2942347 := bstep (se 1 (by rfl) ⟨2206760, by rfl⟩ : syracuseStep 2942347 = 4413521) B4413521
theorem B3923129 : Blo 2009435 3923129 := bstep (se 2 (by rfl) ⟨1471173, by rfl⟩ : syracuseStep 3923129 = 2942347) B2942347
theorem B2615419 : Blo 2009435 2615419 := bstep (se 1 (by rfl) ⟨1961564, by rfl⟩ : syracuseStep 2615419 = 3923129) B3923129
theorem B13948901 : Blo 2009435 13948901 := bstep (se 4 (by rfl) ⟨1307709, by rfl⟩ : syracuseStep 13948901 = 2615419) B2615419
theorem B9299267 : Blo 2009435 9299267 := bstep (se 1 (by rfl) ⟨6974450, by rfl⟩ : syracuseStep 9299267 = 13948901) B13948901
theorem B6199511 : Blo 2009435 6199511 := bstep (se 1 (by rfl) ⟨4649633, by rfl⟩ : syracuseStep 6199511 = 9299267) B9299267
theorem B16532029 : Blo 2009435 16532029 := bstep (se 3 (by rfl) ⟨3099755, by rfl⟩ : syracuseStep 16532029 = 6199511) B6199511
theorem B22042705 : Blo 2009435 22042705 := bstep (se 2 (by rfl) ⟨8266014, by rfl⟩ : syracuseStep 22042705 = 16532029) B16532029
theorem B29390273 : Blo 2009435 29390273 := bstep (se 2 (by rfl) ⟨11021352, by rfl⟩ : syracuseStep 29390273 = 22042705) B22042705
theorem B19593515 : Blo 2009435 19593515 := bstep (se 1 (by rfl) ⟨14695136, by rfl⟩ : syracuseStep 19593515 = 29390273) B29390273
theorem B13062343 : Blo 2009435 13062343 := bstep (se 1 (by rfl) ⟨9796757, by rfl⟩ : syracuseStep 13062343 = 19593515) B19593515
theorem B17416457 : Blo 2009435 17416457 := bstep (se 2 (by rfl) ⟨6531171, by rfl⟩ : syracuseStep 17416457 = 13062343) B13062343
theorem B11610971 : Blo 2009435 11610971 := bstep (se 1 (by rfl) ⟨8708228, by rfl⟩ : syracuseStep 11610971 = 17416457) B17416457
theorem B7740647 : Blo 2009435 7740647 := bstep (se 1 (by rfl) ⟨5805485, by rfl⟩ : syracuseStep 7740647 = 11610971) B11610971
theorem B5160431 : Blo 2009435 5160431 := bstep (se 1 (by rfl) ⟨3870323, by rfl⟩ : syracuseStep 5160431 = 7740647) B7740647
theorem B3440287 : Blo 2009435 3440287 := bstep (se 1 (by rfl) ⟨2580215, by rfl⟩ : syracuseStep 3440287 = 5160431) B5160431
theorem B4587049 : Blo 2009435 4587049 := bstep (se 2 (by rfl) ⟨1720143, by rfl⟩ : syracuseStep 4587049 = 3440287) B3440287
theorem B24464261 : Blo 2009435 24464261 := bstep (se 4 (by rfl) ⟨2293524, by rfl⟩ : syracuseStep 24464261 = 4587049) B4587049
theorem B16309507 : Blo 2009435 16309507 := bstep (se 1 (by rfl) ⟨12232130, by rfl⟩ : syracuseStep 16309507 = 24464261) B24464261
theorem B21746009 : Blo 2009435 21746009 := bstep (se 2 (by rfl) ⟨8154753, by rfl⟩ : syracuseStep 21746009 = 16309507) B16309507
theorem B14497339 : Blo 2009435 14497339 := bstep (se 1 (by rfl) ⟨10873004, by rfl⟩ : syracuseStep 14497339 = 21746009) B21746009
theorem B19329785 : Blo 2009435 19329785 := bstep (se 2 (by rfl) ⟨7248669, by rfl⟩ : syracuseStep 19329785 = 14497339) B14497339
theorem B12886523 : Blo 2009435 12886523 := bstep (se 1 (by rfl) ⟨9664892, by rfl⟩ : syracuseStep 12886523 = 19329785) B19329785
theorem B8591015 : Blo 2009435 8591015 := bstep (se 1 (by rfl) ⟨6443261, by rfl⟩ : syracuseStep 8591015 = 12886523) B12886523
theorem B5727343 : Blo 2009435 5727343 := bstep (se 1 (by rfl) ⟨4295507, by rfl⟩ : syracuseStep 5727343 = 8591015) B8591015
theorem B7636457 : Blo 2009435 7636457 := bstep (se 2 (by rfl) ⟨2863671, by rfl⟩ : syracuseStep 7636457 = 5727343) B5727343
theorem B5090971 : Blo 2009435 5090971 := bstep (se 1 (by rfl) ⟨3818228, by rfl⟩ : syracuseStep 5090971 = 7636457) B7636457
theorem B6787961 : Blo 2009435 6787961 := bstep (se 2 (by rfl) ⟨2545485, by rfl⟩ : syracuseStep 6787961 = 5090971) B5090971
theorem B4525307 : Blo 2009435 4525307 := bstep (se 1 (by rfl) ⟨3393980, by rfl⟩ : syracuseStep 4525307 = 6787961) B6787961
theorem B3016871 : Blo 2009435 3016871 := bstep (se 1 (by rfl) ⟨2262653, by rfl⟩ : syracuseStep 3016871 = 4525307) B4525307
theorem B2011247 : Blo 2009435 2011247 := bstep (se 1 (by rfl) ⟨1508435, by rfl⟩ : syracuseStep 2011247 = 3016871) B3016871
theorem B3016877 : Blo 2009435 3016877 := bbase (se 3 (by rfl) ⟨565664, by rfl⟩ : syracuseStep 3016877 = 1131329) (by norm_num)
theorem B2011251 : Blo 2009435 2011251 := bstep (se 1 (by rfl) ⟨1508438, by rfl⟩ : syracuseStep 2011251 = 3016877) B3016877
theorem B4525325 : Blo 2009435 4525325 := bbase (se 3 (by rfl) ⟨848498, by rfl⟩ : syracuseStep 4525325 = 1696997) (by norm_num)
theorem B3016883 : Blo 2009435 3016883 := bstep (se 1 (by rfl) ⟨2262662, by rfl⟩ : syracuseStep 3016883 = 4525325) B4525325
theorem B2011255 : Blo 2009435 2011255 := bstep (se 1 (by rfl) ⟨1508441, by rfl⟩ : syracuseStep 2011255 = 3016883) B3016883
theorem B2545501 : Blo 2009435 2545501 := bbase (se 3 (by rfl) ⟨477281, by rfl⟩ : syracuseStep 2545501 = 954563) (by norm_num)
theorem B3394001 : Blo 2009435 3394001 := bstep (se 2 (by rfl) ⟨1272750, by rfl⟩ : syracuseStep 3394001 = 2545501) B2545501
theorem B2262667 : Blo 2009435 2262667 := bstep (se 1 (by rfl) ⟨1697000, by rfl⟩ : syracuseStep 2262667 = 3394001) B3394001
theorem B3016889 : Blo 2009435 3016889 := bstep (se 2 (by rfl) ⟨1131333, by rfl⟩ : syracuseStep 3016889 = 2262667) B2262667
theorem B2011259 : Blo 2009435 2011259 := bstep (se 1 (by rfl) ⟨1508444, by rfl⟩ : syracuseStep 2011259 = 3016889) B3016889
theorem B17182165 : Blo 2009435 17182165 := bbase (se 7 (by rfl) ⟨201353, by rfl⟩ : syracuseStep 17182165 = 402707) (by norm_num)
theorem B22909553 : Blo 2009435 22909553 := bstep (se 2 (by rfl) ⟨8591082, by rfl⟩ : syracuseStep 22909553 = 17182165) B17182165
theorem B15273035 : Blo 2009435 15273035 := bstep (se 1 (by rfl) ⟨11454776, by rfl⟩ : syracuseStep 15273035 = 22909553) B22909553
theorem B10182023 : Blo 2009435 10182023 := bstep (se 1 (by rfl) ⟨7636517, by rfl⟩ : syracuseStep 10182023 = 15273035) B15273035
theorem B6788015 : Blo 2009435 6788015 := bstep (se 1 (by rfl) ⟨5091011, by rfl⟩ : syracuseStep 6788015 = 10182023) B10182023
theorem B4525343 : Blo 2009435 4525343 := bstep (se 1 (by rfl) ⟨3394007, by rfl⟩ : syracuseStep 4525343 = 6788015) B6788015
theorem B3016895 : Blo 2009435 3016895 := bstep (se 1 (by rfl) ⟨2262671, by rfl⟩ : syracuseStep 3016895 = 4525343) B4525343
theorem B2011263 : Blo 2009435 2011263 := bstep (se 1 (by rfl) ⟨1508447, by rfl⟩ : syracuseStep 2011263 = 3016895) B3016895
theorem B3016901 : Blo 2009435 3016901 := bbase (se 4 (by rfl) ⟨282834, by rfl⟩ : syracuseStep 3016901 = 565669) (by norm_num)
theorem B2011267 : Blo 2009435 2011267 := bstep (se 1 (by rfl) ⟨1508450, by rfl⟩ : syracuseStep 2011267 = 3016901) B3016901
theorem B3394021 : Blo 2009435 3394021 := bbase (se 4 (by rfl) ⟨318189, by rfl⟩ : syracuseStep 3394021 = 636379) (by norm_num)
theorem B4525361 : Blo 2009435 4525361 := bstep (se 2 (by rfl) ⟨1697010, by rfl⟩ : syracuseStep 4525361 = 3394021) B3394021
theorem B3016907 : Blo 2009435 3016907 := bstep (se 1 (by rfl) ⟨2262680, by rfl⟩ : syracuseStep 3016907 = 4525361) B4525361
theorem B2011271 : Blo 2009435 2011271 := bstep (se 1 (by rfl) ⟨1508453, by rfl⟩ : syracuseStep 2011271 = 3016907) B3016907
theorem B2262685 : Blo 2009435 2262685 := bbase (se 3 (by rfl) ⟨424253, by rfl⟩ : syracuseStep 2262685 = 848507) (by norm_num)
theorem B3016913 : Blo 2009435 3016913 := bstep (se 2 (by rfl) ⟨1131342, by rfl⟩ : syracuseStep 3016913 = 2262685) B2262685
theorem B2011275 : Blo 2009435 2011275 := bstep (se 1 (by rfl) ⟨1508456, by rfl⟩ : syracuseStep 2011275 = 3016913) B3016913
theorem B6788069 : Blo 2009435 6788069 := bbase (se 4 (by rfl) ⟨636381, by rfl⟩ : syracuseStep 6788069 = 1272763) (by norm_num)
theorem B4525379 : Blo 2009435 4525379 := bstep (se 1 (by rfl) ⟨3394034, by rfl⟩ : syracuseStep 4525379 = 6788069) B6788069
theorem B3016919 : Blo 2009435 3016919 := bstep (se 1 (by rfl) ⟨2262689, by rfl⟩ : syracuseStep 3016919 = 4525379) B4525379
theorem B2011279 : Blo 2009435 2011279 := bstep (se 1 (by rfl) ⟨1508459, by rfl⟩ : syracuseStep 2011279 = 3016919) B3016919
theorem B3016925 : Blo 2009435 3016925 := bbase (se 3 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 3016925 = 1131347) (by norm_num)
theorem B2011283 : Blo 2009435 2011283 := bstep (se 1 (by rfl) ⟨1508462, by rfl⟩ : syracuseStep 2011283 = 3016925) B3016925
theorem B4525397 : Blo 2009435 4525397 := bbase (se 11 (by rfl) ⟨3314, by rfl⟩ : syracuseStep 4525397 = 6629) (by norm_num)
theorem B3016931 : Blo 2009435 3016931 := bstep (se 1 (by rfl) ⟨2262698, by rfl⟩ : syracuseStep 3016931 = 4525397) B4525397
theorem B2011287 : Blo 2009435 2011287 := bstep (se 1 (by rfl) ⟨1508465, by rfl⟩ : syracuseStep 2011287 = 3016931) B3016931
theorem B2147801 : Blo 2009435 2147801 := bbase (se 2 (by rfl) ⟨805425, by rfl⟩ : syracuseStep 2147801 = 1610851) (by norm_num)
theorem B5727469 : Blo 2009435 5727469 := bstep (se 3 (by rfl) ⟨1073900, by rfl⟩ : syracuseStep 5727469 = 2147801) B2147801
theorem B7636625 : Blo 2009435 7636625 := bstep (se 2 (by rfl) ⟨2863734, by rfl⟩ : syracuseStep 7636625 = 5727469) B5727469
theorem B5091083 : Blo 2009435 5091083 := bstep (se 1 (by rfl) ⟨3818312, by rfl⟩ : syracuseStep 5091083 = 7636625) B7636625
theorem B3394055 : Blo 2009435 3394055 := bstep (se 1 (by rfl) ⟨2545541, by rfl⟩ : syracuseStep 3394055 = 5091083) B5091083
theorem B2262703 : Blo 2009435 2262703 := bstep (se 1 (by rfl) ⟨1697027, by rfl⟩ : syracuseStep 2262703 = 3394055) B3394055
theorem B3016937 : Blo 2009435 3016937 := bstep (se 2 (by rfl) ⟨1131351, by rfl⟩ : syracuseStep 3016937 = 2262703) B2262703
theorem B2011291 : Blo 2009435 2011291 := bstep (se 1 (by rfl) ⟨1508468, by rfl⟩ : syracuseStep 2011291 = 3016937) B3016937
theorem B6620437 : Blo 2009435 6620437 := bbase (se 6 (by rfl) ⟨155166, by rfl⟩ : syracuseStep 6620437 = 310333) (by norm_num)
theorem B35308997 : Blo 2009435 35308997 := bstep (se 4 (by rfl) ⟨3310218, by rfl⟩ : syracuseStep 35308997 = 6620437) B6620437
theorem B23539331 : Blo 2009435 23539331 := bstep (se 1 (by rfl) ⟨17654498, by rfl⟩ : syracuseStep 23539331 = 35308997) B35308997
theorem B15692887 : Blo 2009435 15692887 := bstep (se 1 (by rfl) ⟨11769665, by rfl⟩ : syracuseStep 15692887 = 23539331) B23539331
theorem B20923849 : Blo 2009435 20923849 := bstep (se 2 (by rfl) ⟨7846443, by rfl⟩ : syracuseStep 20923849 = 15692887) B15692887
theorem B27898465 : Blo 2009435 27898465 := bstep (se 2 (by rfl) ⟨10461924, by rfl⟩ : syracuseStep 27898465 = 20923849) B20923849
theorem B37197953 : Blo 2009435 37197953 := bstep (se 2 (by rfl) ⟨13949232, by rfl⟩ : syracuseStep 37197953 = 27898465) B27898465
theorem B24798635 : Blo 2009435 24798635 := bstep (se 1 (by rfl) ⟨18598976, by rfl⟩ : syracuseStep 24798635 = 37197953) B37197953
theorem B16532423 : Blo 2009435 16532423 := bstep (se 1 (by rfl) ⟨12399317, by rfl⟩ : syracuseStep 16532423 = 24798635) B24798635
theorem B11021615 : Blo 2009435 11021615 := bstep (se 1 (by rfl) ⟨8266211, by rfl⟩ : syracuseStep 11021615 = 16532423) B16532423
theorem B7347743 : Blo 2009435 7347743 := bstep (se 1 (by rfl) ⟨5510807, by rfl⟩ : syracuseStep 7347743 = 11021615) B11021615
theorem B4898495 : Blo 2009435 4898495 := bstep (se 1 (by rfl) ⟨3673871, by rfl⟩ : syracuseStep 4898495 = 7347743) B7347743
theorem B3265663 : Blo 2009435 3265663 := bstep (se 1 (by rfl) ⟨2449247, by rfl⟩ : syracuseStep 3265663 = 4898495) B4898495
theorem B4354217 : Blo 2009435 4354217 := bstep (se 2 (by rfl) ⟨1632831, by rfl⟩ : syracuseStep 4354217 = 3265663) B3265663
theorem B2902811 : Blo 2009435 2902811 := bstep (se 1 (by rfl) ⟨2177108, by rfl⟩ : syracuseStep 2902811 = 4354217) B4354217
theorem B7740829 : Blo 2009435 7740829 := bstep (se 3 (by rfl) ⟨1451405, by rfl⟩ : syracuseStep 7740829 = 2902811) B2902811
theorem B41284421 : Blo 2009435 41284421 := bstep (se 4 (by rfl) ⟨3870414, by rfl⟩ : syracuseStep 41284421 = 7740829) B7740829
theorem B27522947 : Blo 2009435 27522947 := bstep (se 1 (by rfl) ⟨20642210, by rfl⟩ : syracuseStep 27522947 = 41284421) B41284421
theorem B73394525 : Blo 2009435 73394525 := bstep (se 3 (by rfl) ⟨13761473, by rfl⟩ : syracuseStep 73394525 = 27522947) B27522947
theorem B48929683 : Blo 2009435 48929683 := bstep (se 1 (by rfl) ⟨36697262, by rfl⟩ : syracuseStep 48929683 = 73394525) B73394525
theorem B65239577 : Blo 2009435 65239577 := bstep (se 2 (by rfl) ⟨24464841, by rfl⟩ : syracuseStep 65239577 = 48929683) B48929683
theorem B43493051 : Blo 2009435 43493051 := bstep (se 1 (by rfl) ⟨32619788, by rfl⟩ : syracuseStep 43493051 = 65239577) B65239577
theorem B28995367 : Blo 2009435 28995367 := bstep (se 1 (by rfl) ⟨21746525, by rfl⟩ : syracuseStep 28995367 = 43493051) B43493051
theorem B38660489 : Blo 2009435 38660489 := bstep (se 2 (by rfl) ⟨14497683, by rfl⟩ : syracuseStep 38660489 = 28995367) B28995367
theorem B25773659 : Blo 2009435 25773659 := bstep (se 1 (by rfl) ⟨19330244, by rfl⟩ : syracuseStep 25773659 = 38660489) B38660489
theorem B17182439 : Blo 2009435 17182439 := bstep (se 1 (by rfl) ⟨12886829, by rfl⟩ : syracuseStep 17182439 = 25773659) B25773659
theorem B11454959 : Blo 2009435 11454959 := bstep (se 1 (by rfl) ⟨8591219, by rfl⟩ : syracuseStep 11454959 = 17182439) B17182439
theorem B7636639 : Blo 2009435 7636639 := bstep (se 1 (by rfl) ⟨5727479, by rfl⟩ : syracuseStep 7636639 = 11454959) B11454959
theorem B10182185 : Blo 2009435 10182185 := bstep (se 2 (by rfl) ⟨3818319, by rfl⟩ : syracuseStep 10182185 = 7636639) B7636639
theorem B6788123 : Blo 2009435 6788123 := bstep (se 1 (by rfl) ⟨5091092, by rfl⟩ : syracuseStep 6788123 = 10182185) B10182185
theorem B4525415 : Blo 2009435 4525415 := bstep (se 1 (by rfl) ⟨3394061, by rfl⟩ : syracuseStep 4525415 = 6788123) B6788123
theorem B3016943 : Blo 2009435 3016943 := bstep (se 1 (by rfl) ⟨2262707, by rfl⟩ : syracuseStep 3016943 = 4525415) B4525415
theorem B2011295 : Blo 2009435 2011295 := bstep (se 1 (by rfl) ⟨1508471, by rfl⟩ : syracuseStep 2011295 = 3016943) B3016943
theorem B3016949 : Blo 2009435 3016949 := bbase (se 5 (by rfl) ⟨141419, by rfl⟩ : syracuseStep 3016949 = 282839) (by norm_num)
theorem B2011299 : Blo 2009435 2011299 := bstep (se 1 (by rfl) ⟨1508474, by rfl⟩ : syracuseStep 2011299 = 3016949) B3016949
theorem B19330325 : Blo 2009435 19330325 := bbase (se 6 (by rfl) ⟨453054, by rfl⟩ : syracuseStep 19330325 = 906109) (by norm_num)
theorem B12886883 : Blo 2009435 12886883 := bstep (se 1 (by rfl) ⟨9665162, by rfl⟩ : syracuseStep 12886883 = 19330325) B19330325
theorem B8591255 : Blo 2009435 8591255 := bstep (se 1 (by rfl) ⟨6443441, by rfl⟩ : syracuseStep 8591255 = 12886883) B12886883
theorem B5727503 : Blo 2009435 5727503 := bstep (se 1 (by rfl) ⟨4295627, by rfl⟩ : syracuseStep 5727503 = 8591255) B8591255
theorem B3818335 : Blo 2009435 3818335 := bstep (se 1 (by rfl) ⟨2863751, by rfl⟩ : syracuseStep 3818335 = 5727503) B5727503
theorem B5091113 : Blo 2009435 5091113 := bstep (se 2 (by rfl) ⟨1909167, by rfl⟩ : syracuseStep 5091113 = 3818335) B3818335
theorem B3394075 : Blo 2009435 3394075 := bstep (se 1 (by rfl) ⟨2545556, by rfl⟩ : syracuseStep 3394075 = 5091113) B5091113
theorem B4525433 : Blo 2009435 4525433 := bstep (se 2 (by rfl) ⟨1697037, by rfl⟩ : syracuseStep 4525433 = 3394075) B3394075
theorem B3016955 : Blo 2009435 3016955 := bstep (se 1 (by rfl) ⟨2262716, by rfl⟩ : syracuseStep 3016955 = 4525433) B4525433
theorem B2011303 : Blo 2009435 2011303 := bstep (se 1 (by rfl) ⟨1508477, by rfl⟩ : syracuseStep 2011303 = 3016955) B3016955
theorem B2262721 : Blo 2009435 2262721 := bbase (se 2 (by rfl) ⟨848520, by rfl⟩ : syracuseStep 2262721 = 1697041) (by norm_num)
theorem B3016961 : Blo 2009435 3016961 := bstep (se 2 (by rfl) ⟨1131360, by rfl⟩ : syracuseStep 3016961 = 2262721) B2262721
theorem B2011307 : Blo 2009435 2011307 := bstep (se 1 (by rfl) ⟨1508480, by rfl⟩ : syracuseStep 2011307 = 3016961) B3016961
theorem B5091133 : Blo 2009435 5091133 := bbase (se 3 (by rfl) ⟨954587, by rfl⟩ : syracuseStep 5091133 = 1909175) (by norm_num)
theorem B6788177 : Blo 2009435 6788177 := bstep (se 2 (by rfl) ⟨2545566, by rfl⟩ : syracuseStep 6788177 = 5091133) B5091133
theorem B4525451 : Blo 2009435 4525451 := bstep (se 1 (by rfl) ⟨3394088, by rfl⟩ : syracuseStep 4525451 = 6788177) B6788177
theorem B3016967 : Blo 2009435 3016967 := bstep (se 1 (by rfl) ⟨2262725, by rfl⟩ : syracuseStep 3016967 = 4525451) B4525451
theorem B2011311 : Blo 2009435 2011311 := bstep (se 1 (by rfl) ⟨1508483, by rfl⟩ : syracuseStep 2011311 = 3016967) B3016967
theorem B3016973 : Blo 2009435 3016973 := bbase (se 3 (by rfl) ⟨565682, by rfl⟩ : syracuseStep 3016973 = 1131365) (by norm_num)
theorem B2011315 : Blo 2009435 2011315 := bstep (se 1 (by rfl) ⟨1508486, by rfl⟩ : syracuseStep 2011315 = 3016973) B3016973
theorem B4525469 : Blo 2009435 4525469 := bbase (se 3 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 4525469 = 1697051) (by norm_num)
theorem B3016979 : Blo 2009435 3016979 := bstep (se 1 (by rfl) ⟨2262734, by rfl⟩ : syracuseStep 3016979 = 4525469) B4525469
theorem B2011319 : Blo 2009435 2011319 := bstep (se 1 (by rfl) ⟨1508489, by rfl⟩ : syracuseStep 2011319 = 3016979) B3016979
theorem B3394109 : Blo 2009435 3394109 := bbase (se 3 (by rfl) ⟨636395, by rfl⟩ : syracuseStep 3394109 = 1272791) (by norm_num)
theorem B2262739 : Blo 2009435 2262739 := bstep (se 1 (by rfl) ⟨1697054, by rfl⟩ : syracuseStep 2262739 = 3394109) B3394109
theorem B3016985 : Blo 2009435 3016985 := bstep (se 2 (by rfl) ⟨1131369, by rfl⟩ : syracuseStep 3016985 = 2262739) B2262739
theorem B2011323 : Blo 2009435 2011323 := bstep (se 1 (by rfl) ⟨1508492, by rfl⟩ : syracuseStep 2011323 = 3016985) B3016985
theorem B6370085 : Blo 2009435 6370085 := bbase (se 4 (by rfl) ⟨597195, by rfl⟩ : syracuseStep 6370085 = 1194391) (by norm_num)
theorem B4246723 : Blo 2009435 4246723 := bstep (se 1 (by rfl) ⟨3185042, by rfl⟩ : syracuseStep 4246723 = 6370085) B6370085
theorem B5662297 : Blo 2009435 5662297 := bstep (se 2 (by rfl) ⟨2123361, by rfl⟩ : syracuseStep 5662297 = 4246723) B4246723
theorem B7549729 : Blo 2009435 7549729 := bstep (se 2 (by rfl) ⟨2831148, by rfl⟩ : syracuseStep 7549729 = 5662297) B5662297
theorem B161060885 : Blo 2009435 161060885 := bstep (se 6 (by rfl) ⟨3774864, by rfl⟩ : syracuseStep 161060885 = 7549729) B7549729
theorem B107373923 : Blo 2009435 107373923 := bstep (se 1 (by rfl) ⟨80530442, by rfl⟩ : syracuseStep 107373923 = 161060885) B161060885
theorem B71582615 : Blo 2009435 71582615 := bstep (se 1 (by rfl) ⟨53686961, by rfl⟩ : syracuseStep 71582615 = 107373923) B107373923
theorem B47721743 : Blo 2009435 47721743 := bstep (se 1 (by rfl) ⟨35791307, by rfl⟩ : syracuseStep 47721743 = 71582615) B71582615
theorem B31814495 : Blo 2009435 31814495 := bstep (se 1 (by rfl) ⟨23860871, by rfl⟩ : syracuseStep 31814495 = 47721743) B47721743
theorem B21209663 : Blo 2009435 21209663 := bstep (se 1 (by rfl) ⟨15907247, by rfl⟩ : syracuseStep 21209663 = 31814495) B31814495
theorem B14139775 : Blo 2009435 14139775 := bstep (se 1 (by rfl) ⟨10604831, by rfl⟩ : syracuseStep 14139775 = 21209663) B21209663
theorem B75412133 : Blo 2009435 75412133 := bstep (se 4 (by rfl) ⟨7069887, by rfl⟩ : syracuseStep 75412133 = 14139775) B14139775
theorem B50274755 : Blo 2009435 50274755 := bstep (se 1 (by rfl) ⟨37706066, by rfl⟩ : syracuseStep 50274755 = 75412133) B75412133
theorem B33516503 : Blo 2009435 33516503 := bstep (se 1 (by rfl) ⟨25137377, by rfl⟩ : syracuseStep 33516503 = 50274755) B50274755
theorem B22344335 : Blo 2009435 22344335 := bstep (se 1 (by rfl) ⟨16758251, by rfl⟩ : syracuseStep 22344335 = 33516503) B33516503
theorem B14896223 : Blo 2009435 14896223 := bstep (se 1 (by rfl) ⟨11172167, by rfl⟩ : syracuseStep 14896223 = 22344335) B22344335
theorem B9930815 : Blo 2009435 9930815 := bstep (se 1 (by rfl) ⟨7448111, by rfl⟩ : syracuseStep 9930815 = 14896223) B14896223
theorem B6620543 : Blo 2009435 6620543 := bstep (se 1 (by rfl) ⟨4965407, by rfl⟩ : syracuseStep 6620543 = 9930815) B9930815
theorem B4413695 : Blo 2009435 4413695 := bstep (se 1 (by rfl) ⟨3310271, by rfl⟩ : syracuseStep 4413695 = 6620543) B6620543
theorem B47079413 : Blo 2009435 47079413 := bstep (se 5 (by rfl) ⟨2206847, by rfl⟩ : syracuseStep 47079413 = 4413695) B4413695
theorem B31386275 : Blo 2009435 31386275 := bstep (se 1 (by rfl) ⟨23539706, by rfl⟩ : syracuseStep 31386275 = 47079413) B47079413
theorem B20924183 : Blo 2009435 20924183 := bstep (se 1 (by rfl) ⟨15693137, by rfl⟩ : syracuseStep 20924183 = 31386275) B31386275
theorem B55797821 : Blo 2009435 55797821 := bstep (se 3 (by rfl) ⟨10462091, by rfl⟩ : syracuseStep 55797821 = 20924183) B20924183
theorem B37198547 : Blo 2009435 37198547 := bstep (se 1 (by rfl) ⟨27898910, by rfl⟩ : syracuseStep 37198547 = 55797821) B55797821
theorem B24799031 : Blo 2009435 24799031 := bstep (se 1 (by rfl) ⟨18599273, by rfl⟩ : syracuseStep 24799031 = 37198547) B37198547
theorem B16532687 : Blo 2009435 16532687 := bstep (se 1 (by rfl) ⟨12399515, by rfl⟩ : syracuseStep 16532687 = 24799031) B24799031
theorem B44087165 : Blo 2009435 44087165 := bstep (se 3 (by rfl) ⟨8266343, by rfl⟩ : syracuseStep 44087165 = 16532687) B16532687
theorem B29391443 : Blo 2009435 29391443 := bstep (se 1 (by rfl) ⟨22043582, by rfl⟩ : syracuseStep 29391443 = 44087165) B44087165
theorem B19594295 : Blo 2009435 19594295 := bstep (se 1 (by rfl) ⟨14695721, by rfl⟩ : syracuseStep 19594295 = 29391443) B29391443
theorem B13062863 : Blo 2009435 13062863 := bstep (se 1 (by rfl) ⟨9797147, by rfl⟩ : syracuseStep 13062863 = 19594295) B19594295
theorem B8708575 : Blo 2009435 8708575 := bstep (se 1 (by rfl) ⟨6531431, by rfl⟩ : syracuseStep 8708575 = 13062863) B13062863
theorem B11611433 : Blo 2009435 11611433 := bstep (se 2 (by rfl) ⟨4354287, by rfl⟩ : syracuseStep 11611433 = 8708575) B8708575
theorem B7740955 : Blo 2009435 7740955 := bstep (se 1 (by rfl) ⟨5805716, by rfl⟩ : syracuseStep 7740955 = 11611433) B11611433
theorem B10321273 : Blo 2009435 10321273 := bstep (se 2 (by rfl) ⟨3870477, by rfl⟩ : syracuseStep 10321273 = 7740955) B7740955
theorem B55046789 : Blo 2009435 55046789 := bstep (se 4 (by rfl) ⟨5160636, by rfl⟩ : syracuseStep 55046789 = 10321273) B10321273
theorem B36697859 : Blo 2009435 36697859 := bstep (se 1 (by rfl) ⟨27523394, by rfl⟩ : syracuseStep 36697859 = 55046789) B55046789
theorem B24465239 : Blo 2009435 24465239 := bstep (se 1 (by rfl) ⟨18348929, by rfl⟩ : syracuseStep 24465239 = 36697859) B36697859
theorem B16310159 : Blo 2009435 16310159 := bstep (se 1 (by rfl) ⟨12232619, by rfl⟩ : syracuseStep 16310159 = 24465239) B24465239
theorem B10873439 : Blo 2009435 10873439 := bstep (se 1 (by rfl) ⟨8155079, by rfl⟩ : syracuseStep 10873439 = 16310159) B16310159
theorem B7248959 : Blo 2009435 7248959 := bstep (se 1 (by rfl) ⟨5436719, by rfl⟩ : syracuseStep 7248959 = 10873439) B10873439
theorem B4832639 : Blo 2009435 4832639 := bstep (se 1 (by rfl) ⟨3624479, by rfl⟩ : syracuseStep 4832639 = 7248959) B7248959
theorem B3221759 : Blo 2009435 3221759 := bstep (se 1 (by rfl) ⟨2416319, by rfl⟩ : syracuseStep 3221759 = 4832639) B4832639
theorem B2147839 : Blo 2009435 2147839 := bstep (se 1 (by rfl) ⟨1610879, by rfl⟩ : syracuseStep 2147839 = 3221759) B3221759
theorem B11455141 : Blo 2009435 11455141 := bstep (se 4 (by rfl) ⟨1073919, by rfl⟩ : syracuseStep 11455141 = 2147839) B2147839
theorem B15273521 : Blo 2009435 15273521 := bstep (se 2 (by rfl) ⟨5727570, by rfl⟩ : syracuseStep 15273521 = 11455141) B11455141
theorem B10182347 : Blo 2009435 10182347 := bstep (se 1 (by rfl) ⟨7636760, by rfl⟩ : syracuseStep 10182347 = 15273521) B15273521
theorem B6788231 : Blo 2009435 6788231 := bstep (se 1 (by rfl) ⟨5091173, by rfl⟩ : syracuseStep 6788231 = 10182347) B10182347
theorem B4525487 : Blo 2009435 4525487 := bstep (se 1 (by rfl) ⟨3394115, by rfl⟩ : syracuseStep 4525487 = 6788231) B6788231
theorem B3016991 : Blo 2009435 3016991 := bstep (se 1 (by rfl) ⟨2262743, by rfl⟩ : syracuseStep 3016991 = 4525487) B4525487
theorem B2011327 : Blo 2009435 2011327 := bstep (se 1 (by rfl) ⟨1508495, by rfl⟩ : syracuseStep 2011327 = 3016991) B3016991
theorem B3016997 : Blo 2009435 3016997 := bbase (se 4 (by rfl) ⟨282843, by rfl⟩ : syracuseStep 3016997 = 565687) (by norm_num)
theorem B2011331 : Blo 2009435 2011331 := bstep (se 1 (by rfl) ⟨1508498, by rfl⟩ : syracuseStep 2011331 = 3016997) B3016997
theorem B2545597 : Blo 2009435 2545597 := bbase (se 3 (by rfl) ⟨477299, by rfl⟩ : syracuseStep 2545597 = 954599) (by norm_num)
theorem B3394129 : Blo 2009435 3394129 := bstep (se 2 (by rfl) ⟨1272798, by rfl⟩ : syracuseStep 3394129 = 2545597) B2545597
theorem B4525505 : Blo 2009435 4525505 := bstep (se 2 (by rfl) ⟨1697064, by rfl⟩ : syracuseStep 4525505 = 3394129) B3394129
theorem B3017003 : Blo 2009435 3017003 := bstep (se 1 (by rfl) ⟨2262752, by rfl⟩ : syracuseStep 3017003 = 4525505) B4525505
theorem B2011335 : Blo 2009435 2011335 := bstep (se 1 (by rfl) ⟨1508501, by rfl⟩ : syracuseStep 2011335 = 3017003) B3017003
theorem B2262757 : Blo 2009435 2262757 := bbase (se 4 (by rfl) ⟨212133, by rfl⟩ : syracuseStep 2262757 = 424267) (by norm_num)
theorem B3017009 : Blo 2009435 3017009 := bstep (se 2 (by rfl) ⟨1131378, by rfl⟩ : syracuseStep 3017009 = 2262757) B2262757
theorem B2011339 : Blo 2009435 2011339 := bstep (se 1 (by rfl) ⟨1508504, by rfl⟩ : syracuseStep 2011339 = 3017009) B3017009
theorem B3624509 : Blo 2009435 3624509 := bbase (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) (by norm_num)
theorem B2416339 : Blo 2009435 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B3221785 : Blo 2009435 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B4295713 : Blo 2009435 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B5727617 : Blo 2009435 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B3818411 : Blo 2009435 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B2545607 : Blo 2009435 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B6788285 : Blo 2009435 6788285 := bstep (se 3 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 6788285 = 2545607) B2545607
theorem B4525523 : Blo 2009435 4525523 := bstep (se 1 (by rfl) ⟨3394142, by rfl⟩ : syracuseStep 4525523 = 6788285) B6788285
theorem B3017015 : Blo 2009435 3017015 := bstep (se 1 (by rfl) ⟨2262761, by rfl⟩ : syracuseStep 3017015 = 4525523) B4525523
theorem B2011343 : Blo 2009435 2011343 := bstep (se 1 (by rfl) ⟨1508507, by rfl⟩ : syracuseStep 2011343 = 3017015) B3017015
theorem B3017021 : Blo 2009435 3017021 := bbase (se 3 (by rfl) ⟨565691, by rfl⟩ : syracuseStep 3017021 = 1131383) (by norm_num)
theorem B2011347 : Blo 2009435 2011347 := bstep (se 1 (by rfl) ⟨1508510, by rfl⟩ : syracuseStep 2011347 = 3017021) B3017021
theorem B4525541 : Blo 2009435 4525541 := bbase (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) (by norm_num)
theorem B3017027 : Blo 2009435 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B2011351 : Blo 2009435 2011351 := bstep (se 1 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 2011351 = 3017027) B3017027
theorem B5091245 : Blo 2009435 5091245 := bbase (se 3 (by rfl) ⟨954608, by rfl⟩ : syracuseStep 5091245 = 1909217) (by norm_num)
theorem B3394163 : Blo 2009435 3394163 := bstep (se 1 (by rfl) ⟨2545622, by rfl⟩ : syracuseStep 3394163 = 5091245) B5091245
theorem B2262775 : Blo 2009435 2262775 := bstep (se 1 (by rfl) ⟨1697081, by rfl⟩ : syracuseStep 2262775 = 3394163) B3394163
theorem B3017033 : Blo 2009435 3017033 := bstep (se 2 (by rfl) ⟨1131387, by rfl⟩ : syracuseStep 3017033 = 2262775) B2262775
theorem B2011355 : Blo 2009435 2011355 := bstep (se 1 (by rfl) ⟨1508516, by rfl⟩ : syracuseStep 2011355 = 3017033) B3017033
theorem B6443621 : Blo 2009435 6443621 := bbase (se 4 (by rfl) ⟨604089, by rfl⟩ : syracuseStep 6443621 = 1208179) (by norm_num)
theorem B4295747 : Blo 2009435 4295747 := bstep (se 1 (by rfl) ⟨3221810, by rfl⟩ : syracuseStep 4295747 = 6443621) B6443621
theorem B2863831 : Blo 2009435 2863831 := bstep (se 1 (by rfl) ⟨2147873, by rfl⟩ : syracuseStep 2863831 = 4295747) B4295747
theorem B3818441 : Blo 2009435 3818441 := bstep (se 2 (by rfl) ⟨1431915, by rfl⟩ : syracuseStep 3818441 = 2863831) B2863831
theorem B10182509 : Blo 2009435 10182509 := bstep (se 3 (by rfl) ⟨1909220, by rfl⟩ : syracuseStep 10182509 = 3818441) B3818441
theorem B6788339 : Blo 2009435 6788339 := bstep (se 1 (by rfl) ⟨5091254, by rfl⟩ : syracuseStep 6788339 = 10182509) B10182509
theorem B4525559 : Blo 2009435 4525559 := bstep (se 1 (by rfl) ⟨3394169, by rfl⟩ : syracuseStep 4525559 = 6788339) B6788339
theorem B3017039 : Blo 2009435 3017039 := bstep (se 1 (by rfl) ⟨2262779, by rfl⟩ : syracuseStep 3017039 = 4525559) B4525559
theorem B2011359 : Blo 2009435 2011359 := bstep (se 1 (by rfl) ⟨1508519, by rfl⟩ : syracuseStep 2011359 = 3017039) B3017039
theorem B3017045 : Blo 2009435 3017045 := bbase (se 10 (by rfl) ⟨4419, by rfl⟩ : syracuseStep 3017045 = 8839) (by norm_num)
theorem B2011363 : Blo 2009435 2011363 := bstep (se 1 (by rfl) ⟨1508522, by rfl⟩ : syracuseStep 2011363 = 3017045) B3017045
theorem B5727685 : Blo 2009435 5727685 := bbase (se 4 (by rfl) ⟨536970, by rfl⟩ : syracuseStep 5727685 = 1073941) (by norm_num)
theorem B7636913 : Blo 2009435 7636913 := bstep (se 2 (by rfl) ⟨2863842, by rfl⟩ : syracuseStep 7636913 = 5727685) B5727685
theorem B5091275 : Blo 2009435 5091275 := bstep (se 1 (by rfl) ⟨3818456, by rfl⟩ : syracuseStep 5091275 = 7636913) B7636913
theorem B3394183 : Blo 2009435 3394183 := bstep (se 1 (by rfl) ⟨2545637, by rfl⟩ : syracuseStep 3394183 = 5091275) B5091275
theorem B4525577 : Blo 2009435 4525577 := bstep (se 2 (by rfl) ⟨1697091, by rfl⟩ : syracuseStep 4525577 = 3394183) B3394183
theorem B3017051 : Blo 2009435 3017051 := bstep (se 1 (by rfl) ⟨2262788, by rfl⟩ : syracuseStep 3017051 = 4525577) B4525577
theorem B2011367 : Blo 2009435 2011367 := bstep (se 1 (by rfl) ⟨1508525, by rfl⟩ : syracuseStep 2011367 = 3017051) B3017051
theorem B2262793 : Blo 2009435 2262793 := bbase (se 2 (by rfl) ⟨848547, by rfl⟩ : syracuseStep 2262793 = 1697095) (by norm_num)
theorem B3017057 : Blo 2009435 3017057 := bstep (se 2 (by rfl) ⟨1131396, by rfl⟩ : syracuseStep 3017057 = 2262793) B2262793
theorem B2011371 : Blo 2009435 2011371 := bstep (se 1 (by rfl) ⟨1508528, by rfl⟩ : syracuseStep 2011371 = 3017057) B3017057
theorem B14498261 : Blo 2009435 14498261 := bbase (se 7 (by rfl) ⟨169901, by rfl⟩ : syracuseStep 14498261 = 339803) (by norm_num)
theorem B9665507 : Blo 2009435 9665507 := bstep (se 1 (by rfl) ⟨7249130, by rfl⟩ : syracuseStep 9665507 = 14498261) B14498261
theorem B25774685 : Blo 2009435 25774685 := bstep (se 3 (by rfl) ⟨4832753, by rfl⟩ : syracuseStep 25774685 = 9665507) B9665507
theorem B17183123 : Blo 2009435 17183123 := bstep (se 1 (by rfl) ⟨12887342, by rfl⟩ : syracuseStep 17183123 = 25774685) B25774685
theorem B11455415 : Blo 2009435 11455415 := bstep (se 1 (by rfl) ⟨8591561, by rfl⟩ : syracuseStep 11455415 = 17183123) B17183123
theorem B7636943 : Blo 2009435 7636943 := bstep (se 1 (by rfl) ⟨5727707, by rfl⟩ : syracuseStep 7636943 = 11455415) B11455415
theorem B5091295 : Blo 2009435 5091295 := bstep (se 1 (by rfl) ⟨3818471, by rfl⟩ : syracuseStep 5091295 = 7636943) B7636943
theorem B6788393 : Blo 2009435 6788393 := bstep (se 2 (by rfl) ⟨2545647, by rfl⟩ : syracuseStep 6788393 = 5091295) B5091295
theorem B4525595 : Blo 2009435 4525595 := bstep (se 1 (by rfl) ⟨3394196, by rfl⟩ : syracuseStep 4525595 = 6788393) B6788393
theorem B3017063 : Blo 2009435 3017063 := bstep (se 1 (by rfl) ⟨2262797, by rfl⟩ : syracuseStep 3017063 = 4525595) B4525595
theorem B2011375 : Blo 2009435 2011375 := bstep (se 1 (by rfl) ⟨1508531, by rfl⟩ : syracuseStep 2011375 = 3017063) B3017063
theorem B3017069 : Blo 2009435 3017069 := bbase (se 3 (by rfl) ⟨565700, by rfl⟩ : syracuseStep 3017069 = 1131401) (by norm_num)
theorem B2011379 : Blo 2009435 2011379 := bstep (se 1 (by rfl) ⟨1508534, by rfl⟩ : syracuseStep 2011379 = 3017069) B3017069
theorem B4525613 : Blo 2009435 4525613 := bbase (se 3 (by rfl) ⟨848552, by rfl⟩ : syracuseStep 4525613 = 1697105) (by norm_num)
theorem B3017075 : Blo 2009435 3017075 := bstep (se 1 (by rfl) ⟨2262806, by rfl⟩ : syracuseStep 3017075 = 4525613) B4525613
theorem B2011383 : Blo 2009435 2011383 := bstep (se 1 (by rfl) ⟨1508537, by rfl⟩ : syracuseStep 2011383 = 3017075) B3017075
theorem B3265813 : Blo 2009435 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B4354417 : Blo 2009435 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B23223557 : Blo 2009435 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B61929485 : Blo 2009435 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B41286323 : Blo 2009435 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B27524215 : Blo 2009435 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B146795813 : Blo 2009435 146795813 := bstep (se 4 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 146795813 = 27524215) B27524215
theorem B97863875 : Blo 2009435 97863875 := bstep (se 1 (by rfl) ⟨73397906, by rfl⟩ : syracuseStep 97863875 = 146795813) B146795813
theorem B65242583 : Blo 2009435 65242583 := bstep (se 1 (by rfl) ⟨48931937, by rfl⟩ : syracuseStep 65242583 = 97863875) B97863875
theorem B43495055 : Blo 2009435 43495055 := bstep (se 1 (by rfl) ⟨32621291, by rfl⟩ : syracuseStep 43495055 = 65242583) B65242583
theorem B28996703 : Blo 2009435 28996703 := bstep (se 1 (by rfl) ⟨21747527, by rfl⟩ : syracuseStep 28996703 = 43495055) B43495055
theorem B19331135 : Blo 2009435 19331135 := bstep (se 1 (by rfl) ⟨14498351, by rfl⟩ : syracuseStep 19331135 = 28996703) B28996703
theorem B12887423 : Blo 2009435 12887423 := bstep (se 1 (by rfl) ⟨9665567, by rfl⟩ : syracuseStep 12887423 = 19331135) B19331135
theorem B8591615 : Blo 2009435 8591615 := bstep (se 1 (by rfl) ⟨6443711, by rfl⟩ : syracuseStep 8591615 = 12887423) B12887423
theorem B5727743 : Blo 2009435 5727743 := bstep (se 1 (by rfl) ⟨4295807, by rfl⟩ : syracuseStep 5727743 = 8591615) B8591615
theorem B3818495 : Blo 2009435 3818495 := bstep (se 1 (by rfl) ⟨2863871, by rfl⟩ : syracuseStep 3818495 = 5727743) B5727743
theorem B2545663 : Blo 2009435 2545663 := bstep (se 1 (by rfl) ⟨1909247, by rfl⟩ : syracuseStep 2545663 = 3818495) B3818495
theorem B3394217 : Blo 2009435 3394217 := bstep (se 2 (by rfl) ⟨1272831, by rfl⟩ : syracuseStep 3394217 = 2545663) B2545663
theorem B2262811 : Blo 2009435 2262811 := bstep (se 1 (by rfl) ⟨1697108, by rfl⟩ : syracuseStep 2262811 = 3394217) B3394217
theorem B3017081 : Blo 2009435 3017081 := bstep (se 2 (by rfl) ⟨1131405, by rfl⟩ : syracuseStep 3017081 = 2262811) B2262811
theorem B2011387 : Blo 2009435 2011387 := bstep (se 1 (by rfl) ⟨1508540, by rfl⟩ : syracuseStep 2011387 = 3017081) B3017081
theorem B3221861 : Blo 2009435 3221861 := bbase (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) (by norm_num)
theorem B34366517 : Blo 2009435 34366517 := bstep (se 5 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 34366517 = 3221861) B3221861
theorem B22911011 : Blo 2009435 22911011 := bstep (se 1 (by rfl) ⟨17183258, by rfl⟩ : syracuseStep 22911011 = 34366517) B34366517
theorem B15274007 : Blo 2009435 15274007 := bstep (se 1 (by rfl) ⟨11455505, by rfl⟩ : syracuseStep 15274007 = 22911011) B22911011
theorem B10182671 : Blo 2009435 10182671 := bstep (se 1 (by rfl) ⟨7637003, by rfl⟩ : syracuseStep 10182671 = 15274007) B15274007
theorem B6788447 : Blo 2009435 6788447 := bstep (se 1 (by rfl) ⟨5091335, by rfl⟩ : syracuseStep 6788447 = 10182671) B10182671
theorem B4525631 : Blo 2009435 4525631 := bstep (se 1 (by rfl) ⟨3394223, by rfl⟩ : syracuseStep 4525631 = 6788447) B6788447
theorem B3017087 : Blo 2009435 3017087 := bstep (se 1 (by rfl) ⟨2262815, by rfl⟩ : syracuseStep 3017087 = 4525631) B4525631
theorem B2011391 : Blo 2009435 2011391 := bstep (se 1 (by rfl) ⟨1508543, by rfl⟩ : syracuseStep 2011391 = 3017087) B3017087
theorem B3017093 : Blo 2009435 3017093 := bbase (se 4 (by rfl) ⟨282852, by rfl⟩ : syracuseStep 3017093 = 565705) (by norm_num)
theorem B2011395 : Blo 2009435 2011395 := bstep (se 1 (by rfl) ⟨1508546, by rfl⟩ : syracuseStep 2011395 = 3017093) B3017093
theorem B3394237 : Blo 2009435 3394237 := bbase (se 3 (by rfl) ⟨636419, by rfl⟩ : syracuseStep 3394237 = 1272839) (by norm_num)
theorem B4525649 : Blo 2009435 4525649 := bstep (se 2 (by rfl) ⟨1697118, by rfl⟩ : syracuseStep 4525649 = 3394237) B3394237
theorem B3017099 : Blo 2009435 3017099 := bstep (se 1 (by rfl) ⟨2262824, by rfl⟩ : syracuseStep 3017099 = 4525649) B4525649
theorem B2011399 : Blo 2009435 2011399 := bstep (se 1 (by rfl) ⟨1508549, by rfl⟩ : syracuseStep 2011399 = 3017099) B3017099
theorem B2262829 : Blo 2009435 2262829 := bbase (se 3 (by rfl) ⟨424280, by rfl⟩ : syracuseStep 2262829 = 848561) (by norm_num)
theorem B3017105 : Blo 2009435 3017105 := bstep (se 2 (by rfl) ⟨1131414, by rfl⟩ : syracuseStep 3017105 = 2262829) B2262829
theorem B2011403 : Blo 2009435 2011403 := bstep (se 1 (by rfl) ⟨1508552, by rfl⟩ : syracuseStep 2011403 = 3017105) B3017105
theorem B6788501 : Blo 2009435 6788501 := bbase (se 6 (by rfl) ⟨159105, by rfl⟩ : syracuseStep 6788501 = 318211) (by norm_num)
theorem B4525667 : Blo 2009435 4525667 := bstep (se 1 (by rfl) ⟨3394250, by rfl⟩ : syracuseStep 4525667 = 6788501) B6788501
theorem B3017111 : Blo 2009435 3017111 := bstep (se 1 (by rfl) ⟨2262833, by rfl⟩ : syracuseStep 3017111 = 4525667) B4525667
theorem B2011407 : Blo 2009435 2011407 := bstep (se 1 (by rfl) ⟨1508555, by rfl⟩ : syracuseStep 2011407 = 3017111) B3017111
theorem B3017117 : Blo 2009435 3017117 := bbase (se 3 (by rfl) ⟨565709, by rfl⟩ : syracuseStep 3017117 = 1131419) (by norm_num)
theorem B2011411 : Blo 2009435 2011411 := bstep (se 1 (by rfl) ⟨1508558, by rfl⟩ : syracuseStep 2011411 = 3017117) B3017117
theorem B4525685 : Blo 2009435 4525685 := bbase (se 5 (by rfl) ⟨212141, by rfl⟩ : syracuseStep 4525685 = 424283) (by norm_num)
theorem B3017123 : Blo 2009435 3017123 := bstep (se 1 (by rfl) ⟨2262842, by rfl⟩ : syracuseStep 3017123 = 4525685) B4525685
theorem B2011415 : Blo 2009435 2011415 := bstep (se 1 (by rfl) ⟨1508561, by rfl⟩ : syracuseStep 2011415 = 3017123) B3017123
theorem B6443813 : Blo 2009435 6443813 := bbase (se 4 (by rfl) ⟨604107, by rfl⟩ : syracuseStep 6443813 = 1208215) (by norm_num)
theorem B17183501 : Blo 2009435 17183501 := bstep (se 3 (by rfl) ⟨3221906, by rfl⟩ : syracuseStep 17183501 = 6443813) B6443813
theorem B11455667 : Blo 2009435 11455667 := bstep (se 1 (by rfl) ⟨8591750, by rfl⟩ : syracuseStep 11455667 = 17183501) B17183501
theorem B7637111 : Blo 2009435 7637111 := bstep (se 1 (by rfl) ⟨5727833, by rfl⟩ : syracuseStep 7637111 = 11455667) B11455667
theorem B5091407 : Blo 2009435 5091407 := bstep (se 1 (by rfl) ⟨3818555, by rfl⟩ : syracuseStep 5091407 = 7637111) B7637111
theorem B3394271 : Blo 2009435 3394271 := bstep (se 1 (by rfl) ⟨2545703, by rfl⟩ : syracuseStep 3394271 = 5091407) B5091407
theorem B2262847 : Blo 2009435 2262847 := bstep (se 1 (by rfl) ⟨1697135, by rfl⟩ : syracuseStep 2262847 = 3394271) B3394271
theorem B3017129 : Blo 2009435 3017129 := bstep (se 2 (by rfl) ⟨1131423, by rfl⟩ : syracuseStep 3017129 = 2262847) B2262847
theorem B2011419 : Blo 2009435 2011419 := bstep (se 1 (by rfl) ⟨1508564, by rfl⟩ : syracuseStep 2011419 = 3017129) B3017129
theorem B7637125 : Blo 2009435 7637125 := bbase (se 4 (by rfl) ⟨715980, by rfl⟩ : syracuseStep 7637125 = 1431961) (by norm_num)
theorem B10182833 : Blo 2009435 10182833 := bstep (se 2 (by rfl) ⟨3818562, by rfl⟩ : syracuseStep 10182833 = 7637125) B7637125
theorem B6788555 : Blo 2009435 6788555 := bstep (se 1 (by rfl) ⟨5091416, by rfl⟩ : syracuseStep 6788555 = 10182833) B10182833
theorem B4525703 : Blo 2009435 4525703 := bstep (se 1 (by rfl) ⟨3394277, by rfl⟩ : syracuseStep 4525703 = 6788555) B6788555
theorem B3017135 : Blo 2009435 3017135 := bstep (se 1 (by rfl) ⟨2262851, by rfl⟩ : syracuseStep 3017135 = 4525703) B4525703
theorem B2011423 : Blo 2009435 2011423 := bstep (se 1 (by rfl) ⟨1508567, by rfl⟩ : syracuseStep 2011423 = 3017135) B3017135
theorem B3017141 : Blo 2009435 3017141 := bbase (se 5 (by rfl) ⟨141428, by rfl⟩ : syracuseStep 3017141 = 282857) (by norm_num)
theorem B2011427 : Blo 2009435 2011427 := bstep (se 1 (by rfl) ⟨1508570, by rfl⟩ : syracuseStep 2011427 = 3017141) B3017141
theorem B5091437 : Blo 2009435 5091437 := bbase (se 3 (by rfl) ⟨954644, by rfl⟩ : syracuseStep 5091437 = 1909289) (by norm_num)
theorem B3394291 : Blo 2009435 3394291 := bstep (se 1 (by rfl) ⟨2545718, by rfl⟩ : syracuseStep 3394291 = 5091437) B5091437
theorem B4525721 : Blo 2009435 4525721 := bstep (se 2 (by rfl) ⟨1697145, by rfl⟩ : syracuseStep 4525721 = 3394291) B3394291
theorem B3017147 : Blo 2009435 3017147 := bstep (se 1 (by rfl) ⟨2262860, by rfl⟩ : syracuseStep 3017147 = 4525721) B4525721
theorem B2011431 : Blo 2009435 2011431 := bstep (se 1 (by rfl) ⟨1508573, by rfl⟩ : syracuseStep 2011431 = 3017147) B3017147
theorem B2262865 : Blo 2009435 2262865 := bbase (se 2 (by rfl) ⟨848574, by rfl⟩ : syracuseStep 2262865 = 1697149) (by norm_num)
theorem B3017153 : Blo 2009435 3017153 := bstep (se 2 (by rfl) ⟨1131432, by rfl⟩ : syracuseStep 3017153 = 2262865) B2262865
theorem B2011435 : Blo 2009435 2011435 := bstep (se 1 (by rfl) ⟨1508576, by rfl⟩ : syracuseStep 2011435 = 3017153) B3017153
theorem C0 (j : ℕ) (h1 : 502358 ≤ j) (h2 : j ≤ 502858) : Blo 2009435 (4 * j + 3) := by
  interval_cases j
  · exact B2009435
  · exact B2009439
  · exact B2009443
  · exact B2009447
  · exact B2009451
  · exact B2009455
  · exact B2009459
  · exact B2009463
  · exact B2009467
  · exact B2009471
  · exact B2009475
  · exact B2009479
  · exact B2009483
  · exact B2009487
  · exact B2009491
  · exact B2009495
  · exact B2009499
  · exact B2009503
  · exact B2009507
  · exact B2009511
  · exact B2009515
  · exact B2009519
  · exact B2009523
  · exact B2009527
  · exact B2009531
  · exact B2009535
  · exact B2009539
  · exact B2009543
  · exact B2009547
  · exact B2009551
  · exact B2009555
  · exact B2009559
  · exact B2009563
  · exact B2009567
  · exact B2009571
  · exact B2009575
  · exact B2009579
  · exact B2009583
  · exact B2009587
  · exact B2009591
  · exact B2009595
  · exact B2009599
  · exact B2009603
  · exact B2009607
  · exact B2009611
  · exact B2009615
  · exact B2009619
  · exact B2009623
  · exact B2009627
  · exact B2009631
  · exact B2009635
  · exact B2009639
  · exact B2009643
  · exact B2009647
  · exact B2009651
  · exact B2009655
  · exact B2009659
  · exact B2009663
  · exact B2009667
  · exact B2009671
  · exact B2009675
  · exact B2009679
  · exact B2009683
  · exact B2009687
  · exact B2009691
  · exact B2009695
  · exact B2009699
  · exact B2009703
  · exact B2009707
  · exact B2009711
  · exact B2009715
  · exact B2009719
  · exact B2009723
  · exact B2009727
  · exact B2009731
  · exact B2009735
  · exact B2009739
  · exact B2009743
  · exact B2009747
  · exact B2009751
  · exact B2009755
  · exact B2009759
  · exact B2009763
  · exact B2009767
  · exact B2009771
  · exact B2009775
  · exact B2009779
  · exact B2009783
  · exact B2009787
  · exact B2009791
  · exact B2009795
  · exact B2009799
  · exact B2009803
  · exact B2009807
  · exact B2009811
  · exact B2009815
  · exact B2009819
  · exact B2009823
  · exact B2009827
  · exact B2009831
  · exact B2009835
  · exact B2009839
  · exact B2009843
  · exact B2009847
  · exact B2009851
  · exact B2009855
  · exact B2009859
  · exact B2009863
  · exact B2009867
  · exact B2009871
  · exact B2009875
  · exact B2009879
  · exact B2009883
  · exact B2009887
  · exact B2009891
  · exact B2009895
  · exact B2009899
  · exact B2009903
  · exact B2009907
  · exact B2009911
  · exact B2009915
  · exact B2009919
  · exact B2009923
  · exact B2009927
  · exact B2009931
  · exact B2009935
  · exact B2009939
  · exact B2009943
  · exact B2009947
  · exact B2009951
  · exact B2009955
  · exact B2009959
  · exact B2009963
  · exact B2009967
  · exact B2009971
  · exact B2009975
  · exact B2009979
  · exact B2009983
  · exact B2009987
  · exact B2009991
  · exact B2009995
  · exact B2009999
  · exact B2010003
  · exact B2010007
  · exact B2010011
  · exact B2010015
  · exact B2010019
  · exact B2010023
  · exact B2010027
  · exact B2010031
  · exact B2010035
  · exact B2010039
  · exact B2010043
  · exact B2010047
  · exact B2010051
  · exact B2010055
  · exact B2010059
  · exact B2010063
  · exact B2010067
  · exact B2010071
  · exact B2010075
  · exact B2010079
  · exact B2010083
  · exact B2010087
  · exact B2010091
  · exact B2010095
  · exact B2010099
  · exact B2010103
  · exact B2010107
  · exact B2010111
  · exact B2010115
  · exact B2010119
  · exact B2010123
  · exact B2010127
  · exact B2010131
  · exact B2010135
  · exact B2010139
  · exact B2010143
  · exact B2010147
  · exact B2010151
  · exact B2010155
  · exact B2010159
  · exact B2010163
  · exact B2010167
  · exact B2010171
  · exact B2010175
  · exact B2010179
  · exact B2010183
  · exact B2010187
  · exact B2010191
  · exact B2010195
  · exact B2010199
  · exact B2010203
  · exact B2010207
  · exact B2010211
  · exact B2010215
  · exact B2010219
  · exact B2010223
  · exact B2010227
  · exact B2010231
  · exact B2010235
  · exact B2010239
  · exact B2010243
  · exact B2010247
  · exact B2010251
  · exact B2010255
  · exact B2010259
  · exact B2010263
  · exact B2010267
  · exact B2010271
  · exact B2010275
  · exact B2010279
  · exact B2010283
  · exact B2010287
  · exact B2010291
  · exact B2010295
  · exact B2010299
  · exact B2010303
  · exact B2010307
  · exact B2010311
  · exact B2010315
  · exact B2010319
  · exact B2010323
  · exact B2010327
  · exact B2010331
  · exact B2010335
  · exact B2010339
  · exact B2010343
  · exact B2010347
  · exact B2010351
  · exact B2010355
  · exact B2010359
  · exact B2010363
  · exact B2010367
  · exact B2010371
  · exact B2010375
  · exact B2010379
  · exact B2010383
  · exact B2010387
  · exact B2010391
  · exact B2010395
  · exact B2010399
  · exact B2010403
  · exact B2010407
  · exact B2010411
  · exact B2010415
  · exact B2010419
  · exact B2010423
  · exact B2010427
  · exact B2010431
  · exact B2010435
  · exact B2010439
  · exact B2010443
  · exact B2010447
  · exact B2010451
  · exact B2010455
  · exact B2010459
  · exact B2010463
  · exact B2010467
  · exact B2010471
  · exact B2010475
  · exact B2010479
  · exact B2010483
  · exact B2010487
  · exact B2010491
  · exact B2010495
  · exact B2010499
  · exact B2010503
  · exact B2010507
  · exact B2010511
  · exact B2010515
  · exact B2010519
  · exact B2010523
  · exact B2010527
  · exact B2010531
  · exact B2010535
  · exact B2010539
  · exact B2010543
  · exact B2010547
  · exact B2010551
  · exact B2010555
  · exact B2010559
  · exact B2010563
  · exact B2010567
  · exact B2010571
  · exact B2010575
  · exact B2010579
  · exact B2010583
  · exact B2010587
  · exact B2010591
  · exact B2010595
  · exact B2010599
  · exact B2010603
  · exact B2010607
  · exact B2010611
  · exact B2010615
  · exact B2010619
  · exact B2010623
  · exact B2010627
  · exact B2010631
  · exact B2010635
  · exact B2010639
  · exact B2010643
  · exact B2010647
  · exact B2010651
  · exact B2010655
  · exact B2010659
  · exact B2010663
  · exact B2010667
  · exact B2010671
  · exact B2010675
  · exact B2010679
  · exact B2010683
  · exact B2010687
  · exact B2010691
  · exact B2010695
  · exact B2010699
  · exact B2010703
  · exact B2010707
  · exact B2010711
  · exact B2010715
  · exact B2010719
  · exact B2010723
  · exact B2010727
  · exact B2010731
  · exact B2010735
  · exact B2010739
  · exact B2010743
  · exact B2010747
  · exact B2010751
  · exact B2010755
  · exact B2010759
  · exact B2010763
  · exact B2010767
  · exact B2010771
  · exact B2010775
  · exact B2010779
  · exact B2010783
  · exact B2010787
  · exact B2010791
  · exact B2010795
  · exact B2010799
  · exact B2010803
  · exact B2010807
  · exact B2010811
  · exact B2010815
  · exact B2010819
  · exact B2010823
  · exact B2010827
  · exact B2010831
  · exact B2010835
  · exact B2010839
  · exact B2010843
  · exact B2010847
  · exact B2010851
  · exact B2010855
  · exact B2010859
  · exact B2010863
  · exact B2010867
  · exact B2010871
  · exact B2010875
  · exact B2010879
  · exact B2010883
  · exact B2010887
  · exact B2010891
  · exact B2010895
  · exact B2010899
  · exact B2010903
  · exact B2010907
  · exact B2010911
  · exact B2010915
  · exact B2010919
  · exact B2010923
  · exact B2010927
  · exact B2010931
  · exact B2010935
  · exact B2010939
  · exact B2010943
  · exact B2010947
  · exact B2010951
  · exact B2010955
  · exact B2010959
  · exact B2010963
  · exact B2010967
  · exact B2010971
  · exact B2010975
  · exact B2010979
  · exact B2010983
  · exact B2010987
  · exact B2010991
  · exact B2010995
  · exact B2010999
  · exact B2011003
  · exact B2011007
  · exact B2011011
  · exact B2011015
  · exact B2011019
  · exact B2011023
  · exact B2011027
  · exact B2011031
  · exact B2011035
  · exact B2011039
  · exact B2011043
  · exact B2011047
  · exact B2011051
  · exact B2011055
  · exact B2011059
  · exact B2011063
  · exact B2011067
  · exact B2011071
  · exact B2011075
  · exact B2011079
  · exact B2011083
  · exact B2011087
  · exact B2011091
  · exact B2011095
  · exact B2011099
  · exact B2011103
  · exact B2011107
  · exact B2011111
  · exact B2011115
  · exact B2011119
  · exact B2011123
  · exact B2011127
  · exact B2011131
  · exact B2011135
  · exact B2011139
  · exact B2011143
  · exact B2011147
  · exact B2011151
  · exact B2011155
  · exact B2011159
  · exact B2011163
  · exact B2011167
  · exact B2011171
  · exact B2011175
  · exact B2011179
  · exact B2011183
  · exact B2011187
  · exact B2011191
  · exact B2011195
  · exact B2011199
  · exact B2011203
  · exact B2011207
  · exact B2011211
  · exact B2011215
  · exact B2011219
  · exact B2011223
  · exact B2011227
  · exact B2011231
  · exact B2011235
  · exact B2011239
  · exact B2011243
  · exact B2011247
  · exact B2011251
  · exact B2011255
  · exact B2011259
  · exact B2011263
  · exact B2011267
  · exact B2011271
  · exact B2011275
  · exact B2011279
  · exact B2011283
  · exact B2011287
  · exact B2011291
  · exact B2011295
  · exact B2011299
  · exact B2011303
  · exact B2011307
  · exact B2011311
  · exact B2011315
  · exact B2011319
  · exact B2011323
  · exact B2011327
  · exact B2011331
  · exact B2011335
  · exact B2011339
  · exact B2011343
  · exact B2011347
  · exact B2011351
  · exact B2011355
  · exact B2011359
  · exact B2011363
  · exact B2011367
  · exact B2011371
  · exact B2011375
  · exact B2011379
  · exact B2011383
  · exact B2011387
  · exact B2011391
  · exact B2011395
  · exact B2011399
  · exact B2011403
  · exact B2011407
  · exact B2011411
  · exact B2011415
  · exact B2011419
  · exact B2011423
  · exact B2011427
  · exact B2011431
  · exact B2011435
theorem solution (m : ℕ) (hlo : 2009435 ≤ m) (hhi : m ≤ 2011435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 502358 ≤ j := by omega
    have hj2 : j ≤ 502858 := by omega
    have hb : Blo 2009435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
