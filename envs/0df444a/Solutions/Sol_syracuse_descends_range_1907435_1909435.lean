-- Prove2me | solution 1 for syracuse_descends_range_1907435_1909435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:57.327792+00:00
-- url     : https://prove2.me/submissions/1b75028b-9913-4548-8679-130f95ec3534

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

theorem B2145865 : Blo 1907435 2145865 := bbase (se 2 (by rfl) ⟨804699, by rfl⟩ : syracuseStep 2145865 = 1609399) (by norm_num)
theorem B2861153 : Blo 1907435 2861153 := bstep (se 2 (by rfl) ⟨1072932, by rfl⟩ : syracuseStep 2861153 = 2145865) B2145865
theorem B1907435 : Blo 1907435 1907435 := bstep (se 1 (by rfl) ⟨1430576, by rfl⟩ : syracuseStep 1907435 = 2861153) B2861153
theorem B13749077 : Blo 1907435 13749077 := bbase (se 9 (by rfl) ⟨40280, by rfl⟩ : syracuseStep 13749077 = 80561) (by norm_num)
theorem B9166051 : Blo 1907435 9166051 := bstep (se 1 (by rfl) ⟨6874538, by rfl⟩ : syracuseStep 9166051 = 13749077) B13749077
theorem B12221401 : Blo 1907435 12221401 := bstep (se 2 (by rfl) ⟨4583025, by rfl⟩ : syracuseStep 12221401 = 9166051) B9166051
theorem B16295201 : Blo 1907435 16295201 := bstep (se 2 (by rfl) ⟨6110700, by rfl⟩ : syracuseStep 16295201 = 12221401) B12221401
theorem B10863467 : Blo 1907435 10863467 := bstep (se 1 (by rfl) ⟨8147600, by rfl⟩ : syracuseStep 10863467 = 16295201) B16295201
theorem B7242311 : Blo 1907435 7242311 := bstep (se 1 (by rfl) ⟨5431733, by rfl⟩ : syracuseStep 7242311 = 10863467) B10863467
theorem B4828207 : Blo 1907435 4828207 := bstep (se 1 (by rfl) ⟨3621155, by rfl⟩ : syracuseStep 4828207 = 7242311) B7242311
theorem B6437609 : Blo 1907435 6437609 := bstep (se 2 (by rfl) ⟨2414103, by rfl⟩ : syracuseStep 6437609 = 4828207) B4828207
theorem B4291739 : Blo 1907435 4291739 := bstep (se 1 (by rfl) ⟨3218804, by rfl⟩ : syracuseStep 4291739 = 6437609) B6437609
theorem B2861159 : Blo 1907435 2861159 := bstep (se 1 (by rfl) ⟨2145869, by rfl⟩ : syracuseStep 2861159 = 4291739) B4291739
theorem B1907439 : Blo 1907435 1907439 := bstep (se 1 (by rfl) ⟨1430579, by rfl⟩ : syracuseStep 1907439 = 2861159) B2861159
theorem B2861165 : Blo 1907435 2861165 := bbase (se 3 (by rfl) ⟨536468, by rfl⟩ : syracuseStep 2861165 = 1072937) (by norm_num)
theorem B1907443 : Blo 1907435 1907443 := bstep (se 1 (by rfl) ⟨1430582, by rfl⟩ : syracuseStep 1907443 = 2861165) B2861165
theorem B4291757 : Blo 1907435 4291757 := bbase (se 3 (by rfl) ⟨804704, by rfl⟩ : syracuseStep 4291757 = 1609409) (by norm_num)
theorem B2861171 : Blo 1907435 2861171 := bstep (se 1 (by rfl) ⟨2145878, by rfl⟩ : syracuseStep 2861171 = 4291757) B4291757
theorem B1907447 : Blo 1907435 1907447 := bstep (se 1 (by rfl) ⟨1430585, by rfl⟩ : syracuseStep 1907447 = 2861171) B2861171
theorem B6110741 : Blo 1907435 6110741 := bbase (se 6 (by rfl) ⟨143220, by rfl⟩ : syracuseStep 6110741 = 286441) (by norm_num)
theorem B4073827 : Blo 1907435 4073827 := bstep (se 1 (by rfl) ⟨3055370, by rfl⟩ : syracuseStep 4073827 = 6110741) B6110741
theorem B5431769 : Blo 1907435 5431769 := bstep (se 2 (by rfl) ⟨2036913, by rfl⟩ : syracuseStep 5431769 = 4073827) B4073827
theorem B3621179 : Blo 1907435 3621179 := bstep (se 1 (by rfl) ⟨2715884, by rfl⟩ : syracuseStep 3621179 = 5431769) B5431769
theorem B2414119 : Blo 1907435 2414119 := bstep (se 1 (by rfl) ⟨1810589, by rfl⟩ : syracuseStep 2414119 = 3621179) B3621179
theorem B3218825 : Blo 1907435 3218825 := bstep (se 2 (by rfl) ⟨1207059, by rfl⟩ : syracuseStep 3218825 = 2414119) B2414119
theorem B2145883 : Blo 1907435 2145883 := bstep (se 1 (by rfl) ⟨1609412, by rfl⟩ : syracuseStep 2145883 = 3218825) B3218825
theorem B2861177 : Blo 1907435 2861177 := bstep (se 2 (by rfl) ⟨1072941, by rfl⟩ : syracuseStep 2861177 = 2145883) B2145883
theorem B1907451 : Blo 1907435 1907451 := bstep (se 1 (by rfl) ⟨1430588, by rfl⟩ : syracuseStep 1907451 = 2861177) B2861177
theorem B15892789 : Blo 1907435 15892789 := bbase (se 5 (by rfl) ⟨744974, by rfl⟩ : syracuseStep 15892789 = 1489949) (by norm_num)
theorem B21190385 : Blo 1907435 21190385 := bstep (se 2 (by rfl) ⟨7946394, by rfl⟩ : syracuseStep 21190385 = 15892789) B15892789
theorem B14126923 : Blo 1907435 14126923 := bstep (se 1 (by rfl) ⟨10595192, by rfl⟩ : syracuseStep 14126923 = 21190385) B21190385
theorem B18835897 : Blo 1907435 18835897 := bstep (se 2 (by rfl) ⟨7063461, by rfl⟩ : syracuseStep 18835897 = 14126923) B14126923
theorem B25114529 : Blo 1907435 25114529 := bstep (se 2 (by rfl) ⟨9417948, by rfl⟩ : syracuseStep 25114529 = 18835897) B18835897
theorem B16743019 : Blo 1907435 16743019 := bstep (se 1 (by rfl) ⟨12557264, by rfl⟩ : syracuseStep 16743019 = 25114529) B25114529
theorem B22324025 : Blo 1907435 22324025 := bstep (se 2 (by rfl) ⟨8371509, by rfl⟩ : syracuseStep 22324025 = 16743019) B16743019
theorem B59530733 : Blo 1907435 59530733 := bstep (se 3 (by rfl) ⟨11162012, by rfl⟩ : syracuseStep 59530733 = 22324025) B22324025
theorem B39687155 : Blo 1907435 39687155 := bstep (se 1 (by rfl) ⟨29765366, by rfl⟩ : syracuseStep 39687155 = 59530733) B59530733
theorem B26458103 : Blo 1907435 26458103 := bstep (se 1 (by rfl) ⟨19843577, by rfl⟩ : syracuseStep 26458103 = 39687155) B39687155
theorem B17638735 : Blo 1907435 17638735 := bstep (se 1 (by rfl) ⟨13229051, by rfl⟩ : syracuseStep 17638735 = 26458103) B26458103
theorem B23518313 : Blo 1907435 23518313 := bstep (se 2 (by rfl) ⟨8819367, by rfl⟩ : syracuseStep 23518313 = 17638735) B17638735
theorem B15678875 : Blo 1907435 15678875 := bstep (se 1 (by rfl) ⟨11759156, by rfl⟩ : syracuseStep 15678875 = 23518313) B23518313
theorem B10452583 : Blo 1907435 10452583 := bstep (se 1 (by rfl) ⟨7839437, by rfl⟩ : syracuseStep 10452583 = 15678875) B15678875
theorem B55747109 : Blo 1907435 55747109 := bstep (se 4 (by rfl) ⟨5226291, by rfl⟩ : syracuseStep 55747109 = 10452583) B10452583
theorem B37164739 : Blo 1907435 37164739 := bstep (se 1 (by rfl) ⟨27873554, by rfl⟩ : syracuseStep 37164739 = 55747109) B55747109
theorem B49552985 : Blo 1907435 49552985 := bstep (se 2 (by rfl) ⟨18582369, by rfl⟩ : syracuseStep 49552985 = 37164739) B37164739
theorem B33035323 : Blo 1907435 33035323 := bstep (se 1 (by rfl) ⟨24776492, by rfl⟩ : syracuseStep 33035323 = 49552985) B49552985
theorem B44047097 : Blo 1907435 44047097 := bstep (se 2 (by rfl) ⟨16517661, by rfl⟩ : syracuseStep 44047097 = 33035323) B33035323
theorem B29364731 : Blo 1907435 29364731 := bstep (se 1 (by rfl) ⟨22023548, by rfl⟩ : syracuseStep 29364731 = 44047097) B44047097
theorem B19576487 : Blo 1907435 19576487 := bstep (se 1 (by rfl) ⟨14682365, by rfl⟩ : syracuseStep 19576487 = 29364731) B29364731
theorem B13050991 : Blo 1907435 13050991 := bstep (se 1 (by rfl) ⟨9788243, by rfl⟩ : syracuseStep 13050991 = 19576487) B19576487
theorem B17401321 : Blo 1907435 17401321 := bstep (se 2 (by rfl) ⟨6525495, by rfl⟩ : syracuseStep 17401321 = 13050991) B13050991
theorem B23201761 : Blo 1907435 23201761 := bstep (se 2 (by rfl) ⟨8700660, by rfl⟩ : syracuseStep 23201761 = 17401321) B17401321
theorem B30935681 : Blo 1907435 30935681 := bstep (se 2 (by rfl) ⟨11600880, by rfl⟩ : syracuseStep 30935681 = 23201761) B23201761
theorem B20623787 : Blo 1907435 20623787 := bstep (se 1 (by rfl) ⟨15467840, by rfl⟩ : syracuseStep 20623787 = 30935681) B30935681
theorem B13749191 : Blo 1907435 13749191 := bstep (se 1 (by rfl) ⟨10311893, by rfl⟩ : syracuseStep 13749191 = 20623787) B20623787
theorem B9166127 : Blo 1907435 9166127 := bstep (se 1 (by rfl) ⟨6874595, by rfl⟩ : syracuseStep 9166127 = 13749191) B13749191
theorem B24443005 : Blo 1907435 24443005 := bstep (se 3 (by rfl) ⟨4583063, by rfl⟩ : syracuseStep 24443005 = 9166127) B9166127
theorem B32590673 : Blo 1907435 32590673 := bstep (se 2 (by rfl) ⟨12221502, by rfl⟩ : syracuseStep 32590673 = 24443005) B24443005
theorem B21727115 : Blo 1907435 21727115 := bstep (se 1 (by rfl) ⟨16295336, by rfl⟩ : syracuseStep 21727115 = 32590673) B32590673
theorem B14484743 : Blo 1907435 14484743 := bstep (se 1 (by rfl) ⟨10863557, by rfl⟩ : syracuseStep 14484743 = 21727115) B21727115
theorem B9656495 : Blo 1907435 9656495 := bstep (se 1 (by rfl) ⟨7242371, by rfl⟩ : syracuseStep 9656495 = 14484743) B14484743
theorem B6437663 : Blo 1907435 6437663 := bstep (se 1 (by rfl) ⟨4828247, by rfl⟩ : syracuseStep 6437663 = 9656495) B9656495
theorem B4291775 : Blo 1907435 4291775 := bstep (se 1 (by rfl) ⟨3218831, by rfl⟩ : syracuseStep 4291775 = 6437663) B6437663
theorem B2861183 : Blo 1907435 2861183 := bstep (se 1 (by rfl) ⟨2145887, by rfl⟩ : syracuseStep 2861183 = 4291775) B4291775
theorem B1907455 : Blo 1907435 1907455 := bstep (se 1 (by rfl) ⟨1430591, by rfl⟩ : syracuseStep 1907455 = 2861183) B2861183
theorem B2861189 : Blo 1907435 2861189 := bbase (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) (by norm_num)
theorem B1907459 : Blo 1907435 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B3218845 : Blo 1907435 3218845 := bbase (se 3 (by rfl) ⟨603533, by rfl⟩ : syracuseStep 3218845 = 1207067) (by norm_num)
theorem B4291793 : Blo 1907435 4291793 := bstep (se 2 (by rfl) ⟨1609422, by rfl⟩ : syracuseStep 4291793 = 3218845) B3218845
theorem B2861195 : Blo 1907435 2861195 := bstep (se 1 (by rfl) ⟨2145896, by rfl⟩ : syracuseStep 2861195 = 4291793) B4291793
theorem B1907463 : Blo 1907435 1907463 := bstep (se 1 (by rfl) ⟨1430597, by rfl⟩ : syracuseStep 1907463 = 2861195) B2861195
theorem B2145901 : Blo 1907435 2145901 := bbase (se 3 (by rfl) ⟨402356, by rfl⟩ : syracuseStep 2145901 = 804713) (by norm_num)
theorem B2861201 : Blo 1907435 2861201 := bstep (se 2 (by rfl) ⟨1072950, by rfl⟩ : syracuseStep 2861201 = 2145901) B2145901
theorem B1907467 : Blo 1907435 1907467 := bstep (se 1 (by rfl) ⟨1430600, by rfl⟩ : syracuseStep 1907467 = 2861201) B2861201
theorem B6437717 : Blo 1907435 6437717 := bbase (se 9 (by rfl) ⟨18860, by rfl⟩ : syracuseStep 6437717 = 37721) (by norm_num)
theorem B4291811 : Blo 1907435 4291811 := bstep (se 1 (by rfl) ⟨3218858, by rfl⟩ : syracuseStep 4291811 = 6437717) B6437717
theorem B2861207 : Blo 1907435 2861207 := bstep (se 1 (by rfl) ⟨2145905, by rfl⟩ : syracuseStep 2861207 = 4291811) B4291811
theorem B1907471 : Blo 1907435 1907471 := bstep (se 1 (by rfl) ⟨1430603, by rfl⟩ : syracuseStep 1907471 = 2861207) B2861207
theorem B2861213 : Blo 1907435 2861213 := bbase (se 3 (by rfl) ⟨536477, by rfl⟩ : syracuseStep 2861213 = 1072955) (by norm_num)
theorem B1907475 : Blo 1907435 1907475 := bstep (se 1 (by rfl) ⟨1430606, by rfl⟩ : syracuseStep 1907475 = 2861213) B2861213
theorem B4291829 : Blo 1907435 4291829 := bbase (se 5 (by rfl) ⟨201179, by rfl⟩ : syracuseStep 4291829 = 402359) (by norm_num)
theorem B2861219 : Blo 1907435 2861219 := bstep (se 1 (by rfl) ⟨2145914, by rfl⟩ : syracuseStep 2861219 = 4291829) B4291829
theorem B1907479 : Blo 1907435 1907479 := bstep (se 1 (by rfl) ⟨1430609, by rfl⟩ : syracuseStep 1907479 = 2861219) B2861219
theorem B2480485 : Blo 1907435 2480485 := bbase (se 4 (by rfl) ⟨232545, by rfl⟩ : syracuseStep 2480485 = 465091) (by norm_num)
theorem B3307313 : Blo 1907435 3307313 := bstep (se 2 (by rfl) ⟨1240242, by rfl⟩ : syracuseStep 3307313 = 2480485) B2480485
theorem B2204875 : Blo 1907435 2204875 := bstep (se 1 (by rfl) ⟨1653656, by rfl⟩ : syracuseStep 2204875 = 3307313) B3307313
theorem B2939833 : Blo 1907435 2939833 := bstep (se 2 (by rfl) ⟨1102437, by rfl⟩ : syracuseStep 2939833 = 2204875) B2204875
theorem B15679109 : Blo 1907435 15679109 := bstep (se 4 (by rfl) ⟨1469916, by rfl⟩ : syracuseStep 15679109 = 2939833) B2939833
theorem B10452739 : Blo 1907435 10452739 := bstep (se 1 (by rfl) ⟨7839554, by rfl⟩ : syracuseStep 10452739 = 15679109) B15679109
theorem B13936985 : Blo 1907435 13936985 := bstep (se 2 (by rfl) ⟨5226369, by rfl⟩ : syracuseStep 13936985 = 10452739) B10452739
theorem B9291323 : Blo 1907435 9291323 := bstep (se 1 (by rfl) ⟨6968492, by rfl⟩ : syracuseStep 9291323 = 13936985) B13936985
theorem B6194215 : Blo 1907435 6194215 := bstep (se 1 (by rfl) ⟨4645661, by rfl⟩ : syracuseStep 6194215 = 9291323) B9291323
theorem B33035813 : Blo 1907435 33035813 := bstep (se 4 (by rfl) ⟨3097107, by rfl⟩ : syracuseStep 33035813 = 6194215) B6194215
theorem B22023875 : Blo 1907435 22023875 := bstep (se 1 (by rfl) ⟨16517906, by rfl⟩ : syracuseStep 22023875 = 33035813) B33035813
theorem B14682583 : Blo 1907435 14682583 := bstep (se 1 (by rfl) ⟨11011937, by rfl⟩ : syracuseStep 14682583 = 22023875) B22023875
theorem B19576777 : Blo 1907435 19576777 := bstep (se 2 (by rfl) ⟨7341291, by rfl⟩ : syracuseStep 19576777 = 14682583) B14682583
theorem B26102369 : Blo 1907435 26102369 := bstep (se 2 (by rfl) ⟨9788388, by rfl⟩ : syracuseStep 26102369 = 19576777) B19576777
theorem B69606317 : Blo 1907435 69606317 := bstep (se 3 (by rfl) ⟨13051184, by rfl⟩ : syracuseStep 69606317 = 26102369) B26102369
theorem B46404211 : Blo 1907435 46404211 := bstep (se 1 (by rfl) ⟨34803158, by rfl⟩ : syracuseStep 46404211 = 69606317) B69606317
theorem B61872281 : Blo 1907435 61872281 := bstep (se 2 (by rfl) ⟨23202105, by rfl⟩ : syracuseStep 61872281 = 46404211) B46404211
theorem B41248187 : Blo 1907435 41248187 := bstep (se 1 (by rfl) ⟨30936140, by rfl⟩ : syracuseStep 41248187 = 61872281) B61872281
theorem B27498791 : Blo 1907435 27498791 := bstep (se 1 (by rfl) ⟨20624093, by rfl⟩ : syracuseStep 27498791 = 41248187) B41248187
theorem B18332527 : Blo 1907435 18332527 := bstep (se 1 (by rfl) ⟨13749395, by rfl⟩ : syracuseStep 18332527 = 27498791) B27498791
theorem B24443369 : Blo 1907435 24443369 := bstep (se 2 (by rfl) ⟨9166263, by rfl⟩ : syracuseStep 24443369 = 18332527) B18332527
theorem B16295579 : Blo 1907435 16295579 := bstep (se 1 (by rfl) ⟨12221684, by rfl⟩ : syracuseStep 16295579 = 24443369) B24443369
theorem B10863719 : Blo 1907435 10863719 := bstep (se 1 (by rfl) ⟨8147789, by rfl⟩ : syracuseStep 10863719 = 16295579) B16295579
theorem B7242479 : Blo 1907435 7242479 := bstep (se 1 (by rfl) ⟨5431859, by rfl⟩ : syracuseStep 7242479 = 10863719) B10863719
theorem B4828319 : Blo 1907435 4828319 := bstep (se 1 (by rfl) ⟨3621239, by rfl⟩ : syracuseStep 4828319 = 7242479) B7242479
theorem B3218879 : Blo 1907435 3218879 := bstep (se 1 (by rfl) ⟨2414159, by rfl⟩ : syracuseStep 3218879 = 4828319) B4828319
theorem B2145919 : Blo 1907435 2145919 := bstep (se 1 (by rfl) ⟨1609439, by rfl⟩ : syracuseStep 2145919 = 3218879) B3218879
theorem B2861225 : Blo 1907435 2861225 := bstep (se 2 (by rfl) ⟨1072959, by rfl⟩ : syracuseStep 2861225 = 2145919) B2145919
theorem B1907483 : Blo 1907435 1907483 := bstep (se 1 (by rfl) ⟨1430612, by rfl⟩ : syracuseStep 1907483 = 2861225) B2861225
theorem B1933513 : Blo 1907435 1933513 := bbase (se 2 (by rfl) ⟨725067, by rfl⟩ : syracuseStep 1933513 = 1450135) (by norm_num)
theorem B10312069 : Blo 1907435 10312069 := bstep (se 4 (by rfl) ⟨966756, by rfl⟩ : syracuseStep 10312069 = 1933513) B1933513
theorem B13749425 : Blo 1907435 13749425 := bstep (se 2 (by rfl) ⟨5156034, by rfl⟩ : syracuseStep 13749425 = 10312069) B10312069
theorem B9166283 : Blo 1907435 9166283 := bstep (se 1 (by rfl) ⟨6874712, by rfl⟩ : syracuseStep 9166283 = 13749425) B13749425
theorem B6110855 : Blo 1907435 6110855 := bstep (se 1 (by rfl) ⟨4583141, by rfl⟩ : syracuseStep 6110855 = 9166283) B9166283
theorem B4073903 : Blo 1907435 4073903 := bstep (se 1 (by rfl) ⟨3055427, by rfl⟩ : syracuseStep 4073903 = 6110855) B6110855
theorem B2715935 : Blo 1907435 2715935 := bstep (se 1 (by rfl) ⟨2036951, by rfl⟩ : syracuseStep 2715935 = 4073903) B4073903
theorem B7242493 : Blo 1907435 7242493 := bstep (se 3 (by rfl) ⟨1357967, by rfl⟩ : syracuseStep 7242493 = 2715935) B2715935
theorem B9656657 : Blo 1907435 9656657 := bstep (se 2 (by rfl) ⟨3621246, by rfl⟩ : syracuseStep 9656657 = 7242493) B7242493
theorem B6437771 : Blo 1907435 6437771 := bstep (se 1 (by rfl) ⟨4828328, by rfl⟩ : syracuseStep 6437771 = 9656657) B9656657
theorem B4291847 : Blo 1907435 4291847 := bstep (se 1 (by rfl) ⟨3218885, by rfl⟩ : syracuseStep 4291847 = 6437771) B6437771
theorem B2861231 : Blo 1907435 2861231 := bstep (se 1 (by rfl) ⟨2145923, by rfl⟩ : syracuseStep 2861231 = 4291847) B4291847
theorem B1907487 : Blo 1907435 1907487 := bstep (se 1 (by rfl) ⟨1430615, by rfl⟩ : syracuseStep 1907487 = 2861231) B2861231
theorem B2861237 : Blo 1907435 2861237 := bbase (se 5 (by rfl) ⟨134120, by rfl⟩ : syracuseStep 2861237 = 268241) (by norm_num)
theorem B1907491 : Blo 1907435 1907491 := bstep (se 1 (by rfl) ⟨1430618, by rfl⟩ : syracuseStep 1907491 = 2861237) B2861237
theorem B4828349 : Blo 1907435 4828349 := bbase (se 3 (by rfl) ⟨905315, by rfl⟩ : syracuseStep 4828349 = 1810631) (by norm_num)
theorem B3218899 : Blo 1907435 3218899 := bstep (se 1 (by rfl) ⟨2414174, by rfl⟩ : syracuseStep 3218899 = 4828349) B4828349
theorem B4291865 : Blo 1907435 4291865 := bstep (se 2 (by rfl) ⟨1609449, by rfl⟩ : syracuseStep 4291865 = 3218899) B3218899
theorem B2861243 : Blo 1907435 2861243 := bstep (se 1 (by rfl) ⟨2145932, by rfl⟩ : syracuseStep 2861243 = 4291865) B4291865
theorem B1907495 : Blo 1907435 1907495 := bstep (se 1 (by rfl) ⟨1430621, by rfl⟩ : syracuseStep 1907495 = 2861243) B2861243
theorem B2145937 : Blo 1907435 2145937 := bbase (se 2 (by rfl) ⟨804726, by rfl⟩ : syracuseStep 2145937 = 1609453) (by norm_num)
theorem B2861249 : Blo 1907435 2861249 := bstep (se 2 (by rfl) ⟨1072968, by rfl⟩ : syracuseStep 2861249 = 2145937) B2145937
theorem B1907499 : Blo 1907435 1907499 := bstep (se 1 (by rfl) ⟨1430624, by rfl⟩ : syracuseStep 1907499 = 2861249) B2861249
theorem B3621277 : Blo 1907435 3621277 := bbase (se 3 (by rfl) ⟨678989, by rfl⟩ : syracuseStep 3621277 = 1357979) (by norm_num)
theorem B4828369 : Blo 1907435 4828369 := bstep (se 2 (by rfl) ⟨1810638, by rfl⟩ : syracuseStep 4828369 = 3621277) B3621277
theorem B6437825 : Blo 1907435 6437825 := bstep (se 2 (by rfl) ⟨2414184, by rfl⟩ : syracuseStep 6437825 = 4828369) B4828369
theorem B4291883 : Blo 1907435 4291883 := bstep (se 1 (by rfl) ⟨3218912, by rfl⟩ : syracuseStep 4291883 = 6437825) B6437825
theorem B2861255 : Blo 1907435 2861255 := bstep (se 1 (by rfl) ⟨2145941, by rfl⟩ : syracuseStep 2861255 = 4291883) B4291883
theorem B1907503 : Blo 1907435 1907503 := bstep (se 1 (by rfl) ⟨1430627, by rfl⟩ : syracuseStep 1907503 = 2861255) B2861255
theorem B2861261 : Blo 1907435 2861261 := bbase (se 3 (by rfl) ⟨536486, by rfl⟩ : syracuseStep 2861261 = 1072973) (by norm_num)
theorem B1907507 : Blo 1907435 1907507 := bstep (se 1 (by rfl) ⟨1430630, by rfl⟩ : syracuseStep 1907507 = 2861261) B2861261
theorem B4291901 : Blo 1907435 4291901 := bbase (se 3 (by rfl) ⟨804731, by rfl⟩ : syracuseStep 4291901 = 1609463) (by norm_num)
theorem B2861267 : Blo 1907435 2861267 := bstep (se 1 (by rfl) ⟨2145950, by rfl⟩ : syracuseStep 2861267 = 4291901) B4291901
theorem B1907511 : Blo 1907435 1907511 := bstep (se 1 (by rfl) ⟨1430633, by rfl⟩ : syracuseStep 1907511 = 2861267) B2861267
theorem B3218933 : Blo 1907435 3218933 := bbase (se 5 (by rfl) ⟨150887, by rfl⟩ : syracuseStep 3218933 = 301775) (by norm_num)
theorem B2145955 : Blo 1907435 2145955 := bstep (se 1 (by rfl) ⟨1609466, by rfl⟩ : syracuseStep 2145955 = 3218933) B3218933
theorem B2861273 : Blo 1907435 2861273 := bstep (se 2 (by rfl) ⟨1072977, by rfl⟩ : syracuseStep 2861273 = 2145955) B2145955
theorem B1907515 : Blo 1907435 1907515 := bstep (se 1 (by rfl) ⟨1430636, by rfl⟩ : syracuseStep 1907515 = 2861273) B2861273
theorem B2291609 : Blo 1907435 2291609 := bbase (se 2 (by rfl) ⟨859353, by rfl⟩ : syracuseStep 2291609 = 1718707) (by norm_num)
theorem B6110957 : Blo 1907435 6110957 := bstep (se 3 (by rfl) ⟨1145804, by rfl⟩ : syracuseStep 6110957 = 2291609) B2291609
theorem B4073971 : Blo 1907435 4073971 := bstep (se 1 (by rfl) ⟨3055478, by rfl⟩ : syracuseStep 4073971 = 6110957) B6110957
theorem B5431961 : Blo 1907435 5431961 := bstep (se 2 (by rfl) ⟨2036985, by rfl⟩ : syracuseStep 5431961 = 4073971) B4073971
theorem B14485229 : Blo 1907435 14485229 := bstep (se 3 (by rfl) ⟨2715980, by rfl⟩ : syracuseStep 14485229 = 5431961) B5431961
theorem B9656819 : Blo 1907435 9656819 := bstep (se 1 (by rfl) ⟨7242614, by rfl⟩ : syracuseStep 9656819 = 14485229) B14485229
theorem B6437879 : Blo 1907435 6437879 := bstep (se 1 (by rfl) ⟨4828409, by rfl⟩ : syracuseStep 6437879 = 9656819) B9656819
theorem B4291919 : Blo 1907435 4291919 := bstep (se 1 (by rfl) ⟨3218939, by rfl⟩ : syracuseStep 4291919 = 6437879) B6437879
theorem B2861279 : Blo 1907435 2861279 := bstep (se 1 (by rfl) ⟨2145959, by rfl⟩ : syracuseStep 2861279 = 4291919) B4291919
theorem B1907519 : Blo 1907435 1907519 := bstep (se 1 (by rfl) ⟨1430639, by rfl⟩ : syracuseStep 1907519 = 2861279) B2861279
theorem B2861285 : Blo 1907435 2861285 := bbase (se 4 (by rfl) ⟨268245, by rfl⟩ : syracuseStep 2861285 = 536491) (by norm_num)
theorem B1907523 : Blo 1907435 1907523 := bstep (se 1 (by rfl) ⟨1430642, by rfl⟩ : syracuseStep 1907523 = 2861285) B2861285
theorem B4073989 : Blo 1907435 4073989 := bbase (se 4 (by rfl) ⟨381936, by rfl⟩ : syracuseStep 4073989 = 763873) (by norm_num)
theorem B5431985 : Blo 1907435 5431985 := bstep (se 2 (by rfl) ⟨2036994, by rfl⟩ : syracuseStep 5431985 = 4073989) B4073989
theorem B3621323 : Blo 1907435 3621323 := bstep (se 1 (by rfl) ⟨2715992, by rfl⟩ : syracuseStep 3621323 = 5431985) B5431985
theorem B2414215 : Blo 1907435 2414215 := bstep (se 1 (by rfl) ⟨1810661, by rfl⟩ : syracuseStep 2414215 = 3621323) B3621323
theorem B3218953 : Blo 1907435 3218953 := bstep (se 2 (by rfl) ⟨1207107, by rfl⟩ : syracuseStep 3218953 = 2414215) B2414215
theorem B4291937 : Blo 1907435 4291937 := bstep (se 2 (by rfl) ⟨1609476, by rfl⟩ : syracuseStep 4291937 = 3218953) B3218953
theorem B2861291 : Blo 1907435 2861291 := bstep (se 1 (by rfl) ⟨2145968, by rfl⟩ : syracuseStep 2861291 = 4291937) B4291937
theorem B1907527 : Blo 1907435 1907527 := bstep (se 1 (by rfl) ⟨1430645, by rfl⟩ : syracuseStep 1907527 = 2861291) B2861291
theorem B2145973 : Blo 1907435 2145973 := bbase (se 5 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 2145973 = 201185) (by norm_num)
theorem B2861297 : Blo 1907435 2861297 := bstep (se 2 (by rfl) ⟨1072986, by rfl⟩ : syracuseStep 2861297 = 2145973) B2145973
theorem B1907531 : Blo 1907435 1907531 := bstep (se 1 (by rfl) ⟨1430648, by rfl⟩ : syracuseStep 1907531 = 2861297) B2861297
theorem B2414225 : Blo 1907435 2414225 := bbase (se 2 (by rfl) ⟨905334, by rfl⟩ : syracuseStep 2414225 = 1810669) (by norm_num)
theorem B6437933 : Blo 1907435 6437933 := bstep (se 3 (by rfl) ⟨1207112, by rfl⟩ : syracuseStep 6437933 = 2414225) B2414225
theorem B4291955 : Blo 1907435 4291955 := bstep (se 1 (by rfl) ⟨3218966, by rfl⟩ : syracuseStep 4291955 = 6437933) B6437933
theorem B2861303 : Blo 1907435 2861303 := bstep (se 1 (by rfl) ⟨2145977, by rfl⟩ : syracuseStep 2861303 = 4291955) B4291955
theorem B1907535 : Blo 1907435 1907535 := bstep (se 1 (by rfl) ⟨1430651, by rfl⟩ : syracuseStep 1907535 = 2861303) B2861303
theorem B2861309 : Blo 1907435 2861309 := bbase (se 3 (by rfl) ⟨536495, by rfl⟩ : syracuseStep 2861309 = 1072991) (by norm_num)
theorem B1907539 : Blo 1907435 1907539 := bstep (se 1 (by rfl) ⟨1430654, by rfl⟩ : syracuseStep 1907539 = 2861309) B2861309
theorem B4291973 : Blo 1907435 4291973 := bbase (se 4 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 4291973 = 804745) (by norm_num)
theorem B2861315 : Blo 1907435 2861315 := bstep (se 1 (by rfl) ⟨2145986, by rfl⟩ : syracuseStep 2861315 = 4291973) B4291973
theorem B1907543 : Blo 1907435 1907543 := bstep (se 1 (by rfl) ⟨1430657, by rfl⟩ : syracuseStep 1907543 = 2861315) B2861315
theorem B2716021 : Blo 1907435 2716021 := bbase (se 5 (by rfl) ⟨127313, by rfl⟩ : syracuseStep 2716021 = 254627) (by norm_num)
theorem B3621361 : Blo 1907435 3621361 := bstep (se 2 (by rfl) ⟨1358010, by rfl⟩ : syracuseStep 3621361 = 2716021) B2716021
theorem B4828481 : Blo 1907435 4828481 := bstep (se 2 (by rfl) ⟨1810680, by rfl⟩ : syracuseStep 4828481 = 3621361) B3621361
theorem B3218987 : Blo 1907435 3218987 := bstep (se 1 (by rfl) ⟨2414240, by rfl⟩ : syracuseStep 3218987 = 4828481) B4828481
theorem B2145991 : Blo 1907435 2145991 := bstep (se 1 (by rfl) ⟨1609493, by rfl⟩ : syracuseStep 2145991 = 3218987) B3218987
theorem B2861321 : Blo 1907435 2861321 := bstep (se 2 (by rfl) ⟨1072995, by rfl⟩ : syracuseStep 2861321 = 2145991) B2145991
theorem B1907547 : Blo 1907435 1907547 := bstep (se 1 (by rfl) ⟨1430660, by rfl⟩ : syracuseStep 1907547 = 2861321) B2861321
theorem B9656981 : Blo 1907435 9656981 := bbase (se 6 (by rfl) ⟨226335, by rfl⟩ : syracuseStep 9656981 = 452671) (by norm_num)
theorem B6437987 : Blo 1907435 6437987 := bstep (se 1 (by rfl) ⟨4828490, by rfl⟩ : syracuseStep 6437987 = 9656981) B9656981
theorem B4291991 : Blo 1907435 4291991 := bstep (se 1 (by rfl) ⟨3218993, by rfl⟩ : syracuseStep 4291991 = 6437987) B6437987
theorem B2861327 : Blo 1907435 2861327 := bstep (se 1 (by rfl) ⟨2145995, by rfl⟩ : syracuseStep 2861327 = 4291991) B4291991
theorem B1907551 : Blo 1907435 1907551 := bstep (se 1 (by rfl) ⟨1430663, by rfl⟩ : syracuseStep 1907551 = 2861327) B2861327
theorem B2861333 : Blo 1907435 2861333 := bbase (se 6 (by rfl) ⟨67062, by rfl⟩ : syracuseStep 2861333 = 134125) (by norm_num)
theorem B1907555 : Blo 1907435 1907555 := bstep (se 1 (by rfl) ⟨1430666, by rfl⟩ : syracuseStep 1907555 = 2861333) B2861333
theorem B2291657 : Blo 1907435 2291657 := bbase (se 2 (by rfl) ⟨859371, by rfl⟩ : syracuseStep 2291657 = 1718743) (by norm_num)
theorem B24444341 : Blo 1907435 24444341 := bstep (se 5 (by rfl) ⟨1145828, by rfl⟩ : syracuseStep 24444341 = 2291657) B2291657
theorem B16296227 : Blo 1907435 16296227 := bstep (se 1 (by rfl) ⟨12222170, by rfl⟩ : syracuseStep 16296227 = 24444341) B24444341
theorem B10864151 : Blo 1907435 10864151 := bstep (se 1 (by rfl) ⟨8148113, by rfl⟩ : syracuseStep 10864151 = 16296227) B16296227
theorem B7242767 : Blo 1907435 7242767 := bstep (se 1 (by rfl) ⟨5432075, by rfl⟩ : syracuseStep 7242767 = 10864151) B10864151
theorem B4828511 : Blo 1907435 4828511 := bstep (se 1 (by rfl) ⟨3621383, by rfl⟩ : syracuseStep 4828511 = 7242767) B7242767
theorem B3219007 : Blo 1907435 3219007 := bstep (se 1 (by rfl) ⟨2414255, by rfl⟩ : syracuseStep 3219007 = 4828511) B4828511
theorem B4292009 : Blo 1907435 4292009 := bstep (se 2 (by rfl) ⟨1609503, by rfl⟩ : syracuseStep 4292009 = 3219007) B3219007
theorem B2861339 : Blo 1907435 2861339 := bstep (se 1 (by rfl) ⟨2146004, by rfl⟩ : syracuseStep 2861339 = 4292009) B4292009
theorem B1907559 : Blo 1907435 1907559 := bstep (se 1 (by rfl) ⟨1430669, by rfl⟩ : syracuseStep 1907559 = 2861339) B2861339
theorem B2146009 : Blo 1907435 2146009 := bbase (se 2 (by rfl) ⟨804753, by rfl⟩ : syracuseStep 2146009 = 1609507) (by norm_num)
theorem B2861345 : Blo 1907435 2861345 := bstep (se 2 (by rfl) ⟨1073004, by rfl⟩ : syracuseStep 2861345 = 2146009) B2146009
theorem B1907563 : Blo 1907435 1907563 := bstep (se 1 (by rfl) ⟨1430672, by rfl⟩ : syracuseStep 1907563 = 2861345) B2861345
theorem B2037037 : Blo 1907435 2037037 := bbase (se 3 (by rfl) ⟨381944, by rfl⟩ : syracuseStep 2037037 = 763889) (by norm_num)
theorem B2716049 : Blo 1907435 2716049 := bstep (se 2 (by rfl) ⟨1018518, by rfl⟩ : syracuseStep 2716049 = 2037037) B2037037
theorem B7242797 : Blo 1907435 7242797 := bstep (se 3 (by rfl) ⟨1358024, by rfl⟩ : syracuseStep 7242797 = 2716049) B2716049
theorem B4828531 : Blo 1907435 4828531 := bstep (se 1 (by rfl) ⟨3621398, by rfl⟩ : syracuseStep 4828531 = 7242797) B7242797
theorem B6438041 : Blo 1907435 6438041 := bstep (se 2 (by rfl) ⟨2414265, by rfl⟩ : syracuseStep 6438041 = 4828531) B4828531
theorem B4292027 : Blo 1907435 4292027 := bstep (se 1 (by rfl) ⟨3219020, by rfl⟩ : syracuseStep 4292027 = 6438041) B6438041
theorem B2861351 : Blo 1907435 2861351 := bstep (se 1 (by rfl) ⟨2146013, by rfl⟩ : syracuseStep 2861351 = 4292027) B4292027
theorem B1907567 : Blo 1907435 1907567 := bstep (se 1 (by rfl) ⟨1430675, by rfl⟩ : syracuseStep 1907567 = 2861351) B2861351
theorem B2861357 : Blo 1907435 2861357 := bbase (se 3 (by rfl) ⟨536504, by rfl⟩ : syracuseStep 2861357 = 1073009) (by norm_num)
theorem B1907571 : Blo 1907435 1907571 := bstep (se 1 (by rfl) ⟨1430678, by rfl⟩ : syracuseStep 1907571 = 2861357) B2861357
theorem B4292045 : Blo 1907435 4292045 := bbase (se 3 (by rfl) ⟨804758, by rfl⟩ : syracuseStep 4292045 = 1609517) (by norm_num)
theorem B2861363 : Blo 1907435 2861363 := bstep (se 1 (by rfl) ⟨2146022, by rfl⟩ : syracuseStep 2861363 = 4292045) B4292045
theorem B1907575 : Blo 1907435 1907575 := bstep (se 1 (by rfl) ⟨1430681, by rfl⟩ : syracuseStep 1907575 = 2861363) B2861363
theorem B2414281 : Blo 1907435 2414281 := bbase (se 2 (by rfl) ⟨905355, by rfl⟩ : syracuseStep 2414281 = 1810711) (by norm_num)
theorem B3219041 : Blo 1907435 3219041 := bstep (se 2 (by rfl) ⟨1207140, by rfl⟩ : syracuseStep 3219041 = 2414281) B2414281
theorem B2146027 : Blo 1907435 2146027 := bstep (se 1 (by rfl) ⟨1609520, by rfl⟩ : syracuseStep 2146027 = 3219041) B3219041
theorem B2861369 : Blo 1907435 2861369 := bstep (se 2 (by rfl) ⟨1073013, by rfl⟩ : syracuseStep 2861369 = 2146027) B2146027
theorem B1907579 : Blo 1907435 1907579 := bstep (se 1 (by rfl) ⟨1430684, by rfl⟩ : syracuseStep 1907579 = 2861369) B2861369
theorem B5156293 : Blo 1907435 5156293 := bbase (se 4 (by rfl) ⟨483402, by rfl⟩ : syracuseStep 5156293 = 966805) (by norm_num)
theorem B6875057 : Blo 1907435 6875057 := bstep (se 2 (by rfl) ⟨2578146, by rfl⟩ : syracuseStep 6875057 = 5156293) B5156293
theorem B18333485 : Blo 1907435 18333485 := bstep (se 3 (by rfl) ⟨3437528, by rfl⟩ : syracuseStep 18333485 = 6875057) B6875057
theorem B12222323 : Blo 1907435 12222323 := bstep (se 1 (by rfl) ⟨9166742, by rfl⟩ : syracuseStep 12222323 = 18333485) B18333485
theorem B8148215 : Blo 1907435 8148215 := bstep (se 1 (by rfl) ⟨6111161, by rfl⟩ : syracuseStep 8148215 = 12222323) B12222323
theorem B21728573 : Blo 1907435 21728573 := bstep (se 3 (by rfl) ⟨4074107, by rfl⟩ : syracuseStep 21728573 = 8148215) B8148215
theorem B14485715 : Blo 1907435 14485715 := bstep (se 1 (by rfl) ⟨10864286, by rfl⟩ : syracuseStep 14485715 = 21728573) B21728573
theorem B9657143 : Blo 1907435 9657143 := bstep (se 1 (by rfl) ⟨7242857, by rfl⟩ : syracuseStep 9657143 = 14485715) B14485715
theorem B6438095 : Blo 1907435 6438095 := bstep (se 1 (by rfl) ⟨4828571, by rfl⟩ : syracuseStep 6438095 = 9657143) B9657143
theorem B4292063 : Blo 1907435 4292063 := bstep (se 1 (by rfl) ⟨3219047, by rfl⟩ : syracuseStep 4292063 = 6438095) B6438095
theorem B2861375 : Blo 1907435 2861375 := bstep (se 1 (by rfl) ⟨2146031, by rfl⟩ : syracuseStep 2861375 = 4292063) B4292063
theorem B1907583 : Blo 1907435 1907583 := bstep (se 1 (by rfl) ⟨1430687, by rfl⟩ : syracuseStep 1907583 = 2861375) B2861375
theorem B2861381 : Blo 1907435 2861381 := bbase (se 4 (by rfl) ⟨268254, by rfl⟩ : syracuseStep 2861381 = 536509) (by norm_num)
theorem B1907587 : Blo 1907435 1907587 := bstep (se 1 (by rfl) ⟨1430690, by rfl⟩ : syracuseStep 1907587 = 2861381) B2861381
theorem B3219061 : Blo 1907435 3219061 := bbase (se 5 (by rfl) ⟨150893, by rfl⟩ : syracuseStep 3219061 = 301787) (by norm_num)
theorem B4292081 : Blo 1907435 4292081 := bstep (se 2 (by rfl) ⟨1609530, by rfl⟩ : syracuseStep 4292081 = 3219061) B3219061
theorem B2861387 : Blo 1907435 2861387 := bstep (se 1 (by rfl) ⟨2146040, by rfl⟩ : syracuseStep 2861387 = 4292081) B4292081
theorem B1907591 : Blo 1907435 1907591 := bstep (se 1 (by rfl) ⟨1430693, by rfl⟩ : syracuseStep 1907591 = 2861387) B2861387
theorem B2146045 : Blo 1907435 2146045 := bbase (se 3 (by rfl) ⟨402383, by rfl⟩ : syracuseStep 2146045 = 804767) (by norm_num)
theorem B2861393 : Blo 1907435 2861393 := bstep (se 2 (by rfl) ⟨1073022, by rfl⟩ : syracuseStep 2861393 = 2146045) B2146045
theorem B1907595 : Blo 1907435 1907595 := bstep (se 1 (by rfl) ⟨1430696, by rfl⟩ : syracuseStep 1907595 = 2861393) B2861393
theorem B6438149 : Blo 1907435 6438149 := bbase (se 4 (by rfl) ⟨603576, by rfl⟩ : syracuseStep 6438149 = 1207153) (by norm_num)
theorem B4292099 : Blo 1907435 4292099 := bstep (se 1 (by rfl) ⟨3219074, by rfl⟩ : syracuseStep 4292099 = 6438149) B6438149
theorem B2861399 : Blo 1907435 2861399 := bstep (se 1 (by rfl) ⟨2146049, by rfl⟩ : syracuseStep 2861399 = 4292099) B4292099
theorem B1907599 : Blo 1907435 1907599 := bstep (se 1 (by rfl) ⟨1430699, by rfl⟩ : syracuseStep 1907599 = 2861399) B2861399
theorem B2861405 : Blo 1907435 2861405 := bbase (se 3 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 2861405 = 1073027) (by norm_num)
theorem B1907603 : Blo 1907435 1907603 := bstep (se 1 (by rfl) ⟨1430702, by rfl⟩ : syracuseStep 1907603 = 2861405) B2861405
theorem B4292117 : Blo 1907435 4292117 := bbase (se 6 (by rfl) ⟨100596, by rfl⟩ : syracuseStep 4292117 = 201193) (by norm_num)
theorem B2861411 : Blo 1907435 2861411 := bstep (se 1 (by rfl) ⟨2146058, by rfl⟩ : syracuseStep 2861411 = 4292117) B4292117
theorem B1907607 : Blo 1907435 1907607 := bstep (se 1 (by rfl) ⟨1430705, by rfl⟩ : syracuseStep 1907607 = 2861411) B2861411
theorem B7242965 : Blo 1907435 7242965 := bbase (se 7 (by rfl) ⟨84878, by rfl⟩ : syracuseStep 7242965 = 169757) (by norm_num)
theorem B4828643 : Blo 1907435 4828643 := bstep (se 1 (by rfl) ⟨3621482, by rfl⟩ : syracuseStep 4828643 = 7242965) B7242965
theorem B3219095 : Blo 1907435 3219095 := bstep (se 1 (by rfl) ⟨2414321, by rfl⟩ : syracuseStep 3219095 = 4828643) B4828643
theorem B2146063 : Blo 1907435 2146063 := bstep (se 1 (by rfl) ⟨1609547, by rfl⟩ : syracuseStep 2146063 = 3219095) B3219095
theorem B2861417 : Blo 1907435 2861417 := bstep (se 2 (by rfl) ⟨1073031, by rfl⟩ : syracuseStep 2861417 = 2146063) B2146063
theorem B1907611 : Blo 1907435 1907611 := bstep (se 1 (by rfl) ⟨1430708, by rfl⟩ : syracuseStep 1907611 = 2861417) B2861417
theorem B10864469 : Blo 1907435 10864469 := bbase (se 9 (by rfl) ⟨31829, by rfl⟩ : syracuseStep 10864469 = 63659) (by norm_num)
theorem B7242979 : Blo 1907435 7242979 := bstep (se 1 (by rfl) ⟨5432234, by rfl⟩ : syracuseStep 7242979 = 10864469) B10864469
theorem B9657305 : Blo 1907435 9657305 := bstep (se 2 (by rfl) ⟨3621489, by rfl⟩ : syracuseStep 9657305 = 7242979) B7242979
theorem B6438203 : Blo 1907435 6438203 := bstep (se 1 (by rfl) ⟨4828652, by rfl⟩ : syracuseStep 6438203 = 9657305) B9657305
theorem B4292135 : Blo 1907435 4292135 := bstep (se 1 (by rfl) ⟨3219101, by rfl⟩ : syracuseStep 4292135 = 6438203) B6438203
theorem B2861423 : Blo 1907435 2861423 := bstep (se 1 (by rfl) ⟨2146067, by rfl⟩ : syracuseStep 2861423 = 4292135) B4292135
theorem B1907615 : Blo 1907435 1907615 := bstep (se 1 (by rfl) ⟨1430711, by rfl⟩ : syracuseStep 1907615 = 2861423) B2861423
theorem B2861429 : Blo 1907435 2861429 := bbase (se 5 (by rfl) ⟨134129, by rfl⟩ : syracuseStep 2861429 = 268259) (by norm_num)
theorem B1907619 : Blo 1907435 1907619 := bstep (se 1 (by rfl) ⟨1430714, by rfl⟩ : syracuseStep 1907619 = 2861429) B2861429
theorem B2037097 : Blo 1907435 2037097 := bbase (se 2 (by rfl) ⟨763911, by rfl⟩ : syracuseStep 2037097 = 1527823) (by norm_num)
theorem B2716129 : Blo 1907435 2716129 := bstep (se 2 (by rfl) ⟨1018548, by rfl⟩ : syracuseStep 2716129 = 2037097) B2037097
theorem B3621505 : Blo 1907435 3621505 := bstep (se 2 (by rfl) ⟨1358064, by rfl⟩ : syracuseStep 3621505 = 2716129) B2716129
theorem B4828673 : Blo 1907435 4828673 := bstep (se 2 (by rfl) ⟨1810752, by rfl⟩ : syracuseStep 4828673 = 3621505) B3621505
theorem B3219115 : Blo 1907435 3219115 := bstep (se 1 (by rfl) ⟨2414336, by rfl⟩ : syracuseStep 3219115 = 4828673) B4828673
theorem B4292153 : Blo 1907435 4292153 := bstep (se 2 (by rfl) ⟨1609557, by rfl⟩ : syracuseStep 4292153 = 3219115) B3219115
theorem B2861435 : Blo 1907435 2861435 := bstep (se 1 (by rfl) ⟨2146076, by rfl⟩ : syracuseStep 2861435 = 4292153) B4292153
theorem B1907623 : Blo 1907435 1907623 := bstep (se 1 (by rfl) ⟨1430717, by rfl⟩ : syracuseStep 1907623 = 2861435) B2861435
theorem B2146081 : Blo 1907435 2146081 := bbase (se 2 (by rfl) ⟨804780, by rfl⟩ : syracuseStep 2146081 = 1609561) (by norm_num)
theorem B2861441 : Blo 1907435 2861441 := bstep (se 2 (by rfl) ⟨1073040, by rfl⟩ : syracuseStep 2861441 = 2146081) B2146081
theorem B1907627 : Blo 1907435 1907627 := bstep (se 1 (by rfl) ⟨1430720, by rfl⟩ : syracuseStep 1907627 = 2861441) B2861441
theorem B4828693 : Blo 1907435 4828693 := bbase (se 6 (by rfl) ⟨113172, by rfl⟩ : syracuseStep 4828693 = 226345) (by norm_num)
theorem B6438257 : Blo 1907435 6438257 := bstep (se 2 (by rfl) ⟨2414346, by rfl⟩ : syracuseStep 6438257 = 4828693) B4828693
theorem B4292171 : Blo 1907435 4292171 := bstep (se 1 (by rfl) ⟨3219128, by rfl⟩ : syracuseStep 4292171 = 6438257) B6438257
theorem B2861447 : Blo 1907435 2861447 := bstep (se 1 (by rfl) ⟨2146085, by rfl⟩ : syracuseStep 2861447 = 4292171) B4292171
theorem B1907631 : Blo 1907435 1907631 := bstep (se 1 (by rfl) ⟨1430723, by rfl⟩ : syracuseStep 1907631 = 2861447) B2861447
theorem B2861453 : Blo 1907435 2861453 := bbase (se 3 (by rfl) ⟨536522, by rfl⟩ : syracuseStep 2861453 = 1073045) (by norm_num)
theorem B1907635 : Blo 1907435 1907635 := bstep (se 1 (by rfl) ⟨1430726, by rfl⟩ : syracuseStep 1907635 = 2861453) B2861453
theorem B4292189 : Blo 1907435 4292189 := bbase (se 3 (by rfl) ⟨804785, by rfl⟩ : syracuseStep 4292189 = 1609571) (by norm_num)
theorem B2861459 : Blo 1907435 2861459 := bstep (se 1 (by rfl) ⟨2146094, by rfl⟩ : syracuseStep 2861459 = 4292189) B4292189
theorem B1907639 : Blo 1907435 1907639 := bstep (se 1 (by rfl) ⟨1430729, by rfl⟩ : syracuseStep 1907639 = 2861459) B2861459
theorem B3219149 : Blo 1907435 3219149 := bbase (se 3 (by rfl) ⟨603590, by rfl⟩ : syracuseStep 3219149 = 1207181) (by norm_num)
theorem B2146099 : Blo 1907435 2146099 := bstep (se 1 (by rfl) ⟨1609574, by rfl⟩ : syracuseStep 2146099 = 3219149) B3219149
theorem B2861465 : Blo 1907435 2861465 := bstep (se 2 (by rfl) ⟨1073049, by rfl⟩ : syracuseStep 2861465 = 2146099) B2146099
theorem B1907643 : Blo 1907435 1907643 := bstep (se 1 (by rfl) ⟨1430732, by rfl⟩ : syracuseStep 1907643 = 2861465) B2861465
theorem B4583525 : Blo 1907435 4583525 := bbase (se 4 (by rfl) ⟨429705, by rfl⟩ : syracuseStep 4583525 = 859411) (by norm_num)
theorem B12222733 : Blo 1907435 12222733 := bstep (se 3 (by rfl) ⟨2291762, by rfl⟩ : syracuseStep 12222733 = 4583525) B4583525
theorem B16296977 : Blo 1907435 16296977 := bstep (se 2 (by rfl) ⟨6111366, by rfl⟩ : syracuseStep 16296977 = 12222733) B12222733
theorem B10864651 : Blo 1907435 10864651 := bstep (se 1 (by rfl) ⟨8148488, by rfl⟩ : syracuseStep 10864651 = 16296977) B16296977
theorem B14486201 : Blo 1907435 14486201 := bstep (se 2 (by rfl) ⟨5432325, by rfl⟩ : syracuseStep 14486201 = 10864651) B10864651
theorem B9657467 : Blo 1907435 9657467 := bstep (se 1 (by rfl) ⟨7243100, by rfl⟩ : syracuseStep 9657467 = 14486201) B14486201
theorem B6438311 : Blo 1907435 6438311 := bstep (se 1 (by rfl) ⟨4828733, by rfl⟩ : syracuseStep 6438311 = 9657467) B9657467
theorem B4292207 : Blo 1907435 4292207 := bstep (se 1 (by rfl) ⟨3219155, by rfl⟩ : syracuseStep 4292207 = 6438311) B6438311
theorem B2861471 : Blo 1907435 2861471 := bstep (se 1 (by rfl) ⟨2146103, by rfl⟩ : syracuseStep 2861471 = 4292207) B4292207
theorem B1907647 : Blo 1907435 1907647 := bstep (se 1 (by rfl) ⟨1430735, by rfl⟩ : syracuseStep 1907647 = 2861471) B2861471
theorem B2861477 : Blo 1907435 2861477 := bbase (se 4 (by rfl) ⟨268263, by rfl⟩ : syracuseStep 2861477 = 536527) (by norm_num)
theorem B1907651 : Blo 1907435 1907651 := bstep (se 1 (by rfl) ⟨1430738, by rfl⟩ : syracuseStep 1907651 = 2861477) B2861477
theorem B2414377 : Blo 1907435 2414377 := bbase (se 2 (by rfl) ⟨905391, by rfl⟩ : syracuseStep 2414377 = 1810783) (by norm_num)
theorem B3219169 : Blo 1907435 3219169 := bstep (se 2 (by rfl) ⟨1207188, by rfl⟩ : syracuseStep 3219169 = 2414377) B2414377
theorem B4292225 : Blo 1907435 4292225 := bstep (se 2 (by rfl) ⟨1609584, by rfl⟩ : syracuseStep 4292225 = 3219169) B3219169
theorem B2861483 : Blo 1907435 2861483 := bstep (se 1 (by rfl) ⟨2146112, by rfl⟩ : syracuseStep 2861483 = 4292225) B4292225
theorem B1907655 : Blo 1907435 1907655 := bstep (se 1 (by rfl) ⟨1430741, by rfl⟩ : syracuseStep 1907655 = 2861483) B2861483
theorem B2146117 : Blo 1907435 2146117 := bbase (se 4 (by rfl) ⟨201198, by rfl⟩ : syracuseStep 2146117 = 402397) (by norm_num)
theorem B2861489 : Blo 1907435 2861489 := bstep (se 2 (by rfl) ⟨1073058, by rfl⟩ : syracuseStep 2861489 = 2146117) B2146117
theorem B1907659 : Blo 1907435 1907659 := bstep (se 1 (by rfl) ⟨1430744, by rfl⟩ : syracuseStep 1907659 = 2861489) B2861489
theorem B3621581 : Blo 1907435 3621581 := bbase (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) (by norm_num)
theorem B2414387 : Blo 1907435 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B6438365 : Blo 1907435 6438365 := bstep (se 3 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 6438365 = 2414387) B2414387
theorem B4292243 : Blo 1907435 4292243 := bstep (se 1 (by rfl) ⟨3219182, by rfl⟩ : syracuseStep 4292243 = 6438365) B6438365
theorem B2861495 : Blo 1907435 2861495 := bstep (se 1 (by rfl) ⟨2146121, by rfl⟩ : syracuseStep 2861495 = 4292243) B4292243
theorem B1907663 : Blo 1907435 1907663 := bstep (se 1 (by rfl) ⟨1430747, by rfl⟩ : syracuseStep 1907663 = 2861495) B2861495
theorem B2861501 : Blo 1907435 2861501 := bbase (se 3 (by rfl) ⟨536531, by rfl⟩ : syracuseStep 2861501 = 1073063) (by norm_num)
theorem B1907667 : Blo 1907435 1907667 := bstep (se 1 (by rfl) ⟨1430750, by rfl⟩ : syracuseStep 1907667 = 2861501) B2861501
theorem B4292261 : Blo 1907435 4292261 := bbase (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) (by norm_num)
theorem B2861507 : Blo 1907435 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B1907671 : Blo 1907435 1907671 := bstep (se 1 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 1907671 = 2861507) B2861507
theorem B4828805 : Blo 1907435 4828805 := bbase (se 4 (by rfl) ⟨452700, by rfl⟩ : syracuseStep 4828805 = 905401) (by norm_num)
theorem B3219203 : Blo 1907435 3219203 := bstep (se 1 (by rfl) ⟨2414402, by rfl⟩ : syracuseStep 3219203 = 4828805) B4828805
theorem B2146135 : Blo 1907435 2146135 := bstep (se 1 (by rfl) ⟨1609601, by rfl⟩ : syracuseStep 2146135 = 3219203) B3219203
theorem B2861513 : Blo 1907435 2861513 := bstep (se 2 (by rfl) ⟨1073067, by rfl⟩ : syracuseStep 2861513 = 2146135) B2146135
theorem B1907675 : Blo 1907435 1907675 := bstep (se 1 (by rfl) ⟨1430756, by rfl⟩ : syracuseStep 1907675 = 2861513) B2861513
theorem B2578277 : Blo 1907435 2578277 := bbase (se 4 (by rfl) ⟨241713, by rfl⟩ : syracuseStep 2578277 = 483427) (by norm_num)
theorem B6875405 : Blo 1907435 6875405 := bstep (se 3 (by rfl) ⟨1289138, by rfl⟩ : syracuseStep 6875405 = 2578277) B2578277
theorem B4583603 : Blo 1907435 4583603 := bstep (se 1 (by rfl) ⟨3437702, by rfl⟩ : syracuseStep 4583603 = 6875405) B6875405
theorem B3055735 : Blo 1907435 3055735 := bstep (se 1 (by rfl) ⟨2291801, by rfl⟩ : syracuseStep 3055735 = 4583603) B4583603
theorem B4074313 : Blo 1907435 4074313 := bstep (se 2 (by rfl) ⟨1527867, by rfl⟩ : syracuseStep 4074313 = 3055735) B3055735
theorem B5432417 : Blo 1907435 5432417 := bstep (se 2 (by rfl) ⟨2037156, by rfl⟩ : syracuseStep 5432417 = 4074313) B4074313
theorem B3621611 : Blo 1907435 3621611 := bstep (se 1 (by rfl) ⟨2716208, by rfl⟩ : syracuseStep 3621611 = 5432417) B5432417
theorem B9657629 : Blo 1907435 9657629 := bstep (se 3 (by rfl) ⟨1810805, by rfl⟩ : syracuseStep 9657629 = 3621611) B3621611
theorem B6438419 : Blo 1907435 6438419 := bstep (se 1 (by rfl) ⟨4828814, by rfl⟩ : syracuseStep 6438419 = 9657629) B9657629
theorem B4292279 : Blo 1907435 4292279 := bstep (se 1 (by rfl) ⟨3219209, by rfl⟩ : syracuseStep 4292279 = 6438419) B6438419
theorem B2861519 : Blo 1907435 2861519 := bstep (se 1 (by rfl) ⟨2146139, by rfl⟩ : syracuseStep 2861519 = 4292279) B4292279
theorem B1907679 : Blo 1907435 1907679 := bstep (se 1 (by rfl) ⟨1430759, by rfl⟩ : syracuseStep 1907679 = 2861519) B2861519
theorem B2861525 : Blo 1907435 2861525 := bbase (se 7 (by rfl) ⟨33533, by rfl⟩ : syracuseStep 2861525 = 67067) (by norm_num)
theorem B1907683 : Blo 1907435 1907683 := bstep (se 1 (by rfl) ⟨1430762, by rfl⟩ : syracuseStep 1907683 = 2861525) B2861525
theorem B7243253 : Blo 1907435 7243253 := bbase (se 5 (by rfl) ⟨339527, by rfl⟩ : syracuseStep 7243253 = 679055) (by norm_num)
theorem B4828835 : Blo 1907435 4828835 := bstep (se 1 (by rfl) ⟨3621626, by rfl⟩ : syracuseStep 4828835 = 7243253) B7243253
theorem B3219223 : Blo 1907435 3219223 := bstep (se 1 (by rfl) ⟨2414417, by rfl⟩ : syracuseStep 3219223 = 4828835) B4828835
theorem B4292297 : Blo 1907435 4292297 := bstep (se 2 (by rfl) ⟨1609611, by rfl⟩ : syracuseStep 4292297 = 3219223) B3219223
theorem B2861531 : Blo 1907435 2861531 := bstep (se 1 (by rfl) ⟨2146148, by rfl⟩ : syracuseStep 2861531 = 4292297) B4292297
theorem B1907687 : Blo 1907435 1907687 := bstep (se 1 (by rfl) ⟨1430765, by rfl⟩ : syracuseStep 1907687 = 2861531) B2861531
theorem B2146153 : Blo 1907435 2146153 := bbase (se 2 (by rfl) ⟨804807, by rfl⟩ : syracuseStep 2146153 = 1609615) (by norm_num)
theorem B2861537 : Blo 1907435 2861537 := bstep (se 2 (by rfl) ⟨1073076, by rfl⟩ : syracuseStep 2861537 = 2146153) B2146153
theorem B1907691 : Blo 1907435 1907691 := bstep (se 1 (by rfl) ⟨1430768, by rfl⟩ : syracuseStep 1907691 = 2861537) B2861537
theorem B5156597 : Blo 1907435 5156597 := bbase (se 5 (by rfl) ⟨241715, by rfl⟩ : syracuseStep 5156597 = 483431) (by norm_num)
theorem B3437731 : Blo 1907435 3437731 := bstep (se 1 (by rfl) ⟨2578298, by rfl⟩ : syracuseStep 3437731 = 5156597) B5156597
theorem B4583641 : Blo 1907435 4583641 := bstep (se 2 (by rfl) ⟨1718865, by rfl⟩ : syracuseStep 4583641 = 3437731) B3437731
theorem B6111521 : Blo 1907435 6111521 := bstep (se 2 (by rfl) ⟨2291820, by rfl⟩ : syracuseStep 6111521 = 4583641) B4583641
theorem B4074347 : Blo 1907435 4074347 := bstep (se 1 (by rfl) ⟨3055760, by rfl⟩ : syracuseStep 4074347 = 6111521) B6111521
theorem B10864925 : Blo 1907435 10864925 := bstep (se 3 (by rfl) ⟨2037173, by rfl⟩ : syracuseStep 10864925 = 4074347) B4074347
theorem B7243283 : Blo 1907435 7243283 := bstep (se 1 (by rfl) ⟨5432462, by rfl⟩ : syracuseStep 7243283 = 10864925) B10864925
theorem B4828855 : Blo 1907435 4828855 := bstep (se 1 (by rfl) ⟨3621641, by rfl⟩ : syracuseStep 4828855 = 7243283) B7243283
theorem B6438473 : Blo 1907435 6438473 := bstep (se 2 (by rfl) ⟨2414427, by rfl⟩ : syracuseStep 6438473 = 4828855) B4828855
theorem B4292315 : Blo 1907435 4292315 := bstep (se 1 (by rfl) ⟨3219236, by rfl⟩ : syracuseStep 4292315 = 6438473) B6438473
theorem B2861543 : Blo 1907435 2861543 := bstep (se 1 (by rfl) ⟨2146157, by rfl⟩ : syracuseStep 2861543 = 4292315) B4292315
theorem B1907695 : Blo 1907435 1907695 := bstep (se 1 (by rfl) ⟨1430771, by rfl⟩ : syracuseStep 1907695 = 2861543) B2861543
theorem B2861549 : Blo 1907435 2861549 := bbase (se 3 (by rfl) ⟨536540, by rfl⟩ : syracuseStep 2861549 = 1073081) (by norm_num)
theorem B1907699 : Blo 1907435 1907699 := bstep (se 1 (by rfl) ⟨1430774, by rfl⟩ : syracuseStep 1907699 = 2861549) B2861549
theorem B4292333 : Blo 1907435 4292333 := bbase (se 3 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 4292333 = 1609625) (by norm_num)
theorem B2861555 : Blo 1907435 2861555 := bstep (se 1 (by rfl) ⟨2146166, by rfl⟩ : syracuseStep 2861555 = 4292333) B4292333
theorem B1907703 : Blo 1907435 1907703 := bstep (se 1 (by rfl) ⟨1430777, by rfl⟩ : syracuseStep 1907703 = 2861555) B2861555
theorem B3055781 : Blo 1907435 3055781 := bbase (se 4 (by rfl) ⟨286479, by rfl⟩ : syracuseStep 3055781 = 572959) (by norm_num)
theorem B2037187 : Blo 1907435 2037187 := bstep (se 1 (by rfl) ⟨1527890, by rfl⟩ : syracuseStep 2037187 = 3055781) B3055781
theorem B2716249 : Blo 1907435 2716249 := bstep (se 2 (by rfl) ⟨1018593, by rfl⟩ : syracuseStep 2716249 = 2037187) B2037187
theorem B3621665 : Blo 1907435 3621665 := bstep (se 2 (by rfl) ⟨1358124, by rfl⟩ : syracuseStep 3621665 = 2716249) B2716249
theorem B2414443 : Blo 1907435 2414443 := bstep (se 1 (by rfl) ⟨1810832, by rfl⟩ : syracuseStep 2414443 = 3621665) B3621665
theorem B3219257 : Blo 1907435 3219257 := bstep (se 2 (by rfl) ⟨1207221, by rfl⟩ : syracuseStep 3219257 = 2414443) B2414443
theorem B2146171 : Blo 1907435 2146171 := bstep (se 1 (by rfl) ⟨1609628, by rfl⟩ : syracuseStep 2146171 = 3219257) B3219257
theorem B2861561 : Blo 1907435 2861561 := bstep (se 2 (by rfl) ⟨1073085, by rfl⟩ : syracuseStep 2861561 = 2146171) B2146171
theorem B1907707 : Blo 1907435 1907707 := bstep (se 1 (by rfl) ⟨1430780, by rfl⟩ : syracuseStep 1907707 = 2861561) B2861561
theorem B3314621 : Blo 1907435 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B2209747 : Blo 1907435 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B188565077 : Blo 1907435 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B125710051 : Blo 1907435 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B167613401 : Blo 1907435 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B111742267 : Blo 1907435 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B148989689 : Blo 1907435 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B99326459 : Blo 1907435 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B264870557 : Blo 1907435 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B176580371 : Blo 1907435 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B470880989 : Blo 1907435 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B313920659 : Blo 1907435 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B209280439 : Blo 1907435 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B279040585 : Blo 1907435 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B372054113 : Blo 1907435 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B248036075 : Blo 1907435 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B165357383 : Blo 1907435 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B440953021 : Blo 1907435 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B587937361 : Blo 1907435 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B783916481 : Blo 1907435 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B522610987 : Blo 1907435 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B696814649 : Blo 1907435 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B464543099 : Blo 1907435 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B309695399 : Blo 1907435 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B206463599 : Blo 1907435 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B137642399 : Blo 1907435 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B91761599 : Blo 1907435 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B61174399 : Blo 1907435 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B81565865 : Blo 1907435 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B54377243 : Blo 1907435 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B36251495 : Blo 1907435 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B24167663 : Blo 1907435 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B16111775 : Blo 1907435 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B10741183 : Blo 1907435 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B57286309 : Blo 1907435 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B76381745 : Blo 1907435 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B203684653 : Blo 1907435 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B271579537 : Blo 1907435 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B362106049 : Blo 1907435 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B482808065 : Blo 1907435 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B5149952693 : Blo 1907435 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B3433301795 : Blo 1907435 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B2288867863 : Blo 1907435 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B3051823817 : Blo 1907435 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B8138196845 : Blo 1907435 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B5425464563 : Blo 1907435 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B3616976375 : Blo 1907435 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B2411317583 : Blo 1907435 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B1607545055 : Blo 1907435 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B1071696703 : Blo 1907435 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B1428928937 : Blo 1907435 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B952619291 : Blo 1907435 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B635079527 : Blo 1907435 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B423386351 : Blo 1907435 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B282257567 : Blo 1907435 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B188171711 : Blo 1907435 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B125447807 : Blo 1907435 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B83631871 : Blo 1907435 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B446036645 : Blo 1907435 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B297357763 : Blo 1907435 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B396477017 : Blo 1907435 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B264318011 : Blo 1907435 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B176212007 : Blo 1907435 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B117474671 : Blo 1907435 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B313265789 : Blo 1907435 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B208843859 : Blo 1907435 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B139229239 : Blo 1907435 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B185638985 : Blo 1907435 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B123759323 : Blo 1907435 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B82506215 : Blo 1907435 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B55004143 : Blo 1907435 55004143 := bstep (se 1 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 55004143 = 82506215) B82506215
theorem B73338857 : Blo 1907435 73338857 := bstep (se 2 (by rfl) ⟨27502071, by rfl⟩ : syracuseStep 73338857 = 55004143) B55004143
theorem B48892571 : Blo 1907435 48892571 := bstep (se 1 (by rfl) ⟨36669428, by rfl⟩ : syracuseStep 48892571 = 73338857) B73338857
theorem B32595047 : Blo 1907435 32595047 := bstep (se 1 (by rfl) ⟨24446285, by rfl⟩ : syracuseStep 32595047 = 48892571) B48892571
theorem B21730031 : Blo 1907435 21730031 := bstep (se 1 (by rfl) ⟨16297523, by rfl⟩ : syracuseStep 21730031 = 32595047) B32595047
theorem B14486687 : Blo 1907435 14486687 := bstep (se 1 (by rfl) ⟨10865015, by rfl⟩ : syracuseStep 14486687 = 21730031) B21730031
theorem B9657791 : Blo 1907435 9657791 := bstep (se 1 (by rfl) ⟨7243343, by rfl⟩ : syracuseStep 9657791 = 14486687) B14486687
theorem B6438527 : Blo 1907435 6438527 := bstep (se 1 (by rfl) ⟨4828895, by rfl⟩ : syracuseStep 6438527 = 9657791) B9657791
theorem B4292351 : Blo 1907435 4292351 := bstep (se 1 (by rfl) ⟨3219263, by rfl⟩ : syracuseStep 4292351 = 6438527) B6438527
theorem B2861567 : Blo 1907435 2861567 := bstep (se 1 (by rfl) ⟨2146175, by rfl⟩ : syracuseStep 2861567 = 4292351) B4292351
theorem B1907711 : Blo 1907435 1907711 := bstep (se 1 (by rfl) ⟨1430783, by rfl⟩ : syracuseStep 1907711 = 2861567) B2861567
theorem B2861573 : Blo 1907435 2861573 := bbase (se 4 (by rfl) ⟨268272, by rfl⟩ : syracuseStep 2861573 = 536545) (by norm_num)
theorem B1907715 : Blo 1907435 1907715 := bstep (se 1 (by rfl) ⟨1430786, by rfl⟩ : syracuseStep 1907715 = 2861573) B2861573
theorem B3219277 : Blo 1907435 3219277 := bbase (se 3 (by rfl) ⟨603614, by rfl⟩ : syracuseStep 3219277 = 1207229) (by norm_num)
theorem B4292369 : Blo 1907435 4292369 := bstep (se 2 (by rfl) ⟨1609638, by rfl⟩ : syracuseStep 4292369 = 3219277) B3219277
theorem B2861579 : Blo 1907435 2861579 := bstep (se 1 (by rfl) ⟨2146184, by rfl⟩ : syracuseStep 2861579 = 4292369) B4292369
theorem B1907719 : Blo 1907435 1907719 := bstep (se 1 (by rfl) ⟨1430789, by rfl⟩ : syracuseStep 1907719 = 2861579) B2861579
theorem B2146189 : Blo 1907435 2146189 := bbase (se 3 (by rfl) ⟨402410, by rfl⟩ : syracuseStep 2146189 = 804821) (by norm_num)
theorem B2861585 : Blo 1907435 2861585 := bstep (se 2 (by rfl) ⟨1073094, by rfl⟩ : syracuseStep 2861585 = 2146189) B2146189
theorem B1907723 : Blo 1907435 1907723 := bstep (se 1 (by rfl) ⟨1430792, by rfl⟩ : syracuseStep 1907723 = 2861585) B2861585
theorem B6438581 : Blo 1907435 6438581 := bbase (se 5 (by rfl) ⟨301808, by rfl⟩ : syracuseStep 6438581 = 603617) (by norm_num)
theorem B4292387 : Blo 1907435 4292387 := bstep (se 1 (by rfl) ⟨3219290, by rfl⟩ : syracuseStep 4292387 = 6438581) B6438581
theorem B2861591 : Blo 1907435 2861591 := bstep (se 1 (by rfl) ⟨2146193, by rfl⟩ : syracuseStep 2861591 = 4292387) B4292387
theorem B1907727 : Blo 1907435 1907727 := bstep (se 1 (by rfl) ⟨1430795, by rfl⟩ : syracuseStep 1907727 = 2861591) B2861591
theorem B2861597 : Blo 1907435 2861597 := bbase (se 3 (by rfl) ⟨536549, by rfl⟩ : syracuseStep 2861597 = 1073099) (by norm_num)
theorem B1907731 : Blo 1907435 1907731 := bstep (se 1 (by rfl) ⟨1430798, by rfl⟩ : syracuseStep 1907731 = 2861597) B2861597
theorem B4292405 : Blo 1907435 4292405 := bbase (se 5 (by rfl) ⟨201206, by rfl⟩ : syracuseStep 4292405 = 402413) (by norm_num)
theorem B2861603 : Blo 1907435 2861603 := bstep (se 1 (by rfl) ⟨2146202, by rfl⟩ : syracuseStep 2861603 = 4292405) B4292405
theorem B1907735 : Blo 1907435 1907735 := bstep (se 1 (by rfl) ⟨1430801, by rfl⟩ : syracuseStep 1907735 = 2861603) B2861603
theorem B6875621 : Blo 1907435 6875621 := bbase (se 4 (by rfl) ⟨644589, by rfl⟩ : syracuseStep 6875621 = 1289179) (by norm_num)
theorem B4583747 : Blo 1907435 4583747 := bstep (se 1 (by rfl) ⟨3437810, by rfl⟩ : syracuseStep 4583747 = 6875621) B6875621
theorem B12223325 : Blo 1907435 12223325 := bstep (se 3 (by rfl) ⟨2291873, by rfl⟩ : syracuseStep 12223325 = 4583747) B4583747
theorem B8148883 : Blo 1907435 8148883 := bstep (se 1 (by rfl) ⟨6111662, by rfl⟩ : syracuseStep 8148883 = 12223325) B12223325
theorem B10865177 : Blo 1907435 10865177 := bstep (se 2 (by rfl) ⟨4074441, by rfl⟩ : syracuseStep 10865177 = 8148883) B8148883
theorem B7243451 : Blo 1907435 7243451 := bstep (se 1 (by rfl) ⟨5432588, by rfl⟩ : syracuseStep 7243451 = 10865177) B10865177
theorem B4828967 : Blo 1907435 4828967 := bstep (se 1 (by rfl) ⟨3621725, by rfl⟩ : syracuseStep 4828967 = 7243451) B7243451
theorem B3219311 : Blo 1907435 3219311 := bstep (se 1 (by rfl) ⟨2414483, by rfl⟩ : syracuseStep 3219311 = 4828967) B4828967
theorem B2146207 : Blo 1907435 2146207 := bstep (se 1 (by rfl) ⟨1609655, by rfl⟩ : syracuseStep 2146207 = 3219311) B3219311
theorem B2861609 : Blo 1907435 2861609 := bstep (se 2 (by rfl) ⟨1073103, by rfl⟩ : syracuseStep 2861609 = 2146207) B2146207
theorem B1907739 : Blo 1907435 1907739 := bstep (se 1 (by rfl) ⟨1430804, by rfl⟩ : syracuseStep 1907739 = 2861609) B2861609
theorem B12223349 : Blo 1907435 12223349 := bbase (se 5 (by rfl) ⟨572969, by rfl⟩ : syracuseStep 12223349 = 1145939) (by norm_num)
theorem B8148899 : Blo 1907435 8148899 := bstep (se 1 (by rfl) ⟨6111674, by rfl⟩ : syracuseStep 8148899 = 12223349) B12223349
theorem B5432599 : Blo 1907435 5432599 := bstep (se 1 (by rfl) ⟨4074449, by rfl⟩ : syracuseStep 5432599 = 8148899) B8148899
theorem B7243465 : Blo 1907435 7243465 := bstep (se 2 (by rfl) ⟨2716299, by rfl⟩ : syracuseStep 7243465 = 5432599) B5432599
theorem B9657953 : Blo 1907435 9657953 := bstep (se 2 (by rfl) ⟨3621732, by rfl⟩ : syracuseStep 9657953 = 7243465) B7243465
theorem B6438635 : Blo 1907435 6438635 := bstep (se 1 (by rfl) ⟨4828976, by rfl⟩ : syracuseStep 6438635 = 9657953) B9657953
theorem B4292423 : Blo 1907435 4292423 := bstep (se 1 (by rfl) ⟨3219317, by rfl⟩ : syracuseStep 4292423 = 6438635) B6438635
theorem B2861615 : Blo 1907435 2861615 := bstep (se 1 (by rfl) ⟨2146211, by rfl⟩ : syracuseStep 2861615 = 4292423) B4292423
theorem B1907743 : Blo 1907435 1907743 := bstep (se 1 (by rfl) ⟨1430807, by rfl⟩ : syracuseStep 1907743 = 2861615) B2861615
theorem B2861621 : Blo 1907435 2861621 := bbase (se 5 (by rfl) ⟨134138, by rfl⟩ : syracuseStep 2861621 = 268277) (by norm_num)
theorem B1907747 : Blo 1907435 1907747 := bstep (se 1 (by rfl) ⟨1430810, by rfl⟩ : syracuseStep 1907747 = 2861621) B2861621
theorem B4828997 : Blo 1907435 4828997 := bbase (se 4 (by rfl) ⟨452718, by rfl⟩ : syracuseStep 4828997 = 905437) (by norm_num)
theorem B3219331 : Blo 1907435 3219331 := bstep (se 1 (by rfl) ⟨2414498, by rfl⟩ : syracuseStep 3219331 = 4828997) B4828997
theorem B4292441 : Blo 1907435 4292441 := bstep (se 2 (by rfl) ⟨1609665, by rfl⟩ : syracuseStep 4292441 = 3219331) B3219331
theorem B2861627 : Blo 1907435 2861627 := bstep (se 1 (by rfl) ⟨2146220, by rfl⟩ : syracuseStep 2861627 = 4292441) B4292441
theorem B1907751 : Blo 1907435 1907751 := bstep (se 1 (by rfl) ⟨1430813, by rfl⟩ : syracuseStep 1907751 = 2861627) B2861627
theorem B2146225 : Blo 1907435 2146225 := bbase (se 2 (by rfl) ⟨804834, by rfl⟩ : syracuseStep 2146225 = 1609669) (by norm_num)
theorem B2861633 : Blo 1907435 2861633 := bstep (se 2 (by rfl) ⟨1073112, by rfl⟩ : syracuseStep 2861633 = 2146225) B2146225
theorem B1907755 : Blo 1907435 1907755 := bstep (se 1 (by rfl) ⟨1430816, by rfl⟩ : syracuseStep 1907755 = 2861633) B2861633
theorem B5432645 : Blo 1907435 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B3621763 : Blo 1907435 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B4829017 : Blo 1907435 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B6438689 : Blo 1907435 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B4292459 : Blo 1907435 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B2861639 : Blo 1907435 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B1907759 : Blo 1907435 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B2861645 : Blo 1907435 2861645 := bbase (se 3 (by rfl) ⟨536558, by rfl⟩ : syracuseStep 2861645 = 1073117) (by norm_num)
theorem B1907763 : Blo 1907435 1907763 := bstep (se 1 (by rfl) ⟨1430822, by rfl⟩ : syracuseStep 1907763 = 2861645) B2861645
theorem B4292477 : Blo 1907435 4292477 := bbase (se 3 (by rfl) ⟨804839, by rfl⟩ : syracuseStep 4292477 = 1609679) (by norm_num)
theorem B2861651 : Blo 1907435 2861651 := bstep (se 1 (by rfl) ⟨2146238, by rfl⟩ : syracuseStep 2861651 = 4292477) B4292477
theorem B1907767 : Blo 1907435 1907767 := bstep (se 1 (by rfl) ⟨1430825, by rfl⟩ : syracuseStep 1907767 = 2861651) B2861651
theorem B3219365 : Blo 1907435 3219365 := bbase (se 4 (by rfl) ⟨301815, by rfl⟩ : syracuseStep 3219365 = 603631) (by norm_num)
theorem B2146243 : Blo 1907435 2146243 := bstep (se 1 (by rfl) ⟨1609682, by rfl⟩ : syracuseStep 2146243 = 3219365) B3219365
theorem B2861657 : Blo 1907435 2861657 := bstep (se 2 (by rfl) ⟨1073121, by rfl⟩ : syracuseStep 2861657 = 2146243) B2146243
theorem B1907771 : Blo 1907435 1907771 := bstep (se 1 (by rfl) ⟨1430828, by rfl⟩ : syracuseStep 1907771 = 2861657) B2861657
theorem B2291917 : Blo 1907435 2291917 := bbase (se 3 (by rfl) ⟨429734, by rfl⟩ : syracuseStep 2291917 = 859469) (by norm_num)
theorem B3055889 : Blo 1907435 3055889 := bstep (se 2 (by rfl) ⟨1145958, by rfl⟩ : syracuseStep 3055889 = 2291917) B2291917
theorem B2037259 : Blo 1907435 2037259 := bstep (se 1 (by rfl) ⟨1527944, by rfl⟩ : syracuseStep 2037259 = 3055889) B3055889
theorem B2716345 : Blo 1907435 2716345 := bstep (se 2 (by rfl) ⟨1018629, by rfl⟩ : syracuseStep 2716345 = 2037259) B2037259
theorem B14487173 : Blo 1907435 14487173 := bstep (se 4 (by rfl) ⟨1358172, by rfl⟩ : syracuseStep 14487173 = 2716345) B2716345
theorem B9658115 : Blo 1907435 9658115 := bstep (se 1 (by rfl) ⟨7243586, by rfl⟩ : syracuseStep 9658115 = 14487173) B14487173
theorem B6438743 : Blo 1907435 6438743 := bstep (se 1 (by rfl) ⟨4829057, by rfl⟩ : syracuseStep 6438743 = 9658115) B9658115
theorem B4292495 : Blo 1907435 4292495 := bstep (se 1 (by rfl) ⟨3219371, by rfl⟩ : syracuseStep 4292495 = 6438743) B6438743
theorem B2861663 : Blo 1907435 2861663 := bstep (se 1 (by rfl) ⟨2146247, by rfl⟩ : syracuseStep 2861663 = 4292495) B4292495
theorem B1907775 : Blo 1907435 1907775 := bstep (se 1 (by rfl) ⟨1430831, by rfl⟩ : syracuseStep 1907775 = 2861663) B2861663
theorem B2861669 : Blo 1907435 2861669 := bbase (se 4 (by rfl) ⟨268281, by rfl⟩ : syracuseStep 2861669 = 536563) (by norm_num)
theorem B1907779 : Blo 1907435 1907779 := bstep (se 1 (by rfl) ⟨1430834, by rfl⟩ : syracuseStep 1907779 = 2861669) B2861669
theorem B2716357 : Blo 1907435 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B3621809 : Blo 1907435 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B2414539 : Blo 1907435 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B3219385 : Blo 1907435 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B4292513 : Blo 1907435 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B2861675 : Blo 1907435 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B1907783 : Blo 1907435 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B2146261 : Blo 1907435 2146261 := bbase (se 7 (by rfl) ⟨25151, by rfl⟩ : syracuseStep 2146261 = 50303) (by norm_num)
theorem B2861681 : Blo 1907435 2861681 := bstep (se 2 (by rfl) ⟨1073130, by rfl⟩ : syracuseStep 2861681 = 2146261) B2146261
theorem B1907787 : Blo 1907435 1907787 := bstep (se 1 (by rfl) ⟨1430840, by rfl⟩ : syracuseStep 1907787 = 2861681) B2861681
theorem B2414549 : Blo 1907435 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B6438797 : Blo 1907435 6438797 := bstep (se 3 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 6438797 = 2414549) B2414549
theorem B4292531 : Blo 1907435 4292531 := bstep (se 1 (by rfl) ⟨3219398, by rfl⟩ : syracuseStep 4292531 = 6438797) B6438797
theorem B2861687 : Blo 1907435 2861687 := bstep (se 1 (by rfl) ⟨2146265, by rfl⟩ : syracuseStep 2861687 = 4292531) B4292531
theorem B1907791 : Blo 1907435 1907791 := bstep (se 1 (by rfl) ⟨1430843, by rfl⟩ : syracuseStep 1907791 = 2861687) B2861687
theorem B2861693 : Blo 1907435 2861693 := bbase (se 3 (by rfl) ⟨536567, by rfl⟩ : syracuseStep 2861693 = 1073135) (by norm_num)
theorem B1907795 : Blo 1907435 1907795 := bstep (se 1 (by rfl) ⟨1430846, by rfl⟩ : syracuseStep 1907795 = 2861693) B2861693
theorem B4292549 : Blo 1907435 4292549 := bbase (se 4 (by rfl) ⟨402426, by rfl⟩ : syracuseStep 4292549 = 804853) (by norm_num)
theorem B2861699 : Blo 1907435 2861699 := bstep (se 1 (by rfl) ⟨2146274, by rfl⟩ : syracuseStep 2861699 = 4292549) B4292549
theorem B1907799 : Blo 1907435 1907799 := bstep (se 1 (by rfl) ⟨1430849, by rfl⟩ : syracuseStep 1907799 = 2861699) B2861699
theorem B8149157 : Blo 1907435 8149157 := bbase (se 4 (by rfl) ⟨763983, by rfl⟩ : syracuseStep 8149157 = 1527967) (by norm_num)
theorem B5432771 : Blo 1907435 5432771 := bstep (se 1 (by rfl) ⟨4074578, by rfl⟩ : syracuseStep 5432771 = 8149157) B8149157
theorem B3621847 : Blo 1907435 3621847 := bstep (se 1 (by rfl) ⟨2716385, by rfl⟩ : syracuseStep 3621847 = 5432771) B5432771
theorem B4829129 : Blo 1907435 4829129 := bstep (se 2 (by rfl) ⟨1810923, by rfl⟩ : syracuseStep 4829129 = 3621847) B3621847
theorem B3219419 : Blo 1907435 3219419 := bstep (se 1 (by rfl) ⟨2414564, by rfl⟩ : syracuseStep 3219419 = 4829129) B4829129
theorem B2146279 : Blo 1907435 2146279 := bstep (se 1 (by rfl) ⟨1609709, by rfl⟩ : syracuseStep 2146279 = 3219419) B3219419
theorem B2861705 : Blo 1907435 2861705 := bstep (se 2 (by rfl) ⟨1073139, by rfl⟩ : syracuseStep 2861705 = 2146279) B2146279
theorem B1907803 : Blo 1907435 1907803 := bstep (se 1 (by rfl) ⟨1430852, by rfl⟩ : syracuseStep 1907803 = 2861705) B2861705
theorem B9658277 : Blo 1907435 9658277 := bbase (se 4 (by rfl) ⟨905463, by rfl⟩ : syracuseStep 9658277 = 1810927) (by norm_num)
theorem B6438851 : Blo 1907435 6438851 := bstep (se 1 (by rfl) ⟨4829138, by rfl⟩ : syracuseStep 6438851 = 9658277) B9658277
theorem B4292567 : Blo 1907435 4292567 := bstep (se 1 (by rfl) ⟨3219425, by rfl⟩ : syracuseStep 4292567 = 6438851) B6438851
theorem B2861711 : Blo 1907435 2861711 := bstep (se 1 (by rfl) ⟨2146283, by rfl⟩ : syracuseStep 2861711 = 4292567) B4292567
theorem B1907807 : Blo 1907435 1907807 := bstep (se 1 (by rfl) ⟨1430855, by rfl⟩ : syracuseStep 1907807 = 2861711) B2861711
theorem B2861717 : Blo 1907435 2861717 := bbase (se 6 (by rfl) ⟨67071, by rfl⟩ : syracuseStep 2861717 = 134143) (by norm_num)
theorem B1907811 : Blo 1907435 1907811 := bstep (se 1 (by rfl) ⟨1430858, by rfl⟩ : syracuseStep 1907811 = 2861717) B2861717
theorem B3263365 : Blo 1907435 3263365 := bbase (se 4 (by rfl) ⟨305940, by rfl⟩ : syracuseStep 3263365 = 611881) (by norm_num)
theorem B4351153 : Blo 1907435 4351153 := bstep (se 2 (by rfl) ⟨1631682, by rfl⟩ : syracuseStep 4351153 = 3263365) B3263365
theorem B5801537 : Blo 1907435 5801537 := bstep (se 2 (by rfl) ⟨2175576, by rfl⟩ : syracuseStep 5801537 = 4351153) B4351153
theorem B3867691 : Blo 1907435 3867691 := bstep (se 1 (by rfl) ⟨2900768, by rfl⟩ : syracuseStep 3867691 = 5801537) B5801537
theorem B5156921 : Blo 1907435 5156921 := bstep (se 2 (by rfl) ⟨1933845, by rfl⟩ : syracuseStep 5156921 = 3867691) B3867691
theorem B3437947 : Blo 1907435 3437947 := bstep (se 1 (by rfl) ⟨2578460, by rfl⟩ : syracuseStep 3437947 = 5156921) B5156921
theorem B18335717 : Blo 1907435 18335717 := bstep (se 4 (by rfl) ⟨1718973, by rfl⟩ : syracuseStep 18335717 = 3437947) B3437947
theorem B12223811 : Blo 1907435 12223811 := bstep (se 1 (by rfl) ⟨9167858, by rfl⟩ : syracuseStep 12223811 = 18335717) B18335717
theorem B8149207 : Blo 1907435 8149207 := bstep (se 1 (by rfl) ⟨6111905, by rfl⟩ : syracuseStep 8149207 = 12223811) B12223811
theorem B10865609 : Blo 1907435 10865609 := bstep (se 2 (by rfl) ⟨4074603, by rfl⟩ : syracuseStep 10865609 = 8149207) B8149207
theorem B7243739 : Blo 1907435 7243739 := bstep (se 1 (by rfl) ⟨5432804, by rfl⟩ : syracuseStep 7243739 = 10865609) B10865609
theorem B4829159 : Blo 1907435 4829159 := bstep (se 1 (by rfl) ⟨3621869, by rfl⟩ : syracuseStep 4829159 = 7243739) B7243739
theorem B3219439 : Blo 1907435 3219439 := bstep (se 1 (by rfl) ⟨2414579, by rfl⟩ : syracuseStep 3219439 = 4829159) B4829159
theorem B4292585 : Blo 1907435 4292585 := bstep (se 2 (by rfl) ⟨1609719, by rfl⟩ : syracuseStep 4292585 = 3219439) B3219439
theorem B2861723 : Blo 1907435 2861723 := bstep (se 1 (by rfl) ⟨2146292, by rfl⟩ : syracuseStep 2861723 = 4292585) B4292585
theorem B1907815 : Blo 1907435 1907815 := bstep (se 1 (by rfl) ⟨1430861, by rfl⟩ : syracuseStep 1907815 = 2861723) B2861723
theorem B2146297 : Blo 1907435 2146297 := bbase (se 2 (by rfl) ⟨804861, by rfl⟩ : syracuseStep 2146297 = 1609723) (by norm_num)
theorem B2861729 : Blo 1907435 2861729 := bstep (se 2 (by rfl) ⟨1073148, by rfl⟩ : syracuseStep 2861729 = 2146297) B2146297
theorem B1907819 : Blo 1907435 1907819 := bstep (se 1 (by rfl) ⟨1430864, by rfl⟩ : syracuseStep 1907819 = 2861729) B2861729
theorem B6526757 : Blo 1907435 6526757 := bbase (se 4 (by rfl) ⟨611883, by rfl⟩ : syracuseStep 6526757 = 1223767) (by norm_num)
theorem B4351171 : Blo 1907435 4351171 := bstep (se 1 (by rfl) ⟨3263378, by rfl⟩ : syracuseStep 4351171 = 6526757) B6526757
theorem B5801561 : Blo 1907435 5801561 := bstep (se 2 (by rfl) ⟨2175585, by rfl⟩ : syracuseStep 5801561 = 4351171) B4351171
theorem B3867707 : Blo 1907435 3867707 := bstep (se 1 (by rfl) ⟨2900780, by rfl⟩ : syracuseStep 3867707 = 5801561) B5801561
theorem B10313885 : Blo 1907435 10313885 := bstep (se 3 (by rfl) ⟨1933853, by rfl⟩ : syracuseStep 10313885 = 3867707) B3867707
theorem B6875923 : Blo 1907435 6875923 := bstep (se 1 (by rfl) ⟨5156942, by rfl⟩ : syracuseStep 6875923 = 10313885) B10313885
theorem B9167897 : Blo 1907435 9167897 := bstep (se 2 (by rfl) ⟨3437961, by rfl⟩ : syracuseStep 9167897 = 6875923) B6875923
theorem B6111931 : Blo 1907435 6111931 := bstep (se 1 (by rfl) ⟨4583948, by rfl⟩ : syracuseStep 6111931 = 9167897) B9167897
theorem B8149241 : Blo 1907435 8149241 := bstep (se 2 (by rfl) ⟨3055965, by rfl⟩ : syracuseStep 8149241 = 6111931) B6111931
theorem B5432827 : Blo 1907435 5432827 := bstep (se 1 (by rfl) ⟨4074620, by rfl⟩ : syracuseStep 5432827 = 8149241) B8149241
theorem B7243769 : Blo 1907435 7243769 := bstep (se 2 (by rfl) ⟨2716413, by rfl⟩ : syracuseStep 7243769 = 5432827) B5432827
theorem B4829179 : Blo 1907435 4829179 := bstep (se 1 (by rfl) ⟨3621884, by rfl⟩ : syracuseStep 4829179 = 7243769) B7243769
theorem B6438905 : Blo 1907435 6438905 := bstep (se 2 (by rfl) ⟨2414589, by rfl⟩ : syracuseStep 6438905 = 4829179) B4829179
theorem B4292603 : Blo 1907435 4292603 := bstep (se 1 (by rfl) ⟨3219452, by rfl⟩ : syracuseStep 4292603 = 6438905) B6438905
theorem B2861735 : Blo 1907435 2861735 := bstep (se 1 (by rfl) ⟨2146301, by rfl⟩ : syracuseStep 2861735 = 4292603) B4292603
theorem B1907823 : Blo 1907435 1907823 := bstep (se 1 (by rfl) ⟨1430867, by rfl⟩ : syracuseStep 1907823 = 2861735) B2861735
theorem B2861741 : Blo 1907435 2861741 := bbase (se 3 (by rfl) ⟨536576, by rfl⟩ : syracuseStep 2861741 = 1073153) (by norm_num)
theorem B1907827 : Blo 1907435 1907827 := bstep (se 1 (by rfl) ⟨1430870, by rfl⟩ : syracuseStep 1907827 = 2861741) B2861741
theorem B4292621 : Blo 1907435 4292621 := bbase (se 3 (by rfl) ⟨804866, by rfl⟩ : syracuseStep 4292621 = 1609733) (by norm_num)
theorem B2861747 : Blo 1907435 2861747 := bstep (se 1 (by rfl) ⟨2146310, by rfl⟩ : syracuseStep 2861747 = 4292621) B4292621
theorem B1907831 : Blo 1907435 1907831 := bstep (se 1 (by rfl) ⟨1430873, by rfl⟩ : syracuseStep 1907831 = 2861747) B2861747
theorem B2414605 : Blo 1907435 2414605 := bbase (se 3 (by rfl) ⟨452738, by rfl⟩ : syracuseStep 2414605 = 905477) (by norm_num)
theorem B3219473 : Blo 1907435 3219473 := bstep (se 2 (by rfl) ⟨1207302, by rfl⟩ : syracuseStep 3219473 = 2414605) B2414605
theorem B2146315 : Blo 1907435 2146315 := bstep (se 1 (by rfl) ⟨1609736, by rfl⟩ : syracuseStep 2146315 = 3219473) B3219473
theorem B2861753 : Blo 1907435 2861753 := bstep (se 2 (by rfl) ⟨1073157, by rfl⟩ : syracuseStep 2861753 = 2146315) B2146315
theorem B1907835 : Blo 1907435 1907835 := bstep (se 1 (by rfl) ⟨1430876, by rfl⟩ : syracuseStep 1907835 = 2861753) B2861753
theorem B30941909 : Blo 1907435 30941909 := bbase (se 7 (by rfl) ⟨362600, by rfl⟩ : syracuseStep 30941909 = 725201) (by norm_num)
theorem B20627939 : Blo 1907435 20627939 := bstep (se 1 (by rfl) ⟨15470954, by rfl⟩ : syracuseStep 20627939 = 30941909) B30941909
theorem B13751959 : Blo 1907435 13751959 := bstep (se 1 (by rfl) ⟨10313969, by rfl⟩ : syracuseStep 13751959 = 20627939) B20627939
theorem B18335945 : Blo 1907435 18335945 := bstep (se 2 (by rfl) ⟨6875979, by rfl⟩ : syracuseStep 18335945 = 13751959) B13751959
theorem B12223963 : Blo 1907435 12223963 := bstep (se 1 (by rfl) ⟨9167972, by rfl⟩ : syracuseStep 12223963 = 18335945) B18335945
theorem B16298617 : Blo 1907435 16298617 := bstep (se 2 (by rfl) ⟨6111981, by rfl⟩ : syracuseStep 16298617 = 12223963) B12223963
theorem B21731489 : Blo 1907435 21731489 := bstep (se 2 (by rfl) ⟨8149308, by rfl⟩ : syracuseStep 21731489 = 16298617) B16298617
theorem B14487659 : Blo 1907435 14487659 := bstep (se 1 (by rfl) ⟨10865744, by rfl⟩ : syracuseStep 14487659 = 21731489) B21731489
theorem B9658439 : Blo 1907435 9658439 := bstep (se 1 (by rfl) ⟨7243829, by rfl⟩ : syracuseStep 9658439 = 14487659) B14487659
theorem B6438959 : Blo 1907435 6438959 := bstep (se 1 (by rfl) ⟨4829219, by rfl⟩ : syracuseStep 6438959 = 9658439) B9658439
theorem B4292639 : Blo 1907435 4292639 := bstep (se 1 (by rfl) ⟨3219479, by rfl⟩ : syracuseStep 4292639 = 6438959) B6438959
theorem B2861759 : Blo 1907435 2861759 := bstep (se 1 (by rfl) ⟨2146319, by rfl⟩ : syracuseStep 2861759 = 4292639) B4292639
theorem B1907839 : Blo 1907435 1907839 := bstep (se 1 (by rfl) ⟨1430879, by rfl⟩ : syracuseStep 1907839 = 2861759) B2861759
theorem B2861765 : Blo 1907435 2861765 := bbase (se 4 (by rfl) ⟨268290, by rfl⟩ : syracuseStep 2861765 = 536581) (by norm_num)
theorem B1907843 : Blo 1907435 1907843 := bstep (se 1 (by rfl) ⟨1430882, by rfl⟩ : syracuseStep 1907843 = 2861765) B2861765
theorem B3219493 : Blo 1907435 3219493 := bbase (se 4 (by rfl) ⟨301827, by rfl⟩ : syracuseStep 3219493 = 603655) (by norm_num)
theorem B4292657 : Blo 1907435 4292657 := bstep (se 2 (by rfl) ⟨1609746, by rfl⟩ : syracuseStep 4292657 = 3219493) B3219493
theorem B2861771 : Blo 1907435 2861771 := bstep (se 1 (by rfl) ⟨2146328, by rfl⟩ : syracuseStep 2861771 = 4292657) B4292657
theorem B1907847 : Blo 1907435 1907847 := bstep (se 1 (by rfl) ⟨1430885, by rfl⟩ : syracuseStep 1907847 = 2861771) B2861771
theorem B2146333 : Blo 1907435 2146333 := bbase (se 3 (by rfl) ⟨402437, by rfl⟩ : syracuseStep 2146333 = 804875) (by norm_num)
theorem B2861777 : Blo 1907435 2861777 := bstep (se 2 (by rfl) ⟨1073166, by rfl⟩ : syracuseStep 2861777 = 2146333) B2146333
theorem B1907851 : Blo 1907435 1907851 := bstep (se 1 (by rfl) ⟨1430888, by rfl⟩ : syracuseStep 1907851 = 2861777) B2861777
theorem B6439013 : Blo 1907435 6439013 := bbase (se 4 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 6439013 = 1207315) (by norm_num)
theorem B4292675 : Blo 1907435 4292675 := bstep (se 1 (by rfl) ⟨3219506, by rfl⟩ : syracuseStep 4292675 = 6439013) B6439013
theorem B2861783 : Blo 1907435 2861783 := bstep (se 1 (by rfl) ⟨2146337, by rfl⟩ : syracuseStep 2861783 = 4292675) B4292675
theorem B1907855 : Blo 1907435 1907855 := bstep (se 1 (by rfl) ⟨1430891, by rfl⟩ : syracuseStep 1907855 = 2861783) B2861783
theorem B2861789 : Blo 1907435 2861789 := bbase (se 3 (by rfl) ⟨536585, by rfl⟩ : syracuseStep 2861789 = 1073171) (by norm_num)
theorem B1907859 : Blo 1907435 1907859 := bstep (se 1 (by rfl) ⟨1430894, by rfl⟩ : syracuseStep 1907859 = 2861789) B2861789
theorem B4292693 : Blo 1907435 4292693 := bbase (se 8 (by rfl) ⟨25152, by rfl⟩ : syracuseStep 4292693 = 50305) (by norm_num)
theorem B2861795 : Blo 1907435 2861795 := bstep (se 1 (by rfl) ⟨2146346, by rfl⟩ : syracuseStep 2861795 = 4292693) B4292693
theorem B1907863 : Blo 1907435 1907863 := bstep (se 1 (by rfl) ⟨1430897, by rfl⟩ : syracuseStep 1907863 = 2861795) B2861795
theorem B3867797 : Blo 1907435 3867797 := bbase (se 6 (by rfl) ⟨90651, by rfl⟩ : syracuseStep 3867797 = 181303) (by norm_num)
theorem B10314125 : Blo 1907435 10314125 := bstep (se 3 (by rfl) ⟨1933898, by rfl⟩ : syracuseStep 10314125 = 3867797) B3867797
theorem B6876083 : Blo 1907435 6876083 := bstep (se 1 (by rfl) ⟨5157062, by rfl⟩ : syracuseStep 6876083 = 10314125) B10314125
theorem B4584055 : Blo 1907435 4584055 := bstep (se 1 (by rfl) ⟨3438041, by rfl⟩ : syracuseStep 4584055 = 6876083) B6876083
theorem B6112073 : Blo 1907435 6112073 := bstep (se 2 (by rfl) ⟨2292027, by rfl⟩ : syracuseStep 6112073 = 4584055) B4584055
theorem B4074715 : Blo 1907435 4074715 := bstep (se 1 (by rfl) ⟨3056036, by rfl⟩ : syracuseStep 4074715 = 6112073) B6112073
theorem B5432953 : Blo 1907435 5432953 := bstep (se 2 (by rfl) ⟨2037357, by rfl⟩ : syracuseStep 5432953 = 4074715) B4074715
theorem B7243937 : Blo 1907435 7243937 := bstep (se 2 (by rfl) ⟨2716476, by rfl⟩ : syracuseStep 7243937 = 5432953) B5432953
theorem B4829291 : Blo 1907435 4829291 := bstep (se 1 (by rfl) ⟨3621968, by rfl⟩ : syracuseStep 4829291 = 7243937) B7243937
theorem B3219527 : Blo 1907435 3219527 := bstep (se 1 (by rfl) ⟨2414645, by rfl⟩ : syracuseStep 3219527 = 4829291) B4829291
theorem B2146351 : Blo 1907435 2146351 := bstep (se 1 (by rfl) ⟨1609763, by rfl⟩ : syracuseStep 2146351 = 3219527) B3219527
theorem B2861801 : Blo 1907435 2861801 := bstep (se 2 (by rfl) ⟨1073175, by rfl⟩ : syracuseStep 2861801 = 2146351) B2146351
theorem B1907867 : Blo 1907435 1907867 := bstep (se 1 (by rfl) ⟨1430900, by rfl⟩ : syracuseStep 1907867 = 2861801) B2861801
theorem B7442965 : Blo 1907435 7442965 := bbase (se 6 (by rfl) ⟨174444, by rfl⟩ : syracuseStep 7442965 = 348889) (by norm_num)
theorem B9923953 : Blo 1907435 9923953 := bstep (se 2 (by rfl) ⟨3721482, by rfl⟩ : syracuseStep 9923953 = 7442965) B7442965
theorem B13231937 : Blo 1907435 13231937 := bstep (se 2 (by rfl) ⟨4961976, by rfl⟩ : syracuseStep 13231937 = 9923953) B9923953
theorem B35285165 : Blo 1907435 35285165 := bstep (se 3 (by rfl) ⟨6615968, by rfl⟩ : syracuseStep 35285165 = 13231937) B13231937
theorem B23523443 : Blo 1907435 23523443 := bstep (se 1 (by rfl) ⟨17642582, by rfl⟩ : syracuseStep 23523443 = 35285165) B35285165
theorem B15682295 : Blo 1907435 15682295 := bstep (se 1 (by rfl) ⟨11761721, by rfl⟩ : syracuseStep 15682295 = 23523443) B23523443
theorem B41819453 : Blo 1907435 41819453 := bstep (se 3 (by rfl) ⟨7841147, by rfl⟩ : syracuseStep 41819453 = 15682295) B15682295
theorem B27879635 : Blo 1907435 27879635 := bstep (se 1 (by rfl) ⟨20909726, by rfl⟩ : syracuseStep 27879635 = 41819453) B41819453
theorem B18586423 : Blo 1907435 18586423 := bstep (se 1 (by rfl) ⟨13939817, by rfl⟩ : syracuseStep 18586423 = 27879635) B27879635
theorem B24781897 : Blo 1907435 24781897 := bstep (se 2 (by rfl) ⟨9293211, by rfl⟩ : syracuseStep 24781897 = 18586423) B18586423
theorem B33042529 : Blo 1907435 33042529 := bstep (se 2 (by rfl) ⟨12390948, by rfl⟩ : syracuseStep 33042529 = 24781897) B24781897
theorem B44056705 : Blo 1907435 44056705 := bstep (se 2 (by rfl) ⟨16521264, by rfl⟩ : syracuseStep 44056705 = 33042529) B33042529
theorem B58742273 : Blo 1907435 58742273 := bstep (se 2 (by rfl) ⟨22028352, by rfl⟩ : syracuseStep 58742273 = 44056705) B44056705
theorem B39161515 : Blo 1907435 39161515 := bstep (se 1 (by rfl) ⟨29371136, by rfl⟩ : syracuseStep 39161515 = 58742273) B58742273
theorem B52215353 : Blo 1907435 52215353 := bstep (se 2 (by rfl) ⟨19580757, by rfl⟩ : syracuseStep 52215353 = 39161515) B39161515
theorem B34810235 : Blo 1907435 34810235 := bstep (se 1 (by rfl) ⟨26107676, by rfl⟩ : syracuseStep 34810235 = 52215353) B52215353
theorem B23206823 : Blo 1907435 23206823 := bstep (se 1 (by rfl) ⟨17405117, by rfl⟩ : syracuseStep 23206823 = 34810235) B34810235
theorem B15471215 : Blo 1907435 15471215 := bstep (se 1 (by rfl) ⟨11603411, by rfl⟩ : syracuseStep 15471215 = 23206823) B23206823
theorem B10314143 : Blo 1907435 10314143 := bstep (se 1 (by rfl) ⟨7735607, by rfl⟩ : syracuseStep 10314143 = 15471215) B15471215
theorem B6876095 : Blo 1907435 6876095 := bstep (se 1 (by rfl) ⟨5157071, by rfl⟩ : syracuseStep 6876095 = 10314143) B10314143
theorem B18336253 : Blo 1907435 18336253 := bstep (se 3 (by rfl) ⟨3438047, by rfl⟩ : syracuseStep 18336253 = 6876095) B6876095
theorem B24448337 : Blo 1907435 24448337 := bstep (se 2 (by rfl) ⟨9168126, by rfl⟩ : syracuseStep 24448337 = 18336253) B18336253
theorem B16298891 : Blo 1907435 16298891 := bstep (se 1 (by rfl) ⟨12224168, by rfl⟩ : syracuseStep 16298891 = 24448337) B24448337
theorem B10865927 : Blo 1907435 10865927 := bstep (se 1 (by rfl) ⟨8149445, by rfl⟩ : syracuseStep 10865927 = 16298891) B16298891
theorem B7243951 : Blo 1907435 7243951 := bstep (se 1 (by rfl) ⟨5432963, by rfl⟩ : syracuseStep 7243951 = 10865927) B10865927
theorem B9658601 : Blo 1907435 9658601 := bstep (se 2 (by rfl) ⟨3621975, by rfl⟩ : syracuseStep 9658601 = 7243951) B7243951
theorem B6439067 : Blo 1907435 6439067 := bstep (se 1 (by rfl) ⟨4829300, by rfl⟩ : syracuseStep 6439067 = 9658601) B9658601
theorem B4292711 : Blo 1907435 4292711 := bstep (se 1 (by rfl) ⟨3219533, by rfl⟩ : syracuseStep 4292711 = 6439067) B6439067
theorem B2861807 : Blo 1907435 2861807 := bstep (se 1 (by rfl) ⟨2146355, by rfl⟩ : syracuseStep 2861807 = 4292711) B4292711
theorem B1907871 : Blo 1907435 1907871 := bstep (se 1 (by rfl) ⟨1430903, by rfl⟩ : syracuseStep 1907871 = 2861807) B2861807
theorem B2861813 : Blo 1907435 2861813 := bbase (se 5 (by rfl) ⟨134147, by rfl⟩ : syracuseStep 2861813 = 268295) (by norm_num)
theorem B1907875 : Blo 1907435 1907875 := bstep (se 1 (by rfl) ⟨1430906, by rfl⟩ : syracuseStep 1907875 = 2861813) B2861813
theorem B8702597 : Blo 1907435 8702597 := bbase (se 4 (by rfl) ⟨815868, by rfl⟩ : syracuseStep 8702597 = 1631737) (by norm_num)
theorem B23206925 : Blo 1907435 23206925 := bstep (se 3 (by rfl) ⟨4351298, by rfl⟩ : syracuseStep 23206925 = 8702597) B8702597
theorem B15471283 : Blo 1907435 15471283 := bstep (se 1 (by rfl) ⟨11603462, by rfl⟩ : syracuseStep 15471283 = 23206925) B23206925
theorem B20628377 : Blo 1907435 20628377 := bstep (se 2 (by rfl) ⟨7735641, by rfl⟩ : syracuseStep 20628377 = 15471283) B15471283
theorem B13752251 : Blo 1907435 13752251 := bstep (se 1 (by rfl) ⟨10314188, by rfl⟩ : syracuseStep 13752251 = 20628377) B20628377
theorem B9168167 : Blo 1907435 9168167 := bstep (se 1 (by rfl) ⟨6876125, by rfl⟩ : syracuseStep 9168167 = 13752251) B13752251
theorem B6112111 : Blo 1907435 6112111 := bstep (se 1 (by rfl) ⟨4584083, by rfl⟩ : syracuseStep 6112111 = 9168167) B9168167
theorem B8149481 : Blo 1907435 8149481 := bstep (se 2 (by rfl) ⟨3056055, by rfl⟩ : syracuseStep 8149481 = 6112111) B6112111
theorem B5432987 : Blo 1907435 5432987 := bstep (se 1 (by rfl) ⟨4074740, by rfl⟩ : syracuseStep 5432987 = 8149481) B8149481
theorem B3621991 : Blo 1907435 3621991 := bstep (se 1 (by rfl) ⟨2716493, by rfl⟩ : syracuseStep 3621991 = 5432987) B5432987
theorem B4829321 : Blo 1907435 4829321 := bstep (se 2 (by rfl) ⟨1810995, by rfl⟩ : syracuseStep 4829321 = 3621991) B3621991
theorem B3219547 : Blo 1907435 3219547 := bstep (se 1 (by rfl) ⟨2414660, by rfl⟩ : syracuseStep 3219547 = 4829321) B4829321
theorem B4292729 : Blo 1907435 4292729 := bstep (se 2 (by rfl) ⟨1609773, by rfl⟩ : syracuseStep 4292729 = 3219547) B3219547
theorem B2861819 : Blo 1907435 2861819 := bstep (se 1 (by rfl) ⟨2146364, by rfl⟩ : syracuseStep 2861819 = 4292729) B4292729
theorem B1907879 : Blo 1907435 1907879 := bstep (se 1 (by rfl) ⟨1430909, by rfl⟩ : syracuseStep 1907879 = 2861819) B2861819
theorem B2146369 : Blo 1907435 2146369 := bbase (se 2 (by rfl) ⟨804888, by rfl⟩ : syracuseStep 2146369 = 1609777) (by norm_num)
theorem B2861825 : Blo 1907435 2861825 := bstep (se 2 (by rfl) ⟨1073184, by rfl⟩ : syracuseStep 2861825 = 2146369) B2146369
theorem B1907883 : Blo 1907435 1907883 := bstep (se 1 (by rfl) ⟨1430912, by rfl⟩ : syracuseStep 1907883 = 2861825) B2861825
theorem B4829341 : Blo 1907435 4829341 := bbase (se 3 (by rfl) ⟨905501, by rfl⟩ : syracuseStep 4829341 = 1811003) (by norm_num)
theorem B6439121 : Blo 1907435 6439121 := bstep (se 2 (by rfl) ⟨2414670, by rfl⟩ : syracuseStep 6439121 = 4829341) B4829341
theorem B4292747 : Blo 1907435 4292747 := bstep (se 1 (by rfl) ⟨3219560, by rfl⟩ : syracuseStep 4292747 = 6439121) B6439121
theorem B2861831 : Blo 1907435 2861831 := bstep (se 1 (by rfl) ⟨2146373, by rfl⟩ : syracuseStep 2861831 = 4292747) B4292747
theorem B1907887 : Blo 1907435 1907887 := bstep (se 1 (by rfl) ⟨1430915, by rfl⟩ : syracuseStep 1907887 = 2861831) B2861831
theorem B2861837 : Blo 1907435 2861837 := bbase (se 3 (by rfl) ⟨536594, by rfl⟩ : syracuseStep 2861837 = 1073189) (by norm_num)
theorem B1907891 : Blo 1907435 1907891 := bstep (se 1 (by rfl) ⟨1430918, by rfl⟩ : syracuseStep 1907891 = 2861837) B2861837
theorem B4292765 : Blo 1907435 4292765 := bbase (se 3 (by rfl) ⟨804893, by rfl⟩ : syracuseStep 4292765 = 1609787) (by norm_num)
theorem B2861843 : Blo 1907435 2861843 := bstep (se 1 (by rfl) ⟨2146382, by rfl⟩ : syracuseStep 2861843 = 4292765) B4292765
theorem B1907895 : Blo 1907435 1907895 := bstep (se 1 (by rfl) ⟨1430921, by rfl⟩ : syracuseStep 1907895 = 2861843) B2861843
theorem B3219581 : Blo 1907435 3219581 := bbase (se 3 (by rfl) ⟨603671, by rfl⟩ : syracuseStep 3219581 = 1207343) (by norm_num)
theorem B2146387 : Blo 1907435 2146387 := bstep (se 1 (by rfl) ⟨1609790, by rfl⟩ : syracuseStep 2146387 = 3219581) B3219581
theorem B2861849 : Blo 1907435 2861849 := bstep (se 2 (by rfl) ⟨1073193, by rfl⟩ : syracuseStep 2861849 = 2146387) B2146387
theorem B1907899 : Blo 1907435 1907899 := bstep (se 1 (by rfl) ⟨1430924, by rfl⟩ : syracuseStep 1907899 = 2861849) B2861849
theorem B3867869 : Blo 1907435 3867869 := bbase (se 3 (by rfl) ⟨725225, by rfl⟩ : syracuseStep 3867869 = 1450451) (by norm_num)
theorem B10314317 : Blo 1907435 10314317 := bstep (se 3 (by rfl) ⟨1933934, by rfl⟩ : syracuseStep 10314317 = 3867869) B3867869
theorem B6876211 : Blo 1907435 6876211 := bstep (se 1 (by rfl) ⟨5157158, by rfl⟩ : syracuseStep 6876211 = 10314317) B10314317
theorem B9168281 : Blo 1907435 9168281 := bstep (se 2 (by rfl) ⟨3438105, by rfl⟩ : syracuseStep 9168281 = 6876211) B6876211
theorem B6112187 : Blo 1907435 6112187 := bstep (se 1 (by rfl) ⟨4584140, by rfl⟩ : syracuseStep 6112187 = 9168281) B9168281
theorem B4074791 : Blo 1907435 4074791 := bstep (se 1 (by rfl) ⟨3056093, by rfl⟩ : syracuseStep 4074791 = 6112187) B6112187
theorem B10866109 : Blo 1907435 10866109 := bstep (se 3 (by rfl) ⟨2037395, by rfl⟩ : syracuseStep 10866109 = 4074791) B4074791
theorem B14488145 : Blo 1907435 14488145 := bstep (se 2 (by rfl) ⟨5433054, by rfl⟩ : syracuseStep 14488145 = 10866109) B10866109
theorem B9658763 : Blo 1907435 9658763 := bstep (se 1 (by rfl) ⟨7244072, by rfl⟩ : syracuseStep 9658763 = 14488145) B14488145
theorem B6439175 : Blo 1907435 6439175 := bstep (se 1 (by rfl) ⟨4829381, by rfl⟩ : syracuseStep 6439175 = 9658763) B9658763
theorem B4292783 : Blo 1907435 4292783 := bstep (se 1 (by rfl) ⟨3219587, by rfl⟩ : syracuseStep 4292783 = 6439175) B6439175
theorem B2861855 : Blo 1907435 2861855 := bstep (se 1 (by rfl) ⟨2146391, by rfl⟩ : syracuseStep 2861855 = 4292783) B4292783
theorem B1907903 : Blo 1907435 1907903 := bstep (se 1 (by rfl) ⟨1430927, by rfl⟩ : syracuseStep 1907903 = 2861855) B2861855
theorem B2861861 : Blo 1907435 2861861 := bbase (se 4 (by rfl) ⟨268299, by rfl⟩ : syracuseStep 2861861 = 536599) (by norm_num)
theorem B1907907 : Blo 1907435 1907907 := bstep (se 1 (by rfl) ⟨1430930, by rfl⟩ : syracuseStep 1907907 = 2861861) B2861861
theorem B2414701 : Blo 1907435 2414701 := bbase (se 3 (by rfl) ⟨452756, by rfl⟩ : syracuseStep 2414701 = 905513) (by norm_num)
theorem B3219601 : Blo 1907435 3219601 := bstep (se 2 (by rfl) ⟨1207350, by rfl⟩ : syracuseStep 3219601 = 2414701) B2414701
theorem B4292801 : Blo 1907435 4292801 := bstep (se 2 (by rfl) ⟨1609800, by rfl⟩ : syracuseStep 4292801 = 3219601) B3219601
theorem B2861867 : Blo 1907435 2861867 := bstep (se 1 (by rfl) ⟨2146400, by rfl⟩ : syracuseStep 2861867 = 4292801) B4292801
theorem B1907911 : Blo 1907435 1907911 := bstep (se 1 (by rfl) ⟨1430933, by rfl⟩ : syracuseStep 1907911 = 2861867) B2861867
theorem B2146405 : Blo 1907435 2146405 := bbase (se 4 (by rfl) ⟨201225, by rfl⟩ : syracuseStep 2146405 = 402451) (by norm_num)
theorem B2861873 : Blo 1907435 2861873 := bstep (se 2 (by rfl) ⟨1073202, by rfl⟩ : syracuseStep 2861873 = 2146405) B2146405
theorem B1907915 : Blo 1907435 1907915 := bstep (se 1 (by rfl) ⟨1430936, by rfl⟩ : syracuseStep 1907915 = 2861873) B2861873
theorem B2037413 : Blo 1907435 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B5433101 : Blo 1907435 5433101 := bstep (se 3 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 5433101 = 2037413) B2037413
theorem B3622067 : Blo 1907435 3622067 := bstep (se 1 (by rfl) ⟨2716550, by rfl⟩ : syracuseStep 3622067 = 5433101) B5433101
theorem B2414711 : Blo 1907435 2414711 := bstep (se 1 (by rfl) ⟨1811033, by rfl⟩ : syracuseStep 2414711 = 3622067) B3622067
theorem B6439229 : Blo 1907435 6439229 := bstep (se 3 (by rfl) ⟨1207355, by rfl⟩ : syracuseStep 6439229 = 2414711) B2414711
theorem B4292819 : Blo 1907435 4292819 := bstep (se 1 (by rfl) ⟨3219614, by rfl⟩ : syracuseStep 4292819 = 6439229) B6439229
theorem B2861879 : Blo 1907435 2861879 := bstep (se 1 (by rfl) ⟨2146409, by rfl⟩ : syracuseStep 2861879 = 4292819) B4292819
theorem B1907919 : Blo 1907435 1907919 := bstep (se 1 (by rfl) ⟨1430939, by rfl⟩ : syracuseStep 1907919 = 2861879) B2861879
theorem B2861885 : Blo 1907435 2861885 := bbase (se 3 (by rfl) ⟨536603, by rfl⟩ : syracuseStep 2861885 = 1073207) (by norm_num)
theorem B1907923 : Blo 1907435 1907923 := bstep (se 1 (by rfl) ⟨1430942, by rfl⟩ : syracuseStep 1907923 = 2861885) B2861885
theorem B4292837 : Blo 1907435 4292837 := bbase (se 4 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 4292837 = 804907) (by norm_num)
theorem B2861891 : Blo 1907435 2861891 := bstep (se 1 (by rfl) ⟨2146418, by rfl⟩ : syracuseStep 2861891 = 4292837) B4292837
theorem B1907927 : Blo 1907435 1907927 := bstep (se 1 (by rfl) ⟨1430945, by rfl⟩ : syracuseStep 1907927 = 2861891) B2861891
theorem B4829453 : Blo 1907435 4829453 := bbase (se 3 (by rfl) ⟨905522, by rfl⟩ : syracuseStep 4829453 = 1811045) (by norm_num)
theorem B3219635 : Blo 1907435 3219635 := bstep (se 1 (by rfl) ⟨2414726, by rfl⟩ : syracuseStep 3219635 = 4829453) B4829453
theorem B2146423 : Blo 1907435 2146423 := bstep (se 1 (by rfl) ⟨1609817, by rfl⟩ : syracuseStep 2146423 = 3219635) B3219635
theorem B2861897 : Blo 1907435 2861897 := bstep (se 2 (by rfl) ⟨1073211, by rfl⟩ : syracuseStep 2861897 = 2146423) B2146423
theorem B1907931 : Blo 1907435 1907931 := bstep (se 1 (by rfl) ⟨1430948, by rfl⟩ : syracuseStep 1907931 = 2861897) B2861897
theorem B2716573 : Blo 1907435 2716573 := bbase (se 3 (by rfl) ⟨509357, by rfl⟩ : syracuseStep 2716573 = 1018715) (by norm_num)
theorem B3622097 : Blo 1907435 3622097 := bstep (se 2 (by rfl) ⟨1358286, by rfl⟩ : syracuseStep 3622097 = 2716573) B2716573
theorem B9658925 : Blo 1907435 9658925 := bstep (se 3 (by rfl) ⟨1811048, by rfl⟩ : syracuseStep 9658925 = 3622097) B3622097
theorem B6439283 : Blo 1907435 6439283 := bstep (se 1 (by rfl) ⟨4829462, by rfl⟩ : syracuseStep 6439283 = 9658925) B9658925
theorem B4292855 : Blo 1907435 4292855 := bstep (se 1 (by rfl) ⟨3219641, by rfl⟩ : syracuseStep 4292855 = 6439283) B6439283
theorem B2861903 : Blo 1907435 2861903 := bstep (se 1 (by rfl) ⟨2146427, by rfl⟩ : syracuseStep 2861903 = 4292855) B4292855
theorem B1907935 : Blo 1907435 1907935 := bstep (se 1 (by rfl) ⟨1430951, by rfl⟩ : syracuseStep 1907935 = 2861903) B2861903
theorem B2861909 : Blo 1907435 2861909 := bbase (se 9 (by rfl) ⟨8384, by rfl⟩ : syracuseStep 2861909 = 16769) (by norm_num)
theorem B1907939 : Blo 1907435 1907939 := bstep (se 1 (by rfl) ⟨1430954, by rfl⟩ : syracuseStep 1907939 = 2861909) B2861909
theorem B4074877 : Blo 1907435 4074877 := bbase (se 3 (by rfl) ⟨764039, by rfl⟩ : syracuseStep 4074877 = 1528079) (by norm_num)
theorem B5433169 : Blo 1907435 5433169 := bstep (se 2 (by rfl) ⟨2037438, by rfl⟩ : syracuseStep 5433169 = 4074877) B4074877
theorem B7244225 : Blo 1907435 7244225 := bstep (se 2 (by rfl) ⟨2716584, by rfl⟩ : syracuseStep 7244225 = 5433169) B5433169
theorem B4829483 : Blo 1907435 4829483 := bstep (se 1 (by rfl) ⟨3622112, by rfl⟩ : syracuseStep 4829483 = 7244225) B7244225
theorem B3219655 : Blo 1907435 3219655 := bstep (se 1 (by rfl) ⟨2414741, by rfl⟩ : syracuseStep 3219655 = 4829483) B4829483
theorem B4292873 : Blo 1907435 4292873 := bstep (se 2 (by rfl) ⟨1609827, by rfl⟩ : syracuseStep 4292873 = 3219655) B3219655
theorem B2861915 : Blo 1907435 2861915 := bstep (se 1 (by rfl) ⟨2146436, by rfl⟩ : syracuseStep 2861915 = 4292873) B4292873
theorem B1907943 : Blo 1907435 1907943 := bstep (se 1 (by rfl) ⟨1430957, by rfl⟩ : syracuseStep 1907943 = 2861915) B2861915
theorem B2146441 : Blo 1907435 2146441 := bbase (se 2 (by rfl) ⟨804915, by rfl⟩ : syracuseStep 2146441 = 1609831) (by norm_num)
theorem B2861921 : Blo 1907435 2861921 := bstep (se 2 (by rfl) ⟨1073220, by rfl⟩ : syracuseStep 2861921 = 2146441) B2146441
theorem B1907947 : Blo 1907435 1907947 := bstep (se 1 (by rfl) ⟨1430960, by rfl⟩ : syracuseStep 1907947 = 2861921) B2861921
theorem B1960369 : Blo 1907435 1960369 := bbase (se 2 (by rfl) ⟨735138, by rfl⟩ : syracuseStep 1960369 = 1470277) (by norm_num)
theorem B10455301 : Blo 1907435 10455301 := bstep (se 4 (by rfl) ⟨980184, by rfl⟩ : syracuseStep 10455301 = 1960369) B1960369
theorem B13940401 : Blo 1907435 13940401 := bstep (se 2 (by rfl) ⟨5227650, by rfl⟩ : syracuseStep 13940401 = 10455301) B10455301
theorem B18587201 : Blo 1907435 18587201 := bstep (se 2 (by rfl) ⟨6970200, by rfl⟩ : syracuseStep 18587201 = 13940401) B13940401
theorem B198263477 : Blo 1907435 198263477 := bstep (se 5 (by rfl) ⟨9293600, by rfl⟩ : syracuseStep 198263477 = 18587201) B18587201
theorem B132175651 : Blo 1907435 132175651 := bstep (se 1 (by rfl) ⟨99131738, by rfl⟩ : syracuseStep 132175651 = 198263477) B198263477
theorem B176234201 : Blo 1907435 176234201 := bstep (se 2 (by rfl) ⟨66087825, by rfl⟩ : syracuseStep 176234201 = 132175651) B132175651
theorem B117489467 : Blo 1907435 117489467 := bstep (se 1 (by rfl) ⟨88117100, by rfl⟩ : syracuseStep 117489467 = 176234201) B176234201
theorem B78326311 : Blo 1907435 78326311 := bstep (se 1 (by rfl) ⟨58744733, by rfl⟩ : syracuseStep 78326311 = 117489467) B117489467
theorem B104435081 : Blo 1907435 104435081 := bstep (se 2 (by rfl) ⟨39163155, by rfl⟩ : syracuseStep 104435081 = 78326311) B78326311
theorem B69623387 : Blo 1907435 69623387 := bstep (se 1 (by rfl) ⟨52217540, by rfl⟩ : syracuseStep 69623387 = 104435081) B104435081
theorem B46415591 : Blo 1907435 46415591 := bstep (se 1 (by rfl) ⟨34811693, by rfl⟩ : syracuseStep 46415591 = 69623387) B69623387
theorem B30943727 : Blo 1907435 30943727 := bstep (se 1 (by rfl) ⟨23207795, by rfl⟩ : syracuseStep 30943727 = 46415591) B46415591
theorem B20629151 : Blo 1907435 20629151 := bstep (se 1 (by rfl) ⟨15471863, by rfl⟩ : syracuseStep 20629151 = 30943727) B30943727
theorem B13752767 : Blo 1907435 13752767 := bstep (se 1 (by rfl) ⟨10314575, by rfl⟩ : syracuseStep 13752767 = 20629151) B20629151
theorem B36674045 : Blo 1907435 36674045 := bstep (se 3 (by rfl) ⟨6876383, by rfl⟩ : syracuseStep 36674045 = 13752767) B13752767
theorem B24449363 : Blo 1907435 24449363 := bstep (se 1 (by rfl) ⟨18337022, by rfl⟩ : syracuseStep 24449363 = 36674045) B36674045
theorem B16299575 : Blo 1907435 16299575 := bstep (se 1 (by rfl) ⟨12224681, by rfl⟩ : syracuseStep 16299575 = 24449363) B24449363
theorem B10866383 : Blo 1907435 10866383 := bstep (se 1 (by rfl) ⟨8149787, by rfl⟩ : syracuseStep 10866383 = 16299575) B16299575
theorem B7244255 : Blo 1907435 7244255 := bstep (se 1 (by rfl) ⟨5433191, by rfl⟩ : syracuseStep 7244255 = 10866383) B10866383
theorem B4829503 : Blo 1907435 4829503 := bstep (se 1 (by rfl) ⟨3622127, by rfl⟩ : syracuseStep 4829503 = 7244255) B7244255
theorem B6439337 : Blo 1907435 6439337 := bstep (se 2 (by rfl) ⟨2414751, by rfl⟩ : syracuseStep 6439337 = 4829503) B4829503
theorem B4292891 : Blo 1907435 4292891 := bstep (se 1 (by rfl) ⟨3219668, by rfl⟩ : syracuseStep 4292891 = 6439337) B6439337
theorem B2861927 : Blo 1907435 2861927 := bstep (se 1 (by rfl) ⟨2146445, by rfl⟩ : syracuseStep 2861927 = 4292891) B4292891
theorem B1907951 : Blo 1907435 1907951 := bstep (se 1 (by rfl) ⟨1430963, by rfl⟩ : syracuseStep 1907951 = 2861927) B2861927
theorem B2861933 : Blo 1907435 2861933 := bbase (se 3 (by rfl) ⟨536612, by rfl⟩ : syracuseStep 2861933 = 1073225) (by norm_num)
theorem B1907955 : Blo 1907435 1907955 := bstep (se 1 (by rfl) ⟨1430966, by rfl⟩ : syracuseStep 1907955 = 2861933) B2861933
theorem B4292909 : Blo 1907435 4292909 := bbase (se 3 (by rfl) ⟨804920, by rfl⟩ : syracuseStep 4292909 = 1609841) (by norm_num)
theorem B2861939 : Blo 1907435 2861939 := bstep (se 1 (by rfl) ⟨2146454, by rfl⟩ : syracuseStep 2861939 = 4292909) B4292909
theorem B1907959 : Blo 1907435 1907959 := bstep (se 1 (by rfl) ⟨1430969, by rfl⟩ : syracuseStep 1907959 = 2861939) B2861939
theorem B5801989 : Blo 1907435 5801989 := bbase (se 4 (by rfl) ⟨543936, by rfl⟩ : syracuseStep 5801989 = 1087873) (by norm_num)
theorem B7735985 : Blo 1907435 7735985 := bstep (se 2 (by rfl) ⟨2900994, by rfl⟩ : syracuseStep 7735985 = 5801989) B5801989
theorem B5157323 : Blo 1907435 5157323 := bstep (se 1 (by rfl) ⟨3867992, by rfl⟩ : syracuseStep 5157323 = 7735985) B7735985
theorem B3438215 : Blo 1907435 3438215 := bstep (se 1 (by rfl) ⟨2578661, by rfl⟩ : syracuseStep 3438215 = 5157323) B5157323
theorem B2292143 : Blo 1907435 2292143 := bstep (se 1 (by rfl) ⟨1719107, by rfl⟩ : syracuseStep 2292143 = 3438215) B3438215
theorem B6112381 : Blo 1907435 6112381 := bstep (se 3 (by rfl) ⟨1146071, by rfl⟩ : syracuseStep 6112381 = 2292143) B2292143
theorem B8149841 : Blo 1907435 8149841 := bstep (se 2 (by rfl) ⟨3056190, by rfl⟩ : syracuseStep 8149841 = 6112381) B6112381
theorem B5433227 : Blo 1907435 5433227 := bstep (se 1 (by rfl) ⟨4074920, by rfl⟩ : syracuseStep 5433227 = 8149841) B8149841
theorem B3622151 : Blo 1907435 3622151 := bstep (se 1 (by rfl) ⟨2716613, by rfl⟩ : syracuseStep 3622151 = 5433227) B5433227
theorem B2414767 : Blo 1907435 2414767 := bstep (se 1 (by rfl) ⟨1811075, by rfl⟩ : syracuseStep 2414767 = 3622151) B3622151
theorem B3219689 : Blo 1907435 3219689 := bstep (se 2 (by rfl) ⟨1207383, by rfl⟩ : syracuseStep 3219689 = 2414767) B2414767
theorem B2146459 : Blo 1907435 2146459 := bstep (se 1 (by rfl) ⟨1609844, by rfl⟩ : syracuseStep 2146459 = 3219689) B3219689
theorem B2861945 : Blo 1907435 2861945 := bstep (se 2 (by rfl) ⟨1073229, by rfl⟩ : syracuseStep 2861945 = 2146459) B2146459
theorem B1907963 : Blo 1907435 1907963 := bstep (se 1 (by rfl) ⟨1430972, by rfl⟩ : syracuseStep 1907963 = 2861945) B2861945
theorem B4895437 : Blo 1907435 4895437 := bbase (se 3 (by rfl) ⟨917894, by rfl⟩ : syracuseStep 4895437 = 1835789) (by norm_num)
theorem B6527249 : Blo 1907435 6527249 := bstep (se 2 (by rfl) ⟨2447718, by rfl⟩ : syracuseStep 6527249 = 4895437) B4895437
theorem B4351499 : Blo 1907435 4351499 := bstep (se 1 (by rfl) ⟨3263624, by rfl⟩ : syracuseStep 4351499 = 6527249) B6527249
theorem B2900999 : Blo 1907435 2900999 := bstep (se 1 (by rfl) ⟨2175749, by rfl⟩ : syracuseStep 2900999 = 4351499) B4351499
theorem B1933999 : Blo 1907435 1933999 := bstep (se 1 (by rfl) ⟨1450499, by rfl⟩ : syracuseStep 1933999 = 2900999) B2900999
theorem B41258645 : Blo 1907435 41258645 := bstep (se 6 (by rfl) ⟨966999, by rfl⟩ : syracuseStep 41258645 = 1933999) B1933999
theorem B27505763 : Blo 1907435 27505763 := bstep (se 1 (by rfl) ⟨20629322, by rfl⟩ : syracuseStep 27505763 = 41258645) B41258645
theorem B18337175 : Blo 1907435 18337175 := bstep (se 1 (by rfl) ⟨13752881, by rfl⟩ : syracuseStep 18337175 = 27505763) B27505763
theorem B12224783 : Blo 1907435 12224783 := bstep (se 1 (by rfl) ⟨9168587, by rfl⟩ : syracuseStep 12224783 = 18337175) B18337175
theorem B32599421 : Blo 1907435 32599421 := bstep (se 3 (by rfl) ⟨6112391, by rfl⟩ : syracuseStep 32599421 = 12224783) B12224783
theorem B21732947 : Blo 1907435 21732947 := bstep (se 1 (by rfl) ⟨16299710, by rfl⟩ : syracuseStep 21732947 = 32599421) B32599421
theorem B14488631 : Blo 1907435 14488631 := bstep (se 1 (by rfl) ⟨10866473, by rfl⟩ : syracuseStep 14488631 = 21732947) B21732947
theorem B9659087 : Blo 1907435 9659087 := bstep (se 1 (by rfl) ⟨7244315, by rfl⟩ : syracuseStep 9659087 = 14488631) B14488631
theorem B6439391 : Blo 1907435 6439391 := bstep (se 1 (by rfl) ⟨4829543, by rfl⟩ : syracuseStep 6439391 = 9659087) B9659087
theorem B4292927 : Blo 1907435 4292927 := bstep (se 1 (by rfl) ⟨3219695, by rfl⟩ : syracuseStep 4292927 = 6439391) B6439391
theorem B2861951 : Blo 1907435 2861951 := bstep (se 1 (by rfl) ⟨2146463, by rfl⟩ : syracuseStep 2861951 = 4292927) B4292927
theorem B1907967 : Blo 1907435 1907967 := bstep (se 1 (by rfl) ⟨1430975, by rfl⟩ : syracuseStep 1907967 = 2861951) B2861951
theorem B2861957 : Blo 1907435 2861957 := bbase (se 4 (by rfl) ⟨268308, by rfl⟩ : syracuseStep 2861957 = 536617) (by norm_num)
theorem B1907971 : Blo 1907435 1907971 := bstep (se 1 (by rfl) ⟨1430978, by rfl⟩ : syracuseStep 1907971 = 2861957) B2861957
theorem B3219709 : Blo 1907435 3219709 := bbase (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) (by norm_num)
theorem B4292945 : Blo 1907435 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B2861963 : Blo 1907435 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B1907975 : Blo 1907435 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B2146477 : Blo 1907435 2146477 := bbase (se 3 (by rfl) ⟨402464, by rfl⟩ : syracuseStep 2146477 = 804929) (by norm_num)
theorem B2861969 : Blo 1907435 2861969 := bstep (se 2 (by rfl) ⟨1073238, by rfl⟩ : syracuseStep 2861969 = 2146477) B2146477
theorem B1907979 : Blo 1907435 1907979 := bstep (se 1 (by rfl) ⟨1430984, by rfl⟩ : syracuseStep 1907979 = 2861969) B2861969
theorem B6439445 : Blo 1907435 6439445 := bbase (se 6 (by rfl) ⟨150924, by rfl⟩ : syracuseStep 6439445 = 301849) (by norm_num)
theorem B4292963 : Blo 1907435 4292963 := bstep (se 1 (by rfl) ⟨3219722, by rfl⟩ : syracuseStep 4292963 = 6439445) B6439445
theorem B2861975 : Blo 1907435 2861975 := bstep (se 1 (by rfl) ⟨2146481, by rfl⟩ : syracuseStep 2861975 = 4292963) B4292963
theorem B1907983 : Blo 1907435 1907983 := bstep (se 1 (by rfl) ⟨1430987, by rfl⟩ : syracuseStep 1907983 = 2861975) B2861975
theorem B2861981 : Blo 1907435 2861981 := bbase (se 3 (by rfl) ⟨536621, by rfl⟩ : syracuseStep 2861981 = 1073243) (by norm_num)
theorem B1907987 : Blo 1907435 1907987 := bstep (se 1 (by rfl) ⟨1430990, by rfl⟩ : syracuseStep 1907987 = 2861981) B2861981
theorem B4292981 : Blo 1907435 4292981 := bbase (se 5 (by rfl) ⟨201233, by rfl⟩ : syracuseStep 4292981 = 402467) (by norm_num)
theorem B2861987 : Blo 1907435 2861987 := bstep (se 1 (by rfl) ⟨2146490, by rfl⟩ : syracuseStep 2861987 = 4292981) B4292981
theorem B1907991 : Blo 1907435 1907991 := bstep (se 1 (by rfl) ⟨1430993, by rfl⟩ : syracuseStep 1907991 = 2861987) B2861987
theorem B2292181 : Blo 1907435 2292181 := bbase (se 7 (by rfl) ⟨26861, by rfl⟩ : syracuseStep 2292181 = 53723) (by norm_num)
theorem B12224965 : Blo 1907435 12224965 := bstep (se 4 (by rfl) ⟨1146090, by rfl⟩ : syracuseStep 12224965 = 2292181) B2292181
theorem B16299953 : Blo 1907435 16299953 := bstep (se 2 (by rfl) ⟨6112482, by rfl⟩ : syracuseStep 16299953 = 12224965) B12224965
theorem B10866635 : Blo 1907435 10866635 := bstep (se 1 (by rfl) ⟨8149976, by rfl⟩ : syracuseStep 10866635 = 16299953) B16299953
theorem B7244423 : Blo 1907435 7244423 := bstep (se 1 (by rfl) ⟨5433317, by rfl⟩ : syracuseStep 7244423 = 10866635) B10866635
theorem B4829615 : Blo 1907435 4829615 := bstep (se 1 (by rfl) ⟨3622211, by rfl⟩ : syracuseStep 4829615 = 7244423) B7244423
theorem B3219743 : Blo 1907435 3219743 := bstep (se 1 (by rfl) ⟨2414807, by rfl⟩ : syracuseStep 3219743 = 4829615) B4829615
theorem B2146495 : Blo 1907435 2146495 := bstep (se 1 (by rfl) ⟨1609871, by rfl⟩ : syracuseStep 2146495 = 3219743) B3219743
theorem B2861993 : Blo 1907435 2861993 := bstep (se 2 (by rfl) ⟨1073247, by rfl⟩ : syracuseStep 2861993 = 2146495) B2146495
theorem B1907995 : Blo 1907435 1907995 := bstep (se 1 (by rfl) ⟨1430996, by rfl⟩ : syracuseStep 1907995 = 2861993) B2861993
theorem B7244437 : Blo 1907435 7244437 := bbase (se 6 (by rfl) ⟨169791, by rfl⟩ : syracuseStep 7244437 = 339583) (by norm_num)
theorem B9659249 : Blo 1907435 9659249 := bstep (se 2 (by rfl) ⟨3622218, by rfl⟩ : syracuseStep 9659249 = 7244437) B7244437
theorem B6439499 : Blo 1907435 6439499 := bstep (se 1 (by rfl) ⟨4829624, by rfl⟩ : syracuseStep 6439499 = 9659249) B9659249
theorem B4292999 : Blo 1907435 4292999 := bstep (se 1 (by rfl) ⟨3219749, by rfl⟩ : syracuseStep 4292999 = 6439499) B6439499
theorem B2861999 : Blo 1907435 2861999 := bstep (se 1 (by rfl) ⟨2146499, by rfl⟩ : syracuseStep 2861999 = 4292999) B4292999
theorem B1907999 : Blo 1907435 1907999 := bstep (se 1 (by rfl) ⟨1430999, by rfl⟩ : syracuseStep 1907999 = 2861999) B2861999
theorem B2862005 : Blo 1907435 2862005 := bbase (se 5 (by rfl) ⟨134156, by rfl⟩ : syracuseStep 2862005 = 268313) (by norm_num)
theorem B1908003 : Blo 1907435 1908003 := bstep (se 1 (by rfl) ⟨1431002, by rfl⟩ : syracuseStep 1908003 = 2862005) B2862005
theorem B4829645 : Blo 1907435 4829645 := bbase (se 3 (by rfl) ⟨905558, by rfl⟩ : syracuseStep 4829645 = 1811117) (by norm_num)
theorem B3219763 : Blo 1907435 3219763 := bstep (se 1 (by rfl) ⟨2414822, by rfl⟩ : syracuseStep 3219763 = 4829645) B4829645
theorem B4293017 : Blo 1907435 4293017 := bstep (se 2 (by rfl) ⟨1609881, by rfl⟩ : syracuseStep 4293017 = 3219763) B3219763
theorem B2862011 : Blo 1907435 2862011 := bstep (se 1 (by rfl) ⟨2146508, by rfl⟩ : syracuseStep 2862011 = 4293017) B4293017
theorem B1908007 : Blo 1907435 1908007 := bstep (se 1 (by rfl) ⟨1431005, by rfl⟩ : syracuseStep 1908007 = 2862011) B2862011
theorem B2146513 : Blo 1907435 2146513 := bbase (se 2 (by rfl) ⟨804942, by rfl⟩ : syracuseStep 2146513 = 1609885) (by norm_num)
theorem B2862017 : Blo 1907435 2862017 := bstep (se 2 (by rfl) ⟨1073256, by rfl⟩ : syracuseStep 2862017 = 2146513) B2146513
theorem B1908011 : Blo 1907435 1908011 := bstep (se 1 (by rfl) ⟨1431008, by rfl⟩ : syracuseStep 1908011 = 2862017) B2862017
theorem B9168821 : Blo 1907435 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B6112547 : Blo 1907435 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B4075031 : Blo 1907435 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B2716687 : Blo 1907435 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B3622249 : Blo 1907435 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B4829665 : Blo 1907435 4829665 := bstep (se 2 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 4829665 = 3622249) B3622249
theorem B6439553 : Blo 1907435 6439553 := bstep (se 2 (by rfl) ⟨2414832, by rfl⟩ : syracuseStep 6439553 = 4829665) B4829665
theorem B4293035 : Blo 1907435 4293035 := bstep (se 1 (by rfl) ⟨3219776, by rfl⟩ : syracuseStep 4293035 = 6439553) B6439553
theorem B2862023 : Blo 1907435 2862023 := bstep (se 1 (by rfl) ⟨2146517, by rfl⟩ : syracuseStep 2862023 = 4293035) B4293035
theorem B1908015 : Blo 1907435 1908015 := bstep (se 1 (by rfl) ⟨1431011, by rfl⟩ : syracuseStep 1908015 = 2862023) B2862023
theorem B2862029 : Blo 1907435 2862029 := bbase (se 3 (by rfl) ⟨536630, by rfl⟩ : syracuseStep 2862029 = 1073261) (by norm_num)
theorem B1908019 : Blo 1907435 1908019 := bstep (se 1 (by rfl) ⟨1431014, by rfl⟩ : syracuseStep 1908019 = 2862029) B2862029
theorem B4293053 : Blo 1907435 4293053 := bbase (se 3 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 4293053 = 1609895) (by norm_num)
theorem B2862035 : Blo 1907435 2862035 := bstep (se 1 (by rfl) ⟨2146526, by rfl⟩ : syracuseStep 2862035 = 4293053) B4293053
theorem B1908023 : Blo 1907435 1908023 := bstep (se 1 (by rfl) ⟨1431017, by rfl⟩ : syracuseStep 1908023 = 2862035) B2862035
theorem B3219797 : Blo 1907435 3219797 := bbase (se 10 (by rfl) ⟨4716, by rfl⟩ : syracuseStep 3219797 = 9433) (by norm_num)
theorem B2146531 : Blo 1907435 2146531 := bstep (se 1 (by rfl) ⟨1609898, by rfl⟩ : syracuseStep 2146531 = 3219797) B3219797
theorem B2862041 : Blo 1907435 2862041 := bstep (se 2 (by rfl) ⟨1073265, by rfl⟩ : syracuseStep 2862041 = 2146531) B2146531
theorem B1908027 : Blo 1907435 1908027 := bstep (se 1 (by rfl) ⟨1431020, by rfl⟩ : syracuseStep 1908027 = 2862041) B2862041
theorem B6112597 : Blo 1907435 6112597 := bbase (se 12 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 6112597 = 4477) (by norm_num)
theorem B8150129 : Blo 1907435 8150129 := bstep (se 2 (by rfl) ⟨3056298, by rfl⟩ : syracuseStep 8150129 = 6112597) B6112597
theorem B5433419 : Blo 1907435 5433419 := bstep (se 1 (by rfl) ⟨4075064, by rfl⟩ : syracuseStep 5433419 = 8150129) B8150129
theorem B14489117 : Blo 1907435 14489117 := bstep (se 3 (by rfl) ⟨2716709, by rfl⟩ : syracuseStep 14489117 = 5433419) B5433419
theorem B9659411 : Blo 1907435 9659411 := bstep (se 1 (by rfl) ⟨7244558, by rfl⟩ : syracuseStep 9659411 = 14489117) B14489117
theorem B6439607 : Blo 1907435 6439607 := bstep (se 1 (by rfl) ⟨4829705, by rfl⟩ : syracuseStep 6439607 = 9659411) B9659411
theorem B4293071 : Blo 1907435 4293071 := bstep (se 1 (by rfl) ⟨3219803, by rfl⟩ : syracuseStep 4293071 = 6439607) B6439607
theorem B2862047 : Blo 1907435 2862047 := bstep (se 1 (by rfl) ⟨2146535, by rfl⟩ : syracuseStep 2862047 = 4293071) B4293071
theorem B1908031 : Blo 1907435 1908031 := bstep (se 1 (by rfl) ⟨1431023, by rfl⟩ : syracuseStep 1908031 = 2862047) B2862047
theorem B2862053 : Blo 1907435 2862053 := bbase (se 4 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 2862053 = 536635) (by norm_num)
theorem B1908035 : Blo 1907435 1908035 := bstep (se 1 (by rfl) ⟨1431026, by rfl⟩ : syracuseStep 1908035 = 2862053) B2862053
theorem B8150165 : Blo 1907435 8150165 := bbase (se 6 (by rfl) ⟨191019, by rfl⟩ : syracuseStep 8150165 = 382039) (by norm_num)
theorem B5433443 : Blo 1907435 5433443 := bstep (se 1 (by rfl) ⟨4075082, by rfl⟩ : syracuseStep 5433443 = 8150165) B8150165
theorem B3622295 : Blo 1907435 3622295 := bstep (se 1 (by rfl) ⟨2716721, by rfl⟩ : syracuseStep 3622295 = 5433443) B5433443
theorem B2414863 : Blo 1907435 2414863 := bstep (se 1 (by rfl) ⟨1811147, by rfl⟩ : syracuseStep 2414863 = 3622295) B3622295
theorem B3219817 : Blo 1907435 3219817 := bstep (se 2 (by rfl) ⟨1207431, by rfl⟩ : syracuseStep 3219817 = 2414863) B2414863
theorem B4293089 : Blo 1907435 4293089 := bstep (se 2 (by rfl) ⟨1609908, by rfl⟩ : syracuseStep 4293089 = 3219817) B3219817
theorem B2862059 : Blo 1907435 2862059 := bstep (se 1 (by rfl) ⟨2146544, by rfl⟩ : syracuseStep 2862059 = 4293089) B4293089
theorem B1908039 : Blo 1907435 1908039 := bstep (se 1 (by rfl) ⟨1431029, by rfl⟩ : syracuseStep 1908039 = 2862059) B2862059
theorem B2146549 : Blo 1907435 2146549 := bbase (se 5 (by rfl) ⟨100619, by rfl⟩ : syracuseStep 2146549 = 201239) (by norm_num)
theorem B2862065 : Blo 1907435 2862065 := bstep (se 2 (by rfl) ⟨1073274, by rfl⟩ : syracuseStep 2862065 = 2146549) B2146549
theorem B1908043 : Blo 1907435 1908043 := bstep (se 1 (by rfl) ⟨1431032, by rfl⟩ : syracuseStep 1908043 = 2862065) B2862065
theorem B2414873 : Blo 1907435 2414873 := bbase (se 2 (by rfl) ⟨905577, by rfl⟩ : syracuseStep 2414873 = 1811155) (by norm_num)
theorem B6439661 : Blo 1907435 6439661 := bstep (se 3 (by rfl) ⟨1207436, by rfl⟩ : syracuseStep 6439661 = 2414873) B2414873
theorem B4293107 : Blo 1907435 4293107 := bstep (se 1 (by rfl) ⟨3219830, by rfl⟩ : syracuseStep 4293107 = 6439661) B6439661
theorem B2862071 : Blo 1907435 2862071 := bstep (se 1 (by rfl) ⟨2146553, by rfl⟩ : syracuseStep 2862071 = 4293107) B4293107
theorem B1908047 : Blo 1907435 1908047 := bstep (se 1 (by rfl) ⟨1431035, by rfl⟩ : syracuseStep 1908047 = 2862071) B2862071
theorem B2862077 : Blo 1907435 2862077 := bbase (se 3 (by rfl) ⟨536639, by rfl⟩ : syracuseStep 2862077 = 1073279) (by norm_num)
theorem B1908051 : Blo 1907435 1908051 := bstep (se 1 (by rfl) ⟨1431038, by rfl⟩ : syracuseStep 1908051 = 2862077) B2862077
theorem B4293125 : Blo 1907435 4293125 := bbase (se 4 (by rfl) ⟨402480, by rfl⟩ : syracuseStep 4293125 = 804961) (by norm_num)
theorem B2862083 : Blo 1907435 2862083 := bstep (se 1 (by rfl) ⟨2146562, by rfl⟩ : syracuseStep 2862083 = 4293125) B4293125
theorem B1908055 : Blo 1907435 1908055 := bstep (se 1 (by rfl) ⟨1431041, by rfl⟩ : syracuseStep 1908055 = 2862083) B2862083
theorem B3622333 : Blo 1907435 3622333 := bbase (se 3 (by rfl) ⟨679187, by rfl⟩ : syracuseStep 3622333 = 1358375) (by norm_num)
theorem B4829777 : Blo 1907435 4829777 := bstep (se 2 (by rfl) ⟨1811166, by rfl⟩ : syracuseStep 4829777 = 3622333) B3622333
theorem B3219851 : Blo 1907435 3219851 := bstep (se 1 (by rfl) ⟨2414888, by rfl⟩ : syracuseStep 3219851 = 4829777) B4829777
theorem B2146567 : Blo 1907435 2146567 := bstep (se 1 (by rfl) ⟨1609925, by rfl⟩ : syracuseStep 2146567 = 3219851) B3219851
theorem B2862089 : Blo 1907435 2862089 := bstep (se 2 (by rfl) ⟨1073283, by rfl⟩ : syracuseStep 2862089 = 2146567) B2146567
theorem B1908059 : Blo 1907435 1908059 := bstep (se 1 (by rfl) ⟨1431044, by rfl⟩ : syracuseStep 1908059 = 2862089) B2862089
theorem B9659573 : Blo 1907435 9659573 := bbase (se 5 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 9659573 = 905585) (by norm_num)
theorem B6439715 : Blo 1907435 6439715 := bstep (se 1 (by rfl) ⟨4829786, by rfl⟩ : syracuseStep 6439715 = 9659573) B9659573
theorem B4293143 : Blo 1907435 4293143 := bstep (se 1 (by rfl) ⟨3219857, by rfl⟩ : syracuseStep 4293143 = 6439715) B6439715
theorem B2862095 : Blo 1907435 2862095 := bstep (se 1 (by rfl) ⟨2146571, by rfl⟩ : syracuseStep 2862095 = 4293143) B4293143
theorem B1908063 : Blo 1907435 1908063 := bstep (se 1 (by rfl) ⟨1431047, by rfl⟩ : syracuseStep 1908063 = 2862095) B2862095
theorem B2862101 : Blo 1907435 2862101 := bbase (se 6 (by rfl) ⟨67080, by rfl⟩ : syracuseStep 2862101 = 134161) (by norm_num)
theorem B1908067 : Blo 1907435 1908067 := bstep (se 1 (by rfl) ⟨1431050, by rfl⟩ : syracuseStep 1908067 = 2862101) B2862101
theorem B11604629 : Blo 1907435 11604629 := bbase (se 6 (by rfl) ⟨271983, by rfl⟩ : syracuseStep 11604629 = 543967) (by norm_num)
theorem B7736419 : Blo 1907435 7736419 := bstep (se 1 (by rfl) ⟨5802314, by rfl⟩ : syracuseStep 7736419 = 11604629) B11604629
theorem B10315225 : Blo 1907435 10315225 := bstep (se 2 (by rfl) ⟨3868209, by rfl⟩ : syracuseStep 10315225 = 7736419) B7736419
theorem B13753633 : Blo 1907435 13753633 := bstep (se 2 (by rfl) ⟨5157612, by rfl⟩ : syracuseStep 13753633 = 10315225) B10315225
theorem B18338177 : Blo 1907435 18338177 := bstep (se 2 (by rfl) ⟨6876816, by rfl⟩ : syracuseStep 18338177 = 13753633) B13753633
theorem B12225451 : Blo 1907435 12225451 := bstep (se 1 (by rfl) ⟨9169088, by rfl⟩ : syracuseStep 12225451 = 18338177) B18338177
theorem B16300601 : Blo 1907435 16300601 := bstep (se 2 (by rfl) ⟨6112725, by rfl⟩ : syracuseStep 16300601 = 12225451) B12225451
theorem B10867067 : Blo 1907435 10867067 := bstep (se 1 (by rfl) ⟨8150300, by rfl⟩ : syracuseStep 10867067 = 16300601) B16300601
theorem B7244711 : Blo 1907435 7244711 := bstep (se 1 (by rfl) ⟨5433533, by rfl⟩ : syracuseStep 7244711 = 10867067) B10867067
theorem B4829807 : Blo 1907435 4829807 := bstep (se 1 (by rfl) ⟨3622355, by rfl⟩ : syracuseStep 4829807 = 7244711) B7244711
theorem B3219871 : Blo 1907435 3219871 := bstep (se 1 (by rfl) ⟨2414903, by rfl⟩ : syracuseStep 3219871 = 4829807) B4829807
theorem B4293161 : Blo 1907435 4293161 := bstep (se 2 (by rfl) ⟨1609935, by rfl⟩ : syracuseStep 4293161 = 3219871) B3219871
theorem B2862107 : Blo 1907435 2862107 := bstep (se 1 (by rfl) ⟨2146580, by rfl⟩ : syracuseStep 2862107 = 4293161) B4293161
theorem B1908071 : Blo 1907435 1908071 := bstep (se 1 (by rfl) ⟨1431053, by rfl⟩ : syracuseStep 1908071 = 2862107) B2862107
theorem B2146585 : Blo 1907435 2146585 := bbase (se 2 (by rfl) ⟨804969, by rfl⟩ : syracuseStep 2146585 = 1609939) (by norm_num)
theorem B2862113 : Blo 1907435 2862113 := bstep (se 2 (by rfl) ⟨1073292, by rfl⟩ : syracuseStep 2862113 = 2146585) B2146585
theorem B1908075 : Blo 1907435 1908075 := bstep (se 1 (by rfl) ⟨1431056, by rfl⟩ : syracuseStep 1908075 = 2862113) B2862113
theorem B7244741 : Blo 1907435 7244741 := bbase (se 4 (by rfl) ⟨679194, by rfl⟩ : syracuseStep 7244741 = 1358389) (by norm_num)
theorem B4829827 : Blo 1907435 4829827 := bstep (se 1 (by rfl) ⟨3622370, by rfl⟩ : syracuseStep 4829827 = 7244741) B7244741
theorem B6439769 : Blo 1907435 6439769 := bstep (se 2 (by rfl) ⟨2414913, by rfl⟩ : syracuseStep 6439769 = 4829827) B4829827
theorem B4293179 : Blo 1907435 4293179 := bstep (se 1 (by rfl) ⟨3219884, by rfl⟩ : syracuseStep 4293179 = 6439769) B6439769
theorem B2862119 : Blo 1907435 2862119 := bstep (se 1 (by rfl) ⟨2146589, by rfl⟩ : syracuseStep 2862119 = 4293179) B4293179
theorem B1908079 : Blo 1907435 1908079 := bstep (se 1 (by rfl) ⟨1431059, by rfl⟩ : syracuseStep 1908079 = 2862119) B2862119
theorem B2862125 : Blo 1907435 2862125 := bbase (se 3 (by rfl) ⟨536648, by rfl⟩ : syracuseStep 2862125 = 1073297) (by norm_num)
theorem B1908083 : Blo 1907435 1908083 := bstep (se 1 (by rfl) ⟨1431062, by rfl⟩ : syracuseStep 1908083 = 2862125) B2862125
theorem B4293197 : Blo 1907435 4293197 := bbase (se 3 (by rfl) ⟨804974, by rfl⟩ : syracuseStep 4293197 = 1609949) (by norm_num)
theorem B2862131 : Blo 1907435 2862131 := bstep (se 1 (by rfl) ⟨2146598, by rfl⟩ : syracuseStep 2862131 = 4293197) B4293197
theorem B1908087 : Blo 1907435 1908087 := bstep (se 1 (by rfl) ⟨1431065, by rfl⟩ : syracuseStep 1908087 = 2862131) B2862131
theorem B2414929 : Blo 1907435 2414929 := bbase (se 2 (by rfl) ⟨905598, by rfl⟩ : syracuseStep 2414929 = 1811197) (by norm_num)
theorem B3219905 : Blo 1907435 3219905 := bstep (se 2 (by rfl) ⟨1207464, by rfl⟩ : syracuseStep 3219905 = 2414929) B2414929
theorem B2146603 : Blo 1907435 2146603 := bstep (se 1 (by rfl) ⟨1609952, by rfl⟩ : syracuseStep 2146603 = 3219905) B3219905
theorem B2862137 : Blo 1907435 2862137 := bstep (se 2 (by rfl) ⟨1073301, by rfl⟩ : syracuseStep 2862137 = 2146603) B2146603
theorem B1908091 : Blo 1907435 1908091 := bstep (se 1 (by rfl) ⟨1431068, by rfl⟩ : syracuseStep 1908091 = 2862137) B2862137
theorem B2292301 : Blo 1907435 2292301 := bbase (se 3 (by rfl) ⟨429806, by rfl⟩ : syracuseStep 2292301 = 859613) (by norm_num)
theorem B3056401 : Blo 1907435 3056401 := bstep (se 2 (by rfl) ⟨1146150, by rfl⟩ : syracuseStep 3056401 = 2292301) B2292301
theorem B4075201 : Blo 1907435 4075201 := bstep (se 2 (by rfl) ⟨1528200, by rfl⟩ : syracuseStep 4075201 = 3056401) B3056401
theorem B21734405 : Blo 1907435 21734405 := bstep (se 4 (by rfl) ⟨2037600, by rfl⟩ : syracuseStep 21734405 = 4075201) B4075201
theorem B14489603 : Blo 1907435 14489603 := bstep (se 1 (by rfl) ⟨10867202, by rfl⟩ : syracuseStep 14489603 = 21734405) B21734405
theorem B9659735 : Blo 1907435 9659735 := bstep (se 1 (by rfl) ⟨7244801, by rfl⟩ : syracuseStep 9659735 = 14489603) B14489603
theorem B6439823 : Blo 1907435 6439823 := bstep (se 1 (by rfl) ⟨4829867, by rfl⟩ : syracuseStep 6439823 = 9659735) B9659735
theorem B4293215 : Blo 1907435 4293215 := bstep (se 1 (by rfl) ⟨3219911, by rfl⟩ : syracuseStep 4293215 = 6439823) B6439823
theorem B2862143 : Blo 1907435 2862143 := bstep (se 1 (by rfl) ⟨2146607, by rfl⟩ : syracuseStep 2862143 = 4293215) B4293215
theorem B1908095 : Blo 1907435 1908095 := bstep (se 1 (by rfl) ⟨1431071, by rfl⟩ : syracuseStep 1908095 = 2862143) B2862143
theorem B2862149 : Blo 1907435 2862149 := bbase (se 4 (by rfl) ⟨268326, by rfl⟩ : syracuseStep 2862149 = 536653) (by norm_num)
theorem B1908099 : Blo 1907435 1908099 := bstep (se 1 (by rfl) ⟨1431074, by rfl⟩ : syracuseStep 1908099 = 2862149) B2862149
theorem B3219925 : Blo 1907435 3219925 := bbase (se 7 (by rfl) ⟨37733, by rfl⟩ : syracuseStep 3219925 = 75467) (by norm_num)
theorem B4293233 : Blo 1907435 4293233 := bstep (se 2 (by rfl) ⟨1609962, by rfl⟩ : syracuseStep 4293233 = 3219925) B3219925
theorem B2862155 : Blo 1907435 2862155 := bstep (se 1 (by rfl) ⟨2146616, by rfl⟩ : syracuseStep 2862155 = 4293233) B4293233
theorem B1908103 : Blo 1907435 1908103 := bstep (se 1 (by rfl) ⟨1431077, by rfl⟩ : syracuseStep 1908103 = 2862155) B2862155
theorem B2146621 : Blo 1907435 2146621 := bbase (se 3 (by rfl) ⟨402491, by rfl⟩ : syracuseStep 2146621 = 804983) (by norm_num)
theorem B2862161 : Blo 1907435 2862161 := bstep (se 2 (by rfl) ⟨1073310, by rfl⟩ : syracuseStep 2862161 = 2146621) B2146621
theorem B1908107 : Blo 1907435 1908107 := bstep (se 1 (by rfl) ⟨1431080, by rfl⟩ : syracuseStep 1908107 = 2862161) B2862161
theorem B6439877 : Blo 1907435 6439877 := bbase (se 4 (by rfl) ⟨603738, by rfl⟩ : syracuseStep 6439877 = 1207477) (by norm_num)
theorem B4293251 : Blo 1907435 4293251 := bstep (se 1 (by rfl) ⟨3219938, by rfl⟩ : syracuseStep 4293251 = 6439877) B6439877
theorem B2862167 : Blo 1907435 2862167 := bstep (se 1 (by rfl) ⟨2146625, by rfl⟩ : syracuseStep 2862167 = 4293251) B4293251
theorem B1908111 : Blo 1907435 1908111 := bstep (se 1 (by rfl) ⟨1431083, by rfl⟩ : syracuseStep 1908111 = 2862167) B2862167
theorem B2862173 : Blo 1907435 2862173 := bbase (se 3 (by rfl) ⟨536657, by rfl⟩ : syracuseStep 2862173 = 1073315) (by norm_num)
theorem B1908115 : Blo 1907435 1908115 := bstep (se 1 (by rfl) ⟨1431086, by rfl⟩ : syracuseStep 1908115 = 2862173) B2862173
theorem B4293269 : Blo 1907435 4293269 := bbase (se 6 (by rfl) ⟨100623, by rfl⟩ : syracuseStep 4293269 = 201247) (by norm_num)
theorem B2862179 : Blo 1907435 2862179 := bstep (se 1 (by rfl) ⟨2146634, by rfl⟩ : syracuseStep 2862179 = 4293269) B4293269
theorem B1908119 : Blo 1907435 1908119 := bstep (se 1 (by rfl) ⟨1431089, by rfl⟩ : syracuseStep 1908119 = 2862179) B2862179
theorem B4962637 : Blo 1907435 4962637 := bbase (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) (by norm_num)
theorem B6616849 : Blo 1907435 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B8822465 : Blo 1907435 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B5881643 : Blo 1907435 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3921095 : Blo 1907435 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B10456253 : Blo 1907435 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B6970835 : Blo 1907435 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B4647223 : Blo 1907435 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B24785189 : Blo 1907435 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B16523459 : Blo 1907435 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B11015639 : Blo 1907435 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B7343759 : Blo 1907435 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B4895839 : Blo 1907435 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B6527785 : Blo 1907435 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B8703713 : Blo 1907435 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B23209901 : Blo 1907435 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B15473267 : Blo 1907435 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B10315511 : Blo 1907435 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B6877007 : Blo 1907435 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B4584671 : Blo 1907435 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B3056447 : Blo 1907435 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B2037631 : Blo 1907435 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B2716841 : Blo 1907435 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B7244909 : Blo 1907435 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B4829939 : Blo 1907435 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B3219959 : Blo 1907435 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B2146639 : Blo 1907435 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B2862185 : Blo 1907435 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B1908123 : Blo 1907435 1908123 := bstep (se 1 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 1908123 = 2862185) B2862185
theorem B3438509 : Blo 1907435 3438509 := bbase (se 3 (by rfl) ⟨644720, by rfl⟩ : syracuseStep 3438509 = 1289441) (by norm_num)
theorem B9169357 : Blo 1907435 9169357 := bstep (se 3 (by rfl) ⟨1719254, by rfl⟩ : syracuseStep 9169357 = 3438509) B3438509
theorem B12225809 : Blo 1907435 12225809 := bstep (se 2 (by rfl) ⟨4584678, by rfl⟩ : syracuseStep 12225809 = 9169357) B9169357
theorem B8150539 : Blo 1907435 8150539 := bstep (se 1 (by rfl) ⟨6112904, by rfl⟩ : syracuseStep 8150539 = 12225809) B12225809
theorem B10867385 : Blo 1907435 10867385 := bstep (se 2 (by rfl) ⟨4075269, by rfl⟩ : syracuseStep 10867385 = 8150539) B8150539
theorem B7244923 : Blo 1907435 7244923 := bstep (se 1 (by rfl) ⟨5433692, by rfl⟩ : syracuseStep 7244923 = 10867385) B10867385
theorem B9659897 : Blo 1907435 9659897 := bstep (se 2 (by rfl) ⟨3622461, by rfl⟩ : syracuseStep 9659897 = 7244923) B7244923
theorem B6439931 : Blo 1907435 6439931 := bstep (se 1 (by rfl) ⟨4829948, by rfl⟩ : syracuseStep 6439931 = 9659897) B9659897
theorem B4293287 : Blo 1907435 4293287 := bstep (se 1 (by rfl) ⟨3219965, by rfl⟩ : syracuseStep 4293287 = 6439931) B6439931
theorem B2862191 : Blo 1907435 2862191 := bstep (se 1 (by rfl) ⟨2146643, by rfl⟩ : syracuseStep 2862191 = 4293287) B4293287
theorem B1908127 : Blo 1907435 1908127 := bstep (se 1 (by rfl) ⟨1431095, by rfl⟩ : syracuseStep 1908127 = 2862191) B2862191
theorem B2862197 : Blo 1907435 2862197 := bbase (se 5 (by rfl) ⟨134165, by rfl⟩ : syracuseStep 2862197 = 268331) (by norm_num)
theorem B1908131 : Blo 1907435 1908131 := bstep (se 1 (by rfl) ⟨1431098, by rfl⟩ : syracuseStep 1908131 = 2862197) B2862197
theorem B3622477 : Blo 1907435 3622477 := bbase (se 3 (by rfl) ⟨679214, by rfl⟩ : syracuseStep 3622477 = 1358429) (by norm_num)
theorem B4829969 : Blo 1907435 4829969 := bstep (se 2 (by rfl) ⟨1811238, by rfl⟩ : syracuseStep 4829969 = 3622477) B3622477
theorem B3219979 : Blo 1907435 3219979 := bstep (se 1 (by rfl) ⟨2414984, by rfl⟩ : syracuseStep 3219979 = 4829969) B4829969
theorem B4293305 : Blo 1907435 4293305 := bstep (se 2 (by rfl) ⟨1609989, by rfl⟩ : syracuseStep 4293305 = 3219979) B3219979
theorem B2862203 : Blo 1907435 2862203 := bstep (se 1 (by rfl) ⟨2146652, by rfl⟩ : syracuseStep 2862203 = 4293305) B4293305
theorem B1908135 : Blo 1907435 1908135 := bstep (se 1 (by rfl) ⟨1431101, by rfl⟩ : syracuseStep 1908135 = 2862203) B2862203
theorem B2146657 : Blo 1907435 2146657 := bbase (se 2 (by rfl) ⟨804996, by rfl⟩ : syracuseStep 2146657 = 1609993) (by norm_num)
theorem B2862209 : Blo 1907435 2862209 := bstep (se 2 (by rfl) ⟨1073328, by rfl⟩ : syracuseStep 2862209 = 2146657) B2146657
theorem B1908139 : Blo 1907435 1908139 := bstep (se 1 (by rfl) ⟨1431104, by rfl⟩ : syracuseStep 1908139 = 2862209) B2862209
theorem B4829989 : Blo 1907435 4829989 := bbase (se 4 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 4829989 = 905623) (by norm_num)
theorem B6439985 : Blo 1907435 6439985 := bstep (se 2 (by rfl) ⟨2414994, by rfl⟩ : syracuseStep 6439985 = 4829989) B4829989
theorem B4293323 : Blo 1907435 4293323 := bstep (se 1 (by rfl) ⟨3219992, by rfl⟩ : syracuseStep 4293323 = 6439985) B6439985
theorem B2862215 : Blo 1907435 2862215 := bstep (se 1 (by rfl) ⟨2146661, by rfl⟩ : syracuseStep 2862215 = 4293323) B4293323
theorem B1908143 : Blo 1907435 1908143 := bstep (se 1 (by rfl) ⟨1431107, by rfl⟩ : syracuseStep 1908143 = 2862215) B2862215
theorem B2862221 : Blo 1907435 2862221 := bbase (se 3 (by rfl) ⟨536666, by rfl⟩ : syracuseStep 2862221 = 1073333) (by norm_num)
theorem B1908147 : Blo 1907435 1908147 := bstep (se 1 (by rfl) ⟨1431110, by rfl⟩ : syracuseStep 1908147 = 2862221) B2862221
theorem B4293341 : Blo 1907435 4293341 := bbase (se 3 (by rfl) ⟨805001, by rfl⟩ : syracuseStep 4293341 = 1610003) (by norm_num)
theorem B2862227 : Blo 1907435 2862227 := bstep (se 1 (by rfl) ⟨2146670, by rfl⟩ : syracuseStep 2862227 = 4293341) B4293341
theorem B1908151 : Blo 1907435 1908151 := bstep (se 1 (by rfl) ⟨1431113, by rfl⟩ : syracuseStep 1908151 = 2862227) B2862227
theorem B3220013 : Blo 1907435 3220013 := bbase (se 3 (by rfl) ⟨603752, by rfl⟩ : syracuseStep 3220013 = 1207505) (by norm_num)
theorem B2146675 : Blo 1907435 2146675 := bstep (se 1 (by rfl) ⟨1610006, by rfl⟩ : syracuseStep 2146675 = 3220013) B3220013
theorem B2862233 : Blo 1907435 2862233 := bstep (se 2 (by rfl) ⟨1073337, by rfl⟩ : syracuseStep 2862233 = 2146675) B2146675
theorem B1908155 : Blo 1907435 1908155 := bstep (se 1 (by rfl) ⟨1431116, by rfl⟩ : syracuseStep 1908155 = 2862233) B2862233
theorem B5802581 : Blo 1907435 5802581 := bbase (se 8 (by rfl) ⟨33999, by rfl⟩ : syracuseStep 5802581 = 67999) (by norm_num)
theorem B15473549 : Blo 1907435 15473549 := bstep (se 3 (by rfl) ⟨2901290, by rfl⟩ : syracuseStep 15473549 = 5802581) B5802581
theorem B41262797 : Blo 1907435 41262797 := bstep (se 3 (by rfl) ⟨7736774, by rfl⟩ : syracuseStep 41262797 = 15473549) B15473549
theorem B27508531 : Blo 1907435 27508531 := bstep (se 1 (by rfl) ⟨20631398, by rfl⟩ : syracuseStep 27508531 = 41262797) B41262797
theorem B36678041 : Blo 1907435 36678041 := bstep (se 2 (by rfl) ⟨13754265, by rfl⟩ : syracuseStep 36678041 = 27508531) B27508531
theorem B24452027 : Blo 1907435 24452027 := bstep (se 1 (by rfl) ⟨18339020, by rfl⟩ : syracuseStep 24452027 = 36678041) B36678041
theorem B16301351 : Blo 1907435 16301351 := bstep (se 1 (by rfl) ⟨12226013, by rfl⟩ : syracuseStep 16301351 = 24452027) B24452027
theorem B10867567 : Blo 1907435 10867567 := bstep (se 1 (by rfl) ⟨8150675, by rfl⟩ : syracuseStep 10867567 = 16301351) B16301351
theorem B14490089 : Blo 1907435 14490089 := bstep (se 2 (by rfl) ⟨5433783, by rfl⟩ : syracuseStep 14490089 = 10867567) B10867567
theorem B9660059 : Blo 1907435 9660059 := bstep (se 1 (by rfl) ⟨7245044, by rfl⟩ : syracuseStep 9660059 = 14490089) B14490089
theorem B6440039 : Blo 1907435 6440039 := bstep (se 1 (by rfl) ⟨4830029, by rfl⟩ : syracuseStep 6440039 = 9660059) B9660059
theorem B4293359 : Blo 1907435 4293359 := bstep (se 1 (by rfl) ⟨3220019, by rfl⟩ : syracuseStep 4293359 = 6440039) B6440039
theorem B2862239 : Blo 1907435 2862239 := bstep (se 1 (by rfl) ⟨2146679, by rfl⟩ : syracuseStep 2862239 = 4293359) B4293359
theorem B1908159 : Blo 1907435 1908159 := bstep (se 1 (by rfl) ⟨1431119, by rfl⟩ : syracuseStep 1908159 = 2862239) B2862239
theorem B2862245 : Blo 1907435 2862245 := bbase (se 4 (by rfl) ⟨268335, by rfl⟩ : syracuseStep 2862245 = 536671) (by norm_num)
theorem B1908163 : Blo 1907435 1908163 := bstep (se 1 (by rfl) ⟨1431122, by rfl⟩ : syracuseStep 1908163 = 2862245) B2862245
theorem B2415025 : Blo 1907435 2415025 := bbase (se 2 (by rfl) ⟨905634, by rfl⟩ : syracuseStep 2415025 = 1811269) (by norm_num)
theorem B3220033 : Blo 1907435 3220033 := bstep (se 2 (by rfl) ⟨1207512, by rfl⟩ : syracuseStep 3220033 = 2415025) B2415025
theorem B4293377 : Blo 1907435 4293377 := bstep (se 2 (by rfl) ⟨1610016, by rfl⟩ : syracuseStep 4293377 = 3220033) B3220033
theorem B2862251 : Blo 1907435 2862251 := bstep (se 1 (by rfl) ⟨2146688, by rfl⟩ : syracuseStep 2862251 = 4293377) B4293377
theorem B1908167 : Blo 1907435 1908167 := bstep (se 1 (by rfl) ⟨1431125, by rfl⟩ : syracuseStep 1908167 = 2862251) B2862251
theorem B2146693 : Blo 1907435 2146693 := bbase (se 4 (by rfl) ⟨201252, by rfl⟩ : syracuseStep 2146693 = 402505) (by norm_num)
theorem B2862257 : Blo 1907435 2862257 := bstep (se 2 (by rfl) ⟨1073346, by rfl⟩ : syracuseStep 2862257 = 2146693) B2146693
theorem B1908171 : Blo 1907435 1908171 := bstep (se 1 (by rfl) ⟨1431128, by rfl⟩ : syracuseStep 1908171 = 2862257) B2862257
theorem B4075373 : Blo 1907435 4075373 := bbase (se 3 (by rfl) ⟨764132, by rfl⟩ : syracuseStep 4075373 = 1528265) (by norm_num)
theorem B2716915 : Blo 1907435 2716915 := bstep (se 1 (by rfl) ⟨2037686, by rfl⟩ : syracuseStep 2716915 = 4075373) B4075373
theorem B3622553 : Blo 1907435 3622553 := bstep (se 2 (by rfl) ⟨1358457, by rfl⟩ : syracuseStep 3622553 = 2716915) B2716915
theorem B2415035 : Blo 1907435 2415035 := bstep (se 1 (by rfl) ⟨1811276, by rfl⟩ : syracuseStep 2415035 = 3622553) B3622553
theorem B6440093 : Blo 1907435 6440093 := bstep (se 3 (by rfl) ⟨1207517, by rfl⟩ : syracuseStep 6440093 = 2415035) B2415035
theorem B4293395 : Blo 1907435 4293395 := bstep (se 1 (by rfl) ⟨3220046, by rfl⟩ : syracuseStep 4293395 = 6440093) B6440093
theorem B2862263 : Blo 1907435 2862263 := bstep (se 1 (by rfl) ⟨2146697, by rfl⟩ : syracuseStep 2862263 = 4293395) B4293395
theorem B1908175 : Blo 1907435 1908175 := bstep (se 1 (by rfl) ⟨1431131, by rfl⟩ : syracuseStep 1908175 = 2862263) B2862263
theorem B2862269 : Blo 1907435 2862269 := bbase (se 3 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 2862269 = 1073351) (by norm_num)
theorem B1908179 : Blo 1907435 1908179 := bstep (se 1 (by rfl) ⟨1431134, by rfl⟩ : syracuseStep 1908179 = 2862269) B2862269
theorem B4293413 : Blo 1907435 4293413 := bbase (se 4 (by rfl) ⟨402507, by rfl⟩ : syracuseStep 4293413 = 805015) (by norm_num)
theorem B2862275 : Blo 1907435 2862275 := bstep (se 1 (by rfl) ⟨2146706, by rfl⟩ : syracuseStep 2862275 = 4293413) B4293413
theorem B1908183 : Blo 1907435 1908183 := bstep (se 1 (by rfl) ⟨1431137, by rfl⟩ : syracuseStep 1908183 = 2862275) B2862275
theorem B4830101 : Blo 1907435 4830101 := bbase (se 6 (by rfl) ⟨113205, by rfl⟩ : syracuseStep 4830101 = 226411) (by norm_num)
theorem B3220067 : Blo 1907435 3220067 := bstep (se 1 (by rfl) ⟨2415050, by rfl⟩ : syracuseStep 3220067 = 4830101) B4830101
theorem B2146711 : Blo 1907435 2146711 := bstep (se 1 (by rfl) ⟨1610033, by rfl⟩ : syracuseStep 2146711 = 3220067) B3220067
theorem B2862281 : Blo 1907435 2862281 := bstep (se 2 (by rfl) ⟨1073355, by rfl⟩ : syracuseStep 2862281 = 2146711) B2146711
theorem B1908187 : Blo 1907435 1908187 := bstep (se 1 (by rfl) ⟨1431140, by rfl⟩ : syracuseStep 1908187 = 2862281) B2862281
theorem B2901341 : Blo 1907435 2901341 := bbase (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) (by norm_num)
theorem B1934227 : Blo 1907435 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B2578969 : Blo 1907435 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B3438625 : Blo 1907435 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B4584833 : Blo 1907435 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B3056555 : Blo 1907435 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B8150813 : Blo 1907435 8150813 := bstep (se 3 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 8150813 = 3056555) B3056555
theorem B5433875 : Blo 1907435 5433875 := bstep (se 1 (by rfl) ⟨4075406, by rfl⟩ : syracuseStep 5433875 = 8150813) B8150813
theorem B3622583 : Blo 1907435 3622583 := bstep (se 1 (by rfl) ⟨2716937, by rfl⟩ : syracuseStep 3622583 = 5433875) B5433875
theorem B9660221 : Blo 1907435 9660221 := bstep (se 3 (by rfl) ⟨1811291, by rfl⟩ : syracuseStep 9660221 = 3622583) B3622583
theorem B6440147 : Blo 1907435 6440147 := bstep (se 1 (by rfl) ⟨4830110, by rfl⟩ : syracuseStep 6440147 = 9660221) B9660221
theorem B4293431 : Blo 1907435 4293431 := bstep (se 1 (by rfl) ⟨3220073, by rfl⟩ : syracuseStep 4293431 = 6440147) B6440147
theorem B2862287 : Blo 1907435 2862287 := bstep (se 1 (by rfl) ⟨2146715, by rfl⟩ : syracuseStep 2862287 = 4293431) B4293431
theorem B1908191 : Blo 1907435 1908191 := bstep (se 1 (by rfl) ⟨1431143, by rfl⟩ : syracuseStep 1908191 = 2862287) B2862287
theorem B2862293 : Blo 1907435 2862293 := bbase (se 7 (by rfl) ⟨33542, by rfl⟩ : syracuseStep 2862293 = 67085) (by norm_num)
theorem B1908195 : Blo 1907435 1908195 := bstep (se 1 (by rfl) ⟨1431146, by rfl⟩ : syracuseStep 1908195 = 2862293) B2862293
theorem B2716949 : Blo 1907435 2716949 := bbase (se 6 (by rfl) ⟨63678, by rfl⟩ : syracuseStep 2716949 = 127357) (by norm_num)
theorem B7245197 : Blo 1907435 7245197 := bstep (se 3 (by rfl) ⟨1358474, by rfl⟩ : syracuseStep 7245197 = 2716949) B2716949
theorem B4830131 : Blo 1907435 4830131 := bstep (se 1 (by rfl) ⟨3622598, by rfl⟩ : syracuseStep 4830131 = 7245197) B7245197
theorem B3220087 : Blo 1907435 3220087 := bstep (se 1 (by rfl) ⟨2415065, by rfl⟩ : syracuseStep 3220087 = 4830131) B4830131
theorem B4293449 : Blo 1907435 4293449 := bstep (se 2 (by rfl) ⟨1610043, by rfl⟩ : syracuseStep 4293449 = 3220087) B3220087
theorem B2862299 : Blo 1907435 2862299 := bstep (se 1 (by rfl) ⟨2146724, by rfl⟩ : syracuseStep 2862299 = 4293449) B4293449
theorem B1908199 : Blo 1907435 1908199 := bstep (se 1 (by rfl) ⟨1431149, by rfl⟩ : syracuseStep 1908199 = 2862299) B2862299
theorem B2146729 : Blo 1907435 2146729 := bbase (se 2 (by rfl) ⟨805023, by rfl⟩ : syracuseStep 2146729 = 1610047) (by norm_num)
theorem B2862305 : Blo 1907435 2862305 := bstep (se 2 (by rfl) ⟨1073364, by rfl⟩ : syracuseStep 2862305 = 2146729) B2146729
theorem B1908203 : Blo 1907435 1908203 := bstep (se 1 (by rfl) ⟨1431152, by rfl⟩ : syracuseStep 1908203 = 2862305) B2862305
theorem B4896053 : Blo 1907435 4896053 := bbase (se 5 (by rfl) ⟨229502, by rfl⟩ : syracuseStep 4896053 = 459005) (by norm_num)
theorem B3264035 : Blo 1907435 3264035 := bstep (se 1 (by rfl) ⟨2448026, by rfl⟩ : syracuseStep 3264035 = 4896053) B4896053
theorem B8704093 : Blo 1907435 8704093 := bstep (se 3 (by rfl) ⟨1632017, by rfl⟩ : syracuseStep 8704093 = 3264035) B3264035
theorem B11605457 : Blo 1907435 11605457 := bstep (se 2 (by rfl) ⟨4352046, by rfl⟩ : syracuseStep 11605457 = 8704093) B8704093
theorem B7736971 : Blo 1907435 7736971 := bstep (se 1 (by rfl) ⟨5802728, by rfl⟩ : syracuseStep 7736971 = 11605457) B11605457
theorem B10315961 : Blo 1907435 10315961 := bstep (se 2 (by rfl) ⟨3868485, by rfl⟩ : syracuseStep 10315961 = 7736971) B7736971
theorem B6877307 : Blo 1907435 6877307 := bstep (se 1 (by rfl) ⟨5157980, by rfl⟩ : syracuseStep 6877307 = 10315961) B10315961
theorem B4584871 : Blo 1907435 4584871 := bstep (se 1 (by rfl) ⟨3438653, by rfl⟩ : syracuseStep 4584871 = 6877307) B6877307
theorem B6113161 : Blo 1907435 6113161 := bstep (se 2 (by rfl) ⟨2292435, by rfl⟩ : syracuseStep 6113161 = 4584871) B4584871
theorem B8150881 : Blo 1907435 8150881 := bstep (se 2 (by rfl) ⟨3056580, by rfl⟩ : syracuseStep 8150881 = 6113161) B6113161
theorem B10867841 : Blo 1907435 10867841 := bstep (se 2 (by rfl) ⟨4075440, by rfl⟩ : syracuseStep 10867841 = 8150881) B8150881
theorem B7245227 : Blo 1907435 7245227 := bstep (se 1 (by rfl) ⟨5433920, by rfl⟩ : syracuseStep 7245227 = 10867841) B10867841
theorem B4830151 : Blo 1907435 4830151 := bstep (se 1 (by rfl) ⟨3622613, by rfl⟩ : syracuseStep 4830151 = 7245227) B7245227
theorem B6440201 : Blo 1907435 6440201 := bstep (se 2 (by rfl) ⟨2415075, by rfl⟩ : syracuseStep 6440201 = 4830151) B4830151
theorem B4293467 : Blo 1907435 4293467 := bstep (se 1 (by rfl) ⟨3220100, by rfl⟩ : syracuseStep 4293467 = 6440201) B6440201
theorem B2862311 : Blo 1907435 2862311 := bstep (se 1 (by rfl) ⟨2146733, by rfl⟩ : syracuseStep 2862311 = 4293467) B4293467
theorem B1908207 : Blo 1907435 1908207 := bstep (se 1 (by rfl) ⟨1431155, by rfl⟩ : syracuseStep 1908207 = 2862311) B2862311
theorem B2862317 : Blo 1907435 2862317 := bbase (se 3 (by rfl) ⟨536684, by rfl⟩ : syracuseStep 2862317 = 1073369) (by norm_num)
theorem B1908211 : Blo 1907435 1908211 := bstep (se 1 (by rfl) ⟨1431158, by rfl⟩ : syracuseStep 1908211 = 2862317) B2862317
theorem B4293485 : Blo 1907435 4293485 := bbase (se 3 (by rfl) ⟨805028, by rfl⟩ : syracuseStep 4293485 = 1610057) (by norm_num)
theorem B2862323 : Blo 1907435 2862323 := bstep (se 1 (by rfl) ⟨2146742, by rfl⟩ : syracuseStep 2862323 = 4293485) B4293485
theorem B1908215 : Blo 1907435 1908215 := bstep (se 1 (by rfl) ⟨1431161, by rfl⟩ : syracuseStep 1908215 = 2862323) B2862323
theorem B3622637 : Blo 1907435 3622637 := bbase (se 3 (by rfl) ⟨679244, by rfl⟩ : syracuseStep 3622637 = 1358489) (by norm_num)
theorem B2415091 : Blo 1907435 2415091 := bstep (se 1 (by rfl) ⟨1811318, by rfl⟩ : syracuseStep 2415091 = 3622637) B3622637
theorem B3220121 : Blo 1907435 3220121 := bstep (se 2 (by rfl) ⟨1207545, by rfl⟩ : syracuseStep 3220121 = 2415091) B2415091
theorem B2146747 : Blo 1907435 2146747 := bstep (se 1 (by rfl) ⟨1610060, by rfl⟩ : syracuseStep 2146747 = 3220121) B3220121
theorem B2862329 : Blo 1907435 2862329 := bstep (se 2 (by rfl) ⟨1073373, by rfl⟩ : syracuseStep 2862329 = 2146747) B2146747
theorem B1908219 : Blo 1907435 1908219 := bstep (se 1 (by rfl) ⟨1431164, by rfl⟩ : syracuseStep 1908219 = 2862329) B2862329
theorem B3868517 : Blo 1907435 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B10316045 : Blo 1907435 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B27509453 : Blo 1907435 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B18339635 : Blo 1907435 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B48905693 : Blo 1907435 48905693 := bstep (se 3 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 48905693 = 18339635) B18339635
theorem B32603795 : Blo 1907435 32603795 := bstep (se 1 (by rfl) ⟨24452846, by rfl⟩ : syracuseStep 32603795 = 48905693) B48905693
theorem B21735863 : Blo 1907435 21735863 := bstep (se 1 (by rfl) ⟨16301897, by rfl⟩ : syracuseStep 21735863 = 32603795) B32603795
theorem B14490575 : Blo 1907435 14490575 := bstep (se 1 (by rfl) ⟨10867931, by rfl⟩ : syracuseStep 14490575 = 21735863) B21735863
theorem B9660383 : Blo 1907435 9660383 := bstep (se 1 (by rfl) ⟨7245287, by rfl⟩ : syracuseStep 9660383 = 14490575) B14490575
theorem B6440255 : Blo 1907435 6440255 := bstep (se 1 (by rfl) ⟨4830191, by rfl⟩ : syracuseStep 6440255 = 9660383) B9660383
theorem B4293503 : Blo 1907435 4293503 := bstep (se 1 (by rfl) ⟨3220127, by rfl⟩ : syracuseStep 4293503 = 6440255) B6440255
theorem B2862335 : Blo 1907435 2862335 := bstep (se 1 (by rfl) ⟨2146751, by rfl⟩ : syracuseStep 2862335 = 4293503) B4293503
theorem B1908223 : Blo 1907435 1908223 := bstep (se 1 (by rfl) ⟨1431167, by rfl⟩ : syracuseStep 1908223 = 2862335) B2862335
theorem B2862341 : Blo 1907435 2862341 := bbase (se 4 (by rfl) ⟨268344, by rfl⟩ : syracuseStep 2862341 = 536689) (by norm_num)
theorem B1908227 : Blo 1907435 1908227 := bstep (se 1 (by rfl) ⟨1431170, by rfl⟩ : syracuseStep 1908227 = 2862341) B2862341
theorem B3220141 : Blo 1907435 3220141 := bbase (se 3 (by rfl) ⟨603776, by rfl⟩ : syracuseStep 3220141 = 1207553) (by norm_num)
theorem B4293521 : Blo 1907435 4293521 := bstep (se 2 (by rfl) ⟨1610070, by rfl⟩ : syracuseStep 4293521 = 3220141) B3220141
theorem B2862347 : Blo 1907435 2862347 := bstep (se 1 (by rfl) ⟨2146760, by rfl⟩ : syracuseStep 2862347 = 4293521) B4293521
theorem B1908231 : Blo 1907435 1908231 := bstep (se 1 (by rfl) ⟨1431173, by rfl⟩ : syracuseStep 1908231 = 2862347) B2862347
theorem B2146765 : Blo 1907435 2146765 := bbase (se 3 (by rfl) ⟨402518, by rfl⟩ : syracuseStep 2146765 = 805037) (by norm_num)
theorem B2862353 : Blo 1907435 2862353 := bstep (se 2 (by rfl) ⟨1073382, by rfl⟩ : syracuseStep 2862353 = 2146765) B2146765
theorem B1908235 : Blo 1907435 1908235 := bstep (se 1 (by rfl) ⟨1431176, by rfl⟩ : syracuseStep 1908235 = 2862353) B2862353
theorem B6440309 : Blo 1907435 6440309 := bbase (se 5 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 6440309 = 603779) (by norm_num)
theorem B4293539 : Blo 1907435 4293539 := bstep (se 1 (by rfl) ⟨3220154, by rfl⟩ : syracuseStep 4293539 = 6440309) B6440309
theorem B2862359 : Blo 1907435 2862359 := bstep (se 1 (by rfl) ⟨2146769, by rfl⟩ : syracuseStep 2862359 = 4293539) B4293539
theorem B1908239 : Blo 1907435 1908239 := bstep (se 1 (by rfl) ⟨1431179, by rfl⟩ : syracuseStep 1908239 = 2862359) B2862359
theorem B2862365 : Blo 1907435 2862365 := bbase (se 3 (by rfl) ⟨536693, by rfl⟩ : syracuseStep 2862365 = 1073387) (by norm_num)
theorem B1908243 : Blo 1907435 1908243 := bstep (se 1 (by rfl) ⟨1431182, by rfl⟩ : syracuseStep 1908243 = 2862365) B2862365
theorem B4293557 : Blo 1907435 4293557 := bbase (se 5 (by rfl) ⟨201260, by rfl⟩ : syracuseStep 4293557 = 402521) (by norm_num)
theorem B2862371 : Blo 1907435 2862371 := bstep (se 1 (by rfl) ⟨2146778, by rfl⟩ : syracuseStep 2862371 = 4293557) B4293557
theorem B1908247 : Blo 1907435 1908247 := bstep (se 1 (by rfl) ⟨1431185, by rfl⟩ : syracuseStep 1908247 = 2862371) B2862371
theorem B13754933 : Blo 1907435 13754933 := bbase (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) (by norm_num)
theorem B9169955 : Blo 1907435 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B6113303 : Blo 1907435 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B4075535 : Blo 1907435 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B10868093 : Blo 1907435 10868093 := bstep (se 3 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 10868093 = 4075535) B4075535
theorem B7245395 : Blo 1907435 7245395 := bstep (se 1 (by rfl) ⟨5434046, by rfl⟩ : syracuseStep 7245395 = 10868093) B10868093
theorem B4830263 : Blo 1907435 4830263 := bstep (se 1 (by rfl) ⟨3622697, by rfl⟩ : syracuseStep 4830263 = 7245395) B7245395
theorem B3220175 : Blo 1907435 3220175 := bstep (se 1 (by rfl) ⟨2415131, by rfl⟩ : syracuseStep 3220175 = 4830263) B4830263
theorem B2146783 : Blo 1907435 2146783 := bstep (se 1 (by rfl) ⟨1610087, by rfl⟩ : syracuseStep 2146783 = 3220175) B3220175
theorem B2862377 : Blo 1907435 2862377 := bstep (se 2 (by rfl) ⟨1073391, by rfl⟩ : syracuseStep 2862377 = 2146783) B2146783
theorem B1908251 : Blo 1907435 1908251 := bstep (se 1 (by rfl) ⟨1431188, by rfl⟩ : syracuseStep 1908251 = 2862377) B2862377
theorem B9169973 : Blo 1907435 9169973 := bbase (se 5 (by rfl) ⟨429842, by rfl⟩ : syracuseStep 9169973 = 859685) (by norm_num)
theorem B6113315 : Blo 1907435 6113315 := bstep (se 1 (by rfl) ⟨4584986, by rfl⟩ : syracuseStep 6113315 = 9169973) B9169973
theorem B4075543 : Blo 1907435 4075543 := bstep (se 1 (by rfl) ⟨3056657, by rfl⟩ : syracuseStep 4075543 = 6113315) B6113315
theorem B5434057 : Blo 1907435 5434057 := bstep (se 2 (by rfl) ⟨2037771, by rfl⟩ : syracuseStep 5434057 = 4075543) B4075543
theorem B7245409 : Blo 1907435 7245409 := bstep (se 2 (by rfl) ⟨2717028, by rfl⟩ : syracuseStep 7245409 = 5434057) B5434057
theorem B9660545 : Blo 1907435 9660545 := bstep (se 2 (by rfl) ⟨3622704, by rfl⟩ : syracuseStep 9660545 = 7245409) B7245409
theorem B6440363 : Blo 1907435 6440363 := bstep (se 1 (by rfl) ⟨4830272, by rfl⟩ : syracuseStep 6440363 = 9660545) B9660545
theorem B4293575 : Blo 1907435 4293575 := bstep (se 1 (by rfl) ⟨3220181, by rfl⟩ : syracuseStep 4293575 = 6440363) B6440363
theorem B2862383 : Blo 1907435 2862383 := bstep (se 1 (by rfl) ⟨2146787, by rfl⟩ : syracuseStep 2862383 = 4293575) B4293575
theorem B1908255 : Blo 1907435 1908255 := bstep (se 1 (by rfl) ⟨1431191, by rfl⟩ : syracuseStep 1908255 = 2862383) B2862383
theorem B2862389 : Blo 1907435 2862389 := bbase (se 5 (by rfl) ⟨134174, by rfl⟩ : syracuseStep 2862389 = 268349) (by norm_num)
theorem B1908259 : Blo 1907435 1908259 := bstep (se 1 (by rfl) ⟨1431194, by rfl⟩ : syracuseStep 1908259 = 2862389) B2862389
theorem B4830293 : Blo 1907435 4830293 := bbase (se 8 (by rfl) ⟨28302, by rfl⟩ : syracuseStep 4830293 = 56605) (by norm_num)
theorem B3220195 : Blo 1907435 3220195 := bstep (se 1 (by rfl) ⟨2415146, by rfl⟩ : syracuseStep 3220195 = 4830293) B4830293
theorem B4293593 : Blo 1907435 4293593 := bstep (se 2 (by rfl) ⟨1610097, by rfl⟩ : syracuseStep 4293593 = 3220195) B3220195
theorem B2862395 : Blo 1907435 2862395 := bstep (se 1 (by rfl) ⟨2146796, by rfl⟩ : syracuseStep 2862395 = 4293593) B4293593
theorem B1908263 : Blo 1907435 1908263 := bstep (se 1 (by rfl) ⟨1431197, by rfl⟩ : syracuseStep 1908263 = 2862395) B2862395
theorem B2146801 : Blo 1907435 2146801 := bbase (se 2 (by rfl) ⟨805050, by rfl⟩ : syracuseStep 2146801 = 1610101) (by norm_num)
theorem B2862401 : Blo 1907435 2862401 := bstep (se 2 (by rfl) ⟨1073400, by rfl⟩ : syracuseStep 2862401 = 2146801) B2146801
theorem B1908267 : Blo 1907435 1908267 := bstep (se 1 (by rfl) ⟨1431200, by rfl⟩ : syracuseStep 1908267 = 2862401) B2862401
theorem B2579077 : Blo 1907435 2579077 := bbase (se 4 (by rfl) ⟨241788, by rfl⟩ : syracuseStep 2579077 = 483577) (by norm_num)
theorem B3438769 : Blo 1907435 3438769 := bstep (se 2 (by rfl) ⟨1289538, by rfl⟩ : syracuseStep 3438769 = 2579077) B2579077
theorem B4585025 : Blo 1907435 4585025 := bstep (se 2 (by rfl) ⟨1719384, by rfl⟩ : syracuseStep 4585025 = 3438769) B3438769
theorem B12226733 : Blo 1907435 12226733 := bstep (se 3 (by rfl) ⟨2292512, by rfl⟩ : syracuseStep 12226733 = 4585025) B4585025
theorem B8151155 : Blo 1907435 8151155 := bstep (se 1 (by rfl) ⟨6113366, by rfl⟩ : syracuseStep 8151155 = 12226733) B12226733
theorem B5434103 : Blo 1907435 5434103 := bstep (se 1 (by rfl) ⟨4075577, by rfl⟩ : syracuseStep 5434103 = 8151155) B8151155
theorem B3622735 : Blo 1907435 3622735 := bstep (se 1 (by rfl) ⟨2717051, by rfl⟩ : syracuseStep 3622735 = 5434103) B5434103
theorem B4830313 : Blo 1907435 4830313 := bstep (se 2 (by rfl) ⟨1811367, by rfl⟩ : syracuseStep 4830313 = 3622735) B3622735
theorem B6440417 : Blo 1907435 6440417 := bstep (se 2 (by rfl) ⟨2415156, by rfl⟩ : syracuseStep 6440417 = 4830313) B4830313
theorem B4293611 : Blo 1907435 4293611 := bstep (se 1 (by rfl) ⟨3220208, by rfl⟩ : syracuseStep 4293611 = 6440417) B6440417
theorem B2862407 : Blo 1907435 2862407 := bstep (se 1 (by rfl) ⟨2146805, by rfl⟩ : syracuseStep 2862407 = 4293611) B4293611
theorem B1908271 : Blo 1907435 1908271 := bstep (se 1 (by rfl) ⟨1431203, by rfl⟩ : syracuseStep 1908271 = 2862407) B2862407
theorem B2862413 : Blo 1907435 2862413 := bbase (se 3 (by rfl) ⟨536702, by rfl⟩ : syracuseStep 2862413 = 1073405) (by norm_num)
theorem B1908275 : Blo 1907435 1908275 := bstep (se 1 (by rfl) ⟨1431206, by rfl⟩ : syracuseStep 1908275 = 2862413) B2862413
theorem B4293629 : Blo 1907435 4293629 := bbase (se 3 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 4293629 = 1610111) (by norm_num)
theorem B2862419 : Blo 1907435 2862419 := bstep (se 1 (by rfl) ⟨2146814, by rfl⟩ : syracuseStep 2862419 = 4293629) B4293629
theorem B1908279 : Blo 1907435 1908279 := bstep (se 1 (by rfl) ⟨1431209, by rfl⟩ : syracuseStep 1908279 = 2862419) B2862419
theorem B3220229 : Blo 1907435 3220229 := bbase (se 4 (by rfl) ⟨301896, by rfl⟩ : syracuseStep 3220229 = 603793) (by norm_num)
theorem B2146819 : Blo 1907435 2146819 := bstep (se 1 (by rfl) ⟨1610114, by rfl⟩ : syracuseStep 2146819 = 3220229) B3220229
theorem B2862425 : Blo 1907435 2862425 := bstep (se 2 (by rfl) ⟨1073409, by rfl⟩ : syracuseStep 2862425 = 2146819) B2146819
theorem B1908283 : Blo 1907435 1908283 := bstep (se 1 (by rfl) ⟨1431212, by rfl⟩ : syracuseStep 1908283 = 2862425) B2862425
theorem B14491061 : Blo 1907435 14491061 := bbase (se 5 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 14491061 = 1358537) (by norm_num)
theorem B9660707 : Blo 1907435 9660707 := bstep (se 1 (by rfl) ⟨7245530, by rfl⟩ : syracuseStep 9660707 = 14491061) B14491061
theorem B6440471 : Blo 1907435 6440471 := bstep (se 1 (by rfl) ⟨4830353, by rfl⟩ : syracuseStep 6440471 = 9660707) B9660707
theorem B4293647 : Blo 1907435 4293647 := bstep (se 1 (by rfl) ⟨3220235, by rfl⟩ : syracuseStep 4293647 = 6440471) B6440471
theorem B2862431 : Blo 1907435 2862431 := bstep (se 1 (by rfl) ⟨2146823, by rfl⟩ : syracuseStep 2862431 = 4293647) B4293647
theorem B1908287 : Blo 1907435 1908287 := bstep (se 1 (by rfl) ⟨1431215, by rfl⟩ : syracuseStep 1908287 = 2862431) B2862431
theorem B2862437 : Blo 1907435 2862437 := bbase (se 4 (by rfl) ⟨268353, by rfl⟩ : syracuseStep 2862437 = 536707) (by norm_num)
theorem B1908291 : Blo 1907435 1908291 := bstep (se 1 (by rfl) ⟨1431218, by rfl⟩ : syracuseStep 1908291 = 2862437) B2862437
theorem B3622781 : Blo 1907435 3622781 := bbase (se 3 (by rfl) ⟨679271, by rfl⟩ : syracuseStep 3622781 = 1358543) (by norm_num)
theorem B2415187 : Blo 1907435 2415187 := bstep (se 1 (by rfl) ⟨1811390, by rfl⟩ : syracuseStep 2415187 = 3622781) B3622781
theorem B3220249 : Blo 1907435 3220249 := bstep (se 2 (by rfl) ⟨1207593, by rfl⟩ : syracuseStep 3220249 = 2415187) B2415187
theorem B4293665 : Blo 1907435 4293665 := bstep (se 2 (by rfl) ⟨1610124, by rfl⟩ : syracuseStep 4293665 = 3220249) B3220249
theorem B2862443 : Blo 1907435 2862443 := bstep (se 1 (by rfl) ⟨2146832, by rfl⟩ : syracuseStep 2862443 = 4293665) B4293665
theorem B1908295 : Blo 1907435 1908295 := bstep (se 1 (by rfl) ⟨1431221, by rfl⟩ : syracuseStep 1908295 = 2862443) B2862443
theorem B2146837 : Blo 1907435 2146837 := bbase (se 6 (by rfl) ⟨50316, by rfl⟩ : syracuseStep 2146837 = 100633) (by norm_num)
theorem B2862449 : Blo 1907435 2862449 := bstep (se 2 (by rfl) ⟨1073418, by rfl⟩ : syracuseStep 2862449 = 2146837) B2146837
theorem B1908299 : Blo 1907435 1908299 := bstep (se 1 (by rfl) ⟨1431224, by rfl⟩ : syracuseStep 1908299 = 2862449) B2862449
theorem B2415197 : Blo 1907435 2415197 := bbase (se 3 (by rfl) ⟨452849, by rfl⟩ : syracuseStep 2415197 = 905699) (by norm_num)
theorem B6440525 : Blo 1907435 6440525 := bstep (se 3 (by rfl) ⟨1207598, by rfl⟩ : syracuseStep 6440525 = 2415197) B2415197
theorem B4293683 : Blo 1907435 4293683 := bstep (se 1 (by rfl) ⟨3220262, by rfl⟩ : syracuseStep 4293683 = 6440525) B6440525
theorem B2862455 : Blo 1907435 2862455 := bstep (se 1 (by rfl) ⟨2146841, by rfl⟩ : syracuseStep 2862455 = 4293683) B4293683
theorem B1908303 : Blo 1907435 1908303 := bstep (se 1 (by rfl) ⟨1431227, by rfl⟩ : syracuseStep 1908303 = 2862455) B2862455
theorem B2862461 : Blo 1907435 2862461 := bbase (se 3 (by rfl) ⟨536711, by rfl⟩ : syracuseStep 2862461 = 1073423) (by norm_num)
theorem B1908307 : Blo 1907435 1908307 := bstep (se 1 (by rfl) ⟨1431230, by rfl⟩ : syracuseStep 1908307 = 2862461) B2862461
theorem B4293701 : Blo 1907435 4293701 := bbase (se 4 (by rfl) ⟨402534, by rfl⟩ : syracuseStep 4293701 = 805069) (by norm_num)
theorem B2862467 : Blo 1907435 2862467 := bstep (se 1 (by rfl) ⟨2146850, by rfl⟩ : syracuseStep 2862467 = 4293701) B4293701
theorem B1908311 : Blo 1907435 1908311 := bstep (se 1 (by rfl) ⟨1431233, by rfl⟩ : syracuseStep 1908311 = 2862467) B2862467
theorem B5434229 : Blo 1907435 5434229 := bbase (se 5 (by rfl) ⟨254729, by rfl⟩ : syracuseStep 5434229 = 509459) (by norm_num)
theorem B3622819 : Blo 1907435 3622819 := bstep (se 1 (by rfl) ⟨2717114, by rfl⟩ : syracuseStep 3622819 = 5434229) B5434229
theorem B4830425 : Blo 1907435 4830425 := bstep (se 2 (by rfl) ⟨1811409, by rfl⟩ : syracuseStep 4830425 = 3622819) B3622819
theorem B3220283 : Blo 1907435 3220283 := bstep (se 1 (by rfl) ⟨2415212, by rfl⟩ : syracuseStep 3220283 = 4830425) B4830425
theorem B2146855 : Blo 1907435 2146855 := bstep (se 1 (by rfl) ⟨1610141, by rfl⟩ : syracuseStep 2146855 = 3220283) B3220283
theorem B2862473 : Blo 1907435 2862473 := bstep (se 2 (by rfl) ⟨1073427, by rfl⟩ : syracuseStep 2862473 = 2146855) B2146855
theorem B1908315 : Blo 1907435 1908315 := bstep (se 1 (by rfl) ⟨1431236, by rfl⟩ : syracuseStep 1908315 = 2862473) B2862473
theorem B9660869 : Blo 1907435 9660869 := bbase (se 4 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 9660869 = 1811413) (by norm_num)
theorem B6440579 : Blo 1907435 6440579 := bstep (se 1 (by rfl) ⟨4830434, by rfl⟩ : syracuseStep 6440579 = 9660869) B9660869
theorem B4293719 : Blo 1907435 4293719 := bstep (se 1 (by rfl) ⟨3220289, by rfl⟩ : syracuseStep 4293719 = 6440579) B6440579
theorem B2862479 : Blo 1907435 2862479 := bstep (se 1 (by rfl) ⟨2146859, by rfl⟩ : syracuseStep 2862479 = 4293719) B4293719
theorem B1908319 : Blo 1907435 1908319 := bstep (se 1 (by rfl) ⟨1431239, by rfl⟩ : syracuseStep 1908319 = 2862479) B2862479
theorem B2862485 : Blo 1907435 2862485 := bbase (se 6 (by rfl) ⟨67089, by rfl⟩ : syracuseStep 2862485 = 134179) (by norm_num)
theorem B1908323 : Blo 1907435 1908323 := bstep (se 1 (by rfl) ⟨1431242, by rfl⟩ : syracuseStep 1908323 = 2862485) B2862485
theorem B3056773 : Blo 1907435 3056773 := bbase (se 4 (by rfl) ⟨286572, by rfl⟩ : syracuseStep 3056773 = 573145) (by norm_num)
theorem B4075697 : Blo 1907435 4075697 := bstep (se 2 (by rfl) ⟨1528386, by rfl⟩ : syracuseStep 4075697 = 3056773) B3056773
theorem B10868525 : Blo 1907435 10868525 := bstep (se 3 (by rfl) ⟨2037848, by rfl⟩ : syracuseStep 10868525 = 4075697) B4075697
theorem B7245683 : Blo 1907435 7245683 := bstep (se 1 (by rfl) ⟨5434262, by rfl⟩ : syracuseStep 7245683 = 10868525) B10868525
theorem B4830455 : Blo 1907435 4830455 := bstep (se 1 (by rfl) ⟨3622841, by rfl⟩ : syracuseStep 4830455 = 7245683) B7245683
theorem B3220303 : Blo 1907435 3220303 := bstep (se 1 (by rfl) ⟨2415227, by rfl⟩ : syracuseStep 3220303 = 4830455) B4830455
theorem B4293737 : Blo 1907435 4293737 := bstep (se 2 (by rfl) ⟨1610151, by rfl⟩ : syracuseStep 4293737 = 3220303) B3220303
theorem B2862491 : Blo 1907435 2862491 := bstep (se 1 (by rfl) ⟨2146868, by rfl⟩ : syracuseStep 2862491 = 4293737) B4293737
theorem B1908327 : Blo 1907435 1908327 := bstep (se 1 (by rfl) ⟨1431245, by rfl⟩ : syracuseStep 1908327 = 2862491) B2862491
theorem B2146873 : Blo 1907435 2146873 := bbase (se 2 (by rfl) ⟨805077, by rfl⟩ : syracuseStep 2146873 = 1610155) (by norm_num)
theorem B2862497 : Blo 1907435 2862497 := bstep (se 2 (by rfl) ⟨1073436, by rfl⟩ : syracuseStep 2862497 = 2146873) B2146873
theorem B1908331 : Blo 1907435 1908331 := bstep (se 1 (by rfl) ⟨1431248, by rfl⟩ : syracuseStep 1908331 = 2862497) B2862497
theorem B2037857 : Blo 1907435 2037857 := bbase (se 2 (by rfl) ⟨764196, by rfl⟩ : syracuseStep 2037857 = 1528393) (by norm_num)
theorem B5434285 : Blo 1907435 5434285 := bstep (se 3 (by rfl) ⟨1018928, by rfl⟩ : syracuseStep 5434285 = 2037857) B2037857
theorem B7245713 : Blo 1907435 7245713 := bstep (se 2 (by rfl) ⟨2717142, by rfl⟩ : syracuseStep 7245713 = 5434285) B5434285
theorem B4830475 : Blo 1907435 4830475 := bstep (se 1 (by rfl) ⟨3622856, by rfl⟩ : syracuseStep 4830475 = 7245713) B7245713
theorem B6440633 : Blo 1907435 6440633 := bstep (se 2 (by rfl) ⟨2415237, by rfl⟩ : syracuseStep 6440633 = 4830475) B4830475
theorem B4293755 : Blo 1907435 4293755 := bstep (se 1 (by rfl) ⟨3220316, by rfl⟩ : syracuseStep 4293755 = 6440633) B6440633
theorem B2862503 : Blo 1907435 2862503 := bstep (se 1 (by rfl) ⟨2146877, by rfl⟩ : syracuseStep 2862503 = 4293755) B4293755
theorem B1908335 : Blo 1907435 1908335 := bstep (se 1 (by rfl) ⟨1431251, by rfl⟩ : syracuseStep 1908335 = 2862503) B2862503
theorem B2862509 : Blo 1907435 2862509 := bbase (se 3 (by rfl) ⟨536720, by rfl⟩ : syracuseStep 2862509 = 1073441) (by norm_num)
theorem B1908339 : Blo 1907435 1908339 := bstep (se 1 (by rfl) ⟨1431254, by rfl⟩ : syracuseStep 1908339 = 2862509) B2862509
theorem B4293773 : Blo 1907435 4293773 := bbase (se 3 (by rfl) ⟨805082, by rfl⟩ : syracuseStep 4293773 = 1610165) (by norm_num)
theorem B2862515 : Blo 1907435 2862515 := bstep (se 1 (by rfl) ⟨2146886, by rfl⟩ : syracuseStep 2862515 = 4293773) B4293773
theorem B1908343 : Blo 1907435 1908343 := bstep (se 1 (by rfl) ⟨1431257, by rfl⟩ : syracuseStep 1908343 = 2862515) B2862515
theorem B2415253 : Blo 1907435 2415253 := bbase (se 6 (by rfl) ⟨56607, by rfl⟩ : syracuseStep 2415253 = 113215) (by norm_num)
theorem B3220337 : Blo 1907435 3220337 := bstep (se 2 (by rfl) ⟨1207626, by rfl⟩ : syracuseStep 3220337 = 2415253) B2415253
theorem B2146891 : Blo 1907435 2146891 := bstep (se 1 (by rfl) ⟨1610168, by rfl⟩ : syracuseStep 2146891 = 3220337) B3220337
theorem B2862521 : Blo 1907435 2862521 := bstep (se 2 (by rfl) ⟨1073445, by rfl⟩ : syracuseStep 2862521 = 2146891) B2146891
theorem B1908347 : Blo 1907435 1908347 := bstep (se 1 (by rfl) ⟨1431260, by rfl⟩ : syracuseStep 1908347 = 2862521) B2862521
theorem B3672317 : Blo 1907435 3672317 := bbase (se 3 (by rfl) ⟨688559, by rfl⟩ : syracuseStep 3672317 = 1377119) (by norm_num)
theorem B2448211 : Blo 1907435 2448211 := bstep (se 1 (by rfl) ⟨1836158, by rfl⟩ : syracuseStep 2448211 = 3672317) B3672317
theorem B3264281 : Blo 1907435 3264281 := bstep (se 2 (by rfl) ⟨1224105, by rfl⟩ : syracuseStep 3264281 = 2448211) B2448211
theorem B2176187 : Blo 1907435 2176187 := bstep (se 1 (by rfl) ⟨1632140, by rfl⟩ : syracuseStep 2176187 = 3264281) B3264281
theorem B5803165 : Blo 1907435 5803165 := bstep (se 3 (by rfl) ⟨1088093, by rfl⟩ : syracuseStep 5803165 = 2176187) B2176187
theorem B7737553 : Blo 1907435 7737553 := bstep (se 2 (by rfl) ⟨2901582, by rfl⟩ : syracuseStep 7737553 = 5803165) B5803165
theorem B10316737 : Blo 1907435 10316737 := bstep (se 2 (by rfl) ⟨3868776, by rfl⟩ : syracuseStep 10316737 = 7737553) B7737553
theorem B55022597 : Blo 1907435 55022597 := bstep (se 4 (by rfl) ⟨5158368, by rfl⟩ : syracuseStep 55022597 = 10316737) B10316737
theorem B36681731 : Blo 1907435 36681731 := bstep (se 1 (by rfl) ⟨27511298, by rfl⟩ : syracuseStep 36681731 = 55022597) B55022597
theorem B24454487 : Blo 1907435 24454487 := bstep (se 1 (by rfl) ⟨18340865, by rfl⟩ : syracuseStep 24454487 = 36681731) B36681731
theorem B16302991 : Blo 1907435 16302991 := bstep (se 1 (by rfl) ⟨12227243, by rfl⟩ : syracuseStep 16302991 = 24454487) B24454487
theorem B21737321 : Blo 1907435 21737321 := bstep (se 2 (by rfl) ⟨8151495, by rfl⟩ : syracuseStep 21737321 = 16302991) B16302991
theorem B14491547 : Blo 1907435 14491547 := bstep (se 1 (by rfl) ⟨10868660, by rfl⟩ : syracuseStep 14491547 = 21737321) B21737321
theorem B9661031 : Blo 1907435 9661031 := bstep (se 1 (by rfl) ⟨7245773, by rfl⟩ : syracuseStep 9661031 = 14491547) B14491547
theorem B6440687 : Blo 1907435 6440687 := bstep (se 1 (by rfl) ⟨4830515, by rfl⟩ : syracuseStep 6440687 = 9661031) B9661031
theorem B4293791 : Blo 1907435 4293791 := bstep (se 1 (by rfl) ⟨3220343, by rfl⟩ : syracuseStep 4293791 = 6440687) B6440687
theorem B2862527 : Blo 1907435 2862527 := bstep (se 1 (by rfl) ⟨2146895, by rfl⟩ : syracuseStep 2862527 = 4293791) B4293791
theorem B1908351 : Blo 1907435 1908351 := bstep (se 1 (by rfl) ⟨1431263, by rfl⟩ : syracuseStep 1908351 = 2862527) B2862527
theorem B2862533 : Blo 1907435 2862533 := bbase (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) (by norm_num)
theorem B1908355 : Blo 1907435 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B3220357 : Blo 1907435 3220357 := bbase (se 4 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 3220357 = 603817) (by norm_num)
theorem B4293809 : Blo 1907435 4293809 := bstep (se 2 (by rfl) ⟨1610178, by rfl⟩ : syracuseStep 4293809 = 3220357) B3220357
theorem B2862539 : Blo 1907435 2862539 := bstep (se 1 (by rfl) ⟨2146904, by rfl⟩ : syracuseStep 2862539 = 4293809) B4293809
theorem B1908359 : Blo 1907435 1908359 := bstep (se 1 (by rfl) ⟨1431269, by rfl⟩ : syracuseStep 1908359 = 2862539) B2862539
theorem B2146909 : Blo 1907435 2146909 := bbase (se 3 (by rfl) ⟨402545, by rfl⟩ : syracuseStep 2146909 = 805091) (by norm_num)
theorem B2862545 : Blo 1907435 2862545 := bstep (se 2 (by rfl) ⟨1073454, by rfl⟩ : syracuseStep 2862545 = 2146909) B2146909
theorem B1908363 : Blo 1907435 1908363 := bstep (se 1 (by rfl) ⟨1431272, by rfl⟩ : syracuseStep 1908363 = 2862545) B2862545
theorem B6440741 : Blo 1907435 6440741 := bbase (se 4 (by rfl) ⟨603819, by rfl⟩ : syracuseStep 6440741 = 1207639) (by norm_num)
theorem B4293827 : Blo 1907435 4293827 := bstep (se 1 (by rfl) ⟨3220370, by rfl⟩ : syracuseStep 4293827 = 6440741) B6440741
theorem B2862551 : Blo 1907435 2862551 := bstep (se 1 (by rfl) ⟨2146913, by rfl⟩ : syracuseStep 2862551 = 4293827) B4293827
theorem B1908367 : Blo 1907435 1908367 := bstep (se 1 (by rfl) ⟨1431275, by rfl⟩ : syracuseStep 1908367 = 2862551) B2862551
theorem B2862557 : Blo 1907435 2862557 := bbase (se 3 (by rfl) ⟨536729, by rfl⟩ : syracuseStep 2862557 = 1073459) (by norm_num)
theorem B1908371 : Blo 1907435 1908371 := bstep (se 1 (by rfl) ⟨1431278, by rfl⟩ : syracuseStep 1908371 = 2862557) B2862557
theorem B4293845 : Blo 1907435 4293845 := bbase (se 7 (by rfl) ⟨50318, by rfl⟩ : syracuseStep 4293845 = 100637) (by norm_num)
theorem B2862563 : Blo 1907435 2862563 := bstep (se 1 (by rfl) ⟨2146922, by rfl⟩ : syracuseStep 2862563 = 4293845) B4293845
theorem B1908375 : Blo 1907435 1908375 := bstep (se 1 (by rfl) ⟨1431281, by rfl⟩ : syracuseStep 1908375 = 2862563) B2862563
theorem B4585285 : Blo 1907435 4585285 := bbase (se 4 (by rfl) ⟨429870, by rfl⟩ : syracuseStep 4585285 = 859741) (by norm_num)
theorem B6113713 : Blo 1907435 6113713 := bstep (se 2 (by rfl) ⟨2292642, by rfl⟩ : syracuseStep 6113713 = 4585285) B4585285
theorem B8151617 : Blo 1907435 8151617 := bstep (se 2 (by rfl) ⟨3056856, by rfl⟩ : syracuseStep 8151617 = 6113713) B6113713
theorem B5434411 : Blo 1907435 5434411 := bstep (se 1 (by rfl) ⟨4075808, by rfl⟩ : syracuseStep 5434411 = 8151617) B8151617
theorem B7245881 : Blo 1907435 7245881 := bstep (se 2 (by rfl) ⟨2717205, by rfl⟩ : syracuseStep 7245881 = 5434411) B5434411
theorem B4830587 : Blo 1907435 4830587 := bstep (se 1 (by rfl) ⟨3622940, by rfl⟩ : syracuseStep 4830587 = 7245881) B7245881
theorem B3220391 : Blo 1907435 3220391 := bstep (se 1 (by rfl) ⟨2415293, by rfl⟩ : syracuseStep 3220391 = 4830587) B4830587
theorem B2146927 : Blo 1907435 2146927 := bstep (se 1 (by rfl) ⟨1610195, by rfl⟩ : syracuseStep 2146927 = 3220391) B3220391
theorem B2862569 : Blo 1907435 2862569 := bstep (se 2 (by rfl) ⟨1073463, by rfl⟩ : syracuseStep 2862569 = 2146927) B2146927
theorem B1908379 : Blo 1907435 1908379 := bstep (se 1 (by rfl) ⟨1431284, by rfl⟩ : syracuseStep 1908379 = 2862569) B2862569
theorem B4647853 : Blo 1907435 4647853 := bbase (se 3 (by rfl) ⟨871472, by rfl⟩ : syracuseStep 4647853 = 1742945) (by norm_num)
theorem B6197137 : Blo 1907435 6197137 := bstep (se 2 (by rfl) ⟨2323926, by rfl⟩ : syracuseStep 6197137 = 4647853) B4647853
theorem B33051397 : Blo 1907435 33051397 := bstep (se 4 (by rfl) ⟨3098568, by rfl⟩ : syracuseStep 33051397 = 6197137) B6197137
theorem B44068529 : Blo 1907435 44068529 := bstep (se 2 (by rfl) ⟨16525698, by rfl⟩ : syracuseStep 44068529 = 33051397) B33051397
theorem B29379019 : Blo 1907435 29379019 := bstep (se 1 (by rfl) ⟨22034264, by rfl⟩ : syracuseStep 29379019 = 44068529) B44068529
theorem B39172025 : Blo 1907435 39172025 := bstep (se 2 (by rfl) ⟨14689509, by rfl⟩ : syracuseStep 39172025 = 29379019) B29379019
theorem B26114683 : Blo 1907435 26114683 := bstep (se 1 (by rfl) ⟨19586012, by rfl⟩ : syracuseStep 26114683 = 39172025) B39172025
theorem B34819577 : Blo 1907435 34819577 := bstep (se 2 (by rfl) ⟨13057341, by rfl⟩ : syracuseStep 34819577 = 26114683) B26114683
theorem B23213051 : Blo 1907435 23213051 := bstep (se 1 (by rfl) ⟨17409788, by rfl⟩ : syracuseStep 23213051 = 34819577) B34819577
theorem B15475367 : Blo 1907435 15475367 := bstep (se 1 (by rfl) ⟨11606525, by rfl⟩ : syracuseStep 15475367 = 23213051) B23213051
theorem B10316911 : Blo 1907435 10316911 := bstep (se 1 (by rfl) ⟨7737683, by rfl⟩ : syracuseStep 10316911 = 15475367) B15475367
theorem B13755881 : Blo 1907435 13755881 := bstep (se 2 (by rfl) ⟨5158455, by rfl⟩ : syracuseStep 13755881 = 10316911) B10316911
theorem B9170587 : Blo 1907435 9170587 := bstep (se 1 (by rfl) ⟨6877940, by rfl⟩ : syracuseStep 9170587 = 13755881) B13755881
theorem B12227449 : Blo 1907435 12227449 := bstep (se 2 (by rfl) ⟨4585293, by rfl⟩ : syracuseStep 12227449 = 9170587) B9170587
theorem B16303265 : Blo 1907435 16303265 := bstep (se 2 (by rfl) ⟨6113724, by rfl⟩ : syracuseStep 16303265 = 12227449) B12227449
theorem B10868843 : Blo 1907435 10868843 := bstep (se 1 (by rfl) ⟨8151632, by rfl⟩ : syracuseStep 10868843 = 16303265) B16303265
theorem B7245895 : Blo 1907435 7245895 := bstep (se 1 (by rfl) ⟨5434421, by rfl⟩ : syracuseStep 7245895 = 10868843) B10868843
theorem B9661193 : Blo 1907435 9661193 := bstep (se 2 (by rfl) ⟨3622947, by rfl⟩ : syracuseStep 9661193 = 7245895) B7245895
theorem B6440795 : Blo 1907435 6440795 := bstep (se 1 (by rfl) ⟨4830596, by rfl⟩ : syracuseStep 6440795 = 9661193) B9661193
theorem B4293863 : Blo 1907435 4293863 := bstep (se 1 (by rfl) ⟨3220397, by rfl⟩ : syracuseStep 4293863 = 6440795) B6440795
theorem B2862575 : Blo 1907435 2862575 := bstep (se 1 (by rfl) ⟨2146931, by rfl⟩ : syracuseStep 2862575 = 4293863) B4293863
theorem B1908383 : Blo 1907435 1908383 := bstep (se 1 (by rfl) ⟨1431287, by rfl⟩ : syracuseStep 1908383 = 2862575) B2862575
theorem B2862581 : Blo 1907435 2862581 := bbase (se 5 (by rfl) ⟨134183, by rfl⟩ : syracuseStep 2862581 = 268367) (by norm_num)
theorem B1908387 : Blo 1907435 1908387 := bstep (se 1 (by rfl) ⟨1431290, by rfl⟩ : syracuseStep 1908387 = 2862581) B2862581
theorem B2037917 : Blo 1907435 2037917 := bbase (se 3 (by rfl) ⟨382109, by rfl⟩ : syracuseStep 2037917 = 764219) (by norm_num)
theorem B5434445 : Blo 1907435 5434445 := bstep (se 3 (by rfl) ⟨1018958, by rfl⟩ : syracuseStep 5434445 = 2037917) B2037917
theorem B3622963 : Blo 1907435 3622963 := bstep (se 1 (by rfl) ⟨2717222, by rfl⟩ : syracuseStep 3622963 = 5434445) B5434445
theorem B4830617 : Blo 1907435 4830617 := bstep (se 2 (by rfl) ⟨1811481, by rfl⟩ : syracuseStep 4830617 = 3622963) B3622963
theorem B3220411 : Blo 1907435 3220411 := bstep (se 1 (by rfl) ⟨2415308, by rfl⟩ : syracuseStep 3220411 = 4830617) B4830617
theorem B4293881 : Blo 1907435 4293881 := bstep (se 2 (by rfl) ⟨1610205, by rfl⟩ : syracuseStep 4293881 = 3220411) B3220411
theorem B2862587 : Blo 1907435 2862587 := bstep (se 1 (by rfl) ⟨2146940, by rfl⟩ : syracuseStep 2862587 = 4293881) B4293881
theorem B1908391 : Blo 1907435 1908391 := bstep (se 1 (by rfl) ⟨1431293, by rfl⟩ : syracuseStep 1908391 = 2862587) B2862587
theorem B2146945 : Blo 1907435 2146945 := bbase (se 2 (by rfl) ⟨805104, by rfl⟩ : syracuseStep 2146945 = 1610209) (by norm_num)
theorem B2862593 : Blo 1907435 2862593 := bstep (se 2 (by rfl) ⟨1073472, by rfl⟩ : syracuseStep 2862593 = 2146945) B2146945
theorem B1908395 : Blo 1907435 1908395 := bstep (se 1 (by rfl) ⟨1431296, by rfl⟩ : syracuseStep 1908395 = 2862593) B2862593
theorem B4830637 : Blo 1907435 4830637 := bbase (se 3 (by rfl) ⟨905744, by rfl⟩ : syracuseStep 4830637 = 1811489) (by norm_num)
theorem B6440849 : Blo 1907435 6440849 := bstep (se 2 (by rfl) ⟨2415318, by rfl⟩ : syracuseStep 6440849 = 4830637) B4830637
theorem B4293899 : Blo 1907435 4293899 := bstep (se 1 (by rfl) ⟨3220424, by rfl⟩ : syracuseStep 4293899 = 6440849) B6440849
theorem B2862599 : Blo 1907435 2862599 := bstep (se 1 (by rfl) ⟨2146949, by rfl⟩ : syracuseStep 2862599 = 4293899) B4293899
theorem B1908399 : Blo 1907435 1908399 := bstep (se 1 (by rfl) ⟨1431299, by rfl⟩ : syracuseStep 1908399 = 2862599) B2862599
theorem B2862605 : Blo 1907435 2862605 := bbase (se 3 (by rfl) ⟨536738, by rfl⟩ : syracuseStep 2862605 = 1073477) (by norm_num)
theorem B1908403 : Blo 1907435 1908403 := bstep (se 1 (by rfl) ⟨1431302, by rfl⟩ : syracuseStep 1908403 = 2862605) B2862605
theorem B4293917 : Blo 1907435 4293917 := bbase (se 3 (by rfl) ⟨805109, by rfl⟩ : syracuseStep 4293917 = 1610219) (by norm_num)
theorem B2862611 : Blo 1907435 2862611 := bstep (se 1 (by rfl) ⟨2146958, by rfl⟩ : syracuseStep 2862611 = 4293917) B4293917
theorem B1908407 : Blo 1907435 1908407 := bstep (se 1 (by rfl) ⟨1431305, by rfl⟩ : syracuseStep 1908407 = 2862611) B2862611
theorem B3220445 : Blo 1907435 3220445 := bbase (se 3 (by rfl) ⟨603833, by rfl⟩ : syracuseStep 3220445 = 1207667) (by norm_num)
theorem B2146963 : Blo 1907435 2146963 := bstep (se 1 (by rfl) ⟨1610222, by rfl⟩ : syracuseStep 2146963 = 3220445) B3220445
theorem B2862617 : Blo 1907435 2862617 := bstep (se 2 (by rfl) ⟨1073481, by rfl⟩ : syracuseStep 2862617 = 2146963) B2146963
theorem B1908411 : Blo 1907435 1908411 := bstep (se 1 (by rfl) ⟨1431308, by rfl⟩ : syracuseStep 1908411 = 2862617) B2862617
theorem B9170741 : Blo 1907435 9170741 := bbase (se 5 (by rfl) ⟨429878, by rfl⟩ : syracuseStep 9170741 = 859757) (by norm_num)
theorem B6113827 : Blo 1907435 6113827 := bstep (se 1 (by rfl) ⟨4585370, by rfl⟩ : syracuseStep 6113827 = 9170741) B9170741
theorem B8151769 : Blo 1907435 8151769 := bstep (se 2 (by rfl) ⟨3056913, by rfl⟩ : syracuseStep 8151769 = 6113827) B6113827
theorem B10869025 : Blo 1907435 10869025 := bstep (se 2 (by rfl) ⟨4075884, by rfl⟩ : syracuseStep 10869025 = 8151769) B8151769
theorem B14492033 : Blo 1907435 14492033 := bstep (se 2 (by rfl) ⟨5434512, by rfl⟩ : syracuseStep 14492033 = 10869025) B10869025
theorem B9661355 : Blo 1907435 9661355 := bstep (se 1 (by rfl) ⟨7246016, by rfl⟩ : syracuseStep 9661355 = 14492033) B14492033
theorem B6440903 : Blo 1907435 6440903 := bstep (se 1 (by rfl) ⟨4830677, by rfl⟩ : syracuseStep 6440903 = 9661355) B9661355
theorem B4293935 : Blo 1907435 4293935 := bstep (se 1 (by rfl) ⟨3220451, by rfl⟩ : syracuseStep 4293935 = 6440903) B6440903
theorem B2862623 : Blo 1907435 2862623 := bstep (se 1 (by rfl) ⟨2146967, by rfl⟩ : syracuseStep 2862623 = 4293935) B4293935
theorem B1908415 : Blo 1907435 1908415 := bstep (se 1 (by rfl) ⟨1431311, by rfl⟩ : syracuseStep 1908415 = 2862623) B2862623
theorem B2862629 : Blo 1907435 2862629 := bbase (se 4 (by rfl) ⟨268371, by rfl⟩ : syracuseStep 2862629 = 536743) (by norm_num)
theorem B1908419 : Blo 1907435 1908419 := bstep (se 1 (by rfl) ⟨1431314, by rfl⟩ : syracuseStep 1908419 = 2862629) B2862629
theorem B2415349 : Blo 1907435 2415349 := bbase (se 5 (by rfl) ⟨113219, by rfl⟩ : syracuseStep 2415349 = 226439) (by norm_num)
theorem B3220465 : Blo 1907435 3220465 := bstep (se 2 (by rfl) ⟨1207674, by rfl⟩ : syracuseStep 3220465 = 2415349) B2415349
theorem B4293953 : Blo 1907435 4293953 := bstep (se 2 (by rfl) ⟨1610232, by rfl⟩ : syracuseStep 4293953 = 3220465) B3220465
theorem B2862635 : Blo 1907435 2862635 := bstep (se 1 (by rfl) ⟨2146976, by rfl⟩ : syracuseStep 2862635 = 4293953) B4293953
theorem B1908423 : Blo 1907435 1908423 := bstep (se 1 (by rfl) ⟨1431317, by rfl⟩ : syracuseStep 1908423 = 2862635) B2862635
theorem B2146981 : Blo 1907435 2146981 := bbase (se 4 (by rfl) ⟨201279, by rfl⟩ : syracuseStep 2146981 = 402559) (by norm_num)
theorem B2862641 : Blo 1907435 2862641 := bstep (se 2 (by rfl) ⟨1073490, by rfl⟩ : syracuseStep 2862641 = 2146981) B2146981
theorem B1908427 : Blo 1907435 1908427 := bstep (se 1 (by rfl) ⟨1431320, by rfl⟩ : syracuseStep 1908427 = 2862641) B2862641
theorem B17410229 : Blo 1907435 17410229 := bbase (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) (by norm_num)
theorem B11606819 : Blo 1907435 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B30951517 : Blo 1907435 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B41268689 : Blo 1907435 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B27512459 : Blo 1907435 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B18341639 : Blo 1907435 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B12227759 : Blo 1907435 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B8151839 : Blo 1907435 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B5434559 : Blo 1907435 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B3623039 : Blo 1907435 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B2415359 : Blo 1907435 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B6440957 : Blo 1907435 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B4293971 : Blo 1907435 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B2862647 : Blo 1907435 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B1908431 : Blo 1907435 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B2862653 : Blo 1907435 2862653 := bbase (se 3 (by rfl) ⟨536747, by rfl⟩ : syracuseStep 2862653 = 1073495) (by norm_num)
theorem B1908435 : Blo 1907435 1908435 := bstep (se 1 (by rfl) ⟨1431326, by rfl⟩ : syracuseStep 1908435 = 2862653) B2862653
theorem B4293989 : Blo 1907435 4293989 := bbase (se 4 (by rfl) ⟨402561, by rfl⟩ : syracuseStep 4293989 = 805123) (by norm_num)
theorem B2862659 : Blo 1907435 2862659 := bstep (se 1 (by rfl) ⟨2146994, by rfl⟩ : syracuseStep 2862659 = 4293989) B4293989
theorem B1908439 : Blo 1907435 1908439 := bstep (se 1 (by rfl) ⟨1431329, by rfl⟩ : syracuseStep 1908439 = 2862659) B2862659
theorem B4830749 : Blo 1907435 4830749 := bbase (se 3 (by rfl) ⟨905765, by rfl⟩ : syracuseStep 4830749 = 1811531) (by norm_num)
theorem B3220499 : Blo 1907435 3220499 := bstep (se 1 (by rfl) ⟨2415374, by rfl⟩ : syracuseStep 3220499 = 4830749) B4830749
theorem B2146999 : Blo 1907435 2146999 := bstep (se 1 (by rfl) ⟨1610249, by rfl⟩ : syracuseStep 2146999 = 3220499) B3220499
theorem B2862665 : Blo 1907435 2862665 := bstep (se 2 (by rfl) ⟨1073499, by rfl⟩ : syracuseStep 2862665 = 2146999) B2146999
theorem B1908443 : Blo 1907435 1908443 := bstep (se 1 (by rfl) ⟨1431332, by rfl⟩ : syracuseStep 1908443 = 2862665) B2862665
theorem B3623069 : Blo 1907435 3623069 := bbase (se 3 (by rfl) ⟨679325, by rfl⟩ : syracuseStep 3623069 = 1358651) (by norm_num)
theorem B9661517 : Blo 1907435 9661517 := bstep (se 3 (by rfl) ⟨1811534, by rfl⟩ : syracuseStep 9661517 = 3623069) B3623069
theorem B6441011 : Blo 1907435 6441011 := bstep (se 1 (by rfl) ⟨4830758, by rfl⟩ : syracuseStep 6441011 = 9661517) B9661517
theorem B4294007 : Blo 1907435 4294007 := bstep (se 1 (by rfl) ⟨3220505, by rfl⟩ : syracuseStep 4294007 = 6441011) B6441011
theorem B2862671 : Blo 1907435 2862671 := bstep (se 1 (by rfl) ⟨2147003, by rfl⟩ : syracuseStep 2862671 = 4294007) B4294007
theorem B1908447 : Blo 1907435 1908447 := bstep (se 1 (by rfl) ⟨1431335, by rfl⟩ : syracuseStep 1908447 = 2862671) B2862671
theorem B2862677 : Blo 1907435 2862677 := bbase (se 8 (by rfl) ⟨16773, by rfl⟩ : syracuseStep 2862677 = 33547) (by norm_num)
theorem B1908451 : Blo 1907435 1908451 := bstep (se 1 (by rfl) ⟨1431338, by rfl⟩ : syracuseStep 1908451 = 2862677) B2862677
theorem B8151941 : Blo 1907435 8151941 := bbase (se 4 (by rfl) ⟨764244, by rfl⟩ : syracuseStep 8151941 = 1528489) (by norm_num)
theorem B5434627 : Blo 1907435 5434627 := bstep (se 1 (by rfl) ⟨4075970, by rfl⟩ : syracuseStep 5434627 = 8151941) B8151941
theorem B7246169 : Blo 1907435 7246169 := bstep (se 2 (by rfl) ⟨2717313, by rfl⟩ : syracuseStep 7246169 = 5434627) B5434627
theorem B4830779 : Blo 1907435 4830779 := bstep (se 1 (by rfl) ⟨3623084, by rfl⟩ : syracuseStep 4830779 = 7246169) B7246169
theorem B3220519 : Blo 1907435 3220519 := bstep (se 1 (by rfl) ⟨2415389, by rfl⟩ : syracuseStep 3220519 = 4830779) B4830779
theorem B4294025 : Blo 1907435 4294025 := bstep (se 2 (by rfl) ⟨1610259, by rfl⟩ : syracuseStep 4294025 = 3220519) B3220519
theorem B2862683 : Blo 1907435 2862683 := bstep (se 1 (by rfl) ⟨2147012, by rfl⟩ : syracuseStep 2862683 = 4294025) B4294025
theorem B1908455 : Blo 1907435 1908455 := bstep (se 1 (by rfl) ⟨1431341, by rfl⟩ : syracuseStep 1908455 = 2862683) B2862683
theorem B2147017 : Blo 1907435 2147017 := bbase (se 2 (by rfl) ⟨805131, by rfl⟩ : syracuseStep 2147017 = 1610263) (by norm_num)
theorem B2862689 : Blo 1907435 2862689 := bstep (se 2 (by rfl) ⟨1073508, by rfl⟩ : syracuseStep 2862689 = 2147017) B2147017
theorem B1908459 : Blo 1907435 1908459 := bstep (se 1 (by rfl) ⟨1431344, by rfl⟩ : syracuseStep 1908459 = 2862689) B2862689
theorem B3869005 : Blo 1907435 3869005 := bbase (se 3 (by rfl) ⟨725438, by rfl⟩ : syracuseStep 3869005 = 1450877) (by norm_num)
theorem B5158673 : Blo 1907435 5158673 := bstep (se 2 (by rfl) ⟨1934502, by rfl⟩ : syracuseStep 5158673 = 3869005) B3869005
theorem B3439115 : Blo 1907435 3439115 := bstep (se 1 (by rfl) ⟨2579336, by rfl⟩ : syracuseStep 3439115 = 5158673) B5158673
theorem B2292743 : Blo 1907435 2292743 := bstep (se 1 (by rfl) ⟨1719557, by rfl⟩ : syracuseStep 2292743 = 3439115) B3439115
theorem B6113981 : Blo 1907435 6113981 := bstep (se 3 (by rfl) ⟨1146371, by rfl⟩ : syracuseStep 6113981 = 2292743) B2292743
theorem B16303949 : Blo 1907435 16303949 := bstep (se 3 (by rfl) ⟨3056990, by rfl⟩ : syracuseStep 16303949 = 6113981) B6113981
theorem B10869299 : Blo 1907435 10869299 := bstep (se 1 (by rfl) ⟨8151974, by rfl⟩ : syracuseStep 10869299 = 16303949) B16303949
theorem B7246199 : Blo 1907435 7246199 := bstep (se 1 (by rfl) ⟨5434649, by rfl⟩ : syracuseStep 7246199 = 10869299) B10869299
theorem B4830799 : Blo 1907435 4830799 := bstep (se 1 (by rfl) ⟨3623099, by rfl⟩ : syracuseStep 4830799 = 7246199) B7246199
theorem B6441065 : Blo 1907435 6441065 := bstep (se 2 (by rfl) ⟨2415399, by rfl⟩ : syracuseStep 6441065 = 4830799) B4830799
theorem B4294043 : Blo 1907435 4294043 := bstep (se 1 (by rfl) ⟨3220532, by rfl⟩ : syracuseStep 4294043 = 6441065) B6441065
theorem B2862695 : Blo 1907435 2862695 := bstep (se 1 (by rfl) ⟨2147021, by rfl⟩ : syracuseStep 2862695 = 4294043) B4294043
theorem B1908463 : Blo 1907435 1908463 := bstep (se 1 (by rfl) ⟨1431347, by rfl⟩ : syracuseStep 1908463 = 2862695) B2862695
theorem B2862701 : Blo 1907435 2862701 := bbase (se 3 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 2862701 = 1073513) (by norm_num)
theorem B1908467 : Blo 1907435 1908467 := bstep (se 1 (by rfl) ⟨1431350, by rfl⟩ : syracuseStep 1908467 = 2862701) B2862701
theorem B4294061 : Blo 1907435 4294061 := bbase (se 3 (by rfl) ⟨805136, by rfl⟩ : syracuseStep 4294061 = 1610273) (by norm_num)
theorem B2862707 : Blo 1907435 2862707 := bstep (se 1 (by rfl) ⟨2147030, by rfl⟩ : syracuseStep 2862707 = 4294061) B4294061
theorem B1908471 : Blo 1907435 1908471 := bstep (se 1 (by rfl) ⟨1431353, by rfl⟩ : syracuseStep 1908471 = 2862707) B2862707
theorem B4585517 : Blo 1907435 4585517 := bbase (se 3 (by rfl) ⟨859784, by rfl⟩ : syracuseStep 4585517 = 1719569) (by norm_num)
theorem B3057011 : Blo 1907435 3057011 := bstep (se 1 (by rfl) ⟨2292758, by rfl⟩ : syracuseStep 3057011 = 4585517) B4585517
theorem B2038007 : Blo 1907435 2038007 := bstep (se 1 (by rfl) ⟨1528505, by rfl⟩ : syracuseStep 2038007 = 3057011) B3057011
theorem B5434685 : Blo 1907435 5434685 := bstep (se 3 (by rfl) ⟨1019003, by rfl⟩ : syracuseStep 5434685 = 2038007) B2038007
theorem B3623123 : Blo 1907435 3623123 := bstep (se 1 (by rfl) ⟨2717342, by rfl⟩ : syracuseStep 3623123 = 5434685) B5434685
theorem B2415415 : Blo 1907435 2415415 := bstep (se 1 (by rfl) ⟨1811561, by rfl⟩ : syracuseStep 2415415 = 3623123) B3623123
theorem B3220553 : Blo 1907435 3220553 := bstep (se 2 (by rfl) ⟨1207707, by rfl⟩ : syracuseStep 3220553 = 2415415) B2415415
theorem B2147035 : Blo 1907435 2147035 := bstep (se 1 (by rfl) ⟨1610276, by rfl⟩ : syracuseStep 2147035 = 3220553) B3220553
theorem B2862713 : Blo 1907435 2862713 := bstep (se 2 (by rfl) ⟨1073517, by rfl⟩ : syracuseStep 2862713 = 2147035) B2147035
theorem B1908475 : Blo 1907435 1908475 := bstep (se 1 (by rfl) ⟨1431356, by rfl⟩ : syracuseStep 1908475 = 2862713) B2862713
theorem B3722669 : Blo 1907435 3722669 := bbase (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) (by norm_num)
theorem B2481779 : Blo 1907435 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B6618077 : Blo 1907435 6618077 := bstep (se 3 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 6618077 = 2481779) B2481779
theorem B4412051 : Blo 1907435 4412051 := bstep (se 1 (by rfl) ⟨3309038, by rfl⟩ : syracuseStep 4412051 = 6618077) B6618077
theorem B2941367 : Blo 1907435 2941367 := bstep (se 1 (by rfl) ⟨2206025, by rfl⟩ : syracuseStep 2941367 = 4412051) B4412051
theorem B7843645 : Blo 1907435 7843645 := bstep (se 3 (by rfl) ⟨1470683, by rfl⟩ : syracuseStep 7843645 = 2941367) B2941367
theorem B41832773 : Blo 1907435 41832773 := bstep (se 4 (by rfl) ⟨3921822, by rfl⟩ : syracuseStep 41832773 = 7843645) B7843645
theorem B27888515 : Blo 1907435 27888515 := bstep (se 1 (by rfl) ⟨20916386, by rfl⟩ : syracuseStep 27888515 = 41832773) B41832773
theorem B18592343 : Blo 1907435 18592343 := bstep (se 1 (by rfl) ⟨13944257, by rfl⟩ : syracuseStep 18592343 = 27888515) B27888515
theorem B12394895 : Blo 1907435 12394895 := bstep (se 1 (by rfl) ⟨9296171, by rfl⟩ : syracuseStep 12394895 = 18592343) B18592343
theorem B33053053 : Blo 1907435 33053053 := bstep (se 3 (by rfl) ⟨6197447, by rfl⟩ : syracuseStep 33053053 = 12394895) B12394895
theorem B44070737 : Blo 1907435 44070737 := bstep (se 2 (by rfl) ⟨16526526, by rfl⟩ : syracuseStep 44070737 = 33053053) B33053053
theorem B117521965 : Blo 1907435 117521965 := bstep (se 3 (by rfl) ⟨22035368, by rfl⟩ : syracuseStep 117521965 = 44070737) B44070737
theorem B156695953 : Blo 1907435 156695953 := bstep (se 2 (by rfl) ⟨58760982, by rfl⟩ : syracuseStep 156695953 = 117521965) B117521965
theorem B208927937 : Blo 1907435 208927937 := bstep (se 2 (by rfl) ⟨78347976, by rfl⟩ : syracuseStep 208927937 = 156695953) B156695953
theorem B139285291 : Blo 1907435 139285291 := bstep (se 1 (by rfl) ⟨104463968, by rfl⟩ : syracuseStep 139285291 = 208927937) B208927937
theorem B185713721 : Blo 1907435 185713721 := bstep (se 2 (by rfl) ⟨69642645, by rfl⟩ : syracuseStep 185713721 = 139285291) B139285291
theorem B123809147 : Blo 1907435 123809147 := bstep (se 1 (by rfl) ⟨92856860, by rfl⟩ : syracuseStep 123809147 = 185713721) B185713721
theorem B82539431 : Blo 1907435 82539431 := bstep (se 1 (by rfl) ⟨61904573, by rfl⟩ : syracuseStep 82539431 = 123809147) B123809147
theorem B55026287 : Blo 1907435 55026287 := bstep (se 1 (by rfl) ⟨41269715, by rfl⟩ : syracuseStep 55026287 = 82539431) B82539431
theorem B36684191 : Blo 1907435 36684191 := bstep (se 1 (by rfl) ⟨27513143, by rfl⟩ : syracuseStep 36684191 = 55026287) B55026287
theorem B24456127 : Blo 1907435 24456127 := bstep (se 1 (by rfl) ⟨18342095, by rfl⟩ : syracuseStep 24456127 = 36684191) B36684191
theorem B32608169 : Blo 1907435 32608169 := bstep (se 2 (by rfl) ⟨12228063, by rfl⟩ : syracuseStep 32608169 = 24456127) B24456127
theorem B21738779 : Blo 1907435 21738779 := bstep (se 1 (by rfl) ⟨16304084, by rfl⟩ : syracuseStep 21738779 = 32608169) B32608169
theorem B14492519 : Blo 1907435 14492519 := bstep (se 1 (by rfl) ⟨10869389, by rfl⟩ : syracuseStep 14492519 = 21738779) B21738779
theorem B9661679 : Blo 1907435 9661679 := bstep (se 1 (by rfl) ⟨7246259, by rfl⟩ : syracuseStep 9661679 = 14492519) B14492519
theorem B6441119 : Blo 1907435 6441119 := bstep (se 1 (by rfl) ⟨4830839, by rfl⟩ : syracuseStep 6441119 = 9661679) B9661679
theorem B4294079 : Blo 1907435 4294079 := bstep (se 1 (by rfl) ⟨3220559, by rfl⟩ : syracuseStep 4294079 = 6441119) B6441119
theorem B2862719 : Blo 1907435 2862719 := bstep (se 1 (by rfl) ⟨2147039, by rfl⟩ : syracuseStep 2862719 = 4294079) B4294079
theorem B1908479 : Blo 1907435 1908479 := bstep (se 1 (by rfl) ⟨1431359, by rfl⟩ : syracuseStep 1908479 = 2862719) B2862719
theorem B2862725 : Blo 1907435 2862725 := bbase (se 4 (by rfl) ⟨268380, by rfl⟩ : syracuseStep 2862725 = 536761) (by norm_num)
theorem B1908483 : Blo 1907435 1908483 := bstep (se 1 (by rfl) ⟨1431362, by rfl⟩ : syracuseStep 1908483 = 2862725) B2862725
theorem B3220573 : Blo 1907435 3220573 := bbase (se 3 (by rfl) ⟨603857, by rfl⟩ : syracuseStep 3220573 = 1207715) (by norm_num)
theorem B4294097 : Blo 1907435 4294097 := bstep (se 2 (by rfl) ⟨1610286, by rfl⟩ : syracuseStep 4294097 = 3220573) B3220573
theorem B2862731 : Blo 1907435 2862731 := bstep (se 1 (by rfl) ⟨2147048, by rfl⟩ : syracuseStep 2862731 = 4294097) B4294097
theorem B1908487 : Blo 1907435 1908487 := bstep (se 1 (by rfl) ⟨1431365, by rfl⟩ : syracuseStep 1908487 = 2862731) B2862731
theorem B2147053 : Blo 1907435 2147053 := bbase (se 3 (by rfl) ⟨402572, by rfl⟩ : syracuseStep 2147053 = 805145) (by norm_num)
theorem B2862737 : Blo 1907435 2862737 := bstep (se 2 (by rfl) ⟨1073526, by rfl⟩ : syracuseStep 2862737 = 2147053) B2147053
theorem B1908491 : Blo 1907435 1908491 := bstep (se 1 (by rfl) ⟨1431368, by rfl⟩ : syracuseStep 1908491 = 2862737) B2862737
theorem B6441173 : Blo 1907435 6441173 := bbase (se 7 (by rfl) ⟨75482, by rfl⟩ : syracuseStep 6441173 = 150965) (by norm_num)
theorem B4294115 : Blo 1907435 4294115 := bstep (se 1 (by rfl) ⟨3220586, by rfl⟩ : syracuseStep 4294115 = 6441173) B6441173
theorem B2862743 : Blo 1907435 2862743 := bstep (se 1 (by rfl) ⟨2147057, by rfl⟩ : syracuseStep 2862743 = 4294115) B4294115
theorem B1908495 : Blo 1907435 1908495 := bstep (se 1 (by rfl) ⟨1431371, by rfl⟩ : syracuseStep 1908495 = 2862743) B2862743
theorem B2862749 : Blo 1907435 2862749 := bbase (se 3 (by rfl) ⟨536765, by rfl⟩ : syracuseStep 2862749 = 1073531) (by norm_num)
theorem B1908499 : Blo 1907435 1908499 := bstep (se 1 (by rfl) ⟨1431374, by rfl⟩ : syracuseStep 1908499 = 2862749) B2862749
theorem B4294133 : Blo 1907435 4294133 := bbase (se 5 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 4294133 = 402575) (by norm_num)
theorem B2862755 : Blo 1907435 2862755 := bstep (se 1 (by rfl) ⟨2147066, by rfl⟩ : syracuseStep 2862755 = 4294133) B4294133
theorem B1908503 : Blo 1907435 1908503 := bstep (se 1 (by rfl) ⟨1431377, by rfl⟩ : syracuseStep 1908503 = 2862755) B2862755
theorem B8705461 : Blo 1907435 8705461 := bbase (se 5 (by rfl) ⟨408068, by rfl⟩ : syracuseStep 8705461 = 816137) (by norm_num)
theorem B11607281 : Blo 1907435 11607281 := bstep (se 2 (by rfl) ⟨4352730, by rfl⟩ : syracuseStep 11607281 = 8705461) B8705461
theorem B7738187 : Blo 1907435 7738187 := bstep (se 1 (by rfl) ⟨5803640, by rfl⟩ : syracuseStep 7738187 = 11607281) B11607281
theorem B20635165 : Blo 1907435 20635165 := bstep (se 3 (by rfl) ⟨3869093, by rfl⟩ : syracuseStep 20635165 = 7738187) B7738187
theorem B27513553 : Blo 1907435 27513553 := bstep (se 2 (by rfl) ⟨10317582, by rfl⟩ : syracuseStep 27513553 = 20635165) B20635165
theorem B36684737 : Blo 1907435 36684737 := bstep (se 2 (by rfl) ⟨13756776, by rfl⟩ : syracuseStep 36684737 = 27513553) B27513553
theorem B24456491 : Blo 1907435 24456491 := bstep (se 1 (by rfl) ⟨18342368, by rfl⟩ : syracuseStep 24456491 = 36684737) B36684737
theorem B16304327 : Blo 1907435 16304327 := bstep (se 1 (by rfl) ⟨12228245, by rfl⟩ : syracuseStep 16304327 = 24456491) B24456491
theorem B10869551 : Blo 1907435 10869551 := bstep (se 1 (by rfl) ⟨8152163, by rfl⟩ : syracuseStep 10869551 = 16304327) B16304327
theorem B7246367 : Blo 1907435 7246367 := bstep (se 1 (by rfl) ⟨5434775, by rfl⟩ : syracuseStep 7246367 = 10869551) B10869551
theorem B4830911 : Blo 1907435 4830911 := bstep (se 1 (by rfl) ⟨3623183, by rfl⟩ : syracuseStep 4830911 = 7246367) B7246367
theorem B3220607 : Blo 1907435 3220607 := bstep (se 1 (by rfl) ⟨2415455, by rfl⟩ : syracuseStep 3220607 = 4830911) B4830911
theorem B2147071 : Blo 1907435 2147071 := bstep (se 1 (by rfl) ⟨1610303, by rfl⟩ : syracuseStep 2147071 = 3220607) B3220607
theorem B2862761 : Blo 1907435 2862761 := bstep (se 2 (by rfl) ⟨1073535, by rfl⟩ : syracuseStep 2862761 = 2147071) B2147071
theorem B1908507 : Blo 1907435 1908507 := bstep (se 1 (by rfl) ⟨1431380, by rfl⟩ : syracuseStep 1908507 = 2862761) B2862761
theorem B2038045 : Blo 1907435 2038045 := bbase (se 3 (by rfl) ⟨382133, by rfl⟩ : syracuseStep 2038045 = 764267) (by norm_num)
theorem B2717393 : Blo 1907435 2717393 := bstep (se 2 (by rfl) ⟨1019022, by rfl⟩ : syracuseStep 2717393 = 2038045) B2038045
theorem B7246381 : Blo 1907435 7246381 := bstep (se 3 (by rfl) ⟨1358696, by rfl⟩ : syracuseStep 7246381 = 2717393) B2717393
theorem B9661841 : Blo 1907435 9661841 := bstep (se 2 (by rfl) ⟨3623190, by rfl⟩ : syracuseStep 9661841 = 7246381) B7246381
theorem B6441227 : Blo 1907435 6441227 := bstep (se 1 (by rfl) ⟨4830920, by rfl⟩ : syracuseStep 6441227 = 9661841) B9661841
theorem B4294151 : Blo 1907435 4294151 := bstep (se 1 (by rfl) ⟨3220613, by rfl⟩ : syracuseStep 4294151 = 6441227) B6441227
theorem B2862767 : Blo 1907435 2862767 := bstep (se 1 (by rfl) ⟨2147075, by rfl⟩ : syracuseStep 2862767 = 4294151) B4294151
theorem B1908511 : Blo 1907435 1908511 := bstep (se 1 (by rfl) ⟨1431383, by rfl⟩ : syracuseStep 1908511 = 2862767) B2862767
theorem B2862773 : Blo 1907435 2862773 := bbase (se 5 (by rfl) ⟨134192, by rfl⟩ : syracuseStep 2862773 = 268385) (by norm_num)
theorem B1908515 : Blo 1907435 1908515 := bstep (se 1 (by rfl) ⟨1431386, by rfl⟩ : syracuseStep 1908515 = 2862773) B2862773
theorem B4830941 : Blo 1907435 4830941 := bbase (se 3 (by rfl) ⟨905801, by rfl⟩ : syracuseStep 4830941 = 1811603) (by norm_num)
theorem B3220627 : Blo 1907435 3220627 := bstep (se 1 (by rfl) ⟨2415470, by rfl⟩ : syracuseStep 3220627 = 4830941) B4830941
theorem B4294169 : Blo 1907435 4294169 := bstep (se 2 (by rfl) ⟨1610313, by rfl⟩ : syracuseStep 4294169 = 3220627) B3220627
theorem B2862779 : Blo 1907435 2862779 := bstep (se 1 (by rfl) ⟨2147084, by rfl⟩ : syracuseStep 2862779 = 4294169) B4294169
theorem B1908519 : Blo 1907435 1908519 := bstep (se 1 (by rfl) ⟨1431389, by rfl⟩ : syracuseStep 1908519 = 2862779) B2862779
theorem B2147089 : Blo 1907435 2147089 := bbase (se 2 (by rfl) ⟨805158, by rfl⟩ : syracuseStep 2147089 = 1610317) (by norm_num)
theorem B2862785 : Blo 1907435 2862785 := bstep (se 2 (by rfl) ⟨1073544, by rfl⟩ : syracuseStep 2862785 = 2147089) B2147089
theorem B1908523 : Blo 1907435 1908523 := bstep (se 1 (by rfl) ⟨1431392, by rfl⟩ : syracuseStep 1908523 = 2862785) B2862785
theorem B3623221 : Blo 1907435 3623221 := bbase (se 5 (by rfl) ⟨169838, by rfl⟩ : syracuseStep 3623221 = 339677) (by norm_num)
theorem B4830961 : Blo 1907435 4830961 := bstep (se 2 (by rfl) ⟨1811610, by rfl⟩ : syracuseStep 4830961 = 3623221) B3623221
theorem B6441281 : Blo 1907435 6441281 := bstep (se 2 (by rfl) ⟨2415480, by rfl⟩ : syracuseStep 6441281 = 4830961) B4830961
theorem B4294187 : Blo 1907435 4294187 := bstep (se 1 (by rfl) ⟨3220640, by rfl⟩ : syracuseStep 4294187 = 6441281) B6441281
theorem B2862791 : Blo 1907435 2862791 := bstep (se 1 (by rfl) ⟨2147093, by rfl⟩ : syracuseStep 2862791 = 4294187) B4294187
theorem B1908527 : Blo 1907435 1908527 := bstep (se 1 (by rfl) ⟨1431395, by rfl⟩ : syracuseStep 1908527 = 2862791) B2862791
theorem B2862797 : Blo 1907435 2862797 := bbase (se 3 (by rfl) ⟨536774, by rfl⟩ : syracuseStep 2862797 = 1073549) (by norm_num)
theorem B1908531 : Blo 1907435 1908531 := bstep (se 1 (by rfl) ⟨1431398, by rfl⟩ : syracuseStep 1908531 = 2862797) B2862797
theorem B4294205 : Blo 1907435 4294205 := bbase (se 3 (by rfl) ⟨805163, by rfl⟩ : syracuseStep 4294205 = 1610327) (by norm_num)
theorem B2862803 : Blo 1907435 2862803 := bstep (se 1 (by rfl) ⟨2147102, by rfl⟩ : syracuseStep 2862803 = 4294205) B4294205
theorem B1908535 : Blo 1907435 1908535 := bstep (se 1 (by rfl) ⟨1431401, by rfl⟩ : syracuseStep 1908535 = 2862803) B2862803
theorem B3220661 : Blo 1907435 3220661 := bbase (se 5 (by rfl) ⟨150968, by rfl⟩ : syracuseStep 3220661 = 301937) (by norm_num)
theorem B2147107 : Blo 1907435 2147107 := bstep (se 1 (by rfl) ⟨1610330, by rfl⟩ : syracuseStep 2147107 = 3220661) B3220661
theorem B2862809 : Blo 1907435 2862809 := bstep (se 2 (by rfl) ⟨1073553, by rfl⟩ : syracuseStep 2862809 = 2147107) B2147107
theorem B1908539 : Blo 1907435 1908539 := bstep (se 1 (by rfl) ⟨1431404, by rfl⟩ : syracuseStep 1908539 = 2862809) B2862809
theorem B3141109 : Blo 1907435 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B16752581 : Blo 1907435 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B11168387 : Blo 1907435 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B7445591 : Blo 1907435 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B4963727 : Blo 1907435 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B13236605 : Blo 1907435 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B8824403 : Blo 1907435 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B23531741 : Blo 1907435 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B15687827 : Blo 1907435 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B10458551 : Blo 1907435 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B6972367 : Blo 1907435 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B9296489 : Blo 1907435 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B24790637 : Blo 1907435 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B16527091 : Blo 1907435 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B22036121 : Blo 1907435 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B14690747 : Blo 1907435 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B9793831 : Blo 1907435 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B13058441 : Blo 1907435 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B8705627 : Blo 1907435 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B5803751 : Blo 1907435 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B15476669 : Blo 1907435 15476669 := bstep (se 3 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 15476669 = 5803751) B5803751
theorem B10317779 : Blo 1907435 10317779 := bstep (se 1 (by rfl) ⟨7738334, by rfl⟩ : syracuseStep 10317779 = 15476669) B15476669
theorem B6878519 : Blo 1907435 6878519 := bstep (se 1 (by rfl) ⟨5158889, by rfl⟩ : syracuseStep 6878519 = 10317779) B10317779
theorem B4585679 : Blo 1907435 4585679 := bstep (se 1 (by rfl) ⟨3439259, by rfl⟩ : syracuseStep 4585679 = 6878519) B6878519
theorem B3057119 : Blo 1907435 3057119 := bstep (se 1 (by rfl) ⟨2292839, by rfl⟩ : syracuseStep 3057119 = 4585679) B4585679
theorem B2038079 : Blo 1907435 2038079 := bstep (se 1 (by rfl) ⟨1528559, by rfl⟩ : syracuseStep 2038079 = 3057119) B3057119
theorem B5434877 : Blo 1907435 5434877 := bstep (se 3 (by rfl) ⟨1019039, by rfl⟩ : syracuseStep 5434877 = 2038079) B2038079
theorem B14493005 : Blo 1907435 14493005 := bstep (se 3 (by rfl) ⟨2717438, by rfl⟩ : syracuseStep 14493005 = 5434877) B5434877
theorem B9662003 : Blo 1907435 9662003 := bstep (se 1 (by rfl) ⟨7246502, by rfl⟩ : syracuseStep 9662003 = 14493005) B14493005
theorem B6441335 : Blo 1907435 6441335 := bstep (se 1 (by rfl) ⟨4831001, by rfl⟩ : syracuseStep 6441335 = 9662003) B9662003
theorem B4294223 : Blo 1907435 4294223 := bstep (se 1 (by rfl) ⟨3220667, by rfl⟩ : syracuseStep 4294223 = 6441335) B6441335
theorem B2862815 : Blo 1907435 2862815 := bstep (se 1 (by rfl) ⟨2147111, by rfl⟩ : syracuseStep 2862815 = 4294223) B4294223
theorem B1908543 : Blo 1907435 1908543 := bstep (se 1 (by rfl) ⟨1431407, by rfl⟩ : syracuseStep 1908543 = 2862815) B2862815
theorem B2862821 : Blo 1907435 2862821 := bbase (se 4 (by rfl) ⟨268389, by rfl⟩ : syracuseStep 2862821 = 536779) (by norm_num)
theorem B1908547 : Blo 1907435 1908547 := bstep (se 1 (by rfl) ⟨1431410, by rfl⟩ : syracuseStep 1908547 = 2862821) B2862821
theorem B5434901 : Blo 1907435 5434901 := bbase (se 6 (by rfl) ⟨127380, by rfl⟩ : syracuseStep 5434901 = 254761) (by norm_num)
theorem B3623267 : Blo 1907435 3623267 := bstep (se 1 (by rfl) ⟨2717450, by rfl⟩ : syracuseStep 3623267 = 5434901) B5434901
theorem B2415511 : Blo 1907435 2415511 := bstep (se 1 (by rfl) ⟨1811633, by rfl⟩ : syracuseStep 2415511 = 3623267) B3623267
theorem B3220681 : Blo 1907435 3220681 := bstep (se 2 (by rfl) ⟨1207755, by rfl⟩ : syracuseStep 3220681 = 2415511) B2415511
theorem B4294241 : Blo 1907435 4294241 := bstep (se 2 (by rfl) ⟨1610340, by rfl⟩ : syracuseStep 4294241 = 3220681) B3220681
theorem B2862827 : Blo 1907435 2862827 := bstep (se 1 (by rfl) ⟨2147120, by rfl⟩ : syracuseStep 2862827 = 4294241) B4294241
theorem B1908551 : Blo 1907435 1908551 := bstep (se 1 (by rfl) ⟨1431413, by rfl⟩ : syracuseStep 1908551 = 2862827) B2862827
theorem B2147125 : Blo 1907435 2147125 := bbase (se 5 (by rfl) ⟨100646, by rfl⟩ : syracuseStep 2147125 = 201293) (by norm_num)
theorem B2862833 : Blo 1907435 2862833 := bstep (se 2 (by rfl) ⟨1073562, by rfl⟩ : syracuseStep 2862833 = 2147125) B2147125
theorem B1908555 : Blo 1907435 1908555 := bstep (se 1 (by rfl) ⟨1431416, by rfl⟩ : syracuseStep 1908555 = 2862833) B2862833
theorem B2415521 : Blo 1907435 2415521 := bbase (se 2 (by rfl) ⟨905820, by rfl⟩ : syracuseStep 2415521 = 1811641) (by norm_num)
theorem B6441389 : Blo 1907435 6441389 := bstep (se 3 (by rfl) ⟨1207760, by rfl⟩ : syracuseStep 6441389 = 2415521) B2415521
theorem B4294259 : Blo 1907435 4294259 := bstep (se 1 (by rfl) ⟨3220694, by rfl⟩ : syracuseStep 4294259 = 6441389) B6441389
theorem B2862839 : Blo 1907435 2862839 := bstep (se 1 (by rfl) ⟨2147129, by rfl⟩ : syracuseStep 2862839 = 4294259) B4294259
theorem B1908559 : Blo 1907435 1908559 := bstep (se 1 (by rfl) ⟨1431419, by rfl⟩ : syracuseStep 1908559 = 2862839) B2862839
theorem B2862845 : Blo 1907435 2862845 := bbase (se 3 (by rfl) ⟨536783, by rfl⟩ : syracuseStep 2862845 = 1073567) (by norm_num)
theorem B1908563 : Blo 1907435 1908563 := bstep (se 1 (by rfl) ⟨1431422, by rfl⟩ : syracuseStep 1908563 = 2862845) B2862845
theorem B4294277 : Blo 1907435 4294277 := bbase (se 4 (by rfl) ⟨402588, by rfl⟩ : syracuseStep 4294277 = 805177) (by norm_num)
theorem B2862851 : Blo 1907435 2862851 := bstep (se 1 (by rfl) ⟨2147138, by rfl⟩ : syracuseStep 2862851 = 4294277) B4294277
theorem B1908567 : Blo 1907435 1908567 := bstep (se 1 (by rfl) ⟨1431425, by rfl⟩ : syracuseStep 1908567 = 2862851) B2862851
theorem B4412269 : Blo 1907435 4412269 := bbase (se 3 (by rfl) ⟨827300, by rfl⟩ : syracuseStep 4412269 = 1654601) (by norm_num)
theorem B5883025 : Blo 1907435 5883025 := bstep (se 2 (by rfl) ⟨2206134, by rfl⟩ : syracuseStep 5883025 = 4412269) B4412269
theorem B7844033 : Blo 1907435 7844033 := bstep (se 2 (by rfl) ⟨2941512, by rfl⟩ : syracuseStep 7844033 = 5883025) B5883025
theorem B5229355 : Blo 1907435 5229355 := bstep (se 1 (by rfl) ⟨3922016, by rfl⟩ : syracuseStep 5229355 = 7844033) B7844033
theorem B6972473 : Blo 1907435 6972473 := bstep (se 2 (by rfl) ⟨2614677, by rfl⟩ : syracuseStep 6972473 = 5229355) B5229355
theorem B4648315 : Blo 1907435 4648315 := bstep (se 1 (by rfl) ⟨3486236, by rfl⟩ : syracuseStep 4648315 = 6972473) B6972473
theorem B6197753 : Blo 1907435 6197753 := bstep (se 2 (by rfl) ⟨2324157, by rfl⟩ : syracuseStep 6197753 = 4648315) B4648315
theorem B16527341 : Blo 1907435 16527341 := bstep (se 3 (by rfl) ⟨3098876, by rfl⟩ : syracuseStep 16527341 = 6197753) B6197753
theorem B11018227 : Blo 1907435 11018227 := bstep (se 1 (by rfl) ⟨8263670, by rfl⟩ : syracuseStep 11018227 = 16527341) B16527341
theorem B14690969 : Blo 1907435 14690969 := bstep (se 2 (by rfl) ⟨5509113, by rfl⟩ : syracuseStep 14690969 = 11018227) B11018227
theorem B9793979 : Blo 1907435 9793979 := bstep (se 1 (by rfl) ⟨7345484, by rfl⟩ : syracuseStep 9793979 = 14690969) B14690969
theorem B6529319 : Blo 1907435 6529319 := bstep (se 1 (by rfl) ⟨4896989, by rfl⟩ : syracuseStep 6529319 = 9793979) B9793979
theorem B4352879 : Blo 1907435 4352879 := bstep (se 1 (by rfl) ⟨3264659, by rfl⟩ : syracuseStep 4352879 = 6529319) B6529319
theorem B2901919 : Blo 1907435 2901919 := bstep (se 1 (by rfl) ⟨2176439, by rfl⟩ : syracuseStep 2901919 = 4352879) B4352879
theorem B3869225 : Blo 1907435 3869225 := bstep (se 2 (by rfl) ⟨1450959, by rfl⟩ : syracuseStep 3869225 = 2901919) B2901919
theorem B2579483 : Blo 1907435 2579483 := bstep (se 1 (by rfl) ⟨1934612, by rfl⟩ : syracuseStep 2579483 = 3869225) B3869225
theorem B6878621 : Blo 1907435 6878621 := bstep (se 3 (by rfl) ⟨1289741, by rfl⟩ : syracuseStep 6878621 = 2579483) B2579483
theorem B4585747 : Blo 1907435 4585747 := bstep (se 1 (by rfl) ⟨3439310, by rfl⟩ : syracuseStep 4585747 = 6878621) B6878621
theorem B6114329 : Blo 1907435 6114329 := bstep (se 2 (by rfl) ⟨2292873, by rfl⟩ : syracuseStep 6114329 = 4585747) B4585747
theorem B4076219 : Blo 1907435 4076219 := bstep (se 1 (by rfl) ⟨3057164, by rfl⟩ : syracuseStep 4076219 = 6114329) B6114329
theorem B2717479 : Blo 1907435 2717479 := bstep (se 1 (by rfl) ⟨2038109, by rfl⟩ : syracuseStep 2717479 = 4076219) B4076219
theorem B3623305 : Blo 1907435 3623305 := bstep (se 2 (by rfl) ⟨1358739, by rfl⟩ : syracuseStep 3623305 = 2717479) B2717479
theorem B4831073 : Blo 1907435 4831073 := bstep (se 2 (by rfl) ⟨1811652, by rfl⟩ : syracuseStep 4831073 = 3623305) B3623305
theorem B3220715 : Blo 1907435 3220715 := bstep (se 1 (by rfl) ⟨2415536, by rfl⟩ : syracuseStep 3220715 = 4831073) B4831073
theorem B2147143 : Blo 1907435 2147143 := bstep (se 1 (by rfl) ⟨1610357, by rfl⟩ : syracuseStep 2147143 = 3220715) B3220715
theorem B2862857 : Blo 1907435 2862857 := bstep (se 2 (by rfl) ⟨1073571, by rfl⟩ : syracuseStep 2862857 = 2147143) B2147143
theorem B1908571 : Blo 1907435 1908571 := bstep (se 1 (by rfl) ⟨1431428, by rfl⟩ : syracuseStep 1908571 = 2862857) B2862857
theorem B9662165 : Blo 1907435 9662165 := bbase (se 7 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 9662165 = 226457) (by norm_num)
theorem B6441443 : Blo 1907435 6441443 := bstep (se 1 (by rfl) ⟨4831082, by rfl⟩ : syracuseStep 6441443 = 9662165) B9662165
theorem B4294295 : Blo 1907435 4294295 := bstep (se 1 (by rfl) ⟨3220721, by rfl⟩ : syracuseStep 4294295 = 6441443) B6441443
theorem B2862863 : Blo 1907435 2862863 := bstep (se 1 (by rfl) ⟨2147147, by rfl⟩ : syracuseStep 2862863 = 4294295) B4294295
theorem B1908575 : Blo 1907435 1908575 := bstep (se 1 (by rfl) ⟨1431431, by rfl⟩ : syracuseStep 1908575 = 2862863) B2862863
theorem B2862869 : Blo 1907435 2862869 := bbase (se 6 (by rfl) ⟨67098, by rfl⟩ : syracuseStep 2862869 = 134197) (by norm_num)
theorem B1908579 : Blo 1907435 1908579 := bstep (se 1 (by rfl) ⟨1431434, by rfl⟩ : syracuseStep 1908579 = 2862869) B2862869
theorem B29382101 : Blo 1907435 29382101 := bbase (se 7 (by rfl) ⟨344321, by rfl⟩ : syracuseStep 29382101 = 688643) (by norm_num)
theorem B19588067 : Blo 1907435 19588067 := bstep (se 1 (by rfl) ⟨14691050, by rfl⟩ : syracuseStep 19588067 = 29382101) B29382101
theorem B13058711 : Blo 1907435 13058711 := bstep (se 1 (by rfl) ⟨9794033, by rfl⟩ : syracuseStep 13058711 = 19588067) B19588067
theorem B8705807 : Blo 1907435 8705807 := bstep (se 1 (by rfl) ⟨6529355, by rfl⟩ : syracuseStep 8705807 = 13058711) B13058711
theorem B5803871 : Blo 1907435 5803871 := bstep (se 1 (by rfl) ⟨4352903, by rfl⟩ : syracuseStep 5803871 = 8705807) B8705807
theorem B15476989 : Blo 1907435 15476989 := bstep (se 3 (by rfl) ⟨2901935, by rfl⟩ : syracuseStep 15476989 = 5803871) B5803871
theorem B20635985 : Blo 1907435 20635985 := bstep (se 2 (by rfl) ⟨7738494, by rfl⟩ : syracuseStep 20635985 = 15476989) B15476989
theorem B55029293 : Blo 1907435 55029293 := bstep (se 3 (by rfl) ⟨10317992, by rfl⟩ : syracuseStep 55029293 = 20635985) B20635985
theorem B36686195 : Blo 1907435 36686195 := bstep (se 1 (by rfl) ⟨27514646, by rfl⟩ : syracuseStep 36686195 = 55029293) B55029293
theorem B24457463 : Blo 1907435 24457463 := bstep (se 1 (by rfl) ⟨18343097, by rfl⟩ : syracuseStep 24457463 = 36686195) B36686195
theorem B16304975 : Blo 1907435 16304975 := bstep (se 1 (by rfl) ⟨12228731, by rfl⟩ : syracuseStep 16304975 = 24457463) B24457463
theorem B10869983 : Blo 1907435 10869983 := bstep (se 1 (by rfl) ⟨8152487, by rfl⟩ : syracuseStep 10869983 = 16304975) B16304975
theorem B7246655 : Blo 1907435 7246655 := bstep (se 1 (by rfl) ⟨5434991, by rfl⟩ : syracuseStep 7246655 = 10869983) B10869983
theorem B4831103 : Blo 1907435 4831103 := bstep (se 1 (by rfl) ⟨3623327, by rfl⟩ : syracuseStep 4831103 = 7246655) B7246655
theorem B3220735 : Blo 1907435 3220735 := bstep (se 1 (by rfl) ⟨2415551, by rfl⟩ : syracuseStep 3220735 = 4831103) B4831103
theorem B4294313 : Blo 1907435 4294313 := bstep (se 2 (by rfl) ⟨1610367, by rfl⟩ : syracuseStep 4294313 = 3220735) B3220735
theorem B2862875 : Blo 1907435 2862875 := bstep (se 1 (by rfl) ⟨2147156, by rfl⟩ : syracuseStep 2862875 = 4294313) B4294313
theorem B1908583 : Blo 1907435 1908583 := bstep (se 1 (by rfl) ⟨1431437, by rfl⟩ : syracuseStep 1908583 = 2862875) B2862875
theorem B2147161 : Blo 1907435 2147161 := bbase (se 2 (by rfl) ⟨805185, by rfl⟩ : syracuseStep 2147161 = 1610371) (by norm_num)
theorem B2862881 : Blo 1907435 2862881 := bstep (se 2 (by rfl) ⟨1073580, by rfl⟩ : syracuseStep 2862881 = 2147161) B2147161
theorem B1908587 : Blo 1907435 1908587 := bstep (se 1 (by rfl) ⟨1431440, by rfl⟩ : syracuseStep 1908587 = 2862881) B2862881
theorem B4076261 : Blo 1907435 4076261 := bbase (se 4 (by rfl) ⟨382149, by rfl⟩ : syracuseStep 4076261 = 764299) (by norm_num)
theorem B2717507 : Blo 1907435 2717507 := bstep (se 1 (by rfl) ⟨2038130, by rfl⟩ : syracuseStep 2717507 = 4076261) B4076261
theorem B7246685 : Blo 1907435 7246685 := bstep (se 3 (by rfl) ⟨1358753, by rfl⟩ : syracuseStep 7246685 = 2717507) B2717507
theorem B4831123 : Blo 1907435 4831123 := bstep (se 1 (by rfl) ⟨3623342, by rfl⟩ : syracuseStep 4831123 = 7246685) B7246685
theorem B6441497 : Blo 1907435 6441497 := bstep (se 2 (by rfl) ⟨2415561, by rfl⟩ : syracuseStep 6441497 = 4831123) B4831123
theorem B4294331 : Blo 1907435 4294331 := bstep (se 1 (by rfl) ⟨3220748, by rfl⟩ : syracuseStep 4294331 = 6441497) B6441497
theorem B2862887 : Blo 1907435 2862887 := bstep (se 1 (by rfl) ⟨2147165, by rfl⟩ : syracuseStep 2862887 = 4294331) B4294331
theorem B1908591 : Blo 1907435 1908591 := bstep (se 1 (by rfl) ⟨1431443, by rfl⟩ : syracuseStep 1908591 = 2862887) B2862887
theorem B2862893 : Blo 1907435 2862893 := bbase (se 3 (by rfl) ⟨536792, by rfl⟩ : syracuseStep 2862893 = 1073585) (by norm_num)
theorem B1908595 : Blo 1907435 1908595 := bstep (se 1 (by rfl) ⟨1431446, by rfl⟩ : syracuseStep 1908595 = 2862893) B2862893
theorem B4294349 : Blo 1907435 4294349 := bbase (se 3 (by rfl) ⟨805190, by rfl⟩ : syracuseStep 4294349 = 1610381) (by norm_num)
theorem B2862899 : Blo 1907435 2862899 := bstep (se 1 (by rfl) ⟨2147174, by rfl⟩ : syracuseStep 2862899 = 4294349) B4294349
theorem B1908599 : Blo 1907435 1908599 := bstep (se 1 (by rfl) ⟨1431449, by rfl⟩ : syracuseStep 1908599 = 2862899) B2862899
theorem B2415577 : Blo 1907435 2415577 := bbase (se 2 (by rfl) ⟨905841, by rfl⟩ : syracuseStep 2415577 = 1811683) (by norm_num)
theorem B3220769 : Blo 1907435 3220769 := bstep (se 2 (by rfl) ⟨1207788, by rfl⟩ : syracuseStep 3220769 = 2415577) B2415577
theorem B2147179 : Blo 1907435 2147179 := bstep (se 1 (by rfl) ⟨1610384, by rfl⟩ : syracuseStep 2147179 = 3220769) B3220769
theorem B2862905 : Blo 1907435 2862905 := bstep (se 2 (by rfl) ⟨1073589, by rfl⟩ : syracuseStep 2862905 = 2147179) B2147179
theorem B1908603 : Blo 1907435 1908603 := bstep (se 1 (by rfl) ⟨1431452, by rfl⟩ : syracuseStep 1908603 = 2862905) B2862905
theorem B3057221 : Blo 1907435 3057221 := bbase (se 4 (by rfl) ⟨286614, by rfl⟩ : syracuseStep 3057221 = 573229) (by norm_num)
theorem B8152589 : Blo 1907435 8152589 := bstep (se 3 (by rfl) ⟨1528610, by rfl⟩ : syracuseStep 8152589 = 3057221) B3057221
theorem B21740237 : Blo 1907435 21740237 := bstep (se 3 (by rfl) ⟨4076294, by rfl⟩ : syracuseStep 21740237 = 8152589) B8152589
theorem B14493491 : Blo 1907435 14493491 := bstep (se 1 (by rfl) ⟨10870118, by rfl⟩ : syracuseStep 14493491 = 21740237) B21740237
theorem B9662327 : Blo 1907435 9662327 := bstep (se 1 (by rfl) ⟨7246745, by rfl⟩ : syracuseStep 9662327 = 14493491) B14493491
theorem B6441551 : Blo 1907435 6441551 := bstep (se 1 (by rfl) ⟨4831163, by rfl⟩ : syracuseStep 6441551 = 9662327) B9662327
theorem B4294367 : Blo 1907435 4294367 := bstep (se 1 (by rfl) ⟨3220775, by rfl⟩ : syracuseStep 4294367 = 6441551) B6441551
theorem B2862911 : Blo 1907435 2862911 := bstep (se 1 (by rfl) ⟨2147183, by rfl⟩ : syracuseStep 2862911 = 4294367) B4294367
theorem B1908607 : Blo 1907435 1908607 := bstep (se 1 (by rfl) ⟨1431455, by rfl⟩ : syracuseStep 1908607 = 2862911) B2862911
theorem B2862917 : Blo 1907435 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B1908611 : Blo 1907435 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B3220789 : Blo 1907435 3220789 := bbase (se 5 (by rfl) ⟨150974, by rfl⟩ : syracuseStep 3220789 = 301949) (by norm_num)
theorem B4294385 : Blo 1907435 4294385 := bstep (se 2 (by rfl) ⟨1610394, by rfl⟩ : syracuseStep 4294385 = 3220789) B3220789
theorem B2862923 : Blo 1907435 2862923 := bstep (se 1 (by rfl) ⟨2147192, by rfl⟩ : syracuseStep 2862923 = 4294385) B4294385
theorem B1908615 : Blo 1907435 1908615 := bstep (se 1 (by rfl) ⟨1431461, by rfl⟩ : syracuseStep 1908615 = 2862923) B2862923
theorem B2147197 : Blo 1907435 2147197 := bbase (se 3 (by rfl) ⟨402599, by rfl⟩ : syracuseStep 2147197 = 805199) (by norm_num)
theorem B2862929 : Blo 1907435 2862929 := bstep (se 2 (by rfl) ⟨1073598, by rfl⟩ : syracuseStep 2862929 = 2147197) B2147197
theorem B1908619 : Blo 1907435 1908619 := bstep (se 1 (by rfl) ⟨1431464, by rfl⟩ : syracuseStep 1908619 = 2862929) B2862929
theorem B6441605 : Blo 1907435 6441605 := bbase (se 4 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 6441605 = 1207801) (by norm_num)
theorem B4294403 : Blo 1907435 4294403 := bstep (se 1 (by rfl) ⟨3220802, by rfl⟩ : syracuseStep 4294403 = 6441605) B6441605
theorem B2862935 : Blo 1907435 2862935 := bstep (se 1 (by rfl) ⟨2147201, by rfl⟩ : syracuseStep 2862935 = 4294403) B4294403
theorem B1908623 : Blo 1907435 1908623 := bstep (se 1 (by rfl) ⟨1431467, by rfl⟩ : syracuseStep 1908623 = 2862935) B2862935
theorem B2862941 : Blo 1907435 2862941 := bbase (se 3 (by rfl) ⟨536801, by rfl⟩ : syracuseStep 2862941 = 1073603) (by norm_num)
theorem B1908627 : Blo 1907435 1908627 := bstep (se 1 (by rfl) ⟨1431470, by rfl⟩ : syracuseStep 1908627 = 2862941) B2862941
theorem B4294421 : Blo 1907435 4294421 := bbase (se 6 (by rfl) ⟨100650, by rfl⟩ : syracuseStep 4294421 = 201301) (by norm_num)
theorem B2862947 : Blo 1907435 2862947 := bstep (se 1 (by rfl) ⟨2147210, by rfl⟩ : syracuseStep 2862947 = 4294421) B4294421
theorem B1908631 : Blo 1907435 1908631 := bstep (se 1 (by rfl) ⟨1431473, by rfl⟩ : syracuseStep 1908631 = 2862947) B2862947
theorem B7246853 : Blo 1907435 7246853 := bbase (se 4 (by rfl) ⟨679392, by rfl⟩ : syracuseStep 7246853 = 1358785) (by norm_num)
theorem B4831235 : Blo 1907435 4831235 := bstep (se 1 (by rfl) ⟨3623426, by rfl⟩ : syracuseStep 4831235 = 7246853) B7246853
theorem B3220823 : Blo 1907435 3220823 := bstep (se 1 (by rfl) ⟨2415617, by rfl⟩ : syracuseStep 3220823 = 4831235) B4831235
theorem B2147215 : Blo 1907435 2147215 := bstep (se 1 (by rfl) ⟨1610411, by rfl⟩ : syracuseStep 2147215 = 3220823) B3220823
theorem B2862953 : Blo 1907435 2862953 := bstep (se 2 (by rfl) ⟨1073607, by rfl⟩ : syracuseStep 2862953 = 2147215) B2147215
theorem B1908635 : Blo 1907435 1908635 := bstep (se 1 (by rfl) ⟨1431476, by rfl⟩ : syracuseStep 1908635 = 2862953) B2862953
theorem B4585909 : Blo 1907435 4585909 := bbase (se 5 (by rfl) ⟨214964, by rfl⟩ : syracuseStep 4585909 = 429929) (by norm_num)
theorem B6114545 : Blo 1907435 6114545 := bstep (se 2 (by rfl) ⟨2292954, by rfl⟩ : syracuseStep 6114545 = 4585909) B4585909
theorem B4076363 : Blo 1907435 4076363 := bstep (se 1 (by rfl) ⟨3057272, by rfl⟩ : syracuseStep 4076363 = 6114545) B6114545
theorem B10870301 : Blo 1907435 10870301 := bstep (se 3 (by rfl) ⟨2038181, by rfl⟩ : syracuseStep 10870301 = 4076363) B4076363
theorem B7246867 : Blo 1907435 7246867 := bstep (se 1 (by rfl) ⟨5435150, by rfl⟩ : syracuseStep 7246867 = 10870301) B10870301
theorem B9662489 : Blo 1907435 9662489 := bstep (se 2 (by rfl) ⟨3623433, by rfl⟩ : syracuseStep 9662489 = 7246867) B7246867
theorem B6441659 : Blo 1907435 6441659 := bstep (se 1 (by rfl) ⟨4831244, by rfl⟩ : syracuseStep 6441659 = 9662489) B9662489
theorem B4294439 : Blo 1907435 4294439 := bstep (se 1 (by rfl) ⟨3220829, by rfl⟩ : syracuseStep 4294439 = 6441659) B6441659
theorem B2862959 : Blo 1907435 2862959 := bstep (se 1 (by rfl) ⟨2147219, by rfl⟩ : syracuseStep 2862959 = 4294439) B4294439
theorem B1908639 : Blo 1907435 1908639 := bstep (se 1 (by rfl) ⟨1431479, by rfl⟩ : syracuseStep 1908639 = 2862959) B2862959
theorem B2862965 : Blo 1907435 2862965 := bbase (se 5 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 2862965 = 268403) (by norm_num)
theorem B1908643 : Blo 1907435 1908643 := bstep (se 1 (by rfl) ⟨1431482, by rfl⟩ : syracuseStep 1908643 = 2862965) B2862965
theorem B4076381 : Blo 1907435 4076381 := bbase (se 3 (by rfl) ⟨764321, by rfl⟩ : syracuseStep 4076381 = 1528643) (by norm_num)
theorem B2717587 : Blo 1907435 2717587 := bstep (se 1 (by rfl) ⟨2038190, by rfl⟩ : syracuseStep 2717587 = 4076381) B4076381
theorem B3623449 : Blo 1907435 3623449 := bstep (se 2 (by rfl) ⟨1358793, by rfl⟩ : syracuseStep 3623449 = 2717587) B2717587
theorem B4831265 : Blo 1907435 4831265 := bstep (se 2 (by rfl) ⟨1811724, by rfl⟩ : syracuseStep 4831265 = 3623449) B3623449
theorem B3220843 : Blo 1907435 3220843 := bstep (se 1 (by rfl) ⟨2415632, by rfl⟩ : syracuseStep 3220843 = 4831265) B4831265
theorem B4294457 : Blo 1907435 4294457 := bstep (se 2 (by rfl) ⟨1610421, by rfl⟩ : syracuseStep 4294457 = 3220843) B3220843
theorem B2862971 : Blo 1907435 2862971 := bstep (se 1 (by rfl) ⟨2147228, by rfl⟩ : syracuseStep 2862971 = 4294457) B4294457
theorem B1908647 : Blo 1907435 1908647 := bstep (se 1 (by rfl) ⟨1431485, by rfl⟩ : syracuseStep 1908647 = 2862971) B2862971
theorem B2147233 : Blo 1907435 2147233 := bbase (se 2 (by rfl) ⟨805212, by rfl⟩ : syracuseStep 2147233 = 1610425) (by norm_num)
theorem B2862977 : Blo 1907435 2862977 := bstep (se 2 (by rfl) ⟨1073616, by rfl⟩ : syracuseStep 2862977 = 2147233) B2147233
theorem B1908651 : Blo 1907435 1908651 := bstep (se 1 (by rfl) ⟨1431488, by rfl⟩ : syracuseStep 1908651 = 2862977) B2862977
theorem B4831285 : Blo 1907435 4831285 := bbase (se 5 (by rfl) ⟨226466, by rfl⟩ : syracuseStep 4831285 = 452933) (by norm_num)
theorem B6441713 : Blo 1907435 6441713 := bstep (se 2 (by rfl) ⟨2415642, by rfl⟩ : syracuseStep 6441713 = 4831285) B4831285
theorem B4294475 : Blo 1907435 4294475 := bstep (se 1 (by rfl) ⟨3220856, by rfl⟩ : syracuseStep 4294475 = 6441713) B6441713
theorem B2862983 : Blo 1907435 2862983 := bstep (se 1 (by rfl) ⟨2147237, by rfl⟩ : syracuseStep 2862983 = 4294475) B4294475
theorem B1908655 : Blo 1907435 1908655 := bstep (se 1 (by rfl) ⟨1431491, by rfl⟩ : syracuseStep 1908655 = 2862983) B2862983
theorem B2862989 : Blo 1907435 2862989 := bbase (se 3 (by rfl) ⟨536810, by rfl⟩ : syracuseStep 2862989 = 1073621) (by norm_num)
theorem B1908659 : Blo 1907435 1908659 := bstep (se 1 (by rfl) ⟨1431494, by rfl⟩ : syracuseStep 1908659 = 2862989) B2862989
theorem B4294493 : Blo 1907435 4294493 := bbase (se 3 (by rfl) ⟨805217, by rfl⟩ : syracuseStep 4294493 = 1610435) (by norm_num)
theorem B2862995 : Blo 1907435 2862995 := bstep (se 1 (by rfl) ⟨2147246, by rfl⟩ : syracuseStep 2862995 = 4294493) B4294493
theorem B1908663 : Blo 1907435 1908663 := bstep (se 1 (by rfl) ⟨1431497, by rfl⟩ : syracuseStep 1908663 = 2862995) B2862995
theorem B3220877 : Blo 1907435 3220877 := bbase (se 3 (by rfl) ⟨603914, by rfl⟩ : syracuseStep 3220877 = 1207829) (by norm_num)
theorem B2147251 : Blo 1907435 2147251 := bstep (se 1 (by rfl) ⟨1610438, by rfl⟩ : syracuseStep 2147251 = 3220877) B3220877
theorem B2863001 : Blo 1907435 2863001 := bstep (se 2 (by rfl) ⟨1073625, by rfl⟩ : syracuseStep 2863001 = 2147251) B2147251
theorem B1908667 : Blo 1907435 1908667 := bstep (se 1 (by rfl) ⟨1431500, by rfl⟩ : syracuseStep 1908667 = 2863001) B2863001
theorem B1934713 : Blo 1907435 1934713 := bbase (se 2 (by rfl) ⟨725517, by rfl⟩ : syracuseStep 1934713 = 1451035) (by norm_num)
theorem B2579617 : Blo 1907435 2579617 := bstep (se 2 (by rfl) ⟨967356, by rfl⟩ : syracuseStep 2579617 = 1934713) B1934713
theorem B13757957 : Blo 1907435 13757957 := bstep (se 4 (by rfl) ⟨1289808, by rfl⟩ : syracuseStep 13757957 = 2579617) B2579617
theorem B9171971 : Blo 1907435 9171971 := bstep (se 1 (by rfl) ⟨6878978, by rfl⟩ : syracuseStep 9171971 = 13757957) B13757957
theorem B6114647 : Blo 1907435 6114647 := bstep (se 1 (by rfl) ⟨4585985, by rfl⟩ : syracuseStep 6114647 = 9171971) B9171971
theorem B16305725 : Blo 1907435 16305725 := bstep (se 3 (by rfl) ⟨3057323, by rfl⟩ : syracuseStep 16305725 = 6114647) B6114647
theorem B10870483 : Blo 1907435 10870483 := bstep (se 1 (by rfl) ⟨8152862, by rfl⟩ : syracuseStep 10870483 = 16305725) B16305725
theorem B14493977 : Blo 1907435 14493977 := bstep (se 2 (by rfl) ⟨5435241, by rfl⟩ : syracuseStep 14493977 = 10870483) B10870483
theorem B9662651 : Blo 1907435 9662651 := bstep (se 1 (by rfl) ⟨7246988, by rfl⟩ : syracuseStep 9662651 = 14493977) B14493977
theorem B6441767 : Blo 1907435 6441767 := bstep (se 1 (by rfl) ⟨4831325, by rfl⟩ : syracuseStep 6441767 = 9662651) B9662651
theorem B4294511 : Blo 1907435 4294511 := bstep (se 1 (by rfl) ⟨3220883, by rfl⟩ : syracuseStep 4294511 = 6441767) B6441767
theorem B2863007 : Blo 1907435 2863007 := bstep (se 1 (by rfl) ⟨2147255, by rfl⟩ : syracuseStep 2863007 = 4294511) B4294511
theorem B1908671 : Blo 1907435 1908671 := bstep (se 1 (by rfl) ⟨1431503, by rfl⟩ : syracuseStep 1908671 = 2863007) B2863007
theorem B2863013 : Blo 1907435 2863013 := bbase (se 4 (by rfl) ⟨268407, by rfl⟩ : syracuseStep 2863013 = 536815) (by norm_num)
theorem B1908675 : Blo 1907435 1908675 := bstep (se 1 (by rfl) ⟨1431506, by rfl⟩ : syracuseStep 1908675 = 2863013) B2863013
theorem B2415673 : Blo 1907435 2415673 := bbase (se 2 (by rfl) ⟨905877, by rfl⟩ : syracuseStep 2415673 = 1811755) (by norm_num)
theorem B3220897 : Blo 1907435 3220897 := bstep (se 2 (by rfl) ⟨1207836, by rfl⟩ : syracuseStep 3220897 = 2415673) B2415673
theorem B4294529 : Blo 1907435 4294529 := bstep (se 2 (by rfl) ⟨1610448, by rfl⟩ : syracuseStep 4294529 = 3220897) B3220897
theorem B2863019 : Blo 1907435 2863019 := bstep (se 1 (by rfl) ⟨2147264, by rfl⟩ : syracuseStep 2863019 = 4294529) B4294529
theorem B1908679 : Blo 1907435 1908679 := bstep (se 1 (by rfl) ⟨1431509, by rfl⟩ : syracuseStep 1908679 = 2863019) B2863019
theorem B2147269 : Blo 1907435 2147269 := bbase (se 4 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 2147269 = 402613) (by norm_num)
theorem B2863025 : Blo 1907435 2863025 := bstep (se 2 (by rfl) ⟨1073634, by rfl⟩ : syracuseStep 2863025 = 2147269) B2147269
theorem B1908683 : Blo 1907435 1908683 := bstep (se 1 (by rfl) ⟨1431512, by rfl⟩ : syracuseStep 1908683 = 2863025) B2863025
theorem B3623525 : Blo 1907435 3623525 := bbase (se 4 (by rfl) ⟨339705, by rfl⟩ : syracuseStep 3623525 = 679411) (by norm_num)
theorem B2415683 : Blo 1907435 2415683 := bstep (se 1 (by rfl) ⟨1811762, by rfl⟩ : syracuseStep 2415683 = 3623525) B3623525
theorem B6441821 : Blo 1907435 6441821 := bstep (se 3 (by rfl) ⟨1207841, by rfl⟩ : syracuseStep 6441821 = 2415683) B2415683
theorem B4294547 : Blo 1907435 4294547 := bstep (se 1 (by rfl) ⟨3220910, by rfl⟩ : syracuseStep 4294547 = 6441821) B6441821
theorem B2863031 : Blo 1907435 2863031 := bstep (se 1 (by rfl) ⟨2147273, by rfl⟩ : syracuseStep 2863031 = 4294547) B4294547
theorem B1908687 : Blo 1907435 1908687 := bstep (se 1 (by rfl) ⟨1431515, by rfl⟩ : syracuseStep 1908687 = 2863031) B2863031
theorem B2863037 : Blo 1907435 2863037 := bbase (se 3 (by rfl) ⟨536819, by rfl⟩ : syracuseStep 2863037 = 1073639) (by norm_num)
theorem B1908691 : Blo 1907435 1908691 := bstep (se 1 (by rfl) ⟨1431518, by rfl⟩ : syracuseStep 1908691 = 2863037) B2863037
theorem B4294565 : Blo 1907435 4294565 := bbase (se 4 (by rfl) ⟨402615, by rfl⟩ : syracuseStep 4294565 = 805231) (by norm_num)
theorem B2863043 : Blo 1907435 2863043 := bstep (se 1 (by rfl) ⟨2147282, by rfl⟩ : syracuseStep 2863043 = 4294565) B4294565
theorem B1908695 : Blo 1907435 1908695 := bstep (se 1 (by rfl) ⟨1431521, by rfl⟩ : syracuseStep 1908695 = 2863043) B2863043
theorem B4831397 : Blo 1907435 4831397 := bbase (se 4 (by rfl) ⟨452943, by rfl⟩ : syracuseStep 4831397 = 905887) (by norm_num)
theorem B3220931 : Blo 1907435 3220931 := bstep (se 1 (by rfl) ⟨2415698, by rfl⟩ : syracuseStep 3220931 = 4831397) B4831397
theorem B2147287 : Blo 1907435 2147287 := bstep (se 1 (by rfl) ⟨1610465, by rfl⟩ : syracuseStep 2147287 = 3220931) B3220931
theorem B2863049 : Blo 1907435 2863049 := bstep (se 2 (by rfl) ⟨1073643, by rfl⟩ : syracuseStep 2863049 = 2147287) B2147287
theorem B1908699 : Blo 1907435 1908699 := bstep (se 1 (by rfl) ⟨1431524, by rfl⟩ : syracuseStep 1908699 = 2863049) B2863049
theorem B5435333 : Blo 1907435 5435333 := bbase (se 4 (by rfl) ⟨509562, by rfl⟩ : syracuseStep 5435333 = 1019125) (by norm_num)
theorem B3623555 : Blo 1907435 3623555 := bstep (se 1 (by rfl) ⟨2717666, by rfl⟩ : syracuseStep 3623555 = 5435333) B5435333
theorem B9662813 : Blo 1907435 9662813 := bstep (se 3 (by rfl) ⟨1811777, by rfl⟩ : syracuseStep 9662813 = 3623555) B3623555
theorem B6441875 : Blo 1907435 6441875 := bstep (se 1 (by rfl) ⟨4831406, by rfl⟩ : syracuseStep 6441875 = 9662813) B9662813
theorem B4294583 : Blo 1907435 4294583 := bstep (se 1 (by rfl) ⟨3220937, by rfl⟩ : syracuseStep 4294583 = 6441875) B6441875
theorem B2863055 : Blo 1907435 2863055 := bstep (se 1 (by rfl) ⟨2147291, by rfl⟩ : syracuseStep 2863055 = 4294583) B4294583
theorem B1908703 : Blo 1907435 1908703 := bstep (se 1 (by rfl) ⟨1431527, by rfl⟩ : syracuseStep 1908703 = 2863055) B2863055
theorem B2863061 : Blo 1907435 2863061 := bbase (se 7 (by rfl) ⟨33551, by rfl⟩ : syracuseStep 2863061 = 67103) (by norm_num)
theorem B1908707 : Blo 1907435 1908707 := bstep (se 1 (by rfl) ⟨1431530, by rfl⟩ : syracuseStep 1908707 = 2863061) B2863061
theorem B7247141 : Blo 1907435 7247141 := bbase (se 4 (by rfl) ⟨679419, by rfl⟩ : syracuseStep 7247141 = 1358839) (by norm_num)
theorem B4831427 : Blo 1907435 4831427 := bstep (se 1 (by rfl) ⟨3623570, by rfl⟩ : syracuseStep 4831427 = 7247141) B7247141
theorem B3220951 : Blo 1907435 3220951 := bstep (se 1 (by rfl) ⟨2415713, by rfl⟩ : syracuseStep 3220951 = 4831427) B4831427
theorem B4294601 : Blo 1907435 4294601 := bstep (se 2 (by rfl) ⟨1610475, by rfl⟩ : syracuseStep 4294601 = 3220951) B3220951
theorem B2863067 : Blo 1907435 2863067 := bstep (se 1 (by rfl) ⟨2147300, by rfl⟩ : syracuseStep 2863067 = 4294601) B4294601
theorem B1908711 : Blo 1907435 1908711 := bstep (se 1 (by rfl) ⟨1431533, by rfl⟩ : syracuseStep 1908711 = 2863067) B2863067
theorem B2147305 : Blo 1907435 2147305 := bbase (se 2 (by rfl) ⟨805239, by rfl⟩ : syracuseStep 2147305 = 1610479) (by norm_num)
theorem B2863073 : Blo 1907435 2863073 := bstep (se 2 (by rfl) ⟨1073652, by rfl⟩ : syracuseStep 2863073 = 2147305) B2147305
theorem B1908715 : Blo 1907435 1908715 := bstep (se 1 (by rfl) ⟨1431536, by rfl⟩ : syracuseStep 1908715 = 2863073) B2863073
theorem B3869525 : Blo 1907435 3869525 := bbase (se 9 (by rfl) ⟨11336, by rfl⟩ : syracuseStep 3869525 = 22673) (by norm_num)
theorem B2579683 : Blo 1907435 2579683 := bstep (se 1 (by rfl) ⟨1934762, by rfl⟩ : syracuseStep 2579683 = 3869525) B3869525
theorem B3439577 : Blo 1907435 3439577 := bstep (se 2 (by rfl) ⟨1289841, by rfl⟩ : syracuseStep 3439577 = 2579683) B2579683
theorem B2293051 : Blo 1907435 2293051 := bstep (se 1 (by rfl) ⟨1719788, by rfl⟩ : syracuseStep 2293051 = 3439577) B3439577
theorem B3057401 : Blo 1907435 3057401 := bstep (se 2 (by rfl) ⟨1146525, by rfl⟩ : syracuseStep 3057401 = 2293051) B2293051
theorem B2038267 : Blo 1907435 2038267 := bstep (se 1 (by rfl) ⟨1528700, by rfl⟩ : syracuseStep 2038267 = 3057401) B3057401
theorem B10870757 : Blo 1907435 10870757 := bstep (se 4 (by rfl) ⟨1019133, by rfl⟩ : syracuseStep 10870757 = 2038267) B2038267
theorem B7247171 : Blo 1907435 7247171 := bstep (se 1 (by rfl) ⟨5435378, by rfl⟩ : syracuseStep 7247171 = 10870757) B10870757
theorem B4831447 : Blo 1907435 4831447 := bstep (se 1 (by rfl) ⟨3623585, by rfl⟩ : syracuseStep 4831447 = 7247171) B7247171
theorem B6441929 : Blo 1907435 6441929 := bstep (se 2 (by rfl) ⟨2415723, by rfl⟩ : syracuseStep 6441929 = 4831447) B4831447
theorem B4294619 : Blo 1907435 4294619 := bstep (se 1 (by rfl) ⟨3220964, by rfl⟩ : syracuseStep 4294619 = 6441929) B6441929
theorem B2863079 : Blo 1907435 2863079 := bstep (se 1 (by rfl) ⟨2147309, by rfl⟩ : syracuseStep 2863079 = 4294619) B4294619
theorem B1908719 : Blo 1907435 1908719 := bstep (se 1 (by rfl) ⟨1431539, by rfl⟩ : syracuseStep 1908719 = 2863079) B2863079
theorem B2863085 : Blo 1907435 2863085 := bbase (se 3 (by rfl) ⟨536828, by rfl⟩ : syracuseStep 2863085 = 1073657) (by norm_num)
theorem B1908723 : Blo 1907435 1908723 := bstep (se 1 (by rfl) ⟨1431542, by rfl⟩ : syracuseStep 1908723 = 2863085) B2863085
theorem B4294637 : Blo 1907435 4294637 := bbase (se 3 (by rfl) ⟨805244, by rfl⟩ : syracuseStep 4294637 = 1610489) (by norm_num)
theorem B2863091 : Blo 1907435 2863091 := bstep (se 1 (by rfl) ⟨2147318, by rfl⟩ : syracuseStep 2863091 = 4294637) B4294637
theorem B1908727 : Blo 1907435 1908727 := bstep (se 1 (by rfl) ⟨1431545, by rfl⟩ : syracuseStep 1908727 = 2863091) B2863091
theorem B3057421 : Blo 1907435 3057421 := bbase (se 3 (by rfl) ⟨573266, by rfl⟩ : syracuseStep 3057421 = 1146533) (by norm_num)
theorem B4076561 : Blo 1907435 4076561 := bstep (se 2 (by rfl) ⟨1528710, by rfl⟩ : syracuseStep 4076561 = 3057421) B3057421
theorem B2717707 : Blo 1907435 2717707 := bstep (se 1 (by rfl) ⟨2038280, by rfl⟩ : syracuseStep 2717707 = 4076561) B4076561
theorem B3623609 : Blo 1907435 3623609 := bstep (se 2 (by rfl) ⟨1358853, by rfl⟩ : syracuseStep 3623609 = 2717707) B2717707
theorem B2415739 : Blo 1907435 2415739 := bstep (se 1 (by rfl) ⟨1811804, by rfl⟩ : syracuseStep 2415739 = 3623609) B3623609
theorem B3220985 : Blo 1907435 3220985 := bstep (se 2 (by rfl) ⟨1207869, by rfl⟩ : syracuseStep 3220985 = 2415739) B2415739
theorem B2147323 : Blo 1907435 2147323 := bstep (se 1 (by rfl) ⟨1610492, by rfl⟩ : syracuseStep 2147323 = 3220985) B3220985
theorem B2863097 : Blo 1907435 2863097 := bstep (se 2 (by rfl) ⟨1073661, by rfl⟩ : syracuseStep 2863097 = 2147323) B2147323
theorem B1908731 : Blo 1907435 1908731 := bstep (se 1 (by rfl) ⟨1431548, by rfl⟩ : syracuseStep 1908731 = 2863097) B2863097
theorem B18848533 : Blo 1907435 18848533 := bbase (se 6 (by rfl) ⟨441762, by rfl⟩ : syracuseStep 18848533 = 883525) (by norm_num)
theorem B25131377 : Blo 1907435 25131377 := bstep (se 2 (by rfl) ⟨9424266, by rfl⟩ : syracuseStep 25131377 = 18848533) B18848533
theorem B16754251 : Blo 1907435 16754251 := bstep (se 1 (by rfl) ⟨12565688, by rfl⟩ : syracuseStep 16754251 = 25131377) B25131377
theorem B22339001 : Blo 1907435 22339001 := bstep (se 2 (by rfl) ⟨8377125, by rfl⟩ : syracuseStep 22339001 = 16754251) B16754251
theorem B14892667 : Blo 1907435 14892667 := bstep (se 1 (by rfl) ⟨11169500, by rfl⟩ : syracuseStep 14892667 = 22339001) B22339001
theorem B79427557 : Blo 1907435 79427557 := bstep (se 4 (by rfl) ⟨7446333, by rfl⟩ : syracuseStep 79427557 = 14892667) B14892667
theorem B105903409 : Blo 1907435 105903409 := bstep (se 2 (by rfl) ⟨39713778, by rfl⟩ : syracuseStep 105903409 = 79427557) B79427557
theorem B141204545 : Blo 1907435 141204545 := bstep (se 2 (by rfl) ⟨52951704, by rfl⟩ : syracuseStep 141204545 = 105903409) B105903409
theorem B94136363 : Blo 1907435 94136363 := bstep (se 1 (by rfl) ⟨70602272, by rfl⟩ : syracuseStep 94136363 = 141204545) B141204545
theorem B62757575 : Blo 1907435 62757575 := bstep (se 1 (by rfl) ⟨47068181, by rfl⟩ : syracuseStep 62757575 = 94136363) B94136363
theorem B41838383 : Blo 1907435 41838383 := bstep (se 1 (by rfl) ⟨31378787, by rfl⟩ : syracuseStep 41838383 = 62757575) B62757575
theorem B111569021 : Blo 1907435 111569021 := bstep (se 3 (by rfl) ⟨20919191, by rfl⟩ : syracuseStep 111569021 = 41838383) B41838383
theorem B74379347 : Blo 1907435 74379347 := bstep (se 1 (by rfl) ⟨55784510, by rfl⟩ : syracuseStep 74379347 = 111569021) B111569021
theorem B49586231 : Blo 1907435 49586231 := bstep (se 1 (by rfl) ⟨37189673, by rfl⟩ : syracuseStep 49586231 = 74379347) B74379347
theorem B33057487 : Blo 1907435 33057487 := bstep (se 1 (by rfl) ⟨24793115, by rfl⟩ : syracuseStep 33057487 = 49586231) B49586231
theorem B44076649 : Blo 1907435 44076649 := bstep (se 2 (by rfl) ⟨16528743, by rfl⟩ : syracuseStep 44076649 = 33057487) B33057487
theorem B58768865 : Blo 1907435 58768865 := bstep (se 2 (by rfl) ⟨22038324, by rfl⟩ : syracuseStep 58768865 = 44076649) B44076649
theorem B39179243 : Blo 1907435 39179243 := bstep (se 1 (by rfl) ⟨29384432, by rfl⟩ : syracuseStep 39179243 = 58768865) B58768865
theorem B26119495 : Blo 1907435 26119495 := bstep (se 1 (by rfl) ⟨19589621, by rfl⟩ : syracuseStep 26119495 = 39179243) B39179243
theorem B34825993 : Blo 1907435 34825993 := bstep (se 2 (by rfl) ⟨13059747, by rfl⟩ : syracuseStep 34825993 = 26119495) B26119495
theorem B185738629 : Blo 1907435 185738629 := bstep (se 4 (by rfl) ⟨17412996, by rfl⟩ : syracuseStep 185738629 = 34825993) B34825993
theorem B247651505 : Blo 1907435 247651505 := bstep (se 2 (by rfl) ⟨92869314, by rfl⟩ : syracuseStep 247651505 = 185738629) B185738629
theorem B165101003 : Blo 1907435 165101003 := bstep (se 1 (by rfl) ⟨123825752, by rfl⟩ : syracuseStep 165101003 = 247651505) B247651505
theorem B110067335 : Blo 1907435 110067335 := bstep (se 1 (by rfl) ⟨82550501, by rfl⟩ : syracuseStep 110067335 = 165101003) B165101003
theorem B73378223 : Blo 1907435 73378223 := bstep (se 1 (by rfl) ⟨55033667, by rfl⟩ : syracuseStep 73378223 = 110067335) B110067335
theorem B48918815 : Blo 1907435 48918815 := bstep (se 1 (by rfl) ⟨36689111, by rfl⟩ : syracuseStep 48918815 = 73378223) B73378223
theorem B32612543 : Blo 1907435 32612543 := bstep (se 1 (by rfl) ⟨24459407, by rfl⟩ : syracuseStep 32612543 = 48918815) B48918815
theorem B21741695 : Blo 1907435 21741695 := bstep (se 1 (by rfl) ⟨16306271, by rfl⟩ : syracuseStep 21741695 = 32612543) B32612543
theorem B14494463 : Blo 1907435 14494463 := bstep (se 1 (by rfl) ⟨10870847, by rfl⟩ : syracuseStep 14494463 = 21741695) B21741695
theorem B9662975 : Blo 1907435 9662975 := bstep (se 1 (by rfl) ⟨7247231, by rfl⟩ : syracuseStep 9662975 = 14494463) B14494463
theorem B6441983 : Blo 1907435 6441983 := bstep (se 1 (by rfl) ⟨4831487, by rfl⟩ : syracuseStep 6441983 = 9662975) B9662975
theorem B4294655 : Blo 1907435 4294655 := bstep (se 1 (by rfl) ⟨3220991, by rfl⟩ : syracuseStep 4294655 = 6441983) B6441983
theorem B2863103 : Blo 1907435 2863103 := bstep (se 1 (by rfl) ⟨2147327, by rfl⟩ : syracuseStep 2863103 = 4294655) B4294655
theorem B1908735 : Blo 1907435 1908735 := bstep (se 1 (by rfl) ⟨1431551, by rfl⟩ : syracuseStep 1908735 = 2863103) B2863103
theorem B2863109 : Blo 1907435 2863109 := bbase (se 4 (by rfl) ⟨268416, by rfl⟩ : syracuseStep 2863109 = 536833) (by norm_num)
theorem B1908739 : Blo 1907435 1908739 := bstep (se 1 (by rfl) ⟨1431554, by rfl⟩ : syracuseStep 1908739 = 2863109) B2863109
theorem B3221005 : Blo 1907435 3221005 := bbase (se 3 (by rfl) ⟨603938, by rfl⟩ : syracuseStep 3221005 = 1207877) (by norm_num)
theorem B4294673 : Blo 1907435 4294673 := bstep (se 2 (by rfl) ⟨1610502, by rfl⟩ : syracuseStep 4294673 = 3221005) B3221005
theorem B2863115 : Blo 1907435 2863115 := bstep (se 1 (by rfl) ⟨2147336, by rfl⟩ : syracuseStep 2863115 = 4294673) B4294673
theorem B1908743 : Blo 1907435 1908743 := bstep (se 1 (by rfl) ⟨1431557, by rfl⟩ : syracuseStep 1908743 = 2863115) B2863115
theorem B2147341 : Blo 1907435 2147341 := bbase (se 3 (by rfl) ⟨402626, by rfl⟩ : syracuseStep 2147341 = 805253) (by norm_num)
theorem B2863121 : Blo 1907435 2863121 := bstep (se 2 (by rfl) ⟨1073670, by rfl⟩ : syracuseStep 2863121 = 2147341) B2147341
theorem B1908747 : Blo 1907435 1908747 := bstep (se 1 (by rfl) ⟨1431560, by rfl⟩ : syracuseStep 1908747 = 2863121) B2863121
theorem B6442037 : Blo 1907435 6442037 := bbase (se 5 (by rfl) ⟨301970, by rfl⟩ : syracuseStep 6442037 = 603941) (by norm_num)
theorem B4294691 : Blo 1907435 4294691 := bstep (se 1 (by rfl) ⟨3221018, by rfl⟩ : syracuseStep 4294691 = 6442037) B6442037
theorem B2863127 : Blo 1907435 2863127 := bstep (se 1 (by rfl) ⟨2147345, by rfl⟩ : syracuseStep 2863127 = 4294691) B4294691
theorem B1908751 : Blo 1907435 1908751 := bstep (se 1 (by rfl) ⟨1431563, by rfl⟩ : syracuseStep 1908751 = 2863127) B2863127
theorem B2863133 : Blo 1907435 2863133 := bbase (se 3 (by rfl) ⟨536837, by rfl⟩ : syracuseStep 2863133 = 1073675) (by norm_num)
theorem B1908755 : Blo 1907435 1908755 := bstep (se 1 (by rfl) ⟨1431566, by rfl⟩ : syracuseStep 1908755 = 2863133) B2863133
theorem B4294709 : Blo 1907435 4294709 := bbase (se 5 (by rfl) ⟨201314, by rfl⟩ : syracuseStep 4294709 = 402629) (by norm_num)
theorem B2863139 : Blo 1907435 2863139 := bstep (se 1 (by rfl) ⟨2147354, by rfl⟩ : syracuseStep 2863139 = 4294709) B4294709
theorem B1908759 : Blo 1907435 1908759 := bstep (se 1 (by rfl) ⟨1431569, by rfl⟩ : syracuseStep 1908759 = 2863139) B2863139
theorem B2094313 : Blo 1907435 2094313 := bbase (se 2 (by rfl) ⟨785367, by rfl⟩ : syracuseStep 2094313 = 1570735) (by norm_num)
theorem B2792417 : Blo 1907435 2792417 := bstep (se 2 (by rfl) ⟨1047156, by rfl⟩ : syracuseStep 2792417 = 2094313) B2094313
theorem B29785781 : Blo 1907435 29785781 := bstep (se 5 (by rfl) ⟨1396208, by rfl⟩ : syracuseStep 29785781 = 2792417) B2792417
theorem B19857187 : Blo 1907435 19857187 := bstep (se 1 (by rfl) ⟨14892890, by rfl⟩ : syracuseStep 19857187 = 29785781) B29785781
theorem B26476249 : Blo 1907435 26476249 := bstep (se 2 (by rfl) ⟨9928593, by rfl⟩ : syracuseStep 26476249 = 19857187) B19857187
theorem B35301665 : Blo 1907435 35301665 := bstep (se 2 (by rfl) ⟨13238124, by rfl⟩ : syracuseStep 35301665 = 26476249) B26476249
theorem B94137773 : Blo 1907435 94137773 := bstep (se 3 (by rfl) ⟨17650832, by rfl⟩ : syracuseStep 94137773 = 35301665) B35301665
theorem B251034061 : Blo 1907435 251034061 := bstep (se 3 (by rfl) ⟨47068886, by rfl⟩ : syracuseStep 251034061 = 94137773) B94137773
theorem B334712081 : Blo 1907435 334712081 := bstep (se 2 (by rfl) ⟨125517030, by rfl⟩ : syracuseStep 334712081 = 251034061) B251034061
theorem B223141387 : Blo 1907435 223141387 := bstep (se 1 (by rfl) ⟨167356040, by rfl⟩ : syracuseStep 223141387 = 334712081) B334712081
theorem B297521849 : Blo 1907435 297521849 := bstep (se 2 (by rfl) ⟨111570693, by rfl⟩ : syracuseStep 297521849 = 223141387) B223141387
theorem B198347899 : Blo 1907435 198347899 := bstep (se 1 (by rfl) ⟨148760924, by rfl⟩ : syracuseStep 198347899 = 297521849) B297521849
theorem B264463865 : Blo 1907435 264463865 := bstep (se 2 (by rfl) ⟨99173949, by rfl⟩ : syracuseStep 264463865 = 198347899) B198347899
theorem B176309243 : Blo 1907435 176309243 := bstep (se 1 (by rfl) ⟨132231932, by rfl⟩ : syracuseStep 176309243 = 264463865) B264463865
theorem B117539495 : Blo 1907435 117539495 := bstep (se 1 (by rfl) ⟨88154621, by rfl⟩ : syracuseStep 117539495 = 176309243) B176309243
theorem B78359663 : Blo 1907435 78359663 := bstep (se 1 (by rfl) ⟨58769747, by rfl⟩ : syracuseStep 78359663 = 117539495) B117539495
theorem B52239775 : Blo 1907435 52239775 := bstep (se 1 (by rfl) ⟨39179831, by rfl⟩ : syracuseStep 52239775 = 78359663) B78359663
theorem B69653033 : Blo 1907435 69653033 := bstep (se 2 (by rfl) ⟨26119887, by rfl⟩ : syracuseStep 69653033 = 52239775) B52239775
theorem B46435355 : Blo 1907435 46435355 := bstep (se 1 (by rfl) ⟨34826516, by rfl⟩ : syracuseStep 46435355 = 69653033) B69653033
theorem B30956903 : Blo 1907435 30956903 := bstep (se 1 (by rfl) ⟨23217677, by rfl⟩ : syracuseStep 30956903 = 46435355) B46435355
theorem B20637935 : Blo 1907435 20637935 := bstep (se 1 (by rfl) ⟨15478451, by rfl⟩ : syracuseStep 20637935 = 30956903) B30956903
theorem B13758623 : Blo 1907435 13758623 := bstep (se 1 (by rfl) ⟨10318967, by rfl⟩ : syracuseStep 13758623 = 20637935) B20637935
theorem B9172415 : Blo 1907435 9172415 := bstep (se 1 (by rfl) ⟨6879311, by rfl⟩ : syracuseStep 9172415 = 13758623) B13758623
theorem B6114943 : Blo 1907435 6114943 := bstep (se 1 (by rfl) ⟨4586207, by rfl⟩ : syracuseStep 6114943 = 9172415) B9172415
theorem B8153257 : Blo 1907435 8153257 := bstep (se 2 (by rfl) ⟨3057471, by rfl⟩ : syracuseStep 8153257 = 6114943) B6114943
theorem B10871009 : Blo 1907435 10871009 := bstep (se 2 (by rfl) ⟨4076628, by rfl⟩ : syracuseStep 10871009 = 8153257) B8153257
theorem B7247339 : Blo 1907435 7247339 := bstep (se 1 (by rfl) ⟨5435504, by rfl⟩ : syracuseStep 7247339 = 10871009) B10871009
theorem B4831559 : Blo 1907435 4831559 := bstep (se 1 (by rfl) ⟨3623669, by rfl⟩ : syracuseStep 4831559 = 7247339) B7247339
theorem B3221039 : Blo 1907435 3221039 := bstep (se 1 (by rfl) ⟨2415779, by rfl⟩ : syracuseStep 3221039 = 4831559) B4831559
theorem B2147359 : Blo 1907435 2147359 := bstep (se 1 (by rfl) ⟨1610519, by rfl⟩ : syracuseStep 2147359 = 3221039) B3221039
theorem B2863145 : Blo 1907435 2863145 := bstep (se 2 (by rfl) ⟨1073679, by rfl⟩ : syracuseStep 2863145 = 2147359) B2147359
theorem B1908763 : Blo 1907435 1908763 := bstep (se 1 (by rfl) ⟨1431572, by rfl⟩ : syracuseStep 1908763 = 2863145) B2863145
theorem B3869621 : Blo 1907435 3869621 := bbase (se 5 (by rfl) ⟨181388, by rfl⟩ : syracuseStep 3869621 = 362777) (by norm_num)
theorem B2579747 : Blo 1907435 2579747 := bstep (se 1 (by rfl) ⟨1934810, by rfl⟩ : syracuseStep 2579747 = 3869621) B3869621
theorem B6879325 : Blo 1907435 6879325 := bstep (se 3 (by rfl) ⟨1289873, by rfl⟩ : syracuseStep 6879325 = 2579747) B2579747
theorem B9172433 : Blo 1907435 9172433 := bstep (se 2 (by rfl) ⟨3439662, by rfl⟩ : syracuseStep 9172433 = 6879325) B6879325
theorem B6114955 : Blo 1907435 6114955 := bstep (se 1 (by rfl) ⟨4586216, by rfl⟩ : syracuseStep 6114955 = 9172433) B9172433
theorem B8153273 : Blo 1907435 8153273 := bstep (se 2 (by rfl) ⟨3057477, by rfl⟩ : syracuseStep 8153273 = 6114955) B6114955
theorem B5435515 : Blo 1907435 5435515 := bstep (se 1 (by rfl) ⟨4076636, by rfl⟩ : syracuseStep 5435515 = 8153273) B8153273
theorem B7247353 : Blo 1907435 7247353 := bstep (se 2 (by rfl) ⟨2717757, by rfl⟩ : syracuseStep 7247353 = 5435515) B5435515
theorem B9663137 : Blo 1907435 9663137 := bstep (se 2 (by rfl) ⟨3623676, by rfl⟩ : syracuseStep 9663137 = 7247353) B7247353
theorem B6442091 : Blo 1907435 6442091 := bstep (se 1 (by rfl) ⟨4831568, by rfl⟩ : syracuseStep 6442091 = 9663137) B9663137
theorem B4294727 : Blo 1907435 4294727 := bstep (se 1 (by rfl) ⟨3221045, by rfl⟩ : syracuseStep 4294727 = 6442091) B6442091
theorem B2863151 : Blo 1907435 2863151 := bstep (se 1 (by rfl) ⟨2147363, by rfl⟩ : syracuseStep 2863151 = 4294727) B4294727
theorem B1908767 : Blo 1907435 1908767 := bstep (se 1 (by rfl) ⟨1431575, by rfl⟩ : syracuseStep 1908767 = 2863151) B2863151
theorem B2863157 : Blo 1907435 2863157 := bbase (se 5 (by rfl) ⟨134210, by rfl⟩ : syracuseStep 2863157 = 268421) (by norm_num)
theorem B1908771 : Blo 1907435 1908771 := bstep (se 1 (by rfl) ⟨1431578, by rfl⟩ : syracuseStep 1908771 = 2863157) B2863157
theorem B4831589 : Blo 1907435 4831589 := bbase (se 4 (by rfl) ⟨452961, by rfl⟩ : syracuseStep 4831589 = 905923) (by norm_num)
theorem B3221059 : Blo 1907435 3221059 := bstep (se 1 (by rfl) ⟨2415794, by rfl⟩ : syracuseStep 3221059 = 4831589) B4831589
theorem B4294745 : Blo 1907435 4294745 := bstep (se 2 (by rfl) ⟨1610529, by rfl⟩ : syracuseStep 4294745 = 3221059) B3221059
theorem B2863163 : Blo 1907435 2863163 := bstep (se 1 (by rfl) ⟨2147372, by rfl⟩ : syracuseStep 2863163 = 4294745) B4294745
theorem B1908775 : Blo 1907435 1908775 := bstep (se 1 (by rfl) ⟨1431581, by rfl⟩ : syracuseStep 1908775 = 2863163) B2863163
theorem B2147377 : Blo 1907435 2147377 := bbase (se 2 (by rfl) ⟨805266, by rfl⟩ : syracuseStep 2147377 = 1610533) (by norm_num)
theorem B2863169 : Blo 1907435 2863169 := bstep (se 2 (by rfl) ⟨1073688, by rfl⟩ : syracuseStep 2863169 = 2147377) B2147377
theorem B1908779 : Blo 1907435 1908779 := bstep (se 1 (by rfl) ⟨1431584, by rfl⟩ : syracuseStep 1908779 = 2863169) B2863169
theorem B11927893 : Blo 1907435 11927893 := bbase (se 10 (by rfl) ⟨17472, by rfl⟩ : syracuseStep 11927893 = 34945) (by norm_num)
theorem B15903857 : Blo 1907435 15903857 := bstep (se 2 (by rfl) ⟨5963946, by rfl⟩ : syracuseStep 15903857 = 11927893) B11927893
theorem B10602571 : Blo 1907435 10602571 := bstep (se 1 (by rfl) ⟨7951928, by rfl⟩ : syracuseStep 10602571 = 15903857) B15903857
theorem B14136761 : Blo 1907435 14136761 := bstep (se 2 (by rfl) ⟨5301285, by rfl⟩ : syracuseStep 14136761 = 10602571) B10602571
theorem B9424507 : Blo 1907435 9424507 := bstep (se 1 (by rfl) ⟨7068380, by rfl⟩ : syracuseStep 9424507 = 14136761) B14136761
theorem B12566009 : Blo 1907435 12566009 := bstep (se 2 (by rfl) ⟨4712253, by rfl⟩ : syracuseStep 12566009 = 9424507) B9424507
theorem B33509357 : Blo 1907435 33509357 := bstep (se 3 (by rfl) ⟨6283004, by rfl⟩ : syracuseStep 33509357 = 12566009) B12566009
theorem B22339571 : Blo 1907435 22339571 := bstep (se 1 (by rfl) ⟨16754678, by rfl⟩ : syracuseStep 22339571 = 33509357) B33509357
theorem B59572189 : Blo 1907435 59572189 := bstep (se 3 (by rfl) ⟨11169785, by rfl⟩ : syracuseStep 59572189 = 22339571) B22339571
theorem B79429585 : Blo 1907435 79429585 := bstep (se 2 (by rfl) ⟨29786094, by rfl⟩ : syracuseStep 79429585 = 59572189) B59572189
theorem B105906113 : Blo 1907435 105906113 := bstep (se 2 (by rfl) ⟨39714792, by rfl⟩ : syracuseStep 105906113 = 79429585) B79429585
theorem B70604075 : Blo 1907435 70604075 := bstep (se 1 (by rfl) ⟨52953056, by rfl⟩ : syracuseStep 70604075 = 105906113) B105906113
theorem B188277533 : Blo 1907435 188277533 := bstep (se 3 (by rfl) ⟨35302037, by rfl⟩ : syracuseStep 188277533 = 70604075) B70604075
theorem B125518355 : Blo 1907435 125518355 := bstep (se 1 (by rfl) ⟨94138766, by rfl⟩ : syracuseStep 125518355 = 188277533) B188277533
theorem B83678903 : Blo 1907435 83678903 := bstep (se 1 (by rfl) ⟨62759177, by rfl⟩ : syracuseStep 83678903 = 125518355) B125518355
theorem B55785935 : Blo 1907435 55785935 := bstep (se 1 (by rfl) ⟨41839451, by rfl⟩ : syracuseStep 55785935 = 83678903) B83678903
theorem B37190623 : Blo 1907435 37190623 := bstep (se 1 (by rfl) ⟨27892967, by rfl⟩ : syracuseStep 37190623 = 55785935) B55785935
theorem B49587497 : Blo 1907435 49587497 := bstep (se 2 (by rfl) ⟨18595311, by rfl⟩ : syracuseStep 49587497 = 37190623) B37190623
theorem B33058331 : Blo 1907435 33058331 := bstep (se 1 (by rfl) ⟨24793748, by rfl⟩ : syracuseStep 33058331 = 49587497) B49587497
theorem B22038887 : Blo 1907435 22038887 := bstep (se 1 (by rfl) ⟨16529165, by rfl⟩ : syracuseStep 22038887 = 33058331) B33058331
theorem B14692591 : Blo 1907435 14692591 := bstep (se 1 (by rfl) ⟨11019443, by rfl⟩ : syracuseStep 14692591 = 22038887) B22038887
theorem B19590121 : Blo 1907435 19590121 := bstep (se 2 (by rfl) ⟨7346295, by rfl⟩ : syracuseStep 19590121 = 14692591) B14692591
theorem B26120161 : Blo 1907435 26120161 := bstep (se 2 (by rfl) ⟨9795060, by rfl⟩ : syracuseStep 26120161 = 19590121) B19590121
theorem B34826881 : Blo 1907435 34826881 := bstep (se 2 (by rfl) ⟨13060080, by rfl⟩ : syracuseStep 34826881 = 26120161) B26120161
theorem B46435841 : Blo 1907435 46435841 := bstep (se 2 (by rfl) ⟨17413440, by rfl⟩ : syracuseStep 46435841 = 34826881) B34826881
theorem B30957227 : Blo 1907435 30957227 := bstep (se 1 (by rfl) ⟨23217920, by rfl⟩ : syracuseStep 30957227 = 46435841) B46435841
theorem B20638151 : Blo 1907435 20638151 := bstep (se 1 (by rfl) ⟨15478613, by rfl⟩ : syracuseStep 20638151 = 30957227) B30957227
theorem B13758767 : Blo 1907435 13758767 := bstep (se 1 (by rfl) ⟨10319075, by rfl⟩ : syracuseStep 13758767 = 20638151) B20638151
theorem B9172511 : Blo 1907435 9172511 := bstep (se 1 (by rfl) ⟨6879383, by rfl⟩ : syracuseStep 9172511 = 13758767) B13758767
theorem B6115007 : Blo 1907435 6115007 := bstep (se 1 (by rfl) ⟨4586255, by rfl⟩ : syracuseStep 6115007 = 9172511) B9172511
theorem B4076671 : Blo 1907435 4076671 := bstep (se 1 (by rfl) ⟨3057503, by rfl⟩ : syracuseStep 4076671 = 6115007) B6115007
theorem B5435561 : Blo 1907435 5435561 := bstep (se 2 (by rfl) ⟨2038335, by rfl⟩ : syracuseStep 5435561 = 4076671) B4076671
theorem B3623707 : Blo 1907435 3623707 := bstep (se 1 (by rfl) ⟨2717780, by rfl⟩ : syracuseStep 3623707 = 5435561) B5435561
theorem B4831609 : Blo 1907435 4831609 := bstep (se 2 (by rfl) ⟨1811853, by rfl⟩ : syracuseStep 4831609 = 3623707) B3623707
theorem B6442145 : Blo 1907435 6442145 := bstep (se 2 (by rfl) ⟨2415804, by rfl⟩ : syracuseStep 6442145 = 4831609) B4831609
theorem B4294763 : Blo 1907435 4294763 := bstep (se 1 (by rfl) ⟨3221072, by rfl⟩ : syracuseStep 4294763 = 6442145) B6442145
theorem B2863175 : Blo 1907435 2863175 := bstep (se 1 (by rfl) ⟨2147381, by rfl⟩ : syracuseStep 2863175 = 4294763) B4294763
theorem B1908783 : Blo 1907435 1908783 := bstep (se 1 (by rfl) ⟨1431587, by rfl⟩ : syracuseStep 1908783 = 2863175) B2863175
theorem B2863181 : Blo 1907435 2863181 := bbase (se 3 (by rfl) ⟨536846, by rfl⟩ : syracuseStep 2863181 = 1073693) (by norm_num)
theorem B1908787 : Blo 1907435 1908787 := bstep (se 1 (by rfl) ⟨1431590, by rfl⟩ : syracuseStep 1908787 = 2863181) B2863181
theorem B4294781 : Blo 1907435 4294781 := bbase (se 3 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 4294781 = 1610543) (by norm_num)
theorem B2863187 : Blo 1907435 2863187 := bstep (se 1 (by rfl) ⟨2147390, by rfl⟩ : syracuseStep 2863187 = 4294781) B4294781
theorem B1908791 : Blo 1907435 1908791 := bstep (se 1 (by rfl) ⟨1431593, by rfl⟩ : syracuseStep 1908791 = 2863187) B2863187
theorem B3221093 : Blo 1907435 3221093 := bbase (se 4 (by rfl) ⟨301977, by rfl⟩ : syracuseStep 3221093 = 603955) (by norm_num)
theorem B2147395 : Blo 1907435 2147395 := bstep (se 1 (by rfl) ⟨1610546, by rfl⟩ : syracuseStep 2147395 = 3221093) B3221093
theorem B2863193 : Blo 1907435 2863193 := bstep (se 2 (by rfl) ⟨1073697, by rfl⟩ : syracuseStep 2863193 = 2147395) B2147395
theorem B1908795 : Blo 1907435 1908795 := bstep (se 1 (by rfl) ⟨1431596, by rfl⟩ : syracuseStep 1908795 = 2863193) B2863193
theorem B3673181 : Blo 1907435 3673181 := bbase (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) (by norm_num)
theorem B2448787 : Blo 1907435 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B3265049 : Blo 1907435 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B8706797 : Blo 1907435 8706797 := bstep (se 3 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 8706797 = 3265049) B3265049
theorem B5804531 : Blo 1907435 5804531 := bstep (se 1 (by rfl) ⟨4353398, by rfl⟩ : syracuseStep 5804531 = 8706797) B8706797
theorem B3869687 : Blo 1907435 3869687 := bstep (se 1 (by rfl) ⟨2902265, by rfl⟩ : syracuseStep 3869687 = 5804531) B5804531
theorem B2579791 : Blo 1907435 2579791 := bstep (se 1 (by rfl) ⟨1934843, by rfl⟩ : syracuseStep 2579791 = 3869687) B3869687
theorem B3439721 : Blo 1907435 3439721 := bstep (se 2 (by rfl) ⟨1289895, by rfl⟩ : syracuseStep 3439721 = 2579791) B2579791
theorem B2293147 : Blo 1907435 2293147 := bstep (se 1 (by rfl) ⟨1719860, by rfl⟩ : syracuseStep 2293147 = 3439721) B3439721
theorem B3057529 : Blo 1907435 3057529 := bstep (se 2 (by rfl) ⟨1146573, by rfl⟩ : syracuseStep 3057529 = 2293147) B2293147
theorem B4076705 : Blo 1907435 4076705 := bstep (se 2 (by rfl) ⟨1528764, by rfl⟩ : syracuseStep 4076705 = 3057529) B3057529
theorem B2717803 : Blo 1907435 2717803 := bstep (se 1 (by rfl) ⟨2038352, by rfl⟩ : syracuseStep 2717803 = 4076705) B4076705
theorem B14494949 : Blo 1907435 14494949 := bstep (se 4 (by rfl) ⟨1358901, by rfl⟩ : syracuseStep 14494949 = 2717803) B2717803
theorem B9663299 : Blo 1907435 9663299 := bstep (se 1 (by rfl) ⟨7247474, by rfl⟩ : syracuseStep 9663299 = 14494949) B14494949
theorem B6442199 : Blo 1907435 6442199 := bstep (se 1 (by rfl) ⟨4831649, by rfl⟩ : syracuseStep 6442199 = 9663299) B9663299
theorem B4294799 : Blo 1907435 4294799 := bstep (se 1 (by rfl) ⟨3221099, by rfl⟩ : syracuseStep 4294799 = 6442199) B6442199
theorem B2863199 : Blo 1907435 2863199 := bstep (se 1 (by rfl) ⟨2147399, by rfl⟩ : syracuseStep 2863199 = 4294799) B4294799
theorem B1908799 : Blo 1907435 1908799 := bstep (se 1 (by rfl) ⟨1431599, by rfl⟩ : syracuseStep 1908799 = 2863199) B2863199
theorem B2863205 : Blo 1907435 2863205 := bbase (se 4 (by rfl) ⟨268425, by rfl⟩ : syracuseStep 2863205 = 536851) (by norm_num)
theorem B1908803 : Blo 1907435 1908803 := bstep (se 1 (by rfl) ⟨1431602, by rfl⟩ : syracuseStep 1908803 = 2863205) B2863205
theorem B2293157 : Blo 1907435 2293157 := bbase (se 4 (by rfl) ⟨214983, by rfl⟩ : syracuseStep 2293157 = 429967) (by norm_num)
theorem B6115085 : Blo 1907435 6115085 := bstep (se 3 (by rfl) ⟨1146578, by rfl⟩ : syracuseStep 6115085 = 2293157) B2293157
theorem B4076723 : Blo 1907435 4076723 := bstep (se 1 (by rfl) ⟨3057542, by rfl⟩ : syracuseStep 4076723 = 6115085) B6115085
theorem B2717815 : Blo 1907435 2717815 := bstep (se 1 (by rfl) ⟨2038361, by rfl⟩ : syracuseStep 2717815 = 4076723) B4076723
theorem B3623753 : Blo 1907435 3623753 := bstep (se 2 (by rfl) ⟨1358907, by rfl⟩ : syracuseStep 3623753 = 2717815) B2717815
theorem B2415835 : Blo 1907435 2415835 := bstep (se 1 (by rfl) ⟨1811876, by rfl⟩ : syracuseStep 2415835 = 3623753) B3623753
theorem B3221113 : Blo 1907435 3221113 := bstep (se 2 (by rfl) ⟨1207917, by rfl⟩ : syracuseStep 3221113 = 2415835) B2415835
theorem B4294817 : Blo 1907435 4294817 := bstep (se 2 (by rfl) ⟨1610556, by rfl⟩ : syracuseStep 4294817 = 3221113) B3221113
theorem B2863211 : Blo 1907435 2863211 := bstep (se 1 (by rfl) ⟨2147408, by rfl⟩ : syracuseStep 2863211 = 4294817) B4294817
theorem B1908807 : Blo 1907435 1908807 := bstep (se 1 (by rfl) ⟨1431605, by rfl⟩ : syracuseStep 1908807 = 2863211) B2863211
theorem B2147413 : Blo 1907435 2147413 := bbase (se 8 (by rfl) ⟨12582, by rfl⟩ : syracuseStep 2147413 = 25165) (by norm_num)
theorem B2863217 : Blo 1907435 2863217 := bstep (se 2 (by rfl) ⟨1073706, by rfl⟩ : syracuseStep 2863217 = 2147413) B2147413
theorem B1908811 : Blo 1907435 1908811 := bstep (se 1 (by rfl) ⟨1431608, by rfl⟩ : syracuseStep 1908811 = 2863217) B2863217
theorem B2415845 : Blo 1907435 2415845 := bbase (se 4 (by rfl) ⟨226485, by rfl⟩ : syracuseStep 2415845 = 452971) (by norm_num)
theorem B6442253 : Blo 1907435 6442253 := bstep (se 3 (by rfl) ⟨1207922, by rfl⟩ : syracuseStep 6442253 = 2415845) B2415845
theorem B4294835 : Blo 1907435 4294835 := bstep (se 1 (by rfl) ⟨3221126, by rfl⟩ : syracuseStep 4294835 = 6442253) B6442253
theorem B2863223 : Blo 1907435 2863223 := bstep (se 1 (by rfl) ⟨2147417, by rfl⟩ : syracuseStep 2863223 = 4294835) B4294835
theorem B1908815 : Blo 1907435 1908815 := bstep (se 1 (by rfl) ⟨1431611, by rfl⟩ : syracuseStep 1908815 = 2863223) B2863223
theorem B2863229 : Blo 1907435 2863229 := bbase (se 3 (by rfl) ⟨536855, by rfl⟩ : syracuseStep 2863229 = 1073711) (by norm_num)
theorem B1908819 : Blo 1907435 1908819 := bstep (se 1 (by rfl) ⟨1431614, by rfl⟩ : syracuseStep 1908819 = 2863229) B2863229
theorem B4294853 : Blo 1907435 4294853 := bbase (se 4 (by rfl) ⟨402642, by rfl⟩ : syracuseStep 4294853 = 805285) (by norm_num)
theorem B2863235 : Blo 1907435 2863235 := bstep (se 1 (by rfl) ⟨2147426, by rfl⟩ : syracuseStep 2863235 = 4294853) B4294853
theorem B1908823 : Blo 1907435 1908823 := bstep (se 1 (by rfl) ⟨1431617, by rfl⟩ : syracuseStep 1908823 = 2863235) B2863235
theorem B11019701 : Blo 1907435 11019701 := bbase (se 5 (by rfl) ⟨516548, by rfl⟩ : syracuseStep 11019701 = 1033097) (by norm_num)
theorem B7346467 : Blo 1907435 7346467 := bstep (se 1 (by rfl) ⟨5509850, by rfl⟩ : syracuseStep 7346467 = 11019701) B11019701
theorem B9795289 : Blo 1907435 9795289 := bstep (se 2 (by rfl) ⟨3673233, by rfl⟩ : syracuseStep 9795289 = 7346467) B7346467
theorem B13060385 : Blo 1907435 13060385 := bstep (se 2 (by rfl) ⟨4897644, by rfl⟩ : syracuseStep 13060385 = 9795289) B9795289
theorem B8706923 : Blo 1907435 8706923 := bstep (se 1 (by rfl) ⟨6530192, by rfl⟩ : syracuseStep 8706923 = 13060385) B13060385
theorem B5804615 : Blo 1907435 5804615 := bstep (se 1 (by rfl) ⟨4353461, by rfl⟩ : syracuseStep 5804615 = 8706923) B8706923
theorem B3869743 : Blo 1907435 3869743 := bstep (se 1 (by rfl) ⟨2902307, by rfl⟩ : syracuseStep 3869743 = 5804615) B5804615
theorem B5159657 : Blo 1907435 5159657 := bstep (se 2 (by rfl) ⟨1934871, by rfl⟩ : syracuseStep 5159657 = 3869743) B3869743
theorem B13759085 : Blo 1907435 13759085 := bstep (se 3 (by rfl) ⟨2579828, by rfl⟩ : syracuseStep 13759085 = 5159657) B5159657
theorem B9172723 : Blo 1907435 9172723 := bstep (se 1 (by rfl) ⟨6879542, by rfl⟩ : syracuseStep 9172723 = 13759085) B13759085
theorem B12230297 : Blo 1907435 12230297 := bstep (se 2 (by rfl) ⟨4586361, by rfl⟩ : syracuseStep 12230297 = 9172723) B9172723
theorem B8153531 : Blo 1907435 8153531 := bstep (se 1 (by rfl) ⟨6115148, by rfl⟩ : syracuseStep 8153531 = 12230297) B12230297
theorem B5435687 : Blo 1907435 5435687 := bstep (se 1 (by rfl) ⟨4076765, by rfl⟩ : syracuseStep 5435687 = 8153531) B8153531
theorem B3623791 : Blo 1907435 3623791 := bstep (se 1 (by rfl) ⟨2717843, by rfl⟩ : syracuseStep 3623791 = 5435687) B5435687
theorem B4831721 : Blo 1907435 4831721 := bstep (se 2 (by rfl) ⟨1811895, by rfl⟩ : syracuseStep 4831721 = 3623791) B3623791
theorem B3221147 : Blo 1907435 3221147 := bstep (se 1 (by rfl) ⟨2415860, by rfl⟩ : syracuseStep 3221147 = 4831721) B4831721
theorem B2147431 : Blo 1907435 2147431 := bstep (se 1 (by rfl) ⟨1610573, by rfl⟩ : syracuseStep 2147431 = 3221147) B3221147
theorem B2863241 : Blo 1907435 2863241 := bstep (se 2 (by rfl) ⟨1073715, by rfl⟩ : syracuseStep 2863241 = 2147431) B2147431
theorem B1908827 : Blo 1907435 1908827 := bstep (se 1 (by rfl) ⟨1431620, by rfl⟩ : syracuseStep 1908827 = 2863241) B2863241
theorem B9663461 : Blo 1907435 9663461 := bbase (se 4 (by rfl) ⟨905949, by rfl⟩ : syracuseStep 9663461 = 1811899) (by norm_num)
theorem B6442307 : Blo 1907435 6442307 := bstep (se 1 (by rfl) ⟨4831730, by rfl⟩ : syracuseStep 6442307 = 9663461) B9663461
theorem B4294871 : Blo 1907435 4294871 := bstep (se 1 (by rfl) ⟨3221153, by rfl⟩ : syracuseStep 4294871 = 6442307) B6442307
theorem B2863247 : Blo 1907435 2863247 := bstep (se 1 (by rfl) ⟨2147435, by rfl⟩ : syracuseStep 2863247 = 4294871) B4294871
theorem B1908831 : Blo 1907435 1908831 := bstep (se 1 (by rfl) ⟨1431623, by rfl⟩ : syracuseStep 1908831 = 2863247) B2863247
theorem B2863253 : Blo 1907435 2863253 := bbase (se 6 (by rfl) ⟨67107, by rfl⟩ : syracuseStep 2863253 = 134215) (by norm_num)
theorem B1908835 : Blo 1907435 1908835 := bstep (se 1 (by rfl) ⟨1431626, by rfl⟩ : syracuseStep 1908835 = 2863253) B2863253
theorem B2579845 : Blo 1907435 2579845 := bbase (se 4 (by rfl) ⟨241860, by rfl⟩ : syracuseStep 2579845 = 483721) (by norm_num)
theorem B3439793 : Blo 1907435 3439793 := bstep (se 2 (by rfl) ⟨1289922, by rfl⟩ : syracuseStep 3439793 = 2579845) B2579845
theorem B2293195 : Blo 1907435 2293195 := bstep (se 1 (by rfl) ⟨1719896, by rfl⟩ : syracuseStep 2293195 = 3439793) B3439793
theorem B3057593 : Blo 1907435 3057593 := bstep (se 2 (by rfl) ⟨1146597, by rfl⟩ : syracuseStep 3057593 = 2293195) B2293195
theorem B8153581 : Blo 1907435 8153581 := bstep (se 3 (by rfl) ⟨1528796, by rfl⟩ : syracuseStep 8153581 = 3057593) B3057593
theorem B10871441 : Blo 1907435 10871441 := bstep (se 2 (by rfl) ⟨4076790, by rfl⟩ : syracuseStep 10871441 = 8153581) B8153581
theorem B7247627 : Blo 1907435 7247627 := bstep (se 1 (by rfl) ⟨5435720, by rfl⟩ : syracuseStep 7247627 = 10871441) B10871441
theorem B4831751 : Blo 1907435 4831751 := bstep (se 1 (by rfl) ⟨3623813, by rfl⟩ : syracuseStep 4831751 = 7247627) B7247627
theorem B3221167 : Blo 1907435 3221167 := bstep (se 1 (by rfl) ⟨2415875, by rfl⟩ : syracuseStep 3221167 = 4831751) B4831751
theorem B4294889 : Blo 1907435 4294889 := bstep (se 2 (by rfl) ⟨1610583, by rfl⟩ : syracuseStep 4294889 = 3221167) B3221167
theorem B2863259 : Blo 1907435 2863259 := bstep (se 1 (by rfl) ⟨2147444, by rfl⟩ : syracuseStep 2863259 = 4294889) B4294889
theorem B1908839 : Blo 1907435 1908839 := bstep (se 1 (by rfl) ⟨1431629, by rfl⟩ : syracuseStep 1908839 = 2863259) B2863259
theorem B2147449 : Blo 1907435 2147449 := bbase (se 2 (by rfl) ⟨805293, by rfl⟩ : syracuseStep 2147449 = 1610587) (by norm_num)
theorem B2863265 : Blo 1907435 2863265 := bstep (se 2 (by rfl) ⟨1073724, by rfl⟩ : syracuseStep 2863265 = 2147449) B2147449
theorem B1908843 : Blo 1907435 1908843 := bstep (se 1 (by rfl) ⟨1431632, by rfl⟩ : syracuseStep 1908843 = 2863265) B2863265
theorem B8707013 : Blo 1907435 8707013 := bbase (se 4 (by rfl) ⟨816282, by rfl⟩ : syracuseStep 8707013 = 1632565) (by norm_num)
theorem B5804675 : Blo 1907435 5804675 := bstep (se 1 (by rfl) ⟨4353506, by rfl⟩ : syracuseStep 5804675 = 8707013) B8707013
theorem B3869783 : Blo 1907435 3869783 := bstep (se 1 (by rfl) ⟨2902337, by rfl⟩ : syracuseStep 3869783 = 5804675) B5804675
theorem B2579855 : Blo 1907435 2579855 := bstep (se 1 (by rfl) ⟨1934891, by rfl⟩ : syracuseStep 2579855 = 3869783) B3869783
theorem B27518453 : Blo 1907435 27518453 := bstep (se 5 (by rfl) ⟨1289927, by rfl⟩ : syracuseStep 27518453 = 2579855) B2579855
theorem B18345635 : Blo 1907435 18345635 := bstep (se 1 (by rfl) ⟨13759226, by rfl⟩ : syracuseStep 18345635 = 27518453) B27518453
theorem B12230423 : Blo 1907435 12230423 := bstep (se 1 (by rfl) ⟨9172817, by rfl⟩ : syracuseStep 12230423 = 18345635) B18345635
theorem B8153615 : Blo 1907435 8153615 := bstep (se 1 (by rfl) ⟨6115211, by rfl⟩ : syracuseStep 8153615 = 12230423) B12230423
theorem B5435743 : Blo 1907435 5435743 := bstep (se 1 (by rfl) ⟨4076807, by rfl⟩ : syracuseStep 5435743 = 8153615) B8153615
theorem B7247657 : Blo 1907435 7247657 := bstep (se 2 (by rfl) ⟨2717871, by rfl⟩ : syracuseStep 7247657 = 5435743) B5435743
theorem B4831771 : Blo 1907435 4831771 := bstep (se 1 (by rfl) ⟨3623828, by rfl⟩ : syracuseStep 4831771 = 7247657) B7247657
theorem B6442361 : Blo 1907435 6442361 := bstep (se 2 (by rfl) ⟨2415885, by rfl⟩ : syracuseStep 6442361 = 4831771) B4831771
theorem B4294907 : Blo 1907435 4294907 := bstep (se 1 (by rfl) ⟨3221180, by rfl⟩ : syracuseStep 4294907 = 6442361) B6442361
theorem B2863271 : Blo 1907435 2863271 := bstep (se 1 (by rfl) ⟨2147453, by rfl⟩ : syracuseStep 2863271 = 4294907) B4294907
theorem B1908847 : Blo 1907435 1908847 := bstep (se 1 (by rfl) ⟨1431635, by rfl⟩ : syracuseStep 1908847 = 2863271) B2863271
theorem B2863277 : Blo 1907435 2863277 := bbase (se 3 (by rfl) ⟨536864, by rfl⟩ : syracuseStep 2863277 = 1073729) (by norm_num)
theorem B1908851 : Blo 1907435 1908851 := bstep (se 1 (by rfl) ⟨1431638, by rfl⟩ : syracuseStep 1908851 = 2863277) B2863277
theorem B4294925 : Blo 1907435 4294925 := bbase (se 3 (by rfl) ⟨805298, by rfl⟩ : syracuseStep 4294925 = 1610597) (by norm_num)
theorem B2863283 : Blo 1907435 2863283 := bstep (se 1 (by rfl) ⟨2147462, by rfl⟩ : syracuseStep 2863283 = 4294925) B4294925
theorem B1908855 : Blo 1907435 1908855 := bstep (se 1 (by rfl) ⟨1431641, by rfl⟩ : syracuseStep 1908855 = 2863283) B2863283
theorem B2415901 : Blo 1907435 2415901 := bbase (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) (by norm_num)
theorem B3221201 : Blo 1907435 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B2147467 : Blo 1907435 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B2863289 : Blo 1907435 2863289 := bstep (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) B2147467
theorem B1908859 : Blo 1907435 1908859 := bstep (se 1 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 1908859 = 2863289) B2863289
theorem B3265157 : Blo 1907435 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B8707085 : Blo 1907435 8707085 := bstep (se 3 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 8707085 = 3265157) B3265157
theorem B5804723 : Blo 1907435 5804723 := bstep (se 1 (by rfl) ⟨4353542, by rfl⟩ : syracuseStep 5804723 = 8707085) B8707085
theorem B15479261 : Blo 1907435 15479261 := bstep (se 3 (by rfl) ⟨2902361, by rfl⟩ : syracuseStep 15479261 = 5804723) B5804723
theorem B10319507 : Blo 1907435 10319507 := bstep (se 1 (by rfl) ⟨7739630, by rfl⟩ : syracuseStep 10319507 = 15479261) B15479261
theorem B6879671 : Blo 1907435 6879671 := bstep (se 1 (by rfl) ⟨5159753, by rfl⟩ : syracuseStep 6879671 = 10319507) B10319507
theorem B4586447 : Blo 1907435 4586447 := bstep (se 1 (by rfl) ⟨3439835, by rfl⟩ : syracuseStep 4586447 = 6879671) B6879671
theorem B3057631 : Blo 1907435 3057631 := bstep (se 1 (by rfl) ⟨2293223, by rfl⟩ : syracuseStep 3057631 = 4586447) B4586447
theorem B16307365 : Blo 1907435 16307365 := bstep (se 4 (by rfl) ⟨1528815, by rfl⟩ : syracuseStep 16307365 = 3057631) B3057631
theorem B21743153 : Blo 1907435 21743153 := bstep (se 2 (by rfl) ⟨8153682, by rfl⟩ : syracuseStep 21743153 = 16307365) B16307365
theorem B14495435 : Blo 1907435 14495435 := bstep (se 1 (by rfl) ⟨10871576, by rfl⟩ : syracuseStep 14495435 = 21743153) B21743153
theorem B9663623 : Blo 1907435 9663623 := bstep (se 1 (by rfl) ⟨7247717, by rfl⟩ : syracuseStep 9663623 = 14495435) B14495435
theorem B6442415 : Blo 1907435 6442415 := bstep (se 1 (by rfl) ⟨4831811, by rfl⟩ : syracuseStep 6442415 = 9663623) B9663623
theorem B4294943 : Blo 1907435 4294943 := bstep (se 1 (by rfl) ⟨3221207, by rfl⟩ : syracuseStep 4294943 = 6442415) B6442415
theorem B2863295 : Blo 1907435 2863295 := bstep (se 1 (by rfl) ⟨2147471, by rfl⟩ : syracuseStep 2863295 = 4294943) B4294943
theorem B1908863 : Blo 1907435 1908863 := bstep (se 1 (by rfl) ⟨1431647, by rfl⟩ : syracuseStep 1908863 = 2863295) B2863295
theorem B2863301 : Blo 1907435 2863301 := bbase (se 4 (by rfl) ⟨268434, by rfl⟩ : syracuseStep 2863301 = 536869) (by norm_num)
theorem B1908867 : Blo 1907435 1908867 := bstep (se 1 (by rfl) ⟨1431650, by rfl⟩ : syracuseStep 1908867 = 2863301) B2863301
theorem B3221221 : Blo 1907435 3221221 := bbase (se 4 (by rfl) ⟨301989, by rfl⟩ : syracuseStep 3221221 = 603979) (by norm_num)
theorem B4294961 : Blo 1907435 4294961 := bstep (se 2 (by rfl) ⟨1610610, by rfl⟩ : syracuseStep 4294961 = 3221221) B3221221
theorem B2863307 : Blo 1907435 2863307 := bstep (se 1 (by rfl) ⟨2147480, by rfl⟩ : syracuseStep 2863307 = 4294961) B4294961
theorem B1908871 : Blo 1907435 1908871 := bstep (se 1 (by rfl) ⟨1431653, by rfl⟩ : syracuseStep 1908871 = 2863307) B2863307
theorem B2147485 : Blo 1907435 2147485 := bbase (se 3 (by rfl) ⟨402653, by rfl⟩ : syracuseStep 2147485 = 805307) (by norm_num)
theorem B2863313 : Blo 1907435 2863313 := bstep (se 2 (by rfl) ⟨1073742, by rfl⟩ : syracuseStep 2863313 = 2147485) B2147485
theorem B1908875 : Blo 1907435 1908875 := bstep (se 1 (by rfl) ⟨1431656, by rfl⟩ : syracuseStep 1908875 = 2863313) B2863313
theorem B6442469 : Blo 1907435 6442469 := bbase (se 4 (by rfl) ⟨603981, by rfl⟩ : syracuseStep 6442469 = 1207963) (by norm_num)
theorem B4294979 : Blo 1907435 4294979 := bstep (se 1 (by rfl) ⟨3221234, by rfl⟩ : syracuseStep 4294979 = 6442469) B6442469
theorem B2863319 : Blo 1907435 2863319 := bstep (se 1 (by rfl) ⟨2147489, by rfl⟩ : syracuseStep 2863319 = 4294979) B4294979
theorem B1908879 : Blo 1907435 1908879 := bstep (se 1 (by rfl) ⟨1431659, by rfl⟩ : syracuseStep 1908879 = 2863319) B2863319
theorem B2863325 : Blo 1907435 2863325 := bbase (se 3 (by rfl) ⟨536873, by rfl⟩ : syracuseStep 2863325 = 1073747) (by norm_num)
theorem B1908883 : Blo 1907435 1908883 := bstep (se 1 (by rfl) ⟨1431662, by rfl⟩ : syracuseStep 1908883 = 2863325) B2863325
theorem B4294997 : Blo 1907435 4294997 := bbase (se 10 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 4294997 = 12583) (by norm_num)
theorem B2863331 : Blo 1907435 2863331 := bstep (se 1 (by rfl) ⟨2147498, by rfl⟩ : syracuseStep 2863331 = 4294997) B4294997
theorem B1908887 : Blo 1907435 1908887 := bstep (se 1 (by rfl) ⟨1431665, by rfl⟩ : syracuseStep 1908887 = 2863331) B2863331
theorem B3057677 : Blo 1907435 3057677 := bbase (se 3 (by rfl) ⟨573314, by rfl⟩ : syracuseStep 3057677 = 1146629) (by norm_num)
theorem B2038451 : Blo 1907435 2038451 := bstep (se 1 (by rfl) ⟨1528838, by rfl⟩ : syracuseStep 2038451 = 3057677) B3057677
theorem B5435869 : Blo 1907435 5435869 := bstep (se 3 (by rfl) ⟨1019225, by rfl⟩ : syracuseStep 5435869 = 2038451) B2038451
theorem B7247825 : Blo 1907435 7247825 := bstep (se 2 (by rfl) ⟨2717934, by rfl⟩ : syracuseStep 7247825 = 5435869) B5435869
theorem B4831883 : Blo 1907435 4831883 := bstep (se 1 (by rfl) ⟨3623912, by rfl⟩ : syracuseStep 4831883 = 7247825) B7247825
theorem B3221255 : Blo 1907435 3221255 := bstep (se 1 (by rfl) ⟨2415941, by rfl⟩ : syracuseStep 3221255 = 4831883) B4831883
theorem B2147503 : Blo 1907435 2147503 := bstep (se 1 (by rfl) ⟨1610627, by rfl⟩ : syracuseStep 2147503 = 3221255) B3221255
theorem B2863337 : Blo 1907435 2863337 := bstep (se 2 (by rfl) ⟨1073751, by rfl⟩ : syracuseStep 2863337 = 2147503) B2147503
theorem B1908891 : Blo 1907435 1908891 := bstep (se 1 (by rfl) ⟨1431668, by rfl⟩ : syracuseStep 1908891 = 2863337) B2863337
theorem B29386901 : Blo 1907435 29386901 := bbase (se 6 (by rfl) ⟨688755, by rfl⟩ : syracuseStep 29386901 = 1377511) (by norm_num)
theorem B19591267 : Blo 1907435 19591267 := bstep (se 1 (by rfl) ⟨14693450, by rfl⟩ : syracuseStep 19591267 = 29386901) B29386901
theorem B26121689 : Blo 1907435 26121689 := bstep (se 2 (by rfl) ⟨9795633, by rfl⟩ : syracuseStep 26121689 = 19591267) B19591267
theorem B17414459 : Blo 1907435 17414459 := bstep (se 1 (by rfl) ⟨13060844, by rfl⟩ : syracuseStep 17414459 = 26121689) B26121689
theorem B11609639 : Blo 1907435 11609639 := bstep (se 1 (by rfl) ⟨8707229, by rfl⟩ : syracuseStep 11609639 = 17414459) B17414459
theorem B7739759 : Blo 1907435 7739759 := bstep (se 1 (by rfl) ⟨5804819, by rfl⟩ : syracuseStep 7739759 = 11609639) B11609639
theorem B20639357 : Blo 1907435 20639357 := bstep (se 3 (by rfl) ⟨3869879, by rfl⟩ : syracuseStep 20639357 = 7739759) B7739759
theorem B13759571 : Blo 1907435 13759571 := bstep (se 1 (by rfl) ⟨10319678, by rfl⟩ : syracuseStep 13759571 = 20639357) B20639357
theorem B36692189 : Blo 1907435 36692189 := bstep (se 3 (by rfl) ⟨6879785, by rfl⟩ : syracuseStep 36692189 = 13759571) B13759571
theorem B24461459 : Blo 1907435 24461459 := bstep (se 1 (by rfl) ⟨18346094, by rfl⟩ : syracuseStep 24461459 = 36692189) B36692189
theorem B16307639 : Blo 1907435 16307639 := bstep (se 1 (by rfl) ⟨12230729, by rfl⟩ : syracuseStep 16307639 = 24461459) B24461459
theorem B10871759 : Blo 1907435 10871759 := bstep (se 1 (by rfl) ⟨8153819, by rfl⟩ : syracuseStep 10871759 = 16307639) B16307639
theorem B7247839 : Blo 1907435 7247839 := bstep (se 1 (by rfl) ⟨5435879, by rfl⟩ : syracuseStep 7247839 = 10871759) B10871759
theorem B9663785 : Blo 1907435 9663785 := bstep (se 2 (by rfl) ⟨3623919, by rfl⟩ : syracuseStep 9663785 = 7247839) B7247839
theorem B6442523 : Blo 1907435 6442523 := bstep (se 1 (by rfl) ⟨4831892, by rfl⟩ : syracuseStep 6442523 = 9663785) B9663785
theorem B4295015 : Blo 1907435 4295015 := bstep (se 1 (by rfl) ⟨3221261, by rfl⟩ : syracuseStep 4295015 = 6442523) B6442523
theorem B2863343 : Blo 1907435 2863343 := bstep (se 1 (by rfl) ⟨2147507, by rfl⟩ : syracuseStep 2863343 = 4295015) B4295015
theorem B1908895 : Blo 1907435 1908895 := bstep (se 1 (by rfl) ⟨1431671, by rfl⟩ : syracuseStep 1908895 = 2863343) B2863343
theorem B2863349 : Blo 1907435 2863349 := bbase (se 5 (by rfl) ⟨134219, by rfl⟩ : syracuseStep 2863349 = 268439) (by norm_num)
theorem B1908899 : Blo 1907435 1908899 := bstep (se 1 (by rfl) ⟨1431674, by rfl⟩ : syracuseStep 1908899 = 2863349) B2863349
theorem B3272053 : Blo 1907435 3272053 := bbase (se 5 (by rfl) ⟨153377, by rfl⟩ : syracuseStep 3272053 = 306755) (by norm_num)
theorem B4362737 : Blo 1907435 4362737 := bstep (se 2 (by rfl) ⟨1636026, by rfl⟩ : syracuseStep 4362737 = 3272053) B3272053
theorem B11633965 : Blo 1907435 11633965 := bstep (se 3 (by rfl) ⟨2181368, by rfl⟩ : syracuseStep 11633965 = 4362737) B4362737
theorem B62047813 : Blo 1907435 62047813 := bstep (se 4 (by rfl) ⟨5816982, by rfl⟩ : syracuseStep 62047813 = 11633965) B11633965
theorem B82730417 : Blo 1907435 82730417 := bstep (se 2 (by rfl) ⟨31023906, by rfl⟩ : syracuseStep 82730417 = 62047813) B62047813
theorem B220614445 : Blo 1907435 220614445 := bstep (se 3 (by rfl) ⟨41365208, by rfl⟩ : syracuseStep 220614445 = 82730417) B82730417
theorem B1176610373 : Blo 1907435 1176610373 := bstep (se 4 (by rfl) ⟨110307222, by rfl⟩ : syracuseStep 1176610373 = 220614445) B220614445
theorem B784406915 : Blo 1907435 784406915 := bstep (se 1 (by rfl) ⟨588305186, by rfl⟩ : syracuseStep 784406915 = 1176610373) B1176610373
theorem B522937943 : Blo 1907435 522937943 := bstep (se 1 (by rfl) ⟨392203457, by rfl⟩ : syracuseStep 522937943 = 784406915) B784406915
theorem B348625295 : Blo 1907435 348625295 := bstep (se 1 (by rfl) ⟨261468971, by rfl⟩ : syracuseStep 348625295 = 522937943) B522937943
theorem B232416863 : Blo 1907435 232416863 := bstep (se 1 (by rfl) ⟨174312647, by rfl⟩ : syracuseStep 232416863 = 348625295) B348625295
theorem B154944575 : Blo 1907435 154944575 := bstep (se 1 (by rfl) ⟨116208431, by rfl⟩ : syracuseStep 154944575 = 232416863) B232416863
theorem B103296383 : Blo 1907435 103296383 := bstep (se 1 (by rfl) ⟨77472287, by rfl⟩ : syracuseStep 103296383 = 154944575) B154944575
theorem B68864255 : Blo 1907435 68864255 := bstep (se 1 (by rfl) ⟨51648191, by rfl⟩ : syracuseStep 68864255 = 103296383) B103296383
theorem B45909503 : Blo 1907435 45909503 := bstep (se 1 (by rfl) ⟨34432127, by rfl⟩ : syracuseStep 45909503 = 68864255) B68864255
theorem B30606335 : Blo 1907435 30606335 := bstep (se 1 (by rfl) ⟨22954751, by rfl⟩ : syracuseStep 30606335 = 45909503) B45909503
theorem B20404223 : Blo 1907435 20404223 := bstep (se 1 (by rfl) ⟨15303167, by rfl⟩ : syracuseStep 20404223 = 30606335) B30606335
theorem B13602815 : Blo 1907435 13602815 := bstep (se 1 (by rfl) ⟨10202111, by rfl⟩ : syracuseStep 13602815 = 20404223) B20404223
theorem B9068543 : Blo 1907435 9068543 := bstep (se 1 (by rfl) ⟨6801407, by rfl⟩ : syracuseStep 9068543 = 13602815) B13602815
theorem B6045695 : Blo 1907435 6045695 := bstep (se 1 (by rfl) ⟨4534271, by rfl⟩ : syracuseStep 6045695 = 9068543) B9068543
theorem B4030463 : Blo 1907435 4030463 := bstep (se 1 (by rfl) ⟨3022847, by rfl⟩ : syracuseStep 4030463 = 6045695) B6045695
theorem B2686975 : Blo 1907435 2686975 := bstep (se 1 (by rfl) ⟨2015231, by rfl⟩ : syracuseStep 2686975 = 4030463) B4030463
theorem B14330533 : Blo 1907435 14330533 := bstep (se 4 (by rfl) ⟨1343487, by rfl⟩ : syracuseStep 14330533 = 2686975) B2686975
theorem B19107377 : Blo 1907435 19107377 := bstep (se 2 (by rfl) ⟨7165266, by rfl⟩ : syracuseStep 19107377 = 14330533) B14330533
theorem B12738251 : Blo 1907435 12738251 := bstep (se 1 (by rfl) ⟨9553688, by rfl⟩ : syracuseStep 12738251 = 19107377) B19107377
theorem B8492167 : Blo 1907435 8492167 := bstep (se 1 (by rfl) ⟨6369125, by rfl⟩ : syracuseStep 8492167 = 12738251) B12738251
theorem B45291557 : Blo 1907435 45291557 := bstep (se 4 (by rfl) ⟨4246083, by rfl⟩ : syracuseStep 45291557 = 8492167) B8492167
theorem B30194371 : Blo 1907435 30194371 := bstep (se 1 (by rfl) ⟨22645778, by rfl⟩ : syracuseStep 30194371 = 45291557) B45291557
theorem B40259161 : Blo 1907435 40259161 := bstep (se 2 (by rfl) ⟨15097185, by rfl⟩ : syracuseStep 40259161 = 30194371) B30194371
theorem B53678881 : Blo 1907435 53678881 := bstep (se 2 (by rfl) ⟨20129580, by rfl⟩ : syracuseStep 53678881 = 40259161) B40259161
theorem B286287365 : Blo 1907435 286287365 := bstep (se 4 (by rfl) ⟨26839440, by rfl⟩ : syracuseStep 286287365 = 53678881) B53678881
theorem B190858243 : Blo 1907435 190858243 := bstep (se 1 (by rfl) ⟨143143682, by rfl⟩ : syracuseStep 190858243 = 286287365) B286287365
theorem B254477657 : Blo 1907435 254477657 := bstep (se 2 (by rfl) ⟨95429121, by rfl⟩ : syracuseStep 254477657 = 190858243) B190858243
theorem B678607085 : Blo 1907435 678607085 := bstep (se 3 (by rfl) ⟨127238828, by rfl⟩ : syracuseStep 678607085 = 254477657) B254477657
theorem B452404723 : Blo 1907435 452404723 := bstep (se 1 (by rfl) ⟨339303542, by rfl⟩ : syracuseStep 452404723 = 678607085) B678607085
theorem B603206297 : Blo 1907435 603206297 := bstep (se 2 (by rfl) ⟨226202361, by rfl⟩ : syracuseStep 603206297 = 452404723) B452404723
theorem B402137531 : Blo 1907435 402137531 := bstep (se 1 (by rfl) ⟨301603148, by rfl⟩ : syracuseStep 402137531 = 603206297) B603206297
theorem B268091687 : Blo 1907435 268091687 := bstep (se 1 (by rfl) ⟨201068765, by rfl⟩ : syracuseStep 268091687 = 402137531) B402137531
theorem B178727791 : Blo 1907435 178727791 := bstep (se 1 (by rfl) ⟨134045843, by rfl⟩ : syracuseStep 178727791 = 268091687) B268091687
theorem B238303721 : Blo 1907435 238303721 := bstep (se 2 (by rfl) ⟨89363895, by rfl⟩ : syracuseStep 238303721 = 178727791) B178727791
theorem B158869147 : Blo 1907435 158869147 := bstep (se 1 (by rfl) ⟨119151860, by rfl⟩ : syracuseStep 158869147 = 238303721) B238303721
theorem B211825529 : Blo 1907435 211825529 := bstep (se 2 (by rfl) ⟨79434573, by rfl⟩ : syracuseStep 211825529 = 158869147) B158869147
theorem B141217019 : Blo 1907435 141217019 := bstep (se 1 (by rfl) ⟨105912764, by rfl⟩ : syracuseStep 141217019 = 211825529) B211825529
theorem B94144679 : Blo 1907435 94144679 := bstep (se 1 (by rfl) ⟨70608509, by rfl⟩ : syracuseStep 94144679 = 141217019) B141217019
theorem B62763119 : Blo 1907435 62763119 := bstep (se 1 (by rfl) ⟨47072339, by rfl⟩ : syracuseStep 62763119 = 94144679) B94144679
theorem B41842079 : Blo 1907435 41842079 := bstep (se 1 (by rfl) ⟨31381559, by rfl⟩ : syracuseStep 41842079 = 62763119) B62763119
theorem B27894719 : Blo 1907435 27894719 := bstep (se 1 (by rfl) ⟨20921039, by rfl⟩ : syracuseStep 27894719 = 41842079) B41842079
theorem B18596479 : Blo 1907435 18596479 := bstep (se 1 (by rfl) ⟨13947359, by rfl⟩ : syracuseStep 18596479 = 27894719) B27894719
theorem B24795305 : Blo 1907435 24795305 := bstep (se 2 (by rfl) ⟨9298239, by rfl⟩ : syracuseStep 24795305 = 18596479) B18596479
theorem B16530203 : Blo 1907435 16530203 := bstep (se 1 (by rfl) ⟨12397652, by rfl⟩ : syracuseStep 16530203 = 24795305) B24795305
theorem B44080541 : Blo 1907435 44080541 := bstep (se 3 (by rfl) ⟨8265101, by rfl⟩ : syracuseStep 44080541 = 16530203) B16530203
theorem B29387027 : Blo 1907435 29387027 := bstep (se 1 (by rfl) ⟨22040270, by rfl⟩ : syracuseStep 29387027 = 44080541) B44080541
theorem B19591351 : Blo 1907435 19591351 := bstep (se 1 (by rfl) ⟨14693513, by rfl⟩ : syracuseStep 19591351 = 29387027) B29387027
theorem B104487205 : Blo 1907435 104487205 := bstep (se 4 (by rfl) ⟨9795675, by rfl⟩ : syracuseStep 104487205 = 19591351) B19591351
theorem B139316273 : Blo 1907435 139316273 := bstep (se 2 (by rfl) ⟨52243602, by rfl⟩ : syracuseStep 139316273 = 104487205) B104487205
theorem B92877515 : Blo 1907435 92877515 := bstep (se 1 (by rfl) ⟨69658136, by rfl⟩ : syracuseStep 92877515 = 139316273) B139316273
theorem B61918343 : Blo 1907435 61918343 := bstep (se 1 (by rfl) ⟨46438757, by rfl⟩ : syracuseStep 61918343 = 92877515) B92877515
theorem B41278895 : Blo 1907435 41278895 := bstep (se 1 (by rfl) ⟨30959171, by rfl⟩ : syracuseStep 41278895 = 61918343) B61918343
theorem B27519263 : Blo 1907435 27519263 := bstep (se 1 (by rfl) ⟨20639447, by rfl⟩ : syracuseStep 27519263 = 41278895) B41278895
theorem B18346175 : Blo 1907435 18346175 := bstep (se 1 (by rfl) ⟨13759631, by rfl⟩ : syracuseStep 18346175 = 27519263) B27519263
theorem B12230783 : Blo 1907435 12230783 := bstep (se 1 (by rfl) ⟨9173087, by rfl⟩ : syracuseStep 12230783 = 18346175) B18346175
theorem B8153855 : Blo 1907435 8153855 := bstep (se 1 (by rfl) ⟨6115391, by rfl⟩ : syracuseStep 8153855 = 12230783) B12230783
theorem B5435903 : Blo 1907435 5435903 := bstep (se 1 (by rfl) ⟨4076927, by rfl⟩ : syracuseStep 5435903 = 8153855) B8153855
theorem B3623935 : Blo 1907435 3623935 := bstep (se 1 (by rfl) ⟨2717951, by rfl⟩ : syracuseStep 3623935 = 5435903) B5435903
theorem B4831913 : Blo 1907435 4831913 := bstep (se 2 (by rfl) ⟨1811967, by rfl⟩ : syracuseStep 4831913 = 3623935) B3623935
theorem B3221275 : Blo 1907435 3221275 := bstep (se 1 (by rfl) ⟨2415956, by rfl⟩ : syracuseStep 3221275 = 4831913) B4831913
theorem B4295033 : Blo 1907435 4295033 := bstep (se 2 (by rfl) ⟨1610637, by rfl⟩ : syracuseStep 4295033 = 3221275) B3221275
theorem B2863355 : Blo 1907435 2863355 := bstep (se 1 (by rfl) ⟨2147516, by rfl⟩ : syracuseStep 2863355 = 4295033) B4295033
theorem B1908903 : Blo 1907435 1908903 := bstep (se 1 (by rfl) ⟨1431677, by rfl⟩ : syracuseStep 1908903 = 2863355) B2863355
theorem B2147521 : Blo 1907435 2147521 := bbase (se 2 (by rfl) ⟨805320, by rfl⟩ : syracuseStep 2147521 = 1610641) (by norm_num)
theorem B2863361 : Blo 1907435 2863361 := bstep (se 2 (by rfl) ⟨1073760, by rfl⟩ : syracuseStep 2863361 = 2147521) B2147521
theorem B1908907 : Blo 1907435 1908907 := bstep (se 1 (by rfl) ⟨1431680, by rfl⟩ : syracuseStep 1908907 = 2863361) B2863361
theorem B4831933 : Blo 1907435 4831933 := bbase (se 3 (by rfl) ⟨905987, by rfl⟩ : syracuseStep 4831933 = 1811975) (by norm_num)
theorem B6442577 : Blo 1907435 6442577 := bstep (se 2 (by rfl) ⟨2415966, by rfl⟩ : syracuseStep 6442577 = 4831933) B4831933
theorem B4295051 : Blo 1907435 4295051 := bstep (se 1 (by rfl) ⟨3221288, by rfl⟩ : syracuseStep 4295051 = 6442577) B6442577
theorem B2863367 : Blo 1907435 2863367 := bstep (se 1 (by rfl) ⟨2147525, by rfl⟩ : syracuseStep 2863367 = 4295051) B4295051
theorem B1908911 : Blo 1907435 1908911 := bstep (se 1 (by rfl) ⟨1431683, by rfl⟩ : syracuseStep 1908911 = 2863367) B2863367
theorem B2863373 : Blo 1907435 2863373 := bbase (se 3 (by rfl) ⟨536882, by rfl⟩ : syracuseStep 2863373 = 1073765) (by norm_num)
theorem B1908915 : Blo 1907435 1908915 := bstep (se 1 (by rfl) ⟨1431686, by rfl⟩ : syracuseStep 1908915 = 2863373) B2863373
theorem B4295069 : Blo 1907435 4295069 := bbase (se 3 (by rfl) ⟨805325, by rfl⟩ : syracuseStep 4295069 = 1610651) (by norm_num)
theorem B2863379 : Blo 1907435 2863379 := bstep (se 1 (by rfl) ⟨2147534, by rfl⟩ : syracuseStep 2863379 = 4295069) B4295069
theorem B1908919 : Blo 1907435 1908919 := bstep (se 1 (by rfl) ⟨1431689, by rfl⟩ : syracuseStep 1908919 = 2863379) B2863379
theorem B3221309 : Blo 1907435 3221309 := bbase (se 3 (by rfl) ⟨603995, by rfl⟩ : syracuseStep 3221309 = 1207991) (by norm_num)
theorem B2147539 : Blo 1907435 2147539 := bstep (se 1 (by rfl) ⟨1610654, by rfl⟩ : syracuseStep 2147539 = 3221309) B3221309
theorem B2863385 : Blo 1907435 2863385 := bstep (se 2 (by rfl) ⟨1073769, by rfl⟩ : syracuseStep 2863385 = 2147539) B2147539
theorem B1908923 : Blo 1907435 1908923 := bstep (se 1 (by rfl) ⟨1431692, by rfl⟩ : syracuseStep 1908923 = 2863385) B2863385
theorem B2038489 : Blo 1907435 2038489 := bbase (se 2 (by rfl) ⟨764433, by rfl⟩ : syracuseStep 2038489 = 1528867) (by norm_num)
theorem B10871941 : Blo 1907435 10871941 := bstep (se 4 (by rfl) ⟨1019244, by rfl⟩ : syracuseStep 10871941 = 2038489) B2038489
theorem B14495921 : Blo 1907435 14495921 := bstep (se 2 (by rfl) ⟨5435970, by rfl⟩ : syracuseStep 14495921 = 10871941) B10871941
theorem B9663947 : Blo 1907435 9663947 := bstep (se 1 (by rfl) ⟨7247960, by rfl⟩ : syracuseStep 9663947 = 14495921) B14495921
theorem B6442631 : Blo 1907435 6442631 := bstep (se 1 (by rfl) ⟨4831973, by rfl⟩ : syracuseStep 6442631 = 9663947) B9663947
theorem B4295087 : Blo 1907435 4295087 := bstep (se 1 (by rfl) ⟨3221315, by rfl⟩ : syracuseStep 4295087 = 6442631) B6442631
theorem B2863391 : Blo 1907435 2863391 := bstep (se 1 (by rfl) ⟨2147543, by rfl⟩ : syracuseStep 2863391 = 4295087) B4295087
theorem B1908927 : Blo 1907435 1908927 := bstep (se 1 (by rfl) ⟨1431695, by rfl⟩ : syracuseStep 1908927 = 2863391) B2863391
theorem B2863397 : Blo 1907435 2863397 := bbase (se 4 (by rfl) ⟨268443, by rfl⟩ : syracuseStep 2863397 = 536887) (by norm_num)
theorem B1908931 : Blo 1907435 1908931 := bstep (se 1 (by rfl) ⟨1431698, by rfl⟩ : syracuseStep 1908931 = 2863397) B2863397
theorem B2415997 : Blo 1907435 2415997 := bbase (se 3 (by rfl) ⟨452999, by rfl⟩ : syracuseStep 2415997 = 905999) (by norm_num)
theorem B3221329 : Blo 1907435 3221329 := bstep (se 2 (by rfl) ⟨1207998, by rfl⟩ : syracuseStep 3221329 = 2415997) B2415997
theorem B4295105 : Blo 1907435 4295105 := bstep (se 2 (by rfl) ⟨1610664, by rfl⟩ : syracuseStep 4295105 = 3221329) B3221329
theorem B2863403 : Blo 1907435 2863403 := bstep (se 1 (by rfl) ⟨2147552, by rfl⟩ : syracuseStep 2863403 = 4295105) B4295105
theorem B1908935 : Blo 1907435 1908935 := bstep (se 1 (by rfl) ⟨1431701, by rfl⟩ : syracuseStep 1908935 = 2863403) B2863403
theorem B2147557 : Blo 1907435 2147557 := bbase (se 4 (by rfl) ⟨201333, by rfl⟩ : syracuseStep 2147557 = 402667) (by norm_num)
theorem B2863409 : Blo 1907435 2863409 := bstep (se 2 (by rfl) ⟨1073778, by rfl⟩ : syracuseStep 2863409 = 2147557) B2147557
theorem B1908939 : Blo 1907435 1908939 := bstep (se 1 (by rfl) ⟨1431704, by rfl⟩ : syracuseStep 1908939 = 2863409) B2863409
theorem B4077013 : Blo 1907435 4077013 := bbase (se 7 (by rfl) ⟨47777, by rfl⟩ : syracuseStep 4077013 = 95555) (by norm_num)
theorem B5436017 : Blo 1907435 5436017 := bstep (se 2 (by rfl) ⟨2038506, by rfl⟩ : syracuseStep 5436017 = 4077013) B4077013
theorem B3624011 : Blo 1907435 3624011 := bstep (se 1 (by rfl) ⟨2718008, by rfl⟩ : syracuseStep 3624011 = 5436017) B5436017
theorem B2416007 : Blo 1907435 2416007 := bstep (se 1 (by rfl) ⟨1812005, by rfl⟩ : syracuseStep 2416007 = 3624011) B3624011
theorem B6442685 : Blo 1907435 6442685 := bstep (se 3 (by rfl) ⟨1208003, by rfl⟩ : syracuseStep 6442685 = 2416007) B2416007
theorem B4295123 : Blo 1907435 4295123 := bstep (se 1 (by rfl) ⟨3221342, by rfl⟩ : syracuseStep 4295123 = 6442685) B6442685
theorem B2863415 : Blo 1907435 2863415 := bstep (se 1 (by rfl) ⟨2147561, by rfl⟩ : syracuseStep 2863415 = 4295123) B4295123
theorem B1908943 : Blo 1907435 1908943 := bstep (se 1 (by rfl) ⟨1431707, by rfl⟩ : syracuseStep 1908943 = 2863415) B2863415
theorem B2863421 : Blo 1907435 2863421 := bbase (se 3 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 2863421 = 1073783) (by norm_num)
theorem B1908947 : Blo 1907435 1908947 := bstep (se 1 (by rfl) ⟨1431710, by rfl⟩ : syracuseStep 1908947 = 2863421) B2863421
theorem B4295141 : Blo 1907435 4295141 := bbase (se 4 (by rfl) ⟨402669, by rfl⟩ : syracuseStep 4295141 = 805339) (by norm_num)
theorem B2863427 : Blo 1907435 2863427 := bstep (se 1 (by rfl) ⟨2147570, by rfl⟩ : syracuseStep 2863427 = 4295141) B4295141
theorem B1908951 : Blo 1907435 1908951 := bstep (se 1 (by rfl) ⟨1431713, by rfl⟩ : syracuseStep 1908951 = 2863427) B2863427
theorem B4832045 : Blo 1907435 4832045 := bbase (se 3 (by rfl) ⟨906008, by rfl⟩ : syracuseStep 4832045 = 1812017) (by norm_num)
theorem B3221363 : Blo 1907435 3221363 := bstep (se 1 (by rfl) ⟨2416022, by rfl⟩ : syracuseStep 3221363 = 4832045) B4832045
theorem B2147575 : Blo 1907435 2147575 := bstep (se 1 (by rfl) ⟨1610681, by rfl⟩ : syracuseStep 2147575 = 3221363) B3221363
theorem B2863433 : Blo 1907435 2863433 := bstep (se 2 (by rfl) ⟨1073787, by rfl⟩ : syracuseStep 2863433 = 2147575) B2147575
theorem B1908955 : Blo 1907435 1908955 := bstep (se 1 (by rfl) ⟨1431716, by rfl⟩ : syracuseStep 1908955 = 2863433) B2863433
theorem B6530645 : Blo 1907435 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B4353763 : Blo 1907435 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B5805017 : Blo 1907435 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B3870011 : Blo 1907435 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B2580007 : Blo 1907435 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B3440009 : Blo 1907435 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B9173357 : Blo 1907435 9173357 := bstep (se 3 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 9173357 = 3440009) B3440009
theorem B6115571 : Blo 1907435 6115571 := bstep (se 1 (by rfl) ⟨4586678, by rfl⟩ : syracuseStep 6115571 = 9173357) B9173357
theorem B4077047 : Blo 1907435 4077047 := bstep (se 1 (by rfl) ⟨3057785, by rfl⟩ : syracuseStep 4077047 = 6115571) B6115571
theorem B2718031 : Blo 1907435 2718031 := bstep (se 1 (by rfl) ⟨2038523, by rfl⟩ : syracuseStep 2718031 = 4077047) B4077047
theorem B3624041 : Blo 1907435 3624041 := bstep (se 2 (by rfl) ⟨1359015, by rfl⟩ : syracuseStep 3624041 = 2718031) B2718031
theorem B9664109 : Blo 1907435 9664109 := bstep (se 3 (by rfl) ⟨1812020, by rfl⟩ : syracuseStep 9664109 = 3624041) B3624041
theorem B6442739 : Blo 1907435 6442739 := bstep (se 1 (by rfl) ⟨4832054, by rfl⟩ : syracuseStep 6442739 = 9664109) B9664109
theorem B4295159 : Blo 1907435 4295159 := bstep (se 1 (by rfl) ⟨3221369, by rfl⟩ : syracuseStep 4295159 = 6442739) B6442739
theorem B2863439 : Blo 1907435 2863439 := bstep (se 1 (by rfl) ⟨2147579, by rfl⟩ : syracuseStep 2863439 = 4295159) B4295159
theorem B1908959 : Blo 1907435 1908959 := bstep (se 1 (by rfl) ⟨1431719, by rfl⟩ : syracuseStep 1908959 = 2863439) B2863439
theorem B2863445 : Blo 1907435 2863445 := bbase (se 10 (by rfl) ⟨4194, by rfl⟩ : syracuseStep 2863445 = 8389) (by norm_num)
theorem B1908963 : Blo 1907435 1908963 := bstep (se 1 (by rfl) ⟨1431722, by rfl⟩ : syracuseStep 1908963 = 2863445) B2863445
theorem B5436085 : Blo 1907435 5436085 := bbase (se 5 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 5436085 = 509633) (by norm_num)
theorem B7248113 : Blo 1907435 7248113 := bstep (se 2 (by rfl) ⟨2718042, by rfl⟩ : syracuseStep 7248113 = 5436085) B5436085
theorem B4832075 : Blo 1907435 4832075 := bstep (se 1 (by rfl) ⟨3624056, by rfl⟩ : syracuseStep 4832075 = 7248113) B7248113
theorem B3221383 : Blo 1907435 3221383 := bstep (se 1 (by rfl) ⟨2416037, by rfl⟩ : syracuseStep 3221383 = 4832075) B4832075
theorem B4295177 : Blo 1907435 4295177 := bstep (se 2 (by rfl) ⟨1610691, by rfl⟩ : syracuseStep 4295177 = 3221383) B3221383
theorem B2863451 : Blo 1907435 2863451 := bstep (se 1 (by rfl) ⟨2147588, by rfl⟩ : syracuseStep 2863451 = 4295177) B4295177
theorem B1908967 : Blo 1907435 1908967 := bstep (se 1 (by rfl) ⟨1431725, by rfl⟩ : syracuseStep 1908967 = 2863451) B2863451
theorem B2147593 : Blo 1907435 2147593 := bbase (se 2 (by rfl) ⟨805347, by rfl⟩ : syracuseStep 2147593 = 1610695) (by norm_num)
theorem B2863457 : Blo 1907435 2863457 := bstep (se 2 (by rfl) ⟨1073796, by rfl⟩ : syracuseStep 2863457 = 2147593) B2147593
theorem B1908971 : Blo 1907435 1908971 := bstep (se 1 (by rfl) ⟨1431728, by rfl⟩ : syracuseStep 1908971 = 2863457) B2863457
theorem B24462485 : Blo 1907435 24462485 := bbase (se 6 (by rfl) ⟨573339, by rfl⟩ : syracuseStep 24462485 = 1146679) (by norm_num)
theorem B16308323 : Blo 1907435 16308323 := bstep (se 1 (by rfl) ⟨12231242, by rfl⟩ : syracuseStep 16308323 = 24462485) B24462485
theorem B10872215 : Blo 1907435 10872215 := bstep (se 1 (by rfl) ⟨8154161, by rfl⟩ : syracuseStep 10872215 = 16308323) B16308323
theorem B7248143 : Blo 1907435 7248143 := bstep (se 1 (by rfl) ⟨5436107, by rfl⟩ : syracuseStep 7248143 = 10872215) B10872215
theorem B4832095 : Blo 1907435 4832095 := bstep (se 1 (by rfl) ⟨3624071, by rfl⟩ : syracuseStep 4832095 = 7248143) B7248143
theorem B6442793 : Blo 1907435 6442793 := bstep (se 2 (by rfl) ⟨2416047, by rfl⟩ : syracuseStep 6442793 = 4832095) B4832095
theorem B4295195 : Blo 1907435 4295195 := bstep (se 1 (by rfl) ⟨3221396, by rfl⟩ : syracuseStep 4295195 = 6442793) B6442793
theorem B2863463 : Blo 1907435 2863463 := bstep (se 1 (by rfl) ⟨2147597, by rfl⟩ : syracuseStep 2863463 = 4295195) B4295195
theorem B1908975 : Blo 1907435 1908975 := bstep (se 1 (by rfl) ⟨1431731, by rfl⟩ : syracuseStep 1908975 = 2863463) B2863463
theorem B2863469 : Blo 1907435 2863469 := bbase (se 3 (by rfl) ⟨536900, by rfl⟩ : syracuseStep 2863469 = 1073801) (by norm_num)
theorem B1908979 : Blo 1907435 1908979 := bstep (se 1 (by rfl) ⟨1431734, by rfl⟩ : syracuseStep 1908979 = 2863469) B2863469
theorem B4295213 : Blo 1907435 4295213 := bbase (se 3 (by rfl) ⟨805352, by rfl⟩ : syracuseStep 4295213 = 1610705) (by norm_num)
theorem B2863475 : Blo 1907435 2863475 := bstep (se 1 (by rfl) ⟨2147606, by rfl⟩ : syracuseStep 2863475 = 4295213) B4295213
theorem B1908983 : Blo 1907435 1908983 := bstep (se 1 (by rfl) ⟨1431737, by rfl⟩ : syracuseStep 1908983 = 2863475) B2863475
theorem B3723661 : Blo 1907435 3723661 := bbase (se 3 (by rfl) ⟨698186, by rfl⟩ : syracuseStep 3723661 = 1396373) (by norm_num)
theorem B19859525 : Blo 1907435 19859525 := bstep (se 4 (by rfl) ⟨1861830, by rfl⟩ : syracuseStep 19859525 = 3723661) B3723661
theorem B13239683 : Blo 1907435 13239683 := bstep (se 1 (by rfl) ⟨9929762, by rfl⟩ : syracuseStep 13239683 = 19859525) B19859525
theorem B8826455 : Blo 1907435 8826455 := bstep (se 1 (by rfl) ⟨6619841, by rfl⟩ : syracuseStep 8826455 = 13239683) B13239683
theorem B23537213 : Blo 1907435 23537213 := bstep (se 3 (by rfl) ⟨4413227, by rfl⟩ : syracuseStep 23537213 = 8826455) B8826455
theorem B15691475 : Blo 1907435 15691475 := bstep (se 1 (by rfl) ⟨11768606, by rfl⟩ : syracuseStep 15691475 = 23537213) B23537213
theorem B10460983 : Blo 1907435 10460983 := bstep (se 1 (by rfl) ⟨7845737, by rfl⟩ : syracuseStep 10460983 = 15691475) B15691475
theorem B13947977 : Blo 1907435 13947977 := bstep (se 2 (by rfl) ⟨5230491, by rfl⟩ : syracuseStep 13947977 = 10460983) B10460983
theorem B9298651 : Blo 1907435 9298651 := bstep (se 1 (by rfl) ⟨6973988, by rfl⟩ : syracuseStep 9298651 = 13947977) B13947977
theorem B12398201 : Blo 1907435 12398201 := bstep (se 2 (by rfl) ⟨4649325, by rfl⟩ : syracuseStep 12398201 = 9298651) B9298651
theorem B8265467 : Blo 1907435 8265467 := bstep (se 1 (by rfl) ⟨6199100, by rfl⟩ : syracuseStep 8265467 = 12398201) B12398201
theorem B5510311 : Blo 1907435 5510311 := bstep (se 1 (by rfl) ⟨4132733, by rfl⟩ : syracuseStep 5510311 = 8265467) B8265467
theorem B117553301 : Blo 1907435 117553301 := bstep (se 6 (by rfl) ⟨2755155, by rfl⟩ : syracuseStep 117553301 = 5510311) B5510311
theorem B78368867 : Blo 1907435 78368867 := bstep (se 1 (by rfl) ⟨58776650, by rfl⟩ : syracuseStep 78368867 = 117553301) B117553301
theorem B52245911 : Blo 1907435 52245911 := bstep (se 1 (by rfl) ⟨39184433, by rfl⟩ : syracuseStep 52245911 = 78368867) B78368867
theorem B34830607 : Blo 1907435 34830607 := bstep (se 1 (by rfl) ⟨26122955, by rfl⟩ : syracuseStep 34830607 = 52245911) B52245911
theorem B46440809 : Blo 1907435 46440809 := bstep (se 2 (by rfl) ⟨17415303, by rfl⟩ : syracuseStep 46440809 = 34830607) B34830607
theorem B30960539 : Blo 1907435 30960539 := bstep (se 1 (by rfl) ⟨23220404, by rfl⟩ : syracuseStep 30960539 = 46440809) B46440809
theorem B20640359 : Blo 1907435 20640359 := bstep (se 1 (by rfl) ⟨15480269, by rfl⟩ : syracuseStep 20640359 = 30960539) B30960539
theorem B13760239 : Blo 1907435 13760239 := bstep (se 1 (by rfl) ⟨10320179, by rfl⟩ : syracuseStep 13760239 = 20640359) B20640359
theorem B18346985 : Blo 1907435 18346985 := bstep (se 2 (by rfl) ⟨6880119, by rfl⟩ : syracuseStep 18346985 = 13760239) B13760239
theorem B12231323 : Blo 1907435 12231323 := bstep (se 1 (by rfl) ⟨9173492, by rfl⟩ : syracuseStep 12231323 = 18346985) B18346985
theorem B8154215 : Blo 1907435 8154215 := bstep (se 1 (by rfl) ⟨6115661, by rfl⟩ : syracuseStep 8154215 = 12231323) B12231323
theorem B5436143 : Blo 1907435 5436143 := bstep (se 1 (by rfl) ⟨4077107, by rfl⟩ : syracuseStep 5436143 = 8154215) B8154215
theorem B3624095 : Blo 1907435 3624095 := bstep (se 1 (by rfl) ⟨2718071, by rfl⟩ : syracuseStep 3624095 = 5436143) B5436143
theorem B2416063 : Blo 1907435 2416063 := bstep (se 1 (by rfl) ⟨1812047, by rfl⟩ : syracuseStep 2416063 = 3624095) B3624095
theorem B3221417 : Blo 1907435 3221417 := bstep (se 2 (by rfl) ⟨1208031, by rfl⟩ : syracuseStep 3221417 = 2416063) B2416063
theorem B2147611 : Blo 1907435 2147611 := bstep (se 1 (by rfl) ⟨1610708, by rfl⟩ : syracuseStep 2147611 = 3221417) B3221417
theorem B2863481 : Blo 1907435 2863481 := bstep (se 2 (by rfl) ⟨1073805, by rfl⟩ : syracuseStep 2863481 = 2147611) B2147611
theorem B1908987 : Blo 1907435 1908987 := bstep (se 1 (by rfl) ⟨1431740, by rfl⟩ : syracuseStep 1908987 = 2863481) B2863481
theorem B32616917 : Blo 1907435 32616917 := bbase (se 7 (by rfl) ⟨382229, by rfl⟩ : syracuseStep 32616917 = 764459) (by norm_num)
theorem B21744611 : Blo 1907435 21744611 := bstep (se 1 (by rfl) ⟨16308458, by rfl⟩ : syracuseStep 21744611 = 32616917) B32616917
theorem B14496407 : Blo 1907435 14496407 := bstep (se 1 (by rfl) ⟨10872305, by rfl⟩ : syracuseStep 14496407 = 21744611) B21744611
theorem B9664271 : Blo 1907435 9664271 := bstep (se 1 (by rfl) ⟨7248203, by rfl⟩ : syracuseStep 9664271 = 14496407) B14496407
theorem B6442847 : Blo 1907435 6442847 := bstep (se 1 (by rfl) ⟨4832135, by rfl⟩ : syracuseStep 6442847 = 9664271) B9664271
theorem B4295231 : Blo 1907435 4295231 := bstep (se 1 (by rfl) ⟨3221423, by rfl⟩ : syracuseStep 4295231 = 6442847) B6442847
theorem B2863487 : Blo 1907435 2863487 := bstep (se 1 (by rfl) ⟨2147615, by rfl⟩ : syracuseStep 2863487 = 4295231) B4295231
theorem B1908991 : Blo 1907435 1908991 := bstep (se 1 (by rfl) ⟨1431743, by rfl⟩ : syracuseStep 1908991 = 2863487) B2863487
theorem B2863493 : Blo 1907435 2863493 := bbase (se 4 (by rfl) ⟨268452, by rfl⟩ : syracuseStep 2863493 = 536905) (by norm_num)
theorem B1908995 : Blo 1907435 1908995 := bstep (se 1 (by rfl) ⟨1431746, by rfl⟩ : syracuseStep 1908995 = 2863493) B2863493
theorem B3221437 : Blo 1907435 3221437 := bbase (se 3 (by rfl) ⟨604019, by rfl⟩ : syracuseStep 3221437 = 1208039) (by norm_num)
theorem B4295249 : Blo 1907435 4295249 := bstep (se 2 (by rfl) ⟨1610718, by rfl⟩ : syracuseStep 4295249 = 3221437) B3221437
theorem B2863499 : Blo 1907435 2863499 := bstep (se 1 (by rfl) ⟨2147624, by rfl⟩ : syracuseStep 2863499 = 4295249) B4295249
theorem B1908999 : Blo 1907435 1908999 := bstep (se 1 (by rfl) ⟨1431749, by rfl⟩ : syracuseStep 1908999 = 2863499) B2863499
theorem B2147629 : Blo 1907435 2147629 := bbase (se 3 (by rfl) ⟨402680, by rfl⟩ : syracuseStep 2147629 = 805361) (by norm_num)
theorem B2863505 : Blo 1907435 2863505 := bstep (se 2 (by rfl) ⟨1073814, by rfl⟩ : syracuseStep 2863505 = 2147629) B2147629
theorem B1909003 : Blo 1907435 1909003 := bstep (se 1 (by rfl) ⟨1431752, by rfl⟩ : syracuseStep 1909003 = 2863505) B2863505
theorem B6442901 : Blo 1907435 6442901 := bbase (se 6 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 6442901 = 302011) (by norm_num)
theorem B4295267 : Blo 1907435 4295267 := bstep (se 1 (by rfl) ⟨3221450, by rfl⟩ : syracuseStep 4295267 = 6442901) B6442901
theorem B2863511 : Blo 1907435 2863511 := bstep (se 1 (by rfl) ⟨2147633, by rfl⟩ : syracuseStep 2863511 = 4295267) B4295267
theorem B1909007 : Blo 1907435 1909007 := bstep (se 1 (by rfl) ⟨1431755, by rfl⟩ : syracuseStep 1909007 = 2863511) B2863511
theorem B2863517 : Blo 1907435 2863517 := bbase (se 3 (by rfl) ⟨536909, by rfl⟩ : syracuseStep 2863517 = 1073819) (by norm_num)
theorem B1909011 : Blo 1907435 1909011 := bstep (se 1 (by rfl) ⟨1431758, by rfl⟩ : syracuseStep 1909011 = 2863517) B2863517
theorem B4295285 : Blo 1907435 4295285 := bbase (se 5 (by rfl) ⟨201341, by rfl⟩ : syracuseStep 4295285 = 402683) (by norm_num)
theorem B2863523 : Blo 1907435 2863523 := bstep (se 1 (by rfl) ⟨2147642, by rfl⟩ : syracuseStep 2863523 = 4295285) B4295285
theorem B1909015 : Blo 1907435 1909015 := bstep (se 1 (by rfl) ⟨1431761, by rfl⟩ : syracuseStep 1909015 = 2863523) B2863523
theorem B3440117 : Blo 1907435 3440117 := bbase (se 5 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 3440117 = 322511) (by norm_num)
theorem B9173645 : Blo 1907435 9173645 := bstep (se 3 (by rfl) ⟨1720058, by rfl⟩ : syracuseStep 9173645 = 3440117) B3440117
theorem B6115763 : Blo 1907435 6115763 := bstep (se 1 (by rfl) ⟨4586822, by rfl⟩ : syracuseStep 6115763 = 9173645) B9173645
theorem B16308701 : Blo 1907435 16308701 := bstep (se 3 (by rfl) ⟨3057881, by rfl⟩ : syracuseStep 16308701 = 6115763) B6115763
theorem B10872467 : Blo 1907435 10872467 := bstep (se 1 (by rfl) ⟨8154350, by rfl⟩ : syracuseStep 10872467 = 16308701) B16308701
theorem B7248311 : Blo 1907435 7248311 := bstep (se 1 (by rfl) ⟨5436233, by rfl⟩ : syracuseStep 7248311 = 10872467) B10872467
theorem B4832207 : Blo 1907435 4832207 := bstep (se 1 (by rfl) ⟨3624155, by rfl⟩ : syracuseStep 4832207 = 7248311) B7248311
theorem B3221471 : Blo 1907435 3221471 := bstep (se 1 (by rfl) ⟨2416103, by rfl⟩ : syracuseStep 3221471 = 4832207) B4832207
theorem B2147647 : Blo 1907435 2147647 := bstep (se 1 (by rfl) ⟨1610735, by rfl⟩ : syracuseStep 2147647 = 3221471) B3221471
theorem B2863529 : Blo 1907435 2863529 := bstep (se 2 (by rfl) ⟨1073823, by rfl⟩ : syracuseStep 2863529 = 2147647) B2147647
theorem B1909019 : Blo 1907435 1909019 := bstep (se 1 (by rfl) ⟨1431764, by rfl⟩ : syracuseStep 1909019 = 2863529) B2863529
theorem B7248325 : Blo 1907435 7248325 := bbase (se 4 (by rfl) ⟨679530, by rfl⟩ : syracuseStep 7248325 = 1359061) (by norm_num)
theorem B9664433 : Blo 1907435 9664433 := bstep (se 2 (by rfl) ⟨3624162, by rfl⟩ : syracuseStep 9664433 = 7248325) B7248325
theorem B6442955 : Blo 1907435 6442955 := bstep (se 1 (by rfl) ⟨4832216, by rfl⟩ : syracuseStep 6442955 = 9664433) B9664433
theorem B4295303 : Blo 1907435 4295303 := bstep (se 1 (by rfl) ⟨3221477, by rfl⟩ : syracuseStep 4295303 = 6442955) B6442955
theorem B2863535 : Blo 1907435 2863535 := bstep (se 1 (by rfl) ⟨2147651, by rfl⟩ : syracuseStep 2863535 = 4295303) B4295303
theorem B1909023 : Blo 1907435 1909023 := bstep (se 1 (by rfl) ⟨1431767, by rfl⟩ : syracuseStep 1909023 = 2863535) B2863535
theorem B2863541 : Blo 1907435 2863541 := bbase (se 5 (by rfl) ⟨134228, by rfl⟩ : syracuseStep 2863541 = 268457) (by norm_num)
theorem B1909027 : Blo 1907435 1909027 := bstep (se 1 (by rfl) ⟨1431770, by rfl⟩ : syracuseStep 1909027 = 2863541) B2863541
theorem B4832237 : Blo 1907435 4832237 := bbase (se 3 (by rfl) ⟨906044, by rfl⟩ : syracuseStep 4832237 = 1812089) (by norm_num)
theorem B3221491 : Blo 1907435 3221491 := bstep (se 1 (by rfl) ⟨2416118, by rfl⟩ : syracuseStep 3221491 = 4832237) B4832237
theorem B4295321 : Blo 1907435 4295321 := bstep (se 2 (by rfl) ⟨1610745, by rfl⟩ : syracuseStep 4295321 = 3221491) B3221491
theorem B2863547 : Blo 1907435 2863547 := bstep (se 1 (by rfl) ⟨2147660, by rfl⟩ : syracuseStep 2863547 = 4295321) B4295321
theorem B1909031 : Blo 1907435 1909031 := bstep (se 1 (by rfl) ⟨1431773, by rfl⟩ : syracuseStep 1909031 = 2863547) B2863547
theorem B2147665 : Blo 1907435 2147665 := bbase (se 2 (by rfl) ⟨805374, by rfl⟩ : syracuseStep 2147665 = 1610749) (by norm_num)
theorem B2863553 : Blo 1907435 2863553 := bstep (se 2 (by rfl) ⟨1073832, by rfl⟩ : syracuseStep 2863553 = 2147665) B2147665
theorem B1909035 : Blo 1907435 1909035 := bstep (se 1 (by rfl) ⟨1431776, by rfl⟩ : syracuseStep 1909035 = 2863553) B2863553
theorem B2038609 : Blo 1907435 2038609 := bbase (se 2 (by rfl) ⟨764478, by rfl⟩ : syracuseStep 2038609 = 1528957) (by norm_num)
theorem B2718145 : Blo 1907435 2718145 := bstep (se 2 (by rfl) ⟨1019304, by rfl⟩ : syracuseStep 2718145 = 2038609) B2038609
theorem B3624193 : Blo 1907435 3624193 := bstep (se 2 (by rfl) ⟨1359072, by rfl⟩ : syracuseStep 3624193 = 2718145) B2718145
theorem B4832257 : Blo 1907435 4832257 := bstep (se 2 (by rfl) ⟨1812096, by rfl⟩ : syracuseStep 4832257 = 3624193) B3624193
theorem B6443009 : Blo 1907435 6443009 := bstep (se 2 (by rfl) ⟨2416128, by rfl⟩ : syracuseStep 6443009 = 4832257) B4832257
theorem B4295339 : Blo 1907435 4295339 := bstep (se 1 (by rfl) ⟨3221504, by rfl⟩ : syracuseStep 4295339 = 6443009) B6443009
theorem B2863559 : Blo 1907435 2863559 := bstep (se 1 (by rfl) ⟨2147669, by rfl⟩ : syracuseStep 2863559 = 4295339) B4295339
theorem B1909039 : Blo 1907435 1909039 := bstep (se 1 (by rfl) ⟨1431779, by rfl⟩ : syracuseStep 1909039 = 2863559) B2863559
theorem B2863565 : Blo 1907435 2863565 := bbase (se 3 (by rfl) ⟨536918, by rfl⟩ : syracuseStep 2863565 = 1073837) (by norm_num)
theorem B1909043 : Blo 1907435 1909043 := bstep (se 1 (by rfl) ⟨1431782, by rfl⟩ : syracuseStep 1909043 = 2863565) B2863565
theorem B4295357 : Blo 1907435 4295357 := bbase (se 3 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 4295357 = 1610759) (by norm_num)
theorem B2863571 : Blo 1907435 2863571 := bstep (se 1 (by rfl) ⟨2147678, by rfl⟩ : syracuseStep 2863571 = 4295357) B4295357
theorem B1909047 : Blo 1907435 1909047 := bstep (se 1 (by rfl) ⟨1431785, by rfl⟩ : syracuseStep 1909047 = 2863571) B2863571
theorem B3221525 : Blo 1907435 3221525 := bbase (se 6 (by rfl) ⟨75504, by rfl⟩ : syracuseStep 3221525 = 151009) (by norm_num)
theorem B2147683 : Blo 1907435 2147683 := bstep (se 1 (by rfl) ⟨1610762, by rfl⟩ : syracuseStep 2147683 = 3221525) B3221525
theorem B2863577 : Blo 1907435 2863577 := bstep (se 2 (by rfl) ⟨1073841, by rfl⟩ : syracuseStep 2863577 = 2147683) B2147683
theorem B1909051 : Blo 1907435 1909051 := bstep (se 1 (by rfl) ⟨1431788, by rfl⟩ : syracuseStep 1909051 = 2863577) B2863577
theorem B13760725 : Blo 1907435 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B18347633 : Blo 1907435 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B12231755 : Blo 1907435 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B8154503 : Blo 1907435 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B5436335 : Blo 1907435 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B14496893 : Blo 1907435 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B9664595 : Blo 1907435 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B6443063 : Blo 1907435 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B4295375 : Blo 1907435 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B2863583 : Blo 1907435 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B1909055 : Blo 1907435 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B2863589 : Blo 1907435 2863589 := bbase (se 4 (by rfl) ⟨268461, by rfl⟩ : syracuseStep 2863589 = 536923) (by norm_num)
theorem B1909059 : Blo 1907435 1909059 := bstep (se 1 (by rfl) ⟨1431794, by rfl⟩ : syracuseStep 1909059 = 2863589) B2863589
theorem B3141965 : Blo 1907435 3141965 := bbase (se 3 (by rfl) ⟨589118, by rfl⟩ : syracuseStep 3141965 = 1178237) (by norm_num)
theorem B2094643 : Blo 1907435 2094643 := bstep (se 1 (by rfl) ⟨1570982, by rfl⟩ : syracuseStep 2094643 = 3141965) B3141965
theorem B2792857 : Blo 1907435 2792857 := bstep (se 2 (by rfl) ⟨1047321, by rfl⟩ : syracuseStep 2792857 = 2094643) B2094643
theorem B3723809 : Blo 1907435 3723809 := bstep (se 2 (by rfl) ⟨1396428, by rfl⟩ : syracuseStep 3723809 = 2792857) B2792857
theorem B9930157 : Blo 1907435 9930157 := bstep (se 3 (by rfl) ⟨1861904, by rfl⟩ : syracuseStep 9930157 = 3723809) B3723809
theorem B52960837 : Blo 1907435 52960837 := bstep (se 4 (by rfl) ⟨4965078, by rfl⟩ : syracuseStep 52960837 = 9930157) B9930157
theorem B70614449 : Blo 1907435 70614449 := bstep (se 2 (by rfl) ⟨26480418, by rfl⟩ : syracuseStep 70614449 = 52960837) B52960837
theorem B47076299 : Blo 1907435 47076299 := bstep (se 1 (by rfl) ⟨35307224, by rfl⟩ : syracuseStep 47076299 = 70614449) B70614449
theorem B31384199 : Blo 1907435 31384199 := bstep (se 1 (by rfl) ⟨23538149, by rfl⟩ : syracuseStep 31384199 = 47076299) B47076299
theorem B20922799 : Blo 1907435 20922799 := bstep (se 1 (by rfl) ⟨15692099, by rfl⟩ : syracuseStep 20922799 = 31384199) B31384199
theorem B27897065 : Blo 1907435 27897065 := bstep (se 2 (by rfl) ⟨10461399, by rfl⟩ : syracuseStep 27897065 = 20922799) B20922799
theorem B18598043 : Blo 1907435 18598043 := bstep (se 1 (by rfl) ⟨13948532, by rfl⟩ : syracuseStep 18598043 = 27897065) B27897065
theorem B49594781 : Blo 1907435 49594781 := bstep (se 3 (by rfl) ⟨9299021, by rfl⟩ : syracuseStep 49594781 = 18598043) B18598043
theorem B33063187 : Blo 1907435 33063187 := bstep (se 1 (by rfl) ⟨24797390, by rfl⟩ : syracuseStep 33063187 = 49594781) B49594781
theorem B44084249 : Blo 1907435 44084249 := bstep (se 2 (by rfl) ⟨16531593, by rfl⟩ : syracuseStep 44084249 = 33063187) B33063187
theorem B29389499 : Blo 1907435 29389499 := bstep (se 1 (by rfl) ⟨22042124, by rfl⟩ : syracuseStep 29389499 = 44084249) B44084249
theorem B19592999 : Blo 1907435 19592999 := bstep (se 1 (by rfl) ⟨14694749, by rfl⟩ : syracuseStep 19592999 = 29389499) B29389499
theorem B13061999 : Blo 1907435 13061999 := bstep (se 1 (by rfl) ⟨9796499, by rfl⟩ : syracuseStep 13061999 = 19592999) B19592999
theorem B8707999 : Blo 1907435 8707999 := bstep (se 1 (by rfl) ⟨6530999, by rfl⟩ : syracuseStep 8707999 = 13061999) B13061999
theorem B11610665 : Blo 1907435 11610665 := bstep (se 2 (by rfl) ⟨4353999, by rfl⟩ : syracuseStep 11610665 = 8707999) B8707999
theorem B7740443 : Blo 1907435 7740443 := bstep (se 1 (by rfl) ⟨5805332, by rfl⟩ : syracuseStep 7740443 = 11610665) B11610665
theorem B5160295 : Blo 1907435 5160295 := bstep (se 1 (by rfl) ⟨3870221, by rfl⟩ : syracuseStep 5160295 = 7740443) B7740443
theorem B6880393 : Blo 1907435 6880393 := bstep (se 2 (by rfl) ⟨2580147, by rfl⟩ : syracuseStep 6880393 = 5160295) B5160295
theorem B9173857 : Blo 1907435 9173857 := bstep (se 2 (by rfl) ⟨3440196, by rfl⟩ : syracuseStep 9173857 = 6880393) B6880393
theorem B12231809 : Blo 1907435 12231809 := bstep (se 2 (by rfl) ⟨4586928, by rfl⟩ : syracuseStep 12231809 = 9173857) B9173857
theorem B8154539 : Blo 1907435 8154539 := bstep (se 1 (by rfl) ⟨6115904, by rfl⟩ : syracuseStep 8154539 = 12231809) B12231809
theorem B5436359 : Blo 1907435 5436359 := bstep (se 1 (by rfl) ⟨4077269, by rfl⟩ : syracuseStep 5436359 = 8154539) B8154539
theorem B3624239 : Blo 1907435 3624239 := bstep (se 1 (by rfl) ⟨2718179, by rfl⟩ : syracuseStep 3624239 = 5436359) B5436359
theorem B2416159 : Blo 1907435 2416159 := bstep (se 1 (by rfl) ⟨1812119, by rfl⟩ : syracuseStep 2416159 = 3624239) B3624239
theorem B3221545 : Blo 1907435 3221545 := bstep (se 2 (by rfl) ⟨1208079, by rfl⟩ : syracuseStep 3221545 = 2416159) B2416159
theorem B4295393 : Blo 1907435 4295393 := bstep (se 2 (by rfl) ⟨1610772, by rfl⟩ : syracuseStep 4295393 = 3221545) B3221545
theorem B2863595 : Blo 1907435 2863595 := bstep (se 1 (by rfl) ⟨2147696, by rfl⟩ : syracuseStep 2863595 = 4295393) B4295393
theorem B1909063 : Blo 1907435 1909063 := bstep (se 1 (by rfl) ⟨1431797, by rfl⟩ : syracuseStep 1909063 = 2863595) B2863595
theorem B2147701 : Blo 1907435 2147701 := bbase (se 5 (by rfl) ⟨100673, by rfl⟩ : syracuseStep 2147701 = 201347) (by norm_num)
theorem B2863601 : Blo 1907435 2863601 := bstep (se 2 (by rfl) ⟨1073850, by rfl⟩ : syracuseStep 2863601 = 2147701) B2147701
theorem B1909067 : Blo 1907435 1909067 := bstep (se 1 (by rfl) ⟨1431800, by rfl⟩ : syracuseStep 1909067 = 2863601) B2863601
theorem B2416169 : Blo 1907435 2416169 := bbase (se 2 (by rfl) ⟨906063, by rfl⟩ : syracuseStep 2416169 = 1812127) (by norm_num)
theorem B6443117 : Blo 1907435 6443117 := bstep (se 3 (by rfl) ⟨1208084, by rfl⟩ : syracuseStep 6443117 = 2416169) B2416169
theorem B4295411 : Blo 1907435 4295411 := bstep (se 1 (by rfl) ⟨3221558, by rfl⟩ : syracuseStep 4295411 = 6443117) B6443117
theorem B2863607 : Blo 1907435 2863607 := bstep (se 1 (by rfl) ⟨2147705, by rfl⟩ : syracuseStep 2863607 = 4295411) B4295411
theorem B1909071 : Blo 1907435 1909071 := bstep (se 1 (by rfl) ⟨1431803, by rfl⟩ : syracuseStep 1909071 = 2863607) B2863607
theorem B2863613 : Blo 1907435 2863613 := bbase (se 3 (by rfl) ⟨536927, by rfl⟩ : syracuseStep 2863613 = 1073855) (by norm_num)
theorem B1909075 : Blo 1907435 1909075 := bstep (se 1 (by rfl) ⟨1431806, by rfl⟩ : syracuseStep 1909075 = 2863613) B2863613
theorem B4295429 : Blo 1907435 4295429 := bbase (se 4 (by rfl) ⟨402696, by rfl⟩ : syracuseStep 4295429 = 805393) (by norm_num)
theorem B2863619 : Blo 1907435 2863619 := bstep (se 1 (by rfl) ⟨2147714, by rfl⟩ : syracuseStep 2863619 = 4295429) B4295429
theorem B1909079 : Blo 1907435 1909079 := bstep (se 1 (by rfl) ⟨1431809, by rfl⟩ : syracuseStep 1909079 = 2863619) B2863619
theorem B3624277 : Blo 1907435 3624277 := bbase (se 11 (by rfl) ⟨2654, by rfl⟩ : syracuseStep 3624277 = 5309) (by norm_num)
theorem B4832369 : Blo 1907435 4832369 := bstep (se 2 (by rfl) ⟨1812138, by rfl⟩ : syracuseStep 4832369 = 3624277) B3624277
theorem B3221579 : Blo 1907435 3221579 := bstep (se 1 (by rfl) ⟨2416184, by rfl⟩ : syracuseStep 3221579 = 4832369) B4832369
theorem B2147719 : Blo 1907435 2147719 := bstep (se 1 (by rfl) ⟨1610789, by rfl⟩ : syracuseStep 2147719 = 3221579) B3221579
theorem B2863625 : Blo 1907435 2863625 := bstep (se 2 (by rfl) ⟨1073859, by rfl⟩ : syracuseStep 2863625 = 2147719) B2147719
theorem B1909083 : Blo 1907435 1909083 := bstep (se 1 (by rfl) ⟨1431812, by rfl⟩ : syracuseStep 1909083 = 2863625) B2863625
theorem B9664757 : Blo 1907435 9664757 := bbase (se 5 (by rfl) ⟨453035, by rfl⟩ : syracuseStep 9664757 = 906071) (by norm_num)
theorem B6443171 : Blo 1907435 6443171 := bstep (se 1 (by rfl) ⟨4832378, by rfl⟩ : syracuseStep 6443171 = 9664757) B9664757
theorem B4295447 : Blo 1907435 4295447 := bstep (se 1 (by rfl) ⟨3221585, by rfl⟩ : syracuseStep 4295447 = 6443171) B6443171
theorem B2863631 : Blo 1907435 2863631 := bstep (se 1 (by rfl) ⟨2147723, by rfl⟩ : syracuseStep 2863631 = 4295447) B4295447
theorem B1909087 : Blo 1907435 1909087 := bstep (se 1 (by rfl) ⟨1431815, by rfl⟩ : syracuseStep 1909087 = 2863631) B2863631
theorem B2863637 : Blo 1907435 2863637 := bbase (se 6 (by rfl) ⟨67116, by rfl⟩ : syracuseStep 2863637 = 134233) (by norm_num)
theorem B1909091 : Blo 1907435 1909091 := bstep (se 1 (by rfl) ⟨1431818, by rfl⟩ : syracuseStep 1909091 = 2863637) B2863637
theorem B4587005 : Blo 1907435 4587005 := bbase (se 3 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 4587005 = 1720127) (by norm_num)
theorem B3058003 : Blo 1907435 3058003 := bstep (se 1 (by rfl) ⟨2293502, by rfl⟩ : syracuseStep 3058003 = 4587005) B4587005
theorem B16309349 : Blo 1907435 16309349 := bstep (se 4 (by rfl) ⟨1529001, by rfl⟩ : syracuseStep 16309349 = 3058003) B3058003
theorem B10872899 : Blo 1907435 10872899 := bstep (se 1 (by rfl) ⟨8154674, by rfl⟩ : syracuseStep 10872899 = 16309349) B16309349
theorem B7248599 : Blo 1907435 7248599 := bstep (se 1 (by rfl) ⟨5436449, by rfl⟩ : syracuseStep 7248599 = 10872899) B10872899
theorem B4832399 : Blo 1907435 4832399 := bstep (se 1 (by rfl) ⟨3624299, by rfl⟩ : syracuseStep 4832399 = 7248599) B7248599
theorem B3221599 : Blo 1907435 3221599 := bstep (se 1 (by rfl) ⟨2416199, by rfl⟩ : syracuseStep 3221599 = 4832399) B4832399
theorem B4295465 : Blo 1907435 4295465 := bstep (se 2 (by rfl) ⟨1610799, by rfl⟩ : syracuseStep 4295465 = 3221599) B3221599
theorem B2863643 : Blo 1907435 2863643 := bstep (se 1 (by rfl) ⟨2147732, by rfl⟩ : syracuseStep 2863643 = 4295465) B4295465
theorem B1909095 : Blo 1907435 1909095 := bstep (se 1 (by rfl) ⟨1431821, by rfl⟩ : syracuseStep 1909095 = 2863643) B2863643
theorem B2147737 : Blo 1907435 2147737 := bbase (se 2 (by rfl) ⟨805401, by rfl⟩ : syracuseStep 2147737 = 1610803) (by norm_num)
theorem B2863649 : Blo 1907435 2863649 := bstep (se 2 (by rfl) ⟨1073868, by rfl⟩ : syracuseStep 2863649 = 2147737) B2147737
theorem B1909099 : Blo 1907435 1909099 := bstep (se 1 (by rfl) ⟨1431824, by rfl⟩ : syracuseStep 1909099 = 2863649) B2863649
theorem B7248629 : Blo 1907435 7248629 := bbase (se 5 (by rfl) ⟨339779, by rfl⟩ : syracuseStep 7248629 = 679559) (by norm_num)
theorem B4832419 : Blo 1907435 4832419 := bstep (se 1 (by rfl) ⟨3624314, by rfl⟩ : syracuseStep 4832419 = 7248629) B7248629
theorem B6443225 : Blo 1907435 6443225 := bstep (se 2 (by rfl) ⟨2416209, by rfl⟩ : syracuseStep 6443225 = 4832419) B4832419
theorem B4295483 : Blo 1907435 4295483 := bstep (se 1 (by rfl) ⟨3221612, by rfl⟩ : syracuseStep 4295483 = 6443225) B6443225
theorem B2863655 : Blo 1907435 2863655 := bstep (se 1 (by rfl) ⟨2147741, by rfl⟩ : syracuseStep 2863655 = 4295483) B4295483
theorem B1909103 : Blo 1907435 1909103 := bstep (se 1 (by rfl) ⟨1431827, by rfl⟩ : syracuseStep 1909103 = 2863655) B2863655
theorem B2863661 : Blo 1907435 2863661 := bbase (se 3 (by rfl) ⟨536936, by rfl⟩ : syracuseStep 2863661 = 1073873) (by norm_num)
theorem B1909107 : Blo 1907435 1909107 := bstep (se 1 (by rfl) ⟨1431830, by rfl⟩ : syracuseStep 1909107 = 2863661) B2863661
theorem B4295501 : Blo 1907435 4295501 := bbase (se 3 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 4295501 = 1610813) (by norm_num)
theorem B2863667 : Blo 1907435 2863667 := bstep (se 1 (by rfl) ⟨2147750, by rfl⟩ : syracuseStep 2863667 = 4295501) B4295501
theorem B1909111 : Blo 1907435 1909111 := bstep (se 1 (by rfl) ⟨1431833, by rfl⟩ : syracuseStep 1909111 = 2863667) B2863667
theorem B2416225 : Blo 1907435 2416225 := bbase (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) (by norm_num)
theorem B3221633 : Blo 1907435 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B2147755 : Blo 1907435 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B2863673 : Blo 1907435 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B1909115 : Blo 1907435 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B21746069 : Blo 1907435 21746069 := bbase (se 6 (by rfl) ⟨509673, by rfl⟩ : syracuseStep 21746069 = 1019347) (by norm_num)
theorem B14497379 : Blo 1907435 14497379 := bstep (se 1 (by rfl) ⟨10873034, by rfl⟩ : syracuseStep 14497379 = 21746069) B21746069
theorem B9664919 : Blo 1907435 9664919 := bstep (se 1 (by rfl) ⟨7248689, by rfl⟩ : syracuseStep 9664919 = 14497379) B14497379
theorem B6443279 : Blo 1907435 6443279 := bstep (se 1 (by rfl) ⟨4832459, by rfl⟩ : syracuseStep 6443279 = 9664919) B9664919
theorem B4295519 : Blo 1907435 4295519 := bstep (se 1 (by rfl) ⟨3221639, by rfl⟩ : syracuseStep 4295519 = 6443279) B6443279
theorem B2863679 : Blo 1907435 2863679 := bstep (se 1 (by rfl) ⟨2147759, by rfl⟩ : syracuseStep 2863679 = 4295519) B4295519
theorem B1909119 : Blo 1907435 1909119 := bstep (se 1 (by rfl) ⟨1431839, by rfl⟩ : syracuseStep 1909119 = 2863679) B2863679
theorem B2863685 : Blo 1907435 2863685 := bbase (se 4 (by rfl) ⟨268470, by rfl⟩ : syracuseStep 2863685 = 536941) (by norm_num)
theorem B1909123 : Blo 1907435 1909123 := bstep (se 1 (by rfl) ⟨1431842, by rfl⟩ : syracuseStep 1909123 = 2863685) B2863685
theorem B3221653 : Blo 1907435 3221653 := bbase (se 6 (by rfl) ⟨75507, by rfl⟩ : syracuseStep 3221653 = 151015) (by norm_num)
theorem B4295537 : Blo 1907435 4295537 := bstep (se 2 (by rfl) ⟨1610826, by rfl⟩ : syracuseStep 4295537 = 3221653) B3221653
theorem B2863691 : Blo 1907435 2863691 := bstep (se 1 (by rfl) ⟨2147768, by rfl⟩ : syracuseStep 2863691 = 4295537) B4295537
theorem B1909127 : Blo 1907435 1909127 := bstep (se 1 (by rfl) ⟨1431845, by rfl⟩ : syracuseStep 1909127 = 2863691) B2863691
theorem B2147773 : Blo 1907435 2147773 := bbase (se 3 (by rfl) ⟨402707, by rfl⟩ : syracuseStep 2147773 = 805415) (by norm_num)
theorem B2863697 : Blo 1907435 2863697 := bstep (se 2 (by rfl) ⟨1073886, by rfl⟩ : syracuseStep 2863697 = 2147773) B2147773
theorem B1909131 : Blo 1907435 1909131 := bstep (se 1 (by rfl) ⟨1431848, by rfl⟩ : syracuseStep 1909131 = 2863697) B2863697
theorem B6443333 : Blo 1907435 6443333 := bbase (se 4 (by rfl) ⟨604062, by rfl⟩ : syracuseStep 6443333 = 1208125) (by norm_num)
theorem B4295555 : Blo 1907435 4295555 := bstep (se 1 (by rfl) ⟨3221666, by rfl⟩ : syracuseStep 4295555 = 6443333) B6443333
theorem B2863703 : Blo 1907435 2863703 := bstep (se 1 (by rfl) ⟨2147777, by rfl⟩ : syracuseStep 2863703 = 4295555) B4295555
theorem B1909135 : Blo 1907435 1909135 := bstep (se 1 (by rfl) ⟨1431851, by rfl⟩ : syracuseStep 1909135 = 2863703) B2863703
theorem B2863709 : Blo 1907435 2863709 := bbase (se 3 (by rfl) ⟨536945, by rfl⟩ : syracuseStep 2863709 = 1073891) (by norm_num)
theorem B1909139 : Blo 1907435 1909139 := bstep (se 1 (by rfl) ⟨1431854, by rfl⟩ : syracuseStep 1909139 = 2863709) B2863709
theorem B4295573 : Blo 1907435 4295573 := bbase (se 6 (by rfl) ⟨100677, by rfl⟩ : syracuseStep 4295573 = 201355) (by norm_num)
theorem B2863715 : Blo 1907435 2863715 := bstep (se 1 (by rfl) ⟨2147786, by rfl⟩ : syracuseStep 2863715 = 4295573) B4295573
theorem B1909143 : Blo 1907435 1909143 := bstep (se 1 (by rfl) ⟨1431857, by rfl⟩ : syracuseStep 1909143 = 2863715) B2863715
theorem B5805589 : Blo 1907435 5805589 := bbase (se 6 (by rfl) ⟨136068, by rfl⟩ : syracuseStep 5805589 = 272137) (by norm_num)
theorem B7740785 : Blo 1907435 7740785 := bstep (se 2 (by rfl) ⟨2902794, by rfl⟩ : syracuseStep 7740785 = 5805589) B5805589
theorem B5160523 : Blo 1907435 5160523 := bstep (se 1 (by rfl) ⟨3870392, by rfl⟩ : syracuseStep 5160523 = 7740785) B7740785
theorem B6880697 : Blo 1907435 6880697 := bstep (se 2 (by rfl) ⟨2580261, by rfl⟩ : syracuseStep 6880697 = 5160523) B5160523
theorem B4587131 : Blo 1907435 4587131 := bstep (se 1 (by rfl) ⟨3440348, by rfl⟩ : syracuseStep 4587131 = 6880697) B6880697
theorem B3058087 : Blo 1907435 3058087 := bstep (se 1 (by rfl) ⟨2293565, by rfl⟩ : syracuseStep 3058087 = 4587131) B4587131
theorem B4077449 : Blo 1907435 4077449 := bstep (se 2 (by rfl) ⟨1529043, by rfl⟩ : syracuseStep 4077449 = 3058087) B3058087
theorem B2718299 : Blo 1907435 2718299 := bstep (se 1 (by rfl) ⟨2038724, by rfl⟩ : syracuseStep 2718299 = 4077449) B4077449
theorem B7248797 : Blo 1907435 7248797 := bstep (se 3 (by rfl) ⟨1359149, by rfl⟩ : syracuseStep 7248797 = 2718299) B2718299
theorem B4832531 : Blo 1907435 4832531 := bstep (se 1 (by rfl) ⟨3624398, by rfl⟩ : syracuseStep 4832531 = 7248797) B7248797
theorem B3221687 : Blo 1907435 3221687 := bstep (se 1 (by rfl) ⟨2416265, by rfl⟩ : syracuseStep 3221687 = 4832531) B4832531
theorem B2147791 : Blo 1907435 2147791 := bstep (se 1 (by rfl) ⟨1610843, by rfl⟩ : syracuseStep 2147791 = 3221687) B3221687
theorem B2863721 : Blo 1907435 2863721 := bstep (se 2 (by rfl) ⟨1073895, by rfl⟩ : syracuseStep 2863721 = 2147791) B2147791
theorem B1909147 : Blo 1907435 1909147 := bstep (se 1 (by rfl) ⟨1431860, by rfl⟩ : syracuseStep 1909147 = 2863721) B2863721
theorem B6880709 : Blo 1907435 6880709 := bbase (se 4 (by rfl) ⟨645066, by rfl⟩ : syracuseStep 6880709 = 1290133) (by norm_num)
theorem B4587139 : Blo 1907435 4587139 := bstep (se 1 (by rfl) ⟨3440354, by rfl⟩ : syracuseStep 4587139 = 6880709) B6880709
theorem B6116185 : Blo 1907435 6116185 := bstep (se 2 (by rfl) ⟨2293569, by rfl⟩ : syracuseStep 6116185 = 4587139) B4587139
theorem B8154913 : Blo 1907435 8154913 := bstep (se 2 (by rfl) ⟨3058092, by rfl⟩ : syracuseStep 8154913 = 6116185) B6116185
theorem B10873217 : Blo 1907435 10873217 := bstep (se 2 (by rfl) ⟨4077456, by rfl⟩ : syracuseStep 10873217 = 8154913) B8154913
theorem B7248811 : Blo 1907435 7248811 := bstep (se 1 (by rfl) ⟨5436608, by rfl⟩ : syracuseStep 7248811 = 10873217) B10873217
theorem B9665081 : Blo 1907435 9665081 := bstep (se 2 (by rfl) ⟨3624405, by rfl⟩ : syracuseStep 9665081 = 7248811) B7248811
theorem B6443387 : Blo 1907435 6443387 := bstep (se 1 (by rfl) ⟨4832540, by rfl⟩ : syracuseStep 6443387 = 9665081) B9665081
theorem B4295591 : Blo 1907435 4295591 := bstep (se 1 (by rfl) ⟨3221693, by rfl⟩ : syracuseStep 4295591 = 6443387) B6443387
theorem B2863727 : Blo 1907435 2863727 := bstep (se 1 (by rfl) ⟨2147795, by rfl⟩ : syracuseStep 2863727 = 4295591) B4295591
theorem B1909151 : Blo 1907435 1909151 := bstep (se 1 (by rfl) ⟨1431863, by rfl⟩ : syracuseStep 1909151 = 2863727) B2863727
theorem B2863733 : Blo 1907435 2863733 := bbase (se 5 (by rfl) ⟨134237, by rfl⟩ : syracuseStep 2863733 = 268475) (by norm_num)
theorem B1909155 : Blo 1907435 1909155 := bstep (se 1 (by rfl) ⟨1431866, by rfl⟩ : syracuseStep 1909155 = 2863733) B2863733
theorem B3624421 : Blo 1907435 3624421 := bbase (se 4 (by rfl) ⟨339789, by rfl⟩ : syracuseStep 3624421 = 679579) (by norm_num)
theorem B4832561 : Blo 1907435 4832561 := bstep (se 2 (by rfl) ⟨1812210, by rfl⟩ : syracuseStep 4832561 = 3624421) B3624421
theorem B3221707 : Blo 1907435 3221707 := bstep (se 1 (by rfl) ⟨2416280, by rfl⟩ : syracuseStep 3221707 = 4832561) B4832561
theorem B4295609 : Blo 1907435 4295609 := bstep (se 2 (by rfl) ⟨1610853, by rfl⟩ : syracuseStep 4295609 = 3221707) B3221707
theorem B2863739 : Blo 1907435 2863739 := bstep (se 1 (by rfl) ⟨2147804, by rfl⟩ : syracuseStep 2863739 = 4295609) B4295609
theorem B1909159 : Blo 1907435 1909159 := bstep (se 1 (by rfl) ⟨1431869, by rfl⟩ : syracuseStep 1909159 = 2863739) B2863739
theorem B2147809 : Blo 1907435 2147809 := bbase (se 2 (by rfl) ⟨805428, by rfl⟩ : syracuseStep 2147809 = 1610857) (by norm_num)
theorem B2863745 : Blo 1907435 2863745 := bstep (se 2 (by rfl) ⟨1073904, by rfl⟩ : syracuseStep 2863745 = 2147809) B2147809
theorem B1909163 : Blo 1907435 1909163 := bstep (se 1 (by rfl) ⟨1431872, by rfl⟩ : syracuseStep 1909163 = 2863745) B2863745
theorem B4832581 : Blo 1907435 4832581 := bbase (se 4 (by rfl) ⟨453054, by rfl⟩ : syracuseStep 4832581 = 906109) (by norm_num)
theorem B6443441 : Blo 1907435 6443441 := bstep (se 2 (by rfl) ⟨2416290, by rfl⟩ : syracuseStep 6443441 = 4832581) B4832581
theorem B4295627 : Blo 1907435 4295627 := bstep (se 1 (by rfl) ⟨3221720, by rfl⟩ : syracuseStep 4295627 = 6443441) B6443441
theorem B2863751 : Blo 1907435 2863751 := bstep (se 1 (by rfl) ⟨2147813, by rfl⟩ : syracuseStep 2863751 = 4295627) B4295627
theorem B1909167 : Blo 1907435 1909167 := bstep (se 1 (by rfl) ⟨1431875, by rfl⟩ : syracuseStep 1909167 = 2863751) B2863751
theorem B2863757 : Blo 1907435 2863757 := bbase (se 3 (by rfl) ⟨536954, by rfl⟩ : syracuseStep 2863757 = 1073909) (by norm_num)
theorem B1909171 : Blo 1907435 1909171 := bstep (se 1 (by rfl) ⟨1431878, by rfl⟩ : syracuseStep 1909171 = 2863757) B2863757
theorem B4295645 : Blo 1907435 4295645 := bbase (se 3 (by rfl) ⟨805433, by rfl⟩ : syracuseStep 4295645 = 1610867) (by norm_num)
theorem B2863763 : Blo 1907435 2863763 := bstep (se 1 (by rfl) ⟨2147822, by rfl⟩ : syracuseStep 2863763 = 4295645) B4295645
theorem B1909175 : Blo 1907435 1909175 := bstep (se 1 (by rfl) ⟨1431881, by rfl⟩ : syracuseStep 1909175 = 2863763) B2863763
theorem B3221741 : Blo 1907435 3221741 := bbase (se 3 (by rfl) ⟨604076, by rfl⟩ : syracuseStep 3221741 = 1208153) (by norm_num)
theorem B2147827 : Blo 1907435 2147827 := bstep (se 1 (by rfl) ⟨1610870, by rfl⟩ : syracuseStep 2147827 = 3221741) B3221741
theorem B2863769 : Blo 1907435 2863769 := bstep (se 2 (by rfl) ⟨1073913, by rfl⟩ : syracuseStep 2863769 = 2147827) B2147827
theorem B1909179 : Blo 1907435 1909179 := bstep (se 1 (by rfl) ⟨1431884, by rfl⟩ : syracuseStep 1909179 = 2863769) B2863769
theorem B2942453 : Blo 1907435 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1961635 : Blo 1907435 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B2615513 : Blo 1907435 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B27898805 : Blo 1907435 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B18599203 : Blo 1907435 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B99195749 : Blo 1907435 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B66130499 : Blo 1907435 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B44086999 : Blo 1907435 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B58782665 : Blo 1907435 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B39188443 : Blo 1907435 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B52251257 : Blo 1907435 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B34834171 : Blo 1907435 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B46445561 : Blo 1907435 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B30963707 : Blo 1907435 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B20642471 : Blo 1907435 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B13761647 : Blo 1907435 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B9174431 : Blo 1907435 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B24465149 : Blo 1907435 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B16310099 : Blo 1907435 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B10873399 : Blo 1907435 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B14497865 : Blo 1907435 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B9665243 : Blo 1907435 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B6443495 : Blo 1907435 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B4295663 : Blo 1907435 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B2863775 : Blo 1907435 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B1909183 : Blo 1907435 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B2863781 : Blo 1907435 2863781 := bbase (se 4 (by rfl) ⟨268479, by rfl⟩ : syracuseStep 2863781 = 536959) (by norm_num)
theorem B1909187 : Blo 1907435 1909187 := bstep (se 1 (by rfl) ⟨1431890, by rfl⟩ : syracuseStep 1909187 = 2863781) B2863781
theorem B2416321 : Blo 1907435 2416321 := bbase (se 2 (by rfl) ⟨906120, by rfl⟩ : syracuseStep 2416321 = 1812241) (by norm_num)
theorem B3221761 : Blo 1907435 3221761 := bstep (se 2 (by rfl) ⟨1208160, by rfl⟩ : syracuseStep 3221761 = 2416321) B2416321
theorem B4295681 : Blo 1907435 4295681 := bstep (se 2 (by rfl) ⟨1610880, by rfl⟩ : syracuseStep 4295681 = 3221761) B3221761
theorem B2863787 : Blo 1907435 2863787 := bstep (se 1 (by rfl) ⟨2147840, by rfl⟩ : syracuseStep 2863787 = 4295681) B4295681
theorem B1909191 : Blo 1907435 1909191 := bstep (se 1 (by rfl) ⟨1431893, by rfl⟩ : syracuseStep 1909191 = 2863787) B2863787
theorem B2147845 : Blo 1907435 2147845 := bbase (se 4 (by rfl) ⟨201360, by rfl⟩ : syracuseStep 2147845 = 402721) (by norm_num)
theorem B2863793 : Blo 1907435 2863793 := bstep (se 2 (by rfl) ⟨1073922, by rfl⟩ : syracuseStep 2863793 = 2147845) B2147845
theorem B1909195 : Blo 1907435 1909195 := bstep (se 1 (by rfl) ⟨1431896, by rfl⟩ : syracuseStep 1909195 = 2863793) B2863793
theorem B2718373 : Blo 1907435 2718373 := bbase (se 4 (by rfl) ⟨254847, by rfl⟩ : syracuseStep 2718373 = 509695) (by norm_num)
theorem B3624497 : Blo 1907435 3624497 := bstep (se 2 (by rfl) ⟨1359186, by rfl⟩ : syracuseStep 3624497 = 2718373) B2718373
theorem B2416331 : Blo 1907435 2416331 := bstep (se 1 (by rfl) ⟨1812248, by rfl⟩ : syracuseStep 2416331 = 3624497) B3624497
theorem B6443549 : Blo 1907435 6443549 := bstep (se 3 (by rfl) ⟨1208165, by rfl⟩ : syracuseStep 6443549 = 2416331) B2416331
theorem B4295699 : Blo 1907435 4295699 := bstep (se 1 (by rfl) ⟨3221774, by rfl⟩ : syracuseStep 4295699 = 6443549) B6443549
theorem B2863799 : Blo 1907435 2863799 := bstep (se 1 (by rfl) ⟨2147849, by rfl⟩ : syracuseStep 2863799 = 4295699) B4295699
theorem B1909199 : Blo 1907435 1909199 := bstep (se 1 (by rfl) ⟨1431899, by rfl⟩ : syracuseStep 1909199 = 2863799) B2863799
theorem B2863805 : Blo 1907435 2863805 := bbase (se 3 (by rfl) ⟨536963, by rfl⟩ : syracuseStep 2863805 = 1073927) (by norm_num)
theorem B1909203 : Blo 1907435 1909203 := bstep (se 1 (by rfl) ⟨1431902, by rfl⟩ : syracuseStep 1909203 = 2863805) B2863805
theorem B4295717 : Blo 1907435 4295717 := bbase (se 4 (by rfl) ⟨402723, by rfl⟩ : syracuseStep 4295717 = 805447) (by norm_num)
theorem B2863811 : Blo 1907435 2863811 := bstep (se 1 (by rfl) ⟨2147858, by rfl⟩ : syracuseStep 2863811 = 4295717) B4295717
theorem B1909207 : Blo 1907435 1909207 := bstep (se 1 (by rfl) ⟨1431905, by rfl⟩ : syracuseStep 1909207 = 2863811) B2863811
theorem B4832693 : Blo 1907435 4832693 := bbase (se 5 (by rfl) ⟨226532, by rfl⟩ : syracuseStep 4832693 = 453065) (by norm_num)
theorem B3221795 : Blo 1907435 3221795 := bstep (se 1 (by rfl) ⟨2416346, by rfl⟩ : syracuseStep 3221795 = 4832693) B4832693
theorem B2147863 : Blo 1907435 2147863 := bstep (se 1 (by rfl) ⟨1610897, by rfl⟩ : syracuseStep 2147863 = 3221795) B3221795
theorem B2863817 : Blo 1907435 2863817 := bstep (se 2 (by rfl) ⟨1073931, by rfl⟩ : syracuseStep 2863817 = 2147863) B2147863
theorem B1909211 : Blo 1907435 1909211 := bstep (se 1 (by rfl) ⟨1431908, by rfl⟩ : syracuseStep 1909211 = 2863817) B2863817
theorem B4587293 : Blo 1907435 4587293 := bbase (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) (by norm_num)
theorem B12232781 : Blo 1907435 12232781 := bstep (se 3 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 12232781 = 4587293) B4587293
theorem B8155187 : Blo 1907435 8155187 := bstep (se 1 (by rfl) ⟨6116390, by rfl⟩ : syracuseStep 8155187 = 12232781) B12232781
theorem B5436791 : Blo 1907435 5436791 := bstep (se 1 (by rfl) ⟨4077593, by rfl⟩ : syracuseStep 5436791 = 8155187) B8155187
theorem B3624527 : Blo 1907435 3624527 := bstep (se 1 (by rfl) ⟨2718395, by rfl⟩ : syracuseStep 3624527 = 5436791) B5436791
theorem B9665405 : Blo 1907435 9665405 := bstep (se 3 (by rfl) ⟨1812263, by rfl⟩ : syracuseStep 9665405 = 3624527) B3624527
theorem B6443603 : Blo 1907435 6443603 := bstep (se 1 (by rfl) ⟨4832702, by rfl⟩ : syracuseStep 6443603 = 9665405) B9665405
theorem B4295735 : Blo 1907435 4295735 := bstep (se 1 (by rfl) ⟨3221801, by rfl⟩ : syracuseStep 4295735 = 6443603) B6443603
theorem B2863823 : Blo 1907435 2863823 := bstep (se 1 (by rfl) ⟨2147867, by rfl⟩ : syracuseStep 2863823 = 4295735) B4295735
theorem B1909215 : Blo 1907435 1909215 := bstep (se 1 (by rfl) ⟨1431911, by rfl⟩ : syracuseStep 1909215 = 2863823) B2863823
theorem B2863829 : Blo 1907435 2863829 := bbase (se 7 (by rfl) ⟨33560, by rfl⟩ : syracuseStep 2863829 = 67121) (by norm_num)
theorem B1909219 : Blo 1907435 1909219 := bstep (se 1 (by rfl) ⟨1431914, by rfl⟩ : syracuseStep 1909219 = 2863829) B2863829
theorem B3440485 : Blo 1907435 3440485 := bbase (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) (by norm_num)
theorem B4587313 : Blo 1907435 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B6116417 : Blo 1907435 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B4077611 : Blo 1907435 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B2718407 : Blo 1907435 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B7249085 : Blo 1907435 7249085 := bstep (se 3 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 7249085 = 2718407) B2718407
theorem B4832723 : Blo 1907435 4832723 := bstep (se 1 (by rfl) ⟨3624542, by rfl⟩ : syracuseStep 4832723 = 7249085) B7249085
theorem B3221815 : Blo 1907435 3221815 := bstep (se 1 (by rfl) ⟨2416361, by rfl⟩ : syracuseStep 3221815 = 4832723) B4832723
theorem B4295753 : Blo 1907435 4295753 := bstep (se 2 (by rfl) ⟨1610907, by rfl⟩ : syracuseStep 4295753 = 3221815) B3221815
theorem B2863835 : Blo 1907435 2863835 := bstep (se 1 (by rfl) ⟨2147876, by rfl⟩ : syracuseStep 2863835 = 4295753) B4295753
theorem B1909223 : Blo 1907435 1909223 := bstep (se 1 (by rfl) ⟨1431917, by rfl⟩ : syracuseStep 1909223 = 2863835) B2863835
theorem B2147881 : Blo 1907435 2147881 := bbase (se 2 (by rfl) ⟨805455, by rfl⟩ : syracuseStep 2147881 = 1610911) (by norm_num)
theorem B2863841 : Blo 1907435 2863841 := bstep (se 2 (by rfl) ⟨1073940, by rfl⟩ : syracuseStep 2863841 = 2147881) B2147881
theorem B1909227 : Blo 1907435 1909227 := bstep (se 1 (by rfl) ⟨1431920, by rfl⟩ : syracuseStep 1909227 = 2863841) B2863841
theorem B6880997 : Blo 1907435 6880997 := bbase (se 4 (by rfl) ⟨645093, by rfl⟩ : syracuseStep 6880997 = 1290187) (by norm_num)
theorem B18349325 : Blo 1907435 18349325 := bstep (se 3 (by rfl) ⟨3440498, by rfl⟩ : syracuseStep 18349325 = 6880997) B6880997
theorem B12232883 : Blo 1907435 12232883 := bstep (se 1 (by rfl) ⟨9174662, by rfl⟩ : syracuseStep 12232883 = 18349325) B18349325
theorem B8155255 : Blo 1907435 8155255 := bstep (se 1 (by rfl) ⟨6116441, by rfl⟩ : syracuseStep 8155255 = 12232883) B12232883
theorem B10873673 : Blo 1907435 10873673 := bstep (se 2 (by rfl) ⟨4077627, by rfl⟩ : syracuseStep 10873673 = 8155255) B8155255
theorem B7249115 : Blo 1907435 7249115 := bstep (se 1 (by rfl) ⟨5436836, by rfl⟩ : syracuseStep 7249115 = 10873673) B10873673
theorem B4832743 : Blo 1907435 4832743 := bstep (se 1 (by rfl) ⟨3624557, by rfl⟩ : syracuseStep 4832743 = 7249115) B7249115
theorem B6443657 : Blo 1907435 6443657 := bstep (se 2 (by rfl) ⟨2416371, by rfl⟩ : syracuseStep 6443657 = 4832743) B4832743
theorem B4295771 : Blo 1907435 4295771 := bstep (se 1 (by rfl) ⟨3221828, by rfl⟩ : syracuseStep 4295771 = 6443657) B6443657
theorem B2863847 : Blo 1907435 2863847 := bstep (se 1 (by rfl) ⟨2147885, by rfl⟩ : syracuseStep 2863847 = 4295771) B4295771
theorem B1909231 : Blo 1907435 1909231 := bstep (se 1 (by rfl) ⟨1431923, by rfl⟩ : syracuseStep 1909231 = 2863847) B2863847
theorem B2863853 : Blo 1907435 2863853 := bbase (se 3 (by rfl) ⟨536972, by rfl⟩ : syracuseStep 2863853 = 1073945) (by norm_num)
theorem B1909235 : Blo 1907435 1909235 := bstep (se 1 (by rfl) ⟨1431926, by rfl⟩ : syracuseStep 1909235 = 2863853) B2863853
theorem B4295789 : Blo 1907435 4295789 := bbase (se 3 (by rfl) ⟨805460, by rfl⟩ : syracuseStep 4295789 = 1610921) (by norm_num)
theorem B2863859 : Blo 1907435 2863859 := bstep (se 1 (by rfl) ⟨2147894, by rfl⟩ : syracuseStep 2863859 = 4295789) B4295789
theorem B1909239 : Blo 1907435 1909239 := bstep (se 1 (by rfl) ⟨1431929, by rfl⟩ : syracuseStep 1909239 = 2863859) B2863859
theorem B3624581 : Blo 1907435 3624581 := bbase (se 4 (by rfl) ⟨339804, by rfl⟩ : syracuseStep 3624581 = 679609) (by norm_num)
theorem B2416387 : Blo 1907435 2416387 := bstep (se 1 (by rfl) ⟨1812290, by rfl⟩ : syracuseStep 2416387 = 3624581) B3624581
theorem B3221849 : Blo 1907435 3221849 := bstep (se 2 (by rfl) ⟨1208193, by rfl⟩ : syracuseStep 3221849 = 2416387) B2416387
theorem B2147899 : Blo 1907435 2147899 := bstep (se 1 (by rfl) ⟨1610924, by rfl⟩ : syracuseStep 2147899 = 3221849) B3221849
theorem B2863865 : Blo 1907435 2863865 := bstep (se 2 (by rfl) ⟨1073949, by rfl⟩ : syracuseStep 2863865 = 2147899) B2147899
theorem B1909243 : Blo 1907435 1909243 := bstep (se 1 (by rfl) ⟨1431932, by rfl⟩ : syracuseStep 1909243 = 2863865) B2863865
theorem B3265813 : Blo 1907435 3265813 := bbase (se 6 (by rfl) ⟨76542, by rfl⟩ : syracuseStep 3265813 = 153085) (by norm_num)
theorem B4354417 : Blo 1907435 4354417 := bstep (se 2 (by rfl) ⟨1632906, by rfl⟩ : syracuseStep 4354417 = 3265813) B3265813
theorem B23223557 : Blo 1907435 23223557 := bstep (se 4 (by rfl) ⟨2177208, by rfl⟩ : syracuseStep 23223557 = 4354417) B4354417
theorem B61929485 : Blo 1907435 61929485 := bstep (se 3 (by rfl) ⟨11611778, by rfl⟩ : syracuseStep 61929485 = 23223557) B23223557
theorem B41286323 : Blo 1907435 41286323 := bstep (se 1 (by rfl) ⟨30964742, by rfl⟩ : syracuseStep 41286323 = 61929485) B61929485
theorem B27524215 : Blo 1907435 27524215 := bstep (se 1 (by rfl) ⟨20643161, by rfl⟩ : syracuseStep 27524215 = 41286323) B41286323
theorem B36698953 : Blo 1907435 36698953 := bstep (se 2 (by rfl) ⟨13762107, by rfl⟩ : syracuseStep 36698953 = 27524215) B27524215
theorem B48931937 : Blo 1907435 48931937 := bstep (se 2 (by rfl) ⟨18349476, by rfl⟩ : syracuseStep 48931937 = 36698953) B36698953
theorem B32621291 : Blo 1907435 32621291 := bstep (se 1 (by rfl) ⟨24465968, by rfl⟩ : syracuseStep 32621291 = 48931937) B48931937
theorem B21747527 : Blo 1907435 21747527 := bstep (se 1 (by rfl) ⟨16310645, by rfl⟩ : syracuseStep 21747527 = 32621291) B32621291
theorem B14498351 : Blo 1907435 14498351 := bstep (se 1 (by rfl) ⟨10873763, by rfl⟩ : syracuseStep 14498351 = 21747527) B21747527
theorem B9665567 : Blo 1907435 9665567 := bstep (se 1 (by rfl) ⟨7249175, by rfl⟩ : syracuseStep 9665567 = 14498351) B14498351
theorem B6443711 : Blo 1907435 6443711 := bstep (se 1 (by rfl) ⟨4832783, by rfl⟩ : syracuseStep 6443711 = 9665567) B9665567
theorem B4295807 : Blo 1907435 4295807 := bstep (se 1 (by rfl) ⟨3221855, by rfl⟩ : syracuseStep 4295807 = 6443711) B6443711
theorem B2863871 : Blo 1907435 2863871 := bstep (se 1 (by rfl) ⟨2147903, by rfl⟩ : syracuseStep 2863871 = 4295807) B4295807
theorem B1909247 : Blo 1907435 1909247 := bstep (se 1 (by rfl) ⟨1431935, by rfl⟩ : syracuseStep 1909247 = 2863871) B2863871
theorem B2863877 : Blo 1907435 2863877 := bbase (se 4 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 2863877 = 536977) (by norm_num)
theorem B1909251 : Blo 1907435 1909251 := bstep (se 1 (by rfl) ⟨1431938, by rfl⟩ : syracuseStep 1909251 = 2863877) B2863877
theorem B3221869 : Blo 1907435 3221869 := bbase (se 3 (by rfl) ⟨604100, by rfl⟩ : syracuseStep 3221869 = 1208201) (by norm_num)
theorem B4295825 : Blo 1907435 4295825 := bstep (se 2 (by rfl) ⟨1610934, by rfl⟩ : syracuseStep 4295825 = 3221869) B3221869
theorem B2863883 : Blo 1907435 2863883 := bstep (se 1 (by rfl) ⟨2147912, by rfl⟩ : syracuseStep 2863883 = 4295825) B4295825
theorem B1909255 : Blo 1907435 1909255 := bstep (se 1 (by rfl) ⟨1431941, by rfl⟩ : syracuseStep 1909255 = 2863883) B2863883
theorem B2147917 : Blo 1907435 2147917 := bbase (se 3 (by rfl) ⟨402734, by rfl⟩ : syracuseStep 2147917 = 805469) (by norm_num)
theorem B2863889 : Blo 1907435 2863889 := bstep (se 2 (by rfl) ⟨1073958, by rfl⟩ : syracuseStep 2863889 = 2147917) B2147917
theorem B1909259 : Blo 1907435 1909259 := bstep (se 1 (by rfl) ⟨1431944, by rfl⟩ : syracuseStep 1909259 = 2863889) B2863889
theorem B6443765 : Blo 1907435 6443765 := bbase (se 5 (by rfl) ⟨302051, by rfl⟩ : syracuseStep 6443765 = 604103) (by norm_num)
theorem B4295843 : Blo 1907435 4295843 := bstep (se 1 (by rfl) ⟨3221882, by rfl⟩ : syracuseStep 4295843 = 6443765) B6443765
theorem B2863895 : Blo 1907435 2863895 := bstep (se 1 (by rfl) ⟨2147921, by rfl⟩ : syracuseStep 2863895 = 4295843) B4295843
theorem B1909263 : Blo 1907435 1909263 := bstep (se 1 (by rfl) ⟨1431947, by rfl⟩ : syracuseStep 1909263 = 2863895) B2863895
theorem B2863901 : Blo 1907435 2863901 := bbase (se 3 (by rfl) ⟨536981, by rfl⟩ : syracuseStep 2863901 = 1073963) (by norm_num)
theorem B1909267 : Blo 1907435 1909267 := bstep (se 1 (by rfl) ⟨1431950, by rfl⟩ : syracuseStep 1909267 = 2863901) B2863901
theorem B4295861 : Blo 1907435 4295861 := bbase (se 5 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 4295861 = 402737) (by norm_num)
theorem B2863907 : Blo 1907435 2863907 := bstep (se 1 (by rfl) ⟨2147930, by rfl⟩ : syracuseStep 2863907 = 4295861) B4295861
theorem B1909271 : Blo 1907435 1909271 := bstep (se 1 (by rfl) ⟨1431953, by rfl⟩ : syracuseStep 1909271 = 2863907) B2863907
theorem B2038861 : Blo 1907435 2038861 := bbase (se 3 (by rfl) ⟨382286, by rfl⟩ : syracuseStep 2038861 = 764573) (by norm_num)
theorem B10873925 : Blo 1907435 10873925 := bstep (se 4 (by rfl) ⟨1019430, by rfl⟩ : syracuseStep 10873925 = 2038861) B2038861
theorem B7249283 : Blo 1907435 7249283 := bstep (se 1 (by rfl) ⟨5436962, by rfl⟩ : syracuseStep 7249283 = 10873925) B10873925
theorem B4832855 : Blo 1907435 4832855 := bstep (se 1 (by rfl) ⟨3624641, by rfl⟩ : syracuseStep 4832855 = 7249283) B7249283
theorem B3221903 : Blo 1907435 3221903 := bstep (se 1 (by rfl) ⟨2416427, by rfl⟩ : syracuseStep 3221903 = 4832855) B4832855
theorem B2147935 : Blo 1907435 2147935 := bstep (se 1 (by rfl) ⟨1610951, by rfl⟩ : syracuseStep 2147935 = 3221903) B3221903
theorem B2863913 : Blo 1907435 2863913 := bstep (se 2 (by rfl) ⟨1073967, by rfl⟩ : syracuseStep 2863913 = 2147935) B2147935
theorem B1909275 : Blo 1907435 1909275 := bstep (se 1 (by rfl) ⟨1431956, by rfl⟩ : syracuseStep 1909275 = 2863913) B2863913
theorem B2038865 : Blo 1907435 2038865 := bbase (se 2 (by rfl) ⟨764574, by rfl⟩ : syracuseStep 2038865 = 1529149) (by norm_num)
theorem B5436973 : Blo 1907435 5436973 := bstep (se 3 (by rfl) ⟨1019432, by rfl⟩ : syracuseStep 5436973 = 2038865) B2038865
theorem B7249297 : Blo 1907435 7249297 := bstep (se 2 (by rfl) ⟨2718486, by rfl⟩ : syracuseStep 7249297 = 5436973) B5436973
theorem B9665729 : Blo 1907435 9665729 := bstep (se 2 (by rfl) ⟨3624648, by rfl⟩ : syracuseStep 9665729 = 7249297) B7249297
theorem B6443819 : Blo 1907435 6443819 := bstep (se 1 (by rfl) ⟨4832864, by rfl⟩ : syracuseStep 6443819 = 9665729) B9665729
theorem B4295879 : Blo 1907435 4295879 := bstep (se 1 (by rfl) ⟨3221909, by rfl⟩ : syracuseStep 4295879 = 6443819) B6443819
theorem B2863919 : Blo 1907435 2863919 := bstep (se 1 (by rfl) ⟨2147939, by rfl⟩ : syracuseStep 2863919 = 4295879) B4295879
theorem B1909279 : Blo 1907435 1909279 := bstep (se 1 (by rfl) ⟨1431959, by rfl⟩ : syracuseStep 1909279 = 2863919) B2863919
theorem B2863925 : Blo 1907435 2863925 := bbase (se 5 (by rfl) ⟨134246, by rfl⟩ : syracuseStep 2863925 = 268493) (by norm_num)
theorem B1909283 : Blo 1907435 1909283 := bstep (se 1 (by rfl) ⟨1431962, by rfl⟩ : syracuseStep 1909283 = 2863925) B2863925
theorem B4832885 : Blo 1907435 4832885 := bbase (se 5 (by rfl) ⟨226541, by rfl⟩ : syracuseStep 4832885 = 453083) (by norm_num)
theorem B3221923 : Blo 1907435 3221923 := bstep (se 1 (by rfl) ⟨2416442, by rfl⟩ : syracuseStep 3221923 = 4832885) B4832885
theorem B4295897 : Blo 1907435 4295897 := bstep (se 2 (by rfl) ⟨1610961, by rfl⟩ : syracuseStep 4295897 = 3221923) B3221923
theorem B2863931 : Blo 1907435 2863931 := bstep (se 1 (by rfl) ⟨2147948, by rfl⟩ : syracuseStep 2863931 = 4295897) B4295897
theorem B1909287 : Blo 1907435 1909287 := bstep (se 1 (by rfl) ⟨1431965, by rfl⟩ : syracuseStep 1909287 = 2863931) B2863931
theorem B2147953 : Blo 1907435 2147953 := bbase (se 2 (by rfl) ⟨805482, by rfl⟩ : syracuseStep 2147953 = 1610965) (by norm_num)
theorem B2863937 : Blo 1907435 2863937 := bstep (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) B2147953
theorem B1909291 : Blo 1907435 1909291 := bstep (se 1 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 1909291 = 2863937) B2863937
theorem B5806037 : Blo 1907435 5806037 := bbase (se 7 (by rfl) ⟨68039, by rfl⟩ : syracuseStep 5806037 = 136079) (by norm_num)
theorem B15482765 : Blo 1907435 15482765 := bstep (se 3 (by rfl) ⟨2903018, by rfl⟩ : syracuseStep 15482765 = 5806037) B5806037
theorem B10321843 : Blo 1907435 10321843 := bstep (se 1 (by rfl) ⟨7741382, by rfl⟩ : syracuseStep 10321843 = 15482765) B15482765
theorem B13762457 : Blo 1907435 13762457 := bstep (se 2 (by rfl) ⟨5160921, by rfl⟩ : syracuseStep 13762457 = 10321843) B10321843
theorem B9174971 : Blo 1907435 9174971 := bstep (se 1 (by rfl) ⟨6881228, by rfl⟩ : syracuseStep 9174971 = 13762457) B13762457
theorem B6116647 : Blo 1907435 6116647 := bstep (se 1 (by rfl) ⟨4587485, by rfl⟩ : syracuseStep 6116647 = 9174971) B9174971
theorem B8155529 : Blo 1907435 8155529 := bstep (se 2 (by rfl) ⟨3058323, by rfl⟩ : syracuseStep 8155529 = 6116647) B6116647
theorem B5437019 : Blo 1907435 5437019 := bstep (se 1 (by rfl) ⟨4077764, by rfl⟩ : syracuseStep 5437019 = 8155529) B8155529
theorem B3624679 : Blo 1907435 3624679 := bstep (se 1 (by rfl) ⟨2718509, by rfl⟩ : syracuseStep 3624679 = 5437019) B5437019
theorem B4832905 : Blo 1907435 4832905 := bstep (se 2 (by rfl) ⟨1812339, by rfl⟩ : syracuseStep 4832905 = 3624679) B3624679
theorem B6443873 : Blo 1907435 6443873 := bstep (se 2 (by rfl) ⟨2416452, by rfl⟩ : syracuseStep 6443873 = 4832905) B4832905
theorem B4295915 : Blo 1907435 4295915 := bstep (se 1 (by rfl) ⟨3221936, by rfl⟩ : syracuseStep 4295915 = 6443873) B6443873
theorem B2863943 : Blo 1907435 2863943 := bstep (se 1 (by rfl) ⟨2147957, by rfl⟩ : syracuseStep 2863943 = 4295915) B4295915
theorem B1909295 : Blo 1907435 1909295 := bstep (se 1 (by rfl) ⟨1431971, by rfl⟩ : syracuseStep 1909295 = 2863943) B2863943
theorem B2863949 : Blo 1907435 2863949 := bbase (se 3 (by rfl) ⟨536990, by rfl⟩ : syracuseStep 2863949 = 1073981) (by norm_num)
theorem B1909299 : Blo 1907435 1909299 := bstep (se 1 (by rfl) ⟨1431974, by rfl⟩ : syracuseStep 1909299 = 2863949) B2863949
theorem B4295933 : Blo 1907435 4295933 := bbase (se 3 (by rfl) ⟨805487, by rfl⟩ : syracuseStep 4295933 = 1610975) (by norm_num)
theorem B2863955 : Blo 1907435 2863955 := bstep (se 1 (by rfl) ⟨2147966, by rfl⟩ : syracuseStep 2863955 = 4295933) B4295933
theorem B1909303 : Blo 1907435 1909303 := bstep (se 1 (by rfl) ⟨1431977, by rfl⟩ : syracuseStep 1909303 = 2863955) B2863955
theorem B3221957 : Blo 1907435 3221957 := bbase (se 4 (by rfl) ⟨302058, by rfl⟩ : syracuseStep 3221957 = 604117) (by norm_num)
theorem B2147971 : Blo 1907435 2147971 := bstep (se 1 (by rfl) ⟨1610978, by rfl⟩ : syracuseStep 2147971 = 3221957) B3221957
theorem B2863961 : Blo 1907435 2863961 := bstep (se 2 (by rfl) ⟨1073985, by rfl⟩ : syracuseStep 2863961 = 2147971) B2147971
theorem B1909307 : Blo 1907435 1909307 := bstep (se 1 (by rfl) ⟨1431980, by rfl⟩ : syracuseStep 1909307 = 2863961) B2863961
theorem B14498837 : Blo 1907435 14498837 := bbase (se 6 (by rfl) ⟨339816, by rfl⟩ : syracuseStep 14498837 = 679633) (by norm_num)
theorem B9665891 : Blo 1907435 9665891 := bstep (se 1 (by rfl) ⟨7249418, by rfl⟩ : syracuseStep 9665891 = 14498837) B14498837
theorem B6443927 : Blo 1907435 6443927 := bstep (se 1 (by rfl) ⟨4832945, by rfl⟩ : syracuseStep 6443927 = 9665891) B9665891
theorem B4295951 : Blo 1907435 4295951 := bstep (se 1 (by rfl) ⟨3221963, by rfl⟩ : syracuseStep 4295951 = 6443927) B6443927
theorem B2863967 : Blo 1907435 2863967 := bstep (se 1 (by rfl) ⟨2147975, by rfl⟩ : syracuseStep 2863967 = 4295951) B4295951
theorem B1909311 : Blo 1907435 1909311 := bstep (se 1 (by rfl) ⟨1431983, by rfl⟩ : syracuseStep 1909311 = 2863967) B2863967
theorem B2863973 : Blo 1907435 2863973 := bbase (se 4 (by rfl) ⟨268497, by rfl⟩ : syracuseStep 2863973 = 536995) (by norm_num)
theorem B1909315 : Blo 1907435 1909315 := bstep (se 1 (by rfl) ⟨1431986, by rfl⟩ : syracuseStep 1909315 = 2863973) B2863973
theorem B3624725 : Blo 1907435 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B2416483 : Blo 1907435 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B3221977 : Blo 1907435 3221977 := bstep (se 2 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 3221977 = 2416483) B2416483
theorem B4295969 : Blo 1907435 4295969 := bstep (se 2 (by rfl) ⟨1610988, by rfl⟩ : syracuseStep 4295969 = 3221977) B3221977
theorem B2863979 : Blo 1907435 2863979 := bstep (se 1 (by rfl) ⟨2147984, by rfl⟩ : syracuseStep 2863979 = 4295969) B4295969
theorem B1909319 : Blo 1907435 1909319 := bstep (se 1 (by rfl) ⟨1431989, by rfl⟩ : syracuseStep 1909319 = 2863979) B2863979
theorem B2147989 : Blo 1907435 2147989 := bbase (se 6 (by rfl) ⟨50343, by rfl⟩ : syracuseStep 2147989 = 100687) (by norm_num)
theorem B2863985 : Blo 1907435 2863985 := bstep (se 2 (by rfl) ⟨1073994, by rfl⟩ : syracuseStep 2863985 = 2147989) B2147989
theorem B1909323 : Blo 1907435 1909323 := bstep (se 1 (by rfl) ⟨1431992, by rfl⟩ : syracuseStep 1909323 = 2863985) B2863985
theorem B2416493 : Blo 1907435 2416493 := bbase (se 3 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 2416493 = 906185) (by norm_num)
theorem B6443981 : Blo 1907435 6443981 := bstep (se 3 (by rfl) ⟨1208246, by rfl⟩ : syracuseStep 6443981 = 2416493) B2416493
theorem B4295987 : Blo 1907435 4295987 := bstep (se 1 (by rfl) ⟨3221990, by rfl⟩ : syracuseStep 4295987 = 6443981) B6443981
theorem B2863991 : Blo 1907435 2863991 := bstep (se 1 (by rfl) ⟨2147993, by rfl⟩ : syracuseStep 2863991 = 4295987) B4295987
theorem B1909327 : Blo 1907435 1909327 := bstep (se 1 (by rfl) ⟨1431995, by rfl⟩ : syracuseStep 1909327 = 2863991) B2863991
theorem B2863997 : Blo 1907435 2863997 := bbase (se 3 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 2863997 = 1073999) (by norm_num)
theorem B1909331 : Blo 1907435 1909331 := bstep (se 1 (by rfl) ⟨1431998, by rfl⟩ : syracuseStep 1909331 = 2863997) B2863997
theorem B4296005 : Blo 1907435 4296005 := bbase (se 4 (by rfl) ⟨402750, by rfl⟩ : syracuseStep 4296005 = 805501) (by norm_num)
theorem B2864003 : Blo 1907435 2864003 := bstep (se 1 (by rfl) ⟨2148002, by rfl⟩ : syracuseStep 2864003 = 4296005) B4296005
theorem B1909335 : Blo 1907435 1909335 := bstep (se 1 (by rfl) ⟨1432001, by rfl⟩ : syracuseStep 1909335 = 2864003) B2864003
theorem B6116789 : Blo 1907435 6116789 := bbase (se 5 (by rfl) ⟨286724, by rfl⟩ : syracuseStep 6116789 = 573449) (by norm_num)
theorem B4077859 : Blo 1907435 4077859 := bstep (se 1 (by rfl) ⟨3058394, by rfl⟩ : syracuseStep 4077859 = 6116789) B6116789
theorem B5437145 : Blo 1907435 5437145 := bstep (se 2 (by rfl) ⟨2038929, by rfl⟩ : syracuseStep 5437145 = 4077859) B4077859
theorem B3624763 : Blo 1907435 3624763 := bstep (se 1 (by rfl) ⟨2718572, by rfl⟩ : syracuseStep 3624763 = 5437145) B5437145
theorem B4833017 : Blo 1907435 4833017 := bstep (se 2 (by rfl) ⟨1812381, by rfl⟩ : syracuseStep 4833017 = 3624763) B3624763
theorem B3222011 : Blo 1907435 3222011 := bstep (se 1 (by rfl) ⟨2416508, by rfl⟩ : syracuseStep 3222011 = 4833017) B4833017
theorem B2148007 : Blo 1907435 2148007 := bstep (se 1 (by rfl) ⟨1611005, by rfl⟩ : syracuseStep 2148007 = 3222011) B3222011
theorem B2864009 : Blo 1907435 2864009 := bstep (se 2 (by rfl) ⟨1074003, by rfl⟩ : syracuseStep 2864009 = 2148007) B2148007
theorem B1909339 : Blo 1907435 1909339 := bstep (se 1 (by rfl) ⟨1432004, by rfl⟩ : syracuseStep 1909339 = 2864009) B2864009
theorem B9666053 : Blo 1907435 9666053 := bbase (se 4 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 9666053 = 1812385) (by norm_num)
theorem B6444035 : Blo 1907435 6444035 := bstep (se 1 (by rfl) ⟨4833026, by rfl⟩ : syracuseStep 6444035 = 9666053) B9666053
theorem B4296023 : Blo 1907435 4296023 := bstep (se 1 (by rfl) ⟨3222017, by rfl⟩ : syracuseStep 4296023 = 6444035) B6444035
theorem B2864015 : Blo 1907435 2864015 := bstep (se 1 (by rfl) ⟨2148011, by rfl⟩ : syracuseStep 2864015 = 4296023) B4296023
theorem B1909343 : Blo 1907435 1909343 := bstep (se 1 (by rfl) ⟨1432007, by rfl⟩ : syracuseStep 1909343 = 2864015) B2864015
theorem B2864021 : Blo 1907435 2864021 := bbase (se 6 (by rfl) ⟨67125, by rfl⟩ : syracuseStep 2864021 = 134251) (by norm_num)
theorem B1909347 : Blo 1907435 1909347 := bstep (se 1 (by rfl) ⟨1432010, by rfl⟩ : syracuseStep 1909347 = 2864021) B2864021
theorem B10874357 : Blo 1907435 10874357 := bbase (se 5 (by rfl) ⟨509735, by rfl⟩ : syracuseStep 10874357 = 1019471) (by norm_num)
theorem B7249571 : Blo 1907435 7249571 := bstep (se 1 (by rfl) ⟨5437178, by rfl⟩ : syracuseStep 7249571 = 10874357) B10874357
theorem B4833047 : Blo 1907435 4833047 := bstep (se 1 (by rfl) ⟨3624785, by rfl⟩ : syracuseStep 4833047 = 7249571) B7249571
theorem B3222031 : Blo 1907435 3222031 := bstep (se 1 (by rfl) ⟨2416523, by rfl⟩ : syracuseStep 3222031 = 4833047) B4833047
theorem B4296041 : Blo 1907435 4296041 := bstep (se 2 (by rfl) ⟨1611015, by rfl⟩ : syracuseStep 4296041 = 3222031) B3222031
theorem B2864027 : Blo 1907435 2864027 := bstep (se 1 (by rfl) ⟨2148020, by rfl⟩ : syracuseStep 2864027 = 4296041) B4296041
theorem B1909351 : Blo 1907435 1909351 := bstep (se 1 (by rfl) ⟨1432013, by rfl⟩ : syracuseStep 1909351 = 2864027) B2864027
theorem B2148025 : Blo 1907435 2148025 := bbase (se 2 (by rfl) ⟨805509, by rfl⟩ : syracuseStep 2148025 = 1611019) (by norm_num)
theorem B2864033 : Blo 1907435 2864033 := bstep (se 2 (by rfl) ⟨1074012, by rfl⟩ : syracuseStep 2864033 = 2148025) B2148025
theorem B1909355 : Blo 1907435 1909355 := bstep (se 1 (by rfl) ⟨1432016, by rfl⟩ : syracuseStep 1909355 = 2864033) B2864033
theorem B4077901 : Blo 1907435 4077901 := bbase (se 3 (by rfl) ⟨764606, by rfl⟩ : syracuseStep 4077901 = 1529213) (by norm_num)
theorem B5437201 : Blo 1907435 5437201 := bstep (se 2 (by rfl) ⟨2038950, by rfl⟩ : syracuseStep 5437201 = 4077901) B4077901
theorem B7249601 : Blo 1907435 7249601 := bstep (se 2 (by rfl) ⟨2718600, by rfl⟩ : syracuseStep 7249601 = 5437201) B5437201
theorem B4833067 : Blo 1907435 4833067 := bstep (se 1 (by rfl) ⟨3624800, by rfl⟩ : syracuseStep 4833067 = 7249601) B7249601
theorem B6444089 : Blo 1907435 6444089 := bstep (se 2 (by rfl) ⟨2416533, by rfl⟩ : syracuseStep 6444089 = 4833067) B4833067
theorem B4296059 : Blo 1907435 4296059 := bstep (se 1 (by rfl) ⟨3222044, by rfl⟩ : syracuseStep 4296059 = 6444089) B6444089
theorem B2864039 : Blo 1907435 2864039 := bstep (se 1 (by rfl) ⟨2148029, by rfl⟩ : syracuseStep 2864039 = 4296059) B4296059
theorem B1909359 : Blo 1907435 1909359 := bstep (se 1 (by rfl) ⟨1432019, by rfl⟩ : syracuseStep 1909359 = 2864039) B2864039
theorem B2864045 : Blo 1907435 2864045 := bbase (se 3 (by rfl) ⟨537008, by rfl⟩ : syracuseStep 2864045 = 1074017) (by norm_num)
theorem B1909363 : Blo 1907435 1909363 := bstep (se 1 (by rfl) ⟨1432022, by rfl⟩ : syracuseStep 1909363 = 2864045) B2864045
theorem B4296077 : Blo 1907435 4296077 := bbase (se 3 (by rfl) ⟨805514, by rfl⟩ : syracuseStep 4296077 = 1611029) (by norm_num)
theorem B2864051 : Blo 1907435 2864051 := bstep (se 1 (by rfl) ⟨2148038, by rfl⟩ : syracuseStep 2864051 = 4296077) B4296077
theorem B1909367 : Blo 1907435 1909367 := bstep (se 1 (by rfl) ⟨1432025, by rfl⟩ : syracuseStep 1909367 = 2864051) B2864051
theorem B2416549 : Blo 1907435 2416549 := bbase (se 4 (by rfl) ⟨226551, by rfl⟩ : syracuseStep 2416549 = 453103) (by norm_num)
theorem B3222065 : Blo 1907435 3222065 := bstep (se 2 (by rfl) ⟨1208274, by rfl⟩ : syracuseStep 3222065 = 2416549) B2416549
theorem B2148043 : Blo 1907435 2148043 := bstep (se 1 (by rfl) ⟨1611032, by rfl⟩ : syracuseStep 2148043 = 3222065) B3222065
theorem B2864057 : Blo 1907435 2864057 := bstep (se 2 (by rfl) ⟨1074021, by rfl⟩ : syracuseStep 2864057 = 2148043) B2148043
theorem B1909371 : Blo 1907435 1909371 := bstep (se 1 (by rfl) ⟨1432028, by rfl⟩ : syracuseStep 1909371 = 2864057) B2864057
theorem B4133573 : Blo 1907435 4133573 := bbase (se 4 (by rfl) ⟨387522, by rfl⟩ : syracuseStep 4133573 = 775045) (by norm_num)
theorem B2755715 : Blo 1907435 2755715 := bstep (se 1 (by rfl) ⟨2066786, by rfl⟩ : syracuseStep 2755715 = 4133573) B4133573
theorem B7348573 : Blo 1907435 7348573 := bstep (se 3 (by rfl) ⟨1377857, by rfl⟩ : syracuseStep 7348573 = 2755715) B2755715
theorem B9798097 : Blo 1907435 9798097 := bstep (se 2 (by rfl) ⟨3674286, by rfl⟩ : syracuseStep 9798097 = 7348573) B7348573
theorem B13064129 : Blo 1907435 13064129 := bstep (se 2 (by rfl) ⟨4899048, by rfl⟩ : syracuseStep 13064129 = 9798097) B9798097
theorem B8709419 : Blo 1907435 8709419 := bstep (se 1 (by rfl) ⟨6532064, by rfl⟩ : syracuseStep 8709419 = 13064129) B13064129
theorem B5806279 : Blo 1907435 5806279 := bstep (se 1 (by rfl) ⟨4354709, by rfl⟩ : syracuseStep 5806279 = 8709419) B8709419
theorem B7741705 : Blo 1907435 7741705 := bstep (se 2 (by rfl) ⟨2903139, by rfl⟩ : syracuseStep 7741705 = 5806279) B5806279
theorem B10322273 : Blo 1907435 10322273 := bstep (se 2 (by rfl) ⟨3870852, by rfl⟩ : syracuseStep 10322273 = 7741705) B7741705
theorem B27526061 : Blo 1907435 27526061 := bstep (se 3 (by rfl) ⟨5161136, by rfl⟩ : syracuseStep 27526061 = 10322273) B10322273
theorem B18350707 : Blo 1907435 18350707 := bstep (se 1 (by rfl) ⟨13763030, by rfl⟩ : syracuseStep 18350707 = 27526061) B27526061
theorem B24467609 : Blo 1907435 24467609 := bstep (se 2 (by rfl) ⟨9175353, by rfl⟩ : syracuseStep 24467609 = 18350707) B18350707
theorem B16311739 : Blo 1907435 16311739 := bstep (se 1 (by rfl) ⟨12233804, by rfl⟩ : syracuseStep 16311739 = 24467609) B24467609
theorem B21748985 : Blo 1907435 21748985 := bstep (se 2 (by rfl) ⟨8155869, by rfl⟩ : syracuseStep 21748985 = 16311739) B16311739
theorem B14499323 : Blo 1907435 14499323 := bstep (se 1 (by rfl) ⟨10874492, by rfl⟩ : syracuseStep 14499323 = 21748985) B21748985
theorem B9666215 : Blo 1907435 9666215 := bstep (se 1 (by rfl) ⟨7249661, by rfl⟩ : syracuseStep 9666215 = 14499323) B14499323
theorem B6444143 : Blo 1907435 6444143 := bstep (se 1 (by rfl) ⟨4833107, by rfl⟩ : syracuseStep 6444143 = 9666215) B9666215
theorem B4296095 : Blo 1907435 4296095 := bstep (se 1 (by rfl) ⟨3222071, by rfl⟩ : syracuseStep 4296095 = 6444143) B6444143
theorem B2864063 : Blo 1907435 2864063 := bstep (se 1 (by rfl) ⟨2148047, by rfl⟩ : syracuseStep 2864063 = 4296095) B4296095
theorem B1909375 : Blo 1907435 1909375 := bstep (se 1 (by rfl) ⟨1432031, by rfl⟩ : syracuseStep 1909375 = 2864063) B2864063
theorem B2864069 : Blo 1907435 2864069 := bbase (se 4 (by rfl) ⟨268506, by rfl⟩ : syracuseStep 2864069 = 537013) (by norm_num)
theorem B1909379 : Blo 1907435 1909379 := bstep (se 1 (by rfl) ⟨1432034, by rfl⟩ : syracuseStep 1909379 = 2864069) B2864069
theorem B3222085 : Blo 1907435 3222085 := bbase (se 4 (by rfl) ⟨302070, by rfl⟩ : syracuseStep 3222085 = 604141) (by norm_num)
theorem B4296113 : Blo 1907435 4296113 := bstep (se 2 (by rfl) ⟨1611042, by rfl⟩ : syracuseStep 4296113 = 3222085) B3222085
theorem B2864075 : Blo 1907435 2864075 := bstep (se 1 (by rfl) ⟨2148056, by rfl⟩ : syracuseStep 2864075 = 4296113) B4296113
theorem B1909383 : Blo 1907435 1909383 := bstep (se 1 (by rfl) ⟨1432037, by rfl⟩ : syracuseStep 1909383 = 2864075) B2864075
theorem B2148061 : Blo 1907435 2148061 := bbase (se 3 (by rfl) ⟨402761, by rfl⟩ : syracuseStep 2148061 = 805523) (by norm_num)
theorem B2864081 : Blo 1907435 2864081 := bstep (se 2 (by rfl) ⟨1074030, by rfl⟩ : syracuseStep 2864081 = 2148061) B2148061
theorem B1909387 : Blo 1907435 1909387 := bstep (se 1 (by rfl) ⟨1432040, by rfl⟩ : syracuseStep 1909387 = 2864081) B2864081
theorem B6444197 : Blo 1907435 6444197 := bbase (se 4 (by rfl) ⟨604143, by rfl⟩ : syracuseStep 6444197 = 1208287) (by norm_num)
theorem B4296131 : Blo 1907435 4296131 := bstep (se 1 (by rfl) ⟨3222098, by rfl⟩ : syracuseStep 4296131 = 6444197) B6444197
theorem B2864087 : Blo 1907435 2864087 := bstep (se 1 (by rfl) ⟨2148065, by rfl⟩ : syracuseStep 2864087 = 4296131) B4296131
theorem B1909391 : Blo 1907435 1909391 := bstep (se 1 (by rfl) ⟨1432043, by rfl⟩ : syracuseStep 1909391 = 2864087) B2864087
theorem B2864093 : Blo 1907435 2864093 := bbase (se 3 (by rfl) ⟨537017, by rfl⟩ : syracuseStep 2864093 = 1074035) (by norm_num)
theorem B1909395 : Blo 1907435 1909395 := bstep (se 1 (by rfl) ⟨1432046, by rfl⟩ : syracuseStep 1909395 = 2864093) B2864093
theorem B4296149 : Blo 1907435 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B2864099 : Blo 1907435 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B1909399 : Blo 1907435 1909399 := bstep (se 1 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 1909399 = 2864099) B2864099
theorem B6200453 : Blo 1907435 6200453 := bbase (se 4 (by rfl) ⟨581292, by rfl⟩ : syracuseStep 6200453 = 1162585) (by norm_num)
theorem B4133635 : Blo 1907435 4133635 := bstep (se 1 (by rfl) ⟨3100226, by rfl⟩ : syracuseStep 4133635 = 6200453) B6200453
theorem B22046053 : Blo 1907435 22046053 := bstep (se 4 (by rfl) ⟨2066817, by rfl⟩ : syracuseStep 22046053 = 4133635) B4133635
theorem B29394737 : Blo 1907435 29394737 := bstep (se 2 (by rfl) ⟨11023026, by rfl⟩ : syracuseStep 29394737 = 22046053) B22046053
theorem B19596491 : Blo 1907435 19596491 := bstep (se 1 (by rfl) ⟨14697368, by rfl⟩ : syracuseStep 19596491 = 29394737) B29394737
theorem B13064327 : Blo 1907435 13064327 := bstep (se 1 (by rfl) ⟨9798245, by rfl⟩ : syracuseStep 13064327 = 19596491) B19596491
theorem B8709551 : Blo 1907435 8709551 := bstep (se 1 (by rfl) ⟨6532163, by rfl⟩ : syracuseStep 8709551 = 13064327) B13064327
theorem B5806367 : Blo 1907435 5806367 := bstep (se 1 (by rfl) ⟨4354775, by rfl⟩ : syracuseStep 5806367 = 8709551) B8709551
theorem B3870911 : Blo 1907435 3870911 := bstep (se 1 (by rfl) ⟨2903183, by rfl⟩ : syracuseStep 3870911 = 5806367) B5806367
theorem B2580607 : Blo 1907435 2580607 := bstep (se 1 (by rfl) ⟨1935455, by rfl⟩ : syracuseStep 2580607 = 3870911) B3870911
theorem B3440809 : Blo 1907435 3440809 := bstep (se 2 (by rfl) ⟨1290303, by rfl⟩ : syracuseStep 3440809 = 2580607) B2580607
theorem B18350981 : Blo 1907435 18350981 := bstep (se 4 (by rfl) ⟨1720404, by rfl⟩ : syracuseStep 18350981 = 3440809) B3440809
theorem B12233987 : Blo 1907435 12233987 := bstep (se 1 (by rfl) ⟨9175490, by rfl⟩ : syracuseStep 12233987 = 18350981) B18350981
theorem B8155991 : Blo 1907435 8155991 := bstep (se 1 (by rfl) ⟨6116993, by rfl⟩ : syracuseStep 8155991 = 12233987) B12233987
theorem B5437327 : Blo 1907435 5437327 := bstep (se 1 (by rfl) ⟨4077995, by rfl⟩ : syracuseStep 5437327 = 8155991) B8155991
theorem B7249769 : Blo 1907435 7249769 := bstep (se 2 (by rfl) ⟨2718663, by rfl⟩ : syracuseStep 7249769 = 5437327) B5437327
theorem B4833179 : Blo 1907435 4833179 := bstep (se 1 (by rfl) ⟨3624884, by rfl⟩ : syracuseStep 4833179 = 7249769) B7249769
theorem B3222119 : Blo 1907435 3222119 := bstep (se 1 (by rfl) ⟨2416589, by rfl⟩ : syracuseStep 3222119 = 4833179) B4833179
theorem B2148079 : Blo 1907435 2148079 := bstep (se 1 (by rfl) ⟨1611059, by rfl⟩ : syracuseStep 2148079 = 3222119) B3222119
theorem B2864105 : Blo 1907435 2864105 := bstep (se 2 (by rfl) ⟨1074039, by rfl⟩ : syracuseStep 2864105 = 2148079) B2148079
theorem B1909403 : Blo 1907435 1909403 := bstep (se 1 (by rfl) ⟨1432052, by rfl⟩ : syracuseStep 1909403 = 2864105) B2864105
theorem B2293877 : Blo 1907435 2293877 := bbase (se 5 (by rfl) ⟨107525, by rfl⟩ : syracuseStep 2293877 = 215051) (by norm_num)
theorem B6117005 : Blo 1907435 6117005 := bstep (se 3 (by rfl) ⟨1146938, by rfl⟩ : syracuseStep 6117005 = 2293877) B2293877
theorem B16312013 : Blo 1907435 16312013 := bstep (se 3 (by rfl) ⟨3058502, by rfl⟩ : syracuseStep 16312013 = 6117005) B6117005
theorem B10874675 : Blo 1907435 10874675 := bstep (se 1 (by rfl) ⟨8156006, by rfl⟩ : syracuseStep 10874675 = 16312013) B16312013
theorem B7249783 : Blo 1907435 7249783 := bstep (se 1 (by rfl) ⟨5437337, by rfl⟩ : syracuseStep 7249783 = 10874675) B10874675
theorem B9666377 : Blo 1907435 9666377 := bstep (se 2 (by rfl) ⟨3624891, by rfl⟩ : syracuseStep 9666377 = 7249783) B7249783
theorem B6444251 : Blo 1907435 6444251 := bstep (se 1 (by rfl) ⟨4833188, by rfl⟩ : syracuseStep 6444251 = 9666377) B9666377
theorem B4296167 : Blo 1907435 4296167 := bstep (se 1 (by rfl) ⟨3222125, by rfl⟩ : syracuseStep 4296167 = 6444251) B6444251
theorem B2864111 : Blo 1907435 2864111 := bstep (se 1 (by rfl) ⟨2148083, by rfl⟩ : syracuseStep 2864111 = 4296167) B4296167
theorem B1909407 : Blo 1907435 1909407 := bstep (se 1 (by rfl) ⟨1432055, by rfl⟩ : syracuseStep 1909407 = 2864111) B2864111
theorem B2864117 : Blo 1907435 2864117 := bbase (se 5 (by rfl) ⟨134255, by rfl⟩ : syracuseStep 2864117 = 268511) (by norm_num)
theorem B1909411 : Blo 1907435 1909411 := bstep (se 1 (by rfl) ⟨1432058, by rfl⟩ : syracuseStep 1909411 = 2864117) B2864117
theorem B4078021 : Blo 1907435 4078021 := bbase (se 4 (by rfl) ⟨382314, by rfl⟩ : syracuseStep 4078021 = 764629) (by norm_num)
theorem B5437361 : Blo 1907435 5437361 := bstep (se 2 (by rfl) ⟨2039010, by rfl⟩ : syracuseStep 5437361 = 4078021) B4078021
theorem B3624907 : Blo 1907435 3624907 := bstep (se 1 (by rfl) ⟨2718680, by rfl⟩ : syracuseStep 3624907 = 5437361) B5437361
theorem B4833209 : Blo 1907435 4833209 := bstep (se 2 (by rfl) ⟨1812453, by rfl⟩ : syracuseStep 4833209 = 3624907) B3624907
theorem B3222139 : Blo 1907435 3222139 := bstep (se 1 (by rfl) ⟨2416604, by rfl⟩ : syracuseStep 3222139 = 4833209) B4833209
theorem B4296185 : Blo 1907435 4296185 := bstep (se 2 (by rfl) ⟨1611069, by rfl⟩ : syracuseStep 4296185 = 3222139) B3222139
theorem B2864123 : Blo 1907435 2864123 := bstep (se 1 (by rfl) ⟨2148092, by rfl⟩ : syracuseStep 2864123 = 4296185) B4296185
theorem B1909415 : Blo 1907435 1909415 := bstep (se 1 (by rfl) ⟨1432061, by rfl⟩ : syracuseStep 1909415 = 2864123) B2864123
theorem B2148097 : Blo 1907435 2148097 := bbase (se 2 (by rfl) ⟨805536, by rfl⟩ : syracuseStep 2148097 = 1611073) (by norm_num)
theorem B2864129 : Blo 1907435 2864129 := bstep (se 2 (by rfl) ⟨1074048, by rfl⟩ : syracuseStep 2864129 = 2148097) B2148097
theorem B1909419 : Blo 1907435 1909419 := bstep (se 1 (by rfl) ⟨1432064, by rfl⟩ : syracuseStep 1909419 = 2864129) B2864129
theorem B4833229 : Blo 1907435 4833229 := bbase (se 3 (by rfl) ⟨906230, by rfl⟩ : syracuseStep 4833229 = 1812461) (by norm_num)
theorem B6444305 : Blo 1907435 6444305 := bstep (se 2 (by rfl) ⟨2416614, by rfl⟩ : syracuseStep 6444305 = 4833229) B4833229
theorem B4296203 : Blo 1907435 4296203 := bstep (se 1 (by rfl) ⟨3222152, by rfl⟩ : syracuseStep 4296203 = 6444305) B6444305
theorem B2864135 : Blo 1907435 2864135 := bstep (se 1 (by rfl) ⟨2148101, by rfl⟩ : syracuseStep 2864135 = 4296203) B4296203
theorem B1909423 : Blo 1907435 1909423 := bstep (se 1 (by rfl) ⟨1432067, by rfl⟩ : syracuseStep 1909423 = 2864135) B2864135
theorem B2864141 : Blo 1907435 2864141 := bbase (se 3 (by rfl) ⟨537026, by rfl⟩ : syracuseStep 2864141 = 1074053) (by norm_num)
theorem B1909427 : Blo 1907435 1909427 := bstep (se 1 (by rfl) ⟨1432070, by rfl⟩ : syracuseStep 1909427 = 2864141) B2864141
theorem B4296221 : Blo 1907435 4296221 := bbase (se 3 (by rfl) ⟨805541, by rfl⟩ : syracuseStep 4296221 = 1611083) (by norm_num)
theorem B2864147 : Blo 1907435 2864147 := bstep (se 1 (by rfl) ⟨2148110, by rfl⟩ : syracuseStep 2864147 = 4296221) B4296221
theorem B1909431 : Blo 1907435 1909431 := bstep (se 1 (by rfl) ⟨1432073, by rfl⟩ : syracuseStep 1909431 = 2864147) B2864147
theorem B3222173 : Blo 1907435 3222173 := bbase (se 3 (by rfl) ⟨604157, by rfl⟩ : syracuseStep 3222173 = 1208315) (by norm_num)
theorem B2148115 : Blo 1907435 2148115 := bstep (se 1 (by rfl) ⟨1611086, by rfl⟩ : syracuseStep 2148115 = 3222173) B3222173
theorem B2864153 : Blo 1907435 2864153 := bstep (se 2 (by rfl) ⟨1074057, by rfl⟩ : syracuseStep 2864153 = 2148115) B2148115
theorem B1909435 : Blo 1907435 1909435 := bstep (se 1 (by rfl) ⟨1432076, by rfl⟩ : syracuseStep 1909435 = 2864153) B2864153
theorem C0 (j : ℕ) (h1 : 476858 ≤ j) (h2 : j ≤ 477358) : Blo 1907435 (4 * j + 3) := by
  interval_cases j
  · exact B1907435
  · exact B1907439
  · exact B1907443
  · exact B1907447
  · exact B1907451
  · exact B1907455
  · exact B1907459
  · exact B1907463
  · exact B1907467
  · exact B1907471
  · exact B1907475
  · exact B1907479
  · exact B1907483
  · exact B1907487
  · exact B1907491
  · exact B1907495
  · exact B1907499
  · exact B1907503
  · exact B1907507
  · exact B1907511
  · exact B1907515
  · exact B1907519
  · exact B1907523
  · exact B1907527
  · exact B1907531
  · exact B1907535
  · exact B1907539
  · exact B1907543
  · exact B1907547
  · exact B1907551
  · exact B1907555
  · exact B1907559
  · exact B1907563
  · exact B1907567
  · exact B1907571
  · exact B1907575
  · exact B1907579
  · exact B1907583
  · exact B1907587
  · exact B1907591
  · exact B1907595
  · exact B1907599
  · exact B1907603
  · exact B1907607
  · exact B1907611
  · exact B1907615
  · exact B1907619
  · exact B1907623
  · exact B1907627
  · exact B1907631
  · exact B1907635
  · exact B1907639
  · exact B1907643
  · exact B1907647
  · exact B1907651
  · exact B1907655
  · exact B1907659
  · exact B1907663
  · exact B1907667
  · exact B1907671
  · exact B1907675
  · exact B1907679
  · exact B1907683
  · exact B1907687
  · exact B1907691
  · exact B1907695
  · exact B1907699
  · exact B1907703
  · exact B1907707
  · exact B1907711
  · exact B1907715
  · exact B1907719
  · exact B1907723
  · exact B1907727
  · exact B1907731
  · exact B1907735
  · exact B1907739
  · exact B1907743
  · exact B1907747
  · exact B1907751
  · exact B1907755
  · exact B1907759
  · exact B1907763
  · exact B1907767
  · exact B1907771
  · exact B1907775
  · exact B1907779
  · exact B1907783
  · exact B1907787
  · exact B1907791
  · exact B1907795
  · exact B1907799
  · exact B1907803
  · exact B1907807
  · exact B1907811
  · exact B1907815
  · exact B1907819
  · exact B1907823
  · exact B1907827
  · exact B1907831
  · exact B1907835
  · exact B1907839
  · exact B1907843
  · exact B1907847
  · exact B1907851
  · exact B1907855
  · exact B1907859
  · exact B1907863
  · exact B1907867
  · exact B1907871
  · exact B1907875
  · exact B1907879
  · exact B1907883
  · exact B1907887
  · exact B1907891
  · exact B1907895
  · exact B1907899
  · exact B1907903
  · exact B1907907
  · exact B1907911
  · exact B1907915
  · exact B1907919
  · exact B1907923
  · exact B1907927
  · exact B1907931
  · exact B1907935
  · exact B1907939
  · exact B1907943
  · exact B1907947
  · exact B1907951
  · exact B1907955
  · exact B1907959
  · exact B1907963
  · exact B1907967
  · exact B1907971
  · exact B1907975
  · exact B1907979
  · exact B1907983
  · exact B1907987
  · exact B1907991
  · exact B1907995
  · exact B1907999
  · exact B1908003
  · exact B1908007
  · exact B1908011
  · exact B1908015
  · exact B1908019
  · exact B1908023
  · exact B1908027
  · exact B1908031
  · exact B1908035
  · exact B1908039
  · exact B1908043
  · exact B1908047
  · exact B1908051
  · exact B1908055
  · exact B1908059
  · exact B1908063
  · exact B1908067
  · exact B1908071
  · exact B1908075
  · exact B1908079
  · exact B1908083
  · exact B1908087
  · exact B1908091
  · exact B1908095
  · exact B1908099
  · exact B1908103
  · exact B1908107
  · exact B1908111
  · exact B1908115
  · exact B1908119
  · exact B1908123
  · exact B1908127
  · exact B1908131
  · exact B1908135
  · exact B1908139
  · exact B1908143
  · exact B1908147
  · exact B1908151
  · exact B1908155
  · exact B1908159
  · exact B1908163
  · exact B1908167
  · exact B1908171
  · exact B1908175
  · exact B1908179
  · exact B1908183
  · exact B1908187
  · exact B1908191
  · exact B1908195
  · exact B1908199
  · exact B1908203
  · exact B1908207
  · exact B1908211
  · exact B1908215
  · exact B1908219
  · exact B1908223
  · exact B1908227
  · exact B1908231
  · exact B1908235
  · exact B1908239
  · exact B1908243
  · exact B1908247
  · exact B1908251
  · exact B1908255
  · exact B1908259
  · exact B1908263
  · exact B1908267
  · exact B1908271
  · exact B1908275
  · exact B1908279
  · exact B1908283
  · exact B1908287
  · exact B1908291
  · exact B1908295
  · exact B1908299
  · exact B1908303
  · exact B1908307
  · exact B1908311
  · exact B1908315
  · exact B1908319
  · exact B1908323
  · exact B1908327
  · exact B1908331
  · exact B1908335
  · exact B1908339
  · exact B1908343
  · exact B1908347
  · exact B1908351
  · exact B1908355
  · exact B1908359
  · exact B1908363
  · exact B1908367
  · exact B1908371
  · exact B1908375
  · exact B1908379
  · exact B1908383
  · exact B1908387
  · exact B1908391
  · exact B1908395
  · exact B1908399
  · exact B1908403
  · exact B1908407
  · exact B1908411
  · exact B1908415
  · exact B1908419
  · exact B1908423
  · exact B1908427
  · exact B1908431
  · exact B1908435
  · exact B1908439
  · exact B1908443
  · exact B1908447
  · exact B1908451
  · exact B1908455
  · exact B1908459
  · exact B1908463
  · exact B1908467
  · exact B1908471
  · exact B1908475
  · exact B1908479
  · exact B1908483
  · exact B1908487
  · exact B1908491
  · exact B1908495
  · exact B1908499
  · exact B1908503
  · exact B1908507
  · exact B1908511
  · exact B1908515
  · exact B1908519
  · exact B1908523
  · exact B1908527
  · exact B1908531
  · exact B1908535
  · exact B1908539
  · exact B1908543
  · exact B1908547
  · exact B1908551
  · exact B1908555
  · exact B1908559
  · exact B1908563
  · exact B1908567
  · exact B1908571
  · exact B1908575
  · exact B1908579
  · exact B1908583
  · exact B1908587
  · exact B1908591
  · exact B1908595
  · exact B1908599
  · exact B1908603
  · exact B1908607
  · exact B1908611
  · exact B1908615
  · exact B1908619
  · exact B1908623
  · exact B1908627
  · exact B1908631
  · exact B1908635
  · exact B1908639
  · exact B1908643
  · exact B1908647
  · exact B1908651
  · exact B1908655
  · exact B1908659
  · exact B1908663
  · exact B1908667
  · exact B1908671
  · exact B1908675
  · exact B1908679
  · exact B1908683
  · exact B1908687
  · exact B1908691
  · exact B1908695
  · exact B1908699
  · exact B1908703
  · exact B1908707
  · exact B1908711
  · exact B1908715
  · exact B1908719
  · exact B1908723
  · exact B1908727
  · exact B1908731
  · exact B1908735
  · exact B1908739
  · exact B1908743
  · exact B1908747
  · exact B1908751
  · exact B1908755
  · exact B1908759
  · exact B1908763
  · exact B1908767
  · exact B1908771
  · exact B1908775
  · exact B1908779
  · exact B1908783
  · exact B1908787
  · exact B1908791
  · exact B1908795
  · exact B1908799
  · exact B1908803
  · exact B1908807
  · exact B1908811
  · exact B1908815
  · exact B1908819
  · exact B1908823
  · exact B1908827
  · exact B1908831
  · exact B1908835
  · exact B1908839
  · exact B1908843
  · exact B1908847
  · exact B1908851
  · exact B1908855
  · exact B1908859
  · exact B1908863
  · exact B1908867
  · exact B1908871
  · exact B1908875
  · exact B1908879
  · exact B1908883
  · exact B1908887
  · exact B1908891
  · exact B1908895
  · exact B1908899
  · exact B1908903
  · exact B1908907
  · exact B1908911
  · exact B1908915
  · exact B1908919
  · exact B1908923
  · exact B1908927
  · exact B1908931
  · exact B1908935
  · exact B1908939
  · exact B1908943
  · exact B1908947
  · exact B1908951
  · exact B1908955
  · exact B1908959
  · exact B1908963
  · exact B1908967
  · exact B1908971
  · exact B1908975
  · exact B1908979
  · exact B1908983
  · exact B1908987
  · exact B1908991
  · exact B1908995
  · exact B1908999
  · exact B1909003
  · exact B1909007
  · exact B1909011
  · exact B1909015
  · exact B1909019
  · exact B1909023
  · exact B1909027
  · exact B1909031
  · exact B1909035
  · exact B1909039
  · exact B1909043
  · exact B1909047
  · exact B1909051
  · exact B1909055
  · exact B1909059
  · exact B1909063
  · exact B1909067
  · exact B1909071
  · exact B1909075
  · exact B1909079
  · exact B1909083
  · exact B1909087
  · exact B1909091
  · exact B1909095
  · exact B1909099
  · exact B1909103
  · exact B1909107
  · exact B1909111
  · exact B1909115
  · exact B1909119
  · exact B1909123
  · exact B1909127
  · exact B1909131
  · exact B1909135
  · exact B1909139
  · exact B1909143
  · exact B1909147
  · exact B1909151
  · exact B1909155
  · exact B1909159
  · exact B1909163
  · exact B1909167
  · exact B1909171
  · exact B1909175
  · exact B1909179
  · exact B1909183
  · exact B1909187
  · exact B1909191
  · exact B1909195
  · exact B1909199
  · exact B1909203
  · exact B1909207
  · exact B1909211
  · exact B1909215
  · exact B1909219
  · exact B1909223
  · exact B1909227
  · exact B1909231
  · exact B1909235
  · exact B1909239
  · exact B1909243
  · exact B1909247
  · exact B1909251
  · exact B1909255
  · exact B1909259
  · exact B1909263
  · exact B1909267
  · exact B1909271
  · exact B1909275
  · exact B1909279
  · exact B1909283
  · exact B1909287
  · exact B1909291
  · exact B1909295
  · exact B1909299
  · exact B1909303
  · exact B1909307
  · exact B1909311
  · exact B1909315
  · exact B1909319
  · exact B1909323
  · exact B1909327
  · exact B1909331
  · exact B1909335
  · exact B1909339
  · exact B1909343
  · exact B1909347
  · exact B1909351
  · exact B1909355
  · exact B1909359
  · exact B1909363
  · exact B1909367
  · exact B1909371
  · exact B1909375
  · exact B1909379
  · exact B1909383
  · exact B1909387
  · exact B1909391
  · exact B1909395
  · exact B1909399
  · exact B1909403
  · exact B1909407
  · exact B1909411
  · exact B1909415
  · exact B1909419
  · exact B1909423
  · exact B1909427
  · exact B1909431
  · exact B1909435
theorem solution (m : ℕ) (hlo : 1907435 ≤ m) (hhi : m ≤ 1909435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 476858 ≤ j := by omega
    have hj2 : j ≤ 477358 := by omega
    have hb : Blo 1907435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
