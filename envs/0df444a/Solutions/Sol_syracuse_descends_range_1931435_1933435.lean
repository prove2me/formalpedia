-- Prove2me | solution 1 for syracuse_descends_range_1931435_1933435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:22.358403+00:00
-- url     : https://prove2.me/submissions/e23b50e0-a5a1-4c17-be22-9f3a1ee4a046

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

theorem B2172865 : Blo 1931435 2172865 := bbase (se 2 (by rfl) ⟨814824, by rfl⟩ : syracuseStep 2172865 = 1629649) (by norm_num)
theorem B2897153 : Blo 1931435 2897153 := bstep (se 2 (by rfl) ⟨1086432, by rfl⟩ : syracuseStep 2897153 = 2172865) B2172865
theorem B1931435 : Blo 1931435 1931435 := bstep (se 1 (by rfl) ⟨1448576, by rfl⟩ : syracuseStep 1931435 = 2897153) B2897153
theorem B4888957 : Blo 1931435 4888957 := bbase (se 3 (by rfl) ⟨916679, by rfl⟩ : syracuseStep 4888957 = 1833359) (by norm_num)
theorem B6518609 : Blo 1931435 6518609 := bstep (se 2 (by rfl) ⟨2444478, by rfl⟩ : syracuseStep 6518609 = 4888957) B4888957
theorem B4345739 : Blo 1931435 4345739 := bstep (se 1 (by rfl) ⟨3259304, by rfl⟩ : syracuseStep 4345739 = 6518609) B6518609
theorem B2897159 : Blo 1931435 2897159 := bstep (se 1 (by rfl) ⟨2172869, by rfl⟩ : syracuseStep 2897159 = 4345739) B4345739
theorem B1931439 : Blo 1931435 1931439 := bstep (se 1 (by rfl) ⟨1448579, by rfl⟩ : syracuseStep 1931439 = 2897159) B2897159
theorem B2897165 : Blo 1931435 2897165 := bbase (se 3 (by rfl) ⟨543218, by rfl⟩ : syracuseStep 2897165 = 1086437) (by norm_num)
theorem B1931443 : Blo 1931435 1931443 := bstep (se 1 (by rfl) ⟨1448582, by rfl⟩ : syracuseStep 1931443 = 2897165) B2897165
theorem B4345757 : Blo 1931435 4345757 := bbase (se 3 (by rfl) ⟨814829, by rfl⟩ : syracuseStep 4345757 = 1629659) (by norm_num)
theorem B2897171 : Blo 1931435 2897171 := bstep (se 1 (by rfl) ⟨2172878, by rfl⟩ : syracuseStep 2897171 = 4345757) B4345757
theorem B1931447 : Blo 1931435 1931447 := bstep (se 1 (by rfl) ⟨1448585, by rfl⟩ : syracuseStep 1931447 = 2897171) B2897171
theorem B3259325 : Blo 1931435 3259325 := bbase (se 3 (by rfl) ⟨611123, by rfl⟩ : syracuseStep 3259325 = 1222247) (by norm_num)
theorem B2172883 : Blo 1931435 2172883 := bstep (se 1 (by rfl) ⟨1629662, by rfl⟩ : syracuseStep 2172883 = 3259325) B3259325
theorem B2897177 : Blo 1931435 2897177 := bstep (se 2 (by rfl) ⟨1086441, by rfl⟩ : syracuseStep 2897177 = 2172883) B2172883
theorem B1931451 : Blo 1931435 1931451 := bstep (se 1 (by rfl) ⟨1448588, by rfl⟩ : syracuseStep 1931451 = 2897177) B2897177
theorem B11000245 : Blo 1931435 11000245 := bbase (se 5 (by rfl) ⟨515636, by rfl⟩ : syracuseStep 11000245 = 1031273) (by norm_num)
theorem B14666993 : Blo 1931435 14666993 := bstep (se 2 (by rfl) ⟨5500122, by rfl⟩ : syracuseStep 14666993 = 11000245) B11000245
theorem B9777995 : Blo 1931435 9777995 := bstep (se 1 (by rfl) ⟨7333496, by rfl⟩ : syracuseStep 9777995 = 14666993) B14666993
theorem B6518663 : Blo 1931435 6518663 := bstep (se 1 (by rfl) ⟨4888997, by rfl⟩ : syracuseStep 6518663 = 9777995) B9777995
theorem B4345775 : Blo 1931435 4345775 := bstep (se 1 (by rfl) ⟨3259331, by rfl⟩ : syracuseStep 4345775 = 6518663) B6518663
theorem B2897183 : Blo 1931435 2897183 := bstep (se 1 (by rfl) ⟨2172887, by rfl⟩ : syracuseStep 2897183 = 4345775) B4345775
theorem B1931455 : Blo 1931435 1931455 := bstep (se 1 (by rfl) ⟨1448591, by rfl⟩ : syracuseStep 1931455 = 2897183) B2897183
theorem B2897189 : Blo 1931435 2897189 := bbase (se 4 (by rfl) ⟨271611, by rfl⟩ : syracuseStep 2897189 = 543223) (by norm_num)
theorem B1931459 : Blo 1931435 1931459 := bstep (se 1 (by rfl) ⟨1448594, by rfl⟩ : syracuseStep 1931459 = 2897189) B2897189
theorem B2444509 : Blo 1931435 2444509 := bbase (se 3 (by rfl) ⟨458345, by rfl⟩ : syracuseStep 2444509 = 916691) (by norm_num)
theorem B3259345 : Blo 1931435 3259345 := bstep (se 2 (by rfl) ⟨1222254, by rfl⟩ : syracuseStep 3259345 = 2444509) B2444509
theorem B4345793 : Blo 1931435 4345793 := bstep (se 2 (by rfl) ⟨1629672, by rfl⟩ : syracuseStep 4345793 = 3259345) B3259345
theorem B2897195 : Blo 1931435 2897195 := bstep (se 1 (by rfl) ⟨2172896, by rfl⟩ : syracuseStep 2897195 = 4345793) B4345793
theorem B1931463 : Blo 1931435 1931463 := bstep (se 1 (by rfl) ⟨1448597, by rfl⟩ : syracuseStep 1931463 = 2897195) B2897195
theorem B2172901 : Blo 1931435 2172901 := bbase (se 4 (by rfl) ⟨203709, by rfl⟩ : syracuseStep 2172901 = 407419) (by norm_num)
theorem B2897201 : Blo 1931435 2897201 := bstep (se 2 (by rfl) ⟨1086450, by rfl⟩ : syracuseStep 2897201 = 2172901) B2172901
theorem B1931467 : Blo 1931435 1931467 := bstep (se 1 (by rfl) ⟨1448600, by rfl⟩ : syracuseStep 1931467 = 2897201) B2897201
theorem B2202553 : Blo 1931435 2202553 := bbase (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) (by norm_num)
theorem B2936737 : Blo 1931435 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B3915649 : Blo 1931435 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B5220865 : Blo 1931435 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B6961153 : Blo 1931435 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B9281537 : Blo 1931435 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B6187691 : Blo 1931435 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B4125127 : Blo 1931435 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B5500169 : Blo 1931435 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B3666779 : Blo 1931435 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B2444519 : Blo 1931435 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B6518717 : Blo 1931435 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B4345811 : Blo 1931435 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B2897207 : Blo 1931435 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B1931471 : Blo 1931435 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B2897213 : Blo 1931435 2897213 := bbase (se 3 (by rfl) ⟨543227, by rfl⟩ : syracuseStep 2897213 = 1086455) (by norm_num)
theorem B1931475 : Blo 1931435 1931475 := bstep (se 1 (by rfl) ⟨1448606, by rfl⟩ : syracuseStep 1931475 = 2897213) B2897213
theorem B4345829 : Blo 1931435 4345829 := bbase (se 4 (by rfl) ⟨407421, by rfl⟩ : syracuseStep 4345829 = 814843) (by norm_num)
theorem B2897219 : Blo 1931435 2897219 := bstep (se 1 (by rfl) ⟨2172914, by rfl⟩ : syracuseStep 2897219 = 4345829) B4345829
theorem B1931479 : Blo 1931435 1931479 := bstep (se 1 (by rfl) ⟨1448609, by rfl⟩ : syracuseStep 1931479 = 2897219) B2897219
theorem B4889069 : Blo 1931435 4889069 := bbase (se 3 (by rfl) ⟨916700, by rfl⟩ : syracuseStep 4889069 = 1833401) (by norm_num)
theorem B3259379 : Blo 1931435 3259379 := bstep (se 1 (by rfl) ⟨2444534, by rfl⟩ : syracuseStep 3259379 = 4889069) B4889069
theorem B2172919 : Blo 1931435 2172919 := bstep (se 1 (by rfl) ⟨1629689, by rfl⟩ : syracuseStep 2172919 = 3259379) B3259379
theorem B2897225 : Blo 1931435 2897225 := bstep (se 2 (by rfl) ⟨1086459, by rfl⟩ : syracuseStep 2897225 = 2172919) B2172919
theorem B1931483 : Blo 1931435 1931483 := bstep (se 1 (by rfl) ⟨1448612, by rfl⟩ : syracuseStep 1931483 = 2897225) B2897225
theorem B2477893 : Blo 1931435 2477893 := bbase (se 4 (by rfl) ⟨232302, by rfl⟩ : syracuseStep 2477893 = 464605) (by norm_num)
theorem B3303857 : Blo 1931435 3303857 := bstep (se 2 (by rfl) ⟨1238946, by rfl⟩ : syracuseStep 3303857 = 2477893) B2477893
theorem B2202571 : Blo 1931435 2202571 := bstep (se 1 (by rfl) ⟨1651928, by rfl⟩ : syracuseStep 2202571 = 3303857) B3303857
theorem B11747045 : Blo 1931435 11747045 := bstep (se 4 (by rfl) ⟨1101285, by rfl⟩ : syracuseStep 11747045 = 2202571) B2202571
theorem B7831363 : Blo 1931435 7831363 := bstep (se 1 (by rfl) ⟨5873522, by rfl⟩ : syracuseStep 7831363 = 11747045) B11747045
theorem B10441817 : Blo 1931435 10441817 := bstep (se 2 (by rfl) ⟨3915681, by rfl⟩ : syracuseStep 10441817 = 7831363) B7831363
theorem B6961211 : Blo 1931435 6961211 := bstep (se 1 (by rfl) ⟨5220908, by rfl⟩ : syracuseStep 6961211 = 10441817) B10441817
theorem B4640807 : Blo 1931435 4640807 := bstep (se 1 (by rfl) ⟨3480605, by rfl⟩ : syracuseStep 4640807 = 6961211) B6961211
theorem B3093871 : Blo 1931435 3093871 := bstep (se 1 (by rfl) ⟨2320403, by rfl⟩ : syracuseStep 3093871 = 4640807) B4640807
theorem B4125161 : Blo 1931435 4125161 := bstep (se 2 (by rfl) ⟨1546935, by rfl⟩ : syracuseStep 4125161 = 3093871) B3093871
theorem B2750107 : Blo 1931435 2750107 := bstep (se 1 (by rfl) ⟨2062580, by rfl⟩ : syracuseStep 2750107 = 4125161) B4125161
theorem B3666809 : Blo 1931435 3666809 := bstep (se 2 (by rfl) ⟨1375053, by rfl⟩ : syracuseStep 3666809 = 2750107) B2750107
theorem B9778157 : Blo 1931435 9778157 := bstep (se 3 (by rfl) ⟨1833404, by rfl⟩ : syracuseStep 9778157 = 3666809) B3666809
theorem B6518771 : Blo 1931435 6518771 := bstep (se 1 (by rfl) ⟨4889078, by rfl⟩ : syracuseStep 6518771 = 9778157) B9778157
theorem B4345847 : Blo 1931435 4345847 := bstep (se 1 (by rfl) ⟨3259385, by rfl⟩ : syracuseStep 4345847 = 6518771) B6518771
theorem B2897231 : Blo 1931435 2897231 := bstep (se 1 (by rfl) ⟨2172923, by rfl⟩ : syracuseStep 2897231 = 4345847) B4345847
theorem B1931487 : Blo 1931435 1931487 := bstep (se 1 (by rfl) ⟨1448615, by rfl⟩ : syracuseStep 1931487 = 2897231) B2897231
theorem B2897237 : Blo 1931435 2897237 := bbase (se 13 (by rfl) ⟨530, by rfl⟩ : syracuseStep 2897237 = 1061) (by norm_num)
theorem B1931491 : Blo 1931435 1931491 := bstep (se 1 (by rfl) ⟨1448618, by rfl⟩ : syracuseStep 1931491 = 2897237) B2897237
theorem B2062589 : Blo 1931435 2062589 := bbase (se 3 (by rfl) ⟨386735, by rfl⟩ : syracuseStep 2062589 = 773471) (by norm_num)
theorem B5500237 : Blo 1931435 5500237 := bstep (se 3 (by rfl) ⟨1031294, by rfl⟩ : syracuseStep 5500237 = 2062589) B2062589
theorem B7333649 : Blo 1931435 7333649 := bstep (se 2 (by rfl) ⟨2750118, by rfl⟩ : syracuseStep 7333649 = 5500237) B5500237
theorem B4889099 : Blo 1931435 4889099 := bstep (se 1 (by rfl) ⟨3666824, by rfl⟩ : syracuseStep 4889099 = 7333649) B7333649
theorem B3259399 : Blo 1931435 3259399 := bstep (se 1 (by rfl) ⟨2444549, by rfl⟩ : syracuseStep 3259399 = 4889099) B4889099
theorem B4345865 : Blo 1931435 4345865 := bstep (se 2 (by rfl) ⟨1629699, by rfl⟩ : syracuseStep 4345865 = 3259399) B3259399
theorem B2897243 : Blo 1931435 2897243 := bstep (se 1 (by rfl) ⟨2172932, by rfl⟩ : syracuseStep 2897243 = 4345865) B4345865
theorem B1931495 : Blo 1931435 1931495 := bstep (se 1 (by rfl) ⟨1448621, by rfl⟩ : syracuseStep 1931495 = 2897243) B2897243
theorem B2172937 : Blo 1931435 2172937 := bbase (se 2 (by rfl) ⟨814851, by rfl⟩ : syracuseStep 2172937 = 1629703) (by norm_num)
theorem B2897249 : Blo 1931435 2897249 := bstep (se 2 (by rfl) ⟨1086468, by rfl⟩ : syracuseStep 2897249 = 2172937) B2172937
theorem B1931499 : Blo 1931435 1931499 := bstep (se 1 (by rfl) ⟨1448624, by rfl⟩ : syracuseStep 1931499 = 2897249) B2897249
theorem B2202589 : Blo 1931435 2202589 := bbase (se 3 (by rfl) ⟨412985, by rfl⟩ : syracuseStep 2202589 = 825971) (by norm_num)
theorem B2936785 : Blo 1931435 2936785 := bstep (se 2 (by rfl) ⟨1101294, by rfl⟩ : syracuseStep 2936785 = 2202589) B2202589
theorem B3915713 : Blo 1931435 3915713 := bstep (se 2 (by rfl) ⟨1468392, by rfl⟩ : syracuseStep 3915713 = 2936785) B2936785
theorem B2610475 : Blo 1931435 2610475 := bstep (se 1 (by rfl) ⟨1957856, by rfl⟩ : syracuseStep 2610475 = 3915713) B3915713
theorem B13922533 : Blo 1931435 13922533 := bstep (se 4 (by rfl) ⟨1305237, by rfl⟩ : syracuseStep 13922533 = 2610475) B2610475
theorem B18563377 : Blo 1931435 18563377 := bstep (se 2 (by rfl) ⟨6961266, by rfl⟩ : syracuseStep 18563377 = 13922533) B13922533
theorem B24751169 : Blo 1931435 24751169 := bstep (se 2 (by rfl) ⟨9281688, by rfl⟩ : syracuseStep 24751169 = 18563377) B18563377
theorem B16500779 : Blo 1931435 16500779 := bstep (se 1 (by rfl) ⟨12375584, by rfl⟩ : syracuseStep 16500779 = 24751169) B24751169
theorem B11000519 : Blo 1931435 11000519 := bstep (se 1 (by rfl) ⟨8250389, by rfl⟩ : syracuseStep 11000519 = 16500779) B16500779
theorem B7333679 : Blo 1931435 7333679 := bstep (se 1 (by rfl) ⟨5500259, by rfl⟩ : syracuseStep 7333679 = 11000519) B11000519
theorem B4889119 : Blo 1931435 4889119 := bstep (se 1 (by rfl) ⟨3666839, by rfl⟩ : syracuseStep 4889119 = 7333679) B7333679
theorem B6518825 : Blo 1931435 6518825 := bstep (se 2 (by rfl) ⟨2444559, by rfl⟩ : syracuseStep 6518825 = 4889119) B4889119
theorem B4345883 : Blo 1931435 4345883 := bstep (se 1 (by rfl) ⟨3259412, by rfl⟩ : syracuseStep 4345883 = 6518825) B6518825
theorem B2897255 : Blo 1931435 2897255 := bstep (se 1 (by rfl) ⟨2172941, by rfl⟩ : syracuseStep 2897255 = 4345883) B4345883
theorem B1931503 : Blo 1931435 1931503 := bstep (se 1 (by rfl) ⟨1448627, by rfl⟩ : syracuseStep 1931503 = 2897255) B2897255
theorem B2897261 : Blo 1931435 2897261 := bbase (se 3 (by rfl) ⟨543236, by rfl⟩ : syracuseStep 2897261 = 1086473) (by norm_num)
theorem B1931507 : Blo 1931435 1931507 := bstep (se 1 (by rfl) ⟨1448630, by rfl⟩ : syracuseStep 1931507 = 2897261) B2897261
theorem B4345901 : Blo 1931435 4345901 := bbase (se 3 (by rfl) ⟨814856, by rfl⟩ : syracuseStep 4345901 = 1629713) (by norm_num)
theorem B2897267 : Blo 1931435 2897267 := bstep (se 1 (by rfl) ⟨2172950, by rfl⟩ : syracuseStep 2897267 = 4345901) B4345901
theorem B1931511 : Blo 1931435 1931511 := bstep (se 1 (by rfl) ⟨1448633, by rfl⟩ : syracuseStep 1931511 = 2897267) B2897267
theorem B9281749 : Blo 1931435 9281749 := bbase (se 7 (by rfl) ⟨108770, by rfl⟩ : syracuseStep 9281749 = 217541) (by norm_num)
theorem B12375665 : Blo 1931435 12375665 := bstep (se 2 (by rfl) ⟨4640874, by rfl⟩ : syracuseStep 12375665 = 9281749) B9281749
theorem B8250443 : Blo 1931435 8250443 := bstep (se 1 (by rfl) ⟨6187832, by rfl⟩ : syracuseStep 8250443 = 12375665) B12375665
theorem B5500295 : Blo 1931435 5500295 := bstep (se 1 (by rfl) ⟨4125221, by rfl⟩ : syracuseStep 5500295 = 8250443) B8250443
theorem B3666863 : Blo 1931435 3666863 := bstep (se 1 (by rfl) ⟨2750147, by rfl⟩ : syracuseStep 3666863 = 5500295) B5500295
theorem B2444575 : Blo 1931435 2444575 := bstep (se 1 (by rfl) ⟨1833431, by rfl⟩ : syracuseStep 2444575 = 3666863) B3666863
theorem B3259433 : Blo 1931435 3259433 := bstep (se 2 (by rfl) ⟨1222287, by rfl⟩ : syracuseStep 3259433 = 2444575) B2444575
theorem B2172955 : Blo 1931435 2172955 := bstep (se 1 (by rfl) ⟨1629716, by rfl⟩ : syracuseStep 2172955 = 3259433) B3259433
theorem B2897273 : Blo 1931435 2897273 := bstep (se 2 (by rfl) ⟨1086477, by rfl⟩ : syracuseStep 2897273 = 2172955) B2172955
theorem B1931515 : Blo 1931435 1931515 := bstep (se 1 (by rfl) ⟨1448636, by rfl⟩ : syracuseStep 1931515 = 2897273) B2897273
theorem B9281765 : Blo 1931435 9281765 := bbase (se 4 (by rfl) ⟨870165, by rfl⟩ : syracuseStep 9281765 = 1740331) (by norm_num)
theorem B6187843 : Blo 1931435 6187843 := bstep (se 1 (by rfl) ⟨4640882, by rfl⟩ : syracuseStep 6187843 = 9281765) B9281765
theorem B33001829 : Blo 1931435 33001829 := bstep (se 4 (by rfl) ⟨3093921, by rfl⟩ : syracuseStep 33001829 = 6187843) B6187843
theorem B22001219 : Blo 1931435 22001219 := bstep (se 1 (by rfl) ⟨16500914, by rfl⟩ : syracuseStep 22001219 = 33001829) B33001829
theorem B14667479 : Blo 1931435 14667479 := bstep (se 1 (by rfl) ⟨11000609, by rfl⟩ : syracuseStep 14667479 = 22001219) B22001219
theorem B9778319 : Blo 1931435 9778319 := bstep (se 1 (by rfl) ⟨7333739, by rfl⟩ : syracuseStep 9778319 = 14667479) B14667479
theorem B6518879 : Blo 1931435 6518879 := bstep (se 1 (by rfl) ⟨4889159, by rfl⟩ : syracuseStep 6518879 = 9778319) B9778319
theorem B4345919 : Blo 1931435 4345919 := bstep (se 1 (by rfl) ⟨3259439, by rfl⟩ : syracuseStep 4345919 = 6518879) B6518879
theorem B2897279 : Blo 1931435 2897279 := bstep (se 1 (by rfl) ⟨2172959, by rfl⟩ : syracuseStep 2897279 = 4345919) B4345919
theorem B1931519 : Blo 1931435 1931519 := bstep (se 1 (by rfl) ⟨1448639, by rfl⟩ : syracuseStep 1931519 = 2897279) B2897279
theorem B2897285 : Blo 1931435 2897285 := bbase (se 4 (by rfl) ⟨271620, by rfl⟩ : syracuseStep 2897285 = 543241) (by norm_num)
theorem B1931523 : Blo 1931435 1931523 := bstep (se 1 (by rfl) ⟨1448642, by rfl⟩ : syracuseStep 1931523 = 2897285) B2897285
theorem B3259453 : Blo 1931435 3259453 := bbase (se 3 (by rfl) ⟨611147, by rfl⟩ : syracuseStep 3259453 = 1222295) (by norm_num)
theorem B4345937 : Blo 1931435 4345937 := bstep (se 2 (by rfl) ⟨1629726, by rfl⟩ : syracuseStep 4345937 = 3259453) B3259453
theorem B2897291 : Blo 1931435 2897291 := bstep (se 1 (by rfl) ⟨2172968, by rfl⟩ : syracuseStep 2897291 = 4345937) B4345937
theorem B1931527 : Blo 1931435 1931527 := bstep (se 1 (by rfl) ⟨1448645, by rfl⟩ : syracuseStep 1931527 = 2897291) B2897291
theorem B2172973 : Blo 1931435 2172973 := bbase (se 3 (by rfl) ⟨407432, by rfl⟩ : syracuseStep 2172973 = 814865) (by norm_num)
theorem B2897297 : Blo 1931435 2897297 := bstep (se 2 (by rfl) ⟨1086486, by rfl⟩ : syracuseStep 2897297 = 2172973) B2172973
theorem B1931531 : Blo 1931435 1931531 := bstep (se 1 (by rfl) ⟨1448648, by rfl⟩ : syracuseStep 1931531 = 2897297) B2897297
theorem B6518933 : Blo 1931435 6518933 := bbase (se 6 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 6518933 = 305575) (by norm_num)
theorem B4345955 : Blo 1931435 4345955 := bstep (se 1 (by rfl) ⟨3259466, by rfl⟩ : syracuseStep 4345955 = 6518933) B6518933
theorem B2897303 : Blo 1931435 2897303 := bstep (se 1 (by rfl) ⟨2172977, by rfl⟩ : syracuseStep 2897303 = 4345955) B4345955
theorem B1931535 : Blo 1931435 1931535 := bstep (se 1 (by rfl) ⟨1448651, by rfl⟩ : syracuseStep 1931535 = 2897303) B2897303
theorem B2897309 : Blo 1931435 2897309 := bbase (se 3 (by rfl) ⟨543245, by rfl⟩ : syracuseStep 2897309 = 1086491) (by norm_num)
theorem B1931539 : Blo 1931435 1931539 := bstep (se 1 (by rfl) ⟨1448654, by rfl⟩ : syracuseStep 1931539 = 2897309) B2897309
theorem B4345973 : Blo 1931435 4345973 := bbase (se 5 (by rfl) ⟨203717, by rfl⟩ : syracuseStep 4345973 = 407435) (by norm_num)
theorem B2897315 : Blo 1931435 2897315 := bstep (se 1 (by rfl) ⟨2172986, by rfl⟩ : syracuseStep 2897315 = 4345973) B4345973
theorem B1931543 : Blo 1931435 1931543 := bstep (se 1 (by rfl) ⟨1448657, by rfl⟩ : syracuseStep 1931543 = 2897315) B2897315
theorem B15876917 : Blo 1931435 15876917 := bbase (se 5 (by rfl) ⟨744230, by rfl⟩ : syracuseStep 15876917 = 1488461) (by norm_num)
theorem B10584611 : Blo 1931435 10584611 := bstep (se 1 (by rfl) ⟨7938458, by rfl⟩ : syracuseStep 10584611 = 15876917) B15876917
theorem B7056407 : Blo 1931435 7056407 := bstep (se 1 (by rfl) ⟨5292305, by rfl⟩ : syracuseStep 7056407 = 10584611) B10584611
theorem B18817085 : Blo 1931435 18817085 := bstep (se 3 (by rfl) ⟨3528203, by rfl⟩ : syracuseStep 18817085 = 7056407) B7056407
theorem B12544723 : Blo 1931435 12544723 := bstep (se 1 (by rfl) ⟨9408542, by rfl⟩ : syracuseStep 12544723 = 18817085) B18817085
theorem B16726297 : Blo 1931435 16726297 := bstep (se 2 (by rfl) ⟨6272361, by rfl⟩ : syracuseStep 16726297 = 12544723) B12544723
theorem B22301729 : Blo 1931435 22301729 := bstep (se 2 (by rfl) ⟨8363148, by rfl⟩ : syracuseStep 22301729 = 16726297) B16726297
theorem B14867819 : Blo 1931435 14867819 := bstep (se 1 (by rfl) ⟨11150864, by rfl⟩ : syracuseStep 14867819 = 22301729) B22301729
theorem B9911879 : Blo 1931435 9911879 := bstep (se 1 (by rfl) ⟨7433909, by rfl⟩ : syracuseStep 9911879 = 14867819) B14867819
theorem B6607919 : Blo 1931435 6607919 := bstep (se 1 (by rfl) ⟨4955939, by rfl⟩ : syracuseStep 6607919 = 9911879) B9911879
theorem B4405279 : Blo 1931435 4405279 := bstep (se 1 (by rfl) ⟨3303959, by rfl⟩ : syracuseStep 4405279 = 6607919) B6607919
theorem B5873705 : Blo 1931435 5873705 := bstep (se 2 (by rfl) ⟨2202639, by rfl⟩ : syracuseStep 5873705 = 4405279) B4405279
theorem B3915803 : Blo 1931435 3915803 := bstep (se 1 (by rfl) ⟨2936852, by rfl⟩ : syracuseStep 3915803 = 5873705) B5873705
theorem B10442141 : Blo 1931435 10442141 := bstep (se 3 (by rfl) ⟨1957901, by rfl⟩ : syracuseStep 10442141 = 3915803) B3915803
theorem B6961427 : Blo 1931435 6961427 := bstep (se 1 (by rfl) ⟨5221070, by rfl⟩ : syracuseStep 6961427 = 10442141) B10442141
theorem B4640951 : Blo 1931435 4640951 := bstep (se 1 (by rfl) ⟨3480713, by rfl⟩ : syracuseStep 4640951 = 6961427) B6961427
theorem B3093967 : Blo 1931435 3093967 := bstep (se 1 (by rfl) ⟨2320475, by rfl⟩ : syracuseStep 3093967 = 4640951) B4640951
theorem B16501157 : Blo 1931435 16501157 := bstep (se 4 (by rfl) ⟨1546983, by rfl⟩ : syracuseStep 16501157 = 3093967) B3093967
theorem B11000771 : Blo 1931435 11000771 := bstep (se 1 (by rfl) ⟨8250578, by rfl⟩ : syracuseStep 11000771 = 16501157) B16501157
theorem B7333847 : Blo 1931435 7333847 := bstep (se 1 (by rfl) ⟨5500385, by rfl⟩ : syracuseStep 7333847 = 11000771) B11000771
theorem B4889231 : Blo 1931435 4889231 := bstep (se 1 (by rfl) ⟨3666923, by rfl⟩ : syracuseStep 4889231 = 7333847) B7333847
theorem B3259487 : Blo 1931435 3259487 := bstep (se 1 (by rfl) ⟨2444615, by rfl⟩ : syracuseStep 3259487 = 4889231) B4889231
theorem B2172991 : Blo 1931435 2172991 := bstep (se 1 (by rfl) ⟨1629743, by rfl⟩ : syracuseStep 2172991 = 3259487) B3259487
theorem B2897321 : Blo 1931435 2897321 := bstep (se 2 (by rfl) ⟨1086495, by rfl⟩ : syracuseStep 2897321 = 2172991) B2172991
theorem B1931547 : Blo 1931435 1931547 := bstep (se 1 (by rfl) ⟨1448660, by rfl⟩ : syracuseStep 1931547 = 2897321) B2897321
theorem B7333861 : Blo 1931435 7333861 := bbase (se 4 (by rfl) ⟨687549, by rfl⟩ : syracuseStep 7333861 = 1375099) (by norm_num)
theorem B9778481 : Blo 1931435 9778481 := bstep (se 2 (by rfl) ⟨3666930, by rfl⟩ : syracuseStep 9778481 = 7333861) B7333861
theorem B6518987 : Blo 1931435 6518987 := bstep (se 1 (by rfl) ⟨4889240, by rfl⟩ : syracuseStep 6518987 = 9778481) B9778481
theorem B4345991 : Blo 1931435 4345991 := bstep (se 1 (by rfl) ⟨3259493, by rfl⟩ : syracuseStep 4345991 = 6518987) B6518987
theorem B2897327 : Blo 1931435 2897327 := bstep (se 1 (by rfl) ⟨2172995, by rfl⟩ : syracuseStep 2897327 = 4345991) B4345991
theorem B1931551 : Blo 1931435 1931551 := bstep (se 1 (by rfl) ⟨1448663, by rfl⟩ : syracuseStep 1931551 = 2897327) B2897327
theorem B2897333 : Blo 1931435 2897333 := bbase (se 5 (by rfl) ⟨135812, by rfl⟩ : syracuseStep 2897333 = 271625) (by norm_num)
theorem B1931555 : Blo 1931435 1931555 := bstep (se 1 (by rfl) ⟨1448666, by rfl⟩ : syracuseStep 1931555 = 2897333) B2897333
theorem B4889261 : Blo 1931435 4889261 := bbase (se 3 (by rfl) ⟨916736, by rfl⟩ : syracuseStep 4889261 = 1833473) (by norm_num)
theorem B3259507 : Blo 1931435 3259507 := bstep (se 1 (by rfl) ⟨2444630, by rfl⟩ : syracuseStep 3259507 = 4889261) B4889261
theorem B4346009 : Blo 1931435 4346009 := bstep (se 2 (by rfl) ⟨1629753, by rfl⟩ : syracuseStep 4346009 = 3259507) B3259507
theorem B2897339 : Blo 1931435 2897339 := bstep (se 1 (by rfl) ⟨2173004, by rfl⟩ : syracuseStep 2897339 = 4346009) B4346009
theorem B1931559 : Blo 1931435 1931559 := bstep (se 1 (by rfl) ⟨1448669, by rfl⟩ : syracuseStep 1931559 = 2897339) B2897339
theorem B2173009 : Blo 1931435 2173009 := bbase (se 2 (by rfl) ⟨814878, by rfl⟩ : syracuseStep 2173009 = 1629757) (by norm_num)
theorem B2897345 : Blo 1931435 2897345 := bstep (se 2 (by rfl) ⟨1086504, by rfl⟩ : syracuseStep 2897345 = 2173009) B2173009
theorem B1931563 : Blo 1931435 1931563 := bstep (se 1 (by rfl) ⟨1448672, by rfl⟩ : syracuseStep 1931563 = 2897345) B2897345
theorem B2750221 : Blo 1931435 2750221 := bbase (se 3 (by rfl) ⟨515666, by rfl⟩ : syracuseStep 2750221 = 1031333) (by norm_num)
theorem B3666961 : Blo 1931435 3666961 := bstep (se 2 (by rfl) ⟨1375110, by rfl⟩ : syracuseStep 3666961 = 2750221) B2750221
theorem B4889281 : Blo 1931435 4889281 := bstep (se 2 (by rfl) ⟨1833480, by rfl⟩ : syracuseStep 4889281 = 3666961) B3666961
theorem B6519041 : Blo 1931435 6519041 := bstep (se 2 (by rfl) ⟨2444640, by rfl⟩ : syracuseStep 6519041 = 4889281) B4889281
theorem B4346027 : Blo 1931435 4346027 := bstep (se 1 (by rfl) ⟨3259520, by rfl⟩ : syracuseStep 4346027 = 6519041) B6519041
theorem B2897351 : Blo 1931435 2897351 := bstep (se 1 (by rfl) ⟨2173013, by rfl⟩ : syracuseStep 2897351 = 4346027) B4346027
theorem B1931567 : Blo 1931435 1931567 := bstep (se 1 (by rfl) ⟨1448675, by rfl⟩ : syracuseStep 1931567 = 2897351) B2897351
theorem B2897357 : Blo 1931435 2897357 := bbase (se 3 (by rfl) ⟨543254, by rfl⟩ : syracuseStep 2897357 = 1086509) (by norm_num)
theorem B1931571 : Blo 1931435 1931571 := bstep (se 1 (by rfl) ⟨1448678, by rfl⟩ : syracuseStep 1931571 = 2897357) B2897357
theorem B4346045 : Blo 1931435 4346045 := bbase (se 3 (by rfl) ⟨814883, by rfl⟩ : syracuseStep 4346045 = 1629767) (by norm_num)
theorem B2897363 : Blo 1931435 2897363 := bstep (se 1 (by rfl) ⟨2173022, by rfl⟩ : syracuseStep 2897363 = 4346045) B4346045
theorem B1931575 : Blo 1931435 1931575 := bstep (se 1 (by rfl) ⟨1448681, by rfl⟩ : syracuseStep 1931575 = 2897363) B2897363
theorem B3259541 : Blo 1931435 3259541 := bbase (se 6 (by rfl) ⟨76395, by rfl⟩ : syracuseStep 3259541 = 152791) (by norm_num)
theorem B2173027 : Blo 1931435 2173027 := bstep (se 1 (by rfl) ⟨1629770, by rfl⟩ : syracuseStep 2173027 = 3259541) B3259541
theorem B2897369 : Blo 1931435 2897369 := bstep (se 2 (by rfl) ⟨1086513, by rfl⟩ : syracuseStep 2897369 = 2173027) B2173027
theorem B1931579 : Blo 1931435 1931579 := bstep (se 1 (by rfl) ⟨1448684, by rfl⟩ : syracuseStep 1931579 = 2897369) B2897369
theorem B5873813 : Blo 1931435 5873813 := bbase (se 6 (by rfl) ⟨137667, by rfl⟩ : syracuseStep 5873813 = 275335) (by norm_num)
theorem B3915875 : Blo 1931435 3915875 := bstep (se 1 (by rfl) ⟨2936906, by rfl⟩ : syracuseStep 3915875 = 5873813) B5873813
theorem B10442333 : Blo 1931435 10442333 := bstep (se 3 (by rfl) ⟨1957937, by rfl⟩ : syracuseStep 10442333 = 3915875) B3915875
theorem B6961555 : Blo 1931435 6961555 := bstep (se 1 (by rfl) ⟨5221166, by rfl⟩ : syracuseStep 6961555 = 10442333) B10442333
theorem B9282073 : Blo 1931435 9282073 := bstep (se 2 (by rfl) ⟨3480777, by rfl⟩ : syracuseStep 9282073 = 6961555) B6961555
theorem B12376097 : Blo 1931435 12376097 := bstep (se 2 (by rfl) ⟨4641036, by rfl⟩ : syracuseStep 12376097 = 9282073) B9282073
theorem B8250731 : Blo 1931435 8250731 := bstep (se 1 (by rfl) ⟨6188048, by rfl⟩ : syracuseStep 8250731 = 12376097) B12376097
theorem B5500487 : Blo 1931435 5500487 := bstep (se 1 (by rfl) ⟨4125365, by rfl⟩ : syracuseStep 5500487 = 8250731) B8250731
theorem B14667965 : Blo 1931435 14667965 := bstep (se 3 (by rfl) ⟨2750243, by rfl⟩ : syracuseStep 14667965 = 5500487) B5500487
theorem B9778643 : Blo 1931435 9778643 := bstep (se 1 (by rfl) ⟨7333982, by rfl⟩ : syracuseStep 9778643 = 14667965) B14667965
theorem B6519095 : Blo 1931435 6519095 := bstep (se 1 (by rfl) ⟨4889321, by rfl⟩ : syracuseStep 6519095 = 9778643) B9778643
theorem B4346063 : Blo 1931435 4346063 := bstep (se 1 (by rfl) ⟨3259547, by rfl⟩ : syracuseStep 4346063 = 6519095) B6519095
theorem B2897375 : Blo 1931435 2897375 := bstep (se 1 (by rfl) ⟨2173031, by rfl⟩ : syracuseStep 2897375 = 4346063) B4346063
theorem B1931583 : Blo 1931435 1931583 := bstep (se 1 (by rfl) ⟨1448687, by rfl⟩ : syracuseStep 1931583 = 2897375) B2897375
theorem B2897381 : Blo 1931435 2897381 := bbase (se 4 (by rfl) ⟨271629, by rfl⟩ : syracuseStep 2897381 = 543259) (by norm_num)
theorem B1931587 : Blo 1931435 1931587 := bstep (se 1 (by rfl) ⟨1448690, by rfl⟩ : syracuseStep 1931587 = 2897381) B2897381
theorem B5221189 : Blo 1931435 5221189 := bbase (se 4 (by rfl) ⟨489486, by rfl⟩ : syracuseStep 5221189 = 978973) (by norm_num)
theorem B27846341 : Blo 1931435 27846341 := bstep (se 4 (by rfl) ⟨2610594, by rfl⟩ : syracuseStep 27846341 = 5221189) B5221189
theorem B18564227 : Blo 1931435 18564227 := bstep (se 1 (by rfl) ⟨13923170, by rfl⟩ : syracuseStep 18564227 = 27846341) B27846341
theorem B12376151 : Blo 1931435 12376151 := bstep (se 1 (by rfl) ⟨9282113, by rfl⟩ : syracuseStep 12376151 = 18564227) B18564227
theorem B8250767 : Blo 1931435 8250767 := bstep (se 1 (by rfl) ⟨6188075, by rfl⟩ : syracuseStep 8250767 = 12376151) B12376151
theorem B5500511 : Blo 1931435 5500511 := bstep (se 1 (by rfl) ⟨4125383, by rfl⟩ : syracuseStep 5500511 = 8250767) B8250767
theorem B3667007 : Blo 1931435 3667007 := bstep (se 1 (by rfl) ⟨2750255, by rfl⟩ : syracuseStep 3667007 = 5500511) B5500511
theorem B2444671 : Blo 1931435 2444671 := bstep (se 1 (by rfl) ⟨1833503, by rfl⟩ : syracuseStep 2444671 = 3667007) B3667007
theorem B3259561 : Blo 1931435 3259561 := bstep (se 2 (by rfl) ⟨1222335, by rfl⟩ : syracuseStep 3259561 = 2444671) B2444671
theorem B4346081 : Blo 1931435 4346081 := bstep (se 2 (by rfl) ⟨1629780, by rfl⟩ : syracuseStep 4346081 = 3259561) B3259561
theorem B2897387 : Blo 1931435 2897387 := bstep (se 1 (by rfl) ⟨2173040, by rfl⟩ : syracuseStep 2897387 = 4346081) B4346081
theorem B1931591 : Blo 1931435 1931591 := bstep (se 1 (by rfl) ⟨1448693, by rfl⟩ : syracuseStep 1931591 = 2897387) B2897387
theorem B2173045 : Blo 1931435 2173045 := bbase (se 5 (by rfl) ⟨101861, by rfl⟩ : syracuseStep 2173045 = 203723) (by norm_num)
theorem B2897393 : Blo 1931435 2897393 := bstep (se 2 (by rfl) ⟨1086522, by rfl⟩ : syracuseStep 2897393 = 2173045) B2173045
theorem B1931595 : Blo 1931435 1931595 := bstep (se 1 (by rfl) ⟨1448696, by rfl⟩ : syracuseStep 1931595 = 2897393) B2897393
theorem B2444681 : Blo 1931435 2444681 := bbase (se 2 (by rfl) ⟨916755, by rfl⟩ : syracuseStep 2444681 = 1833511) (by norm_num)
theorem B6519149 : Blo 1931435 6519149 := bstep (se 3 (by rfl) ⟨1222340, by rfl⟩ : syracuseStep 6519149 = 2444681) B2444681
theorem B4346099 : Blo 1931435 4346099 := bstep (se 1 (by rfl) ⟨3259574, by rfl⟩ : syracuseStep 4346099 = 6519149) B6519149
theorem B2897399 : Blo 1931435 2897399 := bstep (se 1 (by rfl) ⟨2173049, by rfl⟩ : syracuseStep 2897399 = 4346099) B4346099
theorem B1931599 : Blo 1931435 1931599 := bstep (se 1 (by rfl) ⟨1448699, by rfl⟩ : syracuseStep 1931599 = 2897399) B2897399
theorem B2897405 : Blo 1931435 2897405 := bbase (se 3 (by rfl) ⟨543263, by rfl⟩ : syracuseStep 2897405 = 1086527) (by norm_num)
theorem B1931603 : Blo 1931435 1931603 := bstep (se 1 (by rfl) ⟨1448702, by rfl⟩ : syracuseStep 1931603 = 2897405) B2897405
theorem B4346117 : Blo 1931435 4346117 := bbase (se 4 (by rfl) ⟨407448, by rfl⟩ : syracuseStep 4346117 = 814897) (by norm_num)
theorem B2897411 : Blo 1931435 2897411 := bstep (se 1 (by rfl) ⟨2173058, by rfl⟩ : syracuseStep 2897411 = 4346117) B4346117
theorem B1931607 : Blo 1931435 1931607 := bstep (se 1 (by rfl) ⟨1448705, by rfl⟩ : syracuseStep 1931607 = 2897411) B2897411
theorem B3667045 : Blo 1931435 3667045 := bbase (se 4 (by rfl) ⟨343785, by rfl⟩ : syracuseStep 3667045 = 687571) (by norm_num)
theorem B4889393 : Blo 1931435 4889393 := bstep (se 2 (by rfl) ⟨1833522, by rfl⟩ : syracuseStep 4889393 = 3667045) B3667045
theorem B3259595 : Blo 1931435 3259595 := bstep (se 1 (by rfl) ⟨2444696, by rfl⟩ : syracuseStep 3259595 = 4889393) B4889393
theorem B2173063 : Blo 1931435 2173063 := bstep (se 1 (by rfl) ⟨1629797, by rfl⟩ : syracuseStep 2173063 = 3259595) B3259595
theorem B2897417 : Blo 1931435 2897417 := bstep (se 2 (by rfl) ⟨1086531, by rfl⟩ : syracuseStep 2897417 = 2173063) B2173063
theorem B1931611 : Blo 1931435 1931611 := bstep (se 1 (by rfl) ⟨1448708, by rfl⟩ : syracuseStep 1931611 = 2897417) B2897417
theorem B9778805 : Blo 1931435 9778805 := bbase (se 5 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 9778805 = 916763) (by norm_num)
theorem B6519203 : Blo 1931435 6519203 := bstep (se 1 (by rfl) ⟨4889402, by rfl⟩ : syracuseStep 6519203 = 9778805) B9778805
theorem B4346135 : Blo 1931435 4346135 := bstep (se 1 (by rfl) ⟨3259601, by rfl⟩ : syracuseStep 4346135 = 6519203) B6519203
theorem B2897423 : Blo 1931435 2897423 := bstep (se 1 (by rfl) ⟨2173067, by rfl⟩ : syracuseStep 2897423 = 4346135) B4346135
theorem B1931615 : Blo 1931435 1931615 := bstep (se 1 (by rfl) ⟨1448711, by rfl⟩ : syracuseStep 1931615 = 2897423) B2897423
theorem B2897429 : Blo 1931435 2897429 := bbase (se 6 (by rfl) ⟨67908, by rfl⟩ : syracuseStep 2897429 = 135817) (by norm_num)
theorem B1931619 : Blo 1931435 1931619 := bstep (se 1 (by rfl) ⟨1448714, by rfl⟩ : syracuseStep 1931619 = 2897429) B2897429
theorem B4641133 : Blo 1931435 4641133 := bbase (se 3 (by rfl) ⟨870212, by rfl⟩ : syracuseStep 4641133 = 1740425) (by norm_num)
theorem B6188177 : Blo 1931435 6188177 := bstep (se 2 (by rfl) ⟨2320566, by rfl⟩ : syracuseStep 6188177 = 4641133) B4641133
theorem B16501805 : Blo 1931435 16501805 := bstep (se 3 (by rfl) ⟨3094088, by rfl⟩ : syracuseStep 16501805 = 6188177) B6188177
theorem B11001203 : Blo 1931435 11001203 := bstep (se 1 (by rfl) ⟨8250902, by rfl⟩ : syracuseStep 11001203 = 16501805) B16501805
theorem B7334135 : Blo 1931435 7334135 := bstep (se 1 (by rfl) ⟨5500601, by rfl⟩ : syracuseStep 7334135 = 11001203) B11001203
theorem B4889423 : Blo 1931435 4889423 := bstep (se 1 (by rfl) ⟨3667067, by rfl⟩ : syracuseStep 4889423 = 7334135) B7334135
theorem B3259615 : Blo 1931435 3259615 := bstep (se 1 (by rfl) ⟨2444711, by rfl⟩ : syracuseStep 3259615 = 4889423) B4889423
theorem B4346153 : Blo 1931435 4346153 := bstep (se 2 (by rfl) ⟨1629807, by rfl⟩ : syracuseStep 4346153 = 3259615) B3259615
theorem B2897435 : Blo 1931435 2897435 := bstep (se 1 (by rfl) ⟨2173076, by rfl⟩ : syracuseStep 2897435 = 4346153) B4346153
theorem B1931623 : Blo 1931435 1931623 := bstep (se 1 (by rfl) ⟨1448717, by rfl⟩ : syracuseStep 1931623 = 2897435) B2897435
theorem B2173081 : Blo 1931435 2173081 := bbase (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) (by norm_num)
theorem B2897441 : Blo 1931435 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B1931627 : Blo 1931435 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B7334165 : Blo 1931435 7334165 := bbase (se 6 (by rfl) ⟨171894, by rfl⟩ : syracuseStep 7334165 = 343789) (by norm_num)
theorem B4889443 : Blo 1931435 4889443 := bstep (se 1 (by rfl) ⟨3667082, by rfl⟩ : syracuseStep 4889443 = 7334165) B7334165
theorem B6519257 : Blo 1931435 6519257 := bstep (se 2 (by rfl) ⟨2444721, by rfl⟩ : syracuseStep 6519257 = 4889443) B4889443
theorem B4346171 : Blo 1931435 4346171 := bstep (se 1 (by rfl) ⟨3259628, by rfl⟩ : syracuseStep 4346171 = 6519257) B6519257
theorem B2897447 : Blo 1931435 2897447 := bstep (se 1 (by rfl) ⟨2173085, by rfl⟩ : syracuseStep 2897447 = 4346171) B4346171
theorem B1931631 : Blo 1931435 1931631 := bstep (se 1 (by rfl) ⟨1448723, by rfl⟩ : syracuseStep 1931631 = 2897447) B2897447
theorem B2897453 : Blo 1931435 2897453 := bbase (se 3 (by rfl) ⟨543272, by rfl⟩ : syracuseStep 2897453 = 1086545) (by norm_num)
theorem B1931635 : Blo 1931435 1931635 := bstep (se 1 (by rfl) ⟨1448726, by rfl⟩ : syracuseStep 1931635 = 2897453) B2897453
theorem B4346189 : Blo 1931435 4346189 := bbase (se 3 (by rfl) ⟨814910, by rfl⟩ : syracuseStep 4346189 = 1629821) (by norm_num)
theorem B2897459 : Blo 1931435 2897459 := bstep (se 1 (by rfl) ⟨2173094, by rfl⟩ : syracuseStep 2897459 = 4346189) B4346189
theorem B1931639 : Blo 1931435 1931639 := bstep (se 1 (by rfl) ⟨1448729, by rfl⟩ : syracuseStep 1931639 = 2897459) B2897459
theorem B2444737 : Blo 1931435 2444737 := bbase (se 2 (by rfl) ⟨916776, by rfl⟩ : syracuseStep 2444737 = 1833553) (by norm_num)
theorem B3259649 : Blo 1931435 3259649 := bstep (se 2 (by rfl) ⟨1222368, by rfl⟩ : syracuseStep 3259649 = 2444737) B2444737
theorem B2173099 : Blo 1931435 2173099 := bstep (se 1 (by rfl) ⟨1629824, by rfl⟩ : syracuseStep 2173099 = 3259649) B3259649
theorem B2897465 : Blo 1931435 2897465 := bstep (se 2 (by rfl) ⟨1086549, by rfl⟩ : syracuseStep 2897465 = 2173099) B2173099
theorem B1931643 : Blo 1931435 1931643 := bstep (se 1 (by rfl) ⟨1448732, by rfl⟩ : syracuseStep 1931643 = 2897465) B2897465
theorem B8811013 : Blo 1931435 8811013 := bbase (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) (by norm_num)
theorem B11748017 : Blo 1931435 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B7832011 : Blo 1931435 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B10442681 : Blo 1931435 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B6961787 : Blo 1931435 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B4641191 : Blo 1931435 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B3094127 : Blo 1931435 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B2062751 : Blo 1931435 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B22002677 : Blo 1931435 22002677 := bstep (se 5 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 22002677 = 2062751) B2062751
theorem B14668451 : Blo 1931435 14668451 := bstep (se 1 (by rfl) ⟨11001338, by rfl⟩ : syracuseStep 14668451 = 22002677) B22002677
theorem B9778967 : Blo 1931435 9778967 := bstep (se 1 (by rfl) ⟨7334225, by rfl⟩ : syracuseStep 9778967 = 14668451) B14668451
theorem B6519311 : Blo 1931435 6519311 := bstep (se 1 (by rfl) ⟨4889483, by rfl⟩ : syracuseStep 6519311 = 9778967) B9778967
theorem B4346207 : Blo 1931435 4346207 := bstep (se 1 (by rfl) ⟨3259655, by rfl⟩ : syracuseStep 4346207 = 6519311) B6519311
theorem B2897471 : Blo 1931435 2897471 := bstep (se 1 (by rfl) ⟨2173103, by rfl⟩ : syracuseStep 2897471 = 4346207) B4346207
theorem B1931647 : Blo 1931435 1931647 := bstep (se 1 (by rfl) ⟨1448735, by rfl⟩ : syracuseStep 1931647 = 2897471) B2897471
theorem B2897477 : Blo 1931435 2897477 := bbase (se 4 (by rfl) ⟨271638, by rfl⟩ : syracuseStep 2897477 = 543277) (by norm_num)
theorem B1931651 : Blo 1931435 1931651 := bstep (se 1 (by rfl) ⟨1448738, by rfl⟩ : syracuseStep 1931651 = 2897477) B2897477
theorem B3259669 : Blo 1931435 3259669 := bbase (se 6 (by rfl) ⟨76398, by rfl⟩ : syracuseStep 3259669 = 152797) (by norm_num)
theorem B4346225 : Blo 1931435 4346225 := bstep (se 2 (by rfl) ⟨1629834, by rfl⟩ : syracuseStep 4346225 = 3259669) B3259669
theorem B2897483 : Blo 1931435 2897483 := bstep (se 1 (by rfl) ⟨2173112, by rfl⟩ : syracuseStep 2897483 = 4346225) B4346225
theorem B1931655 : Blo 1931435 1931655 := bstep (se 1 (by rfl) ⟨1448741, by rfl⟩ : syracuseStep 1931655 = 2897483) B2897483
theorem B2173117 : Blo 1931435 2173117 := bbase (se 3 (by rfl) ⟨407459, by rfl⟩ : syracuseStep 2173117 = 814919) (by norm_num)
theorem B2897489 : Blo 1931435 2897489 := bstep (se 2 (by rfl) ⟨1086558, by rfl⟩ : syracuseStep 2897489 = 2173117) B2173117
theorem B1931659 : Blo 1931435 1931659 := bstep (se 1 (by rfl) ⟨1448744, by rfl⟩ : syracuseStep 1931659 = 2897489) B2897489
theorem B6519365 : Blo 1931435 6519365 := bbase (se 4 (by rfl) ⟨611190, by rfl⟩ : syracuseStep 6519365 = 1222381) (by norm_num)
theorem B4346243 : Blo 1931435 4346243 := bstep (se 1 (by rfl) ⟨3259682, by rfl⟩ : syracuseStep 4346243 = 6519365) B6519365
theorem B2897495 : Blo 1931435 2897495 := bstep (se 1 (by rfl) ⟨2173121, by rfl⟩ : syracuseStep 2897495 = 4346243) B4346243
theorem B1931663 : Blo 1931435 1931663 := bstep (se 1 (by rfl) ⟨1448747, by rfl⟩ : syracuseStep 1931663 = 2897495) B2897495
theorem B2897501 : Blo 1931435 2897501 := bbase (se 3 (by rfl) ⟨543281, by rfl⟩ : syracuseStep 2897501 = 1086563) (by norm_num)
theorem B1931667 : Blo 1931435 1931667 := bstep (se 1 (by rfl) ⟨1448750, by rfl⟩ : syracuseStep 1931667 = 2897501) B2897501
theorem B4346261 : Blo 1931435 4346261 := bbase (se 6 (by rfl) ⟨101865, by rfl⟩ : syracuseStep 4346261 = 203731) (by norm_num)
theorem B2897507 : Blo 1931435 2897507 := bstep (se 1 (by rfl) ⟨2173130, by rfl⟩ : syracuseStep 2897507 = 4346261) B4346261
theorem B1931671 : Blo 1931435 1931671 := bstep (se 1 (by rfl) ⟨1448753, by rfl⟩ : syracuseStep 1931671 = 2897507) B2897507
theorem B2787901 : Blo 1931435 2787901 := bbase (se 3 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 2787901 = 1045463) (by norm_num)
theorem B14868805 : Blo 1931435 14868805 := bstep (se 4 (by rfl) ⟨1393950, by rfl⟩ : syracuseStep 14868805 = 2787901) B2787901
theorem B19825073 : Blo 1931435 19825073 := bstep (se 2 (by rfl) ⟨7434402, by rfl⟩ : syracuseStep 19825073 = 14868805) B14868805
theorem B13216715 : Blo 1931435 13216715 := bstep (se 1 (by rfl) ⟨9912536, by rfl⟩ : syracuseStep 13216715 = 19825073) B19825073
theorem B8811143 : Blo 1931435 8811143 := bstep (se 1 (by rfl) ⟨6608357, by rfl⟩ : syracuseStep 8811143 = 13216715) B13216715
theorem B5874095 : Blo 1931435 5874095 := bstep (se 1 (by rfl) ⟨4405571, by rfl⟩ : syracuseStep 5874095 = 8811143) B8811143
theorem B3916063 : Blo 1931435 3916063 := bstep (se 1 (by rfl) ⟨2937047, by rfl⟩ : syracuseStep 3916063 = 5874095) B5874095
theorem B5221417 : Blo 1931435 5221417 := bstep (se 2 (by rfl) ⟨1958031, by rfl⟩ : syracuseStep 5221417 = 3916063) B3916063
theorem B6961889 : Blo 1931435 6961889 := bstep (se 2 (by rfl) ⟨2610708, by rfl⟩ : syracuseStep 6961889 = 5221417) B5221417
theorem B4641259 : Blo 1931435 4641259 := bstep (se 1 (by rfl) ⟨3480944, by rfl⟩ : syracuseStep 4641259 = 6961889) B6961889
theorem B6188345 : Blo 1931435 6188345 := bstep (se 2 (by rfl) ⟨2320629, by rfl⟩ : syracuseStep 6188345 = 4641259) B4641259
theorem B4125563 : Blo 1931435 4125563 := bstep (se 1 (by rfl) ⟨3094172, by rfl⟩ : syracuseStep 4125563 = 6188345) B6188345
theorem B2750375 : Blo 1931435 2750375 := bstep (se 1 (by rfl) ⟨2062781, by rfl⟩ : syracuseStep 2750375 = 4125563) B4125563
theorem B7334333 : Blo 1931435 7334333 := bstep (se 3 (by rfl) ⟨1375187, by rfl⟩ : syracuseStep 7334333 = 2750375) B2750375
theorem B4889555 : Blo 1931435 4889555 := bstep (se 1 (by rfl) ⟨3667166, by rfl⟩ : syracuseStep 4889555 = 7334333) B7334333
theorem B3259703 : Blo 1931435 3259703 := bstep (se 1 (by rfl) ⟨2444777, by rfl⟩ : syracuseStep 3259703 = 4889555) B4889555
theorem B2173135 : Blo 1931435 2173135 := bstep (se 1 (by rfl) ⟨1629851, by rfl⟩ : syracuseStep 2173135 = 3259703) B3259703
theorem B2897513 : Blo 1931435 2897513 := bstep (se 2 (by rfl) ⟨1086567, by rfl⟩ : syracuseStep 2897513 = 2173135) B2173135
theorem B1931675 : Blo 1931435 1931675 := bstep (se 1 (by rfl) ⟨1448756, by rfl⟩ : syracuseStep 1931675 = 2897513) B2897513
theorem B8251141 : Blo 1931435 8251141 := bbase (se 4 (by rfl) ⟨773544, by rfl⟩ : syracuseStep 8251141 = 1547089) (by norm_num)
theorem B11001521 : Blo 1931435 11001521 := bstep (se 2 (by rfl) ⟨4125570, by rfl⟩ : syracuseStep 11001521 = 8251141) B8251141
theorem B7334347 : Blo 1931435 7334347 := bstep (se 1 (by rfl) ⟨5500760, by rfl⟩ : syracuseStep 7334347 = 11001521) B11001521
theorem B9779129 : Blo 1931435 9779129 := bstep (se 2 (by rfl) ⟨3667173, by rfl⟩ : syracuseStep 9779129 = 7334347) B7334347
theorem B6519419 : Blo 1931435 6519419 := bstep (se 1 (by rfl) ⟨4889564, by rfl⟩ : syracuseStep 6519419 = 9779129) B9779129
theorem B4346279 : Blo 1931435 4346279 := bstep (se 1 (by rfl) ⟨3259709, by rfl⟩ : syracuseStep 4346279 = 6519419) B6519419
theorem B2897519 : Blo 1931435 2897519 := bstep (se 1 (by rfl) ⟨2173139, by rfl⟩ : syracuseStep 2897519 = 4346279) B4346279
theorem B1931679 : Blo 1931435 1931679 := bstep (se 1 (by rfl) ⟨1448759, by rfl⟩ : syracuseStep 1931679 = 2897519) B2897519
theorem B2897525 : Blo 1931435 2897525 := bbase (se 5 (by rfl) ⟨135821, by rfl⟩ : syracuseStep 2897525 = 271643) (by norm_num)
theorem B1931683 : Blo 1931435 1931683 := bstep (se 1 (by rfl) ⟨1448762, by rfl⟩ : syracuseStep 1931683 = 2897525) B2897525
theorem B3667189 : Blo 1931435 3667189 := bbase (se 5 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 3667189 = 343799) (by norm_num)
theorem B4889585 : Blo 1931435 4889585 := bstep (se 2 (by rfl) ⟨1833594, by rfl⟩ : syracuseStep 4889585 = 3667189) B3667189
theorem B3259723 : Blo 1931435 3259723 := bstep (se 1 (by rfl) ⟨2444792, by rfl⟩ : syracuseStep 3259723 = 4889585) B4889585
theorem B4346297 : Blo 1931435 4346297 := bstep (se 2 (by rfl) ⟨1629861, by rfl⟩ : syracuseStep 4346297 = 3259723) B3259723
theorem B2897531 : Blo 1931435 2897531 := bstep (se 1 (by rfl) ⟨2173148, by rfl⟩ : syracuseStep 2897531 = 4346297) B4346297
theorem B1931687 : Blo 1931435 1931687 := bstep (se 1 (by rfl) ⟨1448765, by rfl⟩ : syracuseStep 1931687 = 2897531) B2897531
theorem B2173153 : Blo 1931435 2173153 := bbase (se 2 (by rfl) ⟨814932, by rfl⟩ : syracuseStep 2173153 = 1629865) (by norm_num)
theorem B2897537 : Blo 1931435 2897537 := bstep (se 2 (by rfl) ⟨1086576, by rfl⟩ : syracuseStep 2897537 = 2173153) B2173153
theorem B1931691 : Blo 1931435 1931691 := bstep (se 1 (by rfl) ⟨1448768, by rfl⟩ : syracuseStep 1931691 = 2897537) B2897537
theorem B4889605 : Blo 1931435 4889605 := bbase (se 4 (by rfl) ⟨458400, by rfl⟩ : syracuseStep 4889605 = 916801) (by norm_num)
theorem B6519473 : Blo 1931435 6519473 := bstep (se 2 (by rfl) ⟨2444802, by rfl⟩ : syracuseStep 6519473 = 4889605) B4889605
theorem B4346315 : Blo 1931435 4346315 := bstep (se 1 (by rfl) ⟨3259736, by rfl⟩ : syracuseStep 4346315 = 6519473) B6519473
theorem B2897543 : Blo 1931435 2897543 := bstep (se 1 (by rfl) ⟨2173157, by rfl⟩ : syracuseStep 2897543 = 4346315) B4346315
theorem B1931695 : Blo 1931435 1931695 := bstep (se 1 (by rfl) ⟨1448771, by rfl⟩ : syracuseStep 1931695 = 2897543) B2897543
theorem B2897549 : Blo 1931435 2897549 := bbase (se 3 (by rfl) ⟨543290, by rfl⟩ : syracuseStep 2897549 = 1086581) (by norm_num)
theorem B1931699 : Blo 1931435 1931699 := bstep (se 1 (by rfl) ⟨1448774, by rfl⟩ : syracuseStep 1931699 = 2897549) B2897549
theorem B4346333 : Blo 1931435 4346333 := bbase (se 3 (by rfl) ⟨814937, by rfl⟩ : syracuseStep 4346333 = 1629875) (by norm_num)
theorem B2897555 : Blo 1931435 2897555 := bstep (se 1 (by rfl) ⟨2173166, by rfl⟩ : syracuseStep 2897555 = 4346333) B4346333
theorem B1931703 : Blo 1931435 1931703 := bstep (se 1 (by rfl) ⟨1448777, by rfl⟩ : syracuseStep 1931703 = 2897555) B2897555
theorem B3259757 : Blo 1931435 3259757 := bbase (se 3 (by rfl) ⟨611204, by rfl⟩ : syracuseStep 3259757 = 1222409) (by norm_num)
theorem B2173171 : Blo 1931435 2173171 := bstep (se 1 (by rfl) ⟨1629878, by rfl⟩ : syracuseStep 2173171 = 3259757) B3259757
theorem B2897561 : Blo 1931435 2897561 := bstep (se 2 (by rfl) ⟨1086585, by rfl⟩ : syracuseStep 2897561 = 2173171) B2173171
theorem B1931707 : Blo 1931435 1931707 := bstep (se 1 (by rfl) ⟨1448780, by rfl⟩ : syracuseStep 1931707 = 2897561) B2897561
theorem B7153285 : Blo 1931435 7153285 := bbase (se 4 (by rfl) ⟨670620, by rfl⟩ : syracuseStep 7153285 = 1341241) (by norm_num)
theorem B9537713 : Blo 1931435 9537713 := bstep (se 2 (by rfl) ⟨3576642, by rfl⟩ : syracuseStep 9537713 = 7153285) B7153285
theorem B6358475 : Blo 1931435 6358475 := bstep (se 1 (by rfl) ⟨4768856, by rfl⟩ : syracuseStep 6358475 = 9537713) B9537713
theorem B4238983 : Blo 1931435 4238983 := bstep (se 1 (by rfl) ⟨3179237, by rfl⟩ : syracuseStep 4238983 = 6358475) B6358475
theorem B22607909 : Blo 1931435 22607909 := bstep (se 4 (by rfl) ⟨2119491, by rfl⟩ : syracuseStep 22607909 = 4238983) B4238983
theorem B15071939 : Blo 1931435 15071939 := bstep (se 1 (by rfl) ⟨11303954, by rfl⟩ : syracuseStep 15071939 = 22607909) B22607909
theorem B10047959 : Blo 1931435 10047959 := bstep (se 1 (by rfl) ⟨7535969, by rfl⟩ : syracuseStep 10047959 = 15071939) B15071939
theorem B6698639 : Blo 1931435 6698639 := bstep (se 1 (by rfl) ⟨5023979, by rfl⟩ : syracuseStep 6698639 = 10047959) B10047959
theorem B17863037 : Blo 1931435 17863037 := bstep (se 3 (by rfl) ⟨3349319, by rfl⟩ : syracuseStep 17863037 = 6698639) B6698639
theorem B11908691 : Blo 1931435 11908691 := bstep (se 1 (by rfl) ⟨8931518, by rfl⟩ : syracuseStep 11908691 = 17863037) B17863037
theorem B7939127 : Blo 1931435 7939127 := bstep (se 1 (by rfl) ⟨5954345, by rfl⟩ : syracuseStep 7939127 = 11908691) B11908691
theorem B5292751 : Blo 1931435 5292751 := bstep (se 1 (by rfl) ⟨3969563, by rfl⟩ : syracuseStep 5292751 = 7939127) B7939127
theorem B7057001 : Blo 1931435 7057001 := bstep (se 2 (by rfl) ⟨2646375, by rfl⟩ : syracuseStep 7057001 = 5292751) B5292751
theorem B18818669 : Blo 1931435 18818669 := bstep (se 3 (by rfl) ⟨3528500, by rfl⟩ : syracuseStep 18818669 = 7057001) B7057001
theorem B50183117 : Blo 1931435 50183117 := bstep (se 3 (by rfl) ⟨9409334, by rfl⟩ : syracuseStep 50183117 = 18818669) B18818669
theorem B33455411 : Blo 1931435 33455411 := bstep (se 1 (by rfl) ⟨25091558, by rfl⟩ : syracuseStep 33455411 = 50183117) B50183117
theorem B22303607 : Blo 1931435 22303607 := bstep (se 1 (by rfl) ⟨16727705, by rfl⟩ : syracuseStep 22303607 = 33455411) B33455411
theorem B59476285 : Blo 1931435 59476285 := bstep (se 3 (by rfl) ⟨11151803, by rfl⟩ : syracuseStep 59476285 = 22303607) B22303607
theorem B317206853 : Blo 1931435 317206853 := bstep (se 4 (by rfl) ⟨29738142, by rfl⟩ : syracuseStep 317206853 = 59476285) B59476285
theorem B211471235 : Blo 1931435 211471235 := bstep (se 1 (by rfl) ⟨158603426, by rfl⟩ : syracuseStep 211471235 = 317206853) B317206853
theorem B140980823 : Blo 1931435 140980823 := bstep (se 1 (by rfl) ⟨105735617, by rfl⟩ : syracuseStep 140980823 = 211471235) B211471235
theorem B93987215 : Blo 1931435 93987215 := bstep (se 1 (by rfl) ⟨70490411, by rfl⟩ : syracuseStep 93987215 = 140980823) B140980823
theorem B62658143 : Blo 1931435 62658143 := bstep (se 1 (by rfl) ⟨46993607, by rfl⟩ : syracuseStep 62658143 = 93987215) B93987215
theorem B41772095 : Blo 1931435 41772095 := bstep (se 1 (by rfl) ⟨31329071, by rfl⟩ : syracuseStep 41772095 = 62658143) B62658143
theorem B27848063 : Blo 1931435 27848063 := bstep (se 1 (by rfl) ⟨20886047, by rfl⟩ : syracuseStep 27848063 = 41772095) B41772095
theorem B18565375 : Blo 1931435 18565375 := bstep (se 1 (by rfl) ⟨13924031, by rfl⟩ : syracuseStep 18565375 = 27848063) B27848063
theorem B24753833 : Blo 1931435 24753833 := bstep (se 2 (by rfl) ⟨9282687, by rfl⟩ : syracuseStep 24753833 = 18565375) B18565375
theorem B16502555 : Blo 1931435 16502555 := bstep (se 1 (by rfl) ⟨12376916, by rfl⟩ : syracuseStep 16502555 = 24753833) B24753833
theorem B11001703 : Blo 1931435 11001703 := bstep (se 1 (by rfl) ⟨8251277, by rfl⟩ : syracuseStep 11001703 = 16502555) B16502555
theorem B14668937 : Blo 1931435 14668937 := bstep (se 2 (by rfl) ⟨5500851, by rfl⟩ : syracuseStep 14668937 = 11001703) B11001703
theorem B9779291 : Blo 1931435 9779291 := bstep (se 1 (by rfl) ⟨7334468, by rfl⟩ : syracuseStep 9779291 = 14668937) B14668937
theorem B6519527 : Blo 1931435 6519527 := bstep (se 1 (by rfl) ⟨4889645, by rfl⟩ : syracuseStep 6519527 = 9779291) B9779291
theorem B4346351 : Blo 1931435 4346351 := bstep (se 1 (by rfl) ⟨3259763, by rfl⟩ : syracuseStep 4346351 = 6519527) B6519527
theorem B2897567 : Blo 1931435 2897567 := bstep (se 1 (by rfl) ⟨2173175, by rfl⟩ : syracuseStep 2897567 = 4346351) B4346351
theorem B1931711 : Blo 1931435 1931711 := bstep (se 1 (by rfl) ⟨1448783, by rfl⟩ : syracuseStep 1931711 = 2897567) B2897567
theorem B2897573 : Blo 1931435 2897573 := bbase (se 4 (by rfl) ⟨271647, by rfl⟩ : syracuseStep 2897573 = 543295) (by norm_num)
theorem B1931715 : Blo 1931435 1931715 := bstep (se 1 (by rfl) ⟨1448786, by rfl⟩ : syracuseStep 1931715 = 2897573) B2897573
theorem B2444833 : Blo 1931435 2444833 := bbase (se 2 (by rfl) ⟨916812, by rfl⟩ : syracuseStep 2444833 = 1833625) (by norm_num)
theorem B3259777 : Blo 1931435 3259777 := bstep (se 2 (by rfl) ⟨1222416, by rfl⟩ : syracuseStep 3259777 = 2444833) B2444833
theorem B4346369 : Blo 1931435 4346369 := bstep (se 2 (by rfl) ⟨1629888, by rfl⟩ : syracuseStep 4346369 = 3259777) B3259777
theorem B2897579 : Blo 1931435 2897579 := bstep (se 1 (by rfl) ⟨2173184, by rfl⟩ : syracuseStep 2897579 = 4346369) B4346369
theorem B1931719 : Blo 1931435 1931719 := bstep (se 1 (by rfl) ⟨1448789, by rfl⟩ : syracuseStep 1931719 = 2897579) B2897579
theorem B2173189 : Blo 1931435 2173189 := bbase (se 4 (by rfl) ⟨203736, by rfl⟩ : syracuseStep 2173189 = 407473) (by norm_num)
theorem B2897585 : Blo 1931435 2897585 := bstep (se 2 (by rfl) ⟨1086594, by rfl⟩ : syracuseStep 2897585 = 2173189) B2173189
theorem B1931723 : Blo 1931435 1931723 := bstep (se 1 (by rfl) ⟨1448792, by rfl⟩ : syracuseStep 1931723 = 2897585) B2897585
theorem B2062837 : Blo 1931435 2062837 := bbase (se 5 (by rfl) ⟨96695, by rfl⟩ : syracuseStep 2062837 = 193391) (by norm_num)
theorem B2750449 : Blo 1931435 2750449 := bstep (se 2 (by rfl) ⟨1031418, by rfl⟩ : syracuseStep 2750449 = 2062837) B2062837
theorem B3667265 : Blo 1931435 3667265 := bstep (se 2 (by rfl) ⟨1375224, by rfl⟩ : syracuseStep 3667265 = 2750449) B2750449
theorem B2444843 : Blo 1931435 2444843 := bstep (se 1 (by rfl) ⟨1833632, by rfl⟩ : syracuseStep 2444843 = 3667265) B3667265
theorem B6519581 : Blo 1931435 6519581 := bstep (se 3 (by rfl) ⟨1222421, by rfl⟩ : syracuseStep 6519581 = 2444843) B2444843
theorem B4346387 : Blo 1931435 4346387 := bstep (se 1 (by rfl) ⟨3259790, by rfl⟩ : syracuseStep 4346387 = 6519581) B6519581
theorem B2897591 : Blo 1931435 2897591 := bstep (se 1 (by rfl) ⟨2173193, by rfl⟩ : syracuseStep 2897591 = 4346387) B4346387
theorem B1931727 : Blo 1931435 1931727 := bstep (se 1 (by rfl) ⟨1448795, by rfl⟩ : syracuseStep 1931727 = 2897591) B2897591
theorem B2897597 : Blo 1931435 2897597 := bbase (se 3 (by rfl) ⟨543299, by rfl⟩ : syracuseStep 2897597 = 1086599) (by norm_num)
theorem B1931731 : Blo 1931435 1931731 := bstep (se 1 (by rfl) ⟨1448798, by rfl⟩ : syracuseStep 1931731 = 2897597) B2897597
theorem B4346405 : Blo 1931435 4346405 := bbase (se 4 (by rfl) ⟨407475, by rfl⟩ : syracuseStep 4346405 = 814951) (by norm_num)
theorem B2897603 : Blo 1931435 2897603 := bstep (se 1 (by rfl) ⟨2173202, by rfl⟩ : syracuseStep 2897603 = 4346405) B4346405
theorem B1931735 : Blo 1931435 1931735 := bstep (se 1 (by rfl) ⟨1448801, by rfl⟩ : syracuseStep 1931735 = 2897603) B2897603
theorem B4889717 : Blo 1931435 4889717 := bbase (se 5 (by rfl) ⟨229205, by rfl⟩ : syracuseStep 4889717 = 458411) (by norm_num)
theorem B3259811 : Blo 1931435 3259811 := bstep (se 1 (by rfl) ⟨2444858, by rfl⟩ : syracuseStep 3259811 = 4889717) B4889717
theorem B2173207 : Blo 1931435 2173207 := bstep (se 1 (by rfl) ⟨1629905, by rfl⟩ : syracuseStep 2173207 = 3259811) B3259811
theorem B2897609 : Blo 1931435 2897609 := bstep (se 2 (by rfl) ⟨1086603, by rfl⟩ : syracuseStep 2897609 = 2173207) B2173207
theorem B1931739 : Blo 1931435 1931739 := bstep (se 1 (by rfl) ⟨1448804, by rfl⟩ : syracuseStep 1931739 = 2897609) B2897609
theorem B18565685 : Blo 1931435 18565685 := bbase (se 5 (by rfl) ⟨870266, by rfl⟩ : syracuseStep 18565685 = 1740533) (by norm_num)
theorem B12377123 : Blo 1931435 12377123 := bstep (se 1 (by rfl) ⟨9282842, by rfl⟩ : syracuseStep 12377123 = 18565685) B18565685
theorem B8251415 : Blo 1931435 8251415 := bstep (se 1 (by rfl) ⟨6188561, by rfl⟩ : syracuseStep 8251415 = 12377123) B12377123
theorem B5500943 : Blo 1931435 5500943 := bstep (se 1 (by rfl) ⟨4125707, by rfl⟩ : syracuseStep 5500943 = 8251415) B8251415
theorem B3667295 : Blo 1931435 3667295 := bstep (se 1 (by rfl) ⟨2750471, by rfl⟩ : syracuseStep 3667295 = 5500943) B5500943
theorem B9779453 : Blo 1931435 9779453 := bstep (se 3 (by rfl) ⟨1833647, by rfl⟩ : syracuseStep 9779453 = 3667295) B3667295
theorem B6519635 : Blo 1931435 6519635 := bstep (se 1 (by rfl) ⟨4889726, by rfl⟩ : syracuseStep 6519635 = 9779453) B9779453
theorem B4346423 : Blo 1931435 4346423 := bstep (se 1 (by rfl) ⟨3259817, by rfl⟩ : syracuseStep 4346423 = 6519635) B6519635
theorem B2897615 : Blo 1931435 2897615 := bstep (se 1 (by rfl) ⟨2173211, by rfl⟩ : syracuseStep 2897615 = 4346423) B4346423
theorem B1931743 : Blo 1931435 1931743 := bstep (se 1 (by rfl) ⟨1448807, by rfl⟩ : syracuseStep 1931743 = 2897615) B2897615
theorem B2897621 : Blo 1931435 2897621 := bbase (se 7 (by rfl) ⟨33956, by rfl⟩ : syracuseStep 2897621 = 67913) (by norm_num)
theorem B1931747 : Blo 1931435 1931747 := bstep (se 1 (by rfl) ⟨1448810, by rfl⟩ : syracuseStep 1931747 = 2897621) B2897621
theorem B4125725 : Blo 1931435 4125725 := bbase (se 3 (by rfl) ⟨773573, by rfl⟩ : syracuseStep 4125725 = 1547147) (by norm_num)
theorem B2750483 : Blo 1931435 2750483 := bstep (se 1 (by rfl) ⟨2062862, by rfl⟩ : syracuseStep 2750483 = 4125725) B4125725
theorem B7334621 : Blo 1931435 7334621 := bstep (se 3 (by rfl) ⟨1375241, by rfl⟩ : syracuseStep 7334621 = 2750483) B2750483
theorem B4889747 : Blo 1931435 4889747 := bstep (se 1 (by rfl) ⟨3667310, by rfl⟩ : syracuseStep 4889747 = 7334621) B7334621
theorem B3259831 : Blo 1931435 3259831 := bstep (se 1 (by rfl) ⟨2444873, by rfl⟩ : syracuseStep 3259831 = 4889747) B4889747
theorem B4346441 : Blo 1931435 4346441 := bstep (se 2 (by rfl) ⟨1629915, by rfl⟩ : syracuseStep 4346441 = 3259831) B3259831
theorem B2897627 : Blo 1931435 2897627 := bstep (se 1 (by rfl) ⟨2173220, by rfl⟩ : syracuseStep 2897627 = 4346441) B4346441
theorem B1931751 : Blo 1931435 1931751 := bstep (se 1 (by rfl) ⟨1448813, by rfl⟩ : syracuseStep 1931751 = 2897627) B2897627
theorem B2173225 : Blo 1931435 2173225 := bbase (se 2 (by rfl) ⟨814959, by rfl⟩ : syracuseStep 2173225 = 1629919) (by norm_num)
theorem B2897633 : Blo 1931435 2897633 := bstep (se 2 (by rfl) ⟨1086612, by rfl⟩ : syracuseStep 2897633 = 2173225) B2173225
theorem B1931755 : Blo 1931435 1931755 := bstep (se 1 (by rfl) ⟨1448816, by rfl⟩ : syracuseStep 1931755 = 2897633) B2897633
theorem B14114357 : Blo 1931435 14114357 := bbase (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) (by norm_num)
theorem B9409571 : Blo 1931435 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B6273047 : Blo 1931435 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B4182031 : Blo 1931435 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B22304165 : Blo 1931435 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B59477773 : Blo 1931435 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B79303697 : Blo 1931435 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B52869131 : Blo 1931435 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B35246087 : Blo 1931435 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B23497391 : Blo 1931435 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B15664927 : Blo 1931435 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B20886569 : Blo 1931435 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B13924379 : Blo 1931435 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B9282919 : Blo 1931435 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B12377225 : Blo 1931435 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B8251483 : Blo 1931435 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B11001977 : Blo 1931435 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B7334651 : Blo 1931435 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B4889767 : Blo 1931435 4889767 := bstep (se 1 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 4889767 = 7334651) B7334651
theorem B6519689 : Blo 1931435 6519689 := bstep (se 2 (by rfl) ⟨2444883, by rfl⟩ : syracuseStep 6519689 = 4889767) B4889767
theorem B4346459 : Blo 1931435 4346459 := bstep (se 1 (by rfl) ⟨3259844, by rfl⟩ : syracuseStep 4346459 = 6519689) B6519689
theorem B2897639 : Blo 1931435 2897639 := bstep (se 1 (by rfl) ⟨2173229, by rfl⟩ : syracuseStep 2897639 = 4346459) B4346459
theorem B1931759 : Blo 1931435 1931759 := bstep (se 1 (by rfl) ⟨1448819, by rfl⟩ : syracuseStep 1931759 = 2897639) B2897639
theorem B2897645 : Blo 1931435 2897645 := bbase (se 3 (by rfl) ⟨543308, by rfl⟩ : syracuseStep 2897645 = 1086617) (by norm_num)
theorem B1931763 : Blo 1931435 1931763 := bstep (se 1 (by rfl) ⟨1448822, by rfl⟩ : syracuseStep 1931763 = 2897645) B2897645
theorem B4346477 : Blo 1931435 4346477 := bbase (se 3 (by rfl) ⟨814964, by rfl⟩ : syracuseStep 4346477 = 1629929) (by norm_num)
theorem B2897651 : Blo 1931435 2897651 := bstep (se 1 (by rfl) ⟨2173238, by rfl⟩ : syracuseStep 2897651 = 4346477) B4346477
theorem B1931767 : Blo 1931435 1931767 := bstep (se 1 (by rfl) ⟨1448825, by rfl⟩ : syracuseStep 1931767 = 2897651) B2897651
theorem B3667349 : Blo 1931435 3667349 := bbase (se 6 (by rfl) ⟨85953, by rfl⟩ : syracuseStep 3667349 = 171907) (by norm_num)
theorem B2444899 : Blo 1931435 2444899 := bstep (se 1 (by rfl) ⟨1833674, by rfl⟩ : syracuseStep 2444899 = 3667349) B3667349
theorem B3259865 : Blo 1931435 3259865 := bstep (se 2 (by rfl) ⟨1222449, by rfl⟩ : syracuseStep 3259865 = 2444899) B2444899
theorem B2173243 : Blo 1931435 2173243 := bstep (se 1 (by rfl) ⟨1629932, by rfl⟩ : syracuseStep 2173243 = 3259865) B3259865
theorem B2897657 : Blo 1931435 2897657 := bstep (se 2 (by rfl) ⟨1086621, by rfl⟩ : syracuseStep 2897657 = 2173243) B2173243
theorem B1931771 : Blo 1931435 1931771 := bstep (se 1 (by rfl) ⟨1448828, by rfl⟩ : syracuseStep 1931771 = 2897657) B2897657
theorem B12546197 : Blo 1931435 12546197 := bbase (se 6 (by rfl) ⟨294051, by rfl⟩ : syracuseStep 12546197 = 588103) (by norm_num)
theorem B8364131 : Blo 1931435 8364131 := bstep (se 1 (by rfl) ⟨6273098, by rfl⟩ : syracuseStep 8364131 = 12546197) B12546197
theorem B5576087 : Blo 1931435 5576087 := bstep (se 1 (by rfl) ⟨4182065, by rfl⟩ : syracuseStep 5576087 = 8364131) B8364131
theorem B14869565 : Blo 1931435 14869565 := bstep (se 3 (by rfl) ⟨2788043, by rfl⟩ : syracuseStep 14869565 = 5576087) B5576087
theorem B9913043 : Blo 1931435 9913043 := bstep (se 1 (by rfl) ⟨7434782, by rfl⟩ : syracuseStep 9913043 = 14869565) B14869565
theorem B26434781 : Blo 1931435 26434781 := bstep (se 3 (by rfl) ⟨4956521, by rfl⟩ : syracuseStep 26434781 = 9913043) B9913043
theorem B17623187 : Blo 1931435 17623187 := bstep (se 1 (by rfl) ⟨13217390, by rfl⟩ : syracuseStep 17623187 = 26434781) B26434781
theorem B11748791 : Blo 1931435 11748791 := bstep (se 1 (by rfl) ⟨8811593, by rfl⟩ : syracuseStep 11748791 = 17623187) B17623187
theorem B7832527 : Blo 1931435 7832527 := bstep (se 1 (by rfl) ⟨5874395, by rfl⟩ : syracuseStep 7832527 = 11748791) B11748791
theorem B41773477 : Blo 1931435 41773477 := bstep (se 4 (by rfl) ⟨3916263, by rfl⟩ : syracuseStep 41773477 = 7832527) B7832527
theorem B55697969 : Blo 1931435 55697969 := bstep (se 2 (by rfl) ⟨20886738, by rfl⟩ : syracuseStep 55697969 = 41773477) B41773477
theorem B37131979 : Blo 1931435 37131979 := bstep (se 1 (by rfl) ⟨27848984, by rfl⟩ : syracuseStep 37131979 = 55697969) B55697969
theorem B49509305 : Blo 1931435 49509305 := bstep (se 2 (by rfl) ⟨18565989, by rfl⟩ : syracuseStep 49509305 = 37131979) B37131979
theorem B33006203 : Blo 1931435 33006203 := bstep (se 1 (by rfl) ⟨24754652, by rfl⟩ : syracuseStep 33006203 = 49509305) B49509305
theorem B22004135 : Blo 1931435 22004135 := bstep (se 1 (by rfl) ⟨16503101, by rfl⟩ : syracuseStep 22004135 = 33006203) B33006203
theorem B14669423 : Blo 1931435 14669423 := bstep (se 1 (by rfl) ⟨11002067, by rfl⟩ : syracuseStep 14669423 = 22004135) B22004135
theorem B9779615 : Blo 1931435 9779615 := bstep (se 1 (by rfl) ⟨7334711, by rfl⟩ : syracuseStep 9779615 = 14669423) B14669423
theorem B6519743 : Blo 1931435 6519743 := bstep (se 1 (by rfl) ⟨4889807, by rfl⟩ : syracuseStep 6519743 = 9779615) B9779615
theorem B4346495 : Blo 1931435 4346495 := bstep (se 1 (by rfl) ⟨3259871, by rfl⟩ : syracuseStep 4346495 = 6519743) B6519743
theorem B2897663 : Blo 1931435 2897663 := bstep (se 1 (by rfl) ⟨2173247, by rfl⟩ : syracuseStep 2897663 = 4346495) B4346495
theorem B1931775 : Blo 1931435 1931775 := bstep (se 1 (by rfl) ⟨1448831, by rfl⟩ : syracuseStep 1931775 = 2897663) B2897663
theorem B2897669 : Blo 1931435 2897669 := bbase (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) (by norm_num)
theorem B1931779 : Blo 1931435 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B3259885 : Blo 1931435 3259885 := bbase (se 3 (by rfl) ⟨611228, by rfl⟩ : syracuseStep 3259885 = 1222457) (by norm_num)
theorem B4346513 : Blo 1931435 4346513 := bstep (se 2 (by rfl) ⟨1629942, by rfl⟩ : syracuseStep 4346513 = 3259885) B3259885
theorem B2897675 : Blo 1931435 2897675 := bstep (se 1 (by rfl) ⟨2173256, by rfl⟩ : syracuseStep 2897675 = 4346513) B4346513
theorem B1931783 : Blo 1931435 1931783 := bstep (se 1 (by rfl) ⟨1448837, by rfl⟩ : syracuseStep 1931783 = 2897675) B2897675
theorem B2173261 : Blo 1931435 2173261 := bbase (se 3 (by rfl) ⟨407486, by rfl⟩ : syracuseStep 2173261 = 814973) (by norm_num)
theorem B2897681 : Blo 1931435 2897681 := bstep (se 2 (by rfl) ⟨1086630, by rfl⟩ : syracuseStep 2897681 = 2173261) B2173261
theorem B1931787 : Blo 1931435 1931787 := bstep (se 1 (by rfl) ⟨1448840, by rfl⟩ : syracuseStep 1931787 = 2897681) B2897681
theorem B6519797 : Blo 1931435 6519797 := bbase (se 5 (by rfl) ⟨305615, by rfl⟩ : syracuseStep 6519797 = 611231) (by norm_num)
theorem B4346531 : Blo 1931435 4346531 := bstep (se 1 (by rfl) ⟨3259898, by rfl⟩ : syracuseStep 4346531 = 6519797) B6519797
theorem B2897687 : Blo 1931435 2897687 := bstep (se 1 (by rfl) ⟨2173265, by rfl⟩ : syracuseStep 2897687 = 4346531) B4346531
theorem B1931791 : Blo 1931435 1931791 := bstep (se 1 (by rfl) ⟨1448843, by rfl⟩ : syracuseStep 1931791 = 2897687) B2897687
theorem B2897693 : Blo 1931435 2897693 := bbase (se 3 (by rfl) ⟨543317, by rfl⟩ : syracuseStep 2897693 = 1086635) (by norm_num)
theorem B1931795 : Blo 1931435 1931795 := bstep (se 1 (by rfl) ⟨1448846, by rfl⟩ : syracuseStep 1931795 = 2897693) B2897693
theorem B4346549 : Blo 1931435 4346549 := bbase (se 5 (by rfl) ⟨203744, by rfl⟩ : syracuseStep 4346549 = 407489) (by norm_num)
theorem B2897699 : Blo 1931435 2897699 := bstep (se 1 (by rfl) ⟨2173274, by rfl⟩ : syracuseStep 2897699 = 4346549) B4346549
theorem B1931799 : Blo 1931435 1931799 := bstep (se 1 (by rfl) ⟨1448849, by rfl⟩ : syracuseStep 1931799 = 2897699) B2897699
theorem B11002229 : Blo 1931435 11002229 := bbase (se 5 (by rfl) ⟨515729, by rfl⟩ : syracuseStep 11002229 = 1031459) (by norm_num)
theorem B7334819 : Blo 1931435 7334819 := bstep (se 1 (by rfl) ⟨5501114, by rfl⟩ : syracuseStep 7334819 = 11002229) B11002229
theorem B4889879 : Blo 1931435 4889879 := bstep (se 1 (by rfl) ⟨3667409, by rfl⟩ : syracuseStep 4889879 = 7334819) B7334819
theorem B3259919 : Blo 1931435 3259919 := bstep (se 1 (by rfl) ⟨2444939, by rfl⟩ : syracuseStep 3259919 = 4889879) B4889879
theorem B2173279 : Blo 1931435 2173279 := bstep (se 1 (by rfl) ⟨1629959, by rfl⟩ : syracuseStep 2173279 = 3259919) B3259919
theorem B2897705 : Blo 1931435 2897705 := bstep (se 2 (by rfl) ⟨1086639, by rfl⟩ : syracuseStep 2897705 = 2173279) B2173279
theorem B1931803 : Blo 1931435 1931803 := bstep (se 1 (by rfl) ⟨1448852, by rfl⟩ : syracuseStep 1931803 = 2897705) B2897705
theorem B5501125 : Blo 1931435 5501125 := bbase (se 4 (by rfl) ⟨515730, by rfl⟩ : syracuseStep 5501125 = 1031461) (by norm_num)
theorem B7334833 : Blo 1931435 7334833 := bstep (se 2 (by rfl) ⟨2750562, by rfl⟩ : syracuseStep 7334833 = 5501125) B5501125
theorem B9779777 : Blo 1931435 9779777 := bstep (se 2 (by rfl) ⟨3667416, by rfl⟩ : syracuseStep 9779777 = 7334833) B7334833
theorem B6519851 : Blo 1931435 6519851 := bstep (se 1 (by rfl) ⟨4889888, by rfl⟩ : syracuseStep 6519851 = 9779777) B9779777
theorem B4346567 : Blo 1931435 4346567 := bstep (se 1 (by rfl) ⟨3259925, by rfl⟩ : syracuseStep 4346567 = 6519851) B6519851
theorem B2897711 : Blo 1931435 2897711 := bstep (se 1 (by rfl) ⟨2173283, by rfl⟩ : syracuseStep 2897711 = 4346567) B4346567
theorem B1931807 : Blo 1931435 1931807 := bstep (se 1 (by rfl) ⟨1448855, by rfl⟩ : syracuseStep 1931807 = 2897711) B2897711
theorem B2897717 : Blo 1931435 2897717 := bbase (se 5 (by rfl) ⟨135830, by rfl⟩ : syracuseStep 2897717 = 271661) (by norm_num)
theorem B1931811 : Blo 1931435 1931811 := bstep (se 1 (by rfl) ⟨1448858, by rfl⟩ : syracuseStep 1931811 = 2897717) B2897717
theorem B4889909 : Blo 1931435 4889909 := bbase (se 5 (by rfl) ⟨229214, by rfl⟩ : syracuseStep 4889909 = 458429) (by norm_num)
theorem B3259939 : Blo 1931435 3259939 := bstep (se 1 (by rfl) ⟨2444954, by rfl⟩ : syracuseStep 3259939 = 4889909) B4889909
theorem B4346585 : Blo 1931435 4346585 := bstep (se 2 (by rfl) ⟨1629969, by rfl⟩ : syracuseStep 4346585 = 3259939) B3259939
theorem B2897723 : Blo 1931435 2897723 := bstep (se 1 (by rfl) ⟨2173292, by rfl⟩ : syracuseStep 2897723 = 4346585) B4346585
theorem B1931815 : Blo 1931435 1931815 := bstep (se 1 (by rfl) ⟨1448861, by rfl⟩ : syracuseStep 1931815 = 2897723) B2897723
theorem B2173297 : Blo 1931435 2173297 := bbase (se 2 (by rfl) ⟨814986, by rfl⟩ : syracuseStep 2173297 = 1629973) (by norm_num)
theorem B2897729 : Blo 1931435 2897729 := bstep (se 2 (by rfl) ⟨1086648, by rfl⟩ : syracuseStep 2897729 = 2173297) B2173297
theorem B1931819 : Blo 1931435 1931819 := bstep (se 1 (by rfl) ⟨1448864, by rfl⟩ : syracuseStep 1931819 = 2897729) B2897729
theorem B4405909 : Blo 1931435 4405909 := bbase (se 6 (by rfl) ⟨103263, by rfl⟩ : syracuseStep 4405909 = 206527) (by norm_num)
theorem B5874545 : Blo 1931435 5874545 := bstep (se 2 (by rfl) ⟨2202954, by rfl⟩ : syracuseStep 5874545 = 4405909) B4405909
theorem B3916363 : Blo 1931435 3916363 := bstep (se 1 (by rfl) ⟨2937272, by rfl⟩ : syracuseStep 3916363 = 5874545) B5874545
theorem B5221817 : Blo 1931435 5221817 := bstep (se 2 (by rfl) ⟨1958181, by rfl⟩ : syracuseStep 5221817 = 3916363) B3916363
theorem B3481211 : Blo 1931435 3481211 := bstep (se 1 (by rfl) ⟨2610908, by rfl⟩ : syracuseStep 3481211 = 5221817) B5221817
theorem B2320807 : Blo 1931435 2320807 := bstep (se 1 (by rfl) ⟨1740605, by rfl⟩ : syracuseStep 2320807 = 3481211) B3481211
theorem B3094409 : Blo 1931435 3094409 := bstep (se 2 (by rfl) ⟨1160403, by rfl⟩ : syracuseStep 3094409 = 2320807) B2320807
theorem B8251757 : Blo 1931435 8251757 := bstep (se 3 (by rfl) ⟨1547204, by rfl⟩ : syracuseStep 8251757 = 3094409) B3094409
theorem B5501171 : Blo 1931435 5501171 := bstep (se 1 (by rfl) ⟨4125878, by rfl⟩ : syracuseStep 5501171 = 8251757) B8251757
theorem B3667447 : Blo 1931435 3667447 := bstep (se 1 (by rfl) ⟨2750585, by rfl⟩ : syracuseStep 3667447 = 5501171) B5501171
theorem B4889929 : Blo 1931435 4889929 := bstep (se 2 (by rfl) ⟨1833723, by rfl⟩ : syracuseStep 4889929 = 3667447) B3667447
theorem B6519905 : Blo 1931435 6519905 := bstep (se 2 (by rfl) ⟨2444964, by rfl⟩ : syracuseStep 6519905 = 4889929) B4889929
theorem B4346603 : Blo 1931435 4346603 := bstep (se 1 (by rfl) ⟨3259952, by rfl⟩ : syracuseStep 4346603 = 6519905) B6519905
theorem B2897735 : Blo 1931435 2897735 := bstep (se 1 (by rfl) ⟨2173301, by rfl⟩ : syracuseStep 2897735 = 4346603) B4346603
theorem B1931823 : Blo 1931435 1931823 := bstep (se 1 (by rfl) ⟨1448867, by rfl⟩ : syracuseStep 1931823 = 2897735) B2897735
theorem B2897741 : Blo 1931435 2897741 := bbase (se 3 (by rfl) ⟨543326, by rfl⟩ : syracuseStep 2897741 = 1086653) (by norm_num)
theorem B1931827 : Blo 1931435 1931827 := bstep (se 1 (by rfl) ⟨1448870, by rfl⟩ : syracuseStep 1931827 = 2897741) B2897741
theorem B4346621 : Blo 1931435 4346621 := bbase (se 3 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 4346621 = 1629983) (by norm_num)
theorem B2897747 : Blo 1931435 2897747 := bstep (se 1 (by rfl) ⟨2173310, by rfl⟩ : syracuseStep 2897747 = 4346621) B4346621
theorem B1931831 : Blo 1931435 1931831 := bstep (se 1 (by rfl) ⟨1448873, by rfl⟩ : syracuseStep 1931831 = 2897747) B2897747
theorem B3259973 : Blo 1931435 3259973 := bbase (se 4 (by rfl) ⟨305622, by rfl⟩ : syracuseStep 3259973 = 611245) (by norm_num)
theorem B2173315 : Blo 1931435 2173315 := bstep (se 1 (by rfl) ⟨1629986, by rfl⟩ : syracuseStep 2173315 = 3259973) B3259973
theorem B2897753 : Blo 1931435 2897753 := bstep (se 2 (by rfl) ⟨1086657, by rfl⟩ : syracuseStep 2897753 = 2173315) B2173315
theorem B1931835 : Blo 1931435 1931835 := bstep (se 1 (by rfl) ⟨1448876, by rfl⟩ : syracuseStep 1931835 = 2897753) B2897753
theorem B14669909 : Blo 1931435 14669909 := bbase (se 8 (by rfl) ⟨85956, by rfl⟩ : syracuseStep 14669909 = 171913) (by norm_num)
theorem B9779939 : Blo 1931435 9779939 := bstep (se 1 (by rfl) ⟨7334954, by rfl⟩ : syracuseStep 9779939 = 14669909) B14669909
theorem B6519959 : Blo 1931435 6519959 := bstep (se 1 (by rfl) ⟨4889969, by rfl⟩ : syracuseStep 6519959 = 9779939) B9779939
theorem B4346639 : Blo 1931435 4346639 := bstep (se 1 (by rfl) ⟨3259979, by rfl⟩ : syracuseStep 4346639 = 6519959) B6519959
theorem B2897759 : Blo 1931435 2897759 := bstep (se 1 (by rfl) ⟨2173319, by rfl⟩ : syracuseStep 2897759 = 4346639) B4346639
theorem B1931839 : Blo 1931435 1931839 := bstep (se 1 (by rfl) ⟨1448879, by rfl⟩ : syracuseStep 1931839 = 2897759) B2897759
theorem B2897765 : Blo 1931435 2897765 := bbase (se 4 (by rfl) ⟨271665, by rfl⟩ : syracuseStep 2897765 = 543331) (by norm_num)
theorem B1931843 : Blo 1931435 1931843 := bstep (se 1 (by rfl) ⟨1448882, by rfl⟩ : syracuseStep 1931843 = 2897765) B2897765
theorem B3667493 : Blo 1931435 3667493 := bbase (se 4 (by rfl) ⟨343827, by rfl⟩ : syracuseStep 3667493 = 687655) (by norm_num)
theorem B2444995 : Blo 1931435 2444995 := bstep (se 1 (by rfl) ⟨1833746, by rfl⟩ : syracuseStep 2444995 = 3667493) B3667493
theorem B3259993 : Blo 1931435 3259993 := bstep (se 2 (by rfl) ⟨1222497, by rfl⟩ : syracuseStep 3259993 = 2444995) B2444995
theorem B4346657 : Blo 1931435 4346657 := bstep (se 2 (by rfl) ⟨1629996, by rfl⟩ : syracuseStep 4346657 = 3259993) B3259993
theorem B2897771 : Blo 1931435 2897771 := bstep (se 1 (by rfl) ⟨2173328, by rfl⟩ : syracuseStep 2897771 = 4346657) B4346657
theorem B1931847 : Blo 1931435 1931847 := bstep (se 1 (by rfl) ⟨1448885, by rfl⟩ : syracuseStep 1931847 = 2897771) B2897771
theorem B2173333 : Blo 1931435 2173333 := bbase (se 6 (by rfl) ⟨50937, by rfl⟩ : syracuseStep 2173333 = 101875) (by norm_num)
theorem B2897777 : Blo 1931435 2897777 := bstep (se 2 (by rfl) ⟨1086666, by rfl⟩ : syracuseStep 2897777 = 2173333) B2173333
theorem B1931851 : Blo 1931435 1931851 := bstep (se 1 (by rfl) ⟨1448888, by rfl⟩ : syracuseStep 1931851 = 2897777) B2897777
theorem B2445005 : Blo 1931435 2445005 := bbase (se 3 (by rfl) ⟨458438, by rfl⟩ : syracuseStep 2445005 = 916877) (by norm_num)
theorem B6520013 : Blo 1931435 6520013 := bstep (se 3 (by rfl) ⟨1222502, by rfl⟩ : syracuseStep 6520013 = 2445005) B2445005
theorem B4346675 : Blo 1931435 4346675 := bstep (se 1 (by rfl) ⟨3260006, by rfl⟩ : syracuseStep 4346675 = 6520013) B6520013
theorem B2897783 : Blo 1931435 2897783 := bstep (se 1 (by rfl) ⟨2173337, by rfl⟩ : syracuseStep 2897783 = 4346675) B4346675
theorem B1931855 : Blo 1931435 1931855 := bstep (se 1 (by rfl) ⟨1448891, by rfl⟩ : syracuseStep 1931855 = 2897783) B2897783
theorem B2897789 : Blo 1931435 2897789 := bbase (se 3 (by rfl) ⟨543335, by rfl⟩ : syracuseStep 2897789 = 1086671) (by norm_num)
theorem B1931859 : Blo 1931435 1931859 := bstep (se 1 (by rfl) ⟨1448894, by rfl⟩ : syracuseStep 1931859 = 2897789) B2897789
theorem B4346693 : Blo 1931435 4346693 := bbase (se 4 (by rfl) ⟨407502, by rfl⟩ : syracuseStep 4346693 = 815005) (by norm_num)
theorem B2897795 : Blo 1931435 2897795 := bstep (se 1 (by rfl) ⟨2173346, by rfl⟩ : syracuseStep 2897795 = 4346693) B4346693
theorem B1931863 : Blo 1931435 1931863 := bstep (se 1 (by rfl) ⟨1448897, by rfl⟩ : syracuseStep 1931863 = 2897795) B2897795
theorem B4125973 : Blo 1931435 4125973 := bbase (se 6 (by rfl) ⟨96702, by rfl⟩ : syracuseStep 4125973 = 193405) (by norm_num)
theorem B5501297 : Blo 1931435 5501297 := bstep (se 2 (by rfl) ⟨2062986, by rfl⟩ : syracuseStep 5501297 = 4125973) B4125973
theorem B3667531 : Blo 1931435 3667531 := bstep (se 1 (by rfl) ⟨2750648, by rfl⟩ : syracuseStep 3667531 = 5501297) B5501297
theorem B4890041 : Blo 1931435 4890041 := bstep (se 2 (by rfl) ⟨1833765, by rfl⟩ : syracuseStep 4890041 = 3667531) B3667531
theorem B3260027 : Blo 1931435 3260027 := bstep (se 1 (by rfl) ⟨2445020, by rfl⟩ : syracuseStep 3260027 = 4890041) B4890041
theorem B2173351 : Blo 1931435 2173351 := bstep (se 1 (by rfl) ⟨1630013, by rfl⟩ : syracuseStep 2173351 = 3260027) B3260027
theorem B2897801 : Blo 1931435 2897801 := bstep (se 2 (by rfl) ⟨1086675, by rfl⟩ : syracuseStep 2897801 = 2173351) B2173351
theorem B1931867 : Blo 1931435 1931867 := bstep (se 1 (by rfl) ⟨1448900, by rfl⟩ : syracuseStep 1931867 = 2897801) B2897801
theorem B9780101 : Blo 1931435 9780101 := bbase (se 4 (by rfl) ⟨916884, by rfl⟩ : syracuseStep 9780101 = 1833769) (by norm_num)
theorem B6520067 : Blo 1931435 6520067 := bstep (se 1 (by rfl) ⟨4890050, by rfl⟩ : syracuseStep 6520067 = 9780101) B9780101
theorem B4346711 : Blo 1931435 4346711 := bstep (se 1 (by rfl) ⟨3260033, by rfl⟩ : syracuseStep 4346711 = 6520067) B6520067
theorem B2897807 : Blo 1931435 2897807 := bstep (se 1 (by rfl) ⟨2173355, by rfl⟩ : syracuseStep 2897807 = 4346711) B4346711
theorem B1931871 : Blo 1931435 1931871 := bstep (se 1 (by rfl) ⟨1448903, by rfl⟩ : syracuseStep 1931871 = 2897807) B2897807
theorem B2897813 : Blo 1931435 2897813 := bbase (se 6 (by rfl) ⟨67917, by rfl⟩ : syracuseStep 2897813 = 135835) (by norm_num)
theorem B1931875 : Blo 1931435 1931875 := bstep (se 1 (by rfl) ⟨1448906, by rfl⟩ : syracuseStep 1931875 = 2897813) B2897813
theorem B4641749 : Blo 1931435 4641749 := bbase (se 7 (by rfl) ⟨54395, by rfl⟩ : syracuseStep 4641749 = 108791) (by norm_num)
theorem B3094499 : Blo 1931435 3094499 := bstep (se 1 (by rfl) ⟨2320874, by rfl⟩ : syracuseStep 3094499 = 4641749) B4641749
theorem B2062999 : Blo 1931435 2062999 := bstep (se 1 (by rfl) ⟨1547249, by rfl⟩ : syracuseStep 2062999 = 3094499) B3094499
theorem B11002661 : Blo 1931435 11002661 := bstep (se 4 (by rfl) ⟨1031499, by rfl⟩ : syracuseStep 11002661 = 2062999) B2062999
theorem B7335107 : Blo 1931435 7335107 := bstep (se 1 (by rfl) ⟨5501330, by rfl⟩ : syracuseStep 7335107 = 11002661) B11002661
theorem B4890071 : Blo 1931435 4890071 := bstep (se 1 (by rfl) ⟨3667553, by rfl⟩ : syracuseStep 4890071 = 7335107) B7335107
theorem B3260047 : Blo 1931435 3260047 := bstep (se 1 (by rfl) ⟨2445035, by rfl⟩ : syracuseStep 3260047 = 4890071) B4890071
theorem B4346729 : Blo 1931435 4346729 := bstep (se 2 (by rfl) ⟨1630023, by rfl⟩ : syracuseStep 4346729 = 3260047) B3260047
theorem B2897819 : Blo 1931435 2897819 := bstep (se 1 (by rfl) ⟨2173364, by rfl⟩ : syracuseStep 2897819 = 4346729) B4346729
theorem B1931879 : Blo 1931435 1931879 := bstep (se 1 (by rfl) ⟨1448909, by rfl⟩ : syracuseStep 1931879 = 2897819) B2897819
theorem B2173369 : Blo 1931435 2173369 := bbase (se 2 (by rfl) ⟨815013, by rfl⟩ : syracuseStep 2173369 = 1630027) (by norm_num)
theorem B2897825 : Blo 1931435 2897825 := bstep (se 2 (by rfl) ⟨1086684, by rfl⟩ : syracuseStep 2897825 = 2173369) B2173369
theorem B1931883 : Blo 1931435 1931883 := bstep (se 1 (by rfl) ⟨1448912, by rfl⟩ : syracuseStep 1931883 = 2897825) B2897825
theorem B17624213 : Blo 1931435 17624213 := bbase (se 6 (by rfl) ⟨413067, by rfl⟩ : syracuseStep 17624213 = 826135) (by norm_num)
theorem B11749475 : Blo 1931435 11749475 := bstep (se 1 (by rfl) ⟨8812106, by rfl⟩ : syracuseStep 11749475 = 17624213) B17624213
theorem B31331933 : Blo 1931435 31331933 := bstep (se 3 (by rfl) ⟨5874737, by rfl⟩ : syracuseStep 31331933 = 11749475) B11749475
theorem B20887955 : Blo 1931435 20887955 := bstep (se 1 (by rfl) ⟨15665966, by rfl⟩ : syracuseStep 20887955 = 31331933) B31331933
theorem B13925303 : Blo 1931435 13925303 := bstep (se 1 (by rfl) ⟨10443977, by rfl⟩ : syracuseStep 13925303 = 20887955) B20887955
theorem B9283535 : Blo 1931435 9283535 := bstep (se 1 (by rfl) ⟨6962651, by rfl⟩ : syracuseStep 9283535 = 13925303) B13925303
theorem B6189023 : Blo 1931435 6189023 := bstep (se 1 (by rfl) ⟨4641767, by rfl⟩ : syracuseStep 6189023 = 9283535) B9283535
theorem B4126015 : Blo 1931435 4126015 := bstep (se 1 (by rfl) ⟨3094511, by rfl⟩ : syracuseStep 4126015 = 6189023) B6189023
theorem B5501353 : Blo 1931435 5501353 := bstep (se 2 (by rfl) ⟨2063007, by rfl⟩ : syracuseStep 5501353 = 4126015) B4126015
theorem B7335137 : Blo 1931435 7335137 := bstep (se 2 (by rfl) ⟨2750676, by rfl⟩ : syracuseStep 7335137 = 5501353) B5501353
theorem B4890091 : Blo 1931435 4890091 := bstep (se 1 (by rfl) ⟨3667568, by rfl⟩ : syracuseStep 4890091 = 7335137) B7335137
theorem B6520121 : Blo 1931435 6520121 := bstep (se 2 (by rfl) ⟨2445045, by rfl⟩ : syracuseStep 6520121 = 4890091) B4890091
theorem B4346747 : Blo 1931435 4346747 := bstep (se 1 (by rfl) ⟨3260060, by rfl⟩ : syracuseStep 4346747 = 6520121) B6520121
theorem B2897831 : Blo 1931435 2897831 := bstep (se 1 (by rfl) ⟨2173373, by rfl⟩ : syracuseStep 2897831 = 4346747) B4346747
theorem B1931887 : Blo 1931435 1931887 := bstep (se 1 (by rfl) ⟨1448915, by rfl⟩ : syracuseStep 1931887 = 2897831) B2897831
theorem B2897837 : Blo 1931435 2897837 := bbase (se 3 (by rfl) ⟨543344, by rfl⟩ : syracuseStep 2897837 = 1086689) (by norm_num)
theorem B1931891 : Blo 1931435 1931891 := bstep (se 1 (by rfl) ⟨1448918, by rfl⟩ : syracuseStep 1931891 = 2897837) B2897837
theorem B4346765 : Blo 1931435 4346765 := bbase (se 3 (by rfl) ⟨815018, by rfl⟩ : syracuseStep 4346765 = 1630037) (by norm_num)
theorem B2897843 : Blo 1931435 2897843 := bstep (se 1 (by rfl) ⟨2173382, by rfl⟩ : syracuseStep 2897843 = 4346765) B4346765
theorem B1931895 : Blo 1931435 1931895 := bstep (se 1 (by rfl) ⟨1448921, by rfl⟩ : syracuseStep 1931895 = 2897843) B2897843
theorem B2445061 : Blo 1931435 2445061 := bbase (se 4 (by rfl) ⟨229224, by rfl⟩ : syracuseStep 2445061 = 458449) (by norm_num)
theorem B3260081 : Blo 1931435 3260081 := bstep (se 2 (by rfl) ⟨1222530, by rfl⟩ : syracuseStep 3260081 = 2445061) B2445061
theorem B2173387 : Blo 1931435 2173387 := bstep (se 1 (by rfl) ⟨1630040, by rfl⟩ : syracuseStep 2173387 = 3260081) B3260081
theorem B2897849 : Blo 1931435 2897849 := bstep (se 2 (by rfl) ⟨1086693, by rfl⟩ : syracuseStep 2897849 = 2173387) B2173387
theorem B1931899 : Blo 1931435 1931899 := bstep (se 1 (by rfl) ⟨1448924, by rfl⟩ : syracuseStep 1931899 = 2897849) B2897849
theorem B4641805 : Blo 1931435 4641805 := bbase (se 3 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 4641805 = 1740677) (by norm_num)
theorem B24756293 : Blo 1931435 24756293 := bstep (se 4 (by rfl) ⟨2320902, by rfl⟩ : syracuseStep 24756293 = 4641805) B4641805
theorem B16504195 : Blo 1931435 16504195 := bstep (se 1 (by rfl) ⟨12378146, by rfl⟩ : syracuseStep 16504195 = 24756293) B24756293
theorem B22005593 : Blo 1931435 22005593 := bstep (se 2 (by rfl) ⟨8252097, by rfl⟩ : syracuseStep 22005593 = 16504195) B16504195
theorem B14670395 : Blo 1931435 14670395 := bstep (se 1 (by rfl) ⟨11002796, by rfl⟩ : syracuseStep 14670395 = 22005593) B22005593
theorem B9780263 : Blo 1931435 9780263 := bstep (se 1 (by rfl) ⟨7335197, by rfl⟩ : syracuseStep 9780263 = 14670395) B14670395
theorem B6520175 : Blo 1931435 6520175 := bstep (se 1 (by rfl) ⟨4890131, by rfl⟩ : syracuseStep 6520175 = 9780263) B9780263
theorem B4346783 : Blo 1931435 4346783 := bstep (se 1 (by rfl) ⟨3260087, by rfl⟩ : syracuseStep 4346783 = 6520175) B6520175
theorem B2897855 : Blo 1931435 2897855 := bstep (se 1 (by rfl) ⟨2173391, by rfl⟩ : syracuseStep 2897855 = 4346783) B4346783
theorem B1931903 : Blo 1931435 1931903 := bstep (se 1 (by rfl) ⟨1448927, by rfl⟩ : syracuseStep 1931903 = 2897855) B2897855
theorem B2897861 : Blo 1931435 2897861 := bbase (se 4 (by rfl) ⟨271674, by rfl⟩ : syracuseStep 2897861 = 543349) (by norm_num)
theorem B1931907 : Blo 1931435 1931907 := bstep (se 1 (by rfl) ⟨1448930, by rfl⟩ : syracuseStep 1931907 = 2897861) B2897861
theorem B3260101 : Blo 1931435 3260101 := bbase (se 4 (by rfl) ⟨305634, by rfl⟩ : syracuseStep 3260101 = 611269) (by norm_num)
theorem B4346801 : Blo 1931435 4346801 := bstep (se 2 (by rfl) ⟨1630050, by rfl⟩ : syracuseStep 4346801 = 3260101) B3260101
theorem B2897867 : Blo 1931435 2897867 := bstep (se 1 (by rfl) ⟨2173400, by rfl⟩ : syracuseStep 2897867 = 4346801) B4346801
theorem B1931911 : Blo 1931435 1931911 := bstep (se 1 (by rfl) ⟨1448933, by rfl⟩ : syracuseStep 1931911 = 2897867) B2897867
theorem B2173405 : Blo 1931435 2173405 := bbase (se 3 (by rfl) ⟨407513, by rfl⟩ : syracuseStep 2173405 = 815027) (by norm_num)
theorem B2897873 : Blo 1931435 2897873 := bstep (se 2 (by rfl) ⟨1086702, by rfl⟩ : syracuseStep 2897873 = 2173405) B2173405
theorem B1931915 : Blo 1931435 1931915 := bstep (se 1 (by rfl) ⟨1448936, by rfl⟩ : syracuseStep 1931915 = 2897873) B2897873
theorem B6520229 : Blo 1931435 6520229 := bbase (se 4 (by rfl) ⟨611271, by rfl⟩ : syracuseStep 6520229 = 1222543) (by norm_num)
theorem B4346819 : Blo 1931435 4346819 := bstep (se 1 (by rfl) ⟨3260114, by rfl⟩ : syracuseStep 4346819 = 6520229) B6520229
theorem B2897879 : Blo 1931435 2897879 := bstep (se 1 (by rfl) ⟨2173409, by rfl⟩ : syracuseStep 2897879 = 4346819) B4346819
theorem B1931919 : Blo 1931435 1931919 := bstep (se 1 (by rfl) ⟨1448939, by rfl⟩ : syracuseStep 1931919 = 2897879) B2897879
theorem B2897885 : Blo 1931435 2897885 := bbase (se 3 (by rfl) ⟨543353, by rfl⟩ : syracuseStep 2897885 = 1086707) (by norm_num)
theorem B1931923 : Blo 1931435 1931923 := bstep (se 1 (by rfl) ⟨1448942, by rfl⟩ : syracuseStep 1931923 = 2897885) B2897885
theorem B4346837 : Blo 1931435 4346837 := bbase (se 7 (by rfl) ⟨50939, by rfl⟩ : syracuseStep 4346837 = 101879) (by norm_num)
theorem B2897891 : Blo 1931435 2897891 := bstep (se 1 (by rfl) ⟨2173418, by rfl⟩ : syracuseStep 2897891 = 4346837) B4346837
theorem B1931927 : Blo 1931435 1931927 := bstep (se 1 (by rfl) ⟨1448945, by rfl⟩ : syracuseStep 1931927 = 2897891) B2897891
theorem B13925621 : Blo 1931435 13925621 := bbase (se 5 (by rfl) ⟨652763, by rfl⟩ : syracuseStep 13925621 = 1305527) (by norm_num)
theorem B9283747 : Blo 1931435 9283747 := bstep (se 1 (by rfl) ⟨6962810, by rfl⟩ : syracuseStep 9283747 = 13925621) B13925621
theorem B12378329 : Blo 1931435 12378329 := bstep (se 2 (by rfl) ⟨4641873, by rfl⟩ : syracuseStep 12378329 = 9283747) B9283747
theorem B8252219 : Blo 1931435 8252219 := bstep (se 1 (by rfl) ⟨6189164, by rfl⟩ : syracuseStep 8252219 = 12378329) B12378329
theorem B5501479 : Blo 1931435 5501479 := bstep (se 1 (by rfl) ⟨4126109, by rfl⟩ : syracuseStep 5501479 = 8252219) B8252219
theorem B7335305 : Blo 1931435 7335305 := bstep (se 2 (by rfl) ⟨2750739, by rfl⟩ : syracuseStep 7335305 = 5501479) B5501479
theorem B4890203 : Blo 1931435 4890203 := bstep (se 1 (by rfl) ⟨3667652, by rfl⟩ : syracuseStep 4890203 = 7335305) B7335305
theorem B3260135 : Blo 1931435 3260135 := bstep (se 1 (by rfl) ⟨2445101, by rfl⟩ : syracuseStep 3260135 = 4890203) B4890203
theorem B2173423 : Blo 1931435 2173423 := bstep (se 1 (by rfl) ⟨1630067, by rfl⟩ : syracuseStep 2173423 = 3260135) B3260135
theorem B2897897 : Blo 1931435 2897897 := bstep (se 2 (by rfl) ⟨1086711, by rfl⟩ : syracuseStep 2897897 = 2173423) B2173423
theorem B1931931 : Blo 1931435 1931931 := bstep (se 1 (by rfl) ⟨1448948, by rfl⟩ : syracuseStep 1931931 = 2897897) B2897897
theorem B16504469 : Blo 1931435 16504469 := bbase (se 6 (by rfl) ⟨386823, by rfl⟩ : syracuseStep 16504469 = 773647) (by norm_num)
theorem B11002979 : Blo 1931435 11002979 := bstep (se 1 (by rfl) ⟨8252234, by rfl⟩ : syracuseStep 11002979 = 16504469) B16504469
theorem B7335319 : Blo 1931435 7335319 := bstep (se 1 (by rfl) ⟨5501489, by rfl⟩ : syracuseStep 7335319 = 11002979) B11002979
theorem B9780425 : Blo 1931435 9780425 := bstep (se 2 (by rfl) ⟨3667659, by rfl⟩ : syracuseStep 9780425 = 7335319) B7335319
theorem B6520283 : Blo 1931435 6520283 := bstep (se 1 (by rfl) ⟨4890212, by rfl⟩ : syracuseStep 6520283 = 9780425) B9780425
theorem B4346855 : Blo 1931435 4346855 := bstep (se 1 (by rfl) ⟨3260141, by rfl⟩ : syracuseStep 4346855 = 6520283) B6520283
theorem B2897903 : Blo 1931435 2897903 := bstep (se 1 (by rfl) ⟨2173427, by rfl⟩ : syracuseStep 2897903 = 4346855) B4346855
theorem B1931935 : Blo 1931435 1931935 := bstep (se 1 (by rfl) ⟨1448951, by rfl⟩ : syracuseStep 1931935 = 2897903) B2897903
theorem B2897909 : Blo 1931435 2897909 := bbase (se 5 (by rfl) ⟨135839, by rfl⟩ : syracuseStep 2897909 = 271679) (by norm_num)
theorem B1931939 : Blo 1931435 1931939 := bstep (se 1 (by rfl) ⟨1448954, by rfl⟩ : syracuseStep 1931939 = 2897909) B2897909
theorem B4705237 : Blo 1931435 4705237 := bbase (se 7 (by rfl) ⟨55139, by rfl⟩ : syracuseStep 4705237 = 110279) (by norm_num)
theorem B6273649 : Blo 1931435 6273649 := bstep (se 2 (by rfl) ⟨2352618, by rfl⟩ : syracuseStep 6273649 = 4705237) B4705237
theorem B8364865 : Blo 1931435 8364865 := bstep (se 2 (by rfl) ⟨3136824, by rfl⟩ : syracuseStep 8364865 = 6273649) B6273649
theorem B11153153 : Blo 1931435 11153153 := bstep (se 2 (by rfl) ⟨4182432, by rfl⟩ : syracuseStep 11153153 = 8364865) B8364865
theorem B7435435 : Blo 1931435 7435435 := bstep (se 1 (by rfl) ⟨5576576, by rfl⟩ : syracuseStep 7435435 = 11153153) B11153153
theorem B9913913 : Blo 1931435 9913913 := bstep (se 2 (by rfl) ⟨3717717, by rfl⟩ : syracuseStep 9913913 = 7435435) B7435435
theorem B6609275 : Blo 1931435 6609275 := bstep (se 1 (by rfl) ⟨4956956, by rfl⟩ : syracuseStep 6609275 = 9913913) B9913913
theorem B4406183 : Blo 1931435 4406183 := bstep (se 1 (by rfl) ⟨3304637, by rfl⟩ : syracuseStep 4406183 = 6609275) B6609275
theorem B2937455 : Blo 1931435 2937455 := bstep (se 1 (by rfl) ⟨2203091, by rfl⟩ : syracuseStep 2937455 = 4406183) B4406183
theorem B1958303 : Blo 1931435 1958303 := bstep (se 1 (by rfl) ⟨1468727, by rfl⟩ : syracuseStep 1958303 = 2937455) B2937455
theorem B5222141 : Blo 1931435 5222141 := bstep (se 3 (by rfl) ⟨979151, by rfl⟩ : syracuseStep 5222141 = 1958303) B1958303
theorem B3481427 : Blo 1931435 3481427 := bstep (se 1 (by rfl) ⟨2611070, by rfl⟩ : syracuseStep 3481427 = 5222141) B5222141
theorem B9283805 : Blo 1931435 9283805 := bstep (se 3 (by rfl) ⟨1740713, by rfl⟩ : syracuseStep 9283805 = 3481427) B3481427
theorem B6189203 : Blo 1931435 6189203 := bstep (se 1 (by rfl) ⟨4641902, by rfl⟩ : syracuseStep 6189203 = 9283805) B9283805
theorem B4126135 : Blo 1931435 4126135 := bstep (se 1 (by rfl) ⟨3094601, by rfl⟩ : syracuseStep 4126135 = 6189203) B6189203
theorem B5501513 : Blo 1931435 5501513 := bstep (se 2 (by rfl) ⟨2063067, by rfl⟩ : syracuseStep 5501513 = 4126135) B4126135
theorem B3667675 : Blo 1931435 3667675 := bstep (se 1 (by rfl) ⟨2750756, by rfl⟩ : syracuseStep 3667675 = 5501513) B5501513
theorem B4890233 : Blo 1931435 4890233 := bstep (se 2 (by rfl) ⟨1833837, by rfl⟩ : syracuseStep 4890233 = 3667675) B3667675
theorem B3260155 : Blo 1931435 3260155 := bstep (se 1 (by rfl) ⟨2445116, by rfl⟩ : syracuseStep 3260155 = 4890233) B4890233
theorem B4346873 : Blo 1931435 4346873 := bstep (se 2 (by rfl) ⟨1630077, by rfl⟩ : syracuseStep 4346873 = 3260155) B3260155
theorem B2897915 : Blo 1931435 2897915 := bstep (se 1 (by rfl) ⟨2173436, by rfl⟩ : syracuseStep 2897915 = 4346873) B4346873
theorem B1931943 : Blo 1931435 1931943 := bstep (se 1 (by rfl) ⟨1448957, by rfl⟩ : syracuseStep 1931943 = 2897915) B2897915
theorem B2173441 : Blo 1931435 2173441 := bbase (se 2 (by rfl) ⟨815040, by rfl⟩ : syracuseStep 2173441 = 1630081) (by norm_num)
theorem B2897921 : Blo 1931435 2897921 := bstep (se 2 (by rfl) ⟨1086720, by rfl⟩ : syracuseStep 2897921 = 2173441) B2173441
theorem B1931947 : Blo 1931435 1931947 := bstep (se 1 (by rfl) ⟨1448960, by rfl⟩ : syracuseStep 1931947 = 2897921) B2897921
theorem B4890253 : Blo 1931435 4890253 := bbase (se 3 (by rfl) ⟨916922, by rfl⟩ : syracuseStep 4890253 = 1833845) (by norm_num)
theorem B6520337 : Blo 1931435 6520337 := bstep (se 2 (by rfl) ⟨2445126, by rfl⟩ : syracuseStep 6520337 = 4890253) B4890253
theorem B4346891 : Blo 1931435 4346891 := bstep (se 1 (by rfl) ⟨3260168, by rfl⟩ : syracuseStep 4346891 = 6520337) B6520337
theorem B2897927 : Blo 1931435 2897927 := bstep (se 1 (by rfl) ⟨2173445, by rfl⟩ : syracuseStep 2897927 = 4346891) B4346891
theorem B1931951 : Blo 1931435 1931951 := bstep (se 1 (by rfl) ⟨1448963, by rfl⟩ : syracuseStep 1931951 = 2897927) B2897927
theorem B2897933 : Blo 1931435 2897933 := bbase (se 3 (by rfl) ⟨543362, by rfl⟩ : syracuseStep 2897933 = 1086725) (by norm_num)
theorem B1931955 : Blo 1931435 1931955 := bstep (se 1 (by rfl) ⟨1448966, by rfl⟩ : syracuseStep 1931955 = 2897933) B2897933
theorem B4346909 : Blo 1931435 4346909 := bbase (se 3 (by rfl) ⟨815045, by rfl⟩ : syracuseStep 4346909 = 1630091) (by norm_num)
theorem B2897939 : Blo 1931435 2897939 := bstep (se 1 (by rfl) ⟨2173454, by rfl⟩ : syracuseStep 2897939 = 4346909) B4346909
theorem B1931959 : Blo 1931435 1931959 := bstep (se 1 (by rfl) ⟨1448969, by rfl⟩ : syracuseStep 1931959 = 2897939) B2897939
theorem B3260189 : Blo 1931435 3260189 := bbase (se 3 (by rfl) ⟨611285, by rfl⟩ : syracuseStep 3260189 = 1222571) (by norm_num)
theorem B2173459 : Blo 1931435 2173459 := bstep (se 1 (by rfl) ⟨1630094, by rfl⟩ : syracuseStep 2173459 = 3260189) B3260189
theorem B2897945 : Blo 1931435 2897945 := bstep (se 2 (by rfl) ⟨1086729, by rfl⟩ : syracuseStep 2897945 = 2173459) B2173459
theorem B1931963 : Blo 1931435 1931963 := bstep (se 1 (by rfl) ⟨1448972, by rfl⟩ : syracuseStep 1931963 = 2897945) B2897945
theorem B2091241 : Blo 1931435 2091241 := bbase (se 2 (by rfl) ⟨784215, by rfl⟩ : syracuseStep 2091241 = 1568431) (by norm_num)
theorem B11153285 : Blo 1931435 11153285 := bstep (se 4 (by rfl) ⟨1045620, by rfl⟩ : syracuseStep 11153285 = 2091241) B2091241
theorem B7435523 : Blo 1931435 7435523 := bstep (se 1 (by rfl) ⟨5576642, by rfl⟩ : syracuseStep 7435523 = 11153285) B11153285
theorem B19828061 : Blo 1931435 19828061 := bstep (se 3 (by rfl) ⟨3717761, by rfl⟩ : syracuseStep 19828061 = 7435523) B7435523
theorem B13218707 : Blo 1931435 13218707 := bstep (se 1 (by rfl) ⟨9914030, by rfl⟩ : syracuseStep 13218707 = 19828061) B19828061
theorem B8812471 : Blo 1931435 8812471 := bstep (se 1 (by rfl) ⟨6609353, by rfl⟩ : syracuseStep 8812471 = 13218707) B13218707
theorem B11749961 : Blo 1931435 11749961 := bstep (se 2 (by rfl) ⟨4406235, by rfl⟩ : syracuseStep 11749961 = 8812471) B8812471
theorem B7833307 : Blo 1931435 7833307 := bstep (se 1 (by rfl) ⟨5874980, by rfl⟩ : syracuseStep 7833307 = 11749961) B11749961
theorem B10444409 : Blo 1931435 10444409 := bstep (se 2 (by rfl) ⟨3916653, by rfl⟩ : syracuseStep 10444409 = 7833307) B7833307
theorem B6962939 : Blo 1931435 6962939 := bstep (se 1 (by rfl) ⟨5222204, by rfl⟩ : syracuseStep 6962939 = 10444409) B10444409
theorem B4641959 : Blo 1931435 4641959 := bstep (se 1 (by rfl) ⟨3481469, by rfl⟩ : syracuseStep 4641959 = 6962939) B6962939
theorem B12378557 : Blo 1931435 12378557 := bstep (se 3 (by rfl) ⟨2320979, by rfl⟩ : syracuseStep 12378557 = 4641959) B4641959
theorem B8252371 : Blo 1931435 8252371 := bstep (se 1 (by rfl) ⟨6189278, by rfl⟩ : syracuseStep 8252371 = 12378557) B12378557
theorem B11003161 : Blo 1931435 11003161 := bstep (se 2 (by rfl) ⟨4126185, by rfl⟩ : syracuseStep 11003161 = 8252371) B8252371
theorem B14670881 : Blo 1931435 14670881 := bstep (se 2 (by rfl) ⟨5501580, by rfl⟩ : syracuseStep 14670881 = 11003161) B11003161
theorem B9780587 : Blo 1931435 9780587 := bstep (se 1 (by rfl) ⟨7335440, by rfl⟩ : syracuseStep 9780587 = 14670881) B14670881
theorem B6520391 : Blo 1931435 6520391 := bstep (se 1 (by rfl) ⟨4890293, by rfl⟩ : syracuseStep 6520391 = 9780587) B9780587
theorem B4346927 : Blo 1931435 4346927 := bstep (se 1 (by rfl) ⟨3260195, by rfl⟩ : syracuseStep 4346927 = 6520391) B6520391
theorem B2897951 : Blo 1931435 2897951 := bstep (se 1 (by rfl) ⟨2173463, by rfl⟩ : syracuseStep 2897951 = 4346927) B4346927
theorem B1931967 : Blo 1931435 1931967 := bstep (se 1 (by rfl) ⟨1448975, by rfl⟩ : syracuseStep 1931967 = 2897951) B2897951
theorem B2897957 : Blo 1931435 2897957 := bbase (se 4 (by rfl) ⟨271683, by rfl⟩ : syracuseStep 2897957 = 543367) (by norm_num)
theorem B1931971 : Blo 1931435 1931971 := bstep (se 1 (by rfl) ⟨1448978, by rfl⟩ : syracuseStep 1931971 = 2897957) B2897957
theorem B2445157 : Blo 1931435 2445157 := bbase (se 4 (by rfl) ⟨229233, by rfl⟩ : syracuseStep 2445157 = 458467) (by norm_num)
theorem B3260209 : Blo 1931435 3260209 := bstep (se 2 (by rfl) ⟨1222578, by rfl⟩ : syracuseStep 3260209 = 2445157) B2445157
theorem B4346945 : Blo 1931435 4346945 := bstep (se 2 (by rfl) ⟨1630104, by rfl⟩ : syracuseStep 4346945 = 3260209) B3260209
theorem B2897963 : Blo 1931435 2897963 := bstep (se 1 (by rfl) ⟨2173472, by rfl⟩ : syracuseStep 2897963 = 4346945) B4346945
theorem B1931975 : Blo 1931435 1931975 := bstep (se 1 (by rfl) ⟨1448981, by rfl⟩ : syracuseStep 1931975 = 2897963) B2897963
theorem B2173477 : Blo 1931435 2173477 := bbase (se 4 (by rfl) ⟨203763, by rfl⟩ : syracuseStep 2173477 = 407527) (by norm_num)
theorem B2897969 : Blo 1931435 2897969 := bstep (se 2 (by rfl) ⟨1086738, by rfl⟩ : syracuseStep 2897969 = 2173477) B2173477
theorem B1931979 : Blo 1931435 1931979 := bstep (se 1 (by rfl) ⟨1448984, by rfl⟩ : syracuseStep 1931979 = 2897969) B2897969
theorem B2478529 : Blo 1931435 2478529 := bbase (se 2 (by rfl) ⟨929448, by rfl⟩ : syracuseStep 2478529 = 1858897) (by norm_num)
theorem B13218821 : Blo 1931435 13218821 := bstep (se 4 (by rfl) ⟨1239264, by rfl⟩ : syracuseStep 13218821 = 2478529) B2478529
theorem B8812547 : Blo 1931435 8812547 := bstep (se 1 (by rfl) ⟨6609410, by rfl⟩ : syracuseStep 8812547 = 13218821) B13218821
theorem B5875031 : Blo 1931435 5875031 := bstep (se 1 (by rfl) ⟨4406273, by rfl⟩ : syracuseStep 5875031 = 8812547) B8812547
theorem B3916687 : Blo 1931435 3916687 := bstep (se 1 (by rfl) ⟨2937515, by rfl⟩ : syracuseStep 3916687 = 5875031) B5875031
theorem B5222249 : Blo 1931435 5222249 := bstep (se 2 (by rfl) ⟨1958343, by rfl⟩ : syracuseStep 5222249 = 3916687) B3916687
theorem B3481499 : Blo 1931435 3481499 := bstep (se 1 (by rfl) ⟨2611124, by rfl⟩ : syracuseStep 3481499 = 5222249) B5222249
theorem B9283997 : Blo 1931435 9283997 := bstep (se 3 (by rfl) ⟨1740749, by rfl⟩ : syracuseStep 9283997 = 3481499) B3481499
theorem B6189331 : Blo 1931435 6189331 := bstep (se 1 (by rfl) ⟨4641998, by rfl⟩ : syracuseStep 6189331 = 9283997) B9283997
theorem B8252441 : Blo 1931435 8252441 := bstep (se 2 (by rfl) ⟨3094665, by rfl⟩ : syracuseStep 8252441 = 6189331) B6189331
theorem B5501627 : Blo 1931435 5501627 := bstep (se 1 (by rfl) ⟨4126220, by rfl⟩ : syracuseStep 5501627 = 8252441) B8252441
theorem B3667751 : Blo 1931435 3667751 := bstep (se 1 (by rfl) ⟨2750813, by rfl⟩ : syracuseStep 3667751 = 5501627) B5501627
theorem B2445167 : Blo 1931435 2445167 := bstep (se 1 (by rfl) ⟨1833875, by rfl⟩ : syracuseStep 2445167 = 3667751) B3667751
theorem B6520445 : Blo 1931435 6520445 := bstep (se 3 (by rfl) ⟨1222583, by rfl⟩ : syracuseStep 6520445 = 2445167) B2445167
theorem B4346963 : Blo 1931435 4346963 := bstep (se 1 (by rfl) ⟨3260222, by rfl⟩ : syracuseStep 4346963 = 6520445) B6520445
theorem B2897975 : Blo 1931435 2897975 := bstep (se 1 (by rfl) ⟨2173481, by rfl⟩ : syracuseStep 2897975 = 4346963) B4346963
theorem B1931983 : Blo 1931435 1931983 := bstep (se 1 (by rfl) ⟨1448987, by rfl⟩ : syracuseStep 1931983 = 2897975) B2897975
theorem B2897981 : Blo 1931435 2897981 := bbase (se 3 (by rfl) ⟨543371, by rfl⟩ : syracuseStep 2897981 = 1086743) (by norm_num)
theorem B1931987 : Blo 1931435 1931987 := bstep (se 1 (by rfl) ⟨1448990, by rfl⟩ : syracuseStep 1931987 = 2897981) B2897981
theorem B4346981 : Blo 1931435 4346981 := bbase (se 4 (by rfl) ⟨407529, by rfl⟩ : syracuseStep 4346981 = 815059) (by norm_num)
theorem B2897987 : Blo 1931435 2897987 := bstep (se 1 (by rfl) ⟨2173490, by rfl⟩ : syracuseStep 2897987 = 4346981) B4346981
theorem B1931991 : Blo 1931435 1931991 := bstep (se 1 (by rfl) ⟨1448993, by rfl⟩ : syracuseStep 1931991 = 2897987) B2897987
theorem B4890365 : Blo 1931435 4890365 := bbase (se 3 (by rfl) ⟨916943, by rfl⟩ : syracuseStep 4890365 = 1833887) (by norm_num)
theorem B3260243 : Blo 1931435 3260243 := bstep (se 1 (by rfl) ⟨2445182, by rfl⟩ : syracuseStep 3260243 = 4890365) B4890365
theorem B2173495 : Blo 1931435 2173495 := bstep (se 1 (by rfl) ⟨1630121, by rfl⟩ : syracuseStep 2173495 = 3260243) B3260243
theorem B2897993 : Blo 1931435 2897993 := bstep (se 2 (by rfl) ⟨1086747, by rfl⟩ : syracuseStep 2897993 = 2173495) B2173495
theorem B1931995 : Blo 1931435 1931995 := bstep (se 1 (by rfl) ⟨1448996, by rfl⟩ : syracuseStep 1931995 = 2897993) B2897993
theorem B3667781 : Blo 1931435 3667781 := bbase (se 4 (by rfl) ⟨343854, by rfl⟩ : syracuseStep 3667781 = 687709) (by norm_num)
theorem B9780749 : Blo 1931435 9780749 := bstep (se 3 (by rfl) ⟨1833890, by rfl⟩ : syracuseStep 9780749 = 3667781) B3667781
theorem B6520499 : Blo 1931435 6520499 := bstep (se 1 (by rfl) ⟨4890374, by rfl⟩ : syracuseStep 6520499 = 9780749) B9780749
theorem B4346999 : Blo 1931435 4346999 := bstep (se 1 (by rfl) ⟨3260249, by rfl⟩ : syracuseStep 4346999 = 6520499) B6520499
theorem B2897999 : Blo 1931435 2897999 := bstep (se 1 (by rfl) ⟨2173499, by rfl⟩ : syracuseStep 2897999 = 4346999) B4346999
theorem B1931999 : Blo 1931435 1931999 := bstep (se 1 (by rfl) ⟨1448999, by rfl⟩ : syracuseStep 1931999 = 2897999) B2897999
theorem B2898005 : Blo 1931435 2898005 := bbase (se 8 (by rfl) ⟨16980, by rfl⟩ : syracuseStep 2898005 = 33961) (by norm_num)
theorem B1932003 : Blo 1931435 1932003 := bstep (se 1 (by rfl) ⟨1449002, by rfl⟩ : syracuseStep 1932003 = 2898005) B2898005
theorem B29804885 : Blo 1931435 29804885 := bbase (se 10 (by rfl) ⟨43659, by rfl⟩ : syracuseStep 29804885 = 87319) (by norm_num)
theorem B19869923 : Blo 1931435 19869923 := bstep (se 1 (by rfl) ⟨14902442, by rfl⟩ : syracuseStep 19869923 = 29804885) B29804885
theorem B13246615 : Blo 1931435 13246615 := bstep (se 1 (by rfl) ⟨9934961, by rfl⟩ : syracuseStep 13246615 = 19869923) B19869923
theorem B17662153 : Blo 1931435 17662153 := bstep (se 2 (by rfl) ⟨6623307, by rfl⟩ : syracuseStep 17662153 = 13246615) B13246615
theorem B23549537 : Blo 1931435 23549537 := bstep (se 2 (by rfl) ⟨8831076, by rfl⟩ : syracuseStep 23549537 = 17662153) B17662153
theorem B15699691 : Blo 1931435 15699691 := bstep (se 1 (by rfl) ⟨11774768, by rfl⟩ : syracuseStep 15699691 = 23549537) B23549537
theorem B20932921 : Blo 1931435 20932921 := bstep (se 2 (by rfl) ⟨7849845, by rfl⟩ : syracuseStep 20932921 = 15699691) B15699691
theorem B27910561 : Blo 1931435 27910561 := bstep (se 2 (by rfl) ⟨10466460, by rfl⟩ : syracuseStep 27910561 = 20932921) B20932921
theorem B37214081 : Blo 1931435 37214081 := bstep (se 2 (by rfl) ⟨13955280, by rfl⟩ : syracuseStep 37214081 = 27910561) B27910561
theorem B24809387 : Blo 1931435 24809387 := bstep (se 1 (by rfl) ⟨18607040, by rfl⟩ : syracuseStep 24809387 = 37214081) B37214081
theorem B66158365 : Blo 1931435 66158365 := bstep (se 3 (by rfl) ⟨12404693, by rfl⟩ : syracuseStep 66158365 = 24809387) B24809387
theorem B88211153 : Blo 1931435 88211153 := bstep (se 2 (by rfl) ⟨33079182, by rfl⟩ : syracuseStep 88211153 = 66158365) B66158365
theorem B235229741 : Blo 1931435 235229741 := bstep (se 3 (by rfl) ⟨44105576, by rfl⟩ : syracuseStep 235229741 = 88211153) B88211153
theorem B156819827 : Blo 1931435 156819827 := bstep (se 1 (by rfl) ⟨117614870, by rfl⟩ : syracuseStep 156819827 = 235229741) B235229741
theorem B104546551 : Blo 1931435 104546551 := bstep (se 1 (by rfl) ⟨78409913, by rfl⟩ : syracuseStep 104546551 = 156819827) B156819827
theorem B139395401 : Blo 1931435 139395401 := bstep (se 2 (by rfl) ⟨52273275, by rfl⟩ : syracuseStep 139395401 = 104546551) B104546551
theorem B92930267 : Blo 1931435 92930267 := bstep (se 1 (by rfl) ⟨69697700, by rfl⟩ : syracuseStep 92930267 = 139395401) B139395401
theorem B61953511 : Blo 1931435 61953511 := bstep (se 1 (by rfl) ⟨46465133, by rfl⟩ : syracuseStep 61953511 = 92930267) B92930267
theorem B82604681 : Blo 1931435 82604681 := bstep (se 2 (by rfl) ⟨30976755, by rfl⟩ : syracuseStep 82604681 = 61953511) B61953511
theorem B55069787 : Blo 1931435 55069787 := bstep (se 1 (by rfl) ⟨41302340, by rfl⟩ : syracuseStep 55069787 = 82604681) B82604681
theorem B36713191 : Blo 1931435 36713191 := bstep (se 1 (by rfl) ⟨27534893, by rfl⟩ : syracuseStep 36713191 = 55069787) B55069787
theorem B48950921 : Blo 1931435 48950921 := bstep (se 2 (by rfl) ⟨18356595, by rfl⟩ : syracuseStep 48950921 = 36713191) B36713191
theorem B32633947 : Blo 1931435 32633947 := bstep (se 1 (by rfl) ⟨24475460, by rfl⟩ : syracuseStep 32633947 = 48950921) B48950921
theorem B174047717 : Blo 1931435 174047717 := bstep (se 4 (by rfl) ⟨16316973, by rfl⟩ : syracuseStep 174047717 = 32633947) B32633947
theorem B464127245 : Blo 1931435 464127245 := bstep (se 3 (by rfl) ⟨87023858, by rfl⟩ : syracuseStep 464127245 = 174047717) B174047717
theorem B309418163 : Blo 1931435 309418163 := bstep (se 1 (by rfl) ⟨232063622, by rfl⟩ : syracuseStep 309418163 = 464127245) B464127245
theorem B206278775 : Blo 1931435 206278775 := bstep (se 1 (by rfl) ⟨154709081, by rfl⟩ : syracuseStep 206278775 = 309418163) B309418163
theorem B137519183 : Blo 1931435 137519183 := bstep (se 1 (by rfl) ⟨103139387, by rfl⟩ : syracuseStep 137519183 = 206278775) B206278775
theorem B91679455 : Blo 1931435 91679455 := bstep (se 1 (by rfl) ⟨68759591, by rfl⟩ : syracuseStep 91679455 = 137519183) B137519183
theorem B122239273 : Blo 1931435 122239273 := bstep (se 2 (by rfl) ⟨45839727, by rfl⟩ : syracuseStep 122239273 = 91679455) B91679455
theorem B162985697 : Blo 1931435 162985697 := bstep (se 2 (by rfl) ⟨61119636, by rfl⟩ : syracuseStep 162985697 = 122239273) B122239273
theorem B108657131 : Blo 1931435 108657131 := bstep (se 1 (by rfl) ⟨81492848, by rfl⟩ : syracuseStep 108657131 = 162985697) B162985697
theorem B289752349 : Blo 1931435 289752349 := bstep (se 3 (by rfl) ⟨54328565, by rfl⟩ : syracuseStep 289752349 = 108657131) B108657131
theorem B386336465 : Blo 1931435 386336465 := bstep (se 2 (by rfl) ⟨144876174, by rfl⟩ : syracuseStep 386336465 = 289752349) B289752349
theorem B257557643 : Blo 1931435 257557643 := bstep (se 1 (by rfl) ⟨193168232, by rfl⟩ : syracuseStep 257557643 = 386336465) B386336465
theorem B171705095 : Blo 1931435 171705095 := bstep (se 1 (by rfl) ⟨128778821, by rfl⟩ : syracuseStep 171705095 = 257557643) B257557643
theorem B114470063 : Blo 1931435 114470063 := bstep (se 1 (by rfl) ⟨85852547, by rfl⟩ : syracuseStep 114470063 = 171705095) B171705095
theorem B76313375 : Blo 1931435 76313375 := bstep (se 1 (by rfl) ⟨57235031, by rfl⟩ : syracuseStep 76313375 = 114470063) B114470063
theorem B50875583 : Blo 1931435 50875583 := bstep (se 1 (by rfl) ⟨38156687, by rfl⟩ : syracuseStep 50875583 = 76313375) B76313375
theorem B542672885 : Blo 1931435 542672885 := bstep (se 5 (by rfl) ⟨25437791, by rfl⟩ : syracuseStep 542672885 = 50875583) B50875583
theorem B361781923 : Blo 1931435 361781923 := bstep (se 1 (by rfl) ⟨271336442, by rfl⟩ : syracuseStep 361781923 = 542672885) B542672885
theorem B482375897 : Blo 1931435 482375897 := bstep (se 2 (by rfl) ⟨180890961, by rfl⟩ : syracuseStep 482375897 = 361781923) B361781923
theorem B321583931 : Blo 1931435 321583931 := bstep (se 1 (by rfl) ⟨241187948, by rfl⟩ : syracuseStep 321583931 = 482375897) B482375897
theorem B214389287 : Blo 1931435 214389287 := bstep (se 1 (by rfl) ⟨160791965, by rfl⟩ : syracuseStep 214389287 = 321583931) B321583931
theorem B142926191 : Blo 1931435 142926191 := bstep (se 1 (by rfl) ⟨107194643, by rfl⟩ : syracuseStep 142926191 = 214389287) B214389287
theorem B95284127 : Blo 1931435 95284127 := bstep (se 1 (by rfl) ⟨71463095, by rfl⟩ : syracuseStep 95284127 = 142926191) B142926191
theorem B254091005 : Blo 1931435 254091005 := bstep (se 3 (by rfl) ⟨47642063, by rfl⟩ : syracuseStep 254091005 = 95284127) B95284127
theorem B169394003 : Blo 1931435 169394003 := bstep (se 1 (by rfl) ⟨127045502, by rfl⟩ : syracuseStep 169394003 = 254091005) B254091005
theorem B112929335 : Blo 1931435 112929335 := bstep (se 1 (by rfl) ⟨84697001, by rfl⟩ : syracuseStep 112929335 = 169394003) B169394003
theorem B75286223 : Blo 1931435 75286223 := bstep (se 1 (by rfl) ⟨56464667, by rfl⟩ : syracuseStep 75286223 = 112929335) B112929335
theorem B50190815 : Blo 1931435 50190815 := bstep (se 1 (by rfl) ⟨37643111, by rfl⟩ : syracuseStep 50190815 = 75286223) B75286223
theorem B33460543 : Blo 1931435 33460543 := bstep (se 1 (by rfl) ⟨25095407, by rfl⟩ : syracuseStep 33460543 = 50190815) B50190815
theorem B178456229 : Blo 1931435 178456229 := bstep (se 4 (by rfl) ⟨16730271, by rfl⟩ : syracuseStep 178456229 = 33460543) B33460543
theorem B118970819 : Blo 1931435 118970819 := bstep (se 1 (by rfl) ⟨89228114, by rfl⟩ : syracuseStep 118970819 = 178456229) B178456229
theorem B79313879 : Blo 1931435 79313879 := bstep (se 1 (by rfl) ⟨59485409, by rfl⟩ : syracuseStep 79313879 = 118970819) B118970819
theorem B52875919 : Blo 1931435 52875919 := bstep (se 1 (by rfl) ⟨39656939, by rfl⟩ : syracuseStep 52875919 = 79313879) B79313879
theorem B70501225 : Blo 1931435 70501225 := bstep (se 2 (by rfl) ⟨26437959, by rfl⟩ : syracuseStep 70501225 = 52875919) B52875919
theorem B94001633 : Blo 1931435 94001633 := bstep (se 2 (by rfl) ⟨35250612, by rfl⟩ : syracuseStep 94001633 = 70501225) B70501225
theorem B62667755 : Blo 1931435 62667755 := bstep (se 1 (by rfl) ⟨47000816, by rfl⟩ : syracuseStep 62667755 = 94001633) B94001633
theorem B41778503 : Blo 1931435 41778503 := bstep (se 1 (by rfl) ⟨31333877, by rfl⟩ : syracuseStep 41778503 = 62667755) B62667755
theorem B27852335 : Blo 1931435 27852335 := bstep (se 1 (by rfl) ⟨20889251, by rfl⟩ : syracuseStep 27852335 = 41778503) B41778503
theorem B18568223 : Blo 1931435 18568223 := bstep (se 1 (by rfl) ⟨13926167, by rfl⟩ : syracuseStep 18568223 = 27852335) B27852335
theorem B12378815 : Blo 1931435 12378815 := bstep (se 1 (by rfl) ⟨9284111, by rfl⟩ : syracuseStep 12378815 = 18568223) B18568223
theorem B8252543 : Blo 1931435 8252543 := bstep (se 1 (by rfl) ⟨6189407, by rfl⟩ : syracuseStep 8252543 = 12378815) B12378815
theorem B5501695 : Blo 1931435 5501695 := bstep (se 1 (by rfl) ⟨4126271, by rfl⟩ : syracuseStep 5501695 = 8252543) B8252543
theorem B7335593 : Blo 1931435 7335593 := bstep (se 2 (by rfl) ⟨2750847, by rfl⟩ : syracuseStep 7335593 = 5501695) B5501695
theorem B4890395 : Blo 1931435 4890395 := bstep (se 1 (by rfl) ⟨3667796, by rfl⟩ : syracuseStep 4890395 = 7335593) B7335593
theorem B3260263 : Blo 1931435 3260263 := bstep (se 1 (by rfl) ⟨2445197, by rfl⟩ : syracuseStep 3260263 = 4890395) B4890395
theorem B4347017 : Blo 1931435 4347017 := bstep (se 2 (by rfl) ⟨1630131, by rfl⟩ : syracuseStep 4347017 = 3260263) B3260263
theorem B2898011 : Blo 1931435 2898011 := bstep (se 1 (by rfl) ⟨2173508, by rfl⟩ : syracuseStep 2898011 = 4347017) B4347017
theorem B1932007 : Blo 1931435 1932007 := bstep (se 1 (by rfl) ⟨1449005, by rfl⟩ : syracuseStep 1932007 = 2898011) B2898011
theorem B2173513 : Blo 1931435 2173513 := bbase (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) (by norm_num)
theorem B2898017 : Blo 1931435 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B1932011 : Blo 1931435 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B9284149 : Blo 1931435 9284149 := bbase (se 5 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 9284149 = 870389) (by norm_num)
theorem B12378865 : Blo 1931435 12378865 := bstep (se 2 (by rfl) ⟨4642074, by rfl⟩ : syracuseStep 12378865 = 9284149) B9284149
theorem B16505153 : Blo 1931435 16505153 := bstep (se 2 (by rfl) ⟨6189432, by rfl⟩ : syracuseStep 16505153 = 12378865) B12378865
theorem B11003435 : Blo 1931435 11003435 := bstep (se 1 (by rfl) ⟨8252576, by rfl⟩ : syracuseStep 11003435 = 16505153) B16505153
theorem B7335623 : Blo 1931435 7335623 := bstep (se 1 (by rfl) ⟨5501717, by rfl⟩ : syracuseStep 7335623 = 11003435) B11003435
theorem B4890415 : Blo 1931435 4890415 := bstep (se 1 (by rfl) ⟨3667811, by rfl⟩ : syracuseStep 4890415 = 7335623) B7335623
theorem B6520553 : Blo 1931435 6520553 := bstep (se 2 (by rfl) ⟨2445207, by rfl⟩ : syracuseStep 6520553 = 4890415) B4890415
theorem B4347035 : Blo 1931435 4347035 := bstep (se 1 (by rfl) ⟨3260276, by rfl⟩ : syracuseStep 4347035 = 6520553) B6520553
theorem B2898023 : Blo 1931435 2898023 := bstep (se 1 (by rfl) ⟨2173517, by rfl⟩ : syracuseStep 2898023 = 4347035) B4347035
theorem B1932015 : Blo 1931435 1932015 := bstep (se 1 (by rfl) ⟨1449011, by rfl⟩ : syracuseStep 1932015 = 2898023) B2898023
theorem B2898029 : Blo 1931435 2898029 := bbase (se 3 (by rfl) ⟨543380, by rfl⟩ : syracuseStep 2898029 = 1086761) (by norm_num)
theorem B1932019 : Blo 1931435 1932019 := bstep (se 1 (by rfl) ⟨1449014, by rfl⟩ : syracuseStep 1932019 = 2898029) B2898029
theorem B4347053 : Blo 1931435 4347053 := bbase (se 3 (by rfl) ⟨815072, by rfl⟩ : syracuseStep 4347053 = 1630145) (by norm_num)
theorem B2898035 : Blo 1931435 2898035 := bstep (se 1 (by rfl) ⟨2173526, by rfl⟩ : syracuseStep 2898035 = 4347053) B4347053
theorem B1932023 : Blo 1931435 1932023 := bstep (se 1 (by rfl) ⟨1449017, by rfl⟩ : syracuseStep 1932023 = 2898035) B2898035
theorem B2384821 : Blo 1931435 2384821 := bbase (se 5 (by rfl) ⟨111788, by rfl⟩ : syracuseStep 2384821 = 223577) (by norm_num)
theorem B12719045 : Blo 1931435 12719045 := bstep (se 4 (by rfl) ⟨1192410, by rfl⟩ : syracuseStep 12719045 = 2384821) B2384821
theorem B8479363 : Blo 1931435 8479363 := bstep (se 1 (by rfl) ⟨6359522, by rfl⟩ : syracuseStep 8479363 = 12719045) B12719045
theorem B11305817 : Blo 1931435 11305817 := bstep (se 2 (by rfl) ⟨4239681, by rfl⟩ : syracuseStep 11305817 = 8479363) B8479363
theorem B7537211 : Blo 1931435 7537211 := bstep (se 1 (by rfl) ⟨5652908, by rfl⟩ : syracuseStep 7537211 = 11305817) B11305817
theorem B5024807 : Blo 1931435 5024807 := bstep (se 1 (by rfl) ⟨3768605, by rfl⟩ : syracuseStep 5024807 = 7537211) B7537211
theorem B3349871 : Blo 1931435 3349871 := bstep (se 1 (by rfl) ⟨2512403, by rfl⟩ : syracuseStep 3349871 = 5024807) B5024807
theorem B2233247 : Blo 1931435 2233247 := bstep (se 1 (by rfl) ⟨1674935, by rfl⟩ : syracuseStep 2233247 = 3349871) B3349871
theorem B5955325 : Blo 1931435 5955325 := bstep (se 3 (by rfl) ⟨1116623, by rfl⟩ : syracuseStep 5955325 = 2233247) B2233247
theorem B31761733 : Blo 1931435 31761733 := bstep (se 4 (by rfl) ⟨2977662, by rfl⟩ : syracuseStep 31761733 = 5955325) B5955325
theorem B42348977 : Blo 1931435 42348977 := bstep (se 2 (by rfl) ⟨15880866, by rfl⟩ : syracuseStep 42348977 = 31761733) B31761733
theorem B28232651 : Blo 1931435 28232651 := bstep (se 1 (by rfl) ⟨21174488, by rfl⟩ : syracuseStep 28232651 = 42348977) B42348977
theorem B18821767 : Blo 1931435 18821767 := bstep (se 1 (by rfl) ⟨14116325, by rfl⟩ : syracuseStep 18821767 = 28232651) B28232651
theorem B25095689 : Blo 1931435 25095689 := bstep (se 2 (by rfl) ⟨9410883, by rfl⟩ : syracuseStep 25095689 = 18821767) B18821767
theorem B16730459 : Blo 1931435 16730459 := bstep (se 1 (by rfl) ⟨12547844, by rfl⟩ : syracuseStep 16730459 = 25095689) B25095689
theorem B11153639 : Blo 1931435 11153639 := bstep (se 1 (by rfl) ⟨8365229, by rfl⟩ : syracuseStep 11153639 = 16730459) B16730459
theorem B7435759 : Blo 1931435 7435759 := bstep (se 1 (by rfl) ⟨5576819, by rfl⟩ : syracuseStep 7435759 = 11153639) B11153639
theorem B9914345 : Blo 1931435 9914345 := bstep (se 2 (by rfl) ⟨3717879, by rfl⟩ : syracuseStep 9914345 = 7435759) B7435759
theorem B6609563 : Blo 1931435 6609563 := bstep (se 1 (by rfl) ⟨4957172, by rfl⟩ : syracuseStep 6609563 = 9914345) B9914345
theorem B4406375 : Blo 1931435 4406375 := bstep (se 1 (by rfl) ⟨3304781, by rfl⟩ : syracuseStep 4406375 = 6609563) B6609563
theorem B2937583 : Blo 1931435 2937583 := bstep (se 1 (by rfl) ⟨2203187, by rfl⟩ : syracuseStep 2937583 = 4406375) B4406375
theorem B3916777 : Blo 1931435 3916777 := bstep (se 2 (by rfl) ⟨1468791, by rfl⟩ : syracuseStep 3916777 = 2937583) B2937583
theorem B5222369 : Blo 1931435 5222369 := bstep (se 2 (by rfl) ⟨1958388, by rfl⟩ : syracuseStep 5222369 = 3916777) B3916777
theorem B3481579 : Blo 1931435 3481579 := bstep (se 1 (by rfl) ⟨2611184, by rfl⟩ : syracuseStep 3481579 = 5222369) B5222369
theorem B4642105 : Blo 1931435 4642105 := bstep (se 2 (by rfl) ⟨1740789, by rfl⟩ : syracuseStep 4642105 = 3481579) B3481579
theorem B6189473 : Blo 1931435 6189473 := bstep (se 2 (by rfl) ⟨2321052, by rfl⟩ : syracuseStep 6189473 = 4642105) B4642105
theorem B4126315 : Blo 1931435 4126315 := bstep (se 1 (by rfl) ⟨3094736, by rfl⟩ : syracuseStep 4126315 = 6189473) B6189473
theorem B5501753 : Blo 1931435 5501753 := bstep (se 2 (by rfl) ⟨2063157, by rfl⟩ : syracuseStep 5501753 = 4126315) B4126315
theorem B3667835 : Blo 1931435 3667835 := bstep (se 1 (by rfl) ⟨2750876, by rfl⟩ : syracuseStep 3667835 = 5501753) B5501753
theorem B2445223 : Blo 1931435 2445223 := bstep (se 1 (by rfl) ⟨1833917, by rfl⟩ : syracuseStep 2445223 = 3667835) B3667835
theorem B3260297 : Blo 1931435 3260297 := bstep (se 2 (by rfl) ⟨1222611, by rfl⟩ : syracuseStep 3260297 = 2445223) B2445223
theorem B2173531 : Blo 1931435 2173531 := bstep (se 1 (by rfl) ⟨1630148, by rfl⟩ : syracuseStep 2173531 = 3260297) B3260297
theorem B2898041 : Blo 1931435 2898041 := bstep (se 2 (by rfl) ⟨1086765, by rfl⟩ : syracuseStep 2898041 = 2173531) B2173531
theorem B1932027 : Blo 1931435 1932027 := bstep (se 1 (by rfl) ⟨1449020, by rfl⟩ : syracuseStep 1932027 = 2898041) B2898041
theorem B5652917 : Blo 1931435 5652917 := bbase (se 5 (by rfl) ⟨264980, by rfl⟩ : syracuseStep 5652917 = 529961) (by norm_num)
theorem B3768611 : Blo 1931435 3768611 := bstep (se 1 (by rfl) ⟨2826458, by rfl⟩ : syracuseStep 3768611 = 5652917) B5652917
theorem B10049629 : Blo 1931435 10049629 := bstep (se 3 (by rfl) ⟨1884305, by rfl⟩ : syracuseStep 10049629 = 3768611) B3768611
theorem B13399505 : Blo 1931435 13399505 := bstep (se 2 (by rfl) ⟨5024814, by rfl⟩ : syracuseStep 13399505 = 10049629) B10049629
theorem B8933003 : Blo 1931435 8933003 := bstep (se 1 (by rfl) ⟨6699752, by rfl⟩ : syracuseStep 8933003 = 13399505) B13399505
theorem B5955335 : Blo 1931435 5955335 := bstep (se 1 (by rfl) ⟨4466501, by rfl⟩ : syracuseStep 5955335 = 8933003) B8933003
theorem B3970223 : Blo 1931435 3970223 := bstep (se 1 (by rfl) ⟨2977667, by rfl⟩ : syracuseStep 3970223 = 5955335) B5955335
theorem B2646815 : Blo 1931435 2646815 := bstep (se 1 (by rfl) ⟨1985111, by rfl⟩ : syracuseStep 2646815 = 3970223) B3970223
theorem B7058173 : Blo 1931435 7058173 := bstep (se 3 (by rfl) ⟨1323407, by rfl⟩ : syracuseStep 7058173 = 2646815) B2646815
theorem B9410897 : Blo 1931435 9410897 := bstep (se 2 (by rfl) ⟨3529086, by rfl⟩ : syracuseStep 9410897 = 7058173) B7058173
theorem B6273931 : Blo 1931435 6273931 := bstep (se 1 (by rfl) ⟨4705448, by rfl⟩ : syracuseStep 6273931 = 9410897) B9410897
theorem B8365241 : Blo 1931435 8365241 := bstep (se 2 (by rfl) ⟨3136965, by rfl⟩ : syracuseStep 8365241 = 6273931) B6273931
theorem B22307309 : Blo 1931435 22307309 := bstep (se 3 (by rfl) ⟨4182620, by rfl⟩ : syracuseStep 22307309 = 8365241) B8365241
theorem B14871539 : Blo 1931435 14871539 := bstep (se 1 (by rfl) ⟨11153654, by rfl⟩ : syracuseStep 14871539 = 22307309) B22307309
theorem B9914359 : Blo 1931435 9914359 := bstep (se 1 (by rfl) ⟨7435769, by rfl⟩ : syracuseStep 9914359 = 14871539) B14871539
theorem B13219145 : Blo 1931435 13219145 := bstep (se 2 (by rfl) ⟨4957179, by rfl⟩ : syracuseStep 13219145 = 9914359) B9914359
theorem B8812763 : Blo 1931435 8812763 := bstep (se 1 (by rfl) ⟨6609572, by rfl⟩ : syracuseStep 8812763 = 13219145) B13219145
theorem B5875175 : Blo 1931435 5875175 := bstep (se 1 (by rfl) ⟨4406381, by rfl⟩ : syracuseStep 5875175 = 8812763) B8812763
theorem B3916783 : Blo 1931435 3916783 := bstep (se 1 (by rfl) ⟨2937587, by rfl⟩ : syracuseStep 3916783 = 5875175) B5875175
theorem B5222377 : Blo 1931435 5222377 := bstep (se 2 (by rfl) ⟨1958391, by rfl⟩ : syracuseStep 5222377 = 3916783) B3916783
theorem B6963169 : Blo 1931435 6963169 := bstep (se 2 (by rfl) ⟨2611188, by rfl⟩ : syracuseStep 6963169 = 5222377) B5222377
theorem B9284225 : Blo 1931435 9284225 := bstep (se 2 (by rfl) ⟨3481584, by rfl⟩ : syracuseStep 9284225 = 6963169) B6963169
theorem B24757933 : Blo 1931435 24757933 := bstep (se 3 (by rfl) ⟨4642112, by rfl⟩ : syracuseStep 24757933 = 9284225) B9284225
theorem B33010577 : Blo 1931435 33010577 := bstep (se 2 (by rfl) ⟨12378966, by rfl⟩ : syracuseStep 33010577 = 24757933) B24757933
theorem B22007051 : Blo 1931435 22007051 := bstep (se 1 (by rfl) ⟨16505288, by rfl⟩ : syracuseStep 22007051 = 33010577) B33010577
theorem B14671367 : Blo 1931435 14671367 := bstep (se 1 (by rfl) ⟨11003525, by rfl⟩ : syracuseStep 14671367 = 22007051) B22007051
theorem B9780911 : Blo 1931435 9780911 := bstep (se 1 (by rfl) ⟨7335683, by rfl⟩ : syracuseStep 9780911 = 14671367) B14671367
theorem B6520607 : Blo 1931435 6520607 := bstep (se 1 (by rfl) ⟨4890455, by rfl⟩ : syracuseStep 6520607 = 9780911) B9780911
theorem B4347071 : Blo 1931435 4347071 := bstep (se 1 (by rfl) ⟨3260303, by rfl⟩ : syracuseStep 4347071 = 6520607) B6520607
theorem B2898047 : Blo 1931435 2898047 := bstep (se 1 (by rfl) ⟨2173535, by rfl⟩ : syracuseStep 2898047 = 4347071) B4347071
theorem B1932031 : Blo 1931435 1932031 := bstep (se 1 (by rfl) ⟨1449023, by rfl⟩ : syracuseStep 1932031 = 2898047) B2898047
theorem B2898053 : Blo 1931435 2898053 := bbase (se 4 (by rfl) ⟨271692, by rfl⟩ : syracuseStep 2898053 = 543385) (by norm_num)
theorem B1932035 : Blo 1931435 1932035 := bstep (se 1 (by rfl) ⟨1449026, by rfl⟩ : syracuseStep 1932035 = 2898053) B2898053
theorem B3260317 : Blo 1931435 3260317 := bbase (se 3 (by rfl) ⟨611309, by rfl⟩ : syracuseStep 3260317 = 1222619) (by norm_num)
theorem B4347089 : Blo 1931435 4347089 := bstep (se 2 (by rfl) ⟨1630158, by rfl⟩ : syracuseStep 4347089 = 3260317) B3260317
theorem B2898059 : Blo 1931435 2898059 := bstep (se 1 (by rfl) ⟨2173544, by rfl⟩ : syracuseStep 2898059 = 4347089) B4347089
theorem B1932039 : Blo 1931435 1932039 := bstep (se 1 (by rfl) ⟨1449029, by rfl⟩ : syracuseStep 1932039 = 2898059) B2898059
theorem B2173549 : Blo 1931435 2173549 := bbase (se 3 (by rfl) ⟨407540, by rfl⟩ : syracuseStep 2173549 = 815081) (by norm_num)
theorem B2898065 : Blo 1931435 2898065 := bstep (se 2 (by rfl) ⟨1086774, by rfl⟩ : syracuseStep 2898065 = 2173549) B2173549
theorem B1932043 : Blo 1931435 1932043 := bstep (se 1 (by rfl) ⟨1449032, by rfl⟩ : syracuseStep 1932043 = 2898065) B2898065
theorem B6520661 : Blo 1931435 6520661 := bbase (se 9 (by rfl) ⟨19103, by rfl⟩ : syracuseStep 6520661 = 38207) (by norm_num)
theorem B4347107 : Blo 1931435 4347107 := bstep (se 1 (by rfl) ⟨3260330, by rfl⟩ : syracuseStep 4347107 = 6520661) B6520661
theorem B2898071 : Blo 1931435 2898071 := bstep (se 1 (by rfl) ⟨2173553, by rfl⟩ : syracuseStep 2898071 = 4347107) B4347107
theorem B1932047 : Blo 1931435 1932047 := bstep (se 1 (by rfl) ⟨1449035, by rfl⟩ : syracuseStep 1932047 = 2898071) B2898071
theorem B2898077 : Blo 1931435 2898077 := bbase (se 3 (by rfl) ⟨543389, by rfl⟩ : syracuseStep 2898077 = 1086779) (by norm_num)
theorem B1932051 : Blo 1931435 1932051 := bstep (se 1 (by rfl) ⟨1449038, by rfl⟩ : syracuseStep 1932051 = 2898077) B2898077
theorem B4347125 : Blo 1931435 4347125 := bbase (se 5 (by rfl) ⟨203771, by rfl⟩ : syracuseStep 4347125 = 407543) (by norm_num)
theorem B2898083 : Blo 1931435 2898083 := bstep (se 1 (by rfl) ⟨2173562, by rfl⟩ : syracuseStep 2898083 = 4347125) B4347125
theorem B1932055 : Blo 1931435 1932055 := bstep (se 1 (by rfl) ⟨1449041, by rfl⟩ : syracuseStep 1932055 = 2898083) B2898083
theorem B4705517 : Blo 1931435 4705517 := bbase (se 3 (by rfl) ⟨882284, by rfl⟩ : syracuseStep 4705517 = 1764569) (by norm_num)
theorem B3137011 : Blo 1931435 3137011 := bstep (se 1 (by rfl) ⟨2352758, by rfl⟩ : syracuseStep 3137011 = 4705517) B4705517
theorem B16730725 : Blo 1931435 16730725 := bstep (se 4 (by rfl) ⟨1568505, by rfl⟩ : syracuseStep 16730725 = 3137011) B3137011
theorem B22307633 : Blo 1931435 22307633 := bstep (se 2 (by rfl) ⟨8365362, by rfl⟩ : syracuseStep 22307633 = 16730725) B16730725
theorem B14871755 : Blo 1931435 14871755 := bstep (se 1 (by rfl) ⟨11153816, by rfl⟩ : syracuseStep 14871755 = 22307633) B22307633
theorem B9914503 : Blo 1931435 9914503 := bstep (se 1 (by rfl) ⟨7435877, by rfl⟩ : syracuseStep 9914503 = 14871755) B14871755
theorem B13219337 : Blo 1931435 13219337 := bstep (se 2 (by rfl) ⟨4957251, by rfl⟩ : syracuseStep 13219337 = 9914503) B9914503
theorem B8812891 : Blo 1931435 8812891 := bstep (se 1 (by rfl) ⟨6609668, by rfl⟩ : syracuseStep 8812891 = 13219337) B13219337
theorem B11750521 : Blo 1931435 11750521 := bstep (se 2 (by rfl) ⟨4406445, by rfl⟩ : syracuseStep 11750521 = 8812891) B8812891
theorem B15667361 : Blo 1931435 15667361 := bstep (se 2 (by rfl) ⟨5875260, by rfl⟩ : syracuseStep 15667361 = 11750521) B11750521
theorem B10444907 : Blo 1931435 10444907 := bstep (se 1 (by rfl) ⟨7833680, by rfl⟩ : syracuseStep 10444907 = 15667361) B15667361
theorem B27853085 : Blo 1931435 27853085 := bstep (se 3 (by rfl) ⟨5222453, by rfl⟩ : syracuseStep 27853085 = 10444907) B10444907
theorem B18568723 : Blo 1931435 18568723 := bstep (se 1 (by rfl) ⟨13926542, by rfl⟩ : syracuseStep 18568723 = 27853085) B27853085
theorem B24758297 : Blo 1931435 24758297 := bstep (se 2 (by rfl) ⟨9284361, by rfl⟩ : syracuseStep 24758297 = 18568723) B18568723
theorem B16505531 : Blo 1931435 16505531 := bstep (se 1 (by rfl) ⟨12379148, by rfl⟩ : syracuseStep 16505531 = 24758297) B24758297
theorem B11003687 : Blo 1931435 11003687 := bstep (se 1 (by rfl) ⟨8252765, by rfl⟩ : syracuseStep 11003687 = 16505531) B16505531
theorem B7335791 : Blo 1931435 7335791 := bstep (se 1 (by rfl) ⟨5501843, by rfl⟩ : syracuseStep 7335791 = 11003687) B11003687
theorem B4890527 : Blo 1931435 4890527 := bstep (se 1 (by rfl) ⟨3667895, by rfl⟩ : syracuseStep 4890527 = 7335791) B7335791
theorem B3260351 : Blo 1931435 3260351 := bstep (se 1 (by rfl) ⟨2445263, by rfl⟩ : syracuseStep 3260351 = 4890527) B4890527
theorem B2173567 : Blo 1931435 2173567 := bstep (se 1 (by rfl) ⟨1630175, by rfl⟩ : syracuseStep 2173567 = 3260351) B3260351
theorem B2898089 : Blo 1931435 2898089 := bstep (se 2 (by rfl) ⟨1086783, by rfl⟩ : syracuseStep 2898089 = 2173567) B2173567
theorem B1932059 : Blo 1931435 1932059 := bstep (se 1 (by rfl) ⟨1449044, by rfl⟩ : syracuseStep 1932059 = 2898089) B2898089
theorem B2937637 : Blo 1931435 2937637 := bbase (se 4 (by rfl) ⟨275403, by rfl⟩ : syracuseStep 2937637 = 550807) (by norm_num)
theorem B3916849 : Blo 1931435 3916849 := bstep (se 2 (by rfl) ⟨1468818, by rfl⟩ : syracuseStep 3916849 = 2937637) B2937637
theorem B5222465 : Blo 1931435 5222465 := bstep (se 2 (by rfl) ⟨1958424, by rfl⟩ : syracuseStep 5222465 = 3916849) B3916849
theorem B3481643 : Blo 1931435 3481643 := bstep (se 1 (by rfl) ⟨2611232, by rfl⟩ : syracuseStep 3481643 = 5222465) B5222465
theorem B9284381 : Blo 1931435 9284381 := bstep (se 3 (by rfl) ⟨1740821, by rfl⟩ : syracuseStep 9284381 = 3481643) B3481643
theorem B6189587 : Blo 1931435 6189587 := bstep (se 1 (by rfl) ⟨4642190, by rfl⟩ : syracuseStep 6189587 = 9284381) B9284381
theorem B4126391 : Blo 1931435 4126391 := bstep (se 1 (by rfl) ⟨3094793, by rfl⟩ : syracuseStep 4126391 = 6189587) B6189587
theorem B2750927 : Blo 1931435 2750927 := bstep (se 1 (by rfl) ⟨2063195, by rfl⟩ : syracuseStep 2750927 = 4126391) B4126391
theorem B7335805 : Blo 1931435 7335805 := bstep (se 3 (by rfl) ⟨1375463, by rfl⟩ : syracuseStep 7335805 = 2750927) B2750927
theorem B9781073 : Blo 1931435 9781073 := bstep (se 2 (by rfl) ⟨3667902, by rfl⟩ : syracuseStep 9781073 = 7335805) B7335805
theorem B6520715 : Blo 1931435 6520715 := bstep (se 1 (by rfl) ⟨4890536, by rfl⟩ : syracuseStep 6520715 = 9781073) B9781073
theorem B4347143 : Blo 1931435 4347143 := bstep (se 1 (by rfl) ⟨3260357, by rfl⟩ : syracuseStep 4347143 = 6520715) B6520715
theorem B2898095 : Blo 1931435 2898095 := bstep (se 1 (by rfl) ⟨2173571, by rfl⟩ : syracuseStep 2898095 = 4347143) B4347143
theorem B1932063 : Blo 1931435 1932063 := bstep (se 1 (by rfl) ⟨1449047, by rfl⟩ : syracuseStep 1932063 = 2898095) B2898095
theorem B2898101 : Blo 1931435 2898101 := bbase (se 5 (by rfl) ⟨135848, by rfl⟩ : syracuseStep 2898101 = 271697) (by norm_num)
theorem B1932067 : Blo 1931435 1932067 := bstep (se 1 (by rfl) ⟨1449050, by rfl⟩ : syracuseStep 1932067 = 2898101) B2898101
theorem B4890557 : Blo 1931435 4890557 := bbase (se 3 (by rfl) ⟨916979, by rfl⟩ : syracuseStep 4890557 = 1833959) (by norm_num)
theorem B3260371 : Blo 1931435 3260371 := bstep (se 1 (by rfl) ⟨2445278, by rfl⟩ : syracuseStep 3260371 = 4890557) B4890557
theorem B4347161 : Blo 1931435 4347161 := bstep (se 2 (by rfl) ⟨1630185, by rfl⟩ : syracuseStep 4347161 = 3260371) B3260371
theorem B2898107 : Blo 1931435 2898107 := bstep (se 1 (by rfl) ⟨2173580, by rfl⟩ : syracuseStep 2898107 = 4347161) B4347161
theorem B1932071 : Blo 1931435 1932071 := bstep (se 1 (by rfl) ⟨1449053, by rfl⟩ : syracuseStep 1932071 = 2898107) B2898107
theorem B2173585 : Blo 1931435 2173585 := bbase (se 2 (by rfl) ⟨815094, by rfl⟩ : syracuseStep 2173585 = 1630189) (by norm_num)
theorem B2898113 : Blo 1931435 2898113 := bstep (se 2 (by rfl) ⟨1086792, by rfl⟩ : syracuseStep 2898113 = 2173585) B2173585
theorem B1932075 : Blo 1931435 1932075 := bstep (se 1 (by rfl) ⟨1449056, by rfl⟩ : syracuseStep 1932075 = 2898113) B2898113
theorem B3667933 : Blo 1931435 3667933 := bbase (se 3 (by rfl) ⟨687737, by rfl⟩ : syracuseStep 3667933 = 1375475) (by norm_num)
theorem B4890577 : Blo 1931435 4890577 := bstep (se 2 (by rfl) ⟨1833966, by rfl⟩ : syracuseStep 4890577 = 3667933) B3667933
theorem B6520769 : Blo 1931435 6520769 := bstep (se 2 (by rfl) ⟨2445288, by rfl⟩ : syracuseStep 6520769 = 4890577) B4890577
theorem B4347179 : Blo 1931435 4347179 := bstep (se 1 (by rfl) ⟨3260384, by rfl⟩ : syracuseStep 4347179 = 6520769) B6520769
theorem B2898119 : Blo 1931435 2898119 := bstep (se 1 (by rfl) ⟨2173589, by rfl⟩ : syracuseStep 2898119 = 4347179) B4347179
theorem B1932079 : Blo 1931435 1932079 := bstep (se 1 (by rfl) ⟨1449059, by rfl⟩ : syracuseStep 1932079 = 2898119) B2898119
theorem B2898125 : Blo 1931435 2898125 := bbase (se 3 (by rfl) ⟨543398, by rfl⟩ : syracuseStep 2898125 = 1086797) (by norm_num)
theorem B1932083 : Blo 1931435 1932083 := bstep (se 1 (by rfl) ⟨1449062, by rfl⟩ : syracuseStep 1932083 = 2898125) B2898125
theorem B4347197 : Blo 1931435 4347197 := bbase (se 3 (by rfl) ⟨815099, by rfl⟩ : syracuseStep 4347197 = 1630199) (by norm_num)
theorem B2898131 : Blo 1931435 2898131 := bstep (se 1 (by rfl) ⟨2173598, by rfl⟩ : syracuseStep 2898131 = 4347197) B4347197
theorem B1932087 : Blo 1931435 1932087 := bstep (se 1 (by rfl) ⟨1449065, by rfl⟩ : syracuseStep 1932087 = 2898131) B2898131
theorem B3260405 : Blo 1931435 3260405 := bbase (se 5 (by rfl) ⟨152831, by rfl⟩ : syracuseStep 3260405 = 305663) (by norm_num)
theorem B2173603 : Blo 1931435 2173603 := bstep (se 1 (by rfl) ⟨1630202, by rfl⟩ : syracuseStep 2173603 = 3260405) B3260405
theorem B2898137 : Blo 1931435 2898137 := bstep (se 2 (by rfl) ⟨1086801, by rfl⟩ : syracuseStep 2898137 = 2173603) B2173603
theorem B1932091 : Blo 1931435 1932091 := bstep (se 1 (by rfl) ⟨1449068, by rfl⟩ : syracuseStep 1932091 = 2898137) B2898137
theorem B11750741 : Blo 1931435 11750741 := bbase (se 11 (by rfl) ⟨8606, by rfl⟩ : syracuseStep 11750741 = 17213) (by norm_num)
theorem B7833827 : Blo 1931435 7833827 := bstep (se 1 (by rfl) ⟨5875370, by rfl⟩ : syracuseStep 7833827 = 11750741) B11750741
theorem B5222551 : Blo 1931435 5222551 := bstep (se 1 (by rfl) ⟨3916913, by rfl⟩ : syracuseStep 5222551 = 7833827) B7833827
theorem B6963401 : Blo 1931435 6963401 := bstep (se 2 (by rfl) ⟨2611275, by rfl⟩ : syracuseStep 6963401 = 5222551) B5222551
theorem B4642267 : Blo 1931435 4642267 := bstep (se 1 (by rfl) ⟨3481700, by rfl⟩ : syracuseStep 4642267 = 6963401) B6963401
theorem B6189689 : Blo 1931435 6189689 := bstep (se 2 (by rfl) ⟨2321133, by rfl⟩ : syracuseStep 6189689 = 4642267) B4642267
theorem B4126459 : Blo 1931435 4126459 := bstep (se 1 (by rfl) ⟨3094844, by rfl⟩ : syracuseStep 4126459 = 6189689) B6189689
theorem B5501945 : Blo 1931435 5501945 := bstep (se 2 (by rfl) ⟨2063229, by rfl⟩ : syracuseStep 5501945 = 4126459) B4126459
theorem B14671853 : Blo 1931435 14671853 := bstep (se 3 (by rfl) ⟨2750972, by rfl⟩ : syracuseStep 14671853 = 5501945) B5501945
theorem B9781235 : Blo 1931435 9781235 := bstep (se 1 (by rfl) ⟨7335926, by rfl⟩ : syracuseStep 9781235 = 14671853) B14671853
theorem B6520823 : Blo 1931435 6520823 := bstep (se 1 (by rfl) ⟨4890617, by rfl⟩ : syracuseStep 6520823 = 9781235) B9781235
theorem B4347215 : Blo 1931435 4347215 := bstep (se 1 (by rfl) ⟨3260411, by rfl⟩ : syracuseStep 4347215 = 6520823) B6520823
theorem B2898143 : Blo 1931435 2898143 := bstep (se 1 (by rfl) ⟨2173607, by rfl⟩ : syracuseStep 2898143 = 4347215) B4347215
theorem B1932095 : Blo 1931435 1932095 := bstep (se 1 (by rfl) ⟨1449071, by rfl⟩ : syracuseStep 1932095 = 2898143) B2898143
theorem B2898149 : Blo 1931435 2898149 := bbase (se 4 (by rfl) ⟨271701, by rfl⟩ : syracuseStep 2898149 = 543403) (by norm_num)
theorem B1932099 : Blo 1931435 1932099 := bstep (se 1 (by rfl) ⟨1449074, by rfl⟩ : syracuseStep 1932099 = 2898149) B2898149
theorem B4126477 : Blo 1931435 4126477 := bbase (se 3 (by rfl) ⟨773714, by rfl⟩ : syracuseStep 4126477 = 1547429) (by norm_num)
theorem B5501969 : Blo 1931435 5501969 := bstep (se 2 (by rfl) ⟨2063238, by rfl⟩ : syracuseStep 5501969 = 4126477) B4126477
theorem B3667979 : Blo 1931435 3667979 := bstep (se 1 (by rfl) ⟨2750984, by rfl⟩ : syracuseStep 3667979 = 5501969) B5501969
theorem B2445319 : Blo 1931435 2445319 := bstep (se 1 (by rfl) ⟨1833989, by rfl⟩ : syracuseStep 2445319 = 3667979) B3667979
theorem B3260425 : Blo 1931435 3260425 := bstep (se 2 (by rfl) ⟨1222659, by rfl⟩ : syracuseStep 3260425 = 2445319) B2445319
theorem B4347233 : Blo 1931435 4347233 := bstep (se 2 (by rfl) ⟨1630212, by rfl⟩ : syracuseStep 4347233 = 3260425) B3260425
theorem B2898155 : Blo 1931435 2898155 := bstep (se 1 (by rfl) ⟨2173616, by rfl⟩ : syracuseStep 2898155 = 4347233) B4347233
theorem B1932103 : Blo 1931435 1932103 := bstep (se 1 (by rfl) ⟨1449077, by rfl⟩ : syracuseStep 1932103 = 2898155) B2898155
theorem B2173621 : Blo 1931435 2173621 := bbase (se 5 (by rfl) ⟨101888, by rfl⟩ : syracuseStep 2173621 = 203777) (by norm_num)
theorem B2898161 : Blo 1931435 2898161 := bstep (se 2 (by rfl) ⟨1086810, by rfl⟩ : syracuseStep 2898161 = 2173621) B2173621
theorem B1932107 : Blo 1931435 1932107 := bstep (se 1 (by rfl) ⟨1449080, by rfl⟩ : syracuseStep 1932107 = 2898161) B2898161
theorem B2445329 : Blo 1931435 2445329 := bbase (se 2 (by rfl) ⟨916998, by rfl⟩ : syracuseStep 2445329 = 1833997) (by norm_num)
theorem B6520877 : Blo 1931435 6520877 := bstep (se 3 (by rfl) ⟨1222664, by rfl⟩ : syracuseStep 6520877 = 2445329) B2445329
theorem B4347251 : Blo 1931435 4347251 := bstep (se 1 (by rfl) ⟨3260438, by rfl⟩ : syracuseStep 4347251 = 6520877) B6520877
theorem B2898167 : Blo 1931435 2898167 := bstep (se 1 (by rfl) ⟨2173625, by rfl⟩ : syracuseStep 2898167 = 4347251) B4347251
theorem B1932111 : Blo 1931435 1932111 := bstep (se 1 (by rfl) ⟨1449083, by rfl⟩ : syracuseStep 1932111 = 2898167) B2898167
theorem B2898173 : Blo 1931435 2898173 := bbase (se 3 (by rfl) ⟨543407, by rfl⟩ : syracuseStep 2898173 = 1086815) (by norm_num)
theorem B1932115 : Blo 1931435 1932115 := bstep (se 1 (by rfl) ⟨1449086, by rfl⟩ : syracuseStep 1932115 = 2898173) B2898173
theorem B4347269 : Blo 1931435 4347269 := bbase (se 4 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 4347269 = 815113) (by norm_num)
theorem B2898179 : Blo 1931435 2898179 := bstep (se 1 (by rfl) ⟨2173634, by rfl⟩ : syracuseStep 2898179 = 4347269) B4347269
theorem B1932119 : Blo 1931435 1932119 := bstep (se 1 (by rfl) ⟨1449089, by rfl⟩ : syracuseStep 1932119 = 2898179) B2898179
theorem B2751013 : Blo 1931435 2751013 := bbase (se 4 (by rfl) ⟨257907, by rfl⟩ : syracuseStep 2751013 = 515815) (by norm_num)
theorem B3668017 : Blo 1931435 3668017 := bstep (se 2 (by rfl) ⟨1375506, by rfl⟩ : syracuseStep 3668017 = 2751013) B2751013
theorem B4890689 : Blo 1931435 4890689 := bstep (se 2 (by rfl) ⟨1834008, by rfl⟩ : syracuseStep 4890689 = 3668017) B3668017
theorem B3260459 : Blo 1931435 3260459 := bstep (se 1 (by rfl) ⟨2445344, by rfl⟩ : syracuseStep 3260459 = 4890689) B4890689
theorem B2173639 : Blo 1931435 2173639 := bstep (se 1 (by rfl) ⟨1630229, by rfl⟩ : syracuseStep 2173639 = 3260459) B3260459
theorem B2898185 : Blo 1931435 2898185 := bstep (se 2 (by rfl) ⟨1086819, by rfl⟩ : syracuseStep 2898185 = 2173639) B2173639
theorem B1932123 : Blo 1931435 1932123 := bstep (se 1 (by rfl) ⟨1449092, by rfl⟩ : syracuseStep 1932123 = 2898185) B2898185
theorem B9781397 : Blo 1931435 9781397 := bbase (se 6 (by rfl) ⟨229251, by rfl⟩ : syracuseStep 9781397 = 458503) (by norm_num)
theorem B6520931 : Blo 1931435 6520931 := bstep (se 1 (by rfl) ⟨4890698, by rfl⟩ : syracuseStep 6520931 = 9781397) B9781397
theorem B4347287 : Blo 1931435 4347287 := bstep (se 1 (by rfl) ⟨3260465, by rfl⟩ : syracuseStep 4347287 = 6520931) B6520931
theorem B2898191 : Blo 1931435 2898191 := bstep (se 1 (by rfl) ⟨2173643, by rfl⟩ : syracuseStep 2898191 = 4347287) B4347287
theorem B1932127 : Blo 1931435 1932127 := bstep (se 1 (by rfl) ⟨1449095, by rfl⟩ : syracuseStep 1932127 = 2898191) B2898191
theorem B2898197 : Blo 1931435 2898197 := bbase (se 6 (by rfl) ⟨67926, by rfl⟩ : syracuseStep 2898197 = 135853) (by norm_num)
theorem B1932131 : Blo 1931435 1932131 := bstep (se 1 (by rfl) ⟨1449098, by rfl⟩ : syracuseStep 1932131 = 2898197) B2898197
theorem B7833989 : Blo 1931435 7833989 := bbase (se 4 (by rfl) ⟨734436, by rfl⟩ : syracuseStep 7833989 = 1468873) (by norm_num)
theorem B5222659 : Blo 1931435 5222659 := bstep (se 1 (by rfl) ⟨3916994, by rfl⟩ : syracuseStep 5222659 = 7833989) B7833989
theorem B6963545 : Blo 1931435 6963545 := bstep (se 2 (by rfl) ⟨2611329, by rfl⟩ : syracuseStep 6963545 = 5222659) B5222659
theorem B4642363 : Blo 1931435 4642363 := bstep (se 1 (by rfl) ⟨3481772, by rfl⟩ : syracuseStep 4642363 = 6963545) B6963545
theorem B24759269 : Blo 1931435 24759269 := bstep (se 4 (by rfl) ⟨2321181, by rfl⟩ : syracuseStep 24759269 = 4642363) B4642363
theorem B16506179 : Blo 1931435 16506179 := bstep (se 1 (by rfl) ⟨12379634, by rfl⟩ : syracuseStep 16506179 = 24759269) B24759269
theorem B11004119 : Blo 1931435 11004119 := bstep (se 1 (by rfl) ⟨8253089, by rfl⟩ : syracuseStep 11004119 = 16506179) B16506179
theorem B7336079 : Blo 1931435 7336079 := bstep (se 1 (by rfl) ⟨5502059, by rfl⟩ : syracuseStep 7336079 = 11004119) B11004119
theorem B4890719 : Blo 1931435 4890719 := bstep (se 1 (by rfl) ⟨3668039, by rfl⟩ : syracuseStep 4890719 = 7336079) B7336079
theorem B3260479 : Blo 1931435 3260479 := bstep (se 1 (by rfl) ⟨2445359, by rfl⟩ : syracuseStep 3260479 = 4890719) B4890719
theorem B4347305 : Blo 1931435 4347305 := bstep (se 2 (by rfl) ⟨1630239, by rfl⟩ : syracuseStep 4347305 = 3260479) B3260479
theorem B2898203 : Blo 1931435 2898203 := bstep (se 1 (by rfl) ⟨2173652, by rfl⟩ : syracuseStep 2898203 = 4347305) B4347305
theorem B1932135 : Blo 1931435 1932135 := bstep (se 1 (by rfl) ⟨1449101, by rfl⟩ : syracuseStep 1932135 = 2898203) B2898203
theorem B2173657 : Blo 1931435 2173657 := bbase (se 2 (by rfl) ⟨815121, by rfl⟩ : syracuseStep 2173657 = 1630243) (by norm_num)
theorem B2898209 : Blo 1931435 2898209 := bstep (se 2 (by rfl) ⟨1086828, by rfl⟩ : syracuseStep 2898209 = 2173657) B2173657
theorem B1932139 : Blo 1931435 1932139 := bstep (se 1 (by rfl) ⟨1449104, by rfl⟩ : syracuseStep 1932139 = 2898209) B2898209
theorem B2063281 : Blo 1931435 2063281 := bbase (se 2 (by rfl) ⟨773730, by rfl⟩ : syracuseStep 2063281 = 1547461) (by norm_num)
theorem B2751041 : Blo 1931435 2751041 := bstep (se 2 (by rfl) ⟨1031640, by rfl⟩ : syracuseStep 2751041 = 2063281) B2063281
theorem B7336109 : Blo 1931435 7336109 := bstep (se 3 (by rfl) ⟨1375520, by rfl⟩ : syracuseStep 7336109 = 2751041) B2751041
theorem B4890739 : Blo 1931435 4890739 := bstep (se 1 (by rfl) ⟨3668054, by rfl⟩ : syracuseStep 4890739 = 7336109) B7336109
theorem B6520985 : Blo 1931435 6520985 := bstep (se 2 (by rfl) ⟨2445369, by rfl⟩ : syracuseStep 6520985 = 4890739) B4890739
theorem B4347323 : Blo 1931435 4347323 := bstep (se 1 (by rfl) ⟨3260492, by rfl⟩ : syracuseStep 4347323 = 6520985) B6520985
theorem B2898215 : Blo 1931435 2898215 := bstep (se 1 (by rfl) ⟨2173661, by rfl⟩ : syracuseStep 2898215 = 4347323) B4347323
theorem B1932143 : Blo 1931435 1932143 := bstep (se 1 (by rfl) ⟨1449107, by rfl⟩ : syracuseStep 1932143 = 2898215) B2898215
theorem B2898221 : Blo 1931435 2898221 := bbase (se 3 (by rfl) ⟨543416, by rfl⟩ : syracuseStep 2898221 = 1086833) (by norm_num)
theorem B1932147 : Blo 1931435 1932147 := bstep (se 1 (by rfl) ⟨1449110, by rfl⟩ : syracuseStep 1932147 = 2898221) B2898221
theorem B4347341 : Blo 1931435 4347341 := bbase (se 3 (by rfl) ⟨815126, by rfl⟩ : syracuseStep 4347341 = 1630253) (by norm_num)
theorem B2898227 : Blo 1931435 2898227 := bstep (se 1 (by rfl) ⟨2173670, by rfl⟩ : syracuseStep 2898227 = 4347341) B4347341
theorem B1932151 : Blo 1931435 1932151 := bstep (se 1 (by rfl) ⟨1449113, by rfl⟩ : syracuseStep 1932151 = 2898227) B2898227
theorem B2445385 : Blo 1931435 2445385 := bbase (se 2 (by rfl) ⟨917019, by rfl⟩ : syracuseStep 2445385 = 1834039) (by norm_num)
theorem B3260513 : Blo 1931435 3260513 := bstep (se 2 (by rfl) ⟨1222692, by rfl⟩ : syracuseStep 3260513 = 2445385) B2445385
theorem B2173675 : Blo 1931435 2173675 := bstep (se 1 (by rfl) ⟨1630256, by rfl⟩ : syracuseStep 2173675 = 3260513) B3260513
theorem B2898233 : Blo 1931435 2898233 := bstep (se 2 (by rfl) ⟨1086837, by rfl⟩ : syracuseStep 2898233 = 2173675) B2173675
theorem B1932155 : Blo 1931435 1932155 := bstep (se 1 (by rfl) ⟨1449116, by rfl⟩ : syracuseStep 1932155 = 2898233) B2898233
theorem B7834085 : Blo 1931435 7834085 := bbase (se 4 (by rfl) ⟨734445, by rfl⟩ : syracuseStep 7834085 = 1468891) (by norm_num)
theorem B5222723 : Blo 1931435 5222723 := bstep (se 1 (by rfl) ⟨3917042, by rfl⟩ : syracuseStep 5222723 = 7834085) B7834085
theorem B13927261 : Blo 1931435 13927261 := bstep (se 3 (by rfl) ⟨2611361, by rfl⟩ : syracuseStep 13927261 = 5222723) B5222723
theorem B18569681 : Blo 1931435 18569681 := bstep (se 2 (by rfl) ⟨6963630, by rfl⟩ : syracuseStep 18569681 = 13927261) B13927261
theorem B12379787 : Blo 1931435 12379787 := bstep (se 1 (by rfl) ⟨9284840, by rfl⟩ : syracuseStep 12379787 = 18569681) B18569681
theorem B8253191 : Blo 1931435 8253191 := bstep (se 1 (by rfl) ⟨6189893, by rfl⟩ : syracuseStep 8253191 = 12379787) B12379787
theorem B22008509 : Blo 1931435 22008509 := bstep (se 3 (by rfl) ⟨4126595, by rfl⟩ : syracuseStep 22008509 = 8253191) B8253191
theorem B14672339 : Blo 1931435 14672339 := bstep (se 1 (by rfl) ⟨11004254, by rfl⟩ : syracuseStep 14672339 = 22008509) B22008509
theorem B9781559 : Blo 1931435 9781559 := bstep (se 1 (by rfl) ⟨7336169, by rfl⟩ : syracuseStep 9781559 = 14672339) B14672339
theorem B6521039 : Blo 1931435 6521039 := bstep (se 1 (by rfl) ⟨4890779, by rfl⟩ : syracuseStep 6521039 = 9781559) B9781559
theorem B4347359 : Blo 1931435 4347359 := bstep (se 1 (by rfl) ⟨3260519, by rfl⟩ : syracuseStep 4347359 = 6521039) B6521039
theorem B2898239 : Blo 1931435 2898239 := bstep (se 1 (by rfl) ⟨2173679, by rfl⟩ : syracuseStep 2898239 = 4347359) B4347359
theorem B1932159 : Blo 1931435 1932159 := bstep (se 1 (by rfl) ⟨1449119, by rfl⟩ : syracuseStep 1932159 = 2898239) B2898239
theorem B2898245 : Blo 1931435 2898245 := bbase (se 4 (by rfl) ⟨271710, by rfl⟩ : syracuseStep 2898245 = 543421) (by norm_num)
theorem B1932163 : Blo 1931435 1932163 := bstep (se 1 (by rfl) ⟨1449122, by rfl⟩ : syracuseStep 1932163 = 2898245) B2898245
theorem B3260533 : Blo 1931435 3260533 := bbase (se 5 (by rfl) ⟨152837, by rfl⟩ : syracuseStep 3260533 = 305675) (by norm_num)
theorem B4347377 : Blo 1931435 4347377 := bstep (se 2 (by rfl) ⟨1630266, by rfl⟩ : syracuseStep 4347377 = 3260533) B3260533
theorem B2898251 : Blo 1931435 2898251 := bstep (se 1 (by rfl) ⟨2173688, by rfl⟩ : syracuseStep 2898251 = 4347377) B4347377
theorem B1932167 : Blo 1931435 1932167 := bstep (se 1 (by rfl) ⟨1449125, by rfl⟩ : syracuseStep 1932167 = 2898251) B2898251
theorem B2173693 : Blo 1931435 2173693 := bbase (se 3 (by rfl) ⟨407567, by rfl⟩ : syracuseStep 2173693 = 815135) (by norm_num)
theorem B2898257 : Blo 1931435 2898257 := bstep (se 2 (by rfl) ⟨1086846, by rfl⟩ : syracuseStep 2898257 = 2173693) B2173693
theorem B1932171 : Blo 1931435 1932171 := bstep (se 1 (by rfl) ⟨1449128, by rfl⟩ : syracuseStep 1932171 = 2898257) B2898257
theorem B6521093 : Blo 1931435 6521093 := bbase (se 4 (by rfl) ⟨611352, by rfl⟩ : syracuseStep 6521093 = 1222705) (by norm_num)
theorem B4347395 : Blo 1931435 4347395 := bstep (se 1 (by rfl) ⟨3260546, by rfl⟩ : syracuseStep 4347395 = 6521093) B6521093
theorem B2898263 : Blo 1931435 2898263 := bstep (se 1 (by rfl) ⟨2173697, by rfl⟩ : syracuseStep 2898263 = 4347395) B4347395
theorem B1932175 : Blo 1931435 1932175 := bstep (se 1 (by rfl) ⟨1449131, by rfl⟩ : syracuseStep 1932175 = 2898263) B2898263
theorem B2898269 : Blo 1931435 2898269 := bbase (se 3 (by rfl) ⟨543425, by rfl⟩ : syracuseStep 2898269 = 1086851) (by norm_num)
theorem B1932179 : Blo 1931435 1932179 := bstep (se 1 (by rfl) ⟨1449134, by rfl⟩ : syracuseStep 1932179 = 2898269) B2898269
theorem B4347413 : Blo 1931435 4347413 := bbase (se 6 (by rfl) ⟨101892, by rfl⟩ : syracuseStep 4347413 = 203785) (by norm_num)
theorem B2898275 : Blo 1931435 2898275 := bstep (se 1 (by rfl) ⟨2173706, by rfl⟩ : syracuseStep 2898275 = 4347413) B4347413
theorem B1932183 : Blo 1931435 1932183 := bstep (se 1 (by rfl) ⟨1449137, by rfl⟩ : syracuseStep 1932183 = 2898275) B2898275
theorem B7336277 : Blo 1931435 7336277 := bbase (se 10 (by rfl) ⟨10746, by rfl⟩ : syracuseStep 7336277 = 21493) (by norm_num)
theorem B4890851 : Blo 1931435 4890851 := bstep (se 1 (by rfl) ⟨3668138, by rfl⟩ : syracuseStep 4890851 = 7336277) B7336277
theorem B3260567 : Blo 1931435 3260567 := bstep (se 1 (by rfl) ⟨2445425, by rfl⟩ : syracuseStep 3260567 = 4890851) B4890851
theorem B2173711 : Blo 1931435 2173711 := bstep (se 1 (by rfl) ⟨1630283, by rfl⟩ : syracuseStep 2173711 = 3260567) B3260567
theorem B2898281 : Blo 1931435 2898281 := bstep (se 2 (by rfl) ⟨1086855, by rfl⟩ : syracuseStep 2898281 = 2173711) B2173711
theorem B1932187 : Blo 1931435 1932187 := bstep (se 1 (by rfl) ⟨1449140, by rfl⟩ : syracuseStep 1932187 = 2898281) B2898281
theorem B11004437 : Blo 1931435 11004437 := bbase (se 6 (by rfl) ⟨257916, by rfl⟩ : syracuseStep 11004437 = 515833) (by norm_num)
theorem B7336291 : Blo 1931435 7336291 := bstep (se 1 (by rfl) ⟨5502218, by rfl⟩ : syracuseStep 7336291 = 11004437) B11004437
theorem B9781721 : Blo 1931435 9781721 := bstep (se 2 (by rfl) ⟨3668145, by rfl⟩ : syracuseStep 9781721 = 7336291) B7336291
theorem B6521147 : Blo 1931435 6521147 := bstep (se 1 (by rfl) ⟨4890860, by rfl⟩ : syracuseStep 6521147 = 9781721) B9781721
theorem B4347431 : Blo 1931435 4347431 := bstep (se 1 (by rfl) ⟨3260573, by rfl⟩ : syracuseStep 4347431 = 6521147) B6521147
theorem B2898287 : Blo 1931435 2898287 := bstep (se 1 (by rfl) ⟨2173715, by rfl⟩ : syracuseStep 2898287 = 4347431) B4347431
theorem B1932191 : Blo 1931435 1932191 := bstep (se 1 (by rfl) ⟨1449143, by rfl⟩ : syracuseStep 1932191 = 2898287) B2898287
theorem B2898293 : Blo 1931435 2898293 := bbase (se 5 (by rfl) ⟨135857, by rfl⟩ : syracuseStep 2898293 = 271715) (by norm_num)
theorem B1932195 : Blo 1931435 1932195 := bstep (se 1 (by rfl) ⟨1449146, by rfl⟩ : syracuseStep 1932195 = 2898293) B2898293
theorem B2063341 : Blo 1931435 2063341 := bbase (se 3 (by rfl) ⟨386876, by rfl⟩ : syracuseStep 2063341 = 773753) (by norm_num)
theorem B2751121 : Blo 1931435 2751121 := bstep (se 2 (by rfl) ⟨1031670, by rfl⟩ : syracuseStep 2751121 = 2063341) B2063341
theorem B3668161 : Blo 1931435 3668161 := bstep (se 2 (by rfl) ⟨1375560, by rfl⟩ : syracuseStep 3668161 = 2751121) B2751121
theorem B4890881 : Blo 1931435 4890881 := bstep (se 2 (by rfl) ⟨1834080, by rfl⟩ : syracuseStep 4890881 = 3668161) B3668161
theorem B3260587 : Blo 1931435 3260587 := bstep (se 1 (by rfl) ⟨2445440, by rfl⟩ : syracuseStep 3260587 = 4890881) B4890881
theorem B4347449 : Blo 1931435 4347449 := bstep (se 2 (by rfl) ⟨1630293, by rfl⟩ : syracuseStep 4347449 = 3260587) B3260587
theorem B2898299 : Blo 1931435 2898299 := bstep (se 1 (by rfl) ⟨2173724, by rfl⟩ : syracuseStep 2898299 = 4347449) B4347449
theorem B1932199 : Blo 1931435 1932199 := bstep (se 1 (by rfl) ⟨1449149, by rfl⟩ : syracuseStep 1932199 = 2898299) B2898299
theorem B2173729 : Blo 1931435 2173729 := bbase (se 2 (by rfl) ⟨815148, by rfl⟩ : syracuseStep 2173729 = 1630297) (by norm_num)
theorem B2898305 : Blo 1931435 2898305 := bstep (se 2 (by rfl) ⟨1086864, by rfl⟩ : syracuseStep 2898305 = 2173729) B2173729
theorem B1932203 : Blo 1931435 1932203 := bstep (se 1 (by rfl) ⟨1449152, by rfl⟩ : syracuseStep 1932203 = 2898305) B2898305
theorem B4890901 : Blo 1931435 4890901 := bbase (se 6 (by rfl) ⟨114630, by rfl⟩ : syracuseStep 4890901 = 229261) (by norm_num)
theorem B6521201 : Blo 1931435 6521201 := bstep (se 2 (by rfl) ⟨2445450, by rfl⟩ : syracuseStep 6521201 = 4890901) B4890901
theorem B4347467 : Blo 1931435 4347467 := bstep (se 1 (by rfl) ⟨3260600, by rfl⟩ : syracuseStep 4347467 = 6521201) B6521201
theorem B2898311 : Blo 1931435 2898311 := bstep (se 1 (by rfl) ⟨2173733, by rfl⟩ : syracuseStep 2898311 = 4347467) B4347467
theorem B1932207 : Blo 1931435 1932207 := bstep (se 1 (by rfl) ⟨1449155, by rfl⟩ : syracuseStep 1932207 = 2898311) B2898311
theorem B2898317 : Blo 1931435 2898317 := bbase (se 3 (by rfl) ⟨543434, by rfl⟩ : syracuseStep 2898317 = 1086869) (by norm_num)
theorem B1932211 : Blo 1931435 1932211 := bstep (se 1 (by rfl) ⟨1449158, by rfl⟩ : syracuseStep 1932211 = 2898317) B2898317
theorem B4347485 : Blo 1931435 4347485 := bbase (se 3 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 4347485 = 1630307) (by norm_num)
theorem B2898323 : Blo 1931435 2898323 := bstep (se 1 (by rfl) ⟨2173742, by rfl⟩ : syracuseStep 2898323 = 4347485) B4347485
theorem B1932215 : Blo 1931435 1932215 := bstep (se 1 (by rfl) ⟨1449161, by rfl⟩ : syracuseStep 1932215 = 2898323) B2898323
theorem B3260621 : Blo 1931435 3260621 := bbase (se 3 (by rfl) ⟨611366, by rfl⟩ : syracuseStep 3260621 = 1222733) (by norm_num)
theorem B2173747 : Blo 1931435 2173747 := bstep (se 1 (by rfl) ⟨1630310, by rfl⟩ : syracuseStep 2173747 = 3260621) B3260621
theorem B2898329 : Blo 1931435 2898329 := bstep (se 2 (by rfl) ⟨1086873, by rfl⟩ : syracuseStep 2898329 = 2173747) B2173747
theorem B1932219 : Blo 1931435 1932219 := bstep (se 1 (by rfl) ⟨1449164, by rfl⟩ : syracuseStep 1932219 = 2898329) B2898329
theorem B3917173 : Blo 1931435 3917173 := bbase (se 5 (by rfl) ⟨183617, by rfl⟩ : syracuseStep 3917173 = 367235) (by norm_num)
theorem B5222897 : Blo 1931435 5222897 := bstep (se 2 (by rfl) ⟨1958586, by rfl⟩ : syracuseStep 5222897 = 3917173) B3917173
theorem B3481931 : Blo 1931435 3481931 := bstep (se 1 (by rfl) ⟨2611448, by rfl⟩ : syracuseStep 3481931 = 5222897) B5222897
theorem B2321287 : Blo 1931435 2321287 := bstep (se 1 (by rfl) ⟨1740965, by rfl⟩ : syracuseStep 2321287 = 3481931) B3481931
theorem B12380197 : Blo 1931435 12380197 := bstep (se 4 (by rfl) ⟨1160643, by rfl⟩ : syracuseStep 12380197 = 2321287) B2321287
theorem B16506929 : Blo 1931435 16506929 := bstep (se 2 (by rfl) ⟨6190098, by rfl⟩ : syracuseStep 16506929 = 12380197) B12380197
theorem B11004619 : Blo 1931435 11004619 := bstep (se 1 (by rfl) ⟨8253464, by rfl⟩ : syracuseStep 11004619 = 16506929) B16506929
theorem B14672825 : Blo 1931435 14672825 := bstep (se 2 (by rfl) ⟨5502309, by rfl⟩ : syracuseStep 14672825 = 11004619) B11004619
theorem B9781883 : Blo 1931435 9781883 := bstep (se 1 (by rfl) ⟨7336412, by rfl⟩ : syracuseStep 9781883 = 14672825) B14672825
theorem B6521255 : Blo 1931435 6521255 := bstep (se 1 (by rfl) ⟨4890941, by rfl⟩ : syracuseStep 6521255 = 9781883) B9781883
theorem B4347503 : Blo 1931435 4347503 := bstep (se 1 (by rfl) ⟨3260627, by rfl⟩ : syracuseStep 4347503 = 6521255) B6521255
theorem B2898335 : Blo 1931435 2898335 := bstep (se 1 (by rfl) ⟨2173751, by rfl⟩ : syracuseStep 2898335 = 4347503) B4347503
theorem B1932223 : Blo 1931435 1932223 := bstep (se 1 (by rfl) ⟨1449167, by rfl⟩ : syracuseStep 1932223 = 2898335) B2898335
theorem B2898341 : Blo 1931435 2898341 := bbase (se 4 (by rfl) ⟨271719, by rfl⟩ : syracuseStep 2898341 = 543439) (by norm_num)
theorem B1932227 : Blo 1931435 1932227 := bstep (se 1 (by rfl) ⟨1449170, by rfl⟩ : syracuseStep 1932227 = 2898341) B2898341
theorem B2445481 : Blo 1931435 2445481 := bbase (se 2 (by rfl) ⟨917055, by rfl⟩ : syracuseStep 2445481 = 1834111) (by norm_num)
theorem B3260641 : Blo 1931435 3260641 := bstep (se 2 (by rfl) ⟨1222740, by rfl⟩ : syracuseStep 3260641 = 2445481) B2445481
theorem B4347521 : Blo 1931435 4347521 := bstep (se 2 (by rfl) ⟨1630320, by rfl⟩ : syracuseStep 4347521 = 3260641) B3260641
theorem B2898347 : Blo 1931435 2898347 := bstep (se 1 (by rfl) ⟨2173760, by rfl⟩ : syracuseStep 2898347 = 4347521) B4347521
theorem B1932231 : Blo 1931435 1932231 := bstep (se 1 (by rfl) ⟨1449173, by rfl⟩ : syracuseStep 1932231 = 2898347) B2898347
theorem B2173765 : Blo 1931435 2173765 := bbase (se 4 (by rfl) ⟨203790, by rfl⟩ : syracuseStep 2173765 = 407581) (by norm_num)
theorem B2898353 : Blo 1931435 2898353 := bstep (se 2 (by rfl) ⟨1086882, by rfl⟩ : syracuseStep 2898353 = 2173765) B2173765
theorem B1932235 : Blo 1931435 1932235 := bstep (se 1 (by rfl) ⟨1449176, by rfl⟩ : syracuseStep 1932235 = 2898353) B2898353
theorem B3668237 : Blo 1931435 3668237 := bbase (se 3 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 3668237 = 1375589) (by norm_num)
theorem B2445491 : Blo 1931435 2445491 := bstep (se 1 (by rfl) ⟨1834118, by rfl⟩ : syracuseStep 2445491 = 3668237) B3668237
theorem B6521309 : Blo 1931435 6521309 := bstep (se 3 (by rfl) ⟨1222745, by rfl⟩ : syracuseStep 6521309 = 2445491) B2445491
theorem B4347539 : Blo 1931435 4347539 := bstep (se 1 (by rfl) ⟨3260654, by rfl⟩ : syracuseStep 4347539 = 6521309) B6521309
theorem B2898359 : Blo 1931435 2898359 := bstep (se 1 (by rfl) ⟨2173769, by rfl⟩ : syracuseStep 2898359 = 4347539) B4347539
theorem B1932239 : Blo 1931435 1932239 := bstep (se 1 (by rfl) ⟨1449179, by rfl⟩ : syracuseStep 1932239 = 2898359) B2898359
theorem B2898365 : Blo 1931435 2898365 := bbase (se 3 (by rfl) ⟨543443, by rfl⟩ : syracuseStep 2898365 = 1086887) (by norm_num)
theorem B1932243 : Blo 1931435 1932243 := bstep (se 1 (by rfl) ⟨1449182, by rfl⟩ : syracuseStep 1932243 = 2898365) B2898365
theorem B4347557 : Blo 1931435 4347557 := bbase (se 4 (by rfl) ⟨407583, by rfl⟩ : syracuseStep 4347557 = 815167) (by norm_num)
theorem B2898371 : Blo 1931435 2898371 := bstep (se 1 (by rfl) ⟨2173778, by rfl⟩ : syracuseStep 2898371 = 4347557) B4347557
theorem B1932247 : Blo 1931435 1932247 := bstep (se 1 (by rfl) ⟨1449185, by rfl⟩ : syracuseStep 1932247 = 2898371) B2898371
theorem B4891013 : Blo 1931435 4891013 := bbase (se 4 (by rfl) ⟨458532, by rfl⟩ : syracuseStep 4891013 = 917065) (by norm_num)
theorem B3260675 : Blo 1931435 3260675 := bstep (se 1 (by rfl) ⟨2445506, by rfl⟩ : syracuseStep 3260675 = 4891013) B4891013
theorem B2173783 : Blo 1931435 2173783 := bstep (se 1 (by rfl) ⟨1630337, by rfl⟩ : syracuseStep 2173783 = 3260675) B3260675
theorem B2898377 : Blo 1931435 2898377 := bstep (se 2 (by rfl) ⟨1086891, by rfl⟩ : syracuseStep 2898377 = 2173783) B2173783
theorem B1932251 : Blo 1931435 1932251 := bstep (se 1 (by rfl) ⟨1449188, by rfl⟩ : syracuseStep 1932251 = 2898377) B2898377
theorem B3095101 : Blo 1931435 3095101 := bbase (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) (by norm_num)
theorem B4126801 : Blo 1931435 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B5502401 : Blo 1931435 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B3668267 : Blo 1931435 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B9782045 : Blo 1931435 9782045 := bstep (se 3 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 9782045 = 3668267) B3668267
theorem B6521363 : Blo 1931435 6521363 := bstep (se 1 (by rfl) ⟨4891022, by rfl⟩ : syracuseStep 6521363 = 9782045) B9782045
theorem B4347575 : Blo 1931435 4347575 := bstep (se 1 (by rfl) ⟨3260681, by rfl⟩ : syracuseStep 4347575 = 6521363) B6521363
theorem B2898383 : Blo 1931435 2898383 := bstep (se 1 (by rfl) ⟨2173787, by rfl⟩ : syracuseStep 2898383 = 4347575) B4347575
theorem B1932255 : Blo 1931435 1932255 := bstep (se 1 (by rfl) ⟨1449191, by rfl⟩ : syracuseStep 1932255 = 2898383) B2898383
theorem B2898389 : Blo 1931435 2898389 := bbase (se 7 (by rfl) ⟨33965, by rfl⟩ : syracuseStep 2898389 = 67931) (by norm_num)
theorem B1932259 : Blo 1931435 1932259 := bstep (se 1 (by rfl) ⟨1449194, by rfl⟩ : syracuseStep 1932259 = 2898389) B2898389
theorem B7336565 : Blo 1931435 7336565 := bbase (se 5 (by rfl) ⟨343901, by rfl⟩ : syracuseStep 7336565 = 687803) (by norm_num)
theorem B4891043 : Blo 1931435 4891043 := bstep (se 1 (by rfl) ⟨3668282, by rfl⟩ : syracuseStep 4891043 = 7336565) B7336565
theorem B3260695 : Blo 1931435 3260695 := bstep (se 1 (by rfl) ⟨2445521, by rfl⟩ : syracuseStep 3260695 = 4891043) B4891043
theorem B4347593 : Blo 1931435 4347593 := bstep (se 2 (by rfl) ⟨1630347, by rfl⟩ : syracuseStep 4347593 = 3260695) B3260695
theorem B2898395 : Blo 1931435 2898395 := bstep (se 1 (by rfl) ⟨2173796, by rfl⟩ : syracuseStep 2898395 = 4347593) B4347593
theorem B1932263 : Blo 1931435 1932263 := bstep (se 1 (by rfl) ⟨1449197, by rfl⟩ : syracuseStep 1932263 = 2898395) B2898395
theorem B2173801 : Blo 1931435 2173801 := bbase (se 2 (by rfl) ⟨815175, by rfl⟩ : syracuseStep 2173801 = 1630351) (by norm_num)
theorem B2898401 : Blo 1931435 2898401 := bstep (se 2 (by rfl) ⟨1086900, by rfl⟩ : syracuseStep 2898401 = 2173801) B2173801
theorem B1932267 : Blo 1931435 1932267 := bstep (se 1 (by rfl) ⟨1449200, by rfl⟩ : syracuseStep 1932267 = 2898401) B2898401
theorem B2321345 : Blo 1931435 2321345 := bbase (se 2 (by rfl) ⟨870504, by rfl⟩ : syracuseStep 2321345 = 1741009) (by norm_num)
theorem B6190253 : Blo 1931435 6190253 := bstep (se 3 (by rfl) ⟨1160672, by rfl⟩ : syracuseStep 6190253 = 2321345) B2321345
theorem B4126835 : Blo 1931435 4126835 := bstep (se 1 (by rfl) ⟨3095126, by rfl⟩ : syracuseStep 4126835 = 6190253) B6190253
theorem B11004893 : Blo 1931435 11004893 := bstep (se 3 (by rfl) ⟨2063417, by rfl⟩ : syracuseStep 11004893 = 4126835) B4126835
theorem B7336595 : Blo 1931435 7336595 := bstep (se 1 (by rfl) ⟨5502446, by rfl⟩ : syracuseStep 7336595 = 11004893) B11004893
theorem B4891063 : Blo 1931435 4891063 := bstep (se 1 (by rfl) ⟨3668297, by rfl⟩ : syracuseStep 4891063 = 7336595) B7336595
theorem B6521417 : Blo 1931435 6521417 := bstep (se 2 (by rfl) ⟨2445531, by rfl⟩ : syracuseStep 6521417 = 4891063) B4891063
theorem B4347611 : Blo 1931435 4347611 := bstep (se 1 (by rfl) ⟨3260708, by rfl⟩ : syracuseStep 4347611 = 6521417) B6521417
theorem B2898407 : Blo 1931435 2898407 := bstep (se 1 (by rfl) ⟨2173805, by rfl⟩ : syracuseStep 2898407 = 4347611) B4347611
theorem B1932271 : Blo 1931435 1932271 := bstep (se 1 (by rfl) ⟨1449203, by rfl⟩ : syracuseStep 1932271 = 2898407) B2898407
theorem B2898413 : Blo 1931435 2898413 := bbase (se 3 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 2898413 = 1086905) (by norm_num)
theorem B1932275 : Blo 1931435 1932275 := bstep (se 1 (by rfl) ⟨1449206, by rfl⟩ : syracuseStep 1932275 = 2898413) B2898413
theorem B4347629 : Blo 1931435 4347629 := bbase (se 3 (by rfl) ⟨815180, by rfl⟩ : syracuseStep 4347629 = 1630361) (by norm_num)
theorem B2898419 : Blo 1931435 2898419 := bstep (se 1 (by rfl) ⟨2173814, by rfl⟩ : syracuseStep 2898419 = 4347629) B4347629
theorem B1932279 : Blo 1931435 1932279 := bstep (se 1 (by rfl) ⟨1449209, by rfl⟩ : syracuseStep 1932279 = 2898419) B2898419
theorem B2937973 : Blo 1931435 2937973 := bbase (se 5 (by rfl) ⟨137717, by rfl⟩ : syracuseStep 2937973 = 275435) (by norm_num)
theorem B3917297 : Blo 1931435 3917297 := bstep (se 2 (by rfl) ⟨1468986, by rfl⟩ : syracuseStep 3917297 = 2937973) B2937973
theorem B2611531 : Blo 1931435 2611531 := bstep (se 1 (by rfl) ⟨1958648, by rfl⟩ : syracuseStep 2611531 = 3917297) B3917297
theorem B3482041 : Blo 1931435 3482041 := bstep (se 2 (by rfl) ⟨1305765, by rfl⟩ : syracuseStep 3482041 = 2611531) B2611531
theorem B4642721 : Blo 1931435 4642721 := bstep (se 2 (by rfl) ⟨1741020, by rfl⟩ : syracuseStep 4642721 = 3482041) B3482041
theorem B3095147 : Blo 1931435 3095147 := bstep (se 1 (by rfl) ⟨2321360, by rfl⟩ : syracuseStep 3095147 = 4642721) B4642721
theorem B2063431 : Blo 1931435 2063431 := bstep (se 1 (by rfl) ⟨1547573, by rfl⟩ : syracuseStep 2063431 = 3095147) B3095147
theorem B2751241 : Blo 1931435 2751241 := bstep (se 2 (by rfl) ⟨1031715, by rfl⟩ : syracuseStep 2751241 = 2063431) B2063431
theorem B3668321 : Blo 1931435 3668321 := bstep (se 2 (by rfl) ⟨1375620, by rfl⟩ : syracuseStep 3668321 = 2751241) B2751241
theorem B2445547 : Blo 1931435 2445547 := bstep (se 1 (by rfl) ⟨1834160, by rfl⟩ : syracuseStep 2445547 = 3668321) B3668321
theorem B3260729 : Blo 1931435 3260729 := bstep (se 2 (by rfl) ⟨1222773, by rfl⟩ : syracuseStep 3260729 = 2445547) B2445547
theorem B2173819 : Blo 1931435 2173819 := bstep (se 1 (by rfl) ⟨1630364, by rfl⟩ : syracuseStep 2173819 = 3260729) B3260729
theorem B2898425 : Blo 1931435 2898425 := bstep (se 2 (by rfl) ⟨1086909, by rfl⟩ : syracuseStep 2898425 = 2173819) B2173819
theorem B1932283 : Blo 1931435 1932283 := bstep (se 1 (by rfl) ⟨1449212, by rfl⟩ : syracuseStep 1932283 = 2898425) B2898425
theorem B16732693 : Blo 1931435 16732693 := bbase (se 6 (by rfl) ⟨392172, by rfl⟩ : syracuseStep 16732693 = 784345) (by norm_num)
theorem B22310257 : Blo 1931435 22310257 := bstep (se 2 (by rfl) ⟨8366346, by rfl⟩ : syracuseStep 22310257 = 16732693) B16732693
theorem B29747009 : Blo 1931435 29747009 := bstep (se 2 (by rfl) ⟨11155128, by rfl⟩ : syracuseStep 29747009 = 22310257) B22310257
theorem B19831339 : Blo 1931435 19831339 := bstep (se 1 (by rfl) ⟨14873504, by rfl⟩ : syracuseStep 19831339 = 29747009) B29747009
theorem B26441785 : Blo 1931435 26441785 := bstep (se 2 (by rfl) ⟨9915669, by rfl⟩ : syracuseStep 26441785 = 19831339) B19831339
theorem B141022853 : Blo 1931435 141022853 := bstep (se 4 (by rfl) ⟨13220892, by rfl⟩ : syracuseStep 141022853 = 26441785) B26441785
theorem B94015235 : Blo 1931435 94015235 := bstep (se 1 (by rfl) ⟨70511426, by rfl⟩ : syracuseStep 94015235 = 141022853) B141022853
theorem B62676823 : Blo 1931435 62676823 := bstep (se 1 (by rfl) ⟨47007617, by rfl⟩ : syracuseStep 62676823 = 94015235) B94015235
theorem B83569097 : Blo 1931435 83569097 := bstep (se 2 (by rfl) ⟨31338411, by rfl⟩ : syracuseStep 83569097 = 62676823) B62676823
theorem B55712731 : Blo 1931435 55712731 := bstep (se 1 (by rfl) ⟨41784548, by rfl⟩ : syracuseStep 55712731 = 83569097) B83569097
theorem B74283641 : Blo 1931435 74283641 := bstep (se 2 (by rfl) ⟨27856365, by rfl⟩ : syracuseStep 74283641 = 55712731) B55712731
theorem B49522427 : Blo 1931435 49522427 := bstep (se 1 (by rfl) ⟨37141820, by rfl⟩ : syracuseStep 49522427 = 74283641) B74283641
theorem B33014951 : Blo 1931435 33014951 := bstep (se 1 (by rfl) ⟨24761213, by rfl⟩ : syracuseStep 33014951 = 49522427) B49522427
theorem B22009967 : Blo 1931435 22009967 := bstep (se 1 (by rfl) ⟨16507475, by rfl⟩ : syracuseStep 22009967 = 33014951) B33014951
theorem B14673311 : Blo 1931435 14673311 := bstep (se 1 (by rfl) ⟨11004983, by rfl⟩ : syracuseStep 14673311 = 22009967) B22009967
theorem B9782207 : Blo 1931435 9782207 := bstep (se 1 (by rfl) ⟨7336655, by rfl⟩ : syracuseStep 9782207 = 14673311) B14673311
theorem B6521471 : Blo 1931435 6521471 := bstep (se 1 (by rfl) ⟨4891103, by rfl⟩ : syracuseStep 6521471 = 9782207) B9782207
theorem B4347647 : Blo 1931435 4347647 := bstep (se 1 (by rfl) ⟨3260735, by rfl⟩ : syracuseStep 4347647 = 6521471) B6521471
theorem B2898431 : Blo 1931435 2898431 := bstep (se 1 (by rfl) ⟨2173823, by rfl⟩ : syracuseStep 2898431 = 4347647) B4347647
theorem B1932287 : Blo 1931435 1932287 := bstep (se 1 (by rfl) ⟨1449215, by rfl⟩ : syracuseStep 1932287 = 2898431) B2898431
theorem B2898437 : Blo 1931435 2898437 := bbase (se 4 (by rfl) ⟨271728, by rfl⟩ : syracuseStep 2898437 = 543457) (by norm_num)
theorem B1932291 : Blo 1931435 1932291 := bstep (se 1 (by rfl) ⟨1449218, by rfl⟩ : syracuseStep 1932291 = 2898437) B2898437
theorem B3260749 : Blo 1931435 3260749 := bbase (se 3 (by rfl) ⟨611390, by rfl⟩ : syracuseStep 3260749 = 1222781) (by norm_num)
theorem B4347665 : Blo 1931435 4347665 := bstep (se 2 (by rfl) ⟨1630374, by rfl⟩ : syracuseStep 4347665 = 3260749) B3260749
theorem B2898443 : Blo 1931435 2898443 := bstep (se 1 (by rfl) ⟨2173832, by rfl⟩ : syracuseStep 2898443 = 4347665) B4347665
theorem B1932295 : Blo 1931435 1932295 := bstep (se 1 (by rfl) ⟨1449221, by rfl⟩ : syracuseStep 1932295 = 2898443) B2898443
theorem B2173837 : Blo 1931435 2173837 := bbase (se 3 (by rfl) ⟨407594, by rfl⟩ : syracuseStep 2173837 = 815189) (by norm_num)
theorem B2898449 : Blo 1931435 2898449 := bstep (se 2 (by rfl) ⟨1086918, by rfl⟩ : syracuseStep 2898449 = 2173837) B2173837
theorem B1932299 : Blo 1931435 1932299 := bstep (se 1 (by rfl) ⟨1449224, by rfl⟩ : syracuseStep 1932299 = 2898449) B2898449
theorem B6521525 : Blo 1931435 6521525 := bbase (se 5 (by rfl) ⟨305696, by rfl⟩ : syracuseStep 6521525 = 611393) (by norm_num)
theorem B4347683 : Blo 1931435 4347683 := bstep (se 1 (by rfl) ⟨3260762, by rfl⟩ : syracuseStep 4347683 = 6521525) B6521525
theorem B2898455 : Blo 1931435 2898455 := bstep (se 1 (by rfl) ⟨2173841, by rfl⟩ : syracuseStep 2898455 = 4347683) B4347683
theorem B1932303 : Blo 1931435 1932303 := bstep (se 1 (by rfl) ⟨1449227, by rfl⟩ : syracuseStep 1932303 = 2898455) B2898455
theorem B2898461 : Blo 1931435 2898461 := bbase (se 3 (by rfl) ⟨543461, by rfl⟩ : syracuseStep 2898461 = 1086923) (by norm_num)
theorem B1932307 : Blo 1931435 1932307 := bstep (se 1 (by rfl) ⟨1449230, by rfl⟩ : syracuseStep 1932307 = 2898461) B2898461
theorem B4347701 : Blo 1931435 4347701 := bbase (se 5 (by rfl) ⟨203798, by rfl⟩ : syracuseStep 4347701 = 407597) (by norm_num)
theorem B2898467 : Blo 1931435 2898467 := bstep (se 1 (by rfl) ⟨2173850, by rfl⟩ : syracuseStep 2898467 = 4347701) B4347701
theorem B1932311 : Blo 1931435 1932311 := bstep (se 1 (by rfl) ⟨1449233, by rfl⟩ : syracuseStep 1932311 = 2898467) B2898467
theorem B12380789 : Blo 1931435 12380789 := bbase (se 5 (by rfl) ⟨580349, by rfl⟩ : syracuseStep 12380789 = 1160699) (by norm_num)
theorem B8253859 : Blo 1931435 8253859 := bstep (se 1 (by rfl) ⟨6190394, by rfl⟩ : syracuseStep 8253859 = 12380789) B12380789
theorem B11005145 : Blo 1931435 11005145 := bstep (se 2 (by rfl) ⟨4126929, by rfl⟩ : syracuseStep 11005145 = 8253859) B8253859
theorem B7336763 : Blo 1931435 7336763 := bstep (se 1 (by rfl) ⟨5502572, by rfl⟩ : syracuseStep 7336763 = 11005145) B11005145
theorem B4891175 : Blo 1931435 4891175 := bstep (se 1 (by rfl) ⟨3668381, by rfl⟩ : syracuseStep 4891175 = 7336763) B7336763
theorem B3260783 : Blo 1931435 3260783 := bstep (se 1 (by rfl) ⟨2445587, by rfl⟩ : syracuseStep 3260783 = 4891175) B4891175
theorem B2173855 : Blo 1931435 2173855 := bstep (se 1 (by rfl) ⟨1630391, by rfl⟩ : syracuseStep 2173855 = 3260783) B3260783
theorem B2898473 : Blo 1931435 2898473 := bstep (se 2 (by rfl) ⟨1086927, by rfl⟩ : syracuseStep 2898473 = 2173855) B2173855
theorem B1932315 : Blo 1931435 1932315 := bstep (se 1 (by rfl) ⟨1449236, by rfl⟩ : syracuseStep 1932315 = 2898473) B2898473
theorem B4642805 : Blo 1931435 4642805 := bbase (se 5 (by rfl) ⟨217631, by rfl⟩ : syracuseStep 4642805 = 435263) (by norm_num)
theorem B12380813 : Blo 1931435 12380813 := bstep (se 3 (by rfl) ⟨2321402, by rfl⟩ : syracuseStep 12380813 = 4642805) B4642805
theorem B8253875 : Blo 1931435 8253875 := bstep (se 1 (by rfl) ⟨6190406, by rfl⟩ : syracuseStep 8253875 = 12380813) B12380813
theorem B5502583 : Blo 1931435 5502583 := bstep (se 1 (by rfl) ⟨4126937, by rfl⟩ : syracuseStep 5502583 = 8253875) B8253875
theorem B7336777 : Blo 1931435 7336777 := bstep (se 2 (by rfl) ⟨2751291, by rfl⟩ : syracuseStep 7336777 = 5502583) B5502583
theorem B9782369 : Blo 1931435 9782369 := bstep (se 2 (by rfl) ⟨3668388, by rfl⟩ : syracuseStep 9782369 = 7336777) B7336777
theorem B6521579 : Blo 1931435 6521579 := bstep (se 1 (by rfl) ⟨4891184, by rfl⟩ : syracuseStep 6521579 = 9782369) B9782369
theorem B4347719 : Blo 1931435 4347719 := bstep (se 1 (by rfl) ⟨3260789, by rfl⟩ : syracuseStep 4347719 = 6521579) B6521579
theorem B2898479 : Blo 1931435 2898479 := bstep (se 1 (by rfl) ⟨2173859, by rfl⟩ : syracuseStep 2898479 = 4347719) B4347719
theorem B1932319 : Blo 1931435 1932319 := bstep (se 1 (by rfl) ⟨1449239, by rfl⟩ : syracuseStep 1932319 = 2898479) B2898479
theorem B2898485 : Blo 1931435 2898485 := bbase (se 5 (by rfl) ⟨135866, by rfl⟩ : syracuseStep 2898485 = 271733) (by norm_num)
theorem B1932323 : Blo 1931435 1932323 := bstep (se 1 (by rfl) ⟨1449242, by rfl⟩ : syracuseStep 1932323 = 2898485) B2898485
theorem B4891205 : Blo 1931435 4891205 := bbase (se 4 (by rfl) ⟨458550, by rfl⟩ : syracuseStep 4891205 = 917101) (by norm_num)
theorem B3260803 : Blo 1931435 3260803 := bstep (se 1 (by rfl) ⟨2445602, by rfl⟩ : syracuseStep 3260803 = 4891205) B4891205
theorem B4347737 : Blo 1931435 4347737 := bstep (se 2 (by rfl) ⟨1630401, by rfl⟩ : syracuseStep 4347737 = 3260803) B3260803
theorem B2898491 : Blo 1931435 2898491 := bstep (se 1 (by rfl) ⟨2173868, by rfl⟩ : syracuseStep 2898491 = 4347737) B4347737
theorem B1932327 : Blo 1931435 1932327 := bstep (se 1 (by rfl) ⟨1449245, by rfl⟩ : syracuseStep 1932327 = 2898491) B2898491
theorem B2173873 : Blo 1931435 2173873 := bbase (se 2 (by rfl) ⟨815202, by rfl⟩ : syracuseStep 2173873 = 1630405) (by norm_num)
theorem B2898497 : Blo 1931435 2898497 := bstep (se 2 (by rfl) ⟨1086936, by rfl⟩ : syracuseStep 2898497 = 2173873) B2173873
theorem B1932331 : Blo 1931435 1932331 := bstep (se 1 (by rfl) ⟨1449248, by rfl⟩ : syracuseStep 1932331 = 2898497) B2898497
theorem B5502629 : Blo 1931435 5502629 := bbase (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) (by norm_num)
theorem B3668419 : Blo 1931435 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B4891225 : Blo 1931435 4891225 := bstep (se 2 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 4891225 = 3668419) B3668419
theorem B6521633 : Blo 1931435 6521633 := bstep (se 2 (by rfl) ⟨2445612, by rfl⟩ : syracuseStep 6521633 = 4891225) B4891225
theorem B4347755 : Blo 1931435 4347755 := bstep (se 1 (by rfl) ⟨3260816, by rfl⟩ : syracuseStep 4347755 = 6521633) B6521633
theorem B2898503 : Blo 1931435 2898503 := bstep (se 1 (by rfl) ⟨2173877, by rfl⟩ : syracuseStep 2898503 = 4347755) B4347755
theorem B1932335 : Blo 1931435 1932335 := bstep (se 1 (by rfl) ⟨1449251, by rfl⟩ : syracuseStep 1932335 = 2898503) B2898503
theorem B2898509 : Blo 1931435 2898509 := bbase (se 3 (by rfl) ⟨543470, by rfl⟩ : syracuseStep 2898509 = 1086941) (by norm_num)
theorem B1932339 : Blo 1931435 1932339 := bstep (se 1 (by rfl) ⟨1449254, by rfl⟩ : syracuseStep 1932339 = 2898509) B2898509
theorem B4347773 : Blo 1931435 4347773 := bbase (se 3 (by rfl) ⟨815207, by rfl⟩ : syracuseStep 4347773 = 1630415) (by norm_num)
theorem B2898515 : Blo 1931435 2898515 := bstep (se 1 (by rfl) ⟨2173886, by rfl⟩ : syracuseStep 2898515 = 4347773) B4347773
theorem B1932343 : Blo 1931435 1932343 := bstep (se 1 (by rfl) ⟨1449257, by rfl⟩ : syracuseStep 1932343 = 2898515) B2898515
theorem B3260837 : Blo 1931435 3260837 := bbase (se 4 (by rfl) ⟨305703, by rfl⟩ : syracuseStep 3260837 = 611407) (by norm_num)
theorem B2173891 : Blo 1931435 2173891 := bstep (se 1 (by rfl) ⟨1630418, by rfl⟩ : syracuseStep 2173891 = 3260837) B3260837
theorem B2898521 : Blo 1931435 2898521 := bstep (se 2 (by rfl) ⟨1086945, by rfl⟩ : syracuseStep 2898521 = 2173891) B2173891
theorem B1932347 : Blo 1931435 1932347 := bstep (se 1 (by rfl) ⟨1449260, by rfl⟩ : syracuseStep 1932347 = 2898521) B2898521
theorem B6964325 : Blo 1931435 6964325 := bbase (se 4 (by rfl) ⟨652905, by rfl⟩ : syracuseStep 6964325 = 1305811) (by norm_num)
theorem B4642883 : Blo 1931435 4642883 := bstep (se 1 (by rfl) ⟨3482162, by rfl⟩ : syracuseStep 4642883 = 6964325) B6964325
theorem B3095255 : Blo 1931435 3095255 := bstep (se 1 (by rfl) ⟨2321441, by rfl⟩ : syracuseStep 3095255 = 4642883) B4642883
theorem B2063503 : Blo 1931435 2063503 := bstep (se 1 (by rfl) ⟨1547627, by rfl⟩ : syracuseStep 2063503 = 3095255) B3095255
theorem B2751337 : Blo 1931435 2751337 := bstep (se 2 (by rfl) ⟨1031751, by rfl⟩ : syracuseStep 2751337 = 2063503) B2063503
theorem B14673797 : Blo 1931435 14673797 := bstep (se 4 (by rfl) ⟨1375668, by rfl⟩ : syracuseStep 14673797 = 2751337) B2751337
theorem B9782531 : Blo 1931435 9782531 := bstep (se 1 (by rfl) ⟨7336898, by rfl⟩ : syracuseStep 9782531 = 14673797) B14673797
theorem B6521687 : Blo 1931435 6521687 := bstep (se 1 (by rfl) ⟨4891265, by rfl⟩ : syracuseStep 6521687 = 9782531) B9782531
theorem B4347791 : Blo 1931435 4347791 := bstep (se 1 (by rfl) ⟨3260843, by rfl⟩ : syracuseStep 4347791 = 6521687) B6521687
theorem B2898527 : Blo 1931435 2898527 := bstep (se 1 (by rfl) ⟨2173895, by rfl⟩ : syracuseStep 2898527 = 4347791) B4347791
theorem B1932351 : Blo 1931435 1932351 := bstep (se 1 (by rfl) ⟨1449263, by rfl⟩ : syracuseStep 1932351 = 2898527) B2898527
theorem B2898533 : Blo 1931435 2898533 := bbase (se 4 (by rfl) ⟨271737, by rfl⟩ : syracuseStep 2898533 = 543475) (by norm_num)
theorem B1932355 : Blo 1931435 1932355 := bstep (se 1 (by rfl) ⟨1449266, by rfl⟩ : syracuseStep 1932355 = 2898533) B2898533
theorem B2751349 : Blo 1931435 2751349 := bbase (se 5 (by rfl) ⟨128969, by rfl⟩ : syracuseStep 2751349 = 257939) (by norm_num)
theorem B3668465 : Blo 1931435 3668465 := bstep (se 2 (by rfl) ⟨1375674, by rfl⟩ : syracuseStep 3668465 = 2751349) B2751349
theorem B2445643 : Blo 1931435 2445643 := bstep (se 1 (by rfl) ⟨1834232, by rfl⟩ : syracuseStep 2445643 = 3668465) B3668465
theorem B3260857 : Blo 1931435 3260857 := bstep (se 2 (by rfl) ⟨1222821, by rfl⟩ : syracuseStep 3260857 = 2445643) B2445643
theorem B4347809 : Blo 1931435 4347809 := bstep (se 2 (by rfl) ⟨1630428, by rfl⟩ : syracuseStep 4347809 = 3260857) B3260857
theorem B2898539 : Blo 1931435 2898539 := bstep (se 1 (by rfl) ⟨2173904, by rfl⟩ : syracuseStep 2898539 = 4347809) B4347809
theorem B1932359 : Blo 1931435 1932359 := bstep (se 1 (by rfl) ⟨1449269, by rfl⟩ : syracuseStep 1932359 = 2898539) B2898539
theorem B2173909 : Blo 1931435 2173909 := bbase (se 7 (by rfl) ⟨25475, by rfl⟩ : syracuseStep 2173909 = 50951) (by norm_num)
theorem B2898545 : Blo 1931435 2898545 := bstep (se 2 (by rfl) ⟨1086954, by rfl⟩ : syracuseStep 2898545 = 2173909) B2173909
theorem B1932363 : Blo 1931435 1932363 := bstep (se 1 (by rfl) ⟨1449272, by rfl⟩ : syracuseStep 1932363 = 2898545) B2898545
theorem B2445653 : Blo 1931435 2445653 := bbase (se 10 (by rfl) ⟨3582, by rfl⟩ : syracuseStep 2445653 = 7165) (by norm_num)
theorem B6521741 : Blo 1931435 6521741 := bstep (se 3 (by rfl) ⟨1222826, by rfl⟩ : syracuseStep 6521741 = 2445653) B2445653
theorem B4347827 : Blo 1931435 4347827 := bstep (se 1 (by rfl) ⟨3260870, by rfl⟩ : syracuseStep 4347827 = 6521741) B6521741
theorem B2898551 : Blo 1931435 2898551 := bstep (se 1 (by rfl) ⟨2173913, by rfl⟩ : syracuseStep 2898551 = 4347827) B4347827
theorem B1932367 : Blo 1931435 1932367 := bstep (se 1 (by rfl) ⟨1449275, by rfl⟩ : syracuseStep 1932367 = 2898551) B2898551
theorem B2898557 : Blo 1931435 2898557 := bbase (se 3 (by rfl) ⟨543479, by rfl⟩ : syracuseStep 2898557 = 1086959) (by norm_num)
theorem B1932371 : Blo 1931435 1932371 := bstep (se 1 (by rfl) ⟨1449278, by rfl⟩ : syracuseStep 1932371 = 2898557) B2898557
theorem B4347845 : Blo 1931435 4347845 := bbase (se 4 (by rfl) ⟨407610, by rfl⟩ : syracuseStep 4347845 = 815221) (by norm_num)
theorem B2898563 : Blo 1931435 2898563 := bstep (se 1 (by rfl) ⟨2173922, by rfl⟩ : syracuseStep 2898563 = 4347845) B4347845
theorem B1932375 : Blo 1931435 1932375 := bstep (se 1 (by rfl) ⟨1449281, by rfl⟩ : syracuseStep 1932375 = 2898563) B2898563
theorem B8254133 : Blo 1931435 8254133 := bbase (se 5 (by rfl) ⟨386912, by rfl⟩ : syracuseStep 8254133 = 773825) (by norm_num)
theorem B5502755 : Blo 1931435 5502755 := bstep (se 1 (by rfl) ⟨4127066, by rfl⟩ : syracuseStep 5502755 = 8254133) B8254133
theorem B3668503 : Blo 1931435 3668503 := bstep (se 1 (by rfl) ⟨2751377, by rfl⟩ : syracuseStep 3668503 = 5502755) B5502755
theorem B4891337 : Blo 1931435 4891337 := bstep (se 2 (by rfl) ⟨1834251, by rfl⟩ : syracuseStep 4891337 = 3668503) B3668503
theorem B3260891 : Blo 1931435 3260891 := bstep (se 1 (by rfl) ⟨2445668, by rfl⟩ : syracuseStep 3260891 = 4891337) B4891337
theorem B2173927 : Blo 1931435 2173927 := bstep (se 1 (by rfl) ⟨1630445, by rfl⟩ : syracuseStep 2173927 = 3260891) B3260891
theorem B2898569 : Blo 1931435 2898569 := bstep (se 2 (by rfl) ⟨1086963, by rfl⟩ : syracuseStep 2898569 = 2173927) B2173927
theorem B1932379 : Blo 1931435 1932379 := bstep (se 1 (by rfl) ⟨1449284, by rfl⟩ : syracuseStep 1932379 = 2898569) B2898569
theorem B9782693 : Blo 1931435 9782693 := bbase (se 4 (by rfl) ⟨917127, by rfl⟩ : syracuseStep 9782693 = 1834255) (by norm_num)
theorem B6521795 : Blo 1931435 6521795 := bstep (se 1 (by rfl) ⟨4891346, by rfl⟩ : syracuseStep 6521795 = 9782693) B9782693
theorem B4347863 : Blo 1931435 4347863 := bstep (se 1 (by rfl) ⟨3260897, by rfl⟩ : syracuseStep 4347863 = 6521795) B6521795
theorem B2898575 : Blo 1931435 2898575 := bstep (se 1 (by rfl) ⟨2173931, by rfl⟩ : syracuseStep 2898575 = 4347863) B4347863
theorem B1932383 : Blo 1931435 1932383 := bstep (se 1 (by rfl) ⟨1449287, by rfl⟩ : syracuseStep 1932383 = 2898575) B2898575
theorem B2898581 : Blo 1931435 2898581 := bbase (se 6 (by rfl) ⟨67935, by rfl⟩ : syracuseStep 2898581 = 135871) (by norm_num)
theorem B1932387 : Blo 1931435 1932387 := bstep (se 1 (by rfl) ⟨1449290, by rfl⟩ : syracuseStep 1932387 = 2898581) B2898581
theorem B11912885 : Blo 1931435 11912885 := bbase (se 5 (by rfl) ⟨558416, by rfl⟩ : syracuseStep 11912885 = 1116833) (by norm_num)
theorem B7941923 : Blo 1931435 7941923 := bstep (se 1 (by rfl) ⟨5956442, by rfl⟩ : syracuseStep 7941923 = 11912885) B11912885
theorem B5294615 : Blo 1931435 5294615 := bstep (se 1 (by rfl) ⟨3970961, by rfl⟩ : syracuseStep 5294615 = 7941923) B7941923
theorem B56475893 : Blo 1931435 56475893 := bstep (se 5 (by rfl) ⟨2647307, by rfl⟩ : syracuseStep 56475893 = 5294615) B5294615
theorem B37650595 : Blo 1931435 37650595 := bstep (se 1 (by rfl) ⟨28237946, by rfl⟩ : syracuseStep 37650595 = 56475893) B56475893
theorem B50200793 : Blo 1931435 50200793 := bstep (se 2 (by rfl) ⟨18825297, by rfl⟩ : syracuseStep 50200793 = 37650595) B37650595
theorem B33467195 : Blo 1931435 33467195 := bstep (se 1 (by rfl) ⟨25100396, by rfl⟩ : syracuseStep 33467195 = 50200793) B50200793
theorem B22311463 : Blo 1931435 22311463 := bstep (se 1 (by rfl) ⟨16733597, by rfl⟩ : syracuseStep 22311463 = 33467195) B33467195
theorem B29748617 : Blo 1931435 29748617 := bstep (se 2 (by rfl) ⟨11155731, by rfl⟩ : syracuseStep 29748617 = 22311463) B22311463
theorem B19832411 : Blo 1931435 19832411 := bstep (se 1 (by rfl) ⟨14874308, by rfl⟩ : syracuseStep 19832411 = 29748617) B29748617
theorem B52886429 : Blo 1931435 52886429 := bstep (se 3 (by rfl) ⟨9916205, by rfl⟩ : syracuseStep 52886429 = 19832411) B19832411
theorem B35257619 : Blo 1931435 35257619 := bstep (se 1 (by rfl) ⟨26443214, by rfl⟩ : syracuseStep 35257619 = 52886429) B52886429
theorem B23505079 : Blo 1931435 23505079 := bstep (se 1 (by rfl) ⟨17628809, by rfl⟩ : syracuseStep 23505079 = 35257619) B35257619
theorem B31340105 : Blo 1931435 31340105 := bstep (se 2 (by rfl) ⟨11752539, by rfl⟩ : syracuseStep 31340105 = 23505079) B23505079
theorem B20893403 : Blo 1931435 20893403 := bstep (se 1 (by rfl) ⟨15670052, by rfl⟩ : syracuseStep 20893403 = 31340105) B31340105
theorem B13928935 : Blo 1931435 13928935 := bstep (se 1 (by rfl) ⟨10446701, by rfl⟩ : syracuseStep 13928935 = 20893403) B20893403
theorem B18571913 : Blo 1931435 18571913 := bstep (se 2 (by rfl) ⟨6964467, by rfl⟩ : syracuseStep 18571913 = 13928935) B13928935
theorem B12381275 : Blo 1931435 12381275 := bstep (se 1 (by rfl) ⟨9285956, by rfl⟩ : syracuseStep 12381275 = 18571913) B18571913
theorem B8254183 : Blo 1931435 8254183 := bstep (se 1 (by rfl) ⟨6190637, by rfl⟩ : syracuseStep 8254183 = 12381275) B12381275
theorem B11005577 : Blo 1931435 11005577 := bstep (se 2 (by rfl) ⟨4127091, by rfl⟩ : syracuseStep 11005577 = 8254183) B8254183
theorem B7337051 : Blo 1931435 7337051 := bstep (se 1 (by rfl) ⟨5502788, by rfl⟩ : syracuseStep 7337051 = 11005577) B11005577
theorem B4891367 : Blo 1931435 4891367 := bstep (se 1 (by rfl) ⟨3668525, by rfl⟩ : syracuseStep 4891367 = 7337051) B7337051
theorem B3260911 : Blo 1931435 3260911 := bstep (se 1 (by rfl) ⟨2445683, by rfl⟩ : syracuseStep 3260911 = 4891367) B4891367
theorem B4347881 : Blo 1931435 4347881 := bstep (se 2 (by rfl) ⟨1630455, by rfl⟩ : syracuseStep 4347881 = 3260911) B3260911
theorem B2898587 : Blo 1931435 2898587 := bstep (se 1 (by rfl) ⟨2173940, by rfl⟩ : syracuseStep 2898587 = 4347881) B4347881
theorem B1932391 : Blo 1931435 1932391 := bstep (se 1 (by rfl) ⟨1449293, by rfl⟩ : syracuseStep 1932391 = 2898587) B2898587
theorem B2173945 : Blo 1931435 2173945 := bbase (se 2 (by rfl) ⟨815229, by rfl⟩ : syracuseStep 2173945 = 1630459) (by norm_num)
theorem B2898593 : Blo 1931435 2898593 := bstep (se 2 (by rfl) ⟨1086972, by rfl⟩ : syracuseStep 2898593 = 2173945) B2173945
theorem B1932395 : Blo 1931435 1932395 := bstep (se 1 (by rfl) ⟨1449296, by rfl⟩ : syracuseStep 1932395 = 2898593) B2898593
theorem B4407221 : Blo 1931435 4407221 := bbase (se 5 (by rfl) ⟨206588, by rfl⟩ : syracuseStep 4407221 = 413177) (by norm_num)
theorem B11752589 : Blo 1931435 11752589 := bstep (se 3 (by rfl) ⟨2203610, by rfl⟩ : syracuseStep 11752589 = 4407221) B4407221
theorem B7835059 : Blo 1931435 7835059 := bstep (se 1 (by rfl) ⟨5876294, by rfl⟩ : syracuseStep 7835059 = 11752589) B11752589
theorem B10446745 : Blo 1931435 10446745 := bstep (se 2 (by rfl) ⟨3917529, by rfl⟩ : syracuseStep 10446745 = 7835059) B7835059
theorem B13928993 : Blo 1931435 13928993 := bstep (se 2 (by rfl) ⟨5223372, by rfl⟩ : syracuseStep 13928993 = 10446745) B10446745
theorem B9285995 : Blo 1931435 9285995 := bstep (se 1 (by rfl) ⟨6964496, by rfl⟩ : syracuseStep 9285995 = 13928993) B13928993
theorem B6190663 : Blo 1931435 6190663 := bstep (se 1 (by rfl) ⟨4642997, by rfl⟩ : syracuseStep 6190663 = 9285995) B9285995
theorem B8254217 : Blo 1931435 8254217 := bstep (se 2 (by rfl) ⟨3095331, by rfl⟩ : syracuseStep 8254217 = 6190663) B6190663
theorem B5502811 : Blo 1931435 5502811 := bstep (se 1 (by rfl) ⟨4127108, by rfl⟩ : syracuseStep 5502811 = 8254217) B8254217
theorem B7337081 : Blo 1931435 7337081 := bstep (se 2 (by rfl) ⟨2751405, by rfl⟩ : syracuseStep 7337081 = 5502811) B5502811
theorem B4891387 : Blo 1931435 4891387 := bstep (se 1 (by rfl) ⟨3668540, by rfl⟩ : syracuseStep 4891387 = 7337081) B7337081
theorem B6521849 : Blo 1931435 6521849 := bstep (se 2 (by rfl) ⟨2445693, by rfl⟩ : syracuseStep 6521849 = 4891387) B4891387
theorem B4347899 : Blo 1931435 4347899 := bstep (se 1 (by rfl) ⟨3260924, by rfl⟩ : syracuseStep 4347899 = 6521849) B6521849
theorem B2898599 : Blo 1931435 2898599 := bstep (se 1 (by rfl) ⟨2173949, by rfl⟩ : syracuseStep 2898599 = 4347899) B4347899
theorem B1932399 : Blo 1931435 1932399 := bstep (se 1 (by rfl) ⟨1449299, by rfl⟩ : syracuseStep 1932399 = 2898599) B2898599
theorem B2898605 : Blo 1931435 2898605 := bbase (se 3 (by rfl) ⟨543488, by rfl⟩ : syracuseStep 2898605 = 1086977) (by norm_num)
theorem B1932403 : Blo 1931435 1932403 := bstep (se 1 (by rfl) ⟨1449302, by rfl⟩ : syracuseStep 1932403 = 2898605) B2898605
theorem B4347917 : Blo 1931435 4347917 := bbase (se 3 (by rfl) ⟨815234, by rfl⟩ : syracuseStep 4347917 = 1630469) (by norm_num)
theorem B2898611 : Blo 1931435 2898611 := bstep (se 1 (by rfl) ⟨2173958, by rfl⟩ : syracuseStep 2898611 = 4347917) B4347917
theorem B1932407 : Blo 1931435 1932407 := bstep (se 1 (by rfl) ⟨1449305, by rfl⟩ : syracuseStep 1932407 = 2898611) B2898611
theorem B2445709 : Blo 1931435 2445709 := bbase (se 3 (by rfl) ⟨458570, by rfl⟩ : syracuseStep 2445709 = 917141) (by norm_num)
theorem B3260945 : Blo 1931435 3260945 := bstep (se 2 (by rfl) ⟨1222854, by rfl⟩ : syracuseStep 3260945 = 2445709) B2445709
theorem B2173963 : Blo 1931435 2173963 := bstep (se 1 (by rfl) ⟨1630472, by rfl⟩ : syracuseStep 2173963 = 3260945) B3260945
theorem B2898617 : Blo 1931435 2898617 := bstep (se 2 (by rfl) ⟨1086981, by rfl⟩ : syracuseStep 2898617 = 2173963) B2173963
theorem B1932411 : Blo 1931435 1932411 := bstep (se 1 (by rfl) ⟨1449308, by rfl⟩ : syracuseStep 1932411 = 2898617) B2898617
theorem B4958165 : Blo 1931435 4958165 := bbase (se 7 (by rfl) ⟨58103, by rfl⟩ : syracuseStep 4958165 = 116207) (by norm_num)
theorem B3305443 : Blo 1931435 3305443 := bstep (se 1 (by rfl) ⟨2479082, by rfl⟩ : syracuseStep 3305443 = 4958165) B4958165
theorem B4407257 : Blo 1931435 4407257 := bstep (se 2 (by rfl) ⟨1652721, by rfl⟩ : syracuseStep 4407257 = 3305443) B3305443
theorem B11752685 : Blo 1931435 11752685 := bstep (se 3 (by rfl) ⟨2203628, by rfl⟩ : syracuseStep 11752685 = 4407257) B4407257
theorem B7835123 : Blo 1931435 7835123 := bstep (se 1 (by rfl) ⟨5876342, by rfl⟩ : syracuseStep 7835123 = 11752685) B11752685
theorem B5223415 : Blo 1931435 5223415 := bstep (se 1 (by rfl) ⟨3917561, by rfl⟩ : syracuseStep 5223415 = 7835123) B7835123
theorem B6964553 : Blo 1931435 6964553 := bstep (se 2 (by rfl) ⟨2611707, by rfl⟩ : syracuseStep 6964553 = 5223415) B5223415
theorem B18572141 : Blo 1931435 18572141 := bstep (se 3 (by rfl) ⟨3482276, by rfl⟩ : syracuseStep 18572141 = 6964553) B6964553
theorem B12381427 : Blo 1931435 12381427 := bstep (se 1 (by rfl) ⟨9286070, by rfl⟩ : syracuseStep 12381427 = 18572141) B18572141
theorem B16508569 : Blo 1931435 16508569 := bstep (se 2 (by rfl) ⟨6190713, by rfl⟩ : syracuseStep 16508569 = 12381427) B12381427
theorem B22011425 : Blo 1931435 22011425 := bstep (se 2 (by rfl) ⟨8254284, by rfl⟩ : syracuseStep 22011425 = 16508569) B16508569
theorem B14674283 : Blo 1931435 14674283 := bstep (se 1 (by rfl) ⟨11005712, by rfl⟩ : syracuseStep 14674283 = 22011425) B22011425
theorem B9782855 : Blo 1931435 9782855 := bstep (se 1 (by rfl) ⟨7337141, by rfl⟩ : syracuseStep 9782855 = 14674283) B14674283
theorem B6521903 : Blo 1931435 6521903 := bstep (se 1 (by rfl) ⟨4891427, by rfl⟩ : syracuseStep 6521903 = 9782855) B9782855
theorem B4347935 : Blo 1931435 4347935 := bstep (se 1 (by rfl) ⟨3260951, by rfl⟩ : syracuseStep 4347935 = 6521903) B6521903
theorem B2898623 : Blo 1931435 2898623 := bstep (se 1 (by rfl) ⟨2173967, by rfl⟩ : syracuseStep 2898623 = 4347935) B4347935
theorem B1932415 : Blo 1931435 1932415 := bstep (se 1 (by rfl) ⟨1449311, by rfl⟩ : syracuseStep 1932415 = 2898623) B2898623
theorem B2898629 : Blo 1931435 2898629 := bbase (se 4 (by rfl) ⟨271746, by rfl⟩ : syracuseStep 2898629 = 543493) (by norm_num)
theorem B1932419 : Blo 1931435 1932419 := bstep (se 1 (by rfl) ⟨1449314, by rfl⟩ : syracuseStep 1932419 = 2898629) B2898629
theorem B3260965 : Blo 1931435 3260965 := bbase (se 4 (by rfl) ⟨305715, by rfl⟩ : syracuseStep 3260965 = 611431) (by norm_num)
theorem B4347953 : Blo 1931435 4347953 := bstep (se 2 (by rfl) ⟨1630482, by rfl⟩ : syracuseStep 4347953 = 3260965) B3260965
theorem B2898635 : Blo 1931435 2898635 := bstep (se 1 (by rfl) ⟨2173976, by rfl⟩ : syracuseStep 2898635 = 4347953) B4347953
theorem B1932423 : Blo 1931435 1932423 := bstep (se 1 (by rfl) ⟨1449317, by rfl⟩ : syracuseStep 1932423 = 2898635) B2898635
theorem B2173981 : Blo 1931435 2173981 := bbase (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) (by norm_num)
theorem B2898641 : Blo 1931435 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1932427 : Blo 1931435 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B6521957 : Blo 1931435 6521957 := bbase (se 4 (by rfl) ⟨611433, by rfl⟩ : syracuseStep 6521957 = 1222867) (by norm_num)
theorem B4347971 : Blo 1931435 4347971 := bstep (se 1 (by rfl) ⟨3260978, by rfl⟩ : syracuseStep 4347971 = 6521957) B6521957
theorem B2898647 : Blo 1931435 2898647 := bstep (se 1 (by rfl) ⟨2173985, by rfl⟩ : syracuseStep 2898647 = 4347971) B4347971
theorem B1932431 : Blo 1931435 1932431 := bstep (se 1 (by rfl) ⟨1449323, by rfl⟩ : syracuseStep 1932431 = 2898647) B2898647
theorem B2898653 : Blo 1931435 2898653 := bbase (se 3 (by rfl) ⟨543497, by rfl⟩ : syracuseStep 2898653 = 1086995) (by norm_num)
theorem B1932435 : Blo 1931435 1932435 := bstep (se 1 (by rfl) ⟨1449326, by rfl⟩ : syracuseStep 1932435 = 2898653) B2898653
theorem B4347989 : Blo 1931435 4347989 := bbase (se 8 (by rfl) ⟨25476, by rfl⟩ : syracuseStep 4347989 = 50953) (by norm_num)
theorem B2898659 : Blo 1931435 2898659 := bstep (se 1 (by rfl) ⟨2173994, by rfl⟩ : syracuseStep 2898659 = 4347989) B4347989
theorem B1932439 : Blo 1931435 1932439 := bstep (se 1 (by rfl) ⟨1449329, by rfl⟩ : syracuseStep 1932439 = 2898659) B2898659
theorem B6190805 : Blo 1931435 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B4127203 : Blo 1931435 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B5502937 : Blo 1931435 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B7337249 : Blo 1931435 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B4891499 : Blo 1931435 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B3260999 : Blo 1931435 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B2173999 : Blo 1931435 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B2898665 : Blo 1931435 2898665 := bstep (se 2 (by rfl) ⟨1086999, by rfl⟩ : syracuseStep 2898665 = 2173999) B2173999
theorem B1932443 : Blo 1931435 1932443 := bstep (se 1 (by rfl) ⟨1449332, by rfl⟩ : syracuseStep 1932443 = 2898665) B2898665
theorem B4706461 : Blo 1931435 4706461 := bbase (se 3 (by rfl) ⟨882461, by rfl⟩ : syracuseStep 4706461 = 1764923) (by norm_num)
theorem B6275281 : Blo 1931435 6275281 := bstep (se 2 (by rfl) ⟨2353230, by rfl⟩ : syracuseStep 6275281 = 4706461) B4706461
theorem B8367041 : Blo 1931435 8367041 := bstep (se 2 (by rfl) ⟨3137640, by rfl⟩ : syracuseStep 8367041 = 6275281) B6275281
theorem B5578027 : Blo 1931435 5578027 := bstep (se 1 (by rfl) ⟨4183520, by rfl⟩ : syracuseStep 5578027 = 8367041) B8367041
theorem B29749477 : Blo 1931435 29749477 := bstep (se 4 (by rfl) ⟨2789013, by rfl⟩ : syracuseStep 29749477 = 5578027) B5578027
theorem B39665969 : Blo 1931435 39665969 := bstep (se 2 (by rfl) ⟨14874738, by rfl⟩ : syracuseStep 39665969 = 29749477) B29749477
theorem B26443979 : Blo 1931435 26443979 := bstep (se 1 (by rfl) ⟨19832984, by rfl⟩ : syracuseStep 26443979 = 39665969) B39665969
theorem B17629319 : Blo 1931435 17629319 := bstep (se 1 (by rfl) ⟨13221989, by rfl⟩ : syracuseStep 17629319 = 26443979) B26443979
theorem B11752879 : Blo 1931435 11752879 := bstep (se 1 (by rfl) ⟨8814659, by rfl⟩ : syracuseStep 11752879 = 17629319) B17629319
theorem B15670505 : Blo 1931435 15670505 := bstep (se 2 (by rfl) ⟨5876439, by rfl⟩ : syracuseStep 15670505 = 11752879) B11752879
theorem B10447003 : Blo 1931435 10447003 := bstep (se 1 (by rfl) ⟨7835252, by rfl⟩ : syracuseStep 10447003 = 15670505) B15670505
theorem B13929337 : Blo 1931435 13929337 := bstep (se 2 (by rfl) ⟨5223501, by rfl⟩ : syracuseStep 13929337 = 10447003) B10447003
theorem B18572449 : Blo 1931435 18572449 := bstep (se 2 (by rfl) ⟨6964668, by rfl⟩ : syracuseStep 18572449 = 13929337) B13929337
theorem B24763265 : Blo 1931435 24763265 := bstep (se 2 (by rfl) ⟨9286224, by rfl⟩ : syracuseStep 24763265 = 18572449) B18572449
theorem B16508843 : Blo 1931435 16508843 := bstep (se 1 (by rfl) ⟨12381632, by rfl⟩ : syracuseStep 16508843 = 24763265) B24763265
theorem B11005895 : Blo 1931435 11005895 := bstep (se 1 (by rfl) ⟨8254421, by rfl⟩ : syracuseStep 11005895 = 16508843) B16508843
theorem B7337263 : Blo 1931435 7337263 := bstep (se 1 (by rfl) ⟨5502947, by rfl⟩ : syracuseStep 7337263 = 11005895) B11005895
theorem B9783017 : Blo 1931435 9783017 := bstep (se 2 (by rfl) ⟨3668631, by rfl⟩ : syracuseStep 9783017 = 7337263) B7337263
theorem B6522011 : Blo 1931435 6522011 := bstep (se 1 (by rfl) ⟨4891508, by rfl⟩ : syracuseStep 6522011 = 9783017) B9783017
theorem B4348007 : Blo 1931435 4348007 := bstep (se 1 (by rfl) ⟨3261005, by rfl⟩ : syracuseStep 4348007 = 6522011) B6522011
theorem B2898671 : Blo 1931435 2898671 := bstep (se 1 (by rfl) ⟨2174003, by rfl⟩ : syracuseStep 2898671 = 4348007) B4348007
theorem B1932447 : Blo 1931435 1932447 := bstep (se 1 (by rfl) ⟨1449335, by rfl⟩ : syracuseStep 1932447 = 2898671) B2898671
theorem B2898677 : Blo 1931435 2898677 := bbase (se 5 (by rfl) ⟨135875, by rfl⟩ : syracuseStep 2898677 = 271751) (by norm_num)
theorem B1932451 : Blo 1931435 1932451 := bstep (se 1 (by rfl) ⟨1449338, by rfl⟩ : syracuseStep 1932451 = 2898677) B2898677
theorem B17629397 : Blo 1931435 17629397 := bbase (se 7 (by rfl) ⟨206594, by rfl⟩ : syracuseStep 17629397 = 413189) (by norm_num)
theorem B11752931 : Blo 1931435 11752931 := bstep (se 1 (by rfl) ⟨8814698, by rfl⟩ : syracuseStep 11752931 = 17629397) B17629397
theorem B7835287 : Blo 1931435 7835287 := bstep (se 1 (by rfl) ⟨5876465, by rfl⟩ : syracuseStep 7835287 = 11752931) B11752931
theorem B10447049 : Blo 1931435 10447049 := bstep (se 2 (by rfl) ⟨3917643, by rfl⟩ : syracuseStep 10447049 = 7835287) B7835287
theorem B6964699 : Blo 1931435 6964699 := bstep (se 1 (by rfl) ⟨5223524, by rfl⟩ : syracuseStep 6964699 = 10447049) B10447049
theorem B9286265 : Blo 1931435 9286265 := bstep (se 2 (by rfl) ⟨3482349, by rfl⟩ : syracuseStep 9286265 = 6964699) B6964699
theorem B6190843 : Blo 1931435 6190843 := bstep (se 1 (by rfl) ⟨4643132, by rfl⟩ : syracuseStep 6190843 = 9286265) B9286265
theorem B8254457 : Blo 1931435 8254457 := bstep (se 2 (by rfl) ⟨3095421, by rfl⟩ : syracuseStep 8254457 = 6190843) B6190843
theorem B5502971 : Blo 1931435 5502971 := bstep (se 1 (by rfl) ⟨4127228, by rfl⟩ : syracuseStep 5502971 = 8254457) B8254457
theorem B3668647 : Blo 1931435 3668647 := bstep (se 1 (by rfl) ⟨2751485, by rfl⟩ : syracuseStep 3668647 = 5502971) B5502971
theorem B4891529 : Blo 1931435 4891529 := bstep (se 2 (by rfl) ⟨1834323, by rfl⟩ : syracuseStep 4891529 = 3668647) B3668647
theorem B3261019 : Blo 1931435 3261019 := bstep (se 1 (by rfl) ⟨2445764, by rfl⟩ : syracuseStep 3261019 = 4891529) B4891529
theorem B4348025 : Blo 1931435 4348025 := bstep (se 2 (by rfl) ⟨1630509, by rfl⟩ : syracuseStep 4348025 = 3261019) B3261019
theorem B2898683 : Blo 1931435 2898683 := bstep (se 1 (by rfl) ⟨2174012, by rfl⟩ : syracuseStep 2898683 = 4348025) B4348025
theorem B1932455 : Blo 1931435 1932455 := bstep (se 1 (by rfl) ⟨1449341, by rfl⟩ : syracuseStep 1932455 = 2898683) B2898683
theorem B2174017 : Blo 1931435 2174017 := bbase (se 2 (by rfl) ⟨815256, by rfl⟩ : syracuseStep 2174017 = 1630513) (by norm_num)
theorem B2898689 : Blo 1931435 2898689 := bstep (se 2 (by rfl) ⟨1087008, by rfl⟩ : syracuseStep 2898689 = 2174017) B2174017
theorem B1932459 : Blo 1931435 1932459 := bstep (se 1 (by rfl) ⟨1449344, by rfl⟩ : syracuseStep 1932459 = 2898689) B2898689
theorem B4891549 : Blo 1931435 4891549 := bbase (se 3 (by rfl) ⟨917165, by rfl⟩ : syracuseStep 4891549 = 1834331) (by norm_num)
theorem B6522065 : Blo 1931435 6522065 := bstep (se 2 (by rfl) ⟨2445774, by rfl⟩ : syracuseStep 6522065 = 4891549) B4891549
theorem B4348043 : Blo 1931435 4348043 := bstep (se 1 (by rfl) ⟨3261032, by rfl⟩ : syracuseStep 4348043 = 6522065) B6522065
theorem B2898695 : Blo 1931435 2898695 := bstep (se 1 (by rfl) ⟨2174021, by rfl⟩ : syracuseStep 2898695 = 4348043) B4348043
theorem B1932463 : Blo 1931435 1932463 := bstep (se 1 (by rfl) ⟨1449347, by rfl⟩ : syracuseStep 1932463 = 2898695) B2898695
theorem B2898701 : Blo 1931435 2898701 := bbase (se 3 (by rfl) ⟨543506, by rfl⟩ : syracuseStep 2898701 = 1087013) (by norm_num)
theorem B1932467 : Blo 1931435 1932467 := bstep (se 1 (by rfl) ⟨1449350, by rfl⟩ : syracuseStep 1932467 = 2898701) B2898701
theorem B4348061 : Blo 1931435 4348061 := bbase (se 3 (by rfl) ⟨815261, by rfl⟩ : syracuseStep 4348061 = 1630523) (by norm_num)
theorem B2898707 : Blo 1931435 2898707 := bstep (se 1 (by rfl) ⟨2174030, by rfl⟩ : syracuseStep 2898707 = 4348061) B4348061
theorem B1932471 : Blo 1931435 1932471 := bstep (se 1 (by rfl) ⟨1449353, by rfl⟩ : syracuseStep 1932471 = 2898707) B2898707
theorem B3261053 : Blo 1931435 3261053 := bbase (se 3 (by rfl) ⟨611447, by rfl⟩ : syracuseStep 3261053 = 1222895) (by norm_num)
theorem B2174035 : Blo 1931435 2174035 := bstep (se 1 (by rfl) ⟨1630526, by rfl⟩ : syracuseStep 2174035 = 3261053) B3261053
theorem B2898713 : Blo 1931435 2898713 := bstep (se 2 (by rfl) ⟨1087017, by rfl⟩ : syracuseStep 2898713 = 2174035) B2174035
theorem B1932475 : Blo 1931435 1932475 := bstep (se 1 (by rfl) ⟨1449356, by rfl⟩ : syracuseStep 1932475 = 2898713) B2898713
theorem B10589717 : Blo 1931435 10589717 := bbase (se 6 (by rfl) ⟨248196, by rfl⟩ : syracuseStep 10589717 = 496393) (by norm_num)
theorem B7059811 : Blo 1931435 7059811 := bstep (se 1 (by rfl) ⟨5294858, by rfl⟩ : syracuseStep 7059811 = 10589717) B10589717
theorem B9413081 : Blo 1931435 9413081 := bstep (se 2 (by rfl) ⟨3529905, by rfl⟩ : syracuseStep 9413081 = 7059811) B7059811
theorem B6275387 : Blo 1931435 6275387 := bstep (se 1 (by rfl) ⟨4706540, by rfl⟩ : syracuseStep 6275387 = 9413081) B9413081
theorem B4183591 : Blo 1931435 4183591 := bstep (se 1 (by rfl) ⟨3137693, by rfl⟩ : syracuseStep 4183591 = 6275387) B6275387
theorem B5578121 : Blo 1931435 5578121 := bstep (se 2 (by rfl) ⟨2091795, by rfl⟩ : syracuseStep 5578121 = 4183591) B4183591
theorem B3718747 : Blo 1931435 3718747 := bstep (se 1 (by rfl) ⟨2789060, by rfl⟩ : syracuseStep 3718747 = 5578121) B5578121
theorem B4958329 : Blo 1931435 4958329 := bstep (se 2 (by rfl) ⟨1859373, by rfl⟩ : syracuseStep 4958329 = 3718747) B3718747
theorem B6611105 : Blo 1931435 6611105 := bstep (se 2 (by rfl) ⟨2479164, by rfl⟩ : syracuseStep 6611105 = 4958329) B4958329
theorem B17629613 : Blo 1931435 17629613 := bstep (se 3 (by rfl) ⟨3305552, by rfl⟩ : syracuseStep 17629613 = 6611105) B6611105
theorem B11753075 : Blo 1931435 11753075 := bstep (se 1 (by rfl) ⟨8814806, by rfl⟩ : syracuseStep 11753075 = 17629613) B17629613
theorem B7835383 : Blo 1931435 7835383 := bstep (se 1 (by rfl) ⟨5876537, by rfl⟩ : syracuseStep 7835383 = 11753075) B11753075
theorem B10447177 : Blo 1931435 10447177 := bstep (se 2 (by rfl) ⟨3917691, by rfl⟩ : syracuseStep 10447177 = 7835383) B7835383
theorem B13929569 : Blo 1931435 13929569 := bstep (se 2 (by rfl) ⟨5223588, by rfl⟩ : syracuseStep 13929569 = 10447177) B10447177
theorem B9286379 : Blo 1931435 9286379 := bstep (se 1 (by rfl) ⟨6964784, by rfl⟩ : syracuseStep 9286379 = 13929569) B13929569
theorem B6190919 : Blo 1931435 6190919 := bstep (se 1 (by rfl) ⟨4643189, by rfl⟩ : syracuseStep 6190919 = 9286379) B9286379
theorem B4127279 : Blo 1931435 4127279 := bstep (se 1 (by rfl) ⟨3095459, by rfl⟩ : syracuseStep 4127279 = 6190919) B6190919
theorem B11006077 : Blo 1931435 11006077 := bstep (se 3 (by rfl) ⟨2063639, by rfl⟩ : syracuseStep 11006077 = 4127279) B4127279
theorem B14674769 : Blo 1931435 14674769 := bstep (se 2 (by rfl) ⟨5503038, by rfl⟩ : syracuseStep 14674769 = 11006077) B11006077
theorem B9783179 : Blo 1931435 9783179 := bstep (se 1 (by rfl) ⟨7337384, by rfl⟩ : syracuseStep 9783179 = 14674769) B14674769
theorem B6522119 : Blo 1931435 6522119 := bstep (se 1 (by rfl) ⟨4891589, by rfl⟩ : syracuseStep 6522119 = 9783179) B9783179
theorem B4348079 : Blo 1931435 4348079 := bstep (se 1 (by rfl) ⟨3261059, by rfl⟩ : syracuseStep 4348079 = 6522119) B6522119
theorem B2898719 : Blo 1931435 2898719 := bstep (se 1 (by rfl) ⟨2174039, by rfl⟩ : syracuseStep 2898719 = 4348079) B4348079
theorem B1932479 : Blo 1931435 1932479 := bstep (se 1 (by rfl) ⟨1449359, by rfl⟩ : syracuseStep 1932479 = 2898719) B2898719
theorem B2898725 : Blo 1931435 2898725 := bbase (se 4 (by rfl) ⟨271755, by rfl⟩ : syracuseStep 2898725 = 543511) (by norm_num)
theorem B1932483 : Blo 1931435 1932483 := bstep (se 1 (by rfl) ⟨1449362, by rfl⟩ : syracuseStep 1932483 = 2898725) B2898725
theorem B2445805 : Blo 1931435 2445805 := bbase (se 3 (by rfl) ⟨458588, by rfl⟩ : syracuseStep 2445805 = 917177) (by norm_num)
theorem B3261073 : Blo 1931435 3261073 := bstep (se 2 (by rfl) ⟨1222902, by rfl⟩ : syracuseStep 3261073 = 2445805) B2445805
theorem B4348097 : Blo 1931435 4348097 := bstep (se 2 (by rfl) ⟨1630536, by rfl⟩ : syracuseStep 4348097 = 3261073) B3261073
theorem B2898731 : Blo 1931435 2898731 := bstep (se 1 (by rfl) ⟨2174048, by rfl⟩ : syracuseStep 2898731 = 4348097) B4348097
theorem B1932487 : Blo 1931435 1932487 := bstep (se 1 (by rfl) ⟨1449365, by rfl⟩ : syracuseStep 1932487 = 2898731) B2898731
theorem B2174053 : Blo 1931435 2174053 := bbase (se 4 (by rfl) ⟨203817, by rfl⟩ : syracuseStep 2174053 = 407635) (by norm_num)
theorem B2898737 : Blo 1931435 2898737 := bstep (se 2 (by rfl) ⟨1087026, by rfl⟩ : syracuseStep 2898737 = 2174053) B2174053
theorem B1932491 : Blo 1931435 1932491 := bstep (se 1 (by rfl) ⟨1449368, by rfl⟩ : syracuseStep 1932491 = 2898737) B2898737
theorem B2063657 : Blo 1931435 2063657 := bbase (se 2 (by rfl) ⟨773871, by rfl⟩ : syracuseStep 2063657 = 1547743) (by norm_num)
theorem B5503085 : Blo 1931435 5503085 := bstep (se 3 (by rfl) ⟨1031828, by rfl⟩ : syracuseStep 5503085 = 2063657) B2063657
theorem B3668723 : Blo 1931435 3668723 := bstep (se 1 (by rfl) ⟨2751542, by rfl⟩ : syracuseStep 3668723 = 5503085) B5503085
theorem B2445815 : Blo 1931435 2445815 := bstep (se 1 (by rfl) ⟨1834361, by rfl⟩ : syracuseStep 2445815 = 3668723) B3668723
theorem B6522173 : Blo 1931435 6522173 := bstep (se 3 (by rfl) ⟨1222907, by rfl⟩ : syracuseStep 6522173 = 2445815) B2445815
theorem B4348115 : Blo 1931435 4348115 := bstep (se 1 (by rfl) ⟨3261086, by rfl⟩ : syracuseStep 4348115 = 6522173) B6522173
theorem B2898743 : Blo 1931435 2898743 := bstep (se 1 (by rfl) ⟨2174057, by rfl⟩ : syracuseStep 2898743 = 4348115) B4348115
theorem B1932495 : Blo 1931435 1932495 := bstep (se 1 (by rfl) ⟨1449371, by rfl⟩ : syracuseStep 1932495 = 2898743) B2898743
theorem B2898749 : Blo 1931435 2898749 := bbase (se 3 (by rfl) ⟨543515, by rfl⟩ : syracuseStep 2898749 = 1087031) (by norm_num)
theorem B1932499 : Blo 1931435 1932499 := bstep (se 1 (by rfl) ⟨1449374, by rfl⟩ : syracuseStep 1932499 = 2898749) B2898749
theorem B4348133 : Blo 1931435 4348133 := bbase (se 4 (by rfl) ⟨407637, by rfl⟩ : syracuseStep 4348133 = 815275) (by norm_num)
theorem B2898755 : Blo 1931435 2898755 := bstep (se 1 (by rfl) ⟨2174066, by rfl⟩ : syracuseStep 2898755 = 4348133) B4348133
theorem B1932503 : Blo 1931435 1932503 := bstep (se 1 (by rfl) ⟨1449377, by rfl⟩ : syracuseStep 1932503 = 2898755) B2898755
theorem B4891661 : Blo 1931435 4891661 := bbase (se 3 (by rfl) ⟨917186, by rfl⟩ : syracuseStep 4891661 = 1834373) (by norm_num)
theorem B3261107 : Blo 1931435 3261107 := bstep (se 1 (by rfl) ⟨2445830, by rfl⟩ : syracuseStep 3261107 = 4891661) B4891661
theorem B2174071 : Blo 1931435 2174071 := bstep (se 1 (by rfl) ⟨1630553, by rfl⟩ : syracuseStep 2174071 = 3261107) B3261107
theorem B2898761 : Blo 1931435 2898761 := bstep (se 2 (by rfl) ⟨1087035, by rfl⟩ : syracuseStep 2898761 = 2174071) B2174071
theorem B1932507 : Blo 1931435 1932507 := bstep (se 1 (by rfl) ⟨1449380, by rfl⟩ : syracuseStep 1932507 = 2898761) B2898761
theorem B2751565 : Blo 1931435 2751565 := bbase (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) (by norm_num)
theorem B3668753 : Blo 1931435 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B9783341 : Blo 1931435 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B6522227 : Blo 1931435 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B4348151 : Blo 1931435 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B2898767 : Blo 1931435 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B1932511 : Blo 1931435 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B2898773 : Blo 1931435 2898773 := bbase (se 9 (by rfl) ⟨8492, by rfl⟩ : syracuseStep 2898773 = 16985) (by norm_num)
theorem B1932515 : Blo 1931435 1932515 := bstep (se 1 (by rfl) ⟨1449386, by rfl⟩ : syracuseStep 1932515 = 2898773) B2898773
theorem B4127365 : Blo 1931435 4127365 := bbase (se 4 (by rfl) ⟨386940, by rfl⟩ : syracuseStep 4127365 = 773881) (by norm_num)
theorem B5503153 : Blo 1931435 5503153 := bstep (se 2 (by rfl) ⟨2063682, by rfl⟩ : syracuseStep 5503153 = 4127365) B4127365
theorem B7337537 : Blo 1931435 7337537 := bstep (se 2 (by rfl) ⟨2751576, by rfl⟩ : syracuseStep 7337537 = 5503153) B5503153
theorem B4891691 : Blo 1931435 4891691 := bstep (se 1 (by rfl) ⟨3668768, by rfl⟩ : syracuseStep 4891691 = 7337537) B7337537
theorem B3261127 : Blo 1931435 3261127 := bstep (se 1 (by rfl) ⟨2445845, by rfl⟩ : syracuseStep 3261127 = 4891691) B4891691
theorem B4348169 : Blo 1931435 4348169 := bstep (se 2 (by rfl) ⟨1630563, by rfl⟩ : syracuseStep 4348169 = 3261127) B3261127
theorem B2898779 : Blo 1931435 2898779 := bstep (se 1 (by rfl) ⟨2174084, by rfl⟩ : syracuseStep 2898779 = 4348169) B4348169
theorem B1932519 : Blo 1931435 1932519 := bstep (se 1 (by rfl) ⟨1449389, by rfl⟩ : syracuseStep 1932519 = 2898779) B2898779
theorem B2174089 : Blo 1931435 2174089 := bbase (se 2 (by rfl) ⟨815283, by rfl⟩ : syracuseStep 2174089 = 1630567) (by norm_num)
theorem B2898785 : Blo 1931435 2898785 := bstep (se 2 (by rfl) ⟨1087044, by rfl⟩ : syracuseStep 2898785 = 2174089) B2174089
theorem B1932523 : Blo 1931435 1932523 := bstep (se 1 (by rfl) ⟨1449392, by rfl⟩ : syracuseStep 1932523 = 2898785) B2898785
theorem B3917789 : Blo 1931435 3917789 := bbase (se 3 (by rfl) ⟨734585, by rfl⟩ : syracuseStep 3917789 = 1469171) (by norm_num)
theorem B2611859 : Blo 1931435 2611859 := bstep (se 1 (by rfl) ⟨1958894, by rfl⟩ : syracuseStep 2611859 = 3917789) B3917789
theorem B6964957 : Blo 1931435 6964957 := bstep (se 3 (by rfl) ⟨1305929, by rfl⟩ : syracuseStep 6964957 = 2611859) B2611859
theorem B37146437 : Blo 1931435 37146437 := bstep (se 4 (by rfl) ⟨3482478, by rfl⟩ : syracuseStep 37146437 = 6964957) B6964957
theorem B24764291 : Blo 1931435 24764291 := bstep (se 1 (by rfl) ⟨18573218, by rfl⟩ : syracuseStep 24764291 = 37146437) B37146437
theorem B16509527 : Blo 1931435 16509527 := bstep (se 1 (by rfl) ⟨12382145, by rfl⟩ : syracuseStep 16509527 = 24764291) B24764291
theorem B11006351 : Blo 1931435 11006351 := bstep (se 1 (by rfl) ⟨8254763, by rfl⟩ : syracuseStep 11006351 = 16509527) B16509527
theorem B7337567 : Blo 1931435 7337567 := bstep (se 1 (by rfl) ⟨5503175, by rfl⟩ : syracuseStep 7337567 = 11006351) B11006351
theorem B4891711 : Blo 1931435 4891711 := bstep (se 1 (by rfl) ⟨3668783, by rfl⟩ : syracuseStep 4891711 = 7337567) B7337567
theorem B6522281 : Blo 1931435 6522281 := bstep (se 2 (by rfl) ⟨2445855, by rfl⟩ : syracuseStep 6522281 = 4891711) B4891711
theorem B4348187 : Blo 1931435 4348187 := bstep (se 1 (by rfl) ⟨3261140, by rfl⟩ : syracuseStep 4348187 = 6522281) B6522281
theorem B2898791 : Blo 1931435 2898791 := bstep (se 1 (by rfl) ⟨2174093, by rfl⟩ : syracuseStep 2898791 = 4348187) B4348187
theorem B1932527 : Blo 1931435 1932527 := bstep (se 1 (by rfl) ⟨1449395, by rfl⟩ : syracuseStep 1932527 = 2898791) B2898791
theorem B2898797 : Blo 1931435 2898797 := bbase (se 3 (by rfl) ⟨543524, by rfl⟩ : syracuseStep 2898797 = 1087049) (by norm_num)
theorem B1932531 : Blo 1931435 1932531 := bstep (se 1 (by rfl) ⟨1449398, by rfl⟩ : syracuseStep 1932531 = 2898797) B2898797
theorem B4348205 : Blo 1931435 4348205 := bbase (se 3 (by rfl) ⟨815288, by rfl⟩ : syracuseStep 4348205 = 1630577) (by norm_num)
theorem B2898803 : Blo 1931435 2898803 := bstep (se 1 (by rfl) ⟨2174102, by rfl⟩ : syracuseStep 2898803 = 4348205) B4348205
theorem B1932535 : Blo 1931435 1932535 := bstep (se 1 (by rfl) ⟨1449401, by rfl⟩ : syracuseStep 1932535 = 2898803) B2898803
theorem B2789149 : Blo 1931435 2789149 := bbase (se 3 (by rfl) ⟨522965, by rfl⟩ : syracuseStep 2789149 = 1045931) (by norm_num)
theorem B3718865 : Blo 1931435 3718865 := bstep (se 2 (by rfl) ⟨1394574, by rfl⟩ : syracuseStep 3718865 = 2789149) B2789149
theorem B2479243 : Blo 1931435 2479243 := bstep (se 1 (by rfl) ⟨1859432, by rfl⟩ : syracuseStep 2479243 = 3718865) B3718865
theorem B3305657 : Blo 1931435 3305657 := bstep (se 2 (by rfl) ⟨1239621, by rfl⟩ : syracuseStep 3305657 = 2479243) B2479243
theorem B2203771 : Blo 1931435 2203771 := bstep (se 1 (by rfl) ⟨1652828, by rfl⟩ : syracuseStep 2203771 = 3305657) B3305657
theorem B2938361 : Blo 1931435 2938361 := bstep (se 2 (by rfl) ⟨1101885, by rfl⟩ : syracuseStep 2938361 = 2203771) B2203771
theorem B7835629 : Blo 1931435 7835629 := bstep (se 3 (by rfl) ⟨1469180, by rfl⟩ : syracuseStep 7835629 = 2938361) B2938361
theorem B10447505 : Blo 1931435 10447505 := bstep (se 2 (by rfl) ⟨3917814, by rfl⟩ : syracuseStep 10447505 = 7835629) B7835629
theorem B6965003 : Blo 1931435 6965003 := bstep (se 1 (by rfl) ⟨5223752, by rfl⟩ : syracuseStep 6965003 = 10447505) B10447505
theorem B4643335 : Blo 1931435 4643335 := bstep (se 1 (by rfl) ⟨3482501, by rfl⟩ : syracuseStep 4643335 = 6965003) B6965003
theorem B6191113 : Blo 1931435 6191113 := bstep (se 2 (by rfl) ⟨2321667, by rfl⟩ : syracuseStep 6191113 = 4643335) B4643335
theorem B8254817 : Blo 1931435 8254817 := bstep (se 2 (by rfl) ⟨3095556, by rfl⟩ : syracuseStep 8254817 = 6191113) B6191113
theorem B5503211 : Blo 1931435 5503211 := bstep (se 1 (by rfl) ⟨4127408, by rfl⟩ : syracuseStep 5503211 = 8254817) B8254817
theorem B3668807 : Blo 1931435 3668807 := bstep (se 1 (by rfl) ⟨2751605, by rfl⟩ : syracuseStep 3668807 = 5503211) B5503211
theorem B2445871 : Blo 1931435 2445871 := bstep (se 1 (by rfl) ⟨1834403, by rfl⟩ : syracuseStep 2445871 = 3668807) B3668807
theorem B3261161 : Blo 1931435 3261161 := bstep (se 2 (by rfl) ⟨1222935, by rfl⟩ : syracuseStep 3261161 = 2445871) B2445871
theorem B2174107 : Blo 1931435 2174107 := bstep (se 1 (by rfl) ⟨1630580, by rfl⟩ : syracuseStep 2174107 = 3261161) B3261161
theorem B2898809 : Blo 1931435 2898809 := bstep (se 2 (by rfl) ⟨1087053, by rfl⟩ : syracuseStep 2898809 = 2174107) B2174107
theorem B1932539 : Blo 1931435 1932539 := bstep (se 1 (by rfl) ⟨1449404, by rfl⟩ : syracuseStep 1932539 = 2898809) B2898809
theorem B7942549 : Blo 1931435 7942549 := bbase (se 6 (by rfl) ⟨186153, by rfl⟩ : syracuseStep 7942549 = 372307) (by norm_num)
theorem B10590065 : Blo 1931435 10590065 := bstep (se 2 (by rfl) ⟨3971274, by rfl⟩ : syracuseStep 10590065 = 7942549) B7942549
theorem B7060043 : Blo 1931435 7060043 := bstep (se 1 (by rfl) ⟨5295032, by rfl⟩ : syracuseStep 7060043 = 10590065) B10590065
theorem B4706695 : Blo 1931435 4706695 := bstep (se 1 (by rfl) ⟨3530021, by rfl⟩ : syracuseStep 4706695 = 7060043) B7060043
theorem B6275593 : Blo 1931435 6275593 := bstep (se 2 (by rfl) ⟨2353347, by rfl⟩ : syracuseStep 6275593 = 4706695) B4706695
theorem B8367457 : Blo 1931435 8367457 := bstep (se 2 (by rfl) ⟨3137796, by rfl⟩ : syracuseStep 8367457 = 6275593) B6275593
theorem B11156609 : Blo 1931435 11156609 := bstep (se 2 (by rfl) ⟨4183728, by rfl⟩ : syracuseStep 11156609 = 8367457) B8367457
theorem B7437739 : Blo 1931435 7437739 := bstep (se 1 (by rfl) ⟨5578304, by rfl⟩ : syracuseStep 7437739 = 11156609) B11156609
theorem B9916985 : Blo 1931435 9916985 := bstep (se 2 (by rfl) ⟨3718869, by rfl⟩ : syracuseStep 9916985 = 7437739) B7437739
theorem B6611323 : Blo 1931435 6611323 := bstep (se 1 (by rfl) ⟨4958492, by rfl⟩ : syracuseStep 6611323 = 9916985) B9916985
theorem B8815097 : Blo 1931435 8815097 := bstep (se 2 (by rfl) ⟨3305661, by rfl⟩ : syracuseStep 8815097 = 6611323) B6611323
theorem B5876731 : Blo 1931435 5876731 := bstep (se 1 (by rfl) ⟨4407548, by rfl⟩ : syracuseStep 5876731 = 8815097) B8815097
theorem B31342565 : Blo 1931435 31342565 := bstep (se 4 (by rfl) ⟨2938365, by rfl⟩ : syracuseStep 31342565 = 5876731) B5876731
theorem B20895043 : Blo 1931435 20895043 := bstep (se 1 (by rfl) ⟨15671282, by rfl⟩ : syracuseStep 20895043 = 31342565) B31342565
theorem B27860057 : Blo 1931435 27860057 := bstep (se 2 (by rfl) ⟨10447521, by rfl⟩ : syracuseStep 27860057 = 20895043) B20895043
theorem B18573371 : Blo 1931435 18573371 := bstep (se 1 (by rfl) ⟨13930028, by rfl⟩ : syracuseStep 18573371 = 27860057) B27860057
theorem B12382247 : Blo 1931435 12382247 := bstep (se 1 (by rfl) ⟨9286685, by rfl⟩ : syracuseStep 12382247 = 18573371) B18573371
theorem B33019325 : Blo 1931435 33019325 := bstep (se 3 (by rfl) ⟨6191123, by rfl⟩ : syracuseStep 33019325 = 12382247) B12382247
theorem B22012883 : Blo 1931435 22012883 := bstep (se 1 (by rfl) ⟨16509662, by rfl⟩ : syracuseStep 22012883 = 33019325) B33019325
theorem B14675255 : Blo 1931435 14675255 := bstep (se 1 (by rfl) ⟨11006441, by rfl⟩ : syracuseStep 14675255 = 22012883) B22012883
theorem B9783503 : Blo 1931435 9783503 := bstep (se 1 (by rfl) ⟨7337627, by rfl⟩ : syracuseStep 9783503 = 14675255) B14675255
theorem B6522335 : Blo 1931435 6522335 := bstep (se 1 (by rfl) ⟨4891751, by rfl⟩ : syracuseStep 6522335 = 9783503) B9783503
theorem B4348223 : Blo 1931435 4348223 := bstep (se 1 (by rfl) ⟨3261167, by rfl⟩ : syracuseStep 4348223 = 6522335) B6522335
theorem B2898815 : Blo 1931435 2898815 := bstep (se 1 (by rfl) ⟨2174111, by rfl⟩ : syracuseStep 2898815 = 4348223) B4348223
theorem B1932543 : Blo 1931435 1932543 := bstep (se 1 (by rfl) ⟨1449407, by rfl⟩ : syracuseStep 1932543 = 2898815) B2898815
theorem B2898821 : Blo 1931435 2898821 := bbase (se 4 (by rfl) ⟨271764, by rfl⟩ : syracuseStep 2898821 = 543529) (by norm_num)
theorem B1932547 : Blo 1931435 1932547 := bstep (se 1 (by rfl) ⟨1449410, by rfl⟩ : syracuseStep 1932547 = 2898821) B2898821
theorem B3261181 : Blo 1931435 3261181 := bbase (se 3 (by rfl) ⟨611471, by rfl⟩ : syracuseStep 3261181 = 1222943) (by norm_num)
theorem B4348241 : Blo 1931435 4348241 := bstep (se 2 (by rfl) ⟨1630590, by rfl⟩ : syracuseStep 4348241 = 3261181) B3261181
theorem B2898827 : Blo 1931435 2898827 := bstep (se 1 (by rfl) ⟨2174120, by rfl⟩ : syracuseStep 2898827 = 4348241) B4348241
theorem B1932551 : Blo 1931435 1932551 := bstep (se 1 (by rfl) ⟨1449413, by rfl⟩ : syracuseStep 1932551 = 2898827) B2898827
theorem B2174125 : Blo 1931435 2174125 := bbase (se 3 (by rfl) ⟨407648, by rfl⟩ : syracuseStep 2174125 = 815297) (by norm_num)
theorem B2898833 : Blo 1931435 2898833 := bstep (se 2 (by rfl) ⟨1087062, by rfl⟩ : syracuseStep 2898833 = 2174125) B2174125
theorem B1932555 : Blo 1931435 1932555 := bstep (se 1 (by rfl) ⟨1449416, by rfl⟩ : syracuseStep 1932555 = 2898833) B2898833
theorem B6522389 : Blo 1931435 6522389 := bbase (se 6 (by rfl) ⟨152868, by rfl⟩ : syracuseStep 6522389 = 305737) (by norm_num)
theorem B4348259 : Blo 1931435 4348259 := bstep (se 1 (by rfl) ⟨3261194, by rfl⟩ : syracuseStep 4348259 = 6522389) B6522389
theorem B2898839 : Blo 1931435 2898839 := bstep (se 1 (by rfl) ⟨2174129, by rfl⟩ : syracuseStep 2898839 = 4348259) B4348259
theorem B1932559 : Blo 1931435 1932559 := bstep (se 1 (by rfl) ⟨1449419, by rfl⟩ : syracuseStep 1932559 = 2898839) B2898839
theorem B2898845 : Blo 1931435 2898845 := bbase (se 3 (by rfl) ⟨543533, by rfl⟩ : syracuseStep 2898845 = 1087067) (by norm_num)
theorem B1932563 : Blo 1931435 1932563 := bstep (se 1 (by rfl) ⟨1449422, by rfl⟩ : syracuseStep 1932563 = 2898845) B2898845
theorem B4348277 : Blo 1931435 4348277 := bbase (se 5 (by rfl) ⟨203825, by rfl⟩ : syracuseStep 4348277 = 407651) (by norm_num)
theorem B2898851 : Blo 1931435 2898851 := bstep (se 1 (by rfl) ⟨2174138, by rfl⟩ : syracuseStep 2898851 = 4348277) B4348277
theorem B1932567 : Blo 1931435 1932567 := bstep (se 1 (by rfl) ⟨1449425, by rfl⟩ : syracuseStep 1932567 = 2898851) B2898851
theorem B3350813 : Blo 1931435 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B35742005 : Blo 1931435 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B23828003 : Blo 1931435 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B15885335 : Blo 1931435 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B42360893 : Blo 1931435 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B28240595 : Blo 1931435 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B18827063 : Blo 1931435 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B12551375 : Blo 1931435 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B8367583 : Blo 1931435 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B11156777 : Blo 1931435 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B7437851 : Blo 1931435 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B4958567 : Blo 1931435 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B3305711 : Blo 1931435 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B8815229 : Blo 1931435 8815229 := bstep (se 3 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 8815229 = 3305711) B3305711
theorem B5876819 : Blo 1931435 5876819 := bstep (se 1 (by rfl) ⟨4407614, by rfl⟩ : syracuseStep 5876819 = 8815229) B8815229
theorem B3917879 : Blo 1931435 3917879 := bstep (se 1 (by rfl) ⟨2938409, by rfl⟩ : syracuseStep 3917879 = 5876819) B5876819
theorem B2611919 : Blo 1931435 2611919 := bstep (se 1 (by rfl) ⟨1958939, by rfl⟩ : syracuseStep 2611919 = 3917879) B3917879
theorem B6965117 : Blo 1931435 6965117 := bstep (se 3 (by rfl) ⟨1305959, by rfl⟩ : syracuseStep 6965117 = 2611919) B2611919
theorem B4643411 : Blo 1931435 4643411 := bstep (se 1 (by rfl) ⟨3482558, by rfl⟩ : syracuseStep 4643411 = 6965117) B6965117
theorem B12382429 : Blo 1931435 12382429 := bstep (se 3 (by rfl) ⟨2321705, by rfl⟩ : syracuseStep 12382429 = 4643411) B4643411
theorem B16509905 : Blo 1931435 16509905 := bstep (se 2 (by rfl) ⟨6191214, by rfl⟩ : syracuseStep 16509905 = 12382429) B12382429
theorem B11006603 : Blo 1931435 11006603 := bstep (se 1 (by rfl) ⟨8254952, by rfl⟩ : syracuseStep 11006603 = 16509905) B16509905
theorem B7337735 : Blo 1931435 7337735 := bstep (se 1 (by rfl) ⟨5503301, by rfl⟩ : syracuseStep 7337735 = 11006603) B11006603
theorem B4891823 : Blo 1931435 4891823 := bstep (se 1 (by rfl) ⟨3668867, by rfl⟩ : syracuseStep 4891823 = 7337735) B7337735
theorem B3261215 : Blo 1931435 3261215 := bstep (se 1 (by rfl) ⟨2445911, by rfl⟩ : syracuseStep 3261215 = 4891823) B4891823
theorem B2174143 : Blo 1931435 2174143 := bstep (se 1 (by rfl) ⟨1630607, by rfl⟩ : syracuseStep 2174143 = 3261215) B3261215
theorem B2898857 : Blo 1931435 2898857 := bstep (se 2 (by rfl) ⟨1087071, by rfl⟩ : syracuseStep 2898857 = 2174143) B2174143
theorem B1932571 : Blo 1931435 1932571 := bstep (se 1 (by rfl) ⟨1449428, by rfl⟩ : syracuseStep 1932571 = 2898857) B2898857
theorem B7337749 : Blo 1931435 7337749 := bbase (se 6 (by rfl) ⟨171978, by rfl⟩ : syracuseStep 7337749 = 343957) (by norm_num)
theorem B9783665 : Blo 1931435 9783665 := bstep (se 2 (by rfl) ⟨3668874, by rfl⟩ : syracuseStep 9783665 = 7337749) B7337749
theorem B6522443 : Blo 1931435 6522443 := bstep (se 1 (by rfl) ⟨4891832, by rfl⟩ : syracuseStep 6522443 = 9783665) B9783665
theorem B4348295 : Blo 1931435 4348295 := bstep (se 1 (by rfl) ⟨3261221, by rfl⟩ : syracuseStep 4348295 = 6522443) B6522443
theorem B2898863 : Blo 1931435 2898863 := bstep (se 1 (by rfl) ⟨2174147, by rfl⟩ : syracuseStep 2898863 = 4348295) B4348295
theorem B1932575 : Blo 1931435 1932575 := bstep (se 1 (by rfl) ⟨1449431, by rfl⟩ : syracuseStep 1932575 = 2898863) B2898863
theorem B2898869 : Blo 1931435 2898869 := bbase (se 5 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 2898869 = 271769) (by norm_num)
theorem B1932579 : Blo 1931435 1932579 := bstep (se 1 (by rfl) ⟨1449434, by rfl⟩ : syracuseStep 1932579 = 2898869) B2898869
theorem B4891853 : Blo 1931435 4891853 := bbase (se 3 (by rfl) ⟨917222, by rfl⟩ : syracuseStep 4891853 = 1834445) (by norm_num)
theorem B3261235 : Blo 1931435 3261235 := bstep (se 1 (by rfl) ⟨2445926, by rfl⟩ : syracuseStep 3261235 = 4891853) B4891853
theorem B4348313 : Blo 1931435 4348313 := bstep (se 2 (by rfl) ⟨1630617, by rfl⟩ : syracuseStep 4348313 = 3261235) B3261235
theorem B2898875 : Blo 1931435 2898875 := bstep (se 1 (by rfl) ⟨2174156, by rfl⟩ : syracuseStep 2898875 = 4348313) B4348313
theorem B1932583 : Blo 1931435 1932583 := bstep (se 1 (by rfl) ⟨1449437, by rfl⟩ : syracuseStep 1932583 = 2898875) B2898875
theorem B2174161 : Blo 1931435 2174161 := bbase (se 2 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 2174161 = 1630621) (by norm_num)
theorem B2898881 : Blo 1931435 2898881 := bstep (se 2 (by rfl) ⟨1087080, by rfl⟩ : syracuseStep 2898881 = 2174161) B2174161
theorem B1932587 : Blo 1931435 1932587 := bstep (se 1 (by rfl) ⟨1449440, by rfl⟩ : syracuseStep 1932587 = 2898881) B2898881
theorem B2091917 : Blo 1931435 2091917 := bbase (se 3 (by rfl) ⟨392234, by rfl⟩ : syracuseStep 2091917 = 784469) (by norm_num)
theorem B5578445 : Blo 1931435 5578445 := bstep (se 3 (by rfl) ⟨1045958, by rfl⟩ : syracuseStep 5578445 = 2091917) B2091917
theorem B3718963 : Blo 1931435 3718963 := bstep (se 1 (by rfl) ⟨2789222, by rfl⟩ : syracuseStep 3718963 = 5578445) B5578445
theorem B19834469 : Blo 1931435 19834469 := bstep (se 4 (by rfl) ⟨1859481, by rfl⟩ : syracuseStep 19834469 = 3718963) B3718963
theorem B13222979 : Blo 1931435 13222979 := bstep (se 1 (by rfl) ⟨9917234, by rfl⟩ : syracuseStep 13222979 = 19834469) B19834469
theorem B8815319 : Blo 1931435 8815319 := bstep (se 1 (by rfl) ⟨6611489, by rfl⟩ : syracuseStep 8815319 = 13222979) B13222979
theorem B5876879 : Blo 1931435 5876879 := bstep (se 1 (by rfl) ⟨4407659, by rfl⟩ : syracuseStep 5876879 = 8815319) B8815319
theorem B15671677 : Blo 1931435 15671677 := bstep (se 3 (by rfl) ⟨2938439, by rfl⟩ : syracuseStep 15671677 = 5876879) B5876879
theorem B20895569 : Blo 1931435 20895569 := bstep (se 2 (by rfl) ⟨7835838, by rfl⟩ : syracuseStep 20895569 = 15671677) B15671677
theorem B13930379 : Blo 1931435 13930379 := bstep (se 1 (by rfl) ⟨10447784, by rfl⟩ : syracuseStep 13930379 = 20895569) B20895569
theorem B9286919 : Blo 1931435 9286919 := bstep (se 1 (by rfl) ⟨6965189, by rfl⟩ : syracuseStep 9286919 = 13930379) B13930379
theorem B6191279 : Blo 1931435 6191279 := bstep (se 1 (by rfl) ⟨4643459, by rfl⟩ : syracuseStep 6191279 = 9286919) B9286919
theorem B4127519 : Blo 1931435 4127519 := bstep (se 1 (by rfl) ⟨3095639, by rfl⟩ : syracuseStep 4127519 = 6191279) B6191279
theorem B2751679 : Blo 1931435 2751679 := bstep (se 1 (by rfl) ⟨2063759, by rfl⟩ : syracuseStep 2751679 = 4127519) B4127519
theorem B3668905 : Blo 1931435 3668905 := bstep (se 2 (by rfl) ⟨1375839, by rfl⟩ : syracuseStep 3668905 = 2751679) B2751679
theorem B4891873 : Blo 1931435 4891873 := bstep (se 2 (by rfl) ⟨1834452, by rfl⟩ : syracuseStep 4891873 = 3668905) B3668905
theorem B6522497 : Blo 1931435 6522497 := bstep (se 2 (by rfl) ⟨2445936, by rfl⟩ : syracuseStep 6522497 = 4891873) B4891873
theorem B4348331 : Blo 1931435 4348331 := bstep (se 1 (by rfl) ⟨3261248, by rfl⟩ : syracuseStep 4348331 = 6522497) B6522497
theorem B2898887 : Blo 1931435 2898887 := bstep (se 1 (by rfl) ⟨2174165, by rfl⟩ : syracuseStep 2898887 = 4348331) B4348331
theorem B1932591 : Blo 1931435 1932591 := bstep (se 1 (by rfl) ⟨1449443, by rfl⟩ : syracuseStep 1932591 = 2898887) B2898887
theorem B2898893 : Blo 1931435 2898893 := bbase (se 3 (by rfl) ⟨543542, by rfl⟩ : syracuseStep 2898893 = 1087085) (by norm_num)
theorem B1932595 : Blo 1931435 1932595 := bstep (se 1 (by rfl) ⟨1449446, by rfl⟩ : syracuseStep 1932595 = 2898893) B2898893
theorem B4348349 : Blo 1931435 4348349 := bbase (se 3 (by rfl) ⟨815315, by rfl⟩ : syracuseStep 4348349 = 1630631) (by norm_num)
theorem B2898899 : Blo 1931435 2898899 := bstep (se 1 (by rfl) ⟨2174174, by rfl⟩ : syracuseStep 2898899 = 4348349) B4348349
theorem B1932599 : Blo 1931435 1932599 := bstep (se 1 (by rfl) ⟨1449449, by rfl⟩ : syracuseStep 1932599 = 2898899) B2898899
theorem B3261269 : Blo 1931435 3261269 := bbase (se 9 (by rfl) ⟨9554, by rfl⟩ : syracuseStep 3261269 = 19109) (by norm_num)
theorem B2174179 : Blo 1931435 2174179 := bstep (se 1 (by rfl) ⟨1630634, by rfl⟩ : syracuseStep 2174179 = 3261269) B3261269
theorem B2898905 : Blo 1931435 2898905 := bstep (se 2 (by rfl) ⟨1087089, by rfl⟩ : syracuseStep 2898905 = 2174179) B2174179
theorem B1932603 : Blo 1931435 1932603 := bstep (se 1 (by rfl) ⟨1449452, by rfl⟩ : syracuseStep 1932603 = 2898905) B2898905
theorem B7060277 : Blo 1931435 7060277 := bbase (se 5 (by rfl) ⟨330950, by rfl⟩ : syracuseStep 7060277 = 661901) (by norm_num)
theorem B18827405 : Blo 1931435 18827405 := bstep (se 3 (by rfl) ⟨3530138, by rfl⟩ : syracuseStep 18827405 = 7060277) B7060277
theorem B12551603 : Blo 1931435 12551603 := bstep (se 1 (by rfl) ⟨9413702, by rfl⟩ : syracuseStep 12551603 = 18827405) B18827405
theorem B133883765 : Blo 1931435 133883765 := bstep (se 5 (by rfl) ⟨6275801, by rfl⟩ : syracuseStep 133883765 = 12551603) B12551603
theorem B89255843 : Blo 1931435 89255843 := bstep (se 1 (by rfl) ⟨66941882, by rfl⟩ : syracuseStep 89255843 = 133883765) B133883765
theorem B59503895 : Blo 1931435 59503895 := bstep (se 1 (by rfl) ⟨44627921, by rfl⟩ : syracuseStep 59503895 = 89255843) B89255843
theorem B39669263 : Blo 1931435 39669263 := bstep (se 1 (by rfl) ⟨29751947, by rfl⟩ : syracuseStep 39669263 = 59503895) B59503895
theorem B26446175 : Blo 1931435 26446175 := bstep (se 1 (by rfl) ⟨19834631, by rfl⟩ : syracuseStep 26446175 = 39669263) B39669263
theorem B17630783 : Blo 1931435 17630783 := bstep (se 1 (by rfl) ⟨13223087, by rfl⟩ : syracuseStep 17630783 = 26446175) B26446175
theorem B11753855 : Blo 1931435 11753855 := bstep (se 1 (by rfl) ⟨8815391, by rfl⟩ : syracuseStep 11753855 = 17630783) B17630783
theorem B7835903 : Blo 1931435 7835903 := bstep (se 1 (by rfl) ⟨5876927, by rfl⟩ : syracuseStep 7835903 = 11753855) B11753855
theorem B5223935 : Blo 1931435 5223935 := bstep (se 1 (by rfl) ⟨3917951, by rfl⟩ : syracuseStep 5223935 = 7835903) B7835903
theorem B3482623 : Blo 1931435 3482623 := bstep (se 1 (by rfl) ⟨2611967, by rfl⟩ : syracuseStep 3482623 = 5223935) B5223935
theorem B4643497 : Blo 1931435 4643497 := bstep (se 2 (by rfl) ⟨1741311, by rfl⟩ : syracuseStep 4643497 = 3482623) B3482623
theorem B6191329 : Blo 1931435 6191329 := bstep (se 2 (by rfl) ⟨2321748, by rfl⟩ : syracuseStep 6191329 = 4643497) B4643497
theorem B8255105 : Blo 1931435 8255105 := bstep (se 2 (by rfl) ⟨3095664, by rfl⟩ : syracuseStep 8255105 = 6191329) B6191329
theorem B5503403 : Blo 1931435 5503403 := bstep (se 1 (by rfl) ⟨4127552, by rfl⟩ : syracuseStep 5503403 = 8255105) B8255105
theorem B14675741 : Blo 1931435 14675741 := bstep (se 3 (by rfl) ⟨2751701, by rfl⟩ : syracuseStep 14675741 = 5503403) B5503403
theorem B9783827 : Blo 1931435 9783827 := bstep (se 1 (by rfl) ⟨7337870, by rfl⟩ : syracuseStep 9783827 = 14675741) B14675741
theorem B6522551 : Blo 1931435 6522551 := bstep (se 1 (by rfl) ⟨4891913, by rfl⟩ : syracuseStep 6522551 = 9783827) B9783827
theorem B4348367 : Blo 1931435 4348367 := bstep (se 1 (by rfl) ⟨3261275, by rfl⟩ : syracuseStep 4348367 = 6522551) B6522551
theorem B2898911 : Blo 1931435 2898911 := bstep (se 1 (by rfl) ⟨2174183, by rfl⟩ : syracuseStep 2898911 = 4348367) B4348367
theorem B1932607 : Blo 1931435 1932607 := bstep (se 1 (by rfl) ⟨1449455, by rfl⟩ : syracuseStep 1932607 = 2898911) B2898911
theorem B2898917 : Blo 1931435 2898917 := bbase (se 4 (by rfl) ⟨271773, by rfl⟩ : syracuseStep 2898917 = 543547) (by norm_num)
theorem B1932611 : Blo 1931435 1932611 := bstep (se 1 (by rfl) ⟨1449458, by rfl⟩ : syracuseStep 1932611 = 2898917) B2898917
theorem B8255141 : Blo 1931435 8255141 := bbase (se 4 (by rfl) ⟨773919, by rfl⟩ : syracuseStep 8255141 = 1547839) (by norm_num)
theorem B5503427 : Blo 1931435 5503427 := bstep (se 1 (by rfl) ⟨4127570, by rfl⟩ : syracuseStep 5503427 = 8255141) B8255141
theorem B3668951 : Blo 1931435 3668951 := bstep (se 1 (by rfl) ⟨2751713, by rfl⟩ : syracuseStep 3668951 = 5503427) B5503427
theorem B2445967 : Blo 1931435 2445967 := bstep (se 1 (by rfl) ⟨1834475, by rfl⟩ : syracuseStep 2445967 = 3668951) B3668951
theorem B3261289 : Blo 1931435 3261289 := bstep (se 2 (by rfl) ⟨1222983, by rfl⟩ : syracuseStep 3261289 = 2445967) B2445967
theorem B4348385 : Blo 1931435 4348385 := bstep (se 2 (by rfl) ⟨1630644, by rfl⟩ : syracuseStep 4348385 = 3261289) B3261289
theorem B2898923 : Blo 1931435 2898923 := bstep (se 1 (by rfl) ⟨2174192, by rfl⟩ : syracuseStep 2898923 = 4348385) B4348385
theorem B1932615 : Blo 1931435 1932615 := bstep (se 1 (by rfl) ⟨1449461, by rfl⟩ : syracuseStep 1932615 = 2898923) B2898923
theorem B2174197 : Blo 1931435 2174197 := bbase (se 5 (by rfl) ⟨101915, by rfl⟩ : syracuseStep 2174197 = 203831) (by norm_num)
theorem B2898929 : Blo 1931435 2898929 := bstep (se 2 (by rfl) ⟨1087098, by rfl⟩ : syracuseStep 2898929 = 2174197) B2174197
theorem B1932619 : Blo 1931435 1932619 := bstep (se 1 (by rfl) ⟨1449464, by rfl⟩ : syracuseStep 1932619 = 2898929) B2898929
theorem B2445977 : Blo 1931435 2445977 := bbase (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) (by norm_num)
theorem B6522605 : Blo 1931435 6522605 := bstep (se 3 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 6522605 = 2445977) B2445977
theorem B4348403 : Blo 1931435 4348403 := bstep (se 1 (by rfl) ⟨3261302, by rfl⟩ : syracuseStep 4348403 = 6522605) B6522605
theorem B2898935 : Blo 1931435 2898935 := bstep (se 1 (by rfl) ⟨2174201, by rfl⟩ : syracuseStep 2898935 = 4348403) B4348403
theorem B1932623 : Blo 1931435 1932623 := bstep (se 1 (by rfl) ⟨1449467, by rfl⟩ : syracuseStep 1932623 = 2898935) B2898935
theorem B2898941 : Blo 1931435 2898941 := bbase (se 3 (by rfl) ⟨543551, by rfl⟩ : syracuseStep 2898941 = 1087103) (by norm_num)
theorem B1932627 : Blo 1931435 1932627 := bstep (se 1 (by rfl) ⟨1449470, by rfl⟩ : syracuseStep 1932627 = 2898941) B2898941
theorem B4348421 : Blo 1931435 4348421 := bbase (se 4 (by rfl) ⟨407664, by rfl⟩ : syracuseStep 4348421 = 815329) (by norm_num)
theorem B2898947 : Blo 1931435 2898947 := bstep (se 1 (by rfl) ⟨2174210, by rfl⟩ : syracuseStep 2898947 = 4348421) B4348421
theorem B1932631 : Blo 1931435 1932631 := bstep (se 1 (by rfl) ⟨1449473, by rfl⟩ : syracuseStep 1932631 = 2898947) B2898947
theorem B3668989 : Blo 1931435 3668989 := bbase (se 3 (by rfl) ⟨687935, by rfl⟩ : syracuseStep 3668989 = 1375871) (by norm_num)
theorem B4891985 : Blo 1931435 4891985 := bstep (se 2 (by rfl) ⟨1834494, by rfl⟩ : syracuseStep 4891985 = 3668989) B3668989
theorem B3261323 : Blo 1931435 3261323 := bstep (se 1 (by rfl) ⟨2445992, by rfl⟩ : syracuseStep 3261323 = 4891985) B4891985
theorem B2174215 : Blo 1931435 2174215 := bstep (se 1 (by rfl) ⟨1630661, by rfl⟩ : syracuseStep 2174215 = 3261323) B3261323
theorem B2898953 : Blo 1931435 2898953 := bstep (se 2 (by rfl) ⟨1087107, by rfl⟩ : syracuseStep 2898953 = 2174215) B2174215
theorem B1932635 : Blo 1931435 1932635 := bstep (se 1 (by rfl) ⟨1449476, by rfl⟩ : syracuseStep 1932635 = 2898953) B2898953
theorem B9783989 : Blo 1931435 9783989 := bbase (se 5 (by rfl) ⟨458624, by rfl⟩ : syracuseStep 9783989 = 917249) (by norm_num)
theorem B6522659 : Blo 1931435 6522659 := bstep (se 1 (by rfl) ⟨4891994, by rfl⟩ : syracuseStep 6522659 = 9783989) B9783989
theorem B4348439 : Blo 1931435 4348439 := bstep (se 1 (by rfl) ⟨3261329, by rfl⟩ : syracuseStep 4348439 = 6522659) B6522659
theorem B2898959 : Blo 1931435 2898959 := bstep (se 1 (by rfl) ⟨2174219, by rfl⟩ : syracuseStep 2898959 = 4348439) B4348439
theorem B1932639 : Blo 1931435 1932639 := bstep (se 1 (by rfl) ⟨1449479, by rfl⟩ : syracuseStep 1932639 = 2898959) B2898959
theorem B2898965 : Blo 1931435 2898965 := bbase (se 6 (by rfl) ⟨67944, by rfl⟩ : syracuseStep 2898965 = 135889) (by norm_num)
theorem B1932643 : Blo 1931435 1932643 := bstep (se 1 (by rfl) ⟨1449482, by rfl⟩ : syracuseStep 1932643 = 2898965) B2898965
theorem B2513209 : Blo 1931435 2513209 := bbase (se 2 (by rfl) ⟨942453, by rfl⟩ : syracuseStep 2513209 = 1884907) (by norm_num)
theorem B3350945 : Blo 1931435 3350945 := bstep (se 2 (by rfl) ⟨1256604, by rfl⟩ : syracuseStep 3350945 = 2513209) B2513209
theorem B2233963 : Blo 1931435 2233963 := bstep (se 1 (by rfl) ⟨1675472, by rfl⟩ : syracuseStep 2233963 = 3350945) B3350945
theorem B11914469 : Blo 1931435 11914469 := bstep (se 4 (by rfl) ⟨1116981, by rfl⟩ : syracuseStep 11914469 = 2233963) B2233963
theorem B7942979 : Blo 1931435 7942979 := bstep (se 1 (by rfl) ⟨5957234, by rfl⟩ : syracuseStep 7942979 = 11914469) B11914469
theorem B21181277 : Blo 1931435 21181277 := bstep (se 3 (by rfl) ⟨3971489, by rfl⟩ : syracuseStep 21181277 = 7942979) B7942979
theorem B14120851 : Blo 1931435 14120851 := bstep (se 1 (by rfl) ⟨10590638, by rfl⟩ : syracuseStep 14120851 = 21181277) B21181277
theorem B18827801 : Blo 1931435 18827801 := bstep (se 2 (by rfl) ⟨7060425, by rfl⟩ : syracuseStep 18827801 = 14120851) B14120851
theorem B12551867 : Blo 1931435 12551867 := bstep (se 1 (by rfl) ⟨9413900, by rfl⟩ : syracuseStep 12551867 = 18827801) B18827801
theorem B8367911 : Blo 1931435 8367911 := bstep (se 1 (by rfl) ⟨6275933, by rfl⟩ : syracuseStep 8367911 = 12551867) B12551867
theorem B5578607 : Blo 1931435 5578607 := bstep (se 1 (by rfl) ⟨4183955, by rfl⟩ : syracuseStep 5578607 = 8367911) B8367911
theorem B3719071 : Blo 1931435 3719071 := bstep (se 1 (by rfl) ⟨2789303, by rfl⟩ : syracuseStep 3719071 = 5578607) B5578607
theorem B4958761 : Blo 1931435 4958761 := bstep (se 2 (by rfl) ⟨1859535, by rfl⟩ : syracuseStep 4958761 = 3719071) B3719071
theorem B6611681 : Blo 1931435 6611681 := bstep (se 2 (by rfl) ⟨2479380, by rfl⟩ : syracuseStep 6611681 = 4958761) B4958761
theorem B4407787 : Blo 1931435 4407787 := bstep (se 1 (by rfl) ⟨3305840, by rfl⟩ : syracuseStep 4407787 = 6611681) B6611681
theorem B5877049 : Blo 1931435 5877049 := bstep (se 2 (by rfl) ⟨2203893, by rfl⟩ : syracuseStep 5877049 = 4407787) B4407787
theorem B7836065 : Blo 1931435 7836065 := bstep (se 2 (by rfl) ⟨2938524, by rfl⟩ : syracuseStep 7836065 = 5877049) B5877049
theorem B5224043 : Blo 1931435 5224043 := bstep (se 1 (by rfl) ⟨3918032, by rfl⟩ : syracuseStep 5224043 = 7836065) B7836065
theorem B3482695 : Blo 1931435 3482695 := bstep (se 1 (by rfl) ⟨2612021, by rfl⟩ : syracuseStep 3482695 = 5224043) B5224043
theorem B18574373 : Blo 1931435 18574373 := bstep (se 4 (by rfl) ⟨1741347, by rfl⟩ : syracuseStep 18574373 = 3482695) B3482695
theorem B12382915 : Blo 1931435 12382915 := bstep (se 1 (by rfl) ⟨9287186, by rfl⟩ : syracuseStep 12382915 = 18574373) B18574373
theorem B16510553 : Blo 1931435 16510553 := bstep (se 2 (by rfl) ⟨6191457, by rfl⟩ : syracuseStep 16510553 = 12382915) B12382915
theorem B11007035 : Blo 1931435 11007035 := bstep (se 1 (by rfl) ⟨8255276, by rfl⟩ : syracuseStep 11007035 = 16510553) B16510553
theorem B7338023 : Blo 1931435 7338023 := bstep (se 1 (by rfl) ⟨5503517, by rfl⟩ : syracuseStep 7338023 = 11007035) B11007035
theorem B4892015 : Blo 1931435 4892015 := bstep (se 1 (by rfl) ⟨3669011, by rfl⟩ : syracuseStep 4892015 = 7338023) B7338023
theorem B3261343 : Blo 1931435 3261343 := bstep (se 1 (by rfl) ⟨2446007, by rfl⟩ : syracuseStep 3261343 = 4892015) B4892015
theorem B4348457 : Blo 1931435 4348457 := bstep (se 2 (by rfl) ⟨1630671, by rfl⟩ : syracuseStep 4348457 = 3261343) B3261343
theorem B2898971 : Blo 1931435 2898971 := bstep (se 1 (by rfl) ⟨2174228, by rfl⟩ : syracuseStep 2898971 = 4348457) B4348457
theorem B1932647 : Blo 1931435 1932647 := bstep (se 1 (by rfl) ⟨1449485, by rfl⟩ : syracuseStep 1932647 = 2898971) B2898971
theorem B2174233 : Blo 1931435 2174233 := bbase (se 2 (by rfl) ⟨815337, by rfl⟩ : syracuseStep 2174233 = 1630675) (by norm_num)
theorem B2898977 : Blo 1931435 2898977 := bstep (se 2 (by rfl) ⟨1087116, by rfl⟩ : syracuseStep 2898977 = 2174233) B2174233
theorem B1932651 : Blo 1931435 1932651 := bstep (se 1 (by rfl) ⟨1449488, by rfl⟩ : syracuseStep 1932651 = 2898977) B2898977
theorem B7338053 : Blo 1931435 7338053 := bbase (se 4 (by rfl) ⟨687942, by rfl⟩ : syracuseStep 7338053 = 1375885) (by norm_num)
theorem B4892035 : Blo 1931435 4892035 := bstep (se 1 (by rfl) ⟨3669026, by rfl⟩ : syracuseStep 4892035 = 7338053) B7338053
theorem B6522713 : Blo 1931435 6522713 := bstep (se 2 (by rfl) ⟨2446017, by rfl⟩ : syracuseStep 6522713 = 4892035) B4892035
theorem B4348475 : Blo 1931435 4348475 := bstep (se 1 (by rfl) ⟨3261356, by rfl⟩ : syracuseStep 4348475 = 6522713) B6522713
theorem B2898983 : Blo 1931435 2898983 := bstep (se 1 (by rfl) ⟨2174237, by rfl⟩ : syracuseStep 2898983 = 4348475) B4348475
theorem B1932655 : Blo 1931435 1932655 := bstep (se 1 (by rfl) ⟨1449491, by rfl⟩ : syracuseStep 1932655 = 2898983) B2898983
theorem B2898989 : Blo 1931435 2898989 := bbase (se 3 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 2898989 = 1087121) (by norm_num)
theorem B1932659 : Blo 1931435 1932659 := bstep (se 1 (by rfl) ⟨1449494, by rfl⟩ : syracuseStep 1932659 = 2898989) B2898989
theorem B4348493 : Blo 1931435 4348493 := bbase (se 3 (by rfl) ⟨815342, by rfl⟩ : syracuseStep 4348493 = 1630685) (by norm_num)
theorem B2898995 : Blo 1931435 2898995 := bstep (se 1 (by rfl) ⟨2174246, by rfl⟩ : syracuseStep 2898995 = 4348493) B4348493
theorem B1932663 : Blo 1931435 1932663 := bstep (se 1 (by rfl) ⟨1449497, by rfl⟩ : syracuseStep 1932663 = 2898995) B2898995
theorem B2446033 : Blo 1931435 2446033 := bbase (se 2 (by rfl) ⟨917262, by rfl⟩ : syracuseStep 2446033 = 1834525) (by norm_num)
theorem B3261377 : Blo 1931435 3261377 := bstep (se 2 (by rfl) ⟨1223016, by rfl⟩ : syracuseStep 3261377 = 2446033) B2446033
theorem B2174251 : Blo 1931435 2174251 := bstep (se 1 (by rfl) ⟨1630688, by rfl⟩ : syracuseStep 2174251 = 3261377) B3261377
theorem B2899001 : Blo 1931435 2899001 := bstep (se 2 (by rfl) ⟨1087125, by rfl⟩ : syracuseStep 2899001 = 2174251) B2174251
theorem B1932667 : Blo 1931435 1932667 := bstep (se 1 (by rfl) ⟨1449500, by rfl⟩ : syracuseStep 1932667 = 2899001) B2899001
theorem B6965477 : Blo 1931435 6965477 := bbase (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) (by norm_num)
theorem B4643651 : Blo 1931435 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B3095767 : Blo 1931435 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B4127689 : Blo 1931435 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B22014341 : Blo 1931435 22014341 := bstep (se 4 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 22014341 = 4127689) B4127689
theorem B14676227 : Blo 1931435 14676227 := bstep (se 1 (by rfl) ⟨11007170, by rfl⟩ : syracuseStep 14676227 = 22014341) B22014341
theorem B9784151 : Blo 1931435 9784151 := bstep (se 1 (by rfl) ⟨7338113, by rfl⟩ : syracuseStep 9784151 = 14676227) B14676227
theorem B6522767 : Blo 1931435 6522767 := bstep (se 1 (by rfl) ⟨4892075, by rfl⟩ : syracuseStep 6522767 = 9784151) B9784151
theorem B4348511 : Blo 1931435 4348511 := bstep (se 1 (by rfl) ⟨3261383, by rfl⟩ : syracuseStep 4348511 = 6522767) B6522767
theorem B2899007 : Blo 1931435 2899007 := bstep (se 1 (by rfl) ⟨2174255, by rfl⟩ : syracuseStep 2899007 = 4348511) B4348511
theorem B1932671 : Blo 1931435 1932671 := bstep (se 1 (by rfl) ⟨1449503, by rfl⟩ : syracuseStep 1932671 = 2899007) B2899007
theorem B2899013 : Blo 1931435 2899013 := bbase (se 4 (by rfl) ⟨271782, by rfl⟩ : syracuseStep 2899013 = 543565) (by norm_num)
theorem B1932675 : Blo 1931435 1932675 := bstep (se 1 (by rfl) ⟨1449506, by rfl⟩ : syracuseStep 1932675 = 2899013) B2899013
theorem B3261397 : Blo 1931435 3261397 := bbase (se 7 (by rfl) ⟨38219, by rfl⟩ : syracuseStep 3261397 = 76439) (by norm_num)
theorem B4348529 : Blo 1931435 4348529 := bstep (se 2 (by rfl) ⟨1630698, by rfl⟩ : syracuseStep 4348529 = 3261397) B3261397
theorem B2899019 : Blo 1931435 2899019 := bstep (se 1 (by rfl) ⟨2174264, by rfl⟩ : syracuseStep 2899019 = 4348529) B4348529
theorem B1932679 : Blo 1931435 1932679 := bstep (se 1 (by rfl) ⟨1449509, by rfl⟩ : syracuseStep 1932679 = 2899019) B2899019
theorem B2174269 : Blo 1931435 2174269 := bbase (se 3 (by rfl) ⟨407675, by rfl⟩ : syracuseStep 2174269 = 815351) (by norm_num)
theorem B2899025 : Blo 1931435 2899025 := bstep (se 2 (by rfl) ⟨1087134, by rfl⟩ : syracuseStep 2899025 = 2174269) B2174269
theorem B1932683 : Blo 1931435 1932683 := bstep (se 1 (by rfl) ⟨1449512, by rfl⟩ : syracuseStep 1932683 = 2899025) B2899025
theorem B6522821 : Blo 1931435 6522821 := bbase (se 4 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 6522821 = 1223029) (by norm_num)
theorem B4348547 : Blo 1931435 4348547 := bstep (se 1 (by rfl) ⟨3261410, by rfl⟩ : syracuseStep 4348547 = 6522821) B6522821
theorem B2899031 : Blo 1931435 2899031 := bstep (se 1 (by rfl) ⟨2174273, by rfl⟩ : syracuseStep 2899031 = 4348547) B4348547
theorem B1932687 : Blo 1931435 1932687 := bstep (se 1 (by rfl) ⟨1449515, by rfl⟩ : syracuseStep 1932687 = 2899031) B2899031
theorem B2899037 : Blo 1931435 2899037 := bbase (se 3 (by rfl) ⟨543569, by rfl⟩ : syracuseStep 2899037 = 1087139) (by norm_num)
theorem B1932691 : Blo 1931435 1932691 := bstep (se 1 (by rfl) ⟨1449518, by rfl⟩ : syracuseStep 1932691 = 2899037) B2899037
theorem B4348565 : Blo 1931435 4348565 := bbase (se 6 (by rfl) ⟨101919, by rfl⟩ : syracuseStep 4348565 = 203839) (by norm_num)
theorem B2899043 : Blo 1931435 2899043 := bstep (se 1 (by rfl) ⟨2174282, by rfl⟩ : syracuseStep 2899043 = 4348565) B4348565
theorem B1932695 : Blo 1931435 1932695 := bstep (se 1 (by rfl) ⟨1449521, by rfl⟩ : syracuseStep 1932695 = 2899043) B2899043
theorem B3095813 : Blo 1931435 3095813 := bbase (se 4 (by rfl) ⟨290232, by rfl⟩ : syracuseStep 3095813 = 580465) (by norm_num)
theorem B2063875 : Blo 1931435 2063875 := bstep (se 1 (by rfl) ⟨1547906, by rfl⟩ : syracuseStep 2063875 = 3095813) B3095813
theorem B2751833 : Blo 1931435 2751833 := bstep (se 2 (by rfl) ⟨1031937, by rfl⟩ : syracuseStep 2751833 = 2063875) B2063875
theorem B7338221 : Blo 1931435 7338221 := bstep (se 3 (by rfl) ⟨1375916, by rfl⟩ : syracuseStep 7338221 = 2751833) B2751833
theorem B4892147 : Blo 1931435 4892147 := bstep (se 1 (by rfl) ⟨3669110, by rfl⟩ : syracuseStep 4892147 = 7338221) B7338221
theorem B3261431 : Blo 1931435 3261431 := bstep (se 1 (by rfl) ⟨2446073, by rfl⟩ : syracuseStep 3261431 = 4892147) B4892147
theorem B2174287 : Blo 1931435 2174287 := bstep (se 1 (by rfl) ⟨1630715, by rfl⟩ : syracuseStep 2174287 = 3261431) B3261431
theorem B2899049 : Blo 1931435 2899049 := bstep (se 2 (by rfl) ⟨1087143, by rfl⟩ : syracuseStep 2899049 = 2174287) B2174287
theorem B1932699 : Blo 1931435 1932699 := bstep (se 1 (by rfl) ⟨1449524, by rfl⟩ : syracuseStep 1932699 = 2899049) B2899049
theorem B4707085 : Blo 1931435 4707085 := bbase (se 3 (by rfl) ⟨882578, by rfl⟩ : syracuseStep 4707085 = 1765157) (by norm_num)
theorem B6276113 : Blo 1931435 6276113 := bstep (se 2 (by rfl) ⟨2353542, by rfl⟩ : syracuseStep 6276113 = 4707085) B4707085
theorem B4184075 : Blo 1931435 4184075 := bstep (se 1 (by rfl) ⟨3138056, by rfl⟩ : syracuseStep 4184075 = 6276113) B6276113
theorem B11157533 : Blo 1931435 11157533 := bstep (se 3 (by rfl) ⟨2092037, by rfl⟩ : syracuseStep 11157533 = 4184075) B4184075
theorem B7438355 : Blo 1931435 7438355 := bstep (se 1 (by rfl) ⟨5578766, by rfl⟩ : syracuseStep 7438355 = 11157533) B11157533
theorem B4958903 : Blo 1931435 4958903 := bstep (se 1 (by rfl) ⟨3719177, by rfl⟩ : syracuseStep 4958903 = 7438355) B7438355
theorem B13223741 : Blo 1931435 13223741 := bstep (se 3 (by rfl) ⟨2479451, by rfl⟩ : syracuseStep 13223741 = 4958903) B4958903
theorem B35263309 : Blo 1931435 35263309 := bstep (se 3 (by rfl) ⟨6611870, by rfl⟩ : syracuseStep 35263309 = 13223741) B13223741
theorem B47017745 : Blo 1931435 47017745 := bstep (se 2 (by rfl) ⟨17631654, by rfl⟩ : syracuseStep 47017745 = 35263309) B35263309
theorem B31345163 : Blo 1931435 31345163 := bstep (se 1 (by rfl) ⟨23508872, by rfl⟩ : syracuseStep 31345163 = 47017745) B47017745
theorem B20896775 : Blo 1931435 20896775 := bstep (se 1 (by rfl) ⟨15672581, by rfl⟩ : syracuseStep 20896775 = 31345163) B31345163
theorem B13931183 : Blo 1931435 13931183 := bstep (se 1 (by rfl) ⟨10448387, by rfl⟩ : syracuseStep 13931183 = 20896775) B20896775
theorem B9287455 : Blo 1931435 9287455 := bstep (se 1 (by rfl) ⟨6965591, by rfl⟩ : syracuseStep 9287455 = 13931183) B13931183
theorem B12383273 : Blo 1931435 12383273 := bstep (se 2 (by rfl) ⟨4643727, by rfl⟩ : syracuseStep 12383273 = 9287455) B9287455
theorem B8255515 : Blo 1931435 8255515 := bstep (se 1 (by rfl) ⟨6191636, by rfl⟩ : syracuseStep 8255515 = 12383273) B12383273
theorem B11007353 : Blo 1931435 11007353 := bstep (se 2 (by rfl) ⟨4127757, by rfl⟩ : syracuseStep 11007353 = 8255515) B8255515
theorem B7338235 : Blo 1931435 7338235 := bstep (se 1 (by rfl) ⟨5503676, by rfl⟩ : syracuseStep 7338235 = 11007353) B11007353
theorem B9784313 : Blo 1931435 9784313 := bstep (se 2 (by rfl) ⟨3669117, by rfl⟩ : syracuseStep 9784313 = 7338235) B7338235
theorem B6522875 : Blo 1931435 6522875 := bstep (se 1 (by rfl) ⟨4892156, by rfl⟩ : syracuseStep 6522875 = 9784313) B9784313
theorem B4348583 : Blo 1931435 4348583 := bstep (se 1 (by rfl) ⟨3261437, by rfl⟩ : syracuseStep 4348583 = 6522875) B6522875
theorem B2899055 : Blo 1931435 2899055 := bstep (se 1 (by rfl) ⟨2174291, by rfl⟩ : syracuseStep 2899055 = 4348583) B4348583
theorem B1932703 : Blo 1931435 1932703 := bstep (se 1 (by rfl) ⟨1449527, by rfl⟩ : syracuseStep 1932703 = 2899055) B2899055
theorem B2899061 : Blo 1931435 2899061 := bbase (se 5 (by rfl) ⟨135893, by rfl⟩ : syracuseStep 2899061 = 271787) (by norm_num)
theorem B1932707 : Blo 1931435 1932707 := bstep (se 1 (by rfl) ⟨1449530, by rfl⟩ : syracuseStep 1932707 = 2899061) B2899061
theorem B3669133 : Blo 1931435 3669133 := bbase (se 3 (by rfl) ⟨687962, by rfl⟩ : syracuseStep 3669133 = 1375925) (by norm_num)
theorem B4892177 : Blo 1931435 4892177 := bstep (se 2 (by rfl) ⟨1834566, by rfl⟩ : syracuseStep 4892177 = 3669133) B3669133
theorem B3261451 : Blo 1931435 3261451 := bstep (se 1 (by rfl) ⟨2446088, by rfl⟩ : syracuseStep 3261451 = 4892177) B4892177
theorem B4348601 : Blo 1931435 4348601 := bstep (se 2 (by rfl) ⟨1630725, by rfl⟩ : syracuseStep 4348601 = 3261451) B3261451
theorem B2899067 : Blo 1931435 2899067 := bstep (se 1 (by rfl) ⟨2174300, by rfl⟩ : syracuseStep 2899067 = 4348601) B4348601
theorem B1932711 : Blo 1931435 1932711 := bstep (se 1 (by rfl) ⟨1449533, by rfl⟩ : syracuseStep 1932711 = 2899067) B2899067
theorem B2174305 : Blo 1931435 2174305 := bbase (se 2 (by rfl) ⟨815364, by rfl⟩ : syracuseStep 2174305 = 1630729) (by norm_num)
theorem B2899073 : Blo 1931435 2899073 := bstep (se 2 (by rfl) ⟨1087152, by rfl⟩ : syracuseStep 2899073 = 2174305) B2174305
theorem B1932715 : Blo 1931435 1932715 := bstep (se 1 (by rfl) ⟨1449536, by rfl⟩ : syracuseStep 1932715 = 2899073) B2899073
theorem B4892197 : Blo 1931435 4892197 := bbase (se 4 (by rfl) ⟨458643, by rfl⟩ : syracuseStep 4892197 = 917287) (by norm_num)
theorem B6522929 : Blo 1931435 6522929 := bstep (se 2 (by rfl) ⟨2446098, by rfl⟩ : syracuseStep 6522929 = 4892197) B4892197
theorem B4348619 : Blo 1931435 4348619 := bstep (se 1 (by rfl) ⟨3261464, by rfl⟩ : syracuseStep 4348619 = 6522929) B6522929
theorem B2899079 : Blo 1931435 2899079 := bstep (se 1 (by rfl) ⟨2174309, by rfl⟩ : syracuseStep 2899079 = 4348619) B4348619
theorem B1932719 : Blo 1931435 1932719 := bstep (se 1 (by rfl) ⟨1449539, by rfl⟩ : syracuseStep 1932719 = 2899079) B2899079
theorem B2899085 : Blo 1931435 2899085 := bbase (se 3 (by rfl) ⟨543578, by rfl⟩ : syracuseStep 2899085 = 1087157) (by norm_num)
theorem B1932723 : Blo 1931435 1932723 := bstep (se 1 (by rfl) ⟨1449542, by rfl⟩ : syracuseStep 1932723 = 2899085) B2899085
theorem B4348637 : Blo 1931435 4348637 := bbase (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) (by norm_num)
theorem B2899091 : Blo 1931435 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B1932727 : Blo 1931435 1932727 := bstep (se 1 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 1932727 = 2899091) B2899091
theorem B3261485 : Blo 1931435 3261485 := bbase (se 3 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 3261485 = 1223057) (by norm_num)
theorem B2174323 : Blo 1931435 2174323 := bstep (se 1 (by rfl) ⟨1630742, by rfl⟩ : syracuseStep 2174323 = 3261485) B3261485
theorem B2899097 : Blo 1931435 2899097 := bstep (se 2 (by rfl) ⟨1087161, by rfl⟩ : syracuseStep 2899097 = 2174323) B2174323
theorem B1932731 : Blo 1931435 1932731 := bstep (se 1 (by rfl) ⟨1449548, by rfl⟩ : syracuseStep 1932731 = 2899097) B2899097
theorem B2789429 : Blo 1931435 2789429 := bbase (se 5 (by rfl) ⟨130754, by rfl⟩ : syracuseStep 2789429 = 261509) (by norm_num)
theorem B7438477 : Blo 1931435 7438477 := bstep (se 3 (by rfl) ⟨1394714, by rfl⟩ : syracuseStep 7438477 = 2789429) B2789429
theorem B9917969 : Blo 1931435 9917969 := bstep (se 2 (by rfl) ⟨3719238, by rfl⟩ : syracuseStep 9917969 = 7438477) B7438477
theorem B105791669 : Blo 1931435 105791669 := bstep (se 5 (by rfl) ⟨4958984, by rfl⟩ : syracuseStep 105791669 = 9917969) B9917969
theorem B70527779 : Blo 1931435 70527779 := bstep (se 1 (by rfl) ⟨52895834, by rfl⟩ : syracuseStep 70527779 = 105791669) B105791669
theorem B47018519 : Blo 1931435 47018519 := bstep (se 1 (by rfl) ⟨35263889, by rfl⟩ : syracuseStep 47018519 = 70527779) B70527779
theorem B31345679 : Blo 1931435 31345679 := bstep (se 1 (by rfl) ⟨23509259, by rfl⟩ : syracuseStep 31345679 = 47018519) B47018519
theorem B20897119 : Blo 1931435 20897119 := bstep (se 1 (by rfl) ⟨15672839, by rfl⟩ : syracuseStep 20897119 = 31345679) B31345679
theorem B27862825 : Blo 1931435 27862825 := bstep (se 2 (by rfl) ⟨10448559, by rfl⟩ : syracuseStep 27862825 = 20897119) B20897119
theorem B37150433 : Blo 1931435 37150433 := bstep (se 2 (by rfl) ⟨13931412, by rfl⟩ : syracuseStep 37150433 = 27862825) B27862825
theorem B24766955 : Blo 1931435 24766955 := bstep (se 1 (by rfl) ⟨18575216, by rfl⟩ : syracuseStep 24766955 = 37150433) B37150433
theorem B16511303 : Blo 1931435 16511303 := bstep (se 1 (by rfl) ⟨12383477, by rfl⟩ : syracuseStep 16511303 = 24766955) B24766955
theorem B11007535 : Blo 1931435 11007535 := bstep (se 1 (by rfl) ⟨8255651, by rfl⟩ : syracuseStep 11007535 = 16511303) B16511303
theorem B14676713 : Blo 1931435 14676713 := bstep (se 2 (by rfl) ⟨5503767, by rfl⟩ : syracuseStep 14676713 = 11007535) B11007535
theorem B9784475 : Blo 1931435 9784475 := bstep (se 1 (by rfl) ⟨7338356, by rfl⟩ : syracuseStep 9784475 = 14676713) B14676713
theorem B6522983 : Blo 1931435 6522983 := bstep (se 1 (by rfl) ⟨4892237, by rfl⟩ : syracuseStep 6522983 = 9784475) B9784475
theorem B4348655 : Blo 1931435 4348655 := bstep (se 1 (by rfl) ⟨3261491, by rfl⟩ : syracuseStep 4348655 = 6522983) B6522983
theorem B2899103 : Blo 1931435 2899103 := bstep (se 1 (by rfl) ⟨2174327, by rfl⟩ : syracuseStep 2899103 = 4348655) B4348655
theorem B1932735 : Blo 1931435 1932735 := bstep (se 1 (by rfl) ⟨1449551, by rfl⟩ : syracuseStep 1932735 = 2899103) B2899103
theorem B2899109 : Blo 1931435 2899109 := bbase (se 4 (by rfl) ⟨271791, by rfl⟩ : syracuseStep 2899109 = 543583) (by norm_num)
theorem B1932739 : Blo 1931435 1932739 := bstep (se 1 (by rfl) ⟨1449554, by rfl⟩ : syracuseStep 1932739 = 2899109) B2899109
theorem B2446129 : Blo 1931435 2446129 := bbase (se 2 (by rfl) ⟨917298, by rfl⟩ : syracuseStep 2446129 = 1834597) (by norm_num)
theorem B3261505 : Blo 1931435 3261505 := bstep (se 2 (by rfl) ⟨1223064, by rfl⟩ : syracuseStep 3261505 = 2446129) B2446129
theorem B4348673 : Blo 1931435 4348673 := bstep (se 2 (by rfl) ⟨1630752, by rfl⟩ : syracuseStep 4348673 = 3261505) B3261505
theorem B2899115 : Blo 1931435 2899115 := bstep (se 1 (by rfl) ⟨2174336, by rfl⟩ : syracuseStep 2899115 = 4348673) B4348673
theorem B1932743 : Blo 1931435 1932743 := bstep (se 1 (by rfl) ⟨1449557, by rfl⟩ : syracuseStep 1932743 = 2899115) B2899115
theorem B2174341 : Blo 1931435 2174341 := bbase (se 4 (by rfl) ⟨203844, by rfl⟩ : syracuseStep 2174341 = 407689) (by norm_num)
theorem B2899121 : Blo 1931435 2899121 := bstep (se 2 (by rfl) ⟨1087170, by rfl⟩ : syracuseStep 2899121 = 2174341) B2174341
theorem B1932747 : Blo 1931435 1932747 := bstep (se 1 (by rfl) ⟨1449560, by rfl⟩ : syracuseStep 1932747 = 2899121) B2899121
theorem B4127861 : Blo 1931435 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B2751907 : Blo 1931435 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B3669209 : Blo 1931435 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B2446139 : Blo 1931435 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B6523037 : Blo 1931435 6523037 := bstep (se 3 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 6523037 = 2446139) B2446139
theorem B4348691 : Blo 1931435 4348691 := bstep (se 1 (by rfl) ⟨3261518, by rfl⟩ : syracuseStep 4348691 = 6523037) B6523037
theorem B2899127 : Blo 1931435 2899127 := bstep (se 1 (by rfl) ⟨2174345, by rfl⟩ : syracuseStep 2899127 = 4348691) B4348691
theorem B1932751 : Blo 1931435 1932751 := bstep (se 1 (by rfl) ⟨1449563, by rfl⟩ : syracuseStep 1932751 = 2899127) B2899127
theorem B2899133 : Blo 1931435 2899133 := bbase (se 3 (by rfl) ⟨543587, by rfl⟩ : syracuseStep 2899133 = 1087175) (by norm_num)
theorem B1932755 : Blo 1931435 1932755 := bstep (se 1 (by rfl) ⟨1449566, by rfl⟩ : syracuseStep 1932755 = 2899133) B2899133
theorem B4348709 : Blo 1931435 4348709 := bbase (se 4 (by rfl) ⟨407691, by rfl⟩ : syracuseStep 4348709 = 815383) (by norm_num)
theorem B2899139 : Blo 1931435 2899139 := bstep (se 1 (by rfl) ⟨2174354, by rfl⟩ : syracuseStep 2899139 = 4348709) B4348709
theorem B1932759 : Blo 1931435 1932759 := bstep (se 1 (by rfl) ⟨1449569, by rfl⟩ : syracuseStep 1932759 = 2899139) B2899139
theorem B4892309 : Blo 1931435 4892309 := bbase (se 6 (by rfl) ⟨114663, by rfl⟩ : syracuseStep 4892309 = 229327) (by norm_num)
theorem B3261539 : Blo 1931435 3261539 := bstep (se 1 (by rfl) ⟨2446154, by rfl⟩ : syracuseStep 3261539 = 4892309) B4892309
theorem B2174359 : Blo 1931435 2174359 := bstep (se 1 (by rfl) ⟨1630769, by rfl⟩ : syracuseStep 2174359 = 3261539) B3261539
theorem B2899145 : Blo 1931435 2899145 := bstep (se 2 (by rfl) ⟨1087179, by rfl⟩ : syracuseStep 2899145 = 2174359) B2174359
theorem B1932763 : Blo 1931435 1932763 := bstep (se 1 (by rfl) ⟨1449572, by rfl⟩ : syracuseStep 1932763 = 2899145) B2899145
theorem B2321941 : Blo 1931435 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B3095921 : Blo 1931435 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B8255789 : Blo 1931435 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B5503859 : Blo 1931435 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B3669239 : Blo 1931435 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B9784637 : Blo 1931435 9784637 := bstep (se 3 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 9784637 = 3669239) B3669239
theorem B6523091 : Blo 1931435 6523091 := bstep (se 1 (by rfl) ⟨4892318, by rfl⟩ : syracuseStep 6523091 = 9784637) B9784637
theorem B4348727 : Blo 1931435 4348727 := bstep (se 1 (by rfl) ⟨3261545, by rfl⟩ : syracuseStep 4348727 = 6523091) B6523091
theorem B2899151 : Blo 1931435 2899151 := bstep (se 1 (by rfl) ⟨2174363, by rfl⟩ : syracuseStep 2899151 = 4348727) B4348727
theorem B1932767 : Blo 1931435 1932767 := bstep (se 1 (by rfl) ⟨1449575, by rfl⟩ : syracuseStep 1932767 = 2899151) B2899151
theorem B2899157 : Blo 1931435 2899157 := bbase (se 7 (by rfl) ⟨33974, by rfl⟩ : syracuseStep 2899157 = 67949) (by norm_num)
theorem B1932771 : Blo 1931435 1932771 := bstep (se 1 (by rfl) ⟨1449578, by rfl⟩ : syracuseStep 1932771 = 2899157) B2899157
theorem B2751941 : Blo 1931435 2751941 := bbase (se 4 (by rfl) ⟨257994, by rfl⟩ : syracuseStep 2751941 = 515989) (by norm_num)
theorem B7338509 : Blo 1931435 7338509 := bstep (se 3 (by rfl) ⟨1375970, by rfl⟩ : syracuseStep 7338509 = 2751941) B2751941
theorem B4892339 : Blo 1931435 4892339 := bstep (se 1 (by rfl) ⟨3669254, by rfl⟩ : syracuseStep 4892339 = 7338509) B7338509
theorem B3261559 : Blo 1931435 3261559 := bstep (se 1 (by rfl) ⟨2446169, by rfl⟩ : syracuseStep 3261559 = 4892339) B4892339
theorem B4348745 : Blo 1931435 4348745 := bstep (se 2 (by rfl) ⟨1630779, by rfl⟩ : syracuseStep 4348745 = 3261559) B3261559
theorem B2899163 : Blo 1931435 2899163 := bstep (se 1 (by rfl) ⟨2174372, by rfl⟩ : syracuseStep 2899163 = 4348745) B4348745
theorem B1932775 : Blo 1931435 1932775 := bstep (se 1 (by rfl) ⟨1449581, by rfl⟩ : syracuseStep 1932775 = 2899163) B2899163
theorem B2174377 : Blo 1931435 2174377 := bbase (se 2 (by rfl) ⟨815391, by rfl⟩ : syracuseStep 2174377 = 1630783) (by norm_num)
theorem B2899169 : Blo 1931435 2899169 := bstep (se 2 (by rfl) ⟨1087188, by rfl⟩ : syracuseStep 2899169 = 2174377) B2174377
theorem B1932779 : Blo 1931435 1932779 := bstep (se 1 (by rfl) ⟨1449584, by rfl⟩ : syracuseStep 1932779 = 2899169) B2899169
theorem B6191893 : Blo 1931435 6191893 := bbase (se 6 (by rfl) ⟨145122, by rfl⟩ : syracuseStep 6191893 = 290245) (by norm_num)
theorem B8255857 : Blo 1931435 8255857 := bstep (se 2 (by rfl) ⟨3095946, by rfl⟩ : syracuseStep 8255857 = 6191893) B6191893
theorem B11007809 : Blo 1931435 11007809 := bstep (se 2 (by rfl) ⟨4127928, by rfl⟩ : syracuseStep 11007809 = 8255857) B8255857
theorem B7338539 : Blo 1931435 7338539 := bstep (se 1 (by rfl) ⟨5503904, by rfl⟩ : syracuseStep 7338539 = 11007809) B11007809
theorem B4892359 : Blo 1931435 4892359 := bstep (se 1 (by rfl) ⟨3669269, by rfl⟩ : syracuseStep 4892359 = 7338539) B7338539
theorem B6523145 : Blo 1931435 6523145 := bstep (se 2 (by rfl) ⟨2446179, by rfl⟩ : syracuseStep 6523145 = 4892359) B4892359
theorem B4348763 : Blo 1931435 4348763 := bstep (se 1 (by rfl) ⟨3261572, by rfl⟩ : syracuseStep 4348763 = 6523145) B6523145
theorem B2899175 : Blo 1931435 2899175 := bstep (se 1 (by rfl) ⟨2174381, by rfl⟩ : syracuseStep 2899175 = 4348763) B4348763
theorem B1932783 : Blo 1931435 1932783 := bstep (se 1 (by rfl) ⟨1449587, by rfl⟩ : syracuseStep 1932783 = 2899175) B2899175
theorem B2899181 : Blo 1931435 2899181 := bbase (se 3 (by rfl) ⟨543596, by rfl⟩ : syracuseStep 2899181 = 1087193) (by norm_num)
theorem B1932787 : Blo 1931435 1932787 := bstep (se 1 (by rfl) ⟨1449590, by rfl⟩ : syracuseStep 1932787 = 2899181) B2899181
theorem B4348781 : Blo 1931435 4348781 := bbase (se 3 (by rfl) ⟨815396, by rfl⟩ : syracuseStep 4348781 = 1630793) (by norm_num)
theorem B2899187 : Blo 1931435 2899187 := bstep (se 1 (by rfl) ⟨2174390, by rfl⟩ : syracuseStep 2899187 = 4348781) B4348781
theorem B1932791 : Blo 1931435 1932791 := bstep (se 1 (by rfl) ⟨1449593, by rfl⟩ : syracuseStep 1932791 = 2899187) B2899187
theorem B3669293 : Blo 1931435 3669293 := bbase (se 3 (by rfl) ⟨687992, by rfl⟩ : syracuseStep 3669293 = 1375985) (by norm_num)
theorem B2446195 : Blo 1931435 2446195 := bstep (se 1 (by rfl) ⟨1834646, by rfl⟩ : syracuseStep 2446195 = 3669293) B3669293
theorem B3261593 : Blo 1931435 3261593 := bstep (se 2 (by rfl) ⟨1223097, by rfl⟩ : syracuseStep 3261593 = 2446195) B2446195
theorem B2174395 : Blo 1931435 2174395 := bstep (se 1 (by rfl) ⟨1630796, by rfl⟩ : syracuseStep 2174395 = 3261593) B3261593
theorem B2899193 : Blo 1931435 2899193 := bstep (se 2 (by rfl) ⟨1087197, by rfl⟩ : syracuseStep 2899193 = 2174395) B2174395
theorem B1932795 : Blo 1931435 1932795 := bstep (se 1 (by rfl) ⟨1449596, by rfl⟩ : syracuseStep 1932795 = 2899193) B2899193
theorem B4959149 : Blo 1931435 4959149 := bbase (se 3 (by rfl) ⟨929840, by rfl⟩ : syracuseStep 4959149 = 1859681) (by norm_num)
theorem B13224397 : Blo 1931435 13224397 := bstep (se 3 (by rfl) ⟨2479574, by rfl⟩ : syracuseStep 13224397 = 4959149) B4959149
theorem B17632529 : Blo 1931435 17632529 := bstep (se 2 (by rfl) ⟨6612198, by rfl⟩ : syracuseStep 17632529 = 13224397) B13224397
theorem B11755019 : Blo 1931435 11755019 := bstep (se 1 (by rfl) ⟨8816264, by rfl⟩ : syracuseStep 11755019 = 17632529) B17632529
theorem B7836679 : Blo 1931435 7836679 := bstep (se 1 (by rfl) ⟨5877509, by rfl⟩ : syracuseStep 7836679 = 11755019) B11755019
theorem B41795621 : Blo 1931435 41795621 := bstep (se 4 (by rfl) ⟨3918339, by rfl⟩ : syracuseStep 41795621 = 7836679) B7836679
theorem B27863747 : Blo 1931435 27863747 := bstep (se 1 (by rfl) ⟨20897810, by rfl⟩ : syracuseStep 27863747 = 41795621) B41795621
theorem B18575831 : Blo 1931435 18575831 := bstep (se 1 (by rfl) ⟨13931873, by rfl⟩ : syracuseStep 18575831 = 27863747) B27863747
theorem B49535549 : Blo 1931435 49535549 := bstep (se 3 (by rfl) ⟨9287915, by rfl⟩ : syracuseStep 49535549 = 18575831) B18575831
theorem B33023699 : Blo 1931435 33023699 := bstep (se 1 (by rfl) ⟨24767774, by rfl⟩ : syracuseStep 33023699 = 49535549) B49535549
theorem B22015799 : Blo 1931435 22015799 := bstep (se 1 (by rfl) ⟨16511849, by rfl⟩ : syracuseStep 22015799 = 33023699) B33023699
theorem B14677199 : Blo 1931435 14677199 := bstep (se 1 (by rfl) ⟨11007899, by rfl⟩ : syracuseStep 14677199 = 22015799) B22015799
theorem B9784799 : Blo 1931435 9784799 := bstep (se 1 (by rfl) ⟨7338599, by rfl⟩ : syracuseStep 9784799 = 14677199) B14677199
theorem B6523199 : Blo 1931435 6523199 := bstep (se 1 (by rfl) ⟨4892399, by rfl⟩ : syracuseStep 6523199 = 9784799) B9784799
theorem B4348799 : Blo 1931435 4348799 := bstep (se 1 (by rfl) ⟨3261599, by rfl⟩ : syracuseStep 4348799 = 6523199) B6523199
theorem B2899199 : Blo 1931435 2899199 := bstep (se 1 (by rfl) ⟨2174399, by rfl⟩ : syracuseStep 2899199 = 4348799) B4348799
theorem B1932799 : Blo 1931435 1932799 := bstep (se 1 (by rfl) ⟨1449599, by rfl⟩ : syracuseStep 1932799 = 2899199) B2899199
theorem B2899205 : Blo 1931435 2899205 := bbase (se 4 (by rfl) ⟨271800, by rfl⟩ : syracuseStep 2899205 = 543601) (by norm_num)
theorem B1932803 : Blo 1931435 1932803 := bstep (se 1 (by rfl) ⟨1449602, by rfl⟩ : syracuseStep 1932803 = 2899205) B2899205
theorem B3261613 : Blo 1931435 3261613 := bbase (se 3 (by rfl) ⟨611552, by rfl⟩ : syracuseStep 3261613 = 1223105) (by norm_num)
theorem B4348817 : Blo 1931435 4348817 := bstep (se 2 (by rfl) ⟨1630806, by rfl⟩ : syracuseStep 4348817 = 3261613) B3261613
theorem B2899211 : Blo 1931435 2899211 := bstep (se 1 (by rfl) ⟨2174408, by rfl⟩ : syracuseStep 2899211 = 4348817) B4348817
theorem B1932807 : Blo 1931435 1932807 := bstep (se 1 (by rfl) ⟨1449605, by rfl⟩ : syracuseStep 1932807 = 2899211) B2899211
theorem B2174413 : Blo 1931435 2174413 := bbase (se 3 (by rfl) ⟨407702, by rfl⟩ : syracuseStep 2174413 = 815405) (by norm_num)
theorem B2899217 : Blo 1931435 2899217 := bstep (se 2 (by rfl) ⟨1087206, by rfl⟩ : syracuseStep 2899217 = 2174413) B2174413
theorem B1932811 : Blo 1931435 1932811 := bstep (se 1 (by rfl) ⟨1449608, by rfl⟩ : syracuseStep 1932811 = 2899217) B2899217
theorem B6523253 : Blo 1931435 6523253 := bbase (se 5 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 6523253 = 611555) (by norm_num)
theorem B4348835 : Blo 1931435 4348835 := bstep (se 1 (by rfl) ⟨3261626, by rfl⟩ : syracuseStep 4348835 = 6523253) B6523253
theorem B2899223 : Blo 1931435 2899223 := bstep (se 1 (by rfl) ⟨2174417, by rfl⟩ : syracuseStep 2899223 = 4348835) B4348835
theorem B1932815 : Blo 1931435 1932815 := bstep (se 1 (by rfl) ⟨1449611, by rfl⟩ : syracuseStep 1932815 = 2899223) B2899223
theorem B2899229 : Blo 1931435 2899229 := bbase (se 3 (by rfl) ⟨543605, by rfl⟩ : syracuseStep 2899229 = 1087211) (by norm_num)
theorem B1932819 : Blo 1931435 1932819 := bstep (se 1 (by rfl) ⟨1449614, by rfl⟩ : syracuseStep 1932819 = 2899229) B2899229
theorem B4348853 : Blo 1931435 4348853 := bbase (se 5 (by rfl) ⟨203852, by rfl⟩ : syracuseStep 4348853 = 407705) (by norm_num)
theorem B2899235 : Blo 1931435 2899235 := bstep (se 1 (by rfl) ⟨2174426, by rfl⟩ : syracuseStep 2899235 = 4348853) B4348853
theorem B1932823 : Blo 1931435 1932823 := bstep (se 1 (by rfl) ⟨1449617, by rfl⟩ : syracuseStep 1932823 = 2899235) B2899235
theorem B9288053 : Blo 1931435 9288053 := bbase (se 5 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 9288053 = 870755) (by norm_num)
theorem B6192035 : Blo 1931435 6192035 := bstep (se 1 (by rfl) ⟨4644026, by rfl⟩ : syracuseStep 6192035 = 9288053) B9288053
theorem B4128023 : Blo 1931435 4128023 := bstep (se 1 (by rfl) ⟨3096017, by rfl⟩ : syracuseStep 4128023 = 6192035) B6192035
theorem B11008061 : Blo 1931435 11008061 := bstep (se 3 (by rfl) ⟨2064011, by rfl⟩ : syracuseStep 11008061 = 4128023) B4128023
theorem B7338707 : Blo 1931435 7338707 := bstep (se 1 (by rfl) ⟨5504030, by rfl⟩ : syracuseStep 7338707 = 11008061) B11008061
theorem B4892471 : Blo 1931435 4892471 := bstep (se 1 (by rfl) ⟨3669353, by rfl⟩ : syracuseStep 4892471 = 7338707) B7338707
theorem B3261647 : Blo 1931435 3261647 := bstep (se 1 (by rfl) ⟨2446235, by rfl⟩ : syracuseStep 3261647 = 4892471) B4892471
theorem B2174431 : Blo 1931435 2174431 := bstep (se 1 (by rfl) ⟨1630823, by rfl⟩ : syracuseStep 2174431 = 3261647) B3261647
theorem B2899241 : Blo 1931435 2899241 := bstep (se 2 (by rfl) ⟨1087215, by rfl⟩ : syracuseStep 2899241 = 2174431) B2174431
theorem B1932827 : Blo 1931435 1932827 := bstep (se 1 (by rfl) ⟨1449620, by rfl⟩ : syracuseStep 1932827 = 2899241) B2899241
theorem B15673621 : Blo 1931435 15673621 := bbase (se 6 (by rfl) ⟨367350, by rfl⟩ : syracuseStep 15673621 = 734701) (by norm_num)
theorem B20898161 : Blo 1931435 20898161 := bstep (se 2 (by rfl) ⟨7836810, by rfl⟩ : syracuseStep 20898161 = 15673621) B15673621
theorem B13932107 : Blo 1931435 13932107 := bstep (se 1 (by rfl) ⟨10449080, by rfl⟩ : syracuseStep 13932107 = 20898161) B20898161
theorem B9288071 : Blo 1931435 9288071 := bstep (se 1 (by rfl) ⟨6966053, by rfl⟩ : syracuseStep 9288071 = 13932107) B13932107
theorem B6192047 : Blo 1931435 6192047 := bstep (se 1 (by rfl) ⟨4644035, by rfl⟩ : syracuseStep 6192047 = 9288071) B9288071
theorem B4128031 : Blo 1931435 4128031 := bstep (se 1 (by rfl) ⟨3096023, by rfl⟩ : syracuseStep 4128031 = 6192047) B6192047
theorem B5504041 : Blo 1931435 5504041 := bstep (se 2 (by rfl) ⟨2064015, by rfl⟩ : syracuseStep 5504041 = 4128031) B4128031
theorem B7338721 : Blo 1931435 7338721 := bstep (se 2 (by rfl) ⟨2752020, by rfl⟩ : syracuseStep 7338721 = 5504041) B5504041
theorem B9784961 : Blo 1931435 9784961 := bstep (se 2 (by rfl) ⟨3669360, by rfl⟩ : syracuseStep 9784961 = 7338721) B7338721
theorem B6523307 : Blo 1931435 6523307 := bstep (se 1 (by rfl) ⟨4892480, by rfl⟩ : syracuseStep 6523307 = 9784961) B9784961
theorem B4348871 : Blo 1931435 4348871 := bstep (se 1 (by rfl) ⟨3261653, by rfl⟩ : syracuseStep 4348871 = 6523307) B6523307
theorem B2899247 : Blo 1931435 2899247 := bstep (se 1 (by rfl) ⟨2174435, by rfl⟩ : syracuseStep 2899247 = 4348871) B4348871
theorem B1932831 : Blo 1931435 1932831 := bstep (se 1 (by rfl) ⟨1449623, by rfl⟩ : syracuseStep 1932831 = 2899247) B2899247
theorem B2899253 : Blo 1931435 2899253 := bbase (se 5 (by rfl) ⟨135902, by rfl⟩ : syracuseStep 2899253 = 271805) (by norm_num)
theorem B1932835 : Blo 1931435 1932835 := bstep (se 1 (by rfl) ⟨1449626, by rfl⟩ : syracuseStep 1932835 = 2899253) B2899253
theorem B4892501 : Blo 1931435 4892501 := bbase (se 9 (by rfl) ⟨14333, by rfl⟩ : syracuseStep 4892501 = 28667) (by norm_num)
theorem B3261667 : Blo 1931435 3261667 := bstep (se 1 (by rfl) ⟨2446250, by rfl⟩ : syracuseStep 3261667 = 4892501) B4892501
theorem B4348889 : Blo 1931435 4348889 := bstep (se 2 (by rfl) ⟨1630833, by rfl⟩ : syracuseStep 4348889 = 3261667) B3261667
theorem B2899259 : Blo 1931435 2899259 := bstep (se 1 (by rfl) ⟨2174444, by rfl⟩ : syracuseStep 2899259 = 4348889) B4348889
theorem B1932839 : Blo 1931435 1932839 := bstep (se 1 (by rfl) ⟨1449629, by rfl⟩ : syracuseStep 1932839 = 2899259) B2899259
theorem B2174449 : Blo 1931435 2174449 := bbase (se 2 (by rfl) ⟨815418, by rfl⟩ : syracuseStep 2174449 = 1630837) (by norm_num)
theorem B2899265 : Blo 1931435 2899265 := bstep (se 2 (by rfl) ⟨1087224, by rfl⟩ : syracuseStep 2899265 = 2174449) B2174449
theorem B1932843 : Blo 1931435 1932843 := bstep (se 1 (by rfl) ⟨1449632, by rfl⟩ : syracuseStep 1932843 = 2899265) B2899265
theorem B2322037 : Blo 1931435 2322037 := bbase (se 5 (by rfl) ⟨108845, by rfl⟩ : syracuseStep 2322037 = 217691) (by norm_num)
theorem B12384197 : Blo 1931435 12384197 := bstep (se 4 (by rfl) ⟨1161018, by rfl⟩ : syracuseStep 12384197 = 2322037) B2322037
theorem B8256131 : Blo 1931435 8256131 := bstep (se 1 (by rfl) ⟨6192098, by rfl⟩ : syracuseStep 8256131 = 12384197) B12384197
theorem B5504087 : Blo 1931435 5504087 := bstep (se 1 (by rfl) ⟨4128065, by rfl⟩ : syracuseStep 5504087 = 8256131) B8256131
theorem B3669391 : Blo 1931435 3669391 := bstep (se 1 (by rfl) ⟨2752043, by rfl⟩ : syracuseStep 3669391 = 5504087) B5504087
theorem B4892521 : Blo 1931435 4892521 := bstep (se 2 (by rfl) ⟨1834695, by rfl⟩ : syracuseStep 4892521 = 3669391) B3669391
theorem B6523361 : Blo 1931435 6523361 := bstep (se 2 (by rfl) ⟨2446260, by rfl⟩ : syracuseStep 6523361 = 4892521) B4892521
theorem B4348907 : Blo 1931435 4348907 := bstep (se 1 (by rfl) ⟨3261680, by rfl⟩ : syracuseStep 4348907 = 6523361) B6523361
theorem B2899271 : Blo 1931435 2899271 := bstep (se 1 (by rfl) ⟨2174453, by rfl⟩ : syracuseStep 2899271 = 4348907) B4348907
theorem B1932847 : Blo 1931435 1932847 := bstep (se 1 (by rfl) ⟨1449635, by rfl⟩ : syracuseStep 1932847 = 2899271) B2899271
theorem B2899277 : Blo 1931435 2899277 := bbase (se 3 (by rfl) ⟨543614, by rfl⟩ : syracuseStep 2899277 = 1087229) (by norm_num)
theorem B1932851 : Blo 1931435 1932851 := bstep (se 1 (by rfl) ⟨1449638, by rfl⟩ : syracuseStep 1932851 = 2899277) B2899277
theorem B4348925 : Blo 1931435 4348925 := bbase (se 3 (by rfl) ⟨815423, by rfl⟩ : syracuseStep 4348925 = 1630847) (by norm_num)
theorem B2899283 : Blo 1931435 2899283 := bstep (se 1 (by rfl) ⟨2174462, by rfl⟩ : syracuseStep 2899283 = 4348925) B4348925
theorem B1932855 : Blo 1931435 1932855 := bstep (se 1 (by rfl) ⟨1449641, by rfl⟩ : syracuseStep 1932855 = 2899283) B2899283
theorem B3261701 : Blo 1931435 3261701 := bbase (se 4 (by rfl) ⟨305784, by rfl⟩ : syracuseStep 3261701 = 611569) (by norm_num)
theorem B2174467 : Blo 1931435 2174467 := bstep (se 1 (by rfl) ⟨1630850, by rfl⟩ : syracuseStep 2174467 = 3261701) B3261701
theorem B2899289 : Blo 1931435 2899289 := bstep (se 2 (by rfl) ⟨1087233, by rfl⟩ : syracuseStep 2899289 = 2174467) B2174467
theorem B1932859 : Blo 1931435 1932859 := bstep (se 1 (by rfl) ⟨1449644, by rfl⟩ : syracuseStep 1932859 = 2899289) B2899289
theorem B14677685 : Blo 1931435 14677685 := bbase (se 5 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 14677685 = 1376033) (by norm_num)
theorem B9785123 : Blo 1931435 9785123 := bstep (se 1 (by rfl) ⟨7338842, by rfl⟩ : syracuseStep 9785123 = 14677685) B14677685
theorem B6523415 : Blo 1931435 6523415 := bstep (se 1 (by rfl) ⟨4892561, by rfl⟩ : syracuseStep 6523415 = 9785123) B9785123
theorem B4348943 : Blo 1931435 4348943 := bstep (se 1 (by rfl) ⟨3261707, by rfl⟩ : syracuseStep 4348943 = 6523415) B6523415
theorem B2899295 : Blo 1931435 2899295 := bstep (se 1 (by rfl) ⟨2174471, by rfl⟩ : syracuseStep 2899295 = 4348943) B4348943
theorem B1932863 : Blo 1931435 1932863 := bstep (se 1 (by rfl) ⟨1449647, by rfl⟩ : syracuseStep 1932863 = 2899295) B2899295
theorem B2899301 : Blo 1931435 2899301 := bbase (se 4 (by rfl) ⟨271809, by rfl⟩ : syracuseStep 2899301 = 543619) (by norm_num)
theorem B1932867 : Blo 1931435 1932867 := bstep (se 1 (by rfl) ⟨1449650, by rfl⟩ : syracuseStep 1932867 = 2899301) B2899301
theorem B3669437 : Blo 1931435 3669437 := bbase (se 3 (by rfl) ⟨688019, by rfl⟩ : syracuseStep 3669437 = 1376039) (by norm_num)
theorem B2446291 : Blo 1931435 2446291 := bstep (se 1 (by rfl) ⟨1834718, by rfl⟩ : syracuseStep 2446291 = 3669437) B3669437
theorem B3261721 : Blo 1931435 3261721 := bstep (se 2 (by rfl) ⟨1223145, by rfl⟩ : syracuseStep 3261721 = 2446291) B2446291
theorem B4348961 : Blo 1931435 4348961 := bstep (se 2 (by rfl) ⟨1630860, by rfl⟩ : syracuseStep 4348961 = 3261721) B3261721
theorem B2899307 : Blo 1931435 2899307 := bstep (se 1 (by rfl) ⟨2174480, by rfl⟩ : syracuseStep 2899307 = 4348961) B4348961
theorem B1932871 : Blo 1931435 1932871 := bstep (se 1 (by rfl) ⟨1449653, by rfl⟩ : syracuseStep 1932871 = 2899307) B2899307
theorem B2174485 : Blo 1931435 2174485 := bbase (se 6 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 2174485 = 101929) (by norm_num)
theorem B2899313 : Blo 1931435 2899313 := bstep (se 2 (by rfl) ⟨1087242, by rfl⟩ : syracuseStep 2899313 = 2174485) B2174485
theorem B1932875 : Blo 1931435 1932875 := bstep (se 1 (by rfl) ⟨1449656, by rfl⟩ : syracuseStep 1932875 = 2899313) B2899313
theorem B2446301 : Blo 1931435 2446301 := bbase (se 3 (by rfl) ⟨458681, by rfl⟩ : syracuseStep 2446301 = 917363) (by norm_num)
theorem B6523469 : Blo 1931435 6523469 := bstep (se 3 (by rfl) ⟨1223150, by rfl⟩ : syracuseStep 6523469 = 2446301) B2446301
theorem B4348979 : Blo 1931435 4348979 := bstep (se 1 (by rfl) ⟨3261734, by rfl⟩ : syracuseStep 4348979 = 6523469) B6523469
theorem B2899319 : Blo 1931435 2899319 := bstep (se 1 (by rfl) ⟨2174489, by rfl⟩ : syracuseStep 2899319 = 4348979) B4348979
theorem B1932879 : Blo 1931435 1932879 := bstep (se 1 (by rfl) ⟨1449659, by rfl⟩ : syracuseStep 1932879 = 2899319) B2899319
theorem B2899325 : Blo 1931435 2899325 := bbase (se 3 (by rfl) ⟨543623, by rfl⟩ : syracuseStep 2899325 = 1087247) (by norm_num)
theorem B1932883 : Blo 1931435 1932883 := bstep (se 1 (by rfl) ⟨1449662, by rfl⟩ : syracuseStep 1932883 = 2899325) B2899325
theorem B4348997 : Blo 1931435 4348997 := bbase (se 4 (by rfl) ⟨407718, by rfl⟩ : syracuseStep 4348997 = 815437) (by norm_num)
theorem B2899331 : Blo 1931435 2899331 := bstep (se 1 (by rfl) ⟨2174498, by rfl⟩ : syracuseStep 2899331 = 4348997) B4348997
theorem B1932887 : Blo 1931435 1932887 := bstep (se 1 (by rfl) ⟨1449665, by rfl⟩ : syracuseStep 1932887 = 2899331) B2899331
theorem B5504213 : Blo 1931435 5504213 := bbase (se 7 (by rfl) ⟨64502, by rfl⟩ : syracuseStep 5504213 = 129005) (by norm_num)
theorem B3669475 : Blo 1931435 3669475 := bstep (se 1 (by rfl) ⟨2752106, by rfl⟩ : syracuseStep 3669475 = 5504213) B5504213
theorem B4892633 : Blo 1931435 4892633 := bstep (se 2 (by rfl) ⟨1834737, by rfl⟩ : syracuseStep 4892633 = 3669475) B3669475
theorem B3261755 : Blo 1931435 3261755 := bstep (se 1 (by rfl) ⟨2446316, by rfl⟩ : syracuseStep 3261755 = 4892633) B4892633
theorem B2174503 : Blo 1931435 2174503 := bstep (se 1 (by rfl) ⟨1630877, by rfl⟩ : syracuseStep 2174503 = 3261755) B3261755
theorem B2899337 : Blo 1931435 2899337 := bstep (se 2 (by rfl) ⟨1087251, by rfl⟩ : syracuseStep 2899337 = 2174503) B2174503
theorem B1932891 : Blo 1931435 1932891 := bstep (se 1 (by rfl) ⟨1449668, by rfl⟩ : syracuseStep 1932891 = 2899337) B2899337
theorem B9785285 : Blo 1931435 9785285 := bbase (se 4 (by rfl) ⟨917370, by rfl⟩ : syracuseStep 9785285 = 1834741) (by norm_num)
theorem B6523523 : Blo 1931435 6523523 := bstep (se 1 (by rfl) ⟨4892642, by rfl⟩ : syracuseStep 6523523 = 9785285) B9785285
theorem B4349015 : Blo 1931435 4349015 := bstep (se 1 (by rfl) ⟨3261761, by rfl⟩ : syracuseStep 4349015 = 6523523) B6523523
theorem B2899343 : Blo 1931435 2899343 := bstep (se 1 (by rfl) ⟨2174507, by rfl⟩ : syracuseStep 2899343 = 4349015) B4349015
theorem B1932895 : Blo 1931435 1932895 := bstep (se 1 (by rfl) ⟨1449671, by rfl⟩ : syracuseStep 1932895 = 2899343) B2899343
theorem B2899349 : Blo 1931435 2899349 := bbase (se 6 (by rfl) ⟨67953, by rfl⟩ : syracuseStep 2899349 = 135907) (by norm_num)
theorem B1932899 : Blo 1931435 1932899 := bstep (se 1 (by rfl) ⟨1449674, by rfl⟩ : syracuseStep 1932899 = 2899349) B2899349
theorem B3483157 : Blo 1931435 3483157 := bbase (se 6 (by rfl) ⟨81636, by rfl⟩ : syracuseStep 3483157 = 163273) (by norm_num)
theorem B4644209 : Blo 1931435 4644209 := bstep (se 2 (by rfl) ⟨1741578, by rfl⟩ : syracuseStep 4644209 = 3483157) B3483157
theorem B3096139 : Blo 1931435 3096139 := bstep (se 1 (by rfl) ⟨2322104, by rfl⟩ : syracuseStep 3096139 = 4644209) B4644209
theorem B4128185 : Blo 1931435 4128185 := bstep (se 2 (by rfl) ⟨1548069, by rfl⟩ : syracuseStep 4128185 = 3096139) B3096139
theorem B11008493 : Blo 1931435 11008493 := bstep (se 3 (by rfl) ⟨2064092, by rfl⟩ : syracuseStep 11008493 = 4128185) B4128185
theorem B7338995 : Blo 1931435 7338995 := bstep (se 1 (by rfl) ⟨5504246, by rfl⟩ : syracuseStep 7338995 = 11008493) B11008493
theorem B4892663 : Blo 1931435 4892663 := bstep (se 1 (by rfl) ⟨3669497, by rfl⟩ : syracuseStep 4892663 = 7338995) B7338995
theorem B3261775 : Blo 1931435 3261775 := bstep (se 1 (by rfl) ⟨2446331, by rfl⟩ : syracuseStep 3261775 = 4892663) B4892663
theorem B4349033 : Blo 1931435 4349033 := bstep (se 2 (by rfl) ⟨1630887, by rfl⟩ : syracuseStep 4349033 = 3261775) B3261775
theorem B2899355 : Blo 1931435 2899355 := bstep (se 1 (by rfl) ⟨2174516, by rfl⟩ : syracuseStep 2899355 = 4349033) B4349033
theorem B1932903 : Blo 1931435 1932903 := bstep (se 1 (by rfl) ⟨1449677, by rfl⟩ : syracuseStep 1932903 = 2899355) B2899355
theorem B2174521 : Blo 1931435 2174521 := bbase (se 2 (by rfl) ⟨815445, by rfl⟩ : syracuseStep 2174521 = 1630891) (by norm_num)
theorem B2899361 : Blo 1931435 2899361 := bstep (se 2 (by rfl) ⟨1087260, by rfl⟩ : syracuseStep 2899361 = 2174521) B2174521
theorem B1932907 : Blo 1931435 1932907 := bstep (se 1 (by rfl) ⟨1449680, by rfl⟩ : syracuseStep 1932907 = 2899361) B2899361
theorem B2064101 : Blo 1931435 2064101 := bbase (se 4 (by rfl) ⟨193509, by rfl⟩ : syracuseStep 2064101 = 387019) (by norm_num)
theorem B5504269 : Blo 1931435 5504269 := bstep (se 3 (by rfl) ⟨1032050, by rfl⟩ : syracuseStep 5504269 = 2064101) B2064101
theorem B7339025 : Blo 1931435 7339025 := bstep (se 2 (by rfl) ⟨2752134, by rfl⟩ : syracuseStep 7339025 = 5504269) B5504269
theorem B4892683 : Blo 1931435 4892683 := bstep (se 1 (by rfl) ⟨3669512, by rfl⟩ : syracuseStep 4892683 = 7339025) B7339025
theorem B6523577 : Blo 1931435 6523577 := bstep (se 2 (by rfl) ⟨2446341, by rfl⟩ : syracuseStep 6523577 = 4892683) B4892683
theorem B4349051 : Blo 1931435 4349051 := bstep (se 1 (by rfl) ⟨3261788, by rfl⟩ : syracuseStep 4349051 = 6523577) B6523577
theorem B2899367 : Blo 1931435 2899367 := bstep (se 1 (by rfl) ⟨2174525, by rfl⟩ : syracuseStep 2899367 = 4349051) B4349051
theorem B1932911 : Blo 1931435 1932911 := bstep (se 1 (by rfl) ⟨1449683, by rfl⟩ : syracuseStep 1932911 = 2899367) B2899367
theorem B2899373 : Blo 1931435 2899373 := bbase (se 3 (by rfl) ⟨543632, by rfl⟩ : syracuseStep 2899373 = 1087265) (by norm_num)
theorem B1932915 : Blo 1931435 1932915 := bstep (se 1 (by rfl) ⟨1449686, by rfl⟩ : syracuseStep 1932915 = 2899373) B2899373
theorem B4349069 : Blo 1931435 4349069 := bbase (se 3 (by rfl) ⟨815450, by rfl⟩ : syracuseStep 4349069 = 1630901) (by norm_num)
theorem B2899379 : Blo 1931435 2899379 := bstep (se 1 (by rfl) ⟨2174534, by rfl⟩ : syracuseStep 2899379 = 4349069) B4349069
theorem B1932919 : Blo 1931435 1932919 := bstep (se 1 (by rfl) ⟨1449689, by rfl⟩ : syracuseStep 1932919 = 2899379) B2899379
theorem B2446357 : Blo 1931435 2446357 := bbase (se 6 (by rfl) ⟨57336, by rfl⟩ : syracuseStep 2446357 = 114673) (by norm_num)
theorem B3261809 : Blo 1931435 3261809 := bstep (se 2 (by rfl) ⟨1223178, by rfl⟩ : syracuseStep 3261809 = 2446357) B2446357
theorem B2174539 : Blo 1931435 2174539 := bstep (se 1 (by rfl) ⟨1630904, by rfl⟩ : syracuseStep 2174539 = 3261809) B3261809
theorem B2899385 : Blo 1931435 2899385 := bstep (se 2 (by rfl) ⟨1087269, by rfl⟩ : syracuseStep 2899385 = 2174539) B2174539
theorem B1932923 : Blo 1931435 1932923 := bstep (se 1 (by rfl) ⟨1449692, by rfl⟩ : syracuseStep 1932923 = 2899385) B2899385
theorem B3138421 : Blo 1931435 3138421 := bbase (se 5 (by rfl) ⟨147113, by rfl⟩ : syracuseStep 3138421 = 294227) (by norm_num)
theorem B4184561 : Blo 1931435 4184561 := bstep (se 2 (by rfl) ⟨1569210, by rfl⟩ : syracuseStep 4184561 = 3138421) B3138421
theorem B2789707 : Blo 1931435 2789707 := bstep (se 1 (by rfl) ⟨2092280, by rfl⟩ : syracuseStep 2789707 = 4184561) B4184561
theorem B3719609 : Blo 1931435 3719609 := bstep (se 2 (by rfl) ⟨1394853, by rfl⟩ : syracuseStep 3719609 = 2789707) B2789707
theorem B2479739 : Blo 1931435 2479739 := bstep (se 1 (by rfl) ⟨1859804, by rfl⟩ : syracuseStep 2479739 = 3719609) B3719609
theorem B6612637 : Blo 1931435 6612637 := bstep (se 3 (by rfl) ⟨1239869, by rfl⟩ : syracuseStep 6612637 = 2479739) B2479739
theorem B8816849 : Blo 1931435 8816849 := bstep (se 2 (by rfl) ⟨3306318, by rfl⟩ : syracuseStep 8816849 = 6612637) B6612637
theorem B5877899 : Blo 1931435 5877899 := bstep (se 1 (by rfl) ⟨4408424, by rfl⟩ : syracuseStep 5877899 = 8816849) B8816849
theorem B3918599 : Blo 1931435 3918599 := bstep (se 1 (by rfl) ⟨2938949, by rfl⟩ : syracuseStep 3918599 = 5877899) B5877899
theorem B41798389 : Blo 1931435 41798389 := bstep (se 5 (by rfl) ⟨1959299, by rfl⟩ : syracuseStep 41798389 = 3918599) B3918599
theorem B55731185 : Blo 1931435 55731185 := bstep (se 2 (by rfl) ⟨20899194, by rfl⟩ : syracuseStep 55731185 = 41798389) B41798389
theorem B37154123 : Blo 1931435 37154123 := bstep (se 1 (by rfl) ⟨27865592, by rfl⟩ : syracuseStep 37154123 = 55731185) B55731185
theorem B24769415 : Blo 1931435 24769415 := bstep (se 1 (by rfl) ⟨18577061, by rfl⟩ : syracuseStep 24769415 = 37154123) B37154123
theorem B16512943 : Blo 1931435 16512943 := bstep (se 1 (by rfl) ⟨12384707, by rfl⟩ : syracuseStep 16512943 = 24769415) B24769415
theorem B22017257 : Blo 1931435 22017257 := bstep (se 2 (by rfl) ⟨8256471, by rfl⟩ : syracuseStep 22017257 = 16512943) B16512943
theorem B14678171 : Blo 1931435 14678171 := bstep (se 1 (by rfl) ⟨11008628, by rfl⟩ : syracuseStep 14678171 = 22017257) B22017257
theorem B9785447 : Blo 1931435 9785447 := bstep (se 1 (by rfl) ⟨7339085, by rfl⟩ : syracuseStep 9785447 = 14678171) B14678171
theorem B6523631 : Blo 1931435 6523631 := bstep (se 1 (by rfl) ⟨4892723, by rfl⟩ : syracuseStep 6523631 = 9785447) B9785447
theorem B4349087 : Blo 1931435 4349087 := bstep (se 1 (by rfl) ⟨3261815, by rfl⟩ : syracuseStep 4349087 = 6523631) B6523631
theorem B2899391 : Blo 1931435 2899391 := bstep (se 1 (by rfl) ⟨2174543, by rfl⟩ : syracuseStep 2899391 = 4349087) B4349087
theorem B1932927 : Blo 1931435 1932927 := bstep (se 1 (by rfl) ⟨1449695, by rfl⟩ : syracuseStep 1932927 = 2899391) B2899391
theorem B2899397 : Blo 1931435 2899397 := bbase (se 4 (by rfl) ⟨271818, by rfl⟩ : syracuseStep 2899397 = 543637) (by norm_num)
theorem B1932931 : Blo 1931435 1932931 := bstep (se 1 (by rfl) ⟨1449698, by rfl⟩ : syracuseStep 1932931 = 2899397) B2899397
theorem B3261829 : Blo 1931435 3261829 := bbase (se 4 (by rfl) ⟨305796, by rfl⟩ : syracuseStep 3261829 = 611593) (by norm_num)
theorem B4349105 : Blo 1931435 4349105 := bstep (se 2 (by rfl) ⟨1630914, by rfl⟩ : syracuseStep 4349105 = 3261829) B3261829
theorem B2899403 : Blo 1931435 2899403 := bstep (se 1 (by rfl) ⟨2174552, by rfl⟩ : syracuseStep 2899403 = 4349105) B4349105
theorem B1932935 : Blo 1931435 1932935 := bstep (se 1 (by rfl) ⟨1449701, by rfl⟩ : syracuseStep 1932935 = 2899403) B2899403
theorem B2174557 : Blo 1931435 2174557 := bbase (se 3 (by rfl) ⟨407729, by rfl⟩ : syracuseStep 2174557 = 815459) (by norm_num)
theorem B2899409 : Blo 1931435 2899409 := bstep (se 2 (by rfl) ⟨1087278, by rfl⟩ : syracuseStep 2899409 = 2174557) B2174557
theorem B1932939 : Blo 1931435 1932939 := bstep (se 1 (by rfl) ⟨1449704, by rfl⟩ : syracuseStep 1932939 = 2899409) B2899409
theorem B6523685 : Blo 1931435 6523685 := bbase (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) (by norm_num)
theorem B4349123 : Blo 1931435 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B2899415 : Blo 1931435 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B1932943 : Blo 1931435 1932943 := bstep (se 1 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 1932943 = 2899415) B2899415
theorem B2899421 : Blo 1931435 2899421 := bbase (se 3 (by rfl) ⟨543641, by rfl⟩ : syracuseStep 2899421 = 1087283) (by norm_num)
theorem B1932947 : Blo 1931435 1932947 := bstep (se 1 (by rfl) ⟨1449710, by rfl⟩ : syracuseStep 1932947 = 2899421) B2899421
theorem B4349141 : Blo 1931435 4349141 := bbase (se 7 (by rfl) ⟨50966, by rfl⟩ : syracuseStep 4349141 = 101933) (by norm_num)
theorem B2899427 : Blo 1931435 2899427 := bstep (se 1 (by rfl) ⟨2174570, by rfl⟩ : syracuseStep 2899427 = 4349141) B4349141
theorem B1932951 : Blo 1931435 1932951 := bstep (se 1 (by rfl) ⟨1449713, by rfl⟩ : syracuseStep 1932951 = 2899427) B2899427
theorem B1959329 : Blo 1931435 1959329 := bbase (se 2 (by rfl) ⟨734748, by rfl⟩ : syracuseStep 1959329 = 1469497) (by norm_num)
theorem B5224877 : Blo 1931435 5224877 := bstep (se 3 (by rfl) ⟨979664, by rfl⟩ : syracuseStep 5224877 = 1959329) B1959329
theorem B3483251 : Blo 1931435 3483251 := bstep (se 1 (by rfl) ⟨2612438, by rfl⟩ : syracuseStep 3483251 = 5224877) B5224877
theorem B2322167 : Blo 1931435 2322167 := bstep (se 1 (by rfl) ⟨1741625, by rfl⟩ : syracuseStep 2322167 = 3483251) B3483251
theorem B6192445 : Blo 1931435 6192445 := bstep (se 3 (by rfl) ⟨1161083, by rfl⟩ : syracuseStep 6192445 = 2322167) B2322167
theorem B8256593 : Blo 1931435 8256593 := bstep (se 2 (by rfl) ⟨3096222, by rfl⟩ : syracuseStep 8256593 = 6192445) B6192445
theorem B5504395 : Blo 1931435 5504395 := bstep (se 1 (by rfl) ⟨4128296, by rfl⟩ : syracuseStep 5504395 = 8256593) B8256593
theorem B7339193 : Blo 1931435 7339193 := bstep (se 2 (by rfl) ⟨2752197, by rfl⟩ : syracuseStep 7339193 = 5504395) B5504395
theorem B4892795 : Blo 1931435 4892795 := bstep (se 1 (by rfl) ⟨3669596, by rfl⟩ : syracuseStep 4892795 = 7339193) B7339193
theorem B3261863 : Blo 1931435 3261863 := bstep (se 1 (by rfl) ⟨2446397, by rfl⟩ : syracuseStep 3261863 = 4892795) B4892795
theorem B2174575 : Blo 1931435 2174575 := bstep (se 1 (by rfl) ⟨1630931, by rfl⟩ : syracuseStep 2174575 = 3261863) B3261863
theorem B2899433 : Blo 1931435 2899433 := bstep (se 2 (by rfl) ⟨1087287, by rfl⟩ : syracuseStep 2899433 = 2174575) B2174575
theorem B1932955 : Blo 1931435 1932955 := bstep (se 1 (by rfl) ⟨1449716, by rfl⟩ : syracuseStep 1932955 = 2899433) B2899433
theorem B2479781 : Blo 1931435 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B6612749 : Blo 1931435 6612749 := bstep (se 3 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 6612749 = 2479781) B2479781
theorem B4408499 : Blo 1931435 4408499 := bstep (se 1 (by rfl) ⟨3306374, by rfl⟩ : syracuseStep 4408499 = 6612749) B6612749
theorem B2938999 : Blo 1931435 2938999 := bstep (se 1 (by rfl) ⟨2204249, by rfl⟩ : syracuseStep 2938999 = 4408499) B4408499
theorem B3918665 : Blo 1931435 3918665 := bstep (se 2 (by rfl) ⟨1469499, by rfl⟩ : syracuseStep 3918665 = 2938999) B2938999
theorem B2612443 : Blo 1931435 2612443 := bstep (se 1 (by rfl) ⟨1959332, by rfl⟩ : syracuseStep 2612443 = 3918665) B3918665
theorem B3483257 : Blo 1931435 3483257 := bstep (se 2 (by rfl) ⟨1306221, by rfl⟩ : syracuseStep 3483257 = 2612443) B2612443
theorem B9288685 : Blo 1931435 9288685 := bstep (se 3 (by rfl) ⟨1741628, by rfl⟩ : syracuseStep 9288685 = 3483257) B3483257
theorem B12384913 : Blo 1931435 12384913 := bstep (se 2 (by rfl) ⟨4644342, by rfl⟩ : syracuseStep 12384913 = 9288685) B9288685
theorem B16513217 : Blo 1931435 16513217 := bstep (se 2 (by rfl) ⟨6192456, by rfl⟩ : syracuseStep 16513217 = 12384913) B12384913
theorem B11008811 : Blo 1931435 11008811 := bstep (se 1 (by rfl) ⟨8256608, by rfl⟩ : syracuseStep 11008811 = 16513217) B16513217
theorem B7339207 : Blo 1931435 7339207 := bstep (se 1 (by rfl) ⟨5504405, by rfl⟩ : syracuseStep 7339207 = 11008811) B11008811
theorem B9785609 : Blo 1931435 9785609 := bstep (se 2 (by rfl) ⟨3669603, by rfl⟩ : syracuseStep 9785609 = 7339207) B7339207
theorem B6523739 : Blo 1931435 6523739 := bstep (se 1 (by rfl) ⟨4892804, by rfl⟩ : syracuseStep 6523739 = 9785609) B9785609
theorem B4349159 : Blo 1931435 4349159 := bstep (se 1 (by rfl) ⟨3261869, by rfl⟩ : syracuseStep 4349159 = 6523739) B6523739
theorem B2899439 : Blo 1931435 2899439 := bstep (se 1 (by rfl) ⟨2174579, by rfl⟩ : syracuseStep 2899439 = 4349159) B4349159
theorem B1932959 : Blo 1931435 1932959 := bstep (se 1 (by rfl) ⟨1449719, by rfl⟩ : syracuseStep 1932959 = 2899439) B2899439
theorem B2899445 : Blo 1931435 2899445 := bbase (se 5 (by rfl) ⟨135911, by rfl⟩ : syracuseStep 2899445 = 271823) (by norm_num)
theorem B1932963 : Blo 1931435 1932963 := bstep (se 1 (by rfl) ⟨1449722, by rfl⟩ : syracuseStep 1932963 = 2899445) B2899445
theorem B2064161 : Blo 1931435 2064161 := bbase (se 2 (by rfl) ⟨774060, by rfl⟩ : syracuseStep 2064161 = 1548121) (by norm_num)
theorem B5504429 : Blo 1931435 5504429 := bstep (se 3 (by rfl) ⟨1032080, by rfl⟩ : syracuseStep 5504429 = 2064161) B2064161
theorem B3669619 : Blo 1931435 3669619 := bstep (se 1 (by rfl) ⟨2752214, by rfl⟩ : syracuseStep 3669619 = 5504429) B5504429
theorem B4892825 : Blo 1931435 4892825 := bstep (se 2 (by rfl) ⟨1834809, by rfl⟩ : syracuseStep 4892825 = 3669619) B3669619
theorem B3261883 : Blo 1931435 3261883 := bstep (se 1 (by rfl) ⟨2446412, by rfl⟩ : syracuseStep 3261883 = 4892825) B4892825
theorem B4349177 : Blo 1931435 4349177 := bstep (se 2 (by rfl) ⟨1630941, by rfl⟩ : syracuseStep 4349177 = 3261883) B3261883
theorem B2899451 : Blo 1931435 2899451 := bstep (se 1 (by rfl) ⟨2174588, by rfl⟩ : syracuseStep 2899451 = 4349177) B4349177
theorem B1932967 : Blo 1931435 1932967 := bstep (se 1 (by rfl) ⟨1449725, by rfl⟩ : syracuseStep 1932967 = 2899451) B2899451
theorem B2174593 : Blo 1931435 2174593 := bbase (se 2 (by rfl) ⟨815472, by rfl⟩ : syracuseStep 2174593 = 1630945) (by norm_num)
theorem B2899457 : Blo 1931435 2899457 := bstep (se 2 (by rfl) ⟨1087296, by rfl⟩ : syracuseStep 2899457 = 2174593) B2174593
theorem B1932971 : Blo 1931435 1932971 := bstep (se 1 (by rfl) ⟨1449728, by rfl⟩ : syracuseStep 1932971 = 2899457) B2899457
theorem B4892845 : Blo 1931435 4892845 := bbase (se 3 (by rfl) ⟨917408, by rfl⟩ : syracuseStep 4892845 = 1834817) (by norm_num)
theorem B6523793 : Blo 1931435 6523793 := bstep (se 2 (by rfl) ⟨2446422, by rfl⟩ : syracuseStep 6523793 = 4892845) B4892845
theorem B4349195 : Blo 1931435 4349195 := bstep (se 1 (by rfl) ⟨3261896, by rfl⟩ : syracuseStep 4349195 = 6523793) B6523793
theorem B2899463 : Blo 1931435 2899463 := bstep (se 1 (by rfl) ⟨2174597, by rfl⟩ : syracuseStep 2899463 = 4349195) B4349195
theorem B1932975 : Blo 1931435 1932975 := bstep (se 1 (by rfl) ⟨1449731, by rfl⟩ : syracuseStep 1932975 = 2899463) B2899463
theorem B2899469 : Blo 1931435 2899469 := bbase (se 3 (by rfl) ⟨543650, by rfl⟩ : syracuseStep 2899469 = 1087301) (by norm_num)
theorem B1932979 : Blo 1931435 1932979 := bstep (se 1 (by rfl) ⟨1449734, by rfl⟩ : syracuseStep 1932979 = 2899469) B2899469
theorem B4349213 : Blo 1931435 4349213 := bbase (se 3 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 4349213 = 1630955) (by norm_num)
theorem B2899475 : Blo 1931435 2899475 := bstep (se 1 (by rfl) ⟨2174606, by rfl⟩ : syracuseStep 2899475 = 4349213) B4349213
theorem B1932983 : Blo 1931435 1932983 := bstep (se 1 (by rfl) ⟨1449737, by rfl⟩ : syracuseStep 1932983 = 2899475) B2899475
theorem B3261917 : Blo 1931435 3261917 := bbase (se 3 (by rfl) ⟨611609, by rfl⟩ : syracuseStep 3261917 = 1223219) (by norm_num)
theorem B2174611 : Blo 1931435 2174611 := bstep (se 1 (by rfl) ⟨1630958, by rfl⟩ : syracuseStep 2174611 = 3261917) B3261917
theorem B2899481 : Blo 1931435 2899481 := bstep (se 2 (by rfl) ⟨1087305, by rfl⟩ : syracuseStep 2899481 = 2174611) B2174611
theorem B1932987 : Blo 1931435 1932987 := bstep (se 1 (by rfl) ⟨1449740, by rfl⟩ : syracuseStep 1932987 = 2899481) B2899481
theorem B5296261 : Blo 1931435 5296261 := bbase (se 4 (by rfl) ⟨496524, by rfl⟩ : syracuseStep 5296261 = 993049) (by norm_num)
theorem B7061681 : Blo 1931435 7061681 := bstep (se 2 (by rfl) ⟨2648130, by rfl⟩ : syracuseStep 7061681 = 5296261) B5296261
theorem B18831149 : Blo 1931435 18831149 := bstep (se 3 (by rfl) ⟨3530840, by rfl⟩ : syracuseStep 18831149 = 7061681) B7061681
theorem B12554099 : Blo 1931435 12554099 := bstep (se 1 (by rfl) ⟨9415574, by rfl⟩ : syracuseStep 12554099 = 18831149) B18831149
theorem B8369399 : Blo 1931435 8369399 := bstep (se 1 (by rfl) ⟨6277049, by rfl⟩ : syracuseStep 8369399 = 12554099) B12554099
theorem B5579599 : Blo 1931435 5579599 := bstep (se 1 (by rfl) ⟨4184699, by rfl⟩ : syracuseStep 5579599 = 8369399) B8369399
theorem B7439465 : Blo 1931435 7439465 := bstep (se 2 (by rfl) ⟨2789799, by rfl⟩ : syracuseStep 7439465 = 5579599) B5579599
theorem B4959643 : Blo 1931435 4959643 := bstep (se 1 (by rfl) ⟨3719732, by rfl⟩ : syracuseStep 4959643 = 7439465) B7439465
theorem B6612857 : Blo 1931435 6612857 := bstep (se 2 (by rfl) ⟨2479821, by rfl⟩ : syracuseStep 6612857 = 4959643) B4959643
theorem B4408571 : Blo 1931435 4408571 := bstep (se 1 (by rfl) ⟨3306428, by rfl⟩ : syracuseStep 4408571 = 6612857) B6612857
theorem B2939047 : Blo 1931435 2939047 := bstep (se 1 (by rfl) ⟨2204285, by rfl⟩ : syracuseStep 2939047 = 4408571) B4408571
theorem B15674917 : Blo 1931435 15674917 := bstep (se 4 (by rfl) ⟨1469523, by rfl⟩ : syracuseStep 15674917 = 2939047) B2939047
theorem B20899889 : Blo 1931435 20899889 := bstep (se 2 (by rfl) ⟨7837458, by rfl⟩ : syracuseStep 20899889 = 15674917) B15674917
theorem B13933259 : Blo 1931435 13933259 := bstep (se 1 (by rfl) ⟨10449944, by rfl⟩ : syracuseStep 13933259 = 20899889) B20899889
theorem B9288839 : Blo 1931435 9288839 := bstep (se 1 (by rfl) ⟨6966629, by rfl⟩ : syracuseStep 9288839 = 13933259) B13933259
theorem B6192559 : Blo 1931435 6192559 := bstep (se 1 (by rfl) ⟨4644419, by rfl⟩ : syracuseStep 6192559 = 9288839) B9288839
theorem B8256745 : Blo 1931435 8256745 := bstep (se 2 (by rfl) ⟨3096279, by rfl⟩ : syracuseStep 8256745 = 6192559) B6192559
theorem B11008993 : Blo 1931435 11008993 := bstep (se 2 (by rfl) ⟨4128372, by rfl⟩ : syracuseStep 11008993 = 8256745) B8256745
theorem B14678657 : Blo 1931435 14678657 := bstep (se 2 (by rfl) ⟨5504496, by rfl⟩ : syracuseStep 14678657 = 11008993) B11008993
theorem B9785771 : Blo 1931435 9785771 := bstep (se 1 (by rfl) ⟨7339328, by rfl⟩ : syracuseStep 9785771 = 14678657) B14678657
theorem B6523847 : Blo 1931435 6523847 := bstep (se 1 (by rfl) ⟨4892885, by rfl⟩ : syracuseStep 6523847 = 9785771) B9785771
theorem B4349231 : Blo 1931435 4349231 := bstep (se 1 (by rfl) ⟨3261923, by rfl⟩ : syracuseStep 4349231 = 6523847) B6523847
theorem B2899487 : Blo 1931435 2899487 := bstep (se 1 (by rfl) ⟨2174615, by rfl⟩ : syracuseStep 2899487 = 4349231) B4349231
theorem B1932991 : Blo 1931435 1932991 := bstep (se 1 (by rfl) ⟨1449743, by rfl⟩ : syracuseStep 1932991 = 2899487) B2899487
theorem B2899493 : Blo 1931435 2899493 := bbase (se 4 (by rfl) ⟨271827, by rfl⟩ : syracuseStep 2899493 = 543655) (by norm_num)
theorem B1932995 : Blo 1931435 1932995 := bstep (se 1 (by rfl) ⟨1449746, by rfl⟩ : syracuseStep 1932995 = 2899493) B2899493
theorem B2446453 : Blo 1931435 2446453 := bbase (se 5 (by rfl) ⟨114677, by rfl⟩ : syracuseStep 2446453 = 229355) (by norm_num)
theorem B3261937 : Blo 1931435 3261937 := bstep (se 2 (by rfl) ⟨1223226, by rfl⟩ : syracuseStep 3261937 = 2446453) B2446453
theorem B4349249 : Blo 1931435 4349249 := bstep (se 2 (by rfl) ⟨1630968, by rfl⟩ : syracuseStep 4349249 = 3261937) B3261937
theorem B2899499 : Blo 1931435 2899499 := bstep (se 1 (by rfl) ⟨2174624, by rfl⟩ : syracuseStep 2899499 = 4349249) B4349249
theorem B1932999 : Blo 1931435 1932999 := bstep (se 1 (by rfl) ⟨1449749, by rfl⟩ : syracuseStep 1932999 = 2899499) B2899499
theorem B2174629 : Blo 1931435 2174629 := bbase (se 4 (by rfl) ⟨203871, by rfl⟩ : syracuseStep 2174629 = 407743) (by norm_num)
theorem B2899505 : Blo 1931435 2899505 := bstep (se 2 (by rfl) ⟨1087314, by rfl⟩ : syracuseStep 2899505 = 2174629) B2174629
theorem B1933003 : Blo 1931435 1933003 := bstep (se 1 (by rfl) ⟨1449752, by rfl⟩ : syracuseStep 1933003 = 2899505) B2899505
theorem B4903157 : Blo 1931435 4903157 := bbase (se 5 (by rfl) ⟨229835, by rfl⟩ : syracuseStep 4903157 = 459671) (by norm_num)
theorem B13075085 : Blo 1931435 13075085 := bstep (se 3 (by rfl) ⟨2451578, by rfl⟩ : syracuseStep 13075085 = 4903157) B4903157
theorem B34866893 : Blo 1931435 34866893 := bstep (se 3 (by rfl) ⟨6537542, by rfl⟩ : syracuseStep 34866893 = 13075085) B13075085
theorem B92978381 : Blo 1931435 92978381 := bstep (se 3 (by rfl) ⟨17433446, by rfl⟩ : syracuseStep 92978381 = 34866893) B34866893
theorem B61985587 : Blo 1931435 61985587 := bstep (se 1 (by rfl) ⟨46489190, by rfl⟩ : syracuseStep 61985587 = 92978381) B92978381
theorem B82647449 : Blo 1931435 82647449 := bstep (se 2 (by rfl) ⟨30992793, by rfl⟩ : syracuseStep 82647449 = 61985587) B61985587
theorem B55098299 : Blo 1931435 55098299 := bstep (se 1 (by rfl) ⟨41323724, by rfl⟩ : syracuseStep 55098299 = 82647449) B82647449
theorem B36732199 : Blo 1931435 36732199 := bstep (se 1 (by rfl) ⟨27549149, by rfl⟩ : syracuseStep 36732199 = 55098299) B55098299
theorem B48976265 : Blo 1931435 48976265 := bstep (se 2 (by rfl) ⟨18366099, by rfl⟩ : syracuseStep 48976265 = 36732199) B36732199
theorem B130603373 : Blo 1931435 130603373 := bstep (se 3 (by rfl) ⟨24488132, by rfl⟩ : syracuseStep 130603373 = 48976265) B48976265
theorem B87068915 : Blo 1931435 87068915 := bstep (se 1 (by rfl) ⟨65301686, by rfl⟩ : syracuseStep 87068915 = 130603373) B130603373
theorem B58045943 : Blo 1931435 58045943 := bstep (se 1 (by rfl) ⟨43534457, by rfl⟩ : syracuseStep 58045943 = 87068915) B87068915
theorem B154789181 : Blo 1931435 154789181 := bstep (se 3 (by rfl) ⟨29022971, by rfl⟩ : syracuseStep 154789181 = 58045943) B58045943
theorem B103192787 : Blo 1931435 103192787 := bstep (se 1 (by rfl) ⟨77394590, by rfl⟩ : syracuseStep 103192787 = 154789181) B154789181
theorem B68795191 : Blo 1931435 68795191 := bstep (se 1 (by rfl) ⟨51596393, by rfl⟩ : syracuseStep 68795191 = 103192787) B103192787
theorem B91726921 : Blo 1931435 91726921 := bstep (se 2 (by rfl) ⟨34397595, by rfl⟩ : syracuseStep 91726921 = 68795191) B68795191
theorem B122302561 : Blo 1931435 122302561 := bstep (se 2 (by rfl) ⟨45863460, by rfl⟩ : syracuseStep 122302561 = 91726921) B91726921
theorem B163070081 : Blo 1931435 163070081 := bstep (se 2 (by rfl) ⟨61151280, by rfl⟩ : syracuseStep 163070081 = 122302561) B122302561
theorem B108713387 : Blo 1931435 108713387 := bstep (se 1 (by rfl) ⟨81535040, by rfl⟩ : syracuseStep 108713387 = 163070081) B163070081
theorem B289902365 : Blo 1931435 289902365 := bstep (se 3 (by rfl) ⟨54356693, by rfl⟩ : syracuseStep 289902365 = 108713387) B108713387
theorem B193268243 : Blo 1931435 193268243 := bstep (se 1 (by rfl) ⟨144951182, by rfl⟩ : syracuseStep 193268243 = 289902365) B289902365
theorem B128845495 : Blo 1931435 128845495 := bstep (se 1 (by rfl) ⟨96634121, by rfl⟩ : syracuseStep 128845495 = 193268243) B193268243
theorem B687175973 : Blo 1931435 687175973 := bstep (se 4 (by rfl) ⟨64422747, by rfl⟩ : syracuseStep 687175973 = 128845495) B128845495
theorem B458117315 : Blo 1931435 458117315 := bstep (se 1 (by rfl) ⟨343587986, by rfl⟩ : syracuseStep 458117315 = 687175973) B687175973
theorem B305411543 : Blo 1931435 305411543 := bstep (se 1 (by rfl) ⟨229058657, by rfl⟩ : syracuseStep 305411543 = 458117315) B458117315
theorem B203607695 : Blo 1931435 203607695 := bstep (se 1 (by rfl) ⟨152705771, by rfl⟩ : syracuseStep 203607695 = 305411543) B305411543
theorem B135738463 : Blo 1931435 135738463 := bstep (se 1 (by rfl) ⟨101803847, by rfl⟩ : syracuseStep 135738463 = 203607695) B203607695
theorem B180984617 : Blo 1931435 180984617 := bstep (se 2 (by rfl) ⟨67869231, by rfl⟩ : syracuseStep 180984617 = 135738463) B135738463
theorem B120656411 : Blo 1931435 120656411 := bstep (se 1 (by rfl) ⟨90492308, by rfl⟩ : syracuseStep 120656411 = 180984617) B180984617
theorem B80437607 : Blo 1931435 80437607 := bstep (se 1 (by rfl) ⟨60328205, by rfl⟩ : syracuseStep 80437607 = 120656411) B120656411
theorem B53625071 : Blo 1931435 53625071 := bstep (se 1 (by rfl) ⟨40218803, by rfl⟩ : syracuseStep 53625071 = 80437607) B80437607
theorem B35750047 : Blo 1931435 35750047 := bstep (se 1 (by rfl) ⟨26812535, by rfl⟩ : syracuseStep 35750047 = 53625071) B53625071
theorem B47666729 : Blo 1931435 47666729 := bstep (se 2 (by rfl) ⟨17875023, by rfl⟩ : syracuseStep 47666729 = 35750047) B35750047
theorem B127111277 : Blo 1931435 127111277 := bstep (se 3 (by rfl) ⟨23833364, by rfl⟩ : syracuseStep 127111277 = 47666729) B47666729
theorem B84740851 : Blo 1931435 84740851 := bstep (se 1 (by rfl) ⟨63555638, by rfl⟩ : syracuseStep 84740851 = 127111277) B127111277
theorem B112987801 : Blo 1931435 112987801 := bstep (se 2 (by rfl) ⟨42370425, by rfl⟩ : syracuseStep 112987801 = 84740851) B84740851
theorem B150650401 : Blo 1931435 150650401 := bstep (se 2 (by rfl) ⟨56493900, by rfl⟩ : syracuseStep 150650401 = 112987801) B112987801
theorem B200867201 : Blo 1931435 200867201 := bstep (se 2 (by rfl) ⟨75325200, by rfl⟩ : syracuseStep 200867201 = 150650401) B150650401
theorem B133911467 : Blo 1931435 133911467 := bstep (se 1 (by rfl) ⟨100433600, by rfl⟩ : syracuseStep 133911467 = 200867201) B200867201
theorem B89274311 : Blo 1931435 89274311 := bstep (se 1 (by rfl) ⟨66955733, by rfl⟩ : syracuseStep 89274311 = 133911467) B133911467
theorem B59516207 : Blo 1931435 59516207 := bstep (se 1 (by rfl) ⟨44637155, by rfl⟩ : syracuseStep 59516207 = 89274311) B89274311
theorem B39677471 : Blo 1931435 39677471 := bstep (se 1 (by rfl) ⟨29758103, by rfl⟩ : syracuseStep 39677471 = 59516207) B59516207
theorem B26451647 : Blo 1931435 26451647 := bstep (se 1 (by rfl) ⟨19838735, by rfl⟩ : syracuseStep 26451647 = 39677471) B39677471
theorem B17634431 : Blo 1931435 17634431 := bstep (se 1 (by rfl) ⟨13225823, by rfl⟩ : syracuseStep 17634431 = 26451647) B26451647
theorem B11756287 : Blo 1931435 11756287 := bstep (se 1 (by rfl) ⟨8817215, by rfl⟩ : syracuseStep 11756287 = 17634431) B17634431
theorem B15675049 : Blo 1931435 15675049 := bstep (se 2 (by rfl) ⟨5878143, by rfl⟩ : syracuseStep 15675049 = 11756287) B11756287
theorem B20900065 : Blo 1931435 20900065 := bstep (se 2 (by rfl) ⟨7837524, by rfl⟩ : syracuseStep 20900065 = 15675049) B15675049
theorem B27866753 : Blo 1931435 27866753 := bstep (se 2 (by rfl) ⟨10450032, by rfl⟩ : syracuseStep 27866753 = 20900065) B20900065
theorem B18577835 : Blo 1931435 18577835 := bstep (se 1 (by rfl) ⟨13933376, by rfl⟩ : syracuseStep 18577835 = 27866753) B27866753
theorem B12385223 : Blo 1931435 12385223 := bstep (se 1 (by rfl) ⟨9288917, by rfl⟩ : syracuseStep 12385223 = 18577835) B18577835
theorem B8256815 : Blo 1931435 8256815 := bstep (se 1 (by rfl) ⟨6192611, by rfl⟩ : syracuseStep 8256815 = 12385223) B12385223
theorem B5504543 : Blo 1931435 5504543 := bstep (se 1 (by rfl) ⟨4128407, by rfl⟩ : syracuseStep 5504543 = 8256815) B8256815
theorem B3669695 : Blo 1931435 3669695 := bstep (se 1 (by rfl) ⟨2752271, by rfl⟩ : syracuseStep 3669695 = 5504543) B5504543
theorem B2446463 : Blo 1931435 2446463 := bstep (se 1 (by rfl) ⟨1834847, by rfl⟩ : syracuseStep 2446463 = 3669695) B3669695
theorem B6523901 : Blo 1931435 6523901 := bstep (se 3 (by rfl) ⟨1223231, by rfl⟩ : syracuseStep 6523901 = 2446463) B2446463
theorem B4349267 : Blo 1931435 4349267 := bstep (se 1 (by rfl) ⟨3261950, by rfl⟩ : syracuseStep 4349267 = 6523901) B6523901
theorem B2899511 : Blo 1931435 2899511 := bstep (se 1 (by rfl) ⟨2174633, by rfl⟩ : syracuseStep 2899511 = 4349267) B4349267
theorem B1933007 : Blo 1931435 1933007 := bstep (se 1 (by rfl) ⟨1449755, by rfl⟩ : syracuseStep 1933007 = 2899511) B2899511
theorem B2899517 : Blo 1931435 2899517 := bbase (se 3 (by rfl) ⟨543659, by rfl⟩ : syracuseStep 2899517 = 1087319) (by norm_num)
theorem B1933011 : Blo 1931435 1933011 := bstep (se 1 (by rfl) ⟨1449758, by rfl⟩ : syracuseStep 1933011 = 2899517) B2899517
theorem B4349285 : Blo 1931435 4349285 := bbase (se 4 (by rfl) ⟨407745, by rfl⟩ : syracuseStep 4349285 = 815491) (by norm_num)
theorem B2899523 : Blo 1931435 2899523 := bstep (se 1 (by rfl) ⟨2174642, by rfl⟩ : syracuseStep 2899523 = 4349285) B4349285
theorem B1933015 : Blo 1931435 1933015 := bstep (se 1 (by rfl) ⟨1449761, by rfl⟩ : syracuseStep 1933015 = 2899523) B2899523
theorem B4892957 : Blo 1931435 4892957 := bbase (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) (by norm_num)
theorem B3261971 : Blo 1931435 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B2174647 : Blo 1931435 2174647 := bstep (se 1 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 2174647 = 3261971) B3261971
theorem B2899529 : Blo 1931435 2899529 := bstep (se 2 (by rfl) ⟨1087323, by rfl⟩ : syracuseStep 2899529 = 2174647) B2174647
theorem B1933019 : Blo 1931435 1933019 := bstep (se 1 (by rfl) ⟨1449764, by rfl⟩ : syracuseStep 1933019 = 2899529) B2899529
theorem B3669725 : Blo 1931435 3669725 := bbase (se 3 (by rfl) ⟨688073, by rfl⟩ : syracuseStep 3669725 = 1376147) (by norm_num)
theorem B9785933 : Blo 1931435 9785933 := bstep (se 3 (by rfl) ⟨1834862, by rfl⟩ : syracuseStep 9785933 = 3669725) B3669725
theorem B6523955 : Blo 1931435 6523955 := bstep (se 1 (by rfl) ⟨4892966, by rfl⟩ : syracuseStep 6523955 = 9785933) B9785933
theorem B4349303 : Blo 1931435 4349303 := bstep (se 1 (by rfl) ⟨3261977, by rfl⟩ : syracuseStep 4349303 = 6523955) B6523955
theorem B2899535 : Blo 1931435 2899535 := bstep (se 1 (by rfl) ⟨2174651, by rfl⟩ : syracuseStep 2899535 = 4349303) B4349303
theorem B1933023 : Blo 1931435 1933023 := bstep (se 1 (by rfl) ⟨1449767, by rfl⟩ : syracuseStep 1933023 = 2899535) B2899535
theorem B2899541 : Blo 1931435 2899541 := bbase (se 8 (by rfl) ⟨16989, by rfl⟩ : syracuseStep 2899541 = 33979) (by norm_num)
theorem B1933027 : Blo 1931435 1933027 := bstep (se 1 (by rfl) ⟨1449770, by rfl⟩ : syracuseStep 1933027 = 2899541) B2899541
theorem B8256917 : Blo 1931435 8256917 := bbase (se 6 (by rfl) ⟨193521, by rfl⟩ : syracuseStep 8256917 = 387043) (by norm_num)
theorem B5504611 : Blo 1931435 5504611 := bstep (se 1 (by rfl) ⟨4128458, by rfl⟩ : syracuseStep 5504611 = 8256917) B8256917
theorem B7339481 : Blo 1931435 7339481 := bstep (se 2 (by rfl) ⟨2752305, by rfl⟩ : syracuseStep 7339481 = 5504611) B5504611
theorem B4892987 : Blo 1931435 4892987 := bstep (se 1 (by rfl) ⟨3669740, by rfl⟩ : syracuseStep 4892987 = 7339481) B7339481
theorem B3261991 : Blo 1931435 3261991 := bstep (se 1 (by rfl) ⟨2446493, by rfl⟩ : syracuseStep 3261991 = 4892987) B4892987
theorem B4349321 : Blo 1931435 4349321 := bstep (se 2 (by rfl) ⟨1630995, by rfl⟩ : syracuseStep 4349321 = 3261991) B3261991
theorem B2899547 : Blo 1931435 2899547 := bstep (se 1 (by rfl) ⟨2174660, by rfl⟩ : syracuseStep 2899547 = 4349321) B4349321
theorem B1933031 : Blo 1931435 1933031 := bstep (se 1 (by rfl) ⟨1449773, by rfl⟩ : syracuseStep 1933031 = 2899547) B2899547
theorem B2174665 : Blo 1931435 2174665 := bbase (se 2 (by rfl) ⟨815499, by rfl⟩ : syracuseStep 2174665 = 1630999) (by norm_num)
theorem B2899553 : Blo 1931435 2899553 := bstep (se 2 (by rfl) ⟨1087332, by rfl⟩ : syracuseStep 2899553 = 2174665) B2174665
theorem B1933035 : Blo 1931435 1933035 := bstep (se 1 (by rfl) ⟨1449776, by rfl⟩ : syracuseStep 1933035 = 2899553) B2899553
theorem B11159477 : Blo 1931435 11159477 := bbase (se 5 (by rfl) ⟨523100, by rfl⟩ : syracuseStep 11159477 = 1046201) (by norm_num)
theorem B7439651 : Blo 1931435 7439651 := bstep (se 1 (by rfl) ⟨5579738, by rfl⟩ : syracuseStep 7439651 = 11159477) B11159477
theorem B4959767 : Blo 1931435 4959767 := bstep (se 1 (by rfl) ⟨3719825, by rfl⟩ : syracuseStep 4959767 = 7439651) B7439651
theorem B3306511 : Blo 1931435 3306511 := bstep (se 1 (by rfl) ⟨2479883, by rfl⟩ : syracuseStep 3306511 = 4959767) B4959767
theorem B4408681 : Blo 1931435 4408681 := bstep (se 2 (by rfl) ⟨1653255, by rfl⟩ : syracuseStep 4408681 = 3306511) B3306511
theorem B5878241 : Blo 1931435 5878241 := bstep (se 2 (by rfl) ⟨2204340, by rfl⟩ : syracuseStep 5878241 = 4408681) B4408681
theorem B3918827 : Blo 1931435 3918827 := bstep (se 1 (by rfl) ⟨2939120, by rfl⟩ : syracuseStep 3918827 = 5878241) B5878241
theorem B10450205 : Blo 1931435 10450205 := bstep (se 3 (by rfl) ⟨1959413, by rfl⟩ : syracuseStep 10450205 = 3918827) B3918827
theorem B6966803 : Blo 1931435 6966803 := bstep (se 1 (by rfl) ⟨5225102, by rfl⟩ : syracuseStep 6966803 = 10450205) B10450205
theorem B4644535 : Blo 1931435 4644535 := bstep (se 1 (by rfl) ⟨3483401, by rfl⟩ : syracuseStep 4644535 = 6966803) B6966803
theorem B6192713 : Blo 1931435 6192713 := bstep (se 2 (by rfl) ⟨2322267, by rfl⟩ : syracuseStep 6192713 = 4644535) B4644535
theorem B16513901 : Blo 1931435 16513901 := bstep (se 3 (by rfl) ⟨3096356, by rfl⟩ : syracuseStep 16513901 = 6192713) B6192713
theorem B11009267 : Blo 1931435 11009267 := bstep (se 1 (by rfl) ⟨8256950, by rfl⟩ : syracuseStep 11009267 = 16513901) B16513901
theorem B7339511 : Blo 1931435 7339511 := bstep (se 1 (by rfl) ⟨5504633, by rfl⟩ : syracuseStep 7339511 = 11009267) B11009267
theorem B4893007 : Blo 1931435 4893007 := bstep (se 1 (by rfl) ⟨3669755, by rfl⟩ : syracuseStep 4893007 = 7339511) B7339511
theorem B6524009 : Blo 1931435 6524009 := bstep (se 2 (by rfl) ⟨2446503, by rfl⟩ : syracuseStep 6524009 = 4893007) B4893007
theorem B4349339 : Blo 1931435 4349339 := bstep (se 1 (by rfl) ⟨3262004, by rfl⟩ : syracuseStep 4349339 = 6524009) B6524009
theorem B2899559 : Blo 1931435 2899559 := bstep (se 1 (by rfl) ⟨2174669, by rfl⟩ : syracuseStep 2899559 = 4349339) B4349339
theorem B1933039 : Blo 1931435 1933039 := bstep (se 1 (by rfl) ⟨1449779, by rfl⟩ : syracuseStep 1933039 = 2899559) B2899559
theorem B2899565 : Blo 1931435 2899565 := bbase (se 3 (by rfl) ⟨543668, by rfl⟩ : syracuseStep 2899565 = 1087337) (by norm_num)
theorem B1933043 : Blo 1931435 1933043 := bstep (se 1 (by rfl) ⟨1449782, by rfl⟩ : syracuseStep 1933043 = 2899565) B2899565
theorem B4349357 : Blo 1931435 4349357 := bbase (se 3 (by rfl) ⟨815504, by rfl⟩ : syracuseStep 4349357 = 1631009) (by norm_num)
theorem B2899571 : Blo 1931435 2899571 := bstep (se 1 (by rfl) ⟨2174678, by rfl⟩ : syracuseStep 2899571 = 4349357) B4349357
theorem B1933047 : Blo 1931435 1933047 := bstep (se 1 (by rfl) ⟨1449785, by rfl⟩ : syracuseStep 1933047 = 2899571) B2899571
theorem B2939141 : Blo 1931435 2939141 := bbase (se 4 (by rfl) ⟨275544, by rfl⟩ : syracuseStep 2939141 = 551089) (by norm_num)
theorem B1959427 : Blo 1931435 1959427 := bstep (se 1 (by rfl) ⟨1469570, by rfl⟩ : syracuseStep 1959427 = 2939141) B2939141
theorem B2612569 : Blo 1931435 2612569 := bstep (se 2 (by rfl) ⟨979713, by rfl⟩ : syracuseStep 2612569 = 1959427) B1959427
theorem B3483425 : Blo 1931435 3483425 := bstep (se 2 (by rfl) ⟨1306284, by rfl⟩ : syracuseStep 3483425 = 2612569) B2612569
theorem B2322283 : Blo 1931435 2322283 := bstep (se 1 (by rfl) ⟨1741712, by rfl⟩ : syracuseStep 2322283 = 3483425) B3483425
theorem B3096377 : Blo 1931435 3096377 := bstep (se 2 (by rfl) ⟨1161141, by rfl⟩ : syracuseStep 3096377 = 2322283) B2322283
theorem B2064251 : Blo 1931435 2064251 := bstep (se 1 (by rfl) ⟨1548188, by rfl⟩ : syracuseStep 2064251 = 3096377) B3096377
theorem B5504669 : Blo 1931435 5504669 := bstep (se 3 (by rfl) ⟨1032125, by rfl⟩ : syracuseStep 5504669 = 2064251) B2064251
theorem B3669779 : Blo 1931435 3669779 := bstep (se 1 (by rfl) ⟨2752334, by rfl⟩ : syracuseStep 3669779 = 5504669) B5504669
theorem B2446519 : Blo 1931435 2446519 := bstep (se 1 (by rfl) ⟨1834889, by rfl⟩ : syracuseStep 2446519 = 3669779) B3669779
theorem B3262025 : Blo 1931435 3262025 := bstep (se 2 (by rfl) ⟨1223259, by rfl⟩ : syracuseStep 3262025 = 2446519) B2446519
theorem B2174683 : Blo 1931435 2174683 := bstep (se 1 (by rfl) ⟨1631012, by rfl⟩ : syracuseStep 2174683 = 3262025) B3262025
theorem B2899577 : Blo 1931435 2899577 := bstep (se 2 (by rfl) ⟨1087341, by rfl⟩ : syracuseStep 2899577 = 2174683) B2174683
theorem B1933051 : Blo 1931435 1933051 := bstep (se 1 (by rfl) ⟨1449788, by rfl⟩ : syracuseStep 1933051 = 2899577) B2899577
theorem B5441941 : Blo 1931435 5441941 := bbase (se 6 (by rfl) ⟨127545, by rfl⟩ : syracuseStep 5441941 = 255091) (by norm_num)
theorem B7255921 : Blo 1931435 7255921 := bstep (se 2 (by rfl) ⟨2720970, by rfl⟩ : syracuseStep 7255921 = 5441941) B5441941
theorem B9674561 : Blo 1931435 9674561 := bstep (se 2 (by rfl) ⟨3627960, by rfl⟩ : syracuseStep 9674561 = 7255921) B7255921
theorem B6449707 : Blo 1931435 6449707 := bstep (se 1 (by rfl) ⟨4837280, by rfl⟩ : syracuseStep 6449707 = 9674561) B9674561
theorem B8599609 : Blo 1931435 8599609 := bstep (se 2 (by rfl) ⟨3224853, by rfl⟩ : syracuseStep 8599609 = 6449707) B6449707
theorem B45864581 : Blo 1931435 45864581 := bstep (se 4 (by rfl) ⟨4299804, by rfl⟩ : syracuseStep 45864581 = 8599609) B8599609
theorem B122305549 : Blo 1931435 122305549 := bstep (se 3 (by rfl) ⟨22932290, by rfl⟩ : syracuseStep 122305549 = 45864581) B45864581
theorem B163074065 : Blo 1931435 163074065 := bstep (se 2 (by rfl) ⟨61152774, by rfl⟩ : syracuseStep 163074065 = 122305549) B122305549
theorem B434864173 : Blo 1931435 434864173 := bstep (se 3 (by rfl) ⟨81537032, by rfl⟩ : syracuseStep 434864173 = 163074065) B163074065
theorem B579818897 : Blo 1931435 579818897 := bstep (se 2 (by rfl) ⟨217432086, by rfl⟩ : syracuseStep 579818897 = 434864173) B434864173
theorem B386545931 : Blo 1931435 386545931 := bstep (se 1 (by rfl) ⟨289909448, by rfl⟩ : syracuseStep 386545931 = 579818897) B579818897
theorem B257697287 : Blo 1931435 257697287 := bstep (se 1 (by rfl) ⟨193272965, by rfl⟩ : syracuseStep 257697287 = 386545931) B386545931
theorem B171798191 : Blo 1931435 171798191 := bstep (se 1 (by rfl) ⟨128848643, by rfl⟩ : syracuseStep 171798191 = 257697287) B257697287
theorem B114532127 : Blo 1931435 114532127 := bstep (se 1 (by rfl) ⟨85899095, by rfl⟩ : syracuseStep 114532127 = 171798191) B171798191
theorem B76354751 : Blo 1931435 76354751 := bstep (se 1 (by rfl) ⟨57266063, by rfl⟩ : syracuseStep 76354751 = 114532127) B114532127
theorem B203612669 : Blo 1931435 203612669 := bstep (se 3 (by rfl) ⟨38177375, by rfl⟩ : syracuseStep 203612669 = 76354751) B76354751
theorem B135741779 : Blo 1931435 135741779 := bstep (se 1 (by rfl) ⟨101806334, by rfl⟩ : syracuseStep 135741779 = 203612669) B203612669
theorem B90494519 : Blo 1931435 90494519 := bstep (se 1 (by rfl) ⟨67870889, by rfl⟩ : syracuseStep 90494519 = 135741779) B135741779
theorem B965274869 : Blo 1931435 965274869 := bstep (se 5 (by rfl) ⟨45247259, by rfl⟩ : syracuseStep 965274869 = 90494519) B90494519
theorem B643516579 : Blo 1931435 643516579 := bstep (se 1 (by rfl) ⟨482637434, by rfl⟩ : syracuseStep 643516579 = 965274869) B965274869
theorem B3432088421 : Blo 1931435 3432088421 := bstep (se 4 (by rfl) ⟨321758289, by rfl⟩ : syracuseStep 3432088421 = 643516579) B643516579
theorem B2288058947 : Blo 1931435 2288058947 := bstep (se 1 (by rfl) ⟨1716044210, by rfl⟩ : syracuseStep 2288058947 = 3432088421) B3432088421
theorem B1525372631 : Blo 1931435 1525372631 := bstep (se 1 (by rfl) ⟨1144029473, by rfl⟩ : syracuseStep 1525372631 = 2288058947) B2288058947
theorem B1016915087 : Blo 1931435 1016915087 := bstep (se 1 (by rfl) ⟨762686315, by rfl⟩ : syracuseStep 1016915087 = 1525372631) B1525372631
theorem B677943391 : Blo 1931435 677943391 := bstep (se 1 (by rfl) ⟨508457543, by rfl⟩ : syracuseStep 677943391 = 1016915087) B1016915087
theorem B903924521 : Blo 1931435 903924521 := bstep (se 2 (by rfl) ⟨338971695, by rfl⟩ : syracuseStep 903924521 = 677943391) B677943391
theorem B602616347 : Blo 1931435 602616347 := bstep (se 1 (by rfl) ⟨451962260, by rfl⟩ : syracuseStep 602616347 = 903924521) B903924521
theorem B401744231 : Blo 1931435 401744231 := bstep (se 1 (by rfl) ⟨301308173, by rfl⟩ : syracuseStep 401744231 = 602616347) B602616347
theorem B267829487 : Blo 1931435 267829487 := bstep (se 1 (by rfl) ⟨200872115, by rfl⟩ : syracuseStep 267829487 = 401744231) B401744231
theorem B178552991 : Blo 1931435 178552991 := bstep (se 1 (by rfl) ⟨133914743, by rfl⟩ : syracuseStep 178552991 = 267829487) B267829487
theorem B119035327 : Blo 1931435 119035327 := bstep (se 1 (by rfl) ⟨89276495, by rfl⟩ : syracuseStep 119035327 = 178552991) B178552991
theorem B158713769 : Blo 1931435 158713769 := bstep (se 2 (by rfl) ⟨59517663, by rfl⟩ : syracuseStep 158713769 = 119035327) B119035327
theorem B105809179 : Blo 1931435 105809179 := bstep (se 1 (by rfl) ⟨79356884, by rfl⟩ : syracuseStep 105809179 = 158713769) B158713769
theorem B141078905 : Blo 1931435 141078905 := bstep (se 2 (by rfl) ⟨52904589, by rfl⟩ : syracuseStep 141078905 = 105809179) B105809179
theorem B94052603 : Blo 1931435 94052603 := bstep (se 1 (by rfl) ⟨70539452, by rfl⟩ : syracuseStep 94052603 = 141078905) B141078905
theorem B62701735 : Blo 1931435 62701735 := bstep (se 1 (by rfl) ⟨47026301, by rfl⟩ : syracuseStep 62701735 = 94052603) B94052603
theorem B83602313 : Blo 1931435 83602313 := bstep (se 2 (by rfl) ⟨31350867, by rfl⟩ : syracuseStep 83602313 = 62701735) B62701735
theorem B55734875 : Blo 1931435 55734875 := bstep (se 1 (by rfl) ⟨41801156, by rfl⟩ : syracuseStep 55734875 = 83602313) B83602313
theorem B37156583 : Blo 1931435 37156583 := bstep (se 1 (by rfl) ⟨27867437, by rfl⟩ : syracuseStep 37156583 = 55734875) B55734875
theorem B24771055 : Blo 1931435 24771055 := bstep (se 1 (by rfl) ⟨18578291, by rfl⟩ : syracuseStep 24771055 = 37156583) B37156583
theorem B33028073 : Blo 1931435 33028073 := bstep (se 2 (by rfl) ⟨12385527, by rfl⟩ : syracuseStep 33028073 = 24771055) B24771055
theorem B22018715 : Blo 1931435 22018715 := bstep (se 1 (by rfl) ⟨16514036, by rfl⟩ : syracuseStep 22018715 = 33028073) B33028073
theorem B14679143 : Blo 1931435 14679143 := bstep (se 1 (by rfl) ⟨11009357, by rfl⟩ : syracuseStep 14679143 = 22018715) B22018715
theorem B9786095 : Blo 1931435 9786095 := bstep (se 1 (by rfl) ⟨7339571, by rfl⟩ : syracuseStep 9786095 = 14679143) B14679143
theorem B6524063 : Blo 1931435 6524063 := bstep (se 1 (by rfl) ⟨4893047, by rfl⟩ : syracuseStep 6524063 = 9786095) B9786095
theorem B4349375 : Blo 1931435 4349375 := bstep (se 1 (by rfl) ⟨3262031, by rfl⟩ : syracuseStep 4349375 = 6524063) B6524063
theorem B2899583 : Blo 1931435 2899583 := bstep (se 1 (by rfl) ⟨2174687, by rfl⟩ : syracuseStep 2899583 = 4349375) B4349375
theorem B1933055 : Blo 1931435 1933055 := bstep (se 1 (by rfl) ⟨1449791, by rfl⟩ : syracuseStep 1933055 = 2899583) B2899583
theorem B2899589 : Blo 1931435 2899589 := bbase (se 4 (by rfl) ⟨271836, by rfl⟩ : syracuseStep 2899589 = 543673) (by norm_num)
theorem B1933059 : Blo 1931435 1933059 := bstep (se 1 (by rfl) ⟨1449794, by rfl⟩ : syracuseStep 1933059 = 2899589) B2899589
theorem B3262045 : Blo 1931435 3262045 := bbase (se 3 (by rfl) ⟨611633, by rfl⟩ : syracuseStep 3262045 = 1223267) (by norm_num)
theorem B4349393 : Blo 1931435 4349393 := bstep (se 2 (by rfl) ⟨1631022, by rfl⟩ : syracuseStep 4349393 = 3262045) B3262045
theorem B2899595 : Blo 1931435 2899595 := bstep (se 1 (by rfl) ⟨2174696, by rfl⟩ : syracuseStep 2899595 = 4349393) B4349393
theorem B1933063 : Blo 1931435 1933063 := bstep (se 1 (by rfl) ⟨1449797, by rfl⟩ : syracuseStep 1933063 = 2899595) B2899595
theorem B2174701 : Blo 1931435 2174701 := bbase (se 3 (by rfl) ⟨407756, by rfl⟩ : syracuseStep 2174701 = 815513) (by norm_num)
theorem B2899601 : Blo 1931435 2899601 := bstep (se 2 (by rfl) ⟨1087350, by rfl⟩ : syracuseStep 2899601 = 2174701) B2174701
theorem B1933067 : Blo 1931435 1933067 := bstep (se 1 (by rfl) ⟨1449800, by rfl⟩ : syracuseStep 1933067 = 2899601) B2899601
theorem B6524117 : Blo 1931435 6524117 := bbase (se 7 (by rfl) ⟨76454, by rfl⟩ : syracuseStep 6524117 = 152909) (by norm_num)
theorem B4349411 : Blo 1931435 4349411 := bstep (se 1 (by rfl) ⟨3262058, by rfl⟩ : syracuseStep 4349411 = 6524117) B6524117
theorem B2899607 : Blo 1931435 2899607 := bstep (se 1 (by rfl) ⟨2174705, by rfl⟩ : syracuseStep 2899607 = 4349411) B4349411
theorem B1933071 : Blo 1931435 1933071 := bstep (se 1 (by rfl) ⟨1449803, by rfl⟩ : syracuseStep 1933071 = 2899607) B2899607
theorem B2899613 : Blo 1931435 2899613 := bbase (se 3 (by rfl) ⟨543677, by rfl⟩ : syracuseStep 2899613 = 1087355) (by norm_num)
theorem B1933075 : Blo 1931435 1933075 := bstep (se 1 (by rfl) ⟨1449806, by rfl⟩ : syracuseStep 1933075 = 2899613) B2899613
theorem B4349429 : Blo 1931435 4349429 := bbase (se 5 (by rfl) ⟨203879, by rfl⟩ : syracuseStep 4349429 = 407759) (by norm_num)
theorem B2899619 : Blo 1931435 2899619 := bstep (se 1 (by rfl) ⟨2174714, by rfl⟩ : syracuseStep 2899619 = 4349429) B4349429
theorem B1933079 : Blo 1931435 1933079 := bstep (se 1 (by rfl) ⟨1449809, by rfl⟩ : syracuseStep 1933079 = 2899619) B2899619
theorem B3719909 : Blo 1931435 3719909 := bbase (se 4 (by rfl) ⟨348741, by rfl⟩ : syracuseStep 3719909 = 697483) (by norm_num)
theorem B9919757 : Blo 1931435 9919757 := bstep (se 3 (by rfl) ⟨1859954, by rfl⟩ : syracuseStep 9919757 = 3719909) B3719909
theorem B6613171 : Blo 1931435 6613171 := bstep (se 1 (by rfl) ⟨4959878, by rfl⟩ : syracuseStep 6613171 = 9919757) B9919757
theorem B35270245 : Blo 1931435 35270245 := bstep (se 4 (by rfl) ⟨3306585, by rfl⟩ : syracuseStep 35270245 = 6613171) B6613171
theorem B47026993 : Blo 1931435 47026993 := bstep (se 2 (by rfl) ⟨17635122, by rfl⟩ : syracuseStep 47026993 = 35270245) B35270245
theorem B62702657 : Blo 1931435 62702657 := bstep (se 2 (by rfl) ⟨23513496, by rfl⟩ : syracuseStep 62702657 = 47026993) B47026993
theorem B41801771 : Blo 1931435 41801771 := bstep (se 1 (by rfl) ⟨31351328, by rfl⟩ : syracuseStep 41801771 = 62702657) B62702657
theorem B27867847 : Blo 1931435 27867847 := bstep (se 1 (by rfl) ⟨20900885, by rfl⟩ : syracuseStep 27867847 = 41801771) B41801771
theorem B37157129 : Blo 1931435 37157129 := bstep (se 2 (by rfl) ⟨13933923, by rfl⟩ : syracuseStep 37157129 = 27867847) B27867847
theorem B24771419 : Blo 1931435 24771419 := bstep (se 1 (by rfl) ⟨18578564, by rfl⟩ : syracuseStep 24771419 = 37157129) B37157129
theorem B16514279 : Blo 1931435 16514279 := bstep (se 1 (by rfl) ⟨12385709, by rfl⟩ : syracuseStep 16514279 = 24771419) B24771419
theorem B11009519 : Blo 1931435 11009519 := bstep (se 1 (by rfl) ⟨8257139, by rfl⟩ : syracuseStep 11009519 = 16514279) B16514279
theorem B7339679 : Blo 1931435 7339679 := bstep (se 1 (by rfl) ⟨5504759, by rfl⟩ : syracuseStep 7339679 = 11009519) B11009519
theorem B4893119 : Blo 1931435 4893119 := bstep (se 1 (by rfl) ⟨3669839, by rfl⟩ : syracuseStep 4893119 = 7339679) B7339679
theorem B3262079 : Blo 1931435 3262079 := bstep (se 1 (by rfl) ⟨2446559, by rfl⟩ : syracuseStep 3262079 = 4893119) B4893119
theorem B2174719 : Blo 1931435 2174719 := bstep (se 1 (by rfl) ⟨1631039, by rfl⟩ : syracuseStep 2174719 = 3262079) B3262079
theorem B2899625 : Blo 1931435 2899625 := bstep (se 2 (by rfl) ⟨1087359, by rfl⟩ : syracuseStep 2899625 = 2174719) B2174719
theorem B1933083 : Blo 1931435 1933083 := bstep (se 1 (by rfl) ⟨1449812, by rfl⟩ : syracuseStep 1933083 = 2899625) B2899625
theorem B2064289 : Blo 1931435 2064289 := bbase (se 2 (by rfl) ⟨774108, by rfl⟩ : syracuseStep 2064289 = 1548217) (by norm_num)
theorem B2752385 : Blo 1931435 2752385 := bstep (se 2 (by rfl) ⟨1032144, by rfl⟩ : syracuseStep 2752385 = 2064289) B2064289
theorem B7339693 : Blo 1931435 7339693 := bstep (se 3 (by rfl) ⟨1376192, by rfl⟩ : syracuseStep 7339693 = 2752385) B2752385
theorem B9786257 : Blo 1931435 9786257 := bstep (se 2 (by rfl) ⟨3669846, by rfl⟩ : syracuseStep 9786257 = 7339693) B7339693
theorem B6524171 : Blo 1931435 6524171 := bstep (se 1 (by rfl) ⟨4893128, by rfl⟩ : syracuseStep 6524171 = 9786257) B9786257
theorem B4349447 : Blo 1931435 4349447 := bstep (se 1 (by rfl) ⟨3262085, by rfl⟩ : syracuseStep 4349447 = 6524171) B6524171
theorem B2899631 : Blo 1931435 2899631 := bstep (se 1 (by rfl) ⟨2174723, by rfl⟩ : syracuseStep 2899631 = 4349447) B4349447
theorem B1933087 : Blo 1931435 1933087 := bstep (se 1 (by rfl) ⟨1449815, by rfl⟩ : syracuseStep 1933087 = 2899631) B2899631
theorem B2899637 : Blo 1931435 2899637 := bbase (se 5 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 2899637 = 271841) (by norm_num)
theorem B1933091 : Blo 1931435 1933091 := bstep (se 1 (by rfl) ⟨1449818, by rfl⟩ : syracuseStep 1933091 = 2899637) B2899637
theorem B4893149 : Blo 1931435 4893149 := bbase (se 3 (by rfl) ⟨917465, by rfl⟩ : syracuseStep 4893149 = 1834931) (by norm_num)
theorem B3262099 : Blo 1931435 3262099 := bstep (se 1 (by rfl) ⟨2446574, by rfl⟩ : syracuseStep 3262099 = 4893149) B4893149
theorem B4349465 : Blo 1931435 4349465 := bstep (se 2 (by rfl) ⟨1631049, by rfl⟩ : syracuseStep 4349465 = 3262099) B3262099
theorem B2899643 : Blo 1931435 2899643 := bstep (se 1 (by rfl) ⟨2174732, by rfl⟩ : syracuseStep 2899643 = 4349465) B4349465
theorem B1933095 : Blo 1931435 1933095 := bstep (se 1 (by rfl) ⟨1449821, by rfl⟩ : syracuseStep 1933095 = 2899643) B2899643
theorem B2174737 : Blo 1931435 2174737 := bbase (se 2 (by rfl) ⟨815526, by rfl⟩ : syracuseStep 2174737 = 1631053) (by norm_num)
theorem B2899649 : Blo 1931435 2899649 := bstep (se 2 (by rfl) ⟨1087368, by rfl⟩ : syracuseStep 2899649 = 2174737) B2174737
theorem B1933099 : Blo 1931435 1933099 := bstep (se 1 (by rfl) ⟨1449824, by rfl⟩ : syracuseStep 1933099 = 2899649) B2899649
theorem B3669877 : Blo 1931435 3669877 := bbase (se 5 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 3669877 = 344051) (by norm_num)
theorem B4893169 : Blo 1931435 4893169 := bstep (se 2 (by rfl) ⟨1834938, by rfl⟩ : syracuseStep 4893169 = 3669877) B3669877
theorem B6524225 : Blo 1931435 6524225 := bstep (se 2 (by rfl) ⟨2446584, by rfl⟩ : syracuseStep 6524225 = 4893169) B4893169
theorem B4349483 : Blo 1931435 4349483 := bstep (se 1 (by rfl) ⟨3262112, by rfl⟩ : syracuseStep 4349483 = 6524225) B6524225
theorem B2899655 : Blo 1931435 2899655 := bstep (se 1 (by rfl) ⟨2174741, by rfl⟩ : syracuseStep 2899655 = 4349483) B4349483
theorem B1933103 : Blo 1931435 1933103 := bstep (se 1 (by rfl) ⟨1449827, by rfl⟩ : syracuseStep 1933103 = 2899655) B2899655
theorem B2899661 : Blo 1931435 2899661 := bbase (se 3 (by rfl) ⟨543686, by rfl⟩ : syracuseStep 2899661 = 1087373) (by norm_num)
theorem B1933107 : Blo 1931435 1933107 := bstep (se 1 (by rfl) ⟨1449830, by rfl⟩ : syracuseStep 1933107 = 2899661) B2899661
theorem B4349501 : Blo 1931435 4349501 := bbase (se 3 (by rfl) ⟨815531, by rfl⟩ : syracuseStep 4349501 = 1631063) (by norm_num)
theorem B2899667 : Blo 1931435 2899667 := bstep (se 1 (by rfl) ⟨2174750, by rfl⟩ : syracuseStep 2899667 = 4349501) B4349501
theorem B1933111 : Blo 1931435 1933111 := bstep (se 1 (by rfl) ⟨1449833, by rfl⟩ : syracuseStep 1933111 = 2899667) B2899667
theorem B3262133 : Blo 1931435 3262133 := bbase (se 5 (by rfl) ⟨152912, by rfl⟩ : syracuseStep 3262133 = 305825) (by norm_num)
theorem B2174755 : Blo 1931435 2174755 := bstep (se 1 (by rfl) ⟨1631066, by rfl⟩ : syracuseStep 2174755 = 3262133) B3262133
theorem B2899673 : Blo 1931435 2899673 := bstep (se 2 (by rfl) ⟨1087377, by rfl⟩ : syracuseStep 2899673 = 2174755) B2174755
theorem B1933115 : Blo 1931435 1933115 := bstep (se 1 (by rfl) ⟨1449836, by rfl⟩ : syracuseStep 1933115 = 2899673) B2899673
theorem B3096485 : Blo 1931435 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B2064323 : Blo 1931435 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B5504861 : Blo 1931435 5504861 := bstep (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) B2064323
theorem B14679629 : Blo 1931435 14679629 := bstep (se 3 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 14679629 = 5504861) B5504861
theorem B9786419 : Blo 1931435 9786419 := bstep (se 1 (by rfl) ⟨7339814, by rfl⟩ : syracuseStep 9786419 = 14679629) B14679629
theorem B6524279 : Blo 1931435 6524279 := bstep (se 1 (by rfl) ⟨4893209, by rfl⟩ : syracuseStep 6524279 = 9786419) B9786419
theorem B4349519 : Blo 1931435 4349519 := bstep (se 1 (by rfl) ⟨3262139, by rfl⟩ : syracuseStep 4349519 = 6524279) B6524279
theorem B2899679 : Blo 1931435 2899679 := bstep (se 1 (by rfl) ⟨2174759, by rfl⟩ : syracuseStep 2899679 = 4349519) B4349519
theorem B1933119 : Blo 1931435 1933119 := bstep (se 1 (by rfl) ⟨1449839, by rfl⟩ : syracuseStep 1933119 = 2899679) B2899679
theorem B2899685 : Blo 1931435 2899685 := bbase (se 4 (by rfl) ⟨271845, by rfl⟩ : syracuseStep 2899685 = 543691) (by norm_num)
theorem B1933123 : Blo 1931435 1933123 := bstep (se 1 (by rfl) ⟨1449842, by rfl⟩ : syracuseStep 1933123 = 2899685) B2899685
theorem B5504885 : Blo 1931435 5504885 := bbase (se 5 (by rfl) ⟨258041, by rfl⟩ : syracuseStep 5504885 = 516083) (by norm_num)
theorem B3669923 : Blo 1931435 3669923 := bstep (se 1 (by rfl) ⟨2752442, by rfl⟩ : syracuseStep 3669923 = 5504885) B5504885
theorem B2446615 : Blo 1931435 2446615 := bstep (se 1 (by rfl) ⟨1834961, by rfl⟩ : syracuseStep 2446615 = 3669923) B3669923
theorem B3262153 : Blo 1931435 3262153 := bstep (se 2 (by rfl) ⟨1223307, by rfl⟩ : syracuseStep 3262153 = 2446615) B2446615
theorem B4349537 : Blo 1931435 4349537 := bstep (se 2 (by rfl) ⟨1631076, by rfl⟩ : syracuseStep 4349537 = 3262153) B3262153
theorem B2899691 : Blo 1931435 2899691 := bstep (se 1 (by rfl) ⟨2174768, by rfl⟩ : syracuseStep 2899691 = 4349537) B4349537
theorem B1933127 : Blo 1931435 1933127 := bstep (se 1 (by rfl) ⟨1449845, by rfl⟩ : syracuseStep 1933127 = 2899691) B2899691
theorem B2174773 : Blo 1931435 2174773 := bbase (se 5 (by rfl) ⟨101942, by rfl⟩ : syracuseStep 2174773 = 203885) (by norm_num)
theorem B2899697 : Blo 1931435 2899697 := bstep (se 2 (by rfl) ⟨1087386, by rfl⟩ : syracuseStep 2899697 = 2174773) B2174773
theorem B1933131 : Blo 1931435 1933131 := bstep (se 1 (by rfl) ⟨1449848, by rfl⟩ : syracuseStep 1933131 = 2899697) B2899697
theorem B2446625 : Blo 1931435 2446625 := bbase (se 2 (by rfl) ⟨917484, by rfl⟩ : syracuseStep 2446625 = 1834969) (by norm_num)
theorem B6524333 : Blo 1931435 6524333 := bstep (se 3 (by rfl) ⟨1223312, by rfl⟩ : syracuseStep 6524333 = 2446625) B2446625
theorem B4349555 : Blo 1931435 4349555 := bstep (se 1 (by rfl) ⟨3262166, by rfl⟩ : syracuseStep 4349555 = 6524333) B6524333
theorem B2899703 : Blo 1931435 2899703 := bstep (se 1 (by rfl) ⟨2174777, by rfl⟩ : syracuseStep 2899703 = 4349555) B4349555
theorem B1933135 : Blo 1931435 1933135 := bstep (se 1 (by rfl) ⟨1449851, by rfl⟩ : syracuseStep 1933135 = 2899703) B2899703
theorem B2899709 : Blo 1931435 2899709 := bbase (se 3 (by rfl) ⟨543695, by rfl⟩ : syracuseStep 2899709 = 1087391) (by norm_num)
theorem B1933139 : Blo 1931435 1933139 := bstep (se 1 (by rfl) ⟨1449854, by rfl⟩ : syracuseStep 1933139 = 2899709) B2899709
theorem B4349573 : Blo 1931435 4349573 := bbase (se 4 (by rfl) ⟨407772, by rfl⟩ : syracuseStep 4349573 = 815545) (by norm_num)
theorem B2899715 : Blo 1931435 2899715 := bstep (se 1 (by rfl) ⟨2174786, by rfl⟩ : syracuseStep 2899715 = 4349573) B4349573
theorem B1933143 : Blo 1931435 1933143 := bstep (se 1 (by rfl) ⟨1449857, by rfl⟩ : syracuseStep 1933143 = 2899715) B2899715
theorem B6193061 : Blo 1931435 6193061 := bbase (se 4 (by rfl) ⟨580599, by rfl⟩ : syracuseStep 6193061 = 1161199) (by norm_num)
theorem B4128707 : Blo 1931435 4128707 := bstep (se 1 (by rfl) ⟨3096530, by rfl⟩ : syracuseStep 4128707 = 6193061) B6193061
theorem B2752471 : Blo 1931435 2752471 := bstep (se 1 (by rfl) ⟨2064353, by rfl⟩ : syracuseStep 2752471 = 4128707) B4128707
theorem B3669961 : Blo 1931435 3669961 := bstep (se 2 (by rfl) ⟨1376235, by rfl⟩ : syracuseStep 3669961 = 2752471) B2752471
theorem B4893281 : Blo 1931435 4893281 := bstep (se 2 (by rfl) ⟨1834980, by rfl⟩ : syracuseStep 4893281 = 3669961) B3669961
theorem B3262187 : Blo 1931435 3262187 := bstep (se 1 (by rfl) ⟨2446640, by rfl⟩ : syracuseStep 3262187 = 4893281) B4893281
theorem B2174791 : Blo 1931435 2174791 := bstep (se 1 (by rfl) ⟨1631093, by rfl⟩ : syracuseStep 2174791 = 3262187) B3262187
theorem B2899721 : Blo 1931435 2899721 := bstep (se 2 (by rfl) ⟨1087395, by rfl⟩ : syracuseStep 2899721 = 2174791) B2174791
theorem B1933147 : Blo 1931435 1933147 := bstep (se 1 (by rfl) ⟨1449860, by rfl⟩ : syracuseStep 1933147 = 2899721) B2899721
theorem B9786581 : Blo 1931435 9786581 := bbase (se 7 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 9786581 = 229373) (by norm_num)
theorem B6524387 : Blo 1931435 6524387 := bstep (se 1 (by rfl) ⟨4893290, by rfl⟩ : syracuseStep 6524387 = 9786581) B9786581
theorem B4349591 : Blo 1931435 4349591 := bstep (se 1 (by rfl) ⟨3262193, by rfl⟩ : syracuseStep 4349591 = 6524387) B6524387
theorem B2899727 : Blo 1931435 2899727 := bstep (se 1 (by rfl) ⟨2174795, by rfl⟩ : syracuseStep 2899727 = 4349591) B4349591
theorem B1933151 : Blo 1931435 1933151 := bstep (se 1 (by rfl) ⟨1449863, by rfl⟩ : syracuseStep 1933151 = 2899727) B2899727
theorem B2899733 : Blo 1931435 2899733 := bbase (se 6 (by rfl) ⟨67962, by rfl⟩ : syracuseStep 2899733 = 135925) (by norm_num)
theorem B1933155 : Blo 1931435 1933155 := bstep (se 1 (by rfl) ⟨1449866, by rfl⟩ : syracuseStep 1933155 = 2899733) B2899733
theorem B3138797 : Blo 1931435 3138797 := bbase (se 3 (by rfl) ⟨588524, by rfl⟩ : syracuseStep 3138797 = 1177049) (by norm_num)
theorem B8370125 : Blo 1931435 8370125 := bstep (se 3 (by rfl) ⟨1569398, by rfl⟩ : syracuseStep 8370125 = 3138797) B3138797
theorem B5580083 : Blo 1931435 5580083 := bstep (se 1 (by rfl) ⟨4185062, by rfl⟩ : syracuseStep 5580083 = 8370125) B8370125
theorem B3720055 : Blo 1931435 3720055 := bstep (se 1 (by rfl) ⟨2790041, by rfl⟩ : syracuseStep 3720055 = 5580083) B5580083
theorem B4960073 : Blo 1931435 4960073 := bstep (se 2 (by rfl) ⟨1860027, by rfl⟩ : syracuseStep 4960073 = 3720055) B3720055
theorem B13226861 : Blo 1931435 13226861 := bstep (se 3 (by rfl) ⟨2480036, by rfl⟩ : syracuseStep 13226861 = 4960073) B4960073
theorem B35271629 : Blo 1931435 35271629 := bstep (se 3 (by rfl) ⟨6613430, by rfl⟩ : syracuseStep 35271629 = 13226861) B13226861
theorem B23514419 : Blo 1931435 23514419 := bstep (se 1 (by rfl) ⟨17635814, by rfl⟩ : syracuseStep 23514419 = 35271629) B35271629
theorem B62705117 : Blo 1931435 62705117 := bstep (se 3 (by rfl) ⟨11757209, by rfl⟩ : syracuseStep 62705117 = 23514419) B23514419
theorem B41803411 : Blo 1931435 41803411 := bstep (se 1 (by rfl) ⟨31352558, by rfl⟩ : syracuseStep 41803411 = 62705117) B62705117
theorem B55737881 : Blo 1931435 55737881 := bstep (se 2 (by rfl) ⟨20901705, by rfl⟩ : syracuseStep 55737881 = 41803411) B41803411
theorem B37158587 : Blo 1931435 37158587 := bstep (se 1 (by rfl) ⟨27868940, by rfl⟩ : syracuseStep 37158587 = 55737881) B55737881
theorem B24772391 : Blo 1931435 24772391 := bstep (se 1 (by rfl) ⟨18579293, by rfl⟩ : syracuseStep 24772391 = 37158587) B37158587
theorem B16514927 : Blo 1931435 16514927 := bstep (se 1 (by rfl) ⟨12386195, by rfl⟩ : syracuseStep 16514927 = 24772391) B24772391
theorem B11009951 : Blo 1931435 11009951 := bstep (se 1 (by rfl) ⟨8257463, by rfl⟩ : syracuseStep 11009951 = 16514927) B16514927
theorem B7339967 : Blo 1931435 7339967 := bstep (se 1 (by rfl) ⟨5504975, by rfl⟩ : syracuseStep 7339967 = 11009951) B11009951
theorem B4893311 : Blo 1931435 4893311 := bstep (se 1 (by rfl) ⟨3669983, by rfl⟩ : syracuseStep 4893311 = 7339967) B7339967
theorem B3262207 : Blo 1931435 3262207 := bstep (se 1 (by rfl) ⟨2446655, by rfl⟩ : syracuseStep 3262207 = 4893311) B4893311
theorem B4349609 : Blo 1931435 4349609 := bstep (se 2 (by rfl) ⟨1631103, by rfl⟩ : syracuseStep 4349609 = 3262207) B3262207
theorem B2899739 : Blo 1931435 2899739 := bstep (se 1 (by rfl) ⟨2174804, by rfl⟩ : syracuseStep 2899739 = 4349609) B4349609
theorem B1933159 : Blo 1931435 1933159 := bstep (se 1 (by rfl) ⟨1449869, by rfl⟩ : syracuseStep 1933159 = 2899739) B2899739
theorem B2174809 : Blo 1931435 2174809 := bbase (se 2 (by rfl) ⟨815553, by rfl⟩ : syracuseStep 2174809 = 1631107) (by norm_num)
theorem B2899745 : Blo 1931435 2899745 := bstep (se 2 (by rfl) ⟨1087404, by rfl⟩ : syracuseStep 2899745 = 2174809) B2174809
theorem B1933163 : Blo 1931435 1933163 := bstep (se 1 (by rfl) ⟨1449872, by rfl⟩ : syracuseStep 1933163 = 2899745) B2899745
theorem B4128749 : Blo 1931435 4128749 := bbase (se 3 (by rfl) ⟨774140, by rfl⟩ : syracuseStep 4128749 = 1548281) (by norm_num)
theorem B2752499 : Blo 1931435 2752499 := bstep (se 1 (by rfl) ⟨2064374, by rfl⟩ : syracuseStep 2752499 = 4128749) B4128749
theorem B7339997 : Blo 1931435 7339997 := bstep (se 3 (by rfl) ⟨1376249, by rfl⟩ : syracuseStep 7339997 = 2752499) B2752499
theorem B4893331 : Blo 1931435 4893331 := bstep (se 1 (by rfl) ⟨3669998, by rfl⟩ : syracuseStep 4893331 = 7339997) B7339997
theorem B6524441 : Blo 1931435 6524441 := bstep (se 2 (by rfl) ⟨2446665, by rfl⟩ : syracuseStep 6524441 = 4893331) B4893331
theorem B4349627 : Blo 1931435 4349627 := bstep (se 1 (by rfl) ⟨3262220, by rfl⟩ : syracuseStep 4349627 = 6524441) B6524441
theorem B2899751 : Blo 1931435 2899751 := bstep (se 1 (by rfl) ⟨2174813, by rfl⟩ : syracuseStep 2899751 = 4349627) B4349627
theorem B1933167 : Blo 1931435 1933167 := bstep (se 1 (by rfl) ⟨1449875, by rfl⟩ : syracuseStep 1933167 = 2899751) B2899751
theorem B2899757 : Blo 1931435 2899757 := bbase (se 3 (by rfl) ⟨543704, by rfl⟩ : syracuseStep 2899757 = 1087409) (by norm_num)
theorem B1933171 : Blo 1931435 1933171 := bstep (se 1 (by rfl) ⟨1449878, by rfl⟩ : syracuseStep 1933171 = 2899757) B2899757
theorem B4349645 : Blo 1931435 4349645 := bbase (se 3 (by rfl) ⟨815558, by rfl⟩ : syracuseStep 4349645 = 1631117) (by norm_num)
theorem B2899763 : Blo 1931435 2899763 := bstep (se 1 (by rfl) ⟨2174822, by rfl⟩ : syracuseStep 2899763 = 4349645) B4349645
theorem B1933175 : Blo 1931435 1933175 := bstep (se 1 (by rfl) ⟨1449881, by rfl⟩ : syracuseStep 1933175 = 2899763) B2899763
theorem B2446681 : Blo 1931435 2446681 := bbase (se 2 (by rfl) ⟨917505, by rfl⟩ : syracuseStep 2446681 = 1835011) (by norm_num)
theorem B3262241 : Blo 1931435 3262241 := bstep (se 2 (by rfl) ⟨1223340, by rfl⟩ : syracuseStep 3262241 = 2446681) B2446681
theorem B2174827 : Blo 1931435 2174827 := bstep (se 1 (by rfl) ⟨1631120, by rfl⟩ : syracuseStep 2174827 = 3262241) B3262241
theorem B2899769 : Blo 1931435 2899769 := bstep (se 2 (by rfl) ⟨1087413, by rfl⟩ : syracuseStep 2899769 = 2174827) B2174827
theorem B1933179 : Blo 1931435 1933179 := bstep (se 1 (by rfl) ⟨1449884, by rfl⟩ : syracuseStep 1933179 = 2899769) B2899769
theorem B3483661 : Blo 1931435 3483661 := bbase (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) (by norm_num)
theorem B4644881 : Blo 1931435 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B3096587 : Blo 1931435 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B8257565 : Blo 1931435 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B22020173 : Blo 1931435 22020173 := bstep (se 3 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 22020173 = 8257565) B8257565
theorem B14680115 : Blo 1931435 14680115 := bstep (se 1 (by rfl) ⟨11010086, by rfl⟩ : syracuseStep 14680115 = 22020173) B22020173
theorem B9786743 : Blo 1931435 9786743 := bstep (se 1 (by rfl) ⟨7340057, by rfl⟩ : syracuseStep 9786743 = 14680115) B14680115
theorem B6524495 : Blo 1931435 6524495 := bstep (se 1 (by rfl) ⟨4893371, by rfl⟩ : syracuseStep 6524495 = 9786743) B9786743
theorem B4349663 : Blo 1931435 4349663 := bstep (se 1 (by rfl) ⟨3262247, by rfl⟩ : syracuseStep 4349663 = 6524495) B6524495
theorem B2899775 : Blo 1931435 2899775 := bstep (se 1 (by rfl) ⟨2174831, by rfl⟩ : syracuseStep 2899775 = 4349663) B4349663
theorem B1933183 : Blo 1931435 1933183 := bstep (se 1 (by rfl) ⟨1449887, by rfl⟩ : syracuseStep 1933183 = 2899775) B2899775
theorem B2899781 : Blo 1931435 2899781 := bbase (se 4 (by rfl) ⟨271854, by rfl⟩ : syracuseStep 2899781 = 543709) (by norm_num)
theorem B1933187 : Blo 1931435 1933187 := bstep (se 1 (by rfl) ⟨1449890, by rfl⟩ : syracuseStep 1933187 = 2899781) B2899781
theorem B3262261 : Blo 1931435 3262261 := bbase (se 5 (by rfl) ⟨152918, by rfl⟩ : syracuseStep 3262261 = 305837) (by norm_num)
theorem B4349681 : Blo 1931435 4349681 := bstep (se 2 (by rfl) ⟨1631130, by rfl⟩ : syracuseStep 4349681 = 3262261) B3262261
theorem B2899787 : Blo 1931435 2899787 := bstep (se 1 (by rfl) ⟨2174840, by rfl⟩ : syracuseStep 2899787 = 4349681) B4349681
theorem B1933191 : Blo 1931435 1933191 := bstep (se 1 (by rfl) ⟨1449893, by rfl⟩ : syracuseStep 1933191 = 2899787) B2899787
theorem B2174845 : Blo 1931435 2174845 := bbase (se 3 (by rfl) ⟨407783, by rfl⟩ : syracuseStep 2174845 = 815567) (by norm_num)
theorem B2899793 : Blo 1931435 2899793 := bstep (se 2 (by rfl) ⟨1087422, by rfl⟩ : syracuseStep 2899793 = 2174845) B2174845
theorem B1933195 : Blo 1931435 1933195 := bstep (se 1 (by rfl) ⟨1449896, by rfl⟩ : syracuseStep 1933195 = 2899793) B2899793
theorem B6524549 : Blo 1931435 6524549 := bbase (se 4 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 6524549 = 1223353) (by norm_num)
theorem B4349699 : Blo 1931435 4349699 := bstep (se 1 (by rfl) ⟨3262274, by rfl⟩ : syracuseStep 4349699 = 6524549) B6524549
theorem B2899799 : Blo 1931435 2899799 := bstep (se 1 (by rfl) ⟨2174849, by rfl⟩ : syracuseStep 2899799 = 4349699) B4349699
theorem B1933199 : Blo 1931435 1933199 := bstep (se 1 (by rfl) ⟨1449899, by rfl⟩ : syracuseStep 1933199 = 2899799) B2899799
theorem B2899805 : Blo 1931435 2899805 := bbase (se 3 (by rfl) ⟨543713, by rfl⟩ : syracuseStep 2899805 = 1087427) (by norm_num)
theorem B1933203 : Blo 1931435 1933203 := bstep (se 1 (by rfl) ⟨1449902, by rfl⟩ : syracuseStep 1933203 = 2899805) B2899805
theorem B4349717 : Blo 1931435 4349717 := bbase (se 6 (by rfl) ⟨101946, by rfl⟩ : syracuseStep 4349717 = 203893) (by norm_num)
theorem B2899811 : Blo 1931435 2899811 := bstep (se 1 (by rfl) ⟨2174858, by rfl⟩ : syracuseStep 2899811 = 4349717) B4349717
theorem B1933207 : Blo 1931435 1933207 := bstep (se 1 (by rfl) ⟨1449905, by rfl⟩ : syracuseStep 1933207 = 2899811) B2899811
theorem B7340165 : Blo 1931435 7340165 := bbase (se 4 (by rfl) ⟨688140, by rfl⟩ : syracuseStep 7340165 = 1376281) (by norm_num)
theorem B4893443 : Blo 1931435 4893443 := bstep (se 1 (by rfl) ⟨3670082, by rfl⟩ : syracuseStep 4893443 = 7340165) B7340165
theorem B3262295 : Blo 1931435 3262295 := bstep (se 1 (by rfl) ⟨2446721, by rfl⟩ : syracuseStep 3262295 = 4893443) B4893443
theorem B2174863 : Blo 1931435 2174863 := bstep (se 1 (by rfl) ⟨1631147, by rfl⟩ : syracuseStep 2174863 = 3262295) B3262295
theorem B2899817 : Blo 1931435 2899817 := bstep (se 2 (by rfl) ⟨1087431, by rfl⟩ : syracuseStep 2899817 = 2174863) B2174863
theorem B1933211 : Blo 1931435 1933211 := bstep (se 1 (by rfl) ⟨1449908, by rfl⟩ : syracuseStep 1933211 = 2899817) B2899817
theorem B1986329 : Blo 1931435 1986329 := bbase (se 2 (by rfl) ⟨744873, by rfl⟩ : syracuseStep 1986329 = 1489747) (by norm_num)
theorem B5296877 : Blo 1931435 5296877 := bstep (se 3 (by rfl) ⟨993164, by rfl⟩ : syracuseStep 5296877 = 1986329) B1986329
theorem B3531251 : Blo 1931435 3531251 := bstep (se 1 (by rfl) ⟨2648438, by rfl⟩ : syracuseStep 3531251 = 5296877) B5296877
theorem B2354167 : Blo 1931435 2354167 := bstep (se 1 (by rfl) ⟨1765625, by rfl⟩ : syracuseStep 2354167 = 3531251) B3531251
theorem B12555557 : Blo 1931435 12555557 := bstep (se 4 (by rfl) ⟨1177083, by rfl⟩ : syracuseStep 12555557 = 2354167) B2354167
theorem B8370371 : Blo 1931435 8370371 := bstep (se 1 (by rfl) ⟨6277778, by rfl⟩ : syracuseStep 8370371 = 12555557) B12555557
theorem B5580247 : Blo 1931435 5580247 := bstep (se 1 (by rfl) ⟨4185185, by rfl⟩ : syracuseStep 5580247 = 8370371) B8370371
theorem B7440329 : Blo 1931435 7440329 := bstep (se 2 (by rfl) ⟨2790123, by rfl⟩ : syracuseStep 7440329 = 5580247) B5580247
theorem B4960219 : Blo 1931435 4960219 := bstep (se 1 (by rfl) ⟨3720164, by rfl⟩ : syracuseStep 4960219 = 7440329) B7440329
theorem B6613625 : Blo 1931435 6613625 := bstep (se 2 (by rfl) ⟨2480109, by rfl⟩ : syracuseStep 6613625 = 4960219) B4960219
theorem B4409083 : Blo 1931435 4409083 := bstep (se 1 (by rfl) ⟨3306812, by rfl⟩ : syracuseStep 4409083 = 6613625) B6613625
theorem B5878777 : Blo 1931435 5878777 := bstep (se 2 (by rfl) ⟨2204541, by rfl⟩ : syracuseStep 5878777 = 4409083) B4409083
theorem B7838369 : Blo 1931435 7838369 := bstep (se 2 (by rfl) ⟨2939388, by rfl⟩ : syracuseStep 7838369 = 5878777) B5878777
theorem B5225579 : Blo 1931435 5225579 := bstep (se 1 (by rfl) ⟨3919184, by rfl⟩ : syracuseStep 5225579 = 7838369) B7838369
theorem B3483719 : Blo 1931435 3483719 := bstep (se 1 (by rfl) ⟨2612789, by rfl⟩ : syracuseStep 3483719 = 5225579) B5225579
theorem B2322479 : Blo 1931435 2322479 := bstep (se 1 (by rfl) ⟨1741859, by rfl⟩ : syracuseStep 2322479 = 3483719) B3483719
theorem B6193277 : Blo 1931435 6193277 := bstep (se 3 (by rfl) ⟨1161239, by rfl⟩ : syracuseStep 6193277 = 2322479) B2322479
theorem B4128851 : Blo 1931435 4128851 := bstep (se 1 (by rfl) ⟨3096638, by rfl⟩ : syracuseStep 4128851 = 6193277) B6193277
theorem B11010269 : Blo 1931435 11010269 := bstep (se 3 (by rfl) ⟨2064425, by rfl⟩ : syracuseStep 11010269 = 4128851) B4128851
theorem B7340179 : Blo 1931435 7340179 := bstep (se 1 (by rfl) ⟨5505134, by rfl⟩ : syracuseStep 7340179 = 11010269) B11010269
theorem B9786905 : Blo 1931435 9786905 := bstep (se 2 (by rfl) ⟨3670089, by rfl⟩ : syracuseStep 9786905 = 7340179) B7340179
theorem B6524603 : Blo 1931435 6524603 := bstep (se 1 (by rfl) ⟨4893452, by rfl⟩ : syracuseStep 6524603 = 9786905) B9786905
theorem B4349735 : Blo 1931435 4349735 := bstep (se 1 (by rfl) ⟨3262301, by rfl⟩ : syracuseStep 4349735 = 6524603) B6524603
theorem B2899823 : Blo 1931435 2899823 := bstep (se 1 (by rfl) ⟨2174867, by rfl⟩ : syracuseStep 2899823 = 4349735) B4349735
theorem B1933215 : Blo 1931435 1933215 := bstep (se 1 (by rfl) ⟨1449911, by rfl⟩ : syracuseStep 1933215 = 2899823) B2899823
theorem B2899829 : Blo 1931435 2899829 := bbase (se 5 (by rfl) ⟨135929, by rfl⟩ : syracuseStep 2899829 = 271859) (by norm_num)
theorem B1933219 : Blo 1931435 1933219 := bstep (se 1 (by rfl) ⟨1449914, by rfl⟩ : syracuseStep 1933219 = 2899829) B2899829
theorem B4128869 : Blo 1931435 4128869 := bbase (se 4 (by rfl) ⟨387081, by rfl⟩ : syracuseStep 4128869 = 774163) (by norm_num)
theorem B2752579 : Blo 1931435 2752579 := bstep (se 1 (by rfl) ⟨2064434, by rfl⟩ : syracuseStep 2752579 = 4128869) B4128869
theorem B3670105 : Blo 1931435 3670105 := bstep (se 2 (by rfl) ⟨1376289, by rfl⟩ : syracuseStep 3670105 = 2752579) B2752579
theorem B4893473 : Blo 1931435 4893473 := bstep (se 2 (by rfl) ⟨1835052, by rfl⟩ : syracuseStep 4893473 = 3670105) B3670105
theorem B3262315 : Blo 1931435 3262315 := bstep (se 1 (by rfl) ⟨2446736, by rfl⟩ : syracuseStep 3262315 = 4893473) B4893473
theorem B4349753 : Blo 1931435 4349753 := bstep (se 2 (by rfl) ⟨1631157, by rfl⟩ : syracuseStep 4349753 = 3262315) B3262315
theorem B2899835 : Blo 1931435 2899835 := bstep (se 1 (by rfl) ⟨2174876, by rfl⟩ : syracuseStep 2899835 = 4349753) B4349753
theorem B1933223 : Blo 1931435 1933223 := bstep (se 1 (by rfl) ⟨1449917, by rfl⟩ : syracuseStep 1933223 = 2899835) B2899835
theorem B2174881 : Blo 1931435 2174881 := bbase (se 2 (by rfl) ⟨815580, by rfl⟩ : syracuseStep 2174881 = 1631161) (by norm_num)
theorem B2899841 : Blo 1931435 2899841 := bstep (se 2 (by rfl) ⟨1087440, by rfl⟩ : syracuseStep 2899841 = 2174881) B2174881
theorem B1933227 : Blo 1931435 1933227 := bstep (se 1 (by rfl) ⟨1449920, by rfl⟩ : syracuseStep 1933227 = 2899841) B2899841
theorem B4893493 : Blo 1931435 4893493 := bbase (se 5 (by rfl) ⟨229382, by rfl⟩ : syracuseStep 4893493 = 458765) (by norm_num)
theorem B6524657 : Blo 1931435 6524657 := bstep (se 2 (by rfl) ⟨2446746, by rfl⟩ : syracuseStep 6524657 = 4893493) B4893493
theorem B4349771 : Blo 1931435 4349771 := bstep (se 1 (by rfl) ⟨3262328, by rfl⟩ : syracuseStep 4349771 = 6524657) B6524657
theorem B2899847 : Blo 1931435 2899847 := bstep (se 1 (by rfl) ⟨2174885, by rfl⟩ : syracuseStep 2899847 = 4349771) B4349771
theorem B1933231 : Blo 1931435 1933231 := bstep (se 1 (by rfl) ⟨1449923, by rfl⟩ : syracuseStep 1933231 = 2899847) B2899847
theorem B2899853 : Blo 1931435 2899853 := bbase (se 3 (by rfl) ⟨543722, by rfl⟩ : syracuseStep 2899853 = 1087445) (by norm_num)
theorem B1933235 : Blo 1931435 1933235 := bstep (se 1 (by rfl) ⟨1449926, by rfl⟩ : syracuseStep 1933235 = 2899853) B2899853
theorem B4349789 : Blo 1931435 4349789 := bbase (se 3 (by rfl) ⟨815585, by rfl⟩ : syracuseStep 4349789 = 1631171) (by norm_num)
theorem B2899859 : Blo 1931435 2899859 := bstep (se 1 (by rfl) ⟨2174894, by rfl⟩ : syracuseStep 2899859 = 4349789) B4349789
theorem B1933239 : Blo 1931435 1933239 := bstep (se 1 (by rfl) ⟨1449929, by rfl⟩ : syracuseStep 1933239 = 2899859) B2899859
theorem B3262349 : Blo 1931435 3262349 := bbase (se 3 (by rfl) ⟨611690, by rfl⟩ : syracuseStep 3262349 = 1223381) (by norm_num)
theorem B2174899 : Blo 1931435 2174899 := bstep (se 1 (by rfl) ⟨1631174, by rfl⟩ : syracuseStep 2174899 = 3262349) B3262349
theorem B2899865 : Blo 1931435 2899865 := bstep (se 2 (by rfl) ⟨1087449, by rfl⟩ : syracuseStep 2899865 = 2174899) B2174899
theorem B1933243 : Blo 1931435 1933243 := bstep (se 1 (by rfl) ⟨1449932, by rfl⟩ : syracuseStep 1933243 = 2899865) B2899865
theorem B9290069 : Blo 1931435 9290069 := bbase (se 10 (by rfl) ⟨13608, by rfl⟩ : syracuseStep 9290069 = 27217) (by norm_num)
theorem B6193379 : Blo 1931435 6193379 := bstep (se 1 (by rfl) ⟨4645034, by rfl⟩ : syracuseStep 6193379 = 9290069) B9290069
theorem B16515677 : Blo 1931435 16515677 := bstep (se 3 (by rfl) ⟨3096689, by rfl⟩ : syracuseStep 16515677 = 6193379) B6193379
theorem B11010451 : Blo 1931435 11010451 := bstep (se 1 (by rfl) ⟨8257838, by rfl⟩ : syracuseStep 11010451 = 16515677) B16515677
theorem B14680601 : Blo 1931435 14680601 := bstep (se 2 (by rfl) ⟨5505225, by rfl⟩ : syracuseStep 14680601 = 11010451) B11010451
theorem B9787067 : Blo 1931435 9787067 := bstep (se 1 (by rfl) ⟨7340300, by rfl⟩ : syracuseStep 9787067 = 14680601) B14680601
theorem B6524711 : Blo 1931435 6524711 := bstep (se 1 (by rfl) ⟨4893533, by rfl⟩ : syracuseStep 6524711 = 9787067) B9787067
theorem B4349807 : Blo 1931435 4349807 := bstep (se 1 (by rfl) ⟨3262355, by rfl⟩ : syracuseStep 4349807 = 6524711) B6524711
theorem B2899871 : Blo 1931435 2899871 := bstep (se 1 (by rfl) ⟨2174903, by rfl⟩ : syracuseStep 2899871 = 4349807) B4349807
theorem B1933247 : Blo 1931435 1933247 := bstep (se 1 (by rfl) ⟨1449935, by rfl⟩ : syracuseStep 1933247 = 2899871) B2899871
theorem B2899877 : Blo 1931435 2899877 := bbase (se 4 (by rfl) ⟨271863, by rfl⟩ : syracuseStep 2899877 = 543727) (by norm_num)
theorem B1933251 : Blo 1931435 1933251 := bstep (se 1 (by rfl) ⟨1449938, by rfl⟩ : syracuseStep 1933251 = 2899877) B2899877
theorem B2446777 : Blo 1931435 2446777 := bbase (se 2 (by rfl) ⟨917541, by rfl⟩ : syracuseStep 2446777 = 1835083) (by norm_num)
theorem B3262369 : Blo 1931435 3262369 := bstep (se 2 (by rfl) ⟨1223388, by rfl⟩ : syracuseStep 3262369 = 2446777) B2446777
theorem B4349825 : Blo 1931435 4349825 := bstep (se 2 (by rfl) ⟨1631184, by rfl⟩ : syracuseStep 4349825 = 3262369) B3262369
theorem B2899883 : Blo 1931435 2899883 := bstep (se 1 (by rfl) ⟨2174912, by rfl⟩ : syracuseStep 2899883 = 4349825) B4349825
theorem B1933255 : Blo 1931435 1933255 := bstep (se 1 (by rfl) ⟨1449941, by rfl⟩ : syracuseStep 1933255 = 2899883) B2899883
theorem B2174917 : Blo 1931435 2174917 := bbase (se 4 (by rfl) ⟨203898, by rfl⟩ : syracuseStep 2174917 = 407797) (by norm_num)
theorem B2899889 : Blo 1931435 2899889 := bstep (se 2 (by rfl) ⟨1087458, by rfl⟩ : syracuseStep 2899889 = 2174917) B2174917
theorem B1933259 : Blo 1931435 1933259 := bstep (se 1 (by rfl) ⟨1449944, by rfl⟩ : syracuseStep 1933259 = 2899889) B2899889
theorem B3670181 : Blo 1931435 3670181 := bbase (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) (by norm_num)
theorem B2446787 : Blo 1931435 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B6524765 : Blo 1931435 6524765 := bstep (se 3 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 6524765 = 2446787) B2446787
theorem B4349843 : Blo 1931435 4349843 := bstep (se 1 (by rfl) ⟨3262382, by rfl⟩ : syracuseStep 4349843 = 6524765) B6524765
theorem B2899895 : Blo 1931435 2899895 := bstep (se 1 (by rfl) ⟨2174921, by rfl⟩ : syracuseStep 2899895 = 4349843) B4349843
theorem B1933263 : Blo 1931435 1933263 := bstep (se 1 (by rfl) ⟨1449947, by rfl⟩ : syracuseStep 1933263 = 2899895) B2899895
theorem B2899901 : Blo 1931435 2899901 := bbase (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) (by norm_num)
theorem B1933267 : Blo 1931435 1933267 := bstep (se 1 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 1933267 = 2899901) B2899901
theorem B4349861 : Blo 1931435 4349861 := bbase (se 4 (by rfl) ⟨407799, by rfl⟩ : syracuseStep 4349861 = 815599) (by norm_num)
theorem B2899907 : Blo 1931435 2899907 := bstep (se 1 (by rfl) ⟨2174930, by rfl⟩ : syracuseStep 2899907 = 4349861) B4349861
theorem B1933271 : Blo 1931435 1933271 := bstep (se 1 (by rfl) ⟨1449953, by rfl⟩ : syracuseStep 1933271 = 2899907) B2899907
theorem B4893605 : Blo 1931435 4893605 := bbase (se 4 (by rfl) ⟨458775, by rfl⟩ : syracuseStep 4893605 = 917551) (by norm_num)
theorem B3262403 : Blo 1931435 3262403 := bstep (se 1 (by rfl) ⟨2446802, by rfl⟩ : syracuseStep 3262403 = 4893605) B4893605
theorem B2174935 : Blo 1931435 2174935 := bstep (se 1 (by rfl) ⟨1631201, by rfl⟩ : syracuseStep 2174935 = 3262403) B3262403
theorem B2899913 : Blo 1931435 2899913 := bstep (se 2 (by rfl) ⟨1087467, by rfl⟩ : syracuseStep 2899913 = 2174935) B2174935
theorem B1933275 : Blo 1931435 1933275 := bstep (se 1 (by rfl) ⟨1449956, by rfl⟩ : syracuseStep 1933275 = 2899913) B2899913
theorem B5505317 : Blo 1931435 5505317 := bbase (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) (by norm_num)
theorem B3670211 : Blo 1931435 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B9787229 : Blo 1931435 9787229 := bstep (se 3 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 9787229 = 3670211) B3670211
theorem B6524819 : Blo 1931435 6524819 := bstep (se 1 (by rfl) ⟨4893614, by rfl⟩ : syracuseStep 6524819 = 9787229) B9787229
theorem B4349879 : Blo 1931435 4349879 := bstep (se 1 (by rfl) ⟨3262409, by rfl⟩ : syracuseStep 4349879 = 6524819) B6524819
theorem B2899919 : Blo 1931435 2899919 := bstep (se 1 (by rfl) ⟨2174939, by rfl⟩ : syracuseStep 2899919 = 4349879) B4349879
theorem B1933279 : Blo 1931435 1933279 := bstep (se 1 (by rfl) ⟨1449959, by rfl⟩ : syracuseStep 1933279 = 2899919) B2899919
theorem B2899925 : Blo 1931435 2899925 := bbase (se 7 (by rfl) ⟨33983, by rfl⟩ : syracuseStep 2899925 = 67967) (by norm_num)
theorem B1933283 : Blo 1931435 1933283 := bstep (se 1 (by rfl) ⟨1449962, by rfl⟩ : syracuseStep 1933283 = 2899925) B2899925
theorem B7340453 : Blo 1931435 7340453 := bbase (se 4 (by rfl) ⟨688167, by rfl⟩ : syracuseStep 7340453 = 1376335) (by norm_num)
theorem B4893635 : Blo 1931435 4893635 := bstep (se 1 (by rfl) ⟨3670226, by rfl⟩ : syracuseStep 4893635 = 7340453) B7340453
theorem B3262423 : Blo 1931435 3262423 := bstep (se 1 (by rfl) ⟨2446817, by rfl⟩ : syracuseStep 3262423 = 4893635) B4893635
theorem B4349897 : Blo 1931435 4349897 := bstep (se 2 (by rfl) ⟨1631211, by rfl⟩ : syracuseStep 4349897 = 3262423) B3262423
theorem B2899931 : Blo 1931435 2899931 := bstep (se 1 (by rfl) ⟨2174948, by rfl⟩ : syracuseStep 2899931 = 4349897) B4349897
theorem B1933287 : Blo 1931435 1933287 := bstep (se 1 (by rfl) ⟨1449965, by rfl⟩ : syracuseStep 1933287 = 2899931) B2899931
theorem B2174953 : Blo 1931435 2174953 := bbase (se 2 (by rfl) ⟨815607, by rfl⟩ : syracuseStep 2174953 = 1631215) (by norm_num)
theorem B2899937 : Blo 1931435 2899937 := bstep (se 2 (by rfl) ⟨1087476, by rfl⟩ : syracuseStep 2899937 = 2174953) B2174953
theorem B1933291 : Blo 1931435 1933291 := bstep (se 1 (by rfl) ⟨1449968, by rfl⟩ : syracuseStep 1933291 = 2899937) B2899937
theorem B3306949 : Blo 1931435 3306949 := bbase (se 4 (by rfl) ⟨310026, by rfl⟩ : syracuseStep 3306949 = 620053) (by norm_num)
theorem B17637061 : Blo 1931435 17637061 := bstep (se 4 (by rfl) ⟨1653474, by rfl⟩ : syracuseStep 17637061 = 3306949) B3306949
theorem B23516081 : Blo 1931435 23516081 := bstep (se 2 (by rfl) ⟨8818530, by rfl⟩ : syracuseStep 23516081 = 17637061) B17637061
theorem B15677387 : Blo 1931435 15677387 := bstep (se 1 (by rfl) ⟨11758040, by rfl⟩ : syracuseStep 15677387 = 23516081) B23516081
theorem B10451591 : Blo 1931435 10451591 := bstep (se 1 (by rfl) ⟨7838693, by rfl⟩ : syracuseStep 10451591 = 15677387) B15677387
theorem B6967727 : Blo 1931435 6967727 := bstep (se 1 (by rfl) ⟨5225795, by rfl⟩ : syracuseStep 6967727 = 10451591) B10451591
theorem B4645151 : Blo 1931435 4645151 := bstep (se 1 (by rfl) ⟨3483863, by rfl⟩ : syracuseStep 4645151 = 6967727) B6967727
theorem B3096767 : Blo 1931435 3096767 := bstep (se 1 (by rfl) ⟨2322575, by rfl⟩ : syracuseStep 3096767 = 4645151) B4645151
theorem B2064511 : Blo 1931435 2064511 := bstep (se 1 (by rfl) ⟨1548383, by rfl⟩ : syracuseStep 2064511 = 3096767) B3096767
theorem B11010725 : Blo 1931435 11010725 := bstep (se 4 (by rfl) ⟨1032255, by rfl⟩ : syracuseStep 11010725 = 2064511) B2064511
theorem B7340483 : Blo 1931435 7340483 := bstep (se 1 (by rfl) ⟨5505362, by rfl⟩ : syracuseStep 7340483 = 11010725) B11010725
theorem B4893655 : Blo 1931435 4893655 := bstep (se 1 (by rfl) ⟨3670241, by rfl⟩ : syracuseStep 4893655 = 7340483) B7340483
theorem B6524873 : Blo 1931435 6524873 := bstep (se 2 (by rfl) ⟨2446827, by rfl⟩ : syracuseStep 6524873 = 4893655) B4893655
theorem B4349915 : Blo 1931435 4349915 := bstep (se 1 (by rfl) ⟨3262436, by rfl⟩ : syracuseStep 4349915 = 6524873) B6524873
theorem B2899943 : Blo 1931435 2899943 := bstep (se 1 (by rfl) ⟨2174957, by rfl⟩ : syracuseStep 2899943 = 4349915) B4349915
theorem B1933295 : Blo 1931435 1933295 := bstep (se 1 (by rfl) ⟨1449971, by rfl⟩ : syracuseStep 1933295 = 2899943) B2899943
theorem B2899949 : Blo 1931435 2899949 := bbase (se 3 (by rfl) ⟨543740, by rfl⟩ : syracuseStep 2899949 = 1087481) (by norm_num)
theorem B1933299 : Blo 1931435 1933299 := bstep (se 1 (by rfl) ⟨1449974, by rfl⟩ : syracuseStep 1933299 = 2899949) B2899949
theorem B4349933 : Blo 1931435 4349933 := bbase (se 3 (by rfl) ⟨815612, by rfl⟩ : syracuseStep 4349933 = 1631225) (by norm_num)
theorem B2899955 : Blo 1931435 2899955 := bstep (se 1 (by rfl) ⟨2174966, by rfl⟩ : syracuseStep 2899955 = 4349933) B4349933
theorem B1933303 : Blo 1931435 1933303 := bstep (se 1 (by rfl) ⟨1449977, by rfl⟩ : syracuseStep 1933303 = 2899955) B2899955
theorem B4645181 : Blo 1931435 4645181 := bbase (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) (by norm_num)
theorem B3096787 : Blo 1931435 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B4129049 : Blo 1931435 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B2752699 : Blo 1931435 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B3670265 : Blo 1931435 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B2446843 : Blo 1931435 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B3262457 : Blo 1931435 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B2174971 : Blo 1931435 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B2899961 : Blo 1931435 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B1933307 : Blo 1931435 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B12246005 : Blo 1931435 12246005 := bbase (se 5 (by rfl) ⟨574031, by rfl⟩ : syracuseStep 12246005 = 1148063) (by norm_num)
theorem B8164003 : Blo 1931435 8164003 := bstep (se 1 (by rfl) ⟨6123002, by rfl⟩ : syracuseStep 8164003 = 12246005) B12246005
theorem B10885337 : Blo 1931435 10885337 := bstep (se 2 (by rfl) ⟨4082001, by rfl⟩ : syracuseStep 10885337 = 8164003) B8164003
theorem B7256891 : Blo 1931435 7256891 := bstep (se 1 (by rfl) ⟨5442668, by rfl⟩ : syracuseStep 7256891 = 10885337) B10885337
theorem B4837927 : Blo 1931435 4837927 := bstep (se 1 (by rfl) ⟨3628445, by rfl⟩ : syracuseStep 4837927 = 7256891) B7256891
theorem B6450569 : Blo 1931435 6450569 := bstep (se 2 (by rfl) ⟨2418963, by rfl⟩ : syracuseStep 6450569 = 4837927) B4837927
theorem B4300379 : Blo 1931435 4300379 := bstep (se 1 (by rfl) ⟨3225284, by rfl⟩ : syracuseStep 4300379 = 6450569) B6450569
theorem B2866919 : Blo 1931435 2866919 := bstep (se 1 (by rfl) ⟨2150189, by rfl⟩ : syracuseStep 2866919 = 4300379) B4300379
theorem B7645117 : Blo 1931435 7645117 := bstep (se 3 (by rfl) ⟨1433459, by rfl⟩ : syracuseStep 7645117 = 2866919) B2866919
theorem B10193489 : Blo 1931435 10193489 := bstep (se 2 (by rfl) ⟨3822558, by rfl⟩ : syracuseStep 10193489 = 7645117) B7645117
theorem B6795659 : Blo 1931435 6795659 := bstep (se 1 (by rfl) ⟨5096744, by rfl⟩ : syracuseStep 6795659 = 10193489) B10193489
theorem B4530439 : Blo 1931435 4530439 := bstep (se 1 (by rfl) ⟨3397829, by rfl⟩ : syracuseStep 4530439 = 6795659) B6795659
theorem B6040585 : Blo 1931435 6040585 := bstep (se 2 (by rfl) ⟨2265219, by rfl⟩ : syracuseStep 6040585 = 4530439) B4530439
theorem B32216453 : Blo 1931435 32216453 := bstep (se 4 (by rfl) ⟨3020292, by rfl⟩ : syracuseStep 32216453 = 6040585) B6040585
theorem B21477635 : Blo 1931435 21477635 := bstep (se 1 (by rfl) ⟨16108226, by rfl⟩ : syracuseStep 21477635 = 32216453) B32216453
theorem B14318423 : Blo 1931435 14318423 := bstep (se 1 (by rfl) ⟨10738817, by rfl⟩ : syracuseStep 14318423 = 21477635) B21477635
theorem B9545615 : Blo 1931435 9545615 := bstep (se 1 (by rfl) ⟨7159211, by rfl⟩ : syracuseStep 9545615 = 14318423) B14318423
theorem B6363743 : Blo 1931435 6363743 := bstep (se 1 (by rfl) ⟨4772807, by rfl⟩ : syracuseStep 6363743 = 9545615) B9545615
theorem B16969981 : Blo 1931435 16969981 := bstep (se 3 (by rfl) ⟨3181871, by rfl⟩ : syracuseStep 16969981 = 6363743) B6363743
theorem B22626641 : Blo 1931435 22626641 := bstep (se 2 (by rfl) ⟨8484990, by rfl⟩ : syracuseStep 22626641 = 16969981) B16969981
theorem B15084427 : Blo 1931435 15084427 := bstep (se 1 (by rfl) ⟨11313320, by rfl⟩ : syracuseStep 15084427 = 22626641) B22626641
theorem B20112569 : Blo 1931435 20112569 := bstep (se 2 (by rfl) ⟨7542213, by rfl⟩ : syracuseStep 20112569 = 15084427) B15084427
theorem B13408379 : Blo 1931435 13408379 := bstep (se 1 (by rfl) ⟨10056284, by rfl⟩ : syracuseStep 13408379 = 20112569) B20112569
theorem B8938919 : Blo 1931435 8938919 := bstep (se 1 (by rfl) ⟨6704189, by rfl⟩ : syracuseStep 8938919 = 13408379) B13408379
theorem B5959279 : Blo 1931435 5959279 := bstep (se 1 (by rfl) ⟨4469459, by rfl⟩ : syracuseStep 5959279 = 8938919) B8938919
theorem B7945705 : Blo 1931435 7945705 := bstep (se 2 (by rfl) ⟨2979639, by rfl⟩ : syracuseStep 7945705 = 5959279) B5959279
theorem B10594273 : Blo 1931435 10594273 := bstep (se 2 (by rfl) ⟨3972852, by rfl⟩ : syracuseStep 10594273 = 7945705) B7945705
theorem B14125697 : Blo 1931435 14125697 := bstep (se 2 (by rfl) ⟨5297136, by rfl⟩ : syracuseStep 14125697 = 10594273) B10594273
theorem B9417131 : Blo 1931435 9417131 := bstep (se 1 (by rfl) ⟨7062848, by rfl⟩ : syracuseStep 9417131 = 14125697) B14125697
theorem B6278087 : Blo 1931435 6278087 := bstep (se 1 (by rfl) ⟨4708565, by rfl⟩ : syracuseStep 6278087 = 9417131) B9417131
theorem B4185391 : Blo 1931435 4185391 := bstep (se 1 (by rfl) ⟨3139043, by rfl⟩ : syracuseStep 4185391 = 6278087) B6278087
theorem B5580521 : Blo 1931435 5580521 := bstep (se 2 (by rfl) ⟨2092695, by rfl⟩ : syracuseStep 5580521 = 4185391) B4185391
theorem B3720347 : Blo 1931435 3720347 := bstep (se 1 (by rfl) ⟨2790260, by rfl⟩ : syracuseStep 3720347 = 5580521) B5580521
theorem B2480231 : Blo 1931435 2480231 := bstep (se 1 (by rfl) ⟨1860173, by rfl⟩ : syracuseStep 2480231 = 3720347) B3720347
theorem B105823189 : Blo 1931435 105823189 := bstep (se 7 (by rfl) ⟨1240115, by rfl⟩ : syracuseStep 105823189 = 2480231) B2480231
theorem B564390341 : Blo 1931435 564390341 := bstep (se 4 (by rfl) ⟨52911594, by rfl⟩ : syracuseStep 564390341 = 105823189) B105823189
theorem B376260227 : Blo 1931435 376260227 := bstep (se 1 (by rfl) ⟨282195170, by rfl⟩ : syracuseStep 376260227 = 564390341) B564390341
theorem B250840151 : Blo 1931435 250840151 := bstep (se 1 (by rfl) ⟨188130113, by rfl⟩ : syracuseStep 250840151 = 376260227) B376260227
theorem B167226767 : Blo 1931435 167226767 := bstep (se 1 (by rfl) ⟨125420075, by rfl⟩ : syracuseStep 167226767 = 250840151) B250840151
theorem B111484511 : Blo 1931435 111484511 := bstep (se 1 (by rfl) ⟨83613383, by rfl⟩ : syracuseStep 111484511 = 167226767) B167226767
theorem B74323007 : Blo 1931435 74323007 := bstep (se 1 (by rfl) ⟨55742255, by rfl⟩ : syracuseStep 74323007 = 111484511) B111484511
theorem B49548671 : Blo 1931435 49548671 := bstep (se 1 (by rfl) ⟨37161503, by rfl⟩ : syracuseStep 49548671 = 74323007) B74323007
theorem B33032447 : Blo 1931435 33032447 := bstep (se 1 (by rfl) ⟨24774335, by rfl⟩ : syracuseStep 33032447 = 49548671) B49548671
theorem B22021631 : Blo 1931435 22021631 := bstep (se 1 (by rfl) ⟨16516223, by rfl⟩ : syracuseStep 22021631 = 33032447) B33032447
theorem B14681087 : Blo 1931435 14681087 := bstep (se 1 (by rfl) ⟨11010815, by rfl⟩ : syracuseStep 14681087 = 22021631) B22021631
theorem B9787391 : Blo 1931435 9787391 := bstep (se 1 (by rfl) ⟨7340543, by rfl⟩ : syracuseStep 9787391 = 14681087) B14681087
theorem B6524927 : Blo 1931435 6524927 := bstep (se 1 (by rfl) ⟨4893695, by rfl⟩ : syracuseStep 6524927 = 9787391) B9787391
theorem B4349951 : Blo 1931435 4349951 := bstep (se 1 (by rfl) ⟨3262463, by rfl⟩ : syracuseStep 4349951 = 6524927) B6524927
theorem B2899967 : Blo 1931435 2899967 := bstep (se 1 (by rfl) ⟨2174975, by rfl⟩ : syracuseStep 2899967 = 4349951) B4349951
theorem B1933311 : Blo 1931435 1933311 := bstep (se 1 (by rfl) ⟨1449983, by rfl⟩ : syracuseStep 1933311 = 2899967) B2899967
theorem B2899973 : Blo 1931435 2899973 := bbase (se 4 (by rfl) ⟨271872, by rfl⟩ : syracuseStep 2899973 = 543745) (by norm_num)
theorem B1933315 : Blo 1931435 1933315 := bstep (se 1 (by rfl) ⟨1449986, by rfl⟩ : syracuseStep 1933315 = 2899973) B2899973
theorem B3262477 : Blo 1931435 3262477 := bbase (se 3 (by rfl) ⟨611714, by rfl⟩ : syracuseStep 3262477 = 1223429) (by norm_num)
theorem B4349969 : Blo 1931435 4349969 := bstep (se 2 (by rfl) ⟨1631238, by rfl⟩ : syracuseStep 4349969 = 3262477) B3262477
theorem B2899979 : Blo 1931435 2899979 := bstep (se 1 (by rfl) ⟨2174984, by rfl⟩ : syracuseStep 2899979 = 4349969) B4349969
theorem B1933319 : Blo 1931435 1933319 := bstep (se 1 (by rfl) ⟨1449989, by rfl⟩ : syracuseStep 1933319 = 2899979) B2899979
theorem B2174989 : Blo 1931435 2174989 := bbase (se 3 (by rfl) ⟨407810, by rfl⟩ : syracuseStep 2174989 = 815621) (by norm_num)
theorem B2899985 : Blo 1931435 2899985 := bstep (se 2 (by rfl) ⟨1087494, by rfl⟩ : syracuseStep 2899985 = 2174989) B2174989
theorem B1933323 : Blo 1931435 1933323 := bstep (se 1 (by rfl) ⟨1449992, by rfl⟩ : syracuseStep 1933323 = 2899985) B2899985
theorem B6524981 : Blo 1931435 6524981 := bbase (se 5 (by rfl) ⟨305858, by rfl⟩ : syracuseStep 6524981 = 611717) (by norm_num)
theorem B4349987 : Blo 1931435 4349987 := bstep (se 1 (by rfl) ⟨3262490, by rfl⟩ : syracuseStep 4349987 = 6524981) B6524981
theorem B2899991 : Blo 1931435 2899991 := bstep (se 1 (by rfl) ⟨2174993, by rfl⟩ : syracuseStep 2899991 = 4349987) B4349987
theorem B1933327 : Blo 1931435 1933327 := bstep (se 1 (by rfl) ⟨1449995, by rfl⟩ : syracuseStep 1933327 = 2899991) B2899991
theorem B2899997 : Blo 1931435 2899997 := bbase (se 3 (by rfl) ⟨543749, by rfl⟩ : syracuseStep 2899997 = 1087499) (by norm_num)
theorem B1933331 : Blo 1931435 1933331 := bstep (se 1 (by rfl) ⟨1449998, by rfl⟩ : syracuseStep 1933331 = 2899997) B2899997
theorem B4350005 : Blo 1931435 4350005 := bbase (se 5 (by rfl) ⟨203906, by rfl⟩ : syracuseStep 4350005 = 407813) (by norm_num)
theorem B2900003 : Blo 1931435 2900003 := bstep (se 1 (by rfl) ⟨2175002, by rfl⟩ : syracuseStep 2900003 = 4350005) B4350005
theorem B1933335 : Blo 1931435 1933335 := bstep (se 1 (by rfl) ⟨1450001, by rfl⟩ : syracuseStep 1933335 = 2900003) B2900003
theorem B2612957 : Blo 1931435 2612957 := bbase (se 3 (by rfl) ⟨489929, by rfl⟩ : syracuseStep 2612957 = 979859) (by norm_num)
theorem B6967885 : Blo 1931435 6967885 := bstep (se 3 (by rfl) ⟨1306478, by rfl⟩ : syracuseStep 6967885 = 2612957) B2612957
theorem B9290513 : Blo 1931435 9290513 := bstep (se 2 (by rfl) ⟨3483942, by rfl⟩ : syracuseStep 9290513 = 6967885) B6967885
theorem B6193675 : Blo 1931435 6193675 := bstep (se 1 (by rfl) ⟨4645256, by rfl⟩ : syracuseStep 6193675 = 9290513) B9290513
theorem B8258233 : Blo 1931435 8258233 := bstep (se 2 (by rfl) ⟨3096837, by rfl⟩ : syracuseStep 8258233 = 6193675) B6193675
theorem B11010977 : Blo 1931435 11010977 := bstep (se 2 (by rfl) ⟨4129116, by rfl⟩ : syracuseStep 11010977 = 8258233) B8258233
theorem B7340651 : Blo 1931435 7340651 := bstep (se 1 (by rfl) ⟨5505488, by rfl⟩ : syracuseStep 7340651 = 11010977) B11010977
theorem B4893767 : Blo 1931435 4893767 := bstep (se 1 (by rfl) ⟨3670325, by rfl⟩ : syracuseStep 4893767 = 7340651) B7340651
theorem B3262511 : Blo 1931435 3262511 := bstep (se 1 (by rfl) ⟨2446883, by rfl⟩ : syracuseStep 3262511 = 4893767) B4893767
theorem B2175007 : Blo 1931435 2175007 := bstep (se 1 (by rfl) ⟨1631255, by rfl⟩ : syracuseStep 2175007 = 3262511) B3262511
theorem B2900009 : Blo 1931435 2900009 := bstep (se 2 (by rfl) ⟨1087503, by rfl⟩ : syracuseStep 2900009 = 2175007) B2175007
theorem B1933339 : Blo 1931435 1933339 := bstep (se 1 (by rfl) ⟨1450004, by rfl⟩ : syracuseStep 1933339 = 2900009) B2900009
theorem B13935797 : Blo 1931435 13935797 := bbase (se 5 (by rfl) ⟨653240, by rfl⟩ : syracuseStep 13935797 = 1306481) (by norm_num)
theorem B9290531 : Blo 1931435 9290531 := bstep (se 1 (by rfl) ⟨6967898, by rfl⟩ : syracuseStep 9290531 = 13935797) B13935797
theorem B6193687 : Blo 1931435 6193687 := bstep (se 1 (by rfl) ⟨4645265, by rfl⟩ : syracuseStep 6193687 = 9290531) B9290531
theorem B8258249 : Blo 1931435 8258249 := bstep (se 2 (by rfl) ⟨3096843, by rfl⟩ : syracuseStep 8258249 = 6193687) B6193687
theorem B5505499 : Blo 1931435 5505499 := bstep (se 1 (by rfl) ⟨4129124, by rfl⟩ : syracuseStep 5505499 = 8258249) B8258249
theorem B7340665 : Blo 1931435 7340665 := bstep (se 2 (by rfl) ⟨2752749, by rfl⟩ : syracuseStep 7340665 = 5505499) B5505499
theorem B9787553 : Blo 1931435 9787553 := bstep (se 2 (by rfl) ⟨3670332, by rfl⟩ : syracuseStep 9787553 = 7340665) B7340665
theorem B6525035 : Blo 1931435 6525035 := bstep (se 1 (by rfl) ⟨4893776, by rfl⟩ : syracuseStep 6525035 = 9787553) B9787553
theorem B4350023 : Blo 1931435 4350023 := bstep (se 1 (by rfl) ⟨3262517, by rfl⟩ : syracuseStep 4350023 = 6525035) B6525035
theorem B2900015 : Blo 1931435 2900015 := bstep (se 1 (by rfl) ⟨2175011, by rfl⟩ : syracuseStep 2900015 = 4350023) B4350023
theorem B1933343 : Blo 1931435 1933343 := bstep (se 1 (by rfl) ⟨1450007, by rfl⟩ : syracuseStep 1933343 = 2900015) B2900015
theorem B2900021 : Blo 1931435 2900021 := bbase (se 5 (by rfl) ⟨135938, by rfl⟩ : syracuseStep 2900021 = 271877) (by norm_num)
theorem B1933347 : Blo 1931435 1933347 := bstep (se 1 (by rfl) ⟨1450010, by rfl⟩ : syracuseStep 1933347 = 2900021) B2900021
theorem B4893797 : Blo 1931435 4893797 := bbase (se 4 (by rfl) ⟨458793, by rfl⟩ : syracuseStep 4893797 = 917587) (by norm_num)
theorem B3262531 : Blo 1931435 3262531 := bstep (se 1 (by rfl) ⟨2446898, by rfl⟩ : syracuseStep 3262531 = 4893797) B4893797
theorem B4350041 : Blo 1931435 4350041 := bstep (se 2 (by rfl) ⟨1631265, by rfl⟩ : syracuseStep 4350041 = 3262531) B3262531
theorem B2900027 : Blo 1931435 2900027 := bstep (se 1 (by rfl) ⟨2175020, by rfl⟩ : syracuseStep 2900027 = 4350041) B4350041
theorem B1933351 : Blo 1931435 1933351 := bstep (se 1 (by rfl) ⟨1450013, by rfl⟩ : syracuseStep 1933351 = 2900027) B2900027
theorem B2175025 : Blo 1931435 2175025 := bbase (se 2 (by rfl) ⟨815634, by rfl⟩ : syracuseStep 2175025 = 1631269) (by norm_num)
theorem B2900033 : Blo 1931435 2900033 := bstep (se 2 (by rfl) ⟨1087512, by rfl⟩ : syracuseStep 2900033 = 2175025) B2175025
theorem B1933355 : Blo 1931435 1933355 := bstep (se 1 (by rfl) ⟨1450016, by rfl⟩ : syracuseStep 1933355 = 2900033) B2900033
theorem B6967957 : Blo 1931435 6967957 := bbase (se 6 (by rfl) ⟨163311, by rfl⟩ : syracuseStep 6967957 = 326623) (by norm_num)
theorem B9290609 : Blo 1931435 9290609 := bstep (se 2 (by rfl) ⟨3483978, by rfl⟩ : syracuseStep 9290609 = 6967957) B6967957
theorem B6193739 : Blo 1931435 6193739 := bstep (se 1 (by rfl) ⟨4645304, by rfl⟩ : syracuseStep 6193739 = 9290609) B9290609
theorem B4129159 : Blo 1931435 4129159 := bstep (se 1 (by rfl) ⟨3096869, by rfl⟩ : syracuseStep 4129159 = 6193739) B6193739
theorem B5505545 : Blo 1931435 5505545 := bstep (se 2 (by rfl) ⟨2064579, by rfl⟩ : syracuseStep 5505545 = 4129159) B4129159
theorem B3670363 : Blo 1931435 3670363 := bstep (se 1 (by rfl) ⟨2752772, by rfl⟩ : syracuseStep 3670363 = 5505545) B5505545
theorem B4893817 : Blo 1931435 4893817 := bstep (se 2 (by rfl) ⟨1835181, by rfl⟩ : syracuseStep 4893817 = 3670363) B3670363
theorem B6525089 : Blo 1931435 6525089 := bstep (se 2 (by rfl) ⟨2446908, by rfl⟩ : syracuseStep 6525089 = 4893817) B4893817
theorem B4350059 : Blo 1931435 4350059 := bstep (se 1 (by rfl) ⟨3262544, by rfl⟩ : syracuseStep 4350059 = 6525089) B6525089
theorem B2900039 : Blo 1931435 2900039 := bstep (se 1 (by rfl) ⟨2175029, by rfl⟩ : syracuseStep 2900039 = 4350059) B4350059
theorem B1933359 : Blo 1931435 1933359 := bstep (se 1 (by rfl) ⟨1450019, by rfl⟩ : syracuseStep 1933359 = 2900039) B2900039
theorem B2900045 : Blo 1931435 2900045 := bbase (se 3 (by rfl) ⟨543758, by rfl⟩ : syracuseStep 2900045 = 1087517) (by norm_num)
theorem B1933363 : Blo 1931435 1933363 := bstep (se 1 (by rfl) ⟨1450022, by rfl⟩ : syracuseStep 1933363 = 2900045) B2900045
theorem B4350077 : Blo 1931435 4350077 := bbase (se 3 (by rfl) ⟨815639, by rfl⟩ : syracuseStep 4350077 = 1631279) (by norm_num)
theorem B2900051 : Blo 1931435 2900051 := bstep (se 1 (by rfl) ⟨2175038, by rfl⟩ : syracuseStep 2900051 = 4350077) B4350077
theorem B1933367 : Blo 1931435 1933367 := bstep (se 1 (by rfl) ⟨1450025, by rfl⟩ : syracuseStep 1933367 = 2900051) B2900051
theorem B3262565 : Blo 1931435 3262565 := bbase (se 4 (by rfl) ⟨305865, by rfl⟩ : syracuseStep 3262565 = 611731) (by norm_num)
theorem B2175043 : Blo 1931435 2175043 := bstep (se 1 (by rfl) ⟨1631282, by rfl⟩ : syracuseStep 2175043 = 3262565) B3262565
theorem B2900057 : Blo 1931435 2900057 := bstep (se 2 (by rfl) ⟨1087521, by rfl⟩ : syracuseStep 2900057 = 2175043) B2175043
theorem B1933371 : Blo 1931435 1933371 := bstep (se 1 (by rfl) ⟨1450028, by rfl⟩ : syracuseStep 1933371 = 2900057) B2900057
theorem B5959477 : Blo 1931435 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B31783877 : Blo 1931435 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B21189251 : Blo 1931435 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B14126167 : Blo 1931435 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B18834889 : Blo 1931435 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B25113185 : Blo 1931435 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B16742123 : Blo 1931435 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B11161415 : Blo 1931435 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B29763773 : Blo 1931435 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B19842515 : Blo 1931435 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B13228343 : Blo 1931435 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B8818895 : Blo 1931435 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B23517053 : Blo 1931435 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B15678035 : Blo 1931435 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B10452023 : Blo 1931435 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B6968015 : Blo 1931435 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B4645343 : Blo 1931435 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B3096895 : Blo 1931435 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B4129193 : Blo 1931435 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B2752795 : Blo 1931435 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B14681573 : Blo 1931435 14681573 := bstep (se 4 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 14681573 = 2752795) B2752795
theorem B9787715 : Blo 1931435 9787715 := bstep (se 1 (by rfl) ⟨7340786, by rfl⟩ : syracuseStep 9787715 = 14681573) B14681573
theorem B6525143 : Blo 1931435 6525143 := bstep (se 1 (by rfl) ⟨4893857, by rfl⟩ : syracuseStep 6525143 = 9787715) B9787715
theorem B4350095 : Blo 1931435 4350095 := bstep (se 1 (by rfl) ⟨3262571, by rfl⟩ : syracuseStep 4350095 = 6525143) B6525143
theorem B2900063 : Blo 1931435 2900063 := bstep (se 1 (by rfl) ⟨2175047, by rfl⟩ : syracuseStep 2900063 = 4350095) B4350095
theorem B1933375 : Blo 1931435 1933375 := bstep (se 1 (by rfl) ⟨1450031, by rfl⟩ : syracuseStep 1933375 = 2900063) B2900063
theorem B2900069 : Blo 1931435 2900069 := bbase (se 4 (by rfl) ⟨271881, by rfl⟩ : syracuseStep 2900069 = 543763) (by norm_num)
theorem B1933379 : Blo 1931435 1933379 := bstep (se 1 (by rfl) ⟨1450034, by rfl⟩ : syracuseStep 1933379 = 2900069) B2900069
theorem B2939645 : Blo 1931435 2939645 := bbase (se 3 (by rfl) ⟨551183, by rfl⟩ : syracuseStep 2939645 = 1102367) (by norm_num)
theorem B1959763 : Blo 1931435 1959763 := bstep (se 1 (by rfl) ⟨1469822, by rfl⟩ : syracuseStep 1959763 = 2939645) B2939645
theorem B2613017 : Blo 1931435 2613017 := bstep (se 2 (by rfl) ⟨979881, by rfl⟩ : syracuseStep 2613017 = 1959763) B1959763
theorem B6968045 : Blo 1931435 6968045 := bstep (se 3 (by rfl) ⟨1306508, by rfl⟩ : syracuseStep 6968045 = 2613017) B2613017
theorem B4645363 : Blo 1931435 4645363 := bstep (se 1 (by rfl) ⟨3484022, by rfl⟩ : syracuseStep 4645363 = 6968045) B6968045
theorem B6193817 : Blo 1931435 6193817 := bstep (se 2 (by rfl) ⟨2322681, by rfl⟩ : syracuseStep 6193817 = 4645363) B4645363
theorem B4129211 : Blo 1931435 4129211 := bstep (se 1 (by rfl) ⟨3096908, by rfl⟩ : syracuseStep 4129211 = 6193817) B6193817
theorem B2752807 : Blo 1931435 2752807 := bstep (se 1 (by rfl) ⟨2064605, by rfl⟩ : syracuseStep 2752807 = 4129211) B4129211
theorem B3670409 : Blo 1931435 3670409 := bstep (se 2 (by rfl) ⟨1376403, by rfl⟩ : syracuseStep 3670409 = 2752807) B2752807
theorem B2446939 : Blo 1931435 2446939 := bstep (se 1 (by rfl) ⟨1835204, by rfl⟩ : syracuseStep 2446939 = 3670409) B3670409
theorem B3262585 : Blo 1931435 3262585 := bstep (se 2 (by rfl) ⟨1223469, by rfl⟩ : syracuseStep 3262585 = 2446939) B2446939
theorem B4350113 : Blo 1931435 4350113 := bstep (se 2 (by rfl) ⟨1631292, by rfl⟩ : syracuseStep 4350113 = 3262585) B3262585
theorem B2900075 : Blo 1931435 2900075 := bstep (se 1 (by rfl) ⟨2175056, by rfl⟩ : syracuseStep 2900075 = 4350113) B4350113
theorem B1933383 : Blo 1931435 1933383 := bstep (se 1 (by rfl) ⟨1450037, by rfl⟩ : syracuseStep 1933383 = 2900075) B2900075
theorem B2175061 : Blo 1931435 2175061 := bbase (se 8 (by rfl) ⟨12744, by rfl⟩ : syracuseStep 2175061 = 25489) (by norm_num)
theorem B2900081 : Blo 1931435 2900081 := bstep (se 2 (by rfl) ⟨1087530, by rfl⟩ : syracuseStep 2900081 = 2175061) B2175061
theorem B1933387 : Blo 1931435 1933387 := bstep (se 1 (by rfl) ⟨1450040, by rfl⟩ : syracuseStep 1933387 = 2900081) B2900081
theorem B2446949 : Blo 1931435 2446949 := bbase (se 4 (by rfl) ⟨229401, by rfl⟩ : syracuseStep 2446949 = 458803) (by norm_num)
theorem B6525197 : Blo 1931435 6525197 := bstep (se 3 (by rfl) ⟨1223474, by rfl⟩ : syracuseStep 6525197 = 2446949) B2446949
theorem B4350131 : Blo 1931435 4350131 := bstep (se 1 (by rfl) ⟨3262598, by rfl⟩ : syracuseStep 4350131 = 6525197) B6525197
theorem B2900087 : Blo 1931435 2900087 := bstep (se 1 (by rfl) ⟨2175065, by rfl⟩ : syracuseStep 2900087 = 4350131) B4350131
theorem B1933391 : Blo 1931435 1933391 := bstep (se 1 (by rfl) ⟨1450043, by rfl⟩ : syracuseStep 1933391 = 2900087) B2900087
theorem B2900093 : Blo 1931435 2900093 := bbase (se 3 (by rfl) ⟨543767, by rfl⟩ : syracuseStep 2900093 = 1087535) (by norm_num)
theorem B1933395 : Blo 1931435 1933395 := bstep (se 1 (by rfl) ⟨1450046, by rfl⟩ : syracuseStep 1933395 = 2900093) B2900093
theorem B4350149 : Blo 1931435 4350149 := bbase (se 4 (by rfl) ⟨407826, by rfl⟩ : syracuseStep 4350149 = 815653) (by norm_num)
theorem B2900099 : Blo 1931435 2900099 := bstep (se 1 (by rfl) ⟨2175074, by rfl⟩ : syracuseStep 2900099 = 4350149) B4350149
theorem B1933399 : Blo 1931435 1933399 := bstep (se 1 (by rfl) ⟨1450049, by rfl⟩ : syracuseStep 1933399 = 2900099) B2900099
theorem B9290821 : Blo 1931435 9290821 := bbase (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) (by norm_num)
theorem B12387761 : Blo 1931435 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B8258507 : Blo 1931435 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B5505671 : Blo 1931435 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B3670447 : Blo 1931435 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B4893929 : Blo 1931435 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B3262619 : Blo 1931435 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B2175079 : Blo 1931435 2175079 := bstep (se 1 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 2175079 = 3262619) B3262619
theorem B2900105 : Blo 1931435 2900105 := bstep (se 2 (by rfl) ⟨1087539, by rfl⟩ : syracuseStep 2900105 = 2175079) B2175079
theorem B1933403 : Blo 1931435 1933403 := bstep (se 1 (by rfl) ⟨1450052, by rfl⟩ : syracuseStep 1933403 = 2900105) B2900105
theorem B9787877 : Blo 1931435 9787877 := bbase (se 4 (by rfl) ⟨917613, by rfl⟩ : syracuseStep 9787877 = 1835227) (by norm_num)
theorem B6525251 : Blo 1931435 6525251 := bstep (se 1 (by rfl) ⟨4893938, by rfl⟩ : syracuseStep 6525251 = 9787877) B9787877
theorem B4350167 : Blo 1931435 4350167 := bstep (se 1 (by rfl) ⟨3262625, by rfl⟩ : syracuseStep 4350167 = 6525251) B6525251
theorem B2900111 : Blo 1931435 2900111 := bstep (se 1 (by rfl) ⟨2175083, by rfl⟩ : syracuseStep 2900111 = 4350167) B4350167
theorem B1933407 : Blo 1931435 1933407 := bstep (se 1 (by rfl) ⟨1450055, by rfl⟩ : syracuseStep 1933407 = 2900111) B2900111
theorem B2900117 : Blo 1931435 2900117 := bbase (se 6 (by rfl) ⟨67971, by rfl⟩ : syracuseStep 2900117 = 135943) (by norm_num)
theorem B1933411 : Blo 1931435 1933411 := bstep (se 1 (by rfl) ⟨1450058, by rfl⟩ : syracuseStep 1933411 = 2900117) B2900117
theorem B35276309 : Blo 1931435 35276309 := bbase (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) (by norm_num)
theorem B23517539 : Blo 1931435 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B15678359 : Blo 1931435 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B10452239 : Blo 1931435 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B6968159 : Blo 1931435 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B4645439 : Blo 1931435 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B3096959 : Blo 1931435 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B8258557 : Blo 1931435 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B11011409 : Blo 1931435 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B7340939 : Blo 1931435 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B4893959 : Blo 1931435 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B3262639 : Blo 1931435 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B4350185 : Blo 1931435 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B2900123 : Blo 1931435 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B1933415 : Blo 1931435 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B2175097 : Blo 1931435 2175097 := bbase (se 2 (by rfl) ⟨815661, by rfl⟩ : syracuseStep 2175097 = 1631323) (by norm_num)
theorem B2900129 : Blo 1931435 2900129 := bstep (se 2 (by rfl) ⟨1087548, by rfl⟩ : syracuseStep 2900129 = 2175097) B2175097
theorem B1933419 : Blo 1931435 1933419 := bstep (se 1 (by rfl) ⟨1450064, by rfl⟩ : syracuseStep 1933419 = 2900129) B2900129
theorem B3874933 : Blo 1931435 3874933 := bbase (se 5 (by rfl) ⟨181637, by rfl⟩ : syracuseStep 3874933 = 363275) (by norm_num)
theorem B5166577 : Blo 1931435 5166577 := bstep (se 2 (by rfl) ⟨1937466, by rfl⟩ : syracuseStep 5166577 = 3874933) B3874933
theorem B6888769 : Blo 1931435 6888769 := bstep (se 2 (by rfl) ⟨2583288, by rfl⟩ : syracuseStep 6888769 = 5166577) B5166577
theorem B146960405 : Blo 1931435 146960405 := bstep (se 6 (by rfl) ⟨3444384, by rfl⟩ : syracuseStep 146960405 = 6888769) B6888769
theorem B97973603 : Blo 1931435 97973603 := bstep (se 1 (by rfl) ⟨73480202, by rfl⟩ : syracuseStep 97973603 = 146960405) B146960405
theorem B65315735 : Blo 1931435 65315735 := bstep (se 1 (by rfl) ⟨48986801, by rfl⟩ : syracuseStep 65315735 = 97973603) B97973603
theorem B43543823 : Blo 1931435 43543823 := bstep (se 1 (by rfl) ⟨32657867, by rfl⟩ : syracuseStep 43543823 = 65315735) B65315735
theorem B116116861 : Blo 1931435 116116861 := bstep (se 3 (by rfl) ⟨21771911, by rfl⟩ : syracuseStep 116116861 = 43543823) B43543823
theorem B154822481 : Blo 1931435 154822481 := bstep (se 2 (by rfl) ⟨58058430, by rfl⟩ : syracuseStep 154822481 = 116116861) B116116861
theorem B103214987 : Blo 1931435 103214987 := bstep (se 1 (by rfl) ⟨77411240, by rfl⟩ : syracuseStep 103214987 = 154822481) B154822481
theorem B68809991 : Blo 1931435 68809991 := bstep (se 1 (by rfl) ⟨51607493, by rfl⟩ : syracuseStep 68809991 = 103214987) B103214987
theorem B183493309 : Blo 1931435 183493309 := bstep (se 3 (by rfl) ⟨34404995, by rfl⟩ : syracuseStep 183493309 = 68809991) B68809991
theorem B244657745 : Blo 1931435 244657745 := bstep (se 2 (by rfl) ⟨91746654, by rfl⟩ : syracuseStep 244657745 = 183493309) B183493309
theorem B163105163 : Blo 1931435 163105163 := bstep (se 1 (by rfl) ⟨122328872, by rfl⟩ : syracuseStep 163105163 = 244657745) B244657745
theorem B108736775 : Blo 1931435 108736775 := bstep (se 1 (by rfl) ⟨81552581, by rfl⟩ : syracuseStep 108736775 = 163105163) B163105163
theorem B72491183 : Blo 1931435 72491183 := bstep (se 1 (by rfl) ⟨54368387, by rfl⟩ : syracuseStep 72491183 = 108736775) B108736775
theorem B48327455 : Blo 1931435 48327455 := bstep (se 1 (by rfl) ⟨36245591, by rfl⟩ : syracuseStep 48327455 = 72491183) B72491183
theorem B128873213 : Blo 1931435 128873213 := bstep (se 3 (by rfl) ⟨24163727, by rfl⟩ : syracuseStep 128873213 = 48327455) B48327455
theorem B85915475 : Blo 1931435 85915475 := bstep (se 1 (by rfl) ⟨64436606, by rfl⟩ : syracuseStep 85915475 = 128873213) B128873213
theorem B57276983 : Blo 1931435 57276983 := bstep (se 1 (by rfl) ⟨42957737, by rfl⟩ : syracuseStep 57276983 = 85915475) B85915475
theorem B38184655 : Blo 1931435 38184655 := bstep (se 1 (by rfl) ⟨28638491, by rfl⟩ : syracuseStep 38184655 = 57276983) B57276983
theorem B50912873 : Blo 1931435 50912873 := bstep (se 2 (by rfl) ⟨19092327, by rfl⟩ : syracuseStep 50912873 = 38184655) B38184655
theorem B33941915 : Blo 1931435 33941915 := bstep (se 1 (by rfl) ⟨25456436, by rfl⟩ : syracuseStep 33941915 = 50912873) B50912873
theorem B22627943 : Blo 1931435 22627943 := bstep (se 1 (by rfl) ⟨16970957, by rfl⟩ : syracuseStep 22627943 = 33941915) B33941915
theorem B15085295 : Blo 1931435 15085295 := bstep (se 1 (by rfl) ⟨11313971, by rfl⟩ : syracuseStep 15085295 = 22627943) B22627943
theorem B10056863 : Blo 1931435 10056863 := bstep (se 1 (by rfl) ⟨7542647, by rfl⟩ : syracuseStep 10056863 = 15085295) B15085295
theorem B26818301 : Blo 1931435 26818301 := bstep (se 3 (by rfl) ⟨5028431, by rfl⟩ : syracuseStep 26818301 = 10056863) B10056863
theorem B71515469 : Blo 1931435 71515469 := bstep (se 3 (by rfl) ⟨13409150, by rfl⟩ : syracuseStep 71515469 = 26818301) B26818301
theorem B47676979 : Blo 1931435 47676979 := bstep (se 1 (by rfl) ⟨35757734, by rfl⟩ : syracuseStep 47676979 = 71515469) B71515469
theorem B63569305 : Blo 1931435 63569305 := bstep (se 2 (by rfl) ⟨23838489, by rfl⟩ : syracuseStep 63569305 = 47676979) B47676979
theorem B339036293 : Blo 1931435 339036293 := bstep (se 4 (by rfl) ⟨31784652, by rfl⟩ : syracuseStep 339036293 = 63569305) B63569305
theorem B226024195 : Blo 1931435 226024195 := bstep (se 1 (by rfl) ⟨169518146, by rfl⟩ : syracuseStep 226024195 = 339036293) B339036293
theorem B301365593 : Blo 1931435 301365593 := bstep (se 2 (by rfl) ⟨113012097, by rfl⟩ : syracuseStep 301365593 = 226024195) B226024195
theorem B200910395 : Blo 1931435 200910395 := bstep (se 1 (by rfl) ⟨150682796, by rfl⟩ : syracuseStep 200910395 = 301365593) B301365593
theorem B133940263 : Blo 1931435 133940263 := bstep (se 1 (by rfl) ⟨100455197, by rfl⟩ : syracuseStep 133940263 = 200910395) B200910395
theorem B178587017 : Blo 1931435 178587017 := bstep (se 2 (by rfl) ⟨66970131, by rfl⟩ : syracuseStep 178587017 = 133940263) B133940263
theorem B119058011 : Blo 1931435 119058011 := bstep (se 1 (by rfl) ⟨89293508, by rfl⟩ : syracuseStep 119058011 = 178587017) B178587017
theorem B79372007 : Blo 1931435 79372007 := bstep (se 1 (by rfl) ⟨59529005, by rfl⟩ : syracuseStep 79372007 = 119058011) B119058011
theorem B52914671 : Blo 1931435 52914671 := bstep (se 1 (by rfl) ⟨39686003, by rfl⟩ : syracuseStep 52914671 = 79372007) B79372007
theorem B35276447 : Blo 1931435 35276447 := bstep (se 1 (by rfl) ⟨26457335, by rfl⟩ : syracuseStep 35276447 = 52914671) B52914671
theorem B23517631 : Blo 1931435 23517631 := bstep (se 1 (by rfl) ⟨17638223, by rfl⟩ : syracuseStep 23517631 = 35276447) B35276447
theorem B31356841 : Blo 1931435 31356841 := bstep (se 2 (by rfl) ⟨11758815, by rfl⟩ : syracuseStep 31356841 = 23517631) B23517631
theorem B41809121 : Blo 1931435 41809121 := bstep (se 2 (by rfl) ⟨15678420, by rfl⟩ : syracuseStep 41809121 = 31356841) B31356841
theorem B27872747 : Blo 1931435 27872747 := bstep (se 1 (by rfl) ⟨20904560, by rfl⟩ : syracuseStep 27872747 = 41809121) B41809121
theorem B18581831 : Blo 1931435 18581831 := bstep (se 1 (by rfl) ⟨13936373, by rfl⟩ : syracuseStep 18581831 = 27872747) B27872747
theorem B12387887 : Blo 1931435 12387887 := bstep (se 1 (by rfl) ⟨9290915, by rfl⟩ : syracuseStep 12387887 = 18581831) B18581831
theorem B8258591 : Blo 1931435 8258591 := bstep (se 1 (by rfl) ⟨6193943, by rfl⟩ : syracuseStep 8258591 = 12387887) B12387887
theorem B5505727 : Blo 1931435 5505727 := bstep (se 1 (by rfl) ⟨4129295, by rfl⟩ : syracuseStep 5505727 = 8258591) B8258591
theorem B7340969 : Blo 1931435 7340969 := bstep (se 2 (by rfl) ⟨2752863, by rfl⟩ : syracuseStep 7340969 = 5505727) B5505727
theorem B4893979 : Blo 1931435 4893979 := bstep (se 1 (by rfl) ⟨3670484, by rfl⟩ : syracuseStep 4893979 = 7340969) B7340969
theorem B6525305 : Blo 1931435 6525305 := bstep (se 2 (by rfl) ⟨2446989, by rfl⟩ : syracuseStep 6525305 = 4893979) B4893979
theorem B4350203 : Blo 1931435 4350203 := bstep (se 1 (by rfl) ⟨3262652, by rfl⟩ : syracuseStep 4350203 = 6525305) B6525305
theorem B2900135 : Blo 1931435 2900135 := bstep (se 1 (by rfl) ⟨2175101, by rfl⟩ : syracuseStep 2900135 = 4350203) B4350203
theorem B1933423 : Blo 1931435 1933423 := bstep (se 1 (by rfl) ⟨1450067, by rfl⟩ : syracuseStep 1933423 = 2900135) B2900135
theorem B2900141 : Blo 1931435 2900141 := bbase (se 3 (by rfl) ⟨543776, by rfl⟩ : syracuseStep 2900141 = 1087553) (by norm_num)
theorem B1933427 : Blo 1931435 1933427 := bstep (se 1 (by rfl) ⟨1450070, by rfl⟩ : syracuseStep 1933427 = 2900141) B2900141
theorem B4350221 : Blo 1931435 4350221 := bbase (se 3 (by rfl) ⟨815666, by rfl⟩ : syracuseStep 4350221 = 1631333) (by norm_num)
theorem B2900147 : Blo 1931435 2900147 := bstep (se 1 (by rfl) ⟨2175110, by rfl⟩ : syracuseStep 2900147 = 4350221) B4350221
theorem B1933431 : Blo 1931435 1933431 := bstep (se 1 (by rfl) ⟨1450073, by rfl⟩ : syracuseStep 1933431 = 2900147) B2900147
theorem B2447005 : Blo 1931435 2447005 := bbase (se 3 (by rfl) ⟨458813, by rfl⟩ : syracuseStep 2447005 = 917627) (by norm_num)
theorem B3262673 : Blo 1931435 3262673 := bstep (se 2 (by rfl) ⟨1223502, by rfl⟩ : syracuseStep 3262673 = 2447005) B2447005
theorem B2175115 : Blo 1931435 2175115 := bstep (se 1 (by rfl) ⟨1631336, by rfl⟩ : syracuseStep 2175115 = 3262673) B3262673
theorem B2900153 : Blo 1931435 2900153 := bstep (se 2 (by rfl) ⟨1087557, by rfl⟩ : syracuseStep 2900153 = 2175115) B2175115
theorem B1933435 : Blo 1931435 1933435 := bstep (se 1 (by rfl) ⟨1450076, by rfl⟩ : syracuseStep 1933435 = 2900153) B2900153
theorem C0 (j : ℕ) (h1 : 482858 ≤ j) (h2 : j ≤ 483358) : Blo 1931435 (4 * j + 3) := by
  interval_cases j
  · exact B1931435
  · exact B1931439
  · exact B1931443
  · exact B1931447
  · exact B1931451
  · exact B1931455
  · exact B1931459
  · exact B1931463
  · exact B1931467
  · exact B1931471
  · exact B1931475
  · exact B1931479
  · exact B1931483
  · exact B1931487
  · exact B1931491
  · exact B1931495
  · exact B1931499
  · exact B1931503
  · exact B1931507
  · exact B1931511
  · exact B1931515
  · exact B1931519
  · exact B1931523
  · exact B1931527
  · exact B1931531
  · exact B1931535
  · exact B1931539
  · exact B1931543
  · exact B1931547
  · exact B1931551
  · exact B1931555
  · exact B1931559
  · exact B1931563
  · exact B1931567
  · exact B1931571
  · exact B1931575
  · exact B1931579
  · exact B1931583
  · exact B1931587
  · exact B1931591
  · exact B1931595
  · exact B1931599
  · exact B1931603
  · exact B1931607
  · exact B1931611
  · exact B1931615
  · exact B1931619
  · exact B1931623
  · exact B1931627
  · exact B1931631
  · exact B1931635
  · exact B1931639
  · exact B1931643
  · exact B1931647
  · exact B1931651
  · exact B1931655
  · exact B1931659
  · exact B1931663
  · exact B1931667
  · exact B1931671
  · exact B1931675
  · exact B1931679
  · exact B1931683
  · exact B1931687
  · exact B1931691
  · exact B1931695
  · exact B1931699
  · exact B1931703
  · exact B1931707
  · exact B1931711
  · exact B1931715
  · exact B1931719
  · exact B1931723
  · exact B1931727
  · exact B1931731
  · exact B1931735
  · exact B1931739
  · exact B1931743
  · exact B1931747
  · exact B1931751
  · exact B1931755
  · exact B1931759
  · exact B1931763
  · exact B1931767
  · exact B1931771
  · exact B1931775
  · exact B1931779
  · exact B1931783
  · exact B1931787
  · exact B1931791
  · exact B1931795
  · exact B1931799
  · exact B1931803
  · exact B1931807
  · exact B1931811
  · exact B1931815
  · exact B1931819
  · exact B1931823
  · exact B1931827
  · exact B1931831
  · exact B1931835
  · exact B1931839
  · exact B1931843
  · exact B1931847
  · exact B1931851
  · exact B1931855
  · exact B1931859
  · exact B1931863
  · exact B1931867
  · exact B1931871
  · exact B1931875
  · exact B1931879
  · exact B1931883
  · exact B1931887
  · exact B1931891
  · exact B1931895
  · exact B1931899
  · exact B1931903
  · exact B1931907
  · exact B1931911
  · exact B1931915
  · exact B1931919
  · exact B1931923
  · exact B1931927
  · exact B1931931
  · exact B1931935
  · exact B1931939
  · exact B1931943
  · exact B1931947
  · exact B1931951
  · exact B1931955
  · exact B1931959
  · exact B1931963
  · exact B1931967
  · exact B1931971
  · exact B1931975
  · exact B1931979
  · exact B1931983
  · exact B1931987
  · exact B1931991
  · exact B1931995
  · exact B1931999
  · exact B1932003
  · exact B1932007
  · exact B1932011
  · exact B1932015
  · exact B1932019
  · exact B1932023
  · exact B1932027
  · exact B1932031
  · exact B1932035
  · exact B1932039
  · exact B1932043
  · exact B1932047
  · exact B1932051
  · exact B1932055
  · exact B1932059
  · exact B1932063
  · exact B1932067
  · exact B1932071
  · exact B1932075
  · exact B1932079
  · exact B1932083
  · exact B1932087
  · exact B1932091
  · exact B1932095
  · exact B1932099
  · exact B1932103
  · exact B1932107
  · exact B1932111
  · exact B1932115
  · exact B1932119
  · exact B1932123
  · exact B1932127
  · exact B1932131
  · exact B1932135
  · exact B1932139
  · exact B1932143
  · exact B1932147
  · exact B1932151
  · exact B1932155
  · exact B1932159
  · exact B1932163
  · exact B1932167
  · exact B1932171
  · exact B1932175
  · exact B1932179
  · exact B1932183
  · exact B1932187
  · exact B1932191
  · exact B1932195
  · exact B1932199
  · exact B1932203
  · exact B1932207
  · exact B1932211
  · exact B1932215
  · exact B1932219
  · exact B1932223
  · exact B1932227
  · exact B1932231
  · exact B1932235
  · exact B1932239
  · exact B1932243
  · exact B1932247
  · exact B1932251
  · exact B1932255
  · exact B1932259
  · exact B1932263
  · exact B1932267
  · exact B1932271
  · exact B1932275
  · exact B1932279
  · exact B1932283
  · exact B1932287
  · exact B1932291
  · exact B1932295
  · exact B1932299
  · exact B1932303
  · exact B1932307
  · exact B1932311
  · exact B1932315
  · exact B1932319
  · exact B1932323
  · exact B1932327
  · exact B1932331
  · exact B1932335
  · exact B1932339
  · exact B1932343
  · exact B1932347
  · exact B1932351
  · exact B1932355
  · exact B1932359
  · exact B1932363
  · exact B1932367
  · exact B1932371
  · exact B1932375
  · exact B1932379
  · exact B1932383
  · exact B1932387
  · exact B1932391
  · exact B1932395
  · exact B1932399
  · exact B1932403
  · exact B1932407
  · exact B1932411
  · exact B1932415
  · exact B1932419
  · exact B1932423
  · exact B1932427
  · exact B1932431
  · exact B1932435
  · exact B1932439
  · exact B1932443
  · exact B1932447
  · exact B1932451
  · exact B1932455
  · exact B1932459
  · exact B1932463
  · exact B1932467
  · exact B1932471
  · exact B1932475
  · exact B1932479
  · exact B1932483
  · exact B1932487
  · exact B1932491
  · exact B1932495
  · exact B1932499
  · exact B1932503
  · exact B1932507
  · exact B1932511
  · exact B1932515
  · exact B1932519
  · exact B1932523
  · exact B1932527
  · exact B1932531
  · exact B1932535
  · exact B1932539
  · exact B1932543
  · exact B1932547
  · exact B1932551
  · exact B1932555
  · exact B1932559
  · exact B1932563
  · exact B1932567
  · exact B1932571
  · exact B1932575
  · exact B1932579
  · exact B1932583
  · exact B1932587
  · exact B1932591
  · exact B1932595
  · exact B1932599
  · exact B1932603
  · exact B1932607
  · exact B1932611
  · exact B1932615
  · exact B1932619
  · exact B1932623
  · exact B1932627
  · exact B1932631
  · exact B1932635
  · exact B1932639
  · exact B1932643
  · exact B1932647
  · exact B1932651
  · exact B1932655
  · exact B1932659
  · exact B1932663
  · exact B1932667
  · exact B1932671
  · exact B1932675
  · exact B1932679
  · exact B1932683
  · exact B1932687
  · exact B1932691
  · exact B1932695
  · exact B1932699
  · exact B1932703
  · exact B1932707
  · exact B1932711
  · exact B1932715
  · exact B1932719
  · exact B1932723
  · exact B1932727
  · exact B1932731
  · exact B1932735
  · exact B1932739
  · exact B1932743
  · exact B1932747
  · exact B1932751
  · exact B1932755
  · exact B1932759
  · exact B1932763
  · exact B1932767
  · exact B1932771
  · exact B1932775
  · exact B1932779
  · exact B1932783
  · exact B1932787
  · exact B1932791
  · exact B1932795
  · exact B1932799
  · exact B1932803
  · exact B1932807
  · exact B1932811
  · exact B1932815
  · exact B1932819
  · exact B1932823
  · exact B1932827
  · exact B1932831
  · exact B1932835
  · exact B1932839
  · exact B1932843
  · exact B1932847
  · exact B1932851
  · exact B1932855
  · exact B1932859
  · exact B1932863
  · exact B1932867
  · exact B1932871
  · exact B1932875
  · exact B1932879
  · exact B1932883
  · exact B1932887
  · exact B1932891
  · exact B1932895
  · exact B1932899
  · exact B1932903
  · exact B1932907
  · exact B1932911
  · exact B1932915
  · exact B1932919
  · exact B1932923
  · exact B1932927
  · exact B1932931
  · exact B1932935
  · exact B1932939
  · exact B1932943
  · exact B1932947
  · exact B1932951
  · exact B1932955
  · exact B1932959
  · exact B1932963
  · exact B1932967
  · exact B1932971
  · exact B1932975
  · exact B1932979
  · exact B1932983
  · exact B1932987
  · exact B1932991
  · exact B1932995
  · exact B1932999
  · exact B1933003
  · exact B1933007
  · exact B1933011
  · exact B1933015
  · exact B1933019
  · exact B1933023
  · exact B1933027
  · exact B1933031
  · exact B1933035
  · exact B1933039
  · exact B1933043
  · exact B1933047
  · exact B1933051
  · exact B1933055
  · exact B1933059
  · exact B1933063
  · exact B1933067
  · exact B1933071
  · exact B1933075
  · exact B1933079
  · exact B1933083
  · exact B1933087
  · exact B1933091
  · exact B1933095
  · exact B1933099
  · exact B1933103
  · exact B1933107
  · exact B1933111
  · exact B1933115
  · exact B1933119
  · exact B1933123
  · exact B1933127
  · exact B1933131
  · exact B1933135
  · exact B1933139
  · exact B1933143
  · exact B1933147
  · exact B1933151
  · exact B1933155
  · exact B1933159
  · exact B1933163
  · exact B1933167
  · exact B1933171
  · exact B1933175
  · exact B1933179
  · exact B1933183
  · exact B1933187
  · exact B1933191
  · exact B1933195
  · exact B1933199
  · exact B1933203
  · exact B1933207
  · exact B1933211
  · exact B1933215
  · exact B1933219
  · exact B1933223
  · exact B1933227
  · exact B1933231
  · exact B1933235
  · exact B1933239
  · exact B1933243
  · exact B1933247
  · exact B1933251
  · exact B1933255
  · exact B1933259
  · exact B1933263
  · exact B1933267
  · exact B1933271
  · exact B1933275
  · exact B1933279
  · exact B1933283
  · exact B1933287
  · exact B1933291
  · exact B1933295
  · exact B1933299
  · exact B1933303
  · exact B1933307
  · exact B1933311
  · exact B1933315
  · exact B1933319
  · exact B1933323
  · exact B1933327
  · exact B1933331
  · exact B1933335
  · exact B1933339
  · exact B1933343
  · exact B1933347
  · exact B1933351
  · exact B1933355
  · exact B1933359
  · exact B1933363
  · exact B1933367
  · exact B1933371
  · exact B1933375
  · exact B1933379
  · exact B1933383
  · exact B1933387
  · exact B1933391
  · exact B1933395
  · exact B1933399
  · exact B1933403
  · exact B1933407
  · exact B1933411
  · exact B1933415
  · exact B1933419
  · exact B1933423
  · exact B1933427
  · exact B1933431
  · exact B1933435
theorem solution (m : ℕ) (hlo : 1931435 ≤ m) (hhi : m ≤ 1933435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 482858 ≤ j := by omega
    have hj2 : j ≤ 483358 := by omega
    have hb : Blo 1931435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
