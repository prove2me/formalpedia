-- Prove2me | solution 1 for syracuse_descends_range_2211435_2213435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:30.094061+00:00
-- url     : https://prove2.me/submissions/1ce99a2d-fc04-4411-af0a-6acd2def1725

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

theorem B2487865 : Blo 2211435 2487865 := bbase (se 2 (by rfl) ⟨932949, by rfl⟩ : syracuseStep 2487865 = 1865899) (by norm_num)
theorem B3317153 : Blo 2211435 3317153 := bstep (se 2 (by rfl) ⟨1243932, by rfl⟩ : syracuseStep 3317153 = 2487865) B2487865
theorem B2211435 : Blo 2211435 2211435 := bstep (se 1 (by rfl) ⟨1658576, by rfl⟩ : syracuseStep 2211435 = 3317153) B3317153
theorem B2361533 : Blo 2211435 2361533 := bbase (se 3 (by rfl) ⟨442787, by rfl⟩ : syracuseStep 2361533 = 885575) (by norm_num)
theorem B6297421 : Blo 2211435 6297421 := bstep (se 3 (by rfl) ⟨1180766, by rfl⟩ : syracuseStep 6297421 = 2361533) B2361533
theorem B8396561 : Blo 2211435 8396561 := bstep (se 2 (by rfl) ⟨3148710, by rfl⟩ : syracuseStep 8396561 = 6297421) B6297421
theorem B5597707 : Blo 2211435 5597707 := bstep (se 1 (by rfl) ⟨4198280, by rfl⟩ : syracuseStep 5597707 = 8396561) B8396561
theorem B7463609 : Blo 2211435 7463609 := bstep (se 2 (by rfl) ⟨2798853, by rfl⟩ : syracuseStep 7463609 = 5597707) B5597707
theorem B4975739 : Blo 2211435 4975739 := bstep (se 1 (by rfl) ⟨3731804, by rfl⟩ : syracuseStep 4975739 = 7463609) B7463609
theorem B3317159 : Blo 2211435 3317159 := bstep (se 1 (by rfl) ⟨2487869, by rfl⟩ : syracuseStep 3317159 = 4975739) B4975739
theorem B2211439 : Blo 2211435 2211439 := bstep (se 1 (by rfl) ⟨1658579, by rfl⟩ : syracuseStep 2211439 = 3317159) B3317159
theorem B3317165 : Blo 2211435 3317165 := bbase (se 3 (by rfl) ⟨621968, by rfl⟩ : syracuseStep 3317165 = 1243937) (by norm_num)
theorem B2211443 : Blo 2211435 2211443 := bstep (se 1 (by rfl) ⟨1658582, by rfl⟩ : syracuseStep 2211443 = 3317165) B3317165
theorem B4975757 : Blo 2211435 4975757 := bbase (se 3 (by rfl) ⟨932954, by rfl⟩ : syracuseStep 4975757 = 1865909) (by norm_num)
theorem B3317171 : Blo 2211435 3317171 := bstep (se 1 (by rfl) ⟨2487878, by rfl⟩ : syracuseStep 3317171 = 4975757) B4975757
theorem B2211447 : Blo 2211435 2211447 := bstep (se 1 (by rfl) ⟨1658585, by rfl⟩ : syracuseStep 2211447 = 3317171) B3317171
theorem B2798869 : Blo 2211435 2798869 := bbase (se 6 (by rfl) ⟨65598, by rfl⟩ : syracuseStep 2798869 = 131197) (by norm_num)
theorem B3731825 : Blo 2211435 3731825 := bstep (se 2 (by rfl) ⟨1399434, by rfl⟩ : syracuseStep 3731825 = 2798869) B2798869
theorem B2487883 : Blo 2211435 2487883 := bstep (se 1 (by rfl) ⟨1865912, by rfl⟩ : syracuseStep 2487883 = 3731825) B3731825
theorem B3317177 : Blo 2211435 3317177 := bstep (se 2 (by rfl) ⟨1243941, by rfl⟩ : syracuseStep 3317177 = 2487883) B2487883
theorem B2211451 : Blo 2211435 2211451 := bstep (se 1 (by rfl) ⟨1658588, by rfl⟩ : syracuseStep 2211451 = 3317177) B3317177
theorem B5609453 : Blo 2211435 5609453 := bbase (se 3 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 5609453 = 2103545) (by norm_num)
theorem B14958541 : Blo 2211435 14958541 := bstep (se 3 (by rfl) ⟨2804726, by rfl⟩ : syracuseStep 14958541 = 5609453) B5609453
theorem B19944721 : Blo 2211435 19944721 := bstep (se 2 (by rfl) ⟨7479270, by rfl⟩ : syracuseStep 19944721 = 14958541) B14958541
theorem B26592961 : Blo 2211435 26592961 := bstep (se 2 (by rfl) ⟨9972360, by rfl⟩ : syracuseStep 26592961 = 19944721) B19944721
theorem B35457281 : Blo 2211435 35457281 := bstep (se 2 (by rfl) ⟨13296480, by rfl⟩ : syracuseStep 35457281 = 26592961) B26592961
theorem B378210997 : Blo 2211435 378210997 := bstep (se 5 (by rfl) ⟨17728640, by rfl⟩ : syracuseStep 378210997 = 35457281) B35457281
theorem B2017125317 : Blo 2211435 2017125317 := bstep (se 4 (by rfl) ⟨189105498, by rfl⟩ : syracuseStep 2017125317 = 378210997) B378210997
theorem B1344750211 : Blo 2211435 1344750211 := bstep (se 1 (by rfl) ⟨1008562658, by rfl⟩ : syracuseStep 1344750211 = 2017125317) B2017125317
theorem B1793000281 : Blo 2211435 1793000281 := bstep (se 2 (by rfl) ⟨672375105, by rfl⟩ : syracuseStep 1793000281 = 1344750211) B1344750211
theorem B2390667041 : Blo 2211435 2390667041 := bstep (se 2 (by rfl) ⟨896500140, by rfl⟩ : syracuseStep 2390667041 = 1793000281) B1793000281
theorem B1593778027 : Blo 2211435 1593778027 := bstep (se 1 (by rfl) ⟨1195333520, by rfl⟩ : syracuseStep 1593778027 = 2390667041) B2390667041
theorem B2125037369 : Blo 2211435 2125037369 := bstep (se 2 (by rfl) ⟨796889013, by rfl⟩ : syracuseStep 2125037369 = 1593778027) B1593778027
theorem B1416691579 : Blo 2211435 1416691579 := bstep (se 1 (by rfl) ⟨1062518684, by rfl⟩ : syracuseStep 1416691579 = 2125037369) B2125037369
theorem B1888922105 : Blo 2211435 1888922105 := bstep (se 2 (by rfl) ⟨708345789, by rfl⟩ : syracuseStep 1888922105 = 1416691579) B1416691579
theorem B1259281403 : Blo 2211435 1259281403 := bstep (se 1 (by rfl) ⟨944461052, by rfl⟩ : syracuseStep 1259281403 = 1888922105) B1888922105
theorem B839520935 : Blo 2211435 839520935 := bstep (se 1 (by rfl) ⟨629640701, by rfl⟩ : syracuseStep 839520935 = 1259281403) B1259281403
theorem B559680623 : Blo 2211435 559680623 := bstep (se 1 (by rfl) ⟨419760467, by rfl⟩ : syracuseStep 559680623 = 839520935) B839520935
theorem B373120415 : Blo 2211435 373120415 := bstep (se 1 (by rfl) ⟨279840311, by rfl⟩ : syracuseStep 373120415 = 559680623) B559680623
theorem B248746943 : Blo 2211435 248746943 := bstep (se 1 (by rfl) ⟨186560207, by rfl⟩ : syracuseStep 248746943 = 373120415) B373120415
theorem B165831295 : Blo 2211435 165831295 := bstep (se 1 (by rfl) ⟨124373471, by rfl⟩ : syracuseStep 165831295 = 248746943) B248746943
theorem B221108393 : Blo 2211435 221108393 := bstep (se 2 (by rfl) ⟨82915647, by rfl⟩ : syracuseStep 221108393 = 165831295) B165831295
theorem B147405595 : Blo 2211435 147405595 := bstep (se 1 (by rfl) ⟨110554196, by rfl⟩ : syracuseStep 147405595 = 221108393) B221108393
theorem B196540793 : Blo 2211435 196540793 := bstep (se 2 (by rfl) ⟨73702797, by rfl⟩ : syracuseStep 196540793 = 147405595) B147405595
theorem B131027195 : Blo 2211435 131027195 := bstep (se 1 (by rfl) ⟨98270396, by rfl⟩ : syracuseStep 131027195 = 196540793) B196540793
theorem B87351463 : Blo 2211435 87351463 := bstep (se 1 (by rfl) ⟨65513597, by rfl⟩ : syracuseStep 87351463 = 131027195) B131027195
theorem B116468617 : Blo 2211435 116468617 := bstep (se 2 (by rfl) ⟨43675731, by rfl⟩ : syracuseStep 116468617 = 87351463) B87351463
theorem B155291489 : Blo 2211435 155291489 := bstep (se 2 (by rfl) ⟨58234308, by rfl⟩ : syracuseStep 155291489 = 116468617) B116468617
theorem B103527659 : Blo 2211435 103527659 := bstep (se 1 (by rfl) ⟨77645744, by rfl⟩ : syracuseStep 103527659 = 155291489) B155291489
theorem B276073757 : Blo 2211435 276073757 := bstep (se 3 (by rfl) ⟨51763829, by rfl⟩ : syracuseStep 276073757 = 103527659) B103527659
theorem B184049171 : Blo 2211435 184049171 := bstep (se 1 (by rfl) ⟨138036878, by rfl⟩ : syracuseStep 184049171 = 276073757) B276073757
theorem B122699447 : Blo 2211435 122699447 := bstep (se 1 (by rfl) ⟨92024585, by rfl⟩ : syracuseStep 122699447 = 184049171) B184049171
theorem B81799631 : Blo 2211435 81799631 := bstep (se 1 (by rfl) ⟨61349723, by rfl⟩ : syracuseStep 81799631 = 122699447) B122699447
theorem B54533087 : Blo 2211435 54533087 := bstep (se 1 (by rfl) ⟨40899815, by rfl⟩ : syracuseStep 54533087 = 81799631) B81799631
theorem B36355391 : Blo 2211435 36355391 := bstep (se 1 (by rfl) ⟨27266543, by rfl⟩ : syracuseStep 36355391 = 54533087) B54533087
theorem B24236927 : Blo 2211435 24236927 := bstep (se 1 (by rfl) ⟨18177695, by rfl⟩ : syracuseStep 24236927 = 36355391) B36355391
theorem B16157951 : Blo 2211435 16157951 := bstep (se 1 (by rfl) ⟨12118463, by rfl⟩ : syracuseStep 16157951 = 24236927) B24236927
theorem B10771967 : Blo 2211435 10771967 := bstep (se 1 (by rfl) ⟨8078975, by rfl⟩ : syracuseStep 10771967 = 16157951) B16157951
theorem B7181311 : Blo 2211435 7181311 := bstep (se 1 (by rfl) ⟨5385983, by rfl⟩ : syracuseStep 7181311 = 10771967) B10771967
theorem B9575081 : Blo 2211435 9575081 := bstep (se 2 (by rfl) ⟨3590655, by rfl⟩ : syracuseStep 9575081 = 7181311) B7181311
theorem B6383387 : Blo 2211435 6383387 := bstep (se 1 (by rfl) ⟨4787540, by rfl⟩ : syracuseStep 6383387 = 9575081) B9575081
theorem B4255591 : Blo 2211435 4255591 := bstep (se 1 (by rfl) ⟨3191693, by rfl⟩ : syracuseStep 4255591 = 6383387) B6383387
theorem B5674121 : Blo 2211435 5674121 := bstep (se 2 (by rfl) ⟨2127795, by rfl⟩ : syracuseStep 5674121 = 4255591) B4255591
theorem B3782747 : Blo 2211435 3782747 := bstep (se 1 (by rfl) ⟨2837060, by rfl⟩ : syracuseStep 3782747 = 5674121) B5674121
theorem B2521831 : Blo 2211435 2521831 := bstep (se 1 (by rfl) ⟨1891373, by rfl⟩ : syracuseStep 2521831 = 3782747) B3782747
theorem B53799061 : Blo 2211435 53799061 := bstep (se 6 (by rfl) ⟨1260915, by rfl⟩ : syracuseStep 53799061 = 2521831) B2521831
theorem B71732081 : Blo 2211435 71732081 := bstep (se 2 (by rfl) ⟨26899530, by rfl⟩ : syracuseStep 71732081 = 53799061) B53799061
theorem B47821387 : Blo 2211435 47821387 := bstep (se 1 (by rfl) ⟨35866040, by rfl⟩ : syracuseStep 47821387 = 71732081) B71732081
theorem B63761849 : Blo 2211435 63761849 := bstep (se 2 (by rfl) ⟨23910693, by rfl⟩ : syracuseStep 63761849 = 47821387) B47821387
theorem B42507899 : Blo 2211435 42507899 := bstep (se 1 (by rfl) ⟨31880924, by rfl⟩ : syracuseStep 42507899 = 63761849) B63761849
theorem B28338599 : Blo 2211435 28338599 := bstep (se 1 (by rfl) ⟨21253949, by rfl⟩ : syracuseStep 28338599 = 42507899) B42507899
theorem B18892399 : Blo 2211435 18892399 := bstep (se 1 (by rfl) ⟨14169299, by rfl⟩ : syracuseStep 18892399 = 28338599) B28338599
theorem B25189865 : Blo 2211435 25189865 := bstep (se 2 (by rfl) ⟨9446199, by rfl⟩ : syracuseStep 25189865 = 18892399) B18892399
theorem B16793243 : Blo 2211435 16793243 := bstep (se 1 (by rfl) ⟨12594932, by rfl⟩ : syracuseStep 16793243 = 25189865) B25189865
theorem B11195495 : Blo 2211435 11195495 := bstep (se 1 (by rfl) ⟨8396621, by rfl⟩ : syracuseStep 11195495 = 16793243) B16793243
theorem B7463663 : Blo 2211435 7463663 := bstep (se 1 (by rfl) ⟨5597747, by rfl⟩ : syracuseStep 7463663 = 11195495) B11195495
theorem B4975775 : Blo 2211435 4975775 := bstep (se 1 (by rfl) ⟨3731831, by rfl⟩ : syracuseStep 4975775 = 7463663) B7463663
theorem B3317183 : Blo 2211435 3317183 := bstep (se 1 (by rfl) ⟨2487887, by rfl⟩ : syracuseStep 3317183 = 4975775) B4975775
theorem B2211455 : Blo 2211435 2211455 := bstep (se 1 (by rfl) ⟨1658591, by rfl⟩ : syracuseStep 2211455 = 3317183) B3317183
theorem B3317189 : Blo 2211435 3317189 := bbase (se 4 (by rfl) ⟨310986, by rfl⟩ : syracuseStep 3317189 = 621973) (by norm_num)
theorem B2211459 : Blo 2211435 2211459 := bstep (se 1 (by rfl) ⟨1658594, by rfl⟩ : syracuseStep 2211459 = 3317189) B3317189
theorem B3731845 : Blo 2211435 3731845 := bbase (se 4 (by rfl) ⟨349860, by rfl⟩ : syracuseStep 3731845 = 699721) (by norm_num)
theorem B4975793 : Blo 2211435 4975793 := bstep (se 2 (by rfl) ⟨1865922, by rfl⟩ : syracuseStep 4975793 = 3731845) B3731845
theorem B3317195 : Blo 2211435 3317195 := bstep (se 1 (by rfl) ⟨2487896, by rfl⟩ : syracuseStep 3317195 = 4975793) B4975793
theorem B2211463 : Blo 2211435 2211463 := bstep (se 1 (by rfl) ⟨1658597, by rfl⟩ : syracuseStep 2211463 = 3317195) B3317195
theorem B2487901 : Blo 2211435 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B3317201 : Blo 2211435 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B2211467 : Blo 2211435 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B7463717 : Blo 2211435 7463717 := bbase (se 4 (by rfl) ⟨699723, by rfl⟩ : syracuseStep 7463717 = 1399447) (by norm_num)
theorem B4975811 : Blo 2211435 4975811 := bstep (se 1 (by rfl) ⟨3731858, by rfl⟩ : syracuseStep 4975811 = 7463717) B7463717
theorem B3317207 : Blo 2211435 3317207 := bstep (se 1 (by rfl) ⟨2487905, by rfl⟩ : syracuseStep 3317207 = 4975811) B4975811
theorem B2211471 : Blo 2211435 2211471 := bstep (se 1 (by rfl) ⟨1658603, by rfl⟩ : syracuseStep 2211471 = 3317207) B3317207
theorem B3317213 : Blo 2211435 3317213 := bbase (se 3 (by rfl) ⟨621977, by rfl⟩ : syracuseStep 3317213 = 1243955) (by norm_num)
theorem B2211475 : Blo 2211435 2211475 := bstep (se 1 (by rfl) ⟨1658606, by rfl⟩ : syracuseStep 2211475 = 3317213) B3317213
theorem B4975829 : Blo 2211435 4975829 := bbase (se 7 (by rfl) ⟨58310, by rfl⟩ : syracuseStep 4975829 = 116621) (by norm_num)
theorem B3317219 : Blo 2211435 3317219 := bstep (se 1 (by rfl) ⟨2487914, by rfl⟩ : syracuseStep 3317219 = 4975829) B4975829
theorem B2211479 : Blo 2211435 2211479 := bstep (se 1 (by rfl) ⟨1658609, by rfl⟩ : syracuseStep 2211479 = 3317219) B3317219
theorem B7084741 : Blo 2211435 7084741 := bbase (se 4 (by rfl) ⟨664194, by rfl⟩ : syracuseStep 7084741 = 1328389) (by norm_num)
theorem B9446321 : Blo 2211435 9446321 := bstep (se 2 (by rfl) ⟨3542370, by rfl⟩ : syracuseStep 9446321 = 7084741) B7084741
theorem B6297547 : Blo 2211435 6297547 := bstep (se 1 (by rfl) ⟨4723160, by rfl⟩ : syracuseStep 6297547 = 9446321) B9446321
theorem B8396729 : Blo 2211435 8396729 := bstep (se 2 (by rfl) ⟨3148773, by rfl⟩ : syracuseStep 8396729 = 6297547) B6297547
theorem B5597819 : Blo 2211435 5597819 := bstep (se 1 (by rfl) ⟨4198364, by rfl⟩ : syracuseStep 5597819 = 8396729) B8396729
theorem B3731879 : Blo 2211435 3731879 := bstep (se 1 (by rfl) ⟨2798909, by rfl⟩ : syracuseStep 3731879 = 5597819) B5597819
theorem B2487919 : Blo 2211435 2487919 := bstep (se 1 (by rfl) ⟨1865939, by rfl⟩ : syracuseStep 2487919 = 3731879) B3731879
theorem B3317225 : Blo 2211435 3317225 := bstep (se 2 (by rfl) ⟨1243959, by rfl⟩ : syracuseStep 3317225 = 2487919) B2487919
theorem B2211483 : Blo 2211435 2211483 := bstep (se 1 (by rfl) ⟨1658612, by rfl⟩ : syracuseStep 2211483 = 3317225) B3317225
theorem B6724981 : Blo 2211435 6724981 := bbase (se 5 (by rfl) ⟨315233, by rfl⟩ : syracuseStep 6724981 = 630467) (by norm_num)
theorem B8966641 : Blo 2211435 8966641 := bstep (se 2 (by rfl) ⟨3362490, by rfl⟩ : syracuseStep 8966641 = 6724981) B6724981
theorem B11955521 : Blo 2211435 11955521 := bstep (se 2 (by rfl) ⟨4483320, by rfl⟩ : syracuseStep 11955521 = 8966641) B8966641
theorem B7970347 : Blo 2211435 7970347 := bstep (se 1 (by rfl) ⟨5977760, by rfl⟩ : syracuseStep 7970347 = 11955521) B11955521
theorem B10627129 : Blo 2211435 10627129 := bstep (se 2 (by rfl) ⟨3985173, by rfl⟩ : syracuseStep 10627129 = 7970347) B7970347
theorem B14169505 : Blo 2211435 14169505 := bstep (se 2 (by rfl) ⟨5313564, by rfl⟩ : syracuseStep 14169505 = 10627129) B10627129
theorem B18892673 : Blo 2211435 18892673 := bstep (se 2 (by rfl) ⟨7084752, by rfl⟩ : syracuseStep 18892673 = 14169505) B14169505
theorem B12595115 : Blo 2211435 12595115 := bstep (se 1 (by rfl) ⟨9446336, by rfl⟩ : syracuseStep 12595115 = 18892673) B18892673
theorem B8396743 : Blo 2211435 8396743 := bstep (se 1 (by rfl) ⟨6297557, by rfl⟩ : syracuseStep 8396743 = 12595115) B12595115
theorem B11195657 : Blo 2211435 11195657 := bstep (se 2 (by rfl) ⟨4198371, by rfl⟩ : syracuseStep 11195657 = 8396743) B8396743
theorem B7463771 : Blo 2211435 7463771 := bstep (se 1 (by rfl) ⟨5597828, by rfl⟩ : syracuseStep 7463771 = 11195657) B11195657
theorem B4975847 : Blo 2211435 4975847 := bstep (se 1 (by rfl) ⟨3731885, by rfl⟩ : syracuseStep 4975847 = 7463771) B7463771
theorem B3317231 : Blo 2211435 3317231 := bstep (se 1 (by rfl) ⟨2487923, by rfl⟩ : syracuseStep 3317231 = 4975847) B4975847
theorem B2211487 : Blo 2211435 2211487 := bstep (se 1 (by rfl) ⟨1658615, by rfl⟩ : syracuseStep 2211487 = 3317231) B3317231
theorem B3317237 : Blo 2211435 3317237 := bbase (se 5 (by rfl) ⟨155495, by rfl⟩ : syracuseStep 3317237 = 310991) (by norm_num)
theorem B2211491 : Blo 2211435 2211491 := bstep (se 1 (by rfl) ⟨1658618, by rfl⟩ : syracuseStep 2211491 = 3317237) B3317237
theorem B2361593 : Blo 2211435 2361593 := bbase (se 2 (by rfl) ⟨885597, by rfl⟩ : syracuseStep 2361593 = 1771195) (by norm_num)
theorem B6297581 : Blo 2211435 6297581 := bstep (se 3 (by rfl) ⟨1180796, by rfl⟩ : syracuseStep 6297581 = 2361593) B2361593
theorem B4198387 : Blo 2211435 4198387 := bstep (se 1 (by rfl) ⟨3148790, by rfl⟩ : syracuseStep 4198387 = 6297581) B6297581
theorem B5597849 : Blo 2211435 5597849 := bstep (se 2 (by rfl) ⟨2099193, by rfl⟩ : syracuseStep 5597849 = 4198387) B4198387
theorem B3731899 : Blo 2211435 3731899 := bstep (se 1 (by rfl) ⟨2798924, by rfl⟩ : syracuseStep 3731899 = 5597849) B5597849
theorem B4975865 : Blo 2211435 4975865 := bstep (se 2 (by rfl) ⟨1865949, by rfl⟩ : syracuseStep 4975865 = 3731899) B3731899
theorem B3317243 : Blo 2211435 3317243 := bstep (se 1 (by rfl) ⟨2487932, by rfl⟩ : syracuseStep 3317243 = 4975865) B4975865
theorem B2211495 : Blo 2211435 2211495 := bstep (se 1 (by rfl) ⟨1658621, by rfl⟩ : syracuseStep 2211495 = 3317243) B3317243
theorem B2487937 : Blo 2211435 2487937 := bbase (se 2 (by rfl) ⟨932976, by rfl⟩ : syracuseStep 2487937 = 1865953) (by norm_num)
theorem B3317249 : Blo 2211435 3317249 := bstep (se 2 (by rfl) ⟨1243968, by rfl⟩ : syracuseStep 3317249 = 2487937) B2487937
theorem B2211499 : Blo 2211435 2211499 := bstep (se 1 (by rfl) ⟨1658624, by rfl⟩ : syracuseStep 2211499 = 3317249) B3317249
theorem B5597869 : Blo 2211435 5597869 := bbase (se 3 (by rfl) ⟨1049600, by rfl⟩ : syracuseStep 5597869 = 2099201) (by norm_num)
theorem B7463825 : Blo 2211435 7463825 := bstep (se 2 (by rfl) ⟨2798934, by rfl⟩ : syracuseStep 7463825 = 5597869) B5597869
theorem B4975883 : Blo 2211435 4975883 := bstep (se 1 (by rfl) ⟨3731912, by rfl⟩ : syracuseStep 4975883 = 7463825) B7463825
theorem B3317255 : Blo 2211435 3317255 := bstep (se 1 (by rfl) ⟨2487941, by rfl⟩ : syracuseStep 3317255 = 4975883) B4975883
theorem B2211503 : Blo 2211435 2211503 := bstep (se 1 (by rfl) ⟨1658627, by rfl⟩ : syracuseStep 2211503 = 3317255) B3317255
theorem B3317261 : Blo 2211435 3317261 := bbase (se 3 (by rfl) ⟨621986, by rfl⟩ : syracuseStep 3317261 = 1243973) (by norm_num)
theorem B2211507 : Blo 2211435 2211507 := bstep (se 1 (by rfl) ⟨1658630, by rfl⟩ : syracuseStep 2211507 = 3317261) B3317261
theorem B4975901 : Blo 2211435 4975901 := bbase (se 3 (by rfl) ⟨932981, by rfl⟩ : syracuseStep 4975901 = 1865963) (by norm_num)
theorem B3317267 : Blo 2211435 3317267 := bstep (se 1 (by rfl) ⟨2487950, by rfl⟩ : syracuseStep 3317267 = 4975901) B4975901
theorem B2211511 : Blo 2211435 2211511 := bstep (se 1 (by rfl) ⟨1658633, by rfl⟩ : syracuseStep 2211511 = 3317267) B3317267
theorem B3731933 : Blo 2211435 3731933 := bbase (se 3 (by rfl) ⟨699737, by rfl⟩ : syracuseStep 3731933 = 1399475) (by norm_num)
theorem B2487955 : Blo 2211435 2487955 := bstep (se 1 (by rfl) ⟨1865966, by rfl⟩ : syracuseStep 2487955 = 3731933) B3731933
theorem B3317273 : Blo 2211435 3317273 := bstep (se 2 (by rfl) ⟨1243977, by rfl⟩ : syracuseStep 3317273 = 2487955) B2487955
theorem B2211515 : Blo 2211435 2211515 := bstep (se 1 (by rfl) ⟨1658636, by rfl⟩ : syracuseStep 2211515 = 3317273) B3317273
theorem B6383573 : Blo 2211435 6383573 := bbase (se 7 (by rfl) ⟨74807, by rfl⟩ : syracuseStep 6383573 = 149615) (by norm_num)
theorem B4255715 : Blo 2211435 4255715 := bstep (se 1 (by rfl) ⟨3191786, by rfl⟩ : syracuseStep 4255715 = 6383573) B6383573
theorem B2837143 : Blo 2211435 2837143 := bstep (se 1 (by rfl) ⟨2127857, by rfl⟩ : syracuseStep 2837143 = 4255715) B4255715
theorem B3782857 : Blo 2211435 3782857 := bstep (se 2 (by rfl) ⟨1418571, by rfl⟩ : syracuseStep 3782857 = 2837143) B2837143
theorem B5043809 : Blo 2211435 5043809 := bstep (se 2 (by rfl) ⟨1891428, by rfl⟩ : syracuseStep 5043809 = 3782857) B3782857
theorem B13450157 : Blo 2211435 13450157 := bstep (se 3 (by rfl) ⟨2521904, by rfl⟩ : syracuseStep 13450157 = 5043809) B5043809
theorem B8966771 : Blo 2211435 8966771 := bstep (se 1 (by rfl) ⟨6725078, by rfl⟩ : syracuseStep 8966771 = 13450157) B13450157
theorem B5977847 : Blo 2211435 5977847 := bstep (se 1 (by rfl) ⟨4483385, by rfl⟩ : syracuseStep 5977847 = 8966771) B8966771
theorem B15940925 : Blo 2211435 15940925 := bstep (se 3 (by rfl) ⟨2988923, by rfl⟩ : syracuseStep 15940925 = 5977847) B5977847
theorem B10627283 : Blo 2211435 10627283 := bstep (se 1 (by rfl) ⟨7970462, by rfl⟩ : syracuseStep 10627283 = 15940925) B15940925
theorem B7084855 : Blo 2211435 7084855 := bstep (se 1 (by rfl) ⟨5313641, by rfl⟩ : syracuseStep 7084855 = 10627283) B10627283
theorem B9446473 : Blo 2211435 9446473 := bstep (se 2 (by rfl) ⟨3542427, by rfl⟩ : syracuseStep 9446473 = 7084855) B7084855
theorem B12595297 : Blo 2211435 12595297 := bstep (se 2 (by rfl) ⟨4723236, by rfl⟩ : syracuseStep 12595297 = 9446473) B9446473
theorem B16793729 : Blo 2211435 16793729 := bstep (se 2 (by rfl) ⟨6297648, by rfl⟩ : syracuseStep 16793729 = 12595297) B12595297
theorem B11195819 : Blo 2211435 11195819 := bstep (se 1 (by rfl) ⟨8396864, by rfl⟩ : syracuseStep 11195819 = 16793729) B16793729
theorem B7463879 : Blo 2211435 7463879 := bstep (se 1 (by rfl) ⟨5597909, by rfl⟩ : syracuseStep 7463879 = 11195819) B11195819
theorem B4975919 : Blo 2211435 4975919 := bstep (se 1 (by rfl) ⟨3731939, by rfl⟩ : syracuseStep 4975919 = 7463879) B7463879
theorem B3317279 : Blo 2211435 3317279 := bstep (se 1 (by rfl) ⟨2487959, by rfl⟩ : syracuseStep 3317279 = 4975919) B4975919
theorem B2211519 : Blo 2211435 2211519 := bstep (se 1 (by rfl) ⟨1658639, by rfl⟩ : syracuseStep 2211519 = 3317279) B3317279
theorem B3317285 : Blo 2211435 3317285 := bbase (se 4 (by rfl) ⟨310995, by rfl⟩ : syracuseStep 3317285 = 621991) (by norm_num)
theorem B2211523 : Blo 2211435 2211523 := bstep (se 1 (by rfl) ⟨1658642, by rfl⟩ : syracuseStep 2211523 = 3317285) B3317285
theorem B2798965 : Blo 2211435 2798965 := bbase (se 5 (by rfl) ⟨131201, by rfl⟩ : syracuseStep 2798965 = 262403) (by norm_num)
theorem B3731953 : Blo 2211435 3731953 := bstep (se 2 (by rfl) ⟨1399482, by rfl⟩ : syracuseStep 3731953 = 2798965) B2798965
theorem B4975937 : Blo 2211435 4975937 := bstep (se 2 (by rfl) ⟨1865976, by rfl⟩ : syracuseStep 4975937 = 3731953) B3731953
theorem B3317291 : Blo 2211435 3317291 := bstep (se 1 (by rfl) ⟨2487968, by rfl⟩ : syracuseStep 3317291 = 4975937) B4975937
theorem B2211527 : Blo 2211435 2211527 := bstep (se 1 (by rfl) ⟨1658645, by rfl⟩ : syracuseStep 2211527 = 3317291) B3317291
theorem B2487973 : Blo 2211435 2487973 := bbase (se 4 (by rfl) ⟨233247, by rfl⟩ : syracuseStep 2487973 = 466495) (by norm_num)
theorem B3317297 : Blo 2211435 3317297 := bstep (se 2 (by rfl) ⟨1243986, by rfl⟩ : syracuseStep 3317297 = 2487973) B2487973
theorem B2211531 : Blo 2211435 2211531 := bstep (se 1 (by rfl) ⟨1658648, by rfl⟩ : syracuseStep 2211531 = 3317297) B3317297
theorem B8966837 : Blo 2211435 8966837 := bbase (se 5 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 8966837 = 840641) (by norm_num)
theorem B5977891 : Blo 2211435 5977891 := bstep (se 1 (by rfl) ⟨4483418, by rfl⟩ : syracuseStep 5977891 = 8966837) B8966837
theorem B31882085 : Blo 2211435 31882085 := bstep (se 4 (by rfl) ⟨2988945, by rfl⟩ : syracuseStep 31882085 = 5977891) B5977891
theorem B21254723 : Blo 2211435 21254723 := bstep (se 1 (by rfl) ⟨15941042, by rfl⟩ : syracuseStep 21254723 = 31882085) B31882085
theorem B14169815 : Blo 2211435 14169815 := bstep (se 1 (by rfl) ⟨10627361, by rfl⟩ : syracuseStep 14169815 = 21254723) B21254723
theorem B9446543 : Blo 2211435 9446543 := bstep (se 1 (by rfl) ⟨7084907, by rfl⟩ : syracuseStep 9446543 = 14169815) B14169815
theorem B6297695 : Blo 2211435 6297695 := bstep (se 1 (by rfl) ⟨4723271, by rfl⟩ : syracuseStep 6297695 = 9446543) B9446543
theorem B4198463 : Blo 2211435 4198463 := bstep (se 1 (by rfl) ⟨3148847, by rfl⟩ : syracuseStep 4198463 = 6297695) B6297695
theorem B2798975 : Blo 2211435 2798975 := bstep (se 1 (by rfl) ⟨2099231, by rfl⟩ : syracuseStep 2798975 = 4198463) B4198463
theorem B7463933 : Blo 2211435 7463933 := bstep (se 3 (by rfl) ⟨1399487, by rfl⟩ : syracuseStep 7463933 = 2798975) B2798975
theorem B4975955 : Blo 2211435 4975955 := bstep (se 1 (by rfl) ⟨3731966, by rfl⟩ : syracuseStep 4975955 = 7463933) B7463933
theorem B3317303 : Blo 2211435 3317303 := bstep (se 1 (by rfl) ⟨2487977, by rfl⟩ : syracuseStep 3317303 = 4975955) B4975955
theorem B2211535 : Blo 2211435 2211535 := bstep (se 1 (by rfl) ⟨1658651, by rfl⟩ : syracuseStep 2211535 = 3317303) B3317303
theorem B3317309 : Blo 2211435 3317309 := bbase (se 3 (by rfl) ⟨621995, by rfl⟩ : syracuseStep 3317309 = 1243991) (by norm_num)
theorem B2211539 : Blo 2211435 2211539 := bstep (se 1 (by rfl) ⟨1658654, by rfl⟩ : syracuseStep 2211539 = 3317309) B3317309
theorem B4975973 : Blo 2211435 4975973 := bbase (se 4 (by rfl) ⟨466497, by rfl⟩ : syracuseStep 4975973 = 932995) (by norm_num)
theorem B3317315 : Blo 2211435 3317315 := bstep (se 1 (by rfl) ⟨2487986, by rfl⟩ : syracuseStep 3317315 = 4975973) B4975973
theorem B2211543 : Blo 2211435 2211543 := bstep (se 1 (by rfl) ⟨1658657, by rfl⟩ : syracuseStep 2211543 = 3317315) B3317315
theorem B5597981 : Blo 2211435 5597981 := bbase (se 3 (by rfl) ⟨1049621, by rfl⟩ : syracuseStep 5597981 = 2099243) (by norm_num)
theorem B3731987 : Blo 2211435 3731987 := bstep (se 1 (by rfl) ⟨2798990, by rfl⟩ : syracuseStep 3731987 = 5597981) B5597981
theorem B2487991 : Blo 2211435 2487991 := bstep (se 1 (by rfl) ⟨1865993, by rfl⟩ : syracuseStep 2487991 = 3731987) B3731987
theorem B3317321 : Blo 2211435 3317321 := bstep (se 2 (by rfl) ⟨1243995, by rfl⟩ : syracuseStep 3317321 = 2487991) B2487991
theorem B2211547 : Blo 2211435 2211547 := bstep (se 1 (by rfl) ⟨1658660, by rfl⟩ : syracuseStep 2211547 = 3317321) B3317321
theorem B4198493 : Blo 2211435 4198493 := bbase (se 3 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 4198493 = 1574435) (by norm_num)
theorem B11195981 : Blo 2211435 11195981 := bstep (se 3 (by rfl) ⟨2099246, by rfl⟩ : syracuseStep 11195981 = 4198493) B4198493
theorem B7463987 : Blo 2211435 7463987 := bstep (se 1 (by rfl) ⟨5597990, by rfl⟩ : syracuseStep 7463987 = 11195981) B11195981
theorem B4975991 : Blo 2211435 4975991 := bstep (se 1 (by rfl) ⟨3731993, by rfl⟩ : syracuseStep 4975991 = 7463987) B7463987
theorem B3317327 : Blo 2211435 3317327 := bstep (se 1 (by rfl) ⟨2487995, by rfl⟩ : syracuseStep 3317327 = 4975991) B4975991
theorem B2211551 : Blo 2211435 2211551 := bstep (se 1 (by rfl) ⟨1658663, by rfl⟩ : syracuseStep 2211551 = 3317327) B3317327
theorem B3317333 : Blo 2211435 3317333 := bbase (se 8 (by rfl) ⟨19437, by rfl⟩ : syracuseStep 3317333 = 38875) (by norm_num)
theorem B2211555 : Blo 2211435 2211555 := bstep (se 1 (by rfl) ⟨1658666, by rfl⟩ : syracuseStep 2211555 = 3317333) B3317333
theorem B9446645 : Blo 2211435 9446645 := bbase (se 5 (by rfl) ⟨442811, by rfl⟩ : syracuseStep 9446645 = 885623) (by norm_num)
theorem B6297763 : Blo 2211435 6297763 := bstep (se 1 (by rfl) ⟨4723322, by rfl⟩ : syracuseStep 6297763 = 9446645) B9446645
theorem B8397017 : Blo 2211435 8397017 := bstep (se 2 (by rfl) ⟨3148881, by rfl⟩ : syracuseStep 8397017 = 6297763) B6297763
theorem B5598011 : Blo 2211435 5598011 := bstep (se 1 (by rfl) ⟨4198508, by rfl⟩ : syracuseStep 5598011 = 8397017) B8397017
theorem B3732007 : Blo 2211435 3732007 := bstep (se 1 (by rfl) ⟨2799005, by rfl⟩ : syracuseStep 3732007 = 5598011) B5598011
theorem B4976009 : Blo 2211435 4976009 := bstep (se 2 (by rfl) ⟨1866003, by rfl⟩ : syracuseStep 4976009 = 3732007) B3732007
theorem B3317339 : Blo 2211435 3317339 := bstep (se 1 (by rfl) ⟨2488004, by rfl⟩ : syracuseStep 3317339 = 4976009) B4976009
theorem B2211559 : Blo 2211435 2211559 := bstep (se 1 (by rfl) ⟨1658669, by rfl⟩ : syracuseStep 2211559 = 3317339) B3317339
theorem B2488009 : Blo 2211435 2488009 := bbase (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) (by norm_num)
theorem B3317345 : Blo 2211435 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B2211563 : Blo 2211435 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B5313757 : Blo 2211435 5313757 := bbase (se 3 (by rfl) ⟨996329, by rfl⟩ : syracuseStep 5313757 = 1992659) (by norm_num)
theorem B7085009 : Blo 2211435 7085009 := bstep (se 2 (by rfl) ⟨2656878, by rfl⟩ : syracuseStep 7085009 = 5313757) B5313757
theorem B18893357 : Blo 2211435 18893357 := bstep (se 3 (by rfl) ⟨3542504, by rfl⟩ : syracuseStep 18893357 = 7085009) B7085009
theorem B12595571 : Blo 2211435 12595571 := bstep (se 1 (by rfl) ⟨9446678, by rfl⟩ : syracuseStep 12595571 = 18893357) B18893357
theorem B8397047 : Blo 2211435 8397047 := bstep (se 1 (by rfl) ⟨6297785, by rfl⟩ : syracuseStep 8397047 = 12595571) B12595571
theorem B5598031 : Blo 2211435 5598031 := bstep (se 1 (by rfl) ⟨4198523, by rfl⟩ : syracuseStep 5598031 = 8397047) B8397047
theorem B7464041 : Blo 2211435 7464041 := bstep (se 2 (by rfl) ⟨2799015, by rfl⟩ : syracuseStep 7464041 = 5598031) B5598031
theorem B4976027 : Blo 2211435 4976027 := bstep (se 1 (by rfl) ⟨3732020, by rfl⟩ : syracuseStep 4976027 = 7464041) B7464041
theorem B3317351 : Blo 2211435 3317351 := bstep (se 1 (by rfl) ⟨2488013, by rfl⟩ : syracuseStep 3317351 = 4976027) B4976027
theorem B2211567 : Blo 2211435 2211567 := bstep (se 1 (by rfl) ⟨1658675, by rfl⟩ : syracuseStep 2211567 = 3317351) B3317351
theorem B3317357 : Blo 2211435 3317357 := bbase (se 3 (by rfl) ⟨622004, by rfl⟩ : syracuseStep 3317357 = 1244009) (by norm_num)
theorem B2211571 : Blo 2211435 2211571 := bstep (se 1 (by rfl) ⟨1658678, by rfl⟩ : syracuseStep 2211571 = 3317357) B3317357
theorem B4976045 : Blo 2211435 4976045 := bbase (se 3 (by rfl) ⟨933008, by rfl⟩ : syracuseStep 4976045 = 1866017) (by norm_num)
theorem B3317363 : Blo 2211435 3317363 := bstep (se 1 (by rfl) ⟨2488022, by rfl⟩ : syracuseStep 3317363 = 4976045) B4976045
theorem B2211575 : Blo 2211435 2211575 := bstep (se 1 (by rfl) ⟨1658681, by rfl⟩ : syracuseStep 2211575 = 3317363) B3317363
theorem B3542525 : Blo 2211435 3542525 := bbase (se 3 (by rfl) ⟨664223, by rfl⟩ : syracuseStep 3542525 = 1328447) (by norm_num)
theorem B2361683 : Blo 2211435 2361683 := bstep (se 1 (by rfl) ⟨1771262, by rfl⟩ : syracuseStep 2361683 = 3542525) B3542525
theorem B6297821 : Blo 2211435 6297821 := bstep (se 3 (by rfl) ⟨1180841, by rfl⟩ : syracuseStep 6297821 = 2361683) B2361683
theorem B4198547 : Blo 2211435 4198547 := bstep (se 1 (by rfl) ⟨3148910, by rfl⟩ : syracuseStep 4198547 = 6297821) B6297821
theorem B2799031 : Blo 2211435 2799031 := bstep (se 1 (by rfl) ⟨2099273, by rfl⟩ : syracuseStep 2799031 = 4198547) B4198547
theorem B3732041 : Blo 2211435 3732041 := bstep (se 2 (by rfl) ⟨1399515, by rfl⟩ : syracuseStep 3732041 = 2799031) B2799031
theorem B2488027 : Blo 2211435 2488027 := bstep (se 1 (by rfl) ⟨1866020, by rfl⟩ : syracuseStep 2488027 = 3732041) B3732041
theorem B3317369 : Blo 2211435 3317369 := bstep (se 2 (by rfl) ⟨1244013, by rfl⟩ : syracuseStep 3317369 = 2488027) B2488027
theorem B2211579 : Blo 2211435 2211579 := bstep (se 1 (by rfl) ⟨1658684, by rfl⟩ : syracuseStep 2211579 = 3317369) B3317369
theorem B8967029 : Blo 2211435 8967029 := bbase (se 5 (by rfl) ⟨420329, by rfl⟩ : syracuseStep 8967029 = 840659) (by norm_num)
theorem B95648309 : Blo 2211435 95648309 := bstep (se 5 (by rfl) ⟨4483514, by rfl⟩ : syracuseStep 95648309 = 8967029) B8967029
theorem B63765539 : Blo 2211435 63765539 := bstep (se 1 (by rfl) ⟨47824154, by rfl⟩ : syracuseStep 63765539 = 95648309) B95648309
theorem B42510359 : Blo 2211435 42510359 := bstep (se 1 (by rfl) ⟨31882769, by rfl⟩ : syracuseStep 42510359 = 63765539) B63765539
theorem B28340239 : Blo 2211435 28340239 := bstep (se 1 (by rfl) ⟨21255179, by rfl⟩ : syracuseStep 28340239 = 42510359) B42510359
theorem B37786985 : Blo 2211435 37786985 := bstep (se 2 (by rfl) ⟨14170119, by rfl⟩ : syracuseStep 37786985 = 28340239) B28340239
theorem B25191323 : Blo 2211435 25191323 := bstep (se 1 (by rfl) ⟨18893492, by rfl⟩ : syracuseStep 25191323 = 37786985) B37786985
theorem B16794215 : Blo 2211435 16794215 := bstep (se 1 (by rfl) ⟨12595661, by rfl⟩ : syracuseStep 16794215 = 25191323) B25191323
theorem B11196143 : Blo 2211435 11196143 := bstep (se 1 (by rfl) ⟨8397107, by rfl⟩ : syracuseStep 11196143 = 16794215) B16794215
theorem B7464095 : Blo 2211435 7464095 := bstep (se 1 (by rfl) ⟨5598071, by rfl⟩ : syracuseStep 7464095 = 11196143) B11196143
theorem B4976063 : Blo 2211435 4976063 := bstep (se 1 (by rfl) ⟨3732047, by rfl⟩ : syracuseStep 4976063 = 7464095) B7464095
theorem B3317375 : Blo 2211435 3317375 := bstep (se 1 (by rfl) ⟨2488031, by rfl⟩ : syracuseStep 3317375 = 4976063) B4976063
theorem B2211583 : Blo 2211435 2211583 := bstep (se 1 (by rfl) ⟨1658687, by rfl⟩ : syracuseStep 2211583 = 3317375) B3317375
theorem B3317381 : Blo 2211435 3317381 := bbase (se 4 (by rfl) ⟨311004, by rfl⟩ : syracuseStep 3317381 = 622009) (by norm_num)
theorem B2211587 : Blo 2211435 2211587 := bstep (se 1 (by rfl) ⟨1658690, by rfl⟩ : syracuseStep 2211587 = 3317381) B3317381
theorem B3732061 : Blo 2211435 3732061 := bbase (se 3 (by rfl) ⟨699761, by rfl⟩ : syracuseStep 3732061 = 1399523) (by norm_num)
theorem B4976081 : Blo 2211435 4976081 := bstep (se 2 (by rfl) ⟨1866030, by rfl⟩ : syracuseStep 4976081 = 3732061) B3732061
theorem B3317387 : Blo 2211435 3317387 := bstep (se 1 (by rfl) ⟨2488040, by rfl⟩ : syracuseStep 3317387 = 4976081) B4976081
theorem B2211591 : Blo 2211435 2211591 := bstep (se 1 (by rfl) ⟨1658693, by rfl⟩ : syracuseStep 2211591 = 3317387) B3317387
theorem B2488045 : Blo 2211435 2488045 := bbase (se 3 (by rfl) ⟨466508, by rfl⟩ : syracuseStep 2488045 = 933017) (by norm_num)
theorem B3317393 : Blo 2211435 3317393 := bstep (se 2 (by rfl) ⟨1244022, by rfl⟩ : syracuseStep 3317393 = 2488045) B2488045
theorem B2211595 : Blo 2211435 2211595 := bstep (se 1 (by rfl) ⟨1658696, by rfl⟩ : syracuseStep 2211595 = 3317393) B3317393
theorem B7464149 : Blo 2211435 7464149 := bbase (se 7 (by rfl) ⟨87470, by rfl⟩ : syracuseStep 7464149 = 174941) (by norm_num)
theorem B4976099 : Blo 2211435 4976099 := bstep (se 1 (by rfl) ⟨3732074, by rfl⟩ : syracuseStep 4976099 = 7464149) B7464149
theorem B3317399 : Blo 2211435 3317399 := bstep (se 1 (by rfl) ⟨2488049, by rfl⟩ : syracuseStep 3317399 = 4976099) B4976099
theorem B2211599 : Blo 2211435 2211599 := bstep (se 1 (by rfl) ⟨1658699, by rfl⟩ : syracuseStep 2211599 = 3317399) B3317399
theorem B3317405 : Blo 2211435 3317405 := bbase (se 3 (by rfl) ⟨622013, by rfl⟩ : syracuseStep 3317405 = 1244027) (by norm_num)
theorem B2211603 : Blo 2211435 2211603 := bstep (se 1 (by rfl) ⟨1658702, by rfl⟩ : syracuseStep 2211603 = 3317405) B3317405
theorem B4976117 : Blo 2211435 4976117 := bbase (se 5 (by rfl) ⟨233255, by rfl⟩ : syracuseStep 4976117 = 466511) (by norm_num)
theorem B3317411 : Blo 2211435 3317411 := bstep (se 1 (by rfl) ⟨2488058, by rfl⟩ : syracuseStep 3317411 = 4976117) B4976117
theorem B2211607 : Blo 2211435 2211607 := bstep (se 1 (by rfl) ⟨1658705, by rfl⟩ : syracuseStep 2211607 = 3317411) B3317411
theorem B3590909 : Blo 2211435 3590909 := bbase (se 3 (by rfl) ⟨673295, by rfl⟩ : syracuseStep 3590909 = 1346591) (by norm_num)
theorem B2393939 : Blo 2211435 2393939 := bstep (se 1 (by rfl) ⟨1795454, by rfl⟩ : syracuseStep 2393939 = 3590909) B3590909
theorem B6383837 : Blo 2211435 6383837 := bstep (se 3 (by rfl) ⟨1196969, by rfl⟩ : syracuseStep 6383837 = 2393939) B2393939
theorem B4255891 : Blo 2211435 4255891 := bstep (se 1 (by rfl) ⟨3191918, by rfl⟩ : syracuseStep 4255891 = 6383837) B6383837
theorem B22698085 : Blo 2211435 22698085 := bstep (se 4 (by rfl) ⟨2127945, by rfl⟩ : syracuseStep 22698085 = 4255891) B4255891
theorem B30264113 : Blo 2211435 30264113 := bstep (se 2 (by rfl) ⟨11349042, by rfl⟩ : syracuseStep 30264113 = 22698085) B22698085
theorem B20176075 : Blo 2211435 20176075 := bstep (se 1 (by rfl) ⟨15132056, by rfl⟩ : syracuseStep 20176075 = 30264113) B30264113
theorem B26901433 : Blo 2211435 26901433 := bstep (se 2 (by rfl) ⟨10088037, by rfl⟩ : syracuseStep 26901433 = 20176075) B20176075
theorem B35868577 : Blo 2211435 35868577 := bstep (se 2 (by rfl) ⟨13450716, by rfl⟩ : syracuseStep 35868577 = 26901433) B26901433
theorem B47824769 : Blo 2211435 47824769 := bstep (se 2 (by rfl) ⟨17934288, by rfl⟩ : syracuseStep 47824769 = 35868577) B35868577
theorem B31883179 : Blo 2211435 31883179 := bstep (se 1 (by rfl) ⟨23912384, by rfl⟩ : syracuseStep 31883179 = 47824769) B47824769
theorem B42510905 : Blo 2211435 42510905 := bstep (se 2 (by rfl) ⟨15941589, by rfl⟩ : syracuseStep 42510905 = 31883179) B31883179
theorem B28340603 : Blo 2211435 28340603 := bstep (se 1 (by rfl) ⟨21255452, by rfl⟩ : syracuseStep 28340603 = 42510905) B42510905
theorem B18893735 : Blo 2211435 18893735 := bstep (se 1 (by rfl) ⟨14170301, by rfl⟩ : syracuseStep 18893735 = 28340603) B28340603
theorem B12595823 : Blo 2211435 12595823 := bstep (se 1 (by rfl) ⟨9446867, by rfl⟩ : syracuseStep 12595823 = 18893735) B18893735
theorem B8397215 : Blo 2211435 8397215 := bstep (se 1 (by rfl) ⟨6297911, by rfl⟩ : syracuseStep 8397215 = 12595823) B12595823
theorem B5598143 : Blo 2211435 5598143 := bstep (se 1 (by rfl) ⟨4198607, by rfl⟩ : syracuseStep 5598143 = 8397215) B8397215
theorem B3732095 : Blo 2211435 3732095 := bstep (se 1 (by rfl) ⟨2799071, by rfl⟩ : syracuseStep 3732095 = 5598143) B5598143
theorem B2488063 : Blo 2211435 2488063 := bstep (se 1 (by rfl) ⟨1866047, by rfl⟩ : syracuseStep 2488063 = 3732095) B3732095
theorem B3317417 : Blo 2211435 3317417 := bstep (se 2 (by rfl) ⟨1244031, by rfl⟩ : syracuseStep 3317417 = 2488063) B2488063
theorem B2211611 : Blo 2211435 2211611 := bstep (se 1 (by rfl) ⟨1658708, by rfl⟩ : syracuseStep 2211611 = 3317417) B3317417
theorem B2361721 : Blo 2211435 2361721 := bbase (se 2 (by rfl) ⟨885645, by rfl⟩ : syracuseStep 2361721 = 1771291) (by norm_num)
theorem B3148961 : Blo 2211435 3148961 := bstep (se 2 (by rfl) ⟨1180860, by rfl⟩ : syracuseStep 3148961 = 2361721) B2361721
theorem B8397229 : Blo 2211435 8397229 := bstep (se 3 (by rfl) ⟨1574480, by rfl⟩ : syracuseStep 8397229 = 3148961) B3148961
theorem B11196305 : Blo 2211435 11196305 := bstep (se 2 (by rfl) ⟨4198614, by rfl⟩ : syracuseStep 11196305 = 8397229) B8397229
theorem B7464203 : Blo 2211435 7464203 := bstep (se 1 (by rfl) ⟨5598152, by rfl⟩ : syracuseStep 7464203 = 11196305) B11196305
theorem B4976135 : Blo 2211435 4976135 := bstep (se 1 (by rfl) ⟨3732101, by rfl⟩ : syracuseStep 4976135 = 7464203) B7464203
theorem B3317423 : Blo 2211435 3317423 := bstep (se 1 (by rfl) ⟨2488067, by rfl⟩ : syracuseStep 3317423 = 4976135) B4976135
theorem B2211615 : Blo 2211435 2211615 := bstep (se 1 (by rfl) ⟨1658711, by rfl⟩ : syracuseStep 2211615 = 3317423) B3317423
theorem B3317429 : Blo 2211435 3317429 := bbase (se 5 (by rfl) ⟨155504, by rfl⟩ : syracuseStep 3317429 = 311009) (by norm_num)
theorem B2211619 : Blo 2211435 2211619 := bstep (se 1 (by rfl) ⟨1658714, by rfl⟩ : syracuseStep 2211619 = 3317429) B3317429
theorem B5598173 : Blo 2211435 5598173 := bbase (se 3 (by rfl) ⟨1049657, by rfl⟩ : syracuseStep 5598173 = 2099315) (by norm_num)
theorem B3732115 : Blo 2211435 3732115 := bstep (se 1 (by rfl) ⟨2799086, by rfl⟩ : syracuseStep 3732115 = 5598173) B5598173
theorem B4976153 : Blo 2211435 4976153 := bstep (se 2 (by rfl) ⟨1866057, by rfl⟩ : syracuseStep 4976153 = 3732115) B3732115
theorem B3317435 : Blo 2211435 3317435 := bstep (se 1 (by rfl) ⟨2488076, by rfl⟩ : syracuseStep 3317435 = 4976153) B4976153
theorem B2211623 : Blo 2211435 2211623 := bstep (se 1 (by rfl) ⟨1658717, by rfl⟩ : syracuseStep 2211623 = 3317435) B3317435
theorem B2488081 : Blo 2211435 2488081 := bbase (se 2 (by rfl) ⟨933030, by rfl⟩ : syracuseStep 2488081 = 1866061) (by norm_num)
theorem B3317441 : Blo 2211435 3317441 := bstep (se 2 (by rfl) ⟨1244040, by rfl⟩ : syracuseStep 3317441 = 2488081) B2488081
theorem B2211627 : Blo 2211435 2211627 := bstep (se 1 (by rfl) ⟨1658720, by rfl⟩ : syracuseStep 2211627 = 3317441) B3317441
theorem B4198645 : Blo 2211435 4198645 := bbase (se 5 (by rfl) ⟨196811, by rfl⟩ : syracuseStep 4198645 = 393623) (by norm_num)
theorem B5598193 : Blo 2211435 5598193 := bstep (se 2 (by rfl) ⟨2099322, by rfl⟩ : syracuseStep 5598193 = 4198645) B4198645
theorem B7464257 : Blo 2211435 7464257 := bstep (se 2 (by rfl) ⟨2799096, by rfl⟩ : syracuseStep 7464257 = 5598193) B5598193
theorem B4976171 : Blo 2211435 4976171 := bstep (se 1 (by rfl) ⟨3732128, by rfl⟩ : syracuseStep 4976171 = 7464257) B7464257
theorem B3317447 : Blo 2211435 3317447 := bstep (se 1 (by rfl) ⟨2488085, by rfl⟩ : syracuseStep 3317447 = 4976171) B4976171
theorem B2211631 : Blo 2211435 2211631 := bstep (se 1 (by rfl) ⟨1658723, by rfl⟩ : syracuseStep 2211631 = 3317447) B3317447
theorem B3317453 : Blo 2211435 3317453 := bbase (se 3 (by rfl) ⟨622022, by rfl⟩ : syracuseStep 3317453 = 1244045) (by norm_num)
theorem B2211635 : Blo 2211435 2211635 := bstep (se 1 (by rfl) ⟨1658726, by rfl⟩ : syracuseStep 2211635 = 3317453) B3317453
theorem B4976189 : Blo 2211435 4976189 := bbase (se 3 (by rfl) ⟨933035, by rfl⟩ : syracuseStep 4976189 = 1866071) (by norm_num)
theorem B3317459 : Blo 2211435 3317459 := bstep (se 1 (by rfl) ⟨2488094, by rfl⟩ : syracuseStep 3317459 = 4976189) B4976189
theorem B2211639 : Blo 2211435 2211639 := bstep (se 1 (by rfl) ⟨1658729, by rfl⟩ : syracuseStep 2211639 = 3317459) B3317459
theorem B3732149 : Blo 2211435 3732149 := bbase (se 5 (by rfl) ⟨174944, by rfl⟩ : syracuseStep 3732149 = 349889) (by norm_num)
theorem B2488099 : Blo 2211435 2488099 := bstep (se 1 (by rfl) ⟨1866074, by rfl⟩ : syracuseStep 2488099 = 3732149) B3732149
theorem B3317465 : Blo 2211435 3317465 := bstep (se 2 (by rfl) ⟨1244049, by rfl⟩ : syracuseStep 3317465 = 2488099) B2488099
theorem B2211643 : Blo 2211435 2211643 := bstep (se 1 (by rfl) ⟨1658732, by rfl⟩ : syracuseStep 2211643 = 3317465) B3317465
theorem B8511925 : Blo 2211435 8511925 := bbase (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) (by norm_num)
theorem B11349233 : Blo 2211435 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B7566155 : Blo 2211435 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B5044103 : Blo 2211435 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B3362735 : Blo 2211435 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B8967293 : Blo 2211435 8967293 := bstep (se 3 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 8967293 = 3362735) B3362735
theorem B5978195 : Blo 2211435 5978195 := bstep (se 1 (by rfl) ⟨4483646, by rfl⟩ : syracuseStep 5978195 = 8967293) B8967293
theorem B3985463 : Blo 2211435 3985463 := bstep (se 1 (by rfl) ⟨2989097, by rfl⟩ : syracuseStep 3985463 = 5978195) B5978195
theorem B2656975 : Blo 2211435 2656975 := bstep (se 1 (by rfl) ⟨1992731, by rfl⟩ : syracuseStep 2656975 = 3985463) B3985463
theorem B3542633 : Blo 2211435 3542633 := bstep (se 2 (by rfl) ⟨1328487, by rfl⟩ : syracuseStep 3542633 = 2656975) B2656975
theorem B2361755 : Blo 2211435 2361755 := bstep (se 1 (by rfl) ⟨1771316, by rfl⟩ : syracuseStep 2361755 = 3542633) B3542633
theorem B6298013 : Blo 2211435 6298013 := bstep (se 3 (by rfl) ⟨1180877, by rfl⟩ : syracuseStep 6298013 = 2361755) B2361755
theorem B16794701 : Blo 2211435 16794701 := bstep (se 3 (by rfl) ⟨3149006, by rfl⟩ : syracuseStep 16794701 = 6298013) B6298013
theorem B11196467 : Blo 2211435 11196467 := bstep (se 1 (by rfl) ⟨8397350, by rfl⟩ : syracuseStep 11196467 = 16794701) B16794701
theorem B7464311 : Blo 2211435 7464311 := bstep (se 1 (by rfl) ⟨5598233, by rfl⟩ : syracuseStep 7464311 = 11196467) B11196467
theorem B4976207 : Blo 2211435 4976207 := bstep (se 1 (by rfl) ⟨3732155, by rfl⟩ : syracuseStep 4976207 = 7464311) B7464311
theorem B3317471 : Blo 2211435 3317471 := bstep (se 1 (by rfl) ⟨2488103, by rfl⟩ : syracuseStep 3317471 = 4976207) B4976207
theorem B2211647 : Blo 2211435 2211647 := bstep (se 1 (by rfl) ⟨1658735, by rfl⟩ : syracuseStep 2211647 = 3317471) B3317471
theorem B3317477 : Blo 2211435 3317477 := bbase (se 4 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 3317477 = 622027) (by norm_num)
theorem B2211651 : Blo 2211435 2211651 := bstep (se 1 (by rfl) ⟨1658738, by rfl⟩ : syracuseStep 2211651 = 3317477) B3317477
theorem B6298037 : Blo 2211435 6298037 := bbase (se 5 (by rfl) ⟨295220, by rfl⟩ : syracuseStep 6298037 = 590441) (by norm_num)
theorem B4198691 : Blo 2211435 4198691 := bstep (se 1 (by rfl) ⟨3149018, by rfl⟩ : syracuseStep 4198691 = 6298037) B6298037
theorem B2799127 : Blo 2211435 2799127 := bstep (se 1 (by rfl) ⟨2099345, by rfl⟩ : syracuseStep 2799127 = 4198691) B4198691
theorem B3732169 : Blo 2211435 3732169 := bstep (se 2 (by rfl) ⟨1399563, by rfl⟩ : syracuseStep 3732169 = 2799127) B2799127
theorem B4976225 : Blo 2211435 4976225 := bstep (se 2 (by rfl) ⟨1866084, by rfl⟩ : syracuseStep 4976225 = 3732169) B3732169
theorem B3317483 : Blo 2211435 3317483 := bstep (se 1 (by rfl) ⟨2488112, by rfl⟩ : syracuseStep 3317483 = 4976225) B4976225
theorem B2211655 : Blo 2211435 2211655 := bstep (se 1 (by rfl) ⟨1658741, by rfl⟩ : syracuseStep 2211655 = 3317483) B3317483
theorem B2488117 : Blo 2211435 2488117 := bbase (se 5 (by rfl) ⟨116630, by rfl⟩ : syracuseStep 2488117 = 233261) (by norm_num)
theorem B3317489 : Blo 2211435 3317489 := bstep (se 2 (by rfl) ⟨1244058, by rfl⟩ : syracuseStep 3317489 = 2488117) B2488117
theorem B2211659 : Blo 2211435 2211659 := bstep (se 1 (by rfl) ⟨1658744, by rfl⟩ : syracuseStep 2211659 = 3317489) B3317489
theorem B2799137 : Blo 2211435 2799137 := bbase (se 2 (by rfl) ⟨1049676, by rfl⟩ : syracuseStep 2799137 = 2099353) (by norm_num)
theorem B7464365 : Blo 2211435 7464365 := bstep (se 3 (by rfl) ⟨1399568, by rfl⟩ : syracuseStep 7464365 = 2799137) B2799137
theorem B4976243 : Blo 2211435 4976243 := bstep (se 1 (by rfl) ⟨3732182, by rfl⟩ : syracuseStep 4976243 = 7464365) B7464365
theorem B3317495 : Blo 2211435 3317495 := bstep (se 1 (by rfl) ⟨2488121, by rfl⟩ : syracuseStep 3317495 = 4976243) B4976243
theorem B2211663 : Blo 2211435 2211663 := bstep (se 1 (by rfl) ⟨1658747, by rfl⟩ : syracuseStep 2211663 = 3317495) B3317495
theorem B3317501 : Blo 2211435 3317501 := bbase (se 3 (by rfl) ⟨622031, by rfl⟩ : syracuseStep 3317501 = 1244063) (by norm_num)
theorem B2211667 : Blo 2211435 2211667 := bstep (se 1 (by rfl) ⟨1658750, by rfl⟩ : syracuseStep 2211667 = 3317501) B3317501
theorem B4976261 : Blo 2211435 4976261 := bbase (se 4 (by rfl) ⟨466524, by rfl⟩ : syracuseStep 4976261 = 933049) (by norm_num)
theorem B3317507 : Blo 2211435 3317507 := bstep (se 1 (by rfl) ⟨2488130, by rfl⟩ : syracuseStep 3317507 = 4976261) B4976261
theorem B2211671 : Blo 2211435 2211671 := bstep (se 1 (by rfl) ⟨1658753, by rfl⟩ : syracuseStep 2211671 = 3317507) B3317507
theorem B2657009 : Blo 2211435 2657009 := bbase (se 2 (by rfl) ⟨996378, by rfl⟩ : syracuseStep 2657009 = 1992757) (by norm_num)
theorem B7085357 : Blo 2211435 7085357 := bstep (se 3 (by rfl) ⟨1328504, by rfl⟩ : syracuseStep 7085357 = 2657009) B2657009
theorem B4723571 : Blo 2211435 4723571 := bstep (se 1 (by rfl) ⟨3542678, by rfl⟩ : syracuseStep 4723571 = 7085357) B7085357
theorem B3149047 : Blo 2211435 3149047 := bstep (se 1 (by rfl) ⟨2361785, by rfl⟩ : syracuseStep 3149047 = 4723571) B4723571
theorem B4198729 : Blo 2211435 4198729 := bstep (se 2 (by rfl) ⟨1574523, by rfl⟩ : syracuseStep 4198729 = 3149047) B3149047
theorem B5598305 : Blo 2211435 5598305 := bstep (se 2 (by rfl) ⟨2099364, by rfl⟩ : syracuseStep 5598305 = 4198729) B4198729
theorem B3732203 : Blo 2211435 3732203 := bstep (se 1 (by rfl) ⟨2799152, by rfl⟩ : syracuseStep 3732203 = 5598305) B5598305
theorem B2488135 : Blo 2211435 2488135 := bstep (se 1 (by rfl) ⟨1866101, by rfl⟩ : syracuseStep 2488135 = 3732203) B3732203
theorem B3317513 : Blo 2211435 3317513 := bstep (se 2 (by rfl) ⟨1244067, by rfl⟩ : syracuseStep 3317513 = 2488135) B2488135
theorem B2211675 : Blo 2211435 2211675 := bstep (se 1 (by rfl) ⟨1658756, by rfl⟩ : syracuseStep 2211675 = 3317513) B3317513
theorem B11196629 : Blo 2211435 11196629 := bbase (se 7 (by rfl) ⟨131210, by rfl⟩ : syracuseStep 11196629 = 262421) (by norm_num)
theorem B7464419 : Blo 2211435 7464419 := bstep (se 1 (by rfl) ⟨5598314, by rfl⟩ : syracuseStep 7464419 = 11196629) B11196629
theorem B4976279 : Blo 2211435 4976279 := bstep (se 1 (by rfl) ⟨3732209, by rfl⟩ : syracuseStep 4976279 = 7464419) B7464419
theorem B3317519 : Blo 2211435 3317519 := bstep (se 1 (by rfl) ⟨2488139, by rfl⟩ : syracuseStep 3317519 = 4976279) B4976279
theorem B2211679 : Blo 2211435 2211679 := bstep (se 1 (by rfl) ⟨1658759, by rfl⟩ : syracuseStep 2211679 = 3317519) B3317519
theorem B3317525 : Blo 2211435 3317525 := bbase (se 6 (by rfl) ⟨77754, by rfl⟩ : syracuseStep 3317525 = 155509) (by norm_num)
theorem B2211683 : Blo 2211435 2211683 := bstep (se 1 (by rfl) ⟨1658762, by rfl⟩ : syracuseStep 2211683 = 3317525) B3317525
theorem B43092373 : Blo 2211435 43092373 := bbase (se 6 (by rfl) ⟨1009977, by rfl⟩ : syracuseStep 43092373 = 2019955) (by norm_num)
theorem B57456497 : Blo 2211435 57456497 := bstep (se 2 (by rfl) ⟨21546186, by rfl⟩ : syracuseStep 57456497 = 43092373) B43092373
theorem B153217325 : Blo 2211435 153217325 := bstep (se 3 (by rfl) ⟨28728248, by rfl⟩ : syracuseStep 153217325 = 57456497) B57456497
theorem B102144883 : Blo 2211435 102144883 := bstep (se 1 (by rfl) ⟨76608662, by rfl⟩ : syracuseStep 102144883 = 153217325) B153217325
theorem B136193177 : Blo 2211435 136193177 := bstep (se 2 (by rfl) ⟨51072441, by rfl⟩ : syracuseStep 136193177 = 102144883) B102144883
theorem B90795451 : Blo 2211435 90795451 := bstep (se 1 (by rfl) ⟨68096588, by rfl⟩ : syracuseStep 90795451 = 136193177) B136193177
theorem B121060601 : Blo 2211435 121060601 := bstep (se 2 (by rfl) ⟨45397725, by rfl⟩ : syracuseStep 121060601 = 90795451) B90795451
theorem B80707067 : Blo 2211435 80707067 := bstep (se 1 (by rfl) ⟨60530300, by rfl⟩ : syracuseStep 80707067 = 121060601) B121060601
theorem B53804711 : Blo 2211435 53804711 := bstep (se 1 (by rfl) ⟨40353533, by rfl⟩ : syracuseStep 53804711 = 80707067) B80707067
theorem B35869807 : Blo 2211435 35869807 := bstep (se 1 (by rfl) ⟨26902355, by rfl⟩ : syracuseStep 35869807 = 53804711) B53804711
theorem B47826409 : Blo 2211435 47826409 := bstep (se 2 (by rfl) ⟨17934903, by rfl⟩ : syracuseStep 47826409 = 35869807) B35869807
theorem B63768545 : Blo 2211435 63768545 := bstep (se 2 (by rfl) ⟨23913204, by rfl⟩ : syracuseStep 63768545 = 47826409) B47826409
theorem B42512363 : Blo 2211435 42512363 := bstep (se 1 (by rfl) ⟨31884272, by rfl⟩ : syracuseStep 42512363 = 63768545) B63768545
theorem B28341575 : Blo 2211435 28341575 := bstep (se 1 (by rfl) ⟨21256181, by rfl⟩ : syracuseStep 28341575 = 42512363) B42512363
theorem B18894383 : Blo 2211435 18894383 := bstep (se 1 (by rfl) ⟨14170787, by rfl⟩ : syracuseStep 18894383 = 28341575) B28341575
theorem B12596255 : Blo 2211435 12596255 := bstep (se 1 (by rfl) ⟨9447191, by rfl⟩ : syracuseStep 12596255 = 18894383) B18894383
theorem B8397503 : Blo 2211435 8397503 := bstep (se 1 (by rfl) ⟨6298127, by rfl⟩ : syracuseStep 8397503 = 12596255) B12596255
theorem B5598335 : Blo 2211435 5598335 := bstep (se 1 (by rfl) ⟨4198751, by rfl⟩ : syracuseStep 5598335 = 8397503) B8397503
theorem B3732223 : Blo 2211435 3732223 := bstep (se 1 (by rfl) ⟨2799167, by rfl⟩ : syracuseStep 3732223 = 5598335) B5598335
theorem B4976297 : Blo 2211435 4976297 := bstep (se 2 (by rfl) ⟨1866111, by rfl⟩ : syracuseStep 4976297 = 3732223) B3732223
theorem B3317531 : Blo 2211435 3317531 := bstep (se 1 (by rfl) ⟨2488148, by rfl⟩ : syracuseStep 3317531 = 4976297) B4976297
theorem B2211687 : Blo 2211435 2211687 := bstep (se 1 (by rfl) ⟨1658765, by rfl⟩ : syracuseStep 2211687 = 3317531) B3317531
theorem B2488153 : Blo 2211435 2488153 := bbase (se 2 (by rfl) ⟨933057, by rfl⟩ : syracuseStep 2488153 = 1866115) (by norm_num)
theorem B3317537 : Blo 2211435 3317537 := bstep (se 2 (by rfl) ⟨1244076, by rfl⟩ : syracuseStep 3317537 = 2488153) B2488153
theorem B2211691 : Blo 2211435 2211691 := bstep (se 1 (by rfl) ⟨1658768, by rfl⟩ : syracuseStep 2211691 = 3317537) B3317537
theorem B4723613 : Blo 2211435 4723613 := bbase (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) (by norm_num)
theorem B3149075 : Blo 2211435 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B8397533 : Blo 2211435 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B5598355 : Blo 2211435 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B7464473 : Blo 2211435 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B4976315 : Blo 2211435 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B3317543 : Blo 2211435 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B2211695 : Blo 2211435 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B3317549 : Blo 2211435 3317549 := bbase (se 3 (by rfl) ⟨622040, by rfl⟩ : syracuseStep 3317549 = 1244081) (by norm_num)
theorem B2211699 : Blo 2211435 2211699 := bstep (se 1 (by rfl) ⟨1658774, by rfl⟩ : syracuseStep 2211699 = 3317549) B3317549
theorem B4976333 : Blo 2211435 4976333 := bbase (se 3 (by rfl) ⟨933062, by rfl⟩ : syracuseStep 4976333 = 1866125) (by norm_num)
theorem B3317555 : Blo 2211435 3317555 := bstep (se 1 (by rfl) ⟨2488166, by rfl⟩ : syracuseStep 3317555 = 4976333) B4976333
theorem B2211703 : Blo 2211435 2211703 := bstep (se 1 (by rfl) ⟨1658777, by rfl⟩ : syracuseStep 2211703 = 3317555) B3317555
theorem B2799193 : Blo 2211435 2799193 := bbase (se 2 (by rfl) ⟨1049697, by rfl⟩ : syracuseStep 2799193 = 2099395) (by norm_num)
theorem B3732257 : Blo 2211435 3732257 := bstep (se 2 (by rfl) ⟨1399596, by rfl⟩ : syracuseStep 3732257 = 2799193) B2799193
theorem B2488171 : Blo 2211435 2488171 := bstep (se 1 (by rfl) ⟨1866128, by rfl⟩ : syracuseStep 2488171 = 3732257) B3732257
theorem B3317561 : Blo 2211435 3317561 := bstep (se 2 (by rfl) ⟨1244085, by rfl⟩ : syracuseStep 3317561 = 2488171) B2488171
theorem B2211707 : Blo 2211435 2211707 := bstep (se 1 (by rfl) ⟨1658780, by rfl⟩ : syracuseStep 2211707 = 3317561) B3317561
theorem B11504405 : Blo 2211435 11504405 := bbase (se 6 (by rfl) ⟨269634, by rfl⟩ : syracuseStep 11504405 = 539269) (by norm_num)
theorem B7669603 : Blo 2211435 7669603 := bstep (se 1 (by rfl) ⟨5752202, by rfl⟩ : syracuseStep 7669603 = 11504405) B11504405
theorem B10226137 : Blo 2211435 10226137 := bstep (se 2 (by rfl) ⟨3834801, by rfl⟩ : syracuseStep 10226137 = 7669603) B7669603
theorem B13634849 : Blo 2211435 13634849 := bstep (se 2 (by rfl) ⟨5113068, by rfl⟩ : syracuseStep 13634849 = 10226137) B10226137
theorem B36359597 : Blo 2211435 36359597 := bstep (se 3 (by rfl) ⟨6817424, by rfl⟩ : syracuseStep 36359597 = 13634849) B13634849
theorem B24239731 : Blo 2211435 24239731 := bstep (se 1 (by rfl) ⟨18179798, by rfl⟩ : syracuseStep 24239731 = 36359597) B36359597
theorem B32319641 : Blo 2211435 32319641 := bstep (se 2 (by rfl) ⟨12119865, by rfl⟩ : syracuseStep 32319641 = 24239731) B24239731
theorem B21546427 : Blo 2211435 21546427 := bstep (se 1 (by rfl) ⟨16159820, by rfl⟩ : syracuseStep 21546427 = 32319641) B32319641
theorem B28728569 : Blo 2211435 28728569 := bstep (se 2 (by rfl) ⟨10773213, by rfl⟩ : syracuseStep 28728569 = 21546427) B21546427
theorem B19152379 : Blo 2211435 19152379 := bstep (se 1 (by rfl) ⟨14364284, by rfl⟩ : syracuseStep 19152379 = 28728569) B28728569
theorem B25536505 : Blo 2211435 25536505 := bstep (se 2 (by rfl) ⟨9576189, by rfl⟩ : syracuseStep 25536505 = 19152379) B19152379
theorem B34048673 : Blo 2211435 34048673 := bstep (se 2 (by rfl) ⟨12768252, by rfl⟩ : syracuseStep 34048673 = 25536505) B25536505
theorem B22699115 : Blo 2211435 22699115 := bstep (se 1 (by rfl) ⟨17024336, by rfl⟩ : syracuseStep 22699115 = 34048673) B34048673
theorem B15132743 : Blo 2211435 15132743 := bstep (se 1 (by rfl) ⟨11349557, by rfl⟩ : syracuseStep 15132743 = 22699115) B22699115
theorem B10088495 : Blo 2211435 10088495 := bstep (se 1 (by rfl) ⟨7566371, by rfl⟩ : syracuseStep 10088495 = 15132743) B15132743
theorem B6725663 : Blo 2211435 6725663 := bstep (se 1 (by rfl) ⟨5044247, by rfl⟩ : syracuseStep 6725663 = 10088495) B10088495
theorem B4483775 : Blo 2211435 4483775 := bstep (se 1 (by rfl) ⟨3362831, by rfl⟩ : syracuseStep 4483775 = 6725663) B6725663
theorem B11956733 : Blo 2211435 11956733 := bstep (se 3 (by rfl) ⟨2241887, by rfl⟩ : syracuseStep 11956733 = 4483775) B4483775
theorem B7971155 : Blo 2211435 7971155 := bstep (se 1 (by rfl) ⟨5978366, by rfl⟩ : syracuseStep 7971155 = 11956733) B11956733
theorem B5314103 : Blo 2211435 5314103 := bstep (se 1 (by rfl) ⟨3985577, by rfl⟩ : syracuseStep 5314103 = 7971155) B7971155
theorem B3542735 : Blo 2211435 3542735 := bstep (se 1 (by rfl) ⟨2657051, by rfl⟩ : syracuseStep 3542735 = 5314103) B5314103
theorem B9447293 : Blo 2211435 9447293 := bstep (se 3 (by rfl) ⟨1771367, by rfl⟩ : syracuseStep 9447293 = 3542735) B3542735
theorem B25192781 : Blo 2211435 25192781 := bstep (se 3 (by rfl) ⟨4723646, by rfl⟩ : syracuseStep 25192781 = 9447293) B9447293
theorem B16795187 : Blo 2211435 16795187 := bstep (se 1 (by rfl) ⟨12596390, by rfl⟩ : syracuseStep 16795187 = 25192781) B25192781
theorem B11196791 : Blo 2211435 11196791 := bstep (se 1 (by rfl) ⟨8397593, by rfl⟩ : syracuseStep 11196791 = 16795187) B16795187
theorem B7464527 : Blo 2211435 7464527 := bstep (se 1 (by rfl) ⟨5598395, by rfl⟩ : syracuseStep 7464527 = 11196791) B11196791
theorem B4976351 : Blo 2211435 4976351 := bstep (se 1 (by rfl) ⟨3732263, by rfl⟩ : syracuseStep 4976351 = 7464527) B7464527
theorem B3317567 : Blo 2211435 3317567 := bstep (se 1 (by rfl) ⟨2488175, by rfl⟩ : syracuseStep 3317567 = 4976351) B4976351
theorem B2211711 : Blo 2211435 2211711 := bstep (se 1 (by rfl) ⟨1658783, by rfl⟩ : syracuseStep 2211711 = 3317567) B3317567
theorem B3317573 : Blo 2211435 3317573 := bbase (se 4 (by rfl) ⟨311022, by rfl⟩ : syracuseStep 3317573 = 622045) (by norm_num)
theorem B2211715 : Blo 2211435 2211715 := bstep (se 1 (by rfl) ⟨1658786, by rfl⟩ : syracuseStep 2211715 = 3317573) B3317573
theorem B3732277 : Blo 2211435 3732277 := bbase (se 5 (by rfl) ⟨174950, by rfl⟩ : syracuseStep 3732277 = 349901) (by norm_num)
theorem B4976369 : Blo 2211435 4976369 := bstep (se 2 (by rfl) ⟨1866138, by rfl⟩ : syracuseStep 4976369 = 3732277) B3732277
theorem B3317579 : Blo 2211435 3317579 := bstep (se 1 (by rfl) ⟨2488184, by rfl⟩ : syracuseStep 3317579 = 4976369) B4976369
theorem B2211719 : Blo 2211435 2211719 := bstep (se 1 (by rfl) ⟨1658789, by rfl⟩ : syracuseStep 2211719 = 3317579) B3317579
theorem B2488189 : Blo 2211435 2488189 := bbase (se 3 (by rfl) ⟨466535, by rfl⟩ : syracuseStep 2488189 = 933071) (by norm_num)
theorem B3317585 : Blo 2211435 3317585 := bstep (se 2 (by rfl) ⟨1244094, by rfl⟩ : syracuseStep 3317585 = 2488189) B2488189
theorem B2211723 : Blo 2211435 2211723 := bstep (se 1 (by rfl) ⟨1658792, by rfl⟩ : syracuseStep 2211723 = 3317585) B3317585
theorem B7464581 : Blo 2211435 7464581 := bbase (se 4 (by rfl) ⟨699804, by rfl⟩ : syracuseStep 7464581 = 1399609) (by norm_num)
theorem B4976387 : Blo 2211435 4976387 := bstep (se 1 (by rfl) ⟨3732290, by rfl⟩ : syracuseStep 4976387 = 7464581) B7464581
theorem B3317591 : Blo 2211435 3317591 := bstep (se 1 (by rfl) ⟨2488193, by rfl⟩ : syracuseStep 3317591 = 4976387) B4976387
theorem B2211727 : Blo 2211435 2211727 := bstep (se 1 (by rfl) ⟨1658795, by rfl⟩ : syracuseStep 2211727 = 3317591) B3317591
theorem B3317597 : Blo 2211435 3317597 := bbase (se 3 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 3317597 = 1244099) (by norm_num)
theorem B2211731 : Blo 2211435 2211731 := bstep (se 1 (by rfl) ⟨1658798, by rfl⟩ : syracuseStep 2211731 = 3317597) B3317597
theorem B4976405 : Blo 2211435 4976405 := bbase (se 6 (by rfl) ⟨116634, by rfl⟩ : syracuseStep 4976405 = 233269) (by norm_num)
theorem B3317603 : Blo 2211435 3317603 := bstep (se 1 (by rfl) ⟨2488202, by rfl⟩ : syracuseStep 3317603 = 4976405) B4976405
theorem B2211735 : Blo 2211435 2211735 := bstep (se 1 (by rfl) ⟨1658801, by rfl⟩ : syracuseStep 2211735 = 3317603) B3317603
theorem B8397701 : Blo 2211435 8397701 := bbase (se 4 (by rfl) ⟨787284, by rfl⟩ : syracuseStep 8397701 = 1574569) (by norm_num)
theorem B5598467 : Blo 2211435 5598467 := bstep (se 1 (by rfl) ⟨4198850, by rfl⟩ : syracuseStep 5598467 = 8397701) B8397701
theorem B3732311 : Blo 2211435 3732311 := bstep (se 1 (by rfl) ⟨2799233, by rfl⟩ : syracuseStep 3732311 = 5598467) B5598467
theorem B2488207 : Blo 2211435 2488207 := bstep (se 1 (by rfl) ⟨1866155, by rfl⟩ : syracuseStep 2488207 = 3732311) B3732311
theorem B3317609 : Blo 2211435 3317609 := bstep (se 2 (by rfl) ⟨1244103, by rfl⟩ : syracuseStep 3317609 = 2488207) B2488207
theorem B2211739 : Blo 2211435 2211739 := bstep (se 1 (by rfl) ⟨1658804, by rfl⟩ : syracuseStep 2211739 = 3317609) B3317609
theorem B7085573 : Blo 2211435 7085573 := bbase (se 4 (by rfl) ⟨664272, by rfl⟩ : syracuseStep 7085573 = 1328545) (by norm_num)
theorem B4723715 : Blo 2211435 4723715 := bstep (se 1 (by rfl) ⟨3542786, by rfl⟩ : syracuseStep 4723715 = 7085573) B7085573
theorem B12596573 : Blo 2211435 12596573 := bstep (se 3 (by rfl) ⟨2361857, by rfl⟩ : syracuseStep 12596573 = 4723715) B4723715
theorem B8397715 : Blo 2211435 8397715 := bstep (se 1 (by rfl) ⟨6298286, by rfl⟩ : syracuseStep 8397715 = 12596573) B12596573
theorem B11196953 : Blo 2211435 11196953 := bstep (se 2 (by rfl) ⟨4198857, by rfl⟩ : syracuseStep 11196953 = 8397715) B8397715
theorem B7464635 : Blo 2211435 7464635 := bstep (se 1 (by rfl) ⟨5598476, by rfl⟩ : syracuseStep 7464635 = 11196953) B11196953
theorem B4976423 : Blo 2211435 4976423 := bstep (se 1 (by rfl) ⟨3732317, by rfl⟩ : syracuseStep 4976423 = 7464635) B7464635
theorem B3317615 : Blo 2211435 3317615 := bstep (se 1 (by rfl) ⟨2488211, by rfl⟩ : syracuseStep 3317615 = 4976423) B4976423
theorem B2211743 : Blo 2211435 2211743 := bstep (se 1 (by rfl) ⟨1658807, by rfl⟩ : syracuseStep 2211743 = 3317615) B3317615
theorem B3317621 : Blo 2211435 3317621 := bbase (se 5 (by rfl) ⟨155513, by rfl⟩ : syracuseStep 3317621 = 311027) (by norm_num)
theorem B2211747 : Blo 2211435 2211747 := bstep (se 1 (by rfl) ⟨1658810, by rfl⟩ : syracuseStep 2211747 = 3317621) B3317621
theorem B4723733 : Blo 2211435 4723733 := bbase (se 6 (by rfl) ⟨110712, by rfl⟩ : syracuseStep 4723733 = 221425) (by norm_num)
theorem B3149155 : Blo 2211435 3149155 := bstep (se 1 (by rfl) ⟨2361866, by rfl⟩ : syracuseStep 3149155 = 4723733) B4723733
theorem B4198873 : Blo 2211435 4198873 := bstep (se 2 (by rfl) ⟨1574577, by rfl⟩ : syracuseStep 4198873 = 3149155) B3149155
theorem B5598497 : Blo 2211435 5598497 := bstep (se 2 (by rfl) ⟨2099436, by rfl⟩ : syracuseStep 5598497 = 4198873) B4198873
theorem B3732331 : Blo 2211435 3732331 := bstep (se 1 (by rfl) ⟨2799248, by rfl⟩ : syracuseStep 3732331 = 5598497) B5598497
theorem B4976441 : Blo 2211435 4976441 := bstep (se 2 (by rfl) ⟨1866165, by rfl⟩ : syracuseStep 4976441 = 3732331) B3732331
theorem B3317627 : Blo 2211435 3317627 := bstep (se 1 (by rfl) ⟨2488220, by rfl⟩ : syracuseStep 3317627 = 4976441) B4976441
theorem B2211751 : Blo 2211435 2211751 := bstep (se 1 (by rfl) ⟨1658813, by rfl⟩ : syracuseStep 2211751 = 3317627) B3317627
theorem B2488225 : Blo 2211435 2488225 := bbase (se 2 (by rfl) ⟨933084, by rfl⟩ : syracuseStep 2488225 = 1866169) (by norm_num)
theorem B3317633 : Blo 2211435 3317633 := bstep (se 2 (by rfl) ⟨1244112, by rfl⟩ : syracuseStep 3317633 = 2488225) B2488225
theorem B2211755 : Blo 2211435 2211755 := bstep (se 1 (by rfl) ⟨1658816, by rfl⟩ : syracuseStep 2211755 = 3317633) B3317633
theorem B5598517 : Blo 2211435 5598517 := bbase (se 5 (by rfl) ⟨262430, by rfl⟩ : syracuseStep 5598517 = 524861) (by norm_num)
theorem B7464689 : Blo 2211435 7464689 := bstep (se 2 (by rfl) ⟨2799258, by rfl⟩ : syracuseStep 7464689 = 5598517) B5598517
theorem B4976459 : Blo 2211435 4976459 := bstep (se 1 (by rfl) ⟨3732344, by rfl⟩ : syracuseStep 4976459 = 7464689) B7464689
theorem B3317639 : Blo 2211435 3317639 := bstep (se 1 (by rfl) ⟨2488229, by rfl⟩ : syracuseStep 3317639 = 4976459) B4976459
theorem B2211759 : Blo 2211435 2211759 := bstep (se 1 (by rfl) ⟨1658819, by rfl⟩ : syracuseStep 2211759 = 3317639) B3317639
theorem B3317645 : Blo 2211435 3317645 := bbase (se 3 (by rfl) ⟨622058, by rfl⟩ : syracuseStep 3317645 = 1244117) (by norm_num)
theorem B2211763 : Blo 2211435 2211763 := bstep (se 1 (by rfl) ⟨1658822, by rfl⟩ : syracuseStep 2211763 = 3317645) B3317645
theorem B4976477 : Blo 2211435 4976477 := bbase (se 3 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 4976477 = 1866179) (by norm_num)
theorem B3317651 : Blo 2211435 3317651 := bstep (se 1 (by rfl) ⟨2488238, by rfl⟩ : syracuseStep 3317651 = 4976477) B4976477
theorem B2211767 : Blo 2211435 2211767 := bstep (se 1 (by rfl) ⟨1658825, by rfl⟩ : syracuseStep 2211767 = 3317651) B3317651
theorem B3732365 : Blo 2211435 3732365 := bbase (se 3 (by rfl) ⟨699818, by rfl⟩ : syracuseStep 3732365 = 1399637) (by norm_num)
theorem B2488243 : Blo 2211435 2488243 := bstep (se 1 (by rfl) ⟨1866182, by rfl⟩ : syracuseStep 2488243 = 3732365) B3732365
theorem B3317657 : Blo 2211435 3317657 := bstep (se 2 (by rfl) ⟨1244121, by rfl⟩ : syracuseStep 3317657 = 2488243) B2488243
theorem B2211771 : Blo 2211435 2211771 := bstep (se 1 (by rfl) ⟨1658828, by rfl⟩ : syracuseStep 2211771 = 3317657) B3317657
theorem B2876185 : Blo 2211435 2876185 := bbase (se 2 (by rfl) ⟨1078569, by rfl⟩ : syracuseStep 2876185 = 2157139) (by norm_num)
theorem B3834913 : Blo 2211435 3834913 := bstep (se 2 (by rfl) ⟨1438092, by rfl⟩ : syracuseStep 3834913 = 2876185) B2876185
theorem B5113217 : Blo 2211435 5113217 := bstep (se 2 (by rfl) ⟨1917456, by rfl⟩ : syracuseStep 5113217 = 3834913) B3834913
theorem B13635245 : Blo 2211435 13635245 := bstep (se 3 (by rfl) ⟨2556608, by rfl⟩ : syracuseStep 13635245 = 5113217) B5113217
theorem B9090163 : Blo 2211435 9090163 := bstep (se 1 (by rfl) ⟨6817622, by rfl⟩ : syracuseStep 9090163 = 13635245) B13635245
theorem B48480869 : Blo 2211435 48480869 := bstep (se 4 (by rfl) ⟨4545081, by rfl⟩ : syracuseStep 48480869 = 9090163) B9090163
theorem B32320579 : Blo 2211435 32320579 := bstep (se 1 (by rfl) ⟨24240434, by rfl⟩ : syracuseStep 32320579 = 48480869) B48480869
theorem B43094105 : Blo 2211435 43094105 := bstep (se 2 (by rfl) ⟨16160289, by rfl⟩ : syracuseStep 43094105 = 32320579) B32320579
theorem B28729403 : Blo 2211435 28729403 := bstep (se 1 (by rfl) ⟨21547052, by rfl⟩ : syracuseStep 28729403 = 43094105) B43094105
theorem B19152935 : Blo 2211435 19152935 := bstep (se 1 (by rfl) ⟨14364701, by rfl⟩ : syracuseStep 19152935 = 28729403) B28729403
theorem B12768623 : Blo 2211435 12768623 := bstep (se 1 (by rfl) ⟨9576467, by rfl⟩ : syracuseStep 12768623 = 19152935) B19152935
theorem B8512415 : Blo 2211435 8512415 := bstep (se 1 (by rfl) ⟨6384311, by rfl⟩ : syracuseStep 8512415 = 12768623) B12768623
theorem B5674943 : Blo 2211435 5674943 := bstep (se 1 (by rfl) ⟨4256207, by rfl⟩ : syracuseStep 5674943 = 8512415) B8512415
theorem B3783295 : Blo 2211435 3783295 := bstep (se 1 (by rfl) ⟨2837471, by rfl⟩ : syracuseStep 3783295 = 5674943) B5674943
theorem B5044393 : Blo 2211435 5044393 := bstep (se 2 (by rfl) ⟨1891647, by rfl⟩ : syracuseStep 5044393 = 3783295) B3783295
theorem B6725857 : Blo 2211435 6725857 := bstep (se 2 (by rfl) ⟨2522196, by rfl⟩ : syracuseStep 6725857 = 5044393) B5044393
theorem B8967809 : Blo 2211435 8967809 := bstep (se 2 (by rfl) ⟨3362928, by rfl⟩ : syracuseStep 8967809 = 6725857) B6725857
theorem B5978539 : Blo 2211435 5978539 := bstep (se 1 (by rfl) ⟨4483904, by rfl⟩ : syracuseStep 5978539 = 8967809) B8967809
theorem B7971385 : Blo 2211435 7971385 := bstep (se 2 (by rfl) ⟨2989269, by rfl⟩ : syracuseStep 7971385 = 5978539) B5978539
theorem B10628513 : Blo 2211435 10628513 := bstep (se 2 (by rfl) ⟨3985692, by rfl⟩ : syracuseStep 10628513 = 7971385) B7971385
theorem B7085675 : Blo 2211435 7085675 := bstep (se 1 (by rfl) ⟨5314256, by rfl⟩ : syracuseStep 7085675 = 10628513) B10628513
theorem B18895133 : Blo 2211435 18895133 := bstep (se 3 (by rfl) ⟨3542837, by rfl⟩ : syracuseStep 18895133 = 7085675) B7085675
theorem B12596755 : Blo 2211435 12596755 := bstep (se 1 (by rfl) ⟨9447566, by rfl⟩ : syracuseStep 12596755 = 18895133) B18895133
theorem B16795673 : Blo 2211435 16795673 := bstep (se 2 (by rfl) ⟨6298377, by rfl⟩ : syracuseStep 16795673 = 12596755) B12596755
theorem B11197115 : Blo 2211435 11197115 := bstep (se 1 (by rfl) ⟨8397836, by rfl⟩ : syracuseStep 11197115 = 16795673) B16795673
theorem B7464743 : Blo 2211435 7464743 := bstep (se 1 (by rfl) ⟨5598557, by rfl⟩ : syracuseStep 7464743 = 11197115) B11197115
theorem B4976495 : Blo 2211435 4976495 := bstep (se 1 (by rfl) ⟨3732371, by rfl⟩ : syracuseStep 4976495 = 7464743) B7464743
theorem B3317663 : Blo 2211435 3317663 := bstep (se 1 (by rfl) ⟨2488247, by rfl⟩ : syracuseStep 3317663 = 4976495) B4976495
theorem B2211775 : Blo 2211435 2211775 := bstep (se 1 (by rfl) ⟨1658831, by rfl⟩ : syracuseStep 2211775 = 3317663) B3317663
theorem B3317669 : Blo 2211435 3317669 := bbase (se 4 (by rfl) ⟨311031, by rfl⟩ : syracuseStep 3317669 = 622063) (by norm_num)
theorem B2211779 : Blo 2211435 2211779 := bstep (se 1 (by rfl) ⟨1658834, by rfl⟩ : syracuseStep 2211779 = 3317669) B3317669
theorem B2799289 : Blo 2211435 2799289 := bbase (se 2 (by rfl) ⟨1049733, by rfl⟩ : syracuseStep 2799289 = 2099467) (by norm_num)
theorem B3732385 : Blo 2211435 3732385 := bstep (se 2 (by rfl) ⟨1399644, by rfl⟩ : syracuseStep 3732385 = 2799289) B2799289
theorem B4976513 : Blo 2211435 4976513 := bstep (se 2 (by rfl) ⟨1866192, by rfl⟩ : syracuseStep 4976513 = 3732385) B3732385
theorem B3317675 : Blo 2211435 3317675 := bstep (se 1 (by rfl) ⟨2488256, by rfl⟩ : syracuseStep 3317675 = 4976513) B4976513
theorem B2211783 : Blo 2211435 2211783 := bstep (se 1 (by rfl) ⟨1658837, by rfl⟩ : syracuseStep 2211783 = 3317675) B3317675
theorem B2488261 : Blo 2211435 2488261 := bbase (se 4 (by rfl) ⟨233274, by rfl⟩ : syracuseStep 2488261 = 466549) (by norm_num)
theorem B3317681 : Blo 2211435 3317681 := bstep (se 2 (by rfl) ⟨1244130, by rfl⟩ : syracuseStep 3317681 = 2488261) B2488261
theorem B2211787 : Blo 2211435 2211787 := bstep (se 1 (by rfl) ⟨1658840, by rfl⟩ : syracuseStep 2211787 = 3317681) B3317681
theorem B4198949 : Blo 2211435 4198949 := bbase (se 4 (by rfl) ⟨393651, by rfl⟩ : syracuseStep 4198949 = 787303) (by norm_num)
theorem B2799299 : Blo 2211435 2799299 := bstep (se 1 (by rfl) ⟨2099474, by rfl⟩ : syracuseStep 2799299 = 4198949) B4198949
theorem B7464797 : Blo 2211435 7464797 := bstep (se 3 (by rfl) ⟨1399649, by rfl⟩ : syracuseStep 7464797 = 2799299) B2799299
theorem B4976531 : Blo 2211435 4976531 := bstep (se 1 (by rfl) ⟨3732398, by rfl⟩ : syracuseStep 4976531 = 7464797) B7464797
theorem B3317687 : Blo 2211435 3317687 := bstep (se 1 (by rfl) ⟨2488265, by rfl⟩ : syracuseStep 3317687 = 4976531) B4976531
theorem B2211791 : Blo 2211435 2211791 := bstep (se 1 (by rfl) ⟨1658843, by rfl⟩ : syracuseStep 2211791 = 3317687) B3317687
theorem B3317693 : Blo 2211435 3317693 := bbase (se 3 (by rfl) ⟨622067, by rfl⟩ : syracuseStep 3317693 = 1244135) (by norm_num)
theorem B2211795 : Blo 2211435 2211795 := bstep (se 1 (by rfl) ⟨1658846, by rfl⟩ : syracuseStep 2211795 = 3317693) B3317693
theorem B4976549 : Blo 2211435 4976549 := bbase (se 4 (by rfl) ⟨466551, by rfl⟩ : syracuseStep 4976549 = 933103) (by norm_num)
theorem B3317699 : Blo 2211435 3317699 := bstep (se 1 (by rfl) ⟨2488274, by rfl⟩ : syracuseStep 3317699 = 4976549) B4976549
theorem B2211799 : Blo 2211435 2211799 := bstep (se 1 (by rfl) ⟨1658849, by rfl⟩ : syracuseStep 2211799 = 3317699) B3317699
theorem B5598629 : Blo 2211435 5598629 := bbase (se 4 (by rfl) ⟨524871, by rfl⟩ : syracuseStep 5598629 = 1049743) (by norm_num)
theorem B3732419 : Blo 2211435 3732419 := bstep (se 1 (by rfl) ⟨2799314, by rfl⟩ : syracuseStep 3732419 = 5598629) B5598629
theorem B2488279 : Blo 2211435 2488279 := bstep (se 1 (by rfl) ⟨1866209, by rfl⟩ : syracuseStep 2488279 = 3732419) B3732419
theorem B3317705 : Blo 2211435 3317705 := bstep (se 2 (by rfl) ⟨1244139, by rfl⟩ : syracuseStep 3317705 = 2488279) B2488279
theorem B2211803 : Blo 2211435 2211803 := bstep (se 1 (by rfl) ⟨1658852, by rfl⟩ : syracuseStep 2211803 = 3317705) B3317705
theorem B6298469 : Blo 2211435 6298469 := bbase (se 4 (by rfl) ⟨590481, by rfl⟩ : syracuseStep 6298469 = 1180963) (by norm_num)
theorem B4198979 : Blo 2211435 4198979 := bstep (se 1 (by rfl) ⟨3149234, by rfl⟩ : syracuseStep 4198979 = 6298469) B6298469
theorem B11197277 : Blo 2211435 11197277 := bstep (se 3 (by rfl) ⟨2099489, by rfl⟩ : syracuseStep 11197277 = 4198979) B4198979
theorem B7464851 : Blo 2211435 7464851 := bstep (se 1 (by rfl) ⟨5598638, by rfl⟩ : syracuseStep 7464851 = 11197277) B11197277
theorem B4976567 : Blo 2211435 4976567 := bstep (se 1 (by rfl) ⟨3732425, by rfl⟩ : syracuseStep 4976567 = 7464851) B7464851
theorem B3317711 : Blo 2211435 3317711 := bstep (se 1 (by rfl) ⟨2488283, by rfl⟩ : syracuseStep 3317711 = 4976567) B4976567
theorem B2211807 : Blo 2211435 2211807 := bstep (se 1 (by rfl) ⟨1658855, by rfl⟩ : syracuseStep 2211807 = 3317711) B3317711
theorem B3317717 : Blo 2211435 3317717 := bbase (se 7 (by rfl) ⟨38879, by rfl⟩ : syracuseStep 3317717 = 77759) (by norm_num)
theorem B2211811 : Blo 2211435 2211811 := bstep (se 1 (by rfl) ⟨1658858, by rfl⟩ : syracuseStep 2211811 = 3317717) B3317717
theorem B8397989 : Blo 2211435 8397989 := bbase (se 4 (by rfl) ⟨787311, by rfl⟩ : syracuseStep 8397989 = 1574623) (by norm_num)
theorem B5598659 : Blo 2211435 5598659 := bstep (se 1 (by rfl) ⟨4198994, by rfl⟩ : syracuseStep 5598659 = 8397989) B8397989
theorem B3732439 : Blo 2211435 3732439 := bstep (se 1 (by rfl) ⟨2799329, by rfl⟩ : syracuseStep 3732439 = 5598659) B5598659
theorem B4976585 : Blo 2211435 4976585 := bstep (se 2 (by rfl) ⟨1866219, by rfl⟩ : syracuseStep 4976585 = 3732439) B3732439
theorem B3317723 : Blo 2211435 3317723 := bstep (se 1 (by rfl) ⟨2488292, by rfl⟩ : syracuseStep 3317723 = 4976585) B4976585
theorem B2211815 : Blo 2211435 2211815 := bstep (se 1 (by rfl) ⟨1658861, by rfl⟩ : syracuseStep 2211815 = 3317723) B3317723
theorem B2488297 : Blo 2211435 2488297 := bbase (se 2 (by rfl) ⟨933111, by rfl⟩ : syracuseStep 2488297 = 1866223) (by norm_num)
theorem B3317729 : Blo 2211435 3317729 := bstep (se 2 (by rfl) ⟨1244148, by rfl⟩ : syracuseStep 3317729 = 2488297) B2488297
theorem B2211819 : Blo 2211435 2211819 := bstep (se 1 (by rfl) ⟨1658864, by rfl⟩ : syracuseStep 2211819 = 3317729) B3317729
theorem B5314373 : Blo 2211435 5314373 := bbase (se 4 (by rfl) ⟨498222, by rfl⟩ : syracuseStep 5314373 = 996445) (by norm_num)
theorem B3542915 : Blo 2211435 3542915 := bstep (se 1 (by rfl) ⟨2657186, by rfl⟩ : syracuseStep 3542915 = 5314373) B5314373
theorem B2361943 : Blo 2211435 2361943 := bstep (se 1 (by rfl) ⟨1771457, by rfl⟩ : syracuseStep 2361943 = 3542915) B3542915
theorem B12597029 : Blo 2211435 12597029 := bstep (se 4 (by rfl) ⟨1180971, by rfl⟩ : syracuseStep 12597029 = 2361943) B2361943
theorem B8398019 : Blo 2211435 8398019 := bstep (se 1 (by rfl) ⟨6298514, by rfl⟩ : syracuseStep 8398019 = 12597029) B12597029
theorem B5598679 : Blo 2211435 5598679 := bstep (se 1 (by rfl) ⟨4199009, by rfl⟩ : syracuseStep 5598679 = 8398019) B8398019
theorem B7464905 : Blo 2211435 7464905 := bstep (se 2 (by rfl) ⟨2799339, by rfl⟩ : syracuseStep 7464905 = 5598679) B5598679
theorem B4976603 : Blo 2211435 4976603 := bstep (se 1 (by rfl) ⟨3732452, by rfl⟩ : syracuseStep 4976603 = 7464905) B7464905
theorem B3317735 : Blo 2211435 3317735 := bstep (se 1 (by rfl) ⟨2488301, by rfl⟩ : syracuseStep 3317735 = 4976603) B4976603
theorem B2211823 : Blo 2211435 2211823 := bstep (se 1 (by rfl) ⟨1658867, by rfl⟩ : syracuseStep 2211823 = 3317735) B3317735
theorem B3317741 : Blo 2211435 3317741 := bbase (se 3 (by rfl) ⟨622076, by rfl⟩ : syracuseStep 3317741 = 1244153) (by norm_num)
theorem B2211827 : Blo 2211435 2211827 := bstep (se 1 (by rfl) ⟨1658870, by rfl⟩ : syracuseStep 2211827 = 3317741) B3317741
theorem B4976621 : Blo 2211435 4976621 := bbase (se 3 (by rfl) ⟨933116, by rfl⟩ : syracuseStep 4976621 = 1866233) (by norm_num)
theorem B3317747 : Blo 2211435 3317747 := bstep (se 1 (by rfl) ⟨2488310, by rfl⟩ : syracuseStep 3317747 = 4976621) B4976621
theorem B2211831 : Blo 2211435 2211831 := bstep (se 1 (by rfl) ⟨1658873, by rfl⟩ : syracuseStep 2211831 = 3317747) B3317747
theorem B7971605 : Blo 2211435 7971605 := bbase (se 6 (by rfl) ⟨186834, by rfl⟩ : syracuseStep 7971605 = 373669) (by norm_num)
theorem B5314403 : Blo 2211435 5314403 := bstep (se 1 (by rfl) ⟨3985802, by rfl⟩ : syracuseStep 5314403 = 7971605) B7971605
theorem B3542935 : Blo 2211435 3542935 := bstep (se 1 (by rfl) ⟨2657201, by rfl⟩ : syracuseStep 3542935 = 5314403) B5314403
theorem B4723913 : Blo 2211435 4723913 := bstep (se 2 (by rfl) ⟨1771467, by rfl⟩ : syracuseStep 4723913 = 3542935) B3542935
theorem B3149275 : Blo 2211435 3149275 := bstep (se 1 (by rfl) ⟨2361956, by rfl⟩ : syracuseStep 3149275 = 4723913) B4723913
theorem B4199033 : Blo 2211435 4199033 := bstep (se 2 (by rfl) ⟨1574637, by rfl⟩ : syracuseStep 4199033 = 3149275) B3149275
theorem B2799355 : Blo 2211435 2799355 := bstep (se 1 (by rfl) ⟨2099516, by rfl⟩ : syracuseStep 2799355 = 4199033) B4199033
theorem B3732473 : Blo 2211435 3732473 := bstep (se 2 (by rfl) ⟨1399677, by rfl⟩ : syracuseStep 3732473 = 2799355) B2799355
theorem B2488315 : Blo 2211435 2488315 := bstep (se 1 (by rfl) ⟨1866236, by rfl⟩ : syracuseStep 2488315 = 3732473) B3732473
theorem B3317753 : Blo 2211435 3317753 := bstep (se 2 (by rfl) ⟨1244157, by rfl⟩ : syracuseStep 3317753 = 2488315) B2488315
theorem B2211835 : Blo 2211435 2211835 := bstep (se 1 (by rfl) ⟨1658876, by rfl⟩ : syracuseStep 2211835 = 3317753) B3317753
theorem B15340085 : Blo 2211435 15340085 := bbase (se 5 (by rfl) ⟨719066, by rfl⟩ : syracuseStep 15340085 = 1438133) (by norm_num)
theorem B163627573 : Blo 2211435 163627573 := bstep (se 5 (by rfl) ⟨7670042, by rfl⟩ : syracuseStep 163627573 = 15340085) B15340085
theorem B218170097 : Blo 2211435 218170097 := bstep (se 2 (by rfl) ⟨81813786, by rfl⟩ : syracuseStep 218170097 = 163627573) B163627573
theorem B145446731 : Blo 2211435 145446731 := bstep (se 1 (by rfl) ⟨109085048, by rfl⟩ : syracuseStep 145446731 = 218170097) B218170097
theorem B96964487 : Blo 2211435 96964487 := bstep (se 1 (by rfl) ⟨72723365, by rfl⟩ : syracuseStep 96964487 = 145446731) B145446731
theorem B64642991 : Blo 2211435 64642991 := bstep (se 1 (by rfl) ⟨48482243, by rfl⟩ : syracuseStep 64642991 = 96964487) B96964487
theorem B689525237 : Blo 2211435 689525237 := bstep (se 5 (by rfl) ⟨32321495, by rfl⟩ : syracuseStep 689525237 = 64642991) B64642991
theorem B1838733965 : Blo 2211435 1838733965 := bstep (se 3 (by rfl) ⟨344762618, by rfl⟩ : syracuseStep 1838733965 = 689525237) B689525237
theorem B1225822643 : Blo 2211435 1225822643 := bstep (se 1 (by rfl) ⟨919366982, by rfl⟩ : syracuseStep 1225822643 = 1838733965) B1838733965
theorem B817215095 : Blo 2211435 817215095 := bstep (se 1 (by rfl) ⟨612911321, by rfl⟩ : syracuseStep 817215095 = 1225822643) B1225822643
theorem B544810063 : Blo 2211435 544810063 := bstep (se 1 (by rfl) ⟨408607547, by rfl⟩ : syracuseStep 544810063 = 817215095) B817215095
theorem B726413417 : Blo 2211435 726413417 := bstep (se 2 (by rfl) ⟨272405031, by rfl⟩ : syracuseStep 726413417 = 544810063) B544810063
theorem B484275611 : Blo 2211435 484275611 := bstep (se 1 (by rfl) ⟨363206708, by rfl⟩ : syracuseStep 484275611 = 726413417) B726413417
theorem B322850407 : Blo 2211435 322850407 := bstep (se 1 (by rfl) ⟨242137805, by rfl⟩ : syracuseStep 322850407 = 484275611) B484275611
theorem B430467209 : Blo 2211435 430467209 := bstep (se 2 (by rfl) ⟨161425203, by rfl⟩ : syracuseStep 430467209 = 322850407) B322850407
theorem B286978139 : Blo 2211435 286978139 := bstep (se 1 (by rfl) ⟨215233604, by rfl⟩ : syracuseStep 286978139 = 430467209) B430467209
theorem B191318759 : Blo 2211435 191318759 := bstep (se 1 (by rfl) ⟨143489069, by rfl⟩ : syracuseStep 191318759 = 286978139) B286978139
theorem B127545839 : Blo 2211435 127545839 := bstep (se 1 (by rfl) ⟨95659379, by rfl⟩ : syracuseStep 127545839 = 191318759) B191318759
theorem B85030559 : Blo 2211435 85030559 := bstep (se 1 (by rfl) ⟨63772919, by rfl⟩ : syracuseStep 85030559 = 127545839) B127545839
theorem B56687039 : Blo 2211435 56687039 := bstep (se 1 (by rfl) ⟨42515279, by rfl⟩ : syracuseStep 56687039 = 85030559) B85030559
theorem B37791359 : Blo 2211435 37791359 := bstep (se 1 (by rfl) ⟨28343519, by rfl⟩ : syracuseStep 37791359 = 56687039) B56687039
theorem B25194239 : Blo 2211435 25194239 := bstep (se 1 (by rfl) ⟨18895679, by rfl⟩ : syracuseStep 25194239 = 37791359) B37791359
theorem B16796159 : Blo 2211435 16796159 := bstep (se 1 (by rfl) ⟨12597119, by rfl⟩ : syracuseStep 16796159 = 25194239) B25194239
theorem B11197439 : Blo 2211435 11197439 := bstep (se 1 (by rfl) ⟨8398079, by rfl⟩ : syracuseStep 11197439 = 16796159) B16796159
theorem B7464959 : Blo 2211435 7464959 := bstep (se 1 (by rfl) ⟨5598719, by rfl⟩ : syracuseStep 7464959 = 11197439) B11197439
theorem B4976639 : Blo 2211435 4976639 := bstep (se 1 (by rfl) ⟨3732479, by rfl⟩ : syracuseStep 4976639 = 7464959) B7464959
theorem B3317759 : Blo 2211435 3317759 := bstep (se 1 (by rfl) ⟨2488319, by rfl⟩ : syracuseStep 3317759 = 4976639) B4976639
theorem B2211839 : Blo 2211435 2211839 := bstep (se 1 (by rfl) ⟨1658879, by rfl⟩ : syracuseStep 2211839 = 3317759) B3317759
theorem B3317765 : Blo 2211435 3317765 := bbase (se 4 (by rfl) ⟨311040, by rfl⟩ : syracuseStep 3317765 = 622081) (by norm_num)
theorem B2211843 : Blo 2211435 2211843 := bstep (se 1 (by rfl) ⟨1658882, by rfl⟩ : syracuseStep 2211843 = 3317765) B3317765
theorem B3732493 : Blo 2211435 3732493 := bbase (se 3 (by rfl) ⟨699842, by rfl⟩ : syracuseStep 3732493 = 1399685) (by norm_num)
theorem B4976657 : Blo 2211435 4976657 := bstep (se 2 (by rfl) ⟨1866246, by rfl⟩ : syracuseStep 4976657 = 3732493) B3732493
theorem B3317771 : Blo 2211435 3317771 := bstep (se 1 (by rfl) ⟨2488328, by rfl⟩ : syracuseStep 3317771 = 4976657) B4976657
theorem B2211847 : Blo 2211435 2211847 := bstep (se 1 (by rfl) ⟨1658885, by rfl⟩ : syracuseStep 2211847 = 3317771) B3317771
theorem B2488333 : Blo 2211435 2488333 := bbase (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) (by norm_num)
theorem B3317777 : Blo 2211435 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B2211851 : Blo 2211435 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B7465013 : Blo 2211435 7465013 := bbase (se 5 (by rfl) ⟨349922, by rfl⟩ : syracuseStep 7465013 = 699845) (by norm_num)
theorem B4976675 : Blo 2211435 4976675 := bstep (se 1 (by rfl) ⟨3732506, by rfl⟩ : syracuseStep 4976675 = 7465013) B7465013
theorem B3317783 : Blo 2211435 3317783 := bstep (se 1 (by rfl) ⟨2488337, by rfl⟩ : syracuseStep 3317783 = 4976675) B4976675
theorem B2211855 : Blo 2211435 2211855 := bstep (se 1 (by rfl) ⟨1658891, by rfl⟩ : syracuseStep 2211855 = 3317783) B3317783
theorem B3317789 : Blo 2211435 3317789 := bbase (se 3 (by rfl) ⟨622085, by rfl⟩ : syracuseStep 3317789 = 1244171) (by norm_num)
theorem B2211859 : Blo 2211435 2211859 := bstep (se 1 (by rfl) ⟨1658894, by rfl⟩ : syracuseStep 2211859 = 3317789) B3317789
theorem B4976693 : Blo 2211435 4976693 := bbase (se 5 (by rfl) ⟨233282, by rfl⟩ : syracuseStep 4976693 = 466565) (by norm_num)
theorem B3317795 : Blo 2211435 3317795 := bstep (se 1 (by rfl) ⟨2488346, by rfl⟩ : syracuseStep 3317795 = 4976693) B4976693
theorem B2211863 : Blo 2211435 2211863 := bstep (se 1 (by rfl) ⟨1658897, by rfl⟩ : syracuseStep 2211863 = 3317795) B3317795
theorem B5978789 : Blo 2211435 5978789 := bbase (se 4 (by rfl) ⟨560511, by rfl⟩ : syracuseStep 5978789 = 1121023) (by norm_num)
theorem B3985859 : Blo 2211435 3985859 := bstep (se 1 (by rfl) ⟨2989394, by rfl⟩ : syracuseStep 3985859 = 5978789) B5978789
theorem B10628957 : Blo 2211435 10628957 := bstep (se 3 (by rfl) ⟨1992929, by rfl⟩ : syracuseStep 10628957 = 3985859) B3985859
theorem B7085971 : Blo 2211435 7085971 := bstep (se 1 (by rfl) ⟨5314478, by rfl⟩ : syracuseStep 7085971 = 10628957) B10628957
theorem B9447961 : Blo 2211435 9447961 := bstep (se 2 (by rfl) ⟨3542985, by rfl⟩ : syracuseStep 9447961 = 7085971) B7085971
theorem B12597281 : Blo 2211435 12597281 := bstep (se 2 (by rfl) ⟨4723980, by rfl⟩ : syracuseStep 12597281 = 9447961) B9447961
theorem B8398187 : Blo 2211435 8398187 := bstep (se 1 (by rfl) ⟨6298640, by rfl⟩ : syracuseStep 8398187 = 12597281) B12597281
theorem B5598791 : Blo 2211435 5598791 := bstep (se 1 (by rfl) ⟨4199093, by rfl⟩ : syracuseStep 5598791 = 8398187) B8398187
theorem B3732527 : Blo 2211435 3732527 := bstep (se 1 (by rfl) ⟨2799395, by rfl⟩ : syracuseStep 3732527 = 5598791) B5598791
theorem B2488351 : Blo 2211435 2488351 := bstep (se 1 (by rfl) ⟨1866263, by rfl⟩ : syracuseStep 2488351 = 3732527) B3732527
theorem B3317801 : Blo 2211435 3317801 := bstep (se 2 (by rfl) ⟨1244175, by rfl⟩ : syracuseStep 3317801 = 2488351) B2488351
theorem B2211867 : Blo 2211435 2211867 := bstep (se 1 (by rfl) ⟨1658900, by rfl⟩ : syracuseStep 2211867 = 3317801) B3317801
theorem B7182661 : Blo 2211435 7182661 := bbase (se 4 (by rfl) ⟨673374, by rfl⟩ : syracuseStep 7182661 = 1346749) (by norm_num)
theorem B9576881 : Blo 2211435 9576881 := bstep (se 2 (by rfl) ⟨3591330, by rfl⟩ : syracuseStep 9576881 = 7182661) B7182661
theorem B6384587 : Blo 2211435 6384587 := bstep (se 1 (by rfl) ⟨4788440, by rfl⟩ : syracuseStep 6384587 = 9576881) B9576881
theorem B17025565 : Blo 2211435 17025565 := bstep (se 3 (by rfl) ⟨3192293, by rfl⟩ : syracuseStep 17025565 = 6384587) B6384587
theorem B22700753 : Blo 2211435 22700753 := bstep (se 2 (by rfl) ⟨8512782, by rfl⟩ : syracuseStep 22700753 = 17025565) B17025565
theorem B15133835 : Blo 2211435 15133835 := bstep (se 1 (by rfl) ⟨11350376, by rfl⟩ : syracuseStep 15133835 = 22700753) B22700753
theorem B40356893 : Blo 2211435 40356893 := bstep (se 3 (by rfl) ⟨7566917, by rfl⟩ : syracuseStep 40356893 = 15133835) B15133835
theorem B26904595 : Blo 2211435 26904595 := bstep (se 1 (by rfl) ⟨20178446, by rfl⟩ : syracuseStep 26904595 = 40356893) B40356893
theorem B35872793 : Blo 2211435 35872793 := bstep (se 2 (by rfl) ⟨13452297, by rfl⟩ : syracuseStep 35872793 = 26904595) B26904595
theorem B23915195 : Blo 2211435 23915195 := bstep (se 1 (by rfl) ⟨17936396, by rfl⟩ : syracuseStep 23915195 = 35872793) B35872793
theorem B15943463 : Blo 2211435 15943463 := bstep (se 1 (by rfl) ⟨11957597, by rfl⟩ : syracuseStep 15943463 = 23915195) B23915195
theorem B10628975 : Blo 2211435 10628975 := bstep (se 1 (by rfl) ⟨7971731, by rfl⟩ : syracuseStep 10628975 = 15943463) B15943463
theorem B7085983 : Blo 2211435 7085983 := bstep (se 1 (by rfl) ⟨5314487, by rfl⟩ : syracuseStep 7085983 = 10628975) B10628975
theorem B9447977 : Blo 2211435 9447977 := bstep (se 2 (by rfl) ⟨3542991, by rfl⟩ : syracuseStep 9447977 = 7085983) B7085983
theorem B6298651 : Blo 2211435 6298651 := bstep (se 1 (by rfl) ⟨4723988, by rfl⟩ : syracuseStep 6298651 = 9447977) B9447977
theorem B8398201 : Blo 2211435 8398201 := bstep (se 2 (by rfl) ⟨3149325, by rfl⟩ : syracuseStep 8398201 = 6298651) B6298651
theorem B11197601 : Blo 2211435 11197601 := bstep (se 2 (by rfl) ⟨4199100, by rfl⟩ : syracuseStep 11197601 = 8398201) B8398201
theorem B7465067 : Blo 2211435 7465067 := bstep (se 1 (by rfl) ⟨5598800, by rfl⟩ : syracuseStep 7465067 = 11197601) B11197601
theorem B4976711 : Blo 2211435 4976711 := bstep (se 1 (by rfl) ⟨3732533, by rfl⟩ : syracuseStep 4976711 = 7465067) B7465067
theorem B3317807 : Blo 2211435 3317807 := bstep (se 1 (by rfl) ⟨2488355, by rfl⟩ : syracuseStep 3317807 = 4976711) B4976711
theorem B2211871 : Blo 2211435 2211871 := bstep (se 1 (by rfl) ⟨1658903, by rfl⟩ : syracuseStep 2211871 = 3317807) B3317807
theorem B3317813 : Blo 2211435 3317813 := bbase (se 5 (by rfl) ⟨155522, by rfl⟩ : syracuseStep 3317813 = 311045) (by norm_num)
theorem B2211875 : Blo 2211435 2211875 := bstep (se 1 (by rfl) ⟨1658906, by rfl⟩ : syracuseStep 2211875 = 3317813) B3317813
theorem B5598821 : Blo 2211435 5598821 := bbase (se 4 (by rfl) ⟨524889, by rfl⟩ : syracuseStep 5598821 = 1049779) (by norm_num)
theorem B3732547 : Blo 2211435 3732547 := bstep (se 1 (by rfl) ⟨2799410, by rfl⟩ : syracuseStep 3732547 = 5598821) B5598821
theorem B4976729 : Blo 2211435 4976729 := bstep (se 2 (by rfl) ⟨1866273, by rfl⟩ : syracuseStep 4976729 = 3732547) B3732547
theorem B3317819 : Blo 2211435 3317819 := bstep (se 1 (by rfl) ⟨2488364, by rfl⟩ : syracuseStep 3317819 = 4976729) B4976729
theorem B2211879 : Blo 2211435 2211879 := bstep (se 1 (by rfl) ⟨1658909, by rfl⟩ : syracuseStep 2211879 = 3317819) B3317819
theorem B2488369 : Blo 2211435 2488369 := bbase (se 2 (by rfl) ⟨933138, by rfl⟩ : syracuseStep 2488369 = 1866277) (by norm_num)
theorem B3317825 : Blo 2211435 3317825 := bstep (se 2 (by rfl) ⟨1244184, by rfl⟩ : syracuseStep 3317825 = 2488369) B2488369
theorem B2211883 : Blo 2211435 2211883 := bstep (se 1 (by rfl) ⟨1658912, by rfl⟩ : syracuseStep 2211883 = 3317825) B3317825
theorem B5113477 : Blo 2211435 5113477 := bbase (se 4 (by rfl) ⟨479388, by rfl⟩ : syracuseStep 5113477 = 958777) (by norm_num)
theorem B6817969 : Blo 2211435 6817969 := bstep (se 2 (by rfl) ⟨2556738, by rfl⟩ : syracuseStep 6817969 = 5113477) B5113477
theorem B9090625 : Blo 2211435 9090625 := bstep (se 2 (by rfl) ⟨3408984, by rfl⟩ : syracuseStep 9090625 = 6817969) B6817969
theorem B12120833 : Blo 2211435 12120833 := bstep (se 2 (by rfl) ⟨4545312, by rfl⟩ : syracuseStep 12120833 = 9090625) B9090625
theorem B8080555 : Blo 2211435 8080555 := bstep (se 1 (by rfl) ⟨6060416, by rfl⟩ : syracuseStep 8080555 = 12120833) B12120833
theorem B10774073 : Blo 2211435 10774073 := bstep (se 2 (by rfl) ⟨4040277, by rfl⟩ : syracuseStep 10774073 = 8080555) B8080555
theorem B28730861 : Blo 2211435 28730861 := bstep (se 3 (by rfl) ⟨5387036, by rfl⟩ : syracuseStep 28730861 = 10774073) B10774073
theorem B19153907 : Blo 2211435 19153907 := bstep (se 1 (by rfl) ⟨14365430, by rfl⟩ : syracuseStep 19153907 = 28730861) B28730861
theorem B12769271 : Blo 2211435 12769271 := bstep (se 1 (by rfl) ⟨9576953, by rfl⟩ : syracuseStep 12769271 = 19153907) B19153907
theorem B8512847 : Blo 2211435 8512847 := bstep (se 1 (by rfl) ⟨6384635, by rfl⟩ : syracuseStep 8512847 = 12769271) B12769271
theorem B5675231 : Blo 2211435 5675231 := bstep (se 1 (by rfl) ⟨4256423, by rfl⟩ : syracuseStep 5675231 = 8512847) B8512847
theorem B15133949 : Blo 2211435 15133949 := bstep (se 3 (by rfl) ⟨2837615, by rfl⟩ : syracuseStep 15133949 = 5675231) B5675231
theorem B10089299 : Blo 2211435 10089299 := bstep (se 1 (by rfl) ⟨7566974, by rfl⟩ : syracuseStep 10089299 = 15133949) B15133949
theorem B6726199 : Blo 2211435 6726199 := bstep (se 1 (by rfl) ⟨5044649, by rfl⟩ : syracuseStep 6726199 = 10089299) B10089299
theorem B8968265 : Blo 2211435 8968265 := bstep (se 2 (by rfl) ⟨3363099, by rfl⟩ : syracuseStep 8968265 = 6726199) B6726199
theorem B5978843 : Blo 2211435 5978843 := bstep (se 1 (by rfl) ⟨4484132, by rfl⟩ : syracuseStep 5978843 = 8968265) B8968265
theorem B3985895 : Blo 2211435 3985895 := bstep (se 1 (by rfl) ⟨2989421, by rfl⟩ : syracuseStep 3985895 = 5978843) B5978843
theorem B10629053 : Blo 2211435 10629053 := bstep (se 3 (by rfl) ⟨1992947, by rfl⟩ : syracuseStep 10629053 = 3985895) B3985895
theorem B7086035 : Blo 2211435 7086035 := bstep (se 1 (by rfl) ⟨5314526, by rfl⟩ : syracuseStep 7086035 = 10629053) B10629053
theorem B4724023 : Blo 2211435 4724023 := bstep (se 1 (by rfl) ⟨3543017, by rfl⟩ : syracuseStep 4724023 = 7086035) B7086035
theorem B6298697 : Blo 2211435 6298697 := bstep (se 2 (by rfl) ⟨2362011, by rfl⟩ : syracuseStep 6298697 = 4724023) B4724023
theorem B4199131 : Blo 2211435 4199131 := bstep (se 1 (by rfl) ⟨3149348, by rfl⟩ : syracuseStep 4199131 = 6298697) B6298697
theorem B5598841 : Blo 2211435 5598841 := bstep (se 2 (by rfl) ⟨2099565, by rfl⟩ : syracuseStep 5598841 = 4199131) B4199131
theorem B7465121 : Blo 2211435 7465121 := bstep (se 2 (by rfl) ⟨2799420, by rfl⟩ : syracuseStep 7465121 = 5598841) B5598841
theorem B4976747 : Blo 2211435 4976747 := bstep (se 1 (by rfl) ⟨3732560, by rfl⟩ : syracuseStep 4976747 = 7465121) B7465121
theorem B3317831 : Blo 2211435 3317831 := bstep (se 1 (by rfl) ⟨2488373, by rfl⟩ : syracuseStep 3317831 = 4976747) B4976747
theorem B2211887 : Blo 2211435 2211887 := bstep (se 1 (by rfl) ⟨1658915, by rfl⟩ : syracuseStep 2211887 = 3317831) B3317831
theorem B3317837 : Blo 2211435 3317837 := bbase (se 3 (by rfl) ⟨622094, by rfl⟩ : syracuseStep 3317837 = 1244189) (by norm_num)
theorem B2211891 : Blo 2211435 2211891 := bstep (se 1 (by rfl) ⟨1658918, by rfl⟩ : syracuseStep 2211891 = 3317837) B3317837
theorem B4976765 : Blo 2211435 4976765 := bbase (se 3 (by rfl) ⟨933143, by rfl⟩ : syracuseStep 4976765 = 1866287) (by norm_num)
theorem B3317843 : Blo 2211435 3317843 := bstep (se 1 (by rfl) ⟨2488382, by rfl⟩ : syracuseStep 3317843 = 4976765) B4976765
theorem B2211895 : Blo 2211435 2211895 := bstep (se 1 (by rfl) ⟨1658921, by rfl⟩ : syracuseStep 2211895 = 3317843) B3317843
theorem B3732581 : Blo 2211435 3732581 := bbase (se 4 (by rfl) ⟨349929, by rfl⟩ : syracuseStep 3732581 = 699859) (by norm_num)
theorem B2488387 : Blo 2211435 2488387 := bstep (se 1 (by rfl) ⟨1866290, by rfl⟩ : syracuseStep 2488387 = 3732581) B3732581
theorem B3317849 : Blo 2211435 3317849 := bstep (se 2 (by rfl) ⟨1244193, by rfl⟩ : syracuseStep 3317849 = 2488387) B2488387
theorem B2211899 : Blo 2211435 2211899 := bstep (se 1 (by rfl) ⟨1658924, by rfl⟩ : syracuseStep 2211899 = 3317849) B3317849
theorem B5314565 : Blo 2211435 5314565 := bbase (se 4 (by rfl) ⟨498240, by rfl⟩ : syracuseStep 5314565 = 996481) (by norm_num)
theorem B3543043 : Blo 2211435 3543043 := bstep (se 1 (by rfl) ⟨2657282, by rfl⟩ : syracuseStep 3543043 = 5314565) B5314565
theorem B4724057 : Blo 2211435 4724057 := bstep (se 2 (by rfl) ⟨1771521, by rfl⟩ : syracuseStep 4724057 = 3543043) B3543043
theorem B3149371 : Blo 2211435 3149371 := bstep (se 1 (by rfl) ⟨2362028, by rfl⟩ : syracuseStep 3149371 = 4724057) B4724057
theorem B16796645 : Blo 2211435 16796645 := bstep (se 4 (by rfl) ⟨1574685, by rfl⟩ : syracuseStep 16796645 = 3149371) B3149371
theorem B11197763 : Blo 2211435 11197763 := bstep (se 1 (by rfl) ⟨8398322, by rfl⟩ : syracuseStep 11197763 = 16796645) B16796645
theorem B7465175 : Blo 2211435 7465175 := bstep (se 1 (by rfl) ⟨5598881, by rfl⟩ : syracuseStep 7465175 = 11197763) B11197763
theorem B4976783 : Blo 2211435 4976783 := bstep (se 1 (by rfl) ⟨3732587, by rfl⟩ : syracuseStep 4976783 = 7465175) B7465175
theorem B3317855 : Blo 2211435 3317855 := bstep (se 1 (by rfl) ⟨2488391, by rfl⟩ : syracuseStep 3317855 = 4976783) B4976783
theorem B2211903 : Blo 2211435 2211903 := bstep (se 1 (by rfl) ⟨1658927, by rfl⟩ : syracuseStep 2211903 = 3317855) B3317855
theorem B3317861 : Blo 2211435 3317861 := bbase (se 4 (by rfl) ⟨311049, by rfl⟩ : syracuseStep 3317861 = 622099) (by norm_num)
theorem B2211907 : Blo 2211435 2211907 := bstep (se 1 (by rfl) ⟨1658930, by rfl⟩ : syracuseStep 2211907 = 3317861) B3317861
theorem B2522353 : Blo 2211435 2522353 := bbase (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) (by norm_num)
theorem B3363137 : Blo 2211435 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B2242091 : Blo 2211435 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B5978909 : Blo 2211435 5978909 := bstep (se 3 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 5978909 = 2242091) B2242091
theorem B3985939 : Blo 2211435 3985939 := bstep (se 1 (by rfl) ⟨2989454, by rfl⟩ : syracuseStep 3985939 = 5978909) B5978909
theorem B5314585 : Blo 2211435 5314585 := bstep (se 2 (by rfl) ⟨1992969, by rfl⟩ : syracuseStep 5314585 = 3985939) B3985939
theorem B7086113 : Blo 2211435 7086113 := bstep (se 2 (by rfl) ⟨2657292, by rfl⟩ : syracuseStep 7086113 = 5314585) B5314585
theorem B4724075 : Blo 2211435 4724075 := bstep (se 1 (by rfl) ⟨3543056, by rfl⟩ : syracuseStep 4724075 = 7086113) B7086113
theorem B3149383 : Blo 2211435 3149383 := bstep (se 1 (by rfl) ⟨2362037, by rfl⟩ : syracuseStep 3149383 = 4724075) B4724075
theorem B4199177 : Blo 2211435 4199177 := bstep (se 2 (by rfl) ⟨1574691, by rfl⟩ : syracuseStep 4199177 = 3149383) B3149383
theorem B2799451 : Blo 2211435 2799451 := bstep (se 1 (by rfl) ⟨2099588, by rfl⟩ : syracuseStep 2799451 = 4199177) B4199177
theorem B3732601 : Blo 2211435 3732601 := bstep (se 2 (by rfl) ⟨1399725, by rfl⟩ : syracuseStep 3732601 = 2799451) B2799451
theorem B4976801 : Blo 2211435 4976801 := bstep (se 2 (by rfl) ⟨1866300, by rfl⟩ : syracuseStep 4976801 = 3732601) B3732601
theorem B3317867 : Blo 2211435 3317867 := bstep (se 1 (by rfl) ⟨2488400, by rfl⟩ : syracuseStep 3317867 = 4976801) B4976801
theorem B2211911 : Blo 2211435 2211911 := bstep (se 1 (by rfl) ⟨1658933, by rfl⟩ : syracuseStep 2211911 = 3317867) B3317867
theorem B2488405 : Blo 2211435 2488405 := bbase (se 8 (by rfl) ⟨14580, by rfl⟩ : syracuseStep 2488405 = 29161) (by norm_num)
theorem B3317873 : Blo 2211435 3317873 := bstep (se 2 (by rfl) ⟨1244202, by rfl⟩ : syracuseStep 3317873 = 2488405) B2488405
theorem B2211915 : Blo 2211435 2211915 := bstep (se 1 (by rfl) ⟨1658936, by rfl⟩ : syracuseStep 2211915 = 3317873) B3317873
theorem B2799461 : Blo 2211435 2799461 := bbase (se 4 (by rfl) ⟨262449, by rfl⟩ : syracuseStep 2799461 = 524899) (by norm_num)
theorem B7465229 : Blo 2211435 7465229 := bstep (se 3 (by rfl) ⟨1399730, by rfl⟩ : syracuseStep 7465229 = 2799461) B2799461
theorem B4976819 : Blo 2211435 4976819 := bstep (se 1 (by rfl) ⟨3732614, by rfl⟩ : syracuseStep 4976819 = 7465229) B7465229
theorem B3317879 : Blo 2211435 3317879 := bstep (se 1 (by rfl) ⟨2488409, by rfl⟩ : syracuseStep 3317879 = 4976819) B4976819
theorem B2211919 : Blo 2211435 2211919 := bstep (se 1 (by rfl) ⟨1658939, by rfl⟩ : syracuseStep 2211919 = 3317879) B3317879
theorem B3317885 : Blo 2211435 3317885 := bbase (se 3 (by rfl) ⟨622103, by rfl⟩ : syracuseStep 3317885 = 1244207) (by norm_num)
theorem B2211923 : Blo 2211435 2211923 := bstep (se 1 (by rfl) ⟨1658942, by rfl⟩ : syracuseStep 2211923 = 3317885) B3317885
theorem B4976837 : Blo 2211435 4976837 := bbase (se 4 (by rfl) ⟨466578, by rfl⟩ : syracuseStep 4976837 = 933157) (by norm_num)
theorem B3317891 : Blo 2211435 3317891 := bstep (se 1 (by rfl) ⟨2488418, by rfl⟩ : syracuseStep 3317891 = 4976837) B4976837
theorem B2211927 : Blo 2211435 2211927 := bstep (se 1 (by rfl) ⟨1658945, by rfl⟩ : syracuseStep 2211927 = 3317891) B3317891
theorem B17026037 : Blo 2211435 17026037 := bbase (se 5 (by rfl) ⟨798095, by rfl⟩ : syracuseStep 17026037 = 1596191) (by norm_num)
theorem B11350691 : Blo 2211435 11350691 := bstep (se 1 (by rfl) ⟨8513018, by rfl⟩ : syracuseStep 11350691 = 17026037) B17026037
theorem B7567127 : Blo 2211435 7567127 := bstep (se 1 (by rfl) ⟨5675345, by rfl⟩ : syracuseStep 7567127 = 11350691) B11350691
theorem B5044751 : Blo 2211435 5044751 := bstep (se 1 (by rfl) ⟨3783563, by rfl⟩ : syracuseStep 5044751 = 7567127) B7567127
theorem B3363167 : Blo 2211435 3363167 := bstep (se 1 (by rfl) ⟨2522375, by rfl⟩ : syracuseStep 3363167 = 5044751) B5044751
theorem B2242111 : Blo 2211435 2242111 := bstep (se 1 (by rfl) ⟨1681583, by rfl⟩ : syracuseStep 2242111 = 3363167) B3363167
theorem B2989481 : Blo 2211435 2989481 := bstep (se 2 (by rfl) ⟨1121055, by rfl⟩ : syracuseStep 2989481 = 2242111) B2242111
theorem B7971949 : Blo 2211435 7971949 := bstep (se 3 (by rfl) ⟨1494740, by rfl⟩ : syracuseStep 7971949 = 2989481) B2989481
theorem B10629265 : Blo 2211435 10629265 := bstep (se 2 (by rfl) ⟨3985974, by rfl⟩ : syracuseStep 10629265 = 7971949) B7971949
theorem B14172353 : Blo 2211435 14172353 := bstep (se 2 (by rfl) ⟨5314632, by rfl⟩ : syracuseStep 14172353 = 10629265) B10629265
theorem B9448235 : Blo 2211435 9448235 := bstep (se 1 (by rfl) ⟨7086176, by rfl⟩ : syracuseStep 9448235 = 14172353) B14172353
theorem B6298823 : Blo 2211435 6298823 := bstep (se 1 (by rfl) ⟨4724117, by rfl⟩ : syracuseStep 6298823 = 9448235) B9448235
theorem B4199215 : Blo 2211435 4199215 := bstep (se 1 (by rfl) ⟨3149411, by rfl⟩ : syracuseStep 4199215 = 6298823) B6298823
theorem B5598953 : Blo 2211435 5598953 := bstep (se 2 (by rfl) ⟨2099607, by rfl⟩ : syracuseStep 5598953 = 4199215) B4199215
theorem B3732635 : Blo 2211435 3732635 := bstep (se 1 (by rfl) ⟨2799476, by rfl⟩ : syracuseStep 3732635 = 5598953) B5598953
theorem B2488423 : Blo 2211435 2488423 := bstep (se 1 (by rfl) ⟨1866317, by rfl⟩ : syracuseStep 2488423 = 3732635) B3732635
theorem B3317897 : Blo 2211435 3317897 := bstep (se 2 (by rfl) ⟨1244211, by rfl⟩ : syracuseStep 3317897 = 2488423) B2488423
theorem B2211931 : Blo 2211435 2211931 := bstep (se 1 (by rfl) ⟨1658948, by rfl⟩ : syracuseStep 2211931 = 3317897) B3317897
theorem B11197925 : Blo 2211435 11197925 := bbase (se 4 (by rfl) ⟨1049805, by rfl⟩ : syracuseStep 11197925 = 2099611) (by norm_num)
theorem B7465283 : Blo 2211435 7465283 := bstep (se 1 (by rfl) ⟨5598962, by rfl⟩ : syracuseStep 7465283 = 11197925) B11197925
theorem B4976855 : Blo 2211435 4976855 := bstep (se 1 (by rfl) ⟨3732641, by rfl⟩ : syracuseStep 4976855 = 7465283) B7465283
theorem B3317903 : Blo 2211435 3317903 := bstep (se 1 (by rfl) ⟨2488427, by rfl⟩ : syracuseStep 3317903 = 4976855) B4976855
theorem B2211935 : Blo 2211435 2211935 := bstep (se 1 (by rfl) ⟨1658951, by rfl⟩ : syracuseStep 2211935 = 3317903) B3317903
theorem B3317909 : Blo 2211435 3317909 := bbase (se 6 (by rfl) ⟨77763, by rfl⟩ : syracuseStep 3317909 = 155527) (by norm_num)
theorem B2211939 : Blo 2211435 2211939 := bstep (se 1 (by rfl) ⟨1658954, by rfl⟩ : syracuseStep 2211939 = 3317909) B3317909
theorem B5314661 : Blo 2211435 5314661 := bbase (se 4 (by rfl) ⟨498249, by rfl⟩ : syracuseStep 5314661 = 996499) (by norm_num)
theorem B3543107 : Blo 2211435 3543107 := bstep (se 1 (by rfl) ⟨2657330, by rfl⟩ : syracuseStep 3543107 = 5314661) B5314661
theorem B9448285 : Blo 2211435 9448285 := bstep (se 3 (by rfl) ⟨1771553, by rfl⟩ : syracuseStep 9448285 = 3543107) B3543107
theorem B12597713 : Blo 2211435 12597713 := bstep (se 2 (by rfl) ⟨4724142, by rfl⟩ : syracuseStep 12597713 = 9448285) B9448285
theorem B8398475 : Blo 2211435 8398475 := bstep (se 1 (by rfl) ⟨6298856, by rfl⟩ : syracuseStep 8398475 = 12597713) B12597713
theorem B5598983 : Blo 2211435 5598983 := bstep (se 1 (by rfl) ⟨4199237, by rfl⟩ : syracuseStep 5598983 = 8398475) B8398475
theorem B3732655 : Blo 2211435 3732655 := bstep (se 1 (by rfl) ⟨2799491, by rfl⟩ : syracuseStep 3732655 = 5598983) B5598983
theorem B4976873 : Blo 2211435 4976873 := bstep (se 2 (by rfl) ⟨1866327, by rfl⟩ : syracuseStep 4976873 = 3732655) B3732655
theorem B3317915 : Blo 2211435 3317915 := bstep (se 1 (by rfl) ⟨2488436, by rfl⟩ : syracuseStep 3317915 = 4976873) B4976873
theorem B2211943 : Blo 2211435 2211943 := bstep (se 1 (by rfl) ⟨1658957, by rfl⟩ : syracuseStep 2211943 = 3317915) B3317915
theorem B2488441 : Blo 2211435 2488441 := bbase (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) (by norm_num)
theorem B3317921 : Blo 2211435 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B2211947 : Blo 2211435 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B2876413 : Blo 2211435 2876413 := bbase (se 3 (by rfl) ⟨539327, by rfl⟩ : syracuseStep 2876413 = 1078655) (by norm_num)
theorem B3835217 : Blo 2211435 3835217 := bstep (se 2 (by rfl) ⟨1438206, by rfl⟩ : syracuseStep 3835217 = 2876413) B2876413
theorem B2556811 : Blo 2211435 2556811 := bstep (se 1 (by rfl) ⟨1917608, by rfl⟩ : syracuseStep 2556811 = 3835217) B3835217
theorem B13636325 : Blo 2211435 13636325 := bstep (se 4 (by rfl) ⟨1278405, by rfl⟩ : syracuseStep 13636325 = 2556811) B2556811
theorem B9090883 : Blo 2211435 9090883 := bstep (se 1 (by rfl) ⟨6818162, by rfl⟩ : syracuseStep 9090883 = 13636325) B13636325
theorem B48484709 : Blo 2211435 48484709 := bstep (se 4 (by rfl) ⟨4545441, by rfl⟩ : syracuseStep 48484709 = 9090883) B9090883
theorem B32323139 : Blo 2211435 32323139 := bstep (se 1 (by rfl) ⟨24242354, by rfl⟩ : syracuseStep 32323139 = 48484709) B48484709
theorem B21548759 : Blo 2211435 21548759 := bstep (se 1 (by rfl) ⟨16161569, by rfl⟩ : syracuseStep 21548759 = 32323139) B32323139
theorem B57463357 : Blo 2211435 57463357 := bstep (se 3 (by rfl) ⟨10774379, by rfl⟩ : syracuseStep 57463357 = 21548759) B21548759
theorem B76617809 : Blo 2211435 76617809 := bstep (se 2 (by rfl) ⟨28731678, by rfl⟩ : syracuseStep 76617809 = 57463357) B57463357
theorem B51078539 : Blo 2211435 51078539 := bstep (se 1 (by rfl) ⟨38308904, by rfl⟩ : syracuseStep 51078539 = 76617809) B76617809
theorem B136209437 : Blo 2211435 136209437 := bstep (se 3 (by rfl) ⟨25539269, by rfl⟩ : syracuseStep 136209437 = 51078539) B51078539
theorem B90806291 : Blo 2211435 90806291 := bstep (se 1 (by rfl) ⟨68104718, by rfl⟩ : syracuseStep 90806291 = 136209437) B136209437
theorem B60537527 : Blo 2211435 60537527 := bstep (se 1 (by rfl) ⟨45403145, by rfl⟩ : syracuseStep 60537527 = 90806291) B90806291
theorem B40358351 : Blo 2211435 40358351 := bstep (se 1 (by rfl) ⟨30268763, by rfl⟩ : syracuseStep 40358351 = 60537527) B60537527
theorem B107622269 : Blo 2211435 107622269 := bstep (se 3 (by rfl) ⟨20179175, by rfl⟩ : syracuseStep 107622269 = 40358351) B40358351
theorem B71748179 : Blo 2211435 71748179 := bstep (se 1 (by rfl) ⟨53811134, by rfl⟩ : syracuseStep 71748179 = 107622269) B107622269
theorem B47832119 : Blo 2211435 47832119 := bstep (se 1 (by rfl) ⟨35874089, by rfl⟩ : syracuseStep 47832119 = 71748179) B71748179
theorem B31888079 : Blo 2211435 31888079 := bstep (se 1 (by rfl) ⟨23916059, by rfl⟩ : syracuseStep 31888079 = 47832119) B47832119
theorem B21258719 : Blo 2211435 21258719 := bstep (se 1 (by rfl) ⟨15944039, by rfl⟩ : syracuseStep 21258719 = 31888079) B31888079
theorem B14172479 : Blo 2211435 14172479 := bstep (se 1 (by rfl) ⟨10629359, by rfl⟩ : syracuseStep 14172479 = 21258719) B21258719
theorem B9448319 : Blo 2211435 9448319 := bstep (se 1 (by rfl) ⟨7086239, by rfl⟩ : syracuseStep 9448319 = 14172479) B14172479
theorem B6298879 : Blo 2211435 6298879 := bstep (se 1 (by rfl) ⟨4724159, by rfl⟩ : syracuseStep 6298879 = 9448319) B9448319
theorem B8398505 : Blo 2211435 8398505 := bstep (se 2 (by rfl) ⟨3149439, by rfl⟩ : syracuseStep 8398505 = 6298879) B6298879
theorem B5599003 : Blo 2211435 5599003 := bstep (se 1 (by rfl) ⟨4199252, by rfl⟩ : syracuseStep 5599003 = 8398505) B8398505
theorem B7465337 : Blo 2211435 7465337 := bstep (se 2 (by rfl) ⟨2799501, by rfl⟩ : syracuseStep 7465337 = 5599003) B5599003
theorem B4976891 : Blo 2211435 4976891 := bstep (se 1 (by rfl) ⟨3732668, by rfl⟩ : syracuseStep 4976891 = 7465337) B7465337
theorem B3317927 : Blo 2211435 3317927 := bstep (se 1 (by rfl) ⟨2488445, by rfl⟩ : syracuseStep 3317927 = 4976891) B4976891
theorem B2211951 : Blo 2211435 2211951 := bstep (se 1 (by rfl) ⟨1658963, by rfl⟩ : syracuseStep 2211951 = 3317927) B3317927
theorem B3317933 : Blo 2211435 3317933 := bbase (se 3 (by rfl) ⟨622112, by rfl⟩ : syracuseStep 3317933 = 1244225) (by norm_num)
theorem B2211955 : Blo 2211435 2211955 := bstep (se 1 (by rfl) ⟨1658966, by rfl⟩ : syracuseStep 2211955 = 3317933) B3317933
theorem B4976909 : Blo 2211435 4976909 := bbase (se 3 (by rfl) ⟨933170, by rfl⟩ : syracuseStep 4976909 = 1866341) (by norm_num)
theorem B3317939 : Blo 2211435 3317939 := bstep (se 1 (by rfl) ⟨2488454, by rfl⟩ : syracuseStep 3317939 = 4976909) B4976909
theorem B2211959 : Blo 2211435 2211959 := bstep (se 1 (by rfl) ⟨1658969, by rfl⟩ : syracuseStep 2211959 = 3317939) B3317939
theorem B2799517 : Blo 2211435 2799517 := bbase (se 3 (by rfl) ⟨524909, by rfl⟩ : syracuseStep 2799517 = 1049819) (by norm_num)
theorem B3732689 : Blo 2211435 3732689 := bstep (se 2 (by rfl) ⟨1399758, by rfl⟩ : syracuseStep 3732689 = 2799517) B2799517
theorem B2488459 : Blo 2211435 2488459 := bstep (se 1 (by rfl) ⟨1866344, by rfl⟩ : syracuseStep 2488459 = 3732689) B3732689
theorem B3317945 : Blo 2211435 3317945 := bstep (se 2 (by rfl) ⟨1244229, by rfl⟩ : syracuseStep 3317945 = 2488459) B2488459
theorem B2211963 : Blo 2211435 2211963 := bstep (se 1 (by rfl) ⟨1658972, by rfl⟩ : syracuseStep 2211963 = 3317945) B3317945
theorem B3363221 : Blo 2211435 3363221 := bbase (se 6 (by rfl) ⟨78825, by rfl⟩ : syracuseStep 3363221 = 157651) (by norm_num)
theorem B8968589 : Blo 2211435 8968589 := bstep (se 3 (by rfl) ⟨1681610, by rfl⟩ : syracuseStep 8968589 = 3363221) B3363221
theorem B5979059 : Blo 2211435 5979059 := bstep (se 1 (by rfl) ⟨4484294, by rfl⟩ : syracuseStep 5979059 = 8968589) B8968589
theorem B3986039 : Blo 2211435 3986039 := bstep (se 1 (by rfl) ⟨2989529, by rfl⟩ : syracuseStep 3986039 = 5979059) B5979059
theorem B2657359 : Blo 2211435 2657359 := bstep (se 1 (by rfl) ⟨1993019, by rfl⟩ : syracuseStep 2657359 = 3986039) B3986039
theorem B3543145 : Blo 2211435 3543145 := bstep (se 2 (by rfl) ⟨1328679, by rfl⟩ : syracuseStep 3543145 = 2657359) B2657359
theorem B18896773 : Blo 2211435 18896773 := bstep (se 4 (by rfl) ⟨1771572, by rfl⟩ : syracuseStep 18896773 = 3543145) B3543145
theorem B25195697 : Blo 2211435 25195697 := bstep (se 2 (by rfl) ⟨9448386, by rfl⟩ : syracuseStep 25195697 = 18896773) B18896773
theorem B16797131 : Blo 2211435 16797131 := bstep (se 1 (by rfl) ⟨12597848, by rfl⟩ : syracuseStep 16797131 = 25195697) B25195697
theorem B11198087 : Blo 2211435 11198087 := bstep (se 1 (by rfl) ⟨8398565, by rfl⟩ : syracuseStep 11198087 = 16797131) B16797131
theorem B7465391 : Blo 2211435 7465391 := bstep (se 1 (by rfl) ⟨5599043, by rfl⟩ : syracuseStep 7465391 = 11198087) B11198087
theorem B4976927 : Blo 2211435 4976927 := bstep (se 1 (by rfl) ⟨3732695, by rfl⟩ : syracuseStep 4976927 = 7465391) B7465391
theorem B3317951 : Blo 2211435 3317951 := bstep (se 1 (by rfl) ⟨2488463, by rfl⟩ : syracuseStep 3317951 = 4976927) B4976927
theorem B2211967 : Blo 2211435 2211967 := bstep (se 1 (by rfl) ⟨1658975, by rfl⟩ : syracuseStep 2211967 = 3317951) B3317951
theorem B3317957 : Blo 2211435 3317957 := bbase (se 4 (by rfl) ⟨311058, by rfl⟩ : syracuseStep 3317957 = 622117) (by norm_num)
theorem B2211971 : Blo 2211435 2211971 := bstep (se 1 (by rfl) ⟨1658978, by rfl⟩ : syracuseStep 2211971 = 3317957) B3317957
theorem B3732709 : Blo 2211435 3732709 := bbase (se 4 (by rfl) ⟨349941, by rfl⟩ : syracuseStep 3732709 = 699883) (by norm_num)
theorem B4976945 : Blo 2211435 4976945 := bstep (se 2 (by rfl) ⟨1866354, by rfl⟩ : syracuseStep 4976945 = 3732709) B3732709
theorem B3317963 : Blo 2211435 3317963 := bstep (se 1 (by rfl) ⟨2488472, by rfl⟩ : syracuseStep 3317963 = 4976945) B4976945
theorem B2211975 : Blo 2211435 2211975 := bstep (se 1 (by rfl) ⟨1658981, by rfl⟩ : syracuseStep 2211975 = 3317963) B3317963
theorem B2488477 : Blo 2211435 2488477 := bbase (se 3 (by rfl) ⟨466589, by rfl⟩ : syracuseStep 2488477 = 933179) (by norm_num)
theorem B3317969 : Blo 2211435 3317969 := bstep (se 2 (by rfl) ⟨1244238, by rfl⟩ : syracuseStep 3317969 = 2488477) B2488477
theorem B2211979 : Blo 2211435 2211979 := bstep (se 1 (by rfl) ⟨1658984, by rfl⟩ : syracuseStep 2211979 = 3317969) B3317969
theorem B7465445 : Blo 2211435 7465445 := bbase (se 4 (by rfl) ⟨699885, by rfl⟩ : syracuseStep 7465445 = 1399771) (by norm_num)
theorem B4976963 : Blo 2211435 4976963 := bstep (se 1 (by rfl) ⟨3732722, by rfl⟩ : syracuseStep 4976963 = 7465445) B7465445
theorem B3317975 : Blo 2211435 3317975 := bstep (se 1 (by rfl) ⟨2488481, by rfl⟩ : syracuseStep 3317975 = 4976963) B4976963
theorem B2211983 : Blo 2211435 2211983 := bstep (se 1 (by rfl) ⟨1658987, by rfl⟩ : syracuseStep 2211983 = 3317975) B3317975
theorem B3317981 : Blo 2211435 3317981 := bbase (se 3 (by rfl) ⟨622121, by rfl⟩ : syracuseStep 3317981 = 1244243) (by norm_num)
theorem B2211987 : Blo 2211435 2211987 := bstep (se 1 (by rfl) ⟨1658990, by rfl⟩ : syracuseStep 2211987 = 3317981) B3317981
theorem B4976981 : Blo 2211435 4976981 := bbase (se 10 (by rfl) ⟨7290, by rfl⟩ : syracuseStep 4976981 = 14581) (by norm_num)
theorem B3317987 : Blo 2211435 3317987 := bstep (se 1 (by rfl) ⟨2488490, by rfl⟩ : syracuseStep 3317987 = 4976981) B4976981
theorem B2211991 : Blo 2211435 2211991 := bstep (se 1 (by rfl) ⟨1658993, by rfl⟩ : syracuseStep 2211991 = 3317987) B3317987
theorem B7972181 : Blo 2211435 7972181 := bbase (se 12 (by rfl) ⟨2919, by rfl⟩ : syracuseStep 7972181 = 5839) (by norm_num)
theorem B5314787 : Blo 2211435 5314787 := bstep (se 1 (by rfl) ⟨3986090, by rfl⟩ : syracuseStep 5314787 = 7972181) B7972181
theorem B3543191 : Blo 2211435 3543191 := bstep (se 1 (by rfl) ⟨2657393, by rfl⟩ : syracuseStep 3543191 = 5314787) B5314787
theorem B2362127 : Blo 2211435 2362127 := bstep (se 1 (by rfl) ⟨1771595, by rfl⟩ : syracuseStep 2362127 = 3543191) B3543191
theorem B6299005 : Blo 2211435 6299005 := bstep (se 3 (by rfl) ⟨1181063, by rfl⟩ : syracuseStep 6299005 = 2362127) B2362127
theorem B8398673 : Blo 2211435 8398673 := bstep (se 2 (by rfl) ⟨3149502, by rfl⟩ : syracuseStep 8398673 = 6299005) B6299005
theorem B5599115 : Blo 2211435 5599115 := bstep (se 1 (by rfl) ⟨4199336, by rfl⟩ : syracuseStep 5599115 = 8398673) B8398673
theorem B3732743 : Blo 2211435 3732743 := bstep (se 1 (by rfl) ⟨2799557, by rfl⟩ : syracuseStep 3732743 = 5599115) B5599115
theorem B2488495 : Blo 2211435 2488495 := bstep (se 1 (by rfl) ⟨1866371, by rfl⟩ : syracuseStep 2488495 = 3732743) B3732743
theorem B3317993 : Blo 2211435 3317993 := bstep (se 2 (by rfl) ⟨1244247, by rfl⟩ : syracuseStep 3317993 = 2488495) B2488495
theorem B2211995 : Blo 2211435 2211995 := bstep (se 1 (by rfl) ⟨1658996, by rfl⟩ : syracuseStep 2211995 = 3317993) B3317993
theorem B42518357 : Blo 2211435 42518357 := bbase (se 9 (by rfl) ⟨124565, by rfl⟩ : syracuseStep 42518357 = 249131) (by norm_num)
theorem B28345571 : Blo 2211435 28345571 := bstep (se 1 (by rfl) ⟨21259178, by rfl⟩ : syracuseStep 28345571 = 42518357) B42518357
theorem B18897047 : Blo 2211435 18897047 := bstep (se 1 (by rfl) ⟨14172785, by rfl⟩ : syracuseStep 18897047 = 28345571) B28345571
theorem B12598031 : Blo 2211435 12598031 := bstep (se 1 (by rfl) ⟨9448523, by rfl⟩ : syracuseStep 12598031 = 18897047) B18897047
theorem B8398687 : Blo 2211435 8398687 := bstep (se 1 (by rfl) ⟨6299015, by rfl⟩ : syracuseStep 8398687 = 12598031) B12598031
theorem B11198249 : Blo 2211435 11198249 := bstep (se 2 (by rfl) ⟨4199343, by rfl⟩ : syracuseStep 11198249 = 8398687) B8398687
theorem B7465499 : Blo 2211435 7465499 := bstep (se 1 (by rfl) ⟨5599124, by rfl⟩ : syracuseStep 7465499 = 11198249) B11198249
theorem B4976999 : Blo 2211435 4976999 := bstep (se 1 (by rfl) ⟨3732749, by rfl⟩ : syracuseStep 4976999 = 7465499) B7465499
theorem B3317999 : Blo 2211435 3317999 := bstep (se 1 (by rfl) ⟨2488499, by rfl⟩ : syracuseStep 3317999 = 4976999) B4976999
theorem B2211999 : Blo 2211435 2211999 := bstep (se 1 (by rfl) ⟨1658999, by rfl⟩ : syracuseStep 2211999 = 3317999) B3317999
theorem B3318005 : Blo 2211435 3318005 := bbase (se 5 (by rfl) ⟨155531, by rfl⟩ : syracuseStep 3318005 = 311063) (by norm_num)
theorem B2212003 : Blo 2211435 2212003 := bstep (se 1 (by rfl) ⟨1659002, by rfl⟩ : syracuseStep 2212003 = 3318005) B3318005
theorem B17026613 : Blo 2211435 17026613 := bbase (se 5 (by rfl) ⟨798122, by rfl⟩ : syracuseStep 17026613 = 1596245) (by norm_num)
theorem B11351075 : Blo 2211435 11351075 := bstep (se 1 (by rfl) ⟨8513306, by rfl⟩ : syracuseStep 11351075 = 17026613) B17026613
theorem B30269533 : Blo 2211435 30269533 := bstep (se 3 (by rfl) ⟨5675537, by rfl⟩ : syracuseStep 30269533 = 11351075) B11351075
theorem B40359377 : Blo 2211435 40359377 := bstep (se 2 (by rfl) ⟨15134766, by rfl⟩ : syracuseStep 40359377 = 30269533) B30269533
theorem B26906251 : Blo 2211435 26906251 := bstep (se 1 (by rfl) ⟨20179688, by rfl⟩ : syracuseStep 26906251 = 40359377) B40359377
theorem B35875001 : Blo 2211435 35875001 := bstep (se 2 (by rfl) ⟨13453125, by rfl⟩ : syracuseStep 35875001 = 26906251) B26906251
theorem B23916667 : Blo 2211435 23916667 := bstep (se 1 (by rfl) ⟨17937500, by rfl⟩ : syracuseStep 23916667 = 35875001) B35875001
theorem B31888889 : Blo 2211435 31888889 := bstep (se 2 (by rfl) ⟨11958333, by rfl⟩ : syracuseStep 31888889 = 23916667) B23916667
theorem B21259259 : Blo 2211435 21259259 := bstep (se 1 (by rfl) ⟨15944444, by rfl⟩ : syracuseStep 21259259 = 31888889) B31888889
theorem B14172839 : Blo 2211435 14172839 := bstep (se 1 (by rfl) ⟨10629629, by rfl⟩ : syracuseStep 14172839 = 21259259) B21259259
theorem B9448559 : Blo 2211435 9448559 := bstep (se 1 (by rfl) ⟨7086419, by rfl⟩ : syracuseStep 9448559 = 14172839) B14172839
theorem B6299039 : Blo 2211435 6299039 := bstep (se 1 (by rfl) ⟨4724279, by rfl⟩ : syracuseStep 6299039 = 9448559) B9448559
theorem B4199359 : Blo 2211435 4199359 := bstep (se 1 (by rfl) ⟨3149519, by rfl⟩ : syracuseStep 4199359 = 6299039) B6299039
theorem B5599145 : Blo 2211435 5599145 := bstep (se 2 (by rfl) ⟨2099679, by rfl⟩ : syracuseStep 5599145 = 4199359) B4199359
theorem B3732763 : Blo 2211435 3732763 := bstep (se 1 (by rfl) ⟨2799572, by rfl⟩ : syracuseStep 3732763 = 5599145) B5599145
theorem B4977017 : Blo 2211435 4977017 := bstep (se 2 (by rfl) ⟨1866381, by rfl⟩ : syracuseStep 4977017 = 3732763) B3732763
theorem B3318011 : Blo 2211435 3318011 := bstep (se 1 (by rfl) ⟨2488508, by rfl⟩ : syracuseStep 3318011 = 4977017) B4977017
theorem B2212007 : Blo 2211435 2212007 := bstep (se 1 (by rfl) ⟨1659005, by rfl⟩ : syracuseStep 2212007 = 3318011) B3318011
theorem B2488513 : Blo 2211435 2488513 := bbase (se 2 (by rfl) ⟨933192, by rfl⟩ : syracuseStep 2488513 = 1866385) (by norm_num)
theorem B3318017 : Blo 2211435 3318017 := bstep (se 2 (by rfl) ⟨1244256, by rfl⟩ : syracuseStep 3318017 = 2488513) B2488513
theorem B2212011 : Blo 2211435 2212011 := bstep (se 1 (by rfl) ⟨1659008, by rfl⟩ : syracuseStep 2212011 = 3318017) B3318017
theorem B5599165 : Blo 2211435 5599165 := bbase (se 3 (by rfl) ⟨1049843, by rfl⟩ : syracuseStep 5599165 = 2099687) (by norm_num)
theorem B7465553 : Blo 2211435 7465553 := bstep (se 2 (by rfl) ⟨2799582, by rfl⟩ : syracuseStep 7465553 = 5599165) B5599165
theorem B4977035 : Blo 2211435 4977035 := bstep (se 1 (by rfl) ⟨3732776, by rfl⟩ : syracuseStep 4977035 = 7465553) B7465553
theorem B3318023 : Blo 2211435 3318023 := bstep (se 1 (by rfl) ⟨2488517, by rfl⟩ : syracuseStep 3318023 = 4977035) B4977035
theorem B2212015 : Blo 2211435 2212015 := bstep (se 1 (by rfl) ⟨1659011, by rfl⟩ : syracuseStep 2212015 = 3318023) B3318023
theorem B3318029 : Blo 2211435 3318029 := bbase (se 3 (by rfl) ⟨622130, by rfl⟩ : syracuseStep 3318029 = 1244261) (by norm_num)
theorem B2212019 : Blo 2211435 2212019 := bstep (se 1 (by rfl) ⟨1659014, by rfl⟩ : syracuseStep 2212019 = 3318029) B3318029
theorem B4977053 : Blo 2211435 4977053 := bbase (se 3 (by rfl) ⟨933197, by rfl⟩ : syracuseStep 4977053 = 1866395) (by norm_num)
theorem B3318035 : Blo 2211435 3318035 := bstep (se 1 (by rfl) ⟨2488526, by rfl⟩ : syracuseStep 3318035 = 4977053) B4977053
theorem B2212023 : Blo 2211435 2212023 := bstep (se 1 (by rfl) ⟨1659017, by rfl⟩ : syracuseStep 2212023 = 3318035) B3318035
theorem B3732797 : Blo 2211435 3732797 := bbase (se 3 (by rfl) ⟨699899, by rfl⟩ : syracuseStep 3732797 = 1399799) (by norm_num)
theorem B2488531 : Blo 2211435 2488531 := bstep (se 1 (by rfl) ⟨1866398, by rfl⟩ : syracuseStep 2488531 = 3732797) B3732797
theorem B3318041 : Blo 2211435 3318041 := bstep (se 2 (by rfl) ⟨1244265, by rfl⟩ : syracuseStep 3318041 = 2488531) B2488531
theorem B2212027 : Blo 2211435 2212027 := bstep (se 1 (by rfl) ⟨1659020, by rfl⟩ : syracuseStep 2212027 = 3318041) B3318041
theorem B2362165 : Blo 2211435 2362165 := bbase (se 5 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 2362165 = 221453) (by norm_num)
theorem B12598213 : Blo 2211435 12598213 := bstep (se 4 (by rfl) ⟨1181082, by rfl⟩ : syracuseStep 12598213 = 2362165) B2362165
theorem B16797617 : Blo 2211435 16797617 := bstep (se 2 (by rfl) ⟨6299106, by rfl⟩ : syracuseStep 16797617 = 12598213) B12598213
theorem B11198411 : Blo 2211435 11198411 := bstep (se 1 (by rfl) ⟨8398808, by rfl⟩ : syracuseStep 11198411 = 16797617) B16797617
theorem B7465607 : Blo 2211435 7465607 := bstep (se 1 (by rfl) ⟨5599205, by rfl⟩ : syracuseStep 7465607 = 11198411) B11198411
theorem B4977071 : Blo 2211435 4977071 := bstep (se 1 (by rfl) ⟨3732803, by rfl⟩ : syracuseStep 4977071 = 7465607) B7465607
theorem B3318047 : Blo 2211435 3318047 := bstep (se 1 (by rfl) ⟨2488535, by rfl⟩ : syracuseStep 3318047 = 4977071) B4977071
theorem B2212031 : Blo 2211435 2212031 := bstep (se 1 (by rfl) ⟨1659023, by rfl⟩ : syracuseStep 2212031 = 3318047) B3318047
theorem B3318053 : Blo 2211435 3318053 := bbase (se 4 (by rfl) ⟨311067, by rfl⟩ : syracuseStep 3318053 = 622135) (by norm_num)
theorem B2212035 : Blo 2211435 2212035 := bstep (se 1 (by rfl) ⟨1659026, by rfl⟩ : syracuseStep 2212035 = 3318053) B3318053
theorem B2799613 : Blo 2211435 2799613 := bbase (se 3 (by rfl) ⟨524927, by rfl⟩ : syracuseStep 2799613 = 1049855) (by norm_num)
theorem B3732817 : Blo 2211435 3732817 := bstep (se 2 (by rfl) ⟨1399806, by rfl⟩ : syracuseStep 3732817 = 2799613) B2799613
theorem B4977089 : Blo 2211435 4977089 := bstep (se 2 (by rfl) ⟨1866408, by rfl⟩ : syracuseStep 4977089 = 3732817) B3732817
theorem B3318059 : Blo 2211435 3318059 := bstep (se 1 (by rfl) ⟨2488544, by rfl⟩ : syracuseStep 3318059 = 4977089) B4977089
theorem B2212039 : Blo 2211435 2212039 := bstep (se 1 (by rfl) ⟨1659029, by rfl⟩ : syracuseStep 2212039 = 3318059) B3318059
theorem B2488549 : Blo 2211435 2488549 := bbase (se 4 (by rfl) ⟨233301, by rfl⟩ : syracuseStep 2488549 = 466603) (by norm_num)
theorem B3318065 : Blo 2211435 3318065 := bstep (se 2 (by rfl) ⟨1244274, by rfl⟩ : syracuseStep 3318065 = 2488549) B2488549
theorem B2212043 : Blo 2211435 2212043 := bstep (se 1 (by rfl) ⟨1659032, by rfl⟩ : syracuseStep 2212043 = 3318065) B3318065
theorem B4724365 : Blo 2211435 4724365 := bbase (se 3 (by rfl) ⟨885818, by rfl⟩ : syracuseStep 4724365 = 1771637) (by norm_num)
theorem B6299153 : Blo 2211435 6299153 := bstep (se 2 (by rfl) ⟨2362182, by rfl⟩ : syracuseStep 6299153 = 4724365) B4724365
theorem B4199435 : Blo 2211435 4199435 := bstep (se 1 (by rfl) ⟨3149576, by rfl⟩ : syracuseStep 4199435 = 6299153) B6299153
theorem B2799623 : Blo 2211435 2799623 := bstep (se 1 (by rfl) ⟨2099717, by rfl⟩ : syracuseStep 2799623 = 4199435) B4199435
theorem B7465661 : Blo 2211435 7465661 := bstep (se 3 (by rfl) ⟨1399811, by rfl⟩ : syracuseStep 7465661 = 2799623) B2799623
theorem B4977107 : Blo 2211435 4977107 := bstep (se 1 (by rfl) ⟨3732830, by rfl⟩ : syracuseStep 4977107 = 7465661) B7465661
theorem B3318071 : Blo 2211435 3318071 := bstep (se 1 (by rfl) ⟨2488553, by rfl⟩ : syracuseStep 3318071 = 4977107) B4977107
theorem B2212047 : Blo 2211435 2212047 := bstep (se 1 (by rfl) ⟨1659035, by rfl⟩ : syracuseStep 2212047 = 3318071) B3318071
theorem B3318077 : Blo 2211435 3318077 := bbase (se 3 (by rfl) ⟨622139, by rfl⟩ : syracuseStep 3318077 = 1244279) (by norm_num)
theorem B2212051 : Blo 2211435 2212051 := bstep (se 1 (by rfl) ⟨1659038, by rfl⟩ : syracuseStep 2212051 = 3318077) B3318077
theorem B4977125 : Blo 2211435 4977125 := bbase (se 4 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 4977125 = 933211) (by norm_num)
theorem B3318083 : Blo 2211435 3318083 := bstep (se 1 (by rfl) ⟨2488562, by rfl⟩ : syracuseStep 3318083 = 4977125) B4977125
theorem B2212055 : Blo 2211435 2212055 := bstep (se 1 (by rfl) ⟨1659041, by rfl⟩ : syracuseStep 2212055 = 3318083) B3318083
theorem B5599277 : Blo 2211435 5599277 := bbase (se 3 (by rfl) ⟨1049864, by rfl⟩ : syracuseStep 5599277 = 2099729) (by norm_num)
theorem B3732851 : Blo 2211435 3732851 := bstep (se 1 (by rfl) ⟨2799638, by rfl⟩ : syracuseStep 3732851 = 5599277) B5599277
theorem B2488567 : Blo 2211435 2488567 := bstep (se 1 (by rfl) ⟨1866425, by rfl⟩ : syracuseStep 2488567 = 3732851) B3732851
theorem B3318089 : Blo 2211435 3318089 := bstep (se 2 (by rfl) ⟨1244283, by rfl⟩ : syracuseStep 3318089 = 2488567) B2488567
theorem B2212059 : Blo 2211435 2212059 := bstep (se 1 (by rfl) ⟨1659044, by rfl⟩ : syracuseStep 2212059 = 3318089) B3318089
theorem B8513525 : Blo 2211435 8513525 := bbase (se 5 (by rfl) ⟨399071, by rfl⟩ : syracuseStep 8513525 = 798143) (by norm_num)
theorem B5675683 : Blo 2211435 5675683 := bstep (se 1 (by rfl) ⟨4256762, by rfl⟩ : syracuseStep 5675683 = 8513525) B8513525
theorem B7567577 : Blo 2211435 7567577 := bstep (se 2 (by rfl) ⟨2837841, by rfl⟩ : syracuseStep 7567577 = 5675683) B5675683
theorem B5045051 : Blo 2211435 5045051 := bstep (se 1 (by rfl) ⟨3783788, by rfl⟩ : syracuseStep 5045051 = 7567577) B7567577
theorem B3363367 : Blo 2211435 3363367 := bstep (se 1 (by rfl) ⟨2522525, by rfl⟩ : syracuseStep 3363367 = 5045051) B5045051
theorem B4484489 : Blo 2211435 4484489 := bstep (se 2 (by rfl) ⟨1681683, by rfl⟩ : syracuseStep 4484489 = 3363367) B3363367
theorem B11958637 : Blo 2211435 11958637 := bstep (se 3 (by rfl) ⟨2242244, by rfl⟩ : syracuseStep 11958637 = 4484489) B4484489
theorem B15944849 : Blo 2211435 15944849 := bstep (se 2 (by rfl) ⟨5979318, by rfl⟩ : syracuseStep 15944849 = 11958637) B11958637
theorem B10629899 : Blo 2211435 10629899 := bstep (se 1 (by rfl) ⟨7972424, by rfl⟩ : syracuseStep 10629899 = 15944849) B15944849
theorem B7086599 : Blo 2211435 7086599 := bstep (se 1 (by rfl) ⟨5314949, by rfl⟩ : syracuseStep 7086599 = 10629899) B10629899
theorem B4724399 : Blo 2211435 4724399 := bstep (se 1 (by rfl) ⟨3543299, by rfl⟩ : syracuseStep 4724399 = 7086599) B7086599
theorem B3149599 : Blo 2211435 3149599 := bstep (se 1 (by rfl) ⟨2362199, by rfl⟩ : syracuseStep 3149599 = 4724399) B4724399
theorem B4199465 : Blo 2211435 4199465 := bstep (se 2 (by rfl) ⟨1574799, by rfl⟩ : syracuseStep 4199465 = 3149599) B3149599
theorem B11198573 : Blo 2211435 11198573 := bstep (se 3 (by rfl) ⟨2099732, by rfl⟩ : syracuseStep 11198573 = 4199465) B4199465
theorem B7465715 : Blo 2211435 7465715 := bstep (se 1 (by rfl) ⟨5599286, by rfl⟩ : syracuseStep 7465715 = 11198573) B11198573
theorem B4977143 : Blo 2211435 4977143 := bstep (se 1 (by rfl) ⟨3732857, by rfl⟩ : syracuseStep 4977143 = 7465715) B7465715
theorem B3318095 : Blo 2211435 3318095 := bstep (se 1 (by rfl) ⟨2488571, by rfl⟩ : syracuseStep 3318095 = 4977143) B4977143
theorem B2212063 : Blo 2211435 2212063 := bstep (se 1 (by rfl) ⟨1659047, by rfl⟩ : syracuseStep 2212063 = 3318095) B3318095
theorem B3318101 : Blo 2211435 3318101 := bbase (se 10 (by rfl) ⟨4860, by rfl⟩ : syracuseStep 3318101 = 9721) (by norm_num)
theorem B2212067 : Blo 2211435 2212067 := bstep (se 1 (by rfl) ⟨1659050, by rfl⟩ : syracuseStep 2212067 = 3318101) B3318101
theorem B6299221 : Blo 2211435 6299221 := bbase (se 8 (by rfl) ⟨36909, by rfl⟩ : syracuseStep 6299221 = 73819) (by norm_num)
theorem B8398961 : Blo 2211435 8398961 := bstep (se 2 (by rfl) ⟨3149610, by rfl⟩ : syracuseStep 8398961 = 6299221) B6299221
theorem B5599307 : Blo 2211435 5599307 := bstep (se 1 (by rfl) ⟨4199480, by rfl⟩ : syracuseStep 5599307 = 8398961) B8398961
theorem B3732871 : Blo 2211435 3732871 := bstep (se 1 (by rfl) ⟨2799653, by rfl⟩ : syracuseStep 3732871 = 5599307) B5599307
theorem B4977161 : Blo 2211435 4977161 := bstep (se 2 (by rfl) ⟨1866435, by rfl⟩ : syracuseStep 4977161 = 3732871) B3732871
theorem B3318107 : Blo 2211435 3318107 := bstep (se 1 (by rfl) ⟨2488580, by rfl⟩ : syracuseStep 3318107 = 4977161) B4977161
theorem B2212071 : Blo 2211435 2212071 := bstep (se 1 (by rfl) ⟨1659053, by rfl⟩ : syracuseStep 2212071 = 3318107) B3318107
theorem B2488585 : Blo 2211435 2488585 := bbase (se 2 (by rfl) ⟨933219, by rfl⟩ : syracuseStep 2488585 = 1866439) (by norm_num)
theorem B3318113 : Blo 2211435 3318113 := bstep (se 2 (by rfl) ⟨1244292, by rfl⟩ : syracuseStep 3318113 = 2488585) B2488585
theorem B2212075 : Blo 2211435 2212075 := bstep (se 1 (by rfl) ⟨1659056, by rfl⟩ : syracuseStep 2212075 = 3318113) B3318113
theorem B25540757 : Blo 2211435 25540757 := bbase (se 6 (by rfl) ⟨598611, by rfl⟩ : syracuseStep 25540757 = 1197223) (by norm_num)
theorem B17027171 : Blo 2211435 17027171 := bstep (se 1 (by rfl) ⟨12770378, by rfl⟩ : syracuseStep 17027171 = 25540757) B25540757
theorem B11351447 : Blo 2211435 11351447 := bstep (se 1 (by rfl) ⟨8513585, by rfl⟩ : syracuseStep 11351447 = 17027171) B17027171
theorem B7567631 : Blo 2211435 7567631 := bstep (se 1 (by rfl) ⟨5675723, by rfl⟩ : syracuseStep 7567631 = 11351447) B11351447
theorem B5045087 : Blo 2211435 5045087 := bstep (se 1 (by rfl) ⟨3783815, by rfl⟩ : syracuseStep 5045087 = 7567631) B7567631
theorem B3363391 : Blo 2211435 3363391 := bstep (se 1 (by rfl) ⟨2522543, by rfl⟩ : syracuseStep 3363391 = 5045087) B5045087
theorem B4484521 : Blo 2211435 4484521 := bstep (se 2 (by rfl) ⟨1681695, by rfl⟩ : syracuseStep 4484521 = 3363391) B3363391
theorem B5979361 : Blo 2211435 5979361 := bstep (se 2 (by rfl) ⟨2242260, by rfl⟩ : syracuseStep 5979361 = 4484521) B4484521
theorem B7972481 : Blo 2211435 7972481 := bstep (se 2 (by rfl) ⟨2989680, by rfl⟩ : syracuseStep 7972481 = 5979361) B5979361
theorem B5314987 : Blo 2211435 5314987 := bstep (se 1 (by rfl) ⟨3986240, by rfl⟩ : syracuseStep 5314987 = 7972481) B7972481
theorem B28346597 : Blo 2211435 28346597 := bstep (se 4 (by rfl) ⟨2657493, by rfl⟩ : syracuseStep 28346597 = 5314987) B5314987
theorem B18897731 : Blo 2211435 18897731 := bstep (se 1 (by rfl) ⟨14173298, by rfl⟩ : syracuseStep 18897731 = 28346597) B28346597
theorem B12598487 : Blo 2211435 12598487 := bstep (se 1 (by rfl) ⟨9448865, by rfl⟩ : syracuseStep 12598487 = 18897731) B18897731
theorem B8398991 : Blo 2211435 8398991 := bstep (se 1 (by rfl) ⟨6299243, by rfl⟩ : syracuseStep 8398991 = 12598487) B12598487
theorem B5599327 : Blo 2211435 5599327 := bstep (se 1 (by rfl) ⟨4199495, by rfl⟩ : syracuseStep 5599327 = 8398991) B8398991
theorem B7465769 : Blo 2211435 7465769 := bstep (se 2 (by rfl) ⟨2799663, by rfl⟩ : syracuseStep 7465769 = 5599327) B5599327
theorem B4977179 : Blo 2211435 4977179 := bstep (se 1 (by rfl) ⟨3732884, by rfl⟩ : syracuseStep 4977179 = 7465769) B7465769
theorem B3318119 : Blo 2211435 3318119 := bstep (se 1 (by rfl) ⟨2488589, by rfl⟩ : syracuseStep 3318119 = 4977179) B4977179
theorem B2212079 : Blo 2211435 2212079 := bstep (se 1 (by rfl) ⟨1659059, by rfl⟩ : syracuseStep 2212079 = 3318119) B3318119
theorem B3318125 : Blo 2211435 3318125 := bbase (se 3 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 3318125 = 1244297) (by norm_num)
theorem B2212083 : Blo 2211435 2212083 := bstep (se 1 (by rfl) ⟨1659062, by rfl⟩ : syracuseStep 2212083 = 3318125) B3318125
theorem B4977197 : Blo 2211435 4977197 := bbase (se 3 (by rfl) ⟨933224, by rfl⟩ : syracuseStep 4977197 = 1866449) (by norm_num)
theorem B3318131 : Blo 2211435 3318131 := bstep (se 1 (by rfl) ⟨2488598, by rfl⟩ : syracuseStep 3318131 = 4977197) B4977197
theorem B2212087 : Blo 2211435 2212087 := bstep (se 1 (by rfl) ⟨1659065, by rfl⟩ : syracuseStep 2212087 = 3318131) B3318131
theorem B8969093 : Blo 2211435 8969093 := bbase (se 4 (by rfl) ⟨840852, by rfl⟩ : syracuseStep 8969093 = 1681705) (by norm_num)
theorem B5979395 : Blo 2211435 5979395 := bstep (se 1 (by rfl) ⟨4484546, by rfl⟩ : syracuseStep 5979395 = 8969093) B8969093
theorem B3986263 : Blo 2211435 3986263 := bstep (se 1 (by rfl) ⟨2989697, by rfl⟩ : syracuseStep 3986263 = 5979395) B5979395
theorem B21260069 : Blo 2211435 21260069 := bstep (se 4 (by rfl) ⟨1993131, by rfl⟩ : syracuseStep 21260069 = 3986263) B3986263
theorem B14173379 : Blo 2211435 14173379 := bstep (se 1 (by rfl) ⟨10630034, by rfl⟩ : syracuseStep 14173379 = 21260069) B21260069
theorem B9448919 : Blo 2211435 9448919 := bstep (se 1 (by rfl) ⟨7086689, by rfl⟩ : syracuseStep 9448919 = 14173379) B14173379
theorem B6299279 : Blo 2211435 6299279 := bstep (se 1 (by rfl) ⟨4724459, by rfl⟩ : syracuseStep 6299279 = 9448919) B9448919
theorem B4199519 : Blo 2211435 4199519 := bstep (se 1 (by rfl) ⟨3149639, by rfl⟩ : syracuseStep 4199519 = 6299279) B6299279
theorem B2799679 : Blo 2211435 2799679 := bstep (se 1 (by rfl) ⟨2099759, by rfl⟩ : syracuseStep 2799679 = 4199519) B4199519
theorem B3732905 : Blo 2211435 3732905 := bstep (se 2 (by rfl) ⟨1399839, by rfl⟩ : syracuseStep 3732905 = 2799679) B2799679
theorem B2488603 : Blo 2211435 2488603 := bstep (se 1 (by rfl) ⟨1866452, by rfl⟩ : syracuseStep 2488603 = 3732905) B3732905
theorem B3318137 : Blo 2211435 3318137 := bstep (se 2 (by rfl) ⟨1244301, by rfl⟩ : syracuseStep 3318137 = 2488603) B2488603
theorem B2212091 : Blo 2211435 2212091 := bstep (se 1 (by rfl) ⟨1659068, by rfl⟩ : syracuseStep 2212091 = 3318137) B3318137
theorem B37795733 : Blo 2211435 37795733 := bbase (se 6 (by rfl) ⟨885837, by rfl⟩ : syracuseStep 37795733 = 1771675) (by norm_num)
theorem B25197155 : Blo 2211435 25197155 := bstep (se 1 (by rfl) ⟨18897866, by rfl⟩ : syracuseStep 25197155 = 37795733) B37795733
theorem B16798103 : Blo 2211435 16798103 := bstep (se 1 (by rfl) ⟨12598577, by rfl⟩ : syracuseStep 16798103 = 25197155) B25197155
theorem B11198735 : Blo 2211435 11198735 := bstep (se 1 (by rfl) ⟨8399051, by rfl⟩ : syracuseStep 11198735 = 16798103) B16798103
theorem B7465823 : Blo 2211435 7465823 := bstep (se 1 (by rfl) ⟨5599367, by rfl⟩ : syracuseStep 7465823 = 11198735) B11198735
theorem B4977215 : Blo 2211435 4977215 := bstep (se 1 (by rfl) ⟨3732911, by rfl⟩ : syracuseStep 4977215 = 7465823) B7465823
theorem B3318143 : Blo 2211435 3318143 := bstep (se 1 (by rfl) ⟨2488607, by rfl⟩ : syracuseStep 3318143 = 4977215) B4977215
theorem B2212095 : Blo 2211435 2212095 := bstep (se 1 (by rfl) ⟨1659071, by rfl⟩ : syracuseStep 2212095 = 3318143) B3318143
theorem B3318149 : Blo 2211435 3318149 := bbase (se 4 (by rfl) ⟨311076, by rfl⟩ : syracuseStep 3318149 = 622153) (by norm_num)
theorem B2212099 : Blo 2211435 2212099 := bstep (se 1 (by rfl) ⟨1659074, by rfl⟩ : syracuseStep 2212099 = 3318149) B3318149
theorem B3732925 : Blo 2211435 3732925 := bbase (se 3 (by rfl) ⟨699923, by rfl⟩ : syracuseStep 3732925 = 1399847) (by norm_num)
theorem B4977233 : Blo 2211435 4977233 := bstep (se 2 (by rfl) ⟨1866462, by rfl⟩ : syracuseStep 4977233 = 3732925) B3732925
theorem B3318155 : Blo 2211435 3318155 := bstep (se 1 (by rfl) ⟨2488616, by rfl⟩ : syracuseStep 3318155 = 4977233) B4977233
theorem B2212103 : Blo 2211435 2212103 := bstep (se 1 (by rfl) ⟨1659077, by rfl⟩ : syracuseStep 2212103 = 3318155) B3318155
theorem B2488621 : Blo 2211435 2488621 := bbase (se 3 (by rfl) ⟨466616, by rfl⟩ : syracuseStep 2488621 = 933233) (by norm_num)
theorem B3318161 : Blo 2211435 3318161 := bstep (se 2 (by rfl) ⟨1244310, by rfl⟩ : syracuseStep 3318161 = 2488621) B2488621
theorem B2212107 : Blo 2211435 2212107 := bstep (se 1 (by rfl) ⟨1659080, by rfl⟩ : syracuseStep 2212107 = 3318161) B3318161
theorem B7465877 : Blo 2211435 7465877 := bbase (se 6 (by rfl) ⟨174981, by rfl⟩ : syracuseStep 7465877 = 349963) (by norm_num)
theorem B4977251 : Blo 2211435 4977251 := bstep (se 1 (by rfl) ⟨3732938, by rfl⟩ : syracuseStep 4977251 = 7465877) B7465877
theorem B3318167 : Blo 2211435 3318167 := bstep (se 1 (by rfl) ⟨2488625, by rfl⟩ : syracuseStep 3318167 = 4977251) B4977251
theorem B2212111 : Blo 2211435 2212111 := bstep (se 1 (by rfl) ⟨1659083, by rfl⟩ : syracuseStep 2212111 = 3318167) B3318167
theorem B3318173 : Blo 2211435 3318173 := bbase (se 3 (by rfl) ⟨622157, by rfl⟩ : syracuseStep 3318173 = 1244315) (by norm_num)
theorem B2212115 : Blo 2211435 2212115 := bstep (se 1 (by rfl) ⟨1659086, by rfl⟩ : syracuseStep 2212115 = 3318173) B3318173
theorem B4977269 : Blo 2211435 4977269 := bbase (se 5 (by rfl) ⟨233309, by rfl⟩ : syracuseStep 4977269 = 466619) (by norm_num)
theorem B3318179 : Blo 2211435 3318179 := bstep (se 1 (by rfl) ⟨2488634, by rfl⟩ : syracuseStep 3318179 = 4977269) B4977269
theorem B2212119 : Blo 2211435 2212119 := bstep (se 1 (by rfl) ⟨1659089, by rfl⟩ : syracuseStep 2212119 = 3318179) B3318179
theorem B8969221 : Blo 2211435 8969221 := bbase (se 4 (by rfl) ⟨840864, by rfl⟩ : syracuseStep 8969221 = 1681729) (by norm_num)
theorem B11958961 : Blo 2211435 11958961 := bstep (se 2 (by rfl) ⟨4484610, by rfl⟩ : syracuseStep 11958961 = 8969221) B8969221
theorem B15945281 : Blo 2211435 15945281 := bstep (se 2 (by rfl) ⟨5979480, by rfl⟩ : syracuseStep 15945281 = 11958961) B11958961
theorem B10630187 : Blo 2211435 10630187 := bstep (se 1 (by rfl) ⟨7972640, by rfl⟩ : syracuseStep 10630187 = 15945281) B15945281
theorem B7086791 : Blo 2211435 7086791 := bstep (se 1 (by rfl) ⟨5315093, by rfl⟩ : syracuseStep 7086791 = 10630187) B10630187
theorem B18898109 : Blo 2211435 18898109 := bstep (se 3 (by rfl) ⟨3543395, by rfl⟩ : syracuseStep 18898109 = 7086791) B7086791
theorem B12598739 : Blo 2211435 12598739 := bstep (se 1 (by rfl) ⟨9449054, by rfl⟩ : syracuseStep 12598739 = 18898109) B18898109
theorem B8399159 : Blo 2211435 8399159 := bstep (se 1 (by rfl) ⟨6299369, by rfl⟩ : syracuseStep 8399159 = 12598739) B12598739
theorem B5599439 : Blo 2211435 5599439 := bstep (se 1 (by rfl) ⟨4199579, by rfl⟩ : syracuseStep 5599439 = 8399159) B8399159
theorem B3732959 : Blo 2211435 3732959 := bstep (se 1 (by rfl) ⟨2799719, by rfl⟩ : syracuseStep 3732959 = 5599439) B5599439
theorem B2488639 : Blo 2211435 2488639 := bstep (se 1 (by rfl) ⟨1866479, by rfl⟩ : syracuseStep 2488639 = 3732959) B3732959
theorem B3318185 : Blo 2211435 3318185 := bstep (se 2 (by rfl) ⟨1244319, by rfl⟩ : syracuseStep 3318185 = 2488639) B2488639
theorem B2212123 : Blo 2211435 2212123 := bstep (se 1 (by rfl) ⟨1659092, by rfl⟩ : syracuseStep 2212123 = 3318185) B3318185
theorem B8399173 : Blo 2211435 8399173 := bbase (se 4 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 8399173 = 1574845) (by norm_num)
theorem B11198897 : Blo 2211435 11198897 := bstep (se 2 (by rfl) ⟨4199586, by rfl⟩ : syracuseStep 11198897 = 8399173) B8399173
theorem B7465931 : Blo 2211435 7465931 := bstep (se 1 (by rfl) ⟨5599448, by rfl⟩ : syracuseStep 7465931 = 11198897) B11198897
theorem B4977287 : Blo 2211435 4977287 := bstep (se 1 (by rfl) ⟨3732965, by rfl⟩ : syracuseStep 4977287 = 7465931) B7465931
theorem B3318191 : Blo 2211435 3318191 := bstep (se 1 (by rfl) ⟨2488643, by rfl⟩ : syracuseStep 3318191 = 4977287) B4977287
theorem B2212127 : Blo 2211435 2212127 := bstep (se 1 (by rfl) ⟨1659095, by rfl⟩ : syracuseStep 2212127 = 3318191) B3318191
theorem B3318197 : Blo 2211435 3318197 := bbase (se 5 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 3318197 = 311081) (by norm_num)
theorem B2212131 : Blo 2211435 2212131 := bstep (se 1 (by rfl) ⟨1659098, by rfl⟩ : syracuseStep 2212131 = 3318197) B3318197
theorem B5599469 : Blo 2211435 5599469 := bbase (se 3 (by rfl) ⟨1049900, by rfl⟩ : syracuseStep 5599469 = 2099801) (by norm_num)
theorem B3732979 : Blo 2211435 3732979 := bstep (se 1 (by rfl) ⟨2799734, by rfl⟩ : syracuseStep 3732979 = 5599469) B5599469
theorem B4977305 : Blo 2211435 4977305 := bstep (se 2 (by rfl) ⟨1866489, by rfl⟩ : syracuseStep 4977305 = 3732979) B3732979
theorem B3318203 : Blo 2211435 3318203 := bstep (se 1 (by rfl) ⟨2488652, by rfl⟩ : syracuseStep 3318203 = 4977305) B4977305
theorem B2212135 : Blo 2211435 2212135 := bstep (se 1 (by rfl) ⟨1659101, by rfl⟩ : syracuseStep 2212135 = 3318203) B3318203
theorem B2488657 : Blo 2211435 2488657 := bbase (se 2 (by rfl) ⟨933246, by rfl⟩ : syracuseStep 2488657 = 1866493) (by norm_num)
theorem B3318209 : Blo 2211435 3318209 := bstep (se 2 (by rfl) ⟨1244328, by rfl⟩ : syracuseStep 3318209 = 2488657) B2488657
theorem B2212139 : Blo 2211435 2212139 := bstep (se 1 (by rfl) ⟨1659104, by rfl⟩ : syracuseStep 2212139 = 3318209) B3318209
theorem B2362285 : Blo 2211435 2362285 := bbase (se 3 (by rfl) ⟨442928, by rfl⟩ : syracuseStep 2362285 = 885857) (by norm_num)
theorem B3149713 : Blo 2211435 3149713 := bstep (se 2 (by rfl) ⟨1181142, by rfl⟩ : syracuseStep 3149713 = 2362285) B2362285
theorem B4199617 : Blo 2211435 4199617 := bstep (se 2 (by rfl) ⟨1574856, by rfl⟩ : syracuseStep 4199617 = 3149713) B3149713
theorem B5599489 : Blo 2211435 5599489 := bstep (se 2 (by rfl) ⟨2099808, by rfl⟩ : syracuseStep 5599489 = 4199617) B4199617
theorem B7465985 : Blo 2211435 7465985 := bstep (se 2 (by rfl) ⟨2799744, by rfl⟩ : syracuseStep 7465985 = 5599489) B5599489
theorem B4977323 : Blo 2211435 4977323 := bstep (se 1 (by rfl) ⟨3732992, by rfl⟩ : syracuseStep 4977323 = 7465985) B7465985
theorem B3318215 : Blo 2211435 3318215 := bstep (se 1 (by rfl) ⟨2488661, by rfl⟩ : syracuseStep 3318215 = 4977323) B4977323
theorem B2212143 : Blo 2211435 2212143 := bstep (se 1 (by rfl) ⟨1659107, by rfl⟩ : syracuseStep 2212143 = 3318215) B3318215
theorem B3318221 : Blo 2211435 3318221 := bbase (se 3 (by rfl) ⟨622166, by rfl⟩ : syracuseStep 3318221 = 1244333) (by norm_num)
theorem B2212147 : Blo 2211435 2212147 := bstep (se 1 (by rfl) ⟨1659110, by rfl⟩ : syracuseStep 2212147 = 3318221) B3318221
theorem B4977341 : Blo 2211435 4977341 := bbase (se 3 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 4977341 = 1866503) (by norm_num)
theorem B3318227 : Blo 2211435 3318227 := bstep (se 1 (by rfl) ⟨2488670, by rfl⟩ : syracuseStep 3318227 = 4977341) B4977341
theorem B2212151 : Blo 2211435 2212151 := bstep (se 1 (by rfl) ⟨1659113, by rfl⟩ : syracuseStep 2212151 = 3318227) B3318227
theorem B3733013 : Blo 2211435 3733013 := bbase (se 6 (by rfl) ⟨87492, by rfl⟩ : syracuseStep 3733013 = 174985) (by norm_num)
theorem B2488675 : Blo 2211435 2488675 := bstep (se 1 (by rfl) ⟨1866506, by rfl⟩ : syracuseStep 2488675 = 3733013) B3733013
theorem B3318233 : Blo 2211435 3318233 := bstep (se 2 (by rfl) ⟨1244337, by rfl⟩ : syracuseStep 3318233 = 2488675) B2488675
theorem B2212155 : Blo 2211435 2212155 := bstep (se 1 (by rfl) ⟨1659116, by rfl⟩ : syracuseStep 2212155 = 3318233) B3318233
theorem B5045269 : Blo 2211435 5045269 := bbase (se 6 (by rfl) ⟨118248, by rfl⟩ : syracuseStep 5045269 = 236497) (by norm_num)
theorem B6727025 : Blo 2211435 6727025 := bstep (se 2 (by rfl) ⟨2522634, by rfl⟩ : syracuseStep 6727025 = 5045269) B5045269
theorem B4484683 : Blo 2211435 4484683 := bstep (se 1 (by rfl) ⟨3363512, by rfl⟩ : syracuseStep 4484683 = 6727025) B6727025
theorem B5979577 : Blo 2211435 5979577 := bstep (se 2 (by rfl) ⟨2242341, by rfl⟩ : syracuseStep 5979577 = 4484683) B4484683
theorem B7972769 : Blo 2211435 7972769 := bstep (se 2 (by rfl) ⟨2989788, by rfl⟩ : syracuseStep 7972769 = 5979577) B5979577
theorem B21260717 : Blo 2211435 21260717 := bstep (se 3 (by rfl) ⟨3986384, by rfl⟩ : syracuseStep 21260717 = 7972769) B7972769
theorem B14173811 : Blo 2211435 14173811 := bstep (se 1 (by rfl) ⟨10630358, by rfl⟩ : syracuseStep 14173811 = 21260717) B21260717
theorem B9449207 : Blo 2211435 9449207 := bstep (se 1 (by rfl) ⟨7086905, by rfl⟩ : syracuseStep 9449207 = 14173811) B14173811
theorem B6299471 : Blo 2211435 6299471 := bstep (se 1 (by rfl) ⟨4724603, by rfl⟩ : syracuseStep 6299471 = 9449207) B9449207
theorem B16798589 : Blo 2211435 16798589 := bstep (se 3 (by rfl) ⟨3149735, by rfl⟩ : syracuseStep 16798589 = 6299471) B6299471
theorem B11199059 : Blo 2211435 11199059 := bstep (se 1 (by rfl) ⟨8399294, by rfl⟩ : syracuseStep 11199059 = 16798589) B16798589
theorem B7466039 : Blo 2211435 7466039 := bstep (se 1 (by rfl) ⟨5599529, by rfl⟩ : syracuseStep 7466039 = 11199059) B11199059
theorem B4977359 : Blo 2211435 4977359 := bstep (se 1 (by rfl) ⟨3733019, by rfl⟩ : syracuseStep 4977359 = 7466039) B7466039
theorem B3318239 : Blo 2211435 3318239 := bstep (se 1 (by rfl) ⟨2488679, by rfl⟩ : syracuseStep 3318239 = 4977359) B4977359
theorem B2212159 : Blo 2211435 2212159 := bstep (se 1 (by rfl) ⟨1659119, by rfl⟩ : syracuseStep 2212159 = 3318239) B3318239
theorem B3318245 : Blo 2211435 3318245 := bbase (se 4 (by rfl) ⟨311085, by rfl⟩ : syracuseStep 3318245 = 622171) (by norm_num)
theorem B2212163 : Blo 2211435 2212163 := bstep (se 1 (by rfl) ⟨1659122, by rfl⟩ : syracuseStep 2212163 = 3318245) B3318245
theorem B2394541 : Blo 2211435 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B3192721 : Blo 2211435 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B68111381 : Blo 2211435 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B181630349 : Blo 2211435 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B121086899 : Blo 2211435 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B80724599 : Blo 2211435 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B53816399 : Blo 2211435 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B35877599 : Blo 2211435 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B23918399 : Blo 2211435 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B15945599 : Blo 2211435 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B10630399 : Blo 2211435 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B14173865 : Blo 2211435 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B9449243 : Blo 2211435 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B6299495 : Blo 2211435 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B4199663 : Blo 2211435 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B2799775 : Blo 2211435 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B3733033 : Blo 2211435 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B4977377 : Blo 2211435 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B3318251 : Blo 2211435 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B2212167 : Blo 2211435 2212167 := bstep (se 1 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 2212167 = 3318251) B3318251
theorem B2488693 : Blo 2211435 2488693 := bbase (se 5 (by rfl) ⟨116657, by rfl⟩ : syracuseStep 2488693 = 233315) (by norm_num)
theorem B3318257 : Blo 2211435 3318257 := bstep (se 2 (by rfl) ⟨1244346, by rfl⟩ : syracuseStep 3318257 = 2488693) B2488693
theorem B2212171 : Blo 2211435 2212171 := bstep (se 1 (by rfl) ⟨1659128, by rfl⟩ : syracuseStep 2212171 = 3318257) B3318257
theorem B2799785 : Blo 2211435 2799785 := bbase (se 2 (by rfl) ⟨1049919, by rfl⟩ : syracuseStep 2799785 = 2099839) (by norm_num)
theorem B7466093 : Blo 2211435 7466093 := bstep (se 3 (by rfl) ⟨1399892, by rfl⟩ : syracuseStep 7466093 = 2799785) B2799785
theorem B4977395 : Blo 2211435 4977395 := bstep (se 1 (by rfl) ⟨3733046, by rfl⟩ : syracuseStep 4977395 = 7466093) B7466093
theorem B3318263 : Blo 2211435 3318263 := bstep (se 1 (by rfl) ⟨2488697, by rfl⟩ : syracuseStep 3318263 = 4977395) B4977395
theorem B2212175 : Blo 2211435 2212175 := bstep (se 1 (by rfl) ⟨1659131, by rfl⟩ : syracuseStep 2212175 = 3318263) B3318263
theorem B3318269 : Blo 2211435 3318269 := bbase (se 3 (by rfl) ⟨622175, by rfl⟩ : syracuseStep 3318269 = 1244351) (by norm_num)
theorem B2212179 : Blo 2211435 2212179 := bstep (se 1 (by rfl) ⟨1659134, by rfl⟩ : syracuseStep 2212179 = 3318269) B3318269
theorem B4977413 : Blo 2211435 4977413 := bbase (se 4 (by rfl) ⟨466632, by rfl⟩ : syracuseStep 4977413 = 933265) (by norm_num)
theorem B3318275 : Blo 2211435 3318275 := bstep (se 1 (by rfl) ⟨2488706, by rfl⟩ : syracuseStep 3318275 = 4977413) B4977413
theorem B2212183 : Blo 2211435 2212183 := bstep (se 1 (by rfl) ⟨1659137, by rfl⟩ : syracuseStep 2212183 = 3318275) B3318275
theorem B4199701 : Blo 2211435 4199701 := bbase (se 6 (by rfl) ⟨98430, by rfl⟩ : syracuseStep 4199701 = 196861) (by norm_num)
theorem B5599601 : Blo 2211435 5599601 := bstep (se 2 (by rfl) ⟨2099850, by rfl⟩ : syracuseStep 5599601 = 4199701) B4199701
theorem B3733067 : Blo 2211435 3733067 := bstep (se 1 (by rfl) ⟨2799800, by rfl⟩ : syracuseStep 3733067 = 5599601) B5599601
theorem B2488711 : Blo 2211435 2488711 := bstep (se 1 (by rfl) ⟨1866533, by rfl⟩ : syracuseStep 2488711 = 3733067) B3733067
theorem B3318281 : Blo 2211435 3318281 := bstep (se 2 (by rfl) ⟨1244355, by rfl⟩ : syracuseStep 3318281 = 2488711) B2488711
theorem B2212187 : Blo 2211435 2212187 := bstep (se 1 (by rfl) ⟨1659140, by rfl⟩ : syracuseStep 2212187 = 3318281) B3318281
theorem B11199221 : Blo 2211435 11199221 := bbase (se 5 (by rfl) ⟨524963, by rfl⟩ : syracuseStep 11199221 = 1049927) (by norm_num)
theorem B7466147 : Blo 2211435 7466147 := bstep (se 1 (by rfl) ⟨5599610, by rfl⟩ : syracuseStep 7466147 = 11199221) B11199221
theorem B4977431 : Blo 2211435 4977431 := bstep (se 1 (by rfl) ⟨3733073, by rfl⟩ : syracuseStep 4977431 = 7466147) B7466147
theorem B3318287 : Blo 2211435 3318287 := bstep (se 1 (by rfl) ⟨2488715, by rfl⟩ : syracuseStep 3318287 = 4977431) B4977431
theorem B2212191 : Blo 2211435 2212191 := bstep (se 1 (by rfl) ⟨1659143, by rfl⟩ : syracuseStep 2212191 = 3318287) B3318287
theorem B3318293 : Blo 2211435 3318293 := bbase (se 6 (by rfl) ⟨77772, by rfl⟩ : syracuseStep 3318293 = 155545) (by norm_num)
theorem B2212195 : Blo 2211435 2212195 := bstep (se 1 (by rfl) ⟨1659146, by rfl⟩ : syracuseStep 2212195 = 3318293) B3318293
theorem B3543517 : Blo 2211435 3543517 := bbase (se 3 (by rfl) ⟨664409, by rfl⟩ : syracuseStep 3543517 = 1328819) (by norm_num)
theorem B18898757 : Blo 2211435 18898757 := bstep (se 4 (by rfl) ⟨1771758, by rfl⟩ : syracuseStep 18898757 = 3543517) B3543517
theorem B12599171 : Blo 2211435 12599171 := bstep (se 1 (by rfl) ⟨9449378, by rfl⟩ : syracuseStep 12599171 = 18898757) B18898757
theorem B8399447 : Blo 2211435 8399447 := bstep (se 1 (by rfl) ⟨6299585, by rfl⟩ : syracuseStep 8399447 = 12599171) B12599171
theorem B5599631 : Blo 2211435 5599631 := bstep (se 1 (by rfl) ⟨4199723, by rfl⟩ : syracuseStep 5599631 = 8399447) B8399447
theorem B3733087 : Blo 2211435 3733087 := bstep (se 1 (by rfl) ⟨2799815, by rfl⟩ : syracuseStep 3733087 = 5599631) B5599631
theorem B4977449 : Blo 2211435 4977449 := bstep (se 2 (by rfl) ⟨1866543, by rfl⟩ : syracuseStep 4977449 = 3733087) B3733087
theorem B3318299 : Blo 2211435 3318299 := bstep (se 1 (by rfl) ⟨2488724, by rfl⟩ : syracuseStep 3318299 = 4977449) B4977449
theorem B2212199 : Blo 2211435 2212199 := bstep (se 1 (by rfl) ⟨1659149, by rfl⟩ : syracuseStep 2212199 = 3318299) B3318299
theorem B2488729 : Blo 2211435 2488729 := bbase (se 2 (by rfl) ⟨933273, by rfl⟩ : syracuseStep 2488729 = 1866547) (by norm_num)
theorem B3318305 : Blo 2211435 3318305 := bstep (se 2 (by rfl) ⟨1244364, by rfl⟩ : syracuseStep 3318305 = 2488729) B2488729
theorem B2212203 : Blo 2211435 2212203 := bstep (se 1 (by rfl) ⟨1659152, by rfl⟩ : syracuseStep 2212203 = 3318305) B3318305
theorem B8399477 : Blo 2211435 8399477 := bbase (se 5 (by rfl) ⟨393725, by rfl⟩ : syracuseStep 8399477 = 787451) (by norm_num)
theorem B5599651 : Blo 2211435 5599651 := bstep (se 1 (by rfl) ⟨4199738, by rfl⟩ : syracuseStep 5599651 = 8399477) B8399477
theorem B7466201 : Blo 2211435 7466201 := bstep (se 2 (by rfl) ⟨2799825, by rfl⟩ : syracuseStep 7466201 = 5599651) B5599651
theorem B4977467 : Blo 2211435 4977467 := bstep (se 1 (by rfl) ⟨3733100, by rfl⟩ : syracuseStep 4977467 = 7466201) B7466201
theorem B3318311 : Blo 2211435 3318311 := bstep (se 1 (by rfl) ⟨2488733, by rfl⟩ : syracuseStep 3318311 = 4977467) B4977467
theorem B2212207 : Blo 2211435 2212207 := bstep (se 1 (by rfl) ⟨1659155, by rfl⟩ : syracuseStep 2212207 = 3318311) B3318311
theorem B3318317 : Blo 2211435 3318317 := bbase (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) (by norm_num)
theorem B2212211 : Blo 2211435 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B4977485 : Blo 2211435 4977485 := bbase (se 3 (by rfl) ⟨933278, by rfl⟩ : syracuseStep 4977485 = 1866557) (by norm_num)
theorem B3318323 : Blo 2211435 3318323 := bstep (se 1 (by rfl) ⟨2488742, by rfl⟩ : syracuseStep 3318323 = 4977485) B4977485
theorem B2212215 : Blo 2211435 2212215 := bstep (se 1 (by rfl) ⟨1659161, by rfl⟩ : syracuseStep 2212215 = 3318323) B3318323
theorem B2799841 : Blo 2211435 2799841 := bbase (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) (by norm_num)
theorem B3733121 : Blo 2211435 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B2488747 : Blo 2211435 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B3318329 : Blo 2211435 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B2212219 : Blo 2211435 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B25198613 : Blo 2211435 25198613 := bbase (se 6 (by rfl) ⟨590592, by rfl⟩ : syracuseStep 25198613 = 1181185) (by norm_num)
theorem B16799075 : Blo 2211435 16799075 := bstep (se 1 (by rfl) ⟨12599306, by rfl⟩ : syracuseStep 16799075 = 25198613) B25198613
theorem B11199383 : Blo 2211435 11199383 := bstep (se 1 (by rfl) ⟨8399537, by rfl⟩ : syracuseStep 11199383 = 16799075) B16799075
theorem B7466255 : Blo 2211435 7466255 := bstep (se 1 (by rfl) ⟨5599691, by rfl⟩ : syracuseStep 7466255 = 11199383) B11199383
theorem B4977503 : Blo 2211435 4977503 := bstep (se 1 (by rfl) ⟨3733127, by rfl⟩ : syracuseStep 4977503 = 7466255) B7466255
theorem B3318335 : Blo 2211435 3318335 := bstep (se 1 (by rfl) ⟨2488751, by rfl⟩ : syracuseStep 3318335 = 4977503) B4977503
theorem B2212223 : Blo 2211435 2212223 := bstep (se 1 (by rfl) ⟨1659167, by rfl⟩ : syracuseStep 2212223 = 3318335) B3318335
theorem B3318341 : Blo 2211435 3318341 := bbase (se 4 (by rfl) ⟨311094, by rfl⟩ : syracuseStep 3318341 = 622189) (by norm_num)
theorem B2212227 : Blo 2211435 2212227 := bstep (se 1 (by rfl) ⟨1659170, by rfl⟩ : syracuseStep 2212227 = 3318341) B3318341
theorem B3733141 : Blo 2211435 3733141 := bbase (se 6 (by rfl) ⟨87495, by rfl⟩ : syracuseStep 3733141 = 174991) (by norm_num)
theorem B4977521 : Blo 2211435 4977521 := bstep (se 2 (by rfl) ⟨1866570, by rfl⟩ : syracuseStep 4977521 = 3733141) B3733141
theorem B3318347 : Blo 2211435 3318347 := bstep (se 1 (by rfl) ⟨2488760, by rfl⟩ : syracuseStep 3318347 = 4977521) B4977521
theorem B2212231 : Blo 2211435 2212231 := bstep (se 1 (by rfl) ⟨1659173, by rfl⟩ : syracuseStep 2212231 = 3318347) B3318347
theorem B2488765 : Blo 2211435 2488765 := bbase (se 3 (by rfl) ⟨466643, by rfl⟩ : syracuseStep 2488765 = 933287) (by norm_num)
theorem B3318353 : Blo 2211435 3318353 := bstep (se 2 (by rfl) ⟨1244382, by rfl⟩ : syracuseStep 3318353 = 2488765) B2488765
theorem B2212235 : Blo 2211435 2212235 := bstep (se 1 (by rfl) ⟨1659176, by rfl⟩ : syracuseStep 2212235 = 3318353) B3318353
theorem B7466309 : Blo 2211435 7466309 := bbase (se 4 (by rfl) ⟨699966, by rfl⟩ : syracuseStep 7466309 = 1399933) (by norm_num)
theorem B4977539 : Blo 2211435 4977539 := bstep (se 1 (by rfl) ⟨3733154, by rfl⟩ : syracuseStep 4977539 = 7466309) B7466309
theorem B3318359 : Blo 2211435 3318359 := bstep (se 1 (by rfl) ⟨2488769, by rfl⟩ : syracuseStep 3318359 = 4977539) B4977539
theorem B2212239 : Blo 2211435 2212239 := bstep (se 1 (by rfl) ⟨1659179, by rfl⟩ : syracuseStep 2212239 = 3318359) B3318359
theorem B3318365 : Blo 2211435 3318365 := bbase (se 3 (by rfl) ⟨622193, by rfl⟩ : syracuseStep 3318365 = 1244387) (by norm_num)
theorem B2212243 : Blo 2211435 2212243 := bstep (se 1 (by rfl) ⟨1659182, by rfl⟩ : syracuseStep 2212243 = 3318365) B3318365
theorem B4977557 : Blo 2211435 4977557 := bbase (se 6 (by rfl) ⟨116661, by rfl⟩ : syracuseStep 4977557 = 233323) (by norm_num)
theorem B3318371 : Blo 2211435 3318371 := bstep (se 1 (by rfl) ⟨2488778, by rfl⟩ : syracuseStep 3318371 = 4977557) B4977557
theorem B2212247 : Blo 2211435 2212247 := bstep (se 1 (by rfl) ⟨1659185, by rfl⟩ : syracuseStep 2212247 = 3318371) B3318371
theorem B2657701 : Blo 2211435 2657701 := bbase (se 4 (by rfl) ⟨249159, by rfl⟩ : syracuseStep 2657701 = 498319) (by norm_num)
theorem B3543601 : Blo 2211435 3543601 := bstep (se 2 (by rfl) ⟨1328850, by rfl⟩ : syracuseStep 3543601 = 2657701) B2657701
theorem B4724801 : Blo 2211435 4724801 := bstep (se 2 (by rfl) ⟨1771800, by rfl⟩ : syracuseStep 4724801 = 3543601) B3543601
theorem B3149867 : Blo 2211435 3149867 := bstep (se 1 (by rfl) ⟨2362400, by rfl⟩ : syracuseStep 3149867 = 4724801) B4724801
theorem B8399645 : Blo 2211435 8399645 := bstep (se 3 (by rfl) ⟨1574933, by rfl⟩ : syracuseStep 8399645 = 3149867) B3149867
theorem B5599763 : Blo 2211435 5599763 := bstep (se 1 (by rfl) ⟨4199822, by rfl⟩ : syracuseStep 5599763 = 8399645) B8399645
theorem B3733175 : Blo 2211435 3733175 := bstep (se 1 (by rfl) ⟨2799881, by rfl⟩ : syracuseStep 3733175 = 5599763) B5599763
theorem B2488783 : Blo 2211435 2488783 := bstep (se 1 (by rfl) ⟨1866587, by rfl⟩ : syracuseStep 2488783 = 3733175) B3733175
theorem B3318377 : Blo 2211435 3318377 := bstep (se 2 (by rfl) ⟨1244391, by rfl⟩ : syracuseStep 3318377 = 2488783) B2488783
theorem B2212251 : Blo 2211435 2212251 := bstep (se 1 (by rfl) ⟨1659188, by rfl⟩ : syracuseStep 2212251 = 3318377) B3318377
theorem B2657705 : Blo 2211435 2657705 := bbase (se 2 (by rfl) ⟨996639, by rfl⟩ : syracuseStep 2657705 = 1993279) (by norm_num)
theorem B7087213 : Blo 2211435 7087213 := bstep (se 3 (by rfl) ⟨1328852, by rfl⟩ : syracuseStep 7087213 = 2657705) B2657705
theorem B9449617 : Blo 2211435 9449617 := bstep (se 2 (by rfl) ⟨3543606, by rfl⟩ : syracuseStep 9449617 = 7087213) B7087213
theorem B12599489 : Blo 2211435 12599489 := bstep (se 2 (by rfl) ⟨4724808, by rfl⟩ : syracuseStep 12599489 = 9449617) B9449617
theorem B8399659 : Blo 2211435 8399659 := bstep (se 1 (by rfl) ⟨6299744, by rfl⟩ : syracuseStep 8399659 = 12599489) B12599489
theorem B11199545 : Blo 2211435 11199545 := bstep (se 2 (by rfl) ⟨4199829, by rfl⟩ : syracuseStep 11199545 = 8399659) B8399659
theorem B7466363 : Blo 2211435 7466363 := bstep (se 1 (by rfl) ⟨5599772, by rfl⟩ : syracuseStep 7466363 = 11199545) B11199545
theorem B4977575 : Blo 2211435 4977575 := bstep (se 1 (by rfl) ⟨3733181, by rfl⟩ : syracuseStep 4977575 = 7466363) B7466363
theorem B3318383 : Blo 2211435 3318383 := bstep (se 1 (by rfl) ⟨2488787, by rfl⟩ : syracuseStep 3318383 = 4977575) B4977575
theorem B2212255 : Blo 2211435 2212255 := bstep (se 1 (by rfl) ⟨1659191, by rfl⟩ : syracuseStep 2212255 = 3318383) B3318383
theorem B3318389 : Blo 2211435 3318389 := bbase (se 5 (by rfl) ⟨155549, by rfl⟩ : syracuseStep 3318389 = 311099) (by norm_num)
theorem B2212259 : Blo 2211435 2212259 := bstep (se 1 (by rfl) ⟨1659194, by rfl⟩ : syracuseStep 2212259 = 3318389) B3318389
theorem B4199845 : Blo 2211435 4199845 := bbase (se 4 (by rfl) ⟨393735, by rfl⟩ : syracuseStep 4199845 = 787471) (by norm_num)
theorem B5599793 : Blo 2211435 5599793 := bstep (se 2 (by rfl) ⟨2099922, by rfl⟩ : syracuseStep 5599793 = 4199845) B4199845
theorem B3733195 : Blo 2211435 3733195 := bstep (se 1 (by rfl) ⟨2799896, by rfl⟩ : syracuseStep 3733195 = 5599793) B5599793
theorem B4977593 : Blo 2211435 4977593 := bstep (se 2 (by rfl) ⟨1866597, by rfl⟩ : syracuseStep 4977593 = 3733195) B3733195
theorem B3318395 : Blo 2211435 3318395 := bstep (se 1 (by rfl) ⟨2488796, by rfl⟩ : syracuseStep 3318395 = 4977593) B4977593
theorem B2212263 : Blo 2211435 2212263 := bstep (se 1 (by rfl) ⟨1659197, by rfl⟩ : syracuseStep 2212263 = 3318395) B3318395
theorem B2488801 : Blo 2211435 2488801 := bbase (se 2 (by rfl) ⟨933300, by rfl⟩ : syracuseStep 2488801 = 1866601) (by norm_num)
theorem B3318401 : Blo 2211435 3318401 := bstep (se 2 (by rfl) ⟨1244400, by rfl⟩ : syracuseStep 3318401 = 2488801) B2488801
theorem B2212267 : Blo 2211435 2212267 := bstep (se 1 (by rfl) ⟨1659200, by rfl⟩ : syracuseStep 2212267 = 3318401) B3318401
theorem B5599813 : Blo 2211435 5599813 := bbase (se 4 (by rfl) ⟨524982, by rfl⟩ : syracuseStep 5599813 = 1049965) (by norm_num)
theorem B7466417 : Blo 2211435 7466417 := bstep (se 2 (by rfl) ⟨2799906, by rfl⟩ : syracuseStep 7466417 = 5599813) B5599813
theorem B4977611 : Blo 2211435 4977611 := bstep (se 1 (by rfl) ⟨3733208, by rfl⟩ : syracuseStep 4977611 = 7466417) B7466417
theorem B3318407 : Blo 2211435 3318407 := bstep (se 1 (by rfl) ⟨2488805, by rfl⟩ : syracuseStep 3318407 = 4977611) B4977611
theorem B2212271 : Blo 2211435 2212271 := bstep (se 1 (by rfl) ⟨1659203, by rfl⟩ : syracuseStep 2212271 = 3318407) B3318407
theorem B3318413 : Blo 2211435 3318413 := bbase (se 3 (by rfl) ⟨622202, by rfl⟩ : syracuseStep 3318413 = 1244405) (by norm_num)
theorem B2212275 : Blo 2211435 2212275 := bstep (se 1 (by rfl) ⟨1659206, by rfl⟩ : syracuseStep 2212275 = 3318413) B3318413
theorem B4977629 : Blo 2211435 4977629 := bbase (se 3 (by rfl) ⟨933305, by rfl⟩ : syracuseStep 4977629 = 1866611) (by norm_num)
theorem B3318419 : Blo 2211435 3318419 := bstep (se 1 (by rfl) ⟨2488814, by rfl⟩ : syracuseStep 3318419 = 4977629) B4977629
theorem B2212279 : Blo 2211435 2212279 := bstep (se 1 (by rfl) ⟨1659209, by rfl⟩ : syracuseStep 2212279 = 3318419) B3318419
theorem B3733229 : Blo 2211435 3733229 := bbase (se 3 (by rfl) ⟨699980, by rfl⟩ : syracuseStep 3733229 = 1399961) (by norm_num)
theorem B2488819 : Blo 2211435 2488819 := bstep (se 1 (by rfl) ⟨1866614, by rfl⟩ : syracuseStep 2488819 = 3733229) B3733229
theorem B3318425 : Blo 2211435 3318425 := bstep (se 2 (by rfl) ⟨1244409, by rfl⟩ : syracuseStep 3318425 = 2488819) B2488819
theorem B2212283 : Blo 2211435 2212283 := bstep (se 1 (by rfl) ⟨1659212, by rfl⟩ : syracuseStep 2212283 = 3318425) B3318425
theorem B10228805 : Blo 2211435 10228805 := bbase (se 4 (by rfl) ⟨958950, by rfl⟩ : syracuseStep 10228805 = 1917901) (by norm_num)
theorem B6819203 : Blo 2211435 6819203 := bstep (se 1 (by rfl) ⟨5114402, by rfl⟩ : syracuseStep 6819203 = 10228805) B10228805
theorem B4546135 : Blo 2211435 4546135 := bstep (se 1 (by rfl) ⟨3409601, by rfl⟩ : syracuseStep 4546135 = 6819203) B6819203
theorem B24246053 : Blo 2211435 24246053 := bstep (se 4 (by rfl) ⟨2273067, by rfl⟩ : syracuseStep 24246053 = 4546135) B4546135
theorem B16164035 : Blo 2211435 16164035 := bstep (se 1 (by rfl) ⟨12123026, by rfl⟩ : syracuseStep 16164035 = 24246053) B24246053
theorem B10776023 : Blo 2211435 10776023 := bstep (se 1 (by rfl) ⟨8082017, by rfl⟩ : syracuseStep 10776023 = 16164035) B16164035
theorem B7184015 : Blo 2211435 7184015 := bstep (se 1 (by rfl) ⟨5388011, by rfl⟩ : syracuseStep 7184015 = 10776023) B10776023
theorem B4789343 : Blo 2211435 4789343 := bstep (se 1 (by rfl) ⟨3592007, by rfl⟩ : syracuseStep 4789343 = 7184015) B7184015
theorem B3192895 : Blo 2211435 3192895 := bstep (se 1 (by rfl) ⟨2394671, by rfl⟩ : syracuseStep 3192895 = 4789343) B4789343
theorem B4257193 : Blo 2211435 4257193 := bstep (se 2 (by rfl) ⟨1596447, by rfl⟩ : syracuseStep 4257193 = 3192895) B3192895
theorem B5676257 : Blo 2211435 5676257 := bstep (se 2 (by rfl) ⟨2128596, by rfl⟩ : syracuseStep 5676257 = 4257193) B4257193
theorem B3784171 : Blo 2211435 3784171 := bstep (se 1 (by rfl) ⟨2838128, by rfl⟩ : syracuseStep 3784171 = 5676257) B5676257
theorem B5045561 : Blo 2211435 5045561 := bstep (se 2 (by rfl) ⟨1892085, by rfl⟩ : syracuseStep 5045561 = 3784171) B3784171
theorem B3363707 : Blo 2211435 3363707 := bstep (se 1 (by rfl) ⟨2522780, by rfl⟩ : syracuseStep 3363707 = 5045561) B5045561
theorem B8969885 : Blo 2211435 8969885 := bstep (se 3 (by rfl) ⟨1681853, by rfl⟩ : syracuseStep 8969885 = 3363707) B3363707
theorem B5979923 : Blo 2211435 5979923 := bstep (se 1 (by rfl) ⟨4484942, by rfl⟩ : syracuseStep 5979923 = 8969885) B8969885
theorem B3986615 : Blo 2211435 3986615 := bstep (se 1 (by rfl) ⟨2989961, by rfl⟩ : syracuseStep 3986615 = 5979923) B5979923
theorem B10630973 : Blo 2211435 10630973 := bstep (se 3 (by rfl) ⟨1993307, by rfl⟩ : syracuseStep 10630973 = 3986615) B3986615
theorem B28349261 : Blo 2211435 28349261 := bstep (se 3 (by rfl) ⟨5315486, by rfl⟩ : syracuseStep 28349261 = 10630973) B10630973
theorem B18899507 : Blo 2211435 18899507 := bstep (se 1 (by rfl) ⟨14174630, by rfl⟩ : syracuseStep 18899507 = 28349261) B28349261
theorem B12599671 : Blo 2211435 12599671 := bstep (se 1 (by rfl) ⟨9449753, by rfl⟩ : syracuseStep 12599671 = 18899507) B18899507
theorem B16799561 : Blo 2211435 16799561 := bstep (se 2 (by rfl) ⟨6299835, by rfl⟩ : syracuseStep 16799561 = 12599671) B12599671
theorem B11199707 : Blo 2211435 11199707 := bstep (se 1 (by rfl) ⟨8399780, by rfl⟩ : syracuseStep 11199707 = 16799561) B16799561
theorem B7466471 : Blo 2211435 7466471 := bstep (se 1 (by rfl) ⟨5599853, by rfl⟩ : syracuseStep 7466471 = 11199707) B11199707
theorem B4977647 : Blo 2211435 4977647 := bstep (se 1 (by rfl) ⟨3733235, by rfl⟩ : syracuseStep 4977647 = 7466471) B7466471
theorem B3318431 : Blo 2211435 3318431 := bstep (se 1 (by rfl) ⟨2488823, by rfl⟩ : syracuseStep 3318431 = 4977647) B4977647
theorem B2212287 : Blo 2211435 2212287 := bstep (se 1 (by rfl) ⟨1659215, by rfl⟩ : syracuseStep 2212287 = 3318431) B3318431
theorem B3318437 : Blo 2211435 3318437 := bbase (se 4 (by rfl) ⟨311103, by rfl⟩ : syracuseStep 3318437 = 622207) (by norm_num)
theorem B2212291 : Blo 2211435 2212291 := bstep (se 1 (by rfl) ⟨1659218, by rfl⟩ : syracuseStep 2212291 = 3318437) B3318437
theorem B2799937 : Blo 2211435 2799937 := bbase (se 2 (by rfl) ⟨1049976, by rfl⟩ : syracuseStep 2799937 = 2099953) (by norm_num)
theorem B3733249 : Blo 2211435 3733249 := bstep (se 2 (by rfl) ⟨1399968, by rfl⟩ : syracuseStep 3733249 = 2799937) B2799937
theorem B4977665 : Blo 2211435 4977665 := bstep (se 2 (by rfl) ⟨1866624, by rfl⟩ : syracuseStep 4977665 = 3733249) B3733249
theorem B3318443 : Blo 2211435 3318443 := bstep (se 1 (by rfl) ⟨2488832, by rfl⟩ : syracuseStep 3318443 = 4977665) B4977665
theorem B2212295 : Blo 2211435 2212295 := bstep (se 1 (by rfl) ⟨1659221, by rfl⟩ : syracuseStep 2212295 = 3318443) B3318443
theorem B2488837 : Blo 2211435 2488837 := bbase (se 4 (by rfl) ⟨233328, by rfl⟩ : syracuseStep 2488837 = 466657) (by norm_num)
theorem B3318449 : Blo 2211435 3318449 := bstep (se 2 (by rfl) ⟨1244418, by rfl⟩ : syracuseStep 3318449 = 2488837) B2488837
theorem B2212299 : Blo 2211435 2212299 := bstep (se 1 (by rfl) ⟨1659224, by rfl⟩ : syracuseStep 2212299 = 3318449) B3318449
theorem B3149941 : Blo 2211435 3149941 := bbase (se 5 (by rfl) ⟨147653, by rfl⟩ : syracuseStep 3149941 = 295307) (by norm_num)
theorem B4199921 : Blo 2211435 4199921 := bstep (se 2 (by rfl) ⟨1574970, by rfl⟩ : syracuseStep 4199921 = 3149941) B3149941
theorem B2799947 : Blo 2211435 2799947 := bstep (se 1 (by rfl) ⟨2099960, by rfl⟩ : syracuseStep 2799947 = 4199921) B4199921
theorem B7466525 : Blo 2211435 7466525 := bstep (se 3 (by rfl) ⟨1399973, by rfl⟩ : syracuseStep 7466525 = 2799947) B2799947
theorem B4977683 : Blo 2211435 4977683 := bstep (se 1 (by rfl) ⟨3733262, by rfl⟩ : syracuseStep 4977683 = 7466525) B7466525
theorem B3318455 : Blo 2211435 3318455 := bstep (se 1 (by rfl) ⟨2488841, by rfl⟩ : syracuseStep 3318455 = 4977683) B4977683
theorem B2212303 : Blo 2211435 2212303 := bstep (se 1 (by rfl) ⟨1659227, by rfl⟩ : syracuseStep 2212303 = 3318455) B3318455
theorem B3318461 : Blo 2211435 3318461 := bbase (se 3 (by rfl) ⟨622211, by rfl⟩ : syracuseStep 3318461 = 1244423) (by norm_num)
theorem B2212307 : Blo 2211435 2212307 := bstep (se 1 (by rfl) ⟨1659230, by rfl⟩ : syracuseStep 2212307 = 3318461) B3318461
theorem B4977701 : Blo 2211435 4977701 := bbase (se 4 (by rfl) ⟨466659, by rfl⟩ : syracuseStep 4977701 = 933319) (by norm_num)
theorem B3318467 : Blo 2211435 3318467 := bstep (se 1 (by rfl) ⟨2488850, by rfl⟩ : syracuseStep 3318467 = 4977701) B4977701
theorem B2212311 : Blo 2211435 2212311 := bstep (se 1 (by rfl) ⟨1659233, by rfl⟩ : syracuseStep 2212311 = 3318467) B3318467
theorem B5599925 : Blo 2211435 5599925 := bbase (se 5 (by rfl) ⟨262496, by rfl⟩ : syracuseStep 5599925 = 524993) (by norm_num)
theorem B3733283 : Blo 2211435 3733283 := bstep (se 1 (by rfl) ⟨2799962, by rfl⟩ : syracuseStep 3733283 = 5599925) B5599925
theorem B2488855 : Blo 2211435 2488855 := bstep (se 1 (by rfl) ⟨1866641, by rfl⟩ : syracuseStep 2488855 = 3733283) B3733283
theorem B3318473 : Blo 2211435 3318473 := bstep (se 2 (by rfl) ⟨1244427, by rfl⟩ : syracuseStep 3318473 = 2488855) B2488855
theorem B2212315 : Blo 2211435 2212315 := bstep (se 1 (by rfl) ⟨1659236, by rfl⟩ : syracuseStep 2212315 = 3318473) B3318473
theorem B14174837 : Blo 2211435 14174837 := bbase (se 5 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 14174837 = 1328891) (by norm_num)
theorem B9449891 : Blo 2211435 9449891 := bstep (se 1 (by rfl) ⟨7087418, by rfl⟩ : syracuseStep 9449891 = 14174837) B14174837
theorem B6299927 : Blo 2211435 6299927 := bstep (se 1 (by rfl) ⟨4724945, by rfl⟩ : syracuseStep 6299927 = 9449891) B9449891
theorem B4199951 : Blo 2211435 4199951 := bstep (se 1 (by rfl) ⟨3149963, by rfl⟩ : syracuseStep 4199951 = 6299927) B6299927
theorem B11199869 : Blo 2211435 11199869 := bstep (se 3 (by rfl) ⟨2099975, by rfl⟩ : syracuseStep 11199869 = 4199951) B4199951
theorem B7466579 : Blo 2211435 7466579 := bstep (se 1 (by rfl) ⟨5599934, by rfl⟩ : syracuseStep 7466579 = 11199869) B11199869
theorem B4977719 : Blo 2211435 4977719 := bstep (se 1 (by rfl) ⟨3733289, by rfl⟩ : syracuseStep 4977719 = 7466579) B7466579
theorem B3318479 : Blo 2211435 3318479 := bstep (se 1 (by rfl) ⟨2488859, by rfl⟩ : syracuseStep 3318479 = 4977719) B4977719
theorem B2212319 : Blo 2211435 2212319 := bstep (se 1 (by rfl) ⟨1659239, by rfl⟩ : syracuseStep 2212319 = 3318479) B3318479
theorem B3318485 : Blo 2211435 3318485 := bbase (se 7 (by rfl) ⟨38888, by rfl⟩ : syracuseStep 3318485 = 77777) (by norm_num)
theorem B2212323 : Blo 2211435 2212323 := bstep (se 1 (by rfl) ⟨1659242, by rfl⟩ : syracuseStep 2212323 = 3318485) B3318485
theorem B7087445 : Blo 2211435 7087445 := bbase (se 12 (by rfl) ⟨2595, by rfl⟩ : syracuseStep 7087445 = 5191) (by norm_num)
theorem B4724963 : Blo 2211435 4724963 := bstep (se 1 (by rfl) ⟨3543722, by rfl⟩ : syracuseStep 4724963 = 7087445) B7087445
theorem B3149975 : Blo 2211435 3149975 := bstep (se 1 (by rfl) ⟨2362481, by rfl⟩ : syracuseStep 3149975 = 4724963) B4724963
theorem B8399933 : Blo 2211435 8399933 := bstep (se 3 (by rfl) ⟨1574987, by rfl⟩ : syracuseStep 8399933 = 3149975) B3149975
theorem B5599955 : Blo 2211435 5599955 := bstep (se 1 (by rfl) ⟨4199966, by rfl⟩ : syracuseStep 5599955 = 8399933) B8399933
theorem B3733303 : Blo 2211435 3733303 := bstep (se 1 (by rfl) ⟨2799977, by rfl⟩ : syracuseStep 3733303 = 5599955) B5599955
theorem B4977737 : Blo 2211435 4977737 := bstep (se 2 (by rfl) ⟨1866651, by rfl⟩ : syracuseStep 4977737 = 3733303) B3733303
theorem B3318491 : Blo 2211435 3318491 := bstep (se 1 (by rfl) ⟨2488868, by rfl⟩ : syracuseStep 3318491 = 4977737) B4977737
theorem B2212327 : Blo 2211435 2212327 := bstep (se 1 (by rfl) ⟨1659245, by rfl⟩ : syracuseStep 2212327 = 3318491) B3318491
theorem B2488873 : Blo 2211435 2488873 := bbase (se 2 (by rfl) ⟨933327, by rfl⟩ : syracuseStep 2488873 = 1866655) (by norm_num)
theorem B3318497 : Blo 2211435 3318497 := bstep (se 2 (by rfl) ⟨1244436, by rfl⟩ : syracuseStep 3318497 = 2488873) B2488873
theorem B2212331 : Blo 2211435 2212331 := bstep (se 1 (by rfl) ⟨1659248, by rfl⟩ : syracuseStep 2212331 = 3318497) B3318497
theorem B45411029 : Blo 2211435 45411029 := bbase (se 7 (by rfl) ⟨532160, by rfl⟩ : syracuseStep 45411029 = 1064321) (by norm_num)
theorem B30274019 : Blo 2211435 30274019 := bstep (se 1 (by rfl) ⟨22705514, by rfl⟩ : syracuseStep 30274019 = 45411029) B45411029
theorem B20182679 : Blo 2211435 20182679 := bstep (se 1 (by rfl) ⟨15137009, by rfl⟩ : syracuseStep 20182679 = 30274019) B30274019
theorem B13455119 : Blo 2211435 13455119 := bstep (se 1 (by rfl) ⟨10091339, by rfl⟩ : syracuseStep 13455119 = 20182679) B20182679
theorem B35880317 : Blo 2211435 35880317 := bstep (se 3 (by rfl) ⟨6727559, by rfl⟩ : syracuseStep 35880317 = 13455119) B13455119
theorem B23920211 : Blo 2211435 23920211 := bstep (se 1 (by rfl) ⟨17940158, by rfl⟩ : syracuseStep 23920211 = 35880317) B35880317
theorem B15946807 : Blo 2211435 15946807 := bstep (se 1 (by rfl) ⟨11960105, by rfl⟩ : syracuseStep 15946807 = 23920211) B23920211
theorem B21262409 : Blo 2211435 21262409 := bstep (se 2 (by rfl) ⟨7973403, by rfl⟩ : syracuseStep 21262409 = 15946807) B15946807
theorem B14174939 : Blo 2211435 14174939 := bstep (se 1 (by rfl) ⟨10631204, by rfl⟩ : syracuseStep 14174939 = 21262409) B21262409
theorem B9449959 : Blo 2211435 9449959 := bstep (se 1 (by rfl) ⟨7087469, by rfl⟩ : syracuseStep 9449959 = 14174939) B14174939
theorem B12599945 : Blo 2211435 12599945 := bstep (se 2 (by rfl) ⟨4724979, by rfl⟩ : syracuseStep 12599945 = 9449959) B9449959
theorem B8399963 : Blo 2211435 8399963 := bstep (se 1 (by rfl) ⟨6299972, by rfl⟩ : syracuseStep 8399963 = 12599945) B12599945
theorem B5599975 : Blo 2211435 5599975 := bstep (se 1 (by rfl) ⟨4199981, by rfl⟩ : syracuseStep 5599975 = 8399963) B8399963
theorem B7466633 : Blo 2211435 7466633 := bstep (se 2 (by rfl) ⟨2799987, by rfl⟩ : syracuseStep 7466633 = 5599975) B5599975
theorem B4977755 : Blo 2211435 4977755 := bstep (se 1 (by rfl) ⟨3733316, by rfl⟩ : syracuseStep 4977755 = 7466633) B7466633
theorem B3318503 : Blo 2211435 3318503 := bstep (se 1 (by rfl) ⟨2488877, by rfl⟩ : syracuseStep 3318503 = 4977755) B4977755
theorem B2212335 : Blo 2211435 2212335 := bstep (se 1 (by rfl) ⟨1659251, by rfl⟩ : syracuseStep 2212335 = 3318503) B3318503
theorem B3318509 : Blo 2211435 3318509 := bbase (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) (by norm_num)
theorem B2212339 : Blo 2211435 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B4977773 : Blo 2211435 4977773 := bbase (se 3 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 4977773 = 1866665) (by norm_num)
theorem B3318515 : Blo 2211435 3318515 := bstep (se 1 (by rfl) ⟨2488886, by rfl⟩ : syracuseStep 3318515 = 4977773) B4977773
theorem B2212343 : Blo 2211435 2212343 := bstep (se 1 (by rfl) ⟨1659257, by rfl⟩ : syracuseStep 2212343 = 3318515) B3318515
theorem B4200005 : Blo 2211435 4200005 := bbase (se 4 (by rfl) ⟨393750, by rfl⟩ : syracuseStep 4200005 = 787501) (by norm_num)
theorem B2800003 : Blo 2211435 2800003 := bstep (se 1 (by rfl) ⟨2100002, by rfl⟩ : syracuseStep 2800003 = 4200005) B4200005
theorem B3733337 : Blo 2211435 3733337 := bstep (se 2 (by rfl) ⟨1400001, by rfl⟩ : syracuseStep 3733337 = 2800003) B2800003
theorem B2488891 : Blo 2211435 2488891 := bstep (se 1 (by rfl) ⟨1866668, by rfl⟩ : syracuseStep 2488891 = 3733337) B3733337
theorem B3318521 : Blo 2211435 3318521 := bstep (se 2 (by rfl) ⟨1244445, by rfl⟩ : syracuseStep 3318521 = 2488891) B2488891
theorem B2212347 : Blo 2211435 2212347 := bstep (se 1 (by rfl) ⟨1659260, by rfl⟩ : syracuseStep 2212347 = 3318521) B3318521
theorem B10229093 : Blo 2211435 10229093 := bbase (se 4 (by rfl) ⟨958977, by rfl⟩ : syracuseStep 10229093 = 1917955) (by norm_num)
theorem B6819395 : Blo 2211435 6819395 := bstep (se 1 (by rfl) ⟨5114546, by rfl⟩ : syracuseStep 6819395 = 10229093) B10229093
theorem B72740213 : Blo 2211435 72740213 := bstep (se 5 (by rfl) ⟨3409697, by rfl⟩ : syracuseStep 72740213 = 6819395) B6819395
theorem B48493475 : Blo 2211435 48493475 := bstep (se 1 (by rfl) ⟨36370106, by rfl⟩ : syracuseStep 48493475 = 72740213) B72740213
theorem B32328983 : Blo 2211435 32328983 := bstep (se 1 (by rfl) ⟨24246737, by rfl⟩ : syracuseStep 32328983 = 48493475) B48493475
theorem B21552655 : Blo 2211435 21552655 := bstep (se 1 (by rfl) ⟨16164491, by rfl⟩ : syracuseStep 21552655 = 32328983) B32328983
theorem B28736873 : Blo 2211435 28736873 := bstep (se 2 (by rfl) ⟨10776327, by rfl⟩ : syracuseStep 28736873 = 21552655) B21552655
theorem B19157915 : Blo 2211435 19157915 := bstep (se 1 (by rfl) ⟨14368436, by rfl⟩ : syracuseStep 19157915 = 28736873) B28736873
theorem B51087773 : Blo 2211435 51087773 := bstep (se 3 (by rfl) ⟨9578957, by rfl⟩ : syracuseStep 51087773 = 19157915) B19157915
theorem B34058515 : Blo 2211435 34058515 := bstep (se 1 (by rfl) ⟨25543886, by rfl⟩ : syracuseStep 34058515 = 51087773) B51087773
theorem B45411353 : Blo 2211435 45411353 := bstep (se 2 (by rfl) ⟨17029257, by rfl⟩ : syracuseStep 45411353 = 34058515) B34058515
theorem B30274235 : Blo 2211435 30274235 := bstep (se 1 (by rfl) ⟨22705676, by rfl⟩ : syracuseStep 30274235 = 45411353) B45411353
theorem B20182823 : Blo 2211435 20182823 := bstep (se 1 (by rfl) ⟨15137117, by rfl⟩ : syracuseStep 20182823 = 30274235) B30274235
theorem B13455215 : Blo 2211435 13455215 := bstep (se 1 (by rfl) ⟨10091411, by rfl⟩ : syracuseStep 13455215 = 20182823) B20182823
theorem B8970143 : Blo 2211435 8970143 := bstep (se 1 (by rfl) ⟨6727607, by rfl⟩ : syracuseStep 8970143 = 13455215) B13455215
theorem B23920381 : Blo 2211435 23920381 := bstep (se 3 (by rfl) ⟨4485071, by rfl⟩ : syracuseStep 23920381 = 8970143) B8970143
theorem B31893841 : Blo 2211435 31893841 := bstep (se 2 (by rfl) ⟨11960190, by rfl⟩ : syracuseStep 31893841 = 23920381) B23920381
theorem B42525121 : Blo 2211435 42525121 := bstep (se 2 (by rfl) ⟨15946920, by rfl⟩ : syracuseStep 42525121 = 31893841) B31893841
theorem B56700161 : Blo 2211435 56700161 := bstep (se 2 (by rfl) ⟨21262560, by rfl⟩ : syracuseStep 56700161 = 42525121) B42525121
theorem B37800107 : Blo 2211435 37800107 := bstep (se 1 (by rfl) ⟨28350080, by rfl⟩ : syracuseStep 37800107 = 56700161) B56700161
theorem B25200071 : Blo 2211435 25200071 := bstep (se 1 (by rfl) ⟨18900053, by rfl⟩ : syracuseStep 25200071 = 37800107) B37800107
theorem B16800047 : Blo 2211435 16800047 := bstep (se 1 (by rfl) ⟨12600035, by rfl⟩ : syracuseStep 16800047 = 25200071) B25200071
theorem B11200031 : Blo 2211435 11200031 := bstep (se 1 (by rfl) ⟨8400023, by rfl⟩ : syracuseStep 11200031 = 16800047) B16800047
theorem B7466687 : Blo 2211435 7466687 := bstep (se 1 (by rfl) ⟨5600015, by rfl⟩ : syracuseStep 7466687 = 11200031) B11200031
theorem B4977791 : Blo 2211435 4977791 := bstep (se 1 (by rfl) ⟨3733343, by rfl⟩ : syracuseStep 4977791 = 7466687) B7466687
theorem B3318527 : Blo 2211435 3318527 := bstep (se 1 (by rfl) ⟨2488895, by rfl⟩ : syracuseStep 3318527 = 4977791) B4977791
theorem B2212351 : Blo 2211435 2212351 := bstep (se 1 (by rfl) ⟨1659263, by rfl⟩ : syracuseStep 2212351 = 3318527) B3318527
theorem B3318533 : Blo 2211435 3318533 := bbase (se 4 (by rfl) ⟨311112, by rfl⟩ : syracuseStep 3318533 = 622225) (by norm_num)
theorem B2212355 : Blo 2211435 2212355 := bstep (se 1 (by rfl) ⟨1659266, by rfl⟩ : syracuseStep 2212355 = 3318533) B3318533
theorem B3733357 : Blo 2211435 3733357 := bbase (se 3 (by rfl) ⟨700004, by rfl⟩ : syracuseStep 3733357 = 1400009) (by norm_num)
theorem B4977809 : Blo 2211435 4977809 := bstep (se 2 (by rfl) ⟨1866678, by rfl⟩ : syracuseStep 4977809 = 3733357) B3733357
theorem B3318539 : Blo 2211435 3318539 := bstep (se 1 (by rfl) ⟨2488904, by rfl⟩ : syracuseStep 3318539 = 4977809) B4977809
theorem B2212359 : Blo 2211435 2212359 := bstep (se 1 (by rfl) ⟨1659269, by rfl⟩ : syracuseStep 2212359 = 3318539) B3318539
theorem B2488909 : Blo 2211435 2488909 := bbase (se 3 (by rfl) ⟨466670, by rfl⟩ : syracuseStep 2488909 = 933341) (by norm_num)
theorem B3318545 : Blo 2211435 3318545 := bstep (se 2 (by rfl) ⟨1244454, by rfl⟩ : syracuseStep 3318545 = 2488909) B2488909
theorem B2212363 : Blo 2211435 2212363 := bstep (se 1 (by rfl) ⟨1659272, by rfl⟩ : syracuseStep 2212363 = 3318545) B3318545
theorem B7466741 : Blo 2211435 7466741 := bbase (se 5 (by rfl) ⟨350003, by rfl⟩ : syracuseStep 7466741 = 700007) (by norm_num)
theorem B4977827 : Blo 2211435 4977827 := bstep (se 1 (by rfl) ⟨3733370, by rfl⟩ : syracuseStep 4977827 = 7466741) B7466741
theorem B3318551 : Blo 2211435 3318551 := bstep (se 1 (by rfl) ⟨2488913, by rfl⟩ : syracuseStep 3318551 = 4977827) B4977827
theorem B2212367 : Blo 2211435 2212367 := bstep (se 1 (by rfl) ⟨1659275, by rfl⟩ : syracuseStep 2212367 = 3318551) B3318551
theorem B3318557 : Blo 2211435 3318557 := bbase (se 3 (by rfl) ⟨622229, by rfl⟩ : syracuseStep 3318557 = 1244459) (by norm_num)
theorem B2212371 : Blo 2211435 2212371 := bstep (se 1 (by rfl) ⟨1659278, by rfl⟩ : syracuseStep 2212371 = 3318557) B3318557
theorem B4977845 : Blo 2211435 4977845 := bbase (se 5 (by rfl) ⟨233336, by rfl⟩ : syracuseStep 4977845 = 466673) (by norm_num)
theorem B3318563 : Blo 2211435 3318563 := bstep (se 1 (by rfl) ⟨2488922, by rfl⟩ : syracuseStep 3318563 = 4977845) B4977845
theorem B2212375 : Blo 2211435 2212375 := bstep (se 1 (by rfl) ⟨1659281, by rfl⟩ : syracuseStep 2212375 = 3318563) B3318563
theorem B2362537 : Blo 2211435 2362537 := bbase (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) (by norm_num)
theorem B12600197 : Blo 2211435 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B8400131 : Blo 2211435 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B5600087 : Blo 2211435 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B3733391 : Blo 2211435 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B2488927 : Blo 2211435 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B3318569 : Blo 2211435 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B2212379 : Blo 2211435 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B2362541 : Blo 2211435 2362541 := bbase (se 3 (by rfl) ⟨442976, by rfl⟩ : syracuseStep 2362541 = 885953) (by norm_num)
theorem B6300109 : Blo 2211435 6300109 := bstep (se 3 (by rfl) ⟨1181270, by rfl⟩ : syracuseStep 6300109 = 2362541) B2362541
theorem B8400145 : Blo 2211435 8400145 := bstep (se 2 (by rfl) ⟨3150054, by rfl⟩ : syracuseStep 8400145 = 6300109) B6300109
theorem B11200193 : Blo 2211435 11200193 := bstep (se 2 (by rfl) ⟨4200072, by rfl⟩ : syracuseStep 11200193 = 8400145) B8400145
theorem B7466795 : Blo 2211435 7466795 := bstep (se 1 (by rfl) ⟨5600096, by rfl⟩ : syracuseStep 7466795 = 11200193) B11200193
theorem B4977863 : Blo 2211435 4977863 := bstep (se 1 (by rfl) ⟨3733397, by rfl⟩ : syracuseStep 4977863 = 7466795) B7466795
theorem B3318575 : Blo 2211435 3318575 := bstep (se 1 (by rfl) ⟨2488931, by rfl⟩ : syracuseStep 3318575 = 4977863) B4977863
theorem B2212383 : Blo 2211435 2212383 := bstep (se 1 (by rfl) ⟨1659287, by rfl⟩ : syracuseStep 2212383 = 3318575) B3318575
theorem B3318581 : Blo 2211435 3318581 := bbase (se 5 (by rfl) ⟨155558, by rfl⟩ : syracuseStep 3318581 = 311117) (by norm_num)
theorem B2212387 : Blo 2211435 2212387 := bstep (se 1 (by rfl) ⟨1659290, by rfl⟩ : syracuseStep 2212387 = 3318581) B3318581
theorem B5600117 : Blo 2211435 5600117 := bbase (se 5 (by rfl) ⟨262505, by rfl⟩ : syracuseStep 5600117 = 525011) (by norm_num)
theorem B3733411 : Blo 2211435 3733411 := bstep (se 1 (by rfl) ⟨2800058, by rfl⟩ : syracuseStep 3733411 = 5600117) B5600117
theorem B4977881 : Blo 2211435 4977881 := bstep (se 2 (by rfl) ⟨1866705, by rfl⟩ : syracuseStep 4977881 = 3733411) B3733411
theorem B3318587 : Blo 2211435 3318587 := bstep (se 1 (by rfl) ⟨2488940, by rfl⟩ : syracuseStep 3318587 = 4977881) B4977881
theorem B2212391 : Blo 2211435 2212391 := bstep (se 1 (by rfl) ⟨1659293, by rfl⟩ : syracuseStep 2212391 = 3318587) B3318587
theorem B2488945 : Blo 2211435 2488945 := bbase (se 2 (by rfl) ⟨933354, by rfl⟩ : syracuseStep 2488945 = 1866709) (by norm_num)
theorem B3318593 : Blo 2211435 3318593 := bstep (se 2 (by rfl) ⟨1244472, by rfl⟩ : syracuseStep 3318593 = 2488945) B2488945
theorem B2212395 : Blo 2211435 2212395 := bstep (se 1 (by rfl) ⟨1659296, by rfl⟩ : syracuseStep 2212395 = 3318593) B3318593
theorem B2242585 : Blo 2211435 2242585 := bbase (se 2 (by rfl) ⟨840969, by rfl⟩ : syracuseStep 2242585 = 1681939) (by norm_num)
theorem B11960453 : Blo 2211435 11960453 := bstep (se 4 (by rfl) ⟨1121292, by rfl⟩ : syracuseStep 11960453 = 2242585) B2242585
theorem B7973635 : Blo 2211435 7973635 := bstep (se 1 (by rfl) ⟨5980226, by rfl⟩ : syracuseStep 7973635 = 11960453) B11960453
theorem B10631513 : Blo 2211435 10631513 := bstep (se 2 (by rfl) ⟨3986817, by rfl⟩ : syracuseStep 10631513 = 7973635) B7973635
theorem B7087675 : Blo 2211435 7087675 := bstep (se 1 (by rfl) ⟨5315756, by rfl⟩ : syracuseStep 7087675 = 10631513) B10631513
theorem B9450233 : Blo 2211435 9450233 := bstep (se 2 (by rfl) ⟨3543837, by rfl⟩ : syracuseStep 9450233 = 7087675) B7087675
theorem B6300155 : Blo 2211435 6300155 := bstep (se 1 (by rfl) ⟨4725116, by rfl⟩ : syracuseStep 6300155 = 9450233) B9450233
theorem B4200103 : Blo 2211435 4200103 := bstep (se 1 (by rfl) ⟨3150077, by rfl⟩ : syracuseStep 4200103 = 6300155) B6300155
theorem B5600137 : Blo 2211435 5600137 := bstep (se 2 (by rfl) ⟨2100051, by rfl⟩ : syracuseStep 5600137 = 4200103) B4200103
theorem B7466849 : Blo 2211435 7466849 := bstep (se 2 (by rfl) ⟨2800068, by rfl⟩ : syracuseStep 7466849 = 5600137) B5600137
theorem B4977899 : Blo 2211435 4977899 := bstep (se 1 (by rfl) ⟨3733424, by rfl⟩ : syracuseStep 4977899 = 7466849) B7466849
theorem B3318599 : Blo 2211435 3318599 := bstep (se 1 (by rfl) ⟨2488949, by rfl⟩ : syracuseStep 3318599 = 4977899) B4977899
theorem B2212399 : Blo 2211435 2212399 := bstep (se 1 (by rfl) ⟨1659299, by rfl⟩ : syracuseStep 2212399 = 3318599) B3318599
theorem B3318605 : Blo 2211435 3318605 := bbase (se 3 (by rfl) ⟨622238, by rfl⟩ : syracuseStep 3318605 = 1244477) (by norm_num)
theorem B2212403 : Blo 2211435 2212403 := bstep (se 1 (by rfl) ⟨1659302, by rfl⟩ : syracuseStep 2212403 = 3318605) B3318605
theorem B4977917 : Blo 2211435 4977917 := bbase (se 3 (by rfl) ⟨933359, by rfl⟩ : syracuseStep 4977917 = 1866719) (by norm_num)
theorem B3318611 : Blo 2211435 3318611 := bstep (se 1 (by rfl) ⟨2488958, by rfl⟩ : syracuseStep 3318611 = 4977917) B4977917
theorem B2212407 : Blo 2211435 2212407 := bstep (se 1 (by rfl) ⟨1659305, by rfl⟩ : syracuseStep 2212407 = 3318611) B3318611
theorem B3733445 : Blo 2211435 3733445 := bbase (se 4 (by rfl) ⟨350010, by rfl⟩ : syracuseStep 3733445 = 700021) (by norm_num)
theorem B2488963 : Blo 2211435 2488963 := bstep (se 1 (by rfl) ⟨1866722, by rfl⟩ : syracuseStep 2488963 = 3733445) B3733445
theorem B3318617 : Blo 2211435 3318617 := bstep (se 2 (by rfl) ⟨1244481, by rfl⟩ : syracuseStep 3318617 = 2488963) B2488963
theorem B2212411 : Blo 2211435 2212411 := bstep (se 1 (by rfl) ⟨1659308, by rfl⟩ : syracuseStep 2212411 = 3318617) B3318617
theorem B16800533 : Blo 2211435 16800533 := bbase (se 6 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 16800533 = 787525) (by norm_num)
theorem B11200355 : Blo 2211435 11200355 := bstep (se 1 (by rfl) ⟨8400266, by rfl⟩ : syracuseStep 11200355 = 16800533) B16800533
theorem B7466903 : Blo 2211435 7466903 := bstep (se 1 (by rfl) ⟨5600177, by rfl⟩ : syracuseStep 7466903 = 11200355) B11200355
theorem B4977935 : Blo 2211435 4977935 := bstep (se 1 (by rfl) ⟨3733451, by rfl⟩ : syracuseStep 4977935 = 7466903) B7466903
theorem B3318623 : Blo 2211435 3318623 := bstep (se 1 (by rfl) ⟨2488967, by rfl⟩ : syracuseStep 3318623 = 4977935) B4977935
theorem B2212415 : Blo 2211435 2212415 := bstep (se 1 (by rfl) ⟨1659311, by rfl⟩ : syracuseStep 2212415 = 3318623) B3318623
theorem B3318629 : Blo 2211435 3318629 := bbase (se 4 (by rfl) ⟨311121, by rfl⟩ : syracuseStep 3318629 = 622243) (by norm_num)
theorem B2212419 : Blo 2211435 2212419 := bstep (se 1 (by rfl) ⟨1659314, by rfl⟩ : syracuseStep 2212419 = 3318629) B3318629
theorem B4200149 : Blo 2211435 4200149 := bbase (se 7 (by rfl) ⟨49220, by rfl⟩ : syracuseStep 4200149 = 98441) (by norm_num)
theorem B2800099 : Blo 2211435 2800099 := bstep (se 1 (by rfl) ⟨2100074, by rfl⟩ : syracuseStep 2800099 = 4200149) B4200149
theorem B3733465 : Blo 2211435 3733465 := bstep (se 2 (by rfl) ⟨1400049, by rfl⟩ : syracuseStep 3733465 = 2800099) B2800099
theorem B4977953 : Blo 2211435 4977953 := bstep (se 2 (by rfl) ⟨1866732, by rfl⟩ : syracuseStep 4977953 = 3733465) B3733465
theorem B3318635 : Blo 2211435 3318635 := bstep (se 1 (by rfl) ⟨2488976, by rfl⟩ : syracuseStep 3318635 = 4977953) B4977953
theorem B2212423 : Blo 2211435 2212423 := bstep (se 1 (by rfl) ⟨1659317, by rfl⟩ : syracuseStep 2212423 = 3318635) B3318635
theorem B2488981 : Blo 2211435 2488981 := bbase (se 6 (by rfl) ⟨58335, by rfl⟩ : syracuseStep 2488981 = 116671) (by norm_num)
theorem B3318641 : Blo 2211435 3318641 := bstep (se 2 (by rfl) ⟨1244490, by rfl⟩ : syracuseStep 3318641 = 2488981) B2488981
theorem B2212427 : Blo 2211435 2212427 := bstep (se 1 (by rfl) ⟨1659320, by rfl⟩ : syracuseStep 2212427 = 3318641) B3318641
theorem B2800109 : Blo 2211435 2800109 := bbase (se 3 (by rfl) ⟨525020, by rfl⟩ : syracuseStep 2800109 = 1050041) (by norm_num)
theorem B7466957 : Blo 2211435 7466957 := bstep (se 3 (by rfl) ⟨1400054, by rfl⟩ : syracuseStep 7466957 = 2800109) B2800109
theorem B4977971 : Blo 2211435 4977971 := bstep (se 1 (by rfl) ⟨3733478, by rfl⟩ : syracuseStep 4977971 = 7466957) B7466957
theorem B3318647 : Blo 2211435 3318647 := bstep (se 1 (by rfl) ⟨2488985, by rfl⟩ : syracuseStep 3318647 = 4977971) B4977971
theorem B2212431 : Blo 2211435 2212431 := bstep (se 1 (by rfl) ⟨1659323, by rfl⟩ : syracuseStep 2212431 = 3318647) B3318647
theorem B3318653 : Blo 2211435 3318653 := bbase (se 3 (by rfl) ⟨622247, by rfl⟩ : syracuseStep 3318653 = 1244495) (by norm_num)
theorem B2212435 : Blo 2211435 2212435 := bstep (se 1 (by rfl) ⟨1659326, by rfl⟩ : syracuseStep 2212435 = 3318653) B3318653
theorem B4977989 : Blo 2211435 4977989 := bbase (se 4 (by rfl) ⟨466686, by rfl⟩ : syracuseStep 4977989 = 933373) (by norm_num)
theorem B3318659 : Blo 2211435 3318659 := bstep (se 1 (by rfl) ⟨2488994, by rfl⟩ : syracuseStep 3318659 = 4977989) B4977989
theorem B2212439 : Blo 2211435 2212439 := bstep (se 1 (by rfl) ⟨1659329, by rfl⟩ : syracuseStep 2212439 = 3318659) B3318659
theorem B11960693 : Blo 2211435 11960693 := bbase (se 5 (by rfl) ⟨560657, by rfl⟩ : syracuseStep 11960693 = 1121315) (by norm_num)
theorem B7973795 : Blo 2211435 7973795 := bstep (se 1 (by rfl) ⟨5980346, by rfl⟩ : syracuseStep 7973795 = 11960693) B11960693
theorem B5315863 : Blo 2211435 5315863 := bstep (se 1 (by rfl) ⟨3986897, by rfl⟩ : syracuseStep 5315863 = 7973795) B7973795
theorem B7087817 : Blo 2211435 7087817 := bstep (se 2 (by rfl) ⟨2657931, by rfl⟩ : syracuseStep 7087817 = 5315863) B5315863
theorem B4725211 : Blo 2211435 4725211 := bstep (se 1 (by rfl) ⟨3543908, by rfl⟩ : syracuseStep 4725211 = 7087817) B7087817
theorem B6300281 : Blo 2211435 6300281 := bstep (se 2 (by rfl) ⟨2362605, by rfl⟩ : syracuseStep 6300281 = 4725211) B4725211
theorem B4200187 : Blo 2211435 4200187 := bstep (se 1 (by rfl) ⟨3150140, by rfl⟩ : syracuseStep 4200187 = 6300281) B6300281
theorem B5600249 : Blo 2211435 5600249 := bstep (se 2 (by rfl) ⟨2100093, by rfl⟩ : syracuseStep 5600249 = 4200187) B4200187
theorem B3733499 : Blo 2211435 3733499 := bstep (se 1 (by rfl) ⟨2800124, by rfl⟩ : syracuseStep 3733499 = 5600249) B5600249
theorem B2488999 : Blo 2211435 2488999 := bstep (se 1 (by rfl) ⟨1866749, by rfl⟩ : syracuseStep 2488999 = 3733499) B3733499
theorem B3318665 : Blo 2211435 3318665 := bstep (se 2 (by rfl) ⟨1244499, by rfl⟩ : syracuseStep 3318665 = 2488999) B2488999
theorem B2212443 : Blo 2211435 2212443 := bstep (se 1 (by rfl) ⟨1659332, by rfl⟩ : syracuseStep 2212443 = 3318665) B3318665
theorem B11200517 : Blo 2211435 11200517 := bbase (se 4 (by rfl) ⟨1050048, by rfl⟩ : syracuseStep 11200517 = 2100097) (by norm_num)
theorem B7467011 : Blo 2211435 7467011 := bstep (se 1 (by rfl) ⟨5600258, by rfl⟩ : syracuseStep 7467011 = 11200517) B11200517
theorem B4978007 : Blo 2211435 4978007 := bstep (se 1 (by rfl) ⟨3733505, by rfl⟩ : syracuseStep 4978007 = 7467011) B7467011
theorem B3318671 : Blo 2211435 3318671 := bstep (se 1 (by rfl) ⟨2489003, by rfl⟩ : syracuseStep 3318671 = 4978007) B4978007
theorem B2212447 : Blo 2211435 2212447 := bstep (se 1 (by rfl) ⟨1659335, by rfl⟩ : syracuseStep 2212447 = 3318671) B3318671
theorem B3318677 : Blo 2211435 3318677 := bbase (se 6 (by rfl) ⟨77781, by rfl⟩ : syracuseStep 3318677 = 155563) (by norm_num)
theorem B2212451 : Blo 2211435 2212451 := bstep (se 1 (by rfl) ⟨1659338, by rfl⟩ : syracuseStep 2212451 = 3318677) B3318677
theorem B12600629 : Blo 2211435 12600629 := bbase (se 5 (by rfl) ⟨590654, by rfl⟩ : syracuseStep 12600629 = 1181309) (by norm_num)
theorem B8400419 : Blo 2211435 8400419 := bstep (se 1 (by rfl) ⟨6300314, by rfl⟩ : syracuseStep 8400419 = 12600629) B12600629
theorem B5600279 : Blo 2211435 5600279 := bstep (se 1 (by rfl) ⟨4200209, by rfl⟩ : syracuseStep 5600279 = 8400419) B8400419
theorem B3733519 : Blo 2211435 3733519 := bstep (se 1 (by rfl) ⟨2800139, by rfl⟩ : syracuseStep 3733519 = 5600279) B5600279
theorem B4978025 : Blo 2211435 4978025 := bstep (se 2 (by rfl) ⟨1866759, by rfl⟩ : syracuseStep 4978025 = 3733519) B3733519
theorem B3318683 : Blo 2211435 3318683 := bstep (se 1 (by rfl) ⟨2489012, by rfl⟩ : syracuseStep 3318683 = 4978025) B4978025
theorem B2212455 : Blo 2211435 2212455 := bstep (se 1 (by rfl) ⟨1659341, by rfl⟩ : syracuseStep 2212455 = 3318683) B3318683
theorem B2489017 : Blo 2211435 2489017 := bbase (se 2 (by rfl) ⟨933381, by rfl⟩ : syracuseStep 2489017 = 1866763) (by norm_num)
theorem B3318689 : Blo 2211435 3318689 := bstep (se 2 (by rfl) ⟨1244508, by rfl⟩ : syracuseStep 3318689 = 2489017) B2489017
theorem B2212459 : Blo 2211435 2212459 := bstep (se 1 (by rfl) ⟨1659344, by rfl⟩ : syracuseStep 2212459 = 3318689) B3318689
theorem B4725253 : Blo 2211435 4725253 := bbase (se 4 (by rfl) ⟨442992, by rfl⟩ : syracuseStep 4725253 = 885985) (by norm_num)
theorem B6300337 : Blo 2211435 6300337 := bstep (se 2 (by rfl) ⟨2362626, by rfl⟩ : syracuseStep 6300337 = 4725253) B4725253
theorem B8400449 : Blo 2211435 8400449 := bstep (se 2 (by rfl) ⟨3150168, by rfl⟩ : syracuseStep 8400449 = 6300337) B6300337
theorem B5600299 : Blo 2211435 5600299 := bstep (se 1 (by rfl) ⟨4200224, by rfl⟩ : syracuseStep 5600299 = 8400449) B8400449
theorem B7467065 : Blo 2211435 7467065 := bstep (se 2 (by rfl) ⟨2800149, by rfl⟩ : syracuseStep 7467065 = 5600299) B5600299
theorem B4978043 : Blo 2211435 4978043 := bstep (se 1 (by rfl) ⟨3733532, by rfl⟩ : syracuseStep 4978043 = 7467065) B7467065
theorem B3318695 : Blo 2211435 3318695 := bstep (se 1 (by rfl) ⟨2489021, by rfl⟩ : syracuseStep 3318695 = 4978043) B4978043
theorem B2212463 : Blo 2211435 2212463 := bstep (se 1 (by rfl) ⟨1659347, by rfl⟩ : syracuseStep 2212463 = 3318695) B3318695
theorem B3318701 : Blo 2211435 3318701 := bbase (se 3 (by rfl) ⟨622256, by rfl⟩ : syracuseStep 3318701 = 1244513) (by norm_num)
theorem B2212467 : Blo 2211435 2212467 := bstep (se 1 (by rfl) ⟨1659350, by rfl⟩ : syracuseStep 2212467 = 3318701) B3318701
theorem B4978061 : Blo 2211435 4978061 := bbase (se 3 (by rfl) ⟨933386, by rfl⟩ : syracuseStep 4978061 = 1866773) (by norm_num)
theorem B3318707 : Blo 2211435 3318707 := bstep (se 1 (by rfl) ⟨2489030, by rfl⟩ : syracuseStep 3318707 = 4978061) B4978061
theorem B2212471 : Blo 2211435 2212471 := bstep (se 1 (by rfl) ⟨1659353, by rfl⟩ : syracuseStep 2212471 = 3318707) B3318707
theorem B2800165 : Blo 2211435 2800165 := bbase (se 4 (by rfl) ⟨262515, by rfl⟩ : syracuseStep 2800165 = 525031) (by norm_num)
theorem B3733553 : Blo 2211435 3733553 := bstep (se 2 (by rfl) ⟨1400082, by rfl⟩ : syracuseStep 3733553 = 2800165) B2800165
theorem B2489035 : Blo 2211435 2489035 := bstep (se 1 (by rfl) ⟨1866776, by rfl⟩ : syracuseStep 2489035 = 3733553) B3733553
theorem B3318713 : Blo 2211435 3318713 := bstep (se 2 (by rfl) ⟨1244517, by rfl⟩ : syracuseStep 3318713 = 2489035) B2489035
theorem B2212475 : Blo 2211435 2212475 := bstep (se 1 (by rfl) ⟨1659356, by rfl⟩ : syracuseStep 2212475 = 3318713) B3318713
theorem B25545365 : Blo 2211435 25545365 := bbase (se 6 (by rfl) ⟨598719, by rfl⟩ : syracuseStep 25545365 = 1197439) (by norm_num)
theorem B17030243 : Blo 2211435 17030243 := bstep (se 1 (by rfl) ⟨12772682, by rfl⟩ : syracuseStep 17030243 = 25545365) B25545365
theorem B11353495 : Blo 2211435 11353495 := bstep (se 1 (by rfl) ⟨8515121, by rfl⟩ : syracuseStep 11353495 = 17030243) B17030243
theorem B15137993 : Blo 2211435 15137993 := bstep (se 2 (by rfl) ⟨5676747, by rfl⟩ : syracuseStep 15137993 = 11353495) B11353495
theorem B10091995 : Blo 2211435 10091995 := bstep (se 1 (by rfl) ⟨7568996, by rfl⟩ : syracuseStep 10091995 = 15137993) B15137993
theorem B53823973 : Blo 2211435 53823973 := bstep (se 4 (by rfl) ⟨5045997, by rfl⟩ : syracuseStep 53823973 = 10091995) B10091995
theorem B71765297 : Blo 2211435 71765297 := bstep (se 2 (by rfl) ⟨26911986, by rfl⟩ : syracuseStep 71765297 = 53823973) B53823973
theorem B47843531 : Blo 2211435 47843531 := bstep (se 1 (by rfl) ⟨35882648, by rfl⟩ : syracuseStep 47843531 = 71765297) B71765297
theorem B31895687 : Blo 2211435 31895687 := bstep (se 1 (by rfl) ⟨23921765, by rfl⟩ : syracuseStep 31895687 = 47843531) B47843531
theorem B21263791 : Blo 2211435 21263791 := bstep (se 1 (by rfl) ⟨15947843, by rfl⟩ : syracuseStep 21263791 = 31895687) B31895687
theorem B28351721 : Blo 2211435 28351721 := bstep (se 2 (by rfl) ⟨10631895, by rfl⟩ : syracuseStep 28351721 = 21263791) B21263791
theorem B18901147 : Blo 2211435 18901147 := bstep (se 1 (by rfl) ⟨14175860, by rfl⟩ : syracuseStep 18901147 = 28351721) B28351721
theorem B25201529 : Blo 2211435 25201529 := bstep (se 2 (by rfl) ⟨9450573, by rfl⟩ : syracuseStep 25201529 = 18901147) B18901147
theorem B16801019 : Blo 2211435 16801019 := bstep (se 1 (by rfl) ⟨12600764, by rfl⟩ : syracuseStep 16801019 = 25201529) B25201529
theorem B11200679 : Blo 2211435 11200679 := bstep (se 1 (by rfl) ⟨8400509, by rfl⟩ : syracuseStep 11200679 = 16801019) B16801019
theorem B7467119 : Blo 2211435 7467119 := bstep (se 1 (by rfl) ⟨5600339, by rfl⟩ : syracuseStep 7467119 = 11200679) B11200679
theorem B4978079 : Blo 2211435 4978079 := bstep (se 1 (by rfl) ⟨3733559, by rfl⟩ : syracuseStep 4978079 = 7467119) B7467119
theorem B3318719 : Blo 2211435 3318719 := bstep (se 1 (by rfl) ⟨2489039, by rfl⟩ : syracuseStep 3318719 = 4978079) B4978079
theorem B2212479 : Blo 2211435 2212479 := bstep (se 1 (by rfl) ⟨1659359, by rfl⟩ : syracuseStep 2212479 = 3318719) B3318719
theorem B3318725 : Blo 2211435 3318725 := bbase (se 4 (by rfl) ⟨311130, by rfl⟩ : syracuseStep 3318725 = 622261) (by norm_num)
theorem B2212483 : Blo 2211435 2212483 := bstep (se 1 (by rfl) ⟨1659362, by rfl⟩ : syracuseStep 2212483 = 3318725) B3318725
theorem B3733573 : Blo 2211435 3733573 := bbase (se 4 (by rfl) ⟨350022, by rfl⟩ : syracuseStep 3733573 = 700045) (by norm_num)
theorem B4978097 : Blo 2211435 4978097 := bstep (se 2 (by rfl) ⟨1866786, by rfl⟩ : syracuseStep 4978097 = 3733573) B3733573
theorem B3318731 : Blo 2211435 3318731 := bstep (se 1 (by rfl) ⟨2489048, by rfl⟩ : syracuseStep 3318731 = 4978097) B4978097
theorem B2212487 : Blo 2211435 2212487 := bstep (se 1 (by rfl) ⟨1659365, by rfl⟩ : syracuseStep 2212487 = 3318731) B3318731
theorem B2489053 : Blo 2211435 2489053 := bbase (se 3 (by rfl) ⟨466697, by rfl⟩ : syracuseStep 2489053 = 933395) (by norm_num)
theorem B3318737 : Blo 2211435 3318737 := bstep (se 2 (by rfl) ⟨1244526, by rfl⟩ : syracuseStep 3318737 = 2489053) B2489053
theorem B2212491 : Blo 2211435 2212491 := bstep (se 1 (by rfl) ⟨1659368, by rfl⟩ : syracuseStep 2212491 = 3318737) B3318737
theorem B7467173 : Blo 2211435 7467173 := bbase (se 4 (by rfl) ⟨700047, by rfl⟩ : syracuseStep 7467173 = 1400095) (by norm_num)
theorem B4978115 : Blo 2211435 4978115 := bstep (se 1 (by rfl) ⟨3733586, by rfl⟩ : syracuseStep 4978115 = 7467173) B7467173
theorem B3318743 : Blo 2211435 3318743 := bstep (se 1 (by rfl) ⟨2489057, by rfl⟩ : syracuseStep 3318743 = 4978115) B4978115
theorem B2212495 : Blo 2211435 2212495 := bstep (se 1 (by rfl) ⟨1659371, by rfl⟩ : syracuseStep 2212495 = 3318743) B3318743
theorem B3318749 : Blo 2211435 3318749 := bbase (se 3 (by rfl) ⟨622265, by rfl⟩ : syracuseStep 3318749 = 1244531) (by norm_num)
theorem B2212499 : Blo 2211435 2212499 := bstep (se 1 (by rfl) ⟨1659374, by rfl⟩ : syracuseStep 2212499 = 3318749) B3318749
theorem B4978133 : Blo 2211435 4978133 := bbase (se 7 (by rfl) ⟨58337, by rfl⟩ : syracuseStep 4978133 = 116675) (by norm_num)
theorem B3318755 : Blo 2211435 3318755 := bstep (se 1 (by rfl) ⟨2489066, by rfl⟩ : syracuseStep 3318755 = 4978133) B4978133
theorem B2212503 : Blo 2211435 2212503 := bstep (se 1 (by rfl) ⟨1659377, by rfl⟩ : syracuseStep 2212503 = 3318755) B3318755
theorem B4485389 : Blo 2211435 4485389 := bbase (se 3 (by rfl) ⟨841010, by rfl⟩ : syracuseStep 4485389 = 1682021) (by norm_num)
theorem B11961037 : Blo 2211435 11961037 := bstep (se 3 (by rfl) ⟨2242694, by rfl⟩ : syracuseStep 11961037 = 4485389) B4485389
theorem B15948049 : Blo 2211435 15948049 := bstep (se 2 (by rfl) ⟨5980518, by rfl⟩ : syracuseStep 15948049 = 11961037) B11961037
theorem B21264065 : Blo 2211435 21264065 := bstep (se 2 (by rfl) ⟨7974024, by rfl⟩ : syracuseStep 21264065 = 15948049) B15948049
theorem B14176043 : Blo 2211435 14176043 := bstep (se 1 (by rfl) ⟨10632032, by rfl⟩ : syracuseStep 14176043 = 21264065) B21264065
theorem B9450695 : Blo 2211435 9450695 := bstep (se 1 (by rfl) ⟨7088021, by rfl⟩ : syracuseStep 9450695 = 14176043) B14176043
theorem B6300463 : Blo 2211435 6300463 := bstep (se 1 (by rfl) ⟨4725347, by rfl⟩ : syracuseStep 6300463 = 9450695) B9450695
theorem B8400617 : Blo 2211435 8400617 := bstep (se 2 (by rfl) ⟨3150231, by rfl⟩ : syracuseStep 8400617 = 6300463) B6300463
theorem B5600411 : Blo 2211435 5600411 := bstep (se 1 (by rfl) ⟨4200308, by rfl⟩ : syracuseStep 5600411 = 8400617) B8400617
theorem B3733607 : Blo 2211435 3733607 := bstep (se 1 (by rfl) ⟨2800205, by rfl⟩ : syracuseStep 3733607 = 5600411) B5600411
theorem B2489071 : Blo 2211435 2489071 := bstep (se 1 (by rfl) ⟨1866803, by rfl⟩ : syracuseStep 2489071 = 3733607) B3733607
theorem B3318761 : Blo 2211435 3318761 := bstep (se 2 (by rfl) ⟨1244535, by rfl⟩ : syracuseStep 3318761 = 2489071) B2489071
theorem B2212507 : Blo 2211435 2212507 := bstep (se 1 (by rfl) ⟨1659380, by rfl⟩ : syracuseStep 2212507 = 3318761) B3318761
theorem B4485397 : Blo 2211435 4485397 := bbase (se 6 (by rfl) ⟨105126, by rfl⟩ : syracuseStep 4485397 = 210253) (by norm_num)
theorem B5980529 : Blo 2211435 5980529 := bstep (se 2 (by rfl) ⟨2242698, by rfl⟩ : syracuseStep 5980529 = 4485397) B4485397
theorem B3987019 : Blo 2211435 3987019 := bstep (se 1 (by rfl) ⟨2990264, by rfl⟩ : syracuseStep 3987019 = 5980529) B5980529
theorem B5316025 : Blo 2211435 5316025 := bstep (se 2 (by rfl) ⟨1993509, by rfl⟩ : syracuseStep 5316025 = 3987019) B3987019
theorem B7088033 : Blo 2211435 7088033 := bstep (se 2 (by rfl) ⟨2658012, by rfl⟩ : syracuseStep 7088033 = 5316025) B5316025
theorem B18901421 : Blo 2211435 18901421 := bstep (se 3 (by rfl) ⟨3544016, by rfl⟩ : syracuseStep 18901421 = 7088033) B7088033
theorem B12600947 : Blo 2211435 12600947 := bstep (se 1 (by rfl) ⟨9450710, by rfl⟩ : syracuseStep 12600947 = 18901421) B18901421
theorem B8400631 : Blo 2211435 8400631 := bstep (se 1 (by rfl) ⟨6300473, by rfl⟩ : syracuseStep 8400631 = 12600947) B12600947
theorem B11200841 : Blo 2211435 11200841 := bstep (se 2 (by rfl) ⟨4200315, by rfl⟩ : syracuseStep 11200841 = 8400631) B8400631
theorem B7467227 : Blo 2211435 7467227 := bstep (se 1 (by rfl) ⟨5600420, by rfl⟩ : syracuseStep 7467227 = 11200841) B11200841
theorem B4978151 : Blo 2211435 4978151 := bstep (se 1 (by rfl) ⟨3733613, by rfl⟩ : syracuseStep 4978151 = 7467227) B7467227
theorem B3318767 : Blo 2211435 3318767 := bstep (se 1 (by rfl) ⟨2489075, by rfl⟩ : syracuseStep 3318767 = 4978151) B4978151
theorem B2212511 : Blo 2211435 2212511 := bstep (se 1 (by rfl) ⟨1659383, by rfl⟩ : syracuseStep 2212511 = 3318767) B3318767
theorem B3318773 : Blo 2211435 3318773 := bbase (se 5 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 3318773 = 311135) (by norm_num)
theorem B2212515 : Blo 2211435 2212515 := bstep (se 1 (by rfl) ⟨1659386, by rfl⟩ : syracuseStep 2212515 = 3318773) B3318773
theorem B4725373 : Blo 2211435 4725373 := bbase (se 3 (by rfl) ⟨886007, by rfl⟩ : syracuseStep 4725373 = 1772015) (by norm_num)
theorem B6300497 : Blo 2211435 6300497 := bstep (se 2 (by rfl) ⟨2362686, by rfl⟩ : syracuseStep 6300497 = 4725373) B4725373
theorem B4200331 : Blo 2211435 4200331 := bstep (se 1 (by rfl) ⟨3150248, by rfl⟩ : syracuseStep 4200331 = 6300497) B6300497
theorem B5600441 : Blo 2211435 5600441 := bstep (se 2 (by rfl) ⟨2100165, by rfl⟩ : syracuseStep 5600441 = 4200331) B4200331
theorem B3733627 : Blo 2211435 3733627 := bstep (se 1 (by rfl) ⟨2800220, by rfl⟩ : syracuseStep 3733627 = 5600441) B5600441
theorem B4978169 : Blo 2211435 4978169 := bstep (se 2 (by rfl) ⟨1866813, by rfl⟩ : syracuseStep 4978169 = 3733627) B3733627
theorem B3318779 : Blo 2211435 3318779 := bstep (se 1 (by rfl) ⟨2489084, by rfl⟩ : syracuseStep 3318779 = 4978169) B4978169
theorem B2212519 : Blo 2211435 2212519 := bstep (se 1 (by rfl) ⟨1659389, by rfl⟩ : syracuseStep 2212519 = 3318779) B3318779
theorem B2489089 : Blo 2211435 2489089 := bbase (se 2 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 2489089 = 1866817) (by norm_num)
theorem B3318785 : Blo 2211435 3318785 := bstep (se 2 (by rfl) ⟨1244544, by rfl⟩ : syracuseStep 3318785 = 2489089) B2489089
theorem B2212523 : Blo 2211435 2212523 := bstep (se 1 (by rfl) ⟨1659392, by rfl⟩ : syracuseStep 2212523 = 3318785) B3318785
theorem B5600461 : Blo 2211435 5600461 := bbase (se 3 (by rfl) ⟨1050086, by rfl⟩ : syracuseStep 5600461 = 2100173) (by norm_num)
theorem B7467281 : Blo 2211435 7467281 := bstep (se 2 (by rfl) ⟨2800230, by rfl⟩ : syracuseStep 7467281 = 5600461) B5600461
theorem B4978187 : Blo 2211435 4978187 := bstep (se 1 (by rfl) ⟨3733640, by rfl⟩ : syracuseStep 4978187 = 7467281) B7467281
theorem B3318791 : Blo 2211435 3318791 := bstep (se 1 (by rfl) ⟨2489093, by rfl⟩ : syracuseStep 3318791 = 4978187) B4978187
theorem B2212527 : Blo 2211435 2212527 := bstep (se 1 (by rfl) ⟨1659395, by rfl⟩ : syracuseStep 2212527 = 3318791) B3318791
theorem B3318797 : Blo 2211435 3318797 := bbase (se 3 (by rfl) ⟨622274, by rfl⟩ : syracuseStep 3318797 = 1244549) (by norm_num)
theorem B2212531 : Blo 2211435 2212531 := bstep (se 1 (by rfl) ⟨1659398, by rfl⟩ : syracuseStep 2212531 = 3318797) B3318797
theorem B4978205 : Blo 2211435 4978205 := bbase (se 3 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 4978205 = 1866827) (by norm_num)
theorem B3318803 : Blo 2211435 3318803 := bstep (se 1 (by rfl) ⟨2489102, by rfl⟩ : syracuseStep 3318803 = 4978205) B4978205
theorem B2212535 : Blo 2211435 2212535 := bstep (se 1 (by rfl) ⟨1659401, by rfl⟩ : syracuseStep 2212535 = 3318803) B3318803
theorem B3733661 : Blo 2211435 3733661 := bbase (se 3 (by rfl) ⟨700061, by rfl⟩ : syracuseStep 3733661 = 1400123) (by norm_num)
theorem B2489107 : Blo 2211435 2489107 := bstep (se 1 (by rfl) ⟨1866830, by rfl⟩ : syracuseStep 2489107 = 3733661) B3733661
theorem B3318809 : Blo 2211435 3318809 := bstep (se 2 (by rfl) ⟨1244553, by rfl⟩ : syracuseStep 3318809 = 2489107) B2489107
theorem B2212539 : Blo 2211435 2212539 := bstep (se 1 (by rfl) ⟨1659404, by rfl⟩ : syracuseStep 2212539 = 3318809) B3318809
theorem B4485461 : Blo 2211435 4485461 := bbase (se 10 (by rfl) ⟨6570, by rfl⟩ : syracuseStep 4485461 = 13141) (by norm_num)
theorem B47844917 : Blo 2211435 47844917 := bstep (se 5 (by rfl) ⟨2242730, by rfl⟩ : syracuseStep 47844917 = 4485461) B4485461
theorem B31896611 : Blo 2211435 31896611 := bstep (se 1 (by rfl) ⟨23922458, by rfl⟩ : syracuseStep 31896611 = 47844917) B47844917
theorem B21264407 : Blo 2211435 21264407 := bstep (se 1 (by rfl) ⟨15948305, by rfl⟩ : syracuseStep 21264407 = 31896611) B31896611
theorem B14176271 : Blo 2211435 14176271 := bstep (se 1 (by rfl) ⟨10632203, by rfl⟩ : syracuseStep 14176271 = 21264407) B21264407
theorem B9450847 : Blo 2211435 9450847 := bstep (se 1 (by rfl) ⟨7088135, by rfl⟩ : syracuseStep 9450847 = 14176271) B14176271
theorem B12601129 : Blo 2211435 12601129 := bstep (se 2 (by rfl) ⟨4725423, by rfl⟩ : syracuseStep 12601129 = 9450847) B9450847
theorem B16801505 : Blo 2211435 16801505 := bstep (se 2 (by rfl) ⟨6300564, by rfl⟩ : syracuseStep 16801505 = 12601129) B12601129
theorem B11201003 : Blo 2211435 11201003 := bstep (se 1 (by rfl) ⟨8400752, by rfl⟩ : syracuseStep 11201003 = 16801505) B16801505
theorem B7467335 : Blo 2211435 7467335 := bstep (se 1 (by rfl) ⟨5600501, by rfl⟩ : syracuseStep 7467335 = 11201003) B11201003
theorem B4978223 : Blo 2211435 4978223 := bstep (se 1 (by rfl) ⟨3733667, by rfl⟩ : syracuseStep 4978223 = 7467335) B7467335
theorem B3318815 : Blo 2211435 3318815 := bstep (se 1 (by rfl) ⟨2489111, by rfl⟩ : syracuseStep 3318815 = 4978223) B4978223
theorem B2212543 : Blo 2211435 2212543 := bstep (se 1 (by rfl) ⟨1659407, by rfl⟩ : syracuseStep 2212543 = 3318815) B3318815
theorem B3318821 : Blo 2211435 3318821 := bbase (se 4 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 3318821 = 622279) (by norm_num)
theorem B2212547 : Blo 2211435 2212547 := bstep (se 1 (by rfl) ⟨1659410, by rfl⟩ : syracuseStep 2212547 = 3318821) B3318821
theorem B2800261 : Blo 2211435 2800261 := bbase (se 4 (by rfl) ⟨262524, by rfl⟩ : syracuseStep 2800261 = 525049) (by norm_num)
theorem B3733681 : Blo 2211435 3733681 := bstep (se 2 (by rfl) ⟨1400130, by rfl⟩ : syracuseStep 3733681 = 2800261) B2800261
theorem B4978241 : Blo 2211435 4978241 := bstep (se 2 (by rfl) ⟨1866840, by rfl⟩ : syracuseStep 4978241 = 3733681) B3733681
theorem B3318827 : Blo 2211435 3318827 := bstep (se 1 (by rfl) ⟨2489120, by rfl⟩ : syracuseStep 3318827 = 4978241) B4978241
theorem B2212551 : Blo 2211435 2212551 := bstep (se 1 (by rfl) ⟨1659413, by rfl⟩ : syracuseStep 2212551 = 3318827) B3318827
theorem B2489125 : Blo 2211435 2489125 := bbase (se 4 (by rfl) ⟨233355, by rfl⟩ : syracuseStep 2489125 = 466711) (by norm_num)
theorem B3318833 : Blo 2211435 3318833 := bstep (se 2 (by rfl) ⟨1244562, by rfl⟩ : syracuseStep 3318833 = 2489125) B2489125
theorem B2212555 : Blo 2211435 2212555 := bstep (se 1 (by rfl) ⟨1659416, by rfl⟩ : syracuseStep 2212555 = 3318833) B3318833
theorem B9450917 : Blo 2211435 9450917 := bbase (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) (by norm_num)
theorem B6300611 : Blo 2211435 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B4200407 : Blo 2211435 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B2800271 : Blo 2211435 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B7467389 : Blo 2211435 7467389 := bstep (se 3 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 7467389 = 2800271) B2800271
theorem B4978259 : Blo 2211435 4978259 := bstep (se 1 (by rfl) ⟨3733694, by rfl⟩ : syracuseStep 4978259 = 7467389) B7467389
theorem B3318839 : Blo 2211435 3318839 := bstep (se 1 (by rfl) ⟨2489129, by rfl⟩ : syracuseStep 3318839 = 4978259) B4978259
theorem B2212559 : Blo 2211435 2212559 := bstep (se 1 (by rfl) ⟨1659419, by rfl⟩ : syracuseStep 2212559 = 3318839) B3318839
theorem B3318845 : Blo 2211435 3318845 := bbase (se 3 (by rfl) ⟨622283, by rfl⟩ : syracuseStep 3318845 = 1244567) (by norm_num)
theorem B2212563 : Blo 2211435 2212563 := bstep (se 1 (by rfl) ⟨1659422, by rfl⟩ : syracuseStep 2212563 = 3318845) B3318845
theorem B4978277 : Blo 2211435 4978277 := bbase (se 4 (by rfl) ⟨466713, by rfl⟩ : syracuseStep 4978277 = 933427) (by norm_num)
theorem B3318851 : Blo 2211435 3318851 := bstep (se 1 (by rfl) ⟨2489138, by rfl⟩ : syracuseStep 3318851 = 4978277) B4978277
theorem B2212567 : Blo 2211435 2212567 := bstep (se 1 (by rfl) ⟨1659425, by rfl⟩ : syracuseStep 2212567 = 3318851) B3318851
theorem B5600573 : Blo 2211435 5600573 := bbase (se 3 (by rfl) ⟨1050107, by rfl⟩ : syracuseStep 5600573 = 2100215) (by norm_num)
theorem B3733715 : Blo 2211435 3733715 := bstep (se 1 (by rfl) ⟨2800286, by rfl⟩ : syracuseStep 3733715 = 5600573) B5600573
theorem B2489143 : Blo 2211435 2489143 := bstep (se 1 (by rfl) ⟨1866857, by rfl⟩ : syracuseStep 2489143 = 3733715) B3733715
theorem B3318857 : Blo 2211435 3318857 := bstep (se 2 (by rfl) ⟨1244571, by rfl⟩ : syracuseStep 3318857 = 2489143) B2489143
theorem B2212571 : Blo 2211435 2212571 := bstep (se 1 (by rfl) ⟨1659428, by rfl⟩ : syracuseStep 2212571 = 3318857) B3318857
theorem B4200437 : Blo 2211435 4200437 := bbase (se 5 (by rfl) ⟨196895, by rfl⟩ : syracuseStep 4200437 = 393791) (by norm_num)
theorem B11201165 : Blo 2211435 11201165 := bstep (se 3 (by rfl) ⟨2100218, by rfl⟩ : syracuseStep 11201165 = 4200437) B4200437
theorem B7467443 : Blo 2211435 7467443 := bstep (se 1 (by rfl) ⟨5600582, by rfl⟩ : syracuseStep 7467443 = 11201165) B11201165
theorem B4978295 : Blo 2211435 4978295 := bstep (se 1 (by rfl) ⟨3733721, by rfl⟩ : syracuseStep 4978295 = 7467443) B7467443
theorem B3318863 : Blo 2211435 3318863 := bstep (se 1 (by rfl) ⟨2489147, by rfl⟩ : syracuseStep 3318863 = 4978295) B4978295
theorem B2212575 : Blo 2211435 2212575 := bstep (se 1 (by rfl) ⟨1659431, by rfl⟩ : syracuseStep 2212575 = 3318863) B3318863
theorem B3318869 : Blo 2211435 3318869 := bbase (se 8 (by rfl) ⟨19446, by rfl⟩ : syracuseStep 3318869 = 38893) (by norm_num)
theorem B2212579 : Blo 2211435 2212579 := bstep (se 1 (by rfl) ⟨1659434, by rfl⟩ : syracuseStep 2212579 = 3318869) B3318869
theorem B3987149 : Blo 2211435 3987149 := bbase (se 3 (by rfl) ⟨747590, by rfl⟩ : syracuseStep 3987149 = 1495181) (by norm_num)
theorem B10632397 : Blo 2211435 10632397 := bstep (se 3 (by rfl) ⟨1993574, by rfl⟩ : syracuseStep 10632397 = 3987149) B3987149
theorem B14176529 : Blo 2211435 14176529 := bstep (se 2 (by rfl) ⟨5316198, by rfl⟩ : syracuseStep 14176529 = 10632397) B10632397
theorem B9451019 : Blo 2211435 9451019 := bstep (se 1 (by rfl) ⟨7088264, by rfl⟩ : syracuseStep 9451019 = 14176529) B14176529
theorem B6300679 : Blo 2211435 6300679 := bstep (se 1 (by rfl) ⟨4725509, by rfl⟩ : syracuseStep 6300679 = 9451019) B9451019
theorem B8400905 : Blo 2211435 8400905 := bstep (se 2 (by rfl) ⟨3150339, by rfl⟩ : syracuseStep 8400905 = 6300679) B6300679
theorem B5600603 : Blo 2211435 5600603 := bstep (se 1 (by rfl) ⟨4200452, by rfl⟩ : syracuseStep 5600603 = 8400905) B8400905
theorem B3733735 : Blo 2211435 3733735 := bstep (se 1 (by rfl) ⟨2800301, by rfl⟩ : syracuseStep 3733735 = 5600603) B5600603
theorem B4978313 : Blo 2211435 4978313 := bstep (se 2 (by rfl) ⟨1866867, by rfl⟩ : syracuseStep 4978313 = 3733735) B3733735
theorem B3318875 : Blo 2211435 3318875 := bstep (se 1 (by rfl) ⟨2489156, by rfl⟩ : syracuseStep 3318875 = 4978313) B4978313
theorem B2212583 : Blo 2211435 2212583 := bstep (se 1 (by rfl) ⟨1659437, by rfl⟩ : syracuseStep 2212583 = 3318875) B3318875
theorem B2489161 : Blo 2211435 2489161 := bbase (se 2 (by rfl) ⟨933435, by rfl⟩ : syracuseStep 2489161 = 1866871) (by norm_num)
theorem B3318881 : Blo 2211435 3318881 := bstep (se 2 (by rfl) ⟨1244580, by rfl⟩ : syracuseStep 3318881 = 2489161) B2489161
theorem B2212587 : Blo 2211435 2212587 := bstep (se 1 (by rfl) ⟨1659440, by rfl⟩ : syracuseStep 2212587 = 3318881) B3318881
theorem B5677037 : Blo 2211435 5677037 := bbase (se 3 (by rfl) ⟨1064444, by rfl⟩ : syracuseStep 5677037 = 2128889) (by norm_num)
theorem B3784691 : Blo 2211435 3784691 := bstep (se 1 (by rfl) ⟨2838518, by rfl⟩ : syracuseStep 3784691 = 5677037) B5677037
theorem B10092509 : Blo 2211435 10092509 := bstep (se 3 (by rfl) ⟨1892345, by rfl⟩ : syracuseStep 10092509 = 3784691) B3784691
theorem B6728339 : Blo 2211435 6728339 := bstep (se 1 (by rfl) ⟨5046254, by rfl⟩ : syracuseStep 6728339 = 10092509) B10092509
theorem B4485559 : Blo 2211435 4485559 := bstep (se 1 (by rfl) ⟨3364169, by rfl⟩ : syracuseStep 4485559 = 6728339) B6728339
theorem B5980745 : Blo 2211435 5980745 := bstep (se 2 (by rfl) ⟨2242779, by rfl⟩ : syracuseStep 5980745 = 4485559) B4485559
theorem B3987163 : Blo 2211435 3987163 := bstep (se 1 (by rfl) ⟨2990372, by rfl⟩ : syracuseStep 3987163 = 5980745) B5980745
theorem B21264869 : Blo 2211435 21264869 := bstep (se 4 (by rfl) ⟨1993581, by rfl⟩ : syracuseStep 21264869 = 3987163) B3987163
theorem B14176579 : Blo 2211435 14176579 := bstep (se 1 (by rfl) ⟨10632434, by rfl⟩ : syracuseStep 14176579 = 21264869) B21264869
theorem B18902105 : Blo 2211435 18902105 := bstep (se 2 (by rfl) ⟨7088289, by rfl⟩ : syracuseStep 18902105 = 14176579) B14176579
theorem B12601403 : Blo 2211435 12601403 := bstep (se 1 (by rfl) ⟨9451052, by rfl⟩ : syracuseStep 12601403 = 18902105) B18902105
theorem B8400935 : Blo 2211435 8400935 := bstep (se 1 (by rfl) ⟨6300701, by rfl⟩ : syracuseStep 8400935 = 12601403) B12601403
theorem B5600623 : Blo 2211435 5600623 := bstep (se 1 (by rfl) ⟨4200467, by rfl⟩ : syracuseStep 5600623 = 8400935) B8400935
theorem B7467497 : Blo 2211435 7467497 := bstep (se 2 (by rfl) ⟨2800311, by rfl⟩ : syracuseStep 7467497 = 5600623) B5600623
theorem B4978331 : Blo 2211435 4978331 := bstep (se 1 (by rfl) ⟨3733748, by rfl⟩ : syracuseStep 4978331 = 7467497) B7467497
theorem B3318887 : Blo 2211435 3318887 := bstep (se 1 (by rfl) ⟨2489165, by rfl⟩ : syracuseStep 3318887 = 4978331) B4978331
theorem B2212591 : Blo 2211435 2212591 := bstep (se 1 (by rfl) ⟨1659443, by rfl⟩ : syracuseStep 2212591 = 3318887) B3318887
theorem B3318893 : Blo 2211435 3318893 := bbase (se 3 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 3318893 = 1244585) (by norm_num)
theorem B2212595 : Blo 2211435 2212595 := bstep (se 1 (by rfl) ⟨1659446, by rfl⟩ : syracuseStep 2212595 = 3318893) B3318893
theorem B4978349 : Blo 2211435 4978349 := bbase (se 3 (by rfl) ⟨933440, by rfl⟩ : syracuseStep 4978349 = 1866881) (by norm_num)
theorem B3318899 : Blo 2211435 3318899 := bstep (se 1 (by rfl) ⟨2489174, by rfl⟩ : syracuseStep 3318899 = 4978349) B4978349
theorem B2212599 : Blo 2211435 2212599 := bstep (se 1 (by rfl) ⟨1659449, by rfl⟩ : syracuseStep 2212599 = 3318899) B3318899
theorem B3544165 : Blo 2211435 3544165 := bbase (se 4 (by rfl) ⟨332265, by rfl⟩ : syracuseStep 3544165 = 664531) (by norm_num)
theorem B4725553 : Blo 2211435 4725553 := bstep (se 2 (by rfl) ⟨1772082, by rfl⟩ : syracuseStep 4725553 = 3544165) B3544165
theorem B6300737 : Blo 2211435 6300737 := bstep (se 2 (by rfl) ⟨2362776, by rfl⟩ : syracuseStep 6300737 = 4725553) B4725553
theorem B4200491 : Blo 2211435 4200491 := bstep (se 1 (by rfl) ⟨3150368, by rfl⟩ : syracuseStep 4200491 = 6300737) B6300737
theorem B2800327 : Blo 2211435 2800327 := bstep (se 1 (by rfl) ⟨2100245, by rfl⟩ : syracuseStep 2800327 = 4200491) B4200491
theorem B3733769 : Blo 2211435 3733769 := bstep (se 2 (by rfl) ⟨1400163, by rfl⟩ : syracuseStep 3733769 = 2800327) B2800327
theorem B2489179 : Blo 2211435 2489179 := bstep (se 1 (by rfl) ⟨1866884, by rfl⟩ : syracuseStep 2489179 = 3733769) B3733769
theorem B3318905 : Blo 2211435 3318905 := bstep (se 2 (by rfl) ⟨1244589, by rfl⟩ : syracuseStep 3318905 = 2489179) B2489179
theorem B2212603 : Blo 2211435 2212603 := bstep (se 1 (by rfl) ⟨1659452, by rfl⟩ : syracuseStep 2212603 = 3318905) B3318905
theorem B11509061 : Blo 2211435 11509061 := bbase (se 4 (by rfl) ⟨1078974, by rfl⟩ : syracuseStep 11509061 = 2157949) (by norm_num)
theorem B30690829 : Blo 2211435 30690829 := bstep (se 3 (by rfl) ⟨5754530, by rfl⟩ : syracuseStep 30690829 = 11509061) B11509061
theorem B163684421 : Blo 2211435 163684421 := bstep (se 4 (by rfl) ⟨15345414, by rfl⟩ : syracuseStep 163684421 = 30690829) B30690829
theorem B109122947 : Blo 2211435 109122947 := bstep (se 1 (by rfl) ⟨81842210, by rfl⟩ : syracuseStep 109122947 = 163684421) B163684421
theorem B72748631 : Blo 2211435 72748631 := bstep (se 1 (by rfl) ⟨54561473, by rfl⟩ : syracuseStep 72748631 = 109122947) B109122947
theorem B48499087 : Blo 2211435 48499087 := bstep (se 1 (by rfl) ⟨36374315, by rfl⟩ : syracuseStep 48499087 = 72748631) B72748631
theorem B64665449 : Blo 2211435 64665449 := bstep (se 2 (by rfl) ⟨24249543, by rfl⟩ : syracuseStep 64665449 = 48499087) B48499087
theorem B43110299 : Blo 2211435 43110299 := bstep (se 1 (by rfl) ⟨32332724, by rfl⟩ : syracuseStep 43110299 = 64665449) B64665449
theorem B28740199 : Blo 2211435 28740199 := bstep (se 1 (by rfl) ⟨21555149, by rfl⟩ : syracuseStep 28740199 = 43110299) B43110299
theorem B38320265 : Blo 2211435 38320265 := bstep (se 2 (by rfl) ⟨14370099, by rfl⟩ : syracuseStep 38320265 = 28740199) B28740199
theorem B25546843 : Blo 2211435 25546843 := bstep (se 1 (by rfl) ⟨19160132, by rfl⟩ : syracuseStep 25546843 = 38320265) B38320265
theorem B34062457 : Blo 2211435 34062457 := bstep (se 2 (by rfl) ⟨12773421, by rfl⟩ : syracuseStep 34062457 = 25546843) B25546843
theorem B45416609 : Blo 2211435 45416609 := bstep (se 2 (by rfl) ⟨17031228, by rfl⟩ : syracuseStep 45416609 = 34062457) B34062457
theorem B30277739 : Blo 2211435 30277739 := bstep (se 1 (by rfl) ⟨22708304, by rfl⟩ : syracuseStep 30277739 = 45416609) B45416609
theorem B20185159 : Blo 2211435 20185159 := bstep (se 1 (by rfl) ⟨15138869, by rfl⟩ : syracuseStep 20185159 = 30277739) B30277739
theorem B26913545 : Blo 2211435 26913545 := bstep (se 2 (by rfl) ⟨10092579, by rfl⟩ : syracuseStep 26913545 = 20185159) B20185159
theorem B17942363 : Blo 2211435 17942363 := bstep (se 1 (by rfl) ⟨13456772, by rfl⟩ : syracuseStep 17942363 = 26913545) B26913545
theorem B11961575 : Blo 2211435 11961575 := bstep (se 1 (by rfl) ⟨8971181, by rfl⟩ : syracuseStep 11961575 = 17942363) B17942363
theorem B7974383 : Blo 2211435 7974383 := bstep (se 1 (by rfl) ⟨5980787, by rfl⟩ : syracuseStep 7974383 = 11961575) B11961575
theorem B21265021 : Blo 2211435 21265021 := bstep (se 3 (by rfl) ⟨3987191, by rfl⟩ : syracuseStep 21265021 = 7974383) B7974383
theorem B28353361 : Blo 2211435 28353361 := bstep (se 2 (by rfl) ⟨10632510, by rfl⟩ : syracuseStep 28353361 = 21265021) B21265021
theorem B37804481 : Blo 2211435 37804481 := bstep (se 2 (by rfl) ⟨14176680, by rfl⟩ : syracuseStep 37804481 = 28353361) B28353361
theorem B25202987 : Blo 2211435 25202987 := bstep (se 1 (by rfl) ⟨18902240, by rfl⟩ : syracuseStep 25202987 = 37804481) B37804481
theorem B16801991 : Blo 2211435 16801991 := bstep (se 1 (by rfl) ⟨12601493, by rfl⟩ : syracuseStep 16801991 = 25202987) B25202987
theorem B11201327 : Blo 2211435 11201327 := bstep (se 1 (by rfl) ⟨8400995, by rfl⟩ : syracuseStep 11201327 = 16801991) B16801991
theorem B7467551 : Blo 2211435 7467551 := bstep (se 1 (by rfl) ⟨5600663, by rfl⟩ : syracuseStep 7467551 = 11201327) B11201327
theorem B4978367 : Blo 2211435 4978367 := bstep (se 1 (by rfl) ⟨3733775, by rfl⟩ : syracuseStep 4978367 = 7467551) B7467551
theorem B3318911 : Blo 2211435 3318911 := bstep (se 1 (by rfl) ⟨2489183, by rfl⟩ : syracuseStep 3318911 = 4978367) B4978367
theorem B2212607 : Blo 2211435 2212607 := bstep (se 1 (by rfl) ⟨1659455, by rfl⟩ : syracuseStep 2212607 = 3318911) B3318911
theorem B3318917 : Blo 2211435 3318917 := bbase (se 4 (by rfl) ⟨311148, by rfl⟩ : syracuseStep 3318917 = 622297) (by norm_num)
theorem B2212611 : Blo 2211435 2212611 := bstep (se 1 (by rfl) ⟨1659458, by rfl⟩ : syracuseStep 2212611 = 3318917) B3318917
theorem B3733789 : Blo 2211435 3733789 := bbase (se 3 (by rfl) ⟨700085, by rfl⟩ : syracuseStep 3733789 = 1400171) (by norm_num)
theorem B4978385 : Blo 2211435 4978385 := bstep (se 2 (by rfl) ⟨1866894, by rfl⟩ : syracuseStep 4978385 = 3733789) B3733789
theorem B3318923 : Blo 2211435 3318923 := bstep (se 1 (by rfl) ⟨2489192, by rfl⟩ : syracuseStep 3318923 = 4978385) B4978385
theorem B2212615 : Blo 2211435 2212615 := bstep (se 1 (by rfl) ⟨1659461, by rfl⟩ : syracuseStep 2212615 = 3318923) B3318923
theorem B2489197 : Blo 2211435 2489197 := bbase (se 3 (by rfl) ⟨466724, by rfl⟩ : syracuseStep 2489197 = 933449) (by norm_num)
theorem B3318929 : Blo 2211435 3318929 := bstep (se 2 (by rfl) ⟨1244598, by rfl⟩ : syracuseStep 3318929 = 2489197) B2489197
theorem B2212619 : Blo 2211435 2212619 := bstep (se 1 (by rfl) ⟨1659464, by rfl⟩ : syracuseStep 2212619 = 3318929) B3318929
theorem B7467605 : Blo 2211435 7467605 := bbase (se 8 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 7467605 = 87511) (by norm_num)
theorem B4978403 : Blo 2211435 4978403 := bstep (se 1 (by rfl) ⟨3733802, by rfl⟩ : syracuseStep 4978403 = 7467605) B7467605
theorem B3318935 : Blo 2211435 3318935 := bstep (se 1 (by rfl) ⟨2489201, by rfl⟩ : syracuseStep 3318935 = 4978403) B4978403
theorem B2212623 : Blo 2211435 2212623 := bstep (se 1 (by rfl) ⟨1659467, by rfl⟩ : syracuseStep 2212623 = 3318935) B3318935
theorem B3318941 : Blo 2211435 3318941 := bbase (se 3 (by rfl) ⟨622301, by rfl⟩ : syracuseStep 3318941 = 1244603) (by norm_num)
theorem B2212627 : Blo 2211435 2212627 := bstep (se 1 (by rfl) ⟨1659470, by rfl⟩ : syracuseStep 2212627 = 3318941) B3318941
theorem B4978421 : Blo 2211435 4978421 := bbase (se 5 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 4978421 = 466727) (by norm_num)
theorem B3318947 : Blo 2211435 3318947 := bstep (se 1 (by rfl) ⟨2489210, by rfl⟩ : syracuseStep 3318947 = 4978421) B4978421
theorem B2212631 : Blo 2211435 2212631 := bstep (se 1 (by rfl) ⟨1659473, by rfl⟩ : syracuseStep 2212631 = 3318947) B3318947
theorem B10092709 : Blo 2211435 10092709 := bbase (se 4 (by rfl) ⟨946191, by rfl⟩ : syracuseStep 10092709 = 1892383) (by norm_num)
theorem B13456945 : Blo 2211435 13456945 := bstep (se 2 (by rfl) ⟨5046354, by rfl⟩ : syracuseStep 13456945 = 10092709) B10092709
theorem B17942593 : Blo 2211435 17942593 := bstep (se 2 (by rfl) ⟨6728472, by rfl⟩ : syracuseStep 17942593 = 13456945) B13456945
theorem B23923457 : Blo 2211435 23923457 := bstep (se 2 (by rfl) ⟨8971296, by rfl⟩ : syracuseStep 23923457 = 17942593) B17942593
theorem B15948971 : Blo 2211435 15948971 := bstep (se 1 (by rfl) ⟨11961728, by rfl⟩ : syracuseStep 15948971 = 23923457) B23923457
theorem B10632647 : Blo 2211435 10632647 := bstep (se 1 (by rfl) ⟨7974485, by rfl⟩ : syracuseStep 10632647 = 15948971) B15948971
theorem B28353725 : Blo 2211435 28353725 := bstep (se 3 (by rfl) ⟨5316323, by rfl⟩ : syracuseStep 28353725 = 10632647) B10632647
theorem B18902483 : Blo 2211435 18902483 := bstep (se 1 (by rfl) ⟨14176862, by rfl⟩ : syracuseStep 18902483 = 28353725) B28353725
theorem B12601655 : Blo 2211435 12601655 := bstep (se 1 (by rfl) ⟨9451241, by rfl⟩ : syracuseStep 12601655 = 18902483) B18902483
theorem B8401103 : Blo 2211435 8401103 := bstep (se 1 (by rfl) ⟨6300827, by rfl⟩ : syracuseStep 8401103 = 12601655) B12601655
theorem B5600735 : Blo 2211435 5600735 := bstep (se 1 (by rfl) ⟨4200551, by rfl⟩ : syracuseStep 5600735 = 8401103) B8401103
theorem B3733823 : Blo 2211435 3733823 := bstep (se 1 (by rfl) ⟨2800367, by rfl⟩ : syracuseStep 3733823 = 5600735) B5600735
theorem B2489215 : Blo 2211435 2489215 := bstep (se 1 (by rfl) ⟨1866911, by rfl⟩ : syracuseStep 2489215 = 3733823) B3733823
theorem B3318953 : Blo 2211435 3318953 := bstep (se 2 (by rfl) ⟨1244607, by rfl⟩ : syracuseStep 3318953 = 2489215) B2489215
theorem B2212635 : Blo 2211435 2212635 := bstep (se 1 (by rfl) ⟨1659476, by rfl⟩ : syracuseStep 2212635 = 3318953) B3318953
theorem B4725629 : Blo 2211435 4725629 := bbase (se 3 (by rfl) ⟨886055, by rfl⟩ : syracuseStep 4725629 = 1772111) (by norm_num)
theorem B3150419 : Blo 2211435 3150419 := bstep (se 1 (by rfl) ⟨2362814, by rfl⟩ : syracuseStep 3150419 = 4725629) B4725629
theorem B8401117 : Blo 2211435 8401117 := bstep (se 3 (by rfl) ⟨1575209, by rfl⟩ : syracuseStep 8401117 = 3150419) B3150419
theorem B11201489 : Blo 2211435 11201489 := bstep (se 2 (by rfl) ⟨4200558, by rfl⟩ : syracuseStep 11201489 = 8401117) B8401117
theorem B7467659 : Blo 2211435 7467659 := bstep (se 1 (by rfl) ⟨5600744, by rfl⟩ : syracuseStep 7467659 = 11201489) B11201489
theorem B4978439 : Blo 2211435 4978439 := bstep (se 1 (by rfl) ⟨3733829, by rfl⟩ : syracuseStep 4978439 = 7467659) B7467659
theorem B3318959 : Blo 2211435 3318959 := bstep (se 1 (by rfl) ⟨2489219, by rfl⟩ : syracuseStep 3318959 = 4978439) B4978439
theorem B2212639 : Blo 2211435 2212639 := bstep (se 1 (by rfl) ⟨1659479, by rfl⟩ : syracuseStep 2212639 = 3318959) B3318959
theorem B3318965 : Blo 2211435 3318965 := bbase (se 5 (by rfl) ⟨155576, by rfl⟩ : syracuseStep 3318965 = 311153) (by norm_num)
theorem B2212643 : Blo 2211435 2212643 := bstep (se 1 (by rfl) ⟨1659482, by rfl⟩ : syracuseStep 2212643 = 3318965) B3318965
theorem B5600765 : Blo 2211435 5600765 := bbase (se 3 (by rfl) ⟨1050143, by rfl⟩ : syracuseStep 5600765 = 2100287) (by norm_num)
theorem B3733843 : Blo 2211435 3733843 := bstep (se 1 (by rfl) ⟨2800382, by rfl⟩ : syracuseStep 3733843 = 5600765) B5600765
theorem B4978457 : Blo 2211435 4978457 := bstep (se 2 (by rfl) ⟨1866921, by rfl⟩ : syracuseStep 4978457 = 3733843) B3733843
theorem B3318971 : Blo 2211435 3318971 := bstep (se 1 (by rfl) ⟨2489228, by rfl⟩ : syracuseStep 3318971 = 4978457) B4978457
theorem B2212647 : Blo 2211435 2212647 := bstep (se 1 (by rfl) ⟨1659485, by rfl⟩ : syracuseStep 2212647 = 3318971) B3318971
theorem B2489233 : Blo 2211435 2489233 := bbase (se 2 (by rfl) ⟨933462, by rfl⟩ : syracuseStep 2489233 = 1866925) (by norm_num)
theorem B3318977 : Blo 2211435 3318977 := bstep (se 2 (by rfl) ⟨1244616, by rfl⟩ : syracuseStep 3318977 = 2489233) B2489233
theorem B2212651 : Blo 2211435 2212651 := bstep (se 1 (by rfl) ⟨1659488, by rfl⟩ : syracuseStep 2212651 = 3318977) B3318977
theorem B4200589 : Blo 2211435 4200589 := bbase (se 3 (by rfl) ⟨787610, by rfl⟩ : syracuseStep 4200589 = 1575221) (by norm_num)
theorem B5600785 : Blo 2211435 5600785 := bstep (se 2 (by rfl) ⟨2100294, by rfl⟩ : syracuseStep 5600785 = 4200589) B4200589
theorem B7467713 : Blo 2211435 7467713 := bstep (se 2 (by rfl) ⟨2800392, by rfl⟩ : syracuseStep 7467713 = 5600785) B5600785
theorem B4978475 : Blo 2211435 4978475 := bstep (se 1 (by rfl) ⟨3733856, by rfl⟩ : syracuseStep 4978475 = 7467713) B7467713
theorem B3318983 : Blo 2211435 3318983 := bstep (se 1 (by rfl) ⟨2489237, by rfl⟩ : syracuseStep 3318983 = 4978475) B4978475
theorem B2212655 : Blo 2211435 2212655 := bstep (se 1 (by rfl) ⟨1659491, by rfl⟩ : syracuseStep 2212655 = 3318983) B3318983
theorem B3318989 : Blo 2211435 3318989 := bbase (se 3 (by rfl) ⟨622310, by rfl⟩ : syracuseStep 3318989 = 1244621) (by norm_num)
theorem B2212659 : Blo 2211435 2212659 := bstep (se 1 (by rfl) ⟨1659494, by rfl⟩ : syracuseStep 2212659 = 3318989) B3318989
theorem B4978493 : Blo 2211435 4978493 := bbase (se 3 (by rfl) ⟨933467, by rfl⟩ : syracuseStep 4978493 = 1866935) (by norm_num)
theorem B3318995 : Blo 2211435 3318995 := bstep (se 1 (by rfl) ⟨2489246, by rfl⟩ : syracuseStep 3318995 = 4978493) B4978493
theorem B2212663 : Blo 2211435 2212663 := bstep (se 1 (by rfl) ⟨1659497, by rfl⟩ : syracuseStep 2212663 = 3318995) B3318995
theorem B3733877 : Blo 2211435 3733877 := bbase (se 5 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 3733877 = 350051) (by norm_num)
theorem B2489251 : Blo 2211435 2489251 := bstep (se 1 (by rfl) ⟨1866938, by rfl⟩ : syracuseStep 2489251 = 3733877) B3733877
theorem B3319001 : Blo 2211435 3319001 := bstep (se 2 (by rfl) ⟨1244625, by rfl⟩ : syracuseStep 3319001 = 2489251) B2489251
theorem B2212667 : Blo 2211435 2212667 := bstep (se 1 (by rfl) ⟨1659500, by rfl⟩ : syracuseStep 2212667 = 3319001) B3319001
theorem B2658205 : Blo 2211435 2658205 := bbase (se 3 (by rfl) ⟨498413, by rfl⟩ : syracuseStep 2658205 = 996827) (by norm_num)
theorem B3544273 : Blo 2211435 3544273 := bstep (se 2 (by rfl) ⟨1329102, by rfl⟩ : syracuseStep 3544273 = 2658205) B2658205
theorem B4725697 : Blo 2211435 4725697 := bstep (se 2 (by rfl) ⟨1772136, by rfl⟩ : syracuseStep 4725697 = 3544273) B3544273
theorem B6300929 : Blo 2211435 6300929 := bstep (se 2 (by rfl) ⟨2362848, by rfl⟩ : syracuseStep 6300929 = 4725697) B4725697
theorem B16802477 : Blo 2211435 16802477 := bstep (se 3 (by rfl) ⟨3150464, by rfl⟩ : syracuseStep 16802477 = 6300929) B6300929
theorem B11201651 : Blo 2211435 11201651 := bstep (se 1 (by rfl) ⟨8401238, by rfl⟩ : syracuseStep 11201651 = 16802477) B16802477
theorem B7467767 : Blo 2211435 7467767 := bstep (se 1 (by rfl) ⟨5600825, by rfl⟩ : syracuseStep 7467767 = 11201651) B11201651
theorem B4978511 : Blo 2211435 4978511 := bstep (se 1 (by rfl) ⟨3733883, by rfl⟩ : syracuseStep 4978511 = 7467767) B7467767
theorem B3319007 : Blo 2211435 3319007 := bstep (se 1 (by rfl) ⟨2489255, by rfl⟩ : syracuseStep 3319007 = 4978511) B4978511
theorem B2212671 : Blo 2211435 2212671 := bstep (se 1 (by rfl) ⟨1659503, by rfl⟩ : syracuseStep 2212671 = 3319007) B3319007
theorem B3319013 : Blo 2211435 3319013 := bbase (se 4 (by rfl) ⟨311157, by rfl⟩ : syracuseStep 3319013 = 622315) (by norm_num)
theorem B2212675 : Blo 2211435 2212675 := bstep (se 1 (by rfl) ⟨1659506, by rfl⟩ : syracuseStep 2212675 = 3319013) B3319013
theorem B4257949 : Blo 2211435 4257949 := bbase (se 3 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 4257949 = 1596731) (by norm_num)
theorem B5677265 : Blo 2211435 5677265 := bstep (se 2 (by rfl) ⟨2128974, by rfl⟩ : syracuseStep 5677265 = 4257949) B4257949
theorem B3784843 : Blo 2211435 3784843 := bstep (se 1 (by rfl) ⟨2838632, by rfl⟩ : syracuseStep 3784843 = 5677265) B5677265
theorem B5046457 : Blo 2211435 5046457 := bstep (se 2 (by rfl) ⟨1892421, by rfl⟩ : syracuseStep 5046457 = 3784843) B3784843
theorem B6728609 : Blo 2211435 6728609 := bstep (se 2 (by rfl) ⟨2523228, by rfl⟩ : syracuseStep 6728609 = 5046457) B5046457
theorem B4485739 : Blo 2211435 4485739 := bstep (se 1 (by rfl) ⟨3364304, by rfl⟩ : syracuseStep 4485739 = 6728609) B6728609
theorem B5980985 : Blo 2211435 5980985 := bstep (se 2 (by rfl) ⟨2242869, by rfl⟩ : syracuseStep 5980985 = 4485739) B4485739
theorem B3987323 : Blo 2211435 3987323 := bstep (se 1 (by rfl) ⟨2990492, by rfl⟩ : syracuseStep 3987323 = 5980985) B5980985
theorem B2658215 : Blo 2211435 2658215 := bstep (se 1 (by rfl) ⟨1993661, by rfl⟩ : syracuseStep 2658215 = 3987323) B3987323
theorem B7088573 : Blo 2211435 7088573 := bstep (se 3 (by rfl) ⟨1329107, by rfl⟩ : syracuseStep 7088573 = 2658215) B2658215
theorem B4725715 : Blo 2211435 4725715 := bstep (se 1 (by rfl) ⟨3544286, by rfl⟩ : syracuseStep 4725715 = 7088573) B7088573
theorem B6300953 : Blo 2211435 6300953 := bstep (se 2 (by rfl) ⟨2362857, by rfl⟩ : syracuseStep 6300953 = 4725715) B4725715
theorem B4200635 : Blo 2211435 4200635 := bstep (se 1 (by rfl) ⟨3150476, by rfl⟩ : syracuseStep 4200635 = 6300953) B6300953
theorem B2800423 : Blo 2211435 2800423 := bstep (se 1 (by rfl) ⟨2100317, by rfl⟩ : syracuseStep 2800423 = 4200635) B4200635
theorem B3733897 : Blo 2211435 3733897 := bstep (se 2 (by rfl) ⟨1400211, by rfl⟩ : syracuseStep 3733897 = 2800423) B2800423
theorem B4978529 : Blo 2211435 4978529 := bstep (se 2 (by rfl) ⟨1866948, by rfl⟩ : syracuseStep 4978529 = 3733897) B3733897
theorem B3319019 : Blo 2211435 3319019 := bstep (se 1 (by rfl) ⟨2489264, by rfl⟩ : syracuseStep 3319019 = 4978529) B4978529
theorem B2212679 : Blo 2211435 2212679 := bstep (se 1 (by rfl) ⟨1659509, by rfl⟩ : syracuseStep 2212679 = 3319019) B3319019
theorem B2489269 : Blo 2211435 2489269 := bbase (se 5 (by rfl) ⟨116684, by rfl⟩ : syracuseStep 2489269 = 233369) (by norm_num)
theorem B3319025 : Blo 2211435 3319025 := bstep (se 2 (by rfl) ⟨1244634, by rfl⟩ : syracuseStep 3319025 = 2489269) B2489269
theorem B2212683 : Blo 2211435 2212683 := bstep (se 1 (by rfl) ⟨1659512, by rfl⟩ : syracuseStep 2212683 = 3319025) B3319025
theorem B2800433 : Blo 2211435 2800433 := bbase (se 2 (by rfl) ⟨1050162, by rfl⟩ : syracuseStep 2800433 = 2100325) (by norm_num)
theorem B7467821 : Blo 2211435 7467821 := bstep (se 3 (by rfl) ⟨1400216, by rfl⟩ : syracuseStep 7467821 = 2800433) B2800433
theorem B4978547 : Blo 2211435 4978547 := bstep (se 1 (by rfl) ⟨3733910, by rfl⟩ : syracuseStep 4978547 = 7467821) B7467821
theorem B3319031 : Blo 2211435 3319031 := bstep (se 1 (by rfl) ⟨2489273, by rfl⟩ : syracuseStep 3319031 = 4978547) B4978547
theorem B2212687 : Blo 2211435 2212687 := bstep (se 1 (by rfl) ⟨1659515, by rfl⟩ : syracuseStep 2212687 = 3319031) B3319031
theorem B3319037 : Blo 2211435 3319037 := bbase (se 3 (by rfl) ⟨622319, by rfl⟩ : syracuseStep 3319037 = 1244639) (by norm_num)
theorem B2212691 : Blo 2211435 2212691 := bstep (se 1 (by rfl) ⟨1659518, by rfl⟩ : syracuseStep 2212691 = 3319037) B3319037
theorem B4978565 : Blo 2211435 4978565 := bbase (se 4 (by rfl) ⟨466740, by rfl⟩ : syracuseStep 4978565 = 933481) (by norm_num)
theorem B3319043 : Blo 2211435 3319043 := bstep (se 1 (by rfl) ⟨2489282, by rfl⟩ : syracuseStep 3319043 = 4978565) B4978565
theorem B2212695 : Blo 2211435 2212695 := bstep (se 1 (by rfl) ⟨1659521, by rfl⟩ : syracuseStep 2212695 = 3319043) B3319043
theorem B8515973 : Blo 2211435 8515973 := bbase (se 4 (by rfl) ⟨798372, by rfl⟩ : syracuseStep 8515973 = 1596745) (by norm_num)
theorem B22709261 : Blo 2211435 22709261 := bstep (se 3 (by rfl) ⟨4257986, by rfl⟩ : syracuseStep 22709261 = 8515973) B8515973
theorem B60558029 : Blo 2211435 60558029 := bstep (se 3 (by rfl) ⟨11354630, by rfl⟩ : syracuseStep 60558029 = 22709261) B22709261
theorem B40372019 : Blo 2211435 40372019 := bstep (se 1 (by rfl) ⟨30279014, by rfl⟩ : syracuseStep 40372019 = 60558029) B60558029
theorem B26914679 : Blo 2211435 26914679 := bstep (se 1 (by rfl) ⟨20186009, by rfl⟩ : syracuseStep 26914679 = 40372019) B40372019
theorem B17943119 : Blo 2211435 17943119 := bstep (se 1 (by rfl) ⟨13457339, by rfl⟩ : syracuseStep 17943119 = 26914679) B26914679
theorem B11962079 : Blo 2211435 11962079 := bstep (se 1 (by rfl) ⟨8971559, by rfl⟩ : syracuseStep 11962079 = 17943119) B17943119
theorem B7974719 : Blo 2211435 7974719 := bstep (se 1 (by rfl) ⟨5981039, by rfl⟩ : syracuseStep 7974719 = 11962079) B11962079
theorem B5316479 : Blo 2211435 5316479 := bstep (se 1 (by rfl) ⟨3987359, by rfl⟩ : syracuseStep 5316479 = 7974719) B7974719
theorem B3544319 : Blo 2211435 3544319 := bstep (se 1 (by rfl) ⟨2658239, by rfl⟩ : syracuseStep 3544319 = 5316479) B5316479
theorem B2362879 : Blo 2211435 2362879 := bstep (se 1 (by rfl) ⟨1772159, by rfl⟩ : syracuseStep 2362879 = 3544319) B3544319
theorem B3150505 : Blo 2211435 3150505 := bstep (se 2 (by rfl) ⟨1181439, by rfl⟩ : syracuseStep 3150505 = 2362879) B2362879
theorem B4200673 : Blo 2211435 4200673 := bstep (se 2 (by rfl) ⟨1575252, by rfl⟩ : syracuseStep 4200673 = 3150505) B3150505
theorem B5600897 : Blo 2211435 5600897 := bstep (se 2 (by rfl) ⟨2100336, by rfl⟩ : syracuseStep 5600897 = 4200673) B4200673
theorem B3733931 : Blo 2211435 3733931 := bstep (se 1 (by rfl) ⟨2800448, by rfl⟩ : syracuseStep 3733931 = 5600897) B5600897
theorem B2489287 : Blo 2211435 2489287 := bstep (se 1 (by rfl) ⟨1866965, by rfl⟩ : syracuseStep 2489287 = 3733931) B3733931
theorem B3319049 : Blo 2211435 3319049 := bstep (se 2 (by rfl) ⟨1244643, by rfl⟩ : syracuseStep 3319049 = 2489287) B2489287
theorem B2212699 : Blo 2211435 2212699 := bstep (se 1 (by rfl) ⟨1659524, by rfl⟩ : syracuseStep 2212699 = 3319049) B3319049
theorem B11201813 : Blo 2211435 11201813 := bbase (se 6 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 11201813 = 525085) (by norm_num)
theorem B7467875 : Blo 2211435 7467875 := bstep (se 1 (by rfl) ⟨5600906, by rfl⟩ : syracuseStep 7467875 = 11201813) B11201813
theorem B4978583 : Blo 2211435 4978583 := bstep (se 1 (by rfl) ⟨3733937, by rfl⟩ : syracuseStep 4978583 = 7467875) B7467875
theorem B3319055 : Blo 2211435 3319055 := bstep (se 1 (by rfl) ⟨2489291, by rfl⟩ : syracuseStep 3319055 = 4978583) B4978583
theorem B2212703 : Blo 2211435 2212703 := bstep (se 1 (by rfl) ⟨1659527, by rfl⟩ : syracuseStep 2212703 = 3319055) B3319055
theorem B3319061 : Blo 2211435 3319061 := bbase (se 6 (by rfl) ⟨77790, by rfl⟩ : syracuseStep 3319061 = 155581) (by norm_num)
theorem B2212707 : Blo 2211435 2212707 := bstep (se 1 (by rfl) ⟨1659530, by rfl⟩ : syracuseStep 2212707 = 3319061) B3319061
theorem B2877401 : Blo 2211435 2877401 := bbase (se 2 (by rfl) ⟨1079025, by rfl⟩ : syracuseStep 2877401 = 2158051) (by norm_num)
theorem B7673069 : Blo 2211435 7673069 := bstep (se 3 (by rfl) ⟨1438700, by rfl⟩ : syracuseStep 7673069 = 2877401) B2877401
theorem B20461517 : Blo 2211435 20461517 := bstep (se 3 (by rfl) ⟨3836534, by rfl⟩ : syracuseStep 20461517 = 7673069) B7673069
theorem B13641011 : Blo 2211435 13641011 := bstep (se 1 (by rfl) ⟨10230758, by rfl⟩ : syracuseStep 13641011 = 20461517) B20461517
theorem B9094007 : Blo 2211435 9094007 := bstep (se 1 (by rfl) ⟨6820505, by rfl⟩ : syracuseStep 9094007 = 13641011) B13641011
theorem B6062671 : Blo 2211435 6062671 := bstep (se 1 (by rfl) ⟨4547003, by rfl⟩ : syracuseStep 6062671 = 9094007) B9094007
theorem B32334245 : Blo 2211435 32334245 := bstep (se 4 (by rfl) ⟨3031335, by rfl⟩ : syracuseStep 32334245 = 6062671) B6062671
theorem B21556163 : Blo 2211435 21556163 := bstep (se 1 (by rfl) ⟨16167122, by rfl⟩ : syracuseStep 21556163 = 32334245) B32334245
theorem B57483101 : Blo 2211435 57483101 := bstep (se 3 (by rfl) ⟨10778081, by rfl⟩ : syracuseStep 57483101 = 21556163) B21556163
theorem B38322067 : Blo 2211435 38322067 := bstep (se 1 (by rfl) ⟨28741550, by rfl⟩ : syracuseStep 38322067 = 57483101) B57483101
theorem B51096089 : Blo 2211435 51096089 := bstep (se 2 (by rfl) ⟨19161033, by rfl⟩ : syracuseStep 51096089 = 38322067) B38322067
theorem B34064059 : Blo 2211435 34064059 := bstep (se 1 (by rfl) ⟨25548044, by rfl⟩ : syracuseStep 34064059 = 51096089) B51096089
theorem B45418745 : Blo 2211435 45418745 := bstep (se 2 (by rfl) ⟨17032029, by rfl⟩ : syracuseStep 45418745 = 34064059) B34064059
theorem B121116653 : Blo 2211435 121116653 := bstep (se 3 (by rfl) ⟨22709372, by rfl⟩ : syracuseStep 121116653 = 45418745) B45418745
theorem B80744435 : Blo 2211435 80744435 := bstep (se 1 (by rfl) ⟨60558326, by rfl⟩ : syracuseStep 80744435 = 121116653) B121116653
theorem B53829623 : Blo 2211435 53829623 := bstep (se 1 (by rfl) ⟨40372217, by rfl⟩ : syracuseStep 53829623 = 80744435) B80744435
theorem B35886415 : Blo 2211435 35886415 := bstep (se 1 (by rfl) ⟨26914811, by rfl⟩ : syracuseStep 35886415 = 53829623) B53829623
theorem B47848553 : Blo 2211435 47848553 := bstep (se 2 (by rfl) ⟨17943207, by rfl⟩ : syracuseStep 47848553 = 35886415) B35886415
theorem B31899035 : Blo 2211435 31899035 := bstep (se 1 (by rfl) ⟨23924276, by rfl⟩ : syracuseStep 31899035 = 47848553) B47848553
theorem B21266023 : Blo 2211435 21266023 := bstep (se 1 (by rfl) ⟨15949517, by rfl⟩ : syracuseStep 21266023 = 31899035) B31899035
theorem B28354697 : Blo 2211435 28354697 := bstep (se 2 (by rfl) ⟨10633011, by rfl⟩ : syracuseStep 28354697 = 21266023) B21266023
theorem B18903131 : Blo 2211435 18903131 := bstep (se 1 (by rfl) ⟨14177348, by rfl⟩ : syracuseStep 18903131 = 28354697) B28354697
theorem B12602087 : Blo 2211435 12602087 := bstep (se 1 (by rfl) ⟨9451565, by rfl⟩ : syracuseStep 12602087 = 18903131) B18903131
theorem B8401391 : Blo 2211435 8401391 := bstep (se 1 (by rfl) ⟨6301043, by rfl⟩ : syracuseStep 8401391 = 12602087) B12602087
theorem B5600927 : Blo 2211435 5600927 := bstep (se 1 (by rfl) ⟨4200695, by rfl⟩ : syracuseStep 5600927 = 8401391) B8401391
theorem B3733951 : Blo 2211435 3733951 := bstep (se 1 (by rfl) ⟨2800463, by rfl⟩ : syracuseStep 3733951 = 5600927) B5600927
theorem B4978601 : Blo 2211435 4978601 := bstep (se 2 (by rfl) ⟨1866975, by rfl⟩ : syracuseStep 4978601 = 3733951) B3733951
theorem B3319067 : Blo 2211435 3319067 := bstep (se 1 (by rfl) ⟨2489300, by rfl⟩ : syracuseStep 3319067 = 4978601) B4978601
theorem B2212711 : Blo 2211435 2212711 := bstep (se 1 (by rfl) ⟨1659533, by rfl⟩ : syracuseStep 2212711 = 3319067) B3319067
theorem B2489305 : Blo 2211435 2489305 := bbase (se 2 (by rfl) ⟨933489, by rfl⟩ : syracuseStep 2489305 = 1866979) (by norm_num)
theorem B3319073 : Blo 2211435 3319073 := bstep (se 2 (by rfl) ⟨1244652, by rfl⟩ : syracuseStep 3319073 = 2489305) B2489305
theorem B2212715 : Blo 2211435 2212715 := bstep (se 1 (by rfl) ⟨1659536, by rfl⟩ : syracuseStep 2212715 = 3319073) B3319073
theorem B3150533 : Blo 2211435 3150533 := bbase (se 4 (by rfl) ⟨295362, by rfl⟩ : syracuseStep 3150533 = 590725) (by norm_num)
theorem B8401421 : Blo 2211435 8401421 := bstep (se 3 (by rfl) ⟨1575266, by rfl⟩ : syracuseStep 8401421 = 3150533) B3150533
theorem B5600947 : Blo 2211435 5600947 := bstep (se 1 (by rfl) ⟨4200710, by rfl⟩ : syracuseStep 5600947 = 8401421) B8401421
theorem B7467929 : Blo 2211435 7467929 := bstep (se 2 (by rfl) ⟨2800473, by rfl⟩ : syracuseStep 7467929 = 5600947) B5600947
theorem B4978619 : Blo 2211435 4978619 := bstep (se 1 (by rfl) ⟨3733964, by rfl⟩ : syracuseStep 4978619 = 7467929) B7467929
theorem B3319079 : Blo 2211435 3319079 := bstep (se 1 (by rfl) ⟨2489309, by rfl⟩ : syracuseStep 3319079 = 4978619) B4978619
theorem B2212719 : Blo 2211435 2212719 := bstep (se 1 (by rfl) ⟨1659539, by rfl⟩ : syracuseStep 2212719 = 3319079) B3319079
theorem B3319085 : Blo 2211435 3319085 := bbase (se 3 (by rfl) ⟨622328, by rfl⟩ : syracuseStep 3319085 = 1244657) (by norm_num)
theorem B2212723 : Blo 2211435 2212723 := bstep (se 1 (by rfl) ⟨1659542, by rfl⟩ : syracuseStep 2212723 = 3319085) B3319085
theorem B4978637 : Blo 2211435 4978637 := bbase (se 3 (by rfl) ⟨933494, by rfl⟩ : syracuseStep 4978637 = 1866989) (by norm_num)
theorem B3319091 : Blo 2211435 3319091 := bstep (se 1 (by rfl) ⟨2489318, by rfl⟩ : syracuseStep 3319091 = 4978637) B4978637
theorem B2212727 : Blo 2211435 2212727 := bstep (se 1 (by rfl) ⟨1659545, by rfl⟩ : syracuseStep 2212727 = 3319091) B3319091
theorem B2800489 : Blo 2211435 2800489 := bbase (se 2 (by rfl) ⟨1050183, by rfl⟩ : syracuseStep 2800489 = 2100367) (by norm_num)
theorem B3733985 : Blo 2211435 3733985 := bstep (se 2 (by rfl) ⟨1400244, by rfl⟩ : syracuseStep 3733985 = 2800489) B2800489
theorem B2489323 : Blo 2211435 2489323 := bstep (se 1 (by rfl) ⟨1866992, by rfl⟩ : syracuseStep 2489323 = 3733985) B3733985
theorem B3319097 : Blo 2211435 3319097 := bstep (se 2 (by rfl) ⟨1244661, by rfl⟩ : syracuseStep 3319097 = 2489323) B2489323
theorem B2212731 : Blo 2211435 2212731 := bstep (se 1 (by rfl) ⟨1659548, by rfl⟩ : syracuseStep 2212731 = 3319097) B3319097
theorem B6062741 : Blo 2211435 6062741 := bbase (se 6 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 6062741 = 284191) (by norm_num)
theorem B4041827 : Blo 2211435 4041827 := bstep (se 1 (by rfl) ⟨3031370, by rfl⟩ : syracuseStep 4041827 = 6062741) B6062741
theorem B2694551 : Blo 2211435 2694551 := bstep (se 1 (by rfl) ⟨2020913, by rfl⟩ : syracuseStep 2694551 = 4041827) B4041827
theorem B7185469 : Blo 2211435 7185469 := bstep (se 3 (by rfl) ⟨1347275, by rfl⟩ : syracuseStep 7185469 = 2694551) B2694551
theorem B9580625 : Blo 2211435 9580625 := bstep (se 2 (by rfl) ⟨3592734, by rfl⟩ : syracuseStep 9580625 = 7185469) B7185469
theorem B6387083 : Blo 2211435 6387083 := bstep (se 1 (by rfl) ⟨4790312, by rfl⟩ : syracuseStep 6387083 = 9580625) B9580625
theorem B4258055 : Blo 2211435 4258055 := bstep (se 1 (by rfl) ⟨3193541, by rfl⟩ : syracuseStep 4258055 = 6387083) B6387083
theorem B11354813 : Blo 2211435 11354813 := bstep (se 3 (by rfl) ⟨2129027, by rfl⟩ : syracuseStep 11354813 = 4258055) B4258055
theorem B7569875 : Blo 2211435 7569875 := bstep (se 1 (by rfl) ⟨5677406, by rfl⟩ : syracuseStep 7569875 = 11354813) B11354813
theorem B5046583 : Blo 2211435 5046583 := bstep (se 1 (by rfl) ⟨3784937, by rfl⟩ : syracuseStep 5046583 = 7569875) B7569875
theorem B6728777 : Blo 2211435 6728777 := bstep (se 2 (by rfl) ⟨2523291, by rfl⟩ : syracuseStep 6728777 = 5046583) B5046583
theorem B4485851 : Blo 2211435 4485851 := bstep (se 1 (by rfl) ⟨3364388, by rfl⟩ : syracuseStep 4485851 = 6728777) B6728777
theorem B2990567 : Blo 2211435 2990567 := bstep (se 1 (by rfl) ⟨2242925, by rfl⟩ : syracuseStep 2990567 = 4485851) B4485851
theorem B7974845 : Blo 2211435 7974845 := bstep (se 3 (by rfl) ⟨1495283, by rfl⟩ : syracuseStep 7974845 = 2990567) B2990567
theorem B5316563 : Blo 2211435 5316563 := bstep (se 1 (by rfl) ⟨3987422, by rfl⟩ : syracuseStep 5316563 = 7974845) B7974845
theorem B14177501 : Blo 2211435 14177501 := bstep (se 3 (by rfl) ⟨2658281, by rfl⟩ : syracuseStep 14177501 = 5316563) B5316563
theorem B9451667 : Blo 2211435 9451667 := bstep (se 1 (by rfl) ⟨7088750, by rfl⟩ : syracuseStep 9451667 = 14177501) B14177501
theorem B25204445 : Blo 2211435 25204445 := bstep (se 3 (by rfl) ⟨4725833, by rfl⟩ : syracuseStep 25204445 = 9451667) B9451667
theorem B16802963 : Blo 2211435 16802963 := bstep (se 1 (by rfl) ⟨12602222, by rfl⟩ : syracuseStep 16802963 = 25204445) B25204445
theorem B11201975 : Blo 2211435 11201975 := bstep (se 1 (by rfl) ⟨8401481, by rfl⟩ : syracuseStep 11201975 = 16802963) B16802963
theorem B7467983 : Blo 2211435 7467983 := bstep (se 1 (by rfl) ⟨5600987, by rfl⟩ : syracuseStep 7467983 = 11201975) B11201975
theorem B4978655 : Blo 2211435 4978655 := bstep (se 1 (by rfl) ⟨3733991, by rfl⟩ : syracuseStep 4978655 = 7467983) B7467983
theorem B3319103 : Blo 2211435 3319103 := bstep (se 1 (by rfl) ⟨2489327, by rfl⟩ : syracuseStep 3319103 = 4978655) B4978655
theorem B2212735 : Blo 2211435 2212735 := bstep (se 1 (by rfl) ⟨1659551, by rfl⟩ : syracuseStep 2212735 = 3319103) B3319103
theorem B3319109 : Blo 2211435 3319109 := bbase (se 4 (by rfl) ⟨311166, by rfl⟩ : syracuseStep 3319109 = 622333) (by norm_num)
theorem B2212739 : Blo 2211435 2212739 := bstep (se 1 (by rfl) ⟨1659554, by rfl⟩ : syracuseStep 2212739 = 3319109) B3319109
theorem B3734005 : Blo 2211435 3734005 := bbase (se 5 (by rfl) ⟨175031, by rfl⟩ : syracuseStep 3734005 = 350063) (by norm_num)
theorem B4978673 : Blo 2211435 4978673 := bstep (se 2 (by rfl) ⟨1867002, by rfl⟩ : syracuseStep 4978673 = 3734005) B3734005
theorem B3319115 : Blo 2211435 3319115 := bstep (se 1 (by rfl) ⟨2489336, by rfl⟩ : syracuseStep 3319115 = 4978673) B4978673
theorem B2212743 : Blo 2211435 2212743 := bstep (se 1 (by rfl) ⟨1659557, by rfl⟩ : syracuseStep 2212743 = 3319115) B3319115
theorem B2489341 : Blo 2211435 2489341 := bbase (se 3 (by rfl) ⟨466751, by rfl⟩ : syracuseStep 2489341 = 933503) (by norm_num)
theorem B3319121 : Blo 2211435 3319121 := bstep (se 2 (by rfl) ⟨1244670, by rfl⟩ : syracuseStep 3319121 = 2489341) B2489341
theorem B2212747 : Blo 2211435 2212747 := bstep (se 1 (by rfl) ⟨1659560, by rfl⟩ : syracuseStep 2212747 = 3319121) B3319121
theorem B7468037 : Blo 2211435 7468037 := bbase (se 4 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 7468037 = 1400257) (by norm_num)
theorem B4978691 : Blo 2211435 4978691 := bstep (se 1 (by rfl) ⟨3734018, by rfl⟩ : syracuseStep 4978691 = 7468037) B7468037
theorem B3319127 : Blo 2211435 3319127 := bstep (se 1 (by rfl) ⟨2489345, by rfl⟩ : syracuseStep 3319127 = 4978691) B4978691
theorem B2212751 : Blo 2211435 2212751 := bstep (se 1 (by rfl) ⟨1659563, by rfl⟩ : syracuseStep 2212751 = 3319127) B3319127
theorem B3319133 : Blo 2211435 3319133 := bbase (se 3 (by rfl) ⟨622337, by rfl⟩ : syracuseStep 3319133 = 1244675) (by norm_num)
theorem B2212755 : Blo 2211435 2212755 := bstep (se 1 (by rfl) ⟨1659566, by rfl⟩ : syracuseStep 2212755 = 3319133) B3319133
theorem B4978709 : Blo 2211435 4978709 := bbase (se 6 (by rfl) ⟨116688, by rfl⟩ : syracuseStep 4978709 = 233377) (by norm_num)
theorem B3319139 : Blo 2211435 3319139 := bstep (se 1 (by rfl) ⟨2489354, by rfl⟩ : syracuseStep 3319139 = 4978709) B4978709
theorem B2212759 : Blo 2211435 2212759 := bstep (se 1 (by rfl) ⟨1659569, by rfl⟩ : syracuseStep 2212759 = 3319139) B3319139
theorem B8401589 : Blo 2211435 8401589 := bbase (se 5 (by rfl) ⟨393824, by rfl⟩ : syracuseStep 8401589 = 787649) (by norm_num)
theorem B5601059 : Blo 2211435 5601059 := bstep (se 1 (by rfl) ⟨4200794, by rfl⟩ : syracuseStep 5601059 = 8401589) B8401589
theorem B3734039 : Blo 2211435 3734039 := bstep (se 1 (by rfl) ⟨2800529, by rfl⟩ : syracuseStep 3734039 = 5601059) B5601059
theorem B2489359 : Blo 2211435 2489359 := bstep (se 1 (by rfl) ⟨1867019, by rfl⟩ : syracuseStep 2489359 = 3734039) B3734039
theorem B3319145 : Blo 2211435 3319145 := bstep (se 2 (by rfl) ⟨1244679, by rfl⟩ : syracuseStep 3319145 = 2489359) B2489359
theorem B2212763 : Blo 2211435 2212763 := bstep (se 1 (by rfl) ⟨1659572, by rfl⟩ : syracuseStep 2212763 = 3319145) B3319145
theorem B4485917 : Blo 2211435 4485917 := bbase (se 3 (by rfl) ⟨841109, by rfl⟩ : syracuseStep 4485917 = 1682219) (by norm_num)
theorem B2990611 : Blo 2211435 2990611 := bstep (se 1 (by rfl) ⟨2242958, by rfl⟩ : syracuseStep 2990611 = 4485917) B4485917
theorem B3987481 : Blo 2211435 3987481 := bstep (se 2 (by rfl) ⟨1495305, by rfl⟩ : syracuseStep 3987481 = 2990611) B2990611
theorem B5316641 : Blo 2211435 5316641 := bstep (se 2 (by rfl) ⟨1993740, by rfl⟩ : syracuseStep 5316641 = 3987481) B3987481
theorem B3544427 : Blo 2211435 3544427 := bstep (se 1 (by rfl) ⟨2658320, by rfl⟩ : syracuseStep 3544427 = 5316641) B5316641
theorem B2362951 : Blo 2211435 2362951 := bstep (se 1 (by rfl) ⟨1772213, by rfl⟩ : syracuseStep 2362951 = 3544427) B3544427
theorem B12602405 : Blo 2211435 12602405 := bstep (se 4 (by rfl) ⟨1181475, by rfl⟩ : syracuseStep 12602405 = 2362951) B2362951
theorem B8401603 : Blo 2211435 8401603 := bstep (se 1 (by rfl) ⟨6301202, by rfl⟩ : syracuseStep 8401603 = 12602405) B12602405
theorem B11202137 : Blo 2211435 11202137 := bstep (se 2 (by rfl) ⟨4200801, by rfl⟩ : syracuseStep 11202137 = 8401603) B8401603
theorem B7468091 : Blo 2211435 7468091 := bstep (se 1 (by rfl) ⟨5601068, by rfl⟩ : syracuseStep 7468091 = 11202137) B11202137
theorem B4978727 : Blo 2211435 4978727 := bstep (se 1 (by rfl) ⟨3734045, by rfl⟩ : syracuseStep 4978727 = 7468091) B7468091
theorem B3319151 : Blo 2211435 3319151 := bstep (se 1 (by rfl) ⟨2489363, by rfl⟩ : syracuseStep 3319151 = 4978727) B4978727
theorem B2212767 : Blo 2211435 2212767 := bstep (se 1 (by rfl) ⟨1659575, by rfl⟩ : syracuseStep 2212767 = 3319151) B3319151
theorem B3319157 : Blo 2211435 3319157 := bbase (se 5 (by rfl) ⟨155585, by rfl⟩ : syracuseStep 3319157 = 311171) (by norm_num)
theorem B2212771 : Blo 2211435 2212771 := bstep (se 1 (by rfl) ⟨1659578, by rfl⟩ : syracuseStep 2212771 = 3319157) B3319157
theorem B3150613 : Blo 2211435 3150613 := bbase (se 6 (by rfl) ⟨73842, by rfl⟩ : syracuseStep 3150613 = 147685) (by norm_num)
theorem B4200817 : Blo 2211435 4200817 := bstep (se 2 (by rfl) ⟨1575306, by rfl⟩ : syracuseStep 4200817 = 3150613) B3150613
theorem B5601089 : Blo 2211435 5601089 := bstep (se 2 (by rfl) ⟨2100408, by rfl⟩ : syracuseStep 5601089 = 4200817) B4200817
theorem B3734059 : Blo 2211435 3734059 := bstep (se 1 (by rfl) ⟨2800544, by rfl⟩ : syracuseStep 3734059 = 5601089) B5601089
theorem B4978745 : Blo 2211435 4978745 := bstep (se 2 (by rfl) ⟨1867029, by rfl⟩ : syracuseStep 4978745 = 3734059) B3734059
theorem B3319163 : Blo 2211435 3319163 := bstep (se 1 (by rfl) ⟨2489372, by rfl⟩ : syracuseStep 3319163 = 4978745) B4978745
theorem B2212775 : Blo 2211435 2212775 := bstep (se 1 (by rfl) ⟨1659581, by rfl⟩ : syracuseStep 2212775 = 3319163) B3319163
theorem B2489377 : Blo 2211435 2489377 := bbase (se 2 (by rfl) ⟨933516, by rfl⟩ : syracuseStep 2489377 = 1867033) (by norm_num)
theorem B3319169 : Blo 2211435 3319169 := bstep (se 2 (by rfl) ⟨1244688, by rfl⟩ : syracuseStep 3319169 = 2489377) B2489377
theorem B2212779 : Blo 2211435 2212779 := bstep (se 1 (by rfl) ⟨1659584, by rfl⟩ : syracuseStep 2212779 = 3319169) B3319169
theorem B5601109 : Blo 2211435 5601109 := bbase (se 9 (by rfl) ⟨16409, by rfl⟩ : syracuseStep 5601109 = 32819) (by norm_num)
theorem B7468145 : Blo 2211435 7468145 := bstep (se 2 (by rfl) ⟨2800554, by rfl⟩ : syracuseStep 7468145 = 5601109) B5601109
theorem B4978763 : Blo 2211435 4978763 := bstep (se 1 (by rfl) ⟨3734072, by rfl⟩ : syracuseStep 4978763 = 7468145) B7468145
theorem B3319175 : Blo 2211435 3319175 := bstep (se 1 (by rfl) ⟨2489381, by rfl⟩ : syracuseStep 3319175 = 4978763) B4978763
theorem B2212783 : Blo 2211435 2212783 := bstep (se 1 (by rfl) ⟨1659587, by rfl⟩ : syracuseStep 2212783 = 3319175) B3319175
theorem B3319181 : Blo 2211435 3319181 := bbase (se 3 (by rfl) ⟨622346, by rfl⟩ : syracuseStep 3319181 = 1244693) (by norm_num)
theorem B2212787 : Blo 2211435 2212787 := bstep (se 1 (by rfl) ⟨1659590, by rfl⟩ : syracuseStep 2212787 = 3319181) B3319181
theorem B4978781 : Blo 2211435 4978781 := bbase (se 3 (by rfl) ⟨933521, by rfl⟩ : syracuseStep 4978781 = 1867043) (by norm_num)
theorem B3319187 : Blo 2211435 3319187 := bstep (se 1 (by rfl) ⟨2489390, by rfl⟩ : syracuseStep 3319187 = 4978781) B4978781
theorem B2212791 : Blo 2211435 2212791 := bstep (se 1 (by rfl) ⟨1659593, by rfl⟩ : syracuseStep 2212791 = 3319187) B3319187
theorem B3734093 : Blo 2211435 3734093 := bbase (se 3 (by rfl) ⟨700142, by rfl⟩ : syracuseStep 3734093 = 1400285) (by norm_num)
theorem B2489395 : Blo 2211435 2489395 := bstep (se 1 (by rfl) ⟨1867046, by rfl⟩ : syracuseStep 2489395 = 3734093) B3734093
theorem B3319193 : Blo 2211435 3319193 := bstep (se 2 (by rfl) ⟨1244697, by rfl⟩ : syracuseStep 3319193 = 2489395) B2489395
theorem B2212795 : Blo 2211435 2212795 := bstep (se 1 (by rfl) ⟨1659596, by rfl⟩ : syracuseStep 2212795 = 3319193) B3319193
theorem B11962613 : Blo 2211435 11962613 := bbase (se 5 (by rfl) ⟨560747, by rfl⟩ : syracuseStep 11962613 = 1121495) (by norm_num)
theorem B31900301 : Blo 2211435 31900301 := bstep (se 3 (by rfl) ⟨5981306, by rfl⟩ : syracuseStep 31900301 = 11962613) B11962613
theorem B21266867 : Blo 2211435 21266867 := bstep (se 1 (by rfl) ⟨15950150, by rfl⟩ : syracuseStep 21266867 = 31900301) B31900301
theorem B14177911 : Blo 2211435 14177911 := bstep (se 1 (by rfl) ⟨10633433, by rfl⟩ : syracuseStep 14177911 = 21266867) B21266867
theorem B18903881 : Blo 2211435 18903881 := bstep (se 2 (by rfl) ⟨7088955, by rfl⟩ : syracuseStep 18903881 = 14177911) B14177911
theorem B12602587 : Blo 2211435 12602587 := bstep (se 1 (by rfl) ⟨9451940, by rfl⟩ : syracuseStep 12602587 = 18903881) B18903881
theorem B16803449 : Blo 2211435 16803449 := bstep (se 2 (by rfl) ⟨6301293, by rfl⟩ : syracuseStep 16803449 = 12602587) B12602587
theorem B11202299 : Blo 2211435 11202299 := bstep (se 1 (by rfl) ⟨8401724, by rfl⟩ : syracuseStep 11202299 = 16803449) B16803449
theorem B7468199 : Blo 2211435 7468199 := bstep (se 1 (by rfl) ⟨5601149, by rfl⟩ : syracuseStep 7468199 = 11202299) B11202299
theorem B4978799 : Blo 2211435 4978799 := bstep (se 1 (by rfl) ⟨3734099, by rfl⟩ : syracuseStep 4978799 = 7468199) B7468199
theorem B3319199 : Blo 2211435 3319199 := bstep (se 1 (by rfl) ⟨2489399, by rfl⟩ : syracuseStep 3319199 = 4978799) B4978799
theorem B2212799 : Blo 2211435 2212799 := bstep (se 1 (by rfl) ⟨1659599, by rfl⟩ : syracuseStep 2212799 = 3319199) B3319199
theorem B3319205 : Blo 2211435 3319205 := bbase (se 4 (by rfl) ⟨311175, by rfl⟩ : syracuseStep 3319205 = 622351) (by norm_num)
theorem B2212803 : Blo 2211435 2212803 := bstep (se 1 (by rfl) ⟨1659602, by rfl⟩ : syracuseStep 2212803 = 3319205) B3319205
theorem B2800585 : Blo 2211435 2800585 := bbase (se 2 (by rfl) ⟨1050219, by rfl⟩ : syracuseStep 2800585 = 2100439) (by norm_num)
theorem B3734113 : Blo 2211435 3734113 := bstep (se 2 (by rfl) ⟨1400292, by rfl⟩ : syracuseStep 3734113 = 2800585) B2800585
theorem B4978817 : Blo 2211435 4978817 := bstep (se 2 (by rfl) ⟨1867056, by rfl⟩ : syracuseStep 4978817 = 3734113) B3734113
theorem B3319211 : Blo 2211435 3319211 := bstep (se 1 (by rfl) ⟨2489408, by rfl⟩ : syracuseStep 3319211 = 4978817) B4978817
theorem B2212807 : Blo 2211435 2212807 := bstep (se 1 (by rfl) ⟨1659605, by rfl⟩ : syracuseStep 2212807 = 3319211) B3319211
theorem B2489413 : Blo 2211435 2489413 := bbase (se 4 (by rfl) ⟨233382, by rfl⟩ : syracuseStep 2489413 = 466765) (by norm_num)
theorem B3319217 : Blo 2211435 3319217 := bstep (se 2 (by rfl) ⟨1244706, by rfl⟩ : syracuseStep 3319217 = 2489413) B2489413
theorem B2212811 : Blo 2211435 2212811 := bstep (se 1 (by rfl) ⟨1659608, by rfl⟩ : syracuseStep 2212811 = 3319217) B3319217
theorem B4200893 : Blo 2211435 4200893 := bbase (se 3 (by rfl) ⟨787667, by rfl⟩ : syracuseStep 4200893 = 1575335) (by norm_num)
theorem B2800595 : Blo 2211435 2800595 := bstep (se 1 (by rfl) ⟨2100446, by rfl⟩ : syracuseStep 2800595 = 4200893) B4200893
theorem B7468253 : Blo 2211435 7468253 := bstep (se 3 (by rfl) ⟨1400297, by rfl⟩ : syracuseStep 7468253 = 2800595) B2800595
theorem B4978835 : Blo 2211435 4978835 := bstep (se 1 (by rfl) ⟨3734126, by rfl⟩ : syracuseStep 4978835 = 7468253) B7468253
theorem B3319223 : Blo 2211435 3319223 := bstep (se 1 (by rfl) ⟨2489417, by rfl⟩ : syracuseStep 3319223 = 4978835) B4978835
theorem B2212815 : Blo 2211435 2212815 := bstep (se 1 (by rfl) ⟨1659611, by rfl⟩ : syracuseStep 2212815 = 3319223) B3319223
theorem B3319229 : Blo 2211435 3319229 := bbase (se 3 (by rfl) ⟨622355, by rfl⟩ : syracuseStep 3319229 = 1244711) (by norm_num)
theorem B2212819 : Blo 2211435 2212819 := bstep (se 1 (by rfl) ⟨1659614, by rfl⟩ : syracuseStep 2212819 = 3319229) B3319229
theorem B4978853 : Blo 2211435 4978853 := bbase (se 4 (by rfl) ⟨466767, by rfl⟩ : syracuseStep 4978853 = 933535) (by norm_num)
theorem B3319235 : Blo 2211435 3319235 := bstep (se 1 (by rfl) ⟨2489426, by rfl⟩ : syracuseStep 3319235 = 4978853) B4978853
theorem B2212823 : Blo 2211435 2212823 := bstep (se 1 (by rfl) ⟨1659617, by rfl⟩ : syracuseStep 2212823 = 3319235) B3319235
theorem B5601221 : Blo 2211435 5601221 := bbase (se 4 (by rfl) ⟨525114, by rfl⟩ : syracuseStep 5601221 = 1050229) (by norm_num)
theorem B3734147 : Blo 2211435 3734147 := bstep (se 1 (by rfl) ⟨2800610, by rfl⟩ : syracuseStep 3734147 = 5601221) B5601221
theorem B2489431 : Blo 2211435 2489431 := bstep (se 1 (by rfl) ⟨1867073, by rfl⟩ : syracuseStep 2489431 = 3734147) B3734147
theorem B3319241 : Blo 2211435 3319241 := bstep (se 2 (by rfl) ⟨1244715, by rfl⟩ : syracuseStep 3319241 = 2489431) B2489431
theorem B2212827 : Blo 2211435 2212827 := bstep (se 1 (by rfl) ⟨1659620, by rfl⟩ : syracuseStep 2212827 = 3319241) B3319241
theorem B10633589 : Blo 2211435 10633589 := bbase (se 5 (by rfl) ⟨498449, by rfl⟩ : syracuseStep 10633589 = 996899) (by norm_num)
theorem B7089059 : Blo 2211435 7089059 := bstep (se 1 (by rfl) ⟨5316794, by rfl⟩ : syracuseStep 7089059 = 10633589) B10633589
theorem B4726039 : Blo 2211435 4726039 := bstep (se 1 (by rfl) ⟨3544529, by rfl⟩ : syracuseStep 4726039 = 7089059) B7089059
theorem B6301385 : Blo 2211435 6301385 := bstep (se 2 (by rfl) ⟨2363019, by rfl⟩ : syracuseStep 6301385 = 4726039) B4726039
theorem B4200923 : Blo 2211435 4200923 := bstep (se 1 (by rfl) ⟨3150692, by rfl⟩ : syracuseStep 4200923 = 6301385) B6301385
theorem B11202461 : Blo 2211435 11202461 := bstep (se 3 (by rfl) ⟨2100461, by rfl⟩ : syracuseStep 11202461 = 4200923) B4200923
theorem B7468307 : Blo 2211435 7468307 := bstep (se 1 (by rfl) ⟨5601230, by rfl⟩ : syracuseStep 7468307 = 11202461) B11202461
theorem B4978871 : Blo 2211435 4978871 := bstep (se 1 (by rfl) ⟨3734153, by rfl⟩ : syracuseStep 4978871 = 7468307) B7468307
theorem B3319247 : Blo 2211435 3319247 := bstep (se 1 (by rfl) ⟨2489435, by rfl⟩ : syracuseStep 3319247 = 4978871) B4978871
theorem B2212831 : Blo 2211435 2212831 := bstep (se 1 (by rfl) ⟨1659623, by rfl⟩ : syracuseStep 2212831 = 3319247) B3319247
theorem B3319253 : Blo 2211435 3319253 := bbase (se 7 (by rfl) ⟨38897, by rfl⟩ : syracuseStep 3319253 = 77795) (by norm_num)
theorem B2212835 : Blo 2211435 2212835 := bstep (se 1 (by rfl) ⟨1659626, by rfl⟩ : syracuseStep 2212835 = 3319253) B3319253
theorem B8401877 : Blo 2211435 8401877 := bbase (se 7 (by rfl) ⟨98459, by rfl⟩ : syracuseStep 8401877 = 196919) (by norm_num)
theorem B5601251 : Blo 2211435 5601251 := bstep (se 1 (by rfl) ⟨4200938, by rfl⟩ : syracuseStep 5601251 = 8401877) B8401877
theorem B3734167 : Blo 2211435 3734167 := bstep (se 1 (by rfl) ⟨2800625, by rfl⟩ : syracuseStep 3734167 = 5601251) B5601251
theorem B4978889 : Blo 2211435 4978889 := bstep (se 2 (by rfl) ⟨1867083, by rfl⟩ : syracuseStep 4978889 = 3734167) B3734167
theorem B3319259 : Blo 2211435 3319259 := bstep (se 1 (by rfl) ⟨2489444, by rfl⟩ : syracuseStep 3319259 = 4978889) B4978889
theorem B2212839 : Blo 2211435 2212839 := bstep (se 1 (by rfl) ⟨1659629, by rfl⟩ : syracuseStep 2212839 = 3319259) B3319259
theorem B2489449 : Blo 2211435 2489449 := bbase (se 2 (by rfl) ⟨933543, by rfl⟩ : syracuseStep 2489449 = 1867087) (by norm_num)
theorem B3319265 : Blo 2211435 3319265 := bstep (se 2 (by rfl) ⟨1244724, by rfl⟩ : syracuseStep 3319265 = 2489449) B2489449
theorem B2212843 : Blo 2211435 2212843 := bstep (se 1 (by rfl) ⟨1659632, by rfl⟩ : syracuseStep 2212843 = 3319265) B3319265
theorem B12949109 : Blo 2211435 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B8632739 : Blo 2211435 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B5755159 : Blo 2211435 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B7673545 : Blo 2211435 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B10231393 : Blo 2211435 10231393 := bstep (se 2 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 10231393 = 7673545) B7673545
theorem B13641857 : Blo 2211435 13641857 := bstep (se 2 (by rfl) ⟨5115696, by rfl⟩ : syracuseStep 13641857 = 10231393) B10231393
theorem B9094571 : Blo 2211435 9094571 := bstep (se 1 (by rfl) ⟨6820928, by rfl⟩ : syracuseStep 9094571 = 13641857) B13641857
theorem B6063047 : Blo 2211435 6063047 := bstep (se 1 (by rfl) ⟨4547285, by rfl⟩ : syracuseStep 6063047 = 9094571) B9094571
theorem B4042031 : Blo 2211435 4042031 := bstep (se 1 (by rfl) ⟨3031523, by rfl⟩ : syracuseStep 4042031 = 6063047) B6063047
theorem B43114997 : Blo 2211435 43114997 := bstep (se 5 (by rfl) ⟨2021015, by rfl⟩ : syracuseStep 43114997 = 4042031) B4042031
theorem B28743331 : Blo 2211435 28743331 := bstep (se 1 (by rfl) ⟨21557498, by rfl⟩ : syracuseStep 28743331 = 43114997) B43114997
theorem B38324441 : Blo 2211435 38324441 := bstep (se 2 (by rfl) ⟨14371665, by rfl⟩ : syracuseStep 38324441 = 28743331) B28743331
theorem B25549627 : Blo 2211435 25549627 := bstep (se 1 (by rfl) ⟨19162220, by rfl⟩ : syracuseStep 25549627 = 38324441) B38324441
theorem B34066169 : Blo 2211435 34066169 := bstep (se 2 (by rfl) ⟨12774813, by rfl⟩ : syracuseStep 34066169 = 25549627) B25549627
theorem B22710779 : Blo 2211435 22710779 := bstep (se 1 (by rfl) ⟨17033084, by rfl⟩ : syracuseStep 22710779 = 34066169) B34066169
theorem B15140519 : Blo 2211435 15140519 := bstep (se 1 (by rfl) ⟨11355389, by rfl⟩ : syracuseStep 15140519 = 22710779) B22710779
theorem B10093679 : Blo 2211435 10093679 := bstep (se 1 (by rfl) ⟨7570259, by rfl⟩ : syracuseStep 10093679 = 15140519) B15140519
theorem B6729119 : Blo 2211435 6729119 := bstep (se 1 (by rfl) ⟨5046839, by rfl⟩ : syracuseStep 6729119 = 10093679) B10093679
theorem B4486079 : Blo 2211435 4486079 := bstep (se 1 (by rfl) ⟨3364559, by rfl⟩ : syracuseStep 4486079 = 6729119) B6729119
theorem B2990719 : Blo 2211435 2990719 := bstep (se 1 (by rfl) ⟨2243039, by rfl⟩ : syracuseStep 2990719 = 4486079) B4486079
theorem B3987625 : Blo 2211435 3987625 := bstep (se 2 (by rfl) ⟨1495359, by rfl⟩ : syracuseStep 3987625 = 2990719) B2990719
theorem B5316833 : Blo 2211435 5316833 := bstep (se 2 (by rfl) ⟨1993812, by rfl⟩ : syracuseStep 5316833 = 3987625) B3987625
theorem B3544555 : Blo 2211435 3544555 := bstep (se 1 (by rfl) ⟨2658416, by rfl⟩ : syracuseStep 3544555 = 5316833) B5316833
theorem B4726073 : Blo 2211435 4726073 := bstep (se 2 (by rfl) ⟨1772277, by rfl⟩ : syracuseStep 4726073 = 3544555) B3544555
theorem B12602861 : Blo 2211435 12602861 := bstep (se 3 (by rfl) ⟨2363036, by rfl⟩ : syracuseStep 12602861 = 4726073) B4726073
theorem B8401907 : Blo 2211435 8401907 := bstep (se 1 (by rfl) ⟨6301430, by rfl⟩ : syracuseStep 8401907 = 12602861) B12602861
theorem B5601271 : Blo 2211435 5601271 := bstep (se 1 (by rfl) ⟨4200953, by rfl⟩ : syracuseStep 5601271 = 8401907) B8401907
theorem B7468361 : Blo 2211435 7468361 := bstep (se 2 (by rfl) ⟨2800635, by rfl⟩ : syracuseStep 7468361 = 5601271) B5601271
theorem B4978907 : Blo 2211435 4978907 := bstep (se 1 (by rfl) ⟨3734180, by rfl⟩ : syracuseStep 4978907 = 7468361) B7468361
theorem B3319271 : Blo 2211435 3319271 := bstep (se 1 (by rfl) ⟨2489453, by rfl⟩ : syracuseStep 3319271 = 4978907) B4978907
theorem B2212847 : Blo 2211435 2212847 := bstep (se 1 (by rfl) ⟨1659635, by rfl⟩ : syracuseStep 2212847 = 3319271) B3319271
theorem B3319277 : Blo 2211435 3319277 := bbase (se 3 (by rfl) ⟨622364, by rfl⟩ : syracuseStep 3319277 = 1244729) (by norm_num)
theorem B2212851 : Blo 2211435 2212851 := bstep (se 1 (by rfl) ⟨1659638, by rfl⟩ : syracuseStep 2212851 = 3319277) B3319277
theorem B4978925 : Blo 2211435 4978925 := bbase (se 3 (by rfl) ⟨933548, by rfl⟩ : syracuseStep 4978925 = 1867097) (by norm_num)
theorem B3319283 : Blo 2211435 3319283 := bstep (se 1 (by rfl) ⟨2489462, by rfl⟩ : syracuseStep 3319283 = 4978925) B4978925
theorem B2212855 : Blo 2211435 2212855 := bstep (se 1 (by rfl) ⟨1659641, by rfl⟩ : syracuseStep 2212855 = 3319283) B3319283
theorem B3150733 : Blo 2211435 3150733 := bbase (se 3 (by rfl) ⟨590762, by rfl⟩ : syracuseStep 3150733 = 1181525) (by norm_num)
theorem B4200977 : Blo 2211435 4200977 := bstep (se 2 (by rfl) ⟨1575366, by rfl⟩ : syracuseStep 4200977 = 3150733) B3150733
theorem B2800651 : Blo 2211435 2800651 := bstep (se 1 (by rfl) ⟨2100488, by rfl⟩ : syracuseStep 2800651 = 4200977) B4200977
theorem B3734201 : Blo 2211435 3734201 := bstep (se 2 (by rfl) ⟨1400325, by rfl⟩ : syracuseStep 3734201 = 2800651) B2800651
theorem B2489467 : Blo 2211435 2489467 := bstep (se 1 (by rfl) ⟨1867100, by rfl⟩ : syracuseStep 2489467 = 3734201) B3734201
theorem B3319289 : Blo 2211435 3319289 := bstep (se 2 (by rfl) ⟨1244733, by rfl⟩ : syracuseStep 3319289 = 2489467) B2489467
theorem B2212859 : Blo 2211435 2212859 := bstep (se 1 (by rfl) ⟨1659644, by rfl⟩ : syracuseStep 2212859 = 3319289) B3319289
theorem B5677733 : Blo 2211435 5677733 := bbase (se 4 (by rfl) ⟨532287, by rfl⟩ : syracuseStep 5677733 = 1064575) (by norm_num)
theorem B15140621 : Blo 2211435 15140621 := bstep (se 3 (by rfl) ⟨2838866, by rfl⟩ : syracuseStep 15140621 = 5677733) B5677733
theorem B10093747 : Blo 2211435 10093747 := bstep (se 1 (by rfl) ⟨7570310, by rfl⟩ : syracuseStep 10093747 = 15140621) B15140621
theorem B13458329 : Blo 2211435 13458329 := bstep (se 2 (by rfl) ⟨5046873, by rfl⟩ : syracuseStep 13458329 = 10093747) B10093747
theorem B8972219 : Blo 2211435 8972219 := bstep (se 1 (by rfl) ⟨6729164, by rfl⟩ : syracuseStep 8972219 = 13458329) B13458329
theorem B23925917 : Blo 2211435 23925917 := bstep (se 3 (by rfl) ⟨4486109, by rfl⟩ : syracuseStep 23925917 = 8972219) B8972219
theorem B15950611 : Blo 2211435 15950611 := bstep (se 1 (by rfl) ⟨11962958, by rfl⟩ : syracuseStep 15950611 = 23925917) B23925917
theorem B85069925 : Blo 2211435 85069925 := bstep (se 4 (by rfl) ⟨7975305, by rfl⟩ : syracuseStep 85069925 = 15950611) B15950611
theorem B56713283 : Blo 2211435 56713283 := bstep (se 1 (by rfl) ⟨42534962, by rfl⟩ : syracuseStep 56713283 = 85069925) B85069925
theorem B37808855 : Blo 2211435 37808855 := bstep (se 1 (by rfl) ⟨28356641, by rfl⟩ : syracuseStep 37808855 = 56713283) B56713283
theorem B25205903 : Blo 2211435 25205903 := bstep (se 1 (by rfl) ⟨18904427, by rfl⟩ : syracuseStep 25205903 = 37808855) B37808855
theorem B16803935 : Blo 2211435 16803935 := bstep (se 1 (by rfl) ⟨12602951, by rfl⟩ : syracuseStep 16803935 = 25205903) B25205903
theorem B11202623 : Blo 2211435 11202623 := bstep (se 1 (by rfl) ⟨8401967, by rfl⟩ : syracuseStep 11202623 = 16803935) B16803935
theorem B7468415 : Blo 2211435 7468415 := bstep (se 1 (by rfl) ⟨5601311, by rfl⟩ : syracuseStep 7468415 = 11202623) B11202623
theorem B4978943 : Blo 2211435 4978943 := bstep (se 1 (by rfl) ⟨3734207, by rfl⟩ : syracuseStep 4978943 = 7468415) B7468415
theorem B3319295 : Blo 2211435 3319295 := bstep (se 1 (by rfl) ⟨2489471, by rfl⟩ : syracuseStep 3319295 = 4978943) B4978943
theorem B2212863 : Blo 2211435 2212863 := bstep (se 1 (by rfl) ⟨1659647, by rfl⟩ : syracuseStep 2212863 = 3319295) B3319295
theorem B3319301 : Blo 2211435 3319301 := bbase (se 4 (by rfl) ⟨311184, by rfl⟩ : syracuseStep 3319301 = 622369) (by norm_num)
theorem B2212867 : Blo 2211435 2212867 := bstep (se 1 (by rfl) ⟨1659650, by rfl⟩ : syracuseStep 2212867 = 3319301) B3319301
theorem B3734221 : Blo 2211435 3734221 := bbase (se 3 (by rfl) ⟨700166, by rfl⟩ : syracuseStep 3734221 = 1400333) (by norm_num)
theorem B4978961 : Blo 2211435 4978961 := bstep (se 2 (by rfl) ⟨1867110, by rfl⟩ : syracuseStep 4978961 = 3734221) B3734221
theorem B3319307 : Blo 2211435 3319307 := bstep (se 1 (by rfl) ⟨2489480, by rfl⟩ : syracuseStep 3319307 = 4978961) B4978961
theorem B2212871 : Blo 2211435 2212871 := bstep (se 1 (by rfl) ⟨1659653, by rfl⟩ : syracuseStep 2212871 = 3319307) B3319307
theorem B2489485 : Blo 2211435 2489485 := bbase (se 3 (by rfl) ⟨466778, by rfl⟩ : syracuseStep 2489485 = 933557) (by norm_num)
theorem B3319313 : Blo 2211435 3319313 := bstep (se 2 (by rfl) ⟨1244742, by rfl⟩ : syracuseStep 3319313 = 2489485) B2489485
theorem B2212875 : Blo 2211435 2212875 := bstep (se 1 (by rfl) ⟨1659656, by rfl⟩ : syracuseStep 2212875 = 3319313) B3319313
theorem B7468469 : Blo 2211435 7468469 := bbase (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) (by norm_num)
theorem B4978979 : Blo 2211435 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B3319319 : Blo 2211435 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2212879 : Blo 2211435 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B3319325 : Blo 2211435 3319325 := bbase (se 3 (by rfl) ⟨622373, by rfl⟩ : syracuseStep 3319325 = 1244747) (by norm_num)
theorem B2212883 : Blo 2211435 2212883 := bstep (se 1 (by rfl) ⟨1659662, by rfl⟩ : syracuseStep 2212883 = 3319325) B3319325
theorem B4978997 : Blo 2211435 4978997 := bbase (se 5 (by rfl) ⟨233390, by rfl⟩ : syracuseStep 4978997 = 466781) (by norm_num)
theorem B3319331 : Blo 2211435 3319331 := bstep (se 1 (by rfl) ⟨2489498, by rfl⟩ : syracuseStep 3319331 = 4978997) B4978997
theorem B2212887 : Blo 2211435 2212887 := bstep (se 1 (by rfl) ⟨1659665, by rfl⟩ : syracuseStep 2212887 = 3319331) B3319331
theorem B10093877 : Blo 2211435 10093877 := bbase (se 5 (by rfl) ⟨473150, by rfl⟩ : syracuseStep 10093877 = 946301) (by norm_num)
theorem B6729251 : Blo 2211435 6729251 := bstep (se 1 (by rfl) ⟨5046938, by rfl⟩ : syracuseStep 6729251 = 10093877) B10093877
theorem B17944669 : Blo 2211435 17944669 := bstep (se 3 (by rfl) ⟨3364625, by rfl⟩ : syracuseStep 17944669 = 6729251) B6729251
theorem B23926225 : Blo 2211435 23926225 := bstep (se 2 (by rfl) ⟨8972334, by rfl⟩ : syracuseStep 23926225 = 17944669) B17944669
theorem B31901633 : Blo 2211435 31901633 := bstep (se 2 (by rfl) ⟨11963112, by rfl⟩ : syracuseStep 31901633 = 23926225) B23926225
theorem B21267755 : Blo 2211435 21267755 := bstep (se 1 (by rfl) ⟨15950816, by rfl⟩ : syracuseStep 21267755 = 31901633) B31901633
theorem B14178503 : Blo 2211435 14178503 := bstep (se 1 (by rfl) ⟨10633877, by rfl⟩ : syracuseStep 14178503 = 21267755) B21267755
theorem B9452335 : Blo 2211435 9452335 := bstep (se 1 (by rfl) ⟨7089251, by rfl⟩ : syracuseStep 9452335 = 14178503) B14178503
theorem B12603113 : Blo 2211435 12603113 := bstep (se 2 (by rfl) ⟨4726167, by rfl⟩ : syracuseStep 12603113 = 9452335) B9452335
theorem B8402075 : Blo 2211435 8402075 := bstep (se 1 (by rfl) ⟨6301556, by rfl⟩ : syracuseStep 8402075 = 12603113) B12603113
theorem B5601383 : Blo 2211435 5601383 := bstep (se 1 (by rfl) ⟨4201037, by rfl⟩ : syracuseStep 5601383 = 8402075) B8402075
theorem B3734255 : Blo 2211435 3734255 := bstep (se 1 (by rfl) ⟨2800691, by rfl⟩ : syracuseStep 3734255 = 5601383) B5601383
theorem B2489503 : Blo 2211435 2489503 := bstep (se 1 (by rfl) ⟨1867127, by rfl⟩ : syracuseStep 2489503 = 3734255) B3734255
theorem B3319337 : Blo 2211435 3319337 := bstep (se 2 (by rfl) ⟨1244751, by rfl⟩ : syracuseStep 3319337 = 2489503) B2489503
theorem B2212891 : Blo 2211435 2212891 := bstep (se 1 (by rfl) ⟨1659668, by rfl⟩ : syracuseStep 2212891 = 3319337) B3319337
theorem B2694745 : Blo 2211435 2694745 := bbase (se 2 (by rfl) ⟨1010529, by rfl⟩ : syracuseStep 2694745 = 2021059) (by norm_num)
theorem B3592993 : Blo 2211435 3592993 := bstep (se 2 (by rfl) ⟨1347372, by rfl⟩ : syracuseStep 3592993 = 2694745) B2694745
theorem B4790657 : Blo 2211435 4790657 := bstep (se 2 (by rfl) ⟨1796496, by rfl⟩ : syracuseStep 4790657 = 3592993) B3592993
theorem B12775085 : Blo 2211435 12775085 := bstep (se 3 (by rfl) ⟨2395328, by rfl⟩ : syracuseStep 12775085 = 4790657) B4790657
theorem B8516723 : Blo 2211435 8516723 := bstep (se 1 (by rfl) ⟨6387542, by rfl⟩ : syracuseStep 8516723 = 12775085) B12775085
theorem B22711261 : Blo 2211435 22711261 := bstep (se 3 (by rfl) ⟨4258361, by rfl⟩ : syracuseStep 22711261 = 8516723) B8516723
theorem B30281681 : Blo 2211435 30281681 := bstep (se 2 (by rfl) ⟨11355630, by rfl⟩ : syracuseStep 30281681 = 22711261) B22711261
theorem B20187787 : Blo 2211435 20187787 := bstep (se 1 (by rfl) ⟨15140840, by rfl⟩ : syracuseStep 20187787 = 30281681) B30281681
theorem B26917049 : Blo 2211435 26917049 := bstep (se 2 (by rfl) ⟨10093893, by rfl⟩ : syracuseStep 26917049 = 20187787) B20187787
theorem B71778797 : Blo 2211435 71778797 := bstep (se 3 (by rfl) ⟨13458524, by rfl⟩ : syracuseStep 71778797 = 26917049) B26917049
theorem B47852531 : Blo 2211435 47852531 := bstep (se 1 (by rfl) ⟨35889398, by rfl⟩ : syracuseStep 47852531 = 71778797) B71778797
theorem B31901687 : Blo 2211435 31901687 := bstep (se 1 (by rfl) ⟨23926265, by rfl⟩ : syracuseStep 31901687 = 47852531) B47852531
theorem B21267791 : Blo 2211435 21267791 := bstep (se 1 (by rfl) ⟨15950843, by rfl⟩ : syracuseStep 21267791 = 31901687) B31901687
theorem B14178527 : Blo 2211435 14178527 := bstep (se 1 (by rfl) ⟨10633895, by rfl⟩ : syracuseStep 14178527 = 21267791) B21267791
theorem B9452351 : Blo 2211435 9452351 := bstep (se 1 (by rfl) ⟨7089263, by rfl⟩ : syracuseStep 9452351 = 14178527) B14178527
theorem B6301567 : Blo 2211435 6301567 := bstep (se 1 (by rfl) ⟨4726175, by rfl⟩ : syracuseStep 6301567 = 9452351) B9452351
theorem B8402089 : Blo 2211435 8402089 := bstep (se 2 (by rfl) ⟨3150783, by rfl⟩ : syracuseStep 8402089 = 6301567) B6301567
theorem B11202785 : Blo 2211435 11202785 := bstep (se 2 (by rfl) ⟨4201044, by rfl⟩ : syracuseStep 11202785 = 8402089) B8402089
theorem B7468523 : Blo 2211435 7468523 := bstep (se 1 (by rfl) ⟨5601392, by rfl⟩ : syracuseStep 7468523 = 11202785) B11202785
theorem B4979015 : Blo 2211435 4979015 := bstep (se 1 (by rfl) ⟨3734261, by rfl⟩ : syracuseStep 4979015 = 7468523) B7468523
theorem B3319343 : Blo 2211435 3319343 := bstep (se 1 (by rfl) ⟨2489507, by rfl⟩ : syracuseStep 3319343 = 4979015) B4979015
theorem B2212895 : Blo 2211435 2212895 := bstep (se 1 (by rfl) ⟨1659671, by rfl⟩ : syracuseStep 2212895 = 3319343) B3319343
theorem B3319349 : Blo 2211435 3319349 := bbase (se 5 (by rfl) ⟨155594, by rfl⟩ : syracuseStep 3319349 = 311189) (by norm_num)
theorem B2212899 : Blo 2211435 2212899 := bstep (se 1 (by rfl) ⟨1659674, by rfl⟩ : syracuseStep 2212899 = 3319349) B3319349
theorem B5601413 : Blo 2211435 5601413 := bbase (se 4 (by rfl) ⟨525132, by rfl⟩ : syracuseStep 5601413 = 1050265) (by norm_num)
theorem B3734275 : Blo 2211435 3734275 := bstep (se 1 (by rfl) ⟨2800706, by rfl⟩ : syracuseStep 3734275 = 5601413) B5601413
theorem B4979033 : Blo 2211435 4979033 := bstep (se 2 (by rfl) ⟨1867137, by rfl⟩ : syracuseStep 4979033 = 3734275) B3734275
theorem B3319355 : Blo 2211435 3319355 := bstep (se 1 (by rfl) ⟨2489516, by rfl⟩ : syracuseStep 3319355 = 4979033) B4979033
theorem B2212903 : Blo 2211435 2212903 := bstep (se 1 (by rfl) ⟨1659677, by rfl⟩ : syracuseStep 2212903 = 3319355) B3319355
theorem B2489521 : Blo 2211435 2489521 := bbase (se 2 (by rfl) ⟨933570, by rfl⟩ : syracuseStep 2489521 = 1867141) (by norm_num)
theorem B3319361 : Blo 2211435 3319361 := bstep (se 2 (by rfl) ⟨1244760, by rfl⟩ : syracuseStep 3319361 = 2489521) B2489521
theorem B2212907 : Blo 2211435 2212907 := bstep (se 1 (by rfl) ⟨1659680, by rfl⟩ : syracuseStep 2212907 = 3319361) B3319361
theorem B2363105 : Blo 2211435 2363105 := bbase (se 2 (by rfl) ⟨886164, by rfl⟩ : syracuseStep 2363105 = 1772329) (by norm_num)
theorem B6301613 : Blo 2211435 6301613 := bstep (se 3 (by rfl) ⟨1181552, by rfl⟩ : syracuseStep 6301613 = 2363105) B2363105
theorem B4201075 : Blo 2211435 4201075 := bstep (se 1 (by rfl) ⟨3150806, by rfl⟩ : syracuseStep 4201075 = 6301613) B6301613
theorem B5601433 : Blo 2211435 5601433 := bstep (se 2 (by rfl) ⟨2100537, by rfl⟩ : syracuseStep 5601433 = 4201075) B4201075
theorem B7468577 : Blo 2211435 7468577 := bstep (se 2 (by rfl) ⟨2800716, by rfl⟩ : syracuseStep 7468577 = 5601433) B5601433
theorem B4979051 : Blo 2211435 4979051 := bstep (se 1 (by rfl) ⟨3734288, by rfl⟩ : syracuseStep 4979051 = 7468577) B7468577
theorem B3319367 : Blo 2211435 3319367 := bstep (se 1 (by rfl) ⟨2489525, by rfl⟩ : syracuseStep 3319367 = 4979051) B4979051
theorem B2212911 : Blo 2211435 2212911 := bstep (se 1 (by rfl) ⟨1659683, by rfl⟩ : syracuseStep 2212911 = 3319367) B3319367
theorem B3319373 : Blo 2211435 3319373 := bbase (se 3 (by rfl) ⟨622382, by rfl⟩ : syracuseStep 3319373 = 1244765) (by norm_num)
theorem B2212915 : Blo 2211435 2212915 := bstep (se 1 (by rfl) ⟨1659686, by rfl⟩ : syracuseStep 2212915 = 3319373) B3319373
theorem B4979069 : Blo 2211435 4979069 := bbase (se 3 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 4979069 = 1867151) (by norm_num)
theorem B3319379 : Blo 2211435 3319379 := bstep (se 1 (by rfl) ⟨2489534, by rfl⟩ : syracuseStep 3319379 = 4979069) B4979069
theorem B2212919 : Blo 2211435 2212919 := bstep (se 1 (by rfl) ⟨1659689, by rfl⟩ : syracuseStep 2212919 = 3319379) B3319379
theorem B3734309 : Blo 2211435 3734309 := bbase (se 4 (by rfl) ⟨350091, by rfl⟩ : syracuseStep 3734309 = 700183) (by norm_num)
theorem B2489539 : Blo 2211435 2489539 := bstep (se 1 (by rfl) ⟨1867154, by rfl⟩ : syracuseStep 2489539 = 3734309) B3734309
theorem B3319385 : Blo 2211435 3319385 := bstep (se 2 (by rfl) ⟨1244769, by rfl⟩ : syracuseStep 3319385 = 2489539) B2489539
theorem B2212923 : Blo 2211435 2212923 := bstep (se 1 (by rfl) ⟨1659692, by rfl⟩ : syracuseStep 2212923 = 3319385) B3319385
theorem B3150829 : Blo 2211435 3150829 := bbase (se 3 (by rfl) ⟨590780, by rfl⟩ : syracuseStep 3150829 = 1181561) (by norm_num)
theorem B16804421 : Blo 2211435 16804421 := bstep (se 4 (by rfl) ⟨1575414, by rfl⟩ : syracuseStep 16804421 = 3150829) B3150829
theorem B11202947 : Blo 2211435 11202947 := bstep (se 1 (by rfl) ⟨8402210, by rfl⟩ : syracuseStep 11202947 = 16804421) B16804421
theorem B7468631 : Blo 2211435 7468631 := bstep (se 1 (by rfl) ⟨5601473, by rfl⟩ : syracuseStep 7468631 = 11202947) B11202947
theorem B4979087 : Blo 2211435 4979087 := bstep (se 1 (by rfl) ⟨3734315, by rfl⟩ : syracuseStep 4979087 = 7468631) B7468631
theorem B3319391 : Blo 2211435 3319391 := bstep (se 1 (by rfl) ⟨2489543, by rfl⟩ : syracuseStep 3319391 = 4979087) B4979087
theorem B2212927 : Blo 2211435 2212927 := bstep (se 1 (by rfl) ⟨1659695, by rfl⟩ : syracuseStep 2212927 = 3319391) B3319391
theorem B3319397 : Blo 2211435 3319397 := bbase (se 4 (by rfl) ⟨311193, by rfl⟩ : syracuseStep 3319397 = 622387) (by norm_num)
theorem B2212931 : Blo 2211435 2212931 := bstep (se 1 (by rfl) ⟨1659698, by rfl⟩ : syracuseStep 2212931 = 3319397) B3319397
theorem B2523521 : Blo 2211435 2523521 := bbase (se 2 (by rfl) ⟨946320, by rfl⟩ : syracuseStep 2523521 = 1892641) (by norm_num)
theorem B6729389 : Blo 2211435 6729389 := bstep (se 3 (by rfl) ⟨1261760, by rfl⟩ : syracuseStep 6729389 = 2523521) B2523521
theorem B4486259 : Blo 2211435 4486259 := bstep (se 1 (by rfl) ⟨3364694, by rfl⟩ : syracuseStep 4486259 = 6729389) B6729389
theorem B2990839 : Blo 2211435 2990839 := bstep (se 1 (by rfl) ⟨2243129, by rfl⟩ : syracuseStep 2990839 = 4486259) B4486259
theorem B3987785 : Blo 2211435 3987785 := bstep (se 2 (by rfl) ⟨1495419, by rfl⟩ : syracuseStep 3987785 = 2990839) B2990839
theorem B2658523 : Blo 2211435 2658523 := bstep (se 1 (by rfl) ⟨1993892, by rfl⟩ : syracuseStep 2658523 = 3987785) B3987785
theorem B3544697 : Blo 2211435 3544697 := bstep (se 2 (by rfl) ⟨1329261, by rfl⟩ : syracuseStep 3544697 = 2658523) B2658523
theorem B2363131 : Blo 2211435 2363131 := bstep (se 1 (by rfl) ⟨1772348, by rfl⟩ : syracuseStep 2363131 = 3544697) B3544697
theorem B3150841 : Blo 2211435 3150841 := bstep (se 2 (by rfl) ⟨1181565, by rfl⟩ : syracuseStep 3150841 = 2363131) B2363131
theorem B4201121 : Blo 2211435 4201121 := bstep (se 2 (by rfl) ⟨1575420, by rfl⟩ : syracuseStep 4201121 = 3150841) B3150841
theorem B2800747 : Blo 2211435 2800747 := bstep (se 1 (by rfl) ⟨2100560, by rfl⟩ : syracuseStep 2800747 = 4201121) B4201121
theorem B3734329 : Blo 2211435 3734329 := bstep (se 2 (by rfl) ⟨1400373, by rfl⟩ : syracuseStep 3734329 = 2800747) B2800747
theorem B4979105 : Blo 2211435 4979105 := bstep (se 2 (by rfl) ⟨1867164, by rfl⟩ : syracuseStep 4979105 = 3734329) B3734329
theorem B3319403 : Blo 2211435 3319403 := bstep (se 1 (by rfl) ⟨2489552, by rfl⟩ : syracuseStep 3319403 = 4979105) B4979105
theorem B2212935 : Blo 2211435 2212935 := bstep (se 1 (by rfl) ⟨1659701, by rfl⟩ : syracuseStep 2212935 = 3319403) B3319403
theorem B2489557 : Blo 2211435 2489557 := bbase (se 7 (by rfl) ⟨29174, by rfl⟩ : syracuseStep 2489557 = 58349) (by norm_num)
theorem B3319409 : Blo 2211435 3319409 := bstep (se 2 (by rfl) ⟨1244778, by rfl⟩ : syracuseStep 3319409 = 2489557) B2489557
theorem B2212939 : Blo 2211435 2212939 := bstep (se 1 (by rfl) ⟨1659704, by rfl⟩ : syracuseStep 2212939 = 3319409) B3319409
theorem B2800757 : Blo 2211435 2800757 := bbase (se 5 (by rfl) ⟨131285, by rfl⟩ : syracuseStep 2800757 = 262571) (by norm_num)
theorem B7468685 : Blo 2211435 7468685 := bstep (se 3 (by rfl) ⟨1400378, by rfl⟩ : syracuseStep 7468685 = 2800757) B2800757
theorem B4979123 : Blo 2211435 4979123 := bstep (se 1 (by rfl) ⟨3734342, by rfl⟩ : syracuseStep 4979123 = 7468685) B7468685
theorem B3319415 : Blo 2211435 3319415 := bstep (se 1 (by rfl) ⟨2489561, by rfl⟩ : syracuseStep 3319415 = 4979123) B4979123
theorem B2212943 : Blo 2211435 2212943 := bstep (se 1 (by rfl) ⟨1659707, by rfl⟩ : syracuseStep 2212943 = 3319415) B3319415
theorem B3319421 : Blo 2211435 3319421 := bbase (se 3 (by rfl) ⟨622391, by rfl⟩ : syracuseStep 3319421 = 1244783) (by norm_num)
theorem B2212947 : Blo 2211435 2212947 := bstep (se 1 (by rfl) ⟨1659710, by rfl⟩ : syracuseStep 2212947 = 3319421) B3319421
theorem B4979141 : Blo 2211435 4979141 := bbase (se 4 (by rfl) ⟨466794, by rfl⟩ : syracuseStep 4979141 = 933589) (by norm_num)
theorem B3319427 : Blo 2211435 3319427 := bstep (se 1 (by rfl) ⟨2489570, by rfl⟩ : syracuseStep 3319427 = 4979141) B4979141
theorem B2212951 : Blo 2211435 2212951 := bstep (se 1 (by rfl) ⟨1659713, by rfl⟩ : syracuseStep 2212951 = 3319427) B3319427
theorem B5317093 : Blo 2211435 5317093 := bbase (se 4 (by rfl) ⟨498477, by rfl⟩ : syracuseStep 5317093 = 996955) (by norm_num)
theorem B7089457 : Blo 2211435 7089457 := bstep (se 2 (by rfl) ⟨2658546, by rfl⟩ : syracuseStep 7089457 = 5317093) B5317093
theorem B9452609 : Blo 2211435 9452609 := bstep (se 2 (by rfl) ⟨3544728, by rfl⟩ : syracuseStep 9452609 = 7089457) B7089457
theorem B6301739 : Blo 2211435 6301739 := bstep (se 1 (by rfl) ⟨4726304, by rfl⟩ : syracuseStep 6301739 = 9452609) B9452609
theorem B4201159 : Blo 2211435 4201159 := bstep (se 1 (by rfl) ⟨3150869, by rfl⟩ : syracuseStep 4201159 = 6301739) B6301739
theorem B5601545 : Blo 2211435 5601545 := bstep (se 2 (by rfl) ⟨2100579, by rfl⟩ : syracuseStep 5601545 = 4201159) B4201159
theorem B3734363 : Blo 2211435 3734363 := bstep (se 1 (by rfl) ⟨2800772, by rfl⟩ : syracuseStep 3734363 = 5601545) B5601545
theorem B2489575 : Blo 2211435 2489575 := bstep (se 1 (by rfl) ⟨1867181, by rfl⟩ : syracuseStep 2489575 = 3734363) B3734363
theorem B3319433 : Blo 2211435 3319433 := bstep (se 2 (by rfl) ⟨1244787, by rfl⟩ : syracuseStep 3319433 = 2489575) B2489575
theorem B2212955 : Blo 2211435 2212955 := bstep (se 1 (by rfl) ⟨1659716, by rfl⟩ : syracuseStep 2212955 = 3319433) B3319433
theorem B11203109 : Blo 2211435 11203109 := bbase (se 4 (by rfl) ⟨1050291, by rfl⟩ : syracuseStep 11203109 = 2100583) (by norm_num)
theorem B7468739 : Blo 2211435 7468739 := bstep (se 1 (by rfl) ⟨5601554, by rfl⟩ : syracuseStep 7468739 = 11203109) B11203109
theorem B4979159 : Blo 2211435 4979159 := bstep (se 1 (by rfl) ⟨3734369, by rfl⟩ : syracuseStep 4979159 = 7468739) B7468739
theorem B3319439 : Blo 2211435 3319439 := bstep (se 1 (by rfl) ⟨2489579, by rfl⟩ : syracuseStep 3319439 = 4979159) B4979159
theorem B2212959 : Blo 2211435 2212959 := bstep (se 1 (by rfl) ⟨1659719, by rfl⟩ : syracuseStep 2212959 = 3319439) B3319439
theorem B3319445 : Blo 2211435 3319445 := bbase (se 6 (by rfl) ⟨77799, by rfl⟩ : syracuseStep 3319445 = 155599) (by norm_num)
theorem B2212963 : Blo 2211435 2212963 := bstep (se 1 (by rfl) ⟨1659722, by rfl⟩ : syracuseStep 2212963 = 3319445) B3319445
theorem B2243161 : Blo 2211435 2243161 := bbase (se 2 (by rfl) ⟨841185, by rfl⟩ : syracuseStep 2243161 = 1682371) (by norm_num)
theorem B2990881 : Blo 2211435 2990881 := bstep (se 2 (by rfl) ⟨1121580, by rfl⟩ : syracuseStep 2990881 = 2243161) B2243161
theorem B3987841 : Blo 2211435 3987841 := bstep (se 2 (by rfl) ⟨1495440, by rfl⟩ : syracuseStep 3987841 = 2990881) B2990881
theorem B5317121 : Blo 2211435 5317121 := bstep (se 2 (by rfl) ⟨1993920, by rfl⟩ : syracuseStep 5317121 = 3987841) B3987841
theorem B14178989 : Blo 2211435 14178989 := bstep (se 3 (by rfl) ⟨2658560, by rfl⟩ : syracuseStep 14178989 = 5317121) B5317121
theorem B9452659 : Blo 2211435 9452659 := bstep (se 1 (by rfl) ⟨7089494, by rfl⟩ : syracuseStep 9452659 = 14178989) B14178989
theorem B12603545 : Blo 2211435 12603545 := bstep (se 2 (by rfl) ⟨4726329, by rfl⟩ : syracuseStep 12603545 = 9452659) B9452659
theorem B8402363 : Blo 2211435 8402363 := bstep (se 1 (by rfl) ⟨6301772, by rfl⟩ : syracuseStep 8402363 = 12603545) B12603545
theorem B5601575 : Blo 2211435 5601575 := bstep (se 1 (by rfl) ⟨4201181, by rfl⟩ : syracuseStep 5601575 = 8402363) B8402363
theorem B3734383 : Blo 2211435 3734383 := bstep (se 1 (by rfl) ⟨2800787, by rfl⟩ : syracuseStep 3734383 = 5601575) B5601575
theorem B4979177 : Blo 2211435 4979177 := bstep (se 2 (by rfl) ⟨1867191, by rfl⟩ : syracuseStep 4979177 = 3734383) B3734383
theorem B3319451 : Blo 2211435 3319451 := bstep (se 1 (by rfl) ⟨2489588, by rfl⟩ : syracuseStep 3319451 = 4979177) B4979177
theorem B2212967 : Blo 2211435 2212967 := bstep (se 1 (by rfl) ⟨1659725, by rfl⟩ : syracuseStep 2212967 = 3319451) B3319451
theorem B2489593 : Blo 2211435 2489593 := bbase (se 2 (by rfl) ⟨933597, by rfl⟩ : syracuseStep 2489593 = 1867195) (by norm_num)
theorem B3319457 : Blo 2211435 3319457 := bstep (se 2 (by rfl) ⟨1244796, by rfl⟩ : syracuseStep 3319457 = 2489593) B2489593
theorem B2212971 : Blo 2211435 2212971 := bstep (se 1 (by rfl) ⟨1659728, by rfl⟩ : syracuseStep 2212971 = 3319457) B3319457
theorem B9452693 : Blo 2211435 9452693 := bbase (se 6 (by rfl) ⟨221547, by rfl⟩ : syracuseStep 9452693 = 443095) (by norm_num)
theorem B6301795 : Blo 2211435 6301795 := bstep (se 1 (by rfl) ⟨4726346, by rfl⟩ : syracuseStep 6301795 = 9452693) B9452693
theorem B8402393 : Blo 2211435 8402393 := bstep (se 2 (by rfl) ⟨3150897, by rfl⟩ : syracuseStep 8402393 = 6301795) B6301795
theorem B5601595 : Blo 2211435 5601595 := bstep (se 1 (by rfl) ⟨4201196, by rfl⟩ : syracuseStep 5601595 = 8402393) B8402393
theorem B7468793 : Blo 2211435 7468793 := bstep (se 2 (by rfl) ⟨2800797, by rfl⟩ : syracuseStep 7468793 = 5601595) B5601595
theorem B4979195 : Blo 2211435 4979195 := bstep (se 1 (by rfl) ⟨3734396, by rfl⟩ : syracuseStep 4979195 = 7468793) B7468793
theorem B3319463 : Blo 2211435 3319463 := bstep (se 1 (by rfl) ⟨2489597, by rfl⟩ : syracuseStep 3319463 = 4979195) B4979195
theorem B2212975 : Blo 2211435 2212975 := bstep (se 1 (by rfl) ⟨1659731, by rfl⟩ : syracuseStep 2212975 = 3319463) B3319463
theorem B3319469 : Blo 2211435 3319469 := bbase (se 3 (by rfl) ⟨622400, by rfl⟩ : syracuseStep 3319469 = 1244801) (by norm_num)
theorem B2212979 : Blo 2211435 2212979 := bstep (se 1 (by rfl) ⟨1659734, by rfl⟩ : syracuseStep 2212979 = 3319469) B3319469
theorem B4979213 : Blo 2211435 4979213 := bbase (se 3 (by rfl) ⟨933602, by rfl⟩ : syracuseStep 4979213 = 1867205) (by norm_num)
theorem B3319475 : Blo 2211435 3319475 := bstep (se 1 (by rfl) ⟨2489606, by rfl⟩ : syracuseStep 3319475 = 4979213) B4979213
theorem B2212983 : Blo 2211435 2212983 := bstep (se 1 (by rfl) ⟨1659737, by rfl⟩ : syracuseStep 2212983 = 3319475) B3319475
theorem B2800813 : Blo 2211435 2800813 := bbase (se 3 (by rfl) ⟨525152, by rfl⟩ : syracuseStep 2800813 = 1050305) (by norm_num)
theorem B3734417 : Blo 2211435 3734417 := bstep (se 2 (by rfl) ⟨1400406, by rfl⟩ : syracuseStep 3734417 = 2800813) B2800813
theorem B2489611 : Blo 2211435 2489611 := bstep (se 1 (by rfl) ⟨1867208, by rfl⟩ : syracuseStep 2489611 = 3734417) B3734417
theorem B3319481 : Blo 2211435 3319481 := bstep (se 2 (by rfl) ⟨1244805, by rfl⟩ : syracuseStep 3319481 = 2489611) B2489611
theorem B2212987 : Blo 2211435 2212987 := bstep (se 1 (by rfl) ⟨1659740, by rfl⟩ : syracuseStep 2212987 = 3319481) B3319481
theorem B2658589 : Blo 2211435 2658589 := bbase (se 3 (by rfl) ⟨498485, by rfl⟩ : syracuseStep 2658589 = 996971) (by norm_num)
theorem B14179141 : Blo 2211435 14179141 := bstep (se 4 (by rfl) ⟨1329294, by rfl⟩ : syracuseStep 14179141 = 2658589) B2658589
theorem B18905521 : Blo 2211435 18905521 := bstep (se 2 (by rfl) ⟨7089570, by rfl⟩ : syracuseStep 18905521 = 14179141) B14179141
theorem B25207361 : Blo 2211435 25207361 := bstep (se 2 (by rfl) ⟨9452760, by rfl⟩ : syracuseStep 25207361 = 18905521) B18905521
theorem B16804907 : Blo 2211435 16804907 := bstep (se 1 (by rfl) ⟨12603680, by rfl⟩ : syracuseStep 16804907 = 25207361) B25207361
theorem B11203271 : Blo 2211435 11203271 := bstep (se 1 (by rfl) ⟨8402453, by rfl⟩ : syracuseStep 11203271 = 16804907) B16804907
theorem B7468847 : Blo 2211435 7468847 := bstep (se 1 (by rfl) ⟨5601635, by rfl⟩ : syracuseStep 7468847 = 11203271) B11203271
theorem B4979231 : Blo 2211435 4979231 := bstep (se 1 (by rfl) ⟨3734423, by rfl⟩ : syracuseStep 4979231 = 7468847) B7468847
theorem B3319487 : Blo 2211435 3319487 := bstep (se 1 (by rfl) ⟨2489615, by rfl⟩ : syracuseStep 3319487 = 4979231) B4979231
theorem B2212991 : Blo 2211435 2212991 := bstep (se 1 (by rfl) ⟨1659743, by rfl⟩ : syracuseStep 2212991 = 3319487) B3319487
theorem B3319493 : Blo 2211435 3319493 := bbase (se 4 (by rfl) ⟨311202, by rfl⟩ : syracuseStep 3319493 = 622405) (by norm_num)
theorem B2212995 : Blo 2211435 2212995 := bstep (se 1 (by rfl) ⟨1659746, by rfl⟩ : syracuseStep 2212995 = 3319493) B3319493
theorem B3734437 : Blo 2211435 3734437 := bbase (se 4 (by rfl) ⟨350103, by rfl⟩ : syracuseStep 3734437 = 700207) (by norm_num)
theorem B4979249 : Blo 2211435 4979249 := bstep (se 2 (by rfl) ⟨1867218, by rfl⟩ : syracuseStep 4979249 = 3734437) B3734437
theorem B3319499 : Blo 2211435 3319499 := bstep (se 1 (by rfl) ⟨2489624, by rfl⟩ : syracuseStep 3319499 = 4979249) B4979249
theorem B2212999 : Blo 2211435 2212999 := bstep (se 1 (by rfl) ⟨1659749, by rfl⟩ : syracuseStep 2212999 = 3319499) B3319499
theorem B2489629 : Blo 2211435 2489629 := bbase (se 3 (by rfl) ⟨466805, by rfl⟩ : syracuseStep 2489629 = 933611) (by norm_num)
theorem B3319505 : Blo 2211435 3319505 := bstep (se 2 (by rfl) ⟨1244814, by rfl⟩ : syracuseStep 3319505 = 2489629) B2489629
theorem B2213003 : Blo 2211435 2213003 := bstep (se 1 (by rfl) ⟨1659752, by rfl⟩ : syracuseStep 2213003 = 3319505) B3319505
theorem B7468901 : Blo 2211435 7468901 := bbase (se 4 (by rfl) ⟨700209, by rfl⟩ : syracuseStep 7468901 = 1400419) (by norm_num)
theorem B4979267 : Blo 2211435 4979267 := bstep (se 1 (by rfl) ⟨3734450, by rfl⟩ : syracuseStep 4979267 = 7468901) B7468901
theorem B3319511 : Blo 2211435 3319511 := bstep (se 1 (by rfl) ⟨2489633, by rfl⟩ : syracuseStep 3319511 = 4979267) B4979267
theorem B2213007 : Blo 2211435 2213007 := bstep (se 1 (by rfl) ⟨1659755, by rfl⟩ : syracuseStep 2213007 = 3319511) B3319511
theorem B3319517 : Blo 2211435 3319517 := bbase (se 3 (by rfl) ⟨622409, by rfl⟩ : syracuseStep 3319517 = 1244819) (by norm_num)
theorem B2213011 : Blo 2211435 2213011 := bstep (se 1 (by rfl) ⟨1659758, by rfl⟩ : syracuseStep 2213011 = 3319517) B3319517
theorem B4979285 : Blo 2211435 4979285 := bbase (se 8 (by rfl) ⟨29175, by rfl⟩ : syracuseStep 4979285 = 58351) (by norm_num)
theorem B3319523 : Blo 2211435 3319523 := bstep (se 1 (by rfl) ⟨2489642, by rfl⟩ : syracuseStep 3319523 = 4979285) B4979285
theorem B2213015 : Blo 2211435 2213015 := bstep (se 1 (by rfl) ⟨1659761, by rfl⟩ : syracuseStep 2213015 = 3319523) B3319523
theorem B3642221 : Blo 2211435 3642221 := bbase (se 3 (by rfl) ⟨682916, by rfl⟩ : syracuseStep 3642221 = 1365833) (by norm_num)
theorem B2428147 : Blo 2211435 2428147 := bstep (se 1 (by rfl) ⟨1821110, by rfl⟩ : syracuseStep 2428147 = 3642221) B3642221
theorem B12950117 : Blo 2211435 12950117 := bstep (se 4 (by rfl) ⟨1214073, by rfl⟩ : syracuseStep 12950117 = 2428147) B2428147
theorem B8633411 : Blo 2211435 8633411 := bstep (se 1 (by rfl) ⟨6475058, by rfl⟩ : syracuseStep 8633411 = 12950117) B12950117
theorem B5755607 : Blo 2211435 5755607 := bstep (se 1 (by rfl) ⟨4316705, by rfl⟩ : syracuseStep 5755607 = 8633411) B8633411
theorem B3837071 : Blo 2211435 3837071 := bstep (se 1 (by rfl) ⟨2877803, by rfl⟩ : syracuseStep 3837071 = 5755607) B5755607
theorem B2558047 : Blo 2211435 2558047 := bstep (se 1 (by rfl) ⟨1918535, by rfl⟩ : syracuseStep 2558047 = 3837071) B3837071
theorem B3410729 : Blo 2211435 3410729 := bstep (se 2 (by rfl) ⟨1279023, by rfl⟩ : syracuseStep 3410729 = 2558047) B2558047
theorem B2273819 : Blo 2211435 2273819 := bstep (se 1 (by rfl) ⟨1705364, by rfl⟩ : syracuseStep 2273819 = 3410729) B3410729
theorem B6063517 : Blo 2211435 6063517 := bstep (se 3 (by rfl) ⟨1136909, by rfl⟩ : syracuseStep 6063517 = 2273819) B2273819
theorem B32338757 : Blo 2211435 32338757 := bstep (se 4 (by rfl) ⟨3031758, by rfl⟩ : syracuseStep 32338757 = 6063517) B6063517
theorem B21559171 : Blo 2211435 21559171 := bstep (se 1 (by rfl) ⟨16169378, by rfl⟩ : syracuseStep 21559171 = 32338757) B32338757
theorem B28745561 : Blo 2211435 28745561 := bstep (se 2 (by rfl) ⟨10779585, by rfl⟩ : syracuseStep 28745561 = 21559171) B21559171
theorem B76654829 : Blo 2211435 76654829 := bstep (se 3 (by rfl) ⟨14372780, by rfl⟩ : syracuseStep 76654829 = 28745561) B28745561
theorem B51103219 : Blo 2211435 51103219 := bstep (se 1 (by rfl) ⟨38327414, by rfl⟩ : syracuseStep 51103219 = 76654829) B76654829
theorem B68137625 : Blo 2211435 68137625 := bstep (se 2 (by rfl) ⟨25551609, by rfl⟩ : syracuseStep 68137625 = 51103219) B51103219
theorem B45425083 : Blo 2211435 45425083 := bstep (se 1 (by rfl) ⟨34068812, by rfl⟩ : syracuseStep 45425083 = 68137625) B68137625
theorem B60566777 : Blo 2211435 60566777 := bstep (se 2 (by rfl) ⟨22712541, by rfl⟩ : syracuseStep 60566777 = 45425083) B45425083
theorem B40377851 : Blo 2211435 40377851 := bstep (se 1 (by rfl) ⟨30283388, by rfl⟩ : syracuseStep 40377851 = 60566777) B60566777
theorem B26918567 : Blo 2211435 26918567 := bstep (se 1 (by rfl) ⟨20188925, by rfl⟩ : syracuseStep 26918567 = 40377851) B40377851
theorem B17945711 : Blo 2211435 17945711 := bstep (se 1 (by rfl) ⟨13459283, by rfl⟩ : syracuseStep 17945711 = 26918567) B26918567
theorem B11963807 : Blo 2211435 11963807 := bstep (se 1 (by rfl) ⟨8972855, by rfl⟩ : syracuseStep 11963807 = 17945711) B17945711
theorem B7975871 : Blo 2211435 7975871 := bstep (se 1 (by rfl) ⟨5981903, by rfl⟩ : syracuseStep 7975871 = 11963807) B11963807
theorem B5317247 : Blo 2211435 5317247 := bstep (se 1 (by rfl) ⟨3987935, by rfl⟩ : syracuseStep 5317247 = 7975871) B7975871
theorem B3544831 : Blo 2211435 3544831 := bstep (se 1 (by rfl) ⟨2658623, by rfl⟩ : syracuseStep 3544831 = 5317247) B5317247
theorem B4726441 : Blo 2211435 4726441 := bstep (se 2 (by rfl) ⟨1772415, by rfl⟩ : syracuseStep 4726441 = 3544831) B3544831
theorem B6301921 : Blo 2211435 6301921 := bstep (se 2 (by rfl) ⟨2363220, by rfl⟩ : syracuseStep 6301921 = 4726441) B4726441
theorem B8402561 : Blo 2211435 8402561 := bstep (se 2 (by rfl) ⟨3150960, by rfl⟩ : syracuseStep 8402561 = 6301921) B6301921
theorem B5601707 : Blo 2211435 5601707 := bstep (se 1 (by rfl) ⟨4201280, by rfl⟩ : syracuseStep 5601707 = 8402561) B8402561
theorem B3734471 : Blo 2211435 3734471 := bstep (se 1 (by rfl) ⟨2800853, by rfl⟩ : syracuseStep 3734471 = 5601707) B5601707
theorem B2489647 : Blo 2211435 2489647 := bstep (se 1 (by rfl) ⟨1867235, by rfl⟩ : syracuseStep 2489647 = 3734471) B3734471
theorem B3319529 : Blo 2211435 3319529 := bstep (se 2 (by rfl) ⟨1244823, by rfl⟩ : syracuseStep 3319529 = 2489647) B2489647
theorem B2213019 : Blo 2211435 2213019 := bstep (se 1 (by rfl) ⟨1659764, by rfl⟩ : syracuseStep 2213019 = 3319529) B3319529
theorem B8972869 : Blo 2211435 8972869 := bbase (se 4 (by rfl) ⟨841206, by rfl⟩ : syracuseStep 8972869 = 1682413) (by norm_num)
theorem B11963825 : Blo 2211435 11963825 := bstep (se 2 (by rfl) ⟨4486434, by rfl⟩ : syracuseStep 11963825 = 8972869) B8972869
theorem B7975883 : Blo 2211435 7975883 := bstep (se 1 (by rfl) ⟨5981912, by rfl⟩ : syracuseStep 7975883 = 11963825) B11963825
theorem B5317255 : Blo 2211435 5317255 := bstep (se 1 (by rfl) ⟨3987941, by rfl⟩ : syracuseStep 5317255 = 7975883) B7975883
theorem B28358693 : Blo 2211435 28358693 := bstep (se 4 (by rfl) ⟨2658627, by rfl⟩ : syracuseStep 28358693 = 5317255) B5317255
theorem B18905795 : Blo 2211435 18905795 := bstep (se 1 (by rfl) ⟨14179346, by rfl⟩ : syracuseStep 18905795 = 28358693) B28358693
theorem B12603863 : Blo 2211435 12603863 := bstep (se 1 (by rfl) ⟨9452897, by rfl⟩ : syracuseStep 12603863 = 18905795) B18905795
theorem B8402575 : Blo 2211435 8402575 := bstep (se 1 (by rfl) ⟨6301931, by rfl⟩ : syracuseStep 8402575 = 12603863) B12603863
theorem B11203433 : Blo 2211435 11203433 := bstep (se 2 (by rfl) ⟨4201287, by rfl⟩ : syracuseStep 11203433 = 8402575) B8402575
theorem B7468955 : Blo 2211435 7468955 := bstep (se 1 (by rfl) ⟨5601716, by rfl⟩ : syracuseStep 7468955 = 11203433) B11203433
theorem B4979303 : Blo 2211435 4979303 := bstep (se 1 (by rfl) ⟨3734477, by rfl⟩ : syracuseStep 4979303 = 7468955) B7468955
theorem B3319535 : Blo 2211435 3319535 := bstep (se 1 (by rfl) ⟨2489651, by rfl⟩ : syracuseStep 3319535 = 4979303) B4979303
theorem B2213023 : Blo 2211435 2213023 := bstep (se 1 (by rfl) ⟨1659767, by rfl⟩ : syracuseStep 2213023 = 3319535) B3319535
theorem B3319541 : Blo 2211435 3319541 := bbase (se 5 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 3319541 = 311207) (by norm_num)
theorem B2213027 : Blo 2211435 2213027 := bstep (se 1 (by rfl) ⟨1659770, by rfl⟩ : syracuseStep 2213027 = 3319541) B3319541
theorem B9452933 : Blo 2211435 9452933 := bbase (se 4 (by rfl) ⟨886212, by rfl⟩ : syracuseStep 9452933 = 1772425) (by norm_num)
theorem B6301955 : Blo 2211435 6301955 := bstep (se 1 (by rfl) ⟨4726466, by rfl⟩ : syracuseStep 6301955 = 9452933) B9452933
theorem B4201303 : Blo 2211435 4201303 := bstep (se 1 (by rfl) ⟨3150977, by rfl⟩ : syracuseStep 4201303 = 6301955) B6301955
theorem B5601737 : Blo 2211435 5601737 := bstep (se 2 (by rfl) ⟨2100651, by rfl⟩ : syracuseStep 5601737 = 4201303) B4201303
theorem B3734491 : Blo 2211435 3734491 := bstep (se 1 (by rfl) ⟨2800868, by rfl⟩ : syracuseStep 3734491 = 5601737) B5601737
theorem B4979321 : Blo 2211435 4979321 := bstep (se 2 (by rfl) ⟨1867245, by rfl⟩ : syracuseStep 4979321 = 3734491) B3734491
theorem B3319547 : Blo 2211435 3319547 := bstep (se 1 (by rfl) ⟨2489660, by rfl⟩ : syracuseStep 3319547 = 4979321) B4979321
theorem B2213031 : Blo 2211435 2213031 := bstep (se 1 (by rfl) ⟨1659773, by rfl⟩ : syracuseStep 2213031 = 3319547) B3319547
theorem B2489665 : Blo 2211435 2489665 := bbase (se 2 (by rfl) ⟨933624, by rfl⟩ : syracuseStep 2489665 = 1867249) (by norm_num)
theorem B3319553 : Blo 2211435 3319553 := bstep (se 2 (by rfl) ⟨1244832, by rfl⟩ : syracuseStep 3319553 = 2489665) B2489665
theorem B2213035 : Blo 2211435 2213035 := bstep (se 1 (by rfl) ⟨1659776, by rfl⟩ : syracuseStep 2213035 = 3319553) B3319553
theorem B5601757 : Blo 2211435 5601757 := bbase (se 3 (by rfl) ⟨1050329, by rfl⟩ : syracuseStep 5601757 = 2100659) (by norm_num)
theorem B7469009 : Blo 2211435 7469009 := bstep (se 2 (by rfl) ⟨2800878, by rfl⟩ : syracuseStep 7469009 = 5601757) B5601757
theorem B4979339 : Blo 2211435 4979339 := bstep (se 1 (by rfl) ⟨3734504, by rfl⟩ : syracuseStep 4979339 = 7469009) B7469009
theorem B3319559 : Blo 2211435 3319559 := bstep (se 1 (by rfl) ⟨2489669, by rfl⟩ : syracuseStep 3319559 = 4979339) B4979339
theorem B2213039 : Blo 2211435 2213039 := bstep (se 1 (by rfl) ⟨1659779, by rfl⟩ : syracuseStep 2213039 = 3319559) B3319559
theorem B3319565 : Blo 2211435 3319565 := bbase (se 3 (by rfl) ⟨622418, by rfl⟩ : syracuseStep 3319565 = 1244837) (by norm_num)
theorem B2213043 : Blo 2211435 2213043 := bstep (se 1 (by rfl) ⟨1659782, by rfl⟩ : syracuseStep 2213043 = 3319565) B3319565
theorem B4979357 : Blo 2211435 4979357 := bbase (se 3 (by rfl) ⟨933629, by rfl⟩ : syracuseStep 4979357 = 1867259) (by norm_num)
theorem B3319571 : Blo 2211435 3319571 := bstep (se 1 (by rfl) ⟨2489678, by rfl⟩ : syracuseStep 3319571 = 4979357) B4979357
theorem B2213047 : Blo 2211435 2213047 := bstep (se 1 (by rfl) ⟨1659785, by rfl⟩ : syracuseStep 2213047 = 3319571) B3319571
theorem B3734525 : Blo 2211435 3734525 := bbase (se 3 (by rfl) ⟨700223, by rfl⟩ : syracuseStep 3734525 = 1400447) (by norm_num)
theorem B2489683 : Blo 2211435 2489683 := bstep (se 1 (by rfl) ⟨1867262, by rfl⟩ : syracuseStep 2489683 = 3734525) B3734525
theorem B3319577 : Blo 2211435 3319577 := bstep (se 2 (by rfl) ⟨1244841, by rfl⟩ : syracuseStep 3319577 = 2489683) B2489683
theorem B2213051 : Blo 2211435 2213051 := bstep (se 1 (by rfl) ⟨1659788, by rfl⟩ : syracuseStep 2213051 = 3319577) B3319577
theorem B4726517 : Blo 2211435 4726517 := bbase (se 5 (by rfl) ⟨221555, by rfl⟩ : syracuseStep 4726517 = 443111) (by norm_num)
theorem B12604045 : Blo 2211435 12604045 := bstep (se 3 (by rfl) ⟨2363258, by rfl⟩ : syracuseStep 12604045 = 4726517) B4726517
theorem B16805393 : Blo 2211435 16805393 := bstep (se 2 (by rfl) ⟨6302022, by rfl⟩ : syracuseStep 16805393 = 12604045) B12604045
theorem B11203595 : Blo 2211435 11203595 := bstep (se 1 (by rfl) ⟨8402696, by rfl⟩ : syracuseStep 11203595 = 16805393) B16805393
theorem B7469063 : Blo 2211435 7469063 := bstep (se 1 (by rfl) ⟨5601797, by rfl⟩ : syracuseStep 7469063 = 11203595) B11203595
theorem B4979375 : Blo 2211435 4979375 := bstep (se 1 (by rfl) ⟨3734531, by rfl⟩ : syracuseStep 4979375 = 7469063) B7469063
theorem B3319583 : Blo 2211435 3319583 := bstep (se 1 (by rfl) ⟨2489687, by rfl⟩ : syracuseStep 3319583 = 4979375) B4979375
theorem B2213055 : Blo 2211435 2213055 := bstep (se 1 (by rfl) ⟨1659791, by rfl⟩ : syracuseStep 2213055 = 3319583) B3319583
theorem B3319589 : Blo 2211435 3319589 := bbase (se 4 (by rfl) ⟨311211, by rfl⟩ : syracuseStep 3319589 = 622423) (by norm_num)
theorem B2213059 : Blo 2211435 2213059 := bstep (se 1 (by rfl) ⟨1659794, by rfl⟩ : syracuseStep 2213059 = 3319589) B3319589
theorem B2800909 : Blo 2211435 2800909 := bbase (se 3 (by rfl) ⟨525170, by rfl⟩ : syracuseStep 2800909 = 1050341) (by norm_num)
theorem B3734545 : Blo 2211435 3734545 := bstep (se 2 (by rfl) ⟨1400454, by rfl⟩ : syracuseStep 3734545 = 2800909) B2800909
theorem B4979393 : Blo 2211435 4979393 := bstep (se 2 (by rfl) ⟨1867272, by rfl⟩ : syracuseStep 4979393 = 3734545) B3734545
theorem B3319595 : Blo 2211435 3319595 := bstep (se 1 (by rfl) ⟨2489696, by rfl⟩ : syracuseStep 3319595 = 4979393) B4979393
theorem B2213063 : Blo 2211435 2213063 := bstep (se 1 (by rfl) ⟨1659797, by rfl⟩ : syracuseStep 2213063 = 3319595) B3319595
theorem B2489701 : Blo 2211435 2489701 := bbase (se 4 (by rfl) ⟨233409, by rfl⟩ : syracuseStep 2489701 = 466819) (by norm_num)
theorem B3319601 : Blo 2211435 3319601 := bstep (se 2 (by rfl) ⟨1244850, by rfl⟩ : syracuseStep 3319601 = 2489701) B2489701
theorem B2213067 : Blo 2211435 2213067 := bstep (se 1 (by rfl) ⟨1659800, by rfl⟩ : syracuseStep 2213067 = 3319601) B3319601
theorem B6302069 : Blo 2211435 6302069 := bbase (se 5 (by rfl) ⟨295409, by rfl⟩ : syracuseStep 6302069 = 590819) (by norm_num)
theorem B4201379 : Blo 2211435 4201379 := bstep (se 1 (by rfl) ⟨3151034, by rfl⟩ : syracuseStep 4201379 = 6302069) B6302069
theorem B2800919 : Blo 2211435 2800919 := bstep (se 1 (by rfl) ⟨2100689, by rfl⟩ : syracuseStep 2800919 = 4201379) B4201379
theorem B7469117 : Blo 2211435 7469117 := bstep (se 3 (by rfl) ⟨1400459, by rfl⟩ : syracuseStep 7469117 = 2800919) B2800919
theorem B4979411 : Blo 2211435 4979411 := bstep (se 1 (by rfl) ⟨3734558, by rfl⟩ : syracuseStep 4979411 = 7469117) B7469117
theorem B3319607 : Blo 2211435 3319607 := bstep (se 1 (by rfl) ⟨2489705, by rfl⟩ : syracuseStep 3319607 = 4979411) B4979411
theorem B2213071 : Blo 2211435 2213071 := bstep (se 1 (by rfl) ⟨1659803, by rfl⟩ : syracuseStep 2213071 = 3319607) B3319607
theorem B3319613 : Blo 2211435 3319613 := bbase (se 3 (by rfl) ⟨622427, by rfl⟩ : syracuseStep 3319613 = 1244855) (by norm_num)
theorem B2213075 : Blo 2211435 2213075 := bstep (se 1 (by rfl) ⟨1659806, by rfl⟩ : syracuseStep 2213075 = 3319613) B3319613
theorem B4979429 : Blo 2211435 4979429 := bbase (se 4 (by rfl) ⟨466821, by rfl⟩ : syracuseStep 4979429 = 933643) (by norm_num)
theorem B3319619 : Blo 2211435 3319619 := bstep (se 1 (by rfl) ⟨2489714, by rfl⟩ : syracuseStep 3319619 = 4979429) B4979429
theorem B2213079 : Blo 2211435 2213079 := bstep (se 1 (by rfl) ⟨1659809, by rfl⟩ : syracuseStep 2213079 = 3319619) B3319619
theorem B5601869 : Blo 2211435 5601869 := bbase (se 3 (by rfl) ⟨1050350, by rfl⟩ : syracuseStep 5601869 = 2100701) (by norm_num)
theorem B3734579 : Blo 2211435 3734579 := bstep (se 1 (by rfl) ⟨2800934, by rfl⟩ : syracuseStep 3734579 = 5601869) B5601869
theorem B2489719 : Blo 2211435 2489719 := bstep (se 1 (by rfl) ⟨1867289, by rfl⟩ : syracuseStep 2489719 = 3734579) B3734579
theorem B3319625 : Blo 2211435 3319625 := bstep (se 2 (by rfl) ⟨1244859, by rfl⟩ : syracuseStep 3319625 = 2489719) B2489719
theorem B2213083 : Blo 2211435 2213083 := bstep (se 1 (by rfl) ⟨1659812, by rfl⟩ : syracuseStep 2213083 = 3319625) B3319625
theorem B2363293 : Blo 2211435 2363293 := bbase (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) (by norm_num)
theorem B3151057 : Blo 2211435 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B4201409 : Blo 2211435 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B11203757 : Blo 2211435 11203757 := bstep (se 3 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 11203757 = 4201409) B4201409
theorem B7469171 : Blo 2211435 7469171 := bstep (se 1 (by rfl) ⟨5601878, by rfl⟩ : syracuseStep 7469171 = 11203757) B11203757
theorem B4979447 : Blo 2211435 4979447 := bstep (se 1 (by rfl) ⟨3734585, by rfl⟩ : syracuseStep 4979447 = 7469171) B7469171
theorem B3319631 : Blo 2211435 3319631 := bstep (se 1 (by rfl) ⟨2489723, by rfl⟩ : syracuseStep 3319631 = 4979447) B4979447
theorem B2213087 : Blo 2211435 2213087 := bstep (se 1 (by rfl) ⟨1659815, by rfl⟩ : syracuseStep 2213087 = 3319631) B3319631
theorem B3319637 : Blo 2211435 3319637 := bbase (se 9 (by rfl) ⟨9725, by rfl⟩ : syracuseStep 3319637 = 19451) (by norm_num)
theorem B2213091 : Blo 2211435 2213091 := bstep (se 1 (by rfl) ⟨1659818, by rfl⟩ : syracuseStep 2213091 = 3319637) B3319637
theorem B5317429 : Blo 2211435 5317429 := bbase (se 5 (by rfl) ⟨249254, by rfl⟩ : syracuseStep 5317429 = 498509) (by norm_num)
theorem B7089905 : Blo 2211435 7089905 := bstep (se 2 (by rfl) ⟨2658714, by rfl⟩ : syracuseStep 7089905 = 5317429) B5317429
theorem B4726603 : Blo 2211435 4726603 := bstep (se 1 (by rfl) ⟨3544952, by rfl⟩ : syracuseStep 4726603 = 7089905) B7089905
theorem B6302137 : Blo 2211435 6302137 := bstep (se 2 (by rfl) ⟨2363301, by rfl⟩ : syracuseStep 6302137 = 4726603) B4726603
theorem B8402849 : Blo 2211435 8402849 := bstep (se 2 (by rfl) ⟨3151068, by rfl⟩ : syracuseStep 8402849 = 6302137) B6302137
theorem B5601899 : Blo 2211435 5601899 := bstep (se 1 (by rfl) ⟨4201424, by rfl⟩ : syracuseStep 5601899 = 8402849) B8402849
theorem B3734599 : Blo 2211435 3734599 := bstep (se 1 (by rfl) ⟨2800949, by rfl⟩ : syracuseStep 3734599 = 5601899) B5601899
theorem B4979465 : Blo 2211435 4979465 := bstep (se 2 (by rfl) ⟨1867299, by rfl⟩ : syracuseStep 4979465 = 3734599) B3734599
theorem B3319643 : Blo 2211435 3319643 := bstep (se 1 (by rfl) ⟨2489732, by rfl⟩ : syracuseStep 3319643 = 4979465) B4979465
theorem B2213095 : Blo 2211435 2213095 := bstep (se 1 (by rfl) ⟨1659821, by rfl⟩ : syracuseStep 2213095 = 3319643) B3319643
theorem B2489737 : Blo 2211435 2489737 := bbase (se 2 (by rfl) ⟨933651, by rfl⟩ : syracuseStep 2489737 = 1867303) (by norm_num)
theorem B3319649 : Blo 2211435 3319649 := bstep (se 2 (by rfl) ⟨1244868, by rfl⟩ : syracuseStep 3319649 = 2489737) B2489737
theorem B2213099 : Blo 2211435 2213099 := bstep (se 1 (by rfl) ⟨1659824, by rfl⟩ : syracuseStep 2213099 = 3319649) B3319649
theorem B5047421 : Blo 2211435 5047421 := bbase (se 3 (by rfl) ⟨946391, by rfl⟩ : syracuseStep 5047421 = 1892783) (by norm_num)
theorem B13459789 : Blo 2211435 13459789 := bstep (se 3 (by rfl) ⟨2523710, by rfl⟩ : syracuseStep 13459789 = 5047421) B5047421
theorem B71785541 : Blo 2211435 71785541 := bstep (se 4 (by rfl) ⟨6729894, by rfl⟩ : syracuseStep 71785541 = 13459789) B13459789
theorem B47857027 : Blo 2211435 47857027 := bstep (se 1 (by rfl) ⟨35892770, by rfl⟩ : syracuseStep 47857027 = 71785541) B71785541
theorem B63809369 : Blo 2211435 63809369 := bstep (se 2 (by rfl) ⟨23928513, by rfl⟩ : syracuseStep 63809369 = 47857027) B47857027
theorem B42539579 : Blo 2211435 42539579 := bstep (se 1 (by rfl) ⟨31904684, by rfl⟩ : syracuseStep 42539579 = 63809369) B63809369
theorem B28359719 : Blo 2211435 28359719 := bstep (se 1 (by rfl) ⟨21269789, by rfl⟩ : syracuseStep 28359719 = 42539579) B42539579
theorem B18906479 : Blo 2211435 18906479 := bstep (se 1 (by rfl) ⟨14179859, by rfl⟩ : syracuseStep 18906479 = 28359719) B28359719
theorem B12604319 : Blo 2211435 12604319 := bstep (se 1 (by rfl) ⟨9453239, by rfl⟩ : syracuseStep 12604319 = 18906479) B18906479
theorem B8402879 : Blo 2211435 8402879 := bstep (se 1 (by rfl) ⟨6302159, by rfl⟩ : syracuseStep 8402879 = 12604319) B12604319
theorem B5601919 : Blo 2211435 5601919 := bstep (se 1 (by rfl) ⟨4201439, by rfl⟩ : syracuseStep 5601919 = 8402879) B8402879
theorem B7469225 : Blo 2211435 7469225 := bstep (se 2 (by rfl) ⟨2800959, by rfl⟩ : syracuseStep 7469225 = 5601919) B5601919
theorem B4979483 : Blo 2211435 4979483 := bstep (se 1 (by rfl) ⟨3734612, by rfl⟩ : syracuseStep 4979483 = 7469225) B7469225
theorem B3319655 : Blo 2211435 3319655 := bstep (se 1 (by rfl) ⟨2489741, by rfl⟩ : syracuseStep 3319655 = 4979483) B4979483
theorem B2213103 : Blo 2211435 2213103 := bstep (se 1 (by rfl) ⟨1659827, by rfl⟩ : syracuseStep 2213103 = 3319655) B3319655
theorem B3319661 : Blo 2211435 3319661 := bbase (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) (by norm_num)
theorem B2213107 : Blo 2211435 2213107 := bstep (se 1 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 2213107 = 3319661) B3319661
theorem B4979501 : Blo 2211435 4979501 := bbase (se 3 (by rfl) ⟨933656, by rfl⟩ : syracuseStep 4979501 = 1867313) (by norm_num)
theorem B3319667 : Blo 2211435 3319667 := bstep (se 1 (by rfl) ⟨2489750, by rfl⟩ : syracuseStep 3319667 = 4979501) B4979501
theorem B2213111 : Blo 2211435 2213111 := bstep (se 1 (by rfl) ⟨1659833, by rfl⟩ : syracuseStep 2213111 = 3319667) B3319667
theorem B3988109 : Blo 2211435 3988109 := bbase (se 3 (by rfl) ⟨747770, by rfl⟩ : syracuseStep 3988109 = 1495541) (by norm_num)
theorem B2658739 : Blo 2211435 2658739 := bstep (se 1 (by rfl) ⟨1994054, by rfl⟩ : syracuseStep 2658739 = 3988109) B3988109
theorem B3544985 : Blo 2211435 3544985 := bstep (se 2 (by rfl) ⟨1329369, by rfl⟩ : syracuseStep 3544985 = 2658739) B2658739
theorem B9453293 : Blo 2211435 9453293 := bstep (se 3 (by rfl) ⟨1772492, by rfl⟩ : syracuseStep 9453293 = 3544985) B3544985
theorem B6302195 : Blo 2211435 6302195 := bstep (se 1 (by rfl) ⟨4726646, by rfl⟩ : syracuseStep 6302195 = 9453293) B9453293
theorem B4201463 : Blo 2211435 4201463 := bstep (se 1 (by rfl) ⟨3151097, by rfl⟩ : syracuseStep 4201463 = 6302195) B6302195
theorem B2800975 : Blo 2211435 2800975 := bstep (se 1 (by rfl) ⟨2100731, by rfl⟩ : syracuseStep 2800975 = 4201463) B4201463
theorem B3734633 : Blo 2211435 3734633 := bstep (se 2 (by rfl) ⟨1400487, by rfl⟩ : syracuseStep 3734633 = 2800975) B2800975
theorem B2489755 : Blo 2211435 2489755 := bstep (se 1 (by rfl) ⟨1867316, by rfl⟩ : syracuseStep 2489755 = 3734633) B3734633
theorem B3319673 : Blo 2211435 3319673 := bstep (se 2 (by rfl) ⟨1244877, by rfl⟩ : syracuseStep 3319673 = 2489755) B2489755
theorem B2213115 : Blo 2211435 2213115 := bstep (se 1 (by rfl) ⟨1659836, by rfl⟩ : syracuseStep 2213115 = 3319673) B3319673
theorem B6475349 : Blo 2211435 6475349 := bbase (se 8 (by rfl) ⟨37941, by rfl⟩ : syracuseStep 6475349 = 75883) (by norm_num)
theorem B4316899 : Blo 2211435 4316899 := bstep (se 1 (by rfl) ⟨3237674, by rfl⟩ : syracuseStep 4316899 = 6475349) B6475349
theorem B5755865 : Blo 2211435 5755865 := bstep (se 2 (by rfl) ⟨2158449, by rfl⟩ : syracuseStep 5755865 = 4316899) B4316899
theorem B61395893 : Blo 2211435 61395893 := bstep (se 5 (by rfl) ⟨2877932, by rfl⟩ : syracuseStep 61395893 = 5755865) B5755865
theorem B40930595 : Blo 2211435 40930595 := bstep (se 1 (by rfl) ⟨30697946, by rfl⟩ : syracuseStep 40930595 = 61395893) B61395893
theorem B27287063 : Blo 2211435 27287063 := bstep (se 1 (by rfl) ⟨20465297, by rfl⟩ : syracuseStep 27287063 = 40930595) B40930595
theorem B18191375 : Blo 2211435 18191375 := bstep (se 1 (by rfl) ⟨13643531, by rfl⟩ : syracuseStep 18191375 = 27287063) B27287063
theorem B12127583 : Blo 2211435 12127583 := bstep (se 1 (by rfl) ⟨9095687, by rfl⟩ : syracuseStep 12127583 = 18191375) B18191375
theorem B8085055 : Blo 2211435 8085055 := bstep (se 1 (by rfl) ⟨6063791, by rfl⟩ : syracuseStep 8085055 = 12127583) B12127583
theorem B10780073 : Blo 2211435 10780073 := bstep (se 2 (by rfl) ⟨4042527, by rfl⟩ : syracuseStep 10780073 = 8085055) B8085055
theorem B7186715 : Blo 2211435 7186715 := bstep (se 1 (by rfl) ⟨5390036, by rfl⟩ : syracuseStep 7186715 = 10780073) B10780073
theorem B4791143 : Blo 2211435 4791143 := bstep (se 1 (by rfl) ⟨3593357, by rfl⟩ : syracuseStep 4791143 = 7186715) B7186715
theorem B3194095 : Blo 2211435 3194095 := bstep (se 1 (by rfl) ⟨2395571, by rfl⟩ : syracuseStep 3194095 = 4791143) B4791143
theorem B4258793 : Blo 2211435 4258793 := bstep (se 2 (by rfl) ⟨1597047, by rfl⟩ : syracuseStep 4258793 = 3194095) B3194095
theorem B2839195 : Blo 2211435 2839195 := bstep (se 1 (by rfl) ⟨2129396, by rfl⟩ : syracuseStep 2839195 = 4258793) B4258793
theorem B15142373 : Blo 2211435 15142373 := bstep (se 4 (by rfl) ⟨1419597, by rfl⟩ : syracuseStep 15142373 = 2839195) B2839195
theorem B10094915 : Blo 2211435 10094915 := bstep (se 1 (by rfl) ⟨7571186, by rfl⟩ : syracuseStep 10094915 = 15142373) B15142373
theorem B26919773 : Blo 2211435 26919773 := bstep (se 3 (by rfl) ⟨5047457, by rfl⟩ : syracuseStep 26919773 = 10094915) B10094915
theorem B17946515 : Blo 2211435 17946515 := bstep (se 1 (by rfl) ⟨13459886, by rfl⟩ : syracuseStep 17946515 = 26919773) B26919773
theorem B11964343 : Blo 2211435 11964343 := bstep (se 1 (by rfl) ⟨8973257, by rfl⟩ : syracuseStep 11964343 = 17946515) B17946515
theorem B15952457 : Blo 2211435 15952457 := bstep (se 2 (by rfl) ⟨5982171, by rfl⟩ : syracuseStep 15952457 = 11964343) B11964343
theorem B10634971 : Blo 2211435 10634971 := bstep (se 1 (by rfl) ⟨7976228, by rfl⟩ : syracuseStep 10634971 = 15952457) B15952457
theorem B14179961 : Blo 2211435 14179961 := bstep (se 2 (by rfl) ⟨5317485, by rfl⟩ : syracuseStep 14179961 = 10634971) B10634971
theorem B37813229 : Blo 2211435 37813229 := bstep (se 3 (by rfl) ⟨7089980, by rfl⟩ : syracuseStep 37813229 = 14179961) B14179961
theorem B25208819 : Blo 2211435 25208819 := bstep (se 1 (by rfl) ⟨18906614, by rfl⟩ : syracuseStep 25208819 = 37813229) B37813229
theorem B16805879 : Blo 2211435 16805879 := bstep (se 1 (by rfl) ⟨12604409, by rfl⟩ : syracuseStep 16805879 = 25208819) B25208819
theorem B11203919 : Blo 2211435 11203919 := bstep (se 1 (by rfl) ⟨8402939, by rfl⟩ : syracuseStep 11203919 = 16805879) B16805879
theorem B7469279 : Blo 2211435 7469279 := bstep (se 1 (by rfl) ⟨5601959, by rfl⟩ : syracuseStep 7469279 = 11203919) B11203919
theorem B4979519 : Blo 2211435 4979519 := bstep (se 1 (by rfl) ⟨3734639, by rfl⟩ : syracuseStep 4979519 = 7469279) B7469279
theorem B3319679 : Blo 2211435 3319679 := bstep (se 1 (by rfl) ⟨2489759, by rfl⟩ : syracuseStep 3319679 = 4979519) B4979519
theorem B2213119 : Blo 2211435 2213119 := bstep (se 1 (by rfl) ⟨1659839, by rfl⟩ : syracuseStep 2213119 = 3319679) B3319679
theorem B3319685 : Blo 2211435 3319685 := bbase (se 4 (by rfl) ⟨311220, by rfl⟩ : syracuseStep 3319685 = 622441) (by norm_num)
theorem B2213123 : Blo 2211435 2213123 := bstep (se 1 (by rfl) ⟨1659842, by rfl⟩ : syracuseStep 2213123 = 3319685) B3319685
theorem B3734653 : Blo 2211435 3734653 := bbase (se 3 (by rfl) ⟨700247, by rfl⟩ : syracuseStep 3734653 = 1400495) (by norm_num)
theorem B4979537 : Blo 2211435 4979537 := bstep (se 2 (by rfl) ⟨1867326, by rfl⟩ : syracuseStep 4979537 = 3734653) B3734653
theorem B3319691 : Blo 2211435 3319691 := bstep (se 1 (by rfl) ⟨2489768, by rfl⟩ : syracuseStep 3319691 = 4979537) B4979537
theorem B2213127 : Blo 2211435 2213127 := bstep (se 1 (by rfl) ⟨1659845, by rfl⟩ : syracuseStep 2213127 = 3319691) B3319691
theorem B2489773 : Blo 2211435 2489773 := bbase (se 3 (by rfl) ⟨466832, by rfl⟩ : syracuseStep 2489773 = 933665) (by norm_num)
theorem B3319697 : Blo 2211435 3319697 := bstep (se 2 (by rfl) ⟨1244886, by rfl⟩ : syracuseStep 3319697 = 2489773) B2489773
theorem B2213131 : Blo 2211435 2213131 := bstep (se 1 (by rfl) ⟨1659848, by rfl⟩ : syracuseStep 2213131 = 3319697) B3319697
theorem B7469333 : Blo 2211435 7469333 := bbase (se 6 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 7469333 = 350125) (by norm_num)
theorem B4979555 : Blo 2211435 4979555 := bstep (se 1 (by rfl) ⟨3734666, by rfl⟩ : syracuseStep 4979555 = 7469333) B7469333
theorem B3319703 : Blo 2211435 3319703 := bstep (se 1 (by rfl) ⟨2489777, by rfl⟩ : syracuseStep 3319703 = 4979555) B4979555
theorem B2213135 : Blo 2211435 2213135 := bstep (se 1 (by rfl) ⟨1659851, by rfl⟩ : syracuseStep 2213135 = 3319703) B3319703
theorem B3319709 : Blo 2211435 3319709 := bbase (se 3 (by rfl) ⟨622445, by rfl⟩ : syracuseStep 3319709 = 1244891) (by norm_num)
theorem B2213139 : Blo 2211435 2213139 := bstep (se 1 (by rfl) ⟨1659854, by rfl⟩ : syracuseStep 2213139 = 3319709) B3319709
theorem B4979573 : Blo 2211435 4979573 := bbase (se 5 (by rfl) ⟨233417, by rfl⟩ : syracuseStep 4979573 = 466835) (by norm_num)
theorem B3319715 : Blo 2211435 3319715 := bstep (se 1 (by rfl) ⟨2489786, by rfl⟩ : syracuseStep 3319715 = 4979573) B4979573
theorem B2213143 : Blo 2211435 2213143 := bstep (se 1 (by rfl) ⟨1659857, by rfl⟩ : syracuseStep 2213143 = 3319715) B3319715
theorem B2523761 : Blo 2211435 2523761 := bbase (se 2 (by rfl) ⟨946410, by rfl⟩ : syracuseStep 2523761 = 1892821) (by norm_num)
theorem B26920117 : Blo 2211435 26920117 := bstep (se 5 (by rfl) ⟨1261880, by rfl⟩ : syracuseStep 26920117 = 2523761) B2523761
theorem B35893489 : Blo 2211435 35893489 := bstep (se 2 (by rfl) ⟨13460058, by rfl⟩ : syracuseStep 35893489 = 26920117) B26920117
theorem B47857985 : Blo 2211435 47857985 := bstep (se 2 (by rfl) ⟨17946744, by rfl⟩ : syracuseStep 47857985 = 35893489) B35893489
theorem B31905323 : Blo 2211435 31905323 := bstep (se 1 (by rfl) ⟨23928992, by rfl⟩ : syracuseStep 31905323 = 47857985) B47857985
theorem B21270215 : Blo 2211435 21270215 := bstep (se 1 (by rfl) ⟨15952661, by rfl⟩ : syracuseStep 21270215 = 31905323) B31905323
theorem B14180143 : Blo 2211435 14180143 := bstep (se 1 (by rfl) ⟨10635107, by rfl⟩ : syracuseStep 14180143 = 21270215) B21270215
theorem B18906857 : Blo 2211435 18906857 := bstep (se 2 (by rfl) ⟨7090071, by rfl⟩ : syracuseStep 18906857 = 14180143) B14180143
theorem B12604571 : Blo 2211435 12604571 := bstep (se 1 (by rfl) ⟨9453428, by rfl⟩ : syracuseStep 12604571 = 18906857) B18906857
theorem B8403047 : Blo 2211435 8403047 := bstep (se 1 (by rfl) ⟨6302285, by rfl⟩ : syracuseStep 8403047 = 12604571) B12604571
theorem B5602031 : Blo 2211435 5602031 := bstep (se 1 (by rfl) ⟨4201523, by rfl⟩ : syracuseStep 5602031 = 8403047) B8403047
theorem B3734687 : Blo 2211435 3734687 := bstep (se 1 (by rfl) ⟨2801015, by rfl⟩ : syracuseStep 3734687 = 5602031) B5602031
theorem B2489791 : Blo 2211435 2489791 := bstep (se 1 (by rfl) ⟨1867343, by rfl⟩ : syracuseStep 2489791 = 3734687) B3734687
theorem B3319721 : Blo 2211435 3319721 := bstep (se 2 (by rfl) ⟨1244895, by rfl⟩ : syracuseStep 3319721 = 2489791) B2489791
theorem B2213147 : Blo 2211435 2213147 := bstep (se 1 (by rfl) ⟨1659860, by rfl⟩ : syracuseStep 2213147 = 3319721) B3319721
theorem B8403061 : Blo 2211435 8403061 := bbase (se 5 (by rfl) ⟨393893, by rfl⟩ : syracuseStep 8403061 = 787787) (by norm_num)
theorem B11204081 : Blo 2211435 11204081 := bstep (se 2 (by rfl) ⟨4201530, by rfl⟩ : syracuseStep 11204081 = 8403061) B8403061
theorem B7469387 : Blo 2211435 7469387 := bstep (se 1 (by rfl) ⟨5602040, by rfl⟩ : syracuseStep 7469387 = 11204081) B11204081
theorem B4979591 : Blo 2211435 4979591 := bstep (se 1 (by rfl) ⟨3734693, by rfl⟩ : syracuseStep 4979591 = 7469387) B7469387
theorem B3319727 : Blo 2211435 3319727 := bstep (se 1 (by rfl) ⟨2489795, by rfl⟩ : syracuseStep 3319727 = 4979591) B4979591
theorem B2213151 : Blo 2211435 2213151 := bstep (se 1 (by rfl) ⟨1659863, by rfl⟩ : syracuseStep 2213151 = 3319727) B3319727
theorem B3319733 : Blo 2211435 3319733 := bbase (se 5 (by rfl) ⟨155612, by rfl⟩ : syracuseStep 3319733 = 311225) (by norm_num)
theorem B2213155 : Blo 2211435 2213155 := bstep (se 1 (by rfl) ⟨1659866, by rfl⟩ : syracuseStep 2213155 = 3319733) B3319733
theorem B5602061 : Blo 2211435 5602061 := bbase (se 3 (by rfl) ⟨1050386, by rfl⟩ : syracuseStep 5602061 = 2100773) (by norm_num)
theorem B3734707 : Blo 2211435 3734707 := bstep (se 1 (by rfl) ⟨2801030, by rfl⟩ : syracuseStep 3734707 = 5602061) B5602061
theorem B4979609 : Blo 2211435 4979609 := bstep (se 2 (by rfl) ⟨1867353, by rfl⟩ : syracuseStep 4979609 = 3734707) B3734707
theorem B3319739 : Blo 2211435 3319739 := bstep (se 1 (by rfl) ⟨2489804, by rfl⟩ : syracuseStep 3319739 = 4979609) B4979609
theorem B2213159 : Blo 2211435 2213159 := bstep (se 1 (by rfl) ⟨1659869, by rfl⟩ : syracuseStep 2213159 = 3319739) B3319739
theorem B2489809 : Blo 2211435 2489809 := bbase (se 2 (by rfl) ⟨933678, by rfl⟩ : syracuseStep 2489809 = 1867357) (by norm_num)
theorem B3319745 : Blo 2211435 3319745 := bstep (se 2 (by rfl) ⟨1244904, by rfl⟩ : syracuseStep 3319745 = 2489809) B2489809
theorem B2213163 : Blo 2211435 2213163 := bstep (se 1 (by rfl) ⟨1659872, by rfl⟩ : syracuseStep 2213163 = 3319745) B3319745
theorem B4726757 : Blo 2211435 4726757 := bbase (se 4 (by rfl) ⟨443133, by rfl⟩ : syracuseStep 4726757 = 886267) (by norm_num)
theorem B3151171 : Blo 2211435 3151171 := bstep (se 1 (by rfl) ⟨2363378, by rfl⟩ : syracuseStep 3151171 = 4726757) B4726757
theorem B4201561 : Blo 2211435 4201561 := bstep (se 2 (by rfl) ⟨1575585, by rfl⟩ : syracuseStep 4201561 = 3151171) B3151171
theorem B5602081 : Blo 2211435 5602081 := bstep (se 2 (by rfl) ⟨2100780, by rfl⟩ : syracuseStep 5602081 = 4201561) B4201561
theorem B7469441 : Blo 2211435 7469441 := bstep (se 2 (by rfl) ⟨2801040, by rfl⟩ : syracuseStep 7469441 = 5602081) B5602081
theorem B4979627 : Blo 2211435 4979627 := bstep (se 1 (by rfl) ⟨3734720, by rfl⟩ : syracuseStep 4979627 = 7469441) B7469441
theorem B3319751 : Blo 2211435 3319751 := bstep (se 1 (by rfl) ⟨2489813, by rfl⟩ : syracuseStep 3319751 = 4979627) B4979627
theorem B2213167 : Blo 2211435 2213167 := bstep (se 1 (by rfl) ⟨1659875, by rfl⟩ : syracuseStep 2213167 = 3319751) B3319751
theorem B3319757 : Blo 2211435 3319757 := bbase (se 3 (by rfl) ⟨622454, by rfl⟩ : syracuseStep 3319757 = 1244909) (by norm_num)
theorem B2213171 : Blo 2211435 2213171 := bstep (se 1 (by rfl) ⟨1659878, by rfl⟩ : syracuseStep 2213171 = 3319757) B3319757
theorem B4979645 : Blo 2211435 4979645 := bbase (se 3 (by rfl) ⟨933683, by rfl⟩ : syracuseStep 4979645 = 1867367) (by norm_num)
theorem B3319763 : Blo 2211435 3319763 := bstep (se 1 (by rfl) ⟨2489822, by rfl⟩ : syracuseStep 3319763 = 4979645) B4979645
theorem B2213175 : Blo 2211435 2213175 := bstep (se 1 (by rfl) ⟨1659881, by rfl⟩ : syracuseStep 2213175 = 3319763) B3319763
theorem B3734741 : Blo 2211435 3734741 := bbase (se 7 (by rfl) ⟨43766, by rfl⟩ : syracuseStep 3734741 = 87533) (by norm_num)
theorem B2489827 : Blo 2211435 2489827 := bstep (se 1 (by rfl) ⟨1867370, by rfl⟩ : syracuseStep 2489827 = 3734741) B3734741
theorem B3319769 : Blo 2211435 3319769 := bstep (se 2 (by rfl) ⟨1244913, by rfl⟩ : syracuseStep 3319769 = 2489827) B2489827
theorem B2213179 : Blo 2211435 2213179 := bstep (se 1 (by rfl) ⟨1659884, by rfl⟩ : syracuseStep 2213179 = 3319769) B3319769
theorem B3545093 : Blo 2211435 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B9453581 : Blo 2211435 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B6302387 : Blo 2211435 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B16806365 : Blo 2211435 16806365 := bstep (se 3 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 16806365 = 6302387) B6302387
theorem B11204243 : Blo 2211435 11204243 := bstep (se 1 (by rfl) ⟨8403182, by rfl⟩ : syracuseStep 11204243 = 16806365) B16806365
theorem B7469495 : Blo 2211435 7469495 := bstep (se 1 (by rfl) ⟨5602121, by rfl⟩ : syracuseStep 7469495 = 11204243) B11204243
theorem B4979663 : Blo 2211435 4979663 := bstep (se 1 (by rfl) ⟨3734747, by rfl⟩ : syracuseStep 4979663 = 7469495) B7469495
theorem B3319775 : Blo 2211435 3319775 := bstep (se 1 (by rfl) ⟨2489831, by rfl⟩ : syracuseStep 3319775 = 4979663) B4979663
theorem B2213183 : Blo 2211435 2213183 := bstep (se 1 (by rfl) ⟨1659887, by rfl⟩ : syracuseStep 2213183 = 3319775) B3319775
theorem B3319781 : Blo 2211435 3319781 := bbase (se 4 (by rfl) ⟨311229, by rfl⟩ : syracuseStep 3319781 = 622459) (by norm_num)
theorem B2213187 : Blo 2211435 2213187 := bstep (se 1 (by rfl) ⟨1659890, by rfl⟩ : syracuseStep 2213187 = 3319781) B3319781
theorem B7090213 : Blo 2211435 7090213 := bbase (se 4 (by rfl) ⟨664707, by rfl⟩ : syracuseStep 7090213 = 1329415) (by norm_num)
theorem B9453617 : Blo 2211435 9453617 := bstep (se 2 (by rfl) ⟨3545106, by rfl⟩ : syracuseStep 9453617 = 7090213) B7090213
theorem B6302411 : Blo 2211435 6302411 := bstep (se 1 (by rfl) ⟨4726808, by rfl⟩ : syracuseStep 6302411 = 9453617) B9453617
theorem B4201607 : Blo 2211435 4201607 := bstep (se 1 (by rfl) ⟨3151205, by rfl⟩ : syracuseStep 4201607 = 6302411) B6302411
theorem B2801071 : Blo 2211435 2801071 := bstep (se 1 (by rfl) ⟨2100803, by rfl⟩ : syracuseStep 2801071 = 4201607) B4201607
theorem B3734761 : Blo 2211435 3734761 := bstep (se 2 (by rfl) ⟨1400535, by rfl⟩ : syracuseStep 3734761 = 2801071) B2801071
theorem B4979681 : Blo 2211435 4979681 := bstep (se 2 (by rfl) ⟨1867380, by rfl⟩ : syracuseStep 4979681 = 3734761) B3734761
theorem B3319787 : Blo 2211435 3319787 := bstep (se 1 (by rfl) ⟨2489840, by rfl⟩ : syracuseStep 3319787 = 4979681) B4979681
theorem B2213191 : Blo 2211435 2213191 := bstep (se 1 (by rfl) ⟨1659893, by rfl⟩ : syracuseStep 2213191 = 3319787) B3319787
theorem B2489845 : Blo 2211435 2489845 := bbase (se 5 (by rfl) ⟨116711, by rfl⟩ : syracuseStep 2489845 = 233423) (by norm_num)
theorem B3319793 : Blo 2211435 3319793 := bstep (se 2 (by rfl) ⟨1244922, by rfl⟩ : syracuseStep 3319793 = 2489845) B2489845
theorem B2213195 : Blo 2211435 2213195 := bstep (se 1 (by rfl) ⟨1659896, by rfl⟩ : syracuseStep 2213195 = 3319793) B3319793
theorem B2801081 : Blo 2211435 2801081 := bbase (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) (by norm_num)
theorem B7469549 : Blo 2211435 7469549 := bstep (se 3 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 7469549 = 2801081) B2801081
theorem B4979699 : Blo 2211435 4979699 := bstep (se 1 (by rfl) ⟨3734774, by rfl⟩ : syracuseStep 4979699 = 7469549) B7469549
theorem B3319799 : Blo 2211435 3319799 := bstep (se 1 (by rfl) ⟨2489849, by rfl⟩ : syracuseStep 3319799 = 4979699) B4979699
theorem B2213199 : Blo 2211435 2213199 := bstep (se 1 (by rfl) ⟨1659899, by rfl⟩ : syracuseStep 2213199 = 3319799) B3319799
theorem B3319805 : Blo 2211435 3319805 := bbase (se 3 (by rfl) ⟨622463, by rfl⟩ : syracuseStep 3319805 = 1244927) (by norm_num)
theorem B2213203 : Blo 2211435 2213203 := bstep (se 1 (by rfl) ⟨1659902, by rfl⟩ : syracuseStep 2213203 = 3319805) B3319805
theorem B4979717 : Blo 2211435 4979717 := bbase (se 4 (by rfl) ⟨466848, by rfl⟩ : syracuseStep 4979717 = 933697) (by norm_num)
theorem B3319811 : Blo 2211435 3319811 := bstep (se 1 (by rfl) ⟨2489858, by rfl⟩ : syracuseStep 3319811 = 4979717) B4979717
theorem B2213207 : Blo 2211435 2213207 := bstep (se 1 (by rfl) ⟨1659905, by rfl⟩ : syracuseStep 2213207 = 3319811) B3319811
theorem B4201645 : Blo 2211435 4201645 := bbase (se 3 (by rfl) ⟨787808, by rfl⟩ : syracuseStep 4201645 = 1575617) (by norm_num)
theorem B5602193 : Blo 2211435 5602193 := bstep (se 2 (by rfl) ⟨2100822, by rfl⟩ : syracuseStep 5602193 = 4201645) B4201645
theorem B3734795 : Blo 2211435 3734795 := bstep (se 1 (by rfl) ⟨2801096, by rfl⟩ : syracuseStep 3734795 = 5602193) B5602193
theorem B2489863 : Blo 2211435 2489863 := bstep (se 1 (by rfl) ⟨1867397, by rfl⟩ : syracuseStep 2489863 = 3734795) B3734795
theorem B3319817 : Blo 2211435 3319817 := bstep (se 2 (by rfl) ⟨1244931, by rfl⟩ : syracuseStep 3319817 = 2489863) B2489863
theorem B2213211 : Blo 2211435 2213211 := bstep (se 1 (by rfl) ⟨1659908, by rfl⟩ : syracuseStep 2213211 = 3319817) B3319817
theorem B11204405 : Blo 2211435 11204405 := bbase (se 5 (by rfl) ⟨525206, by rfl⟩ : syracuseStep 11204405 = 1050413) (by norm_num)
theorem B7469603 : Blo 2211435 7469603 := bstep (se 1 (by rfl) ⟨5602202, by rfl⟩ : syracuseStep 7469603 = 11204405) B11204405
theorem B4979735 : Blo 2211435 4979735 := bstep (se 1 (by rfl) ⟨3734801, by rfl⟩ : syracuseStep 4979735 = 7469603) B7469603
theorem B3319823 : Blo 2211435 3319823 := bstep (se 1 (by rfl) ⟨2489867, by rfl⟩ : syracuseStep 3319823 = 4979735) B4979735
theorem B2213215 : Blo 2211435 2213215 := bstep (se 1 (by rfl) ⟨1659911, by rfl⟩ : syracuseStep 2213215 = 3319823) B3319823
theorem B3319829 : Blo 2211435 3319829 := bbase (se 6 (by rfl) ⟨77808, by rfl⟩ : syracuseStep 3319829 = 155617) (by norm_num)
theorem B2213219 : Blo 2211435 2213219 := bstep (se 1 (by rfl) ⟨1659914, by rfl⟩ : syracuseStep 2213219 = 3319829) B3319829
theorem B14180629 : Blo 2211435 14180629 := bbase (se 6 (by rfl) ⟨332358, by rfl⟩ : syracuseStep 14180629 = 664717) (by norm_num)
theorem B18907505 : Blo 2211435 18907505 := bstep (se 2 (by rfl) ⟨7090314, by rfl⟩ : syracuseStep 18907505 = 14180629) B14180629
theorem B12605003 : Blo 2211435 12605003 := bstep (se 1 (by rfl) ⟨9453752, by rfl⟩ : syracuseStep 12605003 = 18907505) B18907505
theorem B8403335 : Blo 2211435 8403335 := bstep (se 1 (by rfl) ⟨6302501, by rfl⟩ : syracuseStep 8403335 = 12605003) B12605003
theorem B5602223 : Blo 2211435 5602223 := bstep (se 1 (by rfl) ⟨4201667, by rfl⟩ : syracuseStep 5602223 = 8403335) B8403335
theorem B3734815 : Blo 2211435 3734815 := bstep (se 1 (by rfl) ⟨2801111, by rfl⟩ : syracuseStep 3734815 = 5602223) B5602223
theorem B4979753 : Blo 2211435 4979753 := bstep (se 2 (by rfl) ⟨1867407, by rfl⟩ : syracuseStep 4979753 = 3734815) B3734815
theorem B3319835 : Blo 2211435 3319835 := bstep (se 1 (by rfl) ⟨2489876, by rfl⟩ : syracuseStep 3319835 = 4979753) B4979753
theorem B2213223 : Blo 2211435 2213223 := bstep (se 1 (by rfl) ⟨1659917, by rfl⟩ : syracuseStep 2213223 = 3319835) B3319835
theorem B2489881 : Blo 2211435 2489881 := bbase (se 2 (by rfl) ⟨933705, by rfl⟩ : syracuseStep 2489881 = 1867411) (by norm_num)
theorem B3319841 : Blo 2211435 3319841 := bstep (se 2 (by rfl) ⟨1244940, by rfl⟩ : syracuseStep 3319841 = 2489881) B2489881
theorem B2213227 : Blo 2211435 2213227 := bstep (se 1 (by rfl) ⟨1659920, by rfl⟩ : syracuseStep 2213227 = 3319841) B3319841
theorem B8403365 : Blo 2211435 8403365 := bbase (se 4 (by rfl) ⟨787815, by rfl⟩ : syracuseStep 8403365 = 1575631) (by norm_num)
theorem B5602243 : Blo 2211435 5602243 := bstep (se 1 (by rfl) ⟨4201682, by rfl⟩ : syracuseStep 5602243 = 8403365) B8403365
theorem B7469657 : Blo 2211435 7469657 := bstep (se 2 (by rfl) ⟨2801121, by rfl⟩ : syracuseStep 7469657 = 5602243) B5602243
theorem B4979771 : Blo 2211435 4979771 := bstep (se 1 (by rfl) ⟨3734828, by rfl⟩ : syracuseStep 4979771 = 7469657) B7469657
theorem B3319847 : Blo 2211435 3319847 := bstep (se 1 (by rfl) ⟨2489885, by rfl⟩ : syracuseStep 3319847 = 4979771) B4979771
theorem B2213231 : Blo 2211435 2213231 := bstep (se 1 (by rfl) ⟨1659923, by rfl⟩ : syracuseStep 2213231 = 3319847) B3319847
theorem B3319853 : Blo 2211435 3319853 := bbase (se 3 (by rfl) ⟨622472, by rfl⟩ : syracuseStep 3319853 = 1244945) (by norm_num)
theorem B2213235 : Blo 2211435 2213235 := bstep (se 1 (by rfl) ⟨1659926, by rfl⟩ : syracuseStep 2213235 = 3319853) B3319853
theorem B4979789 : Blo 2211435 4979789 := bbase (se 3 (by rfl) ⟨933710, by rfl⟩ : syracuseStep 4979789 = 1867421) (by norm_num)
theorem B3319859 : Blo 2211435 3319859 := bstep (se 1 (by rfl) ⟨2489894, by rfl⟩ : syracuseStep 3319859 = 4979789) B4979789
theorem B2213239 : Blo 2211435 2213239 := bstep (se 1 (by rfl) ⟨1659929, by rfl⟩ : syracuseStep 2213239 = 3319859) B3319859
theorem B2801137 : Blo 2211435 2801137 := bbase (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) (by norm_num)
theorem B3734849 : Blo 2211435 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B2489899 : Blo 2211435 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B3319865 : Blo 2211435 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B2213243 : Blo 2211435 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B4791421 : Blo 2211435 4791421 := bbase (se 3 (by rfl) ⟨898391, by rfl⟩ : syracuseStep 4791421 = 1796783) (by norm_num)
theorem B6388561 : Blo 2211435 6388561 := bstep (se 2 (by rfl) ⟨2395710, by rfl⟩ : syracuseStep 6388561 = 4791421) B4791421
theorem B8518081 : Blo 2211435 8518081 := bstep (se 2 (by rfl) ⟨3194280, by rfl⟩ : syracuseStep 8518081 = 6388561) B6388561
theorem B11357441 : Blo 2211435 11357441 := bstep (se 2 (by rfl) ⟨4259040, by rfl⟩ : syracuseStep 11357441 = 8518081) B8518081
theorem B7571627 : Blo 2211435 7571627 := bstep (se 1 (by rfl) ⟨5678720, by rfl⟩ : syracuseStep 7571627 = 11357441) B11357441
theorem B5047751 : Blo 2211435 5047751 := bstep (se 1 (by rfl) ⟨3785813, by rfl⟩ : syracuseStep 5047751 = 7571627) B7571627
theorem B3365167 : Blo 2211435 3365167 := bstep (se 1 (by rfl) ⟨2523875, by rfl⟩ : syracuseStep 3365167 = 5047751) B5047751
theorem B4486889 : Blo 2211435 4486889 := bstep (se 2 (by rfl) ⟨1682583, by rfl⟩ : syracuseStep 4486889 = 3365167) B3365167
theorem B2991259 : Blo 2211435 2991259 := bstep (se 1 (by rfl) ⟨2243444, by rfl⟩ : syracuseStep 2991259 = 4486889) B4486889
theorem B15953381 : Blo 2211435 15953381 := bstep (se 4 (by rfl) ⟨1495629, by rfl⟩ : syracuseStep 15953381 = 2991259) B2991259
theorem B10635587 : Blo 2211435 10635587 := bstep (se 1 (by rfl) ⟨7976690, by rfl⟩ : syracuseStep 10635587 = 15953381) B15953381
theorem B7090391 : Blo 2211435 7090391 := bstep (se 1 (by rfl) ⟨5317793, by rfl⟩ : syracuseStep 7090391 = 10635587) B10635587
theorem B4726927 : Blo 2211435 4726927 := bstep (se 1 (by rfl) ⟨3545195, by rfl⟩ : syracuseStep 4726927 = 7090391) B7090391
theorem B25210277 : Blo 2211435 25210277 := bstep (se 4 (by rfl) ⟨2363463, by rfl⟩ : syracuseStep 25210277 = 4726927) B4726927
theorem B16806851 : Blo 2211435 16806851 := bstep (se 1 (by rfl) ⟨12605138, by rfl⟩ : syracuseStep 16806851 = 25210277) B25210277
theorem B11204567 : Blo 2211435 11204567 := bstep (se 1 (by rfl) ⟨8403425, by rfl⟩ : syracuseStep 11204567 = 16806851) B16806851
theorem B7469711 : Blo 2211435 7469711 := bstep (se 1 (by rfl) ⟨5602283, by rfl⟩ : syracuseStep 7469711 = 11204567) B11204567
theorem B4979807 : Blo 2211435 4979807 := bstep (se 1 (by rfl) ⟨3734855, by rfl⟩ : syracuseStep 4979807 = 7469711) B7469711
theorem B3319871 : Blo 2211435 3319871 := bstep (se 1 (by rfl) ⟨2489903, by rfl⟩ : syracuseStep 3319871 = 4979807) B4979807
theorem B2213247 : Blo 2211435 2213247 := bstep (se 1 (by rfl) ⟨1659935, by rfl⟩ : syracuseStep 2213247 = 3319871) B3319871
theorem B3319877 : Blo 2211435 3319877 := bbase (se 4 (by rfl) ⟨311238, by rfl⟩ : syracuseStep 3319877 = 622477) (by norm_num)
theorem B2213251 : Blo 2211435 2213251 := bstep (se 1 (by rfl) ⟨1659938, by rfl⟩ : syracuseStep 2213251 = 3319877) B3319877
theorem B3734869 : Blo 2211435 3734869 := bbase (se 11 (by rfl) ⟨2735, by rfl⟩ : syracuseStep 3734869 = 5471) (by norm_num)
theorem B4979825 : Blo 2211435 4979825 := bstep (se 2 (by rfl) ⟨1867434, by rfl⟩ : syracuseStep 4979825 = 3734869) B3734869
theorem B3319883 : Blo 2211435 3319883 := bstep (se 1 (by rfl) ⟨2489912, by rfl⟩ : syracuseStep 3319883 = 4979825) B4979825
theorem B2213255 : Blo 2211435 2213255 := bstep (se 1 (by rfl) ⟨1659941, by rfl⟩ : syracuseStep 2213255 = 3319883) B3319883
theorem B2489917 : Blo 2211435 2489917 := bbase (se 3 (by rfl) ⟨466859, by rfl⟩ : syracuseStep 2489917 = 933719) (by norm_num)
theorem B3319889 : Blo 2211435 3319889 := bstep (se 2 (by rfl) ⟨1244958, by rfl⟩ : syracuseStep 3319889 = 2489917) B2489917
theorem B2213259 : Blo 2211435 2213259 := bstep (se 1 (by rfl) ⟨1659944, by rfl⟩ : syracuseStep 2213259 = 3319889) B3319889
theorem B7469765 : Blo 2211435 7469765 := bbase (se 4 (by rfl) ⟨700290, by rfl⟩ : syracuseStep 7469765 = 1400581) (by norm_num)
theorem B4979843 : Blo 2211435 4979843 := bstep (se 1 (by rfl) ⟨3734882, by rfl⟩ : syracuseStep 4979843 = 7469765) B7469765
theorem B3319895 : Blo 2211435 3319895 := bstep (se 1 (by rfl) ⟨2489921, by rfl⟩ : syracuseStep 3319895 = 4979843) B4979843
theorem B2213263 : Blo 2211435 2213263 := bstep (se 1 (by rfl) ⟨1659947, by rfl⟩ : syracuseStep 2213263 = 3319895) B3319895
theorem B3319901 : Blo 2211435 3319901 := bbase (se 3 (by rfl) ⟨622481, by rfl⟩ : syracuseStep 3319901 = 1244963) (by norm_num)
theorem B2213267 : Blo 2211435 2213267 := bstep (se 1 (by rfl) ⟨1659950, by rfl⟩ : syracuseStep 2213267 = 3319901) B3319901
theorem B4979861 : Blo 2211435 4979861 := bbase (se 6 (by rfl) ⟨116715, by rfl⟩ : syracuseStep 4979861 = 233431) (by norm_num)
theorem B3319907 : Blo 2211435 3319907 := bstep (se 1 (by rfl) ⟨2489930, by rfl⟩ : syracuseStep 3319907 = 4979861) B4979861
theorem B2213271 : Blo 2211435 2213271 := bstep (se 1 (by rfl) ⟨1659953, by rfl⟩ : syracuseStep 2213271 = 3319907) B3319907
theorem B3151325 : Blo 2211435 3151325 := bbase (se 3 (by rfl) ⟨590873, by rfl⟩ : syracuseStep 3151325 = 1181747) (by norm_num)
theorem B8403533 : Blo 2211435 8403533 := bstep (se 3 (by rfl) ⟨1575662, by rfl⟩ : syracuseStep 8403533 = 3151325) B3151325
theorem B5602355 : Blo 2211435 5602355 := bstep (se 1 (by rfl) ⟨4201766, by rfl⟩ : syracuseStep 5602355 = 8403533) B8403533
theorem B3734903 : Blo 2211435 3734903 := bstep (se 1 (by rfl) ⟨2801177, by rfl⟩ : syracuseStep 3734903 = 5602355) B5602355
theorem B2489935 : Blo 2211435 2489935 := bstep (se 1 (by rfl) ⟨1867451, by rfl⟩ : syracuseStep 2489935 = 3734903) B3734903
theorem B3319913 : Blo 2211435 3319913 := bstep (se 2 (by rfl) ⟨1244967, by rfl⟩ : syracuseStep 3319913 = 2489935) B2489935
theorem B2213275 : Blo 2211435 2213275 := bstep (se 1 (by rfl) ⟨1659956, by rfl⟩ : syracuseStep 2213275 = 3319913) B3319913
theorem B17036405 : Blo 2211435 17036405 := bbase (se 5 (by rfl) ⟨798581, by rfl⟩ : syracuseStep 17036405 = 1597163) (by norm_num)
theorem B11357603 : Blo 2211435 11357603 := bstep (se 1 (by rfl) ⟨8518202, by rfl⟩ : syracuseStep 11357603 = 17036405) B17036405
theorem B7571735 : Blo 2211435 7571735 := bstep (se 1 (by rfl) ⟨5678801, by rfl⟩ : syracuseStep 7571735 = 11357603) B11357603
theorem B5047823 : Blo 2211435 5047823 := bstep (se 1 (by rfl) ⟨3785867, by rfl⟩ : syracuseStep 5047823 = 7571735) B7571735
theorem B3365215 : Blo 2211435 3365215 := bstep (se 1 (by rfl) ⟨2523911, by rfl⟩ : syracuseStep 3365215 = 5047823) B5047823
theorem B17947813 : Blo 2211435 17947813 := bstep (se 4 (by rfl) ⟨1682607, by rfl⟩ : syracuseStep 17947813 = 3365215) B3365215
theorem B23930417 : Blo 2211435 23930417 := bstep (se 2 (by rfl) ⟨8973906, by rfl⟩ : syracuseStep 23930417 = 17947813) B17947813
theorem B15953611 : Blo 2211435 15953611 := bstep (se 1 (by rfl) ⟨11965208, by rfl⟩ : syracuseStep 15953611 = 23930417) B23930417
theorem B21271481 : Blo 2211435 21271481 := bstep (se 2 (by rfl) ⟨7976805, by rfl⟩ : syracuseStep 21271481 = 15953611) B15953611
theorem B14180987 : Blo 2211435 14180987 := bstep (se 1 (by rfl) ⟨10635740, by rfl⟩ : syracuseStep 14180987 = 21271481) B21271481
theorem B9453991 : Blo 2211435 9453991 := bstep (se 1 (by rfl) ⟨7090493, by rfl⟩ : syracuseStep 9453991 = 14180987) B14180987
theorem B12605321 : Blo 2211435 12605321 := bstep (se 2 (by rfl) ⟨4726995, by rfl⟩ : syracuseStep 12605321 = 9453991) B9453991
theorem B8403547 : Blo 2211435 8403547 := bstep (se 1 (by rfl) ⟨6302660, by rfl⟩ : syracuseStep 8403547 = 12605321) B12605321
theorem B11204729 : Blo 2211435 11204729 := bstep (se 2 (by rfl) ⟨4201773, by rfl⟩ : syracuseStep 11204729 = 8403547) B8403547
theorem B7469819 : Blo 2211435 7469819 := bstep (se 1 (by rfl) ⟨5602364, by rfl⟩ : syracuseStep 7469819 = 11204729) B11204729
theorem B4979879 : Blo 2211435 4979879 := bstep (se 1 (by rfl) ⟨3734909, by rfl⟩ : syracuseStep 4979879 = 7469819) B7469819
theorem B3319919 : Blo 2211435 3319919 := bstep (se 1 (by rfl) ⟨2489939, by rfl⟩ : syracuseStep 3319919 = 4979879) B4979879
theorem B2213279 : Blo 2211435 2213279 := bstep (se 1 (by rfl) ⟨1659959, by rfl⟩ : syracuseStep 2213279 = 3319919) B3319919
theorem B3319925 : Blo 2211435 3319925 := bbase (se 5 (by rfl) ⟨155621, by rfl⟩ : syracuseStep 3319925 = 311243) (by norm_num)
theorem B2213283 : Blo 2211435 2213283 := bstep (se 1 (by rfl) ⟨1659962, by rfl⟩ : syracuseStep 2213283 = 3319925) B3319925
theorem B4201789 : Blo 2211435 4201789 := bbase (se 3 (by rfl) ⟨787835, by rfl⟩ : syracuseStep 4201789 = 1575671) (by norm_num)
theorem B5602385 : Blo 2211435 5602385 := bstep (se 2 (by rfl) ⟨2100894, by rfl⟩ : syracuseStep 5602385 = 4201789) B4201789
theorem B3734923 : Blo 2211435 3734923 := bstep (se 1 (by rfl) ⟨2801192, by rfl⟩ : syracuseStep 3734923 = 5602385) B5602385
theorem B4979897 : Blo 2211435 4979897 := bstep (se 2 (by rfl) ⟨1867461, by rfl⟩ : syracuseStep 4979897 = 3734923) B3734923
theorem B3319931 : Blo 2211435 3319931 := bstep (se 1 (by rfl) ⟨2489948, by rfl⟩ : syracuseStep 3319931 = 4979897) B4979897
theorem B2213287 : Blo 2211435 2213287 := bstep (se 1 (by rfl) ⟨1659965, by rfl⟩ : syracuseStep 2213287 = 3319931) B3319931
theorem B2489953 : Blo 2211435 2489953 := bbase (se 2 (by rfl) ⟨933732, by rfl⟩ : syracuseStep 2489953 = 1867465) (by norm_num)
theorem B3319937 : Blo 2211435 3319937 := bstep (se 2 (by rfl) ⟨1244976, by rfl⟩ : syracuseStep 3319937 = 2489953) B2489953
theorem B2213291 : Blo 2211435 2213291 := bstep (se 1 (by rfl) ⟨1659968, by rfl⟩ : syracuseStep 2213291 = 3319937) B3319937
theorem B5602405 : Blo 2211435 5602405 := bbase (se 4 (by rfl) ⟨525225, by rfl⟩ : syracuseStep 5602405 = 1050451) (by norm_num)
theorem B7469873 : Blo 2211435 7469873 := bstep (se 2 (by rfl) ⟨2801202, by rfl⟩ : syracuseStep 7469873 = 5602405) B5602405
theorem B4979915 : Blo 2211435 4979915 := bstep (se 1 (by rfl) ⟨3734936, by rfl⟩ : syracuseStep 4979915 = 7469873) B7469873
theorem B3319943 : Blo 2211435 3319943 := bstep (se 1 (by rfl) ⟨2489957, by rfl⟩ : syracuseStep 3319943 = 4979915) B4979915
theorem B2213295 : Blo 2211435 2213295 := bstep (se 1 (by rfl) ⟨1659971, by rfl⟩ : syracuseStep 2213295 = 3319943) B3319943
theorem B3319949 : Blo 2211435 3319949 := bbase (se 3 (by rfl) ⟨622490, by rfl⟩ : syracuseStep 3319949 = 1244981) (by norm_num)
theorem B2213299 : Blo 2211435 2213299 := bstep (se 1 (by rfl) ⟨1659974, by rfl⟩ : syracuseStep 2213299 = 3319949) B3319949
theorem B4979933 : Blo 2211435 4979933 := bbase (se 3 (by rfl) ⟨933737, by rfl⟩ : syracuseStep 4979933 = 1867475) (by norm_num)
theorem B3319955 : Blo 2211435 3319955 := bstep (se 1 (by rfl) ⟨2489966, by rfl⟩ : syracuseStep 3319955 = 4979933) B4979933
theorem B2213303 : Blo 2211435 2213303 := bstep (se 1 (by rfl) ⟨1659977, by rfl⟩ : syracuseStep 2213303 = 3319955) B3319955
theorem B3734957 : Blo 2211435 3734957 := bbase (se 3 (by rfl) ⟨700304, by rfl⟩ : syracuseStep 3734957 = 1400609) (by norm_num)
theorem B2489971 : Blo 2211435 2489971 := bstep (se 1 (by rfl) ⟨1867478, by rfl⟩ : syracuseStep 2489971 = 3734957) B3734957
theorem B3319961 : Blo 2211435 3319961 := bstep (se 2 (by rfl) ⟨1244985, by rfl⟩ : syracuseStep 3319961 = 2489971) B2489971
theorem B2213307 : Blo 2211435 2213307 := bstep (se 1 (by rfl) ⟨1659980, by rfl⟩ : syracuseStep 2213307 = 3319961) B3319961
theorem B4791557 : Blo 2211435 4791557 := bbase (se 4 (by rfl) ⟨449208, by rfl⟩ : syracuseStep 4791557 = 898417) (by norm_num)
theorem B12777485 : Blo 2211435 12777485 := bstep (se 3 (by rfl) ⟨2395778, by rfl⟩ : syracuseStep 12777485 = 4791557) B4791557
theorem B34073293 : Blo 2211435 34073293 := bstep (se 3 (by rfl) ⟨6388742, by rfl⟩ : syracuseStep 34073293 = 12777485) B12777485
theorem B45431057 : Blo 2211435 45431057 := bstep (se 2 (by rfl) ⟨17036646, by rfl⟩ : syracuseStep 45431057 = 34073293) B34073293
theorem B30287371 : Blo 2211435 30287371 := bstep (se 1 (by rfl) ⟨22715528, by rfl⟩ : syracuseStep 30287371 = 45431057) B45431057
theorem B40383161 : Blo 2211435 40383161 := bstep (se 2 (by rfl) ⟨15143685, by rfl⟩ : syracuseStep 40383161 = 30287371) B30287371
theorem B26922107 : Blo 2211435 26922107 := bstep (se 1 (by rfl) ⟨20191580, by rfl⟩ : syracuseStep 26922107 = 40383161) B40383161
theorem B17948071 : Blo 2211435 17948071 := bstep (se 1 (by rfl) ⟨13461053, by rfl⟩ : syracuseStep 17948071 = 26922107) B26922107
theorem B95723045 : Blo 2211435 95723045 := bstep (se 4 (by rfl) ⟨8974035, by rfl⟩ : syracuseStep 95723045 = 17948071) B17948071
theorem B63815363 : Blo 2211435 63815363 := bstep (se 1 (by rfl) ⟨47861522, by rfl⟩ : syracuseStep 63815363 = 95723045) B95723045
theorem B42543575 : Blo 2211435 42543575 := bstep (se 1 (by rfl) ⟨31907681, by rfl⟩ : syracuseStep 42543575 = 63815363) B63815363
theorem B28362383 : Blo 2211435 28362383 := bstep (se 1 (by rfl) ⟨21271787, by rfl⟩ : syracuseStep 28362383 = 42543575) B42543575
theorem B18908255 : Blo 2211435 18908255 := bstep (se 1 (by rfl) ⟨14181191, by rfl⟩ : syracuseStep 18908255 = 28362383) B28362383
theorem B12605503 : Blo 2211435 12605503 := bstep (se 1 (by rfl) ⟨9454127, by rfl⟩ : syracuseStep 12605503 = 18908255) B18908255
theorem B16807337 : Blo 2211435 16807337 := bstep (se 2 (by rfl) ⟨6302751, by rfl⟩ : syracuseStep 16807337 = 12605503) B12605503
theorem B11204891 : Blo 2211435 11204891 := bstep (se 1 (by rfl) ⟨8403668, by rfl⟩ : syracuseStep 11204891 = 16807337) B16807337
theorem B7469927 : Blo 2211435 7469927 := bstep (se 1 (by rfl) ⟨5602445, by rfl⟩ : syracuseStep 7469927 = 11204891) B11204891
theorem B4979951 : Blo 2211435 4979951 := bstep (se 1 (by rfl) ⟨3734963, by rfl⟩ : syracuseStep 4979951 = 7469927) B7469927
theorem B3319967 : Blo 2211435 3319967 := bstep (se 1 (by rfl) ⟨2489975, by rfl⟩ : syracuseStep 3319967 = 4979951) B4979951
theorem B2213311 : Blo 2211435 2213311 := bstep (se 1 (by rfl) ⟨1659983, by rfl⟩ : syracuseStep 2213311 = 3319967) B3319967
theorem B3319973 : Blo 2211435 3319973 := bbase (se 4 (by rfl) ⟨311247, by rfl⟩ : syracuseStep 3319973 = 622495) (by norm_num)
theorem B2213315 : Blo 2211435 2213315 := bstep (se 1 (by rfl) ⟨1659986, by rfl⟩ : syracuseStep 2213315 = 3319973) B3319973
theorem B2801233 : Blo 2211435 2801233 := bbase (se 2 (by rfl) ⟨1050462, by rfl⟩ : syracuseStep 2801233 = 2100925) (by norm_num)
theorem B3734977 : Blo 2211435 3734977 := bstep (se 2 (by rfl) ⟨1400616, by rfl⟩ : syracuseStep 3734977 = 2801233) B2801233
theorem B4979969 : Blo 2211435 4979969 := bstep (se 2 (by rfl) ⟨1867488, by rfl⟩ : syracuseStep 4979969 = 3734977) B3734977
theorem B3319979 : Blo 2211435 3319979 := bstep (se 1 (by rfl) ⟨2489984, by rfl⟩ : syracuseStep 3319979 = 4979969) B4979969
theorem B2213319 : Blo 2211435 2213319 := bstep (se 1 (by rfl) ⟨1659989, by rfl⟩ : syracuseStep 2213319 = 3319979) B3319979
theorem B2489989 : Blo 2211435 2489989 := bbase (se 4 (by rfl) ⟨233436, by rfl⟩ : syracuseStep 2489989 = 466873) (by norm_num)
theorem B3319985 : Blo 2211435 3319985 := bstep (se 2 (by rfl) ⟨1244994, by rfl⟩ : syracuseStep 3319985 = 2489989) B2489989
theorem B2213323 : Blo 2211435 2213323 := bstep (se 1 (by rfl) ⟨1659992, by rfl⟩ : syracuseStep 2213323 = 3319985) B3319985
theorem B7976981 : Blo 2211435 7976981 := bbase (se 6 (by rfl) ⟨186960, by rfl⟩ : syracuseStep 7976981 = 373921) (by norm_num)
theorem B5317987 : Blo 2211435 5317987 := bstep (se 1 (by rfl) ⟨3988490, by rfl⟩ : syracuseStep 5317987 = 7976981) B7976981
theorem B7090649 : Blo 2211435 7090649 := bstep (se 2 (by rfl) ⟨2658993, by rfl⟩ : syracuseStep 7090649 = 5317987) B5317987
theorem B4727099 : Blo 2211435 4727099 := bstep (se 1 (by rfl) ⟨3545324, by rfl⟩ : syracuseStep 4727099 = 7090649) B7090649
theorem B3151399 : Blo 2211435 3151399 := bstep (se 1 (by rfl) ⟨2363549, by rfl⟩ : syracuseStep 3151399 = 4727099) B4727099
theorem B4201865 : Blo 2211435 4201865 := bstep (se 2 (by rfl) ⟨1575699, by rfl⟩ : syracuseStep 4201865 = 3151399) B3151399
theorem B2801243 : Blo 2211435 2801243 := bstep (se 1 (by rfl) ⟨2100932, by rfl⟩ : syracuseStep 2801243 = 4201865) B4201865
theorem B7469981 : Blo 2211435 7469981 := bstep (se 3 (by rfl) ⟨1400621, by rfl⟩ : syracuseStep 7469981 = 2801243) B2801243
theorem B4979987 : Blo 2211435 4979987 := bstep (se 1 (by rfl) ⟨3734990, by rfl⟩ : syracuseStep 4979987 = 7469981) B7469981
theorem B3319991 : Blo 2211435 3319991 := bstep (se 1 (by rfl) ⟨2489993, by rfl⟩ : syracuseStep 3319991 = 4979987) B4979987
theorem B2213327 : Blo 2211435 2213327 := bstep (se 1 (by rfl) ⟨1659995, by rfl⟩ : syracuseStep 2213327 = 3319991) B3319991
theorem B3319997 : Blo 2211435 3319997 := bbase (se 3 (by rfl) ⟨622499, by rfl⟩ : syracuseStep 3319997 = 1244999) (by norm_num)
theorem B2213331 : Blo 2211435 2213331 := bstep (se 1 (by rfl) ⟨1659998, by rfl⟩ : syracuseStep 2213331 = 3319997) B3319997
theorem B4980005 : Blo 2211435 4980005 := bbase (se 4 (by rfl) ⟨466875, by rfl⟩ : syracuseStep 4980005 = 933751) (by norm_num)
theorem B3320003 : Blo 2211435 3320003 := bstep (se 1 (by rfl) ⟨2490002, by rfl⟩ : syracuseStep 3320003 = 4980005) B4980005
theorem B2213335 : Blo 2211435 2213335 := bstep (se 1 (by rfl) ⟨1660001, by rfl⟩ : syracuseStep 2213335 = 3320003) B3320003
theorem B5602517 : Blo 2211435 5602517 := bbase (se 7 (by rfl) ⟨65654, by rfl⟩ : syracuseStep 5602517 = 131309) (by norm_num)
theorem B3735011 : Blo 2211435 3735011 := bstep (se 1 (by rfl) ⟨2801258, by rfl⟩ : syracuseStep 3735011 = 5602517) B5602517
theorem B2490007 : Blo 2211435 2490007 := bstep (se 1 (by rfl) ⟨1867505, by rfl⟩ : syracuseStep 2490007 = 3735011) B3735011
theorem B3320009 : Blo 2211435 3320009 := bstep (se 2 (by rfl) ⟨1245003, by rfl⟩ : syracuseStep 3320009 = 2490007) B2490007
theorem B2213339 : Blo 2211435 2213339 := bstep (se 1 (by rfl) ⟨1660004, by rfl⟩ : syracuseStep 2213339 = 3320009) B3320009
theorem B2991389 : Blo 2211435 2991389 := bbase (se 3 (by rfl) ⟨560885, by rfl⟩ : syracuseStep 2991389 = 1121771) (by norm_num)
theorem B7977037 : Blo 2211435 7977037 := bstep (se 3 (by rfl) ⟨1495694, by rfl⟩ : syracuseStep 7977037 = 2991389) B2991389
theorem B10636049 : Blo 2211435 10636049 := bstep (se 2 (by rfl) ⟨3988518, by rfl⟩ : syracuseStep 10636049 = 7977037) B7977037
theorem B7090699 : Blo 2211435 7090699 := bstep (se 1 (by rfl) ⟨5318024, by rfl⟩ : syracuseStep 7090699 = 10636049) B10636049
theorem B9454265 : Blo 2211435 9454265 := bstep (se 2 (by rfl) ⟨3545349, by rfl⟩ : syracuseStep 9454265 = 7090699) B7090699
theorem B6302843 : Blo 2211435 6302843 := bstep (se 1 (by rfl) ⟨4727132, by rfl⟩ : syracuseStep 6302843 = 9454265) B9454265
theorem B4201895 : Blo 2211435 4201895 := bstep (se 1 (by rfl) ⟨3151421, by rfl⟩ : syracuseStep 4201895 = 6302843) B6302843
theorem B11205053 : Blo 2211435 11205053 := bstep (se 3 (by rfl) ⟨2100947, by rfl⟩ : syracuseStep 11205053 = 4201895) B4201895
theorem B7470035 : Blo 2211435 7470035 := bstep (se 1 (by rfl) ⟨5602526, by rfl⟩ : syracuseStep 7470035 = 11205053) B11205053
theorem B4980023 : Blo 2211435 4980023 := bstep (se 1 (by rfl) ⟨3735017, by rfl⟩ : syracuseStep 4980023 = 7470035) B7470035
theorem B3320015 : Blo 2211435 3320015 := bstep (se 1 (by rfl) ⟨2490011, by rfl⟩ : syracuseStep 3320015 = 4980023) B4980023
theorem B2213343 : Blo 2211435 2213343 := bstep (se 1 (by rfl) ⟨1660007, by rfl⟩ : syracuseStep 2213343 = 3320015) B3320015
theorem B3320021 : Blo 2211435 3320021 := bbase (se 7 (by rfl) ⟨38906, by rfl⟩ : syracuseStep 3320021 = 77813) (by norm_num)
theorem B2213347 : Blo 2211435 2213347 := bstep (se 1 (by rfl) ⟨1660010, by rfl⟩ : syracuseStep 2213347 = 3320021) B3320021
theorem B5318045 : Blo 2211435 5318045 := bbase (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) (by norm_num)
theorem B3545363 : Blo 2211435 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B2363575 : Blo 2211435 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B3151433 : Blo 2211435 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B8403821 : Blo 2211435 8403821 := bstep (se 3 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 8403821 = 3151433) B3151433
theorem B5602547 : Blo 2211435 5602547 := bstep (se 1 (by rfl) ⟨4201910, by rfl⟩ : syracuseStep 5602547 = 8403821) B8403821
theorem B3735031 : Blo 2211435 3735031 := bstep (se 1 (by rfl) ⟨2801273, by rfl⟩ : syracuseStep 3735031 = 5602547) B5602547
theorem B4980041 : Blo 2211435 4980041 := bstep (se 2 (by rfl) ⟨1867515, by rfl⟩ : syracuseStep 4980041 = 3735031) B3735031
theorem B3320027 : Blo 2211435 3320027 := bstep (se 1 (by rfl) ⟨2490020, by rfl⟩ : syracuseStep 3320027 = 4980041) B4980041
theorem B2213351 : Blo 2211435 2213351 := bstep (se 1 (by rfl) ⟨1660013, by rfl⟩ : syracuseStep 2213351 = 3320027) B3320027
theorem B2490025 : Blo 2211435 2490025 := bbase (se 2 (by rfl) ⟨933759, by rfl⟩ : syracuseStep 2490025 = 1867519) (by norm_num)
theorem B3320033 : Blo 2211435 3320033 := bstep (se 2 (by rfl) ⟨1245012, by rfl⟩ : syracuseStep 3320033 = 2490025) B2490025
theorem B2213355 : Blo 2211435 2213355 := bstep (se 1 (by rfl) ⟨1660016, by rfl⟩ : syracuseStep 2213355 = 3320033) B3320033
theorem B3786005 : Blo 2211435 3786005 := bbase (se 6 (by rfl) ⟨88734, by rfl⟩ : syracuseStep 3786005 = 177469) (by norm_num)
theorem B2524003 : Blo 2211435 2524003 := bstep (se 1 (by rfl) ⟨1893002, by rfl⟩ : syracuseStep 2524003 = 3786005) B3786005
theorem B13461349 : Blo 2211435 13461349 := bstep (se 4 (by rfl) ⟨1262001, by rfl⟩ : syracuseStep 13461349 = 2524003) B2524003
theorem B17948465 : Blo 2211435 17948465 := bstep (se 2 (by rfl) ⟨6730674, by rfl⟩ : syracuseStep 17948465 = 13461349) B13461349
theorem B11965643 : Blo 2211435 11965643 := bstep (se 1 (by rfl) ⟨8974232, by rfl⟩ : syracuseStep 11965643 = 17948465) B17948465
theorem B7977095 : Blo 2211435 7977095 := bstep (se 1 (by rfl) ⟨5982821, by rfl⟩ : syracuseStep 7977095 = 11965643) B11965643
theorem B5318063 : Blo 2211435 5318063 := bstep (se 1 (by rfl) ⟨3988547, by rfl⟩ : syracuseStep 5318063 = 7977095) B7977095
theorem B3545375 : Blo 2211435 3545375 := bstep (se 1 (by rfl) ⟨2659031, by rfl⟩ : syracuseStep 3545375 = 5318063) B5318063
theorem B9454333 : Blo 2211435 9454333 := bstep (se 3 (by rfl) ⟨1772687, by rfl⟩ : syracuseStep 9454333 = 3545375) B3545375
theorem B12605777 : Blo 2211435 12605777 := bstep (se 2 (by rfl) ⟨4727166, by rfl⟩ : syracuseStep 12605777 = 9454333) B9454333
theorem B8403851 : Blo 2211435 8403851 := bstep (se 1 (by rfl) ⟨6302888, by rfl⟩ : syracuseStep 8403851 = 12605777) B12605777
theorem B5602567 : Blo 2211435 5602567 := bstep (se 1 (by rfl) ⟨4201925, by rfl⟩ : syracuseStep 5602567 = 8403851) B8403851
theorem B7470089 : Blo 2211435 7470089 := bstep (se 2 (by rfl) ⟨2801283, by rfl⟩ : syracuseStep 7470089 = 5602567) B5602567
theorem B4980059 : Blo 2211435 4980059 := bstep (se 1 (by rfl) ⟨3735044, by rfl⟩ : syracuseStep 4980059 = 7470089) B7470089
theorem B3320039 : Blo 2211435 3320039 := bstep (se 1 (by rfl) ⟨2490029, by rfl⟩ : syracuseStep 3320039 = 4980059) B4980059
theorem B2213359 : Blo 2211435 2213359 := bstep (se 1 (by rfl) ⟨1660019, by rfl⟩ : syracuseStep 2213359 = 3320039) B3320039
theorem B3320045 : Blo 2211435 3320045 := bbase (se 3 (by rfl) ⟨622508, by rfl⟩ : syracuseStep 3320045 = 1245017) (by norm_num)
theorem B2213363 : Blo 2211435 2213363 := bstep (se 1 (by rfl) ⟨1660022, by rfl⟩ : syracuseStep 2213363 = 3320045) B3320045
theorem B4980077 : Blo 2211435 4980077 := bbase (se 3 (by rfl) ⟨933764, by rfl⟩ : syracuseStep 4980077 = 1867529) (by norm_num)
theorem B3320051 : Blo 2211435 3320051 := bstep (se 1 (by rfl) ⟨2490038, by rfl⟩ : syracuseStep 3320051 = 4980077) B4980077
theorem B2213367 : Blo 2211435 2213367 := bstep (se 1 (by rfl) ⟨1660025, by rfl⟩ : syracuseStep 2213367 = 3320051) B3320051
theorem B4201949 : Blo 2211435 4201949 := bbase (se 3 (by rfl) ⟨787865, by rfl⟩ : syracuseStep 4201949 = 1575731) (by norm_num)
theorem B2801299 : Blo 2211435 2801299 := bstep (se 1 (by rfl) ⟨2100974, by rfl⟩ : syracuseStep 2801299 = 4201949) B4201949
theorem B3735065 : Blo 2211435 3735065 := bstep (se 2 (by rfl) ⟨1400649, by rfl⟩ : syracuseStep 3735065 = 2801299) B2801299
theorem B2490043 : Blo 2211435 2490043 := bstep (se 1 (by rfl) ⟨1867532, by rfl⟩ : syracuseStep 2490043 = 3735065) B3735065
theorem B3320057 : Blo 2211435 3320057 := bstep (se 2 (by rfl) ⟨1245021, by rfl⟩ : syracuseStep 3320057 = 2490043) B2490043
theorem B2213371 : Blo 2211435 2213371 := bstep (se 1 (by rfl) ⟨1660028, by rfl⟩ : syracuseStep 2213371 = 3320057) B3320057
theorem B4259285 : Blo 2211435 4259285 := bbase (se 7 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 4259285 = 99827) (by norm_num)
theorem B45432373 : Blo 2211435 45432373 := bstep (se 5 (by rfl) ⟨2129642, by rfl⟩ : syracuseStep 45432373 = 4259285) B4259285
theorem B60576497 : Blo 2211435 60576497 := bstep (se 2 (by rfl) ⟨22716186, by rfl⟩ : syracuseStep 60576497 = 45432373) B45432373
theorem B40384331 : Blo 2211435 40384331 := bstep (se 1 (by rfl) ⟨30288248, by rfl⟩ : syracuseStep 40384331 = 60576497) B60576497
theorem B26922887 : Blo 2211435 26922887 := bstep (se 1 (by rfl) ⟨20192165, by rfl⟩ : syracuseStep 26922887 = 40384331) B40384331
theorem B17948591 : Blo 2211435 17948591 := bstep (se 1 (by rfl) ⟨13461443, by rfl⟩ : syracuseStep 17948591 = 26922887) B26922887
theorem B11965727 : Blo 2211435 11965727 := bstep (se 1 (by rfl) ⟨8974295, by rfl⟩ : syracuseStep 11965727 = 17948591) B17948591
theorem B7977151 : Blo 2211435 7977151 := bstep (se 1 (by rfl) ⟨5982863, by rfl⟩ : syracuseStep 7977151 = 11965727) B11965727
theorem B10636201 : Blo 2211435 10636201 := bstep (se 2 (by rfl) ⟨3988575, by rfl⟩ : syracuseStep 10636201 = 7977151) B7977151
theorem B56726405 : Blo 2211435 56726405 := bstep (se 4 (by rfl) ⟨5318100, by rfl⟩ : syracuseStep 56726405 = 10636201) B10636201
theorem B37817603 : Blo 2211435 37817603 := bstep (se 1 (by rfl) ⟨28363202, by rfl⟩ : syracuseStep 37817603 = 56726405) B56726405
theorem B25211735 : Blo 2211435 25211735 := bstep (se 1 (by rfl) ⟨18908801, by rfl⟩ : syracuseStep 25211735 = 37817603) B37817603
theorem B16807823 : Blo 2211435 16807823 := bstep (se 1 (by rfl) ⟨12605867, by rfl⟩ : syracuseStep 16807823 = 25211735) B25211735
theorem B11205215 : Blo 2211435 11205215 := bstep (se 1 (by rfl) ⟨8403911, by rfl⟩ : syracuseStep 11205215 = 16807823) B16807823
theorem B7470143 : Blo 2211435 7470143 := bstep (se 1 (by rfl) ⟨5602607, by rfl⟩ : syracuseStep 7470143 = 11205215) B11205215
theorem B4980095 : Blo 2211435 4980095 := bstep (se 1 (by rfl) ⟨3735071, by rfl⟩ : syracuseStep 4980095 = 7470143) B7470143
theorem B3320063 : Blo 2211435 3320063 := bstep (se 1 (by rfl) ⟨2490047, by rfl⟩ : syracuseStep 3320063 = 4980095) B4980095
theorem B2213375 : Blo 2211435 2213375 := bstep (se 1 (by rfl) ⟨1660031, by rfl⟩ : syracuseStep 2213375 = 3320063) B3320063
theorem B3320069 : Blo 2211435 3320069 := bbase (se 4 (by rfl) ⟨311256, by rfl⟩ : syracuseStep 3320069 = 622513) (by norm_num)
theorem B2213379 : Blo 2211435 2213379 := bstep (se 1 (by rfl) ⟨1660034, by rfl⟩ : syracuseStep 2213379 = 3320069) B3320069
theorem B3735085 : Blo 2211435 3735085 := bbase (se 3 (by rfl) ⟨700328, by rfl⟩ : syracuseStep 3735085 = 1400657) (by norm_num)
theorem B4980113 : Blo 2211435 4980113 := bstep (se 2 (by rfl) ⟨1867542, by rfl⟩ : syracuseStep 4980113 = 3735085) B3735085
theorem B3320075 : Blo 2211435 3320075 := bstep (se 1 (by rfl) ⟨2490056, by rfl⟩ : syracuseStep 3320075 = 4980113) B4980113
theorem B2213383 : Blo 2211435 2213383 := bstep (se 1 (by rfl) ⟨1660037, by rfl⟩ : syracuseStep 2213383 = 3320075) B3320075
theorem B2490061 : Blo 2211435 2490061 := bbase (se 3 (by rfl) ⟨466886, by rfl⟩ : syracuseStep 2490061 = 933773) (by norm_num)
theorem B3320081 : Blo 2211435 3320081 := bstep (se 2 (by rfl) ⟨1245030, by rfl⟩ : syracuseStep 3320081 = 2490061) B2490061
theorem B2213387 : Blo 2211435 2213387 := bstep (se 1 (by rfl) ⟨1660040, by rfl⟩ : syracuseStep 2213387 = 3320081) B3320081
theorem B7470197 : Blo 2211435 7470197 := bbase (se 5 (by rfl) ⟨350165, by rfl⟩ : syracuseStep 7470197 = 700331) (by norm_num)
theorem B4980131 : Blo 2211435 4980131 := bstep (se 1 (by rfl) ⟨3735098, by rfl⟩ : syracuseStep 4980131 = 7470197) B7470197
theorem B3320087 : Blo 2211435 3320087 := bstep (se 1 (by rfl) ⟨2490065, by rfl⟩ : syracuseStep 3320087 = 4980131) B4980131
theorem B2213391 : Blo 2211435 2213391 := bstep (se 1 (by rfl) ⟨1660043, by rfl⟩ : syracuseStep 2213391 = 3320087) B3320087
theorem B3320093 : Blo 2211435 3320093 := bbase (se 3 (by rfl) ⟨622517, by rfl⟩ : syracuseStep 3320093 = 1245035) (by norm_num)
theorem B2213395 : Blo 2211435 2213395 := bstep (se 1 (by rfl) ⟨1660046, by rfl⟩ : syracuseStep 2213395 = 3320093) B3320093
theorem B4980149 : Blo 2211435 4980149 := bbase (se 5 (by rfl) ⟨233444, by rfl⟩ : syracuseStep 4980149 = 466889) (by norm_num)
theorem B3320099 : Blo 2211435 3320099 := bstep (se 1 (by rfl) ⟨2490074, by rfl⟩ : syracuseStep 3320099 = 4980149) B4980149
theorem B2213399 : Blo 2211435 2213399 := bstep (se 1 (by rfl) ⟨1660049, by rfl⟩ : syracuseStep 2213399 = 3320099) B3320099
theorem B4727261 : Blo 2211435 4727261 := bbase (se 3 (by rfl) ⟨886361, by rfl⟩ : syracuseStep 4727261 = 1772723) (by norm_num)
theorem B12606029 : Blo 2211435 12606029 := bstep (se 3 (by rfl) ⟨2363630, by rfl⟩ : syracuseStep 12606029 = 4727261) B4727261
theorem B8404019 : Blo 2211435 8404019 := bstep (se 1 (by rfl) ⟨6303014, by rfl⟩ : syracuseStep 8404019 = 12606029) B12606029
theorem B5602679 : Blo 2211435 5602679 := bstep (se 1 (by rfl) ⟨4202009, by rfl⟩ : syracuseStep 5602679 = 8404019) B8404019
theorem B3735119 : Blo 2211435 3735119 := bstep (se 1 (by rfl) ⟨2801339, by rfl⟩ : syracuseStep 3735119 = 5602679) B5602679
theorem B2490079 : Blo 2211435 2490079 := bstep (se 1 (by rfl) ⟨1867559, by rfl⟩ : syracuseStep 2490079 = 3735119) B3735119
theorem B3320105 : Blo 2211435 3320105 := bstep (se 2 (by rfl) ⟨1245039, by rfl⟩ : syracuseStep 3320105 = 2490079) B2490079
theorem B2213403 : Blo 2211435 2213403 := bstep (se 1 (by rfl) ⟨1660052, by rfl⟩ : syracuseStep 2213403 = 3320105) B3320105
theorem B4727269 : Blo 2211435 4727269 := bbase (se 4 (by rfl) ⟨443181, by rfl⟩ : syracuseStep 4727269 = 886363) (by norm_num)
theorem B6303025 : Blo 2211435 6303025 := bstep (se 2 (by rfl) ⟨2363634, by rfl⟩ : syracuseStep 6303025 = 4727269) B4727269
theorem B8404033 : Blo 2211435 8404033 := bstep (se 2 (by rfl) ⟨3151512, by rfl⟩ : syracuseStep 8404033 = 6303025) B6303025
theorem B11205377 : Blo 2211435 11205377 := bstep (se 2 (by rfl) ⟨4202016, by rfl⟩ : syracuseStep 11205377 = 8404033) B8404033
theorem B7470251 : Blo 2211435 7470251 := bstep (se 1 (by rfl) ⟨5602688, by rfl⟩ : syracuseStep 7470251 = 11205377) B11205377
theorem B4980167 : Blo 2211435 4980167 := bstep (se 1 (by rfl) ⟨3735125, by rfl⟩ : syracuseStep 4980167 = 7470251) B7470251
theorem B3320111 : Blo 2211435 3320111 := bstep (se 1 (by rfl) ⟨2490083, by rfl⟩ : syracuseStep 3320111 = 4980167) B4980167
theorem B2213407 : Blo 2211435 2213407 := bstep (se 1 (by rfl) ⟨1660055, by rfl⟩ : syracuseStep 2213407 = 3320111) B3320111
theorem B3320117 : Blo 2211435 3320117 := bbase (se 5 (by rfl) ⟨155630, by rfl⟩ : syracuseStep 3320117 = 311261) (by norm_num)
theorem B2213411 : Blo 2211435 2213411 := bstep (se 1 (by rfl) ⟨1660058, by rfl⟩ : syracuseStep 2213411 = 3320117) B3320117
theorem B5602709 : Blo 2211435 5602709 := bbase (se 6 (by rfl) ⟨131313, by rfl⟩ : syracuseStep 5602709 = 262627) (by norm_num)
theorem B3735139 : Blo 2211435 3735139 := bstep (se 1 (by rfl) ⟨2801354, by rfl⟩ : syracuseStep 3735139 = 5602709) B5602709
theorem B4980185 : Blo 2211435 4980185 := bstep (se 2 (by rfl) ⟨1867569, by rfl⟩ : syracuseStep 4980185 = 3735139) B3735139
theorem B3320123 : Blo 2211435 3320123 := bstep (se 1 (by rfl) ⟨2490092, by rfl⟩ : syracuseStep 3320123 = 4980185) B4980185
theorem B2213415 : Blo 2211435 2213415 := bstep (se 1 (by rfl) ⟨1660061, by rfl⟩ : syracuseStep 2213415 = 3320123) B3320123
theorem B2490097 : Blo 2211435 2490097 := bbase (se 2 (by rfl) ⟨933786, by rfl⟩ : syracuseStep 2490097 = 1867573) (by norm_num)
theorem B3320129 : Blo 2211435 3320129 := bstep (se 2 (by rfl) ⟨1245048, by rfl⟩ : syracuseStep 3320129 = 2490097) B2490097
theorem B2213419 : Blo 2211435 2213419 := bstep (se 1 (by rfl) ⟨1660064, by rfl⟩ : syracuseStep 2213419 = 3320129) B3320129
theorem B5679173 : Blo 2211435 5679173 := bbase (se 4 (by rfl) ⟨532422, by rfl⟩ : syracuseStep 5679173 = 1064845) (by norm_num)
theorem B3786115 : Blo 2211435 3786115 := bstep (se 1 (by rfl) ⟨2839586, by rfl⟩ : syracuseStep 3786115 = 5679173) B5679173
theorem B5048153 : Blo 2211435 5048153 := bstep (se 2 (by rfl) ⟨1893057, by rfl⟩ : syracuseStep 5048153 = 3786115) B3786115
theorem B3365435 : Blo 2211435 3365435 := bstep (se 1 (by rfl) ⟨2524076, by rfl⟩ : syracuseStep 3365435 = 5048153) B5048153
theorem B2243623 : Blo 2211435 2243623 := bstep (se 1 (by rfl) ⟨1682717, by rfl⟩ : syracuseStep 2243623 = 3365435) B3365435
theorem B2991497 : Blo 2211435 2991497 := bstep (se 2 (by rfl) ⟨1121811, by rfl⟩ : syracuseStep 2991497 = 2243623) B2243623
theorem B31909301 : Blo 2211435 31909301 := bstep (se 5 (by rfl) ⟨1495748, by rfl⟩ : syracuseStep 31909301 = 2991497) B2991497
theorem B21272867 : Blo 2211435 21272867 := bstep (se 1 (by rfl) ⟨15954650, by rfl⟩ : syracuseStep 21272867 = 31909301) B31909301
theorem B14181911 : Blo 2211435 14181911 := bstep (se 1 (by rfl) ⟨10636433, by rfl⟩ : syracuseStep 14181911 = 21272867) B21272867
theorem B9454607 : Blo 2211435 9454607 := bstep (se 1 (by rfl) ⟨7090955, by rfl⟩ : syracuseStep 9454607 = 14181911) B14181911
theorem B6303071 : Blo 2211435 6303071 := bstep (se 1 (by rfl) ⟨4727303, by rfl⟩ : syracuseStep 6303071 = 9454607) B9454607
theorem B4202047 : Blo 2211435 4202047 := bstep (se 1 (by rfl) ⟨3151535, by rfl⟩ : syracuseStep 4202047 = 6303071) B6303071
theorem B5602729 : Blo 2211435 5602729 := bstep (se 2 (by rfl) ⟨2101023, by rfl⟩ : syracuseStep 5602729 = 4202047) B4202047
theorem B7470305 : Blo 2211435 7470305 := bstep (se 2 (by rfl) ⟨2801364, by rfl⟩ : syracuseStep 7470305 = 5602729) B5602729
theorem B4980203 : Blo 2211435 4980203 := bstep (se 1 (by rfl) ⟨3735152, by rfl⟩ : syracuseStep 4980203 = 7470305) B7470305
theorem B3320135 : Blo 2211435 3320135 := bstep (se 1 (by rfl) ⟨2490101, by rfl⟩ : syracuseStep 3320135 = 4980203) B4980203
theorem B2213423 : Blo 2211435 2213423 := bstep (se 1 (by rfl) ⟨1660067, by rfl⟩ : syracuseStep 2213423 = 3320135) B3320135
theorem B3320141 : Blo 2211435 3320141 := bbase (se 3 (by rfl) ⟨622526, by rfl⟩ : syracuseStep 3320141 = 1245053) (by norm_num)
theorem B2213427 : Blo 2211435 2213427 := bstep (se 1 (by rfl) ⟨1660070, by rfl⟩ : syracuseStep 2213427 = 3320141) B3320141
theorem B4980221 : Blo 2211435 4980221 := bbase (se 3 (by rfl) ⟨933791, by rfl⟩ : syracuseStep 4980221 = 1867583) (by norm_num)
theorem B3320147 : Blo 2211435 3320147 := bstep (se 1 (by rfl) ⟨2490110, by rfl⟩ : syracuseStep 3320147 = 4980221) B4980221
theorem B2213431 : Blo 2211435 2213431 := bstep (se 1 (by rfl) ⟨1660073, by rfl⟩ : syracuseStep 2213431 = 3320147) B3320147
theorem B3735173 : Blo 2211435 3735173 := bbase (se 4 (by rfl) ⟨350172, by rfl⟩ : syracuseStep 3735173 = 700345) (by norm_num)
theorem B2490115 : Blo 2211435 2490115 := bstep (se 1 (by rfl) ⟨1867586, by rfl⟩ : syracuseStep 2490115 = 3735173) B3735173
theorem B3320153 : Blo 2211435 3320153 := bstep (se 2 (by rfl) ⟨1245057, by rfl⟩ : syracuseStep 3320153 = 2490115) B2490115
theorem B2213435 : Blo 2211435 2213435 := bstep (se 1 (by rfl) ⟨1660076, by rfl⟩ : syracuseStep 2213435 = 3320153) B3320153
theorem C0 (j : ℕ) (h1 : 552858 ≤ j) (h2 : j ≤ 553358) : Blo 2211435 (4 * j + 3) := by
  interval_cases j
  · exact B2211435
  · exact B2211439
  · exact B2211443
  · exact B2211447
  · exact B2211451
  · exact B2211455
  · exact B2211459
  · exact B2211463
  · exact B2211467
  · exact B2211471
  · exact B2211475
  · exact B2211479
  · exact B2211483
  · exact B2211487
  · exact B2211491
  · exact B2211495
  · exact B2211499
  · exact B2211503
  · exact B2211507
  · exact B2211511
  · exact B2211515
  · exact B2211519
  · exact B2211523
  · exact B2211527
  · exact B2211531
  · exact B2211535
  · exact B2211539
  · exact B2211543
  · exact B2211547
  · exact B2211551
  · exact B2211555
  · exact B2211559
  · exact B2211563
  · exact B2211567
  · exact B2211571
  · exact B2211575
  · exact B2211579
  · exact B2211583
  · exact B2211587
  · exact B2211591
  · exact B2211595
  · exact B2211599
  · exact B2211603
  · exact B2211607
  · exact B2211611
  · exact B2211615
  · exact B2211619
  · exact B2211623
  · exact B2211627
  · exact B2211631
  · exact B2211635
  · exact B2211639
  · exact B2211643
  · exact B2211647
  · exact B2211651
  · exact B2211655
  · exact B2211659
  · exact B2211663
  · exact B2211667
  · exact B2211671
  · exact B2211675
  · exact B2211679
  · exact B2211683
  · exact B2211687
  · exact B2211691
  · exact B2211695
  · exact B2211699
  · exact B2211703
  · exact B2211707
  · exact B2211711
  · exact B2211715
  · exact B2211719
  · exact B2211723
  · exact B2211727
  · exact B2211731
  · exact B2211735
  · exact B2211739
  · exact B2211743
  · exact B2211747
  · exact B2211751
  · exact B2211755
  · exact B2211759
  · exact B2211763
  · exact B2211767
  · exact B2211771
  · exact B2211775
  · exact B2211779
  · exact B2211783
  · exact B2211787
  · exact B2211791
  · exact B2211795
  · exact B2211799
  · exact B2211803
  · exact B2211807
  · exact B2211811
  · exact B2211815
  · exact B2211819
  · exact B2211823
  · exact B2211827
  · exact B2211831
  · exact B2211835
  · exact B2211839
  · exact B2211843
  · exact B2211847
  · exact B2211851
  · exact B2211855
  · exact B2211859
  · exact B2211863
  · exact B2211867
  · exact B2211871
  · exact B2211875
  · exact B2211879
  · exact B2211883
  · exact B2211887
  · exact B2211891
  · exact B2211895
  · exact B2211899
  · exact B2211903
  · exact B2211907
  · exact B2211911
  · exact B2211915
  · exact B2211919
  · exact B2211923
  · exact B2211927
  · exact B2211931
  · exact B2211935
  · exact B2211939
  · exact B2211943
  · exact B2211947
  · exact B2211951
  · exact B2211955
  · exact B2211959
  · exact B2211963
  · exact B2211967
  · exact B2211971
  · exact B2211975
  · exact B2211979
  · exact B2211983
  · exact B2211987
  · exact B2211991
  · exact B2211995
  · exact B2211999
  · exact B2212003
  · exact B2212007
  · exact B2212011
  · exact B2212015
  · exact B2212019
  · exact B2212023
  · exact B2212027
  · exact B2212031
  · exact B2212035
  · exact B2212039
  · exact B2212043
  · exact B2212047
  · exact B2212051
  · exact B2212055
  · exact B2212059
  · exact B2212063
  · exact B2212067
  · exact B2212071
  · exact B2212075
  · exact B2212079
  · exact B2212083
  · exact B2212087
  · exact B2212091
  · exact B2212095
  · exact B2212099
  · exact B2212103
  · exact B2212107
  · exact B2212111
  · exact B2212115
  · exact B2212119
  · exact B2212123
  · exact B2212127
  · exact B2212131
  · exact B2212135
  · exact B2212139
  · exact B2212143
  · exact B2212147
  · exact B2212151
  · exact B2212155
  · exact B2212159
  · exact B2212163
  · exact B2212167
  · exact B2212171
  · exact B2212175
  · exact B2212179
  · exact B2212183
  · exact B2212187
  · exact B2212191
  · exact B2212195
  · exact B2212199
  · exact B2212203
  · exact B2212207
  · exact B2212211
  · exact B2212215
  · exact B2212219
  · exact B2212223
  · exact B2212227
  · exact B2212231
  · exact B2212235
  · exact B2212239
  · exact B2212243
  · exact B2212247
  · exact B2212251
  · exact B2212255
  · exact B2212259
  · exact B2212263
  · exact B2212267
  · exact B2212271
  · exact B2212275
  · exact B2212279
  · exact B2212283
  · exact B2212287
  · exact B2212291
  · exact B2212295
  · exact B2212299
  · exact B2212303
  · exact B2212307
  · exact B2212311
  · exact B2212315
  · exact B2212319
  · exact B2212323
  · exact B2212327
  · exact B2212331
  · exact B2212335
  · exact B2212339
  · exact B2212343
  · exact B2212347
  · exact B2212351
  · exact B2212355
  · exact B2212359
  · exact B2212363
  · exact B2212367
  · exact B2212371
  · exact B2212375
  · exact B2212379
  · exact B2212383
  · exact B2212387
  · exact B2212391
  · exact B2212395
  · exact B2212399
  · exact B2212403
  · exact B2212407
  · exact B2212411
  · exact B2212415
  · exact B2212419
  · exact B2212423
  · exact B2212427
  · exact B2212431
  · exact B2212435
  · exact B2212439
  · exact B2212443
  · exact B2212447
  · exact B2212451
  · exact B2212455
  · exact B2212459
  · exact B2212463
  · exact B2212467
  · exact B2212471
  · exact B2212475
  · exact B2212479
  · exact B2212483
  · exact B2212487
  · exact B2212491
  · exact B2212495
  · exact B2212499
  · exact B2212503
  · exact B2212507
  · exact B2212511
  · exact B2212515
  · exact B2212519
  · exact B2212523
  · exact B2212527
  · exact B2212531
  · exact B2212535
  · exact B2212539
  · exact B2212543
  · exact B2212547
  · exact B2212551
  · exact B2212555
  · exact B2212559
  · exact B2212563
  · exact B2212567
  · exact B2212571
  · exact B2212575
  · exact B2212579
  · exact B2212583
  · exact B2212587
  · exact B2212591
  · exact B2212595
  · exact B2212599
  · exact B2212603
  · exact B2212607
  · exact B2212611
  · exact B2212615
  · exact B2212619
  · exact B2212623
  · exact B2212627
  · exact B2212631
  · exact B2212635
  · exact B2212639
  · exact B2212643
  · exact B2212647
  · exact B2212651
  · exact B2212655
  · exact B2212659
  · exact B2212663
  · exact B2212667
  · exact B2212671
  · exact B2212675
  · exact B2212679
  · exact B2212683
  · exact B2212687
  · exact B2212691
  · exact B2212695
  · exact B2212699
  · exact B2212703
  · exact B2212707
  · exact B2212711
  · exact B2212715
  · exact B2212719
  · exact B2212723
  · exact B2212727
  · exact B2212731
  · exact B2212735
  · exact B2212739
  · exact B2212743
  · exact B2212747
  · exact B2212751
  · exact B2212755
  · exact B2212759
  · exact B2212763
  · exact B2212767
  · exact B2212771
  · exact B2212775
  · exact B2212779
  · exact B2212783
  · exact B2212787
  · exact B2212791
  · exact B2212795
  · exact B2212799
  · exact B2212803
  · exact B2212807
  · exact B2212811
  · exact B2212815
  · exact B2212819
  · exact B2212823
  · exact B2212827
  · exact B2212831
  · exact B2212835
  · exact B2212839
  · exact B2212843
  · exact B2212847
  · exact B2212851
  · exact B2212855
  · exact B2212859
  · exact B2212863
  · exact B2212867
  · exact B2212871
  · exact B2212875
  · exact B2212879
  · exact B2212883
  · exact B2212887
  · exact B2212891
  · exact B2212895
  · exact B2212899
  · exact B2212903
  · exact B2212907
  · exact B2212911
  · exact B2212915
  · exact B2212919
  · exact B2212923
  · exact B2212927
  · exact B2212931
  · exact B2212935
  · exact B2212939
  · exact B2212943
  · exact B2212947
  · exact B2212951
  · exact B2212955
  · exact B2212959
  · exact B2212963
  · exact B2212967
  · exact B2212971
  · exact B2212975
  · exact B2212979
  · exact B2212983
  · exact B2212987
  · exact B2212991
  · exact B2212995
  · exact B2212999
  · exact B2213003
  · exact B2213007
  · exact B2213011
  · exact B2213015
  · exact B2213019
  · exact B2213023
  · exact B2213027
  · exact B2213031
  · exact B2213035
  · exact B2213039
  · exact B2213043
  · exact B2213047
  · exact B2213051
  · exact B2213055
  · exact B2213059
  · exact B2213063
  · exact B2213067
  · exact B2213071
  · exact B2213075
  · exact B2213079
  · exact B2213083
  · exact B2213087
  · exact B2213091
  · exact B2213095
  · exact B2213099
  · exact B2213103
  · exact B2213107
  · exact B2213111
  · exact B2213115
  · exact B2213119
  · exact B2213123
  · exact B2213127
  · exact B2213131
  · exact B2213135
  · exact B2213139
  · exact B2213143
  · exact B2213147
  · exact B2213151
  · exact B2213155
  · exact B2213159
  · exact B2213163
  · exact B2213167
  · exact B2213171
  · exact B2213175
  · exact B2213179
  · exact B2213183
  · exact B2213187
  · exact B2213191
  · exact B2213195
  · exact B2213199
  · exact B2213203
  · exact B2213207
  · exact B2213211
  · exact B2213215
  · exact B2213219
  · exact B2213223
  · exact B2213227
  · exact B2213231
  · exact B2213235
  · exact B2213239
  · exact B2213243
  · exact B2213247
  · exact B2213251
  · exact B2213255
  · exact B2213259
  · exact B2213263
  · exact B2213267
  · exact B2213271
  · exact B2213275
  · exact B2213279
  · exact B2213283
  · exact B2213287
  · exact B2213291
  · exact B2213295
  · exact B2213299
  · exact B2213303
  · exact B2213307
  · exact B2213311
  · exact B2213315
  · exact B2213319
  · exact B2213323
  · exact B2213327
  · exact B2213331
  · exact B2213335
  · exact B2213339
  · exact B2213343
  · exact B2213347
  · exact B2213351
  · exact B2213355
  · exact B2213359
  · exact B2213363
  · exact B2213367
  · exact B2213371
  · exact B2213375
  · exact B2213379
  · exact B2213383
  · exact B2213387
  · exact B2213391
  · exact B2213395
  · exact B2213399
  · exact B2213403
  · exact B2213407
  · exact B2213411
  · exact B2213415
  · exact B2213419
  · exact B2213423
  · exact B2213427
  · exact B2213431
  · exact B2213435
theorem solution (m : ℕ) (hlo : 2211435 ≤ m) (hhi : m ≤ 2213435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 552858 ≤ j := by omega
    have hj2 : j ≤ 553358 := by omega
    have hb : Blo 2211435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
