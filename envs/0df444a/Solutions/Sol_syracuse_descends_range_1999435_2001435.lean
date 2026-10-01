-- Prove2me | solution 1 for syracuse_descends_range_1999435_2001435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:32.198327+00:00
-- url     : https://prove2.me/submissions/c0ccfa16-bcb6-442c-9a7c-a68ef05ce35f

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

theorem B2249365 : Blo 1999435 2249365 := bbase (se 6 (by rfl) ⟨52719, by rfl⟩ : syracuseStep 2249365 = 105439) (by norm_num)
theorem B2999153 : Blo 1999435 2999153 := bstep (se 2 (by rfl) ⟨1124682, by rfl⟩ : syracuseStep 2999153 = 2249365) B2249365
theorem B1999435 : Blo 1999435 1999435 := bstep (se 1 (by rfl) ⟨1499576, by rfl⟩ : syracuseStep 1999435 = 2999153) B2999153
theorem B2530541 : Blo 1999435 2530541 := bbase (se 3 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 2530541 = 948953) (by norm_num)
theorem B6748109 : Blo 1999435 6748109 := bstep (se 3 (by rfl) ⟨1265270, by rfl⟩ : syracuseStep 6748109 = 2530541) B2530541
theorem B4498739 : Blo 1999435 4498739 := bstep (se 1 (by rfl) ⟨3374054, by rfl⟩ : syracuseStep 4498739 = 6748109) B6748109
theorem B2999159 : Blo 1999435 2999159 := bstep (se 1 (by rfl) ⟨2249369, by rfl⟩ : syracuseStep 2999159 = 4498739) B4498739
theorem B1999439 : Blo 1999435 1999439 := bstep (se 1 (by rfl) ⟨1499579, by rfl⟩ : syracuseStep 1999439 = 2999159) B2999159
theorem B2999165 : Blo 1999435 2999165 := bbase (se 3 (by rfl) ⟨562343, by rfl⟩ : syracuseStep 2999165 = 1124687) (by norm_num)
theorem B1999443 : Blo 1999435 1999443 := bstep (se 1 (by rfl) ⟨1499582, by rfl⟩ : syracuseStep 1999443 = 2999165) B2999165
theorem B4498757 : Blo 1999435 4498757 := bbase (se 4 (by rfl) ⟨421758, by rfl⟩ : syracuseStep 4498757 = 843517) (by norm_num)
theorem B2999171 : Blo 1999435 2999171 := bstep (se 1 (by rfl) ⟨2249378, by rfl⟩ : syracuseStep 2999171 = 4498757) B4498757
theorem B1999447 : Blo 1999435 1999447 := bstep (se 1 (by rfl) ⟨1499585, by rfl⟩ : syracuseStep 1999447 = 2999171) B2999171
theorem B6080197 : Blo 1999435 6080197 := bbase (se 4 (by rfl) ⟨570018, by rfl⟩ : syracuseStep 6080197 = 1140037) (by norm_num)
theorem B8106929 : Blo 1999435 8106929 := bstep (se 2 (by rfl) ⟨3040098, by rfl⟩ : syracuseStep 8106929 = 6080197) B6080197
theorem B5404619 : Blo 1999435 5404619 := bstep (se 1 (by rfl) ⟨4053464, by rfl⟩ : syracuseStep 5404619 = 8106929) B8106929
theorem B3603079 : Blo 1999435 3603079 := bstep (se 1 (by rfl) ⟨2702309, by rfl⟩ : syracuseStep 3603079 = 5404619) B5404619
theorem B4804105 : Blo 1999435 4804105 := bstep (se 2 (by rfl) ⟨1801539, by rfl⟩ : syracuseStep 4804105 = 3603079) B3603079
theorem B6405473 : Blo 1999435 6405473 := bstep (se 2 (by rfl) ⟨2402052, by rfl⟩ : syracuseStep 6405473 = 4804105) B4804105
theorem B4270315 : Blo 1999435 4270315 := bstep (se 1 (by rfl) ⟨3202736, by rfl⟩ : syracuseStep 4270315 = 6405473) B6405473
theorem B5693753 : Blo 1999435 5693753 := bstep (se 2 (by rfl) ⟨2135157, by rfl⟩ : syracuseStep 5693753 = 4270315) B4270315
theorem B3795835 : Blo 1999435 3795835 := bstep (se 1 (by rfl) ⟨2846876, by rfl⟩ : syracuseStep 3795835 = 5693753) B5693753
theorem B5061113 : Blo 1999435 5061113 := bstep (se 2 (by rfl) ⟨1897917, by rfl⟩ : syracuseStep 5061113 = 3795835) B3795835
theorem B3374075 : Blo 1999435 3374075 := bstep (se 1 (by rfl) ⟨2530556, by rfl⟩ : syracuseStep 3374075 = 5061113) B5061113
theorem B2249383 : Blo 1999435 2249383 := bstep (se 1 (by rfl) ⟨1687037, by rfl⟩ : syracuseStep 2249383 = 3374075) B3374075
theorem B2999177 : Blo 1999435 2999177 := bstep (se 2 (by rfl) ⟨1124691, by rfl⟩ : syracuseStep 2999177 = 2249383) B2249383
theorem B1999451 : Blo 1999435 1999451 := bstep (se 1 (by rfl) ⟨1499588, by rfl⟩ : syracuseStep 1999451 = 2999177) B2999177
theorem B10122245 : Blo 1999435 10122245 := bbase (se 4 (by rfl) ⟨948960, by rfl⟩ : syracuseStep 10122245 = 1897921) (by norm_num)
theorem B6748163 : Blo 1999435 6748163 := bstep (se 1 (by rfl) ⟨5061122, by rfl⟩ : syracuseStep 6748163 = 10122245) B10122245
theorem B4498775 : Blo 1999435 4498775 := bstep (se 1 (by rfl) ⟨3374081, by rfl⟩ : syracuseStep 4498775 = 6748163) B6748163
theorem B2999183 : Blo 1999435 2999183 := bstep (se 1 (by rfl) ⟨2249387, by rfl⟩ : syracuseStep 2999183 = 4498775) B4498775
theorem B1999455 : Blo 1999435 1999455 := bstep (se 1 (by rfl) ⟨1499591, by rfl⟩ : syracuseStep 1999455 = 2999183) B2999183
theorem B2999189 : Blo 1999435 2999189 := bbase (se 6 (by rfl) ⟨70293, by rfl⟩ : syracuseStep 2999189 = 140587) (by norm_num)
theorem B1999459 : Blo 1999435 1999459 := bstep (se 1 (by rfl) ⟨1499594, by rfl⟩ : syracuseStep 1999459 = 2999189) B2999189
theorem B11387573 : Blo 1999435 11387573 := bbase (se 5 (by rfl) ⟨533792, by rfl⟩ : syracuseStep 11387573 = 1067585) (by norm_num)
theorem B7591715 : Blo 1999435 7591715 := bstep (se 1 (by rfl) ⟨5693786, by rfl⟩ : syracuseStep 7591715 = 11387573) B11387573
theorem B5061143 : Blo 1999435 5061143 := bstep (se 1 (by rfl) ⟨3795857, by rfl⟩ : syracuseStep 5061143 = 7591715) B7591715
theorem B3374095 : Blo 1999435 3374095 := bstep (se 1 (by rfl) ⟨2530571, by rfl⟩ : syracuseStep 3374095 = 5061143) B5061143
theorem B4498793 : Blo 1999435 4498793 := bstep (se 2 (by rfl) ⟨1687047, by rfl⟩ : syracuseStep 4498793 = 3374095) B3374095
theorem B2999195 : Blo 1999435 2999195 := bstep (se 1 (by rfl) ⟨2249396, by rfl⟩ : syracuseStep 2999195 = 4498793) B4498793
theorem B1999463 : Blo 1999435 1999463 := bstep (se 1 (by rfl) ⟨1499597, by rfl⟩ : syracuseStep 1999463 = 2999195) B2999195
theorem B2249401 : Blo 1999435 2249401 := bbase (se 2 (by rfl) ⟨843525, by rfl⟩ : syracuseStep 2249401 = 1687051) (by norm_num)
theorem B2999201 : Blo 1999435 2999201 := bstep (se 2 (by rfl) ⟨1124700, by rfl⟩ : syracuseStep 2999201 = 2249401) B2249401
theorem B1999467 : Blo 1999435 1999467 := bstep (se 1 (by rfl) ⟨1499600, by rfl⟩ : syracuseStep 1999467 = 2999201) B2999201
theorem B4270357 : Blo 1999435 4270357 := bbase (se 6 (by rfl) ⟨100086, by rfl⟩ : syracuseStep 4270357 = 200173) (by norm_num)
theorem B5693809 : Blo 1999435 5693809 := bstep (se 2 (by rfl) ⟨2135178, by rfl⟩ : syracuseStep 5693809 = 4270357) B4270357
theorem B7591745 : Blo 1999435 7591745 := bstep (se 2 (by rfl) ⟨2846904, by rfl⟩ : syracuseStep 7591745 = 5693809) B5693809
theorem B5061163 : Blo 1999435 5061163 := bstep (se 1 (by rfl) ⟨3795872, by rfl⟩ : syracuseStep 5061163 = 7591745) B7591745
theorem B6748217 : Blo 1999435 6748217 := bstep (se 2 (by rfl) ⟨2530581, by rfl⟩ : syracuseStep 6748217 = 5061163) B5061163
theorem B4498811 : Blo 1999435 4498811 := bstep (se 1 (by rfl) ⟨3374108, by rfl⟩ : syracuseStep 4498811 = 6748217) B6748217
theorem B2999207 : Blo 1999435 2999207 := bstep (se 1 (by rfl) ⟨2249405, by rfl⟩ : syracuseStep 2999207 = 4498811) B4498811
theorem B1999471 : Blo 1999435 1999471 := bstep (se 1 (by rfl) ⟨1499603, by rfl⟩ : syracuseStep 1999471 = 2999207) B2999207
theorem B2999213 : Blo 1999435 2999213 := bbase (se 3 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 2999213 = 1124705) (by norm_num)
theorem B1999475 : Blo 1999435 1999475 := bstep (se 1 (by rfl) ⟨1499606, by rfl⟩ : syracuseStep 1999475 = 2999213) B2999213
theorem B4498829 : Blo 1999435 4498829 := bbase (se 3 (by rfl) ⟨843530, by rfl⟩ : syracuseStep 4498829 = 1687061) (by norm_num)
theorem B2999219 : Blo 1999435 2999219 := bstep (se 1 (by rfl) ⟨2249414, by rfl⟩ : syracuseStep 2999219 = 4498829) B4498829
theorem B1999479 : Blo 1999435 1999479 := bstep (se 1 (by rfl) ⟨1499609, by rfl⟩ : syracuseStep 1999479 = 2999219) B2999219
theorem B2530597 : Blo 1999435 2530597 := bbase (se 4 (by rfl) ⟨237243, by rfl⟩ : syracuseStep 2530597 = 474487) (by norm_num)
theorem B3374129 : Blo 1999435 3374129 := bstep (se 2 (by rfl) ⟨1265298, by rfl⟩ : syracuseStep 3374129 = 2530597) B2530597
theorem B2249419 : Blo 1999435 2249419 := bstep (se 1 (by rfl) ⟨1687064, by rfl⟩ : syracuseStep 2249419 = 3374129) B3374129
theorem B2999225 : Blo 1999435 2999225 := bstep (se 2 (by rfl) ⟨1124709, by rfl⟩ : syracuseStep 2999225 = 2249419) B2249419
theorem B1999483 : Blo 1999435 1999483 := bstep (se 1 (by rfl) ⟨1499612, by rfl⟩ : syracuseStep 1999483 = 2999225) B2999225
theorem B4164901 : Blo 1999435 4164901 := bbase (se 4 (by rfl) ⟨390459, by rfl⟩ : syracuseStep 4164901 = 780919) (by norm_num)
theorem B22212805 : Blo 1999435 22212805 := bstep (se 4 (by rfl) ⟨2082450, by rfl⟩ : syracuseStep 22212805 = 4164901) B4164901
theorem B29617073 : Blo 1999435 29617073 := bstep (se 2 (by rfl) ⟨11106402, by rfl⟩ : syracuseStep 29617073 = 22212805) B22212805
theorem B19744715 : Blo 1999435 19744715 := bstep (se 1 (by rfl) ⟨14808536, by rfl⟩ : syracuseStep 19744715 = 29617073) B29617073
theorem B13163143 : Blo 1999435 13163143 := bstep (se 1 (by rfl) ⟨9872357, by rfl⟩ : syracuseStep 13163143 = 19744715) B19744715
theorem B17550857 : Blo 1999435 17550857 := bstep (se 2 (by rfl) ⟨6581571, by rfl⟩ : syracuseStep 17550857 = 13163143) B13163143
theorem B11700571 : Blo 1999435 11700571 := bstep (se 1 (by rfl) ⟨8775428, by rfl⟩ : syracuseStep 11700571 = 17550857) B17550857
theorem B15600761 : Blo 1999435 15600761 := bstep (se 2 (by rfl) ⟨5850285, by rfl⟩ : syracuseStep 15600761 = 11700571) B11700571
theorem B10400507 : Blo 1999435 10400507 := bstep (se 1 (by rfl) ⟨7800380, by rfl⟩ : syracuseStep 10400507 = 15600761) B15600761
theorem B6933671 : Blo 1999435 6933671 := bstep (se 1 (by rfl) ⟨5200253, by rfl⟩ : syracuseStep 6933671 = 10400507) B10400507
theorem B4622447 : Blo 1999435 4622447 := bstep (se 1 (by rfl) ⟨3466835, by rfl⟩ : syracuseStep 4622447 = 6933671) B6933671
theorem B12326525 : Blo 1999435 12326525 := bstep (se 3 (by rfl) ⟨2311223, by rfl⟩ : syracuseStep 12326525 = 4622447) B4622447
theorem B8217683 : Blo 1999435 8217683 := bstep (se 1 (by rfl) ⟨6163262, by rfl⟩ : syracuseStep 8217683 = 12326525) B12326525
theorem B5478455 : Blo 1999435 5478455 := bstep (se 1 (by rfl) ⟨4108841, by rfl⟩ : syracuseStep 5478455 = 8217683) B8217683
theorem B3652303 : Blo 1999435 3652303 := bstep (se 1 (by rfl) ⟨2739227, by rfl⟩ : syracuseStep 3652303 = 5478455) B5478455
theorem B4869737 : Blo 1999435 4869737 := bstep (se 2 (by rfl) ⟨1826151, by rfl⟩ : syracuseStep 4869737 = 3652303) B3652303
theorem B3246491 : Blo 1999435 3246491 := bstep (se 1 (by rfl) ⟨2434868, by rfl⟩ : syracuseStep 3246491 = 4869737) B4869737
theorem B2164327 : Blo 1999435 2164327 := bstep (se 1 (by rfl) ⟨1623245, by rfl⟩ : syracuseStep 2164327 = 3246491) B3246491
theorem B11543077 : Blo 1999435 11543077 := bstep (se 4 (by rfl) ⟨1082163, by rfl⟩ : syracuseStep 11543077 = 2164327) B2164327
theorem B15390769 : Blo 1999435 15390769 := bstep (se 2 (by rfl) ⟨5771538, by rfl⟩ : syracuseStep 15390769 = 11543077) B11543077
theorem B20521025 : Blo 1999435 20521025 := bstep (se 2 (by rfl) ⟨7695384, by rfl⟩ : syracuseStep 20521025 = 15390769) B15390769
theorem B13680683 : Blo 1999435 13680683 := bstep (se 1 (by rfl) ⟨10260512, by rfl⟩ : syracuseStep 13680683 = 20521025) B20521025
theorem B9120455 : Blo 1999435 9120455 := bstep (se 1 (by rfl) ⟨6840341, by rfl⟩ : syracuseStep 9120455 = 13680683) B13680683
theorem B6080303 : Blo 1999435 6080303 := bstep (se 1 (by rfl) ⟨4560227, by rfl⟩ : syracuseStep 6080303 = 9120455) B9120455
theorem B16214141 : Blo 1999435 16214141 := bstep (se 3 (by rfl) ⟨3040151, by rfl⟩ : syracuseStep 16214141 = 6080303) B6080303
theorem B43237709 : Blo 1999435 43237709 := bstep (se 3 (by rfl) ⟨8107070, by rfl⟩ : syracuseStep 43237709 = 16214141) B16214141
theorem B28825139 : Blo 1999435 28825139 := bstep (se 1 (by rfl) ⟨21618854, by rfl⟩ : syracuseStep 28825139 = 43237709) B43237709
theorem B19216759 : Blo 1999435 19216759 := bstep (se 1 (by rfl) ⟨14412569, by rfl⟩ : syracuseStep 19216759 = 28825139) B28825139
theorem B25622345 : Blo 1999435 25622345 := bstep (se 2 (by rfl) ⟨9608379, by rfl⟩ : syracuseStep 25622345 = 19216759) B19216759
theorem B17081563 : Blo 1999435 17081563 := bstep (se 1 (by rfl) ⟨12811172, by rfl⟩ : syracuseStep 17081563 = 25622345) B25622345
theorem B22775417 : Blo 1999435 22775417 := bstep (se 2 (by rfl) ⟨8540781, by rfl⟩ : syracuseStep 22775417 = 17081563) B17081563
theorem B15183611 : Blo 1999435 15183611 := bstep (se 1 (by rfl) ⟨11387708, by rfl⟩ : syracuseStep 15183611 = 22775417) B22775417
theorem B10122407 : Blo 1999435 10122407 := bstep (se 1 (by rfl) ⟨7591805, by rfl⟩ : syracuseStep 10122407 = 15183611) B15183611
theorem B6748271 : Blo 1999435 6748271 := bstep (se 1 (by rfl) ⟨5061203, by rfl⟩ : syracuseStep 6748271 = 10122407) B10122407
theorem B4498847 : Blo 1999435 4498847 := bstep (se 1 (by rfl) ⟨3374135, by rfl⟩ : syracuseStep 4498847 = 6748271) B6748271
theorem B2999231 : Blo 1999435 2999231 := bstep (se 1 (by rfl) ⟨2249423, by rfl⟩ : syracuseStep 2999231 = 4498847) B4498847
theorem B1999487 : Blo 1999435 1999487 := bstep (se 1 (by rfl) ⟨1499615, by rfl⟩ : syracuseStep 1999487 = 2999231) B2999231
theorem B2999237 : Blo 1999435 2999237 := bbase (se 4 (by rfl) ⟨281178, by rfl⟩ : syracuseStep 2999237 = 562357) (by norm_num)
theorem B1999491 : Blo 1999435 1999491 := bstep (se 1 (by rfl) ⟨1499618, by rfl⟩ : syracuseStep 1999491 = 2999237) B2999237
theorem B3374149 : Blo 1999435 3374149 := bbase (se 4 (by rfl) ⟨316326, by rfl⟩ : syracuseStep 3374149 = 632653) (by norm_num)
theorem B4498865 : Blo 1999435 4498865 := bstep (se 2 (by rfl) ⟨1687074, by rfl⟩ : syracuseStep 4498865 = 3374149) B3374149
theorem B2999243 : Blo 1999435 2999243 := bstep (se 1 (by rfl) ⟨2249432, by rfl⟩ : syracuseStep 2999243 = 4498865) B4498865
theorem B1999495 : Blo 1999435 1999495 := bstep (se 1 (by rfl) ⟨1499621, by rfl⟩ : syracuseStep 1999495 = 2999243) B2999243
theorem B2249437 : Blo 1999435 2249437 := bbase (se 3 (by rfl) ⟨421769, by rfl⟩ : syracuseStep 2249437 = 843539) (by norm_num)
theorem B2999249 : Blo 1999435 2999249 := bstep (se 2 (by rfl) ⟨1124718, by rfl⟩ : syracuseStep 2999249 = 2249437) B2249437
theorem B1999499 : Blo 1999435 1999499 := bstep (se 1 (by rfl) ⟨1499624, by rfl⟩ : syracuseStep 1999499 = 2999249) B2999249
theorem B6748325 : Blo 1999435 6748325 := bbase (se 4 (by rfl) ⟨632655, by rfl⟩ : syracuseStep 6748325 = 1265311) (by norm_num)
theorem B4498883 : Blo 1999435 4498883 := bstep (se 1 (by rfl) ⟨3374162, by rfl⟩ : syracuseStep 4498883 = 6748325) B6748325
theorem B2999255 : Blo 1999435 2999255 := bstep (se 1 (by rfl) ⟨2249441, by rfl⟩ : syracuseStep 2999255 = 4498883) B4498883
theorem B1999503 : Blo 1999435 1999503 := bstep (se 1 (by rfl) ⟨1499627, by rfl⟩ : syracuseStep 1999503 = 2999255) B2999255
theorem B2999261 : Blo 1999435 2999261 := bbase (se 3 (by rfl) ⟨562361, by rfl⟩ : syracuseStep 2999261 = 1124723) (by norm_num)
theorem B1999507 : Blo 1999435 1999507 := bstep (se 1 (by rfl) ⟨1499630, by rfl⟩ : syracuseStep 1999507 = 2999261) B2999261
theorem B4498901 : Blo 1999435 4498901 := bbase (se 7 (by rfl) ⟨52721, by rfl⟩ : syracuseStep 4498901 = 105443) (by norm_num)
theorem B2999267 : Blo 1999435 2999267 := bstep (se 1 (by rfl) ⟨2249450, by rfl⟩ : syracuseStep 2999267 = 4498901) B4498901
theorem B1999511 : Blo 1999435 1999511 := bstep (se 1 (by rfl) ⟨1499633, by rfl⟩ : syracuseStep 1999511 = 2999267) B2999267
theorem B5771621 : Blo 1999435 5771621 := bbase (se 4 (by rfl) ⟨541089, by rfl⟩ : syracuseStep 5771621 = 1082179) (by norm_num)
theorem B3847747 : Blo 1999435 3847747 := bstep (se 1 (by rfl) ⟨2885810, by rfl⟩ : syracuseStep 3847747 = 5771621) B5771621
theorem B5130329 : Blo 1999435 5130329 := bstep (se 2 (by rfl) ⟨1923873, by rfl⟩ : syracuseStep 5130329 = 3847747) B3847747
theorem B54723509 : Blo 1999435 54723509 := bstep (se 5 (by rfl) ⟨2565164, by rfl⟩ : syracuseStep 54723509 = 5130329) B5130329
theorem B36482339 : Blo 1999435 36482339 := bstep (se 1 (by rfl) ⟨27361754, by rfl⟩ : syracuseStep 36482339 = 54723509) B54723509
theorem B24321559 : Blo 1999435 24321559 := bstep (se 1 (by rfl) ⟨18241169, by rfl⟩ : syracuseStep 24321559 = 36482339) B36482339
theorem B32428745 : Blo 1999435 32428745 := bstep (se 2 (by rfl) ⟨12160779, by rfl⟩ : syracuseStep 32428745 = 24321559) B24321559
theorem B21619163 : Blo 1999435 21619163 := bstep (se 1 (by rfl) ⟨16214372, by rfl⟩ : syracuseStep 21619163 = 32428745) B32428745
theorem B14412775 : Blo 1999435 14412775 := bstep (se 1 (by rfl) ⟨10809581, by rfl⟩ : syracuseStep 14412775 = 21619163) B21619163
theorem B19217033 : Blo 1999435 19217033 := bstep (se 2 (by rfl) ⟨7206387, by rfl⟩ : syracuseStep 19217033 = 14412775) B14412775
theorem B12811355 : Blo 1999435 12811355 := bstep (se 1 (by rfl) ⟨9608516, by rfl⟩ : syracuseStep 12811355 = 19217033) B19217033
theorem B8540903 : Blo 1999435 8540903 := bstep (se 1 (by rfl) ⟨6405677, by rfl⟩ : syracuseStep 8540903 = 12811355) B12811355
theorem B5693935 : Blo 1999435 5693935 := bstep (se 1 (by rfl) ⟨4270451, by rfl⟩ : syracuseStep 5693935 = 8540903) B8540903
theorem B7591913 : Blo 1999435 7591913 := bstep (se 2 (by rfl) ⟨2846967, by rfl⟩ : syracuseStep 7591913 = 5693935) B5693935
theorem B5061275 : Blo 1999435 5061275 := bstep (se 1 (by rfl) ⟨3795956, by rfl⟩ : syracuseStep 5061275 = 7591913) B7591913
theorem B3374183 : Blo 1999435 3374183 := bstep (se 1 (by rfl) ⟨2530637, by rfl⟩ : syracuseStep 3374183 = 5061275) B5061275
theorem B2249455 : Blo 1999435 2249455 := bstep (se 1 (by rfl) ⟨1687091, by rfl⟩ : syracuseStep 2249455 = 3374183) B3374183
theorem B2999273 : Blo 1999435 2999273 := bstep (se 2 (by rfl) ⟨1124727, by rfl⟩ : syracuseStep 2999273 = 2249455) B2249455
theorem B1999515 : Blo 1999435 1999515 := bstep (se 1 (by rfl) ⟨1499636, by rfl⟩ : syracuseStep 1999515 = 2999273) B2999273
theorem B5130341 : Blo 1999435 5130341 := bbase (se 4 (by rfl) ⟨480969, by rfl⟩ : syracuseStep 5130341 = 961939) (by norm_num)
theorem B3420227 : Blo 1999435 3420227 := bstep (se 1 (by rfl) ⟨2565170, by rfl⟩ : syracuseStep 3420227 = 5130341) B5130341
theorem B2280151 : Blo 1999435 2280151 := bstep (se 1 (by rfl) ⟨1710113, by rfl⟩ : syracuseStep 2280151 = 3420227) B3420227
theorem B3040201 : Blo 1999435 3040201 := bstep (se 2 (by rfl) ⟨1140075, by rfl⟩ : syracuseStep 3040201 = 2280151) B2280151
theorem B4053601 : Blo 1999435 4053601 := bstep (se 2 (by rfl) ⟨1520100, by rfl⟩ : syracuseStep 4053601 = 3040201) B3040201
theorem B5404801 : Blo 1999435 5404801 := bstep (se 2 (by rfl) ⟨2026800, by rfl⟩ : syracuseStep 5404801 = 4053601) B4053601
theorem B7206401 : Blo 1999435 7206401 := bstep (se 2 (by rfl) ⟨2702400, by rfl⟩ : syracuseStep 7206401 = 5404801) B5404801
theorem B4804267 : Blo 1999435 4804267 := bstep (se 1 (by rfl) ⟨3603200, by rfl⟩ : syracuseStep 4804267 = 7206401) B7206401
theorem B6405689 : Blo 1999435 6405689 := bstep (se 2 (by rfl) ⟨2402133, by rfl⟩ : syracuseStep 6405689 = 4804267) B4804267
theorem B17081837 : Blo 1999435 17081837 := bstep (se 3 (by rfl) ⟨3202844, by rfl⟩ : syracuseStep 17081837 = 6405689) B6405689
theorem B11387891 : Blo 1999435 11387891 := bstep (se 1 (by rfl) ⟨8540918, by rfl⟩ : syracuseStep 11387891 = 17081837) B17081837
theorem B7591927 : Blo 1999435 7591927 := bstep (se 1 (by rfl) ⟨5693945, by rfl⟩ : syracuseStep 7591927 = 11387891) B11387891
theorem B10122569 : Blo 1999435 10122569 := bstep (se 2 (by rfl) ⟨3795963, by rfl⟩ : syracuseStep 10122569 = 7591927) B7591927
theorem B6748379 : Blo 1999435 6748379 := bstep (se 1 (by rfl) ⟨5061284, by rfl⟩ : syracuseStep 6748379 = 10122569) B10122569
theorem B4498919 : Blo 1999435 4498919 := bstep (se 1 (by rfl) ⟨3374189, by rfl⟩ : syracuseStep 4498919 = 6748379) B6748379
theorem B2999279 : Blo 1999435 2999279 := bstep (se 1 (by rfl) ⟨2249459, by rfl⟩ : syracuseStep 2999279 = 4498919) B4498919
theorem B1999519 : Blo 1999435 1999519 := bstep (se 1 (by rfl) ⟨1499639, by rfl⟩ : syracuseStep 1999519 = 2999279) B2999279
theorem B2999285 : Blo 1999435 2999285 := bbase (se 5 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 2999285 = 281183) (by norm_num)
theorem B1999523 : Blo 1999435 1999523 := bstep (se 1 (by rfl) ⟨1499642, by rfl⟩ : syracuseStep 1999523 = 2999285) B2999285
theorem B4270477 : Blo 1999435 4270477 := bbase (se 3 (by rfl) ⟨800714, by rfl⟩ : syracuseStep 4270477 = 1601429) (by norm_num)
theorem B5693969 : Blo 1999435 5693969 := bstep (se 2 (by rfl) ⟨2135238, by rfl⟩ : syracuseStep 5693969 = 4270477) B4270477
theorem B3795979 : Blo 1999435 3795979 := bstep (se 1 (by rfl) ⟨2846984, by rfl⟩ : syracuseStep 3795979 = 5693969) B5693969
theorem B5061305 : Blo 1999435 5061305 := bstep (se 2 (by rfl) ⟨1897989, by rfl⟩ : syracuseStep 5061305 = 3795979) B3795979
theorem B3374203 : Blo 1999435 3374203 := bstep (se 1 (by rfl) ⟨2530652, by rfl⟩ : syracuseStep 3374203 = 5061305) B5061305
theorem B4498937 : Blo 1999435 4498937 := bstep (se 2 (by rfl) ⟨1687101, by rfl⟩ : syracuseStep 4498937 = 3374203) B3374203
theorem B2999291 : Blo 1999435 2999291 := bstep (se 1 (by rfl) ⟨2249468, by rfl⟩ : syracuseStep 2999291 = 4498937) B4498937
theorem B1999527 : Blo 1999435 1999527 := bstep (se 1 (by rfl) ⟨1499645, by rfl⟩ : syracuseStep 1999527 = 2999291) B2999291
theorem B2249473 : Blo 1999435 2249473 := bbase (se 2 (by rfl) ⟨843552, by rfl⟩ : syracuseStep 2249473 = 1687105) (by norm_num)
theorem B2999297 : Blo 1999435 2999297 := bstep (se 2 (by rfl) ⟨1124736, by rfl⟩ : syracuseStep 2999297 = 2249473) B2249473
theorem B1999531 : Blo 1999435 1999531 := bstep (se 1 (by rfl) ⟨1499648, by rfl⟩ : syracuseStep 1999531 = 2999297) B2999297
theorem B5061325 : Blo 1999435 5061325 := bbase (se 3 (by rfl) ⟨948998, by rfl⟩ : syracuseStep 5061325 = 1897997) (by norm_num)
theorem B6748433 : Blo 1999435 6748433 := bstep (se 2 (by rfl) ⟨2530662, by rfl⟩ : syracuseStep 6748433 = 5061325) B5061325
theorem B4498955 : Blo 1999435 4498955 := bstep (se 1 (by rfl) ⟨3374216, by rfl⟩ : syracuseStep 4498955 = 6748433) B6748433
theorem B2999303 : Blo 1999435 2999303 := bstep (se 1 (by rfl) ⟨2249477, by rfl⟩ : syracuseStep 2999303 = 4498955) B4498955
theorem B1999535 : Blo 1999435 1999535 := bstep (se 1 (by rfl) ⟨1499651, by rfl⟩ : syracuseStep 1999535 = 2999303) B2999303
theorem B2999309 : Blo 1999435 2999309 := bbase (se 3 (by rfl) ⟨562370, by rfl⟩ : syracuseStep 2999309 = 1124741) (by norm_num)
theorem B1999539 : Blo 1999435 1999539 := bstep (se 1 (by rfl) ⟨1499654, by rfl⟩ : syracuseStep 1999539 = 2999309) B2999309
theorem B4498973 : Blo 1999435 4498973 := bbase (se 3 (by rfl) ⟨843557, by rfl⟩ : syracuseStep 4498973 = 1687115) (by norm_num)
theorem B2999315 : Blo 1999435 2999315 := bstep (se 1 (by rfl) ⟨2249486, by rfl⟩ : syracuseStep 2999315 = 4498973) B4498973
theorem B1999543 : Blo 1999435 1999543 := bstep (se 1 (by rfl) ⟨1499657, by rfl⟩ : syracuseStep 1999543 = 2999315) B2999315
theorem B3374237 : Blo 1999435 3374237 := bbase (se 3 (by rfl) ⟨632669, by rfl⟩ : syracuseStep 3374237 = 1265339) (by norm_num)
theorem B2249491 : Blo 1999435 2249491 := bstep (se 1 (by rfl) ⟨1687118, by rfl⟩ : syracuseStep 2249491 = 3374237) B3374237
theorem B2999321 : Blo 1999435 2999321 := bstep (se 2 (by rfl) ⟨1124745, by rfl⟩ : syracuseStep 2999321 = 2249491) B2249491
theorem B1999547 : Blo 1999435 1999547 := bstep (se 1 (by rfl) ⟨1499660, by rfl⟩ : syracuseStep 1999547 = 2999321) B2999321
theorem B7304837 : Blo 1999435 7304837 := bbase (se 4 (by rfl) ⟨684828, by rfl⟩ : syracuseStep 7304837 = 1369657) (by norm_num)
theorem B19479565 : Blo 1999435 19479565 := bstep (se 3 (by rfl) ⟨3652418, by rfl⟩ : syracuseStep 19479565 = 7304837) B7304837
theorem B25972753 : Blo 1999435 25972753 := bstep (se 2 (by rfl) ⟨9739782, by rfl⟩ : syracuseStep 25972753 = 19479565) B19479565
theorem B34630337 : Blo 1999435 34630337 := bstep (se 2 (by rfl) ⟨12986376, by rfl⟩ : syracuseStep 34630337 = 25972753) B25972753
theorem B23086891 : Blo 1999435 23086891 := bstep (se 1 (by rfl) ⟨17315168, by rfl⟩ : syracuseStep 23086891 = 34630337) B34630337
theorem B30782521 : Blo 1999435 30782521 := bstep (se 2 (by rfl) ⟨11543445, by rfl⟩ : syracuseStep 30782521 = 23086891) B23086891
theorem B41043361 : Blo 1999435 41043361 := bstep (se 2 (by rfl) ⟨15391260, by rfl⟩ : syracuseStep 41043361 = 30782521) B30782521
theorem B54724481 : Blo 1999435 54724481 := bstep (se 2 (by rfl) ⟨20521680, by rfl⟩ : syracuseStep 54724481 = 41043361) B41043361
theorem B36482987 : Blo 1999435 36482987 := bstep (se 1 (by rfl) ⟨27362240, by rfl⟩ : syracuseStep 36482987 = 54724481) B54724481
theorem B97287965 : Blo 1999435 97287965 := bstep (se 3 (by rfl) ⟨18241493, by rfl⟩ : syracuseStep 97287965 = 36482987) B36482987
theorem B64858643 : Blo 1999435 64858643 := bstep (se 1 (by rfl) ⟨48643982, by rfl⟩ : syracuseStep 64858643 = 97287965) B97287965
theorem B43239095 : Blo 1999435 43239095 := bstep (se 1 (by rfl) ⟨32429321, by rfl⟩ : syracuseStep 43239095 = 64858643) B64858643
theorem B28826063 : Blo 1999435 28826063 := bstep (se 1 (by rfl) ⟨21619547, by rfl⟩ : syracuseStep 28826063 = 43239095) B43239095
theorem B19217375 : Blo 1999435 19217375 := bstep (se 1 (by rfl) ⟨14413031, by rfl⟩ : syracuseStep 19217375 = 28826063) B28826063
theorem B12811583 : Blo 1999435 12811583 := bstep (se 1 (by rfl) ⟨9608687, by rfl⟩ : syracuseStep 12811583 = 19217375) B19217375
theorem B8541055 : Blo 1999435 8541055 := bstep (se 1 (by rfl) ⟨6405791, by rfl⟩ : syracuseStep 8541055 = 12811583) B12811583
theorem B11388073 : Blo 1999435 11388073 := bstep (se 2 (by rfl) ⟨4270527, by rfl⟩ : syracuseStep 11388073 = 8541055) B8541055
theorem B15184097 : Blo 1999435 15184097 := bstep (se 2 (by rfl) ⟨5694036, by rfl⟩ : syracuseStep 15184097 = 11388073) B11388073
theorem B10122731 : Blo 1999435 10122731 := bstep (se 1 (by rfl) ⟨7592048, by rfl⟩ : syracuseStep 10122731 = 15184097) B15184097
theorem B6748487 : Blo 1999435 6748487 := bstep (se 1 (by rfl) ⟨5061365, by rfl⟩ : syracuseStep 6748487 = 10122731) B10122731
theorem B4498991 : Blo 1999435 4498991 := bstep (se 1 (by rfl) ⟨3374243, by rfl⟩ : syracuseStep 4498991 = 6748487) B6748487
theorem B2999327 : Blo 1999435 2999327 := bstep (se 1 (by rfl) ⟨2249495, by rfl⟩ : syracuseStep 2999327 = 4498991) B4498991
theorem B1999551 : Blo 1999435 1999551 := bstep (se 1 (by rfl) ⟨1499663, by rfl⟩ : syracuseStep 1999551 = 2999327) B2999327
theorem B2999333 : Blo 1999435 2999333 := bbase (se 4 (by rfl) ⟨281187, by rfl⟩ : syracuseStep 2999333 = 562375) (by norm_num)
theorem B1999555 : Blo 1999435 1999555 := bstep (se 1 (by rfl) ⟨1499666, by rfl⟩ : syracuseStep 1999555 = 2999333) B2999333
theorem B2530693 : Blo 1999435 2530693 := bbase (se 4 (by rfl) ⟨237252, by rfl⟩ : syracuseStep 2530693 = 474505) (by norm_num)
theorem B3374257 : Blo 1999435 3374257 := bstep (se 2 (by rfl) ⟨1265346, by rfl⟩ : syracuseStep 3374257 = 2530693) B2530693
theorem B4499009 : Blo 1999435 4499009 := bstep (se 2 (by rfl) ⟨1687128, by rfl⟩ : syracuseStep 4499009 = 3374257) B3374257
theorem B2999339 : Blo 1999435 2999339 := bstep (se 1 (by rfl) ⟨2249504, by rfl⟩ : syracuseStep 2999339 = 4499009) B4499009
theorem B1999559 : Blo 1999435 1999559 := bstep (se 1 (by rfl) ⟨1499669, by rfl⟩ : syracuseStep 1999559 = 2999339) B2999339
theorem B2249509 : Blo 1999435 2249509 := bbase (se 4 (by rfl) ⟨210891, by rfl⟩ : syracuseStep 2249509 = 421783) (by norm_num)
theorem B2999345 : Blo 1999435 2999345 := bstep (se 2 (by rfl) ⟨1124754, by rfl⟩ : syracuseStep 2999345 = 2249509) B2249509
theorem B1999563 : Blo 1999435 1999563 := bstep (se 1 (by rfl) ⟨1499672, by rfl⟩ : syracuseStep 1999563 = 2999345) B2999345
theorem B8541125 : Blo 1999435 8541125 := bbase (se 4 (by rfl) ⟨800730, by rfl⟩ : syracuseStep 8541125 = 1601461) (by norm_num)
theorem B5694083 : Blo 1999435 5694083 := bstep (se 1 (by rfl) ⟨4270562, by rfl⟩ : syracuseStep 5694083 = 8541125) B8541125
theorem B3796055 : Blo 1999435 3796055 := bstep (se 1 (by rfl) ⟨2847041, by rfl⟩ : syracuseStep 3796055 = 5694083) B5694083
theorem B2530703 : Blo 1999435 2530703 := bstep (se 1 (by rfl) ⟨1898027, by rfl⟩ : syracuseStep 2530703 = 3796055) B3796055
theorem B6748541 : Blo 1999435 6748541 := bstep (se 3 (by rfl) ⟨1265351, by rfl⟩ : syracuseStep 6748541 = 2530703) B2530703
theorem B4499027 : Blo 1999435 4499027 := bstep (se 1 (by rfl) ⟨3374270, by rfl⟩ : syracuseStep 4499027 = 6748541) B6748541
theorem B2999351 : Blo 1999435 2999351 := bstep (se 1 (by rfl) ⟨2249513, by rfl⟩ : syracuseStep 2999351 = 4499027) B4499027
theorem B1999567 : Blo 1999435 1999567 := bstep (se 1 (by rfl) ⟨1499675, by rfl⟩ : syracuseStep 1999567 = 2999351) B2999351
theorem B2999357 : Blo 1999435 2999357 := bbase (se 3 (by rfl) ⟨562379, by rfl⟩ : syracuseStep 2999357 = 1124759) (by norm_num)
theorem B1999571 : Blo 1999435 1999571 := bstep (se 1 (by rfl) ⟨1499678, by rfl⟩ : syracuseStep 1999571 = 2999357) B2999357
theorem B4499045 : Blo 1999435 4499045 := bbase (se 4 (by rfl) ⟨421785, by rfl⟩ : syracuseStep 4499045 = 843571) (by norm_num)
theorem B2999363 : Blo 1999435 2999363 := bstep (se 1 (by rfl) ⟨2249522, by rfl⟩ : syracuseStep 2999363 = 4499045) B4499045
theorem B1999575 : Blo 1999435 1999575 := bstep (se 1 (by rfl) ⟨1499681, by rfl⟩ : syracuseStep 1999575 = 2999363) B2999363
theorem B5061437 : Blo 1999435 5061437 := bbase (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) (by norm_num)
theorem B3374291 : Blo 1999435 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B2249527 : Blo 1999435 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B2999369 : Blo 1999435 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B1999579 : Blo 1999435 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B3796085 : Blo 1999435 3796085 := bbase (se 5 (by rfl) ⟨177941, by rfl⟩ : syracuseStep 3796085 = 355883) (by norm_num)
theorem B10122893 : Blo 1999435 10122893 := bstep (se 3 (by rfl) ⟨1898042, by rfl⟩ : syracuseStep 10122893 = 3796085) B3796085
theorem B6748595 : Blo 1999435 6748595 := bstep (se 1 (by rfl) ⟨5061446, by rfl⟩ : syracuseStep 6748595 = 10122893) B10122893
theorem B4499063 : Blo 1999435 4499063 := bstep (se 1 (by rfl) ⟨3374297, by rfl⟩ : syracuseStep 4499063 = 6748595) B6748595
theorem B2999375 : Blo 1999435 2999375 := bstep (se 1 (by rfl) ⟨2249531, by rfl⟩ : syracuseStep 2999375 = 4499063) B4499063
theorem B1999583 : Blo 1999435 1999583 := bstep (se 1 (by rfl) ⟨1499687, by rfl⟩ : syracuseStep 1999583 = 2999375) B2999375
theorem B2999381 : Blo 1999435 2999381 := bbase (se 8 (by rfl) ⟨17574, by rfl⟩ : syracuseStep 2999381 = 35149) (by norm_num)
theorem B1999587 : Blo 1999435 1999587 := bstep (se 1 (by rfl) ⟨1499690, by rfl⟩ : syracuseStep 1999587 = 2999381) B2999381
theorem B7206661 : Blo 1999435 7206661 := bbase (se 4 (by rfl) ⟨675624, by rfl⟩ : syracuseStep 7206661 = 1351249) (by norm_num)
theorem B9608881 : Blo 1999435 9608881 := bstep (se 2 (by rfl) ⟨3603330, by rfl⟩ : syracuseStep 9608881 = 7206661) B7206661
theorem B12811841 : Blo 1999435 12811841 := bstep (se 2 (by rfl) ⟨4804440, by rfl⟩ : syracuseStep 12811841 = 9608881) B9608881
theorem B8541227 : Blo 1999435 8541227 := bstep (se 1 (by rfl) ⟨6405920, by rfl⟩ : syracuseStep 8541227 = 12811841) B12811841
theorem B5694151 : Blo 1999435 5694151 := bstep (se 1 (by rfl) ⟨4270613, by rfl⟩ : syracuseStep 5694151 = 8541227) B8541227
theorem B7592201 : Blo 1999435 7592201 := bstep (se 2 (by rfl) ⟨2847075, by rfl⟩ : syracuseStep 7592201 = 5694151) B5694151
theorem B5061467 : Blo 1999435 5061467 := bstep (se 1 (by rfl) ⟨3796100, by rfl⟩ : syracuseStep 5061467 = 7592201) B7592201
theorem B3374311 : Blo 1999435 3374311 := bstep (se 1 (by rfl) ⟨2530733, by rfl⟩ : syracuseStep 3374311 = 5061467) B5061467
theorem B4499081 : Blo 1999435 4499081 := bstep (se 2 (by rfl) ⟨1687155, by rfl⟩ : syracuseStep 4499081 = 3374311) B3374311
theorem B2999387 : Blo 1999435 2999387 := bstep (se 1 (by rfl) ⟨2249540, by rfl⟩ : syracuseStep 2999387 = 4499081) B4499081
theorem B1999591 : Blo 1999435 1999591 := bstep (se 1 (by rfl) ⟨1499693, by rfl⟩ : syracuseStep 1999591 = 2999387) B2999387
theorem B2249545 : Blo 1999435 2249545 := bbase (se 2 (by rfl) ⟨843579, by rfl⟩ : syracuseStep 2249545 = 1687159) (by norm_num)
theorem B2999393 : Blo 1999435 2999393 := bstep (se 2 (by rfl) ⟨1124772, by rfl⟩ : syracuseStep 2999393 = 2249545) B2249545
theorem B1999595 : Blo 1999435 1999595 := bstep (se 1 (by rfl) ⟨1499696, by rfl⟩ : syracuseStep 1999595 = 2999393) B2999393
theorem B6080645 : Blo 1999435 6080645 := bbase (se 4 (by rfl) ⟨570060, by rfl⟩ : syracuseStep 6080645 = 1140121) (by norm_num)
theorem B4053763 : Blo 1999435 4053763 := bstep (se 1 (by rfl) ⟨3040322, by rfl⟩ : syracuseStep 4053763 = 6080645) B6080645
theorem B5405017 : Blo 1999435 5405017 := bstep (se 2 (by rfl) ⟨2026881, by rfl⟩ : syracuseStep 5405017 = 4053763) B4053763
theorem B7206689 : Blo 1999435 7206689 := bstep (se 2 (by rfl) ⟨2702508, by rfl⟩ : syracuseStep 7206689 = 5405017) B5405017
theorem B19217837 : Blo 1999435 19217837 := bstep (se 3 (by rfl) ⟨3603344, by rfl⟩ : syracuseStep 19217837 = 7206689) B7206689
theorem B12811891 : Blo 1999435 12811891 := bstep (se 1 (by rfl) ⟨9608918, by rfl⟩ : syracuseStep 12811891 = 19217837) B19217837
theorem B17082521 : Blo 1999435 17082521 := bstep (se 2 (by rfl) ⟨6405945, by rfl⟩ : syracuseStep 17082521 = 12811891) B12811891
theorem B11388347 : Blo 1999435 11388347 := bstep (se 1 (by rfl) ⟨8541260, by rfl⟩ : syracuseStep 11388347 = 17082521) B17082521
theorem B7592231 : Blo 1999435 7592231 := bstep (se 1 (by rfl) ⟨5694173, by rfl⟩ : syracuseStep 7592231 = 11388347) B11388347
theorem B5061487 : Blo 1999435 5061487 := bstep (se 1 (by rfl) ⟨3796115, by rfl⟩ : syracuseStep 5061487 = 7592231) B7592231
theorem B6748649 : Blo 1999435 6748649 := bstep (se 2 (by rfl) ⟨2530743, by rfl⟩ : syracuseStep 6748649 = 5061487) B5061487
theorem B4499099 : Blo 1999435 4499099 := bstep (se 1 (by rfl) ⟨3374324, by rfl⟩ : syracuseStep 4499099 = 6748649) B6748649
theorem B2999399 : Blo 1999435 2999399 := bstep (se 1 (by rfl) ⟨2249549, by rfl⟩ : syracuseStep 2999399 = 4499099) B4499099
theorem B1999599 : Blo 1999435 1999599 := bstep (se 1 (by rfl) ⟨1499699, by rfl⟩ : syracuseStep 1999599 = 2999399) B2999399
theorem B2999405 : Blo 1999435 2999405 := bbase (se 3 (by rfl) ⟨562388, by rfl⟩ : syracuseStep 2999405 = 1124777) (by norm_num)
theorem B1999603 : Blo 1999435 1999603 := bstep (se 1 (by rfl) ⟨1499702, by rfl⟩ : syracuseStep 1999603 = 2999405) B2999405
theorem B4499117 : Blo 1999435 4499117 := bbase (se 3 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 4499117 = 1687169) (by norm_num)
theorem B2999411 : Blo 1999435 2999411 := bstep (se 1 (by rfl) ⟨2249558, by rfl⟩ : syracuseStep 2999411 = 4499117) B4499117
theorem B1999607 : Blo 1999435 1999607 := bstep (se 1 (by rfl) ⟨1499705, by rfl⟩ : syracuseStep 1999607 = 2999411) B2999411
theorem B2402245 : Blo 1999435 2402245 := bbase (se 4 (by rfl) ⟨225210, by rfl⟩ : syracuseStep 2402245 = 450421) (by norm_num)
theorem B3202993 : Blo 1999435 3202993 := bstep (se 2 (by rfl) ⟨1201122, by rfl⟩ : syracuseStep 3202993 = 2402245) B2402245
theorem B4270657 : Blo 1999435 4270657 := bstep (se 2 (by rfl) ⟨1601496, by rfl⟩ : syracuseStep 4270657 = 3202993) B3202993
theorem B5694209 : Blo 1999435 5694209 := bstep (se 2 (by rfl) ⟨2135328, by rfl⟩ : syracuseStep 5694209 = 4270657) B4270657
theorem B3796139 : Blo 1999435 3796139 := bstep (se 1 (by rfl) ⟨2847104, by rfl⟩ : syracuseStep 3796139 = 5694209) B5694209
theorem B2530759 : Blo 1999435 2530759 := bstep (se 1 (by rfl) ⟨1898069, by rfl⟩ : syracuseStep 2530759 = 3796139) B3796139
theorem B3374345 : Blo 1999435 3374345 := bstep (se 2 (by rfl) ⟨1265379, by rfl⟩ : syracuseStep 3374345 = 2530759) B2530759
theorem B2249563 : Blo 1999435 2249563 := bstep (se 1 (by rfl) ⟨1687172, by rfl⟩ : syracuseStep 2249563 = 3374345) B3374345
theorem B2999417 : Blo 1999435 2999417 := bstep (se 2 (by rfl) ⟨1124781, by rfl⟩ : syracuseStep 2999417 = 2249563) B2249563
theorem B1999611 : Blo 1999435 1999611 := bstep (se 1 (by rfl) ⟨1499708, by rfl⟩ : syracuseStep 1999611 = 2999417) B2999417
theorem B3603373 : Blo 1999435 3603373 := bbase (se 3 (by rfl) ⟨675632, by rfl⟩ : syracuseStep 3603373 = 1351265) (by norm_num)
theorem B19217989 : Blo 1999435 19217989 := bstep (se 4 (by rfl) ⟨1801686, by rfl⟩ : syracuseStep 19217989 = 3603373) B3603373
theorem B25623985 : Blo 1999435 25623985 := bstep (se 2 (by rfl) ⟨9608994, by rfl⟩ : syracuseStep 25623985 = 19217989) B19217989
theorem B34165313 : Blo 1999435 34165313 := bstep (se 2 (by rfl) ⟨12811992, by rfl⟩ : syracuseStep 34165313 = 25623985) B25623985
theorem B22776875 : Blo 1999435 22776875 := bstep (se 1 (by rfl) ⟨17082656, by rfl⟩ : syracuseStep 22776875 = 34165313) B34165313
theorem B15184583 : Blo 1999435 15184583 := bstep (se 1 (by rfl) ⟨11388437, by rfl⟩ : syracuseStep 15184583 = 22776875) B22776875
theorem B10123055 : Blo 1999435 10123055 := bstep (se 1 (by rfl) ⟨7592291, by rfl⟩ : syracuseStep 10123055 = 15184583) B15184583
theorem B6748703 : Blo 1999435 6748703 := bstep (se 1 (by rfl) ⟨5061527, by rfl⟩ : syracuseStep 6748703 = 10123055) B10123055
theorem B4499135 : Blo 1999435 4499135 := bstep (se 1 (by rfl) ⟨3374351, by rfl⟩ : syracuseStep 4499135 = 6748703) B6748703
theorem B2999423 : Blo 1999435 2999423 := bstep (se 1 (by rfl) ⟨2249567, by rfl⟩ : syracuseStep 2999423 = 4499135) B4499135
theorem B1999615 : Blo 1999435 1999615 := bstep (se 1 (by rfl) ⟨1499711, by rfl⟩ : syracuseStep 1999615 = 2999423) B2999423
theorem B2999429 : Blo 1999435 2999429 := bbase (se 4 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 2999429 = 562393) (by norm_num)
theorem B1999619 : Blo 1999435 1999619 := bstep (se 1 (by rfl) ⟨1499714, by rfl⟩ : syracuseStep 1999619 = 2999429) B2999429
theorem B3374365 : Blo 1999435 3374365 := bbase (se 3 (by rfl) ⟨632693, by rfl⟩ : syracuseStep 3374365 = 1265387) (by norm_num)
theorem B4499153 : Blo 1999435 4499153 := bstep (se 2 (by rfl) ⟨1687182, by rfl⟩ : syracuseStep 4499153 = 3374365) B3374365
theorem B2999435 : Blo 1999435 2999435 := bstep (se 1 (by rfl) ⟨2249576, by rfl⟩ : syracuseStep 2999435 = 4499153) B4499153
theorem B1999623 : Blo 1999435 1999623 := bstep (se 1 (by rfl) ⟨1499717, by rfl⟩ : syracuseStep 1999623 = 2999435) B2999435
theorem B2249581 : Blo 1999435 2249581 := bbase (se 3 (by rfl) ⟨421796, by rfl⟩ : syracuseStep 2249581 = 843593) (by norm_num)
theorem B2999441 : Blo 1999435 2999441 := bstep (se 2 (by rfl) ⟨1124790, by rfl⟩ : syracuseStep 2999441 = 2249581) B2249581
theorem B1999627 : Blo 1999435 1999627 := bstep (se 1 (by rfl) ⟨1499720, by rfl⟩ : syracuseStep 1999627 = 2999441) B2999441
theorem B6748757 : Blo 1999435 6748757 := bbase (se 8 (by rfl) ⟨39543, by rfl⟩ : syracuseStep 6748757 = 79087) (by norm_num)
theorem B4499171 : Blo 1999435 4499171 := bstep (se 1 (by rfl) ⟨3374378, by rfl⟩ : syracuseStep 4499171 = 6748757) B6748757
theorem B2999447 : Blo 1999435 2999447 := bstep (se 1 (by rfl) ⟨2249585, by rfl⟩ : syracuseStep 2999447 = 4499171) B4499171
theorem B1999631 : Blo 1999435 1999631 := bstep (se 1 (by rfl) ⟨1499723, by rfl⟩ : syracuseStep 1999631 = 2999447) B2999447
theorem B2999453 : Blo 1999435 2999453 := bbase (se 3 (by rfl) ⟨562397, by rfl⟩ : syracuseStep 2999453 = 1124795) (by norm_num)
theorem B1999635 : Blo 1999435 1999635 := bstep (se 1 (by rfl) ⟨1499726, by rfl⟩ : syracuseStep 1999635 = 2999453) B2999453
theorem B4499189 : Blo 1999435 4499189 := bbase (se 5 (by rfl) ⟨210899, by rfl⟩ : syracuseStep 4499189 = 421799) (by norm_num)
theorem B2999459 : Blo 1999435 2999459 := bstep (se 1 (by rfl) ⟨2249594, by rfl⟩ : syracuseStep 2999459 = 4499189) B4499189
theorem B1999639 : Blo 1999435 1999639 := bstep (se 1 (by rfl) ⟨1499729, by rfl⟩ : syracuseStep 1999639 = 2999459) B2999459
theorem B2565329 : Blo 1999435 2565329 := bbase (se 2 (by rfl) ⟨961998, by rfl⟩ : syracuseStep 2565329 = 1923997) (by norm_num)
theorem B6840877 : Blo 1999435 6840877 := bstep (se 3 (by rfl) ⟨1282664, by rfl⟩ : syracuseStep 6840877 = 2565329) B2565329
theorem B9121169 : Blo 1999435 9121169 := bstep (se 2 (by rfl) ⟨3420438, by rfl⟩ : syracuseStep 9121169 = 6840877) B6840877
theorem B6080779 : Blo 1999435 6080779 := bstep (se 1 (by rfl) ⟨4560584, by rfl⟩ : syracuseStep 6080779 = 9121169) B9121169
theorem B8107705 : Blo 1999435 8107705 := bstep (se 2 (by rfl) ⟨3040389, by rfl⟩ : syracuseStep 8107705 = 6080779) B6080779
theorem B10810273 : Blo 1999435 10810273 := bstep (se 2 (by rfl) ⟨4053852, by rfl⟩ : syracuseStep 10810273 = 8107705) B8107705
theorem B14413697 : Blo 1999435 14413697 := bstep (se 2 (by rfl) ⟨5405136, by rfl⟩ : syracuseStep 14413697 = 10810273) B10810273
theorem B9609131 : Blo 1999435 9609131 := bstep (se 1 (by rfl) ⟨7206848, by rfl⟩ : syracuseStep 9609131 = 14413697) B14413697
theorem B25624349 : Blo 1999435 25624349 := bstep (se 3 (by rfl) ⟨4804565, by rfl⟩ : syracuseStep 25624349 = 9609131) B9609131
theorem B17082899 : Blo 1999435 17082899 := bstep (se 1 (by rfl) ⟨12812174, by rfl⟩ : syracuseStep 17082899 = 25624349) B25624349
theorem B11388599 : Blo 1999435 11388599 := bstep (se 1 (by rfl) ⟨8541449, by rfl⟩ : syracuseStep 11388599 = 17082899) B17082899
theorem B7592399 : Blo 1999435 7592399 := bstep (se 1 (by rfl) ⟨5694299, by rfl⟩ : syracuseStep 7592399 = 11388599) B11388599
theorem B5061599 : Blo 1999435 5061599 := bstep (se 1 (by rfl) ⟨3796199, by rfl⟩ : syracuseStep 5061599 = 7592399) B7592399
theorem B3374399 : Blo 1999435 3374399 := bstep (se 1 (by rfl) ⟨2530799, by rfl⟩ : syracuseStep 3374399 = 5061599) B5061599
theorem B2249599 : Blo 1999435 2249599 := bstep (se 1 (by rfl) ⟨1687199, by rfl⟩ : syracuseStep 2249599 = 3374399) B3374399
theorem B2999465 : Blo 1999435 2999465 := bstep (se 2 (by rfl) ⟨1124799, by rfl⟩ : syracuseStep 2999465 = 2249599) B2249599
theorem B1999643 : Blo 1999435 1999643 := bstep (se 1 (by rfl) ⟨1499732, by rfl⟩ : syracuseStep 1999643 = 2999465) B2999465
theorem B4270733 : Blo 1999435 4270733 := bbase (se 3 (by rfl) ⟨800762, by rfl⟩ : syracuseStep 4270733 = 1601525) (by norm_num)
theorem B2847155 : Blo 1999435 2847155 := bstep (se 1 (by rfl) ⟨2135366, by rfl⟩ : syracuseStep 2847155 = 4270733) B4270733
theorem B7592413 : Blo 1999435 7592413 := bstep (se 3 (by rfl) ⟨1423577, by rfl⟩ : syracuseStep 7592413 = 2847155) B2847155
theorem B10123217 : Blo 1999435 10123217 := bstep (se 2 (by rfl) ⟨3796206, by rfl⟩ : syracuseStep 10123217 = 7592413) B7592413
theorem B6748811 : Blo 1999435 6748811 := bstep (se 1 (by rfl) ⟨5061608, by rfl⟩ : syracuseStep 6748811 = 10123217) B10123217
theorem B4499207 : Blo 1999435 4499207 := bstep (se 1 (by rfl) ⟨3374405, by rfl⟩ : syracuseStep 4499207 = 6748811) B6748811
theorem B2999471 : Blo 1999435 2999471 := bstep (se 1 (by rfl) ⟨2249603, by rfl⟩ : syracuseStep 2999471 = 4499207) B4499207
theorem B1999647 : Blo 1999435 1999647 := bstep (se 1 (by rfl) ⟨1499735, by rfl⟩ : syracuseStep 1999647 = 2999471) B2999471
theorem B2999477 : Blo 1999435 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B1999651 : Blo 1999435 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B5061629 : Blo 1999435 5061629 := bbase (se 3 (by rfl) ⟨949055, by rfl⟩ : syracuseStep 5061629 = 1898111) (by norm_num)
theorem B3374419 : Blo 1999435 3374419 := bstep (se 1 (by rfl) ⟨2530814, by rfl⟩ : syracuseStep 3374419 = 5061629) B5061629
theorem B4499225 : Blo 1999435 4499225 := bstep (se 2 (by rfl) ⟨1687209, by rfl⟩ : syracuseStep 4499225 = 3374419) B3374419
theorem B2999483 : Blo 1999435 2999483 := bstep (se 1 (by rfl) ⟨2249612, by rfl⟩ : syracuseStep 2999483 = 4499225) B4499225
theorem B1999655 : Blo 1999435 1999655 := bstep (se 1 (by rfl) ⟨1499741, by rfl⟩ : syracuseStep 1999655 = 2999483) B2999483
theorem B2249617 : Blo 1999435 2249617 := bbase (se 2 (by rfl) ⟨843606, by rfl⟩ : syracuseStep 2249617 = 1687213) (by norm_num)
theorem B2999489 : Blo 1999435 2999489 := bstep (se 2 (by rfl) ⟨1124808, by rfl⟩ : syracuseStep 2999489 = 2249617) B2249617
theorem B1999659 : Blo 1999435 1999659 := bstep (se 1 (by rfl) ⟨1499744, by rfl⟩ : syracuseStep 1999659 = 2999489) B2999489
theorem B3796237 : Blo 1999435 3796237 := bbase (se 3 (by rfl) ⟨711794, by rfl⟩ : syracuseStep 3796237 = 1423589) (by norm_num)
theorem B5061649 : Blo 1999435 5061649 := bstep (se 2 (by rfl) ⟨1898118, by rfl⟩ : syracuseStep 5061649 = 3796237) B3796237
theorem B6748865 : Blo 1999435 6748865 := bstep (se 2 (by rfl) ⟨2530824, by rfl⟩ : syracuseStep 6748865 = 5061649) B5061649
theorem B4499243 : Blo 1999435 4499243 := bstep (se 1 (by rfl) ⟨3374432, by rfl⟩ : syracuseStep 4499243 = 6748865) B6748865
theorem B2999495 : Blo 1999435 2999495 := bstep (se 1 (by rfl) ⟨2249621, by rfl⟩ : syracuseStep 2999495 = 4499243) B4499243
theorem B1999663 : Blo 1999435 1999663 := bstep (se 1 (by rfl) ⟨1499747, by rfl⟩ : syracuseStep 1999663 = 2999495) B2999495
theorem B2999501 : Blo 1999435 2999501 := bbase (se 3 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 2999501 = 1124813) (by norm_num)
theorem B1999667 : Blo 1999435 1999667 := bstep (se 1 (by rfl) ⟨1499750, by rfl⟩ : syracuseStep 1999667 = 2999501) B2999501
theorem B4499261 : Blo 1999435 4499261 := bbase (se 3 (by rfl) ⟨843611, by rfl⟩ : syracuseStep 4499261 = 1687223) (by norm_num)
theorem B2999507 : Blo 1999435 2999507 := bstep (se 1 (by rfl) ⟨2249630, by rfl⟩ : syracuseStep 2999507 = 4499261) B4499261
theorem B1999671 : Blo 1999435 1999671 := bstep (se 1 (by rfl) ⟨1499753, by rfl⟩ : syracuseStep 1999671 = 2999507) B2999507
theorem B3374453 : Blo 1999435 3374453 := bbase (se 5 (by rfl) ⟨158177, by rfl⟩ : syracuseStep 3374453 = 316355) (by norm_num)
theorem B2249635 : Blo 1999435 2249635 := bstep (se 1 (by rfl) ⟨1687226, by rfl⟩ : syracuseStep 2249635 = 3374453) B3374453
theorem B2999513 : Blo 1999435 2999513 := bstep (se 2 (by rfl) ⟨1124817, by rfl⟩ : syracuseStep 2999513 = 2249635) B2249635
theorem B1999675 : Blo 1999435 1999675 := bstep (se 1 (by rfl) ⟨1499756, by rfl⟩ : syracuseStep 1999675 = 2999513) B2999513
theorem B3203101 : Blo 1999435 3203101 := bbase (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) (by norm_num)
theorem B4270801 : Blo 1999435 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B5694401 : Blo 1999435 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B15185069 : Blo 1999435 15185069 := bstep (se 3 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 15185069 = 5694401) B5694401
theorem B10123379 : Blo 1999435 10123379 := bstep (se 1 (by rfl) ⟨7592534, by rfl⟩ : syracuseStep 10123379 = 15185069) B15185069
theorem B6748919 : Blo 1999435 6748919 := bstep (se 1 (by rfl) ⟨5061689, by rfl⟩ : syracuseStep 6748919 = 10123379) B10123379
theorem B4499279 : Blo 1999435 4499279 := bstep (se 1 (by rfl) ⟨3374459, by rfl⟩ : syracuseStep 4499279 = 6748919) B6748919
theorem B2999519 : Blo 1999435 2999519 := bstep (se 1 (by rfl) ⟨2249639, by rfl⟩ : syracuseStep 2999519 = 4499279) B4499279
theorem B1999679 : Blo 1999435 1999679 := bstep (se 1 (by rfl) ⟨1499759, by rfl⟩ : syracuseStep 1999679 = 2999519) B2999519
theorem B2999525 : Blo 1999435 2999525 := bbase (se 4 (by rfl) ⟨281205, by rfl⟩ : syracuseStep 2999525 = 562411) (by norm_num)
theorem B1999683 : Blo 1999435 1999683 := bstep (se 1 (by rfl) ⟨1499762, by rfl⟩ : syracuseStep 1999683 = 2999525) B2999525
theorem B6406229 : Blo 1999435 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B4270819 : Blo 1999435 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B5694425 : Blo 1999435 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B3796283 : Blo 1999435 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B2530855 : Blo 1999435 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B3374473 : Blo 1999435 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B4499297 : Blo 1999435 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B2999531 : Blo 1999435 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B1999687 : Blo 1999435 1999687 := bstep (se 1 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 1999687 = 2999531) B2999531
theorem B2249653 : Blo 1999435 2249653 := bbase (se 5 (by rfl) ⟨105452, by rfl⟩ : syracuseStep 2249653 = 210905) (by norm_num)
theorem B2999537 : Blo 1999435 2999537 := bstep (se 2 (by rfl) ⟨1124826, by rfl⟩ : syracuseStep 2999537 = 2249653) B2249653
theorem B1999691 : Blo 1999435 1999691 := bstep (se 1 (by rfl) ⟨1499768, by rfl⟩ : syracuseStep 1999691 = 2999537) B2999537
theorem B2530865 : Blo 1999435 2530865 := bbase (se 2 (by rfl) ⟨949074, by rfl⟩ : syracuseStep 2530865 = 1898149) (by norm_num)
theorem B6748973 : Blo 1999435 6748973 := bstep (se 3 (by rfl) ⟨1265432, by rfl⟩ : syracuseStep 6748973 = 2530865) B2530865
theorem B4499315 : Blo 1999435 4499315 := bstep (se 1 (by rfl) ⟨3374486, by rfl⟩ : syracuseStep 4499315 = 6748973) B6748973
theorem B2999543 : Blo 1999435 2999543 := bstep (se 1 (by rfl) ⟨2249657, by rfl⟩ : syracuseStep 2999543 = 4499315) B4499315
theorem B1999695 : Blo 1999435 1999695 := bstep (se 1 (by rfl) ⟨1499771, by rfl⟩ : syracuseStep 1999695 = 2999543) B2999543
theorem B2999549 : Blo 1999435 2999549 := bbase (se 3 (by rfl) ⟨562415, by rfl⟩ : syracuseStep 2999549 = 1124831) (by norm_num)
theorem B1999699 : Blo 1999435 1999699 := bstep (se 1 (by rfl) ⟨1499774, by rfl⟩ : syracuseStep 1999699 = 2999549) B2999549
theorem B4499333 : Blo 1999435 4499333 := bbase (se 4 (by rfl) ⟨421812, by rfl⟩ : syracuseStep 4499333 = 843625) (by norm_num)
theorem B2999555 : Blo 1999435 2999555 := bstep (se 1 (by rfl) ⟨2249666, by rfl⟩ : syracuseStep 2999555 = 4499333) B4499333
theorem B1999703 : Blo 1999435 1999703 := bstep (se 1 (by rfl) ⟨1499777, by rfl⟩ : syracuseStep 1999703 = 2999555) B2999555
theorem B3603541 : Blo 1999435 3603541 := bbase (se 8 (by rfl) ⟨21114, by rfl⟩ : syracuseStep 3603541 = 42229) (by norm_num)
theorem B4804721 : Blo 1999435 4804721 := bstep (se 2 (by rfl) ⟨1801770, by rfl⟩ : syracuseStep 4804721 = 3603541) B3603541
theorem B3203147 : Blo 1999435 3203147 := bstep (se 1 (by rfl) ⟨2402360, by rfl⟩ : syracuseStep 3203147 = 4804721) B4804721
theorem B2135431 : Blo 1999435 2135431 := bstep (se 1 (by rfl) ⟨1601573, by rfl⟩ : syracuseStep 2135431 = 3203147) B3203147
theorem B2847241 : Blo 1999435 2847241 := bstep (se 2 (by rfl) ⟨1067715, by rfl⟩ : syracuseStep 2847241 = 2135431) B2135431
theorem B3796321 : Blo 1999435 3796321 := bstep (se 2 (by rfl) ⟨1423620, by rfl⟩ : syracuseStep 3796321 = 2847241) B2847241
theorem B5061761 : Blo 1999435 5061761 := bstep (se 2 (by rfl) ⟨1898160, by rfl⟩ : syracuseStep 5061761 = 3796321) B3796321
theorem B3374507 : Blo 1999435 3374507 := bstep (se 1 (by rfl) ⟨2530880, by rfl⟩ : syracuseStep 3374507 = 5061761) B5061761
theorem B2249671 : Blo 1999435 2249671 := bstep (se 1 (by rfl) ⟨1687253, by rfl⟩ : syracuseStep 2249671 = 3374507) B3374507
theorem B2999561 : Blo 1999435 2999561 := bstep (se 2 (by rfl) ⟨1124835, by rfl⟩ : syracuseStep 2999561 = 2249671) B2249671
theorem B1999707 : Blo 1999435 1999707 := bstep (se 1 (by rfl) ⟨1499780, by rfl⟩ : syracuseStep 1999707 = 2999561) B2999561
theorem B10123541 : Blo 1999435 10123541 := bbase (se 6 (by rfl) ⟨237270, by rfl⟩ : syracuseStep 10123541 = 474541) (by norm_num)
theorem B6749027 : Blo 1999435 6749027 := bstep (se 1 (by rfl) ⟨5061770, by rfl⟩ : syracuseStep 6749027 = 10123541) B10123541
theorem B4499351 : Blo 1999435 4499351 := bstep (se 1 (by rfl) ⟨3374513, by rfl⟩ : syracuseStep 4499351 = 6749027) B6749027
theorem B2999567 : Blo 1999435 2999567 := bstep (se 1 (by rfl) ⟨2249675, by rfl⟩ : syracuseStep 2999567 = 4499351) B4499351
theorem B1999711 : Blo 1999435 1999711 := bstep (se 1 (by rfl) ⟨1499783, by rfl⟩ : syracuseStep 1999711 = 2999567) B2999567
theorem B2999573 : Blo 1999435 2999573 := bbase (se 6 (by rfl) ⟨70302, by rfl⟩ : syracuseStep 2999573 = 140605) (by norm_num)
theorem B1999715 : Blo 1999435 1999715 := bstep (se 1 (by rfl) ⟨1499786, by rfl⟩ : syracuseStep 1999715 = 2999573) B2999573
theorem B5629621 : Blo 1999435 5629621 := bbase (se 5 (by rfl) ⟨263888, by rfl⟩ : syracuseStep 5629621 = 527777) (by norm_num)
theorem B7506161 : Blo 1999435 7506161 := bstep (se 2 (by rfl) ⟨2814810, by rfl⟩ : syracuseStep 7506161 = 5629621) B5629621
theorem B5004107 : Blo 1999435 5004107 := bstep (se 1 (by rfl) ⟨3753080, by rfl⟩ : syracuseStep 5004107 = 7506161) B7506161
theorem B3336071 : Blo 1999435 3336071 := bstep (se 1 (by rfl) ⟨2502053, by rfl⟩ : syracuseStep 3336071 = 5004107) B5004107
theorem B8896189 : Blo 1999435 8896189 := bstep (se 3 (by rfl) ⟨1668035, by rfl⟩ : syracuseStep 8896189 = 3336071) B3336071
theorem B11861585 : Blo 1999435 11861585 := bstep (se 2 (by rfl) ⟨4448094, by rfl⟩ : syracuseStep 11861585 = 8896189) B8896189
theorem B7907723 : Blo 1999435 7907723 := bstep (se 1 (by rfl) ⟨5930792, by rfl⟩ : syracuseStep 7907723 = 11861585) B11861585
theorem B5271815 : Blo 1999435 5271815 := bstep (se 1 (by rfl) ⟨3953861, by rfl⟩ : syracuseStep 5271815 = 7907723) B7907723
theorem B14058173 : Blo 1999435 14058173 := bstep (se 3 (by rfl) ⟨2635907, by rfl⟩ : syracuseStep 14058173 = 5271815) B5271815
theorem B9372115 : Blo 1999435 9372115 := bstep (se 1 (by rfl) ⟨7029086, by rfl⟩ : syracuseStep 9372115 = 14058173) B14058173
theorem B12496153 : Blo 1999435 12496153 := bstep (se 2 (by rfl) ⟨4686057, by rfl⟩ : syracuseStep 12496153 = 9372115) B9372115
theorem B16661537 : Blo 1999435 16661537 := bstep (se 2 (by rfl) ⟨6248076, by rfl⟩ : syracuseStep 16661537 = 12496153) B12496153
theorem B11107691 : Blo 1999435 11107691 := bstep (se 1 (by rfl) ⟨8330768, by rfl⟩ : syracuseStep 11107691 = 16661537) B16661537
theorem B7405127 : Blo 1999435 7405127 := bstep (se 1 (by rfl) ⟨5553845, by rfl⟩ : syracuseStep 7405127 = 11107691) B11107691
theorem B4936751 : Blo 1999435 4936751 := bstep (se 1 (by rfl) ⟨3702563, by rfl⟩ : syracuseStep 4936751 = 7405127) B7405127
theorem B3291167 : Blo 1999435 3291167 := bstep (se 1 (by rfl) ⟨2468375, by rfl⟩ : syracuseStep 3291167 = 4936751) B4936751
theorem B2194111 : Blo 1999435 2194111 := bstep (se 1 (by rfl) ⟨1645583, by rfl⟩ : syracuseStep 2194111 = 3291167) B3291167
theorem B2925481 : Blo 1999435 2925481 := bstep (se 2 (by rfl) ⟨1097055, by rfl⟩ : syracuseStep 2925481 = 2194111) B2194111
theorem B3900641 : Blo 1999435 3900641 := bstep (se 2 (by rfl) ⟨1462740, by rfl⟩ : syracuseStep 3900641 = 2925481) B2925481
theorem B10401709 : Blo 1999435 10401709 := bstep (se 3 (by rfl) ⟨1950320, by rfl⟩ : syracuseStep 10401709 = 3900641) B3900641
theorem B13868945 : Blo 1999435 13868945 := bstep (se 2 (by rfl) ⟨5200854, by rfl⟩ : syracuseStep 13868945 = 10401709) B10401709
theorem B9245963 : Blo 1999435 9245963 := bstep (se 1 (by rfl) ⟨6934472, by rfl⟩ : syracuseStep 9245963 = 13868945) B13868945
theorem B6163975 : Blo 1999435 6163975 := bstep (se 1 (by rfl) ⟨4622981, by rfl⟩ : syracuseStep 6163975 = 9245963) B9245963
theorem B8218633 : Blo 1999435 8218633 := bstep (se 2 (by rfl) ⟨3081987, by rfl⟩ : syracuseStep 8218633 = 6163975) B6163975
theorem B10958177 : Blo 1999435 10958177 := bstep (se 2 (by rfl) ⟨4109316, by rfl⟩ : syracuseStep 10958177 = 8218633) B8218633
theorem B7305451 : Blo 1999435 7305451 := bstep (se 1 (by rfl) ⟨5479088, by rfl⟩ : syracuseStep 7305451 = 10958177) B10958177
theorem B38962405 : Blo 1999435 38962405 := bstep (se 4 (by rfl) ⟨3652725, by rfl⟩ : syracuseStep 38962405 = 7305451) B7305451
theorem B51949873 : Blo 1999435 51949873 := bstep (se 2 (by rfl) ⟨19481202, by rfl⟩ : syracuseStep 51949873 = 38962405) B38962405
theorem B69266497 : Blo 1999435 69266497 := bstep (se 2 (by rfl) ⟨25974936, by rfl⟩ : syracuseStep 69266497 = 51949873) B51949873
theorem B92355329 : Blo 1999435 92355329 := bstep (se 2 (by rfl) ⟨34633248, by rfl⟩ : syracuseStep 92355329 = 69266497) B69266497
theorem B61570219 : Blo 1999435 61570219 := bstep (se 1 (by rfl) ⟨46177664, by rfl⟩ : syracuseStep 61570219 = 92355329) B92355329
theorem B82093625 : Blo 1999435 82093625 := bstep (se 2 (by rfl) ⟨30785109, by rfl⟩ : syracuseStep 82093625 = 61570219) B61570219
theorem B54729083 : Blo 1999435 54729083 := bstep (se 1 (by rfl) ⟨41046812, by rfl⟩ : syracuseStep 54729083 = 82093625) B82093625
theorem B36486055 : Blo 1999435 36486055 := bstep (se 1 (by rfl) ⟨27364541, by rfl⟩ : syracuseStep 36486055 = 54729083) B54729083
theorem B48648073 : Blo 1999435 48648073 := bstep (se 2 (by rfl) ⟨18243027, by rfl⟩ : syracuseStep 48648073 = 36486055) B36486055
theorem B64864097 : Blo 1999435 64864097 := bstep (se 2 (by rfl) ⟨24324036, by rfl⟩ : syracuseStep 64864097 = 48648073) B48648073
theorem B43242731 : Blo 1999435 43242731 := bstep (se 1 (by rfl) ⟨32432048, by rfl⟩ : syracuseStep 43242731 = 64864097) B64864097
theorem B28828487 : Blo 1999435 28828487 := bstep (se 1 (by rfl) ⟨21621365, by rfl⟩ : syracuseStep 28828487 = 43242731) B43242731
theorem B19218991 : Blo 1999435 19218991 := bstep (se 1 (by rfl) ⟨14414243, by rfl⟩ : syracuseStep 19218991 = 28828487) B28828487
theorem B25625321 : Blo 1999435 25625321 := bstep (se 2 (by rfl) ⟨9609495, by rfl⟩ : syracuseStep 25625321 = 19218991) B19218991
theorem B17083547 : Blo 1999435 17083547 := bstep (se 1 (by rfl) ⟨12812660, by rfl⟩ : syracuseStep 17083547 = 25625321) B25625321
theorem B11389031 : Blo 1999435 11389031 := bstep (se 1 (by rfl) ⟨8541773, by rfl⟩ : syracuseStep 11389031 = 17083547) B17083547
theorem B7592687 : Blo 1999435 7592687 := bstep (se 1 (by rfl) ⟨5694515, by rfl⟩ : syracuseStep 7592687 = 11389031) B11389031
theorem B5061791 : Blo 1999435 5061791 := bstep (se 1 (by rfl) ⟨3796343, by rfl⟩ : syracuseStep 5061791 = 7592687) B7592687
theorem B3374527 : Blo 1999435 3374527 := bstep (se 1 (by rfl) ⟨2530895, by rfl⟩ : syracuseStep 3374527 = 5061791) B5061791
theorem B4499369 : Blo 1999435 4499369 := bstep (se 2 (by rfl) ⟨1687263, by rfl⟩ : syracuseStep 4499369 = 3374527) B3374527
theorem B2999579 : Blo 1999435 2999579 := bstep (se 1 (by rfl) ⟨2249684, by rfl⟩ : syracuseStep 2999579 = 4499369) B4499369
theorem B1999719 : Blo 1999435 1999719 := bstep (se 1 (by rfl) ⟨1499789, by rfl⟩ : syracuseStep 1999719 = 2999579) B2999579
theorem B2249689 : Blo 1999435 2249689 := bbase (se 2 (by rfl) ⟨843633, by rfl⟩ : syracuseStep 2249689 = 1687267) (by norm_num)
theorem B2999585 : Blo 1999435 2999585 := bstep (se 2 (by rfl) ⟨1124844, by rfl⟩ : syracuseStep 2999585 = 2249689) B2249689
theorem B1999723 : Blo 1999435 1999723 := bstep (se 1 (by rfl) ⟨1499792, by rfl⟩ : syracuseStep 1999723 = 2999585) B2999585
theorem B2847269 : Blo 1999435 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B7592717 : Blo 1999435 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B5061811 : Blo 1999435 5061811 := bstep (se 1 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 5061811 = 7592717) B7592717
theorem B6749081 : Blo 1999435 6749081 := bstep (se 2 (by rfl) ⟨2530905, by rfl⟩ : syracuseStep 6749081 = 5061811) B5061811
theorem B4499387 : Blo 1999435 4499387 := bstep (se 1 (by rfl) ⟨3374540, by rfl⟩ : syracuseStep 4499387 = 6749081) B6749081
theorem B2999591 : Blo 1999435 2999591 := bstep (se 1 (by rfl) ⟨2249693, by rfl⟩ : syracuseStep 2999591 = 4499387) B4499387
theorem B1999727 : Blo 1999435 1999727 := bstep (se 1 (by rfl) ⟨1499795, by rfl⟩ : syracuseStep 1999727 = 2999591) B2999591
theorem B2999597 : Blo 1999435 2999597 := bbase (se 3 (by rfl) ⟨562424, by rfl⟩ : syracuseStep 2999597 = 1124849) (by norm_num)
theorem B1999731 : Blo 1999435 1999731 := bstep (se 1 (by rfl) ⟨1499798, by rfl⟩ : syracuseStep 1999731 = 2999597) B2999597
theorem B4499405 : Blo 1999435 4499405 := bbase (se 3 (by rfl) ⟨843638, by rfl⟩ : syracuseStep 4499405 = 1687277) (by norm_num)
theorem B2999603 : Blo 1999435 2999603 := bstep (se 1 (by rfl) ⟨2249702, by rfl⟩ : syracuseStep 2999603 = 4499405) B4499405
theorem B1999735 : Blo 1999435 1999735 := bstep (se 1 (by rfl) ⟨1499801, by rfl⟩ : syracuseStep 1999735 = 2999603) B2999603
theorem B2530921 : Blo 1999435 2530921 := bbase (se 2 (by rfl) ⟨949095, by rfl⟩ : syracuseStep 2530921 = 1898191) (by norm_num)
theorem B3374561 : Blo 1999435 3374561 := bstep (se 2 (by rfl) ⟨1265460, by rfl⟩ : syracuseStep 3374561 = 2530921) B2530921
theorem B2249707 : Blo 1999435 2249707 := bstep (se 1 (by rfl) ⟨1687280, by rfl⟩ : syracuseStep 2249707 = 3374561) B3374561
theorem B2999609 : Blo 1999435 2999609 := bstep (se 2 (by rfl) ⟨1124853, by rfl⟩ : syracuseStep 2999609 = 2249707) B2249707
theorem B1999739 : Blo 1999435 1999739 := bstep (se 1 (by rfl) ⟨1499804, by rfl⟩ : syracuseStep 1999739 = 2999609) B2999609
theorem B4804805 : Blo 1999435 4804805 := bbase (se 4 (by rfl) ⟨450450, by rfl⟩ : syracuseStep 4804805 = 900901) (by norm_num)
theorem B12812813 : Blo 1999435 12812813 := bstep (se 3 (by rfl) ⟨2402402, by rfl⟩ : syracuseStep 12812813 = 4804805) B4804805
theorem B8541875 : Blo 1999435 8541875 := bstep (se 1 (by rfl) ⟨6406406, by rfl⟩ : syracuseStep 8541875 = 12812813) B12812813
theorem B22778333 : Blo 1999435 22778333 := bstep (se 3 (by rfl) ⟨4270937, by rfl⟩ : syracuseStep 22778333 = 8541875) B8541875
theorem B15185555 : Blo 1999435 15185555 := bstep (se 1 (by rfl) ⟨11389166, by rfl⟩ : syracuseStep 15185555 = 22778333) B22778333
theorem B10123703 : Blo 1999435 10123703 := bstep (se 1 (by rfl) ⟨7592777, by rfl⟩ : syracuseStep 10123703 = 15185555) B15185555
theorem B6749135 : Blo 1999435 6749135 := bstep (se 1 (by rfl) ⟨5061851, by rfl⟩ : syracuseStep 6749135 = 10123703) B10123703
theorem B4499423 : Blo 1999435 4499423 := bstep (se 1 (by rfl) ⟨3374567, by rfl⟩ : syracuseStep 4499423 = 6749135) B6749135
theorem B2999615 : Blo 1999435 2999615 := bstep (se 1 (by rfl) ⟨2249711, by rfl⟩ : syracuseStep 2999615 = 4499423) B4499423
theorem B1999743 : Blo 1999435 1999743 := bstep (se 1 (by rfl) ⟨1499807, by rfl⟩ : syracuseStep 1999743 = 2999615) B2999615
theorem B2999621 : Blo 1999435 2999621 := bbase (se 4 (by rfl) ⟨281214, by rfl⟩ : syracuseStep 2999621 = 562429) (by norm_num)
theorem B1999747 : Blo 1999435 1999747 := bstep (se 1 (by rfl) ⟨1499810, by rfl⟩ : syracuseStep 1999747 = 2999621) B2999621
theorem B3374581 : Blo 1999435 3374581 := bbase (se 5 (by rfl) ⟨158183, by rfl⟩ : syracuseStep 3374581 = 316367) (by norm_num)
theorem B4499441 : Blo 1999435 4499441 := bstep (se 2 (by rfl) ⟨1687290, by rfl⟩ : syracuseStep 4499441 = 3374581) B3374581
theorem B2999627 : Blo 1999435 2999627 := bstep (se 1 (by rfl) ⟨2249720, by rfl⟩ : syracuseStep 2999627 = 4499441) B4499441
theorem B1999751 : Blo 1999435 1999751 := bstep (se 1 (by rfl) ⟨1499813, by rfl⟩ : syracuseStep 1999751 = 2999627) B2999627
theorem B2249725 : Blo 1999435 2249725 := bbase (se 3 (by rfl) ⟨421823, by rfl⟩ : syracuseStep 2249725 = 843647) (by norm_num)
theorem B2999633 : Blo 1999435 2999633 := bstep (se 2 (by rfl) ⟨1124862, by rfl⟩ : syracuseStep 2999633 = 2249725) B2249725
theorem B1999755 : Blo 1999435 1999755 := bstep (se 1 (by rfl) ⟨1499816, by rfl⟩ : syracuseStep 1999755 = 2999633) B2999633
theorem B6749189 : Blo 1999435 6749189 := bbase (se 4 (by rfl) ⟨632736, by rfl⟩ : syracuseStep 6749189 = 1265473) (by norm_num)
theorem B4499459 : Blo 1999435 4499459 := bstep (se 1 (by rfl) ⟨3374594, by rfl⟩ : syracuseStep 4499459 = 6749189) B6749189
theorem B2999639 : Blo 1999435 2999639 := bstep (se 1 (by rfl) ⟨2249729, by rfl⟩ : syracuseStep 2999639 = 4499459) B4499459
theorem B1999759 : Blo 1999435 1999759 := bstep (se 1 (by rfl) ⟨1499819, by rfl⟩ : syracuseStep 1999759 = 2999639) B2999639
theorem B2999645 : Blo 1999435 2999645 := bbase (se 3 (by rfl) ⟨562433, by rfl⟩ : syracuseStep 2999645 = 1124867) (by norm_num)
theorem B1999763 : Blo 1999435 1999763 := bstep (se 1 (by rfl) ⟨1499822, by rfl⟩ : syracuseStep 1999763 = 2999645) B2999645
theorem B4499477 : Blo 1999435 4499477 := bbase (se 6 (by rfl) ⟨105456, by rfl⟩ : syracuseStep 4499477 = 210913) (by norm_num)
theorem B2999651 : Blo 1999435 2999651 := bstep (se 1 (by rfl) ⟨2249738, by rfl⟩ : syracuseStep 2999651 = 4499477) B4499477
theorem B1999767 : Blo 1999435 1999767 := bstep (se 1 (by rfl) ⟨1499825, by rfl⟩ : syracuseStep 1999767 = 2999651) B2999651
theorem B7592885 : Blo 1999435 7592885 := bbase (se 5 (by rfl) ⟨355916, by rfl⟩ : syracuseStep 7592885 = 711833) (by norm_num)
theorem B5061923 : Blo 1999435 5061923 := bstep (se 1 (by rfl) ⟨3796442, by rfl⟩ : syracuseStep 5061923 = 7592885) B7592885
theorem B3374615 : Blo 1999435 3374615 := bstep (se 1 (by rfl) ⟨2530961, by rfl⟩ : syracuseStep 3374615 = 5061923) B5061923
theorem B2249743 : Blo 1999435 2249743 := bstep (se 1 (by rfl) ⟨1687307, by rfl⟩ : syracuseStep 2249743 = 3374615) B3374615
theorem B2999657 : Blo 1999435 2999657 := bstep (se 2 (by rfl) ⟨1124871, by rfl⟩ : syracuseStep 2999657 = 2249743) B2249743
theorem B1999771 : Blo 1999435 1999771 := bstep (se 1 (by rfl) ⟨1499828, by rfl⟩ : syracuseStep 1999771 = 2999657) B2999657
theorem B2435221 : Blo 1999435 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B3246961 : Blo 1999435 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B4329281 : Blo 1999435 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2886187 : Blo 1999435 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B3848249 : Blo 1999435 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B10261997 : Blo 1999435 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B6841331 : Blo 1999435 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B4560887 : Blo 1999435 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B3040591 : Blo 1999435 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B4054121 : Blo 1999435 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B2702747 : Blo 1999435 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B7207325 : Blo 1999435 7207325 := bstep (se 3 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 7207325 = 2702747) B2702747
theorem B4804883 : Blo 1999435 4804883 := bstep (se 1 (by rfl) ⟨3603662, by rfl⟩ : syracuseStep 4804883 = 7207325) B7207325
theorem B3203255 : Blo 1999435 3203255 := bstep (se 1 (by rfl) ⟨2402441, by rfl⟩ : syracuseStep 3203255 = 4804883) B4804883
theorem B2135503 : Blo 1999435 2135503 := bstep (se 1 (by rfl) ⟨1601627, by rfl⟩ : syracuseStep 2135503 = 3203255) B3203255
theorem B11389349 : Blo 1999435 11389349 := bstep (se 4 (by rfl) ⟨1067751, by rfl⟩ : syracuseStep 11389349 = 2135503) B2135503
theorem B7592899 : Blo 1999435 7592899 := bstep (se 1 (by rfl) ⟨5694674, by rfl⟩ : syracuseStep 7592899 = 11389349) B11389349
theorem B10123865 : Blo 1999435 10123865 := bstep (se 2 (by rfl) ⟨3796449, by rfl⟩ : syracuseStep 10123865 = 7592899) B7592899
theorem B6749243 : Blo 1999435 6749243 := bstep (se 1 (by rfl) ⟨5061932, by rfl⟩ : syracuseStep 6749243 = 10123865) B10123865
theorem B4499495 : Blo 1999435 4499495 := bstep (se 1 (by rfl) ⟨3374621, by rfl⟩ : syracuseStep 4499495 = 6749243) B6749243
theorem B2999663 : Blo 1999435 2999663 := bstep (se 1 (by rfl) ⟨2249747, by rfl⟩ : syracuseStep 2999663 = 4499495) B4499495
theorem B1999775 : Blo 1999435 1999775 := bstep (se 1 (by rfl) ⟨1499831, by rfl⟩ : syracuseStep 1999775 = 2999663) B2999663
theorem B2999669 : Blo 1999435 2999669 := bbase (se 5 (by rfl) ⟨140609, by rfl⟩ : syracuseStep 2999669 = 281219) (by norm_num)
theorem B1999779 : Blo 1999435 1999779 := bstep (se 1 (by rfl) ⟨1499834, by rfl⟩ : syracuseStep 1999779 = 2999669) B2999669
theorem B2847349 : Blo 1999435 2847349 := bbase (se 5 (by rfl) ⟨133469, by rfl⟩ : syracuseStep 2847349 = 266939) (by norm_num)
theorem B3796465 : Blo 1999435 3796465 := bstep (se 2 (by rfl) ⟨1423674, by rfl⟩ : syracuseStep 3796465 = 2847349) B2847349
theorem B5061953 : Blo 1999435 5061953 := bstep (se 2 (by rfl) ⟨1898232, by rfl⟩ : syracuseStep 5061953 = 3796465) B3796465
theorem B3374635 : Blo 1999435 3374635 := bstep (se 1 (by rfl) ⟨2530976, by rfl⟩ : syracuseStep 3374635 = 5061953) B5061953
theorem B4499513 : Blo 1999435 4499513 := bstep (se 2 (by rfl) ⟨1687317, by rfl⟩ : syracuseStep 4499513 = 3374635) B3374635
theorem B2999675 : Blo 1999435 2999675 := bstep (se 1 (by rfl) ⟨2249756, by rfl⟩ : syracuseStep 2999675 = 4499513) B4499513
theorem B1999783 : Blo 1999435 1999783 := bstep (se 1 (by rfl) ⟨1499837, by rfl⟩ : syracuseStep 1999783 = 2999675) B2999675
theorem B2249761 : Blo 1999435 2249761 := bbase (se 2 (by rfl) ⟨843660, by rfl⟩ : syracuseStep 2249761 = 1687321) (by norm_num)
theorem B2999681 : Blo 1999435 2999681 := bstep (se 2 (by rfl) ⟨1124880, by rfl⟩ : syracuseStep 2999681 = 2249761) B2249761
theorem B1999787 : Blo 1999435 1999787 := bstep (se 1 (by rfl) ⟨1499840, by rfl⟩ : syracuseStep 1999787 = 2999681) B2999681
theorem B5061973 : Blo 1999435 5061973 := bbase (se 11 (by rfl) ⟨3707, by rfl⟩ : syracuseStep 5061973 = 7415) (by norm_num)
theorem B6749297 : Blo 1999435 6749297 := bstep (se 2 (by rfl) ⟨2530986, by rfl⟩ : syracuseStep 6749297 = 5061973) B5061973
theorem B4499531 : Blo 1999435 4499531 := bstep (se 1 (by rfl) ⟨3374648, by rfl⟩ : syracuseStep 4499531 = 6749297) B6749297
theorem B2999687 : Blo 1999435 2999687 := bstep (se 1 (by rfl) ⟨2249765, by rfl⟩ : syracuseStep 2999687 = 4499531) B4499531
theorem B1999791 : Blo 1999435 1999791 := bstep (se 1 (by rfl) ⟨1499843, by rfl⟩ : syracuseStep 1999791 = 2999687) B2999687
theorem B2999693 : Blo 1999435 2999693 := bbase (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) (by norm_num)
theorem B1999795 : Blo 1999435 1999795 := bstep (se 1 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 1999795 = 2999693) B2999693
theorem B4499549 : Blo 1999435 4499549 := bbase (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) (by norm_num)
theorem B2999699 : Blo 1999435 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B1999799 : Blo 1999435 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B3374669 : Blo 1999435 3374669 := bbase (se 3 (by rfl) ⟨632750, by rfl⟩ : syracuseStep 3374669 = 1265501) (by norm_num)
theorem B2249779 : Blo 1999435 2249779 := bstep (se 1 (by rfl) ⟨1687334, by rfl⟩ : syracuseStep 2249779 = 3374669) B3374669
theorem B2999705 : Blo 1999435 2999705 := bstep (se 2 (by rfl) ⟨1124889, by rfl⟩ : syracuseStep 2999705 = 2249779) B2249779
theorem B1999803 : Blo 1999435 1999803 := bstep (se 1 (by rfl) ⟨1499852, by rfl⟩ : syracuseStep 1999803 = 2999705) B2999705
theorem B18243829 : Blo 1999435 18243829 := bbase (se 5 (by rfl) ⟨855179, by rfl⟩ : syracuseStep 18243829 = 1710359) (by norm_num)
theorem B24325105 : Blo 1999435 24325105 := bstep (se 2 (by rfl) ⟨9121914, by rfl⟩ : syracuseStep 24325105 = 18243829) B18243829
theorem B32433473 : Blo 1999435 32433473 := bstep (se 2 (by rfl) ⟨12162552, by rfl⟩ : syracuseStep 32433473 = 24325105) B24325105
theorem B21622315 : Blo 1999435 21622315 := bstep (se 1 (by rfl) ⟨16216736, by rfl⟩ : syracuseStep 21622315 = 32433473) B32433473
theorem B28829753 : Blo 1999435 28829753 := bstep (se 2 (by rfl) ⟨10811157, by rfl⟩ : syracuseStep 28829753 = 21622315) B21622315
theorem B19219835 : Blo 1999435 19219835 := bstep (se 1 (by rfl) ⟨14414876, by rfl⟩ : syracuseStep 19219835 = 28829753) B28829753
theorem B12813223 : Blo 1999435 12813223 := bstep (se 1 (by rfl) ⟨9609917, by rfl⟩ : syracuseStep 12813223 = 19219835) B19219835
theorem B17084297 : Blo 1999435 17084297 := bstep (se 2 (by rfl) ⟨6406611, by rfl⟩ : syracuseStep 17084297 = 12813223) B12813223
theorem B11389531 : Blo 1999435 11389531 := bstep (se 1 (by rfl) ⟨8542148, by rfl⟩ : syracuseStep 11389531 = 17084297) B17084297
theorem B15186041 : Blo 1999435 15186041 := bstep (se 2 (by rfl) ⟨5694765, by rfl⟩ : syracuseStep 15186041 = 11389531) B11389531
theorem B10124027 : Blo 1999435 10124027 := bstep (se 1 (by rfl) ⟨7593020, by rfl⟩ : syracuseStep 10124027 = 15186041) B15186041
theorem B6749351 : Blo 1999435 6749351 := bstep (se 1 (by rfl) ⟨5062013, by rfl⟩ : syracuseStep 6749351 = 10124027) B10124027
theorem B4499567 : Blo 1999435 4499567 := bstep (se 1 (by rfl) ⟨3374675, by rfl⟩ : syracuseStep 4499567 = 6749351) B6749351
theorem B2999711 : Blo 1999435 2999711 := bstep (se 1 (by rfl) ⟨2249783, by rfl⟩ : syracuseStep 2999711 = 4499567) B4499567
theorem B1999807 : Blo 1999435 1999807 := bstep (se 1 (by rfl) ⟨1499855, by rfl⟩ : syracuseStep 1999807 = 2999711) B2999711
theorem B2999717 : Blo 1999435 2999717 := bbase (se 4 (by rfl) ⟨281223, by rfl⟩ : syracuseStep 2999717 = 562447) (by norm_num)
theorem B1999811 : Blo 1999435 1999811 := bstep (se 1 (by rfl) ⟨1499858, by rfl⟩ : syracuseStep 1999811 = 2999717) B2999717
theorem B2531017 : Blo 1999435 2531017 := bbase (se 2 (by rfl) ⟨949131, by rfl⟩ : syracuseStep 2531017 = 1898263) (by norm_num)
theorem B3374689 : Blo 1999435 3374689 := bstep (se 2 (by rfl) ⟨1265508, by rfl⟩ : syracuseStep 3374689 = 2531017) B2531017
theorem B4499585 : Blo 1999435 4499585 := bstep (se 2 (by rfl) ⟨1687344, by rfl⟩ : syracuseStep 4499585 = 3374689) B3374689
theorem B2999723 : Blo 1999435 2999723 := bstep (se 1 (by rfl) ⟨2249792, by rfl⟩ : syracuseStep 2999723 = 4499585) B4499585
theorem B1999815 : Blo 1999435 1999815 := bstep (se 1 (by rfl) ⟨1499861, by rfl⟩ : syracuseStep 1999815 = 2999723) B2999723
theorem B2249797 : Blo 1999435 2249797 := bbase (se 4 (by rfl) ⟨210918, by rfl⟩ : syracuseStep 2249797 = 421837) (by norm_num)
theorem B2999729 : Blo 1999435 2999729 := bstep (se 2 (by rfl) ⟨1124898, by rfl⟩ : syracuseStep 2999729 = 2249797) B2249797
theorem B1999819 : Blo 1999435 1999819 := bstep (se 1 (by rfl) ⟨1499864, by rfl⟩ : syracuseStep 1999819 = 2999729) B2999729
theorem B3796541 : Blo 1999435 3796541 := bbase (se 3 (by rfl) ⟨711851, by rfl⟩ : syracuseStep 3796541 = 1423703) (by norm_num)
theorem B2531027 : Blo 1999435 2531027 := bstep (se 1 (by rfl) ⟨1898270, by rfl⟩ : syracuseStep 2531027 = 3796541) B3796541
theorem B6749405 : Blo 1999435 6749405 := bstep (se 3 (by rfl) ⟨1265513, by rfl⟩ : syracuseStep 6749405 = 2531027) B2531027
theorem B4499603 : Blo 1999435 4499603 := bstep (se 1 (by rfl) ⟨3374702, by rfl⟩ : syracuseStep 4499603 = 6749405) B6749405
theorem B2999735 : Blo 1999435 2999735 := bstep (se 1 (by rfl) ⟨2249801, by rfl⟩ : syracuseStep 2999735 = 4499603) B4499603
theorem B1999823 : Blo 1999435 1999823 := bstep (se 1 (by rfl) ⟨1499867, by rfl⟩ : syracuseStep 1999823 = 2999735) B2999735
theorem B2999741 : Blo 1999435 2999741 := bbase (se 3 (by rfl) ⟨562451, by rfl⟩ : syracuseStep 2999741 = 1124903) (by norm_num)
theorem B1999827 : Blo 1999435 1999827 := bstep (se 1 (by rfl) ⟨1499870, by rfl⟩ : syracuseStep 1999827 = 2999741) B2999741
theorem B4499621 : Blo 1999435 4499621 := bbase (se 4 (by rfl) ⟨421839, by rfl⟩ : syracuseStep 4499621 = 843679) (by norm_num)
theorem B2999747 : Blo 1999435 2999747 := bstep (se 1 (by rfl) ⟨2249810, by rfl⟩ : syracuseStep 2999747 = 4499621) B4499621
theorem B1999831 : Blo 1999435 1999831 := bstep (se 1 (by rfl) ⟨1499873, by rfl⟩ : syracuseStep 1999831 = 2999747) B2999747
theorem B5062085 : Blo 1999435 5062085 := bbase (se 4 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 5062085 = 949141) (by norm_num)
theorem B3374723 : Blo 1999435 3374723 := bstep (se 1 (by rfl) ⟨2531042, by rfl⟩ : syracuseStep 3374723 = 5062085) B5062085
theorem B2249815 : Blo 1999435 2249815 := bstep (se 1 (by rfl) ⟨1687361, by rfl⟩ : syracuseStep 2249815 = 3374723) B3374723
theorem B2999753 : Blo 1999435 2999753 := bstep (se 2 (by rfl) ⟨1124907, by rfl⟩ : syracuseStep 2999753 = 2249815) B2249815
theorem B1999835 : Blo 1999435 1999835 := bstep (se 1 (by rfl) ⟨1499876, by rfl⟩ : syracuseStep 1999835 = 2999753) B2999753
theorem B2027125 : Blo 1999435 2027125 := bbase (se 5 (by rfl) ⟨95021, by rfl⟩ : syracuseStep 2027125 = 190043) (by norm_num)
theorem B10811333 : Blo 1999435 10811333 := bstep (se 4 (by rfl) ⟨1013562, by rfl⟩ : syracuseStep 10811333 = 2027125) B2027125
theorem B7207555 : Blo 1999435 7207555 := bstep (se 1 (by rfl) ⟨5405666, by rfl⟩ : syracuseStep 7207555 = 10811333) B10811333
theorem B9610073 : Blo 1999435 9610073 := bstep (se 2 (by rfl) ⟨3603777, by rfl⟩ : syracuseStep 9610073 = 7207555) B7207555
theorem B6406715 : Blo 1999435 6406715 := bstep (se 1 (by rfl) ⟨4805036, by rfl⟩ : syracuseStep 6406715 = 9610073) B9610073
theorem B4271143 : Blo 1999435 4271143 := bstep (se 1 (by rfl) ⟨3203357, by rfl⟩ : syracuseStep 4271143 = 6406715) B6406715
theorem B5694857 : Blo 1999435 5694857 := bstep (se 2 (by rfl) ⟨2135571, by rfl⟩ : syracuseStep 5694857 = 4271143) B4271143
theorem B3796571 : Blo 1999435 3796571 := bstep (se 1 (by rfl) ⟨2847428, by rfl⟩ : syracuseStep 3796571 = 5694857) B5694857
theorem B10124189 : Blo 1999435 10124189 := bstep (se 3 (by rfl) ⟨1898285, by rfl⟩ : syracuseStep 10124189 = 3796571) B3796571
theorem B6749459 : Blo 1999435 6749459 := bstep (se 1 (by rfl) ⟨5062094, by rfl⟩ : syracuseStep 6749459 = 10124189) B10124189
theorem B4499639 : Blo 1999435 4499639 := bstep (se 1 (by rfl) ⟨3374729, by rfl⟩ : syracuseStep 4499639 = 6749459) B6749459
theorem B2999759 : Blo 1999435 2999759 := bstep (se 1 (by rfl) ⟨2249819, by rfl⟩ : syracuseStep 2999759 = 4499639) B4499639
theorem B1999839 : Blo 1999435 1999839 := bstep (se 1 (by rfl) ⟨1499879, by rfl⟩ : syracuseStep 1999839 = 2999759) B2999759
theorem B2999765 : Blo 1999435 2999765 := bbase (se 7 (by rfl) ⟨35153, by rfl⟩ : syracuseStep 2999765 = 70307) (by norm_num)
theorem B1999843 : Blo 1999435 1999843 := bstep (se 1 (by rfl) ⟨1499882, by rfl⟩ : syracuseStep 1999843 = 2999765) B2999765
theorem B7593173 : Blo 1999435 7593173 := bbase (se 7 (by rfl) ⟨88982, by rfl⟩ : syracuseStep 7593173 = 177965) (by norm_num)
theorem B5062115 : Blo 1999435 5062115 := bstep (se 1 (by rfl) ⟨3796586, by rfl⟩ : syracuseStep 5062115 = 7593173) B7593173
theorem B3374743 : Blo 1999435 3374743 := bstep (se 1 (by rfl) ⟨2531057, by rfl⟩ : syracuseStep 3374743 = 5062115) B5062115
theorem B4499657 : Blo 1999435 4499657 := bstep (se 2 (by rfl) ⟨1687371, by rfl⟩ : syracuseStep 4499657 = 3374743) B3374743
theorem B2999771 : Blo 1999435 2999771 := bstep (se 1 (by rfl) ⟨2249828, by rfl⟩ : syracuseStep 2999771 = 4499657) B4499657
theorem B1999847 : Blo 1999435 1999847 := bstep (se 1 (by rfl) ⟨1499885, by rfl⟩ : syracuseStep 1999847 = 2999771) B2999771
theorem B2249833 : Blo 1999435 2249833 := bbase (se 2 (by rfl) ⟨843687, by rfl⟩ : syracuseStep 2249833 = 1687375) (by norm_num)
theorem B2999777 : Blo 1999435 2999777 := bstep (se 2 (by rfl) ⟨1124916, by rfl⟩ : syracuseStep 2999777 = 2249833) B2249833
theorem B1999851 : Blo 1999435 1999851 := bstep (se 1 (by rfl) ⟨1499888, by rfl⟩ : syracuseStep 1999851 = 2999777) B2999777
theorem B4561069 : Blo 1999435 4561069 := bbase (se 3 (by rfl) ⟨855200, by rfl⟩ : syracuseStep 4561069 = 1710401) (by norm_num)
theorem B6081425 : Blo 1999435 6081425 := bstep (se 2 (by rfl) ⟨2280534, by rfl⟩ : syracuseStep 6081425 = 4561069) B4561069
theorem B4054283 : Blo 1999435 4054283 := bstep (se 1 (by rfl) ⟨3040712, by rfl⟩ : syracuseStep 4054283 = 6081425) B6081425
theorem B2702855 : Blo 1999435 2702855 := bstep (se 1 (by rfl) ⟨2027141, by rfl⟩ : syracuseStep 2702855 = 4054283) B4054283
theorem B7207613 : Blo 1999435 7207613 := bstep (se 3 (by rfl) ⟨1351427, by rfl⟩ : syracuseStep 7207613 = 2702855) B2702855
theorem B4805075 : Blo 1999435 4805075 := bstep (se 1 (by rfl) ⟨3603806, by rfl⟩ : syracuseStep 4805075 = 7207613) B7207613
theorem B3203383 : Blo 1999435 3203383 := bstep (se 1 (by rfl) ⟨2402537, by rfl⟩ : syracuseStep 3203383 = 4805075) B4805075
theorem B4271177 : Blo 1999435 4271177 := bstep (se 2 (by rfl) ⟨1601691, by rfl⟩ : syracuseStep 4271177 = 3203383) B3203383
theorem B11389805 : Blo 1999435 11389805 := bstep (se 3 (by rfl) ⟨2135588, by rfl⟩ : syracuseStep 11389805 = 4271177) B4271177
theorem B7593203 : Blo 1999435 7593203 := bstep (se 1 (by rfl) ⟨5694902, by rfl⟩ : syracuseStep 7593203 = 11389805) B11389805
theorem B5062135 : Blo 1999435 5062135 := bstep (se 1 (by rfl) ⟨3796601, by rfl⟩ : syracuseStep 5062135 = 7593203) B7593203
theorem B6749513 : Blo 1999435 6749513 := bstep (se 2 (by rfl) ⟨2531067, by rfl⟩ : syracuseStep 6749513 = 5062135) B5062135
theorem B4499675 : Blo 1999435 4499675 := bstep (se 1 (by rfl) ⟨3374756, by rfl⟩ : syracuseStep 4499675 = 6749513) B6749513
theorem B2999783 : Blo 1999435 2999783 := bstep (se 1 (by rfl) ⟨2249837, by rfl⟩ : syracuseStep 2999783 = 4499675) B4499675
theorem B1999855 : Blo 1999435 1999855 := bstep (se 1 (by rfl) ⟨1499891, by rfl⟩ : syracuseStep 1999855 = 2999783) B2999783
theorem B2999789 : Blo 1999435 2999789 := bbase (se 3 (by rfl) ⟨562460, by rfl⟩ : syracuseStep 2999789 = 1124921) (by norm_num)
theorem B1999859 : Blo 1999435 1999859 := bstep (se 1 (by rfl) ⟨1499894, by rfl⟩ : syracuseStep 1999859 = 2999789) B2999789
theorem B4499693 : Blo 1999435 4499693 := bbase (se 3 (by rfl) ⟨843692, by rfl⟩ : syracuseStep 4499693 = 1687385) (by norm_num)
theorem B2999795 : Blo 1999435 2999795 := bstep (se 1 (by rfl) ⟨2249846, by rfl⟩ : syracuseStep 2999795 = 4499693) B4499693
theorem B1999863 : Blo 1999435 1999863 := bstep (se 1 (by rfl) ⟨1499897, by rfl⟩ : syracuseStep 1999863 = 2999795) B2999795
theorem B2847469 : Blo 1999435 2847469 := bbase (se 3 (by rfl) ⟨533900, by rfl⟩ : syracuseStep 2847469 = 1067801) (by norm_num)
theorem B3796625 : Blo 1999435 3796625 := bstep (se 2 (by rfl) ⟨1423734, by rfl⟩ : syracuseStep 3796625 = 2847469) B2847469
theorem B2531083 : Blo 1999435 2531083 := bstep (se 1 (by rfl) ⟨1898312, by rfl⟩ : syracuseStep 2531083 = 3796625) B3796625
theorem B3374777 : Blo 1999435 3374777 := bstep (se 2 (by rfl) ⟨1265541, by rfl⟩ : syracuseStep 3374777 = 2531083) B2531083
theorem B2249851 : Blo 1999435 2249851 := bstep (se 1 (by rfl) ⟨1687388, by rfl⟩ : syracuseStep 2249851 = 3374777) B3374777
theorem B2999801 : Blo 1999435 2999801 := bstep (se 2 (by rfl) ⟨1124925, by rfl⟩ : syracuseStep 2999801 = 2249851) B2249851
theorem B1999867 : Blo 1999435 1999867 := bstep (se 1 (by rfl) ⟨1499900, by rfl⟩ : syracuseStep 1999867 = 2999801) B2999801
theorem B4109629 : Blo 1999435 4109629 := bbase (se 3 (by rfl) ⟨770555, by rfl⟩ : syracuseStep 4109629 = 1541111) (by norm_num)
theorem B5479505 : Blo 1999435 5479505 := bstep (se 2 (by rfl) ⟨2054814, by rfl⟩ : syracuseStep 5479505 = 4109629) B4109629
theorem B3653003 : Blo 1999435 3653003 := bstep (se 1 (by rfl) ⟨2739752, by rfl⟩ : syracuseStep 3653003 = 5479505) B5479505
theorem B9741341 : Blo 1999435 9741341 := bstep (se 3 (by rfl) ⟨1826501, by rfl⟩ : syracuseStep 9741341 = 3653003) B3653003
theorem B25976909 : Blo 1999435 25976909 := bstep (se 3 (by rfl) ⟨4870670, by rfl⟩ : syracuseStep 25976909 = 9741341) B9741341
theorem B69271757 : Blo 1999435 69271757 := bstep (se 3 (by rfl) ⟨12988454, by rfl⟩ : syracuseStep 69271757 = 25976909) B25976909
theorem B46181171 : Blo 1999435 46181171 := bstep (se 1 (by rfl) ⟨34635878, by rfl⟩ : syracuseStep 46181171 = 69271757) B69271757
theorem B30787447 : Blo 1999435 30787447 := bstep (se 1 (by rfl) ⟨23090585, by rfl⟩ : syracuseStep 30787447 = 46181171) B46181171
theorem B41049929 : Blo 1999435 41049929 := bstep (se 2 (by rfl) ⟨15393723, by rfl⟩ : syracuseStep 41049929 = 30787447) B30787447
theorem B27366619 : Blo 1999435 27366619 := bstep (se 1 (by rfl) ⟨20524964, by rfl⟩ : syracuseStep 27366619 = 41049929) B41049929
theorem B36488825 : Blo 1999435 36488825 := bstep (se 2 (by rfl) ⟨13683309, by rfl⟩ : syracuseStep 36488825 = 27366619) B27366619
theorem B24325883 : Blo 1999435 24325883 := bstep (se 1 (by rfl) ⟨18244412, by rfl⟩ : syracuseStep 24325883 = 36488825) B36488825
theorem B16217255 : Blo 1999435 16217255 := bstep (se 1 (by rfl) ⟨12162941, by rfl⟩ : syracuseStep 16217255 = 24325883) B24325883
theorem B10811503 : Blo 1999435 10811503 := bstep (se 1 (by rfl) ⟨8108627, by rfl⟩ : syracuseStep 10811503 = 16217255) B16217255
theorem B14415337 : Blo 1999435 14415337 := bstep (se 2 (by rfl) ⟨5405751, by rfl⟩ : syracuseStep 14415337 = 10811503) B10811503
theorem B76881797 : Blo 1999435 76881797 := bstep (se 4 (by rfl) ⟨7207668, by rfl⟩ : syracuseStep 76881797 = 14415337) B14415337
theorem B51254531 : Blo 1999435 51254531 := bstep (se 1 (by rfl) ⟨38440898, by rfl⟩ : syracuseStep 51254531 = 76881797) B76881797
theorem B34169687 : Blo 1999435 34169687 := bstep (se 1 (by rfl) ⟨25627265, by rfl⟩ : syracuseStep 34169687 = 51254531) B51254531
theorem B22779791 : Blo 1999435 22779791 := bstep (se 1 (by rfl) ⟨17084843, by rfl⟩ : syracuseStep 22779791 = 34169687) B34169687
theorem B15186527 : Blo 1999435 15186527 := bstep (se 1 (by rfl) ⟨11389895, by rfl⟩ : syracuseStep 15186527 = 22779791) B22779791
theorem B10124351 : Blo 1999435 10124351 := bstep (se 1 (by rfl) ⟨7593263, by rfl⟩ : syracuseStep 10124351 = 15186527) B15186527
theorem B6749567 : Blo 1999435 6749567 := bstep (se 1 (by rfl) ⟨5062175, by rfl⟩ : syracuseStep 6749567 = 10124351) B10124351
theorem B4499711 : Blo 1999435 4499711 := bstep (se 1 (by rfl) ⟨3374783, by rfl⟩ : syracuseStep 4499711 = 6749567) B6749567
theorem B2999807 : Blo 1999435 2999807 := bstep (se 1 (by rfl) ⟨2249855, by rfl⟩ : syracuseStep 2999807 = 4499711) B4499711
theorem B1999871 : Blo 1999435 1999871 := bstep (se 1 (by rfl) ⟨1499903, by rfl⟩ : syracuseStep 1999871 = 2999807) B2999807
theorem B2999813 : Blo 1999435 2999813 := bbase (se 4 (by rfl) ⟨281232, by rfl⟩ : syracuseStep 2999813 = 562465) (by norm_num)
theorem B1999875 : Blo 1999435 1999875 := bstep (se 1 (by rfl) ⟨1499906, by rfl⟩ : syracuseStep 1999875 = 2999813) B2999813
theorem B3374797 : Blo 1999435 3374797 := bbase (se 3 (by rfl) ⟨632774, by rfl⟩ : syracuseStep 3374797 = 1265549) (by norm_num)
theorem B4499729 : Blo 1999435 4499729 := bstep (se 2 (by rfl) ⟨1687398, by rfl⟩ : syracuseStep 4499729 = 3374797) B3374797
theorem B2999819 : Blo 1999435 2999819 := bstep (se 1 (by rfl) ⟨2249864, by rfl⟩ : syracuseStep 2999819 = 4499729) B4499729
theorem B1999879 : Blo 1999435 1999879 := bstep (se 1 (by rfl) ⟨1499909, by rfl⟩ : syracuseStep 1999879 = 2999819) B2999819
theorem B2249869 : Blo 1999435 2249869 := bbase (se 3 (by rfl) ⟨421850, by rfl⟩ : syracuseStep 2249869 = 843701) (by norm_num)
theorem B2999825 : Blo 1999435 2999825 := bstep (se 2 (by rfl) ⟨1124934, by rfl⟩ : syracuseStep 2999825 = 2249869) B2249869
theorem B1999883 : Blo 1999435 1999883 := bstep (se 1 (by rfl) ⟨1499912, by rfl⟩ : syracuseStep 1999883 = 2999825) B2999825
theorem B6749621 : Blo 1999435 6749621 := bbase (se 5 (by rfl) ⟨316388, by rfl⟩ : syracuseStep 6749621 = 632777) (by norm_num)
theorem B4499747 : Blo 1999435 4499747 := bstep (se 1 (by rfl) ⟨3374810, by rfl⟩ : syracuseStep 4499747 = 6749621) B6749621
theorem B2999831 : Blo 1999435 2999831 := bstep (se 1 (by rfl) ⟨2249873, by rfl⟩ : syracuseStep 2999831 = 4499747) B4499747
theorem B1999887 : Blo 1999435 1999887 := bstep (se 1 (by rfl) ⟨1499915, by rfl⟩ : syracuseStep 1999887 = 2999831) B2999831
theorem B2999837 : Blo 1999435 2999837 := bbase (se 3 (by rfl) ⟨562469, by rfl⟩ : syracuseStep 2999837 = 1124939) (by norm_num)
theorem B1999891 : Blo 1999435 1999891 := bstep (se 1 (by rfl) ⟨1499918, by rfl⟩ : syracuseStep 1999891 = 2999837) B2999837
theorem B4499765 : Blo 1999435 4499765 := bbase (se 5 (by rfl) ⟨210926, by rfl⟩ : syracuseStep 4499765 = 421853) (by norm_num)
theorem B2999843 : Blo 1999435 2999843 := bstep (se 1 (by rfl) ⟨2249882, by rfl⟩ : syracuseStep 2999843 = 4499765) B4499765
theorem B1999895 : Blo 1999435 1999895 := bstep (se 1 (by rfl) ⟨1499921, by rfl⟩ : syracuseStep 1999895 = 2999843) B2999843
theorem B10262629 : Blo 1999435 10262629 := bbase (se 4 (by rfl) ⟨962121, by rfl⟩ : syracuseStep 10262629 = 1924243) (by norm_num)
theorem B13683505 : Blo 1999435 13683505 := bstep (se 2 (by rfl) ⟨5131314, by rfl⟩ : syracuseStep 13683505 = 10262629) B10262629
theorem B18244673 : Blo 1999435 18244673 := bstep (se 2 (by rfl) ⟨6841752, by rfl⟩ : syracuseStep 18244673 = 13683505) B13683505
theorem B12163115 : Blo 1999435 12163115 := bstep (se 1 (by rfl) ⟨9122336, by rfl⟩ : syracuseStep 12163115 = 18244673) B18244673
theorem B8108743 : Blo 1999435 8108743 := bstep (se 1 (by rfl) ⟨6081557, by rfl⟩ : syracuseStep 8108743 = 12163115) B12163115
theorem B10811657 : Blo 1999435 10811657 := bstep (se 2 (by rfl) ⟨4054371, by rfl⟩ : syracuseStep 10811657 = 8108743) B8108743
theorem B28831085 : Blo 1999435 28831085 := bstep (se 3 (by rfl) ⟨5405828, by rfl⟩ : syracuseStep 28831085 = 10811657) B10811657
theorem B19220723 : Blo 1999435 19220723 := bstep (se 1 (by rfl) ⟨14415542, by rfl⟩ : syracuseStep 19220723 = 28831085) B28831085
theorem B12813815 : Blo 1999435 12813815 := bstep (se 1 (by rfl) ⟨9610361, by rfl⟩ : syracuseStep 12813815 = 19220723) B19220723
theorem B8542543 : Blo 1999435 8542543 := bstep (se 1 (by rfl) ⟨6406907, by rfl⟩ : syracuseStep 8542543 = 12813815) B12813815
theorem B11390057 : Blo 1999435 11390057 := bstep (se 2 (by rfl) ⟨4271271, by rfl⟩ : syracuseStep 11390057 = 8542543) B8542543
theorem B7593371 : Blo 1999435 7593371 := bstep (se 1 (by rfl) ⟨5695028, by rfl⟩ : syracuseStep 7593371 = 11390057) B11390057
theorem B5062247 : Blo 1999435 5062247 := bstep (se 1 (by rfl) ⟨3796685, by rfl⟩ : syracuseStep 5062247 = 7593371) B7593371
theorem B3374831 : Blo 1999435 3374831 := bstep (se 1 (by rfl) ⟨2531123, by rfl⟩ : syracuseStep 3374831 = 5062247) B5062247
theorem B2249887 : Blo 1999435 2249887 := bstep (se 1 (by rfl) ⟨1687415, by rfl⟩ : syracuseStep 2249887 = 3374831) B3374831
theorem B2999849 : Blo 1999435 2999849 := bstep (se 2 (by rfl) ⟨1124943, by rfl⟩ : syracuseStep 2999849 = 2249887) B2249887
theorem B1999899 : Blo 1999435 1999899 := bstep (se 1 (by rfl) ⟨1499924, by rfl⟩ : syracuseStep 1999899 = 2999849) B2999849
theorem B5131325 : Blo 1999435 5131325 := bbase (se 3 (by rfl) ⟨962123, by rfl⟩ : syracuseStep 5131325 = 1924247) (by norm_num)
theorem B3420883 : Blo 1999435 3420883 := bstep (se 1 (by rfl) ⟨2565662, by rfl⟩ : syracuseStep 3420883 = 5131325) B5131325
theorem B4561177 : Blo 1999435 4561177 := bstep (se 2 (by rfl) ⟨1710441, by rfl⟩ : syracuseStep 4561177 = 3420883) B3420883
theorem B6081569 : Blo 1999435 6081569 := bstep (se 2 (by rfl) ⟨2280588, by rfl⟩ : syracuseStep 6081569 = 4561177) B4561177
theorem B4054379 : Blo 1999435 4054379 := bstep (se 1 (by rfl) ⟨3040784, by rfl⟩ : syracuseStep 4054379 = 6081569) B6081569
theorem B43246709 : Blo 1999435 43246709 := bstep (se 5 (by rfl) ⟨2027189, by rfl⟩ : syracuseStep 43246709 = 4054379) B4054379
theorem B28831139 : Blo 1999435 28831139 := bstep (se 1 (by rfl) ⟨21623354, by rfl⟩ : syracuseStep 28831139 = 43246709) B43246709
theorem B19220759 : Blo 1999435 19220759 := bstep (se 1 (by rfl) ⟨14415569, by rfl⟩ : syracuseStep 19220759 = 28831139) B28831139
theorem B12813839 : Blo 1999435 12813839 := bstep (se 1 (by rfl) ⟨9610379, by rfl⟩ : syracuseStep 12813839 = 19220759) B19220759
theorem B8542559 : Blo 1999435 8542559 := bstep (se 1 (by rfl) ⟨6406919, by rfl⟩ : syracuseStep 8542559 = 12813839) B12813839
theorem B5695039 : Blo 1999435 5695039 := bstep (se 1 (by rfl) ⟨4271279, by rfl⟩ : syracuseStep 5695039 = 8542559) B8542559
theorem B7593385 : Blo 1999435 7593385 := bstep (se 2 (by rfl) ⟨2847519, by rfl⟩ : syracuseStep 7593385 = 5695039) B5695039
theorem B10124513 : Blo 1999435 10124513 := bstep (se 2 (by rfl) ⟨3796692, by rfl⟩ : syracuseStep 10124513 = 7593385) B7593385
theorem B6749675 : Blo 1999435 6749675 := bstep (se 1 (by rfl) ⟨5062256, by rfl⟩ : syracuseStep 6749675 = 10124513) B10124513
theorem B4499783 : Blo 1999435 4499783 := bstep (se 1 (by rfl) ⟨3374837, by rfl⟩ : syracuseStep 4499783 = 6749675) B6749675
theorem B2999855 : Blo 1999435 2999855 := bstep (se 1 (by rfl) ⟨2249891, by rfl⟩ : syracuseStep 2999855 = 4499783) B4499783
theorem B1999903 : Blo 1999435 1999903 := bstep (se 1 (by rfl) ⟨1499927, by rfl⟩ : syracuseStep 1999903 = 2999855) B2999855
theorem B2999861 : Blo 1999435 2999861 := bbase (se 5 (by rfl) ⟨140618, by rfl⟩ : syracuseStep 2999861 = 281237) (by norm_num)
theorem B1999907 : Blo 1999435 1999907 := bstep (se 1 (by rfl) ⟨1499930, by rfl⟩ : syracuseStep 1999907 = 2999861) B2999861
theorem B5062277 : Blo 1999435 5062277 := bbase (se 4 (by rfl) ⟨474588, by rfl⟩ : syracuseStep 5062277 = 949177) (by norm_num)
theorem B3374851 : Blo 1999435 3374851 := bstep (se 1 (by rfl) ⟨2531138, by rfl⟩ : syracuseStep 3374851 = 5062277) B5062277
theorem B4499801 : Blo 1999435 4499801 := bstep (se 2 (by rfl) ⟨1687425, by rfl⟩ : syracuseStep 4499801 = 3374851) B3374851
theorem B2999867 : Blo 1999435 2999867 := bstep (se 1 (by rfl) ⟨2249900, by rfl⟩ : syracuseStep 2999867 = 4499801) B4499801
theorem B1999911 : Blo 1999435 1999911 := bstep (se 1 (by rfl) ⟨1499933, by rfl⟩ : syracuseStep 1999911 = 2999867) B2999867
theorem B2249905 : Blo 1999435 2249905 := bbase (se 2 (by rfl) ⟨843714, by rfl⟩ : syracuseStep 2249905 = 1687429) (by norm_num)
theorem B2999873 : Blo 1999435 2999873 := bstep (se 2 (by rfl) ⟨1124952, by rfl⟩ : syracuseStep 2999873 = 2249905) B2249905
theorem B1999915 : Blo 1999435 1999915 := bstep (se 1 (by rfl) ⟨1499936, by rfl⟩ : syracuseStep 1999915 = 2999873) B2999873
theorem B2135657 : Blo 1999435 2135657 := bbase (se 2 (by rfl) ⟨800871, by rfl⟩ : syracuseStep 2135657 = 1601743) (by norm_num)
theorem B5695085 : Blo 1999435 5695085 := bstep (se 3 (by rfl) ⟨1067828, by rfl⟩ : syracuseStep 5695085 = 2135657) B2135657
theorem B3796723 : Blo 1999435 3796723 := bstep (se 1 (by rfl) ⟨2847542, by rfl⟩ : syracuseStep 3796723 = 5695085) B5695085
theorem B5062297 : Blo 1999435 5062297 := bstep (se 2 (by rfl) ⟨1898361, by rfl⟩ : syracuseStep 5062297 = 3796723) B3796723
theorem B6749729 : Blo 1999435 6749729 := bstep (se 2 (by rfl) ⟨2531148, by rfl⟩ : syracuseStep 6749729 = 5062297) B5062297
theorem B4499819 : Blo 1999435 4499819 := bstep (se 1 (by rfl) ⟨3374864, by rfl⟩ : syracuseStep 4499819 = 6749729) B6749729
theorem B2999879 : Blo 1999435 2999879 := bstep (se 1 (by rfl) ⟨2249909, by rfl⟩ : syracuseStep 2999879 = 4499819) B4499819
theorem B1999919 : Blo 1999435 1999919 := bstep (se 1 (by rfl) ⟨1499939, by rfl⟩ : syracuseStep 1999919 = 2999879) B2999879
theorem B2999885 : Blo 1999435 2999885 := bbase (se 3 (by rfl) ⟨562478, by rfl⟩ : syracuseStep 2999885 = 1124957) (by norm_num)
theorem B1999923 : Blo 1999435 1999923 := bstep (se 1 (by rfl) ⟨1499942, by rfl⟩ : syracuseStep 1999923 = 2999885) B2999885
theorem B4499837 : Blo 1999435 4499837 := bbase (se 3 (by rfl) ⟨843719, by rfl⟩ : syracuseStep 4499837 = 1687439) (by norm_num)
theorem B2999891 : Blo 1999435 2999891 := bstep (se 1 (by rfl) ⟨2249918, by rfl⟩ : syracuseStep 2999891 = 4499837) B4499837
theorem B1999927 : Blo 1999435 1999927 := bstep (se 1 (by rfl) ⟨1499945, by rfl⟩ : syracuseStep 1999927 = 2999891) B2999891
theorem B3374885 : Blo 1999435 3374885 := bbase (se 4 (by rfl) ⟨316395, by rfl⟩ : syracuseStep 3374885 = 632791) (by norm_num)
theorem B2249923 : Blo 1999435 2249923 := bstep (se 1 (by rfl) ⟨1687442, by rfl⟩ : syracuseStep 2249923 = 3374885) B3374885
theorem B2999897 : Blo 1999435 2999897 := bstep (se 2 (by rfl) ⟨1124961, by rfl⟩ : syracuseStep 2999897 = 2249923) B2249923
theorem B1999931 : Blo 1999435 1999931 := bstep (se 1 (by rfl) ⟨1499948, by rfl⟩ : syracuseStep 1999931 = 2999897) B2999897
theorem B2847565 : Blo 1999435 2847565 := bbase (se 3 (by rfl) ⟨533918, by rfl⟩ : syracuseStep 2847565 = 1067837) (by norm_num)
theorem B15187013 : Blo 1999435 15187013 := bstep (se 4 (by rfl) ⟨1423782, by rfl⟩ : syracuseStep 15187013 = 2847565) B2847565
theorem B10124675 : Blo 1999435 10124675 := bstep (se 1 (by rfl) ⟨7593506, by rfl⟩ : syracuseStep 10124675 = 15187013) B15187013
theorem B6749783 : Blo 1999435 6749783 := bstep (se 1 (by rfl) ⟨5062337, by rfl⟩ : syracuseStep 6749783 = 10124675) B10124675
theorem B4499855 : Blo 1999435 4499855 := bstep (se 1 (by rfl) ⟨3374891, by rfl⟩ : syracuseStep 4499855 = 6749783) B6749783
theorem B2999903 : Blo 1999435 2999903 := bstep (se 1 (by rfl) ⟨2249927, by rfl⟩ : syracuseStep 2999903 = 4499855) B4499855
theorem B1999935 : Blo 1999435 1999935 := bstep (se 1 (by rfl) ⟨1499951, by rfl⟩ : syracuseStep 1999935 = 2999903) B2999903
theorem B2999909 : Blo 1999435 2999909 := bbase (se 4 (by rfl) ⟨281241, by rfl⟩ : syracuseStep 2999909 = 562483) (by norm_num)
theorem B1999939 : Blo 1999435 1999939 := bstep (se 1 (by rfl) ⟨1499954, by rfl⟩ : syracuseStep 1999939 = 2999909) B2999909
theorem B3203525 : Blo 1999435 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B2135683 : Blo 1999435 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B2847577 : Blo 1999435 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B3796769 : Blo 1999435 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B2531179 : Blo 1999435 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B3374905 : Blo 1999435 3374905 := bstep (se 2 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 3374905 = 2531179) B2531179
theorem B4499873 : Blo 1999435 4499873 := bstep (se 2 (by rfl) ⟨1687452, by rfl⟩ : syracuseStep 4499873 = 3374905) B3374905
theorem B2999915 : Blo 1999435 2999915 := bstep (se 1 (by rfl) ⟨2249936, by rfl⟩ : syracuseStep 2999915 = 4499873) B4499873
theorem B1999943 : Blo 1999435 1999943 := bstep (se 1 (by rfl) ⟨1499957, by rfl⟩ : syracuseStep 1999943 = 2999915) B2999915
theorem B2249941 : Blo 1999435 2249941 := bbase (se 7 (by rfl) ⟨26366, by rfl⟩ : syracuseStep 2249941 = 52733) (by norm_num)
theorem B2999921 : Blo 1999435 2999921 := bstep (se 2 (by rfl) ⟨1124970, by rfl⟩ : syracuseStep 2999921 = 2249941) B2249941
theorem B1999947 : Blo 1999435 1999947 := bstep (se 1 (by rfl) ⟨1499960, by rfl⟩ : syracuseStep 1999947 = 2999921) B2999921
theorem B2531189 : Blo 1999435 2531189 := bbase (se 5 (by rfl) ⟨118649, by rfl⟩ : syracuseStep 2531189 = 237299) (by norm_num)
theorem B6749837 : Blo 1999435 6749837 := bstep (se 3 (by rfl) ⟨1265594, by rfl⟩ : syracuseStep 6749837 = 2531189) B2531189
theorem B4499891 : Blo 1999435 4499891 := bstep (se 1 (by rfl) ⟨3374918, by rfl⟩ : syracuseStep 4499891 = 6749837) B6749837
theorem B2999927 : Blo 1999435 2999927 := bstep (se 1 (by rfl) ⟨2249945, by rfl⟩ : syracuseStep 2999927 = 4499891) B4499891
theorem B1999951 : Blo 1999435 1999951 := bstep (se 1 (by rfl) ⟨1499963, by rfl⟩ : syracuseStep 1999951 = 2999927) B2999927
theorem B2999933 : Blo 1999435 2999933 := bbase (se 3 (by rfl) ⟨562487, by rfl⟩ : syracuseStep 2999933 = 1124975) (by norm_num)
theorem B1999955 : Blo 1999435 1999955 := bstep (se 1 (by rfl) ⟨1499966, by rfl⟩ : syracuseStep 1999955 = 2999933) B2999933
theorem B4499909 : Blo 1999435 4499909 := bbase (se 4 (by rfl) ⟨421866, by rfl⟩ : syracuseStep 4499909 = 843733) (by norm_num)
theorem B2999939 : Blo 1999435 2999939 := bstep (se 1 (by rfl) ⟨2249954, by rfl⟩ : syracuseStep 2999939 = 4499909) B4499909
theorem B1999959 : Blo 1999435 1999959 := bstep (se 1 (by rfl) ⟨1499969, by rfl⟩ : syracuseStep 1999959 = 2999939) B2999939
theorem B3040877 : Blo 1999435 3040877 := bbase (se 3 (by rfl) ⟨570164, by rfl⟩ : syracuseStep 3040877 = 1140329) (by norm_num)
theorem B2027251 : Blo 1999435 2027251 := bstep (se 1 (by rfl) ⟨1520438, by rfl⟩ : syracuseStep 2027251 = 3040877) B3040877
theorem B10812005 : Blo 1999435 10812005 := bstep (se 4 (by rfl) ⟨1013625, by rfl⟩ : syracuseStep 10812005 = 2027251) B2027251
theorem B7208003 : Blo 1999435 7208003 := bstep (se 1 (by rfl) ⟨5406002, by rfl⟩ : syracuseStep 7208003 = 10812005) B10812005
theorem B4805335 : Blo 1999435 4805335 := bstep (se 1 (by rfl) ⟨3604001, by rfl⟩ : syracuseStep 4805335 = 7208003) B7208003
theorem B6407113 : Blo 1999435 6407113 := bstep (se 2 (by rfl) ⟨2402667, by rfl⟩ : syracuseStep 6407113 = 4805335) B4805335
theorem B8542817 : Blo 1999435 8542817 := bstep (se 2 (by rfl) ⟨3203556, by rfl⟩ : syracuseStep 8542817 = 6407113) B6407113
theorem B5695211 : Blo 1999435 5695211 := bstep (se 1 (by rfl) ⟨4271408, by rfl⟩ : syracuseStep 5695211 = 8542817) B8542817
theorem B3796807 : Blo 1999435 3796807 := bstep (se 1 (by rfl) ⟨2847605, by rfl⟩ : syracuseStep 3796807 = 5695211) B5695211
theorem B5062409 : Blo 1999435 5062409 := bstep (se 2 (by rfl) ⟨1898403, by rfl⟩ : syracuseStep 5062409 = 3796807) B3796807
theorem B3374939 : Blo 1999435 3374939 := bstep (se 1 (by rfl) ⟨2531204, by rfl⟩ : syracuseStep 3374939 = 5062409) B5062409
theorem B2249959 : Blo 1999435 2249959 := bstep (se 1 (by rfl) ⟨1687469, by rfl⟩ : syracuseStep 2249959 = 3374939) B3374939
theorem B2999945 : Blo 1999435 2999945 := bstep (se 2 (by rfl) ⟨1124979, by rfl⟩ : syracuseStep 2999945 = 2249959) B2249959
theorem B1999963 : Blo 1999435 1999963 := bstep (se 1 (by rfl) ⟨1499972, by rfl⟩ : syracuseStep 1999963 = 2999945) B2999945
theorem B10124837 : Blo 1999435 10124837 := bbase (se 4 (by rfl) ⟨949203, by rfl⟩ : syracuseStep 10124837 = 1898407) (by norm_num)
theorem B6749891 : Blo 1999435 6749891 := bstep (se 1 (by rfl) ⟨5062418, by rfl⟩ : syracuseStep 6749891 = 10124837) B10124837
theorem B4499927 : Blo 1999435 4499927 := bstep (se 1 (by rfl) ⟨3374945, by rfl⟩ : syracuseStep 4499927 = 6749891) B6749891
theorem B2999951 : Blo 1999435 2999951 := bstep (se 1 (by rfl) ⟨2249963, by rfl⟩ : syracuseStep 2999951 = 4499927) B4499927
theorem B1999967 : Blo 1999435 1999967 := bstep (se 1 (by rfl) ⟨1499975, by rfl⟩ : syracuseStep 1999967 = 2999951) B2999951
theorem B2999957 : Blo 1999435 2999957 := bbase (se 6 (by rfl) ⟨70311, by rfl⟩ : syracuseStep 2999957 = 140623) (by norm_num)
theorem B1999971 : Blo 1999435 1999971 := bstep (se 1 (by rfl) ⟨1499978, by rfl⟩ : syracuseStep 1999971 = 2999957) B2999957
theorem B3291589 : Blo 1999435 3291589 := bbase (se 4 (by rfl) ⟨308586, by rfl⟩ : syracuseStep 3291589 = 617173) (by norm_num)
theorem B4388785 : Blo 1999435 4388785 := bstep (se 2 (by rfl) ⟨1645794, by rfl⟩ : syracuseStep 4388785 = 3291589) B3291589
theorem B93627413 : Blo 1999435 93627413 := bstep (se 6 (by rfl) ⟨2194392, by rfl⟩ : syracuseStep 93627413 = 4388785) B4388785
theorem B62418275 : Blo 1999435 62418275 := bstep (se 1 (by rfl) ⟨46813706, by rfl⟩ : syracuseStep 62418275 = 93627413) B93627413
theorem B41612183 : Blo 1999435 41612183 := bstep (se 1 (by rfl) ⟨31209137, by rfl⟩ : syracuseStep 41612183 = 62418275) B62418275
theorem B27741455 : Blo 1999435 27741455 := bstep (se 1 (by rfl) ⟨20806091, by rfl⟩ : syracuseStep 27741455 = 41612183) B41612183
theorem B18494303 : Blo 1999435 18494303 := bstep (se 1 (by rfl) ⟨13870727, by rfl⟩ : syracuseStep 18494303 = 27741455) B27741455
theorem B49318141 : Blo 1999435 49318141 := bstep (se 3 (by rfl) ⟨9247151, by rfl⟩ : syracuseStep 49318141 = 18494303) B18494303
theorem B65757521 : Blo 1999435 65757521 := bstep (se 2 (by rfl) ⟨24659070, by rfl⟩ : syracuseStep 65757521 = 49318141) B49318141
theorem B43838347 : Blo 1999435 43838347 := bstep (se 1 (by rfl) ⟨32878760, by rfl⟩ : syracuseStep 43838347 = 65757521) B65757521
theorem B58451129 : Blo 1999435 58451129 := bstep (se 2 (by rfl) ⟨21919173, by rfl⟩ : syracuseStep 58451129 = 43838347) B43838347
theorem B38967419 : Blo 1999435 38967419 := bstep (se 1 (by rfl) ⟨29225564, by rfl⟩ : syracuseStep 38967419 = 58451129) B58451129
theorem B25978279 : Blo 1999435 25978279 := bstep (se 1 (by rfl) ⟨19483709, by rfl⟩ : syracuseStep 25978279 = 38967419) B38967419
theorem B34637705 : Blo 1999435 34637705 := bstep (se 2 (by rfl) ⟨12989139, by rfl⟩ : syracuseStep 34637705 = 25978279) B25978279
theorem B23091803 : Blo 1999435 23091803 := bstep (se 1 (by rfl) ⟨17318852, by rfl⟩ : syracuseStep 23091803 = 34637705) B34637705
theorem B15394535 : Blo 1999435 15394535 := bstep (se 1 (by rfl) ⟨11545901, by rfl⟩ : syracuseStep 15394535 = 23091803) B23091803
theorem B10263023 : Blo 1999435 10263023 := bstep (se 1 (by rfl) ⟨7697267, by rfl⟩ : syracuseStep 10263023 = 15394535) B15394535
theorem B6842015 : Blo 1999435 6842015 := bstep (se 1 (by rfl) ⟨5131511, by rfl⟩ : syracuseStep 6842015 = 10263023) B10263023
theorem B4561343 : Blo 1999435 4561343 := bstep (se 1 (by rfl) ⟨3421007, by rfl⟩ : syracuseStep 4561343 = 6842015) B6842015
theorem B3040895 : Blo 1999435 3040895 := bstep (se 1 (by rfl) ⟨2280671, by rfl⟩ : syracuseStep 3040895 = 4561343) B4561343
theorem B2027263 : Blo 1999435 2027263 := bstep (se 1 (by rfl) ⟨1520447, by rfl⟩ : syracuseStep 2027263 = 3040895) B3040895
theorem B2703017 : Blo 1999435 2703017 := bstep (se 2 (by rfl) ⟨1013631, by rfl⟩ : syracuseStep 2703017 = 2027263) B2027263
theorem B7208045 : Blo 1999435 7208045 := bstep (se 3 (by rfl) ⟨1351508, by rfl⟩ : syracuseStep 7208045 = 2703017) B2703017
theorem B4805363 : Blo 1999435 4805363 := bstep (se 1 (by rfl) ⟨3604022, by rfl⟩ : syracuseStep 4805363 = 7208045) B7208045
theorem B12814301 : Blo 1999435 12814301 := bstep (se 3 (by rfl) ⟨2402681, by rfl⟩ : syracuseStep 12814301 = 4805363) B4805363
theorem B8542867 : Blo 1999435 8542867 := bstep (se 1 (by rfl) ⟨6407150, by rfl⟩ : syracuseStep 8542867 = 12814301) B12814301
theorem B11390489 : Blo 1999435 11390489 := bstep (se 2 (by rfl) ⟨4271433, by rfl⟩ : syracuseStep 11390489 = 8542867) B8542867
theorem B7593659 : Blo 1999435 7593659 := bstep (se 1 (by rfl) ⟨5695244, by rfl⟩ : syracuseStep 7593659 = 11390489) B11390489
theorem B5062439 : Blo 1999435 5062439 := bstep (se 1 (by rfl) ⟨3796829, by rfl⟩ : syracuseStep 5062439 = 7593659) B7593659
theorem B3374959 : Blo 1999435 3374959 := bstep (se 1 (by rfl) ⟨2531219, by rfl⟩ : syracuseStep 3374959 = 5062439) B5062439
theorem B4499945 : Blo 1999435 4499945 := bstep (se 2 (by rfl) ⟨1687479, by rfl⟩ : syracuseStep 4499945 = 3374959) B3374959
theorem B2999963 : Blo 1999435 2999963 := bstep (se 1 (by rfl) ⟨2249972, by rfl⟩ : syracuseStep 2999963 = 4499945) B4499945
theorem B1999975 : Blo 1999435 1999975 := bstep (se 1 (by rfl) ⟨1499981, by rfl⟩ : syracuseStep 1999975 = 2999963) B2999963
theorem B2249977 : Blo 1999435 2249977 := bbase (se 2 (by rfl) ⟨843741, by rfl⟩ : syracuseStep 2249977 = 1687483) (by norm_num)
theorem B2999969 : Blo 1999435 2999969 := bstep (se 2 (by rfl) ⟨1124988, by rfl⟩ : syracuseStep 2999969 = 2249977) B2249977
theorem B1999979 : Blo 1999435 1999979 := bstep (se 1 (by rfl) ⟨1499984, by rfl⟩ : syracuseStep 1999979 = 2999969) B2999969
theorem B8542901 : Blo 1999435 8542901 := bbase (se 5 (by rfl) ⟨400448, by rfl⟩ : syracuseStep 8542901 = 800897) (by norm_num)
theorem B5695267 : Blo 1999435 5695267 := bstep (se 1 (by rfl) ⟨4271450, by rfl⟩ : syracuseStep 5695267 = 8542901) B8542901
theorem B7593689 : Blo 1999435 7593689 := bstep (se 2 (by rfl) ⟨2847633, by rfl⟩ : syracuseStep 7593689 = 5695267) B5695267
theorem B5062459 : Blo 1999435 5062459 := bstep (se 1 (by rfl) ⟨3796844, by rfl⟩ : syracuseStep 5062459 = 7593689) B7593689
theorem B6749945 : Blo 1999435 6749945 := bstep (se 2 (by rfl) ⟨2531229, by rfl⟩ : syracuseStep 6749945 = 5062459) B5062459
theorem B4499963 : Blo 1999435 4499963 := bstep (se 1 (by rfl) ⟨3374972, by rfl⟩ : syracuseStep 4499963 = 6749945) B6749945
theorem B2999975 : Blo 1999435 2999975 := bstep (se 1 (by rfl) ⟨2249981, by rfl⟩ : syracuseStep 2999975 = 4499963) B4499963
theorem B1999983 : Blo 1999435 1999983 := bstep (se 1 (by rfl) ⟨1499987, by rfl⟩ : syracuseStep 1999983 = 2999975) B2999975
theorem B2999981 : Blo 1999435 2999981 := bbase (se 3 (by rfl) ⟨562496, by rfl⟩ : syracuseStep 2999981 = 1124993) (by norm_num)
theorem B1999987 : Blo 1999435 1999987 := bstep (se 1 (by rfl) ⟨1499990, by rfl⟩ : syracuseStep 1999987 = 2999981) B2999981
theorem B4499981 : Blo 1999435 4499981 := bbase (se 3 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 4499981 = 1687493) (by norm_num)
theorem B2999987 : Blo 1999435 2999987 := bstep (se 1 (by rfl) ⟨2249990, by rfl⟩ : syracuseStep 2999987 = 4499981) B4499981
theorem B1999991 : Blo 1999435 1999991 := bstep (se 1 (by rfl) ⟨1499993, by rfl⟩ : syracuseStep 1999991 = 2999987) B2999987
theorem B2531245 : Blo 1999435 2531245 := bbase (se 3 (by rfl) ⟨474608, by rfl⟩ : syracuseStep 2531245 = 949217) (by norm_num)
theorem B3374993 : Blo 1999435 3374993 := bstep (se 2 (by rfl) ⟨1265622, by rfl⟩ : syracuseStep 3374993 = 2531245) B2531245
theorem B2249995 : Blo 1999435 2249995 := bstep (se 1 (by rfl) ⟨1687496, by rfl⟩ : syracuseStep 2249995 = 3374993) B3374993
theorem B2999993 : Blo 1999435 2999993 := bstep (se 2 (by rfl) ⟨1124997, by rfl⟩ : syracuseStep 2999993 = 2249995) B2249995
theorem B1999995 : Blo 1999435 1999995 := bstep (se 1 (by rfl) ⟨1499996, by rfl⟩ : syracuseStep 1999995 = 2999993) B2999993
theorem B12814453 : Blo 1999435 12814453 := bbase (se 5 (by rfl) ⟨600677, by rfl⟩ : syracuseStep 12814453 = 1201355) (by norm_num)
theorem B17085937 : Blo 1999435 17085937 := bstep (se 2 (by rfl) ⟨6407226, by rfl⟩ : syracuseStep 17085937 = 12814453) B12814453
theorem B22781249 : Blo 1999435 22781249 := bstep (se 2 (by rfl) ⟨8542968, by rfl⟩ : syracuseStep 22781249 = 17085937) B17085937
theorem B15187499 : Blo 1999435 15187499 := bstep (se 1 (by rfl) ⟨11390624, by rfl⟩ : syracuseStep 15187499 = 22781249) B22781249
theorem B10124999 : Blo 1999435 10124999 := bstep (se 1 (by rfl) ⟨7593749, by rfl⟩ : syracuseStep 10124999 = 15187499) B15187499
theorem B6749999 : Blo 1999435 6749999 := bstep (se 1 (by rfl) ⟨5062499, by rfl⟩ : syracuseStep 6749999 = 10124999) B10124999
theorem B4499999 : Blo 1999435 4499999 := bstep (se 1 (by rfl) ⟨3374999, by rfl⟩ : syracuseStep 4499999 = 6749999) B6749999
theorem B2999999 : Blo 1999435 2999999 := bstep (se 1 (by rfl) ⟨2249999, by rfl⟩ : syracuseStep 2999999 = 4499999) B4499999
theorem B1999999 : Blo 1999435 1999999 := bstep (se 1 (by rfl) ⟨1499999, by rfl⟩ : syracuseStep 1999999 = 2999999) B2999999
theorem B3000005 : Blo 1999435 3000005 := bbase (se 4 (by rfl) ⟨281250, by rfl⟩ : syracuseStep 3000005 = 562501) (by norm_num)
theorem B2000003 : Blo 1999435 2000003 := bstep (se 1 (by rfl) ⟨1500002, by rfl⟩ : syracuseStep 2000003 = 3000005) B3000005
theorem B3375013 : Blo 1999435 3375013 := bbase (se 4 (by rfl) ⟨316407, by rfl⟩ : syracuseStep 3375013 = 632815) (by norm_num)
theorem B4500017 : Blo 1999435 4500017 := bstep (se 2 (by rfl) ⟨1687506, by rfl⟩ : syracuseStep 4500017 = 3375013) B3375013
theorem B3000011 : Blo 1999435 3000011 := bstep (se 1 (by rfl) ⟨2250008, by rfl⟩ : syracuseStep 3000011 = 4500017) B4500017
theorem B2000007 : Blo 1999435 2000007 := bstep (se 1 (by rfl) ⟨1500005, by rfl⟩ : syracuseStep 2000007 = 3000011) B3000011
theorem B2250013 : Blo 1999435 2250013 := bbase (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) (by norm_num)
theorem B3000017 : Blo 1999435 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B2000011 : Blo 1999435 2000011 := bstep (se 1 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 2000011 = 3000017) B3000017
theorem B6750053 : Blo 1999435 6750053 := bbase (se 4 (by rfl) ⟨632817, by rfl⟩ : syracuseStep 6750053 = 1265635) (by norm_num)
theorem B4500035 : Blo 1999435 4500035 := bstep (se 1 (by rfl) ⟨3375026, by rfl⟩ : syracuseStep 4500035 = 6750053) B6750053
theorem B3000023 : Blo 1999435 3000023 := bstep (se 1 (by rfl) ⟨2250017, by rfl⟩ : syracuseStep 3000023 = 4500035) B4500035
theorem B2000015 : Blo 1999435 2000015 := bstep (se 1 (by rfl) ⟨1500011, by rfl⟩ : syracuseStep 2000015 = 3000023) B3000023
theorem B3000029 : Blo 1999435 3000029 := bbase (se 3 (by rfl) ⟨562505, by rfl⟩ : syracuseStep 3000029 = 1125011) (by norm_num)
theorem B2000019 : Blo 1999435 2000019 := bstep (se 1 (by rfl) ⟨1500014, by rfl⟩ : syracuseStep 2000019 = 3000029) B3000029
theorem B4500053 : Blo 1999435 4500053 := bbase (se 8 (by rfl) ⟨26367, by rfl⟩ : syracuseStep 4500053 = 52735) (by norm_num)
theorem B3000035 : Blo 1999435 3000035 := bstep (se 1 (by rfl) ⟨2250026, by rfl⟩ : syracuseStep 3000035 = 4500053) B4500053
theorem B2000023 : Blo 1999435 2000023 := bstep (se 1 (by rfl) ⟨1500017, by rfl⟩ : syracuseStep 2000023 = 3000035) B3000035
theorem B3604117 : Blo 1999435 3604117 := bbase (se 6 (by rfl) ⟨84471, by rfl⟩ : syracuseStep 3604117 = 168943) (by norm_num)
theorem B4805489 : Blo 1999435 4805489 := bstep (se 2 (by rfl) ⟨1802058, by rfl⟩ : syracuseStep 4805489 = 3604117) B3604117
theorem B3203659 : Blo 1999435 3203659 := bstep (se 1 (by rfl) ⟨2402744, by rfl⟩ : syracuseStep 3203659 = 4805489) B4805489
theorem B4271545 : Blo 1999435 4271545 := bstep (se 2 (by rfl) ⟨1601829, by rfl⟩ : syracuseStep 4271545 = 3203659) B3203659
theorem B5695393 : Blo 1999435 5695393 := bstep (se 2 (by rfl) ⟨2135772, by rfl⟩ : syracuseStep 5695393 = 4271545) B4271545
theorem B7593857 : Blo 1999435 7593857 := bstep (se 2 (by rfl) ⟨2847696, by rfl⟩ : syracuseStep 7593857 = 5695393) B5695393
theorem B5062571 : Blo 1999435 5062571 := bstep (se 1 (by rfl) ⟨3796928, by rfl⟩ : syracuseStep 5062571 = 7593857) B7593857
theorem B3375047 : Blo 1999435 3375047 := bstep (se 1 (by rfl) ⟨2531285, by rfl⟩ : syracuseStep 3375047 = 5062571) B5062571
theorem B2250031 : Blo 1999435 2250031 := bstep (se 1 (by rfl) ⟨1687523, by rfl⟩ : syracuseStep 2250031 = 3375047) B3375047
theorem B3000041 : Blo 1999435 3000041 := bstep (se 2 (by rfl) ⟨1125015, by rfl⟩ : syracuseStep 3000041 = 2250031) B2250031
theorem B2000027 : Blo 1999435 2000027 := bstep (se 1 (by rfl) ⟨1500020, by rfl⟩ : syracuseStep 2000027 = 3000041) B3000041
theorem B10959893 : Blo 1999435 10959893 := bbase (se 6 (by rfl) ⟨256872, by rfl⟩ : syracuseStep 10959893 = 513745) (by norm_num)
theorem B7306595 : Blo 1999435 7306595 := bstep (se 1 (by rfl) ⟨5479946, by rfl⟩ : syracuseStep 7306595 = 10959893) B10959893
theorem B4871063 : Blo 1999435 4871063 := bstep (se 1 (by rfl) ⟨3653297, by rfl⟩ : syracuseStep 4871063 = 7306595) B7306595
theorem B3247375 : Blo 1999435 3247375 := bstep (se 1 (by rfl) ⟨2435531, by rfl⟩ : syracuseStep 3247375 = 4871063) B4871063
theorem B4329833 : Blo 1999435 4329833 := bstep (se 2 (by rfl) ⟨1623687, by rfl⟩ : syracuseStep 4329833 = 3247375) B3247375
theorem B11546221 : Blo 1999435 11546221 := bstep (se 3 (by rfl) ⟨2164916, by rfl⟩ : syracuseStep 11546221 = 4329833) B4329833
theorem B15394961 : Blo 1999435 15394961 := bstep (se 2 (by rfl) ⟨5773110, by rfl⟩ : syracuseStep 15394961 = 11546221) B11546221
theorem B10263307 : Blo 1999435 10263307 := bstep (se 1 (by rfl) ⟨7697480, by rfl⟩ : syracuseStep 10263307 = 15394961) B15394961
theorem B13684409 : Blo 1999435 13684409 := bstep (se 2 (by rfl) ⟨5131653, by rfl⟩ : syracuseStep 13684409 = 10263307) B10263307
theorem B9122939 : Blo 1999435 9122939 := bstep (se 1 (by rfl) ⟨6842204, by rfl⟩ : syracuseStep 9122939 = 13684409) B13684409
theorem B6081959 : Blo 1999435 6081959 := bstep (se 1 (by rfl) ⟨4561469, by rfl⟩ : syracuseStep 6081959 = 9122939) B9122939
theorem B4054639 : Blo 1999435 4054639 := bstep (se 1 (by rfl) ⟨3040979, by rfl⟩ : syracuseStep 4054639 = 6081959) B6081959
theorem B5406185 : Blo 1999435 5406185 := bstep (se 2 (by rfl) ⟨2027319, by rfl⟩ : syracuseStep 5406185 = 4054639) B4054639
theorem B3604123 : Blo 1999435 3604123 := bstep (se 1 (by rfl) ⟨2703092, by rfl⟩ : syracuseStep 3604123 = 5406185) B5406185
theorem B4805497 : Blo 1999435 4805497 := bstep (se 2 (by rfl) ⟨1802061, by rfl⟩ : syracuseStep 4805497 = 3604123) B3604123
theorem B25629317 : Blo 1999435 25629317 := bstep (se 4 (by rfl) ⟨2402748, by rfl⟩ : syracuseStep 25629317 = 4805497) B4805497
theorem B17086211 : Blo 1999435 17086211 := bstep (se 1 (by rfl) ⟨12814658, by rfl⟩ : syracuseStep 17086211 = 25629317) B25629317
theorem B11390807 : Blo 1999435 11390807 := bstep (se 1 (by rfl) ⟨8543105, by rfl⟩ : syracuseStep 11390807 = 17086211) B17086211
theorem B7593871 : Blo 1999435 7593871 := bstep (se 1 (by rfl) ⟨5695403, by rfl⟩ : syracuseStep 7593871 = 11390807) B11390807
theorem B10125161 : Blo 1999435 10125161 := bstep (se 2 (by rfl) ⟨3796935, by rfl⟩ : syracuseStep 10125161 = 7593871) B7593871
theorem B6750107 : Blo 1999435 6750107 := bstep (se 1 (by rfl) ⟨5062580, by rfl⟩ : syracuseStep 6750107 = 10125161) B10125161
theorem B4500071 : Blo 1999435 4500071 := bstep (se 1 (by rfl) ⟨3375053, by rfl⟩ : syracuseStep 4500071 = 6750107) B6750107
theorem B3000047 : Blo 1999435 3000047 := bstep (se 1 (by rfl) ⟨2250035, by rfl⟩ : syracuseStep 3000047 = 4500071) B4500071
theorem B2000031 : Blo 1999435 2000031 := bstep (se 1 (by rfl) ⟨1500023, by rfl⟩ : syracuseStep 2000031 = 3000047) B3000047
theorem B3000053 : Blo 1999435 3000053 := bbase (se 5 (by rfl) ⟨140627, by rfl⟩ : syracuseStep 3000053 = 281255) (by norm_num)
theorem B2000035 : Blo 1999435 2000035 := bstep (se 1 (by rfl) ⟨1500026, by rfl⟩ : syracuseStep 2000035 = 3000053) B3000053
theorem B8543141 : Blo 1999435 8543141 := bbase (se 4 (by rfl) ⟨800919, by rfl⟩ : syracuseStep 8543141 = 1601839) (by norm_num)
theorem B5695427 : Blo 1999435 5695427 := bstep (se 1 (by rfl) ⟨4271570, by rfl⟩ : syracuseStep 5695427 = 8543141) B8543141
theorem B3796951 : Blo 1999435 3796951 := bstep (se 1 (by rfl) ⟨2847713, by rfl⟩ : syracuseStep 3796951 = 5695427) B5695427
theorem B5062601 : Blo 1999435 5062601 := bstep (se 2 (by rfl) ⟨1898475, by rfl⟩ : syracuseStep 5062601 = 3796951) B3796951
theorem B3375067 : Blo 1999435 3375067 := bstep (se 1 (by rfl) ⟨2531300, by rfl⟩ : syracuseStep 3375067 = 5062601) B5062601
theorem B4500089 : Blo 1999435 4500089 := bstep (se 2 (by rfl) ⟨1687533, by rfl⟩ : syracuseStep 4500089 = 3375067) B3375067
theorem B3000059 : Blo 1999435 3000059 := bstep (se 1 (by rfl) ⟨2250044, by rfl⟩ : syracuseStep 3000059 = 4500089) B4500089
theorem B2000039 : Blo 1999435 2000039 := bstep (se 1 (by rfl) ⟨1500029, by rfl⟩ : syracuseStep 2000039 = 3000059) B3000059
theorem B2250049 : Blo 1999435 2250049 := bbase (se 2 (by rfl) ⟨843768, by rfl⟩ : syracuseStep 2250049 = 1687537) (by norm_num)
theorem B3000065 : Blo 1999435 3000065 := bstep (se 2 (by rfl) ⟨1125024, by rfl⟩ : syracuseStep 3000065 = 2250049) B2250049
theorem B2000043 : Blo 1999435 2000043 := bstep (se 1 (by rfl) ⟨1500032, by rfl⟩ : syracuseStep 2000043 = 3000065) B3000065
theorem B5062621 : Blo 1999435 5062621 := bbase (se 3 (by rfl) ⟨949241, by rfl⟩ : syracuseStep 5062621 = 1898483) (by norm_num)
theorem B6750161 : Blo 1999435 6750161 := bstep (se 2 (by rfl) ⟨2531310, by rfl⟩ : syracuseStep 6750161 = 5062621) B5062621
theorem B4500107 : Blo 1999435 4500107 := bstep (se 1 (by rfl) ⟨3375080, by rfl⟩ : syracuseStep 4500107 = 6750161) B6750161
theorem B3000071 : Blo 1999435 3000071 := bstep (se 1 (by rfl) ⟨2250053, by rfl⟩ : syracuseStep 3000071 = 4500107) B4500107
theorem B2000047 : Blo 1999435 2000047 := bstep (se 1 (by rfl) ⟨1500035, by rfl⟩ : syracuseStep 2000047 = 3000071) B3000071
theorem B3000077 : Blo 1999435 3000077 := bbase (se 3 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 3000077 = 1125029) (by norm_num)
theorem B2000051 : Blo 1999435 2000051 := bstep (se 1 (by rfl) ⟨1500038, by rfl⟩ : syracuseStep 2000051 = 3000077) B3000077
theorem B4500125 : Blo 1999435 4500125 := bbase (se 3 (by rfl) ⟨843773, by rfl⟩ : syracuseStep 4500125 = 1687547) (by norm_num)
theorem B3000083 : Blo 1999435 3000083 := bstep (se 1 (by rfl) ⟨2250062, by rfl⟩ : syracuseStep 3000083 = 4500125) B4500125
theorem B2000055 : Blo 1999435 2000055 := bstep (se 1 (by rfl) ⟨1500041, by rfl⟩ : syracuseStep 2000055 = 3000083) B3000083
theorem B3375101 : Blo 1999435 3375101 := bbase (se 3 (by rfl) ⟨632831, by rfl⟩ : syracuseStep 3375101 = 1265663) (by norm_num)
theorem B2250067 : Blo 1999435 2250067 := bstep (se 1 (by rfl) ⟨1687550, by rfl⟩ : syracuseStep 2250067 = 3375101) B3375101
theorem B3000089 : Blo 1999435 3000089 := bstep (se 2 (by rfl) ⟨1125033, by rfl⟩ : syracuseStep 3000089 = 2250067) B2250067
theorem B2000059 : Blo 1999435 2000059 := bstep (se 1 (by rfl) ⟨1500044, by rfl⟩ : syracuseStep 2000059 = 3000089) B3000089
theorem B4271621 : Blo 1999435 4271621 := bbase (se 4 (by rfl) ⟨400464, by rfl⟩ : syracuseStep 4271621 = 800929) (by norm_num)
theorem B11390989 : Blo 1999435 11390989 := bstep (se 3 (by rfl) ⟨2135810, by rfl⟩ : syracuseStep 11390989 = 4271621) B4271621
theorem B15187985 : Blo 1999435 15187985 := bstep (se 2 (by rfl) ⟨5695494, by rfl⟩ : syracuseStep 15187985 = 11390989) B11390989
theorem B10125323 : Blo 1999435 10125323 := bstep (se 1 (by rfl) ⟨7593992, by rfl⟩ : syracuseStep 10125323 = 15187985) B15187985
theorem B6750215 : Blo 1999435 6750215 := bstep (se 1 (by rfl) ⟨5062661, by rfl⟩ : syracuseStep 6750215 = 10125323) B10125323
theorem B4500143 : Blo 1999435 4500143 := bstep (se 1 (by rfl) ⟨3375107, by rfl⟩ : syracuseStep 4500143 = 6750215) B6750215
theorem B3000095 : Blo 1999435 3000095 := bstep (se 1 (by rfl) ⟨2250071, by rfl⟩ : syracuseStep 3000095 = 4500143) B4500143
theorem B2000063 : Blo 1999435 2000063 := bstep (se 1 (by rfl) ⟨1500047, by rfl⟩ : syracuseStep 2000063 = 3000095) B3000095
theorem B3000101 : Blo 1999435 3000101 := bbase (se 4 (by rfl) ⟨281259, by rfl⟩ : syracuseStep 3000101 = 562519) (by norm_num)
theorem B2000067 : Blo 1999435 2000067 := bstep (se 1 (by rfl) ⟨1500050, by rfl⟩ : syracuseStep 2000067 = 3000101) B3000101
theorem B2531341 : Blo 1999435 2531341 := bbase (se 3 (by rfl) ⟨474626, by rfl⟩ : syracuseStep 2531341 = 949253) (by norm_num)
theorem B3375121 : Blo 1999435 3375121 := bstep (se 2 (by rfl) ⟨1265670, by rfl⟩ : syracuseStep 3375121 = 2531341) B2531341
theorem B4500161 : Blo 1999435 4500161 := bstep (se 2 (by rfl) ⟨1687560, by rfl⟩ : syracuseStep 4500161 = 3375121) B3375121
theorem B3000107 : Blo 1999435 3000107 := bstep (se 1 (by rfl) ⟨2250080, by rfl⟩ : syracuseStep 3000107 = 4500161) B4500161
theorem B2000071 : Blo 1999435 2000071 := bstep (se 1 (by rfl) ⟨1500053, by rfl⟩ : syracuseStep 2000071 = 3000107) B3000107
theorem B2250085 : Blo 1999435 2250085 := bbase (se 4 (by rfl) ⟨210945, by rfl⟩ : syracuseStep 2250085 = 421891) (by norm_num)
theorem B3000113 : Blo 1999435 3000113 := bstep (se 2 (by rfl) ⟨1125042, by rfl⟩ : syracuseStep 3000113 = 2250085) B2250085
theorem B2000075 : Blo 1999435 2000075 := bstep (se 1 (by rfl) ⟨1500056, by rfl⟩ : syracuseStep 2000075 = 3000113) B3000113
theorem B5695541 : Blo 1999435 5695541 := bbase (se 5 (by rfl) ⟨266978, by rfl⟩ : syracuseStep 5695541 = 533957) (by norm_num)
theorem B3797027 : Blo 1999435 3797027 := bstep (se 1 (by rfl) ⟨2847770, by rfl⟩ : syracuseStep 3797027 = 5695541) B5695541
theorem B2531351 : Blo 1999435 2531351 := bstep (se 1 (by rfl) ⟨1898513, by rfl⟩ : syracuseStep 2531351 = 3797027) B3797027
theorem B6750269 : Blo 1999435 6750269 := bstep (se 3 (by rfl) ⟨1265675, by rfl⟩ : syracuseStep 6750269 = 2531351) B2531351
theorem B4500179 : Blo 1999435 4500179 := bstep (se 1 (by rfl) ⟨3375134, by rfl⟩ : syracuseStep 4500179 = 6750269) B6750269
theorem B3000119 : Blo 1999435 3000119 := bstep (se 1 (by rfl) ⟨2250089, by rfl⟩ : syracuseStep 3000119 = 4500179) B4500179
theorem B2000079 : Blo 1999435 2000079 := bstep (se 1 (by rfl) ⟨1500059, by rfl⟩ : syracuseStep 2000079 = 3000119) B3000119
theorem B3000125 : Blo 1999435 3000125 := bbase (se 3 (by rfl) ⟨562523, by rfl⟩ : syracuseStep 3000125 = 1125047) (by norm_num)
theorem B2000083 : Blo 1999435 2000083 := bstep (se 1 (by rfl) ⟨1500062, by rfl⟩ : syracuseStep 2000083 = 3000125) B3000125
theorem B4500197 : Blo 1999435 4500197 := bbase (se 4 (by rfl) ⟨421893, by rfl⟩ : syracuseStep 4500197 = 843787) (by norm_num)
theorem B3000131 : Blo 1999435 3000131 := bstep (se 1 (by rfl) ⟨2250098, by rfl⟩ : syracuseStep 3000131 = 4500197) B4500197
theorem B2000087 : Blo 1999435 2000087 := bstep (se 1 (by rfl) ⟨1500065, by rfl⟩ : syracuseStep 2000087 = 3000131) B3000131
theorem B5062733 : Blo 1999435 5062733 := bbase (se 3 (by rfl) ⟨949262, by rfl⟩ : syracuseStep 5062733 = 1898525) (by norm_num)
theorem B3375155 : Blo 1999435 3375155 := bstep (se 1 (by rfl) ⟨2531366, by rfl⟩ : syracuseStep 3375155 = 5062733) B5062733
theorem B2250103 : Blo 1999435 2250103 := bstep (se 1 (by rfl) ⟨1687577, by rfl⟩ : syracuseStep 2250103 = 3375155) B3375155
theorem B3000137 : Blo 1999435 3000137 := bstep (se 2 (by rfl) ⟨1125051, by rfl⟩ : syracuseStep 3000137 = 2250103) B2250103
theorem B2000091 : Blo 1999435 2000091 := bstep (se 1 (by rfl) ⟨1500068, by rfl⟩ : syracuseStep 2000091 = 3000137) B3000137
theorem B2135845 : Blo 1999435 2135845 := bbase (se 4 (by rfl) ⟨200235, by rfl⟩ : syracuseStep 2135845 = 400471) (by norm_num)
theorem B2847793 : Blo 1999435 2847793 := bstep (se 2 (by rfl) ⟨1067922, by rfl⟩ : syracuseStep 2847793 = 2135845) B2135845
theorem B3797057 : Blo 1999435 3797057 := bstep (se 2 (by rfl) ⟨1423896, by rfl⟩ : syracuseStep 3797057 = 2847793) B2847793
theorem B10125485 : Blo 1999435 10125485 := bstep (se 3 (by rfl) ⟨1898528, by rfl⟩ : syracuseStep 10125485 = 3797057) B3797057
theorem B6750323 : Blo 1999435 6750323 := bstep (se 1 (by rfl) ⟨5062742, by rfl⟩ : syracuseStep 6750323 = 10125485) B10125485
theorem B4500215 : Blo 1999435 4500215 := bstep (se 1 (by rfl) ⟨3375161, by rfl⟩ : syracuseStep 4500215 = 6750323) B6750323
theorem B3000143 : Blo 1999435 3000143 := bstep (se 1 (by rfl) ⟨2250107, by rfl⟩ : syracuseStep 3000143 = 4500215) B4500215
theorem B2000095 : Blo 1999435 2000095 := bstep (se 1 (by rfl) ⟨1500071, by rfl⟩ : syracuseStep 2000095 = 3000143) B3000143
theorem B3000149 : Blo 1999435 3000149 := bbase (se 9 (by rfl) ⟨8789, by rfl⟩ : syracuseStep 3000149 = 17579) (by norm_num)
theorem B2000099 : Blo 1999435 2000099 := bstep (se 1 (by rfl) ⟨1500074, by rfl⟩ : syracuseStep 2000099 = 3000149) B3000149
theorem B2280817 : Blo 1999435 2280817 := bbase (se 2 (by rfl) ⟨855306, by rfl⟩ : syracuseStep 2280817 = 1710613) (by norm_num)
theorem B12164357 : Blo 1999435 12164357 := bstep (se 4 (by rfl) ⟨1140408, by rfl⟩ : syracuseStep 12164357 = 2280817) B2280817
theorem B8109571 : Blo 1999435 8109571 := bstep (se 1 (by rfl) ⟨6082178, by rfl⟩ : syracuseStep 8109571 = 12164357) B12164357
theorem B10812761 : Blo 1999435 10812761 := bstep (se 2 (by rfl) ⟨4054785, by rfl⟩ : syracuseStep 10812761 = 8109571) B8109571
theorem B7208507 : Blo 1999435 7208507 := bstep (se 1 (by rfl) ⟨5406380, by rfl⟩ : syracuseStep 7208507 = 10812761) B10812761
theorem B4805671 : Blo 1999435 4805671 := bstep (se 1 (by rfl) ⟨3604253, by rfl⟩ : syracuseStep 4805671 = 7208507) B7208507
theorem B6407561 : Blo 1999435 6407561 := bstep (se 2 (by rfl) ⟨2402835, by rfl⟩ : syracuseStep 6407561 = 4805671) B4805671
theorem B4271707 : Blo 1999435 4271707 := bstep (se 1 (by rfl) ⟨3203780, by rfl⟩ : syracuseStep 4271707 = 6407561) B6407561
theorem B5695609 : Blo 1999435 5695609 := bstep (se 2 (by rfl) ⟨2135853, by rfl⟩ : syracuseStep 5695609 = 4271707) B4271707
theorem B7594145 : Blo 1999435 7594145 := bstep (se 2 (by rfl) ⟨2847804, by rfl⟩ : syracuseStep 7594145 = 5695609) B5695609
theorem B5062763 : Blo 1999435 5062763 := bstep (se 1 (by rfl) ⟨3797072, by rfl⟩ : syracuseStep 5062763 = 7594145) B7594145
theorem B3375175 : Blo 1999435 3375175 := bstep (se 1 (by rfl) ⟨2531381, by rfl⟩ : syracuseStep 3375175 = 5062763) B5062763
theorem B4500233 : Blo 1999435 4500233 := bstep (se 2 (by rfl) ⟨1687587, by rfl⟩ : syracuseStep 4500233 = 3375175) B3375175
theorem B3000155 : Blo 1999435 3000155 := bstep (se 1 (by rfl) ⟨2250116, by rfl⟩ : syracuseStep 3000155 = 4500233) B4500233
theorem B2000103 : Blo 1999435 2000103 := bstep (se 1 (by rfl) ⟨1500077, by rfl⟩ : syracuseStep 2000103 = 3000155) B3000155
theorem B2250121 : Blo 1999435 2250121 := bbase (se 2 (by rfl) ⟨843795, by rfl⟩ : syracuseStep 2250121 = 1687591) (by norm_num)
theorem B3000161 : Blo 1999435 3000161 := bstep (se 2 (by rfl) ⟨1125060, by rfl⟩ : syracuseStep 3000161 = 2250121) B2250121
theorem B2000107 : Blo 1999435 2000107 := bstep (se 1 (by rfl) ⟨1500080, by rfl⟩ : syracuseStep 2000107 = 3000161) B3000161
theorem B2565929 : Blo 1999435 2565929 := bbase (se 2 (by rfl) ⟨962223, by rfl⟩ : syracuseStep 2565929 = 1924447) (by norm_num)
theorem B6842477 : Blo 1999435 6842477 := bstep (se 3 (by rfl) ⟨1282964, by rfl⟩ : syracuseStep 6842477 = 2565929) B2565929
theorem B4561651 : Blo 1999435 4561651 := bstep (se 1 (by rfl) ⟨3421238, by rfl⟩ : syracuseStep 4561651 = 6842477) B6842477
theorem B6082201 : Blo 1999435 6082201 := bstep (se 2 (by rfl) ⟨2280825, by rfl⟩ : syracuseStep 6082201 = 4561651) B4561651
theorem B8109601 : Blo 1999435 8109601 := bstep (se 2 (by rfl) ⟨3041100, by rfl⟩ : syracuseStep 8109601 = 6082201) B6082201
theorem B43251205 : Blo 1999435 43251205 := bstep (se 4 (by rfl) ⟨4054800, by rfl⟩ : syracuseStep 43251205 = 8109601) B8109601
theorem B57668273 : Blo 1999435 57668273 := bstep (se 2 (by rfl) ⟨21625602, by rfl⟩ : syracuseStep 57668273 = 43251205) B43251205
theorem B38445515 : Blo 1999435 38445515 := bstep (se 1 (by rfl) ⟨28834136, by rfl⟩ : syracuseStep 38445515 = 57668273) B57668273
theorem B25630343 : Blo 1999435 25630343 := bstep (se 1 (by rfl) ⟨19222757, by rfl⟩ : syracuseStep 25630343 = 38445515) B38445515
theorem B17086895 : Blo 1999435 17086895 := bstep (se 1 (by rfl) ⟨12815171, by rfl⟩ : syracuseStep 17086895 = 25630343) B25630343
theorem B11391263 : Blo 1999435 11391263 := bstep (se 1 (by rfl) ⟨8543447, by rfl⟩ : syracuseStep 11391263 = 17086895) B17086895
theorem B7594175 : Blo 1999435 7594175 := bstep (se 1 (by rfl) ⟨5695631, by rfl⟩ : syracuseStep 7594175 = 11391263) B11391263
theorem B5062783 : Blo 1999435 5062783 := bstep (se 1 (by rfl) ⟨3797087, by rfl⟩ : syracuseStep 5062783 = 7594175) B7594175
theorem B6750377 : Blo 1999435 6750377 := bstep (se 2 (by rfl) ⟨2531391, by rfl⟩ : syracuseStep 6750377 = 5062783) B5062783
theorem B4500251 : Blo 1999435 4500251 := bstep (se 1 (by rfl) ⟨3375188, by rfl⟩ : syracuseStep 4500251 = 6750377) B6750377
theorem B3000167 : Blo 1999435 3000167 := bstep (se 1 (by rfl) ⟨2250125, by rfl⟩ : syracuseStep 3000167 = 4500251) B4500251
theorem B2000111 : Blo 1999435 2000111 := bstep (se 1 (by rfl) ⟨1500083, by rfl⟩ : syracuseStep 2000111 = 3000167) B3000167
theorem B3000173 : Blo 1999435 3000173 := bbase (se 3 (by rfl) ⟨562532, by rfl⟩ : syracuseStep 3000173 = 1125065) (by norm_num)
theorem B2000115 : Blo 1999435 2000115 := bstep (se 1 (by rfl) ⟨1500086, by rfl⟩ : syracuseStep 2000115 = 3000173) B3000173
theorem B4500269 : Blo 1999435 4500269 := bbase (se 3 (by rfl) ⟨843800, by rfl⟩ : syracuseStep 4500269 = 1687601) (by norm_num)
theorem B3000179 : Blo 1999435 3000179 := bstep (se 1 (by rfl) ⟨2250134, by rfl⟩ : syracuseStep 3000179 = 4500269) B4500269
theorem B2000119 : Blo 1999435 2000119 := bstep (se 1 (by rfl) ⟨1500089, by rfl⟩ : syracuseStep 2000119 = 3000179) B3000179
theorem B3203813 : Blo 1999435 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B8543501 : Blo 1999435 8543501 := bstep (se 3 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 8543501 = 3203813) B3203813
theorem B5695667 : Blo 1999435 5695667 := bstep (se 1 (by rfl) ⟨4271750, by rfl⟩ : syracuseStep 5695667 = 8543501) B8543501
theorem B3797111 : Blo 1999435 3797111 := bstep (se 1 (by rfl) ⟨2847833, by rfl⟩ : syracuseStep 3797111 = 5695667) B5695667
theorem B2531407 : Blo 1999435 2531407 := bstep (se 1 (by rfl) ⟨1898555, by rfl⟩ : syracuseStep 2531407 = 3797111) B3797111
theorem B3375209 : Blo 1999435 3375209 := bstep (se 2 (by rfl) ⟨1265703, by rfl⟩ : syracuseStep 3375209 = 2531407) B2531407
theorem B2250139 : Blo 1999435 2250139 := bstep (se 1 (by rfl) ⟨1687604, by rfl⟩ : syracuseStep 2250139 = 3375209) B3375209
theorem B3000185 : Blo 1999435 3000185 := bstep (se 2 (by rfl) ⟨1125069, by rfl⟩ : syracuseStep 3000185 = 2250139) B2250139
theorem B2000123 : Blo 1999435 2000123 := bstep (se 1 (by rfl) ⟨1500092, by rfl⟩ : syracuseStep 2000123 = 3000185) B3000185
theorem B2565949 : Blo 1999435 2565949 := bbase (se 3 (by rfl) ⟨481115, by rfl⟩ : syracuseStep 2565949 = 962231) (by norm_num)
theorem B54740245 : Blo 1999435 54740245 := bstep (se 6 (by rfl) ⟨1282974, by rfl⟩ : syracuseStep 54740245 = 2565949) B2565949
theorem B72986993 : Blo 1999435 72986993 := bstep (se 2 (by rfl) ⟨27370122, by rfl⟩ : syracuseStep 72986993 = 54740245) B54740245
theorem B48657995 : Blo 1999435 48657995 := bstep (se 1 (by rfl) ⟨36493496, by rfl⟩ : syracuseStep 48657995 = 72986993) B72986993
theorem B32438663 : Blo 1999435 32438663 := bstep (se 1 (by rfl) ⟨24328997, by rfl⟩ : syracuseStep 32438663 = 48657995) B48657995
theorem B21625775 : Blo 1999435 21625775 := bstep (se 1 (by rfl) ⟨16219331, by rfl⟩ : syracuseStep 21625775 = 32438663) B32438663
theorem B14417183 : Blo 1999435 14417183 := bstep (se 1 (by rfl) ⟨10812887, by rfl⟩ : syracuseStep 14417183 = 21625775) B21625775
theorem B9611455 : Blo 1999435 9611455 := bstep (se 1 (by rfl) ⟨7208591, by rfl⟩ : syracuseStep 9611455 = 14417183) B14417183
theorem B12815273 : Blo 1999435 12815273 := bstep (se 2 (by rfl) ⟨4805727, by rfl⟩ : syracuseStep 12815273 = 9611455) B9611455
theorem B34174061 : Blo 1999435 34174061 := bstep (se 3 (by rfl) ⟨6407636, by rfl⟩ : syracuseStep 34174061 = 12815273) B12815273
theorem B22782707 : Blo 1999435 22782707 := bstep (se 1 (by rfl) ⟨17087030, by rfl⟩ : syracuseStep 22782707 = 34174061) B34174061
theorem B15188471 : Blo 1999435 15188471 := bstep (se 1 (by rfl) ⟨11391353, by rfl⟩ : syracuseStep 15188471 = 22782707) B22782707
theorem B10125647 : Blo 1999435 10125647 := bstep (se 1 (by rfl) ⟨7594235, by rfl⟩ : syracuseStep 10125647 = 15188471) B15188471
theorem B6750431 : Blo 1999435 6750431 := bstep (se 1 (by rfl) ⟨5062823, by rfl⟩ : syracuseStep 6750431 = 10125647) B10125647
theorem B4500287 : Blo 1999435 4500287 := bstep (se 1 (by rfl) ⟨3375215, by rfl⟩ : syracuseStep 4500287 = 6750431) B6750431
theorem B3000191 : Blo 1999435 3000191 := bstep (se 1 (by rfl) ⟨2250143, by rfl⟩ : syracuseStep 3000191 = 4500287) B4500287
theorem B2000127 : Blo 1999435 2000127 := bstep (se 1 (by rfl) ⟨1500095, by rfl⟩ : syracuseStep 2000127 = 3000191) B3000191
theorem B3000197 : Blo 1999435 3000197 := bbase (se 4 (by rfl) ⟨281268, by rfl⟩ : syracuseStep 3000197 = 562537) (by norm_num)
theorem B2000131 : Blo 1999435 2000131 := bstep (se 1 (by rfl) ⟨1500098, by rfl⟩ : syracuseStep 2000131 = 3000197) B3000197
theorem B3375229 : Blo 1999435 3375229 := bbase (se 3 (by rfl) ⟨632855, by rfl⟩ : syracuseStep 3375229 = 1265711) (by norm_num)
theorem B4500305 : Blo 1999435 4500305 := bstep (se 2 (by rfl) ⟨1687614, by rfl⟩ : syracuseStep 4500305 = 3375229) B3375229
theorem B3000203 : Blo 1999435 3000203 := bstep (se 1 (by rfl) ⟨2250152, by rfl⟩ : syracuseStep 3000203 = 4500305) B4500305
theorem B2000135 : Blo 1999435 2000135 := bstep (se 1 (by rfl) ⟨1500101, by rfl⟩ : syracuseStep 2000135 = 3000203) B3000203
theorem B2250157 : Blo 1999435 2250157 := bbase (se 3 (by rfl) ⟨421904, by rfl⟩ : syracuseStep 2250157 = 843809) (by norm_num)
theorem B3000209 : Blo 1999435 3000209 := bstep (se 2 (by rfl) ⟨1125078, by rfl⟩ : syracuseStep 3000209 = 2250157) B2250157
theorem B2000139 : Blo 1999435 2000139 := bstep (se 1 (by rfl) ⟨1500104, by rfl⟩ : syracuseStep 2000139 = 3000209) B3000209
theorem B6750485 : Blo 1999435 6750485 := bbase (se 6 (by rfl) ⟨158214, by rfl⟩ : syracuseStep 6750485 = 316429) (by norm_num)
theorem B4500323 : Blo 1999435 4500323 := bstep (se 1 (by rfl) ⟨3375242, by rfl⟩ : syracuseStep 4500323 = 6750485) B6750485
theorem B3000215 : Blo 1999435 3000215 := bstep (se 1 (by rfl) ⟨2250161, by rfl⟩ : syracuseStep 3000215 = 4500323) B4500323
theorem B2000143 : Blo 1999435 2000143 := bstep (se 1 (by rfl) ⟨1500107, by rfl⟩ : syracuseStep 2000143 = 3000215) B3000215
theorem B3000221 : Blo 1999435 3000221 := bbase (se 3 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 3000221 = 1125083) (by norm_num)
theorem B2000147 : Blo 1999435 2000147 := bstep (se 1 (by rfl) ⟨1500110, by rfl⟩ : syracuseStep 2000147 = 3000221) B3000221
theorem B4500341 : Blo 1999435 4500341 := bbase (se 5 (by rfl) ⟨210953, by rfl⟩ : syracuseStep 4500341 = 421907) (by norm_num)
theorem B3000227 : Blo 1999435 3000227 := bstep (se 1 (by rfl) ⟨2250170, by rfl⟩ : syracuseStep 3000227 = 4500341) B4500341
theorem B2000151 : Blo 1999435 2000151 := bstep (se 1 (by rfl) ⟨1500113, by rfl⟩ : syracuseStep 2000151 = 3000227) B3000227
theorem B16440853 : Blo 1999435 16440853 := bbase (se 6 (by rfl) ⟨385332, by rfl⟩ : syracuseStep 16440853 = 770665) (by norm_num)
theorem B21921137 : Blo 1999435 21921137 := bstep (se 2 (by rfl) ⟨8220426, by rfl⟩ : syracuseStep 21921137 = 16440853) B16440853
theorem B14614091 : Blo 1999435 14614091 := bstep (se 1 (by rfl) ⟨10960568, by rfl⟩ : syracuseStep 14614091 = 21921137) B21921137
theorem B9742727 : Blo 1999435 9742727 := bstep (se 1 (by rfl) ⟨7307045, by rfl⟩ : syracuseStep 9742727 = 14614091) B14614091
theorem B6495151 : Blo 1999435 6495151 := bstep (se 1 (by rfl) ⟨4871363, by rfl⟩ : syracuseStep 6495151 = 9742727) B9742727
theorem B8660201 : Blo 1999435 8660201 := bstep (se 2 (by rfl) ⟨3247575, by rfl⟩ : syracuseStep 8660201 = 6495151) B6495151
theorem B92375477 : Blo 1999435 92375477 := bstep (se 5 (by rfl) ⟨4330100, by rfl⟩ : syracuseStep 92375477 = 8660201) B8660201
theorem B61583651 : Blo 1999435 61583651 := bstep (se 1 (by rfl) ⟨46187738, by rfl⟩ : syracuseStep 61583651 = 92375477) B92375477
theorem B41055767 : Blo 1999435 41055767 := bstep (se 1 (by rfl) ⟨30791825, by rfl⟩ : syracuseStep 41055767 = 61583651) B61583651
theorem B27370511 : Blo 1999435 27370511 := bstep (se 1 (by rfl) ⟨20527883, by rfl⟩ : syracuseStep 27370511 = 41055767) B41055767
theorem B18247007 : Blo 1999435 18247007 := bstep (se 1 (by rfl) ⟨13685255, by rfl⟩ : syracuseStep 18247007 = 27370511) B27370511
theorem B12164671 : Blo 1999435 12164671 := bstep (se 1 (by rfl) ⟨9123503, by rfl⟩ : syracuseStep 12164671 = 18247007) B18247007
theorem B64878245 : Blo 1999435 64878245 := bstep (se 4 (by rfl) ⟨6082335, by rfl⟩ : syracuseStep 64878245 = 12164671) B12164671
theorem B43252163 : Blo 1999435 43252163 := bstep (se 1 (by rfl) ⟨32439122, by rfl⟩ : syracuseStep 43252163 = 64878245) B64878245
theorem B28834775 : Blo 1999435 28834775 := bstep (se 1 (by rfl) ⟨21626081, by rfl⟩ : syracuseStep 28834775 = 43252163) B43252163
theorem B19223183 : Blo 1999435 19223183 := bstep (se 1 (by rfl) ⟨14417387, by rfl⟩ : syracuseStep 19223183 = 28834775) B28834775
theorem B12815455 : Blo 1999435 12815455 := bstep (se 1 (by rfl) ⟨9611591, by rfl⟩ : syracuseStep 12815455 = 19223183) B19223183
theorem B17087273 : Blo 1999435 17087273 := bstep (se 2 (by rfl) ⟨6407727, by rfl⟩ : syracuseStep 17087273 = 12815455) B12815455
theorem B11391515 : Blo 1999435 11391515 := bstep (se 1 (by rfl) ⟨8543636, by rfl⟩ : syracuseStep 11391515 = 17087273) B17087273
theorem B7594343 : Blo 1999435 7594343 := bstep (se 1 (by rfl) ⟨5695757, by rfl⟩ : syracuseStep 7594343 = 11391515) B11391515
theorem B5062895 : Blo 1999435 5062895 := bstep (se 1 (by rfl) ⟨3797171, by rfl⟩ : syracuseStep 5062895 = 7594343) B7594343
theorem B3375263 : Blo 1999435 3375263 := bstep (se 1 (by rfl) ⟨2531447, by rfl⟩ : syracuseStep 3375263 = 5062895) B5062895
theorem B2250175 : Blo 1999435 2250175 := bstep (se 1 (by rfl) ⟨1687631, by rfl⟩ : syracuseStep 2250175 = 3375263) B3375263
theorem B3000233 : Blo 1999435 3000233 := bstep (se 2 (by rfl) ⟨1125087, by rfl⟩ : syracuseStep 3000233 = 2250175) B2250175
theorem B2000155 : Blo 1999435 2000155 := bstep (se 1 (by rfl) ⟨1500116, by rfl⟩ : syracuseStep 2000155 = 3000233) B3000233
theorem B7594357 : Blo 1999435 7594357 := bbase (se 5 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 7594357 = 711971) (by norm_num)
theorem B10125809 : Blo 1999435 10125809 := bstep (se 2 (by rfl) ⟨3797178, by rfl⟩ : syracuseStep 10125809 = 7594357) B7594357
theorem B6750539 : Blo 1999435 6750539 := bstep (se 1 (by rfl) ⟨5062904, by rfl⟩ : syracuseStep 6750539 = 10125809) B10125809
theorem B4500359 : Blo 1999435 4500359 := bstep (se 1 (by rfl) ⟨3375269, by rfl⟩ : syracuseStep 4500359 = 6750539) B6750539
theorem B3000239 : Blo 1999435 3000239 := bstep (se 1 (by rfl) ⟨2250179, by rfl⟩ : syracuseStep 3000239 = 4500359) B4500359
theorem B2000159 : Blo 1999435 2000159 := bstep (se 1 (by rfl) ⟨1500119, by rfl⟩ : syracuseStep 2000159 = 3000239) B3000239
theorem B3000245 : Blo 1999435 3000245 := bbase (se 5 (by rfl) ⟨140636, by rfl⟩ : syracuseStep 3000245 = 281273) (by norm_num)
theorem B2000163 : Blo 1999435 2000163 := bstep (se 1 (by rfl) ⟨1500122, by rfl⟩ : syracuseStep 2000163 = 3000245) B3000245
theorem B5062925 : Blo 1999435 5062925 := bbase (se 3 (by rfl) ⟨949298, by rfl⟩ : syracuseStep 5062925 = 1898597) (by norm_num)
theorem B3375283 : Blo 1999435 3375283 := bstep (se 1 (by rfl) ⟨2531462, by rfl⟩ : syracuseStep 3375283 = 5062925) B5062925
theorem B4500377 : Blo 1999435 4500377 := bstep (se 2 (by rfl) ⟨1687641, by rfl⟩ : syracuseStep 4500377 = 3375283) B3375283
theorem B3000251 : Blo 1999435 3000251 := bstep (se 1 (by rfl) ⟨2250188, by rfl⟩ : syracuseStep 3000251 = 4500377) B4500377
theorem B2000167 : Blo 1999435 2000167 := bstep (se 1 (by rfl) ⟨1500125, by rfl⟩ : syracuseStep 2000167 = 3000251) B3000251
theorem B2250193 : Blo 1999435 2250193 := bbase (se 2 (by rfl) ⟨843822, by rfl⟩ : syracuseStep 2250193 = 1687645) (by norm_num)
theorem B3000257 : Blo 1999435 3000257 := bstep (se 2 (by rfl) ⟨1125096, by rfl⟩ : syracuseStep 3000257 = 2250193) B2250193
theorem B2000171 : Blo 1999435 2000171 := bstep (se 1 (by rfl) ⟨1500128, by rfl⟩ : syracuseStep 2000171 = 3000257) B3000257
theorem B4271861 : Blo 1999435 4271861 := bbase (se 5 (by rfl) ⟨200243, by rfl⟩ : syracuseStep 4271861 = 400487) (by norm_num)
theorem B2847907 : Blo 1999435 2847907 := bstep (se 1 (by rfl) ⟨2135930, by rfl⟩ : syracuseStep 2847907 = 4271861) B4271861
theorem B3797209 : Blo 1999435 3797209 := bstep (se 2 (by rfl) ⟨1423953, by rfl⟩ : syracuseStep 3797209 = 2847907) B2847907
theorem B5062945 : Blo 1999435 5062945 := bstep (se 2 (by rfl) ⟨1898604, by rfl⟩ : syracuseStep 5062945 = 3797209) B3797209
theorem B6750593 : Blo 1999435 6750593 := bstep (se 2 (by rfl) ⟨2531472, by rfl⟩ : syracuseStep 6750593 = 5062945) B5062945
theorem B4500395 : Blo 1999435 4500395 := bstep (se 1 (by rfl) ⟨3375296, by rfl⟩ : syracuseStep 4500395 = 6750593) B6750593
theorem B3000263 : Blo 1999435 3000263 := bstep (se 1 (by rfl) ⟨2250197, by rfl⟩ : syracuseStep 3000263 = 4500395) B4500395
theorem B2000175 : Blo 1999435 2000175 := bstep (se 1 (by rfl) ⟨1500131, by rfl⟩ : syracuseStep 2000175 = 3000263) B3000263
theorem B3000269 : Blo 1999435 3000269 := bbase (se 3 (by rfl) ⟨562550, by rfl⟩ : syracuseStep 3000269 = 1125101) (by norm_num)
theorem B2000179 : Blo 1999435 2000179 := bstep (se 1 (by rfl) ⟨1500134, by rfl⟩ : syracuseStep 2000179 = 3000269) B3000269
theorem B4500413 : Blo 1999435 4500413 := bbase (se 3 (by rfl) ⟨843827, by rfl⟩ : syracuseStep 4500413 = 1687655) (by norm_num)
theorem B3000275 : Blo 1999435 3000275 := bstep (se 1 (by rfl) ⟨2250206, by rfl⟩ : syracuseStep 3000275 = 4500413) B4500413
theorem B2000183 : Blo 1999435 2000183 := bstep (se 1 (by rfl) ⟨1500137, by rfl⟩ : syracuseStep 2000183 = 3000275) B3000275
theorem B3375317 : Blo 1999435 3375317 := bbase (se 7 (by rfl) ⟨39554, by rfl⟩ : syracuseStep 3375317 = 79109) (by norm_num)
theorem B2250211 : Blo 1999435 2250211 := bstep (se 1 (by rfl) ⟨1687658, by rfl⟩ : syracuseStep 2250211 = 3375317) B3375317
theorem B3000281 : Blo 1999435 3000281 := bstep (se 2 (by rfl) ⟨1125105, by rfl⟩ : syracuseStep 3000281 = 2250211) B2250211
theorem B2000187 : Blo 1999435 2000187 := bstep (se 1 (by rfl) ⟨1500140, by rfl⟩ : syracuseStep 2000187 = 3000281) B3000281
theorem B2402941 : Blo 1999435 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B3203921 : Blo 1999435 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B8543789 : Blo 1999435 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B5695859 : Blo 1999435 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B15188957 : Blo 1999435 15188957 := bstep (se 3 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 15188957 = 5695859) B5695859
theorem B10125971 : Blo 1999435 10125971 := bstep (se 1 (by rfl) ⟨7594478, by rfl⟩ : syracuseStep 10125971 = 15188957) B15188957
theorem B6750647 : Blo 1999435 6750647 := bstep (se 1 (by rfl) ⟨5062985, by rfl⟩ : syracuseStep 6750647 = 10125971) B10125971
theorem B4500431 : Blo 1999435 4500431 := bstep (se 1 (by rfl) ⟨3375323, by rfl⟩ : syracuseStep 4500431 = 6750647) B6750647
theorem B3000287 : Blo 1999435 3000287 := bstep (se 1 (by rfl) ⟨2250215, by rfl⟩ : syracuseStep 3000287 = 4500431) B4500431
theorem B2000191 : Blo 1999435 2000191 := bstep (se 1 (by rfl) ⟨1500143, by rfl⟩ : syracuseStep 2000191 = 3000287) B3000287
theorem B3000293 : Blo 1999435 3000293 := bbase (se 4 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 3000293 = 562555) (by norm_num)
theorem B2000195 : Blo 1999435 2000195 := bstep (se 1 (by rfl) ⟨1500146, by rfl⟩ : syracuseStep 2000195 = 3000293) B3000293
theorem B4054981 : Blo 1999435 4054981 := bbase (se 4 (by rfl) ⟨380154, by rfl⟩ : syracuseStep 4054981 = 760309) (by norm_num)
theorem B5406641 : Blo 1999435 5406641 := bstep (se 2 (by rfl) ⟨2027490, by rfl⟩ : syracuseStep 5406641 = 4054981) B4054981
theorem B3604427 : Blo 1999435 3604427 := bstep (se 1 (by rfl) ⟨2703320, by rfl⟩ : syracuseStep 3604427 = 5406641) B5406641
theorem B2402951 : Blo 1999435 2402951 := bstep (se 1 (by rfl) ⟨1802213, by rfl⟩ : syracuseStep 2402951 = 3604427) B3604427
theorem B6407869 : Blo 1999435 6407869 := bstep (se 3 (by rfl) ⟨1201475, by rfl⟩ : syracuseStep 6407869 = 2402951) B2402951
theorem B8543825 : Blo 1999435 8543825 := bstep (se 2 (by rfl) ⟨3203934, by rfl⟩ : syracuseStep 8543825 = 6407869) B6407869
theorem B5695883 : Blo 1999435 5695883 := bstep (se 1 (by rfl) ⟨4271912, by rfl⟩ : syracuseStep 5695883 = 8543825) B8543825
theorem B3797255 : Blo 1999435 3797255 := bstep (se 1 (by rfl) ⟨2847941, by rfl⟩ : syracuseStep 3797255 = 5695883) B5695883
theorem B2531503 : Blo 1999435 2531503 := bstep (se 1 (by rfl) ⟨1898627, by rfl⟩ : syracuseStep 2531503 = 3797255) B3797255
theorem B3375337 : Blo 1999435 3375337 := bstep (se 2 (by rfl) ⟨1265751, by rfl⟩ : syracuseStep 3375337 = 2531503) B2531503
theorem B4500449 : Blo 1999435 4500449 := bstep (se 2 (by rfl) ⟨1687668, by rfl⟩ : syracuseStep 4500449 = 3375337) B3375337
theorem B3000299 : Blo 1999435 3000299 := bstep (se 1 (by rfl) ⟨2250224, by rfl⟩ : syracuseStep 3000299 = 4500449) B4500449
theorem B2000199 : Blo 1999435 2000199 := bstep (se 1 (by rfl) ⟨1500149, by rfl⟩ : syracuseStep 2000199 = 3000299) B3000299
theorem B2250229 : Blo 1999435 2250229 := bbase (se 5 (by rfl) ⟨105479, by rfl⟩ : syracuseStep 2250229 = 210959) (by norm_num)
theorem B3000305 : Blo 1999435 3000305 := bstep (se 2 (by rfl) ⟨1125114, by rfl⟩ : syracuseStep 3000305 = 2250229) B2250229
theorem B2000203 : Blo 1999435 2000203 := bstep (se 1 (by rfl) ⟨1500152, by rfl⟩ : syracuseStep 2000203 = 3000305) B3000305
theorem B2531513 : Blo 1999435 2531513 := bbase (se 2 (by rfl) ⟨949317, by rfl⟩ : syracuseStep 2531513 = 1898635) (by norm_num)
theorem B6750701 : Blo 1999435 6750701 := bstep (se 3 (by rfl) ⟨1265756, by rfl⟩ : syracuseStep 6750701 = 2531513) B2531513
theorem B4500467 : Blo 1999435 4500467 := bstep (se 1 (by rfl) ⟨3375350, by rfl⟩ : syracuseStep 4500467 = 6750701) B6750701
theorem B3000311 : Blo 1999435 3000311 := bstep (se 1 (by rfl) ⟨2250233, by rfl⟩ : syracuseStep 3000311 = 4500467) B4500467
theorem B2000207 : Blo 1999435 2000207 := bstep (se 1 (by rfl) ⟨1500155, by rfl⟩ : syracuseStep 2000207 = 3000311) B3000311
theorem B3000317 : Blo 1999435 3000317 := bbase (se 3 (by rfl) ⟨562559, by rfl⟩ : syracuseStep 3000317 = 1125119) (by norm_num)
theorem B2000211 : Blo 1999435 2000211 := bstep (se 1 (by rfl) ⟨1500158, by rfl⟩ : syracuseStep 2000211 = 3000317) B3000317
theorem B4500485 : Blo 1999435 4500485 := bbase (se 4 (by rfl) ⟨421920, by rfl⟩ : syracuseStep 4500485 = 843841) (by norm_num)
theorem B3000323 : Blo 1999435 3000323 := bstep (se 1 (by rfl) ⟨2250242, by rfl⟩ : syracuseStep 3000323 = 4500485) B4500485
theorem B2000215 : Blo 1999435 2000215 := bstep (se 1 (by rfl) ⟨1500161, by rfl⟩ : syracuseStep 2000215 = 3000323) B3000323
theorem B3797293 : Blo 1999435 3797293 := bbase (se 3 (by rfl) ⟨711992, by rfl⟩ : syracuseStep 3797293 = 1423985) (by norm_num)
theorem B5063057 : Blo 1999435 5063057 := bstep (se 2 (by rfl) ⟨1898646, by rfl⟩ : syracuseStep 5063057 = 3797293) B3797293
theorem B3375371 : Blo 1999435 3375371 := bstep (se 1 (by rfl) ⟨2531528, by rfl⟩ : syracuseStep 3375371 = 5063057) B5063057
theorem B2250247 : Blo 1999435 2250247 := bstep (se 1 (by rfl) ⟨1687685, by rfl⟩ : syracuseStep 2250247 = 3375371) B3375371
theorem B3000329 : Blo 1999435 3000329 := bstep (se 2 (by rfl) ⟨1125123, by rfl⟩ : syracuseStep 3000329 = 2250247) B2250247
theorem B2000219 : Blo 1999435 2000219 := bstep (se 1 (by rfl) ⟨1500164, by rfl⟩ : syracuseStep 2000219 = 3000329) B3000329
theorem B10126133 : Blo 1999435 10126133 := bbase (se 5 (by rfl) ⟨474662, by rfl⟩ : syracuseStep 10126133 = 949325) (by norm_num)
theorem B6750755 : Blo 1999435 6750755 := bstep (se 1 (by rfl) ⟨5063066, by rfl⟩ : syracuseStep 6750755 = 10126133) B10126133
theorem B4500503 : Blo 1999435 4500503 := bstep (se 1 (by rfl) ⟨3375377, by rfl⟩ : syracuseStep 4500503 = 6750755) B6750755
theorem B3000335 : Blo 1999435 3000335 := bstep (se 1 (by rfl) ⟨2250251, by rfl⟩ : syracuseStep 3000335 = 4500503) B4500503
theorem B2000223 : Blo 1999435 2000223 := bstep (se 1 (by rfl) ⟨1500167, by rfl⟩ : syracuseStep 2000223 = 3000335) B3000335
theorem B3000341 : Blo 1999435 3000341 := bbase (se 6 (by rfl) ⟨70320, by rfl⟩ : syracuseStep 3000341 = 140641) (by norm_num)
theorem B2000227 : Blo 1999435 2000227 := bstep (se 1 (by rfl) ⟨1500170, by rfl⟩ : syracuseStep 2000227 = 3000341) B3000341
theorem B2402989 : Blo 1999435 2402989 := bbase (se 3 (by rfl) ⟨450560, by rfl⟩ : syracuseStep 2402989 = 901121) (by norm_num)
theorem B12815941 : Blo 1999435 12815941 := bstep (se 4 (by rfl) ⟨1201494, by rfl⟩ : syracuseStep 12815941 = 2402989) B2402989
theorem B17087921 : Blo 1999435 17087921 := bstep (se 2 (by rfl) ⟨6407970, by rfl⟩ : syracuseStep 17087921 = 12815941) B12815941
theorem B11391947 : Blo 1999435 11391947 := bstep (se 1 (by rfl) ⟨8543960, by rfl⟩ : syracuseStep 11391947 = 17087921) B17087921
theorem B7594631 : Blo 1999435 7594631 := bstep (se 1 (by rfl) ⟨5695973, by rfl⟩ : syracuseStep 7594631 = 11391947) B11391947
theorem B5063087 : Blo 1999435 5063087 := bstep (se 1 (by rfl) ⟨3797315, by rfl⟩ : syracuseStep 5063087 = 7594631) B7594631
theorem B3375391 : Blo 1999435 3375391 := bstep (se 1 (by rfl) ⟨2531543, by rfl⟩ : syracuseStep 3375391 = 5063087) B5063087
theorem B4500521 : Blo 1999435 4500521 := bstep (se 2 (by rfl) ⟨1687695, by rfl⟩ : syracuseStep 4500521 = 3375391) B3375391
theorem B3000347 : Blo 1999435 3000347 := bstep (se 1 (by rfl) ⟨2250260, by rfl⟩ : syracuseStep 3000347 = 4500521) B4500521
theorem B2000231 : Blo 1999435 2000231 := bstep (se 1 (by rfl) ⟨1500173, by rfl⟩ : syracuseStep 2000231 = 3000347) B3000347
theorem B2250265 : Blo 1999435 2250265 := bbase (se 2 (by rfl) ⟨843849, by rfl⟩ : syracuseStep 2250265 = 1687699) (by norm_num)
theorem B3000353 : Blo 1999435 3000353 := bstep (se 2 (by rfl) ⟨1125132, by rfl⟩ : syracuseStep 3000353 = 2250265) B2250265
theorem B2000235 : Blo 1999435 2000235 := bstep (se 1 (by rfl) ⟨1500176, by rfl⟩ : syracuseStep 2000235 = 3000353) B3000353
theorem B7594661 : Blo 1999435 7594661 := bbase (se 4 (by rfl) ⟨711999, by rfl⟩ : syracuseStep 7594661 = 1423999) (by norm_num)
theorem B5063107 : Blo 1999435 5063107 := bstep (se 1 (by rfl) ⟨3797330, by rfl⟩ : syracuseStep 5063107 = 7594661) B7594661
theorem B6750809 : Blo 1999435 6750809 := bstep (se 2 (by rfl) ⟨2531553, by rfl⟩ : syracuseStep 6750809 = 5063107) B5063107
theorem B4500539 : Blo 1999435 4500539 := bstep (se 1 (by rfl) ⟨3375404, by rfl⟩ : syracuseStep 4500539 = 6750809) B6750809
theorem B3000359 : Blo 1999435 3000359 := bstep (se 1 (by rfl) ⟨2250269, by rfl⟩ : syracuseStep 3000359 = 4500539) B4500539
theorem B2000239 : Blo 1999435 2000239 := bstep (se 1 (by rfl) ⟨1500179, by rfl⟩ : syracuseStep 2000239 = 3000359) B3000359
theorem B3000365 : Blo 1999435 3000365 := bbase (se 3 (by rfl) ⟨562568, by rfl⟩ : syracuseStep 3000365 = 1125137) (by norm_num)
theorem B2000243 : Blo 1999435 2000243 := bstep (se 1 (by rfl) ⟨1500182, by rfl⟩ : syracuseStep 2000243 = 3000365) B3000365
theorem B4500557 : Blo 1999435 4500557 := bbase (se 3 (by rfl) ⟨843854, by rfl⟩ : syracuseStep 4500557 = 1687709) (by norm_num)
theorem B3000371 : Blo 1999435 3000371 := bstep (se 1 (by rfl) ⟨2250278, by rfl⟩ : syracuseStep 3000371 = 4500557) B4500557
theorem B2000247 : Blo 1999435 2000247 := bstep (se 1 (by rfl) ⟨1500185, by rfl⟩ : syracuseStep 2000247 = 3000371) B3000371
theorem B2531569 : Blo 1999435 2531569 := bbase (se 2 (by rfl) ⟨949338, by rfl⟩ : syracuseStep 2531569 = 1898677) (by norm_num)
theorem B3375425 : Blo 1999435 3375425 := bstep (se 2 (by rfl) ⟨1265784, by rfl⟩ : syracuseStep 3375425 = 2531569) B2531569
theorem B2250283 : Blo 1999435 2250283 := bstep (se 1 (by rfl) ⟨1687712, by rfl⟩ : syracuseStep 2250283 = 3375425) B3375425
theorem B3000377 : Blo 1999435 3000377 := bstep (se 2 (by rfl) ⟨1125141, by rfl⟩ : syracuseStep 3000377 = 2250283) B2250283
theorem B2000251 : Blo 1999435 2000251 := bstep (se 1 (by rfl) ⟨1500188, by rfl⟩ : syracuseStep 2000251 = 3000377) B3000377
theorem B7698341 : Blo 1999435 7698341 := bbase (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) (by norm_num)
theorem B20528909 : Blo 1999435 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B13685939 : Blo 1999435 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B9123959 : Blo 1999435 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B24330557 : Blo 1999435 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B16220371 : Blo 1999435 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B21627161 : Blo 1999435 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B14418107 : Blo 1999435 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B9612071 : Blo 1999435 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B6408047 : Blo 1999435 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B4272031 : Blo 1999435 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B22784165 : Blo 1999435 22784165 := bstep (se 4 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 22784165 = 4272031) B4272031
theorem B15189443 : Blo 1999435 15189443 := bstep (se 1 (by rfl) ⟨11392082, by rfl⟩ : syracuseStep 15189443 = 22784165) B22784165
theorem B10126295 : Blo 1999435 10126295 := bstep (se 1 (by rfl) ⟨7594721, by rfl⟩ : syracuseStep 10126295 = 15189443) B15189443
theorem B6750863 : Blo 1999435 6750863 := bstep (se 1 (by rfl) ⟨5063147, by rfl⟩ : syracuseStep 6750863 = 10126295) B10126295
theorem B4500575 : Blo 1999435 4500575 := bstep (se 1 (by rfl) ⟨3375431, by rfl⟩ : syracuseStep 4500575 = 6750863) B6750863
theorem B3000383 : Blo 1999435 3000383 := bstep (se 1 (by rfl) ⟨2250287, by rfl⟩ : syracuseStep 3000383 = 4500575) B4500575
theorem B2000255 : Blo 1999435 2000255 := bstep (se 1 (by rfl) ⟨1500191, by rfl⟩ : syracuseStep 2000255 = 3000383) B3000383
theorem B3000389 : Blo 1999435 3000389 := bbase (se 4 (by rfl) ⟨281286, by rfl⟩ : syracuseStep 3000389 = 562573) (by norm_num)
theorem B2000259 : Blo 1999435 2000259 := bstep (se 1 (by rfl) ⟨1500194, by rfl⟩ : syracuseStep 2000259 = 3000389) B3000389
theorem B3375445 : Blo 1999435 3375445 := bbase (se 10 (by rfl) ⟨4944, by rfl⟩ : syracuseStep 3375445 = 9889) (by norm_num)
theorem B4500593 : Blo 1999435 4500593 := bstep (se 2 (by rfl) ⟨1687722, by rfl⟩ : syracuseStep 4500593 = 3375445) B3375445
theorem B3000395 : Blo 1999435 3000395 := bstep (se 1 (by rfl) ⟨2250296, by rfl⟩ : syracuseStep 3000395 = 4500593) B4500593
theorem B2000263 : Blo 1999435 2000263 := bstep (se 1 (by rfl) ⟨1500197, by rfl⟩ : syracuseStep 2000263 = 3000395) B3000395
theorem B2250301 : Blo 1999435 2250301 := bbase (se 3 (by rfl) ⟨421931, by rfl⟩ : syracuseStep 2250301 = 843863) (by norm_num)
theorem B3000401 : Blo 1999435 3000401 := bstep (se 2 (by rfl) ⟨1125150, by rfl⟩ : syracuseStep 3000401 = 2250301) B2250301
theorem B2000267 : Blo 1999435 2000267 := bstep (se 1 (by rfl) ⟨1500200, by rfl⟩ : syracuseStep 2000267 = 3000401) B3000401
theorem B6750917 : Blo 1999435 6750917 := bbase (se 4 (by rfl) ⟨632898, by rfl⟩ : syracuseStep 6750917 = 1265797) (by norm_num)
theorem B4500611 : Blo 1999435 4500611 := bstep (se 1 (by rfl) ⟨3375458, by rfl⟩ : syracuseStep 4500611 = 6750917) B6750917
theorem B3000407 : Blo 1999435 3000407 := bstep (se 1 (by rfl) ⟨2250305, by rfl⟩ : syracuseStep 3000407 = 4500611) B4500611
theorem B2000271 : Blo 1999435 2000271 := bstep (se 1 (by rfl) ⟨1500203, by rfl⟩ : syracuseStep 2000271 = 3000407) B3000407
theorem B3000413 : Blo 1999435 3000413 := bbase (se 3 (by rfl) ⟨562577, by rfl⟩ : syracuseStep 3000413 = 1125155) (by norm_num)
theorem B2000275 : Blo 1999435 2000275 := bstep (se 1 (by rfl) ⟨1500206, by rfl⟩ : syracuseStep 2000275 = 3000413) B3000413
theorem B4500629 : Blo 1999435 4500629 := bbase (se 6 (by rfl) ⟨105483, by rfl⟩ : syracuseStep 4500629 = 210967) (by norm_num)
theorem B3000419 : Blo 1999435 3000419 := bstep (se 1 (by rfl) ⟨2250314, by rfl⟩ : syracuseStep 3000419 = 4500629) B4500629
theorem B2000279 : Blo 1999435 2000279 := bstep (se 1 (by rfl) ⟨1500209, by rfl⟩ : syracuseStep 2000279 = 3000419) B3000419
theorem B2848061 : Blo 1999435 2848061 := bbase (se 3 (by rfl) ⟨534011, by rfl⟩ : syracuseStep 2848061 = 1068023) (by norm_num)
theorem B7594829 : Blo 1999435 7594829 := bstep (se 3 (by rfl) ⟨1424030, by rfl⟩ : syracuseStep 7594829 = 2848061) B2848061
theorem B5063219 : Blo 1999435 5063219 := bstep (se 1 (by rfl) ⟨3797414, by rfl⟩ : syracuseStep 5063219 = 7594829) B7594829
theorem B3375479 : Blo 1999435 3375479 := bstep (se 1 (by rfl) ⟨2531609, by rfl⟩ : syracuseStep 3375479 = 5063219) B5063219
theorem B2250319 : Blo 1999435 2250319 := bstep (se 1 (by rfl) ⟨1687739, by rfl⟩ : syracuseStep 2250319 = 3375479) B3375479
theorem B3000425 : Blo 1999435 3000425 := bstep (se 2 (by rfl) ⟨1125159, by rfl⟩ : syracuseStep 3000425 = 2250319) B2250319
theorem B2000283 : Blo 1999435 2000283 := bstep (se 1 (by rfl) ⟨1500212, by rfl⟩ : syracuseStep 2000283 = 3000425) B3000425
theorem B8660773 : Blo 1999435 8660773 := bbase (se 4 (by rfl) ⟨811947, by rfl⟩ : syracuseStep 8660773 = 1623895) (by norm_num)
theorem B11547697 : Blo 1999435 11547697 := bstep (se 2 (by rfl) ⟨4330386, by rfl⟩ : syracuseStep 11547697 = 8660773) B8660773
theorem B15396929 : Blo 1999435 15396929 := bstep (se 2 (by rfl) ⟨5773848, by rfl⟩ : syracuseStep 15396929 = 11547697) B11547697
theorem B10264619 : Blo 1999435 10264619 := bstep (se 1 (by rfl) ⟨7698464, by rfl⟩ : syracuseStep 10264619 = 15396929) B15396929
theorem B6843079 : Blo 1999435 6843079 := bstep (se 1 (by rfl) ⟨5132309, by rfl⟩ : syracuseStep 6843079 = 10264619) B10264619
theorem B9124105 : Blo 1999435 9124105 := bstep (se 2 (by rfl) ⟨3421539, by rfl⟩ : syracuseStep 9124105 = 6843079) B6843079
theorem B12165473 : Blo 1999435 12165473 := bstep (se 2 (by rfl) ⟨4562052, by rfl⟩ : syracuseStep 12165473 = 9124105) B9124105
theorem B8110315 : Blo 1999435 8110315 := bstep (se 1 (by rfl) ⟨6082736, by rfl⟩ : syracuseStep 8110315 = 12165473) B12165473
theorem B10813753 : Blo 1999435 10813753 := bstep (se 2 (by rfl) ⟨4055157, by rfl⟩ : syracuseStep 10813753 = 8110315) B8110315
theorem B14418337 : Blo 1999435 14418337 := bstep (se 2 (by rfl) ⟨5406876, by rfl⟩ : syracuseStep 14418337 = 10813753) B10813753
theorem B19224449 : Blo 1999435 19224449 := bstep (se 2 (by rfl) ⟨7209168, by rfl⟩ : syracuseStep 19224449 = 14418337) B14418337
theorem B12816299 : Blo 1999435 12816299 := bstep (se 1 (by rfl) ⟨9612224, by rfl⟩ : syracuseStep 12816299 = 19224449) B19224449
theorem B8544199 : Blo 1999435 8544199 := bstep (se 1 (by rfl) ⟨6408149, by rfl⟩ : syracuseStep 8544199 = 12816299) B12816299
theorem B11392265 : Blo 1999435 11392265 := bstep (se 2 (by rfl) ⟨4272099, by rfl⟩ : syracuseStep 11392265 = 8544199) B8544199
theorem B7594843 : Blo 1999435 7594843 := bstep (se 1 (by rfl) ⟨5696132, by rfl⟩ : syracuseStep 7594843 = 11392265) B11392265
theorem B10126457 : Blo 1999435 10126457 := bstep (se 2 (by rfl) ⟨3797421, by rfl⟩ : syracuseStep 10126457 = 7594843) B7594843
theorem B6750971 : Blo 1999435 6750971 := bstep (se 1 (by rfl) ⟨5063228, by rfl⟩ : syracuseStep 6750971 = 10126457) B10126457
theorem B4500647 : Blo 1999435 4500647 := bstep (se 1 (by rfl) ⟨3375485, by rfl⟩ : syracuseStep 4500647 = 6750971) B6750971
theorem B3000431 : Blo 1999435 3000431 := bstep (se 1 (by rfl) ⟨2250323, by rfl⟩ : syracuseStep 3000431 = 4500647) B4500647
theorem B2000287 : Blo 1999435 2000287 := bstep (se 1 (by rfl) ⟨1500215, by rfl⟩ : syracuseStep 2000287 = 3000431) B3000431
theorem B3000437 : Blo 1999435 3000437 := bbase (se 5 (by rfl) ⟨140645, by rfl⟩ : syracuseStep 3000437 = 281291) (by norm_num)
theorem B2000291 : Blo 1999435 2000291 := bstep (se 1 (by rfl) ⟨1500218, by rfl⟩ : syracuseStep 2000291 = 3000437) B3000437
theorem B3797437 : Blo 1999435 3797437 := bbase (se 3 (by rfl) ⟨712019, by rfl⟩ : syracuseStep 3797437 = 1424039) (by norm_num)
theorem B5063249 : Blo 1999435 5063249 := bstep (se 2 (by rfl) ⟨1898718, by rfl⟩ : syracuseStep 5063249 = 3797437) B3797437
theorem B3375499 : Blo 1999435 3375499 := bstep (se 1 (by rfl) ⟨2531624, by rfl⟩ : syracuseStep 3375499 = 5063249) B5063249
theorem B4500665 : Blo 1999435 4500665 := bstep (se 2 (by rfl) ⟨1687749, by rfl⟩ : syracuseStep 4500665 = 3375499) B3375499
theorem B3000443 : Blo 1999435 3000443 := bstep (se 1 (by rfl) ⟨2250332, by rfl⟩ : syracuseStep 3000443 = 4500665) B4500665
theorem B2000295 : Blo 1999435 2000295 := bstep (se 1 (by rfl) ⟨1500221, by rfl⟩ : syracuseStep 2000295 = 3000443) B3000443
theorem B2250337 : Blo 1999435 2250337 := bbase (se 2 (by rfl) ⟨843876, by rfl⟩ : syracuseStep 2250337 = 1687753) (by norm_num)
theorem B3000449 : Blo 1999435 3000449 := bstep (se 2 (by rfl) ⟨1125168, by rfl⟩ : syracuseStep 3000449 = 2250337) B2250337
theorem B2000299 : Blo 1999435 2000299 := bstep (se 1 (by rfl) ⟨1500224, by rfl⟩ : syracuseStep 2000299 = 3000449) B3000449
theorem B5063269 : Blo 1999435 5063269 := bbase (se 4 (by rfl) ⟨474681, by rfl⟩ : syracuseStep 5063269 = 949363) (by norm_num)
theorem B6751025 : Blo 1999435 6751025 := bstep (se 2 (by rfl) ⟨2531634, by rfl⟩ : syracuseStep 6751025 = 5063269) B5063269
theorem B4500683 : Blo 1999435 4500683 := bstep (se 1 (by rfl) ⟨3375512, by rfl⟩ : syracuseStep 4500683 = 6751025) B6751025
theorem B3000455 : Blo 1999435 3000455 := bstep (se 1 (by rfl) ⟨2250341, by rfl⟩ : syracuseStep 3000455 = 4500683) B4500683
theorem B2000303 : Blo 1999435 2000303 := bstep (se 1 (by rfl) ⟨1500227, by rfl⟩ : syracuseStep 2000303 = 3000455) B3000455
theorem B3000461 : Blo 1999435 3000461 := bbase (se 3 (by rfl) ⟨562586, by rfl⟩ : syracuseStep 3000461 = 1125173) (by norm_num)
theorem B2000307 : Blo 1999435 2000307 := bstep (se 1 (by rfl) ⟨1500230, by rfl⟩ : syracuseStep 2000307 = 3000461) B3000461
theorem B4500701 : Blo 1999435 4500701 := bbase (se 3 (by rfl) ⟨843881, by rfl⟩ : syracuseStep 4500701 = 1687763) (by norm_num)
theorem B3000467 : Blo 1999435 3000467 := bstep (se 1 (by rfl) ⟨2250350, by rfl⟩ : syracuseStep 3000467 = 4500701) B4500701
theorem B2000311 : Blo 1999435 2000311 := bstep (se 1 (by rfl) ⟨1500233, by rfl⟩ : syracuseStep 2000311 = 3000467) B3000467
theorem B3375533 : Blo 1999435 3375533 := bbase (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) (by norm_num)
theorem B2250355 : Blo 1999435 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B3000473 : Blo 1999435 3000473 := bstep (se 2 (by rfl) ⟨1125177, by rfl⟩ : syracuseStep 3000473 = 2250355) B2250355
theorem B2000315 : Blo 1999435 2000315 := bstep (se 1 (by rfl) ⟨1500236, by rfl⟩ : syracuseStep 2000315 = 3000473) B3000473
theorem B2435881 : Blo 1999435 2435881 := bbase (se 2 (by rfl) ⟨913455, by rfl⟩ : syracuseStep 2435881 = 1826911) (by norm_num)
theorem B3247841 : Blo 1999435 3247841 := bstep (se 2 (by rfl) ⟨1217940, by rfl⟩ : syracuseStep 3247841 = 2435881) B2435881
theorem B8660909 : Blo 1999435 8660909 := bstep (se 3 (by rfl) ⟨1623920, by rfl⟩ : syracuseStep 8660909 = 3247841) B3247841
theorem B23095757 : Blo 1999435 23095757 := bstep (se 3 (by rfl) ⟨4330454, by rfl⟩ : syracuseStep 23095757 = 8660909) B8660909
theorem B15397171 : Blo 1999435 15397171 := bstep (se 1 (by rfl) ⟨11547878, by rfl⟩ : syracuseStep 15397171 = 23095757) B23095757
theorem B328472981 : Blo 1999435 328472981 := bstep (se 6 (by rfl) ⟨7698585, by rfl⟩ : syracuseStep 328472981 = 15397171) B15397171
theorem B218981987 : Blo 1999435 218981987 := bstep (se 1 (by rfl) ⟨164236490, by rfl⟩ : syracuseStep 218981987 = 328472981) B328472981
theorem B145987991 : Blo 1999435 145987991 := bstep (se 1 (by rfl) ⟨109490993, by rfl⟩ : syracuseStep 145987991 = 218981987) B218981987
theorem B97325327 : Blo 1999435 97325327 := bstep (se 1 (by rfl) ⟨72993995, by rfl⟩ : syracuseStep 97325327 = 145987991) B145987991
theorem B64883551 : Blo 1999435 64883551 := bstep (se 1 (by rfl) ⟨48662663, by rfl⟩ : syracuseStep 64883551 = 97325327) B97325327
theorem B86511401 : Blo 1999435 86511401 := bstep (se 2 (by rfl) ⟨32441775, by rfl⟩ : syracuseStep 86511401 = 64883551) B64883551
theorem B57674267 : Blo 1999435 57674267 := bstep (se 1 (by rfl) ⟨43255700, by rfl⟩ : syracuseStep 57674267 = 86511401) B86511401
theorem B38449511 : Blo 1999435 38449511 := bstep (se 1 (by rfl) ⟨28837133, by rfl⟩ : syracuseStep 38449511 = 57674267) B57674267
theorem B25633007 : Blo 1999435 25633007 := bstep (se 1 (by rfl) ⟨19224755, by rfl⟩ : syracuseStep 25633007 = 38449511) B38449511
theorem B17088671 : Blo 1999435 17088671 := bstep (se 1 (by rfl) ⟨12816503, by rfl⟩ : syracuseStep 17088671 = 25633007) B25633007
theorem B11392447 : Blo 1999435 11392447 := bstep (se 1 (by rfl) ⟨8544335, by rfl⟩ : syracuseStep 11392447 = 17088671) B17088671
theorem B15189929 : Blo 1999435 15189929 := bstep (se 2 (by rfl) ⟨5696223, by rfl⟩ : syracuseStep 15189929 = 11392447) B11392447
theorem B10126619 : Blo 1999435 10126619 := bstep (se 1 (by rfl) ⟨7594964, by rfl⟩ : syracuseStep 10126619 = 15189929) B15189929
theorem B6751079 : Blo 1999435 6751079 := bstep (se 1 (by rfl) ⟨5063309, by rfl⟩ : syracuseStep 6751079 = 10126619) B10126619
theorem B4500719 : Blo 1999435 4500719 := bstep (se 1 (by rfl) ⟨3375539, by rfl⟩ : syracuseStep 4500719 = 6751079) B6751079
theorem B3000479 : Blo 1999435 3000479 := bstep (se 1 (by rfl) ⟨2250359, by rfl⟩ : syracuseStep 3000479 = 4500719) B4500719
theorem B2000319 : Blo 1999435 2000319 := bstep (se 1 (by rfl) ⟨1500239, by rfl⟩ : syracuseStep 2000319 = 3000479) B3000479
theorem B3000485 : Blo 1999435 3000485 := bbase (se 4 (by rfl) ⟨281295, by rfl⟩ : syracuseStep 3000485 = 562591) (by norm_num)
theorem B2000323 : Blo 1999435 2000323 := bstep (se 1 (by rfl) ⟨1500242, by rfl⟩ : syracuseStep 2000323 = 3000485) B3000485
theorem B2531665 : Blo 1999435 2531665 := bbase (se 2 (by rfl) ⟨949374, by rfl⟩ : syracuseStep 2531665 = 1898749) (by norm_num)
theorem B3375553 : Blo 1999435 3375553 := bstep (se 2 (by rfl) ⟨1265832, by rfl⟩ : syracuseStep 3375553 = 2531665) B2531665
theorem B4500737 : Blo 1999435 4500737 := bstep (se 2 (by rfl) ⟨1687776, by rfl⟩ : syracuseStep 4500737 = 3375553) B3375553
theorem B3000491 : Blo 1999435 3000491 := bstep (se 1 (by rfl) ⟨2250368, by rfl⟩ : syracuseStep 3000491 = 4500737) B4500737
theorem B2000327 : Blo 1999435 2000327 := bstep (se 1 (by rfl) ⟨1500245, by rfl⟩ : syracuseStep 2000327 = 3000491) B3000491
theorem B2250373 : Blo 1999435 2250373 := bbase (se 4 (by rfl) ⟨210972, by rfl⟩ : syracuseStep 2250373 = 421945) (by norm_num)
theorem B3000497 : Blo 1999435 3000497 := bstep (se 2 (by rfl) ⟨1125186, by rfl⟩ : syracuseStep 3000497 = 2250373) B2250373
theorem B2000331 : Blo 1999435 2000331 := bstep (se 1 (by rfl) ⟨1500248, by rfl⟩ : syracuseStep 2000331 = 3000497) B3000497
theorem B4806229 : Blo 1999435 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B6408305 : Blo 1999435 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B4272203 : Blo 1999435 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B2848135 : Blo 1999435 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B3797513 : Blo 1999435 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B2531675 : Blo 1999435 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B6751133 : Blo 1999435 6751133 := bstep (se 3 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 6751133 = 2531675) B2531675
theorem B4500755 : Blo 1999435 4500755 := bstep (se 1 (by rfl) ⟨3375566, by rfl⟩ : syracuseStep 4500755 = 6751133) B6751133
theorem B3000503 : Blo 1999435 3000503 := bstep (se 1 (by rfl) ⟨2250377, by rfl⟩ : syracuseStep 3000503 = 4500755) B4500755
theorem B2000335 : Blo 1999435 2000335 := bstep (se 1 (by rfl) ⟨1500251, by rfl⟩ : syracuseStep 2000335 = 3000503) B3000503
theorem B3000509 : Blo 1999435 3000509 := bbase (se 3 (by rfl) ⟨562595, by rfl⟩ : syracuseStep 3000509 = 1125191) (by norm_num)
theorem B2000339 : Blo 1999435 2000339 := bstep (se 1 (by rfl) ⟨1500254, by rfl⟩ : syracuseStep 2000339 = 3000509) B3000509
theorem B4500773 : Blo 1999435 4500773 := bbase (se 4 (by rfl) ⟨421947, by rfl⟩ : syracuseStep 4500773 = 843895) (by norm_num)
theorem B3000515 : Blo 1999435 3000515 := bstep (se 1 (by rfl) ⟨2250386, by rfl⟩ : syracuseStep 3000515 = 4500773) B4500773
theorem B2000343 : Blo 1999435 2000343 := bstep (se 1 (by rfl) ⟨1500257, by rfl⟩ : syracuseStep 2000343 = 3000515) B3000515
theorem B5063381 : Blo 1999435 5063381 := bbase (se 7 (by rfl) ⟨59336, by rfl⟩ : syracuseStep 5063381 = 118673) (by norm_num)
theorem B3375587 : Blo 1999435 3375587 := bstep (se 1 (by rfl) ⟨2531690, by rfl⟩ : syracuseStep 3375587 = 5063381) B5063381
theorem B2250391 : Blo 1999435 2250391 := bstep (se 1 (by rfl) ⟨1687793, by rfl⟩ : syracuseStep 2250391 = 3375587) B3375587
theorem B3000521 : Blo 1999435 3000521 := bstep (se 2 (by rfl) ⟨1125195, by rfl⟩ : syracuseStep 3000521 = 2250391) B2250391
theorem B2000347 : Blo 1999435 2000347 := bstep (se 1 (by rfl) ⟨1500260, by rfl⟩ : syracuseStep 2000347 = 3000521) B3000521
theorem B9612533 : Blo 1999435 9612533 := bbase (se 5 (by rfl) ⟨450587, by rfl⟩ : syracuseStep 9612533 = 901175) (by norm_num)
theorem B6408355 : Blo 1999435 6408355 := bstep (se 1 (by rfl) ⟨4806266, by rfl⟩ : syracuseStep 6408355 = 9612533) B9612533
theorem B8544473 : Blo 1999435 8544473 := bstep (se 2 (by rfl) ⟨3204177, by rfl⟩ : syracuseStep 8544473 = 6408355) B6408355
theorem B5696315 : Blo 1999435 5696315 := bstep (se 1 (by rfl) ⟨4272236, by rfl⟩ : syracuseStep 5696315 = 8544473) B8544473
theorem B3797543 : Blo 1999435 3797543 := bstep (se 1 (by rfl) ⟨2848157, by rfl⟩ : syracuseStep 3797543 = 5696315) B5696315
theorem B10126781 : Blo 1999435 10126781 := bstep (se 3 (by rfl) ⟨1898771, by rfl⟩ : syracuseStep 10126781 = 3797543) B3797543
theorem B6751187 : Blo 1999435 6751187 := bstep (se 1 (by rfl) ⟨5063390, by rfl⟩ : syracuseStep 6751187 = 10126781) B10126781
theorem B4500791 : Blo 1999435 4500791 := bstep (se 1 (by rfl) ⟨3375593, by rfl⟩ : syracuseStep 4500791 = 6751187) B6751187
theorem B3000527 : Blo 1999435 3000527 := bstep (se 1 (by rfl) ⟨2250395, by rfl⟩ : syracuseStep 3000527 = 4500791) B4500791
theorem B2000351 : Blo 1999435 2000351 := bstep (se 1 (by rfl) ⟨1500263, by rfl⟩ : syracuseStep 2000351 = 3000527) B3000527
theorem B3000533 : Blo 1999435 3000533 := bbase (se 7 (by rfl) ⟨35162, by rfl⟩ : syracuseStep 3000533 = 70325) (by norm_num)
theorem B2000355 : Blo 1999435 2000355 := bstep (se 1 (by rfl) ⟨1500266, by rfl⟩ : syracuseStep 2000355 = 3000533) B3000533
theorem B3849373 : Blo 1999435 3849373 := bbase (se 3 (by rfl) ⟨721757, by rfl⟩ : syracuseStep 3849373 = 1443515) (by norm_num)
theorem B5132497 : Blo 1999435 5132497 := bstep (se 2 (by rfl) ⟨1924686, by rfl⟩ : syracuseStep 5132497 = 3849373) B3849373
theorem B6843329 : Blo 1999435 6843329 := bstep (se 2 (by rfl) ⟨2566248, by rfl⟩ : syracuseStep 6843329 = 5132497) B5132497
theorem B4562219 : Blo 1999435 4562219 := bstep (se 1 (by rfl) ⟨3421664, by rfl⟩ : syracuseStep 4562219 = 6843329) B6843329
theorem B3041479 : Blo 1999435 3041479 := bstep (se 1 (by rfl) ⟨2281109, by rfl⟩ : syracuseStep 3041479 = 4562219) B4562219
theorem B16221221 : Blo 1999435 16221221 := bstep (se 4 (by rfl) ⟨1520739, by rfl⟩ : syracuseStep 16221221 = 3041479) B3041479
theorem B10814147 : Blo 1999435 10814147 := bstep (se 1 (by rfl) ⟨8110610, by rfl⟩ : syracuseStep 10814147 = 16221221) B16221221
theorem B7209431 : Blo 1999435 7209431 := bstep (se 1 (by rfl) ⟨5407073, by rfl⟩ : syracuseStep 7209431 = 10814147) B10814147
theorem B4806287 : Blo 1999435 4806287 := bstep (se 1 (by rfl) ⟨3604715, by rfl⟩ : syracuseStep 4806287 = 7209431) B7209431
theorem B3204191 : Blo 1999435 3204191 := bstep (se 1 (by rfl) ⟨2403143, by rfl⟩ : syracuseStep 3204191 = 4806287) B4806287
theorem B2136127 : Blo 1999435 2136127 := bstep (se 1 (by rfl) ⟨1602095, by rfl⟩ : syracuseStep 2136127 = 3204191) B3204191
theorem B2848169 : Blo 1999435 2848169 := bstep (se 2 (by rfl) ⟨1068063, by rfl⟩ : syracuseStep 2848169 = 2136127) B2136127
theorem B7595117 : Blo 1999435 7595117 := bstep (se 3 (by rfl) ⟨1424084, by rfl⟩ : syracuseStep 7595117 = 2848169) B2848169
theorem B5063411 : Blo 1999435 5063411 := bstep (se 1 (by rfl) ⟨3797558, by rfl⟩ : syracuseStep 5063411 = 7595117) B7595117
theorem B3375607 : Blo 1999435 3375607 := bstep (se 1 (by rfl) ⟨2531705, by rfl⟩ : syracuseStep 3375607 = 5063411) B5063411
theorem B4500809 : Blo 1999435 4500809 := bstep (se 2 (by rfl) ⟨1687803, by rfl⟩ : syracuseStep 4500809 = 3375607) B3375607
theorem B3000539 : Blo 1999435 3000539 := bstep (se 1 (by rfl) ⟨2250404, by rfl⟩ : syracuseStep 3000539 = 4500809) B4500809
theorem B2000359 : Blo 1999435 2000359 := bstep (se 1 (by rfl) ⟨1500269, by rfl⟩ : syracuseStep 2000359 = 3000539) B3000539
theorem B2250409 : Blo 1999435 2250409 := bbase (se 2 (by rfl) ⟨843903, by rfl⟩ : syracuseStep 2250409 = 1687807) (by norm_num)
theorem B3000545 : Blo 1999435 3000545 := bstep (se 2 (by rfl) ⟨1125204, by rfl⟩ : syracuseStep 3000545 = 2250409) B2250409
theorem B2000363 : Blo 1999435 2000363 := bstep (se 1 (by rfl) ⟨1500272, by rfl⟩ : syracuseStep 2000363 = 3000545) B3000545
theorem B4562237 : Blo 1999435 4562237 := bbase (se 3 (by rfl) ⟨855419, by rfl⟩ : syracuseStep 4562237 = 1710839) (by norm_num)
theorem B3041491 : Blo 1999435 3041491 := bstep (se 1 (by rfl) ⟨2281118, by rfl⟩ : syracuseStep 3041491 = 4562237) B4562237
theorem B4055321 : Blo 1999435 4055321 := bstep (se 2 (by rfl) ⟨1520745, by rfl⟩ : syracuseStep 4055321 = 3041491) B3041491
theorem B2703547 : Blo 1999435 2703547 := bstep (se 1 (by rfl) ⟨2027660, by rfl⟩ : syracuseStep 2703547 = 4055321) B4055321
theorem B3604729 : Blo 1999435 3604729 := bstep (se 2 (by rfl) ⟨1351773, by rfl⟩ : syracuseStep 3604729 = 2703547) B2703547
theorem B4806305 : Blo 1999435 4806305 := bstep (se 2 (by rfl) ⟨1802364, by rfl⟩ : syracuseStep 4806305 = 3604729) B3604729
theorem B3204203 : Blo 1999435 3204203 := bstep (se 1 (by rfl) ⟨2403152, by rfl⟩ : syracuseStep 3204203 = 4806305) B4806305
theorem B8544541 : Blo 1999435 8544541 := bstep (se 3 (by rfl) ⟨1602101, by rfl⟩ : syracuseStep 8544541 = 3204203) B3204203
theorem B11392721 : Blo 1999435 11392721 := bstep (se 2 (by rfl) ⟨4272270, by rfl⟩ : syracuseStep 11392721 = 8544541) B8544541
theorem B7595147 : Blo 1999435 7595147 := bstep (se 1 (by rfl) ⟨5696360, by rfl⟩ : syracuseStep 7595147 = 11392721) B11392721
theorem B5063431 : Blo 1999435 5063431 := bstep (se 1 (by rfl) ⟨3797573, by rfl⟩ : syracuseStep 5063431 = 7595147) B7595147
theorem B6751241 : Blo 1999435 6751241 := bstep (se 2 (by rfl) ⟨2531715, by rfl⟩ : syracuseStep 6751241 = 5063431) B5063431
theorem B4500827 : Blo 1999435 4500827 := bstep (se 1 (by rfl) ⟨3375620, by rfl⟩ : syracuseStep 4500827 = 6751241) B6751241
theorem B3000551 : Blo 1999435 3000551 := bstep (se 1 (by rfl) ⟨2250413, by rfl⟩ : syracuseStep 3000551 = 4500827) B4500827
theorem B2000367 : Blo 1999435 2000367 := bstep (se 1 (by rfl) ⟨1500275, by rfl⟩ : syracuseStep 2000367 = 3000551) B3000551
theorem B3000557 : Blo 1999435 3000557 := bbase (se 3 (by rfl) ⟨562604, by rfl⟩ : syracuseStep 3000557 = 1125209) (by norm_num)
theorem B2000371 : Blo 1999435 2000371 := bstep (se 1 (by rfl) ⟨1500278, by rfl⟩ : syracuseStep 2000371 = 3000557) B3000557
theorem B4500845 : Blo 1999435 4500845 := bbase (se 3 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 4500845 = 1687817) (by norm_num)
theorem B3000563 : Blo 1999435 3000563 := bstep (se 1 (by rfl) ⟨2250422, by rfl⟩ : syracuseStep 3000563 = 4500845) B4500845
theorem B2000375 : Blo 1999435 2000375 := bstep (se 1 (by rfl) ⟨1500281, by rfl⟩ : syracuseStep 2000375 = 3000563) B3000563
theorem B3797597 : Blo 1999435 3797597 := bbase (se 3 (by rfl) ⟨712049, by rfl⟩ : syracuseStep 3797597 = 1424099) (by norm_num)
theorem B2531731 : Blo 1999435 2531731 := bstep (se 1 (by rfl) ⟨1898798, by rfl⟩ : syracuseStep 2531731 = 3797597) B3797597
theorem B3375641 : Blo 1999435 3375641 := bstep (se 2 (by rfl) ⟨1265865, by rfl⟩ : syracuseStep 3375641 = 2531731) B2531731
theorem B2250427 : Blo 1999435 2250427 := bstep (se 1 (by rfl) ⟨1687820, by rfl⟩ : syracuseStep 2250427 = 3375641) B3375641
theorem B3000569 : Blo 1999435 3000569 := bstep (se 2 (by rfl) ⟨1125213, by rfl⟩ : syracuseStep 3000569 = 2250427) B2250427
theorem B2000379 : Blo 1999435 2000379 := bstep (se 1 (by rfl) ⟨1500284, by rfl⟩ : syracuseStep 2000379 = 3000569) B3000569
theorem B3604757 : Blo 1999435 3604757 := bbase (se 6 (by rfl) ⟨84486, by rfl⟩ : syracuseStep 3604757 = 168973) (by norm_num)
theorem B9612685 : Blo 1999435 9612685 := bstep (se 3 (by rfl) ⟨1802378, by rfl⟩ : syracuseStep 9612685 = 3604757) B3604757
theorem B51267653 : Blo 1999435 51267653 := bstep (se 4 (by rfl) ⟨4806342, by rfl⟩ : syracuseStep 51267653 = 9612685) B9612685
theorem B34178435 : Blo 1999435 34178435 := bstep (se 1 (by rfl) ⟨25633826, by rfl⟩ : syracuseStep 34178435 = 51267653) B51267653
theorem B22785623 : Blo 1999435 22785623 := bstep (se 1 (by rfl) ⟨17089217, by rfl⟩ : syracuseStep 22785623 = 34178435) B34178435
theorem B15190415 : Blo 1999435 15190415 := bstep (se 1 (by rfl) ⟨11392811, by rfl⟩ : syracuseStep 15190415 = 22785623) B22785623
theorem B10126943 : Blo 1999435 10126943 := bstep (se 1 (by rfl) ⟨7595207, by rfl⟩ : syracuseStep 10126943 = 15190415) B15190415
theorem B6751295 : Blo 1999435 6751295 := bstep (se 1 (by rfl) ⟨5063471, by rfl⟩ : syracuseStep 6751295 = 10126943) B10126943
theorem B4500863 : Blo 1999435 4500863 := bstep (se 1 (by rfl) ⟨3375647, by rfl⟩ : syracuseStep 4500863 = 6751295) B6751295
theorem B3000575 : Blo 1999435 3000575 := bstep (se 1 (by rfl) ⟨2250431, by rfl⟩ : syracuseStep 3000575 = 4500863) B4500863
theorem B2000383 : Blo 1999435 2000383 := bstep (se 1 (by rfl) ⟨1500287, by rfl⟩ : syracuseStep 2000383 = 3000575) B3000575
theorem B3000581 : Blo 1999435 3000581 := bbase (se 4 (by rfl) ⟨281304, by rfl⟩ : syracuseStep 3000581 = 562609) (by norm_num)
theorem B2000387 : Blo 1999435 2000387 := bstep (se 1 (by rfl) ⟨1500290, by rfl⟩ : syracuseStep 2000387 = 3000581) B3000581
theorem B3375661 : Blo 1999435 3375661 := bbase (se 3 (by rfl) ⟨632936, by rfl⟩ : syracuseStep 3375661 = 1265873) (by norm_num)
theorem B4500881 : Blo 1999435 4500881 := bstep (se 2 (by rfl) ⟨1687830, by rfl⟩ : syracuseStep 4500881 = 3375661) B3375661
theorem B3000587 : Blo 1999435 3000587 := bstep (se 1 (by rfl) ⟨2250440, by rfl⟩ : syracuseStep 3000587 = 4500881) B4500881
theorem B2000391 : Blo 1999435 2000391 := bstep (se 1 (by rfl) ⟨1500293, by rfl⟩ : syracuseStep 2000391 = 3000587) B3000587
theorem B2250445 : Blo 1999435 2250445 := bbase (se 3 (by rfl) ⟨421958, by rfl⟩ : syracuseStep 2250445 = 843917) (by norm_num)
theorem B3000593 : Blo 1999435 3000593 := bstep (se 2 (by rfl) ⟨1125222, by rfl⟩ : syracuseStep 3000593 = 2250445) B2250445
theorem B2000395 : Blo 1999435 2000395 := bstep (se 1 (by rfl) ⟨1500296, by rfl⟩ : syracuseStep 2000395 = 3000593) B3000593
theorem B6751349 : Blo 1999435 6751349 := bbase (se 5 (by rfl) ⟨316469, by rfl⟩ : syracuseStep 6751349 = 632939) (by norm_num)
theorem B4500899 : Blo 1999435 4500899 := bstep (se 1 (by rfl) ⟨3375674, by rfl⟩ : syracuseStep 4500899 = 6751349) B6751349
theorem B3000599 : Blo 1999435 3000599 := bstep (se 1 (by rfl) ⟨2250449, by rfl⟩ : syracuseStep 3000599 = 4500899) B4500899
theorem B2000399 : Blo 1999435 2000399 := bstep (se 1 (by rfl) ⟨1500299, by rfl⟩ : syracuseStep 2000399 = 3000599) B3000599
theorem B3000605 : Blo 1999435 3000605 := bbase (se 3 (by rfl) ⟨562613, by rfl⟩ : syracuseStep 3000605 = 1125227) (by norm_num)
theorem B2000403 : Blo 1999435 2000403 := bstep (se 1 (by rfl) ⟨1500302, by rfl⟩ : syracuseStep 2000403 = 3000605) B3000605
theorem B4500917 : Blo 1999435 4500917 := bbase (se 5 (by rfl) ⟨210980, by rfl⟩ : syracuseStep 4500917 = 421961) (by norm_num)
theorem B3000611 : Blo 1999435 3000611 := bstep (se 1 (by rfl) ⟨2250458, by rfl⟩ : syracuseStep 3000611 = 4500917) B4500917
theorem B2000407 : Blo 1999435 2000407 := bstep (se 1 (by rfl) ⟨1500305, by rfl⟩ : syracuseStep 2000407 = 3000611) B3000611
theorem B4272365 : Blo 1999435 4272365 := bbase (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) (by norm_num)
theorem B11392973 : Blo 1999435 11392973 := bstep (se 3 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 11392973 = 4272365) B4272365
theorem B7595315 : Blo 1999435 7595315 := bstep (se 1 (by rfl) ⟨5696486, by rfl⟩ : syracuseStep 7595315 = 11392973) B11392973
theorem B5063543 : Blo 1999435 5063543 := bstep (se 1 (by rfl) ⟨3797657, by rfl⟩ : syracuseStep 5063543 = 7595315) B7595315
theorem B3375695 : Blo 1999435 3375695 := bstep (se 1 (by rfl) ⟨2531771, by rfl⟩ : syracuseStep 3375695 = 5063543) B5063543
theorem B2250463 : Blo 1999435 2250463 := bstep (se 1 (by rfl) ⟨1687847, by rfl⟩ : syracuseStep 2250463 = 3375695) B3375695
theorem B3000617 : Blo 1999435 3000617 := bstep (se 2 (by rfl) ⟨1125231, by rfl⟩ : syracuseStep 3000617 = 2250463) B2250463
theorem B2000411 : Blo 1999435 2000411 := bstep (se 1 (by rfl) ⟨1500308, by rfl⟩ : syracuseStep 2000411 = 3000617) B3000617
theorem B4272373 : Blo 1999435 4272373 := bbase (se 5 (by rfl) ⟨200267, by rfl⟩ : syracuseStep 4272373 = 400535) (by norm_num)
theorem B5696497 : Blo 1999435 5696497 := bstep (se 2 (by rfl) ⟨2136186, by rfl⟩ : syracuseStep 5696497 = 4272373) B4272373
theorem B7595329 : Blo 1999435 7595329 := bstep (se 2 (by rfl) ⟨2848248, by rfl⟩ : syracuseStep 7595329 = 5696497) B5696497
theorem B10127105 : Blo 1999435 10127105 := bstep (se 2 (by rfl) ⟨3797664, by rfl⟩ : syracuseStep 10127105 = 7595329) B7595329
theorem B6751403 : Blo 1999435 6751403 := bstep (se 1 (by rfl) ⟨5063552, by rfl⟩ : syracuseStep 6751403 = 10127105) B10127105
theorem B4500935 : Blo 1999435 4500935 := bstep (se 1 (by rfl) ⟨3375701, by rfl⟩ : syracuseStep 4500935 = 6751403) B6751403
theorem B3000623 : Blo 1999435 3000623 := bstep (se 1 (by rfl) ⟨2250467, by rfl⟩ : syracuseStep 3000623 = 4500935) B4500935
theorem B2000415 : Blo 1999435 2000415 := bstep (se 1 (by rfl) ⟨1500311, by rfl⟩ : syracuseStep 2000415 = 3000623) B3000623
theorem B3000629 : Blo 1999435 3000629 := bbase (se 5 (by rfl) ⟨140654, by rfl⟩ : syracuseStep 3000629 = 281309) (by norm_num)
theorem B2000419 : Blo 1999435 2000419 := bstep (se 1 (by rfl) ⟨1500314, by rfl⟩ : syracuseStep 2000419 = 3000629) B3000629
theorem B5063573 : Blo 1999435 5063573 := bbase (se 6 (by rfl) ⟨118677, by rfl⟩ : syracuseStep 5063573 = 237355) (by norm_num)
theorem B3375715 : Blo 1999435 3375715 := bstep (se 1 (by rfl) ⟨2531786, by rfl⟩ : syracuseStep 3375715 = 5063573) B5063573
theorem B4500953 : Blo 1999435 4500953 := bstep (se 2 (by rfl) ⟨1687857, by rfl⟩ : syracuseStep 4500953 = 3375715) B3375715
theorem B3000635 : Blo 1999435 3000635 := bstep (se 1 (by rfl) ⟨2250476, by rfl⟩ : syracuseStep 3000635 = 4500953) B4500953
theorem B2000423 : Blo 1999435 2000423 := bstep (se 1 (by rfl) ⟨1500317, by rfl⟩ : syracuseStep 2000423 = 3000635) B3000635
theorem B2250481 : Blo 1999435 2250481 := bbase (se 2 (by rfl) ⟨843930, by rfl⟩ : syracuseStep 2250481 = 1687861) (by norm_num)
theorem B3000641 : Blo 1999435 3000641 := bstep (se 2 (by rfl) ⟨1125240, by rfl⟩ : syracuseStep 3000641 = 2250481) B2250481
theorem B2000427 : Blo 1999435 2000427 := bstep (se 1 (by rfl) ⟨1500320, by rfl⟩ : syracuseStep 2000427 = 3000641) B3000641
theorem B5932901 : Blo 1999435 5932901 := bbase (se 4 (by rfl) ⟨556209, by rfl⟩ : syracuseStep 5932901 = 1112419) (by norm_num)
theorem B3955267 : Blo 1999435 3955267 := bstep (se 1 (by rfl) ⟨2966450, by rfl⟩ : syracuseStep 3955267 = 5932901) B5932901
theorem B5273689 : Blo 1999435 5273689 := bstep (se 2 (by rfl) ⟨1977633, by rfl⟩ : syracuseStep 5273689 = 3955267) B3955267
theorem B7031585 : Blo 1999435 7031585 := bstep (se 2 (by rfl) ⟨2636844, by rfl⟩ : syracuseStep 7031585 = 5273689) B5273689
theorem B4687723 : Blo 1999435 4687723 := bstep (se 1 (by rfl) ⟨3515792, by rfl⟩ : syracuseStep 4687723 = 7031585) B7031585
theorem B25001189 : Blo 1999435 25001189 := bstep (se 4 (by rfl) ⟨2343861, by rfl⟩ : syracuseStep 25001189 = 4687723) B4687723
theorem B16667459 : Blo 1999435 16667459 := bstep (se 1 (by rfl) ⟨12500594, by rfl⟩ : syracuseStep 16667459 = 25001189) B25001189
theorem B11111639 : Blo 1999435 11111639 := bstep (se 1 (by rfl) ⟨8333729, by rfl⟩ : syracuseStep 11111639 = 16667459) B16667459
theorem B29631037 : Blo 1999435 29631037 := bstep (se 3 (by rfl) ⟨5555819, by rfl⟩ : syracuseStep 29631037 = 11111639) B11111639
theorem B39508049 : Blo 1999435 39508049 := bstep (se 2 (by rfl) ⟨14815518, by rfl⟩ : syracuseStep 39508049 = 29631037) B29631037
theorem B26338699 : Blo 1999435 26338699 := bstep (se 1 (by rfl) ⟨19754024, by rfl⟩ : syracuseStep 26338699 = 39508049) B39508049
theorem B140473061 : Blo 1999435 140473061 := bstep (se 4 (by rfl) ⟨13169349, by rfl⟩ : syracuseStep 140473061 = 26338699) B26338699
theorem B93648707 : Blo 1999435 93648707 := bstep (se 1 (by rfl) ⟨70236530, by rfl⟩ : syracuseStep 93648707 = 140473061) B140473061
theorem B62432471 : Blo 1999435 62432471 := bstep (se 1 (by rfl) ⟨46824353, by rfl⟩ : syracuseStep 62432471 = 93648707) B93648707
theorem B41621647 : Blo 1999435 41621647 := bstep (se 1 (by rfl) ⟨31216235, by rfl⟩ : syracuseStep 41621647 = 62432471) B62432471
theorem B55495529 : Blo 1999435 55495529 := bstep (se 2 (by rfl) ⟨20810823, by rfl⟩ : syracuseStep 55495529 = 41621647) B41621647
theorem B36997019 : Blo 1999435 36997019 := bstep (se 1 (by rfl) ⟨27747764, by rfl⟩ : syracuseStep 36997019 = 55495529) B55495529
theorem B24664679 : Blo 1999435 24664679 := bstep (se 1 (by rfl) ⟨18498509, by rfl⟩ : syracuseStep 24664679 = 36997019) B36997019
theorem B16443119 : Blo 1999435 16443119 := bstep (se 1 (by rfl) ⟨12332339, by rfl⟩ : syracuseStep 16443119 = 24664679) B24664679
theorem B43848317 : Blo 1999435 43848317 := bstep (se 3 (by rfl) ⟨8221559, by rfl⟩ : syracuseStep 43848317 = 16443119) B16443119
theorem B116928845 : Blo 1999435 116928845 := bstep (se 3 (by rfl) ⟨21924158, by rfl⟩ : syracuseStep 116928845 = 43848317) B43848317
theorem B77952563 : Blo 1999435 77952563 := bstep (se 1 (by rfl) ⟨58464422, by rfl⟩ : syracuseStep 77952563 = 116928845) B116928845
theorem B51968375 : Blo 1999435 51968375 := bstep (se 1 (by rfl) ⟨38976281, by rfl⟩ : syracuseStep 51968375 = 77952563) B77952563
theorem B34645583 : Blo 1999435 34645583 := bstep (se 1 (by rfl) ⟨25984187, by rfl⟩ : syracuseStep 34645583 = 51968375) B51968375
theorem B92388221 : Blo 1999435 92388221 := bstep (se 3 (by rfl) ⟨17322791, by rfl⟩ : syracuseStep 92388221 = 34645583) B34645583
theorem B61592147 : Blo 1999435 61592147 := bstep (se 1 (by rfl) ⟨46194110, by rfl⟩ : syracuseStep 61592147 = 92388221) B92388221
theorem B41061431 : Blo 1999435 41061431 := bstep (se 1 (by rfl) ⟨30796073, by rfl⟩ : syracuseStep 41061431 = 61592147) B61592147
theorem B27374287 : Blo 1999435 27374287 := bstep (se 1 (by rfl) ⟨20530715, by rfl⟩ : syracuseStep 27374287 = 41061431) B41061431
theorem B36499049 : Blo 1999435 36499049 := bstep (se 2 (by rfl) ⟨13687143, by rfl⟩ : syracuseStep 36499049 = 27374287) B27374287
theorem B24332699 : Blo 1999435 24332699 := bstep (se 1 (by rfl) ⟨18249524, by rfl⟩ : syracuseStep 24332699 = 36499049) B36499049
theorem B16221799 : Blo 1999435 16221799 := bstep (se 1 (by rfl) ⟨12166349, by rfl⟩ : syracuseStep 16221799 = 24332699) B24332699
theorem B21629065 : Blo 1999435 21629065 := bstep (se 2 (by rfl) ⟨8110899, by rfl⟩ : syracuseStep 21629065 = 16221799) B16221799
theorem B28838753 : Blo 1999435 28838753 := bstep (se 2 (by rfl) ⟨10814532, by rfl⟩ : syracuseStep 28838753 = 21629065) B21629065
theorem B19225835 : Blo 1999435 19225835 := bstep (se 1 (by rfl) ⟨14419376, by rfl⟩ : syracuseStep 19225835 = 28838753) B28838753
theorem B12817223 : Blo 1999435 12817223 := bstep (se 1 (by rfl) ⟨9612917, by rfl⟩ : syracuseStep 12817223 = 19225835) B19225835
theorem B8544815 : Blo 1999435 8544815 := bstep (se 1 (by rfl) ⟨6408611, by rfl⟩ : syracuseStep 8544815 = 12817223) B12817223
theorem B5696543 : Blo 1999435 5696543 := bstep (se 1 (by rfl) ⟨4272407, by rfl⟩ : syracuseStep 5696543 = 8544815) B8544815
theorem B3797695 : Blo 1999435 3797695 := bstep (se 1 (by rfl) ⟨2848271, by rfl⟩ : syracuseStep 3797695 = 5696543) B5696543
theorem B5063593 : Blo 1999435 5063593 := bstep (se 2 (by rfl) ⟨1898847, by rfl⟩ : syracuseStep 5063593 = 3797695) B3797695
theorem B6751457 : Blo 1999435 6751457 := bstep (se 2 (by rfl) ⟨2531796, by rfl⟩ : syracuseStep 6751457 = 5063593) B5063593
theorem B4500971 : Blo 1999435 4500971 := bstep (se 1 (by rfl) ⟨3375728, by rfl⟩ : syracuseStep 4500971 = 6751457) B6751457
theorem B3000647 : Blo 1999435 3000647 := bstep (se 1 (by rfl) ⟨2250485, by rfl⟩ : syracuseStep 3000647 = 4500971) B4500971
theorem B2000431 : Blo 1999435 2000431 := bstep (se 1 (by rfl) ⟨1500323, by rfl⟩ : syracuseStep 2000431 = 3000647) B3000647
theorem B3000653 : Blo 1999435 3000653 := bbase (se 3 (by rfl) ⟨562622, by rfl⟩ : syracuseStep 3000653 = 1125245) (by norm_num)
theorem B2000435 : Blo 1999435 2000435 := bstep (se 1 (by rfl) ⟨1500326, by rfl⟩ : syracuseStep 2000435 = 3000653) B3000653
theorem B4500989 : Blo 1999435 4500989 := bbase (se 3 (by rfl) ⟨843935, by rfl⟩ : syracuseStep 4500989 = 1687871) (by norm_num)
theorem B3000659 : Blo 1999435 3000659 := bstep (se 1 (by rfl) ⟨2250494, by rfl⟩ : syracuseStep 3000659 = 4500989) B4500989
theorem B2000439 : Blo 1999435 2000439 := bstep (se 1 (by rfl) ⟨1500329, by rfl⟩ : syracuseStep 2000439 = 3000659) B3000659
theorem B3375749 : Blo 1999435 3375749 := bbase (se 4 (by rfl) ⟨316476, by rfl⟩ : syracuseStep 3375749 = 632953) (by norm_num)
theorem B2250499 : Blo 1999435 2250499 := bstep (se 1 (by rfl) ⟨1687874, by rfl⟩ : syracuseStep 2250499 = 3375749) B3375749
theorem B3000665 : Blo 1999435 3000665 := bstep (se 2 (by rfl) ⟨1125249, by rfl⟩ : syracuseStep 3000665 = 2250499) B2250499
theorem B2000443 : Blo 1999435 2000443 := bstep (se 1 (by rfl) ⟨1500332, by rfl⟩ : syracuseStep 2000443 = 3000665) B3000665
theorem B15190901 : Blo 1999435 15190901 := bbase (se 5 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 15190901 = 1424147) (by norm_num)
theorem B10127267 : Blo 1999435 10127267 := bstep (se 1 (by rfl) ⟨7595450, by rfl⟩ : syracuseStep 10127267 = 15190901) B15190901
theorem B6751511 : Blo 1999435 6751511 := bstep (se 1 (by rfl) ⟨5063633, by rfl⟩ : syracuseStep 6751511 = 10127267) B10127267
theorem B4501007 : Blo 1999435 4501007 := bstep (se 1 (by rfl) ⟨3375755, by rfl⟩ : syracuseStep 4501007 = 6751511) B6751511
theorem B3000671 : Blo 1999435 3000671 := bstep (se 1 (by rfl) ⟨2250503, by rfl⟩ : syracuseStep 3000671 = 4501007) B4501007
theorem B2000447 : Blo 1999435 2000447 := bstep (se 1 (by rfl) ⟨1500335, by rfl⟩ : syracuseStep 2000447 = 3000671) B3000671
theorem B3000677 : Blo 1999435 3000677 := bbase (se 4 (by rfl) ⟨281313, by rfl⟩ : syracuseStep 3000677 = 562627) (by norm_num)
theorem B2000451 : Blo 1999435 2000451 := bstep (se 1 (by rfl) ⟨1500338, by rfl⟩ : syracuseStep 2000451 = 3000677) B3000677
theorem B3797741 : Blo 1999435 3797741 := bbase (se 3 (by rfl) ⟨712076, by rfl⟩ : syracuseStep 3797741 = 1424153) (by norm_num)
theorem B2531827 : Blo 1999435 2531827 := bstep (se 1 (by rfl) ⟨1898870, by rfl⟩ : syracuseStep 2531827 = 3797741) B3797741
theorem B3375769 : Blo 1999435 3375769 := bstep (se 2 (by rfl) ⟨1265913, by rfl⟩ : syracuseStep 3375769 = 2531827) B2531827
theorem B4501025 : Blo 1999435 4501025 := bstep (se 2 (by rfl) ⟨1687884, by rfl⟩ : syracuseStep 4501025 = 3375769) B3375769
theorem B3000683 : Blo 1999435 3000683 := bstep (se 1 (by rfl) ⟨2250512, by rfl⟩ : syracuseStep 3000683 = 4501025) B4501025
theorem B2000455 : Blo 1999435 2000455 := bstep (se 1 (by rfl) ⟨1500341, by rfl⟩ : syracuseStep 2000455 = 3000683) B3000683
theorem B2250517 : Blo 1999435 2250517 := bbase (se 6 (by rfl) ⟨52746, by rfl⟩ : syracuseStep 2250517 = 105493) (by norm_num)
theorem B3000689 : Blo 1999435 3000689 := bstep (se 2 (by rfl) ⟨1125258, by rfl⟩ : syracuseStep 3000689 = 2250517) B2250517
theorem B2000459 : Blo 1999435 2000459 := bstep (se 1 (by rfl) ⟨1500344, by rfl⟩ : syracuseStep 2000459 = 3000689) B3000689
theorem B2531837 : Blo 1999435 2531837 := bbase (se 3 (by rfl) ⟨474719, by rfl⟩ : syracuseStep 2531837 = 949439) (by norm_num)
theorem B6751565 : Blo 1999435 6751565 := bstep (se 3 (by rfl) ⟨1265918, by rfl⟩ : syracuseStep 6751565 = 2531837) B2531837
theorem B4501043 : Blo 1999435 4501043 := bstep (se 1 (by rfl) ⟨3375782, by rfl⟩ : syracuseStep 4501043 = 6751565) B6751565
theorem B3000695 : Blo 1999435 3000695 := bstep (se 1 (by rfl) ⟨2250521, by rfl⟩ : syracuseStep 3000695 = 4501043) B4501043
theorem B2000463 : Blo 1999435 2000463 := bstep (se 1 (by rfl) ⟨1500347, by rfl⟩ : syracuseStep 2000463 = 3000695) B3000695
theorem B3000701 : Blo 1999435 3000701 := bbase (se 3 (by rfl) ⟨562631, by rfl⟩ : syracuseStep 3000701 = 1125263) (by norm_num)
theorem B2000467 : Blo 1999435 2000467 := bstep (se 1 (by rfl) ⟨1500350, by rfl⟩ : syracuseStep 2000467 = 3000701) B3000701
theorem B4501061 : Blo 1999435 4501061 := bbase (se 4 (by rfl) ⟨421974, by rfl⟩ : syracuseStep 4501061 = 843949) (by norm_num)
theorem B3000707 : Blo 1999435 3000707 := bstep (se 1 (by rfl) ⟨2250530, by rfl⟩ : syracuseStep 3000707 = 4501061) B4501061
theorem B2000471 : Blo 1999435 2000471 := bstep (se 1 (by rfl) ⟨1500353, by rfl⟩ : syracuseStep 2000471 = 3000707) B3000707
theorem B3604925 : Blo 1999435 3604925 := bbase (se 3 (by rfl) ⟨675923, by rfl⟩ : syracuseStep 3604925 = 1351847) (by norm_num)
theorem B2403283 : Blo 1999435 2403283 := bstep (se 1 (by rfl) ⟨1802462, by rfl⟩ : syracuseStep 2403283 = 3604925) B3604925
theorem B3204377 : Blo 1999435 3204377 := bstep (se 2 (by rfl) ⟨1201641, by rfl⟩ : syracuseStep 3204377 = 2403283) B2403283
theorem B2136251 : Blo 1999435 2136251 := bstep (se 1 (by rfl) ⟨1602188, by rfl⟩ : syracuseStep 2136251 = 3204377) B3204377
theorem B5696669 : Blo 1999435 5696669 := bstep (se 3 (by rfl) ⟨1068125, by rfl⟩ : syracuseStep 5696669 = 2136251) B2136251
theorem B3797779 : Blo 1999435 3797779 := bstep (se 1 (by rfl) ⟨2848334, by rfl⟩ : syracuseStep 3797779 = 5696669) B5696669
theorem B5063705 : Blo 1999435 5063705 := bstep (se 2 (by rfl) ⟨1898889, by rfl⟩ : syracuseStep 5063705 = 3797779) B3797779
theorem B3375803 : Blo 1999435 3375803 := bstep (se 1 (by rfl) ⟨2531852, by rfl⟩ : syracuseStep 3375803 = 5063705) B5063705
theorem B2250535 : Blo 1999435 2250535 := bstep (se 1 (by rfl) ⟨1687901, by rfl⟩ : syracuseStep 2250535 = 3375803) B3375803
theorem B3000713 : Blo 1999435 3000713 := bstep (se 2 (by rfl) ⟨1125267, by rfl⟩ : syracuseStep 3000713 = 2250535) B2250535
theorem B2000475 : Blo 1999435 2000475 := bstep (se 1 (by rfl) ⟨1500356, by rfl⟩ : syracuseStep 2000475 = 3000713) B3000713
theorem B10127429 : Blo 1999435 10127429 := bbase (se 4 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 10127429 = 1898893) (by norm_num)
theorem B6751619 : Blo 1999435 6751619 := bstep (se 1 (by rfl) ⟨5063714, by rfl⟩ : syracuseStep 6751619 = 10127429) B10127429
theorem B4501079 : Blo 1999435 4501079 := bstep (se 1 (by rfl) ⟨3375809, by rfl⟩ : syracuseStep 4501079 = 6751619) B6751619
theorem B3000719 : Blo 1999435 3000719 := bstep (se 1 (by rfl) ⟨2250539, by rfl⟩ : syracuseStep 3000719 = 4501079) B4501079
theorem B2000479 : Blo 1999435 2000479 := bstep (se 1 (by rfl) ⟨1500359, by rfl⟩ : syracuseStep 2000479 = 3000719) B3000719
theorem B3000725 : Blo 1999435 3000725 := bbase (se 6 (by rfl) ⟨70329, by rfl⟩ : syracuseStep 3000725 = 140659) (by norm_num)
theorem B2000483 : Blo 1999435 2000483 := bstep (se 1 (by rfl) ⟨1500362, by rfl⟩ : syracuseStep 2000483 = 3000725) B3000725
theorem B2703709 : Blo 1999435 2703709 := bbase (se 3 (by rfl) ⟨506945, by rfl⟩ : syracuseStep 2703709 = 1013891) (by norm_num)
theorem B14419781 : Blo 1999435 14419781 := bstep (se 4 (by rfl) ⟨1351854, by rfl⟩ : syracuseStep 14419781 = 2703709) B2703709
theorem B9613187 : Blo 1999435 9613187 := bstep (se 1 (by rfl) ⟨7209890, by rfl⟩ : syracuseStep 9613187 = 14419781) B14419781
theorem B6408791 : Blo 1999435 6408791 := bstep (se 1 (by rfl) ⟨4806593, by rfl⟩ : syracuseStep 6408791 = 9613187) B9613187
theorem B4272527 : Blo 1999435 4272527 := bstep (se 1 (by rfl) ⟨3204395, by rfl⟩ : syracuseStep 4272527 = 6408791) B6408791
theorem B11393405 : Blo 1999435 11393405 := bstep (se 3 (by rfl) ⟨2136263, by rfl⟩ : syracuseStep 11393405 = 4272527) B4272527
theorem B7595603 : Blo 1999435 7595603 := bstep (se 1 (by rfl) ⟨5696702, by rfl⟩ : syracuseStep 7595603 = 11393405) B11393405
theorem B5063735 : Blo 1999435 5063735 := bstep (se 1 (by rfl) ⟨3797801, by rfl⟩ : syracuseStep 5063735 = 7595603) B7595603
theorem B3375823 : Blo 1999435 3375823 := bstep (se 1 (by rfl) ⟨2531867, by rfl⟩ : syracuseStep 3375823 = 5063735) B5063735
theorem B4501097 : Blo 1999435 4501097 := bstep (se 2 (by rfl) ⟨1687911, by rfl⟩ : syracuseStep 4501097 = 3375823) B3375823
theorem B3000731 : Blo 1999435 3000731 := bstep (se 1 (by rfl) ⟨2250548, by rfl⟩ : syracuseStep 3000731 = 4501097) B4501097
theorem B2000487 : Blo 1999435 2000487 := bstep (se 1 (by rfl) ⟨1500365, by rfl⟩ : syracuseStep 2000487 = 3000731) B3000731
theorem B2250553 : Blo 1999435 2250553 := bbase (se 2 (by rfl) ⟨843957, by rfl⟩ : syracuseStep 2250553 = 1687915) (by norm_num)
theorem B3000737 : Blo 1999435 3000737 := bstep (se 2 (by rfl) ⟨1125276, by rfl⟩ : syracuseStep 3000737 = 2250553) B2250553
theorem B2000491 : Blo 1999435 2000491 := bstep (se 1 (by rfl) ⟨1500368, by rfl⟩ : syracuseStep 2000491 = 3000737) B3000737
theorem B5696725 : Blo 1999435 5696725 := bbase (se 7 (by rfl) ⟨66758, by rfl⟩ : syracuseStep 5696725 = 133517) (by norm_num)
theorem B7595633 : Blo 1999435 7595633 := bstep (se 2 (by rfl) ⟨2848362, by rfl⟩ : syracuseStep 7595633 = 5696725) B5696725
theorem B5063755 : Blo 1999435 5063755 := bstep (se 1 (by rfl) ⟨3797816, by rfl⟩ : syracuseStep 5063755 = 7595633) B7595633
theorem B6751673 : Blo 1999435 6751673 := bstep (se 2 (by rfl) ⟨2531877, by rfl⟩ : syracuseStep 6751673 = 5063755) B5063755
theorem B4501115 : Blo 1999435 4501115 := bstep (se 1 (by rfl) ⟨3375836, by rfl⟩ : syracuseStep 4501115 = 6751673) B6751673
theorem B3000743 : Blo 1999435 3000743 := bstep (se 1 (by rfl) ⟨2250557, by rfl⟩ : syracuseStep 3000743 = 4501115) B4501115
theorem B2000495 : Blo 1999435 2000495 := bstep (se 1 (by rfl) ⟨1500371, by rfl⟩ : syracuseStep 2000495 = 3000743) B3000743
theorem B3000749 : Blo 1999435 3000749 := bbase (se 3 (by rfl) ⟨562640, by rfl⟩ : syracuseStep 3000749 = 1125281) (by norm_num)
theorem B2000499 : Blo 1999435 2000499 := bstep (se 1 (by rfl) ⟨1500374, by rfl⟩ : syracuseStep 2000499 = 3000749) B3000749
theorem B4501133 : Blo 1999435 4501133 := bbase (se 3 (by rfl) ⟨843962, by rfl⟩ : syracuseStep 4501133 = 1687925) (by norm_num)
theorem B3000755 : Blo 1999435 3000755 := bstep (se 1 (by rfl) ⟨2250566, by rfl⟩ : syracuseStep 3000755 = 4501133) B4501133
theorem B2000503 : Blo 1999435 2000503 := bstep (se 1 (by rfl) ⟨1500377, by rfl⟩ : syracuseStep 2000503 = 3000755) B3000755
theorem B2531893 : Blo 1999435 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B3375857 : Blo 1999435 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B2250571 : Blo 1999435 2250571 := bstep (se 1 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 2250571 = 3375857) B3375857
theorem B3000761 : Blo 1999435 3000761 := bstep (se 2 (by rfl) ⟨1125285, by rfl⟩ : syracuseStep 3000761 = 2250571) B2250571
theorem B2000507 : Blo 1999435 2000507 := bstep (se 1 (by rfl) ⟨1500380, by rfl⟩ : syracuseStep 2000507 = 3000761) B3000761
theorem B6843845 : Blo 1999435 6843845 := bbase (se 4 (by rfl) ⟨641610, by rfl⟩ : syracuseStep 6843845 = 1283221) (by norm_num)
theorem B4562563 : Blo 1999435 4562563 := bstep (se 1 (by rfl) ⟨3421922, by rfl⟩ : syracuseStep 4562563 = 6843845) B6843845
theorem B6083417 : Blo 1999435 6083417 := bstep (se 2 (by rfl) ⟨2281281, by rfl⟩ : syracuseStep 6083417 = 4562563) B4562563
theorem B16222445 : Blo 1999435 16222445 := bstep (se 3 (by rfl) ⟨3041708, by rfl⟩ : syracuseStep 16222445 = 6083417) B6083417
theorem B10814963 : Blo 1999435 10814963 := bstep (se 1 (by rfl) ⟨8111222, by rfl⟩ : syracuseStep 10814963 = 16222445) B16222445
theorem B28839901 : Blo 1999435 28839901 := bstep (se 3 (by rfl) ⟨5407481, by rfl⟩ : syracuseStep 28839901 = 10814963) B10814963
theorem B38453201 : Blo 1999435 38453201 := bstep (se 2 (by rfl) ⟨14419950, by rfl⟩ : syracuseStep 38453201 = 28839901) B28839901
theorem B25635467 : Blo 1999435 25635467 := bstep (se 1 (by rfl) ⟨19226600, by rfl⟩ : syracuseStep 25635467 = 38453201) B38453201
theorem B17090311 : Blo 1999435 17090311 := bstep (se 1 (by rfl) ⟨12817733, by rfl⟩ : syracuseStep 17090311 = 25635467) B25635467
theorem B22787081 : Blo 1999435 22787081 := bstep (se 2 (by rfl) ⟨8545155, by rfl⟩ : syracuseStep 22787081 = 17090311) B17090311
theorem B15191387 : Blo 1999435 15191387 := bstep (se 1 (by rfl) ⟨11393540, by rfl⟩ : syracuseStep 15191387 = 22787081) B22787081
theorem B10127591 : Blo 1999435 10127591 := bstep (se 1 (by rfl) ⟨7595693, by rfl⟩ : syracuseStep 10127591 = 15191387) B15191387
theorem B6751727 : Blo 1999435 6751727 := bstep (se 1 (by rfl) ⟨5063795, by rfl⟩ : syracuseStep 6751727 = 10127591) B10127591
theorem B4501151 : Blo 1999435 4501151 := bstep (se 1 (by rfl) ⟨3375863, by rfl⟩ : syracuseStep 4501151 = 6751727) B6751727
theorem B3000767 : Blo 1999435 3000767 := bstep (se 1 (by rfl) ⟨2250575, by rfl⟩ : syracuseStep 3000767 = 4501151) B4501151
theorem B2000511 : Blo 1999435 2000511 := bstep (se 1 (by rfl) ⟨1500383, by rfl⟩ : syracuseStep 2000511 = 3000767) B3000767
theorem B3000773 : Blo 1999435 3000773 := bbase (se 4 (by rfl) ⟨281322, by rfl⟩ : syracuseStep 3000773 = 562645) (by norm_num)
theorem B2000515 : Blo 1999435 2000515 := bstep (se 1 (by rfl) ⟨1500386, by rfl⟩ : syracuseStep 2000515 = 3000773) B3000773
theorem B3375877 : Blo 1999435 3375877 := bbase (se 4 (by rfl) ⟨316488, by rfl⟩ : syracuseStep 3375877 = 632977) (by norm_num)
theorem B4501169 : Blo 1999435 4501169 := bstep (se 2 (by rfl) ⟨1687938, by rfl⟩ : syracuseStep 4501169 = 3375877) B3375877
theorem B3000779 : Blo 1999435 3000779 := bstep (se 1 (by rfl) ⟨2250584, by rfl⟩ : syracuseStep 3000779 = 4501169) B4501169
theorem B2000519 : Blo 1999435 2000519 := bstep (se 1 (by rfl) ⟨1500389, by rfl⟩ : syracuseStep 2000519 = 3000779) B3000779
theorem B2250589 : Blo 1999435 2250589 := bbase (se 3 (by rfl) ⟨421985, by rfl⟩ : syracuseStep 2250589 = 843971) (by norm_num)
theorem B3000785 : Blo 1999435 3000785 := bstep (se 2 (by rfl) ⟨1125294, by rfl⟩ : syracuseStep 3000785 = 2250589) B2250589
theorem B2000523 : Blo 1999435 2000523 := bstep (se 1 (by rfl) ⟨1500392, by rfl⟩ : syracuseStep 2000523 = 3000785) B3000785
theorem B6751781 : Blo 1999435 6751781 := bbase (se 4 (by rfl) ⟨632979, by rfl⟩ : syracuseStep 6751781 = 1265959) (by norm_num)
theorem B4501187 : Blo 1999435 4501187 := bstep (se 1 (by rfl) ⟨3375890, by rfl⟩ : syracuseStep 4501187 = 6751781) B6751781
theorem B3000791 : Blo 1999435 3000791 := bstep (se 1 (by rfl) ⟨2250593, by rfl⟩ : syracuseStep 3000791 = 4501187) B4501187
theorem B2000527 : Blo 1999435 2000527 := bstep (se 1 (by rfl) ⟨1500395, by rfl⟩ : syracuseStep 2000527 = 3000791) B3000791
theorem B3000797 : Blo 1999435 3000797 := bbase (se 3 (by rfl) ⟨562649, by rfl⟩ : syracuseStep 3000797 = 1125299) (by norm_num)
theorem B2000531 : Blo 1999435 2000531 := bstep (se 1 (by rfl) ⟨1500398, by rfl⟩ : syracuseStep 2000531 = 3000797) B3000797
theorem B4501205 : Blo 1999435 4501205 := bbase (se 7 (by rfl) ⟨52748, by rfl⟩ : syracuseStep 4501205 = 105497) (by norm_num)
theorem B3000803 : Blo 1999435 3000803 := bstep (se 1 (by rfl) ⟨2250602, by rfl⟩ : syracuseStep 3000803 = 4501205) B4501205
theorem B2000535 : Blo 1999435 2000535 := bstep (se 1 (by rfl) ⟨1500401, by rfl⟩ : syracuseStep 2000535 = 3000803) B3000803
theorem B17323733 : Blo 1999435 17323733 := bbase (se 7 (by rfl) ⟨203012, by rfl⟩ : syracuseStep 17323733 = 406025) (by norm_num)
theorem B11549155 : Blo 1999435 11549155 := bstep (se 1 (by rfl) ⟨8661866, by rfl⟩ : syracuseStep 11549155 = 17323733) B17323733
theorem B15398873 : Blo 1999435 15398873 := bstep (se 2 (by rfl) ⟨5774577, by rfl⟩ : syracuseStep 15398873 = 11549155) B11549155
theorem B10265915 : Blo 1999435 10265915 := bstep (se 1 (by rfl) ⟨7699436, by rfl⟩ : syracuseStep 10265915 = 15398873) B15398873
theorem B6843943 : Blo 1999435 6843943 := bstep (se 1 (by rfl) ⟨5132957, by rfl⟩ : syracuseStep 6843943 = 10265915) B10265915
theorem B36501029 : Blo 1999435 36501029 := bstep (se 4 (by rfl) ⟨3421971, by rfl⟩ : syracuseStep 36501029 = 6843943) B6843943
theorem B24334019 : Blo 1999435 24334019 := bstep (se 1 (by rfl) ⟨18250514, by rfl⟩ : syracuseStep 24334019 = 36501029) B36501029
theorem B16222679 : Blo 1999435 16222679 := bstep (se 1 (by rfl) ⟨12167009, by rfl⟩ : syracuseStep 16222679 = 24334019) B24334019
theorem B10815119 : Blo 1999435 10815119 := bstep (se 1 (by rfl) ⟨8111339, by rfl⟩ : syracuseStep 10815119 = 16222679) B16222679
theorem B7210079 : Blo 1999435 7210079 := bstep (se 1 (by rfl) ⟨5407559, by rfl⟩ : syracuseStep 7210079 = 10815119) B10815119
theorem B4806719 : Blo 1999435 4806719 := bstep (se 1 (by rfl) ⟨3605039, by rfl⟩ : syracuseStep 4806719 = 7210079) B7210079
theorem B3204479 : Blo 1999435 3204479 := bstep (se 1 (by rfl) ⟨2403359, by rfl⟩ : syracuseStep 3204479 = 4806719) B4806719
theorem B8545277 : Blo 1999435 8545277 := bstep (se 3 (by rfl) ⟨1602239, by rfl⟩ : syracuseStep 8545277 = 3204479) B3204479
theorem B5696851 : Blo 1999435 5696851 := bstep (se 1 (by rfl) ⟨4272638, by rfl⟩ : syracuseStep 5696851 = 8545277) B8545277
theorem B7595801 : Blo 1999435 7595801 := bstep (se 2 (by rfl) ⟨2848425, by rfl⟩ : syracuseStep 7595801 = 5696851) B5696851
theorem B5063867 : Blo 1999435 5063867 := bstep (se 1 (by rfl) ⟨3797900, by rfl⟩ : syracuseStep 5063867 = 7595801) B7595801
theorem B3375911 : Blo 1999435 3375911 := bstep (se 1 (by rfl) ⟨2531933, by rfl⟩ : syracuseStep 3375911 = 5063867) B5063867
theorem B2250607 : Blo 1999435 2250607 := bstep (se 1 (by rfl) ⟨1687955, by rfl⟩ : syracuseStep 2250607 = 3375911) B3375911
theorem B3000809 : Blo 1999435 3000809 := bstep (se 2 (by rfl) ⟨1125303, by rfl⟩ : syracuseStep 3000809 = 2250607) B2250607
theorem B2000539 : Blo 1999435 2000539 := bstep (se 1 (by rfl) ⟨1500404, by rfl⟩ : syracuseStep 2000539 = 3000809) B3000809
theorem B3849725 : Blo 1999435 3849725 := bbase (se 3 (by rfl) ⟨721823, by rfl⟩ : syracuseStep 3849725 = 1443647) (by norm_num)
theorem B10265933 : Blo 1999435 10265933 := bstep (se 3 (by rfl) ⟨1924862, by rfl⟩ : syracuseStep 10265933 = 3849725) B3849725
theorem B6843955 : Blo 1999435 6843955 := bstep (se 1 (by rfl) ⟨5132966, by rfl⟩ : syracuseStep 6843955 = 10265933) B10265933
theorem B9125273 : Blo 1999435 9125273 := bstep (se 2 (by rfl) ⟨3421977, by rfl⟩ : syracuseStep 9125273 = 6843955) B6843955
theorem B6083515 : Blo 1999435 6083515 := bstep (se 1 (by rfl) ⟨4562636, by rfl⟩ : syracuseStep 6083515 = 9125273) B9125273
theorem B8111353 : Blo 1999435 8111353 := bstep (se 2 (by rfl) ⟨3041757, by rfl⟩ : syracuseStep 8111353 = 6083515) B6083515
theorem B10815137 : Blo 1999435 10815137 := bstep (se 2 (by rfl) ⟨4055676, by rfl⟩ : syracuseStep 10815137 = 8111353) B8111353
theorem B7210091 : Blo 1999435 7210091 := bstep (se 1 (by rfl) ⟨5407568, by rfl⟩ : syracuseStep 7210091 = 10815137) B10815137
theorem B19226909 : Blo 1999435 19226909 := bstep (se 3 (by rfl) ⟨3605045, by rfl⟩ : syracuseStep 19226909 = 7210091) B7210091
theorem B12817939 : Blo 1999435 12817939 := bstep (se 1 (by rfl) ⟨9613454, by rfl⟩ : syracuseStep 12817939 = 19226909) B19226909
theorem B17090585 : Blo 1999435 17090585 := bstep (se 2 (by rfl) ⟨6408969, by rfl⟩ : syracuseStep 17090585 = 12817939) B12817939
theorem B11393723 : Blo 1999435 11393723 := bstep (se 1 (by rfl) ⟨8545292, by rfl⟩ : syracuseStep 11393723 = 17090585) B17090585
theorem B7595815 : Blo 1999435 7595815 := bstep (se 1 (by rfl) ⟨5696861, by rfl⟩ : syracuseStep 7595815 = 11393723) B11393723
theorem B10127753 : Blo 1999435 10127753 := bstep (se 2 (by rfl) ⟨3797907, by rfl⟩ : syracuseStep 10127753 = 7595815) B7595815
theorem B6751835 : Blo 1999435 6751835 := bstep (se 1 (by rfl) ⟨5063876, by rfl⟩ : syracuseStep 6751835 = 10127753) B10127753
theorem B4501223 : Blo 1999435 4501223 := bstep (se 1 (by rfl) ⟨3375917, by rfl⟩ : syracuseStep 4501223 = 6751835) B6751835
theorem B3000815 : Blo 1999435 3000815 := bstep (se 1 (by rfl) ⟨2250611, by rfl⟩ : syracuseStep 3000815 = 4501223) B4501223
theorem B2000543 : Blo 1999435 2000543 := bstep (se 1 (by rfl) ⟨1500407, by rfl⟩ : syracuseStep 2000543 = 3000815) B3000815
theorem B3000821 : Blo 1999435 3000821 := bbase (se 5 (by rfl) ⟨140663, by rfl⟩ : syracuseStep 3000821 = 281327) (by norm_num)
theorem B2000547 : Blo 1999435 2000547 := bstep (se 1 (by rfl) ⟨1500410, by rfl⟩ : syracuseStep 2000547 = 3000821) B3000821
theorem B5696885 : Blo 1999435 5696885 := bbase (se 5 (by rfl) ⟨267041, by rfl⟩ : syracuseStep 5696885 = 534083) (by norm_num)
theorem B3797923 : Blo 1999435 3797923 := bstep (se 1 (by rfl) ⟨2848442, by rfl⟩ : syracuseStep 3797923 = 5696885) B5696885
theorem B5063897 : Blo 1999435 5063897 := bstep (se 2 (by rfl) ⟨1898961, by rfl⟩ : syracuseStep 5063897 = 3797923) B3797923
theorem B3375931 : Blo 1999435 3375931 := bstep (se 1 (by rfl) ⟨2531948, by rfl⟩ : syracuseStep 3375931 = 5063897) B5063897
theorem B4501241 : Blo 1999435 4501241 := bstep (se 2 (by rfl) ⟨1687965, by rfl⟩ : syracuseStep 4501241 = 3375931) B3375931
theorem B3000827 : Blo 1999435 3000827 := bstep (se 1 (by rfl) ⟨2250620, by rfl⟩ : syracuseStep 3000827 = 4501241) B4501241
theorem B2000551 : Blo 1999435 2000551 := bstep (se 1 (by rfl) ⟨1500413, by rfl⟩ : syracuseStep 2000551 = 3000827) B3000827
theorem B2250625 : Blo 1999435 2250625 := bbase (se 2 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 2250625 = 1687969) (by norm_num)
theorem B3000833 : Blo 1999435 3000833 := bstep (se 2 (by rfl) ⟨1125312, by rfl⟩ : syracuseStep 3000833 = 2250625) B2250625
theorem B2000555 : Blo 1999435 2000555 := bstep (se 1 (by rfl) ⟨1500416, by rfl⟩ : syracuseStep 2000555 = 3000833) B3000833
theorem B5063917 : Blo 1999435 5063917 := bbase (se 3 (by rfl) ⟨949484, by rfl⟩ : syracuseStep 5063917 = 1898969) (by norm_num)
theorem B6751889 : Blo 1999435 6751889 := bstep (se 2 (by rfl) ⟨2531958, by rfl⟩ : syracuseStep 6751889 = 5063917) B5063917
theorem B4501259 : Blo 1999435 4501259 := bstep (se 1 (by rfl) ⟨3375944, by rfl⟩ : syracuseStep 4501259 = 6751889) B6751889
theorem B3000839 : Blo 1999435 3000839 := bstep (se 1 (by rfl) ⟨2250629, by rfl⟩ : syracuseStep 3000839 = 4501259) B4501259
theorem B2000559 : Blo 1999435 2000559 := bstep (se 1 (by rfl) ⟨1500419, by rfl⟩ : syracuseStep 2000559 = 3000839) B3000839
theorem B3000845 : Blo 1999435 3000845 := bbase (se 3 (by rfl) ⟨562658, by rfl⟩ : syracuseStep 3000845 = 1125317) (by norm_num)
theorem B2000563 : Blo 1999435 2000563 := bstep (se 1 (by rfl) ⟨1500422, by rfl⟩ : syracuseStep 2000563 = 3000845) B3000845
theorem B4501277 : Blo 1999435 4501277 := bbase (se 3 (by rfl) ⟨843989, by rfl⟩ : syracuseStep 4501277 = 1687979) (by norm_num)
theorem B3000851 : Blo 1999435 3000851 := bstep (se 1 (by rfl) ⟨2250638, by rfl⟩ : syracuseStep 3000851 = 4501277) B4501277
theorem B2000567 : Blo 1999435 2000567 := bstep (se 1 (by rfl) ⟨1500425, by rfl⟩ : syracuseStep 2000567 = 3000851) B3000851
theorem B3375965 : Blo 1999435 3375965 := bbase (se 3 (by rfl) ⟨632993, by rfl⟩ : syracuseStep 3375965 = 1265987) (by norm_num)
theorem B2250643 : Blo 1999435 2250643 := bstep (se 1 (by rfl) ⟨1687982, by rfl⟩ : syracuseStep 2250643 = 3375965) B3375965
theorem B3000857 : Blo 1999435 3000857 := bstep (se 2 (by rfl) ⟨1125321, by rfl⟩ : syracuseStep 3000857 = 2250643) B2250643
theorem B2000571 : Blo 1999435 2000571 := bstep (se 1 (by rfl) ⟨1500428, by rfl⟩ : syracuseStep 2000571 = 3000857) B3000857
theorem B8545429 : Blo 1999435 8545429 := bbase (se 6 (by rfl) ⟨200283, by rfl⟩ : syracuseStep 8545429 = 400567) (by norm_num)
theorem B11393905 : Blo 1999435 11393905 := bstep (se 2 (by rfl) ⟨4272714, by rfl⟩ : syracuseStep 11393905 = 8545429) B8545429
theorem B15191873 : Blo 1999435 15191873 := bstep (se 2 (by rfl) ⟨5696952, by rfl⟩ : syracuseStep 15191873 = 11393905) B11393905
theorem B10127915 : Blo 1999435 10127915 := bstep (se 1 (by rfl) ⟨7595936, by rfl⟩ : syracuseStep 10127915 = 15191873) B15191873
theorem B6751943 : Blo 1999435 6751943 := bstep (se 1 (by rfl) ⟨5063957, by rfl⟩ : syracuseStep 6751943 = 10127915) B10127915
theorem B4501295 : Blo 1999435 4501295 := bstep (se 1 (by rfl) ⟨3375971, by rfl⟩ : syracuseStep 4501295 = 6751943) B6751943
theorem B3000863 : Blo 1999435 3000863 := bstep (se 1 (by rfl) ⟨2250647, by rfl⟩ : syracuseStep 3000863 = 4501295) B4501295
theorem B2000575 : Blo 1999435 2000575 := bstep (se 1 (by rfl) ⟨1500431, by rfl⟩ : syracuseStep 2000575 = 3000863) B3000863
theorem B3000869 : Blo 1999435 3000869 := bbase (se 4 (by rfl) ⟨281331, by rfl⟩ : syracuseStep 3000869 = 562663) (by norm_num)
theorem B2000579 : Blo 1999435 2000579 := bstep (se 1 (by rfl) ⟨1500434, by rfl⟩ : syracuseStep 2000579 = 3000869) B3000869
theorem B2531989 : Blo 1999435 2531989 := bbase (se 6 (by rfl) ⟨59343, by rfl⟩ : syracuseStep 2531989 = 118687) (by norm_num)
theorem B3375985 : Blo 1999435 3375985 := bstep (se 2 (by rfl) ⟨1265994, by rfl⟩ : syracuseStep 3375985 = 2531989) B2531989
theorem B4501313 : Blo 1999435 4501313 := bstep (se 2 (by rfl) ⟨1687992, by rfl⟩ : syracuseStep 4501313 = 3375985) B3375985
theorem B3000875 : Blo 1999435 3000875 := bstep (se 1 (by rfl) ⟨2250656, by rfl⟩ : syracuseStep 3000875 = 4501313) B4501313
theorem B2000583 : Blo 1999435 2000583 := bstep (se 1 (by rfl) ⟨1500437, by rfl⟩ : syracuseStep 2000583 = 3000875) B3000875
theorem B2250661 : Blo 1999435 2250661 := bbase (se 4 (by rfl) ⟨210999, by rfl⟩ : syracuseStep 2250661 = 421999) (by norm_num)
theorem B3000881 : Blo 1999435 3000881 := bstep (se 2 (by rfl) ⟨1125330, by rfl⟩ : syracuseStep 3000881 = 2250661) B2250661
theorem B2000587 : Blo 1999435 2000587 := bstep (se 1 (by rfl) ⟨1500440, by rfl⟩ : syracuseStep 2000587 = 3000881) B3000881
theorem B7699637 : Blo 1999435 7699637 := bbase (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) (by norm_num)
theorem B5133091 : Blo 1999435 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B6844121 : Blo 1999435 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B4562747 : Blo 1999435 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B3041831 : Blo 1999435 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B8111549 : Blo 1999435 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B21630797 : Blo 1999435 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B14420531 : Blo 1999435 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B9613687 : Blo 1999435 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B12818249 : Blo 1999435 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B8545499 : Blo 1999435 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B5696999 : Blo 1999435 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B3797999 : Blo 1999435 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B2531999 : Blo 1999435 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B6751997 : Blo 1999435 6751997 := bstep (se 3 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 6751997 = 2531999) B2531999
theorem B4501331 : Blo 1999435 4501331 := bstep (se 1 (by rfl) ⟨3375998, by rfl⟩ : syracuseStep 4501331 = 6751997) B6751997
theorem B3000887 : Blo 1999435 3000887 := bstep (se 1 (by rfl) ⟨2250665, by rfl⟩ : syracuseStep 3000887 = 4501331) B4501331
theorem B2000591 : Blo 1999435 2000591 := bstep (se 1 (by rfl) ⟨1500443, by rfl⟩ : syracuseStep 2000591 = 3000887) B3000887
theorem B3000893 : Blo 1999435 3000893 := bbase (se 3 (by rfl) ⟨562667, by rfl⟩ : syracuseStep 3000893 = 1125335) (by norm_num)
theorem B2000595 : Blo 1999435 2000595 := bstep (se 1 (by rfl) ⟨1500446, by rfl⟩ : syracuseStep 2000595 = 3000893) B3000893
theorem B4501349 : Blo 1999435 4501349 := bbase (se 4 (by rfl) ⟨422001, by rfl⟩ : syracuseStep 4501349 = 844003) (by norm_num)
theorem B3000899 : Blo 1999435 3000899 := bstep (se 1 (by rfl) ⟨2250674, by rfl⟩ : syracuseStep 3000899 = 4501349) B4501349
theorem B2000599 : Blo 1999435 2000599 := bstep (se 1 (by rfl) ⟨1500449, by rfl⟩ : syracuseStep 2000599 = 3000899) B3000899
theorem B5064029 : Blo 1999435 5064029 := bbase (se 3 (by rfl) ⟨949505, by rfl⟩ : syracuseStep 5064029 = 1899011) (by norm_num)
theorem B3376019 : Blo 1999435 3376019 := bstep (se 1 (by rfl) ⟨2532014, by rfl⟩ : syracuseStep 3376019 = 5064029) B5064029
theorem B2250679 : Blo 1999435 2250679 := bstep (se 1 (by rfl) ⟨1688009, by rfl⟩ : syracuseStep 2250679 = 3376019) B3376019
theorem B3000905 : Blo 1999435 3000905 := bstep (se 2 (by rfl) ⟨1125339, by rfl⟩ : syracuseStep 3000905 = 2250679) B2250679
theorem B2000603 : Blo 1999435 2000603 := bstep (se 1 (by rfl) ⟨1500452, by rfl⟩ : syracuseStep 2000603 = 3000905) B3000905
theorem B3798029 : Blo 1999435 3798029 := bbase (se 3 (by rfl) ⟨712130, by rfl⟩ : syracuseStep 3798029 = 1424261) (by norm_num)
theorem B10128077 : Blo 1999435 10128077 := bstep (se 3 (by rfl) ⟨1899014, by rfl⟩ : syracuseStep 10128077 = 3798029) B3798029
theorem B6752051 : Blo 1999435 6752051 := bstep (se 1 (by rfl) ⟨5064038, by rfl⟩ : syracuseStep 6752051 = 10128077) B10128077
theorem B4501367 : Blo 1999435 4501367 := bstep (se 1 (by rfl) ⟨3376025, by rfl⟩ : syracuseStep 4501367 = 6752051) B6752051
theorem B3000911 : Blo 1999435 3000911 := bstep (se 1 (by rfl) ⟨2250683, by rfl⟩ : syracuseStep 3000911 = 4501367) B4501367
theorem B2000607 : Blo 1999435 2000607 := bstep (se 1 (by rfl) ⟨1500455, by rfl⟩ : syracuseStep 2000607 = 3000911) B3000911
theorem B3000917 : Blo 1999435 3000917 := bbase (se 8 (by rfl) ⟨17583, by rfl⟩ : syracuseStep 3000917 = 35167) (by norm_num)
theorem B2000611 : Blo 1999435 2000611 := bstep (se 1 (by rfl) ⟨1500458, by rfl⟩ : syracuseStep 2000611 = 3000917) B3000917
theorem B4806901 : Blo 1999435 4806901 := bbase (se 5 (by rfl) ⟨225323, by rfl⟩ : syracuseStep 4806901 = 450647) (by norm_num)
theorem B6409201 : Blo 1999435 6409201 := bstep (se 2 (by rfl) ⟨2403450, by rfl⟩ : syracuseStep 6409201 = 4806901) B4806901
theorem B8545601 : Blo 1999435 8545601 := bstep (se 2 (by rfl) ⟨3204600, by rfl⟩ : syracuseStep 8545601 = 6409201) B6409201
theorem B5697067 : Blo 1999435 5697067 := bstep (se 1 (by rfl) ⟨4272800, by rfl⟩ : syracuseStep 5697067 = 8545601) B8545601
theorem B7596089 : Blo 1999435 7596089 := bstep (se 2 (by rfl) ⟨2848533, by rfl⟩ : syracuseStep 7596089 = 5697067) B5697067
theorem B5064059 : Blo 1999435 5064059 := bstep (se 1 (by rfl) ⟨3798044, by rfl⟩ : syracuseStep 5064059 = 7596089) B7596089
theorem B3376039 : Blo 1999435 3376039 := bstep (se 1 (by rfl) ⟨2532029, by rfl⟩ : syracuseStep 3376039 = 5064059) B5064059
theorem B4501385 : Blo 1999435 4501385 := bstep (se 2 (by rfl) ⟨1688019, by rfl⟩ : syracuseStep 4501385 = 3376039) B3376039
theorem B3000923 : Blo 1999435 3000923 := bstep (se 1 (by rfl) ⟨2250692, by rfl⟩ : syracuseStep 3000923 = 4501385) B4501385
theorem B2000615 : Blo 1999435 2000615 := bstep (se 1 (by rfl) ⟨1500461, by rfl⟩ : syracuseStep 2000615 = 3000923) B3000923
theorem B2250697 : Blo 1999435 2250697 := bbase (se 2 (by rfl) ⟨844011, by rfl⟩ : syracuseStep 2250697 = 1688023) (by norm_num)
theorem B3000929 : Blo 1999435 3000929 := bstep (se 2 (by rfl) ⟨1125348, by rfl⟩ : syracuseStep 3000929 = 2250697) B2250697
theorem B2000619 : Blo 1999435 2000619 := bstep (se 1 (by rfl) ⟨1500464, by rfl⟩ : syracuseStep 2000619 = 3000929) B3000929
theorem B3204613 : Blo 1999435 3204613 := bbase (se 4 (by rfl) ⟨300432, by rfl⟩ : syracuseStep 3204613 = 600865) (by norm_num)
theorem B17091269 : Blo 1999435 17091269 := bstep (se 4 (by rfl) ⟨1602306, by rfl⟩ : syracuseStep 17091269 = 3204613) B3204613
theorem B11394179 : Blo 1999435 11394179 := bstep (se 1 (by rfl) ⟨8545634, by rfl⟩ : syracuseStep 11394179 = 17091269) B17091269
theorem B7596119 : Blo 1999435 7596119 := bstep (se 1 (by rfl) ⟨5697089, by rfl⟩ : syracuseStep 7596119 = 11394179) B11394179
theorem B5064079 : Blo 1999435 5064079 := bstep (se 1 (by rfl) ⟨3798059, by rfl⟩ : syracuseStep 5064079 = 7596119) B7596119
theorem B6752105 : Blo 1999435 6752105 := bstep (se 2 (by rfl) ⟨2532039, by rfl⟩ : syracuseStep 6752105 = 5064079) B5064079
theorem B4501403 : Blo 1999435 4501403 := bstep (se 1 (by rfl) ⟨3376052, by rfl⟩ : syracuseStep 4501403 = 6752105) B6752105
theorem B3000935 : Blo 1999435 3000935 := bstep (se 1 (by rfl) ⟨2250701, by rfl⟩ : syracuseStep 3000935 = 4501403) B4501403
theorem B2000623 : Blo 1999435 2000623 := bstep (se 1 (by rfl) ⟨1500467, by rfl⟩ : syracuseStep 2000623 = 3000935) B3000935
theorem B3000941 : Blo 1999435 3000941 := bbase (se 3 (by rfl) ⟨562676, by rfl⟩ : syracuseStep 3000941 = 1125353) (by norm_num)
theorem B2000627 : Blo 1999435 2000627 := bstep (se 1 (by rfl) ⟨1500470, by rfl⟩ : syracuseStep 2000627 = 3000941) B3000941
theorem B4501421 : Blo 1999435 4501421 := bbase (se 3 (by rfl) ⟨844016, by rfl⟩ : syracuseStep 4501421 = 1688033) (by norm_num)
theorem B3000947 : Blo 1999435 3000947 := bstep (se 1 (by rfl) ⟨2250710, by rfl⟩ : syracuseStep 3000947 = 4501421) B4501421
theorem B2000631 : Blo 1999435 2000631 := bstep (se 1 (by rfl) ⟨1500473, by rfl⟩ : syracuseStep 2000631 = 3000947) B3000947
theorem B5697125 : Blo 1999435 5697125 := bbase (se 4 (by rfl) ⟨534105, by rfl⟩ : syracuseStep 5697125 = 1068211) (by norm_num)
theorem B3798083 : Blo 1999435 3798083 := bstep (se 1 (by rfl) ⟨2848562, by rfl⟩ : syracuseStep 3798083 = 5697125) B5697125
theorem B2532055 : Blo 1999435 2532055 := bstep (se 1 (by rfl) ⟨1899041, by rfl⟩ : syracuseStep 2532055 = 3798083) B3798083
theorem B3376073 : Blo 1999435 3376073 := bstep (se 2 (by rfl) ⟨1266027, by rfl⟩ : syracuseStep 3376073 = 2532055) B2532055
theorem B2250715 : Blo 1999435 2250715 := bstep (se 1 (by rfl) ⟨1688036, by rfl⟩ : syracuseStep 2250715 = 3376073) B3376073
theorem B3000953 : Blo 1999435 3000953 := bstep (se 2 (by rfl) ⟨1125357, by rfl⟩ : syracuseStep 3000953 = 2250715) B2250715
theorem B2000635 : Blo 1999435 2000635 := bstep (se 1 (by rfl) ⟨1500476, by rfl⟩ : syracuseStep 2000635 = 3000953) B3000953
theorem B3083405 : Blo 1999435 3083405 := bbase (se 3 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 3083405 = 1156277) (by norm_num)
theorem B32889653 : Blo 1999435 32889653 := bstep (se 5 (by rfl) ⟨1541702, by rfl⟩ : syracuseStep 32889653 = 3083405) B3083405
theorem B21926435 : Blo 1999435 21926435 := bstep (se 1 (by rfl) ⟨16444826, by rfl⟩ : syracuseStep 21926435 = 32889653) B32889653
theorem B58470493 : Blo 1999435 58470493 := bstep (se 3 (by rfl) ⟨10963217, by rfl⟩ : syracuseStep 58470493 = 21926435) B21926435
theorem B77960657 : Blo 1999435 77960657 := bstep (se 2 (by rfl) ⟨29235246, by rfl⟩ : syracuseStep 77960657 = 58470493) B58470493
theorem B51973771 : Blo 1999435 51973771 := bstep (se 1 (by rfl) ⟨38980328, by rfl⟩ : syracuseStep 51973771 = 77960657) B77960657
theorem B69298361 : Blo 1999435 69298361 := bstep (se 2 (by rfl) ⟨25986885, by rfl⟩ : syracuseStep 69298361 = 51973771) B51973771
theorem B46198907 : Blo 1999435 46198907 := bstep (se 1 (by rfl) ⟨34649180, by rfl⟩ : syracuseStep 46198907 = 69298361) B69298361
theorem B30799271 : Blo 1999435 30799271 := bstep (se 1 (by rfl) ⟨23099453, by rfl⟩ : syracuseStep 30799271 = 46198907) B46198907
theorem B20532847 : Blo 1999435 20532847 := bstep (se 1 (by rfl) ⟨15399635, by rfl⟩ : syracuseStep 20532847 = 30799271) B30799271
theorem B27377129 : Blo 1999435 27377129 := bstep (se 2 (by rfl) ⟨10266423, by rfl⟩ : syracuseStep 27377129 = 20532847) B20532847
theorem B18251419 : Blo 1999435 18251419 := bstep (se 1 (by rfl) ⟨13688564, by rfl⟩ : syracuseStep 18251419 = 27377129) B27377129
theorem B24335225 : Blo 1999435 24335225 := bstep (se 2 (by rfl) ⟨9125709, by rfl⟩ : syracuseStep 24335225 = 18251419) B18251419
theorem B16223483 : Blo 1999435 16223483 := bstep (se 1 (by rfl) ⟨12167612, by rfl⟩ : syracuseStep 16223483 = 24335225) B24335225
theorem B10815655 : Blo 1999435 10815655 := bstep (se 1 (by rfl) ⟨8111741, by rfl⟩ : syracuseStep 10815655 = 16223483) B16223483
theorem B14420873 : Blo 1999435 14420873 := bstep (se 2 (by rfl) ⟨5407827, by rfl⟩ : syracuseStep 14420873 = 10815655) B10815655
theorem B38455661 : Blo 1999435 38455661 := bstep (se 3 (by rfl) ⟨7210436, by rfl⟩ : syracuseStep 38455661 = 14420873) B14420873
theorem B25637107 : Blo 1999435 25637107 := bstep (se 1 (by rfl) ⟨19227830, by rfl⟩ : syracuseStep 25637107 = 38455661) B38455661
theorem B34182809 : Blo 1999435 34182809 := bstep (se 2 (by rfl) ⟨12818553, by rfl⟩ : syracuseStep 34182809 = 25637107) B25637107
theorem B22788539 : Blo 1999435 22788539 := bstep (se 1 (by rfl) ⟨17091404, by rfl⟩ : syracuseStep 22788539 = 34182809) B34182809
theorem B15192359 : Blo 1999435 15192359 := bstep (se 1 (by rfl) ⟨11394269, by rfl⟩ : syracuseStep 15192359 = 22788539) B22788539
theorem B10128239 : Blo 1999435 10128239 := bstep (se 1 (by rfl) ⟨7596179, by rfl⟩ : syracuseStep 10128239 = 15192359) B15192359
theorem B6752159 : Blo 1999435 6752159 := bstep (se 1 (by rfl) ⟨5064119, by rfl⟩ : syracuseStep 6752159 = 10128239) B10128239
theorem B4501439 : Blo 1999435 4501439 := bstep (se 1 (by rfl) ⟨3376079, by rfl⟩ : syracuseStep 4501439 = 6752159) B6752159
theorem B3000959 : Blo 1999435 3000959 := bstep (se 1 (by rfl) ⟨2250719, by rfl⟩ : syracuseStep 3000959 = 4501439) B4501439
theorem B2000639 : Blo 1999435 2000639 := bstep (se 1 (by rfl) ⟨1500479, by rfl⟩ : syracuseStep 2000639 = 3000959) B3000959
theorem B3000965 : Blo 1999435 3000965 := bbase (se 4 (by rfl) ⟨281340, by rfl⟩ : syracuseStep 3000965 = 562681) (by norm_num)
theorem B2000643 : Blo 1999435 2000643 := bstep (se 1 (by rfl) ⟨1500482, by rfl⟩ : syracuseStep 2000643 = 3000965) B3000965
theorem B3376093 : Blo 1999435 3376093 := bbase (se 3 (by rfl) ⟨633017, by rfl⟩ : syracuseStep 3376093 = 1266035) (by norm_num)
theorem B4501457 : Blo 1999435 4501457 := bstep (se 2 (by rfl) ⟨1688046, by rfl⟩ : syracuseStep 4501457 = 3376093) B3376093
theorem B3000971 : Blo 1999435 3000971 := bstep (se 1 (by rfl) ⟨2250728, by rfl⟩ : syracuseStep 3000971 = 4501457) B4501457
theorem B2000647 : Blo 1999435 2000647 := bstep (se 1 (by rfl) ⟨1500485, by rfl⟩ : syracuseStep 2000647 = 3000971) B3000971
theorem B2250733 : Blo 1999435 2250733 := bbase (se 3 (by rfl) ⟨422012, by rfl⟩ : syracuseStep 2250733 = 844025) (by norm_num)
theorem B3000977 : Blo 1999435 3000977 := bstep (se 2 (by rfl) ⟨1125366, by rfl⟩ : syracuseStep 3000977 = 2250733) B2250733
theorem B2000651 : Blo 1999435 2000651 := bstep (se 1 (by rfl) ⟨1500488, by rfl⟩ : syracuseStep 2000651 = 3000977) B3000977
theorem B6752213 : Blo 1999435 6752213 := bbase (se 7 (by rfl) ⟨79127, by rfl⟩ : syracuseStep 6752213 = 158255) (by norm_num)
theorem B4501475 : Blo 1999435 4501475 := bstep (se 1 (by rfl) ⟨3376106, by rfl⟩ : syracuseStep 4501475 = 6752213) B6752213
theorem B3000983 : Blo 1999435 3000983 := bstep (se 1 (by rfl) ⟨2250737, by rfl⟩ : syracuseStep 3000983 = 4501475) B4501475
theorem B2000655 : Blo 1999435 2000655 := bstep (se 1 (by rfl) ⟨1500491, by rfl⟩ : syracuseStep 2000655 = 3000983) B3000983
theorem B3000989 : Blo 1999435 3000989 := bbase (se 3 (by rfl) ⟨562685, by rfl⟩ : syracuseStep 3000989 = 1125371) (by norm_num)
theorem B2000659 : Blo 1999435 2000659 := bstep (se 1 (by rfl) ⟨1500494, by rfl⟩ : syracuseStep 2000659 = 3000989) B3000989
theorem B4501493 : Blo 1999435 4501493 := bbase (se 5 (by rfl) ⟨211007, by rfl⟩ : syracuseStep 4501493 = 422015) (by norm_num)
theorem B3000995 : Blo 1999435 3000995 := bstep (se 1 (by rfl) ⟨2250746, by rfl⟩ : syracuseStep 3000995 = 4501493) B4501493
theorem B2000663 : Blo 1999435 2000663 := bstep (se 1 (by rfl) ⟨1500497, by rfl⟩ : syracuseStep 2000663 = 3000995) B3000995
theorem B7308917 : Blo 1999435 7308917 := bbase (se 5 (by rfl) ⟨342605, by rfl⟩ : syracuseStep 7308917 = 685211) (by norm_num)
theorem B4872611 : Blo 1999435 4872611 := bstep (se 1 (by rfl) ⟨3654458, by rfl⟩ : syracuseStep 4872611 = 7308917) B7308917
theorem B3248407 : Blo 1999435 3248407 := bstep (se 1 (by rfl) ⟨2436305, by rfl⟩ : syracuseStep 3248407 = 4872611) B4872611
theorem B17324837 : Blo 1999435 17324837 := bstep (se 4 (by rfl) ⟨1624203, by rfl⟩ : syracuseStep 17324837 = 3248407) B3248407
theorem B11549891 : Blo 1999435 11549891 := bstep (se 1 (by rfl) ⟨8662418, by rfl⟩ : syracuseStep 11549891 = 17324837) B17324837
theorem B7699927 : Blo 1999435 7699927 := bstep (se 1 (by rfl) ⟨5774945, by rfl⟩ : syracuseStep 7699927 = 11549891) B11549891
theorem B10266569 : Blo 1999435 10266569 := bstep (se 2 (by rfl) ⟨3849963, by rfl⟩ : syracuseStep 10266569 = 7699927) B7699927
theorem B6844379 : Blo 1999435 6844379 := bstep (se 1 (by rfl) ⟨5133284, by rfl⟩ : syracuseStep 6844379 = 10266569) B10266569
theorem B18251677 : Blo 1999435 18251677 := bstep (se 3 (by rfl) ⟨3422189, by rfl⟩ : syracuseStep 18251677 = 6844379) B6844379
theorem B24335569 : Blo 1999435 24335569 := bstep (se 2 (by rfl) ⟨9125838, by rfl⟩ : syracuseStep 24335569 = 18251677) B18251677
theorem B129789701 : Blo 1999435 129789701 := bstep (se 4 (by rfl) ⟨12167784, by rfl⟩ : syracuseStep 129789701 = 24335569) B24335569
theorem B86526467 : Blo 1999435 86526467 := bstep (se 1 (by rfl) ⟨64894850, by rfl⟩ : syracuseStep 86526467 = 129789701) B129789701
theorem B57684311 : Blo 1999435 57684311 := bstep (se 1 (by rfl) ⟨43263233, by rfl⟩ : syracuseStep 57684311 = 86526467) B86526467
theorem B38456207 : Blo 1999435 38456207 := bstep (se 1 (by rfl) ⟨28842155, by rfl⟩ : syracuseStep 38456207 = 57684311) B57684311
theorem B25637471 : Blo 1999435 25637471 := bstep (se 1 (by rfl) ⟨19228103, by rfl⟩ : syracuseStep 25637471 = 38456207) B38456207
theorem B17091647 : Blo 1999435 17091647 := bstep (se 1 (by rfl) ⟨12818735, by rfl⟩ : syracuseStep 17091647 = 25637471) B25637471
theorem B11394431 : Blo 1999435 11394431 := bstep (se 1 (by rfl) ⟨8545823, by rfl⟩ : syracuseStep 11394431 = 17091647) B17091647
theorem B7596287 : Blo 1999435 7596287 := bstep (se 1 (by rfl) ⟨5697215, by rfl⟩ : syracuseStep 7596287 = 11394431) B11394431
theorem B5064191 : Blo 1999435 5064191 := bstep (se 1 (by rfl) ⟨3798143, by rfl⟩ : syracuseStep 5064191 = 7596287) B7596287
theorem B3376127 : Blo 1999435 3376127 := bstep (se 1 (by rfl) ⟨2532095, by rfl⟩ : syracuseStep 3376127 = 5064191) B5064191
theorem B2250751 : Blo 1999435 2250751 := bstep (se 1 (by rfl) ⟨1688063, by rfl⟩ : syracuseStep 2250751 = 3376127) B3376127
theorem B3001001 : Blo 1999435 3001001 := bstep (se 2 (by rfl) ⟨1125375, by rfl⟩ : syracuseStep 3001001 = 2250751) B2250751
theorem B2000667 : Blo 1999435 2000667 := bstep (se 1 (by rfl) ⟨1500500, by rfl⟩ : syracuseStep 2000667 = 3001001) B3001001
theorem B2848613 : Blo 1999435 2848613 := bbase (se 4 (by rfl) ⟨267057, by rfl⟩ : syracuseStep 2848613 = 534115) (by norm_num)
theorem B7596301 : Blo 1999435 7596301 := bstep (se 3 (by rfl) ⟨1424306, by rfl⟩ : syracuseStep 7596301 = 2848613) B2848613
theorem B10128401 : Blo 1999435 10128401 := bstep (se 2 (by rfl) ⟨3798150, by rfl⟩ : syracuseStep 10128401 = 7596301) B7596301
theorem B6752267 : Blo 1999435 6752267 := bstep (se 1 (by rfl) ⟨5064200, by rfl⟩ : syracuseStep 6752267 = 10128401) B10128401
theorem B4501511 : Blo 1999435 4501511 := bstep (se 1 (by rfl) ⟨3376133, by rfl⟩ : syracuseStep 4501511 = 6752267) B6752267
theorem B3001007 : Blo 1999435 3001007 := bstep (se 1 (by rfl) ⟨2250755, by rfl⟩ : syracuseStep 3001007 = 4501511) B4501511
theorem B2000671 : Blo 1999435 2000671 := bstep (se 1 (by rfl) ⟨1500503, by rfl⟩ : syracuseStep 2000671 = 3001007) B3001007
theorem B3001013 : Blo 1999435 3001013 := bbase (se 5 (by rfl) ⟨140672, by rfl⟩ : syracuseStep 3001013 = 281345) (by norm_num)
theorem B2000675 : Blo 1999435 2000675 := bstep (se 1 (by rfl) ⟨1500506, by rfl⟩ : syracuseStep 2000675 = 3001013) B3001013
theorem B5064221 : Blo 1999435 5064221 := bbase (se 3 (by rfl) ⟨949541, by rfl⟩ : syracuseStep 5064221 = 1899083) (by norm_num)
theorem B3376147 : Blo 1999435 3376147 := bstep (se 1 (by rfl) ⟨2532110, by rfl⟩ : syracuseStep 3376147 = 5064221) B5064221
theorem B4501529 : Blo 1999435 4501529 := bstep (se 2 (by rfl) ⟨1688073, by rfl⟩ : syracuseStep 4501529 = 3376147) B3376147
theorem B3001019 : Blo 1999435 3001019 := bstep (se 1 (by rfl) ⟨2250764, by rfl⟩ : syracuseStep 3001019 = 4501529) B4501529
theorem B2000679 : Blo 1999435 2000679 := bstep (se 1 (by rfl) ⟨1500509, by rfl⟩ : syracuseStep 2000679 = 3001019) B3001019
theorem B2250769 : Blo 1999435 2250769 := bbase (se 2 (by rfl) ⟨844038, by rfl⟩ : syracuseStep 2250769 = 1688077) (by norm_num)
theorem B3001025 : Blo 1999435 3001025 := bstep (se 2 (by rfl) ⟨1125384, by rfl⟩ : syracuseStep 3001025 = 2250769) B2250769
theorem B2000683 : Blo 1999435 2000683 := bstep (se 1 (by rfl) ⟨1500512, by rfl⟩ : syracuseStep 2000683 = 3001025) B3001025
theorem B3798181 : Blo 1999435 3798181 := bbase (se 4 (by rfl) ⟨356079, by rfl⟩ : syracuseStep 3798181 = 712159) (by norm_num)
theorem B5064241 : Blo 1999435 5064241 := bstep (se 2 (by rfl) ⟨1899090, by rfl⟩ : syracuseStep 5064241 = 3798181) B3798181
theorem B6752321 : Blo 1999435 6752321 := bstep (se 2 (by rfl) ⟨2532120, by rfl⟩ : syracuseStep 6752321 = 5064241) B5064241
theorem B4501547 : Blo 1999435 4501547 := bstep (se 1 (by rfl) ⟨3376160, by rfl⟩ : syracuseStep 4501547 = 6752321) B6752321
theorem B3001031 : Blo 1999435 3001031 := bstep (se 1 (by rfl) ⟨2250773, by rfl⟩ : syracuseStep 3001031 = 4501547) B4501547
theorem B2000687 : Blo 1999435 2000687 := bstep (se 1 (by rfl) ⟨1500515, by rfl⟩ : syracuseStep 2000687 = 3001031) B3001031
theorem B3001037 : Blo 1999435 3001037 := bbase (se 3 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 3001037 = 1125389) (by norm_num)
theorem B2000691 : Blo 1999435 2000691 := bstep (se 1 (by rfl) ⟨1500518, by rfl⟩ : syracuseStep 2000691 = 3001037) B3001037
theorem B4501565 : Blo 1999435 4501565 := bbase (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) (by norm_num)
theorem B3001043 : Blo 1999435 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B2000695 : Blo 1999435 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B3376181 : Blo 1999435 3376181 := bbase (se 5 (by rfl) ⟨158258, by rfl⟩ : syracuseStep 3376181 = 316517) (by norm_num)
theorem B2250787 : Blo 1999435 2250787 := bstep (se 1 (by rfl) ⟨1688090, by rfl⟩ : syracuseStep 2250787 = 3376181) B3376181
theorem B3001049 : Blo 1999435 3001049 := bstep (se 2 (by rfl) ⟨1125393, by rfl⟩ : syracuseStep 3001049 = 2250787) B2250787
theorem B2000699 : Blo 1999435 2000699 := bstep (se 1 (by rfl) ⟨1500524, by rfl⟩ : syracuseStep 2000699 = 3001049) B3001049
theorem B5697317 : Blo 1999435 5697317 := bbase (se 4 (by rfl) ⟨534123, by rfl⟩ : syracuseStep 5697317 = 1068247) (by norm_num)
theorem B15192845 : Blo 1999435 15192845 := bstep (se 3 (by rfl) ⟨2848658, by rfl⟩ : syracuseStep 15192845 = 5697317) B5697317
theorem B10128563 : Blo 1999435 10128563 := bstep (se 1 (by rfl) ⟨7596422, by rfl⟩ : syracuseStep 10128563 = 15192845) B15192845
theorem B6752375 : Blo 1999435 6752375 := bstep (se 1 (by rfl) ⟨5064281, by rfl⟩ : syracuseStep 6752375 = 10128563) B10128563
theorem B4501583 : Blo 1999435 4501583 := bstep (se 1 (by rfl) ⟨3376187, by rfl⟩ : syracuseStep 4501583 = 6752375) B6752375
theorem B3001055 : Blo 1999435 3001055 := bstep (se 1 (by rfl) ⟨2250791, by rfl⟩ : syracuseStep 3001055 = 4501583) B4501583
theorem B2000703 : Blo 1999435 2000703 := bstep (se 1 (by rfl) ⟨1500527, by rfl⟩ : syracuseStep 2000703 = 3001055) B3001055
theorem B3001061 : Blo 1999435 3001061 := bbase (se 4 (by rfl) ⟨281349, by rfl⟩ : syracuseStep 3001061 = 562699) (by norm_num)
theorem B2000707 : Blo 1999435 2000707 := bstep (se 1 (by rfl) ⟨1500530, by rfl⟩ : syracuseStep 2000707 = 3001061) B3001061
theorem B4807133 : Blo 1999435 4807133 := bbase (se 3 (by rfl) ⟨901337, by rfl⟩ : syracuseStep 4807133 = 1802675) (by norm_num)
theorem B3204755 : Blo 1999435 3204755 := bstep (se 1 (by rfl) ⟨2403566, by rfl⟩ : syracuseStep 3204755 = 4807133) B4807133
theorem B2136503 : Blo 1999435 2136503 := bstep (se 1 (by rfl) ⟨1602377, by rfl⟩ : syracuseStep 2136503 = 3204755) B3204755
theorem B5697341 : Blo 1999435 5697341 := bstep (se 3 (by rfl) ⟨1068251, by rfl⟩ : syracuseStep 5697341 = 2136503) B2136503
theorem B3798227 : Blo 1999435 3798227 := bstep (se 1 (by rfl) ⟨2848670, by rfl⟩ : syracuseStep 3798227 = 5697341) B5697341
theorem B2532151 : Blo 1999435 2532151 := bstep (se 1 (by rfl) ⟨1899113, by rfl⟩ : syracuseStep 2532151 = 3798227) B3798227
theorem B3376201 : Blo 1999435 3376201 := bstep (se 2 (by rfl) ⟨1266075, by rfl⟩ : syracuseStep 3376201 = 2532151) B2532151
theorem B4501601 : Blo 1999435 4501601 := bstep (se 2 (by rfl) ⟨1688100, by rfl⟩ : syracuseStep 4501601 = 3376201) B3376201
theorem B3001067 : Blo 1999435 3001067 := bstep (se 1 (by rfl) ⟨2250800, by rfl⟩ : syracuseStep 3001067 = 4501601) B4501601
theorem B2000711 : Blo 1999435 2000711 := bstep (se 1 (by rfl) ⟨1500533, by rfl⟩ : syracuseStep 2000711 = 3001067) B3001067
theorem B2250805 : Blo 1999435 2250805 := bbase (se 5 (by rfl) ⟨105506, by rfl⟩ : syracuseStep 2250805 = 211013) (by norm_num)
theorem B3001073 : Blo 1999435 3001073 := bstep (se 2 (by rfl) ⟨1125402, by rfl⟩ : syracuseStep 3001073 = 2250805) B2250805
theorem B2000715 : Blo 1999435 2000715 := bstep (se 1 (by rfl) ⟨1500536, by rfl⟩ : syracuseStep 2000715 = 3001073) B3001073
theorem B2532161 : Blo 1999435 2532161 := bbase (se 2 (by rfl) ⟨949560, by rfl⟩ : syracuseStep 2532161 = 1899121) (by norm_num)
theorem B6752429 : Blo 1999435 6752429 := bstep (se 3 (by rfl) ⟨1266080, by rfl⟩ : syracuseStep 6752429 = 2532161) B2532161
theorem B4501619 : Blo 1999435 4501619 := bstep (se 1 (by rfl) ⟨3376214, by rfl⟩ : syracuseStep 4501619 = 6752429) B6752429
theorem B3001079 : Blo 1999435 3001079 := bstep (se 1 (by rfl) ⟨2250809, by rfl⟩ : syracuseStep 3001079 = 4501619) B4501619
theorem B2000719 : Blo 1999435 2000719 := bstep (se 1 (by rfl) ⟨1500539, by rfl⟩ : syracuseStep 2000719 = 3001079) B3001079
theorem B3001085 : Blo 1999435 3001085 := bbase (se 3 (by rfl) ⟨562703, by rfl⟩ : syracuseStep 3001085 = 1125407) (by norm_num)
theorem B2000723 : Blo 1999435 2000723 := bstep (se 1 (by rfl) ⟨1500542, by rfl⟩ : syracuseStep 2000723 = 3001085) B3001085
theorem B4501637 : Blo 1999435 4501637 := bbase (se 4 (by rfl) ⟨422028, by rfl⟩ : syracuseStep 4501637 = 844057) (by norm_num)
theorem B3001091 : Blo 1999435 3001091 := bstep (se 1 (by rfl) ⟨2250818, by rfl⟩ : syracuseStep 3001091 = 4501637) B4501637
theorem B2000727 : Blo 1999435 2000727 := bstep (se 1 (by rfl) ⟨1500545, by rfl⟩ : syracuseStep 2000727 = 3001091) B3001091
theorem B4807181 : Blo 1999435 4807181 := bbase (se 3 (by rfl) ⟨901346, by rfl⟩ : syracuseStep 4807181 = 1802693) (by norm_num)
theorem B3204787 : Blo 1999435 3204787 := bstep (se 1 (by rfl) ⟨2403590, by rfl⟩ : syracuseStep 3204787 = 4807181) B4807181
theorem B4273049 : Blo 1999435 4273049 := bstep (se 2 (by rfl) ⟨1602393, by rfl⟩ : syracuseStep 4273049 = 3204787) B3204787
theorem B2848699 : Blo 1999435 2848699 := bstep (se 1 (by rfl) ⟨2136524, by rfl⟩ : syracuseStep 2848699 = 4273049) B4273049
theorem B3798265 : Blo 1999435 3798265 := bstep (se 2 (by rfl) ⟨1424349, by rfl⟩ : syracuseStep 3798265 = 2848699) B2848699
theorem B5064353 : Blo 1999435 5064353 := bstep (se 2 (by rfl) ⟨1899132, by rfl⟩ : syracuseStep 5064353 = 3798265) B3798265
theorem B3376235 : Blo 1999435 3376235 := bstep (se 1 (by rfl) ⟨2532176, by rfl⟩ : syracuseStep 3376235 = 5064353) B5064353
theorem B2250823 : Blo 1999435 2250823 := bstep (se 1 (by rfl) ⟨1688117, by rfl⟩ : syracuseStep 2250823 = 3376235) B3376235
theorem B3001097 : Blo 1999435 3001097 := bstep (se 2 (by rfl) ⟨1125411, by rfl⟩ : syracuseStep 3001097 = 2250823) B2250823
theorem B2000731 : Blo 1999435 2000731 := bstep (se 1 (by rfl) ⟨1500548, by rfl⟩ : syracuseStep 2000731 = 3001097) B3001097
theorem B10128725 : Blo 1999435 10128725 := bbase (se 11 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 10128725 = 14837) (by norm_num)
theorem B6752483 : Blo 1999435 6752483 := bstep (se 1 (by rfl) ⟨5064362, by rfl⟩ : syracuseStep 6752483 = 10128725) B10128725
theorem B4501655 : Blo 1999435 4501655 := bstep (se 1 (by rfl) ⟨3376241, by rfl⟩ : syracuseStep 4501655 = 6752483) B6752483
theorem B3001103 : Blo 1999435 3001103 := bstep (se 1 (by rfl) ⟨2250827, by rfl⟩ : syracuseStep 3001103 = 4501655) B4501655
theorem B2000735 : Blo 1999435 2000735 := bstep (se 1 (by rfl) ⟨1500551, by rfl⟩ : syracuseStep 2000735 = 3001103) B3001103
theorem B3001109 : Blo 1999435 3001109 := bbase (se 6 (by rfl) ⟨70338, by rfl⟩ : syracuseStep 3001109 = 140677) (by norm_num)
theorem B2000739 : Blo 1999435 2000739 := bstep (se 1 (by rfl) ⟨1500554, by rfl⟩ : syracuseStep 2000739 = 3001109) B3001109
theorem B2028041 : Blo 1999435 2028041 := bbase (se 2 (by rfl) ⟨760515, by rfl⟩ : syracuseStep 2028041 = 1521031) (by norm_num)
theorem B21632437 : Blo 1999435 21632437 := bstep (se 5 (by rfl) ⟨1014020, by rfl⟩ : syracuseStep 21632437 = 2028041) B2028041
theorem B28843249 : Blo 1999435 28843249 := bstep (se 2 (by rfl) ⟨10816218, by rfl⟩ : syracuseStep 28843249 = 21632437) B21632437
theorem B38457665 : Blo 1999435 38457665 := bstep (se 2 (by rfl) ⟨14421624, by rfl⟩ : syracuseStep 38457665 = 28843249) B28843249
theorem B25638443 : Blo 1999435 25638443 := bstep (se 1 (by rfl) ⟨19228832, by rfl⟩ : syracuseStep 25638443 = 38457665) B38457665
theorem B17092295 : Blo 1999435 17092295 := bstep (se 1 (by rfl) ⟨12819221, by rfl⟩ : syracuseStep 17092295 = 25638443) B25638443
theorem B11394863 : Blo 1999435 11394863 := bstep (se 1 (by rfl) ⟨8546147, by rfl⟩ : syracuseStep 11394863 = 17092295) B17092295
theorem B7596575 : Blo 1999435 7596575 := bstep (se 1 (by rfl) ⟨5697431, by rfl⟩ : syracuseStep 7596575 = 11394863) B11394863
theorem B5064383 : Blo 1999435 5064383 := bstep (se 1 (by rfl) ⟨3798287, by rfl⟩ : syracuseStep 5064383 = 7596575) B7596575
theorem B3376255 : Blo 1999435 3376255 := bstep (se 1 (by rfl) ⟨2532191, by rfl⟩ : syracuseStep 3376255 = 5064383) B5064383
theorem B4501673 : Blo 1999435 4501673 := bstep (se 2 (by rfl) ⟨1688127, by rfl⟩ : syracuseStep 4501673 = 3376255) B3376255
theorem B3001115 : Blo 1999435 3001115 := bstep (se 1 (by rfl) ⟨2250836, by rfl⟩ : syracuseStep 3001115 = 4501673) B4501673
theorem B2000743 : Blo 1999435 2000743 := bstep (se 1 (by rfl) ⟨1500557, by rfl⟩ : syracuseStep 2000743 = 3001115) B3001115
theorem B2250841 : Blo 1999435 2250841 := bbase (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) (by norm_num)
theorem B3001121 : Blo 1999435 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B2000747 : Blo 1999435 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B6409637 : Blo 1999435 6409637 := bbase (se 4 (by rfl) ⟨600903, by rfl⟩ : syracuseStep 6409637 = 1201807) (by norm_num)
theorem B4273091 : Blo 1999435 4273091 := bstep (se 1 (by rfl) ⟨3204818, by rfl⟩ : syracuseStep 4273091 = 6409637) B6409637
theorem B2848727 : Blo 1999435 2848727 := bstep (se 1 (by rfl) ⟨2136545, by rfl⟩ : syracuseStep 2848727 = 4273091) B4273091
theorem B7596605 : Blo 1999435 7596605 := bstep (se 3 (by rfl) ⟨1424363, by rfl⟩ : syracuseStep 7596605 = 2848727) B2848727
theorem B5064403 : Blo 1999435 5064403 := bstep (se 1 (by rfl) ⟨3798302, by rfl⟩ : syracuseStep 5064403 = 7596605) B7596605
theorem B6752537 : Blo 1999435 6752537 := bstep (se 2 (by rfl) ⟨2532201, by rfl⟩ : syracuseStep 6752537 = 5064403) B5064403
theorem B4501691 : Blo 1999435 4501691 := bstep (se 1 (by rfl) ⟨3376268, by rfl⟩ : syracuseStep 4501691 = 6752537) B6752537
theorem B3001127 : Blo 1999435 3001127 := bstep (se 1 (by rfl) ⟨2250845, by rfl⟩ : syracuseStep 3001127 = 4501691) B4501691
theorem B2000751 : Blo 1999435 2000751 := bstep (se 1 (by rfl) ⟨1500563, by rfl⟩ : syracuseStep 2000751 = 3001127) B3001127
theorem B3001133 : Blo 1999435 3001133 := bbase (se 3 (by rfl) ⟨562712, by rfl⟩ : syracuseStep 3001133 = 1125425) (by norm_num)
theorem B2000755 : Blo 1999435 2000755 := bstep (se 1 (by rfl) ⟨1500566, by rfl⟩ : syracuseStep 2000755 = 3001133) B3001133
theorem B4501709 : Blo 1999435 4501709 := bbase (se 3 (by rfl) ⟨844070, by rfl⟩ : syracuseStep 4501709 = 1688141) (by norm_num)
theorem B3001139 : Blo 1999435 3001139 := bstep (se 1 (by rfl) ⟨2250854, by rfl⟩ : syracuseStep 3001139 = 4501709) B4501709
theorem B2000759 : Blo 1999435 2000759 := bstep (se 1 (by rfl) ⟨1500569, by rfl⟩ : syracuseStep 2000759 = 3001139) B3001139
theorem B2532217 : Blo 1999435 2532217 := bbase (se 2 (by rfl) ⟨949581, by rfl⟩ : syracuseStep 2532217 = 1899163) (by norm_num)
theorem B3376289 : Blo 1999435 3376289 := bstep (se 2 (by rfl) ⟨1266108, by rfl⟩ : syracuseStep 3376289 = 2532217) B2532217
theorem B2250859 : Blo 1999435 2250859 := bstep (se 1 (by rfl) ⟨1688144, by rfl⟩ : syracuseStep 2250859 = 3376289) B3376289
theorem B3001145 : Blo 1999435 3001145 := bstep (se 2 (by rfl) ⟨1125429, by rfl⟩ : syracuseStep 3001145 = 2250859) B2250859
theorem B2000763 : Blo 1999435 2000763 := bstep (se 1 (by rfl) ⟨1500572, by rfl⟩ : syracuseStep 2000763 = 3001145) B3001145
theorem B6084197 : Blo 1999435 6084197 := bbase (se 4 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 6084197 = 1140787) (by norm_num)
theorem B4056131 : Blo 1999435 4056131 := bstep (se 1 (by rfl) ⟨3042098, by rfl⟩ : syracuseStep 4056131 = 6084197) B6084197
theorem B2704087 : Blo 1999435 2704087 := bstep (se 1 (by rfl) ⟨2028065, by rfl⟩ : syracuseStep 2704087 = 4056131) B4056131
theorem B14421797 : Blo 1999435 14421797 := bstep (se 4 (by rfl) ⟨1352043, by rfl⟩ : syracuseStep 14421797 = 2704087) B2704087
theorem B9614531 : Blo 1999435 9614531 := bstep (se 1 (by rfl) ⟨7210898, by rfl⟩ : syracuseStep 9614531 = 14421797) B14421797
theorem B6409687 : Blo 1999435 6409687 := bstep (se 1 (by rfl) ⟨4807265, by rfl⟩ : syracuseStep 6409687 = 9614531) B9614531
theorem B8546249 : Blo 1999435 8546249 := bstep (se 2 (by rfl) ⟨3204843, by rfl⟩ : syracuseStep 8546249 = 6409687) B6409687
theorem B22789997 : Blo 1999435 22789997 := bstep (se 3 (by rfl) ⟨4273124, by rfl⟩ : syracuseStep 22789997 = 8546249) B8546249
theorem B15193331 : Blo 1999435 15193331 := bstep (se 1 (by rfl) ⟨11394998, by rfl⟩ : syracuseStep 15193331 = 22789997) B22789997
theorem B10128887 : Blo 1999435 10128887 := bstep (se 1 (by rfl) ⟨7596665, by rfl⟩ : syracuseStep 10128887 = 15193331) B15193331
theorem B6752591 : Blo 1999435 6752591 := bstep (se 1 (by rfl) ⟨5064443, by rfl⟩ : syracuseStep 6752591 = 10128887) B10128887
theorem B4501727 : Blo 1999435 4501727 := bstep (se 1 (by rfl) ⟨3376295, by rfl⟩ : syracuseStep 4501727 = 6752591) B6752591
theorem B3001151 : Blo 1999435 3001151 := bstep (se 1 (by rfl) ⟨2250863, by rfl⟩ : syracuseStep 3001151 = 4501727) B4501727
theorem B2000767 : Blo 1999435 2000767 := bstep (se 1 (by rfl) ⟨1500575, by rfl⟩ : syracuseStep 2000767 = 3001151) B3001151
theorem B3001157 : Blo 1999435 3001157 := bbase (se 4 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 3001157 = 562717) (by norm_num)
theorem B2000771 : Blo 1999435 2000771 := bstep (se 1 (by rfl) ⟨1500578, by rfl⟩ : syracuseStep 2000771 = 3001157) B3001157
theorem B3376309 : Blo 1999435 3376309 := bbase (se 5 (by rfl) ⟨158264, by rfl⟩ : syracuseStep 3376309 = 316529) (by norm_num)
theorem B4501745 : Blo 1999435 4501745 := bstep (se 2 (by rfl) ⟨1688154, by rfl⟩ : syracuseStep 4501745 = 3376309) B3376309
theorem B3001163 : Blo 1999435 3001163 := bstep (se 1 (by rfl) ⟨2250872, by rfl⟩ : syracuseStep 3001163 = 4501745) B4501745
theorem B2000775 : Blo 1999435 2000775 := bstep (se 1 (by rfl) ⟨1500581, by rfl⟩ : syracuseStep 2000775 = 3001163) B3001163
theorem B2250877 : Blo 1999435 2250877 := bbase (se 3 (by rfl) ⟨422039, by rfl⟩ : syracuseStep 2250877 = 844079) (by norm_num)
theorem B3001169 : Blo 1999435 3001169 := bstep (se 2 (by rfl) ⟨1125438, by rfl⟩ : syracuseStep 3001169 = 2250877) B2250877
theorem B2000779 : Blo 1999435 2000779 := bstep (se 1 (by rfl) ⟨1500584, by rfl⟩ : syracuseStep 2000779 = 3001169) B3001169
theorem B6752645 : Blo 1999435 6752645 := bbase (se 4 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 6752645 = 1266121) (by norm_num)
theorem B4501763 : Blo 1999435 4501763 := bstep (se 1 (by rfl) ⟨3376322, by rfl⟩ : syracuseStep 4501763 = 6752645) B6752645
theorem B3001175 : Blo 1999435 3001175 := bstep (se 1 (by rfl) ⟨2250881, by rfl⟩ : syracuseStep 3001175 = 4501763) B4501763
theorem B2000783 : Blo 1999435 2000783 := bstep (se 1 (by rfl) ⟨1500587, by rfl⟩ : syracuseStep 2000783 = 3001175) B3001175
theorem B3001181 : Blo 1999435 3001181 := bbase (se 3 (by rfl) ⟨562721, by rfl⟩ : syracuseStep 3001181 = 1125443) (by norm_num)
theorem B2000787 : Blo 1999435 2000787 := bstep (se 1 (by rfl) ⟨1500590, by rfl⟩ : syracuseStep 2000787 = 3001181) B3001181
theorem B4501781 : Blo 1999435 4501781 := bbase (se 6 (by rfl) ⟨105510, by rfl⟩ : syracuseStep 4501781 = 211021) (by norm_num)
theorem B3001187 : Blo 1999435 3001187 := bstep (se 1 (by rfl) ⟨2250890, by rfl⟩ : syracuseStep 3001187 = 4501781) B4501781
theorem B2000791 : Blo 1999435 2000791 := bstep (se 1 (by rfl) ⟨1500593, by rfl⟩ : syracuseStep 2000791 = 3001187) B3001187
theorem B7596773 : Blo 1999435 7596773 := bbase (se 4 (by rfl) ⟨712197, by rfl⟩ : syracuseStep 7596773 = 1424395) (by norm_num)
theorem B5064515 : Blo 1999435 5064515 := bstep (se 1 (by rfl) ⟨3798386, by rfl⟩ : syracuseStep 5064515 = 7596773) B7596773
theorem B3376343 : Blo 1999435 3376343 := bstep (se 1 (by rfl) ⟨2532257, by rfl⟩ : syracuseStep 3376343 = 5064515) B5064515
theorem B2250895 : Blo 1999435 2250895 := bstep (se 1 (by rfl) ⟨1688171, by rfl⟩ : syracuseStep 2250895 = 3376343) B3376343
theorem B3001193 : Blo 1999435 3001193 := bstep (se 2 (by rfl) ⟨1125447, by rfl⟩ : syracuseStep 3001193 = 2250895) B2250895
theorem B2000795 : Blo 1999435 2000795 := bstep (se 1 (by rfl) ⟨1500596, by rfl⟩ : syracuseStep 2000795 = 3001193) B3001193
theorem B4563221 : Blo 1999435 4563221 := bbase (se 6 (by rfl) ⟨106950, by rfl⟩ : syracuseStep 4563221 = 213901) (by norm_num)
theorem B12168589 : Blo 1999435 12168589 := bstep (se 3 (by rfl) ⟨2281610, by rfl⟩ : syracuseStep 12168589 = 4563221) B4563221
theorem B16224785 : Blo 1999435 16224785 := bstep (se 2 (by rfl) ⟨6084294, by rfl⟩ : syracuseStep 16224785 = 12168589) B12168589
theorem B10816523 : Blo 1999435 10816523 := bstep (se 1 (by rfl) ⟨8112392, by rfl⟩ : syracuseStep 10816523 = 16224785) B16224785
theorem B7211015 : Blo 1999435 7211015 := bstep (se 1 (by rfl) ⟨5408261, by rfl⟩ : syracuseStep 7211015 = 10816523) B10816523
theorem B4807343 : Blo 1999435 4807343 := bstep (se 1 (by rfl) ⟨3605507, by rfl⟩ : syracuseStep 4807343 = 7211015) B7211015
theorem B3204895 : Blo 1999435 3204895 := bstep (se 1 (by rfl) ⟨2403671, by rfl⟩ : syracuseStep 3204895 = 4807343) B4807343
theorem B4273193 : Blo 1999435 4273193 := bstep (se 2 (by rfl) ⟨1602447, by rfl⟩ : syracuseStep 4273193 = 3204895) B3204895
theorem B11395181 : Blo 1999435 11395181 := bstep (se 3 (by rfl) ⟨2136596, by rfl⟩ : syracuseStep 11395181 = 4273193) B4273193
theorem B7596787 : Blo 1999435 7596787 := bstep (se 1 (by rfl) ⟨5697590, by rfl⟩ : syracuseStep 7596787 = 11395181) B11395181
theorem B10129049 : Blo 1999435 10129049 := bstep (se 2 (by rfl) ⟨3798393, by rfl⟩ : syracuseStep 10129049 = 7596787) B7596787
theorem B6752699 : Blo 1999435 6752699 := bstep (se 1 (by rfl) ⟨5064524, by rfl⟩ : syracuseStep 6752699 = 10129049) B10129049
theorem B4501799 : Blo 1999435 4501799 := bstep (se 1 (by rfl) ⟨3376349, by rfl⟩ : syracuseStep 4501799 = 6752699) B6752699
theorem B3001199 : Blo 1999435 3001199 := bstep (se 1 (by rfl) ⟨2250899, by rfl⟩ : syracuseStep 3001199 = 4501799) B4501799
theorem B2000799 : Blo 1999435 2000799 := bstep (se 1 (by rfl) ⟨1500599, by rfl⟩ : syracuseStep 2000799 = 3001199) B3001199
theorem B3001205 : Blo 1999435 3001205 := bbase (se 5 (by rfl) ⟨140681, by rfl⟩ : syracuseStep 3001205 = 281363) (by norm_num)
theorem B2000803 : Blo 1999435 2000803 := bstep (se 1 (by rfl) ⟨1500602, by rfl⟩ : syracuseStep 2000803 = 3001205) B3001205
theorem B7211045 : Blo 1999435 7211045 := bbase (se 4 (by rfl) ⟨676035, by rfl⟩ : syracuseStep 7211045 = 1352071) (by norm_num)
theorem B4807363 : Blo 1999435 4807363 := bstep (se 1 (by rfl) ⟨3605522, by rfl⟩ : syracuseStep 4807363 = 7211045) B7211045
theorem B6409817 : Blo 1999435 6409817 := bstep (se 2 (by rfl) ⟨2403681, by rfl⟩ : syracuseStep 6409817 = 4807363) B4807363
theorem B4273211 : Blo 1999435 4273211 := bstep (se 1 (by rfl) ⟨3204908, by rfl⟩ : syracuseStep 4273211 = 6409817) B6409817
theorem B2848807 : Blo 1999435 2848807 := bstep (se 1 (by rfl) ⟨2136605, by rfl⟩ : syracuseStep 2848807 = 4273211) B4273211
theorem B3798409 : Blo 1999435 3798409 := bstep (se 2 (by rfl) ⟨1424403, by rfl⟩ : syracuseStep 3798409 = 2848807) B2848807
theorem B5064545 : Blo 1999435 5064545 := bstep (se 2 (by rfl) ⟨1899204, by rfl⟩ : syracuseStep 5064545 = 3798409) B3798409
theorem B3376363 : Blo 1999435 3376363 := bstep (se 1 (by rfl) ⟨2532272, by rfl⟩ : syracuseStep 3376363 = 5064545) B5064545
theorem B4501817 : Blo 1999435 4501817 := bstep (se 2 (by rfl) ⟨1688181, by rfl⟩ : syracuseStep 4501817 = 3376363) B3376363
theorem B3001211 : Blo 1999435 3001211 := bstep (se 1 (by rfl) ⟨2250908, by rfl⟩ : syracuseStep 3001211 = 4501817) B4501817
theorem B2000807 : Blo 1999435 2000807 := bstep (se 1 (by rfl) ⟨1500605, by rfl⟩ : syracuseStep 2000807 = 3001211) B3001211
theorem B2250913 : Blo 1999435 2250913 := bbase (se 2 (by rfl) ⟨844092, by rfl⟩ : syracuseStep 2250913 = 1688185) (by norm_num)
theorem B3001217 : Blo 1999435 3001217 := bstep (se 2 (by rfl) ⟨1125456, by rfl⟩ : syracuseStep 3001217 = 2250913) B2250913
theorem B2000811 : Blo 1999435 2000811 := bstep (se 1 (by rfl) ⟨1500608, by rfl⟩ : syracuseStep 2000811 = 3001217) B3001217
theorem B5064565 : Blo 1999435 5064565 := bbase (se 5 (by rfl) ⟨237401, by rfl⟩ : syracuseStep 5064565 = 474803) (by norm_num)
theorem B6752753 : Blo 1999435 6752753 := bstep (se 2 (by rfl) ⟨2532282, by rfl⟩ : syracuseStep 6752753 = 5064565) B5064565
theorem B4501835 : Blo 1999435 4501835 := bstep (se 1 (by rfl) ⟨3376376, by rfl⟩ : syracuseStep 4501835 = 6752753) B6752753
theorem B3001223 : Blo 1999435 3001223 := bstep (se 1 (by rfl) ⟨2250917, by rfl⟩ : syracuseStep 3001223 = 4501835) B4501835
theorem B2000815 : Blo 1999435 2000815 := bstep (se 1 (by rfl) ⟨1500611, by rfl⟩ : syracuseStep 2000815 = 3001223) B3001223
theorem B3001229 : Blo 1999435 3001229 := bbase (se 3 (by rfl) ⟨562730, by rfl⟩ : syracuseStep 3001229 = 1125461) (by norm_num)
theorem B2000819 : Blo 1999435 2000819 := bstep (se 1 (by rfl) ⟨1500614, by rfl⟩ : syracuseStep 2000819 = 3001229) B3001229
theorem B4501853 : Blo 1999435 4501853 := bbase (se 3 (by rfl) ⟨844097, by rfl⟩ : syracuseStep 4501853 = 1688195) (by norm_num)
theorem B3001235 : Blo 1999435 3001235 := bstep (se 1 (by rfl) ⟨2250926, by rfl⟩ : syracuseStep 3001235 = 4501853) B4501853
theorem B2000823 : Blo 1999435 2000823 := bstep (se 1 (by rfl) ⟨1500617, by rfl⟩ : syracuseStep 2000823 = 3001235) B3001235
theorem B3376397 : Blo 1999435 3376397 := bbase (se 3 (by rfl) ⟨633074, by rfl⟩ : syracuseStep 3376397 = 1266149) (by norm_num)
theorem B2250931 : Blo 1999435 2250931 := bstep (se 1 (by rfl) ⟨1688198, by rfl⟩ : syracuseStep 2250931 = 3376397) B3376397
theorem B3001241 : Blo 1999435 3001241 := bstep (se 2 (by rfl) ⟨1125465, by rfl⟩ : syracuseStep 3001241 = 2250931) B2250931
theorem B2000827 : Blo 1999435 2000827 := bstep (se 1 (by rfl) ⟨1500620, by rfl⟩ : syracuseStep 2000827 = 3001241) B3001241
theorem B17093045 : Blo 1999435 17093045 := bbase (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) (by norm_num)
theorem B11395363 : Blo 1999435 11395363 := bstep (se 1 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 11395363 = 17093045) B17093045
theorem B15193817 : Blo 1999435 15193817 := bstep (se 2 (by rfl) ⟨5697681, by rfl⟩ : syracuseStep 15193817 = 11395363) B11395363
theorem B10129211 : Blo 1999435 10129211 := bstep (se 1 (by rfl) ⟨7596908, by rfl⟩ : syracuseStep 10129211 = 15193817) B15193817
theorem B6752807 : Blo 1999435 6752807 := bstep (se 1 (by rfl) ⟨5064605, by rfl⟩ : syracuseStep 6752807 = 10129211) B10129211
theorem B4501871 : Blo 1999435 4501871 := bstep (se 1 (by rfl) ⟨3376403, by rfl⟩ : syracuseStep 4501871 = 6752807) B6752807
theorem B3001247 : Blo 1999435 3001247 := bstep (se 1 (by rfl) ⟨2250935, by rfl⟩ : syracuseStep 3001247 = 4501871) B4501871
theorem B2000831 : Blo 1999435 2000831 := bstep (se 1 (by rfl) ⟨1500623, by rfl⟩ : syracuseStep 2000831 = 3001247) B3001247
theorem B3001253 : Blo 1999435 3001253 := bbase (se 4 (by rfl) ⟨281367, by rfl⟩ : syracuseStep 3001253 = 562735) (by norm_num)
theorem B2000835 : Blo 1999435 2000835 := bstep (se 1 (by rfl) ⟨1500626, by rfl⟩ : syracuseStep 2000835 = 3001253) B3001253
theorem B2532313 : Blo 1999435 2532313 := bbase (se 2 (by rfl) ⟨949617, by rfl⟩ : syracuseStep 2532313 = 1899235) (by norm_num)
theorem B3376417 : Blo 1999435 3376417 := bstep (se 2 (by rfl) ⟨1266156, by rfl⟩ : syracuseStep 3376417 = 2532313) B2532313
theorem B4501889 : Blo 1999435 4501889 := bstep (se 2 (by rfl) ⟨1688208, by rfl⟩ : syracuseStep 4501889 = 3376417) B3376417
theorem B3001259 : Blo 1999435 3001259 := bstep (se 1 (by rfl) ⟨2250944, by rfl⟩ : syracuseStep 3001259 = 4501889) B4501889
theorem B2000839 : Blo 1999435 2000839 := bstep (se 1 (by rfl) ⟨1500629, by rfl⟩ : syracuseStep 2000839 = 3001259) B3001259
theorem B2250949 : Blo 1999435 2250949 := bbase (se 4 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 2250949 = 422053) (by norm_num)
theorem B3001265 : Blo 1999435 3001265 := bstep (se 2 (by rfl) ⟨1125474, by rfl⟩ : syracuseStep 3001265 = 2250949) B2250949
theorem B2000843 : Blo 1999435 2000843 := bstep (se 1 (by rfl) ⟨1500632, by rfl⟩ : syracuseStep 2000843 = 3001265) B3001265
theorem B3798485 : Blo 1999435 3798485 := bbase (se 7 (by rfl) ⟨44513, by rfl⟩ : syracuseStep 3798485 = 89027) (by norm_num)
theorem B2532323 : Blo 1999435 2532323 := bstep (se 1 (by rfl) ⟨1899242, by rfl⟩ : syracuseStep 2532323 = 3798485) B3798485
theorem B6752861 : Blo 1999435 6752861 := bstep (se 3 (by rfl) ⟨1266161, by rfl⟩ : syracuseStep 6752861 = 2532323) B2532323
theorem B4501907 : Blo 1999435 4501907 := bstep (se 1 (by rfl) ⟨3376430, by rfl⟩ : syracuseStep 4501907 = 6752861) B6752861
theorem B3001271 : Blo 1999435 3001271 := bstep (se 1 (by rfl) ⟨2250953, by rfl⟩ : syracuseStep 3001271 = 4501907) B4501907
theorem B2000847 : Blo 1999435 2000847 := bstep (se 1 (by rfl) ⟨1500635, by rfl⟩ : syracuseStep 2000847 = 3001271) B3001271
theorem B3001277 : Blo 1999435 3001277 := bbase (se 3 (by rfl) ⟨562739, by rfl⟩ : syracuseStep 3001277 = 1125479) (by norm_num)
theorem B2000851 : Blo 1999435 2000851 := bstep (se 1 (by rfl) ⟨1500638, by rfl⟩ : syracuseStep 2000851 = 3001277) B3001277
theorem B4501925 : Blo 1999435 4501925 := bbase (se 4 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 4501925 = 844111) (by norm_num)
theorem B3001283 : Blo 1999435 3001283 := bstep (se 1 (by rfl) ⟨2250962, by rfl⟩ : syracuseStep 3001283 = 4501925) B4501925
theorem B2000855 : Blo 1999435 2000855 := bstep (se 1 (by rfl) ⟨1500641, by rfl⟩ : syracuseStep 2000855 = 3001283) B3001283
theorem B5064677 : Blo 1999435 5064677 := bbase (se 4 (by rfl) ⟨474813, by rfl⟩ : syracuseStep 5064677 = 949627) (by norm_num)
theorem B3376451 : Blo 1999435 3376451 := bstep (se 1 (by rfl) ⟨2532338, by rfl⟩ : syracuseStep 3376451 = 5064677) B5064677
theorem B2250967 : Blo 1999435 2250967 := bstep (se 1 (by rfl) ⟨1688225, by rfl⟩ : syracuseStep 2250967 = 3376451) B3376451
theorem B3001289 : Blo 1999435 3001289 := bstep (se 2 (by rfl) ⟨1125483, by rfl⟩ : syracuseStep 3001289 = 2250967) B2250967
theorem B2000859 : Blo 1999435 2000859 := bstep (se 1 (by rfl) ⟨1500644, by rfl⟩ : syracuseStep 2000859 = 3001289) B3001289
theorem B2136665 : Blo 1999435 2136665 := bbase (se 2 (by rfl) ⟨801249, by rfl⟩ : syracuseStep 2136665 = 1602499) (by norm_num)
theorem B5697773 : Blo 1999435 5697773 := bstep (se 3 (by rfl) ⟨1068332, by rfl⟩ : syracuseStep 5697773 = 2136665) B2136665
theorem B3798515 : Blo 1999435 3798515 := bstep (se 1 (by rfl) ⟨2848886, by rfl⟩ : syracuseStep 3798515 = 5697773) B5697773
theorem B10129373 : Blo 1999435 10129373 := bstep (se 3 (by rfl) ⟨1899257, by rfl⟩ : syracuseStep 10129373 = 3798515) B3798515
theorem B6752915 : Blo 1999435 6752915 := bstep (se 1 (by rfl) ⟨5064686, by rfl⟩ : syracuseStep 6752915 = 10129373) B10129373
theorem B4501943 : Blo 1999435 4501943 := bstep (se 1 (by rfl) ⟨3376457, by rfl⟩ : syracuseStep 4501943 = 6752915) B6752915
theorem B3001295 : Blo 1999435 3001295 := bstep (se 1 (by rfl) ⟨2250971, by rfl⟩ : syracuseStep 3001295 = 4501943) B4501943
theorem B2000863 : Blo 1999435 2000863 := bstep (se 1 (by rfl) ⟨1500647, by rfl⟩ : syracuseStep 2000863 = 3001295) B3001295
theorem B3001301 : Blo 1999435 3001301 := bbase (se 7 (by rfl) ⟨35171, by rfl⟩ : syracuseStep 3001301 = 70343) (by norm_num)
theorem B2000867 : Blo 1999435 2000867 := bstep (se 1 (by rfl) ⟨1500650, by rfl⟩ : syracuseStep 2000867 = 3001301) B3001301
theorem B7597061 : Blo 1999435 7597061 := bbase (se 4 (by rfl) ⟨712224, by rfl⟩ : syracuseStep 7597061 = 1424449) (by norm_num)
theorem B5064707 : Blo 1999435 5064707 := bstep (se 1 (by rfl) ⟨3798530, by rfl⟩ : syracuseStep 5064707 = 7597061) B7597061
theorem B3376471 : Blo 1999435 3376471 := bstep (se 1 (by rfl) ⟨2532353, by rfl⟩ : syracuseStep 3376471 = 5064707) B5064707
theorem B4501961 : Blo 1999435 4501961 := bstep (se 2 (by rfl) ⟨1688235, by rfl⟩ : syracuseStep 4501961 = 3376471) B3376471
theorem B3001307 : Blo 1999435 3001307 := bstep (se 1 (by rfl) ⟨2250980, by rfl⟩ : syracuseStep 3001307 = 4501961) B4501961
theorem B2000871 : Blo 1999435 2000871 := bstep (se 1 (by rfl) ⟨1500653, by rfl⟩ : syracuseStep 2000871 = 3001307) B3001307
theorem B2250985 : Blo 1999435 2250985 := bbase (se 2 (by rfl) ⟨844119, by rfl⟩ : syracuseStep 2250985 = 1688239) (by norm_num)
theorem B3001313 : Blo 1999435 3001313 := bstep (se 2 (by rfl) ⟨1125492, by rfl⟩ : syracuseStep 3001313 = 2250985) B2250985
theorem B2000875 : Blo 1999435 2000875 := bstep (se 1 (by rfl) ⟨1500656, by rfl⟩ : syracuseStep 2000875 = 3001313) B3001313
theorem B11395637 : Blo 1999435 11395637 := bbase (se 5 (by rfl) ⟨534170, by rfl⟩ : syracuseStep 11395637 = 1068341) (by norm_num)
theorem B7597091 : Blo 1999435 7597091 := bstep (se 1 (by rfl) ⟨5697818, by rfl⟩ : syracuseStep 7597091 = 11395637) B11395637
theorem B5064727 : Blo 1999435 5064727 := bstep (se 1 (by rfl) ⟨3798545, by rfl⟩ : syracuseStep 5064727 = 7597091) B7597091
theorem B6752969 : Blo 1999435 6752969 := bstep (se 2 (by rfl) ⟨2532363, by rfl⟩ : syracuseStep 6752969 = 5064727) B5064727
theorem B4501979 : Blo 1999435 4501979 := bstep (se 1 (by rfl) ⟨3376484, by rfl⟩ : syracuseStep 4501979 = 6752969) B6752969
theorem B3001319 : Blo 1999435 3001319 := bstep (se 1 (by rfl) ⟨2250989, by rfl⟩ : syracuseStep 3001319 = 4501979) B4501979
theorem B2000879 : Blo 1999435 2000879 := bstep (se 1 (by rfl) ⟨1500659, by rfl⟩ : syracuseStep 2000879 = 3001319) B3001319
theorem B3001325 : Blo 1999435 3001325 := bbase (se 3 (by rfl) ⟨562748, by rfl⟩ : syracuseStep 3001325 = 1125497) (by norm_num)
theorem B2000883 : Blo 1999435 2000883 := bstep (se 1 (by rfl) ⟨1500662, by rfl⟩ : syracuseStep 2000883 = 3001325) B3001325
theorem B4501997 : Blo 1999435 4501997 := bbase (se 3 (by rfl) ⟨844124, by rfl⟩ : syracuseStep 4501997 = 1688249) (by norm_num)
theorem B3001331 : Blo 1999435 3001331 := bstep (se 1 (by rfl) ⟨2250998, by rfl⟩ : syracuseStep 3001331 = 4501997) B4501997
theorem B2000887 : Blo 1999435 2000887 := bstep (se 1 (by rfl) ⟨1500665, by rfl⟩ : syracuseStep 2000887 = 3001331) B3001331
theorem B2408809 : Blo 1999435 2408809 := bbase (se 2 (by rfl) ⟨903303, by rfl⟩ : syracuseStep 2408809 = 1806607) (by norm_num)
theorem B3211745 : Blo 1999435 3211745 := bstep (se 2 (by rfl) ⟨1204404, by rfl⟩ : syracuseStep 3211745 = 2408809) B2408809
theorem B8564653 : Blo 1999435 8564653 := bstep (se 3 (by rfl) ⟨1605872, by rfl⟩ : syracuseStep 8564653 = 3211745) B3211745
theorem B11419537 : Blo 1999435 11419537 := bstep (se 2 (by rfl) ⟨4282326, by rfl⟩ : syracuseStep 11419537 = 8564653) B8564653
theorem B15226049 : Blo 1999435 15226049 := bstep (se 2 (by rfl) ⟨5709768, by rfl⟩ : syracuseStep 15226049 = 11419537) B11419537
theorem B10150699 : Blo 1999435 10150699 := bstep (se 1 (by rfl) ⟨7613024, by rfl⟩ : syracuseStep 10150699 = 15226049) B15226049
theorem B13534265 : Blo 1999435 13534265 := bstep (se 2 (by rfl) ⟨5075349, by rfl⟩ : syracuseStep 13534265 = 10150699) B10150699
theorem B9022843 : Blo 1999435 9022843 := bstep (se 1 (by rfl) ⟨6767132, by rfl⟩ : syracuseStep 9022843 = 13534265) B13534265
theorem B12030457 : Blo 1999435 12030457 := bstep (se 2 (by rfl) ⟨4511421, by rfl⟩ : syracuseStep 12030457 = 9022843) B9022843
theorem B16040609 : Blo 1999435 16040609 := bstep (se 2 (by rfl) ⟨6015228, by rfl⟩ : syracuseStep 16040609 = 12030457) B12030457
theorem B10693739 : Blo 1999435 10693739 := bstep (se 1 (by rfl) ⟨8020304, by rfl⟩ : syracuseStep 10693739 = 16040609) B16040609
theorem B28516637 : Blo 1999435 28516637 := bstep (se 3 (by rfl) ⟨5346869, by rfl⟩ : syracuseStep 28516637 = 10693739) B10693739
theorem B76044365 : Blo 1999435 76044365 := bstep (se 3 (by rfl) ⟨14258318, by rfl⟩ : syracuseStep 76044365 = 28516637) B28516637
theorem B50696243 : Blo 1999435 50696243 := bstep (se 1 (by rfl) ⟨38022182, by rfl⟩ : syracuseStep 50696243 = 76044365) B76044365
theorem B33797495 : Blo 1999435 33797495 := bstep (se 1 (by rfl) ⟨25348121, by rfl⟩ : syracuseStep 33797495 = 50696243) B50696243
theorem B22531663 : Blo 1999435 22531663 := bstep (se 1 (by rfl) ⟨16898747, by rfl⟩ : syracuseStep 22531663 = 33797495) B33797495
theorem B30042217 : Blo 1999435 30042217 := bstep (se 2 (by rfl) ⟨11265831, by rfl⟩ : syracuseStep 30042217 = 22531663) B22531663
theorem B40056289 : Blo 1999435 40056289 := bstep (se 2 (by rfl) ⟨15021108, by rfl⟩ : syracuseStep 40056289 = 30042217) B30042217
theorem B213633541 : Blo 1999435 213633541 := bstep (se 4 (by rfl) ⟨20028144, by rfl⟩ : syracuseStep 213633541 = 40056289) B40056289
theorem B284844721 : Blo 1999435 284844721 := bstep (se 2 (by rfl) ⟨106816770, by rfl⟩ : syracuseStep 284844721 = 213633541) B213633541
theorem B379792961 : Blo 1999435 379792961 := bstep (se 2 (by rfl) ⟨142422360, by rfl⟩ : syracuseStep 379792961 = 284844721) B284844721
theorem B253195307 : Blo 1999435 253195307 := bstep (se 1 (by rfl) ⟨189896480, by rfl⟩ : syracuseStep 253195307 = 379792961) B379792961
theorem B168796871 : Blo 1999435 168796871 := bstep (se 1 (by rfl) ⟨126597653, by rfl⟩ : syracuseStep 168796871 = 253195307) B253195307
theorem B112531247 : Blo 1999435 112531247 := bstep (se 1 (by rfl) ⟨84398435, by rfl⟩ : syracuseStep 112531247 = 168796871) B168796871
theorem B75020831 : Blo 1999435 75020831 := bstep (se 1 (by rfl) ⟨56265623, by rfl⟩ : syracuseStep 75020831 = 112531247) B112531247
theorem B50013887 : Blo 1999435 50013887 := bstep (se 1 (by rfl) ⟨37510415, by rfl⟩ : syracuseStep 50013887 = 75020831) B75020831
theorem B533481461 : Blo 1999435 533481461 := bstep (se 5 (by rfl) ⟨25006943, by rfl⟩ : syracuseStep 533481461 = 50013887) B50013887
theorem B355654307 : Blo 1999435 355654307 := bstep (se 1 (by rfl) ⟨266740730, by rfl⟩ : syracuseStep 355654307 = 533481461) B533481461
theorem B237102871 : Blo 1999435 237102871 := bstep (se 1 (by rfl) ⟨177827153, by rfl⟩ : syracuseStep 237102871 = 355654307) B355654307
theorem B316137161 : Blo 1999435 316137161 := bstep (se 2 (by rfl) ⟨118551435, by rfl⟩ : syracuseStep 316137161 = 237102871) B237102871
theorem B210758107 : Blo 1999435 210758107 := bstep (se 1 (by rfl) ⟨158068580, by rfl⟩ : syracuseStep 210758107 = 316137161) B316137161
theorem B281010809 : Blo 1999435 281010809 := bstep (se 2 (by rfl) ⟨105379053, by rfl⟩ : syracuseStep 281010809 = 210758107) B210758107
theorem B187340539 : Blo 1999435 187340539 := bstep (se 1 (by rfl) ⟨140505404, by rfl⟩ : syracuseStep 187340539 = 281010809) B281010809
theorem B249787385 : Blo 1999435 249787385 := bstep (se 2 (by rfl) ⟨93670269, by rfl⟩ : syracuseStep 249787385 = 187340539) B187340539
theorem B166524923 : Blo 1999435 166524923 := bstep (se 1 (by rfl) ⟨124893692, by rfl⟩ : syracuseStep 166524923 = 249787385) B249787385
theorem B111016615 : Blo 1999435 111016615 := bstep (se 1 (by rfl) ⟨83262461, by rfl⟩ : syracuseStep 111016615 = 166524923) B166524923
theorem B148022153 : Blo 1999435 148022153 := bstep (se 2 (by rfl) ⟨55508307, by rfl⟩ : syracuseStep 148022153 = 111016615) B111016615
theorem B98681435 : Blo 1999435 98681435 := bstep (se 1 (by rfl) ⟨74011076, by rfl⟩ : syracuseStep 98681435 = 148022153) B148022153
theorem B65787623 : Blo 1999435 65787623 := bstep (se 1 (by rfl) ⟨49340717, by rfl⟩ : syracuseStep 65787623 = 98681435) B98681435
theorem B43858415 : Blo 1999435 43858415 := bstep (se 1 (by rfl) ⟨32893811, by rfl⟩ : syracuseStep 43858415 = 65787623) B65787623
theorem B29238943 : Blo 1999435 29238943 := bstep (se 1 (by rfl) ⟨21929207, by rfl⟩ : syracuseStep 29238943 = 43858415) B43858415
theorem B38985257 : Blo 1999435 38985257 := bstep (se 2 (by rfl) ⟨14619471, by rfl⟩ : syracuseStep 38985257 = 29238943) B29238943
theorem B103960685 : Blo 1999435 103960685 := bstep (se 3 (by rfl) ⟨19492628, by rfl⟩ : syracuseStep 103960685 = 38985257) B38985257
theorem B277228493 : Blo 1999435 277228493 := bstep (se 3 (by rfl) ⟨51980342, by rfl⟩ : syracuseStep 277228493 = 103960685) B103960685
theorem B184818995 : Blo 1999435 184818995 := bstep (se 1 (by rfl) ⟨138614246, by rfl⟩ : syracuseStep 184818995 = 277228493) B277228493
theorem B123212663 : Blo 1999435 123212663 := bstep (se 1 (by rfl) ⟨92409497, by rfl⟩ : syracuseStep 123212663 = 184818995) B184818995
theorem B82141775 : Blo 1999435 82141775 := bstep (se 1 (by rfl) ⟨61606331, by rfl⟩ : syracuseStep 82141775 = 123212663) B123212663
theorem B54761183 : Blo 1999435 54761183 := bstep (se 1 (by rfl) ⟨41070887, by rfl⟩ : syracuseStep 54761183 = 82141775) B82141775
theorem B36507455 : Blo 1999435 36507455 := bstep (se 1 (by rfl) ⟨27380591, by rfl⟩ : syracuseStep 36507455 = 54761183) B54761183
theorem B24338303 : Blo 1999435 24338303 := bstep (se 1 (by rfl) ⟨18253727, by rfl⟩ : syracuseStep 24338303 = 36507455) B36507455
theorem B16225535 : Blo 1999435 16225535 := bstep (se 1 (by rfl) ⟨12169151, by rfl⟩ : syracuseStep 16225535 = 24338303) B24338303
theorem B10817023 : Blo 1999435 10817023 := bstep (se 1 (by rfl) ⟨8112767, by rfl⟩ : syracuseStep 10817023 = 16225535) B16225535
theorem B14422697 : Blo 1999435 14422697 := bstep (se 2 (by rfl) ⟨5408511, by rfl⟩ : syracuseStep 14422697 = 10817023) B10817023
theorem B9615131 : Blo 1999435 9615131 := bstep (se 1 (by rfl) ⟨7211348, by rfl⟩ : syracuseStep 9615131 = 14422697) B14422697
theorem B6410087 : Blo 1999435 6410087 := bstep (se 1 (by rfl) ⟨4807565, by rfl⟩ : syracuseStep 6410087 = 9615131) B9615131
theorem B4273391 : Blo 1999435 4273391 := bstep (se 1 (by rfl) ⟨3205043, by rfl⟩ : syracuseStep 4273391 = 6410087) B6410087
theorem B2848927 : Blo 1999435 2848927 := bstep (se 1 (by rfl) ⟨2136695, by rfl⟩ : syracuseStep 2848927 = 4273391) B4273391
theorem B3798569 : Blo 1999435 3798569 := bstep (se 2 (by rfl) ⟨1424463, by rfl⟩ : syracuseStep 3798569 = 2848927) B2848927
theorem B2532379 : Blo 1999435 2532379 := bstep (se 1 (by rfl) ⟨1899284, by rfl⟩ : syracuseStep 2532379 = 3798569) B3798569
theorem B3376505 : Blo 1999435 3376505 := bstep (se 2 (by rfl) ⟨1266189, by rfl⟩ : syracuseStep 3376505 = 2532379) B2532379
theorem B2251003 : Blo 1999435 2251003 := bstep (se 1 (by rfl) ⟨1688252, by rfl⟩ : syracuseStep 2251003 = 3376505) B3376505
theorem B3001337 : Blo 1999435 3001337 := bstep (se 2 (by rfl) ⟨1125501, by rfl⟩ : syracuseStep 3001337 = 2251003) B2251003
theorem B2000891 : Blo 1999435 2000891 := bstep (se 1 (by rfl) ⟨1500668, by rfl⟩ : syracuseStep 2000891 = 3001337) B3001337
theorem B5133869 : Blo 1999435 5133869 := bbase (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) (by norm_num)
theorem B3422579 : Blo 1999435 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B9126877 : Blo 1999435 9126877 := bstep (se 3 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 9126877 = 3422579) B3422579
theorem B12169169 : Blo 1999435 12169169 := bstep (se 2 (by rfl) ⟨4563438, by rfl⟩ : syracuseStep 12169169 = 9126877) B9126877
theorem B8112779 : Blo 1999435 8112779 := bstep (se 1 (by rfl) ⟨6084584, by rfl⟩ : syracuseStep 8112779 = 12169169) B12169169
theorem B86536309 : Blo 1999435 86536309 := bstep (se 5 (by rfl) ⟨4056389, by rfl⟩ : syracuseStep 86536309 = 8112779) B8112779
theorem B115381745 : Blo 1999435 115381745 := bstep (se 2 (by rfl) ⟨43268154, by rfl⟩ : syracuseStep 115381745 = 86536309) B86536309
theorem B76921163 : Blo 1999435 76921163 := bstep (se 1 (by rfl) ⟨57690872, by rfl⟩ : syracuseStep 76921163 = 115381745) B115381745
theorem B51280775 : Blo 1999435 51280775 := bstep (se 1 (by rfl) ⟨38460581, by rfl⟩ : syracuseStep 51280775 = 76921163) B76921163
theorem B34187183 : Blo 1999435 34187183 := bstep (se 1 (by rfl) ⟨25640387, by rfl⟩ : syracuseStep 34187183 = 51280775) B51280775
theorem B22791455 : Blo 1999435 22791455 := bstep (se 1 (by rfl) ⟨17093591, by rfl⟩ : syracuseStep 22791455 = 34187183) B34187183
theorem B15194303 : Blo 1999435 15194303 := bstep (se 1 (by rfl) ⟨11395727, by rfl⟩ : syracuseStep 15194303 = 22791455) B22791455
theorem B10129535 : Blo 1999435 10129535 := bstep (se 1 (by rfl) ⟨7597151, by rfl⟩ : syracuseStep 10129535 = 15194303) B15194303
theorem B6753023 : Blo 1999435 6753023 := bstep (se 1 (by rfl) ⟨5064767, by rfl⟩ : syracuseStep 6753023 = 10129535) B10129535
theorem B4502015 : Blo 1999435 4502015 := bstep (se 1 (by rfl) ⟨3376511, by rfl⟩ : syracuseStep 4502015 = 6753023) B6753023
theorem B3001343 : Blo 1999435 3001343 := bstep (se 1 (by rfl) ⟨2251007, by rfl⟩ : syracuseStep 3001343 = 4502015) B4502015
theorem B2000895 : Blo 1999435 2000895 := bstep (se 1 (by rfl) ⟨1500671, by rfl⟩ : syracuseStep 2000895 = 3001343) B3001343
theorem B3001349 : Blo 1999435 3001349 := bbase (se 4 (by rfl) ⟨281376, by rfl⟩ : syracuseStep 3001349 = 562753) (by norm_num)
theorem B2000899 : Blo 1999435 2000899 := bstep (se 1 (by rfl) ⟨1500674, by rfl⟩ : syracuseStep 2000899 = 3001349) B3001349
theorem B3376525 : Blo 1999435 3376525 := bbase (se 3 (by rfl) ⟨633098, by rfl⟩ : syracuseStep 3376525 = 1266197) (by norm_num)
theorem B4502033 : Blo 1999435 4502033 := bstep (se 2 (by rfl) ⟨1688262, by rfl⟩ : syracuseStep 4502033 = 3376525) B3376525
theorem B3001355 : Blo 1999435 3001355 := bstep (se 1 (by rfl) ⟨2251016, by rfl⟩ : syracuseStep 3001355 = 4502033) B4502033
theorem B2000903 : Blo 1999435 2000903 := bstep (se 1 (by rfl) ⟨1500677, by rfl⟩ : syracuseStep 2000903 = 3001355) B3001355
theorem B2251021 : Blo 1999435 2251021 := bbase (se 3 (by rfl) ⟨422066, by rfl⟩ : syracuseStep 2251021 = 844133) (by norm_num)
theorem B3001361 : Blo 1999435 3001361 := bstep (se 2 (by rfl) ⟨1125510, by rfl⟩ : syracuseStep 3001361 = 2251021) B2251021
theorem B2000907 : Blo 1999435 2000907 := bstep (se 1 (by rfl) ⟨1500680, by rfl⟩ : syracuseStep 2000907 = 3001361) B3001361
theorem B6753077 : Blo 1999435 6753077 := bbase (se 5 (by rfl) ⟨316550, by rfl⟩ : syracuseStep 6753077 = 633101) (by norm_num)
theorem B4502051 : Blo 1999435 4502051 := bstep (se 1 (by rfl) ⟨3376538, by rfl⟩ : syracuseStep 4502051 = 6753077) B6753077
theorem B3001367 : Blo 1999435 3001367 := bstep (se 1 (by rfl) ⟨2251025, by rfl⟩ : syracuseStep 3001367 = 4502051) B4502051
theorem B2000911 : Blo 1999435 2000911 := bstep (se 1 (by rfl) ⟨1500683, by rfl⟩ : syracuseStep 2000911 = 3001367) B3001367
theorem B3001373 : Blo 1999435 3001373 := bbase (se 3 (by rfl) ⟨562757, by rfl⟩ : syracuseStep 3001373 = 1125515) (by norm_num)
theorem B2000915 : Blo 1999435 2000915 := bstep (se 1 (by rfl) ⟨1500686, by rfl⟩ : syracuseStep 2000915 = 3001373) B3001373
theorem B4502069 : Blo 1999435 4502069 := bbase (se 5 (by rfl) ⟨211034, by rfl⟩ : syracuseStep 4502069 = 422069) (by norm_num)
theorem B3001379 : Blo 1999435 3001379 := bstep (se 1 (by rfl) ⟨2251034, by rfl⟩ : syracuseStep 3001379 = 4502069) B4502069
theorem B2000919 : Blo 1999435 2000919 := bstep (se 1 (by rfl) ⟨1500689, by rfl⟩ : syracuseStep 2000919 = 3001379) B3001379
theorem B8546917 : Blo 1999435 8546917 := bbase (se 4 (by rfl) ⟨801273, by rfl⟩ : syracuseStep 8546917 = 1602547) (by norm_num)
theorem B11395889 : Blo 1999435 11395889 := bstep (se 2 (by rfl) ⟨4273458, by rfl⟩ : syracuseStep 11395889 = 8546917) B8546917
theorem B7597259 : Blo 1999435 7597259 := bstep (se 1 (by rfl) ⟨5697944, by rfl⟩ : syracuseStep 7597259 = 11395889) B11395889
theorem B5064839 : Blo 1999435 5064839 := bstep (se 1 (by rfl) ⟨3798629, by rfl⟩ : syracuseStep 5064839 = 7597259) B7597259
theorem B3376559 : Blo 1999435 3376559 := bstep (se 1 (by rfl) ⟨2532419, by rfl⟩ : syracuseStep 3376559 = 5064839) B5064839
theorem B2251039 : Blo 1999435 2251039 := bstep (se 1 (by rfl) ⟨1688279, by rfl⟩ : syracuseStep 2251039 = 3376559) B3376559
theorem B3001385 : Blo 1999435 3001385 := bstep (se 2 (by rfl) ⟨1125519, by rfl⟩ : syracuseStep 3001385 = 2251039) B2251039
theorem B2000923 : Blo 1999435 2000923 := bstep (se 1 (by rfl) ⟨1500692, by rfl⟩ : syracuseStep 2000923 = 3001385) B3001385
theorem B8546933 : Blo 1999435 8546933 := bbase (se 5 (by rfl) ⟨400637, by rfl⟩ : syracuseStep 8546933 = 801275) (by norm_num)
theorem B5697955 : Blo 1999435 5697955 := bstep (se 1 (by rfl) ⟨4273466, by rfl⟩ : syracuseStep 5697955 = 8546933) B8546933
theorem B7597273 : Blo 1999435 7597273 := bstep (se 2 (by rfl) ⟨2848977, by rfl⟩ : syracuseStep 7597273 = 5697955) B5697955
theorem B10129697 : Blo 1999435 10129697 := bstep (se 2 (by rfl) ⟨3798636, by rfl⟩ : syracuseStep 10129697 = 7597273) B7597273
theorem B6753131 : Blo 1999435 6753131 := bstep (se 1 (by rfl) ⟨5064848, by rfl⟩ : syracuseStep 6753131 = 10129697) B10129697
theorem B4502087 : Blo 1999435 4502087 := bstep (se 1 (by rfl) ⟨3376565, by rfl⟩ : syracuseStep 4502087 = 6753131) B6753131
theorem B3001391 : Blo 1999435 3001391 := bstep (se 1 (by rfl) ⟨2251043, by rfl⟩ : syracuseStep 3001391 = 4502087) B4502087
theorem B2000927 : Blo 1999435 2000927 := bstep (se 1 (by rfl) ⟨1500695, by rfl⟩ : syracuseStep 2000927 = 3001391) B3001391
theorem B3001397 : Blo 1999435 3001397 := bbase (se 5 (by rfl) ⟨140690, by rfl⟩ : syracuseStep 3001397 = 281381) (by norm_num)
theorem B2000931 : Blo 1999435 2000931 := bstep (se 1 (by rfl) ⟨1500698, by rfl⟩ : syracuseStep 2000931 = 3001397) B3001397
theorem B5064869 : Blo 1999435 5064869 := bbase (se 4 (by rfl) ⟨474831, by rfl⟩ : syracuseStep 5064869 = 949663) (by norm_num)
theorem B3376579 : Blo 1999435 3376579 := bstep (se 1 (by rfl) ⟨2532434, by rfl⟩ : syracuseStep 3376579 = 5064869) B5064869
theorem B4502105 : Blo 1999435 4502105 := bstep (se 2 (by rfl) ⟨1688289, by rfl⟩ : syracuseStep 4502105 = 3376579) B3376579
theorem B3001403 : Blo 1999435 3001403 := bstep (se 1 (by rfl) ⟨2251052, by rfl⟩ : syracuseStep 3001403 = 4502105) B4502105
theorem B2000935 : Blo 1999435 2000935 := bstep (se 1 (by rfl) ⟨1500701, by rfl⟩ : syracuseStep 2000935 = 3001403) B3001403
theorem B2251057 : Blo 1999435 2251057 := bbase (se 2 (by rfl) ⟨844146, by rfl⟩ : syracuseStep 2251057 = 1688293) (by norm_num)
theorem B3001409 : Blo 1999435 3001409 := bstep (se 2 (by rfl) ⟨1125528, by rfl⟩ : syracuseStep 3001409 = 2251057) B2251057
theorem B2000939 : Blo 1999435 2000939 := bstep (se 1 (by rfl) ⟨1500704, by rfl⟩ : syracuseStep 2000939 = 3001409) B3001409
theorem B4273501 : Blo 1999435 4273501 := bbase (se 3 (by rfl) ⟨801281, by rfl⟩ : syracuseStep 4273501 = 1602563) (by norm_num)
theorem B5698001 : Blo 1999435 5698001 := bstep (se 2 (by rfl) ⟨2136750, by rfl⟩ : syracuseStep 5698001 = 4273501) B4273501
theorem B3798667 : Blo 1999435 3798667 := bstep (se 1 (by rfl) ⟨2849000, by rfl⟩ : syracuseStep 3798667 = 5698001) B5698001
theorem B5064889 : Blo 1999435 5064889 := bstep (se 2 (by rfl) ⟨1899333, by rfl⟩ : syracuseStep 5064889 = 3798667) B3798667
theorem B6753185 : Blo 1999435 6753185 := bstep (se 2 (by rfl) ⟨2532444, by rfl⟩ : syracuseStep 6753185 = 5064889) B5064889
theorem B4502123 : Blo 1999435 4502123 := bstep (se 1 (by rfl) ⟨3376592, by rfl⟩ : syracuseStep 4502123 = 6753185) B6753185
theorem B3001415 : Blo 1999435 3001415 := bstep (se 1 (by rfl) ⟨2251061, by rfl⟩ : syracuseStep 3001415 = 4502123) B4502123
theorem B2000943 : Blo 1999435 2000943 := bstep (se 1 (by rfl) ⟨1500707, by rfl⟩ : syracuseStep 2000943 = 3001415) B3001415
theorem B3001421 : Blo 1999435 3001421 := bbase (se 3 (by rfl) ⟨562766, by rfl⟩ : syracuseStep 3001421 = 1125533) (by norm_num)
theorem B2000947 : Blo 1999435 2000947 := bstep (se 1 (by rfl) ⟨1500710, by rfl⟩ : syracuseStep 2000947 = 3001421) B3001421
theorem B4502141 : Blo 1999435 4502141 := bbase (se 3 (by rfl) ⟨844151, by rfl⟩ : syracuseStep 4502141 = 1688303) (by norm_num)
theorem B3001427 : Blo 1999435 3001427 := bstep (se 1 (by rfl) ⟨2251070, by rfl⟩ : syracuseStep 3001427 = 4502141) B4502141
theorem B2000951 : Blo 1999435 2000951 := bstep (se 1 (by rfl) ⟨1500713, by rfl⟩ : syracuseStep 2000951 = 3001427) B3001427
theorem B3376613 : Blo 1999435 3376613 := bbase (se 4 (by rfl) ⟨316557, by rfl⟩ : syracuseStep 3376613 = 633115) (by norm_num)
theorem B2251075 : Blo 1999435 2251075 := bstep (se 1 (by rfl) ⟨1688306, by rfl⟩ : syracuseStep 2251075 = 3376613) B3376613
theorem B3001433 : Blo 1999435 3001433 := bstep (se 2 (by rfl) ⟨1125537, by rfl⟩ : syracuseStep 3001433 = 2251075) B2251075
theorem B2000955 : Blo 1999435 2000955 := bstep (se 1 (by rfl) ⟨1500716, by rfl⟩ : syracuseStep 2000955 = 3001433) B3001433
theorem B2567017 : Blo 1999435 2567017 := bbase (se 2 (by rfl) ⟨962631, by rfl⟩ : syracuseStep 2567017 = 1925263) (by norm_num)
theorem B13690757 : Blo 1999435 13690757 := bstep (se 4 (by rfl) ⟨1283508, by rfl⟩ : syracuseStep 13690757 = 2567017) B2567017
theorem B9127171 : Blo 1999435 9127171 := bstep (se 1 (by rfl) ⟨6845378, by rfl⟩ : syracuseStep 9127171 = 13690757) B13690757
theorem B48678245 : Blo 1999435 48678245 := bstep (se 4 (by rfl) ⟨4563585, by rfl⟩ : syracuseStep 48678245 = 9127171) B9127171
theorem B32452163 : Blo 1999435 32452163 := bstep (se 1 (by rfl) ⟨24339122, by rfl⟩ : syracuseStep 32452163 = 48678245) B48678245
theorem B21634775 : Blo 1999435 21634775 := bstep (se 1 (by rfl) ⟨16226081, by rfl⟩ : syracuseStep 21634775 = 32452163) B32452163
theorem B14423183 : Blo 1999435 14423183 := bstep (se 1 (by rfl) ⟨10817387, by rfl⟩ : syracuseStep 14423183 = 21634775) B21634775
theorem B9615455 : Blo 1999435 9615455 := bstep (se 1 (by rfl) ⟨7211591, by rfl⟩ : syracuseStep 9615455 = 14423183) B14423183
theorem B6410303 : Blo 1999435 6410303 := bstep (se 1 (by rfl) ⟨4807727, by rfl⟩ : syracuseStep 6410303 = 9615455) B9615455
theorem B4273535 : Blo 1999435 4273535 := bstep (se 1 (by rfl) ⟨3205151, by rfl⟩ : syracuseStep 4273535 = 6410303) B6410303
theorem B2849023 : Blo 1999435 2849023 := bstep (se 1 (by rfl) ⟨2136767, by rfl⟩ : syracuseStep 2849023 = 4273535) B4273535
theorem B15194789 : Blo 1999435 15194789 := bstep (se 4 (by rfl) ⟨1424511, by rfl⟩ : syracuseStep 15194789 = 2849023) B2849023
theorem B10129859 : Blo 1999435 10129859 := bstep (se 1 (by rfl) ⟨7597394, by rfl⟩ : syracuseStep 10129859 = 15194789) B15194789
theorem B6753239 : Blo 1999435 6753239 := bstep (se 1 (by rfl) ⟨5064929, by rfl⟩ : syracuseStep 6753239 = 10129859) B10129859
theorem B4502159 : Blo 1999435 4502159 := bstep (se 1 (by rfl) ⟨3376619, by rfl⟩ : syracuseStep 4502159 = 6753239) B6753239
theorem B3001439 : Blo 1999435 3001439 := bstep (se 1 (by rfl) ⟨2251079, by rfl⟩ : syracuseStep 3001439 = 4502159) B4502159
theorem B2000959 : Blo 1999435 2000959 := bstep (se 1 (by rfl) ⟨1500719, by rfl⟩ : syracuseStep 2000959 = 3001439) B3001439
theorem B3001445 : Blo 1999435 3001445 := bbase (se 4 (by rfl) ⟨281385, by rfl⟩ : syracuseStep 3001445 = 562771) (by norm_num)
theorem B2000963 : Blo 1999435 2000963 := bstep (se 1 (by rfl) ⟨1500722, by rfl⟩ : syracuseStep 2000963 = 3001445) B3001445
theorem B3205165 : Blo 1999435 3205165 := bbase (se 3 (by rfl) ⟨600968, by rfl⟩ : syracuseStep 3205165 = 1201937) (by norm_num)
theorem B4273553 : Blo 1999435 4273553 := bstep (se 2 (by rfl) ⟨1602582, by rfl⟩ : syracuseStep 4273553 = 3205165) B3205165
theorem B2849035 : Blo 1999435 2849035 := bstep (se 1 (by rfl) ⟨2136776, by rfl⟩ : syracuseStep 2849035 = 4273553) B4273553
theorem B3798713 : Blo 1999435 3798713 := bstep (se 2 (by rfl) ⟨1424517, by rfl⟩ : syracuseStep 3798713 = 2849035) B2849035
theorem B2532475 : Blo 1999435 2532475 := bstep (se 1 (by rfl) ⟨1899356, by rfl⟩ : syracuseStep 2532475 = 3798713) B3798713
theorem B3376633 : Blo 1999435 3376633 := bstep (se 2 (by rfl) ⟨1266237, by rfl⟩ : syracuseStep 3376633 = 2532475) B2532475
theorem B4502177 : Blo 1999435 4502177 := bstep (se 2 (by rfl) ⟨1688316, by rfl⟩ : syracuseStep 4502177 = 3376633) B3376633
theorem B3001451 : Blo 1999435 3001451 := bstep (se 1 (by rfl) ⟨2251088, by rfl⟩ : syracuseStep 3001451 = 4502177) B4502177
theorem B2000967 : Blo 1999435 2000967 := bstep (se 1 (by rfl) ⟨1500725, by rfl⟩ : syracuseStep 2000967 = 3001451) B3001451
theorem B2251093 : Blo 1999435 2251093 := bbase (se 10 (by rfl) ⟨3297, by rfl⟩ : syracuseStep 2251093 = 6595) (by norm_num)
theorem B3001457 : Blo 1999435 3001457 := bstep (se 2 (by rfl) ⟨1125546, by rfl⟩ : syracuseStep 3001457 = 2251093) B2251093
theorem B2000971 : Blo 1999435 2000971 := bstep (se 1 (by rfl) ⟨1500728, by rfl⟩ : syracuseStep 2000971 = 3001457) B3001457
theorem B2532485 : Blo 1999435 2532485 := bbase (se 4 (by rfl) ⟨237420, by rfl⟩ : syracuseStep 2532485 = 474841) (by norm_num)
theorem B6753293 : Blo 1999435 6753293 := bstep (se 3 (by rfl) ⟨1266242, by rfl⟩ : syracuseStep 6753293 = 2532485) B2532485
theorem B4502195 : Blo 1999435 4502195 := bstep (se 1 (by rfl) ⟨3376646, by rfl⟩ : syracuseStep 4502195 = 6753293) B6753293
theorem B3001463 : Blo 1999435 3001463 := bstep (se 1 (by rfl) ⟨2251097, by rfl⟩ : syracuseStep 3001463 = 4502195) B4502195
theorem B2000975 : Blo 1999435 2000975 := bstep (se 1 (by rfl) ⟨1500731, by rfl⟩ : syracuseStep 2000975 = 3001463) B3001463
theorem B3001469 : Blo 1999435 3001469 := bbase (se 3 (by rfl) ⟨562775, by rfl⟩ : syracuseStep 3001469 = 1125551) (by norm_num)
theorem B2000979 : Blo 1999435 2000979 := bstep (se 1 (by rfl) ⟨1500734, by rfl⟩ : syracuseStep 2000979 = 3001469) B3001469
theorem B4502213 : Blo 1999435 4502213 := bbase (se 4 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 4502213 = 844165) (by norm_num)
theorem B3001475 : Blo 1999435 3001475 := bstep (se 1 (by rfl) ⟨2251106, by rfl⟩ : syracuseStep 3001475 = 4502213) B4502213
theorem B2000983 : Blo 1999435 2000983 := bstep (se 1 (by rfl) ⟨1500737, by rfl⟩ : syracuseStep 2000983 = 3001475) B3001475
theorem B2028289 : Blo 1999435 2028289 := bbase (se 2 (by rfl) ⟨760608, by rfl⟩ : syracuseStep 2028289 = 1521217) (by norm_num)
theorem B2704385 : Blo 1999435 2704385 := bstep (se 2 (by rfl) ⟨1014144, by rfl⟩ : syracuseStep 2704385 = 2028289) B2028289
theorem B7211693 : Blo 1999435 7211693 := bstep (se 3 (by rfl) ⟨1352192, by rfl⟩ : syracuseStep 7211693 = 2704385) B2704385
theorem B19231181 : Blo 1999435 19231181 := bstep (se 3 (by rfl) ⟨3605846, by rfl⟩ : syracuseStep 19231181 = 7211693) B7211693
theorem B12820787 : Blo 1999435 12820787 := bstep (se 1 (by rfl) ⟨9615590, by rfl⟩ : syracuseStep 12820787 = 19231181) B19231181
theorem B8547191 : Blo 1999435 8547191 := bstep (se 1 (by rfl) ⟨6410393, by rfl⟩ : syracuseStep 8547191 = 12820787) B12820787
theorem B5698127 : Blo 1999435 5698127 := bstep (se 1 (by rfl) ⟨4273595, by rfl⟩ : syracuseStep 5698127 = 8547191) B8547191
theorem B3798751 : Blo 1999435 3798751 := bstep (se 1 (by rfl) ⟨2849063, by rfl⟩ : syracuseStep 3798751 = 5698127) B5698127
theorem B5065001 : Blo 1999435 5065001 := bstep (se 2 (by rfl) ⟨1899375, by rfl⟩ : syracuseStep 5065001 = 3798751) B3798751
theorem B3376667 : Blo 1999435 3376667 := bstep (se 1 (by rfl) ⟨2532500, by rfl⟩ : syracuseStep 3376667 = 5065001) B5065001
theorem B2251111 : Blo 1999435 2251111 := bstep (se 1 (by rfl) ⟨1688333, by rfl⟩ : syracuseStep 2251111 = 3376667) B3376667
theorem B3001481 : Blo 1999435 3001481 := bstep (se 2 (by rfl) ⟨1125555, by rfl⟩ : syracuseStep 3001481 = 2251111) B2251111
theorem B2000987 : Blo 1999435 2000987 := bstep (se 1 (by rfl) ⟨1500740, by rfl⟩ : syracuseStep 2000987 = 3001481) B3001481
theorem B10130021 : Blo 1999435 10130021 := bbase (se 4 (by rfl) ⟨949689, by rfl⟩ : syracuseStep 10130021 = 1899379) (by norm_num)
theorem B6753347 : Blo 1999435 6753347 := bstep (se 1 (by rfl) ⟨5065010, by rfl⟩ : syracuseStep 6753347 = 10130021) B10130021
theorem B4502231 : Blo 1999435 4502231 := bstep (se 1 (by rfl) ⟨3376673, by rfl⟩ : syracuseStep 4502231 = 6753347) B6753347
theorem B3001487 : Blo 1999435 3001487 := bstep (se 1 (by rfl) ⟨2251115, by rfl⟩ : syracuseStep 3001487 = 4502231) B4502231
theorem B2000991 : Blo 1999435 2000991 := bstep (se 1 (by rfl) ⟨1500743, by rfl⟩ : syracuseStep 2000991 = 3001487) B3001487
theorem B3001493 : Blo 1999435 3001493 := bbase (se 6 (by rfl) ⟨70347, by rfl⟩ : syracuseStep 3001493 = 140695) (by norm_num)
theorem B2000995 : Blo 1999435 2000995 := bstep (se 1 (by rfl) ⟨1500746, by rfl⟩ : syracuseStep 2000995 = 3001493) B3001493
theorem B7701205 : Blo 1999435 7701205 := bbase (se 7 (by rfl) ⟨90248, by rfl⟩ : syracuseStep 7701205 = 180497) (by norm_num)
theorem B10268273 : Blo 1999435 10268273 := bstep (se 2 (by rfl) ⟨3850602, by rfl⟩ : syracuseStep 10268273 = 7701205) B7701205
theorem B6845515 : Blo 1999435 6845515 := bstep (se 1 (by rfl) ⟨5134136, by rfl⟩ : syracuseStep 6845515 = 10268273) B10268273
theorem B36509413 : Blo 1999435 36509413 := bstep (se 4 (by rfl) ⟨3422757, by rfl⟩ : syracuseStep 36509413 = 6845515) B6845515
theorem B48679217 : Blo 1999435 48679217 := bstep (se 2 (by rfl) ⟨18254706, by rfl⟩ : syracuseStep 48679217 = 36509413) B36509413
theorem B32452811 : Blo 1999435 32452811 := bstep (se 1 (by rfl) ⟨24339608, by rfl⟩ : syracuseStep 32452811 = 48679217) B48679217
theorem B21635207 : Blo 1999435 21635207 := bstep (se 1 (by rfl) ⟨16226405, by rfl⟩ : syracuseStep 21635207 = 32452811) B32452811
theorem B14423471 : Blo 1999435 14423471 := bstep (se 1 (by rfl) ⟨10817603, by rfl⟩ : syracuseStep 14423471 = 21635207) B21635207
theorem B9615647 : Blo 1999435 9615647 := bstep (se 1 (by rfl) ⟨7211735, by rfl⟩ : syracuseStep 9615647 = 14423471) B14423471
theorem B6410431 : Blo 1999435 6410431 := bstep (se 1 (by rfl) ⟨4807823, by rfl⟩ : syracuseStep 6410431 = 9615647) B9615647
theorem B8547241 : Blo 1999435 8547241 := bstep (se 2 (by rfl) ⟨3205215, by rfl⟩ : syracuseStep 8547241 = 6410431) B6410431
theorem B11396321 : Blo 1999435 11396321 := bstep (se 2 (by rfl) ⟨4273620, by rfl⟩ : syracuseStep 11396321 = 8547241) B8547241
theorem B7597547 : Blo 1999435 7597547 := bstep (se 1 (by rfl) ⟨5698160, by rfl⟩ : syracuseStep 7597547 = 11396321) B11396321
theorem B5065031 : Blo 1999435 5065031 := bstep (se 1 (by rfl) ⟨3798773, by rfl⟩ : syracuseStep 5065031 = 7597547) B7597547
theorem B3376687 : Blo 1999435 3376687 := bstep (se 1 (by rfl) ⟨2532515, by rfl⟩ : syracuseStep 3376687 = 5065031) B5065031
theorem B4502249 : Blo 1999435 4502249 := bstep (se 2 (by rfl) ⟨1688343, by rfl⟩ : syracuseStep 4502249 = 3376687) B3376687
theorem B3001499 : Blo 1999435 3001499 := bstep (se 1 (by rfl) ⟨2251124, by rfl⟩ : syracuseStep 3001499 = 4502249) B4502249
theorem B2000999 : Blo 1999435 2000999 := bstep (se 1 (by rfl) ⟨1500749, by rfl⟩ : syracuseStep 2000999 = 3001499) B3001499
theorem B2251129 : Blo 1999435 2251129 := bbase (se 2 (by rfl) ⟨844173, by rfl⟩ : syracuseStep 2251129 = 1688347) (by norm_num)
theorem B3001505 : Blo 1999435 3001505 := bstep (se 2 (by rfl) ⟨1125564, by rfl⟩ : syracuseStep 3001505 = 2251129) B2251129
theorem B2001003 : Blo 1999435 2001003 := bstep (se 1 (by rfl) ⟨1500752, by rfl⟩ : syracuseStep 2001003 = 3001505) B3001505
theorem B9615685 : Blo 1999435 9615685 := bbase (se 4 (by rfl) ⟨901470, by rfl⟩ : syracuseStep 9615685 = 1802941) (by norm_num)
theorem B12820913 : Blo 1999435 12820913 := bstep (se 2 (by rfl) ⟨4807842, by rfl⟩ : syracuseStep 12820913 = 9615685) B9615685
theorem B8547275 : Blo 1999435 8547275 := bstep (se 1 (by rfl) ⟨6410456, by rfl⟩ : syracuseStep 8547275 = 12820913) B12820913
theorem B5698183 : Blo 1999435 5698183 := bstep (se 1 (by rfl) ⟨4273637, by rfl⟩ : syracuseStep 5698183 = 8547275) B8547275
theorem B7597577 : Blo 1999435 7597577 := bstep (se 2 (by rfl) ⟨2849091, by rfl⟩ : syracuseStep 7597577 = 5698183) B5698183
theorem B5065051 : Blo 1999435 5065051 := bstep (se 1 (by rfl) ⟨3798788, by rfl⟩ : syracuseStep 5065051 = 7597577) B7597577
theorem B6753401 : Blo 1999435 6753401 := bstep (se 2 (by rfl) ⟨2532525, by rfl⟩ : syracuseStep 6753401 = 5065051) B5065051
theorem B4502267 : Blo 1999435 4502267 := bstep (se 1 (by rfl) ⟨3376700, by rfl⟩ : syracuseStep 4502267 = 6753401) B6753401
theorem B3001511 : Blo 1999435 3001511 := bstep (se 1 (by rfl) ⟨2251133, by rfl⟩ : syracuseStep 3001511 = 4502267) B4502267
theorem B2001007 : Blo 1999435 2001007 := bstep (se 1 (by rfl) ⟨1500755, by rfl⟩ : syracuseStep 2001007 = 3001511) B3001511
theorem B3001517 : Blo 1999435 3001517 := bbase (se 3 (by rfl) ⟨562784, by rfl⟩ : syracuseStep 3001517 = 1125569) (by norm_num)
theorem B2001011 : Blo 1999435 2001011 := bstep (se 1 (by rfl) ⟨1500758, by rfl⟩ : syracuseStep 2001011 = 3001517) B3001517
theorem B4502285 : Blo 1999435 4502285 := bbase (se 3 (by rfl) ⟨844178, by rfl⟩ : syracuseStep 4502285 = 1688357) (by norm_num)
theorem B3001523 : Blo 1999435 3001523 := bstep (se 1 (by rfl) ⟨2251142, by rfl⟩ : syracuseStep 3001523 = 4502285) B4502285
theorem B2001015 : Blo 1999435 2001015 := bstep (se 1 (by rfl) ⟨1500761, by rfl⟩ : syracuseStep 2001015 = 3001523) B3001523
theorem B2532541 : Blo 1999435 2532541 := bbase (se 3 (by rfl) ⟨474851, by rfl⟩ : syracuseStep 2532541 = 949703) (by norm_num)
theorem B3376721 : Blo 1999435 3376721 := bstep (se 2 (by rfl) ⟨1266270, by rfl⟩ : syracuseStep 3376721 = 2532541) B2532541
theorem B2251147 : Blo 1999435 2251147 := bstep (se 1 (by rfl) ⟨1688360, by rfl⟩ : syracuseStep 2251147 = 3376721) B3376721
theorem B3001529 : Blo 1999435 3001529 := bstep (se 2 (by rfl) ⟨1125573, by rfl⟩ : syracuseStep 3001529 = 2251147) B2251147
theorem B2001019 : Blo 1999435 2001019 := bstep (se 1 (by rfl) ⟨1500764, by rfl⟩ : syracuseStep 2001019 = 3001529) B3001529
theorem B2028325 : Blo 1999435 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B2704433 : Blo 1999435 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B7211821 : Blo 1999435 7211821 := bstep (se 3 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 7211821 = 2704433) B2704433
theorem B9615761 : Blo 1999435 9615761 := bstep (se 2 (by rfl) ⟨3605910, by rfl⟩ : syracuseStep 9615761 = 7211821) B7211821
theorem B6410507 : Blo 1999435 6410507 := bstep (se 1 (by rfl) ⟨4807880, by rfl⟩ : syracuseStep 6410507 = 9615761) B9615761
theorem B17094685 : Blo 1999435 17094685 := bstep (se 3 (by rfl) ⟨3205253, by rfl⟩ : syracuseStep 17094685 = 6410507) B6410507
theorem B22792913 : Blo 1999435 22792913 := bstep (se 2 (by rfl) ⟨8547342, by rfl⟩ : syracuseStep 22792913 = 17094685) B17094685
theorem B15195275 : Blo 1999435 15195275 := bstep (se 1 (by rfl) ⟨11396456, by rfl⟩ : syracuseStep 15195275 = 22792913) B22792913
theorem B10130183 : Blo 1999435 10130183 := bstep (se 1 (by rfl) ⟨7597637, by rfl⟩ : syracuseStep 10130183 = 15195275) B15195275
theorem B6753455 : Blo 1999435 6753455 := bstep (se 1 (by rfl) ⟨5065091, by rfl⟩ : syracuseStep 6753455 = 10130183) B10130183
theorem B4502303 : Blo 1999435 4502303 := bstep (se 1 (by rfl) ⟨3376727, by rfl⟩ : syracuseStep 4502303 = 6753455) B6753455
theorem B3001535 : Blo 1999435 3001535 := bstep (se 1 (by rfl) ⟨2251151, by rfl⟩ : syracuseStep 3001535 = 4502303) B4502303
theorem B2001023 : Blo 1999435 2001023 := bstep (se 1 (by rfl) ⟨1500767, by rfl⟩ : syracuseStep 2001023 = 3001535) B3001535
theorem B3001541 : Blo 1999435 3001541 := bbase (se 4 (by rfl) ⟨281394, by rfl⟩ : syracuseStep 3001541 = 562789) (by norm_num)
theorem B2001027 : Blo 1999435 2001027 := bstep (se 1 (by rfl) ⟨1500770, by rfl⟩ : syracuseStep 2001027 = 3001541) B3001541
theorem B3376741 : Blo 1999435 3376741 := bbase (se 4 (by rfl) ⟨316569, by rfl⟩ : syracuseStep 3376741 = 633139) (by norm_num)
theorem B4502321 : Blo 1999435 4502321 := bstep (se 2 (by rfl) ⟨1688370, by rfl⟩ : syracuseStep 4502321 = 3376741) B3376741
theorem B3001547 : Blo 1999435 3001547 := bstep (se 1 (by rfl) ⟨2251160, by rfl⟩ : syracuseStep 3001547 = 4502321) B4502321
theorem B2001031 : Blo 1999435 2001031 := bstep (se 1 (by rfl) ⟨1500773, by rfl⟩ : syracuseStep 2001031 = 3001547) B3001547
theorem B2251165 : Blo 1999435 2251165 := bbase (se 3 (by rfl) ⟨422093, by rfl⟩ : syracuseStep 2251165 = 844187) (by norm_num)
theorem B3001553 : Blo 1999435 3001553 := bstep (se 2 (by rfl) ⟨1125582, by rfl⟩ : syracuseStep 3001553 = 2251165) B2251165
theorem B2001035 : Blo 1999435 2001035 := bstep (se 1 (by rfl) ⟨1500776, by rfl⟩ : syracuseStep 2001035 = 3001553) B3001553
theorem B6753509 : Blo 1999435 6753509 := bbase (se 4 (by rfl) ⟨633141, by rfl⟩ : syracuseStep 6753509 = 1266283) (by norm_num)
theorem B4502339 : Blo 1999435 4502339 := bstep (se 1 (by rfl) ⟨3376754, by rfl⟩ : syracuseStep 4502339 = 6753509) B6753509
theorem B3001559 : Blo 1999435 3001559 := bstep (se 1 (by rfl) ⟨2251169, by rfl⟩ : syracuseStep 3001559 = 4502339) B4502339
theorem B2001039 : Blo 1999435 2001039 := bstep (se 1 (by rfl) ⟨1500779, by rfl⟩ : syracuseStep 2001039 = 3001559) B3001559
theorem B3001565 : Blo 1999435 3001565 := bbase (se 3 (by rfl) ⟨562793, by rfl⟩ : syracuseStep 3001565 = 1125587) (by norm_num)
theorem B2001043 : Blo 1999435 2001043 := bstep (se 1 (by rfl) ⟨1500782, by rfl⟩ : syracuseStep 2001043 = 3001565) B3001565
theorem B4502357 : Blo 1999435 4502357 := bbase (se 9 (by rfl) ⟨13190, by rfl⟩ : syracuseStep 4502357 = 26381) (by norm_num)
theorem B3001571 : Blo 1999435 3001571 := bstep (se 1 (by rfl) ⟨2251178, by rfl⟩ : syracuseStep 3001571 = 4502357) B4502357
theorem B2001047 : Blo 1999435 2001047 := bstep (se 1 (by rfl) ⟨1500785, by rfl⟩ : syracuseStep 2001047 = 3001571) B3001571
theorem B5698309 : Blo 1999435 5698309 := bbase (se 4 (by rfl) ⟨534216, by rfl⟩ : syracuseStep 5698309 = 1068433) (by norm_num)
theorem B7597745 : Blo 1999435 7597745 := bstep (se 2 (by rfl) ⟨2849154, by rfl⟩ : syracuseStep 7597745 = 5698309) B5698309
theorem B5065163 : Blo 1999435 5065163 := bstep (se 1 (by rfl) ⟨3798872, by rfl⟩ : syracuseStep 5065163 = 7597745) B7597745
theorem B3376775 : Blo 1999435 3376775 := bstep (se 1 (by rfl) ⟨2532581, by rfl⟩ : syracuseStep 3376775 = 5065163) B5065163
theorem B2251183 : Blo 1999435 2251183 := bstep (se 1 (by rfl) ⟨1688387, by rfl⟩ : syracuseStep 2251183 = 3376775) B3376775
theorem B3001577 : Blo 1999435 3001577 := bstep (se 2 (by rfl) ⟨1125591, by rfl⟩ : syracuseStep 3001577 = 2251183) B2251183
theorem B2001051 : Blo 1999435 2001051 := bstep (se 1 (by rfl) ⟨1500788, by rfl⟩ : syracuseStep 2001051 = 3001577) B3001577
theorem B3126125 : Blo 1999435 3126125 := bbase (se 3 (by rfl) ⟨586148, by rfl⟩ : syracuseStep 3126125 = 1172297) (by norm_num)
theorem B8336333 : Blo 1999435 8336333 := bstep (se 3 (by rfl) ⟨1563062, by rfl⟩ : syracuseStep 8336333 = 3126125) B3126125
theorem B5557555 : Blo 1999435 5557555 := bstep (se 1 (by rfl) ⟨4168166, by rfl⟩ : syracuseStep 5557555 = 8336333) B8336333
theorem B29640293 : Blo 1999435 29640293 := bstep (se 4 (by rfl) ⟨2778777, by rfl⟩ : syracuseStep 29640293 = 5557555) B5557555
theorem B19760195 : Blo 1999435 19760195 := bstep (se 1 (by rfl) ⟨14820146, by rfl⟩ : syracuseStep 19760195 = 29640293) B29640293
theorem B13173463 : Blo 1999435 13173463 := bstep (se 1 (by rfl) ⟨9880097, by rfl⟩ : syracuseStep 13173463 = 19760195) B19760195
theorem B17564617 : Blo 1999435 17564617 := bstep (se 2 (by rfl) ⟨6586731, by rfl⟩ : syracuseStep 17564617 = 13173463) B13173463
theorem B23419489 : Blo 1999435 23419489 := bstep (se 2 (by rfl) ⟨8782308, by rfl⟩ : syracuseStep 23419489 = 17564617) B17564617
theorem B31225985 : Blo 1999435 31225985 := bstep (se 2 (by rfl) ⟨11709744, by rfl⟩ : syracuseStep 31225985 = 23419489) B23419489
theorem B20817323 : Blo 1999435 20817323 := bstep (se 1 (by rfl) ⟨15612992, by rfl⟩ : syracuseStep 20817323 = 31225985) B31225985
theorem B13878215 : Blo 1999435 13878215 := bstep (se 1 (by rfl) ⟨10408661, by rfl⟩ : syracuseStep 13878215 = 20817323) B20817323
theorem B9252143 : Blo 1999435 9252143 := bstep (se 1 (by rfl) ⟨6939107, by rfl⟩ : syracuseStep 9252143 = 13878215) B13878215
theorem B6168095 : Blo 1999435 6168095 := bstep (se 1 (by rfl) ⟨4626071, by rfl⟩ : syracuseStep 6168095 = 9252143) B9252143
theorem B4112063 : Blo 1999435 4112063 := bstep (se 1 (by rfl) ⟨3084047, by rfl⟩ : syracuseStep 4112063 = 6168095) B6168095
theorem B2741375 : Blo 1999435 2741375 := bstep (se 1 (by rfl) ⟨2056031, by rfl⟩ : syracuseStep 2741375 = 4112063) B4112063
theorem B7310333 : Blo 1999435 7310333 := bstep (se 3 (by rfl) ⟨1370687, by rfl⟩ : syracuseStep 7310333 = 2741375) B2741375
theorem B4873555 : Blo 1999435 4873555 := bstep (se 1 (by rfl) ⟨3655166, by rfl⟩ : syracuseStep 4873555 = 7310333) B7310333
theorem B6498073 : Blo 1999435 6498073 := bstep (se 2 (by rfl) ⟨2436777, by rfl⟩ : syracuseStep 6498073 = 4873555) B4873555
theorem B8664097 : Blo 1999435 8664097 := bstep (se 2 (by rfl) ⟨3249036, by rfl⟩ : syracuseStep 8664097 = 6498073) B6498073
theorem B11552129 : Blo 1999435 11552129 := bstep (se 2 (by rfl) ⟨4332048, by rfl⟩ : syracuseStep 11552129 = 8664097) B8664097
theorem B7701419 : Blo 1999435 7701419 := bstep (se 1 (by rfl) ⟨5776064, by rfl⟩ : syracuseStep 7701419 = 11552129) B11552129
theorem B20537117 : Blo 1999435 20537117 := bstep (se 3 (by rfl) ⟨3850709, by rfl⟩ : syracuseStep 20537117 = 7701419) B7701419
theorem B13691411 : Blo 1999435 13691411 := bstep (se 1 (by rfl) ⟨10268558, by rfl⟩ : syracuseStep 13691411 = 20537117) B20537117
theorem B9127607 : Blo 1999435 9127607 := bstep (se 1 (by rfl) ⟨6845705, by rfl⟩ : syracuseStep 9127607 = 13691411) B13691411
theorem B24340285 : Blo 1999435 24340285 := bstep (se 3 (by rfl) ⟨4563803, by rfl⟩ : syracuseStep 24340285 = 9127607) B9127607
theorem B32453713 : Blo 1999435 32453713 := bstep (se 2 (by rfl) ⟨12170142, by rfl⟩ : syracuseStep 32453713 = 24340285) B24340285
theorem B43271617 : Blo 1999435 43271617 := bstep (se 2 (by rfl) ⟨16226856, by rfl⟩ : syracuseStep 43271617 = 32453713) B32453713
theorem B57695489 : Blo 1999435 57695489 := bstep (se 2 (by rfl) ⟨21635808, by rfl⟩ : syracuseStep 57695489 = 43271617) B43271617
theorem B38463659 : Blo 1999435 38463659 := bstep (se 1 (by rfl) ⟨28847744, by rfl⟩ : syracuseStep 38463659 = 57695489) B57695489
theorem B25642439 : Blo 1999435 25642439 := bstep (se 1 (by rfl) ⟨19231829, by rfl⟩ : syracuseStep 25642439 = 38463659) B38463659
theorem B17094959 : Blo 1999435 17094959 := bstep (se 1 (by rfl) ⟨12821219, by rfl⟩ : syracuseStep 17094959 = 25642439) B25642439
theorem B11396639 : Blo 1999435 11396639 := bstep (se 1 (by rfl) ⟨8547479, by rfl⟩ : syracuseStep 11396639 = 17094959) B17094959
theorem B7597759 : Blo 1999435 7597759 := bstep (se 1 (by rfl) ⟨5698319, by rfl⟩ : syracuseStep 7597759 = 11396639) B11396639
theorem B10130345 : Blo 1999435 10130345 := bstep (se 2 (by rfl) ⟨3798879, by rfl⟩ : syracuseStep 10130345 = 7597759) B7597759
theorem B6753563 : Blo 1999435 6753563 := bstep (se 1 (by rfl) ⟨5065172, by rfl⟩ : syracuseStep 6753563 = 10130345) B10130345
theorem B4502375 : Blo 1999435 4502375 := bstep (se 1 (by rfl) ⟨3376781, by rfl⟩ : syracuseStep 4502375 = 6753563) B6753563
theorem B3001583 : Blo 1999435 3001583 := bstep (se 1 (by rfl) ⟨2251187, by rfl⟩ : syracuseStep 3001583 = 4502375) B4502375
theorem B2001055 : Blo 1999435 2001055 := bstep (se 1 (by rfl) ⟨1500791, by rfl⟩ : syracuseStep 2001055 = 3001583) B3001583
theorem B3001589 : Blo 1999435 3001589 := bbase (se 5 (by rfl) ⟨140699, by rfl⟩ : syracuseStep 3001589 = 281399) (by norm_num)
theorem B2001059 : Blo 1999435 2001059 := bstep (se 1 (by rfl) ⟨1500794, by rfl⟩ : syracuseStep 2001059 = 3001589) B3001589
theorem B6498101 : Blo 1999435 6498101 := bbase (se 5 (by rfl) ⟨304598, by rfl⟩ : syracuseStep 6498101 = 609197) (by norm_num)
theorem B17328269 : Blo 1999435 17328269 := bstep (se 3 (by rfl) ⟨3249050, by rfl⟩ : syracuseStep 17328269 = 6498101) B6498101
theorem B11552179 : Blo 1999435 11552179 := bstep (se 1 (by rfl) ⟨8664134, by rfl⟩ : syracuseStep 11552179 = 17328269) B17328269
theorem B15402905 : Blo 1999435 15402905 := bstep (se 2 (by rfl) ⟨5776089, by rfl⟩ : syracuseStep 15402905 = 11552179) B11552179
theorem B10268603 : Blo 1999435 10268603 := bstep (se 1 (by rfl) ⟨7701452, by rfl⟩ : syracuseStep 10268603 = 15402905) B15402905
theorem B6845735 : Blo 1999435 6845735 := bstep (se 1 (by rfl) ⟨5134301, by rfl⟩ : syracuseStep 6845735 = 10268603) B10268603
theorem B18255293 : Blo 1999435 18255293 := bstep (se 3 (by rfl) ⟨3422867, by rfl⟩ : syracuseStep 18255293 = 6845735) B6845735
theorem B12170195 : Blo 1999435 12170195 := bstep (se 1 (by rfl) ⟨9127646, by rfl⟩ : syracuseStep 12170195 = 18255293) B18255293
theorem B8113463 : Blo 1999435 8113463 := bstep (se 1 (by rfl) ⟨6085097, by rfl⟩ : syracuseStep 8113463 = 12170195) B12170195
theorem B5408975 : Blo 1999435 5408975 := bstep (se 1 (by rfl) ⟨4056731, by rfl⟩ : syracuseStep 5408975 = 8113463) B8113463
theorem B14423933 : Blo 1999435 14423933 := bstep (se 3 (by rfl) ⟨2704487, by rfl⟩ : syracuseStep 14423933 = 5408975) B5408975
theorem B9615955 : Blo 1999435 9615955 := bstep (se 1 (by rfl) ⟨7211966, by rfl⟩ : syracuseStep 9615955 = 14423933) B14423933
theorem B12821273 : Blo 1999435 12821273 := bstep (se 2 (by rfl) ⟨4807977, by rfl⟩ : syracuseStep 12821273 = 9615955) B9615955
theorem B8547515 : Blo 1999435 8547515 := bstep (se 1 (by rfl) ⟨6410636, by rfl⟩ : syracuseStep 8547515 = 12821273) B12821273
theorem B5698343 : Blo 1999435 5698343 := bstep (se 1 (by rfl) ⟨4273757, by rfl⟩ : syracuseStep 5698343 = 8547515) B8547515
theorem B3798895 : Blo 1999435 3798895 := bstep (se 1 (by rfl) ⟨2849171, by rfl⟩ : syracuseStep 3798895 = 5698343) B5698343
theorem B5065193 : Blo 1999435 5065193 := bstep (se 2 (by rfl) ⟨1899447, by rfl⟩ : syracuseStep 5065193 = 3798895) B3798895
theorem B3376795 : Blo 1999435 3376795 := bstep (se 1 (by rfl) ⟨2532596, by rfl⟩ : syracuseStep 3376795 = 5065193) B5065193
theorem B4502393 : Blo 1999435 4502393 := bstep (se 2 (by rfl) ⟨1688397, by rfl⟩ : syracuseStep 4502393 = 3376795) B3376795
theorem B3001595 : Blo 1999435 3001595 := bstep (se 1 (by rfl) ⟨2251196, by rfl⟩ : syracuseStep 3001595 = 4502393) B4502393
theorem B2001063 : Blo 1999435 2001063 := bstep (se 1 (by rfl) ⟨1500797, by rfl⟩ : syracuseStep 2001063 = 3001595) B3001595
theorem B2251201 : Blo 1999435 2251201 := bbase (se 2 (by rfl) ⟨844200, by rfl⟩ : syracuseStep 2251201 = 1688401) (by norm_num)
theorem B3001601 : Blo 1999435 3001601 := bstep (se 2 (by rfl) ⟨1125600, by rfl⟩ : syracuseStep 3001601 = 2251201) B2251201
theorem B2001067 : Blo 1999435 2001067 := bstep (se 1 (by rfl) ⟨1500800, by rfl⟩ : syracuseStep 2001067 = 3001601) B3001601
theorem B5065213 : Blo 1999435 5065213 := bbase (se 3 (by rfl) ⟨949727, by rfl⟩ : syracuseStep 5065213 = 1899455) (by norm_num)
theorem B6753617 : Blo 1999435 6753617 := bstep (se 2 (by rfl) ⟨2532606, by rfl⟩ : syracuseStep 6753617 = 5065213) B5065213
theorem B4502411 : Blo 1999435 4502411 := bstep (se 1 (by rfl) ⟨3376808, by rfl⟩ : syracuseStep 4502411 = 6753617) B6753617
theorem B3001607 : Blo 1999435 3001607 := bstep (se 1 (by rfl) ⟨2251205, by rfl⟩ : syracuseStep 3001607 = 4502411) B4502411
theorem B2001071 : Blo 1999435 2001071 := bstep (se 1 (by rfl) ⟨1500803, by rfl⟩ : syracuseStep 2001071 = 3001607) B3001607
theorem B3001613 : Blo 1999435 3001613 := bbase (se 3 (by rfl) ⟨562802, by rfl⟩ : syracuseStep 3001613 = 1125605) (by norm_num)
theorem B2001075 : Blo 1999435 2001075 := bstep (se 1 (by rfl) ⟨1500806, by rfl⟩ : syracuseStep 2001075 = 3001613) B3001613
theorem B4502429 : Blo 1999435 4502429 := bbase (se 3 (by rfl) ⟨844205, by rfl⟩ : syracuseStep 4502429 = 1688411) (by norm_num)
theorem B3001619 : Blo 1999435 3001619 := bstep (se 1 (by rfl) ⟨2251214, by rfl⟩ : syracuseStep 3001619 = 4502429) B4502429
theorem B2001079 : Blo 1999435 2001079 := bstep (se 1 (by rfl) ⟨1500809, by rfl⟩ : syracuseStep 2001079 = 3001619) B3001619
theorem B3376829 : Blo 1999435 3376829 := bbase (se 3 (by rfl) ⟨633155, by rfl⟩ : syracuseStep 3376829 = 1266311) (by norm_num)
theorem B2251219 : Blo 1999435 2251219 := bstep (se 1 (by rfl) ⟨1688414, by rfl⟩ : syracuseStep 2251219 = 3376829) B3376829
theorem B3001625 : Blo 1999435 3001625 := bstep (se 2 (by rfl) ⟨1125609, by rfl⟩ : syracuseStep 3001625 = 2251219) B2251219
theorem B2001083 : Blo 1999435 2001083 := bstep (se 1 (by rfl) ⟨1500812, by rfl⟩ : syracuseStep 2001083 = 3001625) B3001625
theorem B11396821 : Blo 1999435 11396821 := bbase (se 7 (by rfl) ⟨133556, by rfl⟩ : syracuseStep 11396821 = 267113) (by norm_num)
theorem B15195761 : Blo 1999435 15195761 := bstep (se 2 (by rfl) ⟨5698410, by rfl⟩ : syracuseStep 15195761 = 11396821) B11396821
theorem B10130507 : Blo 1999435 10130507 := bstep (se 1 (by rfl) ⟨7597880, by rfl⟩ : syracuseStep 10130507 = 15195761) B15195761
theorem B6753671 : Blo 1999435 6753671 := bstep (se 1 (by rfl) ⟨5065253, by rfl⟩ : syracuseStep 6753671 = 10130507) B10130507
theorem B4502447 : Blo 1999435 4502447 := bstep (se 1 (by rfl) ⟨3376835, by rfl⟩ : syracuseStep 4502447 = 6753671) B6753671
theorem B3001631 : Blo 1999435 3001631 := bstep (se 1 (by rfl) ⟨2251223, by rfl⟩ : syracuseStep 3001631 = 4502447) B4502447
theorem B2001087 : Blo 1999435 2001087 := bstep (se 1 (by rfl) ⟨1500815, by rfl⟩ : syracuseStep 2001087 = 3001631) B3001631
theorem B3001637 : Blo 1999435 3001637 := bbase (se 4 (by rfl) ⟨281403, by rfl⟩ : syracuseStep 3001637 = 562807) (by norm_num)
theorem B2001091 : Blo 1999435 2001091 := bstep (se 1 (by rfl) ⟨1500818, by rfl⟩ : syracuseStep 2001091 = 3001637) B3001637
theorem B2532637 : Blo 1999435 2532637 := bbase (se 3 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 2532637 = 949739) (by norm_num)
theorem B3376849 : Blo 1999435 3376849 := bstep (se 2 (by rfl) ⟨1266318, by rfl⟩ : syracuseStep 3376849 = 2532637) B2532637
theorem B4502465 : Blo 1999435 4502465 := bstep (se 2 (by rfl) ⟨1688424, by rfl⟩ : syracuseStep 4502465 = 3376849) B3376849
theorem B3001643 : Blo 1999435 3001643 := bstep (se 1 (by rfl) ⟨2251232, by rfl⟩ : syracuseStep 3001643 = 4502465) B4502465
theorem B2001095 : Blo 1999435 2001095 := bstep (se 1 (by rfl) ⟨1500821, by rfl⟩ : syracuseStep 2001095 = 3001643) B3001643
theorem B2251237 : Blo 1999435 2251237 := bbase (se 4 (by rfl) ⟨211053, by rfl⟩ : syracuseStep 2251237 = 422107) (by norm_num)
theorem B3001649 : Blo 1999435 3001649 := bstep (se 2 (by rfl) ⟨1125618, by rfl⟩ : syracuseStep 3001649 = 2251237) B2251237
theorem B2001099 : Blo 1999435 2001099 := bstep (se 1 (by rfl) ⟨1500824, by rfl⟩ : syracuseStep 2001099 = 3001649) B3001649
theorem B2404037 : Blo 1999435 2404037 := bbase (se 4 (by rfl) ⟨225378, by rfl⟩ : syracuseStep 2404037 = 450757) (by norm_num)
theorem B6410765 : Blo 1999435 6410765 := bstep (se 3 (by rfl) ⟨1202018, by rfl⟩ : syracuseStep 6410765 = 2404037) B2404037
theorem B4273843 : Blo 1999435 4273843 := bstep (se 1 (by rfl) ⟨3205382, by rfl⟩ : syracuseStep 4273843 = 6410765) B6410765
theorem B5698457 : Blo 1999435 5698457 := bstep (se 2 (by rfl) ⟨2136921, by rfl⟩ : syracuseStep 5698457 = 4273843) B4273843
theorem B3798971 : Blo 1999435 3798971 := bstep (se 1 (by rfl) ⟨2849228, by rfl⟩ : syracuseStep 3798971 = 5698457) B5698457
theorem B2532647 : Blo 1999435 2532647 := bstep (se 1 (by rfl) ⟨1899485, by rfl⟩ : syracuseStep 2532647 = 3798971) B3798971
theorem B6753725 : Blo 1999435 6753725 := bstep (se 3 (by rfl) ⟨1266323, by rfl⟩ : syracuseStep 6753725 = 2532647) B2532647
theorem B4502483 : Blo 1999435 4502483 := bstep (se 1 (by rfl) ⟨3376862, by rfl⟩ : syracuseStep 4502483 = 6753725) B6753725
theorem B3001655 : Blo 1999435 3001655 := bstep (se 1 (by rfl) ⟨2251241, by rfl⟩ : syracuseStep 3001655 = 4502483) B4502483
theorem B2001103 : Blo 1999435 2001103 := bstep (se 1 (by rfl) ⟨1500827, by rfl⟩ : syracuseStep 2001103 = 3001655) B3001655
theorem B3001661 : Blo 1999435 3001661 := bbase (se 3 (by rfl) ⟨562811, by rfl⟩ : syracuseStep 3001661 = 1125623) (by norm_num)
theorem B2001107 : Blo 1999435 2001107 := bstep (se 1 (by rfl) ⟨1500830, by rfl⟩ : syracuseStep 2001107 = 3001661) B3001661
theorem B4502501 : Blo 1999435 4502501 := bbase (se 4 (by rfl) ⟨422109, by rfl⟩ : syracuseStep 4502501 = 844219) (by norm_num)
theorem B3001667 : Blo 1999435 3001667 := bstep (se 1 (by rfl) ⟨2251250, by rfl⟩ : syracuseStep 3001667 = 4502501) B4502501
theorem B2001111 : Blo 1999435 2001111 := bstep (se 1 (by rfl) ⟨1500833, by rfl⟩ : syracuseStep 2001111 = 3001667) B3001667
theorem B5065325 : Blo 1999435 5065325 := bbase (se 3 (by rfl) ⟨949748, by rfl⟩ : syracuseStep 5065325 = 1899497) (by norm_num)
theorem B3376883 : Blo 1999435 3376883 := bstep (se 1 (by rfl) ⟨2532662, by rfl⟩ : syracuseStep 3376883 = 5065325) B5065325
theorem B2251255 : Blo 1999435 2251255 := bstep (se 1 (by rfl) ⟨1688441, by rfl⟩ : syracuseStep 2251255 = 3376883) B3376883
theorem B3001673 : Blo 1999435 3001673 := bstep (se 2 (by rfl) ⟨1125627, by rfl⟩ : syracuseStep 3001673 = 2251255) B2251255
theorem B2001115 : Blo 1999435 2001115 := bstep (se 1 (by rfl) ⟨1500836, by rfl⟩ : syracuseStep 2001115 = 3001673) B3001673
theorem B4273877 : Blo 1999435 4273877 := bbase (se 7 (by rfl) ⟨50084, by rfl⟩ : syracuseStep 4273877 = 100169) (by norm_num)
theorem B2849251 : Blo 1999435 2849251 := bstep (se 1 (by rfl) ⟨2136938, by rfl⟩ : syracuseStep 2849251 = 4273877) B4273877
theorem B3799001 : Blo 1999435 3799001 := bstep (se 2 (by rfl) ⟨1424625, by rfl⟩ : syracuseStep 3799001 = 2849251) B2849251
theorem B10130669 : Blo 1999435 10130669 := bstep (se 3 (by rfl) ⟨1899500, by rfl⟩ : syracuseStep 10130669 = 3799001) B3799001
theorem B6753779 : Blo 1999435 6753779 := bstep (se 1 (by rfl) ⟨5065334, by rfl⟩ : syracuseStep 6753779 = 10130669) B10130669
theorem B4502519 : Blo 1999435 4502519 := bstep (se 1 (by rfl) ⟨3376889, by rfl⟩ : syracuseStep 4502519 = 6753779) B6753779
theorem B3001679 : Blo 1999435 3001679 := bstep (se 1 (by rfl) ⟨2251259, by rfl⟩ : syracuseStep 3001679 = 4502519) B4502519
theorem B2001119 : Blo 1999435 2001119 := bstep (se 1 (by rfl) ⟨1500839, by rfl⟩ : syracuseStep 2001119 = 3001679) B3001679
theorem B3001685 : Blo 1999435 3001685 := bbase (se 11 (by rfl) ⟨2198, by rfl⟩ : syracuseStep 3001685 = 4397) (by norm_num)
theorem B2001123 : Blo 1999435 2001123 := bstep (se 1 (by rfl) ⟨1500842, by rfl⟩ : syracuseStep 2001123 = 3001685) B3001685
theorem B3205421 : Blo 1999435 3205421 := bbase (se 3 (by rfl) ⟨601016, by rfl⟩ : syracuseStep 3205421 = 1202033) (by norm_num)
theorem B2136947 : Blo 1999435 2136947 := bstep (se 1 (by rfl) ⟨1602710, by rfl⟩ : syracuseStep 2136947 = 3205421) B3205421
theorem B5698525 : Blo 1999435 5698525 := bstep (se 3 (by rfl) ⟨1068473, by rfl⟩ : syracuseStep 5698525 = 2136947) B2136947
theorem B7598033 : Blo 1999435 7598033 := bstep (se 2 (by rfl) ⟨2849262, by rfl⟩ : syracuseStep 7598033 = 5698525) B5698525
theorem B5065355 : Blo 1999435 5065355 := bstep (se 1 (by rfl) ⟨3799016, by rfl⟩ : syracuseStep 5065355 = 7598033) B7598033
theorem B3376903 : Blo 1999435 3376903 := bstep (se 1 (by rfl) ⟨2532677, by rfl⟩ : syracuseStep 3376903 = 5065355) B5065355
theorem B4502537 : Blo 1999435 4502537 := bstep (se 2 (by rfl) ⟨1688451, by rfl⟩ : syracuseStep 4502537 = 3376903) B3376903
theorem B3001691 : Blo 1999435 3001691 := bstep (se 1 (by rfl) ⟨2251268, by rfl⟩ : syracuseStep 3001691 = 4502537) B4502537
theorem B2001127 : Blo 1999435 2001127 := bstep (se 1 (by rfl) ⟨1500845, by rfl⟩ : syracuseStep 2001127 = 3001691) B3001691
theorem B2251273 : Blo 1999435 2251273 := bbase (se 2 (by rfl) ⟨844227, by rfl⟩ : syracuseStep 2251273 = 1688455) (by norm_num)
theorem B3001697 : Blo 1999435 3001697 := bstep (se 2 (by rfl) ⟨1125636, by rfl⟩ : syracuseStep 3001697 = 2251273) B2251273
theorem B2001131 : Blo 1999435 2001131 := bstep (se 1 (by rfl) ⟨1500848, by rfl⟩ : syracuseStep 2001131 = 3001697) B3001697
theorem B9127973 : Blo 1999435 9127973 := bbase (se 4 (by rfl) ⟨855747, by rfl⟩ : syracuseStep 9127973 = 1711495) (by norm_num)
theorem B6085315 : Blo 1999435 6085315 := bstep (se 1 (by rfl) ⟨4563986, by rfl⟩ : syracuseStep 6085315 = 9127973) B9127973
theorem B8113753 : Blo 1999435 8113753 := bstep (se 2 (by rfl) ⟨3042657, by rfl⟩ : syracuseStep 8113753 = 6085315) B6085315
theorem B43273349 : Blo 1999435 43273349 := bstep (se 4 (by rfl) ⟨4056876, by rfl⟩ : syracuseStep 43273349 = 8113753) B8113753
theorem B28848899 : Blo 1999435 28848899 := bstep (se 1 (by rfl) ⟨21636674, by rfl⟩ : syracuseStep 28848899 = 43273349) B43273349
theorem B19232599 : Blo 1999435 19232599 := bstep (se 1 (by rfl) ⟨14424449, by rfl⟩ : syracuseStep 19232599 = 28848899) B28848899
theorem B25643465 : Blo 1999435 25643465 := bstep (se 2 (by rfl) ⟨9616299, by rfl⟩ : syracuseStep 25643465 = 19232599) B19232599
theorem B17095643 : Blo 1999435 17095643 := bstep (se 1 (by rfl) ⟨12821732, by rfl⟩ : syracuseStep 17095643 = 25643465) B25643465
theorem B11397095 : Blo 1999435 11397095 := bstep (se 1 (by rfl) ⟨8547821, by rfl⟩ : syracuseStep 11397095 = 17095643) B17095643
theorem B7598063 : Blo 1999435 7598063 := bstep (se 1 (by rfl) ⟨5698547, by rfl⟩ : syracuseStep 7598063 = 11397095) B11397095
theorem B5065375 : Blo 1999435 5065375 := bstep (se 1 (by rfl) ⟨3799031, by rfl⟩ : syracuseStep 5065375 = 7598063) B7598063
theorem B6753833 : Blo 1999435 6753833 := bstep (se 2 (by rfl) ⟨2532687, by rfl⟩ : syracuseStep 6753833 = 5065375) B5065375
theorem B4502555 : Blo 1999435 4502555 := bstep (se 1 (by rfl) ⟨3376916, by rfl⟩ : syracuseStep 4502555 = 6753833) B6753833
theorem B3001703 : Blo 1999435 3001703 := bstep (se 1 (by rfl) ⟨2251277, by rfl⟩ : syracuseStep 3001703 = 4502555) B4502555
theorem B2001135 : Blo 1999435 2001135 := bstep (se 1 (by rfl) ⟨1500851, by rfl⟩ : syracuseStep 2001135 = 3001703) B3001703
theorem B3001709 : Blo 1999435 3001709 := bbase (se 3 (by rfl) ⟨562820, by rfl⟩ : syracuseStep 3001709 = 1125641) (by norm_num)
theorem B2001139 : Blo 1999435 2001139 := bstep (se 1 (by rfl) ⟨1500854, by rfl⟩ : syracuseStep 2001139 = 3001709) B3001709
theorem B4502573 : Blo 1999435 4502573 := bbase (se 3 (by rfl) ⟨844232, by rfl⟩ : syracuseStep 4502573 = 1688465) (by norm_num)
theorem B3001715 : Blo 1999435 3001715 := bstep (se 1 (by rfl) ⟨2251286, by rfl⟩ : syracuseStep 3001715 = 4502573) B4502573
theorem B2001143 : Blo 1999435 2001143 := bstep (se 1 (by rfl) ⟨1500857, by rfl⟩ : syracuseStep 2001143 = 3001715) B3001715
theorem B12821813 : Blo 1999435 12821813 := bbase (se 5 (by rfl) ⟨601022, by rfl⟩ : syracuseStep 12821813 = 1202045) (by norm_num)
theorem B8547875 : Blo 1999435 8547875 := bstep (se 1 (by rfl) ⟨6410906, by rfl⟩ : syracuseStep 8547875 = 12821813) B12821813
theorem B5698583 : Blo 1999435 5698583 := bstep (se 1 (by rfl) ⟨4273937, by rfl⟩ : syracuseStep 5698583 = 8547875) B8547875
theorem B3799055 : Blo 1999435 3799055 := bstep (se 1 (by rfl) ⟨2849291, by rfl⟩ : syracuseStep 3799055 = 5698583) B5698583
theorem B2532703 : Blo 1999435 2532703 := bstep (se 1 (by rfl) ⟨1899527, by rfl⟩ : syracuseStep 2532703 = 3799055) B3799055
theorem B3376937 : Blo 1999435 3376937 := bstep (se 2 (by rfl) ⟨1266351, by rfl⟩ : syracuseStep 3376937 = 2532703) B2532703
theorem B2251291 : Blo 1999435 2251291 := bstep (se 1 (by rfl) ⟨1688468, by rfl⟩ : syracuseStep 2251291 = 3376937) B3376937
theorem B3001721 : Blo 1999435 3001721 := bstep (se 2 (by rfl) ⟨1125645, by rfl⟩ : syracuseStep 3001721 = 2251291) B2251291
theorem B2001147 : Blo 1999435 2001147 := bstep (se 1 (by rfl) ⟨1500860, by rfl⟩ : syracuseStep 2001147 = 3001721) B3001721
theorem B6410917 : Blo 1999435 6410917 := bbase (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) (by norm_num)
theorem B34191557 : Blo 1999435 34191557 := bstep (se 4 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 34191557 = 6410917) B6410917
theorem B22794371 : Blo 1999435 22794371 := bstep (se 1 (by rfl) ⟨17095778, by rfl⟩ : syracuseStep 22794371 = 34191557) B34191557
theorem B15196247 : Blo 1999435 15196247 := bstep (se 1 (by rfl) ⟨11397185, by rfl⟩ : syracuseStep 15196247 = 22794371) B22794371
theorem B10130831 : Blo 1999435 10130831 := bstep (se 1 (by rfl) ⟨7598123, by rfl⟩ : syracuseStep 10130831 = 15196247) B15196247
theorem B6753887 : Blo 1999435 6753887 := bstep (se 1 (by rfl) ⟨5065415, by rfl⟩ : syracuseStep 6753887 = 10130831) B10130831
theorem B4502591 : Blo 1999435 4502591 := bstep (se 1 (by rfl) ⟨3376943, by rfl⟩ : syracuseStep 4502591 = 6753887) B6753887
theorem B3001727 : Blo 1999435 3001727 := bstep (se 1 (by rfl) ⟨2251295, by rfl⟩ : syracuseStep 3001727 = 4502591) B4502591
theorem B2001151 : Blo 1999435 2001151 := bstep (se 1 (by rfl) ⟨1500863, by rfl⟩ : syracuseStep 2001151 = 3001727) B3001727
theorem B3001733 : Blo 1999435 3001733 := bbase (se 4 (by rfl) ⟨281412, by rfl⟩ : syracuseStep 3001733 = 562825) (by norm_num)
theorem B2001155 : Blo 1999435 2001155 := bstep (se 1 (by rfl) ⟨1500866, by rfl⟩ : syracuseStep 2001155 = 3001733) B3001733
theorem B3376957 : Blo 1999435 3376957 := bbase (se 3 (by rfl) ⟨633179, by rfl⟩ : syracuseStep 3376957 = 1266359) (by norm_num)
theorem B4502609 : Blo 1999435 4502609 := bstep (se 2 (by rfl) ⟨1688478, by rfl⟩ : syracuseStep 4502609 = 3376957) B3376957
theorem B3001739 : Blo 1999435 3001739 := bstep (se 1 (by rfl) ⟨2251304, by rfl⟩ : syracuseStep 3001739 = 4502609) B4502609
theorem B2001159 : Blo 1999435 2001159 := bstep (se 1 (by rfl) ⟨1500869, by rfl⟩ : syracuseStep 2001159 = 3001739) B3001739
theorem B2251309 : Blo 1999435 2251309 := bbase (se 3 (by rfl) ⟨422120, by rfl⟩ : syracuseStep 2251309 = 844241) (by norm_num)
theorem B3001745 : Blo 1999435 3001745 := bstep (se 2 (by rfl) ⟨1125654, by rfl⟩ : syracuseStep 3001745 = 2251309) B2251309
theorem B2001163 : Blo 1999435 2001163 := bstep (se 1 (by rfl) ⟨1500872, by rfl⟩ : syracuseStep 2001163 = 3001745) B3001745
theorem B6753941 : Blo 1999435 6753941 := bbase (se 6 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 6753941 = 316591) (by norm_num)
theorem B4502627 : Blo 1999435 4502627 := bstep (se 1 (by rfl) ⟨3376970, by rfl⟩ : syracuseStep 4502627 = 6753941) B6753941
theorem B3001751 : Blo 1999435 3001751 := bstep (se 1 (by rfl) ⟨2251313, by rfl⟩ : syracuseStep 3001751 = 4502627) B4502627
theorem B2001167 : Blo 1999435 2001167 := bstep (se 1 (by rfl) ⟨1500875, by rfl⟩ : syracuseStep 2001167 = 3001751) B3001751
theorem B3001757 : Blo 1999435 3001757 := bbase (se 3 (by rfl) ⟨562829, by rfl⟩ : syracuseStep 3001757 = 1125659) (by norm_num)
theorem B2001171 : Blo 1999435 2001171 := bstep (se 1 (by rfl) ⟨1500878, by rfl⟩ : syracuseStep 2001171 = 3001757) B3001757
theorem B4502645 : Blo 1999435 4502645 := bbase (se 5 (by rfl) ⟨211061, by rfl⟩ : syracuseStep 4502645 = 422123) (by norm_num)
theorem B3001763 : Blo 1999435 3001763 := bstep (se 1 (by rfl) ⟨2251322, by rfl⟩ : syracuseStep 3001763 = 4502645) B4502645
theorem B2001175 : Blo 1999435 2001175 := bstep (se 1 (by rfl) ⟨1500881, by rfl⟩ : syracuseStep 2001175 = 3001763) B3001763
theorem B17096021 : Blo 1999435 17096021 := bbase (se 11 (by rfl) ⟨12521, by rfl⟩ : syracuseStep 17096021 = 25043) (by norm_num)
theorem B11397347 : Blo 1999435 11397347 := bstep (se 1 (by rfl) ⟨8548010, by rfl⟩ : syracuseStep 11397347 = 17096021) B17096021
theorem B7598231 : Blo 1999435 7598231 := bstep (se 1 (by rfl) ⟨5698673, by rfl⟩ : syracuseStep 7598231 = 11397347) B11397347
theorem B5065487 : Blo 1999435 5065487 := bstep (se 1 (by rfl) ⟨3799115, by rfl⟩ : syracuseStep 5065487 = 7598231) B7598231
theorem B3376991 : Blo 1999435 3376991 := bstep (se 1 (by rfl) ⟨2532743, by rfl⟩ : syracuseStep 3376991 = 5065487) B5065487
theorem B2251327 : Blo 1999435 2251327 := bstep (se 1 (by rfl) ⟨1688495, by rfl⟩ : syracuseStep 2251327 = 3376991) B3376991
theorem B3001769 : Blo 1999435 3001769 := bstep (se 2 (by rfl) ⟨1125663, by rfl⟩ : syracuseStep 3001769 = 2251327) B2251327
theorem B2001179 : Blo 1999435 2001179 := bstep (se 1 (by rfl) ⟨1500884, by rfl⟩ : syracuseStep 2001179 = 3001769) B3001769
theorem B7598245 : Blo 1999435 7598245 := bbase (se 4 (by rfl) ⟨712335, by rfl⟩ : syracuseStep 7598245 = 1424671) (by norm_num)
theorem B10130993 : Blo 1999435 10130993 := bstep (se 2 (by rfl) ⟨3799122, by rfl⟩ : syracuseStep 10130993 = 7598245) B7598245
theorem B6753995 : Blo 1999435 6753995 := bstep (se 1 (by rfl) ⟨5065496, by rfl⟩ : syracuseStep 6753995 = 10130993) B10130993
theorem B4502663 : Blo 1999435 4502663 := bstep (se 1 (by rfl) ⟨3376997, by rfl⟩ : syracuseStep 4502663 = 6753995) B6753995
theorem B3001775 : Blo 1999435 3001775 := bstep (se 1 (by rfl) ⟨2251331, by rfl⟩ : syracuseStep 3001775 = 4502663) B4502663
theorem B2001183 : Blo 1999435 2001183 := bstep (se 1 (by rfl) ⟨1500887, by rfl⟩ : syracuseStep 2001183 = 3001775) B3001775
theorem B3001781 : Blo 1999435 3001781 := bbase (se 5 (by rfl) ⟨140708, by rfl⟩ : syracuseStep 3001781 = 281417) (by norm_num)
theorem B2001187 : Blo 1999435 2001187 := bstep (se 1 (by rfl) ⟨1500890, by rfl⟩ : syracuseStep 2001187 = 3001781) B3001781
theorem B5065517 : Blo 1999435 5065517 := bbase (se 3 (by rfl) ⟨949784, by rfl⟩ : syracuseStep 5065517 = 1899569) (by norm_num)
theorem B3377011 : Blo 1999435 3377011 := bstep (se 1 (by rfl) ⟨2532758, by rfl⟩ : syracuseStep 3377011 = 5065517) B5065517
theorem B4502681 : Blo 1999435 4502681 := bstep (se 2 (by rfl) ⟨1688505, by rfl⟩ : syracuseStep 4502681 = 3377011) B3377011
theorem B3001787 : Blo 1999435 3001787 := bstep (se 1 (by rfl) ⟨2251340, by rfl⟩ : syracuseStep 3001787 = 4502681) B4502681
theorem B2001191 : Blo 1999435 2001191 := bstep (se 1 (by rfl) ⟨1500893, by rfl⟩ : syracuseStep 2001191 = 3001787) B3001787
theorem B2251345 : Blo 1999435 2251345 := bbase (se 2 (by rfl) ⟨844254, by rfl⟩ : syracuseStep 2251345 = 1688509) (by norm_num)
theorem B3001793 : Blo 1999435 3001793 := bstep (se 2 (by rfl) ⟨1125672, by rfl⟩ : syracuseStep 3001793 = 2251345) B2251345
theorem B2001195 : Blo 1999435 2001195 := bstep (se 1 (by rfl) ⟨1500896, by rfl⟩ : syracuseStep 2001195 = 3001793) B3001793
theorem B2849365 : Blo 1999435 2849365 := bbase (se 8 (by rfl) ⟨16695, by rfl⟩ : syracuseStep 2849365 = 33391) (by norm_num)
theorem B3799153 : Blo 1999435 3799153 := bstep (se 2 (by rfl) ⟨1424682, by rfl⟩ : syracuseStep 3799153 = 2849365) B2849365
theorem B5065537 : Blo 1999435 5065537 := bstep (se 2 (by rfl) ⟨1899576, by rfl⟩ : syracuseStep 5065537 = 3799153) B3799153
theorem B6754049 : Blo 1999435 6754049 := bstep (se 2 (by rfl) ⟨2532768, by rfl⟩ : syracuseStep 6754049 = 5065537) B5065537
theorem B4502699 : Blo 1999435 4502699 := bstep (se 1 (by rfl) ⟨3377024, by rfl⟩ : syracuseStep 4502699 = 6754049) B6754049
theorem B3001799 : Blo 1999435 3001799 := bstep (se 1 (by rfl) ⟨2251349, by rfl⟩ : syracuseStep 3001799 = 4502699) B4502699
theorem B2001199 : Blo 1999435 2001199 := bstep (se 1 (by rfl) ⟨1500899, by rfl⟩ : syracuseStep 2001199 = 3001799) B3001799
theorem B3001805 : Blo 1999435 3001805 := bbase (se 3 (by rfl) ⟨562838, by rfl⟩ : syracuseStep 3001805 = 1125677) (by norm_num)
theorem B2001203 : Blo 1999435 2001203 := bstep (se 1 (by rfl) ⟨1500902, by rfl⟩ : syracuseStep 2001203 = 3001805) B3001805
theorem B4502717 : Blo 1999435 4502717 := bbase (se 3 (by rfl) ⟨844259, by rfl⟩ : syracuseStep 4502717 = 1688519) (by norm_num)
theorem B3001811 : Blo 1999435 3001811 := bstep (se 1 (by rfl) ⟨2251358, by rfl⟩ : syracuseStep 3001811 = 4502717) B4502717
theorem B2001207 : Blo 1999435 2001207 := bstep (se 1 (by rfl) ⟨1500905, by rfl⟩ : syracuseStep 2001207 = 3001811) B3001811
theorem B3377045 : Blo 1999435 3377045 := bbase (se 6 (by rfl) ⟨79149, by rfl⟩ : syracuseStep 3377045 = 158299) (by norm_num)
theorem B2251363 : Blo 1999435 2251363 := bstep (se 1 (by rfl) ⟨1688522, by rfl⟩ : syracuseStep 2251363 = 3377045) B3377045
theorem B3001817 : Blo 1999435 3001817 := bstep (se 2 (by rfl) ⟨1125681, by rfl⟩ : syracuseStep 3001817 = 2251363) B2251363
theorem B2001211 : Blo 1999435 2001211 := bstep (se 1 (by rfl) ⟨1500908, by rfl⟩ : syracuseStep 2001211 = 3001817) B3001817
theorem B2704693 : Blo 1999435 2704693 := bbase (se 5 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 2704693 = 253565) (by norm_num)
theorem B3606257 : Blo 1999435 3606257 := bstep (se 2 (by rfl) ⟨1352346, by rfl⟩ : syracuseStep 3606257 = 2704693) B2704693
theorem B2404171 : Blo 1999435 2404171 := bstep (se 1 (by rfl) ⟨1803128, by rfl⟩ : syracuseStep 2404171 = 3606257) B3606257
theorem B12822245 : Blo 1999435 12822245 := bstep (se 4 (by rfl) ⟨1202085, by rfl⟩ : syracuseStep 12822245 = 2404171) B2404171
theorem B8548163 : Blo 1999435 8548163 := bstep (se 1 (by rfl) ⟨6411122, by rfl⟩ : syracuseStep 8548163 = 12822245) B12822245
theorem B5698775 : Blo 1999435 5698775 := bstep (se 1 (by rfl) ⟨4274081, by rfl⟩ : syracuseStep 5698775 = 8548163) B8548163
theorem B15196733 : Blo 1999435 15196733 := bstep (se 3 (by rfl) ⟨2849387, by rfl⟩ : syracuseStep 15196733 = 5698775) B5698775
theorem B10131155 : Blo 1999435 10131155 := bstep (se 1 (by rfl) ⟨7598366, by rfl⟩ : syracuseStep 10131155 = 15196733) B15196733
theorem B6754103 : Blo 1999435 6754103 := bstep (se 1 (by rfl) ⟨5065577, by rfl⟩ : syracuseStep 6754103 = 10131155) B10131155
theorem B4502735 : Blo 1999435 4502735 := bstep (se 1 (by rfl) ⟨3377051, by rfl⟩ : syracuseStep 4502735 = 6754103) B6754103
theorem B3001823 : Blo 1999435 3001823 := bstep (se 1 (by rfl) ⟨2251367, by rfl⟩ : syracuseStep 3001823 = 4502735) B4502735
theorem B2001215 : Blo 1999435 2001215 := bstep (se 1 (by rfl) ⟨1500911, by rfl⟩ : syracuseStep 2001215 = 3001823) B3001823
theorem B3001829 : Blo 1999435 3001829 := bbase (se 4 (by rfl) ⟨281421, by rfl⟩ : syracuseStep 3001829 = 562843) (by norm_num)
theorem B2001219 : Blo 1999435 2001219 := bstep (se 1 (by rfl) ⟨1500914, by rfl⟩ : syracuseStep 2001219 = 3001829) B3001829
theorem B9379157 : Blo 1999435 9379157 := bbase (se 11 (by rfl) ⟨6869, by rfl⟩ : syracuseStep 9379157 = 13739) (by norm_num)
theorem B25011085 : Blo 1999435 25011085 := bstep (se 3 (by rfl) ⟨4689578, by rfl⟩ : syracuseStep 25011085 = 9379157) B9379157
theorem B2134279253 : Blo 1999435 2134279253 := bstep (se 8 (by rfl) ⟨12505542, by rfl⟩ : syracuseStep 2134279253 = 25011085) B25011085
theorem B5691411341 : Blo 1999435 5691411341 := bstep (se 3 (by rfl) ⟨1067139626, by rfl⟩ : syracuseStep 5691411341 = 2134279253) B2134279253
theorem B3794274227 : Blo 1999435 3794274227 := bstep (se 1 (by rfl) ⟨2845705670, by rfl⟩ : syracuseStep 3794274227 = 5691411341) B5691411341
theorem B2529516151 : Blo 1999435 2529516151 := bstep (se 1 (by rfl) ⟨1897137113, by rfl⟩ : syracuseStep 2529516151 = 3794274227) B3794274227
theorem B3372688201 : Blo 1999435 3372688201 := bstep (se 2 (by rfl) ⟨1264758075, by rfl⟩ : syracuseStep 3372688201 = 2529516151) B2529516151
theorem B4496917601 : Blo 1999435 4496917601 := bstep (se 2 (by rfl) ⟨1686344100, by rfl⟩ : syracuseStep 4496917601 = 3372688201) B3372688201
theorem B2997945067 : Blo 1999435 2997945067 := bstep (se 1 (by rfl) ⟨2248458800, by rfl⟩ : syracuseStep 2997945067 = 4496917601) B4496917601
theorem B3997260089 : Blo 1999435 3997260089 := bstep (se 2 (by rfl) ⟨1498972533, by rfl⟩ : syracuseStep 3997260089 = 2997945067) B2997945067
theorem B2664840059 : Blo 1999435 2664840059 := bstep (se 1 (by rfl) ⟨1998630044, by rfl⟩ : syracuseStep 2664840059 = 3997260089) B3997260089
theorem B1776560039 : Blo 1999435 1776560039 := bstep (se 1 (by rfl) ⟨1332420029, by rfl⟩ : syracuseStep 1776560039 = 2664840059) B2664840059
theorem B1184373359 : Blo 1999435 1184373359 := bstep (se 1 (by rfl) ⟨888280019, by rfl⟩ : syracuseStep 1184373359 = 1776560039) B1776560039
theorem B789582239 : Blo 1999435 789582239 := bstep (se 1 (by rfl) ⟨592186679, by rfl⟩ : syracuseStep 789582239 = 1184373359) B1184373359
theorem B526388159 : Blo 1999435 526388159 := bstep (se 1 (by rfl) ⟨394791119, by rfl⟩ : syracuseStep 526388159 = 789582239) B789582239
theorem B1403701757 : Blo 1999435 1403701757 := bstep (se 3 (by rfl) ⟨263194079, by rfl⟩ : syracuseStep 1403701757 = 526388159) B526388159
theorem B935801171 : Blo 1999435 935801171 := bstep (se 1 (by rfl) ⟨701850878, by rfl⟩ : syracuseStep 935801171 = 1403701757) B1403701757
theorem B623867447 : Blo 1999435 623867447 := bstep (se 1 (by rfl) ⟨467900585, by rfl⟩ : syracuseStep 623867447 = 935801171) B935801171
theorem B415911631 : Blo 1999435 415911631 := bstep (se 1 (by rfl) ⟨311933723, by rfl⟩ : syracuseStep 415911631 = 623867447) B623867447
theorem B554548841 : Blo 1999435 554548841 := bstep (se 2 (by rfl) ⟨207955815, by rfl⟩ : syracuseStep 554548841 = 415911631) B415911631
theorem B369699227 : Blo 1999435 369699227 := bstep (se 1 (by rfl) ⟨277274420, by rfl⟩ : syracuseStep 369699227 = 554548841) B554548841
theorem B246466151 : Blo 1999435 246466151 := bstep (se 1 (by rfl) ⟨184849613, by rfl⟩ : syracuseStep 246466151 = 369699227) B369699227
theorem B164310767 : Blo 1999435 164310767 := bstep (se 1 (by rfl) ⟨123233075, by rfl⟩ : syracuseStep 164310767 = 246466151) B246466151
theorem B109540511 : Blo 1999435 109540511 := bstep (se 1 (by rfl) ⟨82155383, by rfl⟩ : syracuseStep 109540511 = 164310767) B164310767
theorem B73027007 : Blo 1999435 73027007 := bstep (se 1 (by rfl) ⟨54770255, by rfl⟩ : syracuseStep 73027007 = 109540511) B109540511
theorem B48684671 : Blo 1999435 48684671 := bstep (se 1 (by rfl) ⟨36513503, by rfl⟩ : syracuseStep 48684671 = 73027007) B73027007
theorem B32456447 : Blo 1999435 32456447 := bstep (se 1 (by rfl) ⟨24342335, by rfl⟩ : syracuseStep 32456447 = 48684671) B48684671
theorem B21637631 : Blo 1999435 21637631 := bstep (se 1 (by rfl) ⟨16228223, by rfl⟩ : syracuseStep 21637631 = 32456447) B32456447
theorem B14425087 : Blo 1999435 14425087 := bstep (se 1 (by rfl) ⟨10818815, by rfl⟩ : syracuseStep 14425087 = 21637631) B21637631
theorem B19233449 : Blo 1999435 19233449 := bstep (se 2 (by rfl) ⟨7212543, by rfl⟩ : syracuseStep 19233449 = 14425087) B14425087
theorem B12822299 : Blo 1999435 12822299 := bstep (se 1 (by rfl) ⟨9616724, by rfl⟩ : syracuseStep 12822299 = 19233449) B19233449
theorem B8548199 : Blo 1999435 8548199 := bstep (se 1 (by rfl) ⟨6411149, by rfl⟩ : syracuseStep 8548199 = 12822299) B12822299
theorem B5698799 : Blo 1999435 5698799 := bstep (se 1 (by rfl) ⟨4274099, by rfl⟩ : syracuseStep 5698799 = 8548199) B8548199
theorem B3799199 : Blo 1999435 3799199 := bstep (se 1 (by rfl) ⟨2849399, by rfl⟩ : syracuseStep 3799199 = 5698799) B5698799
theorem B2532799 : Blo 1999435 2532799 := bstep (se 1 (by rfl) ⟨1899599, by rfl⟩ : syracuseStep 2532799 = 3799199) B3799199
theorem B3377065 : Blo 1999435 3377065 := bstep (se 2 (by rfl) ⟨1266399, by rfl⟩ : syracuseStep 3377065 = 2532799) B2532799
theorem B4502753 : Blo 1999435 4502753 := bstep (se 2 (by rfl) ⟨1688532, by rfl⟩ : syracuseStep 4502753 = 3377065) B3377065
theorem B3001835 : Blo 1999435 3001835 := bstep (se 1 (by rfl) ⟨2251376, by rfl⟩ : syracuseStep 3001835 = 4502753) B4502753
theorem B2001223 : Blo 1999435 2001223 := bstep (se 1 (by rfl) ⟨1500917, by rfl⟩ : syracuseStep 2001223 = 3001835) B3001835
theorem B2251381 : Blo 1999435 2251381 := bbase (se 5 (by rfl) ⟨105533, by rfl⟩ : syracuseStep 2251381 = 211067) (by norm_num)
theorem B3001841 : Blo 1999435 3001841 := bstep (se 2 (by rfl) ⟨1125690, by rfl⟩ : syracuseStep 3001841 = 2251381) B2251381
theorem B2001227 : Blo 1999435 2001227 := bstep (se 1 (by rfl) ⟨1500920, by rfl⟩ : syracuseStep 2001227 = 3001841) B3001841
theorem B2532809 : Blo 1999435 2532809 := bbase (se 2 (by rfl) ⟨949803, by rfl⟩ : syracuseStep 2532809 = 1899607) (by norm_num)
theorem B6754157 : Blo 1999435 6754157 := bstep (se 3 (by rfl) ⟨1266404, by rfl⟩ : syracuseStep 6754157 = 2532809) B2532809
theorem B4502771 : Blo 1999435 4502771 := bstep (se 1 (by rfl) ⟨3377078, by rfl⟩ : syracuseStep 4502771 = 6754157) B6754157
theorem B3001847 : Blo 1999435 3001847 := bstep (se 1 (by rfl) ⟨2251385, by rfl⟩ : syracuseStep 3001847 = 4502771) B4502771
theorem B2001231 : Blo 1999435 2001231 := bstep (se 1 (by rfl) ⟨1500923, by rfl⟩ : syracuseStep 2001231 = 3001847) B3001847
theorem B3001853 : Blo 1999435 3001853 := bbase (se 3 (by rfl) ⟨562847, by rfl⟩ : syracuseStep 3001853 = 1125695) (by norm_num)
theorem B2001235 : Blo 1999435 2001235 := bstep (se 1 (by rfl) ⟨1500926, by rfl⟩ : syracuseStep 2001235 = 3001853) B3001853
theorem B4502789 : Blo 1999435 4502789 := bbase (se 4 (by rfl) ⟨422136, by rfl⟩ : syracuseStep 4502789 = 844273) (by norm_num)
theorem B3001859 : Blo 1999435 3001859 := bstep (se 1 (by rfl) ⟨2251394, by rfl⟩ : syracuseStep 3001859 = 4502789) B4502789
theorem B2001239 : Blo 1999435 2001239 := bstep (se 1 (by rfl) ⟨1500929, by rfl⟩ : syracuseStep 2001239 = 3001859) B3001859
theorem B3799237 : Blo 1999435 3799237 := bbase (se 4 (by rfl) ⟨356178, by rfl⟩ : syracuseStep 3799237 = 712357) (by norm_num)
theorem B5065649 : Blo 1999435 5065649 := bstep (se 2 (by rfl) ⟨1899618, by rfl⟩ : syracuseStep 5065649 = 3799237) B3799237
theorem B3377099 : Blo 1999435 3377099 := bstep (se 1 (by rfl) ⟨2532824, by rfl⟩ : syracuseStep 3377099 = 5065649) B5065649
theorem B2251399 : Blo 1999435 2251399 := bstep (se 1 (by rfl) ⟨1688549, by rfl⟩ : syracuseStep 2251399 = 3377099) B3377099
theorem B3001865 : Blo 1999435 3001865 := bstep (se 2 (by rfl) ⟨1125699, by rfl⟩ : syracuseStep 3001865 = 2251399) B2251399
theorem B2001243 : Blo 1999435 2001243 := bstep (se 1 (by rfl) ⟨1500932, by rfl⟩ : syracuseStep 2001243 = 3001865) B3001865
theorem B10131317 : Blo 1999435 10131317 := bbase (se 5 (by rfl) ⟨474905, by rfl⟩ : syracuseStep 10131317 = 949811) (by norm_num)
theorem B6754211 : Blo 1999435 6754211 := bstep (se 1 (by rfl) ⟨5065658, by rfl⟩ : syracuseStep 6754211 = 10131317) B10131317
theorem B4502807 : Blo 1999435 4502807 := bstep (se 1 (by rfl) ⟨3377105, by rfl⟩ : syracuseStep 4502807 = 6754211) B6754211
theorem B3001871 : Blo 1999435 3001871 := bstep (se 1 (by rfl) ⟨2251403, by rfl⟩ : syracuseStep 3001871 = 4502807) B4502807
theorem B2001247 : Blo 1999435 2001247 := bstep (se 1 (by rfl) ⟨1500935, by rfl⟩ : syracuseStep 2001247 = 3001871) B3001871
theorem B3001877 : Blo 1999435 3001877 := bbase (se 6 (by rfl) ⟨70356, by rfl⟩ : syracuseStep 3001877 = 140713) (by norm_num)
theorem B2001251 : Blo 1999435 2001251 := bstep (se 1 (by rfl) ⟨1500938, by rfl⟩ : syracuseStep 2001251 = 3001877) B3001877
theorem B3423197 : Blo 1999435 3423197 := bbase (se 3 (by rfl) ⟨641849, by rfl⟩ : syracuseStep 3423197 = 1283699) (by norm_num)
theorem B2282131 : Blo 1999435 2282131 := bstep (se 1 (by rfl) ⟨1711598, by rfl⟩ : syracuseStep 2282131 = 3423197) B3423197
theorem B3042841 : Blo 1999435 3042841 := bstep (se 2 (by rfl) ⟨1141065, by rfl⟩ : syracuseStep 3042841 = 2282131) B2282131
theorem B4057121 : Blo 1999435 4057121 := bstep (se 2 (by rfl) ⟨1521420, by rfl⟩ : syracuseStep 4057121 = 3042841) B3042841
theorem B2704747 : Blo 1999435 2704747 := bstep (se 1 (by rfl) ⟨2028560, by rfl⟩ : syracuseStep 2704747 = 4057121) B4057121
theorem B3606329 : Blo 1999435 3606329 := bstep (se 2 (by rfl) ⟨1352373, by rfl⟩ : syracuseStep 3606329 = 2704747) B2704747
theorem B9616877 : Blo 1999435 9616877 := bstep (se 3 (by rfl) ⟨1803164, by rfl⟩ : syracuseStep 9616877 = 3606329) B3606329
theorem B6411251 : Blo 1999435 6411251 := bstep (se 1 (by rfl) ⟨4808438, by rfl⟩ : syracuseStep 6411251 = 9616877) B9616877
theorem B17096669 : Blo 1999435 17096669 := bstep (se 3 (by rfl) ⟨3205625, by rfl⟩ : syracuseStep 17096669 = 6411251) B6411251
theorem B11397779 : Blo 1999435 11397779 := bstep (se 1 (by rfl) ⟨8548334, by rfl⟩ : syracuseStep 11397779 = 17096669) B17096669
theorem B7598519 : Blo 1999435 7598519 := bstep (se 1 (by rfl) ⟨5698889, by rfl⟩ : syracuseStep 7598519 = 11397779) B11397779
theorem B5065679 : Blo 1999435 5065679 := bstep (se 1 (by rfl) ⟨3799259, by rfl⟩ : syracuseStep 5065679 = 7598519) B7598519
theorem B3377119 : Blo 1999435 3377119 := bstep (se 1 (by rfl) ⟨2532839, by rfl⟩ : syracuseStep 3377119 = 5065679) B5065679
theorem B4502825 : Blo 1999435 4502825 := bstep (se 2 (by rfl) ⟨1688559, by rfl⟩ : syracuseStep 4502825 = 3377119) B3377119
theorem B3001883 : Blo 1999435 3001883 := bstep (se 1 (by rfl) ⟨2251412, by rfl⟩ : syracuseStep 3001883 = 4502825) B4502825
theorem B2001255 : Blo 1999435 2001255 := bstep (se 1 (by rfl) ⟨1500941, by rfl⟩ : syracuseStep 2001255 = 3001883) B3001883
theorem B2251417 : Blo 1999435 2251417 := bbase (se 2 (by rfl) ⟨844281, by rfl⟩ : syracuseStep 2251417 = 1688563) (by norm_num)
theorem B3001889 : Blo 1999435 3001889 := bstep (se 2 (by rfl) ⟨1125708, by rfl⟩ : syracuseStep 3001889 = 2251417) B2251417
theorem B2001259 : Blo 1999435 2001259 := bstep (se 1 (by rfl) ⟨1500944, by rfl⟩ : syracuseStep 2001259 = 3001889) B3001889
theorem B7598549 : Blo 1999435 7598549 := bbase (se 7 (by rfl) ⟨89045, by rfl⟩ : syracuseStep 7598549 = 178091) (by norm_num)
theorem B5065699 : Blo 1999435 5065699 := bstep (se 1 (by rfl) ⟨3799274, by rfl⟩ : syracuseStep 5065699 = 7598549) B7598549
theorem B6754265 : Blo 1999435 6754265 := bstep (se 2 (by rfl) ⟨2532849, by rfl⟩ : syracuseStep 6754265 = 5065699) B5065699
theorem B4502843 : Blo 1999435 4502843 := bstep (se 1 (by rfl) ⟨3377132, by rfl⟩ : syracuseStep 4502843 = 6754265) B6754265
theorem B3001895 : Blo 1999435 3001895 := bstep (se 1 (by rfl) ⟨2251421, by rfl⟩ : syracuseStep 3001895 = 4502843) B4502843
theorem B2001263 : Blo 1999435 2001263 := bstep (se 1 (by rfl) ⟨1500947, by rfl⟩ : syracuseStep 2001263 = 3001895) B3001895
theorem B3001901 : Blo 1999435 3001901 := bbase (se 3 (by rfl) ⟨562856, by rfl⟩ : syracuseStep 3001901 = 1125713) (by norm_num)
theorem B2001267 : Blo 1999435 2001267 := bstep (se 1 (by rfl) ⟨1500950, by rfl⟩ : syracuseStep 2001267 = 3001901) B3001901
theorem B4502861 : Blo 1999435 4502861 := bbase (se 3 (by rfl) ⟨844286, by rfl⟩ : syracuseStep 4502861 = 1688573) (by norm_num)
theorem B3001907 : Blo 1999435 3001907 := bstep (se 1 (by rfl) ⟨2251430, by rfl⟩ : syracuseStep 3001907 = 4502861) B4502861
theorem B2001271 : Blo 1999435 2001271 := bstep (se 1 (by rfl) ⟨1500953, by rfl⟩ : syracuseStep 2001271 = 3001907) B3001907
theorem B2532865 : Blo 1999435 2532865 := bbase (se 2 (by rfl) ⟨949824, by rfl⟩ : syracuseStep 2532865 = 1899649) (by norm_num)
theorem B3377153 : Blo 1999435 3377153 := bstep (se 2 (by rfl) ⟨1266432, by rfl⟩ : syracuseStep 3377153 = 2532865) B2532865
theorem B2251435 : Blo 1999435 2251435 := bstep (se 1 (by rfl) ⟨1688576, by rfl⟩ : syracuseStep 2251435 = 3377153) B3377153
theorem B3001913 : Blo 1999435 3001913 := bstep (se 2 (by rfl) ⟨1125717, by rfl⟩ : syracuseStep 3001913 = 2251435) B2251435
theorem B2001275 : Blo 1999435 2001275 := bstep (se 1 (by rfl) ⟨1500956, by rfl⟩ : syracuseStep 2001275 = 3001913) B3001913
theorem B2137109 : Blo 1999435 2137109 := bbase (se 6 (by rfl) ⟨50088, by rfl⟩ : syracuseStep 2137109 = 100177) (by norm_num)
theorem B22795829 : Blo 1999435 22795829 := bstep (se 5 (by rfl) ⟨1068554, by rfl⟩ : syracuseStep 22795829 = 2137109) B2137109
theorem B15197219 : Blo 1999435 15197219 := bstep (se 1 (by rfl) ⟨11397914, by rfl⟩ : syracuseStep 15197219 = 22795829) B22795829
theorem B10131479 : Blo 1999435 10131479 := bstep (se 1 (by rfl) ⟨7598609, by rfl⟩ : syracuseStep 10131479 = 15197219) B15197219
theorem B6754319 : Blo 1999435 6754319 := bstep (se 1 (by rfl) ⟨5065739, by rfl⟩ : syracuseStep 6754319 = 10131479) B10131479
theorem B4502879 : Blo 1999435 4502879 := bstep (se 1 (by rfl) ⟨3377159, by rfl⟩ : syracuseStep 4502879 = 6754319) B6754319
theorem B3001919 : Blo 1999435 3001919 := bstep (se 1 (by rfl) ⟨2251439, by rfl⟩ : syracuseStep 3001919 = 4502879) B4502879
theorem B2001279 : Blo 1999435 2001279 := bstep (se 1 (by rfl) ⟨1500959, by rfl⟩ : syracuseStep 2001279 = 3001919) B3001919
theorem B3001925 : Blo 1999435 3001925 := bbase (se 4 (by rfl) ⟨281430, by rfl⟩ : syracuseStep 3001925 = 562861) (by norm_num)
theorem B2001283 : Blo 1999435 2001283 := bstep (se 1 (by rfl) ⟨1500962, by rfl⟩ : syracuseStep 2001283 = 3001925) B3001925
theorem B3377173 : Blo 1999435 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B4502897 : Blo 1999435 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B3001931 : Blo 1999435 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B2001287 : Blo 1999435 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B2251453 : Blo 1999435 2251453 := bbase (se 3 (by rfl) ⟨422147, by rfl⟩ : syracuseStep 2251453 = 844295) (by norm_num)
theorem B3001937 : Blo 1999435 3001937 := bstep (se 2 (by rfl) ⟨1125726, by rfl⟩ : syracuseStep 3001937 = 2251453) B2251453
theorem B2001291 : Blo 1999435 2001291 := bstep (se 1 (by rfl) ⟨1500968, by rfl⟩ : syracuseStep 2001291 = 3001937) B3001937
theorem B6754373 : Blo 1999435 6754373 := bbase (se 4 (by rfl) ⟨633222, by rfl⟩ : syracuseStep 6754373 = 1266445) (by norm_num)
theorem B4502915 : Blo 1999435 4502915 := bstep (se 1 (by rfl) ⟨3377186, by rfl⟩ : syracuseStep 4502915 = 6754373) B6754373
theorem B3001943 : Blo 1999435 3001943 := bstep (se 1 (by rfl) ⟨2251457, by rfl⟩ : syracuseStep 3001943 = 4502915) B4502915
theorem B2001295 : Blo 1999435 2001295 := bstep (se 1 (by rfl) ⟨1500971, by rfl⟩ : syracuseStep 2001295 = 3001943) B3001943
theorem B3001949 : Blo 1999435 3001949 := bbase (se 3 (by rfl) ⟨562865, by rfl⟩ : syracuseStep 3001949 = 1125731) (by norm_num)
theorem B2001299 : Blo 1999435 2001299 := bstep (se 1 (by rfl) ⟨1500974, by rfl⟩ : syracuseStep 2001299 = 3001949) B3001949
theorem B4502933 : Blo 1999435 4502933 := bbase (se 6 (by rfl) ⟨105537, by rfl⟩ : syracuseStep 4502933 = 211075) (by norm_num)
theorem B3001955 : Blo 1999435 3001955 := bstep (se 1 (by rfl) ⟨2251466, by rfl⟩ : syracuseStep 3001955 = 4502933) B4502933
theorem B2001303 : Blo 1999435 2001303 := bstep (se 1 (by rfl) ⟨1500977, by rfl⟩ : syracuseStep 2001303 = 3001955) B3001955
theorem B13693141 : Blo 1999435 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B18257521 : Blo 1999435 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B24343361 : Blo 1999435 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B16228907 : Blo 1999435 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B10819271 : Blo 1999435 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B7212847 : Blo 1999435 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B9617129 : Blo 1999435 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B6411419 : Blo 1999435 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B4274279 : Blo 1999435 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B2849519 : Blo 1999435 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B7598717 : Blo 1999435 7598717 := bstep (se 3 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 7598717 = 2849519) B2849519
theorem B5065811 : Blo 1999435 5065811 := bstep (se 1 (by rfl) ⟨3799358, by rfl⟩ : syracuseStep 5065811 = 7598717) B7598717
theorem B3377207 : Blo 1999435 3377207 := bstep (se 1 (by rfl) ⟨2532905, by rfl⟩ : syracuseStep 3377207 = 5065811) B5065811
theorem B2251471 : Blo 1999435 2251471 := bstep (se 1 (by rfl) ⟨1688603, by rfl⟩ : syracuseStep 2251471 = 3377207) B3377207
theorem B3001961 : Blo 1999435 3001961 := bstep (se 2 (by rfl) ⟨1125735, by rfl⟩ : syracuseStep 3001961 = 2251471) B2251471
theorem B2001307 : Blo 1999435 2001307 := bstep (se 1 (by rfl) ⟨1500980, by rfl⟩ : syracuseStep 2001307 = 3001961) B3001961
theorem B4808573 : Blo 1999435 4808573 := bbase (se 3 (by rfl) ⟨901607, by rfl⟩ : syracuseStep 4808573 = 1803215) (by norm_num)
theorem B3205715 : Blo 1999435 3205715 := bstep (se 1 (by rfl) ⟨2404286, by rfl⟩ : syracuseStep 3205715 = 4808573) B4808573
theorem B8548573 : Blo 1999435 8548573 := bstep (se 3 (by rfl) ⟨1602857, by rfl⟩ : syracuseStep 8548573 = 3205715) B3205715
theorem B11398097 : Blo 1999435 11398097 := bstep (se 2 (by rfl) ⟨4274286, by rfl⟩ : syracuseStep 11398097 = 8548573) B8548573
theorem B7598731 : Blo 1999435 7598731 := bstep (se 1 (by rfl) ⟨5699048, by rfl⟩ : syracuseStep 7598731 = 11398097) B11398097
theorem B10131641 : Blo 1999435 10131641 := bstep (se 2 (by rfl) ⟨3799365, by rfl⟩ : syracuseStep 10131641 = 7598731) B7598731
theorem B6754427 : Blo 1999435 6754427 := bstep (se 1 (by rfl) ⟨5065820, by rfl⟩ : syracuseStep 6754427 = 10131641) B10131641
theorem B4502951 : Blo 1999435 4502951 := bstep (se 1 (by rfl) ⟨3377213, by rfl⟩ : syracuseStep 4502951 = 6754427) B6754427
theorem B3001967 : Blo 1999435 3001967 := bstep (se 1 (by rfl) ⟨2251475, by rfl⟩ : syracuseStep 3001967 = 4502951) B4502951
theorem B2001311 : Blo 1999435 2001311 := bstep (se 1 (by rfl) ⟨1500983, by rfl⟩ : syracuseStep 2001311 = 3001967) B3001967
theorem B3001973 : Blo 1999435 3001973 := bbase (se 5 (by rfl) ⟨140717, by rfl⟩ : syracuseStep 3001973 = 281435) (by norm_num)
theorem B2001315 : Blo 1999435 2001315 := bstep (se 1 (by rfl) ⟨1500986, by rfl⟩ : syracuseStep 2001315 = 3001973) B3001973
theorem B3799381 : Blo 1999435 3799381 := bbase (se 10 (by rfl) ⟨5565, by rfl⟩ : syracuseStep 3799381 = 11131) (by norm_num)
theorem B5065841 : Blo 1999435 5065841 := bstep (se 2 (by rfl) ⟨1899690, by rfl⟩ : syracuseStep 5065841 = 3799381) B3799381
theorem B3377227 : Blo 1999435 3377227 := bstep (se 1 (by rfl) ⟨2532920, by rfl⟩ : syracuseStep 3377227 = 5065841) B5065841
theorem B4502969 : Blo 1999435 4502969 := bstep (se 2 (by rfl) ⟨1688613, by rfl⟩ : syracuseStep 4502969 = 3377227) B3377227
theorem B3001979 : Blo 1999435 3001979 := bstep (se 1 (by rfl) ⟨2251484, by rfl⟩ : syracuseStep 3001979 = 4502969) B4502969
theorem B2001319 : Blo 1999435 2001319 := bstep (se 1 (by rfl) ⟨1500989, by rfl⟩ : syracuseStep 2001319 = 3001979) B3001979
theorem B2251489 : Blo 1999435 2251489 := bbase (se 2 (by rfl) ⟨844308, by rfl⟩ : syracuseStep 2251489 = 1688617) (by norm_num)
theorem B3001985 : Blo 1999435 3001985 := bstep (se 2 (by rfl) ⟨1125744, by rfl⟩ : syracuseStep 3001985 = 2251489) B2251489
theorem B2001323 : Blo 1999435 2001323 := bstep (se 1 (by rfl) ⟨1500992, by rfl⟩ : syracuseStep 2001323 = 3001985) B3001985
theorem B5065861 : Blo 1999435 5065861 := bbase (se 4 (by rfl) ⟨474924, by rfl⟩ : syracuseStep 5065861 = 949849) (by norm_num)
theorem B6754481 : Blo 1999435 6754481 := bstep (se 2 (by rfl) ⟨2532930, by rfl⟩ : syracuseStep 6754481 = 5065861) B5065861
theorem B4502987 : Blo 1999435 4502987 := bstep (se 1 (by rfl) ⟨3377240, by rfl⟩ : syracuseStep 4502987 = 6754481) B6754481
theorem B3001991 : Blo 1999435 3001991 := bstep (se 1 (by rfl) ⟨2251493, by rfl⟩ : syracuseStep 3001991 = 4502987) B4502987
theorem B2001327 : Blo 1999435 2001327 := bstep (se 1 (by rfl) ⟨1500995, by rfl⟩ : syracuseStep 2001327 = 3001991) B3001991
theorem B3001997 : Blo 1999435 3001997 := bbase (se 3 (by rfl) ⟨562874, by rfl⟩ : syracuseStep 3001997 = 1125749) (by norm_num)
theorem B2001331 : Blo 1999435 2001331 := bstep (se 1 (by rfl) ⟨1500998, by rfl⟩ : syracuseStep 2001331 = 3001997) B3001997
theorem B4503005 : Blo 1999435 4503005 := bbase (se 3 (by rfl) ⟨844313, by rfl⟩ : syracuseStep 4503005 = 1688627) (by norm_num)
theorem B3002003 : Blo 1999435 3002003 := bstep (se 1 (by rfl) ⟨2251502, by rfl⟩ : syracuseStep 3002003 = 4503005) B4503005
theorem B2001335 : Blo 1999435 2001335 := bstep (se 1 (by rfl) ⟨1501001, by rfl⟩ : syracuseStep 2001335 = 3002003) B3002003
theorem B3377261 : Blo 1999435 3377261 := bbase (se 3 (by rfl) ⟨633236, by rfl⟩ : syracuseStep 3377261 = 1266473) (by norm_num)
theorem B2251507 : Blo 1999435 2251507 := bstep (se 1 (by rfl) ⟨1688630, by rfl⟩ : syracuseStep 2251507 = 3377261) B3377261
theorem B3002009 : Blo 1999435 3002009 := bstep (se 2 (by rfl) ⟨1125753, by rfl⟩ : syracuseStep 3002009 = 2251507) B2251507
theorem B2001339 : Blo 1999435 2001339 := bstep (se 1 (by rfl) ⟨1501004, by rfl⟩ : syracuseStep 2001339 = 3002009) B3002009
theorem B8114597 : Blo 1999435 8114597 := bbase (se 4 (by rfl) ⟨760743, by rfl⟩ : syracuseStep 8114597 = 1521487) (by norm_num)
theorem B5409731 : Blo 1999435 5409731 := bstep (se 1 (by rfl) ⟨4057298, by rfl⟩ : syracuseStep 5409731 = 8114597) B8114597
theorem B3606487 : Blo 1999435 3606487 := bstep (se 1 (by rfl) ⟨2704865, by rfl⟩ : syracuseStep 3606487 = 5409731) B5409731
theorem B19234597 : Blo 1999435 19234597 := bstep (se 4 (by rfl) ⟨1803243, by rfl⟩ : syracuseStep 19234597 = 3606487) B3606487
theorem B25646129 : Blo 1999435 25646129 := bstep (se 2 (by rfl) ⟨9617298, by rfl⟩ : syracuseStep 25646129 = 19234597) B19234597
theorem B17097419 : Blo 1999435 17097419 := bstep (se 1 (by rfl) ⟨12823064, by rfl⟩ : syracuseStep 17097419 = 25646129) B25646129
theorem B11398279 : Blo 1999435 11398279 := bstep (se 1 (by rfl) ⟨8548709, by rfl⟩ : syracuseStep 11398279 = 17097419) B17097419
theorem B15197705 : Blo 1999435 15197705 := bstep (se 2 (by rfl) ⟨5699139, by rfl⟩ : syracuseStep 15197705 = 11398279) B11398279
theorem B10131803 : Blo 1999435 10131803 := bstep (se 1 (by rfl) ⟨7598852, by rfl⟩ : syracuseStep 10131803 = 15197705) B15197705
theorem B6754535 : Blo 1999435 6754535 := bstep (se 1 (by rfl) ⟨5065901, by rfl⟩ : syracuseStep 6754535 = 10131803) B10131803
theorem B4503023 : Blo 1999435 4503023 := bstep (se 1 (by rfl) ⟨3377267, by rfl⟩ : syracuseStep 4503023 = 6754535) B6754535
theorem B3002015 : Blo 1999435 3002015 := bstep (se 1 (by rfl) ⟨2251511, by rfl⟩ : syracuseStep 3002015 = 4503023) B4503023
theorem B2001343 : Blo 1999435 2001343 := bstep (se 1 (by rfl) ⟨1501007, by rfl⟩ : syracuseStep 2001343 = 3002015) B3002015
theorem B3002021 : Blo 1999435 3002021 := bbase (se 4 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 3002021 = 562879) (by norm_num)
theorem B2001347 : Blo 1999435 2001347 := bstep (se 1 (by rfl) ⟨1501010, by rfl⟩ : syracuseStep 2001347 = 3002021) B3002021
theorem B2532961 : Blo 1999435 2532961 := bbase (se 2 (by rfl) ⟨949860, by rfl⟩ : syracuseStep 2532961 = 1899721) (by norm_num)
theorem B3377281 : Blo 1999435 3377281 := bstep (se 2 (by rfl) ⟨1266480, by rfl⟩ : syracuseStep 3377281 = 2532961) B2532961
theorem B4503041 : Blo 1999435 4503041 := bstep (se 2 (by rfl) ⟨1688640, by rfl⟩ : syracuseStep 4503041 = 3377281) B3377281
theorem B3002027 : Blo 1999435 3002027 := bstep (se 1 (by rfl) ⟨2251520, by rfl⟩ : syracuseStep 3002027 = 4503041) B4503041
theorem B2001351 : Blo 1999435 2001351 := bstep (se 1 (by rfl) ⟨1501013, by rfl⟩ : syracuseStep 2001351 = 3002027) B3002027
theorem B2251525 : Blo 1999435 2251525 := bbase (se 4 (by rfl) ⟨211080, by rfl⟩ : syracuseStep 2251525 = 422161) (by norm_num)
theorem B3002033 : Blo 1999435 3002033 := bstep (se 2 (by rfl) ⟨1125762, by rfl⟩ : syracuseStep 3002033 = 2251525) B2251525
theorem B2001355 : Blo 1999435 2001355 := bstep (se 1 (by rfl) ⟨1501016, by rfl⟩ : syracuseStep 2001355 = 3002033) B3002033
theorem B2404345 : Blo 1999435 2404345 := bbase (se 2 (by rfl) ⟨901629, by rfl⟩ : syracuseStep 2404345 = 1803259) (by norm_num)
theorem B3205793 : Blo 1999435 3205793 := bstep (se 2 (by rfl) ⟨1202172, by rfl⟩ : syracuseStep 3205793 = 2404345) B2404345
theorem B2137195 : Blo 1999435 2137195 := bstep (se 1 (by rfl) ⟨1602896, by rfl⟩ : syracuseStep 2137195 = 3205793) B3205793
theorem B2849593 : Blo 1999435 2849593 := bstep (se 2 (by rfl) ⟨1068597, by rfl⟩ : syracuseStep 2849593 = 2137195) B2137195
theorem B3799457 : Blo 1999435 3799457 := bstep (se 2 (by rfl) ⟨1424796, by rfl⟩ : syracuseStep 3799457 = 2849593) B2849593
theorem B2532971 : Blo 1999435 2532971 := bstep (se 1 (by rfl) ⟨1899728, by rfl⟩ : syracuseStep 2532971 = 3799457) B3799457
theorem B6754589 : Blo 1999435 6754589 := bstep (se 3 (by rfl) ⟨1266485, by rfl⟩ : syracuseStep 6754589 = 2532971) B2532971
theorem B4503059 : Blo 1999435 4503059 := bstep (se 1 (by rfl) ⟨3377294, by rfl⟩ : syracuseStep 4503059 = 6754589) B6754589
theorem B3002039 : Blo 1999435 3002039 := bstep (se 1 (by rfl) ⟨2251529, by rfl⟩ : syracuseStep 3002039 = 4503059) B4503059
theorem B2001359 : Blo 1999435 2001359 := bstep (se 1 (by rfl) ⟨1501019, by rfl⟩ : syracuseStep 2001359 = 3002039) B3002039
theorem B3002045 : Blo 1999435 3002045 := bbase (se 3 (by rfl) ⟨562883, by rfl⟩ : syracuseStep 3002045 = 1125767) (by norm_num)
theorem B2001363 : Blo 1999435 2001363 := bstep (se 1 (by rfl) ⟨1501022, by rfl⟩ : syracuseStep 2001363 = 3002045) B3002045
theorem B4503077 : Blo 1999435 4503077 := bbase (se 4 (by rfl) ⟨422163, by rfl⟩ : syracuseStep 4503077 = 844327) (by norm_num)
theorem B3002051 : Blo 1999435 3002051 := bstep (se 1 (by rfl) ⟨2251538, by rfl⟩ : syracuseStep 3002051 = 4503077) B4503077
theorem B2001367 : Blo 1999435 2001367 := bstep (se 1 (by rfl) ⟨1501025, by rfl⟩ : syracuseStep 2001367 = 3002051) B3002051
theorem B5065973 : Blo 1999435 5065973 := bbase (se 5 (by rfl) ⟨237467, by rfl⟩ : syracuseStep 5065973 = 474935) (by norm_num)
theorem B3377315 : Blo 1999435 3377315 := bstep (se 1 (by rfl) ⟨2532986, by rfl⟩ : syracuseStep 3377315 = 5065973) B5065973
theorem B2251543 : Blo 1999435 2251543 := bstep (se 1 (by rfl) ⟨1688657, by rfl⟩ : syracuseStep 2251543 = 3377315) B3377315
theorem B3002057 : Blo 1999435 3002057 := bstep (se 2 (by rfl) ⟨1125771, by rfl⟩ : syracuseStep 3002057 = 2251543) B2251543
theorem B2001371 : Blo 1999435 2001371 := bstep (se 1 (by rfl) ⟨1501028, by rfl⟩ : syracuseStep 2001371 = 3002057) B3002057
theorem B17330965 : Blo 1999435 17330965 := bbase (se 6 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 17330965 = 812389) (by norm_num)
theorem B92431813 : Blo 1999435 92431813 := bstep (se 4 (by rfl) ⟨8665482, by rfl⟩ : syracuseStep 92431813 = 17330965) B17330965
theorem B123242417 : Blo 1999435 123242417 := bstep (se 2 (by rfl) ⟨46215906, by rfl⟩ : syracuseStep 123242417 = 92431813) B92431813
theorem B82161611 : Blo 1999435 82161611 := bstep (se 1 (by rfl) ⟨61621208, by rfl⟩ : syracuseStep 82161611 = 123242417) B123242417
theorem B54774407 : Blo 1999435 54774407 := bstep (se 1 (by rfl) ⟨41080805, by rfl⟩ : syracuseStep 54774407 = 82161611) B82161611
theorem B36516271 : Blo 1999435 36516271 := bstep (se 1 (by rfl) ⟨27387203, by rfl⟩ : syracuseStep 36516271 = 54774407) B54774407
theorem B48688361 : Blo 1999435 48688361 := bstep (se 2 (by rfl) ⟨18258135, by rfl⟩ : syracuseStep 48688361 = 36516271) B36516271
theorem B32458907 : Blo 1999435 32458907 := bstep (se 1 (by rfl) ⟨24344180, by rfl⟩ : syracuseStep 32458907 = 48688361) B48688361
theorem B21639271 : Blo 1999435 21639271 := bstep (se 1 (by rfl) ⟨16229453, by rfl⟩ : syracuseStep 21639271 = 32458907) B32458907
theorem B28852361 : Blo 1999435 28852361 := bstep (se 2 (by rfl) ⟨10819635, by rfl⟩ : syracuseStep 28852361 = 21639271) B21639271
theorem B19234907 : Blo 1999435 19234907 := bstep (se 1 (by rfl) ⟨14426180, by rfl⟩ : syracuseStep 19234907 = 28852361) B28852361
theorem B12823271 : Blo 1999435 12823271 := bstep (se 1 (by rfl) ⟨9617453, by rfl⟩ : syracuseStep 12823271 = 19234907) B19234907
theorem B8548847 : Blo 1999435 8548847 := bstep (se 1 (by rfl) ⟨6411635, by rfl⟩ : syracuseStep 8548847 = 12823271) B12823271
theorem B5699231 : Blo 1999435 5699231 := bstep (se 1 (by rfl) ⟨4274423, by rfl⟩ : syracuseStep 5699231 = 8548847) B8548847
theorem B3799487 : Blo 1999435 3799487 := bstep (se 1 (by rfl) ⟨2849615, by rfl⟩ : syracuseStep 3799487 = 5699231) B5699231
theorem B10131965 : Blo 1999435 10131965 := bstep (se 3 (by rfl) ⟨1899743, by rfl⟩ : syracuseStep 10131965 = 3799487) B3799487
theorem B6754643 : Blo 1999435 6754643 := bstep (se 1 (by rfl) ⟨5065982, by rfl⟩ : syracuseStep 6754643 = 10131965) B10131965
theorem B4503095 : Blo 1999435 4503095 := bstep (se 1 (by rfl) ⟨3377321, by rfl⟩ : syracuseStep 4503095 = 6754643) B6754643
theorem B3002063 : Blo 1999435 3002063 := bstep (se 1 (by rfl) ⟨2251547, by rfl⟩ : syracuseStep 3002063 = 4503095) B4503095
theorem B2001375 : Blo 1999435 2001375 := bstep (se 1 (by rfl) ⟨1501031, by rfl⟩ : syracuseStep 2001375 = 3002063) B3002063
theorem B3002069 : Blo 1999435 3002069 := bbase (se 7 (by rfl) ⟨35180, by rfl⟩ : syracuseStep 3002069 = 70361) (by norm_num)
theorem B2001379 : Blo 1999435 2001379 := bstep (se 1 (by rfl) ⟨1501034, by rfl⟩ : syracuseStep 2001379 = 3002069) B3002069
theorem B4057381 : Blo 1999435 4057381 := bbase (se 4 (by rfl) ⟨380379, by rfl⟩ : syracuseStep 4057381 = 760759) (by norm_num)
theorem B5409841 : Blo 1999435 5409841 := bstep (se 2 (by rfl) ⟨2028690, by rfl⟩ : syracuseStep 5409841 = 4057381) B4057381
theorem B7213121 : Blo 1999435 7213121 := bstep (se 2 (by rfl) ⟨2704920, by rfl⟩ : syracuseStep 7213121 = 5409841) B5409841
theorem B4808747 : Blo 1999435 4808747 := bstep (se 1 (by rfl) ⟨3606560, by rfl⟩ : syracuseStep 4808747 = 7213121) B7213121
theorem B3205831 : Blo 1999435 3205831 := bstep (se 1 (by rfl) ⟨2404373, by rfl⟩ : syracuseStep 3205831 = 4808747) B4808747
theorem B4274441 : Blo 1999435 4274441 := bstep (se 2 (by rfl) ⟨1602915, by rfl⟩ : syracuseStep 4274441 = 3205831) B3205831
theorem B2849627 : Blo 1999435 2849627 := bstep (se 1 (by rfl) ⟨2137220, by rfl⟩ : syracuseStep 2849627 = 4274441) B4274441
theorem B7599005 : Blo 1999435 7599005 := bstep (se 3 (by rfl) ⟨1424813, by rfl⟩ : syracuseStep 7599005 = 2849627) B2849627
theorem B5066003 : Blo 1999435 5066003 := bstep (se 1 (by rfl) ⟨3799502, by rfl⟩ : syracuseStep 5066003 = 7599005) B7599005
theorem B3377335 : Blo 1999435 3377335 := bstep (se 1 (by rfl) ⟨2533001, by rfl⟩ : syracuseStep 3377335 = 5066003) B5066003
theorem B4503113 : Blo 1999435 4503113 := bstep (se 2 (by rfl) ⟨1688667, by rfl⟩ : syracuseStep 4503113 = 3377335) B3377335
theorem B3002075 : Blo 1999435 3002075 := bstep (se 1 (by rfl) ⟨2251556, by rfl⟩ : syracuseStep 3002075 = 4503113) B4503113
theorem B2001383 : Blo 1999435 2001383 := bstep (se 1 (by rfl) ⟨1501037, by rfl⟩ : syracuseStep 2001383 = 3002075) B3002075
theorem B2251561 : Blo 1999435 2251561 := bbase (se 2 (by rfl) ⟨844335, by rfl⟩ : syracuseStep 2251561 = 1688671) (by norm_num)
theorem B3002081 : Blo 1999435 3002081 := bstep (se 2 (by rfl) ⟨1125780, by rfl⟩ : syracuseStep 3002081 = 2251561) B2251561
theorem B2001387 : Blo 1999435 2001387 := bstep (se 1 (by rfl) ⟨1501040, by rfl⟩ : syracuseStep 2001387 = 3002081) B3002081
theorem B4808765 : Blo 1999435 4808765 := bbase (se 3 (by rfl) ⟨901643, by rfl⟩ : syracuseStep 4808765 = 1803287) (by norm_num)
theorem B12823373 : Blo 1999435 12823373 := bstep (se 3 (by rfl) ⟨2404382, by rfl⟩ : syracuseStep 12823373 = 4808765) B4808765
theorem B8548915 : Blo 1999435 8548915 := bstep (se 1 (by rfl) ⟨6411686, by rfl⟩ : syracuseStep 8548915 = 12823373) B12823373
theorem B11398553 : Blo 1999435 11398553 := bstep (se 2 (by rfl) ⟨4274457, by rfl⟩ : syracuseStep 11398553 = 8548915) B8548915
theorem B7599035 : Blo 1999435 7599035 := bstep (se 1 (by rfl) ⟨5699276, by rfl⟩ : syracuseStep 7599035 = 11398553) B11398553
theorem B5066023 : Blo 1999435 5066023 := bstep (se 1 (by rfl) ⟨3799517, by rfl⟩ : syracuseStep 5066023 = 7599035) B7599035
theorem B6754697 : Blo 1999435 6754697 := bstep (se 2 (by rfl) ⟨2533011, by rfl⟩ : syracuseStep 6754697 = 5066023) B5066023
theorem B4503131 : Blo 1999435 4503131 := bstep (se 1 (by rfl) ⟨3377348, by rfl⟩ : syracuseStep 4503131 = 6754697) B6754697
theorem B3002087 : Blo 1999435 3002087 := bstep (se 1 (by rfl) ⟨2251565, by rfl⟩ : syracuseStep 3002087 = 4503131) B4503131
theorem B2001391 : Blo 1999435 2001391 := bstep (se 1 (by rfl) ⟨1501043, by rfl⟩ : syracuseStep 2001391 = 3002087) B3002087
theorem B3002093 : Blo 1999435 3002093 := bbase (se 3 (by rfl) ⟨562892, by rfl⟩ : syracuseStep 3002093 = 1125785) (by norm_num)
theorem B2001395 : Blo 1999435 2001395 := bstep (se 1 (by rfl) ⟨1501046, by rfl⟩ : syracuseStep 2001395 = 3002093) B3002093
theorem B4503149 : Blo 1999435 4503149 := bbase (se 3 (by rfl) ⟨844340, by rfl⟩ : syracuseStep 4503149 = 1688681) (by norm_num)
theorem B3002099 : Blo 1999435 3002099 := bstep (se 1 (by rfl) ⟨2251574, by rfl⟩ : syracuseStep 3002099 = 4503149) B4503149
theorem B2001399 : Blo 1999435 2001399 := bstep (se 1 (by rfl) ⟨1501049, by rfl⟩ : syracuseStep 2001399 = 3002099) B3002099
theorem B3799541 : Blo 1999435 3799541 := bbase (se 5 (by rfl) ⟨178103, by rfl⟩ : syracuseStep 3799541 = 356207) (by norm_num)
theorem B2533027 : Blo 1999435 2533027 := bstep (se 1 (by rfl) ⟨1899770, by rfl⟩ : syracuseStep 2533027 = 3799541) B3799541
theorem B3377369 : Blo 1999435 3377369 := bstep (se 2 (by rfl) ⟨1266513, by rfl⟩ : syracuseStep 3377369 = 2533027) B2533027
theorem B2251579 : Blo 1999435 2251579 := bstep (se 1 (by rfl) ⟨1688684, by rfl⟩ : syracuseStep 2251579 = 3377369) B3377369
theorem B3002105 : Blo 1999435 3002105 := bstep (se 2 (by rfl) ⟨1125789, by rfl⟩ : syracuseStep 3002105 = 2251579) B2251579
theorem B2001403 : Blo 1999435 2001403 := bstep (se 1 (by rfl) ⟨1501052, by rfl⟩ : syracuseStep 2001403 = 3002105) B3002105
theorem B6940325 : Blo 1999435 6940325 := bbase (se 4 (by rfl) ⟨650655, by rfl⟩ : syracuseStep 6940325 = 1301311) (by norm_num)
theorem B18507533 : Blo 1999435 18507533 := bstep (se 3 (by rfl) ⟨3470162, by rfl⟩ : syracuseStep 18507533 = 6940325) B6940325
theorem B49353421 : Blo 1999435 49353421 := bstep (se 3 (by rfl) ⟨9253766, by rfl⟩ : syracuseStep 49353421 = 18507533) B18507533
theorem B65804561 : Blo 1999435 65804561 := bstep (se 2 (by rfl) ⟨24676710, by rfl⟩ : syracuseStep 65804561 = 49353421) B49353421
theorem B43869707 : Blo 1999435 43869707 := bstep (se 1 (by rfl) ⟨32902280, by rfl⟩ : syracuseStep 43869707 = 65804561) B65804561
theorem B29246471 : Blo 1999435 29246471 := bstep (se 1 (by rfl) ⟨21934853, by rfl⟩ : syracuseStep 29246471 = 43869707) B43869707
theorem B19497647 : Blo 1999435 19497647 := bstep (se 1 (by rfl) ⟨14623235, by rfl⟩ : syracuseStep 19497647 = 29246471) B29246471
theorem B12998431 : Blo 1999435 12998431 := bstep (se 1 (by rfl) ⟨9748823, by rfl⟩ : syracuseStep 12998431 = 19497647) B19497647
theorem B17331241 : Blo 1999435 17331241 := bstep (se 2 (by rfl) ⟨6499215, by rfl⟩ : syracuseStep 17331241 = 12998431) B12998431
theorem B23108321 : Blo 1999435 23108321 := bstep (se 2 (by rfl) ⟨8665620, by rfl⟩ : syracuseStep 23108321 = 17331241) B17331241
theorem B15405547 : Blo 1999435 15405547 := bstep (se 1 (by rfl) ⟨11554160, by rfl⟩ : syracuseStep 15405547 = 23108321) B23108321
theorem B20540729 : Blo 1999435 20540729 := bstep (se 2 (by rfl) ⟨7702773, by rfl⟩ : syracuseStep 20540729 = 15405547) B15405547
theorem B13693819 : Blo 1999435 13693819 := bstep (se 1 (by rfl) ⟨10270364, by rfl⟩ : syracuseStep 13693819 = 20540729) B20540729
theorem B18258425 : Blo 1999435 18258425 := bstep (se 2 (by rfl) ⟨6846909, by rfl⟩ : syracuseStep 18258425 = 13693819) B13693819
theorem B12172283 : Blo 1999435 12172283 := bstep (se 1 (by rfl) ⟨9129212, by rfl⟩ : syracuseStep 12172283 = 18258425) B18258425
theorem B8114855 : Blo 1999435 8114855 := bstep (se 1 (by rfl) ⟨6086141, by rfl⟩ : syracuseStep 8114855 = 12172283) B12172283
theorem B86558453 : Blo 1999435 86558453 := bstep (se 5 (by rfl) ⟨4057427, by rfl⟩ : syracuseStep 86558453 = 8114855) B8114855
theorem B57705635 : Blo 1999435 57705635 := bstep (se 1 (by rfl) ⟨43279226, by rfl⟩ : syracuseStep 57705635 = 86558453) B86558453
theorem B38470423 : Blo 1999435 38470423 := bstep (se 1 (by rfl) ⟨28852817, by rfl⟩ : syracuseStep 38470423 = 57705635) B57705635
theorem B51293897 : Blo 1999435 51293897 := bstep (se 2 (by rfl) ⟨19235211, by rfl⟩ : syracuseStep 51293897 = 38470423) B38470423
theorem B34195931 : Blo 1999435 34195931 := bstep (se 1 (by rfl) ⟨25646948, by rfl⟩ : syracuseStep 34195931 = 51293897) B51293897
theorem B22797287 : Blo 1999435 22797287 := bstep (se 1 (by rfl) ⟨17097965, by rfl⟩ : syracuseStep 22797287 = 34195931) B34195931
theorem B15198191 : Blo 1999435 15198191 := bstep (se 1 (by rfl) ⟨11398643, by rfl⟩ : syracuseStep 15198191 = 22797287) B22797287
theorem B10132127 : Blo 1999435 10132127 := bstep (se 1 (by rfl) ⟨7599095, by rfl⟩ : syracuseStep 10132127 = 15198191) B15198191
theorem B6754751 : Blo 1999435 6754751 := bstep (se 1 (by rfl) ⟨5066063, by rfl⟩ : syracuseStep 6754751 = 10132127) B10132127
theorem B4503167 : Blo 1999435 4503167 := bstep (se 1 (by rfl) ⟨3377375, by rfl⟩ : syracuseStep 4503167 = 6754751) B6754751
theorem B3002111 : Blo 1999435 3002111 := bstep (se 1 (by rfl) ⟨2251583, by rfl⟩ : syracuseStep 3002111 = 4503167) B4503167
theorem B2001407 : Blo 1999435 2001407 := bstep (se 1 (by rfl) ⟨1501055, by rfl⟩ : syracuseStep 2001407 = 3002111) B3002111
theorem B3002117 : Blo 1999435 3002117 := bbase (se 4 (by rfl) ⟨281448, by rfl⟩ : syracuseStep 3002117 = 562897) (by norm_num)
theorem B2001411 : Blo 1999435 2001411 := bstep (se 1 (by rfl) ⟨1501058, by rfl⟩ : syracuseStep 2001411 = 3002117) B3002117
theorem B3377389 : Blo 1999435 3377389 := bbase (se 3 (by rfl) ⟨633260, by rfl⟩ : syracuseStep 3377389 = 1266521) (by norm_num)
theorem B4503185 : Blo 1999435 4503185 := bstep (se 2 (by rfl) ⟨1688694, by rfl⟩ : syracuseStep 4503185 = 3377389) B3377389
theorem B3002123 : Blo 1999435 3002123 := bstep (se 1 (by rfl) ⟨2251592, by rfl⟩ : syracuseStep 3002123 = 4503185) B4503185
theorem B2001415 : Blo 1999435 2001415 := bstep (se 1 (by rfl) ⟨1501061, by rfl⟩ : syracuseStep 2001415 = 3002123) B3002123
theorem B2251597 : Blo 1999435 2251597 := bbase (se 3 (by rfl) ⟨422174, by rfl⟩ : syracuseStep 2251597 = 844349) (by norm_num)
theorem B3002129 : Blo 1999435 3002129 := bstep (se 2 (by rfl) ⟨1125798, by rfl⟩ : syracuseStep 3002129 = 2251597) B2251597
theorem B2001419 : Blo 1999435 2001419 := bstep (se 1 (by rfl) ⟨1501064, by rfl⟩ : syracuseStep 2001419 = 3002129) B3002129
theorem B6754805 : Blo 1999435 6754805 := bbase (se 5 (by rfl) ⟨316631, by rfl⟩ : syracuseStep 6754805 = 633263) (by norm_num)
theorem B4503203 : Blo 1999435 4503203 := bstep (se 1 (by rfl) ⟨3377402, by rfl⟩ : syracuseStep 4503203 = 6754805) B6754805
theorem B3002135 : Blo 1999435 3002135 := bstep (se 1 (by rfl) ⟨2251601, by rfl⟩ : syracuseStep 3002135 = 4503203) B4503203
theorem B2001423 : Blo 1999435 2001423 := bstep (se 1 (by rfl) ⟨1501067, by rfl⟩ : syracuseStep 2001423 = 3002135) B3002135
theorem B3002141 : Blo 1999435 3002141 := bbase (se 3 (by rfl) ⟨562901, by rfl⟩ : syracuseStep 3002141 = 1125803) (by norm_num)
theorem B2001427 : Blo 1999435 2001427 := bstep (se 1 (by rfl) ⟨1501070, by rfl⟩ : syracuseStep 2001427 = 3002141) B3002141
theorem B4503221 : Blo 1999435 4503221 := bbase (se 5 (by rfl) ⟨211088, by rfl⟩ : syracuseStep 4503221 = 422177) (by norm_num)
theorem B3002147 : Blo 1999435 3002147 := bstep (se 1 (by rfl) ⟨2251610, by rfl⟩ : syracuseStep 3002147 = 4503221) B4503221
theorem B2001431 : Blo 1999435 2001431 := bstep (se 1 (by rfl) ⟨1501073, by rfl⟩ : syracuseStep 2001431 = 3002147) B3002147
theorem B11398805 : Blo 1999435 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B7599203 : Blo 1999435 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B5066135 : Blo 1999435 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B3377423 : Blo 1999435 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B2251615 : Blo 1999435 2251615 := bstep (se 1 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 2251615 = 3377423) B3377423
theorem B3002153 : Blo 1999435 3002153 := bstep (se 2 (by rfl) ⟨1125807, by rfl⟩ : syracuseStep 3002153 = 2251615) B2251615
theorem B2001435 : Blo 1999435 2001435 := bstep (se 1 (by rfl) ⟨1501076, by rfl⟩ : syracuseStep 2001435 = 3002153) B3002153
theorem C0 (j : ℕ) (h1 : 499858 ≤ j) (h2 : j ≤ 500358) : Blo 1999435 (4 * j + 3) := by
  interval_cases j
  · exact B1999435
  · exact B1999439
  · exact B1999443
  · exact B1999447
  · exact B1999451
  · exact B1999455
  · exact B1999459
  · exact B1999463
  · exact B1999467
  · exact B1999471
  · exact B1999475
  · exact B1999479
  · exact B1999483
  · exact B1999487
  · exact B1999491
  · exact B1999495
  · exact B1999499
  · exact B1999503
  · exact B1999507
  · exact B1999511
  · exact B1999515
  · exact B1999519
  · exact B1999523
  · exact B1999527
  · exact B1999531
  · exact B1999535
  · exact B1999539
  · exact B1999543
  · exact B1999547
  · exact B1999551
  · exact B1999555
  · exact B1999559
  · exact B1999563
  · exact B1999567
  · exact B1999571
  · exact B1999575
  · exact B1999579
  · exact B1999583
  · exact B1999587
  · exact B1999591
  · exact B1999595
  · exact B1999599
  · exact B1999603
  · exact B1999607
  · exact B1999611
  · exact B1999615
  · exact B1999619
  · exact B1999623
  · exact B1999627
  · exact B1999631
  · exact B1999635
  · exact B1999639
  · exact B1999643
  · exact B1999647
  · exact B1999651
  · exact B1999655
  · exact B1999659
  · exact B1999663
  · exact B1999667
  · exact B1999671
  · exact B1999675
  · exact B1999679
  · exact B1999683
  · exact B1999687
  · exact B1999691
  · exact B1999695
  · exact B1999699
  · exact B1999703
  · exact B1999707
  · exact B1999711
  · exact B1999715
  · exact B1999719
  · exact B1999723
  · exact B1999727
  · exact B1999731
  · exact B1999735
  · exact B1999739
  · exact B1999743
  · exact B1999747
  · exact B1999751
  · exact B1999755
  · exact B1999759
  · exact B1999763
  · exact B1999767
  · exact B1999771
  · exact B1999775
  · exact B1999779
  · exact B1999783
  · exact B1999787
  · exact B1999791
  · exact B1999795
  · exact B1999799
  · exact B1999803
  · exact B1999807
  · exact B1999811
  · exact B1999815
  · exact B1999819
  · exact B1999823
  · exact B1999827
  · exact B1999831
  · exact B1999835
  · exact B1999839
  · exact B1999843
  · exact B1999847
  · exact B1999851
  · exact B1999855
  · exact B1999859
  · exact B1999863
  · exact B1999867
  · exact B1999871
  · exact B1999875
  · exact B1999879
  · exact B1999883
  · exact B1999887
  · exact B1999891
  · exact B1999895
  · exact B1999899
  · exact B1999903
  · exact B1999907
  · exact B1999911
  · exact B1999915
  · exact B1999919
  · exact B1999923
  · exact B1999927
  · exact B1999931
  · exact B1999935
  · exact B1999939
  · exact B1999943
  · exact B1999947
  · exact B1999951
  · exact B1999955
  · exact B1999959
  · exact B1999963
  · exact B1999967
  · exact B1999971
  · exact B1999975
  · exact B1999979
  · exact B1999983
  · exact B1999987
  · exact B1999991
  · exact B1999995
  · exact B1999999
  · exact B2000003
  · exact B2000007
  · exact B2000011
  · exact B2000015
  · exact B2000019
  · exact B2000023
  · exact B2000027
  · exact B2000031
  · exact B2000035
  · exact B2000039
  · exact B2000043
  · exact B2000047
  · exact B2000051
  · exact B2000055
  · exact B2000059
  · exact B2000063
  · exact B2000067
  · exact B2000071
  · exact B2000075
  · exact B2000079
  · exact B2000083
  · exact B2000087
  · exact B2000091
  · exact B2000095
  · exact B2000099
  · exact B2000103
  · exact B2000107
  · exact B2000111
  · exact B2000115
  · exact B2000119
  · exact B2000123
  · exact B2000127
  · exact B2000131
  · exact B2000135
  · exact B2000139
  · exact B2000143
  · exact B2000147
  · exact B2000151
  · exact B2000155
  · exact B2000159
  · exact B2000163
  · exact B2000167
  · exact B2000171
  · exact B2000175
  · exact B2000179
  · exact B2000183
  · exact B2000187
  · exact B2000191
  · exact B2000195
  · exact B2000199
  · exact B2000203
  · exact B2000207
  · exact B2000211
  · exact B2000215
  · exact B2000219
  · exact B2000223
  · exact B2000227
  · exact B2000231
  · exact B2000235
  · exact B2000239
  · exact B2000243
  · exact B2000247
  · exact B2000251
  · exact B2000255
  · exact B2000259
  · exact B2000263
  · exact B2000267
  · exact B2000271
  · exact B2000275
  · exact B2000279
  · exact B2000283
  · exact B2000287
  · exact B2000291
  · exact B2000295
  · exact B2000299
  · exact B2000303
  · exact B2000307
  · exact B2000311
  · exact B2000315
  · exact B2000319
  · exact B2000323
  · exact B2000327
  · exact B2000331
  · exact B2000335
  · exact B2000339
  · exact B2000343
  · exact B2000347
  · exact B2000351
  · exact B2000355
  · exact B2000359
  · exact B2000363
  · exact B2000367
  · exact B2000371
  · exact B2000375
  · exact B2000379
  · exact B2000383
  · exact B2000387
  · exact B2000391
  · exact B2000395
  · exact B2000399
  · exact B2000403
  · exact B2000407
  · exact B2000411
  · exact B2000415
  · exact B2000419
  · exact B2000423
  · exact B2000427
  · exact B2000431
  · exact B2000435
  · exact B2000439
  · exact B2000443
  · exact B2000447
  · exact B2000451
  · exact B2000455
  · exact B2000459
  · exact B2000463
  · exact B2000467
  · exact B2000471
  · exact B2000475
  · exact B2000479
  · exact B2000483
  · exact B2000487
  · exact B2000491
  · exact B2000495
  · exact B2000499
  · exact B2000503
  · exact B2000507
  · exact B2000511
  · exact B2000515
  · exact B2000519
  · exact B2000523
  · exact B2000527
  · exact B2000531
  · exact B2000535
  · exact B2000539
  · exact B2000543
  · exact B2000547
  · exact B2000551
  · exact B2000555
  · exact B2000559
  · exact B2000563
  · exact B2000567
  · exact B2000571
  · exact B2000575
  · exact B2000579
  · exact B2000583
  · exact B2000587
  · exact B2000591
  · exact B2000595
  · exact B2000599
  · exact B2000603
  · exact B2000607
  · exact B2000611
  · exact B2000615
  · exact B2000619
  · exact B2000623
  · exact B2000627
  · exact B2000631
  · exact B2000635
  · exact B2000639
  · exact B2000643
  · exact B2000647
  · exact B2000651
  · exact B2000655
  · exact B2000659
  · exact B2000663
  · exact B2000667
  · exact B2000671
  · exact B2000675
  · exact B2000679
  · exact B2000683
  · exact B2000687
  · exact B2000691
  · exact B2000695
  · exact B2000699
  · exact B2000703
  · exact B2000707
  · exact B2000711
  · exact B2000715
  · exact B2000719
  · exact B2000723
  · exact B2000727
  · exact B2000731
  · exact B2000735
  · exact B2000739
  · exact B2000743
  · exact B2000747
  · exact B2000751
  · exact B2000755
  · exact B2000759
  · exact B2000763
  · exact B2000767
  · exact B2000771
  · exact B2000775
  · exact B2000779
  · exact B2000783
  · exact B2000787
  · exact B2000791
  · exact B2000795
  · exact B2000799
  · exact B2000803
  · exact B2000807
  · exact B2000811
  · exact B2000815
  · exact B2000819
  · exact B2000823
  · exact B2000827
  · exact B2000831
  · exact B2000835
  · exact B2000839
  · exact B2000843
  · exact B2000847
  · exact B2000851
  · exact B2000855
  · exact B2000859
  · exact B2000863
  · exact B2000867
  · exact B2000871
  · exact B2000875
  · exact B2000879
  · exact B2000883
  · exact B2000887
  · exact B2000891
  · exact B2000895
  · exact B2000899
  · exact B2000903
  · exact B2000907
  · exact B2000911
  · exact B2000915
  · exact B2000919
  · exact B2000923
  · exact B2000927
  · exact B2000931
  · exact B2000935
  · exact B2000939
  · exact B2000943
  · exact B2000947
  · exact B2000951
  · exact B2000955
  · exact B2000959
  · exact B2000963
  · exact B2000967
  · exact B2000971
  · exact B2000975
  · exact B2000979
  · exact B2000983
  · exact B2000987
  · exact B2000991
  · exact B2000995
  · exact B2000999
  · exact B2001003
  · exact B2001007
  · exact B2001011
  · exact B2001015
  · exact B2001019
  · exact B2001023
  · exact B2001027
  · exact B2001031
  · exact B2001035
  · exact B2001039
  · exact B2001043
  · exact B2001047
  · exact B2001051
  · exact B2001055
  · exact B2001059
  · exact B2001063
  · exact B2001067
  · exact B2001071
  · exact B2001075
  · exact B2001079
  · exact B2001083
  · exact B2001087
  · exact B2001091
  · exact B2001095
  · exact B2001099
  · exact B2001103
  · exact B2001107
  · exact B2001111
  · exact B2001115
  · exact B2001119
  · exact B2001123
  · exact B2001127
  · exact B2001131
  · exact B2001135
  · exact B2001139
  · exact B2001143
  · exact B2001147
  · exact B2001151
  · exact B2001155
  · exact B2001159
  · exact B2001163
  · exact B2001167
  · exact B2001171
  · exact B2001175
  · exact B2001179
  · exact B2001183
  · exact B2001187
  · exact B2001191
  · exact B2001195
  · exact B2001199
  · exact B2001203
  · exact B2001207
  · exact B2001211
  · exact B2001215
  · exact B2001219
  · exact B2001223
  · exact B2001227
  · exact B2001231
  · exact B2001235
  · exact B2001239
  · exact B2001243
  · exact B2001247
  · exact B2001251
  · exact B2001255
  · exact B2001259
  · exact B2001263
  · exact B2001267
  · exact B2001271
  · exact B2001275
  · exact B2001279
  · exact B2001283
  · exact B2001287
  · exact B2001291
  · exact B2001295
  · exact B2001299
  · exact B2001303
  · exact B2001307
  · exact B2001311
  · exact B2001315
  · exact B2001319
  · exact B2001323
  · exact B2001327
  · exact B2001331
  · exact B2001335
  · exact B2001339
  · exact B2001343
  · exact B2001347
  · exact B2001351
  · exact B2001355
  · exact B2001359
  · exact B2001363
  · exact B2001367
  · exact B2001371
  · exact B2001375
  · exact B2001379
  · exact B2001383
  · exact B2001387
  · exact B2001391
  · exact B2001395
  · exact B2001399
  · exact B2001403
  · exact B2001407
  · exact B2001411
  · exact B2001415
  · exact B2001419
  · exact B2001423
  · exact B2001427
  · exact B2001431
  · exact B2001435
theorem solution (m : ℕ) (hlo : 1999435 ≤ m) (hhi : m ≤ 2001435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 499858 ≤ j := by omega
    have hj2 : j ≤ 500358 := by omega
    have hb : Blo 1999435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
