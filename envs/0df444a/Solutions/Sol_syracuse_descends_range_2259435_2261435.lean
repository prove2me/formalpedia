-- Prove2me | solution 1 for syracuse_descends_range_2259435_2261435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:16.130176+00:00
-- url     : https://prove2.me/submissions/31b861d8-98b9-4ed4-bd56-8d49945b0340

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

theorem B2541865 : Blo 2259435 2541865 := bbase (se 2 (by rfl) ⟨953199, by rfl⟩ : syracuseStep 2541865 = 1906399) (by norm_num)
theorem B3389153 : Blo 2259435 3389153 := bstep (se 2 (by rfl) ⟨1270932, by rfl⟩ : syracuseStep 3389153 = 2541865) B2541865
theorem B2259435 : Blo 2259435 2259435 := bstep (se 1 (by rfl) ⟨1694576, by rfl⟩ : syracuseStep 2259435 = 3389153) B3389153
theorem B4580533 : Blo 2259435 4580533 := bbase (se 5 (by rfl) ⟨214712, by rfl⟩ : syracuseStep 4580533 = 429425) (by norm_num)
theorem B24429509 : Blo 2259435 24429509 := bstep (se 4 (by rfl) ⟨2290266, by rfl⟩ : syracuseStep 24429509 = 4580533) B4580533
theorem B16286339 : Blo 2259435 16286339 := bstep (se 1 (by rfl) ⟨12214754, by rfl⟩ : syracuseStep 16286339 = 24429509) B24429509
theorem B10857559 : Blo 2259435 10857559 := bstep (se 1 (by rfl) ⟨8143169, by rfl⟩ : syracuseStep 10857559 = 16286339) B16286339
theorem B14476745 : Blo 2259435 14476745 := bstep (se 2 (by rfl) ⟨5428779, by rfl⟩ : syracuseStep 14476745 = 10857559) B10857559
theorem B9651163 : Blo 2259435 9651163 := bstep (se 1 (by rfl) ⟨7238372, by rfl⟩ : syracuseStep 9651163 = 14476745) B14476745
theorem B12868217 : Blo 2259435 12868217 := bstep (se 2 (by rfl) ⟨4825581, by rfl⟩ : syracuseStep 12868217 = 9651163) B9651163
theorem B8578811 : Blo 2259435 8578811 := bstep (se 1 (by rfl) ⟨6434108, by rfl⟩ : syracuseStep 8578811 = 12868217) B12868217
theorem B5719207 : Blo 2259435 5719207 := bstep (se 1 (by rfl) ⟨4289405, by rfl⟩ : syracuseStep 5719207 = 8578811) B8578811
theorem B7625609 : Blo 2259435 7625609 := bstep (se 2 (by rfl) ⟨2859603, by rfl⟩ : syracuseStep 7625609 = 5719207) B5719207
theorem B5083739 : Blo 2259435 5083739 := bstep (se 1 (by rfl) ⟨3812804, by rfl⟩ : syracuseStep 5083739 = 7625609) B7625609
theorem B3389159 : Blo 2259435 3389159 := bstep (se 1 (by rfl) ⟨2541869, by rfl⟩ : syracuseStep 3389159 = 5083739) B5083739
theorem B2259439 : Blo 2259435 2259439 := bstep (se 1 (by rfl) ⟨1694579, by rfl⟩ : syracuseStep 2259439 = 3389159) B3389159
theorem B3389165 : Blo 2259435 3389165 := bbase (se 3 (by rfl) ⟨635468, by rfl⟩ : syracuseStep 3389165 = 1270937) (by norm_num)
theorem B2259443 : Blo 2259435 2259443 := bstep (se 1 (by rfl) ⟨1694582, by rfl⟩ : syracuseStep 2259443 = 3389165) B3389165
theorem B5083757 : Blo 2259435 5083757 := bbase (se 3 (by rfl) ⟨953204, by rfl⟩ : syracuseStep 5083757 = 1906409) (by norm_num)
theorem B3389171 : Blo 2259435 3389171 := bstep (se 1 (by rfl) ⟨2541878, by rfl⟩ : syracuseStep 3389171 = 5083757) B5083757
theorem B2259447 : Blo 2259435 2259447 := bstep (se 1 (by rfl) ⟨1694585, by rfl⟩ : syracuseStep 2259447 = 3389171) B3389171
theorem B4289429 : Blo 2259435 4289429 := bbase (se 6 (by rfl) ⟨100533, by rfl⟩ : syracuseStep 4289429 = 201067) (by norm_num)
theorem B2859619 : Blo 2259435 2859619 := bstep (se 1 (by rfl) ⟨2144714, by rfl⟩ : syracuseStep 2859619 = 4289429) B4289429
theorem B3812825 : Blo 2259435 3812825 := bstep (se 2 (by rfl) ⟨1429809, by rfl⟩ : syracuseStep 3812825 = 2859619) B2859619
theorem B2541883 : Blo 2259435 2541883 := bstep (se 1 (by rfl) ⟨1906412, by rfl⟩ : syracuseStep 2541883 = 3812825) B3812825
theorem B3389177 : Blo 2259435 3389177 := bstep (se 2 (by rfl) ⟨1270941, by rfl⟩ : syracuseStep 3389177 = 2541883) B2541883
theorem B2259451 : Blo 2259435 2259451 := bstep (se 1 (by rfl) ⟨1694588, by rfl⟩ : syracuseStep 2259451 = 3389177) B3389177
theorem B19565813 : Blo 2259435 19565813 := bbase (se 5 (by rfl) ⟨917147, by rfl⟩ : syracuseStep 19565813 = 1834295) (by norm_num)
theorem B52175501 : Blo 2259435 52175501 := bstep (se 3 (by rfl) ⟨9782906, by rfl⟩ : syracuseStep 52175501 = 19565813) B19565813
theorem B34783667 : Blo 2259435 34783667 := bstep (se 1 (by rfl) ⟨26087750, by rfl⟩ : syracuseStep 34783667 = 52175501) B52175501
theorem B23189111 : Blo 2259435 23189111 := bstep (se 1 (by rfl) ⟨17391833, by rfl⟩ : syracuseStep 23189111 = 34783667) B34783667
theorem B15459407 : Blo 2259435 15459407 := bstep (se 1 (by rfl) ⟨11594555, by rfl⟩ : syracuseStep 15459407 = 23189111) B23189111
theorem B10306271 : Blo 2259435 10306271 := bstep (se 1 (by rfl) ⟨7729703, by rfl⟩ : syracuseStep 10306271 = 15459407) B15459407
theorem B27483389 : Blo 2259435 27483389 := bstep (se 3 (by rfl) ⟨5153135, by rfl⟩ : syracuseStep 27483389 = 10306271) B10306271
theorem B18322259 : Blo 2259435 18322259 := bstep (se 1 (by rfl) ⟨13741694, by rfl⟩ : syracuseStep 18322259 = 27483389) B27483389
theorem B48859357 : Blo 2259435 48859357 := bstep (se 3 (by rfl) ⟨9161129, by rfl⟩ : syracuseStep 48859357 = 18322259) B18322259
theorem B65145809 : Blo 2259435 65145809 := bstep (se 2 (by rfl) ⟨24429678, by rfl⟩ : syracuseStep 65145809 = 48859357) B48859357
theorem B43430539 : Blo 2259435 43430539 := bstep (se 1 (by rfl) ⟨32572904, by rfl⟩ : syracuseStep 43430539 = 65145809) B65145809
theorem B57907385 : Blo 2259435 57907385 := bstep (se 2 (by rfl) ⟨21715269, by rfl⟩ : syracuseStep 57907385 = 43430539) B43430539
theorem B38604923 : Blo 2259435 38604923 := bstep (se 1 (by rfl) ⟨28953692, by rfl⟩ : syracuseStep 38604923 = 57907385) B57907385
theorem B25736615 : Blo 2259435 25736615 := bstep (se 1 (by rfl) ⟨19302461, by rfl⟩ : syracuseStep 25736615 = 38604923) B38604923
theorem B17157743 : Blo 2259435 17157743 := bstep (se 1 (by rfl) ⟨12868307, by rfl⟩ : syracuseStep 17157743 = 25736615) B25736615
theorem B11438495 : Blo 2259435 11438495 := bstep (se 1 (by rfl) ⟨8578871, by rfl⟩ : syracuseStep 11438495 = 17157743) B17157743
theorem B7625663 : Blo 2259435 7625663 := bstep (se 1 (by rfl) ⟨5719247, by rfl⟩ : syracuseStep 7625663 = 11438495) B11438495
theorem B5083775 : Blo 2259435 5083775 := bstep (se 1 (by rfl) ⟨3812831, by rfl⟩ : syracuseStep 5083775 = 7625663) B7625663
theorem B3389183 : Blo 2259435 3389183 := bstep (se 1 (by rfl) ⟨2541887, by rfl⟩ : syracuseStep 3389183 = 5083775) B5083775
theorem B2259455 : Blo 2259435 2259455 := bstep (se 1 (by rfl) ⟨1694591, by rfl⟩ : syracuseStep 2259455 = 3389183) B3389183
theorem B3389189 : Blo 2259435 3389189 := bbase (se 4 (by rfl) ⟨317736, by rfl⟩ : syracuseStep 3389189 = 635473) (by norm_num)
theorem B2259459 : Blo 2259435 2259459 := bstep (se 1 (by rfl) ⟨1694594, by rfl⟩ : syracuseStep 2259459 = 3389189) B3389189
theorem B3812845 : Blo 2259435 3812845 := bbase (se 3 (by rfl) ⟨714908, by rfl⟩ : syracuseStep 3812845 = 1429817) (by norm_num)
theorem B5083793 : Blo 2259435 5083793 := bstep (se 2 (by rfl) ⟨1906422, by rfl⟩ : syracuseStep 5083793 = 3812845) B3812845
theorem B3389195 : Blo 2259435 3389195 := bstep (se 1 (by rfl) ⟨2541896, by rfl⟩ : syracuseStep 3389195 = 5083793) B5083793
theorem B2259463 : Blo 2259435 2259463 := bstep (se 1 (by rfl) ⟨1694597, by rfl⟩ : syracuseStep 2259463 = 3389195) B3389195
theorem B2541901 : Blo 2259435 2541901 := bbase (se 3 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 2541901 = 953213) (by norm_num)
theorem B3389201 : Blo 2259435 3389201 := bstep (se 2 (by rfl) ⟨1270950, by rfl⟩ : syracuseStep 3389201 = 2541901) B2541901
theorem B2259467 : Blo 2259435 2259467 := bstep (se 1 (by rfl) ⟨1694600, by rfl⟩ : syracuseStep 2259467 = 3389201) B3389201
theorem B7625717 : Blo 2259435 7625717 := bbase (se 5 (by rfl) ⟨357455, by rfl⟩ : syracuseStep 7625717 = 714911) (by norm_num)
theorem B5083811 : Blo 2259435 5083811 := bstep (se 1 (by rfl) ⟨3812858, by rfl⟩ : syracuseStep 5083811 = 7625717) B7625717
theorem B3389207 : Blo 2259435 3389207 := bstep (se 1 (by rfl) ⟨2541905, by rfl⟩ : syracuseStep 3389207 = 5083811) B5083811
theorem B2259471 : Blo 2259435 2259471 := bstep (se 1 (by rfl) ⟨1694603, by rfl⟩ : syracuseStep 2259471 = 3389207) B3389207
theorem B3389213 : Blo 2259435 3389213 := bbase (se 3 (by rfl) ⟨635477, by rfl⟩ : syracuseStep 3389213 = 1270955) (by norm_num)
theorem B2259475 : Blo 2259435 2259475 := bstep (se 1 (by rfl) ⟨1694606, by rfl⟩ : syracuseStep 2259475 = 3389213) B3389213
theorem B5083829 : Blo 2259435 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B3389219 : Blo 2259435 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B2259479 : Blo 2259435 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B12868469 : Blo 2259435 12868469 := bbase (se 5 (by rfl) ⟨603209, by rfl⟩ : syracuseStep 12868469 = 1206419) (by norm_num)
theorem B8578979 : Blo 2259435 8578979 := bstep (se 1 (by rfl) ⟨6434234, by rfl⟩ : syracuseStep 8578979 = 12868469) B12868469
theorem B5719319 : Blo 2259435 5719319 := bstep (se 1 (by rfl) ⟨4289489, by rfl⟩ : syracuseStep 5719319 = 8578979) B8578979
theorem B3812879 : Blo 2259435 3812879 := bstep (se 1 (by rfl) ⟨2859659, by rfl⟩ : syracuseStep 3812879 = 5719319) B5719319
theorem B2541919 : Blo 2259435 2541919 := bstep (se 1 (by rfl) ⟨1906439, by rfl⟩ : syracuseStep 2541919 = 3812879) B3812879
theorem B3389225 : Blo 2259435 3389225 := bstep (se 2 (by rfl) ⟨1270959, by rfl⟩ : syracuseStep 3389225 = 2541919) B2541919
theorem B2259483 : Blo 2259435 2259483 := bstep (se 1 (by rfl) ⟨1694612, by rfl⟩ : syracuseStep 2259483 = 3389225) B3389225
theorem B6434245 : Blo 2259435 6434245 := bbase (se 4 (by rfl) ⟨603210, by rfl⟩ : syracuseStep 6434245 = 1206421) (by norm_num)
theorem B8578993 : Blo 2259435 8578993 := bstep (se 2 (by rfl) ⟨3217122, by rfl⟩ : syracuseStep 8578993 = 6434245) B6434245
theorem B11438657 : Blo 2259435 11438657 := bstep (se 2 (by rfl) ⟨4289496, by rfl⟩ : syracuseStep 11438657 = 8578993) B8578993
theorem B7625771 : Blo 2259435 7625771 := bstep (se 1 (by rfl) ⟨5719328, by rfl⟩ : syracuseStep 7625771 = 11438657) B11438657
theorem B5083847 : Blo 2259435 5083847 := bstep (se 1 (by rfl) ⟨3812885, by rfl⟩ : syracuseStep 5083847 = 7625771) B7625771
theorem B3389231 : Blo 2259435 3389231 := bstep (se 1 (by rfl) ⟨2541923, by rfl⟩ : syracuseStep 3389231 = 5083847) B5083847
theorem B2259487 : Blo 2259435 2259487 := bstep (se 1 (by rfl) ⟨1694615, by rfl⟩ : syracuseStep 2259487 = 3389231) B3389231
theorem B3389237 : Blo 2259435 3389237 := bbase (se 5 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 3389237 = 317741) (by norm_num)
theorem B2259491 : Blo 2259435 2259491 := bstep (se 1 (by rfl) ⟨1694618, by rfl⟩ : syracuseStep 2259491 = 3389237) B3389237
theorem B5719349 : Blo 2259435 5719349 := bbase (se 5 (by rfl) ⟨268094, by rfl⟩ : syracuseStep 5719349 = 536189) (by norm_num)
theorem B3812899 : Blo 2259435 3812899 := bstep (se 1 (by rfl) ⟨2859674, by rfl⟩ : syracuseStep 3812899 = 5719349) B5719349
theorem B5083865 : Blo 2259435 5083865 := bstep (se 2 (by rfl) ⟨1906449, by rfl⟩ : syracuseStep 5083865 = 3812899) B3812899
theorem B3389243 : Blo 2259435 3389243 := bstep (se 1 (by rfl) ⟨2541932, by rfl⟩ : syracuseStep 3389243 = 5083865) B5083865
theorem B2259495 : Blo 2259435 2259495 := bstep (se 1 (by rfl) ⟨1694621, by rfl⟩ : syracuseStep 2259495 = 3389243) B3389243
theorem B2541937 : Blo 2259435 2541937 := bbase (se 2 (by rfl) ⟨953226, by rfl⟩ : syracuseStep 2541937 = 1906453) (by norm_num)
theorem B3389249 : Blo 2259435 3389249 := bstep (se 2 (by rfl) ⟨1270968, by rfl⟩ : syracuseStep 3389249 = 2541937) B2541937
theorem B2259499 : Blo 2259435 2259499 := bstep (se 1 (by rfl) ⟨1694624, by rfl⟩ : syracuseStep 2259499 = 3389249) B3389249
theorem B4071701 : Blo 2259435 4071701 := bbase (se 6 (by rfl) ⟨95430, by rfl⟩ : syracuseStep 4071701 = 190861) (by norm_num)
theorem B2714467 : Blo 2259435 2714467 := bstep (se 1 (by rfl) ⟨2035850, by rfl⟩ : syracuseStep 2714467 = 4071701) B4071701
theorem B3619289 : Blo 2259435 3619289 := bstep (se 2 (by rfl) ⟨1357233, by rfl⟩ : syracuseStep 3619289 = 2714467) B2714467
theorem B9651437 : Blo 2259435 9651437 := bstep (se 3 (by rfl) ⟨1809644, by rfl⟩ : syracuseStep 9651437 = 3619289) B3619289
theorem B6434291 : Blo 2259435 6434291 := bstep (se 1 (by rfl) ⟨4825718, by rfl⟩ : syracuseStep 6434291 = 9651437) B9651437
theorem B4289527 : Blo 2259435 4289527 := bstep (se 1 (by rfl) ⟨3217145, by rfl⟩ : syracuseStep 4289527 = 6434291) B6434291
theorem B5719369 : Blo 2259435 5719369 := bstep (se 2 (by rfl) ⟨2144763, by rfl⟩ : syracuseStep 5719369 = 4289527) B4289527
theorem B7625825 : Blo 2259435 7625825 := bstep (se 2 (by rfl) ⟨2859684, by rfl⟩ : syracuseStep 7625825 = 5719369) B5719369
theorem B5083883 : Blo 2259435 5083883 := bstep (se 1 (by rfl) ⟨3812912, by rfl⟩ : syracuseStep 5083883 = 7625825) B7625825
theorem B3389255 : Blo 2259435 3389255 := bstep (se 1 (by rfl) ⟨2541941, by rfl⟩ : syracuseStep 3389255 = 5083883) B5083883
theorem B2259503 : Blo 2259435 2259503 := bstep (se 1 (by rfl) ⟨1694627, by rfl⟩ : syracuseStep 2259503 = 3389255) B3389255
theorem B3389261 : Blo 2259435 3389261 := bbase (se 3 (by rfl) ⟨635486, by rfl⟩ : syracuseStep 3389261 = 1270973) (by norm_num)
theorem B2259507 : Blo 2259435 2259507 := bstep (se 1 (by rfl) ⟨1694630, by rfl⟩ : syracuseStep 2259507 = 3389261) B3389261
theorem B5083901 : Blo 2259435 5083901 := bbase (se 3 (by rfl) ⟨953231, by rfl⟩ : syracuseStep 5083901 = 1906463) (by norm_num)
theorem B3389267 : Blo 2259435 3389267 := bstep (se 1 (by rfl) ⟨2541950, by rfl⟩ : syracuseStep 3389267 = 5083901) B5083901
theorem B2259511 : Blo 2259435 2259511 := bstep (se 1 (by rfl) ⟨1694633, by rfl⟩ : syracuseStep 2259511 = 3389267) B3389267
theorem B3812933 : Blo 2259435 3812933 := bbase (se 4 (by rfl) ⟨357462, by rfl⟩ : syracuseStep 3812933 = 714925) (by norm_num)
theorem B2541955 : Blo 2259435 2541955 := bstep (se 1 (by rfl) ⟨1906466, by rfl⟩ : syracuseStep 2541955 = 3812933) B3812933
theorem B3389273 : Blo 2259435 3389273 := bstep (se 2 (by rfl) ⟨1270977, by rfl⟩ : syracuseStep 3389273 = 2541955) B2541955
theorem B2259515 : Blo 2259435 2259515 := bstep (se 1 (by rfl) ⟨1694636, by rfl⟩ : syracuseStep 2259515 = 3389273) B3389273
theorem B17158229 : Blo 2259435 17158229 := bbase (se 8 (by rfl) ⟨100536, by rfl⟩ : syracuseStep 17158229 = 201073) (by norm_num)
theorem B11438819 : Blo 2259435 11438819 := bstep (se 1 (by rfl) ⟨8579114, by rfl⟩ : syracuseStep 11438819 = 17158229) B17158229
theorem B7625879 : Blo 2259435 7625879 := bstep (se 1 (by rfl) ⟨5719409, by rfl⟩ : syracuseStep 7625879 = 11438819) B11438819
theorem B5083919 : Blo 2259435 5083919 := bstep (se 1 (by rfl) ⟨3812939, by rfl⟩ : syracuseStep 5083919 = 7625879) B7625879
theorem B3389279 : Blo 2259435 3389279 := bstep (se 1 (by rfl) ⟨2541959, by rfl⟩ : syracuseStep 3389279 = 5083919) B5083919
theorem B2259519 : Blo 2259435 2259519 := bstep (se 1 (by rfl) ⟨1694639, by rfl⟩ : syracuseStep 2259519 = 3389279) B3389279
theorem B3389285 : Blo 2259435 3389285 := bbase (se 4 (by rfl) ⟨317745, by rfl⟩ : syracuseStep 3389285 = 635491) (by norm_num)
theorem B2259523 : Blo 2259435 2259523 := bstep (se 1 (by rfl) ⟨1694642, by rfl⟩ : syracuseStep 2259523 = 3389285) B3389285
theorem B4289573 : Blo 2259435 4289573 := bbase (se 4 (by rfl) ⟨402147, by rfl⟩ : syracuseStep 4289573 = 804295) (by norm_num)
theorem B2859715 : Blo 2259435 2859715 := bstep (se 1 (by rfl) ⟨2144786, by rfl⟩ : syracuseStep 2859715 = 4289573) B4289573
theorem B3812953 : Blo 2259435 3812953 := bstep (se 2 (by rfl) ⟨1429857, by rfl⟩ : syracuseStep 3812953 = 2859715) B2859715
theorem B5083937 : Blo 2259435 5083937 := bstep (se 2 (by rfl) ⟨1906476, by rfl⟩ : syracuseStep 5083937 = 3812953) B3812953
theorem B3389291 : Blo 2259435 3389291 := bstep (se 1 (by rfl) ⟨2541968, by rfl⟩ : syracuseStep 3389291 = 5083937) B5083937
theorem B2259527 : Blo 2259435 2259527 := bstep (se 1 (by rfl) ⟨1694645, by rfl⟩ : syracuseStep 2259527 = 3389291) B3389291
theorem B2541973 : Blo 2259435 2541973 := bbase (se 6 (by rfl) ⟨59577, by rfl⟩ : syracuseStep 2541973 = 119155) (by norm_num)
theorem B3389297 : Blo 2259435 3389297 := bstep (se 2 (by rfl) ⟨1270986, by rfl⟩ : syracuseStep 3389297 = 2541973) B2541973
theorem B2259531 : Blo 2259435 2259531 := bstep (se 1 (by rfl) ⟨1694648, by rfl⟩ : syracuseStep 2259531 = 3389297) B3389297
theorem B2859725 : Blo 2259435 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B7625933 : Blo 2259435 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B5083955 : Blo 2259435 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B3389303 : Blo 2259435 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B2259535 : Blo 2259435 2259535 := bstep (se 1 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 2259535 = 3389303) B3389303
theorem B3389309 : Blo 2259435 3389309 := bbase (se 3 (by rfl) ⟨635495, by rfl⟩ : syracuseStep 3389309 = 1270991) (by norm_num)
theorem B2259539 : Blo 2259435 2259539 := bstep (se 1 (by rfl) ⟨1694654, by rfl⟩ : syracuseStep 2259539 = 3389309) B3389309
theorem B5083973 : Blo 2259435 5083973 := bbase (se 4 (by rfl) ⟨476622, by rfl⟩ : syracuseStep 5083973 = 953245) (by norm_num)
theorem B3389315 : Blo 2259435 3389315 := bstep (se 1 (by rfl) ⟨2541986, by rfl⟩ : syracuseStep 3389315 = 5083973) B5083973
theorem B2259543 : Blo 2259435 2259543 := bstep (se 1 (by rfl) ⟨1694657, by rfl⟩ : syracuseStep 2259543 = 3389315) B3389315
theorem B4825813 : Blo 2259435 4825813 := bbase (se 7 (by rfl) ⟨56552, by rfl⟩ : syracuseStep 4825813 = 113105) (by norm_num)
theorem B6434417 : Blo 2259435 6434417 := bstep (se 2 (by rfl) ⟨2412906, by rfl⟩ : syracuseStep 6434417 = 4825813) B4825813
theorem B4289611 : Blo 2259435 4289611 := bstep (se 1 (by rfl) ⟨3217208, by rfl⟩ : syracuseStep 4289611 = 6434417) B6434417
theorem B5719481 : Blo 2259435 5719481 := bstep (se 2 (by rfl) ⟨2144805, by rfl⟩ : syracuseStep 5719481 = 4289611) B4289611
theorem B3812987 : Blo 2259435 3812987 := bstep (se 1 (by rfl) ⟨2859740, by rfl⟩ : syracuseStep 3812987 = 5719481) B5719481
theorem B2541991 : Blo 2259435 2541991 := bstep (se 1 (by rfl) ⟨1906493, by rfl⟩ : syracuseStep 2541991 = 3812987) B3812987
theorem B3389321 : Blo 2259435 3389321 := bstep (se 2 (by rfl) ⟨1270995, by rfl⟩ : syracuseStep 3389321 = 2541991) B2541991
theorem B2259547 : Blo 2259435 2259547 := bstep (se 1 (by rfl) ⟨1694660, by rfl⟩ : syracuseStep 2259547 = 3389321) B3389321
theorem B11438981 : Blo 2259435 11438981 := bbase (se 4 (by rfl) ⟨1072404, by rfl⟩ : syracuseStep 11438981 = 2144809) (by norm_num)
theorem B7625987 : Blo 2259435 7625987 := bstep (se 1 (by rfl) ⟨5719490, by rfl⟩ : syracuseStep 7625987 = 11438981) B11438981
theorem B5083991 : Blo 2259435 5083991 := bstep (se 1 (by rfl) ⟨3812993, by rfl⟩ : syracuseStep 5083991 = 7625987) B7625987
theorem B3389327 : Blo 2259435 3389327 := bstep (se 1 (by rfl) ⟨2541995, by rfl⟩ : syracuseStep 3389327 = 5083991) B5083991
theorem B2259551 : Blo 2259435 2259551 := bstep (se 1 (by rfl) ⟨1694663, by rfl⟩ : syracuseStep 2259551 = 3389327) B3389327
theorem B3389333 : Blo 2259435 3389333 := bbase (se 6 (by rfl) ⟨79437, by rfl⟩ : syracuseStep 3389333 = 158875) (by norm_num)
theorem B2259555 : Blo 2259435 2259555 := bstep (se 1 (by rfl) ⟨1694666, by rfl⟩ : syracuseStep 2259555 = 3389333) B3389333
theorem B5429069 : Blo 2259435 5429069 := bbase (se 3 (by rfl) ⟨1017950, by rfl⟩ : syracuseStep 5429069 = 2035901) (by norm_num)
theorem B3619379 : Blo 2259435 3619379 := bstep (se 1 (by rfl) ⟨2714534, by rfl⟩ : syracuseStep 3619379 = 5429069) B5429069
theorem B2412919 : Blo 2259435 2412919 := bstep (se 1 (by rfl) ⟨1809689, by rfl⟩ : syracuseStep 2412919 = 3619379) B3619379
theorem B12868901 : Blo 2259435 12868901 := bstep (se 4 (by rfl) ⟨1206459, by rfl⟩ : syracuseStep 12868901 = 2412919) B2412919
theorem B8579267 : Blo 2259435 8579267 := bstep (se 1 (by rfl) ⟨6434450, by rfl⟩ : syracuseStep 8579267 = 12868901) B12868901
theorem B5719511 : Blo 2259435 5719511 := bstep (se 1 (by rfl) ⟨4289633, by rfl⟩ : syracuseStep 5719511 = 8579267) B8579267
theorem B3813007 : Blo 2259435 3813007 := bstep (se 1 (by rfl) ⟨2859755, by rfl⟩ : syracuseStep 3813007 = 5719511) B5719511
theorem B5084009 : Blo 2259435 5084009 := bstep (se 2 (by rfl) ⟨1906503, by rfl⟩ : syracuseStep 5084009 = 3813007) B3813007
theorem B3389339 : Blo 2259435 3389339 := bstep (se 1 (by rfl) ⟨2542004, by rfl⟩ : syracuseStep 3389339 = 5084009) B5084009
theorem B2259559 : Blo 2259435 2259559 := bstep (se 1 (by rfl) ⟨1694669, by rfl⟩ : syracuseStep 2259559 = 3389339) B3389339
theorem B2542009 : Blo 2259435 2542009 := bbase (se 2 (by rfl) ⟨953253, by rfl⟩ : syracuseStep 2542009 = 1906507) (by norm_num)
theorem B3389345 : Blo 2259435 3389345 := bstep (se 2 (by rfl) ⟨1271004, by rfl⟩ : syracuseStep 3389345 = 2542009) B2542009
theorem B2259563 : Blo 2259435 2259563 := bstep (se 1 (by rfl) ⟨1694672, by rfl⟩ : syracuseStep 2259563 = 3389345) B3389345
theorem B3668773 : Blo 2259435 3668773 := bbase (se 4 (by rfl) ⟨343947, by rfl⟩ : syracuseStep 3668773 = 687895) (by norm_num)
theorem B4891697 : Blo 2259435 4891697 := bstep (se 2 (by rfl) ⟨1834386, by rfl⟩ : syracuseStep 4891697 = 3668773) B3668773
theorem B3261131 : Blo 2259435 3261131 := bstep (se 1 (by rfl) ⟨2445848, by rfl⟩ : syracuseStep 3261131 = 4891697) B4891697
theorem B34785397 : Blo 2259435 34785397 := bstep (se 5 (by rfl) ⟨1630565, by rfl⟩ : syracuseStep 34785397 = 3261131) B3261131
theorem B46380529 : Blo 2259435 46380529 := bstep (se 2 (by rfl) ⟨17392698, by rfl⟩ : syracuseStep 46380529 = 34785397) B34785397
theorem B61840705 : Blo 2259435 61840705 := bstep (se 2 (by rfl) ⟨23190264, by rfl⟩ : syracuseStep 61840705 = 46380529) B46380529
theorem B82454273 : Blo 2259435 82454273 := bstep (se 2 (by rfl) ⟨30920352, by rfl⟩ : syracuseStep 82454273 = 61840705) B61840705
theorem B54969515 : Blo 2259435 54969515 := bstep (se 1 (by rfl) ⟨41227136, by rfl⟩ : syracuseStep 54969515 = 82454273) B82454273
theorem B36646343 : Blo 2259435 36646343 := bstep (se 1 (by rfl) ⟨27484757, by rfl⟩ : syracuseStep 36646343 = 54969515) B54969515
theorem B24430895 : Blo 2259435 24430895 := bstep (se 1 (by rfl) ⟨18323171, by rfl⟩ : syracuseStep 24430895 = 36646343) B36646343
theorem B16287263 : Blo 2259435 16287263 := bstep (se 1 (by rfl) ⟨12215447, by rfl⟩ : syracuseStep 16287263 = 24430895) B24430895
theorem B10858175 : Blo 2259435 10858175 := bstep (se 1 (by rfl) ⟨8143631, by rfl⟩ : syracuseStep 10858175 = 16287263) B16287263
theorem B7238783 : Blo 2259435 7238783 := bstep (se 1 (by rfl) ⟨5429087, by rfl⟩ : syracuseStep 7238783 = 10858175) B10858175
theorem B4825855 : Blo 2259435 4825855 := bstep (se 1 (by rfl) ⟨3619391, by rfl⟩ : syracuseStep 4825855 = 7238783) B7238783
theorem B6434473 : Blo 2259435 6434473 := bstep (se 2 (by rfl) ⟨2412927, by rfl⟩ : syracuseStep 6434473 = 4825855) B4825855
theorem B8579297 : Blo 2259435 8579297 := bstep (se 2 (by rfl) ⟨3217236, by rfl⟩ : syracuseStep 8579297 = 6434473) B6434473
theorem B5719531 : Blo 2259435 5719531 := bstep (se 1 (by rfl) ⟨4289648, by rfl⟩ : syracuseStep 5719531 = 8579297) B8579297
theorem B7626041 : Blo 2259435 7626041 := bstep (se 2 (by rfl) ⟨2859765, by rfl⟩ : syracuseStep 7626041 = 5719531) B5719531
theorem B5084027 : Blo 2259435 5084027 := bstep (se 1 (by rfl) ⟨3813020, by rfl⟩ : syracuseStep 5084027 = 7626041) B7626041
theorem B3389351 : Blo 2259435 3389351 := bstep (se 1 (by rfl) ⟨2542013, by rfl⟩ : syracuseStep 3389351 = 5084027) B5084027
theorem B2259567 : Blo 2259435 2259567 := bstep (se 1 (by rfl) ⟨1694675, by rfl⟩ : syracuseStep 2259567 = 3389351) B3389351
theorem B3389357 : Blo 2259435 3389357 := bbase (se 3 (by rfl) ⟨635504, by rfl⟩ : syracuseStep 3389357 = 1271009) (by norm_num)
theorem B2259571 : Blo 2259435 2259571 := bstep (se 1 (by rfl) ⟨1694678, by rfl⟩ : syracuseStep 2259571 = 3389357) B3389357
theorem B5084045 : Blo 2259435 5084045 := bbase (se 3 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 5084045 = 1906517) (by norm_num)
theorem B3389363 : Blo 2259435 3389363 := bstep (se 1 (by rfl) ⟨2542022, by rfl⟩ : syracuseStep 3389363 = 5084045) B5084045
theorem B2259575 : Blo 2259435 2259575 := bstep (se 1 (by rfl) ⟨1694681, by rfl⟩ : syracuseStep 2259575 = 3389363) B3389363
theorem B2859781 : Blo 2259435 2859781 := bbase (se 4 (by rfl) ⟨268104, by rfl⟩ : syracuseStep 2859781 = 536209) (by norm_num)
theorem B3813041 : Blo 2259435 3813041 := bstep (se 2 (by rfl) ⟨1429890, by rfl⟩ : syracuseStep 3813041 = 2859781) B2859781
theorem B2542027 : Blo 2259435 2542027 := bstep (se 1 (by rfl) ⟨1906520, by rfl⟩ : syracuseStep 2542027 = 3813041) B3813041
theorem B3389369 : Blo 2259435 3389369 := bstep (se 2 (by rfl) ⟨1271013, by rfl⟩ : syracuseStep 3389369 = 2542027) B2542027
theorem B2259579 : Blo 2259435 2259579 := bstep (se 1 (by rfl) ⟨1694684, by rfl⟩ : syracuseStep 2259579 = 3389369) B3389369
theorem B5429125 : Blo 2259435 5429125 := bbase (se 4 (by rfl) ⟨508980, by rfl⟩ : syracuseStep 5429125 = 1017961) (by norm_num)
theorem B28955333 : Blo 2259435 28955333 := bstep (se 4 (by rfl) ⟨2714562, by rfl⟩ : syracuseStep 28955333 = 5429125) B5429125
theorem B19303555 : Blo 2259435 19303555 := bstep (se 1 (by rfl) ⟨14477666, by rfl⟩ : syracuseStep 19303555 = 28955333) B28955333
theorem B25738073 : Blo 2259435 25738073 := bstep (se 2 (by rfl) ⟨9651777, by rfl⟩ : syracuseStep 25738073 = 19303555) B19303555
theorem B17158715 : Blo 2259435 17158715 := bstep (se 1 (by rfl) ⟨12869036, by rfl⟩ : syracuseStep 17158715 = 25738073) B25738073
theorem B11439143 : Blo 2259435 11439143 := bstep (se 1 (by rfl) ⟨8579357, by rfl⟩ : syracuseStep 11439143 = 17158715) B17158715
theorem B7626095 : Blo 2259435 7626095 := bstep (se 1 (by rfl) ⟨5719571, by rfl⟩ : syracuseStep 7626095 = 11439143) B11439143
theorem B5084063 : Blo 2259435 5084063 := bstep (se 1 (by rfl) ⟨3813047, by rfl⟩ : syracuseStep 5084063 = 7626095) B7626095
theorem B3389375 : Blo 2259435 3389375 := bstep (se 1 (by rfl) ⟨2542031, by rfl⟩ : syracuseStep 3389375 = 5084063) B5084063
theorem B2259583 : Blo 2259435 2259583 := bstep (se 1 (by rfl) ⟨1694687, by rfl⟩ : syracuseStep 2259583 = 3389375) B3389375
theorem B3389381 : Blo 2259435 3389381 := bbase (se 4 (by rfl) ⟨317754, by rfl⟩ : syracuseStep 3389381 = 635509) (by norm_num)
theorem B2259587 : Blo 2259435 2259587 := bstep (se 1 (by rfl) ⟨1694690, by rfl⟩ : syracuseStep 2259587 = 3389381) B3389381
theorem B3813061 : Blo 2259435 3813061 := bbase (se 4 (by rfl) ⟨357474, by rfl⟩ : syracuseStep 3813061 = 714949) (by norm_num)
theorem B5084081 : Blo 2259435 5084081 := bstep (se 2 (by rfl) ⟨1906530, by rfl⟩ : syracuseStep 5084081 = 3813061) B3813061
theorem B3389387 : Blo 2259435 3389387 := bstep (se 1 (by rfl) ⟨2542040, by rfl⟩ : syracuseStep 3389387 = 5084081) B5084081
theorem B2259591 : Blo 2259435 2259591 := bstep (se 1 (by rfl) ⟨1694693, by rfl⟩ : syracuseStep 2259591 = 3389387) B3389387
theorem B2542045 : Blo 2259435 2542045 := bbase (se 3 (by rfl) ⟨476633, by rfl⟩ : syracuseStep 2542045 = 953267) (by norm_num)
theorem B3389393 : Blo 2259435 3389393 := bstep (se 2 (by rfl) ⟨1271022, by rfl⟩ : syracuseStep 3389393 = 2542045) B2542045
theorem B2259595 : Blo 2259435 2259595 := bstep (se 1 (by rfl) ⟨1694696, by rfl⟩ : syracuseStep 2259595 = 3389393) B3389393
theorem B7626149 : Blo 2259435 7626149 := bbase (se 4 (by rfl) ⟨714951, by rfl⟩ : syracuseStep 7626149 = 1429903) (by norm_num)
theorem B5084099 : Blo 2259435 5084099 := bstep (se 1 (by rfl) ⟨3813074, by rfl⟩ : syracuseStep 5084099 = 7626149) B7626149
theorem B3389399 : Blo 2259435 3389399 := bstep (se 1 (by rfl) ⟨2542049, by rfl⟩ : syracuseStep 3389399 = 5084099) B5084099
theorem B2259599 : Blo 2259435 2259599 := bstep (se 1 (by rfl) ⟨1694699, by rfl⟩ : syracuseStep 2259599 = 3389399) B3389399
theorem B3389405 : Blo 2259435 3389405 := bbase (se 3 (by rfl) ⟨635513, by rfl⟩ : syracuseStep 3389405 = 1271027) (by norm_num)
theorem B2259603 : Blo 2259435 2259603 := bstep (se 1 (by rfl) ⟨1694702, by rfl⟩ : syracuseStep 2259603 = 3389405) B3389405
theorem B5084117 : Blo 2259435 5084117 := bbase (se 7 (by rfl) ⟨59579, by rfl⟩ : syracuseStep 5084117 = 119159) (by norm_num)
theorem B3389411 : Blo 2259435 3389411 := bstep (se 1 (by rfl) ⟨2542058, by rfl⟩ : syracuseStep 3389411 = 5084117) B5084117
theorem B2259607 : Blo 2259435 2259607 := bstep (se 1 (by rfl) ⟨1694705, by rfl⟩ : syracuseStep 2259607 = 3389411) B3389411
theorem B9161765 : Blo 2259435 9161765 := bbase (se 4 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 9161765 = 1717831) (by norm_num)
theorem B6107843 : Blo 2259435 6107843 := bstep (se 1 (by rfl) ⟨4580882, by rfl⟩ : syracuseStep 6107843 = 9161765) B9161765
theorem B16287581 : Blo 2259435 16287581 := bstep (se 3 (by rfl) ⟨3053921, by rfl⟩ : syracuseStep 16287581 = 6107843) B6107843
theorem B10858387 : Blo 2259435 10858387 := bstep (se 1 (by rfl) ⟨8143790, by rfl⟩ : syracuseStep 10858387 = 16287581) B16287581
theorem B14477849 : Blo 2259435 14477849 := bstep (se 2 (by rfl) ⟨5429193, by rfl⟩ : syracuseStep 14477849 = 10858387) B10858387
theorem B9651899 : Blo 2259435 9651899 := bstep (se 1 (by rfl) ⟨7238924, by rfl⟩ : syracuseStep 9651899 = 14477849) B14477849
theorem B6434599 : Blo 2259435 6434599 := bstep (se 1 (by rfl) ⟨4825949, by rfl⟩ : syracuseStep 6434599 = 9651899) B9651899
theorem B8579465 : Blo 2259435 8579465 := bstep (se 2 (by rfl) ⟨3217299, by rfl⟩ : syracuseStep 8579465 = 6434599) B6434599
theorem B5719643 : Blo 2259435 5719643 := bstep (se 1 (by rfl) ⟨4289732, by rfl⟩ : syracuseStep 5719643 = 8579465) B8579465
theorem B3813095 : Blo 2259435 3813095 := bstep (se 1 (by rfl) ⟨2859821, by rfl⟩ : syracuseStep 3813095 = 5719643) B5719643
theorem B2542063 : Blo 2259435 2542063 := bstep (se 1 (by rfl) ⟨1906547, by rfl⟩ : syracuseStep 2542063 = 3813095) B3813095
theorem B3389417 : Blo 2259435 3389417 := bstep (se 2 (by rfl) ⟨1271031, by rfl⟩ : syracuseStep 3389417 = 2542063) B2542063
theorem B2259611 : Blo 2259435 2259611 := bstep (se 1 (by rfl) ⟨1694708, by rfl⟩ : syracuseStep 2259611 = 3389417) B3389417
theorem B19303829 : Blo 2259435 19303829 := bbase (se 6 (by rfl) ⟨452433, by rfl⟩ : syracuseStep 19303829 = 904867) (by norm_num)
theorem B12869219 : Blo 2259435 12869219 := bstep (se 1 (by rfl) ⟨9651914, by rfl⟩ : syracuseStep 12869219 = 19303829) B19303829
theorem B8579479 : Blo 2259435 8579479 := bstep (se 1 (by rfl) ⟨6434609, by rfl⟩ : syracuseStep 8579479 = 12869219) B12869219
theorem B11439305 : Blo 2259435 11439305 := bstep (se 2 (by rfl) ⟨4289739, by rfl⟩ : syracuseStep 11439305 = 8579479) B8579479
theorem B7626203 : Blo 2259435 7626203 := bstep (se 1 (by rfl) ⟨5719652, by rfl⟩ : syracuseStep 7626203 = 11439305) B11439305
theorem B5084135 : Blo 2259435 5084135 := bstep (se 1 (by rfl) ⟨3813101, by rfl⟩ : syracuseStep 5084135 = 7626203) B7626203
theorem B3389423 : Blo 2259435 3389423 := bstep (se 1 (by rfl) ⟨2542067, by rfl⟩ : syracuseStep 3389423 = 5084135) B5084135
theorem B2259615 : Blo 2259435 2259615 := bstep (se 1 (by rfl) ⟨1694711, by rfl⟩ : syracuseStep 2259615 = 3389423) B3389423
theorem B3389429 : Blo 2259435 3389429 := bbase (se 5 (by rfl) ⟨158879, by rfl⟩ : syracuseStep 3389429 = 317759) (by norm_num)
theorem B2259619 : Blo 2259435 2259619 := bstep (se 1 (by rfl) ⟨1694714, by rfl⟩ : syracuseStep 2259619 = 3389429) B3389429
theorem B4071917 : Blo 2259435 4071917 := bbase (se 3 (by rfl) ⟨763484, by rfl⟩ : syracuseStep 4071917 = 1526969) (by norm_num)
theorem B10858445 : Blo 2259435 10858445 := bstep (se 3 (by rfl) ⟨2035958, by rfl⟩ : syracuseStep 10858445 = 4071917) B4071917
theorem B7238963 : Blo 2259435 7238963 := bstep (se 1 (by rfl) ⟨5429222, by rfl⟩ : syracuseStep 7238963 = 10858445) B10858445
theorem B4825975 : Blo 2259435 4825975 := bstep (se 1 (by rfl) ⟨3619481, by rfl⟩ : syracuseStep 4825975 = 7238963) B7238963
theorem B6434633 : Blo 2259435 6434633 := bstep (se 2 (by rfl) ⟨2412987, by rfl⟩ : syracuseStep 6434633 = 4825975) B4825975
theorem B4289755 : Blo 2259435 4289755 := bstep (se 1 (by rfl) ⟨3217316, by rfl⟩ : syracuseStep 4289755 = 6434633) B6434633
theorem B5719673 : Blo 2259435 5719673 := bstep (se 2 (by rfl) ⟨2144877, by rfl⟩ : syracuseStep 5719673 = 4289755) B4289755
theorem B3813115 : Blo 2259435 3813115 := bstep (se 1 (by rfl) ⟨2859836, by rfl⟩ : syracuseStep 3813115 = 5719673) B5719673
theorem B5084153 : Blo 2259435 5084153 := bstep (se 2 (by rfl) ⟨1906557, by rfl⟩ : syracuseStep 5084153 = 3813115) B3813115
theorem B3389435 : Blo 2259435 3389435 := bstep (se 1 (by rfl) ⟨2542076, by rfl⟩ : syracuseStep 3389435 = 5084153) B5084153
theorem B2259623 : Blo 2259435 2259623 := bstep (se 1 (by rfl) ⟨1694717, by rfl⟩ : syracuseStep 2259623 = 3389435) B3389435
theorem B2542081 : Blo 2259435 2542081 := bbase (se 2 (by rfl) ⟨953280, by rfl⟩ : syracuseStep 2542081 = 1906561) (by norm_num)
theorem B3389441 : Blo 2259435 3389441 := bstep (se 2 (by rfl) ⟨1271040, by rfl⟩ : syracuseStep 3389441 = 2542081) B2542081
theorem B2259627 : Blo 2259435 2259627 := bstep (se 1 (by rfl) ⟨1694720, by rfl⟩ : syracuseStep 2259627 = 3389441) B3389441
theorem B5719693 : Blo 2259435 5719693 := bbase (se 3 (by rfl) ⟨1072442, by rfl⟩ : syracuseStep 5719693 = 2144885) (by norm_num)
theorem B7626257 : Blo 2259435 7626257 := bstep (se 2 (by rfl) ⟨2859846, by rfl⟩ : syracuseStep 7626257 = 5719693) B5719693
theorem B5084171 : Blo 2259435 5084171 := bstep (se 1 (by rfl) ⟨3813128, by rfl⟩ : syracuseStep 5084171 = 7626257) B7626257
theorem B3389447 : Blo 2259435 3389447 := bstep (se 1 (by rfl) ⟨2542085, by rfl⟩ : syracuseStep 3389447 = 5084171) B5084171
theorem B2259631 : Blo 2259435 2259631 := bstep (se 1 (by rfl) ⟨1694723, by rfl⟩ : syracuseStep 2259631 = 3389447) B3389447
theorem B3389453 : Blo 2259435 3389453 := bbase (se 3 (by rfl) ⟨635522, by rfl⟩ : syracuseStep 3389453 = 1271045) (by norm_num)
theorem B2259635 : Blo 2259435 2259635 := bstep (se 1 (by rfl) ⟨1694726, by rfl⟩ : syracuseStep 2259635 = 3389453) B3389453
theorem B5084189 : Blo 2259435 5084189 := bbase (se 3 (by rfl) ⟨953285, by rfl⟩ : syracuseStep 5084189 = 1906571) (by norm_num)
theorem B3389459 : Blo 2259435 3389459 := bstep (se 1 (by rfl) ⟨2542094, by rfl⟩ : syracuseStep 3389459 = 5084189) B5084189
theorem B2259639 : Blo 2259435 2259639 := bstep (se 1 (by rfl) ⟨1694729, by rfl⟩ : syracuseStep 2259639 = 3389459) B3389459
theorem B3813149 : Blo 2259435 3813149 := bbase (se 3 (by rfl) ⟨714965, by rfl⟩ : syracuseStep 3813149 = 1429931) (by norm_num)
theorem B2542099 : Blo 2259435 2542099 := bstep (se 1 (by rfl) ⟨1906574, by rfl⟩ : syracuseStep 2542099 = 3813149) B3813149
theorem B3389465 : Blo 2259435 3389465 := bstep (se 2 (by rfl) ⟨1271049, by rfl⟩ : syracuseStep 3389465 = 2542099) B2542099
theorem B2259643 : Blo 2259435 2259643 := bstep (se 1 (by rfl) ⟨1694732, by rfl⟩ : syracuseStep 2259643 = 3389465) B3389465
theorem B3917917 : Blo 2259435 3917917 := bbase (se 3 (by rfl) ⟨734609, by rfl⟩ : syracuseStep 3917917 = 1469219) (by norm_num)
theorem B5223889 : Blo 2259435 5223889 := bstep (se 2 (by rfl) ⟨1958958, by rfl⟩ : syracuseStep 5223889 = 3917917) B3917917
theorem B6965185 : Blo 2259435 6965185 := bstep (se 2 (by rfl) ⟨2611944, by rfl⟩ : syracuseStep 6965185 = 5223889) B5223889
theorem B9286913 : Blo 2259435 9286913 := bstep (se 2 (by rfl) ⟨3482592, by rfl⟩ : syracuseStep 9286913 = 6965185) B6965185
theorem B6191275 : Blo 2259435 6191275 := bstep (se 1 (by rfl) ⟨4643456, by rfl⟩ : syracuseStep 6191275 = 9286913) B9286913
theorem B8255033 : Blo 2259435 8255033 := bstep (se 2 (by rfl) ⟨3095637, by rfl⟩ : syracuseStep 8255033 = 6191275) B6191275
theorem B5503355 : Blo 2259435 5503355 := bstep (se 1 (by rfl) ⟨4127516, by rfl⟩ : syracuseStep 5503355 = 8255033) B8255033
theorem B3668903 : Blo 2259435 3668903 := bstep (se 1 (by rfl) ⟨2751677, by rfl⟩ : syracuseStep 3668903 = 5503355) B5503355
theorem B2445935 : Blo 2259435 2445935 := bstep (se 1 (by rfl) ⟨1834451, by rfl⟩ : syracuseStep 2445935 = 3668903) B3668903
theorem B6522493 : Blo 2259435 6522493 := bstep (se 3 (by rfl) ⟨1222967, by rfl⟩ : syracuseStep 6522493 = 2445935) B2445935
theorem B8696657 : Blo 2259435 8696657 := bstep (se 2 (by rfl) ⟨3261246, by rfl⟩ : syracuseStep 8696657 = 6522493) B6522493
theorem B23191085 : Blo 2259435 23191085 := bstep (se 3 (by rfl) ⟨4348328, by rfl⟩ : syracuseStep 23191085 = 8696657) B8696657
theorem B15460723 : Blo 2259435 15460723 := bstep (se 1 (by rfl) ⟨11595542, by rfl⟩ : syracuseStep 15460723 = 23191085) B23191085
theorem B20614297 : Blo 2259435 20614297 := bstep (se 2 (by rfl) ⟨7730361, by rfl⟩ : syracuseStep 20614297 = 15460723) B15460723
theorem B27485729 : Blo 2259435 27485729 := bstep (se 2 (by rfl) ⟨10307148, by rfl⟩ : syracuseStep 27485729 = 20614297) B20614297
theorem B18323819 : Blo 2259435 18323819 := bstep (se 1 (by rfl) ⟨13742864, by rfl⟩ : syracuseStep 18323819 = 27485729) B27485729
theorem B12215879 : Blo 2259435 12215879 := bstep (se 1 (by rfl) ⟨9161909, by rfl⟩ : syracuseStep 12215879 = 18323819) B18323819
theorem B8143919 : Blo 2259435 8143919 := bstep (se 1 (by rfl) ⟨6107939, by rfl⟩ : syracuseStep 8143919 = 12215879) B12215879
theorem B5429279 : Blo 2259435 5429279 := bstep (se 1 (by rfl) ⟨4071959, by rfl⟩ : syracuseStep 5429279 = 8143919) B8143919
theorem B14478077 : Blo 2259435 14478077 := bstep (se 3 (by rfl) ⟨2714639, by rfl⟩ : syracuseStep 14478077 = 5429279) B5429279
theorem B9652051 : Blo 2259435 9652051 := bstep (se 1 (by rfl) ⟨7239038, by rfl⟩ : syracuseStep 9652051 = 14478077) B14478077
theorem B12869401 : Blo 2259435 12869401 := bstep (se 2 (by rfl) ⟨4826025, by rfl⟩ : syracuseStep 12869401 = 9652051) B9652051
theorem B17159201 : Blo 2259435 17159201 := bstep (se 2 (by rfl) ⟨6434700, by rfl⟩ : syracuseStep 17159201 = 12869401) B12869401
theorem B11439467 : Blo 2259435 11439467 := bstep (se 1 (by rfl) ⟨8579600, by rfl⟩ : syracuseStep 11439467 = 17159201) B17159201
theorem B7626311 : Blo 2259435 7626311 := bstep (se 1 (by rfl) ⟨5719733, by rfl⟩ : syracuseStep 7626311 = 11439467) B11439467
theorem B5084207 : Blo 2259435 5084207 := bstep (se 1 (by rfl) ⟨3813155, by rfl⟩ : syracuseStep 5084207 = 7626311) B7626311
theorem B3389471 : Blo 2259435 3389471 := bstep (se 1 (by rfl) ⟨2542103, by rfl⟩ : syracuseStep 3389471 = 5084207) B5084207
theorem B2259647 : Blo 2259435 2259647 := bstep (se 1 (by rfl) ⟨1694735, by rfl⟩ : syracuseStep 2259647 = 3389471) B3389471
theorem B3389477 : Blo 2259435 3389477 := bbase (se 4 (by rfl) ⟨317763, by rfl⟩ : syracuseStep 3389477 = 635527) (by norm_num)
theorem B2259651 : Blo 2259435 2259651 := bstep (se 1 (by rfl) ⟨1694738, by rfl⟩ : syracuseStep 2259651 = 3389477) B3389477
theorem B2859877 : Blo 2259435 2859877 := bbase (se 4 (by rfl) ⟨268113, by rfl⟩ : syracuseStep 2859877 = 536227) (by norm_num)
theorem B3813169 : Blo 2259435 3813169 := bstep (se 2 (by rfl) ⟨1429938, by rfl⟩ : syracuseStep 3813169 = 2859877) B2859877
theorem B5084225 : Blo 2259435 5084225 := bstep (se 2 (by rfl) ⟨1906584, by rfl⟩ : syracuseStep 5084225 = 3813169) B3813169
theorem B3389483 : Blo 2259435 3389483 := bstep (se 1 (by rfl) ⟨2542112, by rfl⟩ : syracuseStep 3389483 = 5084225) B5084225
theorem B2259655 : Blo 2259435 2259655 := bstep (se 1 (by rfl) ⟨1694741, by rfl⟩ : syracuseStep 2259655 = 3389483) B3389483
theorem B2542117 : Blo 2259435 2542117 := bbase (se 4 (by rfl) ⟨238323, by rfl⟩ : syracuseStep 2542117 = 476647) (by norm_num)
theorem B3389489 : Blo 2259435 3389489 := bstep (se 2 (by rfl) ⟨1271058, by rfl⟩ : syracuseStep 3389489 = 2542117) B2542117
theorem B2259659 : Blo 2259435 2259659 := bstep (se 1 (by rfl) ⟨1694744, by rfl⟩ : syracuseStep 2259659 = 3389489) B3389489
theorem B4071989 : Blo 2259435 4071989 := bbase (se 5 (by rfl) ⟨190874, by rfl⟩ : syracuseStep 4071989 = 381749) (by norm_num)
theorem B10858637 : Blo 2259435 10858637 := bstep (se 3 (by rfl) ⟨2035994, by rfl⟩ : syracuseStep 10858637 = 4071989) B4071989
theorem B7239091 : Blo 2259435 7239091 := bstep (se 1 (by rfl) ⟨5429318, by rfl⟩ : syracuseStep 7239091 = 10858637) B10858637
theorem B9652121 : Blo 2259435 9652121 := bstep (se 2 (by rfl) ⟨3619545, by rfl⟩ : syracuseStep 9652121 = 7239091) B7239091
theorem B6434747 : Blo 2259435 6434747 := bstep (se 1 (by rfl) ⟨4826060, by rfl⟩ : syracuseStep 6434747 = 9652121) B9652121
theorem B4289831 : Blo 2259435 4289831 := bstep (se 1 (by rfl) ⟨3217373, by rfl⟩ : syracuseStep 4289831 = 6434747) B6434747
theorem B2859887 : Blo 2259435 2859887 := bstep (se 1 (by rfl) ⟨2144915, by rfl⟩ : syracuseStep 2859887 = 4289831) B4289831
theorem B7626365 : Blo 2259435 7626365 := bstep (se 3 (by rfl) ⟨1429943, by rfl⟩ : syracuseStep 7626365 = 2859887) B2859887
theorem B5084243 : Blo 2259435 5084243 := bstep (se 1 (by rfl) ⟨3813182, by rfl⟩ : syracuseStep 5084243 = 7626365) B7626365
theorem B3389495 : Blo 2259435 3389495 := bstep (se 1 (by rfl) ⟨2542121, by rfl⟩ : syracuseStep 3389495 = 5084243) B5084243
theorem B2259663 : Blo 2259435 2259663 := bstep (se 1 (by rfl) ⟨1694747, by rfl⟩ : syracuseStep 2259663 = 3389495) B3389495
theorem B3389501 : Blo 2259435 3389501 := bbase (se 3 (by rfl) ⟨635531, by rfl⟩ : syracuseStep 3389501 = 1271063) (by norm_num)
theorem B2259667 : Blo 2259435 2259667 := bstep (se 1 (by rfl) ⟨1694750, by rfl⟩ : syracuseStep 2259667 = 3389501) B3389501
theorem B5084261 : Blo 2259435 5084261 := bbase (se 4 (by rfl) ⟨476649, by rfl⟩ : syracuseStep 5084261 = 953299) (by norm_num)
theorem B3389507 : Blo 2259435 3389507 := bstep (se 1 (by rfl) ⟨2542130, by rfl⟩ : syracuseStep 3389507 = 5084261) B5084261
theorem B2259671 : Blo 2259435 2259671 := bstep (se 1 (by rfl) ⟨1694753, by rfl⟩ : syracuseStep 2259671 = 3389507) B3389507
theorem B5719805 : Blo 2259435 5719805 := bbase (se 3 (by rfl) ⟨1072463, by rfl⟩ : syracuseStep 5719805 = 2144927) (by norm_num)
theorem B3813203 : Blo 2259435 3813203 := bstep (se 1 (by rfl) ⟨2859902, by rfl⟩ : syracuseStep 3813203 = 5719805) B5719805
theorem B2542135 : Blo 2259435 2542135 := bstep (se 1 (by rfl) ⟨1906601, by rfl⟩ : syracuseStep 2542135 = 3813203) B3813203
theorem B3389513 : Blo 2259435 3389513 := bstep (se 2 (by rfl) ⟨1271067, by rfl⟩ : syracuseStep 3389513 = 2542135) B2542135
theorem B2259675 : Blo 2259435 2259675 := bstep (se 1 (by rfl) ⟨1694756, by rfl⟩ : syracuseStep 2259675 = 3389513) B3389513
theorem B4289861 : Blo 2259435 4289861 := bbase (se 4 (by rfl) ⟨402174, by rfl⟩ : syracuseStep 4289861 = 804349) (by norm_num)
theorem B11439629 : Blo 2259435 11439629 := bstep (se 3 (by rfl) ⟨2144930, by rfl⟩ : syracuseStep 11439629 = 4289861) B4289861
theorem B7626419 : Blo 2259435 7626419 := bstep (se 1 (by rfl) ⟨5719814, by rfl⟩ : syracuseStep 7626419 = 11439629) B11439629
theorem B5084279 : Blo 2259435 5084279 := bstep (se 1 (by rfl) ⟨3813209, by rfl⟩ : syracuseStep 5084279 = 7626419) B7626419
theorem B3389519 : Blo 2259435 3389519 := bstep (se 1 (by rfl) ⟨2542139, by rfl⟩ : syracuseStep 3389519 = 5084279) B5084279
theorem B2259679 : Blo 2259435 2259679 := bstep (se 1 (by rfl) ⟨1694759, by rfl⟩ : syracuseStep 2259679 = 3389519) B3389519
theorem B3389525 : Blo 2259435 3389525 := bbase (se 8 (by rfl) ⟨19860, by rfl⟩ : syracuseStep 3389525 = 39721) (by norm_num)
theorem B2259683 : Blo 2259435 2259683 := bstep (se 1 (by rfl) ⟨1694762, by rfl⟩ : syracuseStep 2259683 = 3389525) B3389525
theorem B13250837 : Blo 2259435 13250837 := bbase (se 6 (by rfl) ⟨310566, by rfl⟩ : syracuseStep 13250837 = 621133) (by norm_num)
theorem B8833891 : Blo 2259435 8833891 := bstep (se 1 (by rfl) ⟨6625418, by rfl⟩ : syracuseStep 8833891 = 13250837) B13250837
theorem B188456341 : Blo 2259435 188456341 := bstep (se 6 (by rfl) ⟨4416945, by rfl⟩ : syracuseStep 188456341 = 8833891) B8833891
theorem B251275121 : Blo 2259435 251275121 := bstep (se 2 (by rfl) ⟨94228170, by rfl⟩ : syracuseStep 251275121 = 188456341) B188456341
theorem B167516747 : Blo 2259435 167516747 := bstep (se 1 (by rfl) ⟨125637560, by rfl⟩ : syracuseStep 167516747 = 251275121) B251275121
theorem B111677831 : Blo 2259435 111677831 := bstep (se 1 (by rfl) ⟨83758373, by rfl⟩ : syracuseStep 111677831 = 167516747) B167516747
theorem B74451887 : Blo 2259435 74451887 := bstep (se 1 (by rfl) ⟨55838915, by rfl⟩ : syracuseStep 74451887 = 111677831) B111677831
theorem B3176613845 : Blo 2259435 3176613845 := bstep (se 7 (by rfl) ⟨37225943, by rfl⟩ : syracuseStep 3176613845 = 74451887) B74451887
theorem B2117742563 : Blo 2259435 2117742563 := bstep (se 1 (by rfl) ⟨1588306922, by rfl⟩ : syracuseStep 2117742563 = 3176613845) B3176613845
theorem B1411828375 : Blo 2259435 1411828375 := bstep (se 1 (by rfl) ⟨1058871281, by rfl⟩ : syracuseStep 1411828375 = 2117742563) B2117742563
theorem B1882437833 : Blo 2259435 1882437833 := bstep (se 2 (by rfl) ⟨705914187, by rfl⟩ : syracuseStep 1882437833 = 1411828375) B1411828375
theorem B1254958555 : Blo 2259435 1254958555 := bstep (se 1 (by rfl) ⟨941218916, by rfl⟩ : syracuseStep 1254958555 = 1882437833) B1882437833
theorem B1673278073 : Blo 2259435 1673278073 := bstep (se 2 (by rfl) ⟨627479277, by rfl⟩ : syracuseStep 1673278073 = 1254958555) B1254958555
theorem B1115518715 : Blo 2259435 1115518715 := bstep (se 1 (by rfl) ⟨836639036, by rfl⟩ : syracuseStep 1115518715 = 1673278073) B1673278073
theorem B743679143 : Blo 2259435 743679143 := bstep (se 1 (by rfl) ⟨557759357, by rfl⟩ : syracuseStep 743679143 = 1115518715) B1115518715
theorem B495786095 : Blo 2259435 495786095 := bstep (se 1 (by rfl) ⟨371839571, by rfl⟩ : syracuseStep 495786095 = 743679143) B743679143
theorem B330524063 : Blo 2259435 330524063 := bstep (se 1 (by rfl) ⟨247893047, by rfl⟩ : syracuseStep 330524063 = 495786095) B495786095
theorem B220349375 : Blo 2259435 220349375 := bstep (se 1 (by rfl) ⟨165262031, by rfl⟩ : syracuseStep 220349375 = 330524063) B330524063
theorem B146899583 : Blo 2259435 146899583 := bstep (se 1 (by rfl) ⟨110174687, by rfl⟩ : syracuseStep 146899583 = 220349375) B220349375
theorem B97933055 : Blo 2259435 97933055 := bstep (se 1 (by rfl) ⟨73449791, by rfl⟩ : syracuseStep 97933055 = 146899583) B146899583
theorem B1044619253 : Blo 2259435 1044619253 := bstep (se 5 (by rfl) ⟨48966527, by rfl⟩ : syracuseStep 1044619253 = 97933055) B97933055
theorem B696412835 : Blo 2259435 696412835 := bstep (se 1 (by rfl) ⟨522309626, by rfl⟩ : syracuseStep 696412835 = 1044619253) B1044619253
theorem B464275223 : Blo 2259435 464275223 := bstep (se 1 (by rfl) ⟨348206417, by rfl⟩ : syracuseStep 464275223 = 696412835) B696412835
theorem B309516815 : Blo 2259435 309516815 := bstep (se 1 (by rfl) ⟨232137611, by rfl⟩ : syracuseStep 309516815 = 464275223) B464275223
theorem B206344543 : Blo 2259435 206344543 := bstep (se 1 (by rfl) ⟨154758407, by rfl⟩ : syracuseStep 206344543 = 309516815) B309516815
theorem B275126057 : Blo 2259435 275126057 := bstep (se 2 (by rfl) ⟨103172271, by rfl⟩ : syracuseStep 275126057 = 206344543) B206344543
theorem B183417371 : Blo 2259435 183417371 := bstep (se 1 (by rfl) ⟨137563028, by rfl⟩ : syracuseStep 183417371 = 275126057) B275126057
theorem B122278247 : Blo 2259435 122278247 := bstep (se 1 (by rfl) ⟨91708685, by rfl⟩ : syracuseStep 122278247 = 183417371) B183417371
theorem B81518831 : Blo 2259435 81518831 := bstep (se 1 (by rfl) ⟨61139123, by rfl⟩ : syracuseStep 81518831 = 122278247) B122278247
theorem B54345887 : Blo 2259435 54345887 := bstep (se 1 (by rfl) ⟨40759415, by rfl⟩ : syracuseStep 54345887 = 81518831) B81518831
theorem B579689461 : Blo 2259435 579689461 := bstep (se 5 (by rfl) ⟨27172943, by rfl⟩ : syracuseStep 579689461 = 54345887) B54345887
theorem B772919281 : Blo 2259435 772919281 := bstep (se 2 (by rfl) ⟨289844730, by rfl⟩ : syracuseStep 772919281 = 579689461) B579689461
theorem B1030559041 : Blo 2259435 1030559041 := bstep (se 2 (by rfl) ⟨386459640, by rfl⟩ : syracuseStep 1030559041 = 772919281) B772919281
theorem B1374078721 : Blo 2259435 1374078721 := bstep (se 2 (by rfl) ⟨515279520, by rfl⟩ : syracuseStep 1374078721 = 1030559041) B1030559041
theorem B1832104961 : Blo 2259435 1832104961 := bstep (se 2 (by rfl) ⟨687039360, by rfl⟩ : syracuseStep 1832104961 = 1374078721) B1374078721
theorem B1221403307 : Blo 2259435 1221403307 := bstep (se 1 (by rfl) ⟨916052480, by rfl⟩ : syracuseStep 1221403307 = 1832104961) B1832104961
theorem B3257075485 : Blo 2259435 3257075485 := bstep (se 3 (by rfl) ⟨610701653, by rfl⟩ : syracuseStep 3257075485 = 1221403307) B1221403307
theorem B4342767313 : Blo 2259435 4342767313 := bstep (se 2 (by rfl) ⟨1628537742, by rfl⟩ : syracuseStep 4342767313 = 3257075485) B3257075485
theorem B5790356417 : Blo 2259435 5790356417 := bstep (se 2 (by rfl) ⟨2171383656, by rfl⟩ : syracuseStep 5790356417 = 4342767313) B4342767313
theorem B3860237611 : Blo 2259435 3860237611 := bstep (se 1 (by rfl) ⟨2895178208, by rfl⟩ : syracuseStep 3860237611 = 5790356417) B5790356417
theorem B5146983481 : Blo 2259435 5146983481 := bstep (se 2 (by rfl) ⟨1930118805, by rfl⟩ : syracuseStep 5146983481 = 3860237611) B3860237611
theorem B6862644641 : Blo 2259435 6862644641 := bstep (se 2 (by rfl) ⟨2573491740, by rfl⟩ : syracuseStep 6862644641 = 5146983481) B5146983481
theorem B4575096427 : Blo 2259435 4575096427 := bstep (se 1 (by rfl) ⟨3431322320, by rfl⟩ : syracuseStep 4575096427 = 6862644641) B6862644641
theorem B6100128569 : Blo 2259435 6100128569 := bstep (se 2 (by rfl) ⟨2287548213, by rfl⟩ : syracuseStep 6100128569 = 4575096427) B4575096427
theorem B4066752379 : Blo 2259435 4066752379 := bstep (se 1 (by rfl) ⟨3050064284, by rfl⟩ : syracuseStep 4066752379 = 6100128569) B6100128569
theorem B5422336505 : Blo 2259435 5422336505 := bstep (se 2 (by rfl) ⟨2033376189, by rfl⟩ : syracuseStep 5422336505 = 4066752379) B4066752379
theorem B3614891003 : Blo 2259435 3614891003 := bstep (se 1 (by rfl) ⟨2711168252, by rfl⟩ : syracuseStep 3614891003 = 5422336505) B5422336505
theorem B2409927335 : Blo 2259435 2409927335 := bstep (se 1 (by rfl) ⟨1807445501, by rfl⟩ : syracuseStep 2409927335 = 3614891003) B3614891003
theorem B1606618223 : Blo 2259435 1606618223 := bstep (se 1 (by rfl) ⟨1204963667, by rfl⟩ : syracuseStep 1606618223 = 2409927335) B2409927335
theorem B1071078815 : Blo 2259435 1071078815 := bstep (se 1 (by rfl) ⟨803309111, by rfl⟩ : syracuseStep 1071078815 = 1606618223) B1606618223
theorem B714052543 : Blo 2259435 714052543 := bstep (se 1 (by rfl) ⟨535539407, by rfl⟩ : syracuseStep 714052543 = 1071078815) B1071078815
theorem B952070057 : Blo 2259435 952070057 := bstep (se 2 (by rfl) ⟨357026271, by rfl⟩ : syracuseStep 952070057 = 714052543) B714052543
theorem B634713371 : Blo 2259435 634713371 := bstep (se 1 (by rfl) ⟨476035028, by rfl⟩ : syracuseStep 634713371 = 952070057) B952070057
theorem B423142247 : Blo 2259435 423142247 := bstep (se 1 (by rfl) ⟨317356685, by rfl⟩ : syracuseStep 423142247 = 634713371) B634713371
theorem B282094831 : Blo 2259435 282094831 := bstep (se 1 (by rfl) ⟨211571123, by rfl⟩ : syracuseStep 282094831 = 423142247) B423142247
theorem B1504505765 : Blo 2259435 1504505765 := bstep (se 4 (by rfl) ⟨141047415, by rfl⟩ : syracuseStep 1504505765 = 282094831) B282094831
theorem B1003003843 : Blo 2259435 1003003843 := bstep (se 1 (by rfl) ⟨752252882, by rfl⟩ : syracuseStep 1003003843 = 1504505765) B1504505765
theorem B1337338457 : Blo 2259435 1337338457 := bstep (se 2 (by rfl) ⟨501501921, by rfl⟩ : syracuseStep 1337338457 = 1003003843) B1003003843
theorem B891558971 : Blo 2259435 891558971 := bstep (se 1 (by rfl) ⟨668669228, by rfl⟩ : syracuseStep 891558971 = 1337338457) B1337338457
theorem B594372647 : Blo 2259435 594372647 := bstep (se 1 (by rfl) ⟨445779485, by rfl⟩ : syracuseStep 594372647 = 891558971) B891558971
theorem B396248431 : Blo 2259435 396248431 := bstep (se 1 (by rfl) ⟨297186323, by rfl⟩ : syracuseStep 396248431 = 594372647) B594372647
theorem B528331241 : Blo 2259435 528331241 := bstep (se 2 (by rfl) ⟨198124215, by rfl⟩ : syracuseStep 528331241 = 396248431) B396248431
theorem B352220827 : Blo 2259435 352220827 := bstep (se 1 (by rfl) ⟨264165620, by rfl⟩ : syracuseStep 352220827 = 528331241) B528331241
theorem B469627769 : Blo 2259435 469627769 := bstep (se 2 (by rfl) ⟨176110413, by rfl⟩ : syracuseStep 469627769 = 352220827) B352220827
theorem B313085179 : Blo 2259435 313085179 := bstep (se 1 (by rfl) ⟨234813884, by rfl⟩ : syracuseStep 313085179 = 469627769) B469627769
theorem B417446905 : Blo 2259435 417446905 := bstep (se 2 (by rfl) ⟨156542589, by rfl⟩ : syracuseStep 417446905 = 313085179) B313085179
theorem B556595873 : Blo 2259435 556595873 := bstep (se 2 (by rfl) ⟨208723452, by rfl⟩ : syracuseStep 556595873 = 417446905) B417446905
theorem B371063915 : Blo 2259435 371063915 := bstep (se 1 (by rfl) ⟨278297936, by rfl⟩ : syracuseStep 371063915 = 556595873) B556595873
theorem B247375943 : Blo 2259435 247375943 := bstep (se 1 (by rfl) ⟨185531957, by rfl⟩ : syracuseStep 247375943 = 371063915) B371063915
theorem B164917295 : Blo 2259435 164917295 := bstep (se 1 (by rfl) ⟨123687971, by rfl⟩ : syracuseStep 164917295 = 247375943) B247375943
theorem B109944863 : Blo 2259435 109944863 := bstep (se 1 (by rfl) ⟨82458647, by rfl⟩ : syracuseStep 109944863 = 164917295) B164917295
theorem B73296575 : Blo 2259435 73296575 := bstep (se 1 (by rfl) ⟨54972431, by rfl⟩ : syracuseStep 73296575 = 109944863) B109944863
theorem B48864383 : Blo 2259435 48864383 := bstep (se 1 (by rfl) ⟨36648287, by rfl⟩ : syracuseStep 48864383 = 73296575) B73296575
theorem B32576255 : Blo 2259435 32576255 := bstep (se 1 (by rfl) ⟨24432191, by rfl⟩ : syracuseStep 32576255 = 48864383) B48864383
theorem B21717503 : Blo 2259435 21717503 := bstep (se 1 (by rfl) ⟨16288127, by rfl⟩ : syracuseStep 21717503 = 32576255) B32576255
theorem B14478335 : Blo 2259435 14478335 := bstep (se 1 (by rfl) ⟨10858751, by rfl⟩ : syracuseStep 14478335 = 21717503) B21717503
theorem B9652223 : Blo 2259435 9652223 := bstep (se 1 (by rfl) ⟨7239167, by rfl⟩ : syracuseStep 9652223 = 14478335) B14478335
theorem B6434815 : Blo 2259435 6434815 := bstep (se 1 (by rfl) ⟨4826111, by rfl⟩ : syracuseStep 6434815 = 9652223) B9652223
theorem B8579753 : Blo 2259435 8579753 := bstep (se 2 (by rfl) ⟨3217407, by rfl⟩ : syracuseStep 8579753 = 6434815) B6434815
theorem B5719835 : Blo 2259435 5719835 := bstep (se 1 (by rfl) ⟨4289876, by rfl⟩ : syracuseStep 5719835 = 8579753) B8579753
theorem B3813223 : Blo 2259435 3813223 := bstep (se 1 (by rfl) ⟨2859917, by rfl⟩ : syracuseStep 3813223 = 5719835) B5719835
theorem B5084297 : Blo 2259435 5084297 := bstep (se 2 (by rfl) ⟨1906611, by rfl⟩ : syracuseStep 5084297 = 3813223) B3813223
theorem B3389531 : Blo 2259435 3389531 := bstep (se 1 (by rfl) ⟨2542148, by rfl⟩ : syracuseStep 3389531 = 5084297) B5084297
theorem B2259687 : Blo 2259435 2259687 := bstep (se 1 (by rfl) ⟨1694765, by rfl⟩ : syracuseStep 2259687 = 3389531) B3389531
theorem B2542153 : Blo 2259435 2542153 := bbase (se 2 (by rfl) ⟨953307, by rfl⟩ : syracuseStep 2542153 = 1906615) (by norm_num)
theorem B3389537 : Blo 2259435 3389537 := bstep (se 2 (by rfl) ⟨1271076, by rfl⟩ : syracuseStep 3389537 = 2542153) B2542153
theorem B2259691 : Blo 2259435 2259691 := bstep (se 1 (by rfl) ⟨1694768, by rfl⟩ : syracuseStep 2259691 = 3389537) B3389537
theorem B10858789 : Blo 2259435 10858789 := bbase (se 4 (by rfl) ⟨1018011, by rfl⟩ : syracuseStep 10858789 = 2036023) (by norm_num)
theorem B14478385 : Blo 2259435 14478385 := bstep (se 2 (by rfl) ⟨5429394, by rfl⟩ : syracuseStep 14478385 = 10858789) B10858789
theorem B19304513 : Blo 2259435 19304513 := bstep (se 2 (by rfl) ⟨7239192, by rfl⟩ : syracuseStep 19304513 = 14478385) B14478385
theorem B12869675 : Blo 2259435 12869675 := bstep (se 1 (by rfl) ⟨9652256, by rfl⟩ : syracuseStep 12869675 = 19304513) B19304513
theorem B8579783 : Blo 2259435 8579783 := bstep (se 1 (by rfl) ⟨6434837, by rfl⟩ : syracuseStep 8579783 = 12869675) B12869675
theorem B5719855 : Blo 2259435 5719855 := bstep (se 1 (by rfl) ⟨4289891, by rfl⟩ : syracuseStep 5719855 = 8579783) B8579783
theorem B7626473 : Blo 2259435 7626473 := bstep (se 2 (by rfl) ⟨2859927, by rfl⟩ : syracuseStep 7626473 = 5719855) B5719855
theorem B5084315 : Blo 2259435 5084315 := bstep (se 1 (by rfl) ⟨3813236, by rfl⟩ : syracuseStep 5084315 = 7626473) B7626473
theorem B3389543 : Blo 2259435 3389543 := bstep (se 1 (by rfl) ⟨2542157, by rfl⟩ : syracuseStep 3389543 = 5084315) B5084315
theorem B2259695 : Blo 2259435 2259695 := bstep (se 1 (by rfl) ⟨1694771, by rfl⟩ : syracuseStep 2259695 = 3389543) B3389543
theorem B3389549 : Blo 2259435 3389549 := bbase (se 3 (by rfl) ⟨635540, by rfl⟩ : syracuseStep 3389549 = 1271081) (by norm_num)
theorem B2259699 : Blo 2259435 2259699 := bstep (se 1 (by rfl) ⟨1694774, by rfl⟩ : syracuseStep 2259699 = 3389549) B3389549
theorem B5084333 : Blo 2259435 5084333 := bbase (se 3 (by rfl) ⟨953312, by rfl⟩ : syracuseStep 5084333 = 1906625) (by norm_num)
theorem B3389555 : Blo 2259435 3389555 := bstep (se 1 (by rfl) ⟨2542166, by rfl⟩ : syracuseStep 3389555 = 5084333) B5084333
theorem B2259703 : Blo 2259435 2259703 := bstep (se 1 (by rfl) ⟨1694777, by rfl⟩ : syracuseStep 2259703 = 3389555) B3389555
theorem B4072069 : Blo 2259435 4072069 := bbase (se 4 (by rfl) ⟨381756, by rfl⟩ : syracuseStep 4072069 = 763513) (by norm_num)
theorem B5429425 : Blo 2259435 5429425 := bstep (se 2 (by rfl) ⟨2036034, by rfl⟩ : syracuseStep 5429425 = 4072069) B4072069
theorem B7239233 : Blo 2259435 7239233 := bstep (se 2 (by rfl) ⟨2714712, by rfl⟩ : syracuseStep 7239233 = 5429425) B5429425
theorem B4826155 : Blo 2259435 4826155 := bstep (se 1 (by rfl) ⟨3619616, by rfl⟩ : syracuseStep 4826155 = 7239233) B7239233
theorem B6434873 : Blo 2259435 6434873 := bstep (se 2 (by rfl) ⟨2413077, by rfl⟩ : syracuseStep 6434873 = 4826155) B4826155
theorem B4289915 : Blo 2259435 4289915 := bstep (se 1 (by rfl) ⟨3217436, by rfl⟩ : syracuseStep 4289915 = 6434873) B6434873
theorem B2859943 : Blo 2259435 2859943 := bstep (se 1 (by rfl) ⟨2144957, by rfl⟩ : syracuseStep 2859943 = 4289915) B4289915
theorem B3813257 : Blo 2259435 3813257 := bstep (se 2 (by rfl) ⟨1429971, by rfl⟩ : syracuseStep 3813257 = 2859943) B2859943
theorem B2542171 : Blo 2259435 2542171 := bstep (se 1 (by rfl) ⟨1906628, by rfl⟩ : syracuseStep 2542171 = 3813257) B3813257
theorem B3389561 : Blo 2259435 3389561 := bstep (se 2 (by rfl) ⟨1271085, by rfl⟩ : syracuseStep 3389561 = 2542171) B2542171
theorem B2259707 : Blo 2259435 2259707 := bstep (se 1 (by rfl) ⟨1694780, by rfl⟩ : syracuseStep 2259707 = 3389561) B3389561
theorem B8144149 : Blo 2259435 8144149 := bbase (se 6 (by rfl) ⟨190878, by rfl⟩ : syracuseStep 8144149 = 381757) (by norm_num)
theorem B10858865 : Blo 2259435 10858865 := bstep (se 2 (by rfl) ⟨4072074, by rfl⟩ : syracuseStep 10858865 = 8144149) B8144149
theorem B28956973 : Blo 2259435 28956973 := bstep (se 3 (by rfl) ⟨5429432, by rfl⟩ : syracuseStep 28956973 = 10858865) B10858865
theorem B38609297 : Blo 2259435 38609297 := bstep (se 2 (by rfl) ⟨14478486, by rfl⟩ : syracuseStep 38609297 = 28956973) B28956973
theorem B25739531 : Blo 2259435 25739531 := bstep (se 1 (by rfl) ⟨19304648, by rfl⟩ : syracuseStep 25739531 = 38609297) B38609297
theorem B17159687 : Blo 2259435 17159687 := bstep (se 1 (by rfl) ⟨12869765, by rfl⟩ : syracuseStep 17159687 = 25739531) B25739531
theorem B11439791 : Blo 2259435 11439791 := bstep (se 1 (by rfl) ⟨8579843, by rfl⟩ : syracuseStep 11439791 = 17159687) B17159687
theorem B7626527 : Blo 2259435 7626527 := bstep (se 1 (by rfl) ⟨5719895, by rfl⟩ : syracuseStep 7626527 = 11439791) B11439791
theorem B5084351 : Blo 2259435 5084351 := bstep (se 1 (by rfl) ⟨3813263, by rfl⟩ : syracuseStep 5084351 = 7626527) B7626527
theorem B3389567 : Blo 2259435 3389567 := bstep (se 1 (by rfl) ⟨2542175, by rfl⟩ : syracuseStep 3389567 = 5084351) B5084351
theorem B2259711 : Blo 2259435 2259711 := bstep (se 1 (by rfl) ⟨1694783, by rfl⟩ : syracuseStep 2259711 = 3389567) B3389567
theorem B3389573 : Blo 2259435 3389573 := bbase (se 4 (by rfl) ⟨317772, by rfl⟩ : syracuseStep 3389573 = 635545) (by norm_num)
theorem B2259715 : Blo 2259435 2259715 := bstep (se 1 (by rfl) ⟨1694786, by rfl⟩ : syracuseStep 2259715 = 3389573) B3389573
theorem B3813277 : Blo 2259435 3813277 := bbase (se 3 (by rfl) ⟨714989, by rfl⟩ : syracuseStep 3813277 = 1429979) (by norm_num)
theorem B5084369 : Blo 2259435 5084369 := bstep (se 2 (by rfl) ⟨1906638, by rfl⟩ : syracuseStep 5084369 = 3813277) B3813277
theorem B3389579 : Blo 2259435 3389579 := bstep (se 1 (by rfl) ⟨2542184, by rfl⟩ : syracuseStep 3389579 = 5084369) B5084369
theorem B2259719 : Blo 2259435 2259719 := bstep (se 1 (by rfl) ⟨1694789, by rfl⟩ : syracuseStep 2259719 = 3389579) B3389579
theorem B2542189 : Blo 2259435 2542189 := bbase (se 3 (by rfl) ⟨476660, by rfl⟩ : syracuseStep 2542189 = 953321) (by norm_num)
theorem B3389585 : Blo 2259435 3389585 := bstep (se 2 (by rfl) ⟨1271094, by rfl⟩ : syracuseStep 3389585 = 2542189) B2542189
theorem B2259723 : Blo 2259435 2259723 := bstep (se 1 (by rfl) ⟨1694792, by rfl⟩ : syracuseStep 2259723 = 3389585) B3389585
theorem B7626581 : Blo 2259435 7626581 := bbase (se 9 (by rfl) ⟨22343, by rfl⟩ : syracuseStep 7626581 = 44687) (by norm_num)
theorem B5084387 : Blo 2259435 5084387 := bstep (se 1 (by rfl) ⟨3813290, by rfl⟩ : syracuseStep 5084387 = 7626581) B7626581
theorem B3389591 : Blo 2259435 3389591 := bstep (se 1 (by rfl) ⟨2542193, by rfl⟩ : syracuseStep 3389591 = 5084387) B5084387
theorem B2259727 : Blo 2259435 2259727 := bstep (se 1 (by rfl) ⟨1694795, by rfl⟩ : syracuseStep 2259727 = 3389591) B3389591
theorem B3389597 : Blo 2259435 3389597 := bbase (se 3 (by rfl) ⟨635549, by rfl⟩ : syracuseStep 3389597 = 1271099) (by norm_num)
theorem B2259731 : Blo 2259435 2259731 := bstep (se 1 (by rfl) ⟨1694798, by rfl⟩ : syracuseStep 2259731 = 3389597) B3389597
theorem B5084405 : Blo 2259435 5084405 := bbase (se 5 (by rfl) ⟨238331, by rfl⟩ : syracuseStep 5084405 = 476663) (by norm_num)
theorem B3389603 : Blo 2259435 3389603 := bstep (se 1 (by rfl) ⟨2542202, by rfl⟩ : syracuseStep 3389603 = 5084405) B5084405
theorem B2259735 : Blo 2259435 2259735 := bstep (se 1 (by rfl) ⟨1694801, by rfl⟩ : syracuseStep 2259735 = 3389603) B3389603
theorem B7730677 : Blo 2259435 7730677 := bbase (se 5 (by rfl) ⟨362375, by rfl⟩ : syracuseStep 7730677 = 724751) (by norm_num)
theorem B10307569 : Blo 2259435 10307569 := bstep (se 2 (by rfl) ⟨3865338, by rfl⟩ : syracuseStep 10307569 = 7730677) B7730677
theorem B13743425 : Blo 2259435 13743425 := bstep (se 2 (by rfl) ⟨5153784, by rfl⟩ : syracuseStep 13743425 = 10307569) B10307569
theorem B9162283 : Blo 2259435 9162283 := bstep (se 1 (by rfl) ⟨6871712, by rfl⟩ : syracuseStep 9162283 = 13743425) B13743425
theorem B12216377 : Blo 2259435 12216377 := bstep (se 2 (by rfl) ⟨4581141, by rfl⟩ : syracuseStep 12216377 = 9162283) B9162283
theorem B32577005 : Blo 2259435 32577005 := bstep (se 3 (by rfl) ⟨6108188, by rfl⟩ : syracuseStep 32577005 = 12216377) B12216377
theorem B21718003 : Blo 2259435 21718003 := bstep (se 1 (by rfl) ⟨16288502, by rfl⟩ : syracuseStep 21718003 = 32577005) B32577005
theorem B28957337 : Blo 2259435 28957337 := bstep (se 2 (by rfl) ⟨10859001, by rfl⟩ : syracuseStep 28957337 = 21718003) B21718003
theorem B19304891 : Blo 2259435 19304891 := bstep (se 1 (by rfl) ⟨14478668, by rfl⟩ : syracuseStep 19304891 = 28957337) B28957337
theorem B12869927 : Blo 2259435 12869927 := bstep (se 1 (by rfl) ⟨9652445, by rfl⟩ : syracuseStep 12869927 = 19304891) B19304891
theorem B8579951 : Blo 2259435 8579951 := bstep (se 1 (by rfl) ⟨6434963, by rfl⟩ : syracuseStep 8579951 = 12869927) B12869927
theorem B5719967 : Blo 2259435 5719967 := bstep (se 1 (by rfl) ⟨4289975, by rfl⟩ : syracuseStep 5719967 = 8579951) B8579951
theorem B3813311 : Blo 2259435 3813311 := bstep (se 1 (by rfl) ⟨2859983, by rfl⟩ : syracuseStep 3813311 = 5719967) B5719967
theorem B2542207 : Blo 2259435 2542207 := bstep (se 1 (by rfl) ⟨1906655, by rfl⟩ : syracuseStep 2542207 = 3813311) B3813311
theorem B3389609 : Blo 2259435 3389609 := bstep (se 2 (by rfl) ⟨1271103, by rfl⟩ : syracuseStep 3389609 = 2542207) B2542207
theorem B2259739 : Blo 2259435 2259739 := bstep (se 1 (by rfl) ⟨1694804, by rfl⟩ : syracuseStep 2259739 = 3389609) B3389609
theorem B4072133 : Blo 2259435 4072133 := bbase (se 4 (by rfl) ⟨381762, by rfl⟩ : syracuseStep 4072133 = 763525) (by norm_num)
theorem B10859021 : Blo 2259435 10859021 := bstep (se 3 (by rfl) ⟨2036066, by rfl⟩ : syracuseStep 10859021 = 4072133) B4072133
theorem B7239347 : Blo 2259435 7239347 := bstep (se 1 (by rfl) ⟨5429510, by rfl⟩ : syracuseStep 7239347 = 10859021) B10859021
theorem B4826231 : Blo 2259435 4826231 := bstep (se 1 (by rfl) ⟨3619673, by rfl⟩ : syracuseStep 4826231 = 7239347) B7239347
theorem B3217487 : Blo 2259435 3217487 := bstep (se 1 (by rfl) ⟨2413115, by rfl⟩ : syracuseStep 3217487 = 4826231) B4826231
theorem B8579965 : Blo 2259435 8579965 := bstep (se 3 (by rfl) ⟨1608743, by rfl⟩ : syracuseStep 8579965 = 3217487) B3217487
theorem B11439953 : Blo 2259435 11439953 := bstep (se 2 (by rfl) ⟨4289982, by rfl⟩ : syracuseStep 11439953 = 8579965) B8579965
theorem B7626635 : Blo 2259435 7626635 := bstep (se 1 (by rfl) ⟨5719976, by rfl⟩ : syracuseStep 7626635 = 11439953) B11439953
theorem B5084423 : Blo 2259435 5084423 := bstep (se 1 (by rfl) ⟨3813317, by rfl⟩ : syracuseStep 5084423 = 7626635) B7626635
theorem B3389615 : Blo 2259435 3389615 := bstep (se 1 (by rfl) ⟨2542211, by rfl⟩ : syracuseStep 3389615 = 5084423) B5084423
theorem B2259743 : Blo 2259435 2259743 := bstep (se 1 (by rfl) ⟨1694807, by rfl⟩ : syracuseStep 2259743 = 3389615) B3389615
theorem B3389621 : Blo 2259435 3389621 := bbase (se 5 (by rfl) ⟨158888, by rfl⟩ : syracuseStep 3389621 = 317777) (by norm_num)
theorem B2259747 : Blo 2259435 2259747 := bstep (se 1 (by rfl) ⟨1694810, by rfl⟩ : syracuseStep 2259747 = 3389621) B3389621
theorem B5719997 : Blo 2259435 5719997 := bbase (se 3 (by rfl) ⟨1072499, by rfl⟩ : syracuseStep 5719997 = 2144999) (by norm_num)
theorem B3813331 : Blo 2259435 3813331 := bstep (se 1 (by rfl) ⟨2859998, by rfl⟩ : syracuseStep 3813331 = 5719997) B5719997
theorem B5084441 : Blo 2259435 5084441 := bstep (se 2 (by rfl) ⟨1906665, by rfl⟩ : syracuseStep 5084441 = 3813331) B3813331
theorem B3389627 : Blo 2259435 3389627 := bstep (se 1 (by rfl) ⟨2542220, by rfl⟩ : syracuseStep 3389627 = 5084441) B5084441
theorem B2259751 : Blo 2259435 2259751 := bstep (se 1 (by rfl) ⟨1694813, by rfl⟩ : syracuseStep 2259751 = 3389627) B3389627
theorem B2542225 : Blo 2259435 2542225 := bbase (se 2 (by rfl) ⟨953334, by rfl⟩ : syracuseStep 2542225 = 1906669) (by norm_num)
theorem B3389633 : Blo 2259435 3389633 := bstep (se 2 (by rfl) ⟨1271112, by rfl⟩ : syracuseStep 3389633 = 2542225) B2542225
theorem B2259755 : Blo 2259435 2259755 := bstep (se 1 (by rfl) ⟨1694816, by rfl⟩ : syracuseStep 2259755 = 3389633) B3389633
theorem B4290013 : Blo 2259435 4290013 := bbase (se 3 (by rfl) ⟨804377, by rfl⟩ : syracuseStep 4290013 = 1608755) (by norm_num)
theorem B5720017 : Blo 2259435 5720017 := bstep (se 2 (by rfl) ⟨2145006, by rfl⟩ : syracuseStep 5720017 = 4290013) B4290013
theorem B7626689 : Blo 2259435 7626689 := bstep (se 2 (by rfl) ⟨2860008, by rfl⟩ : syracuseStep 7626689 = 5720017) B5720017
theorem B5084459 : Blo 2259435 5084459 := bstep (se 1 (by rfl) ⟨3813344, by rfl⟩ : syracuseStep 5084459 = 7626689) B7626689
theorem B3389639 : Blo 2259435 3389639 := bstep (se 1 (by rfl) ⟨2542229, by rfl⟩ : syracuseStep 3389639 = 5084459) B5084459
theorem B2259759 : Blo 2259435 2259759 := bstep (se 1 (by rfl) ⟨1694819, by rfl⟩ : syracuseStep 2259759 = 3389639) B3389639
theorem B3389645 : Blo 2259435 3389645 := bbase (se 3 (by rfl) ⟨635558, by rfl⟩ : syracuseStep 3389645 = 1271117) (by norm_num)
theorem B2259763 : Blo 2259435 2259763 := bstep (se 1 (by rfl) ⟨1694822, by rfl⟩ : syracuseStep 2259763 = 3389645) B3389645
theorem B5084477 : Blo 2259435 5084477 := bbase (se 3 (by rfl) ⟨953339, by rfl⟩ : syracuseStep 5084477 = 1906679) (by norm_num)
theorem B3389651 : Blo 2259435 3389651 := bstep (se 1 (by rfl) ⟨2542238, by rfl⟩ : syracuseStep 3389651 = 5084477) B5084477
theorem B2259767 : Blo 2259435 2259767 := bstep (se 1 (by rfl) ⟨1694825, by rfl⟩ : syracuseStep 2259767 = 3389651) B3389651
theorem B3813365 : Blo 2259435 3813365 := bbase (se 5 (by rfl) ⟨178751, by rfl⟩ : syracuseStep 3813365 = 357503) (by norm_num)
theorem B2542243 : Blo 2259435 2542243 := bstep (se 1 (by rfl) ⟨1906682, by rfl⟩ : syracuseStep 2542243 = 3813365) B3813365
theorem B3389657 : Blo 2259435 3389657 := bstep (se 2 (by rfl) ⟨1271121, by rfl⟩ : syracuseStep 3389657 = 2542243) B2542243
theorem B2259771 : Blo 2259435 2259771 := bstep (se 1 (by rfl) ⟨1694828, by rfl⟩ : syracuseStep 2259771 = 3389657) B3389657
theorem B23192405 : Blo 2259435 23192405 := bbase (se 9 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 23192405 = 135893) (by norm_num)
theorem B15461603 : Blo 2259435 15461603 := bstep (se 1 (by rfl) ⟨11596202, by rfl⟩ : syracuseStep 15461603 = 23192405) B23192405
theorem B10307735 : Blo 2259435 10307735 := bstep (se 1 (by rfl) ⟨7730801, by rfl⟩ : syracuseStep 10307735 = 15461603) B15461603
theorem B6871823 : Blo 2259435 6871823 := bstep (se 1 (by rfl) ⟨5153867, by rfl⟩ : syracuseStep 6871823 = 10307735) B10307735
theorem B4581215 : Blo 2259435 4581215 := bstep (se 1 (by rfl) ⟨3435911, by rfl⟩ : syracuseStep 4581215 = 6871823) B6871823
theorem B3054143 : Blo 2259435 3054143 := bstep (se 1 (by rfl) ⟨2290607, by rfl⟩ : syracuseStep 3054143 = 4581215) B4581215
theorem B8144381 : Blo 2259435 8144381 := bstep (se 3 (by rfl) ⟨1527071, by rfl⟩ : syracuseStep 8144381 = 3054143) B3054143
theorem B5429587 : Blo 2259435 5429587 := bstep (se 1 (by rfl) ⟨4072190, by rfl⟩ : syracuseStep 5429587 = 8144381) B8144381
theorem B7239449 : Blo 2259435 7239449 := bstep (se 2 (by rfl) ⟨2714793, by rfl⟩ : syracuseStep 7239449 = 5429587) B5429587
theorem B4826299 : Blo 2259435 4826299 := bstep (se 1 (by rfl) ⟨3619724, by rfl⟩ : syracuseStep 4826299 = 7239449) B7239449
theorem B6435065 : Blo 2259435 6435065 := bstep (se 2 (by rfl) ⟨2413149, by rfl⟩ : syracuseStep 6435065 = 4826299) B4826299
theorem B17160173 : Blo 2259435 17160173 := bstep (se 3 (by rfl) ⟨3217532, by rfl⟩ : syracuseStep 17160173 = 6435065) B6435065
theorem B11440115 : Blo 2259435 11440115 := bstep (se 1 (by rfl) ⟨8580086, by rfl⟩ : syracuseStep 11440115 = 17160173) B17160173
theorem B7626743 : Blo 2259435 7626743 := bstep (se 1 (by rfl) ⟨5720057, by rfl⟩ : syracuseStep 7626743 = 11440115) B11440115
theorem B5084495 : Blo 2259435 5084495 := bstep (se 1 (by rfl) ⟨3813371, by rfl⟩ : syracuseStep 5084495 = 7626743) B7626743
theorem B3389663 : Blo 2259435 3389663 := bstep (se 1 (by rfl) ⟨2542247, by rfl⟩ : syracuseStep 3389663 = 5084495) B5084495
theorem B2259775 : Blo 2259435 2259775 := bstep (se 1 (by rfl) ⟨1694831, by rfl⟩ : syracuseStep 2259775 = 3389663) B3389663
theorem B3389669 : Blo 2259435 3389669 := bbase (se 4 (by rfl) ⟨317781, by rfl⟩ : syracuseStep 3389669 = 635563) (by norm_num)
theorem B2259779 : Blo 2259435 2259779 := bstep (se 1 (by rfl) ⟨1694834, by rfl⟩ : syracuseStep 2259779 = 3389669) B3389669
theorem B4826317 : Blo 2259435 4826317 := bbase (se 3 (by rfl) ⟨904934, by rfl⟩ : syracuseStep 4826317 = 1809869) (by norm_num)
theorem B6435089 : Blo 2259435 6435089 := bstep (se 2 (by rfl) ⟨2413158, by rfl⟩ : syracuseStep 6435089 = 4826317) B4826317
theorem B4290059 : Blo 2259435 4290059 := bstep (se 1 (by rfl) ⟨3217544, by rfl⟩ : syracuseStep 4290059 = 6435089) B6435089
theorem B2860039 : Blo 2259435 2860039 := bstep (se 1 (by rfl) ⟨2145029, by rfl⟩ : syracuseStep 2860039 = 4290059) B4290059
theorem B3813385 : Blo 2259435 3813385 := bstep (se 2 (by rfl) ⟨1430019, by rfl⟩ : syracuseStep 3813385 = 2860039) B2860039
theorem B5084513 : Blo 2259435 5084513 := bstep (se 2 (by rfl) ⟨1906692, by rfl⟩ : syracuseStep 5084513 = 3813385) B3813385
theorem B3389675 : Blo 2259435 3389675 := bstep (se 1 (by rfl) ⟨2542256, by rfl⟩ : syracuseStep 3389675 = 5084513) B5084513
theorem B2259783 : Blo 2259435 2259783 := bstep (se 1 (by rfl) ⟨1694837, by rfl⟩ : syracuseStep 2259783 = 3389675) B3389675
theorem B2542261 : Blo 2259435 2542261 := bbase (se 5 (by rfl) ⟨119168, by rfl⟩ : syracuseStep 2542261 = 238337) (by norm_num)
theorem B3389681 : Blo 2259435 3389681 := bstep (se 2 (by rfl) ⟨1271130, by rfl⟩ : syracuseStep 3389681 = 2542261) B2542261
theorem B2259787 : Blo 2259435 2259787 := bstep (se 1 (by rfl) ⟨1694840, by rfl⟩ : syracuseStep 2259787 = 3389681) B3389681
theorem B2860049 : Blo 2259435 2860049 := bbase (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) (by norm_num)
theorem B7626797 : Blo 2259435 7626797 := bstep (se 3 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 7626797 = 2860049) B2860049
theorem B5084531 : Blo 2259435 5084531 := bstep (se 1 (by rfl) ⟨3813398, by rfl⟩ : syracuseStep 5084531 = 7626797) B7626797
theorem B3389687 : Blo 2259435 3389687 := bstep (se 1 (by rfl) ⟨2542265, by rfl⟩ : syracuseStep 3389687 = 5084531) B5084531
theorem B2259791 : Blo 2259435 2259791 := bstep (se 1 (by rfl) ⟨1694843, by rfl⟩ : syracuseStep 2259791 = 3389687) B3389687
theorem B3389693 : Blo 2259435 3389693 := bbase (se 3 (by rfl) ⟨635567, by rfl⟩ : syracuseStep 3389693 = 1271135) (by norm_num)
theorem B2259795 : Blo 2259435 2259795 := bstep (se 1 (by rfl) ⟨1694846, by rfl⟩ : syracuseStep 2259795 = 3389693) B3389693
theorem B5084549 : Blo 2259435 5084549 := bbase (se 4 (by rfl) ⟨476676, by rfl⟩ : syracuseStep 5084549 = 953353) (by norm_num)
theorem B3389699 : Blo 2259435 3389699 := bstep (se 1 (by rfl) ⟨2542274, by rfl⟩ : syracuseStep 3389699 = 5084549) B5084549
theorem B2259799 : Blo 2259435 2259799 := bstep (se 1 (by rfl) ⟨1694849, by rfl⟩ : syracuseStep 2259799 = 3389699) B3389699
theorem B3217573 : Blo 2259435 3217573 := bbase (se 4 (by rfl) ⟨301647, by rfl⟩ : syracuseStep 3217573 = 603295) (by norm_num)
theorem B4290097 : Blo 2259435 4290097 := bstep (se 2 (by rfl) ⟨1608786, by rfl⟩ : syracuseStep 4290097 = 3217573) B3217573
theorem B5720129 : Blo 2259435 5720129 := bstep (se 2 (by rfl) ⟨2145048, by rfl⟩ : syracuseStep 5720129 = 4290097) B4290097
theorem B3813419 : Blo 2259435 3813419 := bstep (se 1 (by rfl) ⟨2860064, by rfl⟩ : syracuseStep 3813419 = 5720129) B5720129
theorem B2542279 : Blo 2259435 2542279 := bstep (se 1 (by rfl) ⟨1906709, by rfl⟩ : syracuseStep 2542279 = 3813419) B3813419
theorem B3389705 : Blo 2259435 3389705 := bstep (se 2 (by rfl) ⟨1271139, by rfl⟩ : syracuseStep 3389705 = 2542279) B2542279
theorem B2259803 : Blo 2259435 2259803 := bstep (se 1 (by rfl) ⟨1694852, by rfl⟩ : syracuseStep 2259803 = 3389705) B3389705
theorem B11440277 : Blo 2259435 11440277 := bbase (se 6 (by rfl) ⟨268131, by rfl⟩ : syracuseStep 11440277 = 536263) (by norm_num)
theorem B7626851 : Blo 2259435 7626851 := bstep (se 1 (by rfl) ⟨5720138, by rfl⟩ : syracuseStep 7626851 = 11440277) B11440277
theorem B5084567 : Blo 2259435 5084567 := bstep (se 1 (by rfl) ⟨3813425, by rfl⟩ : syracuseStep 5084567 = 7626851) B7626851
theorem B3389711 : Blo 2259435 3389711 := bstep (se 1 (by rfl) ⟨2542283, by rfl⟩ : syracuseStep 3389711 = 5084567) B5084567
theorem B2259807 : Blo 2259435 2259807 := bstep (se 1 (by rfl) ⟨1694855, by rfl⟩ : syracuseStep 2259807 = 3389711) B3389711
theorem B3389717 : Blo 2259435 3389717 := bbase (se 6 (by rfl) ⟨79446, by rfl⟩ : syracuseStep 3389717 = 158893) (by norm_num)
theorem B2259811 : Blo 2259435 2259811 := bstep (se 1 (by rfl) ⟨1694858, by rfl⟩ : syracuseStep 2259811 = 3389717) B3389717
theorem B3054197 : Blo 2259435 3054197 := bbase (se 5 (by rfl) ⟨143165, by rfl⟩ : syracuseStep 3054197 = 286331) (by norm_num)
theorem B8144525 : Blo 2259435 8144525 := bstep (se 3 (by rfl) ⟨1527098, by rfl⟩ : syracuseStep 8144525 = 3054197) B3054197
theorem B5429683 : Blo 2259435 5429683 := bstep (se 1 (by rfl) ⟨4072262, by rfl⟩ : syracuseStep 5429683 = 8144525) B8144525
theorem B28958309 : Blo 2259435 28958309 := bstep (se 4 (by rfl) ⟨2714841, by rfl⟩ : syracuseStep 28958309 = 5429683) B5429683
theorem B19305539 : Blo 2259435 19305539 := bstep (se 1 (by rfl) ⟨14479154, by rfl⟩ : syracuseStep 19305539 = 28958309) B28958309
theorem B12870359 : Blo 2259435 12870359 := bstep (se 1 (by rfl) ⟨9652769, by rfl⟩ : syracuseStep 12870359 = 19305539) B19305539
theorem B8580239 : Blo 2259435 8580239 := bstep (se 1 (by rfl) ⟨6435179, by rfl⟩ : syracuseStep 8580239 = 12870359) B12870359
theorem B5720159 : Blo 2259435 5720159 := bstep (se 1 (by rfl) ⟨4290119, by rfl⟩ : syracuseStep 5720159 = 8580239) B8580239
theorem B3813439 : Blo 2259435 3813439 := bstep (se 1 (by rfl) ⟨2860079, by rfl⟩ : syracuseStep 3813439 = 5720159) B5720159
theorem B5084585 : Blo 2259435 5084585 := bstep (se 2 (by rfl) ⟨1906719, by rfl⟩ : syracuseStep 5084585 = 3813439) B3813439
theorem B3389723 : Blo 2259435 3389723 := bstep (se 1 (by rfl) ⟨2542292, by rfl⟩ : syracuseStep 3389723 = 5084585) B5084585
theorem B2259815 : Blo 2259435 2259815 := bstep (se 1 (by rfl) ⟨1694861, by rfl⟩ : syracuseStep 2259815 = 3389723) B3389723
theorem B2542297 : Blo 2259435 2542297 := bbase (se 2 (by rfl) ⟨953361, by rfl⟩ : syracuseStep 2542297 = 1906723) (by norm_num)
theorem B3389729 : Blo 2259435 3389729 := bstep (se 2 (by rfl) ⟨1271148, by rfl⟩ : syracuseStep 3389729 = 2542297) B2542297
theorem B2259819 : Blo 2259435 2259819 := bstep (se 1 (by rfl) ⟨1694864, by rfl⟩ : syracuseStep 2259819 = 3389729) B3389729
theorem B2413201 : Blo 2259435 2413201 := bbase (se 2 (by rfl) ⟨904950, by rfl⟩ : syracuseStep 2413201 = 1809901) (by norm_num)
theorem B3217601 : Blo 2259435 3217601 := bstep (se 2 (by rfl) ⟨1206600, by rfl⟩ : syracuseStep 3217601 = 2413201) B2413201
theorem B8580269 : Blo 2259435 8580269 := bstep (se 3 (by rfl) ⟨1608800, by rfl⟩ : syracuseStep 8580269 = 3217601) B3217601
theorem B5720179 : Blo 2259435 5720179 := bstep (se 1 (by rfl) ⟨4290134, by rfl⟩ : syracuseStep 5720179 = 8580269) B8580269
theorem B7626905 : Blo 2259435 7626905 := bstep (se 2 (by rfl) ⟨2860089, by rfl⟩ : syracuseStep 7626905 = 5720179) B5720179
theorem B5084603 : Blo 2259435 5084603 := bstep (se 1 (by rfl) ⟨3813452, by rfl⟩ : syracuseStep 5084603 = 7626905) B7626905
theorem B3389735 : Blo 2259435 3389735 := bstep (se 1 (by rfl) ⟨2542301, by rfl⟩ : syracuseStep 3389735 = 5084603) B5084603
theorem B2259823 : Blo 2259435 2259823 := bstep (se 1 (by rfl) ⟨1694867, by rfl⟩ : syracuseStep 2259823 = 3389735) B3389735
theorem B3389741 : Blo 2259435 3389741 := bbase (se 3 (by rfl) ⟨635576, by rfl⟩ : syracuseStep 3389741 = 1271153) (by norm_num)
theorem B2259827 : Blo 2259435 2259827 := bstep (se 1 (by rfl) ⟨1694870, by rfl⟩ : syracuseStep 2259827 = 3389741) B3389741
theorem B5084621 : Blo 2259435 5084621 := bbase (se 3 (by rfl) ⟨953366, by rfl⟩ : syracuseStep 5084621 = 1906733) (by norm_num)
theorem B3389747 : Blo 2259435 3389747 := bstep (se 1 (by rfl) ⟨2542310, by rfl⟩ : syracuseStep 3389747 = 5084621) B5084621
theorem B2259831 : Blo 2259435 2259831 := bstep (se 1 (by rfl) ⟨1694873, by rfl⟩ : syracuseStep 2259831 = 3389747) B3389747
theorem B2860105 : Blo 2259435 2860105 := bbase (se 2 (by rfl) ⟨1072539, by rfl⟩ : syracuseStep 2860105 = 2145079) (by norm_num)
theorem B3813473 : Blo 2259435 3813473 := bstep (se 2 (by rfl) ⟨1430052, by rfl⟩ : syracuseStep 3813473 = 2860105) B2860105
theorem B2542315 : Blo 2259435 2542315 := bstep (se 1 (by rfl) ⟨1906736, by rfl⟩ : syracuseStep 2542315 = 3813473) B3813473
theorem B3389753 : Blo 2259435 3389753 := bstep (se 2 (by rfl) ⟨1271157, by rfl⟩ : syracuseStep 3389753 = 2542315) B2542315
theorem B2259835 : Blo 2259435 2259835 := bstep (se 1 (by rfl) ⟨1694876, by rfl⟩ : syracuseStep 2259835 = 3389753) B3389753
theorem B3054229 : Blo 2259435 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B16289221 : Blo 2259435 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B21718961 : Blo 2259435 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B14479307 : Blo 2259435 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B9652871 : Blo 2259435 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B25740989 : Blo 2259435 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B17160659 : Blo 2259435 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B11440439 : Blo 2259435 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B7626959 : Blo 2259435 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B5084639 : Blo 2259435 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B3389759 : Blo 2259435 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B2259839 : Blo 2259435 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B3389765 : Blo 2259435 3389765 := bbase (se 4 (by rfl) ⟨317790, by rfl⟩ : syracuseStep 3389765 = 635581) (by norm_num)
theorem B2259843 : Blo 2259435 2259843 := bstep (se 1 (by rfl) ⟨1694882, by rfl⟩ : syracuseStep 2259843 = 3389765) B3389765
theorem B3813493 : Blo 2259435 3813493 := bbase (se 5 (by rfl) ⟨178757, by rfl⟩ : syracuseStep 3813493 = 357515) (by norm_num)
theorem B5084657 : Blo 2259435 5084657 := bstep (se 2 (by rfl) ⟨1906746, by rfl⟩ : syracuseStep 5084657 = 3813493) B3813493
theorem B3389771 : Blo 2259435 3389771 := bstep (se 1 (by rfl) ⟨2542328, by rfl⟩ : syracuseStep 3389771 = 5084657) B5084657
theorem B2259847 : Blo 2259435 2259847 := bstep (se 1 (by rfl) ⟨1694885, by rfl⟩ : syracuseStep 2259847 = 3389771) B3389771
theorem B2542333 : Blo 2259435 2542333 := bbase (se 3 (by rfl) ⟨476687, by rfl⟩ : syracuseStep 2542333 = 953375) (by norm_num)
theorem B3389777 : Blo 2259435 3389777 := bstep (se 2 (by rfl) ⟨1271166, by rfl⟩ : syracuseStep 3389777 = 2542333) B2542333
theorem B2259851 : Blo 2259435 2259851 := bstep (se 1 (by rfl) ⟨1694888, by rfl⟩ : syracuseStep 2259851 = 3389777) B3389777
theorem B7627013 : Blo 2259435 7627013 := bbase (se 4 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 7627013 = 1430065) (by norm_num)
theorem B5084675 : Blo 2259435 5084675 := bstep (se 1 (by rfl) ⟨3813506, by rfl⟩ : syracuseStep 5084675 = 7627013) B7627013
theorem B3389783 : Blo 2259435 3389783 := bstep (se 1 (by rfl) ⟨2542337, by rfl⟩ : syracuseStep 3389783 = 5084675) B5084675
theorem B2259855 : Blo 2259435 2259855 := bstep (se 1 (by rfl) ⟨1694891, by rfl⟩ : syracuseStep 2259855 = 3389783) B3389783
theorem B3389789 : Blo 2259435 3389789 := bbase (se 3 (by rfl) ⟨635585, by rfl⟩ : syracuseStep 3389789 = 1271171) (by norm_num)
theorem B2259859 : Blo 2259435 2259859 := bstep (se 1 (by rfl) ⟨1694894, by rfl⟩ : syracuseStep 2259859 = 3389789) B3389789
theorem B5084693 : Blo 2259435 5084693 := bbase (se 6 (by rfl) ⟨119172, by rfl⟩ : syracuseStep 5084693 = 238345) (by norm_num)
theorem B3389795 : Blo 2259435 3389795 := bstep (se 1 (by rfl) ⟨2542346, by rfl⟩ : syracuseStep 3389795 = 5084693) B5084693
theorem B2259863 : Blo 2259435 2259863 := bstep (se 1 (by rfl) ⟨1694897, by rfl⟩ : syracuseStep 2259863 = 3389795) B3389795
theorem B8580437 : Blo 2259435 8580437 := bbase (se 11 (by rfl) ⟨6284, by rfl⟩ : syracuseStep 8580437 = 12569) (by norm_num)
theorem B5720291 : Blo 2259435 5720291 := bstep (se 1 (by rfl) ⟨4290218, by rfl⟩ : syracuseStep 5720291 = 8580437) B8580437
theorem B3813527 : Blo 2259435 3813527 := bstep (se 1 (by rfl) ⟨2860145, by rfl⟩ : syracuseStep 3813527 = 5720291) B5720291
theorem B2542351 : Blo 2259435 2542351 := bstep (se 1 (by rfl) ⟨1906763, by rfl⟩ : syracuseStep 2542351 = 3813527) B3813527
theorem B3389801 : Blo 2259435 3389801 := bstep (se 2 (by rfl) ⟨1271175, by rfl⟩ : syracuseStep 3389801 = 2542351) B2542351
theorem B2259867 : Blo 2259435 2259867 := bstep (se 1 (by rfl) ⟨1694900, by rfl⟩ : syracuseStep 2259867 = 3389801) B3389801
theorem B12870677 : Blo 2259435 12870677 := bbase (se 6 (by rfl) ⟨301656, by rfl⟩ : syracuseStep 12870677 = 603313) (by norm_num)
theorem B8580451 : Blo 2259435 8580451 := bstep (se 1 (by rfl) ⟨6435338, by rfl⟩ : syracuseStep 8580451 = 12870677) B12870677
theorem B11440601 : Blo 2259435 11440601 := bstep (se 2 (by rfl) ⟨4290225, by rfl⟩ : syracuseStep 11440601 = 8580451) B8580451
theorem B7627067 : Blo 2259435 7627067 := bstep (se 1 (by rfl) ⟨5720300, by rfl⟩ : syracuseStep 7627067 = 11440601) B11440601
theorem B5084711 : Blo 2259435 5084711 := bstep (se 1 (by rfl) ⟨3813533, by rfl⟩ : syracuseStep 5084711 = 7627067) B7627067
theorem B3389807 : Blo 2259435 3389807 := bstep (se 1 (by rfl) ⟨2542355, by rfl⟩ : syracuseStep 3389807 = 5084711) B5084711
theorem B2259871 : Blo 2259435 2259871 := bstep (se 1 (by rfl) ⟨1694903, by rfl⟩ : syracuseStep 2259871 = 3389807) B3389807
theorem B3389813 : Blo 2259435 3389813 := bbase (se 5 (by rfl) ⟨158897, by rfl⟩ : syracuseStep 3389813 = 317795) (by norm_num)
theorem B2259875 : Blo 2259435 2259875 := bstep (se 1 (by rfl) ⟨1694906, by rfl⟩ : syracuseStep 2259875 = 3389813) B3389813
theorem B2413261 : Blo 2259435 2413261 := bbase (se 3 (by rfl) ⟨452486, by rfl⟩ : syracuseStep 2413261 = 904973) (by norm_num)
theorem B3217681 : Blo 2259435 3217681 := bstep (se 2 (by rfl) ⟨1206630, by rfl⟩ : syracuseStep 3217681 = 2413261) B2413261
theorem B4290241 : Blo 2259435 4290241 := bstep (se 2 (by rfl) ⟨1608840, by rfl⟩ : syracuseStep 4290241 = 3217681) B3217681
theorem B5720321 : Blo 2259435 5720321 := bstep (se 2 (by rfl) ⟨2145120, by rfl⟩ : syracuseStep 5720321 = 4290241) B4290241
theorem B3813547 : Blo 2259435 3813547 := bstep (se 1 (by rfl) ⟨2860160, by rfl⟩ : syracuseStep 3813547 = 5720321) B5720321
theorem B5084729 : Blo 2259435 5084729 := bstep (se 2 (by rfl) ⟨1906773, by rfl⟩ : syracuseStep 5084729 = 3813547) B3813547
theorem B3389819 : Blo 2259435 3389819 := bstep (se 1 (by rfl) ⟨2542364, by rfl⟩ : syracuseStep 3389819 = 5084729) B5084729
theorem B2259879 : Blo 2259435 2259879 := bstep (se 1 (by rfl) ⟨1694909, by rfl⟩ : syracuseStep 2259879 = 3389819) B3389819
theorem B2542369 : Blo 2259435 2542369 := bbase (se 2 (by rfl) ⟨953388, by rfl⟩ : syracuseStep 2542369 = 1906777) (by norm_num)
theorem B3389825 : Blo 2259435 3389825 := bstep (se 2 (by rfl) ⟨1271184, by rfl⟩ : syracuseStep 3389825 = 2542369) B2542369
theorem B2259883 : Blo 2259435 2259883 := bstep (se 1 (by rfl) ⟨1694912, by rfl⟩ : syracuseStep 2259883 = 3389825) B3389825
theorem B5720341 : Blo 2259435 5720341 := bbase (se 6 (by rfl) ⟨134070, by rfl⟩ : syracuseStep 5720341 = 268141) (by norm_num)
theorem B7627121 : Blo 2259435 7627121 := bstep (se 2 (by rfl) ⟨2860170, by rfl⟩ : syracuseStep 7627121 = 5720341) B5720341
theorem B5084747 : Blo 2259435 5084747 := bstep (se 1 (by rfl) ⟨3813560, by rfl⟩ : syracuseStep 5084747 = 7627121) B7627121
theorem B3389831 : Blo 2259435 3389831 := bstep (se 1 (by rfl) ⟨2542373, by rfl⟩ : syracuseStep 3389831 = 5084747) B5084747
theorem B2259887 : Blo 2259435 2259887 := bstep (se 1 (by rfl) ⟨1694915, by rfl⟩ : syracuseStep 2259887 = 3389831) B3389831
theorem B3389837 : Blo 2259435 3389837 := bbase (se 3 (by rfl) ⟨635594, by rfl⟩ : syracuseStep 3389837 = 1271189) (by norm_num)
theorem B2259891 : Blo 2259435 2259891 := bstep (se 1 (by rfl) ⟨1694918, by rfl⟩ : syracuseStep 2259891 = 3389837) B3389837
theorem B5084765 : Blo 2259435 5084765 := bbase (se 3 (by rfl) ⟨953393, by rfl⟩ : syracuseStep 5084765 = 1906787) (by norm_num)
theorem B3389843 : Blo 2259435 3389843 := bstep (se 1 (by rfl) ⟨2542382, by rfl⟩ : syracuseStep 3389843 = 5084765) B5084765
theorem B2259895 : Blo 2259435 2259895 := bstep (se 1 (by rfl) ⟨1694921, by rfl⟩ : syracuseStep 2259895 = 3389843) B3389843
theorem B3813581 : Blo 2259435 3813581 := bbase (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) (by norm_num)
theorem B2542387 : Blo 2259435 2542387 := bstep (se 1 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 2542387 = 3813581) B3813581
theorem B3389849 : Blo 2259435 3389849 := bstep (se 2 (by rfl) ⟨1271193, by rfl⟩ : syracuseStep 3389849 = 2542387) B2542387
theorem B2259899 : Blo 2259435 2259899 := bstep (se 1 (by rfl) ⟨1694924, by rfl⟩ : syracuseStep 2259899 = 3389849) B3389849
theorem B4072421 : Blo 2259435 4072421 := bbase (se 4 (by rfl) ⟨381789, by rfl⟩ : syracuseStep 4072421 = 763579) (by norm_num)
theorem B2714947 : Blo 2259435 2714947 := bstep (se 1 (by rfl) ⟨2036210, by rfl⟩ : syracuseStep 2714947 = 4072421) B4072421
theorem B14479717 : Blo 2259435 14479717 := bstep (se 4 (by rfl) ⟨1357473, by rfl⟩ : syracuseStep 14479717 = 2714947) B2714947
theorem B19306289 : Blo 2259435 19306289 := bstep (se 2 (by rfl) ⟨7239858, by rfl⟩ : syracuseStep 19306289 = 14479717) B14479717
theorem B12870859 : Blo 2259435 12870859 := bstep (se 1 (by rfl) ⟨9653144, by rfl⟩ : syracuseStep 12870859 = 19306289) B19306289
theorem B17161145 : Blo 2259435 17161145 := bstep (se 2 (by rfl) ⟨6435429, by rfl⟩ : syracuseStep 17161145 = 12870859) B12870859
theorem B11440763 : Blo 2259435 11440763 := bstep (se 1 (by rfl) ⟨8580572, by rfl⟩ : syracuseStep 11440763 = 17161145) B17161145
theorem B7627175 : Blo 2259435 7627175 := bstep (se 1 (by rfl) ⟨5720381, by rfl⟩ : syracuseStep 7627175 = 11440763) B11440763
theorem B5084783 : Blo 2259435 5084783 := bstep (se 1 (by rfl) ⟨3813587, by rfl⟩ : syracuseStep 5084783 = 7627175) B7627175
theorem B3389855 : Blo 2259435 3389855 := bstep (se 1 (by rfl) ⟨2542391, by rfl⟩ : syracuseStep 3389855 = 5084783) B5084783
theorem B2259903 : Blo 2259435 2259903 := bstep (se 1 (by rfl) ⟨1694927, by rfl⟩ : syracuseStep 2259903 = 3389855) B3389855
theorem B3389861 : Blo 2259435 3389861 := bbase (se 4 (by rfl) ⟨317799, by rfl⟩ : syracuseStep 3389861 = 635599) (by norm_num)
theorem B2259907 : Blo 2259435 2259907 := bstep (se 1 (by rfl) ⟨1694930, by rfl⟩ : syracuseStep 2259907 = 3389861) B3389861
theorem B2860201 : Blo 2259435 2860201 := bbase (se 2 (by rfl) ⟨1072575, by rfl⟩ : syracuseStep 2860201 = 2145151) (by norm_num)
theorem B3813601 : Blo 2259435 3813601 := bstep (se 2 (by rfl) ⟨1430100, by rfl⟩ : syracuseStep 3813601 = 2860201) B2860201
theorem B5084801 : Blo 2259435 5084801 := bstep (se 2 (by rfl) ⟨1906800, by rfl⟩ : syracuseStep 5084801 = 3813601) B3813601
theorem B3389867 : Blo 2259435 3389867 := bstep (se 1 (by rfl) ⟨2542400, by rfl⟩ : syracuseStep 3389867 = 5084801) B5084801
theorem B2259911 : Blo 2259435 2259911 := bstep (se 1 (by rfl) ⟨1694933, by rfl⟩ : syracuseStep 2259911 = 3389867) B3389867
theorem B2542405 : Blo 2259435 2542405 := bbase (se 4 (by rfl) ⟨238350, by rfl⟩ : syracuseStep 2542405 = 476701) (by norm_num)
theorem B3389873 : Blo 2259435 3389873 := bstep (se 2 (by rfl) ⟨1271202, by rfl⟩ : syracuseStep 3389873 = 2542405) B2542405
theorem B2259915 : Blo 2259435 2259915 := bstep (se 1 (by rfl) ⟨1694936, by rfl⟩ : syracuseStep 2259915 = 3389873) B3389873
theorem B4290317 : Blo 2259435 4290317 := bbase (se 3 (by rfl) ⟨804434, by rfl⟩ : syracuseStep 4290317 = 1608869) (by norm_num)
theorem B2860211 : Blo 2259435 2860211 := bstep (se 1 (by rfl) ⟨2145158, by rfl⟩ : syracuseStep 2860211 = 4290317) B4290317
theorem B7627229 : Blo 2259435 7627229 := bstep (se 3 (by rfl) ⟨1430105, by rfl⟩ : syracuseStep 7627229 = 2860211) B2860211
theorem B5084819 : Blo 2259435 5084819 := bstep (se 1 (by rfl) ⟨3813614, by rfl⟩ : syracuseStep 5084819 = 7627229) B7627229
theorem B3389879 : Blo 2259435 3389879 := bstep (se 1 (by rfl) ⟨2542409, by rfl⟩ : syracuseStep 3389879 = 5084819) B5084819
theorem B2259919 : Blo 2259435 2259919 := bstep (se 1 (by rfl) ⟨1694939, by rfl⟩ : syracuseStep 2259919 = 3389879) B3389879
theorem B3389885 : Blo 2259435 3389885 := bbase (se 3 (by rfl) ⟨635603, by rfl⟩ : syracuseStep 3389885 = 1271207) (by norm_num)
theorem B2259923 : Blo 2259435 2259923 := bstep (se 1 (by rfl) ⟨1694942, by rfl⟩ : syracuseStep 2259923 = 3389885) B3389885
theorem B5084837 : Blo 2259435 5084837 := bbase (se 4 (by rfl) ⟨476703, by rfl⟩ : syracuseStep 5084837 = 953407) (by norm_num)
theorem B3389891 : Blo 2259435 3389891 := bstep (se 1 (by rfl) ⟨2542418, by rfl⟩ : syracuseStep 3389891 = 5084837) B5084837
theorem B2259927 : Blo 2259435 2259927 := bstep (se 1 (by rfl) ⟨1694945, by rfl⟩ : syracuseStep 2259927 = 3389891) B3389891
theorem B5720453 : Blo 2259435 5720453 := bbase (se 4 (by rfl) ⟨536292, by rfl⟩ : syracuseStep 5720453 = 1072585) (by norm_num)
theorem B3813635 : Blo 2259435 3813635 := bstep (se 1 (by rfl) ⟨2860226, by rfl⟩ : syracuseStep 3813635 = 5720453) B5720453
theorem B2542423 : Blo 2259435 2542423 := bstep (se 1 (by rfl) ⟨1906817, by rfl⟩ : syracuseStep 2542423 = 3813635) B3813635
theorem B3389897 : Blo 2259435 3389897 := bstep (se 2 (by rfl) ⟨1271211, by rfl⟩ : syracuseStep 3389897 = 2542423) B2542423
theorem B2259931 : Blo 2259435 2259931 := bstep (se 1 (by rfl) ⟨1694948, by rfl⟩ : syracuseStep 2259931 = 3389897) B3389897
theorem B3619981 : Blo 2259435 3619981 := bbase (se 3 (by rfl) ⟨678746, by rfl⟩ : syracuseStep 3619981 = 1357493) (by norm_num)
theorem B4826641 : Blo 2259435 4826641 := bstep (se 2 (by rfl) ⟨1809990, by rfl⟩ : syracuseStep 4826641 = 3619981) B3619981
theorem B6435521 : Blo 2259435 6435521 := bstep (se 2 (by rfl) ⟨2413320, by rfl⟩ : syracuseStep 6435521 = 4826641) B4826641
theorem B4290347 : Blo 2259435 4290347 := bstep (se 1 (by rfl) ⟨3217760, by rfl⟩ : syracuseStep 4290347 = 6435521) B6435521
theorem B11440925 : Blo 2259435 11440925 := bstep (se 3 (by rfl) ⟨2145173, by rfl⟩ : syracuseStep 11440925 = 4290347) B4290347
theorem B7627283 : Blo 2259435 7627283 := bstep (se 1 (by rfl) ⟨5720462, by rfl⟩ : syracuseStep 7627283 = 11440925) B11440925
theorem B5084855 : Blo 2259435 5084855 := bstep (se 1 (by rfl) ⟨3813641, by rfl⟩ : syracuseStep 5084855 = 7627283) B7627283
theorem B3389903 : Blo 2259435 3389903 := bstep (se 1 (by rfl) ⟨2542427, by rfl⟩ : syracuseStep 3389903 = 5084855) B5084855
theorem B2259935 : Blo 2259435 2259935 := bstep (se 1 (by rfl) ⟨1694951, by rfl⟩ : syracuseStep 2259935 = 3389903) B3389903
theorem B3389909 : Blo 2259435 3389909 := bbase (se 7 (by rfl) ⟨39725, by rfl⟩ : syracuseStep 3389909 = 79451) (by norm_num)
theorem B2259939 : Blo 2259435 2259939 := bstep (se 1 (by rfl) ⟨1694954, by rfl⟩ : syracuseStep 2259939 = 3389909) B3389909
theorem B8580725 : Blo 2259435 8580725 := bbase (se 5 (by rfl) ⟨402221, by rfl⟩ : syracuseStep 8580725 = 804443) (by norm_num)
theorem B5720483 : Blo 2259435 5720483 := bstep (se 1 (by rfl) ⟨4290362, by rfl⟩ : syracuseStep 5720483 = 8580725) B8580725
theorem B3813655 : Blo 2259435 3813655 := bstep (se 1 (by rfl) ⟨2860241, by rfl⟩ : syracuseStep 3813655 = 5720483) B5720483
theorem B5084873 : Blo 2259435 5084873 := bstep (se 2 (by rfl) ⟨1906827, by rfl⟩ : syracuseStep 5084873 = 3813655) B3813655
theorem B3389915 : Blo 2259435 3389915 := bstep (se 1 (by rfl) ⟨2542436, by rfl⟩ : syracuseStep 3389915 = 5084873) B5084873
theorem B2259943 : Blo 2259435 2259943 := bstep (se 1 (by rfl) ⟨1694957, by rfl⟩ : syracuseStep 2259943 = 3389915) B3389915
theorem B2542441 : Blo 2259435 2542441 := bbase (se 2 (by rfl) ⟨953415, by rfl⟩ : syracuseStep 2542441 = 1906831) (by norm_num)
theorem B3389921 : Blo 2259435 3389921 := bstep (se 2 (by rfl) ⟨1271220, by rfl⟩ : syracuseStep 3389921 = 2542441) B2542441
theorem B2259947 : Blo 2259435 2259947 := bstep (se 1 (by rfl) ⟨1694960, by rfl⟩ : syracuseStep 2259947 = 3389921) B3389921
theorem B2715005 : Blo 2259435 2715005 := bbase (se 3 (by rfl) ⟨509063, by rfl⟩ : syracuseStep 2715005 = 1018127) (by norm_num)
theorem B7240013 : Blo 2259435 7240013 := bstep (se 3 (by rfl) ⟨1357502, by rfl⟩ : syracuseStep 7240013 = 2715005) B2715005
theorem B4826675 : Blo 2259435 4826675 := bstep (se 1 (by rfl) ⟨3620006, by rfl⟩ : syracuseStep 4826675 = 7240013) B7240013
theorem B12871133 : Blo 2259435 12871133 := bstep (se 3 (by rfl) ⟨2413337, by rfl⟩ : syracuseStep 12871133 = 4826675) B4826675
theorem B8580755 : Blo 2259435 8580755 := bstep (se 1 (by rfl) ⟨6435566, by rfl⟩ : syracuseStep 8580755 = 12871133) B12871133
theorem B5720503 : Blo 2259435 5720503 := bstep (se 1 (by rfl) ⟨4290377, by rfl⟩ : syracuseStep 5720503 = 8580755) B8580755
theorem B7627337 : Blo 2259435 7627337 := bstep (se 2 (by rfl) ⟨2860251, by rfl⟩ : syracuseStep 7627337 = 5720503) B5720503
theorem B5084891 : Blo 2259435 5084891 := bstep (se 1 (by rfl) ⟨3813668, by rfl⟩ : syracuseStep 5084891 = 7627337) B7627337
theorem B3389927 : Blo 2259435 3389927 := bstep (se 1 (by rfl) ⟨2542445, by rfl⟩ : syracuseStep 3389927 = 5084891) B5084891
theorem B2259951 : Blo 2259435 2259951 := bstep (se 1 (by rfl) ⟨1694963, by rfl⟩ : syracuseStep 2259951 = 3389927) B3389927
theorem B3389933 : Blo 2259435 3389933 := bbase (se 3 (by rfl) ⟨635612, by rfl⟩ : syracuseStep 3389933 = 1271225) (by norm_num)
theorem B2259955 : Blo 2259435 2259955 := bstep (se 1 (by rfl) ⟨1694966, by rfl⟩ : syracuseStep 2259955 = 3389933) B3389933
theorem B5084909 : Blo 2259435 5084909 := bbase (se 3 (by rfl) ⟨953420, by rfl⟩ : syracuseStep 5084909 = 1906841) (by norm_num)
theorem B3389939 : Blo 2259435 3389939 := bstep (se 1 (by rfl) ⟨2542454, by rfl⟩ : syracuseStep 3389939 = 5084909) B5084909
theorem B2259959 : Blo 2259435 2259959 := bstep (se 1 (by rfl) ⟨1694969, by rfl⟩ : syracuseStep 2259959 = 3389939) B3389939
theorem B3918469 : Blo 2259435 3918469 := bbase (se 4 (by rfl) ⟨367356, by rfl⟩ : syracuseStep 3918469 = 734713) (by norm_num)
theorem B5224625 : Blo 2259435 5224625 := bstep (se 2 (by rfl) ⟨1959234, by rfl⟩ : syracuseStep 5224625 = 3918469) B3918469
theorem B3483083 : Blo 2259435 3483083 := bstep (se 1 (by rfl) ⟨2612312, by rfl⟩ : syracuseStep 3483083 = 5224625) B5224625
theorem B2322055 : Blo 2259435 2322055 := bstep (se 1 (by rfl) ⟨1741541, by rfl⟩ : syracuseStep 2322055 = 3483083) B3483083
theorem B3096073 : Blo 2259435 3096073 := bstep (se 2 (by rfl) ⟨1161027, by rfl⟩ : syracuseStep 3096073 = 2322055) B2322055
theorem B4128097 : Blo 2259435 4128097 := bstep (se 2 (by rfl) ⟨1548036, by rfl⟩ : syracuseStep 4128097 = 3096073) B3096073
theorem B5504129 : Blo 2259435 5504129 := bstep (se 2 (by rfl) ⟨2064048, by rfl⟩ : syracuseStep 5504129 = 4128097) B4128097
theorem B3669419 : Blo 2259435 3669419 := bstep (se 1 (by rfl) ⟨2752064, by rfl⟩ : syracuseStep 3669419 = 5504129) B5504129
theorem B9785117 : Blo 2259435 9785117 := bstep (se 3 (by rfl) ⟨1834709, by rfl⟩ : syracuseStep 9785117 = 3669419) B3669419
theorem B6523411 : Blo 2259435 6523411 := bstep (se 1 (by rfl) ⟨4892558, by rfl⟩ : syracuseStep 6523411 = 9785117) B9785117
theorem B8697881 : Blo 2259435 8697881 := bstep (se 2 (by rfl) ⟨3261705, by rfl⟩ : syracuseStep 8697881 = 6523411) B6523411
theorem B5798587 : Blo 2259435 5798587 := bstep (se 1 (by rfl) ⟨4348940, by rfl⟩ : syracuseStep 5798587 = 8697881) B8697881
theorem B7731449 : Blo 2259435 7731449 := bstep (se 2 (by rfl) ⟨2899293, by rfl⟩ : syracuseStep 7731449 = 5798587) B5798587
theorem B5154299 : Blo 2259435 5154299 := bstep (se 1 (by rfl) ⟨3865724, by rfl⟩ : syracuseStep 5154299 = 7731449) B7731449
theorem B3436199 : Blo 2259435 3436199 := bstep (se 1 (by rfl) ⟨2577149, by rfl⟩ : syracuseStep 3436199 = 5154299) B5154299
theorem B2290799 : Blo 2259435 2290799 := bstep (se 1 (by rfl) ⟨1718099, by rfl⟩ : syracuseStep 2290799 = 3436199) B3436199
theorem B6108797 : Blo 2259435 6108797 := bstep (se 3 (by rfl) ⟨1145399, by rfl⟩ : syracuseStep 6108797 = 2290799) B2290799
theorem B4072531 : Blo 2259435 4072531 := bstep (se 1 (by rfl) ⟨3054398, by rfl⟩ : syracuseStep 4072531 = 6108797) B6108797
theorem B5430041 : Blo 2259435 5430041 := bstep (se 2 (by rfl) ⟨2036265, by rfl⟩ : syracuseStep 5430041 = 4072531) B4072531
theorem B3620027 : Blo 2259435 3620027 := bstep (se 1 (by rfl) ⟨2715020, by rfl⟩ : syracuseStep 3620027 = 5430041) B5430041
theorem B2413351 : Blo 2259435 2413351 := bstep (se 1 (by rfl) ⟨1810013, by rfl⟩ : syracuseStep 2413351 = 3620027) B3620027
theorem B3217801 : Blo 2259435 3217801 := bstep (se 2 (by rfl) ⟨1206675, by rfl⟩ : syracuseStep 3217801 = 2413351) B2413351
theorem B4290401 : Blo 2259435 4290401 := bstep (se 2 (by rfl) ⟨1608900, by rfl⟩ : syracuseStep 4290401 = 3217801) B3217801
theorem B2860267 : Blo 2259435 2860267 := bstep (se 1 (by rfl) ⟨2145200, by rfl⟩ : syracuseStep 2860267 = 4290401) B4290401
theorem B3813689 : Blo 2259435 3813689 := bstep (se 2 (by rfl) ⟨1430133, by rfl⟩ : syracuseStep 3813689 = 2860267) B2860267
theorem B2542459 : Blo 2259435 2542459 := bstep (se 1 (by rfl) ⟨1906844, by rfl⟩ : syracuseStep 2542459 = 3813689) B3813689
theorem B3389945 : Blo 2259435 3389945 := bstep (se 2 (by rfl) ⟨1271229, by rfl⟩ : syracuseStep 3389945 = 2542459) B2542459
theorem B2259963 : Blo 2259435 2259963 := bstep (se 1 (by rfl) ⟨1694972, by rfl⟩ : syracuseStep 2259963 = 3389945) B3389945
theorem B3719485 : Blo 2259435 3719485 := bbase (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) (by norm_num)
theorem B4959313 : Blo 2259435 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B26449669 : Blo 2259435 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B35266225 : Blo 2259435 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B47021633 : Blo 2259435 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B31347755 : Blo 2259435 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B20898503 : Blo 2259435 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B13932335 : Blo 2259435 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B37152893 : Blo 2259435 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B24768595 : Blo 2259435 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B33024793 : Blo 2259435 33024793 := bstep (se 2 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 33024793 = 24768595) B24768595
theorem B44033057 : Blo 2259435 44033057 := bstep (se 2 (by rfl) ⟨16512396, by rfl⟩ : syracuseStep 44033057 = 33024793) B33024793
theorem B29355371 : Blo 2259435 29355371 := bstep (se 1 (by rfl) ⟨22016528, by rfl⟩ : syracuseStep 29355371 = 44033057) B44033057
theorem B19570247 : Blo 2259435 19570247 := bstep (se 1 (by rfl) ⟨14677685, by rfl⟩ : syracuseStep 19570247 = 29355371) B29355371
theorem B13046831 : Blo 2259435 13046831 := bstep (se 1 (by rfl) ⟨9785123, by rfl⟩ : syracuseStep 13046831 = 19570247) B19570247
theorem B8697887 : Blo 2259435 8697887 := bstep (se 1 (by rfl) ⟨6523415, by rfl⟩ : syracuseStep 8697887 = 13046831) B13046831
theorem B5798591 : Blo 2259435 5798591 := bstep (se 1 (by rfl) ⟨4348943, by rfl⟩ : syracuseStep 5798591 = 8697887) B8697887
theorem B61851637 : Blo 2259435 61851637 := bstep (se 5 (by rfl) ⟨2899295, by rfl⟩ : syracuseStep 61851637 = 5798591) B5798591
theorem B82468849 : Blo 2259435 82468849 := bstep (se 2 (by rfl) ⟨30925818, by rfl⟩ : syracuseStep 82468849 = 61851637) B61851637
theorem B109958465 : Blo 2259435 109958465 := bstep (se 2 (by rfl) ⟨41234424, by rfl⟩ : syracuseStep 109958465 = 82468849) B82468849
theorem B73305643 : Blo 2259435 73305643 := bstep (se 1 (by rfl) ⟨54979232, by rfl⟩ : syracuseStep 73305643 = 109958465) B109958465
theorem B97740857 : Blo 2259435 97740857 := bstep (se 2 (by rfl) ⟨36652821, by rfl⟩ : syracuseStep 97740857 = 73305643) B73305643
theorem B65160571 : Blo 2259435 65160571 := bstep (se 1 (by rfl) ⟨48870428, by rfl⟩ : syracuseStep 65160571 = 97740857) B97740857
theorem B86880761 : Blo 2259435 86880761 := bstep (se 2 (by rfl) ⟨32580285, by rfl⟩ : syracuseStep 86880761 = 65160571) B65160571
theorem B57920507 : Blo 2259435 57920507 := bstep (se 1 (by rfl) ⟨43440380, by rfl⟩ : syracuseStep 57920507 = 86880761) B86880761
theorem B38613671 : Blo 2259435 38613671 := bstep (se 1 (by rfl) ⟨28960253, by rfl⟩ : syracuseStep 38613671 = 57920507) B57920507
theorem B25742447 : Blo 2259435 25742447 := bstep (se 1 (by rfl) ⟨19306835, by rfl⟩ : syracuseStep 25742447 = 38613671) B38613671
theorem B17161631 : Blo 2259435 17161631 := bstep (se 1 (by rfl) ⟨12871223, by rfl⟩ : syracuseStep 17161631 = 25742447) B25742447
theorem B11441087 : Blo 2259435 11441087 := bstep (se 1 (by rfl) ⟨8580815, by rfl⟩ : syracuseStep 11441087 = 17161631) B17161631
theorem B7627391 : Blo 2259435 7627391 := bstep (se 1 (by rfl) ⟨5720543, by rfl⟩ : syracuseStep 7627391 = 11441087) B11441087
theorem B5084927 : Blo 2259435 5084927 := bstep (se 1 (by rfl) ⟨3813695, by rfl⟩ : syracuseStep 5084927 = 7627391) B7627391
theorem B3389951 : Blo 2259435 3389951 := bstep (se 1 (by rfl) ⟨2542463, by rfl⟩ : syracuseStep 3389951 = 5084927) B5084927
theorem B2259967 : Blo 2259435 2259967 := bstep (se 1 (by rfl) ⟨1694975, by rfl⟩ : syracuseStep 2259967 = 3389951) B3389951
theorem B3389957 : Blo 2259435 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B2259971 : Blo 2259435 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B3813709 : Blo 2259435 3813709 := bbase (se 3 (by rfl) ⟨715070, by rfl⟩ : syracuseStep 3813709 = 1430141) (by norm_num)
theorem B5084945 : Blo 2259435 5084945 := bstep (se 2 (by rfl) ⟨1906854, by rfl⟩ : syracuseStep 5084945 = 3813709) B3813709
theorem B3389963 : Blo 2259435 3389963 := bstep (se 1 (by rfl) ⟨2542472, by rfl⟩ : syracuseStep 3389963 = 5084945) B5084945
theorem B2259975 : Blo 2259435 2259975 := bstep (se 1 (by rfl) ⟨1694981, by rfl⟩ : syracuseStep 2259975 = 3389963) B3389963
theorem B2542477 : Blo 2259435 2542477 := bbase (se 3 (by rfl) ⟨476714, by rfl⟩ : syracuseStep 2542477 = 953429) (by norm_num)
theorem B3389969 : Blo 2259435 3389969 := bstep (se 2 (by rfl) ⟨1271238, by rfl⟩ : syracuseStep 3389969 = 2542477) B2542477
theorem B2259979 : Blo 2259435 2259979 := bstep (se 1 (by rfl) ⟨1694984, by rfl⟩ : syracuseStep 2259979 = 3389969) B3389969
theorem B7627445 : Blo 2259435 7627445 := bbase (se 5 (by rfl) ⟨357536, by rfl⟩ : syracuseStep 7627445 = 715073) (by norm_num)
theorem B5084963 : Blo 2259435 5084963 := bstep (se 1 (by rfl) ⟨3813722, by rfl⟩ : syracuseStep 5084963 = 7627445) B7627445
theorem B3389975 : Blo 2259435 3389975 := bstep (se 1 (by rfl) ⟨2542481, by rfl⟩ : syracuseStep 3389975 = 5084963) B5084963
theorem B2259983 : Blo 2259435 2259983 := bstep (se 1 (by rfl) ⟨1694987, by rfl⟩ : syracuseStep 2259983 = 3389975) B3389975
theorem B3389981 : Blo 2259435 3389981 := bbase (se 3 (by rfl) ⟨635621, by rfl⟩ : syracuseStep 3389981 = 1271243) (by norm_num)
theorem B2259987 : Blo 2259435 2259987 := bstep (se 1 (by rfl) ⟨1694990, by rfl⟩ : syracuseStep 2259987 = 3389981) B3389981
theorem B5084981 : Blo 2259435 5084981 := bbase (se 5 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 5084981 = 476717) (by norm_num)
theorem B3389987 : Blo 2259435 3389987 := bstep (se 1 (by rfl) ⟨2542490, by rfl⟩ : syracuseStep 3389987 = 5084981) B5084981
theorem B2259991 : Blo 2259435 2259991 := bstep (se 1 (by rfl) ⟨1694993, by rfl⟩ : syracuseStep 2259991 = 3389987) B3389987
theorem B14480309 : Blo 2259435 14480309 := bbase (se 5 (by rfl) ⟨678764, by rfl⟩ : syracuseStep 14480309 = 1357529) (by norm_num)
theorem B9653539 : Blo 2259435 9653539 := bstep (se 1 (by rfl) ⟨7240154, by rfl⟩ : syracuseStep 9653539 = 14480309) B14480309
theorem B12871385 : Blo 2259435 12871385 := bstep (se 2 (by rfl) ⟨4826769, by rfl⟩ : syracuseStep 12871385 = 9653539) B9653539
theorem B8580923 : Blo 2259435 8580923 := bstep (se 1 (by rfl) ⟨6435692, by rfl⟩ : syracuseStep 8580923 = 12871385) B12871385
theorem B5720615 : Blo 2259435 5720615 := bstep (se 1 (by rfl) ⟨4290461, by rfl⟩ : syracuseStep 5720615 = 8580923) B8580923
theorem B3813743 : Blo 2259435 3813743 := bstep (se 1 (by rfl) ⟨2860307, by rfl⟩ : syracuseStep 3813743 = 5720615) B5720615
theorem B2542495 : Blo 2259435 2542495 := bstep (se 1 (by rfl) ⟨1906871, by rfl⟩ : syracuseStep 2542495 = 3813743) B3813743
theorem B3389993 : Blo 2259435 3389993 := bstep (se 2 (by rfl) ⟨1271247, by rfl⟩ : syracuseStep 3389993 = 2542495) B2542495
theorem B2259995 : Blo 2259435 2259995 := bstep (se 1 (by rfl) ⟨1694996, by rfl⟩ : syracuseStep 2259995 = 3389993) B3389993
theorem B5430125 : Blo 2259435 5430125 := bbase (se 3 (by rfl) ⟨1018148, by rfl⟩ : syracuseStep 5430125 = 2036297) (by norm_num)
theorem B14480333 : Blo 2259435 14480333 := bstep (se 3 (by rfl) ⟨2715062, by rfl⟩ : syracuseStep 14480333 = 5430125) B5430125
theorem B9653555 : Blo 2259435 9653555 := bstep (se 1 (by rfl) ⟨7240166, by rfl⟩ : syracuseStep 9653555 = 14480333) B14480333
theorem B6435703 : Blo 2259435 6435703 := bstep (se 1 (by rfl) ⟨4826777, by rfl⟩ : syracuseStep 6435703 = 9653555) B9653555
theorem B8580937 : Blo 2259435 8580937 := bstep (se 2 (by rfl) ⟨3217851, by rfl⟩ : syracuseStep 8580937 = 6435703) B6435703
theorem B11441249 : Blo 2259435 11441249 := bstep (se 2 (by rfl) ⟨4290468, by rfl⟩ : syracuseStep 11441249 = 8580937) B8580937
theorem B7627499 : Blo 2259435 7627499 := bstep (se 1 (by rfl) ⟨5720624, by rfl⟩ : syracuseStep 7627499 = 11441249) B11441249
theorem B5084999 : Blo 2259435 5084999 := bstep (se 1 (by rfl) ⟨3813749, by rfl⟩ : syracuseStep 5084999 = 7627499) B7627499
theorem B3389999 : Blo 2259435 3389999 := bstep (se 1 (by rfl) ⟨2542499, by rfl⟩ : syracuseStep 3389999 = 5084999) B5084999
theorem B2259999 : Blo 2259435 2259999 := bstep (se 1 (by rfl) ⟨1694999, by rfl⟩ : syracuseStep 2259999 = 3389999) B3389999
theorem B3390005 : Blo 2259435 3390005 := bbase (se 5 (by rfl) ⟨158906, by rfl⟩ : syracuseStep 3390005 = 317813) (by norm_num)
theorem B2260003 : Blo 2259435 2260003 := bstep (se 1 (by rfl) ⟨1695002, by rfl⟩ : syracuseStep 2260003 = 3390005) B3390005
theorem B5720645 : Blo 2259435 5720645 := bbase (se 4 (by rfl) ⟨536310, by rfl⟩ : syracuseStep 5720645 = 1072621) (by norm_num)
theorem B3813763 : Blo 2259435 3813763 := bstep (se 1 (by rfl) ⟨2860322, by rfl⟩ : syracuseStep 3813763 = 5720645) B5720645
theorem B5085017 : Blo 2259435 5085017 := bstep (se 2 (by rfl) ⟨1906881, by rfl⟩ : syracuseStep 5085017 = 3813763) B3813763
theorem B3390011 : Blo 2259435 3390011 := bstep (se 1 (by rfl) ⟨2542508, by rfl⟩ : syracuseStep 3390011 = 5085017) B5085017
theorem B2260007 : Blo 2259435 2260007 := bstep (se 1 (by rfl) ⟨1695005, by rfl⟩ : syracuseStep 2260007 = 3390011) B3390011
theorem B2542513 : Blo 2259435 2542513 := bbase (se 2 (by rfl) ⟨953442, by rfl⟩ : syracuseStep 2542513 = 1906885) (by norm_num)
theorem B3390017 : Blo 2259435 3390017 := bstep (se 2 (by rfl) ⟨1271256, by rfl⟩ : syracuseStep 3390017 = 2542513) B2542513
theorem B2260011 : Blo 2259435 2260011 := bstep (se 1 (by rfl) ⟨1695008, by rfl⟩ : syracuseStep 2260011 = 3390017) B3390017
theorem B6435749 : Blo 2259435 6435749 := bbase (se 4 (by rfl) ⟨603351, by rfl⟩ : syracuseStep 6435749 = 1206703) (by norm_num)
theorem B4290499 : Blo 2259435 4290499 := bstep (se 1 (by rfl) ⟨3217874, by rfl⟩ : syracuseStep 4290499 = 6435749) B6435749
theorem B5720665 : Blo 2259435 5720665 := bstep (se 2 (by rfl) ⟨2145249, by rfl⟩ : syracuseStep 5720665 = 4290499) B4290499
theorem B7627553 : Blo 2259435 7627553 := bstep (se 2 (by rfl) ⟨2860332, by rfl⟩ : syracuseStep 7627553 = 5720665) B5720665
theorem B5085035 : Blo 2259435 5085035 := bstep (se 1 (by rfl) ⟨3813776, by rfl⟩ : syracuseStep 5085035 = 7627553) B7627553
theorem B3390023 : Blo 2259435 3390023 := bstep (se 1 (by rfl) ⟨2542517, by rfl⟩ : syracuseStep 3390023 = 5085035) B5085035
theorem B2260015 : Blo 2259435 2260015 := bstep (se 1 (by rfl) ⟨1695011, by rfl⟩ : syracuseStep 2260015 = 3390023) B3390023
theorem B3390029 : Blo 2259435 3390029 := bbase (se 3 (by rfl) ⟨635630, by rfl⟩ : syracuseStep 3390029 = 1271261) (by norm_num)
theorem B2260019 : Blo 2259435 2260019 := bstep (se 1 (by rfl) ⟨1695014, by rfl⟩ : syracuseStep 2260019 = 3390029) B3390029
theorem B5085053 : Blo 2259435 5085053 := bbase (se 3 (by rfl) ⟨953447, by rfl⟩ : syracuseStep 5085053 = 1906895) (by norm_num)
theorem B3390035 : Blo 2259435 3390035 := bstep (se 1 (by rfl) ⟨2542526, by rfl⟩ : syracuseStep 3390035 = 5085053) B5085053
theorem B2260023 : Blo 2259435 2260023 := bstep (se 1 (by rfl) ⟨1695017, by rfl⟩ : syracuseStep 2260023 = 3390035) B3390035
theorem B3813797 : Blo 2259435 3813797 := bbase (se 4 (by rfl) ⟨357543, by rfl⟩ : syracuseStep 3813797 = 715087) (by norm_num)
theorem B2542531 : Blo 2259435 2542531 := bstep (se 1 (by rfl) ⟨1906898, by rfl⟩ : syracuseStep 2542531 = 3813797) B3813797
theorem B3390041 : Blo 2259435 3390041 := bstep (se 2 (by rfl) ⟨1271265, by rfl⟩ : syracuseStep 3390041 = 2542531) B2542531
theorem B2260027 : Blo 2259435 2260027 := bstep (se 1 (by rfl) ⟨1695020, by rfl⟩ : syracuseStep 2260027 = 3390041) B3390041
theorem B3436301 : Blo 2259435 3436301 := bbase (se 3 (by rfl) ⟨644306, by rfl⟩ : syracuseStep 3436301 = 1288613) (by norm_num)
theorem B9163469 : Blo 2259435 9163469 := bstep (se 3 (by rfl) ⟨1718150, by rfl⟩ : syracuseStep 9163469 = 3436301) B3436301
theorem B6108979 : Blo 2259435 6108979 := bstep (se 1 (by rfl) ⟨4581734, by rfl⟩ : syracuseStep 6108979 = 9163469) B9163469
theorem B8145305 : Blo 2259435 8145305 := bstep (se 2 (by rfl) ⟨3054489, by rfl⟩ : syracuseStep 8145305 = 6108979) B6108979
theorem B5430203 : Blo 2259435 5430203 := bstep (se 1 (by rfl) ⟨4072652, by rfl⟩ : syracuseStep 5430203 = 8145305) B8145305
theorem B3620135 : Blo 2259435 3620135 := bstep (se 1 (by rfl) ⟨2715101, by rfl⟩ : syracuseStep 3620135 = 5430203) B5430203
theorem B2413423 : Blo 2259435 2413423 := bstep (se 1 (by rfl) ⟨1810067, by rfl⟩ : syracuseStep 2413423 = 3620135) B3620135
theorem B3217897 : Blo 2259435 3217897 := bstep (se 2 (by rfl) ⟨1206711, by rfl⟩ : syracuseStep 3217897 = 2413423) B2413423
theorem B17162117 : Blo 2259435 17162117 := bstep (se 4 (by rfl) ⟨1608948, by rfl⟩ : syracuseStep 17162117 = 3217897) B3217897
theorem B11441411 : Blo 2259435 11441411 := bstep (se 1 (by rfl) ⟨8581058, by rfl⟩ : syracuseStep 11441411 = 17162117) B17162117
theorem B7627607 : Blo 2259435 7627607 := bstep (se 1 (by rfl) ⟨5720705, by rfl⟩ : syracuseStep 7627607 = 11441411) B11441411
theorem B5085071 : Blo 2259435 5085071 := bstep (se 1 (by rfl) ⟨3813803, by rfl⟩ : syracuseStep 5085071 = 7627607) B7627607
theorem B3390047 : Blo 2259435 3390047 := bstep (se 1 (by rfl) ⟨2542535, by rfl⟩ : syracuseStep 3390047 = 5085071) B5085071
theorem B2260031 : Blo 2259435 2260031 := bstep (se 1 (by rfl) ⟨1695023, by rfl⟩ : syracuseStep 2260031 = 3390047) B3390047
theorem B3390053 : Blo 2259435 3390053 := bbase (se 4 (by rfl) ⟨317817, by rfl⟩ : syracuseStep 3390053 = 635635) (by norm_num)
theorem B2260035 : Blo 2259435 2260035 := bstep (se 1 (by rfl) ⟨1695026, by rfl⟩ : syracuseStep 2260035 = 3390053) B3390053
theorem B3217909 : Blo 2259435 3217909 := bbase (se 5 (by rfl) ⟨150839, by rfl⟩ : syracuseStep 3217909 = 301679) (by norm_num)
theorem B4290545 : Blo 2259435 4290545 := bstep (se 2 (by rfl) ⟨1608954, by rfl⟩ : syracuseStep 4290545 = 3217909) B3217909
theorem B2860363 : Blo 2259435 2860363 := bstep (se 1 (by rfl) ⟨2145272, by rfl⟩ : syracuseStep 2860363 = 4290545) B4290545
theorem B3813817 : Blo 2259435 3813817 := bstep (se 2 (by rfl) ⟨1430181, by rfl⟩ : syracuseStep 3813817 = 2860363) B2860363
theorem B5085089 : Blo 2259435 5085089 := bstep (se 2 (by rfl) ⟨1906908, by rfl⟩ : syracuseStep 5085089 = 3813817) B3813817
theorem B3390059 : Blo 2259435 3390059 := bstep (se 1 (by rfl) ⟨2542544, by rfl⟩ : syracuseStep 3390059 = 5085089) B5085089
theorem B2260039 : Blo 2259435 2260039 := bstep (se 1 (by rfl) ⟨1695029, by rfl⟩ : syracuseStep 2260039 = 3390059) B3390059
theorem B2542549 : Blo 2259435 2542549 := bbase (se 7 (by rfl) ⟨29795, by rfl⟩ : syracuseStep 2542549 = 59591) (by norm_num)
theorem B3390065 : Blo 2259435 3390065 := bstep (se 2 (by rfl) ⟨1271274, by rfl⟩ : syracuseStep 3390065 = 2542549) B2542549
theorem B2260043 : Blo 2259435 2260043 := bstep (se 1 (by rfl) ⟨1695032, by rfl⟩ : syracuseStep 2260043 = 3390065) B3390065
theorem B2860373 : Blo 2259435 2860373 := bbase (se 12 (by rfl) ⟨1047, by rfl⟩ : syracuseStep 2860373 = 2095) (by norm_num)
theorem B7627661 : Blo 2259435 7627661 := bstep (se 3 (by rfl) ⟨1430186, by rfl⟩ : syracuseStep 7627661 = 2860373) B2860373
theorem B5085107 : Blo 2259435 5085107 := bstep (se 1 (by rfl) ⟨3813830, by rfl⟩ : syracuseStep 5085107 = 7627661) B7627661
theorem B3390071 : Blo 2259435 3390071 := bstep (se 1 (by rfl) ⟨2542553, by rfl⟩ : syracuseStep 3390071 = 5085107) B5085107
theorem B2260047 : Blo 2259435 2260047 := bstep (se 1 (by rfl) ⟨1695035, by rfl⟩ : syracuseStep 2260047 = 3390071) B3390071
theorem B3390077 : Blo 2259435 3390077 := bbase (se 3 (by rfl) ⟨635639, by rfl⟩ : syracuseStep 3390077 = 1271279) (by norm_num)
theorem B2260051 : Blo 2259435 2260051 := bstep (se 1 (by rfl) ⟨1695038, by rfl⟩ : syracuseStep 2260051 = 3390077) B3390077
theorem B5085125 : Blo 2259435 5085125 := bbase (se 4 (by rfl) ⟨476730, by rfl⟩ : syracuseStep 5085125 = 953461) (by norm_num)
theorem B3390083 : Blo 2259435 3390083 := bstep (se 1 (by rfl) ⟨2542562, by rfl⟩ : syracuseStep 3390083 = 5085125) B5085125
theorem B2260055 : Blo 2259435 2260055 := bstep (se 1 (by rfl) ⟨1695041, by rfl⟩ : syracuseStep 2260055 = 3390083) B3390083
theorem B9653813 : Blo 2259435 9653813 := bbase (se 5 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 9653813 = 905045) (by norm_num)
theorem B6435875 : Blo 2259435 6435875 := bstep (se 1 (by rfl) ⟨4826906, by rfl⟩ : syracuseStep 6435875 = 9653813) B9653813
theorem B4290583 : Blo 2259435 4290583 := bstep (se 1 (by rfl) ⟨3217937, by rfl⟩ : syracuseStep 4290583 = 6435875) B6435875
theorem B5720777 : Blo 2259435 5720777 := bstep (se 2 (by rfl) ⟨2145291, by rfl⟩ : syracuseStep 5720777 = 4290583) B4290583
theorem B3813851 : Blo 2259435 3813851 := bstep (se 1 (by rfl) ⟨2860388, by rfl⟩ : syracuseStep 3813851 = 5720777) B5720777
theorem B2542567 : Blo 2259435 2542567 := bstep (se 1 (by rfl) ⟨1906925, by rfl⟩ : syracuseStep 2542567 = 3813851) B3813851
theorem B3390089 : Blo 2259435 3390089 := bstep (se 2 (by rfl) ⟨1271283, by rfl⟩ : syracuseStep 3390089 = 2542567) B2542567
theorem B2260059 : Blo 2259435 2260059 := bstep (se 1 (by rfl) ⟨1695044, by rfl⟩ : syracuseStep 2260059 = 3390089) B3390089
theorem B11441573 : Blo 2259435 11441573 := bbase (se 4 (by rfl) ⟨1072647, by rfl⟩ : syracuseStep 11441573 = 2145295) (by norm_num)
theorem B7627715 : Blo 2259435 7627715 := bstep (se 1 (by rfl) ⟨5720786, by rfl⟩ : syracuseStep 7627715 = 11441573) B11441573
theorem B5085143 : Blo 2259435 5085143 := bstep (se 1 (by rfl) ⟨3813857, by rfl⟩ : syracuseStep 5085143 = 7627715) B7627715
theorem B3390095 : Blo 2259435 3390095 := bstep (se 1 (by rfl) ⟨2542571, by rfl⟩ : syracuseStep 3390095 = 5085143) B5085143
theorem B2260063 : Blo 2259435 2260063 := bstep (se 1 (by rfl) ⟨1695047, by rfl⟩ : syracuseStep 2260063 = 3390095) B3390095
theorem B3390101 : Blo 2259435 3390101 := bbase (se 6 (by rfl) ⟨79455, by rfl⟩ : syracuseStep 3390101 = 158911) (by norm_num)
theorem B2260067 : Blo 2259435 2260067 := bstep (se 1 (by rfl) ⟨1695050, by rfl⟩ : syracuseStep 2260067 = 3390101) B3390101
theorem B20618165 : Blo 2259435 20618165 := bbase (se 5 (by rfl) ⟨966476, by rfl⟩ : syracuseStep 20618165 = 1932953) (by norm_num)
theorem B54981773 : Blo 2259435 54981773 := bstep (se 3 (by rfl) ⟨10309082, by rfl⟩ : syracuseStep 54981773 = 20618165) B20618165
theorem B36654515 : Blo 2259435 36654515 := bstep (se 1 (by rfl) ⟨27490886, by rfl⟩ : syracuseStep 36654515 = 54981773) B54981773
theorem B24436343 : Blo 2259435 24436343 := bstep (se 1 (by rfl) ⟨18327257, by rfl⟩ : syracuseStep 24436343 = 36654515) B36654515
theorem B16290895 : Blo 2259435 16290895 := bstep (se 1 (by rfl) ⟨12218171, by rfl⟩ : syracuseStep 16290895 = 24436343) B24436343
theorem B21721193 : Blo 2259435 21721193 := bstep (se 2 (by rfl) ⟨8145447, by rfl⟩ : syracuseStep 21721193 = 16290895) B16290895
theorem B14480795 : Blo 2259435 14480795 := bstep (se 1 (by rfl) ⟨10860596, by rfl⟩ : syracuseStep 14480795 = 21721193) B21721193
theorem B9653863 : Blo 2259435 9653863 := bstep (se 1 (by rfl) ⟨7240397, by rfl⟩ : syracuseStep 9653863 = 14480795) B14480795
theorem B12871817 : Blo 2259435 12871817 := bstep (se 2 (by rfl) ⟨4826931, by rfl⟩ : syracuseStep 12871817 = 9653863) B9653863
theorem B8581211 : Blo 2259435 8581211 := bstep (se 1 (by rfl) ⟨6435908, by rfl⟩ : syracuseStep 8581211 = 12871817) B12871817
theorem B5720807 : Blo 2259435 5720807 := bstep (se 1 (by rfl) ⟨4290605, by rfl⟩ : syracuseStep 5720807 = 8581211) B8581211
theorem B3813871 : Blo 2259435 3813871 := bstep (se 1 (by rfl) ⟨2860403, by rfl⟩ : syracuseStep 3813871 = 5720807) B5720807
theorem B5085161 : Blo 2259435 5085161 := bstep (se 2 (by rfl) ⟨1906935, by rfl⟩ : syracuseStep 5085161 = 3813871) B3813871
theorem B3390107 : Blo 2259435 3390107 := bstep (se 1 (by rfl) ⟨2542580, by rfl⟩ : syracuseStep 3390107 = 5085161) B5085161
theorem B2260071 : Blo 2259435 2260071 := bstep (se 1 (by rfl) ⟨1695053, by rfl⟩ : syracuseStep 2260071 = 3390107) B3390107
theorem B2542585 : Blo 2259435 2542585 := bbase (se 2 (by rfl) ⟨953469, by rfl⟩ : syracuseStep 2542585 = 1906939) (by norm_num)
theorem B3390113 : Blo 2259435 3390113 := bstep (se 2 (by rfl) ⟨1271292, by rfl⟩ : syracuseStep 3390113 = 2542585) B2542585
theorem B2260075 : Blo 2259435 2260075 := bstep (se 1 (by rfl) ⟨1695056, by rfl⟩ : syracuseStep 2260075 = 3390113) B3390113
theorem B9059221 : Blo 2259435 9059221 := bbase (se 6 (by rfl) ⟨212325, by rfl⟩ : syracuseStep 9059221 = 424651) (by norm_num)
theorem B48315845 : Blo 2259435 48315845 := bstep (se 4 (by rfl) ⟨4529610, by rfl⟩ : syracuseStep 48315845 = 9059221) B9059221
theorem B128842253 : Blo 2259435 128842253 := bstep (se 3 (by rfl) ⟨24157922, by rfl⟩ : syracuseStep 128842253 = 48315845) B48315845
theorem B85894835 : Blo 2259435 85894835 := bstep (se 1 (by rfl) ⟨64421126, by rfl⟩ : syracuseStep 85894835 = 128842253) B128842253
theorem B229052893 : Blo 2259435 229052893 := bstep (se 3 (by rfl) ⟨42947417, by rfl⟩ : syracuseStep 229052893 = 85894835) B85894835
theorem B305403857 : Blo 2259435 305403857 := bstep (se 2 (by rfl) ⟨114526446, by rfl⟩ : syracuseStep 305403857 = 229052893) B229052893
theorem B203602571 : Blo 2259435 203602571 := bstep (se 1 (by rfl) ⟨152701928, by rfl⟩ : syracuseStep 203602571 = 305403857) B305403857
theorem B135735047 : Blo 2259435 135735047 := bstep (se 1 (by rfl) ⟨101801285, by rfl⟩ : syracuseStep 135735047 = 203602571) B203602571
theorem B90490031 : Blo 2259435 90490031 := bstep (se 1 (by rfl) ⟨67867523, by rfl⟩ : syracuseStep 90490031 = 135735047) B135735047
theorem B60326687 : Blo 2259435 60326687 := bstep (se 1 (by rfl) ⟨45245015, by rfl⟩ : syracuseStep 60326687 = 90490031) B90490031
theorem B40217791 : Blo 2259435 40217791 := bstep (se 1 (by rfl) ⟨30163343, by rfl⟩ : syracuseStep 40217791 = 60326687) B60326687
theorem B53623721 : Blo 2259435 53623721 := bstep (se 2 (by rfl) ⟨20108895, by rfl⟩ : syracuseStep 53623721 = 40217791) B40217791
theorem B35749147 : Blo 2259435 35749147 := bstep (se 1 (by rfl) ⟨26811860, by rfl⟩ : syracuseStep 35749147 = 53623721) B53623721
theorem B47665529 : Blo 2259435 47665529 := bstep (se 2 (by rfl) ⟨17874573, by rfl⟩ : syracuseStep 47665529 = 35749147) B35749147
theorem B31777019 : Blo 2259435 31777019 := bstep (se 1 (by rfl) ⟨23832764, by rfl⟩ : syracuseStep 31777019 = 47665529) B47665529
theorem B21184679 : Blo 2259435 21184679 := bstep (se 1 (by rfl) ⟨15888509, by rfl⟩ : syracuseStep 21184679 = 31777019) B31777019
theorem B14123119 : Blo 2259435 14123119 := bstep (se 1 (by rfl) ⟨10592339, by rfl⟩ : syracuseStep 14123119 = 21184679) B21184679
theorem B18830825 : Blo 2259435 18830825 := bstep (se 2 (by rfl) ⟨7061559, by rfl⟩ : syracuseStep 18830825 = 14123119) B14123119
theorem B803448533 : Blo 2259435 803448533 := bstep (se 7 (by rfl) ⟨9415412, by rfl⟩ : syracuseStep 803448533 = 18830825) B18830825
theorem B535632355 : Blo 2259435 535632355 := bstep (se 1 (by rfl) ⟨401724266, by rfl⟩ : syracuseStep 535632355 = 803448533) B803448533
theorem B2856705893 : Blo 2259435 2856705893 := bstep (se 4 (by rfl) ⟨267816177, by rfl⟩ : syracuseStep 2856705893 = 535632355) B535632355
theorem B1904470595 : Blo 2259435 1904470595 := bstep (se 1 (by rfl) ⟨1428352946, by rfl⟩ : syracuseStep 1904470595 = 2856705893) B2856705893
theorem B1269647063 : Blo 2259435 1269647063 := bstep (se 1 (by rfl) ⟨952235297, by rfl⟩ : syracuseStep 1269647063 = 1904470595) B1904470595
theorem B846431375 : Blo 2259435 846431375 := bstep (se 1 (by rfl) ⟨634823531, by rfl⟩ : syracuseStep 846431375 = 1269647063) B1269647063
theorem B2257150333 : Blo 2259435 2257150333 := bstep (se 3 (by rfl) ⟨423215687, by rfl⟩ : syracuseStep 2257150333 = 846431375) B846431375
theorem B3009533777 : Blo 2259435 3009533777 := bstep (se 2 (by rfl) ⟨1128575166, by rfl⟩ : syracuseStep 3009533777 = 2257150333) B2257150333
theorem B2006355851 : Blo 2259435 2006355851 := bstep (se 1 (by rfl) ⟨1504766888, by rfl⟩ : syracuseStep 2006355851 = 3009533777) B3009533777
theorem B1337570567 : Blo 2259435 1337570567 := bstep (se 1 (by rfl) ⟨1003177925, by rfl⟩ : syracuseStep 1337570567 = 2006355851) B2006355851
theorem B891713711 : Blo 2259435 891713711 := bstep (se 1 (by rfl) ⟨668785283, by rfl⟩ : syracuseStep 891713711 = 1337570567) B1337570567
theorem B594475807 : Blo 2259435 594475807 := bstep (se 1 (by rfl) ⟨445856855, by rfl⟩ : syracuseStep 594475807 = 891713711) B891713711
theorem B792634409 : Blo 2259435 792634409 := bstep (se 2 (by rfl) ⟨297237903, by rfl⟩ : syracuseStep 792634409 = 594475807) B594475807
theorem B528422939 : Blo 2259435 528422939 := bstep (se 1 (by rfl) ⟨396317204, by rfl⟩ : syracuseStep 528422939 = 792634409) B792634409
theorem B352281959 : Blo 2259435 352281959 := bstep (se 1 (by rfl) ⟨264211469, by rfl⟩ : syracuseStep 352281959 = 528422939) B528422939
theorem B234854639 : Blo 2259435 234854639 := bstep (se 1 (by rfl) ⟨176140979, by rfl⟩ : syracuseStep 234854639 = 352281959) B352281959
theorem B156569759 : Blo 2259435 156569759 := bstep (se 1 (by rfl) ⟨117427319, by rfl⟩ : syracuseStep 156569759 = 234854639) B234854639
theorem B104379839 : Blo 2259435 104379839 := bstep (se 1 (by rfl) ⟨78284879, by rfl⟩ : syracuseStep 104379839 = 156569759) B156569759
theorem B69586559 : Blo 2259435 69586559 := bstep (se 1 (by rfl) ⟨52189919, by rfl⟩ : syracuseStep 69586559 = 104379839) B104379839
theorem B46391039 : Blo 2259435 46391039 := bstep (se 1 (by rfl) ⟨34793279, by rfl⟩ : syracuseStep 46391039 = 69586559) B69586559
theorem B30927359 : Blo 2259435 30927359 := bstep (se 1 (by rfl) ⟨23195519, by rfl⟩ : syracuseStep 30927359 = 46391039) B46391039
theorem B20618239 : Blo 2259435 20618239 := bstep (se 1 (by rfl) ⟨15463679, by rfl⟩ : syracuseStep 20618239 = 30927359) B30927359
theorem B27490985 : Blo 2259435 27490985 := bstep (se 2 (by rfl) ⟨10309119, by rfl⟩ : syracuseStep 27490985 = 20618239) B20618239
theorem B18327323 : Blo 2259435 18327323 := bstep (se 1 (by rfl) ⟨13745492, by rfl⟩ : syracuseStep 18327323 = 27490985) B27490985
theorem B12218215 : Blo 2259435 12218215 := bstep (se 1 (by rfl) ⟨9163661, by rfl⟩ : syracuseStep 12218215 = 18327323) B18327323
theorem B16290953 : Blo 2259435 16290953 := bstep (se 2 (by rfl) ⟨6109107, by rfl⟩ : syracuseStep 16290953 = 12218215) B12218215
theorem B10860635 : Blo 2259435 10860635 := bstep (se 1 (by rfl) ⟨8145476, by rfl⟩ : syracuseStep 10860635 = 16290953) B16290953
theorem B7240423 : Blo 2259435 7240423 := bstep (se 1 (by rfl) ⟨5430317, by rfl⟩ : syracuseStep 7240423 = 10860635) B10860635
theorem B9653897 : Blo 2259435 9653897 := bstep (se 2 (by rfl) ⟨3620211, by rfl⟩ : syracuseStep 9653897 = 7240423) B7240423
theorem B6435931 : Blo 2259435 6435931 := bstep (se 1 (by rfl) ⟨4826948, by rfl⟩ : syracuseStep 6435931 = 9653897) B9653897
theorem B8581241 : Blo 2259435 8581241 := bstep (se 2 (by rfl) ⟨3217965, by rfl⟩ : syracuseStep 8581241 = 6435931) B6435931
theorem B5720827 : Blo 2259435 5720827 := bstep (se 1 (by rfl) ⟨4290620, by rfl⟩ : syracuseStep 5720827 = 8581241) B8581241
theorem B7627769 : Blo 2259435 7627769 := bstep (se 2 (by rfl) ⟨2860413, by rfl⟩ : syracuseStep 7627769 = 5720827) B5720827
theorem B5085179 : Blo 2259435 5085179 := bstep (se 1 (by rfl) ⟨3813884, by rfl⟩ : syracuseStep 5085179 = 7627769) B7627769
theorem B3390119 : Blo 2259435 3390119 := bstep (se 1 (by rfl) ⟨2542589, by rfl⟩ : syracuseStep 3390119 = 5085179) B5085179
theorem B2260079 : Blo 2259435 2260079 := bstep (se 1 (by rfl) ⟨1695059, by rfl⟩ : syracuseStep 2260079 = 3390119) B3390119
theorem B3390125 : Blo 2259435 3390125 := bbase (se 3 (by rfl) ⟨635648, by rfl⟩ : syracuseStep 3390125 = 1271297) (by norm_num)
theorem B2260083 : Blo 2259435 2260083 := bstep (se 1 (by rfl) ⟨1695062, by rfl⟩ : syracuseStep 2260083 = 3390125) B3390125
theorem B5085197 : Blo 2259435 5085197 := bbase (se 3 (by rfl) ⟨953474, by rfl⟩ : syracuseStep 5085197 = 1906949) (by norm_num)
theorem B3390131 : Blo 2259435 3390131 := bstep (se 1 (by rfl) ⟨2542598, by rfl⟩ : syracuseStep 3390131 = 5085197) B5085197
theorem B2260087 : Blo 2259435 2260087 := bstep (se 1 (by rfl) ⟨1695065, by rfl⟩ : syracuseStep 2260087 = 3390131) B3390131
theorem B2860429 : Blo 2259435 2860429 := bbase (se 3 (by rfl) ⟨536330, by rfl⟩ : syracuseStep 2860429 = 1072661) (by norm_num)
theorem B3813905 : Blo 2259435 3813905 := bstep (se 2 (by rfl) ⟨1430214, by rfl⟩ : syracuseStep 3813905 = 2860429) B2860429
theorem B2542603 : Blo 2259435 2542603 := bstep (se 1 (by rfl) ⟨1906952, by rfl⟩ : syracuseStep 2542603 = 3813905) B3813905
theorem B3390137 : Blo 2259435 3390137 := bstep (se 2 (by rfl) ⟨1271301, by rfl⟩ : syracuseStep 3390137 = 2542603) B2542603
theorem B2260091 : Blo 2259435 2260091 := bstep (se 1 (by rfl) ⟨1695068, by rfl⟩ : syracuseStep 2260091 = 3390137) B3390137
theorem B5224925 : Blo 2259435 5224925 := bbase (se 3 (by rfl) ⟨979673, by rfl⟩ : syracuseStep 5224925 = 1959347) (by norm_num)
theorem B13933133 : Blo 2259435 13933133 := bstep (se 3 (by rfl) ⟨2612462, by rfl⟩ : syracuseStep 13933133 = 5224925) B5224925
theorem B9288755 : Blo 2259435 9288755 := bstep (se 1 (by rfl) ⟨6966566, by rfl⟩ : syracuseStep 9288755 = 13933133) B13933133
theorem B6192503 : Blo 2259435 6192503 := bstep (se 1 (by rfl) ⟨4644377, by rfl⟩ : syracuseStep 6192503 = 9288755) B9288755
theorem B4128335 : Blo 2259435 4128335 := bstep (se 1 (by rfl) ⟨3096251, by rfl⟩ : syracuseStep 4128335 = 6192503) B6192503
theorem B2752223 : Blo 2259435 2752223 := bstep (se 1 (by rfl) ⟨2064167, by rfl⟩ : syracuseStep 2752223 = 4128335) B4128335
theorem B7339261 : Blo 2259435 7339261 := bstep (se 3 (by rfl) ⟨1376111, by rfl⟩ : syracuseStep 7339261 = 2752223) B2752223
theorem B9785681 : Blo 2259435 9785681 := bstep (se 2 (by rfl) ⟨3669630, by rfl⟩ : syracuseStep 9785681 = 7339261) B7339261
theorem B6523787 : Blo 2259435 6523787 := bstep (se 1 (by rfl) ⟨4892840, by rfl⟩ : syracuseStep 6523787 = 9785681) B9785681
theorem B17396765 : Blo 2259435 17396765 := bstep (se 3 (by rfl) ⟨3261893, by rfl⟩ : syracuseStep 17396765 = 6523787) B6523787
theorem B11597843 : Blo 2259435 11597843 := bstep (se 1 (by rfl) ⟨8698382, by rfl⟩ : syracuseStep 11597843 = 17396765) B17396765
theorem B7731895 : Blo 2259435 7731895 := bstep (se 1 (by rfl) ⟨5798921, by rfl⟩ : syracuseStep 7731895 = 11597843) B11597843
theorem B10309193 : Blo 2259435 10309193 := bstep (se 2 (by rfl) ⟨3865947, by rfl⟩ : syracuseStep 10309193 = 7731895) B7731895
theorem B6872795 : Blo 2259435 6872795 := bstep (se 1 (by rfl) ⟨5154596, by rfl⟩ : syracuseStep 6872795 = 10309193) B10309193
theorem B4581863 : Blo 2259435 4581863 := bstep (se 1 (by rfl) ⟨3436397, by rfl⟩ : syracuseStep 4581863 = 6872795) B6872795
theorem B3054575 : Blo 2259435 3054575 := bstep (se 1 (by rfl) ⟨2290931, by rfl⟩ : syracuseStep 3054575 = 4581863) B4581863
theorem B8145533 : Blo 2259435 8145533 := bstep (se 3 (by rfl) ⟨1527287, by rfl⟩ : syracuseStep 8145533 = 3054575) B3054575
theorem B21721421 : Blo 2259435 21721421 := bstep (se 3 (by rfl) ⟨4072766, by rfl⟩ : syracuseStep 21721421 = 8145533) B8145533
theorem B14480947 : Blo 2259435 14480947 := bstep (se 1 (by rfl) ⟨10860710, by rfl⟩ : syracuseStep 14480947 = 21721421) B21721421
theorem B19307929 : Blo 2259435 19307929 := bstep (se 2 (by rfl) ⟨7240473, by rfl⟩ : syracuseStep 19307929 = 14480947) B14480947
theorem B25743905 : Blo 2259435 25743905 := bstep (se 2 (by rfl) ⟨9653964, by rfl⟩ : syracuseStep 25743905 = 19307929) B19307929
theorem B17162603 : Blo 2259435 17162603 := bstep (se 1 (by rfl) ⟨12871952, by rfl⟩ : syracuseStep 17162603 = 25743905) B25743905
theorem B11441735 : Blo 2259435 11441735 := bstep (se 1 (by rfl) ⟨8581301, by rfl⟩ : syracuseStep 11441735 = 17162603) B17162603
theorem B7627823 : Blo 2259435 7627823 := bstep (se 1 (by rfl) ⟨5720867, by rfl⟩ : syracuseStep 7627823 = 11441735) B11441735
theorem B5085215 : Blo 2259435 5085215 := bstep (se 1 (by rfl) ⟨3813911, by rfl⟩ : syracuseStep 5085215 = 7627823) B7627823
theorem B3390143 : Blo 2259435 3390143 := bstep (se 1 (by rfl) ⟨2542607, by rfl⟩ : syracuseStep 3390143 = 5085215) B5085215
theorem B2260095 : Blo 2259435 2260095 := bstep (se 1 (by rfl) ⟨1695071, by rfl⟩ : syracuseStep 2260095 = 3390143) B3390143
theorem B3390149 : Blo 2259435 3390149 := bbase (se 4 (by rfl) ⟨317826, by rfl⟩ : syracuseStep 3390149 = 635653) (by norm_num)
theorem B2260099 : Blo 2259435 2260099 := bstep (se 1 (by rfl) ⟨1695074, by rfl⟩ : syracuseStep 2260099 = 3390149) B3390149
theorem B3813925 : Blo 2259435 3813925 := bbase (se 4 (by rfl) ⟨357555, by rfl⟩ : syracuseStep 3813925 = 715111) (by norm_num)
theorem B5085233 : Blo 2259435 5085233 := bstep (se 2 (by rfl) ⟨1906962, by rfl⟩ : syracuseStep 5085233 = 3813925) B3813925
theorem B3390155 : Blo 2259435 3390155 := bstep (se 1 (by rfl) ⟨2542616, by rfl⟩ : syracuseStep 3390155 = 5085233) B5085233
theorem B2260103 : Blo 2259435 2260103 := bstep (se 1 (by rfl) ⟨1695077, by rfl⟩ : syracuseStep 2260103 = 3390155) B3390155
theorem B2542621 : Blo 2259435 2542621 := bbase (se 3 (by rfl) ⟨476741, by rfl⟩ : syracuseStep 2542621 = 953483) (by norm_num)
theorem B3390161 : Blo 2259435 3390161 := bstep (se 2 (by rfl) ⟨1271310, by rfl⟩ : syracuseStep 3390161 = 2542621) B2542621
theorem B2260107 : Blo 2259435 2260107 := bstep (se 1 (by rfl) ⟨1695080, by rfl⟩ : syracuseStep 2260107 = 3390161) B3390161
theorem B7627877 : Blo 2259435 7627877 := bbase (se 4 (by rfl) ⟨715113, by rfl⟩ : syracuseStep 7627877 = 1430227) (by norm_num)
theorem B5085251 : Blo 2259435 5085251 := bstep (se 1 (by rfl) ⟨3813938, by rfl⟩ : syracuseStep 5085251 = 7627877) B7627877
theorem B3390167 : Blo 2259435 3390167 := bstep (se 1 (by rfl) ⟨2542625, by rfl⟩ : syracuseStep 3390167 = 5085251) B5085251
theorem B2260111 : Blo 2259435 2260111 := bstep (se 1 (by rfl) ⟨1695083, by rfl⟩ : syracuseStep 2260111 = 3390167) B3390167
theorem B3390173 : Blo 2259435 3390173 := bbase (se 3 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 3390173 = 1271315) (by norm_num)
theorem B2260115 : Blo 2259435 2260115 := bstep (se 1 (by rfl) ⟨1695086, by rfl⟩ : syracuseStep 2260115 = 3390173) B3390173
theorem B5085269 : Blo 2259435 5085269 := bbase (se 8 (by rfl) ⟨29796, by rfl⟩ : syracuseStep 5085269 = 59593) (by norm_num)
theorem B3390179 : Blo 2259435 3390179 := bstep (se 1 (by rfl) ⟨2542634, by rfl⟩ : syracuseStep 3390179 = 5085269) B5085269
theorem B2260119 : Blo 2259435 2260119 := bstep (se 1 (by rfl) ⟨1695089, by rfl⟩ : syracuseStep 2260119 = 3390179) B3390179
theorem B7240565 : Blo 2259435 7240565 := bbase (se 5 (by rfl) ⟨339401, by rfl⟩ : syracuseStep 7240565 = 678803) (by norm_num)
theorem B4827043 : Blo 2259435 4827043 := bstep (se 1 (by rfl) ⟨3620282, by rfl⟩ : syracuseStep 4827043 = 7240565) B7240565
theorem B6436057 : Blo 2259435 6436057 := bstep (se 2 (by rfl) ⟨2413521, by rfl⟩ : syracuseStep 6436057 = 4827043) B4827043
theorem B8581409 : Blo 2259435 8581409 := bstep (se 2 (by rfl) ⟨3218028, by rfl⟩ : syracuseStep 8581409 = 6436057) B6436057
theorem B5720939 : Blo 2259435 5720939 := bstep (se 1 (by rfl) ⟨4290704, by rfl⟩ : syracuseStep 5720939 = 8581409) B8581409
theorem B3813959 : Blo 2259435 3813959 := bstep (se 1 (by rfl) ⟨2860469, by rfl⟩ : syracuseStep 3813959 = 5720939) B5720939
theorem B2542639 : Blo 2259435 2542639 := bstep (se 1 (by rfl) ⟨1906979, by rfl⟩ : syracuseStep 2542639 = 3813959) B3813959
theorem B3390185 : Blo 2259435 3390185 := bstep (se 2 (by rfl) ⟨1271319, by rfl⟩ : syracuseStep 3390185 = 2542639) B2542639
theorem B2260123 : Blo 2259435 2260123 := bstep (se 1 (by rfl) ⟨1695092, by rfl⟩ : syracuseStep 2260123 = 3390185) B3390185
theorem B11598005 : Blo 2259435 11598005 := bbase (se 5 (by rfl) ⟨543656, by rfl⟩ : syracuseStep 11598005 = 1087313) (by norm_num)
theorem B30928013 : Blo 2259435 30928013 := bstep (se 3 (by rfl) ⟨5799002, by rfl⟩ : syracuseStep 30928013 = 11598005) B11598005
theorem B20618675 : Blo 2259435 20618675 := bstep (se 1 (by rfl) ⟨15464006, by rfl⟩ : syracuseStep 20618675 = 30928013) B30928013
theorem B13745783 : Blo 2259435 13745783 := bstep (se 1 (by rfl) ⟨10309337, by rfl⟩ : syracuseStep 13745783 = 20618675) B20618675
theorem B9163855 : Blo 2259435 9163855 := bstep (se 1 (by rfl) ⟨6872891, by rfl⟩ : syracuseStep 9163855 = 13745783) B13745783
theorem B12218473 : Blo 2259435 12218473 := bstep (se 2 (by rfl) ⟨4581927, by rfl⟩ : syracuseStep 12218473 = 9163855) B9163855
theorem B16291297 : Blo 2259435 16291297 := bstep (se 2 (by rfl) ⟨6109236, by rfl⟩ : syracuseStep 16291297 = 12218473) B12218473
theorem B21721729 : Blo 2259435 21721729 := bstep (se 2 (by rfl) ⟨8145648, by rfl⟩ : syracuseStep 21721729 = 16291297) B16291297
theorem B28962305 : Blo 2259435 28962305 := bstep (se 2 (by rfl) ⟨10860864, by rfl⟩ : syracuseStep 28962305 = 21721729) B21721729
theorem B19308203 : Blo 2259435 19308203 := bstep (se 1 (by rfl) ⟨14481152, by rfl⟩ : syracuseStep 19308203 = 28962305) B28962305
theorem B12872135 : Blo 2259435 12872135 := bstep (se 1 (by rfl) ⟨9654101, by rfl⟩ : syracuseStep 12872135 = 19308203) B19308203
theorem B8581423 : Blo 2259435 8581423 := bstep (se 1 (by rfl) ⟨6436067, by rfl⟩ : syracuseStep 8581423 = 12872135) B12872135
theorem B11441897 : Blo 2259435 11441897 := bstep (se 2 (by rfl) ⟨4290711, by rfl⟩ : syracuseStep 11441897 = 8581423) B8581423
theorem B7627931 : Blo 2259435 7627931 := bstep (se 1 (by rfl) ⟨5720948, by rfl⟩ : syracuseStep 7627931 = 11441897) B11441897
theorem B5085287 : Blo 2259435 5085287 := bstep (se 1 (by rfl) ⟨3813965, by rfl⟩ : syracuseStep 5085287 = 7627931) B7627931
theorem B3390191 : Blo 2259435 3390191 := bstep (se 1 (by rfl) ⟨2542643, by rfl⟩ : syracuseStep 3390191 = 5085287) B5085287
theorem B2260127 : Blo 2259435 2260127 := bstep (se 1 (by rfl) ⟨1695095, by rfl⟩ : syracuseStep 2260127 = 3390191) B3390191
theorem B3390197 : Blo 2259435 3390197 := bbase (se 5 (by rfl) ⟨158915, by rfl⟩ : syracuseStep 3390197 = 317831) (by norm_num)
theorem B2260131 : Blo 2259435 2260131 := bstep (se 1 (by rfl) ⟨1695098, by rfl⟩ : syracuseStep 2260131 = 3390197) B3390197
theorem B27491669 : Blo 2259435 27491669 := bbase (se 11 (by rfl) ⟨20135, by rfl⟩ : syracuseStep 27491669 = 40271) (by norm_num)
theorem B18327779 : Blo 2259435 18327779 := bstep (se 1 (by rfl) ⟨13745834, by rfl⟩ : syracuseStep 18327779 = 27491669) B27491669
theorem B12218519 : Blo 2259435 12218519 := bstep (se 1 (by rfl) ⟨9163889, by rfl⟩ : syracuseStep 12218519 = 18327779) B18327779
theorem B8145679 : Blo 2259435 8145679 := bstep (se 1 (by rfl) ⟨6109259, by rfl⟩ : syracuseStep 8145679 = 12218519) B12218519
theorem B10860905 : Blo 2259435 10860905 := bstep (se 2 (by rfl) ⟨4072839, by rfl⟩ : syracuseStep 10860905 = 8145679) B8145679
theorem B7240603 : Blo 2259435 7240603 := bstep (se 1 (by rfl) ⟨5430452, by rfl⟩ : syracuseStep 7240603 = 10860905) B10860905
theorem B9654137 : Blo 2259435 9654137 := bstep (se 2 (by rfl) ⟨3620301, by rfl⟩ : syracuseStep 9654137 = 7240603) B7240603
theorem B6436091 : Blo 2259435 6436091 := bstep (se 1 (by rfl) ⟨4827068, by rfl⟩ : syracuseStep 6436091 = 9654137) B9654137
theorem B4290727 : Blo 2259435 4290727 := bstep (se 1 (by rfl) ⟨3218045, by rfl⟩ : syracuseStep 4290727 = 6436091) B6436091
theorem B5720969 : Blo 2259435 5720969 := bstep (se 2 (by rfl) ⟨2145363, by rfl⟩ : syracuseStep 5720969 = 4290727) B4290727
theorem B3813979 : Blo 2259435 3813979 := bstep (se 1 (by rfl) ⟨2860484, by rfl⟩ : syracuseStep 3813979 = 5720969) B5720969
theorem B5085305 : Blo 2259435 5085305 := bstep (se 2 (by rfl) ⟨1906989, by rfl⟩ : syracuseStep 5085305 = 3813979) B3813979
theorem B3390203 : Blo 2259435 3390203 := bstep (se 1 (by rfl) ⟨2542652, by rfl⟩ : syracuseStep 3390203 = 5085305) B5085305
theorem B2260135 : Blo 2259435 2260135 := bstep (se 1 (by rfl) ⟨1695101, by rfl⟩ : syracuseStep 2260135 = 3390203) B3390203
theorem B2542657 : Blo 2259435 2542657 := bbase (se 2 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 2542657 = 1906993) (by norm_num)
theorem B3390209 : Blo 2259435 3390209 := bstep (se 2 (by rfl) ⟨1271328, by rfl⟩ : syracuseStep 3390209 = 2542657) B2542657
theorem B2260139 : Blo 2259435 2260139 := bstep (se 1 (by rfl) ⟨1695104, by rfl⟩ : syracuseStep 2260139 = 3390209) B3390209
theorem B5720989 : Blo 2259435 5720989 := bbase (se 3 (by rfl) ⟨1072685, by rfl⟩ : syracuseStep 5720989 = 2145371) (by norm_num)
theorem B7627985 : Blo 2259435 7627985 := bstep (se 2 (by rfl) ⟨2860494, by rfl⟩ : syracuseStep 7627985 = 5720989) B5720989
theorem B5085323 : Blo 2259435 5085323 := bstep (se 1 (by rfl) ⟨3813992, by rfl⟩ : syracuseStep 5085323 = 7627985) B7627985
theorem B3390215 : Blo 2259435 3390215 := bstep (se 1 (by rfl) ⟨2542661, by rfl⟩ : syracuseStep 3390215 = 5085323) B5085323
theorem B2260143 : Blo 2259435 2260143 := bstep (se 1 (by rfl) ⟨1695107, by rfl⟩ : syracuseStep 2260143 = 3390215) B3390215
theorem B3390221 : Blo 2259435 3390221 := bbase (se 3 (by rfl) ⟨635666, by rfl⟩ : syracuseStep 3390221 = 1271333) (by norm_num)
theorem B2260147 : Blo 2259435 2260147 := bstep (se 1 (by rfl) ⟨1695110, by rfl⟩ : syracuseStep 2260147 = 3390221) B3390221
theorem B5085341 : Blo 2259435 5085341 := bbase (se 3 (by rfl) ⟨953501, by rfl⟩ : syracuseStep 5085341 = 1907003) (by norm_num)
theorem B3390227 : Blo 2259435 3390227 := bstep (se 1 (by rfl) ⟨2542670, by rfl⟩ : syracuseStep 3390227 = 5085341) B5085341
theorem B2260151 : Blo 2259435 2260151 := bstep (se 1 (by rfl) ⟨1695113, by rfl⟩ : syracuseStep 2260151 = 3390227) B3390227
theorem B3814013 : Blo 2259435 3814013 := bbase (se 3 (by rfl) ⟨715127, by rfl⟩ : syracuseStep 3814013 = 1430255) (by norm_num)
theorem B2542675 : Blo 2259435 2542675 := bstep (se 1 (by rfl) ⟨1907006, by rfl⟩ : syracuseStep 2542675 = 3814013) B3814013
theorem B3390233 : Blo 2259435 3390233 := bstep (se 2 (by rfl) ⟨1271337, by rfl⟩ : syracuseStep 3390233 = 2542675) B2542675
theorem B2260155 : Blo 2259435 2260155 := bstep (se 1 (by rfl) ⟨1695116, by rfl⟩ : syracuseStep 2260155 = 3390233) B3390233
theorem B6523973 : Blo 2259435 6523973 := bbase (se 4 (by rfl) ⟨611622, by rfl⟩ : syracuseStep 6523973 = 1223245) (by norm_num)
theorem B4349315 : Blo 2259435 4349315 := bstep (se 1 (by rfl) ⟨3261986, by rfl⟩ : syracuseStep 4349315 = 6523973) B6523973
theorem B2899543 : Blo 2259435 2899543 := bstep (se 1 (by rfl) ⟨2174657, by rfl⟩ : syracuseStep 2899543 = 4349315) B4349315
theorem B3866057 : Blo 2259435 3866057 := bstep (se 2 (by rfl) ⟨1449771, by rfl⟩ : syracuseStep 3866057 = 2899543) B2899543
theorem B2577371 : Blo 2259435 2577371 := bstep (se 1 (by rfl) ⟨1933028, by rfl⟩ : syracuseStep 2577371 = 3866057) B3866057
theorem B27491957 : Blo 2259435 27491957 := bstep (se 5 (by rfl) ⟨1288685, by rfl⟩ : syracuseStep 27491957 = 2577371) B2577371
theorem B18327971 : Blo 2259435 18327971 := bstep (se 1 (by rfl) ⟨13745978, by rfl⟩ : syracuseStep 18327971 = 27491957) B27491957
theorem B12218647 : Blo 2259435 12218647 := bstep (se 1 (by rfl) ⟨9163985, by rfl⟩ : syracuseStep 12218647 = 18327971) B18327971
theorem B16291529 : Blo 2259435 16291529 := bstep (se 2 (by rfl) ⟨6109323, by rfl⟩ : syracuseStep 16291529 = 12218647) B12218647
theorem B10861019 : Blo 2259435 10861019 := bstep (se 1 (by rfl) ⟨8145764, by rfl⟩ : syracuseStep 10861019 = 16291529) B16291529
theorem B7240679 : Blo 2259435 7240679 := bstep (se 1 (by rfl) ⟨5430509, by rfl⟩ : syracuseStep 7240679 = 10861019) B10861019
theorem B4827119 : Blo 2259435 4827119 := bstep (se 1 (by rfl) ⟨3620339, by rfl⟩ : syracuseStep 4827119 = 7240679) B7240679
theorem B12872317 : Blo 2259435 12872317 := bstep (se 3 (by rfl) ⟨2413559, by rfl⟩ : syracuseStep 12872317 = 4827119) B4827119
theorem B17163089 : Blo 2259435 17163089 := bstep (se 2 (by rfl) ⟨6436158, by rfl⟩ : syracuseStep 17163089 = 12872317) B12872317
theorem B11442059 : Blo 2259435 11442059 := bstep (se 1 (by rfl) ⟨8581544, by rfl⟩ : syracuseStep 11442059 = 17163089) B17163089
theorem B7628039 : Blo 2259435 7628039 := bstep (se 1 (by rfl) ⟨5721029, by rfl⟩ : syracuseStep 7628039 = 11442059) B11442059
theorem B5085359 : Blo 2259435 5085359 := bstep (se 1 (by rfl) ⟨3814019, by rfl⟩ : syracuseStep 5085359 = 7628039) B7628039
theorem B3390239 : Blo 2259435 3390239 := bstep (se 1 (by rfl) ⟨2542679, by rfl⟩ : syracuseStep 3390239 = 5085359) B5085359
theorem B2260159 : Blo 2259435 2260159 := bstep (se 1 (by rfl) ⟨1695119, by rfl⟩ : syracuseStep 2260159 = 3390239) B3390239
theorem B3390245 : Blo 2259435 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B2260163 : Blo 2259435 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B2860525 : Blo 2259435 2860525 := bbase (se 3 (by rfl) ⟨536348, by rfl⟩ : syracuseStep 2860525 = 1072697) (by norm_num)
theorem B3814033 : Blo 2259435 3814033 := bstep (se 2 (by rfl) ⟨1430262, by rfl⟩ : syracuseStep 3814033 = 2860525) B2860525
theorem B5085377 : Blo 2259435 5085377 := bstep (se 2 (by rfl) ⟨1907016, by rfl⟩ : syracuseStep 5085377 = 3814033) B3814033
theorem B3390251 : Blo 2259435 3390251 := bstep (se 1 (by rfl) ⟨2542688, by rfl⟩ : syracuseStep 3390251 = 5085377) B5085377
theorem B2260167 : Blo 2259435 2260167 := bstep (se 1 (by rfl) ⟨1695125, by rfl⟩ : syracuseStep 2260167 = 3390251) B3390251
theorem B2542693 : Blo 2259435 2542693 := bbase (se 4 (by rfl) ⟨238377, by rfl⟩ : syracuseStep 2542693 = 476755) (by norm_num)
theorem B3390257 : Blo 2259435 3390257 := bstep (se 2 (by rfl) ⟨1271346, by rfl⟩ : syracuseStep 3390257 = 2542693) B2542693
theorem B2260171 : Blo 2259435 2260171 := bstep (se 1 (by rfl) ⟨1695128, by rfl⟩ : syracuseStep 2260171 = 3390257) B3390257
theorem B2413577 : Blo 2259435 2413577 := bbase (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) (by norm_num)
theorem B6436205 : Blo 2259435 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B4290803 : Blo 2259435 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B2860535 : Blo 2259435 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B7628093 : Blo 2259435 7628093 := bstep (se 3 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 7628093 = 2860535) B2860535
theorem B5085395 : Blo 2259435 5085395 := bstep (se 1 (by rfl) ⟨3814046, by rfl⟩ : syracuseStep 5085395 = 7628093) B7628093
theorem B3390263 : Blo 2259435 3390263 := bstep (se 1 (by rfl) ⟨2542697, by rfl⟩ : syracuseStep 3390263 = 5085395) B5085395
theorem B2260175 : Blo 2259435 2260175 := bstep (se 1 (by rfl) ⟨1695131, by rfl⟩ : syracuseStep 2260175 = 3390263) B3390263
theorem B3390269 : Blo 2259435 3390269 := bbase (se 3 (by rfl) ⟨635675, by rfl⟩ : syracuseStep 3390269 = 1271351) (by norm_num)
theorem B2260179 : Blo 2259435 2260179 := bstep (se 1 (by rfl) ⟨1695134, by rfl⟩ : syracuseStep 2260179 = 3390269) B3390269
theorem B5085413 : Blo 2259435 5085413 := bbase (se 4 (by rfl) ⟨476757, by rfl⟩ : syracuseStep 5085413 = 953515) (by norm_num)
theorem B3390275 : Blo 2259435 3390275 := bstep (se 1 (by rfl) ⟨2542706, by rfl⟩ : syracuseStep 3390275 = 5085413) B5085413
theorem B2260183 : Blo 2259435 2260183 := bstep (se 1 (by rfl) ⟨1695137, by rfl⟩ : syracuseStep 2260183 = 3390275) B3390275
theorem B5721101 : Blo 2259435 5721101 := bbase (se 3 (by rfl) ⟨1072706, by rfl⟩ : syracuseStep 5721101 = 2145413) (by norm_num)
theorem B3814067 : Blo 2259435 3814067 := bstep (se 1 (by rfl) ⟨2860550, by rfl⟩ : syracuseStep 3814067 = 5721101) B5721101
theorem B2542711 : Blo 2259435 2542711 := bstep (se 1 (by rfl) ⟨1907033, by rfl⟩ : syracuseStep 2542711 = 3814067) B3814067
theorem B3390281 : Blo 2259435 3390281 := bstep (se 2 (by rfl) ⟨1271355, by rfl⟩ : syracuseStep 3390281 = 2542711) B2542711
theorem B2260187 : Blo 2259435 2260187 := bstep (se 1 (by rfl) ⟨1695140, by rfl⟩ : syracuseStep 2260187 = 3390281) B3390281
theorem B3218125 : Blo 2259435 3218125 := bbase (se 3 (by rfl) ⟨603398, by rfl⟩ : syracuseStep 3218125 = 1206797) (by norm_num)
theorem B4290833 : Blo 2259435 4290833 := bstep (se 2 (by rfl) ⟨1609062, by rfl⟩ : syracuseStep 4290833 = 3218125) B3218125
theorem B11442221 : Blo 2259435 11442221 := bstep (se 3 (by rfl) ⟨2145416, by rfl⟩ : syracuseStep 11442221 = 4290833) B4290833
theorem B7628147 : Blo 2259435 7628147 := bstep (se 1 (by rfl) ⟨5721110, by rfl⟩ : syracuseStep 7628147 = 11442221) B11442221
theorem B5085431 : Blo 2259435 5085431 := bstep (se 1 (by rfl) ⟨3814073, by rfl⟩ : syracuseStep 5085431 = 7628147) B7628147
theorem B3390287 : Blo 2259435 3390287 := bstep (se 1 (by rfl) ⟨2542715, by rfl⟩ : syracuseStep 3390287 = 5085431) B5085431
theorem B2260191 : Blo 2259435 2260191 := bstep (se 1 (by rfl) ⟨1695143, by rfl⟩ : syracuseStep 2260191 = 3390287) B3390287
theorem B3390293 : Blo 2259435 3390293 := bbase (se 9 (by rfl) ⟨9932, by rfl⟩ : syracuseStep 3390293 = 19865) (by norm_num)
theorem B2260195 : Blo 2259435 2260195 := bstep (se 1 (by rfl) ⟨1695146, by rfl⟩ : syracuseStep 2260195 = 3390293) B3390293
theorem B4827205 : Blo 2259435 4827205 := bbase (se 4 (by rfl) ⟨452550, by rfl⟩ : syracuseStep 4827205 = 905101) (by norm_num)
theorem B6436273 : Blo 2259435 6436273 := bstep (se 2 (by rfl) ⟨2413602, by rfl⟩ : syracuseStep 6436273 = 4827205) B4827205
theorem B8581697 : Blo 2259435 8581697 := bstep (se 2 (by rfl) ⟨3218136, by rfl⟩ : syracuseStep 8581697 = 6436273) B6436273
theorem B5721131 : Blo 2259435 5721131 := bstep (se 1 (by rfl) ⟨4290848, by rfl⟩ : syracuseStep 5721131 = 8581697) B8581697
theorem B3814087 : Blo 2259435 3814087 := bstep (se 1 (by rfl) ⟨2860565, by rfl⟩ : syracuseStep 3814087 = 5721131) B5721131
theorem B5085449 : Blo 2259435 5085449 := bstep (se 2 (by rfl) ⟨1907043, by rfl⟩ : syracuseStep 5085449 = 3814087) B3814087
theorem B3390299 : Blo 2259435 3390299 := bstep (se 1 (by rfl) ⟨2542724, by rfl⟩ : syracuseStep 3390299 = 5085449) B5085449
theorem B2260199 : Blo 2259435 2260199 := bstep (se 1 (by rfl) ⟨1695149, by rfl⟩ : syracuseStep 2260199 = 3390299) B3390299
theorem B2542729 : Blo 2259435 2542729 := bbase (se 2 (by rfl) ⟨953523, by rfl⟩ : syracuseStep 2542729 = 1907047) (by norm_num)
theorem B3390305 : Blo 2259435 3390305 := bstep (se 2 (by rfl) ⟨1271364, by rfl⟩ : syracuseStep 3390305 = 2542729) B2542729
theorem B2260203 : Blo 2259435 2260203 := bstep (se 1 (by rfl) ⟨1695152, by rfl⟩ : syracuseStep 2260203 = 3390305) B3390305
theorem B2291045 : Blo 2259435 2291045 := bbase (se 4 (by rfl) ⟨214785, by rfl⟩ : syracuseStep 2291045 = 429571) (by norm_num)
theorem B6109453 : Blo 2259435 6109453 := bstep (se 3 (by rfl) ⟨1145522, by rfl⟩ : syracuseStep 6109453 = 2291045) B2291045
theorem B8145937 : Blo 2259435 8145937 := bstep (se 2 (by rfl) ⟨3054726, by rfl⟩ : syracuseStep 8145937 = 6109453) B6109453
theorem B43444997 : Blo 2259435 43444997 := bstep (se 4 (by rfl) ⟨4072968, by rfl⟩ : syracuseStep 43444997 = 8145937) B8145937
theorem B28963331 : Blo 2259435 28963331 := bstep (se 1 (by rfl) ⟨21722498, by rfl⟩ : syracuseStep 28963331 = 43444997) B43444997
theorem B19308887 : Blo 2259435 19308887 := bstep (se 1 (by rfl) ⟨14481665, by rfl⟩ : syracuseStep 19308887 = 28963331) B28963331
theorem B12872591 : Blo 2259435 12872591 := bstep (se 1 (by rfl) ⟨9654443, by rfl⟩ : syracuseStep 12872591 = 19308887) B19308887
theorem B8581727 : Blo 2259435 8581727 := bstep (se 1 (by rfl) ⟨6436295, by rfl⟩ : syracuseStep 8581727 = 12872591) B12872591
theorem B5721151 : Blo 2259435 5721151 := bstep (se 1 (by rfl) ⟨4290863, by rfl⟩ : syracuseStep 5721151 = 8581727) B8581727
theorem B7628201 : Blo 2259435 7628201 := bstep (se 2 (by rfl) ⟨2860575, by rfl⟩ : syracuseStep 7628201 = 5721151) B5721151
theorem B5085467 : Blo 2259435 5085467 := bstep (se 1 (by rfl) ⟨3814100, by rfl⟩ : syracuseStep 5085467 = 7628201) B7628201
theorem B3390311 : Blo 2259435 3390311 := bstep (se 1 (by rfl) ⟨2542733, by rfl⟩ : syracuseStep 3390311 = 5085467) B5085467
theorem B2260207 : Blo 2259435 2260207 := bstep (se 1 (by rfl) ⟨1695155, by rfl⟩ : syracuseStep 2260207 = 3390311) B3390311
theorem B3390317 : Blo 2259435 3390317 := bbase (se 3 (by rfl) ⟨635684, by rfl⟩ : syracuseStep 3390317 = 1271369) (by norm_num)
theorem B2260211 : Blo 2259435 2260211 := bstep (se 1 (by rfl) ⟨1695158, by rfl⟩ : syracuseStep 2260211 = 3390317) B3390317
theorem B5085485 : Blo 2259435 5085485 := bbase (se 3 (by rfl) ⟨953528, by rfl⟩ : syracuseStep 5085485 = 1907057) (by norm_num)
theorem B3390323 : Blo 2259435 3390323 := bstep (se 1 (by rfl) ⟨2542742, by rfl⟩ : syracuseStep 3390323 = 5085485) B5085485
theorem B2260215 : Blo 2259435 2260215 := bstep (se 1 (by rfl) ⟨1695161, by rfl⟩ : syracuseStep 2260215 = 3390323) B3390323
theorem B2322317 : Blo 2259435 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B6192845 : Blo 2259435 6192845 := bstep (se 3 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 6192845 = 2322317) B2322317
theorem B4128563 : Blo 2259435 4128563 := bstep (se 1 (by rfl) ⟨3096422, by rfl⟩ : syracuseStep 4128563 = 6192845) B6192845
theorem B2752375 : Blo 2259435 2752375 := bstep (se 1 (by rfl) ⟨2064281, by rfl⟩ : syracuseStep 2752375 = 4128563) B4128563
theorem B3669833 : Blo 2259435 3669833 := bstep (se 2 (by rfl) ⟨1376187, by rfl⟩ : syracuseStep 3669833 = 2752375) B2752375
theorem B2446555 : Blo 2259435 2446555 := bstep (se 1 (by rfl) ⟨1834916, by rfl⟩ : syracuseStep 2446555 = 3669833) B3669833
theorem B3262073 : Blo 2259435 3262073 := bstep (se 2 (by rfl) ⟨1223277, by rfl⟩ : syracuseStep 3262073 = 2446555) B2446555
theorem B8698861 : Blo 2259435 8698861 := bstep (se 3 (by rfl) ⟨1631036, by rfl⟩ : syracuseStep 8698861 = 3262073) B3262073
theorem B11598481 : Blo 2259435 11598481 := bstep (se 2 (by rfl) ⟨4349430, by rfl⟩ : syracuseStep 11598481 = 8698861) B8698861
theorem B61858565 : Blo 2259435 61858565 := bstep (se 4 (by rfl) ⟨5799240, by rfl⟩ : syracuseStep 61858565 = 11598481) B11598481
theorem B41239043 : Blo 2259435 41239043 := bstep (se 1 (by rfl) ⟨30929282, by rfl⟩ : syracuseStep 41239043 = 61858565) B61858565
theorem B27492695 : Blo 2259435 27492695 := bstep (se 1 (by rfl) ⟨20619521, by rfl⟩ : syracuseStep 27492695 = 41239043) B41239043
theorem B18328463 : Blo 2259435 18328463 := bstep (se 1 (by rfl) ⟨13746347, by rfl⟩ : syracuseStep 18328463 = 27492695) B27492695
theorem B12218975 : Blo 2259435 12218975 := bstep (se 1 (by rfl) ⟨9164231, by rfl⟩ : syracuseStep 12218975 = 18328463) B18328463
theorem B8145983 : Blo 2259435 8145983 := bstep (se 1 (by rfl) ⟨6109487, by rfl⟩ : syracuseStep 8145983 = 12218975) B12218975
theorem B5430655 : Blo 2259435 5430655 := bstep (se 1 (by rfl) ⟨4072991, by rfl⟩ : syracuseStep 5430655 = 8145983) B8145983
theorem B7240873 : Blo 2259435 7240873 := bstep (se 2 (by rfl) ⟨2715327, by rfl⟩ : syracuseStep 7240873 = 5430655) B5430655
theorem B9654497 : Blo 2259435 9654497 := bstep (se 2 (by rfl) ⟨3620436, by rfl⟩ : syracuseStep 9654497 = 7240873) B7240873
theorem B6436331 : Blo 2259435 6436331 := bstep (se 1 (by rfl) ⟨4827248, by rfl⟩ : syracuseStep 6436331 = 9654497) B9654497
theorem B4290887 : Blo 2259435 4290887 := bstep (se 1 (by rfl) ⟨3218165, by rfl⟩ : syracuseStep 4290887 = 6436331) B6436331
theorem B2860591 : Blo 2259435 2860591 := bstep (se 1 (by rfl) ⟨2145443, by rfl⟩ : syracuseStep 2860591 = 4290887) B4290887
theorem B3814121 : Blo 2259435 3814121 := bstep (se 2 (by rfl) ⟨1430295, by rfl⟩ : syracuseStep 3814121 = 2860591) B2860591
theorem B2542747 : Blo 2259435 2542747 := bstep (se 1 (by rfl) ⟨1907060, by rfl⟩ : syracuseStep 2542747 = 3814121) B3814121
theorem B3390329 : Blo 2259435 3390329 := bstep (se 2 (by rfl) ⟨1271373, by rfl⟩ : syracuseStep 3390329 = 2542747) B2542747
theorem B2260219 : Blo 2259435 2260219 := bstep (se 1 (by rfl) ⟨1695164, by rfl⟩ : syracuseStep 2260219 = 3390329) B3390329
theorem B3531005 : Blo 2259435 3531005 := bbase (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) (by norm_num)
theorem B2354003 : Blo 2259435 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B25109365 : Blo 2259435 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B33479153 : Blo 2259435 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B22319435 : Blo 2259435 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B14879623 : Blo 2259435 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B19839497 : Blo 2259435 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B52905325 : Blo 2259435 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B70540433 : Blo 2259435 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B47026955 : Blo 2259435 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B31351303 : Blo 2259435 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B167206949 : Blo 2259435 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B111471299 : Blo 2259435 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B74314199 : Blo 2259435 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B49542799 : Blo 2259435 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B66057065 : Blo 2259435 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B44038043 : Blo 2259435 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B29358695 : Blo 2259435 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B19572463 : Blo 2259435 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B26096617 : Blo 2259435 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B34795489 : Blo 2259435 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B46393985 : Blo 2259435 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B123717293 : Blo 2259435 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B82478195 : Blo 2259435 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B54985463 : Blo 2259435 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B36656975 : Blo 2259435 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B24437983 : Blo 2259435 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B32583977 : Blo 2259435 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B21722651 : Blo 2259435 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B14481767 : Blo 2259435 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B38618045 : Blo 2259435 38618045 := bstep (se 3 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 38618045 = 14481767) B14481767
theorem B25745363 : Blo 2259435 25745363 := bstep (se 1 (by rfl) ⟨19309022, by rfl⟩ : syracuseStep 25745363 = 38618045) B38618045
theorem B17163575 : Blo 2259435 17163575 := bstep (se 1 (by rfl) ⟨12872681, by rfl⟩ : syracuseStep 17163575 = 25745363) B25745363
theorem B11442383 : Blo 2259435 11442383 := bstep (se 1 (by rfl) ⟨8581787, by rfl⟩ : syracuseStep 11442383 = 17163575) B17163575
theorem B7628255 : Blo 2259435 7628255 := bstep (se 1 (by rfl) ⟨5721191, by rfl⟩ : syracuseStep 7628255 = 11442383) B11442383
theorem B5085503 : Blo 2259435 5085503 := bstep (se 1 (by rfl) ⟨3814127, by rfl⟩ : syracuseStep 5085503 = 7628255) B7628255
theorem B3390335 : Blo 2259435 3390335 := bstep (se 1 (by rfl) ⟨2542751, by rfl⟩ : syracuseStep 3390335 = 5085503) B5085503
theorem B2260223 : Blo 2259435 2260223 := bstep (se 1 (by rfl) ⟨1695167, by rfl⟩ : syracuseStep 2260223 = 3390335) B3390335
theorem B3390341 : Blo 2259435 3390341 := bbase (se 4 (by rfl) ⟨317844, by rfl⟩ : syracuseStep 3390341 = 635689) (by norm_num)
theorem B2260227 : Blo 2259435 2260227 := bstep (se 1 (by rfl) ⟨1695170, by rfl⟩ : syracuseStep 2260227 = 3390341) B3390341
theorem B3814141 : Blo 2259435 3814141 := bbase (se 3 (by rfl) ⟨715151, by rfl⟩ : syracuseStep 3814141 = 1430303) (by norm_num)
theorem B5085521 : Blo 2259435 5085521 := bstep (se 2 (by rfl) ⟨1907070, by rfl⟩ : syracuseStep 5085521 = 3814141) B3814141
theorem B3390347 : Blo 2259435 3390347 := bstep (se 1 (by rfl) ⟨2542760, by rfl⟩ : syracuseStep 3390347 = 5085521) B5085521
theorem B2260231 : Blo 2259435 2260231 := bstep (se 1 (by rfl) ⟨1695173, by rfl⟩ : syracuseStep 2260231 = 3390347) B3390347
theorem B2542765 : Blo 2259435 2542765 := bbase (se 3 (by rfl) ⟨476768, by rfl⟩ : syracuseStep 2542765 = 953537) (by norm_num)
theorem B3390353 : Blo 2259435 3390353 := bstep (se 2 (by rfl) ⟨1271382, by rfl⟩ : syracuseStep 3390353 = 2542765) B2542765
theorem B2260235 : Blo 2259435 2260235 := bstep (se 1 (by rfl) ⟨1695176, by rfl⟩ : syracuseStep 2260235 = 3390353) B3390353
theorem B7628309 : Blo 2259435 7628309 := bbase (se 6 (by rfl) ⟨178788, by rfl⟩ : syracuseStep 7628309 = 357577) (by norm_num)
theorem B5085539 : Blo 2259435 5085539 := bstep (se 1 (by rfl) ⟨3814154, by rfl⟩ : syracuseStep 5085539 = 7628309) B7628309
theorem B3390359 : Blo 2259435 3390359 := bstep (se 1 (by rfl) ⟨2542769, by rfl⟩ : syracuseStep 3390359 = 5085539) B5085539
theorem B2260239 : Blo 2259435 2260239 := bstep (se 1 (by rfl) ⟨1695179, by rfl⟩ : syracuseStep 2260239 = 3390359) B3390359
theorem B3390365 : Blo 2259435 3390365 := bbase (se 3 (by rfl) ⟨635693, by rfl⟩ : syracuseStep 3390365 = 1271387) (by norm_num)
theorem B2260243 : Blo 2259435 2260243 := bstep (se 1 (by rfl) ⟨1695182, by rfl⟩ : syracuseStep 2260243 = 3390365) B3390365
theorem B5085557 : Blo 2259435 5085557 := bbase (se 5 (by rfl) ⟨238385, by rfl⟩ : syracuseStep 5085557 = 476771) (by norm_num)
theorem B3390371 : Blo 2259435 3390371 := bstep (se 1 (by rfl) ⟨2542778, by rfl⟩ : syracuseStep 3390371 = 5085557) B5085557
theorem B2260247 : Blo 2259435 2260247 := bstep (se 1 (by rfl) ⟨1695185, by rfl⟩ : syracuseStep 2260247 = 3390371) B3390371
theorem B6109573 : Blo 2259435 6109573 := bbase (se 4 (by rfl) ⟨572772, by rfl⟩ : syracuseStep 6109573 = 1145545) (by norm_num)
theorem B8146097 : Blo 2259435 8146097 := bstep (se 2 (by rfl) ⟨3054786, by rfl⟩ : syracuseStep 8146097 = 6109573) B6109573
theorem B5430731 : Blo 2259435 5430731 := bstep (se 1 (by rfl) ⟨4073048, by rfl⟩ : syracuseStep 5430731 = 8146097) B8146097
theorem B14481949 : Blo 2259435 14481949 := bstep (se 3 (by rfl) ⟨2715365, by rfl⟩ : syracuseStep 14481949 = 5430731) B5430731
theorem B19309265 : Blo 2259435 19309265 := bstep (se 2 (by rfl) ⟨7240974, by rfl⟩ : syracuseStep 19309265 = 14481949) B14481949
theorem B12872843 : Blo 2259435 12872843 := bstep (se 1 (by rfl) ⟨9654632, by rfl⟩ : syracuseStep 12872843 = 19309265) B19309265
theorem B8581895 : Blo 2259435 8581895 := bstep (se 1 (by rfl) ⟨6436421, by rfl⟩ : syracuseStep 8581895 = 12872843) B12872843
theorem B5721263 : Blo 2259435 5721263 := bstep (se 1 (by rfl) ⟨4290947, by rfl⟩ : syracuseStep 5721263 = 8581895) B8581895
theorem B3814175 : Blo 2259435 3814175 := bstep (se 1 (by rfl) ⟨2860631, by rfl⟩ : syracuseStep 3814175 = 5721263) B5721263
theorem B2542783 : Blo 2259435 2542783 := bstep (se 1 (by rfl) ⟨1907087, by rfl⟩ : syracuseStep 2542783 = 3814175) B3814175
theorem B3390377 : Blo 2259435 3390377 := bstep (se 2 (by rfl) ⟨1271391, by rfl⟩ : syracuseStep 3390377 = 2542783) B2542783
theorem B2260251 : Blo 2259435 2260251 := bstep (se 1 (by rfl) ⟨1695188, by rfl⟩ : syracuseStep 2260251 = 3390377) B3390377
theorem B8581909 : Blo 2259435 8581909 := bbase (se 6 (by rfl) ⟨201138, by rfl⟩ : syracuseStep 8581909 = 402277) (by norm_num)
theorem B11442545 : Blo 2259435 11442545 := bstep (se 2 (by rfl) ⟨4290954, by rfl⟩ : syracuseStep 11442545 = 8581909) B8581909
theorem B7628363 : Blo 2259435 7628363 := bstep (se 1 (by rfl) ⟨5721272, by rfl⟩ : syracuseStep 7628363 = 11442545) B11442545
theorem B5085575 : Blo 2259435 5085575 := bstep (se 1 (by rfl) ⟨3814181, by rfl⟩ : syracuseStep 5085575 = 7628363) B7628363
theorem B3390383 : Blo 2259435 3390383 := bstep (se 1 (by rfl) ⟨2542787, by rfl⟩ : syracuseStep 3390383 = 5085575) B5085575
theorem B2260255 : Blo 2259435 2260255 := bstep (se 1 (by rfl) ⟨1695191, by rfl⟩ : syracuseStep 2260255 = 3390383) B3390383
theorem B3390389 : Blo 2259435 3390389 := bbase (se 5 (by rfl) ⟨158924, by rfl⟩ : syracuseStep 3390389 = 317849) (by norm_num)
theorem B2260259 : Blo 2259435 2260259 := bstep (se 1 (by rfl) ⟨1695194, by rfl⟩ : syracuseStep 2260259 = 3390389) B3390389
theorem B5721293 : Blo 2259435 5721293 := bbase (se 3 (by rfl) ⟨1072742, by rfl⟩ : syracuseStep 5721293 = 2145485) (by norm_num)
theorem B3814195 : Blo 2259435 3814195 := bstep (se 1 (by rfl) ⟨2860646, by rfl⟩ : syracuseStep 3814195 = 5721293) B5721293
theorem B5085593 : Blo 2259435 5085593 := bstep (se 2 (by rfl) ⟨1907097, by rfl⟩ : syracuseStep 5085593 = 3814195) B3814195
theorem B3390395 : Blo 2259435 3390395 := bstep (se 1 (by rfl) ⟨2542796, by rfl⟩ : syracuseStep 3390395 = 5085593) B5085593
theorem B2260263 : Blo 2259435 2260263 := bstep (se 1 (by rfl) ⟨1695197, by rfl⟩ : syracuseStep 2260263 = 3390395) B3390395
theorem B2542801 : Blo 2259435 2542801 := bbase (se 2 (by rfl) ⟨953550, by rfl⟩ : syracuseStep 2542801 = 1907101) (by norm_num)
theorem B3390401 : Blo 2259435 3390401 := bstep (se 2 (by rfl) ⟨1271400, by rfl⟩ : syracuseStep 3390401 = 2542801) B2542801
theorem B2260267 : Blo 2259435 2260267 := bstep (se 1 (by rfl) ⟨1695200, by rfl⟩ : syracuseStep 2260267 = 3390401) B3390401
theorem B12385973 : Blo 2259435 12385973 := bbase (se 5 (by rfl) ⟨580592, by rfl⟩ : syracuseStep 12385973 = 1161185) (by norm_num)
theorem B8257315 : Blo 2259435 8257315 := bstep (se 1 (by rfl) ⟨6192986, by rfl⟩ : syracuseStep 8257315 = 12385973) B12385973
theorem B11009753 : Blo 2259435 11009753 := bstep (se 2 (by rfl) ⟨4128657, by rfl⟩ : syracuseStep 11009753 = 8257315) B8257315
theorem B7339835 : Blo 2259435 7339835 := bstep (se 1 (by rfl) ⟨5504876, by rfl⟩ : syracuseStep 7339835 = 11009753) B11009753
theorem B4893223 : Blo 2259435 4893223 := bstep (se 1 (by rfl) ⟨3669917, by rfl⟩ : syracuseStep 4893223 = 7339835) B7339835
theorem B6524297 : Blo 2259435 6524297 := bstep (se 2 (by rfl) ⟨2446611, by rfl⟩ : syracuseStep 6524297 = 4893223) B4893223
theorem B4349531 : Blo 2259435 4349531 := bstep (se 1 (by rfl) ⟨3262148, by rfl⟩ : syracuseStep 4349531 = 6524297) B6524297
theorem B2899687 : Blo 2259435 2899687 := bstep (se 1 (by rfl) ⟨2174765, by rfl⟩ : syracuseStep 2899687 = 4349531) B4349531
theorem B3866249 : Blo 2259435 3866249 := bstep (se 2 (by rfl) ⟨1449843, by rfl⟩ : syracuseStep 3866249 = 2899687) B2899687
theorem B10309997 : Blo 2259435 10309997 := bstep (se 3 (by rfl) ⟨1933124, by rfl⟩ : syracuseStep 10309997 = 3866249) B3866249
theorem B6873331 : Blo 2259435 6873331 := bstep (se 1 (by rfl) ⟨5154998, by rfl⟩ : syracuseStep 6873331 = 10309997) B10309997
theorem B9164441 : Blo 2259435 9164441 := bstep (se 2 (by rfl) ⟨3436665, by rfl⟩ : syracuseStep 9164441 = 6873331) B6873331
theorem B24438509 : Blo 2259435 24438509 := bstep (se 3 (by rfl) ⟨4582220, by rfl⟩ : syracuseStep 24438509 = 9164441) B9164441
theorem B16292339 : Blo 2259435 16292339 := bstep (se 1 (by rfl) ⟨12219254, by rfl⟩ : syracuseStep 16292339 = 24438509) B24438509
theorem B10861559 : Blo 2259435 10861559 := bstep (se 1 (by rfl) ⟨8146169, by rfl⟩ : syracuseStep 10861559 = 16292339) B16292339
theorem B7241039 : Blo 2259435 7241039 := bstep (se 1 (by rfl) ⟨5430779, by rfl⟩ : syracuseStep 7241039 = 10861559) B10861559
theorem B4827359 : Blo 2259435 4827359 := bstep (se 1 (by rfl) ⟨3620519, by rfl⟩ : syracuseStep 4827359 = 7241039) B7241039
theorem B3218239 : Blo 2259435 3218239 := bstep (se 1 (by rfl) ⟨2413679, by rfl⟩ : syracuseStep 3218239 = 4827359) B4827359
theorem B4290985 : Blo 2259435 4290985 := bstep (se 2 (by rfl) ⟨1609119, by rfl⟩ : syracuseStep 4290985 = 3218239) B3218239
theorem B5721313 : Blo 2259435 5721313 := bstep (se 2 (by rfl) ⟨2145492, by rfl⟩ : syracuseStep 5721313 = 4290985) B4290985
theorem B7628417 : Blo 2259435 7628417 := bstep (se 2 (by rfl) ⟨2860656, by rfl⟩ : syracuseStep 7628417 = 5721313) B5721313
theorem B5085611 : Blo 2259435 5085611 := bstep (se 1 (by rfl) ⟨3814208, by rfl⟩ : syracuseStep 5085611 = 7628417) B7628417
theorem B3390407 : Blo 2259435 3390407 := bstep (se 1 (by rfl) ⟨2542805, by rfl⟩ : syracuseStep 3390407 = 5085611) B5085611
theorem B2260271 : Blo 2259435 2260271 := bstep (se 1 (by rfl) ⟨1695203, by rfl⟩ : syracuseStep 2260271 = 3390407) B3390407
theorem B3390413 : Blo 2259435 3390413 := bbase (se 3 (by rfl) ⟨635702, by rfl⟩ : syracuseStep 3390413 = 1271405) (by norm_num)
theorem B2260275 : Blo 2259435 2260275 := bstep (se 1 (by rfl) ⟨1695206, by rfl⟩ : syracuseStep 2260275 = 3390413) B3390413
theorem B5085629 : Blo 2259435 5085629 := bbase (se 3 (by rfl) ⟨953555, by rfl⟩ : syracuseStep 5085629 = 1907111) (by norm_num)
theorem B3390419 : Blo 2259435 3390419 := bstep (se 1 (by rfl) ⟨2542814, by rfl⟩ : syracuseStep 3390419 = 5085629) B5085629
theorem B2260279 : Blo 2259435 2260279 := bstep (se 1 (by rfl) ⟨1695209, by rfl⟩ : syracuseStep 2260279 = 3390419) B3390419
theorem B3814229 : Blo 2259435 3814229 := bbase (se 9 (by rfl) ⟨11174, by rfl⟩ : syracuseStep 3814229 = 22349) (by norm_num)
theorem B2542819 : Blo 2259435 2542819 := bstep (se 1 (by rfl) ⟨1907114, by rfl⟩ : syracuseStep 2542819 = 3814229) B3814229
theorem B3390425 : Blo 2259435 3390425 := bstep (se 2 (by rfl) ⟨1271409, by rfl⟩ : syracuseStep 3390425 = 2542819) B2542819
theorem B2260283 : Blo 2259435 2260283 := bstep (se 1 (by rfl) ⟨1695212, by rfl⟩ : syracuseStep 2260283 = 3390425) B3390425
theorem B4582253 : Blo 2259435 4582253 := bbase (se 3 (by rfl) ⟨859172, by rfl⟩ : syracuseStep 4582253 = 1718345) (by norm_num)
theorem B3054835 : Blo 2259435 3054835 := bstep (se 1 (by rfl) ⟨2291126, by rfl⟩ : syracuseStep 3054835 = 4582253) B4582253
theorem B4073113 : Blo 2259435 4073113 := bstep (se 2 (by rfl) ⟨1527417, by rfl⟩ : syracuseStep 4073113 = 3054835) B3054835
theorem B5430817 : Blo 2259435 5430817 := bstep (se 2 (by rfl) ⟨2036556, by rfl⟩ : syracuseStep 5430817 = 4073113) B4073113
theorem B7241089 : Blo 2259435 7241089 := bstep (se 2 (by rfl) ⟨2715408, by rfl⟩ : syracuseStep 7241089 = 5430817) B5430817
theorem B9654785 : Blo 2259435 9654785 := bstep (se 2 (by rfl) ⟨3620544, by rfl⟩ : syracuseStep 9654785 = 7241089) B7241089
theorem B6436523 : Blo 2259435 6436523 := bstep (se 1 (by rfl) ⟨4827392, by rfl⟩ : syracuseStep 6436523 = 9654785) B9654785
theorem B17164061 : Blo 2259435 17164061 := bstep (se 3 (by rfl) ⟨3218261, by rfl⟩ : syracuseStep 17164061 = 6436523) B6436523
theorem B11442707 : Blo 2259435 11442707 := bstep (se 1 (by rfl) ⟨8582030, by rfl⟩ : syracuseStep 11442707 = 17164061) B17164061
theorem B7628471 : Blo 2259435 7628471 := bstep (se 1 (by rfl) ⟨5721353, by rfl⟩ : syracuseStep 7628471 = 11442707) B11442707
theorem B5085647 : Blo 2259435 5085647 := bstep (se 1 (by rfl) ⟨3814235, by rfl⟩ : syracuseStep 5085647 = 7628471) B7628471
theorem B3390431 : Blo 2259435 3390431 := bstep (se 1 (by rfl) ⟨2542823, by rfl⟩ : syracuseStep 3390431 = 5085647) B5085647
theorem B2260287 : Blo 2259435 2260287 := bstep (se 1 (by rfl) ⟨1695215, by rfl⟩ : syracuseStep 2260287 = 3390431) B3390431
theorem B3390437 : Blo 2259435 3390437 := bbase (se 4 (by rfl) ⟨317853, by rfl⟩ : syracuseStep 3390437 = 635707) (by norm_num)
theorem B2260291 : Blo 2259435 2260291 := bstep (se 1 (by rfl) ⟨1695218, by rfl⟩ : syracuseStep 2260291 = 3390437) B3390437
theorem B9654821 : Blo 2259435 9654821 := bbase (se 4 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 9654821 = 1810279) (by norm_num)
theorem B6436547 : Blo 2259435 6436547 := bstep (se 1 (by rfl) ⟨4827410, by rfl⟩ : syracuseStep 6436547 = 9654821) B9654821
theorem B4291031 : Blo 2259435 4291031 := bstep (se 1 (by rfl) ⟨3218273, by rfl⟩ : syracuseStep 4291031 = 6436547) B6436547
theorem B2860687 : Blo 2259435 2860687 := bstep (se 1 (by rfl) ⟨2145515, by rfl⟩ : syracuseStep 2860687 = 4291031) B4291031
theorem B3814249 : Blo 2259435 3814249 := bstep (se 2 (by rfl) ⟨1430343, by rfl⟩ : syracuseStep 3814249 = 2860687) B2860687
theorem B5085665 : Blo 2259435 5085665 := bstep (se 2 (by rfl) ⟨1907124, by rfl⟩ : syracuseStep 5085665 = 3814249) B3814249
theorem B3390443 : Blo 2259435 3390443 := bstep (se 1 (by rfl) ⟨2542832, by rfl⟩ : syracuseStep 3390443 = 5085665) B5085665
theorem B2260295 : Blo 2259435 2260295 := bstep (se 1 (by rfl) ⟨1695221, by rfl⟩ : syracuseStep 2260295 = 3390443) B3390443
theorem B2542837 : Blo 2259435 2542837 := bbase (se 5 (by rfl) ⟨119195, by rfl⟩ : syracuseStep 2542837 = 238391) (by norm_num)
theorem B3390449 : Blo 2259435 3390449 := bstep (se 2 (by rfl) ⟨1271418, by rfl⟩ : syracuseStep 3390449 = 2542837) B2542837
theorem B2260299 : Blo 2259435 2260299 := bstep (se 1 (by rfl) ⟨1695224, by rfl⟩ : syracuseStep 2260299 = 3390449) B3390449
theorem B2860697 : Blo 2259435 2860697 := bbase (se 2 (by rfl) ⟨1072761, by rfl⟩ : syracuseStep 2860697 = 2145523) (by norm_num)
theorem B7628525 : Blo 2259435 7628525 := bstep (se 3 (by rfl) ⟨1430348, by rfl⟩ : syracuseStep 7628525 = 2860697) B2860697
theorem B5085683 : Blo 2259435 5085683 := bstep (se 1 (by rfl) ⟨3814262, by rfl⟩ : syracuseStep 5085683 = 7628525) B7628525
theorem B3390455 : Blo 2259435 3390455 := bstep (se 1 (by rfl) ⟨2542841, by rfl⟩ : syracuseStep 3390455 = 5085683) B5085683
theorem B2260303 : Blo 2259435 2260303 := bstep (se 1 (by rfl) ⟨1695227, by rfl⟩ : syracuseStep 2260303 = 3390455) B3390455
theorem B3390461 : Blo 2259435 3390461 := bbase (se 3 (by rfl) ⟨635711, by rfl⟩ : syracuseStep 3390461 = 1271423) (by norm_num)
theorem B2260307 : Blo 2259435 2260307 := bstep (se 1 (by rfl) ⟨1695230, by rfl⟩ : syracuseStep 2260307 = 3390461) B3390461
theorem B5085701 : Blo 2259435 5085701 := bbase (se 4 (by rfl) ⟨476784, by rfl⟩ : syracuseStep 5085701 = 953569) (by norm_num)
theorem B3390467 : Blo 2259435 3390467 := bstep (se 1 (by rfl) ⟨2542850, by rfl⟩ : syracuseStep 3390467 = 5085701) B5085701
theorem B2260311 : Blo 2259435 2260311 := bstep (se 1 (by rfl) ⟨1695233, by rfl⟩ : syracuseStep 2260311 = 3390467) B3390467
theorem B4291069 : Blo 2259435 4291069 := bbase (se 3 (by rfl) ⟨804575, by rfl⟩ : syracuseStep 4291069 = 1609151) (by norm_num)
theorem B5721425 : Blo 2259435 5721425 := bstep (se 2 (by rfl) ⟨2145534, by rfl⟩ : syracuseStep 5721425 = 4291069) B4291069
theorem B3814283 : Blo 2259435 3814283 := bstep (se 1 (by rfl) ⟨2860712, by rfl⟩ : syracuseStep 3814283 = 5721425) B5721425
theorem B2542855 : Blo 2259435 2542855 := bstep (se 1 (by rfl) ⟨1907141, by rfl⟩ : syracuseStep 2542855 = 3814283) B3814283
theorem B3390473 : Blo 2259435 3390473 := bstep (se 2 (by rfl) ⟨1271427, by rfl⟩ : syracuseStep 3390473 = 2542855) B2542855
theorem B2260315 : Blo 2259435 2260315 := bstep (se 1 (by rfl) ⟨1695236, by rfl⟩ : syracuseStep 2260315 = 3390473) B3390473
theorem B11442869 : Blo 2259435 11442869 := bbase (se 5 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 11442869 = 1072769) (by norm_num)
theorem B7628579 : Blo 2259435 7628579 := bstep (se 1 (by rfl) ⟨5721434, by rfl⟩ : syracuseStep 7628579 = 11442869) B11442869
theorem B5085719 : Blo 2259435 5085719 := bstep (se 1 (by rfl) ⟨3814289, by rfl⟩ : syracuseStep 5085719 = 7628579) B7628579
theorem B3390479 : Blo 2259435 3390479 := bstep (se 1 (by rfl) ⟨2542859, by rfl⟩ : syracuseStep 3390479 = 5085719) B5085719
theorem B2260319 : Blo 2259435 2260319 := bstep (se 1 (by rfl) ⟨1695239, by rfl⟩ : syracuseStep 2260319 = 3390479) B3390479
theorem B3390485 : Blo 2259435 3390485 := bbase (se 6 (by rfl) ⟨79464, by rfl⟩ : syracuseStep 3390485 = 158929) (by norm_num)
theorem B2260323 : Blo 2259435 2260323 := bstep (se 1 (by rfl) ⟨1695242, by rfl⟩ : syracuseStep 2260323 = 3390485) B3390485
theorem B5505013 : Blo 2259435 5505013 := bbase (se 5 (by rfl) ⟨258047, by rfl⟩ : syracuseStep 5505013 = 516095) (by norm_num)
theorem B7340017 : Blo 2259435 7340017 := bstep (se 2 (by rfl) ⟨2752506, by rfl⟩ : syracuseStep 7340017 = 5505013) B5505013
theorem B9786689 : Blo 2259435 9786689 := bstep (se 2 (by rfl) ⟨3670008, by rfl⟩ : syracuseStep 9786689 = 7340017) B7340017
theorem B6524459 : Blo 2259435 6524459 := bstep (se 1 (by rfl) ⟨4893344, by rfl⟩ : syracuseStep 6524459 = 9786689) B9786689
theorem B4349639 : Blo 2259435 4349639 := bstep (se 1 (by rfl) ⟨3262229, by rfl⟩ : syracuseStep 4349639 = 6524459) B6524459
theorem B11599037 : Blo 2259435 11599037 := bstep (se 3 (by rfl) ⟨2174819, by rfl⟩ : syracuseStep 11599037 = 4349639) B4349639
theorem B7732691 : Blo 2259435 7732691 := bstep (se 1 (by rfl) ⟨5799518, by rfl⟩ : syracuseStep 7732691 = 11599037) B11599037
theorem B5155127 : Blo 2259435 5155127 := bstep (se 1 (by rfl) ⟨3866345, by rfl⟩ : syracuseStep 5155127 = 7732691) B7732691
theorem B3436751 : Blo 2259435 3436751 := bstep (se 1 (by rfl) ⟨2577563, by rfl⟩ : syracuseStep 3436751 = 5155127) B5155127
theorem B2291167 : Blo 2259435 2291167 := bstep (se 1 (by rfl) ⟨1718375, by rfl⟩ : syracuseStep 2291167 = 3436751) B3436751
theorem B3054889 : Blo 2259435 3054889 := bstep (se 2 (by rfl) ⟨1145583, by rfl⟩ : syracuseStep 3054889 = 2291167) B2291167
theorem B4073185 : Blo 2259435 4073185 := bstep (se 2 (by rfl) ⟨1527444, by rfl⟩ : syracuseStep 4073185 = 3054889) B3054889
theorem B21723653 : Blo 2259435 21723653 := bstep (se 4 (by rfl) ⟨2036592, by rfl⟩ : syracuseStep 21723653 = 4073185) B4073185
theorem B14482435 : Blo 2259435 14482435 := bstep (se 1 (by rfl) ⟨10861826, by rfl⟩ : syracuseStep 14482435 = 21723653) B21723653
theorem B19309913 : Blo 2259435 19309913 := bstep (se 2 (by rfl) ⟨7241217, by rfl⟩ : syracuseStep 19309913 = 14482435) B14482435
theorem B12873275 : Blo 2259435 12873275 := bstep (se 1 (by rfl) ⟨9654956, by rfl⟩ : syracuseStep 12873275 = 19309913) B19309913
theorem B8582183 : Blo 2259435 8582183 := bstep (se 1 (by rfl) ⟨6436637, by rfl⟩ : syracuseStep 8582183 = 12873275) B12873275
theorem B5721455 : Blo 2259435 5721455 := bstep (se 1 (by rfl) ⟨4291091, by rfl⟩ : syracuseStep 5721455 = 8582183) B8582183
theorem B3814303 : Blo 2259435 3814303 := bstep (se 1 (by rfl) ⟨2860727, by rfl⟩ : syracuseStep 3814303 = 5721455) B5721455
theorem B5085737 : Blo 2259435 5085737 := bstep (se 2 (by rfl) ⟨1907151, by rfl⟩ : syracuseStep 5085737 = 3814303) B3814303
theorem B3390491 : Blo 2259435 3390491 := bstep (se 1 (by rfl) ⟨2542868, by rfl⟩ : syracuseStep 3390491 = 5085737) B5085737
theorem B2260327 : Blo 2259435 2260327 := bstep (se 1 (by rfl) ⟨1695245, by rfl⟩ : syracuseStep 2260327 = 3390491) B3390491
theorem B2542873 : Blo 2259435 2542873 := bbase (se 2 (by rfl) ⟨953577, by rfl⟩ : syracuseStep 2542873 = 1907155) (by norm_num)
theorem B3390497 : Blo 2259435 3390497 := bstep (se 2 (by rfl) ⟨1271436, by rfl⟩ : syracuseStep 3390497 = 2542873) B2542873
theorem B2260331 : Blo 2259435 2260331 := bstep (se 1 (by rfl) ⟨1695248, by rfl⟩ : syracuseStep 2260331 = 3390497) B3390497
theorem B8582213 : Blo 2259435 8582213 := bbase (se 4 (by rfl) ⟨804582, by rfl⟩ : syracuseStep 8582213 = 1609165) (by norm_num)
theorem B5721475 : Blo 2259435 5721475 := bstep (se 1 (by rfl) ⟨4291106, by rfl⟩ : syracuseStep 5721475 = 8582213) B8582213
theorem B7628633 : Blo 2259435 7628633 := bstep (se 2 (by rfl) ⟨2860737, by rfl⟩ : syracuseStep 7628633 = 5721475) B5721475
theorem B5085755 : Blo 2259435 5085755 := bstep (se 1 (by rfl) ⟨3814316, by rfl⟩ : syracuseStep 5085755 = 7628633) B7628633
theorem B3390503 : Blo 2259435 3390503 := bstep (se 1 (by rfl) ⟨2542877, by rfl⟩ : syracuseStep 3390503 = 5085755) B5085755
theorem B2260335 : Blo 2259435 2260335 := bstep (se 1 (by rfl) ⟨1695251, by rfl⟩ : syracuseStep 2260335 = 3390503) B3390503
theorem B3390509 : Blo 2259435 3390509 := bbase (se 3 (by rfl) ⟨635720, by rfl⟩ : syracuseStep 3390509 = 1271441) (by norm_num)
theorem B2260339 : Blo 2259435 2260339 := bstep (se 1 (by rfl) ⟨1695254, by rfl⟩ : syracuseStep 2260339 = 3390509) B3390509
theorem B5085773 : Blo 2259435 5085773 := bbase (se 3 (by rfl) ⟨953582, by rfl⟩ : syracuseStep 5085773 = 1907165) (by norm_num)
theorem B3390515 : Blo 2259435 3390515 := bstep (se 1 (by rfl) ⟨2542886, by rfl⟩ : syracuseStep 3390515 = 5085773) B5085773
theorem B2260343 : Blo 2259435 2260343 := bstep (se 1 (by rfl) ⟨1695257, by rfl⟩ : syracuseStep 2260343 = 3390515) B3390515
theorem B2860753 : Blo 2259435 2860753 := bbase (se 2 (by rfl) ⟨1072782, by rfl⟩ : syracuseStep 2860753 = 2145565) (by norm_num)
theorem B3814337 : Blo 2259435 3814337 := bstep (se 2 (by rfl) ⟨1430376, by rfl⟩ : syracuseStep 3814337 = 2860753) B2860753
theorem B2542891 : Blo 2259435 2542891 := bstep (se 1 (by rfl) ⟨1907168, by rfl⟩ : syracuseStep 2542891 = 3814337) B3814337
theorem B3390521 : Blo 2259435 3390521 := bstep (se 2 (by rfl) ⟨1271445, by rfl⟩ : syracuseStep 3390521 = 2542891) B2542891
theorem B2260347 : Blo 2259435 2260347 := bstep (se 1 (by rfl) ⟨1695260, by rfl⟩ : syracuseStep 2260347 = 3390521) B3390521
theorem B5155181 : Blo 2259435 5155181 := bbase (se 3 (by rfl) ⟨966596, by rfl⟩ : syracuseStep 5155181 = 1933193) (by norm_num)
theorem B3436787 : Blo 2259435 3436787 := bstep (se 1 (by rfl) ⟨2577590, by rfl⟩ : syracuseStep 3436787 = 5155181) B5155181
theorem B9164765 : Blo 2259435 9164765 := bstep (se 3 (by rfl) ⟨1718393, by rfl⟩ : syracuseStep 9164765 = 3436787) B3436787
theorem B6109843 : Blo 2259435 6109843 := bstep (se 1 (by rfl) ⟨4582382, by rfl⟩ : syracuseStep 6109843 = 9164765) B9164765
theorem B8146457 : Blo 2259435 8146457 := bstep (se 2 (by rfl) ⟨3054921, by rfl⟩ : syracuseStep 8146457 = 6109843) B6109843
theorem B5430971 : Blo 2259435 5430971 := bstep (se 1 (by rfl) ⟨4073228, by rfl⟩ : syracuseStep 5430971 = 8146457) B8146457
theorem B3620647 : Blo 2259435 3620647 := bstep (se 1 (by rfl) ⟨2715485, by rfl⟩ : syracuseStep 3620647 = 5430971) B5430971
theorem B4827529 : Blo 2259435 4827529 := bstep (se 2 (by rfl) ⟨1810323, by rfl⟩ : syracuseStep 4827529 = 3620647) B3620647
theorem B25746821 : Blo 2259435 25746821 := bstep (se 4 (by rfl) ⟨2413764, by rfl⟩ : syracuseStep 25746821 = 4827529) B4827529
theorem B17164547 : Blo 2259435 17164547 := bstep (se 1 (by rfl) ⟨12873410, by rfl⟩ : syracuseStep 17164547 = 25746821) B25746821
theorem B11443031 : Blo 2259435 11443031 := bstep (se 1 (by rfl) ⟨8582273, by rfl⟩ : syracuseStep 11443031 = 17164547) B17164547
theorem B7628687 : Blo 2259435 7628687 := bstep (se 1 (by rfl) ⟨5721515, by rfl⟩ : syracuseStep 7628687 = 11443031) B11443031
theorem B5085791 : Blo 2259435 5085791 := bstep (se 1 (by rfl) ⟨3814343, by rfl⟩ : syracuseStep 5085791 = 7628687) B7628687
theorem B3390527 : Blo 2259435 3390527 := bstep (se 1 (by rfl) ⟨2542895, by rfl⟩ : syracuseStep 3390527 = 5085791) B5085791
theorem B2260351 : Blo 2259435 2260351 := bstep (se 1 (by rfl) ⟨1695263, by rfl⟩ : syracuseStep 2260351 = 3390527) B3390527
theorem B3390533 : Blo 2259435 3390533 := bbase (se 4 (by rfl) ⟨317862, by rfl⟩ : syracuseStep 3390533 = 635725) (by norm_num)
theorem B2260355 : Blo 2259435 2260355 := bstep (se 1 (by rfl) ⟨1695266, by rfl⟩ : syracuseStep 2260355 = 3390533) B3390533
theorem B3814357 : Blo 2259435 3814357 := bbase (se 7 (by rfl) ⟨44699, by rfl⟩ : syracuseStep 3814357 = 89399) (by norm_num)
theorem B5085809 : Blo 2259435 5085809 := bstep (se 2 (by rfl) ⟨1907178, by rfl⟩ : syracuseStep 5085809 = 3814357) B3814357
theorem B3390539 : Blo 2259435 3390539 := bstep (se 1 (by rfl) ⟨2542904, by rfl⟩ : syracuseStep 3390539 = 5085809) B5085809
theorem B2260359 : Blo 2259435 2260359 := bstep (se 1 (by rfl) ⟨1695269, by rfl⟩ : syracuseStep 2260359 = 3390539) B3390539
theorem B2542909 : Blo 2259435 2542909 := bbase (se 3 (by rfl) ⟨476795, by rfl⟩ : syracuseStep 2542909 = 953591) (by norm_num)
theorem B3390545 : Blo 2259435 3390545 := bstep (se 2 (by rfl) ⟨1271454, by rfl⟩ : syracuseStep 3390545 = 2542909) B2542909
theorem B2260363 : Blo 2259435 2260363 := bstep (se 1 (by rfl) ⟨1695272, by rfl⟩ : syracuseStep 2260363 = 3390545) B3390545
theorem B7628741 : Blo 2259435 7628741 := bbase (se 4 (by rfl) ⟨715194, by rfl⟩ : syracuseStep 7628741 = 1430389) (by norm_num)
theorem B5085827 : Blo 2259435 5085827 := bstep (se 1 (by rfl) ⟨3814370, by rfl⟩ : syracuseStep 5085827 = 7628741) B7628741
theorem B3390551 : Blo 2259435 3390551 := bstep (se 1 (by rfl) ⟨2542913, by rfl⟩ : syracuseStep 3390551 = 5085827) B5085827
theorem B2260367 : Blo 2259435 2260367 := bstep (se 1 (by rfl) ⟨1695275, by rfl⟩ : syracuseStep 2260367 = 3390551) B3390551
theorem B3390557 : Blo 2259435 3390557 := bbase (se 3 (by rfl) ⟨635729, by rfl⟩ : syracuseStep 3390557 = 1271459) (by norm_num)
theorem B2260371 : Blo 2259435 2260371 := bstep (se 1 (by rfl) ⟨1695278, by rfl⟩ : syracuseStep 2260371 = 3390557) B3390557
theorem B5085845 : Blo 2259435 5085845 := bbase (se 6 (by rfl) ⟨119199, by rfl⟩ : syracuseStep 5085845 = 238399) (by norm_num)
theorem B3390563 : Blo 2259435 3390563 := bstep (se 1 (by rfl) ⟨2542922, by rfl⟩ : syracuseStep 3390563 = 5085845) B5085845
theorem B2260375 : Blo 2259435 2260375 := bstep (se 1 (by rfl) ⟨1695281, by rfl⟩ : syracuseStep 2260375 = 3390563) B3390563
theorem B3620693 : Blo 2259435 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B2413795 : Blo 2259435 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B3218393 : Blo 2259435 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B8582381 : Blo 2259435 8582381 := bstep (se 3 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 8582381 = 3218393) B3218393
theorem B5721587 : Blo 2259435 5721587 := bstep (se 1 (by rfl) ⟨4291190, by rfl⟩ : syracuseStep 5721587 = 8582381) B8582381
theorem B3814391 : Blo 2259435 3814391 := bstep (se 1 (by rfl) ⟨2860793, by rfl⟩ : syracuseStep 3814391 = 5721587) B5721587
theorem B2542927 : Blo 2259435 2542927 := bstep (se 1 (by rfl) ⟨1907195, by rfl⟩ : syracuseStep 2542927 = 3814391) B3814391
theorem B3390569 : Blo 2259435 3390569 := bstep (se 2 (by rfl) ⟨1271463, by rfl⟩ : syracuseStep 3390569 = 2542927) B2542927
theorem B2260379 : Blo 2259435 2260379 := bstep (se 1 (by rfl) ⟨1695284, by rfl⟩ : syracuseStep 2260379 = 3390569) B3390569
theorem B5155253 : Blo 2259435 5155253 := bbase (se 5 (by rfl) ⟨241652, by rfl⟩ : syracuseStep 5155253 = 483305) (by norm_num)
theorem B3436835 : Blo 2259435 3436835 := bstep (se 1 (by rfl) ⟨2577626, by rfl⟩ : syracuseStep 3436835 = 5155253) B5155253
theorem B36659573 : Blo 2259435 36659573 := bstep (se 5 (by rfl) ⟨1718417, by rfl⟩ : syracuseStep 36659573 = 3436835) B3436835
theorem B24439715 : Blo 2259435 24439715 := bstep (se 1 (by rfl) ⟨18329786, by rfl⟩ : syracuseStep 24439715 = 36659573) B36659573
theorem B16293143 : Blo 2259435 16293143 := bstep (se 1 (by rfl) ⟨12219857, by rfl⟩ : syracuseStep 16293143 = 24439715) B24439715
theorem B10862095 : Blo 2259435 10862095 := bstep (se 1 (by rfl) ⟨8146571, by rfl⟩ : syracuseStep 10862095 = 16293143) B16293143
theorem B14482793 : Blo 2259435 14482793 := bstep (se 2 (by rfl) ⟨5431047, by rfl⟩ : syracuseStep 14482793 = 10862095) B10862095
theorem B9655195 : Blo 2259435 9655195 := bstep (se 1 (by rfl) ⟨7241396, by rfl⟩ : syracuseStep 9655195 = 14482793) B14482793
theorem B12873593 : Blo 2259435 12873593 := bstep (se 2 (by rfl) ⟨4827597, by rfl⟩ : syracuseStep 12873593 = 9655195) B9655195
theorem B8582395 : Blo 2259435 8582395 := bstep (se 1 (by rfl) ⟨6436796, by rfl⟩ : syracuseStep 8582395 = 12873593) B12873593
theorem B11443193 : Blo 2259435 11443193 := bstep (se 2 (by rfl) ⟨4291197, by rfl⟩ : syracuseStep 11443193 = 8582395) B8582395
theorem B7628795 : Blo 2259435 7628795 := bstep (se 1 (by rfl) ⟨5721596, by rfl⟩ : syracuseStep 7628795 = 11443193) B11443193
theorem B5085863 : Blo 2259435 5085863 := bstep (se 1 (by rfl) ⟨3814397, by rfl⟩ : syracuseStep 5085863 = 7628795) B7628795
theorem B3390575 : Blo 2259435 3390575 := bstep (se 1 (by rfl) ⟨2542931, by rfl⟩ : syracuseStep 3390575 = 5085863) B5085863
theorem B2260383 : Blo 2259435 2260383 := bstep (se 1 (by rfl) ⟨1695287, by rfl⟩ : syracuseStep 2260383 = 3390575) B3390575
theorem B3390581 : Blo 2259435 3390581 := bbase (se 5 (by rfl) ⟨158933, by rfl⟩ : syracuseStep 3390581 = 317867) (by norm_num)
theorem B2260387 : Blo 2259435 2260387 := bstep (se 1 (by rfl) ⟨1695290, by rfl⟩ : syracuseStep 2260387 = 3390581) B3390581
theorem B4291213 : Blo 2259435 4291213 := bbase (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) (by norm_num)
theorem B5721617 : Blo 2259435 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B3814411 : Blo 2259435 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B5085881 : Blo 2259435 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B3390587 : Blo 2259435 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2260391 : Blo 2259435 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B2542945 : Blo 2259435 2542945 := bbase (se 2 (by rfl) ⟨953604, by rfl⟩ : syracuseStep 2542945 = 1907209) (by norm_num)
theorem B3390593 : Blo 2259435 3390593 := bstep (se 2 (by rfl) ⟨1271472, by rfl⟩ : syracuseStep 3390593 = 2542945) B2542945
theorem B2260395 : Blo 2259435 2260395 := bstep (se 1 (by rfl) ⟨1695296, by rfl⟩ : syracuseStep 2260395 = 3390593) B3390593
theorem B5721637 : Blo 2259435 5721637 := bbase (se 4 (by rfl) ⟨536403, by rfl⟩ : syracuseStep 5721637 = 1072807) (by norm_num)
theorem B7628849 : Blo 2259435 7628849 := bstep (se 2 (by rfl) ⟨2860818, by rfl⟩ : syracuseStep 7628849 = 5721637) B5721637
theorem B5085899 : Blo 2259435 5085899 := bstep (se 1 (by rfl) ⟨3814424, by rfl⟩ : syracuseStep 5085899 = 7628849) B7628849
theorem B3390599 : Blo 2259435 3390599 := bstep (se 1 (by rfl) ⟨2542949, by rfl⟩ : syracuseStep 3390599 = 5085899) B5085899
theorem B2260399 : Blo 2259435 2260399 := bstep (se 1 (by rfl) ⟨1695299, by rfl⟩ : syracuseStep 2260399 = 3390599) B3390599
theorem B3390605 : Blo 2259435 3390605 := bbase (se 3 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 3390605 = 1271477) (by norm_num)
theorem B2260403 : Blo 2259435 2260403 := bstep (se 1 (by rfl) ⟨1695302, by rfl⟩ : syracuseStep 2260403 = 3390605) B3390605
theorem B5085917 : Blo 2259435 5085917 := bbase (se 3 (by rfl) ⟨953609, by rfl⟩ : syracuseStep 5085917 = 1907219) (by norm_num)
theorem B3390611 : Blo 2259435 3390611 := bstep (se 1 (by rfl) ⟨2542958, by rfl⟩ : syracuseStep 3390611 = 5085917) B5085917
theorem B2260407 : Blo 2259435 2260407 := bstep (se 1 (by rfl) ⟨1695305, by rfl⟩ : syracuseStep 2260407 = 3390611) B3390611
theorem B3814445 : Blo 2259435 3814445 := bbase (se 3 (by rfl) ⟨715208, by rfl⟩ : syracuseStep 3814445 = 1430417) (by norm_num)
theorem B2542963 : Blo 2259435 2542963 := bstep (se 1 (by rfl) ⟨1907222, by rfl⟩ : syracuseStep 2542963 = 3814445) B3814445
theorem B3390617 : Blo 2259435 3390617 := bstep (se 2 (by rfl) ⟨1271481, by rfl⟩ : syracuseStep 3390617 = 2542963) B2542963
theorem B2260411 : Blo 2259435 2260411 := bstep (se 1 (by rfl) ⟨1695308, by rfl⟩ : syracuseStep 2260411 = 3390617) B3390617
theorem B3181765 : Blo 2259435 3181765 := bbase (se 4 (by rfl) ⟨298290, by rfl⟩ : syracuseStep 3181765 = 596581) (by norm_num)
theorem B4242353 : Blo 2259435 4242353 := bstep (se 2 (by rfl) ⟨1590882, by rfl⟩ : syracuseStep 4242353 = 3181765) B3181765
theorem B11312941 : Blo 2259435 11312941 := bstep (se 3 (by rfl) ⟨2121176, by rfl⟩ : syracuseStep 11312941 = 4242353) B4242353
theorem B15083921 : Blo 2259435 15083921 := bstep (se 2 (by rfl) ⟨5656470, by rfl⟩ : syracuseStep 15083921 = 11312941) B11312941
theorem B10055947 : Blo 2259435 10055947 := bstep (se 1 (by rfl) ⟨7541960, by rfl⟩ : syracuseStep 10055947 = 15083921) B15083921
theorem B13407929 : Blo 2259435 13407929 := bstep (se 2 (by rfl) ⟨5027973, by rfl⟩ : syracuseStep 13407929 = 10055947) B10055947
theorem B8938619 : Blo 2259435 8938619 := bstep (se 1 (by rfl) ⟨6703964, by rfl⟩ : syracuseStep 8938619 = 13407929) B13407929
theorem B5959079 : Blo 2259435 5959079 := bstep (se 1 (by rfl) ⟨4469309, by rfl⟩ : syracuseStep 5959079 = 8938619) B8938619
theorem B3972719 : Blo 2259435 3972719 := bstep (se 1 (by rfl) ⟨2979539, by rfl⟩ : syracuseStep 3972719 = 5959079) B5959079
theorem B2648479 : Blo 2259435 2648479 := bstep (se 1 (by rfl) ⟨1986359, by rfl⟩ : syracuseStep 2648479 = 3972719) B3972719
theorem B3531305 : Blo 2259435 3531305 := bstep (se 2 (by rfl) ⟨1324239, by rfl⟩ : syracuseStep 3531305 = 2648479) B2648479
theorem B2354203 : Blo 2259435 2354203 := bstep (se 1 (by rfl) ⟨1765652, by rfl⟩ : syracuseStep 2354203 = 3531305) B3531305
theorem B3138937 : Blo 2259435 3138937 := bstep (se 2 (by rfl) ⟨1177101, by rfl⟩ : syracuseStep 3138937 = 2354203) B2354203
theorem B66963989 : Blo 2259435 66963989 := bstep (se 6 (by rfl) ⟨1569468, by rfl⟩ : syracuseStep 66963989 = 3138937) B3138937
theorem B44642659 : Blo 2259435 44642659 := bstep (se 1 (by rfl) ⟨33481994, by rfl⟩ : syracuseStep 44642659 = 66963989) B66963989
theorem B59523545 : Blo 2259435 59523545 := bstep (se 2 (by rfl) ⟨22321329, by rfl⟩ : syracuseStep 59523545 = 44642659) B44642659
theorem B158729453 : Blo 2259435 158729453 := bstep (se 3 (by rfl) ⟨29761772, by rfl⟩ : syracuseStep 158729453 = 59523545) B59523545
theorem B105819635 : Blo 2259435 105819635 := bstep (se 1 (by rfl) ⟨79364726, by rfl⟩ : syracuseStep 105819635 = 158729453) B158729453
theorem B282185693 : Blo 2259435 282185693 := bstep (se 3 (by rfl) ⟨52909817, by rfl⟩ : syracuseStep 282185693 = 105819635) B105819635
theorem B188123795 : Blo 2259435 188123795 := bstep (se 1 (by rfl) ⟨141092846, by rfl⟩ : syracuseStep 188123795 = 282185693) B282185693
theorem B125415863 : Blo 2259435 125415863 := bstep (se 1 (by rfl) ⟨94061897, by rfl⟩ : syracuseStep 125415863 = 188123795) B188123795
theorem B83610575 : Blo 2259435 83610575 := bstep (se 1 (by rfl) ⟨62707931, by rfl⟩ : syracuseStep 83610575 = 125415863) B125415863
theorem B55740383 : Blo 2259435 55740383 := bstep (se 1 (by rfl) ⟨41805287, by rfl⟩ : syracuseStep 55740383 = 83610575) B83610575
theorem B37160255 : Blo 2259435 37160255 := bstep (se 1 (by rfl) ⟨27870191, by rfl⟩ : syracuseStep 37160255 = 55740383) B55740383
theorem B99094013 : Blo 2259435 99094013 := bstep (se 3 (by rfl) ⟨18580127, by rfl⟩ : syracuseStep 99094013 = 37160255) B37160255
theorem B66062675 : Blo 2259435 66062675 := bstep (se 1 (by rfl) ⟨49547006, by rfl⟩ : syracuseStep 66062675 = 99094013) B99094013
theorem B176167133 : Blo 2259435 176167133 := bstep (se 3 (by rfl) ⟨33031337, by rfl⟩ : syracuseStep 176167133 = 66062675) B66062675
theorem B117444755 : Blo 2259435 117444755 := bstep (se 1 (by rfl) ⟨88083566, by rfl⟩ : syracuseStep 117444755 = 176167133) B176167133
theorem B78296503 : Blo 2259435 78296503 := bstep (se 1 (by rfl) ⟨58722377, by rfl⟩ : syracuseStep 78296503 = 117444755) B117444755
theorem B104395337 : Blo 2259435 104395337 := bstep (se 2 (by rfl) ⟨39148251, by rfl⟩ : syracuseStep 104395337 = 78296503) B78296503
theorem B69596891 : Blo 2259435 69596891 := bstep (se 1 (by rfl) ⟨52197668, by rfl⟩ : syracuseStep 69596891 = 104395337) B104395337
theorem B46397927 : Blo 2259435 46397927 := bstep (se 1 (by rfl) ⟨34798445, by rfl⟩ : syracuseStep 46397927 = 69596891) B69596891
theorem B30931951 : Blo 2259435 30931951 := bstep (se 1 (by rfl) ⟨23198963, by rfl⟩ : syracuseStep 30931951 = 46397927) B46397927
theorem B41242601 : Blo 2259435 41242601 := bstep (se 2 (by rfl) ⟨15465975, by rfl⟩ : syracuseStep 41242601 = 30931951) B30931951
theorem B27495067 : Blo 2259435 27495067 := bstep (se 1 (by rfl) ⟨20621300, by rfl⟩ : syracuseStep 27495067 = 41242601) B41242601
theorem B36660089 : Blo 2259435 36660089 := bstep (se 2 (by rfl) ⟨13747533, by rfl⟩ : syracuseStep 36660089 = 27495067) B27495067
theorem B24440059 : Blo 2259435 24440059 := bstep (se 1 (by rfl) ⟨18330044, by rfl⟩ : syracuseStep 24440059 = 36660089) B36660089
theorem B32586745 : Blo 2259435 32586745 := bstep (se 2 (by rfl) ⟨12220029, by rfl⟩ : syracuseStep 32586745 = 24440059) B24440059
theorem B43448993 : Blo 2259435 43448993 := bstep (se 2 (by rfl) ⟨16293372, by rfl⟩ : syracuseStep 43448993 = 32586745) B32586745
theorem B28965995 : Blo 2259435 28965995 := bstep (se 1 (by rfl) ⟨21724496, by rfl⟩ : syracuseStep 28965995 = 43448993) B43448993
theorem B19310663 : Blo 2259435 19310663 := bstep (se 1 (by rfl) ⟨14482997, by rfl⟩ : syracuseStep 19310663 = 28965995) B28965995
theorem B12873775 : Blo 2259435 12873775 := bstep (se 1 (by rfl) ⟨9655331, by rfl⟩ : syracuseStep 12873775 = 19310663) B19310663
theorem B17165033 : Blo 2259435 17165033 := bstep (se 2 (by rfl) ⟨6436887, by rfl⟩ : syracuseStep 17165033 = 12873775) B12873775
theorem B11443355 : Blo 2259435 11443355 := bstep (se 1 (by rfl) ⟨8582516, by rfl⟩ : syracuseStep 11443355 = 17165033) B17165033
theorem B7628903 : Blo 2259435 7628903 := bstep (se 1 (by rfl) ⟨5721677, by rfl⟩ : syracuseStep 7628903 = 11443355) B11443355
theorem B5085935 : Blo 2259435 5085935 := bstep (se 1 (by rfl) ⟨3814451, by rfl⟩ : syracuseStep 5085935 = 7628903) B7628903
theorem B3390623 : Blo 2259435 3390623 := bstep (se 1 (by rfl) ⟨2542967, by rfl⟩ : syracuseStep 3390623 = 5085935) B5085935
theorem B2260415 : Blo 2259435 2260415 := bstep (se 1 (by rfl) ⟨1695311, by rfl⟩ : syracuseStep 2260415 = 3390623) B3390623
theorem B3390629 : Blo 2259435 3390629 := bbase (se 4 (by rfl) ⟨317871, by rfl⟩ : syracuseStep 3390629 = 635743) (by norm_num)
theorem B2260419 : Blo 2259435 2260419 := bstep (se 1 (by rfl) ⟨1695314, by rfl⟩ : syracuseStep 2260419 = 3390629) B3390629
theorem B2860849 : Blo 2259435 2860849 := bbase (se 2 (by rfl) ⟨1072818, by rfl⟩ : syracuseStep 2860849 = 2145637) (by norm_num)
theorem B3814465 : Blo 2259435 3814465 := bstep (se 2 (by rfl) ⟨1430424, by rfl⟩ : syracuseStep 3814465 = 2860849) B2860849
theorem B5085953 : Blo 2259435 5085953 := bstep (se 2 (by rfl) ⟨1907232, by rfl⟩ : syracuseStep 5085953 = 3814465) B3814465
theorem B3390635 : Blo 2259435 3390635 := bstep (se 1 (by rfl) ⟨2542976, by rfl⟩ : syracuseStep 3390635 = 5085953) B5085953
theorem B2260423 : Blo 2259435 2260423 := bstep (se 1 (by rfl) ⟨1695317, by rfl⟩ : syracuseStep 2260423 = 3390635) B3390635
theorem B2542981 : Blo 2259435 2542981 := bbase (se 4 (by rfl) ⟨238404, by rfl⟩ : syracuseStep 2542981 = 476809) (by norm_num)
theorem B3390641 : Blo 2259435 3390641 := bstep (se 2 (by rfl) ⟨1271490, by rfl⟩ : syracuseStep 3390641 = 2542981) B2542981
theorem B2260427 : Blo 2259435 2260427 := bstep (se 1 (by rfl) ⟨1695320, by rfl⟩ : syracuseStep 2260427 = 3390641) B3390641
theorem B4827701 : Blo 2259435 4827701 := bbase (se 5 (by rfl) ⟨226298, by rfl⟩ : syracuseStep 4827701 = 452597) (by norm_num)
theorem B3218467 : Blo 2259435 3218467 := bstep (se 1 (by rfl) ⟨2413850, by rfl⟩ : syracuseStep 3218467 = 4827701) B4827701
theorem B4291289 : Blo 2259435 4291289 := bstep (se 2 (by rfl) ⟨1609233, by rfl⟩ : syracuseStep 4291289 = 3218467) B3218467
theorem B2860859 : Blo 2259435 2860859 := bstep (se 1 (by rfl) ⟨2145644, by rfl⟩ : syracuseStep 2860859 = 4291289) B4291289
theorem B7628957 : Blo 2259435 7628957 := bstep (se 3 (by rfl) ⟨1430429, by rfl⟩ : syracuseStep 7628957 = 2860859) B2860859
theorem B5085971 : Blo 2259435 5085971 := bstep (se 1 (by rfl) ⟨3814478, by rfl⟩ : syracuseStep 5085971 = 7628957) B7628957
theorem B3390647 : Blo 2259435 3390647 := bstep (se 1 (by rfl) ⟨2542985, by rfl⟩ : syracuseStep 3390647 = 5085971) B5085971
theorem B2260431 : Blo 2259435 2260431 := bstep (se 1 (by rfl) ⟨1695323, by rfl⟩ : syracuseStep 2260431 = 3390647) B3390647
theorem B3390653 : Blo 2259435 3390653 := bbase (se 3 (by rfl) ⟨635747, by rfl⟩ : syracuseStep 3390653 = 1271495) (by norm_num)
theorem B2260435 : Blo 2259435 2260435 := bstep (se 1 (by rfl) ⟨1695326, by rfl⟩ : syracuseStep 2260435 = 3390653) B3390653
theorem B5085989 : Blo 2259435 5085989 := bbase (se 4 (by rfl) ⟨476811, by rfl⟩ : syracuseStep 5085989 = 953623) (by norm_num)
theorem B3390659 : Blo 2259435 3390659 := bstep (se 1 (by rfl) ⟨2542994, by rfl⟩ : syracuseStep 3390659 = 5085989) B5085989
theorem B2260439 : Blo 2259435 2260439 := bstep (se 1 (by rfl) ⟨1695329, by rfl⟩ : syracuseStep 2260439 = 3390659) B3390659
theorem B5721749 : Blo 2259435 5721749 := bbase (se 6 (by rfl) ⟨134103, by rfl⟩ : syracuseStep 5721749 = 268207) (by norm_num)
theorem B3814499 : Blo 2259435 3814499 := bstep (se 1 (by rfl) ⟨2860874, by rfl⟩ : syracuseStep 3814499 = 5721749) B5721749
theorem B2542999 : Blo 2259435 2542999 := bstep (se 1 (by rfl) ⟨1907249, by rfl⟩ : syracuseStep 2542999 = 3814499) B3814499
theorem B3390665 : Blo 2259435 3390665 := bstep (se 2 (by rfl) ⟨1271499, by rfl⟩ : syracuseStep 3390665 = 2542999) B2542999
theorem B2260443 : Blo 2259435 2260443 := bstep (se 1 (by rfl) ⟨1695332, by rfl⟩ : syracuseStep 2260443 = 3390665) B3390665
theorem B2715601 : Blo 2259435 2715601 := bbase (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) (by norm_num)
theorem B3620801 : Blo 2259435 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B9655469 : Blo 2259435 9655469 := bstep (se 3 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 9655469 = 3620801) B3620801
theorem B6436979 : Blo 2259435 6436979 := bstep (se 1 (by rfl) ⟨4827734, by rfl⟩ : syracuseStep 6436979 = 9655469) B9655469
theorem B4291319 : Blo 2259435 4291319 := bstep (se 1 (by rfl) ⟨3218489, by rfl⟩ : syracuseStep 4291319 = 6436979) B6436979
theorem B11443517 : Blo 2259435 11443517 := bstep (se 3 (by rfl) ⟨2145659, by rfl⟩ : syracuseStep 11443517 = 4291319) B4291319
theorem B7629011 : Blo 2259435 7629011 := bstep (se 1 (by rfl) ⟨5721758, by rfl⟩ : syracuseStep 7629011 = 11443517) B11443517
theorem B5086007 : Blo 2259435 5086007 := bstep (se 1 (by rfl) ⟨3814505, by rfl⟩ : syracuseStep 5086007 = 7629011) B7629011
theorem B3390671 : Blo 2259435 3390671 := bstep (se 1 (by rfl) ⟨2543003, by rfl⟩ : syracuseStep 3390671 = 5086007) B5086007
theorem B2260447 : Blo 2259435 2260447 := bstep (se 1 (by rfl) ⟨1695335, by rfl⟩ : syracuseStep 2260447 = 3390671) B3390671
theorem B3390677 : Blo 2259435 3390677 := bbase (se 7 (by rfl) ⟨39734, by rfl⟩ : syracuseStep 3390677 = 79469) (by norm_num)
theorem B2260451 : Blo 2259435 2260451 := bstep (se 1 (by rfl) ⟨1695338, by rfl⟩ : syracuseStep 2260451 = 3390677) B3390677
theorem B3218501 : Blo 2259435 3218501 := bbase (se 4 (by rfl) ⟨301734, by rfl⟩ : syracuseStep 3218501 = 603469) (by norm_num)
theorem B8582669 : Blo 2259435 8582669 := bstep (se 3 (by rfl) ⟨1609250, by rfl⟩ : syracuseStep 8582669 = 3218501) B3218501
theorem B5721779 : Blo 2259435 5721779 := bstep (se 1 (by rfl) ⟨4291334, by rfl⟩ : syracuseStep 5721779 = 8582669) B8582669
theorem B3814519 : Blo 2259435 3814519 := bstep (se 1 (by rfl) ⟨2860889, by rfl⟩ : syracuseStep 3814519 = 5721779) B5721779
theorem B5086025 : Blo 2259435 5086025 := bstep (se 2 (by rfl) ⟨1907259, by rfl⟩ : syracuseStep 5086025 = 3814519) B3814519
theorem B3390683 : Blo 2259435 3390683 := bstep (se 1 (by rfl) ⟨2543012, by rfl⟩ : syracuseStep 3390683 = 5086025) B5086025
theorem B2260455 : Blo 2259435 2260455 := bstep (se 1 (by rfl) ⟨1695341, by rfl⟩ : syracuseStep 2260455 = 3390683) B3390683
theorem B2543017 : Blo 2259435 2543017 := bbase (se 2 (by rfl) ⟨953631, by rfl⟩ : syracuseStep 2543017 = 1907263) (by norm_num)
theorem B3390689 : Blo 2259435 3390689 := bstep (se 2 (by rfl) ⟨1271508, by rfl⟩ : syracuseStep 3390689 = 2543017) B2543017
theorem B2260459 : Blo 2259435 2260459 := bstep (se 1 (by rfl) ⟨1695344, by rfl⟩ : syracuseStep 2260459 = 3390689) B3390689
theorem B7241653 : Blo 2259435 7241653 := bbase (se 5 (by rfl) ⟨339452, by rfl⟩ : syracuseStep 7241653 = 678905) (by norm_num)
theorem B9655537 : Blo 2259435 9655537 := bstep (se 2 (by rfl) ⟨3620826, by rfl⟩ : syracuseStep 9655537 = 7241653) B7241653
theorem B12874049 : Blo 2259435 12874049 := bstep (se 2 (by rfl) ⟨4827768, by rfl⟩ : syracuseStep 12874049 = 9655537) B9655537
theorem B8582699 : Blo 2259435 8582699 := bstep (se 1 (by rfl) ⟨6437024, by rfl⟩ : syracuseStep 8582699 = 12874049) B12874049
theorem B5721799 : Blo 2259435 5721799 := bstep (se 1 (by rfl) ⟨4291349, by rfl⟩ : syracuseStep 5721799 = 8582699) B8582699
theorem B7629065 : Blo 2259435 7629065 := bstep (se 2 (by rfl) ⟨2860899, by rfl⟩ : syracuseStep 7629065 = 5721799) B5721799
theorem B5086043 : Blo 2259435 5086043 := bstep (se 1 (by rfl) ⟨3814532, by rfl⟩ : syracuseStep 5086043 = 7629065) B7629065
theorem B3390695 : Blo 2259435 3390695 := bstep (se 1 (by rfl) ⟨2543021, by rfl⟩ : syracuseStep 3390695 = 5086043) B5086043
theorem B2260463 : Blo 2259435 2260463 := bstep (se 1 (by rfl) ⟨1695347, by rfl⟩ : syracuseStep 2260463 = 3390695) B3390695
theorem B3390701 : Blo 2259435 3390701 := bbase (se 3 (by rfl) ⟨635756, by rfl⟩ : syracuseStep 3390701 = 1271513) (by norm_num)
theorem B2260467 : Blo 2259435 2260467 := bstep (se 1 (by rfl) ⟨1695350, by rfl⟩ : syracuseStep 2260467 = 3390701) B3390701
theorem B5086061 : Blo 2259435 5086061 := bbase (se 3 (by rfl) ⟨953636, by rfl⟩ : syracuseStep 5086061 = 1907273) (by norm_num)
theorem B3390707 : Blo 2259435 3390707 := bstep (se 1 (by rfl) ⟨2543030, by rfl⟩ : syracuseStep 3390707 = 5086061) B5086061
theorem B2260471 : Blo 2259435 2260471 := bstep (se 1 (by rfl) ⟨1695353, by rfl⟩ : syracuseStep 2260471 = 3390707) B3390707
theorem B4291373 : Blo 2259435 4291373 := bbase (se 3 (by rfl) ⟨804632, by rfl⟩ : syracuseStep 4291373 = 1609265) (by norm_num)
theorem B2860915 : Blo 2259435 2860915 := bstep (se 1 (by rfl) ⟨2145686, by rfl⟩ : syracuseStep 2860915 = 4291373) B4291373
theorem B3814553 : Blo 2259435 3814553 := bstep (se 2 (by rfl) ⟨1430457, by rfl⟩ : syracuseStep 3814553 = 2860915) B2860915
theorem B2543035 : Blo 2259435 2543035 := bstep (se 1 (by rfl) ⟨1907276, by rfl⟩ : syracuseStep 2543035 = 3814553) B3814553
theorem B3390713 : Blo 2259435 3390713 := bstep (se 2 (by rfl) ⟨1271517, by rfl⟩ : syracuseStep 3390713 = 2543035) B2543035
theorem B2260475 : Blo 2259435 2260475 := bstep (se 1 (by rfl) ⟨1695356, by rfl⟩ : syracuseStep 2260475 = 3390713) B3390713
theorem B18580661 : Blo 2259435 18580661 := bbase (se 5 (by rfl) ⟨870968, by rfl⟩ : syracuseStep 18580661 = 1741937) (by norm_num)
theorem B12387107 : Blo 2259435 12387107 := bstep (se 1 (by rfl) ⟨9290330, by rfl⟩ : syracuseStep 12387107 = 18580661) B18580661
theorem B8258071 : Blo 2259435 8258071 := bstep (se 1 (by rfl) ⟨6193553, by rfl⟩ : syracuseStep 8258071 = 12387107) B12387107
theorem B11010761 : Blo 2259435 11010761 := bstep (se 2 (by rfl) ⟨4129035, by rfl⟩ : syracuseStep 11010761 = 8258071) B8258071
theorem B7340507 : Blo 2259435 7340507 := bstep (se 1 (by rfl) ⟨5505380, by rfl⟩ : syracuseStep 7340507 = 11010761) B11010761
theorem B4893671 : Blo 2259435 4893671 := bstep (se 1 (by rfl) ⟨3670253, by rfl⟩ : syracuseStep 4893671 = 7340507) B7340507
theorem B3262447 : Blo 2259435 3262447 := bstep (se 1 (by rfl) ⟨2446835, by rfl⟩ : syracuseStep 3262447 = 4893671) B4893671
theorem B17399717 : Blo 2259435 17399717 := bstep (se 4 (by rfl) ⟨1631223, by rfl⟩ : syracuseStep 17399717 = 3262447) B3262447
theorem B11599811 : Blo 2259435 11599811 := bstep (se 1 (by rfl) ⟨8699858, by rfl⟩ : syracuseStep 11599811 = 17399717) B17399717
theorem B7733207 : Blo 2259435 7733207 := bstep (se 1 (by rfl) ⟨5799905, by rfl⟩ : syracuseStep 7733207 = 11599811) B11599811
theorem B5155471 : Blo 2259435 5155471 := bstep (se 1 (by rfl) ⟨3866603, by rfl⟩ : syracuseStep 5155471 = 7733207) B7733207
theorem B27495845 : Blo 2259435 27495845 := bstep (se 4 (by rfl) ⟨2577735, by rfl⟩ : syracuseStep 27495845 = 5155471) B5155471
theorem B18330563 : Blo 2259435 18330563 := bstep (se 1 (by rfl) ⟨13747922, by rfl⟩ : syracuseStep 18330563 = 27495845) B27495845
theorem B48881501 : Blo 2259435 48881501 := bstep (se 3 (by rfl) ⟨9165281, by rfl⟩ : syracuseStep 48881501 = 18330563) B18330563
theorem B32587667 : Blo 2259435 32587667 := bstep (se 1 (by rfl) ⟨24440750, by rfl⟩ : syracuseStep 32587667 = 48881501) B48881501
theorem B21725111 : Blo 2259435 21725111 := bstep (se 1 (by rfl) ⟨16293833, by rfl⟩ : syracuseStep 21725111 = 32587667) B32587667
theorem B57933629 : Blo 2259435 57933629 := bstep (se 3 (by rfl) ⟨10862555, by rfl⟩ : syracuseStep 57933629 = 21725111) B21725111
theorem B38622419 : Blo 2259435 38622419 := bstep (se 1 (by rfl) ⟨28966814, by rfl⟩ : syracuseStep 38622419 = 57933629) B57933629
theorem B25748279 : Blo 2259435 25748279 := bstep (se 1 (by rfl) ⟨19311209, by rfl⟩ : syracuseStep 25748279 = 38622419) B38622419
theorem B17165519 : Blo 2259435 17165519 := bstep (se 1 (by rfl) ⟨12874139, by rfl⟩ : syracuseStep 17165519 = 25748279) B25748279
theorem B11443679 : Blo 2259435 11443679 := bstep (se 1 (by rfl) ⟨8582759, by rfl⟩ : syracuseStep 11443679 = 17165519) B17165519
theorem B7629119 : Blo 2259435 7629119 := bstep (se 1 (by rfl) ⟨5721839, by rfl⟩ : syracuseStep 7629119 = 11443679) B11443679
theorem B5086079 : Blo 2259435 5086079 := bstep (se 1 (by rfl) ⟨3814559, by rfl⟩ : syracuseStep 5086079 = 7629119) B7629119
theorem B3390719 : Blo 2259435 3390719 := bstep (se 1 (by rfl) ⟨2543039, by rfl⟩ : syracuseStep 3390719 = 5086079) B5086079
theorem B2260479 : Blo 2259435 2260479 := bstep (se 1 (by rfl) ⟨1695359, by rfl⟩ : syracuseStep 2260479 = 3390719) B3390719
theorem B3390725 : Blo 2259435 3390725 := bbase (se 4 (by rfl) ⟨317880, by rfl⟩ : syracuseStep 3390725 = 635761) (by norm_num)
theorem B2260483 : Blo 2259435 2260483 := bstep (se 1 (by rfl) ⟨1695362, by rfl⟩ : syracuseStep 2260483 = 3390725) B3390725
theorem B3814573 : Blo 2259435 3814573 := bbase (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) (by norm_num)
theorem B5086097 : Blo 2259435 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B3390731 : Blo 2259435 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B2260487 : Blo 2259435 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B2543053 : Blo 2259435 2543053 := bbase (se 3 (by rfl) ⟨476822, by rfl⟩ : syracuseStep 2543053 = 953645) (by norm_num)
theorem B3390737 : Blo 2259435 3390737 := bstep (se 2 (by rfl) ⟨1271526, by rfl⟩ : syracuseStep 3390737 = 2543053) B2543053
theorem B2260491 : Blo 2259435 2260491 := bstep (se 1 (by rfl) ⟨1695368, by rfl⟩ : syracuseStep 2260491 = 3390737) B3390737
theorem B7629173 : Blo 2259435 7629173 := bbase (se 5 (by rfl) ⟨357617, by rfl⟩ : syracuseStep 7629173 = 715235) (by norm_num)
theorem B5086115 : Blo 2259435 5086115 := bstep (se 1 (by rfl) ⟨3814586, by rfl⟩ : syracuseStep 5086115 = 7629173) B7629173
theorem B3390743 : Blo 2259435 3390743 := bstep (se 1 (by rfl) ⟨2543057, by rfl⟩ : syracuseStep 3390743 = 5086115) B5086115
theorem B2260495 : Blo 2259435 2260495 := bstep (se 1 (by rfl) ⟨1695371, by rfl⟩ : syracuseStep 2260495 = 3390743) B3390743
theorem B3390749 : Blo 2259435 3390749 := bbase (se 3 (by rfl) ⟨635765, by rfl⟩ : syracuseStep 3390749 = 1271531) (by norm_num)
theorem B2260499 : Blo 2259435 2260499 := bstep (se 1 (by rfl) ⟨1695374, by rfl⟩ : syracuseStep 2260499 = 3390749) B3390749
theorem B5086133 : Blo 2259435 5086133 := bbase (se 5 (by rfl) ⟨238412, by rfl⟩ : syracuseStep 5086133 = 476825) (by norm_num)
theorem B3390755 : Blo 2259435 3390755 := bstep (se 1 (by rfl) ⟨2543066, by rfl⟩ : syracuseStep 3390755 = 5086133) B5086133
theorem B2260503 : Blo 2259435 2260503 := bstep (se 1 (by rfl) ⟨1695377, by rfl⟩ : syracuseStep 2260503 = 3390755) B3390755
theorem B10862693 : Blo 2259435 10862693 := bbase (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) (by norm_num)
theorem B7241795 : Blo 2259435 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B4827863 : Blo 2259435 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B12874301 : Blo 2259435 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B8582867 : Blo 2259435 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B5721911 : Blo 2259435 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B3814607 : Blo 2259435 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B2543071 : Blo 2259435 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B3390761 : Blo 2259435 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B2260507 : Blo 2259435 2260507 := bstep (se 1 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 2260507 = 3390761) B3390761
theorem B9165413 : Blo 2259435 9165413 := bbase (se 4 (by rfl) ⟨859257, by rfl⟩ : syracuseStep 9165413 = 1718515) (by norm_num)
theorem B24441101 : Blo 2259435 24441101 := bstep (se 3 (by rfl) ⟨4582706, by rfl⟩ : syracuseStep 24441101 = 9165413) B9165413
theorem B16294067 : Blo 2259435 16294067 := bstep (se 1 (by rfl) ⟨12220550, by rfl⟩ : syracuseStep 16294067 = 24441101) B24441101
theorem B10862711 : Blo 2259435 10862711 := bstep (se 1 (by rfl) ⟨8147033, by rfl⟩ : syracuseStep 10862711 = 16294067) B16294067
theorem B7241807 : Blo 2259435 7241807 := bstep (se 1 (by rfl) ⟨5431355, by rfl⟩ : syracuseStep 7241807 = 10862711) B10862711
theorem B4827871 : Blo 2259435 4827871 := bstep (se 1 (by rfl) ⟨3620903, by rfl⟩ : syracuseStep 4827871 = 7241807) B7241807
theorem B6437161 : Blo 2259435 6437161 := bstep (se 2 (by rfl) ⟨2413935, by rfl⟩ : syracuseStep 6437161 = 4827871) B4827871
theorem B8582881 : Blo 2259435 8582881 := bstep (se 2 (by rfl) ⟨3218580, by rfl⟩ : syracuseStep 8582881 = 6437161) B6437161
theorem B11443841 : Blo 2259435 11443841 := bstep (se 2 (by rfl) ⟨4291440, by rfl⟩ : syracuseStep 11443841 = 8582881) B8582881
theorem B7629227 : Blo 2259435 7629227 := bstep (se 1 (by rfl) ⟨5721920, by rfl⟩ : syracuseStep 7629227 = 11443841) B11443841
theorem B5086151 : Blo 2259435 5086151 := bstep (se 1 (by rfl) ⟨3814613, by rfl⟩ : syracuseStep 5086151 = 7629227) B7629227
theorem B3390767 : Blo 2259435 3390767 := bstep (se 1 (by rfl) ⟨2543075, by rfl⟩ : syracuseStep 3390767 = 5086151) B5086151
theorem B2260511 : Blo 2259435 2260511 := bstep (se 1 (by rfl) ⟨1695383, by rfl⟩ : syracuseStep 2260511 = 3390767) B3390767
theorem B3390773 : Blo 2259435 3390773 := bbase (se 5 (by rfl) ⟨158942, by rfl⟩ : syracuseStep 3390773 = 317885) (by norm_num)
theorem B2260515 : Blo 2259435 2260515 := bstep (se 1 (by rfl) ⟨1695386, by rfl⟩ : syracuseStep 2260515 = 3390773) B3390773
theorem B5721941 : Blo 2259435 5721941 := bbase (se 9 (by rfl) ⟨16763, by rfl⟩ : syracuseStep 5721941 = 33527) (by norm_num)
theorem B3814627 : Blo 2259435 3814627 := bstep (se 1 (by rfl) ⟨2860970, by rfl⟩ : syracuseStep 3814627 = 5721941) B5721941
theorem B5086169 : Blo 2259435 5086169 := bstep (se 2 (by rfl) ⟨1907313, by rfl⟩ : syracuseStep 5086169 = 3814627) B3814627
theorem B3390779 : Blo 2259435 3390779 := bstep (se 1 (by rfl) ⟨2543084, by rfl⟩ : syracuseStep 3390779 = 5086169) B5086169
theorem B2260519 : Blo 2259435 2260519 := bstep (se 1 (by rfl) ⟨1695389, by rfl⟩ : syracuseStep 2260519 = 3390779) B3390779
theorem B2543089 : Blo 2259435 2543089 := bbase (se 2 (by rfl) ⟨953658, by rfl⟩ : syracuseStep 2543089 = 1907317) (by norm_num)
theorem B3390785 : Blo 2259435 3390785 := bstep (se 2 (by rfl) ⟨1271544, by rfl⟩ : syracuseStep 3390785 = 2543089) B2543089
theorem B2260523 : Blo 2259435 2260523 := bstep (se 1 (by rfl) ⟨1695392, by rfl⟩ : syracuseStep 2260523 = 3390785) B3390785
theorem B2715697 : Blo 2259435 2715697 := bbase (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) (by norm_num)
theorem B14483717 : Blo 2259435 14483717 := bstep (se 4 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 14483717 = 2715697) B2715697
theorem B9655811 : Blo 2259435 9655811 := bstep (se 1 (by rfl) ⟨7241858, by rfl⟩ : syracuseStep 9655811 = 14483717) B14483717
theorem B6437207 : Blo 2259435 6437207 := bstep (se 1 (by rfl) ⟨4827905, by rfl⟩ : syracuseStep 6437207 = 9655811) B9655811
theorem B4291471 : Blo 2259435 4291471 := bstep (se 1 (by rfl) ⟨3218603, by rfl⟩ : syracuseStep 4291471 = 6437207) B6437207
theorem B5721961 : Blo 2259435 5721961 := bstep (se 2 (by rfl) ⟨2145735, by rfl⟩ : syracuseStep 5721961 = 4291471) B4291471
theorem B7629281 : Blo 2259435 7629281 := bstep (se 2 (by rfl) ⟨2860980, by rfl⟩ : syracuseStep 7629281 = 5721961) B5721961
theorem B5086187 : Blo 2259435 5086187 := bstep (se 1 (by rfl) ⟨3814640, by rfl⟩ : syracuseStep 5086187 = 7629281) B7629281
theorem B3390791 : Blo 2259435 3390791 := bstep (se 1 (by rfl) ⟨2543093, by rfl⟩ : syracuseStep 3390791 = 5086187) B5086187
theorem B2260527 : Blo 2259435 2260527 := bstep (se 1 (by rfl) ⟨1695395, by rfl⟩ : syracuseStep 2260527 = 3390791) B3390791
theorem B3390797 : Blo 2259435 3390797 := bbase (se 3 (by rfl) ⟨635774, by rfl⟩ : syracuseStep 3390797 = 1271549) (by norm_num)
theorem B2260531 : Blo 2259435 2260531 := bstep (se 1 (by rfl) ⟨1695398, by rfl⟩ : syracuseStep 2260531 = 3390797) B3390797
theorem B5086205 : Blo 2259435 5086205 := bbase (se 3 (by rfl) ⟨953663, by rfl⟩ : syracuseStep 5086205 = 1907327) (by norm_num)
theorem B3390803 : Blo 2259435 3390803 := bstep (se 1 (by rfl) ⟨2543102, by rfl⟩ : syracuseStep 3390803 = 5086205) B5086205
theorem B2260535 : Blo 2259435 2260535 := bstep (se 1 (by rfl) ⟨1695401, by rfl⟩ : syracuseStep 2260535 = 3390803) B3390803
theorem B3814661 : Blo 2259435 3814661 := bbase (se 4 (by rfl) ⟨357624, by rfl⟩ : syracuseStep 3814661 = 715249) (by norm_num)
theorem B2543107 : Blo 2259435 2543107 := bstep (se 1 (by rfl) ⟨1907330, by rfl⟩ : syracuseStep 2543107 = 3814661) B3814661
theorem B3390809 : Blo 2259435 3390809 := bstep (se 2 (by rfl) ⟨1271553, by rfl⟩ : syracuseStep 3390809 = 2543107) B2543107
theorem B2260539 : Blo 2259435 2260539 := bstep (se 1 (by rfl) ⟨1695404, by rfl⟩ : syracuseStep 2260539 = 3390809) B3390809
theorem B17166005 : Blo 2259435 17166005 := bbase (se 5 (by rfl) ⟨804656, by rfl⟩ : syracuseStep 17166005 = 1609313) (by norm_num)
theorem B11444003 : Blo 2259435 11444003 := bstep (se 1 (by rfl) ⟨8583002, by rfl⟩ : syracuseStep 11444003 = 17166005) B17166005
theorem B7629335 : Blo 2259435 7629335 := bstep (se 1 (by rfl) ⟨5722001, by rfl⟩ : syracuseStep 7629335 = 11444003) B11444003
theorem B5086223 : Blo 2259435 5086223 := bstep (se 1 (by rfl) ⟨3814667, by rfl⟩ : syracuseStep 5086223 = 7629335) B7629335
theorem B3390815 : Blo 2259435 3390815 := bstep (se 1 (by rfl) ⟨2543111, by rfl⟩ : syracuseStep 3390815 = 5086223) B5086223
theorem B2260543 : Blo 2259435 2260543 := bstep (se 1 (by rfl) ⟨1695407, by rfl⟩ : syracuseStep 2260543 = 3390815) B3390815
theorem B3390821 : Blo 2259435 3390821 := bbase (se 4 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 3390821 = 635779) (by norm_num)
theorem B2260547 : Blo 2259435 2260547 := bstep (se 1 (by rfl) ⟨1695410, by rfl⟩ : syracuseStep 2260547 = 3390821) B3390821
theorem B4291517 : Blo 2259435 4291517 := bbase (se 3 (by rfl) ⟨804659, by rfl⟩ : syracuseStep 4291517 = 1609319) (by norm_num)
theorem B2861011 : Blo 2259435 2861011 := bstep (se 1 (by rfl) ⟨2145758, by rfl⟩ : syracuseStep 2861011 = 4291517) B4291517
theorem B3814681 : Blo 2259435 3814681 := bstep (se 2 (by rfl) ⟨1430505, by rfl⟩ : syracuseStep 3814681 = 2861011) B2861011
theorem B5086241 : Blo 2259435 5086241 := bstep (se 2 (by rfl) ⟨1907340, by rfl⟩ : syracuseStep 5086241 = 3814681) B3814681
theorem B3390827 : Blo 2259435 3390827 := bstep (se 1 (by rfl) ⟨2543120, by rfl⟩ : syracuseStep 3390827 = 5086241) B5086241
theorem B2260551 : Blo 2259435 2260551 := bstep (se 1 (by rfl) ⟨1695413, by rfl⟩ : syracuseStep 2260551 = 3390827) B3390827
theorem B2543125 : Blo 2259435 2543125 := bbase (se 6 (by rfl) ⟨59604, by rfl⟩ : syracuseStep 2543125 = 119209) (by norm_num)
theorem B3390833 : Blo 2259435 3390833 := bstep (se 2 (by rfl) ⟨1271562, by rfl⟩ : syracuseStep 3390833 = 2543125) B2543125
theorem B2260555 : Blo 2259435 2260555 := bstep (se 1 (by rfl) ⟨1695416, by rfl⟩ : syracuseStep 2260555 = 3390833) B3390833
theorem B2861021 : Blo 2259435 2861021 := bbase (se 3 (by rfl) ⟨536441, by rfl⟩ : syracuseStep 2861021 = 1072883) (by norm_num)
theorem B7629389 : Blo 2259435 7629389 := bstep (se 3 (by rfl) ⟨1430510, by rfl⟩ : syracuseStep 7629389 = 2861021) B2861021
theorem B5086259 : Blo 2259435 5086259 := bstep (se 1 (by rfl) ⟨3814694, by rfl⟩ : syracuseStep 5086259 = 7629389) B7629389
theorem B3390839 : Blo 2259435 3390839 := bstep (se 1 (by rfl) ⟨2543129, by rfl⟩ : syracuseStep 3390839 = 5086259) B5086259
theorem B2260559 : Blo 2259435 2260559 := bstep (se 1 (by rfl) ⟨1695419, by rfl⟩ : syracuseStep 2260559 = 3390839) B3390839
theorem B3390845 : Blo 2259435 3390845 := bbase (se 3 (by rfl) ⟨635783, by rfl⟩ : syracuseStep 3390845 = 1271567) (by norm_num)
theorem B2260563 : Blo 2259435 2260563 := bstep (se 1 (by rfl) ⟨1695422, by rfl⟩ : syracuseStep 2260563 = 3390845) B3390845
theorem B5086277 : Blo 2259435 5086277 := bbase (se 4 (by rfl) ⟨476838, by rfl⟩ : syracuseStep 5086277 = 953677) (by norm_num)
theorem B3390851 : Blo 2259435 3390851 := bstep (se 1 (by rfl) ⟨2543138, by rfl⟩ : syracuseStep 3390851 = 5086277) B5086277
theorem B2260567 : Blo 2259435 2260567 := bstep (se 1 (by rfl) ⟨1695425, by rfl⟩ : syracuseStep 2260567 = 3390851) B3390851
theorem B6437333 : Blo 2259435 6437333 := bbase (se 7 (by rfl) ⟨75437, by rfl⟩ : syracuseStep 6437333 = 150875) (by norm_num)
theorem B4291555 : Blo 2259435 4291555 := bstep (se 1 (by rfl) ⟨3218666, by rfl⟩ : syracuseStep 4291555 = 6437333) B6437333
theorem B5722073 : Blo 2259435 5722073 := bstep (se 2 (by rfl) ⟨2145777, by rfl⟩ : syracuseStep 5722073 = 4291555) B4291555
theorem B3814715 : Blo 2259435 3814715 := bstep (se 1 (by rfl) ⟨2861036, by rfl⟩ : syracuseStep 3814715 = 5722073) B5722073
theorem B2543143 : Blo 2259435 2543143 := bstep (se 1 (by rfl) ⟨1907357, by rfl⟩ : syracuseStep 2543143 = 3814715) B3814715
theorem B3390857 : Blo 2259435 3390857 := bstep (se 2 (by rfl) ⟨1271571, by rfl⟩ : syracuseStep 3390857 = 2543143) B2543143
theorem B2260571 : Blo 2259435 2260571 := bstep (se 1 (by rfl) ⟨1695428, by rfl⟩ : syracuseStep 2260571 = 3390857) B3390857
theorem B11444165 : Blo 2259435 11444165 := bbase (se 4 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 11444165 = 2145781) (by norm_num)
theorem B7629443 : Blo 2259435 7629443 := bstep (se 1 (by rfl) ⟨5722082, by rfl⟩ : syracuseStep 7629443 = 11444165) B11444165
theorem B5086295 : Blo 2259435 5086295 := bstep (se 1 (by rfl) ⟨3814721, by rfl⟩ : syracuseStep 5086295 = 7629443) B7629443
theorem B3390863 : Blo 2259435 3390863 := bstep (se 1 (by rfl) ⟨2543147, by rfl⟩ : syracuseStep 3390863 = 5086295) B5086295
theorem B2260575 : Blo 2259435 2260575 := bstep (se 1 (by rfl) ⟨1695431, by rfl⟩ : syracuseStep 2260575 = 3390863) B3390863
theorem B3390869 : Blo 2259435 3390869 := bbase (se 6 (by rfl) ⟨79473, by rfl⟩ : syracuseStep 3390869 = 158947) (by norm_num)
theorem B2260579 : Blo 2259435 2260579 := bstep (se 1 (by rfl) ⟨1695434, by rfl⟩ : syracuseStep 2260579 = 3390869) B3390869
theorem B5226053 : Blo 2259435 5226053 := bbase (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) (by norm_num)
theorem B13936141 : Blo 2259435 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B74326085 : Blo 2259435 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B49550723 : Blo 2259435 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B33033815 : Blo 2259435 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B22022543 : Blo 2259435 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B14681695 : Blo 2259435 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B19575593 : Blo 2259435 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B13050395 : Blo 2259435 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B8700263 : Blo 2259435 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B5800175 : Blo 2259435 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B3866783 : Blo 2259435 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B10311421 : Blo 2259435 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B13748561 : Blo 2259435 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B9165707 : Blo 2259435 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B6110471 : Blo 2259435 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B4073647 : Blo 2259435 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B5431529 : Blo 2259435 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B3621019 : Blo 2259435 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B4828025 : Blo 2259435 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B12874733 : Blo 2259435 12874733 := bstep (se 3 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 12874733 = 4828025) B4828025
theorem B8583155 : Blo 2259435 8583155 := bstep (se 1 (by rfl) ⟨6437366, by rfl⟩ : syracuseStep 8583155 = 12874733) B12874733
theorem B5722103 : Blo 2259435 5722103 := bstep (se 1 (by rfl) ⟨4291577, by rfl⟩ : syracuseStep 5722103 = 8583155) B8583155
theorem B3814735 : Blo 2259435 3814735 := bstep (se 1 (by rfl) ⟨2861051, by rfl⟩ : syracuseStep 3814735 = 5722103) B5722103
theorem B5086313 : Blo 2259435 5086313 := bstep (se 2 (by rfl) ⟨1907367, by rfl⟩ : syracuseStep 5086313 = 3814735) B3814735
theorem B3390875 : Blo 2259435 3390875 := bstep (se 1 (by rfl) ⟨2543156, by rfl⟩ : syracuseStep 3390875 = 5086313) B5086313
theorem B2260583 : Blo 2259435 2260583 := bstep (se 1 (by rfl) ⟨1695437, by rfl⟩ : syracuseStep 2260583 = 3390875) B3390875
theorem B2543161 : Blo 2259435 2543161 := bbase (se 2 (by rfl) ⟨953685, by rfl⟩ : syracuseStep 2543161 = 1907371) (by norm_num)
theorem B3390881 : Blo 2259435 3390881 := bstep (se 2 (by rfl) ⟨1271580, by rfl⟩ : syracuseStep 3390881 = 2543161) B2543161
theorem B2260587 : Blo 2259435 2260587 := bstep (se 1 (by rfl) ⟨1695440, by rfl⟩ : syracuseStep 2260587 = 3390881) B3390881
theorem B2414021 : Blo 2259435 2414021 := bbase (se 4 (by rfl) ⟨226314, by rfl⟩ : syracuseStep 2414021 = 452629) (by norm_num)
theorem B6437389 : Blo 2259435 6437389 := bstep (se 3 (by rfl) ⟨1207010, by rfl⟩ : syracuseStep 6437389 = 2414021) B2414021
theorem B8583185 : Blo 2259435 8583185 := bstep (se 2 (by rfl) ⟨3218694, by rfl⟩ : syracuseStep 8583185 = 6437389) B6437389
theorem B5722123 : Blo 2259435 5722123 := bstep (se 1 (by rfl) ⟨4291592, by rfl⟩ : syracuseStep 5722123 = 8583185) B8583185
theorem B7629497 : Blo 2259435 7629497 := bstep (se 2 (by rfl) ⟨2861061, by rfl⟩ : syracuseStep 7629497 = 5722123) B5722123
theorem B5086331 : Blo 2259435 5086331 := bstep (se 1 (by rfl) ⟨3814748, by rfl⟩ : syracuseStep 5086331 = 7629497) B7629497
theorem B3390887 : Blo 2259435 3390887 := bstep (se 1 (by rfl) ⟨2543165, by rfl⟩ : syracuseStep 3390887 = 5086331) B5086331
theorem B2260591 : Blo 2259435 2260591 := bstep (se 1 (by rfl) ⟨1695443, by rfl⟩ : syracuseStep 2260591 = 3390887) B3390887
theorem B3390893 : Blo 2259435 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B2260595 : Blo 2259435 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B5086349 : Blo 2259435 5086349 := bbase (se 3 (by rfl) ⟨953690, by rfl⟩ : syracuseStep 5086349 = 1907381) (by norm_num)
theorem B3390899 : Blo 2259435 3390899 := bstep (se 1 (by rfl) ⟨2543174, by rfl⟩ : syracuseStep 3390899 = 5086349) B5086349
theorem B2260599 : Blo 2259435 2260599 := bstep (se 1 (by rfl) ⟨1695449, by rfl⟩ : syracuseStep 2260599 = 3390899) B3390899
theorem B2861077 : Blo 2259435 2861077 := bbase (se 6 (by rfl) ⟨67056, by rfl⟩ : syracuseStep 2861077 = 134113) (by norm_num)
theorem B3814769 : Blo 2259435 3814769 := bstep (se 2 (by rfl) ⟨1430538, by rfl⟩ : syracuseStep 3814769 = 2861077) B2861077
theorem B2543179 : Blo 2259435 2543179 := bstep (se 1 (by rfl) ⟨1907384, by rfl⟩ : syracuseStep 2543179 = 3814769) B3814769
theorem B3390905 : Blo 2259435 3390905 := bstep (se 2 (by rfl) ⟨1271589, by rfl⟩ : syracuseStep 3390905 = 2543179) B2543179
theorem B2260603 : Blo 2259435 2260603 := bstep (se 1 (by rfl) ⟨1695452, by rfl⟩ : syracuseStep 2260603 = 3390905) B3390905
theorem B2900117 : Blo 2259435 2900117 := bbase (se 6 (by rfl) ⟨67971, by rfl⟩ : syracuseStep 2900117 = 135943) (by norm_num)
theorem B7733645 : Blo 2259435 7733645 := bstep (se 3 (by rfl) ⟨1450058, by rfl⟩ : syracuseStep 7733645 = 2900117) B2900117
theorem B5155763 : Blo 2259435 5155763 := bstep (se 1 (by rfl) ⟨3866822, by rfl⟩ : syracuseStep 5155763 = 7733645) B7733645
theorem B13748701 : Blo 2259435 13748701 := bstep (se 3 (by rfl) ⟨2577881, by rfl⟩ : syracuseStep 13748701 = 5155763) B5155763
theorem B18331601 : Blo 2259435 18331601 := bstep (se 2 (by rfl) ⟨6874350, by rfl⟩ : syracuseStep 18331601 = 13748701) B13748701
theorem B48884269 : Blo 2259435 48884269 := bstep (se 3 (by rfl) ⟨9165800, by rfl⟩ : syracuseStep 48884269 = 18331601) B18331601
theorem B65179025 : Blo 2259435 65179025 := bstep (se 2 (by rfl) ⟨24442134, by rfl⟩ : syracuseStep 65179025 = 48884269) B48884269
theorem B43452683 : Blo 2259435 43452683 := bstep (se 1 (by rfl) ⟨32589512, by rfl⟩ : syracuseStep 43452683 = 65179025) B65179025
theorem B28968455 : Blo 2259435 28968455 := bstep (se 1 (by rfl) ⟨21726341, by rfl⟩ : syracuseStep 28968455 = 43452683) B43452683
theorem B19312303 : Blo 2259435 19312303 := bstep (se 1 (by rfl) ⟨14484227, by rfl⟩ : syracuseStep 19312303 = 28968455) B28968455
theorem B25749737 : Blo 2259435 25749737 := bstep (se 2 (by rfl) ⟨9656151, by rfl⟩ : syracuseStep 25749737 = 19312303) B19312303
theorem B17166491 : Blo 2259435 17166491 := bstep (se 1 (by rfl) ⟨12874868, by rfl⟩ : syracuseStep 17166491 = 25749737) B25749737
theorem B11444327 : Blo 2259435 11444327 := bstep (se 1 (by rfl) ⟨8583245, by rfl⟩ : syracuseStep 11444327 = 17166491) B17166491
theorem B7629551 : Blo 2259435 7629551 := bstep (se 1 (by rfl) ⟨5722163, by rfl⟩ : syracuseStep 7629551 = 11444327) B11444327
theorem B5086367 : Blo 2259435 5086367 := bstep (se 1 (by rfl) ⟨3814775, by rfl⟩ : syracuseStep 5086367 = 7629551) B7629551
theorem B3390911 : Blo 2259435 3390911 := bstep (se 1 (by rfl) ⟨2543183, by rfl⟩ : syracuseStep 3390911 = 5086367) B5086367
theorem B2260607 : Blo 2259435 2260607 := bstep (se 1 (by rfl) ⟨1695455, by rfl⟩ : syracuseStep 2260607 = 3390911) B3390911
theorem B3390917 : Blo 2259435 3390917 := bbase (se 4 (by rfl) ⟨317898, by rfl⟩ : syracuseStep 3390917 = 635797) (by norm_num)
theorem B2260611 : Blo 2259435 2260611 := bstep (se 1 (by rfl) ⟨1695458, by rfl⟩ : syracuseStep 2260611 = 3390917) B3390917
theorem B3814789 : Blo 2259435 3814789 := bbase (se 4 (by rfl) ⟨357636, by rfl⟩ : syracuseStep 3814789 = 715273) (by norm_num)
theorem B5086385 : Blo 2259435 5086385 := bstep (se 2 (by rfl) ⟨1907394, by rfl⟩ : syracuseStep 5086385 = 3814789) B3814789
theorem B3390923 : Blo 2259435 3390923 := bstep (se 1 (by rfl) ⟨2543192, by rfl⟩ : syracuseStep 3390923 = 5086385) B5086385
theorem B2260615 : Blo 2259435 2260615 := bstep (se 1 (by rfl) ⟨1695461, by rfl⟩ : syracuseStep 2260615 = 3390923) B3390923
theorem B2543197 : Blo 2259435 2543197 := bbase (se 3 (by rfl) ⟨476849, by rfl⟩ : syracuseStep 2543197 = 953699) (by norm_num)
theorem B3390929 : Blo 2259435 3390929 := bstep (se 2 (by rfl) ⟨1271598, by rfl⟩ : syracuseStep 3390929 = 2543197) B2543197
theorem B2260619 : Blo 2259435 2260619 := bstep (se 1 (by rfl) ⟨1695464, by rfl⟩ : syracuseStep 2260619 = 3390929) B3390929
theorem B7629605 : Blo 2259435 7629605 := bbase (se 4 (by rfl) ⟨715275, by rfl⟩ : syracuseStep 7629605 = 1430551) (by norm_num)
theorem B5086403 : Blo 2259435 5086403 := bstep (se 1 (by rfl) ⟨3814802, by rfl⟩ : syracuseStep 5086403 = 7629605) B7629605
theorem B3390935 : Blo 2259435 3390935 := bstep (se 1 (by rfl) ⟨2543201, by rfl⟩ : syracuseStep 3390935 = 5086403) B5086403
theorem B2260623 : Blo 2259435 2260623 := bstep (se 1 (by rfl) ⟨1695467, by rfl⟩ : syracuseStep 2260623 = 3390935) B3390935
theorem B3390941 : Blo 2259435 3390941 := bbase (se 3 (by rfl) ⟨635801, by rfl⟩ : syracuseStep 3390941 = 1271603) (by norm_num)
theorem B2260627 : Blo 2259435 2260627 := bstep (se 1 (by rfl) ⟨1695470, by rfl⟩ : syracuseStep 2260627 = 3390941) B3390941
theorem B5086421 : Blo 2259435 5086421 := bbase (se 7 (by rfl) ⟨59606, by rfl⟩ : syracuseStep 5086421 = 119213) (by norm_num)
theorem B3390947 : Blo 2259435 3390947 := bstep (se 1 (by rfl) ⟨2543210, by rfl⟩ : syracuseStep 3390947 = 5086421) B5086421
theorem B2260631 : Blo 2259435 2260631 := bstep (se 1 (by rfl) ⟨1695473, by rfl⟩ : syracuseStep 2260631 = 3390947) B3390947
theorem B4073741 : Blo 2259435 4073741 := bbase (se 3 (by rfl) ⟨763826, by rfl⟩ : syracuseStep 4073741 = 1527653) (by norm_num)
theorem B2715827 : Blo 2259435 2715827 := bstep (se 1 (by rfl) ⟨2036870, by rfl⟩ : syracuseStep 2715827 = 4073741) B4073741
theorem B7242205 : Blo 2259435 7242205 := bstep (se 3 (by rfl) ⟨1357913, by rfl⟩ : syracuseStep 7242205 = 2715827) B2715827
theorem B9656273 : Blo 2259435 9656273 := bstep (se 2 (by rfl) ⟨3621102, by rfl⟩ : syracuseStep 9656273 = 7242205) B7242205
theorem B6437515 : Blo 2259435 6437515 := bstep (se 1 (by rfl) ⟨4828136, by rfl⟩ : syracuseStep 6437515 = 9656273) B9656273
theorem B8583353 : Blo 2259435 8583353 := bstep (se 2 (by rfl) ⟨3218757, by rfl⟩ : syracuseStep 8583353 = 6437515) B6437515
theorem B5722235 : Blo 2259435 5722235 := bstep (se 1 (by rfl) ⟨4291676, by rfl⟩ : syracuseStep 5722235 = 8583353) B8583353
theorem B3814823 : Blo 2259435 3814823 := bstep (se 1 (by rfl) ⟨2861117, by rfl⟩ : syracuseStep 3814823 = 5722235) B5722235
theorem B2543215 : Blo 2259435 2543215 := bstep (se 1 (by rfl) ⟨1907411, by rfl⟩ : syracuseStep 2543215 = 3814823) B3814823
theorem B3390953 : Blo 2259435 3390953 := bstep (se 2 (by rfl) ⟨1271607, by rfl⟩ : syracuseStep 3390953 = 2543215) B2543215
theorem B2260635 : Blo 2259435 2260635 := bstep (se 1 (by rfl) ⟨1695476, by rfl⟩ : syracuseStep 2260635 = 3390953) B3390953
theorem B3096997 : Blo 2259435 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B66069269 : Blo 2259435 66069269 := bstep (se 6 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 66069269 = 3096997) B3096997
theorem B44046179 : Blo 2259435 44046179 := bstep (se 1 (by rfl) ⟨33034634, by rfl⟩ : syracuseStep 44046179 = 66069269) B66069269
theorem B29364119 : Blo 2259435 29364119 := bstep (se 1 (by rfl) ⟨22023089, by rfl⟩ : syracuseStep 29364119 = 44046179) B44046179
theorem B19576079 : Blo 2259435 19576079 := bstep (se 1 (by rfl) ⟨14682059, by rfl⟩ : syracuseStep 19576079 = 29364119) B29364119
theorem B13050719 : Blo 2259435 13050719 := bstep (se 1 (by rfl) ⟨9788039, by rfl⟩ : syracuseStep 13050719 = 19576079) B19576079
theorem B8700479 : Blo 2259435 8700479 := bstep (se 1 (by rfl) ⟨6525359, by rfl⟩ : syracuseStep 8700479 = 13050719) B13050719
theorem B5800319 : Blo 2259435 5800319 := bstep (se 1 (by rfl) ⟨4350239, by rfl⟩ : syracuseStep 5800319 = 8700479) B8700479
theorem B3866879 : Blo 2259435 3866879 := bstep (se 1 (by rfl) ⟨2900159, by rfl⟩ : syracuseStep 3866879 = 5800319) B5800319
theorem B2577919 : Blo 2259435 2577919 := bstep (se 1 (by rfl) ⟨1933439, by rfl⟩ : syracuseStep 2577919 = 3866879) B3866879
theorem B3437225 : Blo 2259435 3437225 := bstep (se 2 (by rfl) ⟨1288959, by rfl⟩ : syracuseStep 3437225 = 2577919) B2577919
theorem B2291483 : Blo 2259435 2291483 := bstep (se 1 (by rfl) ⟨1718612, by rfl⟩ : syracuseStep 2291483 = 3437225) B3437225
theorem B6110621 : Blo 2259435 6110621 := bstep (se 3 (by rfl) ⟨1145741, by rfl⟩ : syracuseStep 6110621 = 2291483) B2291483
theorem B4073747 : Blo 2259435 4073747 := bstep (se 1 (by rfl) ⟨3055310, by rfl⟩ : syracuseStep 4073747 = 6110621) B6110621
theorem B10863325 : Blo 2259435 10863325 := bstep (se 3 (by rfl) ⟨2036873, by rfl⟩ : syracuseStep 10863325 = 4073747) B4073747
theorem B14484433 : Blo 2259435 14484433 := bstep (se 2 (by rfl) ⟨5431662, by rfl⟩ : syracuseStep 14484433 = 10863325) B10863325
theorem B19312577 : Blo 2259435 19312577 := bstep (se 2 (by rfl) ⟨7242216, by rfl⟩ : syracuseStep 19312577 = 14484433) B14484433
theorem B12875051 : Blo 2259435 12875051 := bstep (se 1 (by rfl) ⟨9656288, by rfl⟩ : syracuseStep 12875051 = 19312577) B19312577
theorem B8583367 : Blo 2259435 8583367 := bstep (se 1 (by rfl) ⟨6437525, by rfl⟩ : syracuseStep 8583367 = 12875051) B12875051
theorem B11444489 : Blo 2259435 11444489 := bstep (se 2 (by rfl) ⟨4291683, by rfl⟩ : syracuseStep 11444489 = 8583367) B8583367
theorem B7629659 : Blo 2259435 7629659 := bstep (se 1 (by rfl) ⟨5722244, by rfl⟩ : syracuseStep 7629659 = 11444489) B11444489
theorem B5086439 : Blo 2259435 5086439 := bstep (se 1 (by rfl) ⟨3814829, by rfl⟩ : syracuseStep 5086439 = 7629659) B7629659
theorem B3390959 : Blo 2259435 3390959 := bstep (se 1 (by rfl) ⟨2543219, by rfl⟩ : syracuseStep 3390959 = 5086439) B5086439
theorem B2260639 : Blo 2259435 2260639 := bstep (se 1 (by rfl) ⟨1695479, by rfl⟩ : syracuseStep 2260639 = 3390959) B3390959
theorem B3390965 : Blo 2259435 3390965 := bbase (se 5 (by rfl) ⟨158951, by rfl⟩ : syracuseStep 3390965 = 317903) (by norm_num)
theorem B2260643 : Blo 2259435 2260643 := bstep (se 1 (by rfl) ⟨1695482, by rfl⟩ : syracuseStep 2260643 = 3390965) B3390965
theorem B2414081 : Blo 2259435 2414081 := bbase (se 2 (by rfl) ⟨905280, by rfl⟩ : syracuseStep 2414081 = 1810561) (by norm_num)
theorem B6437549 : Blo 2259435 6437549 := bstep (se 3 (by rfl) ⟨1207040, by rfl⟩ : syracuseStep 6437549 = 2414081) B2414081
theorem B4291699 : Blo 2259435 4291699 := bstep (se 1 (by rfl) ⟨3218774, by rfl⟩ : syracuseStep 4291699 = 6437549) B6437549
theorem B5722265 : Blo 2259435 5722265 := bstep (se 2 (by rfl) ⟨2145849, by rfl⟩ : syracuseStep 5722265 = 4291699) B4291699
theorem B3814843 : Blo 2259435 3814843 := bstep (se 1 (by rfl) ⟨2861132, by rfl⟩ : syracuseStep 3814843 = 5722265) B5722265
theorem B5086457 : Blo 2259435 5086457 := bstep (se 2 (by rfl) ⟨1907421, by rfl⟩ : syracuseStep 5086457 = 3814843) B3814843
theorem B3390971 : Blo 2259435 3390971 := bstep (se 1 (by rfl) ⟨2543228, by rfl⟩ : syracuseStep 3390971 = 5086457) B5086457
theorem B2260647 : Blo 2259435 2260647 := bstep (se 1 (by rfl) ⟨1695485, by rfl⟩ : syracuseStep 2260647 = 3390971) B3390971
theorem B2543233 : Blo 2259435 2543233 := bbase (se 2 (by rfl) ⟨953712, by rfl⟩ : syracuseStep 2543233 = 1907425) (by norm_num)
theorem B3390977 : Blo 2259435 3390977 := bstep (se 2 (by rfl) ⟨1271616, by rfl⟩ : syracuseStep 3390977 = 2543233) B2543233
theorem B2260651 : Blo 2259435 2260651 := bstep (se 1 (by rfl) ⟨1695488, by rfl⟩ : syracuseStep 2260651 = 3390977) B3390977
theorem B5722285 : Blo 2259435 5722285 := bbase (se 3 (by rfl) ⟨1072928, by rfl⟩ : syracuseStep 5722285 = 2145857) (by norm_num)
theorem B7629713 : Blo 2259435 7629713 := bstep (se 2 (by rfl) ⟨2861142, by rfl⟩ : syracuseStep 7629713 = 5722285) B5722285
theorem B5086475 : Blo 2259435 5086475 := bstep (se 1 (by rfl) ⟨3814856, by rfl⟩ : syracuseStep 5086475 = 7629713) B7629713
theorem B3390983 : Blo 2259435 3390983 := bstep (se 1 (by rfl) ⟨2543237, by rfl⟩ : syracuseStep 3390983 = 5086475) B5086475
theorem B2260655 : Blo 2259435 2260655 := bstep (se 1 (by rfl) ⟨1695491, by rfl⟩ : syracuseStep 2260655 = 3390983) B3390983
theorem B3390989 : Blo 2259435 3390989 := bbase (se 3 (by rfl) ⟨635810, by rfl⟩ : syracuseStep 3390989 = 1271621) (by norm_num)
theorem B2260659 : Blo 2259435 2260659 := bstep (se 1 (by rfl) ⟨1695494, by rfl⟩ : syracuseStep 2260659 = 3390989) B3390989
theorem B5086493 : Blo 2259435 5086493 := bbase (se 3 (by rfl) ⟨953717, by rfl⟩ : syracuseStep 5086493 = 1907435) (by norm_num)
theorem B3390995 : Blo 2259435 3390995 := bstep (se 1 (by rfl) ⟨2543246, by rfl⟩ : syracuseStep 3390995 = 5086493) B5086493
theorem B2260663 : Blo 2259435 2260663 := bstep (se 1 (by rfl) ⟨1695497, by rfl⟩ : syracuseStep 2260663 = 3390995) B3390995
theorem B3814877 : Blo 2259435 3814877 := bbase (se 3 (by rfl) ⟨715289, by rfl⟩ : syracuseStep 3814877 = 1430579) (by norm_num)
theorem B2543251 : Blo 2259435 2543251 := bstep (se 1 (by rfl) ⟨1907438, by rfl⟩ : syracuseStep 2543251 = 3814877) B3814877
theorem B3391001 : Blo 2259435 3391001 := bstep (se 2 (by rfl) ⟨1271625, by rfl⟩ : syracuseStep 3391001 = 2543251) B2543251
theorem B2260667 : Blo 2259435 2260667 := bstep (se 1 (by rfl) ⟨1695500, by rfl⟩ : syracuseStep 2260667 = 3391001) B3391001
theorem B3866933 : Blo 2259435 3866933 := bbase (se 5 (by rfl) ⟨181262, by rfl⟩ : syracuseStep 3866933 = 362525) (by norm_num)
theorem B2577955 : Blo 2259435 2577955 := bstep (se 1 (by rfl) ⟨1933466, by rfl⟩ : syracuseStep 2577955 = 3866933) B3866933
theorem B3437273 : Blo 2259435 3437273 := bstep (se 2 (by rfl) ⟨1288977, by rfl⟩ : syracuseStep 3437273 = 2577955) B2577955
theorem B9166061 : Blo 2259435 9166061 := bstep (se 3 (by rfl) ⟨1718636, by rfl⟩ : syracuseStep 9166061 = 3437273) B3437273
theorem B24442829 : Blo 2259435 24442829 := bstep (se 3 (by rfl) ⟨4583030, by rfl⟩ : syracuseStep 24442829 = 9166061) B9166061
theorem B16295219 : Blo 2259435 16295219 := bstep (se 1 (by rfl) ⟨12221414, by rfl⟩ : syracuseStep 16295219 = 24442829) B24442829
theorem B10863479 : Blo 2259435 10863479 := bstep (se 1 (by rfl) ⟨8147609, by rfl⟩ : syracuseStep 10863479 = 16295219) B16295219
theorem B7242319 : Blo 2259435 7242319 := bstep (se 1 (by rfl) ⟨5431739, by rfl⟩ : syracuseStep 7242319 = 10863479) B10863479
theorem B9656425 : Blo 2259435 9656425 := bstep (se 2 (by rfl) ⟨3621159, by rfl⟩ : syracuseStep 9656425 = 7242319) B7242319
theorem B12875233 : Blo 2259435 12875233 := bstep (se 2 (by rfl) ⟨4828212, by rfl⟩ : syracuseStep 12875233 = 9656425) B9656425
theorem B17166977 : Blo 2259435 17166977 := bstep (se 2 (by rfl) ⟨6437616, by rfl⟩ : syracuseStep 17166977 = 12875233) B12875233
theorem B11444651 : Blo 2259435 11444651 := bstep (se 1 (by rfl) ⟨8583488, by rfl⟩ : syracuseStep 11444651 = 17166977) B17166977
theorem B7629767 : Blo 2259435 7629767 := bstep (se 1 (by rfl) ⟨5722325, by rfl⟩ : syracuseStep 7629767 = 11444651) B11444651
theorem B5086511 : Blo 2259435 5086511 := bstep (se 1 (by rfl) ⟨3814883, by rfl⟩ : syracuseStep 5086511 = 7629767) B7629767
theorem B3391007 : Blo 2259435 3391007 := bstep (se 1 (by rfl) ⟨2543255, by rfl⟩ : syracuseStep 3391007 = 5086511) B5086511
theorem B2260671 : Blo 2259435 2260671 := bstep (se 1 (by rfl) ⟨1695503, by rfl⟩ : syracuseStep 2260671 = 3391007) B3391007
theorem B3391013 : Blo 2259435 3391013 := bbase (se 4 (by rfl) ⟨317907, by rfl⟩ : syracuseStep 3391013 = 635815) (by norm_num)
theorem B2260675 : Blo 2259435 2260675 := bstep (se 1 (by rfl) ⟨1695506, by rfl⟩ : syracuseStep 2260675 = 3391013) B3391013
theorem B2861173 : Blo 2259435 2861173 := bbase (se 5 (by rfl) ⟨134117, by rfl⟩ : syracuseStep 2861173 = 268235) (by norm_num)
theorem B3814897 : Blo 2259435 3814897 := bstep (se 2 (by rfl) ⟨1430586, by rfl⟩ : syracuseStep 3814897 = 2861173) B2861173
theorem B5086529 : Blo 2259435 5086529 := bstep (se 2 (by rfl) ⟨1907448, by rfl⟩ : syracuseStep 5086529 = 3814897) B3814897
theorem B3391019 : Blo 2259435 3391019 := bstep (se 1 (by rfl) ⟨2543264, by rfl⟩ : syracuseStep 3391019 = 5086529) B5086529
theorem B2260679 : Blo 2259435 2260679 := bstep (se 1 (by rfl) ⟨1695509, by rfl⟩ : syracuseStep 2260679 = 3391019) B3391019
theorem B2543269 : Blo 2259435 2543269 := bbase (se 4 (by rfl) ⟨238431, by rfl⟩ : syracuseStep 2543269 = 476863) (by norm_num)
theorem B3391025 : Blo 2259435 3391025 := bstep (se 2 (by rfl) ⟨1271634, by rfl⟩ : syracuseStep 3391025 = 2543269) B2543269
theorem B2260683 : Blo 2259435 2260683 := bstep (se 1 (by rfl) ⟨1695512, by rfl⟩ : syracuseStep 2260683 = 3391025) B3391025
theorem B15892789 : Blo 2259435 15892789 := bbase (se 5 (by rfl) ⟨744974, by rfl⟩ : syracuseStep 15892789 = 1489949) (by norm_num)
theorem B21190385 : Blo 2259435 21190385 := bstep (se 2 (by rfl) ⟨7946394, by rfl⟩ : syracuseStep 21190385 = 15892789) B15892789
theorem B14126923 : Blo 2259435 14126923 := bstep (se 1 (by rfl) ⟨10595192, by rfl⟩ : syracuseStep 14126923 = 21190385) B21190385
theorem B18835897 : Blo 2259435 18835897 := bstep (se 2 (by rfl) ⟨7063461, by rfl⟩ : syracuseStep 18835897 = 14126923) B14126923
theorem B25114529 : Blo 2259435 25114529 := bstep (se 2 (by rfl) ⟨9417948, by rfl⟩ : syracuseStep 25114529 = 18835897) B18835897
theorem B16743019 : Blo 2259435 16743019 := bstep (se 1 (by rfl) ⟨12557264, by rfl⟩ : syracuseStep 16743019 = 25114529) B25114529
theorem B22324025 : Blo 2259435 22324025 := bstep (se 2 (by rfl) ⟨8371509, by rfl⟩ : syracuseStep 22324025 = 16743019) B16743019
theorem B59530733 : Blo 2259435 59530733 := bstep (se 3 (by rfl) ⟨11162012, by rfl⟩ : syracuseStep 59530733 = 22324025) B22324025
theorem B39687155 : Blo 2259435 39687155 := bstep (se 1 (by rfl) ⟨29765366, by rfl⟩ : syracuseStep 39687155 = 59530733) B59530733
theorem B26458103 : Blo 2259435 26458103 := bstep (se 1 (by rfl) ⟨19843577, by rfl⟩ : syracuseStep 26458103 = 39687155) B39687155
theorem B17638735 : Blo 2259435 17638735 := bstep (se 1 (by rfl) ⟨13229051, by rfl⟩ : syracuseStep 17638735 = 26458103) B26458103
theorem B23518313 : Blo 2259435 23518313 := bstep (se 2 (by rfl) ⟨8819367, by rfl⟩ : syracuseStep 23518313 = 17638735) B17638735
theorem B15678875 : Blo 2259435 15678875 := bstep (se 1 (by rfl) ⟨11759156, by rfl⟩ : syracuseStep 15678875 = 23518313) B23518313
theorem B10452583 : Blo 2259435 10452583 := bstep (se 1 (by rfl) ⟨7839437, by rfl⟩ : syracuseStep 10452583 = 15678875) B15678875
theorem B55747109 : Blo 2259435 55747109 := bstep (se 4 (by rfl) ⟨5226291, by rfl⟩ : syracuseStep 55747109 = 10452583) B10452583
theorem B37164739 : Blo 2259435 37164739 := bstep (se 1 (by rfl) ⟨27873554, by rfl⟩ : syracuseStep 37164739 = 55747109) B55747109
theorem B49552985 : Blo 2259435 49552985 := bstep (se 2 (by rfl) ⟨18582369, by rfl⟩ : syracuseStep 49552985 = 37164739) B37164739
theorem B33035323 : Blo 2259435 33035323 := bstep (se 1 (by rfl) ⟨24776492, by rfl⟩ : syracuseStep 33035323 = 49552985) B49552985
theorem B44047097 : Blo 2259435 44047097 := bstep (se 2 (by rfl) ⟨16517661, by rfl⟩ : syracuseStep 44047097 = 33035323) B33035323
theorem B29364731 : Blo 2259435 29364731 := bstep (se 1 (by rfl) ⟨22023548, by rfl⟩ : syracuseStep 29364731 = 44047097) B44047097
theorem B19576487 : Blo 2259435 19576487 := bstep (se 1 (by rfl) ⟨14682365, by rfl⟩ : syracuseStep 19576487 = 29364731) B29364731
theorem B13050991 : Blo 2259435 13050991 := bstep (se 1 (by rfl) ⟨9788243, by rfl⟩ : syracuseStep 13050991 = 19576487) B19576487
theorem B17401321 : Blo 2259435 17401321 := bstep (se 2 (by rfl) ⟨6525495, by rfl⟩ : syracuseStep 17401321 = 13050991) B13050991
theorem B23201761 : Blo 2259435 23201761 := bstep (se 2 (by rfl) ⟨8700660, by rfl⟩ : syracuseStep 23201761 = 17401321) B17401321
theorem B30935681 : Blo 2259435 30935681 := bstep (se 2 (by rfl) ⟨11600880, by rfl⟩ : syracuseStep 30935681 = 23201761) B23201761
theorem B20623787 : Blo 2259435 20623787 := bstep (se 1 (by rfl) ⟨15467840, by rfl⟩ : syracuseStep 20623787 = 30935681) B30935681
theorem B13749191 : Blo 2259435 13749191 := bstep (se 1 (by rfl) ⟨10311893, by rfl⟩ : syracuseStep 13749191 = 20623787) B20623787
theorem B9166127 : Blo 2259435 9166127 := bstep (se 1 (by rfl) ⟨6874595, by rfl⟩ : syracuseStep 9166127 = 13749191) B13749191
theorem B24443005 : Blo 2259435 24443005 := bstep (se 3 (by rfl) ⟨4583063, by rfl⟩ : syracuseStep 24443005 = 9166127) B9166127
theorem B32590673 : Blo 2259435 32590673 := bstep (se 2 (by rfl) ⟨12221502, by rfl⟩ : syracuseStep 32590673 = 24443005) B24443005
theorem B21727115 : Blo 2259435 21727115 := bstep (se 1 (by rfl) ⟨16295336, by rfl⟩ : syracuseStep 21727115 = 32590673) B32590673
theorem B14484743 : Blo 2259435 14484743 := bstep (se 1 (by rfl) ⟨10863557, by rfl⟩ : syracuseStep 14484743 = 21727115) B21727115
theorem B9656495 : Blo 2259435 9656495 := bstep (se 1 (by rfl) ⟨7242371, by rfl⟩ : syracuseStep 9656495 = 14484743) B14484743
theorem B6437663 : Blo 2259435 6437663 := bstep (se 1 (by rfl) ⟨4828247, by rfl⟩ : syracuseStep 6437663 = 9656495) B9656495
theorem B4291775 : Blo 2259435 4291775 := bstep (se 1 (by rfl) ⟨3218831, by rfl⟩ : syracuseStep 4291775 = 6437663) B6437663
theorem B2861183 : Blo 2259435 2861183 := bstep (se 1 (by rfl) ⟨2145887, by rfl⟩ : syracuseStep 2861183 = 4291775) B4291775
theorem B7629821 : Blo 2259435 7629821 := bstep (se 3 (by rfl) ⟨1430591, by rfl⟩ : syracuseStep 7629821 = 2861183) B2861183
theorem B5086547 : Blo 2259435 5086547 := bstep (se 1 (by rfl) ⟨3814910, by rfl⟩ : syracuseStep 5086547 = 7629821) B7629821
theorem B3391031 : Blo 2259435 3391031 := bstep (se 1 (by rfl) ⟨2543273, by rfl⟩ : syracuseStep 3391031 = 5086547) B5086547
theorem B2260687 : Blo 2259435 2260687 := bstep (se 1 (by rfl) ⟨1695515, by rfl⟩ : syracuseStep 2260687 = 3391031) B3391031
theorem B3391037 : Blo 2259435 3391037 := bbase (se 3 (by rfl) ⟨635819, by rfl⟩ : syracuseStep 3391037 = 1271639) (by norm_num)
theorem B2260691 : Blo 2259435 2260691 := bstep (se 1 (by rfl) ⟨1695518, by rfl⟩ : syracuseStep 2260691 = 3391037) B3391037
theorem B5086565 : Blo 2259435 5086565 := bbase (se 4 (by rfl) ⟨476865, by rfl⟩ : syracuseStep 5086565 = 953731) (by norm_num)
theorem B3391043 : Blo 2259435 3391043 := bstep (se 1 (by rfl) ⟨2543282, by rfl⟩ : syracuseStep 3391043 = 5086565) B5086565
theorem B2260695 : Blo 2259435 2260695 := bstep (se 1 (by rfl) ⟨1695521, by rfl⟩ : syracuseStep 2260695 = 3391043) B3391043
theorem B5722397 : Blo 2259435 5722397 := bbase (se 3 (by rfl) ⟨1072949, by rfl⟩ : syracuseStep 5722397 = 2145899) (by norm_num)
theorem B3814931 : Blo 2259435 3814931 := bstep (se 1 (by rfl) ⟨2861198, by rfl⟩ : syracuseStep 3814931 = 5722397) B5722397
theorem B2543287 : Blo 2259435 2543287 := bstep (se 1 (by rfl) ⟨1907465, by rfl⟩ : syracuseStep 2543287 = 3814931) B3814931
theorem B3391049 : Blo 2259435 3391049 := bstep (se 2 (by rfl) ⟨1271643, by rfl⟩ : syracuseStep 3391049 = 2543287) B2543287
theorem B2260699 : Blo 2259435 2260699 := bstep (se 1 (by rfl) ⟨1695524, by rfl⟩ : syracuseStep 2260699 = 3391049) B3391049
theorem B4291805 : Blo 2259435 4291805 := bbase (se 3 (by rfl) ⟨804713, by rfl⟩ : syracuseStep 4291805 = 1609427) (by norm_num)
theorem B11444813 : Blo 2259435 11444813 := bstep (se 3 (by rfl) ⟨2145902, by rfl⟩ : syracuseStep 11444813 = 4291805) B4291805
theorem B7629875 : Blo 2259435 7629875 := bstep (se 1 (by rfl) ⟨5722406, by rfl⟩ : syracuseStep 7629875 = 11444813) B11444813
theorem B5086583 : Blo 2259435 5086583 := bstep (se 1 (by rfl) ⟨3814937, by rfl⟩ : syracuseStep 5086583 = 7629875) B7629875
theorem B3391055 : Blo 2259435 3391055 := bstep (se 1 (by rfl) ⟨2543291, by rfl⟩ : syracuseStep 3391055 = 5086583) B5086583
theorem B2260703 : Blo 2259435 2260703 := bstep (se 1 (by rfl) ⟨1695527, by rfl⟩ : syracuseStep 2260703 = 3391055) B3391055
theorem B3391061 : Blo 2259435 3391061 := bbase (se 8 (by rfl) ⟨19869, by rfl⟩ : syracuseStep 3391061 = 39739) (by norm_num)
theorem B2260707 : Blo 2259435 2260707 := bstep (se 1 (by rfl) ⟨1695530, by rfl⟩ : syracuseStep 2260707 = 3391061) B3391061
theorem B9656597 : Blo 2259435 9656597 := bbase (se 6 (by rfl) ⟨226326, by rfl⟩ : syracuseStep 9656597 = 452653) (by norm_num)
theorem B6437731 : Blo 2259435 6437731 := bstep (se 1 (by rfl) ⟨4828298, by rfl⟩ : syracuseStep 6437731 = 9656597) B9656597
theorem B8583641 : Blo 2259435 8583641 := bstep (se 2 (by rfl) ⟨3218865, by rfl⟩ : syracuseStep 8583641 = 6437731) B6437731
theorem B5722427 : Blo 2259435 5722427 := bstep (se 1 (by rfl) ⟨4291820, by rfl⟩ : syracuseStep 5722427 = 8583641) B8583641
theorem B3814951 : Blo 2259435 3814951 := bstep (se 1 (by rfl) ⟨2861213, by rfl⟩ : syracuseStep 3814951 = 5722427) B5722427
theorem B5086601 : Blo 2259435 5086601 := bstep (se 2 (by rfl) ⟨1907475, by rfl⟩ : syracuseStep 5086601 = 3814951) B3814951
theorem B3391067 : Blo 2259435 3391067 := bstep (se 1 (by rfl) ⟨2543300, by rfl⟩ : syracuseStep 3391067 = 5086601) B5086601
theorem B2260711 : Blo 2259435 2260711 := bstep (se 1 (by rfl) ⟨1695533, by rfl⟩ : syracuseStep 2260711 = 3391067) B3391067
theorem B2543305 : Blo 2259435 2543305 := bbase (se 2 (by rfl) ⟨953739, by rfl⟩ : syracuseStep 2543305 = 1907479) (by norm_num)
theorem B3391073 : Blo 2259435 3391073 := bstep (se 2 (by rfl) ⟨1271652, by rfl⟩ : syracuseStep 3391073 = 2543305) B2543305
theorem B2260715 : Blo 2259435 2260715 := bstep (se 1 (by rfl) ⟨1695536, by rfl⟩ : syracuseStep 2260715 = 3391073) B3391073
theorem B2322829 : Blo 2259435 2322829 := bbase (se 3 (by rfl) ⟨435530, by rfl⟩ : syracuseStep 2322829 = 871061) (by norm_num)
theorem B12388421 : Blo 2259435 12388421 := bstep (se 4 (by rfl) ⟨1161414, by rfl⟩ : syracuseStep 12388421 = 2322829) B2322829
theorem B33035789 : Blo 2259435 33035789 := bstep (se 3 (by rfl) ⟨6194210, by rfl⟩ : syracuseStep 33035789 = 12388421) B12388421
theorem B88095437 : Blo 2259435 88095437 := bstep (se 3 (by rfl) ⟨16517894, by rfl⟩ : syracuseStep 88095437 = 33035789) B33035789
theorem B58730291 : Blo 2259435 58730291 := bstep (se 1 (by rfl) ⟨44047718, by rfl⟩ : syracuseStep 58730291 = 88095437) B88095437
theorem B39153527 : Blo 2259435 39153527 := bstep (se 1 (by rfl) ⟨29365145, by rfl⟩ : syracuseStep 39153527 = 58730291) B58730291
theorem B26102351 : Blo 2259435 26102351 := bstep (se 1 (by rfl) ⟨19576763, by rfl⟩ : syracuseStep 26102351 = 39153527) B39153527
theorem B17401567 : Blo 2259435 17401567 := bstep (se 1 (by rfl) ⟨13051175, by rfl⟩ : syracuseStep 17401567 = 26102351) B26102351
theorem B23202089 : Blo 2259435 23202089 := bstep (se 2 (by rfl) ⟨8700783, by rfl⟩ : syracuseStep 23202089 = 17401567) B17401567
theorem B15468059 : Blo 2259435 15468059 := bstep (se 1 (by rfl) ⟨11601044, by rfl⟩ : syracuseStep 15468059 = 23202089) B23202089
theorem B10312039 : Blo 2259435 10312039 := bstep (se 1 (by rfl) ⟨7734029, by rfl⟩ : syracuseStep 10312039 = 15468059) B15468059
theorem B13749385 : Blo 2259435 13749385 := bstep (se 2 (by rfl) ⟨5156019, by rfl⟩ : syracuseStep 13749385 = 10312039) B10312039
theorem B18332513 : Blo 2259435 18332513 := bstep (se 2 (by rfl) ⟨6874692, by rfl⟩ : syracuseStep 18332513 = 13749385) B13749385
theorem B12221675 : Blo 2259435 12221675 := bstep (se 1 (by rfl) ⟨9166256, by rfl⟩ : syracuseStep 12221675 = 18332513) B18332513
theorem B8147783 : Blo 2259435 8147783 := bstep (se 1 (by rfl) ⟨6110837, by rfl⟩ : syracuseStep 8147783 = 12221675) B12221675
theorem B5431855 : Blo 2259435 5431855 := bstep (se 1 (by rfl) ⟨4073891, by rfl⟩ : syracuseStep 5431855 = 8147783) B8147783
theorem B7242473 : Blo 2259435 7242473 := bstep (se 2 (by rfl) ⟨2715927, by rfl⟩ : syracuseStep 7242473 = 5431855) B5431855
theorem B19313261 : Blo 2259435 19313261 := bstep (se 3 (by rfl) ⟨3621236, by rfl⟩ : syracuseStep 19313261 = 7242473) B7242473
theorem B12875507 : Blo 2259435 12875507 := bstep (se 1 (by rfl) ⟨9656630, by rfl⟩ : syracuseStep 12875507 = 19313261) B19313261
theorem B8583671 : Blo 2259435 8583671 := bstep (se 1 (by rfl) ⟨6437753, by rfl⟩ : syracuseStep 8583671 = 12875507) B12875507
theorem B5722447 : Blo 2259435 5722447 := bstep (se 1 (by rfl) ⟨4291835, by rfl⟩ : syracuseStep 5722447 = 8583671) B8583671
theorem B7629929 : Blo 2259435 7629929 := bstep (se 2 (by rfl) ⟨2861223, by rfl⟩ : syracuseStep 7629929 = 5722447) B5722447
theorem B5086619 : Blo 2259435 5086619 := bstep (se 1 (by rfl) ⟨3814964, by rfl⟩ : syracuseStep 5086619 = 7629929) B7629929
theorem B3391079 : Blo 2259435 3391079 := bstep (se 1 (by rfl) ⟨2543309, by rfl⟩ : syracuseStep 3391079 = 5086619) B5086619
theorem B2260719 : Blo 2259435 2260719 := bstep (se 1 (by rfl) ⟨1695539, by rfl⟩ : syracuseStep 2260719 = 3391079) B3391079
theorem B3391085 : Blo 2259435 3391085 := bbase (se 3 (by rfl) ⟨635828, by rfl⟩ : syracuseStep 3391085 = 1271657) (by norm_num)
theorem B2260723 : Blo 2259435 2260723 := bstep (se 1 (by rfl) ⟨1695542, by rfl⟩ : syracuseStep 2260723 = 3391085) B3391085
theorem B5086637 : Blo 2259435 5086637 := bbase (se 3 (by rfl) ⟨953744, by rfl⟩ : syracuseStep 5086637 = 1907489) (by norm_num)
theorem B3391091 : Blo 2259435 3391091 := bstep (se 1 (by rfl) ⟨2543318, by rfl⟩ : syracuseStep 3391091 = 5086637) B5086637
theorem B2260727 : Blo 2259435 2260727 := bstep (se 1 (by rfl) ⟨1695545, by rfl⟩ : syracuseStep 2260727 = 3391091) B3391091
theorem B2578025 : Blo 2259435 2578025 := bbase (se 2 (by rfl) ⟨966759, by rfl⟩ : syracuseStep 2578025 = 1933519) (by norm_num)
theorem B6874733 : Blo 2259435 6874733 := bstep (se 3 (by rfl) ⟨1289012, by rfl⟩ : syracuseStep 6874733 = 2578025) B2578025
theorem B4583155 : Blo 2259435 4583155 := bstep (se 1 (by rfl) ⟨3437366, by rfl⟩ : syracuseStep 4583155 = 6874733) B6874733
theorem B6110873 : Blo 2259435 6110873 := bstep (se 2 (by rfl) ⟨2291577, by rfl⟩ : syracuseStep 6110873 = 4583155) B4583155
theorem B4073915 : Blo 2259435 4073915 := bstep (se 1 (by rfl) ⟨3055436, by rfl⟩ : syracuseStep 4073915 = 6110873) B6110873
theorem B2715943 : Blo 2259435 2715943 := bstep (se 1 (by rfl) ⟨2036957, by rfl⟩ : syracuseStep 2715943 = 4073915) B4073915
theorem B3621257 : Blo 2259435 3621257 := bstep (se 2 (by rfl) ⟨1357971, by rfl⟩ : syracuseStep 3621257 = 2715943) B2715943
theorem B2414171 : Blo 2259435 2414171 := bstep (se 1 (by rfl) ⟨1810628, by rfl⟩ : syracuseStep 2414171 = 3621257) B3621257
theorem B6437789 : Blo 2259435 6437789 := bstep (se 3 (by rfl) ⟨1207085, by rfl⟩ : syracuseStep 6437789 = 2414171) B2414171
theorem B4291859 : Blo 2259435 4291859 := bstep (se 1 (by rfl) ⟨3218894, by rfl⟩ : syracuseStep 4291859 = 6437789) B6437789
theorem B2861239 : Blo 2259435 2861239 := bstep (se 1 (by rfl) ⟨2145929, by rfl⟩ : syracuseStep 2861239 = 4291859) B4291859
theorem B3814985 : Blo 2259435 3814985 := bstep (se 2 (by rfl) ⟨1430619, by rfl⟩ : syracuseStep 3814985 = 2861239) B2861239
theorem B2543323 : Blo 2259435 2543323 := bstep (se 1 (by rfl) ⟨1907492, by rfl⟩ : syracuseStep 2543323 = 3814985) B3814985
theorem B3391097 : Blo 2259435 3391097 := bstep (se 2 (by rfl) ⟨1271661, by rfl⟩ : syracuseStep 3391097 = 2543323) B2543323
theorem B2260731 : Blo 2259435 2260731 := bstep (se 1 (by rfl) ⟨1695548, by rfl⟩ : syracuseStep 2260731 = 3391097) B3391097
theorem B44648981 : Blo 2259435 44648981 := bbase (se 6 (by rfl) ⟨1046460, by rfl⟩ : syracuseStep 44648981 = 2092921) (by norm_num)
theorem B29765987 : Blo 2259435 29765987 := bstep (se 1 (by rfl) ⟨22324490, by rfl⟩ : syracuseStep 29765987 = 44648981) B44648981
theorem B19843991 : Blo 2259435 19843991 := bstep (se 1 (by rfl) ⟨14882993, by rfl⟩ : syracuseStep 19843991 = 29765987) B29765987
theorem B13229327 : Blo 2259435 13229327 := bstep (se 1 (by rfl) ⟨9921995, by rfl⟩ : syracuseStep 13229327 = 19843991) B19843991
theorem B8819551 : Blo 2259435 8819551 := bstep (se 1 (by rfl) ⟨6614663, by rfl⟩ : syracuseStep 8819551 = 13229327) B13229327
theorem B11759401 : Blo 2259435 11759401 := bstep (se 2 (by rfl) ⟨4409775, by rfl⟩ : syracuseStep 11759401 = 8819551) B8819551
theorem B15679201 : Blo 2259435 15679201 := bstep (se 2 (by rfl) ⟨5879700, by rfl⟩ : syracuseStep 15679201 = 11759401) B11759401
theorem B334489621 : Blo 2259435 334489621 := bstep (se 6 (by rfl) ⟨7839600, by rfl⟩ : syracuseStep 334489621 = 15679201) B15679201
theorem B445986161 : Blo 2259435 445986161 := bstep (se 2 (by rfl) ⟨167244810, by rfl⟩ : syracuseStep 445986161 = 334489621) B334489621
theorem B297324107 : Blo 2259435 297324107 := bstep (se 1 (by rfl) ⟨222993080, by rfl⟩ : syracuseStep 297324107 = 445986161) B445986161
theorem B198216071 : Blo 2259435 198216071 := bstep (se 1 (by rfl) ⟨148662053, by rfl⟩ : syracuseStep 198216071 = 297324107) B297324107
theorem B132144047 : Blo 2259435 132144047 := bstep (se 1 (by rfl) ⟨99108035, by rfl⟩ : syracuseStep 132144047 = 198216071) B198216071
theorem B88096031 : Blo 2259435 88096031 := bstep (se 1 (by rfl) ⟨66072023, by rfl⟩ : syracuseStep 88096031 = 132144047) B132144047
theorem B58730687 : Blo 2259435 58730687 := bstep (se 1 (by rfl) ⟨44048015, by rfl⟩ : syracuseStep 58730687 = 88096031) B88096031
theorem B39153791 : Blo 2259435 39153791 := bstep (se 1 (by rfl) ⟨29365343, by rfl⟩ : syracuseStep 39153791 = 58730687) B58730687
theorem B104410109 : Blo 2259435 104410109 := bstep (se 3 (by rfl) ⟨19576895, by rfl⟩ : syracuseStep 104410109 = 39153791) B39153791
theorem B69606739 : Blo 2259435 69606739 := bstep (se 1 (by rfl) ⟨52205054, by rfl⟩ : syracuseStep 69606739 = 104410109) B104410109
theorem B92808985 : Blo 2259435 92808985 := bstep (se 2 (by rfl) ⟨34803369, by rfl⟩ : syracuseStep 92808985 = 69606739) B69606739
theorem B123745313 : Blo 2259435 123745313 := bstep (se 2 (by rfl) ⟨46404492, by rfl⟩ : syracuseStep 123745313 = 92808985) B92808985
theorem B82496875 : Blo 2259435 82496875 := bstep (se 1 (by rfl) ⟨61872656, by rfl⟩ : syracuseStep 82496875 = 123745313) B123745313
theorem B109995833 : Blo 2259435 109995833 := bstep (se 2 (by rfl) ⟨41248437, by rfl⟩ : syracuseStep 109995833 = 82496875) B82496875
theorem B73330555 : Blo 2259435 73330555 := bstep (se 1 (by rfl) ⟨54997916, by rfl⟩ : syracuseStep 73330555 = 109995833) B109995833
theorem B97774073 : Blo 2259435 97774073 := bstep (se 2 (by rfl) ⟨36665277, by rfl⟩ : syracuseStep 97774073 = 73330555) B73330555
theorem B65182715 : Blo 2259435 65182715 := bstep (se 1 (by rfl) ⟨48887036, by rfl⟩ : syracuseStep 65182715 = 97774073) B97774073
theorem B43455143 : Blo 2259435 43455143 := bstep (se 1 (by rfl) ⟨32591357, by rfl⟩ : syracuseStep 43455143 = 65182715) B65182715
theorem B28970095 : Blo 2259435 28970095 := bstep (se 1 (by rfl) ⟨21727571, by rfl⟩ : syracuseStep 28970095 = 43455143) B43455143
theorem B38626793 : Blo 2259435 38626793 := bstep (se 2 (by rfl) ⟨14485047, by rfl⟩ : syracuseStep 38626793 = 28970095) B28970095
theorem B25751195 : Blo 2259435 25751195 := bstep (se 1 (by rfl) ⟨19313396, by rfl⟩ : syracuseStep 25751195 = 38626793) B38626793
theorem B17167463 : Blo 2259435 17167463 := bstep (se 1 (by rfl) ⟨12875597, by rfl⟩ : syracuseStep 17167463 = 25751195) B25751195
theorem B11444975 : Blo 2259435 11444975 := bstep (se 1 (by rfl) ⟨8583731, by rfl⟩ : syracuseStep 11444975 = 17167463) B17167463
theorem B7629983 : Blo 2259435 7629983 := bstep (se 1 (by rfl) ⟨5722487, by rfl⟩ : syracuseStep 7629983 = 11444975) B11444975
theorem B5086655 : Blo 2259435 5086655 := bstep (se 1 (by rfl) ⟨3814991, by rfl⟩ : syracuseStep 5086655 = 7629983) B7629983
theorem B3391103 : Blo 2259435 3391103 := bstep (se 1 (by rfl) ⟨2543327, by rfl⟩ : syracuseStep 3391103 = 5086655) B5086655
theorem B2260735 : Blo 2259435 2260735 := bstep (se 1 (by rfl) ⟨1695551, by rfl⟩ : syracuseStep 2260735 = 3391103) B3391103
theorem B3391109 : Blo 2259435 3391109 := bbase (se 4 (by rfl) ⟨317916, by rfl⟩ : syracuseStep 3391109 = 635833) (by norm_num)
theorem B2260739 : Blo 2259435 2260739 := bstep (se 1 (by rfl) ⟨1695554, by rfl⟩ : syracuseStep 2260739 = 3391109) B3391109
theorem B3815005 : Blo 2259435 3815005 := bbase (se 3 (by rfl) ⟨715313, by rfl⟩ : syracuseStep 3815005 = 1430627) (by norm_num)
theorem B5086673 : Blo 2259435 5086673 := bstep (se 2 (by rfl) ⟨1907502, by rfl⟩ : syracuseStep 5086673 = 3815005) B3815005
theorem B3391115 : Blo 2259435 3391115 := bstep (se 1 (by rfl) ⟨2543336, by rfl⟩ : syracuseStep 3391115 = 5086673) B5086673
theorem B2260743 : Blo 2259435 2260743 := bstep (se 1 (by rfl) ⟨1695557, by rfl⟩ : syracuseStep 2260743 = 3391115) B3391115
theorem B2543341 : Blo 2259435 2543341 := bbase (se 3 (by rfl) ⟨476876, by rfl⟩ : syracuseStep 2543341 = 953753) (by norm_num)
theorem B3391121 : Blo 2259435 3391121 := bstep (se 2 (by rfl) ⟨1271670, by rfl⟩ : syracuseStep 3391121 = 2543341) B2543341
theorem B2260747 : Blo 2259435 2260747 := bstep (se 1 (by rfl) ⟨1695560, by rfl⟩ : syracuseStep 2260747 = 3391121) B3391121
theorem B7630037 : Blo 2259435 7630037 := bbase (se 7 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 7630037 = 178829) (by norm_num)
theorem B5086691 : Blo 2259435 5086691 := bstep (se 1 (by rfl) ⟨3815018, by rfl⟩ : syracuseStep 5086691 = 7630037) B7630037
theorem B3391127 : Blo 2259435 3391127 := bstep (se 1 (by rfl) ⟨2543345, by rfl⟩ : syracuseStep 3391127 = 5086691) B5086691
theorem B2260751 : Blo 2259435 2260751 := bstep (se 1 (by rfl) ⟨1695563, by rfl⟩ : syracuseStep 2260751 = 3391127) B3391127
theorem B3391133 : Blo 2259435 3391133 := bbase (se 3 (by rfl) ⟨635837, by rfl⟩ : syracuseStep 3391133 = 1271675) (by norm_num)
theorem B2260755 : Blo 2259435 2260755 := bstep (se 1 (by rfl) ⟨1695566, by rfl⟩ : syracuseStep 2260755 = 3391133) B3391133
theorem B5086709 : Blo 2259435 5086709 := bbase (se 5 (by rfl) ⟨238439, by rfl⟩ : syracuseStep 5086709 = 476879) (by norm_num)
theorem B3391139 : Blo 2259435 3391139 := bstep (se 1 (by rfl) ⟨2543354, by rfl⟩ : syracuseStep 3391139 = 5086709) B5086709
theorem B2260759 : Blo 2259435 2260759 := bstep (se 1 (by rfl) ⟨1695569, by rfl⟩ : syracuseStep 2260759 = 3391139) B3391139
theorem B3437413 : Blo 2259435 3437413 := bbase (se 4 (by rfl) ⟨322257, by rfl⟩ : syracuseStep 3437413 = 644515) (by norm_num)
theorem B73331477 : Blo 2259435 73331477 := bstep (se 6 (by rfl) ⟨1718706, by rfl⟩ : syracuseStep 73331477 = 3437413) B3437413
theorem B48887651 : Blo 2259435 48887651 := bstep (se 1 (by rfl) ⟨36665738, by rfl⟩ : syracuseStep 48887651 = 73331477) B73331477
theorem B32591767 : Blo 2259435 32591767 := bstep (se 1 (by rfl) ⟨24443825, by rfl⟩ : syracuseStep 32591767 = 48887651) B48887651
theorem B43455689 : Blo 2259435 43455689 := bstep (se 2 (by rfl) ⟨16295883, by rfl⟩ : syracuseStep 43455689 = 32591767) B32591767
theorem B28970459 : Blo 2259435 28970459 := bstep (se 1 (by rfl) ⟨21727844, by rfl⟩ : syracuseStep 28970459 = 43455689) B43455689
theorem B19313639 : Blo 2259435 19313639 := bstep (se 1 (by rfl) ⟨14485229, by rfl⟩ : syracuseStep 19313639 = 28970459) B28970459
theorem B12875759 : Blo 2259435 12875759 := bstep (se 1 (by rfl) ⟨9656819, by rfl⟩ : syracuseStep 12875759 = 19313639) B19313639
theorem B8583839 : Blo 2259435 8583839 := bstep (se 1 (by rfl) ⟨6437879, by rfl⟩ : syracuseStep 8583839 = 12875759) B12875759
theorem B5722559 : Blo 2259435 5722559 := bstep (se 1 (by rfl) ⟨4291919, by rfl⟩ : syracuseStep 5722559 = 8583839) B8583839
theorem B3815039 : Blo 2259435 3815039 := bstep (se 1 (by rfl) ⟨2861279, by rfl⟩ : syracuseStep 3815039 = 5722559) B5722559
theorem B2543359 : Blo 2259435 2543359 := bstep (se 1 (by rfl) ⟨1907519, by rfl⟩ : syracuseStep 2543359 = 3815039) B3815039
theorem B3391145 : Blo 2259435 3391145 := bstep (se 2 (by rfl) ⟨1271679, by rfl⟩ : syracuseStep 3391145 = 2543359) B2543359
theorem B2260763 : Blo 2259435 2260763 := bstep (se 1 (by rfl) ⟨1695572, by rfl⟩ : syracuseStep 2260763 = 3391145) B3391145
theorem B2414209 : Blo 2259435 2414209 := bbase (se 2 (by rfl) ⟨905328, by rfl⟩ : syracuseStep 2414209 = 1810657) (by norm_num)
theorem B3218945 : Blo 2259435 3218945 := bstep (se 2 (by rfl) ⟨1207104, by rfl⟩ : syracuseStep 3218945 = 2414209) B2414209
theorem B8583853 : Blo 2259435 8583853 := bstep (se 3 (by rfl) ⟨1609472, by rfl⟩ : syracuseStep 8583853 = 3218945) B3218945
theorem B11445137 : Blo 2259435 11445137 := bstep (se 2 (by rfl) ⟨4291926, by rfl⟩ : syracuseStep 11445137 = 8583853) B8583853
theorem B7630091 : Blo 2259435 7630091 := bstep (se 1 (by rfl) ⟨5722568, by rfl⟩ : syracuseStep 7630091 = 11445137) B11445137
theorem B5086727 : Blo 2259435 5086727 := bstep (se 1 (by rfl) ⟨3815045, by rfl⟩ : syracuseStep 5086727 = 7630091) B7630091
theorem B3391151 : Blo 2259435 3391151 := bstep (se 1 (by rfl) ⟨2543363, by rfl⟩ : syracuseStep 3391151 = 5086727) B5086727
theorem B2260767 : Blo 2259435 2260767 := bstep (se 1 (by rfl) ⟨1695575, by rfl⟩ : syracuseStep 2260767 = 3391151) B3391151
theorem B3391157 : Blo 2259435 3391157 := bbase (se 5 (by rfl) ⟨158960, by rfl⟩ : syracuseStep 3391157 = 317921) (by norm_num)
theorem B2260771 : Blo 2259435 2260771 := bstep (se 1 (by rfl) ⟨1695578, by rfl⟩ : syracuseStep 2260771 = 3391157) B3391157
theorem B5722589 : Blo 2259435 5722589 := bbase (se 3 (by rfl) ⟨1072985, by rfl⟩ : syracuseStep 5722589 = 2145971) (by norm_num)
theorem B3815059 : Blo 2259435 3815059 := bstep (se 1 (by rfl) ⟨2861294, by rfl⟩ : syracuseStep 3815059 = 5722589) B5722589
theorem B5086745 : Blo 2259435 5086745 := bstep (se 2 (by rfl) ⟨1907529, by rfl⟩ : syracuseStep 5086745 = 3815059) B3815059
theorem B3391163 : Blo 2259435 3391163 := bstep (se 1 (by rfl) ⟨2543372, by rfl⟩ : syracuseStep 3391163 = 5086745) B5086745
theorem B2260775 : Blo 2259435 2260775 := bstep (se 1 (by rfl) ⟨1695581, by rfl⟩ : syracuseStep 2260775 = 3391163) B3391163
theorem B2543377 : Blo 2259435 2543377 := bbase (se 2 (by rfl) ⟨953766, by rfl⟩ : syracuseStep 2543377 = 1907533) (by norm_num)
theorem B3391169 : Blo 2259435 3391169 := bstep (se 2 (by rfl) ⟨1271688, by rfl⟩ : syracuseStep 3391169 = 2543377) B2543377
theorem B2260779 : Blo 2259435 2260779 := bstep (se 1 (by rfl) ⟨1695584, by rfl⟩ : syracuseStep 2260779 = 3391169) B3391169
theorem B4291957 : Blo 2259435 4291957 := bbase (se 5 (by rfl) ⟨201185, by rfl⟩ : syracuseStep 4291957 = 402371) (by norm_num)
theorem B5722609 : Blo 2259435 5722609 := bstep (se 2 (by rfl) ⟨2145978, by rfl⟩ : syracuseStep 5722609 = 4291957) B4291957
theorem B7630145 : Blo 2259435 7630145 := bstep (se 2 (by rfl) ⟨2861304, by rfl⟩ : syracuseStep 7630145 = 5722609) B5722609
theorem B5086763 : Blo 2259435 5086763 := bstep (se 1 (by rfl) ⟨3815072, by rfl⟩ : syracuseStep 5086763 = 7630145) B7630145
theorem B3391175 : Blo 2259435 3391175 := bstep (se 1 (by rfl) ⟨2543381, by rfl⟩ : syracuseStep 3391175 = 5086763) B5086763
theorem B2260783 : Blo 2259435 2260783 := bstep (se 1 (by rfl) ⟨1695587, by rfl⟩ : syracuseStep 2260783 = 3391175) B3391175
theorem B3391181 : Blo 2259435 3391181 := bbase (se 3 (by rfl) ⟨635846, by rfl⟩ : syracuseStep 3391181 = 1271693) (by norm_num)
theorem B2260787 : Blo 2259435 2260787 := bstep (se 1 (by rfl) ⟨1695590, by rfl⟩ : syracuseStep 2260787 = 3391181) B3391181
theorem B5086781 : Blo 2259435 5086781 := bbase (se 3 (by rfl) ⟨953771, by rfl⟩ : syracuseStep 5086781 = 1907543) (by norm_num)
theorem B3391187 : Blo 2259435 3391187 := bstep (se 1 (by rfl) ⟨2543390, by rfl⟩ : syracuseStep 3391187 = 5086781) B5086781
theorem B2260791 : Blo 2259435 2260791 := bstep (se 1 (by rfl) ⟨1695593, by rfl⟩ : syracuseStep 2260791 = 3391187) B3391187
theorem B3815093 : Blo 2259435 3815093 := bbase (se 5 (by rfl) ⟨178832, by rfl⟩ : syracuseStep 3815093 = 357665) (by norm_num)
theorem B2543395 : Blo 2259435 2543395 := bstep (se 1 (by rfl) ⟨1907546, by rfl⟩ : syracuseStep 2543395 = 3815093) B3815093
theorem B3391193 : Blo 2259435 3391193 := bstep (se 2 (by rfl) ⟨1271697, by rfl⟩ : syracuseStep 3391193 = 2543395) B2543395
theorem B2260795 : Blo 2259435 2260795 := bstep (se 1 (by rfl) ⟨1695596, by rfl⟩ : syracuseStep 2260795 = 3391193) B3391193
theorem B3621365 : Blo 2259435 3621365 := bbase (se 5 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 3621365 = 339503) (by norm_num)
theorem B2414243 : Blo 2259435 2414243 := bstep (se 1 (by rfl) ⟨1810682, by rfl⟩ : syracuseStep 2414243 = 3621365) B3621365
theorem B6437981 : Blo 2259435 6437981 := bstep (se 3 (by rfl) ⟨1207121, by rfl⟩ : syracuseStep 6437981 = 2414243) B2414243
theorem B17167949 : Blo 2259435 17167949 := bstep (se 3 (by rfl) ⟨3218990, by rfl⟩ : syracuseStep 17167949 = 6437981) B6437981
theorem B11445299 : Blo 2259435 11445299 := bstep (se 1 (by rfl) ⟨8583974, by rfl⟩ : syracuseStep 11445299 = 17167949) B17167949
theorem B7630199 : Blo 2259435 7630199 := bstep (se 1 (by rfl) ⟨5722649, by rfl⟩ : syracuseStep 7630199 = 11445299) B11445299
theorem B5086799 : Blo 2259435 5086799 := bstep (se 1 (by rfl) ⟨3815099, by rfl⟩ : syracuseStep 5086799 = 7630199) B7630199
theorem B3391199 : Blo 2259435 3391199 := bstep (se 1 (by rfl) ⟨2543399, by rfl⟩ : syracuseStep 3391199 = 5086799) B5086799
theorem B2260799 : Blo 2259435 2260799 := bstep (se 1 (by rfl) ⟨1695599, by rfl⟩ : syracuseStep 2260799 = 3391199) B3391199
theorem B3391205 : Blo 2259435 3391205 := bbase (se 4 (by rfl) ⟨317925, by rfl⟩ : syracuseStep 3391205 = 635851) (by norm_num)
theorem B2260803 : Blo 2259435 2260803 := bstep (se 1 (by rfl) ⟨1695602, by rfl⟩ : syracuseStep 2260803 = 3391205) B3391205
theorem B6438005 : Blo 2259435 6438005 := bbase (se 5 (by rfl) ⟨301781, by rfl⟩ : syracuseStep 6438005 = 603563) (by norm_num)
theorem B4292003 : Blo 2259435 4292003 := bstep (se 1 (by rfl) ⟨3219002, by rfl⟩ : syracuseStep 4292003 = 6438005) B6438005
theorem B2861335 : Blo 2259435 2861335 := bstep (se 1 (by rfl) ⟨2146001, by rfl⟩ : syracuseStep 2861335 = 4292003) B4292003
theorem B3815113 : Blo 2259435 3815113 := bstep (se 2 (by rfl) ⟨1430667, by rfl⟩ : syracuseStep 3815113 = 2861335) B2861335
theorem B5086817 : Blo 2259435 5086817 := bstep (se 2 (by rfl) ⟨1907556, by rfl⟩ : syracuseStep 5086817 = 3815113) B3815113
theorem B3391211 : Blo 2259435 3391211 := bstep (se 1 (by rfl) ⟨2543408, by rfl⟩ : syracuseStep 3391211 = 5086817) B5086817
theorem B2260807 : Blo 2259435 2260807 := bstep (se 1 (by rfl) ⟨1695605, by rfl⟩ : syracuseStep 2260807 = 3391211) B3391211
theorem B2543413 : Blo 2259435 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B3391217 : Blo 2259435 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B2260811 : Blo 2259435 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B2861345 : Blo 2259435 2861345 := bbase (se 2 (by rfl) ⟨1073004, by rfl⟩ : syracuseStep 2861345 = 2146009) (by norm_num)
theorem B7630253 : Blo 2259435 7630253 := bstep (se 3 (by rfl) ⟨1430672, by rfl⟩ : syracuseStep 7630253 = 2861345) B2861345
theorem B5086835 : Blo 2259435 5086835 := bstep (se 1 (by rfl) ⟨3815126, by rfl⟩ : syracuseStep 5086835 = 7630253) B7630253
theorem B3391223 : Blo 2259435 3391223 := bstep (se 1 (by rfl) ⟨2543417, by rfl⟩ : syracuseStep 3391223 = 5086835) B5086835
theorem B2260815 : Blo 2259435 2260815 := bstep (se 1 (by rfl) ⟨1695611, by rfl⟩ : syracuseStep 2260815 = 3391223) B3391223
theorem B3391229 : Blo 2259435 3391229 := bbase (se 3 (by rfl) ⟨635855, by rfl⟩ : syracuseStep 3391229 = 1271711) (by norm_num)
theorem B2260819 : Blo 2259435 2260819 := bstep (se 1 (by rfl) ⟨1695614, by rfl⟩ : syracuseStep 2260819 = 3391229) B3391229
theorem B5086853 : Blo 2259435 5086853 := bbase (se 4 (by rfl) ⟨476892, by rfl⟩ : syracuseStep 5086853 = 953785) (by norm_num)
theorem B3391235 : Blo 2259435 3391235 := bstep (se 1 (by rfl) ⟨2543426, by rfl⟩ : syracuseStep 3391235 = 5086853) B5086853
theorem B2260823 : Blo 2259435 2260823 := bstep (se 1 (by rfl) ⟨1695617, by rfl⟩ : syracuseStep 2260823 = 3391235) B3391235
theorem B7242821 : Blo 2259435 7242821 := bbase (se 4 (by rfl) ⟨679014, by rfl⟩ : syracuseStep 7242821 = 1358029) (by norm_num)
theorem B4828547 : Blo 2259435 4828547 := bstep (se 1 (by rfl) ⟨3621410, by rfl⟩ : syracuseStep 4828547 = 7242821) B7242821
theorem B3219031 : Blo 2259435 3219031 := bstep (se 1 (by rfl) ⟨2414273, by rfl⟩ : syracuseStep 3219031 = 4828547) B4828547
theorem B4292041 : Blo 2259435 4292041 := bstep (se 2 (by rfl) ⟨1609515, by rfl⟩ : syracuseStep 4292041 = 3219031) B3219031
theorem B5722721 : Blo 2259435 5722721 := bstep (se 2 (by rfl) ⟨2146020, by rfl⟩ : syracuseStep 5722721 = 4292041) B4292041
theorem B3815147 : Blo 2259435 3815147 := bstep (se 1 (by rfl) ⟨2861360, by rfl⟩ : syracuseStep 3815147 = 5722721) B5722721
theorem B2543431 : Blo 2259435 2543431 := bstep (se 1 (by rfl) ⟨1907573, by rfl⟩ : syracuseStep 2543431 = 3815147) B3815147
theorem B3391241 : Blo 2259435 3391241 := bstep (se 2 (by rfl) ⟨1271715, by rfl⟩ : syracuseStep 3391241 = 2543431) B2543431
theorem B2260827 : Blo 2259435 2260827 := bstep (se 1 (by rfl) ⟨1695620, by rfl⟩ : syracuseStep 2260827 = 3391241) B3391241
theorem B11445461 : Blo 2259435 11445461 := bbase (se 7 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 11445461 = 268253) (by norm_num)
theorem B7630307 : Blo 2259435 7630307 := bstep (se 1 (by rfl) ⟨5722730, by rfl⟩ : syracuseStep 7630307 = 11445461) B11445461
theorem B5086871 : Blo 2259435 5086871 := bstep (se 1 (by rfl) ⟨3815153, by rfl⟩ : syracuseStep 5086871 = 7630307) B7630307
theorem B3391247 : Blo 2259435 3391247 := bstep (se 1 (by rfl) ⟨2543435, by rfl⟩ : syracuseStep 3391247 = 5086871) B5086871
theorem B2260831 : Blo 2259435 2260831 := bstep (se 1 (by rfl) ⟨1695623, by rfl⟩ : syracuseStep 2260831 = 3391247) B3391247
theorem B3391253 : Blo 2259435 3391253 := bbase (se 6 (by rfl) ⟨79482, by rfl⟩ : syracuseStep 3391253 = 158965) (by norm_num)
theorem B2260835 : Blo 2259435 2260835 := bstep (se 1 (by rfl) ⟨1695626, by rfl⟩ : syracuseStep 2260835 = 3391253) B3391253
theorem B4409981 : Blo 2259435 4409981 := bbase (se 3 (by rfl) ⟨826871, by rfl⟩ : syracuseStep 4409981 = 1653743) (by norm_num)
theorem B2939987 : Blo 2259435 2939987 := bstep (se 1 (by rfl) ⟨2204990, by rfl⟩ : syracuseStep 2939987 = 4409981) B4409981
theorem B7839965 : Blo 2259435 7839965 := bstep (se 3 (by rfl) ⟨1469993, by rfl⟩ : syracuseStep 7839965 = 2939987) B2939987
theorem B5226643 : Blo 2259435 5226643 := bstep (se 1 (by rfl) ⟨3919982, by rfl⟩ : syracuseStep 5226643 = 7839965) B7839965
theorem B6968857 : Blo 2259435 6968857 := bstep (se 2 (by rfl) ⟨2613321, by rfl⟩ : syracuseStep 6968857 = 5226643) B5226643
theorem B9291809 : Blo 2259435 9291809 := bstep (se 2 (by rfl) ⟨3484428, by rfl⟩ : syracuseStep 9291809 = 6968857) B6968857
theorem B6194539 : Blo 2259435 6194539 := bstep (se 1 (by rfl) ⟨4645904, by rfl⟩ : syracuseStep 6194539 = 9291809) B9291809
theorem B33037541 : Blo 2259435 33037541 := bstep (se 4 (by rfl) ⟨3097269, by rfl⟩ : syracuseStep 33037541 = 6194539) B6194539
theorem B22025027 : Blo 2259435 22025027 := bstep (se 1 (by rfl) ⟨16518770, by rfl⟩ : syracuseStep 22025027 = 33037541) B33037541
theorem B14683351 : Blo 2259435 14683351 := bstep (se 1 (by rfl) ⟨11012513, by rfl⟩ : syracuseStep 14683351 = 22025027) B22025027
theorem B19577801 : Blo 2259435 19577801 := bstep (se 2 (by rfl) ⟨7341675, by rfl⟩ : syracuseStep 19577801 = 14683351) B14683351
theorem B13051867 : Blo 2259435 13051867 := bstep (se 1 (by rfl) ⟨9788900, by rfl⟩ : syracuseStep 13051867 = 19577801) B19577801
theorem B17402489 : Blo 2259435 17402489 := bstep (se 2 (by rfl) ⟨6525933, by rfl⟩ : syracuseStep 17402489 = 13051867) B13051867
theorem B11601659 : Blo 2259435 11601659 := bstep (se 1 (by rfl) ⟨8701244, by rfl⟩ : syracuseStep 11601659 = 17402489) B17402489
theorem B7734439 : Blo 2259435 7734439 := bstep (se 1 (by rfl) ⟨5800829, by rfl⟩ : syracuseStep 7734439 = 11601659) B11601659
theorem B10312585 : Blo 2259435 10312585 := bstep (se 2 (by rfl) ⟨3867219, by rfl⟩ : syracuseStep 10312585 = 7734439) B7734439
theorem B55000453 : Blo 2259435 55000453 := bstep (se 4 (by rfl) ⟨5156292, by rfl⟩ : syracuseStep 55000453 = 10312585) B10312585
theorem B73333937 : Blo 2259435 73333937 := bstep (se 2 (by rfl) ⟨27500226, by rfl⟩ : syracuseStep 73333937 = 55000453) B55000453
theorem B48889291 : Blo 2259435 48889291 := bstep (se 1 (by rfl) ⟨36666968, by rfl⟩ : syracuseStep 48889291 = 73333937) B73333937
theorem B65185721 : Blo 2259435 65185721 := bstep (se 2 (by rfl) ⟨24444645, by rfl⟩ : syracuseStep 65185721 = 48889291) B48889291
theorem B43457147 : Blo 2259435 43457147 := bstep (se 1 (by rfl) ⟨32592860, by rfl⟩ : syracuseStep 43457147 = 65185721) B65185721
theorem B28971431 : Blo 2259435 28971431 := bstep (se 1 (by rfl) ⟨21728573, by rfl⟩ : syracuseStep 28971431 = 43457147) B43457147
theorem B19314287 : Blo 2259435 19314287 := bstep (se 1 (by rfl) ⟨14485715, by rfl⟩ : syracuseStep 19314287 = 28971431) B28971431
theorem B12876191 : Blo 2259435 12876191 := bstep (se 1 (by rfl) ⟨9657143, by rfl⟩ : syracuseStep 12876191 = 19314287) B19314287
theorem B8584127 : Blo 2259435 8584127 := bstep (se 1 (by rfl) ⟨6438095, by rfl⟩ : syracuseStep 8584127 = 12876191) B12876191
theorem B5722751 : Blo 2259435 5722751 := bstep (se 1 (by rfl) ⟨4292063, by rfl⟩ : syracuseStep 5722751 = 8584127) B8584127
theorem B3815167 : Blo 2259435 3815167 := bstep (se 1 (by rfl) ⟨2861375, by rfl⟩ : syracuseStep 3815167 = 5722751) B5722751
theorem B5086889 : Blo 2259435 5086889 := bstep (se 2 (by rfl) ⟨1907583, by rfl⟩ : syracuseStep 5086889 = 3815167) B3815167
theorem B3391259 : Blo 2259435 3391259 := bstep (se 1 (by rfl) ⟨2543444, by rfl⟩ : syracuseStep 3391259 = 5086889) B5086889
theorem B2260839 : Blo 2259435 2260839 := bstep (se 1 (by rfl) ⟨1695629, by rfl⟩ : syracuseStep 2260839 = 3391259) B3391259
theorem B2543449 : Blo 2259435 2543449 := bbase (se 2 (by rfl) ⟨953793, by rfl⟩ : syracuseStep 2543449 = 1907587) (by norm_num)
theorem B3391265 : Blo 2259435 3391265 := bstep (se 2 (by rfl) ⟨1271724, by rfl⟩ : syracuseStep 3391265 = 2543449) B2543449
theorem B2260843 : Blo 2259435 2260843 := bstep (se 1 (by rfl) ⟨1695632, by rfl⟩ : syracuseStep 2260843 = 3391265) B3391265
theorem B4828589 : Blo 2259435 4828589 := bbase (se 3 (by rfl) ⟨905360, by rfl⟩ : syracuseStep 4828589 = 1810721) (by norm_num)
theorem B3219059 : Blo 2259435 3219059 := bstep (se 1 (by rfl) ⟨2414294, by rfl⟩ : syracuseStep 3219059 = 4828589) B4828589
theorem B8584157 : Blo 2259435 8584157 := bstep (se 3 (by rfl) ⟨1609529, by rfl⟩ : syracuseStep 8584157 = 3219059) B3219059
theorem B5722771 : Blo 2259435 5722771 := bstep (se 1 (by rfl) ⟨4292078, by rfl⟩ : syracuseStep 5722771 = 8584157) B8584157
theorem B7630361 : Blo 2259435 7630361 := bstep (se 2 (by rfl) ⟨2861385, by rfl⟩ : syracuseStep 7630361 = 5722771) B5722771
theorem B5086907 : Blo 2259435 5086907 := bstep (se 1 (by rfl) ⟨3815180, by rfl⟩ : syracuseStep 5086907 = 7630361) B7630361
theorem B3391271 : Blo 2259435 3391271 := bstep (se 1 (by rfl) ⟨2543453, by rfl⟩ : syracuseStep 3391271 = 5086907) B5086907
theorem B2260847 : Blo 2259435 2260847 := bstep (se 1 (by rfl) ⟨1695635, by rfl⟩ : syracuseStep 2260847 = 3391271) B3391271
theorem B3391277 : Blo 2259435 3391277 := bbase (se 3 (by rfl) ⟨635864, by rfl⟩ : syracuseStep 3391277 = 1271729) (by norm_num)
theorem B2260851 : Blo 2259435 2260851 := bstep (se 1 (by rfl) ⟨1695638, by rfl⟩ : syracuseStep 2260851 = 3391277) B3391277
theorem B5086925 : Blo 2259435 5086925 := bbase (se 3 (by rfl) ⟨953798, by rfl⟩ : syracuseStep 5086925 = 1907597) (by norm_num)
theorem B3391283 : Blo 2259435 3391283 := bstep (se 1 (by rfl) ⟨2543462, by rfl⟩ : syracuseStep 3391283 = 5086925) B5086925
theorem B2260855 : Blo 2259435 2260855 := bstep (se 1 (by rfl) ⟨1695641, by rfl⟩ : syracuseStep 2260855 = 3391283) B3391283
theorem B2861401 : Blo 2259435 2861401 := bbase (se 2 (by rfl) ⟨1073025, by rfl⟩ : syracuseStep 2861401 = 2146051) (by norm_num)
theorem B3815201 : Blo 2259435 3815201 := bstep (se 2 (by rfl) ⟨1430700, by rfl⟩ : syracuseStep 3815201 = 2861401) B2861401
theorem B2543467 : Blo 2259435 2543467 := bstep (se 1 (by rfl) ⟨1907600, by rfl⟩ : syracuseStep 2543467 = 3815201) B3815201
theorem B3391289 : Blo 2259435 3391289 := bstep (se 2 (by rfl) ⟨1271733, by rfl⟩ : syracuseStep 3391289 = 2543467) B2543467
theorem B2260859 : Blo 2259435 2260859 := bstep (se 1 (by rfl) ⟨1695644, by rfl⟩ : syracuseStep 2260859 = 3391289) B3391289
theorem B6968933 : Blo 2259435 6968933 := bbase (se 4 (by rfl) ⟨653337, by rfl⟩ : syracuseStep 6968933 = 1306675) (by norm_num)
theorem B4645955 : Blo 2259435 4645955 := bstep (se 1 (by rfl) ⟨3484466, by rfl⟩ : syracuseStep 4645955 = 6968933) B6968933
theorem B12389213 : Blo 2259435 12389213 := bstep (se 3 (by rfl) ⟨2322977, by rfl⟩ : syracuseStep 12389213 = 4645955) B4645955
theorem B33037901 : Blo 2259435 33037901 := bstep (se 3 (by rfl) ⟨6194606, by rfl⟩ : syracuseStep 33037901 = 12389213) B12389213
theorem B22025267 : Blo 2259435 22025267 := bstep (se 1 (by rfl) ⟨16518950, by rfl⟩ : syracuseStep 22025267 = 33037901) B33037901
theorem B14683511 : Blo 2259435 14683511 := bstep (se 1 (by rfl) ⟨11012633, by rfl⟩ : syracuseStep 14683511 = 22025267) B22025267
theorem B9789007 : Blo 2259435 9789007 := bstep (se 1 (by rfl) ⟨7341755, by rfl⟩ : syracuseStep 9789007 = 14683511) B14683511
theorem B13052009 : Blo 2259435 13052009 := bstep (se 2 (by rfl) ⟨4894503, by rfl⟩ : syracuseStep 13052009 = 9789007) B9789007
theorem B8701339 : Blo 2259435 8701339 := bstep (se 1 (by rfl) ⟨6526004, by rfl⟩ : syracuseStep 8701339 = 13052009) B13052009
theorem B11601785 : Blo 2259435 11601785 := bstep (se 2 (by rfl) ⟨4350669, by rfl⟩ : syracuseStep 11601785 = 8701339) B8701339
theorem B7734523 : Blo 2259435 7734523 := bstep (se 1 (by rfl) ⟨5800892, by rfl⟩ : syracuseStep 7734523 = 11601785) B11601785
theorem B10312697 : Blo 2259435 10312697 := bstep (se 2 (by rfl) ⟨3867261, by rfl⟩ : syracuseStep 10312697 = 7734523) B7734523
theorem B6875131 : Blo 2259435 6875131 := bstep (se 1 (by rfl) ⟨5156348, by rfl⟩ : syracuseStep 6875131 = 10312697) B10312697
theorem B9166841 : Blo 2259435 9166841 := bstep (se 2 (by rfl) ⟨3437565, by rfl⟩ : syracuseStep 9166841 = 6875131) B6875131
theorem B6111227 : Blo 2259435 6111227 := bstep (se 1 (by rfl) ⟨4583420, by rfl⟩ : syracuseStep 6111227 = 9166841) B9166841
theorem B4074151 : Blo 2259435 4074151 := bstep (se 1 (by rfl) ⟨3055613, by rfl⟩ : syracuseStep 4074151 = 6111227) B6111227
theorem B5432201 : Blo 2259435 5432201 := bstep (se 2 (by rfl) ⟨2037075, by rfl⟩ : syracuseStep 5432201 = 4074151) B4074151
theorem B3621467 : Blo 2259435 3621467 := bstep (se 1 (by rfl) ⟨2716100, by rfl⟩ : syracuseStep 3621467 = 5432201) B5432201
theorem B9657245 : Blo 2259435 9657245 := bstep (se 3 (by rfl) ⟨1810733, by rfl⟩ : syracuseStep 9657245 = 3621467) B3621467
theorem B25752653 : Blo 2259435 25752653 := bstep (se 3 (by rfl) ⟨4828622, by rfl⟩ : syracuseStep 25752653 = 9657245) B9657245
theorem B17168435 : Blo 2259435 17168435 := bstep (se 1 (by rfl) ⟨12876326, by rfl⟩ : syracuseStep 17168435 = 25752653) B25752653
theorem B11445623 : Blo 2259435 11445623 := bstep (se 1 (by rfl) ⟨8584217, by rfl⟩ : syracuseStep 11445623 = 17168435) B17168435
theorem B7630415 : Blo 2259435 7630415 := bstep (se 1 (by rfl) ⟨5722811, by rfl⟩ : syracuseStep 7630415 = 11445623) B11445623
theorem B5086943 : Blo 2259435 5086943 := bstep (se 1 (by rfl) ⟨3815207, by rfl⟩ : syracuseStep 5086943 = 7630415) B7630415
theorem B3391295 : Blo 2259435 3391295 := bstep (se 1 (by rfl) ⟨2543471, by rfl⟩ : syracuseStep 3391295 = 5086943) B5086943
theorem B2260863 : Blo 2259435 2260863 := bstep (se 1 (by rfl) ⟨1695647, by rfl⟩ : syracuseStep 2260863 = 3391295) B3391295
theorem B3391301 : Blo 2259435 3391301 := bbase (se 4 (by rfl) ⟨317934, by rfl⟩ : syracuseStep 3391301 = 635869) (by norm_num)
theorem B2260867 : Blo 2259435 2260867 := bstep (se 1 (by rfl) ⟨1695650, by rfl⟩ : syracuseStep 2260867 = 3391301) B3391301
theorem B3815221 : Blo 2259435 3815221 := bbase (se 5 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 3815221 = 357677) (by norm_num)
theorem B5086961 : Blo 2259435 5086961 := bstep (se 2 (by rfl) ⟨1907610, by rfl⟩ : syracuseStep 5086961 = 3815221) B3815221
theorem B3391307 : Blo 2259435 3391307 := bstep (se 1 (by rfl) ⟨2543480, by rfl⟩ : syracuseStep 3391307 = 5086961) B5086961
theorem B2260871 : Blo 2259435 2260871 := bstep (se 1 (by rfl) ⟨1695653, by rfl⟩ : syracuseStep 2260871 = 3391307) B3391307
theorem B2543485 : Blo 2259435 2543485 := bbase (se 3 (by rfl) ⟨476903, by rfl⟩ : syracuseStep 2543485 = 953807) (by norm_num)
theorem B3391313 : Blo 2259435 3391313 := bstep (se 2 (by rfl) ⟨1271742, by rfl⟩ : syracuseStep 3391313 = 2543485) B2543485
theorem B2260875 : Blo 2259435 2260875 := bstep (se 1 (by rfl) ⟨1695656, by rfl⟩ : syracuseStep 2260875 = 3391313) B3391313
theorem B7630469 : Blo 2259435 7630469 := bbase (se 4 (by rfl) ⟨715356, by rfl⟩ : syracuseStep 7630469 = 1430713) (by norm_num)
theorem B5086979 : Blo 2259435 5086979 := bstep (se 1 (by rfl) ⟨3815234, by rfl⟩ : syracuseStep 5086979 = 7630469) B7630469
theorem B3391319 : Blo 2259435 3391319 := bstep (se 1 (by rfl) ⟨2543489, by rfl⟩ : syracuseStep 3391319 = 5086979) B5086979
theorem B2260879 : Blo 2259435 2260879 := bstep (se 1 (by rfl) ⟨1695659, by rfl⟩ : syracuseStep 2260879 = 3391319) B3391319
theorem B3391325 : Blo 2259435 3391325 := bbase (se 3 (by rfl) ⟨635873, by rfl⟩ : syracuseStep 3391325 = 1271747) (by norm_num)
theorem B2260883 : Blo 2259435 2260883 := bstep (se 1 (by rfl) ⟨1695662, by rfl⟩ : syracuseStep 2260883 = 3391325) B3391325
theorem B5086997 : Blo 2259435 5086997 := bbase (se 6 (by rfl) ⟨119226, by rfl⟩ : syracuseStep 5086997 = 238453) (by norm_num)
theorem B3391331 : Blo 2259435 3391331 := bstep (se 1 (by rfl) ⟨2543498, by rfl⟩ : syracuseStep 3391331 = 5086997) B5086997
theorem B2260887 : Blo 2259435 2260887 := bstep (se 1 (by rfl) ⟨1695665, by rfl⟩ : syracuseStep 2260887 = 3391331) B3391331
theorem B8584325 : Blo 2259435 8584325 := bbase (se 4 (by rfl) ⟨804780, by rfl⟩ : syracuseStep 8584325 = 1609561) (by norm_num)
theorem B5722883 : Blo 2259435 5722883 := bstep (se 1 (by rfl) ⟨4292162, by rfl⟩ : syracuseStep 5722883 = 8584325) B8584325
theorem B3815255 : Blo 2259435 3815255 := bstep (se 1 (by rfl) ⟨2861441, by rfl⟩ : syracuseStep 3815255 = 5722883) B5722883
theorem B2543503 : Blo 2259435 2543503 := bstep (se 1 (by rfl) ⟨1907627, by rfl⟩ : syracuseStep 2543503 = 3815255) B3815255
theorem B3391337 : Blo 2259435 3391337 := bstep (se 2 (by rfl) ⟨1271751, by rfl⟩ : syracuseStep 3391337 = 2543503) B2543503
theorem B2260891 : Blo 2259435 2260891 := bstep (se 1 (by rfl) ⟨1695668, by rfl⟩ : syracuseStep 2260891 = 3391337) B3391337
theorem B5506397 : Blo 2259435 5506397 := bbase (se 3 (by rfl) ⟨1032449, by rfl⟩ : syracuseStep 5506397 = 2064899) (by norm_num)
theorem B3670931 : Blo 2259435 3670931 := bstep (se 1 (by rfl) ⟨2753198, by rfl⟩ : syracuseStep 3670931 = 5506397) B5506397
theorem B9789149 : Blo 2259435 9789149 := bstep (se 3 (by rfl) ⟨1835465, by rfl⟩ : syracuseStep 9789149 = 3670931) B3670931
theorem B6526099 : Blo 2259435 6526099 := bstep (se 1 (by rfl) ⟨4894574, by rfl⟩ : syracuseStep 6526099 = 9789149) B9789149
theorem B8701465 : Blo 2259435 8701465 := bstep (se 2 (by rfl) ⟨3263049, by rfl⟩ : syracuseStep 8701465 = 6526099) B6526099
theorem B11601953 : Blo 2259435 11601953 := bstep (se 2 (by rfl) ⟨4350732, by rfl⟩ : syracuseStep 11601953 = 8701465) B8701465
theorem B7734635 : Blo 2259435 7734635 := bstep (se 1 (by rfl) ⟨5800976, by rfl⟩ : syracuseStep 7734635 = 11601953) B11601953
theorem B5156423 : Blo 2259435 5156423 := bstep (se 1 (by rfl) ⟨3867317, by rfl⟩ : syracuseStep 5156423 = 7734635) B7734635
theorem B3437615 : Blo 2259435 3437615 := bstep (se 1 (by rfl) ⟨2578211, by rfl⟩ : syracuseStep 3437615 = 5156423) B5156423
theorem B2291743 : Blo 2259435 2291743 := bstep (se 1 (by rfl) ⟨1718807, by rfl⟩ : syracuseStep 2291743 = 3437615) B3437615
theorem B3055657 : Blo 2259435 3055657 := bstep (se 2 (by rfl) ⟨1145871, by rfl⟩ : syracuseStep 3055657 = 2291743) B2291743
theorem B4074209 : Blo 2259435 4074209 := bstep (se 2 (by rfl) ⟨1527828, by rfl⟩ : syracuseStep 4074209 = 3055657) B3055657
theorem B2716139 : Blo 2259435 2716139 := bstep (se 1 (by rfl) ⟨2037104, by rfl⟩ : syracuseStep 2716139 = 4074209) B4074209
theorem B7243037 : Blo 2259435 7243037 := bstep (se 3 (by rfl) ⟨1358069, by rfl⟩ : syracuseStep 7243037 = 2716139) B2716139
theorem B4828691 : Blo 2259435 4828691 := bstep (se 1 (by rfl) ⟨3621518, by rfl⟩ : syracuseStep 4828691 = 7243037) B7243037
theorem B12876509 : Blo 2259435 12876509 := bstep (se 3 (by rfl) ⟨2414345, by rfl⟩ : syracuseStep 12876509 = 4828691) B4828691
theorem B8584339 : Blo 2259435 8584339 := bstep (se 1 (by rfl) ⟨6438254, by rfl⟩ : syracuseStep 8584339 = 12876509) B12876509
theorem B11445785 : Blo 2259435 11445785 := bstep (se 2 (by rfl) ⟨4292169, by rfl⟩ : syracuseStep 11445785 = 8584339) B8584339
theorem B7630523 : Blo 2259435 7630523 := bstep (se 1 (by rfl) ⟨5722892, by rfl⟩ : syracuseStep 7630523 = 11445785) B11445785
theorem B5087015 : Blo 2259435 5087015 := bstep (se 1 (by rfl) ⟨3815261, by rfl⟩ : syracuseStep 5087015 = 7630523) B7630523
theorem B3391343 : Blo 2259435 3391343 := bstep (se 1 (by rfl) ⟨2543507, by rfl⟩ : syracuseStep 3391343 = 5087015) B5087015
theorem B2260895 : Blo 2259435 2260895 := bstep (se 1 (by rfl) ⟨1695671, by rfl⟩ : syracuseStep 2260895 = 3391343) B3391343
theorem B3391349 : Blo 2259435 3391349 := bbase (se 5 (by rfl) ⟨158969, by rfl⟩ : syracuseStep 3391349 = 317939) (by norm_num)
theorem B2260899 : Blo 2259435 2260899 := bstep (se 1 (by rfl) ⟨1695674, by rfl⟩ : syracuseStep 2260899 = 3391349) B3391349
theorem B4828709 : Blo 2259435 4828709 := bbase (se 4 (by rfl) ⟨452691, by rfl⟩ : syracuseStep 4828709 = 905383) (by norm_num)
theorem B3219139 : Blo 2259435 3219139 := bstep (se 1 (by rfl) ⟨2414354, by rfl⟩ : syracuseStep 3219139 = 4828709) B4828709
theorem B4292185 : Blo 2259435 4292185 := bstep (se 2 (by rfl) ⟨1609569, by rfl⟩ : syracuseStep 4292185 = 3219139) B3219139
theorem B5722913 : Blo 2259435 5722913 := bstep (se 2 (by rfl) ⟨2146092, by rfl⟩ : syracuseStep 5722913 = 4292185) B4292185
theorem B3815275 : Blo 2259435 3815275 := bstep (se 1 (by rfl) ⟨2861456, by rfl⟩ : syracuseStep 3815275 = 5722913) B5722913
theorem B5087033 : Blo 2259435 5087033 := bstep (se 2 (by rfl) ⟨1907637, by rfl⟩ : syracuseStep 5087033 = 3815275) B3815275
theorem B3391355 : Blo 2259435 3391355 := bstep (se 1 (by rfl) ⟨2543516, by rfl⟩ : syracuseStep 3391355 = 5087033) B5087033
theorem B2260903 : Blo 2259435 2260903 := bstep (se 1 (by rfl) ⟨1695677, by rfl⟩ : syracuseStep 2260903 = 3391355) B3391355
theorem B2543521 : Blo 2259435 2543521 := bbase (se 2 (by rfl) ⟨953820, by rfl⟩ : syracuseStep 2543521 = 1907641) (by norm_num)
theorem B3391361 : Blo 2259435 3391361 := bstep (se 2 (by rfl) ⟨1271760, by rfl⟩ : syracuseStep 3391361 = 2543521) B2543521
theorem B2260907 : Blo 2259435 2260907 := bstep (se 1 (by rfl) ⟨1695680, by rfl⟩ : syracuseStep 2260907 = 3391361) B3391361
theorem B5722933 : Blo 2259435 5722933 := bbase (se 5 (by rfl) ⟨268262, by rfl⟩ : syracuseStep 5722933 = 536525) (by norm_num)
theorem B7630577 : Blo 2259435 7630577 := bstep (se 2 (by rfl) ⟨2861466, by rfl⟩ : syracuseStep 7630577 = 5722933) B5722933
theorem B5087051 : Blo 2259435 5087051 := bstep (se 1 (by rfl) ⟨3815288, by rfl⟩ : syracuseStep 5087051 = 7630577) B7630577
theorem B3391367 : Blo 2259435 3391367 := bstep (se 1 (by rfl) ⟨2543525, by rfl⟩ : syracuseStep 3391367 = 5087051) B5087051
theorem B2260911 : Blo 2259435 2260911 := bstep (se 1 (by rfl) ⟨1695683, by rfl⟩ : syracuseStep 2260911 = 3391367) B3391367
theorem B3391373 : Blo 2259435 3391373 := bbase (se 3 (by rfl) ⟨635882, by rfl⟩ : syracuseStep 3391373 = 1271765) (by norm_num)
theorem B2260915 : Blo 2259435 2260915 := bstep (se 1 (by rfl) ⟨1695686, by rfl⟩ : syracuseStep 2260915 = 3391373) B3391373
theorem B5087069 : Blo 2259435 5087069 := bbase (se 3 (by rfl) ⟨953825, by rfl⟩ : syracuseStep 5087069 = 1907651) (by norm_num)
theorem B3391379 : Blo 2259435 3391379 := bstep (se 1 (by rfl) ⟨2543534, by rfl⟩ : syracuseStep 3391379 = 5087069) B5087069
theorem B2260919 : Blo 2259435 2260919 := bstep (se 1 (by rfl) ⟨1695689, by rfl⟩ : syracuseStep 2260919 = 3391379) B3391379
theorem B3815309 : Blo 2259435 3815309 := bbase (se 3 (by rfl) ⟨715370, by rfl⟩ : syracuseStep 3815309 = 1430741) (by norm_num)
theorem B2543539 : Blo 2259435 2543539 := bstep (se 1 (by rfl) ⟨1907654, by rfl⟩ : syracuseStep 2543539 = 3815309) B3815309
theorem B3391385 : Blo 2259435 3391385 := bstep (se 2 (by rfl) ⟨1271769, by rfl⟩ : syracuseStep 3391385 = 2543539) B2543539
theorem B2260923 : Blo 2259435 2260923 := bstep (se 1 (by rfl) ⟨1695692, by rfl⟩ : syracuseStep 2260923 = 3391385) B3391385
theorem B10864709 : Blo 2259435 10864709 := bbase (se 4 (by rfl) ⟨1018566, by rfl⟩ : syracuseStep 10864709 = 2037133) (by norm_num)
theorem B7243139 : Blo 2259435 7243139 := bstep (se 1 (by rfl) ⟨5432354, by rfl⟩ : syracuseStep 7243139 = 10864709) B10864709
theorem B19315037 : Blo 2259435 19315037 := bstep (se 3 (by rfl) ⟨3621569, by rfl⟩ : syracuseStep 19315037 = 7243139) B7243139
theorem B12876691 : Blo 2259435 12876691 := bstep (se 1 (by rfl) ⟨9657518, by rfl⟩ : syracuseStep 12876691 = 19315037) B19315037
theorem B17168921 : Blo 2259435 17168921 := bstep (se 2 (by rfl) ⟨6438345, by rfl⟩ : syracuseStep 17168921 = 12876691) B12876691
theorem B11445947 : Blo 2259435 11445947 := bstep (se 1 (by rfl) ⟨8584460, by rfl⟩ : syracuseStep 11445947 = 17168921) B17168921
theorem B7630631 : Blo 2259435 7630631 := bstep (se 1 (by rfl) ⟨5722973, by rfl⟩ : syracuseStep 7630631 = 11445947) B11445947
theorem B5087087 : Blo 2259435 5087087 := bstep (se 1 (by rfl) ⟨3815315, by rfl⟩ : syracuseStep 5087087 = 7630631) B7630631
theorem B3391391 : Blo 2259435 3391391 := bstep (se 1 (by rfl) ⟨2543543, by rfl⟩ : syracuseStep 3391391 = 5087087) B5087087
theorem B2260927 : Blo 2259435 2260927 := bstep (se 1 (by rfl) ⟨1695695, by rfl⟩ : syracuseStep 2260927 = 3391391) B3391391
theorem B3391397 : Blo 2259435 3391397 := bbase (se 4 (by rfl) ⟨317943, by rfl⟩ : syracuseStep 3391397 = 635887) (by norm_num)
theorem B2260931 : Blo 2259435 2260931 := bstep (se 1 (by rfl) ⟨1695698, by rfl⟩ : syracuseStep 2260931 = 3391397) B3391397
theorem B2861497 : Blo 2259435 2861497 := bbase (se 2 (by rfl) ⟨1073061, by rfl⟩ : syracuseStep 2861497 = 2146123) (by norm_num)
theorem B3815329 : Blo 2259435 3815329 := bstep (se 2 (by rfl) ⟨1430748, by rfl⟩ : syracuseStep 3815329 = 2861497) B2861497
theorem B5087105 : Blo 2259435 5087105 := bstep (se 2 (by rfl) ⟨1907664, by rfl⟩ : syracuseStep 5087105 = 3815329) B3815329
theorem B3391403 : Blo 2259435 3391403 := bstep (se 1 (by rfl) ⟨2543552, by rfl⟩ : syracuseStep 3391403 = 5087105) B5087105
theorem B2260935 : Blo 2259435 2260935 := bstep (se 1 (by rfl) ⟨1695701, by rfl⟩ : syracuseStep 2260935 = 3391403) B3391403
theorem B2543557 : Blo 2259435 2543557 := bbase (se 4 (by rfl) ⟨238458, by rfl⟩ : syracuseStep 2543557 = 476917) (by norm_num)
theorem B3391409 : Blo 2259435 3391409 := bstep (se 2 (by rfl) ⟨1271778, by rfl⟩ : syracuseStep 3391409 = 2543557) B2543557
theorem B2260939 : Blo 2259435 2260939 := bstep (se 1 (by rfl) ⟨1695704, by rfl⟩ : syracuseStep 2260939 = 3391409) B3391409
theorem B4292261 : Blo 2259435 4292261 := bbase (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) (by norm_num)
theorem B2861507 : Blo 2259435 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B7630685 : Blo 2259435 7630685 := bstep (se 3 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 7630685 = 2861507) B2861507
theorem B5087123 : Blo 2259435 5087123 := bstep (se 1 (by rfl) ⟨3815342, by rfl⟩ : syracuseStep 5087123 = 7630685) B7630685
theorem B3391415 : Blo 2259435 3391415 := bstep (se 1 (by rfl) ⟨2543561, by rfl⟩ : syracuseStep 3391415 = 5087123) B5087123
theorem B2260943 : Blo 2259435 2260943 := bstep (se 1 (by rfl) ⟨1695707, by rfl⟩ : syracuseStep 2260943 = 3391415) B3391415
theorem B3391421 : Blo 2259435 3391421 := bbase (se 3 (by rfl) ⟨635891, by rfl⟩ : syracuseStep 3391421 = 1271783) (by norm_num)
theorem B2260947 : Blo 2259435 2260947 := bstep (se 1 (by rfl) ⟨1695710, by rfl⟩ : syracuseStep 2260947 = 3391421) B3391421
theorem B5087141 : Blo 2259435 5087141 := bbase (se 4 (by rfl) ⟨476919, by rfl⟩ : syracuseStep 5087141 = 953839) (by norm_num)
theorem B3391427 : Blo 2259435 3391427 := bstep (se 1 (by rfl) ⟨2543570, by rfl⟩ : syracuseStep 3391427 = 5087141) B5087141
theorem B2260951 : Blo 2259435 2260951 := bstep (se 1 (by rfl) ⟨1695713, by rfl⟩ : syracuseStep 2260951 = 3391427) B3391427
theorem B5723045 : Blo 2259435 5723045 := bbase (se 4 (by rfl) ⟨536535, by rfl⟩ : syracuseStep 5723045 = 1073071) (by norm_num)
theorem B3815363 : Blo 2259435 3815363 := bstep (se 1 (by rfl) ⟨2861522, by rfl⟩ : syracuseStep 3815363 = 5723045) B5723045
theorem B2543575 : Blo 2259435 2543575 := bstep (se 1 (by rfl) ⟨1907681, by rfl⟩ : syracuseStep 2543575 = 3815363) B3815363
theorem B3391433 : Blo 2259435 3391433 := bstep (se 2 (by rfl) ⟨1271787, by rfl⟩ : syracuseStep 3391433 = 2543575) B2543575
theorem B2260955 : Blo 2259435 2260955 := bstep (se 1 (by rfl) ⟨1695716, by rfl⟩ : syracuseStep 2260955 = 3391433) B3391433
theorem B6438437 : Blo 2259435 6438437 := bbase (se 4 (by rfl) ⟨603603, by rfl⟩ : syracuseStep 6438437 = 1207207) (by norm_num)
theorem B4292291 : Blo 2259435 4292291 := bstep (se 1 (by rfl) ⟨3219218, by rfl⟩ : syracuseStep 4292291 = 6438437) B6438437
theorem B11446109 : Blo 2259435 11446109 := bstep (se 3 (by rfl) ⟨2146145, by rfl⟩ : syracuseStep 11446109 = 4292291) B4292291
theorem B7630739 : Blo 2259435 7630739 := bstep (se 1 (by rfl) ⟨5723054, by rfl⟩ : syracuseStep 7630739 = 11446109) B11446109
theorem B5087159 : Blo 2259435 5087159 := bstep (se 1 (by rfl) ⟨3815369, by rfl⟩ : syracuseStep 5087159 = 7630739) B7630739
theorem B3391439 : Blo 2259435 3391439 := bstep (se 1 (by rfl) ⟨2543579, by rfl⟩ : syracuseStep 3391439 = 5087159) B5087159
theorem B2260959 : Blo 2259435 2260959 := bstep (se 1 (by rfl) ⟨1695719, by rfl⟩ : syracuseStep 2260959 = 3391439) B3391439
theorem B3391445 : Blo 2259435 3391445 := bbase (se 7 (by rfl) ⟨39743, by rfl⟩ : syracuseStep 3391445 = 79487) (by norm_num)
theorem B2260963 : Blo 2259435 2260963 := bstep (se 1 (by rfl) ⟨1695722, by rfl⟩ : syracuseStep 2260963 = 3391445) B3391445
theorem B8584613 : Blo 2259435 8584613 := bbase (se 4 (by rfl) ⟨804807, by rfl⟩ : syracuseStep 8584613 = 1609615) (by norm_num)
theorem B5723075 : Blo 2259435 5723075 := bstep (se 1 (by rfl) ⟨4292306, by rfl⟩ : syracuseStep 5723075 = 8584613) B8584613
theorem B3815383 : Blo 2259435 3815383 := bstep (se 1 (by rfl) ⟨2861537, by rfl⟩ : syracuseStep 3815383 = 5723075) B5723075
theorem B5087177 : Blo 2259435 5087177 := bstep (se 2 (by rfl) ⟨1907691, by rfl⟩ : syracuseStep 5087177 = 3815383) B3815383
theorem B3391451 : Blo 2259435 3391451 := bstep (se 1 (by rfl) ⟨2543588, by rfl⟩ : syracuseStep 3391451 = 5087177) B5087177
theorem B2260967 : Blo 2259435 2260967 := bstep (se 1 (by rfl) ⟨1695725, by rfl⟩ : syracuseStep 2260967 = 3391451) B3391451
theorem B2543593 : Blo 2259435 2543593 := bbase (se 2 (by rfl) ⟨953847, by rfl⟩ : syracuseStep 2543593 = 1907695) (by norm_num)
theorem B3391457 : Blo 2259435 3391457 := bstep (se 2 (by rfl) ⟨1271796, by rfl⟩ : syracuseStep 3391457 = 2543593) B2543593
theorem B2260971 : Blo 2259435 2260971 := bstep (se 1 (by rfl) ⟨1695728, by rfl⟩ : syracuseStep 2260971 = 3391457) B3391457
theorem B12223061 : Blo 2259435 12223061 := bbase (se 8 (by rfl) ⟨71619, by rfl⟩ : syracuseStep 12223061 = 143239) (by norm_num)
theorem B8148707 : Blo 2259435 8148707 := bstep (se 1 (by rfl) ⟨6111530, by rfl⟩ : syracuseStep 8148707 = 12223061) B12223061
theorem B5432471 : Blo 2259435 5432471 := bstep (se 1 (by rfl) ⟨4074353, by rfl⟩ : syracuseStep 5432471 = 8148707) B8148707
theorem B3621647 : Blo 2259435 3621647 := bstep (se 1 (by rfl) ⟨2716235, by rfl⟩ : syracuseStep 3621647 = 5432471) B5432471
theorem B2414431 : Blo 2259435 2414431 := bstep (se 1 (by rfl) ⟨1810823, by rfl⟩ : syracuseStep 2414431 = 3621647) B3621647
theorem B12876965 : Blo 2259435 12876965 := bstep (se 4 (by rfl) ⟨1207215, by rfl⟩ : syracuseStep 12876965 = 2414431) B2414431
theorem B8584643 : Blo 2259435 8584643 := bstep (se 1 (by rfl) ⟨6438482, by rfl⟩ : syracuseStep 8584643 = 12876965) B12876965
theorem B5723095 : Blo 2259435 5723095 := bstep (se 1 (by rfl) ⟨4292321, by rfl⟩ : syracuseStep 5723095 = 8584643) B8584643
theorem B7630793 : Blo 2259435 7630793 := bstep (se 2 (by rfl) ⟨2861547, by rfl⟩ : syracuseStep 7630793 = 5723095) B5723095
theorem B5087195 : Blo 2259435 5087195 := bstep (se 1 (by rfl) ⟨3815396, by rfl⟩ : syracuseStep 5087195 = 7630793) B7630793
theorem B3391463 : Blo 2259435 3391463 := bstep (se 1 (by rfl) ⟨2543597, by rfl⟩ : syracuseStep 3391463 = 5087195) B5087195
theorem B2260975 : Blo 2259435 2260975 := bstep (se 1 (by rfl) ⟨1695731, by rfl⟩ : syracuseStep 2260975 = 3391463) B3391463
theorem B3391469 : Blo 2259435 3391469 := bbase (se 3 (by rfl) ⟨635900, by rfl⟩ : syracuseStep 3391469 = 1271801) (by norm_num)
theorem B2260979 : Blo 2259435 2260979 := bstep (se 1 (by rfl) ⟨1695734, by rfl⟩ : syracuseStep 2260979 = 3391469) B3391469
theorem B5087213 : Blo 2259435 5087213 := bbase (se 3 (by rfl) ⟨953852, by rfl⟩ : syracuseStep 5087213 = 1907705) (by norm_num)
theorem B3391475 : Blo 2259435 3391475 := bstep (se 1 (by rfl) ⟨2543606, by rfl⟩ : syracuseStep 3391475 = 5087213) B5087213
theorem B2260983 : Blo 2259435 2260983 := bstep (se 1 (by rfl) ⟨1695737, by rfl⟩ : syracuseStep 2260983 = 3391475) B3391475
theorem B5432501 : Blo 2259435 5432501 := bbase (se 5 (by rfl) ⟨254648, by rfl⟩ : syracuseStep 5432501 = 509297) (by norm_num)
theorem B3621667 : Blo 2259435 3621667 := bstep (se 1 (by rfl) ⟨2716250, by rfl⟩ : syracuseStep 3621667 = 5432501) B5432501
theorem B4828889 : Blo 2259435 4828889 := bstep (se 2 (by rfl) ⟨1810833, by rfl⟩ : syracuseStep 4828889 = 3621667) B3621667
theorem B3219259 : Blo 2259435 3219259 := bstep (se 1 (by rfl) ⟨2414444, by rfl⟩ : syracuseStep 3219259 = 4828889) B4828889
theorem B4292345 : Blo 2259435 4292345 := bstep (se 2 (by rfl) ⟨1609629, by rfl⟩ : syracuseStep 4292345 = 3219259) B3219259
theorem B2861563 : Blo 2259435 2861563 := bstep (se 1 (by rfl) ⟨2146172, by rfl⟩ : syracuseStep 2861563 = 4292345) B4292345
theorem B3815417 : Blo 2259435 3815417 := bstep (se 2 (by rfl) ⟨1430781, by rfl⟩ : syracuseStep 3815417 = 2861563) B2861563
theorem B2543611 : Blo 2259435 2543611 := bstep (se 1 (by rfl) ⟨1907708, by rfl⟩ : syracuseStep 2543611 = 3815417) B3815417
theorem B3391481 : Blo 2259435 3391481 := bstep (se 2 (by rfl) ⟨1271805, by rfl⟩ : syracuseStep 3391481 = 2543611) B2543611
theorem B2260987 : Blo 2259435 2260987 := bstep (se 1 (by rfl) ⟨1695740, by rfl⟩ : syracuseStep 2260987 = 3391481) B3391481
theorem B55754581 : Blo 2259435 55754581 := bbase (se 9 (by rfl) ⟨163343, by rfl⟩ : syracuseStep 55754581 = 326687) (by norm_num)
theorem B74339441 : Blo 2259435 74339441 := bstep (se 2 (by rfl) ⟨27877290, by rfl⟩ : syracuseStep 74339441 = 55754581) B55754581
theorem B49559627 : Blo 2259435 49559627 := bstep (se 1 (by rfl) ⟨37169720, by rfl⟩ : syracuseStep 49559627 = 74339441) B74339441
theorem B132159005 : Blo 2259435 132159005 := bstep (se 3 (by rfl) ⟨24779813, by rfl⟩ : syracuseStep 132159005 = 49559627) B49559627
theorem B88106003 : Blo 2259435 88106003 := bstep (se 1 (by rfl) ⟨66079502, by rfl⟩ : syracuseStep 88106003 = 132159005) B132159005
theorem B58737335 : Blo 2259435 58737335 := bstep (se 1 (by rfl) ⟨44053001, by rfl⟩ : syracuseStep 58737335 = 88106003) B88106003
theorem B626531573 : Blo 2259435 626531573 := bstep (se 5 (by rfl) ⟨29368667, by rfl⟩ : syracuseStep 626531573 = 58737335) B58737335
theorem B417687715 : Blo 2259435 417687715 := bstep (se 1 (by rfl) ⟨313265786, by rfl⟩ : syracuseStep 417687715 = 626531573) B626531573
theorem B556916953 : Blo 2259435 556916953 := bstep (se 2 (by rfl) ⟨208843857, by rfl⟩ : syracuseStep 556916953 = 417687715) B417687715
theorem B742555937 : Blo 2259435 742555937 := bstep (se 2 (by rfl) ⟨278458476, by rfl⟩ : syracuseStep 742555937 = 556916953) B556916953
theorem B495037291 : Blo 2259435 495037291 := bstep (se 1 (by rfl) ⟨371277968, by rfl⟩ : syracuseStep 495037291 = 742555937) B742555937
theorem B660049721 : Blo 2259435 660049721 := bstep (se 2 (by rfl) ⟨247518645, by rfl⟩ : syracuseStep 660049721 = 495037291) B495037291
theorem B440033147 : Blo 2259435 440033147 := bstep (se 1 (by rfl) ⟨330024860, by rfl⟩ : syracuseStep 440033147 = 660049721) B660049721
theorem B293355431 : Blo 2259435 293355431 := bstep (se 1 (by rfl) ⟨220016573, by rfl⟩ : syracuseStep 293355431 = 440033147) B440033147
theorem B195570287 : Blo 2259435 195570287 := bstep (se 1 (by rfl) ⟨146677715, by rfl⟩ : syracuseStep 195570287 = 293355431) B293355431
theorem B130380191 : Blo 2259435 130380191 := bstep (se 1 (by rfl) ⟨97785143, by rfl⟩ : syracuseStep 130380191 = 195570287) B195570287
theorem B86920127 : Blo 2259435 86920127 := bstep (se 1 (by rfl) ⟨65190095, by rfl⟩ : syracuseStep 86920127 = 130380191) B130380191
theorem B57946751 : Blo 2259435 57946751 := bstep (se 1 (by rfl) ⟨43460063, by rfl⟩ : syracuseStep 57946751 = 86920127) B86920127
theorem B38631167 : Blo 2259435 38631167 := bstep (se 1 (by rfl) ⟨28973375, by rfl⟩ : syracuseStep 38631167 = 57946751) B57946751
theorem B25754111 : Blo 2259435 25754111 := bstep (se 1 (by rfl) ⟨19315583, by rfl⟩ : syracuseStep 25754111 = 38631167) B38631167
theorem B17169407 : Blo 2259435 17169407 := bstep (se 1 (by rfl) ⟨12877055, by rfl⟩ : syracuseStep 17169407 = 25754111) B25754111
theorem B11446271 : Blo 2259435 11446271 := bstep (se 1 (by rfl) ⟨8584703, by rfl⟩ : syracuseStep 11446271 = 17169407) B17169407
theorem B7630847 : Blo 2259435 7630847 := bstep (se 1 (by rfl) ⟨5723135, by rfl⟩ : syracuseStep 7630847 = 11446271) B11446271
theorem B5087231 : Blo 2259435 5087231 := bstep (se 1 (by rfl) ⟨3815423, by rfl⟩ : syracuseStep 5087231 = 7630847) B7630847
theorem B3391487 : Blo 2259435 3391487 := bstep (se 1 (by rfl) ⟨2543615, by rfl⟩ : syracuseStep 3391487 = 5087231) B5087231
theorem B2260991 : Blo 2259435 2260991 := bstep (se 1 (by rfl) ⟨1695743, by rfl⟩ : syracuseStep 2260991 = 3391487) B3391487
theorem B3391493 : Blo 2259435 3391493 := bbase (se 4 (by rfl) ⟨317952, by rfl⟩ : syracuseStep 3391493 = 635905) (by norm_num)
theorem B2260995 : Blo 2259435 2260995 := bstep (se 1 (by rfl) ⟨1695746, by rfl⟩ : syracuseStep 2260995 = 3391493) B3391493
theorem B3815437 : Blo 2259435 3815437 := bbase (se 3 (by rfl) ⟨715394, by rfl⟩ : syracuseStep 3815437 = 1430789) (by norm_num)
theorem B5087249 : Blo 2259435 5087249 := bstep (se 2 (by rfl) ⟨1907718, by rfl⟩ : syracuseStep 5087249 = 3815437) B3815437
theorem B3391499 : Blo 2259435 3391499 := bstep (se 1 (by rfl) ⟨2543624, by rfl⟩ : syracuseStep 3391499 = 5087249) B5087249
theorem B2260999 : Blo 2259435 2260999 := bstep (se 1 (by rfl) ⟨1695749, by rfl⟩ : syracuseStep 2260999 = 3391499) B3391499
theorem B2543629 : Blo 2259435 2543629 := bbase (se 3 (by rfl) ⟨476930, by rfl⟩ : syracuseStep 2543629 = 953861) (by norm_num)
theorem B3391505 : Blo 2259435 3391505 := bstep (se 2 (by rfl) ⟨1271814, by rfl⟩ : syracuseStep 3391505 = 2543629) B2543629
theorem B2261003 : Blo 2259435 2261003 := bstep (se 1 (by rfl) ⟨1695752, by rfl⟩ : syracuseStep 2261003 = 3391505) B3391505
theorem B7630901 : Blo 2259435 7630901 := bbase (se 5 (by rfl) ⟨357698, by rfl⟩ : syracuseStep 7630901 = 715397) (by norm_num)
theorem B5087267 : Blo 2259435 5087267 := bstep (se 1 (by rfl) ⟨3815450, by rfl⟩ : syracuseStep 5087267 = 7630901) B7630901
theorem B3391511 : Blo 2259435 3391511 := bstep (se 1 (by rfl) ⟨2543633, by rfl⟩ : syracuseStep 3391511 = 5087267) B5087267
theorem B2261007 : Blo 2259435 2261007 := bstep (se 1 (by rfl) ⟨1695755, by rfl⟩ : syracuseStep 2261007 = 3391511) B3391511
theorem B3391517 : Blo 2259435 3391517 := bbase (se 3 (by rfl) ⟨635909, by rfl⟩ : syracuseStep 3391517 = 1271819) (by norm_num)
theorem B2261011 : Blo 2259435 2261011 := bstep (se 1 (by rfl) ⟨1695758, by rfl⟩ : syracuseStep 2261011 = 3391517) B3391517
theorem B5087285 : Blo 2259435 5087285 := bbase (se 5 (by rfl) ⟨238466, by rfl⟩ : syracuseStep 5087285 = 476933) (by norm_num)
theorem B3391523 : Blo 2259435 3391523 := bstep (se 1 (by rfl) ⟨2543642, by rfl⟩ : syracuseStep 3391523 = 5087285) B5087285
theorem B2261015 : Blo 2259435 2261015 := bstep (se 1 (by rfl) ⟨1695761, by rfl⟩ : syracuseStep 2261015 = 3391523) B3391523
theorem B3484709 : Blo 2259435 3484709 := bbase (se 4 (by rfl) ⟨326691, by rfl⟩ : syracuseStep 3484709 = 653383) (by norm_num)
theorem B2323139 : Blo 2259435 2323139 := bstep (se 1 (by rfl) ⟨1742354, by rfl⟩ : syracuseStep 2323139 = 3484709) B3484709
theorem B6195037 : Blo 2259435 6195037 := bstep (se 3 (by rfl) ⟨1161569, by rfl⟩ : syracuseStep 6195037 = 2323139) B2323139
theorem B8260049 : Blo 2259435 8260049 := bstep (se 2 (by rfl) ⟨3097518, by rfl⟩ : syracuseStep 8260049 = 6195037) B6195037
theorem B5506699 : Blo 2259435 5506699 := bstep (se 1 (by rfl) ⟨4130024, by rfl⟩ : syracuseStep 5506699 = 8260049) B8260049
theorem B7342265 : Blo 2259435 7342265 := bstep (se 2 (by rfl) ⟨2753349, by rfl⟩ : syracuseStep 7342265 = 5506699) B5506699
theorem B4894843 : Blo 2259435 4894843 := bstep (se 1 (by rfl) ⟨3671132, by rfl⟩ : syracuseStep 4894843 = 7342265) B7342265
theorem B6526457 : Blo 2259435 6526457 := bstep (se 2 (by rfl) ⟨2447421, by rfl⟩ : syracuseStep 6526457 = 4894843) B4894843
theorem B4350971 : Blo 2259435 4350971 := bstep (se 1 (by rfl) ⟨3263228, by rfl⟩ : syracuseStep 4350971 = 6526457) B6526457
theorem B2900647 : Blo 2259435 2900647 := bstep (se 1 (by rfl) ⟨2175485, by rfl⟩ : syracuseStep 2900647 = 4350971) B4350971
theorem B3867529 : Blo 2259435 3867529 := bstep (se 2 (by rfl) ⟨1450323, by rfl⟩ : syracuseStep 3867529 = 2900647) B2900647
theorem B5156705 : Blo 2259435 5156705 := bstep (se 2 (by rfl) ⟨1933764, by rfl⟩ : syracuseStep 5156705 = 3867529) B3867529
theorem B3437803 : Blo 2259435 3437803 := bstep (se 1 (by rfl) ⟨2578352, by rfl⟩ : syracuseStep 3437803 = 5156705) B5156705
theorem B4583737 : Blo 2259435 4583737 := bstep (se 2 (by rfl) ⟨1718901, by rfl⟩ : syracuseStep 4583737 = 3437803) B3437803
theorem B6111649 : Blo 2259435 6111649 := bstep (se 2 (by rfl) ⟨2291868, by rfl⟩ : syracuseStep 6111649 = 4583737) B4583737
theorem B8148865 : Blo 2259435 8148865 := bstep (se 2 (by rfl) ⟨3055824, by rfl⟩ : syracuseStep 8148865 = 6111649) B6111649
theorem B10865153 : Blo 2259435 10865153 := bstep (se 2 (by rfl) ⟨4074432, by rfl⟩ : syracuseStep 10865153 = 8148865) B8148865
theorem B7243435 : Blo 2259435 7243435 := bstep (se 1 (by rfl) ⟨5432576, by rfl⟩ : syracuseStep 7243435 = 10865153) B10865153
theorem B9657913 : Blo 2259435 9657913 := bstep (se 2 (by rfl) ⟨3621717, by rfl⟩ : syracuseStep 9657913 = 7243435) B7243435
theorem B12877217 : Blo 2259435 12877217 := bstep (se 2 (by rfl) ⟨4828956, by rfl⟩ : syracuseStep 12877217 = 9657913) B9657913
theorem B8584811 : Blo 2259435 8584811 := bstep (se 1 (by rfl) ⟨6438608, by rfl⟩ : syracuseStep 8584811 = 12877217) B12877217
theorem B5723207 : Blo 2259435 5723207 := bstep (se 1 (by rfl) ⟨4292405, by rfl⟩ : syracuseStep 5723207 = 8584811) B8584811
theorem B3815471 : Blo 2259435 3815471 := bstep (se 1 (by rfl) ⟨2861603, by rfl⟩ : syracuseStep 3815471 = 5723207) B5723207
theorem B2543647 : Blo 2259435 2543647 := bstep (se 1 (by rfl) ⟨1907735, by rfl⟩ : syracuseStep 2543647 = 3815471) B3815471
theorem B3391529 : Blo 2259435 3391529 := bstep (se 2 (by rfl) ⟨1271823, by rfl⟩ : syracuseStep 3391529 = 2543647) B2543647
theorem B2261019 : Blo 2259435 2261019 := bstep (se 1 (by rfl) ⟨1695764, by rfl⟩ : syracuseStep 2261019 = 3391529) B3391529
theorem B2447425 : Blo 2259435 2447425 := bbase (se 2 (by rfl) ⟨917784, by rfl⟩ : syracuseStep 2447425 = 1835569) (by norm_num)
theorem B13052933 : Blo 2259435 13052933 := bstep (se 4 (by rfl) ⟨1223712, by rfl⟩ : syracuseStep 13052933 = 2447425) B2447425
theorem B8701955 : Blo 2259435 8701955 := bstep (se 1 (by rfl) ⟨6526466, by rfl⟩ : syracuseStep 8701955 = 13052933) B13052933
theorem B5801303 : Blo 2259435 5801303 := bstep (se 1 (by rfl) ⟨4350977, by rfl⟩ : syracuseStep 5801303 = 8701955) B8701955
theorem B3867535 : Blo 2259435 3867535 := bstep (se 1 (by rfl) ⟨2900651, by rfl⟩ : syracuseStep 3867535 = 5801303) B5801303
theorem B5156713 : Blo 2259435 5156713 := bstep (se 2 (by rfl) ⟨1933767, by rfl⟩ : syracuseStep 5156713 = 3867535) B3867535
theorem B6875617 : Blo 2259435 6875617 := bstep (se 2 (by rfl) ⟨2578356, by rfl⟩ : syracuseStep 6875617 = 5156713) B5156713
theorem B9167489 : Blo 2259435 9167489 := bstep (se 2 (by rfl) ⟨3437808, by rfl⟩ : syracuseStep 9167489 = 6875617) B6875617
theorem B6111659 : Blo 2259435 6111659 := bstep (se 1 (by rfl) ⟨4583744, by rfl⟩ : syracuseStep 6111659 = 9167489) B9167489
theorem B16297757 : Blo 2259435 16297757 := bstep (se 3 (by rfl) ⟨3055829, by rfl⟩ : syracuseStep 16297757 = 6111659) B6111659
theorem B10865171 : Blo 2259435 10865171 := bstep (se 1 (by rfl) ⟨8148878, by rfl⟩ : syracuseStep 10865171 = 16297757) B16297757
theorem B7243447 : Blo 2259435 7243447 := bstep (se 1 (by rfl) ⟨5432585, by rfl⟩ : syracuseStep 7243447 = 10865171) B10865171
theorem B9657929 : Blo 2259435 9657929 := bstep (se 2 (by rfl) ⟨3621723, by rfl⟩ : syracuseStep 9657929 = 7243447) B7243447
theorem B6438619 : Blo 2259435 6438619 := bstep (se 1 (by rfl) ⟨4828964, by rfl⟩ : syracuseStep 6438619 = 9657929) B9657929
theorem B8584825 : Blo 2259435 8584825 := bstep (se 2 (by rfl) ⟨3219309, by rfl⟩ : syracuseStep 8584825 = 6438619) B6438619
theorem B11446433 : Blo 2259435 11446433 := bstep (se 2 (by rfl) ⟨4292412, by rfl⟩ : syracuseStep 11446433 = 8584825) B8584825
theorem B7630955 : Blo 2259435 7630955 := bstep (se 1 (by rfl) ⟨5723216, by rfl⟩ : syracuseStep 7630955 = 11446433) B11446433
theorem B5087303 : Blo 2259435 5087303 := bstep (se 1 (by rfl) ⟨3815477, by rfl⟩ : syracuseStep 5087303 = 7630955) B7630955
theorem B3391535 : Blo 2259435 3391535 := bstep (se 1 (by rfl) ⟨2543651, by rfl⟩ : syracuseStep 3391535 = 5087303) B5087303
theorem B2261023 : Blo 2259435 2261023 := bstep (se 1 (by rfl) ⟨1695767, by rfl⟩ : syracuseStep 2261023 = 3391535) B3391535
theorem B3391541 : Blo 2259435 3391541 := bbase (se 5 (by rfl) ⟨158978, by rfl⟩ : syracuseStep 3391541 = 317957) (by norm_num)
theorem B2261027 : Blo 2259435 2261027 := bstep (se 1 (by rfl) ⟨1695770, by rfl⟩ : syracuseStep 2261027 = 3391541) B3391541
theorem B5723237 : Blo 2259435 5723237 := bbase (se 4 (by rfl) ⟨536553, by rfl⟩ : syracuseStep 5723237 = 1073107) (by norm_num)
theorem B3815491 : Blo 2259435 3815491 := bstep (se 1 (by rfl) ⟨2861618, by rfl⟩ : syracuseStep 3815491 = 5723237) B5723237
theorem B5087321 : Blo 2259435 5087321 := bstep (se 2 (by rfl) ⟨1907745, by rfl⟩ : syracuseStep 5087321 = 3815491) B3815491
theorem B3391547 : Blo 2259435 3391547 := bstep (se 1 (by rfl) ⟨2543660, by rfl⟩ : syracuseStep 3391547 = 5087321) B5087321
theorem B2261031 : Blo 2259435 2261031 := bstep (se 1 (by rfl) ⟨1695773, by rfl⟩ : syracuseStep 2261031 = 3391547) B3391547
theorem B2543665 : Blo 2259435 2543665 := bbase (se 2 (by rfl) ⟨953874, by rfl⟩ : syracuseStep 2543665 = 1907749) (by norm_num)
theorem B3391553 : Blo 2259435 3391553 := bstep (se 2 (by rfl) ⟨1271832, by rfl⟩ : syracuseStep 3391553 = 2543665) B2543665
theorem B2261035 : Blo 2259435 2261035 := bstep (se 1 (by rfl) ⟨1695776, by rfl⟩ : syracuseStep 2261035 = 3391553) B3391553
theorem B3671165 : Blo 2259435 3671165 := bbase (se 3 (by rfl) ⟨688343, by rfl⟩ : syracuseStep 3671165 = 1376687) (by norm_num)
theorem B2447443 : Blo 2259435 2447443 := bstep (se 1 (by rfl) ⟨1835582, by rfl⟩ : syracuseStep 2447443 = 3671165) B3671165
theorem B3263257 : Blo 2259435 3263257 := bstep (se 2 (by rfl) ⟨1223721, by rfl⟩ : syracuseStep 3263257 = 2447443) B2447443
theorem B4351009 : Blo 2259435 4351009 := bstep (se 2 (by rfl) ⟨1631628, by rfl⟩ : syracuseStep 4351009 = 3263257) B3263257
theorem B5801345 : Blo 2259435 5801345 := bstep (se 2 (by rfl) ⟨2175504, by rfl⟩ : syracuseStep 5801345 = 4351009) B4351009
theorem B3867563 : Blo 2259435 3867563 := bstep (se 1 (by rfl) ⟨2900672, by rfl⟩ : syracuseStep 3867563 = 5801345) B5801345
theorem B2578375 : Blo 2259435 2578375 := bstep (se 1 (by rfl) ⟨1933781, by rfl⟩ : syracuseStep 2578375 = 3867563) B3867563
theorem B13751333 : Blo 2259435 13751333 := bstep (se 4 (by rfl) ⟨1289187, by rfl⟩ : syracuseStep 13751333 = 2578375) B2578375
theorem B9167555 : Blo 2259435 9167555 := bstep (se 1 (by rfl) ⟨6875666, by rfl⟩ : syracuseStep 9167555 = 13751333) B13751333
theorem B6111703 : Blo 2259435 6111703 := bstep (se 1 (by rfl) ⟨4583777, by rfl⟩ : syracuseStep 6111703 = 9167555) B9167555
theorem B8148937 : Blo 2259435 8148937 := bstep (se 2 (by rfl) ⟨3055851, by rfl⟩ : syracuseStep 8148937 = 6111703) B6111703
theorem B10865249 : Blo 2259435 10865249 := bstep (se 2 (by rfl) ⟨4074468, by rfl⟩ : syracuseStep 10865249 = 8148937) B8148937
theorem B7243499 : Blo 2259435 7243499 := bstep (se 1 (by rfl) ⟨5432624, by rfl⟩ : syracuseStep 7243499 = 10865249) B10865249
theorem B4828999 : Blo 2259435 4828999 := bstep (se 1 (by rfl) ⟨3621749, by rfl⟩ : syracuseStep 4828999 = 7243499) B7243499
theorem B6438665 : Blo 2259435 6438665 := bstep (se 2 (by rfl) ⟨2414499, by rfl⟩ : syracuseStep 6438665 = 4828999) B4828999
theorem B4292443 : Blo 2259435 4292443 := bstep (se 1 (by rfl) ⟨3219332, by rfl⟩ : syracuseStep 4292443 = 6438665) B6438665
theorem B5723257 : Blo 2259435 5723257 := bstep (se 2 (by rfl) ⟨2146221, by rfl⟩ : syracuseStep 5723257 = 4292443) B4292443
theorem B7631009 : Blo 2259435 7631009 := bstep (se 2 (by rfl) ⟨2861628, by rfl⟩ : syracuseStep 7631009 = 5723257) B5723257
theorem B5087339 : Blo 2259435 5087339 := bstep (se 1 (by rfl) ⟨3815504, by rfl⟩ : syracuseStep 5087339 = 7631009) B7631009
theorem B3391559 : Blo 2259435 3391559 := bstep (se 1 (by rfl) ⟨2543669, by rfl⟩ : syracuseStep 3391559 = 5087339) B5087339
theorem B2261039 : Blo 2259435 2261039 := bstep (se 1 (by rfl) ⟨1695779, by rfl⟩ : syracuseStep 2261039 = 3391559) B3391559
theorem B3391565 : Blo 2259435 3391565 := bbase (se 3 (by rfl) ⟨635918, by rfl⟩ : syracuseStep 3391565 = 1271837) (by norm_num)
theorem B2261043 : Blo 2259435 2261043 := bstep (se 1 (by rfl) ⟨1695782, by rfl⟩ : syracuseStep 2261043 = 3391565) B3391565
theorem B5087357 : Blo 2259435 5087357 := bbase (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) (by norm_num)
theorem B3391571 : Blo 2259435 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B2261047 : Blo 2259435 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B3815525 : Blo 2259435 3815525 := bbase (se 4 (by rfl) ⟨357705, by rfl⟩ : syracuseStep 3815525 = 715411) (by norm_num)
theorem B2543683 : Blo 2259435 2543683 := bstep (se 1 (by rfl) ⟨1907762, by rfl⟩ : syracuseStep 2543683 = 3815525) B3815525
theorem B3391577 : Blo 2259435 3391577 := bstep (se 2 (by rfl) ⟨1271841, by rfl⟩ : syracuseStep 3391577 = 2543683) B2543683
theorem B2261051 : Blo 2259435 2261051 := bstep (se 1 (by rfl) ⟨1695788, by rfl⟩ : syracuseStep 2261051 = 3391577) B3391577
theorem B2291905 : Blo 2259435 2291905 := bbase (se 2 (by rfl) ⟨859464, by rfl⟩ : syracuseStep 2291905 = 1718929) (by norm_num)
theorem B12223493 : Blo 2259435 12223493 := bstep (se 4 (by rfl) ⟨1145952, by rfl⟩ : syracuseStep 12223493 = 2291905) B2291905
theorem B8148995 : Blo 2259435 8148995 := bstep (se 1 (by rfl) ⟨6111746, by rfl⟩ : syracuseStep 8148995 = 12223493) B12223493
theorem B5432663 : Blo 2259435 5432663 := bstep (se 1 (by rfl) ⟨4074497, by rfl⟩ : syracuseStep 5432663 = 8148995) B8148995
theorem B3621775 : Blo 2259435 3621775 := bstep (se 1 (by rfl) ⟨2716331, by rfl⟩ : syracuseStep 3621775 = 5432663) B5432663
theorem B4829033 : Blo 2259435 4829033 := bstep (se 2 (by rfl) ⟨1810887, by rfl⟩ : syracuseStep 4829033 = 3621775) B3621775
theorem B3219355 : Blo 2259435 3219355 := bstep (se 1 (by rfl) ⟨2414516, by rfl⟩ : syracuseStep 3219355 = 4829033) B4829033
theorem B17169893 : Blo 2259435 17169893 := bstep (se 4 (by rfl) ⟨1609677, by rfl⟩ : syracuseStep 17169893 = 3219355) B3219355
theorem B11446595 : Blo 2259435 11446595 := bstep (se 1 (by rfl) ⟨8584946, by rfl⟩ : syracuseStep 11446595 = 17169893) B17169893
theorem B7631063 : Blo 2259435 7631063 := bstep (se 1 (by rfl) ⟨5723297, by rfl⟩ : syracuseStep 7631063 = 11446595) B11446595
theorem B5087375 : Blo 2259435 5087375 := bstep (se 1 (by rfl) ⟨3815531, by rfl⟩ : syracuseStep 5087375 = 7631063) B7631063
theorem B3391583 : Blo 2259435 3391583 := bstep (se 1 (by rfl) ⟨2543687, by rfl⟩ : syracuseStep 3391583 = 5087375) B5087375
theorem B2261055 : Blo 2259435 2261055 := bstep (se 1 (by rfl) ⟨1695791, by rfl⟩ : syracuseStep 2261055 = 3391583) B3391583
theorem B3391589 : Blo 2259435 3391589 := bbase (se 4 (by rfl) ⟨317961, by rfl⟩ : syracuseStep 3391589 = 635923) (by norm_num)
theorem B2261059 : Blo 2259435 2261059 := bstep (se 1 (by rfl) ⟨1695794, by rfl⟩ : syracuseStep 2261059 = 3391589) B3391589
theorem B3867605 : Blo 2259435 3867605 := bbase (se 7 (by rfl) ⟨45323, by rfl⟩ : syracuseStep 3867605 = 90647) (by norm_num)
theorem B2578403 : Blo 2259435 2578403 := bstep (se 1 (by rfl) ⟨1933802, by rfl⟩ : syracuseStep 2578403 = 3867605) B3867605
theorem B6875741 : Blo 2259435 6875741 := bstep (se 3 (by rfl) ⟨1289201, by rfl⟩ : syracuseStep 6875741 = 2578403) B2578403
theorem B4583827 : Blo 2259435 4583827 := bstep (se 1 (by rfl) ⟨3437870, by rfl⟩ : syracuseStep 4583827 = 6875741) B6875741
theorem B6111769 : Blo 2259435 6111769 := bstep (se 2 (by rfl) ⟨2291913, by rfl⟩ : syracuseStep 6111769 = 4583827) B4583827
theorem B8149025 : Blo 2259435 8149025 := bstep (se 2 (by rfl) ⟨3055884, by rfl⟩ : syracuseStep 8149025 = 6111769) B6111769
theorem B5432683 : Blo 2259435 5432683 := bstep (se 1 (by rfl) ⟨4074512, by rfl⟩ : syracuseStep 5432683 = 8149025) B8149025
theorem B7243577 : Blo 2259435 7243577 := bstep (se 2 (by rfl) ⟨2716341, by rfl⟩ : syracuseStep 7243577 = 5432683) B5432683
theorem B4829051 : Blo 2259435 4829051 := bstep (se 1 (by rfl) ⟨3621788, by rfl⟩ : syracuseStep 4829051 = 7243577) B7243577
theorem B3219367 : Blo 2259435 3219367 := bstep (se 1 (by rfl) ⟨2414525, by rfl⟩ : syracuseStep 3219367 = 4829051) B4829051
theorem B4292489 : Blo 2259435 4292489 := bstep (se 2 (by rfl) ⟨1609683, by rfl⟩ : syracuseStep 4292489 = 3219367) B3219367
theorem B2861659 : Blo 2259435 2861659 := bstep (se 1 (by rfl) ⟨2146244, by rfl⟩ : syracuseStep 2861659 = 4292489) B4292489
theorem B3815545 : Blo 2259435 3815545 := bstep (se 2 (by rfl) ⟨1430829, by rfl⟩ : syracuseStep 3815545 = 2861659) B2861659
theorem B5087393 : Blo 2259435 5087393 := bstep (se 2 (by rfl) ⟨1907772, by rfl⟩ : syracuseStep 5087393 = 3815545) B3815545
theorem B3391595 : Blo 2259435 3391595 := bstep (se 1 (by rfl) ⟨2543696, by rfl⟩ : syracuseStep 3391595 = 5087393) B5087393
theorem B2261063 : Blo 2259435 2261063 := bstep (se 1 (by rfl) ⟨1695797, by rfl⟩ : syracuseStep 2261063 = 3391595) B3391595
theorem B2543701 : Blo 2259435 2543701 := bbase (se 8 (by rfl) ⟨14904, by rfl⟩ : syracuseStep 2543701 = 29809) (by norm_num)
theorem B3391601 : Blo 2259435 3391601 := bstep (se 2 (by rfl) ⟨1271850, by rfl⟩ : syracuseStep 3391601 = 2543701) B2543701
theorem B2261067 : Blo 2259435 2261067 := bstep (se 1 (by rfl) ⟨1695800, by rfl⟩ : syracuseStep 2261067 = 3391601) B3391601
theorem B2861669 : Blo 2259435 2861669 := bbase (se 4 (by rfl) ⟨268281, by rfl⟩ : syracuseStep 2861669 = 536563) (by norm_num)
theorem B7631117 : Blo 2259435 7631117 := bstep (se 3 (by rfl) ⟨1430834, by rfl⟩ : syracuseStep 7631117 = 2861669) B2861669
theorem B5087411 : Blo 2259435 5087411 := bstep (se 1 (by rfl) ⟨3815558, by rfl⟩ : syracuseStep 5087411 = 7631117) B7631117
theorem B3391607 : Blo 2259435 3391607 := bstep (se 1 (by rfl) ⟨2543705, by rfl⟩ : syracuseStep 3391607 = 5087411) B5087411
theorem B2261071 : Blo 2259435 2261071 := bstep (se 1 (by rfl) ⟨1695803, by rfl⟩ : syracuseStep 2261071 = 3391607) B3391607
theorem B3391613 : Blo 2259435 3391613 := bbase (se 3 (by rfl) ⟨635927, by rfl⟩ : syracuseStep 3391613 = 1271855) (by norm_num)
theorem B2261075 : Blo 2259435 2261075 := bstep (se 1 (by rfl) ⟨1695806, by rfl⟩ : syracuseStep 2261075 = 3391613) B3391613
theorem B5087429 : Blo 2259435 5087429 := bbase (se 4 (by rfl) ⟨476946, by rfl⟩ : syracuseStep 5087429 = 953893) (by norm_num)
theorem B3391619 : Blo 2259435 3391619 := bstep (se 1 (by rfl) ⟨2543714, by rfl⟩ : syracuseStep 3391619 = 5087429) B5087429
theorem B2261079 : Blo 2259435 2261079 := bstep (se 1 (by rfl) ⟨1695809, by rfl⟩ : syracuseStep 2261079 = 3391619) B3391619
theorem B10865461 : Blo 2259435 10865461 := bbase (se 5 (by rfl) ⟨509318, by rfl⟩ : syracuseStep 10865461 = 1018637) (by norm_num)
theorem B14487281 : Blo 2259435 14487281 := bstep (se 2 (by rfl) ⟨5432730, by rfl⟩ : syracuseStep 14487281 = 10865461) B10865461
theorem B9658187 : Blo 2259435 9658187 := bstep (se 1 (by rfl) ⟨7243640, by rfl⟩ : syracuseStep 9658187 = 14487281) B14487281
theorem B6438791 : Blo 2259435 6438791 := bstep (se 1 (by rfl) ⟨4829093, by rfl⟩ : syracuseStep 6438791 = 9658187) B9658187
theorem B4292527 : Blo 2259435 4292527 := bstep (se 1 (by rfl) ⟨3219395, by rfl⟩ : syracuseStep 4292527 = 6438791) B6438791
theorem B5723369 : Blo 2259435 5723369 := bstep (se 2 (by rfl) ⟨2146263, by rfl⟩ : syracuseStep 5723369 = 4292527) B4292527
theorem B3815579 : Blo 2259435 3815579 := bstep (se 1 (by rfl) ⟨2861684, by rfl⟩ : syracuseStep 3815579 = 5723369) B5723369
theorem B2543719 : Blo 2259435 2543719 := bstep (se 1 (by rfl) ⟨1907789, by rfl⟩ : syracuseStep 2543719 = 3815579) B3815579
theorem B3391625 : Blo 2259435 3391625 := bstep (se 2 (by rfl) ⟨1271859, by rfl⟩ : syracuseStep 3391625 = 2543719) B2543719
theorem B2261083 : Blo 2259435 2261083 := bstep (se 1 (by rfl) ⟨1695812, by rfl⟩ : syracuseStep 2261083 = 3391625) B3391625
theorem B11446757 : Blo 2259435 11446757 := bbase (se 4 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 11446757 = 2146267) (by norm_num)
theorem B7631171 : Blo 2259435 7631171 := bstep (se 1 (by rfl) ⟨5723378, by rfl⟩ : syracuseStep 7631171 = 11446757) B11446757
theorem B5087447 : Blo 2259435 5087447 := bstep (se 1 (by rfl) ⟨3815585, by rfl⟩ : syracuseStep 5087447 = 7631171) B7631171
theorem B3391631 : Blo 2259435 3391631 := bstep (se 1 (by rfl) ⟨2543723, by rfl⟩ : syracuseStep 3391631 = 5087447) B5087447
theorem B2261087 : Blo 2259435 2261087 := bstep (se 1 (by rfl) ⟨1695815, by rfl⟩ : syracuseStep 2261087 = 3391631) B3391631
theorem B3391637 : Blo 2259435 3391637 := bbase (se 6 (by rfl) ⟨79491, by rfl⟩ : syracuseStep 3391637 = 158983) (by norm_num)
theorem B2261091 : Blo 2259435 2261091 := bstep (se 1 (by rfl) ⟨1695818, by rfl⟩ : syracuseStep 2261091 = 3391637) B3391637
theorem B4351117 : Blo 2259435 4351117 := bbase (se 3 (by rfl) ⟨815834, by rfl⟩ : syracuseStep 4351117 = 1631669) (by norm_num)
theorem B5801489 : Blo 2259435 5801489 := bstep (se 2 (by rfl) ⟨2175558, by rfl⟩ : syracuseStep 5801489 = 4351117) B4351117
theorem B3867659 : Blo 2259435 3867659 := bstep (se 1 (by rfl) ⟨2900744, by rfl⟩ : syracuseStep 3867659 = 5801489) B5801489
theorem B2578439 : Blo 2259435 2578439 := bstep (se 1 (by rfl) ⟨1933829, by rfl⟩ : syracuseStep 2578439 = 3867659) B3867659
theorem B6875837 : Blo 2259435 6875837 := bstep (se 3 (by rfl) ⟨1289219, by rfl⟩ : syracuseStep 6875837 = 2578439) B2578439
theorem B4583891 : Blo 2259435 4583891 := bstep (se 1 (by rfl) ⟨3437918, by rfl⟩ : syracuseStep 4583891 = 6875837) B6875837
theorem B12223709 : Blo 2259435 12223709 := bstep (se 3 (by rfl) ⟨2291945, by rfl⟩ : syracuseStep 12223709 = 4583891) B4583891
theorem B8149139 : Blo 2259435 8149139 := bstep (se 1 (by rfl) ⟨6111854, by rfl⟩ : syracuseStep 8149139 = 12223709) B12223709
theorem B5432759 : Blo 2259435 5432759 := bstep (se 1 (by rfl) ⟨4074569, by rfl⟩ : syracuseStep 5432759 = 8149139) B8149139
theorem B3621839 : Blo 2259435 3621839 := bstep (se 1 (by rfl) ⟨2716379, by rfl⟩ : syracuseStep 3621839 = 5432759) B5432759
theorem B9658237 : Blo 2259435 9658237 := bstep (se 3 (by rfl) ⟨1810919, by rfl⟩ : syracuseStep 9658237 = 3621839) B3621839
theorem B12877649 : Blo 2259435 12877649 := bstep (se 2 (by rfl) ⟨4829118, by rfl⟩ : syracuseStep 12877649 = 9658237) B9658237
theorem B8585099 : Blo 2259435 8585099 := bstep (se 1 (by rfl) ⟨6438824, by rfl⟩ : syracuseStep 8585099 = 12877649) B12877649
theorem B5723399 : Blo 2259435 5723399 := bstep (se 1 (by rfl) ⟨4292549, by rfl⟩ : syracuseStep 5723399 = 8585099) B8585099
theorem B3815599 : Blo 2259435 3815599 := bstep (se 1 (by rfl) ⟨2861699, by rfl⟩ : syracuseStep 3815599 = 5723399) B5723399
theorem B5087465 : Blo 2259435 5087465 := bstep (se 2 (by rfl) ⟨1907799, by rfl⟩ : syracuseStep 5087465 = 3815599) B3815599
theorem B3391643 : Blo 2259435 3391643 := bstep (se 1 (by rfl) ⟨2543732, by rfl⟩ : syracuseStep 3391643 = 5087465) B5087465
theorem B2261095 : Blo 2259435 2261095 := bstep (se 1 (by rfl) ⟨1695821, by rfl⟩ : syracuseStep 2261095 = 3391643) B3391643
theorem B2543737 : Blo 2259435 2543737 := bbase (se 2 (by rfl) ⟨953901, by rfl⟩ : syracuseStep 2543737 = 1907803) (by norm_num)
theorem B3391649 : Blo 2259435 3391649 := bstep (se 2 (by rfl) ⟨1271868, by rfl⟩ : syracuseStep 3391649 = 2543737) B2543737
theorem B2261099 : Blo 2259435 2261099 := bstep (se 1 (by rfl) ⟨1695824, by rfl⟩ : syracuseStep 2261099 = 3391649) B3391649
theorem B5960893 : Blo 2259435 5960893 := bbase (se 3 (by rfl) ⟨1117667, by rfl⟩ : syracuseStep 5960893 = 2235335) (by norm_num)
theorem B7947857 : Blo 2259435 7947857 := bstep (se 2 (by rfl) ⟨2980446, by rfl⟩ : syracuseStep 7947857 = 5960893) B5960893
theorem B5298571 : Blo 2259435 5298571 := bstep (se 1 (by rfl) ⟨3973928, by rfl⟩ : syracuseStep 5298571 = 7947857) B7947857
theorem B7064761 : Blo 2259435 7064761 := bstep (se 2 (by rfl) ⟨2649285, by rfl⟩ : syracuseStep 7064761 = 5298571) B5298571
theorem B9419681 : Blo 2259435 9419681 := bstep (se 2 (by rfl) ⟨3532380, by rfl⟩ : syracuseStep 9419681 = 7064761) B7064761
theorem B6279787 : Blo 2259435 6279787 := bstep (se 1 (by rfl) ⟨4709840, by rfl⟩ : syracuseStep 6279787 = 9419681) B9419681
theorem B33492197 : Blo 2259435 33492197 := bstep (se 4 (by rfl) ⟨3139893, by rfl⟩ : syracuseStep 33492197 = 6279787) B6279787
theorem B22328131 : Blo 2259435 22328131 := bstep (se 1 (by rfl) ⟨16746098, by rfl⟩ : syracuseStep 22328131 = 33492197) B33492197
theorem B29770841 : Blo 2259435 29770841 := bstep (se 2 (by rfl) ⟨11164065, by rfl⟩ : syracuseStep 29770841 = 22328131) B22328131
theorem B19847227 : Blo 2259435 19847227 := bstep (se 1 (by rfl) ⟨14885420, by rfl⟩ : syracuseStep 19847227 = 29770841) B29770841
theorem B26462969 : Blo 2259435 26462969 := bstep (se 2 (by rfl) ⟨9923613, by rfl⟩ : syracuseStep 26462969 = 19847227) B19847227
theorem B17641979 : Blo 2259435 17641979 := bstep (se 1 (by rfl) ⟨13231484, by rfl⟩ : syracuseStep 17641979 = 26462969) B26462969
theorem B11761319 : Blo 2259435 11761319 := bstep (se 1 (by rfl) ⟨8820989, by rfl⟩ : syracuseStep 11761319 = 17641979) B17641979
theorem B31363517 : Blo 2259435 31363517 := bstep (se 3 (by rfl) ⟨5880659, by rfl⟩ : syracuseStep 31363517 = 11761319) B11761319
theorem B20909011 : Blo 2259435 20909011 := bstep (se 1 (by rfl) ⟨15681758, by rfl⟩ : syracuseStep 20909011 = 31363517) B31363517
theorem B27878681 : Blo 2259435 27878681 := bstep (se 2 (by rfl) ⟨10454505, by rfl⟩ : syracuseStep 27878681 = 20909011) B20909011
theorem B18585787 : Blo 2259435 18585787 := bstep (se 1 (by rfl) ⟨13939340, by rfl⟩ : syracuseStep 18585787 = 27878681) B27878681
theorem B24781049 : Blo 2259435 24781049 := bstep (se 2 (by rfl) ⟨9292893, by rfl⟩ : syracuseStep 24781049 = 18585787) B18585787
theorem B16520699 : Blo 2259435 16520699 := bstep (se 1 (by rfl) ⟨12390524, by rfl⟩ : syracuseStep 16520699 = 24781049) B24781049
theorem B11013799 : Blo 2259435 11013799 := bstep (se 1 (by rfl) ⟨8260349, by rfl⟩ : syracuseStep 11013799 = 16520699) B16520699
theorem B14685065 : Blo 2259435 14685065 := bstep (se 2 (by rfl) ⟨5506899, by rfl⟩ : syracuseStep 14685065 = 11013799) B11013799
theorem B9790043 : Blo 2259435 9790043 := bstep (se 1 (by rfl) ⟨7342532, by rfl⟩ : syracuseStep 9790043 = 14685065) B14685065
theorem B26106781 : Blo 2259435 26106781 := bstep (se 3 (by rfl) ⟨4895021, by rfl⟩ : syracuseStep 26106781 = 9790043) B9790043
theorem B34809041 : Blo 2259435 34809041 := bstep (se 2 (by rfl) ⟨13053390, by rfl⟩ : syracuseStep 34809041 = 26106781) B26106781
theorem B23206027 : Blo 2259435 23206027 := bstep (se 1 (by rfl) ⟨17404520, by rfl⟩ : syracuseStep 23206027 = 34809041) B34809041
theorem B30941369 : Blo 2259435 30941369 := bstep (se 2 (by rfl) ⟨11603013, by rfl⟩ : syracuseStep 30941369 = 23206027) B23206027
theorem B20627579 : Blo 2259435 20627579 := bstep (se 1 (by rfl) ⟨15470684, by rfl⟩ : syracuseStep 20627579 = 30941369) B30941369
theorem B55006877 : Blo 2259435 55006877 := bstep (se 3 (by rfl) ⟨10313789, by rfl⟩ : syracuseStep 55006877 = 20627579) B20627579
theorem B36671251 : Blo 2259435 36671251 := bstep (se 1 (by rfl) ⟨27503438, by rfl⟩ : syracuseStep 36671251 = 55006877) B55006877
theorem B48895001 : Blo 2259435 48895001 := bstep (se 2 (by rfl) ⟨18335625, by rfl⟩ : syracuseStep 48895001 = 36671251) B36671251
theorem B32596667 : Blo 2259435 32596667 := bstep (se 1 (by rfl) ⟨24447500, by rfl⟩ : syracuseStep 32596667 = 48895001) B48895001
theorem B21731111 : Blo 2259435 21731111 := bstep (se 1 (by rfl) ⟨16298333, by rfl⟩ : syracuseStep 21731111 = 32596667) B32596667
theorem B14487407 : Blo 2259435 14487407 := bstep (se 1 (by rfl) ⟨10865555, by rfl⟩ : syracuseStep 14487407 = 21731111) B21731111
theorem B9658271 : Blo 2259435 9658271 := bstep (se 1 (by rfl) ⟨7243703, by rfl⟩ : syracuseStep 9658271 = 14487407) B14487407
theorem B6438847 : Blo 2259435 6438847 := bstep (se 1 (by rfl) ⟨4829135, by rfl⟩ : syracuseStep 6438847 = 9658271) B9658271
theorem B8585129 : Blo 2259435 8585129 := bstep (se 2 (by rfl) ⟨3219423, by rfl⟩ : syracuseStep 8585129 = 6438847) B6438847
theorem B5723419 : Blo 2259435 5723419 := bstep (se 1 (by rfl) ⟨4292564, by rfl⟩ : syracuseStep 5723419 = 8585129) B8585129
theorem B7631225 : Blo 2259435 7631225 := bstep (se 2 (by rfl) ⟨2861709, by rfl⟩ : syracuseStep 7631225 = 5723419) B5723419
theorem B5087483 : Blo 2259435 5087483 := bstep (se 1 (by rfl) ⟨3815612, by rfl⟩ : syracuseStep 5087483 = 7631225) B7631225
theorem B3391655 : Blo 2259435 3391655 := bstep (se 1 (by rfl) ⟨2543741, by rfl⟩ : syracuseStep 3391655 = 5087483) B5087483
theorem B2261103 : Blo 2259435 2261103 := bstep (se 1 (by rfl) ⟨1695827, by rfl⟩ : syracuseStep 2261103 = 3391655) B3391655
theorem B3391661 : Blo 2259435 3391661 := bbase (se 3 (by rfl) ⟨635936, by rfl⟩ : syracuseStep 3391661 = 1271873) (by norm_num)
theorem B2261107 : Blo 2259435 2261107 := bstep (se 1 (by rfl) ⟨1695830, by rfl⟩ : syracuseStep 2261107 = 3391661) B3391661
theorem B5087501 : Blo 2259435 5087501 := bbase (se 3 (by rfl) ⟨953906, by rfl⟩ : syracuseStep 5087501 = 1907813) (by norm_num)
theorem B3391667 : Blo 2259435 3391667 := bstep (se 1 (by rfl) ⟨2543750, by rfl⟩ : syracuseStep 3391667 = 5087501) B5087501
theorem B2261111 : Blo 2259435 2261111 := bstep (se 1 (by rfl) ⟨1695833, by rfl⟩ : syracuseStep 2261111 = 3391667) B3391667
theorem B2861725 : Blo 2259435 2861725 := bbase (se 3 (by rfl) ⟨536573, by rfl⟩ : syracuseStep 2861725 = 1073147) (by norm_num)
theorem B3815633 : Blo 2259435 3815633 := bstep (se 2 (by rfl) ⟨1430862, by rfl⟩ : syracuseStep 3815633 = 2861725) B2861725
theorem B2543755 : Blo 2259435 2543755 := bstep (se 1 (by rfl) ⟨1907816, by rfl⟩ : syracuseStep 2543755 = 3815633) B3815633
theorem B3391673 : Blo 2259435 3391673 := bstep (se 2 (by rfl) ⟨1271877, by rfl⟩ : syracuseStep 3391673 = 2543755) B2543755
theorem B2261115 : Blo 2259435 2261115 := bstep (se 1 (by rfl) ⟨1695836, by rfl⟩ : syracuseStep 2261115 = 3391673) B3391673
theorem B3621877 : Blo 2259435 3621877 := bbase (se 5 (by rfl) ⟨169775, by rfl⟩ : syracuseStep 3621877 = 339551) (by norm_num)
theorem B19316677 : Blo 2259435 19316677 := bstep (se 4 (by rfl) ⟨1810938, by rfl⟩ : syracuseStep 19316677 = 3621877) B3621877
theorem B25755569 : Blo 2259435 25755569 := bstep (se 2 (by rfl) ⟨9658338, by rfl⟩ : syracuseStep 25755569 = 19316677) B19316677
theorem B17170379 : Blo 2259435 17170379 := bstep (se 1 (by rfl) ⟨12877784, by rfl⟩ : syracuseStep 17170379 = 25755569) B25755569
theorem B11446919 : Blo 2259435 11446919 := bstep (se 1 (by rfl) ⟨8585189, by rfl⟩ : syracuseStep 11446919 = 17170379) B17170379
theorem B7631279 : Blo 2259435 7631279 := bstep (se 1 (by rfl) ⟨5723459, by rfl⟩ : syracuseStep 7631279 = 11446919) B11446919
theorem B5087519 : Blo 2259435 5087519 := bstep (se 1 (by rfl) ⟨3815639, by rfl⟩ : syracuseStep 5087519 = 7631279) B7631279
theorem B3391679 : Blo 2259435 3391679 := bstep (se 1 (by rfl) ⟨2543759, by rfl⟩ : syracuseStep 3391679 = 5087519) B5087519
theorem B2261119 : Blo 2259435 2261119 := bstep (se 1 (by rfl) ⟨1695839, by rfl⟩ : syracuseStep 2261119 = 3391679) B3391679
theorem B3391685 : Blo 2259435 3391685 := bbase (se 4 (by rfl) ⟨317970, by rfl⟩ : syracuseStep 3391685 = 635941) (by norm_num)
theorem B2261123 : Blo 2259435 2261123 := bstep (se 1 (by rfl) ⟨1695842, by rfl⟩ : syracuseStep 2261123 = 3391685) B3391685
theorem B3815653 : Blo 2259435 3815653 := bbase (se 4 (by rfl) ⟨357717, by rfl⟩ : syracuseStep 3815653 = 715435) (by norm_num)
theorem B5087537 : Blo 2259435 5087537 := bstep (se 2 (by rfl) ⟨1907826, by rfl⟩ : syracuseStep 5087537 = 3815653) B3815653
theorem B3391691 : Blo 2259435 3391691 := bstep (se 1 (by rfl) ⟨2543768, by rfl⟩ : syracuseStep 3391691 = 5087537) B5087537
theorem B2261127 : Blo 2259435 2261127 := bstep (se 1 (by rfl) ⟨1695845, by rfl⟩ : syracuseStep 2261127 = 3391691) B3391691
theorem B2543773 : Blo 2259435 2543773 := bbase (se 3 (by rfl) ⟨476957, by rfl⟩ : syracuseStep 2543773 = 953915) (by norm_num)
theorem B3391697 : Blo 2259435 3391697 := bstep (se 2 (by rfl) ⟨1271886, by rfl⟩ : syracuseStep 3391697 = 2543773) B2543773
theorem B2261131 : Blo 2259435 2261131 := bstep (se 1 (by rfl) ⟨1695848, by rfl⟩ : syracuseStep 2261131 = 3391697) B3391697
theorem B7631333 : Blo 2259435 7631333 := bbase (se 4 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 7631333 = 1430875) (by norm_num)
theorem B5087555 : Blo 2259435 5087555 := bstep (se 1 (by rfl) ⟨3815666, by rfl⟩ : syracuseStep 5087555 = 7631333) B7631333
theorem B3391703 : Blo 2259435 3391703 := bstep (se 1 (by rfl) ⟨2543777, by rfl⟩ : syracuseStep 3391703 = 5087555) B5087555
theorem B2261135 : Blo 2259435 2261135 := bstep (se 1 (by rfl) ⟨1695851, by rfl⟩ : syracuseStep 2261135 = 3391703) B3391703
theorem B3391709 : Blo 2259435 3391709 := bbase (se 3 (by rfl) ⟨635945, by rfl⟩ : syracuseStep 3391709 = 1271891) (by norm_num)
theorem B2261139 : Blo 2259435 2261139 := bstep (se 1 (by rfl) ⟨1695854, by rfl⟩ : syracuseStep 2261139 = 3391709) B3391709
theorem B5087573 : Blo 2259435 5087573 := bbase (se 10 (by rfl) ⟨7452, by rfl⟩ : syracuseStep 5087573 = 14905) (by norm_num)
theorem B3391715 : Blo 2259435 3391715 := bstep (se 1 (by rfl) ⟨2543786, by rfl⟩ : syracuseStep 3391715 = 5087573) B5087573
theorem B2261143 : Blo 2259435 2261143 := bstep (se 1 (by rfl) ⟨1695857, by rfl⟩ : syracuseStep 2261143 = 3391715) B3391715
theorem B5432885 : Blo 2259435 5432885 := bbase (se 5 (by rfl) ⟨254666, by rfl⟩ : syracuseStep 5432885 = 509333) (by norm_num)
theorem B3621923 : Blo 2259435 3621923 := bstep (se 1 (by rfl) ⟨2716442, by rfl⟩ : syracuseStep 3621923 = 5432885) B5432885
theorem B2414615 : Blo 2259435 2414615 := bstep (se 1 (by rfl) ⟨1810961, by rfl⟩ : syracuseStep 2414615 = 3621923) B3621923
theorem B6438973 : Blo 2259435 6438973 := bstep (se 3 (by rfl) ⟨1207307, by rfl⟩ : syracuseStep 6438973 = 2414615) B2414615
theorem B8585297 : Blo 2259435 8585297 := bstep (se 2 (by rfl) ⟨3219486, by rfl⟩ : syracuseStep 8585297 = 6438973) B6438973
theorem B5723531 : Blo 2259435 5723531 := bstep (se 1 (by rfl) ⟨4292648, by rfl⟩ : syracuseStep 5723531 = 8585297) B8585297
theorem B3815687 : Blo 2259435 3815687 := bstep (se 1 (by rfl) ⟨2861765, by rfl⟩ : syracuseStep 3815687 = 5723531) B5723531
theorem B2543791 : Blo 2259435 2543791 := bstep (se 1 (by rfl) ⟨1907843, by rfl⟩ : syracuseStep 2543791 = 3815687) B3815687
theorem B3391721 : Blo 2259435 3391721 := bstep (se 2 (by rfl) ⟨1271895, by rfl⟩ : syracuseStep 3391721 = 2543791) B2543791
theorem B2261147 : Blo 2259435 2261147 := bstep (se 1 (by rfl) ⟨1695860, by rfl⟩ : syracuseStep 2261147 = 3391721) B3391721
theorem B2753509 : Blo 2259435 2753509 := bbase (se 4 (by rfl) ⟨258141, by rfl⟩ : syracuseStep 2753509 = 516283) (by norm_num)
theorem B3671345 : Blo 2259435 3671345 := bstep (se 2 (by rfl) ⟨1376754, by rfl⟩ : syracuseStep 3671345 = 2753509) B2753509
theorem B9790253 : Blo 2259435 9790253 := bstep (se 3 (by rfl) ⟨1835672, by rfl⟩ : syracuseStep 9790253 = 3671345) B3671345
theorem B6526835 : Blo 2259435 6526835 := bstep (se 1 (by rfl) ⟨4895126, by rfl⟩ : syracuseStep 6526835 = 9790253) B9790253
theorem B4351223 : Blo 2259435 4351223 := bstep (se 1 (by rfl) ⟨3263417, by rfl⟩ : syracuseStep 4351223 = 6526835) B6526835
theorem B2900815 : Blo 2259435 2900815 := bstep (se 1 (by rfl) ⟨2175611, by rfl⟩ : syracuseStep 2900815 = 4351223) B4351223
theorem B15471013 : Blo 2259435 15471013 := bstep (se 4 (by rfl) ⟨1450407, by rfl⟩ : syracuseStep 15471013 = 2900815) B2900815
theorem B20628017 : Blo 2259435 20628017 := bstep (se 2 (by rfl) ⟨7735506, by rfl⟩ : syracuseStep 20628017 = 15471013) B15471013
theorem B13752011 : Blo 2259435 13752011 := bstep (se 1 (by rfl) ⟨10314008, by rfl⟩ : syracuseStep 13752011 = 20628017) B20628017
theorem B9168007 : Blo 2259435 9168007 := bstep (se 1 (by rfl) ⟨6876005, by rfl⟩ : syracuseStep 9168007 = 13752011) B13752011
theorem B12224009 : Blo 2259435 12224009 := bstep (se 2 (by rfl) ⟨4584003, by rfl⟩ : syracuseStep 12224009 = 9168007) B9168007
theorem B8149339 : Blo 2259435 8149339 := bstep (se 1 (by rfl) ⟨6112004, by rfl⟩ : syracuseStep 8149339 = 12224009) B12224009
theorem B43463141 : Blo 2259435 43463141 := bstep (se 4 (by rfl) ⟨4074669, by rfl⟩ : syracuseStep 43463141 = 8149339) B8149339
theorem B28975427 : Blo 2259435 28975427 := bstep (se 1 (by rfl) ⟨21731570, by rfl⟩ : syracuseStep 28975427 = 43463141) B43463141
theorem B19316951 : Blo 2259435 19316951 := bstep (se 1 (by rfl) ⟨14487713, by rfl⟩ : syracuseStep 19316951 = 28975427) B28975427
theorem B12877967 : Blo 2259435 12877967 := bstep (se 1 (by rfl) ⟨9658475, by rfl⟩ : syracuseStep 12877967 = 19316951) B19316951
theorem B8585311 : Blo 2259435 8585311 := bstep (se 1 (by rfl) ⟨6438983, by rfl⟩ : syracuseStep 8585311 = 12877967) B12877967
theorem B11447081 : Blo 2259435 11447081 := bstep (se 2 (by rfl) ⟨4292655, by rfl⟩ : syracuseStep 11447081 = 8585311) B8585311
theorem B7631387 : Blo 2259435 7631387 := bstep (se 1 (by rfl) ⟨5723540, by rfl⟩ : syracuseStep 7631387 = 11447081) B11447081
theorem B5087591 : Blo 2259435 5087591 := bstep (se 1 (by rfl) ⟨3815693, by rfl⟩ : syracuseStep 5087591 = 7631387) B7631387
theorem B3391727 : Blo 2259435 3391727 := bstep (se 1 (by rfl) ⟨2543795, by rfl⟩ : syracuseStep 3391727 = 5087591) B5087591
theorem B2261151 : Blo 2259435 2261151 := bstep (se 1 (by rfl) ⟨1695863, by rfl⟩ : syracuseStep 2261151 = 3391727) B3391727
theorem B3391733 : Blo 2259435 3391733 := bbase (se 5 (by rfl) ⟨158987, by rfl⟩ : syracuseStep 3391733 = 317975) (by norm_num)
theorem B2261155 : Blo 2259435 2261155 := bstep (se 1 (by rfl) ⟨1695866, by rfl⟩ : syracuseStep 2261155 = 3391733) B3391733
theorem B2480965 : Blo 2259435 2480965 := bbase (se 4 (by rfl) ⟨232590, by rfl⟩ : syracuseStep 2480965 = 465181) (by norm_num)
theorem B13231813 : Blo 2259435 13231813 := bstep (se 4 (by rfl) ⟨1240482, by rfl⟩ : syracuseStep 13231813 = 2480965) B2480965
theorem B17642417 : Blo 2259435 17642417 := bstep (se 2 (by rfl) ⟨6615906, by rfl⟩ : syracuseStep 17642417 = 13231813) B13231813
theorem B188185781 : Blo 2259435 188185781 := bstep (se 5 (by rfl) ⟨8821208, by rfl⟩ : syracuseStep 188185781 = 17642417) B17642417
theorem B125457187 : Blo 2259435 125457187 := bstep (se 1 (by rfl) ⟨94092890, by rfl⟩ : syracuseStep 125457187 = 188185781) B188185781
theorem B167276249 : Blo 2259435 167276249 := bstep (se 2 (by rfl) ⟨62728593, by rfl⟩ : syracuseStep 167276249 = 125457187) B125457187
theorem B111517499 : Blo 2259435 111517499 := bstep (se 1 (by rfl) ⟨83638124, by rfl⟩ : syracuseStep 111517499 = 167276249) B167276249
theorem B74344999 : Blo 2259435 74344999 := bstep (se 1 (by rfl) ⟨55758749, by rfl⟩ : syracuseStep 74344999 = 111517499) B111517499
theorem B99126665 : Blo 2259435 99126665 := bstep (se 2 (by rfl) ⟨37172499, by rfl⟩ : syracuseStep 99126665 = 74344999) B74344999
theorem B66084443 : Blo 2259435 66084443 := bstep (se 1 (by rfl) ⟨49563332, by rfl⟩ : syracuseStep 66084443 = 99126665) B99126665
theorem B44056295 : Blo 2259435 44056295 := bstep (se 1 (by rfl) ⟨33042221, by rfl⟩ : syracuseStep 44056295 = 66084443) B66084443
theorem B29370863 : Blo 2259435 29370863 := bstep (se 1 (by rfl) ⟨22028147, by rfl⟩ : syracuseStep 29370863 = 44056295) B44056295
theorem B78322301 : Blo 2259435 78322301 := bstep (se 3 (by rfl) ⟨14685431, by rfl⟩ : syracuseStep 78322301 = 29370863) B29370863
theorem B52214867 : Blo 2259435 52214867 := bstep (se 1 (by rfl) ⟨39161150, by rfl⟩ : syracuseStep 52214867 = 78322301) B78322301
theorem B34809911 : Blo 2259435 34809911 := bstep (se 1 (by rfl) ⟨26107433, by rfl⟩ : syracuseStep 34809911 = 52214867) B52214867
theorem B23206607 : Blo 2259435 23206607 := bstep (se 1 (by rfl) ⟨17404955, by rfl⟩ : syracuseStep 23206607 = 34809911) B34809911
theorem B15471071 : Blo 2259435 15471071 := bstep (se 1 (by rfl) ⟨11603303, by rfl⟩ : syracuseStep 15471071 = 23206607) B23206607
theorem B10314047 : Blo 2259435 10314047 := bstep (se 1 (by rfl) ⟨7735535, by rfl⟩ : syracuseStep 10314047 = 15471071) B15471071
theorem B6876031 : Blo 2259435 6876031 := bstep (se 1 (by rfl) ⟨5157023, by rfl⟩ : syracuseStep 6876031 = 10314047) B10314047
theorem B9168041 : Blo 2259435 9168041 := bstep (se 2 (by rfl) ⟨3438015, by rfl⟩ : syracuseStep 9168041 = 6876031) B6876031
theorem B6112027 : Blo 2259435 6112027 := bstep (se 1 (by rfl) ⟨4584020, by rfl⟩ : syracuseStep 6112027 = 9168041) B9168041
theorem B32597477 : Blo 2259435 32597477 := bstep (se 4 (by rfl) ⟨3056013, by rfl⟩ : syracuseStep 32597477 = 6112027) B6112027
theorem B21731651 : Blo 2259435 21731651 := bstep (se 1 (by rfl) ⟨16298738, by rfl⟩ : syracuseStep 21731651 = 32597477) B32597477
theorem B14487767 : Blo 2259435 14487767 := bstep (se 1 (by rfl) ⟨10865825, by rfl⟩ : syracuseStep 14487767 = 21731651) B21731651
theorem B9658511 : Blo 2259435 9658511 := bstep (se 1 (by rfl) ⟨7243883, by rfl⟩ : syracuseStep 9658511 = 14487767) B14487767
theorem B6439007 : Blo 2259435 6439007 := bstep (se 1 (by rfl) ⟨4829255, by rfl⟩ : syracuseStep 6439007 = 9658511) B9658511
theorem B4292671 : Blo 2259435 4292671 := bstep (se 1 (by rfl) ⟨3219503, by rfl⟩ : syracuseStep 4292671 = 6439007) B6439007
theorem B5723561 : Blo 2259435 5723561 := bstep (se 2 (by rfl) ⟨2146335, by rfl⟩ : syracuseStep 5723561 = 4292671) B4292671
theorem B3815707 : Blo 2259435 3815707 := bstep (se 1 (by rfl) ⟨2861780, by rfl⟩ : syracuseStep 3815707 = 5723561) B5723561
theorem B5087609 : Blo 2259435 5087609 := bstep (se 2 (by rfl) ⟨1907853, by rfl⟩ : syracuseStep 5087609 = 3815707) B3815707
theorem B3391739 : Blo 2259435 3391739 := bstep (se 1 (by rfl) ⟨2543804, by rfl⟩ : syracuseStep 3391739 = 5087609) B5087609
theorem B2261159 : Blo 2259435 2261159 := bstep (se 1 (by rfl) ⟨1695869, by rfl⟩ : syracuseStep 2261159 = 3391739) B3391739
theorem B2543809 : Blo 2259435 2543809 := bbase (se 2 (by rfl) ⟨953928, by rfl⟩ : syracuseStep 2543809 = 1907857) (by norm_num)
theorem B3391745 : Blo 2259435 3391745 := bstep (se 2 (by rfl) ⟨1271904, by rfl⟩ : syracuseStep 3391745 = 2543809) B2543809
theorem B2261163 : Blo 2259435 2261163 := bstep (se 1 (by rfl) ⟨1695872, by rfl⟩ : syracuseStep 2261163 = 3391745) B3391745
theorem B5723581 : Blo 2259435 5723581 := bbase (se 3 (by rfl) ⟨1073171, by rfl⟩ : syracuseStep 5723581 = 2146343) (by norm_num)
theorem B7631441 : Blo 2259435 7631441 := bstep (se 2 (by rfl) ⟨2861790, by rfl⟩ : syracuseStep 7631441 = 5723581) B5723581
theorem B5087627 : Blo 2259435 5087627 := bstep (se 1 (by rfl) ⟨3815720, by rfl⟩ : syracuseStep 5087627 = 7631441) B7631441
theorem B3391751 : Blo 2259435 3391751 := bstep (se 1 (by rfl) ⟨2543813, by rfl⟩ : syracuseStep 3391751 = 5087627) B5087627
theorem B2261167 : Blo 2259435 2261167 := bstep (se 1 (by rfl) ⟨1695875, by rfl⟩ : syracuseStep 2261167 = 3391751) B3391751
theorem B3391757 : Blo 2259435 3391757 := bbase (se 3 (by rfl) ⟨635954, by rfl⟩ : syracuseStep 3391757 = 1271909) (by norm_num)
theorem B2261171 : Blo 2259435 2261171 := bstep (se 1 (by rfl) ⟨1695878, by rfl⟩ : syracuseStep 2261171 = 3391757) B3391757
theorem B5087645 : Blo 2259435 5087645 := bbase (se 3 (by rfl) ⟨953933, by rfl⟩ : syracuseStep 5087645 = 1907867) (by norm_num)
theorem B3391763 : Blo 2259435 3391763 := bstep (se 1 (by rfl) ⟨2543822, by rfl⟩ : syracuseStep 3391763 = 5087645) B5087645
theorem B2261175 : Blo 2259435 2261175 := bstep (se 1 (by rfl) ⟨1695881, by rfl⟩ : syracuseStep 2261175 = 3391763) B3391763
theorem B3815741 : Blo 2259435 3815741 := bbase (se 3 (by rfl) ⟨715451, by rfl⟩ : syracuseStep 3815741 = 1430903) (by norm_num)
theorem B2543827 : Blo 2259435 2543827 := bstep (se 1 (by rfl) ⟨1907870, by rfl⟩ : syracuseStep 2543827 = 3815741) B3815741
theorem B3391769 : Blo 2259435 3391769 := bstep (se 2 (by rfl) ⟨1271913, by rfl⟩ : syracuseStep 3391769 = 2543827) B2543827
theorem B2261179 : Blo 2259435 2261179 := bstep (se 1 (by rfl) ⟨1695884, by rfl⟩ : syracuseStep 2261179 = 3391769) B3391769
theorem B2414653 : Blo 2259435 2414653 := bbase (se 3 (by rfl) ⟨452747, by rfl⟩ : syracuseStep 2414653 = 905495) (by norm_num)
theorem B12878149 : Blo 2259435 12878149 := bstep (se 4 (by rfl) ⟨1207326, by rfl⟩ : syracuseStep 12878149 = 2414653) B2414653
theorem B17170865 : Blo 2259435 17170865 := bstep (se 2 (by rfl) ⟨6439074, by rfl⟩ : syracuseStep 17170865 = 12878149) B12878149
theorem B11447243 : Blo 2259435 11447243 := bstep (se 1 (by rfl) ⟨8585432, by rfl⟩ : syracuseStep 11447243 = 17170865) B17170865
theorem B7631495 : Blo 2259435 7631495 := bstep (se 1 (by rfl) ⟨5723621, by rfl⟩ : syracuseStep 7631495 = 11447243) B11447243
theorem B5087663 : Blo 2259435 5087663 := bstep (se 1 (by rfl) ⟨3815747, by rfl⟩ : syracuseStep 5087663 = 7631495) B7631495
theorem B3391775 : Blo 2259435 3391775 := bstep (se 1 (by rfl) ⟨2543831, by rfl⟩ : syracuseStep 3391775 = 5087663) B5087663
theorem B2261183 : Blo 2259435 2261183 := bstep (se 1 (by rfl) ⟨1695887, by rfl⟩ : syracuseStep 2261183 = 3391775) B3391775
theorem B3391781 : Blo 2259435 3391781 := bbase (se 4 (by rfl) ⟨317979, by rfl⟩ : syracuseStep 3391781 = 635959) (by norm_num)
theorem B2261187 : Blo 2259435 2261187 := bstep (se 1 (by rfl) ⟨1695890, by rfl⟩ : syracuseStep 2261187 = 3391781) B3391781
theorem B2861821 : Blo 2259435 2861821 := bbase (se 3 (by rfl) ⟨536591, by rfl⟩ : syracuseStep 2861821 = 1073183) (by norm_num)
theorem B3815761 : Blo 2259435 3815761 := bstep (se 2 (by rfl) ⟨1430910, by rfl⟩ : syracuseStep 3815761 = 2861821) B2861821
theorem B5087681 : Blo 2259435 5087681 := bstep (se 2 (by rfl) ⟨1907880, by rfl⟩ : syracuseStep 5087681 = 3815761) B3815761
theorem B3391787 : Blo 2259435 3391787 := bstep (se 1 (by rfl) ⟨2543840, by rfl⟩ : syracuseStep 3391787 = 5087681) B5087681
theorem B2261191 : Blo 2259435 2261191 := bstep (se 1 (by rfl) ⟨1695893, by rfl⟩ : syracuseStep 2261191 = 3391787) B3391787
theorem B2543845 : Blo 2259435 2543845 := bbase (se 4 (by rfl) ⟨238485, by rfl⟩ : syracuseStep 2543845 = 476971) (by norm_num)
theorem B3391793 : Blo 2259435 3391793 := bstep (se 2 (by rfl) ⟨1271922, by rfl⟩ : syracuseStep 3391793 = 2543845) B2543845
theorem B2261195 : Blo 2259435 2261195 := bstep (se 1 (by rfl) ⟨1695896, by rfl⟩ : syracuseStep 2261195 = 3391793) B3391793
theorem B4829341 : Blo 2259435 4829341 := bbase (se 3 (by rfl) ⟨905501, by rfl⟩ : syracuseStep 4829341 = 1811003) (by norm_num)
theorem B6439121 : Blo 2259435 6439121 := bstep (se 2 (by rfl) ⟨2414670, by rfl⟩ : syracuseStep 6439121 = 4829341) B4829341
theorem B4292747 : Blo 2259435 4292747 := bstep (se 1 (by rfl) ⟨3219560, by rfl⟩ : syracuseStep 4292747 = 6439121) B6439121
theorem B2861831 : Blo 2259435 2861831 := bstep (se 1 (by rfl) ⟨2146373, by rfl⟩ : syracuseStep 2861831 = 4292747) B4292747
theorem B7631549 : Blo 2259435 7631549 := bstep (se 3 (by rfl) ⟨1430915, by rfl⟩ : syracuseStep 7631549 = 2861831) B2861831
theorem B5087699 : Blo 2259435 5087699 := bstep (se 1 (by rfl) ⟨3815774, by rfl⟩ : syracuseStep 5087699 = 7631549) B7631549
theorem B3391799 : Blo 2259435 3391799 := bstep (se 1 (by rfl) ⟨2543849, by rfl⟩ : syracuseStep 3391799 = 5087699) B5087699
theorem B2261199 : Blo 2259435 2261199 := bstep (se 1 (by rfl) ⟨1695899, by rfl⟩ : syracuseStep 2261199 = 3391799) B3391799
theorem B3391805 : Blo 2259435 3391805 := bbase (se 3 (by rfl) ⟨635963, by rfl⟩ : syracuseStep 3391805 = 1271927) (by norm_num)
theorem B2261203 : Blo 2259435 2261203 := bstep (se 1 (by rfl) ⟨1695902, by rfl⟩ : syracuseStep 2261203 = 3391805) B3391805
theorem B5087717 : Blo 2259435 5087717 := bbase (se 4 (by rfl) ⟨476973, by rfl⟩ : syracuseStep 5087717 = 953947) (by norm_num)
theorem B3391811 : Blo 2259435 3391811 := bstep (se 1 (by rfl) ⟨2543858, by rfl⟩ : syracuseStep 3391811 = 5087717) B5087717
theorem B2261207 : Blo 2259435 2261207 := bstep (se 1 (by rfl) ⟨1695905, by rfl⟩ : syracuseStep 2261207 = 3391811) B3391811
theorem B5723693 : Blo 2259435 5723693 := bbase (se 3 (by rfl) ⟨1073192, by rfl⟩ : syracuseStep 5723693 = 2146385) (by norm_num)
theorem B3815795 : Blo 2259435 3815795 := bstep (se 1 (by rfl) ⟨2861846, by rfl⟩ : syracuseStep 3815795 = 5723693) B5723693
theorem B2543863 : Blo 2259435 2543863 := bstep (se 1 (by rfl) ⟨1907897, by rfl⟩ : syracuseStep 2543863 = 3815795) B3815795
theorem B3391817 : Blo 2259435 3391817 := bstep (se 2 (by rfl) ⟨1271931, by rfl⟩ : syracuseStep 3391817 = 2543863) B2543863
theorem B2261211 : Blo 2259435 2261211 := bstep (se 1 (by rfl) ⟨1695908, by rfl⟩ : syracuseStep 2261211 = 3391817) B3391817
theorem B4130381 : Blo 2259435 4130381 := bbase (se 3 (by rfl) ⟨774446, by rfl⟩ : syracuseStep 4130381 = 1548893) (by norm_num)
theorem B2753587 : Blo 2259435 2753587 := bstep (se 1 (by rfl) ⟨2065190, by rfl⟩ : syracuseStep 2753587 = 4130381) B4130381
theorem B3671449 : Blo 2259435 3671449 := bstep (se 2 (by rfl) ⟨1376793, by rfl⟩ : syracuseStep 3671449 = 2753587) B2753587
theorem B19581061 : Blo 2259435 19581061 := bstep (se 4 (by rfl) ⟨1835724, by rfl⟩ : syracuseStep 19581061 = 3671449) B3671449
theorem B26108081 : Blo 2259435 26108081 := bstep (se 2 (by rfl) ⟨9790530, by rfl⟩ : syracuseStep 26108081 = 19581061) B19581061
theorem B17405387 : Blo 2259435 17405387 := bstep (se 1 (by rfl) ⟨13054040, by rfl⟩ : syracuseStep 17405387 = 26108081) B26108081
theorem B11603591 : Blo 2259435 11603591 := bstep (se 1 (by rfl) ⟨8702693, by rfl⟩ : syracuseStep 11603591 = 17405387) B17405387
theorem B7735727 : Blo 2259435 7735727 := bstep (se 1 (by rfl) ⟨5801795, by rfl⟩ : syracuseStep 7735727 = 11603591) B11603591
theorem B5157151 : Blo 2259435 5157151 := bstep (se 1 (by rfl) ⟨3867863, by rfl⟩ : syracuseStep 5157151 = 7735727) B7735727
theorem B27504805 : Blo 2259435 27504805 := bstep (se 4 (by rfl) ⟨2578575, by rfl⟩ : syracuseStep 27504805 = 5157151) B5157151
theorem B36673073 : Blo 2259435 36673073 := bstep (se 2 (by rfl) ⟨13752402, by rfl⟩ : syracuseStep 36673073 = 27504805) B27504805
theorem B24448715 : Blo 2259435 24448715 := bstep (se 1 (by rfl) ⟨18336536, by rfl⟩ : syracuseStep 24448715 = 36673073) B36673073
theorem B16299143 : Blo 2259435 16299143 := bstep (se 1 (by rfl) ⟨12224357, by rfl⟩ : syracuseStep 16299143 = 24448715) B24448715
theorem B10866095 : Blo 2259435 10866095 := bstep (se 1 (by rfl) ⟨8149571, by rfl⟩ : syracuseStep 10866095 = 16299143) B16299143
theorem B7244063 : Blo 2259435 7244063 := bstep (se 1 (by rfl) ⟨5433047, by rfl⟩ : syracuseStep 7244063 = 10866095) B10866095
theorem B4829375 : Blo 2259435 4829375 := bstep (se 1 (by rfl) ⟨3622031, by rfl⟩ : syracuseStep 4829375 = 7244063) B7244063
theorem B3219583 : Blo 2259435 3219583 := bstep (se 1 (by rfl) ⟨2414687, by rfl⟩ : syracuseStep 3219583 = 4829375) B4829375
theorem B4292777 : Blo 2259435 4292777 := bstep (se 2 (by rfl) ⟨1609791, by rfl⟩ : syracuseStep 4292777 = 3219583) B3219583
theorem B11447405 : Blo 2259435 11447405 := bstep (se 3 (by rfl) ⟨2146388, by rfl⟩ : syracuseStep 11447405 = 4292777) B4292777
theorem B7631603 : Blo 2259435 7631603 := bstep (se 1 (by rfl) ⟨5723702, by rfl⟩ : syracuseStep 7631603 = 11447405) B11447405
theorem B5087735 : Blo 2259435 5087735 := bstep (se 1 (by rfl) ⟨3815801, by rfl⟩ : syracuseStep 5087735 = 7631603) B7631603
theorem B3391823 : Blo 2259435 3391823 := bstep (se 1 (by rfl) ⟨2543867, by rfl⟩ : syracuseStep 3391823 = 5087735) B5087735
theorem B2261215 : Blo 2259435 2261215 := bstep (se 1 (by rfl) ⟨1695911, by rfl⟩ : syracuseStep 2261215 = 3391823) B3391823
theorem B3391829 : Blo 2259435 3391829 := bbase (se 10 (by rfl) ⟨4968, by rfl⟩ : syracuseStep 3391829 = 9937) (by norm_num)
theorem B2261219 : Blo 2259435 2261219 := bstep (se 1 (by rfl) ⟨1695914, by rfl⟩ : syracuseStep 2261219 = 3391829) B3391829
theorem B6439189 : Blo 2259435 6439189 := bbase (se 6 (by rfl) ⟨150918, by rfl⟩ : syracuseStep 6439189 = 301837) (by norm_num)
theorem B8585585 : Blo 2259435 8585585 := bstep (se 2 (by rfl) ⟨3219594, by rfl⟩ : syracuseStep 8585585 = 6439189) B6439189
theorem B5723723 : Blo 2259435 5723723 := bstep (se 1 (by rfl) ⟨4292792, by rfl⟩ : syracuseStep 5723723 = 8585585) B8585585
theorem B3815815 : Blo 2259435 3815815 := bstep (se 1 (by rfl) ⟨2861861, by rfl⟩ : syracuseStep 3815815 = 5723723) B5723723
theorem B5087753 : Blo 2259435 5087753 := bstep (se 2 (by rfl) ⟨1907907, by rfl⟩ : syracuseStep 5087753 = 3815815) B3815815
theorem B3391835 : Blo 2259435 3391835 := bstep (se 1 (by rfl) ⟨2543876, by rfl⟩ : syracuseStep 3391835 = 5087753) B5087753
theorem B2261223 : Blo 2259435 2261223 := bstep (se 1 (by rfl) ⟨1695917, by rfl⟩ : syracuseStep 2261223 = 3391835) B3391835
theorem B2543881 : Blo 2259435 2543881 := bbase (se 2 (by rfl) ⟨953955, by rfl⟩ : syracuseStep 2543881 = 1907911) (by norm_num)
theorem B3391841 : Blo 2259435 3391841 := bstep (se 2 (by rfl) ⟨1271940, by rfl⟩ : syracuseStep 3391841 = 2543881) B2543881
theorem B2261227 : Blo 2259435 2261227 := bstep (se 1 (by rfl) ⟨1695920, by rfl⟩ : syracuseStep 2261227 = 3391841) B3391841
theorem B5433085 : Blo 2259435 5433085 := bbase (se 3 (by rfl) ⟨1018703, by rfl⟩ : syracuseStep 5433085 = 2037407) (by norm_num)
theorem B28976453 : Blo 2259435 28976453 := bstep (se 4 (by rfl) ⟨2716542, by rfl⟩ : syracuseStep 28976453 = 5433085) B5433085
theorem B19317635 : Blo 2259435 19317635 := bstep (se 1 (by rfl) ⟨14488226, by rfl⟩ : syracuseStep 19317635 = 28976453) B28976453
theorem B12878423 : Blo 2259435 12878423 := bstep (se 1 (by rfl) ⟨9658817, by rfl⟩ : syracuseStep 12878423 = 19317635) B19317635
theorem B8585615 : Blo 2259435 8585615 := bstep (se 1 (by rfl) ⟨6439211, by rfl⟩ : syracuseStep 8585615 = 12878423) B12878423
theorem B5723743 : Blo 2259435 5723743 := bstep (se 1 (by rfl) ⟨4292807, by rfl⟩ : syracuseStep 5723743 = 8585615) B8585615
theorem B7631657 : Blo 2259435 7631657 := bstep (se 2 (by rfl) ⟨2861871, by rfl⟩ : syracuseStep 7631657 = 5723743) B5723743
theorem B5087771 : Blo 2259435 5087771 := bstep (se 1 (by rfl) ⟨3815828, by rfl⟩ : syracuseStep 5087771 = 7631657) B7631657
theorem B3391847 : Blo 2259435 3391847 := bstep (se 1 (by rfl) ⟨2543885, by rfl⟩ : syracuseStep 3391847 = 5087771) B5087771
theorem B2261231 : Blo 2259435 2261231 := bstep (se 1 (by rfl) ⟨1695923, by rfl⟩ : syracuseStep 2261231 = 3391847) B3391847
theorem B3391853 : Blo 2259435 3391853 := bbase (se 3 (by rfl) ⟨635972, by rfl⟩ : syracuseStep 3391853 = 1271945) (by norm_num)
theorem B2261235 : Blo 2259435 2261235 := bstep (se 1 (by rfl) ⟨1695926, by rfl⟩ : syracuseStep 2261235 = 3391853) B3391853
theorem B5087789 : Blo 2259435 5087789 := bbase (se 3 (by rfl) ⟨953960, by rfl⟩ : syracuseStep 5087789 = 1907921) (by norm_num)
theorem B3391859 : Blo 2259435 3391859 := bstep (se 1 (by rfl) ⟨2543894, by rfl⟩ : syracuseStep 3391859 = 5087789) B5087789
theorem B2261239 : Blo 2259435 2261239 := bstep (se 1 (by rfl) ⟨1695929, by rfl⟩ : syracuseStep 2261239 = 3391859) B3391859
theorem B7443173 : Blo 2259435 7443173 := bbase (se 4 (by rfl) ⟨697797, by rfl⟩ : syracuseStep 7443173 = 1395595) (by norm_num)
theorem B4962115 : Blo 2259435 4962115 := bstep (se 1 (by rfl) ⟨3721586, by rfl⟩ : syracuseStep 4962115 = 7443173) B7443173
theorem B6616153 : Blo 2259435 6616153 := bstep (se 2 (by rfl) ⟨2481057, by rfl⟩ : syracuseStep 6616153 = 4962115) B4962115
theorem B8821537 : Blo 2259435 8821537 := bstep (se 2 (by rfl) ⟨3308076, by rfl⟩ : syracuseStep 8821537 = 6616153) B6616153
theorem B47048197 : Blo 2259435 47048197 := bstep (se 4 (by rfl) ⟨4410768, by rfl⟩ : syracuseStep 47048197 = 8821537) B8821537
theorem B62730929 : Blo 2259435 62730929 := bstep (se 2 (by rfl) ⟨23524098, by rfl⟩ : syracuseStep 62730929 = 47048197) B47048197
theorem B41820619 : Blo 2259435 41820619 := bstep (se 1 (by rfl) ⟨31365464, by rfl⟩ : syracuseStep 41820619 = 62730929) B62730929
theorem B55760825 : Blo 2259435 55760825 := bstep (se 2 (by rfl) ⟨20910309, by rfl⟩ : syracuseStep 55760825 = 41820619) B41820619
theorem B148695533 : Blo 2259435 148695533 := bstep (se 3 (by rfl) ⟨27880412, by rfl⟩ : syracuseStep 148695533 = 55760825) B55760825
theorem B99130355 : Blo 2259435 99130355 := bstep (se 1 (by rfl) ⟨74347766, by rfl⟩ : syracuseStep 99130355 = 148695533) B148695533
theorem B66086903 : Blo 2259435 66086903 := bstep (se 1 (by rfl) ⟨49565177, by rfl⟩ : syracuseStep 66086903 = 99130355) B99130355
theorem B44057935 : Blo 2259435 44057935 := bstep (se 1 (by rfl) ⟨33043451, by rfl⟩ : syracuseStep 44057935 = 66086903) B66086903
theorem B234975653 : Blo 2259435 234975653 := bstep (se 4 (by rfl) ⟨22028967, by rfl⟩ : syracuseStep 234975653 = 44057935) B44057935
theorem B156650435 : Blo 2259435 156650435 := bstep (se 1 (by rfl) ⟨117487826, by rfl⟩ : syracuseStep 156650435 = 234975653) B234975653
theorem B104433623 : Blo 2259435 104433623 := bstep (se 1 (by rfl) ⟨78325217, by rfl⟩ : syracuseStep 104433623 = 156650435) B156650435
theorem B69622415 : Blo 2259435 69622415 := bstep (se 1 (by rfl) ⟨52216811, by rfl⟩ : syracuseStep 69622415 = 104433623) B104433623
theorem B46414943 : Blo 2259435 46414943 := bstep (se 1 (by rfl) ⟨34811207, by rfl⟩ : syracuseStep 46414943 = 69622415) B69622415
theorem B30943295 : Blo 2259435 30943295 := bstep (se 1 (by rfl) ⟨23207471, by rfl⟩ : syracuseStep 30943295 = 46414943) B46414943
theorem B20628863 : Blo 2259435 20628863 := bstep (se 1 (by rfl) ⟨15471647, by rfl⟩ : syracuseStep 20628863 = 30943295) B30943295
theorem B13752575 : Blo 2259435 13752575 := bstep (se 1 (by rfl) ⟨10314431, by rfl⟩ : syracuseStep 13752575 = 20628863) B20628863
theorem B9168383 : Blo 2259435 9168383 := bstep (se 1 (by rfl) ⟨6876287, by rfl⟩ : syracuseStep 9168383 = 13752575) B13752575
theorem B6112255 : Blo 2259435 6112255 := bstep (se 1 (by rfl) ⟨4584191, by rfl⟩ : syracuseStep 6112255 = 9168383) B9168383
theorem B8149673 : Blo 2259435 8149673 := bstep (se 2 (by rfl) ⟨3056127, by rfl⟩ : syracuseStep 8149673 = 6112255) B6112255
theorem B21732461 : Blo 2259435 21732461 := bstep (se 3 (by rfl) ⟨4074836, by rfl⟩ : syracuseStep 21732461 = 8149673) B8149673
theorem B14488307 : Blo 2259435 14488307 := bstep (se 1 (by rfl) ⟨10866230, by rfl⟩ : syracuseStep 14488307 = 21732461) B21732461
theorem B9658871 : Blo 2259435 9658871 := bstep (se 1 (by rfl) ⟨7244153, by rfl⟩ : syracuseStep 9658871 = 14488307) B14488307
theorem B6439247 : Blo 2259435 6439247 := bstep (se 1 (by rfl) ⟨4829435, by rfl⟩ : syracuseStep 6439247 = 9658871) B9658871
theorem B4292831 : Blo 2259435 4292831 := bstep (se 1 (by rfl) ⟨3219623, by rfl⟩ : syracuseStep 4292831 = 6439247) B6439247
theorem B2861887 : Blo 2259435 2861887 := bstep (se 1 (by rfl) ⟨2146415, by rfl⟩ : syracuseStep 2861887 = 4292831) B4292831
theorem B3815849 : Blo 2259435 3815849 := bstep (se 2 (by rfl) ⟨1430943, by rfl⟩ : syracuseStep 3815849 = 2861887) B2861887
theorem B2543899 : Blo 2259435 2543899 := bstep (se 1 (by rfl) ⟨1907924, by rfl⟩ : syracuseStep 2543899 = 3815849) B3815849
theorem B3391865 : Blo 2259435 3391865 := bstep (se 2 (by rfl) ⟨1271949, by rfl⟩ : syracuseStep 3391865 = 2543899) B2543899
theorem B2261243 : Blo 2259435 2261243 := bstep (se 1 (by rfl) ⟨1695932, by rfl⟩ : syracuseStep 2261243 = 3391865) B3391865
theorem B38635541 : Blo 2259435 38635541 := bbase (se 6 (by rfl) ⟨905520, by rfl⟩ : syracuseStep 38635541 = 1811041) (by norm_num)
theorem B25757027 : Blo 2259435 25757027 := bstep (se 1 (by rfl) ⟨19317770, by rfl⟩ : syracuseStep 25757027 = 38635541) B38635541
theorem B17171351 : Blo 2259435 17171351 := bstep (se 1 (by rfl) ⟨12878513, by rfl⟩ : syracuseStep 17171351 = 25757027) B25757027
theorem B11447567 : Blo 2259435 11447567 := bstep (se 1 (by rfl) ⟨8585675, by rfl⟩ : syracuseStep 11447567 = 17171351) B17171351
theorem B7631711 : Blo 2259435 7631711 := bstep (se 1 (by rfl) ⟨5723783, by rfl⟩ : syracuseStep 7631711 = 11447567) B11447567
theorem B5087807 : Blo 2259435 5087807 := bstep (se 1 (by rfl) ⟨3815855, by rfl⟩ : syracuseStep 5087807 = 7631711) B7631711
theorem B3391871 : Blo 2259435 3391871 := bstep (se 1 (by rfl) ⟨2543903, by rfl⟩ : syracuseStep 3391871 = 5087807) B5087807
theorem B2261247 : Blo 2259435 2261247 := bstep (se 1 (by rfl) ⟨1695935, by rfl⟩ : syracuseStep 2261247 = 3391871) B3391871
theorem B3391877 : Blo 2259435 3391877 := bbase (se 4 (by rfl) ⟨317988, by rfl⟩ : syracuseStep 3391877 = 635977) (by norm_num)
theorem B2261251 : Blo 2259435 2261251 := bstep (se 1 (by rfl) ⟨1695938, by rfl⟩ : syracuseStep 2261251 = 3391877) B3391877
theorem B3815869 : Blo 2259435 3815869 := bbase (se 3 (by rfl) ⟨715475, by rfl⟩ : syracuseStep 3815869 = 1430951) (by norm_num)
theorem B5087825 : Blo 2259435 5087825 := bstep (se 2 (by rfl) ⟨1907934, by rfl⟩ : syracuseStep 5087825 = 3815869) B3815869
theorem B3391883 : Blo 2259435 3391883 := bstep (se 1 (by rfl) ⟨2543912, by rfl⟩ : syracuseStep 3391883 = 5087825) B5087825
theorem B2261255 : Blo 2259435 2261255 := bstep (se 1 (by rfl) ⟨1695941, by rfl⟩ : syracuseStep 2261255 = 3391883) B3391883
theorem B2543917 : Blo 2259435 2543917 := bbase (se 3 (by rfl) ⟨476984, by rfl⟩ : syracuseStep 2543917 = 953969) (by norm_num)
theorem B3391889 : Blo 2259435 3391889 := bstep (se 2 (by rfl) ⟨1271958, by rfl⟩ : syracuseStep 3391889 = 2543917) B2543917
theorem B2261259 : Blo 2259435 2261259 := bstep (se 1 (by rfl) ⟨1695944, by rfl⟩ : syracuseStep 2261259 = 3391889) B3391889
theorem B7631765 : Blo 2259435 7631765 := bbase (se 6 (by rfl) ⟨178869, by rfl⟩ : syracuseStep 7631765 = 357739) (by norm_num)
theorem B5087843 : Blo 2259435 5087843 := bstep (se 1 (by rfl) ⟨3815882, by rfl⟩ : syracuseStep 5087843 = 7631765) B7631765
theorem B3391895 : Blo 2259435 3391895 := bstep (se 1 (by rfl) ⟨2543921, by rfl⟩ : syracuseStep 3391895 = 5087843) B5087843
theorem B2261263 : Blo 2259435 2261263 := bstep (se 1 (by rfl) ⟨1695947, by rfl⟩ : syracuseStep 2261263 = 3391895) B3391895
theorem B3391901 : Blo 2259435 3391901 := bbase (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) (by norm_num)
theorem B2261267 : Blo 2259435 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B5087861 : Blo 2259435 5087861 := bbase (se 5 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 5087861 = 476987) (by norm_num)
theorem B3391907 : Blo 2259435 3391907 := bstep (se 1 (by rfl) ⟨2543930, by rfl⟩ : syracuseStep 3391907 = 5087861) B5087861
theorem B2261271 : Blo 2259435 2261271 := bstep (se 1 (by rfl) ⟨1695953, by rfl⟩ : syracuseStep 2261271 = 3391907) B3391907
theorem B10455301 : Blo 2259435 10455301 := bbase (se 4 (by rfl) ⟨980184, by rfl⟩ : syracuseStep 10455301 = 1960369) (by norm_num)
theorem B13940401 : Blo 2259435 13940401 := bstep (se 2 (by rfl) ⟨5227650, by rfl⟩ : syracuseStep 13940401 = 10455301) B10455301
theorem B18587201 : Blo 2259435 18587201 := bstep (se 2 (by rfl) ⟨6970200, by rfl⟩ : syracuseStep 18587201 = 13940401) B13940401
theorem B198263477 : Blo 2259435 198263477 := bstep (se 5 (by rfl) ⟨9293600, by rfl⟩ : syracuseStep 198263477 = 18587201) B18587201
theorem B132175651 : Blo 2259435 132175651 := bstep (se 1 (by rfl) ⟨99131738, by rfl⟩ : syracuseStep 132175651 = 198263477) B198263477
theorem B176234201 : Blo 2259435 176234201 := bstep (se 2 (by rfl) ⟨66087825, by rfl⟩ : syracuseStep 176234201 = 132175651) B132175651
theorem B117489467 : Blo 2259435 117489467 := bstep (se 1 (by rfl) ⟨88117100, by rfl⟩ : syracuseStep 117489467 = 176234201) B176234201
theorem B78326311 : Blo 2259435 78326311 := bstep (se 1 (by rfl) ⟨58744733, by rfl⟩ : syracuseStep 78326311 = 117489467) B117489467
theorem B104435081 : Blo 2259435 104435081 := bstep (se 2 (by rfl) ⟨39163155, by rfl⟩ : syracuseStep 104435081 = 78326311) B78326311
theorem B69623387 : Blo 2259435 69623387 := bstep (se 1 (by rfl) ⟨52217540, by rfl⟩ : syracuseStep 69623387 = 104435081) B104435081
theorem B46415591 : Blo 2259435 46415591 := bstep (se 1 (by rfl) ⟨34811693, by rfl⟩ : syracuseStep 46415591 = 69623387) B69623387
theorem B30943727 : Blo 2259435 30943727 := bstep (se 1 (by rfl) ⟨23207795, by rfl⟩ : syracuseStep 30943727 = 46415591) B46415591
theorem B20629151 : Blo 2259435 20629151 := bstep (se 1 (by rfl) ⟨15471863, by rfl⟩ : syracuseStep 20629151 = 30943727) B30943727
theorem B13752767 : Blo 2259435 13752767 := bstep (se 1 (by rfl) ⟨10314575, by rfl⟩ : syracuseStep 13752767 = 20629151) B20629151
theorem B36674045 : Blo 2259435 36674045 := bstep (se 3 (by rfl) ⟨6876383, by rfl⟩ : syracuseStep 36674045 = 13752767) B13752767
theorem B24449363 : Blo 2259435 24449363 := bstep (se 1 (by rfl) ⟨18337022, by rfl⟩ : syracuseStep 24449363 = 36674045) B36674045
theorem B16299575 : Blo 2259435 16299575 := bstep (se 1 (by rfl) ⟨12224681, by rfl⟩ : syracuseStep 16299575 = 24449363) B24449363
theorem B10866383 : Blo 2259435 10866383 := bstep (se 1 (by rfl) ⟨8149787, by rfl⟩ : syracuseStep 10866383 = 16299575) B16299575
theorem B7244255 : Blo 2259435 7244255 := bstep (se 1 (by rfl) ⟨5433191, by rfl⟩ : syracuseStep 7244255 = 10866383) B10866383
theorem B19318013 : Blo 2259435 19318013 := bstep (se 3 (by rfl) ⟨3622127, by rfl⟩ : syracuseStep 19318013 = 7244255) B7244255
theorem B12878675 : Blo 2259435 12878675 := bstep (se 1 (by rfl) ⟨9659006, by rfl⟩ : syracuseStep 12878675 = 19318013) B19318013
theorem B8585783 : Blo 2259435 8585783 := bstep (se 1 (by rfl) ⟨6439337, by rfl⟩ : syracuseStep 8585783 = 12878675) B12878675
theorem B5723855 : Blo 2259435 5723855 := bstep (se 1 (by rfl) ⟨4292891, by rfl⟩ : syracuseStep 5723855 = 8585783) B8585783
theorem B3815903 : Blo 2259435 3815903 := bstep (se 1 (by rfl) ⟨2861927, by rfl⟩ : syracuseStep 3815903 = 5723855) B5723855
theorem B2543935 : Blo 2259435 2543935 := bstep (se 1 (by rfl) ⟨1907951, by rfl⟩ : syracuseStep 2543935 = 3815903) B3815903
theorem B3391913 : Blo 2259435 3391913 := bstep (se 2 (by rfl) ⟨1271967, by rfl⟩ : syracuseStep 3391913 = 2543935) B2543935
theorem B2261275 : Blo 2259435 2261275 := bstep (se 1 (by rfl) ⟨1695956, by rfl⟩ : syracuseStep 2261275 = 3391913) B3391913
theorem B8585797 : Blo 2259435 8585797 := bbase (se 4 (by rfl) ⟨804918, by rfl⟩ : syracuseStep 8585797 = 1609837) (by norm_num)
theorem B11447729 : Blo 2259435 11447729 := bstep (se 2 (by rfl) ⟨4292898, by rfl⟩ : syracuseStep 11447729 = 8585797) B8585797
theorem B7631819 : Blo 2259435 7631819 := bstep (se 1 (by rfl) ⟨5723864, by rfl⟩ : syracuseStep 7631819 = 11447729) B11447729
theorem B5087879 : Blo 2259435 5087879 := bstep (se 1 (by rfl) ⟨3815909, by rfl⟩ : syracuseStep 5087879 = 7631819) B7631819
theorem B3391919 : Blo 2259435 3391919 := bstep (se 1 (by rfl) ⟨2543939, by rfl⟩ : syracuseStep 3391919 = 5087879) B5087879
theorem B2261279 : Blo 2259435 2261279 := bstep (se 1 (by rfl) ⟨1695959, by rfl⟩ : syracuseStep 2261279 = 3391919) B3391919
theorem B3391925 : Blo 2259435 3391925 := bbase (se 5 (by rfl) ⟨158996, by rfl⟩ : syracuseStep 3391925 = 317993) (by norm_num)
theorem B2261283 : Blo 2259435 2261283 := bstep (se 1 (by rfl) ⟨1695962, by rfl⟩ : syracuseStep 2261283 = 3391925) B3391925
theorem B5723885 : Blo 2259435 5723885 := bbase (se 3 (by rfl) ⟨1073228, by rfl⟩ : syracuseStep 5723885 = 2146457) (by norm_num)
theorem B3815923 : Blo 2259435 3815923 := bstep (se 1 (by rfl) ⟨2861942, by rfl⟩ : syracuseStep 3815923 = 5723885) B5723885
theorem B5087897 : Blo 2259435 5087897 := bstep (se 2 (by rfl) ⟨1907961, by rfl⟩ : syracuseStep 5087897 = 3815923) B3815923
theorem B3391931 : Blo 2259435 3391931 := bstep (se 1 (by rfl) ⟨2543948, by rfl⟩ : syracuseStep 3391931 = 5087897) B5087897
theorem B2261287 : Blo 2259435 2261287 := bstep (se 1 (by rfl) ⟨1695965, by rfl⟩ : syracuseStep 2261287 = 3391931) B3391931
theorem B2543953 : Blo 2259435 2543953 := bbase (se 2 (by rfl) ⟨953982, by rfl⟩ : syracuseStep 2543953 = 1907965) (by norm_num)
theorem B3391937 : Blo 2259435 3391937 := bstep (se 2 (by rfl) ⟨1271976, by rfl⟩ : syracuseStep 3391937 = 2543953) B2543953
theorem B2261291 : Blo 2259435 2261291 := bstep (se 1 (by rfl) ⟨1695968, by rfl⟩ : syracuseStep 2261291 = 3391937) B3391937
theorem B2414773 : Blo 2259435 2414773 := bbase (se 5 (by rfl) ⟨113192, by rfl⟩ : syracuseStep 2414773 = 226385) (by norm_num)
theorem B3219697 : Blo 2259435 3219697 := bstep (se 2 (by rfl) ⟨1207386, by rfl⟩ : syracuseStep 3219697 = 2414773) B2414773
theorem B4292929 : Blo 2259435 4292929 := bstep (se 2 (by rfl) ⟨1609848, by rfl⟩ : syracuseStep 4292929 = 3219697) B3219697
theorem B5723905 : Blo 2259435 5723905 := bstep (se 2 (by rfl) ⟨2146464, by rfl⟩ : syracuseStep 5723905 = 4292929) B4292929
theorem B7631873 : Blo 2259435 7631873 := bstep (se 2 (by rfl) ⟨2861952, by rfl⟩ : syracuseStep 7631873 = 5723905) B5723905
theorem B5087915 : Blo 2259435 5087915 := bstep (se 1 (by rfl) ⟨3815936, by rfl⟩ : syracuseStep 5087915 = 7631873) B7631873
theorem B3391943 : Blo 2259435 3391943 := bstep (se 1 (by rfl) ⟨2543957, by rfl⟩ : syracuseStep 3391943 = 5087915) B5087915
theorem B2261295 : Blo 2259435 2261295 := bstep (se 1 (by rfl) ⟨1695971, by rfl⟩ : syracuseStep 2261295 = 3391943) B3391943
theorem B3391949 : Blo 2259435 3391949 := bbase (se 3 (by rfl) ⟨635990, by rfl⟩ : syracuseStep 3391949 = 1271981) (by norm_num)
theorem B2261299 : Blo 2259435 2261299 := bstep (se 1 (by rfl) ⟨1695974, by rfl⟩ : syracuseStep 2261299 = 3391949) B3391949
theorem B5087933 : Blo 2259435 5087933 := bbase (se 3 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 5087933 = 1907975) (by norm_num)
theorem B3391955 : Blo 2259435 3391955 := bstep (se 1 (by rfl) ⟨2543966, by rfl⟩ : syracuseStep 3391955 = 5087933) B5087933
theorem B2261303 : Blo 2259435 2261303 := bstep (se 1 (by rfl) ⟨1695977, by rfl⟩ : syracuseStep 2261303 = 3391955) B3391955
theorem B3815957 : Blo 2259435 3815957 := bbase (se 6 (by rfl) ⟨89436, by rfl⟩ : syracuseStep 3815957 = 178873) (by norm_num)
theorem B2543971 : Blo 2259435 2543971 := bstep (se 1 (by rfl) ⟨1907978, by rfl⟩ : syracuseStep 2543971 = 3815957) B3815957
theorem B3391961 : Blo 2259435 3391961 := bstep (se 2 (by rfl) ⟨1271985, by rfl⟩ : syracuseStep 3391961 = 2543971) B2543971
theorem B2261307 : Blo 2259435 2261307 := bstep (se 1 (by rfl) ⟨1695980, by rfl⟩ : syracuseStep 2261307 = 3391961) B3391961
theorem B21733109 : Blo 2259435 21733109 := bbase (se 5 (by rfl) ⟨1018739, by rfl⟩ : syracuseStep 21733109 = 2037479) (by norm_num)
theorem B14488739 : Blo 2259435 14488739 := bstep (se 1 (by rfl) ⟨10866554, by rfl⟩ : syracuseStep 14488739 = 21733109) B21733109
theorem B9659159 : Blo 2259435 9659159 := bstep (se 1 (by rfl) ⟨7244369, by rfl⟩ : syracuseStep 9659159 = 14488739) B14488739
theorem B6439439 : Blo 2259435 6439439 := bstep (se 1 (by rfl) ⟨4829579, by rfl⟩ : syracuseStep 6439439 = 9659159) B9659159
theorem B17171837 : Blo 2259435 17171837 := bstep (se 3 (by rfl) ⟨3219719, by rfl⟩ : syracuseStep 17171837 = 6439439) B6439439
theorem B11447891 : Blo 2259435 11447891 := bstep (se 1 (by rfl) ⟨8585918, by rfl⟩ : syracuseStep 11447891 = 17171837) B17171837
theorem B7631927 : Blo 2259435 7631927 := bstep (se 1 (by rfl) ⟨5723945, by rfl⟩ : syracuseStep 7631927 = 11447891) B11447891
theorem B5087951 : Blo 2259435 5087951 := bstep (se 1 (by rfl) ⟨3815963, by rfl⟩ : syracuseStep 5087951 = 7631927) B7631927
theorem B3391967 : Blo 2259435 3391967 := bstep (se 1 (by rfl) ⟨2543975, by rfl⟩ : syracuseStep 3391967 = 5087951) B5087951
theorem B2261311 : Blo 2259435 2261311 := bstep (se 1 (by rfl) ⟨1695983, by rfl⟩ : syracuseStep 2261311 = 3391967) B3391967
theorem B3391973 : Blo 2259435 3391973 := bbase (se 4 (by rfl) ⟨317997, by rfl⟩ : syracuseStep 3391973 = 635995) (by norm_num)
theorem B2261315 : Blo 2259435 2261315 := bstep (se 1 (by rfl) ⟨1695986, by rfl⟩ : syracuseStep 2261315 = 3391973) B3391973
theorem B16299893 : Blo 2259435 16299893 := bbase (se 5 (by rfl) ⟨764057, by rfl⟩ : syracuseStep 16299893 = 1528115) (by norm_num)
theorem B10866595 : Blo 2259435 10866595 := bstep (se 1 (by rfl) ⟨8149946, by rfl⟩ : syracuseStep 10866595 = 16299893) B16299893
theorem B14488793 : Blo 2259435 14488793 := bstep (se 2 (by rfl) ⟨5433297, by rfl⟩ : syracuseStep 14488793 = 10866595) B10866595
theorem B9659195 : Blo 2259435 9659195 := bstep (se 1 (by rfl) ⟨7244396, by rfl⟩ : syracuseStep 9659195 = 14488793) B14488793
theorem B6439463 : Blo 2259435 6439463 := bstep (se 1 (by rfl) ⟨4829597, by rfl⟩ : syracuseStep 6439463 = 9659195) B9659195
theorem B4292975 : Blo 2259435 4292975 := bstep (se 1 (by rfl) ⟨3219731, by rfl⟩ : syracuseStep 4292975 = 6439463) B6439463
theorem B2861983 : Blo 2259435 2861983 := bstep (se 1 (by rfl) ⟨2146487, by rfl⟩ : syracuseStep 2861983 = 4292975) B4292975
theorem B3815977 : Blo 2259435 3815977 := bstep (se 2 (by rfl) ⟨1430991, by rfl⟩ : syracuseStep 3815977 = 2861983) B2861983
theorem B5087969 : Blo 2259435 5087969 := bstep (se 2 (by rfl) ⟨1907988, by rfl⟩ : syracuseStep 5087969 = 3815977) B3815977
theorem B3391979 : Blo 2259435 3391979 := bstep (se 1 (by rfl) ⟨2543984, by rfl⟩ : syracuseStep 3391979 = 5087969) B5087969
theorem B2261319 : Blo 2259435 2261319 := bstep (se 1 (by rfl) ⟨1695989, by rfl⟩ : syracuseStep 2261319 = 3391979) B3391979
theorem B2543989 : Blo 2259435 2543989 := bbase (se 5 (by rfl) ⟨119249, by rfl⟩ : syracuseStep 2543989 = 238499) (by norm_num)
theorem B3391985 : Blo 2259435 3391985 := bstep (se 2 (by rfl) ⟨1271994, by rfl⟩ : syracuseStep 3391985 = 2543989) B2543989
theorem B2261323 : Blo 2259435 2261323 := bstep (se 1 (by rfl) ⟨1695992, by rfl⟩ : syracuseStep 2261323 = 3391985) B3391985
theorem B2861993 : Blo 2259435 2861993 := bbase (se 2 (by rfl) ⟨1073247, by rfl⟩ : syracuseStep 2861993 = 2146495) (by norm_num)
theorem B7631981 : Blo 2259435 7631981 := bstep (se 3 (by rfl) ⟨1430996, by rfl⟩ : syracuseStep 7631981 = 2861993) B2861993
theorem B5087987 : Blo 2259435 5087987 := bstep (se 1 (by rfl) ⟨3815990, by rfl⟩ : syracuseStep 5087987 = 7631981) B7631981
theorem B3391991 : Blo 2259435 3391991 := bstep (se 1 (by rfl) ⟨2543993, by rfl⟩ : syracuseStep 3391991 = 5087987) B5087987
theorem B2261327 : Blo 2259435 2261327 := bstep (se 1 (by rfl) ⟨1695995, by rfl⟩ : syracuseStep 2261327 = 3391991) B3391991
theorem B3391997 : Blo 2259435 3391997 := bbase (se 3 (by rfl) ⟨635999, by rfl⟩ : syracuseStep 3391997 = 1271999) (by norm_num)
theorem B2261331 : Blo 2259435 2261331 := bstep (se 1 (by rfl) ⟨1695998, by rfl⟩ : syracuseStep 2261331 = 3391997) B3391997
theorem B5088005 : Blo 2259435 5088005 := bbase (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) (by norm_num)
theorem B3392003 : Blo 2259435 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B2261335 : Blo 2259435 2261335 := bstep (se 1 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 2261335 = 3392003) B3392003
theorem B4293013 : Blo 2259435 4293013 := bbase (se 6 (by rfl) ⟨100617, by rfl⟩ : syracuseStep 4293013 = 201235) (by norm_num)
theorem B5724017 : Blo 2259435 5724017 := bstep (se 2 (by rfl) ⟨2146506, by rfl⟩ : syracuseStep 5724017 = 4293013) B4293013
theorem B3816011 : Blo 2259435 3816011 := bstep (se 1 (by rfl) ⟨2862008, by rfl⟩ : syracuseStep 3816011 = 5724017) B5724017
theorem B2544007 : Blo 2259435 2544007 := bstep (se 1 (by rfl) ⟨1908005, by rfl⟩ : syracuseStep 2544007 = 3816011) B3816011
theorem B3392009 : Blo 2259435 3392009 := bstep (se 2 (by rfl) ⟨1272003, by rfl⟩ : syracuseStep 3392009 = 2544007) B2544007
theorem B2261339 : Blo 2259435 2261339 := bstep (se 1 (by rfl) ⟨1696004, by rfl⟩ : syracuseStep 2261339 = 3392009) B3392009
theorem B11448053 : Blo 2259435 11448053 := bbase (se 5 (by rfl) ⟨536627, by rfl⟩ : syracuseStep 11448053 = 1073255) (by norm_num)
theorem B7632035 : Blo 2259435 7632035 := bstep (se 1 (by rfl) ⟨5724026, by rfl⟩ : syracuseStep 7632035 = 11448053) B11448053
theorem B5088023 : Blo 2259435 5088023 := bstep (se 1 (by rfl) ⟨3816017, by rfl⟩ : syracuseStep 5088023 = 7632035) B7632035
theorem B3392015 : Blo 2259435 3392015 := bstep (se 1 (by rfl) ⟨2544011, by rfl⟩ : syracuseStep 3392015 = 5088023) B5088023
theorem B2261343 : Blo 2259435 2261343 := bstep (se 1 (by rfl) ⟨1696007, by rfl⟩ : syracuseStep 2261343 = 3392015) B3392015
theorem B3392021 : Blo 2259435 3392021 := bbase (se 6 (by rfl) ⟨79500, by rfl⟩ : syracuseStep 3392021 = 159001) (by norm_num)
theorem B2261347 : Blo 2259435 2261347 := bstep (se 1 (by rfl) ⟨1696010, by rfl⟩ : syracuseStep 2261347 = 3392021) B3392021
theorem B9168821 : Blo 2259435 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B6112547 : Blo 2259435 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B4075031 : Blo 2259435 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B2716687 : Blo 2259435 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B3622249 : Blo 2259435 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B19318661 : Blo 2259435 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B12879107 : Blo 2259435 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B8586071 : Blo 2259435 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B5724047 : Blo 2259435 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B3816031 : Blo 2259435 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B5088041 : Blo 2259435 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B3392027 : Blo 2259435 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B2261351 : Blo 2259435 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B2544025 : Blo 2259435 2544025 := bbase (se 2 (by rfl) ⟨954009, by rfl⟩ : syracuseStep 2544025 = 1908019) (by norm_num)
theorem B3392033 : Blo 2259435 3392033 := bstep (se 2 (by rfl) ⟨1272012, by rfl⟩ : syracuseStep 3392033 = 2544025) B2544025
theorem B2261355 : Blo 2259435 2261355 := bstep (se 1 (by rfl) ⟨1696016, by rfl⟩ : syracuseStep 2261355 = 3392033) B3392033
theorem B8586101 : Blo 2259435 8586101 := bbase (se 5 (by rfl) ⟨402473, by rfl⟩ : syracuseStep 8586101 = 804947) (by norm_num)
theorem B5724067 : Blo 2259435 5724067 := bstep (se 1 (by rfl) ⟨4293050, by rfl⟩ : syracuseStep 5724067 = 8586101) B8586101
theorem B7632089 : Blo 2259435 7632089 := bstep (se 2 (by rfl) ⟨2862033, by rfl⟩ : syracuseStep 7632089 = 5724067) B5724067
theorem B5088059 : Blo 2259435 5088059 := bstep (se 1 (by rfl) ⟨3816044, by rfl⟩ : syracuseStep 5088059 = 7632089) B7632089
theorem B3392039 : Blo 2259435 3392039 := bstep (se 1 (by rfl) ⟨2544029, by rfl⟩ : syracuseStep 3392039 = 5088059) B5088059
theorem B2261359 : Blo 2259435 2261359 := bstep (se 1 (by rfl) ⟨1696019, by rfl⟩ : syracuseStep 2261359 = 3392039) B3392039
theorem B3392045 : Blo 2259435 3392045 := bbase (se 3 (by rfl) ⟨636008, by rfl⟩ : syracuseStep 3392045 = 1272017) (by norm_num)
theorem B2261363 : Blo 2259435 2261363 := bstep (se 1 (by rfl) ⟨1696022, by rfl⟩ : syracuseStep 2261363 = 3392045) B3392045
theorem B5088077 : Blo 2259435 5088077 := bbase (se 3 (by rfl) ⟨954014, by rfl⟩ : syracuseStep 5088077 = 1908029) (by norm_num)
theorem B3392051 : Blo 2259435 3392051 := bstep (se 1 (by rfl) ⟨2544038, by rfl⟩ : syracuseStep 3392051 = 5088077) B5088077
theorem B2261367 : Blo 2259435 2261367 := bstep (se 1 (by rfl) ⟨1696025, by rfl⟩ : syracuseStep 2261367 = 3392051) B3392051
theorem B2862049 : Blo 2259435 2862049 := bbase (se 2 (by rfl) ⟨1073268, by rfl⟩ : syracuseStep 2862049 = 2146537) (by norm_num)
theorem B3816065 : Blo 2259435 3816065 := bstep (se 2 (by rfl) ⟨1431024, by rfl⟩ : syracuseStep 3816065 = 2862049) B2862049
theorem B2544043 : Blo 2259435 2544043 := bstep (se 1 (by rfl) ⟨1908032, by rfl⟩ : syracuseStep 2544043 = 3816065) B3816065
theorem B3392057 : Blo 2259435 3392057 := bstep (se 2 (by rfl) ⟨1272021, by rfl⟩ : syracuseStep 3392057 = 2544043) B2544043
theorem B2261371 : Blo 2259435 2261371 := bstep (se 1 (by rfl) ⟨1696028, by rfl⟩ : syracuseStep 2261371 = 3392057) B3392057
theorem B25758485 : Blo 2259435 25758485 := bbase (se 6 (by rfl) ⟨603714, by rfl⟩ : syracuseStep 25758485 = 1207429) (by norm_num)
theorem B17172323 : Blo 2259435 17172323 := bstep (se 1 (by rfl) ⟨12879242, by rfl⟩ : syracuseStep 17172323 = 25758485) B25758485
theorem B11448215 : Blo 2259435 11448215 := bstep (se 1 (by rfl) ⟨8586161, by rfl⟩ : syracuseStep 11448215 = 17172323) B17172323
theorem B7632143 : Blo 2259435 7632143 := bstep (se 1 (by rfl) ⟨5724107, by rfl⟩ : syracuseStep 7632143 = 11448215) B11448215
theorem B5088095 : Blo 2259435 5088095 := bstep (se 1 (by rfl) ⟨3816071, by rfl⟩ : syracuseStep 5088095 = 7632143) B7632143
theorem B3392063 : Blo 2259435 3392063 := bstep (se 1 (by rfl) ⟨2544047, by rfl⟩ : syracuseStep 3392063 = 5088095) B5088095
theorem B2261375 : Blo 2259435 2261375 := bstep (se 1 (by rfl) ⟨1696031, by rfl⟩ : syracuseStep 2261375 = 3392063) B3392063
theorem B3392069 : Blo 2259435 3392069 := bbase (se 4 (by rfl) ⟨318006, by rfl⟩ : syracuseStep 3392069 = 636013) (by norm_num)
theorem B2261379 : Blo 2259435 2261379 := bstep (se 1 (by rfl) ⟨1696034, by rfl⟩ : syracuseStep 2261379 = 3392069) B3392069
theorem B3816085 : Blo 2259435 3816085 := bbase (se 6 (by rfl) ⟨89439, by rfl⟩ : syracuseStep 3816085 = 178879) (by norm_num)
theorem B5088113 : Blo 2259435 5088113 := bstep (se 2 (by rfl) ⟨1908042, by rfl⟩ : syracuseStep 5088113 = 3816085) B3816085
theorem B3392075 : Blo 2259435 3392075 := bstep (se 1 (by rfl) ⟨2544056, by rfl⟩ : syracuseStep 3392075 = 5088113) B5088113
theorem B2261383 : Blo 2259435 2261383 := bstep (se 1 (by rfl) ⟨1696037, by rfl⟩ : syracuseStep 2261383 = 3392075) B3392075
theorem B2544061 : Blo 2259435 2544061 := bbase (se 3 (by rfl) ⟨477011, by rfl⟩ : syracuseStep 2544061 = 954023) (by norm_num)
theorem B3392081 : Blo 2259435 3392081 := bstep (se 2 (by rfl) ⟨1272030, by rfl⟩ : syracuseStep 3392081 = 2544061) B2544061
theorem B2261387 : Blo 2259435 2261387 := bstep (se 1 (by rfl) ⟨1696040, by rfl⟩ : syracuseStep 2261387 = 3392081) B3392081
theorem B7632197 : Blo 2259435 7632197 := bbase (se 4 (by rfl) ⟨715518, by rfl⟩ : syracuseStep 7632197 = 1431037) (by norm_num)
theorem B5088131 : Blo 2259435 5088131 := bstep (se 1 (by rfl) ⟨3816098, by rfl⟩ : syracuseStep 5088131 = 7632197) B7632197
theorem B3392087 : Blo 2259435 3392087 := bstep (se 1 (by rfl) ⟨2544065, by rfl⟩ : syracuseStep 3392087 = 5088131) B5088131
theorem B2261391 : Blo 2259435 2261391 := bstep (se 1 (by rfl) ⟨1696043, by rfl⟩ : syracuseStep 2261391 = 3392087) B3392087
theorem B3392093 : Blo 2259435 3392093 := bbase (se 3 (by rfl) ⟨636017, by rfl⟩ : syracuseStep 3392093 = 1272035) (by norm_num)
theorem B2261395 : Blo 2259435 2261395 := bstep (se 1 (by rfl) ⟨1696046, by rfl⟩ : syracuseStep 2261395 = 3392093) B3392093
theorem B5088149 : Blo 2259435 5088149 := bbase (se 6 (by rfl) ⟨119253, by rfl⟩ : syracuseStep 5088149 = 238507) (by norm_num)
theorem B3392099 : Blo 2259435 3392099 := bstep (se 1 (by rfl) ⟨2544074, by rfl⟩ : syracuseStep 3392099 = 5088149) B5088149
theorem B2261399 : Blo 2259435 2261399 := bstep (se 1 (by rfl) ⟨1696049, by rfl⟩ : syracuseStep 2261399 = 3392099) B3392099
theorem B3622333 : Blo 2259435 3622333 := bbase (se 3 (by rfl) ⟨679187, by rfl⟩ : syracuseStep 3622333 = 1358375) (by norm_num)
theorem B4829777 : Blo 2259435 4829777 := bstep (se 2 (by rfl) ⟨1811166, by rfl⟩ : syracuseStep 4829777 = 3622333) B3622333
theorem B3219851 : Blo 2259435 3219851 := bstep (se 1 (by rfl) ⟨2414888, by rfl⟩ : syracuseStep 3219851 = 4829777) B4829777
theorem B8586269 : Blo 2259435 8586269 := bstep (se 3 (by rfl) ⟨1609925, by rfl⟩ : syracuseStep 8586269 = 3219851) B3219851
theorem B5724179 : Blo 2259435 5724179 := bstep (se 1 (by rfl) ⟨4293134, by rfl⟩ : syracuseStep 5724179 = 8586269) B8586269
theorem B3816119 : Blo 2259435 3816119 := bstep (se 1 (by rfl) ⟨2862089, by rfl⟩ : syracuseStep 3816119 = 5724179) B5724179
theorem B2544079 : Blo 2259435 2544079 := bstep (se 1 (by rfl) ⟨1908059, by rfl⟩ : syracuseStep 2544079 = 3816119) B3816119
theorem B3392105 : Blo 2259435 3392105 := bstep (se 2 (by rfl) ⟨1272039, by rfl⟩ : syracuseStep 3392105 = 2544079) B2544079
theorem B2261403 : Blo 2259435 2261403 := bstep (se 1 (by rfl) ⟨1696052, by rfl⟩ : syracuseStep 2261403 = 3392105) B3392105
theorem B7244677 : Blo 2259435 7244677 := bbase (se 4 (by rfl) ⟨679188, by rfl⟩ : syracuseStep 7244677 = 1358377) (by norm_num)
theorem B9659569 : Blo 2259435 9659569 := bstep (se 2 (by rfl) ⟨3622338, by rfl⟩ : syracuseStep 9659569 = 7244677) B7244677
theorem B12879425 : Blo 2259435 12879425 := bstep (se 2 (by rfl) ⟨4829784, by rfl⟩ : syracuseStep 12879425 = 9659569) B9659569
theorem B8586283 : Blo 2259435 8586283 := bstep (se 1 (by rfl) ⟨6439712, by rfl⟩ : syracuseStep 8586283 = 12879425) B12879425
theorem B11448377 : Blo 2259435 11448377 := bstep (se 2 (by rfl) ⟨4293141, by rfl⟩ : syracuseStep 11448377 = 8586283) B8586283
theorem B7632251 : Blo 2259435 7632251 := bstep (se 1 (by rfl) ⟨5724188, by rfl⟩ : syracuseStep 7632251 = 11448377) B11448377
theorem B5088167 : Blo 2259435 5088167 := bstep (se 1 (by rfl) ⟨3816125, by rfl⟩ : syracuseStep 5088167 = 7632251) B7632251
theorem B3392111 : Blo 2259435 3392111 := bstep (se 1 (by rfl) ⟨2544083, by rfl⟩ : syracuseStep 3392111 = 5088167) B5088167
theorem B2261407 : Blo 2259435 2261407 := bstep (se 1 (by rfl) ⟨1696055, by rfl⟩ : syracuseStep 2261407 = 3392111) B3392111
theorem B3392117 : Blo 2259435 3392117 := bbase (se 5 (by rfl) ⟨159005, by rfl⟩ : syracuseStep 3392117 = 318011) (by norm_num)
theorem B2261411 : Blo 2259435 2261411 := bstep (se 1 (by rfl) ⟨1696058, by rfl⟩ : syracuseStep 2261411 = 3392117) B3392117
theorem B4293157 : Blo 2259435 4293157 := bbase (se 4 (by rfl) ⟨402483, by rfl⟩ : syracuseStep 4293157 = 804967) (by norm_num)
theorem B5724209 : Blo 2259435 5724209 := bstep (se 2 (by rfl) ⟨2146578, by rfl⟩ : syracuseStep 5724209 = 4293157) B4293157
theorem B3816139 : Blo 2259435 3816139 := bstep (se 1 (by rfl) ⟨2862104, by rfl⟩ : syracuseStep 3816139 = 5724209) B5724209
theorem B5088185 : Blo 2259435 5088185 := bstep (se 2 (by rfl) ⟨1908069, by rfl⟩ : syracuseStep 5088185 = 3816139) B3816139
theorem B3392123 : Blo 2259435 3392123 := bstep (se 1 (by rfl) ⟨2544092, by rfl⟩ : syracuseStep 3392123 = 5088185) B5088185
theorem B2261415 : Blo 2259435 2261415 := bstep (se 1 (by rfl) ⟨1696061, by rfl⟩ : syracuseStep 2261415 = 3392123) B3392123
theorem B2544097 : Blo 2259435 2544097 := bbase (se 2 (by rfl) ⟨954036, by rfl⟩ : syracuseStep 2544097 = 1908073) (by norm_num)
theorem B3392129 : Blo 2259435 3392129 := bstep (se 2 (by rfl) ⟨1272048, by rfl⟩ : syracuseStep 3392129 = 2544097) B2544097
theorem B2261419 : Blo 2259435 2261419 := bstep (se 1 (by rfl) ⟨1696064, by rfl⟩ : syracuseStep 2261419 = 3392129) B3392129
theorem B5724229 : Blo 2259435 5724229 := bbase (se 4 (by rfl) ⟨536646, by rfl⟩ : syracuseStep 5724229 = 1073293) (by norm_num)
theorem B7632305 : Blo 2259435 7632305 := bstep (se 2 (by rfl) ⟨2862114, by rfl⟩ : syracuseStep 7632305 = 5724229) B5724229
theorem B5088203 : Blo 2259435 5088203 := bstep (se 1 (by rfl) ⟨3816152, by rfl⟩ : syracuseStep 5088203 = 7632305) B7632305
theorem B3392135 : Blo 2259435 3392135 := bstep (se 1 (by rfl) ⟨2544101, by rfl⟩ : syracuseStep 3392135 = 5088203) B5088203
theorem B2261423 : Blo 2259435 2261423 := bstep (se 1 (by rfl) ⟨1696067, by rfl⟩ : syracuseStep 2261423 = 3392135) B3392135
theorem B3392141 : Blo 2259435 3392141 := bbase (se 3 (by rfl) ⟨636026, by rfl⟩ : syracuseStep 3392141 = 1272053) (by norm_num)
theorem B2261427 : Blo 2259435 2261427 := bstep (se 1 (by rfl) ⟨1696070, by rfl⟩ : syracuseStep 2261427 = 3392141) B3392141
theorem B5088221 : Blo 2259435 5088221 := bbase (se 3 (by rfl) ⟨954041, by rfl⟩ : syracuseStep 5088221 = 1908083) (by norm_num)
theorem B3392147 : Blo 2259435 3392147 := bstep (se 1 (by rfl) ⟨2544110, by rfl⟩ : syracuseStep 3392147 = 5088221) B5088221
theorem B2261431 : Blo 2259435 2261431 := bstep (se 1 (by rfl) ⟨1696073, by rfl⟩ : syracuseStep 2261431 = 3392147) B3392147
theorem B3816173 : Blo 2259435 3816173 := bbase (se 3 (by rfl) ⟨715532, by rfl⟩ : syracuseStep 3816173 = 1431065) (by norm_num)
theorem B2544115 : Blo 2259435 2544115 := bstep (se 1 (by rfl) ⟨1908086, by rfl⟩ : syracuseStep 2544115 = 3816173) B3816173
theorem B3392153 : Blo 2259435 3392153 := bstep (se 2 (by rfl) ⟨1272057, by rfl⟩ : syracuseStep 3392153 = 2544115) B2544115
theorem B2261435 : Blo 2259435 2261435 := bstep (se 1 (by rfl) ⟨1696076, by rfl⟩ : syracuseStep 2261435 = 3392153) B3392153
theorem C0 (j : ℕ) (h1 : 564858 ≤ j) (h2 : j ≤ 565358) : Blo 2259435 (4 * j + 3) := by
  interval_cases j
  · exact B2259435
  · exact B2259439
  · exact B2259443
  · exact B2259447
  · exact B2259451
  · exact B2259455
  · exact B2259459
  · exact B2259463
  · exact B2259467
  · exact B2259471
  · exact B2259475
  · exact B2259479
  · exact B2259483
  · exact B2259487
  · exact B2259491
  · exact B2259495
  · exact B2259499
  · exact B2259503
  · exact B2259507
  · exact B2259511
  · exact B2259515
  · exact B2259519
  · exact B2259523
  · exact B2259527
  · exact B2259531
  · exact B2259535
  · exact B2259539
  · exact B2259543
  · exact B2259547
  · exact B2259551
  · exact B2259555
  · exact B2259559
  · exact B2259563
  · exact B2259567
  · exact B2259571
  · exact B2259575
  · exact B2259579
  · exact B2259583
  · exact B2259587
  · exact B2259591
  · exact B2259595
  · exact B2259599
  · exact B2259603
  · exact B2259607
  · exact B2259611
  · exact B2259615
  · exact B2259619
  · exact B2259623
  · exact B2259627
  · exact B2259631
  · exact B2259635
  · exact B2259639
  · exact B2259643
  · exact B2259647
  · exact B2259651
  · exact B2259655
  · exact B2259659
  · exact B2259663
  · exact B2259667
  · exact B2259671
  · exact B2259675
  · exact B2259679
  · exact B2259683
  · exact B2259687
  · exact B2259691
  · exact B2259695
  · exact B2259699
  · exact B2259703
  · exact B2259707
  · exact B2259711
  · exact B2259715
  · exact B2259719
  · exact B2259723
  · exact B2259727
  · exact B2259731
  · exact B2259735
  · exact B2259739
  · exact B2259743
  · exact B2259747
  · exact B2259751
  · exact B2259755
  · exact B2259759
  · exact B2259763
  · exact B2259767
  · exact B2259771
  · exact B2259775
  · exact B2259779
  · exact B2259783
  · exact B2259787
  · exact B2259791
  · exact B2259795
  · exact B2259799
  · exact B2259803
  · exact B2259807
  · exact B2259811
  · exact B2259815
  · exact B2259819
  · exact B2259823
  · exact B2259827
  · exact B2259831
  · exact B2259835
  · exact B2259839
  · exact B2259843
  · exact B2259847
  · exact B2259851
  · exact B2259855
  · exact B2259859
  · exact B2259863
  · exact B2259867
  · exact B2259871
  · exact B2259875
  · exact B2259879
  · exact B2259883
  · exact B2259887
  · exact B2259891
  · exact B2259895
  · exact B2259899
  · exact B2259903
  · exact B2259907
  · exact B2259911
  · exact B2259915
  · exact B2259919
  · exact B2259923
  · exact B2259927
  · exact B2259931
  · exact B2259935
  · exact B2259939
  · exact B2259943
  · exact B2259947
  · exact B2259951
  · exact B2259955
  · exact B2259959
  · exact B2259963
  · exact B2259967
  · exact B2259971
  · exact B2259975
  · exact B2259979
  · exact B2259983
  · exact B2259987
  · exact B2259991
  · exact B2259995
  · exact B2259999
  · exact B2260003
  · exact B2260007
  · exact B2260011
  · exact B2260015
  · exact B2260019
  · exact B2260023
  · exact B2260027
  · exact B2260031
  · exact B2260035
  · exact B2260039
  · exact B2260043
  · exact B2260047
  · exact B2260051
  · exact B2260055
  · exact B2260059
  · exact B2260063
  · exact B2260067
  · exact B2260071
  · exact B2260075
  · exact B2260079
  · exact B2260083
  · exact B2260087
  · exact B2260091
  · exact B2260095
  · exact B2260099
  · exact B2260103
  · exact B2260107
  · exact B2260111
  · exact B2260115
  · exact B2260119
  · exact B2260123
  · exact B2260127
  · exact B2260131
  · exact B2260135
  · exact B2260139
  · exact B2260143
  · exact B2260147
  · exact B2260151
  · exact B2260155
  · exact B2260159
  · exact B2260163
  · exact B2260167
  · exact B2260171
  · exact B2260175
  · exact B2260179
  · exact B2260183
  · exact B2260187
  · exact B2260191
  · exact B2260195
  · exact B2260199
  · exact B2260203
  · exact B2260207
  · exact B2260211
  · exact B2260215
  · exact B2260219
  · exact B2260223
  · exact B2260227
  · exact B2260231
  · exact B2260235
  · exact B2260239
  · exact B2260243
  · exact B2260247
  · exact B2260251
  · exact B2260255
  · exact B2260259
  · exact B2260263
  · exact B2260267
  · exact B2260271
  · exact B2260275
  · exact B2260279
  · exact B2260283
  · exact B2260287
  · exact B2260291
  · exact B2260295
  · exact B2260299
  · exact B2260303
  · exact B2260307
  · exact B2260311
  · exact B2260315
  · exact B2260319
  · exact B2260323
  · exact B2260327
  · exact B2260331
  · exact B2260335
  · exact B2260339
  · exact B2260343
  · exact B2260347
  · exact B2260351
  · exact B2260355
  · exact B2260359
  · exact B2260363
  · exact B2260367
  · exact B2260371
  · exact B2260375
  · exact B2260379
  · exact B2260383
  · exact B2260387
  · exact B2260391
  · exact B2260395
  · exact B2260399
  · exact B2260403
  · exact B2260407
  · exact B2260411
  · exact B2260415
  · exact B2260419
  · exact B2260423
  · exact B2260427
  · exact B2260431
  · exact B2260435
  · exact B2260439
  · exact B2260443
  · exact B2260447
  · exact B2260451
  · exact B2260455
  · exact B2260459
  · exact B2260463
  · exact B2260467
  · exact B2260471
  · exact B2260475
  · exact B2260479
  · exact B2260483
  · exact B2260487
  · exact B2260491
  · exact B2260495
  · exact B2260499
  · exact B2260503
  · exact B2260507
  · exact B2260511
  · exact B2260515
  · exact B2260519
  · exact B2260523
  · exact B2260527
  · exact B2260531
  · exact B2260535
  · exact B2260539
  · exact B2260543
  · exact B2260547
  · exact B2260551
  · exact B2260555
  · exact B2260559
  · exact B2260563
  · exact B2260567
  · exact B2260571
  · exact B2260575
  · exact B2260579
  · exact B2260583
  · exact B2260587
  · exact B2260591
  · exact B2260595
  · exact B2260599
  · exact B2260603
  · exact B2260607
  · exact B2260611
  · exact B2260615
  · exact B2260619
  · exact B2260623
  · exact B2260627
  · exact B2260631
  · exact B2260635
  · exact B2260639
  · exact B2260643
  · exact B2260647
  · exact B2260651
  · exact B2260655
  · exact B2260659
  · exact B2260663
  · exact B2260667
  · exact B2260671
  · exact B2260675
  · exact B2260679
  · exact B2260683
  · exact B2260687
  · exact B2260691
  · exact B2260695
  · exact B2260699
  · exact B2260703
  · exact B2260707
  · exact B2260711
  · exact B2260715
  · exact B2260719
  · exact B2260723
  · exact B2260727
  · exact B2260731
  · exact B2260735
  · exact B2260739
  · exact B2260743
  · exact B2260747
  · exact B2260751
  · exact B2260755
  · exact B2260759
  · exact B2260763
  · exact B2260767
  · exact B2260771
  · exact B2260775
  · exact B2260779
  · exact B2260783
  · exact B2260787
  · exact B2260791
  · exact B2260795
  · exact B2260799
  · exact B2260803
  · exact B2260807
  · exact B2260811
  · exact B2260815
  · exact B2260819
  · exact B2260823
  · exact B2260827
  · exact B2260831
  · exact B2260835
  · exact B2260839
  · exact B2260843
  · exact B2260847
  · exact B2260851
  · exact B2260855
  · exact B2260859
  · exact B2260863
  · exact B2260867
  · exact B2260871
  · exact B2260875
  · exact B2260879
  · exact B2260883
  · exact B2260887
  · exact B2260891
  · exact B2260895
  · exact B2260899
  · exact B2260903
  · exact B2260907
  · exact B2260911
  · exact B2260915
  · exact B2260919
  · exact B2260923
  · exact B2260927
  · exact B2260931
  · exact B2260935
  · exact B2260939
  · exact B2260943
  · exact B2260947
  · exact B2260951
  · exact B2260955
  · exact B2260959
  · exact B2260963
  · exact B2260967
  · exact B2260971
  · exact B2260975
  · exact B2260979
  · exact B2260983
  · exact B2260987
  · exact B2260991
  · exact B2260995
  · exact B2260999
  · exact B2261003
  · exact B2261007
  · exact B2261011
  · exact B2261015
  · exact B2261019
  · exact B2261023
  · exact B2261027
  · exact B2261031
  · exact B2261035
  · exact B2261039
  · exact B2261043
  · exact B2261047
  · exact B2261051
  · exact B2261055
  · exact B2261059
  · exact B2261063
  · exact B2261067
  · exact B2261071
  · exact B2261075
  · exact B2261079
  · exact B2261083
  · exact B2261087
  · exact B2261091
  · exact B2261095
  · exact B2261099
  · exact B2261103
  · exact B2261107
  · exact B2261111
  · exact B2261115
  · exact B2261119
  · exact B2261123
  · exact B2261127
  · exact B2261131
  · exact B2261135
  · exact B2261139
  · exact B2261143
  · exact B2261147
  · exact B2261151
  · exact B2261155
  · exact B2261159
  · exact B2261163
  · exact B2261167
  · exact B2261171
  · exact B2261175
  · exact B2261179
  · exact B2261183
  · exact B2261187
  · exact B2261191
  · exact B2261195
  · exact B2261199
  · exact B2261203
  · exact B2261207
  · exact B2261211
  · exact B2261215
  · exact B2261219
  · exact B2261223
  · exact B2261227
  · exact B2261231
  · exact B2261235
  · exact B2261239
  · exact B2261243
  · exact B2261247
  · exact B2261251
  · exact B2261255
  · exact B2261259
  · exact B2261263
  · exact B2261267
  · exact B2261271
  · exact B2261275
  · exact B2261279
  · exact B2261283
  · exact B2261287
  · exact B2261291
  · exact B2261295
  · exact B2261299
  · exact B2261303
  · exact B2261307
  · exact B2261311
  · exact B2261315
  · exact B2261319
  · exact B2261323
  · exact B2261327
  · exact B2261331
  · exact B2261335
  · exact B2261339
  · exact B2261343
  · exact B2261347
  · exact B2261351
  · exact B2261355
  · exact B2261359
  · exact B2261363
  · exact B2261367
  · exact B2261371
  · exact B2261375
  · exact B2261379
  · exact B2261383
  · exact B2261387
  · exact B2261391
  · exact B2261395
  · exact B2261399
  · exact B2261403
  · exact B2261407
  · exact B2261411
  · exact B2261415
  · exact B2261419
  · exact B2261423
  · exact B2261427
  · exact B2261431
  · exact B2261435
theorem solution (m : ℕ) (hlo : 2259435 ≤ m) (hhi : m ≤ 2261435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 564858 ≤ j := by omega
    have hj2 : j ≤ 565358 := by omega
    have hb : Blo 2259435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
