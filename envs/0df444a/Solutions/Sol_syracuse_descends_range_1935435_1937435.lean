-- Prove2me | solution 1 for syracuse_descends_range_1935435_1937435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:26.425501+00:00
-- url     : https://prove2.me/submissions/a3e3b1f3-fb10-46ef-8d28-70086a72afa4

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

theorem B2177365 : Blo 1935435 2177365 := bbase (se 10 (by rfl) ⟨3189, by rfl⟩ : syracuseStep 2177365 = 6379) (by norm_num)
theorem B2903153 : Blo 1935435 2903153 := bstep (se 2 (by rfl) ⟨1088682, by rfl⟩ : syracuseStep 2903153 = 2177365) B2177365
theorem B1935435 : Blo 1935435 1935435 := bstep (se 1 (by rfl) ⟨1451576, by rfl⟩ : syracuseStep 1935435 = 2903153) B2903153
theorem B2449541 : Blo 1935435 2449541 := bbase (se 4 (by rfl) ⟨229644, by rfl⟩ : syracuseStep 2449541 = 459289) (by norm_num)
theorem B6532109 : Blo 1935435 6532109 := bstep (se 3 (by rfl) ⟨1224770, by rfl⟩ : syracuseStep 6532109 = 2449541) B2449541
theorem B4354739 : Blo 1935435 4354739 := bstep (se 1 (by rfl) ⟨3266054, by rfl⟩ : syracuseStep 4354739 = 6532109) B6532109
theorem B2903159 : Blo 1935435 2903159 := bstep (se 1 (by rfl) ⟨2177369, by rfl⟩ : syracuseStep 2903159 = 4354739) B4354739
theorem B1935439 : Blo 1935435 1935439 := bstep (se 1 (by rfl) ⟨1451579, by rfl⟩ : syracuseStep 1935439 = 2903159) B2903159
theorem B2903165 : Blo 1935435 2903165 := bbase (se 3 (by rfl) ⟨544343, by rfl⟩ : syracuseStep 2903165 = 1088687) (by norm_num)
theorem B1935443 : Blo 1935435 1935443 := bstep (se 1 (by rfl) ⟨1451582, by rfl⟩ : syracuseStep 1935443 = 2903165) B2903165
theorem B4354757 : Blo 1935435 4354757 := bbase (se 4 (by rfl) ⟨408258, by rfl⟩ : syracuseStep 4354757 = 816517) (by norm_num)
theorem B2903171 : Blo 1935435 2903171 := bstep (se 1 (by rfl) ⟨2177378, by rfl⟩ : syracuseStep 2903171 = 4354757) B4354757
theorem B1935447 : Blo 1935435 1935447 := bstep (se 1 (by rfl) ⟨1451585, by rfl⟩ : syracuseStep 1935447 = 2903171) B2903171
theorem B3310637 : Blo 1935435 3310637 := bbase (se 3 (by rfl) ⟨620744, by rfl⟩ : syracuseStep 3310637 = 1241489) (by norm_num)
theorem B8828365 : Blo 1935435 8828365 := bstep (se 3 (by rfl) ⟨1655318, by rfl⟩ : syracuseStep 8828365 = 3310637) B3310637
theorem B11771153 : Blo 1935435 11771153 := bstep (se 2 (by rfl) ⟨4414182, by rfl⟩ : syracuseStep 11771153 = 8828365) B8828365
theorem B7847435 : Blo 1935435 7847435 := bstep (se 1 (by rfl) ⟨5885576, by rfl⟩ : syracuseStep 7847435 = 11771153) B11771153
theorem B5231623 : Blo 1935435 5231623 := bstep (se 1 (by rfl) ⟨3923717, by rfl⟩ : syracuseStep 5231623 = 7847435) B7847435
theorem B6975497 : Blo 1935435 6975497 := bstep (se 2 (by rfl) ⟨2615811, by rfl⟩ : syracuseStep 6975497 = 5231623) B5231623
theorem B18601325 : Blo 1935435 18601325 := bstep (se 3 (by rfl) ⟨3487748, by rfl⟩ : syracuseStep 18601325 = 6975497) B6975497
theorem B12400883 : Blo 1935435 12400883 := bstep (se 1 (by rfl) ⟨9300662, by rfl⟩ : syracuseStep 12400883 = 18601325) B18601325
theorem B8267255 : Blo 1935435 8267255 := bstep (se 1 (by rfl) ⟨6200441, by rfl⟩ : syracuseStep 8267255 = 12400883) B12400883
theorem B5511503 : Blo 1935435 5511503 := bstep (se 1 (by rfl) ⟨4133627, by rfl⟩ : syracuseStep 5511503 = 8267255) B8267255
theorem B3674335 : Blo 1935435 3674335 := bstep (se 1 (by rfl) ⟨2755751, by rfl⟩ : syracuseStep 3674335 = 5511503) B5511503
theorem B4899113 : Blo 1935435 4899113 := bstep (se 2 (by rfl) ⟨1837167, by rfl⟩ : syracuseStep 4899113 = 3674335) B3674335
theorem B3266075 : Blo 1935435 3266075 := bstep (se 1 (by rfl) ⟨2449556, by rfl⟩ : syracuseStep 3266075 = 4899113) B4899113
theorem B2177383 : Blo 1935435 2177383 := bstep (se 1 (by rfl) ⟨1633037, by rfl⟩ : syracuseStep 2177383 = 3266075) B3266075
theorem B2903177 : Blo 1935435 2903177 := bstep (se 2 (by rfl) ⟨1088691, by rfl⟩ : syracuseStep 2903177 = 2177383) B2177383
theorem B1935451 : Blo 1935435 1935451 := bstep (se 1 (by rfl) ⟨1451588, by rfl⟩ : syracuseStep 1935451 = 2903177) B2903177
theorem B9798245 : Blo 1935435 9798245 := bbase (se 4 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 9798245 = 1837171) (by norm_num)
theorem B6532163 : Blo 1935435 6532163 := bstep (se 1 (by rfl) ⟨4899122, by rfl⟩ : syracuseStep 6532163 = 9798245) B9798245
theorem B4354775 : Blo 1935435 4354775 := bstep (se 1 (by rfl) ⟨3266081, by rfl⟩ : syracuseStep 4354775 = 6532163) B6532163
theorem B2903183 : Blo 1935435 2903183 := bstep (se 1 (by rfl) ⟨2177387, by rfl⟩ : syracuseStep 2903183 = 4354775) B4354775
theorem B1935455 : Blo 1935435 1935455 := bstep (se 1 (by rfl) ⟨1451591, by rfl⟩ : syracuseStep 1935455 = 2903183) B2903183
theorem B2903189 : Blo 1935435 2903189 := bbase (se 6 (by rfl) ⟨68043, by rfl⟩ : syracuseStep 2903189 = 136087) (by norm_num)
theorem B1935459 : Blo 1935435 1935459 := bstep (se 1 (by rfl) ⟨1451594, by rfl⟩ : syracuseStep 1935459 = 2903189) B2903189
theorem B2095025 : Blo 1935435 2095025 := bbase (se 2 (by rfl) ⟨785634, by rfl⟩ : syracuseStep 2095025 = 1571269) (by norm_num)
theorem B22346933 : Blo 1935435 22346933 := bstep (se 5 (by rfl) ⟨1047512, by rfl⟩ : syracuseStep 22346933 = 2095025) B2095025
theorem B59591821 : Blo 1935435 59591821 := bstep (se 3 (by rfl) ⟨11173466, by rfl⟩ : syracuseStep 59591821 = 22346933) B22346933
theorem B79455761 : Blo 1935435 79455761 := bstep (se 2 (by rfl) ⟨29795910, by rfl⟩ : syracuseStep 79455761 = 59591821) B59591821
theorem B52970507 : Blo 1935435 52970507 := bstep (se 1 (by rfl) ⟨39727880, by rfl⟩ : syracuseStep 52970507 = 79455761) B79455761
theorem B35313671 : Blo 1935435 35313671 := bstep (se 1 (by rfl) ⟨26485253, by rfl⟩ : syracuseStep 35313671 = 52970507) B52970507
theorem B23542447 : Blo 1935435 23542447 := bstep (se 1 (by rfl) ⟨17656835, by rfl⟩ : syracuseStep 23542447 = 35313671) B35313671
theorem B31389929 : Blo 1935435 31389929 := bstep (se 2 (by rfl) ⟨11771223, by rfl⟩ : syracuseStep 31389929 = 23542447) B23542447
theorem B20926619 : Blo 1935435 20926619 := bstep (se 1 (by rfl) ⟨15694964, by rfl⟩ : syracuseStep 20926619 = 31389929) B31389929
theorem B13951079 : Blo 1935435 13951079 := bstep (se 1 (by rfl) ⟨10463309, by rfl⟩ : syracuseStep 13951079 = 20926619) B20926619
theorem B9300719 : Blo 1935435 9300719 := bstep (se 1 (by rfl) ⟨6975539, by rfl⟩ : syracuseStep 9300719 = 13951079) B13951079
theorem B6200479 : Blo 1935435 6200479 := bstep (se 1 (by rfl) ⟨4650359, by rfl⟩ : syracuseStep 6200479 = 9300719) B9300719
theorem B8267305 : Blo 1935435 8267305 := bstep (se 2 (by rfl) ⟨3100239, by rfl⟩ : syracuseStep 8267305 = 6200479) B6200479
theorem B11023073 : Blo 1935435 11023073 := bstep (se 2 (by rfl) ⟨4133652, by rfl⟩ : syracuseStep 11023073 = 8267305) B8267305
theorem B7348715 : Blo 1935435 7348715 := bstep (se 1 (by rfl) ⟨5511536, by rfl⟩ : syracuseStep 7348715 = 11023073) B11023073
theorem B4899143 : Blo 1935435 4899143 := bstep (se 1 (by rfl) ⟨3674357, by rfl⟩ : syracuseStep 4899143 = 7348715) B7348715
theorem B3266095 : Blo 1935435 3266095 := bstep (se 1 (by rfl) ⟨2449571, by rfl⟩ : syracuseStep 3266095 = 4899143) B4899143
theorem B4354793 : Blo 1935435 4354793 := bstep (se 2 (by rfl) ⟨1633047, by rfl⟩ : syracuseStep 4354793 = 3266095) B3266095
theorem B2903195 : Blo 1935435 2903195 := bstep (se 1 (by rfl) ⟨2177396, by rfl⟩ : syracuseStep 2903195 = 4354793) B4354793
theorem B1935463 : Blo 1935435 1935463 := bstep (se 1 (by rfl) ⟨1451597, by rfl⟩ : syracuseStep 1935463 = 2903195) B2903195
theorem B2177401 : Blo 1935435 2177401 := bbase (se 2 (by rfl) ⟨816525, by rfl⟩ : syracuseStep 2177401 = 1633051) (by norm_num)
theorem B2903201 : Blo 1935435 2903201 := bstep (se 2 (by rfl) ⟨1088700, by rfl⟩ : syracuseStep 2903201 = 2177401) B2177401
theorem B1935467 : Blo 1935435 1935467 := bstep (se 1 (by rfl) ⟨1451600, by rfl⟩ : syracuseStep 1935467 = 2903201) B2903201
theorem B9300757 : Blo 1935435 9300757 := bbase (se 6 (by rfl) ⟨217986, by rfl⟩ : syracuseStep 9300757 = 435973) (by norm_num)
theorem B12401009 : Blo 1935435 12401009 := bstep (se 2 (by rfl) ⟨4650378, by rfl⟩ : syracuseStep 12401009 = 9300757) B9300757
theorem B8267339 : Blo 1935435 8267339 := bstep (se 1 (by rfl) ⟨6200504, by rfl⟩ : syracuseStep 8267339 = 12401009) B12401009
theorem B5511559 : Blo 1935435 5511559 := bstep (se 1 (by rfl) ⟨4133669, by rfl⟩ : syracuseStep 5511559 = 8267339) B8267339
theorem B7348745 : Blo 1935435 7348745 := bstep (se 2 (by rfl) ⟨2755779, by rfl⟩ : syracuseStep 7348745 = 5511559) B5511559
theorem B4899163 : Blo 1935435 4899163 := bstep (se 1 (by rfl) ⟨3674372, by rfl⟩ : syracuseStep 4899163 = 7348745) B7348745
theorem B6532217 : Blo 1935435 6532217 := bstep (se 2 (by rfl) ⟨2449581, by rfl⟩ : syracuseStep 6532217 = 4899163) B4899163
theorem B4354811 : Blo 1935435 4354811 := bstep (se 1 (by rfl) ⟨3266108, by rfl⟩ : syracuseStep 4354811 = 6532217) B6532217
theorem B2903207 : Blo 1935435 2903207 := bstep (se 1 (by rfl) ⟨2177405, by rfl⟩ : syracuseStep 2903207 = 4354811) B4354811
theorem B1935471 : Blo 1935435 1935471 := bstep (se 1 (by rfl) ⟨1451603, by rfl⟩ : syracuseStep 1935471 = 2903207) B2903207
theorem B2903213 : Blo 1935435 2903213 := bbase (se 3 (by rfl) ⟨544352, by rfl⟩ : syracuseStep 2903213 = 1088705) (by norm_num)
theorem B1935475 : Blo 1935435 1935475 := bstep (se 1 (by rfl) ⟨1451606, by rfl⟩ : syracuseStep 1935475 = 2903213) B2903213
theorem B4354829 : Blo 1935435 4354829 := bbase (se 3 (by rfl) ⟨816530, by rfl⟩ : syracuseStep 4354829 = 1633061) (by norm_num)
theorem B2903219 : Blo 1935435 2903219 := bstep (se 1 (by rfl) ⟨2177414, by rfl⟩ : syracuseStep 2903219 = 4354829) B4354829
theorem B1935479 : Blo 1935435 1935479 := bstep (se 1 (by rfl) ⟨1451609, by rfl⟩ : syracuseStep 1935479 = 2903219) B2903219
theorem B2449597 : Blo 1935435 2449597 := bbase (se 3 (by rfl) ⟨459299, by rfl⟩ : syracuseStep 2449597 = 918599) (by norm_num)
theorem B3266129 : Blo 1935435 3266129 := bstep (se 2 (by rfl) ⟨1224798, by rfl⟩ : syracuseStep 3266129 = 2449597) B2449597
theorem B2177419 : Blo 1935435 2177419 := bstep (se 1 (by rfl) ⟨1633064, by rfl⟩ : syracuseStep 2177419 = 3266129) B3266129
theorem B2903225 : Blo 1935435 2903225 := bstep (se 2 (by rfl) ⟨1088709, by rfl⟩ : syracuseStep 2903225 = 2177419) B2177419
theorem B1935483 : Blo 1935435 1935483 := bstep (se 1 (by rfl) ⟨1451612, by rfl⟩ : syracuseStep 1935483 = 2903225) B2903225
theorem B8948981 : Blo 1935435 8948981 := bbase (se 5 (by rfl) ⟨419483, by rfl⟩ : syracuseStep 8948981 = 838967) (by norm_num)
theorem B5965987 : Blo 1935435 5965987 := bstep (se 1 (by rfl) ⟨4474490, by rfl⟩ : syracuseStep 5965987 = 8948981) B8948981
theorem B7954649 : Blo 1935435 7954649 := bstep (se 2 (by rfl) ⟨2982993, by rfl⟩ : syracuseStep 7954649 = 5965987) B5965987
theorem B5303099 : Blo 1935435 5303099 := bstep (se 1 (by rfl) ⟨3977324, by rfl⟩ : syracuseStep 5303099 = 7954649) B7954649
theorem B3535399 : Blo 1935435 3535399 := bstep (se 1 (by rfl) ⟨2651549, by rfl⟩ : syracuseStep 3535399 = 5303099) B5303099
theorem B4713865 : Blo 1935435 4713865 := bstep (se 2 (by rfl) ⟨1767699, by rfl⟩ : syracuseStep 4713865 = 3535399) B3535399
theorem B25140613 : Blo 1935435 25140613 := bstep (se 4 (by rfl) ⟨2356932, by rfl⟩ : syracuseStep 25140613 = 4713865) B4713865
theorem B33520817 : Blo 1935435 33520817 := bstep (se 2 (by rfl) ⟨12570306, by rfl⟩ : syracuseStep 33520817 = 25140613) B25140613
theorem B22347211 : Blo 1935435 22347211 := bstep (se 1 (by rfl) ⟨16760408, by rfl⟩ : syracuseStep 22347211 = 33520817) B33520817
theorem B29796281 : Blo 1935435 29796281 := bstep (se 2 (by rfl) ⟨11173605, by rfl⟩ : syracuseStep 29796281 = 22347211) B22347211
theorem B19864187 : Blo 1935435 19864187 := bstep (se 1 (by rfl) ⟨14898140, by rfl⟩ : syracuseStep 19864187 = 29796281) B29796281
theorem B13242791 : Blo 1935435 13242791 := bstep (se 1 (by rfl) ⟨9932093, by rfl⟩ : syracuseStep 13242791 = 19864187) B19864187
theorem B8828527 : Blo 1935435 8828527 := bstep (se 1 (by rfl) ⟨6621395, by rfl⟩ : syracuseStep 8828527 = 13242791) B13242791
theorem B11771369 : Blo 1935435 11771369 := bstep (se 2 (by rfl) ⟨4414263, by rfl⟩ : syracuseStep 11771369 = 8828527) B8828527
theorem B7847579 : Blo 1935435 7847579 := bstep (se 1 (by rfl) ⟨5885684, by rfl⟩ : syracuseStep 7847579 = 11771369) B11771369
theorem B5231719 : Blo 1935435 5231719 := bstep (se 1 (by rfl) ⟨3923789, by rfl⟩ : syracuseStep 5231719 = 7847579) B7847579
theorem B6975625 : Blo 1935435 6975625 := bstep (se 2 (by rfl) ⟨2615859, by rfl⟩ : syracuseStep 6975625 = 5231719) B5231719
theorem B9300833 : Blo 1935435 9300833 := bstep (se 2 (by rfl) ⟨3487812, by rfl⟩ : syracuseStep 9300833 = 6975625) B6975625
theorem B6200555 : Blo 1935435 6200555 := bstep (se 1 (by rfl) ⟨4650416, by rfl⟩ : syracuseStep 6200555 = 9300833) B9300833
theorem B16534813 : Blo 1935435 16534813 := bstep (se 3 (by rfl) ⟨3100277, by rfl⟩ : syracuseStep 16534813 = 6200555) B6200555
theorem B22046417 : Blo 1935435 22046417 := bstep (se 2 (by rfl) ⟨8267406, by rfl⟩ : syracuseStep 22046417 = 16534813) B16534813
theorem B14697611 : Blo 1935435 14697611 := bstep (se 1 (by rfl) ⟨11023208, by rfl⟩ : syracuseStep 14697611 = 22046417) B22046417
theorem B9798407 : Blo 1935435 9798407 := bstep (se 1 (by rfl) ⟨7348805, by rfl⟩ : syracuseStep 9798407 = 14697611) B14697611
theorem B6532271 : Blo 1935435 6532271 := bstep (se 1 (by rfl) ⟨4899203, by rfl⟩ : syracuseStep 6532271 = 9798407) B9798407
theorem B4354847 : Blo 1935435 4354847 := bstep (se 1 (by rfl) ⟨3266135, by rfl⟩ : syracuseStep 4354847 = 6532271) B6532271
theorem B2903231 : Blo 1935435 2903231 := bstep (se 1 (by rfl) ⟨2177423, by rfl⟩ : syracuseStep 2903231 = 4354847) B4354847
theorem B1935487 : Blo 1935435 1935487 := bstep (se 1 (by rfl) ⟨1451615, by rfl⟩ : syracuseStep 1935487 = 2903231) B2903231
theorem B2903237 : Blo 1935435 2903237 := bbase (se 4 (by rfl) ⟨272178, by rfl⟩ : syracuseStep 2903237 = 544357) (by norm_num)
theorem B1935491 : Blo 1935435 1935491 := bstep (se 1 (by rfl) ⟨1451618, by rfl⟩ : syracuseStep 1935491 = 2903237) B2903237
theorem B3266149 : Blo 1935435 3266149 := bbase (se 4 (by rfl) ⟨306201, by rfl⟩ : syracuseStep 3266149 = 612403) (by norm_num)
theorem B4354865 : Blo 1935435 4354865 := bstep (se 2 (by rfl) ⟨1633074, by rfl⟩ : syracuseStep 4354865 = 3266149) B3266149
theorem B2903243 : Blo 1935435 2903243 := bstep (se 1 (by rfl) ⟨2177432, by rfl⟩ : syracuseStep 2903243 = 4354865) B4354865
theorem B1935495 : Blo 1935435 1935495 := bstep (se 1 (by rfl) ⟨1451621, by rfl⟩ : syracuseStep 1935495 = 2903243) B2903243
theorem B2177437 : Blo 1935435 2177437 := bbase (se 3 (by rfl) ⟨408269, by rfl⟩ : syracuseStep 2177437 = 816539) (by norm_num)
theorem B2903249 : Blo 1935435 2903249 := bstep (se 2 (by rfl) ⟨1088718, by rfl⟩ : syracuseStep 2903249 = 2177437) B2177437
theorem B1935499 : Blo 1935435 1935499 := bstep (se 1 (by rfl) ⟨1451624, by rfl⟩ : syracuseStep 1935499 = 2903249) B2903249
theorem B6532325 : Blo 1935435 6532325 := bbase (se 4 (by rfl) ⟨612405, by rfl⟩ : syracuseStep 6532325 = 1224811) (by norm_num)
theorem B4354883 : Blo 1935435 4354883 := bstep (se 1 (by rfl) ⟨3266162, by rfl⟩ : syracuseStep 4354883 = 6532325) B6532325
theorem B2903255 : Blo 1935435 2903255 := bstep (se 1 (by rfl) ⟨2177441, by rfl⟩ : syracuseStep 2903255 = 4354883) B4354883
theorem B1935503 : Blo 1935435 1935503 := bstep (se 1 (by rfl) ⟨1451627, by rfl⟩ : syracuseStep 1935503 = 2903255) B2903255
theorem B2903261 : Blo 1935435 2903261 := bbase (se 3 (by rfl) ⟨544361, by rfl⟩ : syracuseStep 2903261 = 1088723) (by norm_num)
theorem B1935507 : Blo 1935435 1935507 := bstep (se 1 (by rfl) ⟨1451630, by rfl⟩ : syracuseStep 1935507 = 2903261) B2903261
theorem B4354901 : Blo 1935435 4354901 := bbase (se 9 (by rfl) ⟨12758, by rfl⟩ : syracuseStep 4354901 = 25517) (by norm_num)
theorem B2903267 : Blo 1935435 2903267 := bstep (se 1 (by rfl) ⟨2177450, by rfl⟩ : syracuseStep 2903267 = 4354901) B4354901
theorem B1935511 : Blo 1935435 1935511 := bstep (se 1 (by rfl) ⟨1451633, by rfl⟩ : syracuseStep 1935511 = 2903267) B2903267
theorem B5511685 : Blo 1935435 5511685 := bbase (se 4 (by rfl) ⟨516720, by rfl⟩ : syracuseStep 5511685 = 1033441) (by norm_num)
theorem B7348913 : Blo 1935435 7348913 := bstep (se 2 (by rfl) ⟨2755842, by rfl⟩ : syracuseStep 7348913 = 5511685) B5511685
theorem B4899275 : Blo 1935435 4899275 := bstep (se 1 (by rfl) ⟨3674456, by rfl⟩ : syracuseStep 4899275 = 7348913) B7348913
theorem B3266183 : Blo 1935435 3266183 := bstep (se 1 (by rfl) ⟨2449637, by rfl⟩ : syracuseStep 3266183 = 4899275) B4899275
theorem B2177455 : Blo 1935435 2177455 := bstep (se 1 (by rfl) ⟨1633091, by rfl⟩ : syracuseStep 2177455 = 3266183) B3266183
theorem B2903273 : Blo 1935435 2903273 := bstep (se 2 (by rfl) ⟨1088727, by rfl⟩ : syracuseStep 2903273 = 2177455) B2177455
theorem B1935515 : Blo 1935435 1935515 := bstep (se 1 (by rfl) ⟨1451636, by rfl⟩ : syracuseStep 1935515 = 2903273) B2903273
theorem B2237281 : Blo 1935435 2237281 := bbase (se 2 (by rfl) ⟨838980, by rfl⟩ : syracuseStep 2237281 = 1677961) (by norm_num)
theorem B11932165 : Blo 1935435 11932165 := bstep (se 4 (by rfl) ⟨1118640, by rfl⟩ : syracuseStep 11932165 = 2237281) B2237281
theorem B15909553 : Blo 1935435 15909553 := bstep (se 2 (by rfl) ⟨5966082, by rfl⟩ : syracuseStep 15909553 = 11932165) B11932165
theorem B84850949 : Blo 1935435 84850949 := bstep (se 4 (by rfl) ⟨7954776, by rfl⟩ : syracuseStep 84850949 = 15909553) B15909553
theorem B226269197 : Blo 1935435 226269197 := bstep (se 3 (by rfl) ⟨42425474, by rfl⟩ : syracuseStep 226269197 = 84850949) B84850949
theorem B150846131 : Blo 1935435 150846131 := bstep (se 1 (by rfl) ⟨113134598, by rfl⟩ : syracuseStep 150846131 = 226269197) B226269197
theorem B100564087 : Blo 1935435 100564087 := bstep (se 1 (by rfl) ⟨75423065, by rfl⟩ : syracuseStep 100564087 = 150846131) B150846131
theorem B134085449 : Blo 1935435 134085449 := bstep (se 2 (by rfl) ⟨50282043, by rfl⟩ : syracuseStep 134085449 = 100564087) B100564087
theorem B89390299 : Blo 1935435 89390299 := bstep (se 1 (by rfl) ⟨67042724, by rfl⟩ : syracuseStep 89390299 = 134085449) B134085449
theorem B119187065 : Blo 1935435 119187065 := bstep (se 2 (by rfl) ⟨44695149, by rfl⟩ : syracuseStep 119187065 = 89390299) B89390299
theorem B79458043 : Blo 1935435 79458043 := bstep (se 1 (by rfl) ⟨59593532, by rfl⟩ : syracuseStep 79458043 = 119187065) B119187065
theorem B105944057 : Blo 1935435 105944057 := bstep (se 2 (by rfl) ⟨39729021, by rfl⟩ : syracuseStep 105944057 = 79458043) B79458043
theorem B70629371 : Blo 1935435 70629371 := bstep (se 1 (by rfl) ⟨52972028, by rfl⟩ : syracuseStep 70629371 = 105944057) B105944057
theorem B47086247 : Blo 1935435 47086247 := bstep (se 1 (by rfl) ⟨35314685, by rfl⟩ : syracuseStep 47086247 = 70629371) B70629371
theorem B31390831 : Blo 1935435 31390831 := bstep (se 1 (by rfl) ⟨23543123, by rfl⟩ : syracuseStep 31390831 = 47086247) B47086247
theorem B41854441 : Blo 1935435 41854441 := bstep (se 2 (by rfl) ⟨15695415, by rfl⟩ : syracuseStep 41854441 = 31390831) B31390831
theorem B55805921 : Blo 1935435 55805921 := bstep (se 2 (by rfl) ⟨20927220, by rfl⟩ : syracuseStep 55805921 = 41854441) B41854441
theorem B37203947 : Blo 1935435 37203947 := bstep (se 1 (by rfl) ⟨27902960, by rfl⟩ : syracuseStep 37203947 = 55805921) B55805921
theorem B24802631 : Blo 1935435 24802631 := bstep (se 1 (by rfl) ⟨18601973, by rfl⟩ : syracuseStep 24802631 = 37203947) B37203947
theorem B16535087 : Blo 1935435 16535087 := bstep (se 1 (by rfl) ⟨12401315, by rfl⟩ : syracuseStep 16535087 = 24802631) B24802631
theorem B11023391 : Blo 1935435 11023391 := bstep (se 1 (by rfl) ⟨8267543, by rfl⟩ : syracuseStep 11023391 = 16535087) B16535087
theorem B7348927 : Blo 1935435 7348927 := bstep (se 1 (by rfl) ⟨5511695, by rfl⟩ : syracuseStep 7348927 = 11023391) B11023391
theorem B9798569 : Blo 1935435 9798569 := bstep (se 2 (by rfl) ⟨3674463, by rfl⟩ : syracuseStep 9798569 = 7348927) B7348927
theorem B6532379 : Blo 1935435 6532379 := bstep (se 1 (by rfl) ⟨4899284, by rfl⟩ : syracuseStep 6532379 = 9798569) B9798569
theorem B4354919 : Blo 1935435 4354919 := bstep (se 1 (by rfl) ⟨3266189, by rfl⟩ : syracuseStep 4354919 = 6532379) B6532379
theorem B2903279 : Blo 1935435 2903279 := bstep (se 1 (by rfl) ⟨2177459, by rfl⟩ : syracuseStep 2903279 = 4354919) B4354919
theorem B1935519 : Blo 1935435 1935519 := bstep (se 1 (by rfl) ⟨1451639, by rfl⟩ : syracuseStep 1935519 = 2903279) B2903279
theorem B2903285 : Blo 1935435 2903285 := bbase (se 5 (by rfl) ⟨136091, by rfl⟩ : syracuseStep 2903285 = 272183) (by norm_num)
theorem B1935523 : Blo 1935435 1935523 := bstep (se 1 (by rfl) ⟨1451642, by rfl⟩ : syracuseStep 1935523 = 2903285) B2903285
theorem B13951541 : Blo 1935435 13951541 := bbase (se 5 (by rfl) ⟨653978, by rfl⟩ : syracuseStep 13951541 = 1307957) (by norm_num)
theorem B9301027 : Blo 1935435 9301027 := bstep (se 1 (by rfl) ⟨6975770, by rfl⟩ : syracuseStep 9301027 = 13951541) B13951541
theorem B12401369 : Blo 1935435 12401369 := bstep (se 2 (by rfl) ⟨4650513, by rfl⟩ : syracuseStep 12401369 = 9301027) B9301027
theorem B8267579 : Blo 1935435 8267579 := bstep (se 1 (by rfl) ⟨6200684, by rfl⟩ : syracuseStep 8267579 = 12401369) B12401369
theorem B5511719 : Blo 1935435 5511719 := bstep (se 1 (by rfl) ⟨4133789, by rfl⟩ : syracuseStep 5511719 = 8267579) B8267579
theorem B3674479 : Blo 1935435 3674479 := bstep (se 1 (by rfl) ⟨2755859, by rfl⟩ : syracuseStep 3674479 = 5511719) B5511719
theorem B4899305 : Blo 1935435 4899305 := bstep (se 2 (by rfl) ⟨1837239, by rfl⟩ : syracuseStep 4899305 = 3674479) B3674479
theorem B3266203 : Blo 1935435 3266203 := bstep (se 1 (by rfl) ⟨2449652, by rfl⟩ : syracuseStep 3266203 = 4899305) B4899305
theorem B4354937 : Blo 1935435 4354937 := bstep (se 2 (by rfl) ⟨1633101, by rfl⟩ : syracuseStep 4354937 = 3266203) B3266203
theorem B2903291 : Blo 1935435 2903291 := bstep (se 1 (by rfl) ⟨2177468, by rfl⟩ : syracuseStep 2903291 = 4354937) B4354937
theorem B1935527 : Blo 1935435 1935527 := bstep (se 1 (by rfl) ⟨1451645, by rfl⟩ : syracuseStep 1935527 = 2903291) B2903291
theorem B2177473 : Blo 1935435 2177473 := bbase (se 2 (by rfl) ⟨816552, by rfl⟩ : syracuseStep 2177473 = 1633105) (by norm_num)
theorem B2903297 : Blo 1935435 2903297 := bstep (se 2 (by rfl) ⟨1088736, by rfl⟩ : syracuseStep 2903297 = 2177473) B2177473
theorem B1935531 : Blo 1935435 1935531 := bstep (se 1 (by rfl) ⟨1451648, by rfl⟩ : syracuseStep 1935531 = 2903297) B2903297
theorem B4899325 : Blo 1935435 4899325 := bbase (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) (by norm_num)
theorem B6532433 : Blo 1935435 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B4354955 : Blo 1935435 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B2903303 : Blo 1935435 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B1935535 : Blo 1935435 1935535 := bstep (se 1 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 1935535 = 2903303) B2903303
theorem B2903309 : Blo 1935435 2903309 := bbase (se 3 (by rfl) ⟨544370, by rfl⟩ : syracuseStep 2903309 = 1088741) (by norm_num)
theorem B1935539 : Blo 1935435 1935539 := bstep (se 1 (by rfl) ⟨1451654, by rfl⟩ : syracuseStep 1935539 = 2903309) B2903309
theorem B4354973 : Blo 1935435 4354973 := bbase (se 3 (by rfl) ⟨816557, by rfl⟩ : syracuseStep 4354973 = 1633115) (by norm_num)
theorem B2903315 : Blo 1935435 2903315 := bstep (se 1 (by rfl) ⟨2177486, by rfl⟩ : syracuseStep 2903315 = 4354973) B4354973
theorem B1935543 : Blo 1935435 1935543 := bstep (se 1 (by rfl) ⟨1451657, by rfl⟩ : syracuseStep 1935543 = 2903315) B2903315
theorem B3266237 : Blo 1935435 3266237 := bbase (se 3 (by rfl) ⟨612419, by rfl⟩ : syracuseStep 3266237 = 1224839) (by norm_num)
theorem B2177491 : Blo 1935435 2177491 := bstep (se 1 (by rfl) ⟨1633118, by rfl⟩ : syracuseStep 2177491 = 3266237) B3266237
theorem B2903321 : Blo 1935435 2903321 := bstep (se 2 (by rfl) ⟨1088745, by rfl⟩ : syracuseStep 2903321 = 2177491) B2177491
theorem B1935547 : Blo 1935435 1935547 := bstep (se 1 (by rfl) ⟨1451660, by rfl⟩ : syracuseStep 1935547 = 2903321) B2903321
theorem B11023573 : Blo 1935435 11023573 := bbase (se 7 (by rfl) ⟨129182, by rfl⟩ : syracuseStep 11023573 = 258365) (by norm_num)
theorem B14698097 : Blo 1935435 14698097 := bstep (se 2 (by rfl) ⟨5511786, by rfl⟩ : syracuseStep 14698097 = 11023573) B11023573
theorem B9798731 : Blo 1935435 9798731 := bstep (se 1 (by rfl) ⟨7349048, by rfl⟩ : syracuseStep 9798731 = 14698097) B14698097
theorem B6532487 : Blo 1935435 6532487 := bstep (se 1 (by rfl) ⟨4899365, by rfl⟩ : syracuseStep 6532487 = 9798731) B9798731
theorem B4354991 : Blo 1935435 4354991 := bstep (se 1 (by rfl) ⟨3266243, by rfl⟩ : syracuseStep 4354991 = 6532487) B6532487
theorem B2903327 : Blo 1935435 2903327 := bstep (se 1 (by rfl) ⟨2177495, by rfl⟩ : syracuseStep 2903327 = 4354991) B4354991
theorem B1935551 : Blo 1935435 1935551 := bstep (se 1 (by rfl) ⟨1451663, by rfl⟩ : syracuseStep 1935551 = 2903327) B2903327
theorem B2903333 : Blo 1935435 2903333 := bbase (se 4 (by rfl) ⟨272187, by rfl⟩ : syracuseStep 2903333 = 544375) (by norm_num)
theorem B1935555 : Blo 1935435 1935555 := bstep (se 1 (by rfl) ⟨1451666, by rfl⟩ : syracuseStep 1935555 = 2903333) B2903333
theorem B2449693 : Blo 1935435 2449693 := bbase (se 3 (by rfl) ⟨459317, by rfl⟩ : syracuseStep 2449693 = 918635) (by norm_num)
theorem B3266257 : Blo 1935435 3266257 := bstep (se 2 (by rfl) ⟨1224846, by rfl⟩ : syracuseStep 3266257 = 2449693) B2449693
theorem B4355009 : Blo 1935435 4355009 := bstep (se 2 (by rfl) ⟨1633128, by rfl⟩ : syracuseStep 4355009 = 3266257) B3266257
theorem B2903339 : Blo 1935435 2903339 := bstep (se 1 (by rfl) ⟨2177504, by rfl⟩ : syracuseStep 2903339 = 4355009) B4355009
theorem B1935559 : Blo 1935435 1935559 := bstep (se 1 (by rfl) ⟨1451669, by rfl⟩ : syracuseStep 1935559 = 2903339) B2903339
theorem B2177509 : Blo 1935435 2177509 := bbase (se 4 (by rfl) ⟨204141, by rfl⟩ : syracuseStep 2177509 = 408283) (by norm_num)
theorem B2903345 : Blo 1935435 2903345 := bstep (se 2 (by rfl) ⟨1088754, by rfl⟩ : syracuseStep 2903345 = 2177509) B2177509
theorem B1935563 : Blo 1935435 1935563 := bstep (se 1 (by rfl) ⟨1451672, by rfl⟩ : syracuseStep 1935563 = 2903345) B2903345
theorem B2325305 : Blo 1935435 2325305 := bbase (se 2 (by rfl) ⟨871989, by rfl⟩ : syracuseStep 2325305 = 1743979) (by norm_num)
theorem B6200813 : Blo 1935435 6200813 := bstep (se 3 (by rfl) ⟨1162652, by rfl⟩ : syracuseStep 6200813 = 2325305) B2325305
theorem B4133875 : Blo 1935435 4133875 := bstep (se 1 (by rfl) ⟨3100406, by rfl⟩ : syracuseStep 4133875 = 6200813) B6200813
theorem B5511833 : Blo 1935435 5511833 := bstep (se 2 (by rfl) ⟨2066937, by rfl⟩ : syracuseStep 5511833 = 4133875) B4133875
theorem B3674555 : Blo 1935435 3674555 := bstep (se 1 (by rfl) ⟨2755916, by rfl⟩ : syracuseStep 3674555 = 5511833) B5511833
theorem B2449703 : Blo 1935435 2449703 := bstep (se 1 (by rfl) ⟨1837277, by rfl⟩ : syracuseStep 2449703 = 3674555) B3674555
theorem B6532541 : Blo 1935435 6532541 := bstep (se 3 (by rfl) ⟨1224851, by rfl⟩ : syracuseStep 6532541 = 2449703) B2449703
theorem B4355027 : Blo 1935435 4355027 := bstep (se 1 (by rfl) ⟨3266270, by rfl⟩ : syracuseStep 4355027 = 6532541) B6532541
theorem B2903351 : Blo 1935435 2903351 := bstep (se 1 (by rfl) ⟨2177513, by rfl⟩ : syracuseStep 2903351 = 4355027) B4355027
theorem B1935567 : Blo 1935435 1935567 := bstep (se 1 (by rfl) ⟨1451675, by rfl⟩ : syracuseStep 1935567 = 2903351) B2903351
theorem B2903357 : Blo 1935435 2903357 := bbase (se 3 (by rfl) ⟨544379, by rfl⟩ : syracuseStep 2903357 = 1088759) (by norm_num)
theorem B1935571 : Blo 1935435 1935571 := bstep (se 1 (by rfl) ⟨1451678, by rfl⟩ : syracuseStep 1935571 = 2903357) B2903357
theorem B4355045 : Blo 1935435 4355045 := bbase (se 4 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 4355045 = 816571) (by norm_num)
theorem B2903363 : Blo 1935435 2903363 := bstep (se 1 (by rfl) ⟨2177522, by rfl⟩ : syracuseStep 2903363 = 4355045) B4355045
theorem B1935575 : Blo 1935435 1935575 := bstep (se 1 (by rfl) ⟨1451681, by rfl⟩ : syracuseStep 1935575 = 2903363) B2903363
theorem B4899437 : Blo 1935435 4899437 := bbase (se 3 (by rfl) ⟨918644, by rfl⟩ : syracuseStep 4899437 = 1837289) (by norm_num)
theorem B3266291 : Blo 1935435 3266291 := bstep (se 1 (by rfl) ⟨2449718, by rfl⟩ : syracuseStep 3266291 = 4899437) B4899437
theorem B2177527 : Blo 1935435 2177527 := bstep (se 1 (by rfl) ⟨1633145, by rfl⟩ : syracuseStep 2177527 = 3266291) B3266291
theorem B2903369 : Blo 1935435 2903369 := bstep (se 2 (by rfl) ⟨1088763, by rfl⟩ : syracuseStep 2903369 = 2177527) B2177527
theorem B1935579 : Blo 1935435 1935579 := bstep (se 1 (by rfl) ⟨1451684, by rfl⟩ : syracuseStep 1935579 = 2903369) B2903369
theorem B4133909 : Blo 1935435 4133909 := bbase (se 6 (by rfl) ⟨96888, by rfl⟩ : syracuseStep 4133909 = 193777) (by norm_num)
theorem B2755939 : Blo 1935435 2755939 := bstep (se 1 (by rfl) ⟨2066954, by rfl⟩ : syracuseStep 2755939 = 4133909) B4133909
theorem B3674585 : Blo 1935435 3674585 := bstep (se 2 (by rfl) ⟨1377969, by rfl⟩ : syracuseStep 3674585 = 2755939) B2755939
theorem B9798893 : Blo 1935435 9798893 := bstep (se 3 (by rfl) ⟨1837292, by rfl⟩ : syracuseStep 9798893 = 3674585) B3674585
theorem B6532595 : Blo 1935435 6532595 := bstep (se 1 (by rfl) ⟨4899446, by rfl⟩ : syracuseStep 6532595 = 9798893) B9798893
theorem B4355063 : Blo 1935435 4355063 := bstep (se 1 (by rfl) ⟨3266297, by rfl⟩ : syracuseStep 4355063 = 6532595) B6532595
theorem B2903375 : Blo 1935435 2903375 := bstep (se 1 (by rfl) ⟨2177531, by rfl⟩ : syracuseStep 2903375 = 4355063) B4355063
theorem B1935583 : Blo 1935435 1935583 := bstep (se 1 (by rfl) ⟨1451687, by rfl⟩ : syracuseStep 1935583 = 2903375) B2903375
theorem B2903381 : Blo 1935435 2903381 := bbase (se 11 (by rfl) ⟨2126, by rfl⟩ : syracuseStep 2903381 = 4253) (by norm_num)
theorem B1935587 : Blo 1935435 1935587 := bstep (se 1 (by rfl) ⟨1451690, by rfl⟩ : syracuseStep 1935587 = 2903381) B2903381
theorem B3100445 : Blo 1935435 3100445 := bbase (se 3 (by rfl) ⟨581333, by rfl⟩ : syracuseStep 3100445 = 1162667) (by norm_num)
theorem B2066963 : Blo 1935435 2066963 := bstep (se 1 (by rfl) ⟨1550222, by rfl⟩ : syracuseStep 2066963 = 3100445) B3100445
theorem B5511901 : Blo 1935435 5511901 := bstep (se 3 (by rfl) ⟨1033481, by rfl⟩ : syracuseStep 5511901 = 2066963) B2066963
theorem B7349201 : Blo 1935435 7349201 := bstep (se 2 (by rfl) ⟨2755950, by rfl⟩ : syracuseStep 7349201 = 5511901) B5511901
theorem B4899467 : Blo 1935435 4899467 := bstep (se 1 (by rfl) ⟨3674600, by rfl⟩ : syracuseStep 4899467 = 7349201) B7349201
theorem B3266311 : Blo 1935435 3266311 := bstep (se 1 (by rfl) ⟨2449733, by rfl⟩ : syracuseStep 3266311 = 4899467) B4899467
theorem B4355081 : Blo 1935435 4355081 := bstep (se 2 (by rfl) ⟨1633155, by rfl⟩ : syracuseStep 4355081 = 3266311) B3266311
theorem B2903387 : Blo 1935435 2903387 := bstep (se 1 (by rfl) ⟨2177540, by rfl⟩ : syracuseStep 2903387 = 4355081) B4355081
theorem B1935591 : Blo 1935435 1935591 := bstep (se 1 (by rfl) ⟨1451693, by rfl⟩ : syracuseStep 1935591 = 2903387) B2903387
theorem B2177545 : Blo 1935435 2177545 := bbase (se 2 (by rfl) ⟨816579, by rfl⟩ : syracuseStep 2177545 = 1633159) (by norm_num)
theorem B2903393 : Blo 1935435 2903393 := bstep (se 2 (by rfl) ⟨1088772, by rfl⟩ : syracuseStep 2903393 = 2177545) B2177545
theorem B1935595 : Blo 1935435 1935595 := bstep (se 1 (by rfl) ⟨1451696, by rfl⟩ : syracuseStep 1935595 = 2903393) B2903393
theorem B16990069 : Blo 1935435 16990069 := bbase (se 5 (by rfl) ⟨796409, by rfl⟩ : syracuseStep 16990069 = 1592819) (by norm_num)
theorem B22653425 : Blo 1935435 22653425 := bstep (se 2 (by rfl) ⟨8495034, by rfl⟩ : syracuseStep 22653425 = 16990069) B16990069
theorem B15102283 : Blo 1935435 15102283 := bstep (se 1 (by rfl) ⟨11326712, by rfl⟩ : syracuseStep 15102283 = 22653425) B22653425
theorem B20136377 : Blo 1935435 20136377 := bstep (se 2 (by rfl) ⟨7551141, by rfl⟩ : syracuseStep 20136377 = 15102283) B15102283
theorem B13424251 : Blo 1935435 13424251 := bstep (se 1 (by rfl) ⟨10068188, by rfl⟩ : syracuseStep 13424251 = 20136377) B20136377
theorem B17899001 : Blo 1935435 17899001 := bstep (se 2 (by rfl) ⟨6712125, by rfl⟩ : syracuseStep 17899001 = 13424251) B13424251
theorem B11932667 : Blo 1935435 11932667 := bstep (se 1 (by rfl) ⟨8949500, by rfl⟩ : syracuseStep 11932667 = 17899001) B17899001
theorem B7955111 : Blo 1935435 7955111 := bstep (se 1 (by rfl) ⟨5966333, by rfl⟩ : syracuseStep 7955111 = 11932667) B11932667
theorem B5303407 : Blo 1935435 5303407 := bstep (se 1 (by rfl) ⟨3977555, by rfl⟩ : syracuseStep 5303407 = 7955111) B7955111
theorem B7071209 : Blo 1935435 7071209 := bstep (se 2 (by rfl) ⟨2651703, by rfl⟩ : syracuseStep 7071209 = 5303407) B5303407
theorem B4714139 : Blo 1935435 4714139 := bstep (se 1 (by rfl) ⟨3535604, by rfl⟩ : syracuseStep 4714139 = 7071209) B7071209
theorem B12571037 : Blo 1935435 12571037 := bstep (se 3 (by rfl) ⟨2357069, by rfl⟩ : syracuseStep 12571037 = 4714139) B4714139
theorem B8380691 : Blo 1935435 8380691 := bstep (se 1 (by rfl) ⟨6285518, by rfl⟩ : syracuseStep 8380691 = 12571037) B12571037
theorem B5587127 : Blo 1935435 5587127 := bstep (se 1 (by rfl) ⟨4190345, by rfl⟩ : syracuseStep 5587127 = 8380691) B8380691
theorem B3724751 : Blo 1935435 3724751 := bstep (se 1 (by rfl) ⟨2793563, by rfl⟩ : syracuseStep 3724751 = 5587127) B5587127
theorem B2483167 : Blo 1935435 2483167 := bstep (se 1 (by rfl) ⟨1862375, by rfl⟩ : syracuseStep 2483167 = 3724751) B3724751
theorem B3310889 : Blo 1935435 3310889 := bstep (se 2 (by rfl) ⟨1241583, by rfl⟩ : syracuseStep 3310889 = 2483167) B2483167
theorem B8829037 : Blo 1935435 8829037 := bstep (se 3 (by rfl) ⟨1655444, by rfl⟩ : syracuseStep 8829037 = 3310889) B3310889
theorem B11772049 : Blo 1935435 11772049 := bstep (se 2 (by rfl) ⟨4414518, by rfl⟩ : syracuseStep 11772049 = 8829037) B8829037
theorem B15696065 : Blo 1935435 15696065 := bstep (se 2 (by rfl) ⟨5886024, by rfl⟩ : syracuseStep 15696065 = 11772049) B11772049
theorem B41856173 : Blo 1935435 41856173 := bstep (se 3 (by rfl) ⟨7848032, by rfl⟩ : syracuseStep 41856173 = 15696065) B15696065
theorem B27904115 : Blo 1935435 27904115 := bstep (se 1 (by rfl) ⟨20928086, by rfl⟩ : syracuseStep 27904115 = 41856173) B41856173
theorem B18602743 : Blo 1935435 18602743 := bstep (se 1 (by rfl) ⟨13952057, by rfl⟩ : syracuseStep 18602743 = 27904115) B27904115
theorem B24803657 : Blo 1935435 24803657 := bstep (se 2 (by rfl) ⟨9301371, by rfl⟩ : syracuseStep 24803657 = 18602743) B18602743
theorem B16535771 : Blo 1935435 16535771 := bstep (se 1 (by rfl) ⟨12401828, by rfl⟩ : syracuseStep 16535771 = 24803657) B24803657
theorem B11023847 : Blo 1935435 11023847 := bstep (se 1 (by rfl) ⟨8267885, by rfl⟩ : syracuseStep 11023847 = 16535771) B16535771
theorem B7349231 : Blo 1935435 7349231 := bstep (se 1 (by rfl) ⟨5511923, by rfl⟩ : syracuseStep 7349231 = 11023847) B11023847
theorem B4899487 : Blo 1935435 4899487 := bstep (se 1 (by rfl) ⟨3674615, by rfl⟩ : syracuseStep 4899487 = 7349231) B7349231
theorem B6532649 : Blo 1935435 6532649 := bstep (se 2 (by rfl) ⟨2449743, by rfl⟩ : syracuseStep 6532649 = 4899487) B4899487
theorem B4355099 : Blo 1935435 4355099 := bstep (se 1 (by rfl) ⟨3266324, by rfl⟩ : syracuseStep 4355099 = 6532649) B6532649
theorem B2903399 : Blo 1935435 2903399 := bstep (se 1 (by rfl) ⟨2177549, by rfl⟩ : syracuseStep 2903399 = 4355099) B4355099
theorem B1935599 : Blo 1935435 1935599 := bstep (se 1 (by rfl) ⟨1451699, by rfl⟩ : syracuseStep 1935599 = 2903399) B2903399
theorem B2903405 : Blo 1935435 2903405 := bbase (se 3 (by rfl) ⟨544388, by rfl⟩ : syracuseStep 2903405 = 1088777) (by norm_num)
theorem B1935603 : Blo 1935435 1935603 := bstep (se 1 (by rfl) ⟨1451702, by rfl⟩ : syracuseStep 1935603 = 2903405) B2903405
theorem B4355117 : Blo 1935435 4355117 := bbase (se 3 (by rfl) ⟨816584, by rfl⟩ : syracuseStep 4355117 = 1633169) (by norm_num)
theorem B2903411 : Blo 1935435 2903411 := bstep (se 1 (by rfl) ⟨2177558, by rfl⟩ : syracuseStep 2903411 = 4355117) B4355117
theorem B1935607 : Blo 1935435 1935607 := bstep (se 1 (by rfl) ⟨1451705, by rfl⟩ : syracuseStep 1935607 = 2903411) B2903411
theorem B12401909 : Blo 1935435 12401909 := bbase (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) (by norm_num)
theorem B8267939 : Blo 1935435 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B5511959 : Blo 1935435 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B3674639 : Blo 1935435 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B2449759 : Blo 1935435 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B3266345 : Blo 1935435 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B2177563 : Blo 1935435 2177563 := bstep (se 1 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 2177563 = 3266345) B3266345
theorem B2903417 : Blo 1935435 2903417 := bstep (se 2 (by rfl) ⟨1088781, by rfl⟩ : syracuseStep 2903417 = 2177563) B2177563
theorem B1935611 : Blo 1935435 1935611 := bstep (se 1 (by rfl) ⟨1451708, by rfl⟩ : syracuseStep 1935611 = 2903417) B2903417
theorem B6200965 : Blo 1935435 6200965 := bbase (se 4 (by rfl) ⟨581340, by rfl⟩ : syracuseStep 6200965 = 1162681) (by norm_num)
theorem B33071813 : Blo 1935435 33071813 := bstep (se 4 (by rfl) ⟨3100482, by rfl⟩ : syracuseStep 33071813 = 6200965) B6200965
theorem B22047875 : Blo 1935435 22047875 := bstep (se 1 (by rfl) ⟨16535906, by rfl⟩ : syracuseStep 22047875 = 33071813) B33071813
theorem B14698583 : Blo 1935435 14698583 := bstep (se 1 (by rfl) ⟨11023937, by rfl⟩ : syracuseStep 14698583 = 22047875) B22047875
theorem B9799055 : Blo 1935435 9799055 := bstep (se 1 (by rfl) ⟨7349291, by rfl⟩ : syracuseStep 9799055 = 14698583) B14698583
theorem B6532703 : Blo 1935435 6532703 := bstep (se 1 (by rfl) ⟨4899527, by rfl⟩ : syracuseStep 6532703 = 9799055) B9799055
theorem B4355135 : Blo 1935435 4355135 := bstep (se 1 (by rfl) ⟨3266351, by rfl⟩ : syracuseStep 4355135 = 6532703) B6532703
theorem B2903423 : Blo 1935435 2903423 := bstep (se 1 (by rfl) ⟨2177567, by rfl⟩ : syracuseStep 2903423 = 4355135) B4355135
theorem B1935615 : Blo 1935435 1935615 := bstep (se 1 (by rfl) ⟨1451711, by rfl⟩ : syracuseStep 1935615 = 2903423) B2903423
theorem B2903429 : Blo 1935435 2903429 := bbase (se 4 (by rfl) ⟨272196, by rfl⟩ : syracuseStep 2903429 = 544393) (by norm_num)
theorem B1935619 : Blo 1935435 1935619 := bstep (se 1 (by rfl) ⟨1451714, by rfl⟩ : syracuseStep 1935619 = 2903429) B2903429
theorem B3266365 : Blo 1935435 3266365 := bbase (se 3 (by rfl) ⟨612443, by rfl⟩ : syracuseStep 3266365 = 1224887) (by norm_num)
theorem B4355153 : Blo 1935435 4355153 := bstep (se 2 (by rfl) ⟨1633182, by rfl⟩ : syracuseStep 4355153 = 3266365) B3266365
theorem B2903435 : Blo 1935435 2903435 := bstep (se 1 (by rfl) ⟨2177576, by rfl⟩ : syracuseStep 2903435 = 4355153) B4355153
theorem B1935623 : Blo 1935435 1935623 := bstep (se 1 (by rfl) ⟨1451717, by rfl⟩ : syracuseStep 1935623 = 2903435) B2903435
theorem B2177581 : Blo 1935435 2177581 := bbase (se 3 (by rfl) ⟨408296, by rfl⟩ : syracuseStep 2177581 = 816593) (by norm_num)
theorem B2903441 : Blo 1935435 2903441 := bstep (se 2 (by rfl) ⟨1088790, by rfl⟩ : syracuseStep 2903441 = 2177581) B2177581
theorem B1935627 : Blo 1935435 1935627 := bstep (se 1 (by rfl) ⟨1451720, by rfl⟩ : syracuseStep 1935627 = 2903441) B2903441
theorem B6532757 : Blo 1935435 6532757 := bbase (se 6 (by rfl) ⟨153111, by rfl⟩ : syracuseStep 6532757 = 306223) (by norm_num)
theorem B4355171 : Blo 1935435 4355171 := bstep (se 1 (by rfl) ⟨3266378, by rfl⟩ : syracuseStep 4355171 = 6532757) B6532757
theorem B2903447 : Blo 1935435 2903447 := bstep (se 1 (by rfl) ⟨2177585, by rfl⟩ : syracuseStep 2903447 = 4355171) B4355171
theorem B1935631 : Blo 1935435 1935631 := bstep (se 1 (by rfl) ⟨1451723, by rfl⟩ : syracuseStep 1935631 = 2903447) B2903447
theorem B2903453 : Blo 1935435 2903453 := bbase (se 3 (by rfl) ⟨544397, by rfl⟩ : syracuseStep 2903453 = 1088795) (by norm_num)
theorem B1935635 : Blo 1935435 1935635 := bstep (se 1 (by rfl) ⟨1451726, by rfl⟩ : syracuseStep 1935635 = 2903453) B2903453
theorem B4355189 : Blo 1935435 4355189 := bbase (se 5 (by rfl) ⟨204149, by rfl⟩ : syracuseStep 4355189 = 408299) (by norm_num)
theorem B2903459 : Blo 1935435 2903459 := bstep (se 1 (by rfl) ⟨2177594, by rfl⟩ : syracuseStep 2903459 = 4355189) B4355189
theorem B1935639 : Blo 1935435 1935639 := bstep (se 1 (by rfl) ⟨1451729, by rfl⟩ : syracuseStep 1935639 = 2903459) B2903459
theorem B16536149 : Blo 1935435 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B11024099 : Blo 1935435 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B7349399 : Blo 1935435 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B4899599 : Blo 1935435 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B3266399 : Blo 1935435 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B2177599 : Blo 1935435 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B2903465 : Blo 1935435 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B1935643 : Blo 1935435 1935643 := bstep (se 1 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 1935643 = 2903465) B2903465
theorem B7349413 : Blo 1935435 7349413 := bbase (se 4 (by rfl) ⟨689007, by rfl⟩ : syracuseStep 7349413 = 1378015) (by norm_num)
theorem B9799217 : Blo 1935435 9799217 := bstep (se 2 (by rfl) ⟨3674706, by rfl⟩ : syracuseStep 9799217 = 7349413) B7349413
theorem B6532811 : Blo 1935435 6532811 := bstep (se 1 (by rfl) ⟨4899608, by rfl⟩ : syracuseStep 6532811 = 9799217) B9799217
theorem B4355207 : Blo 1935435 4355207 := bstep (se 1 (by rfl) ⟨3266405, by rfl⟩ : syracuseStep 4355207 = 6532811) B6532811
theorem B2903471 : Blo 1935435 2903471 := bstep (se 1 (by rfl) ⟨2177603, by rfl⟩ : syracuseStep 2903471 = 4355207) B4355207
theorem B1935647 : Blo 1935435 1935647 := bstep (se 1 (by rfl) ⟨1451735, by rfl⟩ : syracuseStep 1935647 = 2903471) B2903471
theorem B2903477 : Blo 1935435 2903477 := bbase (se 5 (by rfl) ⟨136100, by rfl⟩ : syracuseStep 2903477 = 272201) (by norm_num)
theorem B1935651 : Blo 1935435 1935651 := bstep (se 1 (by rfl) ⟨1451738, by rfl⟩ : syracuseStep 1935651 = 2903477) B2903477
theorem B4899629 : Blo 1935435 4899629 := bbase (se 3 (by rfl) ⟨918680, by rfl⟩ : syracuseStep 4899629 = 1837361) (by norm_num)
theorem B3266419 : Blo 1935435 3266419 := bstep (se 1 (by rfl) ⟨2449814, by rfl⟩ : syracuseStep 3266419 = 4899629) B4899629
theorem B4355225 : Blo 1935435 4355225 := bstep (se 2 (by rfl) ⟨1633209, by rfl⟩ : syracuseStep 4355225 = 3266419) B3266419
theorem B2903483 : Blo 1935435 2903483 := bstep (se 1 (by rfl) ⟨2177612, by rfl⟩ : syracuseStep 2903483 = 4355225) B4355225
theorem B1935655 : Blo 1935435 1935655 := bstep (se 1 (by rfl) ⟨1451741, by rfl⟩ : syracuseStep 1935655 = 2903483) B2903483
theorem B2177617 : Blo 1935435 2177617 := bbase (se 2 (by rfl) ⟨816606, by rfl⟩ : syracuseStep 2177617 = 1633213) (by norm_num)
theorem B2903489 : Blo 1935435 2903489 := bstep (se 2 (by rfl) ⟨1088808, by rfl⟩ : syracuseStep 2903489 = 2177617) B2177617
theorem B1935659 : Blo 1935435 1935659 := bstep (se 1 (by rfl) ⟨1451744, by rfl⟩ : syracuseStep 1935659 = 2903489) B2903489
theorem B2756053 : Blo 1935435 2756053 := bbase (se 7 (by rfl) ⟨32297, by rfl⟩ : syracuseStep 2756053 = 64595) (by norm_num)
theorem B3674737 : Blo 1935435 3674737 := bstep (se 2 (by rfl) ⟨1378026, by rfl⟩ : syracuseStep 3674737 = 2756053) B2756053
theorem B4899649 : Blo 1935435 4899649 := bstep (se 2 (by rfl) ⟨1837368, by rfl⟩ : syracuseStep 4899649 = 3674737) B3674737
theorem B6532865 : Blo 1935435 6532865 := bstep (se 2 (by rfl) ⟨2449824, by rfl⟩ : syracuseStep 6532865 = 4899649) B4899649
theorem B4355243 : Blo 1935435 4355243 := bstep (se 1 (by rfl) ⟨3266432, by rfl⟩ : syracuseStep 4355243 = 6532865) B6532865
theorem B2903495 : Blo 1935435 2903495 := bstep (se 1 (by rfl) ⟨2177621, by rfl⟩ : syracuseStep 2903495 = 4355243) B4355243
theorem B1935663 : Blo 1935435 1935663 := bstep (se 1 (by rfl) ⟨1451747, by rfl⟩ : syracuseStep 1935663 = 2903495) B2903495
theorem B2903501 : Blo 1935435 2903501 := bbase (se 3 (by rfl) ⟨544406, by rfl⟩ : syracuseStep 2903501 = 1088813) (by norm_num)
theorem B1935667 : Blo 1935435 1935667 := bstep (se 1 (by rfl) ⟨1451750, by rfl⟩ : syracuseStep 1935667 = 2903501) B2903501
theorem B4355261 : Blo 1935435 4355261 := bbase (se 3 (by rfl) ⟨816611, by rfl⟩ : syracuseStep 4355261 = 1633223) (by norm_num)
theorem B2903507 : Blo 1935435 2903507 := bstep (se 1 (by rfl) ⟨2177630, by rfl⟩ : syracuseStep 2903507 = 4355261) B4355261
theorem B1935671 : Blo 1935435 1935671 := bstep (se 1 (by rfl) ⟨1451753, by rfl⟩ : syracuseStep 1935671 = 2903507) B2903507
theorem B3266453 : Blo 1935435 3266453 := bbase (se 6 (by rfl) ⟨76557, by rfl⟩ : syracuseStep 3266453 = 153115) (by norm_num)
theorem B2177635 : Blo 1935435 2177635 := bstep (se 1 (by rfl) ⟨1633226, by rfl⟩ : syracuseStep 2177635 = 3266453) B3266453
theorem B2903513 : Blo 1935435 2903513 := bstep (se 2 (by rfl) ⟨1088817, by rfl⟩ : syracuseStep 2903513 = 2177635) B2177635
theorem B1935675 : Blo 1935435 1935675 := bstep (se 1 (by rfl) ⟨1451756, by rfl⟩ : syracuseStep 1935675 = 2903513) B2903513
theorem B5966581 : Blo 1935435 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B7955441 : Blo 1935435 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B5303627 : Blo 1935435 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B3535751 : Blo 1935435 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B9428669 : Blo 1935435 9428669 := bstep (se 3 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 9428669 = 3535751) B3535751
theorem B6285779 : Blo 1935435 6285779 := bstep (se 1 (by rfl) ⟨4714334, by rfl⟩ : syracuseStep 6285779 = 9428669) B9428669
theorem B4190519 : Blo 1935435 4190519 := bstep (se 1 (by rfl) ⟨3142889, by rfl⟩ : syracuseStep 4190519 = 6285779) B6285779
theorem B2793679 : Blo 1935435 2793679 := bstep (se 1 (by rfl) ⟨2095259, by rfl⟩ : syracuseStep 2793679 = 4190519) B4190519
theorem B14899621 : Blo 1935435 14899621 := bstep (se 4 (by rfl) ⟨1396839, by rfl⟩ : syracuseStep 14899621 = 2793679) B2793679
theorem B19866161 : Blo 1935435 19866161 := bstep (se 2 (by rfl) ⟨7449810, by rfl⟩ : syracuseStep 19866161 = 14899621) B14899621
theorem B13244107 : Blo 1935435 13244107 := bstep (se 1 (by rfl) ⟨9933080, by rfl⟩ : syracuseStep 13244107 = 19866161) B19866161
theorem B17658809 : Blo 1935435 17658809 := bstep (se 2 (by rfl) ⟨6622053, by rfl⟩ : syracuseStep 17658809 = 13244107) B13244107
theorem B11772539 : Blo 1935435 11772539 := bstep (se 1 (by rfl) ⟨8829404, by rfl⟩ : syracuseStep 11772539 = 17658809) B17658809
theorem B7848359 : Blo 1935435 7848359 := bstep (se 1 (by rfl) ⟨5886269, by rfl⟩ : syracuseStep 7848359 = 11772539) B11772539
theorem B5232239 : Blo 1935435 5232239 := bstep (se 1 (by rfl) ⟨3924179, by rfl⟩ : syracuseStep 5232239 = 7848359) B7848359
theorem B3488159 : Blo 1935435 3488159 := bstep (se 1 (by rfl) ⟨2616119, by rfl⟩ : syracuseStep 3488159 = 5232239) B5232239
theorem B2325439 : Blo 1935435 2325439 := bstep (se 1 (by rfl) ⟨1744079, by rfl⟩ : syracuseStep 2325439 = 3488159) B3488159
theorem B12402341 : Blo 1935435 12402341 := bstep (se 4 (by rfl) ⟨1162719, by rfl⟩ : syracuseStep 12402341 = 2325439) B2325439
theorem B8268227 : Blo 1935435 8268227 := bstep (se 1 (by rfl) ⟨6201170, by rfl⟩ : syracuseStep 8268227 = 12402341) B12402341
theorem B5512151 : Blo 1935435 5512151 := bstep (se 1 (by rfl) ⟨4134113, by rfl⟩ : syracuseStep 5512151 = 8268227) B8268227
theorem B14699069 : Blo 1935435 14699069 := bstep (se 3 (by rfl) ⟨2756075, by rfl⟩ : syracuseStep 14699069 = 5512151) B5512151
theorem B9799379 : Blo 1935435 9799379 := bstep (se 1 (by rfl) ⟨7349534, by rfl⟩ : syracuseStep 9799379 = 14699069) B14699069
theorem B6532919 : Blo 1935435 6532919 := bstep (se 1 (by rfl) ⟨4899689, by rfl⟩ : syracuseStep 6532919 = 9799379) B9799379
theorem B4355279 : Blo 1935435 4355279 := bstep (se 1 (by rfl) ⟨3266459, by rfl⟩ : syracuseStep 4355279 = 6532919) B6532919
theorem B2903519 : Blo 1935435 2903519 := bstep (se 1 (by rfl) ⟨2177639, by rfl⟩ : syracuseStep 2903519 = 4355279) B4355279
theorem B1935679 : Blo 1935435 1935679 := bstep (se 1 (by rfl) ⟨1451759, by rfl⟩ : syracuseStep 1935679 = 2903519) B2903519
theorem B2903525 : Blo 1935435 2903525 := bbase (se 4 (by rfl) ⟨272205, by rfl⟩ : syracuseStep 2903525 = 544411) (by norm_num)
theorem B1935683 : Blo 1935435 1935683 := bstep (se 1 (by rfl) ⟨1451762, by rfl⟩ : syracuseStep 1935683 = 2903525) B2903525
theorem B5587381 : Blo 1935435 5587381 := bbase (se 5 (by rfl) ⟨261908, by rfl⟩ : syracuseStep 5587381 = 523817) (by norm_num)
theorem B7449841 : Blo 1935435 7449841 := bstep (se 2 (by rfl) ⟨2793690, by rfl⟩ : syracuseStep 7449841 = 5587381) B5587381
theorem B9933121 : Blo 1935435 9933121 := bstep (se 2 (by rfl) ⟨3724920, by rfl⟩ : syracuseStep 9933121 = 7449841) B7449841
theorem B13244161 : Blo 1935435 13244161 := bstep (se 2 (by rfl) ⟨4966560, by rfl⟩ : syracuseStep 13244161 = 9933121) B9933121
theorem B17658881 : Blo 1935435 17658881 := bstep (se 2 (by rfl) ⟨6622080, by rfl⟩ : syracuseStep 17658881 = 13244161) B13244161
theorem B11772587 : Blo 1935435 11772587 := bstep (se 1 (by rfl) ⟨8829440, by rfl⟩ : syracuseStep 11772587 = 17658881) B17658881
theorem B31393565 : Blo 1935435 31393565 := bstep (se 3 (by rfl) ⟨5886293, by rfl⟩ : syracuseStep 31393565 = 11772587) B11772587
theorem B20929043 : Blo 1935435 20929043 := bstep (se 1 (by rfl) ⟨15696782, by rfl⟩ : syracuseStep 20929043 = 31393565) B31393565
theorem B13952695 : Blo 1935435 13952695 := bstep (se 1 (by rfl) ⟨10464521, by rfl⟩ : syracuseStep 13952695 = 20929043) B20929043
theorem B18603593 : Blo 1935435 18603593 := bstep (se 2 (by rfl) ⟨6976347, by rfl⟩ : syracuseStep 18603593 = 13952695) B13952695
theorem B12402395 : Blo 1935435 12402395 := bstep (se 1 (by rfl) ⟨9301796, by rfl⟩ : syracuseStep 12402395 = 18603593) B18603593
theorem B8268263 : Blo 1935435 8268263 := bstep (se 1 (by rfl) ⟨6201197, by rfl⟩ : syracuseStep 8268263 = 12402395) B12402395
theorem B5512175 : Blo 1935435 5512175 := bstep (se 1 (by rfl) ⟨4134131, by rfl⟩ : syracuseStep 5512175 = 8268263) B8268263
theorem B3674783 : Blo 1935435 3674783 := bstep (se 1 (by rfl) ⟨2756087, by rfl⟩ : syracuseStep 3674783 = 5512175) B5512175
theorem B2449855 : Blo 1935435 2449855 := bstep (se 1 (by rfl) ⟨1837391, by rfl⟩ : syracuseStep 2449855 = 3674783) B3674783
theorem B3266473 : Blo 1935435 3266473 := bstep (se 2 (by rfl) ⟨1224927, by rfl⟩ : syracuseStep 3266473 = 2449855) B2449855
theorem B4355297 : Blo 1935435 4355297 := bstep (se 2 (by rfl) ⟨1633236, by rfl⟩ : syracuseStep 4355297 = 3266473) B3266473
theorem B2903531 : Blo 1935435 2903531 := bstep (se 1 (by rfl) ⟨2177648, by rfl⟩ : syracuseStep 2903531 = 4355297) B4355297
theorem B1935687 : Blo 1935435 1935687 := bstep (se 1 (by rfl) ⟨1451765, by rfl⟩ : syracuseStep 1935687 = 2903531) B2903531
theorem B2177653 : Blo 1935435 2177653 := bbase (se 5 (by rfl) ⟨102077, by rfl⟩ : syracuseStep 2177653 = 204155) (by norm_num)
theorem B2903537 : Blo 1935435 2903537 := bstep (se 2 (by rfl) ⟨1088826, by rfl⟩ : syracuseStep 2903537 = 2177653) B2177653
theorem B1935691 : Blo 1935435 1935691 := bstep (se 1 (by rfl) ⟨1451768, by rfl⟩ : syracuseStep 1935691 = 2903537) B2903537
theorem B2449865 : Blo 1935435 2449865 := bbase (se 2 (by rfl) ⟨918699, by rfl⟩ : syracuseStep 2449865 = 1837399) (by norm_num)
theorem B6532973 : Blo 1935435 6532973 := bstep (se 3 (by rfl) ⟨1224932, by rfl⟩ : syracuseStep 6532973 = 2449865) B2449865
theorem B4355315 : Blo 1935435 4355315 := bstep (se 1 (by rfl) ⟨3266486, by rfl⟩ : syracuseStep 4355315 = 6532973) B6532973
theorem B2903543 : Blo 1935435 2903543 := bstep (se 1 (by rfl) ⟨2177657, by rfl⟩ : syracuseStep 2903543 = 4355315) B4355315
theorem B1935695 : Blo 1935435 1935695 := bstep (se 1 (by rfl) ⟨1451771, by rfl⟩ : syracuseStep 1935695 = 2903543) B2903543
theorem B2903549 : Blo 1935435 2903549 := bbase (se 3 (by rfl) ⟨544415, by rfl⟩ : syracuseStep 2903549 = 1088831) (by norm_num)
theorem B1935699 : Blo 1935435 1935699 := bstep (se 1 (by rfl) ⟨1451774, by rfl⟩ : syracuseStep 1935699 = 2903549) B2903549
theorem B4355333 : Blo 1935435 4355333 := bbase (se 4 (by rfl) ⟨408312, by rfl⟩ : syracuseStep 4355333 = 816625) (by norm_num)
theorem B2903555 : Blo 1935435 2903555 := bstep (se 1 (by rfl) ⟨2177666, by rfl⟩ : syracuseStep 2903555 = 4355333) B4355333
theorem B1935703 : Blo 1935435 1935703 := bstep (se 1 (by rfl) ⟨1451777, by rfl⟩ : syracuseStep 1935703 = 2903555) B2903555
theorem B3674821 : Blo 1935435 3674821 := bbase (se 4 (by rfl) ⟨344514, by rfl⟩ : syracuseStep 3674821 = 689029) (by norm_num)
theorem B4899761 : Blo 1935435 4899761 := bstep (se 2 (by rfl) ⟨1837410, by rfl⟩ : syracuseStep 4899761 = 3674821) B3674821
theorem B3266507 : Blo 1935435 3266507 := bstep (se 1 (by rfl) ⟨2449880, by rfl⟩ : syracuseStep 3266507 = 4899761) B4899761
theorem B2177671 : Blo 1935435 2177671 := bstep (se 1 (by rfl) ⟨1633253, by rfl⟩ : syracuseStep 2177671 = 3266507) B3266507
theorem B2903561 : Blo 1935435 2903561 := bstep (se 2 (by rfl) ⟨1088835, by rfl⟩ : syracuseStep 2903561 = 2177671) B2177671
theorem B1935707 : Blo 1935435 1935707 := bstep (se 1 (by rfl) ⟨1451780, by rfl⟩ : syracuseStep 1935707 = 2903561) B2903561
theorem B9799541 : Blo 1935435 9799541 := bbase (se 5 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 9799541 = 918707) (by norm_num)
theorem B6533027 : Blo 1935435 6533027 := bstep (se 1 (by rfl) ⟨4899770, by rfl⟩ : syracuseStep 6533027 = 9799541) B9799541
theorem B4355351 : Blo 1935435 4355351 := bstep (se 1 (by rfl) ⟨3266513, by rfl⟩ : syracuseStep 4355351 = 6533027) B6533027
theorem B2903567 : Blo 1935435 2903567 := bstep (se 1 (by rfl) ⟨2177675, by rfl⟩ : syracuseStep 2903567 = 4355351) B4355351
theorem B1935711 : Blo 1935435 1935711 := bstep (se 1 (by rfl) ⟨1451783, by rfl⟩ : syracuseStep 1935711 = 2903567) B2903567
theorem B2903573 : Blo 1935435 2903573 := bbase (se 6 (by rfl) ⟨68052, by rfl⟩ : syracuseStep 2903573 = 136105) (by norm_num)
theorem B1935715 : Blo 1935435 1935715 := bstep (se 1 (by rfl) ⟨1451786, by rfl⟩ : syracuseStep 1935715 = 2903573) B2903573
theorem B2651869 : Blo 1935435 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B3535825 : Blo 1935435 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B4714433 : Blo 1935435 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B3142955 : Blo 1935435 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B2095303 : Blo 1935435 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B2793737 : Blo 1935435 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B7449965 : Blo 1935435 7449965 := bstep (se 3 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 7449965 = 2793737) B2793737
theorem B4966643 : Blo 1935435 4966643 := bstep (se 1 (by rfl) ⟨3724982, by rfl⟩ : syracuseStep 4966643 = 7449965) B7449965
theorem B13244381 : Blo 1935435 13244381 := bstep (se 3 (by rfl) ⟨2483321, by rfl⟩ : syracuseStep 13244381 = 4966643) B4966643
theorem B8829587 : Blo 1935435 8829587 := bstep (se 1 (by rfl) ⟨6622190, by rfl⟩ : syracuseStep 8829587 = 13244381) B13244381
theorem B5886391 : Blo 1935435 5886391 := bstep (se 1 (by rfl) ⟨4414793, by rfl⟩ : syracuseStep 5886391 = 8829587) B8829587
theorem B7848521 : Blo 1935435 7848521 := bstep (se 2 (by rfl) ⟨2943195, by rfl⟩ : syracuseStep 7848521 = 5886391) B5886391
theorem B5232347 : Blo 1935435 5232347 := bstep (se 1 (by rfl) ⟨3924260, by rfl⟩ : syracuseStep 5232347 = 7848521) B7848521
theorem B3488231 : Blo 1935435 3488231 := bstep (se 1 (by rfl) ⟨2616173, by rfl⟩ : syracuseStep 3488231 = 5232347) B5232347
theorem B9301949 : Blo 1935435 9301949 := bstep (se 3 (by rfl) ⟨1744115, by rfl⟩ : syracuseStep 9301949 = 3488231) B3488231
theorem B6201299 : Blo 1935435 6201299 := bstep (se 1 (by rfl) ⟨4650974, by rfl⟩ : syracuseStep 6201299 = 9301949) B9301949
theorem B16536797 : Blo 1935435 16536797 := bstep (se 3 (by rfl) ⟨3100649, by rfl⟩ : syracuseStep 16536797 = 6201299) B6201299
theorem B11024531 : Blo 1935435 11024531 := bstep (se 1 (by rfl) ⟨8268398, by rfl⟩ : syracuseStep 11024531 = 16536797) B16536797
theorem B7349687 : Blo 1935435 7349687 := bstep (se 1 (by rfl) ⟨5512265, by rfl⟩ : syracuseStep 7349687 = 11024531) B11024531
theorem B4899791 : Blo 1935435 4899791 := bstep (se 1 (by rfl) ⟨3674843, by rfl⟩ : syracuseStep 4899791 = 7349687) B7349687
theorem B3266527 : Blo 1935435 3266527 := bstep (se 1 (by rfl) ⟨2449895, by rfl⟩ : syracuseStep 3266527 = 4899791) B4899791
theorem B4355369 : Blo 1935435 4355369 := bstep (se 2 (by rfl) ⟨1633263, by rfl⟩ : syracuseStep 4355369 = 3266527) B3266527
theorem B2903579 : Blo 1935435 2903579 := bstep (se 1 (by rfl) ⟨2177684, by rfl⟩ : syracuseStep 2903579 = 4355369) B4355369
theorem B1935719 : Blo 1935435 1935719 := bstep (se 1 (by rfl) ⟨1451789, by rfl⟩ : syracuseStep 1935719 = 2903579) B2903579
theorem B2177689 : Blo 1935435 2177689 := bbase (se 2 (by rfl) ⟨816633, by rfl⟩ : syracuseStep 2177689 = 1633267) (by norm_num)
theorem B2903585 : Blo 1935435 2903585 := bstep (se 2 (by rfl) ⟨1088844, by rfl⟩ : syracuseStep 2903585 = 2177689) B2177689
theorem B1935723 : Blo 1935435 1935723 := bstep (se 1 (by rfl) ⟨1451792, by rfl⟩ : syracuseStep 1935723 = 2903585) B2903585
theorem B7349717 : Blo 1935435 7349717 := bbase (se 7 (by rfl) ⟨86129, by rfl⟩ : syracuseStep 7349717 = 172259) (by norm_num)
theorem B4899811 : Blo 1935435 4899811 := bstep (se 1 (by rfl) ⟨3674858, by rfl⟩ : syracuseStep 4899811 = 7349717) B7349717
theorem B6533081 : Blo 1935435 6533081 := bstep (se 2 (by rfl) ⟨2449905, by rfl⟩ : syracuseStep 6533081 = 4899811) B4899811
theorem B4355387 : Blo 1935435 4355387 := bstep (se 1 (by rfl) ⟨3266540, by rfl⟩ : syracuseStep 4355387 = 6533081) B6533081
theorem B2903591 : Blo 1935435 2903591 := bstep (se 1 (by rfl) ⟨2177693, by rfl⟩ : syracuseStep 2903591 = 4355387) B4355387
theorem B1935727 : Blo 1935435 1935727 := bstep (se 1 (by rfl) ⟨1451795, by rfl⟩ : syracuseStep 1935727 = 2903591) B2903591
theorem B2903597 : Blo 1935435 2903597 := bbase (se 3 (by rfl) ⟨544424, by rfl⟩ : syracuseStep 2903597 = 1088849) (by norm_num)
theorem B1935731 : Blo 1935435 1935731 := bstep (se 1 (by rfl) ⟨1451798, by rfl⟩ : syracuseStep 1935731 = 2903597) B2903597
theorem B4355405 : Blo 1935435 4355405 := bbase (se 3 (by rfl) ⟨816638, by rfl⟩ : syracuseStep 4355405 = 1633277) (by norm_num)
theorem B2903603 : Blo 1935435 2903603 := bstep (se 1 (by rfl) ⟨2177702, by rfl⟩ : syracuseStep 2903603 = 4355405) B4355405
theorem B1935735 : Blo 1935435 1935735 := bstep (se 1 (by rfl) ⟨1451801, by rfl⟩ : syracuseStep 1935735 = 2903603) B2903603
theorem B2449921 : Blo 1935435 2449921 := bbase (se 2 (by rfl) ⟨918720, by rfl⟩ : syracuseStep 2449921 = 1837441) (by norm_num)
theorem B3266561 : Blo 1935435 3266561 := bstep (se 2 (by rfl) ⟨1224960, by rfl⟩ : syracuseStep 3266561 = 2449921) B2449921
theorem B2177707 : Blo 1935435 2177707 := bstep (se 1 (by rfl) ⟨1633280, by rfl⟩ : syracuseStep 2177707 = 3266561) B3266561
theorem B2903609 : Blo 1935435 2903609 := bstep (se 2 (by rfl) ⟨1088853, by rfl⟩ : syracuseStep 2903609 = 2177707) B2177707
theorem B1935739 : Blo 1935435 1935739 := bstep (se 1 (by rfl) ⟨1451804, by rfl⟩ : syracuseStep 1935739 = 2903609) B2903609
theorem B2067125 : Blo 1935435 2067125 := bbase (se 5 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 2067125 = 193793) (by norm_num)
theorem B22049333 : Blo 1935435 22049333 := bstep (se 5 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 22049333 = 2067125) B2067125
theorem B14699555 : Blo 1935435 14699555 := bstep (se 1 (by rfl) ⟨11024666, by rfl⟩ : syracuseStep 14699555 = 22049333) B22049333
theorem B9799703 : Blo 1935435 9799703 := bstep (se 1 (by rfl) ⟨7349777, by rfl⟩ : syracuseStep 9799703 = 14699555) B14699555
theorem B6533135 : Blo 1935435 6533135 := bstep (se 1 (by rfl) ⟨4899851, by rfl⟩ : syracuseStep 6533135 = 9799703) B9799703
theorem B4355423 : Blo 1935435 4355423 := bstep (se 1 (by rfl) ⟨3266567, by rfl⟩ : syracuseStep 4355423 = 6533135) B6533135
theorem B2903615 : Blo 1935435 2903615 := bstep (se 1 (by rfl) ⟨2177711, by rfl⟩ : syracuseStep 2903615 = 4355423) B4355423
theorem B1935743 : Blo 1935435 1935743 := bstep (se 1 (by rfl) ⟨1451807, by rfl⟩ : syracuseStep 1935743 = 2903615) B2903615
theorem B2903621 : Blo 1935435 2903621 := bbase (se 4 (by rfl) ⟨272214, by rfl⟩ : syracuseStep 2903621 = 544429) (by norm_num)
theorem B1935747 : Blo 1935435 1935747 := bstep (se 1 (by rfl) ⟨1451810, by rfl⟩ : syracuseStep 1935747 = 2903621) B2903621
theorem B3266581 : Blo 1935435 3266581 := bbase (se 6 (by rfl) ⟨76560, by rfl⟩ : syracuseStep 3266581 = 153121) (by norm_num)
theorem B4355441 : Blo 1935435 4355441 := bstep (se 2 (by rfl) ⟨1633290, by rfl⟩ : syracuseStep 4355441 = 3266581) B3266581
theorem B2903627 : Blo 1935435 2903627 := bstep (se 1 (by rfl) ⟨2177720, by rfl⟩ : syracuseStep 2903627 = 4355441) B4355441
theorem B1935751 : Blo 1935435 1935751 := bstep (se 1 (by rfl) ⟨1451813, by rfl⟩ : syracuseStep 1935751 = 2903627) B2903627
theorem B2177725 : Blo 1935435 2177725 := bbase (se 3 (by rfl) ⟨408323, by rfl⟩ : syracuseStep 2177725 = 816647) (by norm_num)
theorem B2903633 : Blo 1935435 2903633 := bstep (se 2 (by rfl) ⟨1088862, by rfl⟩ : syracuseStep 2903633 = 2177725) B2177725
theorem B1935755 : Blo 1935435 1935755 := bstep (se 1 (by rfl) ⟨1451816, by rfl⟩ : syracuseStep 1935755 = 2903633) B2903633
theorem B6533189 : Blo 1935435 6533189 := bbase (se 4 (by rfl) ⟨612486, by rfl⟩ : syracuseStep 6533189 = 1224973) (by norm_num)
theorem B4355459 : Blo 1935435 4355459 := bstep (se 1 (by rfl) ⟨3266594, by rfl⟩ : syracuseStep 4355459 = 6533189) B6533189
theorem B2903639 : Blo 1935435 2903639 := bstep (se 1 (by rfl) ⟨2177729, by rfl⟩ : syracuseStep 2903639 = 4355459) B4355459
theorem B1935759 : Blo 1935435 1935759 := bstep (se 1 (by rfl) ⟨1451819, by rfl⟩ : syracuseStep 1935759 = 2903639) B2903639
theorem B2903645 : Blo 1935435 2903645 := bbase (se 3 (by rfl) ⟨544433, by rfl⟩ : syracuseStep 2903645 = 1088867) (by norm_num)
theorem B1935763 : Blo 1935435 1935763 := bstep (se 1 (by rfl) ⟨1451822, by rfl⟩ : syracuseStep 1935763 = 2903645) B2903645
theorem B4355477 : Blo 1935435 4355477 := bbase (se 6 (by rfl) ⟨102081, by rfl⟩ : syracuseStep 4355477 = 204163) (by norm_num)
theorem B2903651 : Blo 1935435 2903651 := bstep (se 1 (by rfl) ⟨2177738, by rfl⟩ : syracuseStep 2903651 = 4355477) B4355477
theorem B1935767 : Blo 1935435 1935767 := bstep (se 1 (by rfl) ⟨1451825, by rfl⟩ : syracuseStep 1935767 = 2903651) B2903651
theorem B2483389 : Blo 1935435 2483389 := bbase (se 3 (by rfl) ⟨465635, by rfl⟩ : syracuseStep 2483389 = 931271) (by norm_num)
theorem B3311185 : Blo 1935435 3311185 := bstep (se 2 (by rfl) ⟨1241694, by rfl⟩ : syracuseStep 3311185 = 2483389) B2483389
theorem B4414913 : Blo 1935435 4414913 := bstep (se 2 (by rfl) ⟨1655592, by rfl⟩ : syracuseStep 4414913 = 3311185) B3311185
theorem B2943275 : Blo 1935435 2943275 := bstep (se 1 (by rfl) ⟨2207456, by rfl⟩ : syracuseStep 2943275 = 4414913) B4414913
theorem B7848733 : Blo 1935435 7848733 := bstep (se 3 (by rfl) ⟨1471637, by rfl⟩ : syracuseStep 7848733 = 2943275) B2943275
theorem B10464977 : Blo 1935435 10464977 := bstep (se 2 (by rfl) ⟨3924366, by rfl⟩ : syracuseStep 10464977 = 7848733) B7848733
theorem B6976651 : Blo 1935435 6976651 := bstep (se 1 (by rfl) ⟨5232488, by rfl⟩ : syracuseStep 6976651 = 10464977) B10464977
theorem B9302201 : Blo 1935435 9302201 := bstep (se 2 (by rfl) ⟨3488325, by rfl⟩ : syracuseStep 9302201 = 6976651) B6976651
theorem B6201467 : Blo 1935435 6201467 := bstep (se 1 (by rfl) ⟨4651100, by rfl⟩ : syracuseStep 6201467 = 9302201) B9302201
theorem B4134311 : Blo 1935435 4134311 := bstep (se 1 (by rfl) ⟨3100733, by rfl⟩ : syracuseStep 4134311 = 6201467) B6201467
theorem B2756207 : Blo 1935435 2756207 := bstep (se 1 (by rfl) ⟨2067155, by rfl⟩ : syracuseStep 2756207 = 4134311) B4134311
theorem B7349885 : Blo 1935435 7349885 := bstep (se 3 (by rfl) ⟨1378103, by rfl⟩ : syracuseStep 7349885 = 2756207) B2756207
theorem B4899923 : Blo 1935435 4899923 := bstep (se 1 (by rfl) ⟨3674942, by rfl⟩ : syracuseStep 4899923 = 7349885) B7349885
theorem B3266615 : Blo 1935435 3266615 := bstep (se 1 (by rfl) ⟨2449961, by rfl⟩ : syracuseStep 3266615 = 4899923) B4899923
theorem B2177743 : Blo 1935435 2177743 := bstep (se 1 (by rfl) ⟨1633307, by rfl⟩ : syracuseStep 2177743 = 3266615) B3266615
theorem B2903657 : Blo 1935435 2903657 := bstep (se 2 (by rfl) ⟨1088871, by rfl⟩ : syracuseStep 2903657 = 2177743) B2177743
theorem B1935771 : Blo 1935435 1935771 := bstep (se 1 (by rfl) ⟨1451828, by rfl⟩ : syracuseStep 1935771 = 2903657) B2903657
theorem B4651109 : Blo 1935435 4651109 := bbase (se 4 (by rfl) ⟨436041, by rfl⟩ : syracuseStep 4651109 = 872083) (by norm_num)
theorem B3100739 : Blo 1935435 3100739 := bstep (se 1 (by rfl) ⟨2325554, by rfl⟩ : syracuseStep 3100739 = 4651109) B4651109
theorem B8268637 : Blo 1935435 8268637 := bstep (se 3 (by rfl) ⟨1550369, by rfl⟩ : syracuseStep 8268637 = 3100739) B3100739
theorem B11024849 : Blo 1935435 11024849 := bstep (se 2 (by rfl) ⟨4134318, by rfl⟩ : syracuseStep 11024849 = 8268637) B8268637
theorem B7349899 : Blo 1935435 7349899 := bstep (se 1 (by rfl) ⟨5512424, by rfl⟩ : syracuseStep 7349899 = 11024849) B11024849
theorem B9799865 : Blo 1935435 9799865 := bstep (se 2 (by rfl) ⟨3674949, by rfl⟩ : syracuseStep 9799865 = 7349899) B7349899
theorem B6533243 : Blo 1935435 6533243 := bstep (se 1 (by rfl) ⟨4899932, by rfl⟩ : syracuseStep 6533243 = 9799865) B9799865
theorem B4355495 : Blo 1935435 4355495 := bstep (se 1 (by rfl) ⟨3266621, by rfl⟩ : syracuseStep 4355495 = 6533243) B6533243
theorem B2903663 : Blo 1935435 2903663 := bstep (se 1 (by rfl) ⟨2177747, by rfl⟩ : syracuseStep 2903663 = 4355495) B4355495
theorem B1935775 : Blo 1935435 1935775 := bstep (se 1 (by rfl) ⟨1451831, by rfl⟩ : syracuseStep 1935775 = 2903663) B2903663
theorem B2903669 : Blo 1935435 2903669 := bbase (se 5 (by rfl) ⟨136109, by rfl⟩ : syracuseStep 2903669 = 272219) (by norm_num)
theorem B1935779 : Blo 1935435 1935779 := bstep (se 1 (by rfl) ⟨1451834, by rfl⟩ : syracuseStep 1935779 = 2903669) B2903669
theorem B3674965 : Blo 1935435 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B4899953 : Blo 1935435 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B3266635 : Blo 1935435 3266635 := bstep (se 1 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 3266635 = 4899953) B4899953
theorem B4355513 : Blo 1935435 4355513 := bstep (se 2 (by rfl) ⟨1633317, by rfl⟩ : syracuseStep 4355513 = 3266635) B3266635
theorem B2903675 : Blo 1935435 2903675 := bstep (se 1 (by rfl) ⟨2177756, by rfl⟩ : syracuseStep 2903675 = 4355513) B4355513
theorem B1935783 : Blo 1935435 1935783 := bstep (se 1 (by rfl) ⟨1451837, by rfl⟩ : syracuseStep 1935783 = 2903675) B2903675
theorem B2177761 : Blo 1935435 2177761 := bbase (se 2 (by rfl) ⟨816660, by rfl⟩ : syracuseStep 2177761 = 1633321) (by norm_num)
theorem B2903681 : Blo 1935435 2903681 := bstep (se 2 (by rfl) ⟨1088880, by rfl⟩ : syracuseStep 2903681 = 2177761) B2177761
theorem B1935787 : Blo 1935435 1935787 := bstep (se 1 (by rfl) ⟨1451840, by rfl⟩ : syracuseStep 1935787 = 2903681) B2903681
theorem B4899973 : Blo 1935435 4899973 := bbase (se 4 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 4899973 = 918745) (by norm_num)
theorem B6533297 : Blo 1935435 6533297 := bstep (se 2 (by rfl) ⟨2449986, by rfl⟩ : syracuseStep 6533297 = 4899973) B4899973
theorem B4355531 : Blo 1935435 4355531 := bstep (se 1 (by rfl) ⟨3266648, by rfl⟩ : syracuseStep 4355531 = 6533297) B6533297
theorem B2903687 : Blo 1935435 2903687 := bstep (se 1 (by rfl) ⟨2177765, by rfl⟩ : syracuseStep 2903687 = 4355531) B4355531
theorem B1935791 : Blo 1935435 1935791 := bstep (se 1 (by rfl) ⟨1451843, by rfl⟩ : syracuseStep 1935791 = 2903687) B2903687
theorem B2903693 : Blo 1935435 2903693 := bbase (se 3 (by rfl) ⟨544442, by rfl⟩ : syracuseStep 2903693 = 1088885) (by norm_num)
theorem B1935795 : Blo 1935435 1935795 := bstep (se 1 (by rfl) ⟨1451846, by rfl⟩ : syracuseStep 1935795 = 2903693) B2903693
theorem B4355549 : Blo 1935435 4355549 := bbase (se 3 (by rfl) ⟨816665, by rfl⟩ : syracuseStep 4355549 = 1633331) (by norm_num)
theorem B2903699 : Blo 1935435 2903699 := bstep (se 1 (by rfl) ⟨2177774, by rfl⟩ : syracuseStep 2903699 = 4355549) B4355549
theorem B1935799 : Blo 1935435 1935799 := bstep (se 1 (by rfl) ⟨1451849, by rfl⟩ : syracuseStep 1935799 = 2903699) B2903699
theorem B3266669 : Blo 1935435 3266669 := bbase (se 3 (by rfl) ⟨612500, by rfl⟩ : syracuseStep 3266669 = 1225001) (by norm_num)
theorem B2177779 : Blo 1935435 2177779 := bstep (se 1 (by rfl) ⟨1633334, by rfl⟩ : syracuseStep 2177779 = 3266669) B3266669
theorem B2903705 : Blo 1935435 2903705 := bstep (se 2 (by rfl) ⟨1088889, by rfl⟩ : syracuseStep 2903705 = 2177779) B2177779
theorem B1935803 : Blo 1935435 1935803 := bstep (se 1 (by rfl) ⟨1451852, by rfl⟩ : syracuseStep 1935803 = 2903705) B2903705
theorem B3488389 : Blo 1935435 3488389 := bbase (se 4 (by rfl) ⟨327036, by rfl⟩ : syracuseStep 3488389 = 654073) (by norm_num)
theorem B18604741 : Blo 1935435 18604741 := bstep (se 4 (by rfl) ⟨1744194, by rfl⟩ : syracuseStep 18604741 = 3488389) B3488389
theorem B24806321 : Blo 1935435 24806321 := bstep (se 2 (by rfl) ⟨9302370, by rfl⟩ : syracuseStep 24806321 = 18604741) B18604741
theorem B16537547 : Blo 1935435 16537547 := bstep (se 1 (by rfl) ⟨12403160, by rfl⟩ : syracuseStep 16537547 = 24806321) B24806321
theorem B11025031 : Blo 1935435 11025031 := bstep (se 1 (by rfl) ⟨8268773, by rfl⟩ : syracuseStep 11025031 = 16537547) B16537547
theorem B14700041 : Blo 1935435 14700041 := bstep (se 2 (by rfl) ⟨5512515, by rfl⟩ : syracuseStep 14700041 = 11025031) B11025031
theorem B9800027 : Blo 1935435 9800027 := bstep (se 1 (by rfl) ⟨7350020, by rfl⟩ : syracuseStep 9800027 = 14700041) B14700041
theorem B6533351 : Blo 1935435 6533351 := bstep (se 1 (by rfl) ⟨4900013, by rfl⟩ : syracuseStep 6533351 = 9800027) B9800027
theorem B4355567 : Blo 1935435 4355567 := bstep (se 1 (by rfl) ⟨3266675, by rfl⟩ : syracuseStep 4355567 = 6533351) B6533351
theorem B2903711 : Blo 1935435 2903711 := bstep (se 1 (by rfl) ⟨2177783, by rfl⟩ : syracuseStep 2903711 = 4355567) B4355567
theorem B1935807 : Blo 1935435 1935807 := bstep (se 1 (by rfl) ⟨1451855, by rfl⟩ : syracuseStep 1935807 = 2903711) B2903711
theorem B2903717 : Blo 1935435 2903717 := bbase (se 4 (by rfl) ⟨272223, by rfl⟩ : syracuseStep 2903717 = 544447) (by norm_num)
theorem B1935811 : Blo 1935435 1935811 := bstep (se 1 (by rfl) ⟨1451858, by rfl⟩ : syracuseStep 1935811 = 2903717) B2903717
theorem B2450017 : Blo 1935435 2450017 := bbase (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) (by norm_num)
theorem B3266689 : Blo 1935435 3266689 := bstep (se 2 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 3266689 = 2450017) B2450017
theorem B4355585 : Blo 1935435 4355585 := bstep (se 2 (by rfl) ⟨1633344, by rfl⟩ : syracuseStep 4355585 = 3266689) B3266689
theorem B2903723 : Blo 1935435 2903723 := bstep (se 1 (by rfl) ⟨2177792, by rfl⟩ : syracuseStep 2903723 = 4355585) B4355585
theorem B1935815 : Blo 1935435 1935815 := bstep (se 1 (by rfl) ⟨1451861, by rfl⟩ : syracuseStep 1935815 = 2903723) B2903723
theorem B2177797 : Blo 1935435 2177797 := bbase (se 4 (by rfl) ⟨204168, by rfl⟩ : syracuseStep 2177797 = 408337) (by norm_num)
theorem B2903729 : Blo 1935435 2903729 := bstep (se 2 (by rfl) ⟨1088898, by rfl⟩ : syracuseStep 2903729 = 2177797) B2177797
theorem B1935819 : Blo 1935435 1935819 := bstep (se 1 (by rfl) ⟨1451864, by rfl⟩ : syracuseStep 1935819 = 2903729) B2903729
theorem B2325613 : Blo 1935435 2325613 := bbase (se 3 (by rfl) ⟨436052, by rfl⟩ : syracuseStep 2325613 = 872105) (by norm_num)
theorem B3100817 : Blo 1935435 3100817 := bstep (se 2 (by rfl) ⟨1162806, by rfl⟩ : syracuseStep 3100817 = 2325613) B2325613
theorem B2067211 : Blo 1935435 2067211 := bstep (se 1 (by rfl) ⟨1550408, by rfl⟩ : syracuseStep 2067211 = 3100817) B3100817
theorem B2756281 : Blo 1935435 2756281 := bstep (se 2 (by rfl) ⟨1033605, by rfl⟩ : syracuseStep 2756281 = 2067211) B2067211
theorem B3675041 : Blo 1935435 3675041 := bstep (se 2 (by rfl) ⟨1378140, by rfl⟩ : syracuseStep 3675041 = 2756281) B2756281
theorem B2450027 : Blo 1935435 2450027 := bstep (se 1 (by rfl) ⟨1837520, by rfl⟩ : syracuseStep 2450027 = 3675041) B3675041
theorem B6533405 : Blo 1935435 6533405 := bstep (se 3 (by rfl) ⟨1225013, by rfl⟩ : syracuseStep 6533405 = 2450027) B2450027
theorem B4355603 : Blo 1935435 4355603 := bstep (se 1 (by rfl) ⟨3266702, by rfl⟩ : syracuseStep 4355603 = 6533405) B6533405
theorem B2903735 : Blo 1935435 2903735 := bstep (se 1 (by rfl) ⟨2177801, by rfl⟩ : syracuseStep 2903735 = 4355603) B4355603
theorem B1935823 : Blo 1935435 1935823 := bstep (se 1 (by rfl) ⟨1451867, by rfl⟩ : syracuseStep 1935823 = 2903735) B2903735
theorem B2903741 : Blo 1935435 2903741 := bbase (se 3 (by rfl) ⟨544451, by rfl⟩ : syracuseStep 2903741 = 1088903) (by norm_num)
theorem B1935827 : Blo 1935435 1935827 := bstep (se 1 (by rfl) ⟨1451870, by rfl⟩ : syracuseStep 1935827 = 2903741) B2903741
theorem B4355621 : Blo 1935435 4355621 := bbase (se 4 (by rfl) ⟨408339, by rfl⟩ : syracuseStep 4355621 = 816679) (by norm_num)
theorem B2903747 : Blo 1935435 2903747 := bstep (se 1 (by rfl) ⟨2177810, by rfl⟩ : syracuseStep 2903747 = 4355621) B4355621
theorem B1935831 : Blo 1935435 1935831 := bstep (se 1 (by rfl) ⟨1451873, by rfl⟩ : syracuseStep 1935831 = 2903747) B2903747
theorem B4900085 : Blo 1935435 4900085 := bbase (se 5 (by rfl) ⟨229691, by rfl⟩ : syracuseStep 4900085 = 459383) (by norm_num)
theorem B3266723 : Blo 1935435 3266723 := bstep (se 1 (by rfl) ⟨2450042, by rfl⟩ : syracuseStep 3266723 = 4900085) B4900085
theorem B2177815 : Blo 1935435 2177815 := bstep (se 1 (by rfl) ⟨1633361, by rfl⟩ : syracuseStep 2177815 = 3266723) B3266723
theorem B2903753 : Blo 1935435 2903753 := bstep (se 2 (by rfl) ⟨1088907, by rfl⟩ : syracuseStep 2903753 = 2177815) B2177815
theorem B1935835 : Blo 1935435 1935835 := bstep (se 1 (by rfl) ⟨1451876, by rfl⟩ : syracuseStep 1935835 = 2903753) B2903753
theorem B11175637 : Blo 1935435 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B14900849 : Blo 1935435 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B9933899 : Blo 1935435 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B26490397 : Blo 1935435 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B35320529 : Blo 1935435 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B23547019 : Blo 1935435 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B31396025 : Blo 1935435 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B20930683 : Blo 1935435 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B27907577 : Blo 1935435 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B18605051 : Blo 1935435 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B12403367 : Blo 1935435 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B8268911 : Blo 1935435 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B5512607 : Blo 1935435 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B3675071 : Blo 1935435 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B9800189 : Blo 1935435 9800189 := bstep (se 3 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 9800189 = 3675071) B3675071
theorem B6533459 : Blo 1935435 6533459 := bstep (se 1 (by rfl) ⟨4900094, by rfl⟩ : syracuseStep 6533459 = 9800189) B9800189
theorem B4355639 : Blo 1935435 4355639 := bstep (se 1 (by rfl) ⟨3266729, by rfl⟩ : syracuseStep 4355639 = 6533459) B6533459
theorem B2903759 : Blo 1935435 2903759 := bstep (se 1 (by rfl) ⟨2177819, by rfl⟩ : syracuseStep 2903759 = 4355639) B4355639
theorem B1935839 : Blo 1935435 1935839 := bstep (se 1 (by rfl) ⟨1451879, by rfl⟩ : syracuseStep 1935839 = 2903759) B2903759
theorem B2903765 : Blo 1935435 2903765 := bbase (se 7 (by rfl) ⟨34028, by rfl⟩ : syracuseStep 2903765 = 68057) (by norm_num)
theorem B1935843 : Blo 1935435 1935843 := bstep (se 1 (by rfl) ⟨1451882, by rfl⟩ : syracuseStep 1935843 = 2903765) B2903765
theorem B2389537 : Blo 1935435 2389537 := bbase (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) (by norm_num)
theorem B3186049 : Blo 1935435 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B4248065 : Blo 1935435 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B11328173 : Blo 1935435 11328173 := bstep (se 3 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 11328173 = 4248065) B4248065
theorem B7552115 : Blo 1935435 7552115 := bstep (se 1 (by rfl) ⟨5664086, by rfl⟩ : syracuseStep 7552115 = 11328173) B11328173
theorem B5034743 : Blo 1935435 5034743 := bstep (se 1 (by rfl) ⟨3776057, by rfl⟩ : syracuseStep 5034743 = 7552115) B7552115
theorem B3356495 : Blo 1935435 3356495 := bstep (se 1 (by rfl) ⟨2517371, by rfl⟩ : syracuseStep 3356495 = 5034743) B5034743
theorem B2237663 : Blo 1935435 2237663 := bstep (se 1 (by rfl) ⟨1678247, by rfl⟩ : syracuseStep 2237663 = 3356495) B3356495
theorem B5967101 : Blo 1935435 5967101 := bstep (se 3 (by rfl) ⟨1118831, by rfl⟩ : syracuseStep 5967101 = 2237663) B2237663
theorem B3978067 : Blo 1935435 3978067 := bstep (se 1 (by rfl) ⟨2983550, by rfl⟩ : syracuseStep 3978067 = 5967101) B5967101
theorem B5304089 : Blo 1935435 5304089 := bstep (se 2 (by rfl) ⟨1989033, by rfl⟩ : syracuseStep 5304089 = 3978067) B3978067
theorem B3536059 : Blo 1935435 3536059 := bstep (se 1 (by rfl) ⟨2652044, by rfl⟩ : syracuseStep 3536059 = 5304089) B5304089
theorem B4714745 : Blo 1935435 4714745 := bstep (se 2 (by rfl) ⟨1768029, by rfl⟩ : syracuseStep 4714745 = 3536059) B3536059
theorem B12572653 : Blo 1935435 12572653 := bstep (se 3 (by rfl) ⟨2357372, by rfl⟩ : syracuseStep 12572653 = 4714745) B4714745
theorem B16763537 : Blo 1935435 16763537 := bstep (se 2 (by rfl) ⟨6286326, by rfl⟩ : syracuseStep 16763537 = 12572653) B12572653
theorem B11175691 : Blo 1935435 11175691 := bstep (se 1 (by rfl) ⟨8381768, by rfl⟩ : syracuseStep 11175691 = 16763537) B16763537
theorem B14900921 : Blo 1935435 14900921 := bstep (se 2 (by rfl) ⟨5587845, by rfl⟩ : syracuseStep 14900921 = 11175691) B11175691
theorem B9933947 : Blo 1935435 9933947 := bstep (se 1 (by rfl) ⟨7450460, by rfl⟩ : syracuseStep 9933947 = 14900921) B14900921
theorem B6622631 : Blo 1935435 6622631 := bstep (se 1 (by rfl) ⟨4966973, by rfl⟩ : syracuseStep 6622631 = 9933947) B9933947
theorem B4415087 : Blo 1935435 4415087 := bstep (se 1 (by rfl) ⟨3311315, by rfl⟩ : syracuseStep 4415087 = 6622631) B6622631
theorem B2943391 : Blo 1935435 2943391 := bstep (se 1 (by rfl) ⟨2207543, by rfl⟩ : syracuseStep 2943391 = 4415087) B4415087
theorem B3924521 : Blo 1935435 3924521 := bstep (se 2 (by rfl) ⟨1471695, by rfl⟩ : syracuseStep 3924521 = 2943391) B2943391
theorem B2616347 : Blo 1935435 2616347 := bstep (se 1 (by rfl) ⟨1962260, by rfl⟩ : syracuseStep 2616347 = 3924521) B3924521
theorem B6976925 : Blo 1935435 6976925 := bstep (se 3 (by rfl) ⟨1308173, by rfl⟩ : syracuseStep 6976925 = 2616347) B2616347
theorem B4651283 : Blo 1935435 4651283 := bstep (se 1 (by rfl) ⟨3488462, by rfl⟩ : syracuseStep 4651283 = 6976925) B6976925
theorem B3100855 : Blo 1935435 3100855 := bstep (se 1 (by rfl) ⟨2325641, by rfl⟩ : syracuseStep 3100855 = 4651283) B4651283
theorem B4134473 : Blo 1935435 4134473 := bstep (se 2 (by rfl) ⟨1550427, by rfl⟩ : syracuseStep 4134473 = 3100855) B3100855
theorem B2756315 : Blo 1935435 2756315 := bstep (se 1 (by rfl) ⟨2067236, by rfl⟩ : syracuseStep 2756315 = 4134473) B4134473
theorem B7350173 : Blo 1935435 7350173 := bstep (se 3 (by rfl) ⟨1378157, by rfl⟩ : syracuseStep 7350173 = 2756315) B2756315
theorem B4900115 : Blo 1935435 4900115 := bstep (se 1 (by rfl) ⟨3675086, by rfl⟩ : syracuseStep 4900115 = 7350173) B7350173
theorem B3266743 : Blo 1935435 3266743 := bstep (se 1 (by rfl) ⟨2450057, by rfl⟩ : syracuseStep 3266743 = 4900115) B4900115
theorem B4355657 : Blo 1935435 4355657 := bstep (se 2 (by rfl) ⟨1633371, by rfl⟩ : syracuseStep 4355657 = 3266743) B3266743
theorem B2903771 : Blo 1935435 2903771 := bstep (se 1 (by rfl) ⟨2177828, by rfl⟩ : syracuseStep 2903771 = 4355657) B4355657
theorem B1935847 : Blo 1935435 1935847 := bstep (se 1 (by rfl) ⟨1451885, by rfl⟩ : syracuseStep 1935847 = 2903771) B2903771
theorem B2177833 : Blo 1935435 2177833 := bbase (se 2 (by rfl) ⟨816687, by rfl⟩ : syracuseStep 2177833 = 1633375) (by norm_num)
theorem B2903777 : Blo 1935435 2903777 := bstep (se 2 (by rfl) ⟨1088916, by rfl⟩ : syracuseStep 2903777 = 2177833) B2177833
theorem B1935851 : Blo 1935435 1935851 := bstep (se 1 (by rfl) ⟨1451888, by rfl⟩ : syracuseStep 1935851 = 2903777) B2903777
theorem B4651301 : Blo 1935435 4651301 := bbase (se 4 (by rfl) ⟨436059, by rfl⟩ : syracuseStep 4651301 = 872119) (by norm_num)
theorem B12403469 : Blo 1935435 12403469 := bstep (se 3 (by rfl) ⟨2325650, by rfl⟩ : syracuseStep 12403469 = 4651301) B4651301
theorem B8268979 : Blo 1935435 8268979 := bstep (se 1 (by rfl) ⟨6201734, by rfl⟩ : syracuseStep 8268979 = 12403469) B12403469
theorem B11025305 : Blo 1935435 11025305 := bstep (se 2 (by rfl) ⟨4134489, by rfl⟩ : syracuseStep 11025305 = 8268979) B8268979
theorem B7350203 : Blo 1935435 7350203 := bstep (se 1 (by rfl) ⟨5512652, by rfl⟩ : syracuseStep 7350203 = 11025305) B11025305
theorem B4900135 : Blo 1935435 4900135 := bstep (se 1 (by rfl) ⟨3675101, by rfl⟩ : syracuseStep 4900135 = 7350203) B7350203
theorem B6533513 : Blo 1935435 6533513 := bstep (se 2 (by rfl) ⟨2450067, by rfl⟩ : syracuseStep 6533513 = 4900135) B4900135
theorem B4355675 : Blo 1935435 4355675 := bstep (se 1 (by rfl) ⟨3266756, by rfl⟩ : syracuseStep 4355675 = 6533513) B6533513
theorem B2903783 : Blo 1935435 2903783 := bstep (se 1 (by rfl) ⟨2177837, by rfl⟩ : syracuseStep 2903783 = 4355675) B4355675
theorem B1935855 : Blo 1935435 1935855 := bstep (se 1 (by rfl) ⟨1451891, by rfl⟩ : syracuseStep 1935855 = 2903783) B2903783
theorem B2903789 : Blo 1935435 2903789 := bbase (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) (by norm_num)
theorem B1935859 : Blo 1935435 1935859 := bstep (se 1 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 1935859 = 2903789) B2903789
theorem B4355693 : Blo 1935435 4355693 := bbase (se 3 (by rfl) ⟨816692, by rfl⟩ : syracuseStep 4355693 = 1633385) (by norm_num)
theorem B2903795 : Blo 1935435 2903795 := bstep (se 1 (by rfl) ⟨2177846, by rfl⟩ : syracuseStep 2903795 = 4355693) B4355693
theorem B1935863 : Blo 1935435 1935863 := bstep (se 1 (by rfl) ⟨1451897, by rfl⟩ : syracuseStep 1935863 = 2903795) B2903795
theorem B3675125 : Blo 1935435 3675125 := bbase (se 5 (by rfl) ⟨172271, by rfl⟩ : syracuseStep 3675125 = 344543) (by norm_num)
theorem B2450083 : Blo 1935435 2450083 := bstep (se 1 (by rfl) ⟨1837562, by rfl⟩ : syracuseStep 2450083 = 3675125) B3675125
theorem B3266777 : Blo 1935435 3266777 := bstep (se 2 (by rfl) ⟨1225041, by rfl⟩ : syracuseStep 3266777 = 2450083) B2450083
theorem B2177851 : Blo 1935435 2177851 := bstep (se 1 (by rfl) ⟨1633388, by rfl⟩ : syracuseStep 2177851 = 3266777) B3266777
theorem B2903801 : Blo 1935435 2903801 := bstep (se 2 (by rfl) ⟨1088925, by rfl⟩ : syracuseStep 2903801 = 2177851) B2177851
theorem B1935867 : Blo 1935435 1935867 := bstep (se 1 (by rfl) ⟨1451900, by rfl⟩ : syracuseStep 1935867 = 2903801) B2903801
theorem B8830277 : Blo 1935435 8830277 := bbase (se 4 (by rfl) ⟨827838, by rfl⟩ : syracuseStep 8830277 = 1655677) (by norm_num)
theorem B5886851 : Blo 1935435 5886851 := bstep (se 1 (by rfl) ⟨4415138, by rfl⟩ : syracuseStep 5886851 = 8830277) B8830277
theorem B15698269 : Blo 1935435 15698269 := bstep (se 3 (by rfl) ⟨2943425, by rfl⟩ : syracuseStep 15698269 = 5886851) B5886851
theorem B83724101 : Blo 1935435 83724101 := bstep (se 4 (by rfl) ⟨7849134, by rfl⟩ : syracuseStep 83724101 = 15698269) B15698269
theorem B55816067 : Blo 1935435 55816067 := bstep (se 1 (by rfl) ⟨41862050, by rfl⟩ : syracuseStep 55816067 = 83724101) B83724101
theorem B37210711 : Blo 1935435 37210711 := bstep (se 1 (by rfl) ⟨27908033, by rfl⟩ : syracuseStep 37210711 = 55816067) B55816067
theorem B49614281 : Blo 1935435 49614281 := bstep (se 2 (by rfl) ⟨18605355, by rfl⟩ : syracuseStep 49614281 = 37210711) B37210711
theorem B33076187 : Blo 1935435 33076187 := bstep (se 1 (by rfl) ⟨24807140, by rfl⟩ : syracuseStep 33076187 = 49614281) B49614281
theorem B22050791 : Blo 1935435 22050791 := bstep (se 1 (by rfl) ⟨16538093, by rfl⟩ : syracuseStep 22050791 = 33076187) B33076187
theorem B14700527 : Blo 1935435 14700527 := bstep (se 1 (by rfl) ⟨11025395, by rfl⟩ : syracuseStep 14700527 = 22050791) B22050791
theorem B9800351 : Blo 1935435 9800351 := bstep (se 1 (by rfl) ⟨7350263, by rfl⟩ : syracuseStep 9800351 = 14700527) B14700527
theorem B6533567 : Blo 1935435 6533567 := bstep (se 1 (by rfl) ⟨4900175, by rfl⟩ : syracuseStep 6533567 = 9800351) B9800351
theorem B4355711 : Blo 1935435 4355711 := bstep (se 1 (by rfl) ⟨3266783, by rfl⟩ : syracuseStep 4355711 = 6533567) B6533567
theorem B2903807 : Blo 1935435 2903807 := bstep (se 1 (by rfl) ⟨2177855, by rfl⟩ : syracuseStep 2903807 = 4355711) B4355711
theorem B1935871 : Blo 1935435 1935871 := bstep (se 1 (by rfl) ⟨1451903, by rfl⟩ : syracuseStep 1935871 = 2903807) B2903807
theorem B2903813 : Blo 1935435 2903813 := bbase (se 4 (by rfl) ⟨272232, by rfl⟩ : syracuseStep 2903813 = 544465) (by norm_num)
theorem B1935875 : Blo 1935435 1935875 := bstep (se 1 (by rfl) ⟨1451906, by rfl⟩ : syracuseStep 1935875 = 2903813) B2903813
theorem B3266797 : Blo 1935435 3266797 := bbase (se 3 (by rfl) ⟨612524, by rfl⟩ : syracuseStep 3266797 = 1225049) (by norm_num)
theorem B4355729 : Blo 1935435 4355729 := bstep (se 2 (by rfl) ⟨1633398, by rfl⟩ : syracuseStep 4355729 = 3266797) B3266797
theorem B2903819 : Blo 1935435 2903819 := bstep (se 1 (by rfl) ⟨2177864, by rfl⟩ : syracuseStep 2903819 = 4355729) B4355729
theorem B1935879 : Blo 1935435 1935879 := bstep (se 1 (by rfl) ⟨1451909, by rfl⟩ : syracuseStep 1935879 = 2903819) B2903819
theorem B2177869 : Blo 1935435 2177869 := bbase (se 3 (by rfl) ⟨408350, by rfl⟩ : syracuseStep 2177869 = 816701) (by norm_num)
theorem B2903825 : Blo 1935435 2903825 := bstep (se 2 (by rfl) ⟨1088934, by rfl⟩ : syracuseStep 2903825 = 2177869) B2177869
theorem B1935883 : Blo 1935435 1935883 := bstep (se 1 (by rfl) ⟨1451912, by rfl⟩ : syracuseStep 1935883 = 2903825) B2903825
theorem B6533621 : Blo 1935435 6533621 := bbase (se 5 (by rfl) ⟨306263, by rfl⟩ : syracuseStep 6533621 = 612527) (by norm_num)
theorem B4355747 : Blo 1935435 4355747 := bstep (se 1 (by rfl) ⟨3266810, by rfl⟩ : syracuseStep 4355747 = 6533621) B6533621
theorem B2903831 : Blo 1935435 2903831 := bstep (se 1 (by rfl) ⟨2177873, by rfl⟩ : syracuseStep 2903831 = 4355747) B4355747
theorem B1935887 : Blo 1935435 1935887 := bstep (se 1 (by rfl) ⟨1451915, by rfl⟩ : syracuseStep 1935887 = 2903831) B2903831
theorem B2903837 : Blo 1935435 2903837 := bbase (se 3 (by rfl) ⟨544469, by rfl⟩ : syracuseStep 2903837 = 1088939) (by norm_num)
theorem B1935891 : Blo 1935435 1935891 := bstep (se 1 (by rfl) ⟨1451918, by rfl⟩ : syracuseStep 1935891 = 2903837) B2903837
theorem B4355765 : Blo 1935435 4355765 := bbase (se 5 (by rfl) ⟨204176, by rfl⟩ : syracuseStep 4355765 = 408353) (by norm_num)
theorem B2903843 : Blo 1935435 2903843 := bstep (se 1 (by rfl) ⟨2177882, by rfl⟩ : syracuseStep 2903843 = 4355765) B4355765
theorem B1935895 : Blo 1935435 1935895 := bstep (se 1 (by rfl) ⟨1451921, by rfl⟩ : syracuseStep 1935895 = 2903843) B2903843
theorem B11025557 : Blo 1935435 11025557 := bbase (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) (by norm_num)
theorem B7350371 : Blo 1935435 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B4900247 : Blo 1935435 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B3266831 : Blo 1935435 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B2177887 : Blo 1935435 2177887 := bstep (se 1 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 2177887 = 3266831) B3266831
theorem B2903849 : Blo 1935435 2903849 := bstep (se 2 (by rfl) ⟨1088943, by rfl⟩ : syracuseStep 2903849 = 2177887) B2177887
theorem B1935899 : Blo 1935435 1935899 := bstep (se 1 (by rfl) ⟨1451924, by rfl⟩ : syracuseStep 1935899 = 2903849) B2903849
theorem B5512789 : Blo 1935435 5512789 := bbase (se 8 (by rfl) ⟨32301, by rfl⟩ : syracuseStep 5512789 = 64603) (by norm_num)
theorem B7350385 : Blo 1935435 7350385 := bstep (se 2 (by rfl) ⟨2756394, by rfl⟩ : syracuseStep 7350385 = 5512789) B5512789
theorem B9800513 : Blo 1935435 9800513 := bstep (se 2 (by rfl) ⟨3675192, by rfl⟩ : syracuseStep 9800513 = 7350385) B7350385
theorem B6533675 : Blo 1935435 6533675 := bstep (se 1 (by rfl) ⟨4900256, by rfl⟩ : syracuseStep 6533675 = 9800513) B9800513
theorem B4355783 : Blo 1935435 4355783 := bstep (se 1 (by rfl) ⟨3266837, by rfl⟩ : syracuseStep 4355783 = 6533675) B6533675
theorem B2903855 : Blo 1935435 2903855 := bstep (se 1 (by rfl) ⟨2177891, by rfl⟩ : syracuseStep 2903855 = 4355783) B4355783
theorem B1935903 : Blo 1935435 1935903 := bstep (se 1 (by rfl) ⟨1451927, by rfl⟩ : syracuseStep 1935903 = 2903855) B2903855
theorem B2903861 : Blo 1935435 2903861 := bbase (se 5 (by rfl) ⟨136118, by rfl⟩ : syracuseStep 2903861 = 272237) (by norm_num)
theorem B1935907 : Blo 1935435 1935907 := bstep (se 1 (by rfl) ⟨1451930, by rfl⟩ : syracuseStep 1935907 = 2903861) B2903861
theorem B4900277 : Blo 1935435 4900277 := bbase (se 5 (by rfl) ⟨229700, by rfl⟩ : syracuseStep 4900277 = 459401) (by norm_num)
theorem B3266851 : Blo 1935435 3266851 := bstep (se 1 (by rfl) ⟨2450138, by rfl⟩ : syracuseStep 3266851 = 4900277) B4900277
theorem B4355801 : Blo 1935435 4355801 := bstep (se 2 (by rfl) ⟨1633425, by rfl⟩ : syracuseStep 4355801 = 3266851) B3266851
theorem B2903867 : Blo 1935435 2903867 := bstep (se 1 (by rfl) ⟨2177900, by rfl⟩ : syracuseStep 2903867 = 4355801) B4355801
theorem B1935911 : Blo 1935435 1935911 := bstep (se 1 (by rfl) ⟨1451933, by rfl⟩ : syracuseStep 1935911 = 2903867) B2903867
theorem B2177905 : Blo 1935435 2177905 := bbase (se 2 (by rfl) ⟨816714, by rfl⟩ : syracuseStep 2177905 = 1633429) (by norm_num)
theorem B2903873 : Blo 1935435 2903873 := bstep (se 2 (by rfl) ⟨1088952, by rfl⟩ : syracuseStep 2903873 = 2177905) B2177905
theorem B1935915 : Blo 1935435 1935915 := bstep (se 1 (by rfl) ⟨1451936, by rfl⟩ : syracuseStep 1935915 = 2903873) B2903873
theorem B8269253 : Blo 1935435 8269253 := bbase (se 4 (by rfl) ⟨775242, by rfl⟩ : syracuseStep 8269253 = 1550485) (by norm_num)
theorem B5512835 : Blo 1935435 5512835 := bstep (se 1 (by rfl) ⟨4134626, by rfl⟩ : syracuseStep 5512835 = 8269253) B8269253
theorem B3675223 : Blo 1935435 3675223 := bstep (se 1 (by rfl) ⟨2756417, by rfl⟩ : syracuseStep 3675223 = 5512835) B5512835
theorem B4900297 : Blo 1935435 4900297 := bstep (se 2 (by rfl) ⟨1837611, by rfl⟩ : syracuseStep 4900297 = 3675223) B3675223
theorem B6533729 : Blo 1935435 6533729 := bstep (se 2 (by rfl) ⟨2450148, by rfl⟩ : syracuseStep 6533729 = 4900297) B4900297
theorem B4355819 : Blo 1935435 4355819 := bstep (se 1 (by rfl) ⟨3266864, by rfl⟩ : syracuseStep 4355819 = 6533729) B6533729
theorem B2903879 : Blo 1935435 2903879 := bstep (se 1 (by rfl) ⟨2177909, by rfl⟩ : syracuseStep 2903879 = 4355819) B4355819
theorem B1935919 : Blo 1935435 1935919 := bstep (se 1 (by rfl) ⟨1451939, by rfl⟩ : syracuseStep 1935919 = 2903879) B2903879
theorem B2903885 : Blo 1935435 2903885 := bbase (se 3 (by rfl) ⟨544478, by rfl⟩ : syracuseStep 2903885 = 1088957) (by norm_num)
theorem B1935923 : Blo 1935435 1935923 := bstep (se 1 (by rfl) ⟨1451942, by rfl⟩ : syracuseStep 1935923 = 2903885) B2903885
theorem B4355837 : Blo 1935435 4355837 := bbase (se 3 (by rfl) ⟨816719, by rfl⟩ : syracuseStep 4355837 = 1633439) (by norm_num)
theorem B2903891 : Blo 1935435 2903891 := bstep (se 1 (by rfl) ⟨2177918, by rfl⟩ : syracuseStep 2903891 = 4355837) B4355837
theorem B1935927 : Blo 1935435 1935927 := bstep (se 1 (by rfl) ⟨1451945, by rfl⟩ : syracuseStep 1935927 = 2903891) B2903891
theorem B3266885 : Blo 1935435 3266885 := bbase (se 4 (by rfl) ⟨306270, by rfl⟩ : syracuseStep 3266885 = 612541) (by norm_num)
theorem B2177923 : Blo 1935435 2177923 := bstep (se 1 (by rfl) ⟨1633442, by rfl⟩ : syracuseStep 2177923 = 3266885) B3266885
theorem B2903897 : Blo 1935435 2903897 := bstep (se 2 (by rfl) ⟨1088961, by rfl⟩ : syracuseStep 2903897 = 2177923) B2177923
theorem B1935931 : Blo 1935435 1935931 := bstep (se 1 (by rfl) ⟨1451948, by rfl⟩ : syracuseStep 1935931 = 2903897) B2903897
theorem B14701013 : Blo 1935435 14701013 := bbase (se 7 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 14701013 = 344555) (by norm_num)
theorem B9800675 : Blo 1935435 9800675 := bstep (se 1 (by rfl) ⟨7350506, by rfl⟩ : syracuseStep 9800675 = 14701013) B14701013
theorem B6533783 : Blo 1935435 6533783 := bstep (se 1 (by rfl) ⟨4900337, by rfl⟩ : syracuseStep 6533783 = 9800675) B9800675
theorem B4355855 : Blo 1935435 4355855 := bstep (se 1 (by rfl) ⟨3266891, by rfl⟩ : syracuseStep 4355855 = 6533783) B6533783
theorem B2903903 : Blo 1935435 2903903 := bstep (se 1 (by rfl) ⟨2177927, by rfl⟩ : syracuseStep 2903903 = 4355855) B4355855
theorem B1935935 : Blo 1935435 1935935 := bstep (se 1 (by rfl) ⟨1451951, by rfl⟩ : syracuseStep 1935935 = 2903903) B2903903
theorem B2903909 : Blo 1935435 2903909 := bbase (se 4 (by rfl) ⟨272241, by rfl⟩ : syracuseStep 2903909 = 544483) (by norm_num)
theorem B1935939 : Blo 1935435 1935939 := bstep (se 1 (by rfl) ⟨1451954, by rfl⟩ : syracuseStep 1935939 = 2903909) B2903909
theorem B3675269 : Blo 1935435 3675269 := bbase (se 4 (by rfl) ⟨344556, by rfl⟩ : syracuseStep 3675269 = 689113) (by norm_num)
theorem B2450179 : Blo 1935435 2450179 := bstep (se 1 (by rfl) ⟨1837634, by rfl⟩ : syracuseStep 2450179 = 3675269) B3675269
theorem B3266905 : Blo 1935435 3266905 := bstep (se 2 (by rfl) ⟨1225089, by rfl⟩ : syracuseStep 3266905 = 2450179) B2450179
theorem B4355873 : Blo 1935435 4355873 := bstep (se 2 (by rfl) ⟨1633452, by rfl⟩ : syracuseStep 4355873 = 3266905) B3266905
theorem B2903915 : Blo 1935435 2903915 := bstep (se 1 (by rfl) ⟨2177936, by rfl⟩ : syracuseStep 2903915 = 4355873) B4355873
theorem B1935943 : Blo 1935435 1935943 := bstep (se 1 (by rfl) ⟨1451957, by rfl⟩ : syracuseStep 1935943 = 2903915) B2903915
theorem B2177941 : Blo 1935435 2177941 := bbase (se 6 (by rfl) ⟨51045, by rfl⟩ : syracuseStep 2177941 = 102091) (by norm_num)
theorem B2903921 : Blo 1935435 2903921 := bstep (se 2 (by rfl) ⟨1088970, by rfl⟩ : syracuseStep 2903921 = 2177941) B2177941
theorem B1935947 : Blo 1935435 1935947 := bstep (se 1 (by rfl) ⟨1451960, by rfl⟩ : syracuseStep 1935947 = 2903921) B2903921
theorem B2450189 : Blo 1935435 2450189 := bbase (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) (by norm_num)
theorem B6533837 : Blo 1935435 6533837 := bstep (se 3 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 6533837 = 2450189) B2450189
theorem B4355891 : Blo 1935435 4355891 := bstep (se 1 (by rfl) ⟨3266918, by rfl⟩ : syracuseStep 4355891 = 6533837) B6533837
theorem B2903927 : Blo 1935435 2903927 := bstep (se 1 (by rfl) ⟨2177945, by rfl⟩ : syracuseStep 2903927 = 4355891) B4355891
theorem B1935951 : Blo 1935435 1935951 := bstep (se 1 (by rfl) ⟨1451963, by rfl⟩ : syracuseStep 1935951 = 2903927) B2903927
theorem B2903933 : Blo 1935435 2903933 := bbase (se 3 (by rfl) ⟨544487, by rfl⟩ : syracuseStep 2903933 = 1088975) (by norm_num)
theorem B1935955 : Blo 1935435 1935955 := bstep (se 1 (by rfl) ⟨1451966, by rfl⟩ : syracuseStep 1935955 = 2903933) B2903933
theorem B4355909 : Blo 1935435 4355909 := bbase (se 4 (by rfl) ⟨408366, by rfl⟩ : syracuseStep 4355909 = 816733) (by norm_num)
theorem B2903939 : Blo 1935435 2903939 := bstep (se 1 (by rfl) ⟨2177954, by rfl⟩ : syracuseStep 2903939 = 4355909) B4355909
theorem B1935959 : Blo 1935435 1935959 := bstep (se 1 (by rfl) ⟨1451969, by rfl⟩ : syracuseStep 1935959 = 2903939) B2903939
theorem B2325781 : Blo 1935435 2325781 := bbase (se 6 (by rfl) ⟨54510, by rfl⟩ : syracuseStep 2325781 = 109021) (by norm_num)
theorem B3101041 : Blo 1935435 3101041 := bstep (se 2 (by rfl) ⟨1162890, by rfl⟩ : syracuseStep 3101041 = 2325781) B2325781
theorem B4134721 : Blo 1935435 4134721 := bstep (se 2 (by rfl) ⟨1550520, by rfl⟩ : syracuseStep 4134721 = 3101041) B3101041
theorem B5512961 : Blo 1935435 5512961 := bstep (se 2 (by rfl) ⟨2067360, by rfl⟩ : syracuseStep 5512961 = 4134721) B4134721
theorem B3675307 : Blo 1935435 3675307 := bstep (se 1 (by rfl) ⟨2756480, by rfl⟩ : syracuseStep 3675307 = 5512961) B5512961
theorem B4900409 : Blo 1935435 4900409 := bstep (se 2 (by rfl) ⟨1837653, by rfl⟩ : syracuseStep 4900409 = 3675307) B3675307
theorem B3266939 : Blo 1935435 3266939 := bstep (se 1 (by rfl) ⟨2450204, by rfl⟩ : syracuseStep 3266939 = 4900409) B4900409
theorem B2177959 : Blo 1935435 2177959 := bstep (se 1 (by rfl) ⟨1633469, by rfl⟩ : syracuseStep 2177959 = 3266939) B3266939
theorem B2903945 : Blo 1935435 2903945 := bstep (se 2 (by rfl) ⟨1088979, by rfl⟩ : syracuseStep 2903945 = 2177959) B2177959
theorem B1935963 : Blo 1935435 1935963 := bstep (se 1 (by rfl) ⟨1451972, by rfl⟩ : syracuseStep 1935963 = 2903945) B2903945
theorem B9800837 : Blo 1935435 9800837 := bbase (se 4 (by rfl) ⟨918828, by rfl⟩ : syracuseStep 9800837 = 1837657) (by norm_num)
theorem B6533891 : Blo 1935435 6533891 := bstep (se 1 (by rfl) ⟨4900418, by rfl⟩ : syracuseStep 6533891 = 9800837) B9800837
theorem B4355927 : Blo 1935435 4355927 := bstep (se 1 (by rfl) ⟨3266945, by rfl⟩ : syracuseStep 4355927 = 6533891) B6533891
theorem B2903951 : Blo 1935435 2903951 := bstep (se 1 (by rfl) ⟨2177963, by rfl⟩ : syracuseStep 2903951 = 4355927) B4355927
theorem B1935967 : Blo 1935435 1935967 := bstep (se 1 (by rfl) ⟨1451975, by rfl⟩ : syracuseStep 1935967 = 2903951) B2903951
theorem B2903957 : Blo 1935435 2903957 := bbase (se 6 (by rfl) ⟨68061, by rfl⟩ : syracuseStep 2903957 = 136123) (by norm_num)
theorem B1935971 : Blo 1935435 1935971 := bstep (se 1 (by rfl) ⟨1451978, by rfl⟩ : syracuseStep 1935971 = 2903957) B2903957
theorem B2067373 : Blo 1935435 2067373 := bbase (se 3 (by rfl) ⟨387632, by rfl⟩ : syracuseStep 2067373 = 775265) (by norm_num)
theorem B11025989 : Blo 1935435 11025989 := bstep (se 4 (by rfl) ⟨1033686, by rfl⟩ : syracuseStep 11025989 = 2067373) B2067373
theorem B7350659 : Blo 1935435 7350659 := bstep (se 1 (by rfl) ⟨5512994, by rfl⟩ : syracuseStep 7350659 = 11025989) B11025989
theorem B4900439 : Blo 1935435 4900439 := bstep (se 1 (by rfl) ⟨3675329, by rfl⟩ : syracuseStep 4900439 = 7350659) B7350659
theorem B3266959 : Blo 1935435 3266959 := bstep (se 1 (by rfl) ⟨2450219, by rfl⟩ : syracuseStep 3266959 = 4900439) B4900439
theorem B4355945 : Blo 1935435 4355945 := bstep (se 2 (by rfl) ⟨1633479, by rfl⟩ : syracuseStep 4355945 = 3266959) B3266959
theorem B2903963 : Blo 1935435 2903963 := bstep (se 1 (by rfl) ⟨2177972, by rfl⟩ : syracuseStep 2903963 = 4355945) B4355945
theorem B1935975 : Blo 1935435 1935975 := bstep (se 1 (by rfl) ⟨1451981, by rfl⟩ : syracuseStep 1935975 = 2903963) B2903963
theorem B2177977 : Blo 1935435 2177977 := bbase (se 2 (by rfl) ⟨816741, by rfl⟩ : syracuseStep 2177977 = 1633483) (by norm_num)
theorem B2903969 : Blo 1935435 2903969 := bstep (se 2 (by rfl) ⟨1088988, by rfl⟩ : syracuseStep 2903969 = 2177977) B2177977
theorem B1935979 : Blo 1935435 1935979 := bstep (se 1 (by rfl) ⟨1451984, by rfl⟩ : syracuseStep 1935979 = 2903969) B2903969
theorem B5233061 : Blo 1935435 5233061 := bbase (se 4 (by rfl) ⟨490599, by rfl⟩ : syracuseStep 5233061 = 981199) (by norm_num)
theorem B3488707 : Blo 1935435 3488707 := bstep (se 1 (by rfl) ⟨2616530, by rfl⟩ : syracuseStep 3488707 = 5233061) B5233061
theorem B4651609 : Blo 1935435 4651609 := bstep (se 2 (by rfl) ⟨1744353, by rfl⟩ : syracuseStep 4651609 = 3488707) B3488707
theorem B6202145 : Blo 1935435 6202145 := bstep (se 2 (by rfl) ⟨2325804, by rfl⟩ : syracuseStep 6202145 = 4651609) B4651609
theorem B4134763 : Blo 1935435 4134763 := bstep (se 1 (by rfl) ⟨3101072, by rfl⟩ : syracuseStep 4134763 = 6202145) B6202145
theorem B5513017 : Blo 1935435 5513017 := bstep (se 2 (by rfl) ⟨2067381, by rfl⟩ : syracuseStep 5513017 = 4134763) B4134763
theorem B7350689 : Blo 1935435 7350689 := bstep (se 2 (by rfl) ⟨2756508, by rfl⟩ : syracuseStep 7350689 = 5513017) B5513017
theorem B4900459 : Blo 1935435 4900459 := bstep (se 1 (by rfl) ⟨3675344, by rfl⟩ : syracuseStep 4900459 = 7350689) B7350689
theorem B6533945 : Blo 1935435 6533945 := bstep (se 2 (by rfl) ⟨2450229, by rfl⟩ : syracuseStep 6533945 = 4900459) B4900459
theorem B4355963 : Blo 1935435 4355963 := bstep (se 1 (by rfl) ⟨3266972, by rfl⟩ : syracuseStep 4355963 = 6533945) B6533945
theorem B2903975 : Blo 1935435 2903975 := bstep (se 1 (by rfl) ⟨2177981, by rfl⟩ : syracuseStep 2903975 = 4355963) B4355963
theorem B1935983 : Blo 1935435 1935983 := bstep (se 1 (by rfl) ⟨1451987, by rfl⟩ : syracuseStep 1935983 = 2903975) B2903975
theorem B2903981 : Blo 1935435 2903981 := bbase (se 3 (by rfl) ⟨544496, by rfl⟩ : syracuseStep 2903981 = 1088993) (by norm_num)
theorem B1935987 : Blo 1935435 1935987 := bstep (se 1 (by rfl) ⟨1451990, by rfl⟩ : syracuseStep 1935987 = 2903981) B2903981
theorem B4355981 : Blo 1935435 4355981 := bbase (se 3 (by rfl) ⟨816746, by rfl⟩ : syracuseStep 4355981 = 1633493) (by norm_num)
theorem B2903987 : Blo 1935435 2903987 := bstep (se 1 (by rfl) ⟨2177990, by rfl⟩ : syracuseStep 2903987 = 4355981) B4355981
theorem B1935991 : Blo 1935435 1935991 := bstep (se 1 (by rfl) ⟨1451993, by rfl⟩ : syracuseStep 1935991 = 2903987) B2903987
theorem B2450245 : Blo 1935435 2450245 := bbase (se 4 (by rfl) ⟨229710, by rfl⟩ : syracuseStep 2450245 = 459421) (by norm_num)
theorem B3266993 : Blo 1935435 3266993 := bstep (se 2 (by rfl) ⟨1225122, by rfl⟩ : syracuseStep 3266993 = 2450245) B2450245
theorem B2177995 : Blo 1935435 2177995 := bstep (se 1 (by rfl) ⟨1633496, by rfl⟩ : syracuseStep 2177995 = 3266993) B3266993
theorem B2903993 : Blo 1935435 2903993 := bstep (se 2 (by rfl) ⟨1088997, by rfl⟩ : syracuseStep 2903993 = 2177995) B2177995
theorem B1935995 : Blo 1935435 1935995 := bstep (se 1 (by rfl) ⟨1451996, by rfl⟩ : syracuseStep 1935995 = 2903993) B2903993
theorem B174407509 : Blo 1935435 174407509 := bbase (se 9 (by rfl) ⟨510959, by rfl⟩ : syracuseStep 174407509 = 1021919) (by norm_num)
theorem B232543345 : Blo 1935435 232543345 := bstep (se 2 (by rfl) ⟨87203754, by rfl⟩ : syracuseStep 232543345 = 174407509) B174407509
theorem B310057793 : Blo 1935435 310057793 := bstep (se 2 (by rfl) ⟨116271672, by rfl⟩ : syracuseStep 310057793 = 232543345) B232543345
theorem B206705195 : Blo 1935435 206705195 := bstep (se 1 (by rfl) ⟨155028896, by rfl⟩ : syracuseStep 206705195 = 310057793) B310057793
theorem B137803463 : Blo 1935435 137803463 := bstep (se 1 (by rfl) ⟨103352597, by rfl⟩ : syracuseStep 137803463 = 206705195) B206705195
theorem B91868975 : Blo 1935435 91868975 := bstep (se 1 (by rfl) ⟨68901731, by rfl⟩ : syracuseStep 91868975 = 137803463) B137803463
theorem B61245983 : Blo 1935435 61245983 := bstep (se 1 (by rfl) ⟨45934487, by rfl⟩ : syracuseStep 61245983 = 91868975) B91868975
theorem B40830655 : Blo 1935435 40830655 := bstep (se 1 (by rfl) ⟨30622991, by rfl⟩ : syracuseStep 40830655 = 61245983) B61245983
theorem B54440873 : Blo 1935435 54440873 := bstep (se 2 (by rfl) ⟨20415327, by rfl⟩ : syracuseStep 54440873 = 40830655) B40830655
theorem B36293915 : Blo 1935435 36293915 := bstep (se 1 (by rfl) ⟨27220436, by rfl⟩ : syracuseStep 36293915 = 54440873) B54440873
theorem B24195943 : Blo 1935435 24195943 := bstep (se 1 (by rfl) ⟨18146957, by rfl⟩ : syracuseStep 24195943 = 36293915) B36293915
theorem B32261257 : Blo 1935435 32261257 := bstep (se 2 (by rfl) ⟨12097971, by rfl⟩ : syracuseStep 32261257 = 24195943) B24195943
theorem B43015009 : Blo 1935435 43015009 := bstep (se 2 (by rfl) ⟨16130628, by rfl⟩ : syracuseStep 43015009 = 32261257) B32261257
theorem B57353345 : Blo 1935435 57353345 := bstep (se 2 (by rfl) ⟨21507504, by rfl⟩ : syracuseStep 57353345 = 43015009) B43015009
theorem B38235563 : Blo 1935435 38235563 := bstep (se 1 (by rfl) ⟨28676672, by rfl⟩ : syracuseStep 38235563 = 57353345) B57353345
theorem B25490375 : Blo 1935435 25490375 := bstep (se 1 (by rfl) ⟨19117781, by rfl⟩ : syracuseStep 25490375 = 38235563) B38235563
theorem B16993583 : Blo 1935435 16993583 := bstep (se 1 (by rfl) ⟨12745187, by rfl⟩ : syracuseStep 16993583 = 25490375) B25490375
theorem B11329055 : Blo 1935435 11329055 := bstep (se 1 (by rfl) ⟨8496791, by rfl⟩ : syracuseStep 11329055 = 16993583) B16993583
theorem B7552703 : Blo 1935435 7552703 := bstep (se 1 (by rfl) ⟨5664527, by rfl⟩ : syracuseStep 7552703 = 11329055) B11329055
theorem B5035135 : Blo 1935435 5035135 := bstep (se 1 (by rfl) ⟨3776351, by rfl⟩ : syracuseStep 5035135 = 7552703) B7552703
theorem B6713513 : Blo 1935435 6713513 := bstep (se 2 (by rfl) ⟨2517567, by rfl⟩ : syracuseStep 6713513 = 5035135) B5035135
theorem B4475675 : Blo 1935435 4475675 := bstep (se 1 (by rfl) ⟨3356756, by rfl⟩ : syracuseStep 4475675 = 6713513) B6713513
theorem B11935133 : Blo 1935435 11935133 := bstep (se 3 (by rfl) ⟨2237837, by rfl⟩ : syracuseStep 11935133 = 4475675) B4475675
theorem B7956755 : Blo 1935435 7956755 := bstep (se 1 (by rfl) ⟨5967566, by rfl⟩ : syracuseStep 7956755 = 11935133) B11935133
theorem B5304503 : Blo 1935435 5304503 := bstep (se 1 (by rfl) ⟨3978377, by rfl⟩ : syracuseStep 5304503 = 7956755) B7956755
theorem B3536335 : Blo 1935435 3536335 := bstep (se 1 (by rfl) ⟨2652251, by rfl⟩ : syracuseStep 3536335 = 5304503) B5304503
theorem B4715113 : Blo 1935435 4715113 := bstep (se 2 (by rfl) ⟨1768167, by rfl⟩ : syracuseStep 4715113 = 3536335) B3536335
theorem B6286817 : Blo 1935435 6286817 := bstep (se 2 (by rfl) ⟨2357556, by rfl⟩ : syracuseStep 6286817 = 4715113) B4715113
theorem B4191211 : Blo 1935435 4191211 := bstep (se 1 (by rfl) ⟨3143408, by rfl⟩ : syracuseStep 4191211 = 6286817) B6286817
theorem B5588281 : Blo 1935435 5588281 := bstep (se 2 (by rfl) ⟨2095605, by rfl⟩ : syracuseStep 5588281 = 4191211) B4191211
theorem B7451041 : Blo 1935435 7451041 := bstep (se 2 (by rfl) ⟨2794140, by rfl⟩ : syracuseStep 7451041 = 5588281) B5588281
theorem B9934721 : Blo 1935435 9934721 := bstep (se 2 (by rfl) ⟨3725520, by rfl⟩ : syracuseStep 9934721 = 7451041) B7451041
theorem B6623147 : Blo 1935435 6623147 := bstep (se 1 (by rfl) ⟨4967360, by rfl⟩ : syracuseStep 6623147 = 9934721) B9934721
theorem B17661725 : Blo 1935435 17661725 := bstep (se 3 (by rfl) ⟨3311573, by rfl⟩ : syracuseStep 17661725 = 6623147) B6623147
theorem B11774483 : Blo 1935435 11774483 := bstep (se 1 (by rfl) ⟨8830862, by rfl⟩ : syracuseStep 11774483 = 17661725) B17661725
theorem B7849655 : Blo 1935435 7849655 := bstep (se 1 (by rfl) ⟨5887241, by rfl⟩ : syracuseStep 7849655 = 11774483) B11774483
theorem B5233103 : Blo 1935435 5233103 := bstep (se 1 (by rfl) ⟨3924827, by rfl⟩ : syracuseStep 5233103 = 7849655) B7849655
theorem B3488735 : Blo 1935435 3488735 := bstep (se 1 (by rfl) ⟨2616551, by rfl⟩ : syracuseStep 3488735 = 5233103) B5233103
theorem B9303293 : Blo 1935435 9303293 := bstep (se 3 (by rfl) ⟨1744367, by rfl⟩ : syracuseStep 9303293 = 3488735) B3488735
theorem B24808781 : Blo 1935435 24808781 := bstep (se 3 (by rfl) ⟨4651646, by rfl⟩ : syracuseStep 24808781 = 9303293) B9303293
theorem B16539187 : Blo 1935435 16539187 := bstep (se 1 (by rfl) ⟨12404390, by rfl⟩ : syracuseStep 16539187 = 24808781) B24808781
theorem B22052249 : Blo 1935435 22052249 := bstep (se 2 (by rfl) ⟨8269593, by rfl⟩ : syracuseStep 22052249 = 16539187) B16539187
theorem B14701499 : Blo 1935435 14701499 := bstep (se 1 (by rfl) ⟨11026124, by rfl⟩ : syracuseStep 14701499 = 22052249) B22052249
theorem B9800999 : Blo 1935435 9800999 := bstep (se 1 (by rfl) ⟨7350749, by rfl⟩ : syracuseStep 9800999 = 14701499) B14701499
theorem B6533999 : Blo 1935435 6533999 := bstep (se 1 (by rfl) ⟨4900499, by rfl⟩ : syracuseStep 6533999 = 9800999) B9800999
theorem B4355999 : Blo 1935435 4355999 := bstep (se 1 (by rfl) ⟨3266999, by rfl⟩ : syracuseStep 4355999 = 6533999) B6533999
theorem B2903999 : Blo 1935435 2903999 := bstep (se 1 (by rfl) ⟨2177999, by rfl⟩ : syracuseStep 2903999 = 4355999) B4355999
theorem B1935999 : Blo 1935435 1935999 := bstep (se 1 (by rfl) ⟨1451999, by rfl⟩ : syracuseStep 1935999 = 2903999) B2903999
theorem B2904005 : Blo 1935435 2904005 := bbase (se 4 (by rfl) ⟨272250, by rfl⟩ : syracuseStep 2904005 = 544501) (by norm_num)
theorem B1936003 : Blo 1935435 1936003 := bstep (se 1 (by rfl) ⟨1452002, by rfl⟩ : syracuseStep 1936003 = 2904005) B2904005
theorem B3267013 : Blo 1935435 3267013 := bbase (se 4 (by rfl) ⟨306282, by rfl⟩ : syracuseStep 3267013 = 612565) (by norm_num)
theorem B4356017 : Blo 1935435 4356017 := bstep (se 2 (by rfl) ⟨1633506, by rfl⟩ : syracuseStep 4356017 = 3267013) B3267013
theorem B2904011 : Blo 1935435 2904011 := bstep (se 1 (by rfl) ⟨2178008, by rfl⟩ : syracuseStep 2904011 = 4356017) B4356017
theorem B1936007 : Blo 1935435 1936007 := bstep (se 1 (by rfl) ⟨1452005, by rfl⟩ : syracuseStep 1936007 = 2904011) B2904011
theorem B2178013 : Blo 1935435 2178013 := bbase (se 3 (by rfl) ⟨408377, by rfl⟩ : syracuseStep 2178013 = 816755) (by norm_num)
theorem B2904017 : Blo 1935435 2904017 := bstep (se 2 (by rfl) ⟨1089006, by rfl⟩ : syracuseStep 2904017 = 2178013) B2178013
theorem B1936011 : Blo 1935435 1936011 := bstep (se 1 (by rfl) ⟨1452008, by rfl⟩ : syracuseStep 1936011 = 2904017) B2904017
theorem B6534053 : Blo 1935435 6534053 := bbase (se 4 (by rfl) ⟨612567, by rfl⟩ : syracuseStep 6534053 = 1225135) (by norm_num)
theorem B4356035 : Blo 1935435 4356035 := bstep (se 1 (by rfl) ⟨3267026, by rfl⟩ : syracuseStep 4356035 = 6534053) B6534053
theorem B2904023 : Blo 1935435 2904023 := bstep (se 1 (by rfl) ⟨2178017, by rfl⟩ : syracuseStep 2904023 = 4356035) B4356035
theorem B1936015 : Blo 1935435 1936015 := bstep (se 1 (by rfl) ⟨1452011, by rfl⟩ : syracuseStep 1936015 = 2904023) B2904023
theorem B2904029 : Blo 1935435 2904029 := bbase (se 3 (by rfl) ⟨544505, by rfl⟩ : syracuseStep 2904029 = 1089011) (by norm_num)
theorem B1936019 : Blo 1935435 1936019 := bstep (se 1 (by rfl) ⟨1452014, by rfl⟩ : syracuseStep 1936019 = 2904029) B2904029
theorem B4356053 : Blo 1935435 4356053 := bbase (se 7 (by rfl) ⟨51047, by rfl⟩ : syracuseStep 4356053 = 102095) (by norm_num)
theorem B2904035 : Blo 1935435 2904035 := bstep (se 1 (by rfl) ⟨2178026, by rfl⟩ : syracuseStep 2904035 = 4356053) B4356053
theorem B1936023 : Blo 1935435 1936023 := bstep (se 1 (by rfl) ⟨1452017, by rfl⟩ : syracuseStep 1936023 = 2904035) B2904035
theorem B6977573 : Blo 1935435 6977573 := bbase (se 4 (by rfl) ⟨654147, by rfl⟩ : syracuseStep 6977573 = 1308295) (by norm_num)
theorem B4651715 : Blo 1935435 4651715 := bstep (se 1 (by rfl) ⟨3488786, by rfl⟩ : syracuseStep 4651715 = 6977573) B6977573
theorem B12404573 : Blo 1935435 12404573 := bstep (se 3 (by rfl) ⟨2325857, by rfl⟩ : syracuseStep 12404573 = 4651715) B4651715
theorem B8269715 : Blo 1935435 8269715 := bstep (se 1 (by rfl) ⟨6202286, by rfl⟩ : syracuseStep 8269715 = 12404573) B12404573
theorem B5513143 : Blo 1935435 5513143 := bstep (se 1 (by rfl) ⟨4134857, by rfl⟩ : syracuseStep 5513143 = 8269715) B8269715
theorem B7350857 : Blo 1935435 7350857 := bstep (se 2 (by rfl) ⟨2756571, by rfl⟩ : syracuseStep 7350857 = 5513143) B5513143
theorem B4900571 : Blo 1935435 4900571 := bstep (se 1 (by rfl) ⟨3675428, by rfl⟩ : syracuseStep 4900571 = 7350857) B7350857
theorem B3267047 : Blo 1935435 3267047 := bstep (se 1 (by rfl) ⟨2450285, by rfl⟩ : syracuseStep 3267047 = 4900571) B4900571
theorem B2178031 : Blo 1935435 2178031 := bstep (se 1 (by rfl) ⟨1633523, by rfl⟩ : syracuseStep 2178031 = 3267047) B3267047
theorem B2904041 : Blo 1935435 2904041 := bstep (se 2 (by rfl) ⟨1089015, by rfl⟩ : syracuseStep 2904041 = 2178031) B2178031
theorem B1936027 : Blo 1935435 1936027 := bstep (se 1 (by rfl) ⟨1452020, by rfl⟩ : syracuseStep 1936027 = 2904041) B2904041
theorem B3101149 : Blo 1935435 3101149 := bbase (se 3 (by rfl) ⟨581465, by rfl⟩ : syracuseStep 3101149 = 1162931) (by norm_num)
theorem B16539461 : Blo 1935435 16539461 := bstep (se 4 (by rfl) ⟨1550574, by rfl⟩ : syracuseStep 16539461 = 3101149) B3101149
theorem B11026307 : Blo 1935435 11026307 := bstep (se 1 (by rfl) ⟨8269730, by rfl⟩ : syracuseStep 11026307 = 16539461) B16539461
theorem B7350871 : Blo 1935435 7350871 := bstep (se 1 (by rfl) ⟨5513153, by rfl⟩ : syracuseStep 7350871 = 11026307) B11026307
theorem B9801161 : Blo 1935435 9801161 := bstep (se 2 (by rfl) ⟨3675435, by rfl⟩ : syracuseStep 9801161 = 7350871) B7350871
theorem B6534107 : Blo 1935435 6534107 := bstep (se 1 (by rfl) ⟨4900580, by rfl⟩ : syracuseStep 6534107 = 9801161) B9801161
theorem B4356071 : Blo 1935435 4356071 := bstep (se 1 (by rfl) ⟨3267053, by rfl⟩ : syracuseStep 4356071 = 6534107) B6534107
theorem B2904047 : Blo 1935435 2904047 := bstep (se 1 (by rfl) ⟨2178035, by rfl⟩ : syracuseStep 2904047 = 4356071) B4356071
theorem B1936031 : Blo 1935435 1936031 := bstep (se 1 (by rfl) ⟨1452023, by rfl⟩ : syracuseStep 1936031 = 2904047) B2904047
theorem B2904053 : Blo 1935435 2904053 := bbase (se 5 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 2904053 = 272255) (by norm_num)
theorem B1936035 : Blo 1935435 1936035 := bstep (se 1 (by rfl) ⟨1452026, by rfl⟩ : syracuseStep 1936035 = 2904053) B2904053
theorem B6202325 : Blo 1935435 6202325 := bbase (se 7 (by rfl) ⟨72683, by rfl⟩ : syracuseStep 6202325 = 145367) (by norm_num)
theorem B4134883 : Blo 1935435 4134883 := bstep (se 1 (by rfl) ⟨3101162, by rfl⟩ : syracuseStep 4134883 = 6202325) B6202325
theorem B5513177 : Blo 1935435 5513177 := bstep (se 2 (by rfl) ⟨2067441, by rfl⟩ : syracuseStep 5513177 = 4134883) B4134883
theorem B3675451 : Blo 1935435 3675451 := bstep (se 1 (by rfl) ⟨2756588, by rfl⟩ : syracuseStep 3675451 = 5513177) B5513177
theorem B4900601 : Blo 1935435 4900601 := bstep (se 2 (by rfl) ⟨1837725, by rfl⟩ : syracuseStep 4900601 = 3675451) B3675451
theorem B3267067 : Blo 1935435 3267067 := bstep (se 1 (by rfl) ⟨2450300, by rfl⟩ : syracuseStep 3267067 = 4900601) B4900601
theorem B4356089 : Blo 1935435 4356089 := bstep (se 2 (by rfl) ⟨1633533, by rfl⟩ : syracuseStep 4356089 = 3267067) B3267067
theorem B2904059 : Blo 1935435 2904059 := bstep (se 1 (by rfl) ⟨2178044, by rfl⟩ : syracuseStep 2904059 = 4356089) B4356089
theorem B1936039 : Blo 1935435 1936039 := bstep (se 1 (by rfl) ⟨1452029, by rfl⟩ : syracuseStep 1936039 = 2904059) B2904059
theorem B2178049 : Blo 1935435 2178049 := bbase (se 2 (by rfl) ⟨816768, by rfl⟩ : syracuseStep 2178049 = 1633537) (by norm_num)
theorem B2904065 : Blo 1935435 2904065 := bstep (se 2 (by rfl) ⟨1089024, by rfl⟩ : syracuseStep 2904065 = 2178049) B2178049
theorem B1936043 : Blo 1935435 1936043 := bstep (se 1 (by rfl) ⟨1452032, by rfl⟩ : syracuseStep 1936043 = 2904065) B2904065
theorem B4900621 : Blo 1935435 4900621 := bbase (se 3 (by rfl) ⟨918866, by rfl⟩ : syracuseStep 4900621 = 1837733) (by norm_num)
theorem B6534161 : Blo 1935435 6534161 := bstep (se 2 (by rfl) ⟨2450310, by rfl⟩ : syracuseStep 6534161 = 4900621) B4900621
theorem B4356107 : Blo 1935435 4356107 := bstep (se 1 (by rfl) ⟨3267080, by rfl⟩ : syracuseStep 4356107 = 6534161) B6534161
theorem B2904071 : Blo 1935435 2904071 := bstep (se 1 (by rfl) ⟨2178053, by rfl⟩ : syracuseStep 2904071 = 4356107) B4356107
theorem B1936047 : Blo 1935435 1936047 := bstep (se 1 (by rfl) ⟨1452035, by rfl⟩ : syracuseStep 1936047 = 2904071) B2904071
theorem B2904077 : Blo 1935435 2904077 := bbase (se 3 (by rfl) ⟨544514, by rfl⟩ : syracuseStep 2904077 = 1089029) (by norm_num)
theorem B1936051 : Blo 1935435 1936051 := bstep (se 1 (by rfl) ⟨1452038, by rfl⟩ : syracuseStep 1936051 = 2904077) B2904077
theorem B4356125 : Blo 1935435 4356125 := bbase (se 3 (by rfl) ⟨816773, by rfl⟩ : syracuseStep 4356125 = 1633547) (by norm_num)
theorem B2904083 : Blo 1935435 2904083 := bstep (se 1 (by rfl) ⟨2178062, by rfl⟩ : syracuseStep 2904083 = 4356125) B4356125
theorem B1936055 : Blo 1935435 1936055 := bstep (se 1 (by rfl) ⟨1452041, by rfl⟩ : syracuseStep 1936055 = 2904083) B2904083
theorem B3267101 : Blo 1935435 3267101 := bbase (se 3 (by rfl) ⟨612581, by rfl⟩ : syracuseStep 3267101 = 1225163) (by norm_num)
theorem B2178067 : Blo 1935435 2178067 := bstep (se 1 (by rfl) ⟨1633550, by rfl⟩ : syracuseStep 2178067 = 3267101) B3267101
theorem B2904089 : Blo 1935435 2904089 := bstep (se 2 (by rfl) ⟨1089033, by rfl⟩ : syracuseStep 2904089 = 2178067) B2178067
theorem B1936059 : Blo 1935435 1936059 := bstep (se 1 (by rfl) ⟨1452044, by rfl⟩ : syracuseStep 1936059 = 2904089) B2904089
theorem B6977701 : Blo 1935435 6977701 := bbase (se 4 (by rfl) ⟨654159, by rfl⟩ : syracuseStep 6977701 = 1308319) (by norm_num)
theorem B9303601 : Blo 1935435 9303601 := bstep (se 2 (by rfl) ⟨3488850, by rfl⟩ : syracuseStep 9303601 = 6977701) B6977701
theorem B12404801 : Blo 1935435 12404801 := bstep (se 2 (by rfl) ⟨4651800, by rfl⟩ : syracuseStep 12404801 = 9303601) B9303601
theorem B8269867 : Blo 1935435 8269867 := bstep (se 1 (by rfl) ⟨6202400, by rfl⟩ : syracuseStep 8269867 = 12404801) B12404801
theorem B11026489 : Blo 1935435 11026489 := bstep (se 2 (by rfl) ⟨4134933, by rfl⟩ : syracuseStep 11026489 = 8269867) B8269867
theorem B14701985 : Blo 1935435 14701985 := bstep (se 2 (by rfl) ⟨5513244, by rfl⟩ : syracuseStep 14701985 = 11026489) B11026489
theorem B9801323 : Blo 1935435 9801323 := bstep (se 1 (by rfl) ⟨7350992, by rfl⟩ : syracuseStep 9801323 = 14701985) B14701985
theorem B6534215 : Blo 1935435 6534215 := bstep (se 1 (by rfl) ⟨4900661, by rfl⟩ : syracuseStep 6534215 = 9801323) B9801323
theorem B4356143 : Blo 1935435 4356143 := bstep (se 1 (by rfl) ⟨3267107, by rfl⟩ : syracuseStep 4356143 = 6534215) B6534215
theorem B2904095 : Blo 1935435 2904095 := bstep (se 1 (by rfl) ⟨2178071, by rfl⟩ : syracuseStep 2904095 = 4356143) B4356143
theorem B1936063 : Blo 1935435 1936063 := bstep (se 1 (by rfl) ⟨1452047, by rfl⟩ : syracuseStep 1936063 = 2904095) B2904095
theorem B2904101 : Blo 1935435 2904101 := bbase (se 4 (by rfl) ⟨272259, by rfl⟩ : syracuseStep 2904101 = 544519) (by norm_num)
theorem B1936067 : Blo 1935435 1936067 := bstep (se 1 (by rfl) ⟨1452050, by rfl⟩ : syracuseStep 1936067 = 2904101) B2904101
theorem B2450341 : Blo 1935435 2450341 := bbase (se 4 (by rfl) ⟨229719, by rfl⟩ : syracuseStep 2450341 = 459439) (by norm_num)
theorem B3267121 : Blo 1935435 3267121 := bstep (se 2 (by rfl) ⟨1225170, by rfl⟩ : syracuseStep 3267121 = 2450341) B2450341
theorem B4356161 : Blo 1935435 4356161 := bstep (se 2 (by rfl) ⟨1633560, by rfl⟩ : syracuseStep 4356161 = 3267121) B3267121
theorem B2904107 : Blo 1935435 2904107 := bstep (se 1 (by rfl) ⟨2178080, by rfl⟩ : syracuseStep 2904107 = 4356161) B4356161
theorem B1936071 : Blo 1935435 1936071 := bstep (se 1 (by rfl) ⟨1452053, by rfl⟩ : syracuseStep 1936071 = 2904107) B2904107
theorem B2178085 : Blo 1935435 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B2904113 : Blo 1935435 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B1936075 : Blo 1935435 1936075 := bstep (se 1 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 1936075 = 2904113) B2904113
theorem B6202453 : Blo 1935435 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B8269937 : Blo 1935435 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B5513291 : Blo 1935435 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B3675527 : Blo 1935435 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B2450351 : Blo 1935435 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B6534269 : Blo 1935435 6534269 := bstep (se 3 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 6534269 = 2450351) B2450351
theorem B4356179 : Blo 1935435 4356179 := bstep (se 1 (by rfl) ⟨3267134, by rfl⟩ : syracuseStep 4356179 = 6534269) B6534269
theorem B2904119 : Blo 1935435 2904119 := bstep (se 1 (by rfl) ⟨2178089, by rfl⟩ : syracuseStep 2904119 = 4356179) B4356179
theorem B1936079 : Blo 1935435 1936079 := bstep (se 1 (by rfl) ⟨1452059, by rfl⟩ : syracuseStep 1936079 = 2904119) B2904119
theorem B2904125 : Blo 1935435 2904125 := bbase (se 3 (by rfl) ⟨544523, by rfl⟩ : syracuseStep 2904125 = 1089047) (by norm_num)
theorem B1936083 : Blo 1935435 1936083 := bstep (se 1 (by rfl) ⟨1452062, by rfl⟩ : syracuseStep 1936083 = 2904125) B2904125
theorem B4356197 : Blo 1935435 4356197 := bbase (se 4 (by rfl) ⟨408393, by rfl⟩ : syracuseStep 4356197 = 816787) (by norm_num)
theorem B2904131 : Blo 1935435 2904131 := bstep (se 1 (by rfl) ⟨2178098, by rfl⟩ : syracuseStep 2904131 = 4356197) B4356197
theorem B1936087 : Blo 1935435 1936087 := bstep (se 1 (by rfl) ⟨1452065, by rfl⟩ : syracuseStep 1936087 = 2904131) B2904131
theorem B4900733 : Blo 1935435 4900733 := bbase (se 3 (by rfl) ⟨918887, by rfl⟩ : syracuseStep 4900733 = 1837775) (by norm_num)
theorem B3267155 : Blo 1935435 3267155 := bstep (se 1 (by rfl) ⟨2450366, by rfl⟩ : syracuseStep 3267155 = 4900733) B4900733
theorem B2178103 : Blo 1935435 2178103 := bstep (se 1 (by rfl) ⟨1633577, by rfl⟩ : syracuseStep 2178103 = 3267155) B3267155
theorem B2904137 : Blo 1935435 2904137 := bstep (se 2 (by rfl) ⟨1089051, by rfl⟩ : syracuseStep 2904137 = 2178103) B2178103
theorem B1936091 : Blo 1935435 1936091 := bstep (se 1 (by rfl) ⟨1452068, by rfl⟩ : syracuseStep 1936091 = 2904137) B2904137
theorem B3675557 : Blo 1935435 3675557 := bbase (se 4 (by rfl) ⟨344583, by rfl⟩ : syracuseStep 3675557 = 689167) (by norm_num)
theorem B9801485 : Blo 1935435 9801485 := bstep (se 3 (by rfl) ⟨1837778, by rfl⟩ : syracuseStep 9801485 = 3675557) B3675557
theorem B6534323 : Blo 1935435 6534323 := bstep (se 1 (by rfl) ⟨4900742, by rfl⟩ : syracuseStep 6534323 = 9801485) B9801485
theorem B4356215 : Blo 1935435 4356215 := bstep (se 1 (by rfl) ⟨3267161, by rfl⟩ : syracuseStep 4356215 = 6534323) B6534323
theorem B2904143 : Blo 1935435 2904143 := bstep (se 1 (by rfl) ⟨2178107, by rfl⟩ : syracuseStep 2904143 = 4356215) B4356215
theorem B1936095 : Blo 1935435 1936095 := bstep (se 1 (by rfl) ⟨1452071, by rfl⟩ : syracuseStep 1936095 = 2904143) B2904143
theorem B2904149 : Blo 1935435 2904149 := bbase (se 8 (by rfl) ⟨17016, by rfl⟩ : syracuseStep 2904149 = 34033) (by norm_num)
theorem B1936099 : Blo 1935435 1936099 := bstep (se 1 (by rfl) ⟨1452074, by rfl⟩ : syracuseStep 1936099 = 2904149) B2904149
theorem B4191437 : Blo 1935435 4191437 := bbase (se 3 (by rfl) ⟨785894, by rfl⟩ : syracuseStep 4191437 = 1571789) (by norm_num)
theorem B11177165 : Blo 1935435 11177165 := bstep (se 3 (by rfl) ⟨2095718, by rfl⟩ : syracuseStep 11177165 = 4191437) B4191437
theorem B7451443 : Blo 1935435 7451443 := bstep (se 1 (by rfl) ⟨5588582, by rfl⟩ : syracuseStep 7451443 = 11177165) B11177165
theorem B9935257 : Blo 1935435 9935257 := bstep (se 2 (by rfl) ⟨3725721, by rfl⟩ : syracuseStep 9935257 = 7451443) B7451443
theorem B13247009 : Blo 1935435 13247009 := bstep (se 2 (by rfl) ⟨4967628, by rfl⟩ : syracuseStep 13247009 = 9935257) B9935257
theorem B8831339 : Blo 1935435 8831339 := bstep (se 1 (by rfl) ⟨6623504, by rfl⟩ : syracuseStep 8831339 = 13247009) B13247009
theorem B5887559 : Blo 1935435 5887559 := bstep (se 1 (by rfl) ⟨4415669, by rfl⟩ : syracuseStep 5887559 = 8831339) B8831339
theorem B3925039 : Blo 1935435 3925039 := bstep (se 1 (by rfl) ⟨2943779, by rfl⟩ : syracuseStep 3925039 = 5887559) B5887559
theorem B5233385 : Blo 1935435 5233385 := bstep (se 2 (by rfl) ⟨1962519, by rfl⟩ : syracuseStep 5233385 = 3925039) B3925039
theorem B3488923 : Blo 1935435 3488923 := bstep (se 1 (by rfl) ⟨2616692, by rfl⟩ : syracuseStep 3488923 = 5233385) B5233385
theorem B18607589 : Blo 1935435 18607589 := bstep (se 4 (by rfl) ⟨1744461, by rfl⟩ : syracuseStep 18607589 = 3488923) B3488923
theorem B12405059 : Blo 1935435 12405059 := bstep (se 1 (by rfl) ⟨9303794, by rfl⟩ : syracuseStep 12405059 = 18607589) B18607589
theorem B8270039 : Blo 1935435 8270039 := bstep (se 1 (by rfl) ⟨6202529, by rfl⟩ : syracuseStep 8270039 = 12405059) B12405059
theorem B5513359 : Blo 1935435 5513359 := bstep (se 1 (by rfl) ⟨4135019, by rfl⟩ : syracuseStep 5513359 = 8270039) B8270039
theorem B7351145 : Blo 1935435 7351145 := bstep (se 2 (by rfl) ⟨2756679, by rfl⟩ : syracuseStep 7351145 = 5513359) B5513359
theorem B4900763 : Blo 1935435 4900763 := bstep (se 1 (by rfl) ⟨3675572, by rfl⟩ : syracuseStep 4900763 = 7351145) B7351145
theorem B3267175 : Blo 1935435 3267175 := bstep (se 1 (by rfl) ⟨2450381, by rfl⟩ : syracuseStep 3267175 = 4900763) B4900763
theorem B4356233 : Blo 1935435 4356233 := bstep (se 2 (by rfl) ⟨1633587, by rfl⟩ : syracuseStep 4356233 = 3267175) B3267175
theorem B2904155 : Blo 1935435 2904155 := bstep (se 1 (by rfl) ⟨2178116, by rfl⟩ : syracuseStep 2904155 = 4356233) B4356233
theorem B1936103 : Blo 1935435 1936103 := bstep (se 1 (by rfl) ⟨1452077, by rfl⟩ : syracuseStep 1936103 = 2904155) B2904155
theorem B2178121 : Blo 1935435 2178121 := bbase (se 2 (by rfl) ⟨816795, by rfl⟩ : syracuseStep 2178121 = 1633591) (by norm_num)
theorem B2904161 : Blo 1935435 2904161 := bstep (se 2 (by rfl) ⟨1089060, by rfl⟩ : syracuseStep 2904161 = 2178121) B2178121
theorem B1936107 : Blo 1935435 1936107 := bstep (se 1 (by rfl) ⟨1452080, by rfl⟩ : syracuseStep 1936107 = 2904161) B2904161
theorem B12405109 : Blo 1935435 12405109 := bbase (se 5 (by rfl) ⟨581489, by rfl⟩ : syracuseStep 12405109 = 1162979) (by norm_num)
theorem B16540145 : Blo 1935435 16540145 := bstep (se 2 (by rfl) ⟨6202554, by rfl⟩ : syracuseStep 16540145 = 12405109) B12405109
theorem B11026763 : Blo 1935435 11026763 := bstep (se 1 (by rfl) ⟨8270072, by rfl⟩ : syracuseStep 11026763 = 16540145) B16540145
theorem B7351175 : Blo 1935435 7351175 := bstep (se 1 (by rfl) ⟨5513381, by rfl⟩ : syracuseStep 7351175 = 11026763) B11026763
theorem B4900783 : Blo 1935435 4900783 := bstep (se 1 (by rfl) ⟨3675587, by rfl⟩ : syracuseStep 4900783 = 7351175) B7351175
theorem B6534377 : Blo 1935435 6534377 := bstep (se 2 (by rfl) ⟨2450391, by rfl⟩ : syracuseStep 6534377 = 4900783) B4900783
theorem B4356251 : Blo 1935435 4356251 := bstep (se 1 (by rfl) ⟨3267188, by rfl⟩ : syracuseStep 4356251 = 6534377) B6534377
theorem B2904167 : Blo 1935435 2904167 := bstep (se 1 (by rfl) ⟨2178125, by rfl⟩ : syracuseStep 2904167 = 4356251) B4356251
theorem B1936111 : Blo 1935435 1936111 := bstep (se 1 (by rfl) ⟨1452083, by rfl⟩ : syracuseStep 1936111 = 2904167) B2904167
theorem B2904173 : Blo 1935435 2904173 := bbase (se 3 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 2904173 = 1089065) (by norm_num)
theorem B1936115 : Blo 1935435 1936115 := bstep (se 1 (by rfl) ⟨1452086, by rfl⟩ : syracuseStep 1936115 = 2904173) B2904173
theorem B4356269 : Blo 1935435 4356269 := bbase (se 3 (by rfl) ⟨816800, by rfl⟩ : syracuseStep 4356269 = 1633601) (by norm_num)
theorem B2904179 : Blo 1935435 2904179 := bstep (se 1 (by rfl) ⟨2178134, by rfl⟩ : syracuseStep 2904179 = 4356269) B4356269
theorem B1936119 : Blo 1935435 1936119 := bstep (se 1 (by rfl) ⟨1452089, by rfl⟩ : syracuseStep 1936119 = 2904179) B2904179
theorem B9303893 : Blo 1935435 9303893 := bbase (se 9 (by rfl) ⟨27257, by rfl⟩ : syracuseStep 9303893 = 54515) (by norm_num)
theorem B6202595 : Blo 1935435 6202595 := bstep (se 1 (by rfl) ⟨4651946, by rfl⟩ : syracuseStep 6202595 = 9303893) B9303893
theorem B4135063 : Blo 1935435 4135063 := bstep (se 1 (by rfl) ⟨3101297, by rfl⟩ : syracuseStep 4135063 = 6202595) B6202595
theorem B5513417 : Blo 1935435 5513417 := bstep (se 2 (by rfl) ⟨2067531, by rfl⟩ : syracuseStep 5513417 = 4135063) B4135063
theorem B3675611 : Blo 1935435 3675611 := bstep (se 1 (by rfl) ⟨2756708, by rfl⟩ : syracuseStep 3675611 = 5513417) B5513417
theorem B2450407 : Blo 1935435 2450407 := bstep (se 1 (by rfl) ⟨1837805, by rfl⟩ : syracuseStep 2450407 = 3675611) B3675611
theorem B3267209 : Blo 1935435 3267209 := bstep (se 2 (by rfl) ⟨1225203, by rfl⟩ : syracuseStep 3267209 = 2450407) B2450407
theorem B2178139 : Blo 1935435 2178139 := bstep (se 1 (by rfl) ⟨1633604, by rfl⟩ : syracuseStep 2178139 = 3267209) B3267209
theorem B2904185 : Blo 1935435 2904185 := bstep (se 2 (by rfl) ⟨1089069, by rfl⟩ : syracuseStep 2904185 = 2178139) B2178139
theorem B1936123 : Blo 1935435 1936123 := bstep (se 1 (by rfl) ⟨1452092, by rfl⟩ : syracuseStep 1936123 = 2904185) B2904185
theorem B2325977 : Blo 1935435 2325977 := bbase (se 2 (by rfl) ⟨872241, by rfl⟩ : syracuseStep 2325977 = 1744483) (by norm_num)
theorem B24810421 : Blo 1935435 24810421 := bstep (se 5 (by rfl) ⟨1162988, by rfl⟩ : syracuseStep 24810421 = 2325977) B2325977
theorem B33080561 : Blo 1935435 33080561 := bstep (se 2 (by rfl) ⟨12405210, by rfl⟩ : syracuseStep 33080561 = 24810421) B24810421
theorem B22053707 : Blo 1935435 22053707 := bstep (se 1 (by rfl) ⟨16540280, by rfl⟩ : syracuseStep 22053707 = 33080561) B33080561
theorem B14702471 : Blo 1935435 14702471 := bstep (se 1 (by rfl) ⟨11026853, by rfl⟩ : syracuseStep 14702471 = 22053707) B22053707
theorem B9801647 : Blo 1935435 9801647 := bstep (se 1 (by rfl) ⟨7351235, by rfl⟩ : syracuseStep 9801647 = 14702471) B14702471
theorem B6534431 : Blo 1935435 6534431 := bstep (se 1 (by rfl) ⟨4900823, by rfl⟩ : syracuseStep 6534431 = 9801647) B9801647
theorem B4356287 : Blo 1935435 4356287 := bstep (se 1 (by rfl) ⟨3267215, by rfl⟩ : syracuseStep 4356287 = 6534431) B6534431
theorem B2904191 : Blo 1935435 2904191 := bstep (se 1 (by rfl) ⟨2178143, by rfl⟩ : syracuseStep 2904191 = 4356287) B4356287
theorem B1936127 : Blo 1935435 1936127 := bstep (se 1 (by rfl) ⟨1452095, by rfl⟩ : syracuseStep 1936127 = 2904191) B2904191
theorem B2904197 : Blo 1935435 2904197 := bbase (se 4 (by rfl) ⟨272268, by rfl⟩ : syracuseStep 2904197 = 544537) (by norm_num)
theorem B1936131 : Blo 1935435 1936131 := bstep (se 1 (by rfl) ⟨1452098, by rfl⟩ : syracuseStep 1936131 = 2904197) B2904197
theorem B3267229 : Blo 1935435 3267229 := bbase (se 3 (by rfl) ⟨612605, by rfl⟩ : syracuseStep 3267229 = 1225211) (by norm_num)
theorem B4356305 : Blo 1935435 4356305 := bstep (se 2 (by rfl) ⟨1633614, by rfl⟩ : syracuseStep 4356305 = 3267229) B3267229
theorem B2904203 : Blo 1935435 2904203 := bstep (se 1 (by rfl) ⟨2178152, by rfl⟩ : syracuseStep 2904203 = 4356305) B4356305
theorem B1936135 : Blo 1935435 1936135 := bstep (se 1 (by rfl) ⟨1452101, by rfl⟩ : syracuseStep 1936135 = 2904203) B2904203
theorem B2178157 : Blo 1935435 2178157 := bbase (se 3 (by rfl) ⟨408404, by rfl⟩ : syracuseStep 2178157 = 816809) (by norm_num)
theorem B2904209 : Blo 1935435 2904209 := bstep (se 2 (by rfl) ⟨1089078, by rfl⟩ : syracuseStep 2904209 = 2178157) B2178157
theorem B1936139 : Blo 1935435 1936139 := bstep (se 1 (by rfl) ⟨1452104, by rfl⟩ : syracuseStep 1936139 = 2904209) B2904209
theorem B6534485 : Blo 1935435 6534485 := bbase (se 13 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 6534485 = 2393) (by norm_num)
theorem B4356323 : Blo 1935435 4356323 := bstep (se 1 (by rfl) ⟨3267242, by rfl⟩ : syracuseStep 4356323 = 6534485) B6534485
theorem B2904215 : Blo 1935435 2904215 := bstep (se 1 (by rfl) ⟨2178161, by rfl⟩ : syracuseStep 2904215 = 4356323) B4356323
theorem B1936143 : Blo 1935435 1936143 := bstep (se 1 (by rfl) ⟨1452107, by rfl⟩ : syracuseStep 1936143 = 2904215) B2904215
theorem B2904221 : Blo 1935435 2904221 := bbase (se 3 (by rfl) ⟨544541, by rfl⟩ : syracuseStep 2904221 = 1089083) (by norm_num)
theorem B1936147 : Blo 1935435 1936147 := bstep (se 1 (by rfl) ⟨1452110, by rfl⟩ : syracuseStep 1936147 = 2904221) B2904221
theorem B4356341 : Blo 1935435 4356341 := bbase (se 5 (by rfl) ⟨204203, by rfl⟩ : syracuseStep 4356341 = 408407) (by norm_num)
theorem B2904227 : Blo 1935435 2904227 := bstep (se 1 (by rfl) ⟨2178170, by rfl⟩ : syracuseStep 2904227 = 4356341) B4356341
theorem B1936151 : Blo 1935435 1936151 := bstep (se 1 (by rfl) ⟨1452113, by rfl⟩ : syracuseStep 1936151 = 2904227) B2904227
theorem B20934101 : Blo 1935435 20934101 := bbase (se 7 (by rfl) ⟨245321, by rfl⟩ : syracuseStep 20934101 = 490643) (by norm_num)
theorem B13956067 : Blo 1935435 13956067 := bstep (se 1 (by rfl) ⟨10467050, by rfl⟩ : syracuseStep 13956067 = 20934101) B20934101
theorem B18608089 : Blo 1935435 18608089 := bstep (se 2 (by rfl) ⟨6978033, by rfl⟩ : syracuseStep 18608089 = 13956067) B13956067
theorem B24810785 : Blo 1935435 24810785 := bstep (se 2 (by rfl) ⟨9304044, by rfl⟩ : syracuseStep 24810785 = 18608089) B18608089
theorem B16540523 : Blo 1935435 16540523 := bstep (se 1 (by rfl) ⟨12405392, by rfl⟩ : syracuseStep 16540523 = 24810785) B24810785
theorem B11027015 : Blo 1935435 11027015 := bstep (se 1 (by rfl) ⟨8270261, by rfl⟩ : syracuseStep 11027015 = 16540523) B16540523
theorem B7351343 : Blo 1935435 7351343 := bstep (se 1 (by rfl) ⟨5513507, by rfl⟩ : syracuseStep 7351343 = 11027015) B11027015
theorem B4900895 : Blo 1935435 4900895 := bstep (se 1 (by rfl) ⟨3675671, by rfl⟩ : syracuseStep 4900895 = 7351343) B7351343
theorem B3267263 : Blo 1935435 3267263 := bstep (se 1 (by rfl) ⟨2450447, by rfl⟩ : syracuseStep 3267263 = 4900895) B4900895
theorem B2178175 : Blo 1935435 2178175 := bstep (se 1 (by rfl) ⟨1633631, by rfl⟩ : syracuseStep 2178175 = 3267263) B3267263
theorem B2904233 : Blo 1935435 2904233 := bstep (se 2 (by rfl) ⟨1089087, by rfl⟩ : syracuseStep 2904233 = 2178175) B2178175
theorem B1936155 : Blo 1935435 1936155 := bstep (se 1 (by rfl) ⟨1452116, by rfl⟩ : syracuseStep 1936155 = 2904233) B2904233
theorem B6202709 : Blo 1935435 6202709 := bbase (se 12 (by rfl) ⟨2271, by rfl⟩ : syracuseStep 6202709 = 4543) (by norm_num)
theorem B4135139 : Blo 1935435 4135139 := bstep (se 1 (by rfl) ⟨3101354, by rfl⟩ : syracuseStep 4135139 = 6202709) B6202709
theorem B2756759 : Blo 1935435 2756759 := bstep (se 1 (by rfl) ⟨2067569, by rfl⟩ : syracuseStep 2756759 = 4135139) B4135139
theorem B7351357 : Blo 1935435 7351357 := bstep (se 3 (by rfl) ⟨1378379, by rfl⟩ : syracuseStep 7351357 = 2756759) B2756759
theorem B9801809 : Blo 1935435 9801809 := bstep (se 2 (by rfl) ⟨3675678, by rfl⟩ : syracuseStep 9801809 = 7351357) B7351357
theorem B6534539 : Blo 1935435 6534539 := bstep (se 1 (by rfl) ⟨4900904, by rfl⟩ : syracuseStep 6534539 = 9801809) B9801809
theorem B4356359 : Blo 1935435 4356359 := bstep (se 1 (by rfl) ⟨3267269, by rfl⟩ : syracuseStep 4356359 = 6534539) B6534539
theorem B2904239 : Blo 1935435 2904239 := bstep (se 1 (by rfl) ⟨2178179, by rfl⟩ : syracuseStep 2904239 = 4356359) B4356359
theorem B1936159 : Blo 1935435 1936159 := bstep (se 1 (by rfl) ⟨1452119, by rfl⟩ : syracuseStep 1936159 = 2904239) B2904239
theorem B2904245 : Blo 1935435 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B1936163 : Blo 1935435 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B4900925 : Blo 1935435 4900925 := bbase (se 3 (by rfl) ⟨918923, by rfl⟩ : syracuseStep 4900925 = 1837847) (by norm_num)
theorem B3267283 : Blo 1935435 3267283 := bstep (se 1 (by rfl) ⟨2450462, by rfl⟩ : syracuseStep 3267283 = 4900925) B4900925
theorem B4356377 : Blo 1935435 4356377 := bstep (se 2 (by rfl) ⟨1633641, by rfl⟩ : syracuseStep 4356377 = 3267283) B3267283
theorem B2904251 : Blo 1935435 2904251 := bstep (se 1 (by rfl) ⟨2178188, by rfl⟩ : syracuseStep 2904251 = 4356377) B4356377
theorem B1936167 : Blo 1935435 1936167 := bstep (se 1 (by rfl) ⟨1452125, by rfl⟩ : syracuseStep 1936167 = 2904251) B2904251
theorem B2178193 : Blo 1935435 2178193 := bbase (se 2 (by rfl) ⟨816822, by rfl⟩ : syracuseStep 2178193 = 1633645) (by norm_num)
theorem B2904257 : Blo 1935435 2904257 := bstep (se 2 (by rfl) ⟨1089096, by rfl⟩ : syracuseStep 2904257 = 2178193) B2178193
theorem B1936171 : Blo 1935435 1936171 := bstep (se 1 (by rfl) ⟨1452128, by rfl⟩ : syracuseStep 1936171 = 2904257) B2904257
theorem B3675709 : Blo 1935435 3675709 := bbase (se 3 (by rfl) ⟨689195, by rfl⟩ : syracuseStep 3675709 = 1378391) (by norm_num)
theorem B4900945 : Blo 1935435 4900945 := bstep (se 2 (by rfl) ⟨1837854, by rfl⟩ : syracuseStep 4900945 = 3675709) B3675709
theorem B6534593 : Blo 1935435 6534593 := bstep (se 2 (by rfl) ⟨2450472, by rfl⟩ : syracuseStep 6534593 = 4900945) B4900945
theorem B4356395 : Blo 1935435 4356395 := bstep (se 1 (by rfl) ⟨3267296, by rfl⟩ : syracuseStep 4356395 = 6534593) B6534593
theorem B2904263 : Blo 1935435 2904263 := bstep (se 1 (by rfl) ⟨2178197, by rfl⟩ : syracuseStep 2904263 = 4356395) B4356395
theorem B1936175 : Blo 1935435 1936175 := bstep (se 1 (by rfl) ⟨1452131, by rfl⟩ : syracuseStep 1936175 = 2904263) B2904263
theorem B2904269 : Blo 1935435 2904269 := bbase (se 3 (by rfl) ⟨544550, by rfl⟩ : syracuseStep 2904269 = 1089101) (by norm_num)
theorem B1936179 : Blo 1935435 1936179 := bstep (se 1 (by rfl) ⟨1452134, by rfl⟩ : syracuseStep 1936179 = 2904269) B2904269
theorem B4356413 : Blo 1935435 4356413 := bbase (se 3 (by rfl) ⟨816827, by rfl⟩ : syracuseStep 4356413 = 1633655) (by norm_num)
theorem B2904275 : Blo 1935435 2904275 := bstep (se 1 (by rfl) ⟨2178206, by rfl⟩ : syracuseStep 2904275 = 4356413) B4356413
theorem B1936183 : Blo 1935435 1936183 := bstep (se 1 (by rfl) ⟨1452137, by rfl⟩ : syracuseStep 1936183 = 2904275) B2904275
theorem B3267317 : Blo 1935435 3267317 := bbase (se 5 (by rfl) ⟨153155, by rfl⟩ : syracuseStep 3267317 = 306311) (by norm_num)
theorem B2178211 : Blo 1935435 2178211 := bstep (se 1 (by rfl) ⟨1633658, by rfl⟩ : syracuseStep 2178211 = 3267317) B3267317
theorem B2904281 : Blo 1935435 2904281 := bstep (se 2 (by rfl) ⟨1089105, by rfl⟩ : syracuseStep 2904281 = 2178211) B2178211
theorem B1936187 : Blo 1935435 1936187 := bstep (se 1 (by rfl) ⟨1452140, by rfl⟩ : syracuseStep 1936187 = 2904281) B2904281
theorem B6714181 : Blo 1935435 6714181 := bbase (se 4 (by rfl) ⟨629454, by rfl⟩ : syracuseStep 6714181 = 1258909) (by norm_num)
theorem B8952241 : Blo 1935435 8952241 := bstep (se 2 (by rfl) ⟨3357090, by rfl⟩ : syracuseStep 8952241 = 6714181) B6714181
theorem B11936321 : Blo 1935435 11936321 := bstep (se 2 (by rfl) ⟨4476120, by rfl⟩ : syracuseStep 11936321 = 8952241) B8952241
theorem B7957547 : Blo 1935435 7957547 := bstep (se 1 (by rfl) ⟨5968160, by rfl⟩ : syracuseStep 7957547 = 11936321) B11936321
theorem B5305031 : Blo 1935435 5305031 := bstep (se 1 (by rfl) ⟨3978773, by rfl⟩ : syracuseStep 5305031 = 7957547) B7957547
theorem B3536687 : Blo 1935435 3536687 := bstep (se 1 (by rfl) ⟨2652515, by rfl⟩ : syracuseStep 3536687 = 5305031) B5305031
theorem B2357791 : Blo 1935435 2357791 := bstep (se 1 (by rfl) ⟨1768343, by rfl⟩ : syracuseStep 2357791 = 3536687) B3536687
theorem B12574885 : Blo 1935435 12574885 := bstep (se 4 (by rfl) ⟨1178895, by rfl⟩ : syracuseStep 12574885 = 2357791) B2357791
theorem B16766513 : Blo 1935435 16766513 := bstep (se 2 (by rfl) ⟨6287442, by rfl⟩ : syracuseStep 16766513 = 12574885) B12574885
theorem B11177675 : Blo 1935435 11177675 := bstep (se 1 (by rfl) ⟨8383256, by rfl⟩ : syracuseStep 11177675 = 16766513) B16766513
theorem B7451783 : Blo 1935435 7451783 := bstep (se 1 (by rfl) ⟨5588837, by rfl⟩ : syracuseStep 7451783 = 11177675) B11177675
theorem B4967855 : Blo 1935435 4967855 := bstep (se 1 (by rfl) ⟨3725891, by rfl⟩ : syracuseStep 4967855 = 7451783) B7451783
theorem B3311903 : Blo 1935435 3311903 := bstep (se 1 (by rfl) ⟨2483927, by rfl⟩ : syracuseStep 3311903 = 4967855) B4967855
theorem B2207935 : Blo 1935435 2207935 := bstep (se 1 (by rfl) ⟨1655951, by rfl⟩ : syracuseStep 2207935 = 3311903) B3311903
theorem B2943913 : Blo 1935435 2943913 := bstep (se 2 (by rfl) ⟨1103967, by rfl⟩ : syracuseStep 2943913 = 2207935) B2207935
theorem B3925217 : Blo 1935435 3925217 := bstep (se 2 (by rfl) ⟨1471956, by rfl⟩ : syracuseStep 3925217 = 2943913) B2943913
theorem B10467245 : Blo 1935435 10467245 := bstep (se 3 (by rfl) ⟨1962608, by rfl⟩ : syracuseStep 10467245 = 3925217) B3925217
theorem B6978163 : Blo 1935435 6978163 := bstep (se 1 (by rfl) ⟨5233622, by rfl⟩ : syracuseStep 6978163 = 10467245) B10467245
theorem B9304217 : Blo 1935435 9304217 := bstep (se 2 (by rfl) ⟨3489081, by rfl⟩ : syracuseStep 9304217 = 6978163) B6978163
theorem B6202811 : Blo 1935435 6202811 := bstep (se 1 (by rfl) ⟨4652108, by rfl⟩ : syracuseStep 6202811 = 9304217) B9304217
theorem B4135207 : Blo 1935435 4135207 := bstep (se 1 (by rfl) ⟨3101405, by rfl⟩ : syracuseStep 4135207 = 6202811) B6202811
theorem B5513609 : Blo 1935435 5513609 := bstep (se 2 (by rfl) ⟨2067603, by rfl⟩ : syracuseStep 5513609 = 4135207) B4135207
theorem B14702957 : Blo 1935435 14702957 := bstep (se 3 (by rfl) ⟨2756804, by rfl⟩ : syracuseStep 14702957 = 5513609) B5513609
theorem B9801971 : Blo 1935435 9801971 := bstep (se 1 (by rfl) ⟨7351478, by rfl⟩ : syracuseStep 9801971 = 14702957) B14702957
theorem B6534647 : Blo 1935435 6534647 := bstep (se 1 (by rfl) ⟨4900985, by rfl⟩ : syracuseStep 6534647 = 9801971) B9801971
theorem B4356431 : Blo 1935435 4356431 := bstep (se 1 (by rfl) ⟨3267323, by rfl⟩ : syracuseStep 4356431 = 6534647) B6534647
theorem B2904287 : Blo 1935435 2904287 := bstep (se 1 (by rfl) ⟨2178215, by rfl⟩ : syracuseStep 2904287 = 4356431) B4356431
theorem B1936191 : Blo 1935435 1936191 := bstep (se 1 (by rfl) ⟨1452143, by rfl⟩ : syracuseStep 1936191 = 2904287) B2904287
theorem B2904293 : Blo 1935435 2904293 := bbase (se 4 (by rfl) ⟨272277, by rfl⟩ : syracuseStep 2904293 = 544555) (by norm_num)
theorem B1936195 : Blo 1935435 1936195 := bstep (se 1 (by rfl) ⟨1452146, by rfl⟩ : syracuseStep 1936195 = 2904293) B2904293
theorem B2207945 : Blo 1935435 2207945 := bbase (se 2 (by rfl) ⟨827979, by rfl⟩ : syracuseStep 2207945 = 1655959) (by norm_num)
theorem B5887853 : Blo 1935435 5887853 := bstep (se 3 (by rfl) ⟨1103972, by rfl⟩ : syracuseStep 5887853 = 2207945) B2207945
theorem B3925235 : Blo 1935435 3925235 := bstep (se 1 (by rfl) ⟨2943926, by rfl⟩ : syracuseStep 3925235 = 5887853) B5887853
theorem B2616823 : Blo 1935435 2616823 := bstep (se 1 (by rfl) ⟨1962617, by rfl⟩ : syracuseStep 2616823 = 3925235) B3925235
theorem B3489097 : Blo 1935435 3489097 := bstep (se 2 (by rfl) ⟨1308411, by rfl⟩ : syracuseStep 3489097 = 2616823) B2616823
theorem B4652129 : Blo 1935435 4652129 := bstep (se 2 (by rfl) ⟨1744548, by rfl⟩ : syracuseStep 4652129 = 3489097) B3489097
theorem B3101419 : Blo 1935435 3101419 := bstep (se 1 (by rfl) ⟨2326064, by rfl⟩ : syracuseStep 3101419 = 4652129) B4652129
theorem B4135225 : Blo 1935435 4135225 := bstep (se 2 (by rfl) ⟨1550709, by rfl⟩ : syracuseStep 4135225 = 3101419) B3101419
theorem B5513633 : Blo 1935435 5513633 := bstep (se 2 (by rfl) ⟨2067612, by rfl⟩ : syracuseStep 5513633 = 4135225) B4135225
theorem B3675755 : Blo 1935435 3675755 := bstep (se 1 (by rfl) ⟨2756816, by rfl⟩ : syracuseStep 3675755 = 5513633) B5513633
theorem B2450503 : Blo 1935435 2450503 := bstep (se 1 (by rfl) ⟨1837877, by rfl⟩ : syracuseStep 2450503 = 3675755) B3675755
theorem B3267337 : Blo 1935435 3267337 := bstep (se 2 (by rfl) ⟨1225251, by rfl⟩ : syracuseStep 3267337 = 2450503) B2450503
theorem B4356449 : Blo 1935435 4356449 := bstep (se 2 (by rfl) ⟨1633668, by rfl⟩ : syracuseStep 4356449 = 3267337) B3267337
theorem B2904299 : Blo 1935435 2904299 := bstep (se 1 (by rfl) ⟨2178224, by rfl⟩ : syracuseStep 2904299 = 4356449) B4356449
theorem B1936199 : Blo 1935435 1936199 := bstep (se 1 (by rfl) ⟨1452149, by rfl⟩ : syracuseStep 1936199 = 2904299) B2904299
theorem B2178229 : Blo 1935435 2178229 := bbase (se 5 (by rfl) ⟨102104, by rfl⟩ : syracuseStep 2178229 = 204209) (by norm_num)
theorem B2904305 : Blo 1935435 2904305 := bstep (se 2 (by rfl) ⟨1089114, by rfl⟩ : syracuseStep 2904305 = 2178229) B2178229
theorem B1936203 : Blo 1935435 1936203 := bstep (se 1 (by rfl) ⟨1452152, by rfl⟩ : syracuseStep 1936203 = 2904305) B2904305
theorem B2450513 : Blo 1935435 2450513 := bbase (se 2 (by rfl) ⟨918942, by rfl⟩ : syracuseStep 2450513 = 1837885) (by norm_num)
theorem B6534701 : Blo 1935435 6534701 := bstep (se 3 (by rfl) ⟨1225256, by rfl⟩ : syracuseStep 6534701 = 2450513) B2450513
theorem B4356467 : Blo 1935435 4356467 := bstep (se 1 (by rfl) ⟨3267350, by rfl⟩ : syracuseStep 4356467 = 6534701) B6534701
theorem B2904311 : Blo 1935435 2904311 := bstep (se 1 (by rfl) ⟨2178233, by rfl⟩ : syracuseStep 2904311 = 4356467) B4356467
theorem B1936207 : Blo 1935435 1936207 := bstep (se 1 (by rfl) ⟨1452155, by rfl⟩ : syracuseStep 1936207 = 2904311) B2904311
theorem B2904317 : Blo 1935435 2904317 := bbase (se 3 (by rfl) ⟨544559, by rfl⟩ : syracuseStep 2904317 = 1089119) (by norm_num)
theorem B1936211 : Blo 1935435 1936211 := bstep (se 1 (by rfl) ⟨1452158, by rfl⟩ : syracuseStep 1936211 = 2904317) B2904317
theorem B4356485 : Blo 1935435 4356485 := bbase (se 4 (by rfl) ⟨408420, by rfl⟩ : syracuseStep 4356485 = 816841) (by norm_num)
theorem B2904323 : Blo 1935435 2904323 := bstep (se 1 (by rfl) ⟨2178242, by rfl⟩ : syracuseStep 2904323 = 4356485) B4356485
theorem B1936215 : Blo 1935435 1936215 := bstep (se 1 (by rfl) ⟨1452161, by rfl⟩ : syracuseStep 1936215 = 2904323) B2904323
theorem B2756845 : Blo 1935435 2756845 := bbase (se 3 (by rfl) ⟨516908, by rfl⟩ : syracuseStep 2756845 = 1033817) (by norm_num)
theorem B3675793 : Blo 1935435 3675793 := bstep (se 2 (by rfl) ⟨1378422, by rfl⟩ : syracuseStep 3675793 = 2756845) B2756845
theorem B4901057 : Blo 1935435 4901057 := bstep (se 2 (by rfl) ⟨1837896, by rfl⟩ : syracuseStep 4901057 = 3675793) B3675793
theorem B3267371 : Blo 1935435 3267371 := bstep (se 1 (by rfl) ⟨2450528, by rfl⟩ : syracuseStep 3267371 = 4901057) B4901057
theorem B2178247 : Blo 1935435 2178247 := bstep (se 1 (by rfl) ⟨1633685, by rfl⟩ : syracuseStep 2178247 = 3267371) B3267371
theorem B2904329 : Blo 1935435 2904329 := bstep (se 2 (by rfl) ⟨1089123, by rfl⟩ : syracuseStep 2904329 = 2178247) B2178247
theorem B1936219 : Blo 1935435 1936219 := bstep (se 1 (by rfl) ⟨1452164, by rfl⟩ : syracuseStep 1936219 = 2904329) B2904329
theorem B9802133 : Blo 1935435 9802133 := bbase (se 6 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 9802133 = 459475) (by norm_num)
theorem B6534755 : Blo 1935435 6534755 := bstep (se 1 (by rfl) ⟨4901066, by rfl⟩ : syracuseStep 6534755 = 9802133) B9802133
theorem B4356503 : Blo 1935435 4356503 := bstep (se 1 (by rfl) ⟨3267377, by rfl⟩ : syracuseStep 4356503 = 6534755) B6534755
theorem B2904335 : Blo 1935435 2904335 := bstep (se 1 (by rfl) ⟨2178251, by rfl⟩ : syracuseStep 2904335 = 4356503) B4356503
theorem B1936223 : Blo 1935435 1936223 := bstep (se 1 (by rfl) ⟨1452167, by rfl⟩ : syracuseStep 1936223 = 2904335) B2904335
theorem B2904341 : Blo 1935435 2904341 := bbase (se 6 (by rfl) ⟨68070, by rfl⟩ : syracuseStep 2904341 = 136141) (by norm_num)
theorem B1936227 : Blo 1935435 1936227 := bstep (se 1 (by rfl) ⟨1452170, by rfl⟩ : syracuseStep 1936227 = 2904341) B2904341
theorem B1962649 : Blo 1935435 1962649 := bbase (se 2 (by rfl) ⟨735993, by rfl⟩ : syracuseStep 1962649 = 1471987) (by norm_num)
theorem B10467461 : Blo 1935435 10467461 := bstep (se 4 (by rfl) ⟨981324, by rfl⟩ : syracuseStep 10467461 = 1962649) B1962649
theorem B6978307 : Blo 1935435 6978307 := bstep (se 1 (by rfl) ⟨5233730, by rfl⟩ : syracuseStep 6978307 = 10467461) B10467461
theorem B9304409 : Blo 1935435 9304409 := bstep (se 2 (by rfl) ⟨3489153, by rfl⟩ : syracuseStep 9304409 = 6978307) B6978307
theorem B24811757 : Blo 1935435 24811757 := bstep (se 3 (by rfl) ⟨4652204, by rfl⟩ : syracuseStep 24811757 = 9304409) B9304409
theorem B16541171 : Blo 1935435 16541171 := bstep (se 1 (by rfl) ⟨12405878, by rfl⟩ : syracuseStep 16541171 = 24811757) B24811757
theorem B11027447 : Blo 1935435 11027447 := bstep (se 1 (by rfl) ⟨8270585, by rfl⟩ : syracuseStep 11027447 = 16541171) B16541171
theorem B7351631 : Blo 1935435 7351631 := bstep (se 1 (by rfl) ⟨5513723, by rfl⟩ : syracuseStep 7351631 = 11027447) B11027447
theorem B4901087 : Blo 1935435 4901087 := bstep (se 1 (by rfl) ⟨3675815, by rfl⟩ : syracuseStep 4901087 = 7351631) B7351631
theorem B3267391 : Blo 1935435 3267391 := bstep (se 1 (by rfl) ⟨2450543, by rfl⟩ : syracuseStep 3267391 = 4901087) B4901087
theorem B4356521 : Blo 1935435 4356521 := bstep (se 2 (by rfl) ⟨1633695, by rfl⟩ : syracuseStep 4356521 = 3267391) B3267391
theorem B2904347 : Blo 1935435 2904347 := bstep (se 1 (by rfl) ⟨2178260, by rfl⟩ : syracuseStep 2904347 = 4356521) B4356521
theorem B1936231 : Blo 1935435 1936231 := bstep (se 1 (by rfl) ⟨1452173, by rfl⟩ : syracuseStep 1936231 = 2904347) B2904347
theorem B2178265 : Blo 1935435 2178265 := bbase (se 2 (by rfl) ⟨816849, by rfl⟩ : syracuseStep 2178265 = 1633699) (by norm_num)
theorem B2904353 : Blo 1935435 2904353 := bstep (se 2 (by rfl) ⟨1089132, by rfl⟩ : syracuseStep 2904353 = 2178265) B2178265
theorem B1936235 : Blo 1935435 1936235 := bstep (se 1 (by rfl) ⟨1452176, by rfl⟩ : syracuseStep 1936235 = 2904353) B2904353
theorem B2616877 : Blo 1935435 2616877 := bbase (se 3 (by rfl) ⟨490664, by rfl⟩ : syracuseStep 2616877 = 981329) (by norm_num)
theorem B3489169 : Blo 1935435 3489169 := bstep (se 2 (by rfl) ⟨1308438, by rfl⟩ : syracuseStep 3489169 = 2616877) B2616877
theorem B4652225 : Blo 1935435 4652225 := bstep (se 2 (by rfl) ⟨1744584, by rfl⟩ : syracuseStep 4652225 = 3489169) B3489169
theorem B3101483 : Blo 1935435 3101483 := bstep (se 1 (by rfl) ⟨2326112, by rfl⟩ : syracuseStep 3101483 = 4652225) B4652225
theorem B2067655 : Blo 1935435 2067655 := bstep (se 1 (by rfl) ⟨1550741, by rfl⟩ : syracuseStep 2067655 = 3101483) B3101483
theorem B2756873 : Blo 1935435 2756873 := bstep (se 2 (by rfl) ⟨1033827, by rfl⟩ : syracuseStep 2756873 = 2067655) B2067655
theorem B7351661 : Blo 1935435 7351661 := bstep (se 3 (by rfl) ⟨1378436, by rfl⟩ : syracuseStep 7351661 = 2756873) B2756873
theorem B4901107 : Blo 1935435 4901107 := bstep (se 1 (by rfl) ⟨3675830, by rfl⟩ : syracuseStep 4901107 = 7351661) B7351661
theorem B6534809 : Blo 1935435 6534809 := bstep (se 2 (by rfl) ⟨2450553, by rfl⟩ : syracuseStep 6534809 = 4901107) B4901107
theorem B4356539 : Blo 1935435 4356539 := bstep (se 1 (by rfl) ⟨3267404, by rfl⟩ : syracuseStep 4356539 = 6534809) B6534809
theorem B2904359 : Blo 1935435 2904359 := bstep (se 1 (by rfl) ⟨2178269, by rfl⟩ : syracuseStep 2904359 = 4356539) B4356539
theorem B1936239 : Blo 1935435 1936239 := bstep (se 1 (by rfl) ⟨1452179, by rfl⟩ : syracuseStep 1936239 = 2904359) B2904359
theorem B2904365 : Blo 1935435 2904365 := bbase (se 3 (by rfl) ⟨544568, by rfl⟩ : syracuseStep 2904365 = 1089137) (by norm_num)
theorem B1936243 : Blo 1935435 1936243 := bstep (se 1 (by rfl) ⟨1452182, by rfl⟩ : syracuseStep 1936243 = 2904365) B2904365
theorem B4356557 : Blo 1935435 4356557 := bbase (se 3 (by rfl) ⟨816854, by rfl⟩ : syracuseStep 4356557 = 1633709) (by norm_num)
theorem B2904371 : Blo 1935435 2904371 := bstep (se 1 (by rfl) ⟨2178278, by rfl⟩ : syracuseStep 2904371 = 4356557) B4356557
theorem B1936247 : Blo 1935435 1936247 := bstep (se 1 (by rfl) ⟨1452185, by rfl⟩ : syracuseStep 1936247 = 2904371) B2904371
theorem B2450569 : Blo 1935435 2450569 := bbase (se 2 (by rfl) ⟨918963, by rfl⟩ : syracuseStep 2450569 = 1837927) (by norm_num)
theorem B3267425 : Blo 1935435 3267425 := bstep (se 2 (by rfl) ⟨1225284, by rfl⟩ : syracuseStep 3267425 = 2450569) B2450569
theorem B2178283 : Blo 1935435 2178283 := bstep (se 1 (by rfl) ⟨1633712, by rfl⟩ : syracuseStep 2178283 = 3267425) B3267425
theorem B2904377 : Blo 1935435 2904377 := bstep (se 2 (by rfl) ⟨1089141, by rfl⟩ : syracuseStep 2904377 = 2178283) B2178283
theorem B1936251 : Blo 1935435 1936251 := bstep (se 1 (by rfl) ⟨1452188, by rfl⟩ : syracuseStep 1936251 = 2904377) B2904377
theorem B1962673 : Blo 1935435 1962673 := bbase (se 2 (by rfl) ⟨736002, by rfl⟩ : syracuseStep 1962673 = 1472005) (by norm_num)
theorem B41870357 : Blo 1935435 41870357 := bstep (se 6 (by rfl) ⟨981336, by rfl⟩ : syracuseStep 41870357 = 1962673) B1962673
theorem B27913571 : Blo 1935435 27913571 := bstep (se 1 (by rfl) ⟨20935178, by rfl⟩ : syracuseStep 27913571 = 41870357) B41870357
theorem B18609047 : Blo 1935435 18609047 := bstep (se 1 (by rfl) ⟨13956785, by rfl⟩ : syracuseStep 18609047 = 27913571) B27913571
theorem B12406031 : Blo 1935435 12406031 := bstep (se 1 (by rfl) ⟨9304523, by rfl⟩ : syracuseStep 12406031 = 18609047) B18609047
theorem B8270687 : Blo 1935435 8270687 := bstep (se 1 (by rfl) ⟨6203015, by rfl⟩ : syracuseStep 8270687 = 12406031) B12406031
theorem B22055165 : Blo 1935435 22055165 := bstep (se 3 (by rfl) ⟨4135343, by rfl⟩ : syracuseStep 22055165 = 8270687) B8270687
theorem B14703443 : Blo 1935435 14703443 := bstep (se 1 (by rfl) ⟨11027582, by rfl⟩ : syracuseStep 14703443 = 22055165) B22055165
theorem B9802295 : Blo 1935435 9802295 := bstep (se 1 (by rfl) ⟨7351721, by rfl⟩ : syracuseStep 9802295 = 14703443) B14703443
theorem B6534863 : Blo 1935435 6534863 := bstep (se 1 (by rfl) ⟨4901147, by rfl⟩ : syracuseStep 6534863 = 9802295) B9802295
theorem B4356575 : Blo 1935435 4356575 := bstep (se 1 (by rfl) ⟨3267431, by rfl⟩ : syracuseStep 4356575 = 6534863) B6534863
theorem B2904383 : Blo 1935435 2904383 := bstep (se 1 (by rfl) ⟨2178287, by rfl⟩ : syracuseStep 2904383 = 4356575) B4356575
theorem B1936255 : Blo 1935435 1936255 := bstep (se 1 (by rfl) ⟨1452191, by rfl⟩ : syracuseStep 1936255 = 2904383) B2904383
theorem B2904389 : Blo 1935435 2904389 := bbase (se 4 (by rfl) ⟨272286, by rfl⟩ : syracuseStep 2904389 = 544573) (by norm_num)
theorem B1936259 : Blo 1935435 1936259 := bstep (se 1 (by rfl) ⟨1452194, by rfl⟩ : syracuseStep 1936259 = 2904389) B2904389
theorem B3267445 : Blo 1935435 3267445 := bbase (se 5 (by rfl) ⟨153161, by rfl⟩ : syracuseStep 3267445 = 306323) (by norm_num)
theorem B4356593 : Blo 1935435 4356593 := bstep (se 2 (by rfl) ⟨1633722, by rfl⟩ : syracuseStep 4356593 = 3267445) B3267445
theorem B2904395 : Blo 1935435 2904395 := bstep (se 1 (by rfl) ⟨2178296, by rfl⟩ : syracuseStep 2904395 = 4356593) B4356593
theorem B1936263 : Blo 1935435 1936263 := bstep (se 1 (by rfl) ⟨1452197, by rfl⟩ : syracuseStep 1936263 = 2904395) B2904395
theorem B2178301 : Blo 1935435 2178301 := bbase (se 3 (by rfl) ⟨408431, by rfl⟩ : syracuseStep 2178301 = 816863) (by norm_num)
theorem B2904401 : Blo 1935435 2904401 := bstep (se 2 (by rfl) ⟨1089150, by rfl⟩ : syracuseStep 2904401 = 2178301) B2178301
theorem B1936267 : Blo 1935435 1936267 := bstep (se 1 (by rfl) ⟨1452200, by rfl⟩ : syracuseStep 1936267 = 2904401) B2904401
theorem B6534917 : Blo 1935435 6534917 := bbase (se 4 (by rfl) ⟨612648, by rfl⟩ : syracuseStep 6534917 = 1225297) (by norm_num)
theorem B4356611 : Blo 1935435 4356611 := bstep (se 1 (by rfl) ⟨3267458, by rfl⟩ : syracuseStep 4356611 = 6534917) B6534917
theorem B2904407 : Blo 1935435 2904407 := bstep (se 1 (by rfl) ⟨2178305, by rfl⟩ : syracuseStep 2904407 = 4356611) B4356611
theorem B1936271 : Blo 1935435 1936271 := bstep (se 1 (by rfl) ⟨1452203, by rfl⟩ : syracuseStep 1936271 = 2904407) B2904407
theorem B2904413 : Blo 1935435 2904413 := bbase (se 3 (by rfl) ⟨544577, by rfl⟩ : syracuseStep 2904413 = 1089155) (by norm_num)
theorem B1936275 : Blo 1935435 1936275 := bstep (se 1 (by rfl) ⟨1452206, by rfl⟩ : syracuseStep 1936275 = 2904413) B2904413
theorem B4356629 : Blo 1935435 4356629 := bbase (se 6 (by rfl) ⟨102108, by rfl⟩ : syracuseStep 4356629 = 204217) (by norm_num)
theorem B2904419 : Blo 1935435 2904419 := bstep (se 1 (by rfl) ⟨2178314, by rfl⟩ : syracuseStep 2904419 = 4356629) B4356629
theorem B1936279 : Blo 1935435 1936279 := bstep (se 1 (by rfl) ⟨1452209, by rfl⟩ : syracuseStep 1936279 = 2904419) B2904419
theorem B7351829 : Blo 1935435 7351829 := bbase (se 6 (by rfl) ⟨172308, by rfl⟩ : syracuseStep 7351829 = 344617) (by norm_num)
theorem B4901219 : Blo 1935435 4901219 := bstep (se 1 (by rfl) ⟨3675914, by rfl⟩ : syracuseStep 4901219 = 7351829) B7351829
theorem B3267479 : Blo 1935435 3267479 := bstep (se 1 (by rfl) ⟨2450609, by rfl⟩ : syracuseStep 3267479 = 4901219) B4901219
theorem B2178319 : Blo 1935435 2178319 := bstep (se 1 (by rfl) ⟨1633739, by rfl⟩ : syracuseStep 2178319 = 3267479) B3267479
theorem B2904425 : Blo 1935435 2904425 := bstep (se 2 (by rfl) ⟨1089159, by rfl⟩ : syracuseStep 2904425 = 2178319) B2178319
theorem B1936283 : Blo 1935435 1936283 := bstep (se 1 (by rfl) ⟨1452212, by rfl⟩ : syracuseStep 1936283 = 2904425) B2904425
theorem B11027765 : Blo 1935435 11027765 := bbase (se 5 (by rfl) ⟨516926, by rfl⟩ : syracuseStep 11027765 = 1033853) (by norm_num)
theorem B7351843 : Blo 1935435 7351843 := bstep (se 1 (by rfl) ⟨5513882, by rfl⟩ : syracuseStep 7351843 = 11027765) B11027765
theorem B9802457 : Blo 1935435 9802457 := bstep (se 2 (by rfl) ⟨3675921, by rfl⟩ : syracuseStep 9802457 = 7351843) B7351843
theorem B6534971 : Blo 1935435 6534971 := bstep (se 1 (by rfl) ⟨4901228, by rfl⟩ : syracuseStep 6534971 = 9802457) B9802457
theorem B4356647 : Blo 1935435 4356647 := bstep (se 1 (by rfl) ⟨3267485, by rfl⟩ : syracuseStep 4356647 = 6534971) B6534971
theorem B2904431 : Blo 1935435 2904431 := bstep (se 1 (by rfl) ⟨2178323, by rfl⟩ : syracuseStep 2904431 = 4356647) B4356647
theorem B1936287 : Blo 1935435 1936287 := bstep (se 1 (by rfl) ⟨1452215, by rfl⟩ : syracuseStep 1936287 = 2904431) B2904431
theorem B2904437 : Blo 1935435 2904437 := bbase (se 5 (by rfl) ⟨136145, by rfl⟩ : syracuseStep 2904437 = 272291) (by norm_num)
theorem B1936291 : Blo 1935435 1936291 := bstep (se 1 (by rfl) ⟨1452218, by rfl⟩ : syracuseStep 1936291 = 2904437) B2904437
theorem B3101573 : Blo 1935435 3101573 := bbase (se 4 (by rfl) ⟨290772, by rfl⟩ : syracuseStep 3101573 = 581545) (by norm_num)
theorem B2067715 : Blo 1935435 2067715 := bstep (se 1 (by rfl) ⟨1550786, by rfl⟩ : syracuseStep 2067715 = 3101573) B3101573
theorem B2756953 : Blo 1935435 2756953 := bstep (se 2 (by rfl) ⟨1033857, by rfl⟩ : syracuseStep 2756953 = 2067715) B2067715
theorem B3675937 : Blo 1935435 3675937 := bstep (se 2 (by rfl) ⟨1378476, by rfl⟩ : syracuseStep 3675937 = 2756953) B2756953
theorem B4901249 : Blo 1935435 4901249 := bstep (se 2 (by rfl) ⟨1837968, by rfl⟩ : syracuseStep 4901249 = 3675937) B3675937
theorem B3267499 : Blo 1935435 3267499 := bstep (se 1 (by rfl) ⟨2450624, by rfl⟩ : syracuseStep 3267499 = 4901249) B4901249
theorem B4356665 : Blo 1935435 4356665 := bstep (se 2 (by rfl) ⟨1633749, by rfl⟩ : syracuseStep 4356665 = 3267499) B3267499
theorem B2904443 : Blo 1935435 2904443 := bstep (se 1 (by rfl) ⟨2178332, by rfl⟩ : syracuseStep 2904443 = 4356665) B4356665
theorem B1936295 : Blo 1935435 1936295 := bstep (se 1 (by rfl) ⟨1452221, by rfl⟩ : syracuseStep 1936295 = 2904443) B2904443
theorem B2178337 : Blo 1935435 2178337 := bbase (se 2 (by rfl) ⟨816876, by rfl⟩ : syracuseStep 2178337 = 1633753) (by norm_num)
theorem B2904449 : Blo 1935435 2904449 := bstep (se 2 (by rfl) ⟨1089168, by rfl⟩ : syracuseStep 2904449 = 2178337) B2178337
theorem B1936299 : Blo 1935435 1936299 := bstep (se 1 (by rfl) ⟨1452224, by rfl⟩ : syracuseStep 1936299 = 2904449) B2904449
theorem B4901269 : Blo 1935435 4901269 := bbase (se 6 (by rfl) ⟨114873, by rfl⟩ : syracuseStep 4901269 = 229747) (by norm_num)
theorem B6535025 : Blo 1935435 6535025 := bstep (se 2 (by rfl) ⟨2450634, by rfl⟩ : syracuseStep 6535025 = 4901269) B4901269
theorem B4356683 : Blo 1935435 4356683 := bstep (se 1 (by rfl) ⟨3267512, by rfl⟩ : syracuseStep 4356683 = 6535025) B6535025
theorem B2904455 : Blo 1935435 2904455 := bstep (se 1 (by rfl) ⟨2178341, by rfl⟩ : syracuseStep 2904455 = 4356683) B4356683
theorem B1936303 : Blo 1935435 1936303 := bstep (se 1 (by rfl) ⟨1452227, by rfl⟩ : syracuseStep 1936303 = 2904455) B2904455
theorem B2904461 : Blo 1935435 2904461 := bbase (se 3 (by rfl) ⟨544586, by rfl⟩ : syracuseStep 2904461 = 1089173) (by norm_num)
theorem B1936307 : Blo 1935435 1936307 := bstep (se 1 (by rfl) ⟨1452230, by rfl⟩ : syracuseStep 1936307 = 2904461) B2904461
theorem B4356701 : Blo 1935435 4356701 := bbase (se 3 (by rfl) ⟨816881, by rfl⟩ : syracuseStep 4356701 = 1633763) (by norm_num)
theorem B2904467 : Blo 1935435 2904467 := bstep (se 1 (by rfl) ⟨2178350, by rfl⟩ : syracuseStep 2904467 = 4356701) B4356701
theorem B1936311 : Blo 1935435 1936311 := bstep (se 1 (by rfl) ⟨1452233, by rfl⟩ : syracuseStep 1936311 = 2904467) B2904467
theorem B3267533 : Blo 1935435 3267533 := bbase (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) (by norm_num)
theorem B2178355 : Blo 1935435 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B2904473 : Blo 1935435 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B1936315 : Blo 1935435 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B5968549 : Blo 1935435 5968549 := bbase (se 4 (by rfl) ⟨559551, by rfl⟩ : syracuseStep 5968549 = 1119103) (by norm_num)
theorem B31832261 : Blo 1935435 31832261 := bstep (se 4 (by rfl) ⟨2984274, by rfl⟩ : syracuseStep 31832261 = 5968549) B5968549
theorem B21221507 : Blo 1935435 21221507 := bstep (se 1 (by rfl) ⟨15916130, by rfl⟩ : syracuseStep 21221507 = 31832261) B31832261
theorem B14147671 : Blo 1935435 14147671 := bstep (se 1 (by rfl) ⟨10610753, by rfl⟩ : syracuseStep 14147671 = 21221507) B21221507
theorem B18863561 : Blo 1935435 18863561 := bstep (se 2 (by rfl) ⟨7073835, by rfl⟩ : syracuseStep 18863561 = 14147671) B14147671
theorem B50302829 : Blo 1935435 50302829 := bstep (se 3 (by rfl) ⟨9431780, by rfl⟩ : syracuseStep 50302829 = 18863561) B18863561
theorem B33535219 : Blo 1935435 33535219 := bstep (se 1 (by rfl) ⟨25151414, by rfl⟩ : syracuseStep 33535219 = 50302829) B50302829
theorem B44713625 : Blo 1935435 44713625 := bstep (se 2 (by rfl) ⟨16767609, by rfl⟩ : syracuseStep 44713625 = 33535219) B33535219
theorem B119236333 : Blo 1935435 119236333 := bstep (se 3 (by rfl) ⟨22356812, by rfl⟩ : syracuseStep 119236333 = 44713625) B44713625
theorem B158981777 : Blo 1935435 158981777 := bstep (se 2 (by rfl) ⟨59618166, by rfl⟩ : syracuseStep 158981777 = 119236333) B119236333
theorem B105987851 : Blo 1935435 105987851 := bstep (se 1 (by rfl) ⟨79490888, by rfl⟩ : syracuseStep 105987851 = 158981777) B158981777
theorem B70658567 : Blo 1935435 70658567 := bstep (se 1 (by rfl) ⟨52993925, by rfl⟩ : syracuseStep 70658567 = 105987851) B105987851
theorem B47105711 : Blo 1935435 47105711 := bstep (se 1 (by rfl) ⟨35329283, by rfl⟩ : syracuseStep 47105711 = 70658567) B70658567
theorem B31403807 : Blo 1935435 31403807 := bstep (se 1 (by rfl) ⟨23552855, by rfl⟩ : syracuseStep 31403807 = 47105711) B47105711
theorem B20935871 : Blo 1935435 20935871 := bstep (se 1 (by rfl) ⟨15701903, by rfl⟩ : syracuseStep 20935871 = 31403807) B31403807
theorem B13957247 : Blo 1935435 13957247 := bstep (se 1 (by rfl) ⟨10467935, by rfl⟩ : syracuseStep 13957247 = 20935871) B20935871
theorem B9304831 : Blo 1935435 9304831 := bstep (se 1 (by rfl) ⟨6978623, by rfl⟩ : syracuseStep 9304831 = 13957247) B13957247
theorem B12406441 : Blo 1935435 12406441 := bstep (se 2 (by rfl) ⟨4652415, by rfl⟩ : syracuseStep 12406441 = 9304831) B9304831
theorem B16541921 : Blo 1935435 16541921 := bstep (se 2 (by rfl) ⟨6203220, by rfl⟩ : syracuseStep 16541921 = 12406441) B12406441
theorem B11027947 : Blo 1935435 11027947 := bstep (se 1 (by rfl) ⟨8270960, by rfl⟩ : syracuseStep 11027947 = 16541921) B16541921
theorem B14703929 : Blo 1935435 14703929 := bstep (se 2 (by rfl) ⟨5513973, by rfl⟩ : syracuseStep 14703929 = 11027947) B11027947
theorem B9802619 : Blo 1935435 9802619 := bstep (se 1 (by rfl) ⟨7351964, by rfl⟩ : syracuseStep 9802619 = 14703929) B14703929
theorem B6535079 : Blo 1935435 6535079 := bstep (se 1 (by rfl) ⟨4901309, by rfl⟩ : syracuseStep 6535079 = 9802619) B9802619
theorem B4356719 : Blo 1935435 4356719 := bstep (se 1 (by rfl) ⟨3267539, by rfl⟩ : syracuseStep 4356719 = 6535079) B6535079
theorem B2904479 : Blo 1935435 2904479 := bstep (se 1 (by rfl) ⟨2178359, by rfl⟩ : syracuseStep 2904479 = 4356719) B4356719
theorem B1936319 : Blo 1935435 1936319 := bstep (se 1 (by rfl) ⟨1452239, by rfl⟩ : syracuseStep 1936319 = 2904479) B2904479
theorem B2904485 : Blo 1935435 2904485 := bbase (se 4 (by rfl) ⟨272295, by rfl⟩ : syracuseStep 2904485 = 544591) (by norm_num)
theorem B1936323 : Blo 1935435 1936323 := bstep (se 1 (by rfl) ⟨1452242, by rfl⟩ : syracuseStep 1936323 = 2904485) B2904485
theorem B2450665 : Blo 1935435 2450665 := bbase (se 2 (by rfl) ⟨918999, by rfl⟩ : syracuseStep 2450665 = 1837999) (by norm_num)
theorem B3267553 : Blo 1935435 3267553 := bstep (se 2 (by rfl) ⟨1225332, by rfl⟩ : syracuseStep 3267553 = 2450665) B2450665
theorem B4356737 : Blo 1935435 4356737 := bstep (se 2 (by rfl) ⟨1633776, by rfl⟩ : syracuseStep 4356737 = 3267553) B3267553
theorem B2904491 : Blo 1935435 2904491 := bstep (se 1 (by rfl) ⟨2178368, by rfl⟩ : syracuseStep 2904491 = 4356737) B4356737
theorem B1936327 : Blo 1935435 1936327 := bstep (se 1 (by rfl) ⟨1452245, by rfl⟩ : syracuseStep 1936327 = 2904491) B2904491
theorem B2178373 : Blo 1935435 2178373 := bbase (se 4 (by rfl) ⟨204222, by rfl⟩ : syracuseStep 2178373 = 408445) (by norm_num)
theorem B2904497 : Blo 1935435 2904497 := bstep (se 2 (by rfl) ⟨1089186, by rfl⟩ : syracuseStep 2904497 = 2178373) B2178373
theorem B1936331 : Blo 1935435 1936331 := bstep (se 1 (by rfl) ⟨1452248, by rfl⟩ : syracuseStep 1936331 = 2904497) B2904497
theorem B3676013 : Blo 1935435 3676013 := bbase (se 3 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 3676013 = 1378505) (by norm_num)
theorem B2450675 : Blo 1935435 2450675 := bstep (se 1 (by rfl) ⟨1838006, by rfl⟩ : syracuseStep 2450675 = 3676013) B3676013
theorem B6535133 : Blo 1935435 6535133 := bstep (se 3 (by rfl) ⟨1225337, by rfl⟩ : syracuseStep 6535133 = 2450675) B2450675
theorem B4356755 : Blo 1935435 4356755 := bstep (se 1 (by rfl) ⟨3267566, by rfl⟩ : syracuseStep 4356755 = 6535133) B6535133
theorem B2904503 : Blo 1935435 2904503 := bstep (se 1 (by rfl) ⟨2178377, by rfl⟩ : syracuseStep 2904503 = 4356755) B4356755
theorem B1936335 : Blo 1935435 1936335 := bstep (se 1 (by rfl) ⟨1452251, by rfl⟩ : syracuseStep 1936335 = 2904503) B2904503
theorem B2904509 : Blo 1935435 2904509 := bbase (se 3 (by rfl) ⟨544595, by rfl⟩ : syracuseStep 2904509 = 1089191) (by norm_num)
theorem B1936339 : Blo 1935435 1936339 := bstep (se 1 (by rfl) ⟨1452254, by rfl⟩ : syracuseStep 1936339 = 2904509) B2904509
theorem B4356773 : Blo 1935435 4356773 := bbase (se 4 (by rfl) ⟨408447, by rfl⟩ : syracuseStep 4356773 = 816895) (by norm_num)
theorem B2904515 : Blo 1935435 2904515 := bstep (se 1 (by rfl) ⟨2178386, by rfl⟩ : syracuseStep 2904515 = 4356773) B4356773
theorem B1936343 : Blo 1935435 1936343 := bstep (se 1 (by rfl) ⟨1452257, by rfl⟩ : syracuseStep 1936343 = 2904515) B2904515
theorem B4901381 : Blo 1935435 4901381 := bbase (se 4 (by rfl) ⟨459504, by rfl⟩ : syracuseStep 4901381 = 919009) (by norm_num)
theorem B3267587 : Blo 1935435 3267587 := bstep (se 1 (by rfl) ⟨2450690, by rfl⟩ : syracuseStep 3267587 = 4901381) B4901381
theorem B2178391 : Blo 1935435 2178391 := bstep (se 1 (by rfl) ⟨1633793, by rfl⟩ : syracuseStep 2178391 = 3267587) B3267587
theorem B2904521 : Blo 1935435 2904521 := bstep (se 2 (by rfl) ⟨1089195, by rfl⟩ : syracuseStep 2904521 = 2178391) B2178391
theorem B1936347 : Blo 1935435 1936347 := bstep (se 1 (by rfl) ⟨1452260, by rfl⟩ : syracuseStep 1936347 = 2904521) B2904521
theorem B4135549 : Blo 1935435 4135549 := bbase (se 3 (by rfl) ⟨775415, by rfl⟩ : syracuseStep 4135549 = 1550831) (by norm_num)
theorem B5514065 : Blo 1935435 5514065 := bstep (se 2 (by rfl) ⟨2067774, by rfl⟩ : syracuseStep 5514065 = 4135549) B4135549
theorem B3676043 : Blo 1935435 3676043 := bstep (se 1 (by rfl) ⟨2757032, by rfl⟩ : syracuseStep 3676043 = 5514065) B5514065
theorem B9802781 : Blo 1935435 9802781 := bstep (se 3 (by rfl) ⟨1838021, by rfl⟩ : syracuseStep 9802781 = 3676043) B3676043
theorem B6535187 : Blo 1935435 6535187 := bstep (se 1 (by rfl) ⟨4901390, by rfl⟩ : syracuseStep 6535187 = 9802781) B9802781
theorem B4356791 : Blo 1935435 4356791 := bstep (se 1 (by rfl) ⟨3267593, by rfl⟩ : syracuseStep 4356791 = 6535187) B6535187
theorem B2904527 : Blo 1935435 2904527 := bstep (se 1 (by rfl) ⟨2178395, by rfl⟩ : syracuseStep 2904527 = 4356791) B4356791
theorem B1936351 : Blo 1935435 1936351 := bstep (se 1 (by rfl) ⟨1452263, by rfl⟩ : syracuseStep 1936351 = 2904527) B2904527
theorem B2904533 : Blo 1935435 2904533 := bbase (se 7 (by rfl) ⟨34037, by rfl⟩ : syracuseStep 2904533 = 68075) (by norm_num)
theorem B1936355 : Blo 1935435 1936355 := bstep (se 1 (by rfl) ⟨1452266, by rfl⟩ : syracuseStep 1936355 = 2904533) B2904533
theorem B7352117 : Blo 1935435 7352117 := bbase (se 5 (by rfl) ⟨344630, by rfl⟩ : syracuseStep 7352117 = 689261) (by norm_num)
theorem B4901411 : Blo 1935435 4901411 := bstep (se 1 (by rfl) ⟨3676058, by rfl⟩ : syracuseStep 4901411 = 7352117) B7352117
theorem B3267607 : Blo 1935435 3267607 := bstep (se 1 (by rfl) ⟨2450705, by rfl⟩ : syracuseStep 3267607 = 4901411) B4901411
theorem B4356809 : Blo 1935435 4356809 := bstep (se 2 (by rfl) ⟨1633803, by rfl⟩ : syracuseStep 4356809 = 3267607) B3267607
theorem B2904539 : Blo 1935435 2904539 := bstep (se 1 (by rfl) ⟨2178404, by rfl⟩ : syracuseStep 2904539 = 4356809) B4356809
theorem B1936359 : Blo 1935435 1936359 := bstep (se 1 (by rfl) ⟨1452269, by rfl⟩ : syracuseStep 1936359 = 2904539) B2904539
theorem B2178409 : Blo 1935435 2178409 := bbase (se 2 (by rfl) ⟨816903, by rfl⟩ : syracuseStep 2178409 = 1633807) (by norm_num)
theorem B2904545 : Blo 1935435 2904545 := bstep (se 2 (by rfl) ⟨1089204, by rfl⟩ : syracuseStep 2904545 = 2178409) B2178409
theorem B1936363 : Blo 1935435 1936363 := bstep (se 1 (by rfl) ⟨1452272, by rfl⟩ : syracuseStep 1936363 = 2904545) B2904545
theorem B3726229 : Blo 1935435 3726229 := bbase (se 6 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 3726229 = 174667) (by norm_num)
theorem B4968305 : Blo 1935435 4968305 := bstep (se 2 (by rfl) ⟨1863114, by rfl⟩ : syracuseStep 4968305 = 3726229) B3726229
theorem B3312203 : Blo 1935435 3312203 := bstep (se 1 (by rfl) ⟨2484152, by rfl⟩ : syracuseStep 3312203 = 4968305) B4968305
theorem B35330165 : Blo 1935435 35330165 := bstep (se 5 (by rfl) ⟨1656101, by rfl⟩ : syracuseStep 35330165 = 3312203) B3312203
theorem B23553443 : Blo 1935435 23553443 := bstep (se 1 (by rfl) ⟨17665082, by rfl⟩ : syracuseStep 23553443 = 35330165) B35330165
theorem B15702295 : Blo 1935435 15702295 := bstep (se 1 (by rfl) ⟨11776721, by rfl⟩ : syracuseStep 15702295 = 23553443) B23553443
theorem B20936393 : Blo 1935435 20936393 := bstep (se 2 (by rfl) ⟨7851147, by rfl⟩ : syracuseStep 20936393 = 15702295) B15702295
theorem B13957595 : Blo 1935435 13957595 := bstep (se 1 (by rfl) ⟨10468196, by rfl⟩ : syracuseStep 13957595 = 20936393) B20936393
theorem B9305063 : Blo 1935435 9305063 := bstep (se 1 (by rfl) ⟨6978797, by rfl⟩ : syracuseStep 9305063 = 13957595) B13957595
theorem B6203375 : Blo 1935435 6203375 := bstep (se 1 (by rfl) ⟨4652531, by rfl⟩ : syracuseStep 6203375 = 9305063) B9305063
theorem B4135583 : Blo 1935435 4135583 := bstep (se 1 (by rfl) ⟨3101687, by rfl⟩ : syracuseStep 4135583 = 6203375) B6203375
theorem B11028221 : Blo 1935435 11028221 := bstep (se 3 (by rfl) ⟨2067791, by rfl⟩ : syracuseStep 11028221 = 4135583) B4135583
theorem B7352147 : Blo 1935435 7352147 := bstep (se 1 (by rfl) ⟨5514110, by rfl⟩ : syracuseStep 7352147 = 11028221) B11028221
theorem B4901431 : Blo 1935435 4901431 := bstep (se 1 (by rfl) ⟨3676073, by rfl⟩ : syracuseStep 4901431 = 7352147) B7352147
theorem B6535241 : Blo 1935435 6535241 := bstep (se 2 (by rfl) ⟨2450715, by rfl⟩ : syracuseStep 6535241 = 4901431) B4901431
theorem B4356827 : Blo 1935435 4356827 := bstep (se 1 (by rfl) ⟨3267620, by rfl⟩ : syracuseStep 4356827 = 6535241) B6535241
theorem B2904551 : Blo 1935435 2904551 := bstep (se 1 (by rfl) ⟨2178413, by rfl⟩ : syracuseStep 2904551 = 4356827) B4356827
theorem B1936367 : Blo 1935435 1936367 := bstep (se 1 (by rfl) ⟨1452275, by rfl⟩ : syracuseStep 1936367 = 2904551) B2904551
theorem B2904557 : Blo 1935435 2904557 := bbase (se 3 (by rfl) ⟨544604, by rfl⟩ : syracuseStep 2904557 = 1089209) (by norm_num)
theorem B1936371 : Blo 1935435 1936371 := bstep (se 1 (by rfl) ⟨1452278, by rfl⟩ : syracuseStep 1936371 = 2904557) B2904557
theorem B4356845 : Blo 1935435 4356845 := bbase (se 3 (by rfl) ⟨816908, by rfl⟩ : syracuseStep 4356845 = 1633817) (by norm_num)
theorem B2904563 : Blo 1935435 2904563 := bstep (se 1 (by rfl) ⟨2178422, by rfl⟩ : syracuseStep 2904563 = 4356845) B4356845
theorem B1936375 : Blo 1935435 1936375 := bstep (se 1 (by rfl) ⟨1452281, by rfl⟩ : syracuseStep 1936375 = 2904563) B2904563
theorem B2067805 : Blo 1935435 2067805 := bbase (se 3 (by rfl) ⟨387713, by rfl⟩ : syracuseStep 2067805 = 775427) (by norm_num)
theorem B2757073 : Blo 1935435 2757073 := bstep (se 2 (by rfl) ⟨1033902, by rfl⟩ : syracuseStep 2757073 = 2067805) B2067805
theorem B3676097 : Blo 1935435 3676097 := bstep (se 2 (by rfl) ⟨1378536, by rfl⟩ : syracuseStep 3676097 = 2757073) B2757073
theorem B2450731 : Blo 1935435 2450731 := bstep (se 1 (by rfl) ⟨1838048, by rfl⟩ : syracuseStep 2450731 = 3676097) B3676097
theorem B3267641 : Blo 1935435 3267641 := bstep (se 2 (by rfl) ⟨1225365, by rfl⟩ : syracuseStep 3267641 = 2450731) B2450731
theorem B2178427 : Blo 1935435 2178427 := bstep (se 1 (by rfl) ⟨1633820, by rfl⟩ : syracuseStep 2178427 = 3267641) B3267641
theorem B2904569 : Blo 1935435 2904569 := bstep (se 2 (by rfl) ⟨1089213, by rfl⟩ : syracuseStep 2904569 = 2178427) B2178427
theorem B1936379 : Blo 1935435 1936379 := bstep (se 1 (by rfl) ⟨1452284, by rfl⟩ : syracuseStep 1936379 = 2904569) B2904569
theorem B15702421 : Blo 1935435 15702421 := bbase (se 6 (by rfl) ⟨368025, by rfl⟩ : syracuseStep 15702421 = 736051) (by norm_num)
theorem B20936561 : Blo 1935435 20936561 := bstep (se 2 (by rfl) ⟨7851210, by rfl⟩ : syracuseStep 20936561 = 15702421) B15702421
theorem B55830829 : Blo 1935435 55830829 := bstep (se 3 (by rfl) ⟨10468280, by rfl⟩ : syracuseStep 55830829 = 20936561) B20936561
theorem B74441105 : Blo 1935435 74441105 := bstep (se 2 (by rfl) ⟨27915414, by rfl⟩ : syracuseStep 74441105 = 55830829) B55830829
theorem B49627403 : Blo 1935435 49627403 := bstep (se 1 (by rfl) ⟨37220552, by rfl⟩ : syracuseStep 49627403 = 74441105) B74441105
theorem B33084935 : Blo 1935435 33084935 := bstep (se 1 (by rfl) ⟨24813701, by rfl⟩ : syracuseStep 33084935 = 49627403) B49627403
theorem B22056623 : Blo 1935435 22056623 := bstep (se 1 (by rfl) ⟨16542467, by rfl⟩ : syracuseStep 22056623 = 33084935) B33084935
theorem B14704415 : Blo 1935435 14704415 := bstep (se 1 (by rfl) ⟨11028311, by rfl⟩ : syracuseStep 14704415 = 22056623) B22056623
theorem B9802943 : Blo 1935435 9802943 := bstep (se 1 (by rfl) ⟨7352207, by rfl⟩ : syracuseStep 9802943 = 14704415) B14704415
theorem B6535295 : Blo 1935435 6535295 := bstep (se 1 (by rfl) ⟨4901471, by rfl⟩ : syracuseStep 6535295 = 9802943) B9802943
theorem B4356863 : Blo 1935435 4356863 := bstep (se 1 (by rfl) ⟨3267647, by rfl⟩ : syracuseStep 4356863 = 6535295) B6535295
theorem B2904575 : Blo 1935435 2904575 := bstep (se 1 (by rfl) ⟨2178431, by rfl⟩ : syracuseStep 2904575 = 4356863) B4356863
theorem B1936383 : Blo 1935435 1936383 := bstep (se 1 (by rfl) ⟨1452287, by rfl⟩ : syracuseStep 1936383 = 2904575) B2904575
theorem B2904581 : Blo 1935435 2904581 := bbase (se 4 (by rfl) ⟨272304, by rfl⟩ : syracuseStep 2904581 = 544609) (by norm_num)
theorem B1936387 : Blo 1935435 1936387 := bstep (se 1 (by rfl) ⟨1452290, by rfl⟩ : syracuseStep 1936387 = 2904581) B2904581
theorem B3267661 : Blo 1935435 3267661 := bbase (se 3 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 3267661 = 1225373) (by norm_num)
theorem B4356881 : Blo 1935435 4356881 := bstep (se 2 (by rfl) ⟨1633830, by rfl⟩ : syracuseStep 4356881 = 3267661) B3267661
theorem B2904587 : Blo 1935435 2904587 := bstep (se 1 (by rfl) ⟨2178440, by rfl⟩ : syracuseStep 2904587 = 4356881) B4356881
theorem B1936391 : Blo 1935435 1936391 := bstep (se 1 (by rfl) ⟨1452293, by rfl⟩ : syracuseStep 1936391 = 2904587) B2904587
theorem B2178445 : Blo 1935435 2178445 := bbase (se 3 (by rfl) ⟨408458, by rfl⟩ : syracuseStep 2178445 = 816917) (by norm_num)
theorem B2904593 : Blo 1935435 2904593 := bstep (se 2 (by rfl) ⟨1089222, by rfl⟩ : syracuseStep 2904593 = 2178445) B2178445
theorem B1936395 : Blo 1935435 1936395 := bstep (se 1 (by rfl) ⟨1452296, by rfl⟩ : syracuseStep 1936395 = 2904593) B2904593
theorem B6535349 : Blo 1935435 6535349 := bbase (se 5 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 6535349 = 612689) (by norm_num)
theorem B4356899 : Blo 1935435 4356899 := bstep (se 1 (by rfl) ⟨3267674, by rfl⟩ : syracuseStep 4356899 = 6535349) B6535349
theorem B2904599 : Blo 1935435 2904599 := bstep (se 1 (by rfl) ⟨2178449, by rfl⟩ : syracuseStep 2904599 = 4356899) B4356899
theorem B1936399 : Blo 1935435 1936399 := bstep (se 1 (by rfl) ⟨1452299, by rfl⟩ : syracuseStep 1936399 = 2904599) B2904599
theorem B2904605 : Blo 1935435 2904605 := bbase (se 3 (by rfl) ⟨544613, by rfl⟩ : syracuseStep 2904605 = 1089227) (by norm_num)
theorem B1936403 : Blo 1935435 1936403 := bstep (se 1 (by rfl) ⟨1452302, by rfl⟩ : syracuseStep 1936403 = 2904605) B2904605
theorem B4356917 : Blo 1935435 4356917 := bbase (se 5 (by rfl) ⟨204230, by rfl⟩ : syracuseStep 4356917 = 408461) (by norm_num)
theorem B2904611 : Blo 1935435 2904611 := bstep (se 1 (by rfl) ⟨2178458, by rfl⟩ : syracuseStep 2904611 = 4356917) B4356917
theorem B1936407 : Blo 1935435 1936407 := bstep (se 1 (by rfl) ⟨1452305, by rfl⟩ : syracuseStep 1936407 = 2904611) B2904611
theorem B2124649 : Blo 1935435 2124649 := bbase (se 2 (by rfl) ⟨796743, by rfl⟩ : syracuseStep 2124649 = 1593487) (by norm_num)
theorem B11331461 : Blo 1935435 11331461 := bstep (se 4 (by rfl) ⟨1062324, by rfl⟩ : syracuseStep 11331461 = 2124649) B2124649
theorem B7554307 : Blo 1935435 7554307 := bstep (se 1 (by rfl) ⟨5665730, by rfl⟩ : syracuseStep 7554307 = 11331461) B11331461
theorem B10072409 : Blo 1935435 10072409 := bstep (se 2 (by rfl) ⟨3777153, by rfl⟩ : syracuseStep 10072409 = 7554307) B7554307
theorem B26859757 : Blo 1935435 26859757 := bstep (se 3 (by rfl) ⟨5036204, by rfl⟩ : syracuseStep 26859757 = 10072409) B10072409
theorem B35813009 : Blo 1935435 35813009 := bstep (se 2 (by rfl) ⟨13429878, by rfl⟩ : syracuseStep 35813009 = 26859757) B26859757
theorem B23875339 : Blo 1935435 23875339 := bstep (se 1 (by rfl) ⟨17906504, by rfl⟩ : syracuseStep 23875339 = 35813009) B35813009
theorem B31833785 : Blo 1935435 31833785 := bstep (se 2 (by rfl) ⟨11937669, by rfl⟩ : syracuseStep 31833785 = 23875339) B23875339
theorem B21222523 : Blo 1935435 21222523 := bstep (se 1 (by rfl) ⟨15916892, by rfl⟩ : syracuseStep 21222523 = 31833785) B31833785
theorem B28296697 : Blo 1935435 28296697 := bstep (se 2 (by rfl) ⟨10611261, by rfl⟩ : syracuseStep 28296697 = 21222523) B21222523
theorem B37728929 : Blo 1935435 37728929 := bstep (se 2 (by rfl) ⟨14148348, by rfl⟩ : syracuseStep 37728929 = 28296697) B28296697
theorem B25152619 : Blo 1935435 25152619 := bstep (se 1 (by rfl) ⟨18864464, by rfl⟩ : syracuseStep 25152619 = 37728929) B37728929
theorem B33536825 : Blo 1935435 33536825 := bstep (se 2 (by rfl) ⟨12576309, by rfl⟩ : syracuseStep 33536825 = 25152619) B25152619
theorem B22357883 : Blo 1935435 22357883 := bstep (se 1 (by rfl) ⟨16768412, by rfl⟩ : syracuseStep 22357883 = 33536825) B33536825
theorem B14905255 : Blo 1935435 14905255 := bstep (se 1 (by rfl) ⟨11178941, by rfl⟩ : syracuseStep 14905255 = 22357883) B22357883
theorem B19873673 : Blo 1935435 19873673 := bstep (se 2 (by rfl) ⟨7452627, by rfl⟩ : syracuseStep 19873673 = 14905255) B14905255
theorem B13249115 : Blo 1935435 13249115 := bstep (se 1 (by rfl) ⟨9936836, by rfl⟩ : syracuseStep 13249115 = 19873673) B19873673
theorem B8832743 : Blo 1935435 8832743 := bstep (se 1 (by rfl) ⟨6624557, by rfl⟩ : syracuseStep 8832743 = 13249115) B13249115
theorem B5888495 : Blo 1935435 5888495 := bstep (se 1 (by rfl) ⟨4416371, by rfl⟩ : syracuseStep 5888495 = 8832743) B8832743
theorem B15702653 : Blo 1935435 15702653 := bstep (se 3 (by rfl) ⟨2944247, by rfl⟩ : syracuseStep 15702653 = 5888495) B5888495
theorem B10468435 : Blo 1935435 10468435 := bstep (se 1 (by rfl) ⟨7851326, by rfl⟩ : syracuseStep 10468435 = 15702653) B15702653
theorem B13957913 : Blo 1935435 13957913 := bstep (se 2 (by rfl) ⟨5234217, by rfl⟩ : syracuseStep 13957913 = 10468435) B10468435
theorem B9305275 : Blo 1935435 9305275 := bstep (se 1 (by rfl) ⟨6978956, by rfl⟩ : syracuseStep 9305275 = 13957913) B13957913
theorem B12407033 : Blo 1935435 12407033 := bstep (se 2 (by rfl) ⟨4652637, by rfl⟩ : syracuseStep 12407033 = 9305275) B9305275
theorem B8271355 : Blo 1935435 8271355 := bstep (se 1 (by rfl) ⟨6203516, by rfl⟩ : syracuseStep 8271355 = 12407033) B12407033
theorem B11028473 : Blo 1935435 11028473 := bstep (se 2 (by rfl) ⟨4135677, by rfl⟩ : syracuseStep 11028473 = 8271355) B8271355
theorem B7352315 : Blo 1935435 7352315 := bstep (se 1 (by rfl) ⟨5514236, by rfl⟩ : syracuseStep 7352315 = 11028473) B11028473
theorem B4901543 : Blo 1935435 4901543 := bstep (se 1 (by rfl) ⟨3676157, by rfl⟩ : syracuseStep 4901543 = 7352315) B7352315
theorem B3267695 : Blo 1935435 3267695 := bstep (se 1 (by rfl) ⟨2450771, by rfl⟩ : syracuseStep 3267695 = 4901543) B4901543
theorem B2178463 : Blo 1935435 2178463 := bstep (se 1 (by rfl) ⟨1633847, by rfl⟩ : syracuseStep 2178463 = 3267695) B3267695
theorem B2904617 : Blo 1935435 2904617 := bstep (se 2 (by rfl) ⟨1089231, by rfl⟩ : syracuseStep 2904617 = 2178463) B2178463
theorem B1936411 : Blo 1935435 1936411 := bstep (se 1 (by rfl) ⟨1452308, by rfl⟩ : syracuseStep 1936411 = 2904617) B2904617
theorem B3489485 : Blo 1935435 3489485 := bbase (se 3 (by rfl) ⟨654278, by rfl⟩ : syracuseStep 3489485 = 1308557) (by norm_num)
theorem B9305293 : Blo 1935435 9305293 := bstep (se 3 (by rfl) ⟨1744742, by rfl⟩ : syracuseStep 9305293 = 3489485) B3489485
theorem B12407057 : Blo 1935435 12407057 := bstep (se 2 (by rfl) ⟨4652646, by rfl⟩ : syracuseStep 12407057 = 9305293) B9305293
theorem B8271371 : Blo 1935435 8271371 := bstep (se 1 (by rfl) ⟨6203528, by rfl⟩ : syracuseStep 8271371 = 12407057) B12407057
theorem B5514247 : Blo 1935435 5514247 := bstep (se 1 (by rfl) ⟨4135685, by rfl⟩ : syracuseStep 5514247 = 8271371) B8271371
theorem B7352329 : Blo 1935435 7352329 := bstep (se 2 (by rfl) ⟨2757123, by rfl⟩ : syracuseStep 7352329 = 5514247) B5514247
theorem B9803105 : Blo 1935435 9803105 := bstep (se 2 (by rfl) ⟨3676164, by rfl⟩ : syracuseStep 9803105 = 7352329) B7352329
theorem B6535403 : Blo 1935435 6535403 := bstep (se 1 (by rfl) ⟨4901552, by rfl⟩ : syracuseStep 6535403 = 9803105) B9803105
theorem B4356935 : Blo 1935435 4356935 := bstep (se 1 (by rfl) ⟨3267701, by rfl⟩ : syracuseStep 4356935 = 6535403) B6535403
theorem B2904623 : Blo 1935435 2904623 := bstep (se 1 (by rfl) ⟨2178467, by rfl⟩ : syracuseStep 2904623 = 4356935) B4356935
theorem B1936415 : Blo 1935435 1936415 := bstep (se 1 (by rfl) ⟨1452311, by rfl⟩ : syracuseStep 1936415 = 2904623) B2904623
theorem B2904629 : Blo 1935435 2904629 := bbase (se 5 (by rfl) ⟨136154, by rfl⟩ : syracuseStep 2904629 = 272309) (by norm_num)
theorem B1936419 : Blo 1935435 1936419 := bstep (se 1 (by rfl) ⟨1452314, by rfl⟩ : syracuseStep 1936419 = 2904629) B2904629
theorem B4901573 : Blo 1935435 4901573 := bbase (se 4 (by rfl) ⟨459522, by rfl⟩ : syracuseStep 4901573 = 919045) (by norm_num)
theorem B3267715 : Blo 1935435 3267715 := bstep (se 1 (by rfl) ⟨2450786, by rfl⟩ : syracuseStep 3267715 = 4901573) B4901573
theorem B4356953 : Blo 1935435 4356953 := bstep (se 2 (by rfl) ⟨1633857, by rfl⟩ : syracuseStep 4356953 = 3267715) B3267715
theorem B2904635 : Blo 1935435 2904635 := bstep (se 1 (by rfl) ⟨2178476, by rfl⟩ : syracuseStep 2904635 = 4356953) B4356953
theorem B1936423 : Blo 1935435 1936423 := bstep (se 1 (by rfl) ⟨1452317, by rfl⟩ : syracuseStep 1936423 = 2904635) B2904635
theorem B2178481 : Blo 1935435 2178481 := bbase (se 2 (by rfl) ⟨816930, by rfl⟩ : syracuseStep 2178481 = 1633861) (by norm_num)
theorem B2904641 : Blo 1935435 2904641 := bstep (se 2 (by rfl) ⟨1089240, by rfl⟩ : syracuseStep 2904641 = 2178481) B2178481
theorem B1936427 : Blo 1935435 1936427 := bstep (se 1 (by rfl) ⟨1452320, by rfl⟩ : syracuseStep 1936427 = 2904641) B2904641
theorem B5514293 : Blo 1935435 5514293 := bbase (se 5 (by rfl) ⟨258482, by rfl⟩ : syracuseStep 5514293 = 516965) (by norm_num)
theorem B3676195 : Blo 1935435 3676195 := bstep (se 1 (by rfl) ⟨2757146, by rfl⟩ : syracuseStep 3676195 = 5514293) B5514293
theorem B4901593 : Blo 1935435 4901593 := bstep (se 2 (by rfl) ⟨1838097, by rfl⟩ : syracuseStep 4901593 = 3676195) B3676195
theorem B6535457 : Blo 1935435 6535457 := bstep (se 2 (by rfl) ⟨2450796, by rfl⟩ : syracuseStep 6535457 = 4901593) B4901593
theorem B4356971 : Blo 1935435 4356971 := bstep (se 1 (by rfl) ⟨3267728, by rfl⟩ : syracuseStep 4356971 = 6535457) B6535457
theorem B2904647 : Blo 1935435 2904647 := bstep (se 1 (by rfl) ⟨2178485, by rfl⟩ : syracuseStep 2904647 = 4356971) B4356971
theorem B1936431 : Blo 1935435 1936431 := bstep (se 1 (by rfl) ⟨1452323, by rfl⟩ : syracuseStep 1936431 = 2904647) B2904647
theorem B2904653 : Blo 1935435 2904653 := bbase (se 3 (by rfl) ⟨544622, by rfl⟩ : syracuseStep 2904653 = 1089245) (by norm_num)
theorem B1936435 : Blo 1935435 1936435 := bstep (se 1 (by rfl) ⟨1452326, by rfl⟩ : syracuseStep 1936435 = 2904653) B2904653
theorem B4356989 : Blo 1935435 4356989 := bbase (se 3 (by rfl) ⟨816935, by rfl⟩ : syracuseStep 4356989 = 1633871) (by norm_num)
theorem B2904659 : Blo 1935435 2904659 := bstep (se 1 (by rfl) ⟨2178494, by rfl⟩ : syracuseStep 2904659 = 4356989) B4356989
theorem B1936439 : Blo 1935435 1936439 := bstep (se 1 (by rfl) ⟨1452329, by rfl⟩ : syracuseStep 1936439 = 2904659) B2904659
theorem B3267749 : Blo 1935435 3267749 := bbase (se 4 (by rfl) ⟨306351, by rfl⟩ : syracuseStep 3267749 = 612703) (by norm_num)
theorem B2178499 : Blo 1935435 2178499 := bstep (se 1 (by rfl) ⟨1633874, by rfl⟩ : syracuseStep 2178499 = 3267749) B3267749
theorem B2904665 : Blo 1935435 2904665 := bstep (se 2 (by rfl) ⟨1089249, by rfl⟩ : syracuseStep 2904665 = 2178499) B2178499
theorem B1936443 : Blo 1935435 1936443 := bstep (se 1 (by rfl) ⟨1452332, by rfl⟩ : syracuseStep 1936443 = 2904665) B2904665
theorem B2067877 : Blo 1935435 2067877 := bbase (se 4 (by rfl) ⟨193863, by rfl⟩ : syracuseStep 2067877 = 387727) (by norm_num)
theorem B2757169 : Blo 1935435 2757169 := bstep (se 2 (by rfl) ⟨1033938, by rfl⟩ : syracuseStep 2757169 = 2067877) B2067877
theorem B14704901 : Blo 1935435 14704901 := bstep (se 4 (by rfl) ⟨1378584, by rfl⟩ : syracuseStep 14704901 = 2757169) B2757169
theorem B9803267 : Blo 1935435 9803267 := bstep (se 1 (by rfl) ⟨7352450, by rfl⟩ : syracuseStep 9803267 = 14704901) B14704901
theorem B6535511 : Blo 1935435 6535511 := bstep (se 1 (by rfl) ⟨4901633, by rfl⟩ : syracuseStep 6535511 = 9803267) B9803267
theorem B4357007 : Blo 1935435 4357007 := bstep (se 1 (by rfl) ⟨3267755, by rfl⟩ : syracuseStep 4357007 = 6535511) B6535511
theorem B2904671 : Blo 1935435 2904671 := bstep (se 1 (by rfl) ⟨2178503, by rfl⟩ : syracuseStep 2904671 = 4357007) B4357007
theorem B1936447 : Blo 1935435 1936447 := bstep (se 1 (by rfl) ⟨1452335, by rfl⟩ : syracuseStep 1936447 = 2904671) B2904671
theorem B2904677 : Blo 1935435 2904677 := bbase (se 4 (by rfl) ⟨272313, by rfl⟩ : syracuseStep 2904677 = 544627) (by norm_num)
theorem B1936451 : Blo 1935435 1936451 := bstep (se 1 (by rfl) ⟨1452338, by rfl⟩ : syracuseStep 1936451 = 2904677) B2904677
theorem B2757181 : Blo 1935435 2757181 := bbase (se 3 (by rfl) ⟨516971, by rfl⟩ : syracuseStep 2757181 = 1033943) (by norm_num)
theorem B3676241 : Blo 1935435 3676241 := bstep (se 2 (by rfl) ⟨1378590, by rfl⟩ : syracuseStep 3676241 = 2757181) B2757181
theorem B2450827 : Blo 1935435 2450827 := bstep (se 1 (by rfl) ⟨1838120, by rfl⟩ : syracuseStep 2450827 = 3676241) B3676241
theorem B3267769 : Blo 1935435 3267769 := bstep (se 2 (by rfl) ⟨1225413, by rfl⟩ : syracuseStep 3267769 = 2450827) B2450827
theorem B4357025 : Blo 1935435 4357025 := bstep (se 2 (by rfl) ⟨1633884, by rfl⟩ : syracuseStep 4357025 = 3267769) B3267769
theorem B2904683 : Blo 1935435 2904683 := bstep (se 1 (by rfl) ⟨2178512, by rfl⟩ : syracuseStep 2904683 = 4357025) B4357025
theorem B1936455 : Blo 1935435 1936455 := bstep (se 1 (by rfl) ⟨1452341, by rfl⟩ : syracuseStep 1936455 = 2904683) B2904683
theorem B2178517 : Blo 1935435 2178517 := bbase (se 7 (by rfl) ⟨25529, by rfl⟩ : syracuseStep 2178517 = 51059) (by norm_num)
theorem B2904689 : Blo 1935435 2904689 := bstep (se 2 (by rfl) ⟨1089258, by rfl⟩ : syracuseStep 2904689 = 2178517) B2178517
theorem B1936459 : Blo 1935435 1936459 := bstep (se 1 (by rfl) ⟨1452344, by rfl⟩ : syracuseStep 1936459 = 2904689) B2904689
theorem B2450837 : Blo 1935435 2450837 := bbase (se 6 (by rfl) ⟨57441, by rfl⟩ : syracuseStep 2450837 = 114883) (by norm_num)
theorem B6535565 : Blo 1935435 6535565 := bstep (se 3 (by rfl) ⟨1225418, by rfl⟩ : syracuseStep 6535565 = 2450837) B2450837
theorem B4357043 : Blo 1935435 4357043 := bstep (se 1 (by rfl) ⟨3267782, by rfl⟩ : syracuseStep 4357043 = 6535565) B6535565
theorem B2904695 : Blo 1935435 2904695 := bstep (se 1 (by rfl) ⟨2178521, by rfl⟩ : syracuseStep 2904695 = 4357043) B4357043
theorem B1936463 : Blo 1935435 1936463 := bstep (se 1 (by rfl) ⟨1452347, by rfl⟩ : syracuseStep 1936463 = 2904695) B2904695
theorem B2904701 : Blo 1935435 2904701 := bbase (se 3 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 2904701 = 1089263) (by norm_num)
theorem B1936467 : Blo 1935435 1936467 := bstep (se 1 (by rfl) ⟨1452350, by rfl⟩ : syracuseStep 1936467 = 2904701) B2904701
theorem B4357061 : Blo 1935435 4357061 := bbase (se 4 (by rfl) ⟨408474, by rfl⟩ : syracuseStep 4357061 = 816949) (by norm_num)
theorem B2904707 : Blo 1935435 2904707 := bstep (se 1 (by rfl) ⟨2178530, by rfl⟩ : syracuseStep 2904707 = 4357061) B4357061
theorem B1936471 : Blo 1935435 1936471 := bstep (se 1 (by rfl) ⟨1452353, by rfl⟩ : syracuseStep 1936471 = 2904707) B2904707
theorem B3101861 : Blo 1935435 3101861 := bbase (se 4 (by rfl) ⟨290799, by rfl⟩ : syracuseStep 3101861 = 581599) (by norm_num)
theorem B8271629 : Blo 1935435 8271629 := bstep (se 3 (by rfl) ⟨1550930, by rfl⟩ : syracuseStep 8271629 = 3101861) B3101861
theorem B5514419 : Blo 1935435 5514419 := bstep (se 1 (by rfl) ⟨4135814, by rfl⟩ : syracuseStep 5514419 = 8271629) B8271629
theorem B3676279 : Blo 1935435 3676279 := bstep (se 1 (by rfl) ⟨2757209, by rfl⟩ : syracuseStep 3676279 = 5514419) B5514419
theorem B4901705 : Blo 1935435 4901705 := bstep (se 2 (by rfl) ⟨1838139, by rfl⟩ : syracuseStep 4901705 = 3676279) B3676279
theorem B3267803 : Blo 1935435 3267803 := bstep (se 1 (by rfl) ⟨2450852, by rfl⟩ : syracuseStep 3267803 = 4901705) B4901705
theorem B2178535 : Blo 1935435 2178535 := bstep (se 1 (by rfl) ⟨1633901, by rfl⟩ : syracuseStep 2178535 = 3267803) B3267803
theorem B2904713 : Blo 1935435 2904713 := bstep (se 2 (by rfl) ⟨1089267, by rfl⟩ : syracuseStep 2904713 = 2178535) B2178535
theorem B1936475 : Blo 1935435 1936475 := bstep (se 1 (by rfl) ⟨1452356, by rfl⟩ : syracuseStep 1936475 = 2904713) B2904713
theorem B9803429 : Blo 1935435 9803429 := bbase (se 4 (by rfl) ⟨919071, by rfl⟩ : syracuseStep 9803429 = 1838143) (by norm_num)
theorem B6535619 : Blo 1935435 6535619 := bstep (se 1 (by rfl) ⟨4901714, by rfl⟩ : syracuseStep 6535619 = 9803429) B9803429
theorem B4357079 : Blo 1935435 4357079 := bstep (se 1 (by rfl) ⟨3267809, by rfl⟩ : syracuseStep 4357079 = 6535619) B6535619
theorem B2904719 : Blo 1935435 2904719 := bstep (se 1 (by rfl) ⟨2178539, by rfl⟩ : syracuseStep 2904719 = 4357079) B4357079
theorem B1936479 : Blo 1935435 1936479 := bstep (se 1 (by rfl) ⟨1452359, by rfl⟩ : syracuseStep 1936479 = 2904719) B2904719
theorem B2904725 : Blo 1935435 2904725 := bbase (se 6 (by rfl) ⟨68079, by rfl⟩ : syracuseStep 2904725 = 136159) (by norm_num)
theorem B1936483 : Blo 1935435 1936483 := bstep (se 1 (by rfl) ⟨1452362, by rfl⟩ : syracuseStep 1936483 = 2904725) B2904725
theorem B23554901 : Blo 1935435 23554901 := bbase (se 9 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 23554901 = 138017) (by norm_num)
theorem B62813069 : Blo 1935435 62813069 := bstep (se 3 (by rfl) ⟨11777450, by rfl⟩ : syracuseStep 62813069 = 23554901) B23554901
theorem B41875379 : Blo 1935435 41875379 := bstep (se 1 (by rfl) ⟨31406534, by rfl⟩ : syracuseStep 41875379 = 62813069) B62813069
theorem B27916919 : Blo 1935435 27916919 := bstep (se 1 (by rfl) ⟨20937689, by rfl⟩ : syracuseStep 27916919 = 41875379) B41875379
theorem B18611279 : Blo 1935435 18611279 := bstep (se 1 (by rfl) ⟨13958459, by rfl⟩ : syracuseStep 18611279 = 27916919) B27916919
theorem B12407519 : Blo 1935435 12407519 := bstep (se 1 (by rfl) ⟨9305639, by rfl⟩ : syracuseStep 12407519 = 18611279) B18611279
theorem B8271679 : Blo 1935435 8271679 := bstep (se 1 (by rfl) ⟨6203759, by rfl⟩ : syracuseStep 8271679 = 12407519) B12407519
theorem B11028905 : Blo 1935435 11028905 := bstep (se 2 (by rfl) ⟨4135839, by rfl⟩ : syracuseStep 11028905 = 8271679) B8271679
theorem B7352603 : Blo 1935435 7352603 := bstep (se 1 (by rfl) ⟨5514452, by rfl⟩ : syracuseStep 7352603 = 11028905) B11028905
theorem B4901735 : Blo 1935435 4901735 := bstep (se 1 (by rfl) ⟨3676301, by rfl⟩ : syracuseStep 4901735 = 7352603) B7352603
theorem B3267823 : Blo 1935435 3267823 := bstep (se 1 (by rfl) ⟨2450867, by rfl⟩ : syracuseStep 3267823 = 4901735) B4901735
theorem B4357097 : Blo 1935435 4357097 := bstep (se 2 (by rfl) ⟨1633911, by rfl⟩ : syracuseStep 4357097 = 3267823) B3267823
theorem B2904731 : Blo 1935435 2904731 := bstep (se 1 (by rfl) ⟨2178548, by rfl⟩ : syracuseStep 2904731 = 4357097) B4357097
theorem B1936487 : Blo 1935435 1936487 := bstep (se 1 (by rfl) ⟨1452365, by rfl⟩ : syracuseStep 1936487 = 2904731) B2904731
theorem B2178553 : Blo 1935435 2178553 := bbase (se 2 (by rfl) ⟨816957, by rfl⟩ : syracuseStep 2178553 = 1633915) (by norm_num)
theorem B2904737 : Blo 1935435 2904737 := bstep (se 2 (by rfl) ⟨1089276, by rfl⟩ : syracuseStep 2904737 = 2178553) B2178553
theorem B1936491 : Blo 1935435 1936491 := bstep (se 1 (by rfl) ⟨1452368, by rfl⟩ : syracuseStep 1936491 = 2904737) B2904737
theorem B2484317 : Blo 1935435 2484317 := bbase (se 3 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 2484317 = 931619) (by norm_num)
theorem B6624845 : Blo 1935435 6624845 := bstep (se 3 (by rfl) ⟨1242158, by rfl⟩ : syracuseStep 6624845 = 2484317) B2484317
theorem B4416563 : Blo 1935435 4416563 := bstep (se 1 (by rfl) ⟨3312422, by rfl⟩ : syracuseStep 4416563 = 6624845) B6624845
theorem B11777501 : Blo 1935435 11777501 := bstep (se 3 (by rfl) ⟨2208281, by rfl⟩ : syracuseStep 11777501 = 4416563) B4416563
theorem B7851667 : Blo 1935435 7851667 := bstep (se 1 (by rfl) ⟨5888750, by rfl⟩ : syracuseStep 7851667 = 11777501) B11777501
theorem B10468889 : Blo 1935435 10468889 := bstep (se 2 (by rfl) ⟨3925833, by rfl⟩ : syracuseStep 10468889 = 7851667) B7851667
theorem B6979259 : Blo 1935435 6979259 := bstep (se 1 (by rfl) ⟨5234444, by rfl⟩ : syracuseStep 6979259 = 10468889) B10468889
theorem B4652839 : Blo 1935435 4652839 := bstep (se 1 (by rfl) ⟨3489629, by rfl⟩ : syracuseStep 4652839 = 6979259) B6979259
theorem B6203785 : Blo 1935435 6203785 := bstep (se 2 (by rfl) ⟨2326419, by rfl⟩ : syracuseStep 6203785 = 4652839) B4652839
theorem B8271713 : Blo 1935435 8271713 := bstep (se 2 (by rfl) ⟨3101892, by rfl⟩ : syracuseStep 8271713 = 6203785) B6203785
theorem B5514475 : Blo 1935435 5514475 := bstep (se 1 (by rfl) ⟨4135856, by rfl⟩ : syracuseStep 5514475 = 8271713) B8271713
theorem B7352633 : Blo 1935435 7352633 := bstep (se 2 (by rfl) ⟨2757237, by rfl⟩ : syracuseStep 7352633 = 5514475) B5514475
theorem B4901755 : Blo 1935435 4901755 := bstep (se 1 (by rfl) ⟨3676316, by rfl⟩ : syracuseStep 4901755 = 7352633) B7352633
theorem B6535673 : Blo 1935435 6535673 := bstep (se 2 (by rfl) ⟨2450877, by rfl⟩ : syracuseStep 6535673 = 4901755) B4901755
theorem B4357115 : Blo 1935435 4357115 := bstep (se 1 (by rfl) ⟨3267836, by rfl⟩ : syracuseStep 4357115 = 6535673) B6535673
theorem B2904743 : Blo 1935435 2904743 := bstep (se 1 (by rfl) ⟨2178557, by rfl⟩ : syracuseStep 2904743 = 4357115) B4357115
theorem B1936495 : Blo 1935435 1936495 := bstep (se 1 (by rfl) ⟨1452371, by rfl⟩ : syracuseStep 1936495 = 2904743) B2904743
theorem B2904749 : Blo 1935435 2904749 := bbase (se 3 (by rfl) ⟨544640, by rfl⟩ : syracuseStep 2904749 = 1089281) (by norm_num)
theorem B1936499 : Blo 1935435 1936499 := bstep (se 1 (by rfl) ⟨1452374, by rfl⟩ : syracuseStep 1936499 = 2904749) B2904749
theorem B4357133 : Blo 1935435 4357133 := bbase (se 3 (by rfl) ⟨816962, by rfl⟩ : syracuseStep 4357133 = 1633925) (by norm_num)
theorem B2904755 : Blo 1935435 2904755 := bstep (se 1 (by rfl) ⟨2178566, by rfl⟩ : syracuseStep 2904755 = 4357133) B4357133
theorem B1936503 : Blo 1935435 1936503 := bstep (se 1 (by rfl) ⟨1452377, by rfl⟩ : syracuseStep 1936503 = 2904755) B2904755
theorem B2450893 : Blo 1935435 2450893 := bbase (se 3 (by rfl) ⟨459542, by rfl⟩ : syracuseStep 2450893 = 919085) (by norm_num)
theorem B3267857 : Blo 1935435 3267857 := bstep (se 2 (by rfl) ⟨1225446, by rfl⟩ : syracuseStep 3267857 = 2450893) B2450893
theorem B2178571 : Blo 1935435 2178571 := bstep (se 1 (by rfl) ⟨1633928, by rfl⟩ : syracuseStep 2178571 = 3267857) B3267857
theorem B2904761 : Blo 1935435 2904761 := bstep (se 2 (by rfl) ⟨1089285, by rfl⟩ : syracuseStep 2904761 = 2178571) B2178571
theorem B1936507 : Blo 1935435 1936507 := bstep (se 1 (by rfl) ⟨1452380, by rfl⟩ : syracuseStep 1936507 = 2904761) B2904761
theorem B9937349 : Blo 1935435 9937349 := bbase (se 4 (by rfl) ⟨931626, by rfl⟩ : syracuseStep 9937349 = 1863253) (by norm_num)
theorem B6624899 : Blo 1935435 6624899 := bstep (se 1 (by rfl) ⟨4968674, by rfl⟩ : syracuseStep 6624899 = 9937349) B9937349
theorem B4416599 : Blo 1935435 4416599 := bstep (se 1 (by rfl) ⟨3312449, by rfl⟩ : syracuseStep 4416599 = 6624899) B6624899
theorem B2944399 : Blo 1935435 2944399 := bstep (se 1 (by rfl) ⟨2208299, by rfl⟩ : syracuseStep 2944399 = 4416599) B4416599
theorem B3925865 : Blo 1935435 3925865 := bstep (se 2 (by rfl) ⟨1472199, by rfl⟩ : syracuseStep 3925865 = 2944399) B2944399
theorem B10468973 : Blo 1935435 10468973 := bstep (se 3 (by rfl) ⟨1962932, by rfl⟩ : syracuseStep 10468973 = 3925865) B3925865
theorem B27917261 : Blo 1935435 27917261 := bstep (se 3 (by rfl) ⟨5234486, by rfl⟩ : syracuseStep 27917261 = 10468973) B10468973
theorem B18611507 : Blo 1935435 18611507 := bstep (se 1 (by rfl) ⟨13958630, by rfl⟩ : syracuseStep 18611507 = 27917261) B27917261
theorem B12407671 : Blo 1935435 12407671 := bstep (se 1 (by rfl) ⟨9305753, by rfl⟩ : syracuseStep 12407671 = 18611507) B18611507
theorem B16543561 : Blo 1935435 16543561 := bstep (se 2 (by rfl) ⟨6203835, by rfl⟩ : syracuseStep 16543561 = 12407671) B12407671
theorem B22058081 : Blo 1935435 22058081 := bstep (se 2 (by rfl) ⟨8271780, by rfl⟩ : syracuseStep 22058081 = 16543561) B16543561
theorem B14705387 : Blo 1935435 14705387 := bstep (se 1 (by rfl) ⟨11029040, by rfl⟩ : syracuseStep 14705387 = 22058081) B22058081
theorem B9803591 : Blo 1935435 9803591 := bstep (se 1 (by rfl) ⟨7352693, by rfl⟩ : syracuseStep 9803591 = 14705387) B14705387
theorem B6535727 : Blo 1935435 6535727 := bstep (se 1 (by rfl) ⟨4901795, by rfl⟩ : syracuseStep 6535727 = 9803591) B9803591
theorem B4357151 : Blo 1935435 4357151 := bstep (se 1 (by rfl) ⟨3267863, by rfl⟩ : syracuseStep 4357151 = 6535727) B6535727
theorem B2904767 : Blo 1935435 2904767 := bstep (se 1 (by rfl) ⟨2178575, by rfl⟩ : syracuseStep 2904767 = 4357151) B4357151
theorem B1936511 : Blo 1935435 1936511 := bstep (se 1 (by rfl) ⟨1452383, by rfl⟩ : syracuseStep 1936511 = 2904767) B2904767
theorem B2904773 : Blo 1935435 2904773 := bbase (se 4 (by rfl) ⟨272322, by rfl⟩ : syracuseStep 2904773 = 544645) (by norm_num)
theorem B1936515 : Blo 1935435 1936515 := bstep (se 1 (by rfl) ⟨1452386, by rfl⟩ : syracuseStep 1936515 = 2904773) B2904773
theorem B3267877 : Blo 1935435 3267877 := bbase (se 4 (by rfl) ⟨306363, by rfl⟩ : syracuseStep 3267877 = 612727) (by norm_num)
theorem B4357169 : Blo 1935435 4357169 := bstep (se 2 (by rfl) ⟨1633938, by rfl⟩ : syracuseStep 4357169 = 3267877) B3267877
theorem B2904779 : Blo 1935435 2904779 := bstep (se 1 (by rfl) ⟨2178584, by rfl⟩ : syracuseStep 2904779 = 4357169) B4357169
theorem B1936519 : Blo 1935435 1936519 := bstep (se 1 (by rfl) ⟨1452389, by rfl⟩ : syracuseStep 1936519 = 2904779) B2904779
theorem B2178589 : Blo 1935435 2178589 := bbase (se 3 (by rfl) ⟨408485, by rfl⟩ : syracuseStep 2178589 = 816971) (by norm_num)
theorem B2904785 : Blo 1935435 2904785 := bstep (se 2 (by rfl) ⟨1089294, by rfl⟩ : syracuseStep 2904785 = 2178589) B2178589
theorem B1936523 : Blo 1935435 1936523 := bstep (se 1 (by rfl) ⟨1452392, by rfl⟩ : syracuseStep 1936523 = 2904785) B2904785
theorem B6535781 : Blo 1935435 6535781 := bbase (se 4 (by rfl) ⟨612729, by rfl⟩ : syracuseStep 6535781 = 1225459) (by norm_num)
theorem B4357187 : Blo 1935435 4357187 := bstep (se 1 (by rfl) ⟨3267890, by rfl⟩ : syracuseStep 4357187 = 6535781) B6535781
theorem B2904791 : Blo 1935435 2904791 := bstep (se 1 (by rfl) ⟨2178593, by rfl⟩ : syracuseStep 2904791 = 4357187) B4357187
theorem B1936527 : Blo 1935435 1936527 := bstep (se 1 (by rfl) ⟨1452395, by rfl⟩ : syracuseStep 1936527 = 2904791) B2904791
theorem B2904797 : Blo 1935435 2904797 := bbase (se 3 (by rfl) ⟨544649, by rfl⟩ : syracuseStep 2904797 = 1089299) (by norm_num)
theorem B1936531 : Blo 1935435 1936531 := bstep (se 1 (by rfl) ⟨1452398, by rfl⟩ : syracuseStep 1936531 = 2904797) B2904797
theorem B4357205 : Blo 1935435 4357205 := bbase (se 8 (by rfl) ⟨25530, by rfl⟩ : syracuseStep 4357205 = 51061) (by norm_num)
theorem B2904803 : Blo 1935435 2904803 := bstep (se 1 (by rfl) ⟨2178602, by rfl⟩ : syracuseStep 2904803 = 4357205) B4357205
theorem B1936535 : Blo 1935435 1936535 := bstep (se 1 (by rfl) ⟨1452401, by rfl⟩ : syracuseStep 1936535 = 2904803) B2904803
theorem B13958837 : Blo 1935435 13958837 := bbase (se 5 (by rfl) ⟨654320, by rfl⟩ : syracuseStep 13958837 = 1308641) (by norm_num)
theorem B9305891 : Blo 1935435 9305891 := bstep (se 1 (by rfl) ⟨6979418, by rfl⟩ : syracuseStep 9305891 = 13958837) B13958837
theorem B6203927 : Blo 1935435 6203927 := bstep (se 1 (by rfl) ⟨4652945, by rfl⟩ : syracuseStep 6203927 = 9305891) B9305891
theorem B4135951 : Blo 1935435 4135951 := bstep (se 1 (by rfl) ⟨3101963, by rfl⟩ : syracuseStep 4135951 = 6203927) B6203927
theorem B5514601 : Blo 1935435 5514601 := bstep (se 2 (by rfl) ⟨2067975, by rfl⟩ : syracuseStep 5514601 = 4135951) B4135951
theorem B7352801 : Blo 1935435 7352801 := bstep (se 2 (by rfl) ⟨2757300, by rfl⟩ : syracuseStep 7352801 = 5514601) B5514601
theorem B4901867 : Blo 1935435 4901867 := bstep (se 1 (by rfl) ⟨3676400, by rfl⟩ : syracuseStep 4901867 = 7352801) B7352801
theorem B3267911 : Blo 1935435 3267911 := bstep (se 1 (by rfl) ⟨2450933, by rfl⟩ : syracuseStep 3267911 = 4901867) B4901867
theorem B2178607 : Blo 1935435 2178607 := bstep (se 1 (by rfl) ⟨1633955, by rfl⟩ : syracuseStep 2178607 = 3267911) B3267911
theorem B2904809 : Blo 1935435 2904809 := bstep (se 2 (by rfl) ⟨1089303, by rfl⟩ : syracuseStep 2904809 = 2178607) B2178607
theorem B1936539 : Blo 1935435 1936539 := bstep (se 1 (by rfl) ⟨1452404, by rfl⟩ : syracuseStep 1936539 = 2904809) B2904809
theorem B6288581 : Blo 1935435 6288581 := bbase (se 4 (by rfl) ⟨589554, by rfl⟩ : syracuseStep 6288581 = 1179109) (by norm_num)
theorem B16769549 : Blo 1935435 16769549 := bstep (se 3 (by rfl) ⟨3144290, by rfl⟩ : syracuseStep 16769549 = 6288581) B6288581
theorem B44718797 : Blo 1935435 44718797 := bstep (se 3 (by rfl) ⟨8384774, by rfl⟩ : syracuseStep 44718797 = 16769549) B16769549
theorem B29812531 : Blo 1935435 29812531 := bstep (se 1 (by rfl) ⟨22359398, by rfl⟩ : syracuseStep 29812531 = 44718797) B44718797
theorem B39750041 : Blo 1935435 39750041 := bstep (se 2 (by rfl) ⟨14906265, by rfl⟩ : syracuseStep 39750041 = 29812531) B29812531
theorem B106000109 : Blo 1935435 106000109 := bstep (se 3 (by rfl) ⟨19875020, by rfl⟩ : syracuseStep 106000109 = 39750041) B39750041
theorem B70666739 : Blo 1935435 70666739 := bstep (se 1 (by rfl) ⟨53000054, by rfl⟩ : syracuseStep 70666739 = 106000109) B106000109
theorem B47111159 : Blo 1935435 47111159 := bstep (se 1 (by rfl) ⟨35333369, by rfl⟩ : syracuseStep 47111159 = 70666739) B70666739
theorem B31407439 : Blo 1935435 31407439 := bstep (se 1 (by rfl) ⟨23555579, by rfl⟩ : syracuseStep 31407439 = 47111159) B47111159
theorem B41876585 : Blo 1935435 41876585 := bstep (se 2 (by rfl) ⟨15703719, by rfl⟩ : syracuseStep 41876585 = 31407439) B31407439
theorem B27917723 : Blo 1935435 27917723 := bstep (se 1 (by rfl) ⟨20938292, by rfl⟩ : syracuseStep 27917723 = 41876585) B41876585
theorem B18611815 : Blo 1935435 18611815 := bstep (se 1 (by rfl) ⟨13958861, by rfl⟩ : syracuseStep 18611815 = 27917723) B27917723
theorem B24815753 : Blo 1935435 24815753 := bstep (se 2 (by rfl) ⟨9305907, by rfl⟩ : syracuseStep 24815753 = 18611815) B18611815
theorem B16543835 : Blo 1935435 16543835 := bstep (se 1 (by rfl) ⟨12407876, by rfl⟩ : syracuseStep 16543835 = 24815753) B24815753
theorem B11029223 : Blo 1935435 11029223 := bstep (se 1 (by rfl) ⟨8271917, by rfl⟩ : syracuseStep 11029223 = 16543835) B16543835
theorem B7352815 : Blo 1935435 7352815 := bstep (se 1 (by rfl) ⟨5514611, by rfl⟩ : syracuseStep 7352815 = 11029223) B11029223
theorem B9803753 : Blo 1935435 9803753 := bstep (se 2 (by rfl) ⟨3676407, by rfl⟩ : syracuseStep 9803753 = 7352815) B7352815
theorem B6535835 : Blo 1935435 6535835 := bstep (se 1 (by rfl) ⟨4901876, by rfl⟩ : syracuseStep 6535835 = 9803753) B9803753
theorem B4357223 : Blo 1935435 4357223 := bstep (se 1 (by rfl) ⟨3267917, by rfl⟩ : syracuseStep 4357223 = 6535835) B6535835
theorem B2904815 : Blo 1935435 2904815 := bstep (se 1 (by rfl) ⟨2178611, by rfl⟩ : syracuseStep 2904815 = 4357223) B4357223
theorem B1936543 : Blo 1935435 1936543 := bstep (se 1 (by rfl) ⟨1452407, by rfl⟩ : syracuseStep 1936543 = 2904815) B2904815
theorem B2904821 : Blo 1935435 2904821 := bbase (se 5 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 2904821 = 272327) (by norm_num)
theorem B1936547 : Blo 1935435 1936547 := bstep (se 1 (by rfl) ⟨1452410, by rfl⟩ : syracuseStep 1936547 = 2904821) B2904821
theorem B5234597 : Blo 1935435 5234597 := bbase (se 4 (by rfl) ⟨490743, by rfl⟩ : syracuseStep 5234597 = 981487) (by norm_num)
theorem B3489731 : Blo 1935435 3489731 := bstep (se 1 (by rfl) ⟨2617298, by rfl⟩ : syracuseStep 3489731 = 5234597) B5234597
theorem B2326487 : Blo 1935435 2326487 := bstep (se 1 (by rfl) ⟨1744865, by rfl⟩ : syracuseStep 2326487 = 3489731) B3489731
theorem B6203965 : Blo 1935435 6203965 := bstep (se 3 (by rfl) ⟨1163243, by rfl⟩ : syracuseStep 6203965 = 2326487) B2326487
theorem B8271953 : Blo 1935435 8271953 := bstep (se 2 (by rfl) ⟨3101982, by rfl⟩ : syracuseStep 8271953 = 6203965) B6203965
theorem B5514635 : Blo 1935435 5514635 := bstep (se 1 (by rfl) ⟨4135976, by rfl⟩ : syracuseStep 5514635 = 8271953) B8271953
theorem B3676423 : Blo 1935435 3676423 := bstep (se 1 (by rfl) ⟨2757317, by rfl⟩ : syracuseStep 3676423 = 5514635) B5514635
theorem B4901897 : Blo 1935435 4901897 := bstep (se 2 (by rfl) ⟨1838211, by rfl⟩ : syracuseStep 4901897 = 3676423) B3676423
theorem B3267931 : Blo 1935435 3267931 := bstep (se 1 (by rfl) ⟨2450948, by rfl⟩ : syracuseStep 3267931 = 4901897) B4901897
theorem B4357241 : Blo 1935435 4357241 := bstep (se 2 (by rfl) ⟨1633965, by rfl⟩ : syracuseStep 4357241 = 3267931) B3267931
theorem B2904827 : Blo 1935435 2904827 := bstep (se 1 (by rfl) ⟨2178620, by rfl⟩ : syracuseStep 2904827 = 4357241) B4357241
theorem B1936551 : Blo 1935435 1936551 := bstep (se 1 (by rfl) ⟨1452413, by rfl⟩ : syracuseStep 1936551 = 2904827) B2904827
theorem B2178625 : Blo 1935435 2178625 := bbase (se 2 (by rfl) ⟨816984, by rfl⟩ : syracuseStep 2178625 = 1633969) (by norm_num)
theorem B2904833 : Blo 1935435 2904833 := bstep (se 2 (by rfl) ⟨1089312, by rfl⟩ : syracuseStep 2904833 = 2178625) B2178625
theorem B1936555 : Blo 1935435 1936555 := bstep (se 1 (by rfl) ⟨1452416, by rfl⟩ : syracuseStep 1936555 = 2904833) B2904833
theorem B4901917 : Blo 1935435 4901917 := bbase (se 3 (by rfl) ⟨919109, by rfl⟩ : syracuseStep 4901917 = 1838219) (by norm_num)
theorem B6535889 : Blo 1935435 6535889 := bstep (se 2 (by rfl) ⟨2450958, by rfl⟩ : syracuseStep 6535889 = 4901917) B4901917
theorem B4357259 : Blo 1935435 4357259 := bstep (se 1 (by rfl) ⟨3267944, by rfl⟩ : syracuseStep 4357259 = 6535889) B6535889
theorem B2904839 : Blo 1935435 2904839 := bstep (se 1 (by rfl) ⟨2178629, by rfl⟩ : syracuseStep 2904839 = 4357259) B4357259
theorem B1936559 : Blo 1935435 1936559 := bstep (se 1 (by rfl) ⟨1452419, by rfl⟩ : syracuseStep 1936559 = 2904839) B2904839
theorem B2904845 : Blo 1935435 2904845 := bbase (se 3 (by rfl) ⟨544658, by rfl⟩ : syracuseStep 2904845 = 1089317) (by norm_num)
theorem B1936563 : Blo 1935435 1936563 := bstep (se 1 (by rfl) ⟨1452422, by rfl⟩ : syracuseStep 1936563 = 2904845) B2904845
theorem B4357277 : Blo 1935435 4357277 := bbase (se 3 (by rfl) ⟨816989, by rfl⟩ : syracuseStep 4357277 = 1633979) (by norm_num)
theorem B2904851 : Blo 1935435 2904851 := bstep (se 1 (by rfl) ⟨2178638, by rfl⟩ : syracuseStep 2904851 = 4357277) B4357277
theorem B1936567 : Blo 1935435 1936567 := bstep (se 1 (by rfl) ⟨1452425, by rfl⟩ : syracuseStep 1936567 = 2904851) B2904851
theorem B3267965 : Blo 1935435 3267965 := bbase (se 3 (by rfl) ⟨612743, by rfl⟩ : syracuseStep 3267965 = 1225487) (by norm_num)
theorem B2178643 : Blo 1935435 2178643 := bstep (se 1 (by rfl) ⟨1633982, by rfl⟩ : syracuseStep 2178643 = 3267965) B3267965
theorem B2904857 : Blo 1935435 2904857 := bstep (se 2 (by rfl) ⟨1089321, by rfl⟩ : syracuseStep 2904857 = 2178643) B2178643
theorem B1936571 : Blo 1935435 1936571 := bstep (se 1 (by rfl) ⟨1452428, by rfl⟩ : syracuseStep 1936571 = 2904857) B2904857
theorem B8384917 : Blo 1935435 8384917 := bbase (se 6 (by rfl) ⟨196521, by rfl⟩ : syracuseStep 8384917 = 393043) (by norm_num)
theorem B11179889 : Blo 1935435 11179889 := bstep (se 2 (by rfl) ⟨4192458, by rfl⟩ : syracuseStep 11179889 = 8384917) B8384917
theorem B7453259 : Blo 1935435 7453259 := bstep (se 1 (by rfl) ⟨5589944, by rfl⟩ : syracuseStep 7453259 = 11179889) B11179889
theorem B4968839 : Blo 1935435 4968839 := bstep (se 1 (by rfl) ⟨3726629, by rfl⟩ : syracuseStep 4968839 = 7453259) B7453259
theorem B3312559 : Blo 1935435 3312559 := bstep (se 1 (by rfl) ⟨2484419, by rfl⟩ : syracuseStep 3312559 = 4968839) B4968839
theorem B17666981 : Blo 1935435 17666981 := bstep (se 4 (by rfl) ⟨1656279, by rfl⟩ : syracuseStep 17666981 = 3312559) B3312559
theorem B11777987 : Blo 1935435 11777987 := bstep (se 1 (by rfl) ⟨8833490, by rfl⟩ : syracuseStep 11777987 = 17666981) B17666981
theorem B7851991 : Blo 1935435 7851991 := bstep (se 1 (by rfl) ⟨5888993, by rfl⟩ : syracuseStep 7851991 = 11777987) B11777987
theorem B10469321 : Blo 1935435 10469321 := bstep (se 2 (by rfl) ⟨3925995, by rfl⟩ : syracuseStep 10469321 = 7851991) B7851991
theorem B6979547 : Blo 1935435 6979547 := bstep (se 1 (by rfl) ⟨5234660, by rfl⟩ : syracuseStep 6979547 = 10469321) B10469321
theorem B4653031 : Blo 1935435 4653031 := bstep (se 1 (by rfl) ⟨3489773, by rfl⟩ : syracuseStep 4653031 = 6979547) B6979547
theorem B6204041 : Blo 1935435 6204041 := bstep (se 2 (by rfl) ⟨2326515, by rfl⟩ : syracuseStep 6204041 = 4653031) B4653031
theorem B4136027 : Blo 1935435 4136027 := bstep (se 1 (by rfl) ⟨3102020, by rfl⟩ : syracuseStep 4136027 = 6204041) B6204041
theorem B11029405 : Blo 1935435 11029405 := bstep (se 3 (by rfl) ⟨2068013, by rfl⟩ : syracuseStep 11029405 = 4136027) B4136027
theorem B14705873 : Blo 1935435 14705873 := bstep (se 2 (by rfl) ⟨5514702, by rfl⟩ : syracuseStep 14705873 = 11029405) B11029405
theorem B9803915 : Blo 1935435 9803915 := bstep (se 1 (by rfl) ⟨7352936, by rfl⟩ : syracuseStep 9803915 = 14705873) B14705873
theorem B6535943 : Blo 1935435 6535943 := bstep (se 1 (by rfl) ⟨4901957, by rfl⟩ : syracuseStep 6535943 = 9803915) B9803915
theorem B4357295 : Blo 1935435 4357295 := bstep (se 1 (by rfl) ⟨3267971, by rfl⟩ : syracuseStep 4357295 = 6535943) B6535943
theorem B2904863 : Blo 1935435 2904863 := bstep (se 1 (by rfl) ⟨2178647, by rfl⟩ : syracuseStep 2904863 = 4357295) B4357295
theorem B1936575 : Blo 1935435 1936575 := bstep (se 1 (by rfl) ⟨1452431, by rfl⟩ : syracuseStep 1936575 = 2904863) B2904863
theorem B2904869 : Blo 1935435 2904869 := bbase (se 4 (by rfl) ⟨272331, by rfl⟩ : syracuseStep 2904869 = 544663) (by norm_num)
theorem B1936579 : Blo 1935435 1936579 := bstep (se 1 (by rfl) ⟨1452434, by rfl⟩ : syracuseStep 1936579 = 2904869) B2904869
theorem B2450989 : Blo 1935435 2450989 := bbase (se 3 (by rfl) ⟨459560, by rfl⟩ : syracuseStep 2450989 = 919121) (by norm_num)
theorem B3267985 : Blo 1935435 3267985 := bstep (se 2 (by rfl) ⟨1225494, by rfl⟩ : syracuseStep 3267985 = 2450989) B2450989
theorem B4357313 : Blo 1935435 4357313 := bstep (se 2 (by rfl) ⟨1633992, by rfl⟩ : syracuseStep 4357313 = 3267985) B3267985
theorem B2904875 : Blo 1935435 2904875 := bstep (se 1 (by rfl) ⟨2178656, by rfl⟩ : syracuseStep 2904875 = 4357313) B4357313
theorem B1936583 : Blo 1935435 1936583 := bstep (se 1 (by rfl) ⟨1452437, by rfl⟩ : syracuseStep 1936583 = 2904875) B2904875
theorem B2178661 : Blo 1935435 2178661 := bbase (se 4 (by rfl) ⟨204249, by rfl⟩ : syracuseStep 2178661 = 408499) (by norm_num)
theorem B2904881 : Blo 1935435 2904881 := bstep (se 2 (by rfl) ⟨1089330, by rfl⟩ : syracuseStep 2904881 = 2178661) B2178661
theorem B1936587 : Blo 1935435 1936587 := bstep (se 1 (by rfl) ⟨1452440, by rfl⟩ : syracuseStep 1936587 = 2904881) B2904881
theorem B15704117 : Blo 1935435 15704117 := bbase (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) (by norm_num)
theorem B10469411 : Blo 1935435 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B6979607 : Blo 1935435 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B4653071 : Blo 1935435 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B3102047 : Blo 1935435 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B2068031 : Blo 1935435 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B5514749 : Blo 1935435 5514749 := bstep (se 3 (by rfl) ⟨1034015, by rfl⟩ : syracuseStep 5514749 = 2068031) B2068031
theorem B3676499 : Blo 1935435 3676499 := bstep (se 1 (by rfl) ⟨2757374, by rfl⟩ : syracuseStep 3676499 = 5514749) B5514749
theorem B2450999 : Blo 1935435 2450999 := bstep (se 1 (by rfl) ⟨1838249, by rfl⟩ : syracuseStep 2450999 = 3676499) B3676499
theorem B6535997 : Blo 1935435 6535997 := bstep (se 3 (by rfl) ⟨1225499, by rfl⟩ : syracuseStep 6535997 = 2450999) B2450999
theorem B4357331 : Blo 1935435 4357331 := bstep (se 1 (by rfl) ⟨3267998, by rfl⟩ : syracuseStep 4357331 = 6535997) B6535997
theorem B2904887 : Blo 1935435 2904887 := bstep (se 1 (by rfl) ⟨2178665, by rfl⟩ : syracuseStep 2904887 = 4357331) B4357331
theorem B1936591 : Blo 1935435 1936591 := bstep (se 1 (by rfl) ⟨1452443, by rfl⟩ : syracuseStep 1936591 = 2904887) B2904887
theorem B2904893 : Blo 1935435 2904893 := bbase (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) (by norm_num)
theorem B1936595 : Blo 1935435 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B4357349 : Blo 1935435 4357349 := bbase (se 4 (by rfl) ⟨408501, by rfl⟩ : syracuseStep 4357349 = 817003) (by norm_num)
theorem B2904899 : Blo 1935435 2904899 := bstep (se 1 (by rfl) ⟨2178674, by rfl⟩ : syracuseStep 2904899 = 4357349) B4357349
theorem B1936599 : Blo 1935435 1936599 := bstep (se 1 (by rfl) ⟨1452449, by rfl⟩ : syracuseStep 1936599 = 2904899) B2904899
theorem B4902029 : Blo 1935435 4902029 := bbase (se 3 (by rfl) ⟨919130, by rfl⟩ : syracuseStep 4902029 = 1838261) (by norm_num)
theorem B3268019 : Blo 1935435 3268019 := bstep (se 1 (by rfl) ⟨2451014, by rfl⟩ : syracuseStep 3268019 = 4902029) B4902029
theorem B2178679 : Blo 1935435 2178679 := bstep (se 1 (by rfl) ⟨1634009, by rfl⟩ : syracuseStep 2178679 = 3268019) B3268019
theorem B2904905 : Blo 1935435 2904905 := bstep (se 2 (by rfl) ⟨1089339, by rfl⟩ : syracuseStep 2904905 = 2178679) B2178679
theorem B1936603 : Blo 1935435 1936603 := bstep (se 1 (by rfl) ⟨1452452, by rfl⟩ : syracuseStep 1936603 = 2904905) B2904905
theorem B2757397 : Blo 1935435 2757397 := bbase (se 6 (by rfl) ⟨64626, by rfl⟩ : syracuseStep 2757397 = 129253) (by norm_num)
theorem B3676529 : Blo 1935435 3676529 := bstep (se 2 (by rfl) ⟨1378698, by rfl⟩ : syracuseStep 3676529 = 2757397) B2757397
theorem B9804077 : Blo 1935435 9804077 := bstep (se 3 (by rfl) ⟨1838264, by rfl⟩ : syracuseStep 9804077 = 3676529) B3676529
theorem B6536051 : Blo 1935435 6536051 := bstep (se 1 (by rfl) ⟨4902038, by rfl⟩ : syracuseStep 6536051 = 9804077) B9804077
theorem B4357367 : Blo 1935435 4357367 := bstep (se 1 (by rfl) ⟨3268025, by rfl⟩ : syracuseStep 4357367 = 6536051) B6536051
theorem B2904911 : Blo 1935435 2904911 := bstep (se 1 (by rfl) ⟨2178683, by rfl⟩ : syracuseStep 2904911 = 4357367) B4357367
theorem B1936607 : Blo 1935435 1936607 := bstep (se 1 (by rfl) ⟨1452455, by rfl⟩ : syracuseStep 1936607 = 2904911) B2904911
theorem B2904917 : Blo 1935435 2904917 := bbase (se 9 (by rfl) ⟨8510, by rfl⟩ : syracuseStep 2904917 = 17021) (by norm_num)
theorem B1936611 : Blo 1935435 1936611 := bstep (se 1 (by rfl) ⟨1452458, by rfl⟩ : syracuseStep 1936611 = 2904917) B2904917
theorem B3102085 : Blo 1935435 3102085 := bbase (se 4 (by rfl) ⟨290820, by rfl⟩ : syracuseStep 3102085 = 581641) (by norm_num)
theorem B4136113 : Blo 1935435 4136113 := bstep (se 2 (by rfl) ⟨1551042, by rfl⟩ : syracuseStep 4136113 = 3102085) B3102085
theorem B5514817 : Blo 1935435 5514817 := bstep (se 2 (by rfl) ⟨2068056, by rfl⟩ : syracuseStep 5514817 = 4136113) B4136113
theorem B7353089 : Blo 1935435 7353089 := bstep (se 2 (by rfl) ⟨2757408, by rfl⟩ : syracuseStep 7353089 = 5514817) B5514817
theorem B4902059 : Blo 1935435 4902059 := bstep (se 1 (by rfl) ⟨3676544, by rfl⟩ : syracuseStep 4902059 = 7353089) B7353089
theorem B3268039 : Blo 1935435 3268039 := bstep (se 1 (by rfl) ⟨2451029, by rfl⟩ : syracuseStep 3268039 = 4902059) B4902059
theorem B4357385 : Blo 1935435 4357385 := bstep (se 2 (by rfl) ⟨1634019, by rfl⟩ : syracuseStep 4357385 = 3268039) B3268039
theorem B2904923 : Blo 1935435 2904923 := bstep (se 1 (by rfl) ⟨2178692, by rfl⟩ : syracuseStep 2904923 = 4357385) B4357385
theorem B1936615 : Blo 1935435 1936615 := bstep (se 1 (by rfl) ⟨1452461, by rfl⟩ : syracuseStep 1936615 = 2904923) B2904923
theorem B2178697 : Blo 1935435 2178697 := bbase (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) (by norm_num)
theorem B2904929 : Blo 1935435 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B1936619 : Blo 1935435 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B2484481 : Blo 1935435 2484481 := bbase (se 2 (by rfl) ⟨931680, by rfl⟩ : syracuseStep 2484481 = 1863361) (by norm_num)
theorem B3312641 : Blo 1935435 3312641 := bstep (se 2 (by rfl) ⟨1242240, by rfl⟩ : syracuseStep 3312641 = 2484481) B2484481
theorem B2208427 : Blo 1935435 2208427 := bstep (se 1 (by rfl) ⟨1656320, by rfl⟩ : syracuseStep 2208427 = 3312641) B3312641
theorem B11778277 : Blo 1935435 11778277 := bstep (se 4 (by rfl) ⟨1104213, by rfl⟩ : syracuseStep 11778277 = 2208427) B2208427
theorem B15704369 : Blo 1935435 15704369 := bstep (se 2 (by rfl) ⟨5889138, by rfl⟩ : syracuseStep 15704369 = 11778277) B11778277
theorem B10469579 : Blo 1935435 10469579 := bstep (se 1 (by rfl) ⟨7852184, by rfl⟩ : syracuseStep 10469579 = 15704369) B15704369
theorem B27918877 : Blo 1935435 27918877 := bstep (se 3 (by rfl) ⟨5234789, by rfl⟩ : syracuseStep 27918877 = 10469579) B10469579
theorem B37225169 : Blo 1935435 37225169 := bstep (se 2 (by rfl) ⟨13959438, by rfl⟩ : syracuseStep 37225169 = 27918877) B27918877
theorem B24816779 : Blo 1935435 24816779 := bstep (se 1 (by rfl) ⟨18612584, by rfl⟩ : syracuseStep 24816779 = 37225169) B37225169
theorem B16544519 : Blo 1935435 16544519 := bstep (se 1 (by rfl) ⟨12408389, by rfl⟩ : syracuseStep 16544519 = 24816779) B24816779
theorem B11029679 : Blo 1935435 11029679 := bstep (se 1 (by rfl) ⟨8272259, by rfl⟩ : syracuseStep 11029679 = 16544519) B16544519
theorem B7353119 : Blo 1935435 7353119 := bstep (se 1 (by rfl) ⟨5514839, by rfl⟩ : syracuseStep 7353119 = 11029679) B11029679
theorem B4902079 : Blo 1935435 4902079 := bstep (se 1 (by rfl) ⟨3676559, by rfl⟩ : syracuseStep 4902079 = 7353119) B7353119
theorem B6536105 : Blo 1935435 6536105 := bstep (se 2 (by rfl) ⟨2451039, by rfl⟩ : syracuseStep 6536105 = 4902079) B4902079
theorem B4357403 : Blo 1935435 4357403 := bstep (se 1 (by rfl) ⟨3268052, by rfl⟩ : syracuseStep 4357403 = 6536105) B6536105
theorem B2904935 : Blo 1935435 2904935 := bstep (se 1 (by rfl) ⟨2178701, by rfl⟩ : syracuseStep 2904935 = 4357403) B4357403
theorem B1936623 : Blo 1935435 1936623 := bstep (se 1 (by rfl) ⟨1452467, by rfl⟩ : syracuseStep 1936623 = 2904935) B2904935
theorem B2904941 : Blo 1935435 2904941 := bbase (se 3 (by rfl) ⟨544676, by rfl⟩ : syracuseStep 2904941 = 1089353) (by norm_num)
theorem B1936627 : Blo 1935435 1936627 := bstep (se 1 (by rfl) ⟨1452470, by rfl⟩ : syracuseStep 1936627 = 2904941) B2904941
theorem B4357421 : Blo 1935435 4357421 := bbase (se 3 (by rfl) ⟨817016, by rfl⟩ : syracuseStep 4357421 = 1634033) (by norm_num)
theorem B2904947 : Blo 1935435 2904947 := bstep (se 1 (by rfl) ⟨2178710, by rfl⟩ : syracuseStep 2904947 = 4357421) B4357421
theorem B1936631 : Blo 1935435 1936631 := bstep (se 1 (by rfl) ⟨1452473, by rfl⟩ : syracuseStep 1936631 = 2904947) B2904947
theorem B6979765 : Blo 1935435 6979765 := bbase (se 5 (by rfl) ⟨327176, by rfl⟩ : syracuseStep 6979765 = 654353) (by norm_num)
theorem B9306353 : Blo 1935435 9306353 := bstep (se 2 (by rfl) ⟨3489882, by rfl⟩ : syracuseStep 9306353 = 6979765) B6979765
theorem B6204235 : Blo 1935435 6204235 := bstep (se 1 (by rfl) ⟨4653176, by rfl⟩ : syracuseStep 6204235 = 9306353) B9306353
theorem B8272313 : Blo 1935435 8272313 := bstep (se 2 (by rfl) ⟨3102117, by rfl⟩ : syracuseStep 8272313 = 6204235) B6204235
theorem B5514875 : Blo 1935435 5514875 := bstep (se 1 (by rfl) ⟨4136156, by rfl⟩ : syracuseStep 5514875 = 8272313) B8272313
theorem B3676583 : Blo 1935435 3676583 := bstep (se 1 (by rfl) ⟨2757437, by rfl⟩ : syracuseStep 3676583 = 5514875) B5514875
theorem B2451055 : Blo 1935435 2451055 := bstep (se 1 (by rfl) ⟨1838291, by rfl⟩ : syracuseStep 2451055 = 3676583) B3676583
theorem B3268073 : Blo 1935435 3268073 := bstep (se 2 (by rfl) ⟨1225527, by rfl⟩ : syracuseStep 3268073 = 2451055) B2451055
theorem B2178715 : Blo 1935435 2178715 := bstep (se 1 (by rfl) ⟨1634036, by rfl⟩ : syracuseStep 2178715 = 3268073) B3268073
theorem B2904953 : Blo 1935435 2904953 := bstep (se 2 (by rfl) ⟨1089357, by rfl⟩ : syracuseStep 2904953 = 2178715) B2178715
theorem B1936635 : Blo 1935435 1936635 := bstep (se 1 (by rfl) ⟨1452476, by rfl⟩ : syracuseStep 1936635 = 2904953) B2904953
theorem B8833781 : Blo 1935435 8833781 := bbase (se 5 (by rfl) ⟨414083, by rfl⟩ : syracuseStep 8833781 = 828167) (by norm_num)
theorem B5889187 : Blo 1935435 5889187 := bstep (se 1 (by rfl) ⟨4416890, by rfl⟩ : syracuseStep 5889187 = 8833781) B8833781
theorem B7852249 : Blo 1935435 7852249 := bstep (se 2 (by rfl) ⟨2944593, by rfl⟩ : syracuseStep 7852249 = 5889187) B5889187
theorem B10469665 : Blo 1935435 10469665 := bstep (se 2 (by rfl) ⟨3926124, by rfl⟩ : syracuseStep 10469665 = 7852249) B7852249
theorem B13959553 : Blo 1935435 13959553 := bstep (se 2 (by rfl) ⟨5234832, by rfl⟩ : syracuseStep 13959553 = 10469665) B10469665
theorem B18612737 : Blo 1935435 18612737 := bstep (se 2 (by rfl) ⟨6979776, by rfl⟩ : syracuseStep 18612737 = 13959553) B13959553
theorem B12408491 : Blo 1935435 12408491 := bstep (se 1 (by rfl) ⟨9306368, by rfl⟩ : syracuseStep 12408491 = 18612737) B18612737
theorem B33089309 : Blo 1935435 33089309 := bstep (se 3 (by rfl) ⟨6204245, by rfl⟩ : syracuseStep 33089309 = 12408491) B12408491
theorem B22059539 : Blo 1935435 22059539 := bstep (se 1 (by rfl) ⟨16544654, by rfl⟩ : syracuseStep 22059539 = 33089309) B33089309
theorem B14706359 : Blo 1935435 14706359 := bstep (se 1 (by rfl) ⟨11029769, by rfl⟩ : syracuseStep 14706359 = 22059539) B22059539
theorem B9804239 : Blo 1935435 9804239 := bstep (se 1 (by rfl) ⟨7353179, by rfl⟩ : syracuseStep 9804239 = 14706359) B14706359
theorem B6536159 : Blo 1935435 6536159 := bstep (se 1 (by rfl) ⟨4902119, by rfl⟩ : syracuseStep 6536159 = 9804239) B9804239
theorem B4357439 : Blo 1935435 4357439 := bstep (se 1 (by rfl) ⟨3268079, by rfl⟩ : syracuseStep 4357439 = 6536159) B6536159
theorem B2904959 : Blo 1935435 2904959 := bstep (se 1 (by rfl) ⟨2178719, by rfl⟩ : syracuseStep 2904959 = 4357439) B4357439
theorem B1936639 : Blo 1935435 1936639 := bstep (se 1 (by rfl) ⟨1452479, by rfl⟩ : syracuseStep 1936639 = 2904959) B2904959
theorem B2904965 : Blo 1935435 2904965 := bbase (se 4 (by rfl) ⟨272340, by rfl⟩ : syracuseStep 2904965 = 544681) (by norm_num)
theorem B1936643 : Blo 1935435 1936643 := bstep (se 1 (by rfl) ⟨1452482, by rfl⟩ : syracuseStep 1936643 = 2904965) B2904965
theorem B3268093 : Blo 1935435 3268093 := bbase (se 3 (by rfl) ⟨612767, by rfl⟩ : syracuseStep 3268093 = 1225535) (by norm_num)
theorem B4357457 : Blo 1935435 4357457 := bstep (se 2 (by rfl) ⟨1634046, by rfl⟩ : syracuseStep 4357457 = 3268093) B3268093
theorem B2904971 : Blo 1935435 2904971 := bstep (se 1 (by rfl) ⟨2178728, by rfl⟩ : syracuseStep 2904971 = 4357457) B4357457
theorem B1936647 : Blo 1935435 1936647 := bstep (se 1 (by rfl) ⟨1452485, by rfl⟩ : syracuseStep 1936647 = 2904971) B2904971
theorem B2178733 : Blo 1935435 2178733 := bbase (se 3 (by rfl) ⟨408512, by rfl⟩ : syracuseStep 2178733 = 817025) (by norm_num)
theorem B2904977 : Blo 1935435 2904977 := bstep (se 2 (by rfl) ⟨1089366, by rfl⟩ : syracuseStep 2904977 = 2178733) B2178733
theorem B1936651 : Blo 1935435 1936651 := bstep (se 1 (by rfl) ⟨1452488, by rfl⟩ : syracuseStep 1936651 = 2904977) B2904977
theorem B6536213 : Blo 1935435 6536213 := bbase (se 6 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 6536213 = 306385) (by norm_num)
theorem B4357475 : Blo 1935435 4357475 := bstep (se 1 (by rfl) ⟨3268106, by rfl⟩ : syracuseStep 4357475 = 6536213) B6536213
theorem B2904983 : Blo 1935435 2904983 := bstep (se 1 (by rfl) ⟨2178737, by rfl⟩ : syracuseStep 2904983 = 4357475) B4357475
theorem B1936655 : Blo 1935435 1936655 := bstep (se 1 (by rfl) ⟨1452491, by rfl⟩ : syracuseStep 1936655 = 2904983) B2904983
theorem B2904989 : Blo 1935435 2904989 := bbase (se 3 (by rfl) ⟨544685, by rfl⟩ : syracuseStep 2904989 = 1089371) (by norm_num)
theorem B1936659 : Blo 1935435 1936659 := bstep (se 1 (by rfl) ⟨1452494, by rfl⟩ : syracuseStep 1936659 = 2904989) B2904989
theorem B4357493 : Blo 1935435 4357493 := bbase (se 5 (by rfl) ⟨204257, by rfl⟩ : syracuseStep 4357493 = 408515) (by norm_num)
theorem B2904995 : Blo 1935435 2904995 := bstep (se 1 (by rfl) ⟨2178746, by rfl⟩ : syracuseStep 2904995 = 4357493) B4357493
theorem B1936663 : Blo 1935435 1936663 := bstep (se 1 (by rfl) ⟨1452497, by rfl⟩ : syracuseStep 1936663 = 2904995) B2904995
theorem B2096329 : Blo 1935435 2096329 := bbase (se 2 (by rfl) ⟨786123, by rfl⟩ : syracuseStep 2096329 = 1572247) (by norm_num)
theorem B2795105 : Blo 1935435 2795105 := bstep (se 2 (by rfl) ⟨1048164, by rfl⟩ : syracuseStep 2795105 = 2096329) B2096329
theorem B7453613 : Blo 1935435 7453613 := bstep (se 3 (by rfl) ⟨1397552, by rfl⟩ : syracuseStep 7453613 = 2795105) B2795105
theorem B4969075 : Blo 1935435 4969075 := bstep (se 1 (by rfl) ⟨3726806, by rfl⟩ : syracuseStep 4969075 = 7453613) B7453613
theorem B6625433 : Blo 1935435 6625433 := bstep (se 2 (by rfl) ⟨2484537, by rfl⟩ : syracuseStep 6625433 = 4969075) B4969075
theorem B17667821 : Blo 1935435 17667821 := bstep (se 3 (by rfl) ⟨3312716, by rfl⟩ : syracuseStep 17667821 = 6625433) B6625433
theorem B11778547 : Blo 1935435 11778547 := bstep (se 1 (by rfl) ⟨8833910, by rfl⟩ : syracuseStep 11778547 = 17667821) B17667821
theorem B15704729 : Blo 1935435 15704729 := bstep (se 2 (by rfl) ⟨5889273, by rfl⟩ : syracuseStep 15704729 = 11778547) B11778547
theorem B10469819 : Blo 1935435 10469819 := bstep (se 1 (by rfl) ⟨7852364, by rfl⟩ : syracuseStep 10469819 = 15704729) B15704729
theorem B6979879 : Blo 1935435 6979879 := bstep (se 1 (by rfl) ⟨5234909, by rfl⟩ : syracuseStep 6979879 = 10469819) B10469819
theorem B9306505 : Blo 1935435 9306505 := bstep (se 2 (by rfl) ⟨3489939, by rfl⟩ : syracuseStep 9306505 = 6979879) B6979879
theorem B12408673 : Blo 1935435 12408673 := bstep (se 2 (by rfl) ⟨4653252, by rfl⟩ : syracuseStep 12408673 = 9306505) B9306505
theorem B16544897 : Blo 1935435 16544897 := bstep (se 2 (by rfl) ⟨6204336, by rfl⟩ : syracuseStep 16544897 = 12408673) B12408673
theorem B11029931 : Blo 1935435 11029931 := bstep (se 1 (by rfl) ⟨8272448, by rfl⟩ : syracuseStep 11029931 = 16544897) B16544897
theorem B7353287 : Blo 1935435 7353287 := bstep (se 1 (by rfl) ⟨5514965, by rfl⟩ : syracuseStep 7353287 = 11029931) B11029931
theorem B4902191 : Blo 1935435 4902191 := bstep (se 1 (by rfl) ⟨3676643, by rfl⟩ : syracuseStep 4902191 = 7353287) B7353287
theorem B3268127 : Blo 1935435 3268127 := bstep (se 1 (by rfl) ⟨2451095, by rfl⟩ : syracuseStep 3268127 = 4902191) B4902191
theorem B2178751 : Blo 1935435 2178751 := bstep (se 1 (by rfl) ⟨1634063, by rfl⟩ : syracuseStep 2178751 = 3268127) B3268127
theorem B2905001 : Blo 1935435 2905001 := bstep (se 2 (by rfl) ⟨1089375, by rfl⟩ : syracuseStep 2905001 = 2178751) B2178751
theorem B1936667 : Blo 1935435 1936667 := bstep (se 1 (by rfl) ⟨1452500, by rfl⟩ : syracuseStep 1936667 = 2905001) B2905001
theorem B7353301 : Blo 1935435 7353301 := bbase (se 7 (by rfl) ⟨86171, by rfl⟩ : syracuseStep 7353301 = 172343) (by norm_num)
theorem B9804401 : Blo 1935435 9804401 := bstep (se 2 (by rfl) ⟨3676650, by rfl⟩ : syracuseStep 9804401 = 7353301) B7353301
theorem B6536267 : Blo 1935435 6536267 := bstep (se 1 (by rfl) ⟨4902200, by rfl⟩ : syracuseStep 6536267 = 9804401) B9804401
theorem B4357511 : Blo 1935435 4357511 := bstep (se 1 (by rfl) ⟨3268133, by rfl⟩ : syracuseStep 4357511 = 6536267) B6536267
theorem B2905007 : Blo 1935435 2905007 := bstep (se 1 (by rfl) ⟨2178755, by rfl⟩ : syracuseStep 2905007 = 4357511) B4357511
theorem B1936671 : Blo 1935435 1936671 := bstep (se 1 (by rfl) ⟨1452503, by rfl⟩ : syracuseStep 1936671 = 2905007) B2905007
theorem B2905013 : Blo 1935435 2905013 := bbase (se 5 (by rfl) ⟨136172, by rfl⟩ : syracuseStep 2905013 = 272345) (by norm_num)
theorem B1936675 : Blo 1935435 1936675 := bstep (se 1 (by rfl) ⟨1452506, by rfl⟩ : syracuseStep 1936675 = 2905013) B2905013
theorem B4902221 : Blo 1935435 4902221 := bbase (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) (by norm_num)
theorem B3268147 : Blo 1935435 3268147 := bstep (se 1 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 3268147 = 4902221) B4902221
theorem B4357529 : Blo 1935435 4357529 := bstep (se 2 (by rfl) ⟨1634073, by rfl⟩ : syracuseStep 4357529 = 3268147) B3268147
theorem B2905019 : Blo 1935435 2905019 := bstep (se 1 (by rfl) ⟨2178764, by rfl⟩ : syracuseStep 2905019 = 4357529) B4357529
theorem B1936679 : Blo 1935435 1936679 := bstep (se 1 (by rfl) ⟨1452509, by rfl⟩ : syracuseStep 1936679 = 2905019) B2905019
theorem B2178769 : Blo 1935435 2178769 := bbase (se 2 (by rfl) ⟨817038, by rfl⟩ : syracuseStep 2178769 = 1634077) (by norm_num)
theorem B2905025 : Blo 1935435 2905025 := bstep (se 2 (by rfl) ⟨1089384, by rfl⟩ : syracuseStep 2905025 = 2178769) B2178769
theorem B1936683 : Blo 1935435 1936683 := bstep (se 1 (by rfl) ⟨1452512, by rfl⟩ : syracuseStep 1936683 = 2905025) B2905025
theorem B4653301 : Blo 1935435 4653301 := bbase (se 5 (by rfl) ⟨218123, by rfl⟩ : syracuseStep 4653301 = 436247) (by norm_num)
theorem B6204401 : Blo 1935435 6204401 := bstep (se 2 (by rfl) ⟨2326650, by rfl⟩ : syracuseStep 6204401 = 4653301) B4653301
theorem B4136267 : Blo 1935435 4136267 := bstep (se 1 (by rfl) ⟨3102200, by rfl⟩ : syracuseStep 4136267 = 6204401) B6204401
theorem B2757511 : Blo 1935435 2757511 := bstep (se 1 (by rfl) ⟨2068133, by rfl⟩ : syracuseStep 2757511 = 4136267) B4136267
theorem B3676681 : Blo 1935435 3676681 := bstep (se 2 (by rfl) ⟨1378755, by rfl⟩ : syracuseStep 3676681 = 2757511) B2757511
theorem B4902241 : Blo 1935435 4902241 := bstep (se 2 (by rfl) ⟨1838340, by rfl⟩ : syracuseStep 4902241 = 3676681) B3676681
theorem B6536321 : Blo 1935435 6536321 := bstep (se 2 (by rfl) ⟨2451120, by rfl⟩ : syracuseStep 6536321 = 4902241) B4902241
theorem B4357547 : Blo 1935435 4357547 := bstep (se 1 (by rfl) ⟨3268160, by rfl⟩ : syracuseStep 4357547 = 6536321) B6536321
theorem B2905031 : Blo 1935435 2905031 := bstep (se 1 (by rfl) ⟨2178773, by rfl⟩ : syracuseStep 2905031 = 4357547) B4357547
theorem B1936687 : Blo 1935435 1936687 := bstep (se 1 (by rfl) ⟨1452515, by rfl⟩ : syracuseStep 1936687 = 2905031) B2905031
theorem B2905037 : Blo 1935435 2905037 := bbase (se 3 (by rfl) ⟨544694, by rfl⟩ : syracuseStep 2905037 = 1089389) (by norm_num)
theorem B1936691 : Blo 1935435 1936691 := bstep (se 1 (by rfl) ⟨1452518, by rfl⟩ : syracuseStep 1936691 = 2905037) B2905037
theorem B4357565 : Blo 1935435 4357565 := bbase (se 3 (by rfl) ⟨817043, by rfl⟩ : syracuseStep 4357565 = 1634087) (by norm_num)
theorem B2905043 : Blo 1935435 2905043 := bstep (se 1 (by rfl) ⟨2178782, by rfl⟩ : syracuseStep 2905043 = 4357565) B4357565
theorem B1936695 : Blo 1935435 1936695 := bstep (se 1 (by rfl) ⟨1452521, by rfl⟩ : syracuseStep 1936695 = 2905043) B2905043
theorem B3268181 : Blo 1935435 3268181 := bbase (se 8 (by rfl) ⟨19149, by rfl⟩ : syracuseStep 3268181 = 38299) (by norm_num)
theorem B2178787 : Blo 1935435 2178787 := bstep (se 1 (by rfl) ⟨1634090, by rfl⟩ : syracuseStep 2178787 = 3268181) B3268181
theorem B2905049 : Blo 1935435 2905049 := bstep (se 2 (by rfl) ⟨1089393, by rfl⟩ : syracuseStep 2905049 = 2178787) B2178787
theorem B1936699 : Blo 1935435 1936699 := bstep (se 1 (by rfl) ⟨1452524, by rfl⟩ : syracuseStep 1936699 = 2905049) B2905049
theorem B9306677 : Blo 1935435 9306677 := bbase (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) (by norm_num)
theorem B6204451 : Blo 1935435 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B8272601 : Blo 1935435 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B5515067 : Blo 1935435 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B14706845 : Blo 1935435 14706845 := bstep (se 3 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 14706845 = 5515067) B5515067
theorem B9804563 : Blo 1935435 9804563 := bstep (se 1 (by rfl) ⟨7353422, by rfl⟩ : syracuseStep 9804563 = 14706845) B14706845
theorem B6536375 : Blo 1935435 6536375 := bstep (se 1 (by rfl) ⟨4902281, by rfl⟩ : syracuseStep 6536375 = 9804563) B9804563
theorem B4357583 : Blo 1935435 4357583 := bstep (se 1 (by rfl) ⟨3268187, by rfl⟩ : syracuseStep 4357583 = 6536375) B6536375
theorem B2905055 : Blo 1935435 2905055 := bstep (se 1 (by rfl) ⟨2178791, by rfl⟩ : syracuseStep 2905055 = 4357583) B4357583
theorem B1936703 : Blo 1935435 1936703 := bstep (se 1 (by rfl) ⟨1452527, by rfl⟩ : syracuseStep 1936703 = 2905055) B2905055
theorem B2905061 : Blo 1935435 2905061 := bbase (se 4 (by rfl) ⟨272349, by rfl⟩ : syracuseStep 2905061 = 544699) (by norm_num)
theorem B1936707 : Blo 1935435 1936707 := bstep (se 1 (by rfl) ⟨1452530, by rfl⟩ : syracuseStep 1936707 = 2905061) B2905061
theorem B4969189 : Blo 1935435 4969189 := bbase (se 4 (by rfl) ⟨465861, by rfl⟩ : syracuseStep 4969189 = 931723) (by norm_num)
theorem B6625585 : Blo 1935435 6625585 := bstep (se 2 (by rfl) ⟨2484594, by rfl⟩ : syracuseStep 6625585 = 4969189) B4969189
theorem B8834113 : Blo 1935435 8834113 := bstep (se 2 (by rfl) ⟨3312792, by rfl⟩ : syracuseStep 8834113 = 6625585) B6625585
theorem B11778817 : Blo 1935435 11778817 := bstep (se 2 (by rfl) ⟨4417056, by rfl⟩ : syracuseStep 11778817 = 8834113) B8834113
theorem B15705089 : Blo 1935435 15705089 := bstep (se 2 (by rfl) ⟨5889408, by rfl⟩ : syracuseStep 15705089 = 11778817) B11778817
theorem B10470059 : Blo 1935435 10470059 := bstep (se 1 (by rfl) ⟨7852544, by rfl⟩ : syracuseStep 10470059 = 15705089) B15705089
theorem B6980039 : Blo 1935435 6980039 := bstep (se 1 (by rfl) ⟨5235029, by rfl⟩ : syracuseStep 6980039 = 10470059) B10470059
theorem B4653359 : Blo 1935435 4653359 := bstep (se 1 (by rfl) ⟨3490019, by rfl⟩ : syracuseStep 4653359 = 6980039) B6980039
theorem B3102239 : Blo 1935435 3102239 := bstep (se 1 (by rfl) ⟨2326679, by rfl⟩ : syracuseStep 3102239 = 4653359) B4653359
theorem B8272637 : Blo 1935435 8272637 := bstep (se 3 (by rfl) ⟨1551119, by rfl⟩ : syracuseStep 8272637 = 3102239) B3102239
theorem B5515091 : Blo 1935435 5515091 := bstep (se 1 (by rfl) ⟨4136318, by rfl⟩ : syracuseStep 5515091 = 8272637) B8272637
theorem B3676727 : Blo 1935435 3676727 := bstep (se 1 (by rfl) ⟨2757545, by rfl⟩ : syracuseStep 3676727 = 5515091) B5515091
theorem B2451151 : Blo 1935435 2451151 := bstep (se 1 (by rfl) ⟨1838363, by rfl⟩ : syracuseStep 2451151 = 3676727) B3676727
theorem B3268201 : Blo 1935435 3268201 := bstep (se 2 (by rfl) ⟨1225575, by rfl⟩ : syracuseStep 3268201 = 2451151) B2451151
theorem B4357601 : Blo 1935435 4357601 := bstep (se 2 (by rfl) ⟨1634100, by rfl⟩ : syracuseStep 4357601 = 3268201) B3268201
theorem B2905067 : Blo 1935435 2905067 := bstep (se 1 (by rfl) ⟨2178800, by rfl⟩ : syracuseStep 2905067 = 4357601) B4357601
theorem B1936711 : Blo 1935435 1936711 := bstep (se 1 (by rfl) ⟨1452533, by rfl⟩ : syracuseStep 1936711 = 2905067) B2905067
theorem B2178805 : Blo 1935435 2178805 := bbase (se 5 (by rfl) ⟨102131, by rfl⟩ : syracuseStep 2178805 = 204263) (by norm_num)
theorem B2905073 : Blo 1935435 2905073 := bstep (se 2 (by rfl) ⟨1089402, by rfl⟩ : syracuseStep 2905073 = 2178805) B2178805
theorem B1936715 : Blo 1935435 1936715 := bstep (se 1 (by rfl) ⟨1452536, by rfl⟩ : syracuseStep 1936715 = 2905073) B2905073
theorem B2451161 : Blo 1935435 2451161 := bbase (se 2 (by rfl) ⟨919185, by rfl⟩ : syracuseStep 2451161 = 1838371) (by norm_num)
theorem B6536429 : Blo 1935435 6536429 := bstep (se 3 (by rfl) ⟨1225580, by rfl⟩ : syracuseStep 6536429 = 2451161) B2451161
theorem B4357619 : Blo 1935435 4357619 := bstep (se 1 (by rfl) ⟨3268214, by rfl⟩ : syracuseStep 4357619 = 6536429) B6536429
theorem B2905079 : Blo 1935435 2905079 := bstep (se 1 (by rfl) ⟨2178809, by rfl⟩ : syracuseStep 2905079 = 4357619) B4357619
theorem B1936719 : Blo 1935435 1936719 := bstep (se 1 (by rfl) ⟨1452539, by rfl⟩ : syracuseStep 1936719 = 2905079) B2905079
theorem B2905085 : Blo 1935435 2905085 := bbase (se 3 (by rfl) ⟨544703, by rfl⟩ : syracuseStep 2905085 = 1089407) (by norm_num)
theorem B1936723 : Blo 1935435 1936723 := bstep (se 1 (by rfl) ⟨1452542, by rfl⟩ : syracuseStep 1936723 = 2905085) B2905085
theorem B4357637 : Blo 1935435 4357637 := bbase (se 4 (by rfl) ⟨408528, by rfl⟩ : syracuseStep 4357637 = 817057) (by norm_num)
theorem B2905091 : Blo 1935435 2905091 := bstep (se 1 (by rfl) ⟨2178818, by rfl⟩ : syracuseStep 2905091 = 4357637) B4357637
theorem B1936727 : Blo 1935435 1936727 := bstep (se 1 (by rfl) ⟨1452545, by rfl⟩ : syracuseStep 1936727 = 2905091) B2905091
theorem B3676765 : Blo 1935435 3676765 := bbase (se 3 (by rfl) ⟨689393, by rfl⟩ : syracuseStep 3676765 = 1378787) (by norm_num)
theorem B4902353 : Blo 1935435 4902353 := bstep (se 2 (by rfl) ⟨1838382, by rfl⟩ : syracuseStep 4902353 = 3676765) B3676765
theorem B3268235 : Blo 1935435 3268235 := bstep (se 1 (by rfl) ⟨2451176, by rfl⟩ : syracuseStep 3268235 = 4902353) B4902353
theorem B2178823 : Blo 1935435 2178823 := bstep (se 1 (by rfl) ⟨1634117, by rfl⟩ : syracuseStep 2178823 = 3268235) B3268235
theorem B2905097 : Blo 1935435 2905097 := bstep (se 2 (by rfl) ⟨1089411, by rfl⟩ : syracuseStep 2905097 = 2178823) B2178823
theorem B1936731 : Blo 1935435 1936731 := bstep (se 1 (by rfl) ⟨1452548, by rfl⟩ : syracuseStep 1936731 = 2905097) B2905097
theorem B9804725 : Blo 1935435 9804725 := bbase (se 5 (by rfl) ⟨459596, by rfl⟩ : syracuseStep 9804725 = 919193) (by norm_num)
theorem B6536483 : Blo 1935435 6536483 := bstep (se 1 (by rfl) ⟨4902362, by rfl⟩ : syracuseStep 6536483 = 9804725) B9804725
theorem B4357655 : Blo 1935435 4357655 := bstep (se 1 (by rfl) ⟨3268241, by rfl⟩ : syracuseStep 4357655 = 6536483) B6536483
theorem B2905103 : Blo 1935435 2905103 := bstep (se 1 (by rfl) ⟨2178827, by rfl⟩ : syracuseStep 2905103 = 4357655) B4357655
theorem B1936735 : Blo 1935435 1936735 := bstep (se 1 (by rfl) ⟨1452551, by rfl⟩ : syracuseStep 1936735 = 2905103) B2905103
theorem B2905109 : Blo 1935435 2905109 := bbase (se 6 (by rfl) ⟨68088, by rfl⟩ : syracuseStep 2905109 = 136177) (by norm_num)
theorem B1936739 : Blo 1935435 1936739 := bstep (se 1 (by rfl) ⟨1452554, by rfl⟩ : syracuseStep 1936739 = 2905109) B2905109
theorem B3358045 : Blo 1935435 3358045 := bbase (se 3 (by rfl) ⟨629633, by rfl⟩ : syracuseStep 3358045 = 1259267) (by norm_num)
theorem B4477393 : Blo 1935435 4477393 := bstep (se 2 (by rfl) ⟨1679022, by rfl⟩ : syracuseStep 4477393 = 3358045) B3358045
theorem B5969857 : Blo 1935435 5969857 := bstep (se 2 (by rfl) ⟨2238696, by rfl⟩ : syracuseStep 5969857 = 4477393) B4477393
theorem B7959809 : Blo 1935435 7959809 := bstep (se 2 (by rfl) ⟨2984928, by rfl⟩ : syracuseStep 7959809 = 5969857) B5969857
theorem B5306539 : Blo 1935435 5306539 := bstep (se 1 (by rfl) ⟨3979904, by rfl⟩ : syracuseStep 5306539 = 7959809) B7959809
theorem B7075385 : Blo 1935435 7075385 := bstep (se 2 (by rfl) ⟨2653269, by rfl⟩ : syracuseStep 7075385 = 5306539) B5306539
theorem B75470773 : Blo 1935435 75470773 := bstep (se 5 (by rfl) ⟨3537692, by rfl⟩ : syracuseStep 75470773 = 7075385) B7075385
theorem B100627697 : Blo 1935435 100627697 := bstep (se 2 (by rfl) ⟨37735386, by rfl⟩ : syracuseStep 100627697 = 75470773) B75470773
theorem B268340525 : Blo 1935435 268340525 := bstep (se 3 (by rfl) ⟨50313848, by rfl⟩ : syracuseStep 268340525 = 100627697) B100627697
theorem B178893683 : Blo 1935435 178893683 := bstep (se 1 (by rfl) ⟨134170262, by rfl⟩ : syracuseStep 178893683 = 268340525) B268340525
theorem B119262455 : Blo 1935435 119262455 := bstep (se 1 (by rfl) ⟨89446841, by rfl⟩ : syracuseStep 119262455 = 178893683) B178893683
theorem B79508303 : Blo 1935435 79508303 := bstep (se 1 (by rfl) ⟨59631227, by rfl⟩ : syracuseStep 79508303 = 119262455) B119262455
theorem B53005535 : Blo 1935435 53005535 := bstep (se 1 (by rfl) ⟨39754151, by rfl⟩ : syracuseStep 53005535 = 79508303) B79508303
theorem B35337023 : Blo 1935435 35337023 := bstep (se 1 (by rfl) ⟨26502767, by rfl⟩ : syracuseStep 35337023 = 53005535) B53005535
theorem B23558015 : Blo 1935435 23558015 := bstep (se 1 (by rfl) ⟨17668511, by rfl⟩ : syracuseStep 23558015 = 35337023) B35337023
theorem B15705343 : Blo 1935435 15705343 := bstep (se 1 (by rfl) ⟨11779007, by rfl⟩ : syracuseStep 15705343 = 23558015) B23558015
theorem B20940457 : Blo 1935435 20940457 := bstep (se 2 (by rfl) ⟨7852671, by rfl⟩ : syracuseStep 20940457 = 15705343) B15705343
theorem B27920609 : Blo 1935435 27920609 := bstep (se 2 (by rfl) ⟨10470228, by rfl⟩ : syracuseStep 27920609 = 20940457) B20940457
theorem B18613739 : Blo 1935435 18613739 := bstep (se 1 (by rfl) ⟨13960304, by rfl⟩ : syracuseStep 18613739 = 27920609) B27920609
theorem B12409159 : Blo 1935435 12409159 := bstep (se 1 (by rfl) ⟨9306869, by rfl⟩ : syracuseStep 12409159 = 18613739) B18613739
theorem B16545545 : Blo 1935435 16545545 := bstep (se 2 (by rfl) ⟨6204579, by rfl⟩ : syracuseStep 16545545 = 12409159) B12409159
theorem B11030363 : Blo 1935435 11030363 := bstep (se 1 (by rfl) ⟨8272772, by rfl⟩ : syracuseStep 11030363 = 16545545) B16545545
theorem B7353575 : Blo 1935435 7353575 := bstep (se 1 (by rfl) ⟨5515181, by rfl⟩ : syracuseStep 7353575 = 11030363) B11030363
theorem B4902383 : Blo 1935435 4902383 := bstep (se 1 (by rfl) ⟨3676787, by rfl⟩ : syracuseStep 4902383 = 7353575) B7353575
theorem B3268255 : Blo 1935435 3268255 := bstep (se 1 (by rfl) ⟨2451191, by rfl⟩ : syracuseStep 3268255 = 4902383) B4902383
theorem B4357673 : Blo 1935435 4357673 := bstep (se 2 (by rfl) ⟨1634127, by rfl⟩ : syracuseStep 4357673 = 3268255) B3268255
theorem B2905115 : Blo 1935435 2905115 := bstep (se 1 (by rfl) ⟨2178836, by rfl⟩ : syracuseStep 2905115 = 4357673) B4357673
theorem B1936743 : Blo 1935435 1936743 := bstep (se 1 (by rfl) ⟨1452557, by rfl⟩ : syracuseStep 1936743 = 2905115) B2905115
theorem B2178841 : Blo 1935435 2178841 := bbase (se 2 (by rfl) ⟨817065, by rfl⟩ : syracuseStep 2178841 = 1634131) (by norm_num)
theorem B2905121 : Blo 1935435 2905121 := bstep (se 2 (by rfl) ⟨1089420, by rfl⟩ : syracuseStep 2905121 = 2178841) B2178841
theorem B1936747 : Blo 1935435 1936747 := bstep (se 1 (by rfl) ⟨1452560, by rfl⟩ : syracuseStep 1936747 = 2905121) B2905121
theorem B7353605 : Blo 1935435 7353605 := bbase (se 4 (by rfl) ⟨689400, by rfl⟩ : syracuseStep 7353605 = 1378801) (by norm_num)
theorem B4902403 : Blo 1935435 4902403 := bstep (se 1 (by rfl) ⟨3676802, by rfl⟩ : syracuseStep 4902403 = 7353605) B7353605
theorem B6536537 : Blo 1935435 6536537 := bstep (se 2 (by rfl) ⟨2451201, by rfl⟩ : syracuseStep 6536537 = 4902403) B4902403
theorem B4357691 : Blo 1935435 4357691 := bstep (se 1 (by rfl) ⟨3268268, by rfl⟩ : syracuseStep 4357691 = 6536537) B6536537
theorem B2905127 : Blo 1935435 2905127 := bstep (se 1 (by rfl) ⟨2178845, by rfl⟩ : syracuseStep 2905127 = 4357691) B4357691
theorem B1936751 : Blo 1935435 1936751 := bstep (se 1 (by rfl) ⟨1452563, by rfl⟩ : syracuseStep 1936751 = 2905127) B2905127
theorem B2905133 : Blo 1935435 2905133 := bbase (se 3 (by rfl) ⟨544712, by rfl⟩ : syracuseStep 2905133 = 1089425) (by norm_num)
theorem B1936755 : Blo 1935435 1936755 := bstep (se 1 (by rfl) ⟨1452566, by rfl⟩ : syracuseStep 1936755 = 2905133) B2905133
theorem B4357709 : Blo 1935435 4357709 := bbase (se 3 (by rfl) ⟨817070, by rfl⟩ : syracuseStep 4357709 = 1634141) (by norm_num)
theorem B2905139 : Blo 1935435 2905139 := bstep (se 1 (by rfl) ⟨2178854, by rfl⟩ : syracuseStep 2905139 = 4357709) B4357709
theorem B1936759 : Blo 1935435 1936759 := bstep (se 1 (by rfl) ⟨1452569, by rfl⟩ : syracuseStep 1936759 = 2905139) B2905139
theorem B2451217 : Blo 1935435 2451217 := bbase (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) (by norm_num)
theorem B3268289 : Blo 1935435 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B2178859 : Blo 1935435 2178859 := bstep (se 1 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 2178859 = 3268289) B3268289
theorem B2905145 : Blo 1935435 2905145 := bstep (se 2 (by rfl) ⟨1089429, by rfl⟩ : syracuseStep 2905145 = 2178859) B2178859
theorem B1936763 : Blo 1935435 1936763 := bstep (se 1 (by rfl) ⟨1452572, by rfl⟩ : syracuseStep 1936763 = 2905145) B2905145
theorem B4136437 : Blo 1935435 4136437 := bbase (se 5 (by rfl) ⟨193895, by rfl⟩ : syracuseStep 4136437 = 387791) (by norm_num)
theorem B22060997 : Blo 1935435 22060997 := bstep (se 4 (by rfl) ⟨2068218, by rfl⟩ : syracuseStep 22060997 = 4136437) B4136437
theorem B14707331 : Blo 1935435 14707331 := bstep (se 1 (by rfl) ⟨11030498, by rfl⟩ : syracuseStep 14707331 = 22060997) B22060997
theorem B9804887 : Blo 1935435 9804887 := bstep (se 1 (by rfl) ⟨7353665, by rfl⟩ : syracuseStep 9804887 = 14707331) B14707331
theorem B6536591 : Blo 1935435 6536591 := bstep (se 1 (by rfl) ⟨4902443, by rfl⟩ : syracuseStep 6536591 = 9804887) B9804887
theorem B4357727 : Blo 1935435 4357727 := bstep (se 1 (by rfl) ⟨3268295, by rfl⟩ : syracuseStep 4357727 = 6536591) B6536591
theorem B2905151 : Blo 1935435 2905151 := bstep (se 1 (by rfl) ⟨2178863, by rfl⟩ : syracuseStep 2905151 = 4357727) B4357727
theorem B1936767 : Blo 1935435 1936767 := bstep (se 1 (by rfl) ⟨1452575, by rfl⟩ : syracuseStep 1936767 = 2905151) B2905151
theorem B2905157 : Blo 1935435 2905157 := bbase (se 4 (by rfl) ⟨272358, by rfl⟩ : syracuseStep 2905157 = 544717) (by norm_num)
theorem B1936771 : Blo 1935435 1936771 := bstep (se 1 (by rfl) ⟨1452578, by rfl⟩ : syracuseStep 1936771 = 2905157) B2905157
theorem B3268309 : Blo 1935435 3268309 := bbase (se 7 (by rfl) ⟨38300, by rfl⟩ : syracuseStep 3268309 = 76601) (by norm_num)
theorem B4357745 : Blo 1935435 4357745 := bstep (se 2 (by rfl) ⟨1634154, by rfl⟩ : syracuseStep 4357745 = 3268309) B3268309
theorem B2905163 : Blo 1935435 2905163 := bstep (se 1 (by rfl) ⟨2178872, by rfl⟩ : syracuseStep 2905163 = 4357745) B4357745
theorem B1936775 : Blo 1935435 1936775 := bstep (se 1 (by rfl) ⟨1452581, by rfl⟩ : syracuseStep 1936775 = 2905163) B2905163
theorem B2178877 : Blo 1935435 2178877 := bbase (se 3 (by rfl) ⟨408539, by rfl⟩ : syracuseStep 2178877 = 817079) (by norm_num)
theorem B2905169 : Blo 1935435 2905169 := bstep (se 2 (by rfl) ⟨1089438, by rfl⟩ : syracuseStep 2905169 = 2178877) B2178877
theorem B1936779 : Blo 1935435 1936779 := bstep (se 1 (by rfl) ⟨1452584, by rfl⟩ : syracuseStep 1936779 = 2905169) B2905169
theorem B6536645 : Blo 1935435 6536645 := bbase (se 4 (by rfl) ⟨612810, by rfl⟩ : syracuseStep 6536645 = 1225621) (by norm_num)
theorem B4357763 : Blo 1935435 4357763 := bstep (se 1 (by rfl) ⟨3268322, by rfl⟩ : syracuseStep 4357763 = 6536645) B6536645
theorem B2905175 : Blo 1935435 2905175 := bstep (se 1 (by rfl) ⟨2178881, by rfl⟩ : syracuseStep 2905175 = 4357763) B4357763
theorem B1936783 : Blo 1935435 1936783 := bstep (se 1 (by rfl) ⟨1452587, by rfl⟩ : syracuseStep 1936783 = 2905175) B2905175
theorem B2905181 : Blo 1935435 2905181 := bbase (se 3 (by rfl) ⟨544721, by rfl⟩ : syracuseStep 2905181 = 1089443) (by norm_num)
theorem B1936787 : Blo 1935435 1936787 := bstep (se 1 (by rfl) ⟨1452590, by rfl⟩ : syracuseStep 1936787 = 2905181) B2905181
theorem B4357781 : Blo 1935435 4357781 := bbase (se 6 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 4357781 = 204271) (by norm_num)
theorem B2905187 : Blo 1935435 2905187 := bstep (se 1 (by rfl) ⟨2178890, by rfl⟩ : syracuseStep 2905187 = 4357781) B4357781
theorem B1936791 : Blo 1935435 1936791 := bstep (se 1 (by rfl) ⟨1452593, by rfl⟩ : syracuseStep 1936791 = 2905187) B2905187
theorem B2068249 : Blo 1935435 2068249 := bbase (se 2 (by rfl) ⟨775593, by rfl⟩ : syracuseStep 2068249 = 1551187) (by norm_num)
theorem B2757665 : Blo 1935435 2757665 := bstep (se 2 (by rfl) ⟨1034124, by rfl⟩ : syracuseStep 2757665 = 2068249) B2068249
theorem B7353773 : Blo 1935435 7353773 := bstep (se 3 (by rfl) ⟨1378832, by rfl⟩ : syracuseStep 7353773 = 2757665) B2757665
theorem B4902515 : Blo 1935435 4902515 := bstep (se 1 (by rfl) ⟨3676886, by rfl⟩ : syracuseStep 4902515 = 7353773) B7353773
theorem B3268343 : Blo 1935435 3268343 := bstep (se 1 (by rfl) ⟨2451257, by rfl⟩ : syracuseStep 3268343 = 4902515) B4902515
theorem B2178895 : Blo 1935435 2178895 := bstep (se 1 (by rfl) ⟨1634171, by rfl⟩ : syracuseStep 2178895 = 3268343) B3268343
theorem B2905193 : Blo 1935435 2905193 := bstep (se 2 (by rfl) ⟨1089447, by rfl⟩ : syracuseStep 2905193 = 2178895) B2178895
theorem B1936795 : Blo 1935435 1936795 := bstep (se 1 (by rfl) ⟨1452596, by rfl⟩ : syracuseStep 1936795 = 2905193) B2905193
theorem B1963225 : Blo 1935435 1963225 := bbase (se 2 (by rfl) ⟨736209, by rfl⟩ : syracuseStep 1963225 = 1472419) (by norm_num)
theorem B2617633 : Blo 1935435 2617633 := bstep (se 2 (by rfl) ⟨981612, by rfl⟩ : syracuseStep 2617633 = 1963225) B1963225
theorem B3490177 : Blo 1935435 3490177 := bstep (se 2 (by rfl) ⟨1308816, by rfl⟩ : syracuseStep 3490177 = 2617633) B2617633
theorem B4653569 : Blo 1935435 4653569 := bstep (se 2 (by rfl) ⟨1745088, by rfl⟩ : syracuseStep 4653569 = 3490177) B3490177
theorem B12409517 : Blo 1935435 12409517 := bstep (se 3 (by rfl) ⟨2326784, by rfl⟩ : syracuseStep 12409517 = 4653569) B4653569
theorem B8273011 : Blo 1935435 8273011 := bstep (se 1 (by rfl) ⟨6204758, by rfl⟩ : syracuseStep 8273011 = 12409517) B12409517
theorem B11030681 : Blo 1935435 11030681 := bstep (se 2 (by rfl) ⟨4136505, by rfl⟩ : syracuseStep 11030681 = 8273011) B8273011
theorem B7353787 : Blo 1935435 7353787 := bstep (se 1 (by rfl) ⟨5515340, by rfl⟩ : syracuseStep 7353787 = 11030681) B11030681
theorem B9805049 : Blo 1935435 9805049 := bstep (se 2 (by rfl) ⟨3676893, by rfl⟩ : syracuseStep 9805049 = 7353787) B7353787
theorem B6536699 : Blo 1935435 6536699 := bstep (se 1 (by rfl) ⟨4902524, by rfl⟩ : syracuseStep 6536699 = 9805049) B9805049
theorem B4357799 : Blo 1935435 4357799 := bstep (se 1 (by rfl) ⟨3268349, by rfl⟩ : syracuseStep 4357799 = 6536699) B6536699
theorem B2905199 : Blo 1935435 2905199 := bstep (se 1 (by rfl) ⟨2178899, by rfl⟩ : syracuseStep 2905199 = 4357799) B4357799
theorem B1936799 : Blo 1935435 1936799 := bstep (se 1 (by rfl) ⟨1452599, by rfl⟩ : syracuseStep 1936799 = 2905199) B2905199
theorem B2905205 : Blo 1935435 2905205 := bbase (se 5 (by rfl) ⟨136181, by rfl⟩ : syracuseStep 2905205 = 272363) (by norm_num)
theorem B1936803 : Blo 1935435 1936803 := bstep (se 1 (by rfl) ⟨1452602, by rfl⟩ : syracuseStep 1936803 = 2905205) B2905205
theorem B3676909 : Blo 1935435 3676909 := bbase (se 3 (by rfl) ⟨689420, by rfl⟩ : syracuseStep 3676909 = 1378841) (by norm_num)
theorem B4902545 : Blo 1935435 4902545 := bstep (se 2 (by rfl) ⟨1838454, by rfl⟩ : syracuseStep 4902545 = 3676909) B3676909
theorem B3268363 : Blo 1935435 3268363 := bstep (se 1 (by rfl) ⟨2451272, by rfl⟩ : syracuseStep 3268363 = 4902545) B4902545
theorem B4357817 : Blo 1935435 4357817 := bstep (se 2 (by rfl) ⟨1634181, by rfl⟩ : syracuseStep 4357817 = 3268363) B3268363
theorem B2905211 : Blo 1935435 2905211 := bstep (se 1 (by rfl) ⟨2178908, by rfl⟩ : syracuseStep 2905211 = 4357817) B4357817
theorem B1936807 : Blo 1935435 1936807 := bstep (se 1 (by rfl) ⟨1452605, by rfl⟩ : syracuseStep 1936807 = 2905211) B2905211
theorem B2178913 : Blo 1935435 2178913 := bbase (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) (by norm_num)
theorem B2905217 : Blo 1935435 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B1936811 : Blo 1935435 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B4902565 : Blo 1935435 4902565 := bbase (se 4 (by rfl) ⟨459615, by rfl⟩ : syracuseStep 4902565 = 919231) (by norm_num)
theorem B6536753 : Blo 1935435 6536753 := bstep (se 2 (by rfl) ⟨2451282, by rfl⟩ : syracuseStep 6536753 = 4902565) B4902565
theorem B4357835 : Blo 1935435 4357835 := bstep (se 1 (by rfl) ⟨3268376, by rfl⟩ : syracuseStep 4357835 = 6536753) B6536753
theorem B2905223 : Blo 1935435 2905223 := bstep (se 1 (by rfl) ⟨2178917, by rfl⟩ : syracuseStep 2905223 = 4357835) B4357835
theorem B1936815 : Blo 1935435 1936815 := bstep (se 1 (by rfl) ⟨1452611, by rfl⟩ : syracuseStep 1936815 = 2905223) B2905223
theorem B2905229 : Blo 1935435 2905229 := bbase (se 3 (by rfl) ⟨544730, by rfl⟩ : syracuseStep 2905229 = 1089461) (by norm_num)
theorem B1936819 : Blo 1935435 1936819 := bstep (se 1 (by rfl) ⟨1452614, by rfl⟩ : syracuseStep 1936819 = 2905229) B2905229
theorem B4357853 : Blo 1935435 4357853 := bbase (se 3 (by rfl) ⟨817097, by rfl⟩ : syracuseStep 4357853 = 1634195) (by norm_num)
theorem B2905235 : Blo 1935435 2905235 := bstep (se 1 (by rfl) ⟨2178926, by rfl⟩ : syracuseStep 2905235 = 4357853) B4357853
theorem B1936823 : Blo 1935435 1936823 := bstep (se 1 (by rfl) ⟨1452617, by rfl⟩ : syracuseStep 1936823 = 2905235) B2905235
theorem B3268397 : Blo 1935435 3268397 := bbase (se 3 (by rfl) ⟨612824, by rfl⟩ : syracuseStep 3268397 = 1225649) (by norm_num)
theorem B2178931 : Blo 1935435 2178931 := bstep (se 1 (by rfl) ⟨1634198, by rfl⟩ : syracuseStep 2178931 = 3268397) B3268397
theorem B2905241 : Blo 1935435 2905241 := bstep (se 2 (by rfl) ⟨1089465, by rfl⟩ : syracuseStep 2905241 = 2178931) B2178931
theorem B1936827 : Blo 1935435 1936827 := bstep (se 1 (by rfl) ⟨1452620, by rfl⟩ : syracuseStep 1936827 = 2905241) B2905241
theorem B2358569 : Blo 1935435 2358569 := bbase (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) (by norm_num)
theorem B6289517 : Blo 1935435 6289517 := bstep (se 3 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 6289517 = 2358569) B2358569
theorem B4193011 : Blo 1935435 4193011 := bstep (se 1 (by rfl) ⟨3144758, by rfl⟩ : syracuseStep 4193011 = 6289517) B6289517
theorem B22362725 : Blo 1935435 22362725 := bstep (se 4 (by rfl) ⟨2096505, by rfl⟩ : syracuseStep 22362725 = 4193011) B4193011
theorem B14908483 : Blo 1935435 14908483 := bstep (se 1 (by rfl) ⟨11181362, by rfl⟩ : syracuseStep 14908483 = 22362725) B22362725
theorem B19877977 : Blo 1935435 19877977 := bstep (se 2 (by rfl) ⟨7454241, by rfl⟩ : syracuseStep 19877977 = 14908483) B14908483
theorem B26503969 : Blo 1935435 26503969 := bstep (se 2 (by rfl) ⟨9938988, by rfl⟩ : syracuseStep 26503969 = 19877977) B19877977
theorem B35338625 : Blo 1935435 35338625 := bstep (se 2 (by rfl) ⟨13251984, by rfl⟩ : syracuseStep 35338625 = 26503969) B26503969
theorem B23559083 : Blo 1935435 23559083 := bstep (se 1 (by rfl) ⟨17669312, by rfl⟩ : syracuseStep 23559083 = 35338625) B35338625
theorem B15706055 : Blo 1935435 15706055 := bstep (se 1 (by rfl) ⟨11779541, by rfl⟩ : syracuseStep 15706055 = 23559083) B23559083
theorem B10470703 : Blo 1935435 10470703 := bstep (se 1 (by rfl) ⟨7853027, by rfl⟩ : syracuseStep 10470703 = 15706055) B15706055
theorem B13960937 : Blo 1935435 13960937 := bstep (se 2 (by rfl) ⟨5235351, by rfl⟩ : syracuseStep 13960937 = 10470703) B10470703
theorem B37229165 : Blo 1935435 37229165 := bstep (se 3 (by rfl) ⟨6980468, by rfl⟩ : syracuseStep 37229165 = 13960937) B13960937
theorem B24819443 : Blo 1935435 24819443 := bstep (se 1 (by rfl) ⟨18614582, by rfl⟩ : syracuseStep 24819443 = 37229165) B37229165
theorem B16546295 : Blo 1935435 16546295 := bstep (se 1 (by rfl) ⟨12409721, by rfl⟩ : syracuseStep 16546295 = 24819443) B24819443
theorem B11030863 : Blo 1935435 11030863 := bstep (se 1 (by rfl) ⟨8273147, by rfl⟩ : syracuseStep 11030863 = 16546295) B16546295
theorem B14707817 : Blo 1935435 14707817 := bstep (se 2 (by rfl) ⟨5515431, by rfl⟩ : syracuseStep 14707817 = 11030863) B11030863
theorem B9805211 : Blo 1935435 9805211 := bstep (se 1 (by rfl) ⟨7353908, by rfl⟩ : syracuseStep 9805211 = 14707817) B14707817
theorem B6536807 : Blo 1935435 6536807 := bstep (se 1 (by rfl) ⟨4902605, by rfl⟩ : syracuseStep 6536807 = 9805211) B9805211
theorem B4357871 : Blo 1935435 4357871 := bstep (se 1 (by rfl) ⟨3268403, by rfl⟩ : syracuseStep 4357871 = 6536807) B6536807
theorem B2905247 : Blo 1935435 2905247 := bstep (se 1 (by rfl) ⟨2178935, by rfl⟩ : syracuseStep 2905247 = 4357871) B4357871
theorem B1936831 : Blo 1935435 1936831 := bstep (se 1 (by rfl) ⟨1452623, by rfl⟩ : syracuseStep 1936831 = 2905247) B2905247
theorem B2905253 : Blo 1935435 2905253 := bbase (se 4 (by rfl) ⟨272367, by rfl⟩ : syracuseStep 2905253 = 544735) (by norm_num)
theorem B1936835 : Blo 1935435 1936835 := bstep (se 1 (by rfl) ⟨1452626, by rfl⟩ : syracuseStep 1936835 = 2905253) B2905253
theorem B2451313 : Blo 1935435 2451313 := bbase (se 2 (by rfl) ⟨919242, by rfl⟩ : syracuseStep 2451313 = 1838485) (by norm_num)
theorem B3268417 : Blo 1935435 3268417 := bstep (se 2 (by rfl) ⟨1225656, by rfl⟩ : syracuseStep 3268417 = 2451313) B2451313
theorem B4357889 : Blo 1935435 4357889 := bstep (se 2 (by rfl) ⟨1634208, by rfl⟩ : syracuseStep 4357889 = 3268417) B3268417
theorem B2905259 : Blo 1935435 2905259 := bstep (se 1 (by rfl) ⟨2178944, by rfl⟩ : syracuseStep 2905259 = 4357889) B4357889
theorem B1936839 : Blo 1935435 1936839 := bstep (se 1 (by rfl) ⟨1452629, by rfl⟩ : syracuseStep 1936839 = 2905259) B2905259
theorem B2178949 : Blo 1935435 2178949 := bbase (se 4 (by rfl) ⟨204276, by rfl⟩ : syracuseStep 2178949 = 408553) (by norm_num)
theorem B2905265 : Blo 1935435 2905265 := bstep (se 2 (by rfl) ⟨1089474, by rfl⟩ : syracuseStep 2905265 = 2178949) B2178949
theorem B1936843 : Blo 1935435 1936843 := bstep (se 1 (by rfl) ⟨1452632, by rfl⟩ : syracuseStep 1936843 = 2905265) B2905265
theorem B3926549 : Blo 1935435 3926549 := bbase (se 6 (by rfl) ⟨92028, by rfl⟩ : syracuseStep 3926549 = 184057) (by norm_num)
theorem B2617699 : Blo 1935435 2617699 := bstep (se 1 (by rfl) ⟨1963274, by rfl⟩ : syracuseStep 2617699 = 3926549) B3926549
theorem B3490265 : Blo 1935435 3490265 := bstep (se 2 (by rfl) ⟨1308849, by rfl⟩ : syracuseStep 3490265 = 2617699) B2617699
theorem B2326843 : Blo 1935435 2326843 := bstep (se 1 (by rfl) ⟨1745132, by rfl⟩ : syracuseStep 2326843 = 3490265) B3490265
theorem B3102457 : Blo 1935435 3102457 := bstep (se 2 (by rfl) ⟨1163421, by rfl⟩ : syracuseStep 3102457 = 2326843) B2326843
theorem B4136609 : Blo 1935435 4136609 := bstep (se 2 (by rfl) ⟨1551228, by rfl⟩ : syracuseStep 4136609 = 3102457) B3102457
theorem B2757739 : Blo 1935435 2757739 := bstep (se 1 (by rfl) ⟨2068304, by rfl⟩ : syracuseStep 2757739 = 4136609) B4136609
theorem B3676985 : Blo 1935435 3676985 := bstep (se 2 (by rfl) ⟨1378869, by rfl⟩ : syracuseStep 3676985 = 2757739) B2757739
theorem B2451323 : Blo 1935435 2451323 := bstep (se 1 (by rfl) ⟨1838492, by rfl⟩ : syracuseStep 2451323 = 3676985) B3676985
theorem B6536861 : Blo 1935435 6536861 := bstep (se 3 (by rfl) ⟨1225661, by rfl⟩ : syracuseStep 6536861 = 2451323) B2451323
theorem B4357907 : Blo 1935435 4357907 := bstep (se 1 (by rfl) ⟨3268430, by rfl⟩ : syracuseStep 4357907 = 6536861) B6536861
theorem B2905271 : Blo 1935435 2905271 := bstep (se 1 (by rfl) ⟨2178953, by rfl⟩ : syracuseStep 2905271 = 4357907) B4357907
theorem B1936847 : Blo 1935435 1936847 := bstep (se 1 (by rfl) ⟨1452635, by rfl⟩ : syracuseStep 1936847 = 2905271) B2905271
theorem B2905277 : Blo 1935435 2905277 := bbase (se 3 (by rfl) ⟨544739, by rfl⟩ : syracuseStep 2905277 = 1089479) (by norm_num)
theorem B1936851 : Blo 1935435 1936851 := bstep (se 1 (by rfl) ⟨1452638, by rfl⟩ : syracuseStep 1936851 = 2905277) B2905277
theorem B4357925 : Blo 1935435 4357925 := bbase (se 4 (by rfl) ⟨408555, by rfl⟩ : syracuseStep 4357925 = 817111) (by norm_num)
theorem B2905283 : Blo 1935435 2905283 := bstep (se 1 (by rfl) ⟨2178962, by rfl⟩ : syracuseStep 2905283 = 4357925) B4357925
theorem B1936855 : Blo 1935435 1936855 := bstep (se 1 (by rfl) ⟨1452641, by rfl⟩ : syracuseStep 1936855 = 2905283) B2905283
theorem B4902677 : Blo 1935435 4902677 := bbase (se 6 (by rfl) ⟨114906, by rfl⟩ : syracuseStep 4902677 = 229813) (by norm_num)
theorem B3268451 : Blo 1935435 3268451 := bstep (se 1 (by rfl) ⟨2451338, by rfl⟩ : syracuseStep 3268451 = 4902677) B4902677
theorem B2178967 : Blo 1935435 2178967 := bstep (se 1 (by rfl) ⟨1634225, by rfl⟩ : syracuseStep 2178967 = 3268451) B3268451
theorem B2905289 : Blo 1935435 2905289 := bstep (se 2 (by rfl) ⟨1089483, by rfl⟩ : syracuseStep 2905289 = 2178967) B2178967
theorem B1936859 : Blo 1935435 1936859 := bstep (se 1 (by rfl) ⟨1452644, by rfl⟩ : syracuseStep 1936859 = 2905289) B2905289
theorem B8273285 : Blo 1935435 8273285 := bbase (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) (by norm_num)
theorem B5515523 : Blo 1935435 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B3677015 : Blo 1935435 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B9805373 : Blo 1935435 9805373 := bstep (se 3 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 9805373 = 3677015) B3677015
theorem B6536915 : Blo 1935435 6536915 := bstep (se 1 (by rfl) ⟨4902686, by rfl⟩ : syracuseStep 6536915 = 9805373) B9805373
theorem B4357943 : Blo 1935435 4357943 := bstep (se 1 (by rfl) ⟨3268457, by rfl⟩ : syracuseStep 4357943 = 6536915) B6536915
theorem B2905295 : Blo 1935435 2905295 := bstep (se 1 (by rfl) ⟨2178971, by rfl⟩ : syracuseStep 2905295 = 4357943) B4357943
theorem B1936863 : Blo 1935435 1936863 := bstep (se 1 (by rfl) ⟨1452647, by rfl⟩ : syracuseStep 1936863 = 2905295) B2905295
theorem B2905301 : Blo 1935435 2905301 := bbase (se 7 (by rfl) ⟨34046, by rfl⟩ : syracuseStep 2905301 = 68093) (by norm_num)
theorem B1936867 : Blo 1935435 1936867 := bstep (se 1 (by rfl) ⟨1452650, by rfl⟩ : syracuseStep 1936867 = 2905301) B2905301
theorem B2757773 : Blo 1935435 2757773 := bbase (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) (by norm_num)
theorem B7354061 : Blo 1935435 7354061 := bstep (se 3 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 7354061 = 2757773) B2757773
theorem B4902707 : Blo 1935435 4902707 := bstep (se 1 (by rfl) ⟨3677030, by rfl⟩ : syracuseStep 4902707 = 7354061) B7354061
theorem B3268471 : Blo 1935435 3268471 := bstep (se 1 (by rfl) ⟨2451353, by rfl⟩ : syracuseStep 3268471 = 4902707) B4902707
theorem B4357961 : Blo 1935435 4357961 := bstep (se 2 (by rfl) ⟨1634235, by rfl⟩ : syracuseStep 4357961 = 3268471) B3268471
theorem B2905307 : Blo 1935435 2905307 := bstep (se 1 (by rfl) ⟨2178980, by rfl⟩ : syracuseStep 2905307 = 4357961) B4357961
theorem B1936871 : Blo 1935435 1936871 := bstep (se 1 (by rfl) ⟨1452653, by rfl⟩ : syracuseStep 1936871 = 2905307) B2905307
theorem B2178985 : Blo 1935435 2178985 := bbase (se 2 (by rfl) ⟨817119, by rfl⟩ : syracuseStep 2178985 = 1634239) (by norm_num)
theorem B2905313 : Blo 1935435 2905313 := bstep (se 2 (by rfl) ⟨1089492, by rfl⟩ : syracuseStep 2905313 = 2178985) B2178985
theorem B1936875 : Blo 1935435 1936875 := bstep (se 1 (by rfl) ⟨1452656, by rfl⟩ : syracuseStep 1936875 = 2905313) B2905313
theorem B2617741 : Blo 1935435 2617741 := bbase (se 3 (by rfl) ⟨490826, by rfl⟩ : syracuseStep 2617741 = 981653) (by norm_num)
theorem B13961285 : Blo 1935435 13961285 := bstep (se 4 (by rfl) ⟨1308870, by rfl⟩ : syracuseStep 13961285 = 2617741) B2617741
theorem B9307523 : Blo 1935435 9307523 := bstep (se 1 (by rfl) ⟨6980642, by rfl⟩ : syracuseStep 9307523 = 13961285) B13961285
theorem B6205015 : Blo 1935435 6205015 := bstep (se 1 (by rfl) ⟨4653761, by rfl⟩ : syracuseStep 6205015 = 9307523) B9307523
theorem B8273353 : Blo 1935435 8273353 := bstep (se 2 (by rfl) ⟨3102507, by rfl⟩ : syracuseStep 8273353 = 6205015) B6205015
theorem B11031137 : Blo 1935435 11031137 := bstep (se 2 (by rfl) ⟨4136676, by rfl⟩ : syracuseStep 11031137 = 8273353) B8273353
theorem B7354091 : Blo 1935435 7354091 := bstep (se 1 (by rfl) ⟨5515568, by rfl⟩ : syracuseStep 7354091 = 11031137) B11031137
theorem B4902727 : Blo 1935435 4902727 := bstep (se 1 (by rfl) ⟨3677045, by rfl⟩ : syracuseStep 4902727 = 7354091) B7354091
theorem B6536969 : Blo 1935435 6536969 := bstep (se 2 (by rfl) ⟨2451363, by rfl⟩ : syracuseStep 6536969 = 4902727) B4902727
theorem B4357979 : Blo 1935435 4357979 := bstep (se 1 (by rfl) ⟨3268484, by rfl⟩ : syracuseStep 4357979 = 6536969) B6536969
theorem B2905319 : Blo 1935435 2905319 := bstep (se 1 (by rfl) ⟨2178989, by rfl⟩ : syracuseStep 2905319 = 4357979) B4357979
theorem B1936879 : Blo 1935435 1936879 := bstep (se 1 (by rfl) ⟨1452659, by rfl⟩ : syracuseStep 1936879 = 2905319) B2905319
theorem B2905325 : Blo 1935435 2905325 := bbase (se 3 (by rfl) ⟨544748, by rfl⟩ : syracuseStep 2905325 = 1089497) (by norm_num)
theorem B1936883 : Blo 1935435 1936883 := bstep (se 1 (by rfl) ⟨1452662, by rfl⟩ : syracuseStep 1936883 = 2905325) B2905325
theorem B4357997 : Blo 1935435 4357997 := bbase (se 3 (by rfl) ⟨817124, by rfl⟩ : syracuseStep 4357997 = 1634249) (by norm_num)
theorem B2905331 : Blo 1935435 2905331 := bstep (se 1 (by rfl) ⟨2178998, by rfl⟩ : syracuseStep 2905331 = 4357997) B4357997
theorem B1936887 : Blo 1935435 1936887 := bstep (se 1 (by rfl) ⟨1452665, by rfl⟩ : syracuseStep 1936887 = 2905331) B2905331
theorem B3677069 : Blo 1935435 3677069 := bbase (se 3 (by rfl) ⟨689450, by rfl⟩ : syracuseStep 3677069 = 1378901) (by norm_num)
theorem B2451379 : Blo 1935435 2451379 := bstep (se 1 (by rfl) ⟨1838534, by rfl⟩ : syracuseStep 2451379 = 3677069) B3677069
theorem B3268505 : Blo 1935435 3268505 := bstep (se 2 (by rfl) ⟨1225689, by rfl⟩ : syracuseStep 3268505 = 2451379) B2451379
theorem B2179003 : Blo 1935435 2179003 := bstep (se 1 (by rfl) ⟨1634252, by rfl⟩ : syracuseStep 2179003 = 3268505) B3268505
theorem B2905337 : Blo 1935435 2905337 := bstep (se 2 (by rfl) ⟨1089501, by rfl⟩ : syracuseStep 2905337 = 2179003) B2179003
theorem B1936891 : Blo 1935435 1936891 := bstep (se 1 (by rfl) ⟨1452668, by rfl⟩ : syracuseStep 1936891 = 2905337) B2905337
theorem B23881301 : Blo 1935435 23881301 := bbase (se 8 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 23881301 = 279859) (by norm_num)
theorem B15920867 : Blo 1935435 15920867 := bstep (se 1 (by rfl) ⟨11940650, by rfl⟩ : syracuseStep 15920867 = 23881301) B23881301
theorem B10613911 : Blo 1935435 10613911 := bstep (se 1 (by rfl) ⟨7960433, by rfl⟩ : syracuseStep 10613911 = 15920867) B15920867
theorem B14151881 : Blo 1935435 14151881 := bstep (se 2 (by rfl) ⟨5306955, by rfl⟩ : syracuseStep 14151881 = 10613911) B10613911
theorem B37738349 : Blo 1935435 37738349 := bstep (se 3 (by rfl) ⟨7075940, by rfl⟩ : syracuseStep 37738349 = 14151881) B14151881
theorem B25158899 : Blo 1935435 25158899 := bstep (se 1 (by rfl) ⟨18869174, by rfl⟩ : syracuseStep 25158899 = 37738349) B37738349
theorem B16772599 : Blo 1935435 16772599 := bstep (se 1 (by rfl) ⟨12579449, by rfl⟩ : syracuseStep 16772599 = 25158899) B25158899
theorem B22363465 : Blo 1935435 22363465 := bstep (se 2 (by rfl) ⟨8386299, by rfl⟩ : syracuseStep 22363465 = 16772599) B16772599
theorem B29817953 : Blo 1935435 29817953 := bstep (se 2 (by rfl) ⟨11181732, by rfl⟩ : syracuseStep 29817953 = 22363465) B22363465
theorem B19878635 : Blo 1935435 19878635 := bstep (se 1 (by rfl) ⟨14908976, by rfl⟩ : syracuseStep 19878635 = 29817953) B29817953
theorem B13252423 : Blo 1935435 13252423 := bstep (se 1 (by rfl) ⟨9939317, by rfl⟩ : syracuseStep 13252423 = 19878635) B19878635
theorem B17669897 : Blo 1935435 17669897 := bstep (se 2 (by rfl) ⟨6626211, by rfl⟩ : syracuseStep 17669897 = 13252423) B13252423
theorem B11779931 : Blo 1935435 11779931 := bstep (se 1 (by rfl) ⟨8834948, by rfl⟩ : syracuseStep 11779931 = 17669897) B17669897
theorem B7853287 : Blo 1935435 7853287 := bstep (se 1 (by rfl) ⟨5889965, by rfl⟩ : syracuseStep 7853287 = 11779931) B11779931
theorem B10471049 : Blo 1935435 10471049 := bstep (se 2 (by rfl) ⟨3926643, by rfl⟩ : syracuseStep 10471049 = 7853287) B7853287
theorem B6980699 : Blo 1935435 6980699 := bstep (se 1 (by rfl) ⟨5235524, by rfl⟩ : syracuseStep 6980699 = 10471049) B10471049
theorem B18615197 : Blo 1935435 18615197 := bstep (se 3 (by rfl) ⟨3490349, by rfl⟩ : syracuseStep 18615197 = 6980699) B6980699
theorem B49640525 : Blo 1935435 49640525 := bstep (se 3 (by rfl) ⟨9307598, by rfl⟩ : syracuseStep 49640525 = 18615197) B18615197
theorem B33093683 : Blo 1935435 33093683 := bstep (se 1 (by rfl) ⟨24820262, by rfl⟩ : syracuseStep 33093683 = 49640525) B49640525
theorem B22062455 : Blo 1935435 22062455 := bstep (se 1 (by rfl) ⟨16546841, by rfl⟩ : syracuseStep 22062455 = 33093683) B33093683
theorem B14708303 : Blo 1935435 14708303 := bstep (se 1 (by rfl) ⟨11031227, by rfl⟩ : syracuseStep 14708303 = 22062455) B22062455
theorem B9805535 : Blo 1935435 9805535 := bstep (se 1 (by rfl) ⟨7354151, by rfl⟩ : syracuseStep 9805535 = 14708303) B14708303
theorem B6537023 : Blo 1935435 6537023 := bstep (se 1 (by rfl) ⟨4902767, by rfl⟩ : syracuseStep 6537023 = 9805535) B9805535
theorem B4358015 : Blo 1935435 4358015 := bstep (se 1 (by rfl) ⟨3268511, by rfl⟩ : syracuseStep 4358015 = 6537023) B6537023
theorem B2905343 : Blo 1935435 2905343 := bstep (se 1 (by rfl) ⟨2179007, by rfl⟩ : syracuseStep 2905343 = 4358015) B4358015
theorem B1936895 : Blo 1935435 1936895 := bstep (se 1 (by rfl) ⟨1452671, by rfl⟩ : syracuseStep 1936895 = 2905343) B2905343
theorem B2905349 : Blo 1935435 2905349 := bbase (se 4 (by rfl) ⟨272376, by rfl⟩ : syracuseStep 2905349 = 544753) (by norm_num)
theorem B1936899 : Blo 1935435 1936899 := bstep (se 1 (by rfl) ⟨1452674, by rfl⟩ : syracuseStep 1936899 = 2905349) B2905349
theorem B3268525 : Blo 1935435 3268525 := bbase (se 3 (by rfl) ⟨612848, by rfl⟩ : syracuseStep 3268525 = 1225697) (by norm_num)
theorem B4358033 : Blo 1935435 4358033 := bstep (se 2 (by rfl) ⟨1634262, by rfl⟩ : syracuseStep 4358033 = 3268525) B3268525
theorem B2905355 : Blo 1935435 2905355 := bstep (se 1 (by rfl) ⟨2179016, by rfl⟩ : syracuseStep 2905355 = 4358033) B4358033
theorem B1936903 : Blo 1935435 1936903 := bstep (se 1 (by rfl) ⟨1452677, by rfl⟩ : syracuseStep 1936903 = 2905355) B2905355
theorem B2179021 : Blo 1935435 2179021 := bbase (se 3 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 2179021 = 817133) (by norm_num)
theorem B2905361 : Blo 1935435 2905361 := bstep (se 2 (by rfl) ⟨1089510, by rfl⟩ : syracuseStep 2905361 = 2179021) B2179021
theorem B1936907 : Blo 1935435 1936907 := bstep (se 1 (by rfl) ⟨1452680, by rfl⟩ : syracuseStep 1936907 = 2905361) B2905361
theorem B6537077 : Blo 1935435 6537077 := bbase (se 5 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 6537077 = 612851) (by norm_num)
theorem B4358051 : Blo 1935435 4358051 := bstep (se 1 (by rfl) ⟨3268538, by rfl⟩ : syracuseStep 4358051 = 6537077) B6537077
theorem B2905367 : Blo 1935435 2905367 := bstep (se 1 (by rfl) ⟨2179025, by rfl⟩ : syracuseStep 2905367 = 4358051) B4358051
theorem B1936911 : Blo 1935435 1936911 := bstep (se 1 (by rfl) ⟨1452683, by rfl⟩ : syracuseStep 1936911 = 2905367) B2905367
theorem B2905373 : Blo 1935435 2905373 := bbase (se 3 (by rfl) ⟨544757, by rfl⟩ : syracuseStep 2905373 = 1089515) (by norm_num)
theorem B1936915 : Blo 1935435 1936915 := bstep (se 1 (by rfl) ⟨1452686, by rfl⟩ : syracuseStep 1936915 = 2905373) B2905373
theorem B4358069 : Blo 1935435 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B2905379 : Blo 1935435 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B1936919 : Blo 1935435 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B6205157 : Blo 1935435 6205157 := bbase (se 4 (by rfl) ⟨581733, by rfl⟩ : syracuseStep 6205157 = 1163467) (by norm_num)
theorem B4136771 : Blo 1935435 4136771 := bstep (se 1 (by rfl) ⟨3102578, by rfl⟩ : syracuseStep 4136771 = 6205157) B6205157
theorem B11031389 : Blo 1935435 11031389 := bstep (se 3 (by rfl) ⟨2068385, by rfl⟩ : syracuseStep 11031389 = 4136771) B4136771
theorem B7354259 : Blo 1935435 7354259 := bstep (se 1 (by rfl) ⟨5515694, by rfl⟩ : syracuseStep 7354259 = 11031389) B11031389
theorem B4902839 : Blo 1935435 4902839 := bstep (se 1 (by rfl) ⟨3677129, by rfl⟩ : syracuseStep 4902839 = 7354259) B7354259
theorem B3268559 : Blo 1935435 3268559 := bstep (se 1 (by rfl) ⟨2451419, by rfl⟩ : syracuseStep 3268559 = 4902839) B4902839
theorem B2179039 : Blo 1935435 2179039 := bstep (se 1 (by rfl) ⟨1634279, by rfl⟩ : syracuseStep 2179039 = 3268559) B3268559
theorem B2905385 : Blo 1935435 2905385 := bstep (se 2 (by rfl) ⟨1089519, by rfl⟩ : syracuseStep 2905385 = 2179039) B2179039
theorem B1936923 : Blo 1935435 1936923 := bstep (se 1 (by rfl) ⟨1452692, by rfl⟩ : syracuseStep 1936923 = 2905385) B2905385
theorem B4653877 : Blo 1935435 4653877 := bbase (se 5 (by rfl) ⟨218150, by rfl⟩ : syracuseStep 4653877 = 436301) (by norm_num)
theorem B6205169 : Blo 1935435 6205169 := bstep (se 2 (by rfl) ⟨2326938, by rfl⟩ : syracuseStep 6205169 = 4653877) B4653877
theorem B4136779 : Blo 1935435 4136779 := bstep (se 1 (by rfl) ⟨3102584, by rfl⟩ : syracuseStep 4136779 = 6205169) B6205169
theorem B5515705 : Blo 1935435 5515705 := bstep (se 2 (by rfl) ⟨2068389, by rfl⟩ : syracuseStep 5515705 = 4136779) B4136779
theorem B7354273 : Blo 1935435 7354273 := bstep (se 2 (by rfl) ⟨2757852, by rfl⟩ : syracuseStep 7354273 = 5515705) B5515705
theorem B9805697 : Blo 1935435 9805697 := bstep (se 2 (by rfl) ⟨3677136, by rfl⟩ : syracuseStep 9805697 = 7354273) B7354273
theorem B6537131 : Blo 1935435 6537131 := bstep (se 1 (by rfl) ⟨4902848, by rfl⟩ : syracuseStep 6537131 = 9805697) B9805697
theorem B4358087 : Blo 1935435 4358087 := bstep (se 1 (by rfl) ⟨3268565, by rfl⟩ : syracuseStep 4358087 = 6537131) B6537131
theorem B2905391 : Blo 1935435 2905391 := bstep (se 1 (by rfl) ⟨2179043, by rfl⟩ : syracuseStep 2905391 = 4358087) B4358087
theorem B1936927 : Blo 1935435 1936927 := bstep (se 1 (by rfl) ⟨1452695, by rfl⟩ : syracuseStep 1936927 = 2905391) B2905391
theorem B2905397 : Blo 1935435 2905397 := bbase (se 5 (by rfl) ⟨136190, by rfl⟩ : syracuseStep 2905397 = 272381) (by norm_num)
theorem B1936931 : Blo 1935435 1936931 := bstep (se 1 (by rfl) ⟨1452698, by rfl⟩ : syracuseStep 1936931 = 2905397) B2905397
theorem B4902869 : Blo 1935435 4902869 := bbase (se 7 (by rfl) ⟨57455, by rfl⟩ : syracuseStep 4902869 = 114911) (by norm_num)
theorem B3268579 : Blo 1935435 3268579 := bstep (se 1 (by rfl) ⟨2451434, by rfl⟩ : syracuseStep 3268579 = 4902869) B4902869
theorem B4358105 : Blo 1935435 4358105 := bstep (se 2 (by rfl) ⟨1634289, by rfl⟩ : syracuseStep 4358105 = 3268579) B3268579
theorem B2905403 : Blo 1935435 2905403 := bstep (se 1 (by rfl) ⟨2179052, by rfl⟩ : syracuseStep 2905403 = 4358105) B4358105
theorem B1936935 : Blo 1935435 1936935 := bstep (se 1 (by rfl) ⟨1452701, by rfl⟩ : syracuseStep 1936935 = 2905403) B2905403
theorem B2179057 : Blo 1935435 2179057 := bbase (se 2 (by rfl) ⟨817146, by rfl⟩ : syracuseStep 2179057 = 1634293) (by norm_num)
theorem B2905409 : Blo 1935435 2905409 := bstep (se 2 (by rfl) ⟨1089528, by rfl⟩ : syracuseStep 2905409 = 2179057) B2179057
theorem B1936939 : Blo 1935435 1936939 := bstep (se 1 (by rfl) ⟨1452704, by rfl⟩ : syracuseStep 1936939 = 2905409) B2905409
theorem B15921269 : Blo 1935435 15921269 := bbase (se 5 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 15921269 = 1492619) (by norm_num)
theorem B10614179 : Blo 1935435 10614179 := bstep (se 1 (by rfl) ⟨7960634, by rfl⟩ : syracuseStep 10614179 = 15921269) B15921269
theorem B7076119 : Blo 1935435 7076119 := bstep (se 1 (by rfl) ⟨5307089, by rfl⟩ : syracuseStep 7076119 = 10614179) B10614179
theorem B9434825 : Blo 1935435 9434825 := bstep (se 2 (by rfl) ⟨3538059, by rfl⟩ : syracuseStep 9434825 = 7076119) B7076119
theorem B6289883 : Blo 1935435 6289883 := bstep (se 1 (by rfl) ⟨4717412, by rfl⟩ : syracuseStep 6289883 = 9434825) B9434825
theorem B4193255 : Blo 1935435 4193255 := bstep (se 1 (by rfl) ⟨3144941, by rfl⟩ : syracuseStep 4193255 = 6289883) B6289883
theorem B11182013 : Blo 1935435 11182013 := bstep (se 3 (by rfl) ⟨2096627, by rfl⟩ : syracuseStep 11182013 = 4193255) B4193255
theorem B7454675 : Blo 1935435 7454675 := bstep (se 1 (by rfl) ⟨5591006, by rfl⟩ : syracuseStep 7454675 = 11182013) B11182013
theorem B4969783 : Blo 1935435 4969783 := bstep (se 1 (by rfl) ⟨3727337, by rfl⟩ : syracuseStep 4969783 = 7454675) B7454675
theorem B6626377 : Blo 1935435 6626377 := bstep (se 2 (by rfl) ⟨2484891, by rfl⟩ : syracuseStep 6626377 = 4969783) B4969783
theorem B8835169 : Blo 1935435 8835169 := bstep (se 2 (by rfl) ⟨3313188, by rfl⟩ : syracuseStep 8835169 = 6626377) B6626377
theorem B11780225 : Blo 1935435 11780225 := bstep (se 2 (by rfl) ⟨4417584, by rfl⟩ : syracuseStep 11780225 = 8835169) B8835169
theorem B7853483 : Blo 1935435 7853483 := bstep (se 1 (by rfl) ⟨5890112, by rfl⟩ : syracuseStep 7853483 = 11780225) B11780225
theorem B20942621 : Blo 1935435 20942621 := bstep (se 3 (by rfl) ⟨3926741, by rfl⟩ : syracuseStep 20942621 = 7853483) B7853483
theorem B13961747 : Blo 1935435 13961747 := bstep (se 1 (by rfl) ⟨10471310, by rfl⟩ : syracuseStep 13961747 = 20942621) B20942621
theorem B9307831 : Blo 1935435 9307831 := bstep (se 1 (by rfl) ⟨6980873, by rfl⟩ : syracuseStep 9307831 = 13961747) B13961747
theorem B12410441 : Blo 1935435 12410441 := bstep (se 2 (by rfl) ⟨4653915, by rfl⟩ : syracuseStep 12410441 = 9307831) B9307831
theorem B8273627 : Blo 1935435 8273627 := bstep (se 1 (by rfl) ⟨6205220, by rfl⟩ : syracuseStep 8273627 = 12410441) B12410441
theorem B5515751 : Blo 1935435 5515751 := bstep (se 1 (by rfl) ⟨4136813, by rfl⟩ : syracuseStep 5515751 = 8273627) B8273627
theorem B3677167 : Blo 1935435 3677167 := bstep (se 1 (by rfl) ⟨2757875, by rfl⟩ : syracuseStep 3677167 = 5515751) B5515751
theorem B4902889 : Blo 1935435 4902889 := bstep (se 2 (by rfl) ⟨1838583, by rfl⟩ : syracuseStep 4902889 = 3677167) B3677167
theorem B6537185 : Blo 1935435 6537185 := bstep (se 2 (by rfl) ⟨2451444, by rfl⟩ : syracuseStep 6537185 = 4902889) B4902889
theorem B4358123 : Blo 1935435 4358123 := bstep (se 1 (by rfl) ⟨3268592, by rfl⟩ : syracuseStep 4358123 = 6537185) B6537185
theorem B2905415 : Blo 1935435 2905415 := bstep (se 1 (by rfl) ⟨2179061, by rfl⟩ : syracuseStep 2905415 = 4358123) B4358123
theorem B1936943 : Blo 1935435 1936943 := bstep (se 1 (by rfl) ⟨1452707, by rfl⟩ : syracuseStep 1936943 = 2905415) B2905415
theorem B2905421 : Blo 1935435 2905421 := bbase (se 3 (by rfl) ⟨544766, by rfl⟩ : syracuseStep 2905421 = 1089533) (by norm_num)
theorem B1936947 : Blo 1935435 1936947 := bstep (se 1 (by rfl) ⟨1452710, by rfl⟩ : syracuseStep 1936947 = 2905421) B2905421
theorem B4358141 : Blo 1935435 4358141 := bbase (se 3 (by rfl) ⟨817151, by rfl⟩ : syracuseStep 4358141 = 1634303) (by norm_num)
theorem B2905427 : Blo 1935435 2905427 := bstep (se 1 (by rfl) ⟨2179070, by rfl⟩ : syracuseStep 2905427 = 4358141) B4358141
theorem B1936951 : Blo 1935435 1936951 := bstep (se 1 (by rfl) ⟨1452713, by rfl⟩ : syracuseStep 1936951 = 2905427) B2905427
theorem B3268613 : Blo 1935435 3268613 := bbase (se 4 (by rfl) ⟨306432, by rfl⟩ : syracuseStep 3268613 = 612865) (by norm_num)
theorem B2179075 : Blo 1935435 2179075 := bstep (se 1 (by rfl) ⟨1634306, by rfl⟩ : syracuseStep 2179075 = 3268613) B3268613
theorem B2905433 : Blo 1935435 2905433 := bstep (se 2 (by rfl) ⟨1089537, by rfl⟩ : syracuseStep 2905433 = 2179075) B2179075
theorem B1936955 : Blo 1935435 1936955 := bstep (se 1 (by rfl) ⟨1452716, by rfl⟩ : syracuseStep 1936955 = 2905433) B2905433
theorem B14708789 : Blo 1935435 14708789 := bbase (se 5 (by rfl) ⟨689474, by rfl⟩ : syracuseStep 14708789 = 1378949) (by norm_num)
theorem B9805859 : Blo 1935435 9805859 := bstep (se 1 (by rfl) ⟨7354394, by rfl⟩ : syracuseStep 9805859 = 14708789) B14708789
theorem B6537239 : Blo 1935435 6537239 := bstep (se 1 (by rfl) ⟨4902929, by rfl⟩ : syracuseStep 6537239 = 9805859) B9805859
theorem B4358159 : Blo 1935435 4358159 := bstep (se 1 (by rfl) ⟨3268619, by rfl⟩ : syracuseStep 4358159 = 6537239) B6537239
theorem B2905439 : Blo 1935435 2905439 := bstep (se 1 (by rfl) ⟨2179079, by rfl⟩ : syracuseStep 2905439 = 4358159) B4358159
theorem B1936959 : Blo 1935435 1936959 := bstep (se 1 (by rfl) ⟨1452719, by rfl⟩ : syracuseStep 1936959 = 2905439) B2905439
theorem B2905445 : Blo 1935435 2905445 := bbase (se 4 (by rfl) ⟨272385, by rfl⟩ : syracuseStep 2905445 = 544771) (by norm_num)
theorem B1936963 : Blo 1935435 1936963 := bstep (se 1 (by rfl) ⟨1452722, by rfl⟩ : syracuseStep 1936963 = 2905445) B2905445
theorem B3677213 : Blo 1935435 3677213 := bbase (se 3 (by rfl) ⟨689477, by rfl⟩ : syracuseStep 3677213 = 1378955) (by norm_num)
theorem B2451475 : Blo 1935435 2451475 := bstep (se 1 (by rfl) ⟨1838606, by rfl⟩ : syracuseStep 2451475 = 3677213) B3677213
theorem B3268633 : Blo 1935435 3268633 := bstep (se 2 (by rfl) ⟨1225737, by rfl⟩ : syracuseStep 3268633 = 2451475) B2451475
theorem B4358177 : Blo 1935435 4358177 := bstep (se 2 (by rfl) ⟨1634316, by rfl⟩ : syracuseStep 4358177 = 3268633) B3268633
theorem B2905451 : Blo 1935435 2905451 := bstep (se 1 (by rfl) ⟨2179088, by rfl⟩ : syracuseStep 2905451 = 4358177) B4358177
theorem B1936967 : Blo 1935435 1936967 := bstep (se 1 (by rfl) ⟨1452725, by rfl⟩ : syracuseStep 1936967 = 2905451) B2905451
theorem B2179093 : Blo 1935435 2179093 := bbase (se 6 (by rfl) ⟨51072, by rfl⟩ : syracuseStep 2179093 = 102145) (by norm_num)
theorem B2905457 : Blo 1935435 2905457 := bstep (se 2 (by rfl) ⟨1089546, by rfl⟩ : syracuseStep 2905457 = 2179093) B2179093
theorem B1936971 : Blo 1935435 1936971 := bstep (se 1 (by rfl) ⟨1452728, by rfl⟩ : syracuseStep 1936971 = 2905457) B2905457
theorem B2451485 : Blo 1935435 2451485 := bbase (se 3 (by rfl) ⟨459653, by rfl⟩ : syracuseStep 2451485 = 919307) (by norm_num)
theorem B6537293 : Blo 1935435 6537293 := bstep (se 3 (by rfl) ⟨1225742, by rfl⟩ : syracuseStep 6537293 = 2451485) B2451485
theorem B4358195 : Blo 1935435 4358195 := bstep (se 1 (by rfl) ⟨3268646, by rfl⟩ : syracuseStep 4358195 = 6537293) B6537293
theorem B2905463 : Blo 1935435 2905463 := bstep (se 1 (by rfl) ⟨2179097, by rfl⟩ : syracuseStep 2905463 = 4358195) B4358195
theorem B1936975 : Blo 1935435 1936975 := bstep (se 1 (by rfl) ⟨1452731, by rfl⟩ : syracuseStep 1936975 = 2905463) B2905463
theorem B2905469 : Blo 1935435 2905469 := bbase (se 3 (by rfl) ⟨544775, by rfl⟩ : syracuseStep 2905469 = 1089551) (by norm_num)
theorem B1936979 : Blo 1935435 1936979 := bstep (se 1 (by rfl) ⟨1452734, by rfl⟩ : syracuseStep 1936979 = 2905469) B2905469
theorem B4358213 : Blo 1935435 4358213 := bbase (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) (by norm_num)
theorem B2905475 : Blo 1935435 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B1936983 : Blo 1935435 1936983 := bstep (se 1 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 1936983 = 2905475) B2905475
theorem B5515877 : Blo 1935435 5515877 := bbase (se 4 (by rfl) ⟨517113, by rfl⟩ : syracuseStep 5515877 = 1034227) (by norm_num)
theorem B3677251 : Blo 1935435 3677251 := bstep (se 1 (by rfl) ⟨2757938, by rfl⟩ : syracuseStep 3677251 = 5515877) B5515877
theorem B4903001 : Blo 1935435 4903001 := bstep (se 2 (by rfl) ⟨1838625, by rfl⟩ : syracuseStep 4903001 = 3677251) B3677251
theorem B3268667 : Blo 1935435 3268667 := bstep (se 1 (by rfl) ⟨2451500, by rfl⟩ : syracuseStep 3268667 = 4903001) B4903001
theorem B2179111 : Blo 1935435 2179111 := bstep (se 1 (by rfl) ⟨1634333, by rfl⟩ : syracuseStep 2179111 = 3268667) B3268667
theorem B2905481 : Blo 1935435 2905481 := bstep (se 2 (by rfl) ⟨1089555, by rfl⟩ : syracuseStep 2905481 = 2179111) B2179111
theorem B1936987 : Blo 1935435 1936987 := bstep (se 1 (by rfl) ⟨1452740, by rfl⟩ : syracuseStep 1936987 = 2905481) B2905481
theorem B9806021 : Blo 1935435 9806021 := bbase (se 4 (by rfl) ⟨919314, by rfl⟩ : syracuseStep 9806021 = 1838629) (by norm_num)
theorem B6537347 : Blo 1935435 6537347 := bstep (se 1 (by rfl) ⟨4903010, by rfl⟩ : syracuseStep 6537347 = 9806021) B9806021
theorem B4358231 : Blo 1935435 4358231 := bstep (se 1 (by rfl) ⟨3268673, by rfl⟩ : syracuseStep 4358231 = 6537347) B6537347
theorem B2905487 : Blo 1935435 2905487 := bstep (se 1 (by rfl) ⟨2179115, by rfl⟩ : syracuseStep 2905487 = 4358231) B4358231
theorem B1936991 : Blo 1935435 1936991 := bstep (se 1 (by rfl) ⟨1452743, by rfl⟩ : syracuseStep 1936991 = 2905487) B2905487
theorem B2905493 : Blo 1935435 2905493 := bbase (se 6 (by rfl) ⟨68097, by rfl⟩ : syracuseStep 2905493 = 136195) (by norm_num)
theorem B1936995 : Blo 1935435 1936995 := bstep (se 1 (by rfl) ⟨1452746, by rfl⟩ : syracuseStep 1936995 = 2905493) B2905493
theorem B4136933 : Blo 1935435 4136933 := bbase (se 4 (by rfl) ⟨387837, by rfl⟩ : syracuseStep 4136933 = 775675) (by norm_num)
theorem B11031821 : Blo 1935435 11031821 := bstep (se 3 (by rfl) ⟨2068466, by rfl⟩ : syracuseStep 11031821 = 4136933) B4136933
theorem B7354547 : Blo 1935435 7354547 := bstep (se 1 (by rfl) ⟨5515910, by rfl⟩ : syracuseStep 7354547 = 11031821) B11031821
theorem B4903031 : Blo 1935435 4903031 := bstep (se 1 (by rfl) ⟨3677273, by rfl⟩ : syracuseStep 4903031 = 7354547) B7354547
theorem B3268687 : Blo 1935435 3268687 := bstep (se 1 (by rfl) ⟨2451515, by rfl⟩ : syracuseStep 3268687 = 4903031) B4903031
theorem B4358249 : Blo 1935435 4358249 := bstep (se 2 (by rfl) ⟨1634343, by rfl⟩ : syracuseStep 4358249 = 3268687) B3268687
theorem B2905499 : Blo 1935435 2905499 := bstep (se 1 (by rfl) ⟨2179124, by rfl⟩ : syracuseStep 2905499 = 4358249) B4358249
theorem B1936999 : Blo 1935435 1936999 := bstep (se 1 (by rfl) ⟨1452749, by rfl⟩ : syracuseStep 1936999 = 2905499) B2905499
theorem B2179129 : Blo 1935435 2179129 := bbase (se 2 (by rfl) ⟨817173, by rfl⟩ : syracuseStep 2179129 = 1634347) (by norm_num)
theorem B2905505 : Blo 1935435 2905505 := bstep (se 2 (by rfl) ⟨1089564, by rfl⟩ : syracuseStep 2905505 = 2179129) B2179129
theorem B1937003 : Blo 1935435 1937003 := bstep (se 1 (by rfl) ⟨1452752, by rfl⟩ : syracuseStep 1937003 = 2905505) B2905505
theorem B4417733 : Blo 1935435 4417733 := bbase (se 4 (by rfl) ⟨414162, by rfl⟩ : syracuseStep 4417733 = 828325) (by norm_num)
theorem B2945155 : Blo 1935435 2945155 := bstep (se 1 (by rfl) ⟨2208866, by rfl⟩ : syracuseStep 2945155 = 4417733) B4417733
theorem B3926873 : Blo 1935435 3926873 := bstep (se 2 (by rfl) ⟨1472577, by rfl⟩ : syracuseStep 3926873 = 2945155) B2945155
theorem B2617915 : Blo 1935435 2617915 := bstep (se 1 (by rfl) ⟨1963436, by rfl⟩ : syracuseStep 2617915 = 3926873) B3926873
theorem B3490553 : Blo 1935435 3490553 := bstep (se 2 (by rfl) ⟨1308957, by rfl⟩ : syracuseStep 3490553 = 2617915) B2617915
theorem B2327035 : Blo 1935435 2327035 := bstep (se 1 (by rfl) ⟨1745276, by rfl⟩ : syracuseStep 2327035 = 3490553) B3490553
theorem B3102713 : Blo 1935435 3102713 := bstep (se 2 (by rfl) ⟨1163517, by rfl⟩ : syracuseStep 3102713 = 2327035) B2327035
theorem B2068475 : Blo 1935435 2068475 := bstep (se 1 (by rfl) ⟨1551356, by rfl⟩ : syracuseStep 2068475 = 3102713) B3102713
theorem B5515933 : Blo 1935435 5515933 := bstep (se 3 (by rfl) ⟨1034237, by rfl⟩ : syracuseStep 5515933 = 2068475) B2068475
theorem B7354577 : Blo 1935435 7354577 := bstep (se 2 (by rfl) ⟨2757966, by rfl⟩ : syracuseStep 7354577 = 5515933) B5515933
theorem B4903051 : Blo 1935435 4903051 := bstep (se 1 (by rfl) ⟨3677288, by rfl⟩ : syracuseStep 4903051 = 7354577) B7354577
theorem B6537401 : Blo 1935435 6537401 := bstep (se 2 (by rfl) ⟨2451525, by rfl⟩ : syracuseStep 6537401 = 4903051) B4903051
theorem B4358267 : Blo 1935435 4358267 := bstep (se 1 (by rfl) ⟨3268700, by rfl⟩ : syracuseStep 4358267 = 6537401) B6537401
theorem B2905511 : Blo 1935435 2905511 := bstep (se 1 (by rfl) ⟨2179133, by rfl⟩ : syracuseStep 2905511 = 4358267) B4358267
theorem B1937007 : Blo 1935435 1937007 := bstep (se 1 (by rfl) ⟨1452755, by rfl⟩ : syracuseStep 1937007 = 2905511) B2905511
theorem B2905517 : Blo 1935435 2905517 := bbase (se 3 (by rfl) ⟨544784, by rfl⟩ : syracuseStep 2905517 = 1089569) (by norm_num)
theorem B1937011 : Blo 1935435 1937011 := bstep (se 1 (by rfl) ⟨1452758, by rfl⟩ : syracuseStep 1937011 = 2905517) B2905517
theorem B4358285 : Blo 1935435 4358285 := bbase (se 3 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 4358285 = 1634357) (by norm_num)
theorem B2905523 : Blo 1935435 2905523 := bstep (se 1 (by rfl) ⟨2179142, by rfl⟩ : syracuseStep 2905523 = 4358285) B4358285
theorem B1937015 : Blo 1935435 1937015 := bstep (se 1 (by rfl) ⟨1452761, by rfl⟩ : syracuseStep 1937015 = 2905523) B2905523
theorem B2451541 : Blo 1935435 2451541 := bbase (se 8 (by rfl) ⟨14364, by rfl⟩ : syracuseStep 2451541 = 28729) (by norm_num)
theorem B3268721 : Blo 1935435 3268721 := bstep (se 2 (by rfl) ⟨1225770, by rfl⟩ : syracuseStep 3268721 = 2451541) B2451541
theorem B2179147 : Blo 1935435 2179147 := bstep (se 1 (by rfl) ⟨1634360, by rfl⟩ : syracuseStep 2179147 = 3268721) B3268721
theorem B2905529 : Blo 1935435 2905529 := bstep (se 2 (by rfl) ⟨1089573, by rfl⟩ : syracuseStep 2905529 = 2179147) B2179147
theorem B1937019 : Blo 1935435 1937019 := bstep (se 1 (by rfl) ⟨1452764, by rfl⟩ : syracuseStep 1937019 = 2905529) B2905529
theorem B39759893 : Blo 1935435 39759893 := bbase (se 6 (by rfl) ⟨931872, by rfl⟩ : syracuseStep 39759893 = 1863745) (by norm_num)
theorem B26506595 : Blo 1935435 26506595 := bstep (se 1 (by rfl) ⟨19879946, by rfl⟩ : syracuseStep 26506595 = 39759893) B39759893
theorem B17671063 : Blo 1935435 17671063 := bstep (se 1 (by rfl) ⟨13253297, by rfl⟩ : syracuseStep 17671063 = 26506595) B26506595
theorem B23561417 : Blo 1935435 23561417 := bstep (se 2 (by rfl) ⟨8835531, by rfl⟩ : syracuseStep 23561417 = 17671063) B17671063
theorem B15707611 : Blo 1935435 15707611 := bstep (se 1 (by rfl) ⟨11780708, by rfl⟩ : syracuseStep 15707611 = 23561417) B23561417
theorem B83773925 : Blo 1935435 83773925 := bstep (se 4 (by rfl) ⟨7853805, by rfl⟩ : syracuseStep 83773925 = 15707611) B15707611
theorem B55849283 : Blo 1935435 55849283 := bstep (se 1 (by rfl) ⟨41886962, by rfl⟩ : syracuseStep 55849283 = 83773925) B83773925
theorem B37232855 : Blo 1935435 37232855 := bstep (se 1 (by rfl) ⟨27924641, by rfl⟩ : syracuseStep 37232855 = 55849283) B55849283
theorem B24821903 : Blo 1935435 24821903 := bstep (se 1 (by rfl) ⟨18616427, by rfl⟩ : syracuseStep 24821903 = 37232855) B37232855
theorem B16547935 : Blo 1935435 16547935 := bstep (se 1 (by rfl) ⟨12410951, by rfl⟩ : syracuseStep 16547935 = 24821903) B24821903
theorem B22063913 : Blo 1935435 22063913 := bstep (se 2 (by rfl) ⟨8273967, by rfl⟩ : syracuseStep 22063913 = 16547935) B16547935
theorem B14709275 : Blo 1935435 14709275 := bstep (se 1 (by rfl) ⟨11031956, by rfl⟩ : syracuseStep 14709275 = 22063913) B22063913
theorem B9806183 : Blo 1935435 9806183 := bstep (se 1 (by rfl) ⟨7354637, by rfl⟩ : syracuseStep 9806183 = 14709275) B14709275
theorem B6537455 : Blo 1935435 6537455 := bstep (se 1 (by rfl) ⟨4903091, by rfl⟩ : syracuseStep 6537455 = 9806183) B9806183
theorem B4358303 : Blo 1935435 4358303 := bstep (se 1 (by rfl) ⟨3268727, by rfl⟩ : syracuseStep 4358303 = 6537455) B6537455
theorem B2905535 : Blo 1935435 2905535 := bstep (se 1 (by rfl) ⟨2179151, by rfl⟩ : syracuseStep 2905535 = 4358303) B4358303
theorem B1937023 : Blo 1935435 1937023 := bstep (se 1 (by rfl) ⟨1452767, by rfl⟩ : syracuseStep 1937023 = 2905535) B2905535
theorem B2905541 : Blo 1935435 2905541 := bbase (se 4 (by rfl) ⟨272394, by rfl⟩ : syracuseStep 2905541 = 544789) (by norm_num)
theorem B1937027 : Blo 1935435 1937027 := bstep (se 1 (by rfl) ⟨1452770, by rfl⟩ : syracuseStep 1937027 = 2905541) B2905541
theorem B3268741 : Blo 1935435 3268741 := bbase (se 4 (by rfl) ⟨306444, by rfl⟩ : syracuseStep 3268741 = 612889) (by norm_num)
theorem B4358321 : Blo 1935435 4358321 := bstep (se 2 (by rfl) ⟨1634370, by rfl⟩ : syracuseStep 4358321 = 3268741) B3268741
theorem B2905547 : Blo 1935435 2905547 := bstep (se 1 (by rfl) ⟨2179160, by rfl⟩ : syracuseStep 2905547 = 4358321) B4358321
theorem B1937031 : Blo 1935435 1937031 := bstep (se 1 (by rfl) ⟨1452773, by rfl⟩ : syracuseStep 1937031 = 2905547) B2905547
theorem B2179165 : Blo 1935435 2179165 := bbase (se 3 (by rfl) ⟨408593, by rfl⟩ : syracuseStep 2179165 = 817187) (by norm_num)
theorem B2905553 : Blo 1935435 2905553 := bstep (se 2 (by rfl) ⟨1089582, by rfl⟩ : syracuseStep 2905553 = 2179165) B2179165
theorem B1937035 : Blo 1935435 1937035 := bstep (se 1 (by rfl) ⟨1452776, by rfl⟩ : syracuseStep 1937035 = 2905553) B2905553
theorem B6537509 : Blo 1935435 6537509 := bbase (se 4 (by rfl) ⟨612891, by rfl⟩ : syracuseStep 6537509 = 1225783) (by norm_num)
theorem B4358339 : Blo 1935435 4358339 := bstep (se 1 (by rfl) ⟨3268754, by rfl⟩ : syracuseStep 4358339 = 6537509) B6537509
theorem B2905559 : Blo 1935435 2905559 := bstep (se 1 (by rfl) ⟨2179169, by rfl⟩ : syracuseStep 2905559 = 4358339) B4358339
theorem B1937039 : Blo 1935435 1937039 := bstep (se 1 (by rfl) ⟨1452779, by rfl⟩ : syracuseStep 1937039 = 2905559) B2905559
theorem B2905565 : Blo 1935435 2905565 := bbase (se 3 (by rfl) ⟨544793, by rfl⟩ : syracuseStep 2905565 = 1089587) (by norm_num)
theorem B1937043 : Blo 1935435 1937043 := bstep (se 1 (by rfl) ⟨1452782, by rfl⟩ : syracuseStep 1937043 = 2905565) B2905565
theorem B4358357 : Blo 1935435 4358357 := bbase (se 7 (by rfl) ⟨51074, by rfl⟩ : syracuseStep 4358357 = 102149) (by norm_num)
theorem B2905571 : Blo 1935435 2905571 := bstep (se 1 (by rfl) ⟨2179178, by rfl⟩ : syracuseStep 2905571 = 4358357) B4358357
theorem B1937047 : Blo 1935435 1937047 := bstep (se 1 (by rfl) ⟨1452785, by rfl⟩ : syracuseStep 1937047 = 2905571) B2905571
theorem B53013973 : Blo 1935435 53013973 := bbase (se 7 (by rfl) ⟨621257, by rfl⟩ : syracuseStep 53013973 = 1242515) (by norm_num)
theorem B70685297 : Blo 1935435 70685297 := bstep (se 2 (by rfl) ⟨26506986, by rfl⟩ : syracuseStep 70685297 = 53013973) B53013973
theorem B47123531 : Blo 1935435 47123531 := bstep (se 1 (by rfl) ⟨35342648, by rfl⟩ : syracuseStep 47123531 = 70685297) B70685297
theorem B31415687 : Blo 1935435 31415687 := bstep (se 1 (by rfl) ⟨23561765, by rfl⟩ : syracuseStep 31415687 = 47123531) B47123531
theorem B20943791 : Blo 1935435 20943791 := bstep (se 1 (by rfl) ⟨15707843, by rfl⟩ : syracuseStep 20943791 = 31415687) B31415687
theorem B13962527 : Blo 1935435 13962527 := bstep (se 1 (by rfl) ⟨10471895, by rfl⟩ : syracuseStep 13962527 = 20943791) B20943791
theorem B9308351 : Blo 1935435 9308351 := bstep (se 1 (by rfl) ⟨6981263, by rfl⟩ : syracuseStep 9308351 = 13962527) B13962527
theorem B6205567 : Blo 1935435 6205567 := bstep (se 1 (by rfl) ⟨4654175, by rfl⟩ : syracuseStep 6205567 = 9308351) B9308351
theorem B8274089 : Blo 1935435 8274089 := bstep (se 2 (by rfl) ⟨3102783, by rfl⟩ : syracuseStep 8274089 = 6205567) B6205567
theorem B5516059 : Blo 1935435 5516059 := bstep (se 1 (by rfl) ⟨4137044, by rfl⟩ : syracuseStep 5516059 = 8274089) B8274089
theorem B7354745 : Blo 1935435 7354745 := bstep (se 2 (by rfl) ⟨2758029, by rfl⟩ : syracuseStep 7354745 = 5516059) B5516059
theorem B4903163 : Blo 1935435 4903163 := bstep (se 1 (by rfl) ⟨3677372, by rfl⟩ : syracuseStep 4903163 = 7354745) B7354745
theorem B3268775 : Blo 1935435 3268775 := bstep (se 1 (by rfl) ⟨2451581, by rfl⟩ : syracuseStep 3268775 = 4903163) B4903163
theorem B2179183 : Blo 1935435 2179183 := bstep (se 1 (by rfl) ⟨1634387, by rfl⟩ : syracuseStep 2179183 = 3268775) B3268775
theorem B2905577 : Blo 1935435 2905577 := bstep (se 2 (by rfl) ⟨1089591, by rfl⟩ : syracuseStep 2905577 = 2179183) B2179183
theorem B1937051 : Blo 1935435 1937051 := bstep (se 1 (by rfl) ⟨1452788, by rfl⟩ : syracuseStep 1937051 = 2905577) B2905577
theorem B12411157 : Blo 1935435 12411157 := bbase (se 6 (by rfl) ⟨290886, by rfl⟩ : syracuseStep 12411157 = 581773) (by norm_num)
theorem B16548209 : Blo 1935435 16548209 := bstep (se 2 (by rfl) ⟨6205578, by rfl⟩ : syracuseStep 16548209 = 12411157) B12411157
theorem B11032139 : Blo 1935435 11032139 := bstep (se 1 (by rfl) ⟨8274104, by rfl⟩ : syracuseStep 11032139 = 16548209) B16548209
theorem B7354759 : Blo 1935435 7354759 := bstep (se 1 (by rfl) ⟨5516069, by rfl⟩ : syracuseStep 7354759 = 11032139) B11032139
theorem B9806345 : Blo 1935435 9806345 := bstep (se 2 (by rfl) ⟨3677379, by rfl⟩ : syracuseStep 9806345 = 7354759) B7354759
theorem B6537563 : Blo 1935435 6537563 := bstep (se 1 (by rfl) ⟨4903172, by rfl⟩ : syracuseStep 6537563 = 9806345) B9806345
theorem B4358375 : Blo 1935435 4358375 := bstep (se 1 (by rfl) ⟨3268781, by rfl⟩ : syracuseStep 4358375 = 6537563) B6537563
theorem B2905583 : Blo 1935435 2905583 := bstep (se 1 (by rfl) ⟨2179187, by rfl⟩ : syracuseStep 2905583 = 4358375) B4358375
theorem B1937055 : Blo 1935435 1937055 := bstep (se 1 (by rfl) ⟨1452791, by rfl⟩ : syracuseStep 1937055 = 2905583) B2905583
theorem B2905589 : Blo 1935435 2905589 := bbase (se 5 (by rfl) ⟨136199, by rfl⟩ : syracuseStep 2905589 = 272399) (by norm_num)
theorem B1937059 : Blo 1935435 1937059 := bstep (se 1 (by rfl) ⟨1452794, by rfl⟩ : syracuseStep 1937059 = 2905589) B2905589
theorem B4654205 : Blo 1935435 4654205 := bbase (se 3 (by rfl) ⟨872663, by rfl⟩ : syracuseStep 4654205 = 1745327) (by norm_num)
theorem B3102803 : Blo 1935435 3102803 := bstep (se 1 (by rfl) ⟨2327102, by rfl⟩ : syracuseStep 3102803 = 4654205) B4654205
theorem B2068535 : Blo 1935435 2068535 := bstep (se 1 (by rfl) ⟨1551401, by rfl⟩ : syracuseStep 2068535 = 3102803) B3102803
theorem B5516093 : Blo 1935435 5516093 := bstep (se 3 (by rfl) ⟨1034267, by rfl⟩ : syracuseStep 5516093 = 2068535) B2068535
theorem B3677395 : Blo 1935435 3677395 := bstep (se 1 (by rfl) ⟨2758046, by rfl⟩ : syracuseStep 3677395 = 5516093) B5516093
theorem B4903193 : Blo 1935435 4903193 := bstep (se 2 (by rfl) ⟨1838697, by rfl⟩ : syracuseStep 4903193 = 3677395) B3677395
theorem B3268795 : Blo 1935435 3268795 := bstep (se 1 (by rfl) ⟨2451596, by rfl⟩ : syracuseStep 3268795 = 4903193) B4903193
theorem B4358393 : Blo 1935435 4358393 := bstep (se 2 (by rfl) ⟨1634397, by rfl⟩ : syracuseStep 4358393 = 3268795) B3268795
theorem B2905595 : Blo 1935435 2905595 := bstep (se 1 (by rfl) ⟨2179196, by rfl⟩ : syracuseStep 2905595 = 4358393) B4358393
theorem B1937063 : Blo 1935435 1937063 := bstep (se 1 (by rfl) ⟨1452797, by rfl⟩ : syracuseStep 1937063 = 2905595) B2905595
theorem B2179201 : Blo 1935435 2179201 := bbase (se 2 (by rfl) ⟨817200, by rfl⟩ : syracuseStep 2179201 = 1634401) (by norm_num)
theorem B2905601 : Blo 1935435 2905601 := bstep (se 2 (by rfl) ⟨1089600, by rfl⟩ : syracuseStep 2905601 = 2179201) B2179201
theorem B1937067 : Blo 1935435 1937067 := bstep (se 1 (by rfl) ⟨1452800, by rfl⟩ : syracuseStep 1937067 = 2905601) B2905601
theorem B4903213 : Blo 1935435 4903213 := bbase (se 3 (by rfl) ⟨919352, by rfl⟩ : syracuseStep 4903213 = 1838705) (by norm_num)
theorem B6537617 : Blo 1935435 6537617 := bstep (se 2 (by rfl) ⟨2451606, by rfl⟩ : syracuseStep 6537617 = 4903213) B4903213
theorem B4358411 : Blo 1935435 4358411 := bstep (se 1 (by rfl) ⟨3268808, by rfl⟩ : syracuseStep 4358411 = 6537617) B6537617
theorem B2905607 : Blo 1935435 2905607 := bstep (se 1 (by rfl) ⟨2179205, by rfl⟩ : syracuseStep 2905607 = 4358411) B4358411
theorem B1937071 : Blo 1935435 1937071 := bstep (se 1 (by rfl) ⟨1452803, by rfl⟩ : syracuseStep 1937071 = 2905607) B2905607
theorem B2905613 : Blo 1935435 2905613 := bbase (se 3 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 2905613 = 1089605) (by norm_num)
theorem B1937075 : Blo 1935435 1937075 := bstep (se 1 (by rfl) ⟨1452806, by rfl⟩ : syracuseStep 1937075 = 2905613) B2905613
theorem B4358429 : Blo 1935435 4358429 := bbase (se 3 (by rfl) ⟨817205, by rfl⟩ : syracuseStep 4358429 = 1634411) (by norm_num)
theorem B2905619 : Blo 1935435 2905619 := bstep (se 1 (by rfl) ⟨2179214, by rfl⟩ : syracuseStep 2905619 = 4358429) B4358429
theorem B1937079 : Blo 1935435 1937079 := bstep (se 1 (by rfl) ⟨1452809, by rfl⟩ : syracuseStep 1937079 = 2905619) B2905619
theorem B3268829 : Blo 1935435 3268829 := bbase (se 3 (by rfl) ⟨612905, by rfl⟩ : syracuseStep 3268829 = 1225811) (by norm_num)
theorem B2179219 : Blo 1935435 2179219 := bstep (se 1 (by rfl) ⟨1634414, by rfl⟩ : syracuseStep 2179219 = 3268829) B3268829
theorem B2905625 : Blo 1935435 2905625 := bstep (se 2 (by rfl) ⟨1089609, by rfl⟩ : syracuseStep 2905625 = 2179219) B2179219
theorem B1937083 : Blo 1935435 1937083 := bstep (se 1 (by rfl) ⟨1452812, by rfl⟩ : syracuseStep 1937083 = 2905625) B2905625
theorem B4654261 : Blo 1935435 4654261 := bbase (se 5 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 4654261 = 436337) (by norm_num)
theorem B6205681 : Blo 1935435 6205681 := bstep (se 2 (by rfl) ⟨2327130, by rfl⟩ : syracuseStep 6205681 = 4654261) B4654261
theorem B8274241 : Blo 1935435 8274241 := bstep (se 2 (by rfl) ⟨3102840, by rfl⟩ : syracuseStep 8274241 = 6205681) B6205681
theorem B11032321 : Blo 1935435 11032321 := bstep (se 2 (by rfl) ⟨4137120, by rfl⟩ : syracuseStep 11032321 = 8274241) B8274241
theorem B14709761 : Blo 1935435 14709761 := bstep (se 2 (by rfl) ⟨5516160, by rfl⟩ : syracuseStep 14709761 = 11032321) B11032321
theorem B9806507 : Blo 1935435 9806507 := bstep (se 1 (by rfl) ⟨7354880, by rfl⟩ : syracuseStep 9806507 = 14709761) B14709761
theorem B6537671 : Blo 1935435 6537671 := bstep (se 1 (by rfl) ⟨4903253, by rfl⟩ : syracuseStep 6537671 = 9806507) B9806507
theorem B4358447 : Blo 1935435 4358447 := bstep (se 1 (by rfl) ⟨3268835, by rfl⟩ : syracuseStep 4358447 = 6537671) B6537671
theorem B2905631 : Blo 1935435 2905631 := bstep (se 1 (by rfl) ⟨2179223, by rfl⟩ : syracuseStep 2905631 = 4358447) B4358447
theorem B1937087 : Blo 1935435 1937087 := bstep (se 1 (by rfl) ⟨1452815, by rfl⟩ : syracuseStep 1937087 = 2905631) B2905631
theorem B2905637 : Blo 1935435 2905637 := bbase (se 4 (by rfl) ⟨272403, by rfl⟩ : syracuseStep 2905637 = 544807) (by norm_num)
theorem B1937091 : Blo 1935435 1937091 := bstep (se 1 (by rfl) ⟨1452818, by rfl⟩ : syracuseStep 1937091 = 2905637) B2905637
theorem B2451637 : Blo 1935435 2451637 := bbase (se 5 (by rfl) ⟨114920, by rfl⟩ : syracuseStep 2451637 = 229841) (by norm_num)
theorem B3268849 : Blo 1935435 3268849 := bstep (se 2 (by rfl) ⟨1225818, by rfl⟩ : syracuseStep 3268849 = 2451637) B2451637
theorem B4358465 : Blo 1935435 4358465 := bstep (se 2 (by rfl) ⟨1634424, by rfl⟩ : syracuseStep 4358465 = 3268849) B3268849
theorem B2905643 : Blo 1935435 2905643 := bstep (se 1 (by rfl) ⟨2179232, by rfl⟩ : syracuseStep 2905643 = 4358465) B4358465
theorem B1937095 : Blo 1935435 1937095 := bstep (se 1 (by rfl) ⟨1452821, by rfl⟩ : syracuseStep 1937095 = 2905643) B2905643
theorem B2179237 : Blo 1935435 2179237 := bbase (se 4 (by rfl) ⟨204303, by rfl⟩ : syracuseStep 2179237 = 408607) (by norm_num)
theorem B2905649 : Blo 1935435 2905649 := bstep (se 2 (by rfl) ⟨1089618, by rfl⟩ : syracuseStep 2905649 = 2179237) B2179237
theorem B1937099 : Blo 1935435 1937099 := bstep (se 1 (by rfl) ⟨1452824, by rfl⟩ : syracuseStep 1937099 = 2905649) B2905649
theorem B13962901 : Blo 1935435 13962901 := bbase (se 6 (by rfl) ⟨327255, by rfl⟩ : syracuseStep 13962901 = 654511) (by norm_num)
theorem B18617201 : Blo 1935435 18617201 := bstep (se 2 (by rfl) ⟨6981450, by rfl⟩ : syracuseStep 18617201 = 13962901) B13962901
theorem B12411467 : Blo 1935435 12411467 := bstep (se 1 (by rfl) ⟨9308600, by rfl⟩ : syracuseStep 12411467 = 18617201) B18617201
theorem B8274311 : Blo 1935435 8274311 := bstep (se 1 (by rfl) ⟨6205733, by rfl⟩ : syracuseStep 8274311 = 12411467) B12411467
theorem B5516207 : Blo 1935435 5516207 := bstep (se 1 (by rfl) ⟨4137155, by rfl⟩ : syracuseStep 5516207 = 8274311) B8274311
theorem B3677471 : Blo 1935435 3677471 := bstep (se 1 (by rfl) ⟨2758103, by rfl⟩ : syracuseStep 3677471 = 5516207) B5516207
theorem B2451647 : Blo 1935435 2451647 := bstep (se 1 (by rfl) ⟨1838735, by rfl⟩ : syracuseStep 2451647 = 3677471) B3677471
theorem B6537725 : Blo 1935435 6537725 := bstep (se 3 (by rfl) ⟨1225823, by rfl⟩ : syracuseStep 6537725 = 2451647) B2451647
theorem B4358483 : Blo 1935435 4358483 := bstep (se 1 (by rfl) ⟨3268862, by rfl⟩ : syracuseStep 4358483 = 6537725) B6537725
theorem B2905655 : Blo 1935435 2905655 := bstep (se 1 (by rfl) ⟨2179241, by rfl⟩ : syracuseStep 2905655 = 4358483) B4358483
theorem B1937103 : Blo 1935435 1937103 := bstep (se 1 (by rfl) ⟨1452827, by rfl⟩ : syracuseStep 1937103 = 2905655) B2905655
theorem B2905661 : Blo 1935435 2905661 := bbase (se 3 (by rfl) ⟨544811, by rfl⟩ : syracuseStep 2905661 = 1089623) (by norm_num)
theorem B1937107 : Blo 1935435 1937107 := bstep (se 1 (by rfl) ⟨1452830, by rfl⟩ : syracuseStep 1937107 = 2905661) B2905661
theorem B4358501 : Blo 1935435 4358501 := bbase (se 4 (by rfl) ⟨408609, by rfl⟩ : syracuseStep 4358501 = 817219) (by norm_num)
theorem B2905667 : Blo 1935435 2905667 := bstep (se 1 (by rfl) ⟨2179250, by rfl⟩ : syracuseStep 2905667 = 4358501) B4358501
theorem B1937111 : Blo 1935435 1937111 := bstep (se 1 (by rfl) ⟨1452833, by rfl⟩ : syracuseStep 1937111 = 2905667) B2905667
theorem B4903325 : Blo 1935435 4903325 := bbase (se 3 (by rfl) ⟨919373, by rfl⟩ : syracuseStep 4903325 = 1838747) (by norm_num)
theorem B3268883 : Blo 1935435 3268883 := bstep (se 1 (by rfl) ⟨2451662, by rfl⟩ : syracuseStep 3268883 = 4903325) B4903325
theorem B2179255 : Blo 1935435 2179255 := bstep (se 1 (by rfl) ⟨1634441, by rfl⟩ : syracuseStep 2179255 = 3268883) B3268883
theorem B2905673 : Blo 1935435 2905673 := bstep (se 2 (by rfl) ⟨1089627, by rfl⟩ : syracuseStep 2905673 = 2179255) B2179255
theorem B1937115 : Blo 1935435 1937115 := bstep (se 1 (by rfl) ⟨1452836, by rfl⟩ : syracuseStep 1937115 = 2905673) B2905673
theorem B3677501 : Blo 1935435 3677501 := bbase (se 3 (by rfl) ⟨689531, by rfl⟩ : syracuseStep 3677501 = 1379063) (by norm_num)
theorem B9806669 : Blo 1935435 9806669 := bstep (se 3 (by rfl) ⟨1838750, by rfl⟩ : syracuseStep 9806669 = 3677501) B3677501
theorem B6537779 : Blo 1935435 6537779 := bstep (se 1 (by rfl) ⟨4903334, by rfl⟩ : syracuseStep 6537779 = 9806669) B9806669
theorem B4358519 : Blo 1935435 4358519 := bstep (se 1 (by rfl) ⟨3268889, by rfl⟩ : syracuseStep 4358519 = 6537779) B6537779
theorem B2905679 : Blo 1935435 2905679 := bstep (se 1 (by rfl) ⟨2179259, by rfl⟩ : syracuseStep 2905679 = 4358519) B4358519
theorem B1937119 : Blo 1935435 1937119 := bstep (se 1 (by rfl) ⟨1452839, by rfl⟩ : syracuseStep 1937119 = 2905679) B2905679
theorem B2905685 : Blo 1935435 2905685 := bbase (se 8 (by rfl) ⟨17025, by rfl⟩ : syracuseStep 2905685 = 34051) (by norm_num)
theorem B1937123 : Blo 1935435 1937123 := bstep (se 1 (by rfl) ⟨1452842, by rfl⟩ : syracuseStep 1937123 = 2905685) B2905685
theorem B2618077 : Blo 1935435 2618077 := bbase (se 3 (by rfl) ⟨490889, by rfl⟩ : syracuseStep 2618077 = 981779) (by norm_num)
theorem B3490769 : Blo 1935435 3490769 := bstep (se 2 (by rfl) ⟨1309038, by rfl⟩ : syracuseStep 3490769 = 2618077) B2618077
theorem B2327179 : Blo 1935435 2327179 := bstep (se 1 (by rfl) ⟨1745384, by rfl⟩ : syracuseStep 2327179 = 3490769) B3490769
theorem B3102905 : Blo 1935435 3102905 := bstep (se 2 (by rfl) ⟨1163589, by rfl⟩ : syracuseStep 3102905 = 2327179) B2327179
theorem B8274413 : Blo 1935435 8274413 := bstep (se 3 (by rfl) ⟨1551452, by rfl⟩ : syracuseStep 8274413 = 3102905) B3102905
theorem B5516275 : Blo 1935435 5516275 := bstep (se 1 (by rfl) ⟨4137206, by rfl⟩ : syracuseStep 5516275 = 8274413) B8274413
theorem B7355033 : Blo 1935435 7355033 := bstep (se 2 (by rfl) ⟨2758137, by rfl⟩ : syracuseStep 7355033 = 5516275) B5516275
theorem B4903355 : Blo 1935435 4903355 := bstep (se 1 (by rfl) ⟨3677516, by rfl⟩ : syracuseStep 4903355 = 7355033) B7355033
theorem B3268903 : Blo 1935435 3268903 := bstep (se 1 (by rfl) ⟨2451677, by rfl⟩ : syracuseStep 3268903 = 4903355) B4903355
theorem B4358537 : Blo 1935435 4358537 := bstep (se 2 (by rfl) ⟨1634451, by rfl⟩ : syracuseStep 4358537 = 3268903) B3268903
theorem B2905691 : Blo 1935435 2905691 := bstep (se 1 (by rfl) ⟨2179268, by rfl⟩ : syracuseStep 2905691 = 4358537) B4358537
theorem B1937127 : Blo 1935435 1937127 := bstep (se 1 (by rfl) ⟨1452845, by rfl⟩ : syracuseStep 1937127 = 2905691) B2905691
theorem B2179273 : Blo 1935435 2179273 := bbase (se 2 (by rfl) ⟨817227, by rfl⟩ : syracuseStep 2179273 = 1634455) (by norm_num)
theorem B2905697 : Blo 1935435 2905697 := bstep (se 2 (by rfl) ⟨1089636, by rfl⟩ : syracuseStep 2905697 = 2179273) B2179273
theorem B1937131 : Blo 1935435 1937131 := bstep (se 1 (by rfl) ⟨1452848, by rfl⟩ : syracuseStep 1937131 = 2905697) B2905697
theorem B7076821 : Blo 1935435 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B9435761 : Blo 1935435 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B6290507 : Blo 1935435 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B16774685 : Blo 1935435 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B11183123 : Blo 1935435 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B7455415 : Blo 1935435 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B9940553 : Blo 1935435 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B6627035 : Blo 1935435 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B4418023 : Blo 1935435 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B5890697 : Blo 1935435 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B3927131 : Blo 1935435 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B2618087 : Blo 1935435 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B6981565 : Blo 1935435 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B9308753 : Blo 1935435 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B6205835 : Blo 1935435 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B16548893 : Blo 1935435 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B11032595 : Blo 1935435 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B7355063 : Blo 1935435 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B4903375 : Blo 1935435 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B6537833 : Blo 1935435 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B4358555 : Blo 1935435 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B2905703 : Blo 1935435 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B1937135 : Blo 1935435 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B2905709 : Blo 1935435 2905709 := bbase (se 3 (by rfl) ⟨544820, by rfl⟩ : syracuseStep 2905709 = 1089641) (by norm_num)
theorem B1937139 : Blo 1935435 1937139 := bstep (se 1 (by rfl) ⟨1452854, by rfl⟩ : syracuseStep 1937139 = 2905709) B2905709
theorem B4358573 : Blo 1935435 4358573 := bbase (se 3 (by rfl) ⟨817232, by rfl⟩ : syracuseStep 4358573 = 1634465) (by norm_num)
theorem B2905715 : Blo 1935435 2905715 := bstep (se 1 (by rfl) ⟨2179286, by rfl⟩ : syracuseStep 2905715 = 4358573) B4358573
theorem B1937143 : Blo 1935435 1937143 := bstep (se 1 (by rfl) ⟨1452857, by rfl⟩ : syracuseStep 1937143 = 2905715) B2905715
theorem B2068625 : Blo 1935435 2068625 := bbase (se 2 (by rfl) ⟨775734, by rfl⟩ : syracuseStep 2068625 = 1551469) (by norm_num)
theorem B5516333 : Blo 1935435 5516333 := bstep (se 3 (by rfl) ⟨1034312, by rfl⟩ : syracuseStep 5516333 = 2068625) B2068625
theorem B3677555 : Blo 1935435 3677555 := bstep (se 1 (by rfl) ⟨2758166, by rfl⟩ : syracuseStep 3677555 = 5516333) B5516333
theorem B2451703 : Blo 1935435 2451703 := bstep (se 1 (by rfl) ⟨1838777, by rfl⟩ : syracuseStep 2451703 = 3677555) B3677555
theorem B3268937 : Blo 1935435 3268937 := bstep (se 2 (by rfl) ⟨1225851, by rfl⟩ : syracuseStep 3268937 = 2451703) B2451703
theorem B2179291 : Blo 1935435 2179291 := bstep (se 1 (by rfl) ⟨1634468, by rfl⟩ : syracuseStep 2179291 = 3268937) B3268937
theorem B2905721 : Blo 1935435 2905721 := bstep (se 2 (by rfl) ⟨1089645, by rfl⟩ : syracuseStep 2905721 = 2179291) B2179291
theorem B1937147 : Blo 1935435 1937147 := bstep (se 1 (by rfl) ⟨1452860, by rfl⟩ : syracuseStep 1937147 = 2905721) B2905721
theorem B2985557 : Blo 1935435 2985557 := bbase (se 8 (by rfl) ⟨17493, by rfl⟩ : syracuseStep 2985557 = 34987) (by norm_num)
theorem B7961485 : Blo 1935435 7961485 := bstep (se 3 (by rfl) ⟨1492778, by rfl⟩ : syracuseStep 7961485 = 2985557) B2985557
theorem B10615313 : Blo 1935435 10615313 := bstep (se 2 (by rfl) ⟨3980742, by rfl⟩ : syracuseStep 10615313 = 7961485) B7961485
theorem B28307501 : Blo 1935435 28307501 := bstep (se 3 (by rfl) ⟨5307656, by rfl⟩ : syracuseStep 28307501 = 10615313) B10615313
theorem B18871667 : Blo 1935435 18871667 := bstep (se 1 (by rfl) ⟨14153750, by rfl⟩ : syracuseStep 18871667 = 28307501) B28307501
theorem B12581111 : Blo 1935435 12581111 := bstep (se 1 (by rfl) ⟨9435833, by rfl⟩ : syracuseStep 12581111 = 18871667) B18871667
theorem B8387407 : Blo 1935435 8387407 := bstep (se 1 (by rfl) ⟨6290555, by rfl⟩ : syracuseStep 8387407 = 12581111) B12581111
theorem B44732837 : Blo 1935435 44732837 := bstep (se 4 (by rfl) ⟨4193703, by rfl⟩ : syracuseStep 44732837 = 8387407) B8387407
theorem B29821891 : Blo 1935435 29821891 := bstep (se 1 (by rfl) ⟨22366418, by rfl⟩ : syracuseStep 29821891 = 44732837) B44732837
theorem B39762521 : Blo 1935435 39762521 := bstep (se 2 (by rfl) ⟨14910945, by rfl⟩ : syracuseStep 39762521 = 29821891) B29821891
theorem B26508347 : Blo 1935435 26508347 := bstep (se 1 (by rfl) ⟨19881260, by rfl⟩ : syracuseStep 26508347 = 39762521) B39762521
theorem B17672231 : Blo 1935435 17672231 := bstep (se 1 (by rfl) ⟨13254173, by rfl⟩ : syracuseStep 17672231 = 26508347) B26508347
theorem B11781487 : Blo 1935435 11781487 := bstep (se 1 (by rfl) ⟨8836115, by rfl⟩ : syracuseStep 11781487 = 17672231) B17672231
theorem B15708649 : Blo 1935435 15708649 := bstep (se 2 (by rfl) ⟨5890743, by rfl⟩ : syracuseStep 15708649 = 11781487) B11781487
theorem B20944865 : Blo 1935435 20944865 := bstep (se 2 (by rfl) ⟨7854324, by rfl⟩ : syracuseStep 20944865 = 15708649) B15708649
theorem B55852973 : Blo 1935435 55852973 := bstep (se 3 (by rfl) ⟨10472432, by rfl⟩ : syracuseStep 55852973 = 20944865) B20944865
theorem B37235315 : Blo 1935435 37235315 := bstep (se 1 (by rfl) ⟨27926486, by rfl⟩ : syracuseStep 37235315 = 55852973) B55852973
theorem B24823543 : Blo 1935435 24823543 := bstep (se 1 (by rfl) ⟨18617657, by rfl⟩ : syracuseStep 24823543 = 37235315) B37235315
theorem B33098057 : Blo 1935435 33098057 := bstep (se 2 (by rfl) ⟨12411771, by rfl⟩ : syracuseStep 33098057 = 24823543) B24823543
theorem B22065371 : Blo 1935435 22065371 := bstep (se 1 (by rfl) ⟨16549028, by rfl⟩ : syracuseStep 22065371 = 33098057) B33098057
theorem B14710247 : Blo 1935435 14710247 := bstep (se 1 (by rfl) ⟨11032685, by rfl⟩ : syracuseStep 14710247 = 22065371) B22065371
theorem B9806831 : Blo 1935435 9806831 := bstep (se 1 (by rfl) ⟨7355123, by rfl⟩ : syracuseStep 9806831 = 14710247) B14710247
theorem B6537887 : Blo 1935435 6537887 := bstep (se 1 (by rfl) ⟨4903415, by rfl⟩ : syracuseStep 6537887 = 9806831) B9806831
theorem B4358591 : Blo 1935435 4358591 := bstep (se 1 (by rfl) ⟨3268943, by rfl⟩ : syracuseStep 4358591 = 6537887) B6537887
theorem B2905727 : Blo 1935435 2905727 := bstep (se 1 (by rfl) ⟨2179295, by rfl⟩ : syracuseStep 2905727 = 4358591) B4358591
theorem B1937151 : Blo 1935435 1937151 := bstep (se 1 (by rfl) ⟨1452863, by rfl⟩ : syracuseStep 1937151 = 2905727) B2905727
theorem B2905733 : Blo 1935435 2905733 := bbase (se 4 (by rfl) ⟨272412, by rfl⟩ : syracuseStep 2905733 = 544825) (by norm_num)
theorem B1937155 : Blo 1935435 1937155 := bstep (se 1 (by rfl) ⟨1452866, by rfl⟩ : syracuseStep 1937155 = 2905733) B2905733
theorem B3268957 : Blo 1935435 3268957 := bbase (se 3 (by rfl) ⟨612929, by rfl⟩ : syracuseStep 3268957 = 1225859) (by norm_num)
theorem B4358609 : Blo 1935435 4358609 := bstep (se 2 (by rfl) ⟨1634478, by rfl⟩ : syracuseStep 4358609 = 3268957) B3268957
theorem B2905739 : Blo 1935435 2905739 := bstep (se 1 (by rfl) ⟨2179304, by rfl⟩ : syracuseStep 2905739 = 4358609) B4358609
theorem B1937159 : Blo 1935435 1937159 := bstep (se 1 (by rfl) ⟨1452869, by rfl⟩ : syracuseStep 1937159 = 2905739) B2905739
theorem B2179309 : Blo 1935435 2179309 := bbase (se 3 (by rfl) ⟨408620, by rfl⟩ : syracuseStep 2179309 = 817241) (by norm_num)
theorem B2905745 : Blo 1935435 2905745 := bstep (se 2 (by rfl) ⟨1089654, by rfl⟩ : syracuseStep 2905745 = 2179309) B2179309
theorem B1937163 : Blo 1935435 1937163 := bstep (se 1 (by rfl) ⟨1452872, by rfl⟩ : syracuseStep 1937163 = 2905745) B2905745
theorem B6537941 : Blo 1935435 6537941 := bbase (se 7 (by rfl) ⟨76616, by rfl⟩ : syracuseStep 6537941 = 153233) (by norm_num)
theorem B4358627 : Blo 1935435 4358627 := bstep (se 1 (by rfl) ⟨3268970, by rfl⟩ : syracuseStep 4358627 = 6537941) B6537941
theorem B2905751 : Blo 1935435 2905751 := bstep (se 1 (by rfl) ⟨2179313, by rfl⟩ : syracuseStep 2905751 = 4358627) B4358627
theorem B1937167 : Blo 1935435 1937167 := bstep (se 1 (by rfl) ⟨1452875, by rfl⟩ : syracuseStep 1937167 = 2905751) B2905751
theorem B2905757 : Blo 1935435 2905757 := bbase (se 3 (by rfl) ⟨544829, by rfl⟩ : syracuseStep 2905757 = 1089659) (by norm_num)
theorem B1937171 : Blo 1935435 1937171 := bstep (se 1 (by rfl) ⟨1452878, by rfl⟩ : syracuseStep 1937171 = 2905757) B2905757
theorem B4358645 : Blo 1935435 4358645 := bbase (se 5 (by rfl) ⟨204311, by rfl⟩ : syracuseStep 4358645 = 408623) (by norm_num)
theorem B2905763 : Blo 1935435 2905763 := bstep (se 1 (by rfl) ⟨2179322, by rfl⟩ : syracuseStep 2905763 = 4358645) B4358645
theorem B1937175 : Blo 1935435 1937175 := bstep (se 1 (by rfl) ⟨1452881, by rfl⟩ : syracuseStep 1937175 = 2905763) B2905763
theorem B37235861 : Blo 1935435 37235861 := bbase (se 6 (by rfl) ⟨872715, by rfl⟩ : syracuseStep 37235861 = 1745431) (by norm_num)
theorem B24823907 : Blo 1935435 24823907 := bstep (se 1 (by rfl) ⟨18617930, by rfl⟩ : syracuseStep 24823907 = 37235861) B37235861
theorem B16549271 : Blo 1935435 16549271 := bstep (se 1 (by rfl) ⟨12411953, by rfl⟩ : syracuseStep 16549271 = 24823907) B24823907
theorem B11032847 : Blo 1935435 11032847 := bstep (se 1 (by rfl) ⟨8274635, by rfl⟩ : syracuseStep 11032847 = 16549271) B16549271
theorem B7355231 : Blo 1935435 7355231 := bstep (se 1 (by rfl) ⟨5516423, by rfl⟩ : syracuseStep 7355231 = 11032847) B11032847
theorem B4903487 : Blo 1935435 4903487 := bstep (se 1 (by rfl) ⟨3677615, by rfl⟩ : syracuseStep 4903487 = 7355231) B7355231
theorem B3268991 : Blo 1935435 3268991 := bstep (se 1 (by rfl) ⟨2451743, by rfl⟩ : syracuseStep 3268991 = 4903487) B4903487
theorem B2179327 : Blo 1935435 2179327 := bstep (se 1 (by rfl) ⟨1634495, by rfl⟩ : syracuseStep 2179327 = 3268991) B3268991
theorem B2905769 : Blo 1935435 2905769 := bstep (se 2 (by rfl) ⟨1089663, by rfl⟩ : syracuseStep 2905769 = 2179327) B2179327
theorem B1937179 : Blo 1935435 1937179 := bstep (se 1 (by rfl) ⟨1452884, by rfl⟩ : syracuseStep 1937179 = 2905769) B2905769
theorem B4654493 : Blo 1935435 4654493 := bbase (se 3 (by rfl) ⟨872717, by rfl⟩ : syracuseStep 4654493 = 1745435) (by norm_num)
theorem B3102995 : Blo 1935435 3102995 := bstep (se 1 (by rfl) ⟨2327246, by rfl⟩ : syracuseStep 3102995 = 4654493) B4654493
theorem B2068663 : Blo 1935435 2068663 := bstep (se 1 (by rfl) ⟨1551497, by rfl⟩ : syracuseStep 2068663 = 3102995) B3102995
theorem B2758217 : Blo 1935435 2758217 := bstep (se 2 (by rfl) ⟨1034331, by rfl⟩ : syracuseStep 2758217 = 2068663) B2068663
theorem B7355245 : Blo 1935435 7355245 := bstep (se 3 (by rfl) ⟨1379108, by rfl⟩ : syracuseStep 7355245 = 2758217) B2758217
theorem B9806993 : Blo 1935435 9806993 := bstep (se 2 (by rfl) ⟨3677622, by rfl⟩ : syracuseStep 9806993 = 7355245) B7355245
theorem B6537995 : Blo 1935435 6537995 := bstep (se 1 (by rfl) ⟨4903496, by rfl⟩ : syracuseStep 6537995 = 9806993) B9806993
theorem B4358663 : Blo 1935435 4358663 := bstep (se 1 (by rfl) ⟨3268997, by rfl⟩ : syracuseStep 4358663 = 6537995) B6537995
theorem B2905775 : Blo 1935435 2905775 := bstep (se 1 (by rfl) ⟨2179331, by rfl⟩ : syracuseStep 2905775 = 4358663) B4358663
theorem B1937183 : Blo 1935435 1937183 := bstep (se 1 (by rfl) ⟨1452887, by rfl⟩ : syracuseStep 1937183 = 2905775) B2905775
theorem B2905781 : Blo 1935435 2905781 := bbase (se 5 (by rfl) ⟨136208, by rfl⟩ : syracuseStep 2905781 = 272417) (by norm_num)
theorem B1937187 : Blo 1935435 1937187 := bstep (se 1 (by rfl) ⟨1452890, by rfl⟩ : syracuseStep 1937187 = 2905781) B2905781
theorem B4903517 : Blo 1935435 4903517 := bbase (se 3 (by rfl) ⟨919409, by rfl⟩ : syracuseStep 4903517 = 1838819) (by norm_num)
theorem B3269011 : Blo 1935435 3269011 := bstep (se 1 (by rfl) ⟨2451758, by rfl⟩ : syracuseStep 3269011 = 4903517) B4903517
theorem B4358681 : Blo 1935435 4358681 := bstep (se 2 (by rfl) ⟨1634505, by rfl⟩ : syracuseStep 4358681 = 3269011) B3269011
theorem B2905787 : Blo 1935435 2905787 := bstep (se 1 (by rfl) ⟨2179340, by rfl⟩ : syracuseStep 2905787 = 4358681) B4358681
theorem B1937191 : Blo 1935435 1937191 := bstep (se 1 (by rfl) ⟨1452893, by rfl⟩ : syracuseStep 1937191 = 2905787) B2905787
theorem B2179345 : Blo 1935435 2179345 := bbase (se 2 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 2179345 = 1634509) (by norm_num)
theorem B2905793 : Blo 1935435 2905793 := bstep (se 2 (by rfl) ⟨1089672, by rfl⟩ : syracuseStep 2905793 = 2179345) B2179345
theorem B1937195 : Blo 1935435 1937195 := bstep (se 1 (by rfl) ⟨1452896, by rfl⟩ : syracuseStep 1937195 = 2905793) B2905793
theorem B3677653 : Blo 1935435 3677653 := bbase (se 7 (by rfl) ⟨43097, by rfl⟩ : syracuseStep 3677653 = 86195) (by norm_num)
theorem B4903537 : Blo 1935435 4903537 := bstep (se 2 (by rfl) ⟨1838826, by rfl⟩ : syracuseStep 4903537 = 3677653) B3677653
theorem B6538049 : Blo 1935435 6538049 := bstep (se 2 (by rfl) ⟨2451768, by rfl⟩ : syracuseStep 6538049 = 4903537) B4903537
theorem B4358699 : Blo 1935435 4358699 := bstep (se 1 (by rfl) ⟨3269024, by rfl⟩ : syracuseStep 4358699 = 6538049) B6538049
theorem B2905799 : Blo 1935435 2905799 := bstep (se 1 (by rfl) ⟨2179349, by rfl⟩ : syracuseStep 2905799 = 4358699) B4358699
theorem B1937199 : Blo 1935435 1937199 := bstep (se 1 (by rfl) ⟨1452899, by rfl⟩ : syracuseStep 1937199 = 2905799) B2905799
theorem B2905805 : Blo 1935435 2905805 := bbase (se 3 (by rfl) ⟨544838, by rfl⟩ : syracuseStep 2905805 = 1089677) (by norm_num)
theorem B1937203 : Blo 1935435 1937203 := bstep (se 1 (by rfl) ⟨1452902, by rfl⟩ : syracuseStep 1937203 = 2905805) B2905805
theorem B4358717 : Blo 1935435 4358717 := bbase (se 3 (by rfl) ⟨817259, by rfl⟩ : syracuseStep 4358717 = 1634519) (by norm_num)
theorem B2905811 : Blo 1935435 2905811 := bstep (se 1 (by rfl) ⟨2179358, by rfl⟩ : syracuseStep 2905811 = 4358717) B4358717
theorem B1937207 : Blo 1935435 1937207 := bstep (se 1 (by rfl) ⟨1452905, by rfl⟩ : syracuseStep 1937207 = 2905811) B2905811
theorem B3269045 : Blo 1935435 3269045 := bbase (se 5 (by rfl) ⟨153236, by rfl⟩ : syracuseStep 3269045 = 306473) (by norm_num)
theorem B2179363 : Blo 1935435 2179363 := bstep (se 1 (by rfl) ⟨1634522, by rfl⟩ : syracuseStep 2179363 = 3269045) B3269045
theorem B2905817 : Blo 1935435 2905817 := bstep (se 2 (by rfl) ⟨1089681, by rfl⟩ : syracuseStep 2905817 = 2179363) B2179363
theorem B1937211 : Blo 1935435 1937211 := bstep (se 1 (by rfl) ⟨1452908, by rfl⟩ : syracuseStep 1937211 = 2905817) B2905817
theorem B2068697 : Blo 1935435 2068697 := bbase (se 2 (by rfl) ⟨775761, by rfl⟩ : syracuseStep 2068697 = 1551523) (by norm_num)
theorem B5516525 : Blo 1935435 5516525 := bstep (se 3 (by rfl) ⟨1034348, by rfl⟩ : syracuseStep 5516525 = 2068697) B2068697
theorem B14710733 : Blo 1935435 14710733 := bstep (se 3 (by rfl) ⟨2758262, by rfl⟩ : syracuseStep 14710733 = 5516525) B5516525
theorem B9807155 : Blo 1935435 9807155 := bstep (se 1 (by rfl) ⟨7355366, by rfl⟩ : syracuseStep 9807155 = 14710733) B14710733
theorem B6538103 : Blo 1935435 6538103 := bstep (se 1 (by rfl) ⟨4903577, by rfl⟩ : syracuseStep 6538103 = 9807155) B9807155
theorem B4358735 : Blo 1935435 4358735 := bstep (se 1 (by rfl) ⟨3269051, by rfl⟩ : syracuseStep 4358735 = 6538103) B6538103
theorem B2905823 : Blo 1935435 2905823 := bstep (se 1 (by rfl) ⟨2179367, by rfl⟩ : syracuseStep 2905823 = 4358735) B4358735
theorem B1937215 : Blo 1935435 1937215 := bstep (se 1 (by rfl) ⟨1452911, by rfl⟩ : syracuseStep 1937215 = 2905823) B2905823
theorem B2905829 : Blo 1935435 2905829 := bbase (se 4 (by rfl) ⟨272421, by rfl⟩ : syracuseStep 2905829 = 544843) (by norm_num)
theorem B1937219 : Blo 1935435 1937219 := bstep (se 1 (by rfl) ⟨1452914, by rfl⟩ : syracuseStep 1937219 = 2905829) B2905829
theorem B5516549 : Blo 1935435 5516549 := bbase (se 4 (by rfl) ⟨517176, by rfl⟩ : syracuseStep 5516549 = 1034353) (by norm_num)
theorem B3677699 : Blo 1935435 3677699 := bstep (se 1 (by rfl) ⟨2758274, by rfl⟩ : syracuseStep 3677699 = 5516549) B5516549
theorem B2451799 : Blo 1935435 2451799 := bstep (se 1 (by rfl) ⟨1838849, by rfl⟩ : syracuseStep 2451799 = 3677699) B3677699
theorem B3269065 : Blo 1935435 3269065 := bstep (se 2 (by rfl) ⟨1225899, by rfl⟩ : syracuseStep 3269065 = 2451799) B2451799
theorem B4358753 : Blo 1935435 4358753 := bstep (se 2 (by rfl) ⟨1634532, by rfl⟩ : syracuseStep 4358753 = 3269065) B3269065
theorem B2905835 : Blo 1935435 2905835 := bstep (se 1 (by rfl) ⟨2179376, by rfl⟩ : syracuseStep 2905835 = 4358753) B4358753
theorem B1937223 : Blo 1935435 1937223 := bstep (se 1 (by rfl) ⟨1452917, by rfl⟩ : syracuseStep 1937223 = 2905835) B2905835
theorem B2179381 : Blo 1935435 2179381 := bbase (se 5 (by rfl) ⟨102158, by rfl⟩ : syracuseStep 2179381 = 204317) (by norm_num)
theorem B2905841 : Blo 1935435 2905841 := bstep (se 2 (by rfl) ⟨1089690, by rfl⟩ : syracuseStep 2905841 = 2179381) B2179381
theorem B1937227 : Blo 1935435 1937227 := bstep (se 1 (by rfl) ⟨1452920, by rfl⟩ : syracuseStep 1937227 = 2905841) B2905841
theorem B2451809 : Blo 1935435 2451809 := bbase (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) (by norm_num)
theorem B6538157 : Blo 1935435 6538157 := bstep (se 3 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 6538157 = 2451809) B2451809
theorem B4358771 : Blo 1935435 4358771 := bstep (se 1 (by rfl) ⟨3269078, by rfl⟩ : syracuseStep 4358771 = 6538157) B6538157
theorem B2905847 : Blo 1935435 2905847 := bstep (se 1 (by rfl) ⟨2179385, by rfl⟩ : syracuseStep 2905847 = 4358771) B4358771
theorem B1937231 : Blo 1935435 1937231 := bstep (se 1 (by rfl) ⟨1452923, by rfl⟩ : syracuseStep 1937231 = 2905847) B2905847
theorem B2905853 : Blo 1935435 2905853 := bbase (se 3 (by rfl) ⟨544847, by rfl⟩ : syracuseStep 2905853 = 1089695) (by norm_num)
theorem B1937235 : Blo 1935435 1937235 := bstep (se 1 (by rfl) ⟨1452926, by rfl⟩ : syracuseStep 1937235 = 2905853) B2905853
theorem B4358789 : Blo 1935435 4358789 := bbase (se 4 (by rfl) ⟨408636, by rfl⟩ : syracuseStep 4358789 = 817273) (by norm_num)
theorem B2905859 : Blo 1935435 2905859 := bstep (se 1 (by rfl) ⟨2179394, by rfl⟩ : syracuseStep 2905859 = 4358789) B4358789
theorem B1937239 : Blo 1935435 1937239 := bstep (se 1 (by rfl) ⟨1452929, by rfl⟩ : syracuseStep 1937239 = 2905859) B2905859
theorem B3145429 : Blo 1935435 3145429 := bbase (se 7 (by rfl) ⟨36860, by rfl⟩ : syracuseStep 3145429 = 73721) (by norm_num)
theorem B4193905 : Blo 1935435 4193905 := bstep (se 2 (by rfl) ⟨1572714, by rfl⟩ : syracuseStep 4193905 = 3145429) B3145429
theorem B5591873 : Blo 1935435 5591873 := bstep (se 2 (by rfl) ⟨2096952, by rfl⟩ : syracuseStep 5591873 = 4193905) B4193905
theorem B14911661 : Blo 1935435 14911661 := bstep (se 3 (by rfl) ⟨2795936, by rfl⟩ : syracuseStep 14911661 = 5591873) B5591873
theorem B39764429 : Blo 1935435 39764429 := bstep (se 3 (by rfl) ⟨7455830, by rfl⟩ : syracuseStep 39764429 = 14911661) B14911661
theorem B26509619 : Blo 1935435 26509619 := bstep (se 1 (by rfl) ⟨19882214, by rfl⟩ : syracuseStep 26509619 = 39764429) B39764429
theorem B17673079 : Blo 1935435 17673079 := bstep (se 1 (by rfl) ⟨13254809, by rfl⟩ : syracuseStep 17673079 = 26509619) B26509619
theorem B23564105 : Blo 1935435 23564105 := bstep (se 2 (by rfl) ⟨8836539, by rfl⟩ : syracuseStep 23564105 = 17673079) B17673079
theorem B15709403 : Blo 1935435 15709403 := bstep (se 1 (by rfl) ⟨11782052, by rfl⟩ : syracuseStep 15709403 = 23564105) B23564105
theorem B10472935 : Blo 1935435 10472935 := bstep (se 1 (by rfl) ⟨7854701, by rfl⟩ : syracuseStep 10472935 = 15709403) B15709403
theorem B13963913 : Blo 1935435 13963913 := bstep (se 2 (by rfl) ⟨5236467, by rfl⟩ : syracuseStep 13963913 = 10472935) B10472935
theorem B9309275 : Blo 1935435 9309275 := bstep (se 1 (by rfl) ⟨6981956, by rfl⟩ : syracuseStep 9309275 = 13963913) B13963913
theorem B6206183 : Blo 1935435 6206183 := bstep (se 1 (by rfl) ⟨4654637, by rfl⟩ : syracuseStep 6206183 = 9309275) B9309275
theorem B4137455 : Blo 1935435 4137455 := bstep (se 1 (by rfl) ⟨3103091, by rfl⟩ : syracuseStep 4137455 = 6206183) B6206183
theorem B2758303 : Blo 1935435 2758303 := bstep (se 1 (by rfl) ⟨2068727, by rfl⟩ : syracuseStep 2758303 = 4137455) B4137455
theorem B3677737 : Blo 1935435 3677737 := bstep (se 2 (by rfl) ⟨1379151, by rfl⟩ : syracuseStep 3677737 = 2758303) B2758303
theorem B4903649 : Blo 1935435 4903649 := bstep (se 2 (by rfl) ⟨1838868, by rfl⟩ : syracuseStep 4903649 = 3677737) B3677737
theorem B3269099 : Blo 1935435 3269099 := bstep (se 1 (by rfl) ⟨2451824, by rfl⟩ : syracuseStep 3269099 = 4903649) B4903649
theorem B2179399 : Blo 1935435 2179399 := bstep (se 1 (by rfl) ⟨1634549, by rfl⟩ : syracuseStep 2179399 = 3269099) B3269099
theorem B2905865 : Blo 1935435 2905865 := bstep (se 2 (by rfl) ⟨1089699, by rfl⟩ : syracuseStep 2905865 = 2179399) B2179399
theorem B1937243 : Blo 1935435 1937243 := bstep (se 1 (by rfl) ⟨1452932, by rfl⟩ : syracuseStep 1937243 = 2905865) B2905865
theorem B9807317 : Blo 1935435 9807317 := bbase (se 7 (by rfl) ⟨114929, by rfl⟩ : syracuseStep 9807317 = 229859) (by norm_num)
theorem B6538211 : Blo 1935435 6538211 := bstep (se 1 (by rfl) ⟨4903658, by rfl⟩ : syracuseStep 6538211 = 9807317) B9807317
theorem B4358807 : Blo 1935435 4358807 := bstep (se 1 (by rfl) ⟨3269105, by rfl⟩ : syracuseStep 4358807 = 6538211) B6538211
theorem B2905871 : Blo 1935435 2905871 := bstep (se 1 (by rfl) ⟨2179403, by rfl⟩ : syracuseStep 2905871 = 4358807) B4358807
theorem B1937247 : Blo 1935435 1937247 := bstep (se 1 (by rfl) ⟨1452935, by rfl⟩ : syracuseStep 1937247 = 2905871) B2905871
theorem B2905877 : Blo 1935435 2905877 := bbase (se 6 (by rfl) ⟨68106, by rfl⟩ : syracuseStep 2905877 = 136213) (by norm_num)
theorem B1937251 : Blo 1935435 1937251 := bstep (se 1 (by rfl) ⟨1452938, by rfl⟩ : syracuseStep 1937251 = 2905877) B2905877
theorem B2096965 : Blo 1935435 2096965 := bbase (se 4 (by rfl) ⟨196590, by rfl⟩ : syracuseStep 2096965 = 393181) (by norm_num)
theorem B2795953 : Blo 1935435 2795953 := bstep (se 2 (by rfl) ⟨1048482, by rfl⟩ : syracuseStep 2795953 = 2096965) B2096965
theorem B3727937 : Blo 1935435 3727937 := bstep (se 2 (by rfl) ⟨1397976, by rfl⟩ : syracuseStep 3727937 = 2795953) B2795953
theorem B9941165 : Blo 1935435 9941165 := bstep (se 3 (by rfl) ⟨1863968, by rfl⟩ : syracuseStep 9941165 = 3727937) B3727937
theorem B6627443 : Blo 1935435 6627443 := bstep (se 1 (by rfl) ⟨4970582, by rfl⟩ : syracuseStep 6627443 = 9941165) B9941165
theorem B70692725 : Blo 1935435 70692725 := bstep (se 5 (by rfl) ⟨3313721, by rfl⟩ : syracuseStep 70692725 = 6627443) B6627443
theorem B47128483 : Blo 1935435 47128483 := bstep (se 1 (by rfl) ⟨35346362, by rfl⟩ : syracuseStep 47128483 = 70692725) B70692725
theorem B62837977 : Blo 1935435 62837977 := bstep (se 2 (by rfl) ⟨23564241, by rfl⟩ : syracuseStep 62837977 = 47128483) B47128483
theorem B83783969 : Blo 1935435 83783969 := bstep (se 2 (by rfl) ⟨31418988, by rfl⟩ : syracuseStep 83783969 = 62837977) B62837977
theorem B55855979 : Blo 1935435 55855979 := bstep (se 1 (by rfl) ⟨41891984, by rfl⟩ : syracuseStep 55855979 = 83783969) B83783969
theorem B37237319 : Blo 1935435 37237319 := bstep (se 1 (by rfl) ⟨27927989, by rfl⟩ : syracuseStep 37237319 = 55855979) B55855979
theorem B24824879 : Blo 1935435 24824879 := bstep (se 1 (by rfl) ⟨18618659, by rfl⟩ : syracuseStep 24824879 = 37237319) B37237319
theorem B16549919 : Blo 1935435 16549919 := bstep (se 1 (by rfl) ⟨12412439, by rfl⟩ : syracuseStep 16549919 = 24824879) B24824879
theorem B11033279 : Blo 1935435 11033279 := bstep (se 1 (by rfl) ⟨8274959, by rfl⟩ : syracuseStep 11033279 = 16549919) B16549919
theorem B7355519 : Blo 1935435 7355519 := bstep (se 1 (by rfl) ⟨5516639, by rfl⟩ : syracuseStep 7355519 = 11033279) B11033279
theorem B4903679 : Blo 1935435 4903679 := bstep (se 1 (by rfl) ⟨3677759, by rfl⟩ : syracuseStep 4903679 = 7355519) B7355519
theorem B3269119 : Blo 1935435 3269119 := bstep (se 1 (by rfl) ⟨2451839, by rfl⟩ : syracuseStep 3269119 = 4903679) B4903679
theorem B4358825 : Blo 1935435 4358825 := bstep (se 2 (by rfl) ⟨1634559, by rfl⟩ : syracuseStep 4358825 = 3269119) B3269119
theorem B2905883 : Blo 1935435 2905883 := bstep (se 1 (by rfl) ⟨2179412, by rfl⟩ : syracuseStep 2905883 = 4358825) B4358825
theorem B1937255 : Blo 1935435 1937255 := bstep (se 1 (by rfl) ⟨1452941, by rfl⟩ : syracuseStep 1937255 = 2905883) B2905883
theorem B2179417 : Blo 1935435 2179417 := bbase (se 2 (by rfl) ⟨817281, by rfl⟩ : syracuseStep 2179417 = 1634563) (by norm_num)
theorem B2905889 : Blo 1935435 2905889 := bstep (se 2 (by rfl) ⟨1089708, by rfl⟩ : syracuseStep 2905889 = 2179417) B2179417
theorem B1937259 : Blo 1935435 1937259 := bstep (se 1 (by rfl) ⟨1452944, by rfl⟩ : syracuseStep 1937259 = 2905889) B2905889
theorem B4654685 : Blo 1935435 4654685 := bbase (se 3 (by rfl) ⟨872753, by rfl⟩ : syracuseStep 4654685 = 1745507) (by norm_num)
theorem B3103123 : Blo 1935435 3103123 := bstep (se 1 (by rfl) ⟨2327342, by rfl⟩ : syracuseStep 3103123 = 4654685) B4654685
theorem B4137497 : Blo 1935435 4137497 := bstep (se 2 (by rfl) ⟨1551561, by rfl⟩ : syracuseStep 4137497 = 3103123) B3103123
theorem B2758331 : Blo 1935435 2758331 := bstep (se 1 (by rfl) ⟨2068748, by rfl⟩ : syracuseStep 2758331 = 4137497) B4137497
theorem B7355549 : Blo 1935435 7355549 := bstep (se 3 (by rfl) ⟨1379165, by rfl⟩ : syracuseStep 7355549 = 2758331) B2758331
theorem B4903699 : Blo 1935435 4903699 := bstep (se 1 (by rfl) ⟨3677774, by rfl⟩ : syracuseStep 4903699 = 7355549) B7355549
theorem B6538265 : Blo 1935435 6538265 := bstep (se 2 (by rfl) ⟨2451849, by rfl⟩ : syracuseStep 6538265 = 4903699) B4903699
theorem B4358843 : Blo 1935435 4358843 := bstep (se 1 (by rfl) ⟨3269132, by rfl⟩ : syracuseStep 4358843 = 6538265) B6538265
theorem B2905895 : Blo 1935435 2905895 := bstep (se 1 (by rfl) ⟨2179421, by rfl⟩ : syracuseStep 2905895 = 4358843) B4358843
theorem B1937263 : Blo 1935435 1937263 := bstep (se 1 (by rfl) ⟨1452947, by rfl⟩ : syracuseStep 1937263 = 2905895) B2905895
theorem B2905901 : Blo 1935435 2905901 := bbase (se 3 (by rfl) ⟨544856, by rfl⟩ : syracuseStep 2905901 = 1089713) (by norm_num)
theorem B1937267 : Blo 1935435 1937267 := bstep (se 1 (by rfl) ⟨1452950, by rfl⟩ : syracuseStep 1937267 = 2905901) B2905901
theorem B4358861 : Blo 1935435 4358861 := bbase (se 3 (by rfl) ⟨817286, by rfl⟩ : syracuseStep 4358861 = 1634573) (by norm_num)
theorem B2905907 : Blo 1935435 2905907 := bstep (se 1 (by rfl) ⟨2179430, by rfl⟩ : syracuseStep 2905907 = 4358861) B4358861
theorem B1937271 : Blo 1935435 1937271 := bstep (se 1 (by rfl) ⟨1452953, by rfl⟩ : syracuseStep 1937271 = 2905907) B2905907
theorem B2451865 : Blo 1935435 2451865 := bbase (se 2 (by rfl) ⟨919449, by rfl⟩ : syracuseStep 2451865 = 1838899) (by norm_num)
theorem B3269153 : Blo 1935435 3269153 := bstep (se 2 (by rfl) ⟨1225932, by rfl⟩ : syracuseStep 3269153 = 2451865) B2451865
theorem B2179435 : Blo 1935435 2179435 := bstep (se 1 (by rfl) ⟨1634576, by rfl⟩ : syracuseStep 2179435 = 3269153) B3269153
theorem B2905913 : Blo 1935435 2905913 := bstep (se 2 (by rfl) ⟨1089717, by rfl⟩ : syracuseStep 2905913 = 2179435) B2179435
theorem B1937275 : Blo 1935435 1937275 := bstep (se 1 (by rfl) ⟨1452956, by rfl⟩ : syracuseStep 1937275 = 2905913) B2905913
theorem B8275061 : Blo 1935435 8275061 := bbase (se 5 (by rfl) ⟨387893, by rfl⟩ : syracuseStep 8275061 = 775787) (by norm_num)
theorem B22066829 : Blo 1935435 22066829 := bstep (se 3 (by rfl) ⟨4137530, by rfl⟩ : syracuseStep 22066829 = 8275061) B8275061
theorem B14711219 : Blo 1935435 14711219 := bstep (se 1 (by rfl) ⟨11033414, by rfl⟩ : syracuseStep 14711219 = 22066829) B22066829
theorem B9807479 : Blo 1935435 9807479 := bstep (se 1 (by rfl) ⟨7355609, by rfl⟩ : syracuseStep 9807479 = 14711219) B14711219
theorem B6538319 : Blo 1935435 6538319 := bstep (se 1 (by rfl) ⟨4903739, by rfl⟩ : syracuseStep 6538319 = 9807479) B9807479
theorem B4358879 : Blo 1935435 4358879 := bstep (se 1 (by rfl) ⟨3269159, by rfl⟩ : syracuseStep 4358879 = 6538319) B6538319
theorem B2905919 : Blo 1935435 2905919 := bstep (se 1 (by rfl) ⟨2179439, by rfl⟩ : syracuseStep 2905919 = 4358879) B4358879
theorem B1937279 : Blo 1935435 1937279 := bstep (se 1 (by rfl) ⟨1452959, by rfl⟩ : syracuseStep 1937279 = 2905919) B2905919
theorem B2905925 : Blo 1935435 2905925 := bbase (se 4 (by rfl) ⟨272430, by rfl⟩ : syracuseStep 2905925 = 544861) (by norm_num)
theorem B1937283 : Blo 1935435 1937283 := bstep (se 1 (by rfl) ⟨1452962, by rfl⟩ : syracuseStep 1937283 = 2905925) B2905925
theorem B3269173 : Blo 1935435 3269173 := bbase (se 5 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 3269173 = 306485) (by norm_num)
theorem B4358897 : Blo 1935435 4358897 := bstep (se 2 (by rfl) ⟨1634586, by rfl⟩ : syracuseStep 4358897 = 3269173) B3269173
theorem B2905931 : Blo 1935435 2905931 := bstep (se 1 (by rfl) ⟨2179448, by rfl⟩ : syracuseStep 2905931 = 4358897) B4358897
theorem B1937287 : Blo 1935435 1937287 := bstep (se 1 (by rfl) ⟨1452965, by rfl⟩ : syracuseStep 1937287 = 2905931) B2905931
theorem B2179453 : Blo 1935435 2179453 := bbase (se 3 (by rfl) ⟨408647, by rfl⟩ : syracuseStep 2179453 = 817295) (by norm_num)
theorem B2905937 : Blo 1935435 2905937 := bstep (se 2 (by rfl) ⟨1089726, by rfl⟩ : syracuseStep 2905937 = 2179453) B2179453
theorem B1937291 : Blo 1935435 1937291 := bstep (se 1 (by rfl) ⟨1452968, by rfl⟩ : syracuseStep 1937291 = 2905937) B2905937
theorem B6538373 : Blo 1935435 6538373 := bbase (se 4 (by rfl) ⟨612972, by rfl⟩ : syracuseStep 6538373 = 1225945) (by norm_num)
theorem B4358915 : Blo 1935435 4358915 := bstep (se 1 (by rfl) ⟨3269186, by rfl⟩ : syracuseStep 4358915 = 6538373) B6538373
theorem B2905943 : Blo 1935435 2905943 := bstep (se 1 (by rfl) ⟨2179457, by rfl⟩ : syracuseStep 2905943 = 4358915) B4358915
theorem B1937295 : Blo 1935435 1937295 := bstep (se 1 (by rfl) ⟨1452971, by rfl⟩ : syracuseStep 1937295 = 2905943) B2905943
theorem B2905949 : Blo 1935435 2905949 := bbase (se 3 (by rfl) ⟨544865, by rfl⟩ : syracuseStep 2905949 = 1089731) (by norm_num)
theorem B1937299 : Blo 1935435 1937299 := bstep (se 1 (by rfl) ⟨1452974, by rfl⟩ : syracuseStep 1937299 = 2905949) B2905949
theorem B4358933 : Blo 1935435 4358933 := bbase (se 6 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 4358933 = 204325) (by norm_num)
theorem B2905955 : Blo 1935435 2905955 := bstep (se 1 (by rfl) ⟨2179466, by rfl⟩ : syracuseStep 2905955 = 4358933) B4358933
theorem B1937303 : Blo 1935435 1937303 := bstep (se 1 (by rfl) ⟨1452977, by rfl⟩ : syracuseStep 1937303 = 2905955) B2905955
theorem B7355717 : Blo 1935435 7355717 := bbase (se 4 (by rfl) ⟨689598, by rfl⟩ : syracuseStep 7355717 = 1379197) (by norm_num)
theorem B4903811 : Blo 1935435 4903811 := bstep (se 1 (by rfl) ⟨3677858, by rfl⟩ : syracuseStep 4903811 = 7355717) B7355717
theorem B3269207 : Blo 1935435 3269207 := bstep (se 1 (by rfl) ⟨2451905, by rfl⟩ : syracuseStep 3269207 = 4903811) B4903811
theorem B2179471 : Blo 1935435 2179471 := bstep (se 1 (by rfl) ⟨1634603, by rfl⟩ : syracuseStep 2179471 = 3269207) B3269207
theorem B2905961 : Blo 1935435 2905961 := bstep (se 2 (by rfl) ⟨1089735, by rfl⟩ : syracuseStep 2905961 = 2179471) B2179471
theorem B1937307 : Blo 1935435 1937307 := bstep (se 1 (by rfl) ⟨1452980, by rfl⟩ : syracuseStep 1937307 = 2905961) B2905961
theorem B8388101 : Blo 1935435 8388101 := bbase (se 4 (by rfl) ⟨786384, by rfl⟩ : syracuseStep 8388101 = 1572769) (by norm_num)
theorem B22368269 : Blo 1935435 22368269 := bstep (se 3 (by rfl) ⟨4194050, by rfl⟩ : syracuseStep 22368269 = 8388101) B8388101
theorem B59648717 : Blo 1935435 59648717 := bstep (se 3 (by rfl) ⟨11184134, by rfl⟩ : syracuseStep 59648717 = 22368269) B22368269
theorem B39765811 : Blo 1935435 39765811 := bstep (se 1 (by rfl) ⟨29824358, by rfl⟩ : syracuseStep 39765811 = 59648717) B59648717
theorem B53021081 : Blo 1935435 53021081 := bstep (se 2 (by rfl) ⟨19882905, by rfl⟩ : syracuseStep 53021081 = 39765811) B39765811
theorem B35347387 : Blo 1935435 35347387 := bstep (se 1 (by rfl) ⟨26510540, by rfl⟩ : syracuseStep 35347387 = 53021081) B53021081
theorem B47129849 : Blo 1935435 47129849 := bstep (se 2 (by rfl) ⟨17673693, by rfl⟩ : syracuseStep 47129849 = 35347387) B35347387
theorem B31419899 : Blo 1935435 31419899 := bstep (se 1 (by rfl) ⟨23564924, by rfl⟩ : syracuseStep 31419899 = 47129849) B47129849
theorem B20946599 : Blo 1935435 20946599 := bstep (se 1 (by rfl) ⟨15709949, by rfl⟩ : syracuseStep 20946599 = 31419899) B31419899
theorem B13964399 : Blo 1935435 13964399 := bstep (se 1 (by rfl) ⟨10473299, by rfl⟩ : syracuseStep 13964399 = 20946599) B20946599
theorem B9309599 : Blo 1935435 9309599 := bstep (se 1 (by rfl) ⟨6982199, by rfl⟩ : syracuseStep 9309599 = 13964399) B13964399
theorem B6206399 : Blo 1935435 6206399 := bstep (se 1 (by rfl) ⟨4654799, by rfl⟩ : syracuseStep 6206399 = 9309599) B9309599
theorem B4137599 : Blo 1935435 4137599 := bstep (se 1 (by rfl) ⟨3103199, by rfl⟩ : syracuseStep 4137599 = 6206399) B6206399
theorem B11033597 : Blo 1935435 11033597 := bstep (se 3 (by rfl) ⟨2068799, by rfl⟩ : syracuseStep 11033597 = 4137599) B4137599
theorem B7355731 : Blo 1935435 7355731 := bstep (se 1 (by rfl) ⟨5516798, by rfl⟩ : syracuseStep 7355731 = 11033597) B11033597
theorem B9807641 : Blo 1935435 9807641 := bstep (se 2 (by rfl) ⟨3677865, by rfl⟩ : syracuseStep 9807641 = 7355731) B7355731
theorem B6538427 : Blo 1935435 6538427 := bstep (se 1 (by rfl) ⟨4903820, by rfl⟩ : syracuseStep 6538427 = 9807641) B9807641
theorem B4358951 : Blo 1935435 4358951 := bstep (se 1 (by rfl) ⟨3269213, by rfl⟩ : syracuseStep 4358951 = 6538427) B6538427
theorem B2905967 : Blo 1935435 2905967 := bstep (se 1 (by rfl) ⟨2179475, by rfl⟩ : syracuseStep 2905967 = 4358951) B4358951
theorem B1937311 : Blo 1935435 1937311 := bstep (se 1 (by rfl) ⟨1452983, by rfl⟩ : syracuseStep 1937311 = 2905967) B2905967
theorem B2905973 : Blo 1935435 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B1937315 : Blo 1935435 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B3103213 : Blo 1935435 3103213 := bbase (se 3 (by rfl) ⟨581852, by rfl⟩ : syracuseStep 3103213 = 1163705) (by norm_num)
theorem B4137617 : Blo 1935435 4137617 := bstep (se 2 (by rfl) ⟨1551606, by rfl⟩ : syracuseStep 4137617 = 3103213) B3103213
theorem B2758411 : Blo 1935435 2758411 := bstep (se 1 (by rfl) ⟨2068808, by rfl⟩ : syracuseStep 2758411 = 4137617) B4137617
theorem B3677881 : Blo 1935435 3677881 := bstep (se 2 (by rfl) ⟨1379205, by rfl⟩ : syracuseStep 3677881 = 2758411) B2758411
theorem B4903841 : Blo 1935435 4903841 := bstep (se 2 (by rfl) ⟨1838940, by rfl⟩ : syracuseStep 4903841 = 3677881) B3677881
theorem B3269227 : Blo 1935435 3269227 := bstep (se 1 (by rfl) ⟨2451920, by rfl⟩ : syracuseStep 3269227 = 4903841) B4903841
theorem B4358969 : Blo 1935435 4358969 := bstep (se 2 (by rfl) ⟨1634613, by rfl⟩ : syracuseStep 4358969 = 3269227) B3269227
theorem B2905979 : Blo 1935435 2905979 := bstep (se 1 (by rfl) ⟨2179484, by rfl⟩ : syracuseStep 2905979 = 4358969) B4358969
theorem B1937319 : Blo 1935435 1937319 := bstep (se 1 (by rfl) ⟨1452989, by rfl⟩ : syracuseStep 1937319 = 2905979) B2905979
theorem B2179489 : Blo 1935435 2179489 := bbase (se 2 (by rfl) ⟨817308, by rfl⟩ : syracuseStep 2179489 = 1634617) (by norm_num)
theorem B2905985 : Blo 1935435 2905985 := bstep (se 2 (by rfl) ⟨1089744, by rfl⟩ : syracuseStep 2905985 = 2179489) B2179489
theorem B1937323 : Blo 1935435 1937323 := bstep (se 1 (by rfl) ⟨1452992, by rfl⟩ : syracuseStep 1937323 = 2905985) B2905985
theorem B4903861 : Blo 1935435 4903861 := bbase (se 5 (by rfl) ⟨229868, by rfl⟩ : syracuseStep 4903861 = 459737) (by norm_num)
theorem B6538481 : Blo 1935435 6538481 := bstep (se 2 (by rfl) ⟨2451930, by rfl⟩ : syracuseStep 6538481 = 4903861) B4903861
theorem B4358987 : Blo 1935435 4358987 := bstep (se 1 (by rfl) ⟨3269240, by rfl⟩ : syracuseStep 4358987 = 6538481) B6538481
theorem B2905991 : Blo 1935435 2905991 := bstep (se 1 (by rfl) ⟨2179493, by rfl⟩ : syracuseStep 2905991 = 4358987) B4358987
theorem B1937327 : Blo 1935435 1937327 := bstep (se 1 (by rfl) ⟨1452995, by rfl⟩ : syracuseStep 1937327 = 2905991) B2905991
theorem B2905997 : Blo 1935435 2905997 := bbase (se 3 (by rfl) ⟨544874, by rfl⟩ : syracuseStep 2905997 = 1089749) (by norm_num)
theorem B1937331 : Blo 1935435 1937331 := bstep (se 1 (by rfl) ⟨1452998, by rfl⟩ : syracuseStep 1937331 = 2905997) B2905997
theorem B4359005 : Blo 1935435 4359005 := bbase (se 3 (by rfl) ⟨817313, by rfl⟩ : syracuseStep 4359005 = 1634627) (by norm_num)
theorem B2906003 : Blo 1935435 2906003 := bstep (se 1 (by rfl) ⟨2179502, by rfl⟩ : syracuseStep 2906003 = 4359005) B4359005
theorem B1937335 : Blo 1935435 1937335 := bstep (se 1 (by rfl) ⟨1453001, by rfl⟩ : syracuseStep 1937335 = 2906003) B2906003
theorem B3269261 : Blo 1935435 3269261 := bbase (se 3 (by rfl) ⟨612986, by rfl⟩ : syracuseStep 3269261 = 1225973) (by norm_num)
theorem B2179507 : Blo 1935435 2179507 := bstep (se 1 (by rfl) ⟨1634630, by rfl⟩ : syracuseStep 2179507 = 3269261) B3269261
theorem B2906009 : Blo 1935435 2906009 := bstep (se 2 (by rfl) ⟨1089753, by rfl⟩ : syracuseStep 2906009 = 2179507) B2179507
theorem B1937339 : Blo 1935435 1937339 := bstep (se 1 (by rfl) ⟨1453004, by rfl⟩ : syracuseStep 1937339 = 2906009) B2906009
theorem B6206501 : Blo 1935435 6206501 := bbase (se 4 (by rfl) ⟨581859, by rfl⟩ : syracuseStep 6206501 = 1163719) (by norm_num)
theorem B16550669 : Blo 1935435 16550669 := bstep (se 3 (by rfl) ⟨3103250, by rfl⟩ : syracuseStep 16550669 = 6206501) B6206501
theorem B11033779 : Blo 1935435 11033779 := bstep (se 1 (by rfl) ⟨8275334, by rfl⟩ : syracuseStep 11033779 = 16550669) B16550669
theorem B14711705 : Blo 1935435 14711705 := bstep (se 2 (by rfl) ⟨5516889, by rfl⟩ : syracuseStep 14711705 = 11033779) B11033779
theorem B9807803 : Blo 1935435 9807803 := bstep (se 1 (by rfl) ⟨7355852, by rfl⟩ : syracuseStep 9807803 = 14711705) B14711705
theorem B6538535 : Blo 1935435 6538535 := bstep (se 1 (by rfl) ⟨4903901, by rfl⟩ : syracuseStep 6538535 = 9807803) B9807803
theorem B4359023 : Blo 1935435 4359023 := bstep (se 1 (by rfl) ⟨3269267, by rfl⟩ : syracuseStep 4359023 = 6538535) B6538535
theorem B2906015 : Blo 1935435 2906015 := bstep (se 1 (by rfl) ⟨2179511, by rfl⟩ : syracuseStep 2906015 = 4359023) B4359023
theorem B1937343 : Blo 1935435 1937343 := bstep (se 1 (by rfl) ⟨1453007, by rfl⟩ : syracuseStep 1937343 = 2906015) B2906015
theorem B2906021 : Blo 1935435 2906021 := bbase (se 4 (by rfl) ⟨272439, by rfl⟩ : syracuseStep 2906021 = 544879) (by norm_num)
theorem B1937347 : Blo 1935435 1937347 := bstep (se 1 (by rfl) ⟨1453010, by rfl⟩ : syracuseStep 1937347 = 2906021) B2906021
theorem B2451961 : Blo 1935435 2451961 := bbase (se 2 (by rfl) ⟨919485, by rfl⟩ : syracuseStep 2451961 = 1838971) (by norm_num)
theorem B3269281 : Blo 1935435 3269281 := bstep (se 2 (by rfl) ⟨1225980, by rfl⟩ : syracuseStep 3269281 = 2451961) B2451961
theorem B4359041 : Blo 1935435 4359041 := bstep (se 2 (by rfl) ⟨1634640, by rfl⟩ : syracuseStep 4359041 = 3269281) B3269281
theorem B2906027 : Blo 1935435 2906027 := bstep (se 1 (by rfl) ⟨2179520, by rfl⟩ : syracuseStep 2906027 = 4359041) B4359041
theorem B1937351 : Blo 1935435 1937351 := bstep (se 1 (by rfl) ⟨1453013, by rfl⟩ : syracuseStep 1937351 = 2906027) B2906027
theorem B2179525 : Blo 1935435 2179525 := bbase (se 4 (by rfl) ⟨204330, by rfl⟩ : syracuseStep 2179525 = 408661) (by norm_num)
theorem B2906033 : Blo 1935435 2906033 := bstep (se 2 (by rfl) ⟨1089762, by rfl⟩ : syracuseStep 2906033 = 2179525) B2179525
theorem B1937355 : Blo 1935435 1937355 := bstep (se 1 (by rfl) ⟨1453016, by rfl⟩ : syracuseStep 1937355 = 2906033) B2906033
theorem B3677957 : Blo 1935435 3677957 := bbase (se 4 (by rfl) ⟨344808, by rfl⟩ : syracuseStep 3677957 = 689617) (by norm_num)
theorem B2451971 : Blo 1935435 2451971 := bstep (se 1 (by rfl) ⟨1838978, by rfl⟩ : syracuseStep 2451971 = 3677957) B3677957
theorem B6538589 : Blo 1935435 6538589 := bstep (se 3 (by rfl) ⟨1225985, by rfl⟩ : syracuseStep 6538589 = 2451971) B2451971
theorem B4359059 : Blo 1935435 4359059 := bstep (se 1 (by rfl) ⟨3269294, by rfl⟩ : syracuseStep 4359059 = 6538589) B6538589
theorem B2906039 : Blo 1935435 2906039 := bstep (se 1 (by rfl) ⟨2179529, by rfl⟩ : syracuseStep 2906039 = 4359059) B4359059
theorem B1937359 : Blo 1935435 1937359 := bstep (se 1 (by rfl) ⟨1453019, by rfl⟩ : syracuseStep 1937359 = 2906039) B2906039
theorem B2906045 : Blo 1935435 2906045 := bbase (se 3 (by rfl) ⟨544883, by rfl⟩ : syracuseStep 2906045 = 1089767) (by norm_num)
theorem B1937363 : Blo 1935435 1937363 := bstep (se 1 (by rfl) ⟨1453022, by rfl⟩ : syracuseStep 1937363 = 2906045) B2906045
theorem B4359077 : Blo 1935435 4359077 := bbase (se 4 (by rfl) ⟨408663, by rfl⟩ : syracuseStep 4359077 = 817327) (by norm_num)
theorem B2906051 : Blo 1935435 2906051 := bstep (se 1 (by rfl) ⟨2179538, by rfl⟩ : syracuseStep 2906051 = 4359077) B4359077
theorem B1937367 : Blo 1935435 1937367 := bstep (se 1 (by rfl) ⟨1453025, by rfl⟩ : syracuseStep 1937367 = 2906051) B2906051
theorem B4903973 : Blo 1935435 4903973 := bbase (se 4 (by rfl) ⟨459747, by rfl⟩ : syracuseStep 4903973 = 919495) (by norm_num)
theorem B3269315 : Blo 1935435 3269315 := bstep (se 1 (by rfl) ⟨2451986, by rfl⟩ : syracuseStep 3269315 = 4903973) B4903973
theorem B2179543 : Blo 1935435 2179543 := bstep (se 1 (by rfl) ⟨1634657, by rfl⟩ : syracuseStep 2179543 = 3269315) B3269315
theorem B2906057 : Blo 1935435 2906057 := bstep (se 2 (by rfl) ⟨1089771, by rfl⟩ : syracuseStep 2906057 = 2179543) B2179543
theorem B1937371 : Blo 1935435 1937371 := bstep (se 1 (by rfl) ⟨1453028, by rfl⟩ : syracuseStep 1937371 = 2906057) B2906057
theorem B5516981 : Blo 1935435 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B3677987 : Blo 1935435 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B9807965 : Blo 1935435 9807965 := bstep (se 3 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 9807965 = 3677987) B3677987
theorem B6538643 : Blo 1935435 6538643 := bstep (se 1 (by rfl) ⟨4903982, by rfl⟩ : syracuseStep 6538643 = 9807965) B9807965
theorem B4359095 : Blo 1935435 4359095 := bstep (se 1 (by rfl) ⟨3269321, by rfl⟩ : syracuseStep 4359095 = 6538643) B6538643
theorem B2906063 : Blo 1935435 2906063 := bstep (se 1 (by rfl) ⟨2179547, by rfl⟩ : syracuseStep 2906063 = 4359095) B4359095
theorem B1937375 : Blo 1935435 1937375 := bstep (se 1 (by rfl) ⟨1453031, by rfl⟩ : syracuseStep 1937375 = 2906063) B2906063
theorem B2906069 : Blo 1935435 2906069 := bbase (se 7 (by rfl) ⟨34055, by rfl⟩ : syracuseStep 2906069 = 68111) (by norm_num)
theorem B1937379 : Blo 1935435 1937379 := bstep (se 1 (by rfl) ⟨1453034, by rfl⟩ : syracuseStep 1937379 = 2906069) B2906069
theorem B7356005 : Blo 1935435 7356005 := bbase (se 4 (by rfl) ⟨689625, by rfl⟩ : syracuseStep 7356005 = 1379251) (by norm_num)
theorem B4904003 : Blo 1935435 4904003 := bstep (se 1 (by rfl) ⟨3678002, by rfl⟩ : syracuseStep 4904003 = 7356005) B7356005
theorem B3269335 : Blo 1935435 3269335 := bstep (se 1 (by rfl) ⟨2452001, by rfl⟩ : syracuseStep 3269335 = 4904003) B4904003
theorem B4359113 : Blo 1935435 4359113 := bstep (se 2 (by rfl) ⟨1634667, by rfl⟩ : syracuseStep 4359113 = 3269335) B3269335
theorem B2906075 : Blo 1935435 2906075 := bstep (se 1 (by rfl) ⟨2179556, by rfl⟩ : syracuseStep 2906075 = 4359113) B4359113
theorem B1937383 : Blo 1935435 1937383 := bstep (se 1 (by rfl) ⟨1453037, by rfl⟩ : syracuseStep 1937383 = 2906075) B2906075
theorem B2179561 : Blo 1935435 2179561 := bbase (se 2 (by rfl) ⟨817335, by rfl⟩ : syracuseStep 2179561 = 1634671) (by norm_num)
theorem B2906081 : Blo 1935435 2906081 := bstep (se 2 (by rfl) ⟨1089780, by rfl⟩ : syracuseStep 2906081 = 2179561) B2179561
theorem B1937387 : Blo 1935435 1937387 := bstep (se 1 (by rfl) ⟨1453040, by rfl⟩ : syracuseStep 1937387 = 2906081) B2906081
theorem B2068885 : Blo 1935435 2068885 := bbase (se 6 (by rfl) ⟨48489, by rfl⟩ : syracuseStep 2068885 = 96979) (by norm_num)
theorem B11034053 : Blo 1935435 11034053 := bstep (se 4 (by rfl) ⟨1034442, by rfl⟩ : syracuseStep 11034053 = 2068885) B2068885
theorem B7356035 : Blo 1935435 7356035 := bstep (se 1 (by rfl) ⟨5517026, by rfl⟩ : syracuseStep 7356035 = 11034053) B11034053
theorem B4904023 : Blo 1935435 4904023 := bstep (se 1 (by rfl) ⟨3678017, by rfl⟩ : syracuseStep 4904023 = 7356035) B7356035
theorem B6538697 : Blo 1935435 6538697 := bstep (se 2 (by rfl) ⟨2452011, by rfl⟩ : syracuseStep 6538697 = 4904023) B4904023
theorem B4359131 : Blo 1935435 4359131 := bstep (se 1 (by rfl) ⟨3269348, by rfl⟩ : syracuseStep 4359131 = 6538697) B6538697
theorem B2906087 : Blo 1935435 2906087 := bstep (se 1 (by rfl) ⟨2179565, by rfl⟩ : syracuseStep 2906087 = 4359131) B4359131
theorem B1937391 : Blo 1935435 1937391 := bstep (se 1 (by rfl) ⟨1453043, by rfl⟩ : syracuseStep 1937391 = 2906087) B2906087
theorem B2906093 : Blo 1935435 2906093 := bbase (se 3 (by rfl) ⟨544892, by rfl⟩ : syracuseStep 2906093 = 1089785) (by norm_num)
theorem B1937395 : Blo 1935435 1937395 := bstep (se 1 (by rfl) ⟨1453046, by rfl⟩ : syracuseStep 1937395 = 2906093) B2906093
theorem B4359149 : Blo 1935435 4359149 := bbase (se 3 (by rfl) ⟨817340, by rfl⟩ : syracuseStep 4359149 = 1634681) (by norm_num)
theorem B2906099 : Blo 1935435 2906099 := bstep (se 1 (by rfl) ⟨2179574, by rfl⟩ : syracuseStep 2906099 = 4359149) B4359149
theorem B1937399 : Blo 1935435 1937399 := bstep (se 1 (by rfl) ⟨1453049, by rfl⟩ : syracuseStep 1937399 = 2906099) B2906099
theorem B4137797 : Blo 1935435 4137797 := bbase (se 4 (by rfl) ⟨387918, by rfl⟩ : syracuseStep 4137797 = 775837) (by norm_num)
theorem B2758531 : Blo 1935435 2758531 := bstep (se 1 (by rfl) ⟨2068898, by rfl⟩ : syracuseStep 2758531 = 4137797) B4137797
theorem B3678041 : Blo 1935435 3678041 := bstep (se 2 (by rfl) ⟨1379265, by rfl⟩ : syracuseStep 3678041 = 2758531) B2758531
theorem B2452027 : Blo 1935435 2452027 := bstep (se 1 (by rfl) ⟨1839020, by rfl⟩ : syracuseStep 2452027 = 3678041) B3678041
theorem B3269369 : Blo 1935435 3269369 := bstep (se 2 (by rfl) ⟨1226013, by rfl⟩ : syracuseStep 3269369 = 2452027) B2452027
theorem B2179579 : Blo 1935435 2179579 := bstep (se 1 (by rfl) ⟨1634684, by rfl⟩ : syracuseStep 2179579 = 3269369) B3269369
theorem B2906105 : Blo 1935435 2906105 := bstep (se 2 (by rfl) ⟨1089789, by rfl⟩ : syracuseStep 2906105 = 2179579) B2179579
theorem B1937403 : Blo 1935435 1937403 := bstep (se 1 (by rfl) ⟨1453052, by rfl⟩ : syracuseStep 1937403 = 2906105) B2906105
theorem B12582773 : Blo 1935435 12582773 := bbase (se 5 (by rfl) ⟨589817, by rfl⟩ : syracuseStep 12582773 = 1179635) (by norm_num)
theorem B8388515 : Blo 1935435 8388515 := bstep (se 1 (by rfl) ⟨6291386, by rfl⟩ : syracuseStep 8388515 = 12582773) B12582773
theorem B22369373 : Blo 1935435 22369373 := bstep (se 3 (by rfl) ⟨4194257, by rfl⟩ : syracuseStep 22369373 = 8388515) B8388515
theorem B14912915 : Blo 1935435 14912915 := bstep (se 1 (by rfl) ⟨11184686, by rfl⟩ : syracuseStep 14912915 = 22369373) B22369373
theorem B39767773 : Blo 1935435 39767773 := bstep (se 3 (by rfl) ⟨7456457, by rfl⟩ : syracuseStep 39767773 = 14912915) B14912915
theorem B53023697 : Blo 1935435 53023697 := bstep (se 2 (by rfl) ⟨19883886, by rfl⟩ : syracuseStep 53023697 = 39767773) B39767773
theorem B35349131 : Blo 1935435 35349131 := bstep (se 1 (by rfl) ⟨26511848, by rfl⟩ : syracuseStep 35349131 = 53023697) B53023697
theorem B23566087 : Blo 1935435 23566087 := bstep (se 1 (by rfl) ⟨17674565, by rfl⟩ : syracuseStep 23566087 = 35349131) B35349131
theorem B31421449 : Blo 1935435 31421449 := bstep (se 2 (by rfl) ⟨11783043, by rfl⟩ : syracuseStep 31421449 = 23566087) B23566087
theorem B167581061 : Blo 1935435 167581061 := bstep (se 4 (by rfl) ⟨15710724, by rfl⟩ : syracuseStep 167581061 = 31421449) B31421449
theorem B111720707 : Blo 1935435 111720707 := bstep (se 1 (by rfl) ⟨83790530, by rfl⟩ : syracuseStep 111720707 = 167581061) B167581061
theorem B74480471 : Blo 1935435 74480471 := bstep (se 1 (by rfl) ⟨55860353, by rfl⟩ : syracuseStep 74480471 = 111720707) B111720707
theorem B49653647 : Blo 1935435 49653647 := bstep (se 1 (by rfl) ⟨37240235, by rfl⟩ : syracuseStep 49653647 = 74480471) B74480471
theorem B33102431 : Blo 1935435 33102431 := bstep (se 1 (by rfl) ⟨24826823, by rfl⟩ : syracuseStep 33102431 = 49653647) B49653647
theorem B22068287 : Blo 1935435 22068287 := bstep (se 1 (by rfl) ⟨16551215, by rfl⟩ : syracuseStep 22068287 = 33102431) B33102431
theorem B14712191 : Blo 1935435 14712191 := bstep (se 1 (by rfl) ⟨11034143, by rfl⟩ : syracuseStep 14712191 = 22068287) B22068287
theorem B9808127 : Blo 1935435 9808127 := bstep (se 1 (by rfl) ⟨7356095, by rfl⟩ : syracuseStep 9808127 = 14712191) B14712191
theorem B6538751 : Blo 1935435 6538751 := bstep (se 1 (by rfl) ⟨4904063, by rfl⟩ : syracuseStep 6538751 = 9808127) B9808127
theorem B4359167 : Blo 1935435 4359167 := bstep (se 1 (by rfl) ⟨3269375, by rfl⟩ : syracuseStep 4359167 = 6538751) B6538751
theorem B2906111 : Blo 1935435 2906111 := bstep (se 1 (by rfl) ⟨2179583, by rfl⟩ : syracuseStep 2906111 = 4359167) B4359167
theorem B1937407 : Blo 1935435 1937407 := bstep (se 1 (by rfl) ⟨1453055, by rfl⟩ : syracuseStep 1937407 = 2906111) B2906111
theorem B2906117 : Blo 1935435 2906117 := bbase (se 4 (by rfl) ⟨272448, by rfl⟩ : syracuseStep 2906117 = 544897) (by norm_num)
theorem B1937411 : Blo 1935435 1937411 := bstep (se 1 (by rfl) ⟨1453058, by rfl⟩ : syracuseStep 1937411 = 2906117) B2906117
theorem B3269389 : Blo 1935435 3269389 := bbase (se 3 (by rfl) ⟨613010, by rfl⟩ : syracuseStep 3269389 = 1226021) (by norm_num)
theorem B4359185 : Blo 1935435 4359185 := bstep (se 2 (by rfl) ⟨1634694, by rfl⟩ : syracuseStep 4359185 = 3269389) B3269389
theorem B2906123 : Blo 1935435 2906123 := bstep (se 1 (by rfl) ⟨2179592, by rfl⟩ : syracuseStep 2906123 = 4359185) B4359185
theorem B1937415 : Blo 1935435 1937415 := bstep (se 1 (by rfl) ⟨1453061, by rfl⟩ : syracuseStep 1937415 = 2906123) B2906123
theorem B2179597 : Blo 1935435 2179597 := bbase (se 3 (by rfl) ⟨408674, by rfl⟩ : syracuseStep 2179597 = 817349) (by norm_num)
theorem B2906129 : Blo 1935435 2906129 := bstep (se 2 (by rfl) ⟨1089798, by rfl⟩ : syracuseStep 2906129 = 2179597) B2179597
theorem B1937419 : Blo 1935435 1937419 := bstep (se 1 (by rfl) ⟨1453064, by rfl⟩ : syracuseStep 1937419 = 2906129) B2906129
theorem B6538805 : Blo 1935435 6538805 := bbase (se 5 (by rfl) ⟨306506, by rfl⟩ : syracuseStep 6538805 = 613013) (by norm_num)
theorem B4359203 : Blo 1935435 4359203 := bstep (se 1 (by rfl) ⟨3269402, by rfl⟩ : syracuseStep 4359203 = 6538805) B6538805
theorem B2906135 : Blo 1935435 2906135 := bstep (se 1 (by rfl) ⟨2179601, by rfl⟩ : syracuseStep 2906135 = 4359203) B4359203
theorem B1937423 : Blo 1935435 1937423 := bstep (se 1 (by rfl) ⟨1453067, by rfl⟩ : syracuseStep 1937423 = 2906135) B2906135
theorem B2906141 : Blo 1935435 2906141 := bbase (se 3 (by rfl) ⟨544901, by rfl⟩ : syracuseStep 2906141 = 1089803) (by norm_num)
theorem B1937427 : Blo 1935435 1937427 := bstep (se 1 (by rfl) ⟨1453070, by rfl⟩ : syracuseStep 1937427 = 2906141) B2906141
theorem B4359221 : Blo 1935435 4359221 := bbase (se 5 (by rfl) ⟨204338, by rfl⟩ : syracuseStep 4359221 = 408677) (by norm_num)
theorem B2906147 : Blo 1935435 2906147 := bstep (se 1 (by rfl) ⟨2179610, by rfl⟩ : syracuseStep 2906147 = 4359221) B4359221
theorem B1937431 : Blo 1935435 1937431 := bstep (se 1 (by rfl) ⟨1453073, by rfl⟩ : syracuseStep 1937431 = 2906147) B2906147
theorem B2327549 : Blo 1935435 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B6206797 : Blo 1935435 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B8275729 : Blo 1935435 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B11034305 : Blo 1935435 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B7356203 : Blo 1935435 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B4904135 : Blo 1935435 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B3269423 : Blo 1935435 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B2179615 : Blo 1935435 2179615 := bstep (se 1 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 2179615 = 3269423) B3269423
theorem B2906153 : Blo 1935435 2906153 := bstep (se 2 (by rfl) ⟨1089807, by rfl⟩ : syracuseStep 2906153 = 2179615) B2179615
theorem B1937435 : Blo 1935435 1937435 := bstep (se 1 (by rfl) ⟨1453076, by rfl⟩ : syracuseStep 1937435 = 2906153) B2906153
theorem C0 (j : ℕ) (h1 : 483858 ≤ j) (h2 : j ≤ 484358) : Blo 1935435 (4 * j + 3) := by
  interval_cases j
  · exact B1935435
  · exact B1935439
  · exact B1935443
  · exact B1935447
  · exact B1935451
  · exact B1935455
  · exact B1935459
  · exact B1935463
  · exact B1935467
  · exact B1935471
  · exact B1935475
  · exact B1935479
  · exact B1935483
  · exact B1935487
  · exact B1935491
  · exact B1935495
  · exact B1935499
  · exact B1935503
  · exact B1935507
  · exact B1935511
  · exact B1935515
  · exact B1935519
  · exact B1935523
  · exact B1935527
  · exact B1935531
  · exact B1935535
  · exact B1935539
  · exact B1935543
  · exact B1935547
  · exact B1935551
  · exact B1935555
  · exact B1935559
  · exact B1935563
  · exact B1935567
  · exact B1935571
  · exact B1935575
  · exact B1935579
  · exact B1935583
  · exact B1935587
  · exact B1935591
  · exact B1935595
  · exact B1935599
  · exact B1935603
  · exact B1935607
  · exact B1935611
  · exact B1935615
  · exact B1935619
  · exact B1935623
  · exact B1935627
  · exact B1935631
  · exact B1935635
  · exact B1935639
  · exact B1935643
  · exact B1935647
  · exact B1935651
  · exact B1935655
  · exact B1935659
  · exact B1935663
  · exact B1935667
  · exact B1935671
  · exact B1935675
  · exact B1935679
  · exact B1935683
  · exact B1935687
  · exact B1935691
  · exact B1935695
  · exact B1935699
  · exact B1935703
  · exact B1935707
  · exact B1935711
  · exact B1935715
  · exact B1935719
  · exact B1935723
  · exact B1935727
  · exact B1935731
  · exact B1935735
  · exact B1935739
  · exact B1935743
  · exact B1935747
  · exact B1935751
  · exact B1935755
  · exact B1935759
  · exact B1935763
  · exact B1935767
  · exact B1935771
  · exact B1935775
  · exact B1935779
  · exact B1935783
  · exact B1935787
  · exact B1935791
  · exact B1935795
  · exact B1935799
  · exact B1935803
  · exact B1935807
  · exact B1935811
  · exact B1935815
  · exact B1935819
  · exact B1935823
  · exact B1935827
  · exact B1935831
  · exact B1935835
  · exact B1935839
  · exact B1935843
  · exact B1935847
  · exact B1935851
  · exact B1935855
  · exact B1935859
  · exact B1935863
  · exact B1935867
  · exact B1935871
  · exact B1935875
  · exact B1935879
  · exact B1935883
  · exact B1935887
  · exact B1935891
  · exact B1935895
  · exact B1935899
  · exact B1935903
  · exact B1935907
  · exact B1935911
  · exact B1935915
  · exact B1935919
  · exact B1935923
  · exact B1935927
  · exact B1935931
  · exact B1935935
  · exact B1935939
  · exact B1935943
  · exact B1935947
  · exact B1935951
  · exact B1935955
  · exact B1935959
  · exact B1935963
  · exact B1935967
  · exact B1935971
  · exact B1935975
  · exact B1935979
  · exact B1935983
  · exact B1935987
  · exact B1935991
  · exact B1935995
  · exact B1935999
  · exact B1936003
  · exact B1936007
  · exact B1936011
  · exact B1936015
  · exact B1936019
  · exact B1936023
  · exact B1936027
  · exact B1936031
  · exact B1936035
  · exact B1936039
  · exact B1936043
  · exact B1936047
  · exact B1936051
  · exact B1936055
  · exact B1936059
  · exact B1936063
  · exact B1936067
  · exact B1936071
  · exact B1936075
  · exact B1936079
  · exact B1936083
  · exact B1936087
  · exact B1936091
  · exact B1936095
  · exact B1936099
  · exact B1936103
  · exact B1936107
  · exact B1936111
  · exact B1936115
  · exact B1936119
  · exact B1936123
  · exact B1936127
  · exact B1936131
  · exact B1936135
  · exact B1936139
  · exact B1936143
  · exact B1936147
  · exact B1936151
  · exact B1936155
  · exact B1936159
  · exact B1936163
  · exact B1936167
  · exact B1936171
  · exact B1936175
  · exact B1936179
  · exact B1936183
  · exact B1936187
  · exact B1936191
  · exact B1936195
  · exact B1936199
  · exact B1936203
  · exact B1936207
  · exact B1936211
  · exact B1936215
  · exact B1936219
  · exact B1936223
  · exact B1936227
  · exact B1936231
  · exact B1936235
  · exact B1936239
  · exact B1936243
  · exact B1936247
  · exact B1936251
  · exact B1936255
  · exact B1936259
  · exact B1936263
  · exact B1936267
  · exact B1936271
  · exact B1936275
  · exact B1936279
  · exact B1936283
  · exact B1936287
  · exact B1936291
  · exact B1936295
  · exact B1936299
  · exact B1936303
  · exact B1936307
  · exact B1936311
  · exact B1936315
  · exact B1936319
  · exact B1936323
  · exact B1936327
  · exact B1936331
  · exact B1936335
  · exact B1936339
  · exact B1936343
  · exact B1936347
  · exact B1936351
  · exact B1936355
  · exact B1936359
  · exact B1936363
  · exact B1936367
  · exact B1936371
  · exact B1936375
  · exact B1936379
  · exact B1936383
  · exact B1936387
  · exact B1936391
  · exact B1936395
  · exact B1936399
  · exact B1936403
  · exact B1936407
  · exact B1936411
  · exact B1936415
  · exact B1936419
  · exact B1936423
  · exact B1936427
  · exact B1936431
  · exact B1936435
  · exact B1936439
  · exact B1936443
  · exact B1936447
  · exact B1936451
  · exact B1936455
  · exact B1936459
  · exact B1936463
  · exact B1936467
  · exact B1936471
  · exact B1936475
  · exact B1936479
  · exact B1936483
  · exact B1936487
  · exact B1936491
  · exact B1936495
  · exact B1936499
  · exact B1936503
  · exact B1936507
  · exact B1936511
  · exact B1936515
  · exact B1936519
  · exact B1936523
  · exact B1936527
  · exact B1936531
  · exact B1936535
  · exact B1936539
  · exact B1936543
  · exact B1936547
  · exact B1936551
  · exact B1936555
  · exact B1936559
  · exact B1936563
  · exact B1936567
  · exact B1936571
  · exact B1936575
  · exact B1936579
  · exact B1936583
  · exact B1936587
  · exact B1936591
  · exact B1936595
  · exact B1936599
  · exact B1936603
  · exact B1936607
  · exact B1936611
  · exact B1936615
  · exact B1936619
  · exact B1936623
  · exact B1936627
  · exact B1936631
  · exact B1936635
  · exact B1936639
  · exact B1936643
  · exact B1936647
  · exact B1936651
  · exact B1936655
  · exact B1936659
  · exact B1936663
  · exact B1936667
  · exact B1936671
  · exact B1936675
  · exact B1936679
  · exact B1936683
  · exact B1936687
  · exact B1936691
  · exact B1936695
  · exact B1936699
  · exact B1936703
  · exact B1936707
  · exact B1936711
  · exact B1936715
  · exact B1936719
  · exact B1936723
  · exact B1936727
  · exact B1936731
  · exact B1936735
  · exact B1936739
  · exact B1936743
  · exact B1936747
  · exact B1936751
  · exact B1936755
  · exact B1936759
  · exact B1936763
  · exact B1936767
  · exact B1936771
  · exact B1936775
  · exact B1936779
  · exact B1936783
  · exact B1936787
  · exact B1936791
  · exact B1936795
  · exact B1936799
  · exact B1936803
  · exact B1936807
  · exact B1936811
  · exact B1936815
  · exact B1936819
  · exact B1936823
  · exact B1936827
  · exact B1936831
  · exact B1936835
  · exact B1936839
  · exact B1936843
  · exact B1936847
  · exact B1936851
  · exact B1936855
  · exact B1936859
  · exact B1936863
  · exact B1936867
  · exact B1936871
  · exact B1936875
  · exact B1936879
  · exact B1936883
  · exact B1936887
  · exact B1936891
  · exact B1936895
  · exact B1936899
  · exact B1936903
  · exact B1936907
  · exact B1936911
  · exact B1936915
  · exact B1936919
  · exact B1936923
  · exact B1936927
  · exact B1936931
  · exact B1936935
  · exact B1936939
  · exact B1936943
  · exact B1936947
  · exact B1936951
  · exact B1936955
  · exact B1936959
  · exact B1936963
  · exact B1936967
  · exact B1936971
  · exact B1936975
  · exact B1936979
  · exact B1936983
  · exact B1936987
  · exact B1936991
  · exact B1936995
  · exact B1936999
  · exact B1937003
  · exact B1937007
  · exact B1937011
  · exact B1937015
  · exact B1937019
  · exact B1937023
  · exact B1937027
  · exact B1937031
  · exact B1937035
  · exact B1937039
  · exact B1937043
  · exact B1937047
  · exact B1937051
  · exact B1937055
  · exact B1937059
  · exact B1937063
  · exact B1937067
  · exact B1937071
  · exact B1937075
  · exact B1937079
  · exact B1937083
  · exact B1937087
  · exact B1937091
  · exact B1937095
  · exact B1937099
  · exact B1937103
  · exact B1937107
  · exact B1937111
  · exact B1937115
  · exact B1937119
  · exact B1937123
  · exact B1937127
  · exact B1937131
  · exact B1937135
  · exact B1937139
  · exact B1937143
  · exact B1937147
  · exact B1937151
  · exact B1937155
  · exact B1937159
  · exact B1937163
  · exact B1937167
  · exact B1937171
  · exact B1937175
  · exact B1937179
  · exact B1937183
  · exact B1937187
  · exact B1937191
  · exact B1937195
  · exact B1937199
  · exact B1937203
  · exact B1937207
  · exact B1937211
  · exact B1937215
  · exact B1937219
  · exact B1937223
  · exact B1937227
  · exact B1937231
  · exact B1937235
  · exact B1937239
  · exact B1937243
  · exact B1937247
  · exact B1937251
  · exact B1937255
  · exact B1937259
  · exact B1937263
  · exact B1937267
  · exact B1937271
  · exact B1937275
  · exact B1937279
  · exact B1937283
  · exact B1937287
  · exact B1937291
  · exact B1937295
  · exact B1937299
  · exact B1937303
  · exact B1937307
  · exact B1937311
  · exact B1937315
  · exact B1937319
  · exact B1937323
  · exact B1937327
  · exact B1937331
  · exact B1937335
  · exact B1937339
  · exact B1937343
  · exact B1937347
  · exact B1937351
  · exact B1937355
  · exact B1937359
  · exact B1937363
  · exact B1937367
  · exact B1937371
  · exact B1937375
  · exact B1937379
  · exact B1937383
  · exact B1937387
  · exact B1937391
  · exact B1937395
  · exact B1937399
  · exact B1937403
  · exact B1937407
  · exact B1937411
  · exact B1937415
  · exact B1937419
  · exact B1937423
  · exact B1937427
  · exact B1937431
  · exact B1937435
theorem solution (m : ℕ) (hlo : 1935435 ≤ m) (hhi : m ≤ 1937435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 483858 ≤ j := by omega
    have hj2 : j ≤ 484358 := by omega
    have hb : Blo 1935435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
