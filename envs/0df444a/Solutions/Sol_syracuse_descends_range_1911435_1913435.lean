-- Prove2me | solution 1 for syracuse_descends_range_1911435_1913435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:01.191863+00:00
-- url     : https://prove2.me/submissions/09ebfe04-4749-4424-a180-ca77352562c4

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

theorem B2150365 : Blo 1911435 2150365 := bbase (se 3 (by rfl) ⟨403193, by rfl⟩ : syracuseStep 2150365 = 806387) (by norm_num)
theorem B2867153 : Blo 1911435 2867153 := bstep (se 2 (by rfl) ⟨1075182, by rfl⟩ : syracuseStep 2867153 = 2150365) B2150365
theorem B1911435 : Blo 1911435 1911435 := bstep (se 1 (by rfl) ⟨1433576, by rfl⟩ : syracuseStep 1911435 = 2867153) B2867153
theorem B6451109 : Blo 1911435 6451109 := bbase (se 4 (by rfl) ⟨604791, by rfl⟩ : syracuseStep 6451109 = 1209583) (by norm_num)
theorem B4300739 : Blo 1911435 4300739 := bstep (se 1 (by rfl) ⟨3225554, by rfl⟩ : syracuseStep 4300739 = 6451109) B6451109
theorem B2867159 : Blo 1911435 2867159 := bstep (se 1 (by rfl) ⟨2150369, by rfl⟩ : syracuseStep 2867159 = 4300739) B4300739
theorem B1911439 : Blo 1911435 1911439 := bstep (se 1 (by rfl) ⟨1433579, by rfl⟩ : syracuseStep 1911439 = 2867159) B2867159
theorem B2867165 : Blo 1911435 2867165 := bbase (se 3 (by rfl) ⟨537593, by rfl⟩ : syracuseStep 2867165 = 1075187) (by norm_num)
theorem B1911443 : Blo 1911435 1911443 := bstep (se 1 (by rfl) ⟨1433582, by rfl⟩ : syracuseStep 1911443 = 2867165) B2867165
theorem B4300757 : Blo 1911435 4300757 := bbase (se 7 (by rfl) ⟨50399, by rfl⟩ : syracuseStep 4300757 = 100799) (by norm_num)
theorem B2867171 : Blo 1911435 2867171 := bstep (se 1 (by rfl) ⟨2150378, by rfl⟩ : syracuseStep 2867171 = 4300757) B4300757
theorem B1911447 : Blo 1911435 1911447 := bstep (se 1 (by rfl) ⟨1433585, by rfl⟩ : syracuseStep 1911447 = 2867171) B2867171
theorem B2296333 : Blo 1911435 2296333 := bbase (se 3 (by rfl) ⟨430562, by rfl⟩ : syracuseStep 2296333 = 861125) (by norm_num)
theorem B12247109 : Blo 1911435 12247109 := bstep (se 4 (by rfl) ⟨1148166, by rfl⟩ : syracuseStep 12247109 = 2296333) B2296333
theorem B8164739 : Blo 1911435 8164739 := bstep (se 1 (by rfl) ⟨6123554, by rfl⟩ : syracuseStep 8164739 = 12247109) B12247109
theorem B5443159 : Blo 1911435 5443159 := bstep (se 1 (by rfl) ⟨4082369, by rfl⟩ : syracuseStep 5443159 = 8164739) B8164739
theorem B7257545 : Blo 1911435 7257545 := bstep (se 2 (by rfl) ⟨2721579, by rfl⟩ : syracuseStep 7257545 = 5443159) B5443159
theorem B4838363 : Blo 1911435 4838363 := bstep (se 1 (by rfl) ⟨3628772, by rfl⟩ : syracuseStep 4838363 = 7257545) B7257545
theorem B3225575 : Blo 1911435 3225575 := bstep (se 1 (by rfl) ⟨2419181, by rfl⟩ : syracuseStep 3225575 = 4838363) B4838363
theorem B2150383 : Blo 1911435 2150383 := bstep (se 1 (by rfl) ⟨1612787, by rfl⟩ : syracuseStep 2150383 = 3225575) B3225575
theorem B2867177 : Blo 1911435 2867177 := bstep (se 2 (by rfl) ⟨1075191, by rfl⟩ : syracuseStep 2867177 = 2150383) B2150383
theorem B1911451 : Blo 1911435 1911451 := bstep (se 1 (by rfl) ⟨1433588, by rfl⟩ : syracuseStep 1911451 = 2867177) B2867177
theorem B6889013 : Blo 1911435 6889013 := bbase (se 5 (by rfl) ⟨322922, by rfl⟩ : syracuseStep 6889013 = 645845) (by norm_num)
theorem B4592675 : Blo 1911435 4592675 := bstep (se 1 (by rfl) ⟨3444506, by rfl⟩ : syracuseStep 4592675 = 6889013) B6889013
theorem B3061783 : Blo 1911435 3061783 := bstep (se 1 (by rfl) ⟨2296337, by rfl⟩ : syracuseStep 3061783 = 4592675) B4592675
theorem B16329509 : Blo 1911435 16329509 := bstep (se 4 (by rfl) ⟨1530891, by rfl⟩ : syracuseStep 16329509 = 3061783) B3061783
theorem B10886339 : Blo 1911435 10886339 := bstep (se 1 (by rfl) ⟨8164754, by rfl⟩ : syracuseStep 10886339 = 16329509) B16329509
theorem B7257559 : Blo 1911435 7257559 := bstep (se 1 (by rfl) ⟨5443169, by rfl⟩ : syracuseStep 7257559 = 10886339) B10886339
theorem B9676745 : Blo 1911435 9676745 := bstep (se 2 (by rfl) ⟨3628779, by rfl⟩ : syracuseStep 9676745 = 7257559) B7257559
theorem B6451163 : Blo 1911435 6451163 := bstep (se 1 (by rfl) ⟨4838372, by rfl⟩ : syracuseStep 6451163 = 9676745) B9676745
theorem B4300775 : Blo 1911435 4300775 := bstep (se 1 (by rfl) ⟨3225581, by rfl⟩ : syracuseStep 4300775 = 6451163) B6451163
theorem B2867183 : Blo 1911435 2867183 := bstep (se 1 (by rfl) ⟨2150387, by rfl⟩ : syracuseStep 2867183 = 4300775) B4300775
theorem B1911455 : Blo 1911435 1911455 := bstep (se 1 (by rfl) ⟨1433591, by rfl⟩ : syracuseStep 1911455 = 2867183) B2867183
theorem B2867189 : Blo 1911435 2867189 := bbase (se 5 (by rfl) ⟨134399, by rfl⟩ : syracuseStep 2867189 = 268799) (by norm_num)
theorem B1911459 : Blo 1911435 1911459 := bstep (se 1 (by rfl) ⟨1433594, by rfl⟩ : syracuseStep 1911459 = 2867189) B2867189
theorem B13078421 : Blo 1911435 13078421 := bbase (se 6 (by rfl) ⟨306525, by rfl⟩ : syracuseStep 13078421 = 613051) (by norm_num)
theorem B8718947 : Blo 1911435 8718947 := bstep (se 1 (by rfl) ⟨6539210, by rfl⟩ : syracuseStep 8718947 = 13078421) B13078421
theorem B5812631 : Blo 1911435 5812631 := bstep (se 1 (by rfl) ⟨4359473, by rfl⟩ : syracuseStep 5812631 = 8718947) B8718947
theorem B3875087 : Blo 1911435 3875087 := bstep (se 1 (by rfl) ⟨2906315, by rfl⟩ : syracuseStep 3875087 = 5812631) B5812631
theorem B10333565 : Blo 1911435 10333565 := bstep (se 3 (by rfl) ⟨1937543, by rfl⟩ : syracuseStep 10333565 = 3875087) B3875087
theorem B6889043 : Blo 1911435 6889043 := bstep (se 1 (by rfl) ⟨5166782, by rfl⟩ : syracuseStep 6889043 = 10333565) B10333565
theorem B4592695 : Blo 1911435 4592695 := bstep (se 1 (by rfl) ⟨3444521, by rfl⟩ : syracuseStep 4592695 = 6889043) B6889043
theorem B6123593 : Blo 1911435 6123593 := bstep (se 2 (by rfl) ⟨2296347, by rfl⟩ : syracuseStep 6123593 = 4592695) B4592695
theorem B4082395 : Blo 1911435 4082395 := bstep (se 1 (by rfl) ⟨3061796, by rfl⟩ : syracuseStep 4082395 = 6123593) B6123593
theorem B5443193 : Blo 1911435 5443193 := bstep (se 2 (by rfl) ⟨2041197, by rfl⟩ : syracuseStep 5443193 = 4082395) B4082395
theorem B3628795 : Blo 1911435 3628795 := bstep (se 1 (by rfl) ⟨2721596, by rfl⟩ : syracuseStep 3628795 = 5443193) B5443193
theorem B4838393 : Blo 1911435 4838393 := bstep (se 2 (by rfl) ⟨1814397, by rfl⟩ : syracuseStep 4838393 = 3628795) B3628795
theorem B3225595 : Blo 1911435 3225595 := bstep (se 1 (by rfl) ⟨2419196, by rfl⟩ : syracuseStep 3225595 = 4838393) B4838393
theorem B4300793 : Blo 1911435 4300793 := bstep (se 2 (by rfl) ⟨1612797, by rfl⟩ : syracuseStep 4300793 = 3225595) B3225595
theorem B2867195 : Blo 1911435 2867195 := bstep (se 1 (by rfl) ⟨2150396, by rfl⟩ : syracuseStep 2867195 = 4300793) B4300793
theorem B1911463 : Blo 1911435 1911463 := bstep (se 1 (by rfl) ⟨1433597, by rfl⟩ : syracuseStep 1911463 = 2867195) B2867195
theorem B2150401 : Blo 1911435 2150401 := bbase (se 2 (by rfl) ⟨806400, by rfl⟩ : syracuseStep 2150401 = 1612801) (by norm_num)
theorem B2867201 : Blo 1911435 2867201 := bstep (se 2 (by rfl) ⟨1075200, by rfl⟩ : syracuseStep 2867201 = 2150401) B2150401
theorem B1911467 : Blo 1911435 1911467 := bstep (se 1 (by rfl) ⟨1433600, by rfl⟩ : syracuseStep 1911467 = 2867201) B2867201
theorem B4838413 : Blo 1911435 4838413 := bbase (se 3 (by rfl) ⟨907202, by rfl⟩ : syracuseStep 4838413 = 1814405) (by norm_num)
theorem B6451217 : Blo 1911435 6451217 := bstep (se 2 (by rfl) ⟨2419206, by rfl⟩ : syracuseStep 6451217 = 4838413) B4838413
theorem B4300811 : Blo 1911435 4300811 := bstep (se 1 (by rfl) ⟨3225608, by rfl⟩ : syracuseStep 4300811 = 6451217) B6451217
theorem B2867207 : Blo 1911435 2867207 := bstep (se 1 (by rfl) ⟨2150405, by rfl⟩ : syracuseStep 2867207 = 4300811) B4300811
theorem B1911471 : Blo 1911435 1911471 := bstep (se 1 (by rfl) ⟨1433603, by rfl⟩ : syracuseStep 1911471 = 2867207) B2867207
theorem B2867213 : Blo 1911435 2867213 := bbase (se 3 (by rfl) ⟨537602, by rfl⟩ : syracuseStep 2867213 = 1075205) (by norm_num)
theorem B1911475 : Blo 1911435 1911475 := bstep (se 1 (by rfl) ⟨1433606, by rfl⟩ : syracuseStep 1911475 = 2867213) B2867213
theorem B4300829 : Blo 1911435 4300829 := bbase (se 3 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 4300829 = 1612811) (by norm_num)
theorem B2867219 : Blo 1911435 2867219 := bstep (se 1 (by rfl) ⟨2150414, by rfl⟩ : syracuseStep 2867219 = 4300829) B4300829
theorem B1911479 : Blo 1911435 1911479 := bstep (se 1 (by rfl) ⟨1433609, by rfl⟩ : syracuseStep 1911479 = 2867219) B2867219
theorem B3225629 : Blo 1911435 3225629 := bbase (se 3 (by rfl) ⟨604805, by rfl⟩ : syracuseStep 3225629 = 1209611) (by norm_num)
theorem B2150419 : Blo 1911435 2150419 := bstep (se 1 (by rfl) ⟨1612814, by rfl⟩ : syracuseStep 2150419 = 3225629) B3225629
theorem B2867225 : Blo 1911435 2867225 := bstep (se 2 (by rfl) ⟨1075209, by rfl⟩ : syracuseStep 2867225 = 2150419) B2150419
theorem B1911483 : Blo 1911435 1911483 := bstep (se 1 (by rfl) ⟨1433612, by rfl⟩ : syracuseStep 1911483 = 2867225) B2867225
theorem B4479301 : Blo 1911435 4479301 := bbase (se 4 (by rfl) ⟨419934, by rfl⟩ : syracuseStep 4479301 = 839869) (by norm_num)
theorem B5972401 : Blo 1911435 5972401 := bstep (se 2 (by rfl) ⟨2239650, by rfl⟩ : syracuseStep 5972401 = 4479301) B4479301
theorem B7963201 : Blo 1911435 7963201 := bstep (se 2 (by rfl) ⟨2986200, by rfl⟩ : syracuseStep 7963201 = 5972401) B5972401
theorem B10617601 : Blo 1911435 10617601 := bstep (se 2 (by rfl) ⟨3981600, by rfl⟩ : syracuseStep 10617601 = 7963201) B7963201
theorem B14156801 : Blo 1911435 14156801 := bstep (se 2 (by rfl) ⟨5308800, by rfl⟩ : syracuseStep 14156801 = 10617601) B10617601
theorem B9437867 : Blo 1911435 9437867 := bstep (se 1 (by rfl) ⟨7078400, by rfl⟩ : syracuseStep 9437867 = 14156801) B14156801
theorem B6291911 : Blo 1911435 6291911 := bstep (se 1 (by rfl) ⟨4718933, by rfl⟩ : syracuseStep 6291911 = 9437867) B9437867
theorem B4194607 : Blo 1911435 4194607 := bstep (se 1 (by rfl) ⟨3145955, by rfl⟩ : syracuseStep 4194607 = 6291911) B6291911
theorem B5592809 : Blo 1911435 5592809 := bstep (se 2 (by rfl) ⟨2097303, by rfl⟩ : syracuseStep 5592809 = 4194607) B4194607
theorem B3728539 : Blo 1911435 3728539 := bstep (se 1 (by rfl) ⟨2796404, by rfl⟩ : syracuseStep 3728539 = 5592809) B5592809
theorem B4971385 : Blo 1911435 4971385 := bstep (se 2 (by rfl) ⟨1864269, by rfl⟩ : syracuseStep 4971385 = 3728539) B3728539
theorem B6628513 : Blo 1911435 6628513 := bstep (se 2 (by rfl) ⟨2485692, by rfl⟩ : syracuseStep 6628513 = 4971385) B4971385
theorem B8838017 : Blo 1911435 8838017 := bstep (se 2 (by rfl) ⟨3314256, by rfl⟩ : syracuseStep 8838017 = 6628513) B6628513
theorem B5892011 : Blo 1911435 5892011 := bstep (se 1 (by rfl) ⟨4419008, by rfl⟩ : syracuseStep 5892011 = 8838017) B8838017
theorem B3928007 : Blo 1911435 3928007 := bstep (se 1 (by rfl) ⟨2946005, by rfl⟩ : syracuseStep 3928007 = 5892011) B5892011
theorem B2618671 : Blo 1911435 2618671 := bstep (se 1 (by rfl) ⟨1964003, by rfl⟩ : syracuseStep 2618671 = 3928007) B3928007
theorem B3491561 : Blo 1911435 3491561 := bstep (se 2 (by rfl) ⟨1309335, by rfl⟩ : syracuseStep 3491561 = 2618671) B2618671
theorem B2327707 : Blo 1911435 2327707 := bstep (se 1 (by rfl) ⟨1745780, by rfl⟩ : syracuseStep 2327707 = 3491561) B3491561
theorem B3103609 : Blo 1911435 3103609 := bstep (se 2 (by rfl) ⟨1163853, by rfl⟩ : syracuseStep 3103609 = 2327707) B2327707
theorem B4138145 : Blo 1911435 4138145 := bstep (se 2 (by rfl) ⟨1551804, by rfl⟩ : syracuseStep 4138145 = 3103609) B3103609
theorem B2758763 : Blo 1911435 2758763 := bstep (se 1 (by rfl) ⟨2069072, by rfl⟩ : syracuseStep 2758763 = 4138145) B4138145
theorem B7356701 : Blo 1911435 7356701 := bstep (se 3 (by rfl) ⟨1379381, by rfl⟩ : syracuseStep 7356701 = 2758763) B2758763
theorem B19617869 : Blo 1911435 19617869 := bstep (se 3 (by rfl) ⟨3678350, by rfl⟩ : syracuseStep 19617869 = 7356701) B7356701
theorem B13078579 : Blo 1911435 13078579 := bstep (se 1 (by rfl) ⟨9808934, by rfl⟩ : syracuseStep 13078579 = 19617869) B19617869
theorem B17438105 : Blo 1911435 17438105 := bstep (se 2 (by rfl) ⟨6539289, by rfl⟩ : syracuseStep 17438105 = 13078579) B13078579
theorem B46501613 : Blo 1911435 46501613 := bstep (se 3 (by rfl) ⟨8719052, by rfl⟩ : syracuseStep 46501613 = 17438105) B17438105
theorem B31001075 : Blo 1911435 31001075 := bstep (se 1 (by rfl) ⟨23250806, by rfl⟩ : syracuseStep 31001075 = 46501613) B46501613
theorem B20667383 : Blo 1911435 20667383 := bstep (se 1 (by rfl) ⟨15500537, by rfl⟩ : syracuseStep 20667383 = 31001075) B31001075
theorem B13778255 : Blo 1911435 13778255 := bstep (se 1 (by rfl) ⟨10333691, by rfl⟩ : syracuseStep 13778255 = 20667383) B20667383
theorem B9185503 : Blo 1911435 9185503 := bstep (se 1 (by rfl) ⟨6889127, by rfl⟩ : syracuseStep 9185503 = 13778255) B13778255
theorem B12247337 : Blo 1911435 12247337 := bstep (se 2 (by rfl) ⟨4592751, by rfl⟩ : syracuseStep 12247337 = 9185503) B9185503
theorem B8164891 : Blo 1911435 8164891 := bstep (se 1 (by rfl) ⟨6123668, by rfl⟩ : syracuseStep 8164891 = 12247337) B12247337
theorem B10886521 : Blo 1911435 10886521 := bstep (se 2 (by rfl) ⟨4082445, by rfl⟩ : syracuseStep 10886521 = 8164891) B8164891
theorem B14515361 : Blo 1911435 14515361 := bstep (se 2 (by rfl) ⟨5443260, by rfl⟩ : syracuseStep 14515361 = 10886521) B10886521
theorem B9676907 : Blo 1911435 9676907 := bstep (se 1 (by rfl) ⟨7257680, by rfl⟩ : syracuseStep 9676907 = 14515361) B14515361
theorem B6451271 : Blo 1911435 6451271 := bstep (se 1 (by rfl) ⟨4838453, by rfl⟩ : syracuseStep 6451271 = 9676907) B9676907
theorem B4300847 : Blo 1911435 4300847 := bstep (se 1 (by rfl) ⟨3225635, by rfl⟩ : syracuseStep 4300847 = 6451271) B6451271
theorem B2867231 : Blo 1911435 2867231 := bstep (se 1 (by rfl) ⟨2150423, by rfl⟩ : syracuseStep 2867231 = 4300847) B4300847
theorem B1911487 : Blo 1911435 1911487 := bstep (se 1 (by rfl) ⟨1433615, by rfl⟩ : syracuseStep 1911487 = 2867231) B2867231
theorem B2867237 : Blo 1911435 2867237 := bbase (se 4 (by rfl) ⟨268803, by rfl⟩ : syracuseStep 2867237 = 537607) (by norm_num)
theorem B1911491 : Blo 1911435 1911491 := bstep (se 1 (by rfl) ⟨1433618, by rfl⟩ : syracuseStep 1911491 = 2867237) B2867237
theorem B2419237 : Blo 1911435 2419237 := bbase (se 4 (by rfl) ⟨226803, by rfl⟩ : syracuseStep 2419237 = 453607) (by norm_num)
theorem B3225649 : Blo 1911435 3225649 := bstep (se 2 (by rfl) ⟨1209618, by rfl⟩ : syracuseStep 3225649 = 2419237) B2419237
theorem B4300865 : Blo 1911435 4300865 := bstep (se 2 (by rfl) ⟨1612824, by rfl⟩ : syracuseStep 4300865 = 3225649) B3225649
theorem B2867243 : Blo 1911435 2867243 := bstep (se 1 (by rfl) ⟨2150432, by rfl⟩ : syracuseStep 2867243 = 4300865) B4300865
theorem B1911495 : Blo 1911435 1911495 := bstep (se 1 (by rfl) ⟨1433621, by rfl⟩ : syracuseStep 1911495 = 2867243) B2867243
theorem B2150437 : Blo 1911435 2150437 := bbase (se 4 (by rfl) ⟨201603, by rfl⟩ : syracuseStep 2150437 = 403207) (by norm_num)
theorem B2867249 : Blo 1911435 2867249 := bstep (se 2 (by rfl) ⟨1075218, by rfl⟩ : syracuseStep 2867249 = 2150437) B2150437
theorem B1911499 : Blo 1911435 1911499 := bstep (se 1 (by rfl) ⟨1433624, by rfl⟩ : syracuseStep 1911499 = 2867249) B2867249
theorem B10333781 : Blo 1911435 10333781 := bbase (se 8 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 10333781 = 121099) (by norm_num)
theorem B6889187 : Blo 1911435 6889187 := bstep (se 1 (by rfl) ⟨5166890, by rfl⟩ : syracuseStep 6889187 = 10333781) B10333781
theorem B4592791 : Blo 1911435 4592791 := bstep (se 1 (by rfl) ⟨3444593, by rfl⟩ : syracuseStep 4592791 = 6889187) B6889187
theorem B6123721 : Blo 1911435 6123721 := bstep (se 2 (by rfl) ⟨2296395, by rfl⟩ : syracuseStep 6123721 = 4592791) B4592791
theorem B8164961 : Blo 1911435 8164961 := bstep (se 2 (by rfl) ⟨3061860, by rfl⟩ : syracuseStep 8164961 = 6123721) B6123721
theorem B5443307 : Blo 1911435 5443307 := bstep (se 1 (by rfl) ⟨4082480, by rfl⟩ : syracuseStep 5443307 = 8164961) B8164961
theorem B3628871 : Blo 1911435 3628871 := bstep (se 1 (by rfl) ⟨2721653, by rfl⟩ : syracuseStep 3628871 = 5443307) B5443307
theorem B2419247 : Blo 1911435 2419247 := bstep (se 1 (by rfl) ⟨1814435, by rfl⟩ : syracuseStep 2419247 = 3628871) B3628871
theorem B6451325 : Blo 1911435 6451325 := bstep (se 3 (by rfl) ⟨1209623, by rfl⟩ : syracuseStep 6451325 = 2419247) B2419247
theorem B4300883 : Blo 1911435 4300883 := bstep (se 1 (by rfl) ⟨3225662, by rfl⟩ : syracuseStep 4300883 = 6451325) B6451325
theorem B2867255 : Blo 1911435 2867255 := bstep (se 1 (by rfl) ⟨2150441, by rfl⟩ : syracuseStep 2867255 = 4300883) B4300883
theorem B1911503 : Blo 1911435 1911503 := bstep (se 1 (by rfl) ⟨1433627, by rfl⟩ : syracuseStep 1911503 = 2867255) B2867255
theorem B2867261 : Blo 1911435 2867261 := bbase (se 3 (by rfl) ⟨537611, by rfl⟩ : syracuseStep 2867261 = 1075223) (by norm_num)
theorem B1911507 : Blo 1911435 1911507 := bstep (se 1 (by rfl) ⟨1433630, by rfl⟩ : syracuseStep 1911507 = 2867261) B2867261
theorem B4300901 : Blo 1911435 4300901 := bbase (se 4 (by rfl) ⟨403209, by rfl⟩ : syracuseStep 4300901 = 806419) (by norm_num)
theorem B2867267 : Blo 1911435 2867267 := bstep (se 1 (by rfl) ⟨2150450, by rfl⟩ : syracuseStep 2867267 = 4300901) B4300901
theorem B1911511 : Blo 1911435 1911511 := bstep (se 1 (by rfl) ⟨1433633, by rfl⟩ : syracuseStep 1911511 = 2867267) B2867267
theorem B4838525 : Blo 1911435 4838525 := bbase (se 3 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 4838525 = 1814447) (by norm_num)
theorem B3225683 : Blo 1911435 3225683 := bstep (se 1 (by rfl) ⟨2419262, by rfl⟩ : syracuseStep 3225683 = 4838525) B4838525
theorem B2150455 : Blo 1911435 2150455 := bstep (se 1 (by rfl) ⟨1612841, by rfl⟩ : syracuseStep 2150455 = 3225683) B3225683
theorem B2867273 : Blo 1911435 2867273 := bstep (se 2 (by rfl) ⟨1075227, by rfl⟩ : syracuseStep 2867273 = 2150455) B2150455
theorem B1911515 : Blo 1911435 1911515 := bstep (se 1 (by rfl) ⟨1433636, by rfl⟩ : syracuseStep 1911515 = 2867273) B2867273
theorem B3628901 : Blo 1911435 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B9677069 : Blo 1911435 9677069 := bstep (se 3 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 9677069 = 3628901) B3628901
theorem B6451379 : Blo 1911435 6451379 := bstep (se 1 (by rfl) ⟨4838534, by rfl⟩ : syracuseStep 6451379 = 9677069) B9677069
theorem B4300919 : Blo 1911435 4300919 := bstep (se 1 (by rfl) ⟨3225689, by rfl⟩ : syracuseStep 4300919 = 6451379) B6451379
theorem B2867279 : Blo 1911435 2867279 := bstep (se 1 (by rfl) ⟨2150459, by rfl⟩ : syracuseStep 2867279 = 4300919) B4300919
theorem B1911519 : Blo 1911435 1911519 := bstep (se 1 (by rfl) ⟨1433639, by rfl⟩ : syracuseStep 1911519 = 2867279) B2867279
theorem B2867285 : Blo 1911435 2867285 := bbase (se 8 (by rfl) ⟨16800, by rfl⟩ : syracuseStep 2867285 = 33601) (by norm_num)
theorem B1911523 : Blo 1911435 1911523 := bstep (se 1 (by rfl) ⟨1433642, by rfl⟩ : syracuseStep 1911523 = 2867285) B2867285
theorem B10333909 : Blo 1911435 10333909 := bbase (se 7 (by rfl) ⟨121100, by rfl⟩ : syracuseStep 10333909 = 242201) (by norm_num)
theorem B13778545 : Blo 1911435 13778545 := bstep (se 2 (by rfl) ⟨5166954, by rfl⟩ : syracuseStep 13778545 = 10333909) B10333909
theorem B18371393 : Blo 1911435 18371393 := bstep (se 2 (by rfl) ⟨6889272, by rfl⟩ : syracuseStep 18371393 = 13778545) B13778545
theorem B12247595 : Blo 1911435 12247595 := bstep (se 1 (by rfl) ⟨9185696, by rfl⟩ : syracuseStep 12247595 = 18371393) B18371393
theorem B8165063 : Blo 1911435 8165063 := bstep (se 1 (by rfl) ⟨6123797, by rfl⟩ : syracuseStep 8165063 = 12247595) B12247595
theorem B5443375 : Blo 1911435 5443375 := bstep (se 1 (by rfl) ⟨4082531, by rfl⟩ : syracuseStep 5443375 = 8165063) B8165063
theorem B7257833 : Blo 1911435 7257833 := bstep (se 2 (by rfl) ⟨2721687, by rfl⟩ : syracuseStep 7257833 = 5443375) B5443375
theorem B4838555 : Blo 1911435 4838555 := bstep (se 1 (by rfl) ⟨3628916, by rfl⟩ : syracuseStep 4838555 = 7257833) B7257833
theorem B3225703 : Blo 1911435 3225703 := bstep (se 1 (by rfl) ⟨2419277, by rfl⟩ : syracuseStep 3225703 = 4838555) B4838555
theorem B4300937 : Blo 1911435 4300937 := bstep (se 2 (by rfl) ⟨1612851, by rfl⟩ : syracuseStep 4300937 = 3225703) B3225703
theorem B2867291 : Blo 1911435 2867291 := bstep (se 1 (by rfl) ⟨2150468, by rfl⟩ : syracuseStep 2867291 = 4300937) B4300937
theorem B1911527 : Blo 1911435 1911527 := bstep (se 1 (by rfl) ⟨1433645, by rfl⟩ : syracuseStep 1911527 = 2867291) B2867291
theorem B2150473 : Blo 1911435 2150473 := bbase (se 2 (by rfl) ⟨806427, by rfl⟩ : syracuseStep 2150473 = 1612855) (by norm_num)
theorem B2867297 : Blo 1911435 2867297 := bstep (se 2 (by rfl) ⟨1075236, by rfl⟩ : syracuseStep 2867297 = 2150473) B2150473
theorem B1911531 : Blo 1911435 1911531 := bstep (se 1 (by rfl) ⟨1433648, by rfl⟩ : syracuseStep 1911531 = 2867297) B2867297
theorem B6889301 : Blo 1911435 6889301 := bbase (se 9 (by rfl) ⟨20183, by rfl⟩ : syracuseStep 6889301 = 40367) (by norm_num)
theorem B4592867 : Blo 1911435 4592867 := bstep (se 1 (by rfl) ⟨3444650, by rfl⟩ : syracuseStep 4592867 = 6889301) B6889301
theorem B12247645 : Blo 1911435 12247645 := bstep (se 3 (by rfl) ⟨2296433, by rfl⟩ : syracuseStep 12247645 = 4592867) B4592867
theorem B16330193 : Blo 1911435 16330193 := bstep (se 2 (by rfl) ⟨6123822, by rfl⟩ : syracuseStep 16330193 = 12247645) B12247645
theorem B10886795 : Blo 1911435 10886795 := bstep (se 1 (by rfl) ⟨8165096, by rfl⟩ : syracuseStep 10886795 = 16330193) B16330193
theorem B7257863 : Blo 1911435 7257863 := bstep (se 1 (by rfl) ⟨5443397, by rfl⟩ : syracuseStep 7257863 = 10886795) B10886795
theorem B4838575 : Blo 1911435 4838575 := bstep (se 1 (by rfl) ⟨3628931, by rfl⟩ : syracuseStep 4838575 = 7257863) B7257863
theorem B6451433 : Blo 1911435 6451433 := bstep (se 2 (by rfl) ⟨2419287, by rfl⟩ : syracuseStep 6451433 = 4838575) B4838575
theorem B4300955 : Blo 1911435 4300955 := bstep (se 1 (by rfl) ⟨3225716, by rfl⟩ : syracuseStep 4300955 = 6451433) B6451433
theorem B2867303 : Blo 1911435 2867303 := bstep (se 1 (by rfl) ⟨2150477, by rfl⟩ : syracuseStep 2867303 = 4300955) B4300955
theorem B1911535 : Blo 1911435 1911535 := bstep (se 1 (by rfl) ⟨1433651, by rfl⟩ : syracuseStep 1911535 = 2867303) B2867303
theorem B2867309 : Blo 1911435 2867309 := bbase (se 3 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 2867309 = 1075241) (by norm_num)
theorem B1911539 : Blo 1911435 1911539 := bstep (se 1 (by rfl) ⟨1433654, by rfl⟩ : syracuseStep 1911539 = 2867309) B2867309
theorem B4300973 : Blo 1911435 4300973 := bbase (se 3 (by rfl) ⟨806432, by rfl⟩ : syracuseStep 4300973 = 1612865) (by norm_num)
theorem B2867315 : Blo 1911435 2867315 := bstep (se 1 (by rfl) ⟨2150486, by rfl⟩ : syracuseStep 2867315 = 4300973) B4300973
theorem B1911543 : Blo 1911435 1911543 := bstep (se 1 (by rfl) ⟨1433657, by rfl⟩ : syracuseStep 1911543 = 2867315) B2867315
theorem B1937629 : Blo 1911435 1937629 := bbase (se 3 (by rfl) ⟨363305, by rfl⟩ : syracuseStep 1937629 = 726611) (by norm_num)
theorem B2583505 : Blo 1911435 2583505 := bstep (se 2 (by rfl) ⟨968814, by rfl⟩ : syracuseStep 2583505 = 1937629) B1937629
theorem B13778693 : Blo 1911435 13778693 := bstep (se 4 (by rfl) ⟨1291752, by rfl⟩ : syracuseStep 13778693 = 2583505) B2583505
theorem B9185795 : Blo 1911435 9185795 := bstep (se 1 (by rfl) ⟨6889346, by rfl⟩ : syracuseStep 9185795 = 13778693) B13778693
theorem B6123863 : Blo 1911435 6123863 := bstep (se 1 (by rfl) ⟨4592897, by rfl⟩ : syracuseStep 6123863 = 9185795) B9185795
theorem B4082575 : Blo 1911435 4082575 := bstep (se 1 (by rfl) ⟨3061931, by rfl⟩ : syracuseStep 4082575 = 6123863) B6123863
theorem B5443433 : Blo 1911435 5443433 := bstep (se 2 (by rfl) ⟨2041287, by rfl⟩ : syracuseStep 5443433 = 4082575) B4082575
theorem B3628955 : Blo 1911435 3628955 := bstep (se 1 (by rfl) ⟨2721716, by rfl⟩ : syracuseStep 3628955 = 5443433) B5443433
theorem B2419303 : Blo 1911435 2419303 := bstep (se 1 (by rfl) ⟨1814477, by rfl⟩ : syracuseStep 2419303 = 3628955) B3628955
theorem B3225737 : Blo 1911435 3225737 := bstep (se 2 (by rfl) ⟨1209651, by rfl⟩ : syracuseStep 3225737 = 2419303) B2419303
theorem B2150491 : Blo 1911435 2150491 := bstep (se 1 (by rfl) ⟨1612868, by rfl⟩ : syracuseStep 2150491 = 3225737) B3225737
theorem B2867321 : Blo 1911435 2867321 := bstep (se 2 (by rfl) ⟨1075245, by rfl⟩ : syracuseStep 2867321 = 2150491) B2150491
theorem B1911547 : Blo 1911435 1911547 := bstep (se 1 (by rfl) ⟨1433660, by rfl⟩ : syracuseStep 1911547 = 2867321) B2867321
theorem B4138285 : Blo 1911435 4138285 := bbase (se 3 (by rfl) ⟨775928, by rfl⟩ : syracuseStep 4138285 = 1551857) (by norm_num)
theorem B5517713 : Blo 1911435 5517713 := bstep (se 2 (by rfl) ⟨2069142, by rfl⟩ : syracuseStep 5517713 = 4138285) B4138285
theorem B3678475 : Blo 1911435 3678475 := bstep (se 1 (by rfl) ⟨2758856, by rfl⟩ : syracuseStep 3678475 = 5517713) B5517713
theorem B4904633 : Blo 1911435 4904633 := bstep (se 2 (by rfl) ⟨1839237, by rfl⟩ : syracuseStep 4904633 = 3678475) B3678475
theorem B3269755 : Blo 1911435 3269755 := bstep (se 1 (by rfl) ⟨2452316, by rfl⟩ : syracuseStep 3269755 = 4904633) B4904633
theorem B4359673 : Blo 1911435 4359673 := bstep (se 2 (by rfl) ⟨1634877, by rfl⟩ : syracuseStep 4359673 = 3269755) B3269755
theorem B5812897 : Blo 1911435 5812897 := bstep (se 2 (by rfl) ⟨2179836, by rfl⟩ : syracuseStep 5812897 = 4359673) B4359673
theorem B7750529 : Blo 1911435 7750529 := bstep (se 2 (by rfl) ⟨2906448, by rfl⟩ : syracuseStep 7750529 = 5812897) B5812897
theorem B5167019 : Blo 1911435 5167019 := bstep (se 1 (by rfl) ⟨3875264, by rfl⟩ : syracuseStep 5167019 = 7750529) B7750529
theorem B3444679 : Blo 1911435 3444679 := bstep (se 1 (by rfl) ⟨2583509, by rfl⟩ : syracuseStep 3444679 = 5167019) B5167019
theorem B4592905 : Blo 1911435 4592905 := bstep (se 2 (by rfl) ⟨1722339, by rfl⟩ : syracuseStep 4592905 = 3444679) B3444679
theorem B24495493 : Blo 1911435 24495493 := bstep (se 4 (by rfl) ⟨2296452, by rfl⟩ : syracuseStep 24495493 = 4592905) B4592905
theorem B32660657 : Blo 1911435 32660657 := bstep (se 2 (by rfl) ⟨12247746, by rfl⟩ : syracuseStep 32660657 = 24495493) B24495493
theorem B21773771 : Blo 1911435 21773771 := bstep (se 1 (by rfl) ⟨16330328, by rfl⟩ : syracuseStep 21773771 = 32660657) B32660657
theorem B14515847 : Blo 1911435 14515847 := bstep (se 1 (by rfl) ⟨10886885, by rfl⟩ : syracuseStep 14515847 = 21773771) B21773771
theorem B9677231 : Blo 1911435 9677231 := bstep (se 1 (by rfl) ⟨7257923, by rfl⟩ : syracuseStep 9677231 = 14515847) B14515847
theorem B6451487 : Blo 1911435 6451487 := bstep (se 1 (by rfl) ⟨4838615, by rfl⟩ : syracuseStep 6451487 = 9677231) B9677231
theorem B4300991 : Blo 1911435 4300991 := bstep (se 1 (by rfl) ⟨3225743, by rfl⟩ : syracuseStep 4300991 = 6451487) B6451487
theorem B2867327 : Blo 1911435 2867327 := bstep (se 1 (by rfl) ⟨2150495, by rfl⟩ : syracuseStep 2867327 = 4300991) B4300991
theorem B1911551 : Blo 1911435 1911551 := bstep (se 1 (by rfl) ⟨1433663, by rfl⟩ : syracuseStep 1911551 = 2867327) B2867327
theorem B2867333 : Blo 1911435 2867333 := bbase (se 4 (by rfl) ⟨268812, by rfl⟩ : syracuseStep 2867333 = 537625) (by norm_num)
theorem B1911555 : Blo 1911435 1911555 := bstep (se 1 (by rfl) ⟨1433666, by rfl⟩ : syracuseStep 1911555 = 2867333) B2867333
theorem B3225757 : Blo 1911435 3225757 := bbase (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) (by norm_num)
theorem B4301009 : Blo 1911435 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2867339 : Blo 1911435 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B1911559 : Blo 1911435 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B2150509 : Blo 1911435 2150509 := bbase (se 3 (by rfl) ⟨403220, by rfl⟩ : syracuseStep 2150509 = 806441) (by norm_num)
theorem B2867345 : Blo 1911435 2867345 := bstep (se 2 (by rfl) ⟨1075254, by rfl⟩ : syracuseStep 2867345 = 2150509) B2150509
theorem B1911563 : Blo 1911435 1911563 := bstep (se 1 (by rfl) ⟨1433672, by rfl⟩ : syracuseStep 1911563 = 2867345) B2867345
theorem B6451541 : Blo 1911435 6451541 := bbase (se 10 (by rfl) ⟨9450, by rfl⟩ : syracuseStep 6451541 = 18901) (by norm_num)
theorem B4301027 : Blo 1911435 4301027 := bstep (se 1 (by rfl) ⟨3225770, by rfl⟩ : syracuseStep 4301027 = 6451541) B6451541
theorem B2867351 : Blo 1911435 2867351 := bstep (se 1 (by rfl) ⟨2150513, by rfl⟩ : syracuseStep 2867351 = 4301027) B4301027
theorem B1911567 : Blo 1911435 1911567 := bstep (se 1 (by rfl) ⟨1433675, by rfl⟩ : syracuseStep 1911567 = 2867351) B2867351
theorem B2867357 : Blo 1911435 2867357 := bbase (se 3 (by rfl) ⟨537629, by rfl⟩ : syracuseStep 2867357 = 1075259) (by norm_num)
theorem B1911571 : Blo 1911435 1911571 := bstep (se 1 (by rfl) ⟨1433678, by rfl⟩ : syracuseStep 1911571 = 2867357) B2867357
theorem B4301045 : Blo 1911435 4301045 := bbase (se 5 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 4301045 = 403223) (by norm_num)
theorem B2867363 : Blo 1911435 2867363 := bstep (se 1 (by rfl) ⟨2150522, by rfl⟩ : syracuseStep 2867363 = 4301045) B4301045
theorem B1911575 : Blo 1911435 1911575 := bstep (se 1 (by rfl) ⟨1433681, by rfl⟩ : syracuseStep 1911575 = 2867363) B2867363
theorem B18371893 : Blo 1911435 18371893 := bbase (se 5 (by rfl) ⟨861182, by rfl⟩ : syracuseStep 18371893 = 1722365) (by norm_num)
theorem B24495857 : Blo 1911435 24495857 := bstep (se 2 (by rfl) ⟨9185946, by rfl⟩ : syracuseStep 24495857 = 18371893) B18371893
theorem B16330571 : Blo 1911435 16330571 := bstep (se 1 (by rfl) ⟨12247928, by rfl⟩ : syracuseStep 16330571 = 24495857) B24495857
theorem B10887047 : Blo 1911435 10887047 := bstep (se 1 (by rfl) ⟨8165285, by rfl⟩ : syracuseStep 10887047 = 16330571) B16330571
theorem B7258031 : Blo 1911435 7258031 := bstep (se 1 (by rfl) ⟨5443523, by rfl⟩ : syracuseStep 7258031 = 10887047) B10887047
theorem B4838687 : Blo 1911435 4838687 := bstep (se 1 (by rfl) ⟨3629015, by rfl⟩ : syracuseStep 4838687 = 7258031) B7258031
theorem B3225791 : Blo 1911435 3225791 := bstep (se 1 (by rfl) ⟨2419343, by rfl⟩ : syracuseStep 3225791 = 4838687) B4838687
theorem B2150527 : Blo 1911435 2150527 := bstep (se 1 (by rfl) ⟨1612895, by rfl⟩ : syracuseStep 2150527 = 3225791) B3225791
theorem B2867369 : Blo 1911435 2867369 := bstep (se 2 (by rfl) ⟨1075263, by rfl⟩ : syracuseStep 2867369 = 2150527) B2150527
theorem B1911579 : Blo 1911435 1911579 := bstep (se 1 (by rfl) ⟨1433684, by rfl⟩ : syracuseStep 1911579 = 2867369) B2867369
theorem B1937665 : Blo 1911435 1937665 := bbase (se 2 (by rfl) ⟨726624, by rfl⟩ : syracuseStep 1937665 = 1453249) (by norm_num)
theorem B10334213 : Blo 1911435 10334213 := bstep (se 4 (by rfl) ⟨968832, by rfl⟩ : syracuseStep 10334213 = 1937665) B1937665
theorem B6889475 : Blo 1911435 6889475 := bstep (se 1 (by rfl) ⟨5167106, by rfl⟩ : syracuseStep 6889475 = 10334213) B10334213
theorem B4592983 : Blo 1911435 4592983 := bstep (se 1 (by rfl) ⟨3444737, by rfl⟩ : syracuseStep 4592983 = 6889475) B6889475
theorem B6123977 : Blo 1911435 6123977 := bstep (se 2 (by rfl) ⟨2296491, by rfl⟩ : syracuseStep 6123977 = 4592983) B4592983
theorem B4082651 : Blo 1911435 4082651 := bstep (se 1 (by rfl) ⟨3061988, by rfl⟩ : syracuseStep 4082651 = 6123977) B6123977
theorem B2721767 : Blo 1911435 2721767 := bstep (se 1 (by rfl) ⟨2041325, by rfl⟩ : syracuseStep 2721767 = 4082651) B4082651
theorem B7258045 : Blo 1911435 7258045 := bstep (se 3 (by rfl) ⟨1360883, by rfl⟩ : syracuseStep 7258045 = 2721767) B2721767
theorem B9677393 : Blo 1911435 9677393 := bstep (se 2 (by rfl) ⟨3629022, by rfl⟩ : syracuseStep 9677393 = 7258045) B7258045
theorem B6451595 : Blo 1911435 6451595 := bstep (se 1 (by rfl) ⟨4838696, by rfl⟩ : syracuseStep 6451595 = 9677393) B9677393
theorem B4301063 : Blo 1911435 4301063 := bstep (se 1 (by rfl) ⟨3225797, by rfl⟩ : syracuseStep 4301063 = 6451595) B6451595
theorem B2867375 : Blo 1911435 2867375 := bstep (se 1 (by rfl) ⟨2150531, by rfl⟩ : syracuseStep 2867375 = 4301063) B4301063
theorem B1911583 : Blo 1911435 1911583 := bstep (se 1 (by rfl) ⟨1433687, by rfl⟩ : syracuseStep 1911583 = 2867375) B2867375
theorem B2867381 : Blo 1911435 2867381 := bbase (se 5 (by rfl) ⟨134408, by rfl⟩ : syracuseStep 2867381 = 268817) (by norm_num)
theorem B1911587 : Blo 1911435 1911587 := bstep (se 1 (by rfl) ⟨1433690, by rfl⟩ : syracuseStep 1911587 = 2867381) B2867381
theorem B4838717 : Blo 1911435 4838717 := bbase (se 3 (by rfl) ⟨907259, by rfl⟩ : syracuseStep 4838717 = 1814519) (by norm_num)
theorem B3225811 : Blo 1911435 3225811 := bstep (se 1 (by rfl) ⟨2419358, by rfl⟩ : syracuseStep 3225811 = 4838717) B4838717
theorem B4301081 : Blo 1911435 4301081 := bstep (se 2 (by rfl) ⟨1612905, by rfl⟩ : syracuseStep 4301081 = 3225811) B3225811
theorem B2867387 : Blo 1911435 2867387 := bstep (se 1 (by rfl) ⟨2150540, by rfl⟩ : syracuseStep 2867387 = 4301081) B4301081
theorem B1911591 : Blo 1911435 1911591 := bstep (se 1 (by rfl) ⟨1433693, by rfl⟩ : syracuseStep 1911591 = 2867387) B2867387
theorem B2150545 : Blo 1911435 2150545 := bbase (se 2 (by rfl) ⟨806454, by rfl⟩ : syracuseStep 2150545 = 1612909) (by norm_num)
theorem B2867393 : Blo 1911435 2867393 := bstep (se 2 (by rfl) ⟨1075272, by rfl⟩ : syracuseStep 2867393 = 2150545) B2150545
theorem B1911595 : Blo 1911435 1911595 := bstep (se 1 (by rfl) ⟨1433696, by rfl⟩ : syracuseStep 1911595 = 2867393) B2867393
theorem B3629053 : Blo 1911435 3629053 := bbase (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) (by norm_num)
theorem B4838737 : Blo 1911435 4838737 := bstep (se 2 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 4838737 = 3629053) B3629053
theorem B6451649 : Blo 1911435 6451649 := bstep (se 2 (by rfl) ⟨2419368, by rfl⟩ : syracuseStep 6451649 = 4838737) B4838737
theorem B4301099 : Blo 1911435 4301099 := bstep (se 1 (by rfl) ⟨3225824, by rfl⟩ : syracuseStep 4301099 = 6451649) B6451649
theorem B2867399 : Blo 1911435 2867399 := bstep (se 1 (by rfl) ⟨2150549, by rfl⟩ : syracuseStep 2867399 = 4301099) B4301099
theorem B1911599 : Blo 1911435 1911599 := bstep (se 1 (by rfl) ⟨1433699, by rfl⟩ : syracuseStep 1911599 = 2867399) B2867399
theorem B2867405 : Blo 1911435 2867405 := bbase (se 3 (by rfl) ⟨537638, by rfl⟩ : syracuseStep 2867405 = 1075277) (by norm_num)
theorem B1911603 : Blo 1911435 1911603 := bstep (se 1 (by rfl) ⟨1433702, by rfl⟩ : syracuseStep 1911603 = 2867405) B2867405
theorem B4301117 : Blo 1911435 4301117 := bbase (se 3 (by rfl) ⟨806459, by rfl⟩ : syracuseStep 4301117 = 1612919) (by norm_num)
theorem B2867411 : Blo 1911435 2867411 := bstep (se 1 (by rfl) ⟨2150558, by rfl⟩ : syracuseStep 2867411 = 4301117) B4301117
theorem B1911607 : Blo 1911435 1911607 := bstep (se 1 (by rfl) ⟨1433705, by rfl⟩ : syracuseStep 1911607 = 2867411) B2867411
theorem B3225845 : Blo 1911435 3225845 := bbase (se 5 (by rfl) ⟨151211, by rfl⟩ : syracuseStep 3225845 = 302423) (by norm_num)
theorem B2150563 : Blo 1911435 2150563 := bstep (se 1 (by rfl) ⟨1612922, by rfl⟩ : syracuseStep 2150563 = 3225845) B3225845
theorem B2867417 : Blo 1911435 2867417 := bstep (se 2 (by rfl) ⟨1075281, by rfl⟩ : syracuseStep 2867417 = 2150563) B2150563
theorem B1911611 : Blo 1911435 1911611 := bstep (se 1 (by rfl) ⟨1433708, by rfl⟩ : syracuseStep 1911611 = 2867417) B2867417
theorem B14714389 : Blo 1911435 14714389 := bbase (se 6 (by rfl) ⟨344868, by rfl⟩ : syracuseStep 14714389 = 689737) (by norm_num)
theorem B19619185 : Blo 1911435 19619185 := bstep (se 2 (by rfl) ⟨7357194, by rfl⟩ : syracuseStep 19619185 = 14714389) B14714389
theorem B26158913 : Blo 1911435 26158913 := bstep (se 2 (by rfl) ⟨9809592, by rfl⟩ : syracuseStep 26158913 = 19619185) B19619185
theorem B17439275 : Blo 1911435 17439275 := bstep (se 1 (by rfl) ⟨13079456, by rfl⟩ : syracuseStep 17439275 = 26158913) B26158913
theorem B11626183 : Blo 1911435 11626183 := bstep (se 1 (by rfl) ⟨8719637, by rfl⟩ : syracuseStep 11626183 = 17439275) B17439275
theorem B15501577 : Blo 1911435 15501577 := bstep (se 2 (by rfl) ⟨5813091, by rfl⟩ : syracuseStep 15501577 = 11626183) B11626183
theorem B20668769 : Blo 1911435 20668769 := bstep (se 2 (by rfl) ⟨7750788, by rfl⟩ : syracuseStep 20668769 = 15501577) B15501577
theorem B13779179 : Blo 1911435 13779179 := bstep (se 1 (by rfl) ⟨10334384, by rfl⟩ : syracuseStep 13779179 = 20668769) B20668769
theorem B9186119 : Blo 1911435 9186119 := bstep (se 1 (by rfl) ⟨6889589, by rfl⟩ : syracuseStep 9186119 = 13779179) B13779179
theorem B6124079 : Blo 1911435 6124079 := bstep (se 1 (by rfl) ⟨4593059, by rfl⟩ : syracuseStep 6124079 = 9186119) B9186119
theorem B4082719 : Blo 1911435 4082719 := bstep (se 1 (by rfl) ⟨3062039, by rfl⟩ : syracuseStep 4082719 = 6124079) B6124079
theorem B5443625 : Blo 1911435 5443625 := bstep (se 2 (by rfl) ⟨2041359, by rfl⟩ : syracuseStep 5443625 = 4082719) B4082719
theorem B14516333 : Blo 1911435 14516333 := bstep (se 3 (by rfl) ⟨2721812, by rfl⟩ : syracuseStep 14516333 = 5443625) B5443625
theorem B9677555 : Blo 1911435 9677555 := bstep (se 1 (by rfl) ⟨7258166, by rfl⟩ : syracuseStep 9677555 = 14516333) B14516333
theorem B6451703 : Blo 1911435 6451703 := bstep (se 1 (by rfl) ⟨4838777, by rfl⟩ : syracuseStep 6451703 = 9677555) B9677555
theorem B4301135 : Blo 1911435 4301135 := bstep (se 1 (by rfl) ⟨3225851, by rfl⟩ : syracuseStep 4301135 = 6451703) B6451703
theorem B2867423 : Blo 1911435 2867423 := bstep (se 1 (by rfl) ⟨2150567, by rfl⟩ : syracuseStep 2867423 = 4301135) B4301135
theorem B1911615 : Blo 1911435 1911615 := bstep (se 1 (by rfl) ⟨1433711, by rfl⟩ : syracuseStep 1911615 = 2867423) B2867423
theorem B2867429 : Blo 1911435 2867429 := bbase (se 4 (by rfl) ⟨268821, by rfl⟩ : syracuseStep 2867429 = 537643) (by norm_num)
theorem B1911619 : Blo 1911435 1911619 := bstep (se 1 (by rfl) ⟨1433714, by rfl⟩ : syracuseStep 1911619 = 2867429) B2867429
theorem B3062053 : Blo 1911435 3062053 := bbase (se 4 (by rfl) ⟨287067, by rfl⟩ : syracuseStep 3062053 = 574135) (by norm_num)
theorem B4082737 : Blo 1911435 4082737 := bstep (se 2 (by rfl) ⟨1531026, by rfl⟩ : syracuseStep 4082737 = 3062053) B3062053
theorem B5443649 : Blo 1911435 5443649 := bstep (se 2 (by rfl) ⟨2041368, by rfl⟩ : syracuseStep 5443649 = 4082737) B4082737
theorem B3629099 : Blo 1911435 3629099 := bstep (se 1 (by rfl) ⟨2721824, by rfl⟩ : syracuseStep 3629099 = 5443649) B5443649
theorem B2419399 : Blo 1911435 2419399 := bstep (se 1 (by rfl) ⟨1814549, by rfl⟩ : syracuseStep 2419399 = 3629099) B3629099
theorem B3225865 : Blo 1911435 3225865 := bstep (se 2 (by rfl) ⟨1209699, by rfl⟩ : syracuseStep 3225865 = 2419399) B2419399
theorem B4301153 : Blo 1911435 4301153 := bstep (se 2 (by rfl) ⟨1612932, by rfl⟩ : syracuseStep 4301153 = 3225865) B3225865
theorem B2867435 : Blo 1911435 2867435 := bstep (se 1 (by rfl) ⟨2150576, by rfl⟩ : syracuseStep 2867435 = 4301153) B4301153
theorem B1911623 : Blo 1911435 1911623 := bstep (se 1 (by rfl) ⟨1433717, by rfl⟩ : syracuseStep 1911623 = 2867435) B2867435
theorem B2150581 : Blo 1911435 2150581 := bbase (se 5 (by rfl) ⟨100808, by rfl⟩ : syracuseStep 2150581 = 201617) (by norm_num)
theorem B2867441 : Blo 1911435 2867441 := bstep (se 2 (by rfl) ⟨1075290, by rfl⟩ : syracuseStep 2867441 = 2150581) B2150581
theorem B1911627 : Blo 1911435 1911627 := bstep (se 1 (by rfl) ⟨1433720, by rfl⟩ : syracuseStep 1911627 = 2867441) B2867441
theorem B2419409 : Blo 1911435 2419409 := bbase (se 2 (by rfl) ⟨907278, by rfl⟩ : syracuseStep 2419409 = 1814557) (by norm_num)
theorem B6451757 : Blo 1911435 6451757 := bstep (se 3 (by rfl) ⟨1209704, by rfl⟩ : syracuseStep 6451757 = 2419409) B2419409
theorem B4301171 : Blo 1911435 4301171 := bstep (se 1 (by rfl) ⟨3225878, by rfl⟩ : syracuseStep 4301171 = 6451757) B6451757
theorem B2867447 : Blo 1911435 2867447 := bstep (se 1 (by rfl) ⟨2150585, by rfl⟩ : syracuseStep 2867447 = 4301171) B4301171
theorem B1911631 : Blo 1911435 1911631 := bstep (se 1 (by rfl) ⟨1433723, by rfl⟩ : syracuseStep 1911631 = 2867447) B2867447
theorem B2867453 : Blo 1911435 2867453 := bbase (se 3 (by rfl) ⟨537647, by rfl⟩ : syracuseStep 2867453 = 1075295) (by norm_num)
theorem B1911635 : Blo 1911435 1911635 := bstep (se 1 (by rfl) ⟨1433726, by rfl⟩ : syracuseStep 1911635 = 2867453) B2867453
theorem B4301189 : Blo 1911435 4301189 := bbase (se 4 (by rfl) ⟨403236, by rfl⟩ : syracuseStep 4301189 = 806473) (by norm_num)
theorem B2867459 : Blo 1911435 2867459 := bstep (se 1 (by rfl) ⟨2150594, by rfl⟩ : syracuseStep 2867459 = 4301189) B4301189
theorem B1911639 : Blo 1911435 1911639 := bstep (se 1 (by rfl) ⟨1433729, by rfl⟩ : syracuseStep 1911639 = 2867459) B2867459
theorem B2721853 : Blo 1911435 2721853 := bbase (se 3 (by rfl) ⟨510347, by rfl⟩ : syracuseStep 2721853 = 1020695) (by norm_num)
theorem B3629137 : Blo 1911435 3629137 := bstep (se 2 (by rfl) ⟨1360926, by rfl⟩ : syracuseStep 3629137 = 2721853) B2721853
theorem B4838849 : Blo 1911435 4838849 := bstep (se 2 (by rfl) ⟨1814568, by rfl⟩ : syracuseStep 4838849 = 3629137) B3629137
theorem B3225899 : Blo 1911435 3225899 := bstep (se 1 (by rfl) ⟨2419424, by rfl⟩ : syracuseStep 3225899 = 4838849) B4838849
theorem B2150599 : Blo 1911435 2150599 := bstep (se 1 (by rfl) ⟨1612949, by rfl⟩ : syracuseStep 2150599 = 3225899) B3225899
theorem B2867465 : Blo 1911435 2867465 := bstep (se 2 (by rfl) ⟨1075299, by rfl⟩ : syracuseStep 2867465 = 2150599) B2150599
theorem B1911643 : Blo 1911435 1911643 := bstep (se 1 (by rfl) ⟨1433732, by rfl⟩ : syracuseStep 1911643 = 2867465) B2867465
theorem B9677717 : Blo 1911435 9677717 := bbase (se 6 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 9677717 = 453643) (by norm_num)
theorem B6451811 : Blo 1911435 6451811 := bstep (se 1 (by rfl) ⟨4838858, by rfl⟩ : syracuseStep 6451811 = 9677717) B9677717
theorem B4301207 : Blo 1911435 4301207 := bstep (se 1 (by rfl) ⟨3225905, by rfl⟩ : syracuseStep 4301207 = 6451811) B6451811
theorem B2867471 : Blo 1911435 2867471 := bstep (se 1 (by rfl) ⟨2150603, by rfl⟩ : syracuseStep 2867471 = 4301207) B4301207
theorem B1911647 : Blo 1911435 1911647 := bstep (se 1 (by rfl) ⟨1433735, by rfl⟩ : syracuseStep 1911647 = 2867471) B2867471
theorem B2867477 : Blo 1911435 2867477 := bbase (se 6 (by rfl) ⟨67206, by rfl⟩ : syracuseStep 2867477 = 134413) (by norm_num)
theorem B1911651 : Blo 1911435 1911651 := bstep (se 1 (by rfl) ⟨1433738, by rfl⟩ : syracuseStep 1911651 = 2867477) B2867477
theorem B3269933 : Blo 1911435 3269933 := bbase (se 3 (by rfl) ⟨613112, by rfl⟩ : syracuseStep 3269933 = 1226225) (by norm_num)
theorem B2179955 : Blo 1911435 2179955 := bstep (se 1 (by rfl) ⟨1634966, by rfl⟩ : syracuseStep 2179955 = 3269933) B3269933
theorem B5813213 : Blo 1911435 5813213 := bstep (se 3 (by rfl) ⟨1089977, by rfl⟩ : syracuseStep 5813213 = 2179955) B2179955
theorem B15501901 : Blo 1911435 15501901 := bstep (se 3 (by rfl) ⟨2906606, by rfl⟩ : syracuseStep 15501901 = 5813213) B5813213
theorem B20669201 : Blo 1911435 20669201 := bstep (se 2 (by rfl) ⟨7750950, by rfl⟩ : syracuseStep 20669201 = 15501901) B15501901
theorem B13779467 : Blo 1911435 13779467 := bstep (se 1 (by rfl) ⟨10334600, by rfl⟩ : syracuseStep 13779467 = 20669201) B20669201
theorem B9186311 : Blo 1911435 9186311 := bstep (se 1 (by rfl) ⟨6889733, by rfl⟩ : syracuseStep 9186311 = 13779467) B13779467
theorem B24496829 : Blo 1911435 24496829 := bstep (se 3 (by rfl) ⟨4593155, by rfl⟩ : syracuseStep 24496829 = 9186311) B9186311
theorem B16331219 : Blo 1911435 16331219 := bstep (se 1 (by rfl) ⟨12248414, by rfl⟩ : syracuseStep 16331219 = 24496829) B24496829
theorem B10887479 : Blo 1911435 10887479 := bstep (se 1 (by rfl) ⟨8165609, by rfl⟩ : syracuseStep 10887479 = 16331219) B16331219
theorem B7258319 : Blo 1911435 7258319 := bstep (se 1 (by rfl) ⟨5443739, by rfl⟩ : syracuseStep 7258319 = 10887479) B10887479
theorem B4838879 : Blo 1911435 4838879 := bstep (se 1 (by rfl) ⟨3629159, by rfl⟩ : syracuseStep 4838879 = 7258319) B7258319
theorem B3225919 : Blo 1911435 3225919 := bstep (se 1 (by rfl) ⟨2419439, by rfl⟩ : syracuseStep 3225919 = 4838879) B4838879
theorem B4301225 : Blo 1911435 4301225 := bstep (se 2 (by rfl) ⟨1612959, by rfl⟩ : syracuseStep 4301225 = 3225919) B3225919
theorem B2867483 : Blo 1911435 2867483 := bstep (se 1 (by rfl) ⟨2150612, by rfl⟩ : syracuseStep 2867483 = 4301225) B4301225
theorem B1911655 : Blo 1911435 1911655 := bstep (se 1 (by rfl) ⟨1433741, by rfl⟩ : syracuseStep 1911655 = 2867483) B2867483
theorem B2150617 : Blo 1911435 2150617 := bbase (se 2 (by rfl) ⟨806481, by rfl⟩ : syracuseStep 2150617 = 1612963) (by norm_num)
theorem B2867489 : Blo 1911435 2867489 := bstep (se 2 (by rfl) ⟨1075308, by rfl⟩ : syracuseStep 2867489 = 2150617) B2150617
theorem B1911659 : Blo 1911435 1911659 := bstep (se 1 (by rfl) ⟨1433744, by rfl⟩ : syracuseStep 1911659 = 2867489) B2867489
theorem B3062117 : Blo 1911435 3062117 := bbase (se 4 (by rfl) ⟨287073, by rfl⟩ : syracuseStep 3062117 = 574147) (by norm_num)
theorem B2041411 : Blo 1911435 2041411 := bstep (se 1 (by rfl) ⟨1531058, by rfl⟩ : syracuseStep 2041411 = 3062117) B3062117
theorem B2721881 : Blo 1911435 2721881 := bstep (se 2 (by rfl) ⟨1020705, by rfl⟩ : syracuseStep 2721881 = 2041411) B2041411
theorem B7258349 : Blo 1911435 7258349 := bstep (se 3 (by rfl) ⟨1360940, by rfl⟩ : syracuseStep 7258349 = 2721881) B2721881
theorem B4838899 : Blo 1911435 4838899 := bstep (se 1 (by rfl) ⟨3629174, by rfl⟩ : syracuseStep 4838899 = 7258349) B7258349
theorem B6451865 : Blo 1911435 6451865 := bstep (se 2 (by rfl) ⟨2419449, by rfl⟩ : syracuseStep 6451865 = 4838899) B4838899
theorem B4301243 : Blo 1911435 4301243 := bstep (se 1 (by rfl) ⟨3225932, by rfl⟩ : syracuseStep 4301243 = 6451865) B6451865
theorem B2867495 : Blo 1911435 2867495 := bstep (se 1 (by rfl) ⟨2150621, by rfl⟩ : syracuseStep 2867495 = 4301243) B4301243
theorem B1911663 : Blo 1911435 1911663 := bstep (se 1 (by rfl) ⟨1433747, by rfl⟩ : syracuseStep 1911663 = 2867495) B2867495
theorem B2867501 : Blo 1911435 2867501 := bbase (se 3 (by rfl) ⟨537656, by rfl⟩ : syracuseStep 2867501 = 1075313) (by norm_num)
theorem B1911667 : Blo 1911435 1911667 := bstep (se 1 (by rfl) ⟨1433750, by rfl⟩ : syracuseStep 1911667 = 2867501) B2867501
theorem B4301261 : Blo 1911435 4301261 := bbase (se 3 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 4301261 = 1612973) (by norm_num)
theorem B2867507 : Blo 1911435 2867507 := bstep (se 1 (by rfl) ⟨2150630, by rfl⟩ : syracuseStep 2867507 = 4301261) B4301261
theorem B1911671 : Blo 1911435 1911671 := bstep (se 1 (by rfl) ⟨1433753, by rfl⟩ : syracuseStep 1911671 = 2867507) B2867507
theorem B2419465 : Blo 1911435 2419465 := bbase (se 2 (by rfl) ⟨907299, by rfl⟩ : syracuseStep 2419465 = 1814599) (by norm_num)
theorem B3225953 : Blo 1911435 3225953 := bstep (se 2 (by rfl) ⟨1209732, by rfl⟩ : syracuseStep 3225953 = 2419465) B2419465
theorem B2150635 : Blo 1911435 2150635 := bstep (se 1 (by rfl) ⟨1612976, by rfl⟩ : syracuseStep 2150635 = 3225953) B3225953
theorem B2867513 : Blo 1911435 2867513 := bstep (se 2 (by rfl) ⟨1075317, by rfl⟩ : syracuseStep 2867513 = 2150635) B2150635
theorem B1911675 : Blo 1911435 1911675 := bstep (se 1 (by rfl) ⟨1433756, by rfl⟩ : syracuseStep 1911675 = 2867513) B2867513
theorem B13079893 : Blo 1911435 13079893 := bbase (se 14 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 13079893 = 2395) (by norm_num)
theorem B17439857 : Blo 1911435 17439857 := bstep (se 2 (by rfl) ⟨6539946, by rfl⟩ : syracuseStep 17439857 = 13079893) B13079893
theorem B11626571 : Blo 1911435 11626571 := bstep (se 1 (by rfl) ⟨8719928, by rfl⟩ : syracuseStep 11626571 = 17439857) B17439857
theorem B7751047 : Blo 1911435 7751047 := bstep (se 1 (by rfl) ⟨5813285, by rfl⟩ : syracuseStep 7751047 = 11626571) B11626571
theorem B10334729 : Blo 1911435 10334729 := bstep (se 2 (by rfl) ⟨3875523, by rfl⟩ : syracuseStep 10334729 = 7751047) B7751047
theorem B27559277 : Blo 1911435 27559277 := bstep (se 3 (by rfl) ⟨5167364, by rfl⟩ : syracuseStep 27559277 = 10334729) B10334729
theorem B18372851 : Blo 1911435 18372851 := bstep (se 1 (by rfl) ⟨13779638, by rfl⟩ : syracuseStep 18372851 = 27559277) B27559277
theorem B12248567 : Blo 1911435 12248567 := bstep (se 1 (by rfl) ⟨9186425, by rfl⟩ : syracuseStep 12248567 = 18372851) B18372851
theorem B8165711 : Blo 1911435 8165711 := bstep (se 1 (by rfl) ⟨6124283, by rfl⟩ : syracuseStep 8165711 = 12248567) B12248567
theorem B21775229 : Blo 1911435 21775229 := bstep (se 3 (by rfl) ⟨4082855, by rfl⟩ : syracuseStep 21775229 = 8165711) B8165711
theorem B14516819 : Blo 1911435 14516819 := bstep (se 1 (by rfl) ⟨10887614, by rfl⟩ : syracuseStep 14516819 = 21775229) B21775229
theorem B9677879 : Blo 1911435 9677879 := bstep (se 1 (by rfl) ⟨7258409, by rfl⟩ : syracuseStep 9677879 = 14516819) B14516819
theorem B6451919 : Blo 1911435 6451919 := bstep (se 1 (by rfl) ⟨4838939, by rfl⟩ : syracuseStep 6451919 = 9677879) B9677879
theorem B4301279 : Blo 1911435 4301279 := bstep (se 1 (by rfl) ⟨3225959, by rfl⟩ : syracuseStep 4301279 = 6451919) B6451919
theorem B2867519 : Blo 1911435 2867519 := bstep (se 1 (by rfl) ⟨2150639, by rfl⟩ : syracuseStep 2867519 = 4301279) B4301279
theorem B1911679 : Blo 1911435 1911679 := bstep (se 1 (by rfl) ⟨1433759, by rfl⟩ : syracuseStep 1911679 = 2867519) B2867519
theorem B2867525 : Blo 1911435 2867525 := bbase (se 4 (by rfl) ⟨268830, by rfl⟩ : syracuseStep 2867525 = 537661) (by norm_num)
theorem B1911683 : Blo 1911435 1911683 := bstep (se 1 (by rfl) ⟨1433762, by rfl⟩ : syracuseStep 1911683 = 2867525) B2867525
theorem B3225973 : Blo 1911435 3225973 := bbase (se 5 (by rfl) ⟨151217, by rfl⟩ : syracuseStep 3225973 = 302435) (by norm_num)
theorem B4301297 : Blo 1911435 4301297 := bstep (se 2 (by rfl) ⟨1612986, by rfl⟩ : syracuseStep 4301297 = 3225973) B3225973
theorem B2867531 : Blo 1911435 2867531 := bstep (se 1 (by rfl) ⟨2150648, by rfl⟩ : syracuseStep 2867531 = 4301297) B4301297
theorem B1911687 : Blo 1911435 1911687 := bstep (se 1 (by rfl) ⟨1433765, by rfl⟩ : syracuseStep 1911687 = 2867531) B2867531
theorem B2150653 : Blo 1911435 2150653 := bbase (se 3 (by rfl) ⟨403247, by rfl⟩ : syracuseStep 2150653 = 806495) (by norm_num)
theorem B2867537 : Blo 1911435 2867537 := bstep (se 2 (by rfl) ⟨1075326, by rfl⟩ : syracuseStep 2867537 = 2150653) B2150653
theorem B1911691 : Blo 1911435 1911691 := bstep (se 1 (by rfl) ⟨1433768, by rfl⟩ : syracuseStep 1911691 = 2867537) B2867537
theorem B6451973 : Blo 1911435 6451973 := bbase (se 4 (by rfl) ⟨604872, by rfl⟩ : syracuseStep 6451973 = 1209745) (by norm_num)
theorem B4301315 : Blo 1911435 4301315 := bstep (se 1 (by rfl) ⟨3225986, by rfl⟩ : syracuseStep 4301315 = 6451973) B6451973
theorem B2867543 : Blo 1911435 2867543 := bstep (se 1 (by rfl) ⟨2150657, by rfl⟩ : syracuseStep 2867543 = 4301315) B4301315
theorem B1911695 : Blo 1911435 1911695 := bstep (se 1 (by rfl) ⟨1433771, by rfl⟩ : syracuseStep 1911695 = 2867543) B2867543
theorem B2867549 : Blo 1911435 2867549 := bbase (se 3 (by rfl) ⟨537665, by rfl⟩ : syracuseStep 2867549 = 1075331) (by norm_num)
theorem B1911699 : Blo 1911435 1911699 := bstep (se 1 (by rfl) ⟨1433774, by rfl⟩ : syracuseStep 1911699 = 2867549) B2867549
theorem B4301333 : Blo 1911435 4301333 := bbase (se 6 (by rfl) ⟨100812, by rfl⟩ : syracuseStep 4301333 = 201625) (by norm_num)
theorem B2867555 : Blo 1911435 2867555 := bstep (se 1 (by rfl) ⟨2150666, by rfl⟩ : syracuseStep 2867555 = 4301333) B4301333
theorem B1911703 : Blo 1911435 1911703 := bstep (se 1 (by rfl) ⟨1433777, by rfl⟩ : syracuseStep 1911703 = 2867555) B2867555
theorem B7258517 : Blo 1911435 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B4839011 : Blo 1911435 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B3226007 : Blo 1911435 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B2150671 : Blo 1911435 2150671 := bstep (se 1 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 2150671 = 3226007) B3226007
theorem B2867561 : Blo 1911435 2867561 := bstep (se 2 (by rfl) ⟨1075335, by rfl⟩ : syracuseStep 2867561 = 2150671) B2150671
theorem B1911707 : Blo 1911435 1911707 := bstep (se 1 (by rfl) ⟨1433780, by rfl⟩ : syracuseStep 1911707 = 2867561) B2867561
theorem B10887797 : Blo 1911435 10887797 := bbase (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) (by norm_num)
theorem B7258531 : Blo 1911435 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B9678041 : Blo 1911435 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B6452027 : Blo 1911435 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B4301351 : Blo 1911435 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B2867567 : Blo 1911435 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B1911711 : Blo 1911435 1911711 := bstep (se 1 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 1911711 = 2867567) B2867567
theorem B2867573 : Blo 1911435 2867573 := bbase (se 5 (by rfl) ⟨134417, by rfl⟩ : syracuseStep 2867573 = 268835) (by norm_num)
theorem B1911715 : Blo 1911435 1911715 := bstep (se 1 (by rfl) ⟨1433786, by rfl⟩ : syracuseStep 1911715 = 2867573) B2867573
theorem B24831893 : Blo 1911435 24831893 := bbase (se 6 (by rfl) ⟨581997, by rfl⟩ : syracuseStep 24831893 = 1163995) (by norm_num)
theorem B66218381 : Blo 1911435 66218381 := bstep (se 3 (by rfl) ⟨12415946, by rfl⟩ : syracuseStep 66218381 = 24831893) B24831893
theorem B44145587 : Blo 1911435 44145587 := bstep (se 1 (by rfl) ⟨33109190, by rfl⟩ : syracuseStep 44145587 = 66218381) B66218381
theorem B29430391 : Blo 1911435 29430391 := bstep (se 1 (by rfl) ⟨22072793, by rfl⟩ : syracuseStep 29430391 = 44145587) B44145587
theorem B39240521 : Blo 1911435 39240521 := bstep (se 2 (by rfl) ⟨14715195, by rfl⟩ : syracuseStep 39240521 = 29430391) B29430391
theorem B26160347 : Blo 1911435 26160347 := bstep (se 1 (by rfl) ⟨19620260, by rfl⟩ : syracuseStep 26160347 = 39240521) B39240521
theorem B17440231 : Blo 1911435 17440231 := bstep (se 1 (by rfl) ⟨13080173, by rfl⟩ : syracuseStep 17440231 = 26160347) B26160347
theorem B23253641 : Blo 1911435 23253641 := bstep (se 2 (by rfl) ⟨8720115, by rfl⟩ : syracuseStep 23253641 = 17440231) B17440231
theorem B15502427 : Blo 1911435 15502427 := bstep (se 1 (by rfl) ⟨11626820, by rfl⟩ : syracuseStep 15502427 = 23253641) B23253641
theorem B10334951 : Blo 1911435 10334951 := bstep (se 1 (by rfl) ⟨7751213, by rfl⟩ : syracuseStep 10334951 = 15502427) B15502427
theorem B6889967 : Blo 1911435 6889967 := bstep (se 1 (by rfl) ⟨5167475, by rfl⟩ : syracuseStep 6889967 = 10334951) B10334951
theorem B4593311 : Blo 1911435 4593311 := bstep (se 1 (by rfl) ⟨3444983, by rfl⟩ : syracuseStep 4593311 = 6889967) B6889967
theorem B3062207 : Blo 1911435 3062207 := bstep (se 1 (by rfl) ⟨2296655, by rfl⟩ : syracuseStep 3062207 = 4593311) B4593311
theorem B2041471 : Blo 1911435 2041471 := bstep (se 1 (by rfl) ⟨1531103, by rfl⟩ : syracuseStep 2041471 = 3062207) B3062207
theorem B2721961 : Blo 1911435 2721961 := bstep (se 2 (by rfl) ⟨1020735, by rfl⟩ : syracuseStep 2721961 = 2041471) B2041471
theorem B3629281 : Blo 1911435 3629281 := bstep (se 2 (by rfl) ⟨1360980, by rfl⟩ : syracuseStep 3629281 = 2721961) B2721961
theorem B4839041 : Blo 1911435 4839041 := bstep (se 2 (by rfl) ⟨1814640, by rfl⟩ : syracuseStep 4839041 = 3629281) B3629281
theorem B3226027 : Blo 1911435 3226027 := bstep (se 1 (by rfl) ⟨2419520, by rfl⟩ : syracuseStep 3226027 = 4839041) B4839041
theorem B4301369 : Blo 1911435 4301369 := bstep (se 2 (by rfl) ⟨1613013, by rfl⟩ : syracuseStep 4301369 = 3226027) B3226027
theorem B2867579 : Blo 1911435 2867579 := bstep (se 1 (by rfl) ⟨2150684, by rfl⟩ : syracuseStep 2867579 = 4301369) B4301369
theorem B1911719 : Blo 1911435 1911719 := bstep (se 1 (by rfl) ⟨1433789, by rfl⟩ : syracuseStep 1911719 = 2867579) B2867579
theorem B2150689 : Blo 1911435 2150689 := bbase (se 2 (by rfl) ⟨806508, by rfl⟩ : syracuseStep 2150689 = 1613017) (by norm_num)
theorem B2867585 : Blo 1911435 2867585 := bstep (se 2 (by rfl) ⟨1075344, by rfl⟩ : syracuseStep 2867585 = 2150689) B2150689
theorem B1911723 : Blo 1911435 1911723 := bstep (se 1 (by rfl) ⟨1433792, by rfl⟩ : syracuseStep 1911723 = 2867585) B2867585
theorem B4839061 : Blo 1911435 4839061 := bbase (se 6 (by rfl) ⟨113415, by rfl⟩ : syracuseStep 4839061 = 226831) (by norm_num)
theorem B6452081 : Blo 1911435 6452081 := bstep (se 2 (by rfl) ⟨2419530, by rfl⟩ : syracuseStep 6452081 = 4839061) B4839061
theorem B4301387 : Blo 1911435 4301387 := bstep (se 1 (by rfl) ⟨3226040, by rfl⟩ : syracuseStep 4301387 = 6452081) B6452081
theorem B2867591 : Blo 1911435 2867591 := bstep (se 1 (by rfl) ⟨2150693, by rfl⟩ : syracuseStep 2867591 = 4301387) B4301387
theorem B1911727 : Blo 1911435 1911727 := bstep (se 1 (by rfl) ⟨1433795, by rfl⟩ : syracuseStep 1911727 = 2867591) B2867591
theorem B2867597 : Blo 1911435 2867597 := bbase (se 3 (by rfl) ⟨537674, by rfl⟩ : syracuseStep 2867597 = 1075349) (by norm_num)
theorem B1911731 : Blo 1911435 1911731 := bstep (se 1 (by rfl) ⟨1433798, by rfl⟩ : syracuseStep 1911731 = 2867597) B2867597
theorem B4301405 : Blo 1911435 4301405 := bbase (se 3 (by rfl) ⟨806513, by rfl⟩ : syracuseStep 4301405 = 1613027) (by norm_num)
theorem B2867603 : Blo 1911435 2867603 := bstep (se 1 (by rfl) ⟨2150702, by rfl⟩ : syracuseStep 2867603 = 4301405) B4301405
theorem B1911735 : Blo 1911435 1911735 := bstep (se 1 (by rfl) ⟨1433801, by rfl⟩ : syracuseStep 1911735 = 2867603) B2867603
theorem B3226061 : Blo 1911435 3226061 := bbase (se 3 (by rfl) ⟨604886, by rfl⟩ : syracuseStep 3226061 = 1209773) (by norm_num)
theorem B2150707 : Blo 1911435 2150707 := bstep (se 1 (by rfl) ⟨1613030, by rfl⟩ : syracuseStep 2150707 = 3226061) B3226061
theorem B2867609 : Blo 1911435 2867609 := bstep (se 2 (by rfl) ⟨1075353, by rfl⟩ : syracuseStep 2867609 = 2150707) B2150707
theorem B1911739 : Blo 1911435 1911739 := bstep (se 1 (by rfl) ⟨1433804, by rfl⟩ : syracuseStep 1911739 = 2867609) B2867609
theorem B2906741 : Blo 1911435 2906741 := bbase (se 5 (by rfl) ⟨136253, by rfl⟩ : syracuseStep 2906741 = 272507) (by norm_num)
theorem B1937827 : Blo 1911435 1937827 := bstep (se 1 (by rfl) ⟨1453370, by rfl⟩ : syracuseStep 1937827 = 2906741) B2906741
theorem B2583769 : Blo 1911435 2583769 := bstep (se 2 (by rfl) ⟨968913, by rfl⟩ : syracuseStep 2583769 = 1937827) B1937827
theorem B3445025 : Blo 1911435 3445025 := bstep (se 2 (by rfl) ⟨1291884, by rfl⟩ : syracuseStep 3445025 = 2583769) B2583769
theorem B9186733 : Blo 1911435 9186733 := bstep (se 3 (by rfl) ⟨1722512, by rfl⟩ : syracuseStep 9186733 = 3445025) B3445025
theorem B12248977 : Blo 1911435 12248977 := bstep (se 2 (by rfl) ⟨4593366, by rfl⟩ : syracuseStep 12248977 = 9186733) B9186733
theorem B16331969 : Blo 1911435 16331969 := bstep (se 2 (by rfl) ⟨6124488, by rfl⟩ : syracuseStep 16331969 = 12248977) B12248977
theorem B10887979 : Blo 1911435 10887979 := bstep (se 1 (by rfl) ⟨8165984, by rfl⟩ : syracuseStep 10887979 = 16331969) B16331969
theorem B14517305 : Blo 1911435 14517305 := bstep (se 2 (by rfl) ⟨5443989, by rfl⟩ : syracuseStep 14517305 = 10887979) B10887979
theorem B9678203 : Blo 1911435 9678203 := bstep (se 1 (by rfl) ⟨7258652, by rfl⟩ : syracuseStep 9678203 = 14517305) B14517305
theorem B6452135 : Blo 1911435 6452135 := bstep (se 1 (by rfl) ⟨4839101, by rfl⟩ : syracuseStep 6452135 = 9678203) B9678203
theorem B4301423 : Blo 1911435 4301423 := bstep (se 1 (by rfl) ⟨3226067, by rfl⟩ : syracuseStep 4301423 = 6452135) B6452135
theorem B2867615 : Blo 1911435 2867615 := bstep (se 1 (by rfl) ⟨2150711, by rfl⟩ : syracuseStep 2867615 = 4301423) B4301423
theorem B1911743 : Blo 1911435 1911743 := bstep (se 1 (by rfl) ⟨1433807, by rfl⟩ : syracuseStep 1911743 = 2867615) B2867615
theorem B2867621 : Blo 1911435 2867621 := bbase (se 4 (by rfl) ⟨268839, by rfl⟩ : syracuseStep 2867621 = 537679) (by norm_num)
theorem B1911747 : Blo 1911435 1911747 := bstep (se 1 (by rfl) ⟨1433810, by rfl⟩ : syracuseStep 1911747 = 2867621) B2867621
theorem B2419561 : Blo 1911435 2419561 := bbase (se 2 (by rfl) ⟨907335, by rfl⟩ : syracuseStep 2419561 = 1814671) (by norm_num)
theorem B3226081 : Blo 1911435 3226081 := bstep (se 2 (by rfl) ⟨1209780, by rfl⟩ : syracuseStep 3226081 = 2419561) B2419561
theorem B4301441 : Blo 1911435 4301441 := bstep (se 2 (by rfl) ⟨1613040, by rfl⟩ : syracuseStep 4301441 = 3226081) B3226081
theorem B2867627 : Blo 1911435 2867627 := bstep (se 1 (by rfl) ⟨2150720, by rfl⟩ : syracuseStep 2867627 = 4301441) B4301441
theorem B1911751 : Blo 1911435 1911751 := bstep (se 1 (by rfl) ⟨1433813, by rfl⟩ : syracuseStep 1911751 = 2867627) B2867627
theorem B2150725 : Blo 1911435 2150725 := bbase (se 4 (by rfl) ⟨201630, by rfl⟩ : syracuseStep 2150725 = 403261) (by norm_num)
theorem B2867633 : Blo 1911435 2867633 := bstep (se 2 (by rfl) ⟨1075362, by rfl⟩ : syracuseStep 2867633 = 2150725) B2150725
theorem B1911755 : Blo 1911435 1911755 := bstep (se 1 (by rfl) ⟨1433816, by rfl⟩ : syracuseStep 1911755 = 2867633) B2867633
theorem B3629357 : Blo 1911435 3629357 := bbase (se 3 (by rfl) ⟨680504, by rfl⟩ : syracuseStep 3629357 = 1361009) (by norm_num)
theorem B2419571 : Blo 1911435 2419571 := bstep (se 1 (by rfl) ⟨1814678, by rfl⟩ : syracuseStep 2419571 = 3629357) B3629357
theorem B6452189 : Blo 1911435 6452189 := bstep (se 3 (by rfl) ⟨1209785, by rfl⟩ : syracuseStep 6452189 = 2419571) B2419571
theorem B4301459 : Blo 1911435 4301459 := bstep (se 1 (by rfl) ⟨3226094, by rfl⟩ : syracuseStep 4301459 = 6452189) B6452189
theorem B2867639 : Blo 1911435 2867639 := bstep (se 1 (by rfl) ⟨2150729, by rfl⟩ : syracuseStep 2867639 = 4301459) B4301459
theorem B1911759 : Blo 1911435 1911759 := bstep (se 1 (by rfl) ⟨1433819, by rfl⟩ : syracuseStep 1911759 = 2867639) B2867639
theorem B2867645 : Blo 1911435 2867645 := bbase (se 3 (by rfl) ⟨537683, by rfl⟩ : syracuseStep 2867645 = 1075367) (by norm_num)
theorem B1911763 : Blo 1911435 1911763 := bstep (se 1 (by rfl) ⟨1433822, by rfl⟩ : syracuseStep 1911763 = 2867645) B2867645
theorem B4301477 : Blo 1911435 4301477 := bbase (se 4 (by rfl) ⟨403263, by rfl⟩ : syracuseStep 4301477 = 806527) (by norm_num)
theorem B2867651 : Blo 1911435 2867651 := bstep (se 1 (by rfl) ⟨2150738, by rfl⟩ : syracuseStep 2867651 = 4301477) B4301477
theorem B1911767 : Blo 1911435 1911767 := bstep (se 1 (by rfl) ⟨1433825, by rfl⟩ : syracuseStep 1911767 = 2867651) B2867651
theorem B4839173 : Blo 1911435 4839173 := bbase (se 4 (by rfl) ⟨453672, by rfl⟩ : syracuseStep 4839173 = 907345) (by norm_num)
theorem B3226115 : Blo 1911435 3226115 := bstep (se 1 (by rfl) ⟨2419586, by rfl⟩ : syracuseStep 3226115 = 4839173) B4839173
theorem B2150743 : Blo 1911435 2150743 := bstep (se 1 (by rfl) ⟨1613057, by rfl⟩ : syracuseStep 2150743 = 3226115) B3226115
theorem B2867657 : Blo 1911435 2867657 := bstep (se 2 (by rfl) ⟨1075371, by rfl⟩ : syracuseStep 2867657 = 2150743) B2150743
theorem B1911771 : Blo 1911435 1911771 := bstep (se 1 (by rfl) ⟨1433828, by rfl⟩ : syracuseStep 1911771 = 2867657) B2867657
theorem B4083061 : Blo 1911435 4083061 := bbase (se 5 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 4083061 = 382787) (by norm_num)
theorem B5444081 : Blo 1911435 5444081 := bstep (se 2 (by rfl) ⟨2041530, by rfl⟩ : syracuseStep 5444081 = 4083061) B4083061
theorem B3629387 : Blo 1911435 3629387 := bstep (se 1 (by rfl) ⟨2722040, by rfl⟩ : syracuseStep 3629387 = 5444081) B5444081
theorem B9678365 : Blo 1911435 9678365 := bstep (se 3 (by rfl) ⟨1814693, by rfl⟩ : syracuseStep 9678365 = 3629387) B3629387
theorem B6452243 : Blo 1911435 6452243 := bstep (se 1 (by rfl) ⟨4839182, by rfl⟩ : syracuseStep 6452243 = 9678365) B9678365
theorem B4301495 : Blo 1911435 4301495 := bstep (se 1 (by rfl) ⟨3226121, by rfl⟩ : syracuseStep 4301495 = 6452243) B6452243
theorem B2867663 : Blo 1911435 2867663 := bstep (se 1 (by rfl) ⟨2150747, by rfl⟩ : syracuseStep 2867663 = 4301495) B4301495
theorem B1911775 : Blo 1911435 1911775 := bstep (se 1 (by rfl) ⟨1433831, by rfl⟩ : syracuseStep 1911775 = 2867663) B2867663
theorem B2867669 : Blo 1911435 2867669 := bbase (se 7 (by rfl) ⟨33605, by rfl⟩ : syracuseStep 2867669 = 67211) (by norm_num)
theorem B1911779 : Blo 1911435 1911779 := bstep (se 1 (by rfl) ⟨1433834, by rfl⟩ : syracuseStep 1911779 = 2867669) B2867669
theorem B7258805 : Blo 1911435 7258805 := bbase (se 5 (by rfl) ⟨340256, by rfl⟩ : syracuseStep 7258805 = 680513) (by norm_num)
theorem B4839203 : Blo 1911435 4839203 := bstep (se 1 (by rfl) ⟨3629402, by rfl⟩ : syracuseStep 4839203 = 7258805) B7258805
theorem B3226135 : Blo 1911435 3226135 := bstep (se 1 (by rfl) ⟨2419601, by rfl⟩ : syracuseStep 3226135 = 4839203) B4839203
theorem B4301513 : Blo 1911435 4301513 := bstep (se 2 (by rfl) ⟨1613067, by rfl⟩ : syracuseStep 4301513 = 3226135) B3226135
theorem B2867675 : Blo 1911435 2867675 := bstep (se 1 (by rfl) ⟨2150756, by rfl⟩ : syracuseStep 2867675 = 4301513) B4301513
theorem B1911783 : Blo 1911435 1911783 := bstep (se 1 (by rfl) ⟨1433837, by rfl⟩ : syracuseStep 1911783 = 2867675) B2867675
theorem B2150761 : Blo 1911435 2150761 := bbase (se 2 (by rfl) ⟨806535, by rfl⟩ : syracuseStep 2150761 = 1613071) (by norm_num)
theorem B2867681 : Blo 1911435 2867681 := bstep (se 2 (by rfl) ⟨1075380, by rfl⟩ : syracuseStep 2867681 = 2150761) B2150761
theorem B1911787 : Blo 1911435 1911787 := bstep (se 1 (by rfl) ⟨1433840, by rfl⟩ : syracuseStep 1911787 = 2867681) B2867681
theorem B9186965 : Blo 1911435 9186965 := bbase (se 6 (by rfl) ⟨215319, by rfl⟩ : syracuseStep 9186965 = 430639) (by norm_num)
theorem B6124643 : Blo 1911435 6124643 := bstep (se 1 (by rfl) ⟨4593482, by rfl⟩ : syracuseStep 6124643 = 9186965) B9186965
theorem B4083095 : Blo 1911435 4083095 := bstep (se 1 (by rfl) ⟨3062321, by rfl⟩ : syracuseStep 4083095 = 6124643) B6124643
theorem B10888253 : Blo 1911435 10888253 := bstep (se 3 (by rfl) ⟨2041547, by rfl⟩ : syracuseStep 10888253 = 4083095) B4083095
theorem B7258835 : Blo 1911435 7258835 := bstep (se 1 (by rfl) ⟨5444126, by rfl⟩ : syracuseStep 7258835 = 10888253) B10888253
theorem B4839223 : Blo 1911435 4839223 := bstep (se 1 (by rfl) ⟨3629417, by rfl⟩ : syracuseStep 4839223 = 7258835) B7258835
theorem B6452297 : Blo 1911435 6452297 := bstep (se 2 (by rfl) ⟨2419611, by rfl⟩ : syracuseStep 6452297 = 4839223) B4839223
theorem B4301531 : Blo 1911435 4301531 := bstep (se 1 (by rfl) ⟨3226148, by rfl⟩ : syracuseStep 4301531 = 6452297) B6452297
theorem B2867687 : Blo 1911435 2867687 := bstep (se 1 (by rfl) ⟨2150765, by rfl⟩ : syracuseStep 2867687 = 4301531) B4301531
theorem B1911791 : Blo 1911435 1911791 := bstep (se 1 (by rfl) ⟨1433843, by rfl⟩ : syracuseStep 1911791 = 2867687) B2867687
theorem B2867693 : Blo 1911435 2867693 := bbase (se 3 (by rfl) ⟨537692, by rfl⟩ : syracuseStep 2867693 = 1075385) (by norm_num)
theorem B1911795 : Blo 1911435 1911795 := bstep (se 1 (by rfl) ⟨1433846, by rfl⟩ : syracuseStep 1911795 = 2867693) B2867693
theorem B4301549 : Blo 1911435 4301549 := bbase (se 3 (by rfl) ⟨806540, by rfl⟩ : syracuseStep 4301549 = 1613081) (by norm_num)
theorem B2867699 : Blo 1911435 2867699 := bstep (se 1 (by rfl) ⟨2150774, by rfl⟩ : syracuseStep 2867699 = 4301549) B4301549
theorem B1911799 : Blo 1911435 1911799 := bstep (se 1 (by rfl) ⟨1433849, by rfl⟩ : syracuseStep 1911799 = 2867699) B2867699
theorem B2041561 : Blo 1911435 2041561 := bbase (se 2 (by rfl) ⟨765585, by rfl⟩ : syracuseStep 2041561 = 1531171) (by norm_num)
theorem B2722081 : Blo 1911435 2722081 := bstep (se 2 (by rfl) ⟨1020780, by rfl⟩ : syracuseStep 2722081 = 2041561) B2041561
theorem B3629441 : Blo 1911435 3629441 := bstep (se 2 (by rfl) ⟨1361040, by rfl⟩ : syracuseStep 3629441 = 2722081) B2722081
theorem B2419627 : Blo 1911435 2419627 := bstep (se 1 (by rfl) ⟨1814720, by rfl⟩ : syracuseStep 2419627 = 3629441) B3629441
theorem B3226169 : Blo 1911435 3226169 := bstep (se 2 (by rfl) ⟨1209813, by rfl⟩ : syracuseStep 3226169 = 2419627) B2419627
theorem B2150779 : Blo 1911435 2150779 := bstep (se 1 (by rfl) ⟨1613084, by rfl⟩ : syracuseStep 2150779 = 3226169) B3226169
theorem B2867705 : Blo 1911435 2867705 := bstep (se 2 (by rfl) ⟨1075389, by rfl⟩ : syracuseStep 2867705 = 2150779) B2150779
theorem B1911803 : Blo 1911435 1911803 := bstep (se 1 (by rfl) ⟨1433852, by rfl⟩ : syracuseStep 1911803 = 2867705) B2867705
theorem B2906837 : Blo 1911435 2906837 := bbase (se 7 (by rfl) ⟨34064, by rfl⟩ : syracuseStep 2906837 = 68129) (by norm_num)
theorem B31006261 : Blo 1911435 31006261 := bstep (se 5 (by rfl) ⟨1453418, by rfl⟩ : syracuseStep 31006261 = 2906837) B2906837
theorem B41341681 : Blo 1911435 41341681 := bstep (se 2 (by rfl) ⟨15503130, by rfl⟩ : syracuseStep 41341681 = 31006261) B31006261
theorem B55122241 : Blo 1911435 55122241 := bstep (se 2 (by rfl) ⟨20670840, by rfl⟩ : syracuseStep 55122241 = 41341681) B41341681
theorem B73496321 : Blo 1911435 73496321 := bstep (se 2 (by rfl) ⟨27561120, by rfl⟩ : syracuseStep 73496321 = 55122241) B55122241
theorem B48997547 : Blo 1911435 48997547 := bstep (se 1 (by rfl) ⟨36748160, by rfl⟩ : syracuseStep 48997547 = 73496321) B73496321
theorem B32665031 : Blo 1911435 32665031 := bstep (se 1 (by rfl) ⟨24498773, by rfl⟩ : syracuseStep 32665031 = 48997547) B48997547
theorem B21776687 : Blo 1911435 21776687 := bstep (se 1 (by rfl) ⟨16332515, by rfl⟩ : syracuseStep 21776687 = 32665031) B32665031
theorem B14517791 : Blo 1911435 14517791 := bstep (se 1 (by rfl) ⟨10888343, by rfl⟩ : syracuseStep 14517791 = 21776687) B21776687
theorem B9678527 : Blo 1911435 9678527 := bstep (se 1 (by rfl) ⟨7258895, by rfl⟩ : syracuseStep 9678527 = 14517791) B14517791
theorem B6452351 : Blo 1911435 6452351 := bstep (se 1 (by rfl) ⟨4839263, by rfl⟩ : syracuseStep 6452351 = 9678527) B9678527
theorem B4301567 : Blo 1911435 4301567 := bstep (se 1 (by rfl) ⟨3226175, by rfl⟩ : syracuseStep 4301567 = 6452351) B6452351
theorem B2867711 : Blo 1911435 2867711 := bstep (se 1 (by rfl) ⟨2150783, by rfl⟩ : syracuseStep 2867711 = 4301567) B4301567
theorem B1911807 : Blo 1911435 1911807 := bstep (se 1 (by rfl) ⟨1433855, by rfl⟩ : syracuseStep 1911807 = 2867711) B2867711
theorem B2867717 : Blo 1911435 2867717 := bbase (se 4 (by rfl) ⟨268848, by rfl⟩ : syracuseStep 2867717 = 537697) (by norm_num)
theorem B1911811 : Blo 1911435 1911811 := bstep (se 1 (by rfl) ⟨1433858, by rfl⟩ : syracuseStep 1911811 = 2867717) B2867717
theorem B3226189 : Blo 1911435 3226189 := bbase (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) (by norm_num)
theorem B4301585 : Blo 1911435 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B2867723 : Blo 1911435 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B1911815 : Blo 1911435 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B2150797 : Blo 1911435 2150797 := bbase (se 3 (by rfl) ⟨403274, by rfl⟩ : syracuseStep 2150797 = 806549) (by norm_num)
theorem B2867729 : Blo 1911435 2867729 := bstep (se 2 (by rfl) ⟨1075398, by rfl⟩ : syracuseStep 2867729 = 2150797) B2150797
theorem B1911819 : Blo 1911435 1911819 := bstep (se 1 (by rfl) ⟨1433864, by rfl⟩ : syracuseStep 1911819 = 2867729) B2867729
theorem B6452405 : Blo 1911435 6452405 := bbase (se 5 (by rfl) ⟨302456, by rfl⟩ : syracuseStep 6452405 = 604913) (by norm_num)
theorem B4301603 : Blo 1911435 4301603 := bstep (se 1 (by rfl) ⟨3226202, by rfl⟩ : syracuseStep 4301603 = 6452405) B6452405
theorem B2867735 : Blo 1911435 2867735 := bstep (se 1 (by rfl) ⟨2150801, by rfl⟩ : syracuseStep 2867735 = 4301603) B4301603
theorem B1911823 : Blo 1911435 1911823 := bstep (se 1 (by rfl) ⟨1433867, by rfl⟩ : syracuseStep 1911823 = 2867735) B2867735
theorem B2867741 : Blo 1911435 2867741 := bbase (se 3 (by rfl) ⟨537701, by rfl⟩ : syracuseStep 2867741 = 1075403) (by norm_num)
theorem B1911827 : Blo 1911435 1911827 := bstep (se 1 (by rfl) ⟨1433870, by rfl⟩ : syracuseStep 1911827 = 2867741) B2867741
theorem B4301621 : Blo 1911435 4301621 := bbase (se 5 (by rfl) ⟨201638, by rfl⟩ : syracuseStep 4301621 = 403277) (by norm_num)
theorem B2867747 : Blo 1911435 2867747 := bstep (se 1 (by rfl) ⟨2150810, by rfl⟩ : syracuseStep 2867747 = 4301621) B4301621
theorem B1911831 : Blo 1911435 1911831 := bstep (se 1 (by rfl) ⟨1433873, by rfl⟩ : syracuseStep 1911831 = 2867747) B2867747
theorem B2452681 : Blo 1911435 2452681 := bbase (se 2 (by rfl) ⟨919755, by rfl⟩ : syracuseStep 2452681 = 1839511) (by norm_num)
theorem B3270241 : Blo 1911435 3270241 := bstep (se 2 (by rfl) ⟨1226340, by rfl⟩ : syracuseStep 3270241 = 2452681) B2452681
theorem B4360321 : Blo 1911435 4360321 := bstep (se 2 (by rfl) ⟨1635120, by rfl⟩ : syracuseStep 4360321 = 3270241) B3270241
theorem B23255045 : Blo 1911435 23255045 := bstep (se 4 (by rfl) ⟨2180160, by rfl⟩ : syracuseStep 23255045 = 4360321) B4360321
theorem B15503363 : Blo 1911435 15503363 := bstep (se 1 (by rfl) ⟨11627522, by rfl⟩ : syracuseStep 15503363 = 23255045) B23255045
theorem B10335575 : Blo 1911435 10335575 := bstep (se 1 (by rfl) ⟨7751681, by rfl⟩ : syracuseStep 10335575 = 15503363) B15503363
theorem B6890383 : Blo 1911435 6890383 := bstep (se 1 (by rfl) ⟨5167787, by rfl⟩ : syracuseStep 6890383 = 10335575) B10335575
theorem B9187177 : Blo 1911435 9187177 := bstep (se 2 (by rfl) ⟨3445191, by rfl⟩ : syracuseStep 9187177 = 6890383) B6890383
theorem B12249569 : Blo 1911435 12249569 := bstep (se 2 (by rfl) ⟨4593588, by rfl⟩ : syracuseStep 12249569 = 9187177) B9187177
theorem B8166379 : Blo 1911435 8166379 := bstep (se 1 (by rfl) ⟨6124784, by rfl⟩ : syracuseStep 8166379 = 12249569) B12249569
theorem B10888505 : Blo 1911435 10888505 := bstep (se 2 (by rfl) ⟨4083189, by rfl⟩ : syracuseStep 10888505 = 8166379) B8166379
theorem B7259003 : Blo 1911435 7259003 := bstep (se 1 (by rfl) ⟨5444252, by rfl⟩ : syracuseStep 7259003 = 10888505) B10888505
theorem B4839335 : Blo 1911435 4839335 := bstep (se 1 (by rfl) ⟨3629501, by rfl⟩ : syracuseStep 4839335 = 7259003) B7259003
theorem B3226223 : Blo 1911435 3226223 := bstep (se 1 (by rfl) ⟨2419667, by rfl⟩ : syracuseStep 3226223 = 4839335) B4839335
theorem B2150815 : Blo 1911435 2150815 := bstep (se 1 (by rfl) ⟨1613111, by rfl⟩ : syracuseStep 2150815 = 3226223) B3226223
theorem B2867753 : Blo 1911435 2867753 := bstep (se 2 (by rfl) ⟨1075407, by rfl⟩ : syracuseStep 2867753 = 2150815) B2150815
theorem B1911835 : Blo 1911435 1911835 := bstep (se 1 (by rfl) ⟨1433876, by rfl⟩ : syracuseStep 1911835 = 2867753) B2867753
theorem B4419821 : Blo 1911435 4419821 := bbase (se 3 (by rfl) ⟨828716, by rfl⟩ : syracuseStep 4419821 = 1657433) (by norm_num)
theorem B2946547 : Blo 1911435 2946547 := bstep (se 1 (by rfl) ⟨2209910, by rfl⟩ : syracuseStep 2946547 = 4419821) B4419821
theorem B15714917 : Blo 1911435 15714917 := bstep (se 4 (by rfl) ⟨1473273, by rfl⟩ : syracuseStep 15714917 = 2946547) B2946547
theorem B10476611 : Blo 1911435 10476611 := bstep (se 1 (by rfl) ⟨7857458, by rfl⟩ : syracuseStep 10476611 = 15714917) B15714917
theorem B6984407 : Blo 1911435 6984407 := bstep (se 1 (by rfl) ⟨5238305, by rfl⟩ : syracuseStep 6984407 = 10476611) B10476611
theorem B18625085 : Blo 1911435 18625085 := bstep (se 3 (by rfl) ⟨3492203, by rfl⟩ : syracuseStep 18625085 = 6984407) B6984407
theorem B12416723 : Blo 1911435 12416723 := bstep (se 1 (by rfl) ⟨9312542, by rfl⟩ : syracuseStep 12416723 = 18625085) B18625085
theorem B8277815 : Blo 1911435 8277815 := bstep (se 1 (by rfl) ⟨6208361, by rfl⟩ : syracuseStep 8277815 = 12416723) B12416723
theorem B5518543 : Blo 1911435 5518543 := bstep (se 1 (by rfl) ⟨4138907, by rfl⟩ : syracuseStep 5518543 = 8277815) B8277815
theorem B7358057 : Blo 1911435 7358057 := bstep (se 2 (by rfl) ⟨2759271, by rfl⟩ : syracuseStep 7358057 = 5518543) B5518543
theorem B4905371 : Blo 1911435 4905371 := bstep (se 1 (by rfl) ⟨3679028, by rfl⟩ : syracuseStep 4905371 = 7358057) B7358057
theorem B13080989 : Blo 1911435 13080989 := bstep (se 3 (by rfl) ⟨2452685, by rfl⟩ : syracuseStep 13080989 = 4905371) B4905371
theorem B8720659 : Blo 1911435 8720659 := bstep (se 1 (by rfl) ⟨6540494, by rfl⟩ : syracuseStep 8720659 = 13080989) B13080989
theorem B11627545 : Blo 1911435 11627545 := bstep (se 2 (by rfl) ⟨4360329, by rfl⟩ : syracuseStep 11627545 = 8720659) B8720659
theorem B15503393 : Blo 1911435 15503393 := bstep (se 2 (by rfl) ⟨5813772, by rfl⟩ : syracuseStep 15503393 = 11627545) B11627545
theorem B10335595 : Blo 1911435 10335595 := bstep (se 1 (by rfl) ⟨7751696, by rfl⟩ : syracuseStep 10335595 = 15503393) B15503393
theorem B13780793 : Blo 1911435 13780793 := bstep (se 2 (by rfl) ⟨5167797, by rfl⟩ : syracuseStep 13780793 = 10335595) B10335595
theorem B9187195 : Blo 1911435 9187195 := bstep (se 1 (by rfl) ⟨6890396, by rfl⟩ : syracuseStep 9187195 = 13780793) B13780793
theorem B12249593 : Blo 1911435 12249593 := bstep (se 2 (by rfl) ⟨4593597, by rfl⟩ : syracuseStep 12249593 = 9187195) B9187195
theorem B8166395 : Blo 1911435 8166395 := bstep (se 1 (by rfl) ⟨6124796, by rfl⟩ : syracuseStep 8166395 = 12249593) B12249593
theorem B5444263 : Blo 1911435 5444263 := bstep (se 1 (by rfl) ⟨4083197, by rfl⟩ : syracuseStep 5444263 = 8166395) B8166395
theorem B7259017 : Blo 1911435 7259017 := bstep (se 2 (by rfl) ⟨2722131, by rfl⟩ : syracuseStep 7259017 = 5444263) B5444263
theorem B9678689 : Blo 1911435 9678689 := bstep (se 2 (by rfl) ⟨3629508, by rfl⟩ : syracuseStep 9678689 = 7259017) B7259017
theorem B6452459 : Blo 1911435 6452459 := bstep (se 1 (by rfl) ⟨4839344, by rfl⟩ : syracuseStep 6452459 = 9678689) B9678689
theorem B4301639 : Blo 1911435 4301639 := bstep (se 1 (by rfl) ⟨3226229, by rfl⟩ : syracuseStep 4301639 = 6452459) B6452459
theorem B2867759 : Blo 1911435 2867759 := bstep (se 1 (by rfl) ⟨2150819, by rfl⟩ : syracuseStep 2867759 = 4301639) B4301639
theorem B1911839 : Blo 1911435 1911839 := bstep (se 1 (by rfl) ⟨1433879, by rfl⟩ : syracuseStep 1911839 = 2867759) B2867759
theorem B2867765 : Blo 1911435 2867765 := bbase (se 5 (by rfl) ⟨134426, by rfl⟩ : syracuseStep 2867765 = 268853) (by norm_num)
theorem B1911843 : Blo 1911435 1911843 := bstep (se 1 (by rfl) ⟨1433882, by rfl⟩ : syracuseStep 1911843 = 2867765) B2867765
theorem B4839365 : Blo 1911435 4839365 := bbase (se 4 (by rfl) ⟨453690, by rfl⟩ : syracuseStep 4839365 = 907381) (by norm_num)
theorem B3226243 : Blo 1911435 3226243 := bstep (se 1 (by rfl) ⟨2419682, by rfl⟩ : syracuseStep 3226243 = 4839365) B4839365
theorem B4301657 : Blo 1911435 4301657 := bstep (se 2 (by rfl) ⟨1613121, by rfl⟩ : syracuseStep 4301657 = 3226243) B3226243
theorem B2867771 : Blo 1911435 2867771 := bstep (se 1 (by rfl) ⟨2150828, by rfl⟩ : syracuseStep 2867771 = 4301657) B4301657
theorem B1911847 : Blo 1911435 1911847 := bstep (se 1 (by rfl) ⟨1433885, by rfl⟩ : syracuseStep 1911847 = 2867771) B2867771
theorem B2150833 : Blo 1911435 2150833 := bbase (se 2 (by rfl) ⟨806562, by rfl⟩ : syracuseStep 2150833 = 1613125) (by norm_num)
theorem B2867777 : Blo 1911435 2867777 := bstep (se 2 (by rfl) ⟨1075416, by rfl⟩ : syracuseStep 2867777 = 2150833) B2150833
theorem B1911851 : Blo 1911435 1911851 := bstep (se 1 (by rfl) ⟨1433888, by rfl⟩ : syracuseStep 1911851 = 2867777) B2867777
theorem B5444309 : Blo 1911435 5444309 := bbase (se 7 (by rfl) ⟨63800, by rfl⟩ : syracuseStep 5444309 = 127601) (by norm_num)
theorem B3629539 : Blo 1911435 3629539 := bstep (se 1 (by rfl) ⟨2722154, by rfl⟩ : syracuseStep 3629539 = 5444309) B5444309
theorem B4839385 : Blo 1911435 4839385 := bstep (se 2 (by rfl) ⟨1814769, by rfl⟩ : syracuseStep 4839385 = 3629539) B3629539
theorem B6452513 : Blo 1911435 6452513 := bstep (se 2 (by rfl) ⟨2419692, by rfl⟩ : syracuseStep 6452513 = 4839385) B4839385
theorem B4301675 : Blo 1911435 4301675 := bstep (se 1 (by rfl) ⟨3226256, by rfl⟩ : syracuseStep 4301675 = 6452513) B6452513
theorem B2867783 : Blo 1911435 2867783 := bstep (se 1 (by rfl) ⟨2150837, by rfl⟩ : syracuseStep 2867783 = 4301675) B4301675
theorem B1911855 : Blo 1911435 1911855 := bstep (se 1 (by rfl) ⟨1433891, by rfl⟩ : syracuseStep 1911855 = 2867783) B2867783
theorem B2867789 : Blo 1911435 2867789 := bbase (se 3 (by rfl) ⟨537710, by rfl⟩ : syracuseStep 2867789 = 1075421) (by norm_num)
theorem B1911859 : Blo 1911435 1911859 := bstep (se 1 (by rfl) ⟨1433894, by rfl⟩ : syracuseStep 1911859 = 2867789) B2867789
theorem B4301693 : Blo 1911435 4301693 := bbase (se 3 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 4301693 = 1613135) (by norm_num)
theorem B2867795 : Blo 1911435 2867795 := bstep (se 1 (by rfl) ⟨2150846, by rfl⟩ : syracuseStep 2867795 = 4301693) B4301693
theorem B1911863 : Blo 1911435 1911863 := bstep (se 1 (by rfl) ⟨1433897, by rfl⟩ : syracuseStep 1911863 = 2867795) B2867795
theorem B3226277 : Blo 1911435 3226277 := bbase (se 4 (by rfl) ⟨302463, by rfl⟩ : syracuseStep 3226277 = 604927) (by norm_num)
theorem B2150851 : Blo 1911435 2150851 := bstep (se 1 (by rfl) ⟨1613138, by rfl⟩ : syracuseStep 2150851 = 3226277) B3226277
theorem B2867801 : Blo 1911435 2867801 := bstep (se 2 (by rfl) ⟨1075425, by rfl⟩ : syracuseStep 2867801 = 2150851) B2150851
theorem B1911867 : Blo 1911435 1911867 := bstep (se 1 (by rfl) ⟨1433900, by rfl⟩ : syracuseStep 1911867 = 2867801) B2867801
theorem B2041633 : Blo 1911435 2041633 := bbase (se 2 (by rfl) ⟨765612, by rfl⟩ : syracuseStep 2041633 = 1531225) (by norm_num)
theorem B2722177 : Blo 1911435 2722177 := bstep (se 2 (by rfl) ⟨1020816, by rfl⟩ : syracuseStep 2722177 = 2041633) B2041633
theorem B14518277 : Blo 1911435 14518277 := bstep (se 4 (by rfl) ⟨1361088, by rfl⟩ : syracuseStep 14518277 = 2722177) B2722177
theorem B9678851 : Blo 1911435 9678851 := bstep (se 1 (by rfl) ⟨7259138, by rfl⟩ : syracuseStep 9678851 = 14518277) B14518277
theorem B6452567 : Blo 1911435 6452567 := bstep (se 1 (by rfl) ⟨4839425, by rfl⟩ : syracuseStep 6452567 = 9678851) B9678851
theorem B4301711 : Blo 1911435 4301711 := bstep (se 1 (by rfl) ⟨3226283, by rfl⟩ : syracuseStep 4301711 = 6452567) B6452567
theorem B2867807 : Blo 1911435 2867807 := bstep (se 1 (by rfl) ⟨2150855, by rfl⟩ : syracuseStep 2867807 = 4301711) B4301711
theorem B1911871 : Blo 1911435 1911871 := bstep (se 1 (by rfl) ⟨1433903, by rfl⟩ : syracuseStep 1911871 = 2867807) B2867807
theorem B2867813 : Blo 1911435 2867813 := bbase (se 4 (by rfl) ⟨268857, by rfl⟩ : syracuseStep 2867813 = 537715) (by norm_num)
theorem B1911875 : Blo 1911435 1911875 := bstep (se 1 (by rfl) ⟨1433906, by rfl⟩ : syracuseStep 1911875 = 2867813) B2867813
theorem B2722189 : Blo 1911435 2722189 := bbase (se 3 (by rfl) ⟨510410, by rfl⟩ : syracuseStep 2722189 = 1020821) (by norm_num)
theorem B3629585 : Blo 1911435 3629585 := bstep (se 2 (by rfl) ⟨1361094, by rfl⟩ : syracuseStep 3629585 = 2722189) B2722189
theorem B2419723 : Blo 1911435 2419723 := bstep (se 1 (by rfl) ⟨1814792, by rfl⟩ : syracuseStep 2419723 = 3629585) B3629585
theorem B3226297 : Blo 1911435 3226297 := bstep (se 2 (by rfl) ⟨1209861, by rfl⟩ : syracuseStep 3226297 = 2419723) B2419723
theorem B4301729 : Blo 1911435 4301729 := bstep (se 2 (by rfl) ⟨1613148, by rfl⟩ : syracuseStep 4301729 = 3226297) B3226297
theorem B2867819 : Blo 1911435 2867819 := bstep (se 1 (by rfl) ⟨2150864, by rfl⟩ : syracuseStep 2867819 = 4301729) B4301729
theorem B1911879 : Blo 1911435 1911879 := bstep (se 1 (by rfl) ⟨1433909, by rfl⟩ : syracuseStep 1911879 = 2867819) B2867819
theorem B2150869 : Blo 1911435 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B2867825 : Blo 1911435 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B1911883 : Blo 1911435 1911883 := bstep (se 1 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 1911883 = 2867825) B2867825
theorem B2419733 : Blo 1911435 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B6452621 : Blo 1911435 6452621 := bstep (se 3 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 6452621 = 2419733) B2419733
theorem B4301747 : Blo 1911435 4301747 := bstep (se 1 (by rfl) ⟨3226310, by rfl⟩ : syracuseStep 4301747 = 6452621) B6452621
theorem B2867831 : Blo 1911435 2867831 := bstep (se 1 (by rfl) ⟨2150873, by rfl⟩ : syracuseStep 2867831 = 4301747) B4301747
theorem B1911887 : Blo 1911435 1911887 := bstep (se 1 (by rfl) ⟨1433915, by rfl⟩ : syracuseStep 1911887 = 2867831) B2867831
theorem B2867837 : Blo 1911435 2867837 := bbase (se 3 (by rfl) ⟨537719, by rfl⟩ : syracuseStep 2867837 = 1075439) (by norm_num)
theorem B1911891 : Blo 1911435 1911891 := bstep (se 1 (by rfl) ⟨1433918, by rfl⟩ : syracuseStep 1911891 = 2867837) B2867837
theorem B4301765 : Blo 1911435 4301765 := bbase (se 4 (by rfl) ⟨403290, by rfl⟩ : syracuseStep 4301765 = 806581) (by norm_num)
theorem B2867843 : Blo 1911435 2867843 := bstep (se 1 (by rfl) ⟨2150882, by rfl⟩ : syracuseStep 2867843 = 4301765) B4301765
theorem B1911895 : Blo 1911435 1911895 := bstep (se 1 (by rfl) ⟨1433921, by rfl⟩ : syracuseStep 1911895 = 2867843) B2867843
theorem B5813957 : Blo 1911435 5813957 := bbase (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) (by norm_num)
theorem B15503885 : Blo 1911435 15503885 := bstep (se 3 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 15503885 = 5813957) B5813957
theorem B10335923 : Blo 1911435 10335923 := bstep (se 1 (by rfl) ⟨7751942, by rfl⟩ : syracuseStep 10335923 = 15503885) B15503885
theorem B6890615 : Blo 1911435 6890615 := bstep (se 1 (by rfl) ⟨5167961, by rfl⟩ : syracuseStep 6890615 = 10335923) B10335923
theorem B4593743 : Blo 1911435 4593743 := bstep (se 1 (by rfl) ⟨3445307, by rfl⟩ : syracuseStep 4593743 = 6890615) B6890615
theorem B3062495 : Blo 1911435 3062495 := bstep (se 1 (by rfl) ⟨2296871, by rfl⟩ : syracuseStep 3062495 = 4593743) B4593743
theorem B8166653 : Blo 1911435 8166653 := bstep (se 3 (by rfl) ⟨1531247, by rfl⟩ : syracuseStep 8166653 = 3062495) B3062495
theorem B5444435 : Blo 1911435 5444435 := bstep (se 1 (by rfl) ⟨4083326, by rfl⟩ : syracuseStep 5444435 = 8166653) B8166653
theorem B3629623 : Blo 1911435 3629623 := bstep (se 1 (by rfl) ⟨2722217, by rfl⟩ : syracuseStep 3629623 = 5444435) B5444435
theorem B4839497 : Blo 1911435 4839497 := bstep (se 2 (by rfl) ⟨1814811, by rfl⟩ : syracuseStep 4839497 = 3629623) B3629623
theorem B3226331 : Blo 1911435 3226331 := bstep (se 1 (by rfl) ⟨2419748, by rfl⟩ : syracuseStep 3226331 = 4839497) B4839497
theorem B2150887 : Blo 1911435 2150887 := bstep (se 1 (by rfl) ⟨1613165, by rfl⟩ : syracuseStep 2150887 = 3226331) B3226331
theorem B2867849 : Blo 1911435 2867849 := bstep (se 2 (by rfl) ⟨1075443, by rfl⟩ : syracuseStep 2867849 = 2150887) B2150887
theorem B1911899 : Blo 1911435 1911899 := bstep (se 1 (by rfl) ⟨1433924, by rfl⟩ : syracuseStep 1911899 = 2867849) B2867849
theorem B9679013 : Blo 1911435 9679013 := bbase (se 4 (by rfl) ⟨907407, by rfl⟩ : syracuseStep 9679013 = 1814815) (by norm_num)
theorem B6452675 : Blo 1911435 6452675 := bstep (se 1 (by rfl) ⟨4839506, by rfl⟩ : syracuseStep 6452675 = 9679013) B9679013
theorem B4301783 : Blo 1911435 4301783 := bstep (se 1 (by rfl) ⟨3226337, by rfl⟩ : syracuseStep 4301783 = 6452675) B6452675
theorem B2867855 : Blo 1911435 2867855 := bstep (se 1 (by rfl) ⟨2150891, by rfl⟩ : syracuseStep 2867855 = 4301783) B4301783
theorem B1911903 : Blo 1911435 1911903 := bstep (se 1 (by rfl) ⟨1433927, by rfl⟩ : syracuseStep 1911903 = 2867855) B2867855
theorem B2867861 : Blo 1911435 2867861 := bbase (se 6 (by rfl) ⟨67215, by rfl⟩ : syracuseStep 2867861 = 134431) (by norm_num)
theorem B1911907 : Blo 1911435 1911907 := bstep (se 1 (by rfl) ⟨1433930, by rfl⟩ : syracuseStep 1911907 = 2867861) B2867861
theorem B2209993 : Blo 1911435 2209993 := bbase (se 2 (by rfl) ⟨828747, by rfl⟩ : syracuseStep 2209993 = 1657495) (by norm_num)
theorem B11786629 : Blo 1911435 11786629 := bstep (se 4 (by rfl) ⟨1104996, by rfl⟩ : syracuseStep 11786629 = 2209993) B2209993
theorem B15715505 : Blo 1911435 15715505 := bstep (se 2 (by rfl) ⟨5893314, by rfl⟩ : syracuseStep 15715505 = 11786629) B11786629
theorem B41908013 : Blo 1911435 41908013 := bstep (se 3 (by rfl) ⟨7857752, by rfl⟩ : syracuseStep 41908013 = 15715505) B15715505
theorem B27938675 : Blo 1911435 27938675 := bstep (se 1 (by rfl) ⟨20954006, by rfl⟩ : syracuseStep 27938675 = 41908013) B41908013
theorem B18625783 : Blo 1911435 18625783 := bstep (se 1 (by rfl) ⟨13969337, by rfl⟩ : syracuseStep 18625783 = 27938675) B27938675
theorem B24834377 : Blo 1911435 24834377 := bstep (se 2 (by rfl) ⟨9312891, by rfl⟩ : syracuseStep 24834377 = 18625783) B18625783
theorem B16556251 : Blo 1911435 16556251 := bstep (se 1 (by rfl) ⟨12417188, by rfl⟩ : syracuseStep 16556251 = 24834377) B24834377
theorem B22075001 : Blo 1911435 22075001 := bstep (se 2 (by rfl) ⟨8278125, by rfl⟩ : syracuseStep 22075001 = 16556251) B16556251
theorem B14716667 : Blo 1911435 14716667 := bstep (se 1 (by rfl) ⟨11037500, by rfl⟩ : syracuseStep 14716667 = 22075001) B22075001
theorem B39244445 : Blo 1911435 39244445 := bstep (se 3 (by rfl) ⟨7358333, by rfl⟩ : syracuseStep 39244445 = 14716667) B14716667
theorem B26162963 : Blo 1911435 26162963 := bstep (se 1 (by rfl) ⟨19622222, by rfl⟩ : syracuseStep 26162963 = 39244445) B39244445
theorem B17441975 : Blo 1911435 17441975 := bstep (se 1 (by rfl) ⟨13081481, by rfl⟩ : syracuseStep 17441975 = 26162963) B26162963
theorem B11627983 : Blo 1911435 11627983 := bstep (se 1 (by rfl) ⟨8720987, by rfl⟩ : syracuseStep 11627983 = 17441975) B17441975
theorem B15503977 : Blo 1911435 15503977 := bstep (se 2 (by rfl) ⟨5813991, by rfl⟩ : syracuseStep 15503977 = 11627983) B11627983
theorem B20671969 : Blo 1911435 20671969 := bstep (se 2 (by rfl) ⟨7751988, by rfl⟩ : syracuseStep 20671969 = 15503977) B15503977
theorem B27562625 : Blo 1911435 27562625 := bstep (se 2 (by rfl) ⟨10335984, by rfl⟩ : syracuseStep 27562625 = 20671969) B20671969
theorem B18375083 : Blo 1911435 18375083 := bstep (se 1 (by rfl) ⟨13781312, by rfl⟩ : syracuseStep 18375083 = 27562625) B27562625
theorem B12250055 : Blo 1911435 12250055 := bstep (se 1 (by rfl) ⟨9187541, by rfl⟩ : syracuseStep 12250055 = 18375083) B18375083
theorem B8166703 : Blo 1911435 8166703 := bstep (se 1 (by rfl) ⟨6125027, by rfl⟩ : syracuseStep 8166703 = 12250055) B12250055
theorem B10888937 : Blo 1911435 10888937 := bstep (se 2 (by rfl) ⟨4083351, by rfl⟩ : syracuseStep 10888937 = 8166703) B8166703
theorem B7259291 : Blo 1911435 7259291 := bstep (se 1 (by rfl) ⟨5444468, by rfl⟩ : syracuseStep 7259291 = 10888937) B10888937
theorem B4839527 : Blo 1911435 4839527 := bstep (se 1 (by rfl) ⟨3629645, by rfl⟩ : syracuseStep 4839527 = 7259291) B7259291
theorem B3226351 : Blo 1911435 3226351 := bstep (se 1 (by rfl) ⟨2419763, by rfl⟩ : syracuseStep 3226351 = 4839527) B4839527
theorem B4301801 : Blo 1911435 4301801 := bstep (se 2 (by rfl) ⟨1613175, by rfl⟩ : syracuseStep 4301801 = 3226351) B3226351
theorem B2867867 : Blo 1911435 2867867 := bstep (se 1 (by rfl) ⟨2150900, by rfl⟩ : syracuseStep 2867867 = 4301801) B4301801
theorem B1911911 : Blo 1911435 1911911 := bstep (se 1 (by rfl) ⟨1433933, by rfl⟩ : syracuseStep 1911911 = 2867867) B2867867
theorem B2150905 : Blo 1911435 2150905 := bbase (se 2 (by rfl) ⟨806589, by rfl⟩ : syracuseStep 2150905 = 1613179) (by norm_num)
theorem B2867873 : Blo 1911435 2867873 := bstep (se 2 (by rfl) ⟨1075452, by rfl⟩ : syracuseStep 2867873 = 2150905) B2150905
theorem B1911915 : Blo 1911435 1911915 := bstep (se 1 (by rfl) ⟨1433936, by rfl⟩ : syracuseStep 1911915 = 2867873) B2867873
theorem B2452789 : Blo 1911435 2452789 := bbase (se 5 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 2452789 = 229949) (by norm_num)
theorem B3270385 : Blo 1911435 3270385 := bstep (se 2 (by rfl) ⟨1226394, by rfl⟩ : syracuseStep 3270385 = 2452789) B2452789
theorem B17442053 : Blo 1911435 17442053 := bstep (se 4 (by rfl) ⟨1635192, by rfl⟩ : syracuseStep 17442053 = 3270385) B3270385
theorem B11628035 : Blo 1911435 11628035 := bstep (se 1 (by rfl) ⟨8721026, by rfl⟩ : syracuseStep 11628035 = 17442053) B17442053
theorem B7752023 : Blo 1911435 7752023 := bstep (se 1 (by rfl) ⟨5814017, by rfl⟩ : syracuseStep 7752023 = 11628035) B11628035
theorem B5168015 : Blo 1911435 5168015 := bstep (se 1 (by rfl) ⟨3876011, by rfl⟩ : syracuseStep 5168015 = 7752023) B7752023
theorem B3445343 : Blo 1911435 3445343 := bstep (se 1 (by rfl) ⟨2584007, by rfl⟩ : syracuseStep 3445343 = 5168015) B5168015
theorem B2296895 : Blo 1911435 2296895 := bstep (se 1 (by rfl) ⟨1722671, by rfl⟩ : syracuseStep 2296895 = 3445343) B3445343
theorem B6125053 : Blo 1911435 6125053 := bstep (se 3 (by rfl) ⟨1148447, by rfl⟩ : syracuseStep 6125053 = 2296895) B2296895
theorem B8166737 : Blo 1911435 8166737 := bstep (se 2 (by rfl) ⟨3062526, by rfl⟩ : syracuseStep 8166737 = 6125053) B6125053
theorem B5444491 : Blo 1911435 5444491 := bstep (se 1 (by rfl) ⟨4083368, by rfl⟩ : syracuseStep 5444491 = 8166737) B8166737
theorem B7259321 : Blo 1911435 7259321 := bstep (se 2 (by rfl) ⟨2722245, by rfl⟩ : syracuseStep 7259321 = 5444491) B5444491
theorem B4839547 : Blo 1911435 4839547 := bstep (se 1 (by rfl) ⟨3629660, by rfl⟩ : syracuseStep 4839547 = 7259321) B7259321
theorem B6452729 : Blo 1911435 6452729 := bstep (se 2 (by rfl) ⟨2419773, by rfl⟩ : syracuseStep 6452729 = 4839547) B4839547
theorem B4301819 : Blo 1911435 4301819 := bstep (se 1 (by rfl) ⟨3226364, by rfl⟩ : syracuseStep 4301819 = 6452729) B6452729
theorem B2867879 : Blo 1911435 2867879 := bstep (se 1 (by rfl) ⟨2150909, by rfl⟩ : syracuseStep 2867879 = 4301819) B4301819
theorem B1911919 : Blo 1911435 1911919 := bstep (se 1 (by rfl) ⟨1433939, by rfl⟩ : syracuseStep 1911919 = 2867879) B2867879
theorem B2867885 : Blo 1911435 2867885 := bbase (se 3 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 2867885 = 1075457) (by norm_num)
theorem B1911923 : Blo 1911435 1911923 := bstep (se 1 (by rfl) ⟨1433942, by rfl⟩ : syracuseStep 1911923 = 2867885) B2867885
theorem B4301837 : Blo 1911435 4301837 := bbase (se 3 (by rfl) ⟨806594, by rfl⟩ : syracuseStep 4301837 = 1613189) (by norm_num)
theorem B2867891 : Blo 1911435 2867891 := bstep (se 1 (by rfl) ⟨2150918, by rfl⟩ : syracuseStep 2867891 = 4301837) B4301837
theorem B1911927 : Blo 1911435 1911927 := bstep (se 1 (by rfl) ⟨1433945, by rfl⟩ : syracuseStep 1911927 = 2867891) B2867891
theorem B2419789 : Blo 1911435 2419789 := bbase (se 3 (by rfl) ⟨453710, by rfl⟩ : syracuseStep 2419789 = 907421) (by norm_num)
theorem B3226385 : Blo 1911435 3226385 := bstep (se 2 (by rfl) ⟨1209894, by rfl⟩ : syracuseStep 3226385 = 2419789) B2419789
theorem B2150923 : Blo 1911435 2150923 := bstep (se 1 (by rfl) ⟨1613192, by rfl⟩ : syracuseStep 2150923 = 3226385) B3226385
theorem B2867897 : Blo 1911435 2867897 := bstep (se 2 (by rfl) ⟨1075461, by rfl⟩ : syracuseStep 2867897 = 2150923) B2150923
theorem B1911931 : Blo 1911435 1911931 := bstep (se 1 (by rfl) ⟨1433948, by rfl⟩ : syracuseStep 1911931 = 2867897) B2867897
theorem B2069557 : Blo 1911435 2069557 := bbase (se 5 (by rfl) ⟨97010, by rfl⟩ : syracuseStep 2069557 = 194021) (by norm_num)
theorem B11037637 : Blo 1911435 11037637 := bstep (se 4 (by rfl) ⟨1034778, by rfl⟩ : syracuseStep 11037637 = 2069557) B2069557
theorem B58867397 : Blo 1911435 58867397 := bstep (se 4 (by rfl) ⟨5518818, by rfl⟩ : syracuseStep 58867397 = 11037637) B11037637
theorem B39244931 : Blo 1911435 39244931 := bstep (se 1 (by rfl) ⟨29433698, by rfl⟩ : syracuseStep 39244931 = 58867397) B58867397
theorem B26163287 : Blo 1911435 26163287 := bstep (se 1 (by rfl) ⟨19622465, by rfl⟩ : syracuseStep 26163287 = 39244931) B39244931
theorem B17442191 : Blo 1911435 17442191 := bstep (se 1 (by rfl) ⟨13081643, by rfl⟩ : syracuseStep 17442191 = 26163287) B26163287
theorem B11628127 : Blo 1911435 11628127 := bstep (se 1 (by rfl) ⟨8721095, by rfl⟩ : syracuseStep 11628127 = 17442191) B17442191
theorem B62016677 : Blo 1911435 62016677 := bstep (se 4 (by rfl) ⟨5814063, by rfl⟩ : syracuseStep 62016677 = 11628127) B11628127
theorem B41344451 : Blo 1911435 41344451 := bstep (se 1 (by rfl) ⟨31008338, by rfl⟩ : syracuseStep 41344451 = 62016677) B62016677
theorem B27562967 : Blo 1911435 27562967 := bstep (se 1 (by rfl) ⟨20672225, by rfl⟩ : syracuseStep 27562967 = 41344451) B41344451
theorem B18375311 : Blo 1911435 18375311 := bstep (se 1 (by rfl) ⟨13781483, by rfl⟩ : syracuseStep 18375311 = 27562967) B27562967
theorem B12250207 : Blo 1911435 12250207 := bstep (se 1 (by rfl) ⟨9187655, by rfl⟩ : syracuseStep 12250207 = 18375311) B18375311
theorem B16333609 : Blo 1911435 16333609 := bstep (se 2 (by rfl) ⟨6125103, by rfl⟩ : syracuseStep 16333609 = 12250207) B12250207
theorem B21778145 : Blo 1911435 21778145 := bstep (se 2 (by rfl) ⟨8166804, by rfl⟩ : syracuseStep 21778145 = 16333609) B16333609
theorem B14518763 : Blo 1911435 14518763 := bstep (se 1 (by rfl) ⟨10889072, by rfl⟩ : syracuseStep 14518763 = 21778145) B21778145
theorem B9679175 : Blo 1911435 9679175 := bstep (se 1 (by rfl) ⟨7259381, by rfl⟩ : syracuseStep 9679175 = 14518763) B14518763
theorem B6452783 : Blo 1911435 6452783 := bstep (se 1 (by rfl) ⟨4839587, by rfl⟩ : syracuseStep 6452783 = 9679175) B9679175
theorem B4301855 : Blo 1911435 4301855 := bstep (se 1 (by rfl) ⟨3226391, by rfl⟩ : syracuseStep 4301855 = 6452783) B6452783
theorem B2867903 : Blo 1911435 2867903 := bstep (se 1 (by rfl) ⟨2150927, by rfl⟩ : syracuseStep 2867903 = 4301855) B4301855
theorem B1911935 : Blo 1911435 1911935 := bstep (se 1 (by rfl) ⟨1433951, by rfl⟩ : syracuseStep 1911935 = 2867903) B2867903
theorem B2867909 : Blo 1911435 2867909 := bbase (se 4 (by rfl) ⟨268866, by rfl⟩ : syracuseStep 2867909 = 537733) (by norm_num)
theorem B1911939 : Blo 1911435 1911939 := bstep (se 1 (by rfl) ⟨1433954, by rfl⟩ : syracuseStep 1911939 = 2867909) B2867909
theorem B3226405 : Blo 1911435 3226405 := bbase (se 4 (by rfl) ⟨302475, by rfl⟩ : syracuseStep 3226405 = 604951) (by norm_num)
theorem B4301873 : Blo 1911435 4301873 := bstep (se 2 (by rfl) ⟨1613202, by rfl⟩ : syracuseStep 4301873 = 3226405) B3226405
theorem B2867915 : Blo 1911435 2867915 := bstep (se 1 (by rfl) ⟨2150936, by rfl⟩ : syracuseStep 2867915 = 4301873) B4301873
theorem B1911943 : Blo 1911435 1911943 := bstep (se 1 (by rfl) ⟨1433957, by rfl⟩ : syracuseStep 1911943 = 2867915) B2867915
theorem B2150941 : Blo 1911435 2150941 := bbase (se 3 (by rfl) ⟨403301, by rfl⟩ : syracuseStep 2150941 = 806603) (by norm_num)
theorem B2867921 : Blo 1911435 2867921 := bstep (se 2 (by rfl) ⟨1075470, by rfl⟩ : syracuseStep 2867921 = 2150941) B2150941
theorem B1911947 : Blo 1911435 1911947 := bstep (se 1 (by rfl) ⟨1433960, by rfl⟩ : syracuseStep 1911947 = 2867921) B2867921
theorem B6452837 : Blo 1911435 6452837 := bbase (se 4 (by rfl) ⟨604953, by rfl⟩ : syracuseStep 6452837 = 1209907) (by norm_num)
theorem B4301891 : Blo 1911435 4301891 := bstep (se 1 (by rfl) ⟨3226418, by rfl⟩ : syracuseStep 4301891 = 6452837) B6452837
theorem B2867927 : Blo 1911435 2867927 := bstep (se 1 (by rfl) ⟨2150945, by rfl⟩ : syracuseStep 2867927 = 4301891) B4301891
theorem B1911951 : Blo 1911435 1911951 := bstep (se 1 (by rfl) ⟨1433963, by rfl⟩ : syracuseStep 1911951 = 2867927) B2867927
theorem B2867933 : Blo 1911435 2867933 := bbase (se 3 (by rfl) ⟨537737, by rfl⟩ : syracuseStep 2867933 = 1075475) (by norm_num)
theorem B1911955 : Blo 1911435 1911955 := bstep (se 1 (by rfl) ⟨1433966, by rfl⟩ : syracuseStep 1911955 = 2867933) B2867933
theorem B4301909 : Blo 1911435 4301909 := bbase (se 8 (by rfl) ⟨25206, by rfl⟩ : syracuseStep 4301909 = 50413) (by norm_num)
theorem B2867939 : Blo 1911435 2867939 := bstep (se 1 (by rfl) ⟨2150954, by rfl⟩ : syracuseStep 2867939 = 4301909) B4301909
theorem B1911959 : Blo 1911435 1911959 := bstep (se 1 (by rfl) ⟨1433969, by rfl⟩ : syracuseStep 1911959 = 2867939) B2867939
theorem B3876101 : Blo 1911435 3876101 := bbase (se 4 (by rfl) ⟨363384, by rfl⟩ : syracuseStep 3876101 = 726769) (by norm_num)
theorem B2584067 : Blo 1911435 2584067 := bstep (se 1 (by rfl) ⟨1938050, by rfl⟩ : syracuseStep 2584067 = 3876101) B3876101
theorem B6890845 : Blo 1911435 6890845 := bstep (se 3 (by rfl) ⟨1292033, by rfl⟩ : syracuseStep 6890845 = 2584067) B2584067
theorem B9187793 : Blo 1911435 9187793 := bstep (se 2 (by rfl) ⟨3445422, by rfl⟩ : syracuseStep 9187793 = 6890845) B6890845
theorem B6125195 : Blo 1911435 6125195 := bstep (se 1 (by rfl) ⟨4593896, by rfl⟩ : syracuseStep 6125195 = 9187793) B9187793
theorem B4083463 : Blo 1911435 4083463 := bstep (se 1 (by rfl) ⟨3062597, by rfl⟩ : syracuseStep 4083463 = 6125195) B6125195
theorem B5444617 : Blo 1911435 5444617 := bstep (se 2 (by rfl) ⟨2041731, by rfl⟩ : syracuseStep 5444617 = 4083463) B4083463
theorem B7259489 : Blo 1911435 7259489 := bstep (se 2 (by rfl) ⟨2722308, by rfl⟩ : syracuseStep 7259489 = 5444617) B5444617
theorem B4839659 : Blo 1911435 4839659 := bstep (se 1 (by rfl) ⟨3629744, by rfl⟩ : syracuseStep 4839659 = 7259489) B7259489
theorem B3226439 : Blo 1911435 3226439 := bstep (se 1 (by rfl) ⟨2419829, by rfl⟩ : syracuseStep 3226439 = 4839659) B4839659
theorem B2150959 : Blo 1911435 2150959 := bstep (se 1 (by rfl) ⟨1613219, by rfl⟩ : syracuseStep 2150959 = 3226439) B3226439
theorem B2867945 : Blo 1911435 2867945 := bstep (se 2 (by rfl) ⟨1075479, by rfl⟩ : syracuseStep 2867945 = 2150959) B2150959
theorem B1911963 : Blo 1911435 1911963 := bstep (se 1 (by rfl) ⟨1433972, by rfl⟩ : syracuseStep 1911963 = 2867945) B2867945
theorem B17442485 : Blo 1911435 17442485 := bbase (se 5 (by rfl) ⟨817616, by rfl⟩ : syracuseStep 17442485 = 1635233) (by norm_num)
theorem B11628323 : Blo 1911435 11628323 := bstep (se 1 (by rfl) ⟨8721242, by rfl⟩ : syracuseStep 11628323 = 17442485) B17442485
theorem B7752215 : Blo 1911435 7752215 := bstep (se 1 (by rfl) ⟨5814161, by rfl⟩ : syracuseStep 7752215 = 11628323) B11628323
theorem B5168143 : Blo 1911435 5168143 := bstep (se 1 (by rfl) ⟨3876107, by rfl⟩ : syracuseStep 5168143 = 7752215) B7752215
theorem B27563429 : Blo 1911435 27563429 := bstep (se 4 (by rfl) ⟨2584071, by rfl⟩ : syracuseStep 27563429 = 5168143) B5168143
theorem B18375619 : Blo 1911435 18375619 := bstep (se 1 (by rfl) ⟨13781714, by rfl⟩ : syracuseStep 18375619 = 27563429) B27563429
theorem B24500825 : Blo 1911435 24500825 := bstep (se 2 (by rfl) ⟨9187809, by rfl⟩ : syracuseStep 24500825 = 18375619) B18375619
theorem B16333883 : Blo 1911435 16333883 := bstep (se 1 (by rfl) ⟨12250412, by rfl⟩ : syracuseStep 16333883 = 24500825) B24500825
theorem B10889255 : Blo 1911435 10889255 := bstep (se 1 (by rfl) ⟨8166941, by rfl⟩ : syracuseStep 10889255 = 16333883) B16333883
theorem B7259503 : Blo 1911435 7259503 := bstep (se 1 (by rfl) ⟨5444627, by rfl⟩ : syracuseStep 7259503 = 10889255) B10889255
theorem B9679337 : Blo 1911435 9679337 := bstep (se 2 (by rfl) ⟨3629751, by rfl⟩ : syracuseStep 9679337 = 7259503) B7259503
theorem B6452891 : Blo 1911435 6452891 := bstep (se 1 (by rfl) ⟨4839668, by rfl⟩ : syracuseStep 6452891 = 9679337) B9679337
theorem B4301927 : Blo 1911435 4301927 := bstep (se 1 (by rfl) ⟨3226445, by rfl⟩ : syracuseStep 4301927 = 6452891) B6452891
theorem B2867951 : Blo 1911435 2867951 := bstep (se 1 (by rfl) ⟨2150963, by rfl⟩ : syracuseStep 2867951 = 4301927) B4301927
theorem B1911967 : Blo 1911435 1911967 := bstep (se 1 (by rfl) ⟨1433975, by rfl⟩ : syracuseStep 1911967 = 2867951) B2867951
theorem B2867957 : Blo 1911435 2867957 := bbase (se 5 (by rfl) ⟨134435, by rfl⟩ : syracuseStep 2867957 = 268871) (by norm_num)
theorem B1911971 : Blo 1911435 1911971 := bstep (se 1 (by rfl) ⟨1433978, by rfl⟩ : syracuseStep 1911971 = 2867957) B2867957
theorem B4593925 : Blo 1911435 4593925 := bbase (se 4 (by rfl) ⟨430680, by rfl⟩ : syracuseStep 4593925 = 861361) (by norm_num)
theorem B6125233 : Blo 1911435 6125233 := bstep (se 2 (by rfl) ⟨2296962, by rfl⟩ : syracuseStep 6125233 = 4593925) B4593925
theorem B8166977 : Blo 1911435 8166977 := bstep (se 2 (by rfl) ⟨3062616, by rfl⟩ : syracuseStep 8166977 = 6125233) B6125233
theorem B5444651 : Blo 1911435 5444651 := bstep (se 1 (by rfl) ⟨4083488, by rfl⟩ : syracuseStep 5444651 = 8166977) B8166977
theorem B3629767 : Blo 1911435 3629767 := bstep (se 1 (by rfl) ⟨2722325, by rfl⟩ : syracuseStep 3629767 = 5444651) B5444651
theorem B4839689 : Blo 1911435 4839689 := bstep (se 2 (by rfl) ⟨1814883, by rfl⟩ : syracuseStep 4839689 = 3629767) B3629767
theorem B3226459 : Blo 1911435 3226459 := bstep (se 1 (by rfl) ⟨2419844, by rfl⟩ : syracuseStep 3226459 = 4839689) B4839689
theorem B4301945 : Blo 1911435 4301945 := bstep (se 2 (by rfl) ⟨1613229, by rfl⟩ : syracuseStep 4301945 = 3226459) B3226459
theorem B2867963 : Blo 1911435 2867963 := bstep (se 1 (by rfl) ⟨2150972, by rfl⟩ : syracuseStep 2867963 = 4301945) B4301945
theorem B1911975 : Blo 1911435 1911975 := bstep (se 1 (by rfl) ⟨1433981, by rfl⟩ : syracuseStep 1911975 = 2867963) B2867963
theorem B2150977 : Blo 1911435 2150977 := bbase (se 2 (by rfl) ⟨806616, by rfl⟩ : syracuseStep 2150977 = 1613233) (by norm_num)
theorem B2867969 : Blo 1911435 2867969 := bstep (se 2 (by rfl) ⟨1075488, by rfl⟩ : syracuseStep 2867969 = 2150977) B2150977
theorem B1911979 : Blo 1911435 1911979 := bstep (se 1 (by rfl) ⟨1433984, by rfl⟩ : syracuseStep 1911979 = 2867969) B2867969
theorem B4839709 : Blo 1911435 4839709 := bbase (se 3 (by rfl) ⟨907445, by rfl⟩ : syracuseStep 4839709 = 1814891) (by norm_num)
theorem B6452945 : Blo 1911435 6452945 := bstep (se 2 (by rfl) ⟨2419854, by rfl⟩ : syracuseStep 6452945 = 4839709) B4839709
theorem B4301963 : Blo 1911435 4301963 := bstep (se 1 (by rfl) ⟨3226472, by rfl⟩ : syracuseStep 4301963 = 6452945) B6452945
theorem B2867975 : Blo 1911435 2867975 := bstep (se 1 (by rfl) ⟨2150981, by rfl⟩ : syracuseStep 2867975 = 4301963) B4301963
theorem B1911983 : Blo 1911435 1911983 := bstep (se 1 (by rfl) ⟨1433987, by rfl⟩ : syracuseStep 1911983 = 2867975) B2867975
theorem B2867981 : Blo 1911435 2867981 := bbase (se 3 (by rfl) ⟨537746, by rfl⟩ : syracuseStep 2867981 = 1075493) (by norm_num)
theorem B1911987 : Blo 1911435 1911987 := bstep (se 1 (by rfl) ⟨1433990, by rfl⟩ : syracuseStep 1911987 = 2867981) B2867981
theorem B4301981 : Blo 1911435 4301981 := bbase (se 3 (by rfl) ⟨806621, by rfl⟩ : syracuseStep 4301981 = 1613243) (by norm_num)
theorem B2867987 : Blo 1911435 2867987 := bstep (se 1 (by rfl) ⟨2150990, by rfl⟩ : syracuseStep 2867987 = 4301981) B4301981
theorem B1911991 : Blo 1911435 1911991 := bstep (se 1 (by rfl) ⟨1433993, by rfl⟩ : syracuseStep 1911991 = 2867987) B2867987
theorem B3226493 : Blo 1911435 3226493 := bbase (se 3 (by rfl) ⟨604967, by rfl⟩ : syracuseStep 3226493 = 1209935) (by norm_num)
theorem B2150995 : Blo 1911435 2150995 := bstep (se 1 (by rfl) ⟨1613246, by rfl⟩ : syracuseStep 2150995 = 3226493) B3226493
theorem B2867993 : Blo 1911435 2867993 := bstep (se 2 (by rfl) ⟨1075497, by rfl⟩ : syracuseStep 2867993 = 2150995) B2150995
theorem B1911995 : Blo 1911435 1911995 := bstep (se 1 (by rfl) ⟨1433996, by rfl⟩ : syracuseStep 1911995 = 2867993) B2867993
theorem B18626645 : Blo 1911435 18626645 := bbase (se 8 (by rfl) ⟨109140, by rfl⟩ : syracuseStep 18626645 = 218281) (by norm_num)
theorem B49671053 : Blo 1911435 49671053 := bstep (se 3 (by rfl) ⟨9313322, by rfl⟩ : syracuseStep 49671053 = 18626645) B18626645
theorem B33114035 : Blo 1911435 33114035 := bstep (se 1 (by rfl) ⟨24835526, by rfl⟩ : syracuseStep 33114035 = 49671053) B49671053
theorem B22076023 : Blo 1911435 22076023 := bstep (se 1 (by rfl) ⟨16557017, by rfl⟩ : syracuseStep 22076023 = 33114035) B33114035
theorem B29434697 : Blo 1911435 29434697 := bstep (se 2 (by rfl) ⟨11038011, by rfl⟩ : syracuseStep 29434697 = 22076023) B22076023
theorem B19623131 : Blo 1911435 19623131 := bstep (se 1 (by rfl) ⟨14717348, by rfl⟩ : syracuseStep 19623131 = 29434697) B29434697
theorem B13082087 : Blo 1911435 13082087 := bstep (se 1 (by rfl) ⟨9811565, by rfl⟩ : syracuseStep 13082087 = 19623131) B19623131
theorem B8721391 : Blo 1911435 8721391 := bstep (se 1 (by rfl) ⟨6541043, by rfl⟩ : syracuseStep 8721391 = 13082087) B13082087
theorem B11628521 : Blo 1911435 11628521 := bstep (se 2 (by rfl) ⟨4360695, by rfl⟩ : syracuseStep 11628521 = 8721391) B8721391
theorem B7752347 : Blo 1911435 7752347 := bstep (se 1 (by rfl) ⟨5814260, by rfl⟩ : syracuseStep 7752347 = 11628521) B11628521
theorem B5168231 : Blo 1911435 5168231 := bstep (se 1 (by rfl) ⟨3876173, by rfl⟩ : syracuseStep 5168231 = 7752347) B7752347
theorem B3445487 : Blo 1911435 3445487 := bstep (se 1 (by rfl) ⟨2584115, by rfl⟩ : syracuseStep 3445487 = 5168231) B5168231
theorem B2296991 : Blo 1911435 2296991 := bstep (se 1 (by rfl) ⟨1722743, by rfl⟩ : syracuseStep 2296991 = 3445487) B3445487
theorem B6125309 : Blo 1911435 6125309 := bstep (se 3 (by rfl) ⟨1148495, by rfl⟩ : syracuseStep 6125309 = 2296991) B2296991
theorem B4083539 : Blo 1911435 4083539 := bstep (se 1 (by rfl) ⟨3062654, by rfl⟩ : syracuseStep 4083539 = 6125309) B6125309
theorem B10889437 : Blo 1911435 10889437 := bstep (se 3 (by rfl) ⟨2041769, by rfl⟩ : syracuseStep 10889437 = 4083539) B4083539
theorem B14519249 : Blo 1911435 14519249 := bstep (se 2 (by rfl) ⟨5444718, by rfl⟩ : syracuseStep 14519249 = 10889437) B10889437
theorem B9679499 : Blo 1911435 9679499 := bstep (se 1 (by rfl) ⟨7259624, by rfl⟩ : syracuseStep 9679499 = 14519249) B14519249
theorem B6452999 : Blo 1911435 6452999 := bstep (se 1 (by rfl) ⟨4839749, by rfl⟩ : syracuseStep 6452999 = 9679499) B9679499
theorem B4301999 : Blo 1911435 4301999 := bstep (se 1 (by rfl) ⟨3226499, by rfl⟩ : syracuseStep 4301999 = 6452999) B6452999
theorem B2867999 : Blo 1911435 2867999 := bstep (se 1 (by rfl) ⟨2150999, by rfl⟩ : syracuseStep 2867999 = 4301999) B4301999
theorem B1911999 : Blo 1911435 1911999 := bstep (se 1 (by rfl) ⟨1433999, by rfl⟩ : syracuseStep 1911999 = 2867999) B2867999
theorem B2868005 : Blo 1911435 2868005 := bbase (se 4 (by rfl) ⟨268875, by rfl⟩ : syracuseStep 2868005 = 537751) (by norm_num)
theorem B1912003 : Blo 1911435 1912003 := bstep (se 1 (by rfl) ⟨1434002, by rfl⟩ : syracuseStep 1912003 = 2868005) B2868005
theorem B2419885 : Blo 1911435 2419885 := bbase (se 3 (by rfl) ⟨453728, by rfl⟩ : syracuseStep 2419885 = 907457) (by norm_num)
theorem B3226513 : Blo 1911435 3226513 := bstep (se 2 (by rfl) ⟨1209942, by rfl⟩ : syracuseStep 3226513 = 2419885) B2419885
theorem B4302017 : Blo 1911435 4302017 := bstep (se 2 (by rfl) ⟨1613256, by rfl⟩ : syracuseStep 4302017 = 3226513) B3226513
theorem B2868011 : Blo 1911435 2868011 := bstep (se 1 (by rfl) ⟨2151008, by rfl⟩ : syracuseStep 2868011 = 4302017) B4302017
theorem B1912007 : Blo 1911435 1912007 := bstep (se 1 (by rfl) ⟨1434005, by rfl⟩ : syracuseStep 1912007 = 2868011) B2868011
theorem B2151013 : Blo 1911435 2151013 := bbase (se 4 (by rfl) ⟨201657, by rfl⟩ : syracuseStep 2151013 = 403315) (by norm_num)
theorem B2868017 : Blo 1911435 2868017 := bstep (se 2 (by rfl) ⟨1075506, by rfl⟩ : syracuseStep 2868017 = 2151013) B2151013
theorem B1912011 : Blo 1911435 1912011 := bstep (se 1 (by rfl) ⟨1434008, by rfl⟩ : syracuseStep 1912011 = 2868017) B2868017
theorem B3445517 : Blo 1911435 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B2297011 : Blo 1911435 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B3062681 : Blo 1911435 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B2041787 : Blo 1911435 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B5444765 : Blo 1911435 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B3629843 : Blo 1911435 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B2419895 : Blo 1911435 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B6453053 : Blo 1911435 6453053 := bstep (se 3 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 6453053 = 2419895) B2419895
theorem B4302035 : Blo 1911435 4302035 := bstep (se 1 (by rfl) ⟨3226526, by rfl⟩ : syracuseStep 4302035 = 6453053) B6453053
theorem B2868023 : Blo 1911435 2868023 := bstep (se 1 (by rfl) ⟨2151017, by rfl⟩ : syracuseStep 2868023 = 4302035) B4302035
theorem B1912015 : Blo 1911435 1912015 := bstep (se 1 (by rfl) ⟨1434011, by rfl⟩ : syracuseStep 1912015 = 2868023) B2868023
theorem B2868029 : Blo 1911435 2868029 := bbase (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) (by norm_num)
theorem B1912019 : Blo 1911435 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B4302053 : Blo 1911435 4302053 := bbase (se 4 (by rfl) ⟨403317, by rfl⟩ : syracuseStep 4302053 = 806635) (by norm_num)
theorem B2868035 : Blo 1911435 2868035 := bstep (se 1 (by rfl) ⟨2151026, by rfl⟩ : syracuseStep 2868035 = 4302053) B4302053
theorem B1912023 : Blo 1911435 1912023 := bstep (se 1 (by rfl) ⟨1434017, by rfl⟩ : syracuseStep 1912023 = 2868035) B2868035
theorem B4839821 : Blo 1911435 4839821 := bbase (se 3 (by rfl) ⟨907466, by rfl⟩ : syracuseStep 4839821 = 1814933) (by norm_num)
theorem B3226547 : Blo 1911435 3226547 := bstep (se 1 (by rfl) ⟨2419910, by rfl⟩ : syracuseStep 3226547 = 4839821) B4839821
theorem B2151031 : Blo 1911435 2151031 := bstep (se 1 (by rfl) ⟨1613273, by rfl⟩ : syracuseStep 2151031 = 3226547) B3226547
theorem B2868041 : Blo 1911435 2868041 := bstep (se 2 (by rfl) ⟨1075515, by rfl⟩ : syracuseStep 2868041 = 2151031) B2151031
theorem B1912027 : Blo 1911435 1912027 := bstep (se 1 (by rfl) ⟨1434020, by rfl⟩ : syracuseStep 1912027 = 2868041) B2868041
theorem B2722405 : Blo 1911435 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B3629873 : Blo 1911435 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B9679661 : Blo 1911435 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B6453107 : Blo 1911435 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B4302071 : Blo 1911435 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B2868047 : Blo 1911435 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1912031 : Blo 1911435 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B2868053 : Blo 1911435 2868053 := bbase (se 9 (by rfl) ⟨8402, by rfl⟩ : syracuseStep 2868053 = 16805) (by norm_num)
theorem B1912035 : Blo 1911435 1912035 := bstep (se 1 (by rfl) ⟨1434026, by rfl⟩ : syracuseStep 1912035 = 2868053) B2868053
theorem B19623541 : Blo 1911435 19623541 := bbase (se 5 (by rfl) ⟨919853, by rfl⟩ : syracuseStep 19623541 = 1839707) (by norm_num)
theorem B26164721 : Blo 1911435 26164721 := bstep (se 2 (by rfl) ⟨9811770, by rfl⟩ : syracuseStep 26164721 = 19623541) B19623541
theorem B17443147 : Blo 1911435 17443147 := bstep (se 1 (by rfl) ⟨13082360, by rfl⟩ : syracuseStep 17443147 = 26164721) B26164721
theorem B23257529 : Blo 1911435 23257529 := bstep (se 2 (by rfl) ⟨8721573, by rfl⟩ : syracuseStep 23257529 = 17443147) B17443147
theorem B15505019 : Blo 1911435 15505019 := bstep (se 1 (by rfl) ⟨11628764, by rfl⟩ : syracuseStep 15505019 = 23257529) B23257529
theorem B10336679 : Blo 1911435 10336679 := bstep (se 1 (by rfl) ⟨7752509, by rfl⟩ : syracuseStep 10336679 = 15505019) B15505019
theorem B6891119 : Blo 1911435 6891119 := bstep (se 1 (by rfl) ⟨5168339, by rfl⟩ : syracuseStep 6891119 = 10336679) B10336679
theorem B4594079 : Blo 1911435 4594079 := bstep (se 1 (by rfl) ⟨3445559, by rfl⟩ : syracuseStep 4594079 = 6891119) B6891119
theorem B3062719 : Blo 1911435 3062719 := bstep (se 1 (by rfl) ⟨2297039, by rfl⟩ : syracuseStep 3062719 = 4594079) B4594079
theorem B4083625 : Blo 1911435 4083625 := bstep (se 2 (by rfl) ⟨1531359, by rfl⟩ : syracuseStep 4083625 = 3062719) B3062719
theorem B5444833 : Blo 1911435 5444833 := bstep (se 2 (by rfl) ⟨2041812, by rfl⟩ : syracuseStep 5444833 = 4083625) B4083625
theorem B7259777 : Blo 1911435 7259777 := bstep (se 2 (by rfl) ⟨2722416, by rfl⟩ : syracuseStep 7259777 = 5444833) B5444833
theorem B4839851 : Blo 1911435 4839851 := bstep (se 1 (by rfl) ⟨3629888, by rfl⟩ : syracuseStep 4839851 = 7259777) B7259777
theorem B3226567 : Blo 1911435 3226567 := bstep (se 1 (by rfl) ⟨2419925, by rfl⟩ : syracuseStep 3226567 = 4839851) B4839851
theorem B4302089 : Blo 1911435 4302089 := bstep (se 2 (by rfl) ⟨1613283, by rfl⟩ : syracuseStep 4302089 = 3226567) B3226567
theorem B2868059 : Blo 1911435 2868059 := bstep (se 1 (by rfl) ⟨2151044, by rfl⟩ : syracuseStep 2868059 = 4302089) B4302089
theorem B1912039 : Blo 1911435 1912039 := bstep (se 1 (by rfl) ⟨1434029, by rfl⟩ : syracuseStep 1912039 = 2868059) B2868059
theorem B2151049 : Blo 1911435 2151049 := bbase (se 2 (by rfl) ⟨806643, by rfl⟩ : syracuseStep 2151049 = 1613287) (by norm_num)
theorem B2868065 : Blo 1911435 2868065 := bstep (se 2 (by rfl) ⟨1075524, by rfl⟩ : syracuseStep 2868065 = 2151049) B2151049
theorem B1912043 : Blo 1911435 1912043 := bstep (se 1 (by rfl) ⟨1434032, by rfl⟩ : syracuseStep 1912043 = 2868065) B2868065
theorem B6541205 : Blo 1911435 6541205 := bbase (se 6 (by rfl) ⟨153309, by rfl⟩ : syracuseStep 6541205 = 306619) (by norm_num)
theorem B69772853 : Blo 1911435 69772853 := bstep (se 5 (by rfl) ⟨3270602, by rfl⟩ : syracuseStep 69772853 = 6541205) B6541205
theorem B46515235 : Blo 1911435 46515235 := bstep (se 1 (by rfl) ⟨34886426, by rfl⟩ : syracuseStep 46515235 = 69772853) B69772853
theorem B62020313 : Blo 1911435 62020313 := bstep (se 2 (by rfl) ⟨23257617, by rfl⟩ : syracuseStep 62020313 = 46515235) B46515235
theorem B41346875 : Blo 1911435 41346875 := bstep (se 1 (by rfl) ⟨31010156, by rfl⟩ : syracuseStep 41346875 = 62020313) B62020313
theorem B27564583 : Blo 1911435 27564583 := bstep (se 1 (by rfl) ⟨20673437, by rfl⟩ : syracuseStep 27564583 = 41346875) B41346875
theorem B36752777 : Blo 1911435 36752777 := bstep (se 2 (by rfl) ⟨13782291, by rfl⟩ : syracuseStep 36752777 = 27564583) B27564583
theorem B24501851 : Blo 1911435 24501851 := bstep (se 1 (by rfl) ⟨18376388, by rfl⟩ : syracuseStep 24501851 = 36752777) B36752777
theorem B16334567 : Blo 1911435 16334567 := bstep (se 1 (by rfl) ⟨12250925, by rfl⟩ : syracuseStep 16334567 = 24501851) B24501851
theorem B10889711 : Blo 1911435 10889711 := bstep (se 1 (by rfl) ⟨8167283, by rfl⟩ : syracuseStep 10889711 = 16334567) B16334567
theorem B7259807 : Blo 1911435 7259807 := bstep (se 1 (by rfl) ⟨5444855, by rfl⟩ : syracuseStep 7259807 = 10889711) B10889711
theorem B4839871 : Blo 1911435 4839871 := bstep (se 1 (by rfl) ⟨3629903, by rfl⟩ : syracuseStep 4839871 = 7259807) B7259807
theorem B6453161 : Blo 1911435 6453161 := bstep (se 2 (by rfl) ⟨2419935, by rfl⟩ : syracuseStep 6453161 = 4839871) B4839871
theorem B4302107 : Blo 1911435 4302107 := bstep (se 1 (by rfl) ⟨3226580, by rfl⟩ : syracuseStep 4302107 = 6453161) B6453161
theorem B2868071 : Blo 1911435 2868071 := bstep (se 1 (by rfl) ⟨2151053, by rfl⟩ : syracuseStep 2868071 = 4302107) B4302107
theorem B1912047 : Blo 1911435 1912047 := bstep (se 1 (by rfl) ⟨1434035, by rfl⟩ : syracuseStep 1912047 = 2868071) B2868071
theorem B2868077 : Blo 1911435 2868077 := bbase (se 3 (by rfl) ⟨537764, by rfl⟩ : syracuseStep 2868077 = 1075529) (by norm_num)
theorem B1912051 : Blo 1911435 1912051 := bstep (se 1 (by rfl) ⟨1434038, by rfl⟩ : syracuseStep 1912051 = 2868077) B2868077
theorem B4302125 : Blo 1911435 4302125 := bbase (se 3 (by rfl) ⟨806648, by rfl⟩ : syracuseStep 4302125 = 1613297) (by norm_num)
theorem B2868083 : Blo 1911435 2868083 := bstep (se 1 (by rfl) ⟨2151062, by rfl⟩ : syracuseStep 2868083 = 4302125) B4302125
theorem B1912055 : Blo 1911435 1912055 := bstep (se 1 (by rfl) ⟨1434041, by rfl⟩ : syracuseStep 1912055 = 2868083) B2868083
theorem B6209077 : Blo 1911435 6209077 := bbase (se 5 (by rfl) ⟨291050, by rfl⟩ : syracuseStep 6209077 = 582101) (by norm_num)
theorem B8278769 : Blo 1911435 8278769 := bstep (se 2 (by rfl) ⟨3104538, by rfl⟩ : syracuseStep 8278769 = 6209077) B6209077
theorem B5519179 : Blo 1911435 5519179 := bstep (se 1 (by rfl) ⟨4139384, by rfl⟩ : syracuseStep 5519179 = 8278769) B8278769
theorem B7358905 : Blo 1911435 7358905 := bstep (se 2 (by rfl) ⟨2759589, by rfl⟩ : syracuseStep 7358905 = 5519179) B5519179
theorem B9811873 : Blo 1911435 9811873 := bstep (se 2 (by rfl) ⟨3679452, by rfl⟩ : syracuseStep 9811873 = 7358905) B7358905
theorem B52329989 : Blo 1911435 52329989 := bstep (se 4 (by rfl) ⟨4905936, by rfl⟩ : syracuseStep 52329989 = 9811873) B9811873
theorem B34886659 : Blo 1911435 34886659 := bstep (se 1 (by rfl) ⟨26164994, by rfl⟩ : syracuseStep 34886659 = 52329989) B52329989
theorem B46515545 : Blo 1911435 46515545 := bstep (se 2 (by rfl) ⟨17443329, by rfl⟩ : syracuseStep 46515545 = 34886659) B34886659
theorem B31010363 : Blo 1911435 31010363 := bstep (se 1 (by rfl) ⟨23257772, by rfl⟩ : syracuseStep 31010363 = 46515545) B46515545
theorem B20673575 : Blo 1911435 20673575 := bstep (se 1 (by rfl) ⟨15505181, by rfl⟩ : syracuseStep 20673575 = 31010363) B31010363
theorem B13782383 : Blo 1911435 13782383 := bstep (se 1 (by rfl) ⟨10336787, by rfl⟩ : syracuseStep 13782383 = 20673575) B20673575
theorem B9188255 : Blo 1911435 9188255 := bstep (se 1 (by rfl) ⟨6891191, by rfl⟩ : syracuseStep 9188255 = 13782383) B13782383
theorem B6125503 : Blo 1911435 6125503 := bstep (se 1 (by rfl) ⟨4594127, by rfl⟩ : syracuseStep 6125503 = 9188255) B9188255
theorem B8167337 : Blo 1911435 8167337 := bstep (se 2 (by rfl) ⟨3062751, by rfl⟩ : syracuseStep 8167337 = 6125503) B6125503
theorem B5444891 : Blo 1911435 5444891 := bstep (se 1 (by rfl) ⟨4083668, by rfl⟩ : syracuseStep 5444891 = 8167337) B8167337
theorem B3629927 : Blo 1911435 3629927 := bstep (se 1 (by rfl) ⟨2722445, by rfl⟩ : syracuseStep 3629927 = 5444891) B5444891
theorem B2419951 : Blo 1911435 2419951 := bstep (se 1 (by rfl) ⟨1814963, by rfl⟩ : syracuseStep 2419951 = 3629927) B3629927
theorem B3226601 : Blo 1911435 3226601 := bstep (se 2 (by rfl) ⟨1209975, by rfl⟩ : syracuseStep 3226601 = 2419951) B2419951
theorem B2151067 : Blo 1911435 2151067 := bstep (se 1 (by rfl) ⟨1613300, by rfl⟩ : syracuseStep 2151067 = 3226601) B3226601
theorem B2868089 : Blo 1911435 2868089 := bstep (se 2 (by rfl) ⟨1075533, by rfl⟩ : syracuseStep 2868089 = 2151067) B2151067
theorem B1912059 : Blo 1911435 1912059 := bstep (se 1 (by rfl) ⟨1434044, by rfl⟩ : syracuseStep 1912059 = 2868089) B2868089
theorem B2328409 : Blo 1911435 2328409 := bbase (se 2 (by rfl) ⟨873153, by rfl⟩ : syracuseStep 2328409 = 1746307) (by norm_num)
theorem B12418181 : Blo 1911435 12418181 := bstep (se 4 (by rfl) ⟨1164204, by rfl⟩ : syracuseStep 12418181 = 2328409) B2328409
theorem B8278787 : Blo 1911435 8278787 := bstep (se 1 (by rfl) ⟨6209090, by rfl⟩ : syracuseStep 8278787 = 12418181) B12418181
theorem B5519191 : Blo 1911435 5519191 := bstep (se 1 (by rfl) ⟨4139393, by rfl⟩ : syracuseStep 5519191 = 8278787) B8278787
theorem B7358921 : Blo 1911435 7358921 := bstep (se 2 (by rfl) ⟨2759595, by rfl⟩ : syracuseStep 7358921 = 5519191) B5519191
theorem B4905947 : Blo 1911435 4905947 := bstep (se 1 (by rfl) ⟨3679460, by rfl⟩ : syracuseStep 4905947 = 7358921) B7358921
theorem B3270631 : Blo 1911435 3270631 := bstep (se 1 (by rfl) ⟨2452973, by rfl⟩ : syracuseStep 3270631 = 4905947) B4905947
theorem B4360841 : Blo 1911435 4360841 := bstep (se 2 (by rfl) ⟨1635315, by rfl⟩ : syracuseStep 4360841 = 3270631) B3270631
theorem B2907227 : Blo 1911435 2907227 := bstep (se 1 (by rfl) ⟨2180420, by rfl⟩ : syracuseStep 2907227 = 4360841) B4360841
theorem B1938151 : Blo 1911435 1938151 := bstep (se 1 (by rfl) ⟨1453613, by rfl⟩ : syracuseStep 1938151 = 2907227) B2907227
theorem B10336805 : Blo 1911435 10336805 := bstep (se 4 (by rfl) ⟨969075, by rfl⟩ : syracuseStep 10336805 = 1938151) B1938151
theorem B6891203 : Blo 1911435 6891203 := bstep (se 1 (by rfl) ⟨5168402, by rfl⟩ : syracuseStep 6891203 = 10336805) B10336805
theorem B18376541 : Blo 1911435 18376541 := bstep (se 3 (by rfl) ⟨3445601, by rfl⟩ : syracuseStep 18376541 = 6891203) B6891203
theorem B12251027 : Blo 1911435 12251027 := bstep (se 1 (by rfl) ⟨9188270, by rfl⟩ : syracuseStep 12251027 = 18376541) B18376541
theorem B32669405 : Blo 1911435 32669405 := bstep (se 3 (by rfl) ⟨6125513, by rfl⟩ : syracuseStep 32669405 = 12251027) B12251027
theorem B21779603 : Blo 1911435 21779603 := bstep (se 1 (by rfl) ⟨16334702, by rfl⟩ : syracuseStep 21779603 = 32669405) B32669405
theorem B14519735 : Blo 1911435 14519735 := bstep (se 1 (by rfl) ⟨10889801, by rfl⟩ : syracuseStep 14519735 = 21779603) B21779603
theorem B9679823 : Blo 1911435 9679823 := bstep (se 1 (by rfl) ⟨7259867, by rfl⟩ : syracuseStep 9679823 = 14519735) B14519735
theorem B6453215 : Blo 1911435 6453215 := bstep (se 1 (by rfl) ⟨4839911, by rfl⟩ : syracuseStep 6453215 = 9679823) B9679823
theorem B4302143 : Blo 1911435 4302143 := bstep (se 1 (by rfl) ⟨3226607, by rfl⟩ : syracuseStep 4302143 = 6453215) B6453215
theorem B2868095 : Blo 1911435 2868095 := bstep (se 1 (by rfl) ⟨2151071, by rfl⟩ : syracuseStep 2868095 = 4302143) B4302143
theorem B1912063 : Blo 1911435 1912063 := bstep (se 1 (by rfl) ⟨1434047, by rfl⟩ : syracuseStep 1912063 = 2868095) B2868095
theorem B2868101 : Blo 1911435 2868101 := bbase (se 4 (by rfl) ⟨268884, by rfl⟩ : syracuseStep 2868101 = 537769) (by norm_num)
theorem B1912067 : Blo 1911435 1912067 := bstep (se 1 (by rfl) ⟨1434050, by rfl⟩ : syracuseStep 1912067 = 2868101) B2868101
theorem B3226621 : Blo 1911435 3226621 := bbase (se 3 (by rfl) ⟨604991, by rfl⟩ : syracuseStep 3226621 = 1209983) (by norm_num)
theorem B4302161 : Blo 1911435 4302161 := bstep (se 2 (by rfl) ⟨1613310, by rfl⟩ : syracuseStep 4302161 = 3226621) B3226621
theorem B2868107 : Blo 1911435 2868107 := bstep (se 1 (by rfl) ⟨2151080, by rfl⟩ : syracuseStep 2868107 = 4302161) B4302161
theorem B1912071 : Blo 1911435 1912071 := bstep (se 1 (by rfl) ⟨1434053, by rfl⟩ : syracuseStep 1912071 = 2868107) B2868107
theorem B2151085 : Blo 1911435 2151085 := bbase (se 3 (by rfl) ⟨403328, by rfl⟩ : syracuseStep 2151085 = 806657) (by norm_num)
theorem B2868113 : Blo 1911435 2868113 := bstep (se 2 (by rfl) ⟨1075542, by rfl⟩ : syracuseStep 2868113 = 2151085) B2151085
theorem B1912075 : Blo 1911435 1912075 := bstep (se 1 (by rfl) ⟨1434056, by rfl⟩ : syracuseStep 1912075 = 2868113) B2868113
theorem B6453269 : Blo 1911435 6453269 := bbase (se 6 (by rfl) ⟨151248, by rfl⟩ : syracuseStep 6453269 = 302497) (by norm_num)
theorem B4302179 : Blo 1911435 4302179 := bstep (se 1 (by rfl) ⟨3226634, by rfl⟩ : syracuseStep 4302179 = 6453269) B6453269
theorem B2868119 : Blo 1911435 2868119 := bstep (se 1 (by rfl) ⟨2151089, by rfl⟩ : syracuseStep 2868119 = 4302179) B4302179
theorem B1912079 : Blo 1911435 1912079 := bstep (se 1 (by rfl) ⟨1434059, by rfl⟩ : syracuseStep 1912079 = 2868119) B2868119
theorem B2868125 : Blo 1911435 2868125 := bbase (se 3 (by rfl) ⟨537773, by rfl⟩ : syracuseStep 2868125 = 1075547) (by norm_num)
theorem B1912083 : Blo 1911435 1912083 := bstep (se 1 (by rfl) ⟨1434062, by rfl⟩ : syracuseStep 1912083 = 2868125) B2868125
theorem B4302197 : Blo 1911435 4302197 := bbase (se 5 (by rfl) ⟨201665, by rfl⟩ : syracuseStep 4302197 = 403331) (by norm_num)
theorem B2868131 : Blo 1911435 2868131 := bstep (se 1 (by rfl) ⟨2151098, by rfl⟩ : syracuseStep 2868131 = 4302197) B4302197
theorem B1912087 : Blo 1911435 1912087 := bstep (se 1 (by rfl) ⟨1434065, by rfl⟩ : syracuseStep 1912087 = 2868131) B2868131
theorem B2453009 : Blo 1911435 2453009 := bbase (se 2 (by rfl) ⟨919878, by rfl⟩ : syracuseStep 2453009 = 1839757) (by norm_num)
theorem B26165429 : Blo 1911435 26165429 := bstep (se 5 (by rfl) ⟨1226504, by rfl⟩ : syracuseStep 26165429 = 2453009) B2453009
theorem B17443619 : Blo 1911435 17443619 := bstep (se 1 (by rfl) ⟨13082714, by rfl⟩ : syracuseStep 17443619 = 26165429) B26165429
theorem B11629079 : Blo 1911435 11629079 := bstep (se 1 (by rfl) ⟨8721809, by rfl⟩ : syracuseStep 11629079 = 17443619) B17443619
theorem B7752719 : Blo 1911435 7752719 := bstep (se 1 (by rfl) ⟨5814539, by rfl⟩ : syracuseStep 7752719 = 11629079) B11629079
theorem B20673917 : Blo 1911435 20673917 := bstep (se 3 (by rfl) ⟨3876359, by rfl⟩ : syracuseStep 20673917 = 7752719) B7752719
theorem B13782611 : Blo 1911435 13782611 := bstep (se 1 (by rfl) ⟨10336958, by rfl⟩ : syracuseStep 13782611 = 20673917) B20673917
theorem B9188407 : Blo 1911435 9188407 := bstep (se 1 (by rfl) ⟨6891305, by rfl⟩ : syracuseStep 9188407 = 13782611) B13782611
theorem B12251209 : Blo 1911435 12251209 := bstep (se 2 (by rfl) ⟨4594203, by rfl⟩ : syracuseStep 12251209 = 9188407) B9188407
theorem B16334945 : Blo 1911435 16334945 := bstep (se 2 (by rfl) ⟨6125604, by rfl⟩ : syracuseStep 16334945 = 12251209) B12251209
theorem B10889963 : Blo 1911435 10889963 := bstep (se 1 (by rfl) ⟨8167472, by rfl⟩ : syracuseStep 10889963 = 16334945) B16334945
theorem B7259975 : Blo 1911435 7259975 := bstep (se 1 (by rfl) ⟨5444981, by rfl⟩ : syracuseStep 7259975 = 10889963) B10889963
theorem B4839983 : Blo 1911435 4839983 := bstep (se 1 (by rfl) ⟨3629987, by rfl⟩ : syracuseStep 4839983 = 7259975) B7259975
theorem B3226655 : Blo 1911435 3226655 := bstep (se 1 (by rfl) ⟨2419991, by rfl⟩ : syracuseStep 3226655 = 4839983) B4839983
theorem B2151103 : Blo 1911435 2151103 := bstep (se 1 (by rfl) ⟨1613327, by rfl⟩ : syracuseStep 2151103 = 3226655) B3226655
theorem B2868137 : Blo 1911435 2868137 := bstep (se 2 (by rfl) ⟨1075551, by rfl⟩ : syracuseStep 2868137 = 2151103) B2151103
theorem B1912091 : Blo 1911435 1912091 := bstep (se 1 (by rfl) ⟨1434068, by rfl⟩ : syracuseStep 1912091 = 2868137) B2868137
theorem B7259989 : Blo 1911435 7259989 := bbase (se 9 (by rfl) ⟨21269, by rfl⟩ : syracuseStep 7259989 = 42539) (by norm_num)
theorem B9679985 : Blo 1911435 9679985 := bstep (se 2 (by rfl) ⟨3629994, by rfl⟩ : syracuseStep 9679985 = 7259989) B7259989
theorem B6453323 : Blo 1911435 6453323 := bstep (se 1 (by rfl) ⟨4839992, by rfl⟩ : syracuseStep 6453323 = 9679985) B9679985
theorem B4302215 : Blo 1911435 4302215 := bstep (se 1 (by rfl) ⟨3226661, by rfl⟩ : syracuseStep 4302215 = 6453323) B6453323
theorem B2868143 : Blo 1911435 2868143 := bstep (se 1 (by rfl) ⟨2151107, by rfl⟩ : syracuseStep 2868143 = 4302215) B4302215
theorem B1912095 : Blo 1911435 1912095 := bstep (se 1 (by rfl) ⟨1434071, by rfl⟩ : syracuseStep 1912095 = 2868143) B2868143
theorem B2868149 : Blo 1911435 2868149 := bbase (se 5 (by rfl) ⟨134444, by rfl⟩ : syracuseStep 2868149 = 268889) (by norm_num)
theorem B1912099 : Blo 1911435 1912099 := bstep (se 1 (by rfl) ⟨1434074, by rfl⟩ : syracuseStep 1912099 = 2868149) B2868149
theorem B4840013 : Blo 1911435 4840013 := bbase (se 3 (by rfl) ⟨907502, by rfl⟩ : syracuseStep 4840013 = 1815005) (by norm_num)
theorem B3226675 : Blo 1911435 3226675 := bstep (se 1 (by rfl) ⟨2420006, by rfl⟩ : syracuseStep 3226675 = 4840013) B4840013
theorem B4302233 : Blo 1911435 4302233 := bstep (se 2 (by rfl) ⟨1613337, by rfl⟩ : syracuseStep 4302233 = 3226675) B3226675
theorem B2868155 : Blo 1911435 2868155 := bstep (se 1 (by rfl) ⟨2151116, by rfl⟩ : syracuseStep 2868155 = 4302233) B4302233
theorem B1912103 : Blo 1911435 1912103 := bstep (se 1 (by rfl) ⟨1434077, by rfl⟩ : syracuseStep 1912103 = 2868155) B2868155
theorem B2151121 : Blo 1911435 2151121 := bbase (se 2 (by rfl) ⟨806670, by rfl⟩ : syracuseStep 2151121 = 1613341) (by norm_num)
theorem B2868161 : Blo 1911435 2868161 := bstep (se 2 (by rfl) ⟨1075560, by rfl⟩ : syracuseStep 2868161 = 2151121) B2151121
theorem B1912107 : Blo 1911435 1912107 := bstep (se 1 (by rfl) ⟨1434080, by rfl⟩ : syracuseStep 1912107 = 2868161) B2868161
theorem B6125669 : Blo 1911435 6125669 := bbase (se 4 (by rfl) ⟨574281, by rfl⟩ : syracuseStep 6125669 = 1148563) (by norm_num)
theorem B4083779 : Blo 1911435 4083779 := bstep (se 1 (by rfl) ⟨3062834, by rfl⟩ : syracuseStep 4083779 = 6125669) B6125669
theorem B2722519 : Blo 1911435 2722519 := bstep (se 1 (by rfl) ⟨2041889, by rfl⟩ : syracuseStep 2722519 = 4083779) B4083779
theorem B3630025 : Blo 1911435 3630025 := bstep (se 2 (by rfl) ⟨1361259, by rfl⟩ : syracuseStep 3630025 = 2722519) B2722519
theorem B4840033 : Blo 1911435 4840033 := bstep (se 2 (by rfl) ⟨1815012, by rfl⟩ : syracuseStep 4840033 = 3630025) B3630025
theorem B6453377 : Blo 1911435 6453377 := bstep (se 2 (by rfl) ⟨2420016, by rfl⟩ : syracuseStep 6453377 = 4840033) B4840033
theorem B4302251 : Blo 1911435 4302251 := bstep (se 1 (by rfl) ⟨3226688, by rfl⟩ : syracuseStep 4302251 = 6453377) B6453377
theorem B2868167 : Blo 1911435 2868167 := bstep (se 1 (by rfl) ⟨2151125, by rfl⟩ : syracuseStep 2868167 = 4302251) B4302251
theorem B1912111 : Blo 1911435 1912111 := bstep (se 1 (by rfl) ⟨1434083, by rfl⟩ : syracuseStep 1912111 = 2868167) B2868167
theorem B2868173 : Blo 1911435 2868173 := bbase (se 3 (by rfl) ⟨537782, by rfl⟩ : syracuseStep 2868173 = 1075565) (by norm_num)
theorem B1912115 : Blo 1911435 1912115 := bstep (se 1 (by rfl) ⟨1434086, by rfl⟩ : syracuseStep 1912115 = 2868173) B2868173
theorem B4302269 : Blo 1911435 4302269 := bbase (se 3 (by rfl) ⟨806675, by rfl⟩ : syracuseStep 4302269 = 1613351) (by norm_num)
theorem B2868179 : Blo 1911435 2868179 := bstep (se 1 (by rfl) ⟨2151134, by rfl⟩ : syracuseStep 2868179 = 4302269) B4302269
theorem B1912119 : Blo 1911435 1912119 := bstep (se 1 (by rfl) ⟨1434089, by rfl⟩ : syracuseStep 1912119 = 2868179) B2868179
theorem B3226709 : Blo 1911435 3226709 := bbase (se 8 (by rfl) ⟨18906, by rfl⟩ : syracuseStep 3226709 = 37813) (by norm_num)
theorem B2151139 : Blo 1911435 2151139 := bstep (se 1 (by rfl) ⟨1613354, by rfl⟩ : syracuseStep 2151139 = 3226709) B3226709
theorem B2868185 : Blo 1911435 2868185 := bstep (se 2 (by rfl) ⟨1075569, by rfl⟩ : syracuseStep 2868185 = 2151139) B2151139
theorem B1912123 : Blo 1911435 1912123 := bstep (se 1 (by rfl) ⟨1434092, by rfl⟩ : syracuseStep 1912123 = 2868185) B2868185
theorem B13782869 : Blo 1911435 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B9188579 : Blo 1911435 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B6125719 : Blo 1911435 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B8167625 : Blo 1911435 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B5445083 : Blo 1911435 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B14520221 : Blo 1911435 14520221 := bstep (se 3 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 14520221 = 5445083) B5445083
theorem B9680147 : Blo 1911435 9680147 := bstep (se 1 (by rfl) ⟨7260110, by rfl⟩ : syracuseStep 9680147 = 14520221) B14520221
theorem B6453431 : Blo 1911435 6453431 := bstep (se 1 (by rfl) ⟨4840073, by rfl⟩ : syracuseStep 6453431 = 9680147) B9680147
theorem B4302287 : Blo 1911435 4302287 := bstep (se 1 (by rfl) ⟨3226715, by rfl⟩ : syracuseStep 4302287 = 6453431) B6453431
theorem B2868191 : Blo 1911435 2868191 := bstep (se 1 (by rfl) ⟨2151143, by rfl⟩ : syracuseStep 2868191 = 4302287) B4302287
theorem B1912127 : Blo 1911435 1912127 := bstep (se 1 (by rfl) ⟨1434095, by rfl⟩ : syracuseStep 1912127 = 2868191) B2868191
theorem B2868197 : Blo 1911435 2868197 := bbase (se 4 (by rfl) ⟨268893, by rfl⟩ : syracuseStep 2868197 = 537787) (by norm_num)
theorem B1912131 : Blo 1911435 1912131 := bstep (se 1 (by rfl) ⟨1434098, by rfl⟩ : syracuseStep 1912131 = 2868197) B2868197
theorem B3445733 : Blo 1911435 3445733 := bbase (se 4 (by rfl) ⟨323037, by rfl⟩ : syracuseStep 3445733 = 646075) (by norm_num)
theorem B2297155 : Blo 1911435 2297155 := bstep (se 1 (by rfl) ⟨1722866, by rfl⟩ : syracuseStep 2297155 = 3445733) B3445733
theorem B3062873 : Blo 1911435 3062873 := bstep (se 2 (by rfl) ⟨1148577, by rfl⟩ : syracuseStep 3062873 = 2297155) B2297155
theorem B8167661 : Blo 1911435 8167661 := bstep (se 3 (by rfl) ⟨1531436, by rfl⟩ : syracuseStep 8167661 = 3062873) B3062873
theorem B5445107 : Blo 1911435 5445107 := bstep (se 1 (by rfl) ⟨4083830, by rfl⟩ : syracuseStep 5445107 = 8167661) B8167661
theorem B3630071 : Blo 1911435 3630071 := bstep (se 1 (by rfl) ⟨2722553, by rfl⟩ : syracuseStep 3630071 = 5445107) B5445107
theorem B2420047 : Blo 1911435 2420047 := bstep (se 1 (by rfl) ⟨1815035, by rfl⟩ : syracuseStep 2420047 = 3630071) B3630071
theorem B3226729 : Blo 1911435 3226729 := bstep (se 2 (by rfl) ⟨1210023, by rfl⟩ : syracuseStep 3226729 = 2420047) B2420047
theorem B4302305 : Blo 1911435 4302305 := bstep (se 2 (by rfl) ⟨1613364, by rfl⟩ : syracuseStep 4302305 = 3226729) B3226729
theorem B2868203 : Blo 1911435 2868203 := bstep (se 1 (by rfl) ⟨2151152, by rfl⟩ : syracuseStep 2868203 = 4302305) B4302305
theorem B1912135 : Blo 1911435 1912135 := bstep (se 1 (by rfl) ⟨1434101, by rfl⟩ : syracuseStep 1912135 = 2868203) B2868203
theorem B2151157 : Blo 1911435 2151157 := bbase (se 5 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 2151157 = 201671) (by norm_num)
theorem B2868209 : Blo 1911435 2868209 := bstep (se 2 (by rfl) ⟨1075578, by rfl⟩ : syracuseStep 2868209 = 2151157) B2151157
theorem B1912139 : Blo 1911435 1912139 := bstep (se 1 (by rfl) ⟨1434104, by rfl⟩ : syracuseStep 1912139 = 2868209) B2868209
theorem B2420057 : Blo 1911435 2420057 := bbase (se 2 (by rfl) ⟨907521, by rfl⟩ : syracuseStep 2420057 = 1815043) (by norm_num)
theorem B6453485 : Blo 1911435 6453485 := bstep (se 3 (by rfl) ⟨1210028, by rfl⟩ : syracuseStep 6453485 = 2420057) B2420057
theorem B4302323 : Blo 1911435 4302323 := bstep (se 1 (by rfl) ⟨3226742, by rfl⟩ : syracuseStep 4302323 = 6453485) B6453485
theorem B2868215 : Blo 1911435 2868215 := bstep (se 1 (by rfl) ⟨2151161, by rfl⟩ : syracuseStep 2868215 = 4302323) B4302323
theorem B1912143 : Blo 1911435 1912143 := bstep (se 1 (by rfl) ⟨1434107, by rfl⟩ : syracuseStep 1912143 = 2868215) B2868215
theorem B2868221 : Blo 1911435 2868221 := bbase (se 3 (by rfl) ⟨537791, by rfl⟩ : syracuseStep 2868221 = 1075583) (by norm_num)
theorem B1912147 : Blo 1911435 1912147 := bstep (se 1 (by rfl) ⟨1434110, by rfl⟩ : syracuseStep 1912147 = 2868221) B2868221
theorem B4302341 : Blo 1911435 4302341 := bbase (se 4 (by rfl) ⟨403344, by rfl⟩ : syracuseStep 4302341 = 806689) (by norm_num)
theorem B2868227 : Blo 1911435 2868227 := bstep (se 1 (by rfl) ⟨2151170, by rfl⟩ : syracuseStep 2868227 = 4302341) B4302341
theorem B1912151 : Blo 1911435 1912151 := bstep (se 1 (by rfl) ⟨1434113, by rfl⟩ : syracuseStep 1912151 = 2868227) B2868227
theorem B3630109 : Blo 1911435 3630109 := bbase (se 3 (by rfl) ⟨680645, by rfl⟩ : syracuseStep 3630109 = 1361291) (by norm_num)
theorem B4840145 : Blo 1911435 4840145 := bstep (se 2 (by rfl) ⟨1815054, by rfl⟩ : syracuseStep 4840145 = 3630109) B3630109
theorem B3226763 : Blo 1911435 3226763 := bstep (se 1 (by rfl) ⟨2420072, by rfl⟩ : syracuseStep 3226763 = 4840145) B4840145
theorem B2151175 : Blo 1911435 2151175 := bstep (se 1 (by rfl) ⟨1613381, by rfl⟩ : syracuseStep 2151175 = 3226763) B3226763
theorem B2868233 : Blo 1911435 2868233 := bstep (se 2 (by rfl) ⟨1075587, by rfl⟩ : syracuseStep 2868233 = 2151175) B2151175
theorem B1912155 : Blo 1911435 1912155 := bstep (se 1 (by rfl) ⟨1434116, by rfl⟩ : syracuseStep 1912155 = 2868233) B2868233
theorem B9680309 : Blo 1911435 9680309 := bbase (se 5 (by rfl) ⟨453764, by rfl⟩ : syracuseStep 9680309 = 907529) (by norm_num)
theorem B6453539 : Blo 1911435 6453539 := bstep (se 1 (by rfl) ⟨4840154, by rfl⟩ : syracuseStep 6453539 = 9680309) B9680309
theorem B4302359 : Blo 1911435 4302359 := bstep (se 1 (by rfl) ⟨3226769, by rfl⟩ : syracuseStep 4302359 = 6453539) B6453539
theorem B2868239 : Blo 1911435 2868239 := bstep (se 1 (by rfl) ⟨2151179, by rfl⟩ : syracuseStep 2868239 = 4302359) B4302359
theorem B1912159 : Blo 1911435 1912159 := bstep (se 1 (by rfl) ⟨1434119, by rfl⟩ : syracuseStep 1912159 = 2868239) B2868239
theorem B2868245 : Blo 1911435 2868245 := bbase (se 6 (by rfl) ⟨67224, by rfl⟩ : syracuseStep 2868245 = 134449) (by norm_num)
theorem B1912163 : Blo 1911435 1912163 := bstep (se 1 (by rfl) ⟨1434122, by rfl⟩ : syracuseStep 1912163 = 2868245) B2868245
theorem B4657069 : Blo 1911435 4657069 := bbase (se 3 (by rfl) ⟨873200, by rfl⟩ : syracuseStep 4657069 = 1746401) (by norm_num)
theorem B6209425 : Blo 1911435 6209425 := bstep (se 2 (by rfl) ⟨2328534, by rfl⟩ : syracuseStep 6209425 = 4657069) B4657069
theorem B33116933 : Blo 1911435 33116933 := bstep (se 4 (by rfl) ⟨3104712, by rfl⟩ : syracuseStep 33116933 = 6209425) B6209425
theorem B22077955 : Blo 1911435 22077955 := bstep (se 1 (by rfl) ⟨16558466, by rfl⟩ : syracuseStep 22077955 = 33116933) B33116933
theorem B29437273 : Blo 1911435 29437273 := bstep (se 2 (by rfl) ⟨11038977, by rfl⟩ : syracuseStep 29437273 = 22077955) B22077955
theorem B39249697 : Blo 1911435 39249697 := bstep (se 2 (by rfl) ⟨14718636, by rfl⟩ : syracuseStep 39249697 = 29437273) B29437273
theorem B52332929 : Blo 1911435 52332929 := bstep (se 2 (by rfl) ⟨19624848, by rfl⟩ : syracuseStep 52332929 = 39249697) B39249697
theorem B34888619 : Blo 1911435 34888619 := bstep (se 1 (by rfl) ⟨26166464, by rfl⟩ : syracuseStep 34888619 = 52332929) B52332929
theorem B23259079 : Blo 1911435 23259079 := bstep (se 1 (by rfl) ⟨17444309, by rfl⟩ : syracuseStep 23259079 = 34888619) B34888619
theorem B31012105 : Blo 1911435 31012105 := bstep (se 2 (by rfl) ⟨11629539, by rfl⟩ : syracuseStep 31012105 = 23259079) B23259079
theorem B41349473 : Blo 1911435 41349473 := bstep (se 2 (by rfl) ⟨15506052, by rfl⟩ : syracuseStep 41349473 = 31012105) B31012105
theorem B27566315 : Blo 1911435 27566315 := bstep (se 1 (by rfl) ⟨20674736, by rfl⟩ : syracuseStep 27566315 = 41349473) B41349473
theorem B18377543 : Blo 1911435 18377543 := bstep (se 1 (by rfl) ⟨13783157, by rfl⟩ : syracuseStep 18377543 = 27566315) B27566315
theorem B12251695 : Blo 1911435 12251695 := bstep (se 1 (by rfl) ⟨9188771, by rfl⟩ : syracuseStep 12251695 = 18377543) B18377543
theorem B16335593 : Blo 1911435 16335593 := bstep (se 2 (by rfl) ⟨6125847, by rfl⟩ : syracuseStep 16335593 = 12251695) B12251695
theorem B10890395 : Blo 1911435 10890395 := bstep (se 1 (by rfl) ⟨8167796, by rfl⟩ : syracuseStep 10890395 = 16335593) B16335593
theorem B7260263 : Blo 1911435 7260263 := bstep (se 1 (by rfl) ⟨5445197, by rfl⟩ : syracuseStep 7260263 = 10890395) B10890395
theorem B4840175 : Blo 1911435 4840175 := bstep (se 1 (by rfl) ⟨3630131, by rfl⟩ : syracuseStep 4840175 = 7260263) B7260263
theorem B3226783 : Blo 1911435 3226783 := bstep (se 1 (by rfl) ⟨2420087, by rfl⟩ : syracuseStep 3226783 = 4840175) B4840175
theorem B4302377 : Blo 1911435 4302377 := bstep (se 2 (by rfl) ⟨1613391, by rfl⟩ : syracuseStep 4302377 = 3226783) B3226783
theorem B2868251 : Blo 1911435 2868251 := bstep (se 1 (by rfl) ⟨2151188, by rfl⟩ : syracuseStep 2868251 = 4302377) B4302377
theorem B1912167 : Blo 1911435 1912167 := bstep (se 1 (by rfl) ⟨1434125, by rfl⟩ : syracuseStep 1912167 = 2868251) B2868251
theorem B2151193 : Blo 1911435 2151193 := bbase (se 2 (by rfl) ⟨806697, by rfl⟩ : syracuseStep 2151193 = 1613395) (by norm_num)
theorem B2868257 : Blo 1911435 2868257 := bstep (se 2 (by rfl) ⟨1075596, by rfl⟩ : syracuseStep 2868257 = 2151193) B2151193
theorem B1912171 : Blo 1911435 1912171 := bstep (se 1 (by rfl) ⟨1434128, by rfl⟩ : syracuseStep 1912171 = 2868257) B2868257
theorem B7260293 : Blo 1911435 7260293 := bbase (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) (by norm_num)
theorem B4840195 : Blo 1911435 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B6453593 : Blo 1911435 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B4302395 : Blo 1911435 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B2868263 : Blo 1911435 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B1912175 : Blo 1911435 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B2868269 : Blo 1911435 2868269 := bbase (se 3 (by rfl) ⟨537800, by rfl⟩ : syracuseStep 2868269 = 1075601) (by norm_num)
theorem B1912179 : Blo 1911435 1912179 := bstep (se 1 (by rfl) ⟨1434134, by rfl⟩ : syracuseStep 1912179 = 2868269) B2868269
theorem B4302413 : Blo 1911435 4302413 := bbase (se 3 (by rfl) ⟨806702, by rfl⟩ : syracuseStep 4302413 = 1613405) (by norm_num)
theorem B2868275 : Blo 1911435 2868275 := bstep (se 1 (by rfl) ⟨2151206, by rfl⟩ : syracuseStep 2868275 = 4302413) B4302413
theorem B1912183 : Blo 1911435 1912183 := bstep (se 1 (by rfl) ⟨1434137, by rfl⟩ : syracuseStep 1912183 = 2868275) B2868275
theorem B2420113 : Blo 1911435 2420113 := bbase (se 2 (by rfl) ⟨907542, by rfl⟩ : syracuseStep 2420113 = 1815085) (by norm_num)
theorem B3226817 : Blo 1911435 3226817 := bstep (se 2 (by rfl) ⟨1210056, by rfl⟩ : syracuseStep 3226817 = 2420113) B2420113
theorem B2151211 : Blo 1911435 2151211 := bstep (se 1 (by rfl) ⟨1613408, by rfl⟩ : syracuseStep 2151211 = 3226817) B3226817
theorem B2868281 : Blo 1911435 2868281 := bstep (se 2 (by rfl) ⟨1075605, by rfl⟩ : syracuseStep 2868281 = 2151211) B2151211
theorem B1912187 : Blo 1911435 1912187 := bstep (se 1 (by rfl) ⟨1434140, by rfl⟩ : syracuseStep 1912187 = 2868281) B2868281
theorem B4083949 : Blo 1911435 4083949 := bbase (se 3 (by rfl) ⟨765740, by rfl⟩ : syracuseStep 4083949 = 1531481) (by norm_num)
theorem B21781061 : Blo 1911435 21781061 := bstep (se 4 (by rfl) ⟨2041974, by rfl⟩ : syracuseStep 21781061 = 4083949) B4083949
theorem B14520707 : Blo 1911435 14520707 := bstep (se 1 (by rfl) ⟨10890530, by rfl⟩ : syracuseStep 14520707 = 21781061) B21781061
theorem B9680471 : Blo 1911435 9680471 := bstep (se 1 (by rfl) ⟨7260353, by rfl⟩ : syracuseStep 9680471 = 14520707) B14520707
theorem B6453647 : Blo 1911435 6453647 := bstep (se 1 (by rfl) ⟨4840235, by rfl⟩ : syracuseStep 6453647 = 9680471) B9680471
theorem B4302431 : Blo 1911435 4302431 := bstep (se 1 (by rfl) ⟨3226823, by rfl⟩ : syracuseStep 4302431 = 6453647) B6453647
theorem B2868287 : Blo 1911435 2868287 := bstep (se 1 (by rfl) ⟨2151215, by rfl⟩ : syracuseStep 2868287 = 4302431) B4302431
theorem B1912191 : Blo 1911435 1912191 := bstep (se 1 (by rfl) ⟨1434143, by rfl⟩ : syracuseStep 1912191 = 2868287) B2868287
theorem B2868293 : Blo 1911435 2868293 := bbase (se 4 (by rfl) ⟨268902, by rfl⟩ : syracuseStep 2868293 = 537805) (by norm_num)
theorem B1912195 : Blo 1911435 1912195 := bstep (se 1 (by rfl) ⟨1434146, by rfl⟩ : syracuseStep 1912195 = 2868293) B2868293
theorem B3226837 : Blo 1911435 3226837 := bbase (se 7 (by rfl) ⟨37814, by rfl⟩ : syracuseStep 3226837 = 75629) (by norm_num)
theorem B4302449 : Blo 1911435 4302449 := bstep (se 2 (by rfl) ⟨1613418, by rfl⟩ : syracuseStep 4302449 = 3226837) B3226837
theorem B2868299 : Blo 1911435 2868299 := bstep (se 1 (by rfl) ⟨2151224, by rfl⟩ : syracuseStep 2868299 = 4302449) B4302449
theorem B1912199 : Blo 1911435 1912199 := bstep (se 1 (by rfl) ⟨1434149, by rfl⟩ : syracuseStep 1912199 = 2868299) B2868299
theorem B2151229 : Blo 1911435 2151229 := bbase (se 3 (by rfl) ⟨403355, by rfl⟩ : syracuseStep 2151229 = 806711) (by norm_num)
theorem B2868305 : Blo 1911435 2868305 := bstep (se 2 (by rfl) ⟨1075614, by rfl⟩ : syracuseStep 2868305 = 2151229) B2151229
theorem B1912203 : Blo 1911435 1912203 := bstep (se 1 (by rfl) ⟨1434152, by rfl⟩ : syracuseStep 1912203 = 2868305) B2868305
theorem B6453701 : Blo 1911435 6453701 := bbase (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) (by norm_num)
theorem B4302467 : Blo 1911435 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B2868311 : Blo 1911435 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B1912207 : Blo 1911435 1912207 := bstep (se 1 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 1912207 = 2868311) B2868311
theorem B2868317 : Blo 1911435 2868317 := bbase (se 3 (by rfl) ⟨537809, by rfl⟩ : syracuseStep 2868317 = 1075619) (by norm_num)
theorem B1912211 : Blo 1911435 1912211 := bstep (se 1 (by rfl) ⟨1434158, by rfl⟩ : syracuseStep 1912211 = 2868317) B2868317
theorem B4302485 : Blo 1911435 4302485 := bbase (se 6 (by rfl) ⟨100839, by rfl⟩ : syracuseStep 4302485 = 201679) (by norm_num)
theorem B2868323 : Blo 1911435 2868323 := bstep (se 1 (by rfl) ⟨2151242, by rfl⟩ : syracuseStep 2868323 = 4302485) B4302485
theorem B1912215 : Blo 1911435 1912215 := bstep (se 1 (by rfl) ⟨1434161, by rfl⟩ : syracuseStep 1912215 = 2868323) B2868323
theorem B2042005 : Blo 1911435 2042005 := bbase (se 6 (by rfl) ⟨47859, by rfl⟩ : syracuseStep 2042005 = 95719) (by norm_num)
theorem B2722673 : Blo 1911435 2722673 := bstep (se 2 (by rfl) ⟨1021002, by rfl⟩ : syracuseStep 2722673 = 2042005) B2042005
theorem B7260461 : Blo 1911435 7260461 := bstep (se 3 (by rfl) ⟨1361336, by rfl⟩ : syracuseStep 7260461 = 2722673) B2722673
theorem B4840307 : Blo 1911435 4840307 := bstep (se 1 (by rfl) ⟨3630230, by rfl⟩ : syracuseStep 4840307 = 7260461) B7260461
theorem B3226871 : Blo 1911435 3226871 := bstep (se 1 (by rfl) ⟨2420153, by rfl⟩ : syracuseStep 3226871 = 4840307) B4840307
theorem B2151247 : Blo 1911435 2151247 := bstep (se 1 (by rfl) ⟨1613435, by rfl⟩ : syracuseStep 2151247 = 3226871) B3226871
theorem B2868329 : Blo 1911435 2868329 := bstep (se 2 (by rfl) ⟨1075623, by rfl⟩ : syracuseStep 2868329 = 2151247) B2151247
theorem B1912219 : Blo 1911435 1912219 := bstep (se 1 (by rfl) ⟨1434164, by rfl⟩ : syracuseStep 1912219 = 2868329) B2868329
theorem B12252053 : Blo 1911435 12252053 := bbase (se 6 (by rfl) ⟨287157, by rfl⟩ : syracuseStep 12252053 = 574315) (by norm_num)
theorem B8168035 : Blo 1911435 8168035 := bstep (se 1 (by rfl) ⟨6126026, by rfl⟩ : syracuseStep 8168035 = 12252053) B12252053
theorem B10890713 : Blo 1911435 10890713 := bstep (se 2 (by rfl) ⟨4084017, by rfl⟩ : syracuseStep 10890713 = 8168035) B8168035
theorem B7260475 : Blo 1911435 7260475 := bstep (se 1 (by rfl) ⟨5445356, by rfl⟩ : syracuseStep 7260475 = 10890713) B10890713
theorem B9680633 : Blo 1911435 9680633 := bstep (se 2 (by rfl) ⟨3630237, by rfl⟩ : syracuseStep 9680633 = 7260475) B7260475
theorem B6453755 : Blo 1911435 6453755 := bstep (se 1 (by rfl) ⟨4840316, by rfl⟩ : syracuseStep 6453755 = 9680633) B9680633
theorem B4302503 : Blo 1911435 4302503 := bstep (se 1 (by rfl) ⟨3226877, by rfl⟩ : syracuseStep 4302503 = 6453755) B6453755
theorem B2868335 : Blo 1911435 2868335 := bstep (se 1 (by rfl) ⟨2151251, by rfl⟩ : syracuseStep 2868335 = 4302503) B4302503
theorem B1912223 : Blo 1911435 1912223 := bstep (se 1 (by rfl) ⟨1434167, by rfl⟩ : syracuseStep 1912223 = 2868335) B2868335
theorem B2868341 : Blo 1911435 2868341 := bbase (se 5 (by rfl) ⟨134453, by rfl⟩ : syracuseStep 2868341 = 268907) (by norm_num)
theorem B1912227 : Blo 1911435 1912227 := bstep (se 1 (by rfl) ⟨1434170, by rfl⟩ : syracuseStep 1912227 = 2868341) B2868341
theorem B3630253 : Blo 1911435 3630253 := bbase (se 3 (by rfl) ⟨680672, by rfl⟩ : syracuseStep 3630253 = 1361345) (by norm_num)
theorem B4840337 : Blo 1911435 4840337 := bstep (se 2 (by rfl) ⟨1815126, by rfl⟩ : syracuseStep 4840337 = 3630253) B3630253
theorem B3226891 : Blo 1911435 3226891 := bstep (se 1 (by rfl) ⟨2420168, by rfl⟩ : syracuseStep 3226891 = 4840337) B4840337
theorem B4302521 : Blo 1911435 4302521 := bstep (se 2 (by rfl) ⟨1613445, by rfl⟩ : syracuseStep 4302521 = 3226891) B3226891
theorem B2868347 : Blo 1911435 2868347 := bstep (se 1 (by rfl) ⟨2151260, by rfl⟩ : syracuseStep 2868347 = 4302521) B4302521
theorem B1912231 : Blo 1911435 1912231 := bstep (se 1 (by rfl) ⟨1434173, by rfl⟩ : syracuseStep 1912231 = 2868347) B2868347
theorem B2151265 : Blo 1911435 2151265 := bbase (se 2 (by rfl) ⟨806724, by rfl⟩ : syracuseStep 2151265 = 1613449) (by norm_num)
theorem B2868353 : Blo 1911435 2868353 := bstep (se 2 (by rfl) ⟨1075632, by rfl⟩ : syracuseStep 2868353 = 2151265) B2151265
theorem B1912235 : Blo 1911435 1912235 := bstep (se 1 (by rfl) ⟨1434176, by rfl⟩ : syracuseStep 1912235 = 2868353) B2868353
theorem B4840357 : Blo 1911435 4840357 := bbase (se 4 (by rfl) ⟨453783, by rfl⟩ : syracuseStep 4840357 = 907567) (by norm_num)
theorem B6453809 : Blo 1911435 6453809 := bstep (se 2 (by rfl) ⟨2420178, by rfl⟩ : syracuseStep 6453809 = 4840357) B4840357
theorem B4302539 : Blo 1911435 4302539 := bstep (se 1 (by rfl) ⟨3226904, by rfl⟩ : syracuseStep 4302539 = 6453809) B6453809
theorem B2868359 : Blo 1911435 2868359 := bstep (se 1 (by rfl) ⟨2151269, by rfl⟩ : syracuseStep 2868359 = 4302539) B4302539
theorem B1912239 : Blo 1911435 1912239 := bstep (se 1 (by rfl) ⟨1434179, by rfl⟩ : syracuseStep 1912239 = 2868359) B2868359
theorem B2868365 : Blo 1911435 2868365 := bbase (se 3 (by rfl) ⟨537818, by rfl⟩ : syracuseStep 2868365 = 1075637) (by norm_num)
theorem B1912243 : Blo 1911435 1912243 := bstep (se 1 (by rfl) ⟨1434182, by rfl⟩ : syracuseStep 1912243 = 2868365) B2868365
theorem B4302557 : Blo 1911435 4302557 := bbase (se 3 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 4302557 = 1613459) (by norm_num)
theorem B2868371 : Blo 1911435 2868371 := bstep (se 1 (by rfl) ⟨2151278, by rfl⟩ : syracuseStep 2868371 = 4302557) B4302557
theorem B1912247 : Blo 1911435 1912247 := bstep (se 1 (by rfl) ⟨1434185, by rfl⟩ : syracuseStep 1912247 = 2868371) B2868371
theorem B3226925 : Blo 1911435 3226925 := bbase (se 3 (by rfl) ⟨605048, by rfl⟩ : syracuseStep 3226925 = 1210097) (by norm_num)
theorem B2151283 : Blo 1911435 2151283 := bstep (se 1 (by rfl) ⟨1613462, by rfl⟩ : syracuseStep 2151283 = 3226925) B3226925
theorem B2868377 : Blo 1911435 2868377 := bstep (se 2 (by rfl) ⟨1075641, by rfl⟩ : syracuseStep 2868377 = 2151283) B2151283
theorem B1912251 : Blo 1911435 1912251 := bstep (se 1 (by rfl) ⟨1434188, by rfl⟩ : syracuseStep 1912251 = 2868377) B2868377
theorem B4657285 : Blo 1911435 4657285 := bbase (se 4 (by rfl) ⟨436620, by rfl⟩ : syracuseStep 4657285 = 873241) (by norm_num)
theorem B6209713 : Blo 1911435 6209713 := bstep (se 2 (by rfl) ⟨2328642, by rfl⟩ : syracuseStep 6209713 = 4657285) B4657285
theorem B8279617 : Blo 1911435 8279617 := bstep (se 2 (by rfl) ⟨3104856, by rfl⟩ : syracuseStep 8279617 = 6209713) B6209713
theorem B11039489 : Blo 1911435 11039489 := bstep (se 2 (by rfl) ⟨4139808, by rfl⟩ : syracuseStep 11039489 = 8279617) B8279617
theorem B7359659 : Blo 1911435 7359659 := bstep (se 1 (by rfl) ⟨5519744, by rfl⟩ : syracuseStep 7359659 = 11039489) B11039489
theorem B4906439 : Blo 1911435 4906439 := bstep (se 1 (by rfl) ⟨3679829, by rfl⟩ : syracuseStep 4906439 = 7359659) B7359659
theorem B3270959 : Blo 1911435 3270959 := bstep (se 1 (by rfl) ⟨2453219, by rfl⟩ : syracuseStep 3270959 = 4906439) B4906439
theorem B2180639 : Blo 1911435 2180639 := bstep (se 1 (by rfl) ⟨1635479, by rfl⟩ : syracuseStep 2180639 = 3270959) B3270959
theorem B5815037 : Blo 1911435 5815037 := bstep (se 3 (by rfl) ⟨1090319, by rfl⟩ : syracuseStep 5815037 = 2180639) B2180639
theorem B15506765 : Blo 1911435 15506765 := bstep (se 3 (by rfl) ⟨2907518, by rfl⟩ : syracuseStep 15506765 = 5815037) B5815037
theorem B10337843 : Blo 1911435 10337843 := bstep (se 1 (by rfl) ⟨7753382, by rfl⟩ : syracuseStep 10337843 = 15506765) B15506765
theorem B6891895 : Blo 1911435 6891895 := bstep (se 1 (by rfl) ⟨5168921, by rfl⟩ : syracuseStep 6891895 = 10337843) B10337843
theorem B36756773 : Blo 1911435 36756773 := bstep (se 4 (by rfl) ⟨3445947, by rfl⟩ : syracuseStep 36756773 = 6891895) B6891895
theorem B24504515 : Blo 1911435 24504515 := bstep (se 1 (by rfl) ⟨18378386, by rfl⟩ : syracuseStep 24504515 = 36756773) B36756773
theorem B16336343 : Blo 1911435 16336343 := bstep (se 1 (by rfl) ⟨12252257, by rfl⟩ : syracuseStep 16336343 = 24504515) B24504515
theorem B10890895 : Blo 1911435 10890895 := bstep (se 1 (by rfl) ⟨8168171, by rfl⟩ : syracuseStep 10890895 = 16336343) B16336343
theorem B14521193 : Blo 1911435 14521193 := bstep (se 2 (by rfl) ⟨5445447, by rfl⟩ : syracuseStep 14521193 = 10890895) B10890895
theorem B9680795 : Blo 1911435 9680795 := bstep (se 1 (by rfl) ⟨7260596, by rfl⟩ : syracuseStep 9680795 = 14521193) B14521193
theorem B6453863 : Blo 1911435 6453863 := bstep (se 1 (by rfl) ⟨4840397, by rfl⟩ : syracuseStep 6453863 = 9680795) B9680795
theorem B4302575 : Blo 1911435 4302575 := bstep (se 1 (by rfl) ⟨3226931, by rfl⟩ : syracuseStep 4302575 = 6453863) B6453863
theorem B2868383 : Blo 1911435 2868383 := bstep (se 1 (by rfl) ⟨2151287, by rfl⟩ : syracuseStep 2868383 = 4302575) B4302575
theorem B1912255 : Blo 1911435 1912255 := bstep (se 1 (by rfl) ⟨1434191, by rfl⟩ : syracuseStep 1912255 = 2868383) B2868383
theorem B2868389 : Blo 1911435 2868389 := bbase (se 4 (by rfl) ⟨268911, by rfl⟩ : syracuseStep 2868389 = 537823) (by norm_num)
theorem B1912259 : Blo 1911435 1912259 := bstep (se 1 (by rfl) ⟨1434194, by rfl⟩ : syracuseStep 1912259 = 2868389) B2868389
theorem B2420209 : Blo 1911435 2420209 := bbase (se 2 (by rfl) ⟨907578, by rfl⟩ : syracuseStep 2420209 = 1815157) (by norm_num)
theorem B3226945 : Blo 1911435 3226945 := bstep (se 2 (by rfl) ⟨1210104, by rfl⟩ : syracuseStep 3226945 = 2420209) B2420209
theorem B4302593 : Blo 1911435 4302593 := bstep (se 2 (by rfl) ⟨1613472, by rfl⟩ : syracuseStep 4302593 = 3226945) B3226945
theorem B2868395 : Blo 1911435 2868395 := bstep (se 1 (by rfl) ⟨2151296, by rfl⟩ : syracuseStep 2868395 = 4302593) B4302593
theorem B1912263 : Blo 1911435 1912263 := bstep (se 1 (by rfl) ⟨1434197, by rfl⟩ : syracuseStep 1912263 = 2868395) B2868395
theorem B2151301 : Blo 1911435 2151301 := bbase (se 4 (by rfl) ⟨201684, by rfl⟩ : syracuseStep 2151301 = 403369) (by norm_num)
theorem B2868401 : Blo 1911435 2868401 := bstep (se 2 (by rfl) ⟨1075650, by rfl⟩ : syracuseStep 2868401 = 2151301) B2151301
theorem B1912267 : Blo 1911435 1912267 := bstep (se 1 (by rfl) ⟨1434200, by rfl⟩ : syracuseStep 1912267 = 2868401) B2868401
theorem B4594637 : Blo 1911435 4594637 := bbase (se 3 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 4594637 = 1722989) (by norm_num)
theorem B3063091 : Blo 1911435 3063091 := bstep (se 1 (by rfl) ⟨2297318, by rfl⟩ : syracuseStep 3063091 = 4594637) B4594637
theorem B4084121 : Blo 1911435 4084121 := bstep (se 2 (by rfl) ⟨1531545, by rfl⟩ : syracuseStep 4084121 = 3063091) B3063091
theorem B2722747 : Blo 1911435 2722747 := bstep (se 1 (by rfl) ⟨2042060, by rfl⟩ : syracuseStep 2722747 = 4084121) B4084121
theorem B3630329 : Blo 1911435 3630329 := bstep (se 2 (by rfl) ⟨1361373, by rfl⟩ : syracuseStep 3630329 = 2722747) B2722747
theorem B2420219 : Blo 1911435 2420219 := bstep (se 1 (by rfl) ⟨1815164, by rfl⟩ : syracuseStep 2420219 = 3630329) B3630329
theorem B6453917 : Blo 1911435 6453917 := bstep (se 3 (by rfl) ⟨1210109, by rfl⟩ : syracuseStep 6453917 = 2420219) B2420219
theorem B4302611 : Blo 1911435 4302611 := bstep (se 1 (by rfl) ⟨3226958, by rfl⟩ : syracuseStep 4302611 = 6453917) B6453917
theorem B2868407 : Blo 1911435 2868407 := bstep (se 1 (by rfl) ⟨2151305, by rfl⟩ : syracuseStep 2868407 = 4302611) B4302611
theorem B1912271 : Blo 1911435 1912271 := bstep (se 1 (by rfl) ⟨1434203, by rfl⟩ : syracuseStep 1912271 = 2868407) B2868407
theorem B2868413 : Blo 1911435 2868413 := bbase (se 3 (by rfl) ⟨537827, by rfl⟩ : syracuseStep 2868413 = 1075655) (by norm_num)
theorem B1912275 : Blo 1911435 1912275 := bstep (se 1 (by rfl) ⟨1434206, by rfl⟩ : syracuseStep 1912275 = 2868413) B2868413
theorem B4302629 : Blo 1911435 4302629 := bbase (se 4 (by rfl) ⟨403371, by rfl⟩ : syracuseStep 4302629 = 806743) (by norm_num)
theorem B2868419 : Blo 1911435 2868419 := bstep (se 1 (by rfl) ⟨2151314, by rfl⟩ : syracuseStep 2868419 = 4302629) B4302629
theorem B1912279 : Blo 1911435 1912279 := bstep (se 1 (by rfl) ⟨1434209, by rfl⟩ : syracuseStep 1912279 = 2868419) B2868419
theorem B4840469 : Blo 1911435 4840469 := bbase (se 6 (by rfl) ⟨113448, by rfl⟩ : syracuseStep 4840469 = 226897) (by norm_num)
theorem B3226979 : Blo 1911435 3226979 := bstep (se 1 (by rfl) ⟨2420234, by rfl⟩ : syracuseStep 3226979 = 4840469) B4840469
theorem B2151319 : Blo 1911435 2151319 := bstep (se 1 (by rfl) ⟨1613489, by rfl⟩ : syracuseStep 2151319 = 3226979) B3226979
theorem B2868425 : Blo 1911435 2868425 := bstep (se 2 (by rfl) ⟨1075659, by rfl⟩ : syracuseStep 2868425 = 2151319) B2151319
theorem B1912283 : Blo 1911435 1912283 := bstep (se 1 (by rfl) ⟨1434212, by rfl⟩ : syracuseStep 1912283 = 2868425) B2868425
theorem B8168309 : Blo 1911435 8168309 := bbase (se 5 (by rfl) ⟨382889, by rfl⟩ : syracuseStep 8168309 = 765779) (by norm_num)
theorem B5445539 : Blo 1911435 5445539 := bstep (se 1 (by rfl) ⟨4084154, by rfl⟩ : syracuseStep 5445539 = 8168309) B8168309
theorem B3630359 : Blo 1911435 3630359 := bstep (se 1 (by rfl) ⟨2722769, by rfl⟩ : syracuseStep 3630359 = 5445539) B5445539
theorem B9680957 : Blo 1911435 9680957 := bstep (se 3 (by rfl) ⟨1815179, by rfl⟩ : syracuseStep 9680957 = 3630359) B3630359
theorem B6453971 : Blo 1911435 6453971 := bstep (se 1 (by rfl) ⟨4840478, by rfl⟩ : syracuseStep 6453971 = 9680957) B9680957
theorem B4302647 : Blo 1911435 4302647 := bstep (se 1 (by rfl) ⟨3226985, by rfl⟩ : syracuseStep 4302647 = 6453971) B6453971
theorem B2868431 : Blo 1911435 2868431 := bstep (se 1 (by rfl) ⟨2151323, by rfl⟩ : syracuseStep 2868431 = 4302647) B4302647
theorem B1912287 : Blo 1911435 1912287 := bstep (se 1 (by rfl) ⟨1434215, by rfl⟩ : syracuseStep 1912287 = 2868431) B2868431
theorem B2868437 : Blo 1911435 2868437 := bbase (se 7 (by rfl) ⟨33614, by rfl⟩ : syracuseStep 2868437 = 67229) (by norm_num)
theorem B1912291 : Blo 1911435 1912291 := bstep (se 1 (by rfl) ⟨1434218, by rfl⟩ : syracuseStep 1912291 = 2868437) B2868437
theorem B2722781 : Blo 1911435 2722781 := bbase (se 3 (by rfl) ⟨510521, by rfl⟩ : syracuseStep 2722781 = 1021043) (by norm_num)
theorem B7260749 : Blo 1911435 7260749 := bstep (se 3 (by rfl) ⟨1361390, by rfl⟩ : syracuseStep 7260749 = 2722781) B2722781
theorem B4840499 : Blo 1911435 4840499 := bstep (se 1 (by rfl) ⟨3630374, by rfl⟩ : syracuseStep 4840499 = 7260749) B7260749
theorem B3226999 : Blo 1911435 3226999 := bstep (se 1 (by rfl) ⟨2420249, by rfl⟩ : syracuseStep 3226999 = 4840499) B4840499
theorem B4302665 : Blo 1911435 4302665 := bstep (se 2 (by rfl) ⟨1613499, by rfl⟩ : syracuseStep 4302665 = 3226999) B3226999
theorem B2868443 : Blo 1911435 2868443 := bstep (se 1 (by rfl) ⟨2151332, by rfl⟩ : syracuseStep 2868443 = 4302665) B4302665
theorem B1912295 : Blo 1911435 1912295 := bstep (se 1 (by rfl) ⟨1434221, by rfl⟩ : syracuseStep 1912295 = 2868443) B2868443
theorem B2151337 : Blo 1911435 2151337 := bbase (se 2 (by rfl) ⟨806751, by rfl⟩ : syracuseStep 2151337 = 1613503) (by norm_num)
theorem B2868449 : Blo 1911435 2868449 := bstep (se 2 (by rfl) ⟨1075668, by rfl⟩ : syracuseStep 2868449 = 2151337) B2151337
theorem B1912299 : Blo 1911435 1912299 := bstep (se 1 (by rfl) ⟨1434224, by rfl⟩ : syracuseStep 1912299 = 2868449) B2868449
theorem B6892069 : Blo 1911435 6892069 := bbase (se 4 (by rfl) ⟨646131, by rfl⟩ : syracuseStep 6892069 = 1292263) (by norm_num)
theorem B9189425 : Blo 1911435 9189425 := bstep (se 2 (by rfl) ⟨3446034, by rfl⟩ : syracuseStep 9189425 = 6892069) B6892069
theorem B6126283 : Blo 1911435 6126283 := bstep (se 1 (by rfl) ⟨4594712, by rfl⟩ : syracuseStep 6126283 = 9189425) B9189425
theorem B8168377 : Blo 1911435 8168377 := bstep (se 2 (by rfl) ⟨3063141, by rfl⟩ : syracuseStep 8168377 = 6126283) B6126283
theorem B10891169 : Blo 1911435 10891169 := bstep (se 2 (by rfl) ⟨4084188, by rfl⟩ : syracuseStep 10891169 = 8168377) B8168377
theorem B7260779 : Blo 1911435 7260779 := bstep (se 1 (by rfl) ⟨5445584, by rfl⟩ : syracuseStep 7260779 = 10891169) B10891169
theorem B4840519 : Blo 1911435 4840519 := bstep (se 1 (by rfl) ⟨3630389, by rfl⟩ : syracuseStep 4840519 = 7260779) B7260779
theorem B6454025 : Blo 1911435 6454025 := bstep (se 2 (by rfl) ⟨2420259, by rfl⟩ : syracuseStep 6454025 = 4840519) B4840519
theorem B4302683 : Blo 1911435 4302683 := bstep (se 1 (by rfl) ⟨3227012, by rfl⟩ : syracuseStep 4302683 = 6454025) B6454025
theorem B2868455 : Blo 1911435 2868455 := bstep (se 1 (by rfl) ⟨2151341, by rfl⟩ : syracuseStep 2868455 = 4302683) B4302683
theorem B1912303 : Blo 1911435 1912303 := bstep (se 1 (by rfl) ⟨1434227, by rfl⟩ : syracuseStep 1912303 = 2868455) B2868455
theorem B2868461 : Blo 1911435 2868461 := bbase (se 3 (by rfl) ⟨537836, by rfl⟩ : syracuseStep 2868461 = 1075673) (by norm_num)
theorem B1912307 : Blo 1911435 1912307 := bstep (se 1 (by rfl) ⟨1434230, by rfl⟩ : syracuseStep 1912307 = 2868461) B2868461
theorem B4302701 : Blo 1911435 4302701 := bbase (se 3 (by rfl) ⟨806756, by rfl⟩ : syracuseStep 4302701 = 1613513) (by norm_num)
theorem B2868467 : Blo 1911435 2868467 := bstep (se 1 (by rfl) ⟨2151350, by rfl⟩ : syracuseStep 2868467 = 4302701) B4302701
theorem B1912311 : Blo 1911435 1912311 := bstep (se 1 (by rfl) ⟨1434233, by rfl⟩ : syracuseStep 1912311 = 2868467) B2868467
theorem B3630413 : Blo 1911435 3630413 := bbase (se 3 (by rfl) ⟨680702, by rfl⟩ : syracuseStep 3630413 = 1361405) (by norm_num)
theorem B2420275 : Blo 1911435 2420275 := bstep (se 1 (by rfl) ⟨1815206, by rfl⟩ : syracuseStep 2420275 = 3630413) B3630413
theorem B3227033 : Blo 1911435 3227033 := bstep (se 2 (by rfl) ⟨1210137, by rfl⟩ : syracuseStep 3227033 = 2420275) B2420275
theorem B2151355 : Blo 1911435 2151355 := bstep (se 1 (by rfl) ⟨1613516, by rfl⟩ : syracuseStep 2151355 = 3227033) B3227033
theorem B2868473 : Blo 1911435 2868473 := bstep (se 2 (by rfl) ⟨1075677, by rfl⟩ : syracuseStep 2868473 = 2151355) B2151355
theorem B1912315 : Blo 1911435 1912315 := bstep (se 1 (by rfl) ⟨1434236, by rfl⟩ : syracuseStep 1912315 = 2868473) B2868473
theorem B7859429 : Blo 1911435 7859429 := bbase (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) (by norm_num)
theorem B5239619 : Blo 1911435 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B3493079 : Blo 1911435 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B37259509 : Blo 1911435 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B49679345 : Blo 1911435 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B33119563 : Blo 1911435 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B44159417 : Blo 1911435 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B29439611 : Blo 1911435 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B19626407 : Blo 1911435 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B13084271 : Blo 1911435 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B8722847 : Blo 1911435 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B23260925 : Blo 1911435 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B15507283 : Blo 1911435 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B20676377 : Blo 1911435 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B13784251 : Blo 1911435 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B18379001 : Blo 1911435 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B49010669 : Blo 1911435 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B32673779 : Blo 1911435 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B21782519 : Blo 1911435 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B14521679 : Blo 1911435 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B9681119 : Blo 1911435 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B6454079 : Blo 1911435 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B4302719 : Blo 1911435 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B2868479 : Blo 1911435 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B1912319 : Blo 1911435 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B2868485 : Blo 1911435 2868485 := bbase (se 4 (by rfl) ⟨268920, by rfl⟩ : syracuseStep 2868485 = 537841) (by norm_num)
theorem B1912323 : Blo 1911435 1912323 := bstep (se 1 (by rfl) ⟨1434242, by rfl⟩ : syracuseStep 1912323 = 2868485) B2868485
theorem B3227053 : Blo 1911435 3227053 := bbase (se 3 (by rfl) ⟨605072, by rfl⟩ : syracuseStep 3227053 = 1210145) (by norm_num)
theorem B4302737 : Blo 1911435 4302737 := bstep (se 2 (by rfl) ⟨1613526, by rfl⟩ : syracuseStep 4302737 = 3227053) B3227053
theorem B2868491 : Blo 1911435 2868491 := bstep (se 1 (by rfl) ⟨2151368, by rfl⟩ : syracuseStep 2868491 = 4302737) B4302737
theorem B1912327 : Blo 1911435 1912327 := bstep (se 1 (by rfl) ⟨1434245, by rfl⟩ : syracuseStep 1912327 = 2868491) B2868491
theorem B2151373 : Blo 1911435 2151373 := bbase (se 3 (by rfl) ⟨403382, by rfl⟩ : syracuseStep 2151373 = 806765) (by norm_num)
theorem B2868497 : Blo 1911435 2868497 := bstep (se 2 (by rfl) ⟨1075686, by rfl⟩ : syracuseStep 2868497 = 2151373) B2151373
theorem B1912331 : Blo 1911435 1912331 := bstep (se 1 (by rfl) ⟨1434248, by rfl⟩ : syracuseStep 1912331 = 2868497) B2868497
theorem B6454133 : Blo 1911435 6454133 := bbase (se 5 (by rfl) ⟨302537, by rfl⟩ : syracuseStep 6454133 = 605075) (by norm_num)
theorem B4302755 : Blo 1911435 4302755 := bstep (se 1 (by rfl) ⟨3227066, by rfl⟩ : syracuseStep 4302755 = 6454133) B6454133
theorem B2868503 : Blo 1911435 2868503 := bstep (se 1 (by rfl) ⟨2151377, by rfl⟩ : syracuseStep 2868503 = 4302755) B4302755
theorem B1912335 : Blo 1911435 1912335 := bstep (se 1 (by rfl) ⟨1434251, by rfl⟩ : syracuseStep 1912335 = 2868503) B2868503
theorem B2868509 : Blo 1911435 2868509 := bbase (se 3 (by rfl) ⟨537845, by rfl⟩ : syracuseStep 2868509 = 1075691) (by norm_num)
theorem B1912339 : Blo 1911435 1912339 := bstep (se 1 (by rfl) ⟨1434254, by rfl⟩ : syracuseStep 1912339 = 2868509) B2868509
theorem B4302773 : Blo 1911435 4302773 := bbase (se 5 (by rfl) ⟨201692, by rfl⟩ : syracuseStep 4302773 = 403385) (by norm_num)
theorem B2868515 : Blo 1911435 2868515 := bstep (se 1 (by rfl) ⟨2151386, by rfl⟩ : syracuseStep 2868515 = 4302773) B4302773
theorem B1912343 : Blo 1911435 1912343 := bstep (se 1 (by rfl) ⟨1434257, by rfl⟩ : syracuseStep 1912343 = 2868515) B2868515
theorem B6892229 : Blo 1911435 6892229 := bbase (se 4 (by rfl) ⟨646146, by rfl⟩ : syracuseStep 6892229 = 1292293) (by norm_num)
theorem B4594819 : Blo 1911435 4594819 := bstep (se 1 (by rfl) ⟨3446114, by rfl⟩ : syracuseStep 4594819 = 6892229) B6892229
theorem B6126425 : Blo 1911435 6126425 := bstep (se 2 (by rfl) ⟨2297409, by rfl⟩ : syracuseStep 6126425 = 4594819) B4594819
theorem B4084283 : Blo 1911435 4084283 := bstep (se 1 (by rfl) ⟨3063212, by rfl⟩ : syracuseStep 4084283 = 6126425) B6126425
theorem B10891421 : Blo 1911435 10891421 := bstep (se 3 (by rfl) ⟨2042141, by rfl⟩ : syracuseStep 10891421 = 4084283) B4084283
theorem B7260947 : Blo 1911435 7260947 := bstep (se 1 (by rfl) ⟨5445710, by rfl⟩ : syracuseStep 7260947 = 10891421) B10891421
theorem B4840631 : Blo 1911435 4840631 := bstep (se 1 (by rfl) ⟨3630473, by rfl⟩ : syracuseStep 4840631 = 7260947) B7260947
theorem B3227087 : Blo 1911435 3227087 := bstep (se 1 (by rfl) ⟨2420315, by rfl⟩ : syracuseStep 3227087 = 4840631) B4840631
theorem B2151391 : Blo 1911435 2151391 := bstep (se 1 (by rfl) ⟨1613543, by rfl⟩ : syracuseStep 2151391 = 3227087) B3227087
theorem B2868521 : Blo 1911435 2868521 := bstep (se 2 (by rfl) ⟨1075695, by rfl⟩ : syracuseStep 2868521 = 2151391) B2151391
theorem B1912347 : Blo 1911435 1912347 := bstep (se 1 (by rfl) ⟨1434260, by rfl⟩ : syracuseStep 1912347 = 2868521) B2868521
theorem B6126437 : Blo 1911435 6126437 := bbase (se 4 (by rfl) ⟨574353, by rfl⟩ : syracuseStep 6126437 = 1148707) (by norm_num)
theorem B4084291 : Blo 1911435 4084291 := bstep (se 1 (by rfl) ⟨3063218, by rfl⟩ : syracuseStep 4084291 = 6126437) B6126437
theorem B5445721 : Blo 1911435 5445721 := bstep (se 2 (by rfl) ⟨2042145, by rfl⟩ : syracuseStep 5445721 = 4084291) B4084291
theorem B7260961 : Blo 1911435 7260961 := bstep (se 2 (by rfl) ⟨2722860, by rfl⟩ : syracuseStep 7260961 = 5445721) B5445721
theorem B9681281 : Blo 1911435 9681281 := bstep (se 2 (by rfl) ⟨3630480, by rfl⟩ : syracuseStep 9681281 = 7260961) B7260961
theorem B6454187 : Blo 1911435 6454187 := bstep (se 1 (by rfl) ⟨4840640, by rfl⟩ : syracuseStep 6454187 = 9681281) B9681281
theorem B4302791 : Blo 1911435 4302791 := bstep (se 1 (by rfl) ⟨3227093, by rfl⟩ : syracuseStep 4302791 = 6454187) B6454187
theorem B2868527 : Blo 1911435 2868527 := bstep (se 1 (by rfl) ⟨2151395, by rfl⟩ : syracuseStep 2868527 = 4302791) B4302791
theorem B1912351 : Blo 1911435 1912351 := bstep (se 1 (by rfl) ⟨1434263, by rfl⟩ : syracuseStep 1912351 = 2868527) B2868527
theorem B2868533 : Blo 1911435 2868533 := bbase (se 5 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 2868533 = 268925) (by norm_num)
theorem B1912355 : Blo 1911435 1912355 := bstep (se 1 (by rfl) ⟨1434266, by rfl⟩ : syracuseStep 1912355 = 2868533) B2868533
theorem B4840661 : Blo 1911435 4840661 := bbase (se 7 (by rfl) ⟨56726, by rfl⟩ : syracuseStep 4840661 = 113453) (by norm_num)
theorem B3227107 : Blo 1911435 3227107 := bstep (se 1 (by rfl) ⟨2420330, by rfl⟩ : syracuseStep 3227107 = 4840661) B4840661
theorem B4302809 : Blo 1911435 4302809 := bstep (se 2 (by rfl) ⟨1613553, by rfl⟩ : syracuseStep 4302809 = 3227107) B3227107
theorem B2868539 : Blo 1911435 2868539 := bstep (se 1 (by rfl) ⟨2151404, by rfl⟩ : syracuseStep 2868539 = 4302809) B4302809
theorem B1912359 : Blo 1911435 1912359 := bstep (se 1 (by rfl) ⟨1434269, by rfl⟩ : syracuseStep 1912359 = 2868539) B2868539
theorem B2151409 : Blo 1911435 2151409 := bbase (se 2 (by rfl) ⟨806778, by rfl⟩ : syracuseStep 2151409 = 1613557) (by norm_num)
theorem B2868545 : Blo 1911435 2868545 := bstep (se 2 (by rfl) ⟨1075704, by rfl⟩ : syracuseStep 2868545 = 2151409) B2151409
theorem B1912363 : Blo 1911435 1912363 := bstep (se 1 (by rfl) ⟨1434272, by rfl⟩ : syracuseStep 1912363 = 2868545) B2868545
theorem B9189733 : Blo 1911435 9189733 := bbase (se 4 (by rfl) ⟨861537, by rfl⟩ : syracuseStep 9189733 = 1723075) (by norm_num)
theorem B12252977 : Blo 1911435 12252977 := bstep (se 2 (by rfl) ⟨4594866, by rfl⟩ : syracuseStep 12252977 = 9189733) B9189733
theorem B8168651 : Blo 1911435 8168651 := bstep (se 1 (by rfl) ⟨6126488, by rfl⟩ : syracuseStep 8168651 = 12252977) B12252977
theorem B5445767 : Blo 1911435 5445767 := bstep (se 1 (by rfl) ⟨4084325, by rfl⟩ : syracuseStep 5445767 = 8168651) B8168651
theorem B3630511 : Blo 1911435 3630511 := bstep (se 1 (by rfl) ⟨2722883, by rfl⟩ : syracuseStep 3630511 = 5445767) B5445767
theorem B4840681 : Blo 1911435 4840681 := bstep (se 2 (by rfl) ⟨1815255, by rfl⟩ : syracuseStep 4840681 = 3630511) B3630511
theorem B6454241 : Blo 1911435 6454241 := bstep (se 2 (by rfl) ⟨2420340, by rfl⟩ : syracuseStep 6454241 = 4840681) B4840681
theorem B4302827 : Blo 1911435 4302827 := bstep (se 1 (by rfl) ⟨3227120, by rfl⟩ : syracuseStep 4302827 = 6454241) B6454241
theorem B2868551 : Blo 1911435 2868551 := bstep (se 1 (by rfl) ⟨2151413, by rfl⟩ : syracuseStep 2868551 = 4302827) B4302827
theorem B1912367 : Blo 1911435 1912367 := bstep (se 1 (by rfl) ⟨1434275, by rfl⟩ : syracuseStep 1912367 = 2868551) B2868551
theorem B2868557 : Blo 1911435 2868557 := bbase (se 3 (by rfl) ⟨537854, by rfl⟩ : syracuseStep 2868557 = 1075709) (by norm_num)
theorem B1912371 : Blo 1911435 1912371 := bstep (se 1 (by rfl) ⟨1434278, by rfl⟩ : syracuseStep 1912371 = 2868557) B2868557
theorem B4302845 : Blo 1911435 4302845 := bbase (se 3 (by rfl) ⟨806783, by rfl⟩ : syracuseStep 4302845 = 1613567) (by norm_num)
theorem B2868563 : Blo 1911435 2868563 := bstep (se 1 (by rfl) ⟨2151422, by rfl⟩ : syracuseStep 2868563 = 4302845) B4302845
theorem B1912375 : Blo 1911435 1912375 := bstep (se 1 (by rfl) ⟨1434281, by rfl⟩ : syracuseStep 1912375 = 2868563) B2868563
theorem B3227141 : Blo 1911435 3227141 := bbase (se 4 (by rfl) ⟨302544, by rfl⟩ : syracuseStep 3227141 = 605089) (by norm_num)
theorem B2151427 : Blo 1911435 2151427 := bstep (se 1 (by rfl) ⟨1613570, by rfl⟩ : syracuseStep 2151427 = 3227141) B3227141
theorem B2868569 : Blo 1911435 2868569 := bstep (se 2 (by rfl) ⟨1075713, by rfl⟩ : syracuseStep 2868569 = 2151427) B2151427
theorem B1912379 : Blo 1911435 1912379 := bstep (se 1 (by rfl) ⟨1434284, by rfl⟩ : syracuseStep 1912379 = 2868569) B2868569
theorem B14522165 : Blo 1911435 14522165 := bbase (se 5 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 14522165 = 1361453) (by norm_num)
theorem B9681443 : Blo 1911435 9681443 := bstep (se 1 (by rfl) ⟨7261082, by rfl⟩ : syracuseStep 9681443 = 14522165) B14522165
theorem B6454295 : Blo 1911435 6454295 := bstep (se 1 (by rfl) ⟨4840721, by rfl⟩ : syracuseStep 6454295 = 9681443) B9681443
theorem B4302863 : Blo 1911435 4302863 := bstep (se 1 (by rfl) ⟨3227147, by rfl⟩ : syracuseStep 4302863 = 6454295) B6454295
theorem B2868575 : Blo 1911435 2868575 := bstep (se 1 (by rfl) ⟨2151431, by rfl⟩ : syracuseStep 2868575 = 4302863) B4302863
theorem B1912383 : Blo 1911435 1912383 := bstep (se 1 (by rfl) ⟨1434287, by rfl⟩ : syracuseStep 1912383 = 2868575) B2868575
theorem B2868581 : Blo 1911435 2868581 := bbase (se 4 (by rfl) ⟨268929, by rfl⟩ : syracuseStep 2868581 = 537859) (by norm_num)
theorem B1912387 : Blo 1911435 1912387 := bstep (se 1 (by rfl) ⟨1434290, by rfl⟩ : syracuseStep 1912387 = 2868581) B2868581
theorem B3630557 : Blo 1911435 3630557 := bbase (se 3 (by rfl) ⟨680729, by rfl⟩ : syracuseStep 3630557 = 1361459) (by norm_num)
theorem B2420371 : Blo 1911435 2420371 := bstep (se 1 (by rfl) ⟨1815278, by rfl⟩ : syracuseStep 2420371 = 3630557) B3630557
theorem B3227161 : Blo 1911435 3227161 := bstep (se 2 (by rfl) ⟨1210185, by rfl⟩ : syracuseStep 3227161 = 2420371) B2420371
theorem B4302881 : Blo 1911435 4302881 := bstep (se 2 (by rfl) ⟨1613580, by rfl⟩ : syracuseStep 4302881 = 3227161) B3227161
theorem B2868587 : Blo 1911435 2868587 := bstep (se 1 (by rfl) ⟨2151440, by rfl⟩ : syracuseStep 2868587 = 4302881) B4302881
theorem B1912391 : Blo 1911435 1912391 := bstep (se 1 (by rfl) ⟨1434293, by rfl⟩ : syracuseStep 1912391 = 2868587) B2868587
theorem B2151445 : Blo 1911435 2151445 := bbase (se 6 (by rfl) ⟨50424, by rfl⟩ : syracuseStep 2151445 = 100849) (by norm_num)
theorem B2868593 : Blo 1911435 2868593 := bstep (se 2 (by rfl) ⟨1075722, by rfl⟩ : syracuseStep 2868593 = 2151445) B2151445
theorem B1912395 : Blo 1911435 1912395 := bstep (se 1 (by rfl) ⟨1434296, by rfl⟩ : syracuseStep 1912395 = 2868593) B2868593
theorem B2420381 : Blo 1911435 2420381 := bbase (se 3 (by rfl) ⟨453821, by rfl⟩ : syracuseStep 2420381 = 907643) (by norm_num)
theorem B6454349 : Blo 1911435 6454349 := bstep (se 3 (by rfl) ⟨1210190, by rfl⟩ : syracuseStep 6454349 = 2420381) B2420381
theorem B4302899 : Blo 1911435 4302899 := bstep (se 1 (by rfl) ⟨3227174, by rfl⟩ : syracuseStep 4302899 = 6454349) B6454349
theorem B2868599 : Blo 1911435 2868599 := bstep (se 1 (by rfl) ⟨2151449, by rfl⟩ : syracuseStep 2868599 = 4302899) B4302899
theorem B1912399 : Blo 1911435 1912399 := bstep (se 1 (by rfl) ⟨1434299, by rfl⟩ : syracuseStep 1912399 = 2868599) B2868599
theorem B2868605 : Blo 1911435 2868605 := bbase (se 3 (by rfl) ⟨537863, by rfl⟩ : syracuseStep 2868605 = 1075727) (by norm_num)
theorem B1912403 : Blo 1911435 1912403 := bstep (se 1 (by rfl) ⟨1434302, by rfl⟩ : syracuseStep 1912403 = 2868605) B2868605
theorem B4302917 : Blo 1911435 4302917 := bbase (se 4 (by rfl) ⟨403398, by rfl⟩ : syracuseStep 4302917 = 806797) (by norm_num)
theorem B2868611 : Blo 1911435 2868611 := bstep (se 1 (by rfl) ⟨2151458, by rfl⟩ : syracuseStep 2868611 = 4302917) B4302917
theorem B1912407 : Blo 1911435 1912407 := bstep (se 1 (by rfl) ⟨1434305, by rfl⟩ : syracuseStep 1912407 = 2868611) B2868611
theorem B5445893 : Blo 1911435 5445893 := bbase (se 4 (by rfl) ⟨510552, by rfl⟩ : syracuseStep 5445893 = 1021105) (by norm_num)
theorem B3630595 : Blo 1911435 3630595 := bstep (se 1 (by rfl) ⟨2722946, by rfl⟩ : syracuseStep 3630595 = 5445893) B5445893
theorem B4840793 : Blo 1911435 4840793 := bstep (se 2 (by rfl) ⟨1815297, by rfl⟩ : syracuseStep 4840793 = 3630595) B3630595
theorem B3227195 : Blo 1911435 3227195 := bstep (se 1 (by rfl) ⟨2420396, by rfl⟩ : syracuseStep 3227195 = 4840793) B4840793
theorem B2151463 : Blo 1911435 2151463 := bstep (se 1 (by rfl) ⟨1613597, by rfl⟩ : syracuseStep 2151463 = 3227195) B3227195
theorem B2868617 : Blo 1911435 2868617 := bstep (se 2 (by rfl) ⟨1075731, by rfl⟩ : syracuseStep 2868617 = 2151463) B2151463
theorem B1912411 : Blo 1911435 1912411 := bstep (se 1 (by rfl) ⟨1434308, by rfl⟩ : syracuseStep 1912411 = 2868617) B2868617
theorem B9681605 : Blo 1911435 9681605 := bbase (se 4 (by rfl) ⟨907650, by rfl⟩ : syracuseStep 9681605 = 1815301) (by norm_num)
theorem B6454403 : Blo 1911435 6454403 := bstep (se 1 (by rfl) ⟨4840802, by rfl⟩ : syracuseStep 6454403 = 9681605) B9681605
theorem B4302935 : Blo 1911435 4302935 := bstep (se 1 (by rfl) ⟨3227201, by rfl⟩ : syracuseStep 4302935 = 6454403) B6454403
theorem B2868623 : Blo 1911435 2868623 := bstep (se 1 (by rfl) ⟨2151467, by rfl⟩ : syracuseStep 2868623 = 4302935) B4302935
theorem B1912415 : Blo 1911435 1912415 := bstep (se 1 (by rfl) ⟨1434311, by rfl⟩ : syracuseStep 1912415 = 2868623) B2868623
theorem B2868629 : Blo 1911435 2868629 := bbase (se 6 (by rfl) ⟨67233, by rfl⟩ : syracuseStep 2868629 = 134467) (by norm_num)
theorem B1912419 : Blo 1911435 1912419 := bstep (se 1 (by rfl) ⟨1434314, by rfl⟩ : syracuseStep 1912419 = 2868629) B2868629
theorem B4084445 : Blo 1911435 4084445 := bbase (se 3 (by rfl) ⟨765833, by rfl⟩ : syracuseStep 4084445 = 1531667) (by norm_num)
theorem B10891853 : Blo 1911435 10891853 := bstep (se 3 (by rfl) ⟨2042222, by rfl⟩ : syracuseStep 10891853 = 4084445) B4084445
theorem B7261235 : Blo 1911435 7261235 := bstep (se 1 (by rfl) ⟨5445926, by rfl⟩ : syracuseStep 7261235 = 10891853) B10891853
theorem B4840823 : Blo 1911435 4840823 := bstep (se 1 (by rfl) ⟨3630617, by rfl⟩ : syracuseStep 4840823 = 7261235) B7261235
theorem B3227215 : Blo 1911435 3227215 := bstep (se 1 (by rfl) ⟨2420411, by rfl⟩ : syracuseStep 3227215 = 4840823) B4840823
theorem B4302953 : Blo 1911435 4302953 := bstep (se 2 (by rfl) ⟨1613607, by rfl⟩ : syracuseStep 4302953 = 3227215) B3227215
theorem B2868635 : Blo 1911435 2868635 := bstep (se 1 (by rfl) ⟨2151476, by rfl⟩ : syracuseStep 2868635 = 4302953) B4302953
theorem B1912423 : Blo 1911435 1912423 := bstep (se 1 (by rfl) ⟨1434317, by rfl⟩ : syracuseStep 1912423 = 2868635) B2868635
theorem B2151481 : Blo 1911435 2151481 := bbase (se 2 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 2151481 = 1613611) (by norm_num)
theorem B2868641 : Blo 1911435 2868641 := bstep (se 2 (by rfl) ⟨1075740, by rfl⟩ : syracuseStep 2868641 = 2151481) B2151481
theorem B1912427 : Blo 1911435 1912427 := bstep (se 1 (by rfl) ⟨1434320, by rfl⟩ : syracuseStep 1912427 = 2868641) B2868641
theorem B4595021 : Blo 1911435 4595021 := bbase (se 3 (by rfl) ⟨861566, by rfl⟩ : syracuseStep 4595021 = 1723133) (by norm_num)
theorem B3063347 : Blo 1911435 3063347 := bstep (se 1 (by rfl) ⟨2297510, by rfl⟩ : syracuseStep 3063347 = 4595021) B4595021
theorem B2042231 : Blo 1911435 2042231 := bstep (se 1 (by rfl) ⟨1531673, by rfl⟩ : syracuseStep 2042231 = 3063347) B3063347
theorem B5445949 : Blo 1911435 5445949 := bstep (se 3 (by rfl) ⟨1021115, by rfl⟩ : syracuseStep 5445949 = 2042231) B2042231
theorem B7261265 : Blo 1911435 7261265 := bstep (se 2 (by rfl) ⟨2722974, by rfl⟩ : syracuseStep 7261265 = 5445949) B5445949
theorem B4840843 : Blo 1911435 4840843 := bstep (se 1 (by rfl) ⟨3630632, by rfl⟩ : syracuseStep 4840843 = 7261265) B7261265
theorem B6454457 : Blo 1911435 6454457 := bstep (se 2 (by rfl) ⟨2420421, by rfl⟩ : syracuseStep 6454457 = 4840843) B4840843
theorem B4302971 : Blo 1911435 4302971 := bstep (se 1 (by rfl) ⟨3227228, by rfl⟩ : syracuseStep 4302971 = 6454457) B6454457
theorem B2868647 : Blo 1911435 2868647 := bstep (se 1 (by rfl) ⟨2151485, by rfl⟩ : syracuseStep 2868647 = 4302971) B4302971
theorem B1912431 : Blo 1911435 1912431 := bstep (se 1 (by rfl) ⟨1434323, by rfl⟩ : syracuseStep 1912431 = 2868647) B2868647
theorem B2868653 : Blo 1911435 2868653 := bbase (se 3 (by rfl) ⟨537872, by rfl⟩ : syracuseStep 2868653 = 1075745) (by norm_num)
theorem B1912435 : Blo 1911435 1912435 := bstep (se 1 (by rfl) ⟨1434326, by rfl⟩ : syracuseStep 1912435 = 2868653) B2868653
theorem B4302989 : Blo 1911435 4302989 := bbase (se 3 (by rfl) ⟨806810, by rfl⟩ : syracuseStep 4302989 = 1613621) (by norm_num)
theorem B2868659 : Blo 1911435 2868659 := bstep (se 1 (by rfl) ⟨2151494, by rfl⟩ : syracuseStep 2868659 = 4302989) B4302989
theorem B1912439 : Blo 1911435 1912439 := bstep (se 1 (by rfl) ⟨1434329, by rfl⟩ : syracuseStep 1912439 = 2868659) B2868659
theorem B2420437 : Blo 1911435 2420437 := bbase (se 7 (by rfl) ⟨28364, by rfl⟩ : syracuseStep 2420437 = 56729) (by norm_num)
theorem B3227249 : Blo 1911435 3227249 := bstep (se 2 (by rfl) ⟨1210218, by rfl⟩ : syracuseStep 3227249 = 2420437) B2420437
theorem B2151499 : Blo 1911435 2151499 := bstep (se 1 (by rfl) ⟨1613624, by rfl⟩ : syracuseStep 2151499 = 3227249) B3227249
theorem B2868665 : Blo 1911435 2868665 := bstep (se 2 (by rfl) ⟨1075749, by rfl⟩ : syracuseStep 2868665 = 2151499) B2151499
theorem B1912443 : Blo 1911435 1912443 := bstep (se 1 (by rfl) ⟨1434332, by rfl⟩ : syracuseStep 1912443 = 2868665) B2868665
theorem B2453465 : Blo 1911435 2453465 := bbase (se 2 (by rfl) ⟨920049, by rfl⟩ : syracuseStep 2453465 = 1840099) (by norm_num)
theorem B6542573 : Blo 1911435 6542573 := bstep (se 3 (by rfl) ⟨1226732, by rfl⟩ : syracuseStep 6542573 = 2453465) B2453465
theorem B17446861 : Blo 1911435 17446861 := bstep (se 3 (by rfl) ⟨3271286, by rfl⟩ : syracuseStep 17446861 = 6542573) B6542573
theorem B23262481 : Blo 1911435 23262481 := bstep (se 2 (by rfl) ⟨8723430, by rfl⟩ : syracuseStep 23262481 = 17446861) B17446861
theorem B124066565 : Blo 1911435 124066565 := bstep (se 4 (by rfl) ⟨11631240, by rfl⟩ : syracuseStep 124066565 = 23262481) B23262481
theorem B82711043 : Blo 1911435 82711043 := bstep (se 1 (by rfl) ⟨62033282, by rfl⟩ : syracuseStep 82711043 = 124066565) B124066565
theorem B55140695 : Blo 1911435 55140695 := bstep (se 1 (by rfl) ⟨41355521, by rfl⟩ : syracuseStep 55140695 = 82711043) B82711043
theorem B36760463 : Blo 1911435 36760463 := bstep (se 1 (by rfl) ⟨27570347, by rfl⟩ : syracuseStep 36760463 = 55140695) B55140695
theorem B24506975 : Blo 1911435 24506975 := bstep (se 1 (by rfl) ⟨18380231, by rfl⟩ : syracuseStep 24506975 = 36760463) B36760463
theorem B16337983 : Blo 1911435 16337983 := bstep (se 1 (by rfl) ⟨12253487, by rfl⟩ : syracuseStep 16337983 = 24506975) B24506975
theorem B21783977 : Blo 1911435 21783977 := bstep (se 2 (by rfl) ⟨8168991, by rfl⟩ : syracuseStep 21783977 = 16337983) B16337983
theorem B14522651 : Blo 1911435 14522651 := bstep (se 1 (by rfl) ⟨10891988, by rfl⟩ : syracuseStep 14522651 = 21783977) B21783977
theorem B9681767 : Blo 1911435 9681767 := bstep (se 1 (by rfl) ⟨7261325, by rfl⟩ : syracuseStep 9681767 = 14522651) B14522651
theorem B6454511 : Blo 1911435 6454511 := bstep (se 1 (by rfl) ⟨4840883, by rfl⟩ : syracuseStep 6454511 = 9681767) B9681767
theorem B4303007 : Blo 1911435 4303007 := bstep (se 1 (by rfl) ⟨3227255, by rfl⟩ : syracuseStep 4303007 = 6454511) B6454511
theorem B2868671 : Blo 1911435 2868671 := bstep (se 1 (by rfl) ⟨2151503, by rfl⟩ : syracuseStep 2868671 = 4303007) B4303007
theorem B1912447 : Blo 1911435 1912447 := bstep (se 1 (by rfl) ⟨1434335, by rfl⟩ : syracuseStep 1912447 = 2868671) B2868671
theorem B2868677 : Blo 1911435 2868677 := bbase (se 4 (by rfl) ⟨268938, by rfl⟩ : syracuseStep 2868677 = 537877) (by norm_num)
theorem B1912451 : Blo 1911435 1912451 := bstep (se 1 (by rfl) ⟨1434338, by rfl⟩ : syracuseStep 1912451 = 2868677) B2868677
theorem B3227269 : Blo 1911435 3227269 := bbase (se 4 (by rfl) ⟨302556, by rfl⟩ : syracuseStep 3227269 = 605113) (by norm_num)
theorem B4303025 : Blo 1911435 4303025 := bstep (se 2 (by rfl) ⟨1613634, by rfl⟩ : syracuseStep 4303025 = 3227269) B3227269
theorem B2868683 : Blo 1911435 2868683 := bstep (se 1 (by rfl) ⟨2151512, by rfl⟩ : syracuseStep 2868683 = 4303025) B4303025
theorem B1912455 : Blo 1911435 1912455 := bstep (se 1 (by rfl) ⟨1434341, by rfl⟩ : syracuseStep 1912455 = 2868683) B2868683
theorem B2151517 : Blo 1911435 2151517 := bbase (se 3 (by rfl) ⟨403409, by rfl⟩ : syracuseStep 2151517 = 806819) (by norm_num)
theorem B2868689 : Blo 1911435 2868689 := bstep (se 2 (by rfl) ⟨1075758, by rfl⟩ : syracuseStep 2868689 = 2151517) B2151517
theorem B1912459 : Blo 1911435 1912459 := bstep (se 1 (by rfl) ⟨1434344, by rfl⟩ : syracuseStep 1912459 = 2868689) B2868689
theorem B6454565 : Blo 1911435 6454565 := bbase (se 4 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 6454565 = 1210231) (by norm_num)
theorem B4303043 : Blo 1911435 4303043 := bstep (se 1 (by rfl) ⟨3227282, by rfl⟩ : syracuseStep 4303043 = 6454565) B6454565
theorem B2868695 : Blo 1911435 2868695 := bstep (se 1 (by rfl) ⟨2151521, by rfl⟩ : syracuseStep 2868695 = 4303043) B4303043
theorem B1912463 : Blo 1911435 1912463 := bstep (se 1 (by rfl) ⟨1434347, by rfl⟩ : syracuseStep 1912463 = 2868695) B2868695
theorem B2868701 : Blo 1911435 2868701 := bbase (se 3 (by rfl) ⟨537881, by rfl⟩ : syracuseStep 2868701 = 1075763) (by norm_num)
theorem B1912467 : Blo 1911435 1912467 := bstep (se 1 (by rfl) ⟨1434350, by rfl⟩ : syracuseStep 1912467 = 2868701) B2868701
theorem B4303061 : Blo 1911435 4303061 := bbase (se 7 (by rfl) ⟨50426, by rfl⟩ : syracuseStep 4303061 = 100853) (by norm_num)
theorem B2868707 : Blo 1911435 2868707 := bstep (se 1 (by rfl) ⟨2151530, by rfl⟩ : syracuseStep 2868707 = 4303061) B4303061
theorem B1912471 : Blo 1911435 1912471 := bstep (se 1 (by rfl) ⟨1434353, by rfl⟩ : syracuseStep 1912471 = 2868707) B2868707
theorem B50361301 : Blo 1911435 50361301 := bbase (se 7 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 50361301 = 1180343) (by norm_num)
theorem B67148401 : Blo 1911435 67148401 := bstep (se 2 (by rfl) ⟨25180650, by rfl⟩ : syracuseStep 67148401 = 50361301) B50361301
theorem B89531201 : Blo 1911435 89531201 := bstep (se 2 (by rfl) ⟨33574200, by rfl⟩ : syracuseStep 89531201 = 67148401) B67148401
theorem B238749869 : Blo 1911435 238749869 := bstep (se 3 (by rfl) ⟨44765600, by rfl⟩ : syracuseStep 238749869 = 89531201) B89531201
theorem B159166579 : Blo 1911435 159166579 := bstep (se 1 (by rfl) ⟨119374934, by rfl⟩ : syracuseStep 159166579 = 238749869) B238749869
theorem B212222105 : Blo 1911435 212222105 := bstep (se 2 (by rfl) ⟨79583289, by rfl⟩ : syracuseStep 212222105 = 159166579) B159166579
theorem B141481403 : Blo 1911435 141481403 := bstep (se 1 (by rfl) ⟨106111052, by rfl⟩ : syracuseStep 141481403 = 212222105) B212222105
theorem B94320935 : Blo 1911435 94320935 := bstep (se 1 (by rfl) ⟨70740701, by rfl⟩ : syracuseStep 94320935 = 141481403) B141481403
theorem B62880623 : Blo 1911435 62880623 := bstep (se 1 (by rfl) ⟨47160467, by rfl⟩ : syracuseStep 62880623 = 94320935) B94320935
theorem B41920415 : Blo 1911435 41920415 := bstep (se 1 (by rfl) ⟨31440311, by rfl⟩ : syracuseStep 41920415 = 62880623) B62880623
theorem B27946943 : Blo 1911435 27946943 := bstep (se 1 (by rfl) ⟨20960207, by rfl⟩ : syracuseStep 27946943 = 41920415) B41920415
theorem B18631295 : Blo 1911435 18631295 := bstep (se 1 (by rfl) ⟨13973471, by rfl⟩ : syracuseStep 18631295 = 27946943) B27946943
theorem B12420863 : Blo 1911435 12420863 := bstep (se 1 (by rfl) ⟨9315647, by rfl⟩ : syracuseStep 12420863 = 18631295) B18631295
theorem B8280575 : Blo 1911435 8280575 := bstep (se 1 (by rfl) ⟨6210431, by rfl⟩ : syracuseStep 8280575 = 12420863) B12420863
theorem B5520383 : Blo 1911435 5520383 := bstep (se 1 (by rfl) ⟨4140287, by rfl⟩ : syracuseStep 5520383 = 8280575) B8280575
theorem B3680255 : Blo 1911435 3680255 := bstep (se 1 (by rfl) ⟨2760191, by rfl⟩ : syracuseStep 3680255 = 5520383) B5520383
theorem B2453503 : Blo 1911435 2453503 := bstep (se 1 (by rfl) ⟨1840127, by rfl⟩ : syracuseStep 2453503 = 3680255) B3680255
theorem B3271337 : Blo 1911435 3271337 := bstep (se 2 (by rfl) ⟨1226751, by rfl⟩ : syracuseStep 3271337 = 2453503) B2453503
theorem B2180891 : Blo 1911435 2180891 := bstep (se 1 (by rfl) ⟨1635668, by rfl⟩ : syracuseStep 2180891 = 3271337) B3271337
theorem B5815709 : Blo 1911435 5815709 := bstep (se 3 (by rfl) ⟨1090445, by rfl⟩ : syracuseStep 5815709 = 2180891) B2180891
theorem B3877139 : Blo 1911435 3877139 := bstep (se 1 (by rfl) ⟨2907854, by rfl⟩ : syracuseStep 3877139 = 5815709) B5815709
theorem B2584759 : Blo 1911435 2584759 := bstep (se 1 (by rfl) ⟨1938569, by rfl⟩ : syracuseStep 2584759 = 3877139) B3877139
theorem B3446345 : Blo 1911435 3446345 := bstep (se 2 (by rfl) ⟨1292379, by rfl⟩ : syracuseStep 3446345 = 2584759) B2584759
theorem B9190253 : Blo 1911435 9190253 := bstep (se 3 (by rfl) ⟨1723172, by rfl⟩ : syracuseStep 9190253 = 3446345) B3446345
theorem B6126835 : Blo 1911435 6126835 := bstep (se 1 (by rfl) ⟨4595126, by rfl⟩ : syracuseStep 6126835 = 9190253) B9190253
theorem B8169113 : Blo 1911435 8169113 := bstep (se 2 (by rfl) ⟨3063417, by rfl⟩ : syracuseStep 8169113 = 6126835) B6126835
theorem B5446075 : Blo 1911435 5446075 := bstep (se 1 (by rfl) ⟨4084556, by rfl⟩ : syracuseStep 5446075 = 8169113) B8169113
theorem B7261433 : Blo 1911435 7261433 := bstep (se 2 (by rfl) ⟨2723037, by rfl⟩ : syracuseStep 7261433 = 5446075) B5446075
theorem B4840955 : Blo 1911435 4840955 := bstep (se 1 (by rfl) ⟨3630716, by rfl⟩ : syracuseStep 4840955 = 7261433) B7261433
theorem B3227303 : Blo 1911435 3227303 := bstep (se 1 (by rfl) ⟨2420477, by rfl⟩ : syracuseStep 3227303 = 4840955) B4840955
theorem B2151535 : Blo 1911435 2151535 := bstep (se 1 (by rfl) ⟨1613651, by rfl⟩ : syracuseStep 2151535 = 3227303) B3227303
theorem B2868713 : Blo 1911435 2868713 := bstep (se 2 (by rfl) ⟨1075767, by rfl⟩ : syracuseStep 2868713 = 2151535) B2151535
theorem B1912475 : Blo 1911435 1912475 := bstep (se 1 (by rfl) ⟨1434356, by rfl⟩ : syracuseStep 1912475 = 2868713) B2868713
theorem B2486981 : Blo 1911435 2486981 := bbase (se 4 (by rfl) ⟨233154, by rfl⟩ : syracuseStep 2486981 = 466309) (by norm_num)
theorem B6631949 : Blo 1911435 6631949 := bstep (se 3 (by rfl) ⟨1243490, by rfl⟩ : syracuseStep 6631949 = 2486981) B2486981
theorem B4421299 : Blo 1911435 4421299 := bstep (se 1 (by rfl) ⟨3315974, by rfl⟩ : syracuseStep 4421299 = 6631949) B6631949
theorem B5895065 : Blo 1911435 5895065 := bstep (se 2 (by rfl) ⟨2210649, by rfl⟩ : syracuseStep 5895065 = 4421299) B4421299
theorem B15720173 : Blo 1911435 15720173 := bstep (se 3 (by rfl) ⟨2947532, by rfl⟩ : syracuseStep 15720173 = 5895065) B5895065
theorem B10480115 : Blo 1911435 10480115 := bstep (se 1 (by rfl) ⟨7860086, by rfl⟩ : syracuseStep 10480115 = 15720173) B15720173
theorem B27946973 : Blo 1911435 27946973 := bstep (se 3 (by rfl) ⟨5240057, by rfl⟩ : syracuseStep 27946973 = 10480115) B10480115
theorem B18631315 : Blo 1911435 18631315 := bstep (se 1 (by rfl) ⟨13973486, by rfl⟩ : syracuseStep 18631315 = 27946973) B27946973
theorem B99367013 : Blo 1911435 99367013 := bstep (se 4 (by rfl) ⟨9315657, by rfl⟩ : syracuseStep 99367013 = 18631315) B18631315
theorem B66244675 : Blo 1911435 66244675 := bstep (se 1 (by rfl) ⟨49683506, by rfl⟩ : syracuseStep 66244675 = 99367013) B99367013
theorem B88326233 : Blo 1911435 88326233 := bstep (se 2 (by rfl) ⟨33122337, by rfl⟩ : syracuseStep 88326233 = 66244675) B66244675
theorem B58884155 : Blo 1911435 58884155 := bstep (se 1 (by rfl) ⟨44163116, by rfl⟩ : syracuseStep 58884155 = 88326233) B88326233
theorem B39256103 : Blo 1911435 39256103 := bstep (se 1 (by rfl) ⟨29442077, by rfl⟩ : syracuseStep 39256103 = 58884155) B58884155
theorem B26170735 : Blo 1911435 26170735 := bstep (se 1 (by rfl) ⟨19628051, by rfl⟩ : syracuseStep 26170735 = 39256103) B39256103
theorem B34894313 : Blo 1911435 34894313 := bstep (se 2 (by rfl) ⟨13085367, by rfl⟩ : syracuseStep 34894313 = 26170735) B26170735
theorem B23262875 : Blo 1911435 23262875 := bstep (se 1 (by rfl) ⟨17447156, by rfl⟩ : syracuseStep 23262875 = 34894313) B34894313
theorem B15508583 : Blo 1911435 15508583 := bstep (se 1 (by rfl) ⟨11631437, by rfl⟩ : syracuseStep 15508583 = 23262875) B23262875
theorem B10339055 : Blo 1911435 10339055 := bstep (se 1 (by rfl) ⟨7754291, by rfl⟩ : syracuseStep 10339055 = 15508583) B15508583
theorem B6892703 : Blo 1911435 6892703 := bstep (se 1 (by rfl) ⟨5169527, by rfl⟩ : syracuseStep 6892703 = 10339055) B10339055
theorem B4595135 : Blo 1911435 4595135 := bstep (se 1 (by rfl) ⟨3446351, by rfl⟩ : syracuseStep 4595135 = 6892703) B6892703
theorem B12253693 : Blo 1911435 12253693 := bstep (se 3 (by rfl) ⟨2297567, by rfl⟩ : syracuseStep 12253693 = 4595135) B4595135
theorem B16338257 : Blo 1911435 16338257 := bstep (se 2 (by rfl) ⟨6126846, by rfl⟩ : syracuseStep 16338257 = 12253693) B12253693
theorem B10892171 : Blo 1911435 10892171 := bstep (se 1 (by rfl) ⟨8169128, by rfl⟩ : syracuseStep 10892171 = 16338257) B16338257
theorem B7261447 : Blo 1911435 7261447 := bstep (se 1 (by rfl) ⟨5446085, by rfl⟩ : syracuseStep 7261447 = 10892171) B10892171
theorem B9681929 : Blo 1911435 9681929 := bstep (se 2 (by rfl) ⟨3630723, by rfl⟩ : syracuseStep 9681929 = 7261447) B7261447
theorem B6454619 : Blo 1911435 6454619 := bstep (se 1 (by rfl) ⟨4840964, by rfl⟩ : syracuseStep 6454619 = 9681929) B9681929
theorem B4303079 : Blo 1911435 4303079 := bstep (se 1 (by rfl) ⟨3227309, by rfl⟩ : syracuseStep 4303079 = 6454619) B6454619
theorem B2868719 : Blo 1911435 2868719 := bstep (se 1 (by rfl) ⟨2151539, by rfl⟩ : syracuseStep 2868719 = 4303079) B4303079
theorem B1912479 : Blo 1911435 1912479 := bstep (se 1 (by rfl) ⟨1434359, by rfl⟩ : syracuseStep 1912479 = 2868719) B2868719
theorem B2868725 : Blo 1911435 2868725 := bbase (se 5 (by rfl) ⟨134471, by rfl⟩ : syracuseStep 2868725 = 268943) (by norm_num)
theorem B1912483 : Blo 1911435 1912483 := bstep (se 1 (by rfl) ⟨1434362, by rfl⟩ : syracuseStep 1912483 = 2868725) B2868725
theorem B3063437 : Blo 1911435 3063437 := bbase (se 3 (by rfl) ⟨574394, by rfl⟩ : syracuseStep 3063437 = 1148789) (by norm_num)
theorem B2042291 : Blo 1911435 2042291 := bstep (se 1 (by rfl) ⟨1531718, by rfl⟩ : syracuseStep 2042291 = 3063437) B3063437
theorem B5446109 : Blo 1911435 5446109 := bstep (se 3 (by rfl) ⟨1021145, by rfl⟩ : syracuseStep 5446109 = 2042291) B2042291
theorem B3630739 : Blo 1911435 3630739 := bstep (se 1 (by rfl) ⟨2723054, by rfl⟩ : syracuseStep 3630739 = 5446109) B5446109
theorem B4840985 : Blo 1911435 4840985 := bstep (se 2 (by rfl) ⟨1815369, by rfl⟩ : syracuseStep 4840985 = 3630739) B3630739
theorem B3227323 : Blo 1911435 3227323 := bstep (se 1 (by rfl) ⟨2420492, by rfl⟩ : syracuseStep 3227323 = 4840985) B4840985
theorem B4303097 : Blo 1911435 4303097 := bstep (se 2 (by rfl) ⟨1613661, by rfl⟩ : syracuseStep 4303097 = 3227323) B3227323
theorem B2868731 : Blo 1911435 2868731 := bstep (se 1 (by rfl) ⟨2151548, by rfl⟩ : syracuseStep 2868731 = 4303097) B4303097
theorem B1912487 : Blo 1911435 1912487 := bstep (se 1 (by rfl) ⟨1434365, by rfl⟩ : syracuseStep 1912487 = 2868731) B2868731
theorem B2151553 : Blo 1911435 2151553 := bbase (se 2 (by rfl) ⟨806832, by rfl⟩ : syracuseStep 2151553 = 1613665) (by norm_num)
theorem B2868737 : Blo 1911435 2868737 := bstep (se 2 (by rfl) ⟨1075776, by rfl⟩ : syracuseStep 2868737 = 2151553) B2151553
theorem B1912491 : Blo 1911435 1912491 := bstep (se 1 (by rfl) ⟨1434368, by rfl⟩ : syracuseStep 1912491 = 2868737) B2868737
theorem B4841005 : Blo 1911435 4841005 := bbase (se 3 (by rfl) ⟨907688, by rfl⟩ : syracuseStep 4841005 = 1815377) (by norm_num)
theorem B6454673 : Blo 1911435 6454673 := bstep (se 2 (by rfl) ⟨2420502, by rfl⟩ : syracuseStep 6454673 = 4841005) B4841005
theorem B4303115 : Blo 1911435 4303115 := bstep (se 1 (by rfl) ⟨3227336, by rfl⟩ : syracuseStep 4303115 = 6454673) B6454673
theorem B2868743 : Blo 1911435 2868743 := bstep (se 1 (by rfl) ⟨2151557, by rfl⟩ : syracuseStep 2868743 = 4303115) B4303115
theorem B1912495 : Blo 1911435 1912495 := bstep (se 1 (by rfl) ⟨1434371, by rfl⟩ : syracuseStep 1912495 = 2868743) B2868743
theorem B2868749 : Blo 1911435 2868749 := bbase (se 3 (by rfl) ⟨537890, by rfl⟩ : syracuseStep 2868749 = 1075781) (by norm_num)
theorem B1912499 : Blo 1911435 1912499 := bstep (se 1 (by rfl) ⟨1434374, by rfl⟩ : syracuseStep 1912499 = 2868749) B2868749
theorem B4303133 : Blo 1911435 4303133 := bbase (se 3 (by rfl) ⟨806837, by rfl⟩ : syracuseStep 4303133 = 1613675) (by norm_num)
theorem B2868755 : Blo 1911435 2868755 := bstep (se 1 (by rfl) ⟨2151566, by rfl⟩ : syracuseStep 2868755 = 4303133) B4303133
theorem B1912503 : Blo 1911435 1912503 := bstep (se 1 (by rfl) ⟨1434377, by rfl⟩ : syracuseStep 1912503 = 2868755) B2868755
theorem B3227357 : Blo 1911435 3227357 := bbase (se 3 (by rfl) ⟨605129, by rfl⟩ : syracuseStep 3227357 = 1210259) (by norm_num)
theorem B2151571 : Blo 1911435 2151571 := bstep (se 1 (by rfl) ⟨1613678, by rfl⟩ : syracuseStep 2151571 = 3227357) B3227357
theorem B2868761 : Blo 1911435 2868761 := bstep (se 2 (by rfl) ⟨1075785, by rfl⟩ : syracuseStep 2868761 = 2151571) B2151571
theorem B1912507 : Blo 1911435 1912507 := bstep (se 1 (by rfl) ⟨1434380, by rfl⟩ : syracuseStep 1912507 = 2868761) B2868761
theorem B6126949 : Blo 1911435 6126949 := bbase (se 4 (by rfl) ⟨574401, by rfl⟩ : syracuseStep 6126949 = 1148803) (by norm_num)
theorem B8169265 : Blo 1911435 8169265 := bstep (se 2 (by rfl) ⟨3063474, by rfl⟩ : syracuseStep 8169265 = 6126949) B6126949
theorem B10892353 : Blo 1911435 10892353 := bstep (se 2 (by rfl) ⟨4084632, by rfl⟩ : syracuseStep 10892353 = 8169265) B8169265
theorem B14523137 : Blo 1911435 14523137 := bstep (se 2 (by rfl) ⟨5446176, by rfl⟩ : syracuseStep 14523137 = 10892353) B10892353
theorem B9682091 : Blo 1911435 9682091 := bstep (se 1 (by rfl) ⟨7261568, by rfl⟩ : syracuseStep 9682091 = 14523137) B14523137
theorem B6454727 : Blo 1911435 6454727 := bstep (se 1 (by rfl) ⟨4841045, by rfl⟩ : syracuseStep 6454727 = 9682091) B9682091
theorem B4303151 : Blo 1911435 4303151 := bstep (se 1 (by rfl) ⟨3227363, by rfl⟩ : syracuseStep 4303151 = 6454727) B6454727
theorem B2868767 : Blo 1911435 2868767 := bstep (se 1 (by rfl) ⟨2151575, by rfl⟩ : syracuseStep 2868767 = 4303151) B4303151
theorem B1912511 : Blo 1911435 1912511 := bstep (se 1 (by rfl) ⟨1434383, by rfl⟩ : syracuseStep 1912511 = 2868767) B2868767
theorem B2868773 : Blo 1911435 2868773 := bbase (se 4 (by rfl) ⟨268947, by rfl⟩ : syracuseStep 2868773 = 537895) (by norm_num)
theorem B1912515 : Blo 1911435 1912515 := bstep (se 1 (by rfl) ⟨1434386, by rfl⟩ : syracuseStep 1912515 = 2868773) B2868773
theorem B2420533 : Blo 1911435 2420533 := bbase (se 5 (by rfl) ⟨113462, by rfl⟩ : syracuseStep 2420533 = 226925) (by norm_num)
theorem B3227377 : Blo 1911435 3227377 := bstep (se 2 (by rfl) ⟨1210266, by rfl⟩ : syracuseStep 3227377 = 2420533) B2420533
theorem B4303169 : Blo 1911435 4303169 := bstep (se 2 (by rfl) ⟨1613688, by rfl⟩ : syracuseStep 4303169 = 3227377) B3227377
theorem B2868779 : Blo 1911435 2868779 := bstep (se 1 (by rfl) ⟨2151584, by rfl⟩ : syracuseStep 2868779 = 4303169) B4303169
theorem B1912519 : Blo 1911435 1912519 := bstep (se 1 (by rfl) ⟨1434389, by rfl⟩ : syracuseStep 1912519 = 2868779) B2868779
theorem B2151589 : Blo 1911435 2151589 := bbase (se 4 (by rfl) ⟨201711, by rfl⟩ : syracuseStep 2151589 = 403423) (by norm_num)
theorem B2868785 : Blo 1911435 2868785 := bstep (se 2 (by rfl) ⟨1075794, by rfl⟩ : syracuseStep 2868785 = 2151589) B2151589
theorem B1912523 : Blo 1911435 1912523 := bstep (se 1 (by rfl) ⟨1434392, by rfl⟩ : syracuseStep 1912523 = 2868785) B2868785
theorem B2584829 : Blo 1911435 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B6892877 : Blo 1911435 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B18381005 : Blo 1911435 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B12254003 : Blo 1911435 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B8169335 : Blo 1911435 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B5446223 : Blo 1911435 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B3630815 : Blo 1911435 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B2420543 : Blo 1911435 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B6454781 : Blo 1911435 6454781 := bstep (se 3 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 6454781 = 2420543) B2420543
theorem B4303187 : Blo 1911435 4303187 := bstep (se 1 (by rfl) ⟨3227390, by rfl⟩ : syracuseStep 4303187 = 6454781) B6454781
theorem B2868791 : Blo 1911435 2868791 := bstep (se 1 (by rfl) ⟨2151593, by rfl⟩ : syracuseStep 2868791 = 4303187) B4303187
theorem B1912527 : Blo 1911435 1912527 := bstep (se 1 (by rfl) ⟨1434395, by rfl⟩ : syracuseStep 1912527 = 2868791) B2868791
theorem B2868797 : Blo 1911435 2868797 := bbase (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) (by norm_num)
theorem B1912531 : Blo 1911435 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B4303205 : Blo 1911435 4303205 := bbase (se 4 (by rfl) ⟨403425, by rfl⟩ : syracuseStep 4303205 = 806851) (by norm_num)
theorem B2868803 : Blo 1911435 2868803 := bstep (se 1 (by rfl) ⟨2151602, by rfl⟩ : syracuseStep 2868803 = 4303205) B4303205
theorem B1912535 : Blo 1911435 1912535 := bstep (se 1 (by rfl) ⟨1434401, by rfl⟩ : syracuseStep 1912535 = 2868803) B2868803
theorem B4841117 : Blo 1911435 4841117 := bbase (se 3 (by rfl) ⟨907709, by rfl⟩ : syracuseStep 4841117 = 1815419) (by norm_num)
theorem B3227411 : Blo 1911435 3227411 := bstep (se 1 (by rfl) ⟨2420558, by rfl⟩ : syracuseStep 3227411 = 4841117) B4841117
theorem B2151607 : Blo 1911435 2151607 := bstep (se 1 (by rfl) ⟨1613705, by rfl⟩ : syracuseStep 2151607 = 3227411) B3227411
theorem B2868809 : Blo 1911435 2868809 := bstep (se 2 (by rfl) ⟨1075803, by rfl⟩ : syracuseStep 2868809 = 2151607) B2151607
theorem B1912539 : Blo 1911435 1912539 := bstep (se 1 (by rfl) ⟨1434404, by rfl⟩ : syracuseStep 1912539 = 2868809) B2868809
theorem B3630845 : Blo 1911435 3630845 := bbase (se 3 (by rfl) ⟨680783, by rfl⟩ : syracuseStep 3630845 = 1361567) (by norm_num)
theorem B9682253 : Blo 1911435 9682253 := bstep (se 3 (by rfl) ⟨1815422, by rfl⟩ : syracuseStep 9682253 = 3630845) B3630845
theorem B6454835 : Blo 1911435 6454835 := bstep (se 1 (by rfl) ⟨4841126, by rfl⟩ : syracuseStep 6454835 = 9682253) B9682253
theorem B4303223 : Blo 1911435 4303223 := bstep (se 1 (by rfl) ⟨3227417, by rfl⟩ : syracuseStep 4303223 = 6454835) B6454835
theorem B2868815 : Blo 1911435 2868815 := bstep (se 1 (by rfl) ⟨2151611, by rfl⟩ : syracuseStep 2868815 = 4303223) B4303223
theorem B1912543 : Blo 1911435 1912543 := bstep (se 1 (by rfl) ⟨1434407, by rfl⟩ : syracuseStep 1912543 = 2868815) B2868815
theorem B2868821 : Blo 1911435 2868821 := bbase (se 8 (by rfl) ⟨16809, by rfl⟩ : syracuseStep 2868821 = 33619) (by norm_num)
theorem B1912547 : Blo 1911435 1912547 := bstep (se 1 (by rfl) ⟨1434410, by rfl⟩ : syracuseStep 1912547 = 2868821) B2868821
theorem B4595309 : Blo 1911435 4595309 := bbase (se 3 (by rfl) ⟨861620, by rfl⟩ : syracuseStep 4595309 = 1723241) (by norm_num)
theorem B3063539 : Blo 1911435 3063539 := bstep (se 1 (by rfl) ⟨2297654, by rfl⟩ : syracuseStep 3063539 = 4595309) B4595309
theorem B8169437 : Blo 1911435 8169437 := bstep (se 3 (by rfl) ⟨1531769, by rfl⟩ : syracuseStep 8169437 = 3063539) B3063539
theorem B5446291 : Blo 1911435 5446291 := bstep (se 1 (by rfl) ⟨4084718, by rfl⟩ : syracuseStep 5446291 = 8169437) B8169437
theorem B7261721 : Blo 1911435 7261721 := bstep (se 2 (by rfl) ⟨2723145, by rfl⟩ : syracuseStep 7261721 = 5446291) B5446291
theorem B4841147 : Blo 1911435 4841147 := bstep (se 1 (by rfl) ⟨3630860, by rfl⟩ : syracuseStep 4841147 = 7261721) B7261721
theorem B3227431 : Blo 1911435 3227431 := bstep (se 1 (by rfl) ⟨2420573, by rfl⟩ : syracuseStep 3227431 = 4841147) B4841147
theorem B4303241 : Blo 1911435 4303241 := bstep (se 2 (by rfl) ⟨1613715, by rfl⟩ : syracuseStep 4303241 = 3227431) B3227431
theorem B2868827 : Blo 1911435 2868827 := bstep (se 1 (by rfl) ⟨2151620, by rfl⟩ : syracuseStep 2868827 = 4303241) B4303241
theorem B1912551 : Blo 1911435 1912551 := bstep (se 1 (by rfl) ⟨1434413, by rfl⟩ : syracuseStep 1912551 = 2868827) B2868827
theorem B2151625 : Blo 1911435 2151625 := bbase (se 2 (by rfl) ⟨806859, by rfl⟩ : syracuseStep 2151625 = 1613719) (by norm_num)
theorem B2868833 : Blo 1911435 2868833 := bstep (se 2 (by rfl) ⟨1075812, by rfl⟩ : syracuseStep 2868833 = 2151625) B2151625
theorem B1912555 : Blo 1911435 1912555 := bstep (se 1 (by rfl) ⟨1434416, by rfl⟩ : syracuseStep 1912555 = 2868833) B2868833
theorem B5595941 : Blo 1911435 5595941 := bbase (se 4 (by rfl) ⟨524619, by rfl⟩ : syracuseStep 5595941 = 1049239) (by norm_num)
theorem B3730627 : Blo 1911435 3730627 := bstep (se 1 (by rfl) ⟨2797970, by rfl⟩ : syracuseStep 3730627 = 5595941) B5595941
theorem B19896677 : Blo 1911435 19896677 := bstep (se 4 (by rfl) ⟨1865313, by rfl⟩ : syracuseStep 19896677 = 3730627) B3730627
theorem B13264451 : Blo 1911435 13264451 := bstep (se 1 (by rfl) ⟨9948338, by rfl⟩ : syracuseStep 13264451 = 19896677) B19896677
theorem B8842967 : Blo 1911435 8842967 := bstep (se 1 (by rfl) ⟨6632225, by rfl⟩ : syracuseStep 8842967 = 13264451) B13264451
theorem B5895311 : Blo 1911435 5895311 := bstep (se 1 (by rfl) ⟨4421483, by rfl⟩ : syracuseStep 5895311 = 8842967) B8842967
theorem B62883317 : Blo 1911435 62883317 := bstep (se 5 (by rfl) ⟨2947655, by rfl⟩ : syracuseStep 62883317 = 5895311) B5895311
theorem B41922211 : Blo 1911435 41922211 := bstep (se 1 (by rfl) ⟨31441658, by rfl⟩ : syracuseStep 41922211 = 62883317) B62883317
theorem B55896281 : Blo 1911435 55896281 := bstep (se 2 (by rfl) ⟨20961105, by rfl⟩ : syracuseStep 55896281 = 41922211) B41922211
theorem B37264187 : Blo 1911435 37264187 := bstep (se 1 (by rfl) ⟨27948140, by rfl⟩ : syracuseStep 37264187 = 55896281) B55896281
theorem B24842791 : Blo 1911435 24842791 := bstep (se 1 (by rfl) ⟨18632093, by rfl⟩ : syracuseStep 24842791 = 37264187) B37264187
theorem B132494885 : Blo 1911435 132494885 := bstep (se 4 (by rfl) ⟨12421395, by rfl⟩ : syracuseStep 132494885 = 24842791) B24842791
theorem B88329923 : Blo 1911435 88329923 := bstep (se 1 (by rfl) ⟨66247442, by rfl⟩ : syracuseStep 88329923 = 132494885) B132494885
theorem B58886615 : Blo 1911435 58886615 := bstep (se 1 (by rfl) ⟨44164961, by rfl⟩ : syracuseStep 58886615 = 88329923) B88329923
theorem B157030973 : Blo 1911435 157030973 := bstep (se 3 (by rfl) ⟨29443307, by rfl⟩ : syracuseStep 157030973 = 58886615) B58886615
theorem B104687315 : Blo 1911435 104687315 := bstep (se 1 (by rfl) ⟨78515486, by rfl⟩ : syracuseStep 104687315 = 157030973) B157030973
theorem B69791543 : Blo 1911435 69791543 := bstep (se 1 (by rfl) ⟨52343657, by rfl⟩ : syracuseStep 69791543 = 104687315) B104687315
theorem B46527695 : Blo 1911435 46527695 := bstep (se 1 (by rfl) ⟨34895771, by rfl⟩ : syracuseStep 46527695 = 69791543) B69791543
theorem B31018463 : Blo 1911435 31018463 := bstep (se 1 (by rfl) ⟨23263847, by rfl⟩ : syracuseStep 31018463 = 46527695) B46527695
theorem B20678975 : Blo 1911435 20678975 := bstep (se 1 (by rfl) ⟨15509231, by rfl⟩ : syracuseStep 20678975 = 31018463) B31018463
theorem B13785983 : Blo 1911435 13785983 := bstep (se 1 (by rfl) ⟨10339487, by rfl⟩ : syracuseStep 13785983 = 20678975) B20678975
theorem B9190655 : Blo 1911435 9190655 := bstep (se 1 (by rfl) ⟨6892991, by rfl⟩ : syracuseStep 9190655 = 13785983) B13785983
theorem B6127103 : Blo 1911435 6127103 := bstep (se 1 (by rfl) ⟨4595327, by rfl⟩ : syracuseStep 6127103 = 9190655) B9190655
theorem B16338941 : Blo 1911435 16338941 := bstep (se 3 (by rfl) ⟨3063551, by rfl⟩ : syracuseStep 16338941 = 6127103) B6127103
theorem B10892627 : Blo 1911435 10892627 := bstep (se 1 (by rfl) ⟨8169470, by rfl⟩ : syracuseStep 10892627 = 16338941) B16338941
theorem B7261751 : Blo 1911435 7261751 := bstep (se 1 (by rfl) ⟨5446313, by rfl⟩ : syracuseStep 7261751 = 10892627) B10892627
theorem B4841167 : Blo 1911435 4841167 := bstep (se 1 (by rfl) ⟨3630875, by rfl⟩ : syracuseStep 4841167 = 7261751) B7261751
theorem B6454889 : Blo 1911435 6454889 := bstep (se 2 (by rfl) ⟨2420583, by rfl⟩ : syracuseStep 6454889 = 4841167) B4841167
theorem B4303259 : Blo 1911435 4303259 := bstep (se 1 (by rfl) ⟨3227444, by rfl⟩ : syracuseStep 4303259 = 6454889) B6454889
theorem B2868839 : Blo 1911435 2868839 := bstep (se 1 (by rfl) ⟨2151629, by rfl⟩ : syracuseStep 2868839 = 4303259) B4303259
theorem B1912559 : Blo 1911435 1912559 := bstep (se 1 (by rfl) ⟨1434419, by rfl⟩ : syracuseStep 1912559 = 2868839) B2868839
theorem B2868845 : Blo 1911435 2868845 := bbase (se 3 (by rfl) ⟨537908, by rfl⟩ : syracuseStep 2868845 = 1075817) (by norm_num)
theorem B1912563 : Blo 1911435 1912563 := bstep (se 1 (by rfl) ⟨1434422, by rfl⟩ : syracuseStep 1912563 = 2868845) B2868845
theorem B4303277 : Blo 1911435 4303277 := bbase (se 3 (by rfl) ⟨806864, by rfl⟩ : syracuseStep 4303277 = 1613729) (by norm_num)
theorem B2868851 : Blo 1911435 2868851 := bstep (se 1 (by rfl) ⟨2151638, by rfl⟩ : syracuseStep 2868851 = 4303277) B4303277
theorem B1912567 : Blo 1911435 1912567 := bstep (se 1 (by rfl) ⟨1434425, by rfl⟩ : syracuseStep 1912567 = 2868851) B2868851
theorem B2042381 : Blo 1911435 2042381 := bbase (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) (by norm_num)
theorem B5446349 : Blo 1911435 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B3630899 : Blo 1911435 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B2420599 : Blo 1911435 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B3227465 : Blo 1911435 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B2151643 : Blo 1911435 2151643 := bstep (se 1 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 2151643 = 3227465) B3227465
theorem B2868857 : Blo 1911435 2868857 := bstep (se 2 (by rfl) ⟨1075821, by rfl⟩ : syracuseStep 2868857 = 2151643) B2151643
theorem B1912571 : Blo 1911435 1912571 := bstep (se 1 (by rfl) ⟨1434428, by rfl⟩ : syracuseStep 1912571 = 2868857) B2868857
theorem B9814517 : Blo 1911435 9814517 := bbase (se 5 (by rfl) ⟨460055, by rfl⟩ : syracuseStep 9814517 = 920111) (by norm_num)
theorem B6543011 : Blo 1911435 6543011 := bstep (se 1 (by rfl) ⟨4907258, by rfl⟩ : syracuseStep 6543011 = 9814517) B9814517
theorem B17448029 : Blo 1911435 17448029 := bstep (se 3 (by rfl) ⟨3271505, by rfl⟩ : syracuseStep 17448029 = 6543011) B6543011
theorem B11632019 : Blo 1911435 11632019 := bstep (se 1 (by rfl) ⟨8724014, by rfl⟩ : syracuseStep 11632019 = 17448029) B17448029
theorem B31018717 : Blo 1911435 31018717 := bstep (se 3 (by rfl) ⟨5816009, by rfl⟩ : syracuseStep 31018717 = 11632019) B11632019
theorem B41358289 : Blo 1911435 41358289 := bstep (se 2 (by rfl) ⟨15509358, by rfl⟩ : syracuseStep 41358289 = 31018717) B31018717
theorem B55144385 : Blo 1911435 55144385 := bstep (se 2 (by rfl) ⟨20679144, by rfl⟩ : syracuseStep 55144385 = 41358289) B41358289
theorem B36762923 : Blo 1911435 36762923 := bstep (se 1 (by rfl) ⟨27572192, by rfl⟩ : syracuseStep 36762923 = 55144385) B55144385
theorem B24508615 : Blo 1911435 24508615 := bstep (se 1 (by rfl) ⟨18381461, by rfl⟩ : syracuseStep 24508615 = 36762923) B36762923
theorem B32678153 : Blo 1911435 32678153 := bstep (se 2 (by rfl) ⟨12254307, by rfl⟩ : syracuseStep 32678153 = 24508615) B24508615
theorem B21785435 : Blo 1911435 21785435 := bstep (se 1 (by rfl) ⟨16339076, by rfl⟩ : syracuseStep 21785435 = 32678153) B32678153
theorem B14523623 : Blo 1911435 14523623 := bstep (se 1 (by rfl) ⟨10892717, by rfl⟩ : syracuseStep 14523623 = 21785435) B21785435
theorem B9682415 : Blo 1911435 9682415 := bstep (se 1 (by rfl) ⟨7261811, by rfl⟩ : syracuseStep 9682415 = 14523623) B14523623
theorem B6454943 : Blo 1911435 6454943 := bstep (se 1 (by rfl) ⟨4841207, by rfl⟩ : syracuseStep 6454943 = 9682415) B9682415
theorem B4303295 : Blo 1911435 4303295 := bstep (se 1 (by rfl) ⟨3227471, by rfl⟩ : syracuseStep 4303295 = 6454943) B6454943
theorem B2868863 : Blo 1911435 2868863 := bstep (se 1 (by rfl) ⟨2151647, by rfl⟩ : syracuseStep 2868863 = 4303295) B4303295
theorem B1912575 : Blo 1911435 1912575 := bstep (se 1 (by rfl) ⟨1434431, by rfl⟩ : syracuseStep 1912575 = 2868863) B2868863
theorem B2868869 : Blo 1911435 2868869 := bbase (se 4 (by rfl) ⟨268956, by rfl⟩ : syracuseStep 2868869 = 537913) (by norm_num)
theorem B1912579 : Blo 1911435 1912579 := bstep (se 1 (by rfl) ⟨1434434, by rfl⟩ : syracuseStep 1912579 = 2868869) B2868869
theorem B3227485 : Blo 1911435 3227485 := bbase (se 3 (by rfl) ⟨605153, by rfl⟩ : syracuseStep 3227485 = 1210307) (by norm_num)
theorem B4303313 : Blo 1911435 4303313 := bstep (se 2 (by rfl) ⟨1613742, by rfl⟩ : syracuseStep 4303313 = 3227485) B3227485
theorem B2868875 : Blo 1911435 2868875 := bstep (se 1 (by rfl) ⟨2151656, by rfl⟩ : syracuseStep 2868875 = 4303313) B4303313
theorem B1912583 : Blo 1911435 1912583 := bstep (se 1 (by rfl) ⟨1434437, by rfl⟩ : syracuseStep 1912583 = 2868875) B2868875
theorem B2151661 : Blo 1911435 2151661 := bbase (se 3 (by rfl) ⟨403436, by rfl⟩ : syracuseStep 2151661 = 806873) (by norm_num)
theorem B2868881 : Blo 1911435 2868881 := bstep (se 2 (by rfl) ⟨1075830, by rfl⟩ : syracuseStep 2868881 = 2151661) B2151661
theorem B1912587 : Blo 1911435 1912587 := bstep (se 1 (by rfl) ⟨1434440, by rfl⟩ : syracuseStep 1912587 = 2868881) B2868881
theorem B6454997 : Blo 1911435 6454997 := bbase (se 7 (by rfl) ⟨75644, by rfl⟩ : syracuseStep 6454997 = 151289) (by norm_num)
theorem B4303331 : Blo 1911435 4303331 := bstep (se 1 (by rfl) ⟨3227498, by rfl⟩ : syracuseStep 4303331 = 6454997) B6454997
theorem B2868887 : Blo 1911435 2868887 := bstep (se 1 (by rfl) ⟨2151665, by rfl⟩ : syracuseStep 2868887 = 4303331) B4303331
theorem B1912591 : Blo 1911435 1912591 := bstep (se 1 (by rfl) ⟨1434443, by rfl⟩ : syracuseStep 1912591 = 2868887) B2868887
theorem B2868893 : Blo 1911435 2868893 := bbase (se 3 (by rfl) ⟨537917, by rfl⟩ : syracuseStep 2868893 = 1075835) (by norm_num)
theorem B1912595 : Blo 1911435 1912595 := bstep (se 1 (by rfl) ⟨1434446, by rfl⟩ : syracuseStep 1912595 = 2868893) B2868893
theorem B4303349 : Blo 1911435 4303349 := bbase (se 5 (by rfl) ⟨201719, by rfl⟩ : syracuseStep 4303349 = 403439) (by norm_num)
theorem B2868899 : Blo 1911435 2868899 := bstep (se 1 (by rfl) ⟨2151674, by rfl⟩ : syracuseStep 2868899 = 4303349) B4303349
theorem B1912599 : Blo 1911435 1912599 := bstep (se 1 (by rfl) ⟨1434449, by rfl⟩ : syracuseStep 1912599 = 2868899) B2868899
theorem B6543109 : Blo 1911435 6543109 := bbase (se 4 (by rfl) ⟨613416, by rfl⟩ : syracuseStep 6543109 = 1226833) (by norm_num)
theorem B8724145 : Blo 1911435 8724145 := bstep (se 2 (by rfl) ⟨3271554, by rfl⟩ : syracuseStep 8724145 = 6543109) B6543109
theorem B11632193 : Blo 1911435 11632193 := bstep (se 2 (by rfl) ⟨4362072, by rfl⟩ : syracuseStep 11632193 = 8724145) B8724145
theorem B7754795 : Blo 1911435 7754795 := bstep (se 1 (by rfl) ⟨5816096, by rfl⟩ : syracuseStep 7754795 = 11632193) B11632193
theorem B5169863 : Blo 1911435 5169863 := bstep (se 1 (by rfl) ⟨3877397, by rfl⟩ : syracuseStep 5169863 = 7754795) B7754795
theorem B13786301 : Blo 1911435 13786301 := bstep (se 3 (by rfl) ⟨2584931, by rfl⟩ : syracuseStep 13786301 = 5169863) B5169863
theorem B36763469 : Blo 1911435 36763469 := bstep (se 3 (by rfl) ⟨6893150, by rfl⟩ : syracuseStep 36763469 = 13786301) B13786301
theorem B24508979 : Blo 1911435 24508979 := bstep (se 1 (by rfl) ⟨18381734, by rfl⟩ : syracuseStep 24508979 = 36763469) B36763469
theorem B16339319 : Blo 1911435 16339319 := bstep (se 1 (by rfl) ⟨12254489, by rfl⟩ : syracuseStep 16339319 = 24508979) B24508979
theorem B10892879 : Blo 1911435 10892879 := bstep (se 1 (by rfl) ⟨8169659, by rfl⟩ : syracuseStep 10892879 = 16339319) B16339319
theorem B7261919 : Blo 1911435 7261919 := bstep (se 1 (by rfl) ⟨5446439, by rfl⟩ : syracuseStep 7261919 = 10892879) B10892879
theorem B4841279 : Blo 1911435 4841279 := bstep (se 1 (by rfl) ⟨3630959, by rfl⟩ : syracuseStep 4841279 = 7261919) B7261919
theorem B3227519 : Blo 1911435 3227519 := bstep (se 1 (by rfl) ⟨2420639, by rfl⟩ : syracuseStep 3227519 = 4841279) B4841279
theorem B2151679 : Blo 1911435 2151679 := bstep (se 1 (by rfl) ⟨1613759, by rfl⟩ : syracuseStep 2151679 = 3227519) B3227519
theorem B2868905 : Blo 1911435 2868905 := bstep (se 2 (by rfl) ⟨1075839, by rfl⟩ : syracuseStep 2868905 = 2151679) B2151679
theorem B1912603 : Blo 1911435 1912603 := bstep (se 1 (by rfl) ⟨1434452, by rfl⟩ : syracuseStep 1912603 = 2868905) B2868905
theorem B3063629 : Blo 1911435 3063629 := bbase (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) (by norm_num)
theorem B2042419 : Blo 1911435 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B2723225 : Blo 1911435 2723225 := bstep (se 2 (by rfl) ⟨1021209, by rfl⟩ : syracuseStep 2723225 = 2042419) B2042419
theorem B7261933 : Blo 1911435 7261933 := bstep (se 3 (by rfl) ⟨1361612, by rfl⟩ : syracuseStep 7261933 = 2723225) B2723225
theorem B9682577 : Blo 1911435 9682577 := bstep (se 2 (by rfl) ⟨3630966, by rfl⟩ : syracuseStep 9682577 = 7261933) B7261933
theorem B6455051 : Blo 1911435 6455051 := bstep (se 1 (by rfl) ⟨4841288, by rfl⟩ : syracuseStep 6455051 = 9682577) B9682577
theorem B4303367 : Blo 1911435 4303367 := bstep (se 1 (by rfl) ⟨3227525, by rfl⟩ : syracuseStep 4303367 = 6455051) B6455051
theorem B2868911 : Blo 1911435 2868911 := bstep (se 1 (by rfl) ⟨2151683, by rfl⟩ : syracuseStep 2868911 = 4303367) B4303367
theorem B1912607 : Blo 1911435 1912607 := bstep (se 1 (by rfl) ⟨1434455, by rfl⟩ : syracuseStep 1912607 = 2868911) B2868911
theorem B2868917 : Blo 1911435 2868917 := bbase (se 5 (by rfl) ⟨134480, by rfl⟩ : syracuseStep 2868917 = 268961) (by norm_num)
theorem B1912611 : Blo 1911435 1912611 := bstep (se 1 (by rfl) ⟨1434458, by rfl⟩ : syracuseStep 1912611 = 2868917) B2868917
theorem B4841309 : Blo 1911435 4841309 := bbase (se 3 (by rfl) ⟨907745, by rfl⟩ : syracuseStep 4841309 = 1815491) (by norm_num)
theorem B3227539 : Blo 1911435 3227539 := bstep (se 1 (by rfl) ⟨2420654, by rfl⟩ : syracuseStep 3227539 = 4841309) B4841309
theorem B4303385 : Blo 1911435 4303385 := bstep (se 2 (by rfl) ⟨1613769, by rfl⟩ : syracuseStep 4303385 = 3227539) B3227539
theorem B2868923 : Blo 1911435 2868923 := bstep (se 1 (by rfl) ⟨2151692, by rfl⟩ : syracuseStep 2868923 = 4303385) B4303385
theorem B1912615 : Blo 1911435 1912615 := bstep (se 1 (by rfl) ⟨1434461, by rfl⟩ : syracuseStep 1912615 = 2868923) B2868923
theorem B2151697 : Blo 1911435 2151697 := bbase (se 2 (by rfl) ⟨806886, by rfl⟩ : syracuseStep 2151697 = 1613773) (by norm_num)
theorem B2868929 : Blo 1911435 2868929 := bstep (se 2 (by rfl) ⟨1075848, by rfl⟩ : syracuseStep 2868929 = 2151697) B2151697
theorem B1912619 : Blo 1911435 1912619 := bstep (se 1 (by rfl) ⟨1434464, by rfl⟩ : syracuseStep 1912619 = 2868929) B2868929
theorem B3630997 : Blo 1911435 3630997 := bbase (se 6 (by rfl) ⟨85101, by rfl⟩ : syracuseStep 3630997 = 170203) (by norm_num)
theorem B4841329 : Blo 1911435 4841329 := bstep (se 2 (by rfl) ⟨1815498, by rfl⟩ : syracuseStep 4841329 = 3630997) B3630997
theorem B6455105 : Blo 1911435 6455105 := bstep (se 2 (by rfl) ⟨2420664, by rfl⟩ : syracuseStep 6455105 = 4841329) B4841329
theorem B4303403 : Blo 1911435 4303403 := bstep (se 1 (by rfl) ⟨3227552, by rfl⟩ : syracuseStep 4303403 = 6455105) B6455105
theorem B2868935 : Blo 1911435 2868935 := bstep (se 1 (by rfl) ⟨2151701, by rfl⟩ : syracuseStep 2868935 = 4303403) B4303403
theorem B1912623 : Blo 1911435 1912623 := bstep (se 1 (by rfl) ⟨1434467, by rfl⟩ : syracuseStep 1912623 = 2868935) B2868935
theorem B2868941 : Blo 1911435 2868941 := bbase (se 3 (by rfl) ⟨537926, by rfl⟩ : syracuseStep 2868941 = 1075853) (by norm_num)
theorem B1912627 : Blo 1911435 1912627 := bstep (se 1 (by rfl) ⟨1434470, by rfl⟩ : syracuseStep 1912627 = 2868941) B2868941
theorem B4303421 : Blo 1911435 4303421 := bbase (se 3 (by rfl) ⟨806891, by rfl⟩ : syracuseStep 4303421 = 1613783) (by norm_num)
theorem B2868947 : Blo 1911435 2868947 := bstep (se 1 (by rfl) ⟨2151710, by rfl⟩ : syracuseStep 2868947 = 4303421) B4303421
theorem B1912631 : Blo 1911435 1912631 := bstep (se 1 (by rfl) ⟨1434473, by rfl⟩ : syracuseStep 1912631 = 2868947) B2868947
theorem B3227573 : Blo 1911435 3227573 := bbase (se 5 (by rfl) ⟨151292, by rfl⟩ : syracuseStep 3227573 = 302585) (by norm_num)
theorem B2151715 : Blo 1911435 2151715 := bstep (se 1 (by rfl) ⟨1613786, by rfl⟩ : syracuseStep 2151715 = 3227573) B3227573
theorem B2868953 : Blo 1911435 2868953 := bstep (se 2 (by rfl) ⟨1075857, by rfl⟩ : syracuseStep 2868953 = 2151715) B2151715
theorem B1912635 : Blo 1911435 1912635 := bstep (se 1 (by rfl) ⟨1434476, by rfl⟩ : syracuseStep 1912635 = 2868953) B2868953
theorem B2042453 : Blo 1911435 2042453 := bbase (se 8 (by rfl) ⟨11967, by rfl⟩ : syracuseStep 2042453 = 23935) (by norm_num)
theorem B5446541 : Blo 1911435 5446541 := bstep (se 3 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 5446541 = 2042453) B2042453
theorem B14524109 : Blo 1911435 14524109 := bstep (se 3 (by rfl) ⟨2723270, by rfl⟩ : syracuseStep 14524109 = 5446541) B5446541
theorem B9682739 : Blo 1911435 9682739 := bstep (se 1 (by rfl) ⟨7262054, by rfl⟩ : syracuseStep 9682739 = 14524109) B14524109
theorem B6455159 : Blo 1911435 6455159 := bstep (se 1 (by rfl) ⟨4841369, by rfl⟩ : syracuseStep 6455159 = 9682739) B9682739
theorem B4303439 : Blo 1911435 4303439 := bstep (se 1 (by rfl) ⟨3227579, by rfl⟩ : syracuseStep 4303439 = 6455159) B6455159
theorem B2868959 : Blo 1911435 2868959 := bstep (se 1 (by rfl) ⟨2151719, by rfl⟩ : syracuseStep 2868959 = 4303439) B4303439
theorem B1912639 : Blo 1911435 1912639 := bstep (se 1 (by rfl) ⟨1434479, by rfl⟩ : syracuseStep 1912639 = 2868959) B2868959
theorem B2868965 : Blo 1911435 2868965 := bbase (se 4 (by rfl) ⟨268965, by rfl⟩ : syracuseStep 2868965 = 537931) (by norm_num)
theorem B1912643 : Blo 1911435 1912643 := bstep (se 1 (by rfl) ⟨1434482, by rfl⟩ : syracuseStep 1912643 = 2868965) B2868965
theorem B5446565 : Blo 1911435 5446565 := bbase (se 4 (by rfl) ⟨510615, by rfl⟩ : syracuseStep 5446565 = 1021231) (by norm_num)
theorem B3631043 : Blo 1911435 3631043 := bstep (se 1 (by rfl) ⟨2723282, by rfl⟩ : syracuseStep 3631043 = 5446565) B5446565
theorem B2420695 : Blo 1911435 2420695 := bstep (se 1 (by rfl) ⟨1815521, by rfl⟩ : syracuseStep 2420695 = 3631043) B3631043
theorem B3227593 : Blo 1911435 3227593 := bstep (se 2 (by rfl) ⟨1210347, by rfl⟩ : syracuseStep 3227593 = 2420695) B2420695
theorem B4303457 : Blo 1911435 4303457 := bstep (se 2 (by rfl) ⟨1613796, by rfl⟩ : syracuseStep 4303457 = 3227593) B3227593
theorem B2868971 : Blo 1911435 2868971 := bstep (se 1 (by rfl) ⟨2151728, by rfl⟩ : syracuseStep 2868971 = 4303457) B4303457
theorem B1912647 : Blo 1911435 1912647 := bstep (se 1 (by rfl) ⟨1434485, by rfl⟩ : syracuseStep 1912647 = 2868971) B2868971
theorem B2151733 : Blo 1911435 2151733 := bbase (se 5 (by rfl) ⟨100862, by rfl⟩ : syracuseStep 2151733 = 201725) (by norm_num)
theorem B2868977 : Blo 1911435 2868977 := bstep (se 2 (by rfl) ⟨1075866, by rfl⟩ : syracuseStep 2868977 = 2151733) B2151733
theorem B1912651 : Blo 1911435 1912651 := bstep (se 1 (by rfl) ⟨1434488, by rfl⟩ : syracuseStep 1912651 = 2868977) B2868977
theorem B2420705 : Blo 1911435 2420705 := bbase (se 2 (by rfl) ⟨907764, by rfl⟩ : syracuseStep 2420705 = 1815529) (by norm_num)
theorem B6455213 : Blo 1911435 6455213 := bstep (se 3 (by rfl) ⟨1210352, by rfl⟩ : syracuseStep 6455213 = 2420705) B2420705
theorem B4303475 : Blo 1911435 4303475 := bstep (se 1 (by rfl) ⟨3227606, by rfl⟩ : syracuseStep 4303475 = 6455213) B6455213
theorem B2868983 : Blo 1911435 2868983 := bstep (se 1 (by rfl) ⟨2151737, by rfl⟩ : syracuseStep 2868983 = 4303475) B4303475
theorem B1912655 : Blo 1911435 1912655 := bstep (se 1 (by rfl) ⟨1434491, by rfl⟩ : syracuseStep 1912655 = 2868983) B2868983
theorem B2868989 : Blo 1911435 2868989 := bbase (se 3 (by rfl) ⟨537935, by rfl⟩ : syracuseStep 2868989 = 1075871) (by norm_num)
theorem B1912659 : Blo 1911435 1912659 := bstep (se 1 (by rfl) ⟨1434494, by rfl⟩ : syracuseStep 1912659 = 2868989) B2868989
theorem B4303493 : Blo 1911435 4303493 := bbase (se 4 (by rfl) ⟨403452, by rfl⟩ : syracuseStep 4303493 = 806905) (by norm_num)
theorem B2868995 : Blo 1911435 2868995 := bstep (se 1 (by rfl) ⟨2151746, by rfl⟩ : syracuseStep 2868995 = 4303493) B4303493
theorem B1912663 : Blo 1911435 1912663 := bstep (se 1 (by rfl) ⟨1434497, by rfl⟩ : syracuseStep 1912663 = 2868995) B2868995
theorem B13974869 : Blo 1911435 13974869 := bbase (se 11 (by rfl) ⟨10235, by rfl⟩ : syracuseStep 13974869 = 20471) (by norm_num)
theorem B9316579 : Blo 1911435 9316579 := bstep (se 1 (by rfl) ⟨6987434, by rfl⟩ : syracuseStep 9316579 = 13974869) B13974869
theorem B12422105 : Blo 1911435 12422105 := bstep (se 2 (by rfl) ⟨4658289, by rfl⟩ : syracuseStep 12422105 = 9316579) B9316579
theorem B8281403 : Blo 1911435 8281403 := bstep (se 1 (by rfl) ⟨6211052, by rfl⟩ : syracuseStep 8281403 = 12422105) B12422105
theorem B5520935 : Blo 1911435 5520935 := bstep (se 1 (by rfl) ⟨4140701, by rfl⟩ : syracuseStep 5520935 = 8281403) B8281403
theorem B3680623 : Blo 1911435 3680623 := bstep (se 1 (by rfl) ⟨2760467, by rfl⟩ : syracuseStep 3680623 = 5520935) B5520935
theorem B19629989 : Blo 1911435 19629989 := bstep (se 4 (by rfl) ⟨1840311, by rfl⟩ : syracuseStep 19629989 = 3680623) B3680623
theorem B13086659 : Blo 1911435 13086659 := bstep (se 1 (by rfl) ⟨9814994, by rfl⟩ : syracuseStep 13086659 = 19629989) B19629989
theorem B8724439 : Blo 1911435 8724439 := bstep (se 1 (by rfl) ⟨6543329, by rfl⟩ : syracuseStep 8724439 = 13086659) B13086659
theorem B11632585 : Blo 1911435 11632585 := bstep (se 2 (by rfl) ⟨4362219, by rfl⟩ : syracuseStep 11632585 = 8724439) B8724439
theorem B15510113 : Blo 1911435 15510113 := bstep (se 2 (by rfl) ⟨5816292, by rfl⟩ : syracuseStep 15510113 = 11632585) B11632585
theorem B10340075 : Blo 1911435 10340075 := bstep (se 1 (by rfl) ⟨7755056, by rfl⟩ : syracuseStep 10340075 = 15510113) B15510113
theorem B6893383 : Blo 1911435 6893383 := bstep (se 1 (by rfl) ⟨5170037, by rfl⟩ : syracuseStep 6893383 = 10340075) B10340075
theorem B9191177 : Blo 1911435 9191177 := bstep (se 2 (by rfl) ⟨3446691, by rfl⟩ : syracuseStep 9191177 = 6893383) B6893383
theorem B6127451 : Blo 1911435 6127451 := bstep (se 1 (by rfl) ⟨4595588, by rfl⟩ : syracuseStep 6127451 = 9191177) B9191177
theorem B4084967 : Blo 1911435 4084967 := bstep (se 1 (by rfl) ⟨3063725, by rfl⟩ : syracuseStep 4084967 = 6127451) B6127451
theorem B2723311 : Blo 1911435 2723311 := bstep (se 1 (by rfl) ⟨2042483, by rfl⟩ : syracuseStep 2723311 = 4084967) B4084967
theorem B3631081 : Blo 1911435 3631081 := bstep (se 2 (by rfl) ⟨1361655, by rfl⟩ : syracuseStep 3631081 = 2723311) B2723311
theorem B4841441 : Blo 1911435 4841441 := bstep (se 2 (by rfl) ⟨1815540, by rfl⟩ : syracuseStep 4841441 = 3631081) B3631081
theorem B3227627 : Blo 1911435 3227627 := bstep (se 1 (by rfl) ⟨2420720, by rfl⟩ : syracuseStep 3227627 = 4841441) B4841441
theorem B2151751 : Blo 1911435 2151751 := bstep (se 1 (by rfl) ⟨1613813, by rfl⟩ : syracuseStep 2151751 = 3227627) B3227627
theorem B2869001 : Blo 1911435 2869001 := bstep (se 2 (by rfl) ⟨1075875, by rfl⟩ : syracuseStep 2869001 = 2151751) B2151751
theorem B1912667 : Blo 1911435 1912667 := bstep (se 1 (by rfl) ⟨1434500, by rfl⟩ : syracuseStep 1912667 = 2869001) B2869001
theorem B9682901 : Blo 1911435 9682901 := bbase (se 7 (by rfl) ⟨113471, by rfl⟩ : syracuseStep 9682901 = 226943) (by norm_num)
theorem B6455267 : Blo 1911435 6455267 := bstep (se 1 (by rfl) ⟨4841450, by rfl⟩ : syracuseStep 6455267 = 9682901) B9682901
theorem B4303511 : Blo 1911435 4303511 := bstep (se 1 (by rfl) ⟨3227633, by rfl⟩ : syracuseStep 4303511 = 6455267) B6455267
theorem B2869007 : Blo 1911435 2869007 := bstep (se 1 (by rfl) ⟨2151755, by rfl⟩ : syracuseStep 2869007 = 4303511) B4303511
theorem B1912671 : Blo 1911435 1912671 := bstep (se 1 (by rfl) ⟨1434503, by rfl⟩ : syracuseStep 1912671 = 2869007) B2869007
theorem B2869013 : Blo 1911435 2869013 := bbase (se 6 (by rfl) ⟨67242, by rfl⟩ : syracuseStep 2869013 = 134485) (by norm_num)
theorem B1912675 : Blo 1911435 1912675 := bstep (se 1 (by rfl) ⟨1434506, by rfl⟩ : syracuseStep 1912675 = 2869013) B2869013
theorem B28331221 : Blo 1911435 28331221 := bbase (se 7 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 28331221 = 664013) (by norm_num)
theorem B37774961 : Blo 1911435 37774961 := bstep (se 2 (by rfl) ⟨14165610, by rfl⟩ : syracuseStep 37774961 = 28331221) B28331221
theorem B25183307 : Blo 1911435 25183307 := bstep (se 1 (by rfl) ⟨18887480, by rfl⟩ : syracuseStep 25183307 = 37774961) B37774961
theorem B16788871 : Blo 1911435 16788871 := bstep (se 1 (by rfl) ⟨12591653, by rfl⟩ : syracuseStep 16788871 = 25183307) B25183307
theorem B22385161 : Blo 1911435 22385161 := bstep (se 2 (by rfl) ⟨8394435, by rfl⟩ : syracuseStep 22385161 = 16788871) B16788871
theorem B119387525 : Blo 1911435 119387525 := bstep (se 4 (by rfl) ⟨11192580, by rfl⟩ : syracuseStep 119387525 = 22385161) B22385161
theorem B1273466933 : Blo 1911435 1273466933 := bstep (se 5 (by rfl) ⟨59693762, by rfl⟩ : syracuseStep 1273466933 = 119387525) B119387525
theorem B848977955 : Blo 1911435 848977955 := bstep (se 1 (by rfl) ⟨636733466, by rfl⟩ : syracuseStep 848977955 = 1273466933) B1273466933
theorem B565985303 : Blo 1911435 565985303 := bstep (se 1 (by rfl) ⟨424488977, by rfl⟩ : syracuseStep 565985303 = 848977955) B848977955
theorem B377323535 : Blo 1911435 377323535 := bstep (se 1 (by rfl) ⟨282992651, by rfl⟩ : syracuseStep 377323535 = 565985303) B565985303
theorem B251549023 : Blo 1911435 251549023 := bstep (se 1 (by rfl) ⟨188661767, by rfl⟩ : syracuseStep 251549023 = 377323535) B377323535
theorem B335398697 : Blo 1911435 335398697 := bstep (se 2 (by rfl) ⟨125774511, by rfl⟩ : syracuseStep 335398697 = 251549023) B251549023
theorem B223599131 : Blo 1911435 223599131 := bstep (se 1 (by rfl) ⟨167699348, by rfl⟩ : syracuseStep 223599131 = 335398697) B335398697
theorem B149066087 : Blo 1911435 149066087 := bstep (se 1 (by rfl) ⟨111799565, by rfl⟩ : syracuseStep 149066087 = 223599131) B223599131
theorem B397509565 : Blo 1911435 397509565 := bstep (se 3 (by rfl) ⟨74533043, by rfl⟩ : syracuseStep 397509565 = 149066087) B149066087
theorem B530012753 : Blo 1911435 530012753 := bstep (se 2 (by rfl) ⟨198754782, by rfl⟩ : syracuseStep 530012753 = 397509565) B397509565
theorem B353341835 : Blo 1911435 353341835 := bstep (se 1 (by rfl) ⟨265006376, by rfl⟩ : syracuseStep 353341835 = 530012753) B530012753
theorem B235561223 : Blo 1911435 235561223 := bstep (se 1 (by rfl) ⟨176670917, by rfl⟩ : syracuseStep 235561223 = 353341835) B353341835
theorem B628163261 : Blo 1911435 628163261 := bstep (se 3 (by rfl) ⟨117780611, by rfl⟩ : syracuseStep 628163261 = 235561223) B235561223
theorem B418775507 : Blo 1911435 418775507 := bstep (se 1 (by rfl) ⟨314081630, by rfl⟩ : syracuseStep 418775507 = 628163261) B628163261
theorem B279183671 : Blo 1911435 279183671 := bstep (se 1 (by rfl) ⟨209387753, by rfl⟩ : syracuseStep 279183671 = 418775507) B418775507
theorem B186122447 : Blo 1911435 186122447 := bstep (se 1 (by rfl) ⟨139591835, by rfl⟩ : syracuseStep 186122447 = 279183671) B279183671
theorem B124081631 : Blo 1911435 124081631 := bstep (se 1 (by rfl) ⟨93061223, by rfl⟩ : syracuseStep 124081631 = 186122447) B186122447
theorem B82721087 : Blo 1911435 82721087 := bstep (se 1 (by rfl) ⟨62040815, by rfl⟩ : syracuseStep 82721087 = 124081631) B124081631
theorem B55147391 : Blo 1911435 55147391 := bstep (se 1 (by rfl) ⟨41360543, by rfl⟩ : syracuseStep 55147391 = 82721087) B82721087
theorem B36764927 : Blo 1911435 36764927 := bstep (se 1 (by rfl) ⟨27573695, by rfl⟩ : syracuseStep 36764927 = 55147391) B55147391
theorem B24509951 : Blo 1911435 24509951 := bstep (se 1 (by rfl) ⟨18382463, by rfl⟩ : syracuseStep 24509951 = 36764927) B36764927
theorem B16339967 : Blo 1911435 16339967 := bstep (se 1 (by rfl) ⟨12254975, by rfl⟩ : syracuseStep 16339967 = 24509951) B24509951
theorem B10893311 : Blo 1911435 10893311 := bstep (se 1 (by rfl) ⟨8169983, by rfl⟩ : syracuseStep 10893311 = 16339967) B16339967
theorem B7262207 : Blo 1911435 7262207 := bstep (se 1 (by rfl) ⟨5446655, by rfl⟩ : syracuseStep 7262207 = 10893311) B10893311
theorem B4841471 : Blo 1911435 4841471 := bstep (se 1 (by rfl) ⟨3631103, by rfl⟩ : syracuseStep 4841471 = 7262207) B7262207
theorem B3227647 : Blo 1911435 3227647 := bstep (se 1 (by rfl) ⟨2420735, by rfl⟩ : syracuseStep 3227647 = 4841471) B4841471
theorem B4303529 : Blo 1911435 4303529 := bstep (se 2 (by rfl) ⟨1613823, by rfl⟩ : syracuseStep 4303529 = 3227647) B3227647
theorem B2869019 : Blo 1911435 2869019 := bstep (se 1 (by rfl) ⟨2151764, by rfl⟩ : syracuseStep 2869019 = 4303529) B4303529
theorem B1912679 : Blo 1911435 1912679 := bstep (se 1 (by rfl) ⟨1434509, by rfl⟩ : syracuseStep 1912679 = 2869019) B2869019
theorem B2151769 : Blo 1911435 2151769 := bbase (se 2 (by rfl) ⟨806913, by rfl⟩ : syracuseStep 2151769 = 1613827) (by norm_num)
theorem B2869025 : Blo 1911435 2869025 := bstep (se 2 (by rfl) ⟨1075884, by rfl⟩ : syracuseStep 2869025 = 2151769) B2151769
theorem B1912683 : Blo 1911435 1912683 := bstep (se 1 (by rfl) ⟨1434512, by rfl⟩ : syracuseStep 1912683 = 2869025) B2869025
theorem B3063757 : Blo 1911435 3063757 := bbase (se 3 (by rfl) ⟨574454, by rfl⟩ : syracuseStep 3063757 = 1148909) (by norm_num)
theorem B4085009 : Blo 1911435 4085009 := bstep (se 2 (by rfl) ⟨1531878, by rfl⟩ : syracuseStep 4085009 = 3063757) B3063757
theorem B2723339 : Blo 1911435 2723339 := bstep (se 1 (by rfl) ⟨2042504, by rfl⟩ : syracuseStep 2723339 = 4085009) B4085009
theorem B7262237 : Blo 1911435 7262237 := bstep (se 3 (by rfl) ⟨1361669, by rfl⟩ : syracuseStep 7262237 = 2723339) B2723339
theorem B4841491 : Blo 1911435 4841491 := bstep (se 1 (by rfl) ⟨3631118, by rfl⟩ : syracuseStep 4841491 = 7262237) B7262237
theorem B6455321 : Blo 1911435 6455321 := bstep (se 2 (by rfl) ⟨2420745, by rfl⟩ : syracuseStep 6455321 = 4841491) B4841491
theorem B4303547 : Blo 1911435 4303547 := bstep (se 1 (by rfl) ⟨3227660, by rfl⟩ : syracuseStep 4303547 = 6455321) B6455321
theorem B2869031 : Blo 1911435 2869031 := bstep (se 1 (by rfl) ⟨2151773, by rfl⟩ : syracuseStep 2869031 = 4303547) B4303547
theorem B1912687 : Blo 1911435 1912687 := bstep (se 1 (by rfl) ⟨1434515, by rfl⟩ : syracuseStep 1912687 = 2869031) B2869031
theorem B2869037 : Blo 1911435 2869037 := bbase (se 3 (by rfl) ⟨537944, by rfl⟩ : syracuseStep 2869037 = 1075889) (by norm_num)
theorem B1912691 : Blo 1911435 1912691 := bstep (se 1 (by rfl) ⟨1434518, by rfl⟩ : syracuseStep 1912691 = 2869037) B2869037
theorem B4303565 : Blo 1911435 4303565 := bbase (se 3 (by rfl) ⟨806918, by rfl⟩ : syracuseStep 4303565 = 1613837) (by norm_num)
theorem B2869043 : Blo 1911435 2869043 := bstep (se 1 (by rfl) ⟨2151782, by rfl⟩ : syracuseStep 2869043 = 4303565) B4303565
theorem B1912695 : Blo 1911435 1912695 := bstep (se 1 (by rfl) ⟨1434521, by rfl⟩ : syracuseStep 1912695 = 2869043) B2869043
theorem B2420761 : Blo 1911435 2420761 := bbase (se 2 (by rfl) ⟨907785, by rfl⟩ : syracuseStep 2420761 = 1815571) (by norm_num)
theorem B3227681 : Blo 1911435 3227681 := bstep (se 2 (by rfl) ⟨1210380, by rfl⟩ : syracuseStep 3227681 = 2420761) B2420761
theorem B2151787 : Blo 1911435 2151787 := bstep (se 1 (by rfl) ⟨1613840, by rfl⟩ : syracuseStep 2151787 = 3227681) B3227681
theorem B2869049 : Blo 1911435 2869049 := bstep (se 2 (by rfl) ⟨1075893, by rfl⟩ : syracuseStep 2869049 = 2151787) B2151787
theorem B1912699 : Blo 1911435 1912699 := bstep (se 1 (by rfl) ⟨1434524, by rfl⟩ : syracuseStep 1912699 = 2869049) B2869049
theorem B8170085 : Blo 1911435 8170085 := bbase (se 4 (by rfl) ⟨765945, by rfl⟩ : syracuseStep 8170085 = 1531891) (by norm_num)
theorem B21786893 : Blo 1911435 21786893 := bstep (se 3 (by rfl) ⟨4085042, by rfl⟩ : syracuseStep 21786893 = 8170085) B8170085
theorem B14524595 : Blo 1911435 14524595 := bstep (se 1 (by rfl) ⟨10893446, by rfl⟩ : syracuseStep 14524595 = 21786893) B21786893
theorem B9683063 : Blo 1911435 9683063 := bstep (se 1 (by rfl) ⟨7262297, by rfl⟩ : syracuseStep 9683063 = 14524595) B14524595
theorem B6455375 : Blo 1911435 6455375 := bstep (se 1 (by rfl) ⟨4841531, by rfl⟩ : syracuseStep 6455375 = 9683063) B9683063
theorem B4303583 : Blo 1911435 4303583 := bstep (se 1 (by rfl) ⟨3227687, by rfl⟩ : syracuseStep 4303583 = 6455375) B6455375
theorem B2869055 : Blo 1911435 2869055 := bstep (se 1 (by rfl) ⟨2151791, by rfl⟩ : syracuseStep 2869055 = 4303583) B4303583
theorem B1912703 : Blo 1911435 1912703 := bstep (se 1 (by rfl) ⟨1434527, by rfl⟩ : syracuseStep 1912703 = 2869055) B2869055
theorem B2869061 : Blo 1911435 2869061 := bbase (se 4 (by rfl) ⟨268974, by rfl⟩ : syracuseStep 2869061 = 537949) (by norm_num)
theorem B1912707 : Blo 1911435 1912707 := bstep (se 1 (by rfl) ⟨1434530, by rfl⟩ : syracuseStep 1912707 = 2869061) B2869061
theorem B3227701 : Blo 1911435 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B4303601 : Blo 1911435 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B2869067 : Blo 1911435 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B1912711 : Blo 1911435 1912711 := bstep (se 1 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 1912711 = 2869067) B2869067
theorem B2151805 : Blo 1911435 2151805 := bbase (se 3 (by rfl) ⟨403463, by rfl⟩ : syracuseStep 2151805 = 806927) (by norm_num)
theorem B2869073 : Blo 1911435 2869073 := bstep (se 2 (by rfl) ⟨1075902, by rfl⟩ : syracuseStep 2869073 = 2151805) B2151805
theorem B1912715 : Blo 1911435 1912715 := bstep (se 1 (by rfl) ⟨1434536, by rfl⟩ : syracuseStep 1912715 = 2869073) B2869073
theorem B6455429 : Blo 1911435 6455429 := bbase (se 4 (by rfl) ⟨605196, by rfl⟩ : syracuseStep 6455429 = 1210393) (by norm_num)
theorem B4303619 : Blo 1911435 4303619 := bstep (se 1 (by rfl) ⟨3227714, by rfl⟩ : syracuseStep 4303619 = 6455429) B6455429
theorem B2869079 : Blo 1911435 2869079 := bstep (se 1 (by rfl) ⟨2151809, by rfl⟩ : syracuseStep 2869079 = 4303619) B4303619
theorem B1912719 : Blo 1911435 1912719 := bstep (se 1 (by rfl) ⟨1434539, by rfl⟩ : syracuseStep 1912719 = 2869079) B2869079
theorem B2869085 : Blo 1911435 2869085 := bbase (se 3 (by rfl) ⟨537953, by rfl⟩ : syracuseStep 2869085 = 1075907) (by norm_num)
theorem B1912723 : Blo 1911435 1912723 := bstep (se 1 (by rfl) ⟨1434542, by rfl⟩ : syracuseStep 1912723 = 2869085) B2869085
theorem B4303637 : Blo 1911435 4303637 := bbase (se 6 (by rfl) ⟨100866, by rfl⟩ : syracuseStep 4303637 = 201733) (by norm_num)
theorem B2869091 : Blo 1911435 2869091 := bstep (se 1 (by rfl) ⟨2151818, by rfl⟩ : syracuseStep 2869091 = 4303637) B4303637
theorem B1912727 : Blo 1911435 1912727 := bstep (se 1 (by rfl) ⟨1434545, by rfl⟩ : syracuseStep 1912727 = 2869091) B2869091
theorem B7262405 : Blo 1911435 7262405 := bbase (se 4 (by rfl) ⟨680850, by rfl⟩ : syracuseStep 7262405 = 1361701) (by norm_num)
theorem B4841603 : Blo 1911435 4841603 := bstep (se 1 (by rfl) ⟨3631202, by rfl⟩ : syracuseStep 4841603 = 7262405) B7262405
theorem B3227735 : Blo 1911435 3227735 := bstep (se 1 (by rfl) ⟨2420801, by rfl⟩ : syracuseStep 3227735 = 4841603) B4841603
theorem B2151823 : Blo 1911435 2151823 := bstep (se 1 (by rfl) ⟨1613867, by rfl⟩ : syracuseStep 2151823 = 3227735) B3227735
theorem B2869097 : Blo 1911435 2869097 := bstep (se 2 (by rfl) ⟨1075911, by rfl⟩ : syracuseStep 2869097 = 2151823) B2151823
theorem B1912731 : Blo 1911435 1912731 := bstep (se 1 (by rfl) ⟨1434548, by rfl⟩ : syracuseStep 1912731 = 2869097) B2869097
theorem B3446813 : Blo 1911435 3446813 := bbase (se 3 (by rfl) ⟨646277, by rfl⟩ : syracuseStep 3446813 = 1292555) (by norm_num)
theorem B9191501 : Blo 1911435 9191501 := bstep (se 3 (by rfl) ⟨1723406, by rfl⟩ : syracuseStep 9191501 = 3446813) B3446813
theorem B6127667 : Blo 1911435 6127667 := bstep (se 1 (by rfl) ⟨4595750, by rfl⟩ : syracuseStep 6127667 = 9191501) B9191501
theorem B4085111 : Blo 1911435 4085111 := bstep (se 1 (by rfl) ⟨3063833, by rfl⟩ : syracuseStep 4085111 = 6127667) B6127667
theorem B10893629 : Blo 1911435 10893629 := bstep (se 3 (by rfl) ⟨2042555, by rfl⟩ : syracuseStep 10893629 = 4085111) B4085111
theorem B7262419 : Blo 1911435 7262419 := bstep (se 1 (by rfl) ⟨5446814, by rfl⟩ : syracuseStep 7262419 = 10893629) B10893629
theorem B9683225 : Blo 1911435 9683225 := bstep (se 2 (by rfl) ⟨3631209, by rfl⟩ : syracuseStep 9683225 = 7262419) B7262419
theorem B6455483 : Blo 1911435 6455483 := bstep (se 1 (by rfl) ⟨4841612, by rfl⟩ : syracuseStep 6455483 = 9683225) B9683225
theorem B4303655 : Blo 1911435 4303655 := bstep (se 1 (by rfl) ⟨3227741, by rfl⟩ : syracuseStep 4303655 = 6455483) B6455483
theorem B2869103 : Blo 1911435 2869103 := bstep (se 1 (by rfl) ⟨2151827, by rfl⟩ : syracuseStep 2869103 = 4303655) B4303655
theorem B1912735 : Blo 1911435 1912735 := bstep (se 1 (by rfl) ⟨1434551, by rfl⟩ : syracuseStep 1912735 = 2869103) B2869103
theorem B2869109 : Blo 1911435 2869109 := bbase (se 5 (by rfl) ⟨134489, by rfl⟩ : syracuseStep 2869109 = 268979) (by norm_num)
theorem B1912739 : Blo 1911435 1912739 := bstep (se 1 (by rfl) ⟨1434554, by rfl⟩ : syracuseStep 1912739 = 2869109) B2869109
theorem B7755365 : Blo 1911435 7755365 := bbase (se 4 (by rfl) ⟨727065, by rfl⟩ : syracuseStep 7755365 = 1454131) (by norm_num)
theorem B5170243 : Blo 1911435 5170243 := bstep (se 1 (by rfl) ⟨3877682, by rfl⟩ : syracuseStep 5170243 = 7755365) B7755365
theorem B6893657 : Blo 1911435 6893657 := bstep (se 2 (by rfl) ⟨2585121, by rfl⟩ : syracuseStep 6893657 = 5170243) B5170243
theorem B4595771 : Blo 1911435 4595771 := bstep (se 1 (by rfl) ⟨3446828, by rfl⟩ : syracuseStep 4595771 = 6893657) B6893657
theorem B3063847 : Blo 1911435 3063847 := bstep (se 1 (by rfl) ⟨2297885, by rfl⟩ : syracuseStep 3063847 = 4595771) B4595771
theorem B4085129 : Blo 1911435 4085129 := bstep (se 2 (by rfl) ⟨1531923, by rfl⟩ : syracuseStep 4085129 = 3063847) B3063847
theorem B2723419 : Blo 1911435 2723419 := bstep (se 1 (by rfl) ⟨2042564, by rfl⟩ : syracuseStep 2723419 = 4085129) B4085129
theorem B3631225 : Blo 1911435 3631225 := bstep (se 2 (by rfl) ⟨1361709, by rfl⟩ : syracuseStep 3631225 = 2723419) B2723419
theorem B4841633 : Blo 1911435 4841633 := bstep (se 2 (by rfl) ⟨1815612, by rfl⟩ : syracuseStep 4841633 = 3631225) B3631225
theorem B3227755 : Blo 1911435 3227755 := bstep (se 1 (by rfl) ⟨2420816, by rfl⟩ : syracuseStep 3227755 = 4841633) B4841633
theorem B4303673 : Blo 1911435 4303673 := bstep (se 2 (by rfl) ⟨1613877, by rfl⟩ : syracuseStep 4303673 = 3227755) B3227755
theorem B2869115 : Blo 1911435 2869115 := bstep (se 1 (by rfl) ⟨2151836, by rfl⟩ : syracuseStep 2869115 = 4303673) B4303673
theorem B1912743 : Blo 1911435 1912743 := bstep (se 1 (by rfl) ⟨1434557, by rfl⟩ : syracuseStep 1912743 = 2869115) B2869115
theorem B2151841 : Blo 1911435 2151841 := bbase (se 2 (by rfl) ⟨806940, by rfl⟩ : syracuseStep 2151841 = 1613881) (by norm_num)
theorem B2869121 : Blo 1911435 2869121 := bstep (se 2 (by rfl) ⟨1075920, by rfl⟩ : syracuseStep 2869121 = 2151841) B2151841
theorem B1912747 : Blo 1911435 1912747 := bstep (se 1 (by rfl) ⟨1434560, by rfl⟩ : syracuseStep 1912747 = 2869121) B2869121
theorem B4841653 : Blo 1911435 4841653 := bbase (se 5 (by rfl) ⟨226952, by rfl⟩ : syracuseStep 4841653 = 453905) (by norm_num)
theorem B6455537 : Blo 1911435 6455537 := bstep (se 2 (by rfl) ⟨2420826, by rfl⟩ : syracuseStep 6455537 = 4841653) B4841653
theorem B4303691 : Blo 1911435 4303691 := bstep (se 1 (by rfl) ⟨3227768, by rfl⟩ : syracuseStep 4303691 = 6455537) B6455537
theorem B2869127 : Blo 1911435 2869127 := bstep (se 1 (by rfl) ⟨2151845, by rfl⟩ : syracuseStep 2869127 = 4303691) B4303691
theorem B1912751 : Blo 1911435 1912751 := bstep (se 1 (by rfl) ⟨1434563, by rfl⟩ : syracuseStep 1912751 = 2869127) B2869127
theorem B2869133 : Blo 1911435 2869133 := bbase (se 3 (by rfl) ⟨537962, by rfl⟩ : syracuseStep 2869133 = 1075925) (by norm_num)
theorem B1912755 : Blo 1911435 1912755 := bstep (se 1 (by rfl) ⟨1434566, by rfl⟩ : syracuseStep 1912755 = 2869133) B2869133
theorem B4303709 : Blo 1911435 4303709 := bbase (se 3 (by rfl) ⟨806945, by rfl⟩ : syracuseStep 4303709 = 1613891) (by norm_num)
theorem B2869139 : Blo 1911435 2869139 := bstep (se 1 (by rfl) ⟨2151854, by rfl⟩ : syracuseStep 2869139 = 4303709) B4303709
theorem B1912759 : Blo 1911435 1912759 := bstep (se 1 (by rfl) ⟨1434569, by rfl⟩ : syracuseStep 1912759 = 2869139) B2869139
theorem B3227789 : Blo 1911435 3227789 := bbase (se 3 (by rfl) ⟨605210, by rfl⟩ : syracuseStep 3227789 = 1210421) (by norm_num)
theorem B2151859 : Blo 1911435 2151859 := bstep (se 1 (by rfl) ⟨1613894, by rfl⟩ : syracuseStep 2151859 = 3227789) B3227789
theorem B2869145 : Blo 1911435 2869145 := bstep (se 2 (by rfl) ⟨1075929, by rfl⟩ : syracuseStep 2869145 = 2151859) B2151859
theorem B1912763 : Blo 1911435 1912763 := bstep (se 1 (by rfl) ⟨1434572, by rfl⟩ : syracuseStep 1912763 = 2869145) B2869145
theorem B1938865 : Blo 1911435 1938865 := bbase (se 2 (by rfl) ⟨727074, by rfl⟩ : syracuseStep 1938865 = 1454149) (by norm_num)
theorem B2585153 : Blo 1911435 2585153 := bstep (se 2 (by rfl) ⟨969432, by rfl⟩ : syracuseStep 2585153 = 1938865) B1938865
theorem B6893741 : Blo 1911435 6893741 := bstep (se 3 (by rfl) ⟨1292576, by rfl⟩ : syracuseStep 6893741 = 2585153) B2585153
theorem B4595827 : Blo 1911435 4595827 := bstep (se 1 (by rfl) ⟨3446870, by rfl⟩ : syracuseStep 4595827 = 6893741) B6893741
theorem B6127769 : Blo 1911435 6127769 := bstep (se 2 (by rfl) ⟨2297913, by rfl⟩ : syracuseStep 6127769 = 4595827) B4595827
theorem B16340717 : Blo 1911435 16340717 := bstep (se 3 (by rfl) ⟨3063884, by rfl⟩ : syracuseStep 16340717 = 6127769) B6127769
theorem B10893811 : Blo 1911435 10893811 := bstep (se 1 (by rfl) ⟨8170358, by rfl⟩ : syracuseStep 10893811 = 16340717) B16340717
theorem B14525081 : Blo 1911435 14525081 := bstep (se 2 (by rfl) ⟨5446905, by rfl⟩ : syracuseStep 14525081 = 10893811) B10893811
theorem B9683387 : Blo 1911435 9683387 := bstep (se 1 (by rfl) ⟨7262540, by rfl⟩ : syracuseStep 9683387 = 14525081) B14525081
theorem B6455591 : Blo 1911435 6455591 := bstep (se 1 (by rfl) ⟨4841693, by rfl⟩ : syracuseStep 6455591 = 9683387) B9683387
theorem B4303727 : Blo 1911435 4303727 := bstep (se 1 (by rfl) ⟨3227795, by rfl⟩ : syracuseStep 4303727 = 6455591) B6455591
theorem B2869151 : Blo 1911435 2869151 := bstep (se 1 (by rfl) ⟨2151863, by rfl⟩ : syracuseStep 2869151 = 4303727) B4303727
theorem B1912767 : Blo 1911435 1912767 := bstep (se 1 (by rfl) ⟨1434575, by rfl⟩ : syracuseStep 1912767 = 2869151) B2869151
theorem B2869157 : Blo 1911435 2869157 := bbase (se 4 (by rfl) ⟨268983, by rfl⟩ : syracuseStep 2869157 = 537967) (by norm_num)
theorem B1912771 : Blo 1911435 1912771 := bstep (se 1 (by rfl) ⟨1434578, by rfl⟩ : syracuseStep 1912771 = 2869157) B2869157
theorem B2420857 : Blo 1911435 2420857 := bbase (se 2 (by rfl) ⟨907821, by rfl⟩ : syracuseStep 2420857 = 1815643) (by norm_num)
theorem B3227809 : Blo 1911435 3227809 := bstep (se 2 (by rfl) ⟨1210428, by rfl⟩ : syracuseStep 3227809 = 2420857) B2420857
theorem B4303745 : Blo 1911435 4303745 := bstep (se 2 (by rfl) ⟨1613904, by rfl⟩ : syracuseStep 4303745 = 3227809) B3227809
theorem B2869163 : Blo 1911435 2869163 := bstep (se 1 (by rfl) ⟨2151872, by rfl⟩ : syracuseStep 2869163 = 4303745) B4303745
theorem B1912775 : Blo 1911435 1912775 := bstep (se 1 (by rfl) ⟨1434581, by rfl⟩ : syracuseStep 1912775 = 2869163) B2869163
theorem B2151877 : Blo 1911435 2151877 := bbase (se 4 (by rfl) ⟨201738, by rfl⟩ : syracuseStep 2151877 = 403477) (by norm_num)
theorem B2869169 : Blo 1911435 2869169 := bstep (se 2 (by rfl) ⟨1075938, by rfl⟩ : syracuseStep 2869169 = 2151877) B2151877
theorem B1912779 : Blo 1911435 1912779 := bstep (se 1 (by rfl) ⟨1434584, by rfl⟩ : syracuseStep 1912779 = 2869169) B2869169
theorem B3631301 : Blo 1911435 3631301 := bbase (se 4 (by rfl) ⟨340434, by rfl⟩ : syracuseStep 3631301 = 680869) (by norm_num)
theorem B2420867 : Blo 1911435 2420867 := bstep (se 1 (by rfl) ⟨1815650, by rfl⟩ : syracuseStep 2420867 = 3631301) B3631301
theorem B6455645 : Blo 1911435 6455645 := bstep (se 3 (by rfl) ⟨1210433, by rfl⟩ : syracuseStep 6455645 = 2420867) B2420867
theorem B4303763 : Blo 1911435 4303763 := bstep (se 1 (by rfl) ⟨3227822, by rfl⟩ : syracuseStep 4303763 = 6455645) B6455645
theorem B2869175 : Blo 1911435 2869175 := bstep (se 1 (by rfl) ⟨2151881, by rfl⟩ : syracuseStep 2869175 = 4303763) B4303763
theorem B1912783 : Blo 1911435 1912783 := bstep (se 1 (by rfl) ⟨1434587, by rfl⟩ : syracuseStep 1912783 = 2869175) B2869175
theorem B2869181 : Blo 1911435 2869181 := bbase (se 3 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 2869181 = 1075943) (by norm_num)
theorem B1912787 : Blo 1911435 1912787 := bstep (se 1 (by rfl) ⟨1434590, by rfl⟩ : syracuseStep 1912787 = 2869181) B2869181
theorem B4303781 : Blo 1911435 4303781 := bbase (se 4 (by rfl) ⟨403479, by rfl⟩ : syracuseStep 4303781 = 806959) (by norm_num)
theorem B2869187 : Blo 1911435 2869187 := bstep (se 1 (by rfl) ⟨2151890, by rfl⟩ : syracuseStep 2869187 = 4303781) B4303781
theorem B1912791 : Blo 1911435 1912791 := bstep (se 1 (by rfl) ⟨1434593, by rfl⟩ : syracuseStep 1912791 = 2869187) B2869187
theorem B4841765 : Blo 1911435 4841765 := bbase (se 4 (by rfl) ⟨453915, by rfl⟩ : syracuseStep 4841765 = 907831) (by norm_num)
theorem B3227843 : Blo 1911435 3227843 := bstep (se 1 (by rfl) ⟨2420882, by rfl⟩ : syracuseStep 3227843 = 4841765) B4841765
theorem B2151895 : Blo 1911435 2151895 := bstep (se 1 (by rfl) ⟨1613921, by rfl⟩ : syracuseStep 2151895 = 3227843) B3227843
theorem B2869193 : Blo 1911435 2869193 := bstep (se 2 (by rfl) ⟨1075947, by rfl⟩ : syracuseStep 2869193 = 2151895) B2151895
theorem B1912795 : Blo 1911435 1912795 := bstep (se 1 (by rfl) ⟨1434596, by rfl⟩ : syracuseStep 1912795 = 2869193) B2869193
theorem B5446997 : Blo 1911435 5446997 := bbase (se 11 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 5446997 = 7979) (by norm_num)
theorem B3631331 : Blo 1911435 3631331 := bstep (se 1 (by rfl) ⟨2723498, by rfl⟩ : syracuseStep 3631331 = 5446997) B5446997
theorem B9683549 : Blo 1911435 9683549 := bstep (se 3 (by rfl) ⟨1815665, by rfl⟩ : syracuseStep 9683549 = 3631331) B3631331
theorem B6455699 : Blo 1911435 6455699 := bstep (se 1 (by rfl) ⟨4841774, by rfl⟩ : syracuseStep 6455699 = 9683549) B9683549
theorem B4303799 : Blo 1911435 4303799 := bstep (se 1 (by rfl) ⟨3227849, by rfl⟩ : syracuseStep 4303799 = 6455699) B6455699
theorem B2869199 : Blo 1911435 2869199 := bstep (se 1 (by rfl) ⟨2151899, by rfl⟩ : syracuseStep 2869199 = 4303799) B4303799
theorem B1912799 : Blo 1911435 1912799 := bstep (se 1 (by rfl) ⟨1434599, by rfl⟩ : syracuseStep 1912799 = 2869199) B2869199
theorem B2869205 : Blo 1911435 2869205 := bbase (se 7 (by rfl) ⟨33623, by rfl⟩ : syracuseStep 2869205 = 67247) (by norm_num)
theorem B1912803 : Blo 1911435 1912803 := bstep (se 1 (by rfl) ⟨1434602, by rfl⟩ : syracuseStep 1912803 = 2869205) B2869205
theorem B7262693 : Blo 1911435 7262693 := bbase (se 4 (by rfl) ⟨680877, by rfl⟩ : syracuseStep 7262693 = 1361755) (by norm_num)
theorem B4841795 : Blo 1911435 4841795 := bstep (se 1 (by rfl) ⟨3631346, by rfl⟩ : syracuseStep 4841795 = 7262693) B7262693
theorem B3227863 : Blo 1911435 3227863 := bstep (se 1 (by rfl) ⟨2420897, by rfl⟩ : syracuseStep 3227863 = 4841795) B4841795
theorem B4303817 : Blo 1911435 4303817 := bstep (se 2 (by rfl) ⟨1613931, by rfl⟩ : syracuseStep 4303817 = 3227863) B3227863
theorem B2869211 : Blo 1911435 2869211 := bstep (se 1 (by rfl) ⟨2151908, by rfl⟩ : syracuseStep 2869211 = 4303817) B4303817
theorem B1912807 : Blo 1911435 1912807 := bstep (se 1 (by rfl) ⟨1434605, by rfl⟩ : syracuseStep 1912807 = 2869211) B2869211
theorem B2151913 : Blo 1911435 2151913 := bbase (se 2 (by rfl) ⟨806967, by rfl⟩ : syracuseStep 2151913 = 1613935) (by norm_num)
theorem B2869217 : Blo 1911435 2869217 := bstep (se 2 (by rfl) ⟨1075956, by rfl⟩ : syracuseStep 2869217 = 2151913) B2151913
theorem B1912811 : Blo 1911435 1912811 := bstep (se 1 (by rfl) ⟨1434608, by rfl⟩ : syracuseStep 1912811 = 2869217) B2869217
theorem B2042641 : Blo 1911435 2042641 := bbase (se 2 (by rfl) ⟨765990, by rfl⟩ : syracuseStep 2042641 = 1531981) (by norm_num)
theorem B10894085 : Blo 1911435 10894085 := bstep (se 4 (by rfl) ⟨1021320, by rfl⟩ : syracuseStep 10894085 = 2042641) B2042641
theorem B7262723 : Blo 1911435 7262723 := bstep (se 1 (by rfl) ⟨5447042, by rfl⟩ : syracuseStep 7262723 = 10894085) B10894085
theorem B4841815 : Blo 1911435 4841815 := bstep (se 1 (by rfl) ⟨3631361, by rfl⟩ : syracuseStep 4841815 = 7262723) B7262723
theorem B6455753 : Blo 1911435 6455753 := bstep (se 2 (by rfl) ⟨2420907, by rfl⟩ : syracuseStep 6455753 = 4841815) B4841815
theorem B4303835 : Blo 1911435 4303835 := bstep (se 1 (by rfl) ⟨3227876, by rfl⟩ : syracuseStep 4303835 = 6455753) B6455753
theorem B2869223 : Blo 1911435 2869223 := bstep (se 1 (by rfl) ⟨2151917, by rfl⟩ : syracuseStep 2869223 = 4303835) B4303835
theorem B1912815 : Blo 1911435 1912815 := bstep (se 1 (by rfl) ⟨1434611, by rfl⟩ : syracuseStep 1912815 = 2869223) B2869223
theorem B2869229 : Blo 1911435 2869229 := bbase (se 3 (by rfl) ⟨537980, by rfl⟩ : syracuseStep 2869229 = 1075961) (by norm_num)
theorem B1912819 : Blo 1911435 1912819 := bstep (se 1 (by rfl) ⟨1434614, by rfl⟩ : syracuseStep 1912819 = 2869229) B2869229
theorem B4303853 : Blo 1911435 4303853 := bbase (se 3 (by rfl) ⟨806972, by rfl⟩ : syracuseStep 4303853 = 1613945) (by norm_num)
theorem B2869235 : Blo 1911435 2869235 := bstep (se 1 (by rfl) ⟨2151926, by rfl⟩ : syracuseStep 2869235 = 4303853) B4303853
theorem B1912823 : Blo 1911435 1912823 := bstep (se 1 (by rfl) ⟨1434617, by rfl⟩ : syracuseStep 1912823 = 2869235) B2869235
theorem B4085309 : Blo 1911435 4085309 := bbase (se 3 (by rfl) ⟨765995, by rfl⟩ : syracuseStep 4085309 = 1531991) (by norm_num)
theorem B2723539 : Blo 1911435 2723539 := bstep (se 1 (by rfl) ⟨2042654, by rfl⟩ : syracuseStep 2723539 = 4085309) B4085309
theorem B3631385 : Blo 1911435 3631385 := bstep (se 2 (by rfl) ⟨1361769, by rfl⟩ : syracuseStep 3631385 = 2723539) B2723539
theorem B2420923 : Blo 1911435 2420923 := bstep (se 1 (by rfl) ⟨1815692, by rfl⟩ : syracuseStep 2420923 = 3631385) B3631385
theorem B3227897 : Blo 1911435 3227897 := bstep (se 2 (by rfl) ⟨1210461, by rfl⟩ : syracuseStep 3227897 = 2420923) B2420923
theorem B2151931 : Blo 1911435 2151931 := bstep (se 1 (by rfl) ⟨1613948, by rfl⟩ : syracuseStep 2151931 = 3227897) B3227897
theorem B2869241 : Blo 1911435 2869241 := bstep (se 2 (by rfl) ⟨1075965, by rfl⟩ : syracuseStep 2869241 = 2151931) B2151931
theorem B1912827 : Blo 1911435 1912827 := bstep (se 1 (by rfl) ⟨1434620, by rfl⟩ : syracuseStep 1912827 = 2869241) B2869241
theorem B16564213 : Blo 1911435 16564213 := bbase (se 5 (by rfl) ⟨776447, by rfl⟩ : syracuseStep 16564213 = 1552895) (by norm_num)
theorem B22085617 : Blo 1911435 22085617 := bstep (se 2 (by rfl) ⟨8282106, by rfl⟩ : syracuseStep 22085617 = 16564213) B16564213
theorem B29447489 : Blo 1911435 29447489 := bstep (se 2 (by rfl) ⟨11042808, by rfl⟩ : syracuseStep 29447489 = 22085617) B22085617
theorem B78526637 : Blo 1911435 78526637 := bstep (se 3 (by rfl) ⟨14723744, by rfl⟩ : syracuseStep 78526637 = 29447489) B29447489
theorem B52351091 : Blo 1911435 52351091 := bstep (se 1 (by rfl) ⟨39263318, by rfl⟩ : syracuseStep 52351091 = 78526637) B78526637
theorem B34900727 : Blo 1911435 34900727 := bstep (se 1 (by rfl) ⟨26175545, by rfl⟩ : syracuseStep 34900727 = 52351091) B52351091
theorem B93068605 : Blo 1911435 93068605 := bstep (se 3 (by rfl) ⟨17450363, by rfl⟩ : syracuseStep 93068605 = 34900727) B34900727
theorem B124091473 : Blo 1911435 124091473 := bstep (se 2 (by rfl) ⟨46534302, by rfl⟩ : syracuseStep 124091473 = 93068605) B93068605
theorem B165455297 : Blo 1911435 165455297 := bstep (se 2 (by rfl) ⟨62045736, by rfl⟩ : syracuseStep 165455297 = 124091473) B124091473
theorem B110303531 : Blo 1911435 110303531 := bstep (se 1 (by rfl) ⟨82727648, by rfl⟩ : syracuseStep 110303531 = 165455297) B165455297
theorem B73535687 : Blo 1911435 73535687 := bstep (se 1 (by rfl) ⟨55151765, by rfl⟩ : syracuseStep 73535687 = 110303531) B110303531
theorem B49023791 : Blo 1911435 49023791 := bstep (se 1 (by rfl) ⟨36767843, by rfl⟩ : syracuseStep 49023791 = 73535687) B73535687
theorem B32682527 : Blo 1911435 32682527 := bstep (se 1 (by rfl) ⟨24511895, by rfl⟩ : syracuseStep 32682527 = 49023791) B49023791
theorem B21788351 : Blo 1911435 21788351 := bstep (se 1 (by rfl) ⟨16341263, by rfl⟩ : syracuseStep 21788351 = 32682527) B32682527
theorem B14525567 : Blo 1911435 14525567 := bstep (se 1 (by rfl) ⟨10894175, by rfl⟩ : syracuseStep 14525567 = 21788351) B21788351
theorem B9683711 : Blo 1911435 9683711 := bstep (se 1 (by rfl) ⟨7262783, by rfl⟩ : syracuseStep 9683711 = 14525567) B14525567
theorem B6455807 : Blo 1911435 6455807 := bstep (se 1 (by rfl) ⟨4841855, by rfl⟩ : syracuseStep 6455807 = 9683711) B9683711
theorem B4303871 : Blo 1911435 4303871 := bstep (se 1 (by rfl) ⟨3227903, by rfl⟩ : syracuseStep 4303871 = 6455807) B6455807
theorem B2869247 : Blo 1911435 2869247 := bstep (se 1 (by rfl) ⟨2151935, by rfl⟩ : syracuseStep 2869247 = 4303871) B4303871
theorem B1912831 : Blo 1911435 1912831 := bstep (se 1 (by rfl) ⟨1434623, by rfl⟩ : syracuseStep 1912831 = 2869247) B2869247
theorem B2869253 : Blo 1911435 2869253 := bbase (se 4 (by rfl) ⟨268992, by rfl⟩ : syracuseStep 2869253 = 537985) (by norm_num)
theorem B1912835 : Blo 1911435 1912835 := bstep (se 1 (by rfl) ⟨1434626, by rfl⟩ : syracuseStep 1912835 = 2869253) B2869253
theorem B3227917 : Blo 1911435 3227917 := bbase (se 3 (by rfl) ⟨605234, by rfl⟩ : syracuseStep 3227917 = 1210469) (by norm_num)
theorem B4303889 : Blo 1911435 4303889 := bstep (se 2 (by rfl) ⟨1613958, by rfl⟩ : syracuseStep 4303889 = 3227917) B3227917
theorem B2869259 : Blo 1911435 2869259 := bstep (se 1 (by rfl) ⟨2151944, by rfl⟩ : syracuseStep 2869259 = 4303889) B4303889
theorem B1912839 : Blo 1911435 1912839 := bstep (se 1 (by rfl) ⟨1434629, by rfl⟩ : syracuseStep 1912839 = 2869259) B2869259
theorem B2151949 : Blo 1911435 2151949 := bbase (se 3 (by rfl) ⟨403490, by rfl⟩ : syracuseStep 2151949 = 806981) (by norm_num)
theorem B2869265 : Blo 1911435 2869265 := bstep (se 2 (by rfl) ⟨1075974, by rfl⟩ : syracuseStep 2869265 = 2151949) B2151949
theorem B1912843 : Blo 1911435 1912843 := bstep (se 1 (by rfl) ⟨1434632, by rfl⟩ : syracuseStep 1912843 = 2869265) B2869265
theorem B6455861 : Blo 1911435 6455861 := bbase (se 5 (by rfl) ⟨302618, by rfl⟩ : syracuseStep 6455861 = 605237) (by norm_num)
theorem B4303907 : Blo 1911435 4303907 := bstep (se 1 (by rfl) ⟨3227930, by rfl⟩ : syracuseStep 4303907 = 6455861) B6455861
theorem B2869271 : Blo 1911435 2869271 := bstep (se 1 (by rfl) ⟨2151953, by rfl⟩ : syracuseStep 2869271 = 4303907) B4303907
theorem B1912847 : Blo 1911435 1912847 := bstep (se 1 (by rfl) ⟨1434635, by rfl⟩ : syracuseStep 1912847 = 2869271) B2869271
theorem B2869277 : Blo 1911435 2869277 := bbase (se 3 (by rfl) ⟨537989, by rfl⟩ : syracuseStep 2869277 = 1075979) (by norm_num)
theorem B1912851 : Blo 1911435 1912851 := bstep (se 1 (by rfl) ⟨1434638, by rfl⟩ : syracuseStep 1912851 = 2869277) B2869277
theorem B4303925 : Blo 1911435 4303925 := bbase (se 5 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 4303925 = 403493) (by norm_num)
theorem B2869283 : Blo 1911435 2869283 := bstep (se 1 (by rfl) ⟨2151962, by rfl⟩ : syracuseStep 2869283 = 4303925) B4303925
theorem B1912855 : Blo 1911435 1912855 := bstep (se 1 (by rfl) ⟨1434641, by rfl⟩ : syracuseStep 1912855 = 2869283) B2869283
theorem B3447037 : Blo 1911435 3447037 := bbase (se 3 (by rfl) ⟨646319, by rfl⟩ : syracuseStep 3447037 = 1292639) (by norm_num)
theorem B4596049 : Blo 1911435 4596049 := bstep (se 2 (by rfl) ⟨1723518, by rfl⟩ : syracuseStep 4596049 = 3447037) B3447037
theorem B6128065 : Blo 1911435 6128065 := bstep (se 2 (by rfl) ⟨2298024, by rfl⟩ : syracuseStep 6128065 = 4596049) B4596049
theorem B8170753 : Blo 1911435 8170753 := bstep (se 2 (by rfl) ⟨3064032, by rfl⟩ : syracuseStep 8170753 = 6128065) B6128065
theorem B10894337 : Blo 1911435 10894337 := bstep (se 2 (by rfl) ⟨4085376, by rfl⟩ : syracuseStep 10894337 = 8170753) B8170753
theorem B7262891 : Blo 1911435 7262891 := bstep (se 1 (by rfl) ⟨5447168, by rfl⟩ : syracuseStep 7262891 = 10894337) B10894337
theorem B4841927 : Blo 1911435 4841927 := bstep (se 1 (by rfl) ⟨3631445, by rfl⟩ : syracuseStep 4841927 = 7262891) B7262891
theorem B3227951 : Blo 1911435 3227951 := bstep (se 1 (by rfl) ⟨2420963, by rfl⟩ : syracuseStep 3227951 = 4841927) B4841927
theorem B2151967 : Blo 1911435 2151967 := bstep (se 1 (by rfl) ⟨1613975, by rfl⟩ : syracuseStep 2151967 = 3227951) B3227951
theorem B2869289 : Blo 1911435 2869289 := bstep (se 2 (by rfl) ⟨1075983, by rfl⟩ : syracuseStep 2869289 = 2151967) B2151967
theorem B1912859 : Blo 1911435 1912859 := bstep (se 1 (by rfl) ⟨1434644, by rfl⟩ : syracuseStep 1912859 = 2869289) B2869289
theorem B2298029 : Blo 1911435 2298029 := bbase (se 3 (by rfl) ⟨430880, by rfl⟩ : syracuseStep 2298029 = 861761) (by norm_num)
theorem B6128077 : Blo 1911435 6128077 := bstep (se 3 (by rfl) ⟨1149014, by rfl⟩ : syracuseStep 6128077 = 2298029) B2298029
theorem B8170769 : Blo 1911435 8170769 := bstep (se 2 (by rfl) ⟨3064038, by rfl⟩ : syracuseStep 8170769 = 6128077) B6128077
theorem B5447179 : Blo 1911435 5447179 := bstep (se 1 (by rfl) ⟨4085384, by rfl⟩ : syracuseStep 5447179 = 8170769) B8170769
theorem B7262905 : Blo 1911435 7262905 := bstep (se 2 (by rfl) ⟨2723589, by rfl⟩ : syracuseStep 7262905 = 5447179) B5447179
theorem B9683873 : Blo 1911435 9683873 := bstep (se 2 (by rfl) ⟨3631452, by rfl⟩ : syracuseStep 9683873 = 7262905) B7262905
theorem B6455915 : Blo 1911435 6455915 := bstep (se 1 (by rfl) ⟨4841936, by rfl⟩ : syracuseStep 6455915 = 9683873) B9683873
theorem B4303943 : Blo 1911435 4303943 := bstep (se 1 (by rfl) ⟨3227957, by rfl⟩ : syracuseStep 4303943 = 6455915) B6455915
theorem B2869295 : Blo 1911435 2869295 := bstep (se 1 (by rfl) ⟨2151971, by rfl⟩ : syracuseStep 2869295 = 4303943) B4303943
theorem B1912863 : Blo 1911435 1912863 := bstep (se 1 (by rfl) ⟨1434647, by rfl⟩ : syracuseStep 1912863 = 2869295) B2869295
theorem B2869301 : Blo 1911435 2869301 := bbase (se 5 (by rfl) ⟨134498, by rfl⟩ : syracuseStep 2869301 = 268997) (by norm_num)
theorem B1912867 : Blo 1911435 1912867 := bstep (se 1 (by rfl) ⟨1434650, by rfl⟩ : syracuseStep 1912867 = 2869301) B2869301
theorem B4841957 : Blo 1911435 4841957 := bbase (se 4 (by rfl) ⟨453933, by rfl⟩ : syracuseStep 4841957 = 907867) (by norm_num)
theorem B3227971 : Blo 1911435 3227971 := bstep (se 1 (by rfl) ⟨2420978, by rfl⟩ : syracuseStep 3227971 = 4841957) B4841957
theorem B4303961 : Blo 1911435 4303961 := bstep (se 2 (by rfl) ⟨1613985, by rfl⟩ : syracuseStep 4303961 = 3227971) B3227971
theorem B2869307 : Blo 1911435 2869307 := bstep (se 1 (by rfl) ⟨2151980, by rfl⟩ : syracuseStep 2869307 = 4303961) B4303961
theorem B1912871 : Blo 1911435 1912871 := bstep (se 1 (by rfl) ⟨1434653, by rfl⟩ : syracuseStep 1912871 = 2869307) B2869307
theorem B2151985 : Blo 1911435 2151985 := bbase (se 2 (by rfl) ⟨806994, by rfl⟩ : syracuseStep 2151985 = 1613989) (by norm_num)
theorem B2869313 : Blo 1911435 2869313 := bstep (se 2 (by rfl) ⟨1075992, by rfl⟩ : syracuseStep 2869313 = 2151985) B2151985
theorem B1912875 : Blo 1911435 1912875 := bstep (se 1 (by rfl) ⟨1434656, by rfl⟩ : syracuseStep 1912875 = 2869313) B2869313
theorem B2908469 : Blo 1911435 2908469 := bbase (se 5 (by rfl) ⟨136334, by rfl⟩ : syracuseStep 2908469 = 272669) (by norm_num)
theorem B1938979 : Blo 1911435 1938979 := bstep (se 1 (by rfl) ⟨1454234, by rfl⟩ : syracuseStep 1938979 = 2908469) B2908469
theorem B2585305 : Blo 1911435 2585305 := bstep (se 2 (by rfl) ⟨969489, by rfl⟩ : syracuseStep 2585305 = 1938979) B1938979
theorem B3447073 : Blo 1911435 3447073 := bstep (se 2 (by rfl) ⟨1292652, by rfl⟩ : syracuseStep 3447073 = 2585305) B2585305
theorem B4596097 : Blo 1911435 4596097 := bstep (se 2 (by rfl) ⟨1723536, by rfl⟩ : syracuseStep 4596097 = 3447073) B3447073
theorem B6128129 : Blo 1911435 6128129 := bstep (se 2 (by rfl) ⟨2298048, by rfl⟩ : syracuseStep 6128129 = 4596097) B4596097
theorem B4085419 : Blo 1911435 4085419 := bstep (se 1 (by rfl) ⟨3064064, by rfl⟩ : syracuseStep 4085419 = 6128129) B6128129
theorem B5447225 : Blo 1911435 5447225 := bstep (se 2 (by rfl) ⟨2042709, by rfl⟩ : syracuseStep 5447225 = 4085419) B4085419
theorem B3631483 : Blo 1911435 3631483 := bstep (se 1 (by rfl) ⟨2723612, by rfl⟩ : syracuseStep 3631483 = 5447225) B5447225
theorem B4841977 : Blo 1911435 4841977 := bstep (se 2 (by rfl) ⟨1815741, by rfl⟩ : syracuseStep 4841977 = 3631483) B3631483
theorem B6455969 : Blo 1911435 6455969 := bstep (se 2 (by rfl) ⟨2420988, by rfl⟩ : syracuseStep 6455969 = 4841977) B4841977
theorem B4303979 : Blo 1911435 4303979 := bstep (se 1 (by rfl) ⟨3227984, by rfl⟩ : syracuseStep 4303979 = 6455969) B6455969
theorem B2869319 : Blo 1911435 2869319 := bstep (se 1 (by rfl) ⟨2151989, by rfl⟩ : syracuseStep 2869319 = 4303979) B4303979
theorem B1912879 : Blo 1911435 1912879 := bstep (se 1 (by rfl) ⟨1434659, by rfl⟩ : syracuseStep 1912879 = 2869319) B2869319
theorem B2869325 : Blo 1911435 2869325 := bbase (se 3 (by rfl) ⟨537998, by rfl⟩ : syracuseStep 2869325 = 1075997) (by norm_num)
theorem B1912883 : Blo 1911435 1912883 := bstep (se 1 (by rfl) ⟨1434662, by rfl⟩ : syracuseStep 1912883 = 2869325) B2869325
theorem B4303997 : Blo 1911435 4303997 := bbase (se 3 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 4303997 = 1613999) (by norm_num)
theorem B2869331 : Blo 1911435 2869331 := bstep (se 1 (by rfl) ⟨2151998, by rfl⟩ : syracuseStep 2869331 = 4303997) B4303997
theorem B1912887 : Blo 1911435 1912887 := bstep (se 1 (by rfl) ⟨1434665, by rfl⟩ : syracuseStep 1912887 = 2869331) B2869331
theorem B3228005 : Blo 1911435 3228005 := bbase (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) (by norm_num)
theorem B2152003 : Blo 1911435 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B2869337 : Blo 1911435 2869337 := bstep (se 2 (by rfl) ⟨1076001, by rfl⟩ : syracuseStep 2869337 = 2152003) B2152003
theorem B1912891 : Blo 1911435 1912891 := bstep (se 1 (by rfl) ⟨1434668, by rfl⟩ : syracuseStep 1912891 = 2869337) B2869337
theorem B4085453 : Blo 1911435 4085453 := bbase (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) (by norm_num)
theorem B2723635 : Blo 1911435 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B14526053 : Blo 1911435 14526053 := bstep (se 4 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 14526053 = 2723635) B2723635
theorem B9684035 : Blo 1911435 9684035 := bstep (se 1 (by rfl) ⟨7263026, by rfl⟩ : syracuseStep 9684035 = 14526053) B14526053
theorem B6456023 : Blo 1911435 6456023 := bstep (se 1 (by rfl) ⟨4842017, by rfl⟩ : syracuseStep 6456023 = 9684035) B9684035
theorem B4304015 : Blo 1911435 4304015 := bstep (se 1 (by rfl) ⟨3228011, by rfl⟩ : syracuseStep 4304015 = 6456023) B6456023
theorem B2869343 : Blo 1911435 2869343 := bstep (se 1 (by rfl) ⟨2152007, by rfl⟩ : syracuseStep 2869343 = 4304015) B4304015
theorem B1912895 : Blo 1911435 1912895 := bstep (se 1 (by rfl) ⟨1434671, by rfl⟩ : syracuseStep 1912895 = 2869343) B2869343
theorem B2869349 : Blo 1911435 2869349 := bbase (se 4 (by rfl) ⟨269001, by rfl⟩ : syracuseStep 2869349 = 538003) (by norm_num)
theorem B1912899 : Blo 1911435 1912899 := bstep (se 1 (by rfl) ⟨1434674, by rfl⟩ : syracuseStep 1912899 = 2869349) B2869349
theorem B3272069 : Blo 1911435 3272069 := bbase (se 4 (by rfl) ⟨306756, by rfl⟩ : syracuseStep 3272069 = 613513) (by norm_num)
theorem B2181379 : Blo 1911435 2181379 := bstep (se 1 (by rfl) ⟨1636034, by rfl⟩ : syracuseStep 2181379 = 3272069) B3272069
theorem B2908505 : Blo 1911435 2908505 := bstep (se 2 (by rfl) ⟨1090689, by rfl⟩ : syracuseStep 2908505 = 2181379) B2181379
theorem B7756013 : Blo 1911435 7756013 := bstep (se 3 (by rfl) ⟨1454252, by rfl⟩ : syracuseStep 7756013 = 2908505) B2908505
theorem B20682701 : Blo 1911435 20682701 := bstep (se 3 (by rfl) ⟨3878006, by rfl⟩ : syracuseStep 20682701 = 7756013) B7756013
theorem B13788467 : Blo 1911435 13788467 := bstep (se 1 (by rfl) ⟨10341350, by rfl⟩ : syracuseStep 13788467 = 20682701) B20682701
theorem B9192311 : Blo 1911435 9192311 := bstep (se 1 (by rfl) ⟨6894233, by rfl⟩ : syracuseStep 9192311 = 13788467) B13788467
theorem B6128207 : Blo 1911435 6128207 := bstep (se 1 (by rfl) ⟨4596155, by rfl⟩ : syracuseStep 6128207 = 9192311) B9192311
theorem B4085471 : Blo 1911435 4085471 := bstep (se 1 (by rfl) ⟨3064103, by rfl⟩ : syracuseStep 4085471 = 6128207) B6128207
theorem B2723647 : Blo 1911435 2723647 := bstep (se 1 (by rfl) ⟨2042735, by rfl⟩ : syracuseStep 2723647 = 4085471) B4085471
theorem B3631529 : Blo 1911435 3631529 := bstep (se 2 (by rfl) ⟨1361823, by rfl⟩ : syracuseStep 3631529 = 2723647) B2723647
theorem B2421019 : Blo 1911435 2421019 := bstep (se 1 (by rfl) ⟨1815764, by rfl⟩ : syracuseStep 2421019 = 3631529) B3631529
theorem B3228025 : Blo 1911435 3228025 := bstep (se 2 (by rfl) ⟨1210509, by rfl⟩ : syracuseStep 3228025 = 2421019) B2421019
theorem B4304033 : Blo 1911435 4304033 := bstep (se 2 (by rfl) ⟨1614012, by rfl⟩ : syracuseStep 4304033 = 3228025) B3228025
theorem B2869355 : Blo 1911435 2869355 := bstep (se 1 (by rfl) ⟨2152016, by rfl⟩ : syracuseStep 2869355 = 4304033) B4304033
theorem B1912903 : Blo 1911435 1912903 := bstep (se 1 (by rfl) ⟨1434677, by rfl⟩ : syracuseStep 1912903 = 2869355) B2869355
theorem B2152021 : Blo 1911435 2152021 := bbase (se 8 (by rfl) ⟨12609, by rfl⟩ : syracuseStep 2152021 = 25219) (by norm_num)
theorem B2869361 : Blo 1911435 2869361 := bstep (se 2 (by rfl) ⟨1076010, by rfl⟩ : syracuseStep 2869361 = 2152021) B2152021
theorem B1912907 : Blo 1911435 1912907 := bstep (se 1 (by rfl) ⟨1434680, by rfl⟩ : syracuseStep 1912907 = 2869361) B2869361
theorem B2421029 : Blo 1911435 2421029 := bbase (se 4 (by rfl) ⟨226971, by rfl⟩ : syracuseStep 2421029 = 453943) (by norm_num)
theorem B6456077 : Blo 1911435 6456077 := bstep (se 3 (by rfl) ⟨1210514, by rfl⟩ : syracuseStep 6456077 = 2421029) B2421029
theorem B4304051 : Blo 1911435 4304051 := bstep (se 1 (by rfl) ⟨3228038, by rfl⟩ : syracuseStep 4304051 = 6456077) B6456077
theorem B2869367 : Blo 1911435 2869367 := bstep (se 1 (by rfl) ⟨2152025, by rfl⟩ : syracuseStep 2869367 = 4304051) B4304051
theorem B1912911 : Blo 1911435 1912911 := bstep (se 1 (by rfl) ⟨1434683, by rfl⟩ : syracuseStep 1912911 = 2869367) B2869367
theorem B2869373 : Blo 1911435 2869373 := bbase (se 3 (by rfl) ⟨538007, by rfl⟩ : syracuseStep 2869373 = 1076015) (by norm_num)
theorem B1912915 : Blo 1911435 1912915 := bstep (se 1 (by rfl) ⟨1434686, by rfl⟩ : syracuseStep 1912915 = 2869373) B2869373
theorem B4304069 : Blo 1911435 4304069 := bbase (se 4 (by rfl) ⟨403506, by rfl⟩ : syracuseStep 4304069 = 807013) (by norm_num)
theorem B2869379 : Blo 1911435 2869379 := bstep (se 1 (by rfl) ⟨2152034, by rfl⟩ : syracuseStep 2869379 = 4304069) B4304069
theorem B1912919 : Blo 1911435 1912919 := bstep (se 1 (by rfl) ⟨1434689, by rfl⟩ : syracuseStep 1912919 = 2869379) B2869379
theorem B9087653 : Blo 1911435 9087653 := bbase (se 4 (by rfl) ⟨851967, by rfl⟩ : syracuseStep 9087653 = 1703935) (by norm_num)
theorem B6058435 : Blo 1911435 6058435 := bstep (se 1 (by rfl) ⟨4543826, by rfl⟩ : syracuseStep 6058435 = 9087653) B9087653
theorem B8077913 : Blo 1911435 8077913 := bstep (se 2 (by rfl) ⟨3029217, by rfl⟩ : syracuseStep 8077913 = 6058435) B6058435
theorem B5385275 : Blo 1911435 5385275 := bstep (se 1 (by rfl) ⟨4038956, by rfl⟩ : syracuseStep 5385275 = 8077913) B8077913
theorem B3590183 : Blo 1911435 3590183 := bstep (se 1 (by rfl) ⟨2692637, by rfl⟩ : syracuseStep 3590183 = 5385275) B5385275
theorem B9573821 : Blo 1911435 9573821 := bstep (se 3 (by rfl) ⟨1795091, by rfl⟩ : syracuseStep 9573821 = 3590183) B3590183
theorem B6382547 : Blo 1911435 6382547 := bstep (se 1 (by rfl) ⟨4786910, by rfl⟩ : syracuseStep 6382547 = 9573821) B9573821
theorem B4255031 : Blo 1911435 4255031 := bstep (se 1 (by rfl) ⟨3191273, by rfl⟩ : syracuseStep 4255031 = 6382547) B6382547
theorem B11346749 : Blo 1911435 11346749 := bstep (se 3 (by rfl) ⟨2127515, by rfl⟩ : syracuseStep 11346749 = 4255031) B4255031
theorem B7564499 : Blo 1911435 7564499 := bstep (se 1 (by rfl) ⟨5673374, by rfl⟩ : syracuseStep 7564499 = 11346749) B11346749
theorem B5042999 : Blo 1911435 5042999 := bstep (se 1 (by rfl) ⟨3782249, by rfl⟩ : syracuseStep 5042999 = 7564499) B7564499
theorem B3361999 : Blo 1911435 3361999 := bstep (se 1 (by rfl) ⟨2521499, by rfl⟩ : syracuseStep 3361999 = 5042999) B5042999
theorem B4482665 : Blo 1911435 4482665 := bstep (se 2 (by rfl) ⟨1680999, by rfl⟩ : syracuseStep 4482665 = 3361999) B3361999
theorem B2988443 : Blo 1911435 2988443 := bstep (se 1 (by rfl) ⟨2241332, by rfl⟩ : syracuseStep 2988443 = 4482665) B4482665
theorem B1992295 : Blo 1911435 1992295 := bstep (se 1 (by rfl) ⟨1494221, by rfl⟩ : syracuseStep 1992295 = 2988443) B2988443
theorem B10625573 : Blo 1911435 10625573 := bstep (se 4 (by rfl) ⟨996147, by rfl⟩ : syracuseStep 10625573 = 1992295) B1992295
theorem B7083715 : Blo 1911435 7083715 := bstep (se 1 (by rfl) ⟨5312786, by rfl⟩ : syracuseStep 7083715 = 10625573) B10625573
theorem B9444953 : Blo 1911435 9444953 := bstep (se 2 (by rfl) ⟨3541857, by rfl⟩ : syracuseStep 9444953 = 7083715) B7083715
theorem B6296635 : Blo 1911435 6296635 := bstep (se 1 (by rfl) ⟨4722476, by rfl⟩ : syracuseStep 6296635 = 9444953) B9444953
theorem B33582053 : Blo 1911435 33582053 := bstep (se 4 (by rfl) ⟨3148317, by rfl⟩ : syracuseStep 33582053 = 6296635) B6296635
theorem B22388035 : Blo 1911435 22388035 := bstep (se 1 (by rfl) ⟨16791026, by rfl⟩ : syracuseStep 22388035 = 33582053) B33582053
theorem B29850713 : Blo 1911435 29850713 := bstep (se 2 (by rfl) ⟨11194017, by rfl⟩ : syracuseStep 29850713 = 22388035) B22388035
theorem B19900475 : Blo 1911435 19900475 := bstep (se 1 (by rfl) ⟨14925356, by rfl⟩ : syracuseStep 19900475 = 29850713) B29850713
theorem B13266983 : Blo 1911435 13266983 := bstep (se 1 (by rfl) ⟨9950237, by rfl⟩ : syracuseStep 13266983 = 19900475) B19900475
theorem B8844655 : Blo 1911435 8844655 := bstep (se 1 (by rfl) ⟨6633491, by rfl⟩ : syracuseStep 8844655 = 13266983) B13266983
theorem B11792873 : Blo 1911435 11792873 := bstep (se 2 (by rfl) ⟨4422327, by rfl⟩ : syracuseStep 11792873 = 8844655) B8844655
theorem B7861915 : Blo 1911435 7861915 := bstep (se 1 (by rfl) ⟨5896436, by rfl⟩ : syracuseStep 7861915 = 11792873) B11792873
theorem B10482553 : Blo 1911435 10482553 := bstep (se 2 (by rfl) ⟨3930957, by rfl⟩ : syracuseStep 10482553 = 7861915) B7861915
theorem B55906949 : Blo 1911435 55906949 := bstep (se 4 (by rfl) ⟨5241276, by rfl⟩ : syracuseStep 55906949 = 10482553) B10482553
theorem B37271299 : Blo 1911435 37271299 := bstep (se 1 (by rfl) ⟨27953474, by rfl⟩ : syracuseStep 37271299 = 55906949) B55906949
theorem B49695065 : Blo 1911435 49695065 := bstep (se 2 (by rfl) ⟨18635649, by rfl⟩ : syracuseStep 49695065 = 37271299) B37271299
theorem B33130043 : Blo 1911435 33130043 := bstep (se 1 (by rfl) ⟨24847532, by rfl⟩ : syracuseStep 33130043 = 49695065) B49695065
theorem B22086695 : Blo 1911435 22086695 := bstep (se 1 (by rfl) ⟨16565021, by rfl⟩ : syracuseStep 22086695 = 33130043) B33130043
theorem B14724463 : Blo 1911435 14724463 := bstep (se 1 (by rfl) ⟨11043347, by rfl⟩ : syracuseStep 14724463 = 22086695) B22086695
theorem B19632617 : Blo 1911435 19632617 := bstep (se 2 (by rfl) ⟨7362231, by rfl⟩ : syracuseStep 19632617 = 14724463) B14724463
theorem B13088411 : Blo 1911435 13088411 := bstep (se 1 (by rfl) ⟨9816308, by rfl⟩ : syracuseStep 13088411 = 19632617) B19632617
theorem B8725607 : Blo 1911435 8725607 := bstep (se 1 (by rfl) ⟨6544205, by rfl⟩ : syracuseStep 8725607 = 13088411) B13088411
theorem B5817071 : Blo 1911435 5817071 := bstep (se 1 (by rfl) ⟨4362803, by rfl⟩ : syracuseStep 5817071 = 8725607) B8725607
theorem B3878047 : Blo 1911435 3878047 := bstep (se 1 (by rfl) ⟨2908535, by rfl⟩ : syracuseStep 3878047 = 5817071) B5817071
theorem B5170729 : Blo 1911435 5170729 := bstep (se 2 (by rfl) ⟨1939023, by rfl⟩ : syracuseStep 5170729 = 3878047) B3878047
theorem B6894305 : Blo 1911435 6894305 := bstep (se 2 (by rfl) ⟨2585364, by rfl⟩ : syracuseStep 6894305 = 5170729) B5170729
theorem B4596203 : Blo 1911435 4596203 := bstep (se 1 (by rfl) ⟨3447152, by rfl⟩ : syracuseStep 4596203 = 6894305) B6894305
theorem B12256541 : Blo 1911435 12256541 := bstep (se 3 (by rfl) ⟨2298101, by rfl⟩ : syracuseStep 12256541 = 4596203) B4596203
theorem B8171027 : Blo 1911435 8171027 := bstep (se 1 (by rfl) ⟨6128270, by rfl⟩ : syracuseStep 8171027 = 12256541) B12256541
theorem B5447351 : Blo 1911435 5447351 := bstep (se 1 (by rfl) ⟨4085513, by rfl⟩ : syracuseStep 5447351 = 8171027) B8171027
theorem B3631567 : Blo 1911435 3631567 := bstep (se 1 (by rfl) ⟨2723675, by rfl⟩ : syracuseStep 3631567 = 5447351) B5447351
theorem B4842089 : Blo 1911435 4842089 := bstep (se 2 (by rfl) ⟨1815783, by rfl⟩ : syracuseStep 4842089 = 3631567) B3631567
theorem B3228059 : Blo 1911435 3228059 := bstep (se 1 (by rfl) ⟨2421044, by rfl⟩ : syracuseStep 3228059 = 4842089) B4842089
theorem B2152039 : Blo 1911435 2152039 := bstep (se 1 (by rfl) ⟨1614029, by rfl⟩ : syracuseStep 2152039 = 3228059) B3228059
theorem B2869385 : Blo 1911435 2869385 := bstep (se 2 (by rfl) ⟨1076019, by rfl⟩ : syracuseStep 2869385 = 2152039) B2152039
theorem B1912923 : Blo 1911435 1912923 := bstep (se 1 (by rfl) ⟨1434692, by rfl⟩ : syracuseStep 1912923 = 2869385) B2869385
theorem B9684197 : Blo 1911435 9684197 := bbase (se 4 (by rfl) ⟨907893, by rfl⟩ : syracuseStep 9684197 = 1815787) (by norm_num)
theorem B6456131 : Blo 1911435 6456131 := bstep (se 1 (by rfl) ⟨4842098, by rfl⟩ : syracuseStep 6456131 = 9684197) B9684197
theorem B4304087 : Blo 1911435 4304087 := bstep (se 1 (by rfl) ⟨3228065, by rfl⟩ : syracuseStep 4304087 = 6456131) B6456131
theorem B2869391 : Blo 1911435 2869391 := bstep (se 1 (by rfl) ⟨2152043, by rfl⟩ : syracuseStep 2869391 = 4304087) B4304087
theorem B1912927 : Blo 1911435 1912927 := bstep (se 1 (by rfl) ⟨1434695, by rfl⟩ : syracuseStep 1912927 = 2869391) B2869391
theorem B2869397 : Blo 1911435 2869397 := bbase (se 6 (by rfl) ⟨67251, by rfl⟩ : syracuseStep 2869397 = 134503) (by norm_num)
theorem B1912931 : Blo 1911435 1912931 := bstep (se 1 (by rfl) ⟨1434698, by rfl⟩ : syracuseStep 1912931 = 2869397) B2869397
theorem B8171077 : Blo 1911435 8171077 := bbase (se 4 (by rfl) ⟨766038, by rfl⟩ : syracuseStep 8171077 = 1532077) (by norm_num)
theorem B10894769 : Blo 1911435 10894769 := bstep (se 2 (by rfl) ⟨4085538, by rfl⟩ : syracuseStep 10894769 = 8171077) B8171077
theorem B7263179 : Blo 1911435 7263179 := bstep (se 1 (by rfl) ⟨5447384, by rfl⟩ : syracuseStep 7263179 = 10894769) B10894769
theorem B4842119 : Blo 1911435 4842119 := bstep (se 1 (by rfl) ⟨3631589, by rfl⟩ : syracuseStep 4842119 = 7263179) B7263179
theorem B3228079 : Blo 1911435 3228079 := bstep (se 1 (by rfl) ⟨2421059, by rfl⟩ : syracuseStep 3228079 = 4842119) B4842119
theorem B4304105 : Blo 1911435 4304105 := bstep (se 2 (by rfl) ⟨1614039, by rfl⟩ : syracuseStep 4304105 = 3228079) B3228079
theorem B2869403 : Blo 1911435 2869403 := bstep (se 1 (by rfl) ⟨2152052, by rfl⟩ : syracuseStep 2869403 = 4304105) B4304105
theorem B1912935 : Blo 1911435 1912935 := bstep (se 1 (by rfl) ⟨1434701, by rfl⟩ : syracuseStep 1912935 = 2869403) B2869403
theorem B2152057 : Blo 1911435 2152057 := bbase (se 2 (by rfl) ⟨807021, by rfl⟩ : syracuseStep 2152057 = 1614043) (by norm_num)
theorem B2869409 : Blo 1911435 2869409 := bstep (se 2 (by rfl) ⟨1076028, by rfl⟩ : syracuseStep 2869409 = 2152057) B2152057
theorem B1912939 : Blo 1911435 1912939 := bstep (se 1 (by rfl) ⟨1434704, by rfl⟩ : syracuseStep 1912939 = 2869409) B2869409
theorem B3105973 : Blo 1911435 3105973 := bbase (se 5 (by rfl) ⟨145592, by rfl⟩ : syracuseStep 3105973 = 291185) (by norm_num)
theorem B4141297 : Blo 1911435 4141297 := bstep (se 2 (by rfl) ⟨1552986, by rfl⟩ : syracuseStep 4141297 = 3105973) B3105973
theorem B22086917 : Blo 1911435 22086917 := bstep (se 4 (by rfl) ⟨2070648, by rfl⟩ : syracuseStep 22086917 = 4141297) B4141297
theorem B14724611 : Blo 1911435 14724611 := bstep (se 1 (by rfl) ⟨11043458, by rfl⟩ : syracuseStep 14724611 = 22086917) B22086917
theorem B9816407 : Blo 1911435 9816407 := bstep (se 1 (by rfl) ⟨7362305, by rfl⟩ : syracuseStep 9816407 = 14724611) B14724611
theorem B6544271 : Blo 1911435 6544271 := bstep (se 1 (by rfl) ⟨4908203, by rfl⟩ : syracuseStep 6544271 = 9816407) B9816407
theorem B17451389 : Blo 1911435 17451389 := bstep (se 3 (by rfl) ⟨3272135, by rfl⟩ : syracuseStep 17451389 = 6544271) B6544271
theorem B46537037 : Blo 1911435 46537037 := bstep (se 3 (by rfl) ⟨8725694, by rfl⟩ : syracuseStep 46537037 = 17451389) B17451389
theorem B31024691 : Blo 1911435 31024691 := bstep (se 1 (by rfl) ⟨23268518, by rfl⟩ : syracuseStep 31024691 = 46537037) B46537037
theorem B20683127 : Blo 1911435 20683127 := bstep (se 1 (by rfl) ⟨15512345, by rfl⟩ : syracuseStep 20683127 = 31024691) B31024691
theorem B13788751 : Blo 1911435 13788751 := bstep (se 1 (by rfl) ⟨10341563, by rfl⟩ : syracuseStep 13788751 = 20683127) B20683127
theorem B18385001 : Blo 1911435 18385001 := bstep (se 2 (by rfl) ⟨6894375, by rfl⟩ : syracuseStep 18385001 = 13788751) B13788751
theorem B12256667 : Blo 1911435 12256667 := bstep (se 1 (by rfl) ⟨9192500, by rfl⟩ : syracuseStep 12256667 = 18385001) B18385001
theorem B8171111 : Blo 1911435 8171111 := bstep (se 1 (by rfl) ⟨6128333, by rfl⟩ : syracuseStep 8171111 = 12256667) B12256667
theorem B5447407 : Blo 1911435 5447407 := bstep (se 1 (by rfl) ⟨4085555, by rfl⟩ : syracuseStep 5447407 = 8171111) B8171111
theorem B7263209 : Blo 1911435 7263209 := bstep (se 2 (by rfl) ⟨2723703, by rfl⟩ : syracuseStep 7263209 = 5447407) B5447407
theorem B4842139 : Blo 1911435 4842139 := bstep (se 1 (by rfl) ⟨3631604, by rfl⟩ : syracuseStep 4842139 = 7263209) B7263209
theorem B6456185 : Blo 1911435 6456185 := bstep (se 2 (by rfl) ⟨2421069, by rfl⟩ : syracuseStep 6456185 = 4842139) B4842139
theorem B4304123 : Blo 1911435 4304123 := bstep (se 1 (by rfl) ⟨3228092, by rfl⟩ : syracuseStep 4304123 = 6456185) B6456185
theorem B2869415 : Blo 1911435 2869415 := bstep (se 1 (by rfl) ⟨2152061, by rfl⟩ : syracuseStep 2869415 = 4304123) B4304123
theorem B1912943 : Blo 1911435 1912943 := bstep (se 1 (by rfl) ⟨1434707, by rfl⟩ : syracuseStep 1912943 = 2869415) B2869415
theorem B2869421 : Blo 1911435 2869421 := bbase (se 3 (by rfl) ⟨538016, by rfl⟩ : syracuseStep 2869421 = 1076033) (by norm_num)
theorem B1912947 : Blo 1911435 1912947 := bstep (se 1 (by rfl) ⟨1434710, by rfl⟩ : syracuseStep 1912947 = 2869421) B2869421
theorem B4304141 : Blo 1911435 4304141 := bbase (se 3 (by rfl) ⟨807026, by rfl⟩ : syracuseStep 4304141 = 1614053) (by norm_num)
theorem B2869427 : Blo 1911435 2869427 := bstep (se 1 (by rfl) ⟨2152070, by rfl⟩ : syracuseStep 2869427 = 4304141) B4304141
theorem B1912951 : Blo 1911435 1912951 := bstep (se 1 (by rfl) ⟨1434713, by rfl⟩ : syracuseStep 1912951 = 2869427) B2869427
theorem B2421085 : Blo 1911435 2421085 := bbase (se 3 (by rfl) ⟨453953, by rfl⟩ : syracuseStep 2421085 = 907907) (by norm_num)
theorem B3228113 : Blo 1911435 3228113 := bstep (se 2 (by rfl) ⟨1210542, by rfl⟩ : syracuseStep 3228113 = 2421085) B2421085
theorem B2152075 : Blo 1911435 2152075 := bstep (se 1 (by rfl) ⟨1614056, by rfl⟩ : syracuseStep 2152075 = 3228113) B3228113
theorem B2869433 : Blo 1911435 2869433 := bstep (se 2 (by rfl) ⟨1076037, by rfl⟩ : syracuseStep 2869433 = 2152075) B2152075
theorem B1912955 : Blo 1911435 1912955 := bstep (se 1 (by rfl) ⟨1434716, by rfl⟩ : syracuseStep 1912955 = 2869433) B2869433
theorem B16342357 : Blo 1911435 16342357 := bbase (se 11 (by rfl) ⟨11969, by rfl⟩ : syracuseStep 16342357 = 23939) (by norm_num)
theorem B21789809 : Blo 1911435 21789809 := bstep (se 2 (by rfl) ⟨8171178, by rfl⟩ : syracuseStep 21789809 = 16342357) B16342357
theorem B14526539 : Blo 1911435 14526539 := bstep (se 1 (by rfl) ⟨10894904, by rfl⟩ : syracuseStep 14526539 = 21789809) B21789809
theorem B9684359 : Blo 1911435 9684359 := bstep (se 1 (by rfl) ⟨7263269, by rfl⟩ : syracuseStep 9684359 = 14526539) B14526539
theorem B6456239 : Blo 1911435 6456239 := bstep (se 1 (by rfl) ⟨4842179, by rfl⟩ : syracuseStep 6456239 = 9684359) B9684359
theorem B4304159 : Blo 1911435 4304159 := bstep (se 1 (by rfl) ⟨3228119, by rfl⟩ : syracuseStep 4304159 = 6456239) B6456239
theorem B2869439 : Blo 1911435 2869439 := bstep (se 1 (by rfl) ⟨2152079, by rfl⟩ : syracuseStep 2869439 = 4304159) B4304159
theorem B1912959 : Blo 1911435 1912959 := bstep (se 1 (by rfl) ⟨1434719, by rfl⟩ : syracuseStep 1912959 = 2869439) B2869439
theorem B2869445 : Blo 1911435 2869445 := bbase (se 4 (by rfl) ⟨269010, by rfl⟩ : syracuseStep 2869445 = 538021) (by norm_num)
theorem B1912963 : Blo 1911435 1912963 := bstep (se 1 (by rfl) ⟨1434722, by rfl⟩ : syracuseStep 1912963 = 2869445) B2869445
theorem B3228133 : Blo 1911435 3228133 := bbase (se 4 (by rfl) ⟨302637, by rfl⟩ : syracuseStep 3228133 = 605275) (by norm_num)
theorem B4304177 : Blo 1911435 4304177 := bstep (se 2 (by rfl) ⟨1614066, by rfl⟩ : syracuseStep 4304177 = 3228133) B3228133
theorem B2869451 : Blo 1911435 2869451 := bstep (se 1 (by rfl) ⟨2152088, by rfl⟩ : syracuseStep 2869451 = 4304177) B4304177
theorem B1912967 : Blo 1911435 1912967 := bstep (se 1 (by rfl) ⟨1434725, by rfl⟩ : syracuseStep 1912967 = 2869451) B2869451
theorem B2152093 : Blo 1911435 2152093 := bbase (se 3 (by rfl) ⟨403517, by rfl⟩ : syracuseStep 2152093 = 807035) (by norm_num)
theorem B2869457 : Blo 1911435 2869457 := bstep (se 2 (by rfl) ⟨1076046, by rfl⟩ : syracuseStep 2869457 = 2152093) B2152093
theorem B1912971 : Blo 1911435 1912971 := bstep (se 1 (by rfl) ⟨1434728, by rfl⟩ : syracuseStep 1912971 = 2869457) B2869457
theorem B6456293 : Blo 1911435 6456293 := bbase (se 4 (by rfl) ⟨605277, by rfl⟩ : syracuseStep 6456293 = 1210555) (by norm_num)
theorem B4304195 : Blo 1911435 4304195 := bstep (se 1 (by rfl) ⟨3228146, by rfl⟩ : syracuseStep 4304195 = 6456293) B6456293
theorem B2869463 : Blo 1911435 2869463 := bstep (se 1 (by rfl) ⟨2152097, by rfl⟩ : syracuseStep 2869463 = 4304195) B4304195
theorem B1912975 : Blo 1911435 1912975 := bstep (se 1 (by rfl) ⟨1434731, by rfl⟩ : syracuseStep 1912975 = 2869463) B2869463
theorem B2869469 : Blo 1911435 2869469 := bbase (se 3 (by rfl) ⟨538025, by rfl⟩ : syracuseStep 2869469 = 1076051) (by norm_num)
theorem B1912979 : Blo 1911435 1912979 := bstep (se 1 (by rfl) ⟨1434734, by rfl⟩ : syracuseStep 1912979 = 2869469) B2869469
theorem B4304213 : Blo 1911435 4304213 := bbase (se 11 (by rfl) ⟨3152, by rfl⟩ : syracuseStep 4304213 = 6305) (by norm_num)
theorem B2869475 : Blo 1911435 2869475 := bstep (se 1 (by rfl) ⟨2152106, by rfl⟩ : syracuseStep 2869475 = 4304213) B4304213
theorem B1912983 : Blo 1911435 1912983 := bstep (se 1 (by rfl) ⟨1434737, by rfl⟩ : syracuseStep 1912983 = 2869475) B2869475
theorem B2042825 : Blo 1911435 2042825 := bbase (se 2 (by rfl) ⟨766059, by rfl⟩ : syracuseStep 2042825 = 1532119) (by norm_num)
theorem B5447533 : Blo 1911435 5447533 := bstep (se 3 (by rfl) ⟨1021412, by rfl⟩ : syracuseStep 5447533 = 2042825) B2042825
theorem B7263377 : Blo 1911435 7263377 := bstep (se 2 (by rfl) ⟨2723766, by rfl⟩ : syracuseStep 7263377 = 5447533) B5447533
theorem B4842251 : Blo 1911435 4842251 := bstep (se 1 (by rfl) ⟨3631688, by rfl⟩ : syracuseStep 4842251 = 7263377) B7263377
theorem B3228167 : Blo 1911435 3228167 := bstep (se 1 (by rfl) ⟨2421125, by rfl⟩ : syracuseStep 3228167 = 4842251) B4842251
theorem B2152111 : Blo 1911435 2152111 := bstep (se 1 (by rfl) ⟨1614083, by rfl⟩ : syracuseStep 2152111 = 3228167) B3228167
theorem B2869481 : Blo 1911435 2869481 := bstep (se 2 (by rfl) ⟨1076055, by rfl⟩ : syracuseStep 2869481 = 2152111) B2152111
theorem B1912987 : Blo 1911435 1912987 := bstep (se 1 (by rfl) ⟨1434740, by rfl⟩ : syracuseStep 1912987 = 2869481) B2869481
theorem B44174933 : Blo 1911435 44174933 := bbase (se 8 (by rfl) ⟨258837, by rfl⟩ : syracuseStep 44174933 = 517675) (by norm_num)
theorem B29449955 : Blo 1911435 29449955 := bstep (se 1 (by rfl) ⟨22087466, by rfl⟩ : syracuseStep 29449955 = 44174933) B44174933
theorem B19633303 : Blo 1911435 19633303 := bstep (se 1 (by rfl) ⟨14724977, by rfl⟩ : syracuseStep 19633303 = 29449955) B29449955
theorem B26177737 : Blo 1911435 26177737 := bstep (se 2 (by rfl) ⟨9816651, by rfl⟩ : syracuseStep 26177737 = 19633303) B19633303
theorem B34903649 : Blo 1911435 34903649 := bstep (se 2 (by rfl) ⟨13088868, by rfl⟩ : syracuseStep 34903649 = 26177737) B26177737
theorem B93076397 : Blo 1911435 93076397 := bstep (se 3 (by rfl) ⟨17451824, by rfl⟩ : syracuseStep 93076397 = 34903649) B34903649
theorem B62050931 : Blo 1911435 62050931 := bstep (se 1 (by rfl) ⟨46538198, by rfl⟩ : syracuseStep 62050931 = 93076397) B93076397
theorem B41367287 : Blo 1911435 41367287 := bstep (se 1 (by rfl) ⟨31025465, by rfl⟩ : syracuseStep 41367287 = 62050931) B62050931
theorem B27578191 : Blo 1911435 27578191 := bstep (se 1 (by rfl) ⟨20683643, by rfl⟩ : syracuseStep 27578191 = 41367287) B41367287
theorem B36770921 : Blo 1911435 36770921 := bstep (se 2 (by rfl) ⟨13789095, by rfl⟩ : syracuseStep 36770921 = 27578191) B27578191
theorem B24513947 : Blo 1911435 24513947 := bstep (se 1 (by rfl) ⟨18385460, by rfl⟩ : syracuseStep 24513947 = 36770921) B36770921
theorem B16342631 : Blo 1911435 16342631 := bstep (se 1 (by rfl) ⟨12256973, by rfl⟩ : syracuseStep 16342631 = 24513947) B24513947
theorem B10895087 : Blo 1911435 10895087 := bstep (se 1 (by rfl) ⟨8171315, by rfl⟩ : syracuseStep 10895087 = 16342631) B16342631
theorem B7263391 : Blo 1911435 7263391 := bstep (se 1 (by rfl) ⟨5447543, by rfl⟩ : syracuseStep 7263391 = 10895087) B10895087
theorem B9684521 : Blo 1911435 9684521 := bstep (se 2 (by rfl) ⟨3631695, by rfl⟩ : syracuseStep 9684521 = 7263391) B7263391
theorem B6456347 : Blo 1911435 6456347 := bstep (se 1 (by rfl) ⟨4842260, by rfl⟩ : syracuseStep 6456347 = 9684521) B9684521
theorem B4304231 : Blo 1911435 4304231 := bstep (se 1 (by rfl) ⟨3228173, by rfl⟩ : syracuseStep 4304231 = 6456347) B6456347
theorem B2869487 : Blo 1911435 2869487 := bstep (se 1 (by rfl) ⟨2152115, by rfl⟩ : syracuseStep 2869487 = 4304231) B4304231
theorem B1912991 : Blo 1911435 1912991 := bstep (se 1 (by rfl) ⟨1434743, by rfl⟩ : syracuseStep 1912991 = 2869487) B2869487
theorem B2869493 : Blo 1911435 2869493 := bbase (se 5 (by rfl) ⟨134507, by rfl⟩ : syracuseStep 2869493 = 269015) (by norm_num)
theorem B1912995 : Blo 1911435 1912995 := bstep (se 1 (by rfl) ⟨1434746, by rfl⟩ : syracuseStep 1912995 = 2869493) B2869493
theorem B3148445 : Blo 1911435 3148445 := bbase (se 3 (by rfl) ⟨590333, by rfl⟩ : syracuseStep 3148445 = 1180667) (by norm_num)
theorem B2098963 : Blo 1911435 2098963 := bstep (se 1 (by rfl) ⟨1574222, by rfl⟩ : syracuseStep 2098963 = 3148445) B3148445
theorem B11194469 : Blo 1911435 11194469 := bstep (se 4 (by rfl) ⟨1049481, by rfl⟩ : syracuseStep 11194469 = 2098963) B2098963
theorem B7462979 : Blo 1911435 7462979 := bstep (se 1 (by rfl) ⟨5597234, by rfl⟩ : syracuseStep 7462979 = 11194469) B11194469
theorem B4975319 : Blo 1911435 4975319 := bstep (se 1 (by rfl) ⟨3731489, by rfl⟩ : syracuseStep 4975319 = 7462979) B7462979
theorem B3316879 : Blo 1911435 3316879 := bstep (se 1 (by rfl) ⟨2487659, by rfl⟩ : syracuseStep 3316879 = 4975319) B4975319
theorem B17690021 : Blo 1911435 17690021 := bstep (se 4 (by rfl) ⟨1658439, by rfl⟩ : syracuseStep 17690021 = 3316879) B3316879
theorem B11793347 : Blo 1911435 11793347 := bstep (se 1 (by rfl) ⟨8845010, by rfl⟩ : syracuseStep 11793347 = 17690021) B17690021
theorem B7862231 : Blo 1911435 7862231 := bstep (se 1 (by rfl) ⟨5896673, by rfl⟩ : syracuseStep 7862231 = 11793347) B11793347
theorem B20965949 : Blo 1911435 20965949 := bstep (se 3 (by rfl) ⟨3931115, by rfl⟩ : syracuseStep 20965949 = 7862231) B7862231
theorem B13977299 : Blo 1911435 13977299 := bstep (se 1 (by rfl) ⟨10482974, by rfl⟩ : syracuseStep 13977299 = 20965949) B20965949
theorem B9318199 : Blo 1911435 9318199 := bstep (se 1 (by rfl) ⟨6988649, by rfl⟩ : syracuseStep 9318199 = 13977299) B13977299
theorem B12424265 : Blo 1911435 12424265 := bstep (se 2 (by rfl) ⟨4659099, by rfl⟩ : syracuseStep 12424265 = 9318199) B9318199
theorem B8282843 : Blo 1911435 8282843 := bstep (se 1 (by rfl) ⟨6212132, by rfl⟩ : syracuseStep 8282843 = 12424265) B12424265
theorem B5521895 : Blo 1911435 5521895 := bstep (se 1 (by rfl) ⟨4141421, by rfl⟩ : syracuseStep 5521895 = 8282843) B8282843
theorem B3681263 : Blo 1911435 3681263 := bstep (se 1 (by rfl) ⟨2760947, by rfl⟩ : syracuseStep 3681263 = 5521895) B5521895
theorem B2454175 : Blo 1911435 2454175 := bstep (se 1 (by rfl) ⟨1840631, by rfl⟩ : syracuseStep 2454175 = 3681263) B3681263
theorem B3272233 : Blo 1911435 3272233 := bstep (se 2 (by rfl) ⟨1227087, by rfl⟩ : syracuseStep 3272233 = 2454175) B2454175
theorem B4362977 : Blo 1911435 4362977 := bstep (se 2 (by rfl) ⟨1636116, by rfl⟩ : syracuseStep 4362977 = 3272233) B3272233
theorem B2908651 : Blo 1911435 2908651 := bstep (se 1 (by rfl) ⟨2181488, by rfl⟩ : syracuseStep 2908651 = 4362977) B4362977
theorem B3878201 : Blo 1911435 3878201 := bstep (se 2 (by rfl) ⟨1454325, by rfl⟩ : syracuseStep 3878201 = 2908651) B2908651
theorem B2585467 : Blo 1911435 2585467 := bstep (se 1 (by rfl) ⟨1939100, by rfl⟩ : syracuseStep 2585467 = 3878201) B3878201
theorem B3447289 : Blo 1911435 3447289 := bstep (se 2 (by rfl) ⟨1292733, by rfl⟩ : syracuseStep 3447289 = 2585467) B2585467
theorem B18385541 : Blo 1911435 18385541 := bstep (se 4 (by rfl) ⟨1723644, by rfl⟩ : syracuseStep 18385541 = 3447289) B3447289
theorem B12257027 : Blo 1911435 12257027 := bstep (se 1 (by rfl) ⟨9192770, by rfl⟩ : syracuseStep 12257027 = 18385541) B18385541
theorem B8171351 : Blo 1911435 8171351 := bstep (se 1 (by rfl) ⟨6128513, by rfl⟩ : syracuseStep 8171351 = 12257027) B12257027
theorem B5447567 : Blo 1911435 5447567 := bstep (se 1 (by rfl) ⟨4085675, by rfl⟩ : syracuseStep 5447567 = 8171351) B8171351
theorem B3631711 : Blo 1911435 3631711 := bstep (se 1 (by rfl) ⟨2723783, by rfl⟩ : syracuseStep 3631711 = 5447567) B5447567
theorem B4842281 : Blo 1911435 4842281 := bstep (se 2 (by rfl) ⟨1815855, by rfl⟩ : syracuseStep 4842281 = 3631711) B3631711
theorem B3228187 : Blo 1911435 3228187 := bstep (se 1 (by rfl) ⟨2421140, by rfl⟩ : syracuseStep 3228187 = 4842281) B4842281
theorem B4304249 : Blo 1911435 4304249 := bstep (se 2 (by rfl) ⟨1614093, by rfl⟩ : syracuseStep 4304249 = 3228187) B3228187
theorem B2869499 : Blo 1911435 2869499 := bstep (se 1 (by rfl) ⟨2152124, by rfl⟩ : syracuseStep 2869499 = 4304249) B4304249
theorem B1912999 : Blo 1911435 1912999 := bstep (se 1 (by rfl) ⟨1434749, by rfl⟩ : syracuseStep 1912999 = 2869499) B2869499
theorem B2152129 : Blo 1911435 2152129 := bbase (se 2 (by rfl) ⟨807048, by rfl⟩ : syracuseStep 2152129 = 1614097) (by norm_num)
theorem B2869505 : Blo 1911435 2869505 := bstep (se 2 (by rfl) ⟨1076064, by rfl⟩ : syracuseStep 2869505 = 2152129) B2152129
theorem B1913003 : Blo 1911435 1913003 := bstep (se 1 (by rfl) ⟨1434752, by rfl⟩ : syracuseStep 1913003 = 2869505) B2869505
theorem B4842301 : Blo 1911435 4842301 := bbase (se 3 (by rfl) ⟨907931, by rfl⟩ : syracuseStep 4842301 = 1815863) (by norm_num)
theorem B6456401 : Blo 1911435 6456401 := bstep (se 2 (by rfl) ⟨2421150, by rfl⟩ : syracuseStep 6456401 = 4842301) B4842301
theorem B4304267 : Blo 1911435 4304267 := bstep (se 1 (by rfl) ⟨3228200, by rfl⟩ : syracuseStep 4304267 = 6456401) B6456401
theorem B2869511 : Blo 1911435 2869511 := bstep (se 1 (by rfl) ⟨2152133, by rfl⟩ : syracuseStep 2869511 = 4304267) B4304267
theorem B1913007 : Blo 1911435 1913007 := bstep (se 1 (by rfl) ⟨1434755, by rfl⟩ : syracuseStep 1913007 = 2869511) B2869511
theorem B2869517 : Blo 1911435 2869517 := bbase (se 3 (by rfl) ⟨538034, by rfl⟩ : syracuseStep 2869517 = 1076069) (by norm_num)
theorem B1913011 : Blo 1911435 1913011 := bstep (se 1 (by rfl) ⟨1434758, by rfl⟩ : syracuseStep 1913011 = 2869517) B2869517
theorem B4304285 : Blo 1911435 4304285 := bbase (se 3 (by rfl) ⟨807053, by rfl⟩ : syracuseStep 4304285 = 1614107) (by norm_num)
theorem B2869523 : Blo 1911435 2869523 := bstep (se 1 (by rfl) ⟨2152142, by rfl⟩ : syracuseStep 2869523 = 4304285) B4304285
theorem B1913015 : Blo 1911435 1913015 := bstep (se 1 (by rfl) ⟨1434761, by rfl⟩ : syracuseStep 1913015 = 2869523) B2869523
theorem B3228221 : Blo 1911435 3228221 := bbase (se 3 (by rfl) ⟨605291, by rfl⟩ : syracuseStep 3228221 = 1210583) (by norm_num)
theorem B2152147 : Blo 1911435 2152147 := bstep (se 1 (by rfl) ⟨1614110, by rfl⟩ : syracuseStep 2152147 = 3228221) B3228221
theorem B2869529 : Blo 1911435 2869529 := bstep (se 2 (by rfl) ⟨1076073, by rfl⟩ : syracuseStep 2869529 = 2152147) B2152147
theorem B1913019 : Blo 1911435 1913019 := bstep (se 1 (by rfl) ⟨1434764, by rfl⟩ : syracuseStep 1913019 = 2869529) B2869529
theorem B9816821 : Blo 1911435 9816821 := bbase (se 5 (by rfl) ⟨460163, by rfl⟩ : syracuseStep 9816821 = 920327) (by norm_num)
theorem B6544547 : Blo 1911435 6544547 := bstep (se 1 (by rfl) ⟨4908410, by rfl⟩ : syracuseStep 6544547 = 9816821) B9816821
theorem B4363031 : Blo 1911435 4363031 := bstep (se 1 (by rfl) ⟨3272273, by rfl⟩ : syracuseStep 4363031 = 6544547) B6544547
theorem B11634749 : Blo 1911435 11634749 := bstep (se 3 (by rfl) ⟨2181515, by rfl⟩ : syracuseStep 11634749 = 4363031) B4363031
theorem B7756499 : Blo 1911435 7756499 := bstep (se 1 (by rfl) ⟨5817374, by rfl⟩ : syracuseStep 7756499 = 11634749) B11634749
theorem B5170999 : Blo 1911435 5170999 := bstep (se 1 (by rfl) ⟨3878249, by rfl⟩ : syracuseStep 5170999 = 7756499) B7756499
theorem B6894665 : Blo 1911435 6894665 := bstep (se 2 (by rfl) ⟨2585499, by rfl⟩ : syracuseStep 6894665 = 5170999) B5170999
theorem B4596443 : Blo 1911435 4596443 := bstep (se 1 (by rfl) ⟨3447332, by rfl⟩ : syracuseStep 4596443 = 6894665) B6894665
theorem B3064295 : Blo 1911435 3064295 := bstep (se 1 (by rfl) ⟨2298221, by rfl⟩ : syracuseStep 3064295 = 4596443) B4596443
theorem B2042863 : Blo 1911435 2042863 := bstep (se 1 (by rfl) ⟨1532147, by rfl⟩ : syracuseStep 2042863 = 3064295) B3064295
theorem B10895269 : Blo 1911435 10895269 := bstep (se 4 (by rfl) ⟨1021431, by rfl⟩ : syracuseStep 10895269 = 2042863) B2042863
theorem B14527025 : Blo 1911435 14527025 := bstep (se 2 (by rfl) ⟨5447634, by rfl⟩ : syracuseStep 14527025 = 10895269) B10895269
theorem B9684683 : Blo 1911435 9684683 := bstep (se 1 (by rfl) ⟨7263512, by rfl⟩ : syracuseStep 9684683 = 14527025) B14527025
theorem B6456455 : Blo 1911435 6456455 := bstep (se 1 (by rfl) ⟨4842341, by rfl⟩ : syracuseStep 6456455 = 9684683) B9684683
theorem B4304303 : Blo 1911435 4304303 := bstep (se 1 (by rfl) ⟨3228227, by rfl⟩ : syracuseStep 4304303 = 6456455) B6456455
theorem B2869535 : Blo 1911435 2869535 := bstep (se 1 (by rfl) ⟨2152151, by rfl⟩ : syracuseStep 2869535 = 4304303) B4304303
theorem B1913023 : Blo 1911435 1913023 := bstep (se 1 (by rfl) ⟨1434767, by rfl⟩ : syracuseStep 1913023 = 2869535) B2869535
theorem B2869541 : Blo 1911435 2869541 := bbase (se 4 (by rfl) ⟨269019, by rfl⟩ : syracuseStep 2869541 = 538039) (by norm_num)
theorem B1913027 : Blo 1911435 1913027 := bstep (se 1 (by rfl) ⟨1434770, by rfl⟩ : syracuseStep 1913027 = 2869541) B2869541
theorem B2421181 : Blo 1911435 2421181 := bbase (se 3 (by rfl) ⟨453971, by rfl⟩ : syracuseStep 2421181 = 907943) (by norm_num)
theorem B3228241 : Blo 1911435 3228241 := bstep (se 2 (by rfl) ⟨1210590, by rfl⟩ : syracuseStep 3228241 = 2421181) B2421181
theorem B4304321 : Blo 1911435 4304321 := bstep (se 2 (by rfl) ⟨1614120, by rfl⟩ : syracuseStep 4304321 = 3228241) B3228241
theorem B2869547 : Blo 1911435 2869547 := bstep (se 1 (by rfl) ⟨2152160, by rfl⟩ : syracuseStep 2869547 = 4304321) B4304321
theorem B1913031 : Blo 1911435 1913031 := bstep (se 1 (by rfl) ⟨1434773, by rfl⟩ : syracuseStep 1913031 = 2869547) B2869547
theorem B2152165 : Blo 1911435 2152165 := bbase (se 4 (by rfl) ⟨201765, by rfl⟩ : syracuseStep 2152165 = 403531) (by norm_num)
theorem B2869553 : Blo 1911435 2869553 := bstep (se 2 (by rfl) ⟨1076082, by rfl⟩ : syracuseStep 2869553 = 2152165) B2152165
theorem B1913035 : Blo 1911435 1913035 := bstep (se 1 (by rfl) ⟨1434776, by rfl⟩ : syracuseStep 1913035 = 2869553) B2869553
theorem B2298241 : Blo 1911435 2298241 := bbase (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) (by norm_num)
theorem B3064321 : Blo 1911435 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B4085761 : Blo 1911435 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B5447681 : Blo 1911435 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B3631787 : Blo 1911435 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B2421191 : Blo 1911435 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B6456509 : Blo 1911435 6456509 := bstep (se 3 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 6456509 = 2421191) B2421191
theorem B4304339 : Blo 1911435 4304339 := bstep (se 1 (by rfl) ⟨3228254, by rfl⟩ : syracuseStep 4304339 = 6456509) B6456509
theorem B2869559 : Blo 1911435 2869559 := bstep (se 1 (by rfl) ⟨2152169, by rfl⟩ : syracuseStep 2869559 = 4304339) B4304339
theorem B1913039 : Blo 1911435 1913039 := bstep (se 1 (by rfl) ⟨1434779, by rfl⟩ : syracuseStep 1913039 = 2869559) B2869559
theorem B2869565 : Blo 1911435 2869565 := bbase (se 3 (by rfl) ⟨538043, by rfl⟩ : syracuseStep 2869565 = 1076087) (by norm_num)
theorem B1913043 : Blo 1911435 1913043 := bstep (se 1 (by rfl) ⟨1434782, by rfl⟩ : syracuseStep 1913043 = 2869565) B2869565
theorem B4304357 : Blo 1911435 4304357 := bbase (se 4 (by rfl) ⟨403533, by rfl⟩ : syracuseStep 4304357 = 807067) (by norm_num)
theorem B2869571 : Blo 1911435 2869571 := bstep (se 1 (by rfl) ⟨2152178, by rfl⟩ : syracuseStep 2869571 = 4304357) B4304357
theorem B1913047 : Blo 1911435 1913047 := bstep (se 1 (by rfl) ⟨1434785, by rfl⟩ : syracuseStep 1913047 = 2869571) B2869571
theorem B4842413 : Blo 1911435 4842413 := bbase (se 3 (by rfl) ⟨907952, by rfl⟩ : syracuseStep 4842413 = 1815905) (by norm_num)
theorem B3228275 : Blo 1911435 3228275 := bstep (se 1 (by rfl) ⟨2421206, by rfl⟩ : syracuseStep 3228275 = 4842413) B4842413
theorem B2152183 : Blo 1911435 2152183 := bstep (se 1 (by rfl) ⟨1614137, by rfl⟩ : syracuseStep 2152183 = 3228275) B3228275
theorem B2869577 : Blo 1911435 2869577 := bstep (se 2 (by rfl) ⟨1076091, by rfl⟩ : syracuseStep 2869577 = 2152183) B2152183
theorem B1913051 : Blo 1911435 1913051 := bstep (se 1 (by rfl) ⟨1434788, by rfl⟩ : syracuseStep 1913051 = 2869577) B2869577
theorem B6128693 : Blo 1911435 6128693 := bbase (se 5 (by rfl) ⟨287282, by rfl⟩ : syracuseStep 6128693 = 574565) (by norm_num)
theorem B4085795 : Blo 1911435 4085795 := bstep (se 1 (by rfl) ⟨3064346, by rfl⟩ : syracuseStep 4085795 = 6128693) B6128693
theorem B2723863 : Blo 1911435 2723863 := bstep (se 1 (by rfl) ⟨2042897, by rfl⟩ : syracuseStep 2723863 = 4085795) B4085795
theorem B3631817 : Blo 1911435 3631817 := bstep (se 2 (by rfl) ⟨1361931, by rfl⟩ : syracuseStep 3631817 = 2723863) B2723863
theorem B9684845 : Blo 1911435 9684845 := bstep (se 3 (by rfl) ⟨1815908, by rfl⟩ : syracuseStep 9684845 = 3631817) B3631817
theorem B6456563 : Blo 1911435 6456563 := bstep (se 1 (by rfl) ⟨4842422, by rfl⟩ : syracuseStep 6456563 = 9684845) B9684845
theorem B4304375 : Blo 1911435 4304375 := bstep (se 1 (by rfl) ⟨3228281, by rfl⟩ : syracuseStep 4304375 = 6456563) B6456563
theorem B2869583 : Blo 1911435 2869583 := bstep (se 1 (by rfl) ⟨2152187, by rfl⟩ : syracuseStep 2869583 = 4304375) B4304375
theorem B1913055 : Blo 1911435 1913055 := bstep (se 1 (by rfl) ⟨1434791, by rfl⟩ : syracuseStep 1913055 = 2869583) B2869583
theorem B2869589 : Blo 1911435 2869589 := bbase (se 10 (by rfl) ⟨4203, by rfl⟩ : syracuseStep 2869589 = 8407) (by norm_num)
theorem B1913059 : Blo 1911435 1913059 := bstep (se 1 (by rfl) ⟨1434794, by rfl⟩ : syracuseStep 1913059 = 2869589) B2869589
theorem B5447749 : Blo 1911435 5447749 := bbase (se 4 (by rfl) ⟨510726, by rfl⟩ : syracuseStep 5447749 = 1021453) (by norm_num)
theorem B7263665 : Blo 1911435 7263665 := bstep (se 2 (by rfl) ⟨2723874, by rfl⟩ : syracuseStep 7263665 = 5447749) B5447749
theorem B4842443 : Blo 1911435 4842443 := bstep (se 1 (by rfl) ⟨3631832, by rfl⟩ : syracuseStep 4842443 = 7263665) B7263665
theorem B3228295 : Blo 1911435 3228295 := bstep (se 1 (by rfl) ⟨2421221, by rfl⟩ : syracuseStep 3228295 = 4842443) B4842443
theorem B4304393 : Blo 1911435 4304393 := bstep (se 2 (by rfl) ⟨1614147, by rfl⟩ : syracuseStep 4304393 = 3228295) B3228295
theorem B2869595 : Blo 1911435 2869595 := bstep (se 1 (by rfl) ⟨2152196, by rfl⟩ : syracuseStep 2869595 = 4304393) B4304393
theorem B1913063 : Blo 1911435 1913063 := bstep (se 1 (by rfl) ⟨1434797, by rfl⟩ : syracuseStep 1913063 = 2869595) B2869595
theorem B2152201 : Blo 1911435 2152201 := bbase (se 2 (by rfl) ⟨807075, by rfl⟩ : syracuseStep 2152201 = 1614151) (by norm_num)
theorem B2869601 : Blo 1911435 2869601 := bstep (se 2 (by rfl) ⟨1076100, by rfl⟩ : syracuseStep 2869601 = 2152201) B2152201
theorem B1913067 : Blo 1911435 1913067 := bstep (se 1 (by rfl) ⟨1434800, by rfl⟩ : syracuseStep 1913067 = 2869601) B2869601
theorem B3494453 : Blo 1911435 3494453 := bbase (se 5 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 3494453 = 327605) (by norm_num)
theorem B37274165 : Blo 1911435 37274165 := bstep (se 5 (by rfl) ⟨1747226, by rfl⟩ : syracuseStep 37274165 = 3494453) B3494453
theorem B24849443 : Blo 1911435 24849443 := bstep (se 1 (by rfl) ⟨18637082, by rfl⟩ : syracuseStep 24849443 = 37274165) B37274165
theorem B16566295 : Blo 1911435 16566295 := bstep (se 1 (by rfl) ⟨12424721, by rfl⟩ : syracuseStep 16566295 = 24849443) B24849443
theorem B22088393 : Blo 1911435 22088393 := bstep (se 2 (by rfl) ⟨8283147, by rfl⟩ : syracuseStep 22088393 = 16566295) B16566295
theorem B14725595 : Blo 1911435 14725595 := bstep (se 1 (by rfl) ⟨11044196, by rfl⟩ : syracuseStep 14725595 = 22088393) B22088393
theorem B39268253 : Blo 1911435 39268253 := bstep (se 3 (by rfl) ⟨7362797, by rfl⟩ : syracuseStep 39268253 = 14725595) B14725595
theorem B26178835 : Blo 1911435 26178835 := bstep (se 1 (by rfl) ⟨19634126, by rfl⟩ : syracuseStep 26178835 = 39268253) B39268253
theorem B34905113 : Blo 1911435 34905113 := bstep (se 2 (by rfl) ⟨13089417, by rfl⟩ : syracuseStep 34905113 = 26178835) B26178835
theorem B23270075 : Blo 1911435 23270075 := bstep (se 1 (by rfl) ⟨17452556, by rfl⟩ : syracuseStep 23270075 = 34905113) B34905113
theorem B15513383 : Blo 1911435 15513383 := bstep (se 1 (by rfl) ⟨11635037, by rfl⟩ : syracuseStep 15513383 = 23270075) B23270075
theorem B10342255 : Blo 1911435 10342255 := bstep (se 1 (by rfl) ⟨7756691, by rfl⟩ : syracuseStep 10342255 = 15513383) B15513383
theorem B13789673 : Blo 1911435 13789673 := bstep (se 2 (by rfl) ⟨5171127, by rfl⟩ : syracuseStep 13789673 = 10342255) B10342255
theorem B9193115 : Blo 1911435 9193115 := bstep (se 1 (by rfl) ⟨6894836, by rfl⟩ : syracuseStep 9193115 = 13789673) B13789673
theorem B24514973 : Blo 1911435 24514973 := bstep (se 3 (by rfl) ⟨4596557, by rfl⟩ : syracuseStep 24514973 = 9193115) B9193115
theorem B16343315 : Blo 1911435 16343315 := bstep (se 1 (by rfl) ⟨12257486, by rfl⟩ : syracuseStep 16343315 = 24514973) B24514973
theorem B10895543 : Blo 1911435 10895543 := bstep (se 1 (by rfl) ⟨8171657, by rfl⟩ : syracuseStep 10895543 = 16343315) B16343315
theorem B7263695 : Blo 1911435 7263695 := bstep (se 1 (by rfl) ⟨5447771, by rfl⟩ : syracuseStep 7263695 = 10895543) B10895543
theorem B4842463 : Blo 1911435 4842463 := bstep (se 1 (by rfl) ⟨3631847, by rfl⟩ : syracuseStep 4842463 = 7263695) B7263695
theorem B6456617 : Blo 1911435 6456617 := bstep (se 2 (by rfl) ⟨2421231, by rfl⟩ : syracuseStep 6456617 = 4842463) B4842463
theorem B4304411 : Blo 1911435 4304411 := bstep (se 1 (by rfl) ⟨3228308, by rfl⟩ : syracuseStep 4304411 = 6456617) B6456617
theorem B2869607 : Blo 1911435 2869607 := bstep (se 1 (by rfl) ⟨2152205, by rfl⟩ : syracuseStep 2869607 = 4304411) B4304411
theorem B1913071 : Blo 1911435 1913071 := bstep (se 1 (by rfl) ⟨1434803, by rfl⟩ : syracuseStep 1913071 = 2869607) B2869607
theorem B2869613 : Blo 1911435 2869613 := bbase (se 3 (by rfl) ⟨538052, by rfl⟩ : syracuseStep 2869613 = 1076105) (by norm_num)
theorem B1913075 : Blo 1911435 1913075 := bstep (se 1 (by rfl) ⟨1434806, by rfl⟩ : syracuseStep 1913075 = 2869613) B2869613
theorem B4304429 : Blo 1911435 4304429 := bbase (se 3 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 4304429 = 1614161) (by norm_num)
theorem B2869619 : Blo 1911435 2869619 := bstep (se 1 (by rfl) ⟨2152214, by rfl⟩ : syracuseStep 2869619 = 4304429) B4304429
theorem B1913079 : Blo 1911435 1913079 := bstep (se 1 (by rfl) ⟨1434809, by rfl⟩ : syracuseStep 1913079 = 2869619) B2869619
theorem B4659301 : Blo 1911435 4659301 := bbase (se 4 (by rfl) ⟨436809, by rfl⟩ : syracuseStep 4659301 = 873619) (by norm_num)
theorem B24849605 : Blo 1911435 24849605 := bstep (se 4 (by rfl) ⟨2329650, by rfl⟩ : syracuseStep 24849605 = 4659301) B4659301
theorem B66265613 : Blo 1911435 66265613 := bstep (se 3 (by rfl) ⟨12424802, by rfl⟩ : syracuseStep 66265613 = 24849605) B24849605
theorem B44177075 : Blo 1911435 44177075 := bstep (se 1 (by rfl) ⟨33132806, by rfl⟩ : syracuseStep 44177075 = 66265613) B66265613
theorem B29451383 : Blo 1911435 29451383 := bstep (se 1 (by rfl) ⟨22088537, by rfl⟩ : syracuseStep 29451383 = 44177075) B44177075
theorem B19634255 : Blo 1911435 19634255 := bstep (se 1 (by rfl) ⟨14725691, by rfl⟩ : syracuseStep 19634255 = 29451383) B29451383
theorem B13089503 : Blo 1911435 13089503 := bstep (se 1 (by rfl) ⟨9817127, by rfl⟩ : syracuseStep 13089503 = 19634255) B19634255
theorem B8726335 : Blo 1911435 8726335 := bstep (se 1 (by rfl) ⟨6544751, by rfl⟩ : syracuseStep 8726335 = 13089503) B13089503
theorem B46540453 : Blo 1911435 46540453 := bstep (se 4 (by rfl) ⟨4363167, by rfl⟩ : syracuseStep 46540453 = 8726335) B8726335
theorem B62053937 : Blo 1911435 62053937 := bstep (se 2 (by rfl) ⟨23270226, by rfl⟩ : syracuseStep 62053937 = 46540453) B46540453
theorem B41369291 : Blo 1911435 41369291 := bstep (se 1 (by rfl) ⟨31026968, by rfl⟩ : syracuseStep 41369291 = 62053937) B62053937
theorem B27579527 : Blo 1911435 27579527 := bstep (se 1 (by rfl) ⟨20684645, by rfl⟩ : syracuseStep 27579527 = 41369291) B41369291
theorem B18386351 : Blo 1911435 18386351 := bstep (se 1 (by rfl) ⟨13789763, by rfl⟩ : syracuseStep 18386351 = 27579527) B27579527
theorem B12257567 : Blo 1911435 12257567 := bstep (se 1 (by rfl) ⟨9193175, by rfl⟩ : syracuseStep 12257567 = 18386351) B18386351
theorem B8171711 : Blo 1911435 8171711 := bstep (se 1 (by rfl) ⟨6128783, by rfl⟩ : syracuseStep 8171711 = 12257567) B12257567
theorem B5447807 : Blo 1911435 5447807 := bstep (se 1 (by rfl) ⟨4085855, by rfl⟩ : syracuseStep 5447807 = 8171711) B8171711
theorem B3631871 : Blo 1911435 3631871 := bstep (se 1 (by rfl) ⟨2723903, by rfl⟩ : syracuseStep 3631871 = 5447807) B5447807
theorem B2421247 : Blo 1911435 2421247 := bstep (se 1 (by rfl) ⟨1815935, by rfl⟩ : syracuseStep 2421247 = 3631871) B3631871
theorem B3228329 : Blo 1911435 3228329 := bstep (se 2 (by rfl) ⟨1210623, by rfl⟩ : syracuseStep 3228329 = 2421247) B2421247
theorem B2152219 : Blo 1911435 2152219 := bstep (se 1 (by rfl) ⟨1614164, by rfl⟩ : syracuseStep 2152219 = 3228329) B3228329
theorem B2869625 : Blo 1911435 2869625 := bstep (se 2 (by rfl) ⟨1076109, by rfl⟩ : syracuseStep 2869625 = 2152219) B2152219
theorem B1913083 : Blo 1911435 1913083 := bstep (se 1 (by rfl) ⟨1434812, by rfl⟩ : syracuseStep 1913083 = 2869625) B2869625
theorem B3064397 : Blo 1911435 3064397 := bbase (se 3 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 3064397 = 1149149) (by norm_num)
theorem B32686901 : Blo 1911435 32686901 := bstep (se 5 (by rfl) ⟨1532198, by rfl⟩ : syracuseStep 32686901 = 3064397) B3064397
theorem B21791267 : Blo 1911435 21791267 := bstep (se 1 (by rfl) ⟨16343450, by rfl⟩ : syracuseStep 21791267 = 32686901) B32686901
theorem B14527511 : Blo 1911435 14527511 := bstep (se 1 (by rfl) ⟨10895633, by rfl⟩ : syracuseStep 14527511 = 21791267) B21791267
theorem B9685007 : Blo 1911435 9685007 := bstep (se 1 (by rfl) ⟨7263755, by rfl⟩ : syracuseStep 9685007 = 14527511) B14527511
theorem B6456671 : Blo 1911435 6456671 := bstep (se 1 (by rfl) ⟨4842503, by rfl⟩ : syracuseStep 6456671 = 9685007) B9685007
theorem B4304447 : Blo 1911435 4304447 := bstep (se 1 (by rfl) ⟨3228335, by rfl⟩ : syracuseStep 4304447 = 6456671) B6456671
theorem B2869631 : Blo 1911435 2869631 := bstep (se 1 (by rfl) ⟨2152223, by rfl⟩ : syracuseStep 2869631 = 4304447) B4304447
theorem B1913087 : Blo 1911435 1913087 := bstep (se 1 (by rfl) ⟨1434815, by rfl⟩ : syracuseStep 1913087 = 2869631) B2869631
theorem B2869637 : Blo 1911435 2869637 := bbase (se 4 (by rfl) ⟨269028, by rfl⟩ : syracuseStep 2869637 = 538057) (by norm_num)
theorem B1913091 : Blo 1911435 1913091 := bstep (se 1 (by rfl) ⟨1434818, by rfl⟩ : syracuseStep 1913091 = 2869637) B2869637
theorem B3228349 : Blo 1911435 3228349 := bbase (se 3 (by rfl) ⟨605315, by rfl⟩ : syracuseStep 3228349 = 1210631) (by norm_num)
theorem B4304465 : Blo 1911435 4304465 := bstep (se 2 (by rfl) ⟨1614174, by rfl⟩ : syracuseStep 4304465 = 3228349) B3228349
theorem B2869643 : Blo 1911435 2869643 := bstep (se 1 (by rfl) ⟨2152232, by rfl⟩ : syracuseStep 2869643 = 4304465) B4304465
theorem B1913095 : Blo 1911435 1913095 := bstep (se 1 (by rfl) ⟨1434821, by rfl⟩ : syracuseStep 1913095 = 2869643) B2869643
theorem B2152237 : Blo 1911435 2152237 := bbase (se 3 (by rfl) ⟨403544, by rfl⟩ : syracuseStep 2152237 = 807089) (by norm_num)
theorem B2869649 : Blo 1911435 2869649 := bstep (se 2 (by rfl) ⟨1076118, by rfl⟩ : syracuseStep 2869649 = 2152237) B2152237
theorem B1913099 : Blo 1911435 1913099 := bstep (se 1 (by rfl) ⟨1434824, by rfl⟩ : syracuseStep 1913099 = 2869649) B2869649
theorem B6456725 : Blo 1911435 6456725 := bbase (se 6 (by rfl) ⟨151329, by rfl⟩ : syracuseStep 6456725 = 302659) (by norm_num)
theorem B4304483 : Blo 1911435 4304483 := bstep (se 1 (by rfl) ⟨3228362, by rfl⟩ : syracuseStep 4304483 = 6456725) B6456725
theorem B2869655 : Blo 1911435 2869655 := bstep (se 1 (by rfl) ⟨2152241, by rfl⟩ : syracuseStep 2869655 = 4304483) B4304483
theorem B1913103 : Blo 1911435 1913103 := bstep (se 1 (by rfl) ⟨1434827, by rfl⟩ : syracuseStep 1913103 = 2869655) B2869655
theorem B2869661 : Blo 1911435 2869661 := bbase (se 3 (by rfl) ⟨538061, by rfl⟩ : syracuseStep 2869661 = 1076123) (by norm_num)
theorem B1913107 : Blo 1911435 1913107 := bstep (se 1 (by rfl) ⟨1434830, by rfl⟩ : syracuseStep 1913107 = 2869661) B2869661
theorem B4304501 : Blo 1911435 4304501 := bbase (se 5 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 4304501 = 403547) (by norm_num)
theorem B2869667 : Blo 1911435 2869667 := bstep (se 1 (by rfl) ⟨2152250, by rfl⟩ : syracuseStep 2869667 = 4304501) B4304501
theorem B1913111 : Blo 1911435 1913111 := bstep (se 1 (by rfl) ⟨1434833, by rfl⟩ : syracuseStep 1913111 = 2869667) B2869667
theorem B6128885 : Blo 1911435 6128885 := bbase (se 5 (by rfl) ⟨287291, by rfl⟩ : syracuseStep 6128885 = 574583) (by norm_num)
theorem B16343693 : Blo 1911435 16343693 := bstep (se 3 (by rfl) ⟨3064442, by rfl⟩ : syracuseStep 16343693 = 6128885) B6128885
theorem B10895795 : Blo 1911435 10895795 := bstep (se 1 (by rfl) ⟨8171846, by rfl⟩ : syracuseStep 10895795 = 16343693) B16343693
theorem B7263863 : Blo 1911435 7263863 := bstep (se 1 (by rfl) ⟨5447897, by rfl⟩ : syracuseStep 7263863 = 10895795) B10895795
theorem B4842575 : Blo 1911435 4842575 := bstep (se 1 (by rfl) ⟨3631931, by rfl⟩ : syracuseStep 4842575 = 7263863) B7263863
theorem B3228383 : Blo 1911435 3228383 := bstep (se 1 (by rfl) ⟨2421287, by rfl⟩ : syracuseStep 3228383 = 4842575) B4842575
theorem B2152255 : Blo 1911435 2152255 := bstep (se 1 (by rfl) ⟨1614191, by rfl⟩ : syracuseStep 2152255 = 3228383) B3228383
theorem B2869673 : Blo 1911435 2869673 := bstep (se 2 (by rfl) ⟨1076127, by rfl⟩ : syracuseStep 2869673 = 2152255) B2152255
theorem B1913115 : Blo 1911435 1913115 := bstep (se 1 (by rfl) ⟨1434836, by rfl⟩ : syracuseStep 1913115 = 2869673) B2869673
theorem B7263877 : Blo 1911435 7263877 := bbase (se 4 (by rfl) ⟨680988, by rfl⟩ : syracuseStep 7263877 = 1361977) (by norm_num)
theorem B9685169 : Blo 1911435 9685169 := bstep (se 2 (by rfl) ⟨3631938, by rfl⟩ : syracuseStep 9685169 = 7263877) B7263877
theorem B6456779 : Blo 1911435 6456779 := bstep (se 1 (by rfl) ⟨4842584, by rfl⟩ : syracuseStep 6456779 = 9685169) B9685169
theorem B4304519 : Blo 1911435 4304519 := bstep (se 1 (by rfl) ⟨3228389, by rfl⟩ : syracuseStep 4304519 = 6456779) B6456779
theorem B2869679 : Blo 1911435 2869679 := bstep (se 1 (by rfl) ⟨2152259, by rfl⟩ : syracuseStep 2869679 = 4304519) B4304519
theorem B1913119 : Blo 1911435 1913119 := bstep (se 1 (by rfl) ⟨1434839, by rfl⟩ : syracuseStep 1913119 = 2869679) B2869679
theorem B2869685 : Blo 1911435 2869685 := bbase (se 5 (by rfl) ⟨134516, by rfl⟩ : syracuseStep 2869685 = 269033) (by norm_num)
theorem B1913123 : Blo 1911435 1913123 := bstep (se 1 (by rfl) ⟨1434842, by rfl⟩ : syracuseStep 1913123 = 2869685) B2869685
theorem B4842605 : Blo 1911435 4842605 := bbase (se 3 (by rfl) ⟨907988, by rfl⟩ : syracuseStep 4842605 = 1815977) (by norm_num)
theorem B3228403 : Blo 1911435 3228403 := bstep (se 1 (by rfl) ⟨2421302, by rfl⟩ : syracuseStep 3228403 = 4842605) B4842605
theorem B4304537 : Blo 1911435 4304537 := bstep (se 2 (by rfl) ⟨1614201, by rfl⟩ : syracuseStep 4304537 = 3228403) B3228403
theorem B2869691 : Blo 1911435 2869691 := bstep (se 1 (by rfl) ⟨2152268, by rfl⟩ : syracuseStep 2869691 = 4304537) B4304537
theorem B1913127 : Blo 1911435 1913127 := bstep (se 1 (by rfl) ⟨1434845, by rfl⟩ : syracuseStep 1913127 = 2869691) B2869691
theorem B2152273 : Blo 1911435 2152273 := bbase (se 2 (by rfl) ⟨807102, by rfl⟩ : syracuseStep 2152273 = 1614205) (by norm_num)
theorem B2869697 : Blo 1911435 2869697 := bstep (se 2 (by rfl) ⟨1076136, by rfl⟩ : syracuseStep 2869697 = 2152273) B2152273
theorem B1913131 : Blo 1911435 1913131 := bstep (se 1 (by rfl) ⟨1434848, by rfl⟩ : syracuseStep 1913131 = 2869697) B2869697
theorem B18637717 : Blo 1911435 18637717 := bbase (se 6 (by rfl) ⟨436821, by rfl⟩ : syracuseStep 18637717 = 873643) (by norm_num)
theorem B24850289 : Blo 1911435 24850289 := bstep (se 2 (by rfl) ⟨9318858, by rfl⟩ : syracuseStep 24850289 = 18637717) B18637717
theorem B16566859 : Blo 1911435 16566859 := bstep (se 1 (by rfl) ⟨12425144, by rfl⟩ : syracuseStep 16566859 = 24850289) B24850289
theorem B22089145 : Blo 1911435 22089145 := bstep (se 2 (by rfl) ⟨8283429, by rfl⟩ : syracuseStep 22089145 = 16566859) B16566859
theorem B29452193 : Blo 1911435 29452193 := bstep (se 2 (by rfl) ⟨11044572, by rfl⟩ : syracuseStep 29452193 = 22089145) B22089145
theorem B19634795 : Blo 1911435 19634795 := bstep (se 1 (by rfl) ⟨14726096, by rfl⟩ : syracuseStep 19634795 = 29452193) B29452193
theorem B13089863 : Blo 1911435 13089863 := bstep (se 1 (by rfl) ⟨9817397, by rfl⟩ : syracuseStep 13089863 = 19634795) B19634795
theorem B8726575 : Blo 1911435 8726575 := bstep (se 1 (by rfl) ⟨6544931, by rfl⟩ : syracuseStep 8726575 = 13089863) B13089863
theorem B11635433 : Blo 1911435 11635433 := bstep (se 2 (by rfl) ⟨4363287, by rfl⟩ : syracuseStep 11635433 = 8726575) B8726575
theorem B7756955 : Blo 1911435 7756955 := bstep (se 1 (by rfl) ⟨5817716, by rfl⟩ : syracuseStep 7756955 = 11635433) B11635433
theorem B5171303 : Blo 1911435 5171303 := bstep (se 1 (by rfl) ⟨3878477, by rfl⟩ : syracuseStep 5171303 = 7756955) B7756955
theorem B3447535 : Blo 1911435 3447535 := bstep (se 1 (by rfl) ⟨2585651, by rfl⟩ : syracuseStep 3447535 = 5171303) B5171303
theorem B4596713 : Blo 1911435 4596713 := bstep (se 2 (by rfl) ⟨1723767, by rfl⟩ : syracuseStep 4596713 = 3447535) B3447535
theorem B3064475 : Blo 1911435 3064475 := bstep (se 1 (by rfl) ⟨2298356, by rfl⟩ : syracuseStep 3064475 = 4596713) B4596713
theorem B2042983 : Blo 1911435 2042983 := bstep (se 1 (by rfl) ⟨1532237, by rfl⟩ : syracuseStep 2042983 = 3064475) B3064475
theorem B2723977 : Blo 1911435 2723977 := bstep (se 2 (by rfl) ⟨1021491, by rfl⟩ : syracuseStep 2723977 = 2042983) B2042983
theorem B3631969 : Blo 1911435 3631969 := bstep (se 2 (by rfl) ⟨1361988, by rfl⟩ : syracuseStep 3631969 = 2723977) B2723977
theorem B4842625 : Blo 1911435 4842625 := bstep (se 2 (by rfl) ⟨1815984, by rfl⟩ : syracuseStep 4842625 = 3631969) B3631969
theorem B6456833 : Blo 1911435 6456833 := bstep (se 2 (by rfl) ⟨2421312, by rfl⟩ : syracuseStep 6456833 = 4842625) B4842625
theorem B4304555 : Blo 1911435 4304555 := bstep (se 1 (by rfl) ⟨3228416, by rfl⟩ : syracuseStep 4304555 = 6456833) B6456833
theorem B2869703 : Blo 1911435 2869703 := bstep (se 1 (by rfl) ⟨2152277, by rfl⟩ : syracuseStep 2869703 = 4304555) B4304555
theorem B1913135 : Blo 1911435 1913135 := bstep (se 1 (by rfl) ⟨1434851, by rfl⟩ : syracuseStep 1913135 = 2869703) B2869703
theorem B2869709 : Blo 1911435 2869709 := bbase (se 3 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 2869709 = 1076141) (by norm_num)
theorem B1913139 : Blo 1911435 1913139 := bstep (se 1 (by rfl) ⟨1434854, by rfl⟩ : syracuseStep 1913139 = 2869709) B2869709
theorem B4304573 : Blo 1911435 4304573 := bbase (se 3 (by rfl) ⟨807107, by rfl⟩ : syracuseStep 4304573 = 1614215) (by norm_num)
theorem B2869715 : Blo 1911435 2869715 := bstep (se 1 (by rfl) ⟨2152286, by rfl⟩ : syracuseStep 2869715 = 4304573) B4304573
theorem B1913143 : Blo 1911435 1913143 := bstep (se 1 (by rfl) ⟨1434857, by rfl⟩ : syracuseStep 1913143 = 2869715) B2869715
theorem B3228437 : Blo 1911435 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B2152291 : Blo 1911435 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B2869721 : Blo 1911435 2869721 := bstep (se 2 (by rfl) ⟨1076145, by rfl⟩ : syracuseStep 2869721 = 2152291) B2152291
theorem B1913147 : Blo 1911435 1913147 := bstep (se 1 (by rfl) ⟨1434860, by rfl⟩ : syracuseStep 1913147 = 2869721) B2869721
theorem B2329733 : Blo 1911435 2329733 := bbase (se 4 (by rfl) ⟨218412, by rfl⟩ : syracuseStep 2329733 = 436825) (by norm_num)
theorem B6212621 : Blo 1911435 6212621 := bstep (se 3 (by rfl) ⟨1164866, by rfl⟩ : syracuseStep 6212621 = 2329733) B2329733
theorem B4141747 : Blo 1911435 4141747 := bstep (se 1 (by rfl) ⟨3106310, by rfl⟩ : syracuseStep 4141747 = 6212621) B6212621
theorem B5522329 : Blo 1911435 5522329 := bstep (se 2 (by rfl) ⟨2070873, by rfl⟩ : syracuseStep 5522329 = 4141747) B4141747
theorem B7363105 : Blo 1911435 7363105 := bstep (se 2 (by rfl) ⟨2761164, by rfl⟩ : syracuseStep 7363105 = 5522329) B5522329
theorem B39269893 : Blo 1911435 39269893 := bstep (se 4 (by rfl) ⟨3681552, by rfl⟩ : syracuseStep 39269893 = 7363105) B7363105
theorem B52359857 : Blo 1911435 52359857 := bstep (se 2 (by rfl) ⟨19634946, by rfl⟩ : syracuseStep 52359857 = 39269893) B39269893
theorem B34906571 : Blo 1911435 34906571 := bstep (se 1 (by rfl) ⟨26179928, by rfl⟩ : syracuseStep 34906571 = 52359857) B52359857
theorem B23271047 : Blo 1911435 23271047 := bstep (se 1 (by rfl) ⟨17453285, by rfl⟩ : syracuseStep 23271047 = 34906571) B34906571
theorem B15514031 : Blo 1911435 15514031 := bstep (se 1 (by rfl) ⟨11635523, by rfl⟩ : syracuseStep 15514031 = 23271047) B23271047
theorem B41370749 : Blo 1911435 41370749 := bstep (se 3 (by rfl) ⟨7757015, by rfl⟩ : syracuseStep 41370749 = 15514031) B15514031
theorem B27580499 : Blo 1911435 27580499 := bstep (se 1 (by rfl) ⟨20685374, by rfl⟩ : syracuseStep 27580499 = 41370749) B41370749
theorem B18386999 : Blo 1911435 18386999 := bstep (se 1 (by rfl) ⟨13790249, by rfl⟩ : syracuseStep 18386999 = 27580499) B27580499
theorem B12257999 : Blo 1911435 12257999 := bstep (se 1 (by rfl) ⟨9193499, by rfl⟩ : syracuseStep 12257999 = 18386999) B18386999
theorem B8171999 : Blo 1911435 8171999 := bstep (se 1 (by rfl) ⟨6128999, by rfl⟩ : syracuseStep 8171999 = 12257999) B12257999
theorem B5447999 : Blo 1911435 5447999 := bstep (se 1 (by rfl) ⟨4085999, by rfl⟩ : syracuseStep 5447999 = 8171999) B8171999
theorem B14527997 : Blo 1911435 14527997 := bstep (se 3 (by rfl) ⟨2723999, by rfl⟩ : syracuseStep 14527997 = 5447999) B5447999
theorem B9685331 : Blo 1911435 9685331 := bstep (se 1 (by rfl) ⟨7263998, by rfl⟩ : syracuseStep 9685331 = 14527997) B14527997
theorem B6456887 : Blo 1911435 6456887 := bstep (se 1 (by rfl) ⟨4842665, by rfl⟩ : syracuseStep 6456887 = 9685331) B9685331
theorem B4304591 : Blo 1911435 4304591 := bstep (se 1 (by rfl) ⟨3228443, by rfl⟩ : syracuseStep 4304591 = 6456887) B6456887
theorem B2869727 : Blo 1911435 2869727 := bstep (se 1 (by rfl) ⟨2152295, by rfl⟩ : syracuseStep 2869727 = 4304591) B4304591
theorem B1913151 : Blo 1911435 1913151 := bstep (se 1 (by rfl) ⟨1434863, by rfl⟩ : syracuseStep 1913151 = 2869727) B2869727
theorem B2869733 : Blo 1911435 2869733 := bbase (se 4 (by rfl) ⟨269037, by rfl⟩ : syracuseStep 2869733 = 538075) (by norm_num)
theorem B1913155 : Blo 1911435 1913155 := bstep (se 1 (by rfl) ⟨1434866, by rfl⟩ : syracuseStep 1913155 = 2869733) B2869733
theorem B2298385 : Blo 1911435 2298385 := bbase (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) (by norm_num)
theorem B12258053 : Blo 1911435 12258053 := bstep (se 4 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 12258053 = 2298385) B2298385
theorem B8172035 : Blo 1911435 8172035 := bstep (se 1 (by rfl) ⟨6129026, by rfl⟩ : syracuseStep 8172035 = 12258053) B12258053
theorem B5448023 : Blo 1911435 5448023 := bstep (se 1 (by rfl) ⟨4086017, by rfl⟩ : syracuseStep 5448023 = 8172035) B8172035
theorem B3632015 : Blo 1911435 3632015 := bstep (se 1 (by rfl) ⟨2724011, by rfl⟩ : syracuseStep 3632015 = 5448023) B5448023
theorem B2421343 : Blo 1911435 2421343 := bstep (se 1 (by rfl) ⟨1816007, by rfl⟩ : syracuseStep 2421343 = 3632015) B3632015
theorem B3228457 : Blo 1911435 3228457 := bstep (se 2 (by rfl) ⟨1210671, by rfl⟩ : syracuseStep 3228457 = 2421343) B2421343
theorem B4304609 : Blo 1911435 4304609 := bstep (se 2 (by rfl) ⟨1614228, by rfl⟩ : syracuseStep 4304609 = 3228457) B3228457
theorem B2869739 : Blo 1911435 2869739 := bstep (se 1 (by rfl) ⟨2152304, by rfl⟩ : syracuseStep 2869739 = 4304609) B4304609
theorem B1913159 : Blo 1911435 1913159 := bstep (se 1 (by rfl) ⟨1434869, by rfl⟩ : syracuseStep 1913159 = 2869739) B2869739
theorem B2152309 : Blo 1911435 2152309 := bbase (se 5 (by rfl) ⟨100889, by rfl⟩ : syracuseStep 2152309 = 201779) (by norm_num)
theorem B2869745 : Blo 1911435 2869745 := bstep (se 2 (by rfl) ⟨1076154, by rfl⟩ : syracuseStep 2869745 = 2152309) B2152309
theorem B1913163 : Blo 1911435 1913163 := bstep (se 1 (by rfl) ⟨1434872, by rfl⟩ : syracuseStep 1913163 = 2869745) B2869745
theorem B2421353 : Blo 1911435 2421353 := bbase (se 2 (by rfl) ⟨908007, by rfl⟩ : syracuseStep 2421353 = 1816015) (by norm_num)
theorem B6456941 : Blo 1911435 6456941 := bstep (se 3 (by rfl) ⟨1210676, by rfl⟩ : syracuseStep 6456941 = 2421353) B2421353
theorem B4304627 : Blo 1911435 4304627 := bstep (se 1 (by rfl) ⟨3228470, by rfl⟩ : syracuseStep 4304627 = 6456941) B6456941
theorem B2869751 : Blo 1911435 2869751 := bstep (se 1 (by rfl) ⟨2152313, by rfl⟩ : syracuseStep 2869751 = 4304627) B4304627
theorem B1913167 : Blo 1911435 1913167 := bstep (se 1 (by rfl) ⟨1434875, by rfl⟩ : syracuseStep 1913167 = 2869751) B2869751
theorem B2869757 : Blo 1911435 2869757 := bbase (se 3 (by rfl) ⟨538079, by rfl⟩ : syracuseStep 2869757 = 1076159) (by norm_num)
theorem B1913171 : Blo 1911435 1913171 := bstep (se 1 (by rfl) ⟨1434878, by rfl⟩ : syracuseStep 1913171 = 2869757) B2869757
theorem B4304645 : Blo 1911435 4304645 := bbase (se 4 (by rfl) ⟨403560, by rfl⟩ : syracuseStep 4304645 = 807121) (by norm_num)
theorem B2869763 : Blo 1911435 2869763 := bstep (se 1 (by rfl) ⟨2152322, by rfl⟩ : syracuseStep 2869763 = 4304645) B4304645
theorem B1913175 : Blo 1911435 1913175 := bstep (se 1 (by rfl) ⟨1434881, by rfl⟩ : syracuseStep 1913175 = 2869763) B2869763
theorem B3632053 : Blo 1911435 3632053 := bbase (se 5 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 3632053 = 340505) (by norm_num)
theorem B4842737 : Blo 1911435 4842737 := bstep (se 2 (by rfl) ⟨1816026, by rfl⟩ : syracuseStep 4842737 = 3632053) B3632053
theorem B3228491 : Blo 1911435 3228491 := bstep (se 1 (by rfl) ⟨2421368, by rfl⟩ : syracuseStep 3228491 = 4842737) B4842737
theorem B2152327 : Blo 1911435 2152327 := bstep (se 1 (by rfl) ⟨1614245, by rfl⟩ : syracuseStep 2152327 = 3228491) B3228491
theorem B2869769 : Blo 1911435 2869769 := bstep (se 2 (by rfl) ⟨1076163, by rfl⟩ : syracuseStep 2869769 = 2152327) B2152327
theorem B1913179 : Blo 1911435 1913179 := bstep (se 1 (by rfl) ⟨1434884, by rfl⟩ : syracuseStep 1913179 = 2869769) B2869769
theorem B9685493 : Blo 1911435 9685493 := bbase (se 5 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 9685493 = 908015) (by norm_num)
theorem B6456995 : Blo 1911435 6456995 := bstep (se 1 (by rfl) ⟨4842746, by rfl⟩ : syracuseStep 6456995 = 9685493) B9685493
theorem B4304663 : Blo 1911435 4304663 := bstep (se 1 (by rfl) ⟨3228497, by rfl⟩ : syracuseStep 4304663 = 6456995) B6456995
theorem B2869775 : Blo 1911435 2869775 := bstep (se 1 (by rfl) ⟨2152331, by rfl⟩ : syracuseStep 2869775 = 4304663) B4304663
theorem B1913183 : Blo 1911435 1913183 := bstep (se 1 (by rfl) ⟨1434887, by rfl⟩ : syracuseStep 1913183 = 2869775) B2869775
theorem B2869781 : Blo 1911435 2869781 := bbase (se 6 (by rfl) ⟨67260, by rfl⟩ : syracuseStep 2869781 = 134521) (by norm_num)
theorem B1913187 : Blo 1911435 1913187 := bstep (se 1 (by rfl) ⟨1434890, by rfl⟩ : syracuseStep 1913187 = 2869781) B2869781
theorem B16344341 : Blo 1911435 16344341 := bbase (se 6 (by rfl) ⟨383070, by rfl⟩ : syracuseStep 16344341 = 766141) (by norm_num)
theorem B10896227 : Blo 1911435 10896227 := bstep (se 1 (by rfl) ⟨8172170, by rfl⟩ : syracuseStep 10896227 = 16344341) B16344341
theorem B7264151 : Blo 1911435 7264151 := bstep (se 1 (by rfl) ⟨5448113, by rfl⟩ : syracuseStep 7264151 = 10896227) B10896227
theorem B4842767 : Blo 1911435 4842767 := bstep (se 1 (by rfl) ⟨3632075, by rfl⟩ : syracuseStep 4842767 = 7264151) B7264151
theorem B3228511 : Blo 1911435 3228511 := bstep (se 1 (by rfl) ⟨2421383, by rfl⟩ : syracuseStep 3228511 = 4842767) B4842767
theorem B4304681 : Blo 1911435 4304681 := bstep (se 2 (by rfl) ⟨1614255, by rfl⟩ : syracuseStep 4304681 = 3228511) B3228511
theorem B2869787 : Blo 1911435 2869787 := bstep (se 1 (by rfl) ⟨2152340, by rfl⟩ : syracuseStep 2869787 = 4304681) B4304681
theorem B1913191 : Blo 1911435 1913191 := bstep (se 1 (by rfl) ⟨1434893, by rfl⟩ : syracuseStep 1913191 = 2869787) B2869787
theorem B2152345 : Blo 1911435 2152345 := bbase (se 2 (by rfl) ⟨807129, by rfl⟩ : syracuseStep 2152345 = 1614259) (by norm_num)
theorem B2869793 : Blo 1911435 2869793 := bstep (se 2 (by rfl) ⟨1076172, by rfl⟩ : syracuseStep 2869793 = 2152345) B2152345
theorem B1913195 : Blo 1911435 1913195 := bstep (se 1 (by rfl) ⟨1434896, by rfl⟩ : syracuseStep 1913195 = 2869793) B2869793
theorem B7264181 : Blo 1911435 7264181 := bbase (se 5 (by rfl) ⟨340508, by rfl⟩ : syracuseStep 7264181 = 681017) (by norm_num)
theorem B4842787 : Blo 1911435 4842787 := bstep (se 1 (by rfl) ⟨3632090, by rfl⟩ : syracuseStep 4842787 = 7264181) B7264181
theorem B6457049 : Blo 1911435 6457049 := bstep (se 2 (by rfl) ⟨2421393, by rfl⟩ : syracuseStep 6457049 = 4842787) B4842787
theorem B4304699 : Blo 1911435 4304699 := bstep (se 1 (by rfl) ⟨3228524, by rfl⟩ : syracuseStep 4304699 = 6457049) B6457049
theorem B2869799 : Blo 1911435 2869799 := bstep (se 1 (by rfl) ⟨2152349, by rfl⟩ : syracuseStep 2869799 = 4304699) B4304699
theorem B1913199 : Blo 1911435 1913199 := bstep (se 1 (by rfl) ⟨1434899, by rfl⟩ : syracuseStep 1913199 = 2869799) B2869799
theorem B2869805 : Blo 1911435 2869805 := bbase (se 3 (by rfl) ⟨538088, by rfl⟩ : syracuseStep 2869805 = 1076177) (by norm_num)
theorem B1913203 : Blo 1911435 1913203 := bstep (se 1 (by rfl) ⟨1434902, by rfl⟩ : syracuseStep 1913203 = 2869805) B2869805
theorem B4304717 : Blo 1911435 4304717 := bbase (se 3 (by rfl) ⟨807134, by rfl⟩ : syracuseStep 4304717 = 1614269) (by norm_num)
theorem B2869811 : Blo 1911435 2869811 := bstep (se 1 (by rfl) ⟨2152358, by rfl⟩ : syracuseStep 2869811 = 4304717) B4304717
theorem B1913207 : Blo 1911435 1913207 := bstep (se 1 (by rfl) ⟨1434905, by rfl⟩ : syracuseStep 1913207 = 2869811) B2869811
theorem B2421409 : Blo 1911435 2421409 := bbase (se 2 (by rfl) ⟨908028, by rfl⟩ : syracuseStep 2421409 = 1816057) (by norm_num)
theorem B3228545 : Blo 1911435 3228545 := bstep (se 2 (by rfl) ⟨1210704, by rfl⟩ : syracuseStep 3228545 = 2421409) B2421409
theorem B2152363 : Blo 1911435 2152363 := bstep (se 1 (by rfl) ⟨1614272, by rfl⟩ : syracuseStep 2152363 = 3228545) B3228545
theorem B2869817 : Blo 1911435 2869817 := bstep (se 2 (by rfl) ⟨1076181, by rfl⟩ : syracuseStep 2869817 = 2152363) B2152363
theorem B1913211 : Blo 1911435 1913211 := bstep (se 1 (by rfl) ⟨1434908, by rfl⟩ : syracuseStep 1913211 = 2869817) B2869817
theorem B21792725 : Blo 1911435 21792725 := bbase (se 7 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 21792725 = 510767) (by norm_num)
theorem B14528483 : Blo 1911435 14528483 := bstep (se 1 (by rfl) ⟨10896362, by rfl⟩ : syracuseStep 14528483 = 21792725) B21792725
theorem B9685655 : Blo 1911435 9685655 := bstep (se 1 (by rfl) ⟨7264241, by rfl⟩ : syracuseStep 9685655 = 14528483) B14528483
theorem B6457103 : Blo 1911435 6457103 := bstep (se 1 (by rfl) ⟨4842827, by rfl⟩ : syracuseStep 6457103 = 9685655) B9685655
theorem B4304735 : Blo 1911435 4304735 := bstep (se 1 (by rfl) ⟨3228551, by rfl⟩ : syracuseStep 4304735 = 6457103) B6457103
theorem B2869823 : Blo 1911435 2869823 := bstep (se 1 (by rfl) ⟨2152367, by rfl⟩ : syracuseStep 2869823 = 4304735) B4304735
theorem B1913215 : Blo 1911435 1913215 := bstep (se 1 (by rfl) ⟨1434911, by rfl⟩ : syracuseStep 1913215 = 2869823) B2869823
theorem B2869829 : Blo 1911435 2869829 := bbase (se 4 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 2869829 = 538093) (by norm_num)
theorem B1913219 : Blo 1911435 1913219 := bstep (se 1 (by rfl) ⟨1434914, by rfl⟩ : syracuseStep 1913219 = 2869829) B2869829
theorem B3228565 : Blo 1911435 3228565 := bbase (se 6 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 3228565 = 151339) (by norm_num)
theorem B4304753 : Blo 1911435 4304753 := bstep (se 2 (by rfl) ⟨1614282, by rfl⟩ : syracuseStep 4304753 = 3228565) B3228565
theorem B2869835 : Blo 1911435 2869835 := bstep (se 1 (by rfl) ⟨2152376, by rfl⟩ : syracuseStep 2869835 = 4304753) B4304753
theorem B1913223 : Blo 1911435 1913223 := bstep (se 1 (by rfl) ⟨1434917, by rfl⟩ : syracuseStep 1913223 = 2869835) B2869835
theorem B2152381 : Blo 1911435 2152381 := bbase (se 3 (by rfl) ⟨403571, by rfl⟩ : syracuseStep 2152381 = 807143) (by norm_num)
theorem B2869841 : Blo 1911435 2869841 := bstep (se 2 (by rfl) ⟨1076190, by rfl⟩ : syracuseStep 2869841 = 2152381) B2152381
theorem B1913227 : Blo 1911435 1913227 := bstep (se 1 (by rfl) ⟨1434920, by rfl⟩ : syracuseStep 1913227 = 2869841) B2869841
theorem B6457157 : Blo 1911435 6457157 := bbase (se 4 (by rfl) ⟨605358, by rfl⟩ : syracuseStep 6457157 = 1210717) (by norm_num)
theorem B4304771 : Blo 1911435 4304771 := bstep (se 1 (by rfl) ⟨3228578, by rfl⟩ : syracuseStep 4304771 = 6457157) B6457157
theorem B2869847 : Blo 1911435 2869847 := bstep (se 1 (by rfl) ⟨2152385, by rfl⟩ : syracuseStep 2869847 = 4304771) B4304771
theorem B1913231 : Blo 1911435 1913231 := bstep (se 1 (by rfl) ⟨1434923, by rfl⟩ : syracuseStep 1913231 = 2869847) B2869847
theorem B2869853 : Blo 1911435 2869853 := bbase (se 3 (by rfl) ⟨538097, by rfl⟩ : syracuseStep 2869853 = 1076195) (by norm_num)
theorem B1913235 : Blo 1911435 1913235 := bstep (se 1 (by rfl) ⟨1434926, by rfl⟩ : syracuseStep 1913235 = 2869853) B2869853
theorem B4304789 : Blo 1911435 4304789 := bbase (se 6 (by rfl) ⟨100893, by rfl⟩ : syracuseStep 4304789 = 201787) (by norm_num)
theorem B2869859 : Blo 1911435 2869859 := bstep (se 1 (by rfl) ⟨2152394, by rfl⟩ : syracuseStep 2869859 = 4304789) B4304789
theorem B1913239 : Blo 1911435 1913239 := bstep (se 1 (by rfl) ⟨1434929, by rfl⟩ : syracuseStep 1913239 = 2869859) B2869859
theorem B4086197 : Blo 1911435 4086197 := bbase (se 5 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 4086197 = 383081) (by norm_num)
theorem B2724131 : Blo 1911435 2724131 := bstep (se 1 (by rfl) ⟨2043098, by rfl⟩ : syracuseStep 2724131 = 4086197) B4086197
theorem B7264349 : Blo 1911435 7264349 := bstep (se 3 (by rfl) ⟨1362065, by rfl⟩ : syracuseStep 7264349 = 2724131) B2724131
theorem B4842899 : Blo 1911435 4842899 := bstep (se 1 (by rfl) ⟨3632174, by rfl⟩ : syracuseStep 4842899 = 7264349) B7264349
theorem B3228599 : Blo 1911435 3228599 := bstep (se 1 (by rfl) ⟨2421449, by rfl⟩ : syracuseStep 3228599 = 4842899) B4842899
theorem B2152399 : Blo 1911435 2152399 := bstep (se 1 (by rfl) ⟨1614299, by rfl⟩ : syracuseStep 2152399 = 3228599) B3228599
theorem B2869865 : Blo 1911435 2869865 := bstep (se 2 (by rfl) ⟨1076199, by rfl⟩ : syracuseStep 2869865 = 2152399) B2152399
theorem B1913243 : Blo 1911435 1913243 := bstep (se 1 (by rfl) ⟨1434932, by rfl⟩ : syracuseStep 1913243 = 2869865) B2869865
theorem B35384597 : Blo 1911435 35384597 := bbase (se 6 (by rfl) ⟨829326, by rfl⟩ : syracuseStep 35384597 = 1658653) (by norm_num)
theorem B23589731 : Blo 1911435 23589731 := bstep (se 1 (by rfl) ⟨17692298, by rfl⟩ : syracuseStep 23589731 = 35384597) B35384597
theorem B15726487 : Blo 1911435 15726487 := bstep (se 1 (by rfl) ⟨11794865, by rfl⟩ : syracuseStep 15726487 = 23589731) B23589731
theorem B20968649 : Blo 1911435 20968649 := bstep (se 2 (by rfl) ⟨7863243, by rfl⟩ : syracuseStep 20968649 = 15726487) B15726487
theorem B13979099 : Blo 1911435 13979099 := bstep (se 1 (by rfl) ⟨10484324, by rfl⟩ : syracuseStep 13979099 = 20968649) B20968649
theorem B37277597 : Blo 1911435 37277597 := bstep (se 3 (by rfl) ⟨6989549, by rfl⟩ : syracuseStep 37277597 = 13979099) B13979099
theorem B24851731 : Blo 1911435 24851731 := bstep (se 1 (by rfl) ⟨18638798, by rfl⟩ : syracuseStep 24851731 = 37277597) B37277597
theorem B33135641 : Blo 1911435 33135641 := bstep (se 2 (by rfl) ⟨12425865, by rfl⟩ : syracuseStep 33135641 = 24851731) B24851731
theorem B22090427 : Blo 1911435 22090427 := bstep (se 1 (by rfl) ⟨16567820, by rfl⟩ : syracuseStep 22090427 = 33135641) B33135641
theorem B14726951 : Blo 1911435 14726951 := bstep (se 1 (by rfl) ⟨11045213, by rfl⟩ : syracuseStep 14726951 = 22090427) B22090427
theorem B9817967 : Blo 1911435 9817967 := bstep (se 1 (by rfl) ⟨7363475, by rfl⟩ : syracuseStep 9817967 = 14726951) B14726951
theorem B26181245 : Blo 1911435 26181245 := bstep (se 3 (by rfl) ⟨4908983, by rfl⟩ : syracuseStep 26181245 = 9817967) B9817967
theorem B17454163 : Blo 1911435 17454163 := bstep (se 1 (by rfl) ⟨13090622, by rfl⟩ : syracuseStep 17454163 = 26181245) B26181245
theorem B23272217 : Blo 1911435 23272217 := bstep (se 2 (by rfl) ⟨8727081, by rfl⟩ : syracuseStep 23272217 = 17454163) B17454163
theorem B15514811 : Blo 1911435 15514811 := bstep (se 1 (by rfl) ⟨11636108, by rfl⟩ : syracuseStep 15514811 = 23272217) B23272217
theorem B10343207 : Blo 1911435 10343207 := bstep (se 1 (by rfl) ⟨7757405, by rfl⟩ : syracuseStep 10343207 = 15514811) B15514811
theorem B6895471 : Blo 1911435 6895471 := bstep (se 1 (by rfl) ⟨5171603, by rfl⟩ : syracuseStep 6895471 = 10343207) B10343207
theorem B9193961 : Blo 1911435 9193961 := bstep (se 2 (by rfl) ⟨3447735, by rfl⟩ : syracuseStep 9193961 = 6895471) B6895471
theorem B6129307 : Blo 1911435 6129307 := bstep (se 1 (by rfl) ⟨4596980, by rfl⟩ : syracuseStep 6129307 = 9193961) B9193961
theorem B8172409 : Blo 1911435 8172409 := bstep (se 2 (by rfl) ⟨3064653, by rfl⟩ : syracuseStep 8172409 = 6129307) B6129307
theorem B10896545 : Blo 1911435 10896545 := bstep (se 2 (by rfl) ⟨4086204, by rfl⟩ : syracuseStep 10896545 = 8172409) B8172409
theorem B7264363 : Blo 1911435 7264363 := bstep (se 1 (by rfl) ⟨5448272, by rfl⟩ : syracuseStep 7264363 = 10896545) B10896545
theorem B9685817 : Blo 1911435 9685817 := bstep (se 2 (by rfl) ⟨3632181, by rfl⟩ : syracuseStep 9685817 = 7264363) B7264363
theorem B6457211 : Blo 1911435 6457211 := bstep (se 1 (by rfl) ⟨4842908, by rfl⟩ : syracuseStep 6457211 = 9685817) B9685817
theorem B4304807 : Blo 1911435 4304807 := bstep (se 1 (by rfl) ⟨3228605, by rfl⟩ : syracuseStep 4304807 = 6457211) B6457211
theorem B2869871 : Blo 1911435 2869871 := bstep (se 1 (by rfl) ⟨2152403, by rfl⟩ : syracuseStep 2869871 = 4304807) B4304807
theorem B1913247 : Blo 1911435 1913247 := bstep (se 1 (by rfl) ⟨1434935, by rfl⟩ : syracuseStep 1913247 = 2869871) B2869871
theorem B2869877 : Blo 1911435 2869877 := bbase (se 5 (by rfl) ⟨134525, by rfl⟩ : syracuseStep 2869877 = 269051) (by norm_num)
theorem B1913251 : Blo 1911435 1913251 := bstep (se 1 (by rfl) ⟨1434938, by rfl⟩ : syracuseStep 1913251 = 2869877) B2869877
theorem B3632197 : Blo 1911435 3632197 := bbase (se 4 (by rfl) ⟨340518, by rfl⟩ : syracuseStep 3632197 = 681037) (by norm_num)
theorem B4842929 : Blo 1911435 4842929 := bstep (se 2 (by rfl) ⟨1816098, by rfl⟩ : syracuseStep 4842929 = 3632197) B3632197
theorem B3228619 : Blo 1911435 3228619 := bstep (se 1 (by rfl) ⟨2421464, by rfl⟩ : syracuseStep 3228619 = 4842929) B4842929
theorem B4304825 : Blo 1911435 4304825 := bstep (se 2 (by rfl) ⟨1614309, by rfl⟩ : syracuseStep 4304825 = 3228619) B3228619
theorem B2869883 : Blo 1911435 2869883 := bstep (se 1 (by rfl) ⟨2152412, by rfl⟩ : syracuseStep 2869883 = 4304825) B4304825
theorem B1913255 : Blo 1911435 1913255 := bstep (se 1 (by rfl) ⟨1434941, by rfl⟩ : syracuseStep 1913255 = 2869883) B2869883
theorem B2152417 : Blo 1911435 2152417 := bbase (se 2 (by rfl) ⟨807156, by rfl⟩ : syracuseStep 2152417 = 1614313) (by norm_num)
theorem B2869889 : Blo 1911435 2869889 := bstep (se 2 (by rfl) ⟨1076208, by rfl⟩ : syracuseStep 2869889 = 2152417) B2152417
theorem B1913259 : Blo 1911435 1913259 := bstep (se 1 (by rfl) ⟨1434944, by rfl⟩ : syracuseStep 1913259 = 2869889) B2869889
theorem B4842949 : Blo 1911435 4842949 := bbase (se 4 (by rfl) ⟨454026, by rfl⟩ : syracuseStep 4842949 = 908053) (by norm_num)
theorem B6457265 : Blo 1911435 6457265 := bstep (se 2 (by rfl) ⟨2421474, by rfl⟩ : syracuseStep 6457265 = 4842949) B4842949
theorem B4304843 : Blo 1911435 4304843 := bstep (se 1 (by rfl) ⟨3228632, by rfl⟩ : syracuseStep 4304843 = 6457265) B6457265
theorem B2869895 : Blo 1911435 2869895 := bstep (se 1 (by rfl) ⟨2152421, by rfl⟩ : syracuseStep 2869895 = 4304843) B4304843
theorem B1913263 : Blo 1911435 1913263 := bstep (se 1 (by rfl) ⟨1434947, by rfl⟩ : syracuseStep 1913263 = 2869895) B2869895
theorem B2869901 : Blo 1911435 2869901 := bbase (se 3 (by rfl) ⟨538106, by rfl⟩ : syracuseStep 2869901 = 1076213) (by norm_num)
theorem B1913267 : Blo 1911435 1913267 := bstep (se 1 (by rfl) ⟨1434950, by rfl⟩ : syracuseStep 1913267 = 2869901) B2869901
theorem B4304861 : Blo 1911435 4304861 := bbase (se 3 (by rfl) ⟨807161, by rfl⟩ : syracuseStep 4304861 = 1614323) (by norm_num)
theorem B2869907 : Blo 1911435 2869907 := bstep (se 1 (by rfl) ⟨2152430, by rfl⟩ : syracuseStep 2869907 = 4304861) B4304861
theorem B1913271 : Blo 1911435 1913271 := bstep (se 1 (by rfl) ⟨1434953, by rfl⟩ : syracuseStep 1913271 = 2869907) B2869907
theorem B3228653 : Blo 1911435 3228653 := bbase (se 3 (by rfl) ⟨605372, by rfl⟩ : syracuseStep 3228653 = 1210745) (by norm_num)
theorem B2152435 : Blo 1911435 2152435 := bstep (se 1 (by rfl) ⟨1614326, by rfl⟩ : syracuseStep 2152435 = 3228653) B3228653
theorem B2869913 : Blo 1911435 2869913 := bstep (se 2 (by rfl) ⟨1076217, by rfl⟩ : syracuseStep 2869913 = 2152435) B2152435
theorem B1913275 : Blo 1911435 1913275 := bstep (se 1 (by rfl) ⟨1434956, by rfl⟩ : syracuseStep 1913275 = 2869913) B2869913
theorem B2585845 : Blo 1911435 2585845 := bbase (se 5 (by rfl) ⟨121211, by rfl⟩ : syracuseStep 2585845 = 242423) (by norm_num)
theorem B3447793 : Blo 1911435 3447793 := bstep (se 2 (by rfl) ⟨1292922, by rfl⟩ : syracuseStep 3447793 = 2585845) B2585845
theorem B4597057 : Blo 1911435 4597057 := bstep (se 2 (by rfl) ⟨1723896, by rfl⟩ : syracuseStep 4597057 = 3447793) B3447793
theorem B24517637 : Blo 1911435 24517637 := bstep (se 4 (by rfl) ⟨2298528, by rfl⟩ : syracuseStep 24517637 = 4597057) B4597057
theorem B16345091 : Blo 1911435 16345091 := bstep (se 1 (by rfl) ⟨12258818, by rfl⟩ : syracuseStep 16345091 = 24517637) B24517637
theorem B10896727 : Blo 1911435 10896727 := bstep (se 1 (by rfl) ⟨8172545, by rfl⟩ : syracuseStep 10896727 = 16345091) B16345091
theorem B14528969 : Blo 1911435 14528969 := bstep (se 2 (by rfl) ⟨5448363, by rfl⟩ : syracuseStep 14528969 = 10896727) B10896727
theorem B9685979 : Blo 1911435 9685979 := bstep (se 1 (by rfl) ⟨7264484, by rfl⟩ : syracuseStep 9685979 = 14528969) B14528969
theorem B6457319 : Blo 1911435 6457319 := bstep (se 1 (by rfl) ⟨4842989, by rfl⟩ : syracuseStep 6457319 = 9685979) B9685979
theorem B4304879 : Blo 1911435 4304879 := bstep (se 1 (by rfl) ⟨3228659, by rfl⟩ : syracuseStep 4304879 = 6457319) B6457319
theorem B2869919 : Blo 1911435 2869919 := bstep (se 1 (by rfl) ⟨2152439, by rfl⟩ : syracuseStep 2869919 = 4304879) B4304879
theorem B1913279 : Blo 1911435 1913279 := bstep (se 1 (by rfl) ⟨1434959, by rfl⟩ : syracuseStep 1913279 = 2869919) B2869919
theorem B2869925 : Blo 1911435 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B1913283 : Blo 1911435 1913283 := bstep (se 1 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 1913283 = 2869925) B2869925
theorem B2421505 : Blo 1911435 2421505 := bbase (se 2 (by rfl) ⟨908064, by rfl⟩ : syracuseStep 2421505 = 1816129) (by norm_num)
theorem B3228673 : Blo 1911435 3228673 := bstep (se 2 (by rfl) ⟨1210752, by rfl⟩ : syracuseStep 3228673 = 2421505) B2421505
theorem B4304897 : Blo 1911435 4304897 := bstep (se 2 (by rfl) ⟨1614336, by rfl⟩ : syracuseStep 4304897 = 3228673) B3228673
theorem B2869931 : Blo 1911435 2869931 := bstep (se 1 (by rfl) ⟨2152448, by rfl⟩ : syracuseStep 2869931 = 4304897) B4304897
theorem B1913287 : Blo 1911435 1913287 := bstep (se 1 (by rfl) ⟨1434965, by rfl⟩ : syracuseStep 1913287 = 2869931) B2869931
theorem B2152453 : Blo 1911435 2152453 := bbase (se 4 (by rfl) ⟨201792, by rfl⟩ : syracuseStep 2152453 = 403585) (by norm_num)
theorem B2869937 : Blo 1911435 2869937 := bstep (se 2 (by rfl) ⟨1076226, by rfl⟩ : syracuseStep 2869937 = 2152453) B2152453
theorem B1913291 : Blo 1911435 1913291 := bstep (se 1 (by rfl) ⟨1434968, by rfl⟩ : syracuseStep 1913291 = 2869937) B2869937
theorem B2724205 : Blo 1911435 2724205 := bbase (se 3 (by rfl) ⟨510788, by rfl⟩ : syracuseStep 2724205 = 1021577) (by norm_num)
theorem B3632273 : Blo 1911435 3632273 := bstep (se 2 (by rfl) ⟨1362102, by rfl⟩ : syracuseStep 3632273 = 2724205) B2724205
theorem B2421515 : Blo 1911435 2421515 := bstep (se 1 (by rfl) ⟨1816136, by rfl⟩ : syracuseStep 2421515 = 3632273) B3632273
theorem B6457373 : Blo 1911435 6457373 := bstep (se 3 (by rfl) ⟨1210757, by rfl⟩ : syracuseStep 6457373 = 2421515) B2421515
theorem B4304915 : Blo 1911435 4304915 := bstep (se 1 (by rfl) ⟨3228686, by rfl⟩ : syracuseStep 4304915 = 6457373) B6457373
theorem B2869943 : Blo 1911435 2869943 := bstep (se 1 (by rfl) ⟨2152457, by rfl⟩ : syracuseStep 2869943 = 4304915) B4304915
theorem B1913295 : Blo 1911435 1913295 := bstep (se 1 (by rfl) ⟨1434971, by rfl⟩ : syracuseStep 1913295 = 2869943) B2869943
theorem B2869949 : Blo 1911435 2869949 := bbase (se 3 (by rfl) ⟨538115, by rfl⟩ : syracuseStep 2869949 = 1076231) (by norm_num)
theorem B1913299 : Blo 1911435 1913299 := bstep (se 1 (by rfl) ⟨1434974, by rfl⟩ : syracuseStep 1913299 = 2869949) B2869949
theorem B4304933 : Blo 1911435 4304933 := bbase (se 4 (by rfl) ⟨403587, by rfl⟩ : syracuseStep 4304933 = 807175) (by norm_num)
theorem B2869955 : Blo 1911435 2869955 := bstep (se 1 (by rfl) ⟨2152466, by rfl⟩ : syracuseStep 2869955 = 4304933) B4304933
theorem B1913303 : Blo 1911435 1913303 := bstep (se 1 (by rfl) ⟨1434977, by rfl⟩ : syracuseStep 1913303 = 2869955) B2869955
theorem B4843061 : Blo 1911435 4843061 := bbase (se 5 (by rfl) ⟨227018, by rfl⟩ : syracuseStep 4843061 = 454037) (by norm_num)
theorem B3228707 : Blo 1911435 3228707 := bstep (se 1 (by rfl) ⟨2421530, by rfl⟩ : syracuseStep 3228707 = 4843061) B4843061
theorem B2152471 : Blo 1911435 2152471 := bstep (se 1 (by rfl) ⟨1614353, by rfl⟩ : syracuseStep 2152471 = 3228707) B3228707
theorem B2869961 : Blo 1911435 2869961 := bstep (se 2 (by rfl) ⟨1076235, by rfl⟩ : syracuseStep 2869961 = 2152471) B2152471
theorem B1913307 : Blo 1911435 1913307 := bstep (se 1 (by rfl) ⟨1434980, by rfl⟩ : syracuseStep 1913307 = 2869961) B2869961
theorem B2909125 : Blo 1911435 2909125 := bbase (se 4 (by rfl) ⟨272730, by rfl⟩ : syracuseStep 2909125 = 545461) (by norm_num)
theorem B3878833 : Blo 1911435 3878833 := bstep (se 2 (by rfl) ⟨1454562, by rfl⟩ : syracuseStep 3878833 = 2909125) B2909125
theorem B5171777 : Blo 1911435 5171777 := bstep (se 2 (by rfl) ⟨1939416, by rfl⟩ : syracuseStep 5171777 = 3878833) B3878833
theorem B3447851 : Blo 1911435 3447851 := bstep (se 1 (by rfl) ⟨2585888, by rfl⟩ : syracuseStep 3447851 = 5171777) B5171777
theorem B9194269 : Blo 1911435 9194269 := bstep (se 3 (by rfl) ⟨1723925, by rfl⟩ : syracuseStep 9194269 = 3447851) B3447851
theorem B12259025 : Blo 1911435 12259025 := bstep (se 2 (by rfl) ⟨4597134, by rfl⟩ : syracuseStep 12259025 = 9194269) B9194269
theorem B8172683 : Blo 1911435 8172683 := bstep (se 1 (by rfl) ⟨6129512, by rfl⟩ : syracuseStep 8172683 = 12259025) B12259025
theorem B5448455 : Blo 1911435 5448455 := bstep (se 1 (by rfl) ⟨4086341, by rfl⟩ : syracuseStep 5448455 = 8172683) B8172683
theorem B3632303 : Blo 1911435 3632303 := bstep (se 1 (by rfl) ⟨2724227, by rfl⟩ : syracuseStep 3632303 = 5448455) B5448455
theorem B9686141 : Blo 1911435 9686141 := bstep (se 3 (by rfl) ⟨1816151, by rfl⟩ : syracuseStep 9686141 = 3632303) B3632303
theorem B6457427 : Blo 1911435 6457427 := bstep (se 1 (by rfl) ⟨4843070, by rfl⟩ : syracuseStep 6457427 = 9686141) B9686141
theorem B4304951 : Blo 1911435 4304951 := bstep (se 1 (by rfl) ⟨3228713, by rfl⟩ : syracuseStep 4304951 = 6457427) B6457427
theorem B2869967 : Blo 1911435 2869967 := bstep (se 1 (by rfl) ⟨2152475, by rfl⟩ : syracuseStep 2869967 = 4304951) B4304951
theorem B1913311 : Blo 1911435 1913311 := bstep (se 1 (by rfl) ⟨1434983, by rfl⟩ : syracuseStep 1913311 = 2869967) B2869967
theorem B2869973 : Blo 1911435 2869973 := bbase (se 7 (by rfl) ⟨33632, by rfl⟩ : syracuseStep 2869973 = 67265) (by norm_num)
theorem B1913315 : Blo 1911435 1913315 := bstep (se 1 (by rfl) ⟨1434986, by rfl⟩ : syracuseStep 1913315 = 2869973) B2869973
theorem B9194309 : Blo 1911435 9194309 := bbase (se 4 (by rfl) ⟨861966, by rfl⟩ : syracuseStep 9194309 = 1723933) (by norm_num)
theorem B6129539 : Blo 1911435 6129539 := bstep (se 1 (by rfl) ⟨4597154, by rfl⟩ : syracuseStep 6129539 = 9194309) B9194309
theorem B4086359 : Blo 1911435 4086359 := bstep (se 1 (by rfl) ⟨3064769, by rfl⟩ : syracuseStep 4086359 = 6129539) B6129539
theorem B2724239 : Blo 1911435 2724239 := bstep (se 1 (by rfl) ⟨2043179, by rfl⟩ : syracuseStep 2724239 = 4086359) B4086359
theorem B7264637 : Blo 1911435 7264637 := bstep (se 3 (by rfl) ⟨1362119, by rfl⟩ : syracuseStep 7264637 = 2724239) B2724239
theorem B4843091 : Blo 1911435 4843091 := bstep (se 1 (by rfl) ⟨3632318, by rfl⟩ : syracuseStep 4843091 = 7264637) B7264637
theorem B3228727 : Blo 1911435 3228727 := bstep (se 1 (by rfl) ⟨2421545, by rfl⟩ : syracuseStep 3228727 = 4843091) B4843091
theorem B4304969 : Blo 1911435 4304969 := bstep (se 2 (by rfl) ⟨1614363, by rfl⟩ : syracuseStep 4304969 = 3228727) B3228727
theorem B2869979 : Blo 1911435 2869979 := bstep (se 1 (by rfl) ⟨2152484, by rfl⟩ : syracuseStep 2869979 = 4304969) B4304969
theorem B1913319 : Blo 1911435 1913319 := bstep (se 1 (by rfl) ⟨1434989, by rfl⟩ : syracuseStep 1913319 = 2869979) B2869979
theorem B2152489 : Blo 1911435 2152489 := bbase (se 2 (by rfl) ⟨807183, by rfl⟩ : syracuseStep 2152489 = 1614367) (by norm_num)
theorem B2869985 : Blo 1911435 2869985 := bstep (se 2 (by rfl) ⟨1076244, by rfl⟩ : syracuseStep 2869985 = 2152489) B2152489
theorem B1913323 : Blo 1911435 1913323 := bstep (se 1 (by rfl) ⟨1434992, by rfl⟩ : syracuseStep 1913323 = 2869985) B2869985
theorem B4909189 : Blo 1911435 4909189 := bbase (se 4 (by rfl) ⟨460236, by rfl⟩ : syracuseStep 4909189 = 920473) (by norm_num)
theorem B6545585 : Blo 1911435 6545585 := bstep (se 2 (by rfl) ⟨2454594, by rfl⟩ : syracuseStep 6545585 = 4909189) B4909189
theorem B4363723 : Blo 1911435 4363723 := bstep (se 1 (by rfl) ⟨3272792, by rfl⟩ : syracuseStep 4363723 = 6545585) B6545585
theorem B23273189 : Blo 1911435 23273189 := bstep (se 4 (by rfl) ⟨2181861, by rfl⟩ : syracuseStep 23273189 = 4363723) B4363723
theorem B15515459 : Blo 1911435 15515459 := bstep (se 1 (by rfl) ⟨11636594, by rfl⟩ : syracuseStep 15515459 = 23273189) B23273189
theorem B10343639 : Blo 1911435 10343639 := bstep (se 1 (by rfl) ⟨7757729, by rfl⟩ : syracuseStep 10343639 = 15515459) B15515459
theorem B27583037 : Blo 1911435 27583037 := bstep (se 3 (by rfl) ⟨5171819, by rfl⟩ : syracuseStep 27583037 = 10343639) B10343639
theorem B18388691 : Blo 1911435 18388691 := bstep (se 1 (by rfl) ⟨13791518, by rfl⟩ : syracuseStep 18388691 = 27583037) B27583037
theorem B12259127 : Blo 1911435 12259127 := bstep (se 1 (by rfl) ⟨9194345, by rfl⟩ : syracuseStep 12259127 = 18388691) B18388691
theorem B8172751 : Blo 1911435 8172751 := bstep (se 1 (by rfl) ⟨6129563, by rfl⟩ : syracuseStep 8172751 = 12259127) B12259127
theorem B10897001 : Blo 1911435 10897001 := bstep (se 2 (by rfl) ⟨4086375, by rfl⟩ : syracuseStep 10897001 = 8172751) B8172751
theorem B7264667 : Blo 1911435 7264667 := bstep (se 1 (by rfl) ⟨5448500, by rfl⟩ : syracuseStep 7264667 = 10897001) B10897001
theorem B4843111 : Blo 1911435 4843111 := bstep (se 1 (by rfl) ⟨3632333, by rfl⟩ : syracuseStep 4843111 = 7264667) B7264667
theorem B6457481 : Blo 1911435 6457481 := bstep (se 2 (by rfl) ⟨2421555, by rfl⟩ : syracuseStep 6457481 = 4843111) B4843111
theorem B4304987 : Blo 1911435 4304987 := bstep (se 1 (by rfl) ⟨3228740, by rfl⟩ : syracuseStep 4304987 = 6457481) B6457481
theorem B2869991 : Blo 1911435 2869991 := bstep (se 1 (by rfl) ⟨2152493, by rfl⟩ : syracuseStep 2869991 = 4304987) B4304987
theorem B1913327 : Blo 1911435 1913327 := bstep (se 1 (by rfl) ⟨1434995, by rfl⟩ : syracuseStep 1913327 = 2869991) B2869991
theorem B2869997 : Blo 1911435 2869997 := bbase (se 3 (by rfl) ⟨538124, by rfl⟩ : syracuseStep 2869997 = 1076249) (by norm_num)
theorem B1913331 : Blo 1911435 1913331 := bstep (se 1 (by rfl) ⟨1434998, by rfl⟩ : syracuseStep 1913331 = 2869997) B2869997
theorem B4305005 : Blo 1911435 4305005 := bbase (se 3 (by rfl) ⟨807188, by rfl⟩ : syracuseStep 4305005 = 1614377) (by norm_num)
theorem B2870003 : Blo 1911435 2870003 := bstep (se 1 (by rfl) ⟨2152502, by rfl⟩ : syracuseStep 2870003 = 4305005) B4305005
theorem B1913335 : Blo 1911435 1913335 := bstep (se 1 (by rfl) ⟨1435001, by rfl⟩ : syracuseStep 1913335 = 2870003) B2870003
theorem B3632357 : Blo 1911435 3632357 := bbase (se 4 (by rfl) ⟨340533, by rfl⟩ : syracuseStep 3632357 = 681067) (by norm_num)
theorem B2421571 : Blo 1911435 2421571 := bstep (se 1 (by rfl) ⟨1816178, by rfl⟩ : syracuseStep 2421571 = 3632357) B3632357
theorem B3228761 : Blo 1911435 3228761 := bstep (se 2 (by rfl) ⟨1210785, by rfl⟩ : syracuseStep 3228761 = 2421571) B2421571
theorem B2152507 : Blo 1911435 2152507 := bstep (se 1 (by rfl) ⟨1614380, by rfl⟩ : syracuseStep 2152507 = 3228761) B3228761
theorem B2870009 : Blo 1911435 2870009 := bstep (se 2 (by rfl) ⟨1076253, by rfl⟩ : syracuseStep 2870009 = 2152507) B2152507
theorem B1913339 : Blo 1911435 1913339 := bstep (se 1 (by rfl) ⟨1435004, by rfl⟩ : syracuseStep 1913339 = 2870009) B2870009
theorem B36777685 : Blo 1911435 36777685 := bbase (se 7 (by rfl) ⟨430988, by rfl⟩ : syracuseStep 36777685 = 861977) (by norm_num)
theorem B49036913 : Blo 1911435 49036913 := bstep (se 2 (by rfl) ⟨18388842, by rfl⟩ : syracuseStep 49036913 = 36777685) B36777685
theorem B32691275 : Blo 1911435 32691275 := bstep (se 1 (by rfl) ⟨24518456, by rfl⟩ : syracuseStep 32691275 = 49036913) B49036913
theorem B21794183 : Blo 1911435 21794183 := bstep (se 1 (by rfl) ⟨16345637, by rfl⟩ : syracuseStep 21794183 = 32691275) B32691275
theorem B14529455 : Blo 1911435 14529455 := bstep (se 1 (by rfl) ⟨10897091, by rfl⟩ : syracuseStep 14529455 = 21794183) B21794183
theorem B9686303 : Blo 1911435 9686303 := bstep (se 1 (by rfl) ⟨7264727, by rfl⟩ : syracuseStep 9686303 = 14529455) B14529455
theorem B6457535 : Blo 1911435 6457535 := bstep (se 1 (by rfl) ⟨4843151, by rfl⟩ : syracuseStep 6457535 = 9686303) B9686303
theorem B4305023 : Blo 1911435 4305023 := bstep (se 1 (by rfl) ⟨3228767, by rfl⟩ : syracuseStep 4305023 = 6457535) B6457535
theorem B2870015 : Blo 1911435 2870015 := bstep (se 1 (by rfl) ⟨2152511, by rfl⟩ : syracuseStep 2870015 = 4305023) B4305023
theorem B1913343 : Blo 1911435 1913343 := bstep (se 1 (by rfl) ⟨1435007, by rfl⟩ : syracuseStep 1913343 = 2870015) B2870015
theorem B2870021 : Blo 1911435 2870021 := bbase (se 4 (by rfl) ⟨269064, by rfl⟩ : syracuseStep 2870021 = 538129) (by norm_num)
theorem B1913347 : Blo 1911435 1913347 := bstep (se 1 (by rfl) ⟨1435010, by rfl⟩ : syracuseStep 1913347 = 2870021) B2870021
theorem B3228781 : Blo 1911435 3228781 := bbase (se 3 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 3228781 = 1210793) (by norm_num)
theorem B4305041 : Blo 1911435 4305041 := bstep (se 2 (by rfl) ⟨1614390, by rfl⟩ : syracuseStep 4305041 = 3228781) B3228781
theorem B2870027 : Blo 1911435 2870027 := bstep (se 1 (by rfl) ⟨2152520, by rfl⟩ : syracuseStep 2870027 = 4305041) B4305041
theorem B1913351 : Blo 1911435 1913351 := bstep (se 1 (by rfl) ⟨1435013, by rfl⟩ : syracuseStep 1913351 = 2870027) B2870027
theorem B2152525 : Blo 1911435 2152525 := bbase (se 3 (by rfl) ⟨403598, by rfl⟩ : syracuseStep 2152525 = 807197) (by norm_num)
theorem B2870033 : Blo 1911435 2870033 := bstep (se 2 (by rfl) ⟨1076262, by rfl⟩ : syracuseStep 2870033 = 2152525) B2152525
theorem B1913355 : Blo 1911435 1913355 := bstep (se 1 (by rfl) ⟨1435016, by rfl⟩ : syracuseStep 1913355 = 2870033) B2870033
theorem B6457589 : Blo 1911435 6457589 := bbase (se 5 (by rfl) ⟨302699, by rfl⟩ : syracuseStep 6457589 = 605399) (by norm_num)
theorem B4305059 : Blo 1911435 4305059 := bstep (se 1 (by rfl) ⟨3228794, by rfl⟩ : syracuseStep 4305059 = 6457589) B6457589
theorem B2870039 : Blo 1911435 2870039 := bstep (se 1 (by rfl) ⟨2152529, by rfl⟩ : syracuseStep 2870039 = 4305059) B4305059
theorem B1913359 : Blo 1911435 1913359 := bstep (se 1 (by rfl) ⟨1435019, by rfl⟩ : syracuseStep 1913359 = 2870039) B2870039
theorem B2870045 : Blo 1911435 2870045 := bbase (se 3 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 2870045 = 1076267) (by norm_num)
theorem B1913363 : Blo 1911435 1913363 := bstep (se 1 (by rfl) ⟨1435022, by rfl⟩ : syracuseStep 1913363 = 2870045) B2870045
theorem B4305077 : Blo 1911435 4305077 := bbase (se 5 (by rfl) ⟨201800, by rfl⟩ : syracuseStep 4305077 = 403601) (by norm_num)
theorem B2870051 : Blo 1911435 2870051 := bstep (se 1 (by rfl) ⟨2152538, by rfl⟩ : syracuseStep 2870051 = 4305077) B4305077
theorem B1913367 : Blo 1911435 1913367 := bstep (se 1 (by rfl) ⟨1435025, by rfl⟩ : syracuseStep 1913367 = 2870051) B2870051
theorem B3064853 : Blo 1911435 3064853 := bbase (se 6 (by rfl) ⟨71832, by rfl⟩ : syracuseStep 3064853 = 143665) (by norm_num)
theorem B2043235 : Blo 1911435 2043235 := bstep (se 1 (by rfl) ⟨1532426, by rfl⟩ : syracuseStep 2043235 = 3064853) B3064853
theorem B10897253 : Blo 1911435 10897253 := bstep (se 4 (by rfl) ⟨1021617, by rfl⟩ : syracuseStep 10897253 = 2043235) B2043235
theorem B7264835 : Blo 1911435 7264835 := bstep (se 1 (by rfl) ⟨5448626, by rfl⟩ : syracuseStep 7264835 = 10897253) B10897253
theorem B4843223 : Blo 1911435 4843223 := bstep (se 1 (by rfl) ⟨3632417, by rfl⟩ : syracuseStep 4843223 = 7264835) B7264835
theorem B3228815 : Blo 1911435 3228815 := bstep (se 1 (by rfl) ⟨2421611, by rfl⟩ : syracuseStep 3228815 = 4843223) B4843223
theorem B2152543 : Blo 1911435 2152543 := bstep (se 1 (by rfl) ⟨1614407, by rfl⟩ : syracuseStep 2152543 = 3228815) B3228815
theorem B2870057 : Blo 1911435 2870057 := bstep (se 2 (by rfl) ⟨1076271, by rfl⟩ : syracuseStep 2870057 = 2152543) B2152543
theorem B1913371 : Blo 1911435 1913371 := bstep (se 1 (by rfl) ⟨1435028, by rfl⟩ : syracuseStep 1913371 = 2870057) B2870057
theorem B4660013 : Blo 1911435 4660013 := bbase (se 3 (by rfl) ⟨873752, by rfl⟩ : syracuseStep 4660013 = 1747505) (by norm_num)
theorem B12426701 : Blo 1911435 12426701 := bstep (se 3 (by rfl) ⟨2330006, by rfl⟩ : syracuseStep 12426701 = 4660013) B4660013
theorem B33137869 : Blo 1911435 33137869 := bstep (se 3 (by rfl) ⟨6213350, by rfl⟩ : syracuseStep 33137869 = 12426701) B12426701
theorem B44183825 : Blo 1911435 44183825 := bstep (se 2 (by rfl) ⟨16568934, by rfl⟩ : syracuseStep 44183825 = 33137869) B33137869
theorem B29455883 : Blo 1911435 29455883 := bstep (se 1 (by rfl) ⟨22091912, by rfl⟩ : syracuseStep 29455883 = 44183825) B44183825
theorem B19637255 : Blo 1911435 19637255 := bstep (se 1 (by rfl) ⟨14727941, by rfl⟩ : syracuseStep 19637255 = 29455883) B29455883
theorem B13091503 : Blo 1911435 13091503 := bstep (se 1 (by rfl) ⟨9818627, by rfl⟩ : syracuseStep 13091503 = 19637255) B19637255
theorem B17455337 : Blo 1911435 17455337 := bstep (se 2 (by rfl) ⟨6545751, by rfl⟩ : syracuseStep 17455337 = 13091503) B13091503
theorem B11636891 : Blo 1911435 11636891 := bstep (se 1 (by rfl) ⟨8727668, by rfl⟩ : syracuseStep 11636891 = 17455337) B17455337
theorem B7757927 : Blo 1911435 7757927 := bstep (se 1 (by rfl) ⟨5818445, by rfl⟩ : syracuseStep 7757927 = 11636891) B11636891
theorem B5171951 : Blo 1911435 5171951 := bstep (se 1 (by rfl) ⟨3878963, by rfl⟩ : syracuseStep 5171951 = 7757927) B7757927
theorem B3447967 : Blo 1911435 3447967 := bstep (se 1 (by rfl) ⟨2585975, by rfl⟩ : syracuseStep 3447967 = 5171951) B5171951
theorem B4597289 : Blo 1911435 4597289 := bstep (se 2 (by rfl) ⟨1723983, by rfl⟩ : syracuseStep 4597289 = 3447967) B3447967
theorem B3064859 : Blo 1911435 3064859 := bstep (se 1 (by rfl) ⟨2298644, by rfl⟩ : syracuseStep 3064859 = 4597289) B4597289
theorem B2043239 : Blo 1911435 2043239 := bstep (se 1 (by rfl) ⟨1532429, by rfl⟩ : syracuseStep 2043239 = 3064859) B3064859
theorem B5448637 : Blo 1911435 5448637 := bstep (se 3 (by rfl) ⟨1021619, by rfl⟩ : syracuseStep 5448637 = 2043239) B2043239
theorem B7264849 : Blo 1911435 7264849 := bstep (se 2 (by rfl) ⟨2724318, by rfl⟩ : syracuseStep 7264849 = 5448637) B5448637
theorem B9686465 : Blo 1911435 9686465 := bstep (se 2 (by rfl) ⟨3632424, by rfl⟩ : syracuseStep 9686465 = 7264849) B7264849
theorem B6457643 : Blo 1911435 6457643 := bstep (se 1 (by rfl) ⟨4843232, by rfl⟩ : syracuseStep 6457643 = 9686465) B9686465
theorem B4305095 : Blo 1911435 4305095 := bstep (se 1 (by rfl) ⟨3228821, by rfl⟩ : syracuseStep 4305095 = 6457643) B6457643
theorem B2870063 : Blo 1911435 2870063 := bstep (se 1 (by rfl) ⟨2152547, by rfl⟩ : syracuseStep 2870063 = 4305095) B4305095
theorem B1913375 : Blo 1911435 1913375 := bstep (se 1 (by rfl) ⟨1435031, by rfl⟩ : syracuseStep 1913375 = 2870063) B2870063
theorem B2870069 : Blo 1911435 2870069 := bbase (se 5 (by rfl) ⟨134534, by rfl⟩ : syracuseStep 2870069 = 269069) (by norm_num)
theorem B1913379 : Blo 1911435 1913379 := bstep (se 1 (by rfl) ⟨1435034, by rfl⟩ : syracuseStep 1913379 = 2870069) B2870069
theorem B4843253 : Blo 1911435 4843253 := bbase (se 5 (by rfl) ⟨227027, by rfl⟩ : syracuseStep 4843253 = 454055) (by norm_num)
theorem B3228835 : Blo 1911435 3228835 := bstep (se 1 (by rfl) ⟨2421626, by rfl⟩ : syracuseStep 3228835 = 4843253) B4843253
theorem B4305113 : Blo 1911435 4305113 := bstep (se 2 (by rfl) ⟨1614417, by rfl⟩ : syracuseStep 4305113 = 3228835) B3228835
theorem B2870075 : Blo 1911435 2870075 := bstep (se 1 (by rfl) ⟨2152556, by rfl⟩ : syracuseStep 2870075 = 4305113) B4305113
theorem B1913383 : Blo 1911435 1913383 := bstep (se 1 (by rfl) ⟨1435037, by rfl⟩ : syracuseStep 1913383 = 2870075) B2870075
theorem B2152561 : Blo 1911435 2152561 := bbase (se 2 (by rfl) ⟨807210, by rfl⟩ : syracuseStep 2152561 = 1614421) (by norm_num)
theorem B2870081 : Blo 1911435 2870081 := bstep (se 2 (by rfl) ⟨1076280, by rfl⟩ : syracuseStep 2870081 = 2152561) B2152561
theorem B1913387 : Blo 1911435 1913387 := bstep (se 1 (by rfl) ⟨1435040, by rfl⟩ : syracuseStep 1913387 = 2870081) B2870081
theorem B4142269 : Blo 1911435 4142269 := bbase (se 3 (by rfl) ⟨776675, by rfl⟩ : syracuseStep 4142269 = 1553351) (by norm_num)
theorem B5523025 : Blo 1911435 5523025 := bstep (se 2 (by rfl) ⟨2071134, by rfl⟩ : syracuseStep 5523025 = 4142269) B4142269
theorem B7364033 : Blo 1911435 7364033 := bstep (se 2 (by rfl) ⟨2761512, by rfl⟩ : syracuseStep 7364033 = 5523025) B5523025
theorem B4909355 : Blo 1911435 4909355 := bstep (se 1 (by rfl) ⟨3682016, by rfl⟩ : syracuseStep 4909355 = 7364033) B7364033
theorem B3272903 : Blo 1911435 3272903 := bstep (se 1 (by rfl) ⟨2454677, by rfl⟩ : syracuseStep 3272903 = 4909355) B4909355
theorem B2181935 : Blo 1911435 2181935 := bstep (se 1 (by rfl) ⟨1636451, by rfl⟩ : syracuseStep 2181935 = 3272903) B3272903
theorem B5818493 : Blo 1911435 5818493 := bstep (se 3 (by rfl) ⟨1090967, by rfl⟩ : syracuseStep 5818493 = 2181935) B2181935
theorem B15515981 : Blo 1911435 15515981 := bstep (se 3 (by rfl) ⟨2909246, by rfl⟩ : syracuseStep 15515981 = 5818493) B5818493
theorem B10343987 : Blo 1911435 10343987 := bstep (se 1 (by rfl) ⟨7757990, by rfl⟩ : syracuseStep 10343987 = 15515981) B15515981
theorem B6895991 : Blo 1911435 6895991 := bstep (se 1 (by rfl) ⟨5171993, by rfl⟩ : syracuseStep 6895991 = 10343987) B10343987
theorem B4597327 : Blo 1911435 4597327 := bstep (se 1 (by rfl) ⟨3447995, by rfl⟩ : syracuseStep 4597327 = 6895991) B6895991
theorem B6129769 : Blo 1911435 6129769 := bstep (se 2 (by rfl) ⟨2298663, by rfl⟩ : syracuseStep 6129769 = 4597327) B4597327
theorem B8173025 : Blo 1911435 8173025 := bstep (se 2 (by rfl) ⟨3064884, by rfl⟩ : syracuseStep 8173025 = 6129769) B6129769
theorem B5448683 : Blo 1911435 5448683 := bstep (se 1 (by rfl) ⟨4086512, by rfl⟩ : syracuseStep 5448683 = 8173025) B8173025
theorem B3632455 : Blo 1911435 3632455 := bstep (se 1 (by rfl) ⟨2724341, by rfl⟩ : syracuseStep 3632455 = 5448683) B5448683
theorem B4843273 : Blo 1911435 4843273 := bstep (se 2 (by rfl) ⟨1816227, by rfl⟩ : syracuseStep 4843273 = 3632455) B3632455
theorem B6457697 : Blo 1911435 6457697 := bstep (se 2 (by rfl) ⟨2421636, by rfl⟩ : syracuseStep 6457697 = 4843273) B4843273
theorem B4305131 : Blo 1911435 4305131 := bstep (se 1 (by rfl) ⟨3228848, by rfl⟩ : syracuseStep 4305131 = 6457697) B6457697
theorem B2870087 : Blo 1911435 2870087 := bstep (se 1 (by rfl) ⟨2152565, by rfl⟩ : syracuseStep 2870087 = 4305131) B4305131
theorem B1913391 : Blo 1911435 1913391 := bstep (se 1 (by rfl) ⟨1435043, by rfl⟩ : syracuseStep 1913391 = 2870087) B2870087
theorem B2870093 : Blo 1911435 2870093 := bbase (se 3 (by rfl) ⟨538142, by rfl⟩ : syracuseStep 2870093 = 1076285) (by norm_num)
theorem B1913395 : Blo 1911435 1913395 := bstep (se 1 (by rfl) ⟨1435046, by rfl⟩ : syracuseStep 1913395 = 2870093) B2870093
theorem B4305149 : Blo 1911435 4305149 := bbase (se 3 (by rfl) ⟨807215, by rfl⟩ : syracuseStep 4305149 = 1614431) (by norm_num)
theorem B2870099 : Blo 1911435 2870099 := bstep (se 1 (by rfl) ⟨2152574, by rfl⟩ : syracuseStep 2870099 = 4305149) B4305149
theorem B1913399 : Blo 1911435 1913399 := bstep (se 1 (by rfl) ⟨1435049, by rfl⟩ : syracuseStep 1913399 = 2870099) B2870099
theorem B3228869 : Blo 1911435 3228869 := bbase (se 4 (by rfl) ⟨302706, by rfl⟩ : syracuseStep 3228869 = 605413) (by norm_num)
theorem B2152579 : Blo 1911435 2152579 := bstep (se 1 (by rfl) ⟨1614434, by rfl⟩ : syracuseStep 2152579 = 3228869) B3228869
theorem B2870105 : Blo 1911435 2870105 := bstep (se 2 (by rfl) ⟨1076289, by rfl⟩ : syracuseStep 2870105 = 2152579) B2152579
theorem B1913403 : Blo 1911435 1913403 := bstep (se 1 (by rfl) ⟨1435052, by rfl⟩ : syracuseStep 1913403 = 2870105) B2870105
theorem B14529941 : Blo 1911435 14529941 := bbase (se 6 (by rfl) ⟨340545, by rfl⟩ : syracuseStep 14529941 = 681091) (by norm_num)
theorem B9686627 : Blo 1911435 9686627 := bstep (se 1 (by rfl) ⟨7264970, by rfl⟩ : syracuseStep 9686627 = 14529941) B14529941
theorem B6457751 : Blo 1911435 6457751 := bstep (se 1 (by rfl) ⟨4843313, by rfl⟩ : syracuseStep 6457751 = 9686627) B9686627
theorem B4305167 : Blo 1911435 4305167 := bstep (se 1 (by rfl) ⟨3228875, by rfl⟩ : syracuseStep 4305167 = 6457751) B6457751
theorem B2870111 : Blo 1911435 2870111 := bstep (se 1 (by rfl) ⟨2152583, by rfl⟩ : syracuseStep 2870111 = 4305167) B4305167
theorem B1913407 : Blo 1911435 1913407 := bstep (se 1 (by rfl) ⟨1435055, by rfl⟩ : syracuseStep 1913407 = 2870111) B2870111
theorem B2870117 : Blo 1911435 2870117 := bbase (se 4 (by rfl) ⟨269073, by rfl⟩ : syracuseStep 2870117 = 538147) (by norm_num)
theorem B1913411 : Blo 1911435 1913411 := bstep (se 1 (by rfl) ⟨1435058, by rfl⟩ : syracuseStep 1913411 = 2870117) B2870117
theorem B3632501 : Blo 1911435 3632501 := bbase (se 5 (by rfl) ⟨170273, by rfl⟩ : syracuseStep 3632501 = 340547) (by norm_num)
theorem B2421667 : Blo 1911435 2421667 := bstep (se 1 (by rfl) ⟨1816250, by rfl⟩ : syracuseStep 2421667 = 3632501) B3632501
theorem B3228889 : Blo 1911435 3228889 := bstep (se 2 (by rfl) ⟨1210833, by rfl⟩ : syracuseStep 3228889 = 2421667) B2421667
theorem B4305185 : Blo 1911435 4305185 := bstep (se 2 (by rfl) ⟨1614444, by rfl⟩ : syracuseStep 4305185 = 3228889) B3228889
theorem B2870123 : Blo 1911435 2870123 := bstep (se 1 (by rfl) ⟨2152592, by rfl⟩ : syracuseStep 2870123 = 4305185) B4305185
theorem B1913415 : Blo 1911435 1913415 := bstep (se 1 (by rfl) ⟨1435061, by rfl⟩ : syracuseStep 1913415 = 2870123) B2870123
theorem B2152597 : Blo 1911435 2152597 := bbase (se 6 (by rfl) ⟨50451, by rfl⟩ : syracuseStep 2152597 = 100903) (by norm_num)
theorem B2870129 : Blo 1911435 2870129 := bstep (se 2 (by rfl) ⟨1076298, by rfl⟩ : syracuseStep 2870129 = 2152597) B2152597
theorem B1913419 : Blo 1911435 1913419 := bstep (se 1 (by rfl) ⟨1435064, by rfl⟩ : syracuseStep 1913419 = 2870129) B2870129
theorem B2421677 : Blo 1911435 2421677 := bbase (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) (by norm_num)
theorem B6457805 : Blo 1911435 6457805 := bstep (se 3 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 6457805 = 2421677) B2421677
theorem B4305203 : Blo 1911435 4305203 := bstep (se 1 (by rfl) ⟨3228902, by rfl⟩ : syracuseStep 4305203 = 6457805) B6457805
theorem B2870135 : Blo 1911435 2870135 := bstep (se 1 (by rfl) ⟨2152601, by rfl⟩ : syracuseStep 2870135 = 4305203) B4305203
theorem B1913423 : Blo 1911435 1913423 := bstep (se 1 (by rfl) ⟨1435067, by rfl⟩ : syracuseStep 1913423 = 2870135) B2870135
theorem B2870141 : Blo 1911435 2870141 := bbase (se 3 (by rfl) ⟨538151, by rfl⟩ : syracuseStep 2870141 = 1076303) (by norm_num)
theorem B1913427 : Blo 1911435 1913427 := bstep (se 1 (by rfl) ⟨1435070, by rfl⟩ : syracuseStep 1913427 = 2870141) B2870141
theorem B4305221 : Blo 1911435 4305221 := bbase (se 4 (by rfl) ⟨403614, by rfl⟩ : syracuseStep 4305221 = 807229) (by norm_num)
theorem B2870147 : Blo 1911435 2870147 := bstep (se 1 (by rfl) ⟨2152610, by rfl⟩ : syracuseStep 2870147 = 4305221) B4305221
theorem B1913431 : Blo 1911435 1913431 := bstep (se 1 (by rfl) ⟨1435073, by rfl⟩ : syracuseStep 1913431 = 2870147) B2870147
theorem B3879085 : Blo 1911435 3879085 := bbase (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) (by norm_num)
theorem B5172113 : Blo 1911435 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B13792301 : Blo 1911435 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B9194867 : Blo 1911435 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B6129911 : Blo 1911435 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B4086607 : Blo 1911435 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B5448809 : Blo 1911435 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B3632539 : Blo 1911435 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B4843385 : Blo 1911435 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B3228923 : Blo 1911435 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B2152615 : Blo 1911435 2152615 := bstep (se 1 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 2152615 = 3228923) B3228923
theorem B2870153 : Blo 1911435 2870153 := bstep (se 2 (by rfl) ⟨1076307, by rfl⟩ : syracuseStep 2870153 = 2152615) B2152615
theorem B1913435 : Blo 1911435 1913435 := bstep (se 1 (by rfl) ⟨1435076, by rfl⟩ : syracuseStep 1913435 = 2870153) B2870153
theorem C0 (j : ℕ) (h1 : 477858 ≤ j) (h2 : j ≤ 478358) : Blo 1911435 (4 * j + 3) := by
  interval_cases j
  · exact B1911435
  · exact B1911439
  · exact B1911443
  · exact B1911447
  · exact B1911451
  · exact B1911455
  · exact B1911459
  · exact B1911463
  · exact B1911467
  · exact B1911471
  · exact B1911475
  · exact B1911479
  · exact B1911483
  · exact B1911487
  · exact B1911491
  · exact B1911495
  · exact B1911499
  · exact B1911503
  · exact B1911507
  · exact B1911511
  · exact B1911515
  · exact B1911519
  · exact B1911523
  · exact B1911527
  · exact B1911531
  · exact B1911535
  · exact B1911539
  · exact B1911543
  · exact B1911547
  · exact B1911551
  · exact B1911555
  · exact B1911559
  · exact B1911563
  · exact B1911567
  · exact B1911571
  · exact B1911575
  · exact B1911579
  · exact B1911583
  · exact B1911587
  · exact B1911591
  · exact B1911595
  · exact B1911599
  · exact B1911603
  · exact B1911607
  · exact B1911611
  · exact B1911615
  · exact B1911619
  · exact B1911623
  · exact B1911627
  · exact B1911631
  · exact B1911635
  · exact B1911639
  · exact B1911643
  · exact B1911647
  · exact B1911651
  · exact B1911655
  · exact B1911659
  · exact B1911663
  · exact B1911667
  · exact B1911671
  · exact B1911675
  · exact B1911679
  · exact B1911683
  · exact B1911687
  · exact B1911691
  · exact B1911695
  · exact B1911699
  · exact B1911703
  · exact B1911707
  · exact B1911711
  · exact B1911715
  · exact B1911719
  · exact B1911723
  · exact B1911727
  · exact B1911731
  · exact B1911735
  · exact B1911739
  · exact B1911743
  · exact B1911747
  · exact B1911751
  · exact B1911755
  · exact B1911759
  · exact B1911763
  · exact B1911767
  · exact B1911771
  · exact B1911775
  · exact B1911779
  · exact B1911783
  · exact B1911787
  · exact B1911791
  · exact B1911795
  · exact B1911799
  · exact B1911803
  · exact B1911807
  · exact B1911811
  · exact B1911815
  · exact B1911819
  · exact B1911823
  · exact B1911827
  · exact B1911831
  · exact B1911835
  · exact B1911839
  · exact B1911843
  · exact B1911847
  · exact B1911851
  · exact B1911855
  · exact B1911859
  · exact B1911863
  · exact B1911867
  · exact B1911871
  · exact B1911875
  · exact B1911879
  · exact B1911883
  · exact B1911887
  · exact B1911891
  · exact B1911895
  · exact B1911899
  · exact B1911903
  · exact B1911907
  · exact B1911911
  · exact B1911915
  · exact B1911919
  · exact B1911923
  · exact B1911927
  · exact B1911931
  · exact B1911935
  · exact B1911939
  · exact B1911943
  · exact B1911947
  · exact B1911951
  · exact B1911955
  · exact B1911959
  · exact B1911963
  · exact B1911967
  · exact B1911971
  · exact B1911975
  · exact B1911979
  · exact B1911983
  · exact B1911987
  · exact B1911991
  · exact B1911995
  · exact B1911999
  · exact B1912003
  · exact B1912007
  · exact B1912011
  · exact B1912015
  · exact B1912019
  · exact B1912023
  · exact B1912027
  · exact B1912031
  · exact B1912035
  · exact B1912039
  · exact B1912043
  · exact B1912047
  · exact B1912051
  · exact B1912055
  · exact B1912059
  · exact B1912063
  · exact B1912067
  · exact B1912071
  · exact B1912075
  · exact B1912079
  · exact B1912083
  · exact B1912087
  · exact B1912091
  · exact B1912095
  · exact B1912099
  · exact B1912103
  · exact B1912107
  · exact B1912111
  · exact B1912115
  · exact B1912119
  · exact B1912123
  · exact B1912127
  · exact B1912131
  · exact B1912135
  · exact B1912139
  · exact B1912143
  · exact B1912147
  · exact B1912151
  · exact B1912155
  · exact B1912159
  · exact B1912163
  · exact B1912167
  · exact B1912171
  · exact B1912175
  · exact B1912179
  · exact B1912183
  · exact B1912187
  · exact B1912191
  · exact B1912195
  · exact B1912199
  · exact B1912203
  · exact B1912207
  · exact B1912211
  · exact B1912215
  · exact B1912219
  · exact B1912223
  · exact B1912227
  · exact B1912231
  · exact B1912235
  · exact B1912239
  · exact B1912243
  · exact B1912247
  · exact B1912251
  · exact B1912255
  · exact B1912259
  · exact B1912263
  · exact B1912267
  · exact B1912271
  · exact B1912275
  · exact B1912279
  · exact B1912283
  · exact B1912287
  · exact B1912291
  · exact B1912295
  · exact B1912299
  · exact B1912303
  · exact B1912307
  · exact B1912311
  · exact B1912315
  · exact B1912319
  · exact B1912323
  · exact B1912327
  · exact B1912331
  · exact B1912335
  · exact B1912339
  · exact B1912343
  · exact B1912347
  · exact B1912351
  · exact B1912355
  · exact B1912359
  · exact B1912363
  · exact B1912367
  · exact B1912371
  · exact B1912375
  · exact B1912379
  · exact B1912383
  · exact B1912387
  · exact B1912391
  · exact B1912395
  · exact B1912399
  · exact B1912403
  · exact B1912407
  · exact B1912411
  · exact B1912415
  · exact B1912419
  · exact B1912423
  · exact B1912427
  · exact B1912431
  · exact B1912435
  · exact B1912439
  · exact B1912443
  · exact B1912447
  · exact B1912451
  · exact B1912455
  · exact B1912459
  · exact B1912463
  · exact B1912467
  · exact B1912471
  · exact B1912475
  · exact B1912479
  · exact B1912483
  · exact B1912487
  · exact B1912491
  · exact B1912495
  · exact B1912499
  · exact B1912503
  · exact B1912507
  · exact B1912511
  · exact B1912515
  · exact B1912519
  · exact B1912523
  · exact B1912527
  · exact B1912531
  · exact B1912535
  · exact B1912539
  · exact B1912543
  · exact B1912547
  · exact B1912551
  · exact B1912555
  · exact B1912559
  · exact B1912563
  · exact B1912567
  · exact B1912571
  · exact B1912575
  · exact B1912579
  · exact B1912583
  · exact B1912587
  · exact B1912591
  · exact B1912595
  · exact B1912599
  · exact B1912603
  · exact B1912607
  · exact B1912611
  · exact B1912615
  · exact B1912619
  · exact B1912623
  · exact B1912627
  · exact B1912631
  · exact B1912635
  · exact B1912639
  · exact B1912643
  · exact B1912647
  · exact B1912651
  · exact B1912655
  · exact B1912659
  · exact B1912663
  · exact B1912667
  · exact B1912671
  · exact B1912675
  · exact B1912679
  · exact B1912683
  · exact B1912687
  · exact B1912691
  · exact B1912695
  · exact B1912699
  · exact B1912703
  · exact B1912707
  · exact B1912711
  · exact B1912715
  · exact B1912719
  · exact B1912723
  · exact B1912727
  · exact B1912731
  · exact B1912735
  · exact B1912739
  · exact B1912743
  · exact B1912747
  · exact B1912751
  · exact B1912755
  · exact B1912759
  · exact B1912763
  · exact B1912767
  · exact B1912771
  · exact B1912775
  · exact B1912779
  · exact B1912783
  · exact B1912787
  · exact B1912791
  · exact B1912795
  · exact B1912799
  · exact B1912803
  · exact B1912807
  · exact B1912811
  · exact B1912815
  · exact B1912819
  · exact B1912823
  · exact B1912827
  · exact B1912831
  · exact B1912835
  · exact B1912839
  · exact B1912843
  · exact B1912847
  · exact B1912851
  · exact B1912855
  · exact B1912859
  · exact B1912863
  · exact B1912867
  · exact B1912871
  · exact B1912875
  · exact B1912879
  · exact B1912883
  · exact B1912887
  · exact B1912891
  · exact B1912895
  · exact B1912899
  · exact B1912903
  · exact B1912907
  · exact B1912911
  · exact B1912915
  · exact B1912919
  · exact B1912923
  · exact B1912927
  · exact B1912931
  · exact B1912935
  · exact B1912939
  · exact B1912943
  · exact B1912947
  · exact B1912951
  · exact B1912955
  · exact B1912959
  · exact B1912963
  · exact B1912967
  · exact B1912971
  · exact B1912975
  · exact B1912979
  · exact B1912983
  · exact B1912987
  · exact B1912991
  · exact B1912995
  · exact B1912999
  · exact B1913003
  · exact B1913007
  · exact B1913011
  · exact B1913015
  · exact B1913019
  · exact B1913023
  · exact B1913027
  · exact B1913031
  · exact B1913035
  · exact B1913039
  · exact B1913043
  · exact B1913047
  · exact B1913051
  · exact B1913055
  · exact B1913059
  · exact B1913063
  · exact B1913067
  · exact B1913071
  · exact B1913075
  · exact B1913079
  · exact B1913083
  · exact B1913087
  · exact B1913091
  · exact B1913095
  · exact B1913099
  · exact B1913103
  · exact B1913107
  · exact B1913111
  · exact B1913115
  · exact B1913119
  · exact B1913123
  · exact B1913127
  · exact B1913131
  · exact B1913135
  · exact B1913139
  · exact B1913143
  · exact B1913147
  · exact B1913151
  · exact B1913155
  · exact B1913159
  · exact B1913163
  · exact B1913167
  · exact B1913171
  · exact B1913175
  · exact B1913179
  · exact B1913183
  · exact B1913187
  · exact B1913191
  · exact B1913195
  · exact B1913199
  · exact B1913203
  · exact B1913207
  · exact B1913211
  · exact B1913215
  · exact B1913219
  · exact B1913223
  · exact B1913227
  · exact B1913231
  · exact B1913235
  · exact B1913239
  · exact B1913243
  · exact B1913247
  · exact B1913251
  · exact B1913255
  · exact B1913259
  · exact B1913263
  · exact B1913267
  · exact B1913271
  · exact B1913275
  · exact B1913279
  · exact B1913283
  · exact B1913287
  · exact B1913291
  · exact B1913295
  · exact B1913299
  · exact B1913303
  · exact B1913307
  · exact B1913311
  · exact B1913315
  · exact B1913319
  · exact B1913323
  · exact B1913327
  · exact B1913331
  · exact B1913335
  · exact B1913339
  · exact B1913343
  · exact B1913347
  · exact B1913351
  · exact B1913355
  · exact B1913359
  · exact B1913363
  · exact B1913367
  · exact B1913371
  · exact B1913375
  · exact B1913379
  · exact B1913383
  · exact B1913387
  · exact B1913391
  · exact B1913395
  · exact B1913399
  · exact B1913403
  · exact B1913407
  · exact B1913411
  · exact B1913415
  · exact B1913419
  · exact B1913423
  · exact B1913427
  · exact B1913431
  · exact B1913435
theorem solution (m : ℕ) (hlo : 1911435 ≤ m) (hhi : m ≤ 1913435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 477858 ≤ j := by omega
    have hj2 : j ≤ 478358 := by omega
    have hb : Blo 1911435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
