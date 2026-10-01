-- Prove2me | solution 1 for syracuse_descends_range_2007435_2009435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:39.462295+00:00
-- url     : https://prove2.me/submissions/a47d58b7-20f8-4d42-804e-72c6c525a7dd

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

theorem B2258365 : Blo 2007435 2258365 := bbase (se 3 (by rfl) ⟨423443, by rfl⟩ : syracuseStep 2258365 = 846887) (by norm_num)
theorem B3011153 : Blo 2007435 3011153 := bstep (se 2 (by rfl) ⟨1129182, by rfl⟩ : syracuseStep 3011153 = 2258365) B2258365
theorem B2007435 : Blo 2007435 2007435 := bstep (se 1 (by rfl) ⟨1505576, by rfl⟩ : syracuseStep 2007435 = 3011153) B3011153
theorem B6775109 : Blo 2007435 6775109 := bbase (se 4 (by rfl) ⟨635166, by rfl⟩ : syracuseStep 6775109 = 1270333) (by norm_num)
theorem B4516739 : Blo 2007435 4516739 := bstep (se 1 (by rfl) ⟨3387554, by rfl⟩ : syracuseStep 4516739 = 6775109) B6775109
theorem B3011159 : Blo 2007435 3011159 := bstep (se 1 (by rfl) ⟨2258369, by rfl⟩ : syracuseStep 3011159 = 4516739) B4516739
theorem B2007439 : Blo 2007435 2007439 := bstep (se 1 (by rfl) ⟨1505579, by rfl⟩ : syracuseStep 2007439 = 3011159) B3011159
theorem B3011165 : Blo 2007435 3011165 := bbase (se 3 (by rfl) ⟨564593, by rfl⟩ : syracuseStep 3011165 = 1129187) (by norm_num)
theorem B2007443 : Blo 2007435 2007443 := bstep (se 1 (by rfl) ⟨1505582, by rfl⟩ : syracuseStep 2007443 = 3011165) B3011165
theorem B4516757 : Blo 2007435 4516757 := bbase (se 6 (by rfl) ⟨105861, by rfl⟩ : syracuseStep 4516757 = 211723) (by norm_num)
theorem B3011171 : Blo 2007435 3011171 := bstep (se 1 (by rfl) ⟨2258378, by rfl⟩ : syracuseStep 3011171 = 4516757) B4516757
theorem B2007447 : Blo 2007435 2007447 := bstep (se 1 (by rfl) ⟨1505585, by rfl⟩ : syracuseStep 2007447 = 3011171) B3011171
theorem B5150693 : Blo 2007435 5150693 := bbase (se 4 (by rfl) ⟨482877, by rfl⟩ : syracuseStep 5150693 = 965755) (by norm_num)
theorem B3433795 : Blo 2007435 3433795 := bstep (se 1 (by rfl) ⟨2575346, by rfl⟩ : syracuseStep 3433795 = 5150693) B5150693
theorem B18313573 : Blo 2007435 18313573 := bstep (se 4 (by rfl) ⟨1716897, by rfl⟩ : syracuseStep 18313573 = 3433795) B3433795
theorem B24418097 : Blo 2007435 24418097 := bstep (se 2 (by rfl) ⟨9156786, by rfl⟩ : syracuseStep 24418097 = 18313573) B18313573
theorem B16278731 : Blo 2007435 16278731 := bstep (se 1 (by rfl) ⟨12209048, by rfl⟩ : syracuseStep 16278731 = 24418097) B24418097
theorem B10852487 : Blo 2007435 10852487 := bstep (se 1 (by rfl) ⟨8139365, by rfl⟩ : syracuseStep 10852487 = 16278731) B16278731
theorem B7234991 : Blo 2007435 7234991 := bstep (se 1 (by rfl) ⟨5426243, by rfl⟩ : syracuseStep 7234991 = 10852487) B10852487
theorem B4823327 : Blo 2007435 4823327 := bstep (se 1 (by rfl) ⟨3617495, by rfl⟩ : syracuseStep 4823327 = 7234991) B7234991
theorem B3215551 : Blo 2007435 3215551 := bstep (se 1 (by rfl) ⟨2411663, by rfl⟩ : syracuseStep 3215551 = 4823327) B4823327
theorem B4287401 : Blo 2007435 4287401 := bstep (se 2 (by rfl) ⟨1607775, by rfl⟩ : syracuseStep 4287401 = 3215551) B3215551
theorem B2858267 : Blo 2007435 2858267 := bstep (se 1 (by rfl) ⟨2143700, by rfl⟩ : syracuseStep 2858267 = 4287401) B4287401
theorem B7622045 : Blo 2007435 7622045 := bstep (se 3 (by rfl) ⟨1429133, by rfl⟩ : syracuseStep 7622045 = 2858267) B2858267
theorem B5081363 : Blo 2007435 5081363 := bstep (se 1 (by rfl) ⟨3811022, by rfl⟩ : syracuseStep 5081363 = 7622045) B7622045
theorem B3387575 : Blo 2007435 3387575 := bstep (se 1 (by rfl) ⟨2540681, by rfl⟩ : syracuseStep 3387575 = 5081363) B5081363
theorem B2258383 : Blo 2007435 2258383 := bstep (se 1 (by rfl) ⟨1693787, by rfl⟩ : syracuseStep 2258383 = 3387575) B3387575
theorem B3011177 : Blo 2007435 3011177 := bstep (se 2 (by rfl) ⟨1129191, by rfl⟩ : syracuseStep 3011177 = 2258383) B2258383
theorem B2007451 : Blo 2007435 2007451 := bstep (se 1 (by rfl) ⟨1505588, by rfl⟩ : syracuseStep 2007451 = 3011177) B3011177
theorem B2172953 : Blo 2007435 2172953 := bbase (se 2 (by rfl) ⟨814857, by rfl⟩ : syracuseStep 2172953 = 1629715) (by norm_num)
theorem B5794541 : Blo 2007435 5794541 := bstep (se 3 (by rfl) ⟨1086476, by rfl⟩ : syracuseStep 5794541 = 2172953) B2172953
theorem B3863027 : Blo 2007435 3863027 := bstep (se 1 (by rfl) ⟨2897270, by rfl⟩ : syracuseStep 3863027 = 5794541) B5794541
theorem B2575351 : Blo 2007435 2575351 := bstep (se 1 (by rfl) ⟨1931513, by rfl⟩ : syracuseStep 2575351 = 3863027) B3863027
theorem B3433801 : Blo 2007435 3433801 := bstep (se 2 (by rfl) ⟨1287675, by rfl⟩ : syracuseStep 3433801 = 2575351) B2575351
theorem B4578401 : Blo 2007435 4578401 := bstep (se 2 (by rfl) ⟨1716900, by rfl⟩ : syracuseStep 4578401 = 3433801) B3433801
theorem B12209069 : Blo 2007435 12209069 := bstep (se 3 (by rfl) ⟨2289200, by rfl⟩ : syracuseStep 12209069 = 4578401) B4578401
theorem B8139379 : Blo 2007435 8139379 := bstep (se 1 (by rfl) ⟨6104534, by rfl⟩ : syracuseStep 8139379 = 12209069) B12209069
theorem B10852505 : Blo 2007435 10852505 := bstep (se 2 (by rfl) ⟨4069689, by rfl⟩ : syracuseStep 10852505 = 8139379) B8139379
theorem B7235003 : Blo 2007435 7235003 := bstep (se 1 (by rfl) ⟨5426252, by rfl⟩ : syracuseStep 7235003 = 10852505) B10852505
theorem B4823335 : Blo 2007435 4823335 := bstep (se 1 (by rfl) ⟨3617501, by rfl⟩ : syracuseStep 4823335 = 7235003) B7235003
theorem B6431113 : Blo 2007435 6431113 := bstep (se 2 (by rfl) ⟨2411667, by rfl⟩ : syracuseStep 6431113 = 4823335) B4823335
theorem B8574817 : Blo 2007435 8574817 := bstep (se 2 (by rfl) ⟨3215556, by rfl⟩ : syracuseStep 8574817 = 6431113) B6431113
theorem B11433089 : Blo 2007435 11433089 := bstep (se 2 (by rfl) ⟨4287408, by rfl⟩ : syracuseStep 11433089 = 8574817) B8574817
theorem B7622059 : Blo 2007435 7622059 := bstep (se 1 (by rfl) ⟨5716544, by rfl⟩ : syracuseStep 7622059 = 11433089) B11433089
theorem B10162745 : Blo 2007435 10162745 := bstep (se 2 (by rfl) ⟨3811029, by rfl⟩ : syracuseStep 10162745 = 7622059) B7622059
theorem B6775163 : Blo 2007435 6775163 := bstep (se 1 (by rfl) ⟨5081372, by rfl⟩ : syracuseStep 6775163 = 10162745) B10162745
theorem B4516775 : Blo 2007435 4516775 := bstep (se 1 (by rfl) ⟨3387581, by rfl⟩ : syracuseStep 4516775 = 6775163) B6775163
theorem B3011183 : Blo 2007435 3011183 := bstep (se 1 (by rfl) ⟨2258387, by rfl⟩ : syracuseStep 3011183 = 4516775) B4516775
theorem B2007455 : Blo 2007435 2007455 := bstep (se 1 (by rfl) ⟨1505591, by rfl⟩ : syracuseStep 2007455 = 3011183) B3011183
theorem B3011189 : Blo 2007435 3011189 := bbase (se 5 (by rfl) ⟨141149, by rfl⟩ : syracuseStep 3011189 = 282299) (by norm_num)
theorem B2007459 : Blo 2007435 2007459 := bstep (se 1 (by rfl) ⟨1505594, by rfl⟩ : syracuseStep 2007459 = 3011189) B3011189
theorem B3811045 : Blo 2007435 3811045 := bbase (se 4 (by rfl) ⟨357285, by rfl⟩ : syracuseStep 3811045 = 714571) (by norm_num)
theorem B5081393 : Blo 2007435 5081393 := bstep (se 2 (by rfl) ⟨1905522, by rfl⟩ : syracuseStep 5081393 = 3811045) B3811045
theorem B3387595 : Blo 2007435 3387595 := bstep (se 1 (by rfl) ⟨2540696, by rfl⟩ : syracuseStep 3387595 = 5081393) B5081393
theorem B4516793 : Blo 2007435 4516793 := bstep (se 2 (by rfl) ⟨1693797, by rfl⟩ : syracuseStep 4516793 = 3387595) B3387595
theorem B3011195 : Blo 2007435 3011195 := bstep (se 1 (by rfl) ⟨2258396, by rfl⟩ : syracuseStep 3011195 = 4516793) B4516793
theorem B2007463 : Blo 2007435 2007463 := bstep (se 1 (by rfl) ⟨1505597, by rfl⟩ : syracuseStep 2007463 = 3011195) B3011195
theorem B2258401 : Blo 2007435 2258401 := bbase (se 2 (by rfl) ⟨846900, by rfl⟩ : syracuseStep 2258401 = 1693801) (by norm_num)
theorem B3011201 : Blo 2007435 3011201 := bstep (se 2 (by rfl) ⟨1129200, by rfl⟩ : syracuseStep 3011201 = 2258401) B2258401
theorem B2007467 : Blo 2007435 2007467 := bstep (se 1 (by rfl) ⟨1505600, by rfl⟩ : syracuseStep 2007467 = 3011201) B3011201
theorem B5081413 : Blo 2007435 5081413 := bbase (se 4 (by rfl) ⟨476382, by rfl⟩ : syracuseStep 5081413 = 952765) (by norm_num)
theorem B6775217 : Blo 2007435 6775217 := bstep (se 2 (by rfl) ⟨2540706, by rfl⟩ : syracuseStep 6775217 = 5081413) B5081413
theorem B4516811 : Blo 2007435 4516811 := bstep (se 1 (by rfl) ⟨3387608, by rfl⟩ : syracuseStep 4516811 = 6775217) B6775217
theorem B3011207 : Blo 2007435 3011207 := bstep (se 1 (by rfl) ⟨2258405, by rfl⟩ : syracuseStep 3011207 = 4516811) B4516811
theorem B2007471 : Blo 2007435 2007471 := bstep (se 1 (by rfl) ⟨1505603, by rfl⟩ : syracuseStep 2007471 = 3011207) B3011207
theorem B3011213 : Blo 2007435 3011213 := bbase (se 3 (by rfl) ⟨564602, by rfl⟩ : syracuseStep 3011213 = 1129205) (by norm_num)
theorem B2007475 : Blo 2007435 2007475 := bstep (se 1 (by rfl) ⟨1505606, by rfl⟩ : syracuseStep 2007475 = 3011213) B3011213
theorem B4516829 : Blo 2007435 4516829 := bbase (se 3 (by rfl) ⟨846905, by rfl⟩ : syracuseStep 4516829 = 1693811) (by norm_num)
theorem B3011219 : Blo 2007435 3011219 := bstep (se 1 (by rfl) ⟨2258414, by rfl⟩ : syracuseStep 3011219 = 4516829) B4516829
theorem B2007479 : Blo 2007435 2007479 := bstep (se 1 (by rfl) ⟨1505609, by rfl⟩ : syracuseStep 2007479 = 3011219) B3011219
theorem B3387629 : Blo 2007435 3387629 := bbase (se 3 (by rfl) ⟨635180, by rfl⟩ : syracuseStep 3387629 = 1270361) (by norm_num)
theorem B2258419 : Blo 2007435 2258419 := bstep (se 1 (by rfl) ⟨1693814, by rfl⟩ : syracuseStep 2258419 = 3387629) B3387629
theorem B3011225 : Blo 2007435 3011225 := bstep (se 2 (by rfl) ⟨1129209, by rfl⟩ : syracuseStep 3011225 = 2258419) B2258419
theorem B2007483 : Blo 2007435 2007483 := bstep (se 1 (by rfl) ⟨1505612, by rfl⟩ : syracuseStep 2007483 = 3011225) B3011225
theorem B2936845 : Blo 2007435 2936845 := bbase (se 3 (by rfl) ⟨550658, by rfl⟩ : syracuseStep 2936845 = 1101317) (by norm_num)
theorem B3915793 : Blo 2007435 3915793 := bstep (se 2 (by rfl) ⟨1468422, by rfl⟩ : syracuseStep 3915793 = 2936845) B2936845
theorem B20884229 : Blo 2007435 20884229 := bstep (se 4 (by rfl) ⟨1957896, by rfl⟩ : syracuseStep 20884229 = 3915793) B3915793
theorem B13922819 : Blo 2007435 13922819 := bstep (se 1 (by rfl) ⟨10442114, by rfl⟩ : syracuseStep 13922819 = 20884229) B20884229
theorem B9281879 : Blo 2007435 9281879 := bstep (se 1 (by rfl) ⟨6961409, by rfl⟩ : syracuseStep 9281879 = 13922819) B13922819
theorem B6187919 : Blo 2007435 6187919 := bstep (se 1 (by rfl) ⟨4640939, by rfl⟩ : syracuseStep 6187919 = 9281879) B9281879
theorem B16501117 : Blo 2007435 16501117 := bstep (se 3 (by rfl) ⟨3093959, by rfl⟩ : syracuseStep 16501117 = 6187919) B6187919
theorem B22001489 : Blo 2007435 22001489 := bstep (se 2 (by rfl) ⟨8250558, by rfl⟩ : syracuseStep 22001489 = 16501117) B16501117
theorem B14667659 : Blo 2007435 14667659 := bstep (se 1 (by rfl) ⟨11000744, by rfl⟩ : syracuseStep 14667659 = 22001489) B22001489
theorem B9778439 : Blo 2007435 9778439 := bstep (se 1 (by rfl) ⟨7333829, by rfl⟩ : syracuseStep 9778439 = 14667659) B14667659
theorem B26075837 : Blo 2007435 26075837 := bstep (se 3 (by rfl) ⟨4889219, by rfl⟩ : syracuseStep 26075837 = 9778439) B9778439
theorem B17383891 : Blo 2007435 17383891 := bstep (se 1 (by rfl) ⟨13037918, by rfl⟩ : syracuseStep 17383891 = 26075837) B26075837
theorem B23178521 : Blo 2007435 23178521 := bstep (se 2 (by rfl) ⟨8691945, by rfl⟩ : syracuseStep 23178521 = 17383891) B17383891
theorem B61809389 : Blo 2007435 61809389 := bstep (se 3 (by rfl) ⟨11589260, by rfl⟩ : syracuseStep 61809389 = 23178521) B23178521
theorem B41206259 : Blo 2007435 41206259 := bstep (se 1 (by rfl) ⟨30904694, by rfl⟩ : syracuseStep 41206259 = 61809389) B61809389
theorem B27470839 : Blo 2007435 27470839 := bstep (se 1 (by rfl) ⟨20603129, by rfl⟩ : syracuseStep 27470839 = 41206259) B41206259
theorem B36627785 : Blo 2007435 36627785 := bstep (se 2 (by rfl) ⟨13735419, by rfl⟩ : syracuseStep 36627785 = 27470839) B27470839
theorem B24418523 : Blo 2007435 24418523 := bstep (se 1 (by rfl) ⟨18313892, by rfl⟩ : syracuseStep 24418523 = 36627785) B36627785
theorem B16279015 : Blo 2007435 16279015 := bstep (se 1 (by rfl) ⟨12209261, by rfl⟩ : syracuseStep 16279015 = 24418523) B24418523
theorem B21705353 : Blo 2007435 21705353 := bstep (se 2 (by rfl) ⟨8139507, by rfl⟩ : syracuseStep 21705353 = 16279015) B16279015
theorem B14470235 : Blo 2007435 14470235 := bstep (se 1 (by rfl) ⟨10852676, by rfl⟩ : syracuseStep 14470235 = 21705353) B21705353
theorem B9646823 : Blo 2007435 9646823 := bstep (se 1 (by rfl) ⟨7235117, by rfl⟩ : syracuseStep 9646823 = 14470235) B14470235
theorem B25724861 : Blo 2007435 25724861 := bstep (se 3 (by rfl) ⟨4823411, by rfl⟩ : syracuseStep 25724861 = 9646823) B9646823
theorem B17149907 : Blo 2007435 17149907 := bstep (se 1 (by rfl) ⟨12862430, by rfl⟩ : syracuseStep 17149907 = 25724861) B25724861
theorem B11433271 : Blo 2007435 11433271 := bstep (se 1 (by rfl) ⟨8574953, by rfl⟩ : syracuseStep 11433271 = 17149907) B17149907
theorem B15244361 : Blo 2007435 15244361 := bstep (se 2 (by rfl) ⟨5716635, by rfl⟩ : syracuseStep 15244361 = 11433271) B11433271
theorem B10162907 : Blo 2007435 10162907 := bstep (se 1 (by rfl) ⟨7622180, by rfl⟩ : syracuseStep 10162907 = 15244361) B15244361
theorem B6775271 : Blo 2007435 6775271 := bstep (se 1 (by rfl) ⟨5081453, by rfl⟩ : syracuseStep 6775271 = 10162907) B10162907
theorem B4516847 : Blo 2007435 4516847 := bstep (se 1 (by rfl) ⟨3387635, by rfl⟩ : syracuseStep 4516847 = 6775271) B6775271
theorem B3011231 : Blo 2007435 3011231 := bstep (se 1 (by rfl) ⟨2258423, by rfl⟩ : syracuseStep 3011231 = 4516847) B4516847
theorem B2007487 : Blo 2007435 2007487 := bstep (se 1 (by rfl) ⟨1505615, by rfl⟩ : syracuseStep 2007487 = 3011231) B3011231
theorem B3011237 : Blo 2007435 3011237 := bbase (se 4 (by rfl) ⟨282303, by rfl⟩ : syracuseStep 3011237 = 564607) (by norm_num)
theorem B2007491 : Blo 2007435 2007491 := bstep (se 1 (by rfl) ⟨1505618, by rfl⟩ : syracuseStep 2007491 = 3011237) B3011237
theorem B2540737 : Blo 2007435 2540737 := bbase (se 2 (by rfl) ⟨952776, by rfl⟩ : syracuseStep 2540737 = 1905553) (by norm_num)
theorem B3387649 : Blo 2007435 3387649 := bstep (se 2 (by rfl) ⟨1270368, by rfl⟩ : syracuseStep 3387649 = 2540737) B2540737
theorem B4516865 : Blo 2007435 4516865 := bstep (se 2 (by rfl) ⟨1693824, by rfl⟩ : syracuseStep 4516865 = 3387649) B3387649
theorem B3011243 : Blo 2007435 3011243 := bstep (se 1 (by rfl) ⟨2258432, by rfl⟩ : syracuseStep 3011243 = 4516865) B4516865
theorem B2007495 : Blo 2007435 2007495 := bstep (se 1 (by rfl) ⟨1505621, by rfl⟩ : syracuseStep 2007495 = 3011243) B3011243
theorem B2258437 : Blo 2007435 2258437 := bbase (se 4 (by rfl) ⟨211728, by rfl⟩ : syracuseStep 2258437 = 423457) (by norm_num)
theorem B3011249 : Blo 2007435 3011249 := bstep (se 2 (by rfl) ⟨1129218, by rfl⟩ : syracuseStep 3011249 = 2258437) B2258437
theorem B2007499 : Blo 2007435 2007499 := bstep (se 1 (by rfl) ⟨1505624, by rfl⟩ : syracuseStep 2007499 = 3011249) B3011249
theorem B2858341 : Blo 2007435 2858341 := bbase (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) (by norm_num)
theorem B3811121 : Blo 2007435 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B2540747 : Blo 2007435 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B6775325 : Blo 2007435 6775325 := bstep (se 3 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 6775325 = 2540747) B2540747
theorem B4516883 : Blo 2007435 4516883 := bstep (se 1 (by rfl) ⟨3387662, by rfl⟩ : syracuseStep 4516883 = 6775325) B6775325
theorem B3011255 : Blo 2007435 3011255 := bstep (se 1 (by rfl) ⟨2258441, by rfl⟩ : syracuseStep 3011255 = 4516883) B4516883
theorem B2007503 : Blo 2007435 2007503 := bstep (se 1 (by rfl) ⟨1505627, by rfl⟩ : syracuseStep 2007503 = 3011255) B3011255
theorem B3011261 : Blo 2007435 3011261 := bbase (se 3 (by rfl) ⟨564611, by rfl⟩ : syracuseStep 3011261 = 1129223) (by norm_num)
theorem B2007507 : Blo 2007435 2007507 := bstep (se 1 (by rfl) ⟨1505630, by rfl⟩ : syracuseStep 2007507 = 3011261) B3011261
theorem B4516901 : Blo 2007435 4516901 := bbase (se 4 (by rfl) ⟨423459, by rfl⟩ : syracuseStep 4516901 = 846919) (by norm_num)
theorem B3011267 : Blo 2007435 3011267 := bstep (se 1 (by rfl) ⟨2258450, by rfl⟩ : syracuseStep 3011267 = 4516901) B4516901
theorem B2007511 : Blo 2007435 2007511 := bstep (se 1 (by rfl) ⟨1505633, by rfl⟩ : syracuseStep 2007511 = 3011267) B3011267
theorem B5081525 : Blo 2007435 5081525 := bbase (se 5 (by rfl) ⟨238196, by rfl⟩ : syracuseStep 5081525 = 476393) (by norm_num)
theorem B3387683 : Blo 2007435 3387683 := bstep (se 1 (by rfl) ⟨2540762, by rfl⟩ : syracuseStep 3387683 = 5081525) B5081525
theorem B2258455 : Blo 2007435 2258455 := bstep (se 1 (by rfl) ⟨1693841, by rfl⟩ : syracuseStep 2258455 = 3387683) B3387683
theorem B3011273 : Blo 2007435 3011273 := bstep (se 2 (by rfl) ⟨1129227, by rfl⟩ : syracuseStep 3011273 = 2258455) B2258455
theorem B2007515 : Blo 2007435 2007515 := bstep (se 1 (by rfl) ⟨1505636, by rfl⟩ : syracuseStep 2007515 = 3011273) B3011273
theorem B2713213 : Blo 2007435 2713213 := bbase (se 3 (by rfl) ⟨508727, by rfl⟩ : syracuseStep 2713213 = 1017455) (by norm_num)
theorem B3617617 : Blo 2007435 3617617 := bstep (se 2 (by rfl) ⟨1356606, by rfl⟩ : syracuseStep 3617617 = 2713213) B2713213
theorem B4823489 : Blo 2007435 4823489 := bstep (se 2 (by rfl) ⟨1808808, by rfl⟩ : syracuseStep 4823489 = 3617617) B3617617
theorem B12862637 : Blo 2007435 12862637 := bstep (se 3 (by rfl) ⟨2411744, by rfl⟩ : syracuseStep 12862637 = 4823489) B4823489
theorem B8575091 : Blo 2007435 8575091 := bstep (se 1 (by rfl) ⟨6431318, by rfl⟩ : syracuseStep 8575091 = 12862637) B12862637
theorem B5716727 : Blo 2007435 5716727 := bstep (se 1 (by rfl) ⟨4287545, by rfl⟩ : syracuseStep 5716727 = 8575091) B8575091
theorem B3811151 : Blo 2007435 3811151 := bstep (se 1 (by rfl) ⟨2858363, by rfl⟩ : syracuseStep 3811151 = 5716727) B5716727
theorem B10163069 : Blo 2007435 10163069 := bstep (se 3 (by rfl) ⟨1905575, by rfl⟩ : syracuseStep 10163069 = 3811151) B3811151
theorem B6775379 : Blo 2007435 6775379 := bstep (se 1 (by rfl) ⟨5081534, by rfl⟩ : syracuseStep 6775379 = 10163069) B10163069
theorem B4516919 : Blo 2007435 4516919 := bstep (se 1 (by rfl) ⟨3387689, by rfl⟩ : syracuseStep 4516919 = 6775379) B6775379
theorem B3011279 : Blo 2007435 3011279 := bstep (se 1 (by rfl) ⟨2258459, by rfl⟩ : syracuseStep 3011279 = 4516919) B4516919
theorem B2007519 : Blo 2007435 2007519 := bstep (se 1 (by rfl) ⟨1505639, by rfl⟩ : syracuseStep 2007519 = 3011279) B3011279
theorem B3011285 : Blo 2007435 3011285 := bbase (se 7 (by rfl) ⟨35288, by rfl⟩ : syracuseStep 3011285 = 70577) (by norm_num)
theorem B2007523 : Blo 2007435 2007523 := bstep (se 1 (by rfl) ⟨1505642, by rfl⟩ : syracuseStep 2007523 = 3011285) B3011285
theorem B4823509 : Blo 2007435 4823509 := bbase (se 7 (by rfl) ⟨56525, by rfl⟩ : syracuseStep 4823509 = 113051) (by norm_num)
theorem B6431345 : Blo 2007435 6431345 := bstep (se 2 (by rfl) ⟨2411754, by rfl⟩ : syracuseStep 6431345 = 4823509) B4823509
theorem B4287563 : Blo 2007435 4287563 := bstep (se 1 (by rfl) ⟨3215672, by rfl⟩ : syracuseStep 4287563 = 6431345) B6431345
theorem B2858375 : Blo 2007435 2858375 := bstep (se 1 (by rfl) ⟨2143781, by rfl⟩ : syracuseStep 2858375 = 4287563) B4287563
theorem B7622333 : Blo 2007435 7622333 := bstep (se 3 (by rfl) ⟨1429187, by rfl⟩ : syracuseStep 7622333 = 2858375) B2858375
theorem B5081555 : Blo 2007435 5081555 := bstep (se 1 (by rfl) ⟨3811166, by rfl⟩ : syracuseStep 5081555 = 7622333) B7622333
theorem B3387703 : Blo 2007435 3387703 := bstep (se 1 (by rfl) ⟨2540777, by rfl⟩ : syracuseStep 3387703 = 5081555) B5081555
theorem B4516937 : Blo 2007435 4516937 := bstep (se 2 (by rfl) ⟨1693851, by rfl⟩ : syracuseStep 4516937 = 3387703) B3387703
theorem B3011291 : Blo 2007435 3011291 := bstep (se 1 (by rfl) ⟨2258468, by rfl⟩ : syracuseStep 3011291 = 4516937) B4516937
theorem B2007527 : Blo 2007435 2007527 := bstep (se 1 (by rfl) ⟨1505645, by rfl⟩ : syracuseStep 2007527 = 3011291) B3011291
theorem B2258473 : Blo 2007435 2258473 := bbase (se 2 (by rfl) ⟨846927, by rfl⟩ : syracuseStep 2258473 = 1693855) (by norm_num)
theorem B3011297 : Blo 2007435 3011297 := bstep (se 2 (by rfl) ⟨1129236, by rfl⟩ : syracuseStep 3011297 = 2258473) B2258473
theorem B2007531 : Blo 2007435 2007531 := bstep (se 1 (by rfl) ⟨1505648, by rfl⟩ : syracuseStep 2007531 = 3011297) B3011297
theorem B10301813 : Blo 2007435 10301813 := bbase (se 5 (by rfl) ⟨482897, by rfl⟩ : syracuseStep 10301813 = 965795) (by norm_num)
theorem B6867875 : Blo 2007435 6867875 := bstep (se 1 (by rfl) ⟨5150906, by rfl⟩ : syracuseStep 6867875 = 10301813) B10301813
theorem B18314333 : Blo 2007435 18314333 := bstep (se 3 (by rfl) ⟨3433937, by rfl⟩ : syracuseStep 18314333 = 6867875) B6867875
theorem B12209555 : Blo 2007435 12209555 := bstep (se 1 (by rfl) ⟨9157166, by rfl⟩ : syracuseStep 12209555 = 18314333) B18314333
theorem B8139703 : Blo 2007435 8139703 := bstep (se 1 (by rfl) ⟨6104777, by rfl⟩ : syracuseStep 8139703 = 12209555) B12209555
theorem B10852937 : Blo 2007435 10852937 := bstep (se 2 (by rfl) ⟨4069851, by rfl⟩ : syracuseStep 10852937 = 8139703) B8139703
theorem B7235291 : Blo 2007435 7235291 := bstep (se 1 (by rfl) ⟨5426468, by rfl⟩ : syracuseStep 7235291 = 10852937) B10852937
theorem B19294109 : Blo 2007435 19294109 := bstep (se 3 (by rfl) ⟨3617645, by rfl⟩ : syracuseStep 19294109 = 7235291) B7235291
theorem B12862739 : Blo 2007435 12862739 := bstep (se 1 (by rfl) ⟨9647054, by rfl⟩ : syracuseStep 12862739 = 19294109) B19294109
theorem B8575159 : Blo 2007435 8575159 := bstep (se 1 (by rfl) ⟨6431369, by rfl⟩ : syracuseStep 8575159 = 12862739) B12862739
theorem B11433545 : Blo 2007435 11433545 := bstep (se 2 (by rfl) ⟨4287579, by rfl⟩ : syracuseStep 11433545 = 8575159) B8575159
theorem B7622363 : Blo 2007435 7622363 := bstep (se 1 (by rfl) ⟨5716772, by rfl⟩ : syracuseStep 7622363 = 11433545) B11433545
theorem B5081575 : Blo 2007435 5081575 := bstep (se 1 (by rfl) ⟨3811181, by rfl⟩ : syracuseStep 5081575 = 7622363) B7622363
theorem B6775433 : Blo 2007435 6775433 := bstep (se 2 (by rfl) ⟨2540787, by rfl⟩ : syracuseStep 6775433 = 5081575) B5081575
theorem B4516955 : Blo 2007435 4516955 := bstep (se 1 (by rfl) ⟨3387716, by rfl⟩ : syracuseStep 4516955 = 6775433) B6775433
theorem B3011303 : Blo 2007435 3011303 := bstep (se 1 (by rfl) ⟨2258477, by rfl⟩ : syracuseStep 3011303 = 4516955) B4516955
theorem B2007535 : Blo 2007435 2007535 := bstep (se 1 (by rfl) ⟨1505651, by rfl⟩ : syracuseStep 2007535 = 3011303) B3011303
theorem B3011309 : Blo 2007435 3011309 := bbase (se 3 (by rfl) ⟨564620, by rfl⟩ : syracuseStep 3011309 = 1129241) (by norm_num)
theorem B2007539 : Blo 2007435 2007539 := bstep (se 1 (by rfl) ⟨1505654, by rfl⟩ : syracuseStep 2007539 = 3011309) B3011309
theorem B4516973 : Blo 2007435 4516973 := bbase (se 3 (by rfl) ⟨846932, by rfl⟩ : syracuseStep 4516973 = 1693865) (by norm_num)
theorem B3011315 : Blo 2007435 3011315 := bstep (se 1 (by rfl) ⟨2258486, by rfl⟩ : syracuseStep 3011315 = 4516973) B4516973
theorem B2007543 : Blo 2007435 2007543 := bstep (se 1 (by rfl) ⟨1505657, by rfl⟩ : syracuseStep 2007543 = 3011315) B3011315
theorem B3811205 : Blo 2007435 3811205 := bbase (se 4 (by rfl) ⟨357300, by rfl⟩ : syracuseStep 3811205 = 714601) (by norm_num)
theorem B2540803 : Blo 2007435 2540803 := bstep (se 1 (by rfl) ⟨1905602, by rfl⟩ : syracuseStep 2540803 = 3811205) B3811205
theorem B3387737 : Blo 2007435 3387737 := bstep (se 2 (by rfl) ⟨1270401, by rfl⟩ : syracuseStep 3387737 = 2540803) B2540803
theorem B2258491 : Blo 2007435 2258491 := bstep (se 1 (by rfl) ⟨1693868, by rfl⟩ : syracuseStep 2258491 = 3387737) B3387737
theorem B3011321 : Blo 2007435 3011321 := bstep (se 2 (by rfl) ⟨1129245, by rfl⟩ : syracuseStep 3011321 = 2258491) B2258491
theorem B2007547 : Blo 2007435 2007547 := bstep (se 1 (by rfl) ⟨1505660, by rfl⟩ : syracuseStep 2007547 = 3011321) B3011321
theorem B36628949 : Blo 2007435 36628949 := bbase (se 7 (by rfl) ⟨429245, by rfl⟩ : syracuseStep 36628949 = 858491) (by norm_num)
theorem B97677197 : Blo 2007435 97677197 := bstep (se 3 (by rfl) ⟨18314474, by rfl⟩ : syracuseStep 97677197 = 36628949) B36628949
theorem B65118131 : Blo 2007435 65118131 := bstep (se 1 (by rfl) ⟨48838598, by rfl⟩ : syracuseStep 65118131 = 97677197) B97677197
theorem B43412087 : Blo 2007435 43412087 := bstep (se 1 (by rfl) ⟨32559065, by rfl⟩ : syracuseStep 43412087 = 65118131) B65118131
theorem B28941391 : Blo 2007435 28941391 := bstep (se 1 (by rfl) ⟨21706043, by rfl⟩ : syracuseStep 28941391 = 43412087) B43412087
theorem B38588521 : Blo 2007435 38588521 := bstep (se 2 (by rfl) ⟨14470695, by rfl⟩ : syracuseStep 38588521 = 28941391) B28941391
theorem B51451361 : Blo 2007435 51451361 := bstep (se 2 (by rfl) ⟨19294260, by rfl⟩ : syracuseStep 51451361 = 38588521) B38588521
theorem B34300907 : Blo 2007435 34300907 := bstep (se 1 (by rfl) ⟨25725680, by rfl⟩ : syracuseStep 34300907 = 51451361) B51451361
theorem B22867271 : Blo 2007435 22867271 := bstep (se 1 (by rfl) ⟨17150453, by rfl⟩ : syracuseStep 22867271 = 34300907) B34300907
theorem B15244847 : Blo 2007435 15244847 := bstep (se 1 (by rfl) ⟨11433635, by rfl⟩ : syracuseStep 15244847 = 22867271) B22867271
theorem B10163231 : Blo 2007435 10163231 := bstep (se 1 (by rfl) ⟨7622423, by rfl⟩ : syracuseStep 10163231 = 15244847) B15244847
theorem B6775487 : Blo 2007435 6775487 := bstep (se 1 (by rfl) ⟨5081615, by rfl⟩ : syracuseStep 6775487 = 10163231) B10163231
theorem B4516991 : Blo 2007435 4516991 := bstep (se 1 (by rfl) ⟨3387743, by rfl⟩ : syracuseStep 4516991 = 6775487) B6775487
theorem B3011327 : Blo 2007435 3011327 := bstep (se 1 (by rfl) ⟨2258495, by rfl⟩ : syracuseStep 3011327 = 4516991) B4516991
theorem B2007551 : Blo 2007435 2007551 := bstep (se 1 (by rfl) ⟨1505663, by rfl⟩ : syracuseStep 2007551 = 3011327) B3011327
theorem B3011333 : Blo 2007435 3011333 := bbase (se 4 (by rfl) ⟨282312, by rfl⟩ : syracuseStep 3011333 = 564625) (by norm_num)
theorem B2007555 : Blo 2007435 2007555 := bstep (se 1 (by rfl) ⟨1505666, by rfl⟩ : syracuseStep 2007555 = 3011333) B3011333
theorem B3387757 : Blo 2007435 3387757 := bbase (se 3 (by rfl) ⟨635204, by rfl⟩ : syracuseStep 3387757 = 1270409) (by norm_num)
theorem B4517009 : Blo 2007435 4517009 := bstep (se 2 (by rfl) ⟨1693878, by rfl⟩ : syracuseStep 4517009 = 3387757) B3387757
theorem B3011339 : Blo 2007435 3011339 := bstep (se 1 (by rfl) ⟨2258504, by rfl⟩ : syracuseStep 3011339 = 4517009) B4517009
theorem B2007559 : Blo 2007435 2007559 := bstep (se 1 (by rfl) ⟨1505669, by rfl⟩ : syracuseStep 2007559 = 3011339) B3011339
theorem B2258509 : Blo 2007435 2258509 := bbase (se 3 (by rfl) ⟨423470, by rfl⟩ : syracuseStep 2258509 = 846941) (by norm_num)
theorem B3011345 : Blo 2007435 3011345 := bstep (se 2 (by rfl) ⟨1129254, by rfl⟩ : syracuseStep 3011345 = 2258509) B2258509
theorem B2007563 : Blo 2007435 2007563 := bstep (se 1 (by rfl) ⟨1505672, by rfl⟩ : syracuseStep 2007563 = 3011345) B3011345
theorem B6775541 : Blo 2007435 6775541 := bbase (se 5 (by rfl) ⟨317603, by rfl⟩ : syracuseStep 6775541 = 635207) (by norm_num)
theorem B4517027 : Blo 2007435 4517027 := bstep (se 1 (by rfl) ⟨3387770, by rfl⟩ : syracuseStep 4517027 = 6775541) B6775541
theorem B3011351 : Blo 2007435 3011351 := bstep (se 1 (by rfl) ⟨2258513, by rfl⟩ : syracuseStep 3011351 = 4517027) B4517027
theorem B2007567 : Blo 2007435 2007567 := bstep (se 1 (by rfl) ⟨1505675, by rfl⟩ : syracuseStep 2007567 = 3011351) B3011351
theorem B3011357 : Blo 2007435 3011357 := bbase (se 3 (by rfl) ⟨564629, by rfl⟩ : syracuseStep 3011357 = 1129259) (by norm_num)
theorem B2007571 : Blo 2007435 2007571 := bstep (se 1 (by rfl) ⟨1505678, by rfl⟩ : syracuseStep 2007571 = 3011357) B3011357
theorem B4517045 : Blo 2007435 4517045 := bbase (se 5 (by rfl) ⟨211736, by rfl⟩ : syracuseStep 4517045 = 423473) (by norm_num)
theorem B3011363 : Blo 2007435 3011363 := bstep (se 1 (by rfl) ⟨2258522, by rfl⟩ : syracuseStep 3011363 = 4517045) B4517045
theorem B2007575 : Blo 2007435 2007575 := bstep (se 1 (by rfl) ⟨1505681, by rfl⟩ : syracuseStep 2007575 = 3011363) B3011363
theorem B2143837 : Blo 2007435 2143837 := bbase (se 3 (by rfl) ⟨401969, by rfl⟩ : syracuseStep 2143837 = 803939) (by norm_num)
theorem B11433797 : Blo 2007435 11433797 := bstep (se 4 (by rfl) ⟨1071918, by rfl⟩ : syracuseStep 11433797 = 2143837) B2143837
theorem B7622531 : Blo 2007435 7622531 := bstep (se 1 (by rfl) ⟨5716898, by rfl⟩ : syracuseStep 7622531 = 11433797) B11433797
theorem B5081687 : Blo 2007435 5081687 := bstep (se 1 (by rfl) ⟨3811265, by rfl⟩ : syracuseStep 5081687 = 7622531) B7622531
theorem B3387791 : Blo 2007435 3387791 := bstep (se 1 (by rfl) ⟨2540843, by rfl⟩ : syracuseStep 3387791 = 5081687) B5081687
theorem B2258527 : Blo 2007435 2258527 := bstep (se 1 (by rfl) ⟨1693895, by rfl⟩ : syracuseStep 2258527 = 3387791) B3387791
theorem B3011369 : Blo 2007435 3011369 := bstep (se 2 (by rfl) ⟨1129263, by rfl⟩ : syracuseStep 3011369 = 2258527) B2258527
theorem B2007579 : Blo 2007435 2007579 := bstep (se 1 (by rfl) ⟨1505684, by rfl⟩ : syracuseStep 2007579 = 3011369) B3011369
theorem B2143841 : Blo 2007435 2143841 := bbase (se 2 (by rfl) ⟨803940, by rfl⟩ : syracuseStep 2143841 = 1607881) (by norm_num)
theorem B5716909 : Blo 2007435 5716909 := bstep (se 3 (by rfl) ⟨1071920, by rfl⟩ : syracuseStep 5716909 = 2143841) B2143841
theorem B7622545 : Blo 2007435 7622545 := bstep (se 2 (by rfl) ⟨2858454, by rfl⟩ : syracuseStep 7622545 = 5716909) B5716909
theorem B10163393 : Blo 2007435 10163393 := bstep (se 2 (by rfl) ⟨3811272, by rfl⟩ : syracuseStep 10163393 = 7622545) B7622545
theorem B6775595 : Blo 2007435 6775595 := bstep (se 1 (by rfl) ⟨5081696, by rfl⟩ : syracuseStep 6775595 = 10163393) B10163393
theorem B4517063 : Blo 2007435 4517063 := bstep (se 1 (by rfl) ⟨3387797, by rfl⟩ : syracuseStep 4517063 = 6775595) B6775595
theorem B3011375 : Blo 2007435 3011375 := bstep (se 1 (by rfl) ⟨2258531, by rfl⟩ : syracuseStep 3011375 = 4517063) B4517063
theorem B2007583 : Blo 2007435 2007583 := bstep (se 1 (by rfl) ⟨1505687, by rfl⟩ : syracuseStep 2007583 = 3011375) B3011375
theorem B3011381 : Blo 2007435 3011381 := bbase (se 5 (by rfl) ⟨141158, by rfl⟩ : syracuseStep 3011381 = 282317) (by norm_num)
theorem B2007587 : Blo 2007435 2007587 := bstep (se 1 (by rfl) ⟨1505690, by rfl⟩ : syracuseStep 2007587 = 3011381) B3011381
theorem B5081717 : Blo 2007435 5081717 := bbase (se 5 (by rfl) ⟨238205, by rfl⟩ : syracuseStep 5081717 = 476411) (by norm_num)
theorem B3387811 : Blo 2007435 3387811 := bstep (se 1 (by rfl) ⟨2540858, by rfl⟩ : syracuseStep 3387811 = 5081717) B5081717
theorem B4517081 : Blo 2007435 4517081 := bstep (se 2 (by rfl) ⟨1693905, by rfl⟩ : syracuseStep 4517081 = 3387811) B3387811
theorem B3011387 : Blo 2007435 3011387 := bstep (se 1 (by rfl) ⟨2258540, by rfl⟩ : syracuseStep 3011387 = 4517081) B4517081
theorem B2007591 : Blo 2007435 2007591 := bstep (se 1 (by rfl) ⟨1505693, by rfl⟩ : syracuseStep 2007591 = 3011387) B3011387
theorem B2258545 : Blo 2007435 2258545 := bbase (se 2 (by rfl) ⟨846954, by rfl⟩ : syracuseStep 2258545 = 1693909) (by norm_num)
theorem B3011393 : Blo 2007435 3011393 := bstep (se 2 (by rfl) ⟨1129272, by rfl⟩ : syracuseStep 3011393 = 2258545) B2258545
theorem B2007595 : Blo 2007435 2007595 := bstep (se 1 (by rfl) ⟨1505696, by rfl⟩ : syracuseStep 2007595 = 3011393) B3011393
theorem B2062757 : Blo 2007435 2062757 := bbase (se 4 (by rfl) ⟨193383, by rfl⟩ : syracuseStep 2062757 = 386767) (by norm_num)
theorem B5500685 : Blo 2007435 5500685 := bstep (se 3 (by rfl) ⟨1031378, by rfl⟩ : syracuseStep 5500685 = 2062757) B2062757
theorem B3667123 : Blo 2007435 3667123 := bstep (se 1 (by rfl) ⟨2750342, by rfl⟩ : syracuseStep 3667123 = 5500685) B5500685
theorem B4889497 : Blo 2007435 4889497 := bstep (se 2 (by rfl) ⟨1833561, by rfl⟩ : syracuseStep 4889497 = 3667123) B3667123
theorem B6519329 : Blo 2007435 6519329 := bstep (se 2 (by rfl) ⟨2444748, by rfl⟩ : syracuseStep 6519329 = 4889497) B4889497
theorem B4346219 : Blo 2007435 4346219 := bstep (se 1 (by rfl) ⟨3259664, by rfl⟩ : syracuseStep 4346219 = 6519329) B6519329
theorem B2897479 : Blo 2007435 2897479 := bstep (se 1 (by rfl) ⟨2173109, by rfl⟩ : syracuseStep 2897479 = 4346219) B4346219
theorem B3863305 : Blo 2007435 3863305 := bstep (se 2 (by rfl) ⟨1448739, by rfl⟩ : syracuseStep 3863305 = 2897479) B2897479
theorem B5151073 : Blo 2007435 5151073 := bstep (se 2 (by rfl) ⟨1931652, by rfl⟩ : syracuseStep 5151073 = 3863305) B3863305
theorem B6868097 : Blo 2007435 6868097 := bstep (se 2 (by rfl) ⟨2575536, by rfl⟩ : syracuseStep 6868097 = 5151073) B5151073
theorem B4578731 : Blo 2007435 4578731 := bstep (se 1 (by rfl) ⟨3434048, by rfl⟩ : syracuseStep 4578731 = 6868097) B6868097
theorem B3052487 : Blo 2007435 3052487 := bstep (se 1 (by rfl) ⟨2289365, by rfl⟩ : syracuseStep 3052487 = 4578731) B4578731
theorem B2034991 : Blo 2007435 2034991 := bstep (se 1 (by rfl) ⟨1526243, by rfl⟩ : syracuseStep 2034991 = 3052487) B3052487
theorem B2713321 : Blo 2007435 2713321 := bstep (se 2 (by rfl) ⟨1017495, by rfl⟩ : syracuseStep 2713321 = 2034991) B2034991
theorem B14471045 : Blo 2007435 14471045 := bstep (se 4 (by rfl) ⟨1356660, by rfl⟩ : syracuseStep 14471045 = 2713321) B2713321
theorem B9647363 : Blo 2007435 9647363 := bstep (se 1 (by rfl) ⟨7235522, by rfl⟩ : syracuseStep 9647363 = 14471045) B14471045
theorem B6431575 : Blo 2007435 6431575 := bstep (se 1 (by rfl) ⟨4823681, by rfl⟩ : syracuseStep 6431575 = 9647363) B9647363
theorem B8575433 : Blo 2007435 8575433 := bstep (se 2 (by rfl) ⟨3215787, by rfl⟩ : syracuseStep 8575433 = 6431575) B6431575
theorem B5716955 : Blo 2007435 5716955 := bstep (se 1 (by rfl) ⟨4287716, by rfl⟩ : syracuseStep 5716955 = 8575433) B8575433
theorem B3811303 : Blo 2007435 3811303 := bstep (se 1 (by rfl) ⟨2858477, by rfl⟩ : syracuseStep 3811303 = 5716955) B5716955
theorem B5081737 : Blo 2007435 5081737 := bstep (se 2 (by rfl) ⟨1905651, by rfl⟩ : syracuseStep 5081737 = 3811303) B3811303
theorem B6775649 : Blo 2007435 6775649 := bstep (se 2 (by rfl) ⟨2540868, by rfl⟩ : syracuseStep 6775649 = 5081737) B5081737
theorem B4517099 : Blo 2007435 4517099 := bstep (se 1 (by rfl) ⟨3387824, by rfl⟩ : syracuseStep 4517099 = 6775649) B6775649
theorem B3011399 : Blo 2007435 3011399 := bstep (se 1 (by rfl) ⟨2258549, by rfl⟩ : syracuseStep 3011399 = 4517099) B4517099
theorem B2007599 : Blo 2007435 2007599 := bstep (se 1 (by rfl) ⟨1505699, by rfl⟩ : syracuseStep 2007599 = 3011399) B3011399
theorem B3011405 : Blo 2007435 3011405 := bbase (se 3 (by rfl) ⟨564638, by rfl⟩ : syracuseStep 3011405 = 1129277) (by norm_num)
theorem B2007603 : Blo 2007435 2007603 := bstep (se 1 (by rfl) ⟨1505702, by rfl⟩ : syracuseStep 2007603 = 3011405) B3011405
theorem B4517117 : Blo 2007435 4517117 := bbase (se 3 (by rfl) ⟨846959, by rfl⟩ : syracuseStep 4517117 = 1693919) (by norm_num)
theorem B3011411 : Blo 2007435 3011411 := bstep (se 1 (by rfl) ⟨2258558, by rfl⟩ : syracuseStep 3011411 = 4517117) B4517117
theorem B2007607 : Blo 2007435 2007607 := bstep (se 1 (by rfl) ⟨1505705, by rfl⟩ : syracuseStep 2007607 = 3011411) B3011411
theorem B3387845 : Blo 2007435 3387845 := bbase (se 4 (by rfl) ⟨317610, by rfl⟩ : syracuseStep 3387845 = 635221) (by norm_num)
theorem B2258563 : Blo 2007435 2258563 := bstep (se 1 (by rfl) ⟨1693922, by rfl⟩ : syracuseStep 2258563 = 3387845) B3387845
theorem B3011417 : Blo 2007435 3011417 := bstep (se 2 (by rfl) ⟨1129281, by rfl⟩ : syracuseStep 3011417 = 2258563) B2258563
theorem B2007611 : Blo 2007435 2007611 := bstep (se 1 (by rfl) ⟨1505708, by rfl⟩ : syracuseStep 2007611 = 3011417) B3011417
theorem B15245333 : Blo 2007435 15245333 := bbase (se 6 (by rfl) ⟨357312, by rfl⟩ : syracuseStep 15245333 = 714625) (by norm_num)
theorem B10163555 : Blo 2007435 10163555 := bstep (se 1 (by rfl) ⟨7622666, by rfl⟩ : syracuseStep 10163555 = 15245333) B15245333
theorem B6775703 : Blo 2007435 6775703 := bstep (se 1 (by rfl) ⟨5081777, by rfl⟩ : syracuseStep 6775703 = 10163555) B10163555
theorem B4517135 : Blo 2007435 4517135 := bstep (se 1 (by rfl) ⟨3387851, by rfl⟩ : syracuseStep 4517135 = 6775703) B6775703
theorem B3011423 : Blo 2007435 3011423 := bstep (se 1 (by rfl) ⟨2258567, by rfl⟩ : syracuseStep 3011423 = 4517135) B4517135
theorem B2007615 : Blo 2007435 2007615 := bstep (se 1 (by rfl) ⟨1505711, by rfl⟩ : syracuseStep 2007615 = 3011423) B3011423
theorem B3011429 : Blo 2007435 3011429 := bbase (se 4 (by rfl) ⟨282321, by rfl⟩ : syracuseStep 3011429 = 564643) (by norm_num)
theorem B2007619 : Blo 2007435 2007619 := bstep (se 1 (by rfl) ⟨1505714, by rfl⟩ : syracuseStep 2007619 = 3011429) B3011429
theorem B3811349 : Blo 2007435 3811349 := bbase (se 6 (by rfl) ⟨89328, by rfl⟩ : syracuseStep 3811349 = 178657) (by norm_num)
theorem B2540899 : Blo 2007435 2540899 := bstep (se 1 (by rfl) ⟨1905674, by rfl⟩ : syracuseStep 2540899 = 3811349) B3811349
theorem B3387865 : Blo 2007435 3387865 := bstep (se 2 (by rfl) ⟨1270449, by rfl⟩ : syracuseStep 3387865 = 2540899) B2540899
theorem B4517153 : Blo 2007435 4517153 := bstep (se 2 (by rfl) ⟨1693932, by rfl⟩ : syracuseStep 4517153 = 3387865) B3387865
theorem B3011435 : Blo 2007435 3011435 := bstep (se 1 (by rfl) ⟨2258576, by rfl⟩ : syracuseStep 3011435 = 4517153) B4517153
theorem B2007623 : Blo 2007435 2007623 := bstep (se 1 (by rfl) ⟨1505717, by rfl⟩ : syracuseStep 2007623 = 3011435) B3011435
theorem B2258581 : Blo 2007435 2258581 := bbase (se 6 (by rfl) ⟨52935, by rfl⟩ : syracuseStep 2258581 = 105871) (by norm_num)
theorem B3011441 : Blo 2007435 3011441 := bstep (se 2 (by rfl) ⟨1129290, by rfl⟩ : syracuseStep 3011441 = 2258581) B2258581
theorem B2007627 : Blo 2007435 2007627 := bstep (se 1 (by rfl) ⟨1505720, by rfl⟩ : syracuseStep 2007627 = 3011441) B3011441
theorem B2540909 : Blo 2007435 2540909 := bbase (se 3 (by rfl) ⟨476420, by rfl⟩ : syracuseStep 2540909 = 952841) (by norm_num)
theorem B6775757 : Blo 2007435 6775757 := bstep (se 3 (by rfl) ⟨1270454, by rfl⟩ : syracuseStep 6775757 = 2540909) B2540909
theorem B4517171 : Blo 2007435 4517171 := bstep (se 1 (by rfl) ⟨3387878, by rfl⟩ : syracuseStep 4517171 = 6775757) B6775757
theorem B3011447 : Blo 2007435 3011447 := bstep (se 1 (by rfl) ⟨2258585, by rfl⟩ : syracuseStep 3011447 = 4517171) B4517171
theorem B2007631 : Blo 2007435 2007631 := bstep (se 1 (by rfl) ⟨1505723, by rfl⟩ : syracuseStep 2007631 = 3011447) B3011447
theorem B3011453 : Blo 2007435 3011453 := bbase (se 3 (by rfl) ⟨564647, by rfl⟩ : syracuseStep 3011453 = 1129295) (by norm_num)
theorem B2007635 : Blo 2007435 2007635 := bstep (se 1 (by rfl) ⟨1505726, by rfl⟩ : syracuseStep 2007635 = 3011453) B3011453
theorem B4517189 : Blo 2007435 4517189 := bbase (se 4 (by rfl) ⟨423486, by rfl⟩ : syracuseStep 4517189 = 846973) (by norm_num)
theorem B3011459 : Blo 2007435 3011459 := bstep (se 1 (by rfl) ⟨2258594, by rfl⟩ : syracuseStep 3011459 = 4517189) B4517189
theorem B2007639 : Blo 2007435 2007639 := bstep (se 1 (by rfl) ⟨1505729, by rfl⟩ : syracuseStep 2007639 = 3011459) B3011459
theorem B6431717 : Blo 2007435 6431717 := bbase (se 4 (by rfl) ⟨602973, by rfl⟩ : syracuseStep 6431717 = 1205947) (by norm_num)
theorem B4287811 : Blo 2007435 4287811 := bstep (se 1 (by rfl) ⟨3215858, by rfl⟩ : syracuseStep 4287811 = 6431717) B6431717
theorem B5717081 : Blo 2007435 5717081 := bstep (se 2 (by rfl) ⟨2143905, by rfl⟩ : syracuseStep 5717081 = 4287811) B4287811
theorem B3811387 : Blo 2007435 3811387 := bstep (se 1 (by rfl) ⟨2858540, by rfl⟩ : syracuseStep 3811387 = 5717081) B5717081
theorem B5081849 : Blo 2007435 5081849 := bstep (se 2 (by rfl) ⟨1905693, by rfl⟩ : syracuseStep 5081849 = 3811387) B3811387
theorem B3387899 : Blo 2007435 3387899 := bstep (se 1 (by rfl) ⟨2540924, by rfl⟩ : syracuseStep 3387899 = 5081849) B5081849
theorem B2258599 : Blo 2007435 2258599 := bstep (se 1 (by rfl) ⟨1693949, by rfl⟩ : syracuseStep 2258599 = 3387899) B3387899
theorem B3011465 : Blo 2007435 3011465 := bstep (se 2 (by rfl) ⟨1129299, by rfl⟩ : syracuseStep 3011465 = 2258599) B2258599
theorem B2007643 : Blo 2007435 2007643 := bstep (se 1 (by rfl) ⟨1505732, by rfl⟩ : syracuseStep 2007643 = 3011465) B3011465
theorem B10163717 : Blo 2007435 10163717 := bbase (se 4 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 10163717 = 1905697) (by norm_num)
theorem B6775811 : Blo 2007435 6775811 := bstep (se 1 (by rfl) ⟨5081858, by rfl⟩ : syracuseStep 6775811 = 10163717) B10163717
theorem B4517207 : Blo 2007435 4517207 := bstep (se 1 (by rfl) ⟨3387905, by rfl⟩ : syracuseStep 4517207 = 6775811) B6775811
theorem B3011471 : Blo 2007435 3011471 := bstep (se 1 (by rfl) ⟨2258603, by rfl⟩ : syracuseStep 3011471 = 4517207) B4517207
theorem B2007647 : Blo 2007435 2007647 := bstep (se 1 (by rfl) ⟨1505735, by rfl⟩ : syracuseStep 2007647 = 3011471) B3011471
theorem B3011477 : Blo 2007435 3011477 := bbase (se 6 (by rfl) ⟨70581, by rfl⟩ : syracuseStep 3011477 = 141163) (by norm_num)
theorem B2007651 : Blo 2007435 2007651 := bstep (se 1 (by rfl) ⟨1505738, by rfl⟩ : syracuseStep 2007651 = 3011477) B3011477
theorem B11434229 : Blo 2007435 11434229 := bbase (se 5 (by rfl) ⟨535979, by rfl⟩ : syracuseStep 11434229 = 1071959) (by norm_num)
theorem B7622819 : Blo 2007435 7622819 := bstep (se 1 (by rfl) ⟨5717114, by rfl⟩ : syracuseStep 7622819 = 11434229) B11434229
theorem B5081879 : Blo 2007435 5081879 := bstep (se 1 (by rfl) ⟨3811409, by rfl⟩ : syracuseStep 5081879 = 7622819) B7622819
theorem B3387919 : Blo 2007435 3387919 := bstep (se 1 (by rfl) ⟨2540939, by rfl⟩ : syracuseStep 3387919 = 5081879) B5081879
theorem B4517225 : Blo 2007435 4517225 := bstep (se 2 (by rfl) ⟨1693959, by rfl⟩ : syracuseStep 4517225 = 3387919) B3387919
theorem B3011483 : Blo 2007435 3011483 := bstep (se 1 (by rfl) ⟨2258612, by rfl⟩ : syracuseStep 3011483 = 4517225) B4517225
theorem B2007655 : Blo 2007435 2007655 := bstep (se 1 (by rfl) ⟨1505741, by rfl⟩ : syracuseStep 2007655 = 3011483) B3011483
theorem B2258617 : Blo 2007435 2258617 := bbase (se 2 (by rfl) ⟨846981, by rfl⟩ : syracuseStep 2258617 = 1693963) (by norm_num)
theorem B3011489 : Blo 2007435 3011489 := bstep (se 2 (by rfl) ⟨1129308, by rfl⟩ : syracuseStep 3011489 = 2258617) B2258617
theorem B2007659 : Blo 2007435 2007659 := bstep (se 1 (by rfl) ⟨1505744, by rfl⟩ : syracuseStep 2007659 = 3011489) B3011489
theorem B4287853 : Blo 2007435 4287853 := bbase (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) (by norm_num)
theorem B5717137 : Blo 2007435 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B7622849 : Blo 2007435 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B5081899 : Blo 2007435 5081899 := bstep (se 1 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 5081899 = 7622849) B7622849
theorem B6775865 : Blo 2007435 6775865 := bstep (se 2 (by rfl) ⟨2540949, by rfl⟩ : syracuseStep 6775865 = 5081899) B5081899
theorem B4517243 : Blo 2007435 4517243 := bstep (se 1 (by rfl) ⟨3387932, by rfl⟩ : syracuseStep 4517243 = 6775865) B6775865
theorem B3011495 : Blo 2007435 3011495 := bstep (se 1 (by rfl) ⟨2258621, by rfl⟩ : syracuseStep 3011495 = 4517243) B4517243
theorem B2007663 : Blo 2007435 2007663 := bstep (se 1 (by rfl) ⟨1505747, by rfl⟩ : syracuseStep 2007663 = 3011495) B3011495
theorem B3011501 : Blo 2007435 3011501 := bbase (se 3 (by rfl) ⟨564656, by rfl⟩ : syracuseStep 3011501 = 1129313) (by norm_num)
theorem B2007667 : Blo 2007435 2007667 := bstep (se 1 (by rfl) ⟨1505750, by rfl⟩ : syracuseStep 2007667 = 3011501) B3011501
theorem B4517261 : Blo 2007435 4517261 := bbase (se 3 (by rfl) ⟨846986, by rfl⟩ : syracuseStep 4517261 = 1693973) (by norm_num)
theorem B3011507 : Blo 2007435 3011507 := bstep (se 1 (by rfl) ⟨2258630, by rfl⟩ : syracuseStep 3011507 = 4517261) B4517261
theorem B2007671 : Blo 2007435 2007671 := bstep (se 1 (by rfl) ⟨1505753, by rfl⟩ : syracuseStep 2007671 = 3011507) B3011507
theorem B2540965 : Blo 2007435 2540965 := bbase (se 4 (by rfl) ⟨238215, by rfl⟩ : syracuseStep 2540965 = 476431) (by norm_num)
theorem B3387953 : Blo 2007435 3387953 := bstep (se 2 (by rfl) ⟨1270482, by rfl⟩ : syracuseStep 3387953 = 2540965) B2540965
theorem B2258635 : Blo 2007435 2258635 := bstep (se 1 (by rfl) ⟨1693976, by rfl⟩ : syracuseStep 2258635 = 3387953) B3387953
theorem B3011513 : Blo 2007435 3011513 := bstep (se 2 (by rfl) ⟨1129317, by rfl⟩ : syracuseStep 3011513 = 2258635) B2258635
theorem B2007675 : Blo 2007435 2007675 := bstep (se 1 (by rfl) ⟨1505756, by rfl⟩ : syracuseStep 2007675 = 3011513) B3011513
theorem B26434133 : Blo 2007435 26434133 := bbase (se 8 (by rfl) ⟨154887, by rfl⟩ : syracuseStep 26434133 = 309775) (by norm_num)
theorem B17622755 : Blo 2007435 17622755 := bstep (se 1 (by rfl) ⟨13217066, by rfl⟩ : syracuseStep 17622755 = 26434133) B26434133
theorem B11748503 : Blo 2007435 11748503 := bstep (se 1 (by rfl) ⟨8811377, by rfl⟩ : syracuseStep 11748503 = 17622755) B17622755
theorem B31329341 : Blo 2007435 31329341 := bstep (se 3 (by rfl) ⟨5874251, by rfl⟩ : syracuseStep 31329341 = 11748503) B11748503
theorem B20886227 : Blo 2007435 20886227 := bstep (se 1 (by rfl) ⟨15664670, by rfl⟩ : syracuseStep 20886227 = 31329341) B31329341
theorem B13924151 : Blo 2007435 13924151 := bstep (se 1 (by rfl) ⟨10443113, by rfl⟩ : syracuseStep 13924151 = 20886227) B20886227
theorem B9282767 : Blo 2007435 9282767 := bstep (se 1 (by rfl) ⟨6962075, by rfl⟩ : syracuseStep 9282767 = 13924151) B13924151
theorem B99016181 : Blo 2007435 99016181 := bstep (se 5 (by rfl) ⟨4641383, by rfl⟩ : syracuseStep 99016181 = 9282767) B9282767
theorem B66010787 : Blo 2007435 66010787 := bstep (se 1 (by rfl) ⟨49508090, by rfl⟩ : syracuseStep 66010787 = 99016181) B99016181
theorem B44007191 : Blo 2007435 44007191 := bstep (se 1 (by rfl) ⟨33005393, by rfl⟩ : syracuseStep 44007191 = 66010787) B66010787
theorem B29338127 : Blo 2007435 29338127 := bstep (se 1 (by rfl) ⟨22003595, by rfl⟩ : syracuseStep 29338127 = 44007191) B44007191
theorem B19558751 : Blo 2007435 19558751 := bstep (se 1 (by rfl) ⟨14669063, by rfl⟩ : syracuseStep 19558751 = 29338127) B29338127
theorem B52156669 : Blo 2007435 52156669 := bstep (se 3 (by rfl) ⟨9779375, by rfl⟩ : syracuseStep 52156669 = 19558751) B19558751
theorem B69542225 : Blo 2007435 69542225 := bstep (se 2 (by rfl) ⟨26078334, by rfl⟩ : syracuseStep 69542225 = 52156669) B52156669
theorem B46361483 : Blo 2007435 46361483 := bstep (se 1 (by rfl) ⟨34771112, by rfl⟩ : syracuseStep 46361483 = 69542225) B69542225
theorem B30907655 : Blo 2007435 30907655 := bstep (se 1 (by rfl) ⟨23180741, by rfl⟩ : syracuseStep 30907655 = 46361483) B46361483
theorem B20605103 : Blo 2007435 20605103 := bstep (se 1 (by rfl) ⟨15453827, by rfl⟩ : syracuseStep 20605103 = 30907655) B30907655
theorem B13736735 : Blo 2007435 13736735 := bstep (se 1 (by rfl) ⟨10302551, by rfl⟩ : syracuseStep 13736735 = 20605103) B20605103
theorem B9157823 : Blo 2007435 9157823 := bstep (se 1 (by rfl) ⟨6868367, by rfl⟩ : syracuseStep 9157823 = 13736735) B13736735
theorem B6105215 : Blo 2007435 6105215 := bstep (se 1 (by rfl) ⟨4578911, by rfl⟩ : syracuseStep 6105215 = 9157823) B9157823
theorem B4070143 : Blo 2007435 4070143 := bstep (se 1 (by rfl) ⟨3052607, by rfl⟩ : syracuseStep 4070143 = 6105215) B6105215
theorem B5426857 : Blo 2007435 5426857 := bstep (se 2 (by rfl) ⟨2035071, by rfl⟩ : syracuseStep 5426857 = 4070143) B4070143
theorem B28943237 : Blo 2007435 28943237 := bstep (se 4 (by rfl) ⟨2713428, by rfl⟩ : syracuseStep 28943237 = 5426857) B5426857
theorem B19295491 : Blo 2007435 19295491 := bstep (se 1 (by rfl) ⟨14471618, by rfl⟩ : syracuseStep 19295491 = 28943237) B28943237
theorem B25727321 : Blo 2007435 25727321 := bstep (se 2 (by rfl) ⟨9647745, by rfl⟩ : syracuseStep 25727321 = 19295491) B19295491
theorem B17151547 : Blo 2007435 17151547 := bstep (se 1 (by rfl) ⟨12863660, by rfl⟩ : syracuseStep 17151547 = 25727321) B25727321
theorem B22868729 : Blo 2007435 22868729 := bstep (se 2 (by rfl) ⟨8575773, by rfl⟩ : syracuseStep 22868729 = 17151547) B17151547
theorem B15245819 : Blo 2007435 15245819 := bstep (se 1 (by rfl) ⟨11434364, by rfl⟩ : syracuseStep 15245819 = 22868729) B22868729
theorem B10163879 : Blo 2007435 10163879 := bstep (se 1 (by rfl) ⟨7622909, by rfl⟩ : syracuseStep 10163879 = 15245819) B15245819
theorem B6775919 : Blo 2007435 6775919 := bstep (se 1 (by rfl) ⟨5081939, by rfl⟩ : syracuseStep 6775919 = 10163879) B10163879
theorem B4517279 : Blo 2007435 4517279 := bstep (se 1 (by rfl) ⟨3387959, by rfl⟩ : syracuseStep 4517279 = 6775919) B6775919
theorem B3011519 : Blo 2007435 3011519 := bstep (se 1 (by rfl) ⟨2258639, by rfl⟩ : syracuseStep 3011519 = 4517279) B4517279
theorem B2007679 : Blo 2007435 2007679 := bstep (se 1 (by rfl) ⟨1505759, by rfl⟩ : syracuseStep 2007679 = 3011519) B3011519
theorem B3011525 : Blo 2007435 3011525 := bbase (se 4 (by rfl) ⟨282330, by rfl⟩ : syracuseStep 3011525 = 564661) (by norm_num)
theorem B2007683 : Blo 2007435 2007683 := bstep (se 1 (by rfl) ⟨1505762, by rfl⟩ : syracuseStep 2007683 = 3011525) B3011525
theorem B3387973 : Blo 2007435 3387973 := bbase (se 4 (by rfl) ⟨317622, by rfl⟩ : syracuseStep 3387973 = 635245) (by norm_num)
theorem B4517297 : Blo 2007435 4517297 := bstep (se 2 (by rfl) ⟨1693986, by rfl⟩ : syracuseStep 4517297 = 3387973) B3387973
theorem B3011531 : Blo 2007435 3011531 := bstep (se 1 (by rfl) ⟨2258648, by rfl⟩ : syracuseStep 3011531 = 4517297) B4517297
theorem B2007687 : Blo 2007435 2007687 := bstep (se 1 (by rfl) ⟨1505765, by rfl⟩ : syracuseStep 2007687 = 3011531) B3011531
theorem B2258653 : Blo 2007435 2258653 := bbase (se 3 (by rfl) ⟨423497, by rfl⟩ : syracuseStep 2258653 = 846995) (by norm_num)
theorem B3011537 : Blo 2007435 3011537 := bstep (se 2 (by rfl) ⟨1129326, by rfl⟩ : syracuseStep 3011537 = 2258653) B2258653
theorem B2007691 : Blo 2007435 2007691 := bstep (se 1 (by rfl) ⟨1505768, by rfl⟩ : syracuseStep 2007691 = 3011537) B3011537
theorem B6775973 : Blo 2007435 6775973 := bbase (se 4 (by rfl) ⟨635247, by rfl⟩ : syracuseStep 6775973 = 1270495) (by norm_num)
theorem B4517315 : Blo 2007435 4517315 := bstep (se 1 (by rfl) ⟨3387986, by rfl⟩ : syracuseStep 4517315 = 6775973) B6775973
theorem B3011543 : Blo 2007435 3011543 := bstep (se 1 (by rfl) ⟨2258657, by rfl⟩ : syracuseStep 3011543 = 4517315) B4517315
theorem B2007695 : Blo 2007435 2007695 := bstep (se 1 (by rfl) ⟨1505771, by rfl⟩ : syracuseStep 2007695 = 3011543) B3011543
theorem B3011549 : Blo 2007435 3011549 := bbase (se 3 (by rfl) ⟨564665, by rfl⟩ : syracuseStep 3011549 = 1129331) (by norm_num)
theorem B2007699 : Blo 2007435 2007699 := bstep (se 1 (by rfl) ⟨1505774, by rfl⟩ : syracuseStep 2007699 = 3011549) B3011549
theorem B4517333 : Blo 2007435 4517333 := bbase (se 7 (by rfl) ⟨52937, by rfl⟩ : syracuseStep 4517333 = 105875) (by norm_num)
theorem B3011555 : Blo 2007435 3011555 := bstep (se 1 (by rfl) ⟨2258666, by rfl⟩ : syracuseStep 3011555 = 4517333) B4517333
theorem B2007703 : Blo 2007435 2007703 := bstep (se 1 (by rfl) ⟨1505777, by rfl⟩ : syracuseStep 2007703 = 3011555) B3011555
theorem B19295765 : Blo 2007435 19295765 := bbase (se 6 (by rfl) ⟨452244, by rfl⟩ : syracuseStep 19295765 = 904489) (by norm_num)
theorem B12863843 : Blo 2007435 12863843 := bstep (se 1 (by rfl) ⟨9647882, by rfl⟩ : syracuseStep 12863843 = 19295765) B19295765
theorem B8575895 : Blo 2007435 8575895 := bstep (se 1 (by rfl) ⟨6431921, by rfl⟩ : syracuseStep 8575895 = 12863843) B12863843
theorem B5717263 : Blo 2007435 5717263 := bstep (se 1 (by rfl) ⟨4287947, by rfl⟩ : syracuseStep 5717263 = 8575895) B8575895
theorem B7623017 : Blo 2007435 7623017 := bstep (se 2 (by rfl) ⟨2858631, by rfl⟩ : syracuseStep 7623017 = 5717263) B5717263
theorem B5082011 : Blo 2007435 5082011 := bstep (se 1 (by rfl) ⟨3811508, by rfl⟩ : syracuseStep 5082011 = 7623017) B7623017
theorem B3388007 : Blo 2007435 3388007 := bstep (se 1 (by rfl) ⟨2541005, by rfl⟩ : syracuseStep 3388007 = 5082011) B5082011
theorem B2258671 : Blo 2007435 2258671 := bstep (se 1 (by rfl) ⟨1694003, by rfl⟩ : syracuseStep 2258671 = 3388007) B3388007
theorem B3011561 : Blo 2007435 3011561 := bstep (se 2 (by rfl) ⟨1129335, by rfl⟩ : syracuseStep 3011561 = 2258671) B2258671
theorem B2007707 : Blo 2007435 2007707 := bstep (se 1 (by rfl) ⟨1505780, by rfl⟩ : syracuseStep 2007707 = 3011561) B3011561
theorem B2289493 : Blo 2007435 2289493 := bbase (se 9 (by rfl) ⟨6707, by rfl⟩ : syracuseStep 2289493 = 13415) (by norm_num)
theorem B3052657 : Blo 2007435 3052657 := bstep (se 2 (by rfl) ⟨1144746, by rfl⟩ : syracuseStep 3052657 = 2289493) B2289493
theorem B4070209 : Blo 2007435 4070209 := bstep (se 2 (by rfl) ⟨1526328, by rfl⟩ : syracuseStep 4070209 = 3052657) B3052657
theorem B5426945 : Blo 2007435 5426945 := bstep (se 2 (by rfl) ⟨2035104, by rfl⟩ : syracuseStep 5426945 = 4070209) B4070209
theorem B3617963 : Blo 2007435 3617963 := bstep (se 1 (by rfl) ⟨2713472, by rfl⟩ : syracuseStep 3617963 = 5426945) B5426945
theorem B2411975 : Blo 2007435 2411975 := bstep (se 1 (by rfl) ⟨1808981, by rfl⟩ : syracuseStep 2411975 = 3617963) B3617963
theorem B6431933 : Blo 2007435 6431933 := bstep (se 3 (by rfl) ⟨1205987, by rfl⟩ : syracuseStep 6431933 = 2411975) B2411975
theorem B17151821 : Blo 2007435 17151821 := bstep (se 3 (by rfl) ⟨3215966, by rfl⟩ : syracuseStep 17151821 = 6431933) B6431933
theorem B11434547 : Blo 2007435 11434547 := bstep (se 1 (by rfl) ⟨8575910, by rfl⟩ : syracuseStep 11434547 = 17151821) B17151821
theorem B7623031 : Blo 2007435 7623031 := bstep (se 1 (by rfl) ⟨5717273, by rfl⟩ : syracuseStep 7623031 = 11434547) B11434547
theorem B10164041 : Blo 2007435 10164041 := bstep (se 2 (by rfl) ⟨3811515, by rfl⟩ : syracuseStep 10164041 = 7623031) B7623031
theorem B6776027 : Blo 2007435 6776027 := bstep (se 1 (by rfl) ⟨5082020, by rfl⟩ : syracuseStep 6776027 = 10164041) B10164041
theorem B4517351 : Blo 2007435 4517351 := bstep (se 1 (by rfl) ⟨3388013, by rfl⟩ : syracuseStep 4517351 = 6776027) B6776027
theorem B3011567 : Blo 2007435 3011567 := bstep (se 1 (by rfl) ⟨2258675, by rfl⟩ : syracuseStep 3011567 = 4517351) B4517351
theorem B2007711 : Blo 2007435 2007711 := bstep (se 1 (by rfl) ⟨1505783, by rfl⟩ : syracuseStep 2007711 = 3011567) B3011567
theorem B3011573 : Blo 2007435 3011573 := bbase (se 5 (by rfl) ⟨141167, by rfl⟩ : syracuseStep 3011573 = 282335) (by norm_num)
theorem B2007715 : Blo 2007435 2007715 := bstep (se 1 (by rfl) ⟨1505786, by rfl⟩ : syracuseStep 2007715 = 3011573) B3011573
theorem B4287973 : Blo 2007435 4287973 := bbase (se 4 (by rfl) ⟨401997, by rfl⟩ : syracuseStep 4287973 = 803995) (by norm_num)
theorem B5717297 : Blo 2007435 5717297 := bstep (se 2 (by rfl) ⟨2143986, by rfl⟩ : syracuseStep 5717297 = 4287973) B4287973
theorem B3811531 : Blo 2007435 3811531 := bstep (se 1 (by rfl) ⟨2858648, by rfl⟩ : syracuseStep 3811531 = 5717297) B5717297
theorem B5082041 : Blo 2007435 5082041 := bstep (se 2 (by rfl) ⟨1905765, by rfl⟩ : syracuseStep 5082041 = 3811531) B3811531
theorem B3388027 : Blo 2007435 3388027 := bstep (se 1 (by rfl) ⟨2541020, by rfl⟩ : syracuseStep 3388027 = 5082041) B5082041
theorem B4517369 : Blo 2007435 4517369 := bstep (se 2 (by rfl) ⟨1694013, by rfl⟩ : syracuseStep 4517369 = 3388027) B3388027
theorem B3011579 : Blo 2007435 3011579 := bstep (se 1 (by rfl) ⟨2258684, by rfl⟩ : syracuseStep 3011579 = 4517369) B4517369
theorem B2007719 : Blo 2007435 2007719 := bstep (se 1 (by rfl) ⟨1505789, by rfl⟩ : syracuseStep 2007719 = 3011579) B3011579
theorem B2258689 : Blo 2007435 2258689 := bbase (se 2 (by rfl) ⟨847008, by rfl⟩ : syracuseStep 2258689 = 1694017) (by norm_num)
theorem B3011585 : Blo 2007435 3011585 := bstep (se 2 (by rfl) ⟨1129344, by rfl⟩ : syracuseStep 3011585 = 2258689) B2258689
theorem B2007723 : Blo 2007435 2007723 := bstep (se 1 (by rfl) ⟨1505792, by rfl⟩ : syracuseStep 2007723 = 3011585) B3011585
theorem B5082061 : Blo 2007435 5082061 := bbase (se 3 (by rfl) ⟨952886, by rfl⟩ : syracuseStep 5082061 = 1905773) (by norm_num)
theorem B6776081 : Blo 2007435 6776081 := bstep (se 2 (by rfl) ⟨2541030, by rfl⟩ : syracuseStep 6776081 = 5082061) B5082061
theorem B4517387 : Blo 2007435 4517387 := bstep (se 1 (by rfl) ⟨3388040, by rfl⟩ : syracuseStep 4517387 = 6776081) B6776081
theorem B3011591 : Blo 2007435 3011591 := bstep (se 1 (by rfl) ⟨2258693, by rfl⟩ : syracuseStep 3011591 = 4517387) B4517387
theorem B2007727 : Blo 2007435 2007727 := bstep (se 1 (by rfl) ⟨1505795, by rfl⟩ : syracuseStep 2007727 = 3011591) B3011591
theorem B3011597 : Blo 2007435 3011597 := bbase (se 3 (by rfl) ⟨564674, by rfl⟩ : syracuseStep 3011597 = 1129349) (by norm_num)
theorem B2007731 : Blo 2007435 2007731 := bstep (se 1 (by rfl) ⟨1505798, by rfl⟩ : syracuseStep 2007731 = 3011597) B3011597
theorem B4517405 : Blo 2007435 4517405 := bbase (se 3 (by rfl) ⟨847013, by rfl⟩ : syracuseStep 4517405 = 1694027) (by norm_num)
theorem B3011603 : Blo 2007435 3011603 := bstep (se 1 (by rfl) ⟨2258702, by rfl⟩ : syracuseStep 3011603 = 4517405) B4517405
theorem B2007735 : Blo 2007435 2007735 := bstep (se 1 (by rfl) ⟨1505801, by rfl⟩ : syracuseStep 2007735 = 3011603) B3011603
theorem B3388061 : Blo 2007435 3388061 := bbase (se 3 (by rfl) ⟨635261, by rfl⟩ : syracuseStep 3388061 = 1270523) (by norm_num)
theorem B2258707 : Blo 2007435 2258707 := bstep (se 1 (by rfl) ⟨1694030, by rfl⟩ : syracuseStep 2258707 = 3388061) B3388061
theorem B3011609 : Blo 2007435 3011609 := bstep (se 2 (by rfl) ⟨1129353, by rfl⟩ : syracuseStep 3011609 = 2258707) B2258707
theorem B2007739 : Blo 2007435 2007739 := bstep (se 1 (by rfl) ⟨1505804, by rfl⟩ : syracuseStep 2007739 = 3011609) B3011609
theorem B3434293 : Blo 2007435 3434293 := bbase (se 5 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 3434293 = 321965) (by norm_num)
theorem B4579057 : Blo 2007435 4579057 := bstep (se 2 (by rfl) ⟨1717146, by rfl⟩ : syracuseStep 4579057 = 3434293) B3434293
theorem B24421637 : Blo 2007435 24421637 := bstep (se 4 (by rfl) ⟨2289528, by rfl⟩ : syracuseStep 24421637 = 4579057) B4579057
theorem B16281091 : Blo 2007435 16281091 := bstep (se 1 (by rfl) ⟨12210818, by rfl⟩ : syracuseStep 16281091 = 24421637) B24421637
theorem B21708121 : Blo 2007435 21708121 := bstep (se 2 (by rfl) ⟨8140545, by rfl⟩ : syracuseStep 21708121 = 16281091) B16281091
theorem B28944161 : Blo 2007435 28944161 := bstep (se 2 (by rfl) ⟨10854060, by rfl⟩ : syracuseStep 28944161 = 21708121) B21708121
theorem B19296107 : Blo 2007435 19296107 := bstep (se 1 (by rfl) ⟨14472080, by rfl⟩ : syracuseStep 19296107 = 28944161) B28944161
theorem B12864071 : Blo 2007435 12864071 := bstep (se 1 (by rfl) ⟨9648053, by rfl⟩ : syracuseStep 12864071 = 19296107) B19296107
theorem B8576047 : Blo 2007435 8576047 := bstep (se 1 (by rfl) ⟨6432035, by rfl⟩ : syracuseStep 8576047 = 12864071) B12864071
theorem B11434729 : Blo 2007435 11434729 := bstep (se 2 (by rfl) ⟨4288023, by rfl⟩ : syracuseStep 11434729 = 8576047) B8576047
theorem B15246305 : Blo 2007435 15246305 := bstep (se 2 (by rfl) ⟨5717364, by rfl⟩ : syracuseStep 15246305 = 11434729) B11434729
theorem B10164203 : Blo 2007435 10164203 := bstep (se 1 (by rfl) ⟨7623152, by rfl⟩ : syracuseStep 10164203 = 15246305) B15246305
theorem B6776135 : Blo 2007435 6776135 := bstep (se 1 (by rfl) ⟨5082101, by rfl⟩ : syracuseStep 6776135 = 10164203) B10164203
theorem B4517423 : Blo 2007435 4517423 := bstep (se 1 (by rfl) ⟨3388067, by rfl⟩ : syracuseStep 4517423 = 6776135) B6776135
theorem B3011615 : Blo 2007435 3011615 := bstep (se 1 (by rfl) ⟨2258711, by rfl⟩ : syracuseStep 3011615 = 4517423) B4517423
theorem B2007743 : Blo 2007435 2007743 := bstep (se 1 (by rfl) ⟨1505807, by rfl⟩ : syracuseStep 2007743 = 3011615) B3011615
theorem B3011621 : Blo 2007435 3011621 := bbase (se 4 (by rfl) ⟨282339, by rfl⟩ : syracuseStep 3011621 = 564679) (by norm_num)
theorem B2007747 : Blo 2007435 2007747 := bstep (se 1 (by rfl) ⟨1505810, by rfl⟩ : syracuseStep 2007747 = 3011621) B3011621
theorem B2541061 : Blo 2007435 2541061 := bbase (se 4 (by rfl) ⟨238224, by rfl⟩ : syracuseStep 2541061 = 476449) (by norm_num)
theorem B3388081 : Blo 2007435 3388081 := bstep (se 2 (by rfl) ⟨1270530, by rfl⟩ : syracuseStep 3388081 = 2541061) B2541061
theorem B4517441 : Blo 2007435 4517441 := bstep (se 2 (by rfl) ⟨1694040, by rfl⟩ : syracuseStep 4517441 = 3388081) B3388081
theorem B3011627 : Blo 2007435 3011627 := bstep (se 1 (by rfl) ⟨2258720, by rfl⟩ : syracuseStep 3011627 = 4517441) B4517441
theorem B2007751 : Blo 2007435 2007751 := bstep (se 1 (by rfl) ⟨1505813, by rfl⟩ : syracuseStep 2007751 = 3011627) B3011627
theorem B2258725 : Blo 2007435 2258725 := bbase (se 4 (by rfl) ⟨211755, by rfl⟩ : syracuseStep 2258725 = 423511) (by norm_num)
theorem B3011633 : Blo 2007435 3011633 := bstep (se 2 (by rfl) ⟨1129362, by rfl⟩ : syracuseStep 3011633 = 2258725) B2258725
theorem B2007755 : Blo 2007435 2007755 := bstep (se 1 (by rfl) ⟨1505816, by rfl⟩ : syracuseStep 2007755 = 3011633) B3011633
theorem B8576117 : Blo 2007435 8576117 := bbase (se 5 (by rfl) ⟨402005, by rfl⟩ : syracuseStep 8576117 = 804011) (by norm_num)
theorem B5717411 : Blo 2007435 5717411 := bstep (se 1 (by rfl) ⟨4288058, by rfl⟩ : syracuseStep 5717411 = 8576117) B8576117
theorem B3811607 : Blo 2007435 3811607 := bstep (se 1 (by rfl) ⟨2858705, by rfl⟩ : syracuseStep 3811607 = 5717411) B5717411
theorem B2541071 : Blo 2007435 2541071 := bstep (se 1 (by rfl) ⟨1905803, by rfl⟩ : syracuseStep 2541071 = 3811607) B3811607
theorem B6776189 : Blo 2007435 6776189 := bstep (se 3 (by rfl) ⟨1270535, by rfl⟩ : syracuseStep 6776189 = 2541071) B2541071
theorem B4517459 : Blo 2007435 4517459 := bstep (se 1 (by rfl) ⟨3388094, by rfl⟩ : syracuseStep 4517459 = 6776189) B6776189
theorem B3011639 : Blo 2007435 3011639 := bstep (se 1 (by rfl) ⟨2258729, by rfl⟩ : syracuseStep 3011639 = 4517459) B4517459
theorem B2007759 : Blo 2007435 2007759 := bstep (se 1 (by rfl) ⟨1505819, by rfl⟩ : syracuseStep 2007759 = 3011639) B3011639
theorem B3011645 : Blo 2007435 3011645 := bbase (se 3 (by rfl) ⟨564683, by rfl⟩ : syracuseStep 3011645 = 1129367) (by norm_num)
theorem B2007763 : Blo 2007435 2007763 := bstep (se 1 (by rfl) ⟨1505822, by rfl⟩ : syracuseStep 2007763 = 3011645) B3011645
theorem B4517477 : Blo 2007435 4517477 := bbase (se 4 (by rfl) ⟨423513, by rfl⟩ : syracuseStep 4517477 = 847027) (by norm_num)
theorem B3011651 : Blo 2007435 3011651 := bstep (se 1 (by rfl) ⟨2258738, by rfl⟩ : syracuseStep 3011651 = 4517477) B4517477
theorem B2007767 : Blo 2007435 2007767 := bstep (se 1 (by rfl) ⟨1505825, by rfl⟩ : syracuseStep 2007767 = 3011651) B3011651
theorem B5082173 : Blo 2007435 5082173 := bbase (se 3 (by rfl) ⟨952907, by rfl⟩ : syracuseStep 5082173 = 1905815) (by norm_num)
theorem B3388115 : Blo 2007435 3388115 := bstep (se 1 (by rfl) ⟨2541086, by rfl⟩ : syracuseStep 3388115 = 5082173) B5082173
theorem B2258743 : Blo 2007435 2258743 := bstep (se 1 (by rfl) ⟨1694057, by rfl⟩ : syracuseStep 2258743 = 3388115) B3388115
theorem B3011657 : Blo 2007435 3011657 := bstep (se 2 (by rfl) ⟨1129371, by rfl⟩ : syracuseStep 3011657 = 2258743) B2258743
theorem B2007771 : Blo 2007435 2007771 := bstep (se 1 (by rfl) ⟨1505828, by rfl⟩ : syracuseStep 2007771 = 3011657) B3011657
theorem B3811637 : Blo 2007435 3811637 := bbase (se 5 (by rfl) ⟨178670, by rfl⟩ : syracuseStep 3811637 = 357341) (by norm_num)
theorem B10164365 : Blo 2007435 10164365 := bstep (se 3 (by rfl) ⟨1905818, by rfl⟩ : syracuseStep 10164365 = 3811637) B3811637
theorem B6776243 : Blo 2007435 6776243 := bstep (se 1 (by rfl) ⟨5082182, by rfl⟩ : syracuseStep 6776243 = 10164365) B10164365
theorem B4517495 : Blo 2007435 4517495 := bstep (se 1 (by rfl) ⟨3388121, by rfl⟩ : syracuseStep 4517495 = 6776243) B6776243
theorem B3011663 : Blo 2007435 3011663 := bstep (se 1 (by rfl) ⟨2258747, by rfl⟩ : syracuseStep 3011663 = 4517495) B4517495
theorem B2007775 : Blo 2007435 2007775 := bstep (se 1 (by rfl) ⟨1505831, by rfl⟩ : syracuseStep 2007775 = 3011663) B3011663
theorem B3011669 : Blo 2007435 3011669 := bbase (se 8 (by rfl) ⟨17646, by rfl⟩ : syracuseStep 3011669 = 35293) (by norm_num)
theorem B2007779 : Blo 2007435 2007779 := bstep (se 1 (by rfl) ⟨1505834, by rfl⟩ : syracuseStep 2007779 = 3011669) B3011669
theorem B8140709 : Blo 2007435 8140709 := bbase (se 4 (by rfl) ⟨763191, by rfl⟩ : syracuseStep 8140709 = 1526383) (by norm_num)
theorem B21708557 : Blo 2007435 21708557 := bstep (se 3 (by rfl) ⟨4070354, by rfl⟩ : syracuseStep 21708557 = 8140709) B8140709
theorem B14472371 : Blo 2007435 14472371 := bstep (se 1 (by rfl) ⟨10854278, by rfl⟩ : syracuseStep 14472371 = 21708557) B21708557
theorem B9648247 : Blo 2007435 9648247 := bstep (se 1 (by rfl) ⟨7236185, by rfl⟩ : syracuseStep 9648247 = 14472371) B14472371
theorem B12864329 : Blo 2007435 12864329 := bstep (se 2 (by rfl) ⟨4824123, by rfl⟩ : syracuseStep 12864329 = 9648247) B9648247
theorem B8576219 : Blo 2007435 8576219 := bstep (se 1 (by rfl) ⟨6432164, by rfl⟩ : syracuseStep 8576219 = 12864329) B12864329
theorem B5717479 : Blo 2007435 5717479 := bstep (se 1 (by rfl) ⟨4288109, by rfl⟩ : syracuseStep 5717479 = 8576219) B8576219
theorem B7623305 : Blo 2007435 7623305 := bstep (se 2 (by rfl) ⟨2858739, by rfl⟩ : syracuseStep 7623305 = 5717479) B5717479
theorem B5082203 : Blo 2007435 5082203 := bstep (se 1 (by rfl) ⟨3811652, by rfl⟩ : syracuseStep 5082203 = 7623305) B7623305
theorem B3388135 : Blo 2007435 3388135 := bstep (se 1 (by rfl) ⟨2541101, by rfl⟩ : syracuseStep 3388135 = 5082203) B5082203
theorem B4517513 : Blo 2007435 4517513 := bstep (se 2 (by rfl) ⟨1694067, by rfl⟩ : syracuseStep 4517513 = 3388135) B3388135
theorem B3011675 : Blo 2007435 3011675 := bstep (se 1 (by rfl) ⟨2258756, by rfl⟩ : syracuseStep 3011675 = 4517513) B4517513
theorem B2007783 : Blo 2007435 2007783 := bstep (se 1 (by rfl) ⟨1505837, by rfl⟩ : syracuseStep 2007783 = 3011675) B3011675
theorem B2258761 : Blo 2007435 2258761 := bbase (se 2 (by rfl) ⟨847035, by rfl⟩ : syracuseStep 2258761 = 1694071) (by norm_num)
theorem B3011681 : Blo 2007435 3011681 := bstep (se 2 (by rfl) ⟨1129380, by rfl⟩ : syracuseStep 3011681 = 2258761) B2258761
theorem B2007787 : Blo 2007435 2007787 := bstep (se 1 (by rfl) ⟨1505840, by rfl⟩ : syracuseStep 2007787 = 3011681) B3011681
theorem B3094429 : Blo 2007435 3094429 := bbase (se 3 (by rfl) ⟨580205, by rfl⟩ : syracuseStep 3094429 = 1160411) (by norm_num)
theorem B4125905 : Blo 2007435 4125905 := bstep (se 2 (by rfl) ⟨1547214, by rfl⟩ : syracuseStep 4125905 = 3094429) B3094429
theorem B2750603 : Blo 2007435 2750603 := bstep (se 1 (by rfl) ⟨2062952, by rfl⟩ : syracuseStep 2750603 = 4125905) B4125905
theorem B7334941 : Blo 2007435 7334941 := bstep (se 3 (by rfl) ⟨1375301, by rfl⟩ : syracuseStep 7334941 = 2750603) B2750603
theorem B9779921 : Blo 2007435 9779921 := bstep (se 2 (by rfl) ⟨3667470, by rfl⟩ : syracuseStep 9779921 = 7334941) B7334941
theorem B6519947 : Blo 2007435 6519947 := bstep (se 1 (by rfl) ⟨4889960, by rfl⟩ : syracuseStep 6519947 = 9779921) B9779921
theorem B17386525 : Blo 2007435 17386525 := bstep (se 3 (by rfl) ⟨3259973, by rfl⟩ : syracuseStep 17386525 = 6519947) B6519947
theorem B23182033 : Blo 2007435 23182033 := bstep (se 2 (by rfl) ⟨8693262, by rfl⟩ : syracuseStep 23182033 = 17386525) B17386525
theorem B30909377 : Blo 2007435 30909377 := bstep (se 2 (by rfl) ⟨11591016, by rfl⟩ : syracuseStep 30909377 = 23182033) B23182033
theorem B20606251 : Blo 2007435 20606251 := bstep (se 1 (by rfl) ⟨15454688, by rfl⟩ : syracuseStep 20606251 = 30909377) B30909377
theorem B27475001 : Blo 2007435 27475001 := bstep (se 2 (by rfl) ⟨10303125, by rfl⟩ : syracuseStep 27475001 = 20606251) B20606251
theorem B18316667 : Blo 2007435 18316667 := bstep (se 1 (by rfl) ⟨13737500, by rfl⟩ : syracuseStep 18316667 = 27475001) B27475001
theorem B12211111 : Blo 2007435 12211111 := bstep (se 1 (by rfl) ⟨9158333, by rfl⟩ : syracuseStep 12211111 = 18316667) B18316667
theorem B16281481 : Blo 2007435 16281481 := bstep (se 2 (by rfl) ⟨6105555, by rfl⟩ : syracuseStep 16281481 = 12211111) B12211111
theorem B21708641 : Blo 2007435 21708641 := bstep (se 2 (by rfl) ⟨8140740, by rfl⟩ : syracuseStep 21708641 = 16281481) B16281481
theorem B14472427 : Blo 2007435 14472427 := bstep (se 1 (by rfl) ⟨10854320, by rfl⟩ : syracuseStep 14472427 = 21708641) B21708641
theorem B19296569 : Blo 2007435 19296569 := bstep (se 2 (by rfl) ⟨7236213, by rfl⟩ : syracuseStep 19296569 = 14472427) B14472427
theorem B12864379 : Blo 2007435 12864379 := bstep (se 1 (by rfl) ⟨9648284, by rfl⟩ : syracuseStep 12864379 = 19296569) B19296569
theorem B17152505 : Blo 2007435 17152505 := bstep (se 2 (by rfl) ⟨6432189, by rfl⟩ : syracuseStep 17152505 = 12864379) B12864379
theorem B11435003 : Blo 2007435 11435003 := bstep (se 1 (by rfl) ⟨8576252, by rfl⟩ : syracuseStep 11435003 = 17152505) B17152505
theorem B7623335 : Blo 2007435 7623335 := bstep (se 1 (by rfl) ⟨5717501, by rfl⟩ : syracuseStep 7623335 = 11435003) B11435003
theorem B5082223 : Blo 2007435 5082223 := bstep (se 1 (by rfl) ⟨3811667, by rfl⟩ : syracuseStep 5082223 = 7623335) B7623335
theorem B6776297 : Blo 2007435 6776297 := bstep (se 2 (by rfl) ⟨2541111, by rfl⟩ : syracuseStep 6776297 = 5082223) B5082223
theorem B4517531 : Blo 2007435 4517531 := bstep (se 1 (by rfl) ⟨3388148, by rfl⟩ : syracuseStep 4517531 = 6776297) B6776297
theorem B3011687 : Blo 2007435 3011687 := bstep (se 1 (by rfl) ⟨2258765, by rfl⟩ : syracuseStep 3011687 = 4517531) B4517531
theorem B2007791 : Blo 2007435 2007791 := bstep (se 1 (by rfl) ⟨1505843, by rfl⟩ : syracuseStep 2007791 = 3011687) B3011687
theorem B3011693 : Blo 2007435 3011693 := bbase (se 3 (by rfl) ⟨564692, by rfl⟩ : syracuseStep 3011693 = 1129385) (by norm_num)
theorem B2007795 : Blo 2007435 2007795 := bstep (se 1 (by rfl) ⟨1505846, by rfl⟩ : syracuseStep 2007795 = 3011693) B3011693
theorem B4517549 : Blo 2007435 4517549 := bbase (se 3 (by rfl) ⟨847040, by rfl⟩ : syracuseStep 4517549 = 1694081) (by norm_num)
theorem B3011699 : Blo 2007435 3011699 := bstep (se 1 (by rfl) ⟨2258774, by rfl⟩ : syracuseStep 3011699 = 4517549) B4517549
theorem B2007799 : Blo 2007435 2007799 := bstep (se 1 (by rfl) ⟨1505849, by rfl⟩ : syracuseStep 2007799 = 3011699) B3011699
theorem B4824173 : Blo 2007435 4824173 := bbase (se 3 (by rfl) ⟨904532, by rfl⟩ : syracuseStep 4824173 = 1809065) (by norm_num)
theorem B3216115 : Blo 2007435 3216115 := bstep (se 1 (by rfl) ⟨2412086, by rfl⟩ : syracuseStep 3216115 = 4824173) B4824173
theorem B4288153 : Blo 2007435 4288153 := bstep (se 2 (by rfl) ⟨1608057, by rfl⟩ : syracuseStep 4288153 = 3216115) B3216115
theorem B5717537 : Blo 2007435 5717537 := bstep (se 2 (by rfl) ⟨2144076, by rfl⟩ : syracuseStep 5717537 = 4288153) B4288153
theorem B3811691 : Blo 2007435 3811691 := bstep (se 1 (by rfl) ⟨2858768, by rfl⟩ : syracuseStep 3811691 = 5717537) B5717537
theorem B2541127 : Blo 2007435 2541127 := bstep (se 1 (by rfl) ⟨1905845, by rfl⟩ : syracuseStep 2541127 = 3811691) B3811691
theorem B3388169 : Blo 2007435 3388169 := bstep (se 2 (by rfl) ⟨1270563, by rfl⟩ : syracuseStep 3388169 = 2541127) B2541127
theorem B2258779 : Blo 2007435 2258779 := bstep (se 1 (by rfl) ⟨1694084, by rfl⟩ : syracuseStep 2258779 = 3388169) B3388169
theorem B3011705 : Blo 2007435 3011705 := bstep (se 2 (by rfl) ⟨1129389, by rfl⟩ : syracuseStep 3011705 = 2258779) B2258779
theorem B2007803 : Blo 2007435 2007803 := bstep (se 1 (by rfl) ⟨1505852, by rfl⟩ : syracuseStep 2007803 = 3011705) B3011705
theorem B8140805 : Blo 2007435 8140805 := bbase (se 4 (by rfl) ⟨763200, by rfl⟩ : syracuseStep 8140805 = 1526401) (by norm_num)
theorem B5427203 : Blo 2007435 5427203 := bstep (se 1 (by rfl) ⟨4070402, by rfl⟩ : syracuseStep 5427203 = 8140805) B8140805
theorem B14472541 : Blo 2007435 14472541 := bstep (se 3 (by rfl) ⟨2713601, by rfl⟩ : syracuseStep 14472541 = 5427203) B5427203
theorem B19296721 : Blo 2007435 19296721 := bstep (se 2 (by rfl) ⟨7236270, by rfl⟩ : syracuseStep 19296721 = 14472541) B14472541
theorem B25728961 : Blo 2007435 25728961 := bstep (se 2 (by rfl) ⟨9648360, by rfl⟩ : syracuseStep 25728961 = 19296721) B19296721
theorem B34305281 : Blo 2007435 34305281 := bstep (se 2 (by rfl) ⟨12864480, by rfl⟩ : syracuseStep 34305281 = 25728961) B25728961
theorem B22870187 : Blo 2007435 22870187 := bstep (se 1 (by rfl) ⟨17152640, by rfl⟩ : syracuseStep 22870187 = 34305281) B34305281
theorem B15246791 : Blo 2007435 15246791 := bstep (se 1 (by rfl) ⟨11435093, by rfl⟩ : syracuseStep 15246791 = 22870187) B22870187
theorem B10164527 : Blo 2007435 10164527 := bstep (se 1 (by rfl) ⟨7623395, by rfl⟩ : syracuseStep 10164527 = 15246791) B15246791
theorem B6776351 : Blo 2007435 6776351 := bstep (se 1 (by rfl) ⟨5082263, by rfl⟩ : syracuseStep 6776351 = 10164527) B10164527
theorem B4517567 : Blo 2007435 4517567 := bstep (se 1 (by rfl) ⟨3388175, by rfl⟩ : syracuseStep 4517567 = 6776351) B6776351
theorem B3011711 : Blo 2007435 3011711 := bstep (se 1 (by rfl) ⟨2258783, by rfl⟩ : syracuseStep 3011711 = 4517567) B4517567
theorem B2007807 : Blo 2007435 2007807 := bstep (se 1 (by rfl) ⟨1505855, by rfl⟩ : syracuseStep 2007807 = 3011711) B3011711
theorem B3011717 : Blo 2007435 3011717 := bbase (se 4 (by rfl) ⟨282348, by rfl⟩ : syracuseStep 3011717 = 564697) (by norm_num)
theorem B2007811 : Blo 2007435 2007811 := bstep (se 1 (by rfl) ⟨1505858, by rfl⟩ : syracuseStep 2007811 = 3011717) B3011717
theorem B3388189 : Blo 2007435 3388189 := bbase (se 3 (by rfl) ⟨635285, by rfl⟩ : syracuseStep 3388189 = 1270571) (by norm_num)
theorem B4517585 : Blo 2007435 4517585 := bstep (se 2 (by rfl) ⟨1694094, by rfl⟩ : syracuseStep 4517585 = 3388189) B3388189
theorem B3011723 : Blo 2007435 3011723 := bstep (se 1 (by rfl) ⟨2258792, by rfl⟩ : syracuseStep 3011723 = 4517585) B4517585
theorem B2007815 : Blo 2007435 2007815 := bstep (se 1 (by rfl) ⟨1505861, by rfl⟩ : syracuseStep 2007815 = 3011723) B3011723
theorem B2258797 : Blo 2007435 2258797 := bbase (se 3 (by rfl) ⟨423524, by rfl⟩ : syracuseStep 2258797 = 847049) (by norm_num)
theorem B3011729 : Blo 2007435 3011729 := bstep (se 2 (by rfl) ⟨1129398, by rfl⟩ : syracuseStep 3011729 = 2258797) B2258797
theorem B2007819 : Blo 2007435 2007819 := bstep (se 1 (by rfl) ⟨1505864, by rfl⟩ : syracuseStep 2007819 = 3011729) B3011729
theorem B6776405 : Blo 2007435 6776405 := bbase (se 8 (by rfl) ⟨39705, by rfl⟩ : syracuseStep 6776405 = 79411) (by norm_num)
theorem B4517603 : Blo 2007435 4517603 := bstep (se 1 (by rfl) ⟨3388202, by rfl⟩ : syracuseStep 4517603 = 6776405) B6776405
theorem B3011735 : Blo 2007435 3011735 := bstep (se 1 (by rfl) ⟨2258801, by rfl⟩ : syracuseStep 3011735 = 4517603) B4517603
theorem B2007823 : Blo 2007435 2007823 := bstep (se 1 (by rfl) ⟨1505867, by rfl⟩ : syracuseStep 2007823 = 3011735) B3011735
theorem B3011741 : Blo 2007435 3011741 := bbase (se 3 (by rfl) ⟨564701, by rfl⟩ : syracuseStep 3011741 = 1129403) (by norm_num)
theorem B2007827 : Blo 2007435 2007827 := bstep (se 1 (by rfl) ⟨1505870, by rfl⟩ : syracuseStep 2007827 = 3011741) B3011741
theorem B4517621 : Blo 2007435 4517621 := bbase (se 5 (by rfl) ⟨211763, by rfl⟩ : syracuseStep 4517621 = 423527) (by norm_num)
theorem B3011747 : Blo 2007435 3011747 := bstep (se 1 (by rfl) ⟨2258810, by rfl⟩ : syracuseStep 3011747 = 4517621) B4517621
theorem B2007831 : Blo 2007435 2007831 := bstep (se 1 (by rfl) ⟨1505873, by rfl⟩ : syracuseStep 2007831 = 3011747) B3011747
theorem B7236373 : Blo 2007435 7236373 := bbase (se 6 (by rfl) ⟨169602, by rfl⟩ : syracuseStep 7236373 = 339205) (by norm_num)
theorem B9648497 : Blo 2007435 9648497 := bstep (se 2 (by rfl) ⟨3618186, by rfl⟩ : syracuseStep 9648497 = 7236373) B7236373
theorem B25729325 : Blo 2007435 25729325 := bstep (se 3 (by rfl) ⟨4824248, by rfl⟩ : syracuseStep 25729325 = 9648497) B9648497
theorem B17152883 : Blo 2007435 17152883 := bstep (se 1 (by rfl) ⟨12864662, by rfl⟩ : syracuseStep 17152883 = 25729325) B25729325
theorem B11435255 : Blo 2007435 11435255 := bstep (se 1 (by rfl) ⟨8576441, by rfl⟩ : syracuseStep 11435255 = 17152883) B17152883
theorem B7623503 : Blo 2007435 7623503 := bstep (se 1 (by rfl) ⟨5717627, by rfl⟩ : syracuseStep 7623503 = 11435255) B11435255
theorem B5082335 : Blo 2007435 5082335 := bstep (se 1 (by rfl) ⟨3811751, by rfl⟩ : syracuseStep 5082335 = 7623503) B7623503
theorem B3388223 : Blo 2007435 3388223 := bstep (se 1 (by rfl) ⟨2541167, by rfl⟩ : syracuseStep 3388223 = 5082335) B5082335
theorem B2258815 : Blo 2007435 2258815 := bstep (se 1 (by rfl) ⟨1694111, by rfl⟩ : syracuseStep 2258815 = 3388223) B3388223
theorem B3011753 : Blo 2007435 3011753 := bstep (se 2 (by rfl) ⟨1129407, by rfl⟩ : syracuseStep 3011753 = 2258815) B2258815
theorem B2007835 : Blo 2007435 2007835 := bstep (se 1 (by rfl) ⟨1505876, by rfl⟩ : syracuseStep 2007835 = 3011753) B3011753
theorem B4288229 : Blo 2007435 4288229 := bbase (se 4 (by rfl) ⟨402021, by rfl⟩ : syracuseStep 4288229 = 804043) (by norm_num)
theorem B2858819 : Blo 2007435 2858819 := bstep (se 1 (by rfl) ⟨2144114, by rfl⟩ : syracuseStep 2858819 = 4288229) B4288229
theorem B7623517 : Blo 2007435 7623517 := bstep (se 3 (by rfl) ⟨1429409, by rfl⟩ : syracuseStep 7623517 = 2858819) B2858819
theorem B10164689 : Blo 2007435 10164689 := bstep (se 2 (by rfl) ⟨3811758, by rfl⟩ : syracuseStep 10164689 = 7623517) B7623517
theorem B6776459 : Blo 2007435 6776459 := bstep (se 1 (by rfl) ⟨5082344, by rfl⟩ : syracuseStep 6776459 = 10164689) B10164689
theorem B4517639 : Blo 2007435 4517639 := bstep (se 1 (by rfl) ⟨3388229, by rfl⟩ : syracuseStep 4517639 = 6776459) B6776459
theorem B3011759 : Blo 2007435 3011759 := bstep (se 1 (by rfl) ⟨2258819, by rfl⟩ : syracuseStep 3011759 = 4517639) B4517639
theorem B2007839 : Blo 2007435 2007839 := bstep (se 1 (by rfl) ⟨1505879, by rfl⟩ : syracuseStep 2007839 = 3011759) B3011759
theorem B3011765 : Blo 2007435 3011765 := bbase (se 5 (by rfl) ⟨141176, by rfl⟩ : syracuseStep 3011765 = 282353) (by norm_num)
theorem B2007843 : Blo 2007435 2007843 := bstep (se 1 (by rfl) ⟨1505882, by rfl⟩ : syracuseStep 2007843 = 3011765) B3011765
theorem B5082365 : Blo 2007435 5082365 := bbase (se 3 (by rfl) ⟨952943, by rfl⟩ : syracuseStep 5082365 = 1905887) (by norm_num)
theorem B3388243 : Blo 2007435 3388243 := bstep (se 1 (by rfl) ⟨2541182, by rfl⟩ : syracuseStep 3388243 = 5082365) B5082365
theorem B4517657 : Blo 2007435 4517657 := bstep (se 2 (by rfl) ⟨1694121, by rfl⟩ : syracuseStep 4517657 = 3388243) B3388243
theorem B3011771 : Blo 2007435 3011771 := bstep (se 1 (by rfl) ⟨2258828, by rfl⟩ : syracuseStep 3011771 = 4517657) B4517657
theorem B2007847 : Blo 2007435 2007847 := bstep (se 1 (by rfl) ⟨1505885, by rfl⟩ : syracuseStep 2007847 = 3011771) B3011771
theorem B2258833 : Blo 2007435 2258833 := bbase (se 2 (by rfl) ⟨847062, by rfl⟩ : syracuseStep 2258833 = 1694125) (by norm_num)
theorem B3011777 : Blo 2007435 3011777 := bstep (se 2 (by rfl) ⟨1129416, by rfl⟩ : syracuseStep 3011777 = 2258833) B2258833
theorem B2007851 : Blo 2007435 2007851 := bstep (se 1 (by rfl) ⟨1505888, by rfl⟩ : syracuseStep 2007851 = 3011777) B3011777
theorem B3811789 : Blo 2007435 3811789 := bbase (se 3 (by rfl) ⟨714710, by rfl⟩ : syracuseStep 3811789 = 1429421) (by norm_num)
theorem B5082385 : Blo 2007435 5082385 := bstep (se 2 (by rfl) ⟨1905894, by rfl⟩ : syracuseStep 5082385 = 3811789) B3811789
theorem B6776513 : Blo 2007435 6776513 := bstep (se 2 (by rfl) ⟨2541192, by rfl⟩ : syracuseStep 6776513 = 5082385) B5082385
theorem B4517675 : Blo 2007435 4517675 := bstep (se 1 (by rfl) ⟨3388256, by rfl⟩ : syracuseStep 4517675 = 6776513) B6776513
theorem B3011783 : Blo 2007435 3011783 := bstep (se 1 (by rfl) ⟨2258837, by rfl⟩ : syracuseStep 3011783 = 4517675) B4517675
theorem B2007855 : Blo 2007435 2007855 := bstep (se 1 (by rfl) ⟨1505891, by rfl⟩ : syracuseStep 2007855 = 3011783) B3011783
theorem B3011789 : Blo 2007435 3011789 := bbase (se 3 (by rfl) ⟨564710, by rfl⟩ : syracuseStep 3011789 = 1129421) (by norm_num)
theorem B2007859 : Blo 2007435 2007859 := bstep (se 1 (by rfl) ⟨1505894, by rfl⟩ : syracuseStep 2007859 = 3011789) B3011789
theorem B4517693 : Blo 2007435 4517693 := bbase (se 3 (by rfl) ⟨847067, by rfl⟩ : syracuseStep 4517693 = 1694135) (by norm_num)
theorem B3011795 : Blo 2007435 3011795 := bstep (se 1 (by rfl) ⟨2258846, by rfl⟩ : syracuseStep 3011795 = 4517693) B4517693
theorem B2007863 : Blo 2007435 2007863 := bstep (se 1 (by rfl) ⟨1505897, by rfl⟩ : syracuseStep 2007863 = 3011795) B3011795
theorem B3388277 : Blo 2007435 3388277 := bbase (se 5 (by rfl) ⟨158825, by rfl⟩ : syracuseStep 3388277 = 317651) (by norm_num)
theorem B2258851 : Blo 2007435 2258851 := bstep (se 1 (by rfl) ⟨1694138, by rfl⟩ : syracuseStep 2258851 = 3388277) B3388277
theorem B3011801 : Blo 2007435 3011801 := bstep (se 2 (by rfl) ⟨1129425, by rfl⟩ : syracuseStep 3011801 = 2258851) B2258851
theorem B2007867 : Blo 2007435 2007867 := bstep (se 1 (by rfl) ⟨1505900, by rfl⟩ : syracuseStep 2007867 = 3011801) B3011801
theorem B16282133 : Blo 2007435 16282133 := bbase (se 6 (by rfl) ⟨381612, by rfl⟩ : syracuseStep 16282133 = 763225) (by norm_num)
theorem B10854755 : Blo 2007435 10854755 := bstep (se 1 (by rfl) ⟨8141066, by rfl⟩ : syracuseStep 10854755 = 16282133) B16282133
theorem B7236503 : Blo 2007435 7236503 := bstep (se 1 (by rfl) ⟨5427377, by rfl⟩ : syracuseStep 7236503 = 10854755) B10854755
theorem B4824335 : Blo 2007435 4824335 := bstep (se 1 (by rfl) ⟨3618251, by rfl⟩ : syracuseStep 4824335 = 7236503) B7236503
theorem B3216223 : Blo 2007435 3216223 := bstep (se 1 (by rfl) ⟨2412167, by rfl⟩ : syracuseStep 3216223 = 4824335) B4824335
theorem B4288297 : Blo 2007435 4288297 := bstep (se 2 (by rfl) ⟨1608111, by rfl⟩ : syracuseStep 4288297 = 3216223) B3216223
theorem B5717729 : Blo 2007435 5717729 := bstep (se 2 (by rfl) ⟨2144148, by rfl⟩ : syracuseStep 5717729 = 4288297) B4288297
theorem B15247277 : Blo 2007435 15247277 := bstep (se 3 (by rfl) ⟨2858864, by rfl⟩ : syracuseStep 15247277 = 5717729) B5717729
theorem B10164851 : Blo 2007435 10164851 := bstep (se 1 (by rfl) ⟨7623638, by rfl⟩ : syracuseStep 10164851 = 15247277) B15247277
theorem B6776567 : Blo 2007435 6776567 := bstep (se 1 (by rfl) ⟨5082425, by rfl⟩ : syracuseStep 6776567 = 10164851) B10164851
theorem B4517711 : Blo 2007435 4517711 := bstep (se 1 (by rfl) ⟨3388283, by rfl⟩ : syracuseStep 4517711 = 6776567) B6776567
theorem B3011807 : Blo 2007435 3011807 := bstep (se 1 (by rfl) ⟨2258855, by rfl⟩ : syracuseStep 3011807 = 4517711) B4517711
theorem B2007871 : Blo 2007435 2007871 := bstep (se 1 (by rfl) ⟨1505903, by rfl⟩ : syracuseStep 2007871 = 3011807) B3011807
theorem B3011813 : Blo 2007435 3011813 := bbase (se 4 (by rfl) ⟨282357, by rfl⟩ : syracuseStep 3011813 = 564715) (by norm_num)
theorem B2007875 : Blo 2007435 2007875 := bstep (se 1 (by rfl) ⟨1505906, by rfl⟩ : syracuseStep 2007875 = 3011813) B3011813
theorem B7236533 : Blo 2007435 7236533 := bbase (se 5 (by rfl) ⟨339212, by rfl⟩ : syracuseStep 7236533 = 678425) (by norm_num)
theorem B4824355 : Blo 2007435 4824355 := bstep (se 1 (by rfl) ⟨3618266, by rfl⟩ : syracuseStep 4824355 = 7236533) B7236533
theorem B6432473 : Blo 2007435 6432473 := bstep (se 2 (by rfl) ⟨2412177, by rfl⟩ : syracuseStep 6432473 = 4824355) B4824355
theorem B4288315 : Blo 2007435 4288315 := bstep (se 1 (by rfl) ⟨3216236, by rfl⟩ : syracuseStep 4288315 = 6432473) B6432473
theorem B5717753 : Blo 2007435 5717753 := bstep (se 2 (by rfl) ⟨2144157, by rfl⟩ : syracuseStep 5717753 = 4288315) B4288315
theorem B3811835 : Blo 2007435 3811835 := bstep (se 1 (by rfl) ⟨2858876, by rfl⟩ : syracuseStep 3811835 = 5717753) B5717753
theorem B2541223 : Blo 2007435 2541223 := bstep (se 1 (by rfl) ⟨1905917, by rfl⟩ : syracuseStep 2541223 = 3811835) B3811835
theorem B3388297 : Blo 2007435 3388297 := bstep (se 2 (by rfl) ⟨1270611, by rfl⟩ : syracuseStep 3388297 = 2541223) B2541223
theorem B4517729 : Blo 2007435 4517729 := bstep (se 2 (by rfl) ⟨1694148, by rfl⟩ : syracuseStep 4517729 = 3388297) B3388297
theorem B3011819 : Blo 2007435 3011819 := bstep (se 1 (by rfl) ⟨2258864, by rfl⟩ : syracuseStep 3011819 = 4517729) B4517729
theorem B2007879 : Blo 2007435 2007879 := bstep (se 1 (by rfl) ⟨1505909, by rfl⟩ : syracuseStep 2007879 = 3011819) B3011819
theorem B2258869 : Blo 2007435 2258869 := bbase (se 5 (by rfl) ⟨105884, by rfl⟩ : syracuseStep 2258869 = 211769) (by norm_num)
theorem B3011825 : Blo 2007435 3011825 := bstep (se 2 (by rfl) ⟨1129434, by rfl⟩ : syracuseStep 3011825 = 2258869) B2258869
theorem B2007883 : Blo 2007435 2007883 := bstep (se 1 (by rfl) ⟨1505912, by rfl⟩ : syracuseStep 2007883 = 3011825) B3011825
theorem B2541233 : Blo 2007435 2541233 := bbase (se 2 (by rfl) ⟨952962, by rfl⟩ : syracuseStep 2541233 = 1905925) (by norm_num)
theorem B6776621 : Blo 2007435 6776621 := bstep (se 3 (by rfl) ⟨1270616, by rfl⟩ : syracuseStep 6776621 = 2541233) B2541233
theorem B4517747 : Blo 2007435 4517747 := bstep (se 1 (by rfl) ⟨3388310, by rfl⟩ : syracuseStep 4517747 = 6776621) B6776621
theorem B3011831 : Blo 2007435 3011831 := bstep (se 1 (by rfl) ⟨2258873, by rfl⟩ : syracuseStep 3011831 = 4517747) B4517747
theorem B2007887 : Blo 2007435 2007887 := bstep (se 1 (by rfl) ⟨1505915, by rfl⟩ : syracuseStep 2007887 = 3011831) B3011831
theorem B3011837 : Blo 2007435 3011837 := bbase (se 3 (by rfl) ⟨564719, by rfl⟩ : syracuseStep 3011837 = 1129439) (by norm_num)
theorem B2007891 : Blo 2007435 2007891 := bstep (se 1 (by rfl) ⟨1505918, by rfl⟩ : syracuseStep 2007891 = 3011837) B3011837
theorem B4517765 : Blo 2007435 4517765 := bbase (se 4 (by rfl) ⟨423540, by rfl⟩ : syracuseStep 4517765 = 847081) (by norm_num)
theorem B3011843 : Blo 2007435 3011843 := bstep (se 1 (by rfl) ⟨2258882, by rfl⟩ : syracuseStep 3011843 = 4517765) B4517765
theorem B2007895 : Blo 2007435 2007895 := bstep (se 1 (by rfl) ⟨1505921, by rfl⟩ : syracuseStep 2007895 = 3011843) B3011843
theorem B3216269 : Blo 2007435 3216269 := bbase (se 3 (by rfl) ⟨603050, by rfl⟩ : syracuseStep 3216269 = 1206101) (by norm_num)
theorem B2144179 : Blo 2007435 2144179 := bstep (se 1 (by rfl) ⟨1608134, by rfl⟩ : syracuseStep 2144179 = 3216269) B3216269
theorem B2858905 : Blo 2007435 2858905 := bstep (se 2 (by rfl) ⟨1072089, by rfl⟩ : syracuseStep 2858905 = 2144179) B2144179
theorem B3811873 : Blo 2007435 3811873 := bstep (se 2 (by rfl) ⟨1429452, by rfl⟩ : syracuseStep 3811873 = 2858905) B2858905
theorem B5082497 : Blo 2007435 5082497 := bstep (se 2 (by rfl) ⟨1905936, by rfl⟩ : syracuseStep 5082497 = 3811873) B3811873
theorem B3388331 : Blo 2007435 3388331 := bstep (se 1 (by rfl) ⟨2541248, by rfl⟩ : syracuseStep 3388331 = 5082497) B5082497
theorem B2258887 : Blo 2007435 2258887 := bstep (se 1 (by rfl) ⟨1694165, by rfl⟩ : syracuseStep 2258887 = 3388331) B3388331
theorem B3011849 : Blo 2007435 3011849 := bstep (se 2 (by rfl) ⟨1129443, by rfl⟩ : syracuseStep 3011849 = 2258887) B2258887
theorem B2007899 : Blo 2007435 2007899 := bstep (se 1 (by rfl) ⟨1505924, by rfl⟩ : syracuseStep 2007899 = 3011849) B3011849
theorem B10165013 : Blo 2007435 10165013 := bbase (se 6 (by rfl) ⟨238242, by rfl⟩ : syracuseStep 10165013 = 476485) (by norm_num)
theorem B6776675 : Blo 2007435 6776675 := bstep (se 1 (by rfl) ⟨5082506, by rfl⟩ : syracuseStep 6776675 = 10165013) B10165013
theorem B4517783 : Blo 2007435 4517783 := bstep (se 1 (by rfl) ⟨3388337, by rfl⟩ : syracuseStep 4517783 = 6776675) B6776675
theorem B3011855 : Blo 2007435 3011855 := bstep (se 1 (by rfl) ⟨2258891, by rfl⟩ : syracuseStep 3011855 = 4517783) B4517783
theorem B2007903 : Blo 2007435 2007903 := bstep (se 1 (by rfl) ⟨1505927, by rfl⟩ : syracuseStep 2007903 = 3011855) B3011855
theorem B3011861 : Blo 2007435 3011861 := bbase (se 6 (by rfl) ⟨70590, by rfl⟩ : syracuseStep 3011861 = 141181) (by norm_num)
theorem B2007907 : Blo 2007435 2007907 := bstep (se 1 (by rfl) ⟨1505930, by rfl⟩ : syracuseStep 2007907 = 3011861) B3011861
theorem B5576597 : Blo 2007435 5576597 := bbase (se 6 (by rfl) ⟨130701, by rfl⟩ : syracuseStep 5576597 = 261403) (by norm_num)
theorem B3717731 : Blo 2007435 3717731 := bstep (se 1 (by rfl) ⟨2788298, by rfl⟩ : syracuseStep 3717731 = 5576597) B5576597
theorem B2478487 : Blo 2007435 2478487 := bstep (se 1 (by rfl) ⟨1858865, by rfl⟩ : syracuseStep 2478487 = 3717731) B3717731
theorem B3304649 : Blo 2007435 3304649 := bstep (se 2 (by rfl) ⟨1239243, by rfl⟩ : syracuseStep 3304649 = 2478487) B2478487
theorem B8812397 : Blo 2007435 8812397 := bstep (se 3 (by rfl) ⟨1652324, by rfl⟩ : syracuseStep 8812397 = 3304649) B3304649
theorem B5874931 : Blo 2007435 5874931 := bstep (se 1 (by rfl) ⟨4406198, by rfl⟩ : syracuseStep 5874931 = 8812397) B8812397
theorem B7833241 : Blo 2007435 7833241 := bstep (se 2 (by rfl) ⟨2937465, by rfl⟩ : syracuseStep 7833241 = 5874931) B5874931
theorem B10444321 : Blo 2007435 10444321 := bstep (se 2 (by rfl) ⟨3916620, by rfl⟩ : syracuseStep 10444321 = 7833241) B7833241
theorem B55703045 : Blo 2007435 55703045 := bstep (se 4 (by rfl) ⟨5222160, by rfl⟩ : syracuseStep 55703045 = 10444321) B10444321
theorem B37135363 : Blo 2007435 37135363 := bstep (se 1 (by rfl) ⟨27851522, by rfl⟩ : syracuseStep 37135363 = 55703045) B55703045
theorem B49513817 : Blo 2007435 49513817 := bstep (se 2 (by rfl) ⟨18567681, by rfl⟩ : syracuseStep 49513817 = 37135363) B37135363
theorem B33009211 : Blo 2007435 33009211 := bstep (se 1 (by rfl) ⟨24756908, by rfl⟩ : syracuseStep 33009211 = 49513817) B49513817
theorem B44012281 : Blo 2007435 44012281 := bstep (se 2 (by rfl) ⟨16504605, by rfl⟩ : syracuseStep 44012281 = 33009211) B33009211
theorem B58683041 : Blo 2007435 58683041 := bstep (se 2 (by rfl) ⟨22006140, by rfl⟩ : syracuseStep 58683041 = 44012281) B44012281
theorem B39122027 : Blo 2007435 39122027 := bstep (se 1 (by rfl) ⟨29341520, by rfl⟩ : syracuseStep 39122027 = 58683041) B58683041
theorem B26081351 : Blo 2007435 26081351 := bstep (se 1 (by rfl) ⟨19561013, by rfl⟩ : syracuseStep 26081351 = 39122027) B39122027
theorem B17387567 : Blo 2007435 17387567 := bstep (se 1 (by rfl) ⟨13040675, by rfl⟩ : syracuseStep 17387567 = 26081351) B26081351
theorem B11591711 : Blo 2007435 11591711 := bstep (se 1 (by rfl) ⟨8693783, by rfl⟩ : syracuseStep 11591711 = 17387567) B17387567
theorem B7727807 : Blo 2007435 7727807 := bstep (se 1 (by rfl) ⟨5795855, by rfl⟩ : syracuseStep 7727807 = 11591711) B11591711
theorem B5151871 : Blo 2007435 5151871 := bstep (se 1 (by rfl) ⟨3863903, by rfl⟩ : syracuseStep 5151871 = 7727807) B7727807
theorem B6869161 : Blo 2007435 6869161 := bstep (se 2 (by rfl) ⟨2575935, by rfl⟩ : syracuseStep 6869161 = 5151871) B5151871
theorem B9158881 : Blo 2007435 9158881 := bstep (se 2 (by rfl) ⟨3434580, by rfl⟩ : syracuseStep 9158881 = 6869161) B6869161
theorem B12211841 : Blo 2007435 12211841 := bstep (se 2 (by rfl) ⟨4579440, by rfl⟩ : syracuseStep 12211841 = 9158881) B9158881
theorem B32564909 : Blo 2007435 32564909 := bstep (se 3 (by rfl) ⟨6105920, by rfl⟩ : syracuseStep 32564909 = 12211841) B12211841
theorem B21709939 : Blo 2007435 21709939 := bstep (se 1 (by rfl) ⟨16282454, by rfl⟩ : syracuseStep 21709939 = 32564909) B32564909
theorem B28946585 : Blo 2007435 28946585 := bstep (se 2 (by rfl) ⟨10854969, by rfl⟩ : syracuseStep 28946585 = 21709939) B21709939
theorem B19297723 : Blo 2007435 19297723 := bstep (se 1 (by rfl) ⟨14473292, by rfl⟩ : syracuseStep 19297723 = 28946585) B28946585
theorem B25730297 : Blo 2007435 25730297 := bstep (se 2 (by rfl) ⟨9648861, by rfl⟩ : syracuseStep 25730297 = 19297723) B19297723
theorem B17153531 : Blo 2007435 17153531 := bstep (se 1 (by rfl) ⟨12865148, by rfl⟩ : syracuseStep 17153531 = 25730297) B25730297
theorem B11435687 : Blo 2007435 11435687 := bstep (se 1 (by rfl) ⟨8576765, by rfl⟩ : syracuseStep 11435687 = 17153531) B17153531
theorem B7623791 : Blo 2007435 7623791 := bstep (se 1 (by rfl) ⟨5717843, by rfl⟩ : syracuseStep 7623791 = 11435687) B11435687
theorem B5082527 : Blo 2007435 5082527 := bstep (se 1 (by rfl) ⟨3811895, by rfl⟩ : syracuseStep 5082527 = 7623791) B7623791
theorem B3388351 : Blo 2007435 3388351 := bstep (se 1 (by rfl) ⟨2541263, by rfl⟩ : syracuseStep 3388351 = 5082527) B5082527
theorem B4517801 : Blo 2007435 4517801 := bstep (se 2 (by rfl) ⟨1694175, by rfl⟩ : syracuseStep 4517801 = 3388351) B3388351
theorem B3011867 : Blo 2007435 3011867 := bstep (se 1 (by rfl) ⟨2258900, by rfl⟩ : syracuseStep 3011867 = 4517801) B4517801
theorem B2007911 : Blo 2007435 2007911 := bstep (se 1 (by rfl) ⟨1505933, by rfl⟩ : syracuseStep 2007911 = 3011867) B3011867
theorem B2258905 : Blo 2007435 2258905 := bbase (se 2 (by rfl) ⟨847089, by rfl⟩ : syracuseStep 2258905 = 1694179) (by norm_num)
theorem B3011873 : Blo 2007435 3011873 := bstep (se 2 (by rfl) ⟨1129452, by rfl⟩ : syracuseStep 3011873 = 2258905) B2258905
theorem B2007915 : Blo 2007435 2007915 := bstep (se 1 (by rfl) ⟨1505936, by rfl⟩ : syracuseStep 2007915 = 3011873) B3011873
theorem B2858933 : Blo 2007435 2858933 := bbase (se 5 (by rfl) ⟨134012, by rfl⟩ : syracuseStep 2858933 = 268025) (by norm_num)
theorem B7623821 : Blo 2007435 7623821 := bstep (se 3 (by rfl) ⟨1429466, by rfl⟩ : syracuseStep 7623821 = 2858933) B2858933
theorem B5082547 : Blo 2007435 5082547 := bstep (se 1 (by rfl) ⟨3811910, by rfl⟩ : syracuseStep 5082547 = 7623821) B7623821
theorem B6776729 : Blo 2007435 6776729 := bstep (se 2 (by rfl) ⟨2541273, by rfl⟩ : syracuseStep 6776729 = 5082547) B5082547
theorem B4517819 : Blo 2007435 4517819 := bstep (se 1 (by rfl) ⟨3388364, by rfl⟩ : syracuseStep 4517819 = 6776729) B6776729
theorem B3011879 : Blo 2007435 3011879 := bstep (se 1 (by rfl) ⟨2258909, by rfl⟩ : syracuseStep 3011879 = 4517819) B4517819
theorem B2007919 : Blo 2007435 2007919 := bstep (se 1 (by rfl) ⟨1505939, by rfl⟩ : syracuseStep 2007919 = 3011879) B3011879
theorem B3011885 : Blo 2007435 3011885 := bbase (se 3 (by rfl) ⟨564728, by rfl⟩ : syracuseStep 3011885 = 1129457) (by norm_num)
theorem B2007923 : Blo 2007435 2007923 := bstep (se 1 (by rfl) ⟨1505942, by rfl⟩ : syracuseStep 2007923 = 3011885) B3011885
theorem B4517837 : Blo 2007435 4517837 := bbase (se 3 (by rfl) ⟨847094, by rfl⟩ : syracuseStep 4517837 = 1694189) (by norm_num)
theorem B3011891 : Blo 2007435 3011891 := bstep (se 1 (by rfl) ⟨2258918, by rfl⟩ : syracuseStep 3011891 = 4517837) B4517837
theorem B2007927 : Blo 2007435 2007927 := bstep (se 1 (by rfl) ⟨1505945, by rfl⟩ : syracuseStep 2007927 = 3011891) B3011891
theorem B2541289 : Blo 2007435 2541289 := bbase (se 2 (by rfl) ⟨952983, by rfl⟩ : syracuseStep 2541289 = 1905967) (by norm_num)
theorem B3388385 : Blo 2007435 3388385 := bstep (se 2 (by rfl) ⟨1270644, by rfl⟩ : syracuseStep 3388385 = 2541289) B2541289
theorem B2258923 : Blo 2007435 2258923 := bstep (se 1 (by rfl) ⟨1694192, by rfl⟩ : syracuseStep 2258923 = 3388385) B3388385
theorem B3011897 : Blo 2007435 3011897 := bstep (se 2 (by rfl) ⟨1129461, by rfl⟩ : syracuseStep 3011897 = 2258923) B2258923
theorem B2007931 : Blo 2007435 2007931 := bstep (se 1 (by rfl) ⟨1505948, by rfl⟩ : syracuseStep 2007931 = 3011897) B3011897
theorem B12865301 : Blo 2007435 12865301 := bbase (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) (by norm_num)
theorem B8576867 : Blo 2007435 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B22871645 : Blo 2007435 22871645 := bstep (se 3 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 22871645 = 8576867) B8576867
theorem B15247763 : Blo 2007435 15247763 := bstep (se 1 (by rfl) ⟨11435822, by rfl⟩ : syracuseStep 15247763 = 22871645) B22871645
theorem B10165175 : Blo 2007435 10165175 := bstep (se 1 (by rfl) ⟨7623881, by rfl⟩ : syracuseStep 10165175 = 15247763) B15247763
theorem B6776783 : Blo 2007435 6776783 := bstep (se 1 (by rfl) ⟨5082587, by rfl⟩ : syracuseStep 6776783 = 10165175) B10165175
theorem B4517855 : Blo 2007435 4517855 := bstep (se 1 (by rfl) ⟨3388391, by rfl⟩ : syracuseStep 4517855 = 6776783) B6776783
theorem B3011903 : Blo 2007435 3011903 := bstep (se 1 (by rfl) ⟨2258927, by rfl⟩ : syracuseStep 3011903 = 4517855) B4517855
theorem B2007935 : Blo 2007435 2007935 := bstep (se 1 (by rfl) ⟨1505951, by rfl⟩ : syracuseStep 2007935 = 3011903) B3011903
theorem B3011909 : Blo 2007435 3011909 := bbase (se 4 (by rfl) ⟨282366, by rfl⟩ : syracuseStep 3011909 = 564733) (by norm_num)
theorem B2007939 : Blo 2007435 2007939 := bstep (se 1 (by rfl) ⟨1505954, by rfl⟩ : syracuseStep 2007939 = 3011909) B3011909
theorem B3388405 : Blo 2007435 3388405 := bbase (se 5 (by rfl) ⟨158831, by rfl⟩ : syracuseStep 3388405 = 317663) (by norm_num)
theorem B4517873 : Blo 2007435 4517873 := bstep (se 2 (by rfl) ⟨1694202, by rfl⟩ : syracuseStep 4517873 = 3388405) B3388405
theorem B3011915 : Blo 2007435 3011915 := bstep (se 1 (by rfl) ⟨2258936, by rfl⟩ : syracuseStep 3011915 = 4517873) B4517873
theorem B2007943 : Blo 2007435 2007943 := bstep (se 1 (by rfl) ⟨1505957, by rfl⟩ : syracuseStep 2007943 = 3011915) B3011915
theorem B2258941 : Blo 2007435 2258941 := bbase (se 3 (by rfl) ⟨423551, by rfl⟩ : syracuseStep 2258941 = 847103) (by norm_num)
theorem B3011921 : Blo 2007435 3011921 := bstep (se 2 (by rfl) ⟨1129470, by rfl⟩ : syracuseStep 3011921 = 2258941) B2258941
theorem B2007947 : Blo 2007435 2007947 := bstep (se 1 (by rfl) ⟨1505960, by rfl⟩ : syracuseStep 2007947 = 3011921) B3011921
theorem B6776837 : Blo 2007435 6776837 := bbase (se 4 (by rfl) ⟨635328, by rfl⟩ : syracuseStep 6776837 = 1270657) (by norm_num)
theorem B4517891 : Blo 2007435 4517891 := bstep (se 1 (by rfl) ⟨3388418, by rfl⟩ : syracuseStep 4517891 = 6776837) B6776837
theorem B3011927 : Blo 2007435 3011927 := bstep (se 1 (by rfl) ⟨2258945, by rfl⟩ : syracuseStep 3011927 = 4517891) B4517891
theorem B2007951 : Blo 2007435 2007951 := bstep (se 1 (by rfl) ⟨1505963, by rfl⟩ : syracuseStep 2007951 = 3011927) B3011927
theorem B3011933 : Blo 2007435 3011933 := bbase (se 3 (by rfl) ⟨564737, by rfl⟩ : syracuseStep 3011933 = 1129475) (by norm_num)
theorem B2007955 : Blo 2007435 2007955 := bstep (se 1 (by rfl) ⟨1505966, by rfl⟩ : syracuseStep 2007955 = 3011933) B3011933
theorem B4517909 : Blo 2007435 4517909 := bbase (se 6 (by rfl) ⟨105888, by rfl⟩ : syracuseStep 4517909 = 211777) (by norm_num)
theorem B3011939 : Blo 2007435 3011939 := bstep (se 1 (by rfl) ⟨2258954, by rfl⟩ : syracuseStep 3011939 = 4517909) B4517909
theorem B2007959 : Blo 2007435 2007959 := bstep (se 1 (by rfl) ⟨1505969, by rfl⟩ : syracuseStep 2007959 = 3011939) B3011939
theorem B7623989 : Blo 2007435 7623989 := bbase (se 5 (by rfl) ⟨357374, by rfl⟩ : syracuseStep 7623989 = 714749) (by norm_num)
theorem B5082659 : Blo 2007435 5082659 := bstep (se 1 (by rfl) ⟨3811994, by rfl⟩ : syracuseStep 5082659 = 7623989) B7623989
theorem B3388439 : Blo 2007435 3388439 := bstep (se 1 (by rfl) ⟨2541329, by rfl⟩ : syracuseStep 3388439 = 5082659) B5082659
theorem B2258959 : Blo 2007435 2258959 := bstep (se 1 (by rfl) ⟨1694219, by rfl⟩ : syracuseStep 2258959 = 3388439) B3388439
theorem B3011945 : Blo 2007435 3011945 := bstep (se 2 (by rfl) ⟨1129479, by rfl⟩ : syracuseStep 3011945 = 2258959) B2258959
theorem B2007963 : Blo 2007435 2007963 := bstep (se 1 (by rfl) ⟨1505972, by rfl⟩ : syracuseStep 2007963 = 3011945) B3011945
theorem B2576009 : Blo 2007435 2576009 := bbase (se 2 (by rfl) ⟨966003, by rfl⟩ : syracuseStep 2576009 = 1932007) (by norm_num)
theorem B6869357 : Blo 2007435 6869357 := bstep (se 3 (by rfl) ⟨1288004, by rfl⟩ : syracuseStep 6869357 = 2576009) B2576009
theorem B4579571 : Blo 2007435 4579571 := bstep (se 1 (by rfl) ⟨3434678, by rfl⟩ : syracuseStep 4579571 = 6869357) B6869357
theorem B3053047 : Blo 2007435 3053047 := bstep (se 1 (by rfl) ⟨2289785, by rfl⟩ : syracuseStep 3053047 = 4579571) B4579571
theorem B4070729 : Blo 2007435 4070729 := bstep (se 2 (by rfl) ⟨1526523, by rfl⟩ : syracuseStep 4070729 = 3053047) B3053047
theorem B2713819 : Blo 2007435 2713819 := bstep (se 1 (by rfl) ⟨2035364, by rfl⟩ : syracuseStep 2713819 = 4070729) B4070729
theorem B3618425 : Blo 2007435 3618425 := bstep (se 2 (by rfl) ⟨1356909, by rfl⟩ : syracuseStep 3618425 = 2713819) B2713819
theorem B2412283 : Blo 2007435 2412283 := bstep (se 1 (by rfl) ⟨1809212, by rfl⟩ : syracuseStep 2412283 = 3618425) B3618425
theorem B3216377 : Blo 2007435 3216377 := bstep (se 2 (by rfl) ⟨1206141, by rfl⟩ : syracuseStep 3216377 = 2412283) B2412283
theorem B2144251 : Blo 2007435 2144251 := bstep (se 1 (by rfl) ⟨1608188, by rfl⟩ : syracuseStep 2144251 = 3216377) B3216377
theorem B11436005 : Blo 2007435 11436005 := bstep (se 4 (by rfl) ⟨1072125, by rfl⟩ : syracuseStep 11436005 = 2144251) B2144251
theorem B7624003 : Blo 2007435 7624003 := bstep (se 1 (by rfl) ⟨5718002, by rfl⟩ : syracuseStep 7624003 = 11436005) B11436005
theorem B10165337 : Blo 2007435 10165337 := bstep (se 2 (by rfl) ⟨3812001, by rfl⟩ : syracuseStep 10165337 = 7624003) B7624003
theorem B6776891 : Blo 2007435 6776891 := bstep (se 1 (by rfl) ⟨5082668, by rfl⟩ : syracuseStep 6776891 = 10165337) B10165337
theorem B4517927 : Blo 2007435 4517927 := bstep (se 1 (by rfl) ⟨3388445, by rfl⟩ : syracuseStep 4517927 = 6776891) B6776891
theorem B3011951 : Blo 2007435 3011951 := bstep (se 1 (by rfl) ⟨2258963, by rfl⟩ : syracuseStep 3011951 = 4517927) B4517927
theorem B2007967 : Blo 2007435 2007967 := bstep (se 1 (by rfl) ⟨1505975, by rfl⟩ : syracuseStep 2007967 = 3011951) B3011951
theorem B3011957 : Blo 2007435 3011957 := bbase (se 5 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 3011957 = 282371) (by norm_num)
theorem B2007971 : Blo 2007435 2007971 := bstep (se 1 (by rfl) ⟨1505978, by rfl⟩ : syracuseStep 2007971 = 3011957) B3011957
theorem B2859013 : Blo 2007435 2859013 := bbase (se 4 (by rfl) ⟨268032, by rfl⟩ : syracuseStep 2859013 = 536065) (by norm_num)
theorem B3812017 : Blo 2007435 3812017 := bstep (se 2 (by rfl) ⟨1429506, by rfl⟩ : syracuseStep 3812017 = 2859013) B2859013
theorem B5082689 : Blo 2007435 5082689 := bstep (se 2 (by rfl) ⟨1906008, by rfl⟩ : syracuseStep 5082689 = 3812017) B3812017
theorem B3388459 : Blo 2007435 3388459 := bstep (se 1 (by rfl) ⟨2541344, by rfl⟩ : syracuseStep 3388459 = 5082689) B5082689
theorem B4517945 : Blo 2007435 4517945 := bstep (se 2 (by rfl) ⟨1694229, by rfl⟩ : syracuseStep 4517945 = 3388459) B3388459
theorem B3011963 : Blo 2007435 3011963 := bstep (se 1 (by rfl) ⟨2258972, by rfl⟩ : syracuseStep 3011963 = 4517945) B4517945
theorem B2007975 : Blo 2007435 2007975 := bstep (se 1 (by rfl) ⟨1505981, by rfl⟩ : syracuseStep 2007975 = 3011963) B3011963
theorem B2258977 : Blo 2007435 2258977 := bbase (se 2 (by rfl) ⟨847116, by rfl⟩ : syracuseStep 2258977 = 1694233) (by norm_num)
theorem B3011969 : Blo 2007435 3011969 := bstep (se 2 (by rfl) ⟨1129488, by rfl⟩ : syracuseStep 3011969 = 2258977) B2258977
theorem B2007979 : Blo 2007435 2007979 := bstep (se 1 (by rfl) ⟨1505984, by rfl⟩ : syracuseStep 2007979 = 3011969) B3011969
theorem B5082709 : Blo 2007435 5082709 := bbase (se 8 (by rfl) ⟨29781, by rfl⟩ : syracuseStep 5082709 = 59563) (by norm_num)
theorem B6776945 : Blo 2007435 6776945 := bstep (se 2 (by rfl) ⟨2541354, by rfl⟩ : syracuseStep 6776945 = 5082709) B5082709
theorem B4517963 : Blo 2007435 4517963 := bstep (se 1 (by rfl) ⟨3388472, by rfl⟩ : syracuseStep 4517963 = 6776945) B6776945
theorem B3011975 : Blo 2007435 3011975 := bstep (se 1 (by rfl) ⟨2258981, by rfl⟩ : syracuseStep 3011975 = 4517963) B4517963
theorem B2007983 : Blo 2007435 2007983 := bstep (se 1 (by rfl) ⟨1505987, by rfl⟩ : syracuseStep 2007983 = 3011975) B3011975
theorem B3011981 : Blo 2007435 3011981 := bbase (se 3 (by rfl) ⟨564746, by rfl⟩ : syracuseStep 3011981 = 1129493) (by norm_num)
theorem B2007987 : Blo 2007435 2007987 := bstep (se 1 (by rfl) ⟨1505990, by rfl⟩ : syracuseStep 2007987 = 3011981) B3011981
theorem B4517981 : Blo 2007435 4517981 := bbase (se 3 (by rfl) ⟨847121, by rfl⟩ : syracuseStep 4517981 = 1694243) (by norm_num)
theorem B3011987 : Blo 2007435 3011987 := bstep (se 1 (by rfl) ⟨2258990, by rfl⟩ : syracuseStep 3011987 = 4517981) B4517981
theorem B2007991 : Blo 2007435 2007991 := bstep (se 1 (by rfl) ⟨1505993, by rfl⟩ : syracuseStep 2007991 = 3011987) B3011987
theorem B3388493 : Blo 2007435 3388493 := bbase (se 3 (by rfl) ⟨635342, by rfl⟩ : syracuseStep 3388493 = 1270685) (by norm_num)
theorem B2258995 : Blo 2007435 2258995 := bstep (se 1 (by rfl) ⟨1694246, by rfl⟩ : syracuseStep 2258995 = 3388493) B3388493
theorem B3011993 : Blo 2007435 3011993 := bstep (se 2 (by rfl) ⟨1129497, by rfl⟩ : syracuseStep 3011993 = 2258995) B2258995
theorem B2007995 : Blo 2007435 2007995 := bstep (se 1 (by rfl) ⟨1505996, by rfl⟩ : syracuseStep 2007995 = 3011993) B3011993
theorem B27477845 : Blo 2007435 27477845 := bbase (se 9 (by rfl) ⟨80501, by rfl⟩ : syracuseStep 27477845 = 161003) (by norm_num)
theorem B18318563 : Blo 2007435 18318563 := bstep (se 1 (by rfl) ⟨13738922, by rfl⟩ : syracuseStep 18318563 = 27477845) B27477845
theorem B12212375 : Blo 2007435 12212375 := bstep (se 1 (by rfl) ⟨9159281, by rfl⟩ : syracuseStep 12212375 = 18318563) B18318563
theorem B32566333 : Blo 2007435 32566333 := bstep (se 3 (by rfl) ⟨6106187, by rfl⟩ : syracuseStep 32566333 = 12212375) B12212375
theorem B43421777 : Blo 2007435 43421777 := bstep (se 2 (by rfl) ⟨16283166, by rfl⟩ : syracuseStep 43421777 = 32566333) B32566333
theorem B28947851 : Blo 2007435 28947851 := bstep (se 1 (by rfl) ⟨21710888, by rfl⟩ : syracuseStep 28947851 = 43421777) B43421777
theorem B19298567 : Blo 2007435 19298567 := bstep (se 1 (by rfl) ⟨14473925, by rfl⟩ : syracuseStep 19298567 = 28947851) B28947851
theorem B12865711 : Blo 2007435 12865711 := bstep (se 1 (by rfl) ⟨9649283, by rfl⟩ : syracuseStep 12865711 = 19298567) B19298567
theorem B17154281 : Blo 2007435 17154281 := bstep (se 2 (by rfl) ⟨6432855, by rfl⟩ : syracuseStep 17154281 = 12865711) B12865711
theorem B11436187 : Blo 2007435 11436187 := bstep (se 1 (by rfl) ⟨8577140, by rfl⟩ : syracuseStep 11436187 = 17154281) B17154281
theorem B15248249 : Blo 2007435 15248249 := bstep (se 2 (by rfl) ⟨5718093, by rfl⟩ : syracuseStep 15248249 = 11436187) B11436187
theorem B10165499 : Blo 2007435 10165499 := bstep (se 1 (by rfl) ⟨7624124, by rfl⟩ : syracuseStep 10165499 = 15248249) B15248249
theorem B6776999 : Blo 2007435 6776999 := bstep (se 1 (by rfl) ⟨5082749, by rfl⟩ : syracuseStep 6776999 = 10165499) B10165499
theorem B4517999 : Blo 2007435 4517999 := bstep (se 1 (by rfl) ⟨3388499, by rfl⟩ : syracuseStep 4517999 = 6776999) B6776999
theorem B3011999 : Blo 2007435 3011999 := bstep (se 1 (by rfl) ⟨2258999, by rfl⟩ : syracuseStep 3011999 = 4517999) B4517999
theorem B2007999 : Blo 2007435 2007999 := bstep (se 1 (by rfl) ⟨1505999, by rfl⟩ : syracuseStep 2007999 = 3011999) B3011999
theorem B3012005 : Blo 2007435 3012005 := bbase (se 4 (by rfl) ⟨282375, by rfl⟩ : syracuseStep 3012005 = 564751) (by norm_num)
theorem B2008003 : Blo 2007435 2008003 := bstep (se 1 (by rfl) ⟨1506002, by rfl⟩ : syracuseStep 2008003 = 3012005) B3012005
theorem B2541385 : Blo 2007435 2541385 := bbase (se 2 (by rfl) ⟨953019, by rfl⟩ : syracuseStep 2541385 = 1906039) (by norm_num)
theorem B3388513 : Blo 2007435 3388513 := bstep (se 2 (by rfl) ⟨1270692, by rfl⟩ : syracuseStep 3388513 = 2541385) B2541385
theorem B4518017 : Blo 2007435 4518017 := bstep (se 2 (by rfl) ⟨1694256, by rfl⟩ : syracuseStep 4518017 = 3388513) B3388513
theorem B3012011 : Blo 2007435 3012011 := bstep (se 1 (by rfl) ⟨2259008, by rfl⟩ : syracuseStep 3012011 = 4518017) B4518017
theorem B2008007 : Blo 2007435 2008007 := bstep (se 1 (by rfl) ⟨1506005, by rfl⟩ : syracuseStep 2008007 = 3012011) B3012011
theorem B2259013 : Blo 2007435 2259013 := bbase (se 4 (by rfl) ⟨211782, by rfl⟩ : syracuseStep 2259013 = 423565) (by norm_num)
theorem B3012017 : Blo 2007435 3012017 := bstep (se 2 (by rfl) ⟨1129506, by rfl⟩ : syracuseStep 3012017 = 2259013) B2259013
theorem B2008011 : Blo 2007435 2008011 := bstep (se 1 (by rfl) ⟨1506008, by rfl⟩ : syracuseStep 2008011 = 3012017) B3012017
theorem B3812093 : Blo 2007435 3812093 := bbase (se 3 (by rfl) ⟨714767, by rfl⟩ : syracuseStep 3812093 = 1429535) (by norm_num)
theorem B2541395 : Blo 2007435 2541395 := bstep (se 1 (by rfl) ⟨1906046, by rfl⟩ : syracuseStep 2541395 = 3812093) B3812093
theorem B6777053 : Blo 2007435 6777053 := bstep (se 3 (by rfl) ⟨1270697, by rfl⟩ : syracuseStep 6777053 = 2541395) B2541395
theorem B4518035 : Blo 2007435 4518035 := bstep (se 1 (by rfl) ⟨3388526, by rfl⟩ : syracuseStep 4518035 = 6777053) B6777053
theorem B3012023 : Blo 2007435 3012023 := bstep (se 1 (by rfl) ⟨2259017, by rfl⟩ : syracuseStep 3012023 = 4518035) B4518035
theorem B2008015 : Blo 2007435 2008015 := bstep (se 1 (by rfl) ⟨1506011, by rfl⟩ : syracuseStep 2008015 = 3012023) B3012023
theorem B3012029 : Blo 2007435 3012029 := bbase (se 3 (by rfl) ⟨564755, by rfl⟩ : syracuseStep 3012029 = 1129511) (by norm_num)
theorem B2008019 : Blo 2007435 2008019 := bstep (se 1 (by rfl) ⟨1506014, by rfl⟩ : syracuseStep 2008019 = 3012029) B3012029
theorem B4518053 : Blo 2007435 4518053 := bbase (se 4 (by rfl) ⟨423567, by rfl⟩ : syracuseStep 4518053 = 847135) (by norm_num)
theorem B3012035 : Blo 2007435 3012035 := bstep (se 1 (by rfl) ⟨2259026, by rfl⟩ : syracuseStep 3012035 = 4518053) B4518053
theorem B2008023 : Blo 2007435 2008023 := bstep (se 1 (by rfl) ⟨1506017, by rfl⟩ : syracuseStep 2008023 = 3012035) B3012035
theorem B5082821 : Blo 2007435 5082821 := bbase (se 4 (by rfl) ⟨476514, by rfl⟩ : syracuseStep 5082821 = 953029) (by norm_num)
theorem B3388547 : Blo 2007435 3388547 := bstep (se 1 (by rfl) ⟨2541410, by rfl⟩ : syracuseStep 3388547 = 5082821) B5082821
theorem B2259031 : Blo 2007435 2259031 := bstep (se 1 (by rfl) ⟨1694273, by rfl⟩ : syracuseStep 2259031 = 3388547) B3388547
theorem B3012041 : Blo 2007435 3012041 := bstep (se 2 (by rfl) ⟨1129515, by rfl⟩ : syracuseStep 3012041 = 2259031) B2259031
theorem B2008027 : Blo 2007435 2008027 := bstep (se 1 (by rfl) ⟨1506020, by rfl⟩ : syracuseStep 2008027 = 3012041) B3012041
theorem B36637717 : Blo 2007435 36637717 := bbase (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) (by norm_num)
theorem B48850289 : Blo 2007435 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B32566859 : Blo 2007435 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B21711239 : Blo 2007435 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B14474159 : Blo 2007435 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B9649439 : Blo 2007435 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B6432959 : Blo 2007435 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B4288639 : Blo 2007435 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B5718185 : Blo 2007435 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B3812123 : Blo 2007435 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B10165661 : Blo 2007435 10165661 := bstep (se 3 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 10165661 = 3812123) B3812123
theorem B6777107 : Blo 2007435 6777107 := bstep (se 1 (by rfl) ⟨5082830, by rfl⟩ : syracuseStep 6777107 = 10165661) B10165661
theorem B4518071 : Blo 2007435 4518071 := bstep (se 1 (by rfl) ⟨3388553, by rfl⟩ : syracuseStep 4518071 = 6777107) B6777107
theorem B3012047 : Blo 2007435 3012047 := bstep (se 1 (by rfl) ⟨2259035, by rfl⟩ : syracuseStep 3012047 = 4518071) B4518071
theorem B2008031 : Blo 2007435 2008031 := bstep (se 1 (by rfl) ⟨1506023, by rfl⟩ : syracuseStep 2008031 = 3012047) B3012047
theorem B3012053 : Blo 2007435 3012053 := bbase (se 7 (by rfl) ⟨35297, by rfl⟩ : syracuseStep 3012053 = 70595) (by norm_num)
theorem B2008035 : Blo 2007435 2008035 := bstep (se 1 (by rfl) ⟨1506026, by rfl⟩ : syracuseStep 2008035 = 3012053) B3012053
theorem B7624277 : Blo 2007435 7624277 := bbase (se 8 (by rfl) ⟨44673, by rfl⟩ : syracuseStep 7624277 = 89347) (by norm_num)
theorem B5082851 : Blo 2007435 5082851 := bstep (se 1 (by rfl) ⟨3812138, by rfl⟩ : syracuseStep 5082851 = 7624277) B7624277
theorem B3388567 : Blo 2007435 3388567 := bstep (se 1 (by rfl) ⟨2541425, by rfl⟩ : syracuseStep 3388567 = 5082851) B5082851
theorem B4518089 : Blo 2007435 4518089 := bstep (se 2 (by rfl) ⟨1694283, by rfl⟩ : syracuseStep 4518089 = 3388567) B3388567
theorem B3012059 : Blo 2007435 3012059 := bstep (se 1 (by rfl) ⟨2259044, by rfl⟩ : syracuseStep 3012059 = 4518089) B4518089
theorem B2008039 : Blo 2007435 2008039 := bstep (se 1 (by rfl) ⟨1506029, by rfl⟩ : syracuseStep 2008039 = 3012059) B3012059
theorem B2259049 : Blo 2007435 2259049 := bbase (se 2 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 2259049 = 1694287) (by norm_num)
theorem B3012065 : Blo 2007435 3012065 := bstep (se 2 (by rfl) ⟨1129524, by rfl⟩ : syracuseStep 3012065 = 2259049) B2259049
theorem B2008043 : Blo 2007435 2008043 := bstep (se 1 (by rfl) ⟨1506032, by rfl⟩ : syracuseStep 2008043 = 3012065) B3012065
theorem B4406501 : Blo 2007435 4406501 := bbase (se 4 (by rfl) ⟨413109, by rfl⟩ : syracuseStep 4406501 = 826219) (by norm_num)
theorem B11750669 : Blo 2007435 11750669 := bstep (se 3 (by rfl) ⟨2203250, by rfl⟩ : syracuseStep 11750669 = 4406501) B4406501
theorem B7833779 : Blo 2007435 7833779 := bstep (se 1 (by rfl) ⟨5875334, by rfl⟩ : syracuseStep 7833779 = 11750669) B11750669
theorem B5222519 : Blo 2007435 5222519 := bstep (se 1 (by rfl) ⟨3916889, by rfl⟩ : syracuseStep 5222519 = 7833779) B7833779
theorem B3481679 : Blo 2007435 3481679 := bstep (se 1 (by rfl) ⟨2611259, by rfl⟩ : syracuseStep 3481679 = 5222519) B5222519
theorem B2321119 : Blo 2007435 2321119 := bstep (se 1 (by rfl) ⟨1740839, by rfl⟩ : syracuseStep 2321119 = 3481679) B3481679
theorem B12379301 : Blo 2007435 12379301 := bstep (se 4 (by rfl) ⟨1160559, by rfl⟩ : syracuseStep 12379301 = 2321119) B2321119
theorem B8252867 : Blo 2007435 8252867 := bstep (se 1 (by rfl) ⟨6189650, by rfl⟩ : syracuseStep 8252867 = 12379301) B12379301
theorem B22007645 : Blo 2007435 22007645 := bstep (se 3 (by rfl) ⟨4126433, by rfl⟩ : syracuseStep 22007645 = 8252867) B8252867
theorem B14671763 : Blo 2007435 14671763 := bstep (se 1 (by rfl) ⟨11003822, by rfl⟩ : syracuseStep 14671763 = 22007645) B22007645
theorem B9781175 : Blo 2007435 9781175 := bstep (se 1 (by rfl) ⟨7335881, by rfl⟩ : syracuseStep 9781175 = 14671763) B14671763
theorem B26083133 : Blo 2007435 26083133 := bstep (se 3 (by rfl) ⟨4890587, by rfl⟩ : syracuseStep 26083133 = 9781175) B9781175
theorem B17388755 : Blo 2007435 17388755 := bstep (se 1 (by rfl) ⟨13041566, by rfl⟩ : syracuseStep 17388755 = 26083133) B26083133
theorem B11592503 : Blo 2007435 11592503 := bstep (se 1 (by rfl) ⟨8694377, by rfl⟩ : syracuseStep 11592503 = 17388755) B17388755
theorem B7728335 : Blo 2007435 7728335 := bstep (se 1 (by rfl) ⟨5796251, by rfl⟩ : syracuseStep 7728335 = 11592503) B11592503
theorem B5152223 : Blo 2007435 5152223 := bstep (se 1 (by rfl) ⟨3864167, by rfl⟩ : syracuseStep 5152223 = 7728335) B7728335
theorem B3434815 : Blo 2007435 3434815 := bstep (se 1 (by rfl) ⟨2576111, by rfl⟩ : syracuseStep 3434815 = 5152223) B5152223
theorem B4579753 : Blo 2007435 4579753 := bstep (se 2 (by rfl) ⟨1717407, by rfl⟩ : syracuseStep 4579753 = 3434815) B3434815
theorem B6106337 : Blo 2007435 6106337 := bstep (se 2 (by rfl) ⟨2289876, by rfl⟩ : syracuseStep 6106337 = 4579753) B4579753
theorem B4070891 : Blo 2007435 4070891 := bstep (se 1 (by rfl) ⟨3053168, by rfl⟩ : syracuseStep 4070891 = 6106337) B6106337
theorem B2713927 : Blo 2007435 2713927 := bstep (se 1 (by rfl) ⟨2035445, by rfl⟩ : syracuseStep 2713927 = 4070891) B4070891
theorem B3618569 : Blo 2007435 3618569 := bstep (se 2 (by rfl) ⟨1356963, by rfl⟩ : syracuseStep 3618569 = 2713927) B2713927
theorem B2412379 : Blo 2007435 2412379 := bstep (se 1 (by rfl) ⟨1809284, by rfl⟩ : syracuseStep 2412379 = 3618569) B3618569
theorem B3216505 : Blo 2007435 3216505 := bstep (se 2 (by rfl) ⟨1206189, by rfl⟩ : syracuseStep 3216505 = 2412379) B2412379
theorem B4288673 : Blo 2007435 4288673 := bstep (se 2 (by rfl) ⟨1608252, by rfl⟩ : syracuseStep 4288673 = 3216505) B3216505
theorem B11436461 : Blo 2007435 11436461 := bstep (se 3 (by rfl) ⟨2144336, by rfl⟩ : syracuseStep 11436461 = 4288673) B4288673
theorem B7624307 : Blo 2007435 7624307 := bstep (se 1 (by rfl) ⟨5718230, by rfl⟩ : syracuseStep 7624307 = 11436461) B11436461
theorem B5082871 : Blo 2007435 5082871 := bstep (se 1 (by rfl) ⟨3812153, by rfl⟩ : syracuseStep 5082871 = 7624307) B7624307
theorem B6777161 : Blo 2007435 6777161 := bstep (se 2 (by rfl) ⟨2541435, by rfl⟩ : syracuseStep 6777161 = 5082871) B5082871
theorem B4518107 : Blo 2007435 4518107 := bstep (se 1 (by rfl) ⟨3388580, by rfl⟩ : syracuseStep 4518107 = 6777161) B6777161
theorem B3012071 : Blo 2007435 3012071 := bstep (se 1 (by rfl) ⟨2259053, by rfl⟩ : syracuseStep 3012071 = 4518107) B4518107
theorem B2008047 : Blo 2007435 2008047 := bstep (se 1 (by rfl) ⟨1506035, by rfl⟩ : syracuseStep 2008047 = 3012071) B3012071
theorem B3012077 : Blo 2007435 3012077 := bbase (se 3 (by rfl) ⟨564764, by rfl⟩ : syracuseStep 3012077 = 1129529) (by norm_num)
theorem B2008051 : Blo 2007435 2008051 := bstep (se 1 (by rfl) ⟨1506038, by rfl⟩ : syracuseStep 2008051 = 3012077) B3012077
theorem B4518125 : Blo 2007435 4518125 := bbase (se 3 (by rfl) ⟨847148, by rfl⟩ : syracuseStep 4518125 = 1694297) (by norm_num)
theorem B3012083 : Blo 2007435 3012083 := bstep (se 1 (by rfl) ⟨2259062, by rfl⟩ : syracuseStep 3012083 = 4518125) B4518125
theorem B2008055 : Blo 2007435 2008055 := bstep (se 1 (by rfl) ⟨1506041, by rfl⟩ : syracuseStep 2008055 = 3012083) B3012083
theorem B2859133 : Blo 2007435 2859133 := bbase (se 3 (by rfl) ⟨536087, by rfl⟩ : syracuseStep 2859133 = 1072175) (by norm_num)
theorem B3812177 : Blo 2007435 3812177 := bstep (se 2 (by rfl) ⟨1429566, by rfl⟩ : syracuseStep 3812177 = 2859133) B2859133
theorem B2541451 : Blo 2007435 2541451 := bstep (se 1 (by rfl) ⟨1906088, by rfl⟩ : syracuseStep 2541451 = 3812177) B3812177
theorem B3388601 : Blo 2007435 3388601 := bstep (se 2 (by rfl) ⟨1270725, by rfl⟩ : syracuseStep 3388601 = 2541451) B2541451
theorem B2259067 : Blo 2007435 2259067 := bstep (se 1 (by rfl) ⟨1694300, by rfl⟩ : syracuseStep 2259067 = 3388601) B3388601
theorem B3012089 : Blo 2007435 3012089 := bstep (se 2 (by rfl) ⟨1129533, by rfl⟩ : syracuseStep 3012089 = 2259067) B2259067
theorem B2008059 : Blo 2007435 2008059 := bstep (se 1 (by rfl) ⟨1506044, by rfl⟩ : syracuseStep 2008059 = 3012089) B3012089
theorem B5152261 : Blo 2007435 5152261 := bbase (se 4 (by rfl) ⟨483024, by rfl⟩ : syracuseStep 5152261 = 966049) (by norm_num)
theorem B6869681 : Blo 2007435 6869681 := bstep (se 2 (by rfl) ⟨2576130, by rfl⟩ : syracuseStep 6869681 = 5152261) B5152261
theorem B4579787 : Blo 2007435 4579787 := bstep (se 1 (by rfl) ⟨3434840, by rfl⟩ : syracuseStep 4579787 = 6869681) B6869681
theorem B12212765 : Blo 2007435 12212765 := bstep (se 3 (by rfl) ⟨2289893, by rfl⟩ : syracuseStep 12212765 = 4579787) B4579787
theorem B8141843 : Blo 2007435 8141843 := bstep (se 1 (by rfl) ⟨6106382, by rfl⟩ : syracuseStep 8141843 = 12212765) B12212765
theorem B5427895 : Blo 2007435 5427895 := bstep (se 1 (by rfl) ⟨4070921, by rfl⟩ : syracuseStep 5427895 = 8141843) B8141843
theorem B7237193 : Blo 2007435 7237193 := bstep (se 2 (by rfl) ⟨2713947, by rfl⟩ : syracuseStep 7237193 = 5427895) B5427895
theorem B77196725 : Blo 2007435 77196725 := bstep (se 5 (by rfl) ⟨3618596, by rfl⟩ : syracuseStep 77196725 = 7237193) B7237193
theorem B51464483 : Blo 2007435 51464483 := bstep (se 1 (by rfl) ⟨38598362, by rfl⟩ : syracuseStep 51464483 = 77196725) B77196725
theorem B34309655 : Blo 2007435 34309655 := bstep (se 1 (by rfl) ⟨25732241, by rfl⟩ : syracuseStep 34309655 = 51464483) B51464483
theorem B22873103 : Blo 2007435 22873103 := bstep (se 1 (by rfl) ⟨17154827, by rfl⟩ : syracuseStep 22873103 = 34309655) B34309655
theorem B15248735 : Blo 2007435 15248735 := bstep (se 1 (by rfl) ⟨11436551, by rfl⟩ : syracuseStep 15248735 = 22873103) B22873103
theorem B10165823 : Blo 2007435 10165823 := bstep (se 1 (by rfl) ⟨7624367, by rfl⟩ : syracuseStep 10165823 = 15248735) B15248735
theorem B6777215 : Blo 2007435 6777215 := bstep (se 1 (by rfl) ⟨5082911, by rfl⟩ : syracuseStep 6777215 = 10165823) B10165823
theorem B4518143 : Blo 2007435 4518143 := bstep (se 1 (by rfl) ⟨3388607, by rfl⟩ : syracuseStep 4518143 = 6777215) B6777215
theorem B3012095 : Blo 2007435 3012095 := bstep (se 1 (by rfl) ⟨2259071, by rfl⟩ : syracuseStep 3012095 = 4518143) B4518143
theorem B2008063 : Blo 2007435 2008063 := bstep (se 1 (by rfl) ⟨1506047, by rfl⟩ : syracuseStep 2008063 = 3012095) B3012095
theorem B3012101 : Blo 2007435 3012101 := bbase (se 4 (by rfl) ⟨282384, by rfl⟩ : syracuseStep 3012101 = 564769) (by norm_num)
theorem B2008067 : Blo 2007435 2008067 := bstep (se 1 (by rfl) ⟨1506050, by rfl⟩ : syracuseStep 2008067 = 3012101) B3012101
theorem B3388621 : Blo 2007435 3388621 := bbase (se 3 (by rfl) ⟨635366, by rfl⟩ : syracuseStep 3388621 = 1270733) (by norm_num)
theorem B4518161 : Blo 2007435 4518161 := bstep (se 2 (by rfl) ⟨1694310, by rfl⟩ : syracuseStep 4518161 = 3388621) B3388621
theorem B3012107 : Blo 2007435 3012107 := bstep (se 1 (by rfl) ⟨2259080, by rfl⟩ : syracuseStep 3012107 = 4518161) B4518161
theorem B2008071 : Blo 2007435 2008071 := bstep (se 1 (by rfl) ⟨1506053, by rfl⟩ : syracuseStep 2008071 = 3012107) B3012107
theorem B2259085 : Blo 2007435 2259085 := bbase (se 3 (by rfl) ⟨423578, by rfl⟩ : syracuseStep 2259085 = 847157) (by norm_num)
theorem B3012113 : Blo 2007435 3012113 := bstep (se 2 (by rfl) ⟨1129542, by rfl⟩ : syracuseStep 3012113 = 2259085) B2259085
theorem B2008075 : Blo 2007435 2008075 := bstep (se 1 (by rfl) ⟨1506056, by rfl⟩ : syracuseStep 2008075 = 3012113) B3012113
theorem B6777269 : Blo 2007435 6777269 := bbase (se 5 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 6777269 = 635369) (by norm_num)
theorem B4518179 : Blo 2007435 4518179 := bstep (se 1 (by rfl) ⟨3388634, by rfl⟩ : syracuseStep 4518179 = 6777269) B6777269
theorem B3012119 : Blo 2007435 3012119 := bstep (se 1 (by rfl) ⟨2259089, by rfl⟩ : syracuseStep 3012119 = 4518179) B4518179
theorem B2008079 : Blo 2007435 2008079 := bstep (se 1 (by rfl) ⟨1506059, by rfl⟩ : syracuseStep 2008079 = 3012119) B3012119
theorem B3012125 : Blo 2007435 3012125 := bbase (se 3 (by rfl) ⟨564773, by rfl⟩ : syracuseStep 3012125 = 1129547) (by norm_num)
theorem B2008083 : Blo 2007435 2008083 := bstep (se 1 (by rfl) ⟨1506062, by rfl⟩ : syracuseStep 2008083 = 3012125) B3012125
theorem B4518197 : Blo 2007435 4518197 := bbase (se 5 (by rfl) ⟨211790, by rfl⟩ : syracuseStep 4518197 = 423581) (by norm_num)
theorem B3012131 : Blo 2007435 3012131 := bstep (se 1 (by rfl) ⟨2259098, by rfl⟩ : syracuseStep 3012131 = 4518197) B4518197
theorem B2008087 : Blo 2007435 2008087 := bstep (se 1 (by rfl) ⟨1506065, by rfl⟩ : syracuseStep 2008087 = 3012131) B3012131
theorem B7336037 : Blo 2007435 7336037 := bbase (se 4 (by rfl) ⟨687753, by rfl⟩ : syracuseStep 7336037 = 1375507) (by norm_num)
theorem B4890691 : Blo 2007435 4890691 := bstep (se 1 (by rfl) ⟨3668018, by rfl⟩ : syracuseStep 4890691 = 7336037) B7336037
theorem B26083685 : Blo 2007435 26083685 := bstep (se 4 (by rfl) ⟨2445345, by rfl⟩ : syracuseStep 26083685 = 4890691) B4890691
theorem B69556493 : Blo 2007435 69556493 := bstep (se 3 (by rfl) ⟨13041842, by rfl⟩ : syracuseStep 69556493 = 26083685) B26083685
theorem B185483981 : Blo 2007435 185483981 := bstep (se 3 (by rfl) ⟨34778246, by rfl⟩ : syracuseStep 185483981 = 69556493) B69556493
theorem B123655987 : Blo 2007435 123655987 := bstep (se 1 (by rfl) ⟨92741990, by rfl⟩ : syracuseStep 123655987 = 185483981) B185483981
theorem B164874649 : Blo 2007435 164874649 := bstep (se 2 (by rfl) ⟨61827993, by rfl⟩ : syracuseStep 164874649 = 123655987) B123655987
theorem B219832865 : Blo 2007435 219832865 := bstep (se 2 (by rfl) ⟨82437324, by rfl⟩ : syracuseStep 219832865 = 164874649) B164874649
theorem B146555243 : Blo 2007435 146555243 := bstep (se 1 (by rfl) ⟨109916432, by rfl⟩ : syracuseStep 146555243 = 219832865) B219832865
theorem B97703495 : Blo 2007435 97703495 := bstep (se 1 (by rfl) ⟨73277621, by rfl⟩ : syracuseStep 97703495 = 146555243) B146555243
theorem B65135663 : Blo 2007435 65135663 := bstep (se 1 (by rfl) ⟨48851747, by rfl⟩ : syracuseStep 65135663 = 97703495) B97703495
theorem B43423775 : Blo 2007435 43423775 := bstep (se 1 (by rfl) ⟨32567831, by rfl⟩ : syracuseStep 43423775 = 65135663) B65135663
theorem B28949183 : Blo 2007435 28949183 := bstep (se 1 (by rfl) ⟨21711887, by rfl⟩ : syracuseStep 28949183 = 43423775) B43423775
theorem B19299455 : Blo 2007435 19299455 := bstep (se 1 (by rfl) ⟨14474591, by rfl⟩ : syracuseStep 19299455 = 28949183) B28949183
theorem B12866303 : Blo 2007435 12866303 := bstep (se 1 (by rfl) ⟨9649727, by rfl⟩ : syracuseStep 12866303 = 19299455) B19299455
theorem B8577535 : Blo 2007435 8577535 := bstep (se 1 (by rfl) ⟨6433151, by rfl⟩ : syracuseStep 8577535 = 12866303) B12866303
theorem B11436713 : Blo 2007435 11436713 := bstep (se 2 (by rfl) ⟨4288767, by rfl⟩ : syracuseStep 11436713 = 8577535) B8577535
theorem B7624475 : Blo 2007435 7624475 := bstep (se 1 (by rfl) ⟨5718356, by rfl⟩ : syracuseStep 7624475 = 11436713) B11436713
theorem B5082983 : Blo 2007435 5082983 := bstep (se 1 (by rfl) ⟨3812237, by rfl⟩ : syracuseStep 5082983 = 7624475) B7624475
theorem B3388655 : Blo 2007435 3388655 := bstep (se 1 (by rfl) ⟨2541491, by rfl⟩ : syracuseStep 3388655 = 5082983) B5082983
theorem B2259103 : Blo 2007435 2259103 := bstep (se 1 (by rfl) ⟨1694327, by rfl⟩ : syracuseStep 2259103 = 3388655) B3388655
theorem B3012137 : Blo 2007435 3012137 := bstep (se 2 (by rfl) ⟨1129551, by rfl⟩ : syracuseStep 3012137 = 2259103) B2259103
theorem B2008091 : Blo 2007435 2008091 := bstep (se 1 (by rfl) ⟨1506068, by rfl⟩ : syracuseStep 2008091 = 3012137) B3012137
theorem B4579861 : Blo 2007435 4579861 := bbase (se 6 (by rfl) ⟨107340, by rfl⟩ : syracuseStep 4579861 = 214681) (by norm_num)
theorem B6106481 : Blo 2007435 6106481 := bstep (se 2 (by rfl) ⟨2289930, by rfl⟩ : syracuseStep 6106481 = 4579861) B4579861
theorem B4070987 : Blo 2007435 4070987 := bstep (se 1 (by rfl) ⟨3053240, by rfl⟩ : syracuseStep 4070987 = 6106481) B6106481
theorem B2713991 : Blo 2007435 2713991 := bstep (se 1 (by rfl) ⟨2035493, by rfl⟩ : syracuseStep 2713991 = 4070987) B4070987
theorem B28949237 : Blo 2007435 28949237 := bstep (se 5 (by rfl) ⟨1356995, by rfl⟩ : syracuseStep 28949237 = 2713991) B2713991
theorem B19299491 : Blo 2007435 19299491 := bstep (se 1 (by rfl) ⟨14474618, by rfl⟩ : syracuseStep 19299491 = 28949237) B28949237
theorem B12866327 : Blo 2007435 12866327 := bstep (se 1 (by rfl) ⟨9649745, by rfl⟩ : syracuseStep 12866327 = 19299491) B19299491
theorem B8577551 : Blo 2007435 8577551 := bstep (se 1 (by rfl) ⟨6433163, by rfl⟩ : syracuseStep 8577551 = 12866327) B12866327
theorem B5718367 : Blo 2007435 5718367 := bstep (se 1 (by rfl) ⟨4288775, by rfl⟩ : syracuseStep 5718367 = 8577551) B8577551
theorem B7624489 : Blo 2007435 7624489 := bstep (se 2 (by rfl) ⟨2859183, by rfl⟩ : syracuseStep 7624489 = 5718367) B5718367
theorem B10165985 : Blo 2007435 10165985 := bstep (se 2 (by rfl) ⟨3812244, by rfl⟩ : syracuseStep 10165985 = 7624489) B7624489
theorem B6777323 : Blo 2007435 6777323 := bstep (se 1 (by rfl) ⟨5082992, by rfl⟩ : syracuseStep 6777323 = 10165985) B10165985
theorem B4518215 : Blo 2007435 4518215 := bstep (se 1 (by rfl) ⟨3388661, by rfl⟩ : syracuseStep 4518215 = 6777323) B6777323
theorem B3012143 : Blo 2007435 3012143 := bstep (se 1 (by rfl) ⟨2259107, by rfl⟩ : syracuseStep 3012143 = 4518215) B4518215
theorem B2008095 : Blo 2007435 2008095 := bstep (se 1 (by rfl) ⟨1506071, by rfl⟩ : syracuseStep 2008095 = 3012143) B3012143
theorem B3012149 : Blo 2007435 3012149 := bbase (se 5 (by rfl) ⟨141194, by rfl⟩ : syracuseStep 3012149 = 282389) (by norm_num)
theorem B2008099 : Blo 2007435 2008099 := bstep (se 1 (by rfl) ⟨1506074, by rfl⟩ : syracuseStep 2008099 = 3012149) B3012149
theorem B5083013 : Blo 2007435 5083013 := bbase (se 4 (by rfl) ⟨476532, by rfl⟩ : syracuseStep 5083013 = 953065) (by norm_num)
theorem B3388675 : Blo 2007435 3388675 := bstep (se 1 (by rfl) ⟨2541506, by rfl⟩ : syracuseStep 3388675 = 5083013) B5083013
theorem B4518233 : Blo 2007435 4518233 := bstep (se 2 (by rfl) ⟨1694337, by rfl⟩ : syracuseStep 4518233 = 3388675) B3388675
theorem B3012155 : Blo 2007435 3012155 := bstep (se 1 (by rfl) ⟨2259116, by rfl⟩ : syracuseStep 3012155 = 4518233) B4518233
theorem B2008103 : Blo 2007435 2008103 := bstep (se 1 (by rfl) ⟨1506077, by rfl⟩ : syracuseStep 2008103 = 3012155) B3012155
theorem B2259121 : Blo 2007435 2259121 := bbase (se 2 (by rfl) ⟨847170, by rfl⟩ : syracuseStep 2259121 = 1694341) (by norm_num)
theorem B3012161 : Blo 2007435 3012161 := bstep (se 2 (by rfl) ⟨1129560, by rfl⟩ : syracuseStep 3012161 = 2259121) B2259121
theorem B2008107 : Blo 2007435 2008107 := bstep (se 1 (by rfl) ⟨1506080, by rfl⟩ : syracuseStep 2008107 = 3012161) B3012161
theorem B2144405 : Blo 2007435 2144405 := bbase (se 6 (by rfl) ⟨50259, by rfl⟩ : syracuseStep 2144405 = 100519) (by norm_num)
theorem B5718413 : Blo 2007435 5718413 := bstep (se 3 (by rfl) ⟨1072202, by rfl⟩ : syracuseStep 5718413 = 2144405) B2144405
theorem B3812275 : Blo 2007435 3812275 := bstep (se 1 (by rfl) ⟨2859206, by rfl⟩ : syracuseStep 3812275 = 5718413) B5718413
theorem B5083033 : Blo 2007435 5083033 := bstep (se 2 (by rfl) ⟨1906137, by rfl⟩ : syracuseStep 5083033 = 3812275) B3812275
theorem B6777377 : Blo 2007435 6777377 := bstep (se 2 (by rfl) ⟨2541516, by rfl⟩ : syracuseStep 6777377 = 5083033) B5083033
theorem B4518251 : Blo 2007435 4518251 := bstep (se 1 (by rfl) ⟨3388688, by rfl⟩ : syracuseStep 4518251 = 6777377) B6777377
theorem B3012167 : Blo 2007435 3012167 := bstep (se 1 (by rfl) ⟨2259125, by rfl⟩ : syracuseStep 3012167 = 4518251) B4518251
theorem B2008111 : Blo 2007435 2008111 := bstep (se 1 (by rfl) ⟨1506083, by rfl⟩ : syracuseStep 2008111 = 3012167) B3012167
theorem B3012173 : Blo 2007435 3012173 := bbase (se 3 (by rfl) ⟨564782, by rfl⟩ : syracuseStep 3012173 = 1129565) (by norm_num)
theorem B2008115 : Blo 2007435 2008115 := bstep (se 1 (by rfl) ⟨1506086, by rfl⟩ : syracuseStep 2008115 = 3012173) B3012173
theorem B4518269 : Blo 2007435 4518269 := bbase (se 3 (by rfl) ⟨847175, by rfl⟩ : syracuseStep 4518269 = 1694351) (by norm_num)
theorem B3012179 : Blo 2007435 3012179 := bstep (se 1 (by rfl) ⟨2259134, by rfl⟩ : syracuseStep 3012179 = 4518269) B4518269
theorem B2008119 : Blo 2007435 2008119 := bstep (se 1 (by rfl) ⟨1506089, by rfl⟩ : syracuseStep 2008119 = 3012179) B3012179
theorem B3388709 : Blo 2007435 3388709 := bbase (se 4 (by rfl) ⟨317691, by rfl⟩ : syracuseStep 3388709 = 635383) (by norm_num)
theorem B2259139 : Blo 2007435 2259139 := bstep (se 1 (by rfl) ⟨1694354, by rfl⟩ : syracuseStep 2259139 = 3388709) B3388709
theorem B3012185 : Blo 2007435 3012185 := bstep (se 2 (by rfl) ⟨1129569, by rfl⟩ : syracuseStep 3012185 = 2259139) B2259139
theorem B2008123 : Blo 2007435 2008123 := bstep (se 1 (by rfl) ⟨1506092, by rfl⟩ : syracuseStep 2008123 = 3012185) B3012185
theorem B2859229 : Blo 2007435 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B15249221 : Blo 2007435 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B10166147 : Blo 2007435 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B6777431 : Blo 2007435 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B4518287 : Blo 2007435 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B3012191 : Blo 2007435 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B2008127 : Blo 2007435 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B3012197 : Blo 2007435 3012197 := bbase (se 4 (by rfl) ⟨282393, by rfl⟩ : syracuseStep 3012197 = 564787) (by norm_num)
theorem B2008131 : Blo 2007435 2008131 := bstep (se 1 (by rfl) ⟨1506098, by rfl⟩ : syracuseStep 2008131 = 3012197) B3012197
theorem B2576225 : Blo 2007435 2576225 := bbase (se 2 (by rfl) ⟨966084, by rfl⟩ : syracuseStep 2576225 = 1932169) (by norm_num)
theorem B6869933 : Blo 2007435 6869933 := bstep (se 3 (by rfl) ⟨1288112, by rfl⟩ : syracuseStep 6869933 = 2576225) B2576225
theorem B4579955 : Blo 2007435 4579955 := bstep (se 1 (by rfl) ⟨3434966, by rfl⟩ : syracuseStep 4579955 = 6869933) B6869933
theorem B3053303 : Blo 2007435 3053303 := bstep (se 1 (by rfl) ⟨2289977, by rfl⟩ : syracuseStep 3053303 = 4579955) B4579955
theorem B2035535 : Blo 2007435 2035535 := bstep (se 1 (by rfl) ⟨1526651, by rfl⟩ : syracuseStep 2035535 = 3053303) B3053303
theorem B5428093 : Blo 2007435 5428093 := bstep (se 3 (by rfl) ⟨1017767, by rfl⟩ : syracuseStep 5428093 = 2035535) B2035535
theorem B7237457 : Blo 2007435 7237457 := bstep (se 2 (by rfl) ⟨2714046, by rfl⟩ : syracuseStep 7237457 = 5428093) B5428093
theorem B4824971 : Blo 2007435 4824971 := bstep (se 1 (by rfl) ⟨3618728, by rfl⟩ : syracuseStep 4824971 = 7237457) B7237457
theorem B3216647 : Blo 2007435 3216647 := bstep (se 1 (by rfl) ⟨2412485, by rfl⟩ : syracuseStep 3216647 = 4824971) B4824971
theorem B2144431 : Blo 2007435 2144431 := bstep (se 1 (by rfl) ⟨1608323, by rfl⟩ : syracuseStep 2144431 = 3216647) B3216647
theorem B2859241 : Blo 2007435 2859241 := bstep (se 2 (by rfl) ⟨1072215, by rfl⟩ : syracuseStep 2859241 = 2144431) B2144431
theorem B3812321 : Blo 2007435 3812321 := bstep (se 2 (by rfl) ⟨1429620, by rfl⟩ : syracuseStep 3812321 = 2859241) B2859241
theorem B2541547 : Blo 2007435 2541547 := bstep (se 1 (by rfl) ⟨1906160, by rfl⟩ : syracuseStep 2541547 = 3812321) B3812321
theorem B3388729 : Blo 2007435 3388729 := bstep (se 2 (by rfl) ⟨1270773, by rfl⟩ : syracuseStep 3388729 = 2541547) B2541547
theorem B4518305 : Blo 2007435 4518305 := bstep (se 2 (by rfl) ⟨1694364, by rfl⟩ : syracuseStep 4518305 = 3388729) B3388729
theorem B3012203 : Blo 2007435 3012203 := bstep (se 1 (by rfl) ⟨2259152, by rfl⟩ : syracuseStep 3012203 = 4518305) B4518305
theorem B2008135 : Blo 2007435 2008135 := bstep (se 1 (by rfl) ⟨1506101, by rfl⟩ : syracuseStep 2008135 = 3012203) B3012203
theorem B2259157 : Blo 2007435 2259157 := bbase (se 7 (by rfl) ⟨26474, by rfl⟩ : syracuseStep 2259157 = 52949) (by norm_num)
theorem B3012209 : Blo 2007435 3012209 := bstep (se 2 (by rfl) ⟨1129578, by rfl⟩ : syracuseStep 3012209 = 2259157) B2259157
theorem B2008139 : Blo 2007435 2008139 := bstep (se 1 (by rfl) ⟨1506104, by rfl⟩ : syracuseStep 2008139 = 3012209) B3012209
theorem B2541557 : Blo 2007435 2541557 := bbase (se 5 (by rfl) ⟨119135, by rfl⟩ : syracuseStep 2541557 = 238271) (by norm_num)
theorem B6777485 : Blo 2007435 6777485 := bstep (se 3 (by rfl) ⟨1270778, by rfl⟩ : syracuseStep 6777485 = 2541557) B2541557
theorem B4518323 : Blo 2007435 4518323 := bstep (se 1 (by rfl) ⟨3388742, by rfl⟩ : syracuseStep 4518323 = 6777485) B6777485
theorem B3012215 : Blo 2007435 3012215 := bstep (se 1 (by rfl) ⟨2259161, by rfl⟩ : syracuseStep 3012215 = 4518323) B4518323
theorem B2008143 : Blo 2007435 2008143 := bstep (se 1 (by rfl) ⟨1506107, by rfl⟩ : syracuseStep 2008143 = 3012215) B3012215
theorem B3012221 : Blo 2007435 3012221 := bbase (se 3 (by rfl) ⟨564791, by rfl⟩ : syracuseStep 3012221 = 1129583) (by norm_num)
theorem B2008147 : Blo 2007435 2008147 := bstep (se 1 (by rfl) ⟨1506110, by rfl⟩ : syracuseStep 2008147 = 3012221) B3012221
theorem B4518341 : Blo 2007435 4518341 := bbase (se 4 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 4518341 = 847189) (by norm_num)
theorem B3012227 : Blo 2007435 3012227 := bstep (se 1 (by rfl) ⟨2259170, by rfl⟩ : syracuseStep 3012227 = 4518341) B4518341
theorem B2008151 : Blo 2007435 2008151 := bstep (se 1 (by rfl) ⟨1506113, by rfl⟩ : syracuseStep 2008151 = 3012227) B3012227
theorem B2412509 : Blo 2007435 2412509 := bbase (se 3 (by rfl) ⟨452345, by rfl⟩ : syracuseStep 2412509 = 904691) (by norm_num)
theorem B6433357 : Blo 2007435 6433357 := bstep (se 3 (by rfl) ⟨1206254, by rfl⟩ : syracuseStep 6433357 = 2412509) B2412509
theorem B8577809 : Blo 2007435 8577809 := bstep (se 2 (by rfl) ⟨3216678, by rfl⟩ : syracuseStep 8577809 = 6433357) B6433357
theorem B5718539 : Blo 2007435 5718539 := bstep (se 1 (by rfl) ⟨4288904, by rfl⟩ : syracuseStep 5718539 = 8577809) B8577809
theorem B3812359 : Blo 2007435 3812359 := bstep (se 1 (by rfl) ⟨2859269, by rfl⟩ : syracuseStep 3812359 = 5718539) B5718539
theorem B5083145 : Blo 2007435 5083145 := bstep (se 2 (by rfl) ⟨1906179, by rfl⟩ : syracuseStep 5083145 = 3812359) B3812359
theorem B3388763 : Blo 2007435 3388763 := bstep (se 1 (by rfl) ⟨2541572, by rfl⟩ : syracuseStep 3388763 = 5083145) B5083145
theorem B2259175 : Blo 2007435 2259175 := bstep (se 1 (by rfl) ⟨1694381, by rfl⟩ : syracuseStep 2259175 = 3388763) B3388763
theorem B3012233 : Blo 2007435 3012233 := bstep (se 2 (by rfl) ⟨1129587, by rfl⟩ : syracuseStep 3012233 = 2259175) B2259175
theorem B2008155 : Blo 2007435 2008155 := bstep (se 1 (by rfl) ⟨1506116, by rfl⟩ : syracuseStep 2008155 = 3012233) B3012233
theorem B10166309 : Blo 2007435 10166309 := bbase (se 4 (by rfl) ⟨953091, by rfl⟩ : syracuseStep 10166309 = 1906183) (by norm_num)
theorem B6777539 : Blo 2007435 6777539 := bstep (se 1 (by rfl) ⟨5083154, by rfl⟩ : syracuseStep 6777539 = 10166309) B10166309
theorem B4518359 : Blo 2007435 4518359 := bstep (se 1 (by rfl) ⟨3388769, by rfl⟩ : syracuseStep 4518359 = 6777539) B6777539
theorem B3012239 : Blo 2007435 3012239 := bstep (se 1 (by rfl) ⟨2259179, by rfl⟩ : syracuseStep 3012239 = 4518359) B4518359
theorem B2008159 : Blo 2007435 2008159 := bstep (se 1 (by rfl) ⟨1506119, by rfl⟩ : syracuseStep 2008159 = 3012239) B3012239
theorem B3012245 : Blo 2007435 3012245 := bbase (se 6 (by rfl) ⟨70599, by rfl⟩ : syracuseStep 3012245 = 141199) (by norm_num)
theorem B2008163 : Blo 2007435 2008163 := bstep (se 1 (by rfl) ⟨1506122, by rfl⟩ : syracuseStep 2008163 = 3012245) B3012245
theorem B2063341 : Blo 2007435 2063341 := bbase (se 3 (by rfl) ⟨386876, by rfl⟩ : syracuseStep 2063341 = 773753) (by norm_num)
theorem B2751121 : Blo 2007435 2751121 := bstep (se 2 (by rfl) ⟨1031670, by rfl⟩ : syracuseStep 2751121 = 2063341) B2063341
theorem B3668161 : Blo 2007435 3668161 := bstep (se 2 (by rfl) ⟨1375560, by rfl⟩ : syracuseStep 3668161 = 2751121) B2751121
theorem B4890881 : Blo 2007435 4890881 := bstep (se 2 (by rfl) ⟨1834080, by rfl⟩ : syracuseStep 4890881 = 3668161) B3668161
theorem B3260587 : Blo 2007435 3260587 := bstep (se 1 (by rfl) ⟨2445440, by rfl⟩ : syracuseStep 3260587 = 4890881) B4890881
theorem B4347449 : Blo 2007435 4347449 := bstep (se 2 (by rfl) ⟨1630293, by rfl⟩ : syracuseStep 4347449 = 3260587) B3260587
theorem B2898299 : Blo 2007435 2898299 := bstep (se 1 (by rfl) ⟨2173724, by rfl⟩ : syracuseStep 2898299 = 4347449) B4347449
theorem B7728797 : Blo 2007435 7728797 := bstep (se 3 (by rfl) ⟨1449149, by rfl⟩ : syracuseStep 7728797 = 2898299) B2898299
theorem B5152531 : Blo 2007435 5152531 := bstep (se 1 (by rfl) ⟨3864398, by rfl⟩ : syracuseStep 5152531 = 7728797) B7728797
theorem B6870041 : Blo 2007435 6870041 := bstep (se 2 (by rfl) ⟨2576265, by rfl⟩ : syracuseStep 6870041 = 5152531) B5152531
theorem B4580027 : Blo 2007435 4580027 := bstep (se 1 (by rfl) ⟨3435020, by rfl⟩ : syracuseStep 4580027 = 6870041) B6870041
theorem B3053351 : Blo 2007435 3053351 := bstep (se 1 (by rfl) ⟨2290013, by rfl⟩ : syracuseStep 3053351 = 4580027) B4580027
theorem B2035567 : Blo 2007435 2035567 := bstep (se 1 (by rfl) ⟨1526675, by rfl⟩ : syracuseStep 2035567 = 3053351) B3053351
theorem B2714089 : Blo 2007435 2714089 := bstep (se 2 (by rfl) ⟨1017783, by rfl⟩ : syracuseStep 2714089 = 2035567) B2035567
theorem B3618785 : Blo 2007435 3618785 := bstep (se 2 (by rfl) ⟨1357044, by rfl⟩ : syracuseStep 3618785 = 2714089) B2714089
theorem B2412523 : Blo 2007435 2412523 := bstep (se 1 (by rfl) ⟨1809392, by rfl⟩ : syracuseStep 2412523 = 3618785) B3618785
theorem B12866789 : Blo 2007435 12866789 := bstep (se 4 (by rfl) ⟨1206261, by rfl⟩ : syracuseStep 12866789 = 2412523) B2412523
theorem B8577859 : Blo 2007435 8577859 := bstep (se 1 (by rfl) ⟨6433394, by rfl⟩ : syracuseStep 8577859 = 12866789) B12866789
theorem B11437145 : Blo 2007435 11437145 := bstep (se 2 (by rfl) ⟨4288929, by rfl⟩ : syracuseStep 11437145 = 8577859) B8577859
theorem B7624763 : Blo 2007435 7624763 := bstep (se 1 (by rfl) ⟨5718572, by rfl⟩ : syracuseStep 7624763 = 11437145) B11437145
theorem B5083175 : Blo 2007435 5083175 := bstep (se 1 (by rfl) ⟨3812381, by rfl⟩ : syracuseStep 5083175 = 7624763) B7624763
theorem B3388783 : Blo 2007435 3388783 := bstep (se 1 (by rfl) ⟨2541587, by rfl⟩ : syracuseStep 3388783 = 5083175) B5083175
theorem B4518377 : Blo 2007435 4518377 := bstep (se 2 (by rfl) ⟨1694391, by rfl⟩ : syracuseStep 4518377 = 3388783) B3388783
theorem B3012251 : Blo 2007435 3012251 := bstep (se 1 (by rfl) ⟨2259188, by rfl⟩ : syracuseStep 3012251 = 4518377) B4518377
theorem B2008167 : Blo 2007435 2008167 := bstep (se 1 (by rfl) ⟨1506125, by rfl⟩ : syracuseStep 2008167 = 3012251) B3012251
theorem B2259193 : Blo 2007435 2259193 := bbase (se 2 (by rfl) ⟨847197, by rfl⟩ : syracuseStep 2259193 = 1694395) (by norm_num)
theorem B3012257 : Blo 2007435 3012257 := bstep (se 2 (by rfl) ⟨1129596, by rfl⟩ : syracuseStep 3012257 = 2259193) B2259193
theorem B2008171 : Blo 2007435 2008171 := bstep (se 1 (by rfl) ⟨1506128, by rfl⟩ : syracuseStep 2008171 = 3012257) B3012257
theorem B8577893 : Blo 2007435 8577893 := bbase (se 4 (by rfl) ⟨804177, by rfl⟩ : syracuseStep 8577893 = 1608355) (by norm_num)
theorem B5718595 : Blo 2007435 5718595 := bstep (se 1 (by rfl) ⟨4288946, by rfl⟩ : syracuseStep 5718595 = 8577893) B8577893
theorem B7624793 : Blo 2007435 7624793 := bstep (se 2 (by rfl) ⟨2859297, by rfl⟩ : syracuseStep 7624793 = 5718595) B5718595
theorem B5083195 : Blo 2007435 5083195 := bstep (se 1 (by rfl) ⟨3812396, by rfl⟩ : syracuseStep 5083195 = 7624793) B7624793
theorem B6777593 : Blo 2007435 6777593 := bstep (se 2 (by rfl) ⟨2541597, by rfl⟩ : syracuseStep 6777593 = 5083195) B5083195
theorem B4518395 : Blo 2007435 4518395 := bstep (se 1 (by rfl) ⟨3388796, by rfl⟩ : syracuseStep 4518395 = 6777593) B6777593
theorem B3012263 : Blo 2007435 3012263 := bstep (se 1 (by rfl) ⟨2259197, by rfl⟩ : syracuseStep 3012263 = 4518395) B4518395
theorem B2008175 : Blo 2007435 2008175 := bstep (se 1 (by rfl) ⟨1506131, by rfl⟩ : syracuseStep 2008175 = 3012263) B3012263
theorem B3012269 : Blo 2007435 3012269 := bbase (se 3 (by rfl) ⟨564800, by rfl⟩ : syracuseStep 3012269 = 1129601) (by norm_num)
theorem B2008179 : Blo 2007435 2008179 := bstep (se 1 (by rfl) ⟨1506134, by rfl⟩ : syracuseStep 2008179 = 3012269) B3012269
theorem B4518413 : Blo 2007435 4518413 := bbase (se 3 (by rfl) ⟨847202, by rfl⟩ : syracuseStep 4518413 = 1694405) (by norm_num)
theorem B3012275 : Blo 2007435 3012275 := bstep (se 1 (by rfl) ⟨2259206, by rfl⟩ : syracuseStep 3012275 = 4518413) B4518413
theorem B2008183 : Blo 2007435 2008183 := bstep (se 1 (by rfl) ⟨1506137, by rfl⟩ : syracuseStep 2008183 = 3012275) B3012275
theorem B2541613 : Blo 2007435 2541613 := bbase (se 3 (by rfl) ⟨476552, by rfl⟩ : syracuseStep 2541613 = 953105) (by norm_num)
theorem B3388817 : Blo 2007435 3388817 := bstep (se 2 (by rfl) ⟨1270806, by rfl⟩ : syracuseStep 3388817 = 2541613) B2541613
theorem B2259211 : Blo 2007435 2259211 := bstep (se 1 (by rfl) ⟨1694408, by rfl⟩ : syracuseStep 2259211 = 3388817) B3388817
theorem B3012281 : Blo 2007435 3012281 := bstep (se 2 (by rfl) ⟨1129605, by rfl⟩ : syracuseStep 3012281 = 2259211) B2259211
theorem B2008187 : Blo 2007435 2008187 := bstep (se 1 (by rfl) ⟨1506140, by rfl⟩ : syracuseStep 2008187 = 3012281) B3012281
theorem B16284725 : Blo 2007435 16284725 := bbase (se 5 (by rfl) ⟨763346, by rfl⟩ : syracuseStep 16284725 = 1526693) (by norm_num)
theorem B10856483 : Blo 2007435 10856483 := bstep (se 1 (by rfl) ⟨8142362, by rfl⟩ : syracuseStep 10856483 = 16284725) B16284725
theorem B7237655 : Blo 2007435 7237655 := bstep (se 1 (by rfl) ⟨5428241, by rfl⟩ : syracuseStep 7237655 = 10856483) B10856483
theorem B4825103 : Blo 2007435 4825103 := bstep (se 1 (by rfl) ⟨3618827, by rfl⟩ : syracuseStep 4825103 = 7237655) B7237655
theorem B12866941 : Blo 2007435 12866941 := bstep (se 3 (by rfl) ⟨2412551, by rfl⟩ : syracuseStep 12866941 = 4825103) B4825103
theorem B17155921 : Blo 2007435 17155921 := bstep (se 2 (by rfl) ⟨6433470, by rfl⟩ : syracuseStep 17155921 = 12866941) B12866941
theorem B22874561 : Blo 2007435 22874561 := bstep (se 2 (by rfl) ⟨8577960, by rfl⟩ : syracuseStep 22874561 = 17155921) B17155921
theorem B15249707 : Blo 2007435 15249707 := bstep (se 1 (by rfl) ⟨11437280, by rfl⟩ : syracuseStep 15249707 = 22874561) B22874561
theorem B10166471 : Blo 2007435 10166471 := bstep (se 1 (by rfl) ⟨7624853, by rfl⟩ : syracuseStep 10166471 = 15249707) B15249707
theorem B6777647 : Blo 2007435 6777647 := bstep (se 1 (by rfl) ⟨5083235, by rfl⟩ : syracuseStep 6777647 = 10166471) B10166471
theorem B4518431 : Blo 2007435 4518431 := bstep (se 1 (by rfl) ⟨3388823, by rfl⟩ : syracuseStep 4518431 = 6777647) B6777647
theorem B3012287 : Blo 2007435 3012287 := bstep (se 1 (by rfl) ⟨2259215, by rfl⟩ : syracuseStep 3012287 = 4518431) B4518431
theorem B2008191 : Blo 2007435 2008191 := bstep (se 1 (by rfl) ⟨1506143, by rfl⟩ : syracuseStep 2008191 = 3012287) B3012287
theorem B3012293 : Blo 2007435 3012293 := bbase (se 4 (by rfl) ⟨282402, by rfl⟩ : syracuseStep 3012293 = 564805) (by norm_num)
theorem B2008195 : Blo 2007435 2008195 := bstep (se 1 (by rfl) ⟨1506146, by rfl⟩ : syracuseStep 2008195 = 3012293) B3012293
theorem B3388837 : Blo 2007435 3388837 := bbase (se 4 (by rfl) ⟨317703, by rfl⟩ : syracuseStep 3388837 = 635407) (by norm_num)
theorem B4518449 : Blo 2007435 4518449 := bstep (se 2 (by rfl) ⟨1694418, by rfl⟩ : syracuseStep 4518449 = 3388837) B3388837
theorem B3012299 : Blo 2007435 3012299 := bstep (se 1 (by rfl) ⟨2259224, by rfl⟩ : syracuseStep 3012299 = 4518449) B4518449
theorem B2008199 : Blo 2007435 2008199 := bstep (se 1 (by rfl) ⟨1506149, by rfl⟩ : syracuseStep 2008199 = 3012299) B3012299
theorem B2259229 : Blo 2007435 2259229 := bbase (se 3 (by rfl) ⟨423605, by rfl⟩ : syracuseStep 2259229 = 847211) (by norm_num)
theorem B3012305 : Blo 2007435 3012305 := bstep (se 2 (by rfl) ⟨1129614, by rfl⟩ : syracuseStep 3012305 = 2259229) B2259229
theorem B2008203 : Blo 2007435 2008203 := bstep (se 1 (by rfl) ⟨1506152, by rfl⟩ : syracuseStep 2008203 = 3012305) B3012305
theorem B6777701 : Blo 2007435 6777701 := bbase (se 4 (by rfl) ⟨635409, by rfl⟩ : syracuseStep 6777701 = 1270819) (by norm_num)
theorem B4518467 : Blo 2007435 4518467 := bstep (se 1 (by rfl) ⟨3388850, by rfl⟩ : syracuseStep 4518467 = 6777701) B6777701
theorem B3012311 : Blo 2007435 3012311 := bstep (se 1 (by rfl) ⟨2259233, by rfl⟩ : syracuseStep 3012311 = 4518467) B4518467
theorem B2008207 : Blo 2007435 2008207 := bstep (se 1 (by rfl) ⟨1506155, by rfl⟩ : syracuseStep 2008207 = 3012311) B3012311
theorem B3012317 : Blo 2007435 3012317 := bbase (se 3 (by rfl) ⟨564809, by rfl⟩ : syracuseStep 3012317 = 1129619) (by norm_num)
theorem B2008211 : Blo 2007435 2008211 := bstep (se 1 (by rfl) ⟨1506158, by rfl⟩ : syracuseStep 2008211 = 3012317) B3012317
theorem B4518485 : Blo 2007435 4518485 := bbase (se 8 (by rfl) ⟨26475, by rfl⟩ : syracuseStep 4518485 = 52951) (by norm_num)
theorem B3012323 : Blo 2007435 3012323 := bstep (se 1 (by rfl) ⟨2259242, by rfl⟩ : syracuseStep 3012323 = 4518485) B4518485
theorem B2008215 : Blo 2007435 2008215 := bstep (se 1 (by rfl) ⟨1506161, by rfl⟩ : syracuseStep 2008215 = 3012323) B3012323
theorem B3216781 : Blo 2007435 3216781 := bbase (se 3 (by rfl) ⟨603146, by rfl⟩ : syracuseStep 3216781 = 1206293) (by norm_num)
theorem B4289041 : Blo 2007435 4289041 := bstep (se 2 (by rfl) ⟨1608390, by rfl⟩ : syracuseStep 4289041 = 3216781) B3216781
theorem B5718721 : Blo 2007435 5718721 := bstep (se 2 (by rfl) ⟨2144520, by rfl⟩ : syracuseStep 5718721 = 4289041) B4289041
theorem B7624961 : Blo 2007435 7624961 := bstep (se 2 (by rfl) ⟨2859360, by rfl⟩ : syracuseStep 7624961 = 5718721) B5718721
theorem B5083307 : Blo 2007435 5083307 := bstep (se 1 (by rfl) ⟨3812480, by rfl⟩ : syracuseStep 5083307 = 7624961) B7624961
theorem B3388871 : Blo 2007435 3388871 := bstep (se 1 (by rfl) ⟨2541653, by rfl⟩ : syracuseStep 3388871 = 5083307) B5083307
theorem B2259247 : Blo 2007435 2259247 := bstep (se 1 (by rfl) ⟨1694435, by rfl⟩ : syracuseStep 2259247 = 3388871) B3388871
theorem B3012329 : Blo 2007435 3012329 := bstep (se 2 (by rfl) ⟨1129623, by rfl⟩ : syracuseStep 3012329 = 2259247) B2259247
theorem B2008219 : Blo 2007435 2008219 := bstep (se 1 (by rfl) ⟨1506164, by rfl⟩ : syracuseStep 2008219 = 3012329) B3012329
theorem B25734293 : Blo 2007435 25734293 := bbase (se 6 (by rfl) ⟨603147, by rfl⟩ : syracuseStep 25734293 = 1206295) (by norm_num)
theorem B17156195 : Blo 2007435 17156195 := bstep (se 1 (by rfl) ⟨12867146, by rfl⟩ : syracuseStep 17156195 = 25734293) B25734293
theorem B11437463 : Blo 2007435 11437463 := bstep (se 1 (by rfl) ⟨8578097, by rfl⟩ : syracuseStep 11437463 = 17156195) B17156195
theorem B7624975 : Blo 2007435 7624975 := bstep (se 1 (by rfl) ⟨5718731, by rfl⟩ : syracuseStep 7624975 = 11437463) B11437463
theorem B10166633 : Blo 2007435 10166633 := bstep (se 2 (by rfl) ⟨3812487, by rfl⟩ : syracuseStep 10166633 = 7624975) B7624975
theorem B6777755 : Blo 2007435 6777755 := bstep (se 1 (by rfl) ⟨5083316, by rfl⟩ : syracuseStep 6777755 = 10166633) B10166633
theorem B4518503 : Blo 2007435 4518503 := bstep (se 1 (by rfl) ⟨3388877, by rfl⟩ : syracuseStep 4518503 = 6777755) B6777755
theorem B3012335 : Blo 2007435 3012335 := bstep (se 1 (by rfl) ⟨2259251, by rfl⟩ : syracuseStep 3012335 = 4518503) B4518503
theorem B2008223 : Blo 2007435 2008223 := bstep (se 1 (by rfl) ⟨1506167, by rfl⟩ : syracuseStep 2008223 = 3012335) B3012335
theorem B3012341 : Blo 2007435 3012341 := bbase (se 5 (by rfl) ⟨141203, by rfl⟩ : syracuseStep 3012341 = 282407) (by norm_num)
theorem B2008227 : Blo 2007435 2008227 := bstep (se 1 (by rfl) ⟨1506170, by rfl⟩ : syracuseStep 2008227 = 3012341) B3012341
theorem B8578133 : Blo 2007435 8578133 := bbase (se 8 (by rfl) ⟨50262, by rfl⟩ : syracuseStep 8578133 = 100525) (by norm_num)
theorem B5718755 : Blo 2007435 5718755 := bstep (se 1 (by rfl) ⟨4289066, by rfl⟩ : syracuseStep 5718755 = 8578133) B8578133
theorem B3812503 : Blo 2007435 3812503 := bstep (se 1 (by rfl) ⟨2859377, by rfl⟩ : syracuseStep 3812503 = 5718755) B5718755
theorem B5083337 : Blo 2007435 5083337 := bstep (se 2 (by rfl) ⟨1906251, by rfl⟩ : syracuseStep 5083337 = 3812503) B3812503
theorem B3388891 : Blo 2007435 3388891 := bstep (se 1 (by rfl) ⟨2541668, by rfl⟩ : syracuseStep 3388891 = 5083337) B5083337
theorem B4518521 : Blo 2007435 4518521 := bstep (se 2 (by rfl) ⟨1694445, by rfl⟩ : syracuseStep 4518521 = 3388891) B3388891
theorem B3012347 : Blo 2007435 3012347 := bstep (se 1 (by rfl) ⟨2259260, by rfl⟩ : syracuseStep 3012347 = 4518521) B4518521
theorem B2008231 : Blo 2007435 2008231 := bstep (se 1 (by rfl) ⟨1506173, by rfl⟩ : syracuseStep 2008231 = 3012347) B3012347
theorem B2259265 : Blo 2007435 2259265 := bbase (se 2 (by rfl) ⟨847224, by rfl⟩ : syracuseStep 2259265 = 1694449) (by norm_num)
theorem B3012353 : Blo 2007435 3012353 := bstep (se 2 (by rfl) ⟨1129632, by rfl⟩ : syracuseStep 3012353 = 2259265) B2259265
theorem B2008235 : Blo 2007435 2008235 := bstep (se 1 (by rfl) ⟨1506176, by rfl⟩ : syracuseStep 2008235 = 3012353) B3012353
theorem B5083357 : Blo 2007435 5083357 := bbase (se 3 (by rfl) ⟨953129, by rfl⟩ : syracuseStep 5083357 = 1906259) (by norm_num)
theorem B6777809 : Blo 2007435 6777809 := bstep (se 2 (by rfl) ⟨2541678, by rfl⟩ : syracuseStep 6777809 = 5083357) B5083357
theorem B4518539 : Blo 2007435 4518539 := bstep (se 1 (by rfl) ⟨3388904, by rfl⟩ : syracuseStep 4518539 = 6777809) B6777809
theorem B3012359 : Blo 2007435 3012359 := bstep (se 1 (by rfl) ⟨2259269, by rfl⟩ : syracuseStep 3012359 = 4518539) B4518539
theorem B2008239 : Blo 2007435 2008239 := bstep (se 1 (by rfl) ⟨1506179, by rfl⟩ : syracuseStep 2008239 = 3012359) B3012359
theorem B3012365 : Blo 2007435 3012365 := bbase (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) (by norm_num)
theorem B2008243 : Blo 2007435 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B4518557 : Blo 2007435 4518557 := bbase (se 3 (by rfl) ⟨847229, by rfl⟩ : syracuseStep 4518557 = 1694459) (by norm_num)
theorem B3012371 : Blo 2007435 3012371 := bstep (se 1 (by rfl) ⟨2259278, by rfl⟩ : syracuseStep 3012371 = 4518557) B4518557
theorem B2008247 : Blo 2007435 2008247 := bstep (se 1 (by rfl) ⟨1506185, by rfl⟩ : syracuseStep 2008247 = 3012371) B3012371
theorem B3388925 : Blo 2007435 3388925 := bbase (se 3 (by rfl) ⟨635423, by rfl⟩ : syracuseStep 3388925 = 1270847) (by norm_num)
theorem B2259283 : Blo 2007435 2259283 := bstep (se 1 (by rfl) ⟨1694462, by rfl⟩ : syracuseStep 2259283 = 3388925) B3388925
theorem B3012377 : Blo 2007435 3012377 := bstep (se 2 (by rfl) ⟨1129641, by rfl⟩ : syracuseStep 3012377 = 2259283) B2259283
theorem B2008251 : Blo 2007435 2008251 := bstep (se 1 (by rfl) ⟨1506188, by rfl⟩ : syracuseStep 2008251 = 3012377) B3012377
theorem B4289117 : Blo 2007435 4289117 := bbase (se 3 (by rfl) ⟨804209, by rfl⟩ : syracuseStep 4289117 = 1608419) (by norm_num)
theorem B11437645 : Blo 2007435 11437645 := bstep (se 3 (by rfl) ⟨2144558, by rfl⟩ : syracuseStep 11437645 = 4289117) B4289117
theorem B15250193 : Blo 2007435 15250193 := bstep (se 2 (by rfl) ⟨5718822, by rfl⟩ : syracuseStep 15250193 = 11437645) B11437645
theorem B10166795 : Blo 2007435 10166795 := bstep (se 1 (by rfl) ⟨7625096, by rfl⟩ : syracuseStep 10166795 = 15250193) B15250193
theorem B6777863 : Blo 2007435 6777863 := bstep (se 1 (by rfl) ⟨5083397, by rfl⟩ : syracuseStep 6777863 = 10166795) B10166795
theorem B4518575 : Blo 2007435 4518575 := bstep (se 1 (by rfl) ⟨3388931, by rfl⟩ : syracuseStep 4518575 = 6777863) B6777863
theorem B3012383 : Blo 2007435 3012383 := bstep (se 1 (by rfl) ⟨2259287, by rfl⟩ : syracuseStep 3012383 = 4518575) B4518575
theorem B2008255 : Blo 2007435 2008255 := bstep (se 1 (by rfl) ⟨1506191, by rfl⟩ : syracuseStep 2008255 = 3012383) B3012383
theorem B3012389 : Blo 2007435 3012389 := bbase (se 4 (by rfl) ⟨282411, by rfl⟩ : syracuseStep 3012389 = 564823) (by norm_num)
theorem B2008259 : Blo 2007435 2008259 := bstep (se 1 (by rfl) ⟨1506194, by rfl⟩ : syracuseStep 2008259 = 3012389) B3012389
theorem B2541709 : Blo 2007435 2541709 := bbase (se 3 (by rfl) ⟨476570, by rfl⟩ : syracuseStep 2541709 = 953141) (by norm_num)
theorem B3388945 : Blo 2007435 3388945 := bstep (se 2 (by rfl) ⟨1270854, by rfl⟩ : syracuseStep 3388945 = 2541709) B2541709
theorem B4518593 : Blo 2007435 4518593 := bstep (se 2 (by rfl) ⟨1694472, by rfl⟩ : syracuseStep 4518593 = 3388945) B3388945
theorem B3012395 : Blo 2007435 3012395 := bstep (se 1 (by rfl) ⟨2259296, by rfl⟩ : syracuseStep 3012395 = 4518593) B4518593
theorem B2008263 : Blo 2007435 2008263 := bstep (se 1 (by rfl) ⟨1506197, by rfl⟩ : syracuseStep 2008263 = 3012395) B3012395
theorem B2259301 : Blo 2007435 2259301 := bbase (se 4 (by rfl) ⟨211809, by rfl⟩ : syracuseStep 2259301 = 423619) (by norm_num)
theorem B3012401 : Blo 2007435 3012401 := bstep (se 2 (by rfl) ⟨1129650, by rfl⟩ : syracuseStep 3012401 = 2259301) B2259301
theorem B2008267 : Blo 2007435 2008267 := bstep (se 1 (by rfl) ⟨1506200, by rfl⟩ : syracuseStep 2008267 = 3012401) B3012401
theorem B5718869 : Blo 2007435 5718869 := bbase (se 9 (by rfl) ⟨16754, by rfl⟩ : syracuseStep 5718869 = 33509) (by norm_num)
theorem B3812579 : Blo 2007435 3812579 := bstep (se 1 (by rfl) ⟨2859434, by rfl⟩ : syracuseStep 3812579 = 5718869) B5718869
theorem B2541719 : Blo 2007435 2541719 := bstep (se 1 (by rfl) ⟨1906289, by rfl⟩ : syracuseStep 2541719 = 3812579) B3812579
theorem B6777917 : Blo 2007435 6777917 := bstep (se 3 (by rfl) ⟨1270859, by rfl⟩ : syracuseStep 6777917 = 2541719) B2541719
theorem B4518611 : Blo 2007435 4518611 := bstep (se 1 (by rfl) ⟨3388958, by rfl⟩ : syracuseStep 4518611 = 6777917) B6777917
theorem B3012407 : Blo 2007435 3012407 := bstep (se 1 (by rfl) ⟨2259305, by rfl⟩ : syracuseStep 3012407 = 4518611) B4518611
theorem B2008271 : Blo 2007435 2008271 := bstep (se 1 (by rfl) ⟨1506203, by rfl⟩ : syracuseStep 2008271 = 3012407) B3012407
theorem B3012413 : Blo 2007435 3012413 := bbase (se 3 (by rfl) ⟨564827, by rfl⟩ : syracuseStep 3012413 = 1129655) (by norm_num)
theorem B2008275 : Blo 2007435 2008275 := bstep (se 1 (by rfl) ⟨1506206, by rfl⟩ : syracuseStep 2008275 = 3012413) B3012413
theorem B4518629 : Blo 2007435 4518629 := bbase (se 4 (by rfl) ⟨423621, by rfl⟩ : syracuseStep 4518629 = 847243) (by norm_num)
theorem B3012419 : Blo 2007435 3012419 := bstep (se 1 (by rfl) ⟨2259314, by rfl⟩ : syracuseStep 3012419 = 4518629) B4518629
theorem B2008279 : Blo 2007435 2008279 := bstep (se 1 (by rfl) ⟨1506209, by rfl⟩ : syracuseStep 2008279 = 3012419) B3012419
theorem B5083469 : Blo 2007435 5083469 := bbase (se 3 (by rfl) ⟨953150, by rfl⟩ : syracuseStep 5083469 = 1906301) (by norm_num)
theorem B3388979 : Blo 2007435 3388979 := bstep (se 1 (by rfl) ⟨2541734, by rfl⟩ : syracuseStep 3388979 = 5083469) B5083469
theorem B2259319 : Blo 2007435 2259319 := bstep (se 1 (by rfl) ⟨1694489, by rfl⟩ : syracuseStep 2259319 = 3388979) B3388979
theorem B3012425 : Blo 2007435 3012425 := bstep (se 2 (by rfl) ⟨1129659, by rfl⟩ : syracuseStep 3012425 = 2259319) B2259319
theorem B2008283 : Blo 2007435 2008283 := bstep (se 1 (by rfl) ⟨1506212, by rfl⟩ : syracuseStep 2008283 = 3012425) B3012425
theorem B2144593 : Blo 2007435 2144593 := bbase (se 2 (by rfl) ⟨804222, by rfl⟩ : syracuseStep 2144593 = 1608445) (by norm_num)
theorem B2859457 : Blo 2007435 2859457 := bstep (se 2 (by rfl) ⟨1072296, by rfl⟩ : syracuseStep 2859457 = 2144593) B2144593
theorem B3812609 : Blo 2007435 3812609 := bstep (se 2 (by rfl) ⟨1429728, by rfl⟩ : syracuseStep 3812609 = 2859457) B2859457
theorem B10166957 : Blo 2007435 10166957 := bstep (se 3 (by rfl) ⟨1906304, by rfl⟩ : syracuseStep 10166957 = 3812609) B3812609
theorem B6777971 : Blo 2007435 6777971 := bstep (se 1 (by rfl) ⟨5083478, by rfl⟩ : syracuseStep 6777971 = 10166957) B10166957
theorem B4518647 : Blo 2007435 4518647 := bstep (se 1 (by rfl) ⟨3388985, by rfl⟩ : syracuseStep 4518647 = 6777971) B6777971
theorem B3012431 : Blo 2007435 3012431 := bstep (se 1 (by rfl) ⟨2259323, by rfl⟩ : syracuseStep 3012431 = 4518647) B4518647
theorem B2008287 : Blo 2007435 2008287 := bstep (se 1 (by rfl) ⟨1506215, by rfl⟩ : syracuseStep 2008287 = 3012431) B3012431
theorem B3012437 : Blo 2007435 3012437 := bbase (se 9 (by rfl) ⟨8825, by rfl⟩ : syracuseStep 3012437 = 17651) (by norm_num)
theorem B2008291 : Blo 2007435 2008291 := bstep (se 1 (by rfl) ⟨1506218, by rfl⟩ : syracuseStep 2008291 = 3012437) B3012437
theorem B2412677 : Blo 2007435 2412677 := bbase (se 4 (by rfl) ⟨226188, by rfl⟩ : syracuseStep 2412677 = 452377) (by norm_num)
theorem B6433805 : Blo 2007435 6433805 := bstep (se 3 (by rfl) ⟨1206338, by rfl⟩ : syracuseStep 6433805 = 2412677) B2412677
theorem B4289203 : Blo 2007435 4289203 := bstep (se 1 (by rfl) ⟨3216902, by rfl⟩ : syracuseStep 4289203 = 6433805) B6433805
theorem B5718937 : Blo 2007435 5718937 := bstep (se 2 (by rfl) ⟨2144601, by rfl⟩ : syracuseStep 5718937 = 4289203) B4289203
theorem B7625249 : Blo 2007435 7625249 := bstep (se 2 (by rfl) ⟨2859468, by rfl⟩ : syracuseStep 7625249 = 5718937) B5718937
theorem B5083499 : Blo 2007435 5083499 := bstep (se 1 (by rfl) ⟨3812624, by rfl⟩ : syracuseStep 5083499 = 7625249) B7625249
theorem B3388999 : Blo 2007435 3388999 := bstep (se 1 (by rfl) ⟨2541749, by rfl⟩ : syracuseStep 3388999 = 5083499) B5083499
theorem B4518665 : Blo 2007435 4518665 := bstep (se 2 (by rfl) ⟨1694499, by rfl⟩ : syracuseStep 4518665 = 3388999) B3388999
theorem B3012443 : Blo 2007435 3012443 := bstep (se 1 (by rfl) ⟨2259332, by rfl⟩ : syracuseStep 3012443 = 4518665) B4518665
theorem B2008295 : Blo 2007435 2008295 := bstep (se 1 (by rfl) ⟨1506221, by rfl⟩ : syracuseStep 2008295 = 3012443) B3012443
theorem B2259337 : Blo 2007435 2259337 := bbase (se 2 (by rfl) ⟨847251, by rfl⟩ : syracuseStep 2259337 = 1694503) (by norm_num)
theorem B3012449 : Blo 2007435 3012449 := bstep (se 2 (by rfl) ⟨1129668, by rfl⟩ : syracuseStep 3012449 = 2259337) B2259337
theorem B2008299 : Blo 2007435 2008299 := bstep (se 1 (by rfl) ⟨1506224, by rfl⟩ : syracuseStep 2008299 = 3012449) B3012449
theorem B57904469 : Blo 2007435 57904469 := bbase (se 11 (by rfl) ⟨42410, by rfl⟩ : syracuseStep 57904469 = 84821) (by norm_num)
theorem B38602979 : Blo 2007435 38602979 := bstep (se 1 (by rfl) ⟨28952234, by rfl⟩ : syracuseStep 38602979 = 57904469) B57904469
theorem B25735319 : Blo 2007435 25735319 := bstep (se 1 (by rfl) ⟨19301489, by rfl⟩ : syracuseStep 25735319 = 38602979) B38602979
theorem B17156879 : Blo 2007435 17156879 := bstep (se 1 (by rfl) ⟨12867659, by rfl⟩ : syracuseStep 17156879 = 25735319) B25735319
theorem B11437919 : Blo 2007435 11437919 := bstep (se 1 (by rfl) ⟨8578439, by rfl⟩ : syracuseStep 11437919 = 17156879) B17156879
theorem B7625279 : Blo 2007435 7625279 := bstep (se 1 (by rfl) ⟨5718959, by rfl⟩ : syracuseStep 7625279 = 11437919) B11437919
theorem B5083519 : Blo 2007435 5083519 := bstep (se 1 (by rfl) ⟨3812639, by rfl⟩ : syracuseStep 5083519 = 7625279) B7625279
theorem B6778025 : Blo 2007435 6778025 := bstep (se 2 (by rfl) ⟨2541759, by rfl⟩ : syracuseStep 6778025 = 5083519) B5083519
theorem B4518683 : Blo 2007435 4518683 := bstep (se 1 (by rfl) ⟨3389012, by rfl⟩ : syracuseStep 4518683 = 6778025) B6778025
theorem B3012455 : Blo 2007435 3012455 := bstep (se 1 (by rfl) ⟨2259341, by rfl⟩ : syracuseStep 3012455 = 4518683) B4518683
theorem B2008303 : Blo 2007435 2008303 := bstep (se 1 (by rfl) ⟨1506227, by rfl⟩ : syracuseStep 2008303 = 3012455) B3012455
theorem B3012461 : Blo 2007435 3012461 := bbase (se 3 (by rfl) ⟨564836, by rfl⟩ : syracuseStep 3012461 = 1129673) (by norm_num)
theorem B2008307 : Blo 2007435 2008307 := bstep (se 1 (by rfl) ⟨1506230, by rfl⟩ : syracuseStep 2008307 = 3012461) B3012461
theorem B4518701 : Blo 2007435 4518701 := bbase (se 3 (by rfl) ⟨847256, by rfl⟩ : syracuseStep 4518701 = 1694513) (by norm_num)
theorem B3012467 : Blo 2007435 3012467 := bstep (se 1 (by rfl) ⟨2259350, by rfl⟩ : syracuseStep 3012467 = 4518701) B4518701
theorem B2008311 : Blo 2007435 2008311 := bstep (se 1 (by rfl) ⟨1506233, by rfl⟩ : syracuseStep 2008311 = 3012467) B3012467
theorem B8142869 : Blo 2007435 8142869 := bbase (se 6 (by rfl) ⟨190848, by rfl⟩ : syracuseStep 8142869 = 381697) (by norm_num)
theorem B5428579 : Blo 2007435 5428579 := bstep (se 1 (by rfl) ⟨4071434, by rfl⟩ : syracuseStep 5428579 = 8142869) B8142869
theorem B7238105 : Blo 2007435 7238105 := bstep (se 2 (by rfl) ⟨2714289, by rfl⟩ : syracuseStep 7238105 = 5428579) B5428579
theorem B4825403 : Blo 2007435 4825403 := bstep (se 1 (by rfl) ⟨3619052, by rfl⟩ : syracuseStep 4825403 = 7238105) B7238105
theorem B3216935 : Blo 2007435 3216935 := bstep (se 1 (by rfl) ⟨2412701, by rfl⟩ : syracuseStep 3216935 = 4825403) B4825403
theorem B8578493 : Blo 2007435 8578493 := bstep (se 3 (by rfl) ⟨1608467, by rfl⟩ : syracuseStep 8578493 = 3216935) B3216935
theorem B5718995 : Blo 2007435 5718995 := bstep (se 1 (by rfl) ⟨4289246, by rfl⟩ : syracuseStep 5718995 = 8578493) B8578493
theorem B3812663 : Blo 2007435 3812663 := bstep (se 1 (by rfl) ⟨2859497, by rfl⟩ : syracuseStep 3812663 = 5718995) B5718995
theorem B2541775 : Blo 2007435 2541775 := bstep (se 1 (by rfl) ⟨1906331, by rfl⟩ : syracuseStep 2541775 = 3812663) B3812663
theorem B3389033 : Blo 2007435 3389033 := bstep (se 2 (by rfl) ⟨1270887, by rfl⟩ : syracuseStep 3389033 = 2541775) B2541775
theorem B2259355 : Blo 2007435 2259355 := bstep (se 1 (by rfl) ⟨1694516, by rfl⟩ : syracuseStep 2259355 = 3389033) B3389033
theorem B3012473 : Blo 2007435 3012473 := bstep (se 2 (by rfl) ⟨1129677, by rfl⟩ : syracuseStep 3012473 = 2259355) B2259355
theorem B2008315 : Blo 2007435 2008315 := bstep (se 1 (by rfl) ⟨1506236, by rfl⟩ : syracuseStep 2008315 = 3012473) B3012473
theorem B9650821 : Blo 2007435 9650821 := bbase (se 4 (by rfl) ⟨904764, by rfl⟩ : syracuseStep 9650821 = 1809529) (by norm_num)
theorem B12867761 : Blo 2007435 12867761 := bstep (se 2 (by rfl) ⟨4825410, by rfl⟩ : syracuseStep 12867761 = 9650821) B9650821
theorem B34314029 : Blo 2007435 34314029 := bstep (se 3 (by rfl) ⟨6433880, by rfl⟩ : syracuseStep 34314029 = 12867761) B12867761
theorem B22876019 : Blo 2007435 22876019 := bstep (se 1 (by rfl) ⟨17157014, by rfl⟩ : syracuseStep 22876019 = 34314029) B34314029
theorem B15250679 : Blo 2007435 15250679 := bstep (se 1 (by rfl) ⟨11438009, by rfl⟩ : syracuseStep 15250679 = 22876019) B22876019
theorem B10167119 : Blo 2007435 10167119 := bstep (se 1 (by rfl) ⟨7625339, by rfl⟩ : syracuseStep 10167119 = 15250679) B15250679
theorem B6778079 : Blo 2007435 6778079 := bstep (se 1 (by rfl) ⟨5083559, by rfl⟩ : syracuseStep 6778079 = 10167119) B10167119
theorem B4518719 : Blo 2007435 4518719 := bstep (se 1 (by rfl) ⟨3389039, by rfl⟩ : syracuseStep 4518719 = 6778079) B6778079
theorem B3012479 : Blo 2007435 3012479 := bstep (se 1 (by rfl) ⟨2259359, by rfl⟩ : syracuseStep 3012479 = 4518719) B4518719
theorem B2008319 : Blo 2007435 2008319 := bstep (se 1 (by rfl) ⟨1506239, by rfl⟩ : syracuseStep 2008319 = 3012479) B3012479
theorem B3012485 : Blo 2007435 3012485 := bbase (se 4 (by rfl) ⟨282420, by rfl⟩ : syracuseStep 3012485 = 564841) (by norm_num)
theorem B2008323 : Blo 2007435 2008323 := bstep (se 1 (by rfl) ⟨1506242, by rfl⟩ : syracuseStep 2008323 = 3012485) B3012485
theorem B3389053 : Blo 2007435 3389053 := bbase (se 3 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 3389053 = 1270895) (by norm_num)
theorem B4518737 : Blo 2007435 4518737 := bstep (se 2 (by rfl) ⟨1694526, by rfl⟩ : syracuseStep 4518737 = 3389053) B3389053
theorem B3012491 : Blo 2007435 3012491 := bstep (se 1 (by rfl) ⟨2259368, by rfl⟩ : syracuseStep 3012491 = 4518737) B4518737
theorem B2008327 : Blo 2007435 2008327 := bstep (se 1 (by rfl) ⟨1506245, by rfl⟩ : syracuseStep 2008327 = 3012491) B3012491
theorem B2259373 : Blo 2007435 2259373 := bbase (se 3 (by rfl) ⟨423632, by rfl⟩ : syracuseStep 2259373 = 847265) (by norm_num)
theorem B3012497 : Blo 2007435 3012497 := bstep (se 2 (by rfl) ⟨1129686, by rfl⟩ : syracuseStep 3012497 = 2259373) B2259373
theorem B2008331 : Blo 2007435 2008331 := bstep (se 1 (by rfl) ⟨1506248, by rfl⟩ : syracuseStep 2008331 = 3012497) B3012497
theorem B6778133 : Blo 2007435 6778133 := bbase (se 6 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 6778133 = 317725) (by norm_num)
theorem B4518755 : Blo 2007435 4518755 := bstep (se 1 (by rfl) ⟨3389066, by rfl⟩ : syracuseStep 4518755 = 6778133) B6778133
theorem B3012503 : Blo 2007435 3012503 := bstep (se 1 (by rfl) ⟨2259377, by rfl⟩ : syracuseStep 3012503 = 4518755) B4518755
theorem B2008335 : Blo 2007435 2008335 := bstep (se 1 (by rfl) ⟨1506251, by rfl⟩ : syracuseStep 2008335 = 3012503) B3012503
theorem B3012509 : Blo 2007435 3012509 := bbase (se 3 (by rfl) ⟨564845, by rfl⟩ : syracuseStep 3012509 = 1129691) (by norm_num)
theorem B2008339 : Blo 2007435 2008339 := bstep (se 1 (by rfl) ⟨1506254, by rfl⟩ : syracuseStep 2008339 = 3012509) B3012509
theorem B4518773 : Blo 2007435 4518773 := bbase (se 5 (by rfl) ⟨211817, by rfl⟩ : syracuseStep 4518773 = 423635) (by norm_num)
theorem B3012515 : Blo 2007435 3012515 := bstep (se 1 (by rfl) ⟨2259386, by rfl⟩ : syracuseStep 3012515 = 4518773) B4518773
theorem B2008343 : Blo 2007435 2008343 := bstep (se 1 (by rfl) ⟨1506257, by rfl⟩ : syracuseStep 2008343 = 3012515) B3012515
theorem B2751365 : Blo 2007435 2751365 := bbase (se 4 (by rfl) ⟨257940, by rfl⟩ : syracuseStep 2751365 = 515881) (by norm_num)
theorem B7336973 : Blo 2007435 7336973 := bstep (se 3 (by rfl) ⟨1375682, by rfl⟩ : syracuseStep 7336973 = 2751365) B2751365
theorem B4891315 : Blo 2007435 4891315 := bstep (se 1 (by rfl) ⟨3668486, by rfl⟩ : syracuseStep 4891315 = 7336973) B7336973
theorem B6521753 : Blo 2007435 6521753 := bstep (se 2 (by rfl) ⟨2445657, by rfl⟩ : syracuseStep 6521753 = 4891315) B4891315
theorem B17391341 : Blo 2007435 17391341 := bstep (se 3 (by rfl) ⟨3260876, by rfl⟩ : syracuseStep 17391341 = 6521753) B6521753
theorem B11594227 : Blo 2007435 11594227 := bstep (se 1 (by rfl) ⟨8695670, by rfl⟩ : syracuseStep 11594227 = 17391341) B17391341
theorem B15458969 : Blo 2007435 15458969 := bstep (se 2 (by rfl) ⟨5797113, by rfl⟩ : syracuseStep 15458969 = 11594227) B11594227
theorem B41223917 : Blo 2007435 41223917 := bstep (se 3 (by rfl) ⟨7729484, by rfl⟩ : syracuseStep 41223917 = 15458969) B15458969
theorem B109930445 : Blo 2007435 109930445 := bstep (se 3 (by rfl) ⟨20611958, by rfl⟩ : syracuseStep 109930445 = 41223917) B41223917
theorem B73286963 : Blo 2007435 73286963 := bstep (se 1 (by rfl) ⟨54965222, by rfl⟩ : syracuseStep 73286963 = 109930445) B109930445
theorem B48857975 : Blo 2007435 48857975 := bstep (se 1 (by rfl) ⟨36643481, by rfl⟩ : syracuseStep 48857975 = 73286963) B73286963
theorem B32571983 : Blo 2007435 32571983 := bstep (se 1 (by rfl) ⟨24428987, by rfl⟩ : syracuseStep 32571983 = 48857975) B48857975
theorem B21714655 : Blo 2007435 21714655 := bstep (se 1 (by rfl) ⟨16285991, by rfl⟩ : syracuseStep 21714655 = 32571983) B32571983
theorem B28952873 : Blo 2007435 28952873 := bstep (se 2 (by rfl) ⟨10857327, by rfl⟩ : syracuseStep 28952873 = 21714655) B21714655
theorem B19301915 : Blo 2007435 19301915 := bstep (se 1 (by rfl) ⟨14476436, by rfl⟩ : syracuseStep 19301915 = 28952873) B28952873
theorem B12867943 : Blo 2007435 12867943 := bstep (se 1 (by rfl) ⟨9650957, by rfl⟩ : syracuseStep 12867943 = 19301915) B19301915
theorem B17157257 : Blo 2007435 17157257 := bstep (se 2 (by rfl) ⟨6433971, by rfl⟩ : syracuseStep 17157257 = 12867943) B12867943
theorem B11438171 : Blo 2007435 11438171 := bstep (se 1 (by rfl) ⟨8578628, by rfl⟩ : syracuseStep 11438171 = 17157257) B17157257
theorem B7625447 : Blo 2007435 7625447 := bstep (se 1 (by rfl) ⟨5719085, by rfl⟩ : syracuseStep 7625447 = 11438171) B11438171
theorem B5083631 : Blo 2007435 5083631 := bstep (se 1 (by rfl) ⟨3812723, by rfl⟩ : syracuseStep 5083631 = 7625447) B7625447
theorem B3389087 : Blo 2007435 3389087 := bstep (se 1 (by rfl) ⟨2541815, by rfl⟩ : syracuseStep 3389087 = 5083631) B5083631
theorem B2259391 : Blo 2007435 2259391 := bstep (se 1 (by rfl) ⟨1694543, by rfl⟩ : syracuseStep 2259391 = 3389087) B3389087
theorem B3012521 : Blo 2007435 3012521 := bstep (se 2 (by rfl) ⟨1129695, by rfl⟩ : syracuseStep 3012521 = 2259391) B2259391
theorem B2008347 : Blo 2007435 2008347 := bstep (se 1 (by rfl) ⟨1506260, by rfl⟩ : syracuseStep 2008347 = 3012521) B3012521
theorem B7625461 : Blo 2007435 7625461 := bbase (se 5 (by rfl) ⟨357443, by rfl⟩ : syracuseStep 7625461 = 714887) (by norm_num)
theorem B10167281 : Blo 2007435 10167281 := bstep (se 2 (by rfl) ⟨3812730, by rfl⟩ : syracuseStep 10167281 = 7625461) B7625461
theorem B6778187 : Blo 2007435 6778187 := bstep (se 1 (by rfl) ⟨5083640, by rfl⟩ : syracuseStep 6778187 = 10167281) B10167281
theorem B4518791 : Blo 2007435 4518791 := bstep (se 1 (by rfl) ⟨3389093, by rfl⟩ : syracuseStep 4518791 = 6778187) B6778187
theorem B3012527 : Blo 2007435 3012527 := bstep (se 1 (by rfl) ⟨2259395, by rfl⟩ : syracuseStep 3012527 = 4518791) B4518791
theorem B2008351 : Blo 2007435 2008351 := bstep (se 1 (by rfl) ⟨1506263, by rfl⟩ : syracuseStep 2008351 = 3012527) B3012527
theorem B3012533 : Blo 2007435 3012533 := bbase (se 5 (by rfl) ⟨141212, by rfl⟩ : syracuseStep 3012533 = 282425) (by norm_num)
theorem B2008355 : Blo 2007435 2008355 := bstep (se 1 (by rfl) ⟨1506266, by rfl⟩ : syracuseStep 2008355 = 3012533) B3012533
theorem B5083661 : Blo 2007435 5083661 := bbase (se 3 (by rfl) ⟨953186, by rfl⟩ : syracuseStep 5083661 = 1906373) (by norm_num)
theorem B3389107 : Blo 2007435 3389107 := bstep (se 1 (by rfl) ⟨2541830, by rfl⟩ : syracuseStep 3389107 = 5083661) B5083661
theorem B4518809 : Blo 2007435 4518809 := bstep (se 2 (by rfl) ⟨1694553, by rfl⟩ : syracuseStep 4518809 = 3389107) B3389107
theorem B3012539 : Blo 2007435 3012539 := bstep (se 1 (by rfl) ⟨2259404, by rfl⟩ : syracuseStep 3012539 = 4518809) B4518809
theorem B2008359 : Blo 2007435 2008359 := bstep (se 1 (by rfl) ⟨1506269, by rfl⟩ : syracuseStep 2008359 = 3012539) B3012539
theorem B2259409 : Blo 2007435 2259409 := bbase (se 2 (by rfl) ⟨847278, by rfl⟩ : syracuseStep 2259409 = 1694557) (by norm_num)
theorem B3012545 : Blo 2007435 3012545 := bstep (se 2 (by rfl) ⟨1129704, by rfl⟩ : syracuseStep 3012545 = 2259409) B2259409
theorem B2008363 : Blo 2007435 2008363 := bstep (se 1 (by rfl) ⟨1506272, by rfl⟩ : syracuseStep 2008363 = 3012545) B3012545
theorem B4289357 : Blo 2007435 4289357 := bbase (se 3 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 4289357 = 1608509) (by norm_num)
theorem B2859571 : Blo 2007435 2859571 := bstep (se 1 (by rfl) ⟨2144678, by rfl⟩ : syracuseStep 2859571 = 4289357) B4289357
theorem B3812761 : Blo 2007435 3812761 := bstep (se 2 (by rfl) ⟨1429785, by rfl⟩ : syracuseStep 3812761 = 2859571) B2859571
theorem B5083681 : Blo 2007435 5083681 := bstep (se 2 (by rfl) ⟨1906380, by rfl⟩ : syracuseStep 5083681 = 3812761) B3812761
theorem B6778241 : Blo 2007435 6778241 := bstep (se 2 (by rfl) ⟨2541840, by rfl⟩ : syracuseStep 6778241 = 5083681) B5083681
theorem B4518827 : Blo 2007435 4518827 := bstep (se 1 (by rfl) ⟨3389120, by rfl⟩ : syracuseStep 4518827 = 6778241) B6778241
theorem B3012551 : Blo 2007435 3012551 := bstep (se 1 (by rfl) ⟨2259413, by rfl⟩ : syracuseStep 3012551 = 4518827) B4518827
theorem B2008367 : Blo 2007435 2008367 := bstep (se 1 (by rfl) ⟨1506275, by rfl⟩ : syracuseStep 2008367 = 3012551) B3012551
theorem B3012557 : Blo 2007435 3012557 := bbase (se 3 (by rfl) ⟨564854, by rfl⟩ : syracuseStep 3012557 = 1129709) (by norm_num)
theorem B2008371 : Blo 2007435 2008371 := bstep (se 1 (by rfl) ⟨1506278, by rfl⟩ : syracuseStep 2008371 = 3012557) B3012557
theorem B4518845 : Blo 2007435 4518845 := bbase (se 3 (by rfl) ⟨847283, by rfl⟩ : syracuseStep 4518845 = 1694567) (by norm_num)
theorem B3012563 : Blo 2007435 3012563 := bstep (se 1 (by rfl) ⟨2259422, by rfl⟩ : syracuseStep 3012563 = 4518845) B4518845
theorem B2008375 : Blo 2007435 2008375 := bstep (se 1 (by rfl) ⟨1506281, by rfl⟩ : syracuseStep 2008375 = 3012563) B3012563
theorem B3389141 : Blo 2007435 3389141 := bbase (se 7 (by rfl) ⟨39716, by rfl⟩ : syracuseStep 3389141 = 79433) (by norm_num)
theorem B2259427 : Blo 2007435 2259427 := bstep (se 1 (by rfl) ⟨1694570, by rfl⟩ : syracuseStep 2259427 = 3389141) B3389141
theorem B3012569 : Blo 2007435 3012569 := bstep (se 2 (by rfl) ⟨1129713, by rfl⟩ : syracuseStep 3012569 = 2259427) B2259427
theorem B2008379 : Blo 2007435 2008379 := bstep (se 1 (by rfl) ⟨1506284, by rfl⟩ : syracuseStep 2008379 = 3012569) B3012569
theorem B4825565 : Blo 2007435 4825565 := bbase (se 3 (by rfl) ⟨904793, by rfl⟩ : syracuseStep 4825565 = 1809587) (by norm_num)
theorem B3217043 : Blo 2007435 3217043 := bstep (se 1 (by rfl) ⟨2412782, by rfl⟩ : syracuseStep 3217043 = 4825565) B4825565
theorem B8578781 : Blo 2007435 8578781 := bstep (se 3 (by rfl) ⟨1608521, by rfl⟩ : syracuseStep 8578781 = 3217043) B3217043
theorem B5719187 : Blo 2007435 5719187 := bstep (se 1 (by rfl) ⟨4289390, by rfl⟩ : syracuseStep 5719187 = 8578781) B8578781
theorem B15251165 : Blo 2007435 15251165 := bstep (se 3 (by rfl) ⟨2859593, by rfl⟩ : syracuseStep 15251165 = 5719187) B5719187
theorem B10167443 : Blo 2007435 10167443 := bstep (se 1 (by rfl) ⟨7625582, by rfl⟩ : syracuseStep 10167443 = 15251165) B15251165
theorem B6778295 : Blo 2007435 6778295 := bstep (se 1 (by rfl) ⟨5083721, by rfl⟩ : syracuseStep 6778295 = 10167443) B10167443
theorem B4518863 : Blo 2007435 4518863 := bstep (se 1 (by rfl) ⟨3389147, by rfl⟩ : syracuseStep 4518863 = 6778295) B6778295
theorem B3012575 : Blo 2007435 3012575 := bstep (se 1 (by rfl) ⟨2259431, by rfl⟩ : syracuseStep 3012575 = 4518863) B4518863
theorem B2008383 : Blo 2007435 2008383 := bstep (se 1 (by rfl) ⟨1506287, by rfl⟩ : syracuseStep 2008383 = 3012575) B3012575
theorem B3012581 : Blo 2007435 3012581 := bbase (se 4 (by rfl) ⟨282429, by rfl⟩ : syracuseStep 3012581 = 564859) (by norm_num)
theorem B2008387 : Blo 2007435 2008387 := bstep (se 1 (by rfl) ⟨1506290, by rfl⟩ : syracuseStep 2008387 = 3012581) B3012581
theorem B3619189 : Blo 2007435 3619189 := bbase (se 5 (by rfl) ⟨169649, by rfl⟩ : syracuseStep 3619189 = 339299) (by norm_num)
theorem B4825585 : Blo 2007435 4825585 := bstep (se 2 (by rfl) ⟨1809594, by rfl⟩ : syracuseStep 4825585 = 3619189) B3619189
theorem B6434113 : Blo 2007435 6434113 := bstep (se 2 (by rfl) ⟨2412792, by rfl⟩ : syracuseStep 6434113 = 4825585) B4825585
theorem B8578817 : Blo 2007435 8578817 := bstep (se 2 (by rfl) ⟨3217056, by rfl⟩ : syracuseStep 8578817 = 6434113) B6434113
theorem B5719211 : Blo 2007435 5719211 := bstep (se 1 (by rfl) ⟨4289408, by rfl⟩ : syracuseStep 5719211 = 8578817) B8578817
theorem B3812807 : Blo 2007435 3812807 := bstep (se 1 (by rfl) ⟨2859605, by rfl⟩ : syracuseStep 3812807 = 5719211) B5719211
theorem B2541871 : Blo 2007435 2541871 := bstep (se 1 (by rfl) ⟨1906403, by rfl⟩ : syracuseStep 2541871 = 3812807) B3812807
theorem B3389161 : Blo 2007435 3389161 := bstep (se 2 (by rfl) ⟨1270935, by rfl⟩ : syracuseStep 3389161 = 2541871) B2541871
theorem B4518881 : Blo 2007435 4518881 := bstep (se 2 (by rfl) ⟨1694580, by rfl⟩ : syracuseStep 4518881 = 3389161) B3389161
theorem B3012587 : Blo 2007435 3012587 := bstep (se 1 (by rfl) ⟨2259440, by rfl⟩ : syracuseStep 3012587 = 4518881) B4518881
theorem B2008391 : Blo 2007435 2008391 := bstep (se 1 (by rfl) ⟨1506293, by rfl⟩ : syracuseStep 2008391 = 3012587) B3012587
theorem B2259445 : Blo 2007435 2259445 := bbase (se 5 (by rfl) ⟨105911, by rfl⟩ : syracuseStep 2259445 = 211823) (by norm_num)
theorem B3012593 : Blo 2007435 3012593 := bstep (se 2 (by rfl) ⟨1129722, by rfl⟩ : syracuseStep 3012593 = 2259445) B2259445
theorem B2008395 : Blo 2007435 2008395 := bstep (se 1 (by rfl) ⟨1506296, by rfl⟩ : syracuseStep 2008395 = 3012593) B3012593
theorem B2541881 : Blo 2007435 2541881 := bbase (se 2 (by rfl) ⟨953205, by rfl⟩ : syracuseStep 2541881 = 1906411) (by norm_num)
theorem B6778349 : Blo 2007435 6778349 := bstep (se 3 (by rfl) ⟨1270940, by rfl⟩ : syracuseStep 6778349 = 2541881) B2541881
theorem B4518899 : Blo 2007435 4518899 := bstep (se 1 (by rfl) ⟨3389174, by rfl⟩ : syracuseStep 4518899 = 6778349) B6778349
theorem B3012599 : Blo 2007435 3012599 := bstep (se 1 (by rfl) ⟨2259449, by rfl⟩ : syracuseStep 3012599 = 4518899) B4518899
theorem B2008399 : Blo 2007435 2008399 := bstep (se 1 (by rfl) ⟨1506299, by rfl⟩ : syracuseStep 2008399 = 3012599) B3012599
theorem B3012605 : Blo 2007435 3012605 := bbase (se 3 (by rfl) ⟨564863, by rfl⟩ : syracuseStep 3012605 = 1129727) (by norm_num)
theorem B2008403 : Blo 2007435 2008403 := bstep (se 1 (by rfl) ⟨1506302, by rfl⟩ : syracuseStep 2008403 = 3012605) B3012605
theorem B4518917 : Blo 2007435 4518917 := bbase (se 4 (by rfl) ⟨423648, by rfl⟩ : syracuseStep 4518917 = 847297) (by norm_num)
theorem B3012611 : Blo 2007435 3012611 := bstep (se 1 (by rfl) ⟨2259458, by rfl⟩ : syracuseStep 3012611 = 4518917) B4518917
theorem B2008407 : Blo 2007435 2008407 := bstep (se 1 (by rfl) ⟨1506305, by rfl⟩ : syracuseStep 2008407 = 3012611) B3012611
theorem B3812845 : Blo 2007435 3812845 := bbase (se 3 (by rfl) ⟨714908, by rfl⟩ : syracuseStep 3812845 = 1429817) (by norm_num)
theorem B5083793 : Blo 2007435 5083793 := bstep (se 2 (by rfl) ⟨1906422, by rfl⟩ : syracuseStep 5083793 = 3812845) B3812845
theorem B3389195 : Blo 2007435 3389195 := bstep (se 1 (by rfl) ⟨2541896, by rfl⟩ : syracuseStep 3389195 = 5083793) B5083793
theorem B2259463 : Blo 2007435 2259463 := bstep (se 1 (by rfl) ⟨1694597, by rfl⟩ : syracuseStep 2259463 = 3389195) B3389195
theorem B3012617 : Blo 2007435 3012617 := bstep (se 2 (by rfl) ⟨1129731, by rfl⟩ : syracuseStep 3012617 = 2259463) B2259463
theorem B2008411 : Blo 2007435 2008411 := bstep (se 1 (by rfl) ⟨1506308, by rfl⟩ : syracuseStep 2008411 = 3012617) B3012617
theorem B10167605 : Blo 2007435 10167605 := bbase (se 5 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 10167605 = 953213) (by norm_num)
theorem B6778403 : Blo 2007435 6778403 := bstep (se 1 (by rfl) ⟨5083802, by rfl⟩ : syracuseStep 6778403 = 10167605) B10167605
theorem B4518935 : Blo 2007435 4518935 := bstep (se 1 (by rfl) ⟨3389201, by rfl⟩ : syracuseStep 4518935 = 6778403) B6778403
theorem B3012623 : Blo 2007435 3012623 := bstep (se 1 (by rfl) ⟨2259467, by rfl⟩ : syracuseStep 3012623 = 4518935) B4518935
theorem B2008415 : Blo 2007435 2008415 := bstep (se 1 (by rfl) ⟨1506311, by rfl⟩ : syracuseStep 2008415 = 3012623) B3012623
theorem B3012629 : Blo 2007435 3012629 := bbase (se 6 (by rfl) ⟨70608, by rfl⟩ : syracuseStep 3012629 = 141217) (by norm_num)
theorem B2008419 : Blo 2007435 2008419 := bstep (se 1 (by rfl) ⟨1506314, by rfl⟩ : syracuseStep 2008419 = 3012629) B3012629
theorem B4825661 : Blo 2007435 4825661 := bbase (se 3 (by rfl) ⟨904811, by rfl⟩ : syracuseStep 4825661 = 1809623) (by norm_num)
theorem B12868429 : Blo 2007435 12868429 := bstep (se 3 (by rfl) ⟨2412830, by rfl⟩ : syracuseStep 12868429 = 4825661) B4825661
theorem B17157905 : Blo 2007435 17157905 := bstep (se 2 (by rfl) ⟨6434214, by rfl⟩ : syracuseStep 17157905 = 12868429) B12868429
theorem B11438603 : Blo 2007435 11438603 := bstep (se 1 (by rfl) ⟨8578952, by rfl⟩ : syracuseStep 11438603 = 17157905) B17157905
theorem B7625735 : Blo 2007435 7625735 := bstep (se 1 (by rfl) ⟨5719301, by rfl⟩ : syracuseStep 7625735 = 11438603) B11438603
theorem B5083823 : Blo 2007435 5083823 := bstep (se 1 (by rfl) ⟨3812867, by rfl⟩ : syracuseStep 5083823 = 7625735) B7625735
theorem B3389215 : Blo 2007435 3389215 := bstep (se 1 (by rfl) ⟨2541911, by rfl⟩ : syracuseStep 3389215 = 5083823) B5083823
theorem B4518953 : Blo 2007435 4518953 := bstep (se 2 (by rfl) ⟨1694607, by rfl⟩ : syracuseStep 4518953 = 3389215) B3389215
theorem B3012635 : Blo 2007435 3012635 := bstep (se 1 (by rfl) ⟨2259476, by rfl⟩ : syracuseStep 3012635 = 4518953) B4518953
theorem B2008423 : Blo 2007435 2008423 := bstep (se 1 (by rfl) ⟨1506317, by rfl⟩ : syracuseStep 2008423 = 3012635) B3012635
theorem B2259481 : Blo 2007435 2259481 := bbase (se 2 (by rfl) ⟨847305, by rfl⟩ : syracuseStep 2259481 = 1694611) (by norm_num)
theorem B3012641 : Blo 2007435 3012641 := bstep (se 2 (by rfl) ⟨1129740, by rfl⟩ : syracuseStep 3012641 = 2259481) B2259481
theorem B2008427 : Blo 2007435 2008427 := bstep (se 1 (by rfl) ⟨1506320, by rfl⟩ : syracuseStep 2008427 = 3012641) B3012641
theorem B7625765 : Blo 2007435 7625765 := bbase (se 4 (by rfl) ⟨714915, by rfl⟩ : syracuseStep 7625765 = 1429831) (by norm_num)
theorem B5083843 : Blo 2007435 5083843 := bstep (se 1 (by rfl) ⟨3812882, by rfl⟩ : syracuseStep 5083843 = 7625765) B7625765
theorem B6778457 : Blo 2007435 6778457 := bstep (se 2 (by rfl) ⟨2541921, by rfl⟩ : syracuseStep 6778457 = 5083843) B5083843
theorem B4518971 : Blo 2007435 4518971 := bstep (se 1 (by rfl) ⟨3389228, by rfl⟩ : syracuseStep 4518971 = 6778457) B6778457
theorem B3012647 : Blo 2007435 3012647 := bstep (se 1 (by rfl) ⟨2259485, by rfl⟩ : syracuseStep 3012647 = 4518971) B4518971
theorem B2008431 : Blo 2007435 2008431 := bstep (se 1 (by rfl) ⟨1506323, by rfl⟩ : syracuseStep 2008431 = 3012647) B3012647
theorem B3012653 : Blo 2007435 3012653 := bbase (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) (by norm_num)
theorem B2008435 : Blo 2007435 2008435 := bstep (se 1 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 2008435 = 3012653) B3012653
theorem B4518989 : Blo 2007435 4518989 := bbase (se 3 (by rfl) ⟨847310, by rfl⟩ : syracuseStep 4518989 = 1694621) (by norm_num)
theorem B3012659 : Blo 2007435 3012659 := bstep (se 1 (by rfl) ⟨2259494, by rfl⟩ : syracuseStep 3012659 = 4518989) B4518989
theorem B2008439 : Blo 2007435 2008439 := bstep (se 1 (by rfl) ⟨1506329, by rfl⟩ : syracuseStep 2008439 = 3012659) B3012659
theorem B2541937 : Blo 2007435 2541937 := bbase (se 2 (by rfl) ⟨953226, by rfl⟩ : syracuseStep 2541937 = 1906453) (by norm_num)
theorem B3389249 : Blo 2007435 3389249 := bstep (se 2 (by rfl) ⟨1270968, by rfl⟩ : syracuseStep 3389249 = 2541937) B2541937
theorem B2259499 : Blo 2007435 2259499 := bstep (se 1 (by rfl) ⟨1694624, by rfl⟩ : syracuseStep 2259499 = 3389249) B3389249
theorem B3012665 : Blo 2007435 3012665 := bstep (se 2 (by rfl) ⟨1129749, by rfl⟩ : syracuseStep 3012665 = 2259499) B2259499
theorem B2008443 : Blo 2007435 2008443 := bstep (se 1 (by rfl) ⟨1506332, by rfl⟩ : syracuseStep 2008443 = 3012665) B3012665
theorem B4071701 : Blo 2007435 4071701 := bbase (se 6 (by rfl) ⟨95430, by rfl⟩ : syracuseStep 4071701 = 190861) (by norm_num)
theorem B2714467 : Blo 2007435 2714467 := bstep (se 1 (by rfl) ⟨2035850, by rfl⟩ : syracuseStep 2714467 = 4071701) B4071701
theorem B3619289 : Blo 2007435 3619289 := bstep (se 2 (by rfl) ⟨1357233, by rfl⟩ : syracuseStep 3619289 = 2714467) B2714467
theorem B9651437 : Blo 2007435 9651437 := bstep (se 3 (by rfl) ⟨1809644, by rfl⟩ : syracuseStep 9651437 = 3619289) B3619289
theorem B6434291 : Blo 2007435 6434291 := bstep (se 1 (by rfl) ⟨4825718, by rfl⟩ : syracuseStep 6434291 = 9651437) B9651437
theorem B4289527 : Blo 2007435 4289527 := bstep (se 1 (by rfl) ⟨3217145, by rfl⟩ : syracuseStep 4289527 = 6434291) B6434291
theorem B22877477 : Blo 2007435 22877477 := bstep (se 4 (by rfl) ⟨2144763, by rfl⟩ : syracuseStep 22877477 = 4289527) B4289527
theorem B15251651 : Blo 2007435 15251651 := bstep (se 1 (by rfl) ⟨11438738, by rfl⟩ : syracuseStep 15251651 = 22877477) B22877477
theorem B10167767 : Blo 2007435 10167767 := bstep (se 1 (by rfl) ⟨7625825, by rfl⟩ : syracuseStep 10167767 = 15251651) B15251651
theorem B6778511 : Blo 2007435 6778511 := bstep (se 1 (by rfl) ⟨5083883, by rfl⟩ : syracuseStep 6778511 = 10167767) B10167767
theorem B4519007 : Blo 2007435 4519007 := bstep (se 1 (by rfl) ⟨3389255, by rfl⟩ : syracuseStep 4519007 = 6778511) B6778511
theorem B3012671 : Blo 2007435 3012671 := bstep (se 1 (by rfl) ⟨2259503, by rfl⟩ : syracuseStep 3012671 = 4519007) B4519007
theorem B2008447 : Blo 2007435 2008447 := bstep (se 1 (by rfl) ⟨1506335, by rfl⟩ : syracuseStep 2008447 = 3012671) B3012671
theorem B3012677 : Blo 2007435 3012677 := bbase (se 4 (by rfl) ⟨282438, by rfl⟩ : syracuseStep 3012677 = 564877) (by norm_num)
theorem B2008451 : Blo 2007435 2008451 := bstep (se 1 (by rfl) ⟨1506338, by rfl⟩ : syracuseStep 2008451 = 3012677) B3012677
theorem B3389269 : Blo 2007435 3389269 := bbase (se 9 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 3389269 = 19859) (by norm_num)
theorem B4519025 : Blo 2007435 4519025 := bstep (se 2 (by rfl) ⟨1694634, by rfl⟩ : syracuseStep 4519025 = 3389269) B3389269
theorem B3012683 : Blo 2007435 3012683 := bstep (se 1 (by rfl) ⟨2259512, by rfl⟩ : syracuseStep 3012683 = 4519025) B4519025
theorem B2008455 : Blo 2007435 2008455 := bstep (se 1 (by rfl) ⟨1506341, by rfl⟩ : syracuseStep 2008455 = 3012683) B3012683
theorem B2259517 : Blo 2007435 2259517 := bbase (se 3 (by rfl) ⟨423659, by rfl⟩ : syracuseStep 2259517 = 847319) (by norm_num)
theorem B3012689 : Blo 2007435 3012689 := bstep (se 2 (by rfl) ⟨1129758, by rfl⟩ : syracuseStep 3012689 = 2259517) B2259517
theorem B2008459 : Blo 2007435 2008459 := bstep (se 1 (by rfl) ⟨1506344, by rfl⟩ : syracuseStep 2008459 = 3012689) B3012689
theorem B6778565 : Blo 2007435 6778565 := bbase (se 4 (by rfl) ⟨635490, by rfl⟩ : syracuseStep 6778565 = 1270981) (by norm_num)
theorem B4519043 : Blo 2007435 4519043 := bstep (se 1 (by rfl) ⟨3389282, by rfl⟩ : syracuseStep 4519043 = 6778565) B6778565
theorem B3012695 : Blo 2007435 3012695 := bstep (se 1 (by rfl) ⟨2259521, by rfl⟩ : syracuseStep 3012695 = 4519043) B4519043
theorem B2008463 : Blo 2007435 2008463 := bstep (se 1 (by rfl) ⟨1506347, by rfl⟩ : syracuseStep 2008463 = 3012695) B3012695
theorem B3012701 : Blo 2007435 3012701 := bbase (se 3 (by rfl) ⟨564881, by rfl⟩ : syracuseStep 3012701 = 1129763) (by norm_num)
theorem B2008467 : Blo 2007435 2008467 := bstep (se 1 (by rfl) ⟨1506350, by rfl⟩ : syracuseStep 2008467 = 3012701) B3012701
theorem B4519061 : Blo 2007435 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B3012707 : Blo 2007435 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B2008471 : Blo 2007435 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B2859725 : Blo 2007435 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B7625933 : Blo 2007435 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B5083955 : Blo 2007435 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B3389303 : Blo 2007435 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B2259535 : Blo 2007435 2259535 := bstep (se 1 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 2259535 = 3389303) B3389303
theorem B3012713 : Blo 2007435 3012713 := bstep (se 2 (by rfl) ⟨1129767, by rfl⟩ : syracuseStep 3012713 = 2259535) B2259535
theorem B2008475 : Blo 2007435 2008475 := bstep (se 1 (by rfl) ⟨1506356, by rfl⟩ : syracuseStep 2008475 = 3012713) B3012713
theorem B7238693 : Blo 2007435 7238693 := bbase (se 4 (by rfl) ⟨678627, by rfl⟩ : syracuseStep 7238693 = 1357255) (by norm_num)
theorem B19303181 : Blo 2007435 19303181 := bstep (se 3 (by rfl) ⟨3619346, by rfl⟩ : syracuseStep 19303181 = 7238693) B7238693
theorem B12868787 : Blo 2007435 12868787 := bstep (se 1 (by rfl) ⟨9651590, by rfl⟩ : syracuseStep 12868787 = 19303181) B19303181
theorem B8579191 : Blo 2007435 8579191 := bstep (se 1 (by rfl) ⟨6434393, by rfl⟩ : syracuseStep 8579191 = 12868787) B12868787
theorem B11438921 : Blo 2007435 11438921 := bstep (se 2 (by rfl) ⟨4289595, by rfl⟩ : syracuseStep 11438921 = 8579191) B8579191
theorem B7625947 : Blo 2007435 7625947 := bstep (se 1 (by rfl) ⟨5719460, by rfl⟩ : syracuseStep 7625947 = 11438921) B11438921
theorem B10167929 : Blo 2007435 10167929 := bstep (se 2 (by rfl) ⟨3812973, by rfl⟩ : syracuseStep 10167929 = 7625947) B7625947
theorem B6778619 : Blo 2007435 6778619 := bstep (se 1 (by rfl) ⟨5083964, by rfl⟩ : syracuseStep 6778619 = 10167929) B10167929
theorem B4519079 : Blo 2007435 4519079 := bstep (se 1 (by rfl) ⟨3389309, by rfl⟩ : syracuseStep 4519079 = 6778619) B6778619
theorem B3012719 : Blo 2007435 3012719 := bstep (se 1 (by rfl) ⟨2259539, by rfl⟩ : syracuseStep 3012719 = 4519079) B4519079
theorem B2008479 : Blo 2007435 2008479 := bstep (se 1 (by rfl) ⟨1506359, by rfl⟩ : syracuseStep 2008479 = 3012719) B3012719
theorem B3012725 : Blo 2007435 3012725 := bbase (se 5 (by rfl) ⟨141221, by rfl⟩ : syracuseStep 3012725 = 282443) (by norm_num)
theorem B2008483 : Blo 2007435 2008483 := bstep (se 1 (by rfl) ⟨1506362, by rfl⟩ : syracuseStep 2008483 = 3012725) B3012725
theorem B3812989 : Blo 2007435 3812989 := bbase (se 3 (by rfl) ⟨714935, by rfl⟩ : syracuseStep 3812989 = 1429871) (by norm_num)
theorem B5083985 : Blo 2007435 5083985 := bstep (se 2 (by rfl) ⟨1906494, by rfl⟩ : syracuseStep 5083985 = 3812989) B3812989
theorem B3389323 : Blo 2007435 3389323 := bstep (se 1 (by rfl) ⟨2541992, by rfl⟩ : syracuseStep 3389323 = 5083985) B5083985
theorem B4519097 : Blo 2007435 4519097 := bstep (se 2 (by rfl) ⟨1694661, by rfl⟩ : syracuseStep 4519097 = 3389323) B3389323
theorem B3012731 : Blo 2007435 3012731 := bstep (se 1 (by rfl) ⟨2259548, by rfl⟩ : syracuseStep 3012731 = 4519097) B4519097
theorem B2008487 : Blo 2007435 2008487 := bstep (se 1 (by rfl) ⟨1506365, by rfl⟩ : syracuseStep 2008487 = 3012731) B3012731
theorem B2259553 : Blo 2007435 2259553 := bbase (se 2 (by rfl) ⟨847332, by rfl⟩ : syracuseStep 2259553 = 1694665) (by norm_num)
theorem B3012737 : Blo 2007435 3012737 := bstep (se 2 (by rfl) ⟨1129776, by rfl⟩ : syracuseStep 3012737 = 2259553) B2259553
theorem B2008491 : Blo 2007435 2008491 := bstep (se 1 (by rfl) ⟨1506368, by rfl⟩ : syracuseStep 2008491 = 3012737) B3012737
theorem B5084005 : Blo 2007435 5084005 := bbase (se 4 (by rfl) ⟨476625, by rfl⟩ : syracuseStep 5084005 = 953251) (by norm_num)
theorem B6778673 : Blo 2007435 6778673 := bstep (se 2 (by rfl) ⟨2542002, by rfl⟩ : syracuseStep 6778673 = 5084005) B5084005
theorem B4519115 : Blo 2007435 4519115 := bstep (se 1 (by rfl) ⟨3389336, by rfl⟩ : syracuseStep 4519115 = 6778673) B6778673
theorem B3012743 : Blo 2007435 3012743 := bstep (se 1 (by rfl) ⟨2259557, by rfl⟩ : syracuseStep 3012743 = 4519115) B4519115
theorem B2008495 : Blo 2007435 2008495 := bstep (se 1 (by rfl) ⟨1506371, by rfl⟩ : syracuseStep 2008495 = 3012743) B3012743
theorem B3012749 : Blo 2007435 3012749 := bbase (se 3 (by rfl) ⟨564890, by rfl⟩ : syracuseStep 3012749 = 1129781) (by norm_num)
theorem B2008499 : Blo 2007435 2008499 := bstep (se 1 (by rfl) ⟨1506374, by rfl⟩ : syracuseStep 2008499 = 3012749) B3012749
theorem B4519133 : Blo 2007435 4519133 := bbase (se 3 (by rfl) ⟨847337, by rfl⟩ : syracuseStep 4519133 = 1694675) (by norm_num)
theorem B3012755 : Blo 2007435 3012755 := bstep (se 1 (by rfl) ⟨2259566, by rfl⟩ : syracuseStep 3012755 = 4519133) B4519133
theorem B2008503 : Blo 2007435 2008503 := bstep (se 1 (by rfl) ⟨1506377, by rfl⟩ : syracuseStep 2008503 = 3012755) B3012755
theorem B3389357 : Blo 2007435 3389357 := bbase (se 3 (by rfl) ⟨635504, by rfl⟩ : syracuseStep 3389357 = 1271009) (by norm_num)
theorem B2259571 : Blo 2007435 2259571 := bstep (se 1 (by rfl) ⟨1694678, by rfl⟩ : syracuseStep 2259571 = 3389357) B3389357
theorem B3012761 : Blo 2007435 3012761 := bstep (se 2 (by rfl) ⟨1129785, by rfl⟩ : syracuseStep 3012761 = 2259571) B2259571
theorem B2008507 : Blo 2007435 2008507 := bstep (se 1 (by rfl) ⟨1506380, by rfl⟩ : syracuseStep 2008507 = 3012761) B3012761
theorem B9286613 : Blo 2007435 9286613 := bbase (se 7 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 9286613 = 217655) (by norm_num)
theorem B6191075 : Blo 2007435 6191075 := bstep (se 1 (by rfl) ⟨4643306, by rfl⟩ : syracuseStep 6191075 = 9286613) B9286613
theorem B4127383 : Blo 2007435 4127383 := bstep (se 1 (by rfl) ⟨3095537, by rfl⟩ : syracuseStep 4127383 = 6191075) B6191075
theorem B5503177 : Blo 2007435 5503177 := bstep (se 2 (by rfl) ⟨2063691, by rfl⟩ : syracuseStep 5503177 = 4127383) B4127383
theorem B29350277 : Blo 2007435 29350277 := bstep (se 4 (by rfl) ⟨2751588, by rfl⟩ : syracuseStep 29350277 = 5503177) B5503177
theorem B19566851 : Blo 2007435 19566851 := bstep (se 1 (by rfl) ⟨14675138, by rfl⟩ : syracuseStep 19566851 = 29350277) B29350277
theorem B52178269 : Blo 2007435 52178269 := bstep (se 3 (by rfl) ⟨9783425, by rfl⟩ : syracuseStep 52178269 = 19566851) B19566851
theorem B69571025 : Blo 2007435 69571025 := bstep (se 2 (by rfl) ⟨26089134, by rfl⟩ : syracuseStep 69571025 = 52178269) B52178269
theorem B46380683 : Blo 2007435 46380683 := bstep (se 1 (by rfl) ⟨34785512, by rfl⟩ : syracuseStep 46380683 = 69571025) B69571025
theorem B123681821 : Blo 2007435 123681821 := bstep (se 3 (by rfl) ⟨23190341, by rfl⟩ : syracuseStep 123681821 = 46380683) B46380683
theorem B329818189 : Blo 2007435 329818189 := bstep (se 3 (by rfl) ⟨61840910, by rfl⟩ : syracuseStep 329818189 = 123681821) B123681821
theorem B439757585 : Blo 2007435 439757585 := bstep (se 2 (by rfl) ⟨164909094, by rfl⟩ : syracuseStep 439757585 = 329818189) B329818189
theorem B293171723 : Blo 2007435 293171723 := bstep (se 1 (by rfl) ⟨219878792, by rfl⟩ : syracuseStep 293171723 = 439757585) B439757585
theorem B195447815 : Blo 2007435 195447815 := bstep (se 1 (by rfl) ⟨146585861, by rfl⟩ : syracuseStep 195447815 = 293171723) B293171723
theorem B130298543 : Blo 2007435 130298543 := bstep (se 1 (by rfl) ⟨97723907, by rfl⟩ : syracuseStep 130298543 = 195447815) B195447815
theorem B86865695 : Blo 2007435 86865695 := bstep (se 1 (by rfl) ⟨65149271, by rfl⟩ : syracuseStep 86865695 = 130298543) B130298543
theorem B57910463 : Blo 2007435 57910463 := bstep (se 1 (by rfl) ⟨43432847, by rfl⟩ : syracuseStep 57910463 = 86865695) B86865695
theorem B38606975 : Blo 2007435 38606975 := bstep (se 1 (by rfl) ⟨28955231, by rfl⟩ : syracuseStep 38606975 = 57910463) B57910463
theorem B25737983 : Blo 2007435 25737983 := bstep (se 1 (by rfl) ⟨19303487, by rfl⟩ : syracuseStep 25737983 = 38606975) B38606975
theorem B17158655 : Blo 2007435 17158655 := bstep (se 1 (by rfl) ⟨12868991, by rfl⟩ : syracuseStep 17158655 = 25737983) B25737983
theorem B11439103 : Blo 2007435 11439103 := bstep (se 1 (by rfl) ⟨8579327, by rfl⟩ : syracuseStep 11439103 = 17158655) B17158655
theorem B15252137 : Blo 2007435 15252137 := bstep (se 2 (by rfl) ⟨5719551, by rfl⟩ : syracuseStep 15252137 = 11439103) B11439103
theorem B10168091 : Blo 2007435 10168091 := bstep (se 1 (by rfl) ⟨7626068, by rfl⟩ : syracuseStep 10168091 = 15252137) B15252137
theorem B6778727 : Blo 2007435 6778727 := bstep (se 1 (by rfl) ⟨5084045, by rfl⟩ : syracuseStep 6778727 = 10168091) B10168091
theorem B4519151 : Blo 2007435 4519151 := bstep (se 1 (by rfl) ⟨3389363, by rfl⟩ : syracuseStep 4519151 = 6778727) B6778727
theorem B3012767 : Blo 2007435 3012767 := bstep (se 1 (by rfl) ⟨2259575, by rfl⟩ : syracuseStep 3012767 = 4519151) B4519151
theorem B2008511 : Blo 2007435 2008511 := bstep (se 1 (by rfl) ⟨1506383, by rfl⟩ : syracuseStep 2008511 = 3012767) B3012767
theorem B3012773 : Blo 2007435 3012773 := bbase (se 4 (by rfl) ⟨282447, by rfl⟩ : syracuseStep 3012773 = 564895) (by norm_num)
theorem B2008515 : Blo 2007435 2008515 := bstep (se 1 (by rfl) ⟨1506386, by rfl⟩ : syracuseStep 2008515 = 3012773) B3012773
theorem B2542033 : Blo 2007435 2542033 := bbase (se 2 (by rfl) ⟨953262, by rfl⟩ : syracuseStep 2542033 = 1906525) (by norm_num)
theorem B3389377 : Blo 2007435 3389377 := bstep (se 2 (by rfl) ⟨1271016, by rfl⟩ : syracuseStep 3389377 = 2542033) B2542033
theorem B4519169 : Blo 2007435 4519169 := bstep (se 2 (by rfl) ⟨1694688, by rfl⟩ : syracuseStep 4519169 = 3389377) B3389377
theorem B3012779 : Blo 2007435 3012779 := bstep (se 1 (by rfl) ⟨2259584, by rfl⟩ : syracuseStep 3012779 = 4519169) B4519169
theorem B2008519 : Blo 2007435 2008519 := bstep (se 1 (by rfl) ⟨1506389, by rfl⟩ : syracuseStep 2008519 = 3012779) B3012779
theorem B2259589 : Blo 2007435 2259589 := bbase (se 4 (by rfl) ⟨211836, by rfl⟩ : syracuseStep 2259589 = 423673) (by norm_num)
theorem B3012785 : Blo 2007435 3012785 := bstep (se 2 (by rfl) ⟨1129794, by rfl⟩ : syracuseStep 3012785 = 2259589) B2259589
theorem B2008523 : Blo 2007435 2008523 := bstep (se 1 (by rfl) ⟨1506392, by rfl⟩ : syracuseStep 2008523 = 3012785) B3012785
theorem B6434549 : Blo 2007435 6434549 := bbase (se 5 (by rfl) ⟨301619, by rfl⟩ : syracuseStep 6434549 = 603239) (by norm_num)
theorem B4289699 : Blo 2007435 4289699 := bstep (se 1 (by rfl) ⟨3217274, by rfl⟩ : syracuseStep 4289699 = 6434549) B6434549
theorem B2859799 : Blo 2007435 2859799 := bstep (se 1 (by rfl) ⟨2144849, by rfl⟩ : syracuseStep 2859799 = 4289699) B4289699
theorem B3813065 : Blo 2007435 3813065 := bstep (se 2 (by rfl) ⟨1429899, by rfl⟩ : syracuseStep 3813065 = 2859799) B2859799
theorem B2542043 : Blo 2007435 2542043 := bstep (se 1 (by rfl) ⟨1906532, by rfl⟩ : syracuseStep 2542043 = 3813065) B3813065
theorem B6778781 : Blo 2007435 6778781 := bstep (se 3 (by rfl) ⟨1271021, by rfl⟩ : syracuseStep 6778781 = 2542043) B2542043
theorem B4519187 : Blo 2007435 4519187 := bstep (se 1 (by rfl) ⟨3389390, by rfl⟩ : syracuseStep 4519187 = 6778781) B6778781
theorem B3012791 : Blo 2007435 3012791 := bstep (se 1 (by rfl) ⟨2259593, by rfl⟩ : syracuseStep 3012791 = 4519187) B4519187
theorem B2008527 : Blo 2007435 2008527 := bstep (se 1 (by rfl) ⟨1506395, by rfl⟩ : syracuseStep 2008527 = 3012791) B3012791
theorem B3012797 : Blo 2007435 3012797 := bbase (se 3 (by rfl) ⟨564899, by rfl⟩ : syracuseStep 3012797 = 1129799) (by norm_num)
theorem B2008531 : Blo 2007435 2008531 := bstep (se 1 (by rfl) ⟨1506398, by rfl⟩ : syracuseStep 2008531 = 3012797) B3012797
theorem B4519205 : Blo 2007435 4519205 := bbase (se 4 (by rfl) ⟨423675, by rfl⟩ : syracuseStep 4519205 = 847351) (by norm_num)
theorem B3012803 : Blo 2007435 3012803 := bstep (se 1 (by rfl) ⟨2259602, by rfl⟩ : syracuseStep 3012803 = 4519205) B4519205
theorem B2008535 : Blo 2007435 2008535 := bstep (se 1 (by rfl) ⟨1506401, by rfl⟩ : syracuseStep 2008535 = 3012803) B3012803
theorem B5084117 : Blo 2007435 5084117 := bbase (se 7 (by rfl) ⟨59579, by rfl⟩ : syracuseStep 5084117 = 119159) (by norm_num)
theorem B3389411 : Blo 2007435 3389411 := bstep (se 1 (by rfl) ⟨2542058, by rfl⟩ : syracuseStep 3389411 = 5084117) B5084117
theorem B2259607 : Blo 2007435 2259607 := bstep (se 1 (by rfl) ⟨1694705, by rfl⟩ : syracuseStep 2259607 = 3389411) B3389411
theorem B3012809 : Blo 2007435 3012809 := bstep (se 2 (by rfl) ⟨1129803, by rfl⟩ : syracuseStep 3012809 = 2259607) B2259607
theorem B2008539 : Blo 2007435 2008539 := bstep (se 1 (by rfl) ⟨1506404, by rfl⟩ : syracuseStep 2008539 = 3012809) B3012809
theorem B9161765 : Blo 2007435 9161765 := bbase (se 4 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 9161765 = 1717831) (by norm_num)
theorem B6107843 : Blo 2007435 6107843 := bstep (se 1 (by rfl) ⟨4580882, by rfl⟩ : syracuseStep 6107843 = 9161765) B9161765
theorem B16287581 : Blo 2007435 16287581 := bstep (se 3 (by rfl) ⟨3053921, by rfl⟩ : syracuseStep 16287581 = 6107843) B6107843
theorem B10858387 : Blo 2007435 10858387 := bstep (se 1 (by rfl) ⟨8143790, by rfl⟩ : syracuseStep 10858387 = 16287581) B16287581
theorem B14477849 : Blo 2007435 14477849 := bstep (se 2 (by rfl) ⟨5429193, by rfl⟩ : syracuseStep 14477849 = 10858387) B10858387
theorem B9651899 : Blo 2007435 9651899 := bstep (se 1 (by rfl) ⟨7238924, by rfl⟩ : syracuseStep 9651899 = 14477849) B14477849
theorem B6434599 : Blo 2007435 6434599 := bstep (se 1 (by rfl) ⟨4825949, by rfl⟩ : syracuseStep 6434599 = 9651899) B9651899
theorem B8579465 : Blo 2007435 8579465 := bstep (se 2 (by rfl) ⟨3217299, by rfl⟩ : syracuseStep 8579465 = 6434599) B6434599
theorem B5719643 : Blo 2007435 5719643 := bstep (se 1 (by rfl) ⟨4289732, by rfl⟩ : syracuseStep 5719643 = 8579465) B8579465
theorem B3813095 : Blo 2007435 3813095 := bstep (se 1 (by rfl) ⟨2859821, by rfl⟩ : syracuseStep 3813095 = 5719643) B5719643
theorem B10168253 : Blo 2007435 10168253 := bstep (se 3 (by rfl) ⟨1906547, by rfl⟩ : syracuseStep 10168253 = 3813095) B3813095
theorem B6778835 : Blo 2007435 6778835 := bstep (se 1 (by rfl) ⟨5084126, by rfl⟩ : syracuseStep 6778835 = 10168253) B10168253
theorem B4519223 : Blo 2007435 4519223 := bstep (se 1 (by rfl) ⟨3389417, by rfl⟩ : syracuseStep 4519223 = 6778835) B6778835
theorem B3012815 : Blo 2007435 3012815 := bstep (se 1 (by rfl) ⟨2259611, by rfl⟩ : syracuseStep 3012815 = 4519223) B4519223
theorem B2008543 : Blo 2007435 2008543 := bstep (se 1 (by rfl) ⟨1506407, by rfl⟩ : syracuseStep 2008543 = 3012815) B3012815
theorem B3012821 : Blo 2007435 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B2008547 : Blo 2007435 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B2412985 : Blo 2007435 2412985 := bbase (se 2 (by rfl) ⟨904869, by rfl⟩ : syracuseStep 2412985 = 1809739) (by norm_num)
theorem B3217313 : Blo 2007435 3217313 := bstep (se 2 (by rfl) ⟨1206492, by rfl⟩ : syracuseStep 3217313 = 2412985) B2412985
theorem B2144875 : Blo 2007435 2144875 := bstep (se 1 (by rfl) ⟨1608656, by rfl⟩ : syracuseStep 2144875 = 3217313) B3217313
theorem B2859833 : Blo 2007435 2859833 := bstep (se 2 (by rfl) ⟨1072437, by rfl⟩ : syracuseStep 2859833 = 2144875) B2144875
theorem B7626221 : Blo 2007435 7626221 := bstep (se 3 (by rfl) ⟨1429916, by rfl⟩ : syracuseStep 7626221 = 2859833) B2859833
theorem B5084147 : Blo 2007435 5084147 := bstep (se 1 (by rfl) ⟨3813110, by rfl⟩ : syracuseStep 5084147 = 7626221) B7626221
theorem B3389431 : Blo 2007435 3389431 := bstep (se 1 (by rfl) ⟨2542073, by rfl⟩ : syracuseStep 3389431 = 5084147) B5084147
theorem B4519241 : Blo 2007435 4519241 := bstep (se 2 (by rfl) ⟨1694715, by rfl⟩ : syracuseStep 4519241 = 3389431) B3389431
theorem B3012827 : Blo 2007435 3012827 := bstep (se 1 (by rfl) ⟨2259620, by rfl⟩ : syracuseStep 3012827 = 4519241) B4519241
theorem B2008551 : Blo 2007435 2008551 := bstep (se 1 (by rfl) ⟨1506413, by rfl⟩ : syracuseStep 2008551 = 3012827) B3012827
theorem B2259625 : Blo 2007435 2259625 := bbase (se 2 (by rfl) ⟨847359, by rfl⟩ : syracuseStep 2259625 = 1694719) (by norm_num)
theorem B3012833 : Blo 2007435 3012833 := bstep (se 2 (by rfl) ⟨1129812, by rfl⟩ : syracuseStep 3012833 = 2259625) B2259625
theorem B2008555 : Blo 2007435 2008555 := bstep (se 1 (by rfl) ⟨1506416, by rfl⟩ : syracuseStep 2008555 = 3012833) B3012833
theorem B3217325 : Blo 2007435 3217325 := bbase (se 3 (by rfl) ⟨603248, by rfl⟩ : syracuseStep 3217325 = 1206497) (by norm_num)
theorem B8579533 : Blo 2007435 8579533 := bstep (se 3 (by rfl) ⟨1608662, by rfl⟩ : syracuseStep 8579533 = 3217325) B3217325
theorem B11439377 : Blo 2007435 11439377 := bstep (se 2 (by rfl) ⟨4289766, by rfl⟩ : syracuseStep 11439377 = 8579533) B8579533
theorem B7626251 : Blo 2007435 7626251 := bstep (se 1 (by rfl) ⟨5719688, by rfl⟩ : syracuseStep 7626251 = 11439377) B11439377
theorem B5084167 : Blo 2007435 5084167 := bstep (se 1 (by rfl) ⟨3813125, by rfl⟩ : syracuseStep 5084167 = 7626251) B7626251
theorem B6778889 : Blo 2007435 6778889 := bstep (se 2 (by rfl) ⟨2542083, by rfl⟩ : syracuseStep 6778889 = 5084167) B5084167
theorem B4519259 : Blo 2007435 4519259 := bstep (se 1 (by rfl) ⟨3389444, by rfl⟩ : syracuseStep 4519259 = 6778889) B6778889
theorem B3012839 : Blo 2007435 3012839 := bstep (se 1 (by rfl) ⟨2259629, by rfl⟩ : syracuseStep 3012839 = 4519259) B4519259
theorem B2008559 : Blo 2007435 2008559 := bstep (se 1 (by rfl) ⟨1506419, by rfl⟩ : syracuseStep 2008559 = 3012839) B3012839
theorem B3012845 : Blo 2007435 3012845 := bbase (se 3 (by rfl) ⟨564908, by rfl⟩ : syracuseStep 3012845 = 1129817) (by norm_num)
theorem B2008563 : Blo 2007435 2008563 := bstep (se 1 (by rfl) ⟨1506422, by rfl⟩ : syracuseStep 2008563 = 3012845) B3012845
theorem B4519277 : Blo 2007435 4519277 := bbase (se 3 (by rfl) ⟨847364, by rfl⟩ : syracuseStep 4519277 = 1694729) (by norm_num)
theorem B3012851 : Blo 2007435 3012851 := bstep (se 1 (by rfl) ⟨2259638, by rfl⟩ : syracuseStep 3012851 = 4519277) B4519277
theorem B2008567 : Blo 2007435 2008567 := bstep (se 1 (by rfl) ⟨1506425, by rfl⟩ : syracuseStep 2008567 = 3012851) B3012851
theorem B3813149 : Blo 2007435 3813149 := bbase (se 3 (by rfl) ⟨714965, by rfl⟩ : syracuseStep 3813149 = 1429931) (by norm_num)
theorem B2542099 : Blo 2007435 2542099 := bstep (se 1 (by rfl) ⟨1906574, by rfl⟩ : syracuseStep 2542099 = 3813149) B3813149
theorem B3389465 : Blo 2007435 3389465 := bstep (se 2 (by rfl) ⟨1271049, by rfl⟩ : syracuseStep 3389465 = 2542099) B2542099
theorem B2259643 : Blo 2007435 2259643 := bstep (se 1 (by rfl) ⟨1694732, by rfl⟩ : syracuseStep 2259643 = 3389465) B3389465
theorem B3012857 : Blo 2007435 3012857 := bstep (se 2 (by rfl) ⟨1129821, by rfl⟩ : syracuseStep 3012857 = 2259643) B2259643
theorem B2008571 : Blo 2007435 2008571 := bstep (se 1 (by rfl) ⟨1506428, by rfl⟩ : syracuseStep 2008571 = 3012857) B3012857
theorem B3917917 : Blo 2007435 3917917 := bbase (se 3 (by rfl) ⟨734609, by rfl⟩ : syracuseStep 3917917 = 1469219) (by norm_num)
theorem B5223889 : Blo 2007435 5223889 := bstep (se 2 (by rfl) ⟨1958958, by rfl⟩ : syracuseStep 5223889 = 3917917) B3917917
theorem B6965185 : Blo 2007435 6965185 := bstep (se 2 (by rfl) ⟨2611944, by rfl⟩ : syracuseStep 6965185 = 5223889) B5223889
theorem B9286913 : Blo 2007435 9286913 := bstep (se 2 (by rfl) ⟨3482592, by rfl⟩ : syracuseStep 9286913 = 6965185) B6965185
theorem B6191275 : Blo 2007435 6191275 := bstep (se 1 (by rfl) ⟨4643456, by rfl⟩ : syracuseStep 6191275 = 9286913) B9286913
theorem B8255033 : Blo 2007435 8255033 := bstep (se 2 (by rfl) ⟨3095637, by rfl⟩ : syracuseStep 8255033 = 6191275) B6191275
theorem B5503355 : Blo 2007435 5503355 := bstep (se 1 (by rfl) ⟨4127516, by rfl⟩ : syracuseStep 5503355 = 8255033) B8255033
theorem B3668903 : Blo 2007435 3668903 := bstep (se 1 (by rfl) ⟨2751677, by rfl⟩ : syracuseStep 3668903 = 5503355) B5503355
theorem B2445935 : Blo 2007435 2445935 := bstep (se 1 (by rfl) ⟨1834451, by rfl⟩ : syracuseStep 2445935 = 3668903) B3668903
theorem B6522493 : Blo 2007435 6522493 := bstep (se 3 (by rfl) ⟨1222967, by rfl⟩ : syracuseStep 6522493 = 2445935) B2445935
theorem B8696657 : Blo 2007435 8696657 := bstep (se 2 (by rfl) ⟨3261246, by rfl⟩ : syracuseStep 8696657 = 6522493) B6522493
theorem B23191085 : Blo 2007435 23191085 := bstep (se 3 (by rfl) ⟨4348328, by rfl⟩ : syracuseStep 23191085 = 8696657) B8696657
theorem B15460723 : Blo 2007435 15460723 := bstep (se 1 (by rfl) ⟨11595542, by rfl⟩ : syracuseStep 15460723 = 23191085) B23191085
theorem B20614297 : Blo 2007435 20614297 := bstep (se 2 (by rfl) ⟨7730361, by rfl⟩ : syracuseStep 20614297 = 15460723) B15460723
theorem B27485729 : Blo 2007435 27485729 := bstep (se 2 (by rfl) ⟨10307148, by rfl⟩ : syracuseStep 27485729 = 20614297) B20614297
theorem B18323819 : Blo 2007435 18323819 := bstep (se 1 (by rfl) ⟨13742864, by rfl⟩ : syracuseStep 18323819 = 27485729) B27485729
theorem B12215879 : Blo 2007435 12215879 := bstep (se 1 (by rfl) ⟨9161909, by rfl⟩ : syracuseStep 12215879 = 18323819) B18323819
theorem B8143919 : Blo 2007435 8143919 := bstep (se 1 (by rfl) ⟨6107939, by rfl⟩ : syracuseStep 8143919 = 12215879) B12215879
theorem B5429279 : Blo 2007435 5429279 := bstep (se 1 (by rfl) ⟨4071959, by rfl⟩ : syracuseStep 5429279 = 8143919) B8143919
theorem B14478077 : Blo 2007435 14478077 := bstep (se 3 (by rfl) ⟨2714639, by rfl⟩ : syracuseStep 14478077 = 5429279) B5429279
theorem B9652051 : Blo 2007435 9652051 := bstep (se 1 (by rfl) ⟨7239038, by rfl⟩ : syracuseStep 9652051 = 14478077) B14478077
theorem B51477605 : Blo 2007435 51477605 := bstep (se 4 (by rfl) ⟨4826025, by rfl⟩ : syracuseStep 51477605 = 9652051) B9652051
theorem B34318403 : Blo 2007435 34318403 := bstep (se 1 (by rfl) ⟨25738802, by rfl⟩ : syracuseStep 34318403 = 51477605) B51477605
theorem B22878935 : Blo 2007435 22878935 := bstep (se 1 (by rfl) ⟨17159201, by rfl⟩ : syracuseStep 22878935 = 34318403) B34318403
theorem B15252623 : Blo 2007435 15252623 := bstep (se 1 (by rfl) ⟨11439467, by rfl⟩ : syracuseStep 15252623 = 22878935) B22878935
theorem B10168415 : Blo 2007435 10168415 := bstep (se 1 (by rfl) ⟨7626311, by rfl⟩ : syracuseStep 10168415 = 15252623) B15252623
theorem B6778943 : Blo 2007435 6778943 := bstep (se 1 (by rfl) ⟨5084207, by rfl⟩ : syracuseStep 6778943 = 10168415) B10168415
theorem B4519295 : Blo 2007435 4519295 := bstep (se 1 (by rfl) ⟨3389471, by rfl⟩ : syracuseStep 4519295 = 6778943) B6778943
theorem B3012863 : Blo 2007435 3012863 := bstep (se 1 (by rfl) ⟨2259647, by rfl⟩ : syracuseStep 3012863 = 4519295) B4519295
theorem B2008575 : Blo 2007435 2008575 := bstep (se 1 (by rfl) ⟨1506431, by rfl⟩ : syracuseStep 2008575 = 3012863) B3012863
theorem B3012869 : Blo 2007435 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B2008579 : Blo 2007435 2008579 := bstep (se 1 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 2008579 = 3012869) B3012869
theorem B3389485 : Blo 2007435 3389485 := bbase (se 3 (by rfl) ⟨635528, by rfl⟩ : syracuseStep 3389485 = 1271057) (by norm_num)
theorem B4519313 : Blo 2007435 4519313 := bstep (se 2 (by rfl) ⟨1694742, by rfl⟩ : syracuseStep 4519313 = 3389485) B3389485
theorem B3012875 : Blo 2007435 3012875 := bstep (se 1 (by rfl) ⟨2259656, by rfl⟩ : syracuseStep 3012875 = 4519313) B4519313
theorem B2008583 : Blo 2007435 2008583 := bstep (se 1 (by rfl) ⟨1506437, by rfl⟩ : syracuseStep 2008583 = 3012875) B3012875
theorem B2259661 : Blo 2007435 2259661 := bbase (se 3 (by rfl) ⟨423686, by rfl⟩ : syracuseStep 2259661 = 847373) (by norm_num)
theorem B3012881 : Blo 2007435 3012881 := bstep (se 2 (by rfl) ⟨1129830, by rfl⟩ : syracuseStep 3012881 = 2259661) B2259661
theorem B2008587 : Blo 2007435 2008587 := bstep (se 1 (by rfl) ⟨1506440, by rfl⟩ : syracuseStep 2008587 = 3012881) B3012881
theorem B6778997 : Blo 2007435 6778997 := bbase (se 5 (by rfl) ⟨317765, by rfl⟩ : syracuseStep 6778997 = 635531) (by norm_num)
theorem B4519331 : Blo 2007435 4519331 := bstep (se 1 (by rfl) ⟨3389498, by rfl⟩ : syracuseStep 4519331 = 6778997) B6778997
theorem B3012887 : Blo 2007435 3012887 := bstep (se 1 (by rfl) ⟨2259665, by rfl⟩ : syracuseStep 3012887 = 4519331) B4519331
theorem B2008591 : Blo 2007435 2008591 := bstep (se 1 (by rfl) ⟨1506443, by rfl⟩ : syracuseStep 2008591 = 3012887) B3012887
theorem B3012893 : Blo 2007435 3012893 := bbase (se 3 (by rfl) ⟨564917, by rfl⟩ : syracuseStep 3012893 = 1129835) (by norm_num)
theorem B2008595 : Blo 2007435 2008595 := bstep (se 1 (by rfl) ⟨1506446, by rfl⟩ : syracuseStep 2008595 = 3012893) B3012893
theorem B4519349 : Blo 2007435 4519349 := bbase (se 5 (by rfl) ⟨211844, by rfl⟩ : syracuseStep 4519349 = 423689) (by norm_num)
theorem B3012899 : Blo 2007435 3012899 := bstep (se 1 (by rfl) ⟨2259674, by rfl⟩ : syracuseStep 3012899 = 4519349) B4519349
theorem B2008599 : Blo 2007435 2008599 := bstep (se 1 (by rfl) ⟨1506449, by rfl⟩ : syracuseStep 2008599 = 3012899) B3012899
theorem B4289861 : Blo 2007435 4289861 := bbase (se 4 (by rfl) ⟨402174, by rfl⟩ : syracuseStep 4289861 = 804349) (by norm_num)
theorem B11439629 : Blo 2007435 11439629 := bstep (se 3 (by rfl) ⟨2144930, by rfl⟩ : syracuseStep 11439629 = 4289861) B4289861
theorem B7626419 : Blo 2007435 7626419 := bstep (se 1 (by rfl) ⟨5719814, by rfl⟩ : syracuseStep 7626419 = 11439629) B11439629
theorem B5084279 : Blo 2007435 5084279 := bstep (se 1 (by rfl) ⟨3813209, by rfl⟩ : syracuseStep 5084279 = 7626419) B7626419
theorem B3389519 : Blo 2007435 3389519 := bstep (se 1 (by rfl) ⟨2542139, by rfl⟩ : syracuseStep 3389519 = 5084279) B5084279
theorem B2259679 : Blo 2007435 2259679 := bstep (se 1 (by rfl) ⟨1694759, by rfl⟩ : syracuseStep 2259679 = 3389519) B3389519
theorem B3012905 : Blo 2007435 3012905 := bstep (se 2 (by rfl) ⟨1129839, by rfl⟩ : syracuseStep 3012905 = 2259679) B2259679
theorem B2008603 : Blo 2007435 2008603 := bstep (se 1 (by rfl) ⟨1506452, by rfl⟩ : syracuseStep 2008603 = 3012905) B3012905
theorem B4289869 : Blo 2007435 4289869 := bbase (se 3 (by rfl) ⟨804350, by rfl⟩ : syracuseStep 4289869 = 1608701) (by norm_num)
theorem B5719825 : Blo 2007435 5719825 := bstep (se 2 (by rfl) ⟨2144934, by rfl⟩ : syracuseStep 5719825 = 4289869) B4289869
theorem B7626433 : Blo 2007435 7626433 := bstep (se 2 (by rfl) ⟨2859912, by rfl⟩ : syracuseStep 7626433 = 5719825) B5719825
theorem B10168577 : Blo 2007435 10168577 := bstep (se 2 (by rfl) ⟨3813216, by rfl⟩ : syracuseStep 10168577 = 7626433) B7626433
theorem B6779051 : Blo 2007435 6779051 := bstep (se 1 (by rfl) ⟨5084288, by rfl⟩ : syracuseStep 6779051 = 10168577) B10168577
theorem B4519367 : Blo 2007435 4519367 := bstep (se 1 (by rfl) ⟨3389525, by rfl⟩ : syracuseStep 4519367 = 6779051) B6779051
theorem B3012911 : Blo 2007435 3012911 := bstep (se 1 (by rfl) ⟨2259683, by rfl⟩ : syracuseStep 3012911 = 4519367) B4519367
theorem B2008607 : Blo 2007435 2008607 := bstep (se 1 (by rfl) ⟨1506455, by rfl⟩ : syracuseStep 2008607 = 3012911) B3012911
theorem B3012917 : Blo 2007435 3012917 := bbase (se 5 (by rfl) ⟨141230, by rfl⟩ : syracuseStep 3012917 = 282461) (by norm_num)
theorem B2008611 : Blo 2007435 2008611 := bstep (se 1 (by rfl) ⟨1506458, by rfl⟩ : syracuseStep 2008611 = 3012917) B3012917
theorem B5084309 : Blo 2007435 5084309 := bbase (se 6 (by rfl) ⟨119163, by rfl⟩ : syracuseStep 5084309 = 238327) (by norm_num)
theorem B3389539 : Blo 2007435 3389539 := bstep (se 1 (by rfl) ⟨2542154, by rfl⟩ : syracuseStep 3389539 = 5084309) B5084309
theorem B4519385 : Blo 2007435 4519385 := bstep (se 2 (by rfl) ⟨1694769, by rfl⟩ : syracuseStep 4519385 = 3389539) B3389539
theorem B3012923 : Blo 2007435 3012923 := bstep (se 1 (by rfl) ⟨2259692, by rfl⟩ : syracuseStep 3012923 = 4519385) B4519385
theorem B2008615 : Blo 2007435 2008615 := bstep (se 1 (by rfl) ⟨1506461, by rfl⟩ : syracuseStep 2008615 = 3012923) B3012923
theorem B2259697 : Blo 2007435 2259697 := bbase (se 2 (by rfl) ⟨847386, by rfl⟩ : syracuseStep 2259697 = 1694773) (by norm_num)
theorem B3012929 : Blo 2007435 3012929 := bstep (se 2 (by rfl) ⟨1129848, by rfl⟩ : syracuseStep 3012929 = 2259697) B2259697
theorem B2008619 : Blo 2007435 2008619 := bstep (se 1 (by rfl) ⟨1506464, by rfl⟩ : syracuseStep 2008619 = 3012929) B3012929
theorem B7730549 : Blo 2007435 7730549 := bbase (se 5 (by rfl) ⟨362369, by rfl⟩ : syracuseStep 7730549 = 724739) (by norm_num)
theorem B5153699 : Blo 2007435 5153699 := bstep (se 1 (by rfl) ⟨3865274, by rfl⟩ : syracuseStep 5153699 = 7730549) B7730549
theorem B3435799 : Blo 2007435 3435799 := bstep (se 1 (by rfl) ⟨2576849, by rfl⟩ : syracuseStep 3435799 = 5153699) B5153699
theorem B4581065 : Blo 2007435 4581065 := bstep (se 2 (by rfl) ⟨1717899, by rfl⟩ : syracuseStep 4581065 = 3435799) B3435799
theorem B3054043 : Blo 2007435 3054043 := bstep (se 1 (by rfl) ⟨2290532, by rfl⟩ : syracuseStep 3054043 = 4581065) B4581065
theorem B16288229 : Blo 2007435 16288229 := bstep (se 4 (by rfl) ⟨1527021, by rfl⟩ : syracuseStep 16288229 = 3054043) B3054043
theorem B43435277 : Blo 2007435 43435277 := bstep (se 3 (by rfl) ⟨8144114, by rfl⟩ : syracuseStep 43435277 = 16288229) B16288229
theorem B28956851 : Blo 2007435 28956851 := bstep (se 1 (by rfl) ⟨21717638, by rfl⟩ : syracuseStep 28956851 = 43435277) B43435277
theorem B19304567 : Blo 2007435 19304567 := bstep (se 1 (by rfl) ⟨14478425, by rfl⟩ : syracuseStep 19304567 = 28956851) B28956851
theorem B12869711 : Blo 2007435 12869711 := bstep (se 1 (by rfl) ⟨9652283, by rfl⟩ : syracuseStep 12869711 = 19304567) B19304567
theorem B8579807 : Blo 2007435 8579807 := bstep (se 1 (by rfl) ⟨6434855, by rfl⟩ : syracuseStep 8579807 = 12869711) B12869711
theorem B5719871 : Blo 2007435 5719871 := bstep (se 1 (by rfl) ⟨4289903, by rfl⟩ : syracuseStep 5719871 = 8579807) B8579807
theorem B3813247 : Blo 2007435 3813247 := bstep (se 1 (by rfl) ⟨2859935, by rfl⟩ : syracuseStep 3813247 = 5719871) B5719871
theorem B5084329 : Blo 2007435 5084329 := bstep (se 2 (by rfl) ⟨1906623, by rfl⟩ : syracuseStep 5084329 = 3813247) B3813247
theorem B6779105 : Blo 2007435 6779105 := bstep (se 2 (by rfl) ⟨2542164, by rfl⟩ : syracuseStep 6779105 = 5084329) B5084329
theorem B4519403 : Blo 2007435 4519403 := bstep (se 1 (by rfl) ⟨3389552, by rfl⟩ : syracuseStep 4519403 = 6779105) B6779105
theorem B3012935 : Blo 2007435 3012935 := bstep (se 1 (by rfl) ⟨2259701, by rfl⟩ : syracuseStep 3012935 = 4519403) B4519403
theorem B2008623 : Blo 2007435 2008623 := bstep (se 1 (by rfl) ⟨1506467, by rfl⟩ : syracuseStep 2008623 = 3012935) B3012935
theorem B3012941 : Blo 2007435 3012941 := bbase (se 3 (by rfl) ⟨564926, by rfl⟩ : syracuseStep 3012941 = 1129853) (by norm_num)
theorem B2008627 : Blo 2007435 2008627 := bstep (se 1 (by rfl) ⟨1506470, by rfl⟩ : syracuseStep 2008627 = 3012941) B3012941
theorem B4519421 : Blo 2007435 4519421 := bbase (se 3 (by rfl) ⟨847391, by rfl⟩ : syracuseStep 4519421 = 1694783) (by norm_num)
theorem B3012947 : Blo 2007435 3012947 := bstep (se 1 (by rfl) ⟨2259710, by rfl⟩ : syracuseStep 3012947 = 4519421) B4519421
theorem B2008631 : Blo 2007435 2008631 := bstep (se 1 (by rfl) ⟨1506473, by rfl⟩ : syracuseStep 2008631 = 3012947) B3012947
theorem B3389573 : Blo 2007435 3389573 := bbase (se 4 (by rfl) ⟨317772, by rfl⟩ : syracuseStep 3389573 = 635545) (by norm_num)
theorem B2259715 : Blo 2007435 2259715 := bstep (se 1 (by rfl) ⟨1694786, by rfl⟩ : syracuseStep 2259715 = 3389573) B3389573
theorem B3012953 : Blo 2007435 3012953 := bstep (se 2 (by rfl) ⟨1129857, by rfl⟩ : syracuseStep 3012953 = 2259715) B2259715
theorem B2008635 : Blo 2007435 2008635 := bstep (se 1 (by rfl) ⟨1506476, by rfl⟩ : syracuseStep 2008635 = 3012953) B3012953
theorem B15253109 : Blo 2007435 15253109 := bbase (se 5 (by rfl) ⟨714989, by rfl⟩ : syracuseStep 15253109 = 1429979) (by norm_num)
theorem B10168739 : Blo 2007435 10168739 := bstep (se 1 (by rfl) ⟨7626554, by rfl⟩ : syracuseStep 10168739 = 15253109) B15253109
theorem B6779159 : Blo 2007435 6779159 := bstep (se 1 (by rfl) ⟨5084369, by rfl⟩ : syracuseStep 6779159 = 10168739) B10168739
theorem B4519439 : Blo 2007435 4519439 := bstep (se 1 (by rfl) ⟨3389579, by rfl⟩ : syracuseStep 4519439 = 6779159) B6779159
theorem B3012959 : Blo 2007435 3012959 := bstep (se 1 (by rfl) ⟨2259719, by rfl⟩ : syracuseStep 3012959 = 4519439) B4519439
theorem B2008639 : Blo 2007435 2008639 := bstep (se 1 (by rfl) ⟨1506479, by rfl⟩ : syracuseStep 2008639 = 3012959) B3012959
theorem B3012965 : Blo 2007435 3012965 := bbase (se 4 (by rfl) ⟨282465, by rfl⟩ : syracuseStep 3012965 = 564931) (by norm_num)
theorem B2008643 : Blo 2007435 2008643 := bstep (se 1 (by rfl) ⟨1506482, by rfl⟩ : syracuseStep 2008643 = 3012965) B3012965
theorem B3813293 : Blo 2007435 3813293 := bbase (se 3 (by rfl) ⟨714992, by rfl⟩ : syracuseStep 3813293 = 1429985) (by norm_num)
theorem B2542195 : Blo 2007435 2542195 := bstep (se 1 (by rfl) ⟨1906646, by rfl⟩ : syracuseStep 2542195 = 3813293) B3813293
theorem B3389593 : Blo 2007435 3389593 := bstep (se 2 (by rfl) ⟨1271097, by rfl⟩ : syracuseStep 3389593 = 2542195) B2542195
theorem B4519457 : Blo 2007435 4519457 := bstep (se 2 (by rfl) ⟨1694796, by rfl⟩ : syracuseStep 4519457 = 3389593) B3389593
theorem B3012971 : Blo 2007435 3012971 := bstep (se 1 (by rfl) ⟨2259728, by rfl⟩ : syracuseStep 3012971 = 4519457) B4519457
theorem B2008647 : Blo 2007435 2008647 := bstep (se 1 (by rfl) ⟨1506485, by rfl⟩ : syracuseStep 2008647 = 3012971) B3012971
theorem B2259733 : Blo 2007435 2259733 := bbase (se 6 (by rfl) ⟨52962, by rfl⟩ : syracuseStep 2259733 = 105925) (by norm_num)
theorem B3012977 : Blo 2007435 3012977 := bstep (se 2 (by rfl) ⟨1129866, by rfl⟩ : syracuseStep 3012977 = 2259733) B2259733
theorem B2008651 : Blo 2007435 2008651 := bstep (se 1 (by rfl) ⟨1506488, by rfl⟩ : syracuseStep 2008651 = 3012977) B3012977
theorem B2542205 : Blo 2007435 2542205 := bbase (se 3 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 2542205 = 953327) (by norm_num)
theorem B6779213 : Blo 2007435 6779213 := bstep (se 3 (by rfl) ⟨1271102, by rfl⟩ : syracuseStep 6779213 = 2542205) B2542205
theorem B4519475 : Blo 2007435 4519475 := bstep (se 1 (by rfl) ⟨3389606, by rfl⟩ : syracuseStep 4519475 = 6779213) B6779213
theorem B3012983 : Blo 2007435 3012983 := bstep (se 1 (by rfl) ⟨2259737, by rfl⟩ : syracuseStep 3012983 = 4519475) B4519475
theorem B2008655 : Blo 2007435 2008655 := bstep (se 1 (by rfl) ⟨1506491, by rfl⟩ : syracuseStep 2008655 = 3012983) B3012983
theorem B3012989 : Blo 2007435 3012989 := bbase (se 3 (by rfl) ⟨564935, by rfl⟩ : syracuseStep 3012989 = 1129871) (by norm_num)
theorem B2008659 : Blo 2007435 2008659 := bstep (se 1 (by rfl) ⟨1506494, by rfl⟩ : syracuseStep 2008659 = 3012989) B3012989
theorem B4519493 : Blo 2007435 4519493 := bbase (se 4 (by rfl) ⟨423702, by rfl⟩ : syracuseStep 4519493 = 847405) (by norm_num)
theorem B3012995 : Blo 2007435 3012995 := bstep (se 1 (by rfl) ⟨2259746, by rfl⟩ : syracuseStep 3012995 = 4519493) B4519493
theorem B2008663 : Blo 2007435 2008663 := bstep (se 1 (by rfl) ⟨1506497, by rfl⟩ : syracuseStep 2008663 = 3012995) B3012995
theorem B8697061 : Blo 2007435 8697061 := bbase (se 4 (by rfl) ⟨815349, by rfl⟩ : syracuseStep 8697061 = 1630699) (by norm_num)
theorem B46384325 : Blo 2007435 46384325 := bstep (se 4 (by rfl) ⟨4348530, by rfl⟩ : syracuseStep 46384325 = 8697061) B8697061
theorem B30922883 : Blo 2007435 30922883 := bstep (se 1 (by rfl) ⟨23192162, by rfl⟩ : syracuseStep 30922883 = 46384325) B46384325
theorem B20615255 : Blo 2007435 20615255 := bstep (se 1 (by rfl) ⟨15461441, by rfl⟩ : syracuseStep 20615255 = 30922883) B30922883
theorem B13743503 : Blo 2007435 13743503 := bstep (se 1 (by rfl) ⟨10307627, by rfl⟩ : syracuseStep 13743503 = 20615255) B20615255
theorem B9162335 : Blo 2007435 9162335 := bstep (se 1 (by rfl) ⟨6871751, by rfl⟩ : syracuseStep 9162335 = 13743503) B13743503
theorem B6108223 : Blo 2007435 6108223 := bstep (se 1 (by rfl) ⟨4581167, by rfl⟩ : syracuseStep 6108223 = 9162335) B9162335
theorem B8144297 : Blo 2007435 8144297 := bstep (se 2 (by rfl) ⟨3054111, by rfl⟩ : syracuseStep 8144297 = 6108223) B6108223
theorem B5429531 : Blo 2007435 5429531 := bstep (se 1 (by rfl) ⟨4072148, by rfl⟩ : syracuseStep 5429531 = 8144297) B8144297
theorem B3619687 : Blo 2007435 3619687 := bstep (se 1 (by rfl) ⟨2714765, by rfl⟩ : syracuseStep 3619687 = 5429531) B5429531
theorem B4826249 : Blo 2007435 4826249 := bstep (se 2 (by rfl) ⟨1809843, by rfl⟩ : syracuseStep 4826249 = 3619687) B3619687
theorem B3217499 : Blo 2007435 3217499 := bstep (se 1 (by rfl) ⟨2413124, by rfl⟩ : syracuseStep 3217499 = 4826249) B4826249
theorem B2144999 : Blo 2007435 2144999 := bstep (se 1 (by rfl) ⟨1608749, by rfl⟩ : syracuseStep 2144999 = 3217499) B3217499
theorem B5719997 : Blo 2007435 5719997 := bstep (se 3 (by rfl) ⟨1072499, by rfl⟩ : syracuseStep 5719997 = 2144999) B2144999
theorem B3813331 : Blo 2007435 3813331 := bstep (se 1 (by rfl) ⟨2859998, by rfl⟩ : syracuseStep 3813331 = 5719997) B5719997
theorem B5084441 : Blo 2007435 5084441 := bstep (se 2 (by rfl) ⟨1906665, by rfl⟩ : syracuseStep 5084441 = 3813331) B3813331
theorem B3389627 : Blo 2007435 3389627 := bstep (se 1 (by rfl) ⟨2542220, by rfl⟩ : syracuseStep 3389627 = 5084441) B5084441
theorem B2259751 : Blo 2007435 2259751 := bstep (se 1 (by rfl) ⟨1694813, by rfl⟩ : syracuseStep 2259751 = 3389627) B3389627
theorem B3013001 : Blo 2007435 3013001 := bstep (se 2 (by rfl) ⟨1129875, by rfl⟩ : syracuseStep 3013001 = 2259751) B2259751
theorem B2008667 : Blo 2007435 2008667 := bstep (se 1 (by rfl) ⟨1506500, by rfl⟩ : syracuseStep 2008667 = 3013001) B3013001
theorem B10168901 : Blo 2007435 10168901 := bbase (se 4 (by rfl) ⟨953334, by rfl⟩ : syracuseStep 10168901 = 1906669) (by norm_num)
theorem B6779267 : Blo 2007435 6779267 := bstep (se 1 (by rfl) ⟨5084450, by rfl⟩ : syracuseStep 6779267 = 10168901) B10168901
theorem B4519511 : Blo 2007435 4519511 := bstep (se 1 (by rfl) ⟨3389633, by rfl⟩ : syracuseStep 4519511 = 6779267) B6779267
theorem B3013007 : Blo 2007435 3013007 := bstep (se 1 (by rfl) ⟨2259755, by rfl⟩ : syracuseStep 3013007 = 4519511) B4519511
theorem B2008671 : Blo 2007435 2008671 := bstep (se 1 (by rfl) ⟨1506503, by rfl⟩ : syracuseStep 2008671 = 3013007) B3013007
theorem B3013013 : Blo 2007435 3013013 := bbase (se 6 (by rfl) ⟨70617, by rfl⟩ : syracuseStep 3013013 = 141235) (by norm_num)
theorem B2008675 : Blo 2007435 2008675 := bstep (se 1 (by rfl) ⟨1506506, by rfl⟩ : syracuseStep 2008675 = 3013013) B3013013
theorem B2899037 : Blo 2007435 2899037 := bbase (se 3 (by rfl) ⟨543569, by rfl⟩ : syracuseStep 2899037 = 1087139) (by norm_num)
theorem B7730765 : Blo 2007435 7730765 := bstep (se 3 (by rfl) ⟨1449518, by rfl⟩ : syracuseStep 7730765 = 2899037) B2899037
theorem B5153843 : Blo 2007435 5153843 := bstep (se 1 (by rfl) ⟨3865382, by rfl⟩ : syracuseStep 5153843 = 7730765) B7730765
theorem B3435895 : Blo 2007435 3435895 := bstep (se 1 (by rfl) ⟨2576921, by rfl⟩ : syracuseStep 3435895 = 5153843) B5153843
theorem B4581193 : Blo 2007435 4581193 := bstep (se 2 (by rfl) ⟨1717947, by rfl⟩ : syracuseStep 4581193 = 3435895) B3435895
theorem B6108257 : Blo 2007435 6108257 := bstep (se 2 (by rfl) ⟨2290596, by rfl⟩ : syracuseStep 6108257 = 4581193) B4581193
theorem B16288685 : Blo 2007435 16288685 := bstep (se 3 (by rfl) ⟨3054128, by rfl⟩ : syracuseStep 16288685 = 6108257) B6108257
theorem B10859123 : Blo 2007435 10859123 := bstep (se 1 (by rfl) ⟨8144342, by rfl⟩ : syracuseStep 10859123 = 16288685) B16288685
theorem B7239415 : Blo 2007435 7239415 := bstep (se 1 (by rfl) ⟨5429561, by rfl⟩ : syracuseStep 7239415 = 10859123) B10859123
theorem B9652553 : Blo 2007435 9652553 := bstep (se 2 (by rfl) ⟨3619707, by rfl⟩ : syracuseStep 9652553 = 7239415) B7239415
theorem B6435035 : Blo 2007435 6435035 := bstep (se 1 (by rfl) ⟨4826276, by rfl⟩ : syracuseStep 6435035 = 9652553) B9652553
theorem B4290023 : Blo 2007435 4290023 := bstep (se 1 (by rfl) ⟨3217517, by rfl⟩ : syracuseStep 4290023 = 6435035) B6435035
theorem B11440061 : Blo 2007435 11440061 := bstep (se 3 (by rfl) ⟨2145011, by rfl⟩ : syracuseStep 11440061 = 4290023) B4290023
theorem B7626707 : Blo 2007435 7626707 := bstep (se 1 (by rfl) ⟨5720030, by rfl⟩ : syracuseStep 7626707 = 11440061) B11440061
theorem B5084471 : Blo 2007435 5084471 := bstep (se 1 (by rfl) ⟨3813353, by rfl⟩ : syracuseStep 5084471 = 7626707) B7626707
theorem B3389647 : Blo 2007435 3389647 := bstep (se 1 (by rfl) ⟨2542235, by rfl⟩ : syracuseStep 3389647 = 5084471) B5084471
theorem B4519529 : Blo 2007435 4519529 := bstep (se 2 (by rfl) ⟨1694823, by rfl⟩ : syracuseStep 4519529 = 3389647) B3389647
theorem B3013019 : Blo 2007435 3013019 := bstep (se 1 (by rfl) ⟨2259764, by rfl⟩ : syracuseStep 3013019 = 4519529) B4519529
theorem B2008679 : Blo 2007435 2008679 := bstep (se 1 (by rfl) ⟨1506509, by rfl⟩ : syracuseStep 2008679 = 3013019) B3013019
theorem B2259769 : Blo 2007435 2259769 := bbase (se 2 (by rfl) ⟨847413, by rfl⟩ : syracuseStep 2259769 = 1694827) (by norm_num)
theorem B3013025 : Blo 2007435 3013025 := bstep (se 2 (by rfl) ⟨1129884, by rfl⟩ : syracuseStep 3013025 = 2259769) B2259769
theorem B2008683 : Blo 2007435 2008683 := bstep (se 1 (by rfl) ⟨1506512, by rfl⟩ : syracuseStep 2008683 = 3013025) B3013025
theorem B5720053 : Blo 2007435 5720053 := bbase (se 5 (by rfl) ⟨268127, by rfl⟩ : syracuseStep 5720053 = 536255) (by norm_num)
theorem B7626737 : Blo 2007435 7626737 := bstep (se 2 (by rfl) ⟨2860026, by rfl⟩ : syracuseStep 7626737 = 5720053) B5720053
theorem B5084491 : Blo 2007435 5084491 := bstep (se 1 (by rfl) ⟨3813368, by rfl⟩ : syracuseStep 5084491 = 7626737) B7626737
theorem B6779321 : Blo 2007435 6779321 := bstep (se 2 (by rfl) ⟨2542245, by rfl⟩ : syracuseStep 6779321 = 5084491) B5084491
theorem B4519547 : Blo 2007435 4519547 := bstep (se 1 (by rfl) ⟨3389660, by rfl⟩ : syracuseStep 4519547 = 6779321) B6779321
theorem B3013031 : Blo 2007435 3013031 := bstep (se 1 (by rfl) ⟨2259773, by rfl⟩ : syracuseStep 3013031 = 4519547) B4519547
theorem B2008687 : Blo 2007435 2008687 := bstep (se 1 (by rfl) ⟨1506515, by rfl⟩ : syracuseStep 2008687 = 3013031) B3013031
theorem B3013037 : Blo 2007435 3013037 := bbase (se 3 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 3013037 = 1129889) (by norm_num)
theorem B2008691 : Blo 2007435 2008691 := bstep (se 1 (by rfl) ⟨1506518, by rfl⟩ : syracuseStep 2008691 = 3013037) B3013037
theorem B4519565 : Blo 2007435 4519565 := bbase (se 3 (by rfl) ⟨847418, by rfl⟩ : syracuseStep 4519565 = 1694837) (by norm_num)
theorem B3013043 : Blo 2007435 3013043 := bstep (se 1 (by rfl) ⟨2259782, by rfl⟩ : syracuseStep 3013043 = 4519565) B4519565
theorem B2008695 : Blo 2007435 2008695 := bstep (se 1 (by rfl) ⟨1506521, by rfl⟩ : syracuseStep 2008695 = 3013043) B3013043
theorem B2542261 : Blo 2007435 2542261 := bbase (se 5 (by rfl) ⟨119168, by rfl⟩ : syracuseStep 2542261 = 238337) (by norm_num)
theorem B3389681 : Blo 2007435 3389681 := bstep (se 2 (by rfl) ⟨1271130, by rfl⟩ : syracuseStep 3389681 = 2542261) B2542261
theorem B2259787 : Blo 2007435 2259787 := bstep (se 1 (by rfl) ⟨1694840, by rfl⟩ : syracuseStep 2259787 = 3389681) B3389681
theorem B3013049 : Blo 2007435 3013049 := bstep (se 2 (by rfl) ⟨1129893, by rfl⟩ : syracuseStep 3013049 = 2259787) B2259787
theorem B2008699 : Blo 2007435 2008699 := bstep (se 1 (by rfl) ⟨1506524, by rfl⟩ : syracuseStep 2008699 = 3013049) B3013049
theorem B3482813 : Blo 2007435 3482813 := bbase (se 3 (by rfl) ⟨653027, by rfl⟩ : syracuseStep 3482813 = 1306055) (by norm_num)
theorem B2321875 : Blo 2007435 2321875 := bstep (se 1 (by rfl) ⟨1741406, by rfl⟩ : syracuseStep 2321875 = 3482813) B3482813
theorem B12383333 : Blo 2007435 12383333 := bstep (se 4 (by rfl) ⟨1160937, by rfl⟩ : syracuseStep 12383333 = 2321875) B2321875
theorem B8255555 : Blo 2007435 8255555 := bstep (se 1 (by rfl) ⟨6191666, by rfl⟩ : syracuseStep 8255555 = 12383333) B12383333
theorem B5503703 : Blo 2007435 5503703 := bstep (se 1 (by rfl) ⟨4127777, by rfl⟩ : syracuseStep 5503703 = 8255555) B8255555
theorem B58706165 : Blo 2007435 58706165 := bstep (se 5 (by rfl) ⟨2751851, by rfl⟩ : syracuseStep 58706165 = 5503703) B5503703
theorem B156549773 : Blo 2007435 156549773 := bstep (se 3 (by rfl) ⟨29353082, by rfl⟩ : syracuseStep 156549773 = 58706165) B58706165
theorem B104366515 : Blo 2007435 104366515 := bstep (se 1 (by rfl) ⟨78274886, by rfl⟩ : syracuseStep 104366515 = 156549773) B156549773
theorem B139155353 : Blo 2007435 139155353 := bstep (se 2 (by rfl) ⟨52183257, by rfl⟩ : syracuseStep 139155353 = 104366515) B104366515
theorem B92770235 : Blo 2007435 92770235 := bstep (se 1 (by rfl) ⟨69577676, by rfl⟩ : syracuseStep 92770235 = 139155353) B139155353
theorem B61846823 : Blo 2007435 61846823 := bstep (se 1 (by rfl) ⟨46385117, by rfl⟩ : syracuseStep 61846823 = 92770235) B92770235
theorem B41231215 : Blo 2007435 41231215 := bstep (se 1 (by rfl) ⟨30923411, by rfl⟩ : syracuseStep 41231215 = 61846823) B61846823
theorem B54974953 : Blo 2007435 54974953 := bstep (se 2 (by rfl) ⟨20615607, by rfl⟩ : syracuseStep 54974953 = 41231215) B41231215
theorem B73299937 : Blo 2007435 73299937 := bstep (se 2 (by rfl) ⟨27487476, by rfl⟩ : syracuseStep 73299937 = 54974953) B54974953
theorem B97733249 : Blo 2007435 97733249 := bstep (se 2 (by rfl) ⟨36649968, by rfl⟩ : syracuseStep 97733249 = 73299937) B73299937
theorem B65155499 : Blo 2007435 65155499 := bstep (se 1 (by rfl) ⟨48866624, by rfl⟩ : syracuseStep 65155499 = 97733249) B97733249
theorem B43436999 : Blo 2007435 43436999 := bstep (se 1 (by rfl) ⟨32577749, by rfl⟩ : syracuseStep 43436999 = 65155499) B65155499
theorem B28957999 : Blo 2007435 28957999 := bstep (se 1 (by rfl) ⟨21718499, by rfl⟩ : syracuseStep 28957999 = 43436999) B43436999
theorem B38610665 : Blo 2007435 38610665 := bstep (se 2 (by rfl) ⟨14478999, by rfl⟩ : syracuseStep 38610665 = 28957999) B28957999
theorem B25740443 : Blo 2007435 25740443 := bstep (se 1 (by rfl) ⟨19305332, by rfl⟩ : syracuseStep 25740443 = 38610665) B38610665
theorem B17160295 : Blo 2007435 17160295 := bstep (se 1 (by rfl) ⟨12870221, by rfl⟩ : syracuseStep 17160295 = 25740443) B25740443
theorem B22880393 : Blo 2007435 22880393 := bstep (se 2 (by rfl) ⟨8580147, by rfl⟩ : syracuseStep 22880393 = 17160295) B17160295
theorem B15253595 : Blo 2007435 15253595 := bstep (se 1 (by rfl) ⟨11440196, by rfl⟩ : syracuseStep 15253595 = 22880393) B22880393
theorem B10169063 : Blo 2007435 10169063 := bstep (se 1 (by rfl) ⟨7626797, by rfl⟩ : syracuseStep 10169063 = 15253595) B15253595
theorem B6779375 : Blo 2007435 6779375 := bstep (se 1 (by rfl) ⟨5084531, by rfl⟩ : syracuseStep 6779375 = 10169063) B10169063
theorem B4519583 : Blo 2007435 4519583 := bstep (se 1 (by rfl) ⟨3389687, by rfl⟩ : syracuseStep 4519583 = 6779375) B6779375
theorem B3013055 : Blo 2007435 3013055 := bstep (se 1 (by rfl) ⟨2259791, by rfl⟩ : syracuseStep 3013055 = 4519583) B4519583
theorem B2008703 : Blo 2007435 2008703 := bstep (se 1 (by rfl) ⟨1506527, by rfl⟩ : syracuseStep 2008703 = 3013055) B3013055
theorem B3013061 : Blo 2007435 3013061 := bbase (se 4 (by rfl) ⟨282474, by rfl⟩ : syracuseStep 3013061 = 564949) (by norm_num)
theorem B2008707 : Blo 2007435 2008707 := bstep (se 1 (by rfl) ⟨1506530, by rfl⟩ : syracuseStep 2008707 = 3013061) B3013061
theorem B3389701 : Blo 2007435 3389701 := bbase (se 4 (by rfl) ⟨317784, by rfl⟩ : syracuseStep 3389701 = 635569) (by norm_num)
theorem B4519601 : Blo 2007435 4519601 := bstep (se 2 (by rfl) ⟨1694850, by rfl⟩ : syracuseStep 4519601 = 3389701) B3389701
theorem B3013067 : Blo 2007435 3013067 := bstep (se 1 (by rfl) ⟨2259800, by rfl⟩ : syracuseStep 3013067 = 4519601) B4519601
theorem B2008711 : Blo 2007435 2008711 := bstep (se 1 (by rfl) ⟨1506533, by rfl⟩ : syracuseStep 2008711 = 3013067) B3013067
theorem B2259805 : Blo 2007435 2259805 := bbase (se 3 (by rfl) ⟨423713, by rfl⟩ : syracuseStep 2259805 = 847427) (by norm_num)
theorem B3013073 : Blo 2007435 3013073 := bstep (se 2 (by rfl) ⟨1129902, by rfl⟩ : syracuseStep 3013073 = 2259805) B2259805
theorem B2008715 : Blo 2007435 2008715 := bstep (se 1 (by rfl) ⟨1506536, by rfl⟩ : syracuseStep 2008715 = 3013073) B3013073
theorem B6779429 : Blo 2007435 6779429 := bbase (se 4 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 6779429 = 1271143) (by norm_num)
theorem B4519619 : Blo 2007435 4519619 := bstep (se 1 (by rfl) ⟨3389714, by rfl⟩ : syracuseStep 4519619 = 6779429) B6779429
theorem B3013079 : Blo 2007435 3013079 := bstep (se 1 (by rfl) ⟨2259809, by rfl⟩ : syracuseStep 3013079 = 4519619) B4519619
theorem B2008719 : Blo 2007435 2008719 := bstep (se 1 (by rfl) ⟨1506539, by rfl⟩ : syracuseStep 2008719 = 3013079) B3013079
theorem B3013085 : Blo 2007435 3013085 := bbase (se 3 (by rfl) ⟨564953, by rfl⟩ : syracuseStep 3013085 = 1129907) (by norm_num)
theorem B2008723 : Blo 2007435 2008723 := bstep (se 1 (by rfl) ⟨1506542, by rfl⟩ : syracuseStep 2008723 = 3013085) B3013085
theorem B4519637 : Blo 2007435 4519637 := bbase (se 7 (by rfl) ⟨52964, by rfl⟩ : syracuseStep 4519637 = 105929) (by norm_num)
theorem B3013091 : Blo 2007435 3013091 := bstep (se 1 (by rfl) ⟨2259818, by rfl⟩ : syracuseStep 3013091 = 4519637) B4519637
theorem B2008727 : Blo 2007435 2008727 := bstep (se 1 (by rfl) ⟨1506545, by rfl⟩ : syracuseStep 2008727 = 3013091) B3013091
theorem B2413201 : Blo 2007435 2413201 := bbase (se 2 (by rfl) ⟨904950, by rfl⟩ : syracuseStep 2413201 = 1809901) (by norm_num)
theorem B3217601 : Blo 2007435 3217601 := bstep (se 2 (by rfl) ⟨1206600, by rfl⟩ : syracuseStep 3217601 = 2413201) B2413201
theorem B8580269 : Blo 2007435 8580269 := bstep (se 3 (by rfl) ⟨1608800, by rfl⟩ : syracuseStep 8580269 = 3217601) B3217601
theorem B5720179 : Blo 2007435 5720179 := bstep (se 1 (by rfl) ⟨4290134, by rfl⟩ : syracuseStep 5720179 = 8580269) B8580269
theorem B7626905 : Blo 2007435 7626905 := bstep (se 2 (by rfl) ⟨2860089, by rfl⟩ : syracuseStep 7626905 = 5720179) B5720179
theorem B5084603 : Blo 2007435 5084603 := bstep (se 1 (by rfl) ⟨3813452, by rfl⟩ : syracuseStep 5084603 = 7626905) B7626905
theorem B3389735 : Blo 2007435 3389735 := bstep (se 1 (by rfl) ⟨2542301, by rfl⟩ : syracuseStep 3389735 = 5084603) B5084603
theorem B2259823 : Blo 2007435 2259823 := bstep (se 1 (by rfl) ⟨1694867, by rfl⟩ : syracuseStep 2259823 = 3389735) B3389735
theorem B3013097 : Blo 2007435 3013097 := bstep (se 2 (by rfl) ⟨1129911, by rfl⟩ : syracuseStep 3013097 = 2259823) B2259823
theorem B2008731 : Blo 2007435 2008731 := bstep (se 1 (by rfl) ⟨1506548, by rfl⟩ : syracuseStep 2008731 = 3013097) B3013097
theorem B8697349 : Blo 2007435 8697349 := bbase (se 4 (by rfl) ⟨815376, by rfl⟩ : syracuseStep 8697349 = 1630753) (by norm_num)
theorem B11596465 : Blo 2007435 11596465 := bstep (se 2 (by rfl) ⟨4348674, by rfl⟩ : syracuseStep 11596465 = 8697349) B8697349
theorem B61847813 : Blo 2007435 61847813 := bstep (se 4 (by rfl) ⟨5798232, by rfl⟩ : syracuseStep 61847813 = 11596465) B11596465
theorem B164927501 : Blo 2007435 164927501 := bstep (se 3 (by rfl) ⟨30923906, by rfl⟩ : syracuseStep 164927501 = 61847813) B61847813
theorem B109951667 : Blo 2007435 109951667 := bstep (se 1 (by rfl) ⟨82463750, by rfl⟩ : syracuseStep 109951667 = 164927501) B164927501
theorem B73301111 : Blo 2007435 73301111 := bstep (se 1 (by rfl) ⟨54975833, by rfl⟩ : syracuseStep 73301111 = 109951667) B109951667
theorem B48867407 : Blo 2007435 48867407 := bstep (se 1 (by rfl) ⟨36650555, by rfl⟩ : syracuseStep 48867407 = 73301111) B73301111
theorem B32578271 : Blo 2007435 32578271 := bstep (se 1 (by rfl) ⟨24433703, by rfl⟩ : syracuseStep 32578271 = 48867407) B48867407
theorem B21718847 : Blo 2007435 21718847 := bstep (se 1 (by rfl) ⟨16289135, by rfl⟩ : syracuseStep 21718847 = 32578271) B32578271
theorem B14479231 : Blo 2007435 14479231 := bstep (se 1 (by rfl) ⟨10859423, by rfl⟩ : syracuseStep 14479231 = 21718847) B21718847
theorem B19305641 : Blo 2007435 19305641 := bstep (se 2 (by rfl) ⟨7239615, by rfl⟩ : syracuseStep 19305641 = 14479231) B14479231
theorem B12870427 : Blo 2007435 12870427 := bstep (se 1 (by rfl) ⟨9652820, by rfl⟩ : syracuseStep 12870427 = 19305641) B19305641
theorem B17160569 : Blo 2007435 17160569 := bstep (se 2 (by rfl) ⟨6435213, by rfl⟩ : syracuseStep 17160569 = 12870427) B12870427
theorem B11440379 : Blo 2007435 11440379 := bstep (se 1 (by rfl) ⟨8580284, by rfl⟩ : syracuseStep 11440379 = 17160569) B17160569
theorem B7626919 : Blo 2007435 7626919 := bstep (se 1 (by rfl) ⟨5720189, by rfl⟩ : syracuseStep 7626919 = 11440379) B11440379
theorem B10169225 : Blo 2007435 10169225 := bstep (se 2 (by rfl) ⟨3813459, by rfl⟩ : syracuseStep 10169225 = 7626919) B7626919
theorem B6779483 : Blo 2007435 6779483 := bstep (se 1 (by rfl) ⟨5084612, by rfl⟩ : syracuseStep 6779483 = 10169225) B10169225
theorem B4519655 : Blo 2007435 4519655 := bstep (se 1 (by rfl) ⟨3389741, by rfl⟩ : syracuseStep 4519655 = 6779483) B6779483
theorem B3013103 : Blo 2007435 3013103 := bstep (se 1 (by rfl) ⟨2259827, by rfl⟩ : syracuseStep 3013103 = 4519655) B4519655
theorem B2008735 : Blo 2007435 2008735 := bstep (se 1 (by rfl) ⟨1506551, by rfl⟩ : syracuseStep 2008735 = 3013103) B3013103
theorem B3013109 : Blo 2007435 3013109 := bbase (se 5 (by rfl) ⟨141239, by rfl⟩ : syracuseStep 3013109 = 282479) (by norm_num)
theorem B2008739 : Blo 2007435 2008739 := bstep (se 1 (by rfl) ⟨1506554, by rfl⟩ : syracuseStep 2008739 = 3013109) B3013109
theorem B5720213 : Blo 2007435 5720213 := bbase (se 6 (by rfl) ⟨134067, by rfl⟩ : syracuseStep 5720213 = 268135) (by norm_num)
theorem B3813475 : Blo 2007435 3813475 := bstep (se 1 (by rfl) ⟨2860106, by rfl⟩ : syracuseStep 3813475 = 5720213) B5720213
theorem B5084633 : Blo 2007435 5084633 := bstep (se 2 (by rfl) ⟨1906737, by rfl⟩ : syracuseStep 5084633 = 3813475) B3813475
theorem B3389755 : Blo 2007435 3389755 := bstep (se 1 (by rfl) ⟨2542316, by rfl⟩ : syracuseStep 3389755 = 5084633) B5084633
theorem B4519673 : Blo 2007435 4519673 := bstep (se 2 (by rfl) ⟨1694877, by rfl⟩ : syracuseStep 4519673 = 3389755) B3389755
theorem B3013115 : Blo 2007435 3013115 := bstep (se 1 (by rfl) ⟨2259836, by rfl⟩ : syracuseStep 3013115 = 4519673) B4519673
theorem B2008743 : Blo 2007435 2008743 := bstep (se 1 (by rfl) ⟨1506557, by rfl⟩ : syracuseStep 2008743 = 3013115) B3013115
theorem B2259841 : Blo 2007435 2259841 := bbase (se 2 (by rfl) ⟨847440, by rfl⟩ : syracuseStep 2259841 = 1694881) (by norm_num)
theorem B3013121 : Blo 2007435 3013121 := bstep (se 2 (by rfl) ⟨1129920, by rfl⟩ : syracuseStep 3013121 = 2259841) B2259841
theorem B2008747 : Blo 2007435 2008747 := bstep (se 1 (by rfl) ⟨1506560, by rfl⟩ : syracuseStep 2008747 = 3013121) B3013121
theorem B5084653 : Blo 2007435 5084653 := bbase (se 3 (by rfl) ⟨953372, by rfl⟩ : syracuseStep 5084653 = 1906745) (by norm_num)
theorem B6779537 : Blo 2007435 6779537 := bstep (se 2 (by rfl) ⟨2542326, by rfl⟩ : syracuseStep 6779537 = 5084653) B5084653
theorem B4519691 : Blo 2007435 4519691 := bstep (se 1 (by rfl) ⟨3389768, by rfl⟩ : syracuseStep 4519691 = 6779537) B6779537
theorem B3013127 : Blo 2007435 3013127 := bstep (se 1 (by rfl) ⟨2259845, by rfl⟩ : syracuseStep 3013127 = 4519691) B4519691
theorem B2008751 : Blo 2007435 2008751 := bstep (se 1 (by rfl) ⟨1506563, by rfl⟩ : syracuseStep 2008751 = 3013127) B3013127
theorem B3013133 : Blo 2007435 3013133 := bbase (se 3 (by rfl) ⟨564962, by rfl⟩ : syracuseStep 3013133 = 1129925) (by norm_num)
theorem B2008755 : Blo 2007435 2008755 := bstep (se 1 (by rfl) ⟨1506566, by rfl⟩ : syracuseStep 2008755 = 3013133) B3013133
theorem B4519709 : Blo 2007435 4519709 := bbase (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) (by norm_num)
theorem B3013139 : Blo 2007435 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B2008759 : Blo 2007435 2008759 := bstep (se 1 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 2008759 = 3013139) B3013139
theorem B3389789 : Blo 2007435 3389789 := bbase (se 3 (by rfl) ⟨635585, by rfl⟩ : syracuseStep 3389789 = 1271171) (by norm_num)
theorem B2259859 : Blo 2007435 2259859 := bstep (se 1 (by rfl) ⟨1694894, by rfl⟩ : syracuseStep 2259859 = 3389789) B3389789
theorem B3013145 : Blo 2007435 3013145 := bstep (se 2 (by rfl) ⟨1129929, by rfl⟩ : syracuseStep 3013145 = 2259859) B2259859
theorem B2008763 : Blo 2007435 2008763 := bstep (se 1 (by rfl) ⟨1506572, by rfl⟩ : syracuseStep 2008763 = 3013145) B3013145
theorem B8580421 : Blo 2007435 8580421 := bbase (se 4 (by rfl) ⟨804414, by rfl⟩ : syracuseStep 8580421 = 1608829) (by norm_num)
theorem B11440561 : Blo 2007435 11440561 := bstep (se 2 (by rfl) ⟨4290210, by rfl⟩ : syracuseStep 11440561 = 8580421) B8580421
theorem B15254081 : Blo 2007435 15254081 := bstep (se 2 (by rfl) ⟨5720280, by rfl⟩ : syracuseStep 15254081 = 11440561) B11440561
theorem B10169387 : Blo 2007435 10169387 := bstep (se 1 (by rfl) ⟨7627040, by rfl⟩ : syracuseStep 10169387 = 15254081) B15254081
theorem B6779591 : Blo 2007435 6779591 := bstep (se 1 (by rfl) ⟨5084693, by rfl⟩ : syracuseStep 6779591 = 10169387) B10169387
theorem B4519727 : Blo 2007435 4519727 := bstep (se 1 (by rfl) ⟨3389795, by rfl⟩ : syracuseStep 4519727 = 6779591) B6779591
theorem B3013151 : Blo 2007435 3013151 := bstep (se 1 (by rfl) ⟨2259863, by rfl⟩ : syracuseStep 3013151 = 4519727) B4519727
theorem B2008767 : Blo 2007435 2008767 := bstep (se 1 (by rfl) ⟨1506575, by rfl⟩ : syracuseStep 2008767 = 3013151) B3013151
theorem B3013157 : Blo 2007435 3013157 := bbase (se 4 (by rfl) ⟨282483, by rfl⟩ : syracuseStep 3013157 = 564967) (by norm_num)
theorem B2008771 : Blo 2007435 2008771 := bstep (se 1 (by rfl) ⟨1506578, by rfl⟩ : syracuseStep 2008771 = 3013157) B3013157
theorem B2542357 : Blo 2007435 2542357 := bbase (se 6 (by rfl) ⟨59586, by rfl⟩ : syracuseStep 2542357 = 119173) (by norm_num)
theorem B3389809 : Blo 2007435 3389809 := bstep (se 2 (by rfl) ⟨1271178, by rfl⟩ : syracuseStep 3389809 = 2542357) B2542357
theorem B4519745 : Blo 2007435 4519745 := bstep (se 2 (by rfl) ⟨1694904, by rfl⟩ : syracuseStep 4519745 = 3389809) B3389809
theorem B3013163 : Blo 2007435 3013163 := bstep (se 1 (by rfl) ⟨2259872, by rfl⟩ : syracuseStep 3013163 = 4519745) B4519745
theorem B2008775 : Blo 2007435 2008775 := bstep (se 1 (by rfl) ⟨1506581, by rfl⟩ : syracuseStep 2008775 = 3013163) B3013163
theorem B2259877 : Blo 2007435 2259877 := bbase (se 4 (by rfl) ⟨211863, by rfl⟩ : syracuseStep 2259877 = 423727) (by norm_num)
theorem B3013169 : Blo 2007435 3013169 := bstep (se 2 (by rfl) ⟨1129938, by rfl⟩ : syracuseStep 3013169 = 2259877) B2259877
theorem B2008779 : Blo 2007435 2008779 := bstep (se 1 (by rfl) ⟨1506584, by rfl⟩ : syracuseStep 2008779 = 3013169) B3013169
theorem B6965909 : Blo 2007435 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B4643939 : Blo 2007435 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B12383837 : Blo 2007435 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B8255891 : Blo 2007435 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B22015709 : Blo 2007435 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B14677139 : Blo 2007435 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B9784759 : Blo 2007435 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B13046345 : Blo 2007435 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B8697563 : Blo 2007435 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B5798375 : Blo 2007435 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B3865583 : Blo 2007435 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B10308221 : Blo 2007435 10308221 := bstep (se 3 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 10308221 = 3865583) B3865583
theorem B6872147 : Blo 2007435 6872147 := bstep (se 1 (by rfl) ⟨5154110, by rfl⟩ : syracuseStep 6872147 = 10308221) B10308221
theorem B4581431 : Blo 2007435 4581431 := bstep (se 1 (by rfl) ⟨3436073, by rfl⟩ : syracuseStep 4581431 = 6872147) B6872147
theorem B3054287 : Blo 2007435 3054287 := bstep (se 1 (by rfl) ⟨2290715, by rfl⟩ : syracuseStep 3054287 = 4581431) B4581431
theorem B8144765 : Blo 2007435 8144765 := bstep (se 3 (by rfl) ⟨1527143, by rfl⟩ : syracuseStep 8144765 = 3054287) B3054287
theorem B5429843 : Blo 2007435 5429843 := bstep (se 1 (by rfl) ⟨4072382, by rfl⟩ : syracuseStep 5429843 = 8144765) B8144765
theorem B3619895 : Blo 2007435 3619895 := bstep (se 1 (by rfl) ⟨2714921, by rfl⟩ : syracuseStep 3619895 = 5429843) B5429843
theorem B9653053 : Blo 2007435 9653053 := bstep (se 3 (by rfl) ⟨1809947, by rfl⟩ : syracuseStep 9653053 = 3619895) B3619895
theorem B12870737 : Blo 2007435 12870737 := bstep (se 2 (by rfl) ⟨4826526, by rfl⟩ : syracuseStep 12870737 = 9653053) B9653053
theorem B8580491 : Blo 2007435 8580491 := bstep (se 1 (by rfl) ⟨6435368, by rfl⟩ : syracuseStep 8580491 = 12870737) B12870737
theorem B5720327 : Blo 2007435 5720327 := bstep (se 1 (by rfl) ⟨4290245, by rfl⟩ : syracuseStep 5720327 = 8580491) B8580491
theorem B3813551 : Blo 2007435 3813551 := bstep (se 1 (by rfl) ⟨2860163, by rfl⟩ : syracuseStep 3813551 = 5720327) B5720327
theorem B2542367 : Blo 2007435 2542367 := bstep (se 1 (by rfl) ⟨1906775, by rfl⟩ : syracuseStep 2542367 = 3813551) B3813551
theorem B6779645 : Blo 2007435 6779645 := bstep (se 3 (by rfl) ⟨1271183, by rfl⟩ : syracuseStep 6779645 = 2542367) B2542367
theorem B4519763 : Blo 2007435 4519763 := bstep (se 1 (by rfl) ⟨3389822, by rfl⟩ : syracuseStep 4519763 = 6779645) B6779645
theorem B3013175 : Blo 2007435 3013175 := bstep (se 1 (by rfl) ⟨2259881, by rfl⟩ : syracuseStep 3013175 = 4519763) B4519763
theorem B2008783 : Blo 2007435 2008783 := bstep (se 1 (by rfl) ⟨1506587, by rfl⟩ : syracuseStep 2008783 = 3013175) B3013175
theorem B3013181 : Blo 2007435 3013181 := bbase (se 3 (by rfl) ⟨564971, by rfl⟩ : syracuseStep 3013181 = 1129943) (by norm_num)
theorem B2008787 : Blo 2007435 2008787 := bstep (se 1 (by rfl) ⟨1506590, by rfl⟩ : syracuseStep 2008787 = 3013181) B3013181
theorem B4519781 : Blo 2007435 4519781 := bbase (se 4 (by rfl) ⟨423729, by rfl⟩ : syracuseStep 4519781 = 847459) (by norm_num)
theorem B3013187 : Blo 2007435 3013187 := bstep (se 1 (by rfl) ⟨2259890, by rfl⟩ : syracuseStep 3013187 = 4519781) B4519781
theorem B2008791 : Blo 2007435 2008791 := bstep (se 1 (by rfl) ⟨1506593, by rfl⟩ : syracuseStep 2008791 = 3013187) B3013187
theorem B5084765 : Blo 2007435 5084765 := bbase (se 3 (by rfl) ⟨953393, by rfl⟩ : syracuseStep 5084765 = 1906787) (by norm_num)
theorem B3389843 : Blo 2007435 3389843 := bstep (se 1 (by rfl) ⟨2542382, by rfl⟩ : syracuseStep 3389843 = 5084765) B5084765
theorem B2259895 : Blo 2007435 2259895 := bstep (se 1 (by rfl) ⟨1694921, by rfl⟩ : syracuseStep 2259895 = 3389843) B3389843
theorem B3013193 : Blo 2007435 3013193 := bstep (se 2 (by rfl) ⟨1129947, by rfl⟩ : syracuseStep 3013193 = 2259895) B2259895
theorem B2008795 : Blo 2007435 2008795 := bstep (se 1 (by rfl) ⟨1506596, by rfl⟩ : syracuseStep 2008795 = 3013193) B3013193
theorem B3813581 : Blo 2007435 3813581 := bbase (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) (by norm_num)
theorem B10169549 : Blo 2007435 10169549 := bstep (se 3 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 10169549 = 3813581) B3813581
theorem B6779699 : Blo 2007435 6779699 := bstep (se 1 (by rfl) ⟨5084774, by rfl⟩ : syracuseStep 6779699 = 10169549) B10169549
theorem B4519799 : Blo 2007435 4519799 := bstep (se 1 (by rfl) ⟨3389849, by rfl⟩ : syracuseStep 4519799 = 6779699) B6779699
theorem B3013199 : Blo 2007435 3013199 := bstep (se 1 (by rfl) ⟨2259899, by rfl⟩ : syracuseStep 3013199 = 4519799) B4519799
theorem B2008799 : Blo 2007435 2008799 := bstep (se 1 (by rfl) ⟨1506599, by rfl⟩ : syracuseStep 2008799 = 3013199) B3013199
theorem B3013205 : Blo 2007435 3013205 := bbase (se 8 (by rfl) ⟨17655, by rfl⟩ : syracuseStep 3013205 = 35311) (by norm_num)
theorem B2008803 : Blo 2007435 2008803 := bstep (se 1 (by rfl) ⟨1506602, by rfl⟩ : syracuseStep 2008803 = 3013205) B3013205
theorem B6435445 : Blo 2007435 6435445 := bbase (se 5 (by rfl) ⟨301661, by rfl⟩ : syracuseStep 6435445 = 603323) (by norm_num)
theorem B8580593 : Blo 2007435 8580593 := bstep (se 2 (by rfl) ⟨3217722, by rfl⟩ : syracuseStep 8580593 = 6435445) B6435445
theorem B5720395 : Blo 2007435 5720395 := bstep (se 1 (by rfl) ⟨4290296, by rfl⟩ : syracuseStep 5720395 = 8580593) B8580593
theorem B7627193 : Blo 2007435 7627193 := bstep (se 2 (by rfl) ⟨2860197, by rfl⟩ : syracuseStep 7627193 = 5720395) B5720395
theorem B5084795 : Blo 2007435 5084795 := bstep (se 1 (by rfl) ⟨3813596, by rfl⟩ : syracuseStep 5084795 = 7627193) B7627193
theorem B3389863 : Blo 2007435 3389863 := bstep (se 1 (by rfl) ⟨2542397, by rfl⟩ : syracuseStep 3389863 = 5084795) B5084795
theorem B4519817 : Blo 2007435 4519817 := bstep (se 2 (by rfl) ⟨1694931, by rfl⟩ : syracuseStep 4519817 = 3389863) B3389863
theorem B3013211 : Blo 2007435 3013211 := bstep (se 1 (by rfl) ⟨2259908, by rfl⟩ : syracuseStep 3013211 = 4519817) B4519817
theorem B2008807 : Blo 2007435 2008807 := bstep (se 1 (by rfl) ⟨1506605, by rfl⟩ : syracuseStep 2008807 = 3013211) B3013211
theorem B2259913 : Blo 2007435 2259913 := bbase (se 2 (by rfl) ⟨847467, by rfl⟩ : syracuseStep 2259913 = 1694935) (by norm_num)
theorem B3013217 : Blo 2007435 3013217 := bstep (se 2 (by rfl) ⟨1129956, by rfl⟩ : syracuseStep 3013217 = 2259913) B2259913
theorem B2008811 : Blo 2007435 2008811 := bstep (se 1 (by rfl) ⟨1506608, by rfl⟩ : syracuseStep 2008811 = 3013217) B3013217
theorem B2938789 : Blo 2007435 2938789 := bbase (se 4 (by rfl) ⟨275511, by rfl⟩ : syracuseStep 2938789 = 551023) (by norm_num)
theorem B3918385 : Blo 2007435 3918385 := bstep (se 2 (by rfl) ⟨1469394, by rfl⟩ : syracuseStep 3918385 = 2938789) B2938789
theorem B5224513 : Blo 2007435 5224513 := bstep (se 2 (by rfl) ⟨1959192, by rfl⟩ : syracuseStep 5224513 = 3918385) B3918385
theorem B6966017 : Blo 2007435 6966017 := bstep (se 2 (by rfl) ⟨2612256, by rfl⟩ : syracuseStep 6966017 = 5224513) B5224513
theorem B4644011 : Blo 2007435 4644011 := bstep (se 1 (by rfl) ⟨3483008, by rfl⟩ : syracuseStep 4644011 = 6966017) B6966017
theorem B12384029 : Blo 2007435 12384029 := bstep (se 3 (by rfl) ⟨2322005, by rfl⟩ : syracuseStep 12384029 = 4644011) B4644011
theorem B33024077 : Blo 2007435 33024077 := bstep (se 3 (by rfl) ⟨6192014, by rfl⟩ : syracuseStep 33024077 = 12384029) B12384029
theorem B22016051 : Blo 2007435 22016051 := bstep (se 1 (by rfl) ⟨16512038, by rfl⟩ : syracuseStep 22016051 = 33024077) B33024077
theorem B14677367 : Blo 2007435 14677367 := bstep (se 1 (by rfl) ⟨11008025, by rfl⟩ : syracuseStep 14677367 = 22016051) B22016051
theorem B156558581 : Blo 2007435 156558581 := bstep (se 5 (by rfl) ⟨7338683, by rfl⟩ : syracuseStep 156558581 = 14677367) B14677367
theorem B104372387 : Blo 2007435 104372387 := bstep (se 1 (by rfl) ⟨78279290, by rfl⟩ : syracuseStep 104372387 = 156558581) B156558581
theorem B69581591 : Blo 2007435 69581591 := bstep (se 1 (by rfl) ⟨52186193, by rfl⟩ : syracuseStep 69581591 = 104372387) B104372387
theorem B46387727 : Blo 2007435 46387727 := bstep (se 1 (by rfl) ⟨34790795, by rfl⟩ : syracuseStep 46387727 = 69581591) B69581591
theorem B30925151 : Blo 2007435 30925151 := bstep (se 1 (by rfl) ⟨23193863, by rfl⟩ : syracuseStep 30925151 = 46387727) B46387727
theorem B20616767 : Blo 2007435 20616767 := bstep (se 1 (by rfl) ⟨15462575, by rfl⟩ : syracuseStep 20616767 = 30925151) B30925151
theorem B13744511 : Blo 2007435 13744511 := bstep (se 1 (by rfl) ⟨10308383, by rfl⟩ : syracuseStep 13744511 = 20616767) B20616767
theorem B9163007 : Blo 2007435 9163007 := bstep (se 1 (by rfl) ⟨6872255, by rfl⟩ : syracuseStep 9163007 = 13744511) B13744511
theorem B6108671 : Blo 2007435 6108671 := bstep (se 1 (by rfl) ⟨4581503, by rfl⟩ : syracuseStep 6108671 = 9163007) B9163007
theorem B4072447 : Blo 2007435 4072447 := bstep (se 1 (by rfl) ⟨3054335, by rfl⟩ : syracuseStep 4072447 = 6108671) B6108671
theorem B5429929 : Blo 2007435 5429929 := bstep (se 2 (by rfl) ⟨2036223, by rfl⟩ : syracuseStep 5429929 = 4072447) B4072447
theorem B7239905 : Blo 2007435 7239905 := bstep (se 2 (by rfl) ⟨2714964, by rfl⟩ : syracuseStep 7239905 = 5429929) B5429929
theorem B4826603 : Blo 2007435 4826603 := bstep (se 1 (by rfl) ⟨3619952, by rfl⟩ : syracuseStep 4826603 = 7239905) B7239905
theorem B3217735 : Blo 2007435 3217735 := bstep (se 1 (by rfl) ⟨2413301, by rfl⟩ : syracuseStep 3217735 = 4826603) B4826603
theorem B17161253 : Blo 2007435 17161253 := bstep (se 4 (by rfl) ⟨1608867, by rfl⟩ : syracuseStep 17161253 = 3217735) B3217735
theorem B11440835 : Blo 2007435 11440835 := bstep (se 1 (by rfl) ⟨8580626, by rfl⟩ : syracuseStep 11440835 = 17161253) B17161253
theorem B7627223 : Blo 2007435 7627223 := bstep (se 1 (by rfl) ⟨5720417, by rfl⟩ : syracuseStep 7627223 = 11440835) B11440835
theorem B5084815 : Blo 2007435 5084815 := bstep (se 1 (by rfl) ⟨3813611, by rfl⟩ : syracuseStep 5084815 = 7627223) B7627223
theorem B6779753 : Blo 2007435 6779753 := bstep (se 2 (by rfl) ⟨2542407, by rfl⟩ : syracuseStep 6779753 = 5084815) B5084815
theorem B4519835 : Blo 2007435 4519835 := bstep (se 1 (by rfl) ⟨3389876, by rfl⟩ : syracuseStep 4519835 = 6779753) B6779753
theorem B3013223 : Blo 2007435 3013223 := bstep (se 1 (by rfl) ⟨2259917, by rfl⟩ : syracuseStep 3013223 = 4519835) B4519835
theorem B2008815 : Blo 2007435 2008815 := bstep (se 1 (by rfl) ⟨1506611, by rfl⟩ : syracuseStep 2008815 = 3013223) B3013223
theorem B3013229 : Blo 2007435 3013229 := bbase (se 3 (by rfl) ⟨564980, by rfl⟩ : syracuseStep 3013229 = 1129961) (by norm_num)
theorem B2008819 : Blo 2007435 2008819 := bstep (se 1 (by rfl) ⟨1506614, by rfl⟩ : syracuseStep 2008819 = 3013229) B3013229
theorem B4519853 : Blo 2007435 4519853 := bbase (se 3 (by rfl) ⟨847472, by rfl⟩ : syracuseStep 4519853 = 1694945) (by norm_num)
theorem B3013235 : Blo 2007435 3013235 := bstep (se 1 (by rfl) ⟨2259926, by rfl⟩ : syracuseStep 3013235 = 4519853) B4519853
theorem B2008823 : Blo 2007435 2008823 := bstep (se 1 (by rfl) ⟨1506617, by rfl⟩ : syracuseStep 2008823 = 3013235) B3013235
theorem B5720453 : Blo 2007435 5720453 := bbase (se 4 (by rfl) ⟨536292, by rfl⟩ : syracuseStep 5720453 = 1072585) (by norm_num)
theorem B3813635 : Blo 2007435 3813635 := bstep (se 1 (by rfl) ⟨2860226, by rfl⟩ : syracuseStep 3813635 = 5720453) B5720453
theorem B2542423 : Blo 2007435 2542423 := bstep (se 1 (by rfl) ⟨1906817, by rfl⟩ : syracuseStep 2542423 = 3813635) B3813635
theorem B3389897 : Blo 2007435 3389897 := bstep (se 2 (by rfl) ⟨1271211, by rfl⟩ : syracuseStep 3389897 = 2542423) B2542423
theorem B2259931 : Blo 2007435 2259931 := bstep (se 1 (by rfl) ⟨1694948, by rfl⟩ : syracuseStep 2259931 = 3389897) B3389897
theorem B3013241 : Blo 2007435 3013241 := bstep (se 2 (by rfl) ⟨1129965, by rfl⟩ : syracuseStep 3013241 = 2259931) B2259931
theorem B2008827 : Blo 2007435 2008827 := bstep (se 1 (by rfl) ⟨1506620, by rfl⟩ : syracuseStep 2008827 = 3013241) B3013241
theorem B6872309 : Blo 2007435 6872309 := bbase (se 5 (by rfl) ⟨322139, by rfl⟩ : syracuseStep 6872309 = 644279) (by norm_num)
theorem B4581539 : Blo 2007435 4581539 := bstep (se 1 (by rfl) ⟨3436154, by rfl⟩ : syracuseStep 4581539 = 6872309) B6872309
theorem B3054359 : Blo 2007435 3054359 := bstep (se 1 (by rfl) ⟨2290769, by rfl⟩ : syracuseStep 3054359 = 4581539) B4581539
theorem B8144957 : Blo 2007435 8144957 := bstep (se 3 (by rfl) ⟨1527179, by rfl⟩ : syracuseStep 8144957 = 3054359) B3054359
theorem B5429971 : Blo 2007435 5429971 := bstep (se 1 (by rfl) ⟨4072478, by rfl⟩ : syracuseStep 5429971 = 8144957) B8144957
theorem B7239961 : Blo 2007435 7239961 := bstep (se 2 (by rfl) ⟨2714985, by rfl⟩ : syracuseStep 7239961 = 5429971) B5429971
theorem B38613125 : Blo 2007435 38613125 := bstep (se 4 (by rfl) ⟨3619980, by rfl⟩ : syracuseStep 38613125 = 7239961) B7239961
theorem B25742083 : Blo 2007435 25742083 := bstep (se 1 (by rfl) ⟨19306562, by rfl⟩ : syracuseStep 25742083 = 38613125) B38613125
theorem B34322777 : Blo 2007435 34322777 := bstep (se 2 (by rfl) ⟨12871041, by rfl⟩ : syracuseStep 34322777 = 25742083) B25742083
theorem B22881851 : Blo 2007435 22881851 := bstep (se 1 (by rfl) ⟨17161388, by rfl⟩ : syracuseStep 22881851 = 34322777) B34322777
theorem B15254567 : Blo 2007435 15254567 := bstep (se 1 (by rfl) ⟨11440925, by rfl⟩ : syracuseStep 15254567 = 22881851) B22881851
theorem B10169711 : Blo 2007435 10169711 := bstep (se 1 (by rfl) ⟨7627283, by rfl⟩ : syracuseStep 10169711 = 15254567) B15254567
theorem B6779807 : Blo 2007435 6779807 := bstep (se 1 (by rfl) ⟨5084855, by rfl⟩ : syracuseStep 6779807 = 10169711) B10169711
theorem B4519871 : Blo 2007435 4519871 := bstep (se 1 (by rfl) ⟨3389903, by rfl⟩ : syracuseStep 4519871 = 6779807) B6779807
theorem B3013247 : Blo 2007435 3013247 := bstep (se 1 (by rfl) ⟨2259935, by rfl⟩ : syracuseStep 3013247 = 4519871) B4519871
theorem B2008831 : Blo 2007435 2008831 := bstep (se 1 (by rfl) ⟨1506623, by rfl⟩ : syracuseStep 2008831 = 3013247) B3013247
theorem B3013253 : Blo 2007435 3013253 := bbase (se 4 (by rfl) ⟨282492, by rfl⟩ : syracuseStep 3013253 = 564985) (by norm_num)
theorem B2008835 : Blo 2007435 2008835 := bstep (se 1 (by rfl) ⟨1506626, by rfl⟩ : syracuseStep 2008835 = 3013253) B3013253
theorem B3389917 : Blo 2007435 3389917 := bbase (se 3 (by rfl) ⟨635609, by rfl⟩ : syracuseStep 3389917 = 1271219) (by norm_num)
theorem B4519889 : Blo 2007435 4519889 := bstep (se 2 (by rfl) ⟨1694958, by rfl⟩ : syracuseStep 4519889 = 3389917) B3389917
theorem B3013259 : Blo 2007435 3013259 := bstep (se 1 (by rfl) ⟨2259944, by rfl⟩ : syracuseStep 3013259 = 4519889) B4519889
theorem B2008839 : Blo 2007435 2008839 := bstep (se 1 (by rfl) ⟨1506629, by rfl⟩ : syracuseStep 2008839 = 3013259) B3013259
theorem B2259949 : Blo 2007435 2259949 := bbase (se 3 (by rfl) ⟨423740, by rfl⟩ : syracuseStep 2259949 = 847481) (by norm_num)
theorem B3013265 : Blo 2007435 3013265 := bstep (se 2 (by rfl) ⟨1129974, by rfl⟩ : syracuseStep 3013265 = 2259949) B2259949
theorem B2008843 : Blo 2007435 2008843 := bstep (se 1 (by rfl) ⟨1506632, by rfl⟩ : syracuseStep 2008843 = 3013265) B3013265
theorem B6779861 : Blo 2007435 6779861 := bbase (se 7 (by rfl) ⟨79451, by rfl⟩ : syracuseStep 6779861 = 158903) (by norm_num)
theorem B4519907 : Blo 2007435 4519907 := bstep (se 1 (by rfl) ⟨3389930, by rfl⟩ : syracuseStep 4519907 = 6779861) B6779861
theorem B3013271 : Blo 2007435 3013271 := bstep (se 1 (by rfl) ⟨2259953, by rfl⟩ : syracuseStep 3013271 = 4519907) B4519907
theorem B2008847 : Blo 2007435 2008847 := bstep (se 1 (by rfl) ⟨1506635, by rfl⟩ : syracuseStep 2008847 = 3013271) B3013271
theorem B3013277 : Blo 2007435 3013277 := bbase (se 3 (by rfl) ⟨564989, by rfl⟩ : syracuseStep 3013277 = 1129979) (by norm_num)
theorem B2008851 : Blo 2007435 2008851 := bstep (se 1 (by rfl) ⟨1506638, by rfl⟩ : syracuseStep 2008851 = 3013277) B3013277
theorem B4519925 : Blo 2007435 4519925 := bbase (se 5 (by rfl) ⟨211871, by rfl⟩ : syracuseStep 4519925 = 423743) (by norm_num)
theorem B3013283 : Blo 2007435 3013283 := bstep (se 1 (by rfl) ⟨2259962, by rfl⟩ : syracuseStep 3013283 = 4519925) B4519925
theorem B2008855 : Blo 2007435 2008855 := bstep (se 1 (by rfl) ⟨1506641, by rfl⟩ : syracuseStep 2008855 = 3013283) B3013283
theorem B3719485 : Blo 2007435 3719485 := bbase (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) (by norm_num)
theorem B4959313 : Blo 2007435 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B26449669 : Blo 2007435 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B35266225 : Blo 2007435 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B47021633 : Blo 2007435 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B31347755 : Blo 2007435 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B20898503 : Blo 2007435 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B13932335 : Blo 2007435 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B37152893 : Blo 2007435 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B24768595 : Blo 2007435 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B33024793 : Blo 2007435 33024793 := bstep (se 2 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 33024793 = 24768595) B24768595
theorem B44033057 : Blo 2007435 44033057 := bstep (se 2 (by rfl) ⟨16512396, by rfl⟩ : syracuseStep 44033057 = 33024793) B33024793
theorem B29355371 : Blo 2007435 29355371 := bstep (se 1 (by rfl) ⟨22016528, by rfl⟩ : syracuseStep 29355371 = 44033057) B44033057
theorem B19570247 : Blo 2007435 19570247 := bstep (se 1 (by rfl) ⟨14677685, by rfl⟩ : syracuseStep 19570247 = 29355371) B29355371
theorem B13046831 : Blo 2007435 13046831 := bstep (se 1 (by rfl) ⟨9785123, by rfl⟩ : syracuseStep 13046831 = 19570247) B19570247
theorem B8697887 : Blo 2007435 8697887 := bstep (se 1 (by rfl) ⟨6523415, by rfl⟩ : syracuseStep 8697887 = 13046831) B13046831
theorem B5798591 : Blo 2007435 5798591 := bstep (se 1 (by rfl) ⟨4348943, by rfl⟩ : syracuseStep 5798591 = 8697887) B8697887
theorem B61851637 : Blo 2007435 61851637 := bstep (se 5 (by rfl) ⟨2899295, by rfl⟩ : syracuseStep 61851637 = 5798591) B5798591
theorem B82468849 : Blo 2007435 82468849 := bstep (se 2 (by rfl) ⟨30925818, by rfl⟩ : syracuseStep 82468849 = 61851637) B61851637
theorem B109958465 : Blo 2007435 109958465 := bstep (se 2 (by rfl) ⟨41234424, by rfl⟩ : syracuseStep 109958465 = 82468849) B82468849
theorem B73305643 : Blo 2007435 73305643 := bstep (se 1 (by rfl) ⟨54979232, by rfl⟩ : syracuseStep 73305643 = 109958465) B109958465
theorem B97740857 : Blo 2007435 97740857 := bstep (se 2 (by rfl) ⟨36652821, by rfl⟩ : syracuseStep 97740857 = 73305643) B73305643
theorem B65160571 : Blo 2007435 65160571 := bstep (se 1 (by rfl) ⟨48870428, by rfl⟩ : syracuseStep 65160571 = 97740857) B97740857
theorem B86880761 : Blo 2007435 86880761 := bstep (se 2 (by rfl) ⟨32580285, by rfl⟩ : syracuseStep 86880761 = 65160571) B65160571
theorem B57920507 : Blo 2007435 57920507 := bstep (se 1 (by rfl) ⟨43440380, by rfl⟩ : syracuseStep 57920507 = 86880761) B86880761
theorem B38613671 : Blo 2007435 38613671 := bstep (se 1 (by rfl) ⟨28960253, by rfl⟩ : syracuseStep 38613671 = 57920507) B57920507
theorem B25742447 : Blo 2007435 25742447 := bstep (se 1 (by rfl) ⟨19306835, by rfl⟩ : syracuseStep 25742447 = 38613671) B38613671
theorem B17161631 : Blo 2007435 17161631 := bstep (se 1 (by rfl) ⟨12871223, by rfl⟩ : syracuseStep 17161631 = 25742447) B25742447
theorem B11441087 : Blo 2007435 11441087 := bstep (se 1 (by rfl) ⟨8580815, by rfl⟩ : syracuseStep 11441087 = 17161631) B17161631
theorem B7627391 : Blo 2007435 7627391 := bstep (se 1 (by rfl) ⟨5720543, by rfl⟩ : syracuseStep 7627391 = 11441087) B11441087
theorem B5084927 : Blo 2007435 5084927 := bstep (se 1 (by rfl) ⟨3813695, by rfl⟩ : syracuseStep 5084927 = 7627391) B7627391
theorem B3389951 : Blo 2007435 3389951 := bstep (se 1 (by rfl) ⟨2542463, by rfl⟩ : syracuseStep 3389951 = 5084927) B5084927
theorem B2259967 : Blo 2007435 2259967 := bstep (se 1 (by rfl) ⟨1694975, by rfl⟩ : syracuseStep 2259967 = 3389951) B3389951
theorem B3013289 : Blo 2007435 3013289 := bstep (se 2 (by rfl) ⟨1129983, by rfl⟩ : syracuseStep 3013289 = 2259967) B2259967
theorem B2008859 : Blo 2007435 2008859 := bstep (se 1 (by rfl) ⟨1506644, by rfl⟩ : syracuseStep 2008859 = 3013289) B3013289
theorem B2860277 : Blo 2007435 2860277 := bbase (se 5 (by rfl) ⟨134075, by rfl⟩ : syracuseStep 2860277 = 268151) (by norm_num)
theorem B7627405 : Blo 2007435 7627405 := bstep (se 3 (by rfl) ⟨1430138, by rfl⟩ : syracuseStep 7627405 = 2860277) B2860277
theorem B10169873 : Blo 2007435 10169873 := bstep (se 2 (by rfl) ⟨3813702, by rfl⟩ : syracuseStep 10169873 = 7627405) B7627405
theorem B6779915 : Blo 2007435 6779915 := bstep (se 1 (by rfl) ⟨5084936, by rfl⟩ : syracuseStep 6779915 = 10169873) B10169873
theorem B4519943 : Blo 2007435 4519943 := bstep (se 1 (by rfl) ⟨3389957, by rfl⟩ : syracuseStep 4519943 = 6779915) B6779915
theorem B3013295 : Blo 2007435 3013295 := bstep (se 1 (by rfl) ⟨2259971, by rfl⟩ : syracuseStep 3013295 = 4519943) B4519943
theorem B2008863 : Blo 2007435 2008863 := bstep (se 1 (by rfl) ⟨1506647, by rfl⟩ : syracuseStep 2008863 = 3013295) B3013295
theorem B3013301 : Blo 2007435 3013301 := bbase (se 5 (by rfl) ⟨141248, by rfl⟩ : syracuseStep 3013301 = 282497) (by norm_num)
theorem B2008867 : Blo 2007435 2008867 := bstep (se 1 (by rfl) ⟨1506650, by rfl⟩ : syracuseStep 2008867 = 3013301) B3013301
theorem B5084957 : Blo 2007435 5084957 := bbase (se 3 (by rfl) ⟨953429, by rfl⟩ : syracuseStep 5084957 = 1906859) (by norm_num)
theorem B3389971 : Blo 2007435 3389971 := bstep (se 1 (by rfl) ⟨2542478, by rfl⟩ : syracuseStep 3389971 = 5084957) B5084957
theorem B4519961 : Blo 2007435 4519961 := bstep (se 2 (by rfl) ⟨1694985, by rfl⟩ : syracuseStep 4519961 = 3389971) B3389971
theorem B3013307 : Blo 2007435 3013307 := bstep (se 1 (by rfl) ⟨2259980, by rfl⟩ : syracuseStep 3013307 = 4519961) B4519961
theorem B2008871 : Blo 2007435 2008871 := bstep (se 1 (by rfl) ⟨1506653, by rfl⟩ : syracuseStep 2008871 = 3013307) B3013307
theorem B2259985 : Blo 2007435 2259985 := bbase (se 2 (by rfl) ⟨847494, by rfl⟩ : syracuseStep 2259985 = 1694989) (by norm_num)
theorem B3013313 : Blo 2007435 3013313 := bstep (se 2 (by rfl) ⟨1129992, by rfl⟩ : syracuseStep 3013313 = 2259985) B2259985
theorem B2008875 : Blo 2007435 2008875 := bstep (se 1 (by rfl) ⟨1506656, by rfl⟩ : syracuseStep 2008875 = 3013313) B3013313
theorem B3813733 : Blo 2007435 3813733 := bbase (se 4 (by rfl) ⟨357537, by rfl⟩ : syracuseStep 3813733 = 715075) (by norm_num)
theorem B5084977 : Blo 2007435 5084977 := bstep (se 2 (by rfl) ⟨1906866, by rfl⟩ : syracuseStep 5084977 = 3813733) B3813733
theorem B6779969 : Blo 2007435 6779969 := bstep (se 2 (by rfl) ⟨2542488, by rfl⟩ : syracuseStep 6779969 = 5084977) B5084977
theorem B4519979 : Blo 2007435 4519979 := bstep (se 1 (by rfl) ⟨3389984, by rfl⟩ : syracuseStep 4519979 = 6779969) B6779969
theorem B3013319 : Blo 2007435 3013319 := bstep (se 1 (by rfl) ⟨2259989, by rfl⟩ : syracuseStep 3013319 = 4519979) B4519979
theorem B2008879 : Blo 2007435 2008879 := bstep (se 1 (by rfl) ⟨1506659, by rfl⟩ : syracuseStep 2008879 = 3013319) B3013319
theorem B3013325 : Blo 2007435 3013325 := bbase (se 3 (by rfl) ⟨564998, by rfl⟩ : syracuseStep 3013325 = 1129997) (by norm_num)
theorem B2008883 : Blo 2007435 2008883 := bstep (se 1 (by rfl) ⟨1506662, by rfl⟩ : syracuseStep 2008883 = 3013325) B3013325
theorem B4519997 : Blo 2007435 4519997 := bbase (se 3 (by rfl) ⟨847499, by rfl⟩ : syracuseStep 4519997 = 1694999) (by norm_num)
theorem B3013331 : Blo 2007435 3013331 := bstep (se 1 (by rfl) ⟨2259998, by rfl⟩ : syracuseStep 3013331 = 4519997) B4519997
theorem B2008887 : Blo 2007435 2008887 := bstep (se 1 (by rfl) ⟨1506665, by rfl⟩ : syracuseStep 2008887 = 3013331) B3013331
theorem B3390005 : Blo 2007435 3390005 := bbase (se 5 (by rfl) ⟨158906, by rfl⟩ : syracuseStep 3390005 = 317813) (by norm_num)
theorem B2260003 : Blo 2007435 2260003 := bstep (se 1 (by rfl) ⟨1695002, by rfl⟩ : syracuseStep 2260003 = 3390005) B3390005
theorem B3013337 : Blo 2007435 3013337 := bstep (se 2 (by rfl) ⟨1130001, by rfl⟩ : syracuseStep 3013337 = 2260003) B2260003
theorem B2008891 : Blo 2007435 2008891 := bstep (se 1 (by rfl) ⟨1506668, by rfl⟩ : syracuseStep 2008891 = 3013337) B3013337
theorem B5720645 : Blo 2007435 5720645 := bbase (se 4 (by rfl) ⟨536310, by rfl⟩ : syracuseStep 5720645 = 1072621) (by norm_num)
theorem B15255053 : Blo 2007435 15255053 := bstep (se 3 (by rfl) ⟨2860322, by rfl⟩ : syracuseStep 15255053 = 5720645) B5720645
theorem B10170035 : Blo 2007435 10170035 := bstep (se 1 (by rfl) ⟨7627526, by rfl⟩ : syracuseStep 10170035 = 15255053) B15255053
theorem B6780023 : Blo 2007435 6780023 := bstep (se 1 (by rfl) ⟨5085017, by rfl⟩ : syracuseStep 6780023 = 10170035) B10170035
theorem B4520015 : Blo 2007435 4520015 := bstep (se 1 (by rfl) ⟨3390011, by rfl⟩ : syracuseStep 4520015 = 6780023) B6780023
theorem B3013343 : Blo 2007435 3013343 := bstep (se 1 (by rfl) ⟨2260007, by rfl⟩ : syracuseStep 3013343 = 4520015) B4520015
theorem B2008895 : Blo 2007435 2008895 := bstep (se 1 (by rfl) ⟨1506671, by rfl⟩ : syracuseStep 2008895 = 3013343) B3013343
theorem B3013349 : Blo 2007435 3013349 := bbase (se 4 (by rfl) ⟨282501, by rfl⟩ : syracuseStep 3013349 = 565003) (by norm_num)
theorem B2008899 : Blo 2007435 2008899 := bstep (se 1 (by rfl) ⟨1506674, by rfl⟩ : syracuseStep 2008899 = 3013349) B3013349
theorem B3217877 : Blo 2007435 3217877 := bbase (se 7 (by rfl) ⟨37709, by rfl⟩ : syracuseStep 3217877 = 75419) (by norm_num)
theorem B2145251 : Blo 2007435 2145251 := bstep (se 1 (by rfl) ⟨1608938, by rfl⟩ : syracuseStep 2145251 = 3217877) B3217877
theorem B5720669 : Blo 2007435 5720669 := bstep (se 3 (by rfl) ⟨1072625, by rfl⟩ : syracuseStep 5720669 = 2145251) B2145251
theorem B3813779 : Blo 2007435 3813779 := bstep (se 1 (by rfl) ⟨2860334, by rfl⟩ : syracuseStep 3813779 = 5720669) B5720669
theorem B2542519 : Blo 2007435 2542519 := bstep (se 1 (by rfl) ⟨1906889, by rfl⟩ : syracuseStep 2542519 = 3813779) B3813779
theorem B3390025 : Blo 2007435 3390025 := bstep (se 2 (by rfl) ⟨1271259, by rfl⟩ : syracuseStep 3390025 = 2542519) B2542519
theorem B4520033 : Blo 2007435 4520033 := bstep (se 2 (by rfl) ⟨1695012, by rfl⟩ : syracuseStep 4520033 = 3390025) B3390025
theorem B3013355 : Blo 2007435 3013355 := bstep (se 1 (by rfl) ⟨2260016, by rfl⟩ : syracuseStep 3013355 = 4520033) B4520033
theorem B2008903 : Blo 2007435 2008903 := bstep (se 1 (by rfl) ⟨1506677, by rfl⟩ : syracuseStep 2008903 = 3013355) B3013355
theorem B2260021 : Blo 2007435 2260021 := bbase (se 5 (by rfl) ⟨105938, by rfl⟩ : syracuseStep 2260021 = 211877) (by norm_num)
theorem B3013361 : Blo 2007435 3013361 := bstep (se 2 (by rfl) ⟨1130010, by rfl⟩ : syracuseStep 3013361 = 2260021) B2260021
theorem B2008907 : Blo 2007435 2008907 := bstep (se 1 (by rfl) ⟨1506680, by rfl⟩ : syracuseStep 2008907 = 3013361) B3013361
theorem B2542529 : Blo 2007435 2542529 := bbase (se 2 (by rfl) ⟨953448, by rfl⟩ : syracuseStep 2542529 = 1906897) (by norm_num)
theorem B6780077 : Blo 2007435 6780077 := bstep (se 3 (by rfl) ⟨1271264, by rfl⟩ : syracuseStep 6780077 = 2542529) B2542529
theorem B4520051 : Blo 2007435 4520051 := bstep (se 1 (by rfl) ⟨3390038, by rfl⟩ : syracuseStep 4520051 = 6780077) B6780077
theorem B3013367 : Blo 2007435 3013367 := bstep (se 1 (by rfl) ⟨2260025, by rfl⟩ : syracuseStep 3013367 = 4520051) B4520051
theorem B2008911 : Blo 2007435 2008911 := bstep (se 1 (by rfl) ⟨1506683, by rfl⟩ : syracuseStep 2008911 = 3013367) B3013367
theorem B3013373 : Blo 2007435 3013373 := bbase (se 3 (by rfl) ⟨565007, by rfl⟩ : syracuseStep 3013373 = 1130015) (by norm_num)
theorem B2008915 : Blo 2007435 2008915 := bstep (se 1 (by rfl) ⟨1506686, by rfl⟩ : syracuseStep 2008915 = 3013373) B3013373
theorem B4520069 : Blo 2007435 4520069 := bbase (se 4 (by rfl) ⟨423756, by rfl⟩ : syracuseStep 4520069 = 847513) (by norm_num)
theorem B3013379 : Blo 2007435 3013379 := bstep (se 1 (by rfl) ⟨2260034, by rfl⟩ : syracuseStep 3013379 = 4520069) B4520069
theorem B2008919 : Blo 2007435 2008919 := bstep (se 1 (by rfl) ⟨1506689, by rfl⟩ : syracuseStep 2008919 = 3013379) B3013379
theorem B3217909 : Blo 2007435 3217909 := bbase (se 5 (by rfl) ⟨150839, by rfl⟩ : syracuseStep 3217909 = 301679) (by norm_num)
theorem B4290545 : Blo 2007435 4290545 := bstep (se 2 (by rfl) ⟨1608954, by rfl⟩ : syracuseStep 4290545 = 3217909) B3217909
theorem B2860363 : Blo 2007435 2860363 := bstep (se 1 (by rfl) ⟨2145272, by rfl⟩ : syracuseStep 2860363 = 4290545) B4290545
theorem B3813817 : Blo 2007435 3813817 := bstep (se 2 (by rfl) ⟨1430181, by rfl⟩ : syracuseStep 3813817 = 2860363) B2860363
theorem B5085089 : Blo 2007435 5085089 := bstep (se 2 (by rfl) ⟨1906908, by rfl⟩ : syracuseStep 5085089 = 3813817) B3813817
theorem B3390059 : Blo 2007435 3390059 := bstep (se 1 (by rfl) ⟨2542544, by rfl⟩ : syracuseStep 3390059 = 5085089) B5085089
theorem B2260039 : Blo 2007435 2260039 := bstep (se 1 (by rfl) ⟨1695029, by rfl⟩ : syracuseStep 2260039 = 3390059) B3390059
theorem B3013385 : Blo 2007435 3013385 := bstep (se 2 (by rfl) ⟨1130019, by rfl⟩ : syracuseStep 3013385 = 2260039) B2260039
theorem B2008923 : Blo 2007435 2008923 := bstep (se 1 (by rfl) ⟨1506692, by rfl⟩ : syracuseStep 2008923 = 3013385) B3013385
theorem B10170197 : Blo 2007435 10170197 := bbase (se 9 (by rfl) ⟨29795, by rfl⟩ : syracuseStep 10170197 = 59591) (by norm_num)
theorem B6780131 : Blo 2007435 6780131 := bstep (se 1 (by rfl) ⟨5085098, by rfl⟩ : syracuseStep 6780131 = 10170197) B10170197
theorem B4520087 : Blo 2007435 4520087 := bstep (se 1 (by rfl) ⟨3390065, by rfl⟩ : syracuseStep 4520087 = 6780131) B6780131
theorem B3013391 : Blo 2007435 3013391 := bstep (se 1 (by rfl) ⟨2260043, by rfl⟩ : syracuseStep 3013391 = 4520087) B4520087
theorem B2008927 : Blo 2007435 2008927 := bstep (se 1 (by rfl) ⟨1506695, by rfl⟩ : syracuseStep 2008927 = 3013391) B3013391
theorem B3013397 : Blo 2007435 3013397 := bbase (se 6 (by rfl) ⟨70626, by rfl⟩ : syracuseStep 3013397 = 141253) (by norm_num)
theorem B2008931 : Blo 2007435 2008931 := bstep (se 1 (by rfl) ⟨1506698, by rfl⟩ : syracuseStep 2008931 = 3013397) B3013397
theorem B12218069 : Blo 2007435 12218069 := bbase (se 7 (by rfl) ⟨143180, by rfl⟩ : syracuseStep 12218069 = 286361) (by norm_num)
theorem B8145379 : Blo 2007435 8145379 := bstep (se 1 (by rfl) ⟨6109034, by rfl⟩ : syracuseStep 8145379 = 12218069) B12218069
theorem B43442021 : Blo 2007435 43442021 := bstep (se 4 (by rfl) ⟨4072689, by rfl⟩ : syracuseStep 43442021 = 8145379) B8145379
theorem B28961347 : Blo 2007435 28961347 := bstep (se 1 (by rfl) ⟨21721010, by rfl⟩ : syracuseStep 28961347 = 43442021) B43442021
theorem B38615129 : Blo 2007435 38615129 := bstep (se 2 (by rfl) ⟨14480673, by rfl⟩ : syracuseStep 38615129 = 28961347) B28961347
theorem B25743419 : Blo 2007435 25743419 := bstep (se 1 (by rfl) ⟨19307564, by rfl⟩ : syracuseStep 25743419 = 38615129) B38615129
theorem B17162279 : Blo 2007435 17162279 := bstep (se 1 (by rfl) ⟨12871709, by rfl⟩ : syracuseStep 17162279 = 25743419) B25743419
theorem B11441519 : Blo 2007435 11441519 := bstep (se 1 (by rfl) ⟨8581139, by rfl⟩ : syracuseStep 11441519 = 17162279) B17162279
theorem B7627679 : Blo 2007435 7627679 := bstep (se 1 (by rfl) ⟨5720759, by rfl⟩ : syracuseStep 7627679 = 11441519) B11441519
theorem B5085119 : Blo 2007435 5085119 := bstep (se 1 (by rfl) ⟨3813839, by rfl⟩ : syracuseStep 5085119 = 7627679) B7627679
theorem B3390079 : Blo 2007435 3390079 := bstep (se 1 (by rfl) ⟨2542559, by rfl⟩ : syracuseStep 3390079 = 5085119) B5085119
theorem B4520105 : Blo 2007435 4520105 := bstep (se 2 (by rfl) ⟨1695039, by rfl⟩ : syracuseStep 4520105 = 3390079) B3390079
theorem B3013403 : Blo 2007435 3013403 := bstep (se 1 (by rfl) ⟨2260052, by rfl⟩ : syracuseStep 3013403 = 4520105) B4520105
theorem B2008935 : Blo 2007435 2008935 := bstep (se 1 (by rfl) ⟨1506701, by rfl⟩ : syracuseStep 2008935 = 3013403) B3013403
theorem B2260057 : Blo 2007435 2260057 := bbase (se 2 (by rfl) ⟨847521, by rfl⟩ : syracuseStep 2260057 = 1695043) (by norm_num)
theorem B3013409 : Blo 2007435 3013409 := bstep (se 2 (by rfl) ⟨1130028, by rfl⟩ : syracuseStep 3013409 = 2260057) B2260057
theorem B2008939 : Blo 2007435 2008939 := bstep (se 1 (by rfl) ⟨1506704, by rfl⟩ : syracuseStep 2008939 = 3013409) B3013409
theorem B6872693 : Blo 2007435 6872693 := bbase (se 5 (by rfl) ⟨322157, by rfl⟩ : syracuseStep 6872693 = 644315) (by norm_num)
theorem B18327181 : Blo 2007435 18327181 := bstep (se 3 (by rfl) ⟨3436346, by rfl⟩ : syracuseStep 18327181 = 6872693) B6872693
theorem B24436241 : Blo 2007435 24436241 := bstep (se 2 (by rfl) ⟨9163590, by rfl⟩ : syracuseStep 24436241 = 18327181) B18327181
theorem B16290827 : Blo 2007435 16290827 := bstep (se 1 (by rfl) ⟨12218120, by rfl⟩ : syracuseStep 16290827 = 24436241) B24436241
theorem B10860551 : Blo 2007435 10860551 := bstep (se 1 (by rfl) ⟨8145413, by rfl⟩ : syracuseStep 10860551 = 16290827) B16290827
theorem B7240367 : Blo 2007435 7240367 := bstep (se 1 (by rfl) ⟨5430275, by rfl⟩ : syracuseStep 7240367 = 10860551) B10860551
theorem B4826911 : Blo 2007435 4826911 := bstep (se 1 (by rfl) ⟨3620183, by rfl⟩ : syracuseStep 4826911 = 7240367) B7240367
theorem B6435881 : Blo 2007435 6435881 := bstep (se 2 (by rfl) ⟨2413455, by rfl⟩ : syracuseStep 6435881 = 4826911) B4826911
theorem B4290587 : Blo 2007435 4290587 := bstep (se 1 (by rfl) ⟨3217940, by rfl⟩ : syracuseStep 4290587 = 6435881) B6435881
theorem B2860391 : Blo 2007435 2860391 := bstep (se 1 (by rfl) ⟨2145293, by rfl⟩ : syracuseStep 2860391 = 4290587) B4290587
theorem B7627709 : Blo 2007435 7627709 := bstep (se 3 (by rfl) ⟨1430195, by rfl⟩ : syracuseStep 7627709 = 2860391) B2860391
theorem B5085139 : Blo 2007435 5085139 := bstep (se 1 (by rfl) ⟨3813854, by rfl⟩ : syracuseStep 5085139 = 7627709) B7627709
theorem B6780185 : Blo 2007435 6780185 := bstep (se 2 (by rfl) ⟨2542569, by rfl⟩ : syracuseStep 6780185 = 5085139) B5085139
theorem B4520123 : Blo 2007435 4520123 := bstep (se 1 (by rfl) ⟨3390092, by rfl⟩ : syracuseStep 4520123 = 6780185) B6780185
theorem B3013415 : Blo 2007435 3013415 := bstep (se 1 (by rfl) ⟨2260061, by rfl⟩ : syracuseStep 3013415 = 4520123) B4520123
theorem B2008943 : Blo 2007435 2008943 := bstep (se 1 (by rfl) ⟨1506707, by rfl⟩ : syracuseStep 2008943 = 3013415) B3013415
theorem B3013421 : Blo 2007435 3013421 := bbase (se 3 (by rfl) ⟨565016, by rfl⟩ : syracuseStep 3013421 = 1130033) (by norm_num)
theorem B2008947 : Blo 2007435 2008947 := bstep (se 1 (by rfl) ⟨1506710, by rfl⟩ : syracuseStep 2008947 = 3013421) B3013421
theorem B4520141 : Blo 2007435 4520141 := bbase (se 3 (by rfl) ⟨847526, by rfl⟩ : syracuseStep 4520141 = 1695053) (by norm_num)
theorem B3013427 : Blo 2007435 3013427 := bstep (se 1 (by rfl) ⟨2260070, by rfl⟩ : syracuseStep 3013427 = 4520141) B4520141
theorem B2008951 : Blo 2007435 2008951 := bstep (se 1 (by rfl) ⟨1506713, by rfl⟩ : syracuseStep 2008951 = 3013427) B3013427
theorem B2542585 : Blo 2007435 2542585 := bbase (se 2 (by rfl) ⟨953469, by rfl⟩ : syracuseStep 2542585 = 1906939) (by norm_num)
theorem B3390113 : Blo 2007435 3390113 := bstep (se 2 (by rfl) ⟨1271292, by rfl⟩ : syracuseStep 3390113 = 2542585) B2542585
theorem B2260075 : Blo 2007435 2260075 := bstep (se 1 (by rfl) ⟨1695056, by rfl⟩ : syracuseStep 2260075 = 3390113) B3390113
theorem B3013433 : Blo 2007435 3013433 := bstep (se 2 (by rfl) ⟨1130037, by rfl⟩ : syracuseStep 3013433 = 2260075) B2260075
theorem B2008955 : Blo 2007435 2008955 := bstep (se 1 (by rfl) ⟨1506716, by rfl⟩ : syracuseStep 2008955 = 3013433) B3013433
theorem B9059221 : Blo 2007435 9059221 := bbase (se 6 (by rfl) ⟨212325, by rfl⟩ : syracuseStep 9059221 = 424651) (by norm_num)
theorem B48315845 : Blo 2007435 48315845 := bstep (se 4 (by rfl) ⟨4529610, by rfl⟩ : syracuseStep 48315845 = 9059221) B9059221
theorem B128842253 : Blo 2007435 128842253 := bstep (se 3 (by rfl) ⟨24157922, by rfl⟩ : syracuseStep 128842253 = 48315845) B48315845
theorem B85894835 : Blo 2007435 85894835 := bstep (se 1 (by rfl) ⟨64421126, by rfl⟩ : syracuseStep 85894835 = 128842253) B128842253
theorem B229052893 : Blo 2007435 229052893 := bstep (se 3 (by rfl) ⟨42947417, by rfl⟩ : syracuseStep 229052893 = 85894835) B85894835
theorem B305403857 : Blo 2007435 305403857 := bstep (se 2 (by rfl) ⟨114526446, by rfl⟩ : syracuseStep 305403857 = 229052893) B229052893
theorem B203602571 : Blo 2007435 203602571 := bstep (se 1 (by rfl) ⟨152701928, by rfl⟩ : syracuseStep 203602571 = 305403857) B305403857
theorem B135735047 : Blo 2007435 135735047 := bstep (se 1 (by rfl) ⟨101801285, by rfl⟩ : syracuseStep 135735047 = 203602571) B203602571
theorem B90490031 : Blo 2007435 90490031 := bstep (se 1 (by rfl) ⟨67867523, by rfl⟩ : syracuseStep 90490031 = 135735047) B135735047
theorem B60326687 : Blo 2007435 60326687 := bstep (se 1 (by rfl) ⟨45245015, by rfl⟩ : syracuseStep 60326687 = 90490031) B90490031
theorem B40217791 : Blo 2007435 40217791 := bstep (se 1 (by rfl) ⟨30163343, by rfl⟩ : syracuseStep 40217791 = 60326687) B60326687
theorem B53623721 : Blo 2007435 53623721 := bstep (se 2 (by rfl) ⟨20108895, by rfl⟩ : syracuseStep 53623721 = 40217791) B40217791
theorem B35749147 : Blo 2007435 35749147 := bstep (se 1 (by rfl) ⟨26811860, by rfl⟩ : syracuseStep 35749147 = 53623721) B53623721
theorem B47665529 : Blo 2007435 47665529 := bstep (se 2 (by rfl) ⟨17874573, by rfl⟩ : syracuseStep 47665529 = 35749147) B35749147
theorem B31777019 : Blo 2007435 31777019 := bstep (se 1 (by rfl) ⟨23832764, by rfl⟩ : syracuseStep 31777019 = 47665529) B47665529
theorem B21184679 : Blo 2007435 21184679 := bstep (se 1 (by rfl) ⟨15888509, by rfl⟩ : syracuseStep 21184679 = 31777019) B31777019
theorem B14123119 : Blo 2007435 14123119 := bstep (se 1 (by rfl) ⟨10592339, by rfl⟩ : syracuseStep 14123119 = 21184679) B21184679
theorem B18830825 : Blo 2007435 18830825 := bstep (se 2 (by rfl) ⟨7061559, by rfl⟩ : syracuseStep 18830825 = 14123119) B14123119
theorem B803448533 : Blo 2007435 803448533 := bstep (se 7 (by rfl) ⟨9415412, by rfl⟩ : syracuseStep 803448533 = 18830825) B18830825
theorem B535632355 : Blo 2007435 535632355 := bstep (se 1 (by rfl) ⟨401724266, by rfl⟩ : syracuseStep 535632355 = 803448533) B803448533
theorem B2856705893 : Blo 2007435 2856705893 := bstep (se 4 (by rfl) ⟨267816177, by rfl⟩ : syracuseStep 2856705893 = 535632355) B535632355
theorem B1904470595 : Blo 2007435 1904470595 := bstep (se 1 (by rfl) ⟨1428352946, by rfl⟩ : syracuseStep 1904470595 = 2856705893) B2856705893
theorem B1269647063 : Blo 2007435 1269647063 := bstep (se 1 (by rfl) ⟨952235297, by rfl⟩ : syracuseStep 1269647063 = 1904470595) B1904470595
theorem B846431375 : Blo 2007435 846431375 := bstep (se 1 (by rfl) ⟨634823531, by rfl⟩ : syracuseStep 846431375 = 1269647063) B1269647063
theorem B2257150333 : Blo 2007435 2257150333 := bstep (se 3 (by rfl) ⟨423215687, by rfl⟩ : syracuseStep 2257150333 = 846431375) B846431375
theorem B3009533777 : Blo 2007435 3009533777 := bstep (se 2 (by rfl) ⟨1128575166, by rfl⟩ : syracuseStep 3009533777 = 2257150333) B2257150333
theorem B2006355851 : Blo 2007435 2006355851 := bstep (se 1 (by rfl) ⟨1504766888, by rfl⟩ : syracuseStep 2006355851 = 3009533777) B3009533777
theorem B1337570567 : Blo 2007435 1337570567 := bstep (se 1 (by rfl) ⟨1003177925, by rfl⟩ : syracuseStep 1337570567 = 2006355851) B2006355851
theorem B891713711 : Blo 2007435 891713711 := bstep (se 1 (by rfl) ⟨668785283, by rfl⟩ : syracuseStep 891713711 = 1337570567) B1337570567
theorem B594475807 : Blo 2007435 594475807 := bstep (se 1 (by rfl) ⟨445856855, by rfl⟩ : syracuseStep 594475807 = 891713711) B891713711
theorem B792634409 : Blo 2007435 792634409 := bstep (se 2 (by rfl) ⟨297237903, by rfl⟩ : syracuseStep 792634409 = 594475807) B594475807
theorem B528422939 : Blo 2007435 528422939 := bstep (se 1 (by rfl) ⟨396317204, by rfl⟩ : syracuseStep 528422939 = 792634409) B792634409
theorem B352281959 : Blo 2007435 352281959 := bstep (se 1 (by rfl) ⟨264211469, by rfl⟩ : syracuseStep 352281959 = 528422939) B528422939
theorem B234854639 : Blo 2007435 234854639 := bstep (se 1 (by rfl) ⟨176140979, by rfl⟩ : syracuseStep 234854639 = 352281959) B352281959
theorem B156569759 : Blo 2007435 156569759 := bstep (se 1 (by rfl) ⟨117427319, by rfl⟩ : syracuseStep 156569759 = 234854639) B234854639
theorem B104379839 : Blo 2007435 104379839 := bstep (se 1 (by rfl) ⟨78284879, by rfl⟩ : syracuseStep 104379839 = 156569759) B156569759
theorem B69586559 : Blo 2007435 69586559 := bstep (se 1 (by rfl) ⟨52189919, by rfl⟩ : syracuseStep 69586559 = 104379839) B104379839
theorem B46391039 : Blo 2007435 46391039 := bstep (se 1 (by rfl) ⟨34793279, by rfl⟩ : syracuseStep 46391039 = 69586559) B69586559
theorem B30927359 : Blo 2007435 30927359 := bstep (se 1 (by rfl) ⟨23195519, by rfl⟩ : syracuseStep 30927359 = 46391039) B46391039
theorem B20618239 : Blo 2007435 20618239 := bstep (se 1 (by rfl) ⟨15463679, by rfl⟩ : syracuseStep 20618239 = 30927359) B30927359
theorem B27490985 : Blo 2007435 27490985 := bstep (se 2 (by rfl) ⟨10309119, by rfl⟩ : syracuseStep 27490985 = 20618239) B20618239
theorem B18327323 : Blo 2007435 18327323 := bstep (se 1 (by rfl) ⟨13745492, by rfl⟩ : syracuseStep 18327323 = 27490985) B27490985
theorem B12218215 : Blo 2007435 12218215 := bstep (se 1 (by rfl) ⟨9163661, by rfl⟩ : syracuseStep 12218215 = 18327323) B18327323
theorem B16290953 : Blo 2007435 16290953 := bstep (se 2 (by rfl) ⟨6109107, by rfl⟩ : syracuseStep 16290953 = 12218215) B12218215
theorem B10860635 : Blo 2007435 10860635 := bstep (se 1 (by rfl) ⟨8145476, by rfl⟩ : syracuseStep 10860635 = 16290953) B16290953
theorem B7240423 : Blo 2007435 7240423 := bstep (se 1 (by rfl) ⟨5430317, by rfl⟩ : syracuseStep 7240423 = 10860635) B10860635
theorem B9653897 : Blo 2007435 9653897 := bstep (se 2 (by rfl) ⟨3620211, by rfl⟩ : syracuseStep 9653897 = 7240423) B7240423
theorem B6435931 : Blo 2007435 6435931 := bstep (se 1 (by rfl) ⟨4826948, by rfl⟩ : syracuseStep 6435931 = 9653897) B9653897
theorem B8581241 : Blo 2007435 8581241 := bstep (se 2 (by rfl) ⟨3217965, by rfl⟩ : syracuseStep 8581241 = 6435931) B6435931
theorem B22883309 : Blo 2007435 22883309 := bstep (se 3 (by rfl) ⟨4290620, by rfl⟩ : syracuseStep 22883309 = 8581241) B8581241
theorem B15255539 : Blo 2007435 15255539 := bstep (se 1 (by rfl) ⟨11441654, by rfl⟩ : syracuseStep 15255539 = 22883309) B22883309
theorem B10170359 : Blo 2007435 10170359 := bstep (se 1 (by rfl) ⟨7627769, by rfl⟩ : syracuseStep 10170359 = 15255539) B15255539
theorem B6780239 : Blo 2007435 6780239 := bstep (se 1 (by rfl) ⟨5085179, by rfl⟩ : syracuseStep 6780239 = 10170359) B10170359
theorem B4520159 : Blo 2007435 4520159 := bstep (se 1 (by rfl) ⟨3390119, by rfl⟩ : syracuseStep 4520159 = 6780239) B6780239
theorem B3013439 : Blo 2007435 3013439 := bstep (se 1 (by rfl) ⟨2260079, by rfl⟩ : syracuseStep 3013439 = 4520159) B4520159
theorem B2008959 : Blo 2007435 2008959 := bstep (se 1 (by rfl) ⟨1506719, by rfl⟩ : syracuseStep 2008959 = 3013439) B3013439
theorem B3013445 : Blo 2007435 3013445 := bbase (se 4 (by rfl) ⟨282510, by rfl⟩ : syracuseStep 3013445 = 565021) (by norm_num)
theorem B2008963 : Blo 2007435 2008963 := bstep (se 1 (by rfl) ⟨1506722, by rfl⟩ : syracuseStep 2008963 = 3013445) B3013445
theorem B3390133 : Blo 2007435 3390133 := bbase (se 5 (by rfl) ⟨158912, by rfl⟩ : syracuseStep 3390133 = 317825) (by norm_num)
theorem B4520177 : Blo 2007435 4520177 := bstep (se 2 (by rfl) ⟨1695066, by rfl⟩ : syracuseStep 4520177 = 3390133) B3390133
theorem B3013451 : Blo 2007435 3013451 := bstep (se 1 (by rfl) ⟨2260088, by rfl⟩ : syracuseStep 3013451 = 4520177) B4520177
theorem B2008967 : Blo 2007435 2008967 := bstep (se 1 (by rfl) ⟨1506725, by rfl⟩ : syracuseStep 2008967 = 3013451) B3013451
theorem B2260093 : Blo 2007435 2260093 := bbase (se 3 (by rfl) ⟨423767, by rfl⟩ : syracuseStep 2260093 = 847535) (by norm_num)
theorem B3013457 : Blo 2007435 3013457 := bstep (se 2 (by rfl) ⟨1130046, by rfl⟩ : syracuseStep 3013457 = 2260093) B2260093
theorem B2008971 : Blo 2007435 2008971 := bstep (se 1 (by rfl) ⟨1506728, by rfl⟩ : syracuseStep 2008971 = 3013457) B3013457
theorem B6780293 : Blo 2007435 6780293 := bbase (se 4 (by rfl) ⟨635652, by rfl⟩ : syracuseStep 6780293 = 1271305) (by norm_num)
theorem B4520195 : Blo 2007435 4520195 := bstep (se 1 (by rfl) ⟨3390146, by rfl⟩ : syracuseStep 4520195 = 6780293) B6780293
theorem B3013463 : Blo 2007435 3013463 := bstep (se 1 (by rfl) ⟨2260097, by rfl⟩ : syracuseStep 3013463 = 4520195) B4520195
theorem B2008975 : Blo 2007435 2008975 := bstep (se 1 (by rfl) ⟨1506731, by rfl⟩ : syracuseStep 2008975 = 3013463) B3013463
theorem B3013469 : Blo 2007435 3013469 := bbase (se 3 (by rfl) ⟨565025, by rfl⟩ : syracuseStep 3013469 = 1130051) (by norm_num)
theorem B2008979 : Blo 2007435 2008979 := bstep (se 1 (by rfl) ⟨1506734, by rfl⟩ : syracuseStep 2008979 = 3013469) B3013469
theorem B4520213 : Blo 2007435 4520213 := bbase (se 6 (by rfl) ⟨105942, by rfl⟩ : syracuseStep 4520213 = 211885) (by norm_num)
theorem B3013475 : Blo 2007435 3013475 := bstep (se 1 (by rfl) ⟨2260106, by rfl⟩ : syracuseStep 3013475 = 4520213) B4520213
theorem B2008983 : Blo 2007435 2008983 := bstep (se 1 (by rfl) ⟨1506737, by rfl⟩ : syracuseStep 2008983 = 3013475) B3013475
theorem B7627877 : Blo 2007435 7627877 := bbase (se 4 (by rfl) ⟨715113, by rfl⟩ : syracuseStep 7627877 = 1430227) (by norm_num)
theorem B5085251 : Blo 2007435 5085251 := bstep (se 1 (by rfl) ⟨3813938, by rfl⟩ : syracuseStep 5085251 = 7627877) B7627877
theorem B3390167 : Blo 2007435 3390167 := bstep (se 1 (by rfl) ⟨2542625, by rfl⟩ : syracuseStep 3390167 = 5085251) B5085251
theorem B2260111 : Blo 2007435 2260111 := bstep (se 1 (by rfl) ⟨1695083, by rfl⟩ : syracuseStep 2260111 = 3390167) B3390167
theorem B3013481 : Blo 2007435 3013481 := bstep (se 2 (by rfl) ⟨1130055, by rfl⟩ : syracuseStep 3013481 = 2260111) B2260111
theorem B2008987 : Blo 2007435 2008987 := bstep (se 1 (by rfl) ⟨1506740, by rfl⟩ : syracuseStep 2008987 = 3013481) B3013481
theorem B2413513 : Blo 2007435 2413513 := bbase (se 2 (by rfl) ⟨905067, by rfl⟩ : syracuseStep 2413513 = 1810135) (by norm_num)
theorem B3218017 : Blo 2007435 3218017 := bstep (se 2 (by rfl) ⟨1206756, by rfl⟩ : syracuseStep 3218017 = 2413513) B2413513
theorem B4290689 : Blo 2007435 4290689 := bstep (se 2 (by rfl) ⟨1609008, by rfl⟩ : syracuseStep 4290689 = 3218017) B3218017
theorem B11441837 : Blo 2007435 11441837 := bstep (se 3 (by rfl) ⟨2145344, by rfl⟩ : syracuseStep 11441837 = 4290689) B4290689
theorem B7627891 : Blo 2007435 7627891 := bstep (se 1 (by rfl) ⟨5720918, by rfl⟩ : syracuseStep 7627891 = 11441837) B11441837
theorem B10170521 : Blo 2007435 10170521 := bstep (se 2 (by rfl) ⟨3813945, by rfl⟩ : syracuseStep 10170521 = 7627891) B7627891
theorem B6780347 : Blo 2007435 6780347 := bstep (se 1 (by rfl) ⟨5085260, by rfl⟩ : syracuseStep 6780347 = 10170521) B10170521
theorem B4520231 : Blo 2007435 4520231 := bstep (se 1 (by rfl) ⟨3390173, by rfl⟩ : syracuseStep 4520231 = 6780347) B6780347
theorem B3013487 : Blo 2007435 3013487 := bstep (se 1 (by rfl) ⟨2260115, by rfl⟩ : syracuseStep 3013487 = 4520231) B4520231
theorem B2008991 : Blo 2007435 2008991 := bstep (se 1 (by rfl) ⟨1506743, by rfl⟩ : syracuseStep 2008991 = 3013487) B3013487
theorem B3013493 : Blo 2007435 3013493 := bbase (se 5 (by rfl) ⟨141257, by rfl⟩ : syracuseStep 3013493 = 282515) (by norm_num)
theorem B2008995 : Blo 2007435 2008995 := bstep (se 1 (by rfl) ⟨1506746, by rfl⟩ : syracuseStep 2008995 = 3013493) B3013493
theorem B3620285 : Blo 2007435 3620285 := bbase (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) (by norm_num)
theorem B2413523 : Blo 2007435 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B6436061 : Blo 2007435 6436061 := bstep (se 3 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 6436061 = 2413523) B2413523
theorem B4290707 : Blo 2007435 4290707 := bstep (se 1 (by rfl) ⟨3218030, by rfl⟩ : syracuseStep 4290707 = 6436061) B6436061
theorem B2860471 : Blo 2007435 2860471 := bstep (se 1 (by rfl) ⟨2145353, by rfl⟩ : syracuseStep 2860471 = 4290707) B4290707
theorem B3813961 : Blo 2007435 3813961 := bstep (se 2 (by rfl) ⟨1430235, by rfl⟩ : syracuseStep 3813961 = 2860471) B2860471
theorem B5085281 : Blo 2007435 5085281 := bstep (se 2 (by rfl) ⟨1906980, by rfl⟩ : syracuseStep 5085281 = 3813961) B3813961
theorem B3390187 : Blo 2007435 3390187 := bstep (se 1 (by rfl) ⟨2542640, by rfl⟩ : syracuseStep 3390187 = 5085281) B5085281
theorem B4520249 : Blo 2007435 4520249 := bstep (se 2 (by rfl) ⟨1695093, by rfl⟩ : syracuseStep 4520249 = 3390187) B3390187
theorem B3013499 : Blo 2007435 3013499 := bstep (se 1 (by rfl) ⟨2260124, by rfl⟩ : syracuseStep 3013499 = 4520249) B4520249
theorem B2008999 : Blo 2007435 2008999 := bstep (se 1 (by rfl) ⟨1506749, by rfl⟩ : syracuseStep 2008999 = 3013499) B3013499
theorem B2260129 : Blo 2007435 2260129 := bbase (se 2 (by rfl) ⟨847548, by rfl⟩ : syracuseStep 2260129 = 1695097) (by norm_num)
theorem B3013505 : Blo 2007435 3013505 := bstep (se 2 (by rfl) ⟨1130064, by rfl⟩ : syracuseStep 3013505 = 2260129) B2260129
theorem B2009003 : Blo 2007435 2009003 := bstep (se 1 (by rfl) ⟨1506752, by rfl⟩ : syracuseStep 2009003 = 3013505) B3013505
theorem B5085301 : Blo 2007435 5085301 := bbase (se 5 (by rfl) ⟨238373, by rfl⟩ : syracuseStep 5085301 = 476747) (by norm_num)
theorem B6780401 : Blo 2007435 6780401 := bstep (se 2 (by rfl) ⟨2542650, by rfl⟩ : syracuseStep 6780401 = 5085301) B5085301
theorem B4520267 : Blo 2007435 4520267 := bstep (se 1 (by rfl) ⟨3390200, by rfl⟩ : syracuseStep 4520267 = 6780401) B6780401
theorem B3013511 : Blo 2007435 3013511 := bstep (se 1 (by rfl) ⟨2260133, by rfl⟩ : syracuseStep 3013511 = 4520267) B4520267
theorem B2009007 : Blo 2007435 2009007 := bstep (se 1 (by rfl) ⟨1506755, by rfl⟩ : syracuseStep 2009007 = 3013511) B3013511
theorem B3013517 : Blo 2007435 3013517 := bbase (se 3 (by rfl) ⟨565034, by rfl⟩ : syracuseStep 3013517 = 1130069) (by norm_num)
theorem B2009011 : Blo 2007435 2009011 := bstep (se 1 (by rfl) ⟨1506758, by rfl⟩ : syracuseStep 2009011 = 3013517) B3013517
theorem B4520285 : Blo 2007435 4520285 := bbase (se 3 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 4520285 = 1695107) (by norm_num)
theorem B3013523 : Blo 2007435 3013523 := bstep (se 1 (by rfl) ⟨2260142, by rfl⟩ : syracuseStep 3013523 = 4520285) B4520285
theorem B2009015 : Blo 2007435 2009015 := bstep (se 1 (by rfl) ⟨1506761, by rfl⟩ : syracuseStep 2009015 = 3013523) B3013523
theorem B3390221 : Blo 2007435 3390221 := bbase (se 3 (by rfl) ⟨635666, by rfl⟩ : syracuseStep 3390221 = 1271333) (by norm_num)
theorem B2260147 : Blo 2007435 2260147 := bstep (se 1 (by rfl) ⟨1695110, by rfl⟩ : syracuseStep 2260147 = 3390221) B3390221
theorem B3013529 : Blo 2007435 3013529 := bstep (se 2 (by rfl) ⟨1130073, by rfl⟩ : syracuseStep 3013529 = 2260147) B2260147
theorem B2009019 : Blo 2007435 2009019 := bstep (se 1 (by rfl) ⟨1506764, by rfl⟩ : syracuseStep 2009019 = 3013529) B3013529
theorem B17163029 : Blo 2007435 17163029 := bbase (se 6 (by rfl) ⟨402258, by rfl⟩ : syracuseStep 17163029 = 804517) (by norm_num)
theorem B11442019 : Blo 2007435 11442019 := bstep (se 1 (by rfl) ⟨8581514, by rfl⟩ : syracuseStep 11442019 = 17163029) B17163029
theorem B15256025 : Blo 2007435 15256025 := bstep (se 2 (by rfl) ⟨5721009, by rfl⟩ : syracuseStep 15256025 = 11442019) B11442019
theorem B10170683 : Blo 2007435 10170683 := bstep (se 1 (by rfl) ⟨7628012, by rfl⟩ : syracuseStep 10170683 = 15256025) B15256025
theorem B6780455 : Blo 2007435 6780455 := bstep (se 1 (by rfl) ⟨5085341, by rfl⟩ : syracuseStep 6780455 = 10170683) B10170683
theorem B4520303 : Blo 2007435 4520303 := bstep (se 1 (by rfl) ⟨3390227, by rfl⟩ : syracuseStep 4520303 = 6780455) B6780455
theorem B3013535 : Blo 2007435 3013535 := bstep (se 1 (by rfl) ⟨2260151, by rfl⟩ : syracuseStep 3013535 = 4520303) B4520303
theorem B2009023 : Blo 2007435 2009023 := bstep (se 1 (by rfl) ⟨1506767, by rfl⟩ : syracuseStep 2009023 = 3013535) B3013535
theorem B3013541 : Blo 2007435 3013541 := bbase (se 4 (by rfl) ⟨282519, by rfl⟩ : syracuseStep 3013541 = 565039) (by norm_num)
theorem B2009027 : Blo 2007435 2009027 := bstep (se 1 (by rfl) ⟨1506770, by rfl⟩ : syracuseStep 2009027 = 3013541) B3013541
theorem B2542681 : Blo 2007435 2542681 := bbase (se 2 (by rfl) ⟨953505, by rfl⟩ : syracuseStep 2542681 = 1907011) (by norm_num)
theorem B3390241 : Blo 2007435 3390241 := bstep (se 2 (by rfl) ⟨1271340, by rfl⟩ : syracuseStep 3390241 = 2542681) B2542681
theorem B4520321 : Blo 2007435 4520321 := bstep (se 2 (by rfl) ⟨1695120, by rfl⟩ : syracuseStep 4520321 = 3390241) B3390241
theorem B3013547 : Blo 2007435 3013547 := bstep (se 1 (by rfl) ⟨2260160, by rfl⟩ : syracuseStep 3013547 = 4520321) B4520321
theorem B2009031 : Blo 2007435 2009031 := bstep (se 1 (by rfl) ⟨1506773, by rfl⟩ : syracuseStep 2009031 = 3013547) B3013547
theorem B2260165 : Blo 2007435 2260165 := bbase (se 4 (by rfl) ⟨211890, by rfl⟩ : syracuseStep 2260165 = 423781) (by norm_num)
theorem B3013553 : Blo 2007435 3013553 := bstep (se 2 (by rfl) ⟨1130082, by rfl⟩ : syracuseStep 3013553 = 2260165) B2260165
theorem B2009035 : Blo 2007435 2009035 := bstep (se 1 (by rfl) ⟨1506776, by rfl⟩ : syracuseStep 2009035 = 3013553) B3013553
theorem B3814037 : Blo 2007435 3814037 := bbase (se 6 (by rfl) ⟨89391, by rfl⟩ : syracuseStep 3814037 = 178783) (by norm_num)
theorem B2542691 : Blo 2007435 2542691 := bstep (se 1 (by rfl) ⟨1907018, by rfl⟩ : syracuseStep 2542691 = 3814037) B3814037
theorem B6780509 : Blo 2007435 6780509 := bstep (se 3 (by rfl) ⟨1271345, by rfl⟩ : syracuseStep 6780509 = 2542691) B2542691
theorem B4520339 : Blo 2007435 4520339 := bstep (se 1 (by rfl) ⟨3390254, by rfl⟩ : syracuseStep 4520339 = 6780509) B6780509
theorem B3013559 : Blo 2007435 3013559 := bstep (se 1 (by rfl) ⟨2260169, by rfl⟩ : syracuseStep 3013559 = 4520339) B4520339
theorem B2009039 : Blo 2007435 2009039 := bstep (se 1 (by rfl) ⟨1506779, by rfl⟩ : syracuseStep 2009039 = 3013559) B3013559
theorem B3013565 : Blo 2007435 3013565 := bbase (se 3 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 3013565 = 1130087) (by norm_num)
theorem B2009043 : Blo 2007435 2009043 := bstep (se 1 (by rfl) ⟨1506782, by rfl⟩ : syracuseStep 2009043 = 3013565) B3013565
theorem B4520357 : Blo 2007435 4520357 := bbase (se 4 (by rfl) ⟨423783, by rfl⟩ : syracuseStep 4520357 = 847567) (by norm_num)
theorem B3013571 : Blo 2007435 3013571 := bstep (se 1 (by rfl) ⟨2260178, by rfl⟩ : syracuseStep 3013571 = 4520357) B4520357
theorem B2009047 : Blo 2007435 2009047 := bstep (se 1 (by rfl) ⟨1506785, by rfl⟩ : syracuseStep 2009047 = 3013571) B3013571
theorem B5085413 : Blo 2007435 5085413 := bbase (se 4 (by rfl) ⟨476757, by rfl⟩ : syracuseStep 5085413 = 953515) (by norm_num)
theorem B3390275 : Blo 2007435 3390275 := bstep (se 1 (by rfl) ⟨2542706, by rfl⟩ : syracuseStep 3390275 = 5085413) B5085413
theorem B2260183 : Blo 2007435 2260183 := bstep (se 1 (by rfl) ⟨1695137, by rfl⟩ : syracuseStep 2260183 = 3390275) B3390275
theorem B3013577 : Blo 2007435 3013577 := bstep (se 2 (by rfl) ⟨1130091, by rfl⟩ : syracuseStep 3013577 = 2260183) B2260183
theorem B2009051 : Blo 2007435 2009051 := bstep (se 1 (by rfl) ⟨1506788, by rfl⟩ : syracuseStep 2009051 = 3013577) B3013577
theorem B2145413 : Blo 2007435 2145413 := bbase (se 4 (by rfl) ⟨201132, by rfl⟩ : syracuseStep 2145413 = 402265) (by norm_num)
theorem B5721101 : Blo 2007435 5721101 := bstep (se 3 (by rfl) ⟨1072706, by rfl⟩ : syracuseStep 5721101 = 2145413) B2145413
theorem B3814067 : Blo 2007435 3814067 := bstep (se 1 (by rfl) ⟨2860550, by rfl⟩ : syracuseStep 3814067 = 5721101) B5721101
theorem B10170845 : Blo 2007435 10170845 := bstep (se 3 (by rfl) ⟨1907033, by rfl⟩ : syracuseStep 10170845 = 3814067) B3814067
theorem B6780563 : Blo 2007435 6780563 := bstep (se 1 (by rfl) ⟨5085422, by rfl⟩ : syracuseStep 6780563 = 10170845) B10170845
theorem B4520375 : Blo 2007435 4520375 := bstep (se 1 (by rfl) ⟨3390281, by rfl⟩ : syracuseStep 4520375 = 6780563) B6780563
theorem B3013583 : Blo 2007435 3013583 := bstep (se 1 (by rfl) ⟨2260187, by rfl⟩ : syracuseStep 3013583 = 4520375) B4520375
theorem B2009055 : Blo 2007435 2009055 := bstep (se 1 (by rfl) ⟨1506791, by rfl⟩ : syracuseStep 2009055 = 3013583) B3013583
theorem B3013589 : Blo 2007435 3013589 := bbase (se 7 (by rfl) ⟨35315, by rfl⟩ : syracuseStep 3013589 = 70631) (by norm_num)
theorem B2009059 : Blo 2007435 2009059 := bstep (se 1 (by rfl) ⟨1506794, by rfl⟩ : syracuseStep 2009059 = 3013589) B3013589
theorem B7628165 : Blo 2007435 7628165 := bbase (se 4 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 7628165 = 1430281) (by norm_num)
theorem B5085443 : Blo 2007435 5085443 := bstep (se 1 (by rfl) ⟨3814082, by rfl⟩ : syracuseStep 5085443 = 7628165) B7628165
theorem B3390295 : Blo 2007435 3390295 := bstep (se 1 (by rfl) ⟨2542721, by rfl⟩ : syracuseStep 3390295 = 5085443) B5085443
theorem B4520393 : Blo 2007435 4520393 := bstep (se 2 (by rfl) ⟨1695147, by rfl⟩ : syracuseStep 4520393 = 3390295) B3390295
theorem B3013595 : Blo 2007435 3013595 := bstep (se 1 (by rfl) ⟨2260196, by rfl⟩ : syracuseStep 3013595 = 4520393) B4520393
theorem B2009063 : Blo 2007435 2009063 := bstep (se 1 (by rfl) ⟨1506797, by rfl⟩ : syracuseStep 2009063 = 3013595) B3013595
theorem B2260201 : Blo 2007435 2260201 := bbase (se 2 (by rfl) ⟨847575, by rfl⟩ : syracuseStep 2260201 = 1695151) (by norm_num)
theorem B3013601 : Blo 2007435 3013601 := bstep (se 2 (by rfl) ⟨1130100, by rfl⟩ : syracuseStep 3013601 = 2260201) B2260201
theorem B2009067 : Blo 2007435 2009067 := bstep (se 1 (by rfl) ⟨1506800, by rfl⟩ : syracuseStep 2009067 = 3013601) B3013601
theorem B11442293 : Blo 2007435 11442293 := bbase (se 5 (by rfl) ⟨536357, by rfl⟩ : syracuseStep 11442293 = 1072715) (by norm_num)
theorem B7628195 : Blo 2007435 7628195 := bstep (se 1 (by rfl) ⟨5721146, by rfl⟩ : syracuseStep 7628195 = 11442293) B11442293
theorem B5085463 : Blo 2007435 5085463 := bstep (se 1 (by rfl) ⟨3814097, by rfl⟩ : syracuseStep 5085463 = 7628195) B7628195
theorem B6780617 : Blo 2007435 6780617 := bstep (se 2 (by rfl) ⟨2542731, by rfl⟩ : syracuseStep 6780617 = 5085463) B5085463
theorem B4520411 : Blo 2007435 4520411 := bstep (se 1 (by rfl) ⟨3390308, by rfl⟩ : syracuseStep 4520411 = 6780617) B6780617
theorem B3013607 : Blo 2007435 3013607 := bstep (se 1 (by rfl) ⟨2260205, by rfl⟩ : syracuseStep 3013607 = 4520411) B4520411
theorem B2009071 : Blo 2007435 2009071 := bstep (se 1 (by rfl) ⟨1506803, by rfl⟩ : syracuseStep 2009071 = 3013607) B3013607
theorem B3013613 : Blo 2007435 3013613 := bbase (se 3 (by rfl) ⟨565052, by rfl⟩ : syracuseStep 3013613 = 1130105) (by norm_num)
theorem B2009075 : Blo 2007435 2009075 := bstep (se 1 (by rfl) ⟨1506806, by rfl⟩ : syracuseStep 2009075 = 3013613) B3013613
theorem B4520429 : Blo 2007435 4520429 := bbase (se 3 (by rfl) ⟨847580, by rfl⟩ : syracuseStep 4520429 = 1695161) (by norm_num)
theorem B3013619 : Blo 2007435 3013619 := bstep (se 1 (by rfl) ⟨2260214, by rfl⟩ : syracuseStep 3013619 = 4520429) B4520429
theorem B2009079 : Blo 2007435 2009079 := bstep (se 1 (by rfl) ⟨1506809, by rfl⟩ : syracuseStep 2009079 = 3013619) B3013619
theorem B2322317 : Blo 2007435 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B6192845 : Blo 2007435 6192845 := bstep (se 3 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 6192845 = 2322317) B2322317
theorem B4128563 : Blo 2007435 4128563 := bstep (se 1 (by rfl) ⟨3096422, by rfl⟩ : syracuseStep 4128563 = 6192845) B6192845
theorem B2752375 : Blo 2007435 2752375 := bstep (se 1 (by rfl) ⟨2064281, by rfl⟩ : syracuseStep 2752375 = 4128563) B4128563
theorem B3669833 : Blo 2007435 3669833 := bstep (se 2 (by rfl) ⟨1376187, by rfl⟩ : syracuseStep 3669833 = 2752375) B2752375
theorem B2446555 : Blo 2007435 2446555 := bstep (se 1 (by rfl) ⟨1834916, by rfl⟩ : syracuseStep 2446555 = 3669833) B3669833
theorem B3262073 : Blo 2007435 3262073 := bstep (se 2 (by rfl) ⟨1223277, by rfl⟩ : syracuseStep 3262073 = 2446555) B2446555
theorem B8698861 : Blo 2007435 8698861 := bstep (se 3 (by rfl) ⟨1631036, by rfl⟩ : syracuseStep 8698861 = 3262073) B3262073
theorem B11598481 : Blo 2007435 11598481 := bstep (se 2 (by rfl) ⟨4349430, by rfl⟩ : syracuseStep 11598481 = 8698861) B8698861
theorem B61858565 : Blo 2007435 61858565 := bstep (se 4 (by rfl) ⟨5799240, by rfl⟩ : syracuseStep 61858565 = 11598481) B11598481
theorem B41239043 : Blo 2007435 41239043 := bstep (se 1 (by rfl) ⟨30929282, by rfl⟩ : syracuseStep 41239043 = 61858565) B61858565
theorem B27492695 : Blo 2007435 27492695 := bstep (se 1 (by rfl) ⟨20619521, by rfl⟩ : syracuseStep 27492695 = 41239043) B41239043
theorem B18328463 : Blo 2007435 18328463 := bstep (se 1 (by rfl) ⟨13746347, by rfl⟩ : syracuseStep 18328463 = 27492695) B27492695
theorem B12218975 : Blo 2007435 12218975 := bstep (se 1 (by rfl) ⟨9164231, by rfl⟩ : syracuseStep 12218975 = 18328463) B18328463
theorem B8145983 : Blo 2007435 8145983 := bstep (se 1 (by rfl) ⟨6109487, by rfl⟩ : syracuseStep 8145983 = 12218975) B12218975
theorem B5430655 : Blo 2007435 5430655 := bstep (se 1 (by rfl) ⟨4072991, by rfl⟩ : syracuseStep 5430655 = 8145983) B8145983
theorem B7240873 : Blo 2007435 7240873 := bstep (se 2 (by rfl) ⟨2715327, by rfl⟩ : syracuseStep 7240873 = 5430655) B5430655
theorem B9654497 : Blo 2007435 9654497 := bstep (se 2 (by rfl) ⟨3620436, by rfl⟩ : syracuseStep 9654497 = 7240873) B7240873
theorem B6436331 : Blo 2007435 6436331 := bstep (se 1 (by rfl) ⟨4827248, by rfl⟩ : syracuseStep 6436331 = 9654497) B9654497
theorem B4290887 : Blo 2007435 4290887 := bstep (se 1 (by rfl) ⟨3218165, by rfl⟩ : syracuseStep 4290887 = 6436331) B6436331
theorem B2860591 : Blo 2007435 2860591 := bstep (se 1 (by rfl) ⟨2145443, by rfl⟩ : syracuseStep 2860591 = 4290887) B4290887
theorem B3814121 : Blo 2007435 3814121 := bstep (se 2 (by rfl) ⟨1430295, by rfl⟩ : syracuseStep 3814121 = 2860591) B2860591
theorem B2542747 : Blo 2007435 2542747 := bstep (se 1 (by rfl) ⟨1907060, by rfl⟩ : syracuseStep 2542747 = 3814121) B3814121
theorem B3390329 : Blo 2007435 3390329 := bstep (se 2 (by rfl) ⟨1271373, by rfl⟩ : syracuseStep 3390329 = 2542747) B2542747
theorem B2260219 : Blo 2007435 2260219 := bstep (se 1 (by rfl) ⟨1695164, by rfl⟩ : syracuseStep 2260219 = 3390329) B3390329
theorem B3013625 : Blo 2007435 3013625 := bstep (se 2 (by rfl) ⟨1130109, by rfl⟩ : syracuseStep 3013625 = 2260219) B2260219
theorem B2009083 : Blo 2007435 2009083 := bstep (se 1 (by rfl) ⟨1506812, by rfl⟩ : syracuseStep 2009083 = 3013625) B3013625
theorem B4644637 : Blo 2007435 4644637 := bbase (se 3 (by rfl) ⟨870869, by rfl⟩ : syracuseStep 4644637 = 1741739) (by norm_num)
theorem B24771397 : Blo 2007435 24771397 := bstep (se 4 (by rfl) ⟨2322318, by rfl⟩ : syracuseStep 24771397 = 4644637) B4644637
theorem B33028529 : Blo 2007435 33028529 := bstep (se 2 (by rfl) ⟨12385698, by rfl⟩ : syracuseStep 33028529 = 24771397) B24771397
theorem B352304309 : Blo 2007435 352304309 := bstep (se 5 (by rfl) ⟨16514264, by rfl⟩ : syracuseStep 352304309 = 33028529) B33028529
theorem B234869539 : Blo 2007435 234869539 := bstep (se 1 (by rfl) ⟨176152154, by rfl⟩ : syracuseStep 234869539 = 352304309) B352304309
theorem B313159385 : Blo 2007435 313159385 := bstep (se 2 (by rfl) ⟨117434769, by rfl⟩ : syracuseStep 313159385 = 234869539) B234869539
theorem B208772923 : Blo 2007435 208772923 := bstep (se 1 (by rfl) ⟨156579692, by rfl⟩ : syracuseStep 208772923 = 313159385) B313159385
theorem B278363897 : Blo 2007435 278363897 := bstep (se 2 (by rfl) ⟨104386461, by rfl⟩ : syracuseStep 278363897 = 208772923) B208772923
theorem B185575931 : Blo 2007435 185575931 := bstep (se 1 (by rfl) ⟨139181948, by rfl⟩ : syracuseStep 185575931 = 278363897) B278363897
theorem B123717287 : Blo 2007435 123717287 := bstep (se 1 (by rfl) ⟨92787965, by rfl⟩ : syracuseStep 123717287 = 185575931) B185575931
theorem B82478191 : Blo 2007435 82478191 := bstep (se 1 (by rfl) ⟨61858643, by rfl⟩ : syracuseStep 82478191 = 123717287) B123717287
theorem B109970921 : Blo 2007435 109970921 := bstep (se 2 (by rfl) ⟨41239095, by rfl⟩ : syracuseStep 109970921 = 82478191) B82478191
theorem B73313947 : Blo 2007435 73313947 := bstep (se 1 (by rfl) ⟨54985460, by rfl⟩ : syracuseStep 73313947 = 109970921) B109970921
theorem B97751929 : Blo 2007435 97751929 := bstep (se 2 (by rfl) ⟨36656973, by rfl⟩ : syracuseStep 97751929 = 73313947) B73313947
theorem B130335905 : Blo 2007435 130335905 := bstep (se 2 (by rfl) ⟨48875964, by rfl⟩ : syracuseStep 130335905 = 97751929) B97751929
theorem B86890603 : Blo 2007435 86890603 := bstep (se 1 (by rfl) ⟨65167952, by rfl⟩ : syracuseStep 86890603 = 130335905) B130335905
theorem B115854137 : Blo 2007435 115854137 := bstep (se 2 (by rfl) ⟨43445301, by rfl⟩ : syracuseStep 115854137 = 86890603) B86890603
theorem B77236091 : Blo 2007435 77236091 := bstep (se 1 (by rfl) ⟨57927068, by rfl⟩ : syracuseStep 77236091 = 115854137) B115854137
theorem B51490727 : Blo 2007435 51490727 := bstep (se 1 (by rfl) ⟨38618045, by rfl⟩ : syracuseStep 51490727 = 77236091) B77236091
theorem B34327151 : Blo 2007435 34327151 := bstep (se 1 (by rfl) ⟨25745363, by rfl⟩ : syracuseStep 34327151 = 51490727) B51490727
theorem B22884767 : Blo 2007435 22884767 := bstep (se 1 (by rfl) ⟨17163575, by rfl⟩ : syracuseStep 22884767 = 34327151) B34327151
theorem B15256511 : Blo 2007435 15256511 := bstep (se 1 (by rfl) ⟨11442383, by rfl⟩ : syracuseStep 15256511 = 22884767) B22884767
theorem B10171007 : Blo 2007435 10171007 := bstep (se 1 (by rfl) ⟨7628255, by rfl⟩ : syracuseStep 10171007 = 15256511) B15256511
theorem B6780671 : Blo 2007435 6780671 := bstep (se 1 (by rfl) ⟨5085503, by rfl⟩ : syracuseStep 6780671 = 10171007) B10171007
theorem B4520447 : Blo 2007435 4520447 := bstep (se 1 (by rfl) ⟨3390335, by rfl⟩ : syracuseStep 4520447 = 6780671) B6780671
theorem B3013631 : Blo 2007435 3013631 := bstep (se 1 (by rfl) ⟨2260223, by rfl⟩ : syracuseStep 3013631 = 4520447) B4520447
theorem B2009087 : Blo 2007435 2009087 := bstep (se 1 (by rfl) ⟨1506815, by rfl⟩ : syracuseStep 2009087 = 3013631) B3013631
theorem B3013637 : Blo 2007435 3013637 := bbase (se 4 (by rfl) ⟨282528, by rfl⟩ : syracuseStep 3013637 = 565057) (by norm_num)
theorem B2009091 : Blo 2007435 2009091 := bstep (se 1 (by rfl) ⟨1506818, by rfl⟩ : syracuseStep 2009091 = 3013637) B3013637
theorem B3390349 : Blo 2007435 3390349 := bbase (se 3 (by rfl) ⟨635690, by rfl⟩ : syracuseStep 3390349 = 1271381) (by norm_num)
theorem B4520465 : Blo 2007435 4520465 := bstep (se 2 (by rfl) ⟨1695174, by rfl⟩ : syracuseStep 4520465 = 3390349) B3390349
theorem B3013643 : Blo 2007435 3013643 := bstep (se 1 (by rfl) ⟨2260232, by rfl⟩ : syracuseStep 3013643 = 4520465) B4520465
theorem B2009095 : Blo 2007435 2009095 := bstep (se 1 (by rfl) ⟨1506821, by rfl⟩ : syracuseStep 2009095 = 3013643) B3013643
theorem B2260237 : Blo 2007435 2260237 := bbase (se 3 (by rfl) ⟨423794, by rfl⟩ : syracuseStep 2260237 = 847589) (by norm_num)
theorem B3013649 : Blo 2007435 3013649 := bstep (se 2 (by rfl) ⟨1130118, by rfl⟩ : syracuseStep 3013649 = 2260237) B2260237
theorem B2009099 : Blo 2007435 2009099 := bstep (se 1 (by rfl) ⟨1506824, by rfl⟩ : syracuseStep 2009099 = 3013649) B3013649
theorem B6780725 : Blo 2007435 6780725 := bbase (se 5 (by rfl) ⟨317846, by rfl⟩ : syracuseStep 6780725 = 635693) (by norm_num)
theorem B4520483 : Blo 2007435 4520483 := bstep (se 1 (by rfl) ⟨3390362, by rfl⟩ : syracuseStep 4520483 = 6780725) B6780725
theorem B3013655 : Blo 2007435 3013655 := bstep (se 1 (by rfl) ⟨2260241, by rfl⟩ : syracuseStep 3013655 = 4520483) B4520483
theorem B2009103 : Blo 2007435 2009103 := bstep (se 1 (by rfl) ⟨1506827, by rfl⟩ : syracuseStep 2009103 = 3013655) B3013655
theorem B3013661 : Blo 2007435 3013661 := bbase (se 3 (by rfl) ⟨565061, by rfl⟩ : syracuseStep 3013661 = 1130123) (by norm_num)
theorem B2009107 : Blo 2007435 2009107 := bstep (se 1 (by rfl) ⟨1506830, by rfl⟩ : syracuseStep 2009107 = 3013661) B3013661
theorem B4520501 : Blo 2007435 4520501 := bbase (se 5 (by rfl) ⟨211898, by rfl⟩ : syracuseStep 4520501 = 423797) (by norm_num)
theorem B3013667 : Blo 2007435 3013667 := bstep (se 1 (by rfl) ⟨2260250, by rfl⟩ : syracuseStep 3013667 = 4520501) B4520501
theorem B2009111 : Blo 2007435 2009111 := bstep (se 1 (by rfl) ⟨1506833, by rfl⟩ : syracuseStep 2009111 = 3013667) B3013667
theorem B8581909 : Blo 2007435 8581909 := bbase (se 6 (by rfl) ⟨201138, by rfl⟩ : syracuseStep 8581909 = 402277) (by norm_num)
theorem B11442545 : Blo 2007435 11442545 := bstep (se 2 (by rfl) ⟨4290954, by rfl⟩ : syracuseStep 11442545 = 8581909) B8581909
theorem B7628363 : Blo 2007435 7628363 := bstep (se 1 (by rfl) ⟨5721272, by rfl⟩ : syracuseStep 7628363 = 11442545) B11442545
theorem B5085575 : Blo 2007435 5085575 := bstep (se 1 (by rfl) ⟨3814181, by rfl⟩ : syracuseStep 5085575 = 7628363) B7628363
theorem B3390383 : Blo 2007435 3390383 := bstep (se 1 (by rfl) ⟨2542787, by rfl⟩ : syracuseStep 3390383 = 5085575) B5085575
theorem B2260255 : Blo 2007435 2260255 := bstep (se 1 (by rfl) ⟨1695191, by rfl⟩ : syracuseStep 2260255 = 3390383) B3390383
theorem B3013673 : Blo 2007435 3013673 := bstep (se 2 (by rfl) ⟨1130127, by rfl⟩ : syracuseStep 3013673 = 2260255) B2260255
theorem B2009115 : Blo 2007435 2009115 := bstep (se 1 (by rfl) ⟨1506836, by rfl⟩ : syracuseStep 2009115 = 3013673) B3013673
theorem B8581925 : Blo 2007435 8581925 := bbase (se 4 (by rfl) ⟨804555, by rfl⟩ : syracuseStep 8581925 = 1609111) (by norm_num)
theorem B5721283 : Blo 2007435 5721283 := bstep (se 1 (by rfl) ⟨4290962, by rfl⟩ : syracuseStep 5721283 = 8581925) B8581925
theorem B7628377 : Blo 2007435 7628377 := bstep (se 2 (by rfl) ⟨2860641, by rfl⟩ : syracuseStep 7628377 = 5721283) B5721283
theorem B10171169 : Blo 2007435 10171169 := bstep (se 2 (by rfl) ⟨3814188, by rfl⟩ : syracuseStep 10171169 = 7628377) B7628377
theorem B6780779 : Blo 2007435 6780779 := bstep (se 1 (by rfl) ⟨5085584, by rfl⟩ : syracuseStep 6780779 = 10171169) B10171169
theorem B4520519 : Blo 2007435 4520519 := bstep (se 1 (by rfl) ⟨3390389, by rfl⟩ : syracuseStep 4520519 = 6780779) B6780779
theorem B3013679 : Blo 2007435 3013679 := bstep (se 1 (by rfl) ⟨2260259, by rfl⟩ : syracuseStep 3013679 = 4520519) B4520519
theorem B2009119 : Blo 2007435 2009119 := bstep (se 1 (by rfl) ⟨1506839, by rfl⟩ : syracuseStep 2009119 = 3013679) B3013679
theorem B3013685 : Blo 2007435 3013685 := bbase (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) (by norm_num)
theorem B2009123 : Blo 2007435 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B5085605 : Blo 2007435 5085605 := bbase (se 4 (by rfl) ⟨476775, by rfl⟩ : syracuseStep 5085605 = 953551) (by norm_num)
theorem B3390403 : Blo 2007435 3390403 := bstep (se 1 (by rfl) ⟨2542802, by rfl⟩ : syracuseStep 3390403 = 5085605) B5085605
theorem B4520537 : Blo 2007435 4520537 := bstep (se 2 (by rfl) ⟨1695201, by rfl⟩ : syracuseStep 4520537 = 3390403) B3390403
theorem B3013691 : Blo 2007435 3013691 := bstep (se 1 (by rfl) ⟨2260268, by rfl⟩ : syracuseStep 3013691 = 4520537) B4520537
theorem B2009127 : Blo 2007435 2009127 := bstep (se 1 (by rfl) ⟨1506845, by rfl⟩ : syracuseStep 2009127 = 3013691) B3013691
theorem B2260273 : Blo 2007435 2260273 := bbase (se 2 (by rfl) ⟨847602, by rfl⟩ : syracuseStep 2260273 = 1695205) (by norm_num)
theorem B3013697 : Blo 2007435 3013697 := bstep (se 2 (by rfl) ⟨1130136, by rfl⟩ : syracuseStep 3013697 = 2260273) B2260273
theorem B2009131 : Blo 2007435 2009131 := bstep (se 1 (by rfl) ⟨1506848, by rfl⟩ : syracuseStep 2009131 = 3013697) B3013697
theorem B4290997 : Blo 2007435 4290997 := bbase (se 5 (by rfl) ⟨201140, by rfl⟩ : syracuseStep 4290997 = 402281) (by norm_num)
theorem B5721329 : Blo 2007435 5721329 := bstep (se 2 (by rfl) ⟨2145498, by rfl⟩ : syracuseStep 5721329 = 4290997) B4290997
theorem B3814219 : Blo 2007435 3814219 := bstep (se 1 (by rfl) ⟨2860664, by rfl⟩ : syracuseStep 3814219 = 5721329) B5721329
theorem B5085625 : Blo 2007435 5085625 := bstep (se 2 (by rfl) ⟨1907109, by rfl⟩ : syracuseStep 5085625 = 3814219) B3814219
theorem B6780833 : Blo 2007435 6780833 := bstep (se 2 (by rfl) ⟨2542812, by rfl⟩ : syracuseStep 6780833 = 5085625) B5085625
theorem B4520555 : Blo 2007435 4520555 := bstep (se 1 (by rfl) ⟨3390416, by rfl⟩ : syracuseStep 4520555 = 6780833) B6780833
theorem B3013703 : Blo 2007435 3013703 := bstep (se 1 (by rfl) ⟨2260277, by rfl⟩ : syracuseStep 3013703 = 4520555) B4520555
theorem B2009135 : Blo 2007435 2009135 := bstep (se 1 (by rfl) ⟨1506851, by rfl⟩ : syracuseStep 2009135 = 3013703) B3013703
theorem B3013709 : Blo 2007435 3013709 := bbase (se 3 (by rfl) ⟨565070, by rfl⟩ : syracuseStep 3013709 = 1130141) (by norm_num)
theorem B2009139 : Blo 2007435 2009139 := bstep (se 1 (by rfl) ⟨1506854, by rfl⟩ : syracuseStep 2009139 = 3013709) B3013709
theorem B4520573 : Blo 2007435 4520573 := bbase (se 3 (by rfl) ⟨847607, by rfl⟩ : syracuseStep 4520573 = 1695215) (by norm_num)
theorem B3013715 : Blo 2007435 3013715 := bstep (se 1 (by rfl) ⟨2260286, by rfl⟩ : syracuseStep 3013715 = 4520573) B4520573
theorem B2009143 : Blo 2007435 2009143 := bstep (se 1 (by rfl) ⟨1506857, by rfl⟩ : syracuseStep 2009143 = 3013715) B3013715
theorem B3390437 : Blo 2007435 3390437 := bbase (se 4 (by rfl) ⟨317853, by rfl⟩ : syracuseStep 3390437 = 635707) (by norm_num)
theorem B2260291 : Blo 2007435 2260291 := bstep (se 1 (by rfl) ⟨1695218, by rfl⟩ : syracuseStep 2260291 = 3390437) B3390437
theorem B3013721 : Blo 2007435 3013721 := bstep (se 2 (by rfl) ⟨1130145, by rfl⟩ : syracuseStep 3013721 = 2260291) B2260291
theorem B2009147 : Blo 2007435 2009147 := bstep (se 1 (by rfl) ⟨1506860, by rfl⟩ : syracuseStep 2009147 = 3013721) B3013721
theorem B9654821 : Blo 2007435 9654821 := bbase (se 4 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 9654821 = 1810279) (by norm_num)
theorem B6436547 : Blo 2007435 6436547 := bstep (se 1 (by rfl) ⟨4827410, by rfl⟩ : syracuseStep 6436547 = 9654821) B9654821
theorem B4291031 : Blo 2007435 4291031 := bstep (se 1 (by rfl) ⟨3218273, by rfl⟩ : syracuseStep 4291031 = 6436547) B6436547
theorem B2860687 : Blo 2007435 2860687 := bstep (se 1 (by rfl) ⟨2145515, by rfl⟩ : syracuseStep 2860687 = 4291031) B4291031
theorem B15256997 : Blo 2007435 15256997 := bstep (se 4 (by rfl) ⟨1430343, by rfl⟩ : syracuseStep 15256997 = 2860687) B2860687
theorem B10171331 : Blo 2007435 10171331 := bstep (se 1 (by rfl) ⟨7628498, by rfl⟩ : syracuseStep 10171331 = 15256997) B15256997
theorem B6780887 : Blo 2007435 6780887 := bstep (se 1 (by rfl) ⟨5085665, by rfl⟩ : syracuseStep 6780887 = 10171331) B10171331
theorem B4520591 : Blo 2007435 4520591 := bstep (se 1 (by rfl) ⟨3390443, by rfl⟩ : syracuseStep 4520591 = 6780887) B6780887
theorem B3013727 : Blo 2007435 3013727 := bstep (se 1 (by rfl) ⟨2260295, by rfl⟩ : syracuseStep 3013727 = 4520591) B4520591
theorem B2009151 : Blo 2007435 2009151 := bstep (se 1 (by rfl) ⟨1506863, by rfl⟩ : syracuseStep 2009151 = 3013727) B3013727
theorem B3013733 : Blo 2007435 3013733 := bbase (se 4 (by rfl) ⟨282537, by rfl⟩ : syracuseStep 3013733 = 565075) (by norm_num)
theorem B2009155 : Blo 2007435 2009155 := bstep (se 1 (by rfl) ⟨1506866, by rfl⟩ : syracuseStep 2009155 = 3013733) B3013733
theorem B3436717 : Blo 2007435 3436717 := bbase (se 3 (by rfl) ⟨644384, by rfl⟩ : syracuseStep 3436717 = 1288769) (by norm_num)
theorem B4582289 : Blo 2007435 4582289 := bstep (se 2 (by rfl) ⟨1718358, by rfl⟩ : syracuseStep 4582289 = 3436717) B3436717
theorem B12219437 : Blo 2007435 12219437 := bstep (se 3 (by rfl) ⟨2291144, by rfl⟩ : syracuseStep 12219437 = 4582289) B4582289
theorem B8146291 : Blo 2007435 8146291 := bstep (se 1 (by rfl) ⟨6109718, by rfl⟩ : syracuseStep 8146291 = 12219437) B12219437
theorem B10861721 : Blo 2007435 10861721 := bstep (se 2 (by rfl) ⟨4073145, by rfl⟩ : syracuseStep 10861721 = 8146291) B8146291
theorem B7241147 : Blo 2007435 7241147 := bstep (se 1 (by rfl) ⟨5430860, by rfl⟩ : syracuseStep 7241147 = 10861721) B10861721
theorem B4827431 : Blo 2007435 4827431 := bstep (se 1 (by rfl) ⟨3620573, by rfl⟩ : syracuseStep 4827431 = 7241147) B7241147
theorem B3218287 : Blo 2007435 3218287 := bstep (se 1 (by rfl) ⟨2413715, by rfl⟩ : syracuseStep 3218287 = 4827431) B4827431
theorem B4291049 : Blo 2007435 4291049 := bstep (se 2 (by rfl) ⟨1609143, by rfl⟩ : syracuseStep 4291049 = 3218287) B3218287
theorem B2860699 : Blo 2007435 2860699 := bstep (se 1 (by rfl) ⟨2145524, by rfl⟩ : syracuseStep 2860699 = 4291049) B4291049
theorem B3814265 : Blo 2007435 3814265 := bstep (se 2 (by rfl) ⟨1430349, by rfl⟩ : syracuseStep 3814265 = 2860699) B2860699
theorem B2542843 : Blo 2007435 2542843 := bstep (se 1 (by rfl) ⟨1907132, by rfl⟩ : syracuseStep 2542843 = 3814265) B3814265
theorem B3390457 : Blo 2007435 3390457 := bstep (se 2 (by rfl) ⟨1271421, by rfl⟩ : syracuseStep 3390457 = 2542843) B2542843
theorem B4520609 : Blo 2007435 4520609 := bstep (se 2 (by rfl) ⟨1695228, by rfl⟩ : syracuseStep 4520609 = 3390457) B3390457
theorem B3013739 : Blo 2007435 3013739 := bstep (se 1 (by rfl) ⟨2260304, by rfl⟩ : syracuseStep 3013739 = 4520609) B4520609
theorem B2009159 : Blo 2007435 2009159 := bstep (se 1 (by rfl) ⟨1506869, by rfl⟩ : syracuseStep 2009159 = 3013739) B3013739
theorem B2260309 : Blo 2007435 2260309 := bbase (se 11 (by rfl) ⟨1655, by rfl⟩ : syracuseStep 2260309 = 3311) (by norm_num)
theorem B3013745 : Blo 2007435 3013745 := bstep (se 2 (by rfl) ⟨1130154, by rfl⟩ : syracuseStep 3013745 = 2260309) B2260309
theorem B2009163 : Blo 2007435 2009163 := bstep (se 1 (by rfl) ⟨1506872, by rfl⟩ : syracuseStep 2009163 = 3013745) B3013745
theorem B2542853 : Blo 2007435 2542853 := bbase (se 4 (by rfl) ⟨238392, by rfl⟩ : syracuseStep 2542853 = 476785) (by norm_num)
theorem B6780941 : Blo 2007435 6780941 := bstep (se 3 (by rfl) ⟨1271426, by rfl⟩ : syracuseStep 6780941 = 2542853) B2542853
theorem B4520627 : Blo 2007435 4520627 := bstep (se 1 (by rfl) ⟨3390470, by rfl⟩ : syracuseStep 4520627 = 6780941) B6780941
theorem B3013751 : Blo 2007435 3013751 := bstep (se 1 (by rfl) ⟨2260313, by rfl⟩ : syracuseStep 3013751 = 4520627) B4520627
theorem B2009167 : Blo 2007435 2009167 := bstep (se 1 (by rfl) ⟨1506875, by rfl⟩ : syracuseStep 2009167 = 3013751) B3013751
theorem B3013757 : Blo 2007435 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B2009171 : Blo 2007435 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B4520645 : Blo 2007435 4520645 := bbase (se 4 (by rfl) ⟨423810, by rfl⟩ : syracuseStep 4520645 = 847621) (by norm_num)
theorem B3013763 : Blo 2007435 3013763 := bstep (se 1 (by rfl) ⟨2260322, by rfl⟩ : syracuseStep 3013763 = 4520645) B4520645
theorem B2009175 : Blo 2007435 2009175 := bstep (se 1 (by rfl) ⟨1506881, by rfl⟩ : syracuseStep 2009175 = 3013763) B3013763
theorem B5505013 : Blo 2007435 5505013 := bbase (se 5 (by rfl) ⟨258047, by rfl⟩ : syracuseStep 5505013 = 516095) (by norm_num)
theorem B7340017 : Blo 2007435 7340017 := bstep (se 2 (by rfl) ⟨2752506, by rfl⟩ : syracuseStep 7340017 = 5505013) B5505013
theorem B9786689 : Blo 2007435 9786689 := bstep (se 2 (by rfl) ⟨3670008, by rfl⟩ : syracuseStep 9786689 = 7340017) B7340017
theorem B6524459 : Blo 2007435 6524459 := bstep (se 1 (by rfl) ⟨4893344, by rfl⟩ : syracuseStep 6524459 = 9786689) B9786689
theorem B4349639 : Blo 2007435 4349639 := bstep (se 1 (by rfl) ⟨3262229, by rfl⟩ : syracuseStep 4349639 = 6524459) B6524459
theorem B11599037 : Blo 2007435 11599037 := bstep (se 3 (by rfl) ⟨2174819, by rfl⟩ : syracuseStep 11599037 = 4349639) B4349639
theorem B7732691 : Blo 2007435 7732691 := bstep (se 1 (by rfl) ⟨5799518, by rfl⟩ : syracuseStep 7732691 = 11599037) B11599037
theorem B5155127 : Blo 2007435 5155127 := bstep (se 1 (by rfl) ⟨3866345, by rfl⟩ : syracuseStep 5155127 = 7732691) B7732691
theorem B3436751 : Blo 2007435 3436751 := bstep (se 1 (by rfl) ⟨2577563, by rfl⟩ : syracuseStep 3436751 = 5155127) B5155127
theorem B2291167 : Blo 2007435 2291167 := bstep (se 1 (by rfl) ⟨1718375, by rfl⟩ : syracuseStep 2291167 = 3436751) B3436751
theorem B3054889 : Blo 2007435 3054889 := bstep (se 2 (by rfl) ⟨1145583, by rfl⟩ : syracuseStep 3054889 = 2291167) B2291167
theorem B4073185 : Blo 2007435 4073185 := bstep (se 2 (by rfl) ⟨1527444, by rfl⟩ : syracuseStep 4073185 = 3054889) B3054889
theorem B21723653 : Blo 2007435 21723653 := bstep (se 4 (by rfl) ⟨2036592, by rfl⟩ : syracuseStep 21723653 = 4073185) B4073185
theorem B14482435 : Blo 2007435 14482435 := bstep (se 1 (by rfl) ⟨10861826, by rfl⟩ : syracuseStep 14482435 = 21723653) B21723653
theorem B19309913 : Blo 2007435 19309913 := bstep (se 2 (by rfl) ⟨7241217, by rfl⟩ : syracuseStep 19309913 = 14482435) B14482435
theorem B12873275 : Blo 2007435 12873275 := bstep (se 1 (by rfl) ⟨9654956, by rfl⟩ : syracuseStep 12873275 = 19309913) B19309913
theorem B8582183 : Blo 2007435 8582183 := bstep (se 1 (by rfl) ⟨6436637, by rfl⟩ : syracuseStep 8582183 = 12873275) B12873275
theorem B5721455 : Blo 2007435 5721455 := bstep (se 1 (by rfl) ⟨4291091, by rfl⟩ : syracuseStep 5721455 = 8582183) B8582183
theorem B3814303 : Blo 2007435 3814303 := bstep (se 1 (by rfl) ⟨2860727, by rfl⟩ : syracuseStep 3814303 = 5721455) B5721455
theorem B5085737 : Blo 2007435 5085737 := bstep (se 2 (by rfl) ⟨1907151, by rfl⟩ : syracuseStep 5085737 = 3814303) B3814303
theorem B3390491 : Blo 2007435 3390491 := bstep (se 1 (by rfl) ⟨2542868, by rfl⟩ : syracuseStep 3390491 = 5085737) B5085737
theorem B2260327 : Blo 2007435 2260327 := bstep (se 1 (by rfl) ⟨1695245, by rfl⟩ : syracuseStep 2260327 = 3390491) B3390491
theorem B3013769 : Blo 2007435 3013769 := bstep (se 2 (by rfl) ⟨1130163, by rfl⟩ : syracuseStep 3013769 = 2260327) B2260327
theorem B2009179 : Blo 2007435 2009179 := bstep (se 1 (by rfl) ⟨1506884, by rfl⟩ : syracuseStep 2009179 = 3013769) B3013769
theorem B10171493 : Blo 2007435 10171493 := bbase (se 4 (by rfl) ⟨953577, by rfl⟩ : syracuseStep 10171493 = 1907155) (by norm_num)
theorem B6780995 : Blo 2007435 6780995 := bstep (se 1 (by rfl) ⟨5085746, by rfl⟩ : syracuseStep 6780995 = 10171493) B10171493
theorem B4520663 : Blo 2007435 4520663 := bstep (se 1 (by rfl) ⟨3390497, by rfl⟩ : syracuseStep 4520663 = 6780995) B6780995
theorem B3013775 : Blo 2007435 3013775 := bstep (se 1 (by rfl) ⟨2260331, by rfl⟩ : syracuseStep 3013775 = 4520663) B4520663
theorem B2009183 : Blo 2007435 2009183 := bstep (se 1 (by rfl) ⟨1506887, by rfl⟩ : syracuseStep 2009183 = 3013775) B3013775
theorem B3013781 : Blo 2007435 3013781 := bbase (se 6 (by rfl) ⟨70635, by rfl⟩ : syracuseStep 3013781 = 141271) (by norm_num)
theorem B2009187 : Blo 2007435 2009187 := bstep (se 1 (by rfl) ⟨1506890, by rfl⟩ : syracuseStep 2009187 = 3013781) B3013781
theorem B9655013 : Blo 2007435 9655013 := bbase (se 4 (by rfl) ⟨905157, by rfl⟩ : syracuseStep 9655013 = 1810315) (by norm_num)
theorem B6436675 : Blo 2007435 6436675 := bstep (se 1 (by rfl) ⟨4827506, by rfl⟩ : syracuseStep 6436675 = 9655013) B9655013
theorem B8582233 : Blo 2007435 8582233 := bstep (se 2 (by rfl) ⟨3218337, by rfl⟩ : syracuseStep 8582233 = 6436675) B6436675
theorem B11442977 : Blo 2007435 11442977 := bstep (se 2 (by rfl) ⟨4291116, by rfl⟩ : syracuseStep 11442977 = 8582233) B8582233
theorem B7628651 : Blo 2007435 7628651 := bstep (se 1 (by rfl) ⟨5721488, by rfl⟩ : syracuseStep 7628651 = 11442977) B11442977
theorem B5085767 : Blo 2007435 5085767 := bstep (se 1 (by rfl) ⟨3814325, by rfl⟩ : syracuseStep 5085767 = 7628651) B7628651
theorem B3390511 : Blo 2007435 3390511 := bstep (se 1 (by rfl) ⟨2542883, by rfl⟩ : syracuseStep 3390511 = 5085767) B5085767
theorem B4520681 : Blo 2007435 4520681 := bstep (se 2 (by rfl) ⟨1695255, by rfl⟩ : syracuseStep 4520681 = 3390511) B3390511
theorem B3013787 : Blo 2007435 3013787 := bstep (se 1 (by rfl) ⟨2260340, by rfl⟩ : syracuseStep 3013787 = 4520681) B4520681
theorem B2009191 : Blo 2007435 2009191 := bstep (se 1 (by rfl) ⟨1506893, by rfl⟩ : syracuseStep 2009191 = 3013787) B3013787
theorem B2260345 : Blo 2007435 2260345 := bbase (se 2 (by rfl) ⟨847629, by rfl⟩ : syracuseStep 2260345 = 1695259) (by norm_num)
theorem B3013793 : Blo 2007435 3013793 := bstep (se 2 (by rfl) ⟨1130172, by rfl⟩ : syracuseStep 3013793 = 2260345) B2260345
theorem B2009195 : Blo 2007435 2009195 := bstep (se 1 (by rfl) ⟨1506896, by rfl⟩ : syracuseStep 2009195 = 3013793) B3013793
theorem B13049045 : Blo 2007435 13049045 := bbase (se 7 (by rfl) ⟨152918, by rfl⟩ : syracuseStep 13049045 = 305837) (by norm_num)
theorem B8699363 : Blo 2007435 8699363 := bstep (se 1 (by rfl) ⟨6524522, by rfl⟩ : syracuseStep 8699363 = 13049045) B13049045
theorem B5799575 : Blo 2007435 5799575 := bstep (se 1 (by rfl) ⟨4349681, by rfl⟩ : syracuseStep 5799575 = 8699363) B8699363
theorem B3866383 : Blo 2007435 3866383 := bstep (se 1 (by rfl) ⟨2899787, by rfl⟩ : syracuseStep 3866383 = 5799575) B5799575
theorem B5155177 : Blo 2007435 5155177 := bstep (se 2 (by rfl) ⟨1933191, by rfl⟩ : syracuseStep 5155177 = 3866383) B3866383
theorem B6873569 : Blo 2007435 6873569 := bstep (se 2 (by rfl) ⟨2577588, by rfl⟩ : syracuseStep 6873569 = 5155177) B5155177
theorem B4582379 : Blo 2007435 4582379 := bstep (se 1 (by rfl) ⟨3436784, by rfl⟩ : syracuseStep 4582379 = 6873569) B6873569
theorem B3054919 : Blo 2007435 3054919 := bstep (se 1 (by rfl) ⟨2291189, by rfl⟩ : syracuseStep 3054919 = 4582379) B4582379
theorem B4073225 : Blo 2007435 4073225 := bstep (se 2 (by rfl) ⟨1527459, by rfl⟩ : syracuseStep 4073225 = 3054919) B3054919
theorem B10861933 : Blo 2007435 10861933 := bstep (se 3 (by rfl) ⟨2036612, by rfl⟩ : syracuseStep 10861933 = 4073225) B4073225
theorem B14482577 : Blo 2007435 14482577 := bstep (se 2 (by rfl) ⟨5430966, by rfl⟩ : syracuseStep 14482577 = 10861933) B10861933
theorem B9655051 : Blo 2007435 9655051 := bstep (se 1 (by rfl) ⟨7241288, by rfl⟩ : syracuseStep 9655051 = 14482577) B14482577
theorem B12873401 : Blo 2007435 12873401 := bstep (se 2 (by rfl) ⟨4827525, by rfl⟩ : syracuseStep 12873401 = 9655051) B9655051
theorem B8582267 : Blo 2007435 8582267 := bstep (se 1 (by rfl) ⟨6436700, by rfl⟩ : syracuseStep 8582267 = 12873401) B12873401
theorem B5721511 : Blo 2007435 5721511 := bstep (se 1 (by rfl) ⟨4291133, by rfl⟩ : syracuseStep 5721511 = 8582267) B8582267
theorem B7628681 : Blo 2007435 7628681 := bstep (se 2 (by rfl) ⟨2860755, by rfl⟩ : syracuseStep 7628681 = 5721511) B5721511
theorem B5085787 : Blo 2007435 5085787 := bstep (se 1 (by rfl) ⟨3814340, by rfl⟩ : syracuseStep 5085787 = 7628681) B7628681
theorem B6781049 : Blo 2007435 6781049 := bstep (se 2 (by rfl) ⟨2542893, by rfl⟩ : syracuseStep 6781049 = 5085787) B5085787
theorem B4520699 : Blo 2007435 4520699 := bstep (se 1 (by rfl) ⟨3390524, by rfl⟩ : syracuseStep 4520699 = 6781049) B6781049
theorem B3013799 : Blo 2007435 3013799 := bstep (se 1 (by rfl) ⟨2260349, by rfl⟩ : syracuseStep 3013799 = 4520699) B4520699
theorem B2009199 : Blo 2007435 2009199 := bstep (se 1 (by rfl) ⟨1506899, by rfl⟩ : syracuseStep 2009199 = 3013799) B3013799
theorem B3013805 : Blo 2007435 3013805 := bbase (se 3 (by rfl) ⟨565088, by rfl⟩ : syracuseStep 3013805 = 1130177) (by norm_num)
theorem B2009203 : Blo 2007435 2009203 := bstep (se 1 (by rfl) ⟨1506902, by rfl⟩ : syracuseStep 2009203 = 3013805) B3013805
theorem B4520717 : Blo 2007435 4520717 := bbase (se 3 (by rfl) ⟨847634, by rfl⟩ : syracuseStep 4520717 = 1695269) (by norm_num)
theorem B3013811 : Blo 2007435 3013811 := bstep (se 1 (by rfl) ⟨2260358, by rfl⟩ : syracuseStep 3013811 = 4520717) B4520717
theorem B2009207 : Blo 2007435 2009207 := bstep (se 1 (by rfl) ⟨1506905, by rfl⟩ : syracuseStep 2009207 = 3013811) B3013811
theorem B2542909 : Blo 2007435 2542909 := bbase (se 3 (by rfl) ⟨476795, by rfl⟩ : syracuseStep 2542909 = 953591) (by norm_num)
theorem B3390545 : Blo 2007435 3390545 := bstep (se 2 (by rfl) ⟨1271454, by rfl⟩ : syracuseStep 3390545 = 2542909) B2542909
theorem B2260363 : Blo 2007435 2260363 := bstep (se 1 (by rfl) ⟨1695272, by rfl⟩ : syracuseStep 2260363 = 3390545) B3390545
theorem B3013817 : Blo 2007435 3013817 := bstep (se 2 (by rfl) ⟨1130181, by rfl⟩ : syracuseStep 3013817 = 2260363) B2260363
theorem B2009211 : Blo 2007435 2009211 := bstep (se 1 (by rfl) ⟨1506908, by rfl⟩ : syracuseStep 2009211 = 3013817) B3013817
theorem B15465653 : Blo 2007435 15465653 := bbase (se 5 (by rfl) ⟨724952, by rfl⟩ : syracuseStep 15465653 = 1449905) (by norm_num)
theorem B10310435 : Blo 2007435 10310435 := bstep (se 1 (by rfl) ⟨7732826, by rfl⟩ : syracuseStep 10310435 = 15465653) B15465653
theorem B6873623 : Blo 2007435 6873623 := bstep (se 1 (by rfl) ⟨5155217, by rfl⟩ : syracuseStep 6873623 = 10310435) B10310435
theorem B4582415 : Blo 2007435 4582415 := bstep (se 1 (by rfl) ⟨3436811, by rfl⟩ : syracuseStep 4582415 = 6873623) B6873623
theorem B3054943 : Blo 2007435 3054943 := bstep (se 1 (by rfl) ⟨2291207, by rfl⟩ : syracuseStep 3054943 = 4582415) B4582415
theorem B4073257 : Blo 2007435 4073257 := bstep (se 2 (by rfl) ⟨1527471, by rfl⟩ : syracuseStep 4073257 = 3054943) B3054943
theorem B21724037 : Blo 2007435 21724037 := bstep (se 4 (by rfl) ⟨2036628, by rfl⟩ : syracuseStep 21724037 = 4073257) B4073257
theorem B14482691 : Blo 2007435 14482691 := bstep (se 1 (by rfl) ⟨10862018, by rfl⟩ : syracuseStep 14482691 = 21724037) B21724037
theorem B9655127 : Blo 2007435 9655127 := bstep (se 1 (by rfl) ⟨7241345, by rfl⟩ : syracuseStep 9655127 = 14482691) B14482691
theorem B6436751 : Blo 2007435 6436751 := bstep (se 1 (by rfl) ⟨4827563, by rfl⟩ : syracuseStep 6436751 = 9655127) B9655127
theorem B17164669 : Blo 2007435 17164669 := bstep (se 3 (by rfl) ⟨3218375, by rfl⟩ : syracuseStep 17164669 = 6436751) B6436751
theorem B22886225 : Blo 2007435 22886225 := bstep (se 2 (by rfl) ⟨8582334, by rfl⟩ : syracuseStep 22886225 = 17164669) B17164669
theorem B15257483 : Blo 2007435 15257483 := bstep (se 1 (by rfl) ⟨11443112, by rfl⟩ : syracuseStep 15257483 = 22886225) B22886225
theorem B10171655 : Blo 2007435 10171655 := bstep (se 1 (by rfl) ⟨7628741, by rfl⟩ : syracuseStep 10171655 = 15257483) B15257483
theorem B6781103 : Blo 2007435 6781103 := bstep (se 1 (by rfl) ⟨5085827, by rfl⟩ : syracuseStep 6781103 = 10171655) B10171655
theorem B4520735 : Blo 2007435 4520735 := bstep (se 1 (by rfl) ⟨3390551, by rfl⟩ : syracuseStep 4520735 = 6781103) B6781103
theorem B3013823 : Blo 2007435 3013823 := bstep (se 1 (by rfl) ⟨2260367, by rfl⟩ : syracuseStep 3013823 = 4520735) B4520735
theorem B2009215 : Blo 2007435 2009215 := bstep (se 1 (by rfl) ⟨1506911, by rfl⟩ : syracuseStep 2009215 = 3013823) B3013823
theorem B3013829 : Blo 2007435 3013829 := bbase (se 4 (by rfl) ⟨282546, by rfl⟩ : syracuseStep 3013829 = 565093) (by norm_num)
theorem B2009219 : Blo 2007435 2009219 := bstep (se 1 (by rfl) ⟨1506914, by rfl⟩ : syracuseStep 2009219 = 3013829) B3013829
theorem B3390565 : Blo 2007435 3390565 := bbase (se 4 (by rfl) ⟨317865, by rfl⟩ : syracuseStep 3390565 = 635731) (by norm_num)
theorem B4520753 : Blo 2007435 4520753 := bstep (se 2 (by rfl) ⟨1695282, by rfl⟩ : syracuseStep 4520753 = 3390565) B3390565
theorem B3013835 : Blo 2007435 3013835 := bstep (se 1 (by rfl) ⟨2260376, by rfl⟩ : syracuseStep 3013835 = 4520753) B4520753
theorem B2009223 : Blo 2007435 2009223 := bstep (se 1 (by rfl) ⟨1506917, by rfl⟩ : syracuseStep 2009223 = 3013835) B3013835
theorem B2260381 : Blo 2007435 2260381 := bbase (se 3 (by rfl) ⟨423821, by rfl⟩ : syracuseStep 2260381 = 847643) (by norm_num)
theorem B3013841 : Blo 2007435 3013841 := bstep (se 2 (by rfl) ⟨1130190, by rfl⟩ : syracuseStep 3013841 = 2260381) B2260381
theorem B2009227 : Blo 2007435 2009227 := bstep (se 1 (by rfl) ⟨1506920, by rfl⟩ : syracuseStep 2009227 = 3013841) B3013841
theorem B6781157 : Blo 2007435 6781157 := bbase (se 4 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 6781157 = 1271467) (by norm_num)
theorem B4520771 : Blo 2007435 4520771 := bstep (se 1 (by rfl) ⟨3390578, by rfl⟩ : syracuseStep 4520771 = 6781157) B6781157
theorem B3013847 : Blo 2007435 3013847 := bstep (se 1 (by rfl) ⟨2260385, by rfl⟩ : syracuseStep 3013847 = 4520771) B4520771
theorem B2009231 : Blo 2007435 2009231 := bstep (se 1 (by rfl) ⟨1506923, by rfl⟩ : syracuseStep 2009231 = 3013847) B3013847
theorem B3013853 : Blo 2007435 3013853 := bbase (se 3 (by rfl) ⟨565097, by rfl⟩ : syracuseStep 3013853 = 1130195) (by norm_num)
theorem B2009235 : Blo 2007435 2009235 := bstep (se 1 (by rfl) ⟨1506926, by rfl⟩ : syracuseStep 2009235 = 3013853) B3013853
theorem B4520789 : Blo 2007435 4520789 := bbase (se 9 (by rfl) ⟨13244, by rfl⟩ : syracuseStep 4520789 = 26489) (by norm_num)
theorem B3013859 : Blo 2007435 3013859 := bstep (se 1 (by rfl) ⟨2260394, by rfl⟩ : syracuseStep 3013859 = 4520789) B4520789
theorem B2009239 : Blo 2007435 2009239 := bstep (se 1 (by rfl) ⟨1506929, by rfl⟩ : syracuseStep 2009239 = 3013859) B3013859
theorem B5721637 : Blo 2007435 5721637 := bbase (se 4 (by rfl) ⟨536403, by rfl⟩ : syracuseStep 5721637 = 1072807) (by norm_num)
theorem B7628849 : Blo 2007435 7628849 := bstep (se 2 (by rfl) ⟨2860818, by rfl⟩ : syracuseStep 7628849 = 5721637) B5721637
theorem B5085899 : Blo 2007435 5085899 := bstep (se 1 (by rfl) ⟨3814424, by rfl⟩ : syracuseStep 5085899 = 7628849) B7628849
theorem B3390599 : Blo 2007435 3390599 := bstep (se 1 (by rfl) ⟨2542949, by rfl⟩ : syracuseStep 3390599 = 5085899) B5085899
theorem B2260399 : Blo 2007435 2260399 := bstep (se 1 (by rfl) ⟨1695299, by rfl⟩ : syracuseStep 2260399 = 3390599) B3390599
theorem B3013865 : Blo 2007435 3013865 := bstep (se 2 (by rfl) ⟨1130199, by rfl⟩ : syracuseStep 3013865 = 2260399) B2260399
theorem B2009243 : Blo 2007435 2009243 := bstep (se 1 (by rfl) ⟨1506932, by rfl⟩ : syracuseStep 2009243 = 3013865) B3013865
theorem B9787013 : Blo 2007435 9787013 := bbase (se 4 (by rfl) ⟨917532, by rfl⟩ : syracuseStep 9787013 = 1835065) (by norm_num)
theorem B6524675 : Blo 2007435 6524675 := bstep (se 1 (by rfl) ⟨4893506, by rfl⟩ : syracuseStep 6524675 = 9787013) B9787013
theorem B4349783 : Blo 2007435 4349783 := bstep (se 1 (by rfl) ⟨3262337, by rfl⟩ : syracuseStep 4349783 = 6524675) B6524675
theorem B11599421 : Blo 2007435 11599421 := bstep (se 3 (by rfl) ⟨2174891, by rfl⟩ : syracuseStep 11599421 = 4349783) B4349783
theorem B30931789 : Blo 2007435 30931789 := bstep (se 3 (by rfl) ⟨5799710, by rfl⟩ : syracuseStep 30931789 = 11599421) B11599421
theorem B41242385 : Blo 2007435 41242385 := bstep (se 2 (by rfl) ⟨15465894, by rfl⟩ : syracuseStep 41242385 = 30931789) B30931789
theorem B27494923 : Blo 2007435 27494923 := bstep (se 1 (by rfl) ⟨20621192, by rfl⟩ : syracuseStep 27494923 = 41242385) B41242385
theorem B36659897 : Blo 2007435 36659897 := bstep (se 2 (by rfl) ⟨13747461, by rfl⟩ : syracuseStep 36659897 = 27494923) B27494923
theorem B24439931 : Blo 2007435 24439931 := bstep (se 1 (by rfl) ⟨18329948, by rfl⟩ : syracuseStep 24439931 = 36659897) B36659897
theorem B16293287 : Blo 2007435 16293287 := bstep (se 1 (by rfl) ⟨12219965, by rfl⟩ : syracuseStep 16293287 = 24439931) B24439931
theorem B10862191 : Blo 2007435 10862191 := bstep (se 1 (by rfl) ⟨8146643, by rfl⟩ : syracuseStep 10862191 = 16293287) B16293287
theorem B57931685 : Blo 2007435 57931685 := bstep (se 4 (by rfl) ⟨5431095, by rfl⟩ : syracuseStep 57931685 = 10862191) B10862191
theorem B38621123 : Blo 2007435 38621123 := bstep (se 1 (by rfl) ⟨28965842, by rfl⟩ : syracuseStep 38621123 = 57931685) B57931685
theorem B25747415 : Blo 2007435 25747415 := bstep (se 1 (by rfl) ⟨19310561, by rfl⟩ : syracuseStep 25747415 = 38621123) B38621123
theorem B17164943 : Blo 2007435 17164943 := bstep (se 1 (by rfl) ⟨12873707, by rfl⟩ : syracuseStep 17164943 = 25747415) B25747415
theorem B11443295 : Blo 2007435 11443295 := bstep (se 1 (by rfl) ⟨8582471, by rfl⟩ : syracuseStep 11443295 = 17164943) B17164943
theorem B7628863 : Blo 2007435 7628863 := bstep (se 1 (by rfl) ⟨5721647, by rfl⟩ : syracuseStep 7628863 = 11443295) B11443295
theorem B10171817 : Blo 2007435 10171817 := bstep (se 2 (by rfl) ⟨3814431, by rfl⟩ : syracuseStep 10171817 = 7628863) B7628863
theorem B6781211 : Blo 2007435 6781211 := bstep (se 1 (by rfl) ⟨5085908, by rfl⟩ : syracuseStep 6781211 = 10171817) B10171817
theorem B4520807 : Blo 2007435 4520807 := bstep (se 1 (by rfl) ⟨3390605, by rfl⟩ : syracuseStep 4520807 = 6781211) B6781211
theorem B3013871 : Blo 2007435 3013871 := bstep (se 1 (by rfl) ⟨2260403, by rfl⟩ : syracuseStep 3013871 = 4520807) B4520807
theorem B2009247 : Blo 2007435 2009247 := bstep (se 1 (by rfl) ⟨1506935, by rfl⟩ : syracuseStep 2009247 = 3013871) B3013871
theorem B3013877 : Blo 2007435 3013877 := bbase (se 5 (by rfl) ⟨141275, by rfl⟩ : syracuseStep 3013877 = 282551) (by norm_num)
theorem B2009251 : Blo 2007435 2009251 := bstep (se 1 (by rfl) ⟨1506938, by rfl⟩ : syracuseStep 2009251 = 3013877) B3013877
theorem B5505221 : Blo 2007435 5505221 := bbase (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) (by norm_num)
theorem B3670147 : Blo 2007435 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B4893529 : Blo 2007435 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B6524705 : Blo 2007435 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B4349803 : Blo 2007435 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B5799737 : Blo 2007435 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B3866491 : Blo 2007435 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B5155321 : Blo 2007435 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B6873761 : Blo 2007435 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B4582507 : Blo 2007435 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B6110009 : Blo 2007435 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B4073339 : Blo 2007435 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B10862237 : Blo 2007435 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B7241491 : Blo 2007435 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B9655321 : Blo 2007435 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B12873761 : Blo 2007435 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B8582507 : Blo 2007435 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B5721671 : Blo 2007435 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B3814447 : Blo 2007435 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B5085929 : Blo 2007435 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B3390619 : Blo 2007435 3390619 := bstep (se 1 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 3390619 = 5085929) B5085929
theorem B4520825 : Blo 2007435 4520825 := bstep (se 2 (by rfl) ⟨1695309, by rfl⟩ : syracuseStep 4520825 = 3390619) B3390619
theorem B3013883 : Blo 2007435 3013883 := bstep (se 1 (by rfl) ⟨2260412, by rfl⟩ : syracuseStep 3013883 = 4520825) B4520825
theorem B2009255 : Blo 2007435 2009255 := bstep (se 1 (by rfl) ⟨1506941, by rfl⟩ : syracuseStep 2009255 = 3013883) B3013883
theorem B2260417 : Blo 2007435 2260417 := bbase (se 2 (by rfl) ⟨847656, by rfl⟩ : syracuseStep 2260417 = 1695313) (by norm_num)
theorem B3013889 : Blo 2007435 3013889 := bstep (se 2 (by rfl) ⟨1130208, by rfl⟩ : syracuseStep 3013889 = 2260417) B2260417
theorem B2009259 : Blo 2007435 2009259 := bstep (se 1 (by rfl) ⟨1506944, by rfl⟩ : syracuseStep 2009259 = 3013889) B3013889
theorem B5085949 : Blo 2007435 5085949 := bbase (se 3 (by rfl) ⟨953615, by rfl⟩ : syracuseStep 5085949 = 1907231) (by norm_num)
theorem B6781265 : Blo 2007435 6781265 := bstep (se 2 (by rfl) ⟨2542974, by rfl⟩ : syracuseStep 6781265 = 5085949) B5085949
theorem B4520843 : Blo 2007435 4520843 := bstep (se 1 (by rfl) ⟨3390632, by rfl⟩ : syracuseStep 4520843 = 6781265) B6781265
theorem B3013895 : Blo 2007435 3013895 := bstep (se 1 (by rfl) ⟨2260421, by rfl⟩ : syracuseStep 3013895 = 4520843) B4520843
theorem B2009263 : Blo 2007435 2009263 := bstep (se 1 (by rfl) ⟨1506947, by rfl⟩ : syracuseStep 2009263 = 3013895) B3013895
theorem B3013901 : Blo 2007435 3013901 := bbase (se 3 (by rfl) ⟨565106, by rfl⟩ : syracuseStep 3013901 = 1130213) (by norm_num)
theorem B2009267 : Blo 2007435 2009267 := bstep (se 1 (by rfl) ⟨1506950, by rfl⟩ : syracuseStep 2009267 = 3013901) B3013901
theorem B4520861 : Blo 2007435 4520861 := bbase (se 3 (by rfl) ⟨847661, by rfl⟩ : syracuseStep 4520861 = 1695323) (by norm_num)
theorem B3013907 : Blo 2007435 3013907 := bstep (se 1 (by rfl) ⟨2260430, by rfl⟩ : syracuseStep 3013907 = 4520861) B4520861
theorem B2009271 : Blo 2007435 2009271 := bstep (se 1 (by rfl) ⟨1506953, by rfl⟩ : syracuseStep 2009271 = 3013907) B3013907
theorem B3390653 : Blo 2007435 3390653 := bbase (se 3 (by rfl) ⟨635747, by rfl⟩ : syracuseStep 3390653 = 1271495) (by norm_num)
theorem B2260435 : Blo 2007435 2260435 := bstep (se 1 (by rfl) ⟨1695326, by rfl⟩ : syracuseStep 2260435 = 3390653) B3390653
theorem B3013913 : Blo 2007435 3013913 := bstep (se 2 (by rfl) ⟨1130217, by rfl⟩ : syracuseStep 3013913 = 2260435) B2260435
theorem B2009275 : Blo 2007435 2009275 := bstep (se 1 (by rfl) ⟨1506956, by rfl⟩ : syracuseStep 2009275 = 3013913) B3013913
theorem B11443477 : Blo 2007435 11443477 := bbase (se 6 (by rfl) ⟨268206, by rfl⟩ : syracuseStep 11443477 = 536413) (by norm_num)
theorem B15257969 : Blo 2007435 15257969 := bstep (se 2 (by rfl) ⟨5721738, by rfl⟩ : syracuseStep 15257969 = 11443477) B11443477
theorem B10171979 : Blo 2007435 10171979 := bstep (se 1 (by rfl) ⟨7628984, by rfl⟩ : syracuseStep 10171979 = 15257969) B15257969
theorem B6781319 : Blo 2007435 6781319 := bstep (se 1 (by rfl) ⟨5085989, by rfl⟩ : syracuseStep 6781319 = 10171979) B10171979
theorem B4520879 : Blo 2007435 4520879 := bstep (se 1 (by rfl) ⟨3390659, by rfl⟩ : syracuseStep 4520879 = 6781319) B6781319
theorem B3013919 : Blo 2007435 3013919 := bstep (se 1 (by rfl) ⟨2260439, by rfl⟩ : syracuseStep 3013919 = 4520879) B4520879
theorem B2009279 : Blo 2007435 2009279 := bstep (se 1 (by rfl) ⟨1506959, by rfl⟩ : syracuseStep 2009279 = 3013919) B3013919
theorem B3013925 : Blo 2007435 3013925 := bbase (se 4 (by rfl) ⟨282555, by rfl⟩ : syracuseStep 3013925 = 565111) (by norm_num)
theorem B2009283 : Blo 2007435 2009283 := bstep (se 1 (by rfl) ⟨1506962, by rfl⟩ : syracuseStep 2009283 = 3013925) B3013925
theorem B2543005 : Blo 2007435 2543005 := bbase (se 3 (by rfl) ⟨476813, by rfl⟩ : syracuseStep 2543005 = 953627) (by norm_num)
theorem B3390673 : Blo 2007435 3390673 := bstep (se 2 (by rfl) ⟨1271502, by rfl⟩ : syracuseStep 3390673 = 2543005) B2543005
theorem B4520897 : Blo 2007435 4520897 := bstep (se 2 (by rfl) ⟨1695336, by rfl⟩ : syracuseStep 4520897 = 3390673) B3390673
theorem B3013931 : Blo 2007435 3013931 := bstep (se 1 (by rfl) ⟨2260448, by rfl⟩ : syracuseStep 3013931 = 4520897) B4520897
theorem B2009287 : Blo 2007435 2009287 := bstep (se 1 (by rfl) ⟨1506965, by rfl⟩ : syracuseStep 2009287 = 3013931) B3013931
theorem B2260453 : Blo 2007435 2260453 := bbase (se 4 (by rfl) ⟨211917, by rfl⟩ : syracuseStep 2260453 = 423835) (by norm_num)
theorem B3013937 : Blo 2007435 3013937 := bstep (se 2 (by rfl) ⟨1130226, by rfl⟩ : syracuseStep 3013937 = 2260453) B2260453
theorem B2009291 : Blo 2007435 2009291 := bstep (se 1 (by rfl) ⟨1506968, by rfl⟩ : syracuseStep 2009291 = 3013937) B3013937
theorem B4827757 : Blo 2007435 4827757 := bbase (se 3 (by rfl) ⟨905204, by rfl⟩ : syracuseStep 4827757 = 1810409) (by norm_num)
theorem B6437009 : Blo 2007435 6437009 := bstep (se 2 (by rfl) ⟨2413878, by rfl⟩ : syracuseStep 6437009 = 4827757) B4827757
theorem B4291339 : Blo 2007435 4291339 := bstep (se 1 (by rfl) ⟨3218504, by rfl⟩ : syracuseStep 4291339 = 6437009) B6437009
theorem B5721785 : Blo 2007435 5721785 := bstep (se 2 (by rfl) ⟨2145669, by rfl⟩ : syracuseStep 5721785 = 4291339) B4291339
theorem B3814523 : Blo 2007435 3814523 := bstep (se 1 (by rfl) ⟨2860892, by rfl⟩ : syracuseStep 3814523 = 5721785) B5721785
theorem B2543015 : Blo 2007435 2543015 := bstep (se 1 (by rfl) ⟨1907261, by rfl⟩ : syracuseStep 2543015 = 3814523) B3814523
theorem B6781373 : Blo 2007435 6781373 := bstep (se 3 (by rfl) ⟨1271507, by rfl⟩ : syracuseStep 6781373 = 2543015) B2543015
theorem B4520915 : Blo 2007435 4520915 := bstep (se 1 (by rfl) ⟨3390686, by rfl⟩ : syracuseStep 4520915 = 6781373) B6781373
theorem B3013943 : Blo 2007435 3013943 := bstep (se 1 (by rfl) ⟨2260457, by rfl⟩ : syracuseStep 3013943 = 4520915) B4520915
theorem B2009295 : Blo 2007435 2009295 := bstep (se 1 (by rfl) ⟨1506971, by rfl⟩ : syracuseStep 2009295 = 3013943) B3013943
theorem B3013949 : Blo 2007435 3013949 := bbase (se 3 (by rfl) ⟨565115, by rfl⟩ : syracuseStep 3013949 = 1130231) (by norm_num)
theorem B2009299 : Blo 2007435 2009299 := bstep (se 1 (by rfl) ⟨1506974, by rfl⟩ : syracuseStep 2009299 = 3013949) B3013949
theorem B4520933 : Blo 2007435 4520933 := bbase (se 4 (by rfl) ⟨423837, by rfl⟩ : syracuseStep 4520933 = 847675) (by norm_num)
theorem B3013955 : Blo 2007435 3013955 := bstep (se 1 (by rfl) ⟨2260466, by rfl⟩ : syracuseStep 3013955 = 4520933) B4520933
theorem B2009303 : Blo 2007435 2009303 := bstep (se 1 (by rfl) ⟨1506977, by rfl⟩ : syracuseStep 2009303 = 3013955) B3013955
theorem B5086061 : Blo 2007435 5086061 := bbase (se 3 (by rfl) ⟨953636, by rfl⟩ : syracuseStep 5086061 = 1907273) (by norm_num)
theorem B3390707 : Blo 2007435 3390707 := bstep (se 1 (by rfl) ⟨2543030, by rfl⟩ : syracuseStep 3390707 = 5086061) B5086061
theorem B2260471 : Blo 2007435 2260471 := bstep (se 1 (by rfl) ⟨1695353, by rfl⟩ : syracuseStep 2260471 = 3390707) B3390707
theorem B3013961 : Blo 2007435 3013961 := bstep (se 2 (by rfl) ⟨1130235, by rfl⟩ : syracuseStep 3013961 = 2260471) B2260471
theorem B2009307 : Blo 2007435 2009307 := bstep (se 1 (by rfl) ⟨1506980, by rfl⟩ : syracuseStep 2009307 = 3013961) B3013961
theorem B4291373 : Blo 2007435 4291373 := bbase (se 3 (by rfl) ⟨804632, by rfl⟩ : syracuseStep 4291373 = 1609265) (by norm_num)
theorem B2860915 : Blo 2007435 2860915 := bstep (se 1 (by rfl) ⟨2145686, by rfl⟩ : syracuseStep 2860915 = 4291373) B4291373
theorem B3814553 : Blo 2007435 3814553 := bstep (se 2 (by rfl) ⟨1430457, by rfl⟩ : syracuseStep 3814553 = 2860915) B2860915
theorem B10172141 : Blo 2007435 10172141 := bstep (se 3 (by rfl) ⟨1907276, by rfl⟩ : syracuseStep 10172141 = 3814553) B3814553
theorem B6781427 : Blo 2007435 6781427 := bstep (se 1 (by rfl) ⟨5086070, by rfl⟩ : syracuseStep 6781427 = 10172141) B10172141
theorem B4520951 : Blo 2007435 4520951 := bstep (se 1 (by rfl) ⟨3390713, by rfl⟩ : syracuseStep 4520951 = 6781427) B6781427
theorem B3013967 : Blo 2007435 3013967 := bstep (se 1 (by rfl) ⟨2260475, by rfl⟩ : syracuseStep 3013967 = 4520951) B4520951
theorem B2009311 : Blo 2007435 2009311 := bstep (se 1 (by rfl) ⟨1506983, by rfl⟩ : syracuseStep 2009311 = 3013967) B3013967
theorem B3013973 : Blo 2007435 3013973 := bbase (se 11 (by rfl) ⟨2207, by rfl⟩ : syracuseStep 3013973 = 4415) (by norm_num)
theorem B2009315 : Blo 2007435 2009315 := bstep (se 1 (by rfl) ⟨1506986, by rfl⟩ : syracuseStep 2009315 = 3013973) B3013973
theorem B17399765 : Blo 2007435 17399765 := bbase (se 7 (by rfl) ⟨203903, by rfl⟩ : syracuseStep 17399765 = 407807) (by norm_num)
theorem B11599843 : Blo 2007435 11599843 := bstep (se 1 (by rfl) ⟨8699882, by rfl⟩ : syracuseStep 11599843 = 17399765) B17399765
theorem B15466457 : Blo 2007435 15466457 := bstep (se 2 (by rfl) ⟨5799921, by rfl⟩ : syracuseStep 15466457 = 11599843) B11599843
theorem B10310971 : Blo 2007435 10310971 := bstep (se 1 (by rfl) ⟨7733228, by rfl⟩ : syracuseStep 10310971 = 15466457) B15466457
theorem B13747961 : Blo 2007435 13747961 := bstep (se 2 (by rfl) ⟨5155485, by rfl⟩ : syracuseStep 13747961 = 10310971) B10310971
theorem B9165307 : Blo 2007435 9165307 := bstep (se 1 (by rfl) ⟨6873980, by rfl⟩ : syracuseStep 9165307 = 13747961) B13747961
theorem B12220409 : Blo 2007435 12220409 := bstep (se 2 (by rfl) ⟨4582653, by rfl⟩ : syracuseStep 12220409 = 9165307) B9165307
theorem B8146939 : Blo 2007435 8146939 := bstep (se 1 (by rfl) ⟨6110204, by rfl⟩ : syracuseStep 8146939 = 12220409) B12220409
theorem B10862585 : Blo 2007435 10862585 := bstep (se 2 (by rfl) ⟨4073469, by rfl⟩ : syracuseStep 10862585 = 8146939) B8146939
theorem B7241723 : Blo 2007435 7241723 := bstep (se 1 (by rfl) ⟨5431292, by rfl⟩ : syracuseStep 7241723 = 10862585) B10862585
theorem B4827815 : Blo 2007435 4827815 := bstep (se 1 (by rfl) ⟨3620861, by rfl⟩ : syracuseStep 4827815 = 7241723) B7241723
theorem B3218543 : Blo 2007435 3218543 := bstep (se 1 (by rfl) ⟨2413907, by rfl⟩ : syracuseStep 3218543 = 4827815) B4827815
theorem B2145695 : Blo 2007435 2145695 := bstep (se 1 (by rfl) ⟨1609271, by rfl⟩ : syracuseStep 2145695 = 3218543) B3218543
theorem B5721853 : Blo 2007435 5721853 := bstep (se 3 (by rfl) ⟨1072847, by rfl⟩ : syracuseStep 5721853 = 2145695) B2145695
theorem B7629137 : Blo 2007435 7629137 := bstep (se 2 (by rfl) ⟨2860926, by rfl⟩ : syracuseStep 7629137 = 5721853) B5721853
theorem B5086091 : Blo 2007435 5086091 := bstep (se 1 (by rfl) ⟨3814568, by rfl⟩ : syracuseStep 5086091 = 7629137) B7629137
theorem B3390727 : Blo 2007435 3390727 := bstep (se 1 (by rfl) ⟨2543045, by rfl⟩ : syracuseStep 3390727 = 5086091) B5086091
theorem B4520969 : Blo 2007435 4520969 := bstep (se 2 (by rfl) ⟨1695363, by rfl⟩ : syracuseStep 4520969 = 3390727) B3390727
theorem B3013979 : Blo 2007435 3013979 := bstep (se 1 (by rfl) ⟨2260484, by rfl⟩ : syracuseStep 3013979 = 4520969) B4520969
theorem B2009319 : Blo 2007435 2009319 := bstep (se 1 (by rfl) ⟨1506989, by rfl⟩ : syracuseStep 2009319 = 3013979) B3013979
theorem B2260489 : Blo 2007435 2260489 := bbase (se 2 (by rfl) ⟨847683, by rfl⟩ : syracuseStep 2260489 = 1695367) (by norm_num)
theorem B3013985 : Blo 2007435 3013985 := bstep (se 2 (by rfl) ⟨1130244, by rfl⟩ : syracuseStep 3013985 = 2260489) B2260489
theorem B2009323 : Blo 2007435 2009323 := bstep (se 1 (by rfl) ⟨1506992, by rfl⟩ : syracuseStep 2009323 = 3013985) B3013985
theorem B28966997 : Blo 2007435 28966997 := bbase (se 8 (by rfl) ⟨169728, by rfl⟩ : syracuseStep 28966997 = 339457) (by norm_num)
theorem B19311331 : Blo 2007435 19311331 := bstep (se 1 (by rfl) ⟨14483498, by rfl⟩ : syracuseStep 19311331 = 28966997) B28966997
theorem B25748441 : Blo 2007435 25748441 := bstep (se 2 (by rfl) ⟨9655665, by rfl⟩ : syracuseStep 25748441 = 19311331) B19311331
theorem B17165627 : Blo 2007435 17165627 := bstep (se 1 (by rfl) ⟨12874220, by rfl⟩ : syracuseStep 17165627 = 25748441) B25748441
theorem B11443751 : Blo 2007435 11443751 := bstep (se 1 (by rfl) ⟨8582813, by rfl⟩ : syracuseStep 11443751 = 17165627) B17165627
theorem B7629167 : Blo 2007435 7629167 := bstep (se 1 (by rfl) ⟨5721875, by rfl⟩ : syracuseStep 7629167 = 11443751) B11443751
theorem B5086111 : Blo 2007435 5086111 := bstep (se 1 (by rfl) ⟨3814583, by rfl⟩ : syracuseStep 5086111 = 7629167) B7629167
theorem B6781481 : Blo 2007435 6781481 := bstep (se 2 (by rfl) ⟨2543055, by rfl⟩ : syracuseStep 6781481 = 5086111) B5086111
theorem B4520987 : Blo 2007435 4520987 := bstep (se 1 (by rfl) ⟨3390740, by rfl⟩ : syracuseStep 4520987 = 6781481) B6781481
theorem B3013991 : Blo 2007435 3013991 := bstep (se 1 (by rfl) ⟨2260493, by rfl⟩ : syracuseStep 3013991 = 4520987) B4520987
theorem B2009327 : Blo 2007435 2009327 := bstep (se 1 (by rfl) ⟨1506995, by rfl⟩ : syracuseStep 2009327 = 3013991) B3013991
theorem B3013997 : Blo 2007435 3013997 := bbase (se 3 (by rfl) ⟨565124, by rfl⟩ : syracuseStep 3013997 = 1130249) (by norm_num)
theorem B2009331 : Blo 2007435 2009331 := bstep (se 1 (by rfl) ⟨1506998, by rfl⟩ : syracuseStep 2009331 = 3013997) B3013997
theorem B4521005 : Blo 2007435 4521005 := bbase (se 3 (by rfl) ⟨847688, by rfl⟩ : syracuseStep 4521005 = 1695377) (by norm_num)
theorem B3014003 : Blo 2007435 3014003 := bstep (se 1 (by rfl) ⟨2260502, by rfl⟩ : syracuseStep 3014003 = 4521005) B4521005
theorem B2009335 : Blo 2007435 2009335 := bstep (se 1 (by rfl) ⟨1507001, by rfl⟩ : syracuseStep 2009335 = 3014003) B3014003
theorem B3055133 : Blo 2007435 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B2036755 : Blo 2007435 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B10862693 : Blo 2007435 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B7241795 : Blo 2007435 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B4827863 : Blo 2007435 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B12874301 : Blo 2007435 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B8582867 : Blo 2007435 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B5721911 : Blo 2007435 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B3814607 : Blo 2007435 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B2543071 : Blo 2007435 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B3390761 : Blo 2007435 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B2260507 : Blo 2007435 2260507 := bstep (se 1 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 2260507 = 3390761) B3390761
theorem B3014009 : Blo 2007435 3014009 := bstep (se 2 (by rfl) ⟨1130253, by rfl⟩ : syracuseStep 3014009 = 2260507) B2260507
theorem B2009339 : Blo 2007435 2009339 := bstep (se 1 (by rfl) ⟨1507004, by rfl⟩ : syracuseStep 2009339 = 3014009) B3014009
theorem B9165413 : Blo 2007435 9165413 := bbase (se 4 (by rfl) ⟨859257, by rfl⟩ : syracuseStep 9165413 = 1718515) (by norm_num)
theorem B24441101 : Blo 2007435 24441101 := bstep (se 3 (by rfl) ⟨4582706, by rfl⟩ : syracuseStep 24441101 = 9165413) B9165413
theorem B16294067 : Blo 2007435 16294067 := bstep (se 1 (by rfl) ⟨12220550, by rfl⟩ : syracuseStep 16294067 = 24441101) B24441101
theorem B10862711 : Blo 2007435 10862711 := bstep (se 1 (by rfl) ⟨8147033, by rfl⟩ : syracuseStep 10862711 = 16294067) B16294067
theorem B7241807 : Blo 2007435 7241807 := bstep (se 1 (by rfl) ⟨5431355, by rfl⟩ : syracuseStep 7241807 = 10862711) B10862711
theorem B4827871 : Blo 2007435 4827871 := bstep (se 1 (by rfl) ⟨3620903, by rfl⟩ : syracuseStep 4827871 = 7241807) B7241807
theorem B6437161 : Blo 2007435 6437161 := bstep (se 2 (by rfl) ⟨2413935, by rfl⟩ : syracuseStep 6437161 = 4827871) B4827871
theorem B34331525 : Blo 2007435 34331525 := bstep (se 4 (by rfl) ⟨3218580, by rfl⟩ : syracuseStep 34331525 = 6437161) B6437161
theorem B22887683 : Blo 2007435 22887683 := bstep (se 1 (by rfl) ⟨17165762, by rfl⟩ : syracuseStep 22887683 = 34331525) B34331525
theorem B15258455 : Blo 2007435 15258455 := bstep (se 1 (by rfl) ⟨11443841, by rfl⟩ : syracuseStep 15258455 = 22887683) B22887683
theorem B10172303 : Blo 2007435 10172303 := bstep (se 1 (by rfl) ⟨7629227, by rfl⟩ : syracuseStep 10172303 = 15258455) B15258455
theorem B6781535 : Blo 2007435 6781535 := bstep (se 1 (by rfl) ⟨5086151, by rfl⟩ : syracuseStep 6781535 = 10172303) B10172303
theorem B4521023 : Blo 2007435 4521023 := bstep (se 1 (by rfl) ⟨3390767, by rfl⟩ : syracuseStep 4521023 = 6781535) B6781535
theorem B3014015 : Blo 2007435 3014015 := bstep (se 1 (by rfl) ⟨2260511, by rfl⟩ : syracuseStep 3014015 = 4521023) B4521023
theorem B2009343 : Blo 2007435 2009343 := bstep (se 1 (by rfl) ⟨1507007, by rfl⟩ : syracuseStep 2009343 = 3014015) B3014015
theorem B3014021 : Blo 2007435 3014021 := bbase (se 4 (by rfl) ⟨282564, by rfl⟩ : syracuseStep 3014021 = 565129) (by norm_num)
theorem B2009347 : Blo 2007435 2009347 := bstep (se 1 (by rfl) ⟨1507010, by rfl⟩ : syracuseStep 2009347 = 3014021) B3014021
theorem B3390781 : Blo 2007435 3390781 := bbase (se 3 (by rfl) ⟨635771, by rfl⟩ : syracuseStep 3390781 = 1271543) (by norm_num)
theorem B4521041 : Blo 2007435 4521041 := bstep (se 2 (by rfl) ⟨1695390, by rfl⟩ : syracuseStep 4521041 = 3390781) B3390781
theorem B3014027 : Blo 2007435 3014027 := bstep (se 1 (by rfl) ⟨2260520, by rfl⟩ : syracuseStep 3014027 = 4521041) B4521041
theorem B2009351 : Blo 2007435 2009351 := bstep (se 1 (by rfl) ⟨1507013, by rfl⟩ : syracuseStep 2009351 = 3014027) B3014027
theorem B2260525 : Blo 2007435 2260525 := bbase (se 3 (by rfl) ⟨423848, by rfl⟩ : syracuseStep 2260525 = 847697) (by norm_num)
theorem B3014033 : Blo 2007435 3014033 := bstep (se 2 (by rfl) ⟨1130262, by rfl⟩ : syracuseStep 3014033 = 2260525) B2260525
theorem B2009355 : Blo 2007435 2009355 := bstep (se 1 (by rfl) ⟨1507016, by rfl⟩ : syracuseStep 2009355 = 3014033) B3014033
theorem B6781589 : Blo 2007435 6781589 := bbase (se 6 (by rfl) ⟨158943, by rfl⟩ : syracuseStep 6781589 = 317887) (by norm_num)
theorem B4521059 : Blo 2007435 4521059 := bstep (se 1 (by rfl) ⟨3390794, by rfl⟩ : syracuseStep 4521059 = 6781589) B6781589
theorem B3014039 : Blo 2007435 3014039 := bstep (se 1 (by rfl) ⟨2260529, by rfl⟩ : syracuseStep 3014039 = 4521059) B4521059
theorem B2009359 : Blo 2007435 2009359 := bstep (se 1 (by rfl) ⟨1507019, by rfl⟩ : syracuseStep 2009359 = 3014039) B3014039
theorem B3014045 : Blo 2007435 3014045 := bbase (se 3 (by rfl) ⟨565133, by rfl⟩ : syracuseStep 3014045 = 1130267) (by norm_num)
theorem B2009363 : Blo 2007435 2009363 := bstep (se 1 (by rfl) ⟨1507022, by rfl⟩ : syracuseStep 2009363 = 3014045) B3014045
theorem B4521077 : Blo 2007435 4521077 := bbase (se 5 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 4521077 = 423851) (by norm_num)
theorem B3014051 : Blo 2007435 3014051 := bstep (se 1 (by rfl) ⟨2260538, by rfl⟩ : syracuseStep 3014051 = 4521077) B4521077
theorem B2009367 : Blo 2007435 2009367 := bstep (se 1 (by rfl) ⟨1507025, by rfl⟩ : syracuseStep 2009367 = 3014051) B3014051
theorem B17166005 : Blo 2007435 17166005 := bbase (se 5 (by rfl) ⟨804656, by rfl⟩ : syracuseStep 17166005 = 1609313) (by norm_num)
theorem B11444003 : Blo 2007435 11444003 := bstep (se 1 (by rfl) ⟨8583002, by rfl⟩ : syracuseStep 11444003 = 17166005) B17166005
theorem B7629335 : Blo 2007435 7629335 := bstep (se 1 (by rfl) ⟨5722001, by rfl⟩ : syracuseStep 7629335 = 11444003) B11444003
theorem B5086223 : Blo 2007435 5086223 := bstep (se 1 (by rfl) ⟨3814667, by rfl⟩ : syracuseStep 5086223 = 7629335) B7629335
theorem B3390815 : Blo 2007435 3390815 := bstep (se 1 (by rfl) ⟨2543111, by rfl⟩ : syracuseStep 3390815 = 5086223) B5086223
theorem B2260543 : Blo 2007435 2260543 := bstep (se 1 (by rfl) ⟨1695407, by rfl⟩ : syracuseStep 2260543 = 3390815) B3390815
theorem B3014057 : Blo 2007435 3014057 := bstep (se 2 (by rfl) ⟨1130271, by rfl⟩ : syracuseStep 3014057 = 2260543) B2260543
theorem B2009371 : Blo 2007435 2009371 := bstep (se 1 (by rfl) ⟨1507028, by rfl⟩ : syracuseStep 2009371 = 3014057) B3014057
theorem B7629349 : Blo 2007435 7629349 := bbase (se 4 (by rfl) ⟨715251, by rfl⟩ : syracuseStep 7629349 = 1430503) (by norm_num)
theorem B10172465 : Blo 2007435 10172465 := bstep (se 2 (by rfl) ⟨3814674, by rfl⟩ : syracuseStep 10172465 = 7629349) B7629349
theorem B6781643 : Blo 2007435 6781643 := bstep (se 1 (by rfl) ⟨5086232, by rfl⟩ : syracuseStep 6781643 = 10172465) B10172465
theorem B4521095 : Blo 2007435 4521095 := bstep (se 1 (by rfl) ⟨3390821, by rfl⟩ : syracuseStep 4521095 = 6781643) B6781643
theorem B3014063 : Blo 2007435 3014063 := bstep (se 1 (by rfl) ⟨2260547, by rfl⟩ : syracuseStep 3014063 = 4521095) B4521095
theorem B2009375 : Blo 2007435 2009375 := bstep (se 1 (by rfl) ⟨1507031, by rfl⟩ : syracuseStep 2009375 = 3014063) B3014063
theorem B3014069 : Blo 2007435 3014069 := bbase (se 5 (by rfl) ⟨141284, by rfl⟩ : syracuseStep 3014069 = 282569) (by norm_num)
theorem B2009379 : Blo 2007435 2009379 := bstep (se 1 (by rfl) ⟨1507034, by rfl⟩ : syracuseStep 2009379 = 3014069) B3014069
theorem B5086253 : Blo 2007435 5086253 := bbase (se 3 (by rfl) ⟨953672, by rfl⟩ : syracuseStep 5086253 = 1907345) (by norm_num)
theorem B3390835 : Blo 2007435 3390835 := bstep (se 1 (by rfl) ⟨2543126, by rfl⟩ : syracuseStep 3390835 = 5086253) B5086253
theorem B4521113 : Blo 2007435 4521113 := bstep (se 2 (by rfl) ⟨1695417, by rfl⟩ : syracuseStep 4521113 = 3390835) B3390835
theorem B3014075 : Blo 2007435 3014075 := bstep (se 1 (by rfl) ⟨2260556, by rfl⟩ : syracuseStep 3014075 = 4521113) B4521113
theorem B2009383 : Blo 2007435 2009383 := bstep (se 1 (by rfl) ⟨1507037, by rfl⟩ : syracuseStep 2009383 = 3014075) B3014075
theorem B2260561 : Blo 2007435 2260561 := bbase (se 2 (by rfl) ⟨847710, by rfl⟩ : syracuseStep 2260561 = 1695421) (by norm_num)
theorem B3014081 : Blo 2007435 3014081 := bstep (se 2 (by rfl) ⟨1130280, by rfl⟩ : syracuseStep 3014081 = 2260561) B2260561
theorem B2009387 : Blo 2007435 2009387 := bstep (se 1 (by rfl) ⟨1507040, by rfl⟩ : syracuseStep 2009387 = 3014081) B3014081
theorem B2861029 : Blo 2007435 2861029 := bbase (se 4 (by rfl) ⟨268221, by rfl⟩ : syracuseStep 2861029 = 536443) (by norm_num)
theorem B3814705 : Blo 2007435 3814705 := bstep (se 2 (by rfl) ⟨1430514, by rfl⟩ : syracuseStep 3814705 = 2861029) B2861029
theorem B5086273 : Blo 2007435 5086273 := bstep (se 2 (by rfl) ⟨1907352, by rfl⟩ : syracuseStep 5086273 = 3814705) B3814705
theorem B6781697 : Blo 2007435 6781697 := bstep (se 2 (by rfl) ⟨2543136, by rfl⟩ : syracuseStep 6781697 = 5086273) B5086273
theorem B4521131 : Blo 2007435 4521131 := bstep (se 1 (by rfl) ⟨3390848, by rfl⟩ : syracuseStep 4521131 = 6781697) B6781697
theorem B3014087 : Blo 2007435 3014087 := bstep (se 1 (by rfl) ⟨2260565, by rfl⟩ : syracuseStep 3014087 = 4521131) B4521131
theorem B2009391 : Blo 2007435 2009391 := bstep (se 1 (by rfl) ⟨1507043, by rfl⟩ : syracuseStep 2009391 = 3014087) B3014087
theorem B3014093 : Blo 2007435 3014093 := bbase (se 3 (by rfl) ⟨565142, by rfl⟩ : syracuseStep 3014093 = 1130285) (by norm_num)
theorem B2009395 : Blo 2007435 2009395 := bstep (se 1 (by rfl) ⟨1507046, by rfl⟩ : syracuseStep 2009395 = 3014093) B3014093
theorem B4521149 : Blo 2007435 4521149 := bbase (se 3 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 4521149 = 1695431) (by norm_num)
theorem B3014099 : Blo 2007435 3014099 := bstep (se 1 (by rfl) ⟨2260574, by rfl⟩ : syracuseStep 3014099 = 4521149) B4521149
theorem B2009399 : Blo 2007435 2009399 := bstep (se 1 (by rfl) ⟨1507049, by rfl⟩ : syracuseStep 2009399 = 3014099) B3014099
theorem B3390869 : Blo 2007435 3390869 := bbase (se 6 (by rfl) ⟨79473, by rfl⟩ : syracuseStep 3390869 = 158947) (by norm_num)
theorem B2260579 : Blo 2007435 2260579 := bstep (se 1 (by rfl) ⟨1695434, by rfl⟩ : syracuseStep 2260579 = 3390869) B3390869
theorem B3014105 : Blo 2007435 3014105 := bstep (se 2 (by rfl) ⟨1130289, by rfl⟩ : syracuseStep 3014105 = 2260579) B2260579
theorem B2009403 : Blo 2007435 2009403 := bstep (se 1 (by rfl) ⟨1507052, by rfl⟩ : syracuseStep 2009403 = 3014105) B3014105
theorem B5226053 : Blo 2007435 5226053 := bbase (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) (by norm_num)
theorem B13936141 : Blo 2007435 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B74326085 : Blo 2007435 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B49550723 : Blo 2007435 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B33033815 : Blo 2007435 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B22022543 : Blo 2007435 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B14681695 : Blo 2007435 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B19575593 : Blo 2007435 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B13050395 : Blo 2007435 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B8700263 : Blo 2007435 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B5800175 : Blo 2007435 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B3866783 : Blo 2007435 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B10311421 : Blo 2007435 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B13748561 : Blo 2007435 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B9165707 : Blo 2007435 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B6110471 : Blo 2007435 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B4073647 : Blo 2007435 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B5431529 : Blo 2007435 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B3621019 : Blo 2007435 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B4828025 : Blo 2007435 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B12874733 : Blo 2007435 12874733 := bstep (se 3 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 12874733 = 4828025) B4828025
theorem B8583155 : Blo 2007435 8583155 := bstep (se 1 (by rfl) ⟨6437366, by rfl⟩ : syracuseStep 8583155 = 12874733) B12874733
theorem B5722103 : Blo 2007435 5722103 := bstep (se 1 (by rfl) ⟨4291577, by rfl⟩ : syracuseStep 5722103 = 8583155) B8583155
theorem B15258941 : Blo 2007435 15258941 := bstep (se 3 (by rfl) ⟨2861051, by rfl⟩ : syracuseStep 15258941 = 5722103) B5722103
theorem B10172627 : Blo 2007435 10172627 := bstep (se 1 (by rfl) ⟨7629470, by rfl⟩ : syracuseStep 10172627 = 15258941) B15258941
theorem B6781751 : Blo 2007435 6781751 := bstep (se 1 (by rfl) ⟨5086313, by rfl⟩ : syracuseStep 6781751 = 10172627) B10172627
theorem B4521167 : Blo 2007435 4521167 := bstep (se 1 (by rfl) ⟨3390875, by rfl⟩ : syracuseStep 4521167 = 6781751) B6781751
theorem B3014111 : Blo 2007435 3014111 := bstep (se 1 (by rfl) ⟨2260583, by rfl⟩ : syracuseStep 3014111 = 4521167) B4521167
theorem B2009407 : Blo 2007435 2009407 := bstep (se 1 (by rfl) ⟨1507055, by rfl⟩ : syracuseStep 2009407 = 3014111) B3014111
theorem B3014117 : Blo 2007435 3014117 := bbase (se 4 (by rfl) ⟨282573, by rfl⟩ : syracuseStep 3014117 = 565147) (by norm_num)
theorem B2009411 : Blo 2007435 2009411 := bstep (se 1 (by rfl) ⟨1507058, by rfl⟩ : syracuseStep 2009411 = 3014117) B3014117
theorem B19312181 : Blo 2007435 19312181 := bbase (se 5 (by rfl) ⟨905258, by rfl⟩ : syracuseStep 19312181 = 1810517) (by norm_num)
theorem B12874787 : Blo 2007435 12874787 := bstep (se 1 (by rfl) ⟨9656090, by rfl⟩ : syracuseStep 12874787 = 19312181) B19312181
theorem B8583191 : Blo 2007435 8583191 := bstep (se 1 (by rfl) ⟨6437393, by rfl⟩ : syracuseStep 8583191 = 12874787) B12874787
theorem B5722127 : Blo 2007435 5722127 := bstep (se 1 (by rfl) ⟨4291595, by rfl⟩ : syracuseStep 5722127 = 8583191) B8583191
theorem B3814751 : Blo 2007435 3814751 := bstep (se 1 (by rfl) ⟨2861063, by rfl⟩ : syracuseStep 3814751 = 5722127) B5722127
theorem B2543167 : Blo 2007435 2543167 := bstep (se 1 (by rfl) ⟨1907375, by rfl⟩ : syracuseStep 2543167 = 3814751) B3814751
theorem B3390889 : Blo 2007435 3390889 := bstep (se 2 (by rfl) ⟨1271583, by rfl⟩ : syracuseStep 3390889 = 2543167) B2543167
theorem B4521185 : Blo 2007435 4521185 := bstep (se 2 (by rfl) ⟨1695444, by rfl⟩ : syracuseStep 4521185 = 3390889) B3390889
theorem B3014123 : Blo 2007435 3014123 := bstep (se 1 (by rfl) ⟨2260592, by rfl⟩ : syracuseStep 3014123 = 4521185) B4521185
theorem B2009415 : Blo 2007435 2009415 := bstep (se 1 (by rfl) ⟨1507061, by rfl⟩ : syracuseStep 2009415 = 3014123) B3014123
theorem B2260597 : Blo 2007435 2260597 := bbase (se 5 (by rfl) ⟨105965, by rfl⟩ : syracuseStep 2260597 = 211931) (by norm_num)
theorem B3014129 : Blo 2007435 3014129 := bstep (se 2 (by rfl) ⟨1130298, by rfl⟩ : syracuseStep 3014129 = 2260597) B2260597
theorem B2009419 : Blo 2007435 2009419 := bstep (se 1 (by rfl) ⟨1507064, by rfl⟩ : syracuseStep 2009419 = 3014129) B3014129
theorem B2543177 : Blo 2007435 2543177 := bbase (se 2 (by rfl) ⟨953691, by rfl⟩ : syracuseStep 2543177 = 1907383) (by norm_num)
theorem B6781805 : Blo 2007435 6781805 := bstep (se 3 (by rfl) ⟨1271588, by rfl⟩ : syracuseStep 6781805 = 2543177) B2543177
theorem B4521203 : Blo 2007435 4521203 := bstep (se 1 (by rfl) ⟨3390902, by rfl⟩ : syracuseStep 4521203 = 6781805) B6781805
theorem B3014135 : Blo 2007435 3014135 := bstep (se 1 (by rfl) ⟨2260601, by rfl⟩ : syracuseStep 3014135 = 4521203) B4521203
theorem B2009423 : Blo 2007435 2009423 := bstep (se 1 (by rfl) ⟨1507067, by rfl⟩ : syracuseStep 2009423 = 3014135) B3014135
theorem B3014141 : Blo 2007435 3014141 := bbase (se 3 (by rfl) ⟨565151, by rfl⟩ : syracuseStep 3014141 = 1130303) (by norm_num)
theorem B2009427 : Blo 2007435 2009427 := bstep (se 1 (by rfl) ⟨1507070, by rfl⟩ : syracuseStep 2009427 = 3014141) B3014141
theorem B4521221 : Blo 2007435 4521221 := bbase (se 4 (by rfl) ⟨423864, by rfl⟩ : syracuseStep 4521221 = 847729) (by norm_num)
theorem B3014147 : Blo 2007435 3014147 := bstep (se 1 (by rfl) ⟨2260610, by rfl⟩ : syracuseStep 3014147 = 4521221) B4521221
theorem B2009431 : Blo 2007435 2009431 := bstep (se 1 (by rfl) ⟨1507073, by rfl⟩ : syracuseStep 2009431 = 3014147) B3014147
theorem B3814789 : Blo 2007435 3814789 := bbase (se 4 (by rfl) ⟨357636, by rfl⟩ : syracuseStep 3814789 = 715273) (by norm_num)
theorem B5086385 : Blo 2007435 5086385 := bstep (se 2 (by rfl) ⟨1907394, by rfl⟩ : syracuseStep 5086385 = 3814789) B3814789
theorem B3390923 : Blo 2007435 3390923 := bstep (se 1 (by rfl) ⟨2543192, by rfl⟩ : syracuseStep 3390923 = 5086385) B5086385
theorem B2260615 : Blo 2007435 2260615 := bstep (se 1 (by rfl) ⟨1695461, by rfl⟩ : syracuseStep 2260615 = 3390923) B3390923
theorem B3014153 : Blo 2007435 3014153 := bstep (se 2 (by rfl) ⟨1130307, by rfl⟩ : syracuseStep 3014153 = 2260615) B2260615
theorem B2009435 : Blo 2007435 2009435 := bstep (se 1 (by rfl) ⟨1507076, by rfl⟩ : syracuseStep 2009435 = 3014153) B3014153
theorem C0 (j : ℕ) (h1 : 501858 ≤ j) (h2 : j ≤ 502358) : Blo 2007435 (4 * j + 3) := by
  interval_cases j
  · exact B2007435
  · exact B2007439
  · exact B2007443
  · exact B2007447
  · exact B2007451
  · exact B2007455
  · exact B2007459
  · exact B2007463
  · exact B2007467
  · exact B2007471
  · exact B2007475
  · exact B2007479
  · exact B2007483
  · exact B2007487
  · exact B2007491
  · exact B2007495
  · exact B2007499
  · exact B2007503
  · exact B2007507
  · exact B2007511
  · exact B2007515
  · exact B2007519
  · exact B2007523
  · exact B2007527
  · exact B2007531
  · exact B2007535
  · exact B2007539
  · exact B2007543
  · exact B2007547
  · exact B2007551
  · exact B2007555
  · exact B2007559
  · exact B2007563
  · exact B2007567
  · exact B2007571
  · exact B2007575
  · exact B2007579
  · exact B2007583
  · exact B2007587
  · exact B2007591
  · exact B2007595
  · exact B2007599
  · exact B2007603
  · exact B2007607
  · exact B2007611
  · exact B2007615
  · exact B2007619
  · exact B2007623
  · exact B2007627
  · exact B2007631
  · exact B2007635
  · exact B2007639
  · exact B2007643
  · exact B2007647
  · exact B2007651
  · exact B2007655
  · exact B2007659
  · exact B2007663
  · exact B2007667
  · exact B2007671
  · exact B2007675
  · exact B2007679
  · exact B2007683
  · exact B2007687
  · exact B2007691
  · exact B2007695
  · exact B2007699
  · exact B2007703
  · exact B2007707
  · exact B2007711
  · exact B2007715
  · exact B2007719
  · exact B2007723
  · exact B2007727
  · exact B2007731
  · exact B2007735
  · exact B2007739
  · exact B2007743
  · exact B2007747
  · exact B2007751
  · exact B2007755
  · exact B2007759
  · exact B2007763
  · exact B2007767
  · exact B2007771
  · exact B2007775
  · exact B2007779
  · exact B2007783
  · exact B2007787
  · exact B2007791
  · exact B2007795
  · exact B2007799
  · exact B2007803
  · exact B2007807
  · exact B2007811
  · exact B2007815
  · exact B2007819
  · exact B2007823
  · exact B2007827
  · exact B2007831
  · exact B2007835
  · exact B2007839
  · exact B2007843
  · exact B2007847
  · exact B2007851
  · exact B2007855
  · exact B2007859
  · exact B2007863
  · exact B2007867
  · exact B2007871
  · exact B2007875
  · exact B2007879
  · exact B2007883
  · exact B2007887
  · exact B2007891
  · exact B2007895
  · exact B2007899
  · exact B2007903
  · exact B2007907
  · exact B2007911
  · exact B2007915
  · exact B2007919
  · exact B2007923
  · exact B2007927
  · exact B2007931
  · exact B2007935
  · exact B2007939
  · exact B2007943
  · exact B2007947
  · exact B2007951
  · exact B2007955
  · exact B2007959
  · exact B2007963
  · exact B2007967
  · exact B2007971
  · exact B2007975
  · exact B2007979
  · exact B2007983
  · exact B2007987
  · exact B2007991
  · exact B2007995
  · exact B2007999
  · exact B2008003
  · exact B2008007
  · exact B2008011
  · exact B2008015
  · exact B2008019
  · exact B2008023
  · exact B2008027
  · exact B2008031
  · exact B2008035
  · exact B2008039
  · exact B2008043
  · exact B2008047
  · exact B2008051
  · exact B2008055
  · exact B2008059
  · exact B2008063
  · exact B2008067
  · exact B2008071
  · exact B2008075
  · exact B2008079
  · exact B2008083
  · exact B2008087
  · exact B2008091
  · exact B2008095
  · exact B2008099
  · exact B2008103
  · exact B2008107
  · exact B2008111
  · exact B2008115
  · exact B2008119
  · exact B2008123
  · exact B2008127
  · exact B2008131
  · exact B2008135
  · exact B2008139
  · exact B2008143
  · exact B2008147
  · exact B2008151
  · exact B2008155
  · exact B2008159
  · exact B2008163
  · exact B2008167
  · exact B2008171
  · exact B2008175
  · exact B2008179
  · exact B2008183
  · exact B2008187
  · exact B2008191
  · exact B2008195
  · exact B2008199
  · exact B2008203
  · exact B2008207
  · exact B2008211
  · exact B2008215
  · exact B2008219
  · exact B2008223
  · exact B2008227
  · exact B2008231
  · exact B2008235
  · exact B2008239
  · exact B2008243
  · exact B2008247
  · exact B2008251
  · exact B2008255
  · exact B2008259
  · exact B2008263
  · exact B2008267
  · exact B2008271
  · exact B2008275
  · exact B2008279
  · exact B2008283
  · exact B2008287
  · exact B2008291
  · exact B2008295
  · exact B2008299
  · exact B2008303
  · exact B2008307
  · exact B2008311
  · exact B2008315
  · exact B2008319
  · exact B2008323
  · exact B2008327
  · exact B2008331
  · exact B2008335
  · exact B2008339
  · exact B2008343
  · exact B2008347
  · exact B2008351
  · exact B2008355
  · exact B2008359
  · exact B2008363
  · exact B2008367
  · exact B2008371
  · exact B2008375
  · exact B2008379
  · exact B2008383
  · exact B2008387
  · exact B2008391
  · exact B2008395
  · exact B2008399
  · exact B2008403
  · exact B2008407
  · exact B2008411
  · exact B2008415
  · exact B2008419
  · exact B2008423
  · exact B2008427
  · exact B2008431
  · exact B2008435
  · exact B2008439
  · exact B2008443
  · exact B2008447
  · exact B2008451
  · exact B2008455
  · exact B2008459
  · exact B2008463
  · exact B2008467
  · exact B2008471
  · exact B2008475
  · exact B2008479
  · exact B2008483
  · exact B2008487
  · exact B2008491
  · exact B2008495
  · exact B2008499
  · exact B2008503
  · exact B2008507
  · exact B2008511
  · exact B2008515
  · exact B2008519
  · exact B2008523
  · exact B2008527
  · exact B2008531
  · exact B2008535
  · exact B2008539
  · exact B2008543
  · exact B2008547
  · exact B2008551
  · exact B2008555
  · exact B2008559
  · exact B2008563
  · exact B2008567
  · exact B2008571
  · exact B2008575
  · exact B2008579
  · exact B2008583
  · exact B2008587
  · exact B2008591
  · exact B2008595
  · exact B2008599
  · exact B2008603
  · exact B2008607
  · exact B2008611
  · exact B2008615
  · exact B2008619
  · exact B2008623
  · exact B2008627
  · exact B2008631
  · exact B2008635
  · exact B2008639
  · exact B2008643
  · exact B2008647
  · exact B2008651
  · exact B2008655
  · exact B2008659
  · exact B2008663
  · exact B2008667
  · exact B2008671
  · exact B2008675
  · exact B2008679
  · exact B2008683
  · exact B2008687
  · exact B2008691
  · exact B2008695
  · exact B2008699
  · exact B2008703
  · exact B2008707
  · exact B2008711
  · exact B2008715
  · exact B2008719
  · exact B2008723
  · exact B2008727
  · exact B2008731
  · exact B2008735
  · exact B2008739
  · exact B2008743
  · exact B2008747
  · exact B2008751
  · exact B2008755
  · exact B2008759
  · exact B2008763
  · exact B2008767
  · exact B2008771
  · exact B2008775
  · exact B2008779
  · exact B2008783
  · exact B2008787
  · exact B2008791
  · exact B2008795
  · exact B2008799
  · exact B2008803
  · exact B2008807
  · exact B2008811
  · exact B2008815
  · exact B2008819
  · exact B2008823
  · exact B2008827
  · exact B2008831
  · exact B2008835
  · exact B2008839
  · exact B2008843
  · exact B2008847
  · exact B2008851
  · exact B2008855
  · exact B2008859
  · exact B2008863
  · exact B2008867
  · exact B2008871
  · exact B2008875
  · exact B2008879
  · exact B2008883
  · exact B2008887
  · exact B2008891
  · exact B2008895
  · exact B2008899
  · exact B2008903
  · exact B2008907
  · exact B2008911
  · exact B2008915
  · exact B2008919
  · exact B2008923
  · exact B2008927
  · exact B2008931
  · exact B2008935
  · exact B2008939
  · exact B2008943
  · exact B2008947
  · exact B2008951
  · exact B2008955
  · exact B2008959
  · exact B2008963
  · exact B2008967
  · exact B2008971
  · exact B2008975
  · exact B2008979
  · exact B2008983
  · exact B2008987
  · exact B2008991
  · exact B2008995
  · exact B2008999
  · exact B2009003
  · exact B2009007
  · exact B2009011
  · exact B2009015
  · exact B2009019
  · exact B2009023
  · exact B2009027
  · exact B2009031
  · exact B2009035
  · exact B2009039
  · exact B2009043
  · exact B2009047
  · exact B2009051
  · exact B2009055
  · exact B2009059
  · exact B2009063
  · exact B2009067
  · exact B2009071
  · exact B2009075
  · exact B2009079
  · exact B2009083
  · exact B2009087
  · exact B2009091
  · exact B2009095
  · exact B2009099
  · exact B2009103
  · exact B2009107
  · exact B2009111
  · exact B2009115
  · exact B2009119
  · exact B2009123
  · exact B2009127
  · exact B2009131
  · exact B2009135
  · exact B2009139
  · exact B2009143
  · exact B2009147
  · exact B2009151
  · exact B2009155
  · exact B2009159
  · exact B2009163
  · exact B2009167
  · exact B2009171
  · exact B2009175
  · exact B2009179
  · exact B2009183
  · exact B2009187
  · exact B2009191
  · exact B2009195
  · exact B2009199
  · exact B2009203
  · exact B2009207
  · exact B2009211
  · exact B2009215
  · exact B2009219
  · exact B2009223
  · exact B2009227
  · exact B2009231
  · exact B2009235
  · exact B2009239
  · exact B2009243
  · exact B2009247
  · exact B2009251
  · exact B2009255
  · exact B2009259
  · exact B2009263
  · exact B2009267
  · exact B2009271
  · exact B2009275
  · exact B2009279
  · exact B2009283
  · exact B2009287
  · exact B2009291
  · exact B2009295
  · exact B2009299
  · exact B2009303
  · exact B2009307
  · exact B2009311
  · exact B2009315
  · exact B2009319
  · exact B2009323
  · exact B2009327
  · exact B2009331
  · exact B2009335
  · exact B2009339
  · exact B2009343
  · exact B2009347
  · exact B2009351
  · exact B2009355
  · exact B2009359
  · exact B2009363
  · exact B2009367
  · exact B2009371
  · exact B2009375
  · exact B2009379
  · exact B2009383
  · exact B2009387
  · exact B2009391
  · exact B2009395
  · exact B2009399
  · exact B2009403
  · exact B2009407
  · exact B2009411
  · exact B2009415
  · exact B2009419
  · exact B2009423
  · exact B2009427
  · exact B2009431
  · exact B2009435
theorem solution (m : ℕ) (hlo : 2007435 ≤ m) (hhi : m ≤ 2009435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 501858 ≤ j := by omega
    have hj2 : j ≤ 502358 := by omega
    have hb : Blo 2007435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
