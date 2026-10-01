-- Prove2me | solution 1 for syracuse_descends_range_2203435_2205435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:21.115572+00:00
-- url     : https://prove2.me/submissions/08cf1274-6c50-4295-abc8-fd715783a287

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

theorem B2478865 : Blo 2203435 2478865 := bbase (se 2 (by rfl) ⟨929574, by rfl⟩ : syracuseStep 2478865 = 1859149) (by norm_num)
theorem B3305153 : Blo 2203435 3305153 := bstep (se 2 (by rfl) ⟨1239432, by rfl⟩ : syracuseStep 3305153 = 2478865) B2478865
theorem B2203435 : Blo 2203435 2203435 := bstep (se 1 (by rfl) ⟨1652576, by rfl⟩ : syracuseStep 2203435 = 3305153) B3305153
theorem B4183093 : Blo 2203435 4183093 := bbase (se 5 (by rfl) ⟨196082, by rfl⟩ : syracuseStep 4183093 = 392165) (by norm_num)
theorem B5577457 : Blo 2203435 5577457 := bstep (se 2 (by rfl) ⟨2091546, by rfl⟩ : syracuseStep 5577457 = 4183093) B4183093
theorem B7436609 : Blo 2203435 7436609 := bstep (se 2 (by rfl) ⟨2788728, by rfl⟩ : syracuseStep 7436609 = 5577457) B5577457
theorem B4957739 : Blo 2203435 4957739 := bstep (se 1 (by rfl) ⟨3718304, by rfl⟩ : syracuseStep 4957739 = 7436609) B7436609
theorem B3305159 : Blo 2203435 3305159 := bstep (se 1 (by rfl) ⟨2478869, by rfl⟩ : syracuseStep 3305159 = 4957739) B4957739
theorem B2203439 : Blo 2203435 2203439 := bstep (se 1 (by rfl) ⟨1652579, by rfl⟩ : syracuseStep 2203439 = 3305159) B3305159
theorem B3305165 : Blo 2203435 3305165 := bbase (se 3 (by rfl) ⟨619718, by rfl⟩ : syracuseStep 3305165 = 1239437) (by norm_num)
theorem B2203443 : Blo 2203435 2203443 := bstep (se 1 (by rfl) ⟨1652582, by rfl⟩ : syracuseStep 2203443 = 3305165) B3305165
theorem B4957757 : Blo 2203435 4957757 := bbase (se 3 (by rfl) ⟨929579, by rfl⟩ : syracuseStep 4957757 = 1859159) (by norm_num)
theorem B3305171 : Blo 2203435 3305171 := bstep (se 1 (by rfl) ⟨2478878, by rfl⟩ : syracuseStep 3305171 = 4957757) B4957757
theorem B2203447 : Blo 2203435 2203447 := bstep (se 1 (by rfl) ⟨1652585, by rfl⟩ : syracuseStep 2203447 = 3305171) B3305171
theorem B3718325 : Blo 2203435 3718325 := bbase (se 5 (by rfl) ⟨174296, by rfl⟩ : syracuseStep 3718325 = 348593) (by norm_num)
theorem B2478883 : Blo 2203435 2478883 := bstep (se 1 (by rfl) ⟨1859162, by rfl⟩ : syracuseStep 2478883 = 3718325) B3718325
theorem B3305177 : Blo 2203435 3305177 := bstep (se 2 (by rfl) ⟨1239441, by rfl⟩ : syracuseStep 3305177 = 2478883) B2478883
theorem B2203451 : Blo 2203435 2203451 := bstep (se 1 (by rfl) ⟨1652588, by rfl⟩ : syracuseStep 2203451 = 3305177) B3305177
theorem B5653597 : Blo 2203435 5653597 := bbase (se 3 (by rfl) ⟨1060049, by rfl⟩ : syracuseStep 5653597 = 2120099) (by norm_num)
theorem B7538129 : Blo 2203435 7538129 := bstep (se 2 (by rfl) ⟨2826798, by rfl⟩ : syracuseStep 7538129 = 5653597) B5653597
theorem B5025419 : Blo 2203435 5025419 := bstep (se 1 (by rfl) ⟨3769064, by rfl⟩ : syracuseStep 5025419 = 7538129) B7538129
theorem B3350279 : Blo 2203435 3350279 := bstep (se 1 (by rfl) ⟨2512709, by rfl⟩ : syracuseStep 3350279 = 5025419) B5025419
theorem B8934077 : Blo 2203435 8934077 := bstep (se 3 (by rfl) ⟨1675139, by rfl⟩ : syracuseStep 8934077 = 3350279) B3350279
theorem B5956051 : Blo 2203435 5956051 := bstep (se 1 (by rfl) ⟨4467038, by rfl⟩ : syracuseStep 5956051 = 8934077) B8934077
theorem B7941401 : Blo 2203435 7941401 := bstep (se 2 (by rfl) ⟨2978025, by rfl⟩ : syracuseStep 7941401 = 5956051) B5956051
theorem B5294267 : Blo 2203435 5294267 := bstep (se 1 (by rfl) ⟨3970700, by rfl⟩ : syracuseStep 5294267 = 7941401) B7941401
theorem B3529511 : Blo 2203435 3529511 := bstep (se 1 (by rfl) ⟨2647133, by rfl⟩ : syracuseStep 3529511 = 5294267) B5294267
theorem B2353007 : Blo 2203435 2353007 := bstep (se 1 (by rfl) ⟨1764755, by rfl⟩ : syracuseStep 2353007 = 3529511) B3529511
theorem B6274685 : Blo 2203435 6274685 := bstep (se 3 (by rfl) ⟨1176503, by rfl⟩ : syracuseStep 6274685 = 2353007) B2353007
theorem B16732493 : Blo 2203435 16732493 := bstep (se 3 (by rfl) ⟨3137342, by rfl⟩ : syracuseStep 16732493 = 6274685) B6274685
theorem B11154995 : Blo 2203435 11154995 := bstep (se 1 (by rfl) ⟨8366246, by rfl⟩ : syracuseStep 11154995 = 16732493) B16732493
theorem B7436663 : Blo 2203435 7436663 := bstep (se 1 (by rfl) ⟨5577497, by rfl⟩ : syracuseStep 7436663 = 11154995) B11154995
theorem B4957775 : Blo 2203435 4957775 := bstep (se 1 (by rfl) ⟨3718331, by rfl⟩ : syracuseStep 4957775 = 7436663) B7436663
theorem B3305183 : Blo 2203435 3305183 := bstep (se 1 (by rfl) ⟨2478887, by rfl⟩ : syracuseStep 3305183 = 4957775) B4957775
theorem B2203455 : Blo 2203435 2203455 := bstep (se 1 (by rfl) ⟨1652591, by rfl⟩ : syracuseStep 2203455 = 3305183) B3305183
theorem B3305189 : Blo 2203435 3305189 := bbase (se 4 (by rfl) ⟨309861, by rfl⟩ : syracuseStep 3305189 = 619723) (by norm_num)
theorem B2203459 : Blo 2203435 2203459 := bstep (se 1 (by rfl) ⟨1652594, by rfl⟩ : syracuseStep 2203459 = 3305189) B3305189
theorem B6274709 : Blo 2203435 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B4183139 : Blo 2203435 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B2788759 : Blo 2203435 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B3718345 : Blo 2203435 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B4957793 : Blo 2203435 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B3305195 : Blo 2203435 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B2203463 : Blo 2203435 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B2478901 : Blo 2203435 2478901 := bbase (se 5 (by rfl) ⟨116198, by rfl⟩ : syracuseStep 2478901 = 232397) (by norm_num)
theorem B3305201 : Blo 2203435 3305201 := bstep (se 2 (by rfl) ⟨1239450, by rfl⟩ : syracuseStep 3305201 = 2478901) B2478901
theorem B2203467 : Blo 2203435 2203467 := bstep (se 1 (by rfl) ⟨1652600, by rfl⟩ : syracuseStep 2203467 = 3305201) B3305201
theorem B2788769 : Blo 2203435 2788769 := bbase (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) (by norm_num)
theorem B7436717 : Blo 2203435 7436717 := bstep (se 3 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 7436717 = 2788769) B2788769
theorem B4957811 : Blo 2203435 4957811 := bstep (se 1 (by rfl) ⟨3718358, by rfl⟩ : syracuseStep 4957811 = 7436717) B7436717
theorem B3305207 : Blo 2203435 3305207 := bstep (se 1 (by rfl) ⟨2478905, by rfl⟩ : syracuseStep 3305207 = 4957811) B4957811
theorem B2203471 : Blo 2203435 2203471 := bstep (se 1 (by rfl) ⟨1652603, by rfl⟩ : syracuseStep 2203471 = 3305207) B3305207
theorem B3305213 : Blo 2203435 3305213 := bbase (se 3 (by rfl) ⟨619727, by rfl⟩ : syracuseStep 3305213 = 1239455) (by norm_num)
theorem B2203475 : Blo 2203435 2203475 := bstep (se 1 (by rfl) ⟨1652606, by rfl⟩ : syracuseStep 2203475 = 3305213) B3305213
theorem B4957829 : Blo 2203435 4957829 := bbase (se 4 (by rfl) ⟨464796, by rfl⟩ : syracuseStep 4957829 = 929593) (by norm_num)
theorem B3305219 : Blo 2203435 3305219 := bstep (se 1 (by rfl) ⟨2478914, by rfl⟩ : syracuseStep 3305219 = 4957829) B4957829
theorem B2203479 : Blo 2203435 2203479 := bstep (se 1 (by rfl) ⟨1652609, by rfl⟩ : syracuseStep 2203479 = 3305219) B3305219
theorem B5808997 : Blo 2203435 5808997 := bbase (se 4 (by rfl) ⟨544593, by rfl⟩ : syracuseStep 5808997 = 1089187) (by norm_num)
theorem B7745329 : Blo 2203435 7745329 := bstep (se 2 (by rfl) ⟨2904498, by rfl⟩ : syracuseStep 7745329 = 5808997) B5808997
theorem B10327105 : Blo 2203435 10327105 := bstep (se 2 (by rfl) ⟨3872664, by rfl⟩ : syracuseStep 10327105 = 7745329) B7745329
theorem B13769473 : Blo 2203435 13769473 := bstep (se 2 (by rfl) ⟨5163552, by rfl⟩ : syracuseStep 13769473 = 10327105) B10327105
theorem B18359297 : Blo 2203435 18359297 := bstep (se 2 (by rfl) ⟨6884736, by rfl⟩ : syracuseStep 18359297 = 13769473) B13769473
theorem B12239531 : Blo 2203435 12239531 := bstep (se 1 (by rfl) ⟨9179648, by rfl⟩ : syracuseStep 12239531 = 18359297) B18359297
theorem B8159687 : Blo 2203435 8159687 := bstep (se 1 (by rfl) ⟨6119765, by rfl⟩ : syracuseStep 8159687 = 12239531) B12239531
theorem B5439791 : Blo 2203435 5439791 := bstep (se 1 (by rfl) ⟨4079843, by rfl⟩ : syracuseStep 5439791 = 8159687) B8159687
theorem B3626527 : Blo 2203435 3626527 := bstep (se 1 (by rfl) ⟨2719895, by rfl⟩ : syracuseStep 3626527 = 5439791) B5439791
theorem B4835369 : Blo 2203435 4835369 := bstep (se 2 (by rfl) ⟨1813263, by rfl⟩ : syracuseStep 4835369 = 3626527) B3626527
theorem B3223579 : Blo 2203435 3223579 := bstep (se 1 (by rfl) ⟨2417684, by rfl⟩ : syracuseStep 3223579 = 4835369) B4835369
theorem B4298105 : Blo 2203435 4298105 := bstep (se 2 (by rfl) ⟨1611789, by rfl⟩ : syracuseStep 4298105 = 3223579) B3223579
theorem B2865403 : Blo 2203435 2865403 := bstep (se 1 (by rfl) ⟨2149052, by rfl⟩ : syracuseStep 2865403 = 4298105) B4298105
theorem B3820537 : Blo 2203435 3820537 := bstep (se 2 (by rfl) ⟨1432701, by rfl⟩ : syracuseStep 3820537 = 2865403) B2865403
theorem B20376197 : Blo 2203435 20376197 := bstep (se 4 (by rfl) ⟨1910268, by rfl⟩ : syracuseStep 20376197 = 3820537) B3820537
theorem B13584131 : Blo 2203435 13584131 := bstep (se 1 (by rfl) ⟨10188098, by rfl⟩ : syracuseStep 13584131 = 20376197) B20376197
theorem B9056087 : Blo 2203435 9056087 := bstep (se 1 (by rfl) ⟨6792065, by rfl⟩ : syracuseStep 9056087 = 13584131) B13584131
theorem B6037391 : Blo 2203435 6037391 := bstep (se 1 (by rfl) ⟨4528043, by rfl⟩ : syracuseStep 6037391 = 9056087) B9056087
theorem B4024927 : Blo 2203435 4024927 := bstep (se 1 (by rfl) ⟨3018695, by rfl⟩ : syracuseStep 4024927 = 6037391) B6037391
theorem B5366569 : Blo 2203435 5366569 := bstep (se 2 (by rfl) ⟨2012463, by rfl⟩ : syracuseStep 5366569 = 4024927) B4024927
theorem B7155425 : Blo 2203435 7155425 := bstep (se 2 (by rfl) ⟨2683284, by rfl⟩ : syracuseStep 7155425 = 5366569) B5366569
theorem B4770283 : Blo 2203435 4770283 := bstep (se 1 (by rfl) ⟨3577712, by rfl⟩ : syracuseStep 4770283 = 7155425) B7155425
theorem B6360377 : Blo 2203435 6360377 := bstep (se 2 (by rfl) ⟨2385141, by rfl⟩ : syracuseStep 6360377 = 4770283) B4770283
theorem B16961005 : Blo 2203435 16961005 := bstep (se 3 (by rfl) ⟨3180188, by rfl⟩ : syracuseStep 16961005 = 6360377) B6360377
theorem B90458693 : Blo 2203435 90458693 := bstep (se 4 (by rfl) ⟨8480502, by rfl⟩ : syracuseStep 90458693 = 16961005) B16961005
theorem B60305795 : Blo 2203435 60305795 := bstep (se 1 (by rfl) ⟨45229346, by rfl⟩ : syracuseStep 60305795 = 90458693) B90458693
theorem B40203863 : Blo 2203435 40203863 := bstep (se 1 (by rfl) ⟨30152897, by rfl⟩ : syracuseStep 40203863 = 60305795) B60305795
theorem B26802575 : Blo 2203435 26802575 := bstep (se 1 (by rfl) ⟨20101931, by rfl⟩ : syracuseStep 26802575 = 40203863) B40203863
theorem B17868383 : Blo 2203435 17868383 := bstep (se 1 (by rfl) ⟨13401287, by rfl⟩ : syracuseStep 17868383 = 26802575) B26802575
theorem B11912255 : Blo 2203435 11912255 := bstep (se 1 (by rfl) ⟨8934191, by rfl⟩ : syracuseStep 11912255 = 17868383) B17868383
theorem B7941503 : Blo 2203435 7941503 := bstep (se 1 (by rfl) ⟨5956127, by rfl⟩ : syracuseStep 7941503 = 11912255) B11912255
theorem B5294335 : Blo 2203435 5294335 := bstep (se 1 (by rfl) ⟨3970751, by rfl⟩ : syracuseStep 5294335 = 7941503) B7941503
theorem B7059113 : Blo 2203435 7059113 := bstep (se 2 (by rfl) ⟨2647167, by rfl⟩ : syracuseStep 7059113 = 5294335) B5294335
theorem B4706075 : Blo 2203435 4706075 := bstep (se 1 (by rfl) ⟨3529556, by rfl⟩ : syracuseStep 4706075 = 7059113) B7059113
theorem B3137383 : Blo 2203435 3137383 := bstep (se 1 (by rfl) ⟨2353037, by rfl⟩ : syracuseStep 3137383 = 4706075) B4706075
theorem B4183177 : Blo 2203435 4183177 := bstep (se 2 (by rfl) ⟨1568691, by rfl⟩ : syracuseStep 4183177 = 3137383) B3137383
theorem B5577569 : Blo 2203435 5577569 := bstep (se 2 (by rfl) ⟨2091588, by rfl⟩ : syracuseStep 5577569 = 4183177) B4183177
theorem B3718379 : Blo 2203435 3718379 := bstep (se 1 (by rfl) ⟨2788784, by rfl⟩ : syracuseStep 3718379 = 5577569) B5577569
theorem B2478919 : Blo 2203435 2478919 := bstep (se 1 (by rfl) ⟨1859189, by rfl⟩ : syracuseStep 2478919 = 3718379) B3718379
theorem B3305225 : Blo 2203435 3305225 := bstep (se 2 (by rfl) ⟨1239459, by rfl⟩ : syracuseStep 3305225 = 2478919) B2478919
theorem B2203483 : Blo 2203435 2203483 := bstep (se 1 (by rfl) ⟨1652612, by rfl⟩ : syracuseStep 2203483 = 3305225) B3305225
theorem B11155157 : Blo 2203435 11155157 := bbase (se 7 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 11155157 = 261449) (by norm_num)
theorem B7436771 : Blo 2203435 7436771 := bstep (se 1 (by rfl) ⟨5577578, by rfl⟩ : syracuseStep 7436771 = 11155157) B11155157
theorem B4957847 : Blo 2203435 4957847 := bstep (se 1 (by rfl) ⟨3718385, by rfl⟩ : syracuseStep 4957847 = 7436771) B7436771
theorem B3305231 : Blo 2203435 3305231 := bstep (se 1 (by rfl) ⟨2478923, by rfl⟩ : syracuseStep 3305231 = 4957847) B4957847
theorem B2203487 : Blo 2203435 2203487 := bstep (se 1 (by rfl) ⟨1652615, by rfl⟩ : syracuseStep 2203487 = 3305231) B3305231
theorem B3305237 : Blo 2203435 3305237 := bbase (se 6 (by rfl) ⟨77466, by rfl⟩ : syracuseStep 3305237 = 154933) (by norm_num)
theorem B2203491 : Blo 2203435 2203491 := bstep (se 1 (by rfl) ⟨1652618, by rfl⟩ : syracuseStep 2203491 = 3305237) B3305237
theorem B3180205 : Blo 2203435 3180205 := bbase (se 3 (by rfl) ⟨596288, by rfl⟩ : syracuseStep 3180205 = 1192577) (by norm_num)
theorem B4240273 : Blo 2203435 4240273 := bstep (se 2 (by rfl) ⟨1590102, by rfl⟩ : syracuseStep 4240273 = 3180205) B3180205
theorem B5653697 : Blo 2203435 5653697 := bstep (se 2 (by rfl) ⟨2120136, by rfl⟩ : syracuseStep 5653697 = 4240273) B4240273
theorem B15076525 : Blo 2203435 15076525 := bstep (se 3 (by rfl) ⟨2826848, by rfl⟩ : syracuseStep 15076525 = 5653697) B5653697
theorem B20102033 : Blo 2203435 20102033 := bstep (se 2 (by rfl) ⟨7538262, by rfl⟩ : syracuseStep 20102033 = 15076525) B15076525
theorem B53605421 : Blo 2203435 53605421 := bstep (se 3 (by rfl) ⟨10051016, by rfl⟩ : syracuseStep 53605421 = 20102033) B20102033
theorem B35736947 : Blo 2203435 35736947 := bstep (se 1 (by rfl) ⟨26802710, by rfl⟩ : syracuseStep 35736947 = 53605421) B53605421
theorem B23824631 : Blo 2203435 23824631 := bstep (se 1 (by rfl) ⟨17868473, by rfl⟩ : syracuseStep 23824631 = 35736947) B35736947
theorem B63532349 : Blo 2203435 63532349 := bstep (se 3 (by rfl) ⟨11912315, by rfl⟩ : syracuseStep 63532349 = 23824631) B23824631
theorem B42354899 : Blo 2203435 42354899 := bstep (se 1 (by rfl) ⟨31766174, by rfl⟩ : syracuseStep 42354899 = 63532349) B63532349
theorem B28236599 : Blo 2203435 28236599 := bstep (se 1 (by rfl) ⟨21177449, by rfl⟩ : syracuseStep 28236599 = 42354899) B42354899
theorem B18824399 : Blo 2203435 18824399 := bstep (se 1 (by rfl) ⟨14118299, by rfl⟩ : syracuseStep 18824399 = 28236599) B28236599
theorem B12549599 : Blo 2203435 12549599 := bstep (se 1 (by rfl) ⟨9412199, by rfl⟩ : syracuseStep 12549599 = 18824399) B18824399
theorem B8366399 : Blo 2203435 8366399 := bstep (se 1 (by rfl) ⟨6274799, by rfl⟩ : syracuseStep 8366399 = 12549599) B12549599
theorem B5577599 : Blo 2203435 5577599 := bstep (se 1 (by rfl) ⟨4183199, by rfl⟩ : syracuseStep 5577599 = 8366399) B8366399
theorem B3718399 : Blo 2203435 3718399 := bstep (se 1 (by rfl) ⟨2788799, by rfl⟩ : syracuseStep 3718399 = 5577599) B5577599
theorem B4957865 : Blo 2203435 4957865 := bstep (se 2 (by rfl) ⟨1859199, by rfl⟩ : syracuseStep 4957865 = 3718399) B3718399
theorem B3305243 : Blo 2203435 3305243 := bstep (se 1 (by rfl) ⟨2478932, by rfl⟩ : syracuseStep 3305243 = 4957865) B4957865
theorem B2203495 : Blo 2203435 2203495 := bstep (se 1 (by rfl) ⟨1652621, by rfl⟩ : syracuseStep 2203495 = 3305243) B3305243
theorem B2478937 : Blo 2203435 2478937 := bbase (se 2 (by rfl) ⟨929601, by rfl⟩ : syracuseStep 2478937 = 1859203) (by norm_num)
theorem B3305249 : Blo 2203435 3305249 := bstep (se 2 (by rfl) ⟨1239468, by rfl⟩ : syracuseStep 3305249 = 2478937) B2478937
theorem B2203499 : Blo 2203435 2203499 := bstep (se 1 (by rfl) ⟨1652624, by rfl⟩ : syracuseStep 2203499 = 3305249) B3305249
theorem B4706117 : Blo 2203435 4706117 := bbase (se 4 (by rfl) ⟨441198, by rfl⟩ : syracuseStep 4706117 = 882397) (by norm_num)
theorem B3137411 : Blo 2203435 3137411 := bstep (se 1 (by rfl) ⟨2353058, by rfl⟩ : syracuseStep 3137411 = 4706117) B4706117
theorem B8366429 : Blo 2203435 8366429 := bstep (se 3 (by rfl) ⟨1568705, by rfl⟩ : syracuseStep 8366429 = 3137411) B3137411
theorem B5577619 : Blo 2203435 5577619 := bstep (se 1 (by rfl) ⟨4183214, by rfl⟩ : syracuseStep 5577619 = 8366429) B8366429
theorem B7436825 : Blo 2203435 7436825 := bstep (se 2 (by rfl) ⟨2788809, by rfl⟩ : syracuseStep 7436825 = 5577619) B5577619
theorem B4957883 : Blo 2203435 4957883 := bstep (se 1 (by rfl) ⟨3718412, by rfl⟩ : syracuseStep 4957883 = 7436825) B7436825
theorem B3305255 : Blo 2203435 3305255 := bstep (se 1 (by rfl) ⟨2478941, by rfl⟩ : syracuseStep 3305255 = 4957883) B4957883
theorem B2203503 : Blo 2203435 2203503 := bstep (se 1 (by rfl) ⟨1652627, by rfl⟩ : syracuseStep 2203503 = 3305255) B3305255
theorem B3305261 : Blo 2203435 3305261 := bbase (se 3 (by rfl) ⟨619736, by rfl⟩ : syracuseStep 3305261 = 1239473) (by norm_num)
theorem B2203507 : Blo 2203435 2203507 := bstep (se 1 (by rfl) ⟨1652630, by rfl⟩ : syracuseStep 2203507 = 3305261) B3305261
theorem B4957901 : Blo 2203435 4957901 := bbase (se 3 (by rfl) ⟨929606, by rfl⟩ : syracuseStep 4957901 = 1859213) (by norm_num)
theorem B3305267 : Blo 2203435 3305267 := bstep (se 1 (by rfl) ⟨2478950, by rfl⟩ : syracuseStep 3305267 = 4957901) B4957901
theorem B2203511 : Blo 2203435 2203511 := bstep (se 1 (by rfl) ⟨1652633, by rfl⟩ : syracuseStep 2203511 = 3305267) B3305267
theorem B2788825 : Blo 2203435 2788825 := bbase (se 2 (by rfl) ⟨1045809, by rfl⟩ : syracuseStep 2788825 = 2091619) (by norm_num)
theorem B3718433 : Blo 2203435 3718433 := bstep (se 2 (by rfl) ⟨1394412, by rfl⟩ : syracuseStep 3718433 = 2788825) B2788825
theorem B2478955 : Blo 2203435 2478955 := bstep (se 1 (by rfl) ⟨1859216, by rfl⟩ : syracuseStep 2478955 = 3718433) B3718433
theorem B3305273 : Blo 2203435 3305273 := bstep (se 2 (by rfl) ⟨1239477, by rfl⟩ : syracuseStep 3305273 = 2478955) B2478955
theorem B2203515 : Blo 2203435 2203515 := bstep (se 1 (by rfl) ⟨1652636, by rfl⟩ : syracuseStep 2203515 = 3305273) B3305273
theorem B3529613 : Blo 2203435 3529613 := bbase (se 3 (by rfl) ⟨661802, by rfl⟩ : syracuseStep 3529613 = 1323605) (by norm_num)
theorem B9412301 : Blo 2203435 9412301 := bstep (se 3 (by rfl) ⟨1764806, by rfl⟩ : syracuseStep 9412301 = 3529613) B3529613
theorem B25099469 : Blo 2203435 25099469 := bstep (se 3 (by rfl) ⟨4706150, by rfl⟩ : syracuseStep 25099469 = 9412301) B9412301
theorem B16732979 : Blo 2203435 16732979 := bstep (se 1 (by rfl) ⟨12549734, by rfl⟩ : syracuseStep 16732979 = 25099469) B25099469
theorem B11155319 : Blo 2203435 11155319 := bstep (se 1 (by rfl) ⟨8366489, by rfl⟩ : syracuseStep 11155319 = 16732979) B16732979
theorem B7436879 : Blo 2203435 7436879 := bstep (se 1 (by rfl) ⟨5577659, by rfl⟩ : syracuseStep 7436879 = 11155319) B11155319
theorem B4957919 : Blo 2203435 4957919 := bstep (se 1 (by rfl) ⟨3718439, by rfl⟩ : syracuseStep 4957919 = 7436879) B7436879
theorem B3305279 : Blo 2203435 3305279 := bstep (se 1 (by rfl) ⟨2478959, by rfl⟩ : syracuseStep 3305279 = 4957919) B4957919
theorem B2203519 : Blo 2203435 2203519 := bstep (se 1 (by rfl) ⟨1652639, by rfl⟩ : syracuseStep 2203519 = 3305279) B3305279
theorem B3305285 : Blo 2203435 3305285 := bbase (se 4 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 3305285 = 619741) (by norm_num)
theorem B2203523 : Blo 2203435 2203523 := bstep (se 1 (by rfl) ⟨1652642, by rfl⟩ : syracuseStep 2203523 = 3305285) B3305285
theorem B3718453 : Blo 2203435 3718453 := bbase (se 5 (by rfl) ⟨174302, by rfl⟩ : syracuseStep 3718453 = 348605) (by norm_num)
theorem B4957937 : Blo 2203435 4957937 := bstep (se 2 (by rfl) ⟨1859226, by rfl⟩ : syracuseStep 4957937 = 3718453) B3718453
theorem B3305291 : Blo 2203435 3305291 := bstep (se 1 (by rfl) ⟨2478968, by rfl⟩ : syracuseStep 3305291 = 4957937) B4957937
theorem B2203527 : Blo 2203435 2203527 := bstep (se 1 (by rfl) ⟨1652645, by rfl⟩ : syracuseStep 2203527 = 3305291) B3305291
theorem B2478973 : Blo 2203435 2478973 := bbase (se 3 (by rfl) ⟨464807, by rfl⟩ : syracuseStep 2478973 = 929615) (by norm_num)
theorem B3305297 : Blo 2203435 3305297 := bstep (se 2 (by rfl) ⟨1239486, by rfl⟩ : syracuseStep 3305297 = 2478973) B2478973
theorem B2203531 : Blo 2203435 2203531 := bstep (se 1 (by rfl) ⟨1652648, by rfl⟩ : syracuseStep 2203531 = 3305297) B3305297
theorem B7436933 : Blo 2203435 7436933 := bbase (se 4 (by rfl) ⟨697212, by rfl⟩ : syracuseStep 7436933 = 1394425) (by norm_num)
theorem B4957955 : Blo 2203435 4957955 := bstep (se 1 (by rfl) ⟨3718466, by rfl⟩ : syracuseStep 4957955 = 7436933) B7436933
theorem B3305303 : Blo 2203435 3305303 := bstep (se 1 (by rfl) ⟨2478977, by rfl⟩ : syracuseStep 3305303 = 4957955) B4957955
theorem B2203535 : Blo 2203435 2203535 := bstep (se 1 (by rfl) ⟨1652651, by rfl⟩ : syracuseStep 2203535 = 3305303) B3305303
theorem B3305309 : Blo 2203435 3305309 := bbase (se 3 (by rfl) ⟨619745, by rfl⟩ : syracuseStep 3305309 = 1239491) (by norm_num)
theorem B2203539 : Blo 2203435 2203539 := bstep (se 1 (by rfl) ⟨1652654, by rfl⟩ : syracuseStep 2203539 = 3305309) B3305309
theorem B4957973 : Blo 2203435 4957973 := bbase (se 6 (by rfl) ⟨116202, by rfl⟩ : syracuseStep 4957973 = 232405) (by norm_num)
theorem B3305315 : Blo 2203435 3305315 := bstep (se 1 (by rfl) ⟨2478986, by rfl⟩ : syracuseStep 3305315 = 4957973) B4957973
theorem B2203543 : Blo 2203435 2203543 := bstep (se 1 (by rfl) ⟨1652657, by rfl⟩ : syracuseStep 2203543 = 3305315) B3305315
theorem B8366597 : Blo 2203435 8366597 := bbase (se 4 (by rfl) ⟨784368, by rfl⟩ : syracuseStep 8366597 = 1568737) (by norm_num)
theorem B5577731 : Blo 2203435 5577731 := bstep (se 1 (by rfl) ⟨4183298, by rfl⟩ : syracuseStep 5577731 = 8366597) B8366597
theorem B3718487 : Blo 2203435 3718487 := bstep (se 1 (by rfl) ⟨2788865, by rfl⟩ : syracuseStep 3718487 = 5577731) B5577731
theorem B2478991 : Blo 2203435 2478991 := bstep (se 1 (by rfl) ⟨1859243, by rfl⟩ : syracuseStep 2478991 = 3718487) B3718487
theorem B3305321 : Blo 2203435 3305321 := bstep (se 2 (by rfl) ⟨1239495, by rfl⟩ : syracuseStep 3305321 = 2478991) B2478991
theorem B2203547 : Blo 2203435 2203547 := bstep (se 1 (by rfl) ⟨1652660, by rfl⟩ : syracuseStep 2203547 = 3305321) B3305321
theorem B3769229 : Blo 2203435 3769229 := bbase (se 3 (by rfl) ⟨706730, by rfl⟩ : syracuseStep 3769229 = 1413461) (by norm_num)
theorem B2512819 : Blo 2203435 2512819 := bstep (se 1 (by rfl) ⟨1884614, by rfl⟩ : syracuseStep 2512819 = 3769229) B3769229
theorem B3350425 : Blo 2203435 3350425 := bstep (se 2 (by rfl) ⟨1256409, by rfl⟩ : syracuseStep 3350425 = 2512819) B2512819
theorem B4467233 : Blo 2203435 4467233 := bstep (se 2 (by rfl) ⟨1675212, by rfl⟩ : syracuseStep 4467233 = 3350425) B3350425
theorem B2978155 : Blo 2203435 2978155 := bstep (se 1 (by rfl) ⟨2233616, by rfl⟩ : syracuseStep 2978155 = 4467233) B4467233
theorem B3970873 : Blo 2203435 3970873 := bstep (se 2 (by rfl) ⟨1489077, by rfl⟩ : syracuseStep 3970873 = 2978155) B2978155
theorem B5294497 : Blo 2203435 5294497 := bstep (se 2 (by rfl) ⟨1985436, by rfl⟩ : syracuseStep 5294497 = 3970873) B3970873
theorem B7059329 : Blo 2203435 7059329 := bstep (se 2 (by rfl) ⟨2647248, by rfl⟩ : syracuseStep 7059329 = 5294497) B5294497
theorem B4706219 : Blo 2203435 4706219 := bstep (se 1 (by rfl) ⟨3529664, by rfl⟩ : syracuseStep 4706219 = 7059329) B7059329
theorem B12549917 : Blo 2203435 12549917 := bstep (se 3 (by rfl) ⟨2353109, by rfl⟩ : syracuseStep 12549917 = 4706219) B4706219
theorem B8366611 : Blo 2203435 8366611 := bstep (se 1 (by rfl) ⟨6274958, by rfl⟩ : syracuseStep 8366611 = 12549917) B12549917
theorem B11155481 : Blo 2203435 11155481 := bstep (se 2 (by rfl) ⟨4183305, by rfl⟩ : syracuseStep 11155481 = 8366611) B8366611
theorem B7436987 : Blo 2203435 7436987 := bstep (se 1 (by rfl) ⟨5577740, by rfl⟩ : syracuseStep 7436987 = 11155481) B11155481
theorem B4957991 : Blo 2203435 4957991 := bstep (se 1 (by rfl) ⟨3718493, by rfl⟩ : syracuseStep 4957991 = 7436987) B7436987
theorem B3305327 : Blo 2203435 3305327 := bstep (se 1 (by rfl) ⟨2478995, by rfl⟩ : syracuseStep 3305327 = 4957991) B4957991
theorem B2203551 : Blo 2203435 2203551 := bstep (se 1 (by rfl) ⟨1652663, by rfl⟩ : syracuseStep 2203551 = 3305327) B3305327
theorem B3305333 : Blo 2203435 3305333 := bbase (se 5 (by rfl) ⟨154937, by rfl⟩ : syracuseStep 3305333 = 309875) (by norm_num)
theorem B2203555 : Blo 2203435 2203555 := bstep (se 1 (by rfl) ⟨1652666, by rfl⟩ : syracuseStep 2203555 = 3305333) B3305333
theorem B4706237 : Blo 2203435 4706237 := bbase (se 3 (by rfl) ⟨882419, by rfl⟩ : syracuseStep 4706237 = 1764839) (by norm_num)
theorem B3137491 : Blo 2203435 3137491 := bstep (se 1 (by rfl) ⟨2353118, by rfl⟩ : syracuseStep 3137491 = 4706237) B4706237
theorem B4183321 : Blo 2203435 4183321 := bstep (se 2 (by rfl) ⟨1568745, by rfl⟩ : syracuseStep 4183321 = 3137491) B3137491
theorem B5577761 : Blo 2203435 5577761 := bstep (se 2 (by rfl) ⟨2091660, by rfl⟩ : syracuseStep 5577761 = 4183321) B4183321
theorem B3718507 : Blo 2203435 3718507 := bstep (se 1 (by rfl) ⟨2788880, by rfl⟩ : syracuseStep 3718507 = 5577761) B5577761
theorem B4958009 : Blo 2203435 4958009 := bstep (se 2 (by rfl) ⟨1859253, by rfl⟩ : syracuseStep 4958009 = 3718507) B3718507
theorem B3305339 : Blo 2203435 3305339 := bstep (se 1 (by rfl) ⟨2479004, by rfl⟩ : syracuseStep 3305339 = 4958009) B4958009
theorem B2203559 : Blo 2203435 2203559 := bstep (se 1 (by rfl) ⟨1652669, by rfl⟩ : syracuseStep 2203559 = 3305339) B3305339
theorem B2479009 : Blo 2203435 2479009 := bbase (se 2 (by rfl) ⟨929628, by rfl⟩ : syracuseStep 2479009 = 1859257) (by norm_num)
theorem B3305345 : Blo 2203435 3305345 := bstep (se 2 (by rfl) ⟨1239504, by rfl⟩ : syracuseStep 3305345 = 2479009) B2479009
theorem B2203563 : Blo 2203435 2203563 := bstep (se 1 (by rfl) ⟨1652672, by rfl⟩ : syracuseStep 2203563 = 3305345) B3305345
theorem B5577781 : Blo 2203435 5577781 := bbase (se 5 (by rfl) ⟨261458, by rfl⟩ : syracuseStep 5577781 = 522917) (by norm_num)
theorem B7437041 : Blo 2203435 7437041 := bstep (se 2 (by rfl) ⟨2788890, by rfl⟩ : syracuseStep 7437041 = 5577781) B5577781
theorem B4958027 : Blo 2203435 4958027 := bstep (se 1 (by rfl) ⟨3718520, by rfl⟩ : syracuseStep 4958027 = 7437041) B7437041
theorem B3305351 : Blo 2203435 3305351 := bstep (se 1 (by rfl) ⟨2479013, by rfl⟩ : syracuseStep 3305351 = 4958027) B4958027
theorem B2203567 : Blo 2203435 2203567 := bstep (se 1 (by rfl) ⟨1652675, by rfl⟩ : syracuseStep 2203567 = 3305351) B3305351
theorem B3305357 : Blo 2203435 3305357 := bbase (se 3 (by rfl) ⟨619754, by rfl⟩ : syracuseStep 3305357 = 1239509) (by norm_num)
theorem B2203571 : Blo 2203435 2203571 := bstep (se 1 (by rfl) ⟨1652678, by rfl⟩ : syracuseStep 2203571 = 3305357) B3305357
theorem B4958045 : Blo 2203435 4958045 := bbase (se 3 (by rfl) ⟨929633, by rfl⟩ : syracuseStep 4958045 = 1859267) (by norm_num)
theorem B3305363 : Blo 2203435 3305363 := bstep (se 1 (by rfl) ⟨2479022, by rfl⟩ : syracuseStep 3305363 = 4958045) B4958045
theorem B2203575 : Blo 2203435 2203575 := bstep (se 1 (by rfl) ⟨1652681, by rfl⟩ : syracuseStep 2203575 = 3305363) B3305363
theorem B3718541 : Blo 2203435 3718541 := bbase (se 3 (by rfl) ⟨697226, by rfl⟩ : syracuseStep 3718541 = 1394453) (by norm_num)
theorem B2479027 : Blo 2203435 2479027 := bstep (se 1 (by rfl) ⟨1859270, by rfl⟩ : syracuseStep 2479027 = 3718541) B3718541
theorem B3305369 : Blo 2203435 3305369 := bstep (se 2 (by rfl) ⟨1239513, by rfl⟩ : syracuseStep 3305369 = 2479027) B2479027
theorem B2203579 : Blo 2203435 2203579 := bstep (se 1 (by rfl) ⟨1652684, by rfl⟩ : syracuseStep 2203579 = 3305369) B3305369
theorem B5025709 : Blo 2203435 5025709 := bbase (se 3 (by rfl) ⟨942320, by rfl⟩ : syracuseStep 5025709 = 1884641) (by norm_num)
theorem B26803781 : Blo 2203435 26803781 := bstep (se 4 (by rfl) ⟨2512854, by rfl⟩ : syracuseStep 26803781 = 5025709) B5025709
theorem B17869187 : Blo 2203435 17869187 := bstep (se 1 (by rfl) ⟨13401890, by rfl⟩ : syracuseStep 17869187 = 26803781) B26803781
theorem B11912791 : Blo 2203435 11912791 := bstep (se 1 (by rfl) ⟨8934593, by rfl⟩ : syracuseStep 11912791 = 17869187) B17869187
theorem B15883721 : Blo 2203435 15883721 := bstep (se 2 (by rfl) ⟨5956395, by rfl⟩ : syracuseStep 15883721 = 11912791) B11912791
theorem B10589147 : Blo 2203435 10589147 := bstep (se 1 (by rfl) ⟨7941860, by rfl⟩ : syracuseStep 10589147 = 15883721) B15883721
theorem B7059431 : Blo 2203435 7059431 := bstep (se 1 (by rfl) ⟨5294573, by rfl⟩ : syracuseStep 7059431 = 10589147) B10589147
theorem B18825149 : Blo 2203435 18825149 := bstep (se 3 (by rfl) ⟨3529715, by rfl⟩ : syracuseStep 18825149 = 7059431) B7059431
theorem B12550099 : Blo 2203435 12550099 := bstep (se 1 (by rfl) ⟨9412574, by rfl⟩ : syracuseStep 12550099 = 18825149) B18825149
theorem B16733465 : Blo 2203435 16733465 := bstep (se 2 (by rfl) ⟨6275049, by rfl⟩ : syracuseStep 16733465 = 12550099) B12550099
theorem B11155643 : Blo 2203435 11155643 := bstep (se 1 (by rfl) ⟨8366732, by rfl⟩ : syracuseStep 11155643 = 16733465) B16733465
theorem B7437095 : Blo 2203435 7437095 := bstep (se 1 (by rfl) ⟨5577821, by rfl⟩ : syracuseStep 7437095 = 11155643) B11155643
theorem B4958063 : Blo 2203435 4958063 := bstep (se 1 (by rfl) ⟨3718547, by rfl⟩ : syracuseStep 4958063 = 7437095) B7437095
theorem B3305375 : Blo 2203435 3305375 := bstep (se 1 (by rfl) ⟨2479031, by rfl⟩ : syracuseStep 3305375 = 4958063) B4958063
theorem B2203583 : Blo 2203435 2203583 := bstep (se 1 (by rfl) ⟨1652687, by rfl⟩ : syracuseStep 2203583 = 3305375) B3305375
theorem B3305381 : Blo 2203435 3305381 := bbase (se 4 (by rfl) ⟨309879, by rfl⟩ : syracuseStep 3305381 = 619759) (by norm_num)
theorem B2203587 : Blo 2203435 2203587 := bstep (se 1 (by rfl) ⟨1652690, by rfl⟩ : syracuseStep 2203587 = 3305381) B3305381
theorem B2788921 : Blo 2203435 2788921 := bbase (se 2 (by rfl) ⟨1045845, by rfl⟩ : syracuseStep 2788921 = 2091691) (by norm_num)
theorem B3718561 : Blo 2203435 3718561 := bstep (se 2 (by rfl) ⟨1394460, by rfl⟩ : syracuseStep 3718561 = 2788921) B2788921
theorem B4958081 : Blo 2203435 4958081 := bstep (se 2 (by rfl) ⟨1859280, by rfl⟩ : syracuseStep 4958081 = 3718561) B3718561
theorem B3305387 : Blo 2203435 3305387 := bstep (se 1 (by rfl) ⟨2479040, by rfl⟩ : syracuseStep 3305387 = 4958081) B4958081
theorem B2203591 : Blo 2203435 2203591 := bstep (se 1 (by rfl) ⟨1652693, by rfl⟩ : syracuseStep 2203591 = 3305387) B3305387
theorem B2479045 : Blo 2203435 2479045 := bbase (se 4 (by rfl) ⟨232410, by rfl⟩ : syracuseStep 2479045 = 464821) (by norm_num)
theorem B3305393 : Blo 2203435 3305393 := bstep (se 2 (by rfl) ⟨1239522, by rfl⟩ : syracuseStep 3305393 = 2479045) B2479045
theorem B2203595 : Blo 2203435 2203595 := bstep (se 1 (by rfl) ⟨1652696, by rfl⟩ : syracuseStep 2203595 = 3305393) B3305393
theorem B4183397 : Blo 2203435 4183397 := bbase (se 4 (by rfl) ⟨392193, by rfl⟩ : syracuseStep 4183397 = 784387) (by norm_num)
theorem B2788931 : Blo 2203435 2788931 := bstep (se 1 (by rfl) ⟨2091698, by rfl⟩ : syracuseStep 2788931 = 4183397) B4183397
theorem B7437149 : Blo 2203435 7437149 := bstep (se 3 (by rfl) ⟨1394465, by rfl⟩ : syracuseStep 7437149 = 2788931) B2788931
theorem B4958099 : Blo 2203435 4958099 := bstep (se 1 (by rfl) ⟨3718574, by rfl⟩ : syracuseStep 4958099 = 7437149) B7437149
theorem B3305399 : Blo 2203435 3305399 := bstep (se 1 (by rfl) ⟨2479049, by rfl⟩ : syracuseStep 3305399 = 4958099) B4958099
theorem B2203599 : Blo 2203435 2203599 := bstep (se 1 (by rfl) ⟨1652699, by rfl⟩ : syracuseStep 2203599 = 3305399) B3305399
theorem B3305405 : Blo 2203435 3305405 := bbase (se 3 (by rfl) ⟨619763, by rfl⟩ : syracuseStep 3305405 = 1239527) (by norm_num)
theorem B2203603 : Blo 2203435 2203603 := bstep (se 1 (by rfl) ⟨1652702, by rfl⟩ : syracuseStep 2203603 = 3305405) B3305405
theorem B4958117 : Blo 2203435 4958117 := bbase (se 4 (by rfl) ⟨464823, by rfl⟩ : syracuseStep 4958117 = 929647) (by norm_num)
theorem B3305411 : Blo 2203435 3305411 := bstep (se 1 (by rfl) ⟨2479058, by rfl⟩ : syracuseStep 3305411 = 4958117) B4958117
theorem B2203607 : Blo 2203435 2203607 := bstep (se 1 (by rfl) ⟨1652705, by rfl⟩ : syracuseStep 2203607 = 3305411) B3305411
theorem B5577893 : Blo 2203435 5577893 := bbase (se 4 (by rfl) ⟨522927, by rfl⟩ : syracuseStep 5577893 = 1045855) (by norm_num)
theorem B3718595 : Blo 2203435 3718595 := bstep (se 1 (by rfl) ⟨2788946, by rfl⟩ : syracuseStep 3718595 = 5577893) B5577893
theorem B2479063 : Blo 2203435 2479063 := bstep (se 1 (by rfl) ⟨1859297, by rfl⟩ : syracuseStep 2479063 = 3718595) B3718595
theorem B3305417 : Blo 2203435 3305417 := bstep (se 2 (by rfl) ⟨1239531, by rfl⟩ : syracuseStep 3305417 = 2479063) B2479063
theorem B2203611 : Blo 2203435 2203611 := bstep (se 1 (by rfl) ⟨1652708, by rfl⟩ : syracuseStep 2203611 = 3305417) B3305417
theorem B6275141 : Blo 2203435 6275141 := bbase (se 4 (by rfl) ⟨588294, by rfl⟩ : syracuseStep 6275141 = 1176589) (by norm_num)
theorem B4183427 : Blo 2203435 4183427 := bstep (se 1 (by rfl) ⟨3137570, by rfl⟩ : syracuseStep 4183427 = 6275141) B6275141
theorem B11155805 : Blo 2203435 11155805 := bstep (se 3 (by rfl) ⟨2091713, by rfl⟩ : syracuseStep 11155805 = 4183427) B4183427
theorem B7437203 : Blo 2203435 7437203 := bstep (se 1 (by rfl) ⟨5577902, by rfl⟩ : syracuseStep 7437203 = 11155805) B11155805
theorem B4958135 : Blo 2203435 4958135 := bstep (se 1 (by rfl) ⟨3718601, by rfl⟩ : syracuseStep 4958135 = 7437203) B7437203
theorem B3305423 : Blo 2203435 3305423 := bstep (se 1 (by rfl) ⟨2479067, by rfl⟩ : syracuseStep 3305423 = 4958135) B4958135
theorem B2203615 : Blo 2203435 2203615 := bstep (se 1 (by rfl) ⟨1652711, by rfl⟩ : syracuseStep 2203615 = 3305423) B3305423
theorem B3305429 : Blo 2203435 3305429 := bbase (se 7 (by rfl) ⟨38735, by rfl⟩ : syracuseStep 3305429 = 77471) (by norm_num)
theorem B2203619 : Blo 2203435 2203619 := bstep (se 1 (by rfl) ⟨1652714, by rfl⟩ : syracuseStep 2203619 = 3305429) B3305429
theorem B8366885 : Blo 2203435 8366885 := bbase (se 4 (by rfl) ⟨784395, by rfl⟩ : syracuseStep 8366885 = 1568791) (by norm_num)
theorem B5577923 : Blo 2203435 5577923 := bstep (se 1 (by rfl) ⟨4183442, by rfl⟩ : syracuseStep 5577923 = 8366885) B8366885
theorem B3718615 : Blo 2203435 3718615 := bstep (se 1 (by rfl) ⟨2788961, by rfl⟩ : syracuseStep 3718615 = 5577923) B5577923
theorem B4958153 : Blo 2203435 4958153 := bstep (se 2 (by rfl) ⟨1859307, by rfl⟩ : syracuseStep 4958153 = 3718615) B3718615
theorem B3305435 : Blo 2203435 3305435 := bstep (se 1 (by rfl) ⟨2479076, by rfl⟩ : syracuseStep 3305435 = 4958153) B4958153
theorem B2203623 : Blo 2203435 2203623 := bstep (se 1 (by rfl) ⟨1652717, by rfl⟩ : syracuseStep 2203623 = 3305435) B3305435
theorem B2479081 : Blo 2203435 2479081 := bbase (se 2 (by rfl) ⟨929655, by rfl⟩ : syracuseStep 2479081 = 1859311) (by norm_num)
theorem B3305441 : Blo 2203435 3305441 := bstep (se 2 (by rfl) ⟨1239540, by rfl⟩ : syracuseStep 3305441 = 2479081) B2479081
theorem B2203627 : Blo 2203435 2203627 := bstep (se 1 (by rfl) ⟨1652720, by rfl⟩ : syracuseStep 2203627 = 3305441) B3305441
theorem B2647345 : Blo 2203435 2647345 := bbase (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) (by norm_num)
theorem B3529793 : Blo 2203435 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B2353195 : Blo 2203435 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B12550373 : Blo 2203435 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B8366915 : Blo 2203435 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B5577943 : Blo 2203435 5577943 := bstep (se 1 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 5577943 = 8366915) B8366915
theorem B7437257 : Blo 2203435 7437257 := bstep (se 2 (by rfl) ⟨2788971, by rfl⟩ : syracuseStep 7437257 = 5577943) B5577943
theorem B4958171 : Blo 2203435 4958171 := bstep (se 1 (by rfl) ⟨3718628, by rfl⟩ : syracuseStep 4958171 = 7437257) B7437257
theorem B3305447 : Blo 2203435 3305447 := bstep (se 1 (by rfl) ⟨2479085, by rfl⟩ : syracuseStep 3305447 = 4958171) B4958171
theorem B2203631 : Blo 2203435 2203631 := bstep (se 1 (by rfl) ⟨1652723, by rfl⟩ : syracuseStep 2203631 = 3305447) B3305447
theorem B3305453 : Blo 2203435 3305453 := bbase (se 3 (by rfl) ⟨619772, by rfl⟩ : syracuseStep 3305453 = 1239545) (by norm_num)
theorem B2203635 : Blo 2203435 2203635 := bstep (se 1 (by rfl) ⟨1652726, by rfl⟩ : syracuseStep 2203635 = 3305453) B3305453
theorem B4958189 : Blo 2203435 4958189 := bbase (se 3 (by rfl) ⟨929660, by rfl⟩ : syracuseStep 4958189 = 1859321) (by norm_num)
theorem B3305459 : Blo 2203435 3305459 := bstep (se 1 (by rfl) ⟨2479094, by rfl⟩ : syracuseStep 3305459 = 4958189) B4958189
theorem B2203639 : Blo 2203435 2203639 := bstep (se 1 (by rfl) ⟨1652729, by rfl⟩ : syracuseStep 2203639 = 3305459) B3305459
theorem B3529813 : Blo 2203435 3529813 := bbase (se 8 (by rfl) ⟨20682, by rfl⟩ : syracuseStep 3529813 = 41365) (by norm_num)
theorem B4706417 : Blo 2203435 4706417 := bstep (se 2 (by rfl) ⟨1764906, by rfl⟩ : syracuseStep 4706417 = 3529813) B3529813
theorem B3137611 : Blo 2203435 3137611 := bstep (se 1 (by rfl) ⟨2353208, by rfl⟩ : syracuseStep 3137611 = 4706417) B4706417
theorem B4183481 : Blo 2203435 4183481 := bstep (se 2 (by rfl) ⟨1568805, by rfl⟩ : syracuseStep 4183481 = 3137611) B3137611
theorem B2788987 : Blo 2203435 2788987 := bstep (se 1 (by rfl) ⟨2091740, by rfl⟩ : syracuseStep 2788987 = 4183481) B4183481
theorem B3718649 : Blo 2203435 3718649 := bstep (se 2 (by rfl) ⟨1394493, by rfl⟩ : syracuseStep 3718649 = 2788987) B2788987
theorem B2479099 : Blo 2203435 2479099 := bstep (se 1 (by rfl) ⟨1859324, by rfl⟩ : syracuseStep 2479099 = 3718649) B3718649
theorem B3305465 : Blo 2203435 3305465 := bstep (se 2 (by rfl) ⟨1239549, by rfl⟩ : syracuseStep 3305465 = 2479099) B2479099
theorem B2203643 : Blo 2203435 2203643 := bstep (se 1 (by rfl) ⟨1652732, by rfl⟩ : syracuseStep 2203643 = 3305465) B3305465
theorem B2450849 : Blo 2203435 2450849 := bbase (se 2 (by rfl) ⟨919068, by rfl⟩ : syracuseStep 2450849 = 1838137) (by norm_num)
theorem B6535597 : Blo 2203435 6535597 := bstep (se 3 (by rfl) ⟨1225424, by rfl⟩ : syracuseStep 6535597 = 2450849) B2450849
theorem B139426069 : Blo 2203435 139426069 := bstep (se 6 (by rfl) ⟨3267798, by rfl⟩ : syracuseStep 139426069 = 6535597) B6535597
theorem B185901425 : Blo 2203435 185901425 := bstep (se 2 (by rfl) ⟨69713034, by rfl⟩ : syracuseStep 185901425 = 139426069) B139426069
theorem B123934283 : Blo 2203435 123934283 := bstep (se 1 (by rfl) ⟨92950712, by rfl⟩ : syracuseStep 123934283 = 185901425) B185901425
theorem B82622855 : Blo 2203435 82622855 := bstep (se 1 (by rfl) ⟨61967141, by rfl⟩ : syracuseStep 82622855 = 123934283) B123934283
theorem B55081903 : Blo 2203435 55081903 := bstep (se 1 (by rfl) ⟨41311427, by rfl⟩ : syracuseStep 55081903 = 82622855) B82622855
theorem B73442537 : Blo 2203435 73442537 := bstep (se 2 (by rfl) ⟨27540951, by rfl⟩ : syracuseStep 73442537 = 55081903) B55081903
theorem B48961691 : Blo 2203435 48961691 := bstep (se 1 (by rfl) ⟨36721268, by rfl⟩ : syracuseStep 48961691 = 73442537) B73442537
theorem B32641127 : Blo 2203435 32641127 := bstep (se 1 (by rfl) ⟨24480845, by rfl⟩ : syracuseStep 32641127 = 48961691) B48961691
theorem B21760751 : Blo 2203435 21760751 := bstep (se 1 (by rfl) ⟨16320563, by rfl⟩ : syracuseStep 21760751 = 32641127) B32641127
theorem B14507167 : Blo 2203435 14507167 := bstep (se 1 (by rfl) ⟨10880375, by rfl⟩ : syracuseStep 14507167 = 21760751) B21760751
theorem B19342889 : Blo 2203435 19342889 := bstep (se 2 (by rfl) ⟨7253583, by rfl⟩ : syracuseStep 19342889 = 14507167) B14507167
theorem B12895259 : Blo 2203435 12895259 := bstep (se 1 (by rfl) ⟨9671444, by rfl⟩ : syracuseStep 12895259 = 19342889) B19342889
theorem B137549429 : Blo 2203435 137549429 := bstep (se 5 (by rfl) ⟨6447629, by rfl⟩ : syracuseStep 137549429 = 12895259) B12895259
theorem B91699619 : Blo 2203435 91699619 := bstep (se 1 (by rfl) ⟨68774714, by rfl⟩ : syracuseStep 91699619 = 137549429) B137549429
theorem B244532317 : Blo 2203435 244532317 := bstep (se 3 (by rfl) ⟨45849809, by rfl⟩ : syracuseStep 244532317 = 91699619) B91699619
theorem B326043089 : Blo 2203435 326043089 := bstep (se 2 (by rfl) ⟨122266158, by rfl⟩ : syracuseStep 326043089 = 244532317) B244532317
theorem B217362059 : Blo 2203435 217362059 := bstep (se 1 (by rfl) ⟨163021544, by rfl⟩ : syracuseStep 217362059 = 326043089) B326043089
theorem B144908039 : Blo 2203435 144908039 := bstep (se 1 (by rfl) ⟨108681029, by rfl⟩ : syracuseStep 144908039 = 217362059) B217362059
theorem B386421437 : Blo 2203435 386421437 := bstep (se 3 (by rfl) ⟨72454019, by rfl⟩ : syracuseStep 386421437 = 144908039) B144908039
theorem B257614291 : Blo 2203435 257614291 := bstep (se 1 (by rfl) ⟨193210718, by rfl⟩ : syracuseStep 257614291 = 386421437) B386421437
theorem B343485721 : Blo 2203435 343485721 := bstep (se 2 (by rfl) ⟨128807145, by rfl⟩ : syracuseStep 343485721 = 257614291) B257614291
theorem B457980961 : Blo 2203435 457980961 := bstep (se 2 (by rfl) ⟨171742860, by rfl⟩ : syracuseStep 457980961 = 343485721) B343485721
theorem B610641281 : Blo 2203435 610641281 := bstep (se 2 (by rfl) ⟨228990480, by rfl⟩ : syracuseStep 610641281 = 457980961) B457980961
theorem B407094187 : Blo 2203435 407094187 := bstep (se 1 (by rfl) ⟨305320640, by rfl⟩ : syracuseStep 407094187 = 610641281) B610641281
theorem B542792249 : Blo 2203435 542792249 := bstep (se 2 (by rfl) ⟨203547093, by rfl⟩ : syracuseStep 542792249 = 407094187) B407094187
theorem B361861499 : Blo 2203435 361861499 := bstep (se 1 (by rfl) ⟨271396124, by rfl⟩ : syracuseStep 361861499 = 542792249) B542792249
theorem B241240999 : Blo 2203435 241240999 := bstep (se 1 (by rfl) ⟨180930749, by rfl⟩ : syracuseStep 241240999 = 361861499) B361861499
theorem B321654665 : Blo 2203435 321654665 := bstep (se 2 (by rfl) ⟨120620499, by rfl⟩ : syracuseStep 321654665 = 241240999) B241240999
theorem B214436443 : Blo 2203435 214436443 := bstep (se 1 (by rfl) ⟨160827332, by rfl⟩ : syracuseStep 214436443 = 321654665) B321654665
theorem B285915257 : Blo 2203435 285915257 := bstep (se 2 (by rfl) ⟨107218221, by rfl⟩ : syracuseStep 285915257 = 214436443) B214436443
theorem B190610171 : Blo 2203435 190610171 := bstep (se 1 (by rfl) ⟨142957628, by rfl⟩ : syracuseStep 190610171 = 285915257) B285915257
theorem B127073447 : Blo 2203435 127073447 := bstep (se 1 (by rfl) ⟨95305085, by rfl⟩ : syracuseStep 127073447 = 190610171) B190610171
theorem B84715631 : Blo 2203435 84715631 := bstep (se 1 (by rfl) ⟨63536723, by rfl⟩ : syracuseStep 84715631 = 127073447) B127073447
theorem B56477087 : Blo 2203435 56477087 := bstep (se 1 (by rfl) ⟨42357815, by rfl⟩ : syracuseStep 56477087 = 84715631) B84715631
theorem B37651391 : Blo 2203435 37651391 := bstep (se 1 (by rfl) ⟨28238543, by rfl⟩ : syracuseStep 37651391 = 56477087) B56477087
theorem B25100927 : Blo 2203435 25100927 := bstep (se 1 (by rfl) ⟨18825695, by rfl⟩ : syracuseStep 25100927 = 37651391) B37651391
theorem B16733951 : Blo 2203435 16733951 := bstep (se 1 (by rfl) ⟨12550463, by rfl⟩ : syracuseStep 16733951 = 25100927) B25100927
theorem B11155967 : Blo 2203435 11155967 := bstep (se 1 (by rfl) ⟨8366975, by rfl⟩ : syracuseStep 11155967 = 16733951) B16733951
theorem B7437311 : Blo 2203435 7437311 := bstep (se 1 (by rfl) ⟨5577983, by rfl⟩ : syracuseStep 7437311 = 11155967) B11155967
theorem B4958207 : Blo 2203435 4958207 := bstep (se 1 (by rfl) ⟨3718655, by rfl⟩ : syracuseStep 4958207 = 7437311) B7437311
theorem B3305471 : Blo 2203435 3305471 := bstep (se 1 (by rfl) ⟨2479103, by rfl⟩ : syracuseStep 3305471 = 4958207) B4958207
theorem B2203647 : Blo 2203435 2203647 := bstep (se 1 (by rfl) ⟨1652735, by rfl⟩ : syracuseStep 2203647 = 3305471) B3305471
theorem B3305477 : Blo 2203435 3305477 := bbase (se 4 (by rfl) ⟨309888, by rfl⟩ : syracuseStep 3305477 = 619777) (by norm_num)
theorem B2203651 : Blo 2203435 2203651 := bstep (se 1 (by rfl) ⟨1652738, by rfl⟩ : syracuseStep 2203651 = 3305477) B3305477
theorem B3718669 : Blo 2203435 3718669 := bbase (se 3 (by rfl) ⟨697250, by rfl⟩ : syracuseStep 3718669 = 1394501) (by norm_num)
theorem B4958225 : Blo 2203435 4958225 := bstep (se 2 (by rfl) ⟨1859334, by rfl⟩ : syracuseStep 4958225 = 3718669) B3718669
theorem B3305483 : Blo 2203435 3305483 := bstep (se 1 (by rfl) ⟨2479112, by rfl⟩ : syracuseStep 3305483 = 4958225) B4958225
theorem B2203655 : Blo 2203435 2203655 := bstep (se 1 (by rfl) ⟨1652741, by rfl⟩ : syracuseStep 2203655 = 3305483) B3305483
theorem B2479117 : Blo 2203435 2479117 := bbase (se 3 (by rfl) ⟨464834, by rfl⟩ : syracuseStep 2479117 = 929669) (by norm_num)
theorem B3305489 : Blo 2203435 3305489 := bstep (se 2 (by rfl) ⟨1239558, by rfl⟩ : syracuseStep 3305489 = 2479117) B2479117
theorem B2203659 : Blo 2203435 2203659 := bstep (se 1 (by rfl) ⟨1652744, by rfl⟩ : syracuseStep 2203659 = 3305489) B3305489
theorem B7437365 : Blo 2203435 7437365 := bbase (se 5 (by rfl) ⟨348626, by rfl⟩ : syracuseStep 7437365 = 697253) (by norm_num)
theorem B4958243 : Blo 2203435 4958243 := bstep (se 1 (by rfl) ⟨3718682, by rfl⟩ : syracuseStep 4958243 = 7437365) B7437365
theorem B3305495 : Blo 2203435 3305495 := bstep (se 1 (by rfl) ⟨2479121, by rfl⟩ : syracuseStep 3305495 = 4958243) B4958243
theorem B2203663 : Blo 2203435 2203663 := bstep (se 1 (by rfl) ⟨1652747, by rfl⟩ : syracuseStep 2203663 = 3305495) B3305495
theorem B3305501 : Blo 2203435 3305501 := bbase (se 3 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 3305501 = 1239563) (by norm_num)
theorem B2203667 : Blo 2203435 2203667 := bstep (se 1 (by rfl) ⟨1652750, by rfl⟩ : syracuseStep 2203667 = 3305501) B3305501
theorem B4958261 : Blo 2203435 4958261 := bbase (se 5 (by rfl) ⟨232418, by rfl⟩ : syracuseStep 4958261 = 464837) (by norm_num)
theorem B3305507 : Blo 2203435 3305507 := bstep (se 1 (by rfl) ⟨2479130, by rfl⟩ : syracuseStep 3305507 = 4958261) B4958261
theorem B2203671 : Blo 2203435 2203671 := bstep (se 1 (by rfl) ⟨1652753, by rfl⟩ : syracuseStep 2203671 = 3305507) B3305507
theorem B23826581 : Blo 2203435 23826581 := bbase (se 6 (by rfl) ⟨558435, by rfl⟩ : syracuseStep 23826581 = 1116871) (by norm_num)
theorem B15884387 : Blo 2203435 15884387 := bstep (se 1 (by rfl) ⟨11913290, by rfl⟩ : syracuseStep 15884387 = 23826581) B23826581
theorem B10589591 : Blo 2203435 10589591 := bstep (se 1 (by rfl) ⟨7942193, by rfl⟩ : syracuseStep 10589591 = 15884387) B15884387
theorem B7059727 : Blo 2203435 7059727 := bstep (se 1 (by rfl) ⟨5294795, by rfl⟩ : syracuseStep 7059727 = 10589591) B10589591
theorem B9412969 : Blo 2203435 9412969 := bstep (se 2 (by rfl) ⟨3529863, by rfl⟩ : syracuseStep 9412969 = 7059727) B7059727
theorem B12550625 : Blo 2203435 12550625 := bstep (se 2 (by rfl) ⟨4706484, by rfl⟩ : syracuseStep 12550625 = 9412969) B9412969
theorem B8367083 : Blo 2203435 8367083 := bstep (se 1 (by rfl) ⟨6275312, by rfl⟩ : syracuseStep 8367083 = 12550625) B12550625
theorem B5578055 : Blo 2203435 5578055 := bstep (se 1 (by rfl) ⟨4183541, by rfl⟩ : syracuseStep 5578055 = 8367083) B8367083
theorem B3718703 : Blo 2203435 3718703 := bstep (se 1 (by rfl) ⟨2789027, by rfl⟩ : syracuseStep 3718703 = 5578055) B5578055
theorem B2479135 : Blo 2203435 2479135 := bstep (se 1 (by rfl) ⟨1859351, by rfl⟩ : syracuseStep 2479135 = 3718703) B3718703
theorem B3305513 : Blo 2203435 3305513 := bstep (se 2 (by rfl) ⟨1239567, by rfl⟩ : syracuseStep 3305513 = 2479135) B2479135
theorem B2203675 : Blo 2203435 2203675 := bstep (se 1 (by rfl) ⟨1652756, by rfl⟩ : syracuseStep 2203675 = 3305513) B3305513
theorem B2385353 : Blo 2203435 2385353 := bbase (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) (by norm_num)
theorem B6360941 : Blo 2203435 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B16962509 : Blo 2203435 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B11308339 : Blo 2203435 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B60311141 : Blo 2203435 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B40207427 : Blo 2203435 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B26804951 : Blo 2203435 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B17869967 : Blo 2203435 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B11913311 : Blo 2203435 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B7942207 : Blo 2203435 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B10589609 : Blo 2203435 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B7059739 : Blo 2203435 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B9412985 : Blo 2203435 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B6275323 : Blo 2203435 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B8367097 : Blo 2203435 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B11156129 : Blo 2203435 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B7437419 : Blo 2203435 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B4958279 : Blo 2203435 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B3305519 : Blo 2203435 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B2203679 : Blo 2203435 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B3305525 : Blo 2203435 3305525 := bbase (se 5 (by rfl) ⟨154946, by rfl⟩ : syracuseStep 3305525 = 309893) (by norm_num)
theorem B2203683 : Blo 2203435 2203683 := bstep (se 1 (by rfl) ⟨1652762, by rfl⟩ : syracuseStep 2203683 = 3305525) B3305525
theorem B5578085 : Blo 2203435 5578085 := bbase (se 4 (by rfl) ⟨522945, by rfl⟩ : syracuseStep 5578085 = 1045891) (by norm_num)
theorem B3718723 : Blo 2203435 3718723 := bstep (se 1 (by rfl) ⟨2789042, by rfl⟩ : syracuseStep 3718723 = 5578085) B5578085
theorem B4958297 : Blo 2203435 4958297 := bstep (se 2 (by rfl) ⟨1859361, by rfl⟩ : syracuseStep 4958297 = 3718723) B3718723
theorem B3305531 : Blo 2203435 3305531 := bstep (se 1 (by rfl) ⟨2479148, by rfl⟩ : syracuseStep 3305531 = 4958297) B4958297
theorem B2203687 : Blo 2203435 2203687 := bstep (se 1 (by rfl) ⟨1652765, by rfl⟩ : syracuseStep 2203687 = 3305531) B3305531
theorem B2479153 : Blo 2203435 2479153 := bbase (se 2 (by rfl) ⟨929682, by rfl⟩ : syracuseStep 2479153 = 1859365) (by norm_num)
theorem B3305537 : Blo 2203435 3305537 := bstep (se 2 (by rfl) ⟨1239576, by rfl⟩ : syracuseStep 3305537 = 2479153) B2479153
theorem B2203691 : Blo 2203435 2203691 := bstep (se 1 (by rfl) ⟨1652768, by rfl⟩ : syracuseStep 2203691 = 3305537) B3305537
theorem B19082965 : Blo 2203435 19082965 := bbase (se 7 (by rfl) ⟨223628, by rfl⟩ : syracuseStep 19082965 = 447257) (by norm_num)
theorem B25443953 : Blo 2203435 25443953 := bstep (se 2 (by rfl) ⟨9541482, by rfl⟩ : syracuseStep 25443953 = 19082965) B19082965
theorem B16962635 : Blo 2203435 16962635 := bstep (se 1 (by rfl) ⟨12721976, by rfl⟩ : syracuseStep 16962635 = 25443953) B25443953
theorem B11308423 : Blo 2203435 11308423 := bstep (se 1 (by rfl) ⟨8481317, by rfl⟩ : syracuseStep 11308423 = 16962635) B16962635
theorem B15077897 : Blo 2203435 15077897 := bstep (se 2 (by rfl) ⟨5654211, by rfl⟩ : syracuseStep 15077897 = 11308423) B11308423
theorem B10051931 : Blo 2203435 10051931 := bstep (se 1 (by rfl) ⟨7538948, by rfl⟩ : syracuseStep 10051931 = 15077897) B15077897
theorem B6701287 : Blo 2203435 6701287 := bstep (se 1 (by rfl) ⟨5025965, by rfl⟩ : syracuseStep 6701287 = 10051931) B10051931
theorem B8935049 : Blo 2203435 8935049 := bstep (se 2 (by rfl) ⟨3350643, by rfl⟩ : syracuseStep 8935049 = 6701287) B6701287
theorem B23826797 : Blo 2203435 23826797 := bstep (se 3 (by rfl) ⟨4467524, by rfl⟩ : syracuseStep 23826797 = 8935049) B8935049
theorem B15884531 : Blo 2203435 15884531 := bstep (se 1 (by rfl) ⟨11913398, by rfl⟩ : syracuseStep 15884531 = 23826797) B23826797
theorem B10589687 : Blo 2203435 10589687 := bstep (se 1 (by rfl) ⟨7942265, by rfl⟩ : syracuseStep 10589687 = 15884531) B15884531
theorem B7059791 : Blo 2203435 7059791 := bstep (se 1 (by rfl) ⟨5294843, by rfl⟩ : syracuseStep 7059791 = 10589687) B10589687
theorem B4706527 : Blo 2203435 4706527 := bstep (se 1 (by rfl) ⟨3529895, by rfl⟩ : syracuseStep 4706527 = 7059791) B7059791
theorem B6275369 : Blo 2203435 6275369 := bstep (se 2 (by rfl) ⟨2353263, by rfl⟩ : syracuseStep 6275369 = 4706527) B4706527
theorem B4183579 : Blo 2203435 4183579 := bstep (se 1 (by rfl) ⟨3137684, by rfl⟩ : syracuseStep 4183579 = 6275369) B6275369
theorem B5578105 : Blo 2203435 5578105 := bstep (se 2 (by rfl) ⟨2091789, by rfl⟩ : syracuseStep 5578105 = 4183579) B4183579
theorem B7437473 : Blo 2203435 7437473 := bstep (se 2 (by rfl) ⟨2789052, by rfl⟩ : syracuseStep 7437473 = 5578105) B5578105
theorem B4958315 : Blo 2203435 4958315 := bstep (se 1 (by rfl) ⟨3718736, by rfl⟩ : syracuseStep 4958315 = 7437473) B7437473
theorem B3305543 : Blo 2203435 3305543 := bstep (se 1 (by rfl) ⟨2479157, by rfl⟩ : syracuseStep 3305543 = 4958315) B4958315
theorem B2203695 : Blo 2203435 2203695 := bstep (se 1 (by rfl) ⟨1652771, by rfl⟩ : syracuseStep 2203695 = 3305543) B3305543
theorem B3305549 : Blo 2203435 3305549 := bbase (se 3 (by rfl) ⟨619790, by rfl⟩ : syracuseStep 3305549 = 1239581) (by norm_num)
theorem B2203699 : Blo 2203435 2203699 := bstep (se 1 (by rfl) ⟨1652774, by rfl⟩ : syracuseStep 2203699 = 3305549) B3305549
theorem B4958333 : Blo 2203435 4958333 := bbase (se 3 (by rfl) ⟨929687, by rfl⟩ : syracuseStep 4958333 = 1859375) (by norm_num)
theorem B3305555 : Blo 2203435 3305555 := bstep (se 1 (by rfl) ⟨2479166, by rfl⟩ : syracuseStep 3305555 = 4958333) B4958333
theorem B2203703 : Blo 2203435 2203703 := bstep (se 1 (by rfl) ⟨1652777, by rfl⟩ : syracuseStep 2203703 = 3305555) B3305555
theorem B3718757 : Blo 2203435 3718757 := bbase (se 4 (by rfl) ⟨348633, by rfl⟩ : syracuseStep 3718757 = 697267) (by norm_num)
theorem B2479171 : Blo 2203435 2479171 := bstep (se 1 (by rfl) ⟨1859378, by rfl⟩ : syracuseStep 2479171 = 3718757) B3718757
theorem B3305561 : Blo 2203435 3305561 := bstep (se 2 (by rfl) ⟨1239585, by rfl⟩ : syracuseStep 3305561 = 2479171) B2479171
theorem B2203707 : Blo 2203435 2203707 := bstep (se 1 (by rfl) ⟨1652780, by rfl⟩ : syracuseStep 2203707 = 3305561) B3305561
theorem B2647441 : Blo 2203435 2647441 := bbase (se 2 (by rfl) ⟨992790, by rfl⟩ : syracuseStep 2647441 = 1985581) (by norm_num)
theorem B3529921 : Blo 2203435 3529921 := bstep (se 2 (by rfl) ⟨1323720, by rfl⟩ : syracuseStep 3529921 = 2647441) B2647441
theorem B4706561 : Blo 2203435 4706561 := bstep (se 2 (by rfl) ⟨1764960, by rfl⟩ : syracuseStep 4706561 = 3529921) B3529921
theorem B3137707 : Blo 2203435 3137707 := bstep (se 1 (by rfl) ⟨2353280, by rfl⟩ : syracuseStep 3137707 = 4706561) B4706561
theorem B16734437 : Blo 2203435 16734437 := bstep (se 4 (by rfl) ⟨1568853, by rfl⟩ : syracuseStep 16734437 = 3137707) B3137707
theorem B11156291 : Blo 2203435 11156291 := bstep (se 1 (by rfl) ⟨8367218, by rfl⟩ : syracuseStep 11156291 = 16734437) B16734437
theorem B7437527 : Blo 2203435 7437527 := bstep (se 1 (by rfl) ⟨5578145, by rfl⟩ : syracuseStep 7437527 = 11156291) B11156291
theorem B4958351 : Blo 2203435 4958351 := bstep (se 1 (by rfl) ⟨3718763, by rfl⟩ : syracuseStep 4958351 = 7437527) B7437527
theorem B3305567 : Blo 2203435 3305567 := bstep (se 1 (by rfl) ⟨2479175, by rfl⟩ : syracuseStep 3305567 = 4958351) B4958351
theorem B2203711 : Blo 2203435 2203711 := bstep (se 1 (by rfl) ⟨1652783, by rfl⟩ : syracuseStep 2203711 = 3305567) B3305567
theorem B3305573 : Blo 2203435 3305573 := bbase (se 4 (by rfl) ⟨309897, by rfl⟩ : syracuseStep 3305573 = 619795) (by norm_num)
theorem B2203715 : Blo 2203435 2203715 := bstep (se 1 (by rfl) ⟨1652786, by rfl⟩ : syracuseStep 2203715 = 3305573) B3305573
theorem B3769517 : Blo 2203435 3769517 := bbase (se 3 (by rfl) ⟨706784, by rfl⟩ : syracuseStep 3769517 = 1413569) (by norm_num)
theorem B10052045 : Blo 2203435 10052045 := bstep (se 3 (by rfl) ⟨1884758, by rfl⟩ : syracuseStep 10052045 = 3769517) B3769517
theorem B6701363 : Blo 2203435 6701363 := bstep (se 1 (by rfl) ⟨5026022, by rfl⟩ : syracuseStep 6701363 = 10052045) B10052045
theorem B4467575 : Blo 2203435 4467575 := bstep (se 1 (by rfl) ⟨3350681, by rfl⟩ : syracuseStep 4467575 = 6701363) B6701363
theorem B2978383 : Blo 2203435 2978383 := bstep (se 1 (by rfl) ⟨2233787, by rfl⟩ : syracuseStep 2978383 = 4467575) B4467575
theorem B3971177 : Blo 2203435 3971177 := bstep (se 2 (by rfl) ⟨1489191, by rfl⟩ : syracuseStep 3971177 = 2978383) B2978383
theorem B2647451 : Blo 2203435 2647451 := bstep (se 1 (by rfl) ⟨1985588, by rfl⟩ : syracuseStep 2647451 = 3971177) B3971177
theorem B7059869 : Blo 2203435 7059869 := bstep (se 3 (by rfl) ⟨1323725, by rfl⟩ : syracuseStep 7059869 = 2647451) B2647451
theorem B4706579 : Blo 2203435 4706579 := bstep (se 1 (by rfl) ⟨3529934, by rfl⟩ : syracuseStep 4706579 = 7059869) B7059869
theorem B3137719 : Blo 2203435 3137719 := bstep (se 1 (by rfl) ⟨2353289, by rfl⟩ : syracuseStep 3137719 = 4706579) B4706579
theorem B4183625 : Blo 2203435 4183625 := bstep (se 2 (by rfl) ⟨1568859, by rfl⟩ : syracuseStep 4183625 = 3137719) B3137719
theorem B2789083 : Blo 2203435 2789083 := bstep (se 1 (by rfl) ⟨2091812, by rfl⟩ : syracuseStep 2789083 = 4183625) B4183625
theorem B3718777 : Blo 2203435 3718777 := bstep (se 2 (by rfl) ⟨1394541, by rfl⟩ : syracuseStep 3718777 = 2789083) B2789083
theorem B4958369 : Blo 2203435 4958369 := bstep (se 2 (by rfl) ⟨1859388, by rfl⟩ : syracuseStep 4958369 = 3718777) B3718777
theorem B3305579 : Blo 2203435 3305579 := bstep (se 1 (by rfl) ⟨2479184, by rfl⟩ : syracuseStep 3305579 = 4958369) B4958369
theorem B2203719 : Blo 2203435 2203719 := bstep (se 1 (by rfl) ⟨1652789, by rfl⟩ : syracuseStep 2203719 = 3305579) B3305579
theorem B2479189 : Blo 2203435 2479189 := bbase (se 8 (by rfl) ⟨14526, by rfl⟩ : syracuseStep 2479189 = 29053) (by norm_num)
theorem B3305585 : Blo 2203435 3305585 := bstep (se 2 (by rfl) ⟨1239594, by rfl⟩ : syracuseStep 3305585 = 2479189) B2479189
theorem B2203723 : Blo 2203435 2203723 := bstep (se 1 (by rfl) ⟨1652792, by rfl⟩ : syracuseStep 2203723 = 3305585) B3305585
theorem B2789093 : Blo 2203435 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B7437581 : Blo 2203435 7437581 := bstep (se 3 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 7437581 = 2789093) B2789093
theorem B4958387 : Blo 2203435 4958387 := bstep (se 1 (by rfl) ⟨3718790, by rfl⟩ : syracuseStep 4958387 = 7437581) B7437581
theorem B3305591 : Blo 2203435 3305591 := bstep (se 1 (by rfl) ⟨2479193, by rfl⟩ : syracuseStep 3305591 = 4958387) B4958387
theorem B2203727 : Blo 2203435 2203727 := bstep (se 1 (by rfl) ⟨1652795, by rfl⟩ : syracuseStep 2203727 = 3305591) B3305591
theorem B3305597 : Blo 2203435 3305597 := bbase (se 3 (by rfl) ⟨619799, by rfl⟩ : syracuseStep 3305597 = 1239599) (by norm_num)
theorem B2203731 : Blo 2203435 2203731 := bstep (se 1 (by rfl) ⟨1652798, by rfl⟩ : syracuseStep 2203731 = 3305597) B3305597
theorem B4958405 : Blo 2203435 4958405 := bbase (se 4 (by rfl) ⟨464850, by rfl⟩ : syracuseStep 4958405 = 929701) (by norm_num)
theorem B3305603 : Blo 2203435 3305603 := bstep (se 1 (by rfl) ⟨2479202, by rfl⟩ : syracuseStep 3305603 = 4958405) B4958405
theorem B2203735 : Blo 2203435 2203735 := bstep (se 1 (by rfl) ⟨1652801, by rfl⟩ : syracuseStep 2203735 = 3305603) B3305603
theorem B10734389 : Blo 2203435 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B7156259 : Blo 2203435 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B4770839 : Blo 2203435 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B3180559 : Blo 2203435 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B4240745 : Blo 2203435 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B2827163 : Blo 2203435 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B7539101 : Blo 2203435 7539101 := bstep (se 3 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 7539101 = 2827163) B2827163
theorem B5026067 : Blo 2203435 5026067 := bstep (se 1 (by rfl) ⟨3769550, by rfl⟩ : syracuseStep 5026067 = 7539101) B7539101
theorem B3350711 : Blo 2203435 3350711 := bstep (se 1 (by rfl) ⟨2513033, by rfl⟩ : syracuseStep 3350711 = 5026067) B5026067
theorem B2233807 : Blo 2203435 2233807 := bstep (se 1 (by rfl) ⟨1675355, by rfl⟩ : syracuseStep 2233807 = 3350711) B3350711
theorem B11913637 : Blo 2203435 11913637 := bstep (se 4 (by rfl) ⟨1116903, by rfl⟩ : syracuseStep 11913637 = 2233807) B2233807
theorem B15884849 : Blo 2203435 15884849 := bstep (se 2 (by rfl) ⟨5956818, by rfl⟩ : syracuseStep 15884849 = 11913637) B11913637
theorem B10589899 : Blo 2203435 10589899 := bstep (se 1 (by rfl) ⟨7942424, by rfl⟩ : syracuseStep 10589899 = 15884849) B15884849
theorem B14119865 : Blo 2203435 14119865 := bstep (se 2 (by rfl) ⟨5294949, by rfl⟩ : syracuseStep 14119865 = 10589899) B10589899
theorem B9413243 : Blo 2203435 9413243 := bstep (se 1 (by rfl) ⟨7059932, by rfl⟩ : syracuseStep 9413243 = 14119865) B14119865
theorem B6275495 : Blo 2203435 6275495 := bstep (se 1 (by rfl) ⟨4706621, by rfl⟩ : syracuseStep 6275495 = 9413243) B9413243
theorem B4183663 : Blo 2203435 4183663 := bstep (se 1 (by rfl) ⟨3137747, by rfl⟩ : syracuseStep 4183663 = 6275495) B6275495
theorem B5578217 : Blo 2203435 5578217 := bstep (se 2 (by rfl) ⟨2091831, by rfl⟩ : syracuseStep 5578217 = 4183663) B4183663
theorem B3718811 : Blo 2203435 3718811 := bstep (se 1 (by rfl) ⟨2789108, by rfl⟩ : syracuseStep 3718811 = 5578217) B5578217
theorem B2479207 : Blo 2203435 2479207 := bstep (se 1 (by rfl) ⟨1859405, by rfl⟩ : syracuseStep 2479207 = 3718811) B3718811
theorem B3305609 : Blo 2203435 3305609 := bstep (se 2 (by rfl) ⟨1239603, by rfl⟩ : syracuseStep 3305609 = 2479207) B2479207
theorem B2203739 : Blo 2203435 2203739 := bstep (se 1 (by rfl) ⟨1652804, by rfl⟩ : syracuseStep 2203739 = 3305609) B3305609
theorem B11156453 : Blo 2203435 11156453 := bbase (se 4 (by rfl) ⟨1045917, by rfl⟩ : syracuseStep 11156453 = 2091835) (by norm_num)
theorem B7437635 : Blo 2203435 7437635 := bstep (se 1 (by rfl) ⟨5578226, by rfl⟩ : syracuseStep 7437635 = 11156453) B11156453
theorem B4958423 : Blo 2203435 4958423 := bstep (se 1 (by rfl) ⟨3718817, by rfl⟩ : syracuseStep 4958423 = 7437635) B7437635
theorem B3305615 : Blo 2203435 3305615 := bstep (se 1 (by rfl) ⟨2479211, by rfl⟩ : syracuseStep 3305615 = 4958423) B4958423
theorem B2203743 : Blo 2203435 2203743 := bstep (se 1 (by rfl) ⟨1652807, by rfl⟩ : syracuseStep 2203743 = 3305615) B3305615
theorem B3305621 : Blo 2203435 3305621 := bbase (se 6 (by rfl) ⟨77475, by rfl⟩ : syracuseStep 3305621 = 154951) (by norm_num)
theorem B2203747 : Blo 2203435 2203747 := bstep (se 1 (by rfl) ⟨1652810, by rfl⟩ : syracuseStep 2203747 = 3305621) B3305621
theorem B2647489 : Blo 2203435 2647489 := bbase (se 2 (by rfl) ⟨992808, by rfl⟩ : syracuseStep 2647489 = 1985617) (by norm_num)
theorem B3529985 : Blo 2203435 3529985 := bstep (se 2 (by rfl) ⟨1323744, by rfl⟩ : syracuseStep 3529985 = 2647489) B2647489
theorem B9413293 : Blo 2203435 9413293 := bstep (se 3 (by rfl) ⟨1764992, by rfl⟩ : syracuseStep 9413293 = 3529985) B3529985
theorem B12551057 : Blo 2203435 12551057 := bstep (se 2 (by rfl) ⟨4706646, by rfl⟩ : syracuseStep 12551057 = 9413293) B9413293
theorem B8367371 : Blo 2203435 8367371 := bstep (se 1 (by rfl) ⟨6275528, by rfl⟩ : syracuseStep 8367371 = 12551057) B12551057
theorem B5578247 : Blo 2203435 5578247 := bstep (se 1 (by rfl) ⟨4183685, by rfl⟩ : syracuseStep 5578247 = 8367371) B8367371
theorem B3718831 : Blo 2203435 3718831 := bstep (se 1 (by rfl) ⟨2789123, by rfl⟩ : syracuseStep 3718831 = 5578247) B5578247
theorem B4958441 : Blo 2203435 4958441 := bstep (se 2 (by rfl) ⟨1859415, by rfl⟩ : syracuseStep 4958441 = 3718831) B3718831
theorem B3305627 : Blo 2203435 3305627 := bstep (se 1 (by rfl) ⟨2479220, by rfl⟩ : syracuseStep 3305627 = 4958441) B4958441
theorem B2203751 : Blo 2203435 2203751 := bstep (se 1 (by rfl) ⟨1652813, by rfl⟩ : syracuseStep 2203751 = 3305627) B3305627
theorem B2479225 : Blo 2203435 2479225 := bbase (se 2 (by rfl) ⟨929709, by rfl⟩ : syracuseStep 2479225 = 1859419) (by norm_num)
theorem B3305633 : Blo 2203435 3305633 := bstep (se 2 (by rfl) ⟨1239612, by rfl⟩ : syracuseStep 3305633 = 2479225) B2479225
theorem B2203755 : Blo 2203435 2203755 := bstep (se 1 (by rfl) ⟨1652816, by rfl⟩ : syracuseStep 2203755 = 3305633) B3305633
theorem B7253957 : Blo 2203435 7253957 := bbase (se 4 (by rfl) ⟨680058, by rfl⟩ : syracuseStep 7253957 = 1360117) (by norm_num)
theorem B4835971 : Blo 2203435 4835971 := bstep (se 1 (by rfl) ⟨3626978, by rfl⟩ : syracuseStep 4835971 = 7253957) B7253957
theorem B6447961 : Blo 2203435 6447961 := bstep (se 2 (by rfl) ⟨2417985, by rfl⟩ : syracuseStep 6447961 = 4835971) B4835971
theorem B8597281 : Blo 2203435 8597281 := bstep (se 2 (by rfl) ⟨3223980, by rfl⟩ : syracuseStep 8597281 = 6447961) B6447961
theorem B11463041 : Blo 2203435 11463041 := bstep (se 2 (by rfl) ⟨4298640, by rfl⟩ : syracuseStep 11463041 = 8597281) B8597281
theorem B30568109 : Blo 2203435 30568109 := bstep (se 3 (by rfl) ⟨5731520, by rfl⟩ : syracuseStep 30568109 = 11463041) B11463041
theorem B81514957 : Blo 2203435 81514957 := bstep (se 3 (by rfl) ⟨15284054, by rfl⟩ : syracuseStep 81514957 = 30568109) B30568109
theorem B108686609 : Blo 2203435 108686609 := bstep (se 2 (by rfl) ⟨40757478, by rfl⟩ : syracuseStep 108686609 = 81514957) B81514957
theorem B72457739 : Blo 2203435 72457739 := bstep (se 1 (by rfl) ⟨54343304, by rfl⟩ : syracuseStep 72457739 = 108686609) B108686609
theorem B48305159 : Blo 2203435 48305159 := bstep (se 1 (by rfl) ⟨36228869, by rfl⟩ : syracuseStep 48305159 = 72457739) B72457739
theorem B32203439 : Blo 2203435 32203439 := bstep (se 1 (by rfl) ⟨24152579, by rfl⟩ : syracuseStep 32203439 = 48305159) B48305159
theorem B21468959 : Blo 2203435 21468959 := bstep (se 1 (by rfl) ⟨16101719, by rfl⟩ : syracuseStep 21468959 = 32203439) B32203439
theorem B14312639 : Blo 2203435 14312639 := bstep (se 1 (by rfl) ⟨10734479, by rfl⟩ : syracuseStep 14312639 = 21468959) B21468959
theorem B9541759 : Blo 2203435 9541759 := bstep (se 1 (by rfl) ⟨7156319, by rfl⟩ : syracuseStep 9541759 = 14312639) B14312639
theorem B12722345 : Blo 2203435 12722345 := bstep (se 2 (by rfl) ⟨4770879, by rfl⟩ : syracuseStep 12722345 = 9541759) B9541759
theorem B8481563 : Blo 2203435 8481563 := bstep (se 1 (by rfl) ⟨6361172, by rfl⟩ : syracuseStep 8481563 = 12722345) B12722345
theorem B5654375 : Blo 2203435 5654375 := bstep (se 1 (by rfl) ⟨4240781, by rfl⟩ : syracuseStep 5654375 = 8481563) B8481563
theorem B3769583 : Blo 2203435 3769583 := bstep (se 1 (by rfl) ⟨2827187, by rfl⟩ : syracuseStep 3769583 = 5654375) B5654375
theorem B40208885 : Blo 2203435 40208885 := bstep (se 5 (by rfl) ⟨1884791, by rfl⟩ : syracuseStep 40208885 = 3769583) B3769583
theorem B26805923 : Blo 2203435 26805923 := bstep (se 1 (by rfl) ⟨20104442, by rfl⟩ : syracuseStep 26805923 = 40208885) B40208885
theorem B17870615 : Blo 2203435 17870615 := bstep (se 1 (by rfl) ⟨13402961, by rfl⟩ : syracuseStep 17870615 = 26805923) B26805923
theorem B11913743 : Blo 2203435 11913743 := bstep (se 1 (by rfl) ⟨8935307, by rfl⟩ : syracuseStep 11913743 = 17870615) B17870615
theorem B31769981 : Blo 2203435 31769981 := bstep (se 3 (by rfl) ⟨5956871, by rfl⟩ : syracuseStep 31769981 = 11913743) B11913743
theorem B21179987 : Blo 2203435 21179987 := bstep (se 1 (by rfl) ⟨15884990, by rfl⟩ : syracuseStep 21179987 = 31769981) B31769981
theorem B14119991 : Blo 2203435 14119991 := bstep (se 1 (by rfl) ⟨10589993, by rfl⟩ : syracuseStep 14119991 = 21179987) B21179987
theorem B9413327 : Blo 2203435 9413327 := bstep (se 1 (by rfl) ⟨7059995, by rfl⟩ : syracuseStep 9413327 = 14119991) B14119991
theorem B6275551 : Blo 2203435 6275551 := bstep (se 1 (by rfl) ⟨4706663, by rfl⟩ : syracuseStep 6275551 = 9413327) B9413327
theorem B8367401 : Blo 2203435 8367401 := bstep (se 2 (by rfl) ⟨3137775, by rfl⟩ : syracuseStep 8367401 = 6275551) B6275551
theorem B5578267 : Blo 2203435 5578267 := bstep (se 1 (by rfl) ⟨4183700, by rfl⟩ : syracuseStep 5578267 = 8367401) B8367401
theorem B7437689 : Blo 2203435 7437689 := bstep (se 2 (by rfl) ⟨2789133, by rfl⟩ : syracuseStep 7437689 = 5578267) B5578267
theorem B4958459 : Blo 2203435 4958459 := bstep (se 1 (by rfl) ⟨3718844, by rfl⟩ : syracuseStep 4958459 = 7437689) B7437689
theorem B3305639 : Blo 2203435 3305639 := bstep (se 1 (by rfl) ⟨2479229, by rfl⟩ : syracuseStep 3305639 = 4958459) B4958459
theorem B2203759 : Blo 2203435 2203759 := bstep (se 1 (by rfl) ⟨1652819, by rfl⟩ : syracuseStep 2203759 = 3305639) B3305639
theorem B3305645 : Blo 2203435 3305645 := bbase (se 3 (by rfl) ⟨619808, by rfl⟩ : syracuseStep 3305645 = 1239617) (by norm_num)
theorem B2203763 : Blo 2203435 2203763 := bstep (se 1 (by rfl) ⟨1652822, by rfl⟩ : syracuseStep 2203763 = 3305645) B3305645
theorem B4958477 : Blo 2203435 4958477 := bbase (se 3 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 4958477 = 1859429) (by norm_num)
theorem B3305651 : Blo 2203435 3305651 := bstep (se 1 (by rfl) ⟨2479238, by rfl⟩ : syracuseStep 3305651 = 4958477) B4958477
theorem B2203767 : Blo 2203435 2203767 := bstep (se 1 (by rfl) ⟨1652825, by rfl⟩ : syracuseStep 2203767 = 3305651) B3305651
theorem B2789149 : Blo 2203435 2789149 := bbase (se 3 (by rfl) ⟨522965, by rfl⟩ : syracuseStep 2789149 = 1045931) (by norm_num)
theorem B3718865 : Blo 2203435 3718865 := bstep (se 2 (by rfl) ⟨1394574, by rfl⟩ : syracuseStep 3718865 = 2789149) B2789149
theorem B2479243 : Blo 2203435 2479243 := bstep (se 1 (by rfl) ⟨1859432, by rfl⟩ : syracuseStep 2479243 = 3718865) B3718865
theorem B3305657 : Blo 2203435 3305657 := bstep (se 2 (by rfl) ⟨1239621, by rfl⟩ : syracuseStep 3305657 = 2479243) B2479243
theorem B2203771 : Blo 2203435 2203771 := bstep (se 1 (by rfl) ⟨1652828, by rfl⟩ : syracuseStep 2203771 = 3305657) B3305657
theorem B3350765 : Blo 2203435 3350765 := bbase (se 3 (by rfl) ⟨628268, by rfl⟩ : syracuseStep 3350765 = 1256537) (by norm_num)
theorem B8935373 : Blo 2203435 8935373 := bstep (se 3 (by rfl) ⟨1675382, by rfl⟩ : syracuseStep 8935373 = 3350765) B3350765
theorem B5956915 : Blo 2203435 5956915 := bstep (se 1 (by rfl) ⟨4467686, by rfl⟩ : syracuseStep 5956915 = 8935373) B8935373
theorem B7942553 : Blo 2203435 7942553 := bstep (se 2 (by rfl) ⟨2978457, by rfl⟩ : syracuseStep 7942553 = 5956915) B5956915
theorem B5295035 : Blo 2203435 5295035 := bstep (se 1 (by rfl) ⟨3971276, by rfl⟩ : syracuseStep 5295035 = 7942553) B7942553
theorem B3530023 : Blo 2203435 3530023 := bstep (se 1 (by rfl) ⟨2647517, by rfl⟩ : syracuseStep 3530023 = 5295035) B5295035
theorem B18826789 : Blo 2203435 18826789 := bstep (se 4 (by rfl) ⟨1765011, by rfl⟩ : syracuseStep 18826789 = 3530023) B3530023
theorem B25102385 : Blo 2203435 25102385 := bstep (se 2 (by rfl) ⟨9413394, by rfl⟩ : syracuseStep 25102385 = 18826789) B18826789
theorem B16734923 : Blo 2203435 16734923 := bstep (se 1 (by rfl) ⟨12551192, by rfl⟩ : syracuseStep 16734923 = 25102385) B25102385
theorem B11156615 : Blo 2203435 11156615 := bstep (se 1 (by rfl) ⟨8367461, by rfl⟩ : syracuseStep 11156615 = 16734923) B16734923
theorem B7437743 : Blo 2203435 7437743 := bstep (se 1 (by rfl) ⟨5578307, by rfl⟩ : syracuseStep 7437743 = 11156615) B11156615
theorem B4958495 : Blo 2203435 4958495 := bstep (se 1 (by rfl) ⟨3718871, by rfl⟩ : syracuseStep 4958495 = 7437743) B7437743
theorem B3305663 : Blo 2203435 3305663 := bstep (se 1 (by rfl) ⟨2479247, by rfl⟩ : syracuseStep 3305663 = 4958495) B4958495
theorem B2203775 : Blo 2203435 2203775 := bstep (se 1 (by rfl) ⟨1652831, by rfl⟩ : syracuseStep 2203775 = 3305663) B3305663
theorem B3305669 : Blo 2203435 3305669 := bbase (se 4 (by rfl) ⟨309906, by rfl⟩ : syracuseStep 3305669 = 619813) (by norm_num)
theorem B2203779 : Blo 2203435 2203779 := bstep (se 1 (by rfl) ⟨1652834, by rfl⟩ : syracuseStep 2203779 = 3305669) B3305669
theorem B3718885 : Blo 2203435 3718885 := bbase (se 4 (by rfl) ⟨348645, by rfl⟩ : syracuseStep 3718885 = 697291) (by norm_num)
theorem B4958513 : Blo 2203435 4958513 := bstep (se 2 (by rfl) ⟨1859442, by rfl⟩ : syracuseStep 4958513 = 3718885) B3718885
theorem B3305675 : Blo 2203435 3305675 := bstep (se 1 (by rfl) ⟨2479256, by rfl⟩ : syracuseStep 3305675 = 4958513) B4958513
theorem B2203783 : Blo 2203435 2203783 := bstep (se 1 (by rfl) ⟨1652837, by rfl⟩ : syracuseStep 2203783 = 3305675) B3305675
theorem B2479261 : Blo 2203435 2479261 := bbase (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) (by norm_num)
theorem B3305681 : Blo 2203435 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B2203787 : Blo 2203435 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B7437797 : Blo 2203435 7437797 := bbase (se 4 (by rfl) ⟨697293, by rfl⟩ : syracuseStep 7437797 = 1394587) (by norm_num)
theorem B4958531 : Blo 2203435 4958531 := bstep (se 1 (by rfl) ⟨3718898, by rfl⟩ : syracuseStep 4958531 = 7437797) B7437797
theorem B3305687 : Blo 2203435 3305687 := bstep (se 1 (by rfl) ⟨2479265, by rfl⟩ : syracuseStep 3305687 = 4958531) B4958531
theorem B2203791 : Blo 2203435 2203791 := bstep (se 1 (by rfl) ⟨1652843, by rfl⟩ : syracuseStep 2203791 = 3305687) B3305687
theorem B3305693 : Blo 2203435 3305693 := bbase (se 3 (by rfl) ⟨619817, by rfl⟩ : syracuseStep 3305693 = 1239635) (by norm_num)
theorem B2203795 : Blo 2203435 2203795 := bstep (se 1 (by rfl) ⟨1652846, by rfl⟩ : syracuseStep 2203795 = 3305693) B3305693
theorem B4958549 : Blo 2203435 4958549 := bbase (se 10 (by rfl) ⟨7263, by rfl⟩ : syracuseStep 4958549 = 14527) (by norm_num)
theorem B3305699 : Blo 2203435 3305699 := bstep (se 1 (by rfl) ⟨2479274, by rfl⟩ : syracuseStep 3305699 = 4958549) B4958549
theorem B2203799 : Blo 2203435 2203799 := bstep (se 1 (by rfl) ⟨1652849, by rfl⟩ : syracuseStep 2203799 = 3305699) B3305699
theorem B3530069 : Blo 2203435 3530069 := bbase (se 11 (by rfl) ⟨2585, by rfl⟩ : syracuseStep 3530069 = 5171) (by norm_num)
theorem B2353379 : Blo 2203435 2353379 := bstep (se 1 (by rfl) ⟨1765034, by rfl⟩ : syracuseStep 2353379 = 3530069) B3530069
theorem B6275677 : Blo 2203435 6275677 := bstep (se 3 (by rfl) ⟨1176689, by rfl⟩ : syracuseStep 6275677 = 2353379) B2353379
theorem B8367569 : Blo 2203435 8367569 := bstep (se 2 (by rfl) ⟨3137838, by rfl⟩ : syracuseStep 8367569 = 6275677) B6275677
theorem B5578379 : Blo 2203435 5578379 := bstep (se 1 (by rfl) ⟨4183784, by rfl⟩ : syracuseStep 5578379 = 8367569) B8367569
theorem B3718919 : Blo 2203435 3718919 := bstep (se 1 (by rfl) ⟨2789189, by rfl⟩ : syracuseStep 3718919 = 5578379) B5578379
theorem B2479279 : Blo 2203435 2479279 := bstep (se 1 (by rfl) ⟨1859459, by rfl⟩ : syracuseStep 2479279 = 3718919) B3718919
theorem B3305705 : Blo 2203435 3305705 := bstep (se 2 (by rfl) ⟨1239639, by rfl⟩ : syracuseStep 3305705 = 2479279) B2479279
theorem B2203803 : Blo 2203435 2203803 := bstep (se 1 (by rfl) ⟨1652852, by rfl⟩ : syracuseStep 2203803 = 3305705) B3305705
theorem B3350813 : Blo 2203435 3350813 := bbase (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) (by norm_num)
theorem B35742005 : Blo 2203435 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B23828003 : Blo 2203435 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B15885335 : Blo 2203435 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B42360893 : Blo 2203435 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B28240595 : Blo 2203435 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B18827063 : Blo 2203435 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B12551375 : Blo 2203435 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B8367583 : Blo 2203435 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B11156777 : Blo 2203435 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B7437851 : Blo 2203435 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B4958567 : Blo 2203435 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B3305711 : Blo 2203435 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B2203807 : Blo 2203435 2203807 := bstep (se 1 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 2203807 = 3305711) B3305711
theorem B3305717 : Blo 2203435 3305717 := bbase (se 5 (by rfl) ⟨154955, by rfl⟩ : syracuseStep 3305717 = 309911) (by norm_num)
theorem B2203811 : Blo 2203435 2203811 := bstep (se 1 (by rfl) ⟨1652858, by rfl⟩ : syracuseStep 2203811 = 3305717) B3305717
theorem B8499509 : Blo 2203435 8499509 := bbase (se 5 (by rfl) ⟨398414, by rfl⟩ : syracuseStep 8499509 = 796829) (by norm_num)
theorem B5666339 : Blo 2203435 5666339 := bstep (se 1 (by rfl) ⟨4249754, by rfl⟩ : syracuseStep 5666339 = 8499509) B8499509
theorem B15110237 : Blo 2203435 15110237 := bstep (se 3 (by rfl) ⟨2833169, by rfl⟩ : syracuseStep 15110237 = 5666339) B5666339
theorem B10073491 : Blo 2203435 10073491 := bstep (se 1 (by rfl) ⟨7555118, by rfl⟩ : syracuseStep 10073491 = 15110237) B15110237
theorem B53725285 : Blo 2203435 53725285 := bstep (se 4 (by rfl) ⟨5036745, by rfl⟩ : syracuseStep 53725285 = 10073491) B10073491
theorem B286534853 : Blo 2203435 286534853 := bstep (se 4 (by rfl) ⟨26862642, by rfl⟩ : syracuseStep 286534853 = 53725285) B53725285
theorem B191023235 : Blo 2203435 191023235 := bstep (se 1 (by rfl) ⟨143267426, by rfl⟩ : syracuseStep 191023235 = 286534853) B286534853
theorem B127348823 : Blo 2203435 127348823 := bstep (se 1 (by rfl) ⟨95511617, by rfl⟩ : syracuseStep 127348823 = 191023235) B191023235
theorem B84899215 : Blo 2203435 84899215 := bstep (se 1 (by rfl) ⟨63674411, by rfl⟩ : syracuseStep 84899215 = 127348823) B127348823
theorem B113198953 : Blo 2203435 113198953 := bstep (se 2 (by rfl) ⟨42449607, by rfl⟩ : syracuseStep 113198953 = 84899215) B84899215
theorem B150931937 : Blo 2203435 150931937 := bstep (se 2 (by rfl) ⟨56599476, by rfl⟩ : syracuseStep 150931937 = 113198953) B113198953
theorem B100621291 : Blo 2203435 100621291 := bstep (se 1 (by rfl) ⟨75465968, by rfl⟩ : syracuseStep 100621291 = 150931937) B150931937
theorem B134161721 : Blo 2203435 134161721 := bstep (se 2 (by rfl) ⟨50310645, by rfl⟩ : syracuseStep 134161721 = 100621291) B100621291
theorem B89441147 : Blo 2203435 89441147 := bstep (se 1 (by rfl) ⟨67080860, by rfl⟩ : syracuseStep 89441147 = 134161721) B134161721
theorem B59627431 : Blo 2203435 59627431 := bstep (se 1 (by rfl) ⟨44720573, by rfl⟩ : syracuseStep 59627431 = 89441147) B89441147
theorem B79503241 : Blo 2203435 79503241 := bstep (se 2 (by rfl) ⟨29813715, by rfl⟩ : syracuseStep 79503241 = 59627431) B59627431
theorem B106004321 : Blo 2203435 106004321 := bstep (se 2 (by rfl) ⟨39751620, by rfl⟩ : syracuseStep 106004321 = 79503241) B79503241
theorem B70669547 : Blo 2203435 70669547 := bstep (se 1 (by rfl) ⟨53002160, by rfl⟩ : syracuseStep 70669547 = 106004321) B106004321
theorem B47113031 : Blo 2203435 47113031 := bstep (se 1 (by rfl) ⟨35334773, by rfl⟩ : syracuseStep 47113031 = 70669547) B70669547
theorem B31408687 : Blo 2203435 31408687 := bstep (se 1 (by rfl) ⟨23556515, by rfl⟩ : syracuseStep 31408687 = 47113031) B47113031
theorem B41878249 : Blo 2203435 41878249 := bstep (se 2 (by rfl) ⟨15704343, by rfl⟩ : syracuseStep 41878249 = 31408687) B31408687
theorem B223350661 : Blo 2203435 223350661 := bstep (se 4 (by rfl) ⟨20939124, by rfl⟩ : syracuseStep 223350661 = 41878249) B41878249
theorem B1191203525 : Blo 2203435 1191203525 := bstep (se 4 (by rfl) ⟨111675330, by rfl⟩ : syracuseStep 1191203525 = 223350661) B223350661
theorem B794135683 : Blo 2203435 794135683 := bstep (se 1 (by rfl) ⟨595601762, by rfl⟩ : syracuseStep 794135683 = 1191203525) B1191203525
theorem B4235390309 : Blo 2203435 4235390309 := bstep (se 4 (by rfl) ⟨397067841, by rfl⟩ : syracuseStep 4235390309 = 794135683) B794135683
theorem B2823593539 : Blo 2203435 2823593539 := bstep (se 1 (by rfl) ⟨2117695154, by rfl⟩ : syracuseStep 2823593539 = 4235390309) B4235390309
theorem B3764791385 : Blo 2203435 3764791385 := bstep (se 2 (by rfl) ⟨1411796769, by rfl⟩ : syracuseStep 3764791385 = 2823593539) B2823593539
theorem B2509860923 : Blo 2203435 2509860923 := bstep (se 1 (by rfl) ⟨1882395692, by rfl⟩ : syracuseStep 2509860923 = 3764791385) B3764791385
theorem B1673240615 : Blo 2203435 1673240615 := bstep (se 1 (by rfl) ⟨1254930461, by rfl⟩ : syracuseStep 1673240615 = 2509860923) B2509860923
theorem B1115493743 : Blo 2203435 1115493743 := bstep (se 1 (by rfl) ⟨836620307, by rfl⟩ : syracuseStep 1115493743 = 1673240615) B1673240615
theorem B743662495 : Blo 2203435 743662495 := bstep (se 1 (by rfl) ⟨557746871, by rfl⟩ : syracuseStep 743662495 = 1115493743) B1115493743
theorem B991549993 : Blo 2203435 991549993 := bstep (se 2 (by rfl) ⟨371831247, by rfl⟩ : syracuseStep 991549993 = 743662495) B743662495
theorem B1322066657 : Blo 2203435 1322066657 := bstep (se 2 (by rfl) ⟨495774996, by rfl⟩ : syracuseStep 1322066657 = 991549993) B991549993
theorem B881377771 : Blo 2203435 881377771 := bstep (se 1 (by rfl) ⟨661033328, by rfl⟩ : syracuseStep 881377771 = 1322066657) B1322066657
theorem B1175170361 : Blo 2203435 1175170361 := bstep (se 2 (by rfl) ⟨440688885, by rfl⟩ : syracuseStep 1175170361 = 881377771) B881377771
theorem B3133787629 : Blo 2203435 3133787629 := bstep (se 3 (by rfl) ⟨587585180, by rfl⟩ : syracuseStep 3133787629 = 1175170361) B1175170361
theorem B4178383505 : Blo 2203435 4178383505 := bstep (se 2 (by rfl) ⟨1566893814, by rfl⟩ : syracuseStep 4178383505 = 3133787629) B3133787629
theorem B2785589003 : Blo 2203435 2785589003 := bstep (se 1 (by rfl) ⟨2089191752, by rfl⟩ : syracuseStep 2785589003 = 4178383505) B4178383505
theorem B1857059335 : Blo 2203435 1857059335 := bstep (se 1 (by rfl) ⟨1392794501, by rfl⟩ : syracuseStep 1857059335 = 2785589003) B2785589003
theorem B2476079113 : Blo 2203435 2476079113 := bstep (se 2 (by rfl) ⟨928529667, by rfl⟩ : syracuseStep 2476079113 = 1857059335) B1857059335
theorem B3301438817 : Blo 2203435 3301438817 := bstep (se 2 (by rfl) ⟨1238039556, by rfl⟩ : syracuseStep 3301438817 = 2476079113) B2476079113
theorem B2200959211 : Blo 2203435 2200959211 := bstep (se 1 (by rfl) ⟨1650719408, by rfl⟩ : syracuseStep 2200959211 = 3301438817) B3301438817
theorem B2934612281 : Blo 2203435 2934612281 := bstep (se 2 (by rfl) ⟨1100479605, by rfl⟩ : syracuseStep 2934612281 = 2200959211) B2200959211
theorem B1956408187 : Blo 2203435 1956408187 := bstep (se 1 (by rfl) ⟨1467306140, by rfl⟩ : syracuseStep 1956408187 = 2934612281) B2934612281
theorem B2608544249 : Blo 2203435 2608544249 := bstep (se 2 (by rfl) ⟨978204093, by rfl⟩ : syracuseStep 2608544249 = 1956408187) B1956408187
theorem B1739029499 : Blo 2203435 1739029499 := bstep (se 1 (by rfl) ⟨1304272124, by rfl⟩ : syracuseStep 1739029499 = 2608544249) B2608544249
theorem B1159352999 : Blo 2203435 1159352999 := bstep (se 1 (by rfl) ⟨869514749, by rfl⟩ : syracuseStep 1159352999 = 1739029499) B1739029499
theorem B772901999 : Blo 2203435 772901999 := bstep (se 1 (by rfl) ⟨579676499, by rfl⟩ : syracuseStep 772901999 = 1159352999) B1159352999
theorem B515267999 : Blo 2203435 515267999 := bstep (se 1 (by rfl) ⟨386450999, by rfl⟩ : syracuseStep 515267999 = 772901999) B772901999
theorem B343511999 : Blo 2203435 343511999 := bstep (se 1 (by rfl) ⟨257633999, by rfl⟩ : syracuseStep 343511999 = 515267999) B515267999
theorem B229007999 : Blo 2203435 229007999 := bstep (se 1 (by rfl) ⟨171755999, by rfl⟩ : syracuseStep 229007999 = 343511999) B343511999
theorem B152671999 : Blo 2203435 152671999 := bstep (se 1 (by rfl) ⟨114503999, by rfl⟩ : syracuseStep 152671999 = 229007999) B229007999
theorem B203562665 : Blo 2203435 203562665 := bstep (se 2 (by rfl) ⟨76335999, by rfl⟩ : syracuseStep 203562665 = 152671999) B152671999
theorem B135708443 : Blo 2203435 135708443 := bstep (se 1 (by rfl) ⟨101781332, by rfl⟩ : syracuseStep 135708443 = 203562665) B203562665
theorem B90472295 : Blo 2203435 90472295 := bstep (se 1 (by rfl) ⟨67854221, by rfl⟩ : syracuseStep 90472295 = 135708443) B135708443
theorem B60314863 : Blo 2203435 60314863 := bstep (se 1 (by rfl) ⟨45236147, by rfl⟩ : syracuseStep 60314863 = 90472295) B90472295
theorem B80419817 : Blo 2203435 80419817 := bstep (se 2 (by rfl) ⟨30157431, by rfl⟩ : syracuseStep 80419817 = 60314863) B60314863
theorem B53613211 : Blo 2203435 53613211 := bstep (se 1 (by rfl) ⟨40209908, by rfl⟩ : syracuseStep 53613211 = 80419817) B80419817
theorem B71484281 : Blo 2203435 71484281 := bstep (se 2 (by rfl) ⟨26806605, by rfl⟩ : syracuseStep 71484281 = 53613211) B53613211
theorem B47656187 : Blo 2203435 47656187 := bstep (se 1 (by rfl) ⟨35742140, by rfl⟩ : syracuseStep 47656187 = 71484281) B71484281
theorem B31770791 : Blo 2203435 31770791 := bstep (se 1 (by rfl) ⟨23828093, by rfl⟩ : syracuseStep 31770791 = 47656187) B47656187
theorem B21180527 : Blo 2203435 21180527 := bstep (se 1 (by rfl) ⟨15885395, by rfl⟩ : syracuseStep 21180527 = 31770791) B31770791
theorem B14120351 : Blo 2203435 14120351 := bstep (se 1 (by rfl) ⟨10590263, by rfl⟩ : syracuseStep 14120351 = 21180527) B21180527
theorem B9413567 : Blo 2203435 9413567 := bstep (se 1 (by rfl) ⟨7060175, by rfl⟩ : syracuseStep 9413567 = 14120351) B14120351
theorem B6275711 : Blo 2203435 6275711 := bstep (se 1 (by rfl) ⟨4706783, by rfl⟩ : syracuseStep 6275711 = 9413567) B9413567
theorem B4183807 : Blo 2203435 4183807 := bstep (se 1 (by rfl) ⟨3137855, by rfl⟩ : syracuseStep 4183807 = 6275711) B6275711
theorem B5578409 : Blo 2203435 5578409 := bstep (se 2 (by rfl) ⟨2091903, by rfl⟩ : syracuseStep 5578409 = 4183807) B4183807
theorem B3718939 : Blo 2203435 3718939 := bstep (se 1 (by rfl) ⟨2789204, by rfl⟩ : syracuseStep 3718939 = 5578409) B5578409
theorem B4958585 : Blo 2203435 4958585 := bstep (se 2 (by rfl) ⟨1859469, by rfl⟩ : syracuseStep 4958585 = 3718939) B3718939
theorem B3305723 : Blo 2203435 3305723 := bstep (se 1 (by rfl) ⟨2479292, by rfl⟩ : syracuseStep 3305723 = 4958585) B4958585
theorem B2203815 : Blo 2203435 2203815 := bstep (se 1 (by rfl) ⟨1652861, by rfl⟩ : syracuseStep 2203815 = 3305723) B3305723
theorem B2479297 : Blo 2203435 2479297 := bbase (se 2 (by rfl) ⟨929736, by rfl⟩ : syracuseStep 2479297 = 1859473) (by norm_num)
theorem B3305729 : Blo 2203435 3305729 := bstep (se 2 (by rfl) ⟨1239648, by rfl⟩ : syracuseStep 3305729 = 2479297) B2479297
theorem B2203819 : Blo 2203435 2203819 := bstep (se 1 (by rfl) ⟨1652864, by rfl⟩ : syracuseStep 2203819 = 3305729) B3305729
theorem B5578429 : Blo 2203435 5578429 := bbase (se 3 (by rfl) ⟨1045955, by rfl⟩ : syracuseStep 5578429 = 2091911) (by norm_num)
theorem B7437905 : Blo 2203435 7437905 := bstep (se 2 (by rfl) ⟨2789214, by rfl⟩ : syracuseStep 7437905 = 5578429) B5578429
theorem B4958603 : Blo 2203435 4958603 := bstep (se 1 (by rfl) ⟨3718952, by rfl⟩ : syracuseStep 4958603 = 7437905) B7437905
theorem B3305735 : Blo 2203435 3305735 := bstep (se 1 (by rfl) ⟨2479301, by rfl⟩ : syracuseStep 3305735 = 4958603) B4958603
theorem B2203823 : Blo 2203435 2203823 := bstep (se 1 (by rfl) ⟨1652867, by rfl⟩ : syracuseStep 2203823 = 3305735) B3305735
theorem B3305741 : Blo 2203435 3305741 := bbase (se 3 (by rfl) ⟨619826, by rfl⟩ : syracuseStep 3305741 = 1239653) (by norm_num)
theorem B2203827 : Blo 2203435 2203827 := bstep (se 1 (by rfl) ⟨1652870, by rfl⟩ : syracuseStep 2203827 = 3305741) B3305741
theorem B4958621 : Blo 2203435 4958621 := bbase (se 3 (by rfl) ⟨929741, by rfl⟩ : syracuseStep 4958621 = 1859483) (by norm_num)
theorem B3305747 : Blo 2203435 3305747 := bstep (se 1 (by rfl) ⟨2479310, by rfl⟩ : syracuseStep 3305747 = 4958621) B4958621
theorem B2203831 : Blo 2203435 2203831 := bstep (se 1 (by rfl) ⟨1652873, by rfl⟩ : syracuseStep 2203831 = 3305747) B3305747
theorem B3718973 : Blo 2203435 3718973 := bbase (se 3 (by rfl) ⟨697307, by rfl⟩ : syracuseStep 3718973 = 1394615) (by norm_num)
theorem B2479315 : Blo 2203435 2479315 := bstep (se 1 (by rfl) ⟨1859486, by rfl⟩ : syracuseStep 2479315 = 3718973) B3718973
theorem B3305753 : Blo 2203435 3305753 := bstep (se 2 (by rfl) ⟨1239657, by rfl⟩ : syracuseStep 3305753 = 2479315) B2479315
theorem B2203835 : Blo 2203435 2203835 := bstep (se 1 (by rfl) ⟨1652876, by rfl⟩ : syracuseStep 2203835 = 3305753) B3305753
theorem B2353417 : Blo 2203435 2353417 := bbase (se 2 (by rfl) ⟨882531, by rfl⟩ : syracuseStep 2353417 = 1765063) (by norm_num)
theorem B12551557 : Blo 2203435 12551557 := bstep (se 4 (by rfl) ⟨1176708, by rfl⟩ : syracuseStep 12551557 = 2353417) B2353417
theorem B16735409 : Blo 2203435 16735409 := bstep (se 2 (by rfl) ⟨6275778, by rfl⟩ : syracuseStep 16735409 = 12551557) B12551557
theorem B11156939 : Blo 2203435 11156939 := bstep (se 1 (by rfl) ⟨8367704, by rfl⟩ : syracuseStep 11156939 = 16735409) B16735409
theorem B7437959 : Blo 2203435 7437959 := bstep (se 1 (by rfl) ⟨5578469, by rfl⟩ : syracuseStep 7437959 = 11156939) B11156939
theorem B4958639 : Blo 2203435 4958639 := bstep (se 1 (by rfl) ⟨3718979, by rfl⟩ : syracuseStep 4958639 = 7437959) B7437959
theorem B3305759 : Blo 2203435 3305759 := bstep (se 1 (by rfl) ⟨2479319, by rfl⟩ : syracuseStep 3305759 = 4958639) B4958639
theorem B2203839 : Blo 2203435 2203839 := bstep (se 1 (by rfl) ⟨1652879, by rfl⟩ : syracuseStep 2203839 = 3305759) B3305759
theorem B3305765 : Blo 2203435 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B2203843 : Blo 2203435 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B2789245 : Blo 2203435 2789245 := bbase (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) (by norm_num)
theorem B3718993 : Blo 2203435 3718993 := bstep (se 2 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 3718993 = 2789245) B2789245
theorem B4958657 : Blo 2203435 4958657 := bstep (se 2 (by rfl) ⟨1859496, by rfl⟩ : syracuseStep 4958657 = 3718993) B3718993
theorem B3305771 : Blo 2203435 3305771 := bstep (se 1 (by rfl) ⟨2479328, by rfl⟩ : syracuseStep 3305771 = 4958657) B4958657
theorem B2203847 : Blo 2203435 2203847 := bstep (se 1 (by rfl) ⟨1652885, by rfl⟩ : syracuseStep 2203847 = 3305771) B3305771
theorem B2479333 : Blo 2203435 2479333 := bbase (se 4 (by rfl) ⟨232437, by rfl⟩ : syracuseStep 2479333 = 464875) (by norm_num)
theorem B3305777 : Blo 2203435 3305777 := bstep (se 2 (by rfl) ⟨1239666, by rfl⟩ : syracuseStep 3305777 = 2479333) B2479333
theorem B2203851 : Blo 2203435 2203851 := bstep (se 1 (by rfl) ⟨1652888, by rfl⟩ : syracuseStep 2203851 = 3305777) B3305777
theorem B4706869 : Blo 2203435 4706869 := bbase (se 5 (by rfl) ⟨220634, by rfl⟩ : syracuseStep 4706869 = 441269) (by norm_num)
theorem B6275825 : Blo 2203435 6275825 := bstep (se 2 (by rfl) ⟨2353434, by rfl⟩ : syracuseStep 6275825 = 4706869) B4706869
theorem B4183883 : Blo 2203435 4183883 := bstep (se 1 (by rfl) ⟨3137912, by rfl⟩ : syracuseStep 4183883 = 6275825) B6275825
theorem B2789255 : Blo 2203435 2789255 := bstep (se 1 (by rfl) ⟨2091941, by rfl⟩ : syracuseStep 2789255 = 4183883) B4183883
theorem B7438013 : Blo 2203435 7438013 := bstep (se 3 (by rfl) ⟨1394627, by rfl⟩ : syracuseStep 7438013 = 2789255) B2789255
theorem B4958675 : Blo 2203435 4958675 := bstep (se 1 (by rfl) ⟨3719006, by rfl⟩ : syracuseStep 4958675 = 7438013) B7438013
theorem B3305783 : Blo 2203435 3305783 := bstep (se 1 (by rfl) ⟨2479337, by rfl⟩ : syracuseStep 3305783 = 4958675) B4958675
theorem B2203855 : Blo 2203435 2203855 := bstep (se 1 (by rfl) ⟨1652891, by rfl⟩ : syracuseStep 2203855 = 3305783) B3305783
theorem B3305789 : Blo 2203435 3305789 := bbase (se 3 (by rfl) ⟨619835, by rfl⟩ : syracuseStep 3305789 = 1239671) (by norm_num)
theorem B2203859 : Blo 2203435 2203859 := bstep (se 1 (by rfl) ⟨1652894, by rfl⟩ : syracuseStep 2203859 = 3305789) B3305789
theorem B4958693 : Blo 2203435 4958693 := bbase (se 4 (by rfl) ⟨464877, by rfl⟩ : syracuseStep 4958693 = 929755) (by norm_num)
theorem B3305795 : Blo 2203435 3305795 := bstep (se 1 (by rfl) ⟨2479346, by rfl⟩ : syracuseStep 3305795 = 4958693) B4958693
theorem B2203863 : Blo 2203435 2203863 := bstep (se 1 (by rfl) ⟨1652897, by rfl⟩ : syracuseStep 2203863 = 3305795) B3305795
theorem B5578541 : Blo 2203435 5578541 := bbase (se 3 (by rfl) ⟨1045976, by rfl⟩ : syracuseStep 5578541 = 2091953) (by norm_num)
theorem B3719027 : Blo 2203435 3719027 := bstep (se 1 (by rfl) ⟨2789270, by rfl⟩ : syracuseStep 3719027 = 5578541) B5578541
theorem B2479351 : Blo 2203435 2479351 := bstep (se 1 (by rfl) ⟨1859513, by rfl⟩ : syracuseStep 2479351 = 3719027) B3719027
theorem B3305801 : Blo 2203435 3305801 := bstep (se 2 (by rfl) ⟨1239675, by rfl⟩ : syracuseStep 3305801 = 2479351) B2479351
theorem B2203867 : Blo 2203435 2203867 := bstep (se 1 (by rfl) ⟨1652900, by rfl⟩ : syracuseStep 2203867 = 3305801) B3305801
theorem B10590533 : Blo 2203435 10590533 := bbase (se 4 (by rfl) ⟨992862, by rfl⟩ : syracuseStep 10590533 = 1985725) (by norm_num)
theorem B7060355 : Blo 2203435 7060355 := bstep (se 1 (by rfl) ⟨5295266, by rfl⟩ : syracuseStep 7060355 = 10590533) B10590533
theorem B4706903 : Blo 2203435 4706903 := bstep (se 1 (by rfl) ⟨3530177, by rfl⟩ : syracuseStep 4706903 = 7060355) B7060355
theorem B3137935 : Blo 2203435 3137935 := bstep (se 1 (by rfl) ⟨2353451, by rfl⟩ : syracuseStep 3137935 = 4706903) B4706903
theorem B4183913 : Blo 2203435 4183913 := bstep (se 2 (by rfl) ⟨1568967, by rfl⟩ : syracuseStep 4183913 = 3137935) B3137935
theorem B11157101 : Blo 2203435 11157101 := bstep (se 3 (by rfl) ⟨2091956, by rfl⟩ : syracuseStep 11157101 = 4183913) B4183913
theorem B7438067 : Blo 2203435 7438067 := bstep (se 1 (by rfl) ⟨5578550, by rfl⟩ : syracuseStep 7438067 = 11157101) B11157101
theorem B4958711 : Blo 2203435 4958711 := bstep (se 1 (by rfl) ⟨3719033, by rfl⟩ : syracuseStep 4958711 = 7438067) B7438067
theorem B3305807 : Blo 2203435 3305807 := bstep (se 1 (by rfl) ⟨2479355, by rfl⟩ : syracuseStep 3305807 = 4958711) B4958711
theorem B2203871 : Blo 2203435 2203871 := bstep (se 1 (by rfl) ⟨1652903, by rfl⟩ : syracuseStep 2203871 = 3305807) B3305807
theorem B3305813 : Blo 2203435 3305813 := bbase (se 10 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 3305813 = 9685) (by norm_num)
theorem B2203875 : Blo 2203435 2203875 := bstep (se 1 (by rfl) ⟨1652906, by rfl⟩ : syracuseStep 2203875 = 3305813) B3305813
theorem B6275893 : Blo 2203435 6275893 := bbase (se 5 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 6275893 = 588365) (by norm_num)
theorem B8367857 : Blo 2203435 8367857 := bstep (se 2 (by rfl) ⟨3137946, by rfl⟩ : syracuseStep 8367857 = 6275893) B6275893
theorem B5578571 : Blo 2203435 5578571 := bstep (se 1 (by rfl) ⟨4183928, by rfl⟩ : syracuseStep 5578571 = 8367857) B8367857
theorem B3719047 : Blo 2203435 3719047 := bstep (se 1 (by rfl) ⟨2789285, by rfl⟩ : syracuseStep 3719047 = 5578571) B5578571
theorem B4958729 : Blo 2203435 4958729 := bstep (se 2 (by rfl) ⟨1859523, by rfl⟩ : syracuseStep 4958729 = 3719047) B3719047
theorem B3305819 : Blo 2203435 3305819 := bstep (se 1 (by rfl) ⟨2479364, by rfl⟩ : syracuseStep 3305819 = 4958729) B4958729
theorem B2203879 : Blo 2203435 2203879 := bstep (se 1 (by rfl) ⟨1652909, by rfl⟩ : syracuseStep 2203879 = 3305819) B3305819
theorem B2479369 : Blo 2203435 2479369 := bbase (se 2 (by rfl) ⟨929763, by rfl⟩ : syracuseStep 2479369 = 1859527) (by norm_num)
theorem B3305825 : Blo 2203435 3305825 := bstep (se 2 (by rfl) ⟨1239684, by rfl⟩ : syracuseStep 3305825 = 2479369) B2479369
theorem B2203883 : Blo 2203435 2203883 := bstep (se 1 (by rfl) ⟨1652912, by rfl⟩ : syracuseStep 2203883 = 3305825) B3305825
theorem B28241621 : Blo 2203435 28241621 := bbase (se 7 (by rfl) ⟨330956, by rfl⟩ : syracuseStep 28241621 = 661913) (by norm_num)
theorem B18827747 : Blo 2203435 18827747 := bstep (se 1 (by rfl) ⟨14120810, by rfl⟩ : syracuseStep 18827747 = 28241621) B28241621
theorem B12551831 : Blo 2203435 12551831 := bstep (se 1 (by rfl) ⟨9413873, by rfl⟩ : syracuseStep 12551831 = 18827747) B18827747
theorem B8367887 : Blo 2203435 8367887 := bstep (se 1 (by rfl) ⟨6275915, by rfl⟩ : syracuseStep 8367887 = 12551831) B12551831
theorem B5578591 : Blo 2203435 5578591 := bstep (se 1 (by rfl) ⟨4183943, by rfl⟩ : syracuseStep 5578591 = 8367887) B8367887
theorem B7438121 : Blo 2203435 7438121 := bstep (se 2 (by rfl) ⟨2789295, by rfl⟩ : syracuseStep 7438121 = 5578591) B5578591
theorem B4958747 : Blo 2203435 4958747 := bstep (se 1 (by rfl) ⟨3719060, by rfl⟩ : syracuseStep 4958747 = 7438121) B7438121
theorem B3305831 : Blo 2203435 3305831 := bstep (se 1 (by rfl) ⟨2479373, by rfl⟩ : syracuseStep 3305831 = 4958747) B4958747
theorem B2203887 : Blo 2203435 2203887 := bstep (se 1 (by rfl) ⟨1652915, by rfl⟩ : syracuseStep 2203887 = 3305831) B3305831
theorem B3305837 : Blo 2203435 3305837 := bbase (se 3 (by rfl) ⟨619844, by rfl⟩ : syracuseStep 3305837 = 1239689) (by norm_num)
theorem B2203891 : Blo 2203435 2203891 := bstep (se 1 (by rfl) ⟨1652918, by rfl⟩ : syracuseStep 2203891 = 3305837) B3305837
theorem B4958765 : Blo 2203435 4958765 := bbase (se 3 (by rfl) ⟨929768, by rfl⟩ : syracuseStep 4958765 = 1859537) (by norm_num)
theorem B3305843 : Blo 2203435 3305843 := bstep (se 1 (by rfl) ⟨2479382, by rfl⟩ : syracuseStep 3305843 = 4958765) B4958765
theorem B2203895 : Blo 2203435 2203895 := bstep (se 1 (by rfl) ⟨1652921, by rfl⟩ : syracuseStep 2203895 = 3305843) B3305843
theorem B8935877 : Blo 2203435 8935877 := bbase (se 4 (by rfl) ⟨837738, by rfl⟩ : syracuseStep 8935877 = 1675477) (by norm_num)
theorem B23829005 : Blo 2203435 23829005 := bstep (se 3 (by rfl) ⟨4467938, by rfl⟩ : syracuseStep 23829005 = 8935877) B8935877
theorem B15886003 : Blo 2203435 15886003 := bstep (se 1 (by rfl) ⟨11914502, by rfl⟩ : syracuseStep 15886003 = 23829005) B23829005
theorem B21181337 : Blo 2203435 21181337 := bstep (se 2 (by rfl) ⟨7943001, by rfl⟩ : syracuseStep 21181337 = 15886003) B15886003
theorem B14120891 : Blo 2203435 14120891 := bstep (se 1 (by rfl) ⟨10590668, by rfl⟩ : syracuseStep 14120891 = 21181337) B21181337
theorem B9413927 : Blo 2203435 9413927 := bstep (se 1 (by rfl) ⟨7060445, by rfl⟩ : syracuseStep 9413927 = 14120891) B14120891
theorem B6275951 : Blo 2203435 6275951 := bstep (se 1 (by rfl) ⟨4706963, by rfl⟩ : syracuseStep 6275951 = 9413927) B9413927
theorem B4183967 : Blo 2203435 4183967 := bstep (se 1 (by rfl) ⟨3137975, by rfl⟩ : syracuseStep 4183967 = 6275951) B6275951
theorem B2789311 : Blo 2203435 2789311 := bstep (se 1 (by rfl) ⟨2091983, by rfl⟩ : syracuseStep 2789311 = 4183967) B4183967
theorem B3719081 : Blo 2203435 3719081 := bstep (se 2 (by rfl) ⟨1394655, by rfl⟩ : syracuseStep 3719081 = 2789311) B2789311
theorem B2479387 : Blo 2203435 2479387 := bstep (se 1 (by rfl) ⟨1859540, by rfl⟩ : syracuseStep 2479387 = 3719081) B3719081
theorem B3305849 : Blo 2203435 3305849 := bstep (se 2 (by rfl) ⟨1239693, by rfl⟩ : syracuseStep 3305849 = 2479387) B2479387
theorem B2203899 : Blo 2203435 2203899 := bstep (se 1 (by rfl) ⟨1652924, by rfl⟩ : syracuseStep 2203899 = 3305849) B3305849
theorem B37655765 : Blo 2203435 37655765 := bbase (se 7 (by rfl) ⟨441278, by rfl⟩ : syracuseStep 37655765 = 882557) (by norm_num)
theorem B25103843 : Blo 2203435 25103843 := bstep (se 1 (by rfl) ⟨18827882, by rfl⟩ : syracuseStep 25103843 = 37655765) B37655765
theorem B16735895 : Blo 2203435 16735895 := bstep (se 1 (by rfl) ⟨12551921, by rfl⟩ : syracuseStep 16735895 = 25103843) B25103843
theorem B11157263 : Blo 2203435 11157263 := bstep (se 1 (by rfl) ⟨8367947, by rfl⟩ : syracuseStep 11157263 = 16735895) B16735895
theorem B7438175 : Blo 2203435 7438175 := bstep (se 1 (by rfl) ⟨5578631, by rfl⟩ : syracuseStep 7438175 = 11157263) B11157263
theorem B4958783 : Blo 2203435 4958783 := bstep (se 1 (by rfl) ⟨3719087, by rfl⟩ : syracuseStep 4958783 = 7438175) B7438175
theorem B3305855 : Blo 2203435 3305855 := bstep (se 1 (by rfl) ⟨2479391, by rfl⟩ : syracuseStep 3305855 = 4958783) B4958783
theorem B2203903 : Blo 2203435 2203903 := bstep (se 1 (by rfl) ⟨1652927, by rfl⟩ : syracuseStep 2203903 = 3305855) B3305855
theorem B3305861 : Blo 2203435 3305861 := bbase (se 4 (by rfl) ⟨309924, by rfl⟩ : syracuseStep 3305861 = 619849) (by norm_num)
theorem B2203907 : Blo 2203435 2203907 := bstep (se 1 (by rfl) ⟨1652930, by rfl⟩ : syracuseStep 2203907 = 3305861) B3305861
theorem B3719101 : Blo 2203435 3719101 := bbase (se 3 (by rfl) ⟨697331, by rfl⟩ : syracuseStep 3719101 = 1394663) (by norm_num)
theorem B4958801 : Blo 2203435 4958801 := bstep (se 2 (by rfl) ⟨1859550, by rfl⟩ : syracuseStep 4958801 = 3719101) B3719101
theorem B3305867 : Blo 2203435 3305867 := bstep (se 1 (by rfl) ⟨2479400, by rfl⟩ : syracuseStep 3305867 = 4958801) B4958801
theorem B2203911 : Blo 2203435 2203911 := bstep (se 1 (by rfl) ⟨1652933, by rfl⟩ : syracuseStep 2203911 = 3305867) B3305867
theorem B2479405 : Blo 2203435 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B3305873 : Blo 2203435 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B2203915 : Blo 2203435 2203915 := bstep (se 1 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 2203915 = 3305873) B3305873
theorem B7438229 : Blo 2203435 7438229 := bbase (se 6 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 7438229 = 348667) (by norm_num)
theorem B4958819 : Blo 2203435 4958819 := bstep (se 1 (by rfl) ⟨3719114, by rfl⟩ : syracuseStep 4958819 = 7438229) B7438229
theorem B3305879 : Blo 2203435 3305879 := bstep (se 1 (by rfl) ⟨2479409, by rfl⟩ : syracuseStep 3305879 = 4958819) B4958819
theorem B2203919 : Blo 2203435 2203919 := bstep (se 1 (by rfl) ⟨1652939, by rfl⟩ : syracuseStep 2203919 = 3305879) B3305879
theorem B3305885 : Blo 2203435 3305885 := bbase (se 3 (by rfl) ⟨619853, by rfl⟩ : syracuseStep 3305885 = 1239707) (by norm_num)
theorem B2203923 : Blo 2203435 2203923 := bstep (se 1 (by rfl) ⟨1652942, by rfl⟩ : syracuseStep 2203923 = 3305885) B3305885
theorem B4958837 : Blo 2203435 4958837 := bbase (se 5 (by rfl) ⟨232445, by rfl⟩ : syracuseStep 4958837 = 464891) (by norm_num)
theorem B3305891 : Blo 2203435 3305891 := bstep (se 1 (by rfl) ⟨2479418, by rfl⟩ : syracuseStep 3305891 = 4958837) B4958837
theorem B2203927 : Blo 2203435 2203927 := bstep (se 1 (by rfl) ⟨1652945, by rfl⟩ : syracuseStep 2203927 = 3305891) B3305891
theorem B10590821 : Blo 2203435 10590821 := bbase (se 4 (by rfl) ⟨992889, by rfl⟩ : syracuseStep 10590821 = 1985779) (by norm_num)
theorem B7060547 : Blo 2203435 7060547 := bstep (se 1 (by rfl) ⟨5295410, by rfl⟩ : syracuseStep 7060547 = 10590821) B10590821
theorem B18828125 : Blo 2203435 18828125 := bstep (se 3 (by rfl) ⟨3530273, by rfl⟩ : syracuseStep 18828125 = 7060547) B7060547
theorem B12552083 : Blo 2203435 12552083 := bstep (se 1 (by rfl) ⟨9414062, by rfl⟩ : syracuseStep 12552083 = 18828125) B18828125
theorem B8368055 : Blo 2203435 8368055 := bstep (se 1 (by rfl) ⟨6276041, by rfl⟩ : syracuseStep 8368055 = 12552083) B12552083
theorem B5578703 : Blo 2203435 5578703 := bstep (se 1 (by rfl) ⟨4184027, by rfl⟩ : syracuseStep 5578703 = 8368055) B8368055
theorem B3719135 : Blo 2203435 3719135 := bstep (se 1 (by rfl) ⟨2789351, by rfl⟩ : syracuseStep 3719135 = 5578703) B5578703
theorem B2479423 : Blo 2203435 2479423 := bstep (se 1 (by rfl) ⟨1859567, by rfl⟩ : syracuseStep 2479423 = 3719135) B3719135
theorem B3305897 : Blo 2203435 3305897 := bstep (se 2 (by rfl) ⟨1239711, by rfl⟩ : syracuseStep 3305897 = 2479423) B2479423
theorem B2203931 : Blo 2203435 2203931 := bstep (se 1 (by rfl) ⟨1652948, by rfl⟩ : syracuseStep 2203931 = 3305897) B3305897
theorem B8368069 : Blo 2203435 8368069 := bbase (se 4 (by rfl) ⟨784506, by rfl⟩ : syracuseStep 8368069 = 1569013) (by norm_num)
theorem B11157425 : Blo 2203435 11157425 := bstep (se 2 (by rfl) ⟨4184034, by rfl⟩ : syracuseStep 11157425 = 8368069) B8368069
theorem B7438283 : Blo 2203435 7438283 := bstep (se 1 (by rfl) ⟨5578712, by rfl⟩ : syracuseStep 7438283 = 11157425) B11157425
theorem B4958855 : Blo 2203435 4958855 := bstep (se 1 (by rfl) ⟨3719141, by rfl⟩ : syracuseStep 4958855 = 7438283) B7438283
theorem B3305903 : Blo 2203435 3305903 := bstep (se 1 (by rfl) ⟨2479427, by rfl⟩ : syracuseStep 3305903 = 4958855) B4958855
theorem B2203935 : Blo 2203435 2203935 := bstep (se 1 (by rfl) ⟨1652951, by rfl⟩ : syracuseStep 2203935 = 3305903) B3305903
theorem B3305909 : Blo 2203435 3305909 := bbase (se 5 (by rfl) ⟨154964, by rfl⟩ : syracuseStep 3305909 = 309929) (by norm_num)
theorem B2203939 : Blo 2203435 2203939 := bstep (se 1 (by rfl) ⟨1652954, by rfl⟩ : syracuseStep 2203939 = 3305909) B3305909
theorem B5578733 : Blo 2203435 5578733 := bbase (se 3 (by rfl) ⟨1046012, by rfl⟩ : syracuseStep 5578733 = 2092025) (by norm_num)
theorem B3719155 : Blo 2203435 3719155 := bstep (se 1 (by rfl) ⟨2789366, by rfl⟩ : syracuseStep 3719155 = 5578733) B5578733
theorem B4958873 : Blo 2203435 4958873 := bstep (se 2 (by rfl) ⟨1859577, by rfl⟩ : syracuseStep 4958873 = 3719155) B3719155
theorem B3305915 : Blo 2203435 3305915 := bstep (se 1 (by rfl) ⟨2479436, by rfl⟩ : syracuseStep 3305915 = 4958873) B4958873
theorem B2203943 : Blo 2203435 2203943 := bstep (se 1 (by rfl) ⟨1652957, by rfl⟩ : syracuseStep 2203943 = 3305915) B3305915
theorem B2479441 : Blo 2203435 2479441 := bbase (se 2 (by rfl) ⟨929790, by rfl⟩ : syracuseStep 2479441 = 1859581) (by norm_num)
theorem B3305921 : Blo 2203435 3305921 := bstep (se 2 (by rfl) ⟨1239720, by rfl⟩ : syracuseStep 3305921 = 2479441) B2479441
theorem B2203947 : Blo 2203435 2203947 := bstep (se 1 (by rfl) ⟨1652960, by rfl⟩ : syracuseStep 2203947 = 3305921) B3305921
theorem B2353537 : Blo 2203435 2353537 := bbase (se 2 (by rfl) ⟨882576, by rfl⟩ : syracuseStep 2353537 = 1765153) (by norm_num)
theorem B3138049 : Blo 2203435 3138049 := bstep (se 2 (by rfl) ⟨1176768, by rfl⟩ : syracuseStep 3138049 = 2353537) B2353537
theorem B4184065 : Blo 2203435 4184065 := bstep (se 2 (by rfl) ⟨1569024, by rfl⟩ : syracuseStep 4184065 = 3138049) B3138049
theorem B5578753 : Blo 2203435 5578753 := bstep (se 2 (by rfl) ⟨2092032, by rfl⟩ : syracuseStep 5578753 = 4184065) B4184065
theorem B7438337 : Blo 2203435 7438337 := bstep (se 2 (by rfl) ⟨2789376, by rfl⟩ : syracuseStep 7438337 = 5578753) B5578753
theorem B4958891 : Blo 2203435 4958891 := bstep (se 1 (by rfl) ⟨3719168, by rfl⟩ : syracuseStep 4958891 = 7438337) B7438337
theorem B3305927 : Blo 2203435 3305927 := bstep (se 1 (by rfl) ⟨2479445, by rfl⟩ : syracuseStep 3305927 = 4958891) B4958891
theorem B2203951 : Blo 2203435 2203951 := bstep (se 1 (by rfl) ⟨1652963, by rfl⟩ : syracuseStep 2203951 = 3305927) B3305927
theorem B3305933 : Blo 2203435 3305933 := bbase (se 3 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 3305933 = 1239725) (by norm_num)
theorem B2203955 : Blo 2203435 2203955 := bstep (se 1 (by rfl) ⟨1652966, by rfl⟩ : syracuseStep 2203955 = 3305933) B3305933
theorem B4958909 : Blo 2203435 4958909 := bbase (se 3 (by rfl) ⟨929795, by rfl⟩ : syracuseStep 4958909 = 1859591) (by norm_num)
theorem B3305939 : Blo 2203435 3305939 := bstep (se 1 (by rfl) ⟨2479454, by rfl⟩ : syracuseStep 3305939 = 4958909) B4958909
theorem B2203959 : Blo 2203435 2203959 := bstep (se 1 (by rfl) ⟨1652969, by rfl⟩ : syracuseStep 2203959 = 3305939) B3305939
theorem B3719189 : Blo 2203435 3719189 := bbase (se 6 (by rfl) ⟨87168, by rfl⟩ : syracuseStep 3719189 = 174337) (by norm_num)
theorem B2479459 : Blo 2203435 2479459 := bstep (se 1 (by rfl) ⟨1859594, by rfl⟩ : syracuseStep 2479459 = 3719189) B3719189
theorem B3305945 : Blo 2203435 3305945 := bstep (se 2 (by rfl) ⟨1239729, by rfl⟩ : syracuseStep 3305945 = 2479459) B2479459
theorem B2203963 : Blo 2203435 2203963 := bstep (se 1 (by rfl) ⟨1652972, by rfl⟩ : syracuseStep 2203963 = 3305945) B3305945
theorem B5654909 : Blo 2203435 5654909 := bbase (se 3 (by rfl) ⟨1060295, by rfl⟩ : syracuseStep 5654909 = 2120591) (by norm_num)
theorem B3769939 : Blo 2203435 3769939 := bstep (se 1 (by rfl) ⟨2827454, by rfl⟩ : syracuseStep 3769939 = 5654909) B5654909
theorem B5026585 : Blo 2203435 5026585 := bstep (se 2 (by rfl) ⟨1884969, by rfl⟩ : syracuseStep 5026585 = 3769939) B3769939
theorem B6702113 : Blo 2203435 6702113 := bstep (se 2 (by rfl) ⟨2513292, by rfl⟩ : syracuseStep 6702113 = 5026585) B5026585
theorem B17872301 : Blo 2203435 17872301 := bstep (se 3 (by rfl) ⟨3351056, by rfl⟩ : syracuseStep 17872301 = 6702113) B6702113
theorem B11914867 : Blo 2203435 11914867 := bstep (se 1 (by rfl) ⟨8936150, by rfl⟩ : syracuseStep 11914867 = 17872301) B17872301
theorem B15886489 : Blo 2203435 15886489 := bstep (se 2 (by rfl) ⟨5957433, by rfl⟩ : syracuseStep 15886489 = 11914867) B11914867
theorem B21181985 : Blo 2203435 21181985 := bstep (se 2 (by rfl) ⟨7943244, by rfl⟩ : syracuseStep 21181985 = 15886489) B15886489
theorem B14121323 : Blo 2203435 14121323 := bstep (se 1 (by rfl) ⟨10590992, by rfl⟩ : syracuseStep 14121323 = 21181985) B21181985
theorem B9414215 : Blo 2203435 9414215 := bstep (se 1 (by rfl) ⟨7060661, by rfl⟩ : syracuseStep 9414215 = 14121323) B14121323
theorem B6276143 : Blo 2203435 6276143 := bstep (se 1 (by rfl) ⟨4707107, by rfl⟩ : syracuseStep 6276143 = 9414215) B9414215
theorem B16736381 : Blo 2203435 16736381 := bstep (se 3 (by rfl) ⟨3138071, by rfl⟩ : syracuseStep 16736381 = 6276143) B6276143
theorem B11157587 : Blo 2203435 11157587 := bstep (se 1 (by rfl) ⟨8368190, by rfl⟩ : syracuseStep 11157587 = 16736381) B16736381
theorem B7438391 : Blo 2203435 7438391 := bstep (se 1 (by rfl) ⟨5578793, by rfl⟩ : syracuseStep 7438391 = 11157587) B11157587
theorem B4958927 : Blo 2203435 4958927 := bstep (se 1 (by rfl) ⟨3719195, by rfl⟩ : syracuseStep 4958927 = 7438391) B7438391
theorem B3305951 : Blo 2203435 3305951 := bstep (se 1 (by rfl) ⟨2479463, by rfl⟩ : syracuseStep 3305951 = 4958927) B4958927
theorem B2203967 : Blo 2203435 2203967 := bstep (se 1 (by rfl) ⟨1652975, by rfl⟩ : syracuseStep 2203967 = 3305951) B3305951
theorem B3305957 : Blo 2203435 3305957 := bbase (se 4 (by rfl) ⟨309933, by rfl⟩ : syracuseStep 3305957 = 619867) (by norm_num)
theorem B2203971 : Blo 2203435 2203971 := bstep (se 1 (by rfl) ⟨1652978, by rfl⟩ : syracuseStep 2203971 = 3305957) B3305957
theorem B11309861 : Blo 2203435 11309861 := bbase (se 4 (by rfl) ⟨1060299, by rfl⟩ : syracuseStep 11309861 = 2120599) (by norm_num)
theorem B7539907 : Blo 2203435 7539907 := bstep (se 1 (by rfl) ⟨5654930, by rfl⟩ : syracuseStep 7539907 = 11309861) B11309861
theorem B10053209 : Blo 2203435 10053209 := bstep (se 2 (by rfl) ⟨3769953, by rfl⟩ : syracuseStep 10053209 = 7539907) B7539907
theorem B6702139 : Blo 2203435 6702139 := bstep (se 1 (by rfl) ⟨5026604, by rfl⟩ : syracuseStep 6702139 = 10053209) B10053209
theorem B8936185 : Blo 2203435 8936185 := bstep (se 2 (by rfl) ⟨3351069, by rfl⟩ : syracuseStep 8936185 = 6702139) B6702139
theorem B11914913 : Blo 2203435 11914913 := bstep (se 2 (by rfl) ⟨4468092, by rfl⟩ : syracuseStep 11914913 = 8936185) B8936185
theorem B7943275 : Blo 2203435 7943275 := bstep (se 1 (by rfl) ⟨5957456, by rfl⟩ : syracuseStep 7943275 = 11914913) B11914913
theorem B10591033 : Blo 2203435 10591033 := bstep (se 2 (by rfl) ⟨3971637, by rfl⟩ : syracuseStep 10591033 = 7943275) B7943275
theorem B14121377 : Blo 2203435 14121377 := bstep (se 2 (by rfl) ⟨5295516, by rfl⟩ : syracuseStep 14121377 = 10591033) B10591033
theorem B9414251 : Blo 2203435 9414251 := bstep (se 1 (by rfl) ⟨7060688, by rfl⟩ : syracuseStep 9414251 = 14121377) B14121377
theorem B6276167 : Blo 2203435 6276167 := bstep (se 1 (by rfl) ⟨4707125, by rfl⟩ : syracuseStep 6276167 = 9414251) B9414251
theorem B4184111 : Blo 2203435 4184111 := bstep (se 1 (by rfl) ⟨3138083, by rfl⟩ : syracuseStep 4184111 = 6276167) B6276167
theorem B2789407 : Blo 2203435 2789407 := bstep (se 1 (by rfl) ⟨2092055, by rfl⟩ : syracuseStep 2789407 = 4184111) B4184111
theorem B3719209 : Blo 2203435 3719209 := bstep (se 2 (by rfl) ⟨1394703, by rfl⟩ : syracuseStep 3719209 = 2789407) B2789407
theorem B4958945 : Blo 2203435 4958945 := bstep (se 2 (by rfl) ⟨1859604, by rfl⟩ : syracuseStep 4958945 = 3719209) B3719209
theorem B3305963 : Blo 2203435 3305963 := bstep (se 1 (by rfl) ⟨2479472, by rfl⟩ : syracuseStep 3305963 = 4958945) B4958945
theorem B2203975 : Blo 2203435 2203975 := bstep (se 1 (by rfl) ⟨1652981, by rfl⟩ : syracuseStep 2203975 = 3305963) B3305963
theorem B2479477 : Blo 2203435 2479477 := bbase (se 5 (by rfl) ⟨116225, by rfl⟩ : syracuseStep 2479477 = 232451) (by norm_num)
theorem B3305969 : Blo 2203435 3305969 := bstep (se 2 (by rfl) ⟨1239738, by rfl⟩ : syracuseStep 3305969 = 2479477) B2479477
theorem B2203979 : Blo 2203435 2203979 := bstep (se 1 (by rfl) ⟨1652984, by rfl⟩ : syracuseStep 2203979 = 3305969) B3305969
theorem B2789417 : Blo 2203435 2789417 := bbase (se 2 (by rfl) ⟨1046031, by rfl⟩ : syracuseStep 2789417 = 2092063) (by norm_num)
theorem B7438445 : Blo 2203435 7438445 := bstep (se 3 (by rfl) ⟨1394708, by rfl⟩ : syracuseStep 7438445 = 2789417) B2789417
theorem B4958963 : Blo 2203435 4958963 := bstep (se 1 (by rfl) ⟨3719222, by rfl⟩ : syracuseStep 4958963 = 7438445) B7438445
theorem B3305975 : Blo 2203435 3305975 := bstep (se 1 (by rfl) ⟨2479481, by rfl⟩ : syracuseStep 3305975 = 4958963) B4958963
theorem B2203983 : Blo 2203435 2203983 := bstep (se 1 (by rfl) ⟨1652987, by rfl⟩ : syracuseStep 2203983 = 3305975) B3305975
theorem B3305981 : Blo 2203435 3305981 := bbase (se 3 (by rfl) ⟨619871, by rfl⟩ : syracuseStep 3305981 = 1239743) (by norm_num)
theorem B2203987 : Blo 2203435 2203987 := bstep (se 1 (by rfl) ⟨1652990, by rfl⟩ : syracuseStep 2203987 = 3305981) B3305981
theorem B4958981 : Blo 2203435 4958981 := bbase (se 4 (by rfl) ⟨464904, by rfl⟩ : syracuseStep 4958981 = 929809) (by norm_num)
theorem B3305987 : Blo 2203435 3305987 := bstep (se 1 (by rfl) ⟨2479490, by rfl⟩ : syracuseStep 3305987 = 4958981) B4958981
theorem B2203991 : Blo 2203435 2203991 := bstep (se 1 (by rfl) ⟨1652993, by rfl⟩ : syracuseStep 2203991 = 3305987) B3305987
theorem B4184149 : Blo 2203435 4184149 := bbase (se 8 (by rfl) ⟨24516, by rfl⟩ : syracuseStep 4184149 = 49033) (by norm_num)
theorem B5578865 : Blo 2203435 5578865 := bstep (se 2 (by rfl) ⟨2092074, by rfl⟩ : syracuseStep 5578865 = 4184149) B4184149
theorem B3719243 : Blo 2203435 3719243 := bstep (se 1 (by rfl) ⟨2789432, by rfl⟩ : syracuseStep 3719243 = 5578865) B5578865
theorem B2479495 : Blo 2203435 2479495 := bstep (se 1 (by rfl) ⟨1859621, by rfl⟩ : syracuseStep 2479495 = 3719243) B3719243
theorem B3305993 : Blo 2203435 3305993 := bstep (se 2 (by rfl) ⟨1239747, by rfl⟩ : syracuseStep 3305993 = 2479495) B2479495
theorem B2203995 : Blo 2203435 2203995 := bstep (se 1 (by rfl) ⟨1652996, by rfl⟩ : syracuseStep 2203995 = 3305993) B3305993
theorem B11157749 : Blo 2203435 11157749 := bbase (se 5 (by rfl) ⟨523019, by rfl⟩ : syracuseStep 11157749 = 1046039) (by norm_num)
theorem B7438499 : Blo 2203435 7438499 := bstep (se 1 (by rfl) ⟨5578874, by rfl⟩ : syracuseStep 7438499 = 11157749) B11157749
theorem B4958999 : Blo 2203435 4958999 := bstep (se 1 (by rfl) ⟨3719249, by rfl⟩ : syracuseStep 4958999 = 7438499) B7438499
theorem B3305999 : Blo 2203435 3305999 := bstep (se 1 (by rfl) ⟨2479499, by rfl⟩ : syracuseStep 3305999 = 4958999) B4958999
theorem B2203999 : Blo 2203435 2203999 := bstep (se 1 (by rfl) ⟨1652999, by rfl⟩ : syracuseStep 2203999 = 3305999) B3305999
theorem B3306005 : Blo 2203435 3306005 := bbase (se 6 (by rfl) ⟨77484, by rfl⟩ : syracuseStep 3306005 = 154969) (by norm_num)
theorem B2204003 : Blo 2203435 2204003 := bstep (se 1 (by rfl) ⟨1653002, by rfl⟩ : syracuseStep 2204003 = 3306005) B3306005
theorem B5367845 : Blo 2203435 5367845 := bbase (se 4 (by rfl) ⟨503235, by rfl⟩ : syracuseStep 5367845 = 1006471) (by norm_num)
theorem B3578563 : Blo 2203435 3578563 := bstep (se 1 (by rfl) ⟨2683922, by rfl⟩ : syracuseStep 3578563 = 5367845) B5367845
theorem B19085669 : Blo 2203435 19085669 := bstep (se 4 (by rfl) ⟨1789281, by rfl⟩ : syracuseStep 19085669 = 3578563) B3578563
theorem B12723779 : Blo 2203435 12723779 := bstep (se 1 (by rfl) ⟨9542834, by rfl⟩ : syracuseStep 12723779 = 19085669) B19085669
theorem B8482519 : Blo 2203435 8482519 := bstep (se 1 (by rfl) ⟨6361889, by rfl⟩ : syracuseStep 8482519 = 12723779) B12723779
theorem B11310025 : Blo 2203435 11310025 := bstep (se 2 (by rfl) ⟨4241259, by rfl⟩ : syracuseStep 11310025 = 8482519) B8482519
theorem B15080033 : Blo 2203435 15080033 := bstep (se 2 (by rfl) ⟨5655012, by rfl⟩ : syracuseStep 15080033 = 11310025) B11310025
theorem B10053355 : Blo 2203435 10053355 := bstep (se 1 (by rfl) ⟨7540016, by rfl⟩ : syracuseStep 10053355 = 15080033) B15080033
theorem B13404473 : Blo 2203435 13404473 := bstep (se 2 (by rfl) ⟨5026677, by rfl⟩ : syracuseStep 13404473 = 10053355) B10053355
theorem B8936315 : Blo 2203435 8936315 := bstep (se 1 (by rfl) ⟨6702236, by rfl⟩ : syracuseStep 8936315 = 13404473) B13404473
theorem B5957543 : Blo 2203435 5957543 := bstep (se 1 (by rfl) ⟨4468157, by rfl⟩ : syracuseStep 5957543 = 8936315) B8936315
theorem B3971695 : Blo 2203435 3971695 := bstep (se 1 (by rfl) ⟨2978771, by rfl⟩ : syracuseStep 3971695 = 5957543) B5957543
theorem B5295593 : Blo 2203435 5295593 := bstep (se 2 (by rfl) ⟨1985847, by rfl⟩ : syracuseStep 5295593 = 3971695) B3971695
theorem B3530395 : Blo 2203435 3530395 := bstep (se 1 (by rfl) ⟨2647796, by rfl⟩ : syracuseStep 3530395 = 5295593) B5295593
theorem B18828773 : Blo 2203435 18828773 := bstep (se 4 (by rfl) ⟨1765197, by rfl⟩ : syracuseStep 18828773 = 3530395) B3530395
theorem B12552515 : Blo 2203435 12552515 := bstep (se 1 (by rfl) ⟨9414386, by rfl⟩ : syracuseStep 12552515 = 18828773) B18828773
theorem B8368343 : Blo 2203435 8368343 := bstep (se 1 (by rfl) ⟨6276257, by rfl⟩ : syracuseStep 8368343 = 12552515) B12552515
theorem B5578895 : Blo 2203435 5578895 := bstep (se 1 (by rfl) ⟨4184171, by rfl⟩ : syracuseStep 5578895 = 8368343) B8368343
theorem B3719263 : Blo 2203435 3719263 := bstep (se 1 (by rfl) ⟨2789447, by rfl⟩ : syracuseStep 3719263 = 5578895) B5578895
theorem B4959017 : Blo 2203435 4959017 := bstep (se 2 (by rfl) ⟨1859631, by rfl⟩ : syracuseStep 4959017 = 3719263) B3719263
theorem B3306011 : Blo 2203435 3306011 := bstep (se 1 (by rfl) ⟨2479508, by rfl⟩ : syracuseStep 3306011 = 4959017) B4959017
theorem B2204007 : Blo 2203435 2204007 := bstep (se 1 (by rfl) ⟨1653005, by rfl⟩ : syracuseStep 2204007 = 3306011) B3306011
theorem B2479513 : Blo 2203435 2479513 := bbase (se 2 (by rfl) ⟨929817, by rfl⟩ : syracuseStep 2479513 = 1859635) (by norm_num)
theorem B3306017 : Blo 2203435 3306017 := bstep (se 2 (by rfl) ⟨1239756, by rfl⟩ : syracuseStep 3306017 = 2479513) B2479513
theorem B2204011 : Blo 2203435 2204011 := bstep (se 1 (by rfl) ⟨1653008, by rfl⟩ : syracuseStep 2204011 = 3306017) B3306017
theorem B8368373 : Blo 2203435 8368373 := bbase (se 5 (by rfl) ⟨392267, by rfl⟩ : syracuseStep 8368373 = 784535) (by norm_num)
theorem B5578915 : Blo 2203435 5578915 := bstep (se 1 (by rfl) ⟨4184186, by rfl⟩ : syracuseStep 5578915 = 8368373) B8368373
theorem B7438553 : Blo 2203435 7438553 := bstep (se 2 (by rfl) ⟨2789457, by rfl⟩ : syracuseStep 7438553 = 5578915) B5578915
theorem B4959035 : Blo 2203435 4959035 := bstep (se 1 (by rfl) ⟨3719276, by rfl⟩ : syracuseStep 4959035 = 7438553) B7438553
theorem B3306023 : Blo 2203435 3306023 := bstep (se 1 (by rfl) ⟨2479517, by rfl⟩ : syracuseStep 3306023 = 4959035) B4959035
theorem B2204015 : Blo 2203435 2204015 := bstep (se 1 (by rfl) ⟨1653011, by rfl⟩ : syracuseStep 2204015 = 3306023) B3306023
theorem B3306029 : Blo 2203435 3306029 := bbase (se 3 (by rfl) ⟨619880, by rfl⟩ : syracuseStep 3306029 = 1239761) (by norm_num)
theorem B2204019 : Blo 2203435 2204019 := bstep (se 1 (by rfl) ⟨1653014, by rfl⟩ : syracuseStep 2204019 = 3306029) B3306029
theorem B4959053 : Blo 2203435 4959053 := bbase (se 3 (by rfl) ⟨929822, by rfl⟩ : syracuseStep 4959053 = 1859645) (by norm_num)
theorem B3306035 : Blo 2203435 3306035 := bstep (se 1 (by rfl) ⟨2479526, by rfl⟩ : syracuseStep 3306035 = 4959053) B4959053
theorem B2204023 : Blo 2203435 2204023 := bstep (se 1 (by rfl) ⟨1653017, by rfl⟩ : syracuseStep 2204023 = 3306035) B3306035
theorem B2789473 : Blo 2203435 2789473 := bbase (se 2 (by rfl) ⟨1046052, by rfl⟩ : syracuseStep 2789473 = 2092105) (by norm_num)
theorem B3719297 : Blo 2203435 3719297 := bstep (se 2 (by rfl) ⟨1394736, by rfl⟩ : syracuseStep 3719297 = 2789473) B2789473
theorem B2479531 : Blo 2203435 2479531 := bstep (se 1 (by rfl) ⟨1859648, by rfl⟩ : syracuseStep 2479531 = 3719297) B3719297
theorem B3306041 : Blo 2203435 3306041 := bstep (se 2 (by rfl) ⟨1239765, by rfl⟩ : syracuseStep 3306041 = 2479531) B2479531
theorem B2204027 : Blo 2203435 2204027 := bstep (se 1 (by rfl) ⟨1653020, by rfl⟩ : syracuseStep 2204027 = 3306041) B3306041
theorem B25105301 : Blo 2203435 25105301 := bbase (se 6 (by rfl) ⟨588405, by rfl⟩ : syracuseStep 25105301 = 1176811) (by norm_num)
theorem B16736867 : Blo 2203435 16736867 := bstep (se 1 (by rfl) ⟨12552650, by rfl⟩ : syracuseStep 16736867 = 25105301) B25105301
theorem B11157911 : Blo 2203435 11157911 := bstep (se 1 (by rfl) ⟨8368433, by rfl⟩ : syracuseStep 11157911 = 16736867) B16736867
theorem B7438607 : Blo 2203435 7438607 := bstep (se 1 (by rfl) ⟨5578955, by rfl⟩ : syracuseStep 7438607 = 11157911) B11157911
theorem B4959071 : Blo 2203435 4959071 := bstep (se 1 (by rfl) ⟨3719303, by rfl⟩ : syracuseStep 4959071 = 7438607) B7438607
theorem B3306047 : Blo 2203435 3306047 := bstep (se 1 (by rfl) ⟨2479535, by rfl⟩ : syracuseStep 3306047 = 4959071) B4959071
theorem B2204031 : Blo 2203435 2204031 := bstep (se 1 (by rfl) ⟨1653023, by rfl⟩ : syracuseStep 2204031 = 3306047) B3306047
theorem B3306053 : Blo 2203435 3306053 := bbase (se 4 (by rfl) ⟨309942, by rfl⟩ : syracuseStep 3306053 = 619885) (by norm_num)
theorem B2204035 : Blo 2203435 2204035 := bstep (se 1 (by rfl) ⟨1653026, by rfl⟩ : syracuseStep 2204035 = 3306053) B3306053
theorem B3719317 : Blo 2203435 3719317 := bbase (se 6 (by rfl) ⟨87171, by rfl⟩ : syracuseStep 3719317 = 174343) (by norm_num)
theorem B4959089 : Blo 2203435 4959089 := bstep (se 2 (by rfl) ⟨1859658, by rfl⟩ : syracuseStep 4959089 = 3719317) B3719317
theorem B3306059 : Blo 2203435 3306059 := bstep (se 1 (by rfl) ⟨2479544, by rfl⟩ : syracuseStep 3306059 = 4959089) B4959089
theorem B2204039 : Blo 2203435 2204039 := bstep (se 1 (by rfl) ⟨1653029, by rfl⟩ : syracuseStep 2204039 = 3306059) B3306059
theorem B2479549 : Blo 2203435 2479549 := bbase (se 3 (by rfl) ⟨464915, by rfl⟩ : syracuseStep 2479549 = 929831) (by norm_num)
theorem B3306065 : Blo 2203435 3306065 := bstep (se 2 (by rfl) ⟨1239774, by rfl⟩ : syracuseStep 3306065 = 2479549) B2479549
theorem B2204043 : Blo 2203435 2204043 := bstep (se 1 (by rfl) ⟨1653032, by rfl⟩ : syracuseStep 2204043 = 3306065) B3306065
theorem B7438661 : Blo 2203435 7438661 := bbase (se 4 (by rfl) ⟨697374, by rfl⟩ : syracuseStep 7438661 = 1394749) (by norm_num)
theorem B4959107 : Blo 2203435 4959107 := bstep (se 1 (by rfl) ⟨3719330, by rfl⟩ : syracuseStep 4959107 = 7438661) B7438661
theorem B3306071 : Blo 2203435 3306071 := bstep (se 1 (by rfl) ⟨2479553, by rfl⟩ : syracuseStep 3306071 = 4959107) B4959107
theorem B2204047 : Blo 2203435 2204047 := bstep (se 1 (by rfl) ⟨1653035, by rfl⟩ : syracuseStep 2204047 = 3306071) B3306071
theorem B3306077 : Blo 2203435 3306077 := bbase (se 3 (by rfl) ⟨619889, by rfl⟩ : syracuseStep 3306077 = 1239779) (by norm_num)
theorem B2204051 : Blo 2203435 2204051 := bstep (se 1 (by rfl) ⟨1653038, by rfl⟩ : syracuseStep 2204051 = 3306077) B3306077
theorem B4959125 : Blo 2203435 4959125 := bbase (se 6 (by rfl) ⟨116229, by rfl⟩ : syracuseStep 4959125 = 232459) (by norm_num)
theorem B3306083 : Blo 2203435 3306083 := bstep (se 1 (by rfl) ⟨2479562, by rfl⟩ : syracuseStep 3306083 = 4959125) B4959125
theorem B2204055 : Blo 2203435 2204055 := bstep (se 1 (by rfl) ⟨1653041, by rfl⟩ : syracuseStep 2204055 = 3306083) B3306083
theorem B11310293 : Blo 2203435 11310293 := bbase (se 7 (by rfl) ⟨132542, by rfl⟩ : syracuseStep 11310293 = 265085) (by norm_num)
theorem B30160781 : Blo 2203435 30160781 := bstep (se 3 (by rfl) ⟨5655146, by rfl⟩ : syracuseStep 30160781 = 11310293) B11310293
theorem B20107187 : Blo 2203435 20107187 := bstep (se 1 (by rfl) ⟨15080390, by rfl⟩ : syracuseStep 20107187 = 30160781) B30160781
theorem B13404791 : Blo 2203435 13404791 := bstep (se 1 (by rfl) ⟨10053593, by rfl⟩ : syracuseStep 13404791 = 20107187) B20107187
theorem B8936527 : Blo 2203435 8936527 := bstep (se 1 (by rfl) ⟨6702395, by rfl⟩ : syracuseStep 8936527 = 13404791) B13404791
theorem B11915369 : Blo 2203435 11915369 := bstep (se 2 (by rfl) ⟨4468263, by rfl⟩ : syracuseStep 11915369 = 8936527) B8936527
theorem B7943579 : Blo 2203435 7943579 := bstep (se 1 (by rfl) ⟨5957684, by rfl⟩ : syracuseStep 7943579 = 11915369) B11915369
theorem B5295719 : Blo 2203435 5295719 := bstep (se 1 (by rfl) ⟨3971789, by rfl⟩ : syracuseStep 5295719 = 7943579) B7943579
theorem B3530479 : Blo 2203435 3530479 := bstep (se 1 (by rfl) ⟨2647859, by rfl⟩ : syracuseStep 3530479 = 5295719) B5295719
theorem B4707305 : Blo 2203435 4707305 := bstep (se 2 (by rfl) ⟨1765239, by rfl⟩ : syracuseStep 4707305 = 3530479) B3530479
theorem B3138203 : Blo 2203435 3138203 := bstep (se 1 (by rfl) ⟨2353652, by rfl⟩ : syracuseStep 3138203 = 4707305) B4707305
theorem B8368541 : Blo 2203435 8368541 := bstep (se 3 (by rfl) ⟨1569101, by rfl⟩ : syracuseStep 8368541 = 3138203) B3138203
theorem B5579027 : Blo 2203435 5579027 := bstep (se 1 (by rfl) ⟨4184270, by rfl⟩ : syracuseStep 5579027 = 8368541) B8368541
theorem B3719351 : Blo 2203435 3719351 := bstep (se 1 (by rfl) ⟨2789513, by rfl⟩ : syracuseStep 3719351 = 5579027) B5579027
theorem B2479567 : Blo 2203435 2479567 := bstep (se 1 (by rfl) ⟨1859675, by rfl⟩ : syracuseStep 2479567 = 3719351) B3719351
theorem B3306089 : Blo 2203435 3306089 := bstep (se 2 (by rfl) ⟨1239783, by rfl⟩ : syracuseStep 3306089 = 2479567) B2479567
theorem B2204059 : Blo 2203435 2204059 := bstep (se 1 (by rfl) ⟨1653044, by rfl⟩ : syracuseStep 2204059 = 3306089) B3306089
theorem B2385769 : Blo 2203435 2385769 := bbase (se 2 (by rfl) ⟨894663, by rfl⟩ : syracuseStep 2385769 = 1789327) (by norm_num)
theorem B3181025 : Blo 2203435 3181025 := bstep (se 2 (by rfl) ⟨1192884, by rfl⟩ : syracuseStep 3181025 = 2385769) B2385769
theorem B8482733 : Blo 2203435 8482733 := bstep (se 3 (by rfl) ⟨1590512, by rfl⟩ : syracuseStep 8482733 = 3181025) B3181025
theorem B5655155 : Blo 2203435 5655155 := bstep (se 1 (by rfl) ⟨4241366, by rfl⟩ : syracuseStep 5655155 = 8482733) B8482733
theorem B15080413 : Blo 2203435 15080413 := bstep (se 3 (by rfl) ⟨2827577, by rfl⟩ : syracuseStep 15080413 = 5655155) B5655155
theorem B20107217 : Blo 2203435 20107217 := bstep (se 2 (by rfl) ⟨7540206, by rfl⟩ : syracuseStep 20107217 = 15080413) B15080413
theorem B13404811 : Blo 2203435 13404811 := bstep (se 1 (by rfl) ⟨10053608, by rfl⟩ : syracuseStep 13404811 = 20107217) B20107217
theorem B17873081 : Blo 2203435 17873081 := bstep (se 2 (by rfl) ⟨6702405, by rfl⟩ : syracuseStep 17873081 = 13404811) B13404811
theorem B11915387 : Blo 2203435 11915387 := bstep (se 1 (by rfl) ⟨8936540, by rfl⟩ : syracuseStep 11915387 = 17873081) B17873081
theorem B7943591 : Blo 2203435 7943591 := bstep (se 1 (by rfl) ⟨5957693, by rfl⟩ : syracuseStep 7943591 = 11915387) B11915387
theorem B5295727 : Blo 2203435 5295727 := bstep (se 1 (by rfl) ⟨3971795, by rfl⟩ : syracuseStep 5295727 = 7943591) B7943591
theorem B7060969 : Blo 2203435 7060969 := bstep (se 2 (by rfl) ⟨2647863, by rfl⟩ : syracuseStep 7060969 = 5295727) B5295727
theorem B9414625 : Blo 2203435 9414625 := bstep (se 2 (by rfl) ⟨3530484, by rfl⟩ : syracuseStep 9414625 = 7060969) B7060969
theorem B12552833 : Blo 2203435 12552833 := bstep (se 2 (by rfl) ⟨4707312, by rfl⟩ : syracuseStep 12552833 = 9414625) B9414625
theorem B8368555 : Blo 2203435 8368555 := bstep (se 1 (by rfl) ⟨6276416, by rfl⟩ : syracuseStep 8368555 = 12552833) B12552833
theorem B11158073 : Blo 2203435 11158073 := bstep (se 2 (by rfl) ⟨4184277, by rfl⟩ : syracuseStep 11158073 = 8368555) B8368555
theorem B7438715 : Blo 2203435 7438715 := bstep (se 1 (by rfl) ⟨5579036, by rfl⟩ : syracuseStep 7438715 = 11158073) B11158073
theorem B4959143 : Blo 2203435 4959143 := bstep (se 1 (by rfl) ⟨3719357, by rfl⟩ : syracuseStep 4959143 = 7438715) B7438715
theorem B3306095 : Blo 2203435 3306095 := bstep (se 1 (by rfl) ⟨2479571, by rfl⟩ : syracuseStep 3306095 = 4959143) B4959143
theorem B2204063 : Blo 2203435 2204063 := bstep (se 1 (by rfl) ⟨1653047, by rfl⟩ : syracuseStep 2204063 = 3306095) B3306095
theorem B3306101 : Blo 2203435 3306101 := bbase (se 5 (by rfl) ⟨154973, by rfl⟩ : syracuseStep 3306101 = 309947) (by norm_num)
theorem B2204067 : Blo 2203435 2204067 := bstep (se 1 (by rfl) ⟨1653050, by rfl⟩ : syracuseStep 2204067 = 3306101) B3306101
theorem B4184293 : Blo 2203435 4184293 := bbase (se 4 (by rfl) ⟨392277, by rfl⟩ : syracuseStep 4184293 = 784555) (by norm_num)
theorem B5579057 : Blo 2203435 5579057 := bstep (se 2 (by rfl) ⟨2092146, by rfl⟩ : syracuseStep 5579057 = 4184293) B4184293
theorem B3719371 : Blo 2203435 3719371 := bstep (se 1 (by rfl) ⟨2789528, by rfl⟩ : syracuseStep 3719371 = 5579057) B5579057
theorem B4959161 : Blo 2203435 4959161 := bstep (se 2 (by rfl) ⟨1859685, by rfl⟩ : syracuseStep 4959161 = 3719371) B3719371
theorem B3306107 : Blo 2203435 3306107 := bstep (se 1 (by rfl) ⟨2479580, by rfl⟩ : syracuseStep 3306107 = 4959161) B4959161
theorem B2204071 : Blo 2203435 2204071 := bstep (se 1 (by rfl) ⟨1653053, by rfl⟩ : syracuseStep 2204071 = 3306107) B3306107
theorem B2479585 : Blo 2203435 2479585 := bbase (se 2 (by rfl) ⟨929844, by rfl⟩ : syracuseStep 2479585 = 1859689) (by norm_num)
theorem B3306113 : Blo 2203435 3306113 := bstep (se 2 (by rfl) ⟨1239792, by rfl⟩ : syracuseStep 3306113 = 2479585) B2479585
theorem B2204075 : Blo 2203435 2204075 := bstep (se 1 (by rfl) ⟨1653056, by rfl⟩ : syracuseStep 2204075 = 3306113) B3306113
theorem B5579077 : Blo 2203435 5579077 := bbase (se 4 (by rfl) ⟨523038, by rfl⟩ : syracuseStep 5579077 = 1046077) (by norm_num)
theorem B7438769 : Blo 2203435 7438769 := bstep (se 2 (by rfl) ⟨2789538, by rfl⟩ : syracuseStep 7438769 = 5579077) B5579077
theorem B4959179 : Blo 2203435 4959179 := bstep (se 1 (by rfl) ⟨3719384, by rfl⟩ : syracuseStep 4959179 = 7438769) B7438769
theorem B3306119 : Blo 2203435 3306119 := bstep (se 1 (by rfl) ⟨2479589, by rfl⟩ : syracuseStep 3306119 = 4959179) B4959179
theorem B2204079 : Blo 2203435 2204079 := bstep (se 1 (by rfl) ⟨1653059, by rfl⟩ : syracuseStep 2204079 = 3306119) B3306119
theorem B3306125 : Blo 2203435 3306125 := bbase (se 3 (by rfl) ⟨619898, by rfl⟩ : syracuseStep 3306125 = 1239797) (by norm_num)
theorem B2204083 : Blo 2203435 2204083 := bstep (se 1 (by rfl) ⟨1653062, by rfl⟩ : syracuseStep 2204083 = 3306125) B3306125
theorem B4959197 : Blo 2203435 4959197 := bbase (se 3 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 4959197 = 1859699) (by norm_num)
theorem B3306131 : Blo 2203435 3306131 := bstep (se 1 (by rfl) ⟨2479598, by rfl⟩ : syracuseStep 3306131 = 4959197) B4959197
theorem B2204087 : Blo 2203435 2204087 := bstep (se 1 (by rfl) ⟨1653065, by rfl⟩ : syracuseStep 2204087 = 3306131) B3306131
theorem B3719405 : Blo 2203435 3719405 := bbase (se 3 (by rfl) ⟨697388, by rfl⟩ : syracuseStep 3719405 = 1394777) (by norm_num)
theorem B2479603 : Blo 2203435 2479603 := bstep (se 1 (by rfl) ⟨1859702, by rfl⟩ : syracuseStep 2479603 = 3719405) B3719405
theorem B3306137 : Blo 2203435 3306137 := bstep (se 2 (by rfl) ⟨1239801, by rfl⟩ : syracuseStep 3306137 = 2479603) B2479603
theorem B2204091 : Blo 2203435 2204091 := bstep (se 1 (by rfl) ⟨1653068, by rfl⟩ : syracuseStep 2204091 = 3306137) B3306137
theorem B5026877 : Blo 2203435 5026877 := bbase (se 3 (by rfl) ⟨942539, by rfl⟩ : syracuseStep 5026877 = 1885079) (by norm_num)
theorem B3351251 : Blo 2203435 3351251 := bstep (se 1 (by rfl) ⟨2513438, by rfl⟩ : syracuseStep 3351251 = 5026877) B5026877
theorem B8936669 : Blo 2203435 8936669 := bstep (se 3 (by rfl) ⟨1675625, by rfl⟩ : syracuseStep 8936669 = 3351251) B3351251
theorem B23831117 : Blo 2203435 23831117 := bstep (se 3 (by rfl) ⟨4468334, by rfl⟩ : syracuseStep 23831117 = 8936669) B8936669
theorem B15887411 : Blo 2203435 15887411 := bstep (se 1 (by rfl) ⟨11915558, by rfl⟩ : syracuseStep 15887411 = 23831117) B23831117
theorem B10591607 : Blo 2203435 10591607 := bstep (se 1 (by rfl) ⟨7943705, by rfl⟩ : syracuseStep 10591607 = 15887411) B15887411
theorem B28244285 : Blo 2203435 28244285 := bstep (se 3 (by rfl) ⟨5295803, by rfl⟩ : syracuseStep 28244285 = 10591607) B10591607
theorem B18829523 : Blo 2203435 18829523 := bstep (se 1 (by rfl) ⟨14122142, by rfl⟩ : syracuseStep 18829523 = 28244285) B28244285
theorem B12553015 : Blo 2203435 12553015 := bstep (se 1 (by rfl) ⟨9414761, by rfl⟩ : syracuseStep 12553015 = 18829523) B18829523
theorem B16737353 : Blo 2203435 16737353 := bstep (se 2 (by rfl) ⟨6276507, by rfl⟩ : syracuseStep 16737353 = 12553015) B12553015
theorem B11158235 : Blo 2203435 11158235 := bstep (se 1 (by rfl) ⟨8368676, by rfl⟩ : syracuseStep 11158235 = 16737353) B16737353
theorem B7438823 : Blo 2203435 7438823 := bstep (se 1 (by rfl) ⟨5579117, by rfl⟩ : syracuseStep 7438823 = 11158235) B11158235
theorem B4959215 : Blo 2203435 4959215 := bstep (se 1 (by rfl) ⟨3719411, by rfl⟩ : syracuseStep 4959215 = 7438823) B7438823
theorem B3306143 : Blo 2203435 3306143 := bstep (se 1 (by rfl) ⟨2479607, by rfl⟩ : syracuseStep 3306143 = 4959215) B4959215
theorem B2204095 : Blo 2203435 2204095 := bstep (se 1 (by rfl) ⟨1653071, by rfl⟩ : syracuseStep 2204095 = 3306143) B3306143
theorem B3306149 : Blo 2203435 3306149 := bbase (se 4 (by rfl) ⟨309951, by rfl⟩ : syracuseStep 3306149 = 619903) (by norm_num)
theorem B2204099 : Blo 2203435 2204099 := bstep (se 1 (by rfl) ⟨1653074, by rfl⟩ : syracuseStep 2204099 = 3306149) B3306149
theorem B2789569 : Blo 2203435 2789569 := bbase (se 2 (by rfl) ⟨1046088, by rfl⟩ : syracuseStep 2789569 = 2092177) (by norm_num)
theorem B3719425 : Blo 2203435 3719425 := bstep (se 2 (by rfl) ⟨1394784, by rfl⟩ : syracuseStep 3719425 = 2789569) B2789569
theorem B4959233 : Blo 2203435 4959233 := bstep (se 2 (by rfl) ⟨1859712, by rfl⟩ : syracuseStep 4959233 = 3719425) B3719425
theorem B3306155 : Blo 2203435 3306155 := bstep (se 1 (by rfl) ⟨2479616, by rfl⟩ : syracuseStep 3306155 = 4959233) B4959233
theorem B2204103 : Blo 2203435 2204103 := bstep (se 1 (by rfl) ⟨1653077, by rfl⟩ : syracuseStep 2204103 = 3306155) B3306155
theorem B2479621 : Blo 2203435 2479621 := bbase (se 4 (by rfl) ⟨232464, by rfl⟩ : syracuseStep 2479621 = 464929) (by norm_num)
theorem B3306161 : Blo 2203435 3306161 := bstep (se 2 (by rfl) ⟨1239810, by rfl⟩ : syracuseStep 3306161 = 2479621) B2479621
theorem B2204107 : Blo 2203435 2204107 := bstep (se 1 (by rfl) ⟨1653080, by rfl⟩ : syracuseStep 2204107 = 3306161) B3306161
theorem B3138277 : Blo 2203435 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B4184369 : Blo 2203435 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B2789579 : Blo 2203435 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B7438877 : Blo 2203435 7438877 := bstep (se 3 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 7438877 = 2789579) B2789579
theorem B4959251 : Blo 2203435 4959251 := bstep (se 1 (by rfl) ⟨3719438, by rfl⟩ : syracuseStep 4959251 = 7438877) B7438877
theorem B3306167 : Blo 2203435 3306167 := bstep (se 1 (by rfl) ⟨2479625, by rfl⟩ : syracuseStep 3306167 = 4959251) B4959251
theorem B2204111 : Blo 2203435 2204111 := bstep (se 1 (by rfl) ⟨1653083, by rfl⟩ : syracuseStep 2204111 = 3306167) B3306167
theorem B3306173 : Blo 2203435 3306173 := bbase (se 3 (by rfl) ⟨619907, by rfl⟩ : syracuseStep 3306173 = 1239815) (by norm_num)
theorem B2204115 : Blo 2203435 2204115 := bstep (se 1 (by rfl) ⟨1653086, by rfl⟩ : syracuseStep 2204115 = 3306173) B3306173
theorem B4959269 : Blo 2203435 4959269 := bbase (se 4 (by rfl) ⟨464931, by rfl⟩ : syracuseStep 4959269 = 929863) (by norm_num)
theorem B3306179 : Blo 2203435 3306179 := bstep (se 1 (by rfl) ⟨2479634, by rfl⟩ : syracuseStep 3306179 = 4959269) B4959269
theorem B2204119 : Blo 2203435 2204119 := bstep (se 1 (by rfl) ⟨1653089, by rfl⟩ : syracuseStep 2204119 = 3306179) B3306179
theorem B5579189 : Blo 2203435 5579189 := bbase (se 5 (by rfl) ⟨261524, by rfl⟩ : syracuseStep 5579189 = 523049) (by norm_num)
theorem B3719459 : Blo 2203435 3719459 := bstep (se 1 (by rfl) ⟨2789594, by rfl⟩ : syracuseStep 3719459 = 5579189) B5579189
theorem B2479639 : Blo 2203435 2479639 := bstep (se 1 (by rfl) ⟨1859729, by rfl⟩ : syracuseStep 2479639 = 3719459) B3719459
theorem B3306185 : Blo 2203435 3306185 := bstep (se 2 (by rfl) ⟨1239819, by rfl⟩ : syracuseStep 3306185 = 2479639) B2479639
theorem B2204123 : Blo 2203435 2204123 := bstep (se 1 (by rfl) ⟨1653092, by rfl⟩ : syracuseStep 2204123 = 3306185) B3306185
theorem B8482981 : Blo 2203435 8482981 := bbase (se 4 (by rfl) ⟨795279, by rfl⟩ : syracuseStep 8482981 = 1590559) (by norm_num)
theorem B11310641 : Blo 2203435 11310641 := bstep (se 2 (by rfl) ⟨4241490, by rfl⟩ : syracuseStep 11310641 = 8482981) B8482981
theorem B7540427 : Blo 2203435 7540427 := bstep (se 1 (by rfl) ⟨5655320, by rfl⟩ : syracuseStep 7540427 = 11310641) B11310641
theorem B5026951 : Blo 2203435 5026951 := bstep (se 1 (by rfl) ⟨3770213, by rfl⟩ : syracuseStep 5026951 = 7540427) B7540427
theorem B6702601 : Blo 2203435 6702601 := bstep (se 2 (by rfl) ⟨2513475, by rfl⟩ : syracuseStep 6702601 = 5026951) B5026951
theorem B8936801 : Blo 2203435 8936801 := bstep (se 2 (by rfl) ⟨3351300, by rfl⟩ : syracuseStep 8936801 = 6702601) B6702601
theorem B5957867 : Blo 2203435 5957867 := bstep (se 1 (by rfl) ⟨4468400, by rfl⟩ : syracuseStep 5957867 = 8936801) B8936801
theorem B3971911 : Blo 2203435 3971911 := bstep (se 1 (by rfl) ⟨2978933, by rfl⟩ : syracuseStep 3971911 = 5957867) B5957867
theorem B5295881 : Blo 2203435 5295881 := bstep (se 2 (by rfl) ⟨1985955, by rfl⟩ : syracuseStep 5295881 = 3971911) B3971911
theorem B14122349 : Blo 2203435 14122349 := bstep (se 3 (by rfl) ⟨2647940, by rfl⟩ : syracuseStep 14122349 = 5295881) B5295881
theorem B9414899 : Blo 2203435 9414899 := bstep (se 1 (by rfl) ⟨7061174, by rfl⟩ : syracuseStep 9414899 = 14122349) B14122349
theorem B6276599 : Blo 2203435 6276599 := bstep (se 1 (by rfl) ⟨4707449, by rfl⟩ : syracuseStep 6276599 = 9414899) B9414899
theorem B4184399 : Blo 2203435 4184399 := bstep (se 1 (by rfl) ⟨3138299, by rfl⟩ : syracuseStep 4184399 = 6276599) B6276599
theorem B11158397 : Blo 2203435 11158397 := bstep (se 3 (by rfl) ⟨2092199, by rfl⟩ : syracuseStep 11158397 = 4184399) B4184399
theorem B7438931 : Blo 2203435 7438931 := bstep (se 1 (by rfl) ⟨5579198, by rfl⟩ : syracuseStep 7438931 = 11158397) B11158397
theorem B4959287 : Blo 2203435 4959287 := bstep (se 1 (by rfl) ⟨3719465, by rfl⟩ : syracuseStep 4959287 = 7438931) B7438931
theorem B3306191 : Blo 2203435 3306191 := bstep (se 1 (by rfl) ⟨2479643, by rfl⟩ : syracuseStep 3306191 = 4959287) B4959287
theorem B2204127 : Blo 2203435 2204127 := bstep (se 1 (by rfl) ⟨1653095, by rfl⟩ : syracuseStep 2204127 = 3306191) B3306191
theorem B3306197 : Blo 2203435 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B2204131 : Blo 2203435 2204131 := bstep (se 1 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 2204131 = 3306197) B3306197
theorem B5295901 : Blo 2203435 5295901 := bbase (se 3 (by rfl) ⟨992981, by rfl⟩ : syracuseStep 5295901 = 1985963) (by norm_num)
theorem B7061201 : Blo 2203435 7061201 := bstep (se 2 (by rfl) ⟨2647950, by rfl⟩ : syracuseStep 7061201 = 5295901) B5295901
theorem B4707467 : Blo 2203435 4707467 := bstep (se 1 (by rfl) ⟨3530600, by rfl⟩ : syracuseStep 4707467 = 7061201) B7061201
theorem B3138311 : Blo 2203435 3138311 := bstep (se 1 (by rfl) ⟨2353733, by rfl⟩ : syracuseStep 3138311 = 4707467) B4707467
theorem B8368829 : Blo 2203435 8368829 := bstep (se 3 (by rfl) ⟨1569155, by rfl⟩ : syracuseStep 8368829 = 3138311) B3138311
theorem B5579219 : Blo 2203435 5579219 := bstep (se 1 (by rfl) ⟨4184414, by rfl⟩ : syracuseStep 5579219 = 8368829) B8368829
theorem B3719479 : Blo 2203435 3719479 := bstep (se 1 (by rfl) ⟨2789609, by rfl⟩ : syracuseStep 3719479 = 5579219) B5579219
theorem B4959305 : Blo 2203435 4959305 := bstep (se 2 (by rfl) ⟨1859739, by rfl⟩ : syracuseStep 4959305 = 3719479) B3719479
theorem B3306203 : Blo 2203435 3306203 := bstep (se 1 (by rfl) ⟨2479652, by rfl⟩ : syracuseStep 3306203 = 4959305) B4959305
theorem B2204135 : Blo 2203435 2204135 := bstep (se 1 (by rfl) ⟨1653101, by rfl⟩ : syracuseStep 2204135 = 3306203) B3306203
theorem B2479657 : Blo 2203435 2479657 := bbase (se 2 (by rfl) ⟨929871, by rfl⟩ : syracuseStep 2479657 = 1859743) (by norm_num)
theorem B3306209 : Blo 2203435 3306209 := bstep (se 2 (by rfl) ⟨1239828, by rfl⟩ : syracuseStep 3306209 = 2479657) B2479657
theorem B2204139 : Blo 2203435 2204139 := bstep (se 1 (by rfl) ⟨1653104, by rfl⟩ : syracuseStep 2204139 = 3306209) B3306209
theorem B10053973 : Blo 2203435 10053973 := bbase (se 10 (by rfl) ⟨14727, by rfl⟩ : syracuseStep 10053973 = 29455) (by norm_num)
theorem B13405297 : Blo 2203435 13405297 := bstep (se 2 (by rfl) ⟨5026986, by rfl⟩ : syracuseStep 13405297 = 10053973) B10053973
theorem B17873729 : Blo 2203435 17873729 := bstep (se 2 (by rfl) ⟨6702648, by rfl⟩ : syracuseStep 17873729 = 13405297) B13405297
theorem B11915819 : Blo 2203435 11915819 := bstep (se 1 (by rfl) ⟨8936864, by rfl⟩ : syracuseStep 11915819 = 17873729) B17873729
theorem B7943879 : Blo 2203435 7943879 := bstep (se 1 (by rfl) ⟨5957909, by rfl⟩ : syracuseStep 7943879 = 11915819) B11915819
theorem B21183677 : Blo 2203435 21183677 := bstep (se 3 (by rfl) ⟨3971939, by rfl⟩ : syracuseStep 21183677 = 7943879) B7943879
theorem B14122451 : Blo 2203435 14122451 := bstep (se 1 (by rfl) ⟨10591838, by rfl⟩ : syracuseStep 14122451 = 21183677) B21183677
theorem B9414967 : Blo 2203435 9414967 := bstep (se 1 (by rfl) ⟨7061225, by rfl⟩ : syracuseStep 9414967 = 14122451) B14122451
theorem B12553289 : Blo 2203435 12553289 := bstep (se 2 (by rfl) ⟨4707483, by rfl⟩ : syracuseStep 12553289 = 9414967) B9414967
theorem B8368859 : Blo 2203435 8368859 := bstep (se 1 (by rfl) ⟨6276644, by rfl⟩ : syracuseStep 8368859 = 12553289) B12553289
theorem B5579239 : Blo 2203435 5579239 := bstep (se 1 (by rfl) ⟨4184429, by rfl⟩ : syracuseStep 5579239 = 8368859) B8368859
theorem B7438985 : Blo 2203435 7438985 := bstep (se 2 (by rfl) ⟨2789619, by rfl⟩ : syracuseStep 7438985 = 5579239) B5579239
theorem B4959323 : Blo 2203435 4959323 := bstep (se 1 (by rfl) ⟨3719492, by rfl⟩ : syracuseStep 4959323 = 7438985) B7438985
theorem B3306215 : Blo 2203435 3306215 := bstep (se 1 (by rfl) ⟨2479661, by rfl⟩ : syracuseStep 3306215 = 4959323) B4959323
theorem B2204143 : Blo 2203435 2204143 := bstep (se 1 (by rfl) ⟨1653107, by rfl⟩ : syracuseStep 2204143 = 3306215) B3306215
theorem B3306221 : Blo 2203435 3306221 := bbase (se 3 (by rfl) ⟨619916, by rfl⟩ : syracuseStep 3306221 = 1239833) (by norm_num)
theorem B2204147 : Blo 2203435 2204147 := bstep (se 1 (by rfl) ⟨1653110, by rfl⟩ : syracuseStep 2204147 = 3306221) B3306221
theorem B4959341 : Blo 2203435 4959341 := bbase (se 3 (by rfl) ⟨929876, by rfl⟩ : syracuseStep 4959341 = 1859753) (by norm_num)
theorem B3306227 : Blo 2203435 3306227 := bstep (se 1 (by rfl) ⟨2479670, by rfl⟩ : syracuseStep 3306227 = 4959341) B4959341
theorem B2204151 : Blo 2203435 2204151 := bstep (se 1 (by rfl) ⟨1653113, by rfl⟩ : syracuseStep 2204151 = 3306227) B3306227
theorem B4184453 : Blo 2203435 4184453 := bbase (se 4 (by rfl) ⟨392292, by rfl⟩ : syracuseStep 4184453 = 784585) (by norm_num)
theorem B2789635 : Blo 2203435 2789635 := bstep (se 1 (by rfl) ⟨2092226, by rfl⟩ : syracuseStep 2789635 = 4184453) B4184453
theorem B3719513 : Blo 2203435 3719513 := bstep (se 2 (by rfl) ⟨1394817, by rfl⟩ : syracuseStep 3719513 = 2789635) B2789635
theorem B2479675 : Blo 2203435 2479675 := bstep (se 1 (by rfl) ⟨1859756, by rfl⟩ : syracuseStep 2479675 = 3719513) B3719513
theorem B3306233 : Blo 2203435 3306233 := bstep (se 2 (by rfl) ⟨1239837, by rfl⟩ : syracuseStep 3306233 = 2479675) B2479675
theorem B2204155 : Blo 2203435 2204155 := bstep (se 1 (by rfl) ⟨1653116, by rfl⟩ : syracuseStep 2204155 = 3306233) B3306233
theorem B44125525 : Blo 2203435 44125525 := bbase (se 11 (by rfl) ⟨32318, by rfl⟩ : syracuseStep 44125525 = 64637) (by norm_num)
theorem B58834033 : Blo 2203435 58834033 := bstep (se 2 (by rfl) ⟨22062762, by rfl⟩ : syracuseStep 58834033 = 44125525) B44125525
theorem B313781509 : Blo 2203435 313781509 := bstep (se 4 (by rfl) ⟨29417016, by rfl⟩ : syracuseStep 313781509 = 58834033) B58834033
theorem B1673501381 : Blo 2203435 1673501381 := bstep (se 4 (by rfl) ⟨156890754, by rfl⟩ : syracuseStep 1673501381 = 313781509) B313781509
theorem B1115667587 : Blo 2203435 1115667587 := bstep (se 1 (by rfl) ⟨836750690, by rfl⟩ : syracuseStep 1115667587 = 1673501381) B1673501381
theorem B2975113565 : Blo 2203435 2975113565 := bstep (se 3 (by rfl) ⟨557833793, by rfl⟩ : syracuseStep 2975113565 = 1115667587) B1115667587
theorem B1983409043 : Blo 2203435 1983409043 := bstep (se 1 (by rfl) ⟨1487556782, by rfl⟩ : syracuseStep 1983409043 = 2975113565) B2975113565
theorem B5289090781 : Blo 2203435 5289090781 := bstep (se 3 (by rfl) ⟨991704521, by rfl⟩ : syracuseStep 5289090781 = 1983409043) B1983409043
theorem B7052121041 : Blo 2203435 7052121041 := bstep (se 2 (by rfl) ⟨2644545390, by rfl⟩ : syracuseStep 7052121041 = 5289090781) B5289090781
theorem B18805656109 : Blo 2203435 18805656109 := bstep (se 3 (by rfl) ⟨3526060520, by rfl⟩ : syracuseStep 18805656109 = 7052121041) B7052121041
theorem B25074208145 : Blo 2203435 25074208145 := bstep (se 2 (by rfl) ⟨9402828054, by rfl⟩ : syracuseStep 25074208145 = 18805656109) B18805656109
theorem B16716138763 : Blo 2203435 16716138763 := bstep (se 1 (by rfl) ⟨12537104072, by rfl⟩ : syracuseStep 16716138763 = 25074208145) B25074208145
theorem B22288185017 : Blo 2203435 22288185017 := bstep (se 2 (by rfl) ⟨8358069381, by rfl⟩ : syracuseStep 22288185017 = 16716138763) B16716138763
theorem B14858790011 : Blo 2203435 14858790011 := bstep (se 1 (by rfl) ⟨11144092508, by rfl⟩ : syracuseStep 14858790011 = 22288185017) B22288185017
theorem B9905860007 : Blo 2203435 9905860007 := bstep (se 1 (by rfl) ⟨7429395005, by rfl⟩ : syracuseStep 9905860007 = 14858790011) B14858790011
theorem B6603906671 : Blo 2203435 6603906671 := bstep (se 1 (by rfl) ⟨4952930003, by rfl⟩ : syracuseStep 6603906671 = 9905860007) B9905860007
theorem B4402604447 : Blo 2203435 4402604447 := bstep (se 1 (by rfl) ⟨3301953335, by rfl⟩ : syracuseStep 4402604447 = 6603906671) B6603906671
theorem B2935069631 : Blo 2203435 2935069631 := bstep (se 1 (by rfl) ⟨2201302223, by rfl⟩ : syracuseStep 2935069631 = 4402604447) B4402604447
theorem B1956713087 : Blo 2203435 1956713087 := bstep (se 1 (by rfl) ⟨1467534815, by rfl⟩ : syracuseStep 1956713087 = 2935069631) B2935069631
theorem B1304475391 : Blo 2203435 1304475391 := bstep (se 1 (by rfl) ⟨978356543, by rfl⟩ : syracuseStep 1304475391 = 1956713087) B1956713087
theorem B1739300521 : Blo 2203435 1739300521 := bstep (se 2 (by rfl) ⟨652237695, by rfl⟩ : syracuseStep 1739300521 = 1304475391) B1304475391
theorem B2319067361 : Blo 2203435 2319067361 := bstep (se 2 (by rfl) ⟨869650260, by rfl⟩ : syracuseStep 2319067361 = 1739300521) B1739300521
theorem B1546044907 : Blo 2203435 1546044907 := bstep (se 1 (by rfl) ⟨1159533680, by rfl⟩ : syracuseStep 1546044907 = 2319067361) B2319067361
theorem B2061393209 : Blo 2203435 2061393209 := bstep (se 2 (by rfl) ⟨773022453, by rfl⟩ : syracuseStep 2061393209 = 1546044907) B1546044907
theorem B1374262139 : Blo 2203435 1374262139 := bstep (se 1 (by rfl) ⟨1030696604, by rfl⟩ : syracuseStep 1374262139 = 2061393209) B2061393209
theorem B916174759 : Blo 2203435 916174759 := bstep (se 1 (by rfl) ⟨687131069, by rfl⟩ : syracuseStep 916174759 = 1374262139) B1374262139
theorem B1221566345 : Blo 2203435 1221566345 := bstep (se 2 (by rfl) ⟨458087379, by rfl⟩ : syracuseStep 1221566345 = 916174759) B916174759
theorem B814377563 : Blo 2203435 814377563 := bstep (se 1 (by rfl) ⟨610783172, by rfl⟩ : syracuseStep 814377563 = 1221566345) B1221566345
theorem B542918375 : Blo 2203435 542918375 := bstep (se 1 (by rfl) ⟨407188781, by rfl⟩ : syracuseStep 542918375 = 814377563) B814377563
theorem B361945583 : Blo 2203435 361945583 := bstep (se 1 (by rfl) ⟨271459187, by rfl⟩ : syracuseStep 361945583 = 542918375) B542918375
theorem B241297055 : Blo 2203435 241297055 := bstep (se 1 (by rfl) ⟨180972791, by rfl⟩ : syracuseStep 241297055 = 361945583) B361945583
theorem B160864703 : Blo 2203435 160864703 := bstep (se 1 (by rfl) ⟨120648527, by rfl⟩ : syracuseStep 160864703 = 241297055) B241297055
theorem B107243135 : Blo 2203435 107243135 := bstep (se 1 (by rfl) ⟨80432351, by rfl⟩ : syracuseStep 107243135 = 160864703) B160864703
theorem B71495423 : Blo 2203435 71495423 := bstep (se 1 (by rfl) ⟨53621567, by rfl⟩ : syracuseStep 71495423 = 107243135) B107243135
theorem B47663615 : Blo 2203435 47663615 := bstep (se 1 (by rfl) ⟨35747711, by rfl⟩ : syracuseStep 47663615 = 71495423) B71495423
theorem B31775743 : Blo 2203435 31775743 := bstep (se 1 (by rfl) ⟨23831807, by rfl⟩ : syracuseStep 31775743 = 47663615) B47663615
theorem B42367657 : Blo 2203435 42367657 := bstep (se 2 (by rfl) ⟨15887871, by rfl⟩ : syracuseStep 42367657 = 31775743) B31775743
theorem B56490209 : Blo 2203435 56490209 := bstep (se 2 (by rfl) ⟨21183828, by rfl⟩ : syracuseStep 56490209 = 42367657) B42367657
theorem B37660139 : Blo 2203435 37660139 := bstep (se 1 (by rfl) ⟨28245104, by rfl⟩ : syracuseStep 37660139 = 56490209) B56490209
theorem B25106759 : Blo 2203435 25106759 := bstep (se 1 (by rfl) ⟨18830069, by rfl⟩ : syracuseStep 25106759 = 37660139) B37660139
theorem B16737839 : Blo 2203435 16737839 := bstep (se 1 (by rfl) ⟨12553379, by rfl⟩ : syracuseStep 16737839 = 25106759) B25106759
theorem B11158559 : Blo 2203435 11158559 := bstep (se 1 (by rfl) ⟨8368919, by rfl⟩ : syracuseStep 11158559 = 16737839) B16737839
theorem B7439039 : Blo 2203435 7439039 := bstep (se 1 (by rfl) ⟨5579279, by rfl⟩ : syracuseStep 7439039 = 11158559) B11158559
theorem B4959359 : Blo 2203435 4959359 := bstep (se 1 (by rfl) ⟨3719519, by rfl⟩ : syracuseStep 4959359 = 7439039) B7439039
theorem B3306239 : Blo 2203435 3306239 := bstep (se 1 (by rfl) ⟨2479679, by rfl⟩ : syracuseStep 3306239 = 4959359) B4959359
theorem B2204159 : Blo 2203435 2204159 := bstep (se 1 (by rfl) ⟨1653119, by rfl⟩ : syracuseStep 2204159 = 3306239) B3306239
theorem B3306245 : Blo 2203435 3306245 := bbase (se 4 (by rfl) ⟨309960, by rfl⟩ : syracuseStep 3306245 = 619921) (by norm_num)
theorem B2204163 : Blo 2203435 2204163 := bstep (se 1 (by rfl) ⟨1653122, by rfl⟩ : syracuseStep 2204163 = 3306245) B3306245
theorem B3719533 : Blo 2203435 3719533 := bbase (se 3 (by rfl) ⟨697412, by rfl⟩ : syracuseStep 3719533 = 1394825) (by norm_num)
theorem B4959377 : Blo 2203435 4959377 := bstep (se 2 (by rfl) ⟨1859766, by rfl⟩ : syracuseStep 4959377 = 3719533) B3719533
theorem B3306251 : Blo 2203435 3306251 := bstep (se 1 (by rfl) ⟨2479688, by rfl⟩ : syracuseStep 3306251 = 4959377) B4959377
theorem B2204167 : Blo 2203435 2204167 := bstep (se 1 (by rfl) ⟨1653125, by rfl⟩ : syracuseStep 2204167 = 3306251) B3306251
theorem B2479693 : Blo 2203435 2479693 := bbase (se 3 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 2479693 = 929885) (by norm_num)
theorem B3306257 : Blo 2203435 3306257 := bstep (se 2 (by rfl) ⟨1239846, by rfl⟩ : syracuseStep 3306257 = 2479693) B2479693
theorem B2204171 : Blo 2203435 2204171 := bstep (se 1 (by rfl) ⟨1653128, by rfl⟩ : syracuseStep 2204171 = 3306257) B3306257
theorem B7439093 : Blo 2203435 7439093 := bbase (se 5 (by rfl) ⟨348707, by rfl⟩ : syracuseStep 7439093 = 697415) (by norm_num)
theorem B4959395 : Blo 2203435 4959395 := bstep (se 1 (by rfl) ⟨3719546, by rfl⟩ : syracuseStep 4959395 = 7439093) B7439093
theorem B3306263 : Blo 2203435 3306263 := bstep (se 1 (by rfl) ⟨2479697, by rfl⟩ : syracuseStep 3306263 = 4959395) B4959395
theorem B2204175 : Blo 2203435 2204175 := bstep (se 1 (by rfl) ⟨1653131, by rfl⟩ : syracuseStep 2204175 = 3306263) B3306263
theorem B3306269 : Blo 2203435 3306269 := bbase (se 3 (by rfl) ⟨619925, by rfl⟩ : syracuseStep 3306269 = 1239851) (by norm_num)
theorem B2204179 : Blo 2203435 2204179 := bstep (se 1 (by rfl) ⟨1653134, by rfl⟩ : syracuseStep 2204179 = 3306269) B3306269
theorem B4959413 : Blo 2203435 4959413 := bbase (se 5 (by rfl) ⟨232472, by rfl⟩ : syracuseStep 4959413 = 464945) (by norm_num)
theorem B3306275 : Blo 2203435 3306275 := bstep (se 1 (by rfl) ⟨2479706, by rfl⟩ : syracuseStep 3306275 = 4959413) B4959413
theorem B2204183 : Blo 2203435 2204183 := bstep (se 1 (by rfl) ⟨1653137, by rfl⟩ : syracuseStep 2204183 = 3306275) B3306275
theorem B2353789 : Blo 2203435 2353789 := bbase (se 3 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 2353789 = 882671) (by norm_num)
theorem B12553541 : Blo 2203435 12553541 := bstep (se 4 (by rfl) ⟨1176894, by rfl⟩ : syracuseStep 12553541 = 2353789) B2353789
theorem B8369027 : Blo 2203435 8369027 := bstep (se 1 (by rfl) ⟨6276770, by rfl⟩ : syracuseStep 8369027 = 12553541) B12553541
theorem B5579351 : Blo 2203435 5579351 := bstep (se 1 (by rfl) ⟨4184513, by rfl⟩ : syracuseStep 5579351 = 8369027) B8369027
theorem B3719567 : Blo 2203435 3719567 := bstep (se 1 (by rfl) ⟨2789675, by rfl⟩ : syracuseStep 3719567 = 5579351) B5579351
theorem B2479711 : Blo 2203435 2479711 := bstep (se 1 (by rfl) ⟨1859783, by rfl⟩ : syracuseStep 2479711 = 3719567) B3719567
theorem B3306281 : Blo 2203435 3306281 := bstep (se 2 (by rfl) ⟨1239855, by rfl⟩ : syracuseStep 3306281 = 2479711) B2479711
theorem B2204187 : Blo 2203435 2204187 := bstep (se 1 (by rfl) ⟨1653140, by rfl⟩ : syracuseStep 2204187 = 3306281) B3306281
theorem B2353793 : Blo 2203435 2353793 := bbase (se 2 (by rfl) ⟨882672, by rfl⟩ : syracuseStep 2353793 = 1765345) (by norm_num)
theorem B6276781 : Blo 2203435 6276781 := bstep (se 3 (by rfl) ⟨1176896, by rfl⟩ : syracuseStep 6276781 = 2353793) B2353793
theorem B8369041 : Blo 2203435 8369041 := bstep (se 2 (by rfl) ⟨3138390, by rfl⟩ : syracuseStep 8369041 = 6276781) B6276781
theorem B11158721 : Blo 2203435 11158721 := bstep (se 2 (by rfl) ⟨4184520, by rfl⟩ : syracuseStep 11158721 = 8369041) B8369041
theorem B7439147 : Blo 2203435 7439147 := bstep (se 1 (by rfl) ⟨5579360, by rfl⟩ : syracuseStep 7439147 = 11158721) B11158721
theorem B4959431 : Blo 2203435 4959431 := bstep (se 1 (by rfl) ⟨3719573, by rfl⟩ : syracuseStep 4959431 = 7439147) B7439147
theorem B3306287 : Blo 2203435 3306287 := bstep (se 1 (by rfl) ⟨2479715, by rfl⟩ : syracuseStep 3306287 = 4959431) B4959431
theorem B2204191 : Blo 2203435 2204191 := bstep (se 1 (by rfl) ⟨1653143, by rfl⟩ : syracuseStep 2204191 = 3306287) B3306287
theorem B3306293 : Blo 2203435 3306293 := bbase (se 5 (by rfl) ⟨154982, by rfl⟩ : syracuseStep 3306293 = 309965) (by norm_num)
theorem B2204195 : Blo 2203435 2204195 := bstep (se 1 (by rfl) ⟨1653146, by rfl⟩ : syracuseStep 2204195 = 3306293) B3306293
theorem B5579381 : Blo 2203435 5579381 := bbase (se 5 (by rfl) ⟨261533, by rfl⟩ : syracuseStep 5579381 = 523067) (by norm_num)
theorem B3719587 : Blo 2203435 3719587 := bstep (se 1 (by rfl) ⟨2789690, by rfl⟩ : syracuseStep 3719587 = 5579381) B5579381
theorem B4959449 : Blo 2203435 4959449 := bstep (se 2 (by rfl) ⟨1859793, by rfl⟩ : syracuseStep 4959449 = 3719587) B3719587
theorem B3306299 : Blo 2203435 3306299 := bstep (se 1 (by rfl) ⟨2479724, by rfl⟩ : syracuseStep 3306299 = 4959449) B4959449
theorem B2204199 : Blo 2203435 2204199 := bstep (se 1 (by rfl) ⟨1653149, by rfl⟩ : syracuseStep 2204199 = 3306299) B3306299
theorem B2479729 : Blo 2203435 2479729 := bbase (se 2 (by rfl) ⟨929898, by rfl⟩ : syracuseStep 2479729 = 1859797) (by norm_num)
theorem B3306305 : Blo 2203435 3306305 := bstep (se 2 (by rfl) ⟨1239864, by rfl⟩ : syracuseStep 3306305 = 2479729) B2479729
theorem B2204203 : Blo 2203435 2204203 := bstep (se 1 (by rfl) ⟨1653152, by rfl⟩ : syracuseStep 2204203 = 3306305) B3306305
theorem B8937125 : Blo 2203435 8937125 := bbase (se 4 (by rfl) ⟨837855, by rfl⟩ : syracuseStep 8937125 = 1675711) (by norm_num)
theorem B5958083 : Blo 2203435 5958083 := bstep (se 1 (by rfl) ⟨4468562, by rfl⟩ : syracuseStep 5958083 = 8937125) B8937125
theorem B15888221 : Blo 2203435 15888221 := bstep (se 3 (by rfl) ⟨2979041, by rfl⟩ : syracuseStep 15888221 = 5958083) B5958083
theorem B10592147 : Blo 2203435 10592147 := bstep (se 1 (by rfl) ⟨7944110, by rfl⟩ : syracuseStep 10592147 = 15888221) B15888221
theorem B7061431 : Blo 2203435 7061431 := bstep (se 1 (by rfl) ⟨5296073, by rfl⟩ : syracuseStep 7061431 = 10592147) B10592147
theorem B9415241 : Blo 2203435 9415241 := bstep (se 2 (by rfl) ⟨3530715, by rfl⟩ : syracuseStep 9415241 = 7061431) B7061431
theorem B6276827 : Blo 2203435 6276827 := bstep (se 1 (by rfl) ⟨4707620, by rfl⟩ : syracuseStep 6276827 = 9415241) B9415241
theorem B4184551 : Blo 2203435 4184551 := bstep (se 1 (by rfl) ⟨3138413, by rfl⟩ : syracuseStep 4184551 = 6276827) B6276827
theorem B5579401 : Blo 2203435 5579401 := bstep (se 2 (by rfl) ⟨2092275, by rfl⟩ : syracuseStep 5579401 = 4184551) B4184551
theorem B7439201 : Blo 2203435 7439201 := bstep (se 2 (by rfl) ⟨2789700, by rfl⟩ : syracuseStep 7439201 = 5579401) B5579401
theorem B4959467 : Blo 2203435 4959467 := bstep (se 1 (by rfl) ⟨3719600, by rfl⟩ : syracuseStep 4959467 = 7439201) B7439201
theorem B3306311 : Blo 2203435 3306311 := bstep (se 1 (by rfl) ⟨2479733, by rfl⟩ : syracuseStep 3306311 = 4959467) B4959467
theorem B2204207 : Blo 2203435 2204207 := bstep (se 1 (by rfl) ⟨1653155, by rfl⟩ : syracuseStep 2204207 = 3306311) B3306311
theorem B3306317 : Blo 2203435 3306317 := bbase (se 3 (by rfl) ⟨619934, by rfl⟩ : syracuseStep 3306317 = 1239869) (by norm_num)
theorem B2204211 : Blo 2203435 2204211 := bstep (se 1 (by rfl) ⟨1653158, by rfl⟩ : syracuseStep 2204211 = 3306317) B3306317
theorem B4959485 : Blo 2203435 4959485 := bbase (se 3 (by rfl) ⟨929903, by rfl⟩ : syracuseStep 4959485 = 1859807) (by norm_num)
theorem B3306323 : Blo 2203435 3306323 := bstep (se 1 (by rfl) ⟨2479742, by rfl⟩ : syracuseStep 3306323 = 4959485) B4959485
theorem B2204215 : Blo 2203435 2204215 := bstep (se 1 (by rfl) ⟨1653161, by rfl⟩ : syracuseStep 2204215 = 3306323) B3306323
theorem B3719621 : Blo 2203435 3719621 := bbase (se 4 (by rfl) ⟨348714, by rfl⟩ : syracuseStep 3719621 = 697429) (by norm_num)
theorem B2479747 : Blo 2203435 2479747 := bstep (se 1 (by rfl) ⟨1859810, by rfl⟩ : syracuseStep 2479747 = 3719621) B3719621
theorem B3306329 : Blo 2203435 3306329 := bstep (se 2 (by rfl) ⟨1239873, by rfl⟩ : syracuseStep 3306329 = 2479747) B2479747
theorem B2204219 : Blo 2203435 2204219 := bstep (se 1 (by rfl) ⟨1653164, by rfl⟩ : syracuseStep 2204219 = 3306329) B3306329
theorem B16738325 : Blo 2203435 16738325 := bbase (se 6 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 16738325 = 784609) (by norm_num)
theorem B11158883 : Blo 2203435 11158883 := bstep (se 1 (by rfl) ⟨8369162, by rfl⟩ : syracuseStep 11158883 = 16738325) B16738325
theorem B7439255 : Blo 2203435 7439255 := bstep (se 1 (by rfl) ⟨5579441, by rfl⟩ : syracuseStep 7439255 = 11158883) B11158883
theorem B4959503 : Blo 2203435 4959503 := bstep (se 1 (by rfl) ⟨3719627, by rfl⟩ : syracuseStep 4959503 = 7439255) B7439255
theorem B3306335 : Blo 2203435 3306335 := bstep (se 1 (by rfl) ⟨2479751, by rfl⟩ : syracuseStep 3306335 = 4959503) B4959503
theorem B2204223 : Blo 2203435 2204223 := bstep (se 1 (by rfl) ⟨1653167, by rfl⟩ : syracuseStep 2204223 = 3306335) B3306335
theorem B3306341 : Blo 2203435 3306341 := bbase (se 4 (by rfl) ⟨309969, by rfl⟩ : syracuseStep 3306341 = 619939) (by norm_num)
theorem B2204227 : Blo 2203435 2204227 := bstep (se 1 (by rfl) ⟨1653170, by rfl⟩ : syracuseStep 2204227 = 3306341) B3306341
theorem B4184597 : Blo 2203435 4184597 := bbase (se 6 (by rfl) ⟨98076, by rfl⟩ : syracuseStep 4184597 = 196153) (by norm_num)
theorem B2789731 : Blo 2203435 2789731 := bstep (se 1 (by rfl) ⟨2092298, by rfl⟩ : syracuseStep 2789731 = 4184597) B4184597
theorem B3719641 : Blo 2203435 3719641 := bstep (se 2 (by rfl) ⟨1394865, by rfl⟩ : syracuseStep 3719641 = 2789731) B2789731
theorem B4959521 : Blo 2203435 4959521 := bstep (se 2 (by rfl) ⟨1859820, by rfl⟩ : syracuseStep 4959521 = 3719641) B3719641
theorem B3306347 : Blo 2203435 3306347 := bstep (se 1 (by rfl) ⟨2479760, by rfl⟩ : syracuseStep 3306347 = 4959521) B4959521
theorem B2204231 : Blo 2203435 2204231 := bstep (se 1 (by rfl) ⟨1653173, by rfl⟩ : syracuseStep 2204231 = 3306347) B3306347
theorem B2479765 : Blo 2203435 2479765 := bbase (se 6 (by rfl) ⟨58119, by rfl⟩ : syracuseStep 2479765 = 116239) (by norm_num)
theorem B3306353 : Blo 2203435 3306353 := bstep (se 2 (by rfl) ⟨1239882, by rfl⟩ : syracuseStep 3306353 = 2479765) B2479765
theorem B2204235 : Blo 2203435 2204235 := bstep (se 1 (by rfl) ⟨1653176, by rfl⟩ : syracuseStep 2204235 = 3306353) B3306353
theorem B2789741 : Blo 2203435 2789741 := bbase (se 3 (by rfl) ⟨523076, by rfl⟩ : syracuseStep 2789741 = 1046153) (by norm_num)
theorem B7439309 : Blo 2203435 7439309 := bstep (se 3 (by rfl) ⟨1394870, by rfl⟩ : syracuseStep 7439309 = 2789741) B2789741
theorem B4959539 : Blo 2203435 4959539 := bstep (se 1 (by rfl) ⟨3719654, by rfl⟩ : syracuseStep 4959539 = 7439309) B7439309
theorem B3306359 : Blo 2203435 3306359 := bstep (se 1 (by rfl) ⟨2479769, by rfl⟩ : syracuseStep 3306359 = 4959539) B4959539
theorem B2204239 : Blo 2203435 2204239 := bstep (se 1 (by rfl) ⟨1653179, by rfl⟩ : syracuseStep 2204239 = 3306359) B3306359
theorem B3306365 : Blo 2203435 3306365 := bbase (se 3 (by rfl) ⟨619943, by rfl⟩ : syracuseStep 3306365 = 1239887) (by norm_num)
theorem B2204243 : Blo 2203435 2204243 := bstep (se 1 (by rfl) ⟨1653182, by rfl⟩ : syracuseStep 2204243 = 3306365) B3306365
theorem B4959557 : Blo 2203435 4959557 := bbase (se 4 (by rfl) ⟨464958, by rfl⟩ : syracuseStep 4959557 = 929917) (by norm_num)
theorem B3306371 : Blo 2203435 3306371 := bstep (se 1 (by rfl) ⟨2479778, by rfl⟩ : syracuseStep 3306371 = 4959557) B4959557
theorem B2204247 : Blo 2203435 2204247 := bstep (se 1 (by rfl) ⟨1653185, by rfl⟩ : syracuseStep 2204247 = 3306371) B3306371
theorem B7061573 : Blo 2203435 7061573 := bbase (se 4 (by rfl) ⟨662022, by rfl⟩ : syracuseStep 7061573 = 1324045) (by norm_num)
theorem B4707715 : Blo 2203435 4707715 := bstep (se 1 (by rfl) ⟨3530786, by rfl⟩ : syracuseStep 4707715 = 7061573) B7061573
theorem B6276953 : Blo 2203435 6276953 := bstep (se 2 (by rfl) ⟨2353857, by rfl⟩ : syracuseStep 6276953 = 4707715) B4707715
theorem B4184635 : Blo 2203435 4184635 := bstep (se 1 (by rfl) ⟨3138476, by rfl⟩ : syracuseStep 4184635 = 6276953) B6276953
theorem B5579513 : Blo 2203435 5579513 := bstep (se 2 (by rfl) ⟨2092317, by rfl⟩ : syracuseStep 5579513 = 4184635) B4184635
theorem B3719675 : Blo 2203435 3719675 := bstep (se 1 (by rfl) ⟨2789756, by rfl⟩ : syracuseStep 3719675 = 5579513) B5579513
theorem B2479783 : Blo 2203435 2479783 := bstep (se 1 (by rfl) ⟨1859837, by rfl⟩ : syracuseStep 2479783 = 3719675) B3719675
theorem B3306377 : Blo 2203435 3306377 := bstep (se 2 (by rfl) ⟨1239891, by rfl⟩ : syracuseStep 3306377 = 2479783) B2479783
theorem B2204251 : Blo 2203435 2204251 := bstep (se 1 (by rfl) ⟨1653188, by rfl⟩ : syracuseStep 2204251 = 3306377) B3306377
theorem B11159045 : Blo 2203435 11159045 := bbase (se 4 (by rfl) ⟨1046160, by rfl⟩ : syracuseStep 11159045 = 2092321) (by norm_num)
theorem B7439363 : Blo 2203435 7439363 := bstep (se 1 (by rfl) ⟨5579522, by rfl⟩ : syracuseStep 7439363 = 11159045) B11159045
theorem B4959575 : Blo 2203435 4959575 := bstep (se 1 (by rfl) ⟨3719681, by rfl⟩ : syracuseStep 4959575 = 7439363) B7439363
theorem B3306383 : Blo 2203435 3306383 := bstep (se 1 (by rfl) ⟨2479787, by rfl⟩ : syracuseStep 3306383 = 4959575) B4959575
theorem B2204255 : Blo 2203435 2204255 := bstep (se 1 (by rfl) ⟨1653191, by rfl⟩ : syracuseStep 2204255 = 3306383) B3306383
theorem B3306389 : Blo 2203435 3306389 := bbase (se 6 (by rfl) ⟨77493, by rfl⟩ : syracuseStep 3306389 = 154987) (by norm_num)
theorem B2204259 : Blo 2203435 2204259 := bstep (se 1 (by rfl) ⟨1653194, by rfl⟩ : syracuseStep 2204259 = 3306389) B3306389
theorem B12553973 : Blo 2203435 12553973 := bbase (se 5 (by rfl) ⟨588467, by rfl⟩ : syracuseStep 12553973 = 1176935) (by norm_num)
theorem B8369315 : Blo 2203435 8369315 := bstep (se 1 (by rfl) ⟨6276986, by rfl⟩ : syracuseStep 8369315 = 12553973) B12553973
theorem B5579543 : Blo 2203435 5579543 := bstep (se 1 (by rfl) ⟨4184657, by rfl⟩ : syracuseStep 5579543 = 8369315) B8369315
theorem B3719695 : Blo 2203435 3719695 := bstep (se 1 (by rfl) ⟨2789771, by rfl⟩ : syracuseStep 3719695 = 5579543) B5579543
theorem B4959593 : Blo 2203435 4959593 := bstep (se 2 (by rfl) ⟨1859847, by rfl⟩ : syracuseStep 4959593 = 3719695) B3719695
theorem B3306395 : Blo 2203435 3306395 := bstep (se 1 (by rfl) ⟨2479796, by rfl⟩ : syracuseStep 3306395 = 4959593) B4959593
theorem B2204263 : Blo 2203435 2204263 := bstep (se 1 (by rfl) ⟨1653197, by rfl⟩ : syracuseStep 2204263 = 3306395) B3306395
theorem B2479801 : Blo 2203435 2479801 := bbase (se 2 (by rfl) ⟨929925, by rfl⟩ : syracuseStep 2479801 = 1859851) (by norm_num)
theorem B3306401 : Blo 2203435 3306401 := bstep (se 2 (by rfl) ⟨1239900, by rfl⟩ : syracuseStep 3306401 = 2479801) B2479801
theorem B2204267 : Blo 2203435 2204267 := bstep (se 1 (by rfl) ⟨1653200, by rfl⟩ : syracuseStep 2204267 = 3306401) B3306401
theorem B4707757 : Blo 2203435 4707757 := bbase (se 3 (by rfl) ⟨882704, by rfl⟩ : syracuseStep 4707757 = 1765409) (by norm_num)
theorem B6277009 : Blo 2203435 6277009 := bstep (se 2 (by rfl) ⟨2353878, by rfl⟩ : syracuseStep 6277009 = 4707757) B4707757
theorem B8369345 : Blo 2203435 8369345 := bstep (se 2 (by rfl) ⟨3138504, by rfl⟩ : syracuseStep 8369345 = 6277009) B6277009
theorem B5579563 : Blo 2203435 5579563 := bstep (se 1 (by rfl) ⟨4184672, by rfl⟩ : syracuseStep 5579563 = 8369345) B8369345
theorem B7439417 : Blo 2203435 7439417 := bstep (se 2 (by rfl) ⟨2789781, by rfl⟩ : syracuseStep 7439417 = 5579563) B5579563
theorem B4959611 : Blo 2203435 4959611 := bstep (se 1 (by rfl) ⟨3719708, by rfl⟩ : syracuseStep 4959611 = 7439417) B7439417
theorem B3306407 : Blo 2203435 3306407 := bstep (se 1 (by rfl) ⟨2479805, by rfl⟩ : syracuseStep 3306407 = 4959611) B4959611
theorem B2204271 : Blo 2203435 2204271 := bstep (se 1 (by rfl) ⟨1653203, by rfl⟩ : syracuseStep 2204271 = 3306407) B3306407
theorem B3306413 : Blo 2203435 3306413 := bbase (se 3 (by rfl) ⟨619952, by rfl⟩ : syracuseStep 3306413 = 1239905) (by norm_num)
theorem B2204275 : Blo 2203435 2204275 := bstep (se 1 (by rfl) ⟨1653206, by rfl⟩ : syracuseStep 2204275 = 3306413) B3306413
theorem B4959629 : Blo 2203435 4959629 := bbase (se 3 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 4959629 = 1859861) (by norm_num)
theorem B3306419 : Blo 2203435 3306419 := bstep (se 1 (by rfl) ⟨2479814, by rfl⟩ : syracuseStep 3306419 = 4959629) B4959629
theorem B2204279 : Blo 2203435 2204279 := bstep (se 1 (by rfl) ⟨1653209, by rfl⟩ : syracuseStep 2204279 = 3306419) B3306419
theorem B2789797 : Blo 2203435 2789797 := bbase (se 4 (by rfl) ⟨261543, by rfl⟩ : syracuseStep 2789797 = 523087) (by norm_num)
theorem B3719729 : Blo 2203435 3719729 := bstep (se 2 (by rfl) ⟨1394898, by rfl⟩ : syracuseStep 3719729 = 2789797) B2789797
theorem B2479819 : Blo 2203435 2479819 := bstep (se 1 (by rfl) ⟨1859864, by rfl⟩ : syracuseStep 2479819 = 3719729) B3719729
theorem B3306425 : Blo 2203435 3306425 := bstep (se 2 (by rfl) ⟨1239909, by rfl⟩ : syracuseStep 3306425 = 2479819) B2479819
theorem B2204283 : Blo 2203435 2204283 := bstep (se 1 (by rfl) ⟨1653212, by rfl⟩ : syracuseStep 2204283 = 3306425) B3306425
theorem B2979149 : Blo 2203435 2979149 := bbase (se 3 (by rfl) ⟨558590, by rfl⟩ : syracuseStep 2979149 = 1117181) (by norm_num)
theorem B31777589 : Blo 2203435 31777589 := bstep (se 5 (by rfl) ⟨1489574, by rfl⟩ : syracuseStep 31777589 = 2979149) B2979149
theorem B21185059 : Blo 2203435 21185059 := bstep (se 1 (by rfl) ⟨15888794, by rfl⟩ : syracuseStep 21185059 = 31777589) B31777589
theorem B28246745 : Blo 2203435 28246745 := bstep (se 2 (by rfl) ⟨10592529, by rfl⟩ : syracuseStep 28246745 = 21185059) B21185059
theorem B18831163 : Blo 2203435 18831163 := bstep (se 1 (by rfl) ⟨14123372, by rfl⟩ : syracuseStep 18831163 = 28246745) B28246745
theorem B25108217 : Blo 2203435 25108217 := bstep (se 2 (by rfl) ⟨9415581, by rfl⟩ : syracuseStep 25108217 = 18831163) B18831163
theorem B16738811 : Blo 2203435 16738811 := bstep (se 1 (by rfl) ⟨12554108, by rfl⟩ : syracuseStep 16738811 = 25108217) B25108217
theorem B11159207 : Blo 2203435 11159207 := bstep (se 1 (by rfl) ⟨8369405, by rfl⟩ : syracuseStep 11159207 = 16738811) B16738811
theorem B7439471 : Blo 2203435 7439471 := bstep (se 1 (by rfl) ⟨5579603, by rfl⟩ : syracuseStep 7439471 = 11159207) B11159207
theorem B4959647 : Blo 2203435 4959647 := bstep (se 1 (by rfl) ⟨3719735, by rfl⟩ : syracuseStep 4959647 = 7439471) B7439471
theorem B3306431 : Blo 2203435 3306431 := bstep (se 1 (by rfl) ⟨2479823, by rfl⟩ : syracuseStep 3306431 = 4959647) B4959647
theorem B2204287 : Blo 2203435 2204287 := bstep (se 1 (by rfl) ⟨1653215, by rfl⟩ : syracuseStep 2204287 = 3306431) B3306431
theorem B3306437 : Blo 2203435 3306437 := bbase (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) (by norm_num)
theorem B2204291 : Blo 2203435 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B3719749 : Blo 2203435 3719749 := bbase (se 4 (by rfl) ⟨348726, by rfl⟩ : syracuseStep 3719749 = 697453) (by norm_num)
theorem B4959665 : Blo 2203435 4959665 := bstep (se 2 (by rfl) ⟨1859874, by rfl⟩ : syracuseStep 4959665 = 3719749) B3719749
theorem B3306443 : Blo 2203435 3306443 := bstep (se 1 (by rfl) ⟨2479832, by rfl⟩ : syracuseStep 3306443 = 4959665) B4959665
theorem B2204295 : Blo 2203435 2204295 := bstep (se 1 (by rfl) ⟨1653221, by rfl⟩ : syracuseStep 2204295 = 3306443) B3306443
theorem B2479837 : Blo 2203435 2479837 := bbase (se 3 (by rfl) ⟨464969, by rfl⟩ : syracuseStep 2479837 = 929939) (by norm_num)
theorem B3306449 : Blo 2203435 3306449 := bstep (se 2 (by rfl) ⟨1239918, by rfl⟩ : syracuseStep 3306449 = 2479837) B2479837
theorem B2204299 : Blo 2203435 2204299 := bstep (se 1 (by rfl) ⟨1653224, by rfl⟩ : syracuseStep 2204299 = 3306449) B3306449
theorem B7439525 : Blo 2203435 7439525 := bbase (se 4 (by rfl) ⟨697455, by rfl⟩ : syracuseStep 7439525 = 1394911) (by norm_num)
theorem B4959683 : Blo 2203435 4959683 := bstep (se 1 (by rfl) ⟨3719762, by rfl⟩ : syracuseStep 4959683 = 7439525) B7439525
theorem B3306455 : Blo 2203435 3306455 := bstep (se 1 (by rfl) ⟨2479841, by rfl⟩ : syracuseStep 3306455 = 4959683) B4959683
theorem B2204303 : Blo 2203435 2204303 := bstep (se 1 (by rfl) ⟨1653227, by rfl⟩ : syracuseStep 2204303 = 3306455) B3306455
theorem B3306461 : Blo 2203435 3306461 := bbase (se 3 (by rfl) ⟨619961, by rfl⟩ : syracuseStep 3306461 = 1239923) (by norm_num)
theorem B2204307 : Blo 2203435 2204307 := bstep (se 1 (by rfl) ⟨1653230, by rfl⟩ : syracuseStep 2204307 = 3306461) B3306461
theorem B4959701 : Blo 2203435 4959701 := bbase (se 7 (by rfl) ⟨58121, by rfl⟩ : syracuseStep 4959701 = 116243) (by norm_num)
theorem B3306467 : Blo 2203435 3306467 := bstep (se 1 (by rfl) ⟨2479850, by rfl⟩ : syracuseStep 3306467 = 4959701) B4959701
theorem B2204311 : Blo 2203435 2204311 := bstep (se 1 (by rfl) ⟨1653233, by rfl⟩ : syracuseStep 2204311 = 3306467) B3306467
theorem B21185333 : Blo 2203435 21185333 := bbase (se 5 (by rfl) ⟨993062, by rfl⟩ : syracuseStep 21185333 = 1986125) (by norm_num)
theorem B14123555 : Blo 2203435 14123555 := bstep (se 1 (by rfl) ⟨10592666, by rfl⟩ : syracuseStep 14123555 = 21185333) B21185333
theorem B9415703 : Blo 2203435 9415703 := bstep (se 1 (by rfl) ⟨7061777, by rfl⟩ : syracuseStep 9415703 = 14123555) B14123555
theorem B6277135 : Blo 2203435 6277135 := bstep (se 1 (by rfl) ⟨4707851, by rfl⟩ : syracuseStep 6277135 = 9415703) B9415703
theorem B8369513 : Blo 2203435 8369513 := bstep (se 2 (by rfl) ⟨3138567, by rfl⟩ : syracuseStep 8369513 = 6277135) B6277135
theorem B5579675 : Blo 2203435 5579675 := bstep (se 1 (by rfl) ⟨4184756, by rfl⟩ : syracuseStep 5579675 = 8369513) B8369513
theorem B3719783 : Blo 2203435 3719783 := bstep (se 1 (by rfl) ⟨2789837, by rfl⟩ : syracuseStep 3719783 = 5579675) B5579675
theorem B2479855 : Blo 2203435 2479855 := bstep (se 1 (by rfl) ⟨1859891, by rfl⟩ : syracuseStep 2479855 = 3719783) B3719783
theorem B3306473 : Blo 2203435 3306473 := bstep (se 2 (by rfl) ⟨1239927, by rfl⟩ : syracuseStep 3306473 = 2479855) B2479855
theorem B2204315 : Blo 2203435 2204315 := bstep (se 1 (by rfl) ⟨1653236, by rfl⟩ : syracuseStep 2204315 = 3306473) B3306473
theorem B3874133 : Blo 2203435 3874133 := bbase (se 11 (by rfl) ⟨2837, by rfl⟩ : syracuseStep 3874133 = 5675) (by norm_num)
theorem B10331021 : Blo 2203435 10331021 := bstep (se 3 (by rfl) ⟨1937066, by rfl⟩ : syracuseStep 10331021 = 3874133) B3874133
theorem B27549389 : Blo 2203435 27549389 := bstep (se 3 (by rfl) ⟨5165510, by rfl⟩ : syracuseStep 27549389 = 10331021) B10331021
theorem B18366259 : Blo 2203435 18366259 := bstep (se 1 (by rfl) ⟨13774694, by rfl⟩ : syracuseStep 18366259 = 27549389) B27549389
theorem B24488345 : Blo 2203435 24488345 := bstep (se 2 (by rfl) ⟨9183129, by rfl⟩ : syracuseStep 24488345 = 18366259) B18366259
theorem B16325563 : Blo 2203435 16325563 := bstep (se 1 (by rfl) ⟨12244172, by rfl⟩ : syracuseStep 16325563 = 24488345) B24488345
theorem B21767417 : Blo 2203435 21767417 := bstep (se 2 (by rfl) ⟨8162781, by rfl⟩ : syracuseStep 21767417 = 16325563) B16325563
theorem B14511611 : Blo 2203435 14511611 := bstep (se 1 (by rfl) ⟨10883708, by rfl⟩ : syracuseStep 14511611 = 21767417) B21767417
theorem B9674407 : Blo 2203435 9674407 := bstep (se 1 (by rfl) ⟨7255805, by rfl⟩ : syracuseStep 9674407 = 14511611) B14511611
theorem B12899209 : Blo 2203435 12899209 := bstep (se 2 (by rfl) ⟨4837203, by rfl⟩ : syracuseStep 12899209 = 9674407) B9674407
theorem B17198945 : Blo 2203435 17198945 := bstep (se 2 (by rfl) ⟨6449604, by rfl⟩ : syracuseStep 17198945 = 12899209) B12899209
theorem B11465963 : Blo 2203435 11465963 := bstep (se 1 (by rfl) ⟨8599472, by rfl⟩ : syracuseStep 11465963 = 17198945) B17198945
theorem B7643975 : Blo 2203435 7643975 := bstep (se 1 (by rfl) ⟨5732981, by rfl⟩ : syracuseStep 7643975 = 11465963) B11465963
theorem B20383933 : Blo 2203435 20383933 := bstep (se 3 (by rfl) ⟨3821987, by rfl⟩ : syracuseStep 20383933 = 7643975) B7643975
theorem B27178577 : Blo 2203435 27178577 := bstep (se 2 (by rfl) ⟨10191966, by rfl⟩ : syracuseStep 27178577 = 20383933) B20383933
theorem B18119051 : Blo 2203435 18119051 := bstep (se 1 (by rfl) ⟨13589288, by rfl⟩ : syracuseStep 18119051 = 27178577) B27178577
theorem B12079367 : Blo 2203435 12079367 := bstep (se 1 (by rfl) ⟨9059525, by rfl⟩ : syracuseStep 12079367 = 18119051) B18119051
theorem B8052911 : Blo 2203435 8052911 := bstep (se 1 (by rfl) ⟨6039683, by rfl⟩ : syracuseStep 8052911 = 12079367) B12079367
theorem B5368607 : Blo 2203435 5368607 := bstep (se 1 (by rfl) ⟨4026455, by rfl⟩ : syracuseStep 5368607 = 8052911) B8052911
theorem B3579071 : Blo 2203435 3579071 := bstep (se 1 (by rfl) ⟨2684303, by rfl⟩ : syracuseStep 3579071 = 5368607) B5368607
theorem B9544189 : Blo 2203435 9544189 := bstep (se 3 (by rfl) ⟨1789535, by rfl⟩ : syracuseStep 9544189 = 3579071) B3579071
theorem B12725585 : Blo 2203435 12725585 := bstep (se 2 (by rfl) ⟨4772094, by rfl⟩ : syracuseStep 12725585 = 9544189) B9544189
theorem B8483723 : Blo 2203435 8483723 := bstep (se 1 (by rfl) ⟨6362792, by rfl⟩ : syracuseStep 8483723 = 12725585) B12725585
theorem B5655815 : Blo 2203435 5655815 := bstep (se 1 (by rfl) ⟨4241861, by rfl⟩ : syracuseStep 5655815 = 8483723) B8483723
theorem B3770543 : Blo 2203435 3770543 := bstep (se 1 (by rfl) ⟨2827907, by rfl⟩ : syracuseStep 3770543 = 5655815) B5655815
theorem B2513695 : Blo 2203435 2513695 := bstep (se 1 (by rfl) ⟨1885271, by rfl⟩ : syracuseStep 2513695 = 3770543) B3770543
theorem B3351593 : Blo 2203435 3351593 := bstep (se 2 (by rfl) ⟨1256847, by rfl⟩ : syracuseStep 3351593 = 2513695) B2513695
theorem B2234395 : Blo 2203435 2234395 := bstep (se 1 (by rfl) ⟨1675796, by rfl⟩ : syracuseStep 2234395 = 3351593) B3351593
theorem B2979193 : Blo 2203435 2979193 := bstep (se 2 (by rfl) ⟨1117197, by rfl⟩ : syracuseStep 2979193 = 2234395) B2234395
theorem B3972257 : Blo 2203435 3972257 := bstep (se 2 (by rfl) ⟨1489596, by rfl⟩ : syracuseStep 3972257 = 2979193) B2979193
theorem B2648171 : Blo 2203435 2648171 := bstep (se 1 (by rfl) ⟨1986128, by rfl⟩ : syracuseStep 2648171 = 3972257) B3972257
theorem B7061789 : Blo 2203435 7061789 := bstep (se 3 (by rfl) ⟨1324085, by rfl⟩ : syracuseStep 7061789 = 2648171) B2648171
theorem B18831437 : Blo 2203435 18831437 := bstep (se 3 (by rfl) ⟨3530894, by rfl⟩ : syracuseStep 18831437 = 7061789) B7061789
theorem B12554291 : Blo 2203435 12554291 := bstep (se 1 (by rfl) ⟨9415718, by rfl⟩ : syracuseStep 12554291 = 18831437) B18831437
theorem B8369527 : Blo 2203435 8369527 := bstep (se 1 (by rfl) ⟨6277145, by rfl⟩ : syracuseStep 8369527 = 12554291) B12554291
theorem B11159369 : Blo 2203435 11159369 := bstep (se 2 (by rfl) ⟨4184763, by rfl⟩ : syracuseStep 11159369 = 8369527) B8369527
theorem B7439579 : Blo 2203435 7439579 := bstep (se 1 (by rfl) ⟨5579684, by rfl⟩ : syracuseStep 7439579 = 11159369) B11159369
theorem B4959719 : Blo 2203435 4959719 := bstep (se 1 (by rfl) ⟨3719789, by rfl⟩ : syracuseStep 4959719 = 7439579) B7439579
theorem B3306479 : Blo 2203435 3306479 := bstep (se 1 (by rfl) ⟨2479859, by rfl⟩ : syracuseStep 3306479 = 4959719) B4959719
theorem B2204319 : Blo 2203435 2204319 := bstep (se 1 (by rfl) ⟨1653239, by rfl⟩ : syracuseStep 2204319 = 3306479) B3306479
theorem B3306485 : Blo 2203435 3306485 := bbase (se 5 (by rfl) ⟨154991, by rfl⟩ : syracuseStep 3306485 = 309983) (by norm_num)
theorem B2204323 : Blo 2203435 2204323 := bstep (se 1 (by rfl) ⟨1653242, by rfl⟩ : syracuseStep 2204323 = 3306485) B3306485
theorem B4707877 : Blo 2203435 4707877 := bbase (se 4 (by rfl) ⟨441363, by rfl⟩ : syracuseStep 4707877 = 882727) (by norm_num)
theorem B6277169 : Blo 2203435 6277169 := bstep (se 2 (by rfl) ⟨2353938, by rfl⟩ : syracuseStep 6277169 = 4707877) B4707877
theorem B4184779 : Blo 2203435 4184779 := bstep (se 1 (by rfl) ⟨3138584, by rfl⟩ : syracuseStep 4184779 = 6277169) B6277169
theorem B5579705 : Blo 2203435 5579705 := bstep (se 2 (by rfl) ⟨2092389, by rfl⟩ : syracuseStep 5579705 = 4184779) B4184779
theorem B3719803 : Blo 2203435 3719803 := bstep (se 1 (by rfl) ⟨2789852, by rfl⟩ : syracuseStep 3719803 = 5579705) B5579705
theorem B4959737 : Blo 2203435 4959737 := bstep (se 2 (by rfl) ⟨1859901, by rfl⟩ : syracuseStep 4959737 = 3719803) B3719803
theorem B3306491 : Blo 2203435 3306491 := bstep (se 1 (by rfl) ⟨2479868, by rfl⟩ : syracuseStep 3306491 = 4959737) B4959737
theorem B2204327 : Blo 2203435 2204327 := bstep (se 1 (by rfl) ⟨1653245, by rfl⟩ : syracuseStep 2204327 = 3306491) B3306491
theorem B2479873 : Blo 2203435 2479873 := bbase (se 2 (by rfl) ⟨929952, by rfl⟩ : syracuseStep 2479873 = 1859905) (by norm_num)
theorem B3306497 : Blo 2203435 3306497 := bstep (se 2 (by rfl) ⟨1239936, by rfl⟩ : syracuseStep 3306497 = 2479873) B2479873
theorem B2204331 : Blo 2203435 2204331 := bstep (se 1 (by rfl) ⟨1653248, by rfl⟩ : syracuseStep 2204331 = 3306497) B3306497
theorem B5579725 : Blo 2203435 5579725 := bbase (se 3 (by rfl) ⟨1046198, by rfl⟩ : syracuseStep 5579725 = 2092397) (by norm_num)
theorem B7439633 : Blo 2203435 7439633 := bstep (se 2 (by rfl) ⟨2789862, by rfl⟩ : syracuseStep 7439633 = 5579725) B5579725
theorem B4959755 : Blo 2203435 4959755 := bstep (se 1 (by rfl) ⟨3719816, by rfl⟩ : syracuseStep 4959755 = 7439633) B7439633
theorem B3306503 : Blo 2203435 3306503 := bstep (se 1 (by rfl) ⟨2479877, by rfl⟩ : syracuseStep 3306503 = 4959755) B4959755
theorem B2204335 : Blo 2203435 2204335 := bstep (se 1 (by rfl) ⟨1653251, by rfl⟩ : syracuseStep 2204335 = 3306503) B3306503
theorem B3306509 : Blo 2203435 3306509 := bbase (se 3 (by rfl) ⟨619970, by rfl⟩ : syracuseStep 3306509 = 1239941) (by norm_num)
theorem B2204339 : Blo 2203435 2204339 := bstep (se 1 (by rfl) ⟨1653254, by rfl⟩ : syracuseStep 2204339 = 3306509) B3306509
theorem B4959773 : Blo 2203435 4959773 := bbase (se 3 (by rfl) ⟨929957, by rfl⟩ : syracuseStep 4959773 = 1859915) (by norm_num)
theorem B3306515 : Blo 2203435 3306515 := bstep (se 1 (by rfl) ⟨2479886, by rfl⟩ : syracuseStep 3306515 = 4959773) B4959773
theorem B2204343 : Blo 2203435 2204343 := bstep (se 1 (by rfl) ⟨1653257, by rfl⟩ : syracuseStep 2204343 = 3306515) B3306515
theorem B3719837 : Blo 2203435 3719837 := bbase (se 3 (by rfl) ⟨697469, by rfl⟩ : syracuseStep 3719837 = 1394939) (by norm_num)
theorem B2479891 : Blo 2203435 2479891 := bstep (se 1 (by rfl) ⟨1859918, by rfl⟩ : syracuseStep 2479891 = 3719837) B3719837
theorem B3306521 : Blo 2203435 3306521 := bstep (se 2 (by rfl) ⟨1239945, by rfl⟩ : syracuseStep 3306521 = 2479891) B2479891
theorem B2204347 : Blo 2203435 2204347 := bstep (se 1 (by rfl) ⟨1653260, by rfl⟩ : syracuseStep 2204347 = 3306521) B3306521
theorem B4299797 : Blo 2203435 4299797 := bbase (se 6 (by rfl) ⟨100776, by rfl⟩ : syracuseStep 4299797 = 201553) (by norm_num)
theorem B2866531 : Blo 2203435 2866531 := bstep (se 1 (by rfl) ⟨2149898, by rfl⟩ : syracuseStep 2866531 = 4299797) B4299797
theorem B3822041 : Blo 2203435 3822041 := bstep (se 2 (by rfl) ⟨1433265, by rfl⟩ : syracuseStep 3822041 = 2866531) B2866531
theorem B2548027 : Blo 2203435 2548027 := bstep (se 1 (by rfl) ⟨1911020, by rfl⟩ : syracuseStep 2548027 = 3822041) B3822041
theorem B13589477 : Blo 2203435 13589477 := bstep (se 4 (by rfl) ⟨1274013, by rfl⟩ : syracuseStep 13589477 = 2548027) B2548027
theorem B9059651 : Blo 2203435 9059651 := bstep (se 1 (by rfl) ⟨6794738, by rfl⟩ : syracuseStep 9059651 = 13589477) B13589477
theorem B6039767 : Blo 2203435 6039767 := bstep (se 1 (by rfl) ⟨4529825, by rfl⟩ : syracuseStep 6039767 = 9059651) B9059651
theorem B4026511 : Blo 2203435 4026511 := bstep (se 1 (by rfl) ⟨3019883, by rfl⟩ : syracuseStep 4026511 = 6039767) B6039767
theorem B5368681 : Blo 2203435 5368681 := bstep (se 2 (by rfl) ⟨2013255, by rfl⟩ : syracuseStep 5368681 = 4026511) B4026511
theorem B7158241 : Blo 2203435 7158241 := bstep (se 2 (by rfl) ⟨2684340, by rfl⟩ : syracuseStep 7158241 = 5368681) B5368681
theorem B9544321 : Blo 2203435 9544321 := bstep (se 2 (by rfl) ⟨3579120, by rfl⟩ : syracuseStep 9544321 = 7158241) B7158241
theorem B12725761 : Blo 2203435 12725761 := bstep (se 2 (by rfl) ⟨4772160, by rfl⟩ : syracuseStep 12725761 = 9544321) B9544321
theorem B16967681 : Blo 2203435 16967681 := bstep (se 2 (by rfl) ⟨6362880, by rfl⟩ : syracuseStep 16967681 = 12725761) B12725761
theorem B11311787 : Blo 2203435 11311787 := bstep (se 1 (by rfl) ⟨8483840, by rfl⟩ : syracuseStep 11311787 = 16967681) B16967681
theorem B7541191 : Blo 2203435 7541191 := bstep (se 1 (by rfl) ⟨5655893, by rfl⟩ : syracuseStep 7541191 = 11311787) B11311787
theorem B10054921 : Blo 2203435 10054921 := bstep (se 2 (by rfl) ⟨3770595, by rfl⟩ : syracuseStep 10054921 = 7541191) B7541191
theorem B13406561 : Blo 2203435 13406561 := bstep (se 2 (by rfl) ⟨5027460, by rfl⟩ : syracuseStep 13406561 = 10054921) B10054921
theorem B8937707 : Blo 2203435 8937707 := bstep (se 1 (by rfl) ⟨6703280, by rfl⟩ : syracuseStep 8937707 = 13406561) B13406561
theorem B23833885 : Blo 2203435 23833885 := bstep (se 3 (by rfl) ⟨4468853, by rfl⟩ : syracuseStep 23833885 = 8937707) B8937707
theorem B31778513 : Blo 2203435 31778513 := bstep (se 2 (by rfl) ⟨11916942, by rfl⟩ : syracuseStep 31778513 = 23833885) B23833885
theorem B21185675 : Blo 2203435 21185675 := bstep (se 1 (by rfl) ⟨15889256, by rfl⟩ : syracuseStep 21185675 = 31778513) B31778513
theorem B14123783 : Blo 2203435 14123783 := bstep (se 1 (by rfl) ⟨10592837, by rfl⟩ : syracuseStep 14123783 = 21185675) B21185675
theorem B9415855 : Blo 2203435 9415855 := bstep (se 1 (by rfl) ⟨7061891, by rfl⟩ : syracuseStep 9415855 = 14123783) B14123783
theorem B12554473 : Blo 2203435 12554473 := bstep (se 2 (by rfl) ⟨4707927, by rfl⟩ : syracuseStep 12554473 = 9415855) B9415855
theorem B16739297 : Blo 2203435 16739297 := bstep (se 2 (by rfl) ⟨6277236, by rfl⟩ : syracuseStep 16739297 = 12554473) B12554473
theorem B11159531 : Blo 2203435 11159531 := bstep (se 1 (by rfl) ⟨8369648, by rfl⟩ : syracuseStep 11159531 = 16739297) B16739297
theorem B7439687 : Blo 2203435 7439687 := bstep (se 1 (by rfl) ⟨5579765, by rfl⟩ : syracuseStep 7439687 = 11159531) B11159531
theorem B4959791 : Blo 2203435 4959791 := bstep (se 1 (by rfl) ⟨3719843, by rfl⟩ : syracuseStep 4959791 = 7439687) B7439687
theorem B3306527 : Blo 2203435 3306527 := bstep (se 1 (by rfl) ⟨2479895, by rfl⟩ : syracuseStep 3306527 = 4959791) B4959791
theorem B2204351 : Blo 2203435 2204351 := bstep (se 1 (by rfl) ⟨1653263, by rfl⟩ : syracuseStep 2204351 = 3306527) B3306527
theorem B3306533 : Blo 2203435 3306533 := bbase (se 4 (by rfl) ⟨309987, by rfl⟩ : syracuseStep 3306533 = 619975) (by norm_num)
theorem B2204355 : Blo 2203435 2204355 := bstep (se 1 (by rfl) ⟨1653266, by rfl⟩ : syracuseStep 2204355 = 3306533) B3306533
theorem B2789893 : Blo 2203435 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B3719857 : Blo 2203435 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B4959809 : Blo 2203435 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B3306539 : Blo 2203435 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B2204359 : Blo 2203435 2204359 := bstep (se 1 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 2204359 = 3306539) B3306539
theorem B2479909 : Blo 2203435 2479909 := bbase (se 4 (by rfl) ⟨232491, by rfl⟩ : syracuseStep 2479909 = 464983) (by norm_num)
theorem B3306545 : Blo 2203435 3306545 := bstep (se 2 (by rfl) ⟨1239954, by rfl⟩ : syracuseStep 3306545 = 2479909) B2479909
theorem B2204363 : Blo 2203435 2204363 := bstep (se 1 (by rfl) ⟨1653272, by rfl⟩ : syracuseStep 2204363 = 3306545) B3306545
theorem B9415925 : Blo 2203435 9415925 := bbase (se 5 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 9415925 = 882743) (by norm_num)
theorem B6277283 : Blo 2203435 6277283 := bstep (se 1 (by rfl) ⟨4707962, by rfl⟩ : syracuseStep 6277283 = 9415925) B9415925
theorem B4184855 : Blo 2203435 4184855 := bstep (se 1 (by rfl) ⟨3138641, by rfl⟩ : syracuseStep 4184855 = 6277283) B6277283
theorem B2789903 : Blo 2203435 2789903 := bstep (se 1 (by rfl) ⟨2092427, by rfl⟩ : syracuseStep 2789903 = 4184855) B4184855
theorem B7439741 : Blo 2203435 7439741 := bstep (se 3 (by rfl) ⟨1394951, by rfl⟩ : syracuseStep 7439741 = 2789903) B2789903
theorem B4959827 : Blo 2203435 4959827 := bstep (se 1 (by rfl) ⟨3719870, by rfl⟩ : syracuseStep 4959827 = 7439741) B7439741
theorem B3306551 : Blo 2203435 3306551 := bstep (se 1 (by rfl) ⟨2479913, by rfl⟩ : syracuseStep 3306551 = 4959827) B4959827
theorem B2204367 : Blo 2203435 2204367 := bstep (se 1 (by rfl) ⟨1653275, by rfl⟩ : syracuseStep 2204367 = 3306551) B3306551
theorem B3306557 : Blo 2203435 3306557 := bbase (se 3 (by rfl) ⟨619979, by rfl⟩ : syracuseStep 3306557 = 1239959) (by norm_num)
theorem B2204371 : Blo 2203435 2204371 := bstep (se 1 (by rfl) ⟨1653278, by rfl⟩ : syracuseStep 2204371 = 3306557) B3306557
theorem B4959845 : Blo 2203435 4959845 := bbase (se 4 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 4959845 = 929971) (by norm_num)
theorem B3306563 : Blo 2203435 3306563 := bstep (se 1 (by rfl) ⟨2479922, by rfl⟩ : syracuseStep 3306563 = 4959845) B4959845
theorem B2204375 : Blo 2203435 2204375 := bstep (se 1 (by rfl) ⟨1653281, by rfl⟩ : syracuseStep 2204375 = 3306563) B3306563
theorem B5579837 : Blo 2203435 5579837 := bbase (se 3 (by rfl) ⟨1046219, by rfl⟩ : syracuseStep 5579837 = 2092439) (by norm_num)
theorem B3719891 : Blo 2203435 3719891 := bstep (se 1 (by rfl) ⟨2789918, by rfl⟩ : syracuseStep 3719891 = 5579837) B5579837
theorem B2479927 : Blo 2203435 2479927 := bstep (se 1 (by rfl) ⟨1859945, by rfl⟩ : syracuseStep 2479927 = 3719891) B3719891
theorem B3306569 : Blo 2203435 3306569 := bstep (se 2 (by rfl) ⟨1239963, by rfl⟩ : syracuseStep 3306569 = 2479927) B2479927
theorem B2204379 : Blo 2203435 2204379 := bstep (se 1 (by rfl) ⟨1653284, by rfl⟩ : syracuseStep 2204379 = 3306569) B3306569
theorem B4184885 : Blo 2203435 4184885 := bbase (se 5 (by rfl) ⟨196166, by rfl⟩ : syracuseStep 4184885 = 392333) (by norm_num)
theorem B11159693 : Blo 2203435 11159693 := bstep (se 3 (by rfl) ⟨2092442, by rfl⟩ : syracuseStep 11159693 = 4184885) B4184885
theorem B7439795 : Blo 2203435 7439795 := bstep (se 1 (by rfl) ⟨5579846, by rfl⟩ : syracuseStep 7439795 = 11159693) B11159693
theorem B4959863 : Blo 2203435 4959863 := bstep (se 1 (by rfl) ⟨3719897, by rfl⟩ : syracuseStep 4959863 = 7439795) B7439795
theorem B3306575 : Blo 2203435 3306575 := bstep (se 1 (by rfl) ⟨2479931, by rfl⟩ : syracuseStep 3306575 = 4959863) B4959863
theorem B2204383 : Blo 2203435 2204383 := bstep (se 1 (by rfl) ⟨1653287, by rfl⟩ : syracuseStep 2204383 = 3306575) B3306575
theorem B3306581 : Blo 2203435 3306581 := bbase (se 8 (by rfl) ⟨19374, by rfl⟩ : syracuseStep 3306581 = 38749) (by norm_num)
theorem B2204387 : Blo 2203435 2204387 := bstep (se 1 (by rfl) ⟨1653290, by rfl⟩ : syracuseStep 2204387 = 3306581) B3306581
theorem B5655997 : Blo 2203435 5655997 := bbase (se 3 (by rfl) ⟨1060499, by rfl⟩ : syracuseStep 5655997 = 2120999) (by norm_num)
theorem B7541329 : Blo 2203435 7541329 := bstep (se 2 (by rfl) ⟨2827998, by rfl⟩ : syracuseStep 7541329 = 5655997) B5655997
theorem B10055105 : Blo 2203435 10055105 := bstep (se 2 (by rfl) ⟨3770664, by rfl⟩ : syracuseStep 10055105 = 7541329) B7541329
theorem B6703403 : Blo 2203435 6703403 := bstep (se 1 (by rfl) ⟨5027552, by rfl⟩ : syracuseStep 6703403 = 10055105) B10055105
theorem B17875741 : Blo 2203435 17875741 := bstep (se 3 (by rfl) ⟨3351701, by rfl⟩ : syracuseStep 17875741 = 6703403) B6703403
theorem B23834321 : Blo 2203435 23834321 := bstep (se 2 (by rfl) ⟨8937870, by rfl⟩ : syracuseStep 23834321 = 17875741) B17875741
theorem B15889547 : Blo 2203435 15889547 := bstep (se 1 (by rfl) ⟨11917160, by rfl⟩ : syracuseStep 15889547 = 23834321) B23834321
theorem B10593031 : Blo 2203435 10593031 := bstep (se 1 (by rfl) ⟨7944773, by rfl⟩ : syracuseStep 10593031 = 15889547) B15889547
theorem B14124041 : Blo 2203435 14124041 := bstep (se 2 (by rfl) ⟨5296515, by rfl⟩ : syracuseStep 14124041 = 10593031) B10593031
theorem B9416027 : Blo 2203435 9416027 := bstep (se 1 (by rfl) ⟨7062020, by rfl⟩ : syracuseStep 9416027 = 14124041) B14124041
theorem B6277351 : Blo 2203435 6277351 := bstep (se 1 (by rfl) ⟨4708013, by rfl⟩ : syracuseStep 6277351 = 9416027) B9416027
theorem B8369801 : Blo 2203435 8369801 := bstep (se 2 (by rfl) ⟨3138675, by rfl⟩ : syracuseStep 8369801 = 6277351) B6277351
theorem B5579867 : Blo 2203435 5579867 := bstep (se 1 (by rfl) ⟨4184900, by rfl⟩ : syracuseStep 5579867 = 8369801) B8369801
theorem B3719911 : Blo 2203435 3719911 := bstep (se 1 (by rfl) ⟨2789933, by rfl⟩ : syracuseStep 3719911 = 5579867) B5579867
theorem B4959881 : Blo 2203435 4959881 := bstep (se 2 (by rfl) ⟨1859955, by rfl⟩ : syracuseStep 4959881 = 3719911) B3719911
theorem B3306587 : Blo 2203435 3306587 := bstep (se 1 (by rfl) ⟨2479940, by rfl⟩ : syracuseStep 3306587 = 4959881) B4959881
theorem B2204391 : Blo 2203435 2204391 := bstep (se 1 (by rfl) ⟨1653293, by rfl⟩ : syracuseStep 2204391 = 3306587) B3306587
theorem B2479945 : Blo 2203435 2479945 := bbase (se 2 (by rfl) ⟨929979, by rfl⟩ : syracuseStep 2479945 = 1859959) (by norm_num)
theorem B3306593 : Blo 2203435 3306593 := bstep (se 2 (by rfl) ⟨1239972, by rfl⟩ : syracuseStep 3306593 = 2479945) B2479945
theorem B2204395 : Blo 2203435 2204395 := bstep (se 1 (by rfl) ⟨1653296, by rfl⟩ : syracuseStep 2204395 = 3306593) B3306593
theorem B10055141 : Blo 2203435 10055141 := bbase (se 4 (by rfl) ⟨942669, by rfl⟩ : syracuseStep 10055141 = 1885339) (by norm_num)
theorem B6703427 : Blo 2203435 6703427 := bstep (se 1 (by rfl) ⟨5027570, by rfl⟩ : syracuseStep 6703427 = 10055141) B10055141
theorem B4468951 : Blo 2203435 4468951 := bstep (se 1 (by rfl) ⟨3351713, by rfl⟩ : syracuseStep 4468951 = 6703427) B6703427
theorem B23834405 : Blo 2203435 23834405 := bstep (se 4 (by rfl) ⟨2234475, by rfl⟩ : syracuseStep 23834405 = 4468951) B4468951
theorem B15889603 : Blo 2203435 15889603 := bstep (se 1 (by rfl) ⟨11917202, by rfl⟩ : syracuseStep 15889603 = 23834405) B23834405
theorem B21186137 : Blo 2203435 21186137 := bstep (se 2 (by rfl) ⟨7944801, by rfl⟩ : syracuseStep 21186137 = 15889603) B15889603
theorem B14124091 : Blo 2203435 14124091 := bstep (se 1 (by rfl) ⟨10593068, by rfl⟩ : syracuseStep 14124091 = 21186137) B21186137
theorem B18832121 : Blo 2203435 18832121 := bstep (se 2 (by rfl) ⟨7062045, by rfl⟩ : syracuseStep 18832121 = 14124091) B14124091
theorem B12554747 : Blo 2203435 12554747 := bstep (se 1 (by rfl) ⟨9416060, by rfl⟩ : syracuseStep 12554747 = 18832121) B18832121
theorem B8369831 : Blo 2203435 8369831 := bstep (se 1 (by rfl) ⟨6277373, by rfl⟩ : syracuseStep 8369831 = 12554747) B12554747
theorem B5579887 : Blo 2203435 5579887 := bstep (se 1 (by rfl) ⟨4184915, by rfl⟩ : syracuseStep 5579887 = 8369831) B8369831
theorem B7439849 : Blo 2203435 7439849 := bstep (se 2 (by rfl) ⟨2789943, by rfl⟩ : syracuseStep 7439849 = 5579887) B5579887
theorem B4959899 : Blo 2203435 4959899 := bstep (se 1 (by rfl) ⟨3719924, by rfl⟩ : syracuseStep 4959899 = 7439849) B7439849
theorem B3306599 : Blo 2203435 3306599 := bstep (se 1 (by rfl) ⟨2479949, by rfl⟩ : syracuseStep 3306599 = 4959899) B4959899
theorem B2204399 : Blo 2203435 2204399 := bstep (se 1 (by rfl) ⟨1653299, by rfl⟩ : syracuseStep 2204399 = 3306599) B3306599
theorem B3306605 : Blo 2203435 3306605 := bbase (se 3 (by rfl) ⟨619988, by rfl⟩ : syracuseStep 3306605 = 1239977) (by norm_num)
theorem B2204403 : Blo 2203435 2204403 := bstep (se 1 (by rfl) ⟨1653302, by rfl⟩ : syracuseStep 2204403 = 3306605) B3306605
theorem B4959917 : Blo 2203435 4959917 := bbase (se 3 (by rfl) ⟨929984, by rfl⟩ : syracuseStep 4959917 = 1859969) (by norm_num)
theorem B3306611 : Blo 2203435 3306611 := bstep (se 1 (by rfl) ⟨2479958, by rfl⟩ : syracuseStep 3306611 = 4959917) B4959917
theorem B2204407 : Blo 2203435 2204407 := bstep (se 1 (by rfl) ⟨1653305, by rfl⟩ : syracuseStep 2204407 = 3306611) B3306611
theorem B5296565 : Blo 2203435 5296565 := bbase (se 5 (by rfl) ⟨248276, by rfl⟩ : syracuseStep 5296565 = 496553) (by norm_num)
theorem B3531043 : Blo 2203435 3531043 := bstep (se 1 (by rfl) ⟨2648282, by rfl⟩ : syracuseStep 3531043 = 5296565) B5296565
theorem B4708057 : Blo 2203435 4708057 := bstep (se 2 (by rfl) ⟨1765521, by rfl⟩ : syracuseStep 4708057 = 3531043) B3531043
theorem B6277409 : Blo 2203435 6277409 := bstep (se 2 (by rfl) ⟨2354028, by rfl⟩ : syracuseStep 6277409 = 4708057) B4708057
theorem B4184939 : Blo 2203435 4184939 := bstep (se 1 (by rfl) ⟨3138704, by rfl⟩ : syracuseStep 4184939 = 6277409) B6277409
theorem B2789959 : Blo 2203435 2789959 := bstep (se 1 (by rfl) ⟨2092469, by rfl⟩ : syracuseStep 2789959 = 4184939) B4184939
theorem B3719945 : Blo 2203435 3719945 := bstep (se 2 (by rfl) ⟨1394979, by rfl⟩ : syracuseStep 3719945 = 2789959) B2789959
theorem B2479963 : Blo 2203435 2479963 := bstep (se 1 (by rfl) ⟨1859972, by rfl⟩ : syracuseStep 2479963 = 3719945) B3719945
theorem B3306617 : Blo 2203435 3306617 := bstep (se 2 (by rfl) ⟨1239981, by rfl⟩ : syracuseStep 3306617 = 2479963) B2479963
theorem B2204411 : Blo 2203435 2204411 := bstep (se 1 (by rfl) ⟨1653308, by rfl⟩ : syracuseStep 2204411 = 3306617) B3306617
theorem B15889717 : Blo 2203435 15889717 := bbase (se 5 (by rfl) ⟨744830, by rfl⟩ : syracuseStep 15889717 = 1489661) (by norm_num)
theorem B21186289 : Blo 2203435 21186289 := bstep (se 2 (by rfl) ⟨7944858, by rfl⟩ : syracuseStep 21186289 = 15889717) B15889717
theorem B28248385 : Blo 2203435 28248385 := bstep (se 2 (by rfl) ⟨10593144, by rfl⟩ : syracuseStep 28248385 = 21186289) B21186289
theorem B37664513 : Blo 2203435 37664513 := bstep (se 2 (by rfl) ⟨14124192, by rfl⟩ : syracuseStep 37664513 = 28248385) B28248385
theorem B25109675 : Blo 2203435 25109675 := bstep (se 1 (by rfl) ⟨18832256, by rfl⟩ : syracuseStep 25109675 = 37664513) B37664513
theorem B16739783 : Blo 2203435 16739783 := bstep (se 1 (by rfl) ⟨12554837, by rfl⟩ : syracuseStep 16739783 = 25109675) B25109675
theorem B11159855 : Blo 2203435 11159855 := bstep (se 1 (by rfl) ⟨8369891, by rfl⟩ : syracuseStep 11159855 = 16739783) B16739783
theorem B7439903 : Blo 2203435 7439903 := bstep (se 1 (by rfl) ⟨5579927, by rfl⟩ : syracuseStep 7439903 = 11159855) B11159855
theorem B4959935 : Blo 2203435 4959935 := bstep (se 1 (by rfl) ⟨3719951, by rfl⟩ : syracuseStep 4959935 = 7439903) B7439903
theorem B3306623 : Blo 2203435 3306623 := bstep (se 1 (by rfl) ⟨2479967, by rfl⟩ : syracuseStep 3306623 = 4959935) B4959935
theorem B2204415 : Blo 2203435 2204415 := bstep (se 1 (by rfl) ⟨1653311, by rfl⟩ : syracuseStep 2204415 = 3306623) B3306623
theorem B3306629 : Blo 2203435 3306629 := bbase (se 4 (by rfl) ⟨309996, by rfl⟩ : syracuseStep 3306629 = 619993) (by norm_num)
theorem B2204419 : Blo 2203435 2204419 := bstep (se 1 (by rfl) ⟨1653314, by rfl⟩ : syracuseStep 2204419 = 3306629) B3306629
theorem B3719965 : Blo 2203435 3719965 := bbase (se 3 (by rfl) ⟨697493, by rfl⟩ : syracuseStep 3719965 = 1394987) (by norm_num)
theorem B4959953 : Blo 2203435 4959953 := bstep (se 2 (by rfl) ⟨1859982, by rfl⟩ : syracuseStep 4959953 = 3719965) B3719965
theorem B3306635 : Blo 2203435 3306635 := bstep (se 1 (by rfl) ⟨2479976, by rfl⟩ : syracuseStep 3306635 = 4959953) B4959953
theorem B2204423 : Blo 2203435 2204423 := bstep (se 1 (by rfl) ⟨1653317, by rfl⟩ : syracuseStep 2204423 = 3306635) B3306635
theorem B2479981 : Blo 2203435 2479981 := bbase (se 3 (by rfl) ⟨464996, by rfl⟩ : syracuseStep 2479981 = 929993) (by norm_num)
theorem B3306641 : Blo 2203435 3306641 := bstep (se 2 (by rfl) ⟨1239990, by rfl⟩ : syracuseStep 3306641 = 2479981) B2479981
theorem B2204427 : Blo 2203435 2204427 := bstep (se 1 (by rfl) ⟨1653320, by rfl⟩ : syracuseStep 2204427 = 3306641) B3306641
theorem B7439957 : Blo 2203435 7439957 := bbase (se 8 (by rfl) ⟨43593, by rfl⟩ : syracuseStep 7439957 = 87187) (by norm_num)
theorem B4959971 : Blo 2203435 4959971 := bstep (se 1 (by rfl) ⟨3719978, by rfl⟩ : syracuseStep 4959971 = 7439957) B7439957
theorem B3306647 : Blo 2203435 3306647 := bstep (se 1 (by rfl) ⟨2479985, by rfl⟩ : syracuseStep 3306647 = 4959971) B4959971
theorem B2204431 : Blo 2203435 2204431 := bstep (se 1 (by rfl) ⟨1653323, by rfl⟩ : syracuseStep 2204431 = 3306647) B3306647
theorem B3306653 : Blo 2203435 3306653 := bbase (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) (by norm_num)
theorem B2204435 : Blo 2203435 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B4959989 : Blo 2203435 4959989 := bbase (se 5 (by rfl) ⟨232499, by rfl⟩ : syracuseStep 4959989 = 464999) (by norm_num)
theorem B3306659 : Blo 2203435 3306659 := bstep (se 1 (by rfl) ⟨2479994, by rfl⟩ : syracuseStep 3306659 = 4959989) B4959989
theorem B2204439 : Blo 2203435 2204439 := bstep (se 1 (by rfl) ⟨1653329, by rfl⟩ : syracuseStep 2204439 = 3306659) B3306659
theorem B3351781 : Blo 2203435 3351781 := bbase (se 4 (by rfl) ⟨314229, by rfl⟩ : syracuseStep 3351781 = 628459) (by norm_num)
theorem B4469041 : Blo 2203435 4469041 := bstep (se 2 (by rfl) ⟨1675890, by rfl⟩ : syracuseStep 4469041 = 3351781) B3351781
theorem B5958721 : Blo 2203435 5958721 := bstep (se 2 (by rfl) ⟨2234520, by rfl⟩ : syracuseStep 5958721 = 4469041) B4469041
theorem B7944961 : Blo 2203435 7944961 := bstep (se 2 (by rfl) ⟨2979360, by rfl⟩ : syracuseStep 7944961 = 5958721) B5958721
theorem B10593281 : Blo 2203435 10593281 := bstep (se 2 (by rfl) ⟨3972480, by rfl⟩ : syracuseStep 10593281 = 7944961) B7944961
theorem B28248749 : Blo 2203435 28248749 := bstep (se 3 (by rfl) ⟨5296640, by rfl⟩ : syracuseStep 28248749 = 10593281) B10593281
theorem B18832499 : Blo 2203435 18832499 := bstep (se 1 (by rfl) ⟨14124374, by rfl⟩ : syracuseStep 18832499 = 28248749) B28248749
theorem B12554999 : Blo 2203435 12554999 := bstep (se 1 (by rfl) ⟨9416249, by rfl⟩ : syracuseStep 12554999 = 18832499) B18832499
theorem B8369999 : Blo 2203435 8369999 := bstep (se 1 (by rfl) ⟨6277499, by rfl⟩ : syracuseStep 8369999 = 12554999) B12554999
theorem B5579999 : Blo 2203435 5579999 := bstep (se 1 (by rfl) ⟨4184999, by rfl⟩ : syracuseStep 5579999 = 8369999) B8369999
theorem B3719999 : Blo 2203435 3719999 := bstep (se 1 (by rfl) ⟨2789999, by rfl⟩ : syracuseStep 3719999 = 5579999) B5579999
theorem B2479999 : Blo 2203435 2479999 := bstep (se 1 (by rfl) ⟨1859999, by rfl⟩ : syracuseStep 2479999 = 3719999) B3719999
theorem B3306665 : Blo 2203435 3306665 := bstep (se 2 (by rfl) ⟨1239999, by rfl⟩ : syracuseStep 3306665 = 2479999) B2479999
theorem B2204443 : Blo 2203435 2204443 := bstep (se 1 (by rfl) ⟨1653332, by rfl⟩ : syracuseStep 2204443 = 3306665) B3306665
theorem B4708133 : Blo 2203435 4708133 := bbase (se 4 (by rfl) ⟨441387, by rfl⟩ : syracuseStep 4708133 = 882775) (by norm_num)
theorem B3138755 : Blo 2203435 3138755 := bstep (se 1 (by rfl) ⟨2354066, by rfl⟩ : syracuseStep 3138755 = 4708133) B4708133
theorem B8370013 : Blo 2203435 8370013 := bstep (se 3 (by rfl) ⟨1569377, by rfl⟩ : syracuseStep 8370013 = 3138755) B3138755
theorem B11160017 : Blo 2203435 11160017 := bstep (se 2 (by rfl) ⟨4185006, by rfl⟩ : syracuseStep 11160017 = 8370013) B8370013
theorem B7440011 : Blo 2203435 7440011 := bstep (se 1 (by rfl) ⟨5580008, by rfl⟩ : syracuseStep 7440011 = 11160017) B11160017
theorem B4960007 : Blo 2203435 4960007 := bstep (se 1 (by rfl) ⟨3720005, by rfl⟩ : syracuseStep 4960007 = 7440011) B7440011
theorem B3306671 : Blo 2203435 3306671 := bstep (se 1 (by rfl) ⟨2480003, by rfl⟩ : syracuseStep 3306671 = 4960007) B4960007
theorem B2204447 : Blo 2203435 2204447 := bstep (se 1 (by rfl) ⟨1653335, by rfl⟩ : syracuseStep 2204447 = 3306671) B3306671
theorem B3306677 : Blo 2203435 3306677 := bbase (se 5 (by rfl) ⟨155000, by rfl⟩ : syracuseStep 3306677 = 310001) (by norm_num)
theorem B2204451 : Blo 2203435 2204451 := bstep (se 1 (by rfl) ⟨1653338, by rfl⟩ : syracuseStep 2204451 = 3306677) B3306677
theorem B5580029 : Blo 2203435 5580029 := bbase (se 3 (by rfl) ⟨1046255, by rfl⟩ : syracuseStep 5580029 = 2092511) (by norm_num)
theorem B3720019 : Blo 2203435 3720019 := bstep (se 1 (by rfl) ⟨2790014, by rfl⟩ : syracuseStep 3720019 = 5580029) B5580029
theorem B4960025 : Blo 2203435 4960025 := bstep (se 2 (by rfl) ⟨1860009, by rfl⟩ : syracuseStep 4960025 = 3720019) B3720019
theorem B3306683 : Blo 2203435 3306683 := bstep (se 1 (by rfl) ⟨2480012, by rfl⟩ : syracuseStep 3306683 = 4960025) B4960025
theorem B2204455 : Blo 2203435 2204455 := bstep (se 1 (by rfl) ⟨1653341, by rfl⟩ : syracuseStep 2204455 = 3306683) B3306683
theorem B2480017 : Blo 2203435 2480017 := bbase (se 2 (by rfl) ⟨930006, by rfl⟩ : syracuseStep 2480017 = 1860013) (by norm_num)
theorem B3306689 : Blo 2203435 3306689 := bstep (se 2 (by rfl) ⟨1240008, by rfl⟩ : syracuseStep 3306689 = 2480017) B2480017
theorem B2204459 : Blo 2203435 2204459 := bstep (se 1 (by rfl) ⟨1653344, by rfl⟩ : syracuseStep 2204459 = 3306689) B3306689
theorem B4185037 : Blo 2203435 4185037 := bbase (se 3 (by rfl) ⟨784694, by rfl⟩ : syracuseStep 4185037 = 1569389) (by norm_num)
theorem B5580049 : Blo 2203435 5580049 := bstep (se 2 (by rfl) ⟨2092518, by rfl⟩ : syracuseStep 5580049 = 4185037) B4185037
theorem B7440065 : Blo 2203435 7440065 := bstep (se 2 (by rfl) ⟨2790024, by rfl⟩ : syracuseStep 7440065 = 5580049) B5580049
theorem B4960043 : Blo 2203435 4960043 := bstep (se 1 (by rfl) ⟨3720032, by rfl⟩ : syracuseStep 4960043 = 7440065) B7440065
theorem B3306695 : Blo 2203435 3306695 := bstep (se 1 (by rfl) ⟨2480021, by rfl⟩ : syracuseStep 3306695 = 4960043) B4960043
theorem B2204463 : Blo 2203435 2204463 := bstep (se 1 (by rfl) ⟨1653347, by rfl⟩ : syracuseStep 2204463 = 3306695) B3306695
theorem B3306701 : Blo 2203435 3306701 := bbase (se 3 (by rfl) ⟨620006, by rfl⟩ : syracuseStep 3306701 = 1240013) (by norm_num)
theorem B2204467 : Blo 2203435 2204467 := bstep (se 1 (by rfl) ⟨1653350, by rfl⟩ : syracuseStep 2204467 = 3306701) B3306701
theorem B4960061 : Blo 2203435 4960061 := bbase (se 3 (by rfl) ⟨930011, by rfl⟩ : syracuseStep 4960061 = 1860023) (by norm_num)
theorem B3306707 : Blo 2203435 3306707 := bstep (se 1 (by rfl) ⟨2480030, by rfl⟩ : syracuseStep 3306707 = 4960061) B4960061
theorem B2204471 : Blo 2203435 2204471 := bstep (se 1 (by rfl) ⟨1653353, by rfl⟩ : syracuseStep 2204471 = 3306707) B3306707
theorem B3720053 : Blo 2203435 3720053 := bbase (se 5 (by rfl) ⟨174377, by rfl⟩ : syracuseStep 3720053 = 348755) (by norm_num)
theorem B2480035 : Blo 2203435 2480035 := bstep (se 1 (by rfl) ⟨1860026, by rfl⟩ : syracuseStep 2480035 = 3720053) B3720053
theorem B3306713 : Blo 2203435 3306713 := bstep (se 2 (by rfl) ⟨1240017, by rfl⟩ : syracuseStep 3306713 = 2480035) B2480035
theorem B2204475 : Blo 2203435 2204475 := bstep (se 1 (by rfl) ⟨1653356, by rfl⟩ : syracuseStep 2204475 = 3306713) B3306713
theorem B2234557 : Blo 2203435 2234557 := bbase (se 3 (by rfl) ⟨418979, by rfl⟩ : syracuseStep 2234557 = 837959) (by norm_num)
theorem B11917637 : Blo 2203435 11917637 := bstep (se 4 (by rfl) ⟨1117278, by rfl⟩ : syracuseStep 11917637 = 2234557) B2234557
theorem B7945091 : Blo 2203435 7945091 := bstep (se 1 (by rfl) ⟨5958818, by rfl⟩ : syracuseStep 7945091 = 11917637) B11917637
theorem B5296727 : Blo 2203435 5296727 := bstep (se 1 (by rfl) ⟨3972545, by rfl⟩ : syracuseStep 5296727 = 7945091) B7945091
theorem B3531151 : Blo 2203435 3531151 := bstep (se 1 (by rfl) ⟨2648363, by rfl⟩ : syracuseStep 3531151 = 5296727) B5296727
theorem B4708201 : Blo 2203435 4708201 := bstep (se 2 (by rfl) ⟨1765575, by rfl⟩ : syracuseStep 4708201 = 3531151) B3531151
theorem B6277601 : Blo 2203435 6277601 := bstep (se 2 (by rfl) ⟨2354100, by rfl⟩ : syracuseStep 6277601 = 4708201) B4708201
theorem B16740269 : Blo 2203435 16740269 := bstep (se 3 (by rfl) ⟨3138800, by rfl⟩ : syracuseStep 16740269 = 6277601) B6277601
theorem B11160179 : Blo 2203435 11160179 := bstep (se 1 (by rfl) ⟨8370134, by rfl⟩ : syracuseStep 11160179 = 16740269) B16740269
theorem B7440119 : Blo 2203435 7440119 := bstep (se 1 (by rfl) ⟨5580089, by rfl⟩ : syracuseStep 7440119 = 11160179) B11160179
theorem B4960079 : Blo 2203435 4960079 := bstep (se 1 (by rfl) ⟨3720059, by rfl⟩ : syracuseStep 4960079 = 7440119) B7440119
theorem B3306719 : Blo 2203435 3306719 := bstep (se 1 (by rfl) ⟨2480039, by rfl⟩ : syracuseStep 3306719 = 4960079) B4960079
theorem B2204479 : Blo 2203435 2204479 := bstep (se 1 (by rfl) ⟨1653359, by rfl⟩ : syracuseStep 2204479 = 3306719) B3306719
theorem B3306725 : Blo 2203435 3306725 := bbase (se 4 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 3306725 = 620011) (by norm_num)
theorem B2204483 : Blo 2203435 2204483 := bstep (se 1 (by rfl) ⟨1653362, by rfl⟩ : syracuseStep 2204483 = 3306725) B3306725
theorem B5027773 : Blo 2203435 5027773 := bbase (se 3 (by rfl) ⟨942707, by rfl⟩ : syracuseStep 5027773 = 1885415) (by norm_num)
theorem B6703697 : Blo 2203435 6703697 := bstep (se 2 (by rfl) ⟨2513886, by rfl⟩ : syracuseStep 6703697 = 5027773) B5027773
theorem B4469131 : Blo 2203435 4469131 := bstep (se 1 (by rfl) ⟨3351848, by rfl⟩ : syracuseStep 4469131 = 6703697) B6703697
theorem B5958841 : Blo 2203435 5958841 := bstep (se 2 (by rfl) ⟨2234565, by rfl⟩ : syracuseStep 5958841 = 4469131) B4469131
theorem B7945121 : Blo 2203435 7945121 := bstep (se 2 (by rfl) ⟨2979420, by rfl⟩ : syracuseStep 7945121 = 5958841) B5958841
theorem B5296747 : Blo 2203435 5296747 := bstep (se 1 (by rfl) ⟨3972560, by rfl⟩ : syracuseStep 5296747 = 7945121) B7945121
theorem B7062329 : Blo 2203435 7062329 := bstep (se 2 (by rfl) ⟨2648373, by rfl⟩ : syracuseStep 7062329 = 5296747) B5296747
theorem B4708219 : Blo 2203435 4708219 := bstep (se 1 (by rfl) ⟨3531164, by rfl⟩ : syracuseStep 4708219 = 7062329) B7062329
theorem B6277625 : Blo 2203435 6277625 := bstep (se 2 (by rfl) ⟨2354109, by rfl⟩ : syracuseStep 6277625 = 4708219) B4708219
theorem B4185083 : Blo 2203435 4185083 := bstep (se 1 (by rfl) ⟨3138812, by rfl⟩ : syracuseStep 4185083 = 6277625) B6277625
theorem B2790055 : Blo 2203435 2790055 := bstep (se 1 (by rfl) ⟨2092541, by rfl⟩ : syracuseStep 2790055 = 4185083) B4185083
theorem B3720073 : Blo 2203435 3720073 := bstep (se 2 (by rfl) ⟨1395027, by rfl⟩ : syracuseStep 3720073 = 2790055) B2790055
theorem B4960097 : Blo 2203435 4960097 := bstep (se 2 (by rfl) ⟨1860036, by rfl⟩ : syracuseStep 4960097 = 3720073) B3720073
theorem B3306731 : Blo 2203435 3306731 := bstep (se 1 (by rfl) ⟨2480048, by rfl⟩ : syracuseStep 3306731 = 4960097) B4960097
theorem B2204487 : Blo 2203435 2204487 := bstep (se 1 (by rfl) ⟨1653365, by rfl⟩ : syracuseStep 2204487 = 3306731) B3306731
theorem B2480053 : Blo 2203435 2480053 := bbase (se 5 (by rfl) ⟨116252, by rfl⟩ : syracuseStep 2480053 = 232505) (by norm_num)
theorem B3306737 : Blo 2203435 3306737 := bstep (se 2 (by rfl) ⟨1240026, by rfl⟩ : syracuseStep 3306737 = 2480053) B2480053
theorem B2204491 : Blo 2203435 2204491 := bstep (se 1 (by rfl) ⟨1653368, by rfl⟩ : syracuseStep 2204491 = 3306737) B3306737
theorem B2790065 : Blo 2203435 2790065 := bbase (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) (by norm_num)
theorem B7440173 : Blo 2203435 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B4960115 : Blo 2203435 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B3306743 : Blo 2203435 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B2204495 : Blo 2203435 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B3306749 : Blo 2203435 3306749 := bbase (se 3 (by rfl) ⟨620015, by rfl⟩ : syracuseStep 3306749 = 1240031) (by norm_num)
theorem B2204499 : Blo 2203435 2204499 := bstep (se 1 (by rfl) ⟨1653374, by rfl⟩ : syracuseStep 2204499 = 3306749) B3306749
theorem B4960133 : Blo 2203435 4960133 := bbase (se 4 (by rfl) ⟨465012, by rfl⟩ : syracuseStep 4960133 = 930025) (by norm_num)
theorem B3306755 : Blo 2203435 3306755 := bstep (se 1 (by rfl) ⟨2480066, by rfl⟩ : syracuseStep 3306755 = 4960133) B4960133
theorem B2204503 : Blo 2203435 2204503 := bstep (se 1 (by rfl) ⟨1653377, by rfl⟩ : syracuseStep 2204503 = 3306755) B3306755
theorem B3531197 : Blo 2203435 3531197 := bbase (se 3 (by rfl) ⟨662099, by rfl⟩ : syracuseStep 3531197 = 1324199) (by norm_num)
theorem B2354131 : Blo 2203435 2354131 := bstep (se 1 (by rfl) ⟨1765598, by rfl⟩ : syracuseStep 2354131 = 3531197) B3531197
theorem B3138841 : Blo 2203435 3138841 := bstep (se 2 (by rfl) ⟨1177065, by rfl⟩ : syracuseStep 3138841 = 2354131) B2354131
theorem B4185121 : Blo 2203435 4185121 := bstep (se 2 (by rfl) ⟨1569420, by rfl⟩ : syracuseStep 4185121 = 3138841) B3138841
theorem B5580161 : Blo 2203435 5580161 := bstep (se 2 (by rfl) ⟨2092560, by rfl⟩ : syracuseStep 5580161 = 4185121) B4185121
theorem B3720107 : Blo 2203435 3720107 := bstep (se 1 (by rfl) ⟨2790080, by rfl⟩ : syracuseStep 3720107 = 5580161) B5580161
theorem B2480071 : Blo 2203435 2480071 := bstep (se 1 (by rfl) ⟨1860053, by rfl⟩ : syracuseStep 2480071 = 3720107) B3720107
theorem B3306761 : Blo 2203435 3306761 := bstep (se 2 (by rfl) ⟨1240035, by rfl⟩ : syracuseStep 3306761 = 2480071) B2480071
theorem B2204507 : Blo 2203435 2204507 := bstep (se 1 (by rfl) ⟨1653380, by rfl⟩ : syracuseStep 2204507 = 3306761) B3306761
theorem B11160341 : Blo 2203435 11160341 := bbase (se 6 (by rfl) ⟨261570, by rfl⟩ : syracuseStep 11160341 = 523141) (by norm_num)
theorem B7440227 : Blo 2203435 7440227 := bstep (se 1 (by rfl) ⟨5580170, by rfl⟩ : syracuseStep 7440227 = 11160341) B11160341
theorem B4960151 : Blo 2203435 4960151 := bstep (se 1 (by rfl) ⟨3720113, by rfl⟩ : syracuseStep 4960151 = 7440227) B7440227
theorem B3306767 : Blo 2203435 3306767 := bstep (se 1 (by rfl) ⟨2480075, by rfl⟩ : syracuseStep 3306767 = 4960151) B4960151
theorem B2204511 : Blo 2203435 2204511 := bstep (se 1 (by rfl) ⟨1653383, by rfl⟩ : syracuseStep 2204511 = 3306767) B3306767
theorem B3306773 : Blo 2203435 3306773 := bbase (se 6 (by rfl) ⟨77502, by rfl⟩ : syracuseStep 3306773 = 155005) (by norm_num)
theorem B2204515 : Blo 2203435 2204515 := bstep (se 1 (by rfl) ⟨1653386, by rfl⟩ : syracuseStep 2204515 = 3306773) B3306773
theorem B6363365 : Blo 2203435 6363365 := bbase (se 4 (by rfl) ⟨596565, by rfl⟩ : syracuseStep 6363365 = 1193131) (by norm_num)
theorem B67875893 : Blo 2203435 67875893 := bstep (se 5 (by rfl) ⟨3181682, by rfl⟩ : syracuseStep 67875893 = 6363365) B6363365
theorem B45250595 : Blo 2203435 45250595 := bstep (se 1 (by rfl) ⟨33937946, by rfl⟩ : syracuseStep 45250595 = 67875893) B67875893
theorem B30167063 : Blo 2203435 30167063 := bstep (se 1 (by rfl) ⟨22625297, by rfl⟩ : syracuseStep 30167063 = 45250595) B45250595
theorem B20111375 : Blo 2203435 20111375 := bstep (se 1 (by rfl) ⟨15083531, by rfl⟩ : syracuseStep 20111375 = 30167063) B30167063
theorem B53630333 : Blo 2203435 53630333 := bstep (se 3 (by rfl) ⟨10055687, by rfl⟩ : syracuseStep 53630333 = 20111375) B20111375
theorem B35753555 : Blo 2203435 35753555 := bstep (se 1 (by rfl) ⟨26815166, by rfl⟩ : syracuseStep 35753555 = 53630333) B53630333
theorem B23835703 : Blo 2203435 23835703 := bstep (se 1 (by rfl) ⟨17876777, by rfl⟩ : syracuseStep 23835703 = 35753555) B35753555
theorem B31780937 : Blo 2203435 31780937 := bstep (se 2 (by rfl) ⟨11917851, by rfl⟩ : syracuseStep 31780937 = 23835703) B23835703
theorem B21187291 : Blo 2203435 21187291 := bstep (se 1 (by rfl) ⟨15890468, by rfl⟩ : syracuseStep 21187291 = 31780937) B31780937
theorem B28249721 : Blo 2203435 28249721 := bstep (se 2 (by rfl) ⟨10593645, by rfl⟩ : syracuseStep 28249721 = 21187291) B21187291
theorem B18833147 : Blo 2203435 18833147 := bstep (se 1 (by rfl) ⟨14124860, by rfl⟩ : syracuseStep 18833147 = 28249721) B28249721
theorem B12555431 : Blo 2203435 12555431 := bstep (se 1 (by rfl) ⟨9416573, by rfl⟩ : syracuseStep 12555431 = 18833147) B18833147
theorem B8370287 : Blo 2203435 8370287 := bstep (se 1 (by rfl) ⟨6277715, by rfl⟩ : syracuseStep 8370287 = 12555431) B12555431
theorem B5580191 : Blo 2203435 5580191 := bstep (se 1 (by rfl) ⟨4185143, by rfl⟩ : syracuseStep 5580191 = 8370287) B8370287
theorem B3720127 : Blo 2203435 3720127 := bstep (se 1 (by rfl) ⟨2790095, by rfl⟩ : syracuseStep 3720127 = 5580191) B5580191
theorem B4960169 : Blo 2203435 4960169 := bstep (se 2 (by rfl) ⟨1860063, by rfl⟩ : syracuseStep 4960169 = 3720127) B3720127
theorem B3306779 : Blo 2203435 3306779 := bstep (se 1 (by rfl) ⟨2480084, by rfl⟩ : syracuseStep 3306779 = 4960169) B4960169
theorem B2204519 : Blo 2203435 2204519 := bstep (se 1 (by rfl) ⟨1653389, by rfl⟩ : syracuseStep 2204519 = 3306779) B3306779
theorem B2480089 : Blo 2203435 2480089 := bbase (se 2 (by rfl) ⟨930033, by rfl⟩ : syracuseStep 2480089 = 1860067) (by norm_num)
theorem B3306785 : Blo 2203435 3306785 := bstep (se 2 (by rfl) ⟨1240044, by rfl⟩ : syracuseStep 3306785 = 2480089) B2480089
theorem B2204523 : Blo 2203435 2204523 := bstep (se 1 (by rfl) ⟨1653392, by rfl⟩ : syracuseStep 2204523 = 3306785) B3306785
theorem B3138869 : Blo 2203435 3138869 := bbase (se 5 (by rfl) ⟨147134, by rfl⟩ : syracuseStep 3138869 = 294269) (by norm_num)
theorem B8370317 : Blo 2203435 8370317 := bstep (se 3 (by rfl) ⟨1569434, by rfl⟩ : syracuseStep 8370317 = 3138869) B3138869
theorem B5580211 : Blo 2203435 5580211 := bstep (se 1 (by rfl) ⟨4185158, by rfl⟩ : syracuseStep 5580211 = 8370317) B8370317
theorem B7440281 : Blo 2203435 7440281 := bstep (se 2 (by rfl) ⟨2790105, by rfl⟩ : syracuseStep 7440281 = 5580211) B5580211
theorem B4960187 : Blo 2203435 4960187 := bstep (se 1 (by rfl) ⟨3720140, by rfl⟩ : syracuseStep 4960187 = 7440281) B7440281
theorem B3306791 : Blo 2203435 3306791 := bstep (se 1 (by rfl) ⟨2480093, by rfl⟩ : syracuseStep 3306791 = 4960187) B4960187
theorem B2204527 : Blo 2203435 2204527 := bstep (se 1 (by rfl) ⟨1653395, by rfl⟩ : syracuseStep 2204527 = 3306791) B3306791
theorem B3306797 : Blo 2203435 3306797 := bbase (se 3 (by rfl) ⟨620024, by rfl⟩ : syracuseStep 3306797 = 1240049) (by norm_num)
theorem B2204531 : Blo 2203435 2204531 := bstep (se 1 (by rfl) ⟨1653398, by rfl⟩ : syracuseStep 2204531 = 3306797) B3306797
theorem B4960205 : Blo 2203435 4960205 := bbase (se 3 (by rfl) ⟨930038, by rfl⟩ : syracuseStep 4960205 = 1860077) (by norm_num)
theorem B3306803 : Blo 2203435 3306803 := bstep (se 1 (by rfl) ⟨2480102, by rfl⟩ : syracuseStep 3306803 = 4960205) B4960205
theorem B2204535 : Blo 2203435 2204535 := bstep (se 1 (by rfl) ⟨1653401, by rfl⟩ : syracuseStep 2204535 = 3306803) B3306803
theorem B2790121 : Blo 2203435 2790121 := bbase (se 2 (by rfl) ⟨1046295, by rfl⟩ : syracuseStep 2790121 = 2092591) (by norm_num)
theorem B3720161 : Blo 2203435 3720161 := bstep (se 2 (by rfl) ⟨1395060, by rfl⟩ : syracuseStep 3720161 = 2790121) B2790121
theorem B2480107 : Blo 2203435 2480107 := bstep (se 1 (by rfl) ⟨1860080, by rfl⟩ : syracuseStep 2480107 = 3720161) B3720161
theorem B3306809 : Blo 2203435 3306809 := bstep (se 2 (by rfl) ⟨1240053, by rfl⟩ : syracuseStep 3306809 = 2480107) B2480107
theorem B2204539 : Blo 2203435 2204539 := bstep (se 1 (by rfl) ⟨1653404, by rfl⟩ : syracuseStep 2204539 = 3306809) B3306809
theorem B14125013 : Blo 2203435 14125013 := bbase (se 7 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 14125013 = 331055) (by norm_num)
theorem B9416675 : Blo 2203435 9416675 := bstep (se 1 (by rfl) ⟨7062506, by rfl⟩ : syracuseStep 9416675 = 14125013) B14125013
theorem B25111133 : Blo 2203435 25111133 := bstep (se 3 (by rfl) ⟨4708337, by rfl⟩ : syracuseStep 25111133 = 9416675) B9416675
theorem B16740755 : Blo 2203435 16740755 := bstep (se 1 (by rfl) ⟨12555566, by rfl⟩ : syracuseStep 16740755 = 25111133) B25111133
theorem B11160503 : Blo 2203435 11160503 := bstep (se 1 (by rfl) ⟨8370377, by rfl⟩ : syracuseStep 11160503 = 16740755) B16740755
theorem B7440335 : Blo 2203435 7440335 := bstep (se 1 (by rfl) ⟨5580251, by rfl⟩ : syracuseStep 7440335 = 11160503) B11160503
theorem B4960223 : Blo 2203435 4960223 := bstep (se 1 (by rfl) ⟨3720167, by rfl⟩ : syracuseStep 4960223 = 7440335) B7440335
theorem B3306815 : Blo 2203435 3306815 := bstep (se 1 (by rfl) ⟨2480111, by rfl⟩ : syracuseStep 3306815 = 4960223) B4960223
theorem B2204543 : Blo 2203435 2204543 := bstep (se 1 (by rfl) ⟨1653407, by rfl⟩ : syracuseStep 2204543 = 3306815) B3306815
theorem B3306821 : Blo 2203435 3306821 := bbase (se 4 (by rfl) ⟨310014, by rfl⟩ : syracuseStep 3306821 = 620029) (by norm_num)
theorem B2204547 : Blo 2203435 2204547 := bstep (se 1 (by rfl) ⟨1653410, by rfl⟩ : syracuseStep 2204547 = 3306821) B3306821
theorem B3720181 : Blo 2203435 3720181 := bbase (se 5 (by rfl) ⟨174383, by rfl⟩ : syracuseStep 3720181 = 348767) (by norm_num)
theorem B4960241 : Blo 2203435 4960241 := bstep (se 2 (by rfl) ⟨1860090, by rfl⟩ : syracuseStep 4960241 = 3720181) B3720181
theorem B3306827 : Blo 2203435 3306827 := bstep (se 1 (by rfl) ⟨2480120, by rfl⟩ : syracuseStep 3306827 = 4960241) B4960241
theorem B2204551 : Blo 2203435 2204551 := bstep (se 1 (by rfl) ⟨1653413, by rfl⟩ : syracuseStep 2204551 = 3306827) B3306827
theorem B2480125 : Blo 2203435 2480125 := bbase (se 3 (by rfl) ⟨465023, by rfl⟩ : syracuseStep 2480125 = 930047) (by norm_num)
theorem B3306833 : Blo 2203435 3306833 := bstep (se 2 (by rfl) ⟨1240062, by rfl⟩ : syracuseStep 3306833 = 2480125) B2480125
theorem B2204555 : Blo 2203435 2204555 := bstep (se 1 (by rfl) ⟨1653416, by rfl⟩ : syracuseStep 2204555 = 3306833) B3306833
theorem B7440389 : Blo 2203435 7440389 := bbase (se 4 (by rfl) ⟨697536, by rfl⟩ : syracuseStep 7440389 = 1395073) (by norm_num)
theorem B4960259 : Blo 2203435 4960259 := bstep (se 1 (by rfl) ⟨3720194, by rfl⟩ : syracuseStep 4960259 = 7440389) B7440389
theorem B3306839 : Blo 2203435 3306839 := bstep (se 1 (by rfl) ⟨2480129, by rfl⟩ : syracuseStep 3306839 = 4960259) B4960259
theorem B2204559 : Blo 2203435 2204559 := bstep (se 1 (by rfl) ⟨1653419, by rfl⟩ : syracuseStep 2204559 = 3306839) B3306839
theorem B3306845 : Blo 2203435 3306845 := bbase (se 3 (by rfl) ⟨620033, by rfl⟩ : syracuseStep 3306845 = 1240067) (by norm_num)
theorem B2204563 : Blo 2203435 2204563 := bstep (se 1 (by rfl) ⟨1653422, by rfl⟩ : syracuseStep 2204563 = 3306845) B3306845
theorem B4960277 : Blo 2203435 4960277 := bbase (se 6 (by rfl) ⟨116256, by rfl⟩ : syracuseStep 4960277 = 232513) (by norm_num)
theorem B3306851 : Blo 2203435 3306851 := bstep (se 1 (by rfl) ⟨2480138, by rfl⟩ : syracuseStep 3306851 = 4960277) B4960277
theorem B2204567 : Blo 2203435 2204567 := bstep (se 1 (by rfl) ⟨1653425, by rfl⟩ : syracuseStep 2204567 = 3306851) B3306851
theorem B8370485 : Blo 2203435 8370485 := bbase (se 5 (by rfl) ⟨392366, by rfl⟩ : syracuseStep 8370485 = 784733) (by norm_num)
theorem B5580323 : Blo 2203435 5580323 := bstep (se 1 (by rfl) ⟨4185242, by rfl⟩ : syracuseStep 5580323 = 8370485) B8370485
theorem B3720215 : Blo 2203435 3720215 := bstep (se 1 (by rfl) ⟨2790161, by rfl⟩ : syracuseStep 3720215 = 5580323) B5580323
theorem B2480143 : Blo 2203435 2480143 := bstep (se 1 (by rfl) ⟨1860107, by rfl⟩ : syracuseStep 2480143 = 3720215) B3720215
theorem B3306857 : Blo 2203435 3306857 := bstep (se 2 (by rfl) ⟨1240071, by rfl⟩ : syracuseStep 3306857 = 2480143) B2480143
theorem B2204571 : Blo 2203435 2204571 := bstep (se 1 (by rfl) ⟨1653428, by rfl⟩ : syracuseStep 2204571 = 3306857) B3306857
theorem B3181765 : Blo 2203435 3181765 := bbase (se 4 (by rfl) ⟨298290, by rfl⟩ : syracuseStep 3181765 = 596581) (by norm_num)
theorem B4242353 : Blo 2203435 4242353 := bstep (se 2 (by rfl) ⟨1590882, by rfl⟩ : syracuseStep 4242353 = 3181765) B3181765
theorem B11312941 : Blo 2203435 11312941 := bstep (se 3 (by rfl) ⟨2121176, by rfl⟩ : syracuseStep 11312941 = 4242353) B4242353
theorem B15083921 : Blo 2203435 15083921 := bstep (se 2 (by rfl) ⟨5656470, by rfl⟩ : syracuseStep 15083921 = 11312941) B11312941
theorem B10055947 : Blo 2203435 10055947 := bstep (se 1 (by rfl) ⟨7541960, by rfl⟩ : syracuseStep 10055947 = 15083921) B15083921
theorem B13407929 : Blo 2203435 13407929 := bstep (se 2 (by rfl) ⟨5027973, by rfl⟩ : syracuseStep 13407929 = 10055947) B10055947
theorem B8938619 : Blo 2203435 8938619 := bstep (se 1 (by rfl) ⟨6703964, by rfl⟩ : syracuseStep 8938619 = 13407929) B13407929
theorem B5959079 : Blo 2203435 5959079 := bstep (se 1 (by rfl) ⟨4469309, by rfl⟩ : syracuseStep 5959079 = 8938619) B8938619
theorem B3972719 : Blo 2203435 3972719 := bstep (se 1 (by rfl) ⟨2979539, by rfl⟩ : syracuseStep 3972719 = 5959079) B5959079
theorem B2648479 : Blo 2203435 2648479 := bstep (se 1 (by rfl) ⟨1986359, by rfl⟩ : syracuseStep 2648479 = 3972719) B3972719
theorem B3531305 : Blo 2203435 3531305 := bstep (se 2 (by rfl) ⟨1324239, by rfl⟩ : syracuseStep 3531305 = 2648479) B2648479
theorem B2354203 : Blo 2203435 2354203 := bstep (se 1 (by rfl) ⟨1765652, by rfl⟩ : syracuseStep 2354203 = 3531305) B3531305
theorem B12555749 : Blo 2203435 12555749 := bstep (se 4 (by rfl) ⟨1177101, by rfl⟩ : syracuseStep 12555749 = 2354203) B2354203
theorem B8370499 : Blo 2203435 8370499 := bstep (se 1 (by rfl) ⟨6277874, by rfl⟩ : syracuseStep 8370499 = 12555749) B12555749
theorem B11160665 : Blo 2203435 11160665 := bstep (se 2 (by rfl) ⟨4185249, by rfl⟩ : syracuseStep 11160665 = 8370499) B8370499
theorem B7440443 : Blo 2203435 7440443 := bstep (se 1 (by rfl) ⟨5580332, by rfl⟩ : syracuseStep 7440443 = 11160665) B11160665
theorem B4960295 : Blo 2203435 4960295 := bstep (se 1 (by rfl) ⟨3720221, by rfl⟩ : syracuseStep 4960295 = 7440443) B7440443
theorem B3306863 : Blo 2203435 3306863 := bstep (se 1 (by rfl) ⟨2480147, by rfl⟩ : syracuseStep 3306863 = 4960295) B4960295
theorem B2204575 : Blo 2203435 2204575 := bstep (se 1 (by rfl) ⟨1653431, by rfl⟩ : syracuseStep 2204575 = 3306863) B3306863
theorem B3306869 : Blo 2203435 3306869 := bbase (se 5 (by rfl) ⟨155009, by rfl⟩ : syracuseStep 3306869 = 310019) (by norm_num)
theorem B2204579 : Blo 2203435 2204579 := bstep (se 1 (by rfl) ⟨1653434, by rfl⟩ : syracuseStep 2204579 = 3306869) B3306869
theorem B3138949 : Blo 2203435 3138949 := bbase (se 4 (by rfl) ⟨294276, by rfl⟩ : syracuseStep 3138949 = 588553) (by norm_num)
theorem B4185265 : Blo 2203435 4185265 := bstep (se 2 (by rfl) ⟨1569474, by rfl⟩ : syracuseStep 4185265 = 3138949) B3138949
theorem B5580353 : Blo 2203435 5580353 := bstep (se 2 (by rfl) ⟨2092632, by rfl⟩ : syracuseStep 5580353 = 4185265) B4185265
theorem B3720235 : Blo 2203435 3720235 := bstep (se 1 (by rfl) ⟨2790176, by rfl⟩ : syracuseStep 3720235 = 5580353) B5580353
theorem B4960313 : Blo 2203435 4960313 := bstep (se 2 (by rfl) ⟨1860117, by rfl⟩ : syracuseStep 4960313 = 3720235) B3720235
theorem B3306875 : Blo 2203435 3306875 := bstep (se 1 (by rfl) ⟨2480156, by rfl⟩ : syracuseStep 3306875 = 4960313) B4960313
theorem B2204583 : Blo 2203435 2204583 := bstep (se 1 (by rfl) ⟨1653437, by rfl⟩ : syracuseStep 2204583 = 3306875) B3306875
theorem B2480161 : Blo 2203435 2480161 := bbase (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) (by norm_num)
theorem B3306881 : Blo 2203435 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B2204587 : Blo 2203435 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B5580373 : Blo 2203435 5580373 := bbase (se 8 (by rfl) ⟨32697, by rfl⟩ : syracuseStep 5580373 = 65395) (by norm_num)
theorem B7440497 : Blo 2203435 7440497 := bstep (se 2 (by rfl) ⟨2790186, by rfl⟩ : syracuseStep 7440497 = 5580373) B5580373
theorem B4960331 : Blo 2203435 4960331 := bstep (se 1 (by rfl) ⟨3720248, by rfl⟩ : syracuseStep 4960331 = 7440497) B7440497
theorem B3306887 : Blo 2203435 3306887 := bstep (se 1 (by rfl) ⟨2480165, by rfl⟩ : syracuseStep 3306887 = 4960331) B4960331
theorem B2204591 : Blo 2203435 2204591 := bstep (se 1 (by rfl) ⟨1653443, by rfl⟩ : syracuseStep 2204591 = 3306887) B3306887
theorem B3306893 : Blo 2203435 3306893 := bbase (se 3 (by rfl) ⟨620042, by rfl⟩ : syracuseStep 3306893 = 1240085) (by norm_num)
theorem B2204595 : Blo 2203435 2204595 := bstep (se 1 (by rfl) ⟨1653446, by rfl⟩ : syracuseStep 2204595 = 3306893) B3306893
theorem B4960349 : Blo 2203435 4960349 := bbase (se 3 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 4960349 = 1860131) (by norm_num)
theorem B3306899 : Blo 2203435 3306899 := bstep (se 1 (by rfl) ⟨2480174, by rfl⟩ : syracuseStep 3306899 = 4960349) B4960349
theorem B2204599 : Blo 2203435 2204599 := bstep (se 1 (by rfl) ⟨1653449, by rfl⟩ : syracuseStep 2204599 = 3306899) B3306899
theorem B3720269 : Blo 2203435 3720269 := bbase (se 3 (by rfl) ⟨697550, by rfl⟩ : syracuseStep 3720269 = 1395101) (by norm_num)
theorem B2480179 : Blo 2203435 2480179 := bstep (se 1 (by rfl) ⟨1860134, by rfl⟩ : syracuseStep 2480179 = 3720269) B3720269
theorem B3306905 : Blo 2203435 3306905 := bstep (se 2 (by rfl) ⟨1240089, by rfl⟩ : syracuseStep 3306905 = 2480179) B2480179
theorem B2204603 : Blo 2203435 2204603 := bstep (se 1 (by rfl) ⟨1653452, by rfl⟩ : syracuseStep 2204603 = 3306905) B3306905
theorem B53632469 : Blo 2203435 53632469 := bbase (se 7 (by rfl) ⟨628505, by rfl⟩ : syracuseStep 53632469 = 1257011) (by norm_num)
theorem B35754979 : Blo 2203435 35754979 := bstep (se 1 (by rfl) ⟨26816234, by rfl⟩ : syracuseStep 35754979 = 53632469) B53632469
theorem B47673305 : Blo 2203435 47673305 := bstep (se 2 (by rfl) ⟨17877489, by rfl⟩ : syracuseStep 47673305 = 35754979) B35754979
theorem B31782203 : Blo 2203435 31782203 := bstep (se 1 (by rfl) ⟨23836652, by rfl⟩ : syracuseStep 31782203 = 47673305) B47673305
theorem B21188135 : Blo 2203435 21188135 := bstep (se 1 (by rfl) ⟨15891101, by rfl⟩ : syracuseStep 21188135 = 31782203) B31782203
theorem B14125423 : Blo 2203435 14125423 := bstep (se 1 (by rfl) ⟨10594067, by rfl⟩ : syracuseStep 14125423 = 21188135) B21188135
theorem B18833897 : Blo 2203435 18833897 := bstep (se 2 (by rfl) ⟨7062711, by rfl⟩ : syracuseStep 18833897 = 14125423) B14125423
theorem B12555931 : Blo 2203435 12555931 := bstep (se 1 (by rfl) ⟨9416948, by rfl⟩ : syracuseStep 12555931 = 18833897) B18833897
theorem B16741241 : Blo 2203435 16741241 := bstep (se 2 (by rfl) ⟨6277965, by rfl⟩ : syracuseStep 16741241 = 12555931) B12555931
theorem B11160827 : Blo 2203435 11160827 := bstep (se 1 (by rfl) ⟨8370620, by rfl⟩ : syracuseStep 11160827 = 16741241) B16741241
theorem B7440551 : Blo 2203435 7440551 := bstep (se 1 (by rfl) ⟨5580413, by rfl⟩ : syracuseStep 7440551 = 11160827) B11160827
theorem B4960367 : Blo 2203435 4960367 := bstep (se 1 (by rfl) ⟨3720275, by rfl⟩ : syracuseStep 4960367 = 7440551) B7440551
theorem B3306911 : Blo 2203435 3306911 := bstep (se 1 (by rfl) ⟨2480183, by rfl⟩ : syracuseStep 3306911 = 4960367) B4960367
theorem B2204607 : Blo 2203435 2204607 := bstep (se 1 (by rfl) ⟨1653455, by rfl⟩ : syracuseStep 2204607 = 3306911) B3306911
theorem B3306917 : Blo 2203435 3306917 := bbase (se 4 (by rfl) ⟨310023, by rfl⟩ : syracuseStep 3306917 = 620047) (by norm_num)
theorem B2204611 : Blo 2203435 2204611 := bstep (se 1 (by rfl) ⟨1653458, by rfl⟩ : syracuseStep 2204611 = 3306917) B3306917
theorem B2790217 : Blo 2203435 2790217 := bbase (se 2 (by rfl) ⟨1046331, by rfl⟩ : syracuseStep 2790217 = 2092663) (by norm_num)
theorem B3720289 : Blo 2203435 3720289 := bstep (se 2 (by rfl) ⟨1395108, by rfl⟩ : syracuseStep 3720289 = 2790217) B2790217
theorem B4960385 : Blo 2203435 4960385 := bstep (se 2 (by rfl) ⟨1860144, by rfl⟩ : syracuseStep 4960385 = 3720289) B3720289
theorem B3306923 : Blo 2203435 3306923 := bstep (se 1 (by rfl) ⟨2480192, by rfl⟩ : syracuseStep 3306923 = 4960385) B4960385
theorem B2204615 : Blo 2203435 2204615 := bstep (se 1 (by rfl) ⟨1653461, by rfl⟩ : syracuseStep 2204615 = 3306923) B3306923
theorem B2480197 : Blo 2203435 2480197 := bbase (se 4 (by rfl) ⟨232518, by rfl⟩ : syracuseStep 2480197 = 465037) (by norm_num)
theorem B3306929 : Blo 2203435 3306929 := bstep (se 2 (by rfl) ⟨1240098, by rfl⟩ : syracuseStep 3306929 = 2480197) B2480197
theorem B2204619 : Blo 2203435 2204619 := bstep (se 1 (by rfl) ⟨1653464, by rfl⟩ : syracuseStep 2204619 = 3306929) B3306929
theorem B4185341 : Blo 2203435 4185341 := bbase (se 3 (by rfl) ⟨784751, by rfl⟩ : syracuseStep 4185341 = 1569503) (by norm_num)
theorem B2790227 : Blo 2203435 2790227 := bstep (se 1 (by rfl) ⟨2092670, by rfl⟩ : syracuseStep 2790227 = 4185341) B4185341
theorem B7440605 : Blo 2203435 7440605 := bstep (se 3 (by rfl) ⟨1395113, by rfl⟩ : syracuseStep 7440605 = 2790227) B2790227
theorem B4960403 : Blo 2203435 4960403 := bstep (se 1 (by rfl) ⟨3720302, by rfl⟩ : syracuseStep 4960403 = 7440605) B7440605
theorem B3306935 : Blo 2203435 3306935 := bstep (se 1 (by rfl) ⟨2480201, by rfl⟩ : syracuseStep 3306935 = 4960403) B4960403
theorem B2204623 : Blo 2203435 2204623 := bstep (se 1 (by rfl) ⟨1653467, by rfl⟩ : syracuseStep 2204623 = 3306935) B3306935
theorem B3306941 : Blo 2203435 3306941 := bbase (se 3 (by rfl) ⟨620051, by rfl⟩ : syracuseStep 3306941 = 1240103) (by norm_num)
theorem B2204627 : Blo 2203435 2204627 := bstep (se 1 (by rfl) ⟨1653470, by rfl⟩ : syracuseStep 2204627 = 3306941) B3306941
theorem B4960421 : Blo 2203435 4960421 := bbase (se 4 (by rfl) ⟨465039, by rfl⟩ : syracuseStep 4960421 = 930079) (by norm_num)
theorem B3306947 : Blo 2203435 3306947 := bstep (se 1 (by rfl) ⟨2480210, by rfl⟩ : syracuseStep 3306947 = 4960421) B4960421
theorem B2204631 : Blo 2203435 2204631 := bstep (se 1 (by rfl) ⟨1653473, by rfl⟩ : syracuseStep 2204631 = 3306947) B3306947
theorem B5580485 : Blo 2203435 5580485 := bbase (se 4 (by rfl) ⟨523170, by rfl⟩ : syracuseStep 5580485 = 1046341) (by norm_num)
theorem B3720323 : Blo 2203435 3720323 := bstep (se 1 (by rfl) ⟨2790242, by rfl⟩ : syracuseStep 3720323 = 5580485) B5580485
theorem B2480215 : Blo 2203435 2480215 := bstep (se 1 (by rfl) ⟨1860161, by rfl⟩ : syracuseStep 2480215 = 3720323) B3720323
theorem B3306953 : Blo 2203435 3306953 := bstep (se 2 (by rfl) ⟨1240107, by rfl⟩ : syracuseStep 3306953 = 2480215) B2480215
theorem B2204635 : Blo 2203435 2204635 := bstep (se 1 (by rfl) ⟨1653476, by rfl⟩ : syracuseStep 2204635 = 3306953) B3306953
theorem B2828317 : Blo 2203435 2828317 := bbase (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) (by norm_num)
theorem B3771089 : Blo 2203435 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B2514059 : Blo 2203435 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B26816629 : Blo 2203435 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B35755505 : Blo 2203435 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B23837003 : Blo 2203435 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B15891335 : Blo 2203435 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B10594223 : Blo 2203435 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B7062815 : Blo 2203435 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B4708543 : Blo 2203435 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B6278057 : Blo 2203435 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B4185371 : Blo 2203435 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B11160989 : Blo 2203435 11160989 := bstep (se 3 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 11160989 = 4185371) B4185371
theorem B7440659 : Blo 2203435 7440659 := bstep (se 1 (by rfl) ⟨5580494, by rfl⟩ : syracuseStep 7440659 = 11160989) B11160989
theorem B4960439 : Blo 2203435 4960439 := bstep (se 1 (by rfl) ⟨3720329, by rfl⟩ : syracuseStep 4960439 = 7440659) B7440659
theorem B3306959 : Blo 2203435 3306959 := bstep (se 1 (by rfl) ⟨2480219, by rfl⟩ : syracuseStep 3306959 = 4960439) B4960439
theorem B2204639 : Blo 2203435 2204639 := bstep (se 1 (by rfl) ⟨1653479, by rfl⟩ : syracuseStep 2204639 = 3306959) B3306959
theorem B3306965 : Blo 2203435 3306965 := bbase (se 7 (by rfl) ⟨38753, by rfl⟩ : syracuseStep 3306965 = 77507) (by norm_num)
theorem B2204643 : Blo 2203435 2204643 := bstep (se 1 (by rfl) ⟨1653482, by rfl⟩ : syracuseStep 2204643 = 3306965) B3306965
theorem B8370773 : Blo 2203435 8370773 := bbase (se 8 (by rfl) ⟨49047, by rfl⟩ : syracuseStep 8370773 = 98095) (by norm_num)
theorem B5580515 : Blo 2203435 5580515 := bstep (se 1 (by rfl) ⟨4185386, by rfl⟩ : syracuseStep 5580515 = 8370773) B8370773
theorem B3720343 : Blo 2203435 3720343 := bstep (se 1 (by rfl) ⟨2790257, by rfl⟩ : syracuseStep 3720343 = 5580515) B5580515
theorem B4960457 : Blo 2203435 4960457 := bstep (se 2 (by rfl) ⟨1860171, by rfl⟩ : syracuseStep 4960457 = 3720343) B3720343
theorem B3306971 : Blo 2203435 3306971 := bstep (se 1 (by rfl) ⟨2480228, by rfl⟩ : syracuseStep 3306971 = 4960457) B4960457
theorem B2204647 : Blo 2203435 2204647 := bstep (se 1 (by rfl) ⟨1653485, by rfl⟩ : syracuseStep 2204647 = 3306971) B3306971
theorem B2480233 : Blo 2203435 2480233 := bbase (se 2 (by rfl) ⟨930087, by rfl⟩ : syracuseStep 2480233 = 1860175) (by norm_num)
theorem B3306977 : Blo 2203435 3306977 := bstep (se 2 (by rfl) ⟨1240116, by rfl⟩ : syracuseStep 3306977 = 2480233) B2480233
theorem B2204651 : Blo 2203435 2204651 := bstep (se 1 (by rfl) ⟨1653488, by rfl⟩ : syracuseStep 2204651 = 3306977) B3306977
theorem B3628453 : Blo 2203435 3628453 := bbase (se 4 (by rfl) ⟨340167, by rfl⟩ : syracuseStep 3628453 = 680335) (by norm_num)
theorem B4837937 : Blo 2203435 4837937 := bstep (se 2 (by rfl) ⟨1814226, by rfl⟩ : syracuseStep 4837937 = 3628453) B3628453
theorem B12901165 : Blo 2203435 12901165 := bstep (se 3 (by rfl) ⟨2418968, by rfl⟩ : syracuseStep 12901165 = 4837937) B4837937
theorem B275224853 : Blo 2203435 275224853 := bstep (se 6 (by rfl) ⟨6450582, by rfl⟩ : syracuseStep 275224853 = 12901165) B12901165
theorem B183483235 : Blo 2203435 183483235 := bstep (se 1 (by rfl) ⟨137612426, by rfl⟩ : syracuseStep 183483235 = 275224853) B275224853
theorem B244644313 : Blo 2203435 244644313 := bstep (se 2 (by rfl) ⟨91741617, by rfl⟩ : syracuseStep 244644313 = 183483235) B183483235
theorem B326192417 : Blo 2203435 326192417 := bstep (se 2 (by rfl) ⟨122322156, by rfl⟩ : syracuseStep 326192417 = 244644313) B244644313
theorem B217461611 : Blo 2203435 217461611 := bstep (se 1 (by rfl) ⟨163096208, by rfl⟩ : syracuseStep 217461611 = 326192417) B326192417
theorem B579897629 : Blo 2203435 579897629 := bstep (se 3 (by rfl) ⟨108730805, by rfl⟩ : syracuseStep 579897629 = 217461611) B217461611
theorem B386598419 : Blo 2203435 386598419 := bstep (se 1 (by rfl) ⟨289948814, by rfl⟩ : syracuseStep 386598419 = 579897629) B579897629
theorem B257732279 : Blo 2203435 257732279 := bstep (se 1 (by rfl) ⟨193299209, by rfl⟩ : syracuseStep 257732279 = 386598419) B386598419
theorem B171821519 : Blo 2203435 171821519 := bstep (se 1 (by rfl) ⟨128866139, by rfl⟩ : syracuseStep 171821519 = 257732279) B257732279
theorem B114547679 : Blo 2203435 114547679 := bstep (se 1 (by rfl) ⟨85910759, by rfl⟩ : syracuseStep 114547679 = 171821519) B171821519
theorem B76365119 : Blo 2203435 76365119 := bstep (se 1 (by rfl) ⟨57273839, by rfl⟩ : syracuseStep 76365119 = 114547679) B114547679
theorem B50910079 : Blo 2203435 50910079 := bstep (se 1 (by rfl) ⟨38182559, by rfl⟩ : syracuseStep 50910079 = 76365119) B76365119
theorem B67880105 : Blo 2203435 67880105 := bstep (se 2 (by rfl) ⟨25455039, by rfl⟩ : syracuseStep 67880105 = 50910079) B50910079
theorem B45253403 : Blo 2203435 45253403 := bstep (se 1 (by rfl) ⟨33940052, by rfl⟩ : syracuseStep 45253403 = 67880105) B67880105
theorem B30168935 : Blo 2203435 30168935 := bstep (se 1 (by rfl) ⟨22626701, by rfl⟩ : syracuseStep 30168935 = 45253403) B45253403
theorem B20112623 : Blo 2203435 20112623 := bstep (se 1 (by rfl) ⟨15084467, by rfl⟩ : syracuseStep 20112623 = 30168935) B30168935
theorem B13408415 : Blo 2203435 13408415 := bstep (se 1 (by rfl) ⟨10056311, by rfl⟩ : syracuseStep 13408415 = 20112623) B20112623
theorem B8938943 : Blo 2203435 8938943 := bstep (se 1 (by rfl) ⟨6704207, by rfl⟩ : syracuseStep 8938943 = 13408415) B13408415
theorem B5959295 : Blo 2203435 5959295 := bstep (se 1 (by rfl) ⟨4469471, by rfl⟩ : syracuseStep 5959295 = 8938943) B8938943
theorem B3972863 : Blo 2203435 3972863 := bstep (se 1 (by rfl) ⟨2979647, by rfl⟩ : syracuseStep 3972863 = 5959295) B5959295
theorem B2648575 : Blo 2203435 2648575 := bstep (se 1 (by rfl) ⟨1986431, by rfl⟩ : syracuseStep 2648575 = 3972863) B3972863
theorem B3531433 : Blo 2203435 3531433 := bstep (se 2 (by rfl) ⟨1324287, by rfl⟩ : syracuseStep 3531433 = 2648575) B2648575
theorem B4708577 : Blo 2203435 4708577 := bstep (se 2 (by rfl) ⟨1765716, by rfl⟩ : syracuseStep 4708577 = 3531433) B3531433
theorem B12556205 : Blo 2203435 12556205 := bstep (se 3 (by rfl) ⟨2354288, by rfl⟩ : syracuseStep 12556205 = 4708577) B4708577
theorem B8370803 : Blo 2203435 8370803 := bstep (se 1 (by rfl) ⟨6278102, by rfl⟩ : syracuseStep 8370803 = 12556205) B12556205
theorem B5580535 : Blo 2203435 5580535 := bstep (se 1 (by rfl) ⟨4185401, by rfl⟩ : syracuseStep 5580535 = 8370803) B8370803
theorem B7440713 : Blo 2203435 7440713 := bstep (se 2 (by rfl) ⟨2790267, by rfl⟩ : syracuseStep 7440713 = 5580535) B5580535
theorem B4960475 : Blo 2203435 4960475 := bstep (se 1 (by rfl) ⟨3720356, by rfl⟩ : syracuseStep 4960475 = 7440713) B7440713
theorem B3306983 : Blo 2203435 3306983 := bstep (se 1 (by rfl) ⟨2480237, by rfl⟩ : syracuseStep 3306983 = 4960475) B4960475
theorem B2204655 : Blo 2203435 2204655 := bstep (se 1 (by rfl) ⟨1653491, by rfl⟩ : syracuseStep 2204655 = 3306983) B3306983
theorem B3306989 : Blo 2203435 3306989 := bbase (se 3 (by rfl) ⟨620060, by rfl⟩ : syracuseStep 3306989 = 1240121) (by norm_num)
theorem B2204659 : Blo 2203435 2204659 := bstep (se 1 (by rfl) ⟨1653494, by rfl⟩ : syracuseStep 2204659 = 3306989) B3306989
theorem B4960493 : Blo 2203435 4960493 := bbase (se 3 (by rfl) ⟨930092, by rfl⟩ : syracuseStep 4960493 = 1860185) (by norm_num)
theorem B3306995 : Blo 2203435 3306995 := bstep (se 1 (by rfl) ⟨2480246, by rfl⟩ : syracuseStep 3306995 = 4960493) B4960493
theorem B2204663 : Blo 2203435 2204663 := bstep (se 1 (by rfl) ⟨1653497, by rfl⟩ : syracuseStep 2204663 = 3306995) B3306995
theorem B3139069 : Blo 2203435 3139069 := bbase (se 3 (by rfl) ⟨588575, by rfl⟩ : syracuseStep 3139069 = 1177151) (by norm_num)
theorem B4185425 : Blo 2203435 4185425 := bstep (se 2 (by rfl) ⟨1569534, by rfl⟩ : syracuseStep 4185425 = 3139069) B3139069
theorem B2790283 : Blo 2203435 2790283 := bstep (se 1 (by rfl) ⟨2092712, by rfl⟩ : syracuseStep 2790283 = 4185425) B4185425
theorem B3720377 : Blo 2203435 3720377 := bstep (se 2 (by rfl) ⟨1395141, by rfl⟩ : syracuseStep 3720377 = 2790283) B2790283
theorem B2480251 : Blo 2203435 2480251 := bstep (se 1 (by rfl) ⟨1860188, by rfl⟩ : syracuseStep 2480251 = 3720377) B3720377
theorem B3307001 : Blo 2203435 3307001 := bstep (se 2 (by rfl) ⟨1240125, by rfl⟩ : syracuseStep 3307001 = 2480251) B2480251
theorem B2204667 : Blo 2203435 2204667 := bstep (se 1 (by rfl) ⟨1653500, by rfl⟩ : syracuseStep 2204667 = 3307001) B3307001
theorem B7945781 : Blo 2203435 7945781 := bbase (se 5 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 7945781 = 744917) (by norm_num)
theorem B84754997 : Blo 2203435 84754997 := bstep (se 5 (by rfl) ⟨3972890, by rfl⟩ : syracuseStep 84754997 = 7945781) B7945781
theorem B56503331 : Blo 2203435 56503331 := bstep (se 1 (by rfl) ⟨42377498, by rfl⟩ : syracuseStep 56503331 = 84754997) B84754997
theorem B37668887 : Blo 2203435 37668887 := bstep (se 1 (by rfl) ⟨28251665, by rfl⟩ : syracuseStep 37668887 = 56503331) B56503331
theorem B25112591 : Blo 2203435 25112591 := bstep (se 1 (by rfl) ⟨18834443, by rfl⟩ : syracuseStep 25112591 = 37668887) B37668887
theorem B16741727 : Blo 2203435 16741727 := bstep (se 1 (by rfl) ⟨12556295, by rfl⟩ : syracuseStep 16741727 = 25112591) B25112591
theorem B11161151 : Blo 2203435 11161151 := bstep (se 1 (by rfl) ⟨8370863, by rfl⟩ : syracuseStep 11161151 = 16741727) B16741727
theorem B7440767 : Blo 2203435 7440767 := bstep (se 1 (by rfl) ⟨5580575, by rfl⟩ : syracuseStep 7440767 = 11161151) B11161151
theorem B4960511 : Blo 2203435 4960511 := bstep (se 1 (by rfl) ⟨3720383, by rfl⟩ : syracuseStep 4960511 = 7440767) B7440767
theorem B3307007 : Blo 2203435 3307007 := bstep (se 1 (by rfl) ⟨2480255, by rfl⟩ : syracuseStep 3307007 = 4960511) B4960511
theorem B2204671 : Blo 2203435 2204671 := bstep (se 1 (by rfl) ⟨1653503, by rfl⟩ : syracuseStep 2204671 = 3307007) B3307007
theorem B3307013 : Blo 2203435 3307013 := bbase (se 4 (by rfl) ⟨310032, by rfl⟩ : syracuseStep 3307013 = 620065) (by norm_num)
theorem B2204675 : Blo 2203435 2204675 := bstep (se 1 (by rfl) ⟨1653506, by rfl⟩ : syracuseStep 2204675 = 3307013) B3307013
theorem B3720397 : Blo 2203435 3720397 := bbase (se 3 (by rfl) ⟨697574, by rfl⟩ : syracuseStep 3720397 = 1395149) (by norm_num)
theorem B4960529 : Blo 2203435 4960529 := bstep (se 2 (by rfl) ⟨1860198, by rfl⟩ : syracuseStep 4960529 = 3720397) B3720397
theorem B3307019 : Blo 2203435 3307019 := bstep (se 1 (by rfl) ⟨2480264, by rfl⟩ : syracuseStep 3307019 = 4960529) B4960529
theorem B2204679 : Blo 2203435 2204679 := bstep (se 1 (by rfl) ⟨1653509, by rfl⟩ : syracuseStep 2204679 = 3307019) B3307019
theorem B2480269 : Blo 2203435 2480269 := bbase (se 3 (by rfl) ⟨465050, by rfl⟩ : syracuseStep 2480269 = 930101) (by norm_num)
theorem B3307025 : Blo 2203435 3307025 := bstep (se 2 (by rfl) ⟨1240134, by rfl⟩ : syracuseStep 3307025 = 2480269) B2480269
theorem B2204683 : Blo 2203435 2204683 := bstep (se 1 (by rfl) ⟨1653512, by rfl⟩ : syracuseStep 2204683 = 3307025) B3307025
theorem B7440821 : Blo 2203435 7440821 := bbase (se 5 (by rfl) ⟨348788, by rfl⟩ : syracuseStep 7440821 = 697577) (by norm_num)
theorem B4960547 : Blo 2203435 4960547 := bstep (se 1 (by rfl) ⟨3720410, by rfl⟩ : syracuseStep 4960547 = 7440821) B7440821
theorem B3307031 : Blo 2203435 3307031 := bstep (se 1 (by rfl) ⟨2480273, by rfl⟩ : syracuseStep 3307031 = 4960547) B4960547
theorem B2204687 : Blo 2203435 2204687 := bstep (se 1 (by rfl) ⟨1653515, by rfl⟩ : syracuseStep 2204687 = 3307031) B3307031
theorem B3307037 : Blo 2203435 3307037 := bbase (se 3 (by rfl) ⟨620069, by rfl⟩ : syracuseStep 3307037 = 1240139) (by norm_num)
theorem B2204691 : Blo 2203435 2204691 := bstep (se 1 (by rfl) ⟨1653518, by rfl⟩ : syracuseStep 2204691 = 3307037) B3307037
theorem B4960565 : Blo 2203435 4960565 := bbase (se 5 (by rfl) ⟨232526, by rfl⟩ : syracuseStep 4960565 = 465053) (by norm_num)
theorem B3307043 : Blo 2203435 3307043 := bstep (se 1 (by rfl) ⟨2480282, by rfl⟩ : syracuseStep 3307043 = 4960565) B4960565
theorem B2204695 : Blo 2203435 2204695 := bstep (se 1 (by rfl) ⟨1653521, by rfl⟩ : syracuseStep 2204695 = 3307043) B3307043
theorem B2654165 : Blo 2203435 2654165 := bbase (se 7 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 2654165 = 62207) (by norm_num)
theorem B7077773 : Blo 2203435 7077773 := bstep (se 3 (by rfl) ⟨1327082, by rfl⟩ : syracuseStep 7077773 = 2654165) B2654165
theorem B4718515 : Blo 2203435 4718515 := bstep (se 1 (by rfl) ⟨3538886, by rfl⟩ : syracuseStep 4718515 = 7077773) B7077773
theorem B6291353 : Blo 2203435 6291353 := bstep (se 2 (by rfl) ⟨2359257, by rfl⟩ : syracuseStep 6291353 = 4718515) B4718515
theorem B1073724245 : Blo 2203435 1073724245 := bstep (se 9 (by rfl) ⟨3145676, by rfl⟩ : syracuseStep 1073724245 = 6291353) B6291353
theorem B715816163 : Blo 2203435 715816163 := bstep (se 1 (by rfl) ⟨536862122, by rfl⟩ : syracuseStep 715816163 = 1073724245) B1073724245
theorem B477210775 : Blo 2203435 477210775 := bstep (se 1 (by rfl) ⟨357908081, by rfl⟩ : syracuseStep 477210775 = 715816163) B715816163
theorem B636281033 : Blo 2203435 636281033 := bstep (se 2 (by rfl) ⟨238605387, by rfl⟩ : syracuseStep 636281033 = 477210775) B477210775
theorem B6786997685 : Blo 2203435 6786997685 := bstep (se 5 (by rfl) ⟨318140516, by rfl⟩ : syracuseStep 6786997685 = 636281033) B636281033
theorem B4524665123 : Blo 2203435 4524665123 := bstep (se 1 (by rfl) ⟨3393498842, by rfl⟩ : syracuseStep 4524665123 = 6786997685) B6786997685
theorem B3016443415 : Blo 2203435 3016443415 := bstep (se 1 (by rfl) ⟨2262332561, by rfl⟩ : syracuseStep 3016443415 = 4524665123) B4524665123
theorem B4021924553 : Blo 2203435 4021924553 := bstep (se 2 (by rfl) ⟨1508221707, by rfl⟩ : syracuseStep 4021924553 = 3016443415) B3016443415
theorem B2681283035 : Blo 2203435 2681283035 := bstep (se 1 (by rfl) ⟨2010962276, by rfl⟩ : syracuseStep 2681283035 = 4021924553) B4021924553
theorem B1787522023 : Blo 2203435 1787522023 := bstep (se 1 (by rfl) ⟨1340641517, by rfl⟩ : syracuseStep 1787522023 = 2681283035) B2681283035
theorem B9533450789 : Blo 2203435 9533450789 := bstep (se 4 (by rfl) ⟨893761011, by rfl⟩ : syracuseStep 9533450789 = 1787522023) B1787522023
theorem B6355633859 : Blo 2203435 6355633859 := bstep (se 1 (by rfl) ⟨4766725394, by rfl⟩ : syracuseStep 6355633859 = 9533450789) B9533450789
theorem B4237089239 : Blo 2203435 4237089239 := bstep (se 1 (by rfl) ⟨3177816929, by rfl⟩ : syracuseStep 4237089239 = 6355633859) B6355633859
theorem B2824726159 : Blo 2203435 2824726159 := bstep (se 1 (by rfl) ⟨2118544619, by rfl⟩ : syracuseStep 2824726159 = 4237089239) B4237089239
theorem B3766301545 : Blo 2203435 3766301545 := bstep (se 2 (by rfl) ⟨1412363079, by rfl⟩ : syracuseStep 3766301545 = 2824726159) B2824726159
theorem B5021735393 : Blo 2203435 5021735393 := bstep (se 2 (by rfl) ⟨1883150772, by rfl⟩ : syracuseStep 5021735393 = 3766301545) B3766301545
theorem B3347823595 : Blo 2203435 3347823595 := bstep (se 1 (by rfl) ⟨2510867696, by rfl⟩ : syracuseStep 3347823595 = 5021735393) B5021735393
theorem B4463764793 : Blo 2203435 4463764793 := bstep (se 2 (by rfl) ⟨1673911797, by rfl⟩ : syracuseStep 4463764793 = 3347823595) B3347823595
theorem B2975843195 : Blo 2203435 2975843195 := bstep (se 1 (by rfl) ⟨2231882396, by rfl⟩ : syracuseStep 2975843195 = 4463764793) B4463764793
theorem B1983895463 : Blo 2203435 1983895463 := bstep (se 1 (by rfl) ⟨1487921597, by rfl⟩ : syracuseStep 1983895463 = 2975843195) B2975843195
theorem B5290387901 : Blo 2203435 5290387901 := bstep (se 3 (by rfl) ⟨991947731, by rfl⟩ : syracuseStep 5290387901 = 1983895463) B1983895463
theorem B3526925267 : Blo 2203435 3526925267 := bstep (se 1 (by rfl) ⟨2645193950, by rfl⟩ : syracuseStep 3526925267 = 5290387901) B5290387901
theorem B2351283511 : Blo 2203435 2351283511 := bstep (se 1 (by rfl) ⟨1763462633, by rfl⟩ : syracuseStep 2351283511 = 3526925267) B3526925267
theorem B3135044681 : Blo 2203435 3135044681 := bstep (se 2 (by rfl) ⟨1175641755, by rfl⟩ : syracuseStep 3135044681 = 2351283511) B2351283511
theorem B2090029787 : Blo 2203435 2090029787 := bstep (se 1 (by rfl) ⟨1567522340, by rfl⟩ : syracuseStep 2090029787 = 3135044681) B3135044681
theorem B1393353191 : Blo 2203435 1393353191 := bstep (se 1 (by rfl) ⟨1045014893, by rfl⟩ : syracuseStep 1393353191 = 2090029787) B2090029787
theorem B928902127 : Blo 2203435 928902127 := bstep (se 1 (by rfl) ⟨696676595, by rfl⟩ : syracuseStep 928902127 = 1393353191) B1393353191
theorem B1238536169 : Blo 2203435 1238536169 := bstep (se 2 (by rfl) ⟨464451063, by rfl⟩ : syracuseStep 1238536169 = 928902127) B928902127
theorem B825690779 : Blo 2203435 825690779 := bstep (se 1 (by rfl) ⟨619268084, by rfl⟩ : syracuseStep 825690779 = 1238536169) B1238536169
theorem B550460519 : Blo 2203435 550460519 := bstep (se 1 (by rfl) ⟨412845389, by rfl⟩ : syracuseStep 550460519 = 825690779) B825690779
theorem B366973679 : Blo 2203435 366973679 := bstep (se 1 (by rfl) ⟨275230259, by rfl⟩ : syracuseStep 366973679 = 550460519) B550460519
theorem B978596477 : Blo 2203435 978596477 := bstep (se 3 (by rfl) ⟨183486839, by rfl⟩ : syracuseStep 978596477 = 366973679) B366973679
theorem B652397651 : Blo 2203435 652397651 := bstep (se 1 (by rfl) ⟨489298238, by rfl⟩ : syracuseStep 652397651 = 978596477) B978596477
theorem B434931767 : Blo 2203435 434931767 := bstep (se 1 (by rfl) ⟨326198825, by rfl⟩ : syracuseStep 434931767 = 652397651) B652397651
theorem B289954511 : Blo 2203435 289954511 := bstep (se 1 (by rfl) ⟨217465883, by rfl⟩ : syracuseStep 289954511 = 434931767) B434931767
theorem B193303007 : Blo 2203435 193303007 := bstep (se 1 (by rfl) ⟨144977255, by rfl⟩ : syracuseStep 193303007 = 289954511) B289954511
theorem B128868671 : Blo 2203435 128868671 := bstep (se 1 (by rfl) ⟨96651503, by rfl⟩ : syracuseStep 128868671 = 193303007) B193303007
theorem B343649789 : Blo 2203435 343649789 := bstep (se 3 (by rfl) ⟨64434335, by rfl⟩ : syracuseStep 343649789 = 128868671) B128868671
theorem B229099859 : Blo 2203435 229099859 := bstep (se 1 (by rfl) ⟨171824894, by rfl⟩ : syracuseStep 229099859 = 343649789) B343649789
theorem B152733239 : Blo 2203435 152733239 := bstep (se 1 (by rfl) ⟨114549929, by rfl⟩ : syracuseStep 152733239 = 229099859) B229099859
theorem B101822159 : Blo 2203435 101822159 := bstep (se 1 (by rfl) ⟨76366619, by rfl⟩ : syracuseStep 101822159 = 152733239) B152733239
theorem B67881439 : Blo 2203435 67881439 := bstep (se 1 (by rfl) ⟨50911079, by rfl⟩ : syracuseStep 67881439 = 101822159) B101822159
theorem B90508585 : Blo 2203435 90508585 := bstep (se 2 (by rfl) ⟨33940719, by rfl⟩ : syracuseStep 90508585 = 67881439) B67881439
theorem B120678113 : Blo 2203435 120678113 := bstep (se 2 (by rfl) ⟨45254292, by rfl⟩ : syracuseStep 120678113 = 90508585) B90508585
theorem B80452075 : Blo 2203435 80452075 := bstep (se 1 (by rfl) ⟨60339056, by rfl⟩ : syracuseStep 80452075 = 120678113) B120678113
theorem B107269433 : Blo 2203435 107269433 := bstep (se 2 (by rfl) ⟨40226037, by rfl⟩ : syracuseStep 107269433 = 80452075) B80452075
theorem B71512955 : Blo 2203435 71512955 := bstep (se 1 (by rfl) ⟨53634716, by rfl⟩ : syracuseStep 71512955 = 107269433) B107269433
theorem B47675303 : Blo 2203435 47675303 := bstep (se 1 (by rfl) ⟨35756477, by rfl⟩ : syracuseStep 47675303 = 71512955) B71512955
theorem B31783535 : Blo 2203435 31783535 := bstep (se 1 (by rfl) ⟨23837651, by rfl⟩ : syracuseStep 31783535 = 47675303) B47675303
theorem B21189023 : Blo 2203435 21189023 := bstep (se 1 (by rfl) ⟨15891767, by rfl⟩ : syracuseStep 21189023 = 31783535) B31783535
theorem B14126015 : Blo 2203435 14126015 := bstep (se 1 (by rfl) ⟨10594511, by rfl⟩ : syracuseStep 14126015 = 21189023) B21189023
theorem B9417343 : Blo 2203435 9417343 := bstep (se 1 (by rfl) ⟨7063007, by rfl⟩ : syracuseStep 9417343 = 14126015) B14126015
theorem B12556457 : Blo 2203435 12556457 := bstep (se 2 (by rfl) ⟨4708671, by rfl⟩ : syracuseStep 12556457 = 9417343) B9417343
theorem B8370971 : Blo 2203435 8370971 := bstep (se 1 (by rfl) ⟨6278228, by rfl⟩ : syracuseStep 8370971 = 12556457) B12556457
theorem B5580647 : Blo 2203435 5580647 := bstep (se 1 (by rfl) ⟨4185485, by rfl⟩ : syracuseStep 5580647 = 8370971) B8370971
theorem B3720431 : Blo 2203435 3720431 := bstep (se 1 (by rfl) ⟨2790323, by rfl⟩ : syracuseStep 3720431 = 5580647) B5580647
theorem B2480287 : Blo 2203435 2480287 := bstep (se 1 (by rfl) ⟨1860215, by rfl⟩ : syracuseStep 2480287 = 3720431) B3720431
theorem B3307049 : Blo 2203435 3307049 := bstep (se 2 (by rfl) ⟨1240143, by rfl⟩ : syracuseStep 3307049 = 2480287) B2480287
theorem B2204699 : Blo 2203435 2204699 := bstep (se 1 (by rfl) ⟨1653524, by rfl⟩ : syracuseStep 2204699 = 3307049) B3307049
theorem B2548433 : Blo 2203435 2548433 := bbase (se 2 (by rfl) ⟨955662, by rfl⟩ : syracuseStep 2548433 = 1911325) (by norm_num)
theorem B108733141 : Blo 2203435 108733141 := bstep (se 7 (by rfl) ⟨1274216, by rfl⟩ : syracuseStep 108733141 = 2548433) B2548433
theorem B144977521 : Blo 2203435 144977521 := bstep (se 2 (by rfl) ⟨54366570, by rfl⟩ : syracuseStep 144977521 = 108733141) B108733141
theorem B193303361 : Blo 2203435 193303361 := bstep (se 2 (by rfl) ⟨72488760, by rfl⟩ : syracuseStep 193303361 = 144977521) B144977521
theorem B128868907 : Blo 2203435 128868907 := bstep (se 1 (by rfl) ⟨96651680, by rfl⟩ : syracuseStep 128868907 = 193303361) B193303361
theorem B171825209 : Blo 2203435 171825209 := bstep (se 2 (by rfl) ⟨64434453, by rfl⟩ : syracuseStep 171825209 = 128868907) B128868907
theorem B114550139 : Blo 2203435 114550139 := bstep (se 1 (by rfl) ⟨85912604, by rfl⟩ : syracuseStep 114550139 = 171825209) B171825209
theorem B76366759 : Blo 2203435 76366759 := bstep (se 1 (by rfl) ⟨57275069, by rfl⟩ : syracuseStep 76366759 = 114550139) B114550139
theorem B101822345 : Blo 2203435 101822345 := bstep (se 2 (by rfl) ⟨38183379, by rfl⟩ : syracuseStep 101822345 = 76366759) B76366759
theorem B67881563 : Blo 2203435 67881563 := bstep (se 1 (by rfl) ⟨50911172, by rfl⟩ : syracuseStep 67881563 = 101822345) B101822345
theorem B45254375 : Blo 2203435 45254375 := bstep (se 1 (by rfl) ⟨33940781, by rfl⟩ : syracuseStep 45254375 = 67881563) B67881563
theorem B30169583 : Blo 2203435 30169583 := bstep (se 1 (by rfl) ⟨22627187, by rfl⟩ : syracuseStep 30169583 = 45254375) B45254375
theorem B20113055 : Blo 2203435 20113055 := bstep (se 1 (by rfl) ⟨15084791, by rfl⟩ : syracuseStep 20113055 = 30169583) B30169583
theorem B13408703 : Blo 2203435 13408703 := bstep (se 1 (by rfl) ⟨10056527, by rfl⟩ : syracuseStep 13408703 = 20113055) B20113055
theorem B8939135 : Blo 2203435 8939135 := bstep (se 1 (by rfl) ⟨6704351, by rfl⟩ : syracuseStep 8939135 = 13408703) B13408703
theorem B5959423 : Blo 2203435 5959423 := bstep (se 1 (by rfl) ⟨4469567, by rfl⟩ : syracuseStep 5959423 = 8939135) B8939135
theorem B31783589 : Blo 2203435 31783589 := bstep (se 4 (by rfl) ⟨2979711, by rfl⟩ : syracuseStep 31783589 = 5959423) B5959423
theorem B21189059 : Blo 2203435 21189059 := bstep (se 1 (by rfl) ⟨15891794, by rfl⟩ : syracuseStep 21189059 = 31783589) B31783589
theorem B14126039 : Blo 2203435 14126039 := bstep (se 1 (by rfl) ⟨10594529, by rfl⟩ : syracuseStep 14126039 = 21189059) B21189059
theorem B9417359 : Blo 2203435 9417359 := bstep (se 1 (by rfl) ⟨7063019, by rfl⟩ : syracuseStep 9417359 = 14126039) B14126039
theorem B6278239 : Blo 2203435 6278239 := bstep (se 1 (by rfl) ⟨4708679, by rfl⟩ : syracuseStep 6278239 = 9417359) B9417359
theorem B8370985 : Blo 2203435 8370985 := bstep (se 2 (by rfl) ⟨3139119, by rfl⟩ : syracuseStep 8370985 = 6278239) B6278239
theorem B11161313 : Blo 2203435 11161313 := bstep (se 2 (by rfl) ⟨4185492, by rfl⟩ : syracuseStep 11161313 = 8370985) B8370985
theorem B7440875 : Blo 2203435 7440875 := bstep (se 1 (by rfl) ⟨5580656, by rfl⟩ : syracuseStep 7440875 = 11161313) B11161313
theorem B4960583 : Blo 2203435 4960583 := bstep (se 1 (by rfl) ⟨3720437, by rfl⟩ : syracuseStep 4960583 = 7440875) B7440875
theorem B3307055 : Blo 2203435 3307055 := bstep (se 1 (by rfl) ⟨2480291, by rfl⟩ : syracuseStep 3307055 = 4960583) B4960583
theorem B2204703 : Blo 2203435 2204703 := bstep (se 1 (by rfl) ⟨1653527, by rfl⟩ : syracuseStep 2204703 = 3307055) B3307055
theorem B3307061 : Blo 2203435 3307061 := bbase (se 5 (by rfl) ⟨155018, by rfl⟩ : syracuseStep 3307061 = 310037) (by norm_num)
theorem B2204707 : Blo 2203435 2204707 := bstep (se 1 (by rfl) ⟨1653530, by rfl⟩ : syracuseStep 2204707 = 3307061) B3307061
theorem B5580677 : Blo 2203435 5580677 := bbase (se 4 (by rfl) ⟨523188, by rfl⟩ : syracuseStep 5580677 = 1046377) (by norm_num)
theorem B3720451 : Blo 2203435 3720451 := bstep (se 1 (by rfl) ⟨2790338, by rfl⟩ : syracuseStep 3720451 = 5580677) B5580677
theorem B4960601 : Blo 2203435 4960601 := bstep (se 2 (by rfl) ⟨1860225, by rfl⟩ : syracuseStep 4960601 = 3720451) B3720451
theorem B3307067 : Blo 2203435 3307067 := bstep (se 1 (by rfl) ⟨2480300, by rfl⟩ : syracuseStep 3307067 = 4960601) B4960601
theorem B2204711 : Blo 2203435 2204711 := bstep (se 1 (by rfl) ⟨1653533, by rfl⟩ : syracuseStep 2204711 = 3307067) B3307067
theorem B2480305 : Blo 2203435 2480305 := bbase (se 2 (by rfl) ⟨930114, by rfl⟩ : syracuseStep 2480305 = 1860229) (by norm_num)
theorem B3307073 : Blo 2203435 3307073 := bstep (se 2 (by rfl) ⟨1240152, by rfl⟩ : syracuseStep 3307073 = 2480305) B2480305
theorem B2204715 : Blo 2203435 2204715 := bstep (se 1 (by rfl) ⟨1653536, by rfl⟩ : syracuseStep 2204715 = 3307073) B3307073
theorem B2354357 : Blo 2203435 2354357 := bbase (se 5 (by rfl) ⟨110360, by rfl⟩ : syracuseStep 2354357 = 220721) (by norm_num)
theorem B6278285 : Blo 2203435 6278285 := bstep (se 3 (by rfl) ⟨1177178, by rfl⟩ : syracuseStep 6278285 = 2354357) B2354357
theorem B4185523 : Blo 2203435 4185523 := bstep (se 1 (by rfl) ⟨3139142, by rfl⟩ : syracuseStep 4185523 = 6278285) B6278285
theorem B5580697 : Blo 2203435 5580697 := bstep (se 2 (by rfl) ⟨2092761, by rfl⟩ : syracuseStep 5580697 = 4185523) B4185523
theorem B7440929 : Blo 2203435 7440929 := bstep (se 2 (by rfl) ⟨2790348, by rfl⟩ : syracuseStep 7440929 = 5580697) B5580697
theorem B4960619 : Blo 2203435 4960619 := bstep (se 1 (by rfl) ⟨3720464, by rfl⟩ : syracuseStep 4960619 = 7440929) B7440929
theorem B3307079 : Blo 2203435 3307079 := bstep (se 1 (by rfl) ⟨2480309, by rfl⟩ : syracuseStep 3307079 = 4960619) B4960619
theorem B2204719 : Blo 2203435 2204719 := bstep (se 1 (by rfl) ⟨1653539, by rfl⟩ : syracuseStep 2204719 = 3307079) B3307079
theorem B3307085 : Blo 2203435 3307085 := bbase (se 3 (by rfl) ⟨620078, by rfl⟩ : syracuseStep 3307085 = 1240157) (by norm_num)
theorem B2204723 : Blo 2203435 2204723 := bstep (se 1 (by rfl) ⟨1653542, by rfl⟩ : syracuseStep 2204723 = 3307085) B3307085
theorem B4960637 : Blo 2203435 4960637 := bbase (se 3 (by rfl) ⟨930119, by rfl⟩ : syracuseStep 4960637 = 1860239) (by norm_num)
theorem B3307091 : Blo 2203435 3307091 := bstep (se 1 (by rfl) ⟨2480318, by rfl⟩ : syracuseStep 3307091 = 4960637) B4960637
theorem B2204727 : Blo 2203435 2204727 := bstep (se 1 (by rfl) ⟨1653545, by rfl⟩ : syracuseStep 2204727 = 3307091) B3307091
theorem B3720485 : Blo 2203435 3720485 := bbase (se 4 (by rfl) ⟨348795, by rfl⟩ : syracuseStep 3720485 = 697591) (by norm_num)
theorem B2480323 : Blo 2203435 2480323 := bstep (se 1 (by rfl) ⟨1860242, by rfl⟩ : syracuseStep 2480323 = 3720485) B3720485
theorem B3307097 : Blo 2203435 3307097 := bstep (se 2 (by rfl) ⟨1240161, by rfl⟩ : syracuseStep 3307097 = 2480323) B2480323
theorem B2204731 : Blo 2203435 2204731 := bstep (se 1 (by rfl) ⟨1653548, by rfl⟩ : syracuseStep 2204731 = 3307097) B3307097
theorem B3139165 : Blo 2203435 3139165 := bbase (se 3 (by rfl) ⟨588593, by rfl⟩ : syracuseStep 3139165 = 1177187) (by norm_num)
theorem B16742213 : Blo 2203435 16742213 := bstep (se 4 (by rfl) ⟨1569582, by rfl⟩ : syracuseStep 16742213 = 3139165) B3139165
theorem B11161475 : Blo 2203435 11161475 := bstep (se 1 (by rfl) ⟨8371106, by rfl⟩ : syracuseStep 11161475 = 16742213) B16742213
theorem B7440983 : Blo 2203435 7440983 := bstep (se 1 (by rfl) ⟨5580737, by rfl⟩ : syracuseStep 7440983 = 11161475) B11161475
theorem B4960655 : Blo 2203435 4960655 := bstep (se 1 (by rfl) ⟨3720491, by rfl⟩ : syracuseStep 4960655 = 7440983) B7440983
theorem B3307103 : Blo 2203435 3307103 := bstep (se 1 (by rfl) ⟨2480327, by rfl⟩ : syracuseStep 3307103 = 4960655) B4960655
theorem B2204735 : Blo 2203435 2204735 := bstep (se 1 (by rfl) ⟨1653551, by rfl⟩ : syracuseStep 2204735 = 3307103) B3307103
theorem B3307109 : Blo 2203435 3307109 := bbase (se 4 (by rfl) ⟨310041, by rfl⟩ : syracuseStep 3307109 = 620083) (by norm_num)
theorem B2204739 : Blo 2203435 2204739 := bstep (se 1 (by rfl) ⟨1653554, by rfl⟩ : syracuseStep 2204739 = 3307109) B3307109
theorem B3771269 : Blo 2203435 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B2514179 : Blo 2203435 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B6704477 : Blo 2203435 6704477 := bstep (se 3 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 6704477 = 2514179) B2514179
theorem B4469651 : Blo 2203435 4469651 := bstep (se 1 (by rfl) ⟨3352238, by rfl⟩ : syracuseStep 4469651 = 6704477) B6704477
theorem B2979767 : Blo 2203435 2979767 := bstep (se 1 (by rfl) ⟨2234825, by rfl⟩ : syracuseStep 2979767 = 4469651) B4469651
theorem B7946045 : Blo 2203435 7946045 := bstep (se 3 (by rfl) ⟨1489883, by rfl⟩ : syracuseStep 7946045 = 2979767) B2979767
theorem B5297363 : Blo 2203435 5297363 := bstep (se 1 (by rfl) ⟨3973022, by rfl⟩ : syracuseStep 5297363 = 7946045) B7946045
theorem B3531575 : Blo 2203435 3531575 := bstep (se 1 (by rfl) ⟨2648681, by rfl⟩ : syracuseStep 3531575 = 5297363) B5297363
theorem B2354383 : Blo 2203435 2354383 := bstep (se 1 (by rfl) ⟨1765787, by rfl⟩ : syracuseStep 2354383 = 3531575) B3531575
theorem B3139177 : Blo 2203435 3139177 := bstep (se 2 (by rfl) ⟨1177191, by rfl⟩ : syracuseStep 3139177 = 2354383) B2354383
theorem B4185569 : Blo 2203435 4185569 := bstep (se 2 (by rfl) ⟨1569588, by rfl⟩ : syracuseStep 4185569 = 3139177) B3139177
theorem B2790379 : Blo 2203435 2790379 := bstep (se 1 (by rfl) ⟨2092784, by rfl⟩ : syracuseStep 2790379 = 4185569) B4185569
theorem B3720505 : Blo 2203435 3720505 := bstep (se 2 (by rfl) ⟨1395189, by rfl⟩ : syracuseStep 3720505 = 2790379) B2790379
theorem B4960673 : Blo 2203435 4960673 := bstep (se 2 (by rfl) ⟨1860252, by rfl⟩ : syracuseStep 4960673 = 3720505) B3720505
theorem B3307115 : Blo 2203435 3307115 := bstep (se 1 (by rfl) ⟨2480336, by rfl⟩ : syracuseStep 3307115 = 4960673) B4960673
theorem B2204743 : Blo 2203435 2204743 := bstep (se 1 (by rfl) ⟨1653557, by rfl⟩ : syracuseStep 2204743 = 3307115) B3307115
theorem B2480341 : Blo 2203435 2480341 := bbase (se 7 (by rfl) ⟨29066, by rfl⟩ : syracuseStep 2480341 = 58133) (by norm_num)
theorem B3307121 : Blo 2203435 3307121 := bstep (se 2 (by rfl) ⟨1240170, by rfl⟩ : syracuseStep 3307121 = 2480341) B2480341
theorem B2204747 : Blo 2203435 2204747 := bstep (se 1 (by rfl) ⟨1653560, by rfl⟩ : syracuseStep 2204747 = 3307121) B3307121
theorem B2790389 : Blo 2203435 2790389 := bbase (se 5 (by rfl) ⟨130799, by rfl⟩ : syracuseStep 2790389 = 261599) (by norm_num)
theorem B7441037 : Blo 2203435 7441037 := bstep (se 3 (by rfl) ⟨1395194, by rfl⟩ : syracuseStep 7441037 = 2790389) B2790389
theorem B4960691 : Blo 2203435 4960691 := bstep (se 1 (by rfl) ⟨3720518, by rfl⟩ : syracuseStep 4960691 = 7441037) B7441037
theorem B3307127 : Blo 2203435 3307127 := bstep (se 1 (by rfl) ⟨2480345, by rfl⟩ : syracuseStep 3307127 = 4960691) B4960691
theorem B2204751 : Blo 2203435 2204751 := bstep (se 1 (by rfl) ⟨1653563, by rfl⟩ : syracuseStep 2204751 = 3307127) B3307127
theorem B3307133 : Blo 2203435 3307133 := bbase (se 3 (by rfl) ⟨620087, by rfl⟩ : syracuseStep 3307133 = 1240175) (by norm_num)
theorem B2204755 : Blo 2203435 2204755 := bstep (se 1 (by rfl) ⟨1653566, by rfl⟩ : syracuseStep 2204755 = 3307133) B3307133
theorem B4960709 : Blo 2203435 4960709 := bbase (se 4 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 4960709 = 930133) (by norm_num)
theorem B3307139 : Blo 2203435 3307139 := bstep (se 1 (by rfl) ⟨2480354, by rfl⟩ : syracuseStep 3307139 = 4960709) B4960709
theorem B2204759 : Blo 2203435 2204759 := bstep (se 1 (by rfl) ⟨1653569, by rfl⟩ : syracuseStep 2204759 = 3307139) B3307139
theorem B2648705 : Blo 2203435 2648705 := bbase (se 2 (by rfl) ⟨993264, by rfl⟩ : syracuseStep 2648705 = 1986529) (by norm_num)
theorem B7063213 : Blo 2203435 7063213 := bstep (se 3 (by rfl) ⟨1324352, by rfl⟩ : syracuseStep 7063213 = 2648705) B2648705
theorem B9417617 : Blo 2203435 9417617 := bstep (se 2 (by rfl) ⟨3531606, by rfl⟩ : syracuseStep 9417617 = 7063213) B7063213
theorem B6278411 : Blo 2203435 6278411 := bstep (se 1 (by rfl) ⟨4708808, by rfl⟩ : syracuseStep 6278411 = 9417617) B9417617
theorem B4185607 : Blo 2203435 4185607 := bstep (se 1 (by rfl) ⟨3139205, by rfl⟩ : syracuseStep 4185607 = 6278411) B6278411
theorem B5580809 : Blo 2203435 5580809 := bstep (se 2 (by rfl) ⟨2092803, by rfl⟩ : syracuseStep 5580809 = 4185607) B4185607
theorem B3720539 : Blo 2203435 3720539 := bstep (se 1 (by rfl) ⟨2790404, by rfl⟩ : syracuseStep 3720539 = 5580809) B5580809
theorem B2480359 : Blo 2203435 2480359 := bstep (se 1 (by rfl) ⟨1860269, by rfl⟩ : syracuseStep 2480359 = 3720539) B3720539
theorem B3307145 : Blo 2203435 3307145 := bstep (se 2 (by rfl) ⟨1240179, by rfl⟩ : syracuseStep 3307145 = 2480359) B2480359
theorem B2204763 : Blo 2203435 2204763 := bstep (se 1 (by rfl) ⟨1653572, by rfl⟩ : syracuseStep 2204763 = 3307145) B3307145
theorem B11161637 : Blo 2203435 11161637 := bbase (se 4 (by rfl) ⟨1046403, by rfl⟩ : syracuseStep 11161637 = 2092807) (by norm_num)
theorem B7441091 : Blo 2203435 7441091 := bstep (se 1 (by rfl) ⟨5580818, by rfl⟩ : syracuseStep 7441091 = 11161637) B11161637
theorem B4960727 : Blo 2203435 4960727 := bstep (se 1 (by rfl) ⟨3720545, by rfl⟩ : syracuseStep 4960727 = 7441091) B7441091
theorem B3307151 : Blo 2203435 3307151 := bstep (se 1 (by rfl) ⟨2480363, by rfl⟩ : syracuseStep 3307151 = 4960727) B4960727
theorem B2204767 : Blo 2203435 2204767 := bstep (se 1 (by rfl) ⟨1653575, by rfl⟩ : syracuseStep 2204767 = 3307151) B3307151
theorem B3307157 : Blo 2203435 3307157 := bbase (se 6 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 3307157 = 155023) (by norm_num)
theorem B2204771 : Blo 2203435 2204771 := bstep (se 1 (by rfl) ⟨1653578, by rfl⟩ : syracuseStep 2204771 = 3307157) B3307157
theorem B8939429 : Blo 2203435 8939429 := bbase (se 4 (by rfl) ⟨838071, by rfl⟩ : syracuseStep 8939429 = 1676143) (by norm_num)
theorem B5959619 : Blo 2203435 5959619 := bstep (se 1 (by rfl) ⟨4469714, by rfl⟩ : syracuseStep 5959619 = 8939429) B8939429
theorem B3973079 : Blo 2203435 3973079 := bstep (se 1 (by rfl) ⟨2979809, by rfl⟩ : syracuseStep 3973079 = 5959619) B5959619
theorem B2648719 : Blo 2203435 2648719 := bstep (se 1 (by rfl) ⟨1986539, by rfl⟩ : syracuseStep 2648719 = 3973079) B3973079
theorem B14126501 : Blo 2203435 14126501 := bstep (se 4 (by rfl) ⟨1324359, by rfl⟩ : syracuseStep 14126501 = 2648719) B2648719
theorem B9417667 : Blo 2203435 9417667 := bstep (se 1 (by rfl) ⟨7063250, by rfl⟩ : syracuseStep 9417667 = 14126501) B14126501
theorem B12556889 : Blo 2203435 12556889 := bstep (se 2 (by rfl) ⟨4708833, by rfl⟩ : syracuseStep 12556889 = 9417667) B9417667
theorem B8371259 : Blo 2203435 8371259 := bstep (se 1 (by rfl) ⟨6278444, by rfl⟩ : syracuseStep 8371259 = 12556889) B12556889
theorem B5580839 : Blo 2203435 5580839 := bstep (se 1 (by rfl) ⟨4185629, by rfl⟩ : syracuseStep 5580839 = 8371259) B8371259
theorem B3720559 : Blo 2203435 3720559 := bstep (se 1 (by rfl) ⟨2790419, by rfl⟩ : syracuseStep 3720559 = 5580839) B5580839
theorem B4960745 : Blo 2203435 4960745 := bstep (se 2 (by rfl) ⟨1860279, by rfl⟩ : syracuseStep 4960745 = 3720559) B3720559
theorem B3307163 : Blo 2203435 3307163 := bstep (se 1 (by rfl) ⟨2480372, by rfl⟩ : syracuseStep 3307163 = 4960745) B4960745
theorem B2204775 : Blo 2203435 2204775 := bstep (se 1 (by rfl) ⟨1653581, by rfl⟩ : syracuseStep 2204775 = 3307163) B3307163
theorem B2480377 : Blo 2203435 2480377 := bbase (se 2 (by rfl) ⟨930141, by rfl⟩ : syracuseStep 2480377 = 1860283) (by norm_num)
theorem B3307169 : Blo 2203435 3307169 := bstep (se 2 (by rfl) ⟨1240188, by rfl⟩ : syracuseStep 3307169 = 2480377) B2480377
theorem B2204779 : Blo 2203435 2204779 := bstep (se 1 (by rfl) ⟨1653584, by rfl⟩ : syracuseStep 2204779 = 3307169) B3307169
theorem B9417701 : Blo 2203435 9417701 := bbase (se 4 (by rfl) ⟨882909, by rfl⟩ : syracuseStep 9417701 = 1765819) (by norm_num)
theorem B6278467 : Blo 2203435 6278467 := bstep (se 1 (by rfl) ⟨4708850, by rfl⟩ : syracuseStep 6278467 = 9417701) B9417701
theorem B8371289 : Blo 2203435 8371289 := bstep (se 2 (by rfl) ⟨3139233, by rfl⟩ : syracuseStep 8371289 = 6278467) B6278467
theorem B5580859 : Blo 2203435 5580859 := bstep (se 1 (by rfl) ⟨4185644, by rfl⟩ : syracuseStep 5580859 = 8371289) B8371289
theorem B7441145 : Blo 2203435 7441145 := bstep (se 2 (by rfl) ⟨2790429, by rfl⟩ : syracuseStep 7441145 = 5580859) B5580859
theorem B4960763 : Blo 2203435 4960763 := bstep (se 1 (by rfl) ⟨3720572, by rfl⟩ : syracuseStep 4960763 = 7441145) B7441145
theorem B3307175 : Blo 2203435 3307175 := bstep (se 1 (by rfl) ⟨2480381, by rfl⟩ : syracuseStep 3307175 = 4960763) B4960763
theorem B2204783 : Blo 2203435 2204783 := bstep (se 1 (by rfl) ⟨1653587, by rfl⟩ : syracuseStep 2204783 = 3307175) B3307175
theorem B3307181 : Blo 2203435 3307181 := bbase (se 3 (by rfl) ⟨620096, by rfl⟩ : syracuseStep 3307181 = 1240193) (by norm_num)
theorem B2204787 : Blo 2203435 2204787 := bstep (se 1 (by rfl) ⟨1653590, by rfl⟩ : syracuseStep 2204787 = 3307181) B3307181
theorem B4960781 : Blo 2203435 4960781 := bbase (se 3 (by rfl) ⟨930146, by rfl⟩ : syracuseStep 4960781 = 1860293) (by norm_num)
theorem B3307187 : Blo 2203435 3307187 := bstep (se 1 (by rfl) ⟨2480390, by rfl⟩ : syracuseStep 3307187 = 4960781) B4960781
theorem B2204791 : Blo 2203435 2204791 := bstep (se 1 (by rfl) ⟨1653593, by rfl⟩ : syracuseStep 2204791 = 3307187) B3307187
theorem B2790445 : Blo 2203435 2790445 := bbase (se 3 (by rfl) ⟨523208, by rfl⟩ : syracuseStep 2790445 = 1046417) (by norm_num)
theorem B3720593 : Blo 2203435 3720593 := bstep (se 2 (by rfl) ⟨1395222, by rfl⟩ : syracuseStep 3720593 = 2790445) B2790445
theorem B2480395 : Blo 2203435 2480395 := bstep (se 1 (by rfl) ⟨1860296, by rfl⟩ : syracuseStep 2480395 = 3720593) B3720593
theorem B3307193 : Blo 2203435 3307193 := bstep (se 2 (by rfl) ⟨1240197, by rfl⟩ : syracuseStep 3307193 = 2480395) B2480395
theorem B2204795 : Blo 2203435 2204795 := bstep (se 1 (by rfl) ⟨1653596, by rfl⟩ : syracuseStep 2204795 = 3307193) B3307193
theorem B2234881 : Blo 2203435 2234881 := bbase (se 2 (by rfl) ⟨838080, by rfl⟩ : syracuseStep 2234881 = 1676161) (by norm_num)
theorem B11919365 : Blo 2203435 11919365 := bstep (se 4 (by rfl) ⟨1117440, by rfl⟩ : syracuseStep 11919365 = 2234881) B2234881
theorem B7946243 : Blo 2203435 7946243 := bstep (se 1 (by rfl) ⟨5959682, by rfl⟩ : syracuseStep 7946243 = 11919365) B11919365
theorem B5297495 : Blo 2203435 5297495 := bstep (se 1 (by rfl) ⟨3973121, by rfl⟩ : syracuseStep 5297495 = 7946243) B7946243
theorem B14126653 : Blo 2203435 14126653 := bstep (se 3 (by rfl) ⟨2648747, by rfl⟩ : syracuseStep 14126653 = 5297495) B5297495
theorem B18835537 : Blo 2203435 18835537 := bstep (se 2 (by rfl) ⟨7063326, by rfl⟩ : syracuseStep 18835537 = 14126653) B14126653
theorem B25114049 : Blo 2203435 25114049 := bstep (se 2 (by rfl) ⟨9417768, by rfl⟩ : syracuseStep 25114049 = 18835537) B18835537
theorem B16742699 : Blo 2203435 16742699 := bstep (se 1 (by rfl) ⟨12557024, by rfl⟩ : syracuseStep 16742699 = 25114049) B25114049
theorem B11161799 : Blo 2203435 11161799 := bstep (se 1 (by rfl) ⟨8371349, by rfl⟩ : syracuseStep 11161799 = 16742699) B16742699
theorem B7441199 : Blo 2203435 7441199 := bstep (se 1 (by rfl) ⟨5580899, by rfl⟩ : syracuseStep 7441199 = 11161799) B11161799
theorem B4960799 : Blo 2203435 4960799 := bstep (se 1 (by rfl) ⟨3720599, by rfl⟩ : syracuseStep 4960799 = 7441199) B7441199
theorem B3307199 : Blo 2203435 3307199 := bstep (se 1 (by rfl) ⟨2480399, by rfl⟩ : syracuseStep 3307199 = 4960799) B4960799
theorem B2204799 : Blo 2203435 2204799 := bstep (se 1 (by rfl) ⟨1653599, by rfl⟩ : syracuseStep 2204799 = 3307199) B3307199
theorem B3307205 : Blo 2203435 3307205 := bbase (se 4 (by rfl) ⟨310050, by rfl⟩ : syracuseStep 3307205 = 620101) (by norm_num)
theorem B2204803 : Blo 2203435 2204803 := bstep (se 1 (by rfl) ⟨1653602, by rfl⟩ : syracuseStep 2204803 = 3307205) B3307205
theorem B3720613 : Blo 2203435 3720613 := bbase (se 4 (by rfl) ⟨348807, by rfl⟩ : syracuseStep 3720613 = 697615) (by norm_num)
theorem B4960817 : Blo 2203435 4960817 := bstep (se 2 (by rfl) ⟨1860306, by rfl⟩ : syracuseStep 4960817 = 3720613) B3720613
theorem B3307211 : Blo 2203435 3307211 := bstep (se 1 (by rfl) ⟨2480408, by rfl⟩ : syracuseStep 3307211 = 4960817) B4960817
theorem B2204807 : Blo 2203435 2204807 := bstep (se 1 (by rfl) ⟨1653605, by rfl⟩ : syracuseStep 2204807 = 3307211) B3307211
theorem B2480413 : Blo 2203435 2480413 := bbase (se 3 (by rfl) ⟨465077, by rfl⟩ : syracuseStep 2480413 = 930155) (by norm_num)
theorem B3307217 : Blo 2203435 3307217 := bstep (se 2 (by rfl) ⟨1240206, by rfl⟩ : syracuseStep 3307217 = 2480413) B2480413
theorem B2204811 : Blo 2203435 2204811 := bstep (se 1 (by rfl) ⟨1653608, by rfl⟩ : syracuseStep 2204811 = 3307217) B3307217
theorem B7441253 : Blo 2203435 7441253 := bbase (se 4 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 7441253 = 1395235) (by norm_num)
theorem B4960835 : Blo 2203435 4960835 := bstep (se 1 (by rfl) ⟨3720626, by rfl⟩ : syracuseStep 4960835 = 7441253) B7441253
theorem B3307223 : Blo 2203435 3307223 := bstep (se 1 (by rfl) ⟨2480417, by rfl⟩ : syracuseStep 3307223 = 4960835) B4960835
theorem B2204815 : Blo 2203435 2204815 := bstep (se 1 (by rfl) ⟨1653611, by rfl⟩ : syracuseStep 2204815 = 3307223) B3307223
theorem B3307229 : Blo 2203435 3307229 := bbase (se 3 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 3307229 = 1240211) (by norm_num)
theorem B2204819 : Blo 2203435 2204819 := bstep (se 1 (by rfl) ⟨1653614, by rfl⟩ : syracuseStep 2204819 = 3307229) B3307229
theorem B4960853 : Blo 2203435 4960853 := bbase (se 8 (by rfl) ⟨29067, by rfl⟩ : syracuseStep 4960853 = 58135) (by norm_num)
theorem B3307235 : Blo 2203435 3307235 := bstep (se 1 (by rfl) ⟨2480426, by rfl⟩ : syracuseStep 3307235 = 4960853) B4960853
theorem B2204823 : Blo 2203435 2204823 := bstep (se 1 (by rfl) ⟨1653617, by rfl⟩ : syracuseStep 2204823 = 3307235) B3307235
theorem B3531709 : Blo 2203435 3531709 := bbase (se 3 (by rfl) ⟨662195, by rfl⟩ : syracuseStep 3531709 = 1324391) (by norm_num)
theorem B4708945 : Blo 2203435 4708945 := bstep (se 2 (by rfl) ⟨1765854, by rfl⟩ : syracuseStep 4708945 = 3531709) B3531709
theorem B6278593 : Blo 2203435 6278593 := bstep (se 2 (by rfl) ⟨2354472, by rfl⟩ : syracuseStep 6278593 = 4708945) B4708945
theorem B8371457 : Blo 2203435 8371457 := bstep (se 2 (by rfl) ⟨3139296, by rfl⟩ : syracuseStep 8371457 = 6278593) B6278593
theorem B5580971 : Blo 2203435 5580971 := bstep (se 1 (by rfl) ⟨4185728, by rfl⟩ : syracuseStep 5580971 = 8371457) B8371457
theorem B3720647 : Blo 2203435 3720647 := bstep (se 1 (by rfl) ⟨2790485, by rfl⟩ : syracuseStep 3720647 = 5580971) B5580971
theorem B2480431 : Blo 2203435 2480431 := bstep (se 1 (by rfl) ⟨1860323, by rfl⟩ : syracuseStep 2480431 = 3720647) B3720647
theorem B3307241 : Blo 2203435 3307241 := bstep (se 2 (by rfl) ⟨1240215, by rfl⟩ : syracuseStep 3307241 = 2480431) B2480431
theorem B2204827 : Blo 2203435 2204827 := bstep (se 1 (by rfl) ⟨1653620, by rfl⟩ : syracuseStep 2204827 = 3307241) B3307241
theorem B28253717 : Blo 2203435 28253717 := bbase (se 6 (by rfl) ⟨662196, by rfl⟩ : syracuseStep 28253717 = 1324393) (by norm_num)
theorem B18835811 : Blo 2203435 18835811 := bstep (se 1 (by rfl) ⟨14126858, by rfl⟩ : syracuseStep 18835811 = 28253717) B28253717
theorem B12557207 : Blo 2203435 12557207 := bstep (se 1 (by rfl) ⟨9417905, by rfl⟩ : syracuseStep 12557207 = 18835811) B18835811
theorem B8371471 : Blo 2203435 8371471 := bstep (se 1 (by rfl) ⟨6278603, by rfl⟩ : syracuseStep 8371471 = 12557207) B12557207
theorem B11161961 : Blo 2203435 11161961 := bstep (se 2 (by rfl) ⟨4185735, by rfl⟩ : syracuseStep 11161961 = 8371471) B8371471
theorem B7441307 : Blo 2203435 7441307 := bstep (se 1 (by rfl) ⟨5580980, by rfl⟩ : syracuseStep 7441307 = 11161961) B11161961
theorem B4960871 : Blo 2203435 4960871 := bstep (se 1 (by rfl) ⟨3720653, by rfl⟩ : syracuseStep 4960871 = 7441307) B7441307
theorem B3307247 : Blo 2203435 3307247 := bstep (se 1 (by rfl) ⟨2480435, by rfl⟩ : syracuseStep 3307247 = 4960871) B4960871
theorem B2204831 : Blo 2203435 2204831 := bstep (se 1 (by rfl) ⟨1653623, by rfl⟩ : syracuseStep 2204831 = 3307247) B3307247
theorem B3307253 : Blo 2203435 3307253 := bbase (se 5 (by rfl) ⟨155027, by rfl⟩ : syracuseStep 3307253 = 310055) (by norm_num)
theorem B2204835 : Blo 2203435 2204835 := bstep (se 1 (by rfl) ⟨1653626, by rfl⟩ : syracuseStep 2204835 = 3307253) B3307253
theorem B9417941 : Blo 2203435 9417941 := bbase (se 7 (by rfl) ⟨110366, by rfl⟩ : syracuseStep 9417941 = 220733) (by norm_num)
theorem B6278627 : Blo 2203435 6278627 := bstep (se 1 (by rfl) ⟨4708970, by rfl⟩ : syracuseStep 6278627 = 9417941) B9417941
theorem B4185751 : Blo 2203435 4185751 := bstep (se 1 (by rfl) ⟨3139313, by rfl⟩ : syracuseStep 4185751 = 6278627) B6278627
theorem B5581001 : Blo 2203435 5581001 := bstep (se 2 (by rfl) ⟨2092875, by rfl⟩ : syracuseStep 5581001 = 4185751) B4185751
theorem B3720667 : Blo 2203435 3720667 := bstep (se 1 (by rfl) ⟨2790500, by rfl⟩ : syracuseStep 3720667 = 5581001) B5581001
theorem B4960889 : Blo 2203435 4960889 := bstep (se 2 (by rfl) ⟨1860333, by rfl⟩ : syracuseStep 4960889 = 3720667) B3720667
theorem B3307259 : Blo 2203435 3307259 := bstep (se 1 (by rfl) ⟨2480444, by rfl⟩ : syracuseStep 3307259 = 4960889) B4960889
theorem B2204839 : Blo 2203435 2204839 := bstep (se 1 (by rfl) ⟨1653629, by rfl⟩ : syracuseStep 2204839 = 3307259) B3307259
theorem B2480449 : Blo 2203435 2480449 := bbase (se 2 (by rfl) ⟨930168, by rfl⟩ : syracuseStep 2480449 = 1860337) (by norm_num)
theorem B3307265 : Blo 2203435 3307265 := bstep (se 2 (by rfl) ⟨1240224, by rfl⟩ : syracuseStep 3307265 = 2480449) B2480449
theorem B2204843 : Blo 2203435 2204843 := bstep (se 1 (by rfl) ⟨1653632, by rfl⟩ : syracuseStep 2204843 = 3307265) B3307265
theorem B5581021 : Blo 2203435 5581021 := bbase (se 3 (by rfl) ⟨1046441, by rfl⟩ : syracuseStep 5581021 = 2092883) (by norm_num)
theorem B7441361 : Blo 2203435 7441361 := bstep (se 2 (by rfl) ⟨2790510, by rfl⟩ : syracuseStep 7441361 = 5581021) B5581021
theorem B4960907 : Blo 2203435 4960907 := bstep (se 1 (by rfl) ⟨3720680, by rfl⟩ : syracuseStep 4960907 = 7441361) B7441361
theorem B3307271 : Blo 2203435 3307271 := bstep (se 1 (by rfl) ⟨2480453, by rfl⟩ : syracuseStep 3307271 = 4960907) B4960907
theorem B2204847 : Blo 2203435 2204847 := bstep (se 1 (by rfl) ⟨1653635, by rfl⟩ : syracuseStep 2204847 = 3307271) B3307271
theorem B3307277 : Blo 2203435 3307277 := bbase (se 3 (by rfl) ⟨620114, by rfl⟩ : syracuseStep 3307277 = 1240229) (by norm_num)
theorem B2204851 : Blo 2203435 2204851 := bstep (se 1 (by rfl) ⟨1653638, by rfl⟩ : syracuseStep 2204851 = 3307277) B3307277
theorem B4960925 : Blo 2203435 4960925 := bbase (se 3 (by rfl) ⟨930173, by rfl⟩ : syracuseStep 4960925 = 1860347) (by norm_num)
theorem B3307283 : Blo 2203435 3307283 := bstep (se 1 (by rfl) ⟨2480462, by rfl⟩ : syracuseStep 3307283 = 4960925) B4960925
theorem B2204855 : Blo 2203435 2204855 := bstep (se 1 (by rfl) ⟨1653641, by rfl⟩ : syracuseStep 2204855 = 3307283) B3307283
theorem B3720701 : Blo 2203435 3720701 := bbase (se 3 (by rfl) ⟨697631, by rfl⟩ : syracuseStep 3720701 = 1395263) (by norm_num)
theorem B2480467 : Blo 2203435 2480467 := bstep (se 1 (by rfl) ⟨1860350, by rfl⟩ : syracuseStep 2480467 = 3720701) B3720701
theorem B3307289 : Blo 2203435 3307289 := bstep (se 2 (by rfl) ⟨1240233, by rfl⟩ : syracuseStep 3307289 = 2480467) B2480467
theorem B2204859 : Blo 2203435 2204859 := bstep (se 1 (by rfl) ⟨1653644, by rfl⟩ : syracuseStep 2204859 = 3307289) B3307289
theorem B4709021 : Blo 2203435 4709021 := bbase (se 3 (by rfl) ⟨882941, by rfl⟩ : syracuseStep 4709021 = 1765883) (by norm_num)
theorem B12557389 : Blo 2203435 12557389 := bstep (se 3 (by rfl) ⟨2354510, by rfl⟩ : syracuseStep 12557389 = 4709021) B4709021
theorem B16743185 : Blo 2203435 16743185 := bstep (se 2 (by rfl) ⟨6278694, by rfl⟩ : syracuseStep 16743185 = 12557389) B12557389
theorem B11162123 : Blo 2203435 11162123 := bstep (se 1 (by rfl) ⟨8371592, by rfl⟩ : syracuseStep 11162123 = 16743185) B16743185
theorem B7441415 : Blo 2203435 7441415 := bstep (se 1 (by rfl) ⟨5581061, by rfl⟩ : syracuseStep 7441415 = 11162123) B11162123
theorem B4960943 : Blo 2203435 4960943 := bstep (se 1 (by rfl) ⟨3720707, by rfl⟩ : syracuseStep 4960943 = 7441415) B7441415
theorem B3307295 : Blo 2203435 3307295 := bstep (se 1 (by rfl) ⟨2480471, by rfl⟩ : syracuseStep 3307295 = 4960943) B4960943
theorem B2204863 : Blo 2203435 2204863 := bstep (se 1 (by rfl) ⟨1653647, by rfl⟩ : syracuseStep 2204863 = 3307295) B3307295
theorem B3307301 : Blo 2203435 3307301 := bbase (se 4 (by rfl) ⟨310059, by rfl⟩ : syracuseStep 3307301 = 620119) (by norm_num)
theorem B2204867 : Blo 2203435 2204867 := bstep (se 1 (by rfl) ⟨1653650, by rfl⟩ : syracuseStep 2204867 = 3307301) B3307301
theorem B2790541 : Blo 2203435 2790541 := bbase (se 3 (by rfl) ⟨523226, by rfl⟩ : syracuseStep 2790541 = 1046453) (by norm_num)
theorem B3720721 : Blo 2203435 3720721 := bstep (se 2 (by rfl) ⟨1395270, by rfl⟩ : syracuseStep 3720721 = 2790541) B2790541
theorem B4960961 : Blo 2203435 4960961 := bstep (se 2 (by rfl) ⟨1860360, by rfl⟩ : syracuseStep 4960961 = 3720721) B3720721
theorem B3307307 : Blo 2203435 3307307 := bstep (se 1 (by rfl) ⟨2480480, by rfl⟩ : syracuseStep 3307307 = 4960961) B4960961
theorem B2204871 : Blo 2203435 2204871 := bstep (se 1 (by rfl) ⟨1653653, by rfl⟩ : syracuseStep 2204871 = 3307307) B3307307
theorem B2480485 : Blo 2203435 2480485 := bbase (se 4 (by rfl) ⟨232545, by rfl⟩ : syracuseStep 2480485 = 465091) (by norm_num)
theorem B3307313 : Blo 2203435 3307313 := bstep (se 2 (by rfl) ⟨1240242, by rfl⟩ : syracuseStep 3307313 = 2480485) B2480485
theorem B2204875 : Blo 2203435 2204875 := bstep (se 1 (by rfl) ⟨1653656, by rfl⟩ : syracuseStep 2204875 = 3307313) B3307313
theorem B6278741 : Blo 2203435 6278741 := bbase (se 8 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 6278741 = 73579) (by norm_num)
theorem B4185827 : Blo 2203435 4185827 := bstep (se 1 (by rfl) ⟨3139370, by rfl⟩ : syracuseStep 4185827 = 6278741) B6278741
theorem B2790551 : Blo 2203435 2790551 := bstep (se 1 (by rfl) ⟨2092913, by rfl⟩ : syracuseStep 2790551 = 4185827) B4185827
theorem B7441469 : Blo 2203435 7441469 := bstep (se 3 (by rfl) ⟨1395275, by rfl⟩ : syracuseStep 7441469 = 2790551) B2790551
theorem B4960979 : Blo 2203435 4960979 := bstep (se 1 (by rfl) ⟨3720734, by rfl⟩ : syracuseStep 4960979 = 7441469) B7441469
theorem B3307319 : Blo 2203435 3307319 := bstep (se 1 (by rfl) ⟨2480489, by rfl⟩ : syracuseStep 3307319 = 4960979) B4960979
theorem B2204879 : Blo 2203435 2204879 := bstep (se 1 (by rfl) ⟨1653659, by rfl⟩ : syracuseStep 2204879 = 3307319) B3307319
theorem B3307325 : Blo 2203435 3307325 := bbase (se 3 (by rfl) ⟨620123, by rfl⟩ : syracuseStep 3307325 = 1240247) (by norm_num)
theorem B2204883 : Blo 2203435 2204883 := bstep (se 1 (by rfl) ⟨1653662, by rfl⟩ : syracuseStep 2204883 = 3307325) B3307325
theorem B4960997 : Blo 2203435 4960997 := bbase (se 4 (by rfl) ⟨465093, by rfl⟩ : syracuseStep 4960997 = 930187) (by norm_num)
theorem B3307331 : Blo 2203435 3307331 := bstep (se 1 (by rfl) ⟨2480498, by rfl⟩ : syracuseStep 3307331 = 4960997) B4960997
theorem B2204887 : Blo 2203435 2204887 := bstep (se 1 (by rfl) ⟨1653665, by rfl⟩ : syracuseStep 2204887 = 3307331) B3307331
theorem B5581133 : Blo 2203435 5581133 := bbase (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) (by norm_num)
theorem B3720755 : Blo 2203435 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B2480503 : Blo 2203435 2480503 := bstep (se 1 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 2480503 = 3720755) B3720755
theorem B3307337 : Blo 2203435 3307337 := bstep (se 2 (by rfl) ⟨1240251, by rfl⟩ : syracuseStep 3307337 = 2480503) B2480503
theorem B2204891 : Blo 2203435 2204891 := bstep (se 1 (by rfl) ⟨1653668, by rfl⟩ : syracuseStep 2204891 = 3307337) B3307337
theorem B2354545 : Blo 2203435 2354545 := bbase (se 2 (by rfl) ⟨882954, by rfl⟩ : syracuseStep 2354545 = 1765909) (by norm_num)
theorem B3139393 : Blo 2203435 3139393 := bstep (se 2 (by rfl) ⟨1177272, by rfl⟩ : syracuseStep 3139393 = 2354545) B2354545
theorem B4185857 : Blo 2203435 4185857 := bstep (se 2 (by rfl) ⟨1569696, by rfl⟩ : syracuseStep 4185857 = 3139393) B3139393
theorem B11162285 : Blo 2203435 11162285 := bstep (se 3 (by rfl) ⟨2092928, by rfl⟩ : syracuseStep 11162285 = 4185857) B4185857
theorem B7441523 : Blo 2203435 7441523 := bstep (se 1 (by rfl) ⟨5581142, by rfl⟩ : syracuseStep 7441523 = 11162285) B11162285
theorem B4961015 : Blo 2203435 4961015 := bstep (se 1 (by rfl) ⟨3720761, by rfl⟩ : syracuseStep 4961015 = 7441523) B7441523
theorem B3307343 : Blo 2203435 3307343 := bstep (se 1 (by rfl) ⟨2480507, by rfl⟩ : syracuseStep 3307343 = 4961015) B4961015
theorem B2204895 : Blo 2203435 2204895 := bstep (se 1 (by rfl) ⟨1653671, by rfl⟩ : syracuseStep 2204895 = 3307343) B3307343
theorem B3307349 : Blo 2203435 3307349 := bbase (se 9 (by rfl) ⟨9689, by rfl⟩ : syracuseStep 3307349 = 19379) (by norm_num)
theorem B2204899 : Blo 2203435 2204899 := bstep (se 1 (by rfl) ⟨1653674, by rfl⟩ : syracuseStep 2204899 = 3307349) B3307349
theorem B2648873 : Blo 2203435 2648873 := bbase (se 2 (by rfl) ⟨993327, by rfl⟩ : syracuseStep 2648873 = 1986655) (by norm_num)
theorem B7063661 : Blo 2203435 7063661 := bstep (se 3 (by rfl) ⟨1324436, by rfl⟩ : syracuseStep 7063661 = 2648873) B2648873
theorem B4709107 : Blo 2203435 4709107 := bstep (se 1 (by rfl) ⟨3531830, by rfl⟩ : syracuseStep 4709107 = 7063661) B7063661
theorem B6278809 : Blo 2203435 6278809 := bstep (se 2 (by rfl) ⟨2354553, by rfl⟩ : syracuseStep 6278809 = 4709107) B4709107
theorem B8371745 : Blo 2203435 8371745 := bstep (se 2 (by rfl) ⟨3139404, by rfl⟩ : syracuseStep 8371745 = 6278809) B6278809
theorem B5581163 : Blo 2203435 5581163 := bstep (se 1 (by rfl) ⟨4185872, by rfl⟩ : syracuseStep 5581163 = 8371745) B8371745
theorem B3720775 : Blo 2203435 3720775 := bstep (se 1 (by rfl) ⟨2790581, by rfl⟩ : syracuseStep 3720775 = 5581163) B5581163
theorem B4961033 : Blo 2203435 4961033 := bstep (se 2 (by rfl) ⟨1860387, by rfl⟩ : syracuseStep 4961033 = 3720775) B3720775
theorem B3307355 : Blo 2203435 3307355 := bstep (se 1 (by rfl) ⟨2480516, by rfl⟩ : syracuseStep 3307355 = 4961033) B4961033
theorem B2204903 : Blo 2203435 2204903 := bstep (se 1 (by rfl) ⟨1653677, by rfl⟩ : syracuseStep 2204903 = 3307355) B3307355
theorem B2480521 : Blo 2203435 2480521 := bbase (se 2 (by rfl) ⟨930195, by rfl⟩ : syracuseStep 2480521 = 1860391) (by norm_num)
theorem B3307361 : Blo 2203435 3307361 := bstep (se 2 (by rfl) ⟨1240260, by rfl⟩ : syracuseStep 3307361 = 2480521) B2480521
theorem B2204907 : Blo 2203435 2204907 := bstep (se 1 (by rfl) ⟨1653680, by rfl⟩ : syracuseStep 2204907 = 3307361) B3307361
theorem B4469989 : Blo 2203435 4469989 := bbase (se 4 (by rfl) ⟨419061, by rfl⟩ : syracuseStep 4469989 = 838123) (by norm_num)
theorem B5959985 : Blo 2203435 5959985 := bstep (se 2 (by rfl) ⟨2234994, by rfl⟩ : syracuseStep 5959985 = 4469989) B4469989
theorem B63573173 : Blo 2203435 63573173 := bstep (se 5 (by rfl) ⟨2979992, by rfl⟩ : syracuseStep 63573173 = 5959985) B5959985
theorem B42382115 : Blo 2203435 42382115 := bstep (se 1 (by rfl) ⟨31786586, by rfl⟩ : syracuseStep 42382115 = 63573173) B63573173
theorem B28254743 : Blo 2203435 28254743 := bstep (se 1 (by rfl) ⟨21191057, by rfl⟩ : syracuseStep 28254743 = 42382115) B42382115
theorem B18836495 : Blo 2203435 18836495 := bstep (se 1 (by rfl) ⟨14127371, by rfl⟩ : syracuseStep 18836495 = 28254743) B28254743
theorem B12557663 : Blo 2203435 12557663 := bstep (se 1 (by rfl) ⟨9418247, by rfl⟩ : syracuseStep 12557663 = 18836495) B18836495
theorem B8371775 : Blo 2203435 8371775 := bstep (se 1 (by rfl) ⟨6278831, by rfl⟩ : syracuseStep 8371775 = 12557663) B12557663
theorem B5581183 : Blo 2203435 5581183 := bstep (se 1 (by rfl) ⟨4185887, by rfl⟩ : syracuseStep 5581183 = 8371775) B8371775
theorem B7441577 : Blo 2203435 7441577 := bstep (se 2 (by rfl) ⟨2790591, by rfl⟩ : syracuseStep 7441577 = 5581183) B5581183
theorem B4961051 : Blo 2203435 4961051 := bstep (se 1 (by rfl) ⟨3720788, by rfl⟩ : syracuseStep 4961051 = 7441577) B7441577
theorem B3307367 : Blo 2203435 3307367 := bstep (se 1 (by rfl) ⟨2480525, by rfl⟩ : syracuseStep 3307367 = 4961051) B4961051
theorem B2204911 : Blo 2203435 2204911 := bstep (se 1 (by rfl) ⟨1653683, by rfl⟩ : syracuseStep 2204911 = 3307367) B3307367
theorem B3307373 : Blo 2203435 3307373 := bbase (se 3 (by rfl) ⟨620132, by rfl⟩ : syracuseStep 3307373 = 1240265) (by norm_num)
theorem B2204915 : Blo 2203435 2204915 := bstep (se 1 (by rfl) ⟨1653686, by rfl⟩ : syracuseStep 2204915 = 3307373) B3307373
theorem B4961069 : Blo 2203435 4961069 := bbase (se 3 (by rfl) ⟨930200, by rfl⟩ : syracuseStep 4961069 = 1860401) (by norm_num)
theorem B3307379 : Blo 2203435 3307379 := bstep (se 1 (by rfl) ⟨2480534, by rfl⟩ : syracuseStep 3307379 = 4961069) B4961069
theorem B2204919 : Blo 2203435 2204919 := bstep (se 1 (by rfl) ⟨1653689, by rfl⟩ : syracuseStep 2204919 = 3307379) B3307379
theorem B7946693 : Blo 2203435 7946693 := bbase (se 4 (by rfl) ⟨745002, by rfl⟩ : syracuseStep 7946693 = 1490005) (by norm_num)
theorem B5297795 : Blo 2203435 5297795 := bstep (se 1 (by rfl) ⟨3973346, by rfl⟩ : syracuseStep 5297795 = 7946693) B7946693
theorem B3531863 : Blo 2203435 3531863 := bstep (se 1 (by rfl) ⟨2648897, by rfl⟩ : syracuseStep 3531863 = 5297795) B5297795
theorem B9418301 : Blo 2203435 9418301 := bstep (se 3 (by rfl) ⟨1765931, by rfl⟩ : syracuseStep 9418301 = 3531863) B3531863
theorem B6278867 : Blo 2203435 6278867 := bstep (se 1 (by rfl) ⟨4709150, by rfl⟩ : syracuseStep 6278867 = 9418301) B9418301
theorem B4185911 : Blo 2203435 4185911 := bstep (se 1 (by rfl) ⟨3139433, by rfl⟩ : syracuseStep 4185911 = 6278867) B6278867
theorem B2790607 : Blo 2203435 2790607 := bstep (se 1 (by rfl) ⟨2092955, by rfl⟩ : syracuseStep 2790607 = 4185911) B4185911
theorem B3720809 : Blo 2203435 3720809 := bstep (se 2 (by rfl) ⟨1395303, by rfl⟩ : syracuseStep 3720809 = 2790607) B2790607
theorem B2480539 : Blo 2203435 2480539 := bstep (se 1 (by rfl) ⟨1860404, by rfl⟩ : syracuseStep 2480539 = 3720809) B3720809
theorem B3307385 : Blo 2203435 3307385 := bstep (se 2 (by rfl) ⟨1240269, by rfl⟩ : syracuseStep 3307385 = 2480539) B2480539
theorem B2204923 : Blo 2203435 2204923 := bstep (se 1 (by rfl) ⟨1653692, by rfl⟩ : syracuseStep 2204923 = 3307385) B3307385
theorem B10595605 : Blo 2203435 10595605 := bbase (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) (by norm_num)
theorem B14127473 : Blo 2203435 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B37673261 : Blo 2203435 37673261 := bstep (se 3 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 37673261 = 14127473) B14127473
theorem B25115507 : Blo 2203435 25115507 := bstep (se 1 (by rfl) ⟨18836630, by rfl⟩ : syracuseStep 25115507 = 37673261) B37673261
theorem B16743671 : Blo 2203435 16743671 := bstep (se 1 (by rfl) ⟨12557753, by rfl⟩ : syracuseStep 16743671 = 25115507) B25115507
theorem B11162447 : Blo 2203435 11162447 := bstep (se 1 (by rfl) ⟨8371835, by rfl⟩ : syracuseStep 11162447 = 16743671) B16743671
theorem B7441631 : Blo 2203435 7441631 := bstep (se 1 (by rfl) ⟨5581223, by rfl⟩ : syracuseStep 7441631 = 11162447) B11162447
theorem B4961087 : Blo 2203435 4961087 := bstep (se 1 (by rfl) ⟨3720815, by rfl⟩ : syracuseStep 4961087 = 7441631) B7441631
theorem B3307391 : Blo 2203435 3307391 := bstep (se 1 (by rfl) ⟨2480543, by rfl⟩ : syracuseStep 3307391 = 4961087) B4961087
theorem B2204927 : Blo 2203435 2204927 := bstep (se 1 (by rfl) ⟨1653695, by rfl⟩ : syracuseStep 2204927 = 3307391) B3307391
theorem B3307397 : Blo 2203435 3307397 := bbase (se 4 (by rfl) ⟨310068, by rfl⟩ : syracuseStep 3307397 = 620137) (by norm_num)
theorem B2204931 : Blo 2203435 2204931 := bstep (se 1 (by rfl) ⟨1653698, by rfl⟩ : syracuseStep 2204931 = 3307397) B3307397
theorem B3720829 : Blo 2203435 3720829 := bbase (se 3 (by rfl) ⟨697655, by rfl⟩ : syracuseStep 3720829 = 1395311) (by norm_num)
theorem B4961105 : Blo 2203435 4961105 := bstep (se 2 (by rfl) ⟨1860414, by rfl⟩ : syracuseStep 4961105 = 3720829) B3720829
theorem B3307403 : Blo 2203435 3307403 := bstep (se 1 (by rfl) ⟨2480552, by rfl⟩ : syracuseStep 3307403 = 4961105) B4961105
theorem B2204935 : Blo 2203435 2204935 := bstep (se 1 (by rfl) ⟨1653701, by rfl⟩ : syracuseStep 2204935 = 3307403) B3307403
theorem B2480557 : Blo 2203435 2480557 := bbase (se 3 (by rfl) ⟨465104, by rfl⟩ : syracuseStep 2480557 = 930209) (by norm_num)
theorem B3307409 : Blo 2203435 3307409 := bstep (se 2 (by rfl) ⟨1240278, by rfl⟩ : syracuseStep 3307409 = 2480557) B2480557
theorem B2204939 : Blo 2203435 2204939 := bstep (se 1 (by rfl) ⟨1653704, by rfl⟩ : syracuseStep 2204939 = 3307409) B3307409
theorem B7441685 : Blo 2203435 7441685 := bbase (se 6 (by rfl) ⟨174414, by rfl⟩ : syracuseStep 7441685 = 348829) (by norm_num)
theorem B4961123 : Blo 2203435 4961123 := bstep (se 1 (by rfl) ⟨3720842, by rfl⟩ : syracuseStep 4961123 = 7441685) B7441685
theorem B3307415 : Blo 2203435 3307415 := bstep (se 1 (by rfl) ⟨2480561, by rfl⟩ : syracuseStep 3307415 = 4961123) B4961123
theorem B2204943 : Blo 2203435 2204943 := bstep (se 1 (by rfl) ⟨1653707, by rfl⟩ : syracuseStep 2204943 = 3307415) B3307415
theorem B3307421 : Blo 2203435 3307421 := bbase (se 3 (by rfl) ⟨620141, by rfl⟩ : syracuseStep 3307421 = 1240283) (by norm_num)
theorem B2204947 : Blo 2203435 2204947 := bstep (se 1 (by rfl) ⟨1653710, by rfl⟩ : syracuseStep 2204947 = 3307421) B3307421
theorem B4961141 : Blo 2203435 4961141 := bbase (se 5 (by rfl) ⟨232553, by rfl⟩ : syracuseStep 4961141 = 465107) (by norm_num)
theorem B3307427 : Blo 2203435 3307427 := bstep (se 1 (by rfl) ⟨2480570, by rfl⟩ : syracuseStep 3307427 = 4961141) B4961141
theorem B2204951 : Blo 2203435 2204951 := bstep (se 1 (by rfl) ⟨1653713, by rfl⟩ : syracuseStep 2204951 = 3307427) B3307427
theorem B19093877 : Blo 2203435 19093877 := bbase (se 5 (by rfl) ⟨895025, by rfl⟩ : syracuseStep 19093877 = 1790051) (by norm_num)
theorem B12729251 : Blo 2203435 12729251 := bstep (se 1 (by rfl) ⟨9546938, by rfl⟩ : syracuseStep 12729251 = 19093877) B19093877
theorem B8486167 : Blo 2203435 8486167 := bstep (se 1 (by rfl) ⟨6364625, by rfl⟩ : syracuseStep 8486167 = 12729251) B12729251
theorem B11314889 : Blo 2203435 11314889 := bstep (se 2 (by rfl) ⟨4243083, by rfl⟩ : syracuseStep 11314889 = 8486167) B8486167
theorem B7543259 : Blo 2203435 7543259 := bstep (se 1 (by rfl) ⟨5657444, by rfl⟩ : syracuseStep 7543259 = 11314889) B11314889
theorem B5028839 : Blo 2203435 5028839 := bstep (se 1 (by rfl) ⟨3771629, by rfl⟩ : syracuseStep 5028839 = 7543259) B7543259
theorem B3352559 : Blo 2203435 3352559 := bstep (se 1 (by rfl) ⟨2514419, by rfl⟩ : syracuseStep 3352559 = 5028839) B5028839
theorem B35760629 : Blo 2203435 35760629 := bstep (se 5 (by rfl) ⟨1676279, by rfl⟩ : syracuseStep 35760629 = 3352559) B3352559
theorem B23840419 : Blo 2203435 23840419 := bstep (se 1 (by rfl) ⟨17880314, by rfl⟩ : syracuseStep 23840419 = 35760629) B35760629
theorem B31787225 : Blo 2203435 31787225 := bstep (se 2 (by rfl) ⟨11920209, by rfl⟩ : syracuseStep 31787225 = 23840419) B23840419
theorem B21191483 : Blo 2203435 21191483 := bstep (se 1 (by rfl) ⟨15893612, by rfl⟩ : syracuseStep 21191483 = 31787225) B31787225
theorem B14127655 : Blo 2203435 14127655 := bstep (se 1 (by rfl) ⟨10595741, by rfl⟩ : syracuseStep 14127655 = 21191483) B21191483
theorem B18836873 : Blo 2203435 18836873 := bstep (se 2 (by rfl) ⟨7063827, by rfl⟩ : syracuseStep 18836873 = 14127655) B14127655
theorem B12557915 : Blo 2203435 12557915 := bstep (se 1 (by rfl) ⟨9418436, by rfl⟩ : syracuseStep 12557915 = 18836873) B18836873
theorem B8371943 : Blo 2203435 8371943 := bstep (se 1 (by rfl) ⟨6278957, by rfl⟩ : syracuseStep 8371943 = 12557915) B12557915
theorem B5581295 : Blo 2203435 5581295 := bstep (se 1 (by rfl) ⟨4185971, by rfl⟩ : syracuseStep 5581295 = 8371943) B8371943
theorem B3720863 : Blo 2203435 3720863 := bstep (se 1 (by rfl) ⟨2790647, by rfl⟩ : syracuseStep 3720863 = 5581295) B5581295
theorem B2480575 : Blo 2203435 2480575 := bstep (se 1 (by rfl) ⟨1860431, by rfl⟩ : syracuseStep 2480575 = 3720863) B3720863
theorem B3307433 : Blo 2203435 3307433 := bstep (se 2 (by rfl) ⟨1240287, by rfl⟩ : syracuseStep 3307433 = 2480575) B2480575
theorem B2204955 : Blo 2203435 2204955 := bstep (se 1 (by rfl) ⟨1653716, by rfl⟩ : syracuseStep 2204955 = 3307433) B3307433
theorem B8371957 : Blo 2203435 8371957 := bbase (se 5 (by rfl) ⟨392435, by rfl⟩ : syracuseStep 8371957 = 784871) (by norm_num)
theorem B11162609 : Blo 2203435 11162609 := bstep (se 2 (by rfl) ⟨4185978, by rfl⟩ : syracuseStep 11162609 = 8371957) B8371957
theorem B7441739 : Blo 2203435 7441739 := bstep (se 1 (by rfl) ⟨5581304, by rfl⟩ : syracuseStep 7441739 = 11162609) B11162609
theorem B4961159 : Blo 2203435 4961159 := bstep (se 1 (by rfl) ⟨3720869, by rfl⟩ : syracuseStep 4961159 = 7441739) B7441739
theorem B3307439 : Blo 2203435 3307439 := bstep (se 1 (by rfl) ⟨2480579, by rfl⟩ : syracuseStep 3307439 = 4961159) B4961159
theorem B2204959 : Blo 2203435 2204959 := bstep (se 1 (by rfl) ⟨1653719, by rfl⟩ : syracuseStep 2204959 = 3307439) B3307439
theorem B3307445 : Blo 2203435 3307445 := bbase (se 5 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 3307445 = 310073) (by norm_num)
theorem B2204963 : Blo 2203435 2204963 := bstep (se 1 (by rfl) ⟨1653722, by rfl⟩ : syracuseStep 2204963 = 3307445) B3307445
theorem B5581325 : Blo 2203435 5581325 := bbase (se 3 (by rfl) ⟨1046498, by rfl⟩ : syracuseStep 5581325 = 2092997) (by norm_num)
theorem B3720883 : Blo 2203435 3720883 := bstep (se 1 (by rfl) ⟨2790662, by rfl⟩ : syracuseStep 3720883 = 5581325) B5581325
theorem B4961177 : Blo 2203435 4961177 := bstep (se 2 (by rfl) ⟨1860441, by rfl⟩ : syracuseStep 4961177 = 3720883) B3720883
theorem B3307451 : Blo 2203435 3307451 := bstep (se 1 (by rfl) ⟨2480588, by rfl⟩ : syracuseStep 3307451 = 4961177) B4961177
theorem B2204967 : Blo 2203435 2204967 := bstep (se 1 (by rfl) ⟨1653725, by rfl⟩ : syracuseStep 2204967 = 3307451) B3307451
theorem B2480593 : Blo 2203435 2480593 := bbase (se 2 (by rfl) ⟨930222, by rfl⟩ : syracuseStep 2480593 = 1860445) (by norm_num)
theorem B3307457 : Blo 2203435 3307457 := bstep (se 2 (by rfl) ⟨1240296, by rfl⟩ : syracuseStep 3307457 = 2480593) B2480593
theorem B2204971 : Blo 2203435 2204971 := bstep (se 1 (by rfl) ⟨1653728, by rfl⟩ : syracuseStep 2204971 = 3307457) B3307457
theorem B4709261 : Blo 2203435 4709261 := bbase (se 3 (by rfl) ⟨882986, by rfl⟩ : syracuseStep 4709261 = 1765973) (by norm_num)
theorem B3139507 : Blo 2203435 3139507 := bstep (se 1 (by rfl) ⟨2354630, by rfl⟩ : syracuseStep 3139507 = 4709261) B4709261
theorem B4186009 : Blo 2203435 4186009 := bstep (se 2 (by rfl) ⟨1569753, by rfl⟩ : syracuseStep 4186009 = 3139507) B3139507
theorem B5581345 : Blo 2203435 5581345 := bstep (se 2 (by rfl) ⟨2093004, by rfl⟩ : syracuseStep 5581345 = 4186009) B4186009
theorem B7441793 : Blo 2203435 7441793 := bstep (se 2 (by rfl) ⟨2790672, by rfl⟩ : syracuseStep 7441793 = 5581345) B5581345
theorem B4961195 : Blo 2203435 4961195 := bstep (se 1 (by rfl) ⟨3720896, by rfl⟩ : syracuseStep 4961195 = 7441793) B7441793
theorem B3307463 : Blo 2203435 3307463 := bstep (se 1 (by rfl) ⟨2480597, by rfl⟩ : syracuseStep 3307463 = 4961195) B4961195
theorem B2204975 : Blo 2203435 2204975 := bstep (se 1 (by rfl) ⟨1653731, by rfl⟩ : syracuseStep 2204975 = 3307463) B3307463
theorem B3307469 : Blo 2203435 3307469 := bbase (se 3 (by rfl) ⟨620150, by rfl⟩ : syracuseStep 3307469 = 1240301) (by norm_num)
theorem B2204979 : Blo 2203435 2204979 := bstep (se 1 (by rfl) ⟨1653734, by rfl⟩ : syracuseStep 2204979 = 3307469) B3307469
theorem B4961213 : Blo 2203435 4961213 := bbase (se 3 (by rfl) ⟨930227, by rfl⟩ : syracuseStep 4961213 = 1860455) (by norm_num)
theorem B3307475 : Blo 2203435 3307475 := bstep (se 1 (by rfl) ⟨2480606, by rfl⟩ : syracuseStep 3307475 = 4961213) B4961213
theorem B2204983 : Blo 2203435 2204983 := bstep (se 1 (by rfl) ⟨1653737, by rfl⟩ : syracuseStep 2204983 = 3307475) B3307475
theorem B3720917 : Blo 2203435 3720917 := bbase (se 7 (by rfl) ⟨43604, by rfl⟩ : syracuseStep 3720917 = 87209) (by norm_num)
theorem B2480611 : Blo 2203435 2480611 := bstep (se 1 (by rfl) ⟨1860458, by rfl⟩ : syracuseStep 2480611 = 3720917) B3720917
theorem B3307481 : Blo 2203435 3307481 := bstep (se 2 (by rfl) ⟨1240305, by rfl⟩ : syracuseStep 3307481 = 2480611) B2480611
theorem B2204987 : Blo 2203435 2204987 := bstep (se 1 (by rfl) ⟨1653740, by rfl⟩ : syracuseStep 2204987 = 3307481) B3307481
theorem B5297957 : Blo 2203435 5297957 := bbase (se 4 (by rfl) ⟨496683, by rfl⟩ : syracuseStep 5297957 = 993367) (by norm_num)
theorem B3531971 : Blo 2203435 3531971 := bstep (se 1 (by rfl) ⟨2648978, by rfl⟩ : syracuseStep 3531971 = 5297957) B5297957
theorem B9418589 : Blo 2203435 9418589 := bstep (se 3 (by rfl) ⟨1765985, by rfl⟩ : syracuseStep 9418589 = 3531971) B3531971
theorem B6279059 : Blo 2203435 6279059 := bstep (se 1 (by rfl) ⟨4709294, by rfl⟩ : syracuseStep 6279059 = 9418589) B9418589
theorem B16744157 : Blo 2203435 16744157 := bstep (se 3 (by rfl) ⟨3139529, by rfl⟩ : syracuseStep 16744157 = 6279059) B6279059
theorem B11162771 : Blo 2203435 11162771 := bstep (se 1 (by rfl) ⟨8372078, by rfl⟩ : syracuseStep 11162771 = 16744157) B16744157
theorem B7441847 : Blo 2203435 7441847 := bstep (se 1 (by rfl) ⟨5581385, by rfl⟩ : syracuseStep 7441847 = 11162771) B11162771
theorem B4961231 : Blo 2203435 4961231 := bstep (se 1 (by rfl) ⟨3720923, by rfl⟩ : syracuseStep 4961231 = 7441847) B7441847
theorem B3307487 : Blo 2203435 3307487 := bstep (se 1 (by rfl) ⟨2480615, by rfl⟩ : syracuseStep 3307487 = 4961231) B4961231
theorem B2204991 : Blo 2203435 2204991 := bstep (se 1 (by rfl) ⟨1653743, by rfl⟩ : syracuseStep 2204991 = 3307487) B3307487
theorem B3307493 : Blo 2203435 3307493 := bbase (se 4 (by rfl) ⟨310077, by rfl⟩ : syracuseStep 3307493 = 620155) (by norm_num)
theorem B2204995 : Blo 2203435 2204995 := bstep (se 1 (by rfl) ⟨1653746, by rfl⟩ : syracuseStep 2204995 = 3307493) B3307493
theorem B5028941 : Blo 2203435 5028941 := bbase (se 3 (by rfl) ⟨942926, by rfl⟩ : syracuseStep 5028941 = 1885853) (by norm_num)
theorem B3352627 : Blo 2203435 3352627 := bstep (se 1 (by rfl) ⟨2514470, by rfl⟩ : syracuseStep 3352627 = 5028941) B5028941
theorem B4470169 : Blo 2203435 4470169 := bstep (se 2 (by rfl) ⟨1676313, by rfl⟩ : syracuseStep 4470169 = 3352627) B3352627
theorem B5960225 : Blo 2203435 5960225 := bstep (se 2 (by rfl) ⟨2235084, by rfl⟩ : syracuseStep 5960225 = 4470169) B4470169
theorem B3973483 : Blo 2203435 3973483 := bstep (se 1 (by rfl) ⟨2980112, by rfl⟩ : syracuseStep 3973483 = 5960225) B5960225
theorem B5297977 : Blo 2203435 5297977 := bstep (se 2 (by rfl) ⟨1986741, by rfl⟩ : syracuseStep 5297977 = 3973483) B3973483
theorem B7063969 : Blo 2203435 7063969 := bstep (se 2 (by rfl) ⟨2648988, by rfl⟩ : syracuseStep 7063969 = 5297977) B5297977
theorem B9418625 : Blo 2203435 9418625 := bstep (se 2 (by rfl) ⟨3531984, by rfl⟩ : syracuseStep 9418625 = 7063969) B7063969
theorem B6279083 : Blo 2203435 6279083 := bstep (se 1 (by rfl) ⟨4709312, by rfl⟩ : syracuseStep 6279083 = 9418625) B9418625
theorem B4186055 : Blo 2203435 4186055 := bstep (se 1 (by rfl) ⟨3139541, by rfl⟩ : syracuseStep 4186055 = 6279083) B6279083
theorem B2790703 : Blo 2203435 2790703 := bstep (se 1 (by rfl) ⟨2093027, by rfl⟩ : syracuseStep 2790703 = 4186055) B4186055
theorem B3720937 : Blo 2203435 3720937 := bstep (se 2 (by rfl) ⟨1395351, by rfl⟩ : syracuseStep 3720937 = 2790703) B2790703
theorem B4961249 : Blo 2203435 4961249 := bstep (se 2 (by rfl) ⟨1860468, by rfl⟩ : syracuseStep 4961249 = 3720937) B3720937
theorem B3307499 : Blo 2203435 3307499 := bstep (se 1 (by rfl) ⟨2480624, by rfl⟩ : syracuseStep 3307499 = 4961249) B4961249
theorem B2204999 : Blo 2203435 2204999 := bstep (se 1 (by rfl) ⟨1653749, by rfl⟩ : syracuseStep 2204999 = 3307499) B3307499
theorem B2480629 : Blo 2203435 2480629 := bbase (se 5 (by rfl) ⟨116279, by rfl⟩ : syracuseStep 2480629 = 232559) (by norm_num)
theorem B3307505 : Blo 2203435 3307505 := bstep (se 2 (by rfl) ⟨1240314, by rfl⟩ : syracuseStep 3307505 = 2480629) B2480629
theorem B2205003 : Blo 2203435 2205003 := bstep (se 1 (by rfl) ⟨1653752, by rfl⟩ : syracuseStep 2205003 = 3307505) B3307505
theorem B2790713 : Blo 2203435 2790713 := bbase (se 2 (by rfl) ⟨1046517, by rfl⟩ : syracuseStep 2790713 = 2093035) (by norm_num)
theorem B7441901 : Blo 2203435 7441901 := bstep (se 3 (by rfl) ⟨1395356, by rfl⟩ : syracuseStep 7441901 = 2790713) B2790713
theorem B4961267 : Blo 2203435 4961267 := bstep (se 1 (by rfl) ⟨3720950, by rfl⟩ : syracuseStep 4961267 = 7441901) B7441901
theorem B3307511 : Blo 2203435 3307511 := bstep (se 1 (by rfl) ⟨2480633, by rfl⟩ : syracuseStep 3307511 = 4961267) B4961267
theorem B2205007 : Blo 2203435 2205007 := bstep (se 1 (by rfl) ⟨1653755, by rfl⟩ : syracuseStep 2205007 = 3307511) B3307511
theorem B3307517 : Blo 2203435 3307517 := bbase (se 3 (by rfl) ⟨620159, by rfl⟩ : syracuseStep 3307517 = 1240319) (by norm_num)
theorem B2205011 : Blo 2203435 2205011 := bstep (se 1 (by rfl) ⟨1653758, by rfl⟩ : syracuseStep 2205011 = 3307517) B3307517
theorem B4961285 : Blo 2203435 4961285 := bbase (se 4 (by rfl) ⟨465120, by rfl⟩ : syracuseStep 4961285 = 930241) (by norm_num)
theorem B3307523 : Blo 2203435 3307523 := bstep (se 1 (by rfl) ⟨2480642, by rfl⟩ : syracuseStep 3307523 = 4961285) B4961285
theorem B2205015 : Blo 2203435 2205015 := bstep (se 1 (by rfl) ⟨1653761, by rfl⟩ : syracuseStep 2205015 = 3307523) B3307523
theorem B4186093 : Blo 2203435 4186093 := bbase (se 3 (by rfl) ⟨784892, by rfl⟩ : syracuseStep 4186093 = 1569785) (by norm_num)
theorem B5581457 : Blo 2203435 5581457 := bstep (se 2 (by rfl) ⟨2093046, by rfl⟩ : syracuseStep 5581457 = 4186093) B4186093
theorem B3720971 : Blo 2203435 3720971 := bstep (se 1 (by rfl) ⟨2790728, by rfl⟩ : syracuseStep 3720971 = 5581457) B5581457
theorem B2480647 : Blo 2203435 2480647 := bstep (se 1 (by rfl) ⟨1860485, by rfl⟩ : syracuseStep 2480647 = 3720971) B3720971
theorem B3307529 : Blo 2203435 3307529 := bstep (se 2 (by rfl) ⟨1240323, by rfl⟩ : syracuseStep 3307529 = 2480647) B2480647
theorem B2205019 : Blo 2203435 2205019 := bstep (se 1 (by rfl) ⟨1653764, by rfl⟩ : syracuseStep 2205019 = 3307529) B3307529
theorem B11162933 : Blo 2203435 11162933 := bbase (se 5 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 11162933 = 1046525) (by norm_num)
theorem B7441955 : Blo 2203435 7441955 := bstep (se 1 (by rfl) ⟨5581466, by rfl⟩ : syracuseStep 7441955 = 11162933) B11162933
theorem B4961303 : Blo 2203435 4961303 := bstep (se 1 (by rfl) ⟨3720977, by rfl⟩ : syracuseStep 4961303 = 7441955) B7441955
theorem B3307535 : Blo 2203435 3307535 := bstep (se 1 (by rfl) ⟨2480651, by rfl⟩ : syracuseStep 3307535 = 4961303) B4961303
theorem B2205023 : Blo 2203435 2205023 := bstep (se 1 (by rfl) ⟨1653767, by rfl⟩ : syracuseStep 2205023 = 3307535) B3307535
theorem B3307541 : Blo 2203435 3307541 := bbase (se 6 (by rfl) ⟨77520, by rfl⟩ : syracuseStep 3307541 = 155041) (by norm_num)
theorem B2205027 : Blo 2203435 2205027 := bstep (se 1 (by rfl) ⟨1653770, by rfl⟩ : syracuseStep 2205027 = 3307541) B3307541
theorem B5298053 : Blo 2203435 5298053 := bbase (se 4 (by rfl) ⟨496692, by rfl⟩ : syracuseStep 5298053 = 993385) (by norm_num)
theorem B14128141 : Blo 2203435 14128141 := bstep (se 3 (by rfl) ⟨2649026, by rfl⟩ : syracuseStep 14128141 = 5298053) B5298053
theorem B18837521 : Blo 2203435 18837521 := bstep (se 2 (by rfl) ⟨7064070, by rfl⟩ : syracuseStep 18837521 = 14128141) B14128141
theorem B12558347 : Blo 2203435 12558347 := bstep (se 1 (by rfl) ⟨9418760, by rfl⟩ : syracuseStep 12558347 = 18837521) B18837521
theorem B8372231 : Blo 2203435 8372231 := bstep (se 1 (by rfl) ⟨6279173, by rfl⟩ : syracuseStep 8372231 = 12558347) B12558347
theorem B5581487 : Blo 2203435 5581487 := bstep (se 1 (by rfl) ⟨4186115, by rfl⟩ : syracuseStep 5581487 = 8372231) B8372231
theorem B3720991 : Blo 2203435 3720991 := bstep (se 1 (by rfl) ⟨2790743, by rfl⟩ : syracuseStep 3720991 = 5581487) B5581487
theorem B4961321 : Blo 2203435 4961321 := bstep (se 2 (by rfl) ⟨1860495, by rfl⟩ : syracuseStep 4961321 = 3720991) B3720991
theorem B3307547 : Blo 2203435 3307547 := bstep (se 1 (by rfl) ⟨2480660, by rfl⟩ : syracuseStep 3307547 = 4961321) B4961321
theorem B2205031 : Blo 2203435 2205031 := bstep (se 1 (by rfl) ⟨1653773, by rfl⟩ : syracuseStep 2205031 = 3307547) B3307547
theorem B2480665 : Blo 2203435 2480665 := bbase (se 2 (by rfl) ⟨930249, by rfl⟩ : syracuseStep 2480665 = 1860499) (by norm_num)
theorem B3307553 : Blo 2203435 3307553 := bstep (se 2 (by rfl) ⟨1240332, by rfl⟩ : syracuseStep 3307553 = 2480665) B2480665
theorem B2205035 : Blo 2203435 2205035 := bstep (se 1 (by rfl) ⟨1653776, by rfl⟩ : syracuseStep 2205035 = 3307553) B3307553
theorem B8372261 : Blo 2203435 8372261 := bbase (se 4 (by rfl) ⟨784899, by rfl⟩ : syracuseStep 8372261 = 1569799) (by norm_num)
theorem B5581507 : Blo 2203435 5581507 := bstep (se 1 (by rfl) ⟨4186130, by rfl⟩ : syracuseStep 5581507 = 8372261) B8372261
theorem B7442009 : Blo 2203435 7442009 := bstep (se 2 (by rfl) ⟨2790753, by rfl⟩ : syracuseStep 7442009 = 5581507) B5581507
theorem B4961339 : Blo 2203435 4961339 := bstep (se 1 (by rfl) ⟨3721004, by rfl⟩ : syracuseStep 4961339 = 7442009) B7442009
theorem B3307559 : Blo 2203435 3307559 := bstep (se 1 (by rfl) ⟨2480669, by rfl⟩ : syracuseStep 3307559 = 4961339) B4961339
theorem B2205039 : Blo 2203435 2205039 := bstep (se 1 (by rfl) ⟨1653779, by rfl⟩ : syracuseStep 2205039 = 3307559) B3307559
theorem B3307565 : Blo 2203435 3307565 := bbase (se 3 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 3307565 = 1240337) (by norm_num)
theorem B2205043 : Blo 2203435 2205043 := bstep (se 1 (by rfl) ⟨1653782, by rfl⟩ : syracuseStep 2205043 = 3307565) B3307565
theorem B4961357 : Blo 2203435 4961357 := bbase (se 3 (by rfl) ⟨930254, by rfl⟩ : syracuseStep 4961357 = 1860509) (by norm_num)
theorem B3307571 : Blo 2203435 3307571 := bstep (se 1 (by rfl) ⟨2480678, by rfl⟩ : syracuseStep 3307571 = 4961357) B4961357
theorem B2205047 : Blo 2203435 2205047 := bstep (se 1 (by rfl) ⟨1653785, by rfl⟩ : syracuseStep 2205047 = 3307571) B3307571
theorem B2790769 : Blo 2203435 2790769 := bbase (se 2 (by rfl) ⟨1046538, by rfl⟩ : syracuseStep 2790769 = 2093077) (by norm_num)
theorem B3721025 : Blo 2203435 3721025 := bstep (se 2 (by rfl) ⟨1395384, by rfl⟩ : syracuseStep 3721025 = 2790769) B2790769
theorem B2480683 : Blo 2203435 2480683 := bstep (se 1 (by rfl) ⟨1860512, by rfl⟩ : syracuseStep 2480683 = 3721025) B3721025
theorem B3307577 : Blo 2203435 3307577 := bstep (se 2 (by rfl) ⟨1240341, by rfl⟩ : syracuseStep 3307577 = 2480683) B2480683
theorem B2205051 : Blo 2203435 2205051 := bstep (se 1 (by rfl) ⟨1653788, by rfl⟩ : syracuseStep 2205051 = 3307577) B3307577
theorem B5657701 : Blo 2203435 5657701 := bbase (se 4 (by rfl) ⟨530409, by rfl⟩ : syracuseStep 5657701 = 1060819) (by norm_num)
theorem B7543601 : Blo 2203435 7543601 := bstep (se 2 (by rfl) ⟨2828850, by rfl⟩ : syracuseStep 7543601 = 5657701) B5657701
theorem B5029067 : Blo 2203435 5029067 := bstep (se 1 (by rfl) ⟨3771800, by rfl⟩ : syracuseStep 5029067 = 7543601) B7543601
theorem B13410845 : Blo 2203435 13410845 := bstep (se 3 (by rfl) ⟨2514533, by rfl⟩ : syracuseStep 13410845 = 5029067) B5029067
theorem B8940563 : Blo 2203435 8940563 := bstep (se 1 (by rfl) ⟨6705422, by rfl⟩ : syracuseStep 8940563 = 13410845) B13410845
theorem B5960375 : Blo 2203435 5960375 := bstep (se 1 (by rfl) ⟨4470281, by rfl⟩ : syracuseStep 5960375 = 8940563) B8940563
theorem B3973583 : Blo 2203435 3973583 := bstep (se 1 (by rfl) ⟨2980187, by rfl⟩ : syracuseStep 3973583 = 5960375) B5960375
theorem B10596221 : Blo 2203435 10596221 := bstep (se 3 (by rfl) ⟨1986791, by rfl⟩ : syracuseStep 10596221 = 3973583) B3973583
theorem B7064147 : Blo 2203435 7064147 := bstep (se 1 (by rfl) ⟨5298110, by rfl⟩ : syracuseStep 7064147 = 10596221) B10596221
theorem B4709431 : Blo 2203435 4709431 := bstep (se 1 (by rfl) ⟨3532073, by rfl⟩ : syracuseStep 4709431 = 7064147) B7064147
theorem B25116965 : Blo 2203435 25116965 := bstep (se 4 (by rfl) ⟨2354715, by rfl⟩ : syracuseStep 25116965 = 4709431) B4709431
theorem B16744643 : Blo 2203435 16744643 := bstep (se 1 (by rfl) ⟨12558482, by rfl⟩ : syracuseStep 16744643 = 25116965) B25116965
theorem B11163095 : Blo 2203435 11163095 := bstep (se 1 (by rfl) ⟨8372321, by rfl⟩ : syracuseStep 11163095 = 16744643) B16744643
theorem B7442063 : Blo 2203435 7442063 := bstep (se 1 (by rfl) ⟨5581547, by rfl⟩ : syracuseStep 7442063 = 11163095) B11163095
theorem B4961375 : Blo 2203435 4961375 := bstep (se 1 (by rfl) ⟨3721031, by rfl⟩ : syracuseStep 4961375 = 7442063) B7442063
theorem B3307583 : Blo 2203435 3307583 := bstep (se 1 (by rfl) ⟨2480687, by rfl⟩ : syracuseStep 3307583 = 4961375) B4961375
theorem B2205055 : Blo 2203435 2205055 := bstep (se 1 (by rfl) ⟨1653791, by rfl⟩ : syracuseStep 2205055 = 3307583) B3307583
theorem B3307589 : Blo 2203435 3307589 := bbase (se 4 (by rfl) ⟨310086, by rfl⟩ : syracuseStep 3307589 = 620173) (by norm_num)
theorem B2205059 : Blo 2203435 2205059 := bstep (se 1 (by rfl) ⟨1653794, by rfl⟩ : syracuseStep 2205059 = 3307589) B3307589
theorem B3721045 : Blo 2203435 3721045 := bbase (se 9 (by rfl) ⟨10901, by rfl⟩ : syracuseStep 3721045 = 21803) (by norm_num)
theorem B4961393 : Blo 2203435 4961393 := bstep (se 2 (by rfl) ⟨1860522, by rfl⟩ : syracuseStep 4961393 = 3721045) B3721045
theorem B3307595 : Blo 2203435 3307595 := bstep (se 1 (by rfl) ⟨2480696, by rfl⟩ : syracuseStep 3307595 = 4961393) B4961393
theorem B2205063 : Blo 2203435 2205063 := bstep (se 1 (by rfl) ⟨1653797, by rfl⟩ : syracuseStep 2205063 = 3307595) B3307595
theorem B2480701 : Blo 2203435 2480701 := bbase (se 3 (by rfl) ⟨465131, by rfl⟩ : syracuseStep 2480701 = 930263) (by norm_num)
theorem B3307601 : Blo 2203435 3307601 := bstep (se 2 (by rfl) ⟨1240350, by rfl⟩ : syracuseStep 3307601 = 2480701) B2480701
theorem B2205067 : Blo 2203435 2205067 := bstep (se 1 (by rfl) ⟨1653800, by rfl⟩ : syracuseStep 2205067 = 3307601) B3307601
theorem B7442117 : Blo 2203435 7442117 := bbase (se 4 (by rfl) ⟨697698, by rfl⟩ : syracuseStep 7442117 = 1395397) (by norm_num)
theorem B4961411 : Blo 2203435 4961411 := bstep (se 1 (by rfl) ⟨3721058, by rfl⟩ : syracuseStep 4961411 = 7442117) B7442117
theorem B3307607 : Blo 2203435 3307607 := bstep (se 1 (by rfl) ⟨2480705, by rfl⟩ : syracuseStep 3307607 = 4961411) B4961411
theorem B2205071 : Blo 2203435 2205071 := bstep (se 1 (by rfl) ⟨1653803, by rfl⟩ : syracuseStep 2205071 = 3307607) B3307607
theorem B3307613 : Blo 2203435 3307613 := bbase (se 3 (by rfl) ⟨620177, by rfl⟩ : syracuseStep 3307613 = 1240355) (by norm_num)
theorem B2205075 : Blo 2203435 2205075 := bstep (se 1 (by rfl) ⟨1653806, by rfl⟩ : syracuseStep 2205075 = 3307613) B3307613
theorem B4961429 : Blo 2203435 4961429 := bbase (se 6 (by rfl) ⟨116283, by rfl⟩ : syracuseStep 4961429 = 232567) (by norm_num)
theorem B3307619 : Blo 2203435 3307619 := bstep (se 1 (by rfl) ⟨2480714, by rfl⟩ : syracuseStep 3307619 = 4961429) B4961429
theorem B2205079 : Blo 2203435 2205079 := bstep (se 1 (by rfl) ⟨1653809, by rfl⟩ : syracuseStep 2205079 = 3307619) B3307619
theorem B3139661 : Blo 2203435 3139661 := bbase (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) (by norm_num)
theorem B8372429 : Blo 2203435 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B5581619 : Blo 2203435 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B3721079 : Blo 2203435 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B2480719 : Blo 2203435 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B3307625 : Blo 2203435 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B2205083 : Blo 2203435 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B2235173 : Blo 2203435 2235173 := bbase (se 4 (by rfl) ⟨209547, by rfl⟩ : syracuseStep 2235173 = 419095) (by norm_num)
theorem B5960461 : Blo 2203435 5960461 := bstep (se 3 (by rfl) ⟨1117586, by rfl⟩ : syracuseStep 5960461 = 2235173) B2235173
theorem B7947281 : Blo 2203435 7947281 := bstep (se 2 (by rfl) ⟨2980230, by rfl⟩ : syracuseStep 7947281 = 5960461) B5960461
theorem B21192749 : Blo 2203435 21192749 := bstep (se 3 (by rfl) ⟨3973640, by rfl⟩ : syracuseStep 21192749 = 7947281) B7947281
theorem B14128499 : Blo 2203435 14128499 := bstep (se 1 (by rfl) ⟨10596374, by rfl⟩ : syracuseStep 14128499 = 21192749) B21192749
theorem B9418999 : Blo 2203435 9418999 := bstep (se 1 (by rfl) ⟨7064249, by rfl⟩ : syracuseStep 9418999 = 14128499) B14128499
theorem B12558665 : Blo 2203435 12558665 := bstep (se 2 (by rfl) ⟨4709499, by rfl⟩ : syracuseStep 12558665 = 9418999) B9418999
theorem B8372443 : Blo 2203435 8372443 := bstep (se 1 (by rfl) ⟨6279332, by rfl⟩ : syracuseStep 8372443 = 12558665) B12558665
theorem B11163257 : Blo 2203435 11163257 := bstep (se 2 (by rfl) ⟨4186221, by rfl⟩ : syracuseStep 11163257 = 8372443) B8372443
theorem B7442171 : Blo 2203435 7442171 := bstep (se 1 (by rfl) ⟨5581628, by rfl⟩ : syracuseStep 7442171 = 11163257) B11163257
theorem B4961447 : Blo 2203435 4961447 := bstep (se 1 (by rfl) ⟨3721085, by rfl⟩ : syracuseStep 4961447 = 7442171) B7442171
theorem B3307631 : Blo 2203435 3307631 := bstep (se 1 (by rfl) ⟨2480723, by rfl⟩ : syracuseStep 3307631 = 4961447) B4961447
theorem B2205087 : Blo 2203435 2205087 := bstep (se 1 (by rfl) ⟨1653815, by rfl⟩ : syracuseStep 2205087 = 3307631) B3307631
theorem B3307637 : Blo 2203435 3307637 := bbase (se 5 (by rfl) ⟨155045, by rfl⟩ : syracuseStep 3307637 = 310091) (by norm_num)
theorem B2205091 : Blo 2203435 2205091 := bstep (se 1 (by rfl) ⟨1653818, by rfl⟩ : syracuseStep 2205091 = 3307637) B3307637
theorem B4186237 : Blo 2203435 4186237 := bbase (se 3 (by rfl) ⟨784919, by rfl⟩ : syracuseStep 4186237 = 1569839) (by norm_num)
theorem B5581649 : Blo 2203435 5581649 := bstep (se 2 (by rfl) ⟨2093118, by rfl⟩ : syracuseStep 5581649 = 4186237) B4186237
theorem B3721099 : Blo 2203435 3721099 := bstep (se 1 (by rfl) ⟨2790824, by rfl⟩ : syracuseStep 3721099 = 5581649) B5581649
theorem B4961465 : Blo 2203435 4961465 := bstep (se 2 (by rfl) ⟨1860549, by rfl⟩ : syracuseStep 4961465 = 3721099) B3721099
theorem B3307643 : Blo 2203435 3307643 := bstep (se 1 (by rfl) ⟨2480732, by rfl⟩ : syracuseStep 3307643 = 4961465) B4961465
theorem B2205095 : Blo 2203435 2205095 := bstep (se 1 (by rfl) ⟨1653821, by rfl⟩ : syracuseStep 2205095 = 3307643) B3307643
theorem B2480737 : Blo 2203435 2480737 := bbase (se 2 (by rfl) ⟨930276, by rfl⟩ : syracuseStep 2480737 = 1860553) (by norm_num)
theorem B3307649 : Blo 2203435 3307649 := bstep (se 2 (by rfl) ⟨1240368, by rfl⟩ : syracuseStep 3307649 = 2480737) B2480737
theorem B2205099 : Blo 2203435 2205099 := bstep (se 1 (by rfl) ⟨1653824, by rfl⟩ : syracuseStep 2205099 = 3307649) B3307649
theorem B5581669 : Blo 2203435 5581669 := bbase (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) (by norm_num)
theorem B7442225 : Blo 2203435 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B4961483 : Blo 2203435 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B3307655 : Blo 2203435 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B2205103 : Blo 2203435 2205103 := bstep (se 1 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 2205103 = 3307655) B3307655
theorem B3307661 : Blo 2203435 3307661 := bbase (se 3 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 3307661 = 1240373) (by norm_num)
theorem B2205107 : Blo 2203435 2205107 := bstep (se 1 (by rfl) ⟨1653830, by rfl⟩ : syracuseStep 2205107 = 3307661) B3307661
theorem B4961501 : Blo 2203435 4961501 := bbase (se 3 (by rfl) ⟨930281, by rfl⟩ : syracuseStep 4961501 = 1860563) (by norm_num)
theorem B3307667 : Blo 2203435 3307667 := bstep (se 1 (by rfl) ⟨2480750, by rfl⟩ : syracuseStep 3307667 = 4961501) B4961501
theorem B2205111 : Blo 2203435 2205111 := bstep (se 1 (by rfl) ⟨1653833, by rfl⟩ : syracuseStep 2205111 = 3307667) B3307667
theorem B3721133 : Blo 2203435 3721133 := bbase (se 3 (by rfl) ⟨697712, by rfl⟩ : syracuseStep 3721133 = 1395425) (by norm_num)
theorem B2480755 : Blo 2203435 2480755 := bstep (se 1 (by rfl) ⟨1860566, by rfl⟩ : syracuseStep 2480755 = 3721133) B3721133
theorem B3307673 : Blo 2203435 3307673 := bstep (se 2 (by rfl) ⟨1240377, by rfl⟩ : syracuseStep 3307673 = 2480755) B2480755
theorem B2205115 : Blo 2203435 2205115 := bstep (se 1 (by rfl) ⟨1653836, by rfl⟩ : syracuseStep 2205115 = 3307673) B3307673
theorem B2296613 : Blo 2203435 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B6124301 : Blo 2203435 6124301 := bstep (se 3 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 6124301 = 2296613) B2296613
theorem B4082867 : Blo 2203435 4082867 := bstep (se 1 (by rfl) ⟨3062150, by rfl⟩ : syracuseStep 4082867 = 6124301) B6124301
theorem B2721911 : Blo 2203435 2721911 := bstep (se 1 (by rfl) ⟨2041433, by rfl⟩ : syracuseStep 2721911 = 4082867) B4082867
theorem B7258429 : Blo 2203435 7258429 := bstep (se 3 (by rfl) ⟨1360955, by rfl⟩ : syracuseStep 7258429 = 2721911) B2721911
theorem B9677905 : Blo 2203435 9677905 := bstep (se 2 (by rfl) ⟨3629214, by rfl⟩ : syracuseStep 9677905 = 7258429) B7258429
theorem B206461973 : Blo 2203435 206461973 := bstep (se 6 (by rfl) ⟨4838952, by rfl⟩ : syracuseStep 206461973 = 9677905) B9677905
theorem B137641315 : Blo 2203435 137641315 := bstep (se 1 (by rfl) ⟨103230986, by rfl⟩ : syracuseStep 137641315 = 206461973) B206461973
theorem B183521753 : Blo 2203435 183521753 := bstep (se 2 (by rfl) ⟨68820657, by rfl⟩ : syracuseStep 183521753 = 137641315) B137641315
theorem B122347835 : Blo 2203435 122347835 := bstep (se 1 (by rfl) ⟨91760876, by rfl⟩ : syracuseStep 122347835 = 183521753) B183521753
theorem B81565223 : Blo 2203435 81565223 := bstep (se 1 (by rfl) ⟨61173917, by rfl⟩ : syracuseStep 81565223 = 122347835) B122347835
theorem B870029045 : Blo 2203435 870029045 := bstep (se 5 (by rfl) ⟨40782611, by rfl⟩ : syracuseStep 870029045 = 81565223) B81565223
theorem B580019363 : Blo 2203435 580019363 := bstep (se 1 (by rfl) ⟨435014522, by rfl⟩ : syracuseStep 580019363 = 870029045) B870029045
theorem B386679575 : Blo 2203435 386679575 := bstep (se 1 (by rfl) ⟨290009681, by rfl⟩ : syracuseStep 386679575 = 580019363) B580019363
theorem B257786383 : Blo 2203435 257786383 := bstep (se 1 (by rfl) ⟨193339787, by rfl⟩ : syracuseStep 257786383 = 386679575) B386679575
theorem B343715177 : Blo 2203435 343715177 := bstep (se 2 (by rfl) ⟨128893191, by rfl⟩ : syracuseStep 343715177 = 257786383) B257786383
theorem B916573805 : Blo 2203435 916573805 := bstep (se 3 (by rfl) ⟨171857588, by rfl⟩ : syracuseStep 916573805 = 343715177) B343715177
theorem B611049203 : Blo 2203435 611049203 := bstep (se 1 (by rfl) ⟨458286902, by rfl⟩ : syracuseStep 611049203 = 916573805) B916573805
theorem B407366135 : Blo 2203435 407366135 := bstep (se 1 (by rfl) ⟨305524601, by rfl⟩ : syracuseStep 407366135 = 611049203) B611049203
theorem B271577423 : Blo 2203435 271577423 := bstep (se 1 (by rfl) ⟨203683067, by rfl⟩ : syracuseStep 271577423 = 407366135) B407366135
theorem B181051615 : Blo 2203435 181051615 := bstep (se 1 (by rfl) ⟨135788711, by rfl⟩ : syracuseStep 181051615 = 271577423) B271577423
theorem B241402153 : Blo 2203435 241402153 := bstep (se 2 (by rfl) ⟨90525807, by rfl⟩ : syracuseStep 241402153 = 181051615) B181051615
theorem B321869537 : Blo 2203435 321869537 := bstep (se 2 (by rfl) ⟨120701076, by rfl⟩ : syracuseStep 321869537 = 241402153) B241402153
theorem B214579691 : Blo 2203435 214579691 := bstep (se 1 (by rfl) ⟨160934768, by rfl⟩ : syracuseStep 214579691 = 321869537) B321869537
theorem B143053127 : Blo 2203435 143053127 := bstep (se 1 (by rfl) ⟨107289845, by rfl⟩ : syracuseStep 143053127 = 214579691) B214579691
theorem B95368751 : Blo 2203435 95368751 := bstep (se 1 (by rfl) ⟨71526563, by rfl⟩ : syracuseStep 95368751 = 143053127) B143053127
theorem B63579167 : Blo 2203435 63579167 := bstep (se 1 (by rfl) ⟨47684375, by rfl⟩ : syracuseStep 63579167 = 95368751) B95368751
theorem B42386111 : Blo 2203435 42386111 := bstep (se 1 (by rfl) ⟨31789583, by rfl⟩ : syracuseStep 42386111 = 63579167) B63579167
theorem B28257407 : Blo 2203435 28257407 := bstep (se 1 (by rfl) ⟨21193055, by rfl⟩ : syracuseStep 28257407 = 42386111) B42386111
theorem B18838271 : Blo 2203435 18838271 := bstep (se 1 (by rfl) ⟨14128703, by rfl⟩ : syracuseStep 18838271 = 28257407) B28257407
theorem B12558847 : Blo 2203435 12558847 := bstep (se 1 (by rfl) ⟨9419135, by rfl⟩ : syracuseStep 12558847 = 18838271) B18838271
theorem B16745129 : Blo 2203435 16745129 := bstep (se 2 (by rfl) ⟨6279423, by rfl⟩ : syracuseStep 16745129 = 12558847) B12558847
theorem B11163419 : Blo 2203435 11163419 := bstep (se 1 (by rfl) ⟨8372564, by rfl⟩ : syracuseStep 11163419 = 16745129) B16745129
theorem B7442279 : Blo 2203435 7442279 := bstep (se 1 (by rfl) ⟨5581709, by rfl⟩ : syracuseStep 7442279 = 11163419) B11163419
theorem B4961519 : Blo 2203435 4961519 := bstep (se 1 (by rfl) ⟨3721139, by rfl⟩ : syracuseStep 4961519 = 7442279) B7442279
theorem B3307679 : Blo 2203435 3307679 := bstep (se 1 (by rfl) ⟨2480759, by rfl⟩ : syracuseStep 3307679 = 4961519) B4961519
theorem B2205119 : Blo 2203435 2205119 := bstep (se 1 (by rfl) ⟨1653839, by rfl⟩ : syracuseStep 2205119 = 3307679) B3307679
theorem B3307685 : Blo 2203435 3307685 := bbase (se 4 (by rfl) ⟨310095, by rfl⟩ : syracuseStep 3307685 = 620191) (by norm_num)
theorem B2205123 : Blo 2203435 2205123 := bstep (se 1 (by rfl) ⟨1653842, by rfl⟩ : syracuseStep 2205123 = 3307685) B3307685
theorem B2790865 : Blo 2203435 2790865 := bbase (se 2 (by rfl) ⟨1046574, by rfl⟩ : syracuseStep 2790865 = 2093149) (by norm_num)
theorem B3721153 : Blo 2203435 3721153 := bstep (se 2 (by rfl) ⟨1395432, by rfl⟩ : syracuseStep 3721153 = 2790865) B2790865
theorem B4961537 : Blo 2203435 4961537 := bstep (se 2 (by rfl) ⟨1860576, by rfl⟩ : syracuseStep 4961537 = 3721153) B3721153
theorem B3307691 : Blo 2203435 3307691 := bstep (se 1 (by rfl) ⟨2480768, by rfl⟩ : syracuseStep 3307691 = 4961537) B4961537
theorem B2205127 : Blo 2203435 2205127 := bstep (se 1 (by rfl) ⟨1653845, by rfl⟩ : syracuseStep 2205127 = 3307691) B3307691
theorem B2480773 : Blo 2203435 2480773 := bbase (se 4 (by rfl) ⟨232572, by rfl⟩ : syracuseStep 2480773 = 465145) (by norm_num)
theorem B3307697 : Blo 2203435 3307697 := bstep (se 2 (by rfl) ⟨1240386, by rfl⟩ : syracuseStep 3307697 = 2480773) B2480773
theorem B2205131 : Blo 2203435 2205131 := bstep (se 1 (by rfl) ⟨1653848, by rfl⟩ : syracuseStep 2205131 = 3307697) B3307697
theorem B7064405 : Blo 2203435 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B4709603 : Blo 2203435 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B3139735 : Blo 2203435 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B4186313 : Blo 2203435 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B2790875 : Blo 2203435 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B7442333 : Blo 2203435 7442333 := bstep (se 3 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 7442333 = 2790875) B2790875
theorem B4961555 : Blo 2203435 4961555 := bstep (se 1 (by rfl) ⟨3721166, by rfl⟩ : syracuseStep 4961555 = 7442333) B7442333
theorem B3307703 : Blo 2203435 3307703 := bstep (se 1 (by rfl) ⟨2480777, by rfl⟩ : syracuseStep 3307703 = 4961555) B4961555
theorem B2205135 : Blo 2203435 2205135 := bstep (se 1 (by rfl) ⟨1653851, by rfl⟩ : syracuseStep 2205135 = 3307703) B3307703
theorem B3307709 : Blo 2203435 3307709 := bbase (se 3 (by rfl) ⟨620195, by rfl⟩ : syracuseStep 3307709 = 1240391) (by norm_num)
theorem B2205139 : Blo 2203435 2205139 := bstep (se 1 (by rfl) ⟨1653854, by rfl⟩ : syracuseStep 2205139 = 3307709) B3307709
theorem B4961573 : Blo 2203435 4961573 := bbase (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) (by norm_num)
theorem B3307715 : Blo 2203435 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B2205143 : Blo 2203435 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B5581781 : Blo 2203435 5581781 := bbase (se 7 (by rfl) ⟨65411, by rfl⟩ : syracuseStep 5581781 = 130823) (by norm_num)
theorem B3721187 : Blo 2203435 3721187 := bstep (se 1 (by rfl) ⟨2790890, by rfl⟩ : syracuseStep 3721187 = 5581781) B5581781
theorem B2480791 : Blo 2203435 2480791 := bstep (se 1 (by rfl) ⟨1860593, by rfl⟩ : syracuseStep 2480791 = 3721187) B3721187
theorem B3307721 : Blo 2203435 3307721 := bstep (se 2 (by rfl) ⟨1240395, by rfl⟩ : syracuseStep 3307721 = 2480791) B2480791
theorem B2205147 : Blo 2203435 2205147 := bstep (se 1 (by rfl) ⟨1653860, by rfl⟩ : syracuseStep 2205147 = 3307721) B3307721
theorem B11921269 : Blo 2203435 11921269 := bbase (se 5 (by rfl) ⟨558809, by rfl⟩ : syracuseStep 11921269 = 1117619) (by norm_num)
theorem B15895025 : Blo 2203435 15895025 := bstep (se 2 (by rfl) ⟨5960634, by rfl⟩ : syracuseStep 15895025 = 11921269) B11921269
theorem B10596683 : Blo 2203435 10596683 := bstep (se 1 (by rfl) ⟨7947512, by rfl⟩ : syracuseStep 10596683 = 15895025) B15895025
theorem B7064455 : Blo 2203435 7064455 := bstep (se 1 (by rfl) ⟨5298341, by rfl⟩ : syracuseStep 7064455 = 10596683) B10596683
theorem B9419273 : Blo 2203435 9419273 := bstep (se 2 (by rfl) ⟨3532227, by rfl⟩ : syracuseStep 9419273 = 7064455) B7064455
theorem B6279515 : Blo 2203435 6279515 := bstep (se 1 (by rfl) ⟨4709636, by rfl⟩ : syracuseStep 6279515 = 9419273) B9419273
theorem B4186343 : Blo 2203435 4186343 := bstep (se 1 (by rfl) ⟨3139757, by rfl⟩ : syracuseStep 4186343 = 6279515) B6279515
theorem B11163581 : Blo 2203435 11163581 := bstep (se 3 (by rfl) ⟨2093171, by rfl⟩ : syracuseStep 11163581 = 4186343) B4186343
theorem B7442387 : Blo 2203435 7442387 := bstep (se 1 (by rfl) ⟨5581790, by rfl⟩ : syracuseStep 7442387 = 11163581) B11163581
theorem B4961591 : Blo 2203435 4961591 := bstep (se 1 (by rfl) ⟨3721193, by rfl⟩ : syracuseStep 4961591 = 7442387) B7442387
theorem B3307727 : Blo 2203435 3307727 := bstep (se 1 (by rfl) ⟨2480795, by rfl⟩ : syracuseStep 3307727 = 4961591) B4961591
theorem B2205151 : Blo 2203435 2205151 := bstep (se 1 (by rfl) ⟨1653863, by rfl⟩ : syracuseStep 2205151 = 3307727) B3307727
theorem B3307733 : Blo 2203435 3307733 := bbase (se 7 (by rfl) ⟨38762, by rfl⟩ : syracuseStep 3307733 = 77525) (by norm_num)
theorem B2205155 : Blo 2203435 2205155 := bstep (se 1 (by rfl) ⟨1653866, by rfl⟩ : syracuseStep 2205155 = 3307733) B3307733
theorem B2649181 : Blo 2203435 2649181 := bbase (se 3 (by rfl) ⟨496721, by rfl⟩ : syracuseStep 2649181 = 993443) (by norm_num)
theorem B3532241 : Blo 2203435 3532241 := bstep (se 2 (by rfl) ⟨1324590, by rfl⟩ : syracuseStep 3532241 = 2649181) B2649181
theorem B2354827 : Blo 2203435 2354827 := bstep (se 1 (by rfl) ⟨1766120, by rfl⟩ : syracuseStep 2354827 = 3532241) B3532241
theorem B3139769 : Blo 2203435 3139769 := bstep (se 2 (by rfl) ⟨1177413, by rfl⟩ : syracuseStep 3139769 = 2354827) B2354827
theorem B8372717 : Blo 2203435 8372717 := bstep (se 3 (by rfl) ⟨1569884, by rfl⟩ : syracuseStep 8372717 = 3139769) B3139769
theorem B5581811 : Blo 2203435 5581811 := bstep (se 1 (by rfl) ⟨4186358, by rfl⟩ : syracuseStep 5581811 = 8372717) B8372717
theorem B3721207 : Blo 2203435 3721207 := bstep (se 1 (by rfl) ⟨2790905, by rfl⟩ : syracuseStep 3721207 = 5581811) B5581811
theorem B4961609 : Blo 2203435 4961609 := bstep (se 2 (by rfl) ⟨1860603, by rfl⟩ : syracuseStep 4961609 = 3721207) B3721207
theorem B3307739 : Blo 2203435 3307739 := bstep (se 1 (by rfl) ⟨2480804, by rfl⟩ : syracuseStep 3307739 = 4961609) B4961609
theorem B2205159 : Blo 2203435 2205159 := bstep (se 1 (by rfl) ⟨1653869, by rfl⟩ : syracuseStep 2205159 = 3307739) B3307739
theorem B2480809 : Blo 2203435 2480809 := bbase (se 2 (by rfl) ⟨930303, by rfl⟩ : syracuseStep 2480809 = 1860607) (by norm_num)
theorem B3307745 : Blo 2203435 3307745 := bstep (se 2 (by rfl) ⟨1240404, by rfl⟩ : syracuseStep 3307745 = 2480809) B2480809
theorem B2205163 : Blo 2203435 2205163 := bstep (se 1 (by rfl) ⟨1653872, by rfl⟩ : syracuseStep 2205163 = 3307745) B3307745
theorem B3532253 : Blo 2203435 3532253 := bbase (se 3 (by rfl) ⟨662297, by rfl⟩ : syracuseStep 3532253 = 1324595) (by norm_num)
theorem B9419341 : Blo 2203435 9419341 := bstep (se 3 (by rfl) ⟨1766126, by rfl⟩ : syracuseStep 9419341 = 3532253) B3532253
theorem B12559121 : Blo 2203435 12559121 := bstep (se 2 (by rfl) ⟨4709670, by rfl⟩ : syracuseStep 12559121 = 9419341) B9419341
theorem B8372747 : Blo 2203435 8372747 := bstep (se 1 (by rfl) ⟨6279560, by rfl⟩ : syracuseStep 8372747 = 12559121) B12559121
theorem B5581831 : Blo 2203435 5581831 := bstep (se 1 (by rfl) ⟨4186373, by rfl⟩ : syracuseStep 5581831 = 8372747) B8372747
theorem B7442441 : Blo 2203435 7442441 := bstep (se 2 (by rfl) ⟨2790915, by rfl⟩ : syracuseStep 7442441 = 5581831) B5581831
theorem B4961627 : Blo 2203435 4961627 := bstep (se 1 (by rfl) ⟨3721220, by rfl⟩ : syracuseStep 4961627 = 7442441) B7442441
theorem B3307751 : Blo 2203435 3307751 := bstep (se 1 (by rfl) ⟨2480813, by rfl⟩ : syracuseStep 3307751 = 4961627) B4961627
theorem B2205167 : Blo 2203435 2205167 := bstep (se 1 (by rfl) ⟨1653875, by rfl⟩ : syracuseStep 2205167 = 3307751) B3307751
theorem B3307757 : Blo 2203435 3307757 := bbase (se 3 (by rfl) ⟨620204, by rfl⟩ : syracuseStep 3307757 = 1240409) (by norm_num)
theorem B2205171 : Blo 2203435 2205171 := bstep (se 1 (by rfl) ⟨1653878, by rfl⟩ : syracuseStep 2205171 = 3307757) B3307757
theorem B4961645 : Blo 2203435 4961645 := bbase (se 3 (by rfl) ⟨930308, by rfl⟩ : syracuseStep 4961645 = 1860617) (by norm_num)
theorem B3307763 : Blo 2203435 3307763 := bstep (se 1 (by rfl) ⟨2480822, by rfl⟩ : syracuseStep 3307763 = 4961645) B4961645
theorem B2205175 : Blo 2203435 2205175 := bstep (se 1 (by rfl) ⟨1653881, by rfl⟩ : syracuseStep 2205175 = 3307763) B3307763
theorem B4186397 : Blo 2203435 4186397 := bbase (se 3 (by rfl) ⟨784949, by rfl⟩ : syracuseStep 4186397 = 1569899) (by norm_num)
theorem B2790931 : Blo 2203435 2790931 := bstep (se 1 (by rfl) ⟨2093198, by rfl⟩ : syracuseStep 2790931 = 4186397) B4186397
theorem B3721241 : Blo 2203435 3721241 := bstep (se 2 (by rfl) ⟨1395465, by rfl⟩ : syracuseStep 3721241 = 2790931) B2790931
theorem B2480827 : Blo 2203435 2480827 := bstep (se 1 (by rfl) ⟨1860620, by rfl⟩ : syracuseStep 2480827 = 3721241) B3721241
theorem B3307769 : Blo 2203435 3307769 := bstep (se 2 (by rfl) ⟨1240413, by rfl⟩ : syracuseStep 3307769 = 2480827) B2480827
theorem B2205179 : Blo 2203435 2205179 := bstep (se 1 (by rfl) ⟨1653884, by rfl⟩ : syracuseStep 2205179 = 3307769) B3307769
theorem B15895253 : Blo 2203435 15895253 := bbase (se 7 (by rfl) ⟨186272, by rfl⟩ : syracuseStep 15895253 = 372545) (by norm_num)
theorem B10596835 : Blo 2203435 10596835 := bstep (se 1 (by rfl) ⟨7947626, by rfl⟩ : syracuseStep 10596835 = 15895253) B15895253
theorem B56516453 : Blo 2203435 56516453 := bstep (se 4 (by rfl) ⟨5298417, by rfl⟩ : syracuseStep 56516453 = 10596835) B10596835
theorem B37677635 : Blo 2203435 37677635 := bstep (se 1 (by rfl) ⟨28258226, by rfl⟩ : syracuseStep 37677635 = 56516453) B56516453
theorem B25118423 : Blo 2203435 25118423 := bstep (se 1 (by rfl) ⟨18838817, by rfl⟩ : syracuseStep 25118423 = 37677635) B37677635
theorem B16745615 : Blo 2203435 16745615 := bstep (se 1 (by rfl) ⟨12559211, by rfl⟩ : syracuseStep 16745615 = 25118423) B25118423
theorem B11163743 : Blo 2203435 11163743 := bstep (se 1 (by rfl) ⟨8372807, by rfl⟩ : syracuseStep 11163743 = 16745615) B16745615
theorem B7442495 : Blo 2203435 7442495 := bstep (se 1 (by rfl) ⟨5581871, by rfl⟩ : syracuseStep 7442495 = 11163743) B11163743
theorem B4961663 : Blo 2203435 4961663 := bstep (se 1 (by rfl) ⟨3721247, by rfl⟩ : syracuseStep 4961663 = 7442495) B7442495
theorem B3307775 : Blo 2203435 3307775 := bstep (se 1 (by rfl) ⟨2480831, by rfl⟩ : syracuseStep 3307775 = 4961663) B4961663
theorem B2205183 : Blo 2203435 2205183 := bstep (se 1 (by rfl) ⟨1653887, by rfl⟩ : syracuseStep 2205183 = 3307775) B3307775
theorem B3307781 : Blo 2203435 3307781 := bbase (se 4 (by rfl) ⟨310104, by rfl⟩ : syracuseStep 3307781 = 620209) (by norm_num)
theorem B2205187 : Blo 2203435 2205187 := bstep (se 1 (by rfl) ⟨1653890, by rfl⟩ : syracuseStep 2205187 = 3307781) B3307781
theorem B3721261 : Blo 2203435 3721261 := bbase (se 3 (by rfl) ⟨697736, by rfl⟩ : syracuseStep 3721261 = 1395473) (by norm_num)
theorem B4961681 : Blo 2203435 4961681 := bstep (se 2 (by rfl) ⟨1860630, by rfl⟩ : syracuseStep 4961681 = 3721261) B3721261
theorem B3307787 : Blo 2203435 3307787 := bstep (se 1 (by rfl) ⟨2480840, by rfl⟩ : syracuseStep 3307787 = 4961681) B4961681
theorem B2205191 : Blo 2203435 2205191 := bstep (se 1 (by rfl) ⟨1653893, by rfl⟩ : syracuseStep 2205191 = 3307787) B3307787
theorem B2480845 : Blo 2203435 2480845 := bbase (se 3 (by rfl) ⟨465158, by rfl⟩ : syracuseStep 2480845 = 930317) (by norm_num)
theorem B3307793 : Blo 2203435 3307793 := bstep (se 2 (by rfl) ⟨1240422, by rfl⟩ : syracuseStep 3307793 = 2480845) B2480845
theorem B2205195 : Blo 2203435 2205195 := bstep (se 1 (by rfl) ⟨1653896, by rfl⟩ : syracuseStep 2205195 = 3307793) B3307793
theorem B7442549 : Blo 2203435 7442549 := bbase (se 5 (by rfl) ⟨348869, by rfl⟩ : syracuseStep 7442549 = 697739) (by norm_num)
theorem B4961699 : Blo 2203435 4961699 := bstep (se 1 (by rfl) ⟨3721274, by rfl⟩ : syracuseStep 4961699 = 7442549) B7442549
theorem B3307799 : Blo 2203435 3307799 := bstep (se 1 (by rfl) ⟨2480849, by rfl⟩ : syracuseStep 3307799 = 4961699) B4961699
theorem B2205199 : Blo 2203435 2205199 := bstep (se 1 (by rfl) ⟨1653899, by rfl⟩ : syracuseStep 2205199 = 3307799) B3307799
theorem B3307805 : Blo 2203435 3307805 := bbase (se 3 (by rfl) ⟨620213, by rfl⟩ : syracuseStep 3307805 = 1240427) (by norm_num)
theorem B2205203 : Blo 2203435 2205203 := bstep (se 1 (by rfl) ⟨1653902, by rfl⟩ : syracuseStep 2205203 = 3307805) B3307805
theorem B4961717 : Blo 2203435 4961717 := bbase (se 5 (by rfl) ⟨232580, by rfl⟩ : syracuseStep 4961717 = 465161) (by norm_num)
theorem B3307811 : Blo 2203435 3307811 := bstep (se 1 (by rfl) ⟨2480858, by rfl⟩ : syracuseStep 3307811 = 4961717) B4961717
theorem B2205207 : Blo 2203435 2205207 := bstep (se 1 (by rfl) ⟨1653905, by rfl⟩ : syracuseStep 2205207 = 3307811) B3307811
theorem B4709765 : Blo 2203435 4709765 := bbase (se 4 (by rfl) ⟨441540, by rfl⟩ : syracuseStep 4709765 = 883081) (by norm_num)
theorem B12559373 : Blo 2203435 12559373 := bstep (se 3 (by rfl) ⟨2354882, by rfl⟩ : syracuseStep 12559373 = 4709765) B4709765
theorem B8372915 : Blo 2203435 8372915 := bstep (se 1 (by rfl) ⟨6279686, by rfl⟩ : syracuseStep 8372915 = 12559373) B12559373
theorem B5581943 : Blo 2203435 5581943 := bstep (se 1 (by rfl) ⟨4186457, by rfl⟩ : syracuseStep 5581943 = 8372915) B8372915
theorem B3721295 : Blo 2203435 3721295 := bstep (se 1 (by rfl) ⟨2790971, by rfl⟩ : syracuseStep 3721295 = 5581943) B5581943
theorem B2480863 : Blo 2203435 2480863 := bstep (se 1 (by rfl) ⟨1860647, by rfl⟩ : syracuseStep 2480863 = 3721295) B3721295
theorem B3307817 : Blo 2203435 3307817 := bstep (se 2 (by rfl) ⟨1240431, by rfl⟩ : syracuseStep 3307817 = 2480863) B2480863
theorem B2205211 : Blo 2203435 2205211 := bstep (se 1 (by rfl) ⟨1653908, by rfl⟩ : syracuseStep 2205211 = 3307817) B3307817
theorem B4709773 : Blo 2203435 4709773 := bbase (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) (by norm_num)
theorem B6279697 : Blo 2203435 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B8372929 : Blo 2203435 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B11163905 : Blo 2203435 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B7442603 : Blo 2203435 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B4961735 : Blo 2203435 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B3307823 : Blo 2203435 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B2205215 : Blo 2203435 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B3307829 : Blo 2203435 3307829 := bbase (se 5 (by rfl) ⟨155054, by rfl⟩ : syracuseStep 3307829 = 310109) (by norm_num)
theorem B2205219 : Blo 2203435 2205219 := bstep (se 1 (by rfl) ⟨1653914, by rfl⟩ : syracuseStep 2205219 = 3307829) B3307829
theorem B5581973 : Blo 2203435 5581973 := bbase (se 6 (by rfl) ⟨130827, by rfl⟩ : syracuseStep 5581973 = 261655) (by norm_num)
theorem B3721315 : Blo 2203435 3721315 := bstep (se 1 (by rfl) ⟨2790986, by rfl⟩ : syracuseStep 3721315 = 5581973) B5581973
theorem B4961753 : Blo 2203435 4961753 := bstep (se 2 (by rfl) ⟨1860657, by rfl⟩ : syracuseStep 4961753 = 3721315) B3721315
theorem B3307835 : Blo 2203435 3307835 := bstep (se 1 (by rfl) ⟨2480876, by rfl⟩ : syracuseStep 3307835 = 4961753) B4961753
theorem B2205223 : Blo 2203435 2205223 := bstep (se 1 (by rfl) ⟨1653917, by rfl⟩ : syracuseStep 2205223 = 3307835) B3307835
theorem B2480881 : Blo 2203435 2480881 := bbase (se 2 (by rfl) ⟨930330, by rfl⟩ : syracuseStep 2480881 = 1860661) (by norm_num)
theorem B3307841 : Blo 2203435 3307841 := bstep (se 2 (by rfl) ⟨1240440, by rfl⟩ : syracuseStep 3307841 = 2480881) B2480881
theorem B2205227 : Blo 2203435 2205227 := bstep (se 1 (by rfl) ⟨1653920, by rfl⟩ : syracuseStep 2205227 = 3307841) B3307841
theorem B5029469 : Blo 2203435 5029469 := bbase (se 3 (by rfl) ⟨943025, by rfl⟩ : syracuseStep 5029469 = 1886051) (by norm_num)
theorem B3352979 : Blo 2203435 3352979 := bstep (se 1 (by rfl) ⟨2514734, by rfl⟩ : syracuseStep 3352979 = 5029469) B5029469
theorem B2235319 : Blo 2203435 2235319 := bstep (se 1 (by rfl) ⟨1676489, by rfl⟩ : syracuseStep 2235319 = 3352979) B3352979
theorem B47686805 : Blo 2203435 47686805 := bstep (se 6 (by rfl) ⟨1117659, by rfl⟩ : syracuseStep 47686805 = 2235319) B2235319
theorem B31791203 : Blo 2203435 31791203 := bstep (se 1 (by rfl) ⟨23843402, by rfl⟩ : syracuseStep 31791203 = 47686805) B47686805
theorem B21194135 : Blo 2203435 21194135 := bstep (se 1 (by rfl) ⟨15895601, by rfl⟩ : syracuseStep 21194135 = 31791203) B31791203
theorem B14129423 : Blo 2203435 14129423 := bstep (se 1 (by rfl) ⟨10597067, by rfl⟩ : syracuseStep 14129423 = 21194135) B21194135
theorem B9419615 : Blo 2203435 9419615 := bstep (se 1 (by rfl) ⟨7064711, by rfl⟩ : syracuseStep 9419615 = 14129423) B14129423
theorem B6279743 : Blo 2203435 6279743 := bstep (se 1 (by rfl) ⟨4709807, by rfl⟩ : syracuseStep 6279743 = 9419615) B9419615
theorem B4186495 : Blo 2203435 4186495 := bstep (se 1 (by rfl) ⟨3139871, by rfl⟩ : syracuseStep 4186495 = 6279743) B6279743
theorem B5581993 : Blo 2203435 5581993 := bstep (se 2 (by rfl) ⟨2093247, by rfl⟩ : syracuseStep 5581993 = 4186495) B4186495
theorem B7442657 : Blo 2203435 7442657 := bstep (se 2 (by rfl) ⟨2790996, by rfl⟩ : syracuseStep 7442657 = 5581993) B5581993
theorem B4961771 : Blo 2203435 4961771 := bstep (se 1 (by rfl) ⟨3721328, by rfl⟩ : syracuseStep 4961771 = 7442657) B7442657
theorem B3307847 : Blo 2203435 3307847 := bstep (se 1 (by rfl) ⟨2480885, by rfl⟩ : syracuseStep 3307847 = 4961771) B4961771
theorem B2205231 : Blo 2203435 2205231 := bstep (se 1 (by rfl) ⟨1653923, by rfl⟩ : syracuseStep 2205231 = 3307847) B3307847
theorem B3307853 : Blo 2203435 3307853 := bbase (se 3 (by rfl) ⟨620222, by rfl⟩ : syracuseStep 3307853 = 1240445) (by norm_num)
theorem B2205235 : Blo 2203435 2205235 := bstep (se 1 (by rfl) ⟨1653926, by rfl⟩ : syracuseStep 2205235 = 3307853) B3307853
theorem B4961789 : Blo 2203435 4961789 := bbase (se 3 (by rfl) ⟨930335, by rfl⟩ : syracuseStep 4961789 = 1860671) (by norm_num)
theorem B3307859 : Blo 2203435 3307859 := bstep (se 1 (by rfl) ⟨2480894, by rfl⟩ : syracuseStep 3307859 = 4961789) B4961789
theorem B2205239 : Blo 2203435 2205239 := bstep (se 1 (by rfl) ⟨1653929, by rfl⟩ : syracuseStep 2205239 = 3307859) B3307859
theorem B3721349 : Blo 2203435 3721349 := bbase (se 4 (by rfl) ⟨348876, by rfl⟩ : syracuseStep 3721349 = 697753) (by norm_num)
theorem B2480899 : Blo 2203435 2480899 := bstep (se 1 (by rfl) ⟨1860674, by rfl⟩ : syracuseStep 2480899 = 3721349) B3721349
theorem B3307865 : Blo 2203435 3307865 := bstep (se 2 (by rfl) ⟨1240449, by rfl⟩ : syracuseStep 3307865 = 2480899) B2480899
theorem B2205243 : Blo 2203435 2205243 := bstep (se 1 (by rfl) ⟨1653932, by rfl⟩ : syracuseStep 2205243 = 3307865) B3307865
theorem B16746101 : Blo 2203435 16746101 := bbase (se 5 (by rfl) ⟨784973, by rfl⟩ : syracuseStep 16746101 = 1569947) (by norm_num)
theorem B11164067 : Blo 2203435 11164067 := bstep (se 1 (by rfl) ⟨8373050, by rfl⟩ : syracuseStep 11164067 = 16746101) B16746101
theorem B7442711 : Blo 2203435 7442711 := bstep (se 1 (by rfl) ⟨5582033, by rfl⟩ : syracuseStep 7442711 = 11164067) B11164067
theorem B4961807 : Blo 2203435 4961807 := bstep (se 1 (by rfl) ⟨3721355, by rfl⟩ : syracuseStep 4961807 = 7442711) B7442711
theorem B3307871 : Blo 2203435 3307871 := bstep (se 1 (by rfl) ⟨2480903, by rfl⟩ : syracuseStep 3307871 = 4961807) B4961807
theorem B2205247 : Blo 2203435 2205247 := bstep (se 1 (by rfl) ⟨1653935, by rfl⟩ : syracuseStep 2205247 = 3307871) B3307871
theorem B3307877 : Blo 2203435 3307877 := bbase (se 4 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 3307877 = 620227) (by norm_num)
theorem B2205251 : Blo 2203435 2205251 := bstep (se 1 (by rfl) ⟨1653938, by rfl⟩ : syracuseStep 2205251 = 3307877) B3307877
theorem B4186541 : Blo 2203435 4186541 := bbase (se 3 (by rfl) ⟨784976, by rfl⟩ : syracuseStep 4186541 = 1569953) (by norm_num)
theorem B2791027 : Blo 2203435 2791027 := bstep (se 1 (by rfl) ⟨2093270, by rfl⟩ : syracuseStep 2791027 = 4186541) B4186541
theorem B3721369 : Blo 2203435 3721369 := bstep (se 2 (by rfl) ⟨1395513, by rfl⟩ : syracuseStep 3721369 = 2791027) B2791027
theorem B4961825 : Blo 2203435 4961825 := bstep (se 2 (by rfl) ⟨1860684, by rfl⟩ : syracuseStep 4961825 = 3721369) B3721369
theorem B3307883 : Blo 2203435 3307883 := bstep (se 1 (by rfl) ⟨2480912, by rfl⟩ : syracuseStep 3307883 = 4961825) B4961825
theorem B2205255 : Blo 2203435 2205255 := bstep (se 1 (by rfl) ⟨1653941, by rfl⟩ : syracuseStep 2205255 = 3307883) B3307883
theorem B2480917 : Blo 2203435 2480917 := bbase (se 6 (by rfl) ⟨58146, by rfl⟩ : syracuseStep 2480917 = 116293) (by norm_num)
theorem B3307889 : Blo 2203435 3307889 := bstep (se 2 (by rfl) ⟨1240458, by rfl⟩ : syracuseStep 3307889 = 2480917) B2480917
theorem B2205259 : Blo 2203435 2205259 := bstep (se 1 (by rfl) ⟨1653944, by rfl⟩ : syracuseStep 2205259 = 3307889) B3307889
theorem B2791037 : Blo 2203435 2791037 := bbase (se 3 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 2791037 = 1046639) (by norm_num)
theorem B7442765 : Blo 2203435 7442765 := bstep (se 3 (by rfl) ⟨1395518, by rfl⟩ : syracuseStep 7442765 = 2791037) B2791037
theorem B4961843 : Blo 2203435 4961843 := bstep (se 1 (by rfl) ⟨3721382, by rfl⟩ : syracuseStep 4961843 = 7442765) B7442765
theorem B3307895 : Blo 2203435 3307895 := bstep (se 1 (by rfl) ⟨2480921, by rfl⟩ : syracuseStep 3307895 = 4961843) B4961843
theorem B2205263 : Blo 2203435 2205263 := bstep (se 1 (by rfl) ⟨1653947, by rfl⟩ : syracuseStep 2205263 = 3307895) B3307895
theorem B3307901 : Blo 2203435 3307901 := bbase (se 3 (by rfl) ⟨620231, by rfl⟩ : syracuseStep 3307901 = 1240463) (by norm_num)
theorem B2205267 : Blo 2203435 2205267 := bstep (se 1 (by rfl) ⟨1653950, by rfl⟩ : syracuseStep 2205267 = 3307901) B3307901
theorem B4961861 : Blo 2203435 4961861 := bbase (se 4 (by rfl) ⟨465174, by rfl⟩ : syracuseStep 4961861 = 930349) (by norm_num)
theorem B3307907 : Blo 2203435 3307907 := bstep (se 1 (by rfl) ⟨2480930, by rfl⟩ : syracuseStep 3307907 = 4961861) B4961861
theorem B2205271 : Blo 2203435 2205271 := bstep (se 1 (by rfl) ⟨1653953, by rfl⟩ : syracuseStep 2205271 = 3307907) B3307907
theorem B3973981 : Blo 2203435 3973981 := bbase (se 3 (by rfl) ⟨745121, by rfl⟩ : syracuseStep 3973981 = 1490243) (by norm_num)
theorem B5298641 : Blo 2203435 5298641 := bstep (se 2 (by rfl) ⟨1986990, by rfl⟩ : syracuseStep 5298641 = 3973981) B3973981
theorem B3532427 : Blo 2203435 3532427 := bstep (se 1 (by rfl) ⟨2649320, by rfl⟩ : syracuseStep 3532427 = 5298641) B5298641
theorem B2354951 : Blo 2203435 2354951 := bstep (se 1 (by rfl) ⟨1766213, by rfl⟩ : syracuseStep 2354951 = 3532427) B3532427
theorem B6279869 : Blo 2203435 6279869 := bstep (se 3 (by rfl) ⟨1177475, by rfl⟩ : syracuseStep 6279869 = 2354951) B2354951
theorem B4186579 : Blo 2203435 4186579 := bstep (se 1 (by rfl) ⟨3139934, by rfl⟩ : syracuseStep 4186579 = 6279869) B6279869
theorem B5582105 : Blo 2203435 5582105 := bstep (se 2 (by rfl) ⟨2093289, by rfl⟩ : syracuseStep 5582105 = 4186579) B4186579
theorem B3721403 : Blo 2203435 3721403 := bstep (se 1 (by rfl) ⟨2791052, by rfl⟩ : syracuseStep 3721403 = 5582105) B5582105
theorem B2480935 : Blo 2203435 2480935 := bstep (se 1 (by rfl) ⟨1860701, by rfl⟩ : syracuseStep 2480935 = 3721403) B3721403
theorem B3307913 : Blo 2203435 3307913 := bstep (se 2 (by rfl) ⟨1240467, by rfl⟩ : syracuseStep 3307913 = 2480935) B2480935
theorem B2205275 : Blo 2203435 2205275 := bstep (se 1 (by rfl) ⟨1653956, by rfl⟩ : syracuseStep 2205275 = 3307913) B3307913
theorem B11164229 : Blo 2203435 11164229 := bbase (se 4 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 11164229 = 2093293) (by norm_num)
theorem B7442819 : Blo 2203435 7442819 := bstep (se 1 (by rfl) ⟨5582114, by rfl⟩ : syracuseStep 7442819 = 11164229) B11164229
theorem B4961879 : Blo 2203435 4961879 := bstep (se 1 (by rfl) ⟨3721409, by rfl⟩ : syracuseStep 4961879 = 7442819) B7442819
theorem B3307919 : Blo 2203435 3307919 := bstep (se 1 (by rfl) ⟨2480939, by rfl⟩ : syracuseStep 3307919 = 4961879) B4961879
theorem B2205279 : Blo 2203435 2205279 := bstep (se 1 (by rfl) ⟨1653959, by rfl⟩ : syracuseStep 2205279 = 3307919) B3307919
theorem B3307925 : Blo 2203435 3307925 := bbase (se 6 (by rfl) ⟨77529, by rfl⟩ : syracuseStep 3307925 = 155059) (by norm_num)
theorem B2205283 : Blo 2203435 2205283 := bstep (se 1 (by rfl) ⟨1653962, by rfl⟩ : syracuseStep 2205283 = 3307925) B3307925
theorem B11922005 : Blo 2203435 11922005 := bbase (se 8 (by rfl) ⟨69855, by rfl⟩ : syracuseStep 11922005 = 139711) (by norm_num)
theorem B7948003 : Blo 2203435 7948003 := bstep (se 1 (by rfl) ⟨5961002, by rfl⟩ : syracuseStep 7948003 = 11922005) B11922005
theorem B10597337 : Blo 2203435 10597337 := bstep (se 2 (by rfl) ⟨3974001, by rfl⟩ : syracuseStep 10597337 = 7948003) B7948003
theorem B7064891 : Blo 2203435 7064891 := bstep (se 1 (by rfl) ⟨5298668, by rfl⟩ : syracuseStep 7064891 = 10597337) B10597337
theorem B4709927 : Blo 2203435 4709927 := bstep (se 1 (by rfl) ⟨3532445, by rfl⟩ : syracuseStep 4709927 = 7064891) B7064891
theorem B12559805 : Blo 2203435 12559805 := bstep (se 3 (by rfl) ⟨2354963, by rfl⟩ : syracuseStep 12559805 = 4709927) B4709927
theorem B8373203 : Blo 2203435 8373203 := bstep (se 1 (by rfl) ⟨6279902, by rfl⟩ : syracuseStep 8373203 = 12559805) B12559805
theorem B5582135 : Blo 2203435 5582135 := bstep (se 1 (by rfl) ⟨4186601, by rfl⟩ : syracuseStep 5582135 = 8373203) B8373203
theorem B3721423 : Blo 2203435 3721423 := bstep (se 1 (by rfl) ⟨2791067, by rfl⟩ : syracuseStep 3721423 = 5582135) B5582135
theorem B4961897 : Blo 2203435 4961897 := bstep (se 2 (by rfl) ⟨1860711, by rfl⟩ : syracuseStep 4961897 = 3721423) B3721423
theorem B3307931 : Blo 2203435 3307931 := bstep (se 1 (by rfl) ⟨2480948, by rfl⟩ : syracuseStep 3307931 = 4961897) B4961897
theorem B2205287 : Blo 2203435 2205287 := bstep (se 1 (by rfl) ⟨1653965, by rfl⟩ : syracuseStep 2205287 = 3307931) B3307931
theorem B2480953 : Blo 2203435 2480953 := bbase (se 2 (by rfl) ⟨930357, by rfl⟩ : syracuseStep 2480953 = 1860715) (by norm_num)
theorem B3307937 : Blo 2203435 3307937 := bstep (se 2 (by rfl) ⟨1240476, by rfl⟩ : syracuseStep 3307937 = 2480953) B2480953
theorem B2205291 : Blo 2203435 2205291 := bstep (se 1 (by rfl) ⟨1653968, by rfl⟩ : syracuseStep 2205291 = 3307937) B3307937
theorem B6279925 : Blo 2203435 6279925 := bbase (se 5 (by rfl) ⟨294371, by rfl⟩ : syracuseStep 6279925 = 588743) (by norm_num)
theorem B8373233 : Blo 2203435 8373233 := bstep (se 2 (by rfl) ⟨3139962, by rfl⟩ : syracuseStep 8373233 = 6279925) B6279925
theorem B5582155 : Blo 2203435 5582155 := bstep (se 1 (by rfl) ⟨4186616, by rfl⟩ : syracuseStep 5582155 = 8373233) B8373233
theorem B7442873 : Blo 2203435 7442873 := bstep (se 2 (by rfl) ⟨2791077, by rfl⟩ : syracuseStep 7442873 = 5582155) B5582155
theorem B4961915 : Blo 2203435 4961915 := bstep (se 1 (by rfl) ⟨3721436, by rfl⟩ : syracuseStep 4961915 = 7442873) B7442873
theorem B3307943 : Blo 2203435 3307943 := bstep (se 1 (by rfl) ⟨2480957, by rfl⟩ : syracuseStep 3307943 = 4961915) B4961915
theorem B2205295 : Blo 2203435 2205295 := bstep (se 1 (by rfl) ⟨1653971, by rfl⟩ : syracuseStep 2205295 = 3307943) B3307943
theorem B3307949 : Blo 2203435 3307949 := bbase (se 3 (by rfl) ⟨620240, by rfl⟩ : syracuseStep 3307949 = 1240481) (by norm_num)
theorem B2205299 : Blo 2203435 2205299 := bstep (se 1 (by rfl) ⟨1653974, by rfl⟩ : syracuseStep 2205299 = 3307949) B3307949
theorem B4961933 : Blo 2203435 4961933 := bbase (se 3 (by rfl) ⟨930362, by rfl⟩ : syracuseStep 4961933 = 1860725) (by norm_num)
theorem B3307955 : Blo 2203435 3307955 := bstep (se 1 (by rfl) ⟨2480966, by rfl⟩ : syracuseStep 3307955 = 4961933) B4961933
theorem B2205303 : Blo 2203435 2205303 := bstep (se 1 (by rfl) ⟨1653977, by rfl⟩ : syracuseStep 2205303 = 3307955) B3307955
theorem B2791093 : Blo 2203435 2791093 := bbase (se 5 (by rfl) ⟨130832, by rfl⟩ : syracuseStep 2791093 = 261665) (by norm_num)
theorem B3721457 : Blo 2203435 3721457 := bstep (se 2 (by rfl) ⟨1395546, by rfl⟩ : syracuseStep 3721457 = 2791093) B2791093
theorem B2480971 : Blo 2203435 2480971 := bstep (se 1 (by rfl) ⟨1860728, by rfl⟩ : syracuseStep 2480971 = 3721457) B3721457
theorem B3307961 : Blo 2203435 3307961 := bstep (se 2 (by rfl) ⟨1240485, by rfl⟩ : syracuseStep 3307961 = 2480971) B2480971
theorem B2205307 : Blo 2203435 2205307 := bstep (se 1 (by rfl) ⟨1653980, by rfl⟩ : syracuseStep 2205307 = 3307961) B3307961
theorem B9187253 : Blo 2203435 9187253 := bbase (se 5 (by rfl) ⟨430652, by rfl⟩ : syracuseStep 9187253 = 861305) (by norm_num)
theorem B6124835 : Blo 2203435 6124835 := bstep (se 1 (by rfl) ⟨4593626, by rfl⟩ : syracuseStep 6124835 = 9187253) B9187253
theorem B16332893 : Blo 2203435 16332893 := bstep (se 3 (by rfl) ⟨3062417, by rfl⟩ : syracuseStep 16332893 = 6124835) B6124835
theorem B10888595 : Blo 2203435 10888595 := bstep (se 1 (by rfl) ⟨8166446, by rfl⟩ : syracuseStep 10888595 = 16332893) B16332893
theorem B7259063 : Blo 2203435 7259063 := bstep (se 1 (by rfl) ⟨5444297, by rfl⟩ : syracuseStep 7259063 = 10888595) B10888595
theorem B77430005 : Blo 2203435 77430005 := bstep (se 5 (by rfl) ⟨3629531, by rfl⟩ : syracuseStep 77430005 = 7259063) B7259063
theorem B51620003 : Blo 2203435 51620003 := bstep (se 1 (by rfl) ⟨38715002, by rfl⟩ : syracuseStep 51620003 = 77430005) B77430005
theorem B34413335 : Blo 2203435 34413335 := bstep (se 1 (by rfl) ⟨25810001, by rfl⟩ : syracuseStep 34413335 = 51620003) B51620003
theorem B22942223 : Blo 2203435 22942223 := bstep (se 1 (by rfl) ⟨17206667, by rfl⟩ : syracuseStep 22942223 = 34413335) B34413335
theorem B15294815 : Blo 2203435 15294815 := bstep (se 1 (by rfl) ⟨11471111, by rfl⟩ : syracuseStep 15294815 = 22942223) B22942223
theorem B10196543 : Blo 2203435 10196543 := bstep (se 1 (by rfl) ⟨7647407, by rfl⟩ : syracuseStep 10196543 = 15294815) B15294815
theorem B6797695 : Blo 2203435 6797695 := bstep (se 1 (by rfl) ⟨5098271, by rfl⟩ : syracuseStep 6797695 = 10196543) B10196543
theorem B9063593 : Blo 2203435 9063593 := bstep (se 2 (by rfl) ⟨3398847, by rfl⟩ : syracuseStep 9063593 = 6797695) B6797695
theorem B6042395 : Blo 2203435 6042395 := bstep (se 1 (by rfl) ⟨4531796, by rfl⟩ : syracuseStep 6042395 = 9063593) B9063593
theorem B16113053 : Blo 2203435 16113053 := bstep (se 3 (by rfl) ⟨3021197, by rfl⟩ : syracuseStep 16113053 = 6042395) B6042395
theorem B42968141 : Blo 2203435 42968141 := bstep (se 3 (by rfl) ⟨8056526, by rfl⟩ : syracuseStep 42968141 = 16113053) B16113053
theorem B28645427 : Blo 2203435 28645427 := bstep (se 1 (by rfl) ⟨21484070, by rfl⟩ : syracuseStep 28645427 = 42968141) B42968141
theorem B19096951 : Blo 2203435 19096951 := bstep (se 1 (by rfl) ⟨14322713, by rfl⟩ : syracuseStep 19096951 = 28645427) B28645427
theorem B25462601 : Blo 2203435 25462601 := bstep (se 2 (by rfl) ⟨9548475, by rfl⟩ : syracuseStep 25462601 = 19096951) B19096951
theorem B16975067 : Blo 2203435 16975067 := bstep (se 1 (by rfl) ⟨12731300, by rfl⟩ : syracuseStep 16975067 = 25462601) B25462601
theorem B45266845 : Blo 2203435 45266845 := bstep (se 3 (by rfl) ⟨8487533, by rfl⟩ : syracuseStep 45266845 = 16975067) B16975067
theorem B60355793 : Blo 2203435 60355793 := bstep (se 2 (by rfl) ⟨22633422, by rfl⟩ : syracuseStep 60355793 = 45266845) B45266845
theorem B160948781 : Blo 2203435 160948781 := bstep (se 3 (by rfl) ⟨30177896, by rfl⟩ : syracuseStep 160948781 = 60355793) B60355793
theorem B107299187 : Blo 2203435 107299187 := bstep (se 1 (by rfl) ⟨80474390, by rfl⟩ : syracuseStep 107299187 = 160948781) B160948781
theorem B71532791 : Blo 2203435 71532791 := bstep (se 1 (by rfl) ⟨53649593, by rfl⟩ : syracuseStep 71532791 = 107299187) B107299187
theorem B47688527 : Blo 2203435 47688527 := bstep (se 1 (by rfl) ⟨35766395, by rfl⟩ : syracuseStep 47688527 = 71532791) B71532791
theorem B31792351 : Blo 2203435 31792351 := bstep (se 1 (by rfl) ⟨23844263, by rfl⟩ : syracuseStep 31792351 = 47688527) B47688527
theorem B42389801 : Blo 2203435 42389801 := bstep (se 2 (by rfl) ⟨15896175, by rfl⟩ : syracuseStep 42389801 = 31792351) B31792351
theorem B28259867 : Blo 2203435 28259867 := bstep (se 1 (by rfl) ⟨21194900, by rfl⟩ : syracuseStep 28259867 = 42389801) B42389801
theorem B18839911 : Blo 2203435 18839911 := bstep (se 1 (by rfl) ⟨14129933, by rfl⟩ : syracuseStep 18839911 = 28259867) B28259867
theorem B25119881 : Blo 2203435 25119881 := bstep (se 2 (by rfl) ⟨9419955, by rfl⟩ : syracuseStep 25119881 = 18839911) B18839911
theorem B16746587 : Blo 2203435 16746587 := bstep (se 1 (by rfl) ⟨12559940, by rfl⟩ : syracuseStep 16746587 = 25119881) B25119881
theorem B11164391 : Blo 2203435 11164391 := bstep (se 1 (by rfl) ⟨8373293, by rfl⟩ : syracuseStep 11164391 = 16746587) B16746587
theorem B7442927 : Blo 2203435 7442927 := bstep (se 1 (by rfl) ⟨5582195, by rfl⟩ : syracuseStep 7442927 = 11164391) B11164391
theorem B4961951 : Blo 2203435 4961951 := bstep (se 1 (by rfl) ⟨3721463, by rfl⟩ : syracuseStep 4961951 = 7442927) B7442927
theorem B3307967 : Blo 2203435 3307967 := bstep (se 1 (by rfl) ⟨2480975, by rfl⟩ : syracuseStep 3307967 = 4961951) B4961951
theorem B2205311 : Blo 2203435 2205311 := bstep (se 1 (by rfl) ⟨1653983, by rfl⟩ : syracuseStep 2205311 = 3307967) B3307967
theorem B3307973 : Blo 2203435 3307973 := bbase (se 4 (by rfl) ⟨310122, by rfl⟩ : syracuseStep 3307973 = 620245) (by norm_num)
theorem B2205315 : Blo 2203435 2205315 := bstep (se 1 (by rfl) ⟨1653986, by rfl⟩ : syracuseStep 2205315 = 3307973) B3307973
theorem B3721477 : Blo 2203435 3721477 := bbase (se 4 (by rfl) ⟨348888, by rfl⟩ : syracuseStep 3721477 = 697777) (by norm_num)
theorem B4961969 : Blo 2203435 4961969 := bstep (se 2 (by rfl) ⟨1860738, by rfl⟩ : syracuseStep 4961969 = 3721477) B3721477
theorem B3307979 : Blo 2203435 3307979 := bstep (se 1 (by rfl) ⟨2480984, by rfl⟩ : syracuseStep 3307979 = 4961969) B4961969
theorem B2205319 : Blo 2203435 2205319 := bstep (se 1 (by rfl) ⟨1653989, by rfl⟩ : syracuseStep 2205319 = 3307979) B3307979
theorem B2480989 : Blo 2203435 2480989 := bbase (se 3 (by rfl) ⟨465185, by rfl⟩ : syracuseStep 2480989 = 930371) (by norm_num)
theorem B3307985 : Blo 2203435 3307985 := bstep (se 2 (by rfl) ⟨1240494, by rfl⟩ : syracuseStep 3307985 = 2480989) B2480989
theorem B2205323 : Blo 2203435 2205323 := bstep (se 1 (by rfl) ⟨1653992, by rfl⟩ : syracuseStep 2205323 = 3307985) B3307985
theorem B7442981 : Blo 2203435 7442981 := bbase (se 4 (by rfl) ⟨697779, by rfl⟩ : syracuseStep 7442981 = 1395559) (by norm_num)
theorem B4961987 : Blo 2203435 4961987 := bstep (se 1 (by rfl) ⟨3721490, by rfl⟩ : syracuseStep 4961987 = 7442981) B7442981
theorem B3307991 : Blo 2203435 3307991 := bstep (se 1 (by rfl) ⟨2480993, by rfl⟩ : syracuseStep 3307991 = 4961987) B4961987
theorem B2205327 : Blo 2203435 2205327 := bstep (se 1 (by rfl) ⟨1653995, by rfl⟩ : syracuseStep 2205327 = 3307991) B3307991
theorem B3307997 : Blo 2203435 3307997 := bbase (se 3 (by rfl) ⟨620249, by rfl⟩ : syracuseStep 3307997 = 1240499) (by norm_num)
theorem B2205331 : Blo 2203435 2205331 := bstep (se 1 (by rfl) ⟨1653998, by rfl⟩ : syracuseStep 2205331 = 3307997) B3307997
theorem B4962005 : Blo 2203435 4962005 := bbase (se 7 (by rfl) ⟨58148, by rfl⟩ : syracuseStep 4962005 = 116297) (by norm_num)
theorem B3308003 : Blo 2203435 3308003 := bstep (se 1 (by rfl) ⟨2481002, by rfl⟩ : syracuseStep 3308003 = 4962005) B4962005
theorem B2205335 : Blo 2203435 2205335 := bstep (se 1 (by rfl) ⟨1654001, by rfl⟩ : syracuseStep 2205335 = 3308003) B3308003
theorem B2649397 : Blo 2203435 2649397 := bbase (se 5 (by rfl) ⟨124190, by rfl⟩ : syracuseStep 2649397 = 248381) (by norm_num)
theorem B3532529 : Blo 2203435 3532529 := bstep (se 2 (by rfl) ⟨1324698, by rfl⟩ : syracuseStep 3532529 = 2649397) B2649397
theorem B9420077 : Blo 2203435 9420077 := bstep (se 3 (by rfl) ⟨1766264, by rfl⟩ : syracuseStep 9420077 = 3532529) B3532529
theorem B6280051 : Blo 2203435 6280051 := bstep (se 1 (by rfl) ⟨4710038, by rfl⟩ : syracuseStep 6280051 = 9420077) B9420077
theorem B8373401 : Blo 2203435 8373401 := bstep (se 2 (by rfl) ⟨3140025, by rfl⟩ : syracuseStep 8373401 = 6280051) B6280051
theorem B5582267 : Blo 2203435 5582267 := bstep (se 1 (by rfl) ⟨4186700, by rfl⟩ : syracuseStep 5582267 = 8373401) B8373401
theorem B3721511 : Blo 2203435 3721511 := bstep (se 1 (by rfl) ⟨2791133, by rfl⟩ : syracuseStep 3721511 = 5582267) B5582267
theorem B2481007 : Blo 2203435 2481007 := bstep (se 1 (by rfl) ⟨1860755, by rfl⟩ : syracuseStep 2481007 = 3721511) B3721511
theorem B3308009 : Blo 2203435 3308009 := bstep (se 2 (by rfl) ⟨1240503, by rfl⟩ : syracuseStep 3308009 = 2481007) B2481007
theorem B2205339 : Blo 2203435 2205339 := bstep (se 1 (by rfl) ⟨1654004, by rfl⟩ : syracuseStep 2205339 = 3308009) B3308009
theorem B6042485 : Blo 2203435 6042485 := bbase (se 5 (by rfl) ⟨283241, by rfl⟩ : syracuseStep 6042485 = 566483) (by norm_num)
theorem B16113293 : Blo 2203435 16113293 := bstep (se 3 (by rfl) ⟨3021242, by rfl⟩ : syracuseStep 16113293 = 6042485) B6042485
theorem B10742195 : Blo 2203435 10742195 := bstep (se 1 (by rfl) ⟨8056646, by rfl⟩ : syracuseStep 10742195 = 16113293) B16113293
theorem B7161463 : Blo 2203435 7161463 := bstep (se 1 (by rfl) ⟨5371097, by rfl⟩ : syracuseStep 7161463 = 10742195) B10742195
theorem B9548617 : Blo 2203435 9548617 := bstep (se 2 (by rfl) ⟨3580731, by rfl⟩ : syracuseStep 9548617 = 7161463) B7161463
theorem B12731489 : Blo 2203435 12731489 := bstep (se 2 (by rfl) ⟨4774308, by rfl⟩ : syracuseStep 12731489 = 9548617) B9548617
theorem B8487659 : Blo 2203435 8487659 := bstep (se 1 (by rfl) ⟨6365744, by rfl⟩ : syracuseStep 8487659 = 12731489) B12731489
theorem B5658439 : Blo 2203435 5658439 := bstep (se 1 (by rfl) ⟨4243829, by rfl⟩ : syracuseStep 5658439 = 8487659) B8487659
theorem B7544585 : Blo 2203435 7544585 := bstep (se 2 (by rfl) ⟨2829219, by rfl⟩ : syracuseStep 7544585 = 5658439) B5658439
theorem B5029723 : Blo 2203435 5029723 := bstep (se 1 (by rfl) ⟨3772292, by rfl⟩ : syracuseStep 5029723 = 7544585) B7544585
theorem B6706297 : Blo 2203435 6706297 := bstep (se 2 (by rfl) ⟨2514861, by rfl⟩ : syracuseStep 6706297 = 5029723) B5029723
theorem B35766917 : Blo 2203435 35766917 := bstep (se 4 (by rfl) ⟨3353148, by rfl⟩ : syracuseStep 35766917 = 6706297) B6706297
theorem B23844611 : Blo 2203435 23844611 := bstep (se 1 (by rfl) ⟨17883458, by rfl⟩ : syracuseStep 23844611 = 35766917) B35766917
theorem B15896407 : Blo 2203435 15896407 := bstep (se 1 (by rfl) ⟨11922305, by rfl⟩ : syracuseStep 15896407 = 23844611) B23844611
theorem B21195209 : Blo 2203435 21195209 := bstep (se 2 (by rfl) ⟨7948203, by rfl⟩ : syracuseStep 21195209 = 15896407) B15896407
theorem B14130139 : Blo 2203435 14130139 := bstep (se 1 (by rfl) ⟨10597604, by rfl⟩ : syracuseStep 14130139 = 21195209) B21195209
theorem B18840185 : Blo 2203435 18840185 := bstep (se 2 (by rfl) ⟨7065069, by rfl⟩ : syracuseStep 18840185 = 14130139) B14130139
theorem B12560123 : Blo 2203435 12560123 := bstep (se 1 (by rfl) ⟨9420092, by rfl⟩ : syracuseStep 12560123 = 18840185) B18840185
theorem B8373415 : Blo 2203435 8373415 := bstep (se 1 (by rfl) ⟨6280061, by rfl⟩ : syracuseStep 8373415 = 12560123) B12560123
theorem B11164553 : Blo 2203435 11164553 := bstep (se 2 (by rfl) ⟨4186707, by rfl⟩ : syracuseStep 11164553 = 8373415) B8373415
theorem B7443035 : Blo 2203435 7443035 := bstep (se 1 (by rfl) ⟨5582276, by rfl⟩ : syracuseStep 7443035 = 11164553) B11164553
theorem B4962023 : Blo 2203435 4962023 := bstep (se 1 (by rfl) ⟨3721517, by rfl⟩ : syracuseStep 4962023 = 7443035) B7443035
theorem B3308015 : Blo 2203435 3308015 := bstep (se 1 (by rfl) ⟨2481011, by rfl⟩ : syracuseStep 3308015 = 4962023) B4962023
theorem B2205343 : Blo 2203435 2205343 := bstep (se 1 (by rfl) ⟨1654007, by rfl⟩ : syracuseStep 2205343 = 3308015) B3308015
theorem B3308021 : Blo 2203435 3308021 := bbase (se 5 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 3308021 = 310127) (by norm_num)
theorem B2205347 : Blo 2203435 2205347 := bstep (se 1 (by rfl) ⟨1654010, by rfl⟩ : syracuseStep 2205347 = 3308021) B3308021
theorem B6280085 : Blo 2203435 6280085 := bbase (se 6 (by rfl) ⟨147189, by rfl⟩ : syracuseStep 6280085 = 294379) (by norm_num)
theorem B4186723 : Blo 2203435 4186723 := bstep (se 1 (by rfl) ⟨3140042, by rfl⟩ : syracuseStep 4186723 = 6280085) B6280085
theorem B5582297 : Blo 2203435 5582297 := bstep (se 2 (by rfl) ⟨2093361, by rfl⟩ : syracuseStep 5582297 = 4186723) B4186723
theorem B3721531 : Blo 2203435 3721531 := bstep (se 1 (by rfl) ⟨2791148, by rfl⟩ : syracuseStep 3721531 = 5582297) B5582297
theorem B4962041 : Blo 2203435 4962041 := bstep (se 2 (by rfl) ⟨1860765, by rfl⟩ : syracuseStep 4962041 = 3721531) B3721531
theorem B3308027 : Blo 2203435 3308027 := bstep (se 1 (by rfl) ⟨2481020, by rfl⟩ : syracuseStep 3308027 = 4962041) B4962041
theorem B2205351 : Blo 2203435 2205351 := bstep (se 1 (by rfl) ⟨1654013, by rfl⟩ : syracuseStep 2205351 = 3308027) B3308027
theorem B2481025 : Blo 2203435 2481025 := bbase (se 2 (by rfl) ⟨930384, by rfl⟩ : syracuseStep 2481025 = 1860769) (by norm_num)
theorem B3308033 : Blo 2203435 3308033 := bstep (se 2 (by rfl) ⟨1240512, by rfl⟩ : syracuseStep 3308033 = 2481025) B2481025
theorem B2205355 : Blo 2203435 2205355 := bstep (se 1 (by rfl) ⟨1654016, by rfl⟩ : syracuseStep 2205355 = 3308033) B3308033
theorem B5582317 : Blo 2203435 5582317 := bbase (se 3 (by rfl) ⟨1046684, by rfl⟩ : syracuseStep 5582317 = 2093369) (by norm_num)
theorem B7443089 : Blo 2203435 7443089 := bstep (se 2 (by rfl) ⟨2791158, by rfl⟩ : syracuseStep 7443089 = 5582317) B5582317
theorem B4962059 : Blo 2203435 4962059 := bstep (se 1 (by rfl) ⟨3721544, by rfl⟩ : syracuseStep 4962059 = 7443089) B7443089
theorem B3308039 : Blo 2203435 3308039 := bstep (se 1 (by rfl) ⟨2481029, by rfl⟩ : syracuseStep 3308039 = 4962059) B4962059
theorem B2205359 : Blo 2203435 2205359 := bstep (se 1 (by rfl) ⟨1654019, by rfl⟩ : syracuseStep 2205359 = 3308039) B3308039
theorem B3308045 : Blo 2203435 3308045 := bbase (se 3 (by rfl) ⟨620258, by rfl⟩ : syracuseStep 3308045 = 1240517) (by norm_num)
theorem B2205363 : Blo 2203435 2205363 := bstep (se 1 (by rfl) ⟨1654022, by rfl⟩ : syracuseStep 2205363 = 3308045) B3308045
theorem B4962077 : Blo 2203435 4962077 := bbase (se 3 (by rfl) ⟨930389, by rfl⟩ : syracuseStep 4962077 = 1860779) (by norm_num)
theorem B3308051 : Blo 2203435 3308051 := bstep (se 1 (by rfl) ⟨2481038, by rfl⟩ : syracuseStep 3308051 = 4962077) B4962077
theorem B2205367 : Blo 2203435 2205367 := bstep (se 1 (by rfl) ⟨1654025, by rfl⟩ : syracuseStep 2205367 = 3308051) B3308051
theorem B3721565 : Blo 2203435 3721565 := bbase (se 3 (by rfl) ⟨697793, by rfl⟩ : syracuseStep 3721565 = 1395587) (by norm_num)
theorem B2481043 : Blo 2203435 2481043 := bstep (se 1 (by rfl) ⟨1860782, by rfl⟩ : syracuseStep 2481043 = 3721565) B3721565
theorem B3308057 : Blo 2203435 3308057 := bstep (se 2 (by rfl) ⟨1240521, by rfl⟩ : syracuseStep 3308057 = 2481043) B2481043
theorem B2205371 : Blo 2203435 2205371 := bstep (se 1 (by rfl) ⟨1654028, by rfl⟩ : syracuseStep 2205371 = 3308057) B3308057
theorem B9420229 : Blo 2203435 9420229 := bbase (se 4 (by rfl) ⟨883146, by rfl⟩ : syracuseStep 9420229 = 1766293) (by norm_num)
theorem B12560305 : Blo 2203435 12560305 := bstep (se 2 (by rfl) ⟨4710114, by rfl⟩ : syracuseStep 12560305 = 9420229) B9420229
theorem B16747073 : Blo 2203435 16747073 := bstep (se 2 (by rfl) ⟨6280152, by rfl⟩ : syracuseStep 16747073 = 12560305) B12560305
theorem B11164715 : Blo 2203435 11164715 := bstep (se 1 (by rfl) ⟨8373536, by rfl⟩ : syracuseStep 11164715 = 16747073) B16747073
theorem B7443143 : Blo 2203435 7443143 := bstep (se 1 (by rfl) ⟨5582357, by rfl⟩ : syracuseStep 7443143 = 11164715) B11164715
theorem B4962095 : Blo 2203435 4962095 := bstep (se 1 (by rfl) ⟨3721571, by rfl⟩ : syracuseStep 4962095 = 7443143) B7443143
theorem B3308063 : Blo 2203435 3308063 := bstep (se 1 (by rfl) ⟨2481047, by rfl⟩ : syracuseStep 3308063 = 4962095) B4962095
theorem B2205375 : Blo 2203435 2205375 := bstep (se 1 (by rfl) ⟨1654031, by rfl⟩ : syracuseStep 2205375 = 3308063) B3308063
theorem B3308069 : Blo 2203435 3308069 := bbase (se 4 (by rfl) ⟨310131, by rfl⟩ : syracuseStep 3308069 = 620263) (by norm_num)
theorem B2205379 : Blo 2203435 2205379 := bstep (se 1 (by rfl) ⟨1654034, by rfl⟩ : syracuseStep 2205379 = 3308069) B3308069
theorem B2791189 : Blo 2203435 2791189 := bbase (se 6 (by rfl) ⟨65418, by rfl⟩ : syracuseStep 2791189 = 130837) (by norm_num)
theorem B3721585 : Blo 2203435 3721585 := bstep (se 2 (by rfl) ⟨1395594, by rfl⟩ : syracuseStep 3721585 = 2791189) B2791189
theorem B4962113 : Blo 2203435 4962113 := bstep (se 2 (by rfl) ⟨1860792, by rfl⟩ : syracuseStep 4962113 = 3721585) B3721585
theorem B3308075 : Blo 2203435 3308075 := bstep (se 1 (by rfl) ⟨2481056, by rfl⟩ : syracuseStep 3308075 = 4962113) B4962113
theorem B2205383 : Blo 2203435 2205383 := bstep (se 1 (by rfl) ⟨1654037, by rfl⟩ : syracuseStep 2205383 = 3308075) B3308075
theorem B2481061 : Blo 2203435 2481061 := bbase (se 4 (by rfl) ⟨232599, by rfl⟩ : syracuseStep 2481061 = 465199) (by norm_num)
theorem B3308081 : Blo 2203435 3308081 := bstep (se 2 (by rfl) ⟨1240530, by rfl⟩ : syracuseStep 3308081 = 2481061) B2481061
theorem B2205387 : Blo 2203435 2205387 := bstep (se 1 (by rfl) ⟨1654040, by rfl⟩ : syracuseStep 2205387 = 3308081) B3308081
theorem B3974189 : Blo 2203435 3974189 := bbase (se 3 (by rfl) ⟨745160, by rfl⟩ : syracuseStep 3974189 = 1490321) (by norm_num)
theorem B10597837 : Blo 2203435 10597837 := bstep (se 3 (by rfl) ⟨1987094, by rfl⟩ : syracuseStep 10597837 = 3974189) B3974189
theorem B14130449 : Blo 2203435 14130449 := bstep (se 2 (by rfl) ⟨5298918, by rfl⟩ : syracuseStep 14130449 = 10597837) B10597837
theorem B9420299 : Blo 2203435 9420299 := bstep (se 1 (by rfl) ⟨7065224, by rfl⟩ : syracuseStep 9420299 = 14130449) B14130449
theorem B6280199 : Blo 2203435 6280199 := bstep (se 1 (by rfl) ⟨4710149, by rfl⟩ : syracuseStep 6280199 = 9420299) B9420299
theorem B4186799 : Blo 2203435 4186799 := bstep (se 1 (by rfl) ⟨3140099, by rfl⟩ : syracuseStep 4186799 = 6280199) B6280199
theorem B2791199 : Blo 2203435 2791199 := bstep (se 1 (by rfl) ⟨2093399, by rfl⟩ : syracuseStep 2791199 = 4186799) B4186799
theorem B7443197 : Blo 2203435 7443197 := bstep (se 3 (by rfl) ⟨1395599, by rfl⟩ : syracuseStep 7443197 = 2791199) B2791199
theorem B4962131 : Blo 2203435 4962131 := bstep (se 1 (by rfl) ⟨3721598, by rfl⟩ : syracuseStep 4962131 = 7443197) B7443197
theorem B3308087 : Blo 2203435 3308087 := bstep (se 1 (by rfl) ⟨2481065, by rfl⟩ : syracuseStep 3308087 = 4962131) B4962131
theorem B2205391 : Blo 2203435 2205391 := bstep (se 1 (by rfl) ⟨1654043, by rfl⟩ : syracuseStep 2205391 = 3308087) B3308087
theorem B3308093 : Blo 2203435 3308093 := bbase (se 3 (by rfl) ⟨620267, by rfl⟩ : syracuseStep 3308093 = 1240535) (by norm_num)
theorem B2205395 : Blo 2203435 2205395 := bstep (se 1 (by rfl) ⟨1654046, by rfl⟩ : syracuseStep 2205395 = 3308093) B3308093
theorem B4962149 : Blo 2203435 4962149 := bbase (se 4 (by rfl) ⟨465201, by rfl⟩ : syracuseStep 4962149 = 930403) (by norm_num)
theorem B3308099 : Blo 2203435 3308099 := bstep (se 1 (by rfl) ⟨2481074, by rfl⟩ : syracuseStep 3308099 = 4962149) B4962149
theorem B2205399 : Blo 2203435 2205399 := bstep (se 1 (by rfl) ⟨1654049, by rfl⟩ : syracuseStep 2205399 = 3308099) B3308099
theorem B5582429 : Blo 2203435 5582429 := bbase (se 3 (by rfl) ⟨1046705, by rfl⟩ : syracuseStep 5582429 = 2093411) (by norm_num)
theorem B3721619 : Blo 2203435 3721619 := bstep (se 1 (by rfl) ⟨2791214, by rfl⟩ : syracuseStep 3721619 = 5582429) B5582429
theorem B2481079 : Blo 2203435 2481079 := bstep (se 1 (by rfl) ⟨1860809, by rfl⟩ : syracuseStep 2481079 = 3721619) B3721619
theorem B3308105 : Blo 2203435 3308105 := bstep (se 2 (by rfl) ⟨1240539, by rfl⟩ : syracuseStep 3308105 = 2481079) B2481079
theorem B2205403 : Blo 2203435 2205403 := bstep (se 1 (by rfl) ⟨1654052, by rfl⟩ : syracuseStep 2205403 = 3308105) B3308105
theorem B4186829 : Blo 2203435 4186829 := bbase (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) (by norm_num)
theorem B11164877 : Blo 2203435 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B7443251 : Blo 2203435 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B4962167 : Blo 2203435 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B3308111 : Blo 2203435 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B2205407 : Blo 2203435 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B3308117 : Blo 2203435 3308117 := bbase (se 8 (by rfl) ⟨19383, by rfl⟩ : syracuseStep 3308117 = 38767) (by norm_num)
theorem B2205411 : Blo 2203435 2205411 := bstep (se 1 (by rfl) ⟨1654058, by rfl⟩ : syracuseStep 2205411 = 3308117) B3308117
theorem B7065301 : Blo 2203435 7065301 := bbase (se 7 (by rfl) ⟨82796, by rfl⟩ : syracuseStep 7065301 = 165593) (by norm_num)
theorem B9420401 : Blo 2203435 9420401 := bstep (se 2 (by rfl) ⟨3532650, by rfl⟩ : syracuseStep 9420401 = 7065301) B7065301
theorem B6280267 : Blo 2203435 6280267 := bstep (se 1 (by rfl) ⟨4710200, by rfl⟩ : syracuseStep 6280267 = 9420401) B9420401
theorem B8373689 : Blo 2203435 8373689 := bstep (se 2 (by rfl) ⟨3140133, by rfl⟩ : syracuseStep 8373689 = 6280267) B6280267
theorem B5582459 : Blo 2203435 5582459 := bstep (se 1 (by rfl) ⟨4186844, by rfl⟩ : syracuseStep 5582459 = 8373689) B8373689
theorem B3721639 : Blo 2203435 3721639 := bstep (se 1 (by rfl) ⟨2791229, by rfl⟩ : syracuseStep 3721639 = 5582459) B5582459
theorem B4962185 : Blo 2203435 4962185 := bstep (se 2 (by rfl) ⟨1860819, by rfl⟩ : syracuseStep 4962185 = 3721639) B3721639
theorem B3308123 : Blo 2203435 3308123 := bstep (se 1 (by rfl) ⟨2481092, by rfl⟩ : syracuseStep 3308123 = 4962185) B4962185
theorem B2205415 : Blo 2203435 2205415 := bstep (se 1 (by rfl) ⟨1654061, by rfl⟩ : syracuseStep 2205415 = 3308123) B3308123
theorem B2481097 : Blo 2203435 2481097 := bbase (se 2 (by rfl) ⟨930411, by rfl⟩ : syracuseStep 2481097 = 1860823) (by norm_num)
theorem B3308129 : Blo 2203435 3308129 := bstep (se 2 (by rfl) ⟨1240548, by rfl⟩ : syracuseStep 3308129 = 2481097) B2481097
theorem B2205419 : Blo 2203435 2205419 := bstep (se 1 (by rfl) ⟨1654064, by rfl⟩ : syracuseStep 2205419 = 3308129) B3308129
theorem B2980685 : Blo 2203435 2980685 := bbase (se 3 (by rfl) ⟨558878, by rfl⟩ : syracuseStep 2980685 = 1117757) (by norm_num)
theorem B7948493 : Blo 2203435 7948493 := bstep (se 3 (by rfl) ⟨1490342, by rfl⟩ : syracuseStep 7948493 = 2980685) B2980685
theorem B5298995 : Blo 2203435 5298995 := bstep (se 1 (by rfl) ⟨3974246, by rfl⟩ : syracuseStep 5298995 = 7948493) B7948493
theorem B3532663 : Blo 2203435 3532663 := bstep (se 1 (by rfl) ⟨2649497, by rfl⟩ : syracuseStep 3532663 = 5298995) B5298995
theorem B18840869 : Blo 2203435 18840869 := bstep (se 4 (by rfl) ⟨1766331, by rfl⟩ : syracuseStep 18840869 = 3532663) B3532663
theorem B12560579 : Blo 2203435 12560579 := bstep (se 1 (by rfl) ⟨9420434, by rfl⟩ : syracuseStep 12560579 = 18840869) B18840869
theorem B8373719 : Blo 2203435 8373719 := bstep (se 1 (by rfl) ⟨6280289, by rfl⟩ : syracuseStep 8373719 = 12560579) B12560579
theorem B5582479 : Blo 2203435 5582479 := bstep (se 1 (by rfl) ⟨4186859, by rfl⟩ : syracuseStep 5582479 = 8373719) B8373719
theorem B7443305 : Blo 2203435 7443305 := bstep (se 2 (by rfl) ⟨2791239, by rfl⟩ : syracuseStep 7443305 = 5582479) B5582479
theorem B4962203 : Blo 2203435 4962203 := bstep (se 1 (by rfl) ⟨3721652, by rfl⟩ : syracuseStep 4962203 = 7443305) B7443305
theorem B3308135 : Blo 2203435 3308135 := bstep (se 1 (by rfl) ⟨2481101, by rfl⟩ : syracuseStep 3308135 = 4962203) B4962203
theorem B2205423 : Blo 2203435 2205423 := bstep (se 1 (by rfl) ⟨1654067, by rfl⟩ : syracuseStep 2205423 = 3308135) B3308135
theorem B3308141 : Blo 2203435 3308141 := bbase (se 3 (by rfl) ⟨620276, by rfl⟩ : syracuseStep 3308141 = 1240553) (by norm_num)
theorem B2205427 : Blo 2203435 2205427 := bstep (se 1 (by rfl) ⟨1654070, by rfl⟩ : syracuseStep 2205427 = 3308141) B3308141
theorem B4962221 : Blo 2203435 4962221 := bbase (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) (by norm_num)
theorem B3308147 : Blo 2203435 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B2205431 : Blo 2203435 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B6280325 : Blo 2203435 6280325 := bbase (se 4 (by rfl) ⟨588780, by rfl⟩ : syracuseStep 6280325 = 1177561) (by norm_num)
theorem B4186883 : Blo 2203435 4186883 := bstep (se 1 (by rfl) ⟨3140162, by rfl⟩ : syracuseStep 4186883 = 6280325) B6280325
theorem B2791255 : Blo 2203435 2791255 := bstep (se 1 (by rfl) ⟨2093441, by rfl⟩ : syracuseStep 2791255 = 4186883) B4186883
theorem B3721673 : Blo 2203435 3721673 := bstep (se 2 (by rfl) ⟨1395627, by rfl⟩ : syracuseStep 3721673 = 2791255) B2791255
theorem B2481115 : Blo 2203435 2481115 := bstep (se 1 (by rfl) ⟨1860836, by rfl⟩ : syracuseStep 2481115 = 3721673) B3721673
theorem B3308153 : Blo 2203435 3308153 := bstep (se 2 (by rfl) ⟨1240557, by rfl⟩ : syracuseStep 3308153 = 2481115) B2481115
theorem B2205435 : Blo 2203435 2205435 := bstep (se 1 (by rfl) ⟨1654076, by rfl⟩ : syracuseStep 2205435 = 3308153) B3308153
theorem C0 (j : ℕ) (h1 : 550858 ≤ j) (h2 : j ≤ 551358) : Blo 2203435 (4 * j + 3) := by
  interval_cases j
  · exact B2203435
  · exact B2203439
  · exact B2203443
  · exact B2203447
  · exact B2203451
  · exact B2203455
  · exact B2203459
  · exact B2203463
  · exact B2203467
  · exact B2203471
  · exact B2203475
  · exact B2203479
  · exact B2203483
  · exact B2203487
  · exact B2203491
  · exact B2203495
  · exact B2203499
  · exact B2203503
  · exact B2203507
  · exact B2203511
  · exact B2203515
  · exact B2203519
  · exact B2203523
  · exact B2203527
  · exact B2203531
  · exact B2203535
  · exact B2203539
  · exact B2203543
  · exact B2203547
  · exact B2203551
  · exact B2203555
  · exact B2203559
  · exact B2203563
  · exact B2203567
  · exact B2203571
  · exact B2203575
  · exact B2203579
  · exact B2203583
  · exact B2203587
  · exact B2203591
  · exact B2203595
  · exact B2203599
  · exact B2203603
  · exact B2203607
  · exact B2203611
  · exact B2203615
  · exact B2203619
  · exact B2203623
  · exact B2203627
  · exact B2203631
  · exact B2203635
  · exact B2203639
  · exact B2203643
  · exact B2203647
  · exact B2203651
  · exact B2203655
  · exact B2203659
  · exact B2203663
  · exact B2203667
  · exact B2203671
  · exact B2203675
  · exact B2203679
  · exact B2203683
  · exact B2203687
  · exact B2203691
  · exact B2203695
  · exact B2203699
  · exact B2203703
  · exact B2203707
  · exact B2203711
  · exact B2203715
  · exact B2203719
  · exact B2203723
  · exact B2203727
  · exact B2203731
  · exact B2203735
  · exact B2203739
  · exact B2203743
  · exact B2203747
  · exact B2203751
  · exact B2203755
  · exact B2203759
  · exact B2203763
  · exact B2203767
  · exact B2203771
  · exact B2203775
  · exact B2203779
  · exact B2203783
  · exact B2203787
  · exact B2203791
  · exact B2203795
  · exact B2203799
  · exact B2203803
  · exact B2203807
  · exact B2203811
  · exact B2203815
  · exact B2203819
  · exact B2203823
  · exact B2203827
  · exact B2203831
  · exact B2203835
  · exact B2203839
  · exact B2203843
  · exact B2203847
  · exact B2203851
  · exact B2203855
  · exact B2203859
  · exact B2203863
  · exact B2203867
  · exact B2203871
  · exact B2203875
  · exact B2203879
  · exact B2203883
  · exact B2203887
  · exact B2203891
  · exact B2203895
  · exact B2203899
  · exact B2203903
  · exact B2203907
  · exact B2203911
  · exact B2203915
  · exact B2203919
  · exact B2203923
  · exact B2203927
  · exact B2203931
  · exact B2203935
  · exact B2203939
  · exact B2203943
  · exact B2203947
  · exact B2203951
  · exact B2203955
  · exact B2203959
  · exact B2203963
  · exact B2203967
  · exact B2203971
  · exact B2203975
  · exact B2203979
  · exact B2203983
  · exact B2203987
  · exact B2203991
  · exact B2203995
  · exact B2203999
  · exact B2204003
  · exact B2204007
  · exact B2204011
  · exact B2204015
  · exact B2204019
  · exact B2204023
  · exact B2204027
  · exact B2204031
  · exact B2204035
  · exact B2204039
  · exact B2204043
  · exact B2204047
  · exact B2204051
  · exact B2204055
  · exact B2204059
  · exact B2204063
  · exact B2204067
  · exact B2204071
  · exact B2204075
  · exact B2204079
  · exact B2204083
  · exact B2204087
  · exact B2204091
  · exact B2204095
  · exact B2204099
  · exact B2204103
  · exact B2204107
  · exact B2204111
  · exact B2204115
  · exact B2204119
  · exact B2204123
  · exact B2204127
  · exact B2204131
  · exact B2204135
  · exact B2204139
  · exact B2204143
  · exact B2204147
  · exact B2204151
  · exact B2204155
  · exact B2204159
  · exact B2204163
  · exact B2204167
  · exact B2204171
  · exact B2204175
  · exact B2204179
  · exact B2204183
  · exact B2204187
  · exact B2204191
  · exact B2204195
  · exact B2204199
  · exact B2204203
  · exact B2204207
  · exact B2204211
  · exact B2204215
  · exact B2204219
  · exact B2204223
  · exact B2204227
  · exact B2204231
  · exact B2204235
  · exact B2204239
  · exact B2204243
  · exact B2204247
  · exact B2204251
  · exact B2204255
  · exact B2204259
  · exact B2204263
  · exact B2204267
  · exact B2204271
  · exact B2204275
  · exact B2204279
  · exact B2204283
  · exact B2204287
  · exact B2204291
  · exact B2204295
  · exact B2204299
  · exact B2204303
  · exact B2204307
  · exact B2204311
  · exact B2204315
  · exact B2204319
  · exact B2204323
  · exact B2204327
  · exact B2204331
  · exact B2204335
  · exact B2204339
  · exact B2204343
  · exact B2204347
  · exact B2204351
  · exact B2204355
  · exact B2204359
  · exact B2204363
  · exact B2204367
  · exact B2204371
  · exact B2204375
  · exact B2204379
  · exact B2204383
  · exact B2204387
  · exact B2204391
  · exact B2204395
  · exact B2204399
  · exact B2204403
  · exact B2204407
  · exact B2204411
  · exact B2204415
  · exact B2204419
  · exact B2204423
  · exact B2204427
  · exact B2204431
  · exact B2204435
  · exact B2204439
  · exact B2204443
  · exact B2204447
  · exact B2204451
  · exact B2204455
  · exact B2204459
  · exact B2204463
  · exact B2204467
  · exact B2204471
  · exact B2204475
  · exact B2204479
  · exact B2204483
  · exact B2204487
  · exact B2204491
  · exact B2204495
  · exact B2204499
  · exact B2204503
  · exact B2204507
  · exact B2204511
  · exact B2204515
  · exact B2204519
  · exact B2204523
  · exact B2204527
  · exact B2204531
  · exact B2204535
  · exact B2204539
  · exact B2204543
  · exact B2204547
  · exact B2204551
  · exact B2204555
  · exact B2204559
  · exact B2204563
  · exact B2204567
  · exact B2204571
  · exact B2204575
  · exact B2204579
  · exact B2204583
  · exact B2204587
  · exact B2204591
  · exact B2204595
  · exact B2204599
  · exact B2204603
  · exact B2204607
  · exact B2204611
  · exact B2204615
  · exact B2204619
  · exact B2204623
  · exact B2204627
  · exact B2204631
  · exact B2204635
  · exact B2204639
  · exact B2204643
  · exact B2204647
  · exact B2204651
  · exact B2204655
  · exact B2204659
  · exact B2204663
  · exact B2204667
  · exact B2204671
  · exact B2204675
  · exact B2204679
  · exact B2204683
  · exact B2204687
  · exact B2204691
  · exact B2204695
  · exact B2204699
  · exact B2204703
  · exact B2204707
  · exact B2204711
  · exact B2204715
  · exact B2204719
  · exact B2204723
  · exact B2204727
  · exact B2204731
  · exact B2204735
  · exact B2204739
  · exact B2204743
  · exact B2204747
  · exact B2204751
  · exact B2204755
  · exact B2204759
  · exact B2204763
  · exact B2204767
  · exact B2204771
  · exact B2204775
  · exact B2204779
  · exact B2204783
  · exact B2204787
  · exact B2204791
  · exact B2204795
  · exact B2204799
  · exact B2204803
  · exact B2204807
  · exact B2204811
  · exact B2204815
  · exact B2204819
  · exact B2204823
  · exact B2204827
  · exact B2204831
  · exact B2204835
  · exact B2204839
  · exact B2204843
  · exact B2204847
  · exact B2204851
  · exact B2204855
  · exact B2204859
  · exact B2204863
  · exact B2204867
  · exact B2204871
  · exact B2204875
  · exact B2204879
  · exact B2204883
  · exact B2204887
  · exact B2204891
  · exact B2204895
  · exact B2204899
  · exact B2204903
  · exact B2204907
  · exact B2204911
  · exact B2204915
  · exact B2204919
  · exact B2204923
  · exact B2204927
  · exact B2204931
  · exact B2204935
  · exact B2204939
  · exact B2204943
  · exact B2204947
  · exact B2204951
  · exact B2204955
  · exact B2204959
  · exact B2204963
  · exact B2204967
  · exact B2204971
  · exact B2204975
  · exact B2204979
  · exact B2204983
  · exact B2204987
  · exact B2204991
  · exact B2204995
  · exact B2204999
  · exact B2205003
  · exact B2205007
  · exact B2205011
  · exact B2205015
  · exact B2205019
  · exact B2205023
  · exact B2205027
  · exact B2205031
  · exact B2205035
  · exact B2205039
  · exact B2205043
  · exact B2205047
  · exact B2205051
  · exact B2205055
  · exact B2205059
  · exact B2205063
  · exact B2205067
  · exact B2205071
  · exact B2205075
  · exact B2205079
  · exact B2205083
  · exact B2205087
  · exact B2205091
  · exact B2205095
  · exact B2205099
  · exact B2205103
  · exact B2205107
  · exact B2205111
  · exact B2205115
  · exact B2205119
  · exact B2205123
  · exact B2205127
  · exact B2205131
  · exact B2205135
  · exact B2205139
  · exact B2205143
  · exact B2205147
  · exact B2205151
  · exact B2205155
  · exact B2205159
  · exact B2205163
  · exact B2205167
  · exact B2205171
  · exact B2205175
  · exact B2205179
  · exact B2205183
  · exact B2205187
  · exact B2205191
  · exact B2205195
  · exact B2205199
  · exact B2205203
  · exact B2205207
  · exact B2205211
  · exact B2205215
  · exact B2205219
  · exact B2205223
  · exact B2205227
  · exact B2205231
  · exact B2205235
  · exact B2205239
  · exact B2205243
  · exact B2205247
  · exact B2205251
  · exact B2205255
  · exact B2205259
  · exact B2205263
  · exact B2205267
  · exact B2205271
  · exact B2205275
  · exact B2205279
  · exact B2205283
  · exact B2205287
  · exact B2205291
  · exact B2205295
  · exact B2205299
  · exact B2205303
  · exact B2205307
  · exact B2205311
  · exact B2205315
  · exact B2205319
  · exact B2205323
  · exact B2205327
  · exact B2205331
  · exact B2205335
  · exact B2205339
  · exact B2205343
  · exact B2205347
  · exact B2205351
  · exact B2205355
  · exact B2205359
  · exact B2205363
  · exact B2205367
  · exact B2205371
  · exact B2205375
  · exact B2205379
  · exact B2205383
  · exact B2205387
  · exact B2205391
  · exact B2205395
  · exact B2205399
  · exact B2205403
  · exact B2205407
  · exact B2205411
  · exact B2205415
  · exact B2205419
  · exact B2205423
  · exact B2205427
  · exact B2205431
  · exact B2205435
theorem solution (m : ℕ) (hlo : 2203435 ≤ m) (hhi : m ≤ 2205435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 550858 ≤ j := by omega
    have hj2 : j ≤ 551358 := by omega
    have hb : Blo 2203435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
