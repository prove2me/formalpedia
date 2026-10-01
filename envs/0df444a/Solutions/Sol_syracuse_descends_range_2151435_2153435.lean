-- Prove2me | solution 1 for syracuse_descends_range_2151435_2153435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:28.337395+00:00
-- url     : https://prove2.me/submissions/fd56f03c-b05b-474a-90c7-b7723d5f2f36

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

theorem B2420365 : Blo 2151435 2420365 := bbase (se 3 (by rfl) ⟨453818, by rfl⟩ : syracuseStep 2420365 = 907637) (by norm_num)
theorem B3227153 : Blo 2151435 3227153 := bstep (se 2 (by rfl) ⟨1210182, by rfl⟩ : syracuseStep 3227153 = 2420365) B2420365
theorem B2151435 : Blo 2151435 2151435 := bstep (se 1 (by rfl) ⟨1613576, by rfl⟩ : syracuseStep 2151435 = 3227153) B3227153
theorem B7261109 : Blo 2151435 7261109 := bbase (se 5 (by rfl) ⟨340364, by rfl⟩ : syracuseStep 7261109 = 680729) (by norm_num)
theorem B4840739 : Blo 2151435 4840739 := bstep (se 1 (by rfl) ⟨3630554, by rfl⟩ : syracuseStep 4840739 = 7261109) B7261109
theorem B3227159 : Blo 2151435 3227159 := bstep (se 1 (by rfl) ⟨2420369, by rfl⟩ : syracuseStep 3227159 = 4840739) B4840739
theorem B2151439 : Blo 2151435 2151439 := bstep (se 1 (by rfl) ⟨1613579, by rfl⟩ : syracuseStep 2151439 = 3227159) B3227159
theorem B3227165 : Blo 2151435 3227165 := bbase (se 3 (by rfl) ⟨605093, by rfl⟩ : syracuseStep 3227165 = 1210187) (by norm_num)
theorem B2151443 : Blo 2151435 2151443 := bstep (se 1 (by rfl) ⟨1613582, by rfl⟩ : syracuseStep 2151443 = 3227165) B3227165
theorem B4840757 : Blo 2151435 4840757 := bbase (se 5 (by rfl) ⟨226910, by rfl⟩ : syracuseStep 4840757 = 453821) (by norm_num)
theorem B3227171 : Blo 2151435 3227171 := bstep (se 1 (by rfl) ⟨2420378, by rfl⟩ : syracuseStep 3227171 = 4840757) B4840757
theorem B2151447 : Blo 2151435 2151447 := bstep (se 1 (by rfl) ⟨1613585, by rfl⟩ : syracuseStep 2151447 = 3227171) B3227171
theorem B4906813 : Blo 2151435 4906813 := bbase (se 3 (by rfl) ⟨920027, by rfl⟩ : syracuseStep 4906813 = 1840055) (by norm_num)
theorem B6542417 : Blo 2151435 6542417 := bstep (se 2 (by rfl) ⟨2453406, by rfl⟩ : syracuseStep 6542417 = 4906813) B4906813
theorem B4361611 : Blo 2151435 4361611 := bstep (se 1 (by rfl) ⟨3271208, by rfl⟩ : syracuseStep 4361611 = 6542417) B6542417
theorem B5815481 : Blo 2151435 5815481 := bstep (se 2 (by rfl) ⟨2180805, by rfl⟩ : syracuseStep 5815481 = 4361611) B4361611
theorem B15507949 : Blo 2151435 15507949 := bstep (se 3 (by rfl) ⟨2907740, by rfl⟩ : syracuseStep 15507949 = 5815481) B5815481
theorem B20677265 : Blo 2151435 20677265 := bstep (se 2 (by rfl) ⟨7753974, by rfl⟩ : syracuseStep 20677265 = 15507949) B15507949
theorem B13784843 : Blo 2151435 13784843 := bstep (se 1 (by rfl) ⟨10338632, by rfl⟩ : syracuseStep 13784843 = 20677265) B20677265
theorem B9189895 : Blo 2151435 9189895 := bstep (se 1 (by rfl) ⟨6892421, by rfl⟩ : syracuseStep 9189895 = 13784843) B13784843
theorem B12253193 : Blo 2151435 12253193 := bstep (se 2 (by rfl) ⟨4594947, by rfl⟩ : syracuseStep 12253193 = 9189895) B9189895
theorem B8168795 : Blo 2151435 8168795 := bstep (se 1 (by rfl) ⟨6126596, by rfl⟩ : syracuseStep 8168795 = 12253193) B12253193
theorem B5445863 : Blo 2151435 5445863 := bstep (se 1 (by rfl) ⟨4084397, by rfl⟩ : syracuseStep 5445863 = 8168795) B8168795
theorem B3630575 : Blo 2151435 3630575 := bstep (se 1 (by rfl) ⟨2722931, by rfl⟩ : syracuseStep 3630575 = 5445863) B5445863
theorem B2420383 : Blo 2151435 2420383 := bstep (se 1 (by rfl) ⟨1815287, by rfl⟩ : syracuseStep 2420383 = 3630575) B3630575
theorem B3227177 : Blo 2151435 3227177 := bstep (se 2 (by rfl) ⟨1210191, by rfl⟩ : syracuseStep 3227177 = 2420383) B2420383
theorem B2151451 : Blo 2151435 2151451 := bstep (se 1 (by rfl) ⟨1613588, by rfl⟩ : syracuseStep 2151451 = 3227177) B3227177
theorem B20677301 : Blo 2151435 20677301 := bbase (se 5 (by rfl) ⟨969248, by rfl⟩ : syracuseStep 20677301 = 1938497) (by norm_num)
theorem B13784867 : Blo 2151435 13784867 := bstep (se 1 (by rfl) ⟨10338650, by rfl⟩ : syracuseStep 13784867 = 20677301) B20677301
theorem B9189911 : Blo 2151435 9189911 := bstep (se 1 (by rfl) ⟨6892433, by rfl⟩ : syracuseStep 9189911 = 13784867) B13784867
theorem B6126607 : Blo 2151435 6126607 := bstep (se 1 (by rfl) ⟨4594955, by rfl⟩ : syracuseStep 6126607 = 9189911) B9189911
theorem B8168809 : Blo 2151435 8168809 := bstep (se 2 (by rfl) ⟨3063303, by rfl⟩ : syracuseStep 8168809 = 6126607) B6126607
theorem B10891745 : Blo 2151435 10891745 := bstep (se 2 (by rfl) ⟨4084404, by rfl⟩ : syracuseStep 10891745 = 8168809) B8168809
theorem B7261163 : Blo 2151435 7261163 := bstep (se 1 (by rfl) ⟨5445872, by rfl⟩ : syracuseStep 7261163 = 10891745) B10891745
theorem B4840775 : Blo 2151435 4840775 := bstep (se 1 (by rfl) ⟨3630581, by rfl⟩ : syracuseStep 4840775 = 7261163) B7261163
theorem B3227183 : Blo 2151435 3227183 := bstep (se 1 (by rfl) ⟨2420387, by rfl⟩ : syracuseStep 3227183 = 4840775) B4840775
theorem B2151455 : Blo 2151435 2151455 := bstep (se 1 (by rfl) ⟨1613591, by rfl⟩ : syracuseStep 2151455 = 3227183) B3227183
theorem B3227189 : Blo 2151435 3227189 := bbase (se 5 (by rfl) ⟨151274, by rfl⟩ : syracuseStep 3227189 = 302549) (by norm_num)
theorem B2151459 : Blo 2151435 2151459 := bstep (se 1 (by rfl) ⟨1613594, by rfl⟩ : syracuseStep 2151459 = 3227189) B3227189
theorem B5445893 : Blo 2151435 5445893 := bbase (se 4 (by rfl) ⟨510552, by rfl⟩ : syracuseStep 5445893 = 1021105) (by norm_num)
theorem B3630595 : Blo 2151435 3630595 := bstep (se 1 (by rfl) ⟨2722946, by rfl⟩ : syracuseStep 3630595 = 5445893) B5445893
theorem B4840793 : Blo 2151435 4840793 := bstep (se 2 (by rfl) ⟨1815297, by rfl⟩ : syracuseStep 4840793 = 3630595) B3630595
theorem B3227195 : Blo 2151435 3227195 := bstep (se 1 (by rfl) ⟨2420396, by rfl⟩ : syracuseStep 3227195 = 4840793) B4840793
theorem B2151463 : Blo 2151435 2151463 := bstep (se 1 (by rfl) ⟨1613597, by rfl⟩ : syracuseStep 2151463 = 3227195) B3227195
theorem B2420401 : Blo 2151435 2420401 := bbase (se 2 (by rfl) ⟨907650, by rfl⟩ : syracuseStep 2420401 = 1815301) (by norm_num)
theorem B3227201 : Blo 2151435 3227201 := bstep (se 2 (by rfl) ⟨1210200, by rfl⟩ : syracuseStep 3227201 = 2420401) B2420401
theorem B2151467 : Blo 2151435 2151467 := bstep (se 1 (by rfl) ⟨1613600, by rfl⟩ : syracuseStep 2151467 = 3227201) B3227201
theorem B5169365 : Blo 2151435 5169365 := bbase (se 7 (by rfl) ⟨60578, by rfl⟩ : syracuseStep 5169365 = 121157) (by norm_num)
theorem B3446243 : Blo 2151435 3446243 := bstep (se 1 (by rfl) ⟨2584682, by rfl⟩ : syracuseStep 3446243 = 5169365) B5169365
theorem B2297495 : Blo 2151435 2297495 := bstep (se 1 (by rfl) ⟨1723121, by rfl⟩ : syracuseStep 2297495 = 3446243) B3446243
theorem B6126653 : Blo 2151435 6126653 := bstep (se 3 (by rfl) ⟨1148747, by rfl⟩ : syracuseStep 6126653 = 2297495) B2297495
theorem B4084435 : Blo 2151435 4084435 := bstep (se 1 (by rfl) ⟨3063326, by rfl⟩ : syracuseStep 4084435 = 6126653) B6126653
theorem B5445913 : Blo 2151435 5445913 := bstep (se 2 (by rfl) ⟨2042217, by rfl⟩ : syracuseStep 5445913 = 4084435) B4084435
theorem B7261217 : Blo 2151435 7261217 := bstep (se 2 (by rfl) ⟨2722956, by rfl⟩ : syracuseStep 7261217 = 5445913) B5445913
theorem B4840811 : Blo 2151435 4840811 := bstep (se 1 (by rfl) ⟨3630608, by rfl⟩ : syracuseStep 4840811 = 7261217) B7261217
theorem B3227207 : Blo 2151435 3227207 := bstep (se 1 (by rfl) ⟨2420405, by rfl⟩ : syracuseStep 3227207 = 4840811) B4840811
theorem B2151471 : Blo 2151435 2151471 := bstep (se 1 (by rfl) ⟨1613603, by rfl⟩ : syracuseStep 2151471 = 3227207) B3227207
theorem B3227213 : Blo 2151435 3227213 := bbase (se 3 (by rfl) ⟨605102, by rfl⟩ : syracuseStep 3227213 = 1210205) (by norm_num)
theorem B2151475 : Blo 2151435 2151475 := bstep (se 1 (by rfl) ⟨1613606, by rfl⟩ : syracuseStep 2151475 = 3227213) B3227213
theorem B4840829 : Blo 2151435 4840829 := bbase (se 3 (by rfl) ⟨907655, by rfl⟩ : syracuseStep 4840829 = 1815311) (by norm_num)
theorem B3227219 : Blo 2151435 3227219 := bstep (se 1 (by rfl) ⟨2420414, by rfl⟩ : syracuseStep 3227219 = 4840829) B4840829
theorem B2151479 : Blo 2151435 2151479 := bstep (se 1 (by rfl) ⟨1613609, by rfl⟩ : syracuseStep 2151479 = 3227219) B3227219
theorem B3630629 : Blo 2151435 3630629 := bbase (se 4 (by rfl) ⟨340371, by rfl⟩ : syracuseStep 3630629 = 680743) (by norm_num)
theorem B2420419 : Blo 2151435 2420419 := bstep (se 1 (by rfl) ⟨1815314, by rfl⟩ : syracuseStep 2420419 = 3630629) B3630629
theorem B3227225 : Blo 2151435 3227225 := bstep (se 2 (by rfl) ⟨1210209, by rfl⟩ : syracuseStep 3227225 = 2420419) B2420419
theorem B2151483 : Blo 2151435 2151483 := bstep (se 1 (by rfl) ⟨1613612, by rfl⟩ : syracuseStep 2151483 = 3227225) B3227225
theorem B3063349 : Blo 2151435 3063349 := bbase (se 5 (by rfl) ⟨143594, by rfl⟩ : syracuseStep 3063349 = 287189) (by norm_num)
theorem B16337861 : Blo 2151435 16337861 := bstep (se 4 (by rfl) ⟨1531674, by rfl⟩ : syracuseStep 16337861 = 3063349) B3063349
theorem B10891907 : Blo 2151435 10891907 := bstep (se 1 (by rfl) ⟨8168930, by rfl⟩ : syracuseStep 10891907 = 16337861) B16337861
theorem B7261271 : Blo 2151435 7261271 := bstep (se 1 (by rfl) ⟨5445953, by rfl⟩ : syracuseStep 7261271 = 10891907) B10891907
theorem B4840847 : Blo 2151435 4840847 := bstep (se 1 (by rfl) ⟨3630635, by rfl⟩ : syracuseStep 4840847 = 7261271) B7261271
theorem B3227231 : Blo 2151435 3227231 := bstep (se 1 (by rfl) ⟨2420423, by rfl⟩ : syracuseStep 3227231 = 4840847) B4840847
theorem B2151487 : Blo 2151435 2151487 := bstep (se 1 (by rfl) ⟨1613615, by rfl⟩ : syracuseStep 2151487 = 3227231) B3227231
theorem B3227237 : Blo 2151435 3227237 := bbase (se 4 (by rfl) ⟨302553, by rfl⟩ : syracuseStep 3227237 = 605107) (by norm_num)
theorem B2151491 : Blo 2151435 2151491 := bstep (se 1 (by rfl) ⟨1613618, by rfl⟩ : syracuseStep 2151491 = 3227237) B3227237
theorem B2297521 : Blo 2151435 2297521 := bbase (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) (by norm_num)
theorem B3063361 : Blo 2151435 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B4084481 : Blo 2151435 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B2722987 : Blo 2151435 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B3630649 : Blo 2151435 3630649 := bstep (se 2 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 3630649 = 2722987) B2722987
theorem B4840865 : Blo 2151435 4840865 := bstep (se 2 (by rfl) ⟨1815324, by rfl⟩ : syracuseStep 4840865 = 3630649) B3630649
theorem B3227243 : Blo 2151435 3227243 := bstep (se 1 (by rfl) ⟨2420432, by rfl⟩ : syracuseStep 3227243 = 4840865) B4840865
theorem B2151495 : Blo 2151435 2151495 := bstep (se 1 (by rfl) ⟨1613621, by rfl⟩ : syracuseStep 2151495 = 3227243) B3227243
theorem B2420437 : Blo 2151435 2420437 := bbase (se 7 (by rfl) ⟨28364, by rfl⟩ : syracuseStep 2420437 = 56729) (by norm_num)
theorem B3227249 : Blo 2151435 3227249 := bstep (se 2 (by rfl) ⟨1210218, by rfl⟩ : syracuseStep 3227249 = 2420437) B2420437
theorem B2151499 : Blo 2151435 2151499 := bstep (se 1 (by rfl) ⟨1613624, by rfl⟩ : syracuseStep 2151499 = 3227249) B3227249
theorem B2722997 : Blo 2151435 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B7261325 : Blo 2151435 7261325 := bstep (se 3 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 7261325 = 2722997) B2722997
theorem B4840883 : Blo 2151435 4840883 := bstep (se 1 (by rfl) ⟨3630662, by rfl⟩ : syracuseStep 4840883 = 7261325) B7261325
theorem B3227255 : Blo 2151435 3227255 := bstep (se 1 (by rfl) ⟨2420441, by rfl⟩ : syracuseStep 3227255 = 4840883) B4840883
theorem B2151503 : Blo 2151435 2151503 := bstep (se 1 (by rfl) ⟨1613627, by rfl⟩ : syracuseStep 2151503 = 3227255) B3227255
theorem B3227261 : Blo 2151435 3227261 := bbase (se 3 (by rfl) ⟨605111, by rfl⟩ : syracuseStep 3227261 = 1210223) (by norm_num)
theorem B2151507 : Blo 2151435 2151507 := bstep (se 1 (by rfl) ⟨1613630, by rfl⟩ : syracuseStep 2151507 = 3227261) B3227261
theorem B4840901 : Blo 2151435 4840901 := bbase (se 4 (by rfl) ⟨453834, by rfl⟩ : syracuseStep 4840901 = 907669) (by norm_num)
theorem B3227267 : Blo 2151435 3227267 := bstep (se 1 (by rfl) ⟨2420450, by rfl⟩ : syracuseStep 3227267 = 4840901) B4840901
theorem B2151511 : Blo 2151435 2151511 := bstep (se 1 (by rfl) ⟨1613633, by rfl⟩ : syracuseStep 2151511 = 3227267) B3227267
theorem B6631877 : Blo 2151435 6631877 := bbase (se 4 (by rfl) ⟨621738, by rfl⟩ : syracuseStep 6631877 = 1243477) (by norm_num)
theorem B4421251 : Blo 2151435 4421251 := bstep (se 1 (by rfl) ⟨3315938, by rfl⟩ : syracuseStep 4421251 = 6631877) B6631877
theorem B5895001 : Blo 2151435 5895001 := bstep (se 2 (by rfl) ⟨2210625, by rfl⟩ : syracuseStep 5895001 = 4421251) B4421251
theorem B31440005 : Blo 2151435 31440005 := bstep (se 4 (by rfl) ⟨2947500, by rfl⟩ : syracuseStep 31440005 = 5895001) B5895001
theorem B20960003 : Blo 2151435 20960003 := bstep (se 1 (by rfl) ⟨15720002, by rfl⟩ : syracuseStep 20960003 = 31440005) B31440005
theorem B55893341 : Blo 2151435 55893341 := bstep (se 3 (by rfl) ⟨10480001, by rfl⟩ : syracuseStep 55893341 = 20960003) B20960003
theorem B37262227 : Blo 2151435 37262227 := bstep (se 1 (by rfl) ⟨27946670, by rfl⟩ : syracuseStep 37262227 = 55893341) B55893341
theorem B49682969 : Blo 2151435 49682969 := bstep (se 2 (by rfl) ⟨18631113, by rfl⟩ : syracuseStep 49682969 = 37262227) B37262227
theorem B33121979 : Blo 2151435 33121979 := bstep (se 1 (by rfl) ⟨24841484, by rfl⟩ : syracuseStep 33121979 = 49682969) B49682969
theorem B22081319 : Blo 2151435 22081319 := bstep (se 1 (by rfl) ⟨16560989, by rfl⟩ : syracuseStep 22081319 = 33121979) B33121979
theorem B14720879 : Blo 2151435 14720879 := bstep (se 1 (by rfl) ⟨11040659, by rfl⟩ : syracuseStep 14720879 = 22081319) B22081319
theorem B9813919 : Blo 2151435 9813919 := bstep (se 1 (by rfl) ⟨7360439, by rfl⟩ : syracuseStep 9813919 = 14720879) B14720879
theorem B13085225 : Blo 2151435 13085225 := bstep (se 2 (by rfl) ⟨4906959, by rfl⟩ : syracuseStep 13085225 = 9813919) B9813919
theorem B8723483 : Blo 2151435 8723483 := bstep (se 1 (by rfl) ⟨6542612, by rfl⟩ : syracuseStep 8723483 = 13085225) B13085225
theorem B5815655 : Blo 2151435 5815655 := bstep (se 1 (by rfl) ⟨4361741, by rfl⟩ : syracuseStep 5815655 = 8723483) B8723483
theorem B3877103 : Blo 2151435 3877103 := bstep (se 1 (by rfl) ⟨2907827, by rfl⟩ : syracuseStep 3877103 = 5815655) B5815655
theorem B10338941 : Blo 2151435 10338941 := bstep (se 3 (by rfl) ⟨1938551, by rfl⟩ : syracuseStep 10338941 = 3877103) B3877103
theorem B6892627 : Blo 2151435 6892627 := bstep (se 1 (by rfl) ⟨5169470, by rfl⟩ : syracuseStep 6892627 = 10338941) B10338941
theorem B9190169 : Blo 2151435 9190169 := bstep (se 2 (by rfl) ⟨3446313, by rfl⟩ : syracuseStep 9190169 = 6892627) B6892627
theorem B6126779 : Blo 2151435 6126779 := bstep (se 1 (by rfl) ⟨4595084, by rfl⟩ : syracuseStep 6126779 = 9190169) B9190169
theorem B4084519 : Blo 2151435 4084519 := bstep (se 1 (by rfl) ⟨3063389, by rfl⟩ : syracuseStep 4084519 = 6126779) B6126779
theorem B5446025 : Blo 2151435 5446025 := bstep (se 2 (by rfl) ⟨2042259, by rfl⟩ : syracuseStep 5446025 = 4084519) B4084519
theorem B3630683 : Blo 2151435 3630683 := bstep (se 1 (by rfl) ⟨2723012, by rfl⟩ : syracuseStep 3630683 = 5446025) B5446025
theorem B2420455 : Blo 2151435 2420455 := bstep (se 1 (by rfl) ⟨1815341, by rfl⟩ : syracuseStep 2420455 = 3630683) B3630683
theorem B3227273 : Blo 2151435 3227273 := bstep (se 2 (by rfl) ⟨1210227, by rfl⟩ : syracuseStep 3227273 = 2420455) B2420455
theorem B2151515 : Blo 2151435 2151515 := bstep (se 1 (by rfl) ⟨1613636, by rfl⟩ : syracuseStep 2151515 = 3227273) B3227273
theorem B10892069 : Blo 2151435 10892069 := bbase (se 4 (by rfl) ⟨1021131, by rfl⟩ : syracuseStep 10892069 = 2042263) (by norm_num)
theorem B7261379 : Blo 2151435 7261379 := bstep (se 1 (by rfl) ⟨5446034, by rfl⟩ : syracuseStep 7261379 = 10892069) B10892069
theorem B4840919 : Blo 2151435 4840919 := bstep (se 1 (by rfl) ⟨3630689, by rfl⟩ : syracuseStep 4840919 = 7261379) B7261379
theorem B3227279 : Blo 2151435 3227279 := bstep (se 1 (by rfl) ⟨2420459, by rfl⟩ : syracuseStep 3227279 = 4840919) B4840919
theorem B2151519 : Blo 2151435 2151519 := bstep (se 1 (by rfl) ⟨1613639, by rfl⟩ : syracuseStep 2151519 = 3227279) B3227279
theorem B3227285 : Blo 2151435 3227285 := bbase (se 6 (by rfl) ⟨75639, by rfl⟩ : syracuseStep 3227285 = 151279) (by norm_num)
theorem B2151523 : Blo 2151435 2151523 := bstep (se 1 (by rfl) ⟨1613642, by rfl⟩ : syracuseStep 2151523 = 3227285) B3227285
theorem B10338997 : Blo 2151435 10338997 := bbase (se 5 (by rfl) ⟨484640, by rfl⟩ : syracuseStep 10338997 = 969281) (by norm_num)
theorem B13785329 : Blo 2151435 13785329 := bstep (se 2 (by rfl) ⟨5169498, by rfl⟩ : syracuseStep 13785329 = 10338997) B10338997
theorem B9190219 : Blo 2151435 9190219 := bstep (se 1 (by rfl) ⟨6892664, by rfl⟩ : syracuseStep 9190219 = 13785329) B13785329
theorem B12253625 : Blo 2151435 12253625 := bstep (se 2 (by rfl) ⟨4595109, by rfl⟩ : syracuseStep 12253625 = 9190219) B9190219
theorem B8169083 : Blo 2151435 8169083 := bstep (se 1 (by rfl) ⟨6126812, by rfl⟩ : syracuseStep 8169083 = 12253625) B12253625
theorem B5446055 : Blo 2151435 5446055 := bstep (se 1 (by rfl) ⟨4084541, by rfl⟩ : syracuseStep 5446055 = 8169083) B8169083
theorem B3630703 : Blo 2151435 3630703 := bstep (se 1 (by rfl) ⟨2723027, by rfl⟩ : syracuseStep 3630703 = 5446055) B5446055
theorem B4840937 : Blo 2151435 4840937 := bstep (se 2 (by rfl) ⟨1815351, by rfl⟩ : syracuseStep 4840937 = 3630703) B3630703
theorem B3227291 : Blo 2151435 3227291 := bstep (se 1 (by rfl) ⟨2420468, by rfl⟩ : syracuseStep 3227291 = 4840937) B4840937
theorem B2151527 : Blo 2151435 2151527 := bstep (se 1 (by rfl) ⟨1613645, by rfl⟩ : syracuseStep 2151527 = 3227291) B3227291
theorem B2420473 : Blo 2151435 2420473 := bbase (se 2 (by rfl) ⟨907677, by rfl⟩ : syracuseStep 2420473 = 1815355) (by norm_num)
theorem B3227297 : Blo 2151435 3227297 := bstep (se 2 (by rfl) ⟨1210236, by rfl⟩ : syracuseStep 3227297 = 2420473) B2420473
theorem B2151531 : Blo 2151435 2151531 := bstep (se 1 (by rfl) ⟨1613648, by rfl⟩ : syracuseStep 2151531 = 3227297) B3227297
theorem B50361301 : Blo 2151435 50361301 := bbase (se 7 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 50361301 = 1180343) (by norm_num)
theorem B67148401 : Blo 2151435 67148401 := bstep (se 2 (by rfl) ⟨25180650, by rfl⟩ : syracuseStep 67148401 = 50361301) B50361301
theorem B89531201 : Blo 2151435 89531201 := bstep (se 2 (by rfl) ⟨33574200, by rfl⟩ : syracuseStep 89531201 = 67148401) B67148401
theorem B238749869 : Blo 2151435 238749869 := bstep (se 3 (by rfl) ⟨44765600, by rfl⟩ : syracuseStep 238749869 = 89531201) B89531201
theorem B159166579 : Blo 2151435 159166579 := bstep (se 1 (by rfl) ⟨119374934, by rfl⟩ : syracuseStep 159166579 = 238749869) B238749869
theorem B212222105 : Blo 2151435 212222105 := bstep (se 2 (by rfl) ⟨79583289, by rfl⟩ : syracuseStep 212222105 = 159166579) B159166579
theorem B141481403 : Blo 2151435 141481403 := bstep (se 1 (by rfl) ⟨106111052, by rfl⟩ : syracuseStep 141481403 = 212222105) B212222105
theorem B94320935 : Blo 2151435 94320935 := bstep (se 1 (by rfl) ⟨70740701, by rfl⟩ : syracuseStep 94320935 = 141481403) B141481403
theorem B62880623 : Blo 2151435 62880623 := bstep (se 1 (by rfl) ⟨47160467, by rfl⟩ : syracuseStep 62880623 = 94320935) B94320935
theorem B41920415 : Blo 2151435 41920415 := bstep (se 1 (by rfl) ⟨31440311, by rfl⟩ : syracuseStep 41920415 = 62880623) B62880623
theorem B27946943 : Blo 2151435 27946943 := bstep (se 1 (by rfl) ⟨20960207, by rfl⟩ : syracuseStep 27946943 = 41920415) B41920415
theorem B18631295 : Blo 2151435 18631295 := bstep (se 1 (by rfl) ⟨13973471, by rfl⟩ : syracuseStep 18631295 = 27946943) B27946943
theorem B12420863 : Blo 2151435 12420863 := bstep (se 1 (by rfl) ⟨9315647, by rfl⟩ : syracuseStep 12420863 = 18631295) B18631295
theorem B8280575 : Blo 2151435 8280575 := bstep (se 1 (by rfl) ⟨6210431, by rfl⟩ : syracuseStep 8280575 = 12420863) B12420863
theorem B5520383 : Blo 2151435 5520383 := bstep (se 1 (by rfl) ⟨4140287, by rfl⟩ : syracuseStep 5520383 = 8280575) B8280575
theorem B3680255 : Blo 2151435 3680255 := bstep (se 1 (by rfl) ⟨2760191, by rfl⟩ : syracuseStep 3680255 = 5520383) B5520383
theorem B2453503 : Blo 2151435 2453503 := bstep (se 1 (by rfl) ⟨1840127, by rfl⟩ : syracuseStep 2453503 = 3680255) B3680255
theorem B3271337 : Blo 2151435 3271337 := bstep (se 2 (by rfl) ⟨1226751, by rfl⟩ : syracuseStep 3271337 = 2453503) B2453503
theorem B2180891 : Blo 2151435 2180891 := bstep (se 1 (by rfl) ⟨1635668, by rfl⟩ : syracuseStep 2180891 = 3271337) B3271337
theorem B5815709 : Blo 2151435 5815709 := bstep (se 3 (by rfl) ⟨1090445, by rfl⟩ : syracuseStep 5815709 = 2180891) B2180891
theorem B3877139 : Blo 2151435 3877139 := bstep (se 1 (by rfl) ⟨2907854, by rfl⟩ : syracuseStep 3877139 = 5815709) B5815709
theorem B2584759 : Blo 2151435 2584759 := bstep (se 1 (by rfl) ⟨1938569, by rfl⟩ : syracuseStep 2584759 = 3877139) B3877139
theorem B3446345 : Blo 2151435 3446345 := bstep (se 2 (by rfl) ⟨1292379, by rfl⟩ : syracuseStep 3446345 = 2584759) B2584759
theorem B9190253 : Blo 2151435 9190253 := bstep (se 3 (by rfl) ⟨1723172, by rfl⟩ : syracuseStep 9190253 = 3446345) B3446345
theorem B6126835 : Blo 2151435 6126835 := bstep (se 1 (by rfl) ⟨4595126, by rfl⟩ : syracuseStep 6126835 = 9190253) B9190253
theorem B8169113 : Blo 2151435 8169113 := bstep (se 2 (by rfl) ⟨3063417, by rfl⟩ : syracuseStep 8169113 = 6126835) B6126835
theorem B5446075 : Blo 2151435 5446075 := bstep (se 1 (by rfl) ⟨4084556, by rfl⟩ : syracuseStep 5446075 = 8169113) B8169113
theorem B7261433 : Blo 2151435 7261433 := bstep (se 2 (by rfl) ⟨2723037, by rfl⟩ : syracuseStep 7261433 = 5446075) B5446075
theorem B4840955 : Blo 2151435 4840955 := bstep (se 1 (by rfl) ⟨3630716, by rfl⟩ : syracuseStep 4840955 = 7261433) B7261433
theorem B3227303 : Blo 2151435 3227303 := bstep (se 1 (by rfl) ⟨2420477, by rfl⟩ : syracuseStep 3227303 = 4840955) B4840955
theorem B2151535 : Blo 2151435 2151535 := bstep (se 1 (by rfl) ⟨1613651, by rfl⟩ : syracuseStep 2151535 = 3227303) B3227303
theorem B3227309 : Blo 2151435 3227309 := bbase (se 3 (by rfl) ⟨605120, by rfl⟩ : syracuseStep 3227309 = 1210241) (by norm_num)
theorem B2151539 : Blo 2151435 2151539 := bstep (se 1 (by rfl) ⟨1613654, by rfl⟩ : syracuseStep 2151539 = 3227309) B3227309
theorem B4840973 : Blo 2151435 4840973 := bbase (se 3 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 4840973 = 1815365) (by norm_num)
theorem B3227315 : Blo 2151435 3227315 := bstep (se 1 (by rfl) ⟨2420486, by rfl⟩ : syracuseStep 3227315 = 4840973) B4840973
theorem B2151543 : Blo 2151435 2151543 := bstep (se 1 (by rfl) ⟨1613657, by rfl⟩ : syracuseStep 2151543 = 3227315) B3227315
theorem B2723053 : Blo 2151435 2723053 := bbase (se 3 (by rfl) ⟨510572, by rfl⟩ : syracuseStep 2723053 = 1021145) (by norm_num)
theorem B3630737 : Blo 2151435 3630737 := bstep (se 2 (by rfl) ⟨1361526, by rfl⟩ : syracuseStep 3630737 = 2723053) B2723053
theorem B2420491 : Blo 2151435 2420491 := bstep (se 1 (by rfl) ⟨1815368, by rfl⟩ : syracuseStep 2420491 = 3630737) B3630737
theorem B3227321 : Blo 2151435 3227321 := bstep (se 2 (by rfl) ⟨1210245, by rfl⟩ : syracuseStep 3227321 = 2420491) B2420491
theorem B2151547 : Blo 2151435 2151547 := bstep (se 1 (by rfl) ⟨1613660, by rfl⟩ : syracuseStep 2151547 = 3227321) B3227321
theorem B4973989 : Blo 2151435 4973989 := bbase (se 4 (by rfl) ⟨466311, by rfl⟩ : syracuseStep 4973989 = 932623) (by norm_num)
theorem B6631985 : Blo 2151435 6631985 := bstep (se 2 (by rfl) ⟨2486994, by rfl⟩ : syracuseStep 6631985 = 4973989) B4973989
theorem B4421323 : Blo 2151435 4421323 := bstep (se 1 (by rfl) ⟨3315992, by rfl⟩ : syracuseStep 4421323 = 6631985) B6631985
theorem B23580389 : Blo 2151435 23580389 := bstep (se 4 (by rfl) ⟨2210661, by rfl⟩ : syracuseStep 23580389 = 4421323) B4421323
theorem B15720259 : Blo 2151435 15720259 := bstep (se 1 (by rfl) ⟨11790194, by rfl⟩ : syracuseStep 15720259 = 23580389) B23580389
theorem B20960345 : Blo 2151435 20960345 := bstep (se 2 (by rfl) ⟨7860129, by rfl⟩ : syracuseStep 20960345 = 15720259) B15720259
theorem B13973563 : Blo 2151435 13973563 := bstep (se 1 (by rfl) ⟨10480172, by rfl⟩ : syracuseStep 13973563 = 20960345) B20960345
theorem B74525669 : Blo 2151435 74525669 := bstep (se 4 (by rfl) ⟨6986781, by rfl⟩ : syracuseStep 74525669 = 13973563) B13973563
theorem B49683779 : Blo 2151435 49683779 := bstep (se 1 (by rfl) ⟨37262834, by rfl⟩ : syracuseStep 49683779 = 74525669) B74525669
theorem B33122519 : Blo 2151435 33122519 := bstep (se 1 (by rfl) ⟨24841889, by rfl⟩ : syracuseStep 33122519 = 49683779) B49683779
theorem B22081679 : Blo 2151435 22081679 := bstep (se 1 (by rfl) ⟨16561259, by rfl⟩ : syracuseStep 22081679 = 33122519) B33122519
theorem B14721119 : Blo 2151435 14721119 := bstep (se 1 (by rfl) ⟨11040839, by rfl⟩ : syracuseStep 14721119 = 22081679) B22081679
theorem B9814079 : Blo 2151435 9814079 := bstep (se 1 (by rfl) ⟨7360559, by rfl⟩ : syracuseStep 9814079 = 14721119) B14721119
theorem B26170877 : Blo 2151435 26170877 := bstep (se 3 (by rfl) ⟨4907039, by rfl⟩ : syracuseStep 26170877 = 9814079) B9814079
theorem B17447251 : Blo 2151435 17447251 := bstep (se 1 (by rfl) ⟨13085438, by rfl⟩ : syracuseStep 17447251 = 26170877) B26170877
theorem B23263001 : Blo 2151435 23263001 := bstep (se 2 (by rfl) ⟨8723625, by rfl⟩ : syracuseStep 23263001 = 17447251) B17447251
theorem B15508667 : Blo 2151435 15508667 := bstep (se 1 (by rfl) ⟨11631500, by rfl⟩ : syracuseStep 15508667 = 23263001) B23263001
theorem B10339111 : Blo 2151435 10339111 := bstep (se 1 (by rfl) ⟨7754333, by rfl⟩ : syracuseStep 10339111 = 15508667) B15508667
theorem B13785481 : Blo 2151435 13785481 := bstep (se 2 (by rfl) ⟨5169555, by rfl⟩ : syracuseStep 13785481 = 10339111) B10339111
theorem B18380641 : Blo 2151435 18380641 := bstep (se 2 (by rfl) ⟨6892740, by rfl⟩ : syracuseStep 18380641 = 13785481) B13785481
theorem B24507521 : Blo 2151435 24507521 := bstep (se 2 (by rfl) ⟨9190320, by rfl⟩ : syracuseStep 24507521 = 18380641) B18380641
theorem B16338347 : Blo 2151435 16338347 := bstep (se 1 (by rfl) ⟨12253760, by rfl⟩ : syracuseStep 16338347 = 24507521) B24507521
theorem B10892231 : Blo 2151435 10892231 := bstep (se 1 (by rfl) ⟨8169173, by rfl⟩ : syracuseStep 10892231 = 16338347) B16338347
theorem B7261487 : Blo 2151435 7261487 := bstep (se 1 (by rfl) ⟨5446115, by rfl⟩ : syracuseStep 7261487 = 10892231) B10892231
theorem B4840991 : Blo 2151435 4840991 := bstep (se 1 (by rfl) ⟨3630743, by rfl⟩ : syracuseStep 4840991 = 7261487) B7261487
theorem B3227327 : Blo 2151435 3227327 := bstep (se 1 (by rfl) ⟨2420495, by rfl⟩ : syracuseStep 3227327 = 4840991) B4840991
theorem B2151551 : Blo 2151435 2151551 := bstep (se 1 (by rfl) ⟨1613663, by rfl⟩ : syracuseStep 2151551 = 3227327) B3227327
theorem B3227333 : Blo 2151435 3227333 := bbase (se 4 (by rfl) ⟨302562, by rfl⟩ : syracuseStep 3227333 = 605125) (by norm_num)
theorem B2151555 : Blo 2151435 2151555 := bstep (se 1 (by rfl) ⟨1613666, by rfl⟩ : syracuseStep 2151555 = 3227333) B3227333
theorem B3630757 : Blo 2151435 3630757 := bbase (se 4 (by rfl) ⟨340383, by rfl⟩ : syracuseStep 3630757 = 680767) (by norm_num)
theorem B4841009 : Blo 2151435 4841009 := bstep (se 2 (by rfl) ⟨1815378, by rfl⟩ : syracuseStep 4841009 = 3630757) B3630757
theorem B3227339 : Blo 2151435 3227339 := bstep (se 1 (by rfl) ⟨2420504, by rfl⟩ : syracuseStep 3227339 = 4841009) B4841009
theorem B2151559 : Blo 2151435 2151559 := bstep (se 1 (by rfl) ⟨1613669, by rfl⟩ : syracuseStep 2151559 = 3227339) B3227339
theorem B2420509 : Blo 2151435 2420509 := bbase (se 3 (by rfl) ⟨453845, by rfl⟩ : syracuseStep 2420509 = 907691) (by norm_num)
theorem B3227345 : Blo 2151435 3227345 := bstep (se 2 (by rfl) ⟨1210254, by rfl⟩ : syracuseStep 3227345 = 2420509) B2420509
theorem B2151563 : Blo 2151435 2151563 := bstep (se 1 (by rfl) ⟨1613672, by rfl⟩ : syracuseStep 2151563 = 3227345) B3227345
theorem B7261541 : Blo 2151435 7261541 := bbase (se 4 (by rfl) ⟨680769, by rfl⟩ : syracuseStep 7261541 = 1361539) (by norm_num)
theorem B4841027 : Blo 2151435 4841027 := bstep (se 1 (by rfl) ⟨3630770, by rfl⟩ : syracuseStep 4841027 = 7261541) B7261541
theorem B3227351 : Blo 2151435 3227351 := bstep (se 1 (by rfl) ⟨2420513, by rfl⟩ : syracuseStep 3227351 = 4841027) B4841027
theorem B2151567 : Blo 2151435 2151567 := bstep (se 1 (by rfl) ⟨1613675, by rfl⟩ : syracuseStep 2151567 = 3227351) B3227351
theorem B3227357 : Blo 2151435 3227357 := bbase (se 3 (by rfl) ⟨605129, by rfl⟩ : syracuseStep 3227357 = 1210259) (by norm_num)
theorem B2151571 : Blo 2151435 2151571 := bstep (se 1 (by rfl) ⟨1613678, by rfl⟩ : syracuseStep 2151571 = 3227357) B3227357
theorem B4841045 : Blo 2151435 4841045 := bbase (se 8 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 4841045 = 56731) (by norm_num)
theorem B3227363 : Blo 2151435 3227363 := bstep (se 1 (by rfl) ⟨2420522, by rfl⟩ : syracuseStep 3227363 = 4841045) B4841045
theorem B2151575 : Blo 2151435 2151575 := bstep (se 1 (by rfl) ⟨1613681, by rfl⟩ : syracuseStep 2151575 = 3227363) B3227363
theorem B4595221 : Blo 2151435 4595221 := bbase (se 6 (by rfl) ⟨107700, by rfl⟩ : syracuseStep 4595221 = 215401) (by norm_num)
theorem B6126961 : Blo 2151435 6126961 := bstep (se 2 (by rfl) ⟨2297610, by rfl⟩ : syracuseStep 6126961 = 4595221) B4595221
theorem B8169281 : Blo 2151435 8169281 := bstep (se 2 (by rfl) ⟨3063480, by rfl⟩ : syracuseStep 8169281 = 6126961) B6126961
theorem B5446187 : Blo 2151435 5446187 := bstep (se 1 (by rfl) ⟨4084640, by rfl⟩ : syracuseStep 5446187 = 8169281) B8169281
theorem B3630791 : Blo 2151435 3630791 := bstep (se 1 (by rfl) ⟨2723093, by rfl⟩ : syracuseStep 3630791 = 5446187) B5446187
theorem B2420527 : Blo 2151435 2420527 := bstep (se 1 (by rfl) ⟨1815395, by rfl⟩ : syracuseStep 2420527 = 3630791) B3630791
theorem B3227369 : Blo 2151435 3227369 := bstep (se 2 (by rfl) ⟨1210263, by rfl⟩ : syracuseStep 3227369 = 2420527) B2420527
theorem B2151579 : Blo 2151435 2151579 := bstep (se 1 (by rfl) ⟨1613684, by rfl⟩ : syracuseStep 2151579 = 3227369) B3227369
theorem B2453557 : Blo 2151435 2453557 := bbase (se 5 (by rfl) ⟨115010, by rfl⟩ : syracuseStep 2453557 = 230021) (by norm_num)
theorem B3271409 : Blo 2151435 3271409 := bstep (se 2 (by rfl) ⟨1226778, by rfl⟩ : syracuseStep 3271409 = 2453557) B2453557
theorem B2180939 : Blo 2151435 2180939 := bstep (se 1 (by rfl) ⟨1635704, by rfl⟩ : syracuseStep 2180939 = 3271409) B3271409
theorem B5815837 : Blo 2151435 5815837 := bstep (se 3 (by rfl) ⟨1090469, by rfl⟩ : syracuseStep 5815837 = 2180939) B2180939
theorem B7754449 : Blo 2151435 7754449 := bstep (se 2 (by rfl) ⟨2907918, by rfl⟩ : syracuseStep 7754449 = 5815837) B5815837
theorem B10339265 : Blo 2151435 10339265 := bstep (se 2 (by rfl) ⟨3877224, by rfl⟩ : syracuseStep 10339265 = 7754449) B7754449
theorem B27571373 : Blo 2151435 27571373 := bstep (se 3 (by rfl) ⟨5169632, by rfl⟩ : syracuseStep 27571373 = 10339265) B10339265
theorem B18380915 : Blo 2151435 18380915 := bstep (se 1 (by rfl) ⟨13785686, by rfl⟩ : syracuseStep 18380915 = 27571373) B27571373
theorem B12253943 : Blo 2151435 12253943 := bstep (se 1 (by rfl) ⟨9190457, by rfl⟩ : syracuseStep 12253943 = 18380915) B18380915
theorem B8169295 : Blo 2151435 8169295 := bstep (se 1 (by rfl) ⟨6126971, by rfl⟩ : syracuseStep 8169295 = 12253943) B12253943
theorem B10892393 : Blo 2151435 10892393 := bstep (se 2 (by rfl) ⟨4084647, by rfl⟩ : syracuseStep 10892393 = 8169295) B8169295
theorem B7261595 : Blo 2151435 7261595 := bstep (se 1 (by rfl) ⟨5446196, by rfl⟩ : syracuseStep 7261595 = 10892393) B10892393
theorem B4841063 : Blo 2151435 4841063 := bstep (se 1 (by rfl) ⟨3630797, by rfl⟩ : syracuseStep 4841063 = 7261595) B7261595
theorem B3227375 : Blo 2151435 3227375 := bstep (se 1 (by rfl) ⟨2420531, by rfl⟩ : syracuseStep 3227375 = 4841063) B4841063
theorem B2151583 : Blo 2151435 2151583 := bstep (se 1 (by rfl) ⟨1613687, by rfl⟩ : syracuseStep 2151583 = 3227375) B3227375
theorem B3227381 : Blo 2151435 3227381 := bbase (se 5 (by rfl) ⟨151283, by rfl⟩ : syracuseStep 3227381 = 302567) (by norm_num)
theorem B2151587 : Blo 2151435 2151587 := bstep (se 1 (by rfl) ⟨1613690, by rfl⟩ : syracuseStep 2151587 = 3227381) B3227381
theorem B5169653 : Blo 2151435 5169653 := bbase (se 5 (by rfl) ⟨242327, by rfl⟩ : syracuseStep 5169653 = 484655) (by norm_num)
theorem B3446435 : Blo 2151435 3446435 := bstep (se 1 (by rfl) ⟨2584826, by rfl⟩ : syracuseStep 3446435 = 5169653) B5169653
theorem B9190493 : Blo 2151435 9190493 := bstep (se 3 (by rfl) ⟨1723217, by rfl⟩ : syracuseStep 9190493 = 3446435) B3446435
theorem B6126995 : Blo 2151435 6126995 := bstep (se 1 (by rfl) ⟨4595246, by rfl⟩ : syracuseStep 6126995 = 9190493) B9190493
theorem B4084663 : Blo 2151435 4084663 := bstep (se 1 (by rfl) ⟨3063497, by rfl⟩ : syracuseStep 4084663 = 6126995) B6126995
theorem B5446217 : Blo 2151435 5446217 := bstep (se 2 (by rfl) ⟨2042331, by rfl⟩ : syracuseStep 5446217 = 4084663) B4084663
theorem B3630811 : Blo 2151435 3630811 := bstep (se 1 (by rfl) ⟨2723108, by rfl⟩ : syracuseStep 3630811 = 5446217) B5446217
theorem B4841081 : Blo 2151435 4841081 := bstep (se 2 (by rfl) ⟨1815405, by rfl⟩ : syracuseStep 4841081 = 3630811) B3630811
theorem B3227387 : Blo 2151435 3227387 := bstep (se 1 (by rfl) ⟨2420540, by rfl⟩ : syracuseStep 3227387 = 4841081) B4841081
theorem B2151591 : Blo 2151435 2151591 := bstep (se 1 (by rfl) ⟨1613693, by rfl⟩ : syracuseStep 2151591 = 3227387) B3227387
theorem B2420545 : Blo 2151435 2420545 := bbase (se 2 (by rfl) ⟨907704, by rfl⟩ : syracuseStep 2420545 = 1815409) (by norm_num)
theorem B3227393 : Blo 2151435 3227393 := bstep (se 2 (by rfl) ⟨1210272, by rfl⟩ : syracuseStep 3227393 = 2420545) B2420545
theorem B2151595 : Blo 2151435 2151595 := bstep (se 1 (by rfl) ⟨1613696, by rfl⟩ : syracuseStep 2151595 = 3227393) B3227393
theorem B5446237 : Blo 2151435 5446237 := bbase (se 3 (by rfl) ⟨1021169, by rfl⟩ : syracuseStep 5446237 = 2042339) (by norm_num)
theorem B7261649 : Blo 2151435 7261649 := bstep (se 2 (by rfl) ⟨2723118, by rfl⟩ : syracuseStep 7261649 = 5446237) B5446237
theorem B4841099 : Blo 2151435 4841099 := bstep (se 1 (by rfl) ⟨3630824, by rfl⟩ : syracuseStep 4841099 = 7261649) B7261649
theorem B3227399 : Blo 2151435 3227399 := bstep (se 1 (by rfl) ⟨2420549, by rfl⟩ : syracuseStep 3227399 = 4841099) B4841099
theorem B2151599 : Blo 2151435 2151599 := bstep (se 1 (by rfl) ⟨1613699, by rfl⟩ : syracuseStep 2151599 = 3227399) B3227399
theorem B3227405 : Blo 2151435 3227405 := bbase (se 3 (by rfl) ⟨605138, by rfl⟩ : syracuseStep 3227405 = 1210277) (by norm_num)
theorem B2151603 : Blo 2151435 2151603 := bstep (se 1 (by rfl) ⟨1613702, by rfl⟩ : syracuseStep 2151603 = 3227405) B3227405
theorem B4841117 : Blo 2151435 4841117 := bbase (se 3 (by rfl) ⟨907709, by rfl⟩ : syracuseStep 4841117 = 1815419) (by norm_num)
theorem B3227411 : Blo 2151435 3227411 := bstep (se 1 (by rfl) ⟨2420558, by rfl⟩ : syracuseStep 3227411 = 4841117) B4841117
theorem B2151607 : Blo 2151435 2151607 := bstep (se 1 (by rfl) ⟨1613705, by rfl⟩ : syracuseStep 2151607 = 3227411) B3227411
theorem B3630845 : Blo 2151435 3630845 := bbase (se 3 (by rfl) ⟨680783, by rfl⟩ : syracuseStep 3630845 = 1361567) (by norm_num)
theorem B2420563 : Blo 2151435 2420563 := bstep (se 1 (by rfl) ⟨1815422, by rfl⟩ : syracuseStep 2420563 = 3630845) B3630845
theorem B3227417 : Blo 2151435 3227417 := bstep (se 2 (by rfl) ⟨1210281, by rfl⟩ : syracuseStep 3227417 = 2420563) B2420563
theorem B2151611 : Blo 2151435 2151611 := bstep (se 1 (by rfl) ⟨1613708, by rfl⟩ : syracuseStep 2151611 = 3227417) B3227417
theorem B5815925 : Blo 2151435 5815925 := bbase (se 5 (by rfl) ⟨272621, by rfl⟩ : syracuseStep 5815925 = 545243) (by norm_num)
theorem B3877283 : Blo 2151435 3877283 := bstep (se 1 (by rfl) ⟨2907962, by rfl⟩ : syracuseStep 3877283 = 5815925) B5815925
theorem B2584855 : Blo 2151435 2584855 := bstep (se 1 (by rfl) ⟨1938641, by rfl⟩ : syracuseStep 2584855 = 3877283) B3877283
theorem B3446473 : Blo 2151435 3446473 := bstep (se 2 (by rfl) ⟨1292427, by rfl⟩ : syracuseStep 3446473 = 2584855) B2584855
theorem B4595297 : Blo 2151435 4595297 := bstep (se 2 (by rfl) ⟨1723236, by rfl⟩ : syracuseStep 4595297 = 3446473) B3446473
theorem B12254125 : Blo 2151435 12254125 := bstep (se 3 (by rfl) ⟨2297648, by rfl⟩ : syracuseStep 12254125 = 4595297) B4595297
theorem B16338833 : Blo 2151435 16338833 := bstep (se 2 (by rfl) ⟨6127062, by rfl⟩ : syracuseStep 16338833 = 12254125) B12254125
theorem B10892555 : Blo 2151435 10892555 := bstep (se 1 (by rfl) ⟨8169416, by rfl⟩ : syracuseStep 10892555 = 16338833) B16338833
theorem B7261703 : Blo 2151435 7261703 := bstep (se 1 (by rfl) ⟨5446277, by rfl⟩ : syracuseStep 7261703 = 10892555) B10892555
theorem B4841135 : Blo 2151435 4841135 := bstep (se 1 (by rfl) ⟨3630851, by rfl⟩ : syracuseStep 4841135 = 7261703) B7261703
theorem B3227423 : Blo 2151435 3227423 := bstep (se 1 (by rfl) ⟨2420567, by rfl⟩ : syracuseStep 3227423 = 4841135) B4841135
theorem B2151615 : Blo 2151435 2151615 := bstep (se 1 (by rfl) ⟨1613711, by rfl⟩ : syracuseStep 2151615 = 3227423) B3227423
theorem B3227429 : Blo 2151435 3227429 := bbase (se 4 (by rfl) ⟨302571, by rfl⟩ : syracuseStep 3227429 = 605143) (by norm_num)
theorem B2151619 : Blo 2151435 2151619 := bstep (se 1 (by rfl) ⟨1613714, by rfl⟩ : syracuseStep 2151619 = 3227429) B3227429
theorem B2723149 : Blo 2151435 2723149 := bbase (se 3 (by rfl) ⟨510590, by rfl⟩ : syracuseStep 2723149 = 1021181) (by norm_num)
theorem B3630865 : Blo 2151435 3630865 := bstep (se 2 (by rfl) ⟨1361574, by rfl⟩ : syracuseStep 3630865 = 2723149) B2723149
theorem B4841153 : Blo 2151435 4841153 := bstep (se 2 (by rfl) ⟨1815432, by rfl⟩ : syracuseStep 4841153 = 3630865) B3630865
theorem B3227435 : Blo 2151435 3227435 := bstep (se 1 (by rfl) ⟨2420576, by rfl⟩ : syracuseStep 3227435 = 4841153) B4841153
theorem B2151623 : Blo 2151435 2151623 := bstep (se 1 (by rfl) ⟨1613717, by rfl⟩ : syracuseStep 2151623 = 3227435) B3227435
theorem B2420581 : Blo 2151435 2420581 := bbase (se 4 (by rfl) ⟨226929, by rfl⟩ : syracuseStep 2420581 = 453859) (by norm_num)
theorem B3227441 : Blo 2151435 3227441 := bstep (se 2 (by rfl) ⟨1210290, by rfl⟩ : syracuseStep 3227441 = 2420581) B2420581
theorem B2151627 : Blo 2151435 2151627 := bstep (se 1 (by rfl) ⟨1613720, by rfl⟩ : syracuseStep 2151627 = 3227441) B3227441
theorem B6127109 : Blo 2151435 6127109 := bbase (se 4 (by rfl) ⟨574416, by rfl⟩ : syracuseStep 6127109 = 1148833) (by norm_num)
theorem B4084739 : Blo 2151435 4084739 := bstep (se 1 (by rfl) ⟨3063554, by rfl⟩ : syracuseStep 4084739 = 6127109) B6127109
theorem B2723159 : Blo 2151435 2723159 := bstep (se 1 (by rfl) ⟨2042369, by rfl⟩ : syracuseStep 2723159 = 4084739) B4084739
theorem B7261757 : Blo 2151435 7261757 := bstep (se 3 (by rfl) ⟨1361579, by rfl⟩ : syracuseStep 7261757 = 2723159) B2723159
theorem B4841171 : Blo 2151435 4841171 := bstep (se 1 (by rfl) ⟨3630878, by rfl⟩ : syracuseStep 4841171 = 7261757) B7261757
theorem B3227447 : Blo 2151435 3227447 := bstep (se 1 (by rfl) ⟨2420585, by rfl⟩ : syracuseStep 3227447 = 4841171) B4841171
theorem B2151631 : Blo 2151435 2151631 := bstep (se 1 (by rfl) ⟨1613723, by rfl⟩ : syracuseStep 2151631 = 3227447) B3227447
theorem B3227453 : Blo 2151435 3227453 := bbase (se 3 (by rfl) ⟨605147, by rfl⟩ : syracuseStep 3227453 = 1210295) (by norm_num)
theorem B2151635 : Blo 2151435 2151635 := bstep (se 1 (by rfl) ⟨1613726, by rfl⟩ : syracuseStep 2151635 = 3227453) B3227453
theorem B4841189 : Blo 2151435 4841189 := bbase (se 4 (by rfl) ⟨453861, by rfl⟩ : syracuseStep 4841189 = 907723) (by norm_num)
theorem B3227459 : Blo 2151435 3227459 := bstep (se 1 (by rfl) ⟨2420594, by rfl⟩ : syracuseStep 3227459 = 4841189) B4841189
theorem B2151639 : Blo 2151435 2151639 := bstep (se 1 (by rfl) ⟨1613729, by rfl⟩ : syracuseStep 2151639 = 3227459) B3227459
theorem B5446349 : Blo 2151435 5446349 := bbase (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) (by norm_num)
theorem B3630899 : Blo 2151435 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B2420599 : Blo 2151435 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B3227465 : Blo 2151435 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B2151643 : Blo 2151435 2151643 := bstep (se 1 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 2151643 = 3227465) B3227465
theorem B3446525 : Blo 2151435 3446525 := bbase (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) (by norm_num)
theorem B2297683 : Blo 2151435 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B3063577 : Blo 2151435 3063577 := bstep (se 2 (by rfl) ⟨1148841, by rfl⟩ : syracuseStep 3063577 = 2297683) B2297683
theorem B4084769 : Blo 2151435 4084769 := bstep (se 2 (by rfl) ⟨1531788, by rfl⟩ : syracuseStep 4084769 = 3063577) B3063577
theorem B10892717 : Blo 2151435 10892717 := bstep (se 3 (by rfl) ⟨2042384, by rfl⟩ : syracuseStep 10892717 = 4084769) B4084769
theorem B7261811 : Blo 2151435 7261811 := bstep (se 1 (by rfl) ⟨5446358, by rfl⟩ : syracuseStep 7261811 = 10892717) B10892717
theorem B4841207 : Blo 2151435 4841207 := bstep (se 1 (by rfl) ⟨3630905, by rfl⟩ : syracuseStep 4841207 = 7261811) B7261811
theorem B3227471 : Blo 2151435 3227471 := bstep (se 1 (by rfl) ⟨2420603, by rfl⟩ : syracuseStep 3227471 = 4841207) B4841207
theorem B2151647 : Blo 2151435 2151647 := bstep (se 1 (by rfl) ⟨1613735, by rfl⟩ : syracuseStep 2151647 = 3227471) B3227471
theorem B3227477 : Blo 2151435 3227477 := bbase (se 9 (by rfl) ⟨9455, by rfl⟩ : syracuseStep 3227477 = 18911) (by norm_num)
theorem B2151651 : Blo 2151435 2151651 := bstep (se 1 (by rfl) ⟨1613738, by rfl⟩ : syracuseStep 2151651 = 3227477) B3227477
theorem B16562069 : Blo 2151435 16562069 := bbase (se 6 (by rfl) ⟨388173, by rfl⟩ : syracuseStep 16562069 = 776347) (by norm_num)
theorem B11041379 : Blo 2151435 11041379 := bstep (se 1 (by rfl) ⟨8281034, by rfl⟩ : syracuseStep 11041379 = 16562069) B16562069
theorem B7360919 : Blo 2151435 7360919 := bstep (se 1 (by rfl) ⟨5520689, by rfl⟩ : syracuseStep 7360919 = 11041379) B11041379
theorem B4907279 : Blo 2151435 4907279 := bstep (se 1 (by rfl) ⟨3680459, by rfl⟩ : syracuseStep 4907279 = 7360919) B7360919
theorem B3271519 : Blo 2151435 3271519 := bstep (se 1 (by rfl) ⟨2453639, by rfl⟩ : syracuseStep 3271519 = 4907279) B4907279
theorem B4362025 : Blo 2151435 4362025 := bstep (se 2 (by rfl) ⟨1635759, by rfl⟩ : syracuseStep 4362025 = 3271519) B3271519
theorem B5816033 : Blo 2151435 5816033 := bstep (se 2 (by rfl) ⟨2181012, by rfl⟩ : syracuseStep 5816033 = 4362025) B4362025
theorem B3877355 : Blo 2151435 3877355 := bstep (se 1 (by rfl) ⟨2908016, by rfl⟩ : syracuseStep 3877355 = 5816033) B5816033
theorem B10339613 : Blo 2151435 10339613 := bstep (se 3 (by rfl) ⟨1938677, by rfl⟩ : syracuseStep 10339613 = 3877355) B3877355
theorem B6893075 : Blo 2151435 6893075 := bstep (se 1 (by rfl) ⟨5169806, by rfl⟩ : syracuseStep 6893075 = 10339613) B10339613
theorem B4595383 : Blo 2151435 4595383 := bstep (se 1 (by rfl) ⟨3446537, by rfl⟩ : syracuseStep 4595383 = 6893075) B6893075
theorem B6127177 : Blo 2151435 6127177 := bstep (se 2 (by rfl) ⟨2297691, by rfl⟩ : syracuseStep 6127177 = 4595383) B4595383
theorem B8169569 : Blo 2151435 8169569 := bstep (se 2 (by rfl) ⟨3063588, by rfl⟩ : syracuseStep 8169569 = 6127177) B6127177
theorem B5446379 : Blo 2151435 5446379 := bstep (se 1 (by rfl) ⟨4084784, by rfl⟩ : syracuseStep 5446379 = 8169569) B8169569
theorem B3630919 : Blo 2151435 3630919 := bstep (se 1 (by rfl) ⟨2723189, by rfl⟩ : syracuseStep 3630919 = 5446379) B5446379
theorem B4841225 : Blo 2151435 4841225 := bstep (se 2 (by rfl) ⟨1815459, by rfl⟩ : syracuseStep 4841225 = 3630919) B3630919
theorem B3227483 : Blo 2151435 3227483 := bstep (se 1 (by rfl) ⟨2420612, by rfl⟩ : syracuseStep 3227483 = 4841225) B4841225
theorem B2151655 : Blo 2151435 2151655 := bstep (se 1 (by rfl) ⟨1613741, by rfl⟩ : syracuseStep 2151655 = 3227483) B3227483
theorem B2420617 : Blo 2151435 2420617 := bbase (se 2 (by rfl) ⟨907731, by rfl⟩ : syracuseStep 2420617 = 1815463) (by norm_num)
theorem B3227489 : Blo 2151435 3227489 := bstep (se 2 (by rfl) ⟨1210308, by rfl⟩ : syracuseStep 3227489 = 2420617) B2420617
theorem B2151659 : Blo 2151435 2151659 := bstep (se 1 (by rfl) ⟨1613744, by rfl⟩ : syracuseStep 2151659 = 3227489) B3227489
theorem B13264661 : Blo 2151435 13264661 := bbase (se 6 (by rfl) ⟨310890, by rfl⟩ : syracuseStep 13264661 = 621781) (by norm_num)
theorem B8843107 : Blo 2151435 8843107 := bstep (se 1 (by rfl) ⟨6632330, by rfl⟩ : syracuseStep 8843107 = 13264661) B13264661
theorem B11790809 : Blo 2151435 11790809 := bstep (se 2 (by rfl) ⟨4421553, by rfl⟩ : syracuseStep 11790809 = 8843107) B8843107
theorem B7860539 : Blo 2151435 7860539 := bstep (se 1 (by rfl) ⟨5895404, by rfl⟩ : syracuseStep 7860539 = 11790809) B11790809
theorem B5240359 : Blo 2151435 5240359 := bstep (se 1 (by rfl) ⟨3930269, by rfl⟩ : syracuseStep 5240359 = 7860539) B7860539
theorem B6987145 : Blo 2151435 6987145 := bstep (se 2 (by rfl) ⟨2620179, by rfl⟩ : syracuseStep 6987145 = 5240359) B5240359
theorem B9316193 : Blo 2151435 9316193 := bstep (se 2 (by rfl) ⟨3493572, by rfl⟩ : syracuseStep 9316193 = 6987145) B6987145
theorem B24843181 : Blo 2151435 24843181 := bstep (se 3 (by rfl) ⟨4658096, by rfl⟩ : syracuseStep 24843181 = 9316193) B9316193
theorem B33124241 : Blo 2151435 33124241 := bstep (se 2 (by rfl) ⟨12421590, by rfl⟩ : syracuseStep 33124241 = 24843181) B24843181
theorem B88331309 : Blo 2151435 88331309 := bstep (se 3 (by rfl) ⟨16562120, by rfl⟩ : syracuseStep 88331309 = 33124241) B33124241
theorem B58887539 : Blo 2151435 58887539 := bstep (se 1 (by rfl) ⟨44165654, by rfl⟩ : syracuseStep 58887539 = 88331309) B88331309
theorem B39258359 : Blo 2151435 39258359 := bstep (se 1 (by rfl) ⟨29443769, by rfl⟩ : syracuseStep 39258359 = 58887539) B58887539
theorem B26172239 : Blo 2151435 26172239 := bstep (se 1 (by rfl) ⟨19629179, by rfl⟩ : syracuseStep 26172239 = 39258359) B39258359
theorem B69792637 : Blo 2151435 69792637 := bstep (se 3 (by rfl) ⟨13086119, by rfl⟩ : syracuseStep 69792637 = 26172239) B26172239
theorem B93056849 : Blo 2151435 93056849 := bstep (se 2 (by rfl) ⟨34896318, by rfl⟩ : syracuseStep 93056849 = 69792637) B69792637
theorem B62037899 : Blo 2151435 62037899 := bstep (se 1 (by rfl) ⟨46528424, by rfl⟩ : syracuseStep 62037899 = 93056849) B93056849
theorem B41358599 : Blo 2151435 41358599 := bstep (se 1 (by rfl) ⟨31018949, by rfl⟩ : syracuseStep 41358599 = 62037899) B62037899
theorem B27572399 : Blo 2151435 27572399 := bstep (se 1 (by rfl) ⟨20679299, by rfl⟩ : syracuseStep 27572399 = 41358599) B41358599
theorem B18381599 : Blo 2151435 18381599 := bstep (se 1 (by rfl) ⟨13786199, by rfl⟩ : syracuseStep 18381599 = 27572399) B27572399
theorem B12254399 : Blo 2151435 12254399 := bstep (se 1 (by rfl) ⟨9190799, by rfl⟩ : syracuseStep 12254399 = 18381599) B18381599
theorem B8169599 : Blo 2151435 8169599 := bstep (se 1 (by rfl) ⟨6127199, by rfl⟩ : syracuseStep 8169599 = 12254399) B12254399
theorem B5446399 : Blo 2151435 5446399 := bstep (se 1 (by rfl) ⟨4084799, by rfl⟩ : syracuseStep 5446399 = 8169599) B8169599
theorem B7261865 : Blo 2151435 7261865 := bstep (se 2 (by rfl) ⟨2723199, by rfl⟩ : syracuseStep 7261865 = 5446399) B5446399
theorem B4841243 : Blo 2151435 4841243 := bstep (se 1 (by rfl) ⟨3630932, by rfl⟩ : syracuseStep 4841243 = 7261865) B7261865
theorem B3227495 : Blo 2151435 3227495 := bstep (se 1 (by rfl) ⟨2420621, by rfl⟩ : syracuseStep 3227495 = 4841243) B4841243
theorem B2151663 : Blo 2151435 2151663 := bstep (se 1 (by rfl) ⟨1613747, by rfl⟩ : syracuseStep 2151663 = 3227495) B3227495
theorem B3227501 : Blo 2151435 3227501 := bbase (se 3 (by rfl) ⟨605156, by rfl⟩ : syracuseStep 3227501 = 1210313) (by norm_num)
theorem B2151667 : Blo 2151435 2151667 := bstep (se 1 (by rfl) ⟨1613750, by rfl⟩ : syracuseStep 2151667 = 3227501) B3227501
theorem B4841261 : Blo 2151435 4841261 := bbase (se 3 (by rfl) ⟨907736, by rfl⟩ : syracuseStep 4841261 = 1815473) (by norm_num)
theorem B3227507 : Blo 2151435 3227507 := bstep (se 1 (by rfl) ⟨2420630, by rfl⟩ : syracuseStep 3227507 = 4841261) B4841261
theorem B2151671 : Blo 2151435 2151671 := bstep (se 1 (by rfl) ⟨1613753, by rfl⟩ : syracuseStep 2151671 = 3227507) B3227507
theorem B9190853 : Blo 2151435 9190853 := bbase (se 4 (by rfl) ⟨861642, by rfl⟩ : syracuseStep 9190853 = 1723285) (by norm_num)
theorem B6127235 : Blo 2151435 6127235 := bstep (se 1 (by rfl) ⟨4595426, by rfl⟩ : syracuseStep 6127235 = 9190853) B9190853
theorem B4084823 : Blo 2151435 4084823 := bstep (se 1 (by rfl) ⟨3063617, by rfl⟩ : syracuseStep 4084823 = 6127235) B6127235
theorem B2723215 : Blo 2151435 2723215 := bstep (se 1 (by rfl) ⟨2042411, by rfl⟩ : syracuseStep 2723215 = 4084823) B4084823
theorem B3630953 : Blo 2151435 3630953 := bstep (se 2 (by rfl) ⟨1361607, by rfl⟩ : syracuseStep 3630953 = 2723215) B2723215
theorem B2420635 : Blo 2151435 2420635 := bstep (se 1 (by rfl) ⟨1815476, by rfl⟩ : syracuseStep 2420635 = 3630953) B3630953
theorem B3227513 : Blo 2151435 3227513 := bstep (se 2 (by rfl) ⟨1210317, by rfl⟩ : syracuseStep 3227513 = 2420635) B2420635
theorem B2151675 : Blo 2151435 2151675 := bstep (se 1 (by rfl) ⟨1613756, by rfl⟩ : syracuseStep 2151675 = 3227513) B3227513
theorem B6543109 : Blo 2151435 6543109 := bbase (se 4 (by rfl) ⟨613416, by rfl⟩ : syracuseStep 6543109 = 1226833) (by norm_num)
theorem B8724145 : Blo 2151435 8724145 := bstep (se 2 (by rfl) ⟨3271554, by rfl⟩ : syracuseStep 8724145 = 6543109) B6543109
theorem B11632193 : Blo 2151435 11632193 := bstep (se 2 (by rfl) ⟨4362072, by rfl⟩ : syracuseStep 11632193 = 8724145) B8724145
theorem B7754795 : Blo 2151435 7754795 := bstep (se 1 (by rfl) ⟨5816096, by rfl⟩ : syracuseStep 7754795 = 11632193) B11632193
theorem B5169863 : Blo 2151435 5169863 := bstep (se 1 (by rfl) ⟨3877397, by rfl⟩ : syracuseStep 5169863 = 7754795) B7754795
theorem B13786301 : Blo 2151435 13786301 := bstep (se 3 (by rfl) ⟨2584931, by rfl⟩ : syracuseStep 13786301 = 5169863) B5169863
theorem B36763469 : Blo 2151435 36763469 := bstep (se 3 (by rfl) ⟨6893150, by rfl⟩ : syracuseStep 36763469 = 13786301) B13786301
theorem B24508979 : Blo 2151435 24508979 := bstep (se 1 (by rfl) ⟨18381734, by rfl⟩ : syracuseStep 24508979 = 36763469) B36763469
theorem B16339319 : Blo 2151435 16339319 := bstep (se 1 (by rfl) ⟨12254489, by rfl⟩ : syracuseStep 16339319 = 24508979) B24508979
theorem B10892879 : Blo 2151435 10892879 := bstep (se 1 (by rfl) ⟨8169659, by rfl⟩ : syracuseStep 10892879 = 16339319) B16339319
theorem B7261919 : Blo 2151435 7261919 := bstep (se 1 (by rfl) ⟨5446439, by rfl⟩ : syracuseStep 7261919 = 10892879) B10892879
theorem B4841279 : Blo 2151435 4841279 := bstep (se 1 (by rfl) ⟨3630959, by rfl⟩ : syracuseStep 4841279 = 7261919) B7261919
theorem B3227519 : Blo 2151435 3227519 := bstep (se 1 (by rfl) ⟨2420639, by rfl⟩ : syracuseStep 3227519 = 4841279) B4841279
theorem B2151679 : Blo 2151435 2151679 := bstep (se 1 (by rfl) ⟨1613759, by rfl⟩ : syracuseStep 2151679 = 3227519) B3227519
theorem B3227525 : Blo 2151435 3227525 := bbase (se 4 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 3227525 = 605161) (by norm_num)
theorem B2151683 : Blo 2151435 2151683 := bstep (se 1 (by rfl) ⟨1613762, by rfl⟩ : syracuseStep 2151683 = 3227525) B3227525
theorem B3630973 : Blo 2151435 3630973 := bbase (se 3 (by rfl) ⟨680807, by rfl⟩ : syracuseStep 3630973 = 1361615) (by norm_num)
theorem B4841297 : Blo 2151435 4841297 := bstep (se 2 (by rfl) ⟨1815486, by rfl⟩ : syracuseStep 4841297 = 3630973) B3630973
theorem B3227531 : Blo 2151435 3227531 := bstep (se 1 (by rfl) ⟨2420648, by rfl⟩ : syracuseStep 3227531 = 4841297) B4841297
theorem B2151687 : Blo 2151435 2151687 := bstep (se 1 (by rfl) ⟨1613765, by rfl⟩ : syracuseStep 2151687 = 3227531) B3227531
theorem B2420653 : Blo 2151435 2420653 := bbase (se 3 (by rfl) ⟨453872, by rfl⟩ : syracuseStep 2420653 = 907745) (by norm_num)
theorem B3227537 : Blo 2151435 3227537 := bstep (se 2 (by rfl) ⟨1210326, by rfl⟩ : syracuseStep 3227537 = 2420653) B2420653
theorem B2151691 : Blo 2151435 2151691 := bstep (se 1 (by rfl) ⟨1613768, by rfl⟩ : syracuseStep 2151691 = 3227537) B3227537
theorem B7261973 : Blo 2151435 7261973 := bbase (se 6 (by rfl) ⟨170202, by rfl⟩ : syracuseStep 7261973 = 340405) (by norm_num)
theorem B4841315 : Blo 2151435 4841315 := bstep (se 1 (by rfl) ⟨3630986, by rfl⟩ : syracuseStep 4841315 = 7261973) B7261973
theorem B3227543 : Blo 2151435 3227543 := bstep (se 1 (by rfl) ⟨2420657, by rfl⟩ : syracuseStep 3227543 = 4841315) B4841315
theorem B2151695 : Blo 2151435 2151695 := bstep (se 1 (by rfl) ⟨1613771, by rfl⟩ : syracuseStep 2151695 = 3227543) B3227543
theorem B3227549 : Blo 2151435 3227549 := bbase (se 3 (by rfl) ⟨605165, by rfl⟩ : syracuseStep 3227549 = 1210331) (by norm_num)
theorem B2151699 : Blo 2151435 2151699 := bstep (se 1 (by rfl) ⟨1613774, by rfl⟩ : syracuseStep 2151699 = 3227549) B3227549
theorem B4841333 : Blo 2151435 4841333 := bbase (se 5 (by rfl) ⟨226937, by rfl⟩ : syracuseStep 4841333 = 453875) (by norm_num)
theorem B3227555 : Blo 2151435 3227555 := bstep (se 1 (by rfl) ⟨2420666, by rfl⟩ : syracuseStep 3227555 = 4841333) B4841333
theorem B2151703 : Blo 2151435 2151703 := bstep (se 1 (by rfl) ⟨1613777, by rfl⟩ : syracuseStep 2151703 = 3227555) B3227555
theorem B2181065 : Blo 2151435 2181065 := bbase (se 2 (by rfl) ⟨817899, by rfl⟩ : syracuseStep 2181065 = 1635799) (by norm_num)
theorem B5816173 : Blo 2151435 5816173 := bstep (se 3 (by rfl) ⟨1090532, by rfl⟩ : syracuseStep 5816173 = 2181065) B2181065
theorem B7754897 : Blo 2151435 7754897 := bstep (se 2 (by rfl) ⟨2908086, by rfl⟩ : syracuseStep 7754897 = 5816173) B5816173
theorem B20679725 : Blo 2151435 20679725 := bstep (se 3 (by rfl) ⟨3877448, by rfl⟩ : syracuseStep 20679725 = 7754897) B7754897
theorem B13786483 : Blo 2151435 13786483 := bstep (se 1 (by rfl) ⟨10339862, by rfl⟩ : syracuseStep 13786483 = 20679725) B20679725
theorem B18381977 : Blo 2151435 18381977 := bstep (se 2 (by rfl) ⟨6893241, by rfl⟩ : syracuseStep 18381977 = 13786483) B13786483
theorem B12254651 : Blo 2151435 12254651 := bstep (se 1 (by rfl) ⟨9190988, by rfl⟩ : syracuseStep 12254651 = 18381977) B18381977
theorem B8169767 : Blo 2151435 8169767 := bstep (se 1 (by rfl) ⟨6127325, by rfl⟩ : syracuseStep 8169767 = 12254651) B12254651
theorem B5446511 : Blo 2151435 5446511 := bstep (se 1 (by rfl) ⟨4084883, by rfl⟩ : syracuseStep 5446511 = 8169767) B8169767
theorem B3631007 : Blo 2151435 3631007 := bstep (se 1 (by rfl) ⟨2723255, by rfl⟩ : syracuseStep 3631007 = 5446511) B5446511
theorem B2420671 : Blo 2151435 2420671 := bstep (se 1 (by rfl) ⟨1815503, by rfl⟩ : syracuseStep 2420671 = 3631007) B3631007
theorem B3227561 : Blo 2151435 3227561 := bstep (se 2 (by rfl) ⟨1210335, by rfl⟩ : syracuseStep 3227561 = 2420671) B2420671
theorem B2151707 : Blo 2151435 2151707 := bstep (se 1 (by rfl) ⟨1613780, by rfl⟩ : syracuseStep 2151707 = 3227561) B3227561
theorem B8169781 : Blo 2151435 8169781 := bbase (se 5 (by rfl) ⟨382958, by rfl⟩ : syracuseStep 8169781 = 765917) (by norm_num)
theorem B10893041 : Blo 2151435 10893041 := bstep (se 2 (by rfl) ⟨4084890, by rfl⟩ : syracuseStep 10893041 = 8169781) B8169781
theorem B7262027 : Blo 2151435 7262027 := bstep (se 1 (by rfl) ⟨5446520, by rfl⟩ : syracuseStep 7262027 = 10893041) B10893041
theorem B4841351 : Blo 2151435 4841351 := bstep (se 1 (by rfl) ⟨3631013, by rfl⟩ : syracuseStep 4841351 = 7262027) B7262027
theorem B3227567 : Blo 2151435 3227567 := bstep (se 1 (by rfl) ⟨2420675, by rfl⟩ : syracuseStep 3227567 = 4841351) B4841351
theorem B2151711 : Blo 2151435 2151711 := bstep (se 1 (by rfl) ⟨1613783, by rfl⟩ : syracuseStep 2151711 = 3227567) B3227567
theorem B3227573 : Blo 2151435 3227573 := bbase (se 5 (by rfl) ⟨151292, by rfl⟩ : syracuseStep 3227573 = 302585) (by norm_num)
theorem B2151715 : Blo 2151435 2151715 := bstep (se 1 (by rfl) ⟨1613786, by rfl⟩ : syracuseStep 2151715 = 3227573) B3227573
theorem B5446541 : Blo 2151435 5446541 := bbase (se 3 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 5446541 = 2042453) (by norm_num)
theorem B3631027 : Blo 2151435 3631027 := bstep (se 1 (by rfl) ⟨2723270, by rfl⟩ : syracuseStep 3631027 = 5446541) B5446541
theorem B4841369 : Blo 2151435 4841369 := bstep (se 2 (by rfl) ⟨1815513, by rfl⟩ : syracuseStep 4841369 = 3631027) B3631027
theorem B3227579 : Blo 2151435 3227579 := bstep (se 1 (by rfl) ⟨2420684, by rfl⟩ : syracuseStep 3227579 = 4841369) B4841369
theorem B2151719 : Blo 2151435 2151719 := bstep (se 1 (by rfl) ⟨1613789, by rfl⟩ : syracuseStep 2151719 = 3227579) B3227579
theorem B2420689 : Blo 2151435 2420689 := bbase (se 2 (by rfl) ⟨907758, by rfl⟩ : syracuseStep 2420689 = 1815517) (by norm_num)
theorem B3227585 : Blo 2151435 3227585 := bstep (se 2 (by rfl) ⟨1210344, by rfl⟩ : syracuseStep 3227585 = 2420689) B2420689
theorem B2151723 : Blo 2151435 2151723 := bstep (se 1 (by rfl) ⟨1613792, by rfl⟩ : syracuseStep 2151723 = 3227585) B3227585
theorem B3446653 : Blo 2151435 3446653 := bbase (se 3 (by rfl) ⟨646247, by rfl⟩ : syracuseStep 3446653 = 1292495) (by norm_num)
theorem B4595537 : Blo 2151435 4595537 := bstep (se 2 (by rfl) ⟨1723326, by rfl⟩ : syracuseStep 4595537 = 3446653) B3446653
theorem B3063691 : Blo 2151435 3063691 := bstep (se 1 (by rfl) ⟨2297768, by rfl⟩ : syracuseStep 3063691 = 4595537) B4595537
theorem B4084921 : Blo 2151435 4084921 := bstep (se 2 (by rfl) ⟨1531845, by rfl⟩ : syracuseStep 4084921 = 3063691) B3063691
theorem B5446561 : Blo 2151435 5446561 := bstep (se 2 (by rfl) ⟨2042460, by rfl⟩ : syracuseStep 5446561 = 4084921) B4084921
theorem B7262081 : Blo 2151435 7262081 := bstep (se 2 (by rfl) ⟨2723280, by rfl⟩ : syracuseStep 7262081 = 5446561) B5446561
theorem B4841387 : Blo 2151435 4841387 := bstep (se 1 (by rfl) ⟨3631040, by rfl⟩ : syracuseStep 4841387 = 7262081) B7262081
theorem B3227591 : Blo 2151435 3227591 := bstep (se 1 (by rfl) ⟨2420693, by rfl⟩ : syracuseStep 3227591 = 4841387) B4841387
theorem B2151727 : Blo 2151435 2151727 := bstep (se 1 (by rfl) ⟨1613795, by rfl⟩ : syracuseStep 2151727 = 3227591) B3227591
theorem B3227597 : Blo 2151435 3227597 := bbase (se 3 (by rfl) ⟨605174, by rfl⟩ : syracuseStep 3227597 = 1210349) (by norm_num)
theorem B2151731 : Blo 2151435 2151731 := bstep (se 1 (by rfl) ⟨1613798, by rfl⟩ : syracuseStep 2151731 = 3227597) B3227597
theorem B4841405 : Blo 2151435 4841405 := bbase (se 3 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 4841405 = 1815527) (by norm_num)
theorem B3227603 : Blo 2151435 3227603 := bstep (se 1 (by rfl) ⟨2420702, by rfl⟩ : syracuseStep 3227603 = 4841405) B4841405
theorem B2151735 : Blo 2151435 2151735 := bstep (se 1 (by rfl) ⟨1613801, by rfl⟩ : syracuseStep 2151735 = 3227603) B3227603
theorem B3631061 : Blo 2151435 3631061 := bbase (se 7 (by rfl) ⟨42551, by rfl⟩ : syracuseStep 3631061 = 85103) (by norm_num)
theorem B2420707 : Blo 2151435 2420707 := bstep (se 1 (by rfl) ⟨1815530, by rfl⟩ : syracuseStep 2420707 = 3631061) B3631061
theorem B3227609 : Blo 2151435 3227609 := bstep (se 2 (by rfl) ⟨1210353, by rfl⟩ : syracuseStep 3227609 = 2420707) B2420707
theorem B2151739 : Blo 2151435 2151739 := bstep (se 1 (by rfl) ⟨1613804, by rfl⟩ : syracuseStep 2151739 = 3227609) B3227609
theorem B9191141 : Blo 2151435 9191141 := bbase (se 4 (by rfl) ⟨861669, by rfl⟩ : syracuseStep 9191141 = 1723339) (by norm_num)
theorem B6127427 : Blo 2151435 6127427 := bstep (se 1 (by rfl) ⟨4595570, by rfl⟩ : syracuseStep 6127427 = 9191141) B9191141
theorem B16339805 : Blo 2151435 16339805 := bstep (se 3 (by rfl) ⟨3063713, by rfl⟩ : syracuseStep 16339805 = 6127427) B6127427
theorem B10893203 : Blo 2151435 10893203 := bstep (se 1 (by rfl) ⟨8169902, by rfl⟩ : syracuseStep 10893203 = 16339805) B16339805
theorem B7262135 : Blo 2151435 7262135 := bstep (se 1 (by rfl) ⟨5446601, by rfl⟩ : syracuseStep 7262135 = 10893203) B10893203
theorem B4841423 : Blo 2151435 4841423 := bstep (se 1 (by rfl) ⟨3631067, by rfl⟩ : syracuseStep 4841423 = 7262135) B7262135
theorem B3227615 : Blo 2151435 3227615 := bstep (se 1 (by rfl) ⟨2420711, by rfl⟩ : syracuseStep 3227615 = 4841423) B4841423
theorem B2151743 : Blo 2151435 2151743 := bstep (se 1 (by rfl) ⟨1613807, by rfl⟩ : syracuseStep 2151743 = 3227615) B3227615
theorem B3227621 : Blo 2151435 3227621 := bbase (se 4 (by rfl) ⟨302589, by rfl⟩ : syracuseStep 3227621 = 605179) (by norm_num)
theorem B2151747 : Blo 2151435 2151747 := bstep (se 1 (by rfl) ⟨1613810, by rfl⟩ : syracuseStep 2151747 = 3227621) B3227621
theorem B13974869 : Blo 2151435 13974869 := bbase (se 11 (by rfl) ⟨10235, by rfl⟩ : syracuseStep 13974869 = 20471) (by norm_num)
theorem B9316579 : Blo 2151435 9316579 := bstep (se 1 (by rfl) ⟨6987434, by rfl⟩ : syracuseStep 9316579 = 13974869) B13974869
theorem B12422105 : Blo 2151435 12422105 := bstep (se 2 (by rfl) ⟨4658289, by rfl⟩ : syracuseStep 12422105 = 9316579) B9316579
theorem B8281403 : Blo 2151435 8281403 := bstep (se 1 (by rfl) ⟨6211052, by rfl⟩ : syracuseStep 8281403 = 12422105) B12422105
theorem B5520935 : Blo 2151435 5520935 := bstep (se 1 (by rfl) ⟨4140701, by rfl⟩ : syracuseStep 5520935 = 8281403) B8281403
theorem B3680623 : Blo 2151435 3680623 := bstep (se 1 (by rfl) ⟨2760467, by rfl⟩ : syracuseStep 3680623 = 5520935) B5520935
theorem B19629989 : Blo 2151435 19629989 := bstep (se 4 (by rfl) ⟨1840311, by rfl⟩ : syracuseStep 19629989 = 3680623) B3680623
theorem B13086659 : Blo 2151435 13086659 := bstep (se 1 (by rfl) ⟨9814994, by rfl⟩ : syracuseStep 13086659 = 19629989) B19629989
theorem B8724439 : Blo 2151435 8724439 := bstep (se 1 (by rfl) ⟨6543329, by rfl⟩ : syracuseStep 8724439 = 13086659) B13086659
theorem B11632585 : Blo 2151435 11632585 := bstep (se 2 (by rfl) ⟨4362219, by rfl⟩ : syracuseStep 11632585 = 8724439) B8724439
theorem B15510113 : Blo 2151435 15510113 := bstep (se 2 (by rfl) ⟨5816292, by rfl⟩ : syracuseStep 15510113 = 11632585) B11632585
theorem B10340075 : Blo 2151435 10340075 := bstep (se 1 (by rfl) ⟨7755056, by rfl⟩ : syracuseStep 10340075 = 15510113) B15510113
theorem B6893383 : Blo 2151435 6893383 := bstep (se 1 (by rfl) ⟨5170037, by rfl⟩ : syracuseStep 6893383 = 10340075) B10340075
theorem B9191177 : Blo 2151435 9191177 := bstep (se 2 (by rfl) ⟨3446691, by rfl⟩ : syracuseStep 9191177 = 6893383) B6893383
theorem B6127451 : Blo 2151435 6127451 := bstep (se 1 (by rfl) ⟨4595588, by rfl⟩ : syracuseStep 6127451 = 9191177) B9191177
theorem B4084967 : Blo 2151435 4084967 := bstep (se 1 (by rfl) ⟨3063725, by rfl⟩ : syracuseStep 4084967 = 6127451) B6127451
theorem B2723311 : Blo 2151435 2723311 := bstep (se 1 (by rfl) ⟨2042483, by rfl⟩ : syracuseStep 2723311 = 4084967) B4084967
theorem B3631081 : Blo 2151435 3631081 := bstep (se 2 (by rfl) ⟨1361655, by rfl⟩ : syracuseStep 3631081 = 2723311) B2723311
theorem B4841441 : Blo 2151435 4841441 := bstep (se 2 (by rfl) ⟨1815540, by rfl⟩ : syracuseStep 4841441 = 3631081) B3631081
theorem B3227627 : Blo 2151435 3227627 := bstep (se 1 (by rfl) ⟨2420720, by rfl⟩ : syracuseStep 3227627 = 4841441) B4841441
theorem B2151751 : Blo 2151435 2151751 := bstep (se 1 (by rfl) ⟨1613813, by rfl⟩ : syracuseStep 2151751 = 3227627) B3227627
theorem B2420725 : Blo 2151435 2420725 := bbase (se 5 (by rfl) ⟨113471, by rfl⟩ : syracuseStep 2420725 = 226943) (by norm_num)
theorem B3227633 : Blo 2151435 3227633 := bstep (se 2 (by rfl) ⟨1210362, by rfl⟩ : syracuseStep 3227633 = 2420725) B2420725
theorem B2151755 : Blo 2151435 2151755 := bstep (se 1 (by rfl) ⟨1613816, by rfl⟩ : syracuseStep 2151755 = 3227633) B3227633
theorem B2723321 : Blo 2151435 2723321 := bbase (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) (by norm_num)
theorem B7262189 : Blo 2151435 7262189 := bstep (se 3 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 7262189 = 2723321) B2723321
theorem B4841459 : Blo 2151435 4841459 := bstep (se 1 (by rfl) ⟨3631094, by rfl⟩ : syracuseStep 4841459 = 7262189) B7262189
theorem B3227639 : Blo 2151435 3227639 := bstep (se 1 (by rfl) ⟨2420729, by rfl⟩ : syracuseStep 3227639 = 4841459) B4841459
theorem B2151759 : Blo 2151435 2151759 := bstep (se 1 (by rfl) ⟨1613819, by rfl⟩ : syracuseStep 2151759 = 3227639) B3227639
theorem B3227645 : Blo 2151435 3227645 := bbase (se 3 (by rfl) ⟨605183, by rfl⟩ : syracuseStep 3227645 = 1210367) (by norm_num)
theorem B2151763 : Blo 2151435 2151763 := bstep (se 1 (by rfl) ⟨1613822, by rfl⟩ : syracuseStep 2151763 = 3227645) B3227645
theorem B4841477 : Blo 2151435 4841477 := bbase (se 4 (by rfl) ⟨453888, by rfl⟩ : syracuseStep 4841477 = 907777) (by norm_num)
theorem B3227651 : Blo 2151435 3227651 := bstep (se 1 (by rfl) ⟨2420738, by rfl⟩ : syracuseStep 3227651 = 4841477) B4841477
theorem B2151767 : Blo 2151435 2151767 := bstep (se 1 (by rfl) ⟨1613825, by rfl⟩ : syracuseStep 2151767 = 3227651) B3227651
theorem B4085005 : Blo 2151435 4085005 := bbase (se 3 (by rfl) ⟨765938, by rfl⟩ : syracuseStep 4085005 = 1531877) (by norm_num)
theorem B5446673 : Blo 2151435 5446673 := bstep (se 2 (by rfl) ⟨2042502, by rfl⟩ : syracuseStep 5446673 = 4085005) B4085005
theorem B3631115 : Blo 2151435 3631115 := bstep (se 1 (by rfl) ⟨2723336, by rfl⟩ : syracuseStep 3631115 = 5446673) B5446673
theorem B2420743 : Blo 2151435 2420743 := bstep (se 1 (by rfl) ⟨1815557, by rfl⟩ : syracuseStep 2420743 = 3631115) B3631115
theorem B3227657 : Blo 2151435 3227657 := bstep (se 2 (by rfl) ⟨1210371, by rfl⟩ : syracuseStep 3227657 = 2420743) B2420743
theorem B2151771 : Blo 2151435 2151771 := bstep (se 1 (by rfl) ⟨1613828, by rfl⟩ : syracuseStep 2151771 = 3227657) B3227657
theorem B10893365 : Blo 2151435 10893365 := bbase (se 5 (by rfl) ⟨510626, by rfl⟩ : syracuseStep 10893365 = 1021253) (by norm_num)
theorem B7262243 : Blo 2151435 7262243 := bstep (se 1 (by rfl) ⟨5446682, by rfl⟩ : syracuseStep 7262243 = 10893365) B10893365
theorem B4841495 : Blo 2151435 4841495 := bstep (se 1 (by rfl) ⟨3631121, by rfl⟩ : syracuseStep 4841495 = 7262243) B7262243
theorem B3227663 : Blo 2151435 3227663 := bstep (se 1 (by rfl) ⟨2420747, by rfl⟩ : syracuseStep 3227663 = 4841495) B4841495
theorem B2151775 : Blo 2151435 2151775 := bstep (se 1 (by rfl) ⟨1613831, by rfl⟩ : syracuseStep 2151775 = 3227663) B3227663
theorem B3227669 : Blo 2151435 3227669 := bbase (se 6 (by rfl) ⟨75648, by rfl⟩ : syracuseStep 3227669 = 151297) (by norm_num)
theorem B2151779 : Blo 2151435 2151779 := bstep (se 1 (by rfl) ⟨1613834, by rfl⟩ : syracuseStep 2151779 = 3227669) B3227669
theorem B2908189 : Blo 2151435 2908189 := bbase (se 3 (by rfl) ⟨545285, by rfl⟩ : syracuseStep 2908189 = 1090571) (by norm_num)
theorem B15510341 : Blo 2151435 15510341 := bstep (se 4 (by rfl) ⟨1454094, by rfl⟩ : syracuseStep 15510341 = 2908189) B2908189
theorem B10340227 : Blo 2151435 10340227 := bstep (se 1 (by rfl) ⟨7755170, by rfl⟩ : syracuseStep 10340227 = 15510341) B15510341
theorem B13786969 : Blo 2151435 13786969 := bstep (se 2 (by rfl) ⟨5170113, by rfl⟩ : syracuseStep 13786969 = 10340227) B10340227
theorem B18382625 : Blo 2151435 18382625 := bstep (se 2 (by rfl) ⟨6893484, by rfl⟩ : syracuseStep 18382625 = 13786969) B13786969
theorem B12255083 : Blo 2151435 12255083 := bstep (se 1 (by rfl) ⟨9191312, by rfl⟩ : syracuseStep 12255083 = 18382625) B18382625
theorem B8170055 : Blo 2151435 8170055 := bstep (se 1 (by rfl) ⟨6127541, by rfl⟩ : syracuseStep 8170055 = 12255083) B12255083
theorem B5446703 : Blo 2151435 5446703 := bstep (se 1 (by rfl) ⟨4085027, by rfl⟩ : syracuseStep 5446703 = 8170055) B8170055
theorem B3631135 : Blo 2151435 3631135 := bstep (se 1 (by rfl) ⟨2723351, by rfl⟩ : syracuseStep 3631135 = 5446703) B5446703
theorem B4841513 : Blo 2151435 4841513 := bstep (se 2 (by rfl) ⟨1815567, by rfl⟩ : syracuseStep 4841513 = 3631135) B3631135
theorem B3227675 : Blo 2151435 3227675 := bstep (se 1 (by rfl) ⟨2420756, by rfl⟩ : syracuseStep 3227675 = 4841513) B4841513
theorem B2151783 : Blo 2151435 2151783 := bstep (se 1 (by rfl) ⟨1613837, by rfl⟩ : syracuseStep 2151783 = 3227675) B3227675
theorem B2420761 : Blo 2151435 2420761 := bbase (se 2 (by rfl) ⟨907785, by rfl⟩ : syracuseStep 2420761 = 1815571) (by norm_num)
theorem B3227681 : Blo 2151435 3227681 := bstep (se 2 (by rfl) ⟨1210380, by rfl⟩ : syracuseStep 3227681 = 2420761) B2420761
theorem B2151787 : Blo 2151435 2151787 := bstep (se 1 (by rfl) ⟨1613840, by rfl⟩ : syracuseStep 2151787 = 3227681) B3227681
theorem B8170085 : Blo 2151435 8170085 := bbase (se 4 (by rfl) ⟨765945, by rfl⟩ : syracuseStep 8170085 = 1531891) (by norm_num)
theorem B5446723 : Blo 2151435 5446723 := bstep (se 1 (by rfl) ⟨4085042, by rfl⟩ : syracuseStep 5446723 = 8170085) B8170085
theorem B7262297 : Blo 2151435 7262297 := bstep (se 2 (by rfl) ⟨2723361, by rfl⟩ : syracuseStep 7262297 = 5446723) B5446723
theorem B4841531 : Blo 2151435 4841531 := bstep (se 1 (by rfl) ⟨3631148, by rfl⟩ : syracuseStep 4841531 = 7262297) B7262297
theorem B3227687 : Blo 2151435 3227687 := bstep (se 1 (by rfl) ⟨2420765, by rfl⟩ : syracuseStep 3227687 = 4841531) B4841531
theorem B2151791 : Blo 2151435 2151791 := bstep (se 1 (by rfl) ⟨1613843, by rfl⟩ : syracuseStep 2151791 = 3227687) B3227687
theorem B3227693 : Blo 2151435 3227693 := bbase (se 3 (by rfl) ⟨605192, by rfl⟩ : syracuseStep 3227693 = 1210385) (by norm_num)
theorem B2151795 : Blo 2151435 2151795 := bstep (se 1 (by rfl) ⟨1613846, by rfl⟩ : syracuseStep 2151795 = 3227693) B3227693
theorem B4841549 : Blo 2151435 4841549 := bbase (se 3 (by rfl) ⟨907790, by rfl⟩ : syracuseStep 4841549 = 1815581) (by norm_num)
theorem B3227699 : Blo 2151435 3227699 := bstep (se 1 (by rfl) ⟨2420774, by rfl⟩ : syracuseStep 3227699 = 4841549) B4841549
theorem B2151799 : Blo 2151435 2151799 := bstep (se 1 (by rfl) ⟨1613849, by rfl⟩ : syracuseStep 2151799 = 3227699) B3227699
theorem B2723377 : Blo 2151435 2723377 := bbase (se 2 (by rfl) ⟨1021266, by rfl⟩ : syracuseStep 2723377 = 2042533) (by norm_num)
theorem B3631169 : Blo 2151435 3631169 := bstep (se 2 (by rfl) ⟨1361688, by rfl⟩ : syracuseStep 3631169 = 2723377) B2723377
theorem B2420779 : Blo 2151435 2420779 := bstep (se 1 (by rfl) ⟨1815584, by rfl⟩ : syracuseStep 2420779 = 3631169) B3631169
theorem B3227705 : Blo 2151435 3227705 := bstep (se 2 (by rfl) ⟨1210389, by rfl⟩ : syracuseStep 3227705 = 2420779) B2420779
theorem B2151803 : Blo 2151435 2151803 := bstep (se 1 (by rfl) ⟨1613852, by rfl⟩ : syracuseStep 2151803 = 3227705) B3227705
theorem B7461877 : Blo 2151435 7461877 := bbase (se 5 (by rfl) ⟨349775, by rfl⟩ : syracuseStep 7461877 = 699551) (by norm_num)
theorem B9949169 : Blo 2151435 9949169 := bstep (se 2 (by rfl) ⟨3730938, by rfl⟩ : syracuseStep 9949169 = 7461877) B7461877
theorem B6632779 : Blo 2151435 6632779 := bstep (se 1 (by rfl) ⟨4974584, by rfl⟩ : syracuseStep 6632779 = 9949169) B9949169
theorem B8843705 : Blo 2151435 8843705 := bstep (se 2 (by rfl) ⟨3316389, by rfl⟩ : syracuseStep 8843705 = 6632779) B6632779
theorem B5895803 : Blo 2151435 5895803 := bstep (se 1 (by rfl) ⟨4421852, by rfl⟩ : syracuseStep 5895803 = 8843705) B8843705
theorem B3930535 : Blo 2151435 3930535 := bstep (se 1 (by rfl) ⟨2947901, by rfl⟩ : syracuseStep 3930535 = 5895803) B5895803
theorem B5240713 : Blo 2151435 5240713 := bstep (se 2 (by rfl) ⟨1965267, by rfl⟩ : syracuseStep 5240713 = 3930535) B3930535
theorem B6987617 : Blo 2151435 6987617 := bstep (se 2 (by rfl) ⟨2620356, by rfl⟩ : syracuseStep 6987617 = 5240713) B5240713
theorem B4658411 : Blo 2151435 4658411 := bstep (se 1 (by rfl) ⟨3493808, by rfl⟩ : syracuseStep 4658411 = 6987617) B6987617
theorem B3105607 : Blo 2151435 3105607 := bstep (se 1 (by rfl) ⟨2329205, by rfl⟩ : syracuseStep 3105607 = 4658411) B4658411
theorem B4140809 : Blo 2151435 4140809 := bstep (se 2 (by rfl) ⟨1552803, by rfl⟩ : syracuseStep 4140809 = 3105607) B3105607
theorem B2760539 : Blo 2151435 2760539 := bstep (se 1 (by rfl) ⟨2070404, by rfl⟩ : syracuseStep 2760539 = 4140809) B4140809
theorem B7361437 : Blo 2151435 7361437 := bstep (se 3 (by rfl) ⟨1380269, by rfl⟩ : syracuseStep 7361437 = 2760539) B2760539
theorem B9815249 : Blo 2151435 9815249 := bstep (se 2 (by rfl) ⟨3680718, by rfl⟩ : syracuseStep 9815249 = 7361437) B7361437
theorem B6543499 : Blo 2151435 6543499 := bstep (se 1 (by rfl) ⟨4907624, by rfl⟩ : syracuseStep 6543499 = 9815249) B9815249
theorem B8724665 : Blo 2151435 8724665 := bstep (se 2 (by rfl) ⟨3271749, by rfl⟩ : syracuseStep 8724665 = 6543499) B6543499
theorem B5816443 : Blo 2151435 5816443 := bstep (se 1 (by rfl) ⟨4362332, by rfl⟩ : syracuseStep 5816443 = 8724665) B8724665
theorem B7755257 : Blo 2151435 7755257 := bstep (se 2 (by rfl) ⟨2908221, by rfl⟩ : syracuseStep 7755257 = 5816443) B5816443
theorem B5170171 : Blo 2151435 5170171 := bstep (se 1 (by rfl) ⟨3877628, by rfl⟩ : syracuseStep 5170171 = 7755257) B7755257
theorem B6893561 : Blo 2151435 6893561 := bstep (se 2 (by rfl) ⟨2585085, by rfl⟩ : syracuseStep 6893561 = 5170171) B5170171
theorem B4595707 : Blo 2151435 4595707 := bstep (se 1 (by rfl) ⟨3446780, by rfl⟩ : syracuseStep 4595707 = 6893561) B6893561
theorem B24510437 : Blo 2151435 24510437 := bstep (se 4 (by rfl) ⟨2297853, by rfl⟩ : syracuseStep 24510437 = 4595707) B4595707
theorem B16340291 : Blo 2151435 16340291 := bstep (se 1 (by rfl) ⟨12255218, by rfl⟩ : syracuseStep 16340291 = 24510437) B24510437
theorem B10893527 : Blo 2151435 10893527 := bstep (se 1 (by rfl) ⟨8170145, by rfl⟩ : syracuseStep 10893527 = 16340291) B16340291
theorem B7262351 : Blo 2151435 7262351 := bstep (se 1 (by rfl) ⟨5446763, by rfl⟩ : syracuseStep 7262351 = 10893527) B10893527
theorem B4841567 : Blo 2151435 4841567 := bstep (se 1 (by rfl) ⟨3631175, by rfl⟩ : syracuseStep 4841567 = 7262351) B7262351
theorem B3227711 : Blo 2151435 3227711 := bstep (se 1 (by rfl) ⟨2420783, by rfl⟩ : syracuseStep 3227711 = 4841567) B4841567
theorem B2151807 : Blo 2151435 2151807 := bstep (se 1 (by rfl) ⟨1613855, by rfl⟩ : syracuseStep 2151807 = 3227711) B3227711
theorem B3227717 : Blo 2151435 3227717 := bbase (se 4 (by rfl) ⟨302598, by rfl⟩ : syracuseStep 3227717 = 605197) (by norm_num)
theorem B2151811 : Blo 2151435 2151811 := bstep (se 1 (by rfl) ⟨1613858, by rfl⟩ : syracuseStep 2151811 = 3227717) B3227717
theorem B3631189 : Blo 2151435 3631189 := bbase (se 8 (by rfl) ⟨21276, by rfl⟩ : syracuseStep 3631189 = 42553) (by norm_num)
theorem B4841585 : Blo 2151435 4841585 := bstep (se 2 (by rfl) ⟨1815594, by rfl⟩ : syracuseStep 4841585 = 3631189) B3631189
theorem B3227723 : Blo 2151435 3227723 := bstep (se 1 (by rfl) ⟨2420792, by rfl⟩ : syracuseStep 3227723 = 4841585) B4841585
theorem B2151815 : Blo 2151435 2151815 := bstep (se 1 (by rfl) ⟨1613861, by rfl⟩ : syracuseStep 2151815 = 3227723) B3227723
theorem B2420797 : Blo 2151435 2420797 := bbase (se 3 (by rfl) ⟨453899, by rfl⟩ : syracuseStep 2420797 = 907799) (by norm_num)
theorem B3227729 : Blo 2151435 3227729 := bstep (se 2 (by rfl) ⟨1210398, by rfl⟩ : syracuseStep 3227729 = 2420797) B2420797
theorem B2151819 : Blo 2151435 2151819 := bstep (se 1 (by rfl) ⟨1613864, by rfl⟩ : syracuseStep 2151819 = 3227729) B3227729
theorem B7262405 : Blo 2151435 7262405 := bbase (se 4 (by rfl) ⟨680850, by rfl⟩ : syracuseStep 7262405 = 1361701) (by norm_num)
theorem B4841603 : Blo 2151435 4841603 := bstep (se 1 (by rfl) ⟨3631202, by rfl⟩ : syracuseStep 4841603 = 7262405) B7262405
theorem B3227735 : Blo 2151435 3227735 := bstep (se 1 (by rfl) ⟨2420801, by rfl⟩ : syracuseStep 3227735 = 4841603) B4841603
theorem B2151823 : Blo 2151435 2151823 := bstep (se 1 (by rfl) ⟨1613867, by rfl⟩ : syracuseStep 2151823 = 3227735) B3227735
theorem B3227741 : Blo 2151435 3227741 := bbase (se 3 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 3227741 = 1210403) (by norm_num)
theorem B2151827 : Blo 2151435 2151827 := bstep (se 1 (by rfl) ⟨1613870, by rfl⟩ : syracuseStep 2151827 = 3227741) B3227741
theorem B4841621 : Blo 2151435 4841621 := bbase (se 6 (by rfl) ⟨113475, by rfl⟩ : syracuseStep 4841621 = 226951) (by norm_num)
theorem B3227747 : Blo 2151435 3227747 := bstep (se 1 (by rfl) ⟨2420810, by rfl⟩ : syracuseStep 3227747 = 4841621) B4841621
theorem B2151831 : Blo 2151435 2151831 := bstep (se 1 (by rfl) ⟨1613873, by rfl⟩ : syracuseStep 2151831 = 3227747) B3227747
theorem B3063845 : Blo 2151435 3063845 := bbase (se 4 (by rfl) ⟨287235, by rfl⟩ : syracuseStep 3063845 = 574471) (by norm_num)
theorem B8170253 : Blo 2151435 8170253 := bstep (se 3 (by rfl) ⟨1531922, by rfl⟩ : syracuseStep 8170253 = 3063845) B3063845
theorem B5446835 : Blo 2151435 5446835 := bstep (se 1 (by rfl) ⟨4085126, by rfl⟩ : syracuseStep 5446835 = 8170253) B8170253
theorem B3631223 : Blo 2151435 3631223 := bstep (se 1 (by rfl) ⟨2723417, by rfl⟩ : syracuseStep 3631223 = 5446835) B5446835
theorem B2420815 : Blo 2151435 2420815 := bstep (se 1 (by rfl) ⟨1815611, by rfl⟩ : syracuseStep 2420815 = 3631223) B3631223
theorem B3227753 : Blo 2151435 3227753 := bstep (se 2 (by rfl) ⟨1210407, by rfl⟩ : syracuseStep 3227753 = 2420815) B2420815
theorem B2151835 : Blo 2151435 2151835 := bstep (se 1 (by rfl) ⟨1613876, by rfl⟩ : syracuseStep 2151835 = 3227753) B3227753
theorem B4140869 : Blo 2151435 4140869 := bbase (se 4 (by rfl) ⟨388206, by rfl⟩ : syracuseStep 4140869 = 776413) (by norm_num)
theorem B11042317 : Blo 2151435 11042317 := bstep (se 3 (by rfl) ⟨2070434, by rfl⟩ : syracuseStep 11042317 = 4140869) B4140869
theorem B14723089 : Blo 2151435 14723089 := bstep (se 2 (by rfl) ⟨5521158, by rfl⟩ : syracuseStep 14723089 = 11042317) B11042317
theorem B78523141 : Blo 2151435 78523141 := bstep (se 4 (by rfl) ⟨7361544, by rfl⟩ : syracuseStep 78523141 = 14723089) B14723089
theorem B104697521 : Blo 2151435 104697521 := bstep (se 2 (by rfl) ⟨39261570, by rfl⟩ : syracuseStep 104697521 = 78523141) B78523141
theorem B69798347 : Blo 2151435 69798347 := bstep (se 1 (by rfl) ⟨52348760, by rfl⟩ : syracuseStep 69798347 = 104697521) B104697521
theorem B46532231 : Blo 2151435 46532231 := bstep (se 1 (by rfl) ⟨34899173, by rfl⟩ : syracuseStep 46532231 = 69798347) B69798347
theorem B31021487 : Blo 2151435 31021487 := bstep (se 1 (by rfl) ⟨23266115, by rfl⟩ : syracuseStep 31021487 = 46532231) B46532231
theorem B20680991 : Blo 2151435 20680991 := bstep (se 1 (by rfl) ⟨15510743, by rfl⟩ : syracuseStep 20680991 = 31021487) B31021487
theorem B13787327 : Blo 2151435 13787327 := bstep (se 1 (by rfl) ⟨10340495, by rfl⟩ : syracuseStep 13787327 = 20680991) B20680991
theorem B9191551 : Blo 2151435 9191551 := bstep (se 1 (by rfl) ⟨6893663, by rfl⟩ : syracuseStep 9191551 = 13787327) B13787327
theorem B12255401 : Blo 2151435 12255401 := bstep (se 2 (by rfl) ⟨4595775, by rfl⟩ : syracuseStep 12255401 = 9191551) B9191551
theorem B8170267 : Blo 2151435 8170267 := bstep (se 1 (by rfl) ⟨6127700, by rfl⟩ : syracuseStep 8170267 = 12255401) B12255401
theorem B10893689 : Blo 2151435 10893689 := bstep (se 2 (by rfl) ⟨4085133, by rfl⟩ : syracuseStep 10893689 = 8170267) B8170267
theorem B7262459 : Blo 2151435 7262459 := bstep (se 1 (by rfl) ⟨5446844, by rfl⟩ : syracuseStep 7262459 = 10893689) B10893689
theorem B4841639 : Blo 2151435 4841639 := bstep (se 1 (by rfl) ⟨3631229, by rfl⟩ : syracuseStep 4841639 = 7262459) B7262459
theorem B3227759 : Blo 2151435 3227759 := bstep (se 1 (by rfl) ⟨2420819, by rfl⟩ : syracuseStep 3227759 = 4841639) B4841639
theorem B2151839 : Blo 2151435 2151839 := bstep (se 1 (by rfl) ⟨1613879, by rfl⟩ : syracuseStep 2151839 = 3227759) B3227759
theorem B3227765 : Blo 2151435 3227765 := bbase (se 5 (by rfl) ⟨151301, by rfl⟩ : syracuseStep 3227765 = 302603) (by norm_num)
theorem B2151843 : Blo 2151435 2151843 := bstep (se 1 (by rfl) ⟨1613882, by rfl⟩ : syracuseStep 2151843 = 3227765) B3227765
theorem B4085149 : Blo 2151435 4085149 := bbase (se 3 (by rfl) ⟨765965, by rfl⟩ : syracuseStep 4085149 = 1531931) (by norm_num)
theorem B5446865 : Blo 2151435 5446865 := bstep (se 2 (by rfl) ⟨2042574, by rfl⟩ : syracuseStep 5446865 = 4085149) B4085149
theorem B3631243 : Blo 2151435 3631243 := bstep (se 1 (by rfl) ⟨2723432, by rfl⟩ : syracuseStep 3631243 = 5446865) B5446865
theorem B4841657 : Blo 2151435 4841657 := bstep (se 2 (by rfl) ⟨1815621, by rfl⟩ : syracuseStep 4841657 = 3631243) B3631243
theorem B3227771 : Blo 2151435 3227771 := bstep (se 1 (by rfl) ⟨2420828, by rfl⟩ : syracuseStep 3227771 = 4841657) B4841657
theorem B2151847 : Blo 2151435 2151847 := bstep (se 1 (by rfl) ⟨1613885, by rfl⟩ : syracuseStep 2151847 = 3227771) B3227771
theorem B2420833 : Blo 2151435 2420833 := bbase (se 2 (by rfl) ⟨907812, by rfl⟩ : syracuseStep 2420833 = 1815625) (by norm_num)
theorem B3227777 : Blo 2151435 3227777 := bstep (se 2 (by rfl) ⟨1210416, by rfl⟩ : syracuseStep 3227777 = 2420833) B2420833
theorem B2151851 : Blo 2151435 2151851 := bstep (se 1 (by rfl) ⟨1613888, by rfl⟩ : syracuseStep 2151851 = 3227777) B3227777
theorem B5446885 : Blo 2151435 5446885 := bbase (se 4 (by rfl) ⟨510645, by rfl⟩ : syracuseStep 5446885 = 1021291) (by norm_num)
theorem B7262513 : Blo 2151435 7262513 := bstep (se 2 (by rfl) ⟨2723442, by rfl⟩ : syracuseStep 7262513 = 5446885) B5446885
theorem B4841675 : Blo 2151435 4841675 := bstep (se 1 (by rfl) ⟨3631256, by rfl⟩ : syracuseStep 4841675 = 7262513) B7262513
theorem B3227783 : Blo 2151435 3227783 := bstep (se 1 (by rfl) ⟨2420837, by rfl⟩ : syracuseStep 3227783 = 4841675) B4841675
theorem B2151855 : Blo 2151435 2151855 := bstep (se 1 (by rfl) ⟨1613891, by rfl⟩ : syracuseStep 2151855 = 3227783) B3227783
theorem B3227789 : Blo 2151435 3227789 := bbase (se 3 (by rfl) ⟨605210, by rfl⟩ : syracuseStep 3227789 = 1210421) (by norm_num)
theorem B2151859 : Blo 2151435 2151859 := bstep (se 1 (by rfl) ⟨1613894, by rfl⟩ : syracuseStep 2151859 = 3227789) B3227789
theorem B4841693 : Blo 2151435 4841693 := bbase (se 3 (by rfl) ⟨907817, by rfl⟩ : syracuseStep 4841693 = 1815635) (by norm_num)
theorem B3227795 : Blo 2151435 3227795 := bstep (se 1 (by rfl) ⟨2420846, by rfl⟩ : syracuseStep 3227795 = 4841693) B4841693
theorem B2151863 : Blo 2151435 2151863 := bstep (se 1 (by rfl) ⟨1613897, by rfl⟩ : syracuseStep 2151863 = 3227795) B3227795
theorem B3631277 : Blo 2151435 3631277 := bbase (se 3 (by rfl) ⟨680864, by rfl⟩ : syracuseStep 3631277 = 1361729) (by norm_num)
theorem B2420851 : Blo 2151435 2420851 := bstep (se 1 (by rfl) ⟨1815638, by rfl⟩ : syracuseStep 2420851 = 3631277) B3631277
theorem B3227801 : Blo 2151435 3227801 := bstep (se 2 (by rfl) ⟨1210425, by rfl⟩ : syracuseStep 3227801 = 2420851) B2420851
theorem B2151867 : Blo 2151435 2151867 := bstep (se 1 (by rfl) ⟨1613900, by rfl⟩ : syracuseStep 2151867 = 3227801) B3227801
theorem B6211397 : Blo 2151435 6211397 := bbase (se 4 (by rfl) ⟨582318, by rfl⟩ : syracuseStep 6211397 = 1164637) (by norm_num)
theorem B4140931 : Blo 2151435 4140931 := bstep (se 1 (by rfl) ⟨3105698, by rfl⟩ : syracuseStep 4140931 = 6211397) B6211397
theorem B5521241 : Blo 2151435 5521241 := bstep (se 2 (by rfl) ⟨2070465, by rfl⟩ : syracuseStep 5521241 = 4140931) B4140931
theorem B14723309 : Blo 2151435 14723309 := bstep (se 3 (by rfl) ⟨2760620, by rfl⟩ : syracuseStep 14723309 = 5521241) B5521241
theorem B9815539 : Blo 2151435 9815539 := bstep (se 1 (by rfl) ⟨7361654, by rfl⟩ : syracuseStep 9815539 = 14723309) B14723309
theorem B13087385 : Blo 2151435 13087385 := bstep (se 2 (by rfl) ⟨4907769, by rfl⟩ : syracuseStep 13087385 = 9815539) B9815539
theorem B8724923 : Blo 2151435 8724923 := bstep (se 1 (by rfl) ⟨6543692, by rfl⟩ : syracuseStep 8724923 = 13087385) B13087385
theorem B5816615 : Blo 2151435 5816615 := bstep (se 1 (by rfl) ⟨4362461, by rfl⟩ : syracuseStep 5816615 = 8724923) B8724923
theorem B62043893 : Blo 2151435 62043893 := bstep (se 5 (by rfl) ⟨2908307, by rfl⟩ : syracuseStep 62043893 = 5816615) B5816615
theorem B41362595 : Blo 2151435 41362595 := bstep (se 1 (by rfl) ⟨31021946, by rfl⟩ : syracuseStep 41362595 = 62043893) B62043893
theorem B27575063 : Blo 2151435 27575063 := bstep (se 1 (by rfl) ⟨20681297, by rfl⟩ : syracuseStep 27575063 = 41362595) B41362595
theorem B18383375 : Blo 2151435 18383375 := bstep (se 1 (by rfl) ⟨13787531, by rfl⟩ : syracuseStep 18383375 = 27575063) B27575063
theorem B12255583 : Blo 2151435 12255583 := bstep (se 1 (by rfl) ⟨9191687, by rfl⟩ : syracuseStep 12255583 = 18383375) B18383375
theorem B16340777 : Blo 2151435 16340777 := bstep (se 2 (by rfl) ⟨6127791, by rfl⟩ : syracuseStep 16340777 = 12255583) B12255583
theorem B10893851 : Blo 2151435 10893851 := bstep (se 1 (by rfl) ⟨8170388, by rfl⟩ : syracuseStep 10893851 = 16340777) B16340777
theorem B7262567 : Blo 2151435 7262567 := bstep (se 1 (by rfl) ⟨5446925, by rfl⟩ : syracuseStep 7262567 = 10893851) B10893851
theorem B4841711 : Blo 2151435 4841711 := bstep (se 1 (by rfl) ⟨3631283, by rfl⟩ : syracuseStep 4841711 = 7262567) B7262567
theorem B3227807 : Blo 2151435 3227807 := bstep (se 1 (by rfl) ⟨2420855, by rfl⟩ : syracuseStep 3227807 = 4841711) B4841711
theorem B2151871 : Blo 2151435 2151871 := bstep (se 1 (by rfl) ⟨1613903, by rfl⟩ : syracuseStep 2151871 = 3227807) B3227807
theorem B3227813 : Blo 2151435 3227813 := bbase (se 4 (by rfl) ⟨302607, by rfl⟩ : syracuseStep 3227813 = 605215) (by norm_num)
theorem B2151875 : Blo 2151435 2151875 := bstep (se 1 (by rfl) ⟨1613906, by rfl⟩ : syracuseStep 2151875 = 3227813) B3227813
theorem B2723473 : Blo 2151435 2723473 := bbase (se 2 (by rfl) ⟨1021302, by rfl⟩ : syracuseStep 2723473 = 2042605) (by norm_num)
theorem B3631297 : Blo 2151435 3631297 := bstep (se 2 (by rfl) ⟨1361736, by rfl⟩ : syracuseStep 3631297 = 2723473) B2723473
theorem B4841729 : Blo 2151435 4841729 := bstep (se 2 (by rfl) ⟨1815648, by rfl⟩ : syracuseStep 4841729 = 3631297) B3631297
theorem B3227819 : Blo 2151435 3227819 := bstep (se 1 (by rfl) ⟨2420864, by rfl⟩ : syracuseStep 3227819 = 4841729) B4841729
theorem B2151879 : Blo 2151435 2151879 := bstep (se 1 (by rfl) ⟨1613909, by rfl⟩ : syracuseStep 2151879 = 3227819) B3227819
theorem B2420869 : Blo 2151435 2420869 := bbase (se 4 (by rfl) ⟨226956, by rfl⟩ : syracuseStep 2420869 = 453913) (by norm_num)
theorem B3227825 : Blo 2151435 3227825 := bstep (se 2 (by rfl) ⟨1210434, by rfl⟩ : syracuseStep 3227825 = 2420869) B2420869
theorem B2151883 : Blo 2151435 2151883 := bstep (se 1 (by rfl) ⟨1613912, by rfl⟩ : syracuseStep 2151883 = 3227825) B3227825
theorem B2692445 : Blo 2151435 2692445 := bbase (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) (by norm_num)
theorem B7179853 : Blo 2151435 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B9573137 : Blo 2151435 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B6382091 : Blo 2151435 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B17018909 : Blo 2151435 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B11345939 : Blo 2151435 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B7563959 : Blo 2151435 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B5042639 : Blo 2151435 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B13447037 : Blo 2151435 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B35858765 : Blo 2151435 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B23905843 : Blo 2151435 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B127497829 : Blo 2151435 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B169997105 : Blo 2151435 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B113331403 : Blo 2151435 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B151108537 : Blo 2151435 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B201478049 : Blo 2151435 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B134318699 : Blo 2151435 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B89545799 : Blo 2151435 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B59697199 : Blo 2151435 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B79596265 : Blo 2151435 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B106128353 : Blo 2151435 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B283008941 : Blo 2151435 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B188672627 : Blo 2151435 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B125781751 : Blo 2151435 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B167709001 : Blo 2151435 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B223612001 : Blo 2151435 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B149074667 : Blo 2151435 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B99383111 : Blo 2151435 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B66255407 : Blo 2151435 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B44170271 : Blo 2151435 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B29446847 : Blo 2151435 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B19631231 : Blo 2151435 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B13087487 : Blo 2151435 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B8724991 : Blo 2151435 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B11633321 : Blo 2151435 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B7755547 : Blo 2151435 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B10340729 : Blo 2151435 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B6893819 : Blo 2151435 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B4595879 : Blo 2151435 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B3063919 : Blo 2151435 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B4085225 : Blo 2151435 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B2723483 : Blo 2151435 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B7262621 : Blo 2151435 7262621 := bstep (se 3 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 7262621 = 2723483) B2723483
theorem B4841747 : Blo 2151435 4841747 := bstep (se 1 (by rfl) ⟨3631310, by rfl⟩ : syracuseStep 4841747 = 7262621) B7262621
theorem B3227831 : Blo 2151435 3227831 := bstep (se 1 (by rfl) ⟨2420873, by rfl⟩ : syracuseStep 3227831 = 4841747) B4841747
theorem B2151887 : Blo 2151435 2151887 := bstep (se 1 (by rfl) ⟨1613915, by rfl⟩ : syracuseStep 2151887 = 3227831) B3227831
theorem B3227837 : Blo 2151435 3227837 := bbase (se 3 (by rfl) ⟨605219, by rfl⟩ : syracuseStep 3227837 = 1210439) (by norm_num)
theorem B2151891 : Blo 2151435 2151891 := bstep (se 1 (by rfl) ⟨1613918, by rfl⟩ : syracuseStep 2151891 = 3227837) B3227837
theorem B4841765 : Blo 2151435 4841765 := bbase (se 4 (by rfl) ⟨453915, by rfl⟩ : syracuseStep 4841765 = 907831) (by norm_num)
theorem B3227843 : Blo 2151435 3227843 := bstep (se 1 (by rfl) ⟨2420882, by rfl⟩ : syracuseStep 3227843 = 4841765) B4841765
theorem B2151895 : Blo 2151435 2151895 := bstep (se 1 (by rfl) ⟨1613921, by rfl⟩ : syracuseStep 2151895 = 3227843) B3227843
theorem B5446997 : Blo 2151435 5446997 := bbase (se 11 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 5446997 = 7979) (by norm_num)
theorem B3631331 : Blo 2151435 3631331 := bstep (se 1 (by rfl) ⟨2723498, by rfl⟩ : syracuseStep 3631331 = 5446997) B5446997
theorem B2420887 : Blo 2151435 2420887 := bstep (se 1 (by rfl) ⟨1815665, by rfl⟩ : syracuseStep 2420887 = 3631331) B3631331
theorem B3227849 : Blo 2151435 3227849 := bstep (se 2 (by rfl) ⟨1210443, by rfl⟩ : syracuseStep 3227849 = 2420887) B2420887
theorem B2151899 : Blo 2151435 2151899 := bstep (se 1 (by rfl) ⟨1613924, by rfl⟩ : syracuseStep 2151899 = 3227849) B3227849
theorem B2585201 : Blo 2151435 2585201 := bbase (se 2 (by rfl) ⟨969450, by rfl⟩ : syracuseStep 2585201 = 1938901) (by norm_num)
theorem B6893869 : Blo 2151435 6893869 := bstep (se 3 (by rfl) ⟨1292600, by rfl⟩ : syracuseStep 6893869 = 2585201) B2585201
theorem B9191825 : Blo 2151435 9191825 := bstep (se 2 (by rfl) ⟨3446934, by rfl⟩ : syracuseStep 9191825 = 6893869) B6893869
theorem B6127883 : Blo 2151435 6127883 := bstep (se 1 (by rfl) ⟨4595912, by rfl⟩ : syracuseStep 6127883 = 9191825) B9191825
theorem B4085255 : Blo 2151435 4085255 := bstep (se 1 (by rfl) ⟨3063941, by rfl⟩ : syracuseStep 4085255 = 6127883) B6127883
theorem B10894013 : Blo 2151435 10894013 := bstep (se 3 (by rfl) ⟨2042627, by rfl⟩ : syracuseStep 10894013 = 4085255) B4085255
theorem B7262675 : Blo 2151435 7262675 := bstep (se 1 (by rfl) ⟨5447006, by rfl⟩ : syracuseStep 7262675 = 10894013) B10894013
theorem B4841783 : Blo 2151435 4841783 := bstep (se 1 (by rfl) ⟨3631337, by rfl⟩ : syracuseStep 4841783 = 7262675) B7262675
theorem B3227855 : Blo 2151435 3227855 := bstep (se 1 (by rfl) ⟨2420891, by rfl⟩ : syracuseStep 3227855 = 4841783) B4841783
theorem B2151903 : Blo 2151435 2151903 := bstep (se 1 (by rfl) ⟨1613927, by rfl⟩ : syracuseStep 2151903 = 3227855) B3227855
theorem B3227861 : Blo 2151435 3227861 := bbase (se 7 (by rfl) ⟨37826, by rfl⟩ : syracuseStep 3227861 = 75653) (by norm_num)
theorem B2151907 : Blo 2151435 2151907 := bstep (se 1 (by rfl) ⟨1613930, by rfl⟩ : syracuseStep 2151907 = 3227861) B3227861
theorem B2297965 : Blo 2151435 2297965 := bbase (se 3 (by rfl) ⟨430868, by rfl⟩ : syracuseStep 2297965 = 861737) (by norm_num)
theorem B3063953 : Blo 2151435 3063953 := bstep (se 2 (by rfl) ⟨1148982, by rfl⟩ : syracuseStep 3063953 = 2297965) B2297965
theorem B8170541 : Blo 2151435 8170541 := bstep (se 3 (by rfl) ⟨1531976, by rfl⟩ : syracuseStep 8170541 = 3063953) B3063953
theorem B5447027 : Blo 2151435 5447027 := bstep (se 1 (by rfl) ⟨4085270, by rfl⟩ : syracuseStep 5447027 = 8170541) B8170541
theorem B3631351 : Blo 2151435 3631351 := bstep (se 1 (by rfl) ⟨2723513, by rfl⟩ : syracuseStep 3631351 = 5447027) B5447027
theorem B4841801 : Blo 2151435 4841801 := bstep (se 2 (by rfl) ⟨1815675, by rfl⟩ : syracuseStep 4841801 = 3631351) B3631351
theorem B3227867 : Blo 2151435 3227867 := bstep (se 1 (by rfl) ⟨2420900, by rfl⟩ : syracuseStep 3227867 = 4841801) B4841801
theorem B2151911 : Blo 2151435 2151911 := bstep (se 1 (by rfl) ⟨1613933, by rfl⟩ : syracuseStep 2151911 = 3227867) B3227867
theorem B2420905 : Blo 2151435 2420905 := bbase (se 2 (by rfl) ⟨907839, by rfl⟩ : syracuseStep 2420905 = 1815679) (by norm_num)
theorem B3227873 : Blo 2151435 3227873 := bstep (se 2 (by rfl) ⟨1210452, by rfl⟩ : syracuseStep 3227873 = 2420905) B2420905
theorem B2151915 : Blo 2151435 2151915 := bstep (se 1 (by rfl) ⟨1613936, by rfl⟩ : syracuseStep 2151915 = 3227873) B3227873
theorem B9191893 : Blo 2151435 9191893 := bbase (se 7 (by rfl) ⟨107717, by rfl⟩ : syracuseStep 9191893 = 215435) (by norm_num)
theorem B12255857 : Blo 2151435 12255857 := bstep (se 2 (by rfl) ⟨4595946, by rfl⟩ : syracuseStep 12255857 = 9191893) B9191893
theorem B8170571 : Blo 2151435 8170571 := bstep (se 1 (by rfl) ⟨6127928, by rfl⟩ : syracuseStep 8170571 = 12255857) B12255857
theorem B5447047 : Blo 2151435 5447047 := bstep (se 1 (by rfl) ⟨4085285, by rfl⟩ : syracuseStep 5447047 = 8170571) B8170571
theorem B7262729 : Blo 2151435 7262729 := bstep (se 2 (by rfl) ⟨2723523, by rfl⟩ : syracuseStep 7262729 = 5447047) B5447047
theorem B4841819 : Blo 2151435 4841819 := bstep (se 1 (by rfl) ⟨3631364, by rfl⟩ : syracuseStep 4841819 = 7262729) B7262729
theorem B3227879 : Blo 2151435 3227879 := bstep (se 1 (by rfl) ⟨2420909, by rfl⟩ : syracuseStep 3227879 = 4841819) B4841819
theorem B2151919 : Blo 2151435 2151919 := bstep (se 1 (by rfl) ⟨1613939, by rfl⟩ : syracuseStep 2151919 = 3227879) B3227879
theorem B3227885 : Blo 2151435 3227885 := bbase (se 3 (by rfl) ⟨605228, by rfl⟩ : syracuseStep 3227885 = 1210457) (by norm_num)
theorem B2151923 : Blo 2151435 2151923 := bstep (se 1 (by rfl) ⟨1613942, by rfl⟩ : syracuseStep 2151923 = 3227885) B3227885
theorem B4841837 : Blo 2151435 4841837 := bbase (se 3 (by rfl) ⟨907844, by rfl⟩ : syracuseStep 4841837 = 1815689) (by norm_num)
theorem B3227891 : Blo 2151435 3227891 := bstep (se 1 (by rfl) ⟨2420918, by rfl⟩ : syracuseStep 3227891 = 4841837) B4841837
theorem B2151927 : Blo 2151435 2151927 := bstep (se 1 (by rfl) ⟨1613945, by rfl⟩ : syracuseStep 2151927 = 3227891) B3227891
theorem B4085309 : Blo 2151435 4085309 := bbase (se 3 (by rfl) ⟨765995, by rfl⟩ : syracuseStep 4085309 = 1531991) (by norm_num)
theorem B2723539 : Blo 2151435 2723539 := bstep (se 1 (by rfl) ⟨2042654, by rfl⟩ : syracuseStep 2723539 = 4085309) B4085309
theorem B3631385 : Blo 2151435 3631385 := bstep (se 2 (by rfl) ⟨1361769, by rfl⟩ : syracuseStep 3631385 = 2723539) B2723539
theorem B2420923 : Blo 2151435 2420923 := bstep (se 1 (by rfl) ⟨1815692, by rfl⟩ : syracuseStep 2420923 = 3631385) B3631385
theorem B3227897 : Blo 2151435 3227897 := bstep (se 2 (by rfl) ⟨1210461, by rfl⟩ : syracuseStep 3227897 = 2420923) B2420923
theorem B2151931 : Blo 2151435 2151931 := bstep (se 1 (by rfl) ⟨1613948, by rfl⟩ : syracuseStep 2151931 = 3227897) B3227897
theorem B5816789 : Blo 2151435 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B3877859 : Blo 2151435 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B2585239 : Blo 2151435 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B55151765 : Blo 2151435 55151765 := bstep (se 6 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 55151765 = 2585239) B2585239
theorem B36767843 : Blo 2151435 36767843 := bstep (se 1 (by rfl) ⟨27575882, by rfl⟩ : syracuseStep 36767843 = 55151765) B55151765
theorem B24511895 : Blo 2151435 24511895 := bstep (se 1 (by rfl) ⟨18383921, by rfl⟩ : syracuseStep 24511895 = 36767843) B36767843
theorem B16341263 : Blo 2151435 16341263 := bstep (se 1 (by rfl) ⟨12255947, by rfl⟩ : syracuseStep 16341263 = 24511895) B24511895
theorem B10894175 : Blo 2151435 10894175 := bstep (se 1 (by rfl) ⟨8170631, by rfl⟩ : syracuseStep 10894175 = 16341263) B16341263
theorem B7262783 : Blo 2151435 7262783 := bstep (se 1 (by rfl) ⟨5447087, by rfl⟩ : syracuseStep 7262783 = 10894175) B10894175
theorem B4841855 : Blo 2151435 4841855 := bstep (se 1 (by rfl) ⟨3631391, by rfl⟩ : syracuseStep 4841855 = 7262783) B7262783
theorem B3227903 : Blo 2151435 3227903 := bstep (se 1 (by rfl) ⟨2420927, by rfl⟩ : syracuseStep 3227903 = 4841855) B4841855
theorem B2151935 : Blo 2151435 2151935 := bstep (se 1 (by rfl) ⟨1613951, by rfl⟩ : syracuseStep 2151935 = 3227903) B3227903
theorem B3227909 : Blo 2151435 3227909 := bbase (se 4 (by rfl) ⟨302616, by rfl⟩ : syracuseStep 3227909 = 605233) (by norm_num)
theorem B2151939 : Blo 2151435 2151939 := bstep (se 1 (by rfl) ⟨1613954, by rfl⟩ : syracuseStep 2151939 = 3227909) B3227909
theorem B3631405 : Blo 2151435 3631405 := bbase (se 3 (by rfl) ⟨680888, by rfl⟩ : syracuseStep 3631405 = 1361777) (by norm_num)
theorem B4841873 : Blo 2151435 4841873 := bstep (se 2 (by rfl) ⟨1815702, by rfl⟩ : syracuseStep 4841873 = 3631405) B3631405
theorem B3227915 : Blo 2151435 3227915 := bstep (se 1 (by rfl) ⟨2420936, by rfl⟩ : syracuseStep 3227915 = 4841873) B4841873
theorem B2151943 : Blo 2151435 2151943 := bstep (se 1 (by rfl) ⟨1613957, by rfl⟩ : syracuseStep 2151943 = 3227915) B3227915
theorem B2420941 : Blo 2151435 2420941 := bbase (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) (by norm_num)
theorem B3227921 : Blo 2151435 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B2151947 : Blo 2151435 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B7262837 : Blo 2151435 7262837 := bbase (se 5 (by rfl) ⟨340445, by rfl⟩ : syracuseStep 7262837 = 680891) (by norm_num)
theorem B4841891 : Blo 2151435 4841891 := bstep (se 1 (by rfl) ⟨3631418, by rfl⟩ : syracuseStep 4841891 = 7262837) B7262837
theorem B3227927 : Blo 2151435 3227927 := bstep (se 1 (by rfl) ⟨2420945, by rfl⟩ : syracuseStep 3227927 = 4841891) B4841891
theorem B2151951 : Blo 2151435 2151951 := bstep (se 1 (by rfl) ⟨1613963, by rfl⟩ : syracuseStep 2151951 = 3227927) B3227927
theorem B3227933 : Blo 2151435 3227933 := bbase (se 3 (by rfl) ⟨605237, by rfl⟩ : syracuseStep 3227933 = 1210475) (by norm_num)
theorem B2151955 : Blo 2151435 2151955 := bstep (se 1 (by rfl) ⟨1613966, by rfl⟩ : syracuseStep 2151955 = 3227933) B3227933
theorem B4841909 : Blo 2151435 4841909 := bbase (se 5 (by rfl) ⟨226964, by rfl⟩ : syracuseStep 4841909 = 453929) (by norm_num)
theorem B3227939 : Blo 2151435 3227939 := bstep (se 1 (by rfl) ⟨2420954, by rfl⟩ : syracuseStep 3227939 = 4841909) B4841909
theorem B2151959 : Blo 2151435 2151959 := bstep (se 1 (by rfl) ⟨1613969, by rfl⟩ : syracuseStep 2151959 = 3227939) B3227939
theorem B2181325 : Blo 2151435 2181325 := bbase (se 3 (by rfl) ⟨408998, by rfl⟩ : syracuseStep 2181325 = 817997) (by norm_num)
theorem B2908433 : Blo 2151435 2908433 := bstep (se 2 (by rfl) ⟨1090662, by rfl⟩ : syracuseStep 2908433 = 2181325) B2181325
theorem B7755821 : Blo 2151435 7755821 := bstep (se 3 (by rfl) ⟨1454216, by rfl⟩ : syracuseStep 7755821 = 2908433) B2908433
theorem B5170547 : Blo 2151435 5170547 := bstep (se 1 (by rfl) ⟨3877910, by rfl⟩ : syracuseStep 5170547 = 7755821) B7755821
theorem B3447031 : Blo 2151435 3447031 := bstep (se 1 (by rfl) ⟨2585273, by rfl⟩ : syracuseStep 3447031 = 5170547) B5170547
theorem B4596041 : Blo 2151435 4596041 := bstep (se 2 (by rfl) ⟨1723515, by rfl⟩ : syracuseStep 4596041 = 3447031) B3447031
theorem B12256109 : Blo 2151435 12256109 := bstep (se 3 (by rfl) ⟨2298020, by rfl⟩ : syracuseStep 12256109 = 4596041) B4596041
theorem B8170739 : Blo 2151435 8170739 := bstep (se 1 (by rfl) ⟨6128054, by rfl⟩ : syracuseStep 8170739 = 12256109) B12256109
theorem B5447159 : Blo 2151435 5447159 := bstep (se 1 (by rfl) ⟨4085369, by rfl⟩ : syracuseStep 5447159 = 8170739) B8170739
theorem B3631439 : Blo 2151435 3631439 := bstep (se 1 (by rfl) ⟨2723579, by rfl⟩ : syracuseStep 3631439 = 5447159) B5447159
theorem B2420959 : Blo 2151435 2420959 := bstep (se 1 (by rfl) ⟨1815719, by rfl⟩ : syracuseStep 2420959 = 3631439) B3631439
theorem B3227945 : Blo 2151435 3227945 := bstep (se 2 (by rfl) ⟨1210479, by rfl⟩ : syracuseStep 3227945 = 2420959) B2420959
theorem B2151963 : Blo 2151435 2151963 := bstep (se 1 (by rfl) ⟨1613972, by rfl⟩ : syracuseStep 2151963 = 3227945) B3227945
theorem B3447037 : Blo 2151435 3447037 := bbase (se 3 (by rfl) ⟨646319, by rfl⟩ : syracuseStep 3447037 = 1292639) (by norm_num)
theorem B4596049 : Blo 2151435 4596049 := bstep (se 2 (by rfl) ⟨1723518, by rfl⟩ : syracuseStep 4596049 = 3447037) B3447037
theorem B6128065 : Blo 2151435 6128065 := bstep (se 2 (by rfl) ⟨2298024, by rfl⟩ : syracuseStep 6128065 = 4596049) B4596049
theorem B8170753 : Blo 2151435 8170753 := bstep (se 2 (by rfl) ⟨3064032, by rfl⟩ : syracuseStep 8170753 = 6128065) B6128065
theorem B10894337 : Blo 2151435 10894337 := bstep (se 2 (by rfl) ⟨4085376, by rfl⟩ : syracuseStep 10894337 = 8170753) B8170753
theorem B7262891 : Blo 2151435 7262891 := bstep (se 1 (by rfl) ⟨5447168, by rfl⟩ : syracuseStep 7262891 = 10894337) B10894337
theorem B4841927 : Blo 2151435 4841927 := bstep (se 1 (by rfl) ⟨3631445, by rfl⟩ : syracuseStep 4841927 = 7262891) B7262891
theorem B3227951 : Blo 2151435 3227951 := bstep (se 1 (by rfl) ⟨2420963, by rfl⟩ : syracuseStep 3227951 = 4841927) B4841927
theorem B2151967 : Blo 2151435 2151967 := bstep (se 1 (by rfl) ⟨1613975, by rfl⟩ : syracuseStep 2151967 = 3227951) B3227951
theorem B3227957 : Blo 2151435 3227957 := bbase (se 5 (by rfl) ⟨151310, by rfl⟩ : syracuseStep 3227957 = 302621) (by norm_num)
theorem B2151971 : Blo 2151435 2151971 := bstep (se 1 (by rfl) ⟨1613978, by rfl⟩ : syracuseStep 2151971 = 3227957) B3227957
theorem B5447189 : Blo 2151435 5447189 := bbase (se 6 (by rfl) ⟨127668, by rfl⟩ : syracuseStep 5447189 = 255337) (by norm_num)
theorem B3631459 : Blo 2151435 3631459 := bstep (se 1 (by rfl) ⟨2723594, by rfl⟩ : syracuseStep 3631459 = 5447189) B5447189
theorem B4841945 : Blo 2151435 4841945 := bstep (se 2 (by rfl) ⟨1815729, by rfl⟩ : syracuseStep 4841945 = 3631459) B3631459
theorem B3227963 : Blo 2151435 3227963 := bstep (se 1 (by rfl) ⟨2420972, by rfl⟩ : syracuseStep 3227963 = 4841945) B4841945
theorem B2151975 : Blo 2151435 2151975 := bstep (se 1 (by rfl) ⟨1613981, by rfl⟩ : syracuseStep 2151975 = 3227963) B3227963
theorem B2420977 : Blo 2151435 2420977 := bbase (se 2 (by rfl) ⟨907866, by rfl⟩ : syracuseStep 2420977 = 1815733) (by norm_num)
theorem B3227969 : Blo 2151435 3227969 := bstep (se 2 (by rfl) ⟨1210488, by rfl⟩ : syracuseStep 3227969 = 2420977) B2420977
theorem B2151979 : Blo 2151435 2151979 := bstep (se 1 (by rfl) ⟨1613984, by rfl⟩ : syracuseStep 2151979 = 3227969) B3227969
theorem B8282293 : Blo 2151435 8282293 := bbase (se 5 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 8282293 = 776465) (by norm_num)
theorem B44172229 : Blo 2151435 44172229 := bstep (se 4 (by rfl) ⟨4141146, by rfl⟩ : syracuseStep 44172229 = 8282293) B8282293
theorem B58896305 : Blo 2151435 58896305 := bstep (se 2 (by rfl) ⟨22086114, by rfl⟩ : syracuseStep 58896305 = 44172229) B44172229
theorem B39264203 : Blo 2151435 39264203 := bstep (se 1 (by rfl) ⟨29448152, by rfl⟩ : syracuseStep 39264203 = 58896305) B58896305
theorem B26176135 : Blo 2151435 26176135 := bstep (se 1 (by rfl) ⟨19632101, by rfl⟩ : syracuseStep 26176135 = 39264203) B39264203
theorem B34901513 : Blo 2151435 34901513 := bstep (se 2 (by rfl) ⟨13088067, by rfl⟩ : syracuseStep 34901513 = 26176135) B26176135
theorem B23267675 : Blo 2151435 23267675 := bstep (se 1 (by rfl) ⟨17450756, by rfl⟩ : syracuseStep 23267675 = 34901513) B34901513
theorem B15511783 : Blo 2151435 15511783 := bstep (se 1 (by rfl) ⟨11633837, by rfl⟩ : syracuseStep 15511783 = 23267675) B23267675
theorem B20682377 : Blo 2151435 20682377 := bstep (se 2 (by rfl) ⟨7755891, by rfl⟩ : syracuseStep 20682377 = 15511783) B15511783
theorem B13788251 : Blo 2151435 13788251 := bstep (se 1 (by rfl) ⟨10341188, by rfl⟩ : syracuseStep 13788251 = 20682377) B20682377
theorem B9192167 : Blo 2151435 9192167 := bstep (se 1 (by rfl) ⟨6894125, by rfl⟩ : syracuseStep 9192167 = 13788251) B13788251
theorem B6128111 : Blo 2151435 6128111 := bstep (se 1 (by rfl) ⟨4596083, by rfl⟩ : syracuseStep 6128111 = 9192167) B9192167
theorem B4085407 : Blo 2151435 4085407 := bstep (se 1 (by rfl) ⟨3064055, by rfl⟩ : syracuseStep 4085407 = 6128111) B6128111
theorem B5447209 : Blo 2151435 5447209 := bstep (se 2 (by rfl) ⟨2042703, by rfl⟩ : syracuseStep 5447209 = 4085407) B4085407
theorem B7262945 : Blo 2151435 7262945 := bstep (se 2 (by rfl) ⟨2723604, by rfl⟩ : syracuseStep 7262945 = 5447209) B5447209
theorem B4841963 : Blo 2151435 4841963 := bstep (se 1 (by rfl) ⟨3631472, by rfl⟩ : syracuseStep 4841963 = 7262945) B7262945
theorem B3227975 : Blo 2151435 3227975 := bstep (se 1 (by rfl) ⟨2420981, by rfl⟩ : syracuseStep 3227975 = 4841963) B4841963
theorem B2151983 : Blo 2151435 2151983 := bstep (se 1 (by rfl) ⟨1613987, by rfl⟩ : syracuseStep 2151983 = 3227975) B3227975
theorem B3227981 : Blo 2151435 3227981 := bbase (se 3 (by rfl) ⟨605246, by rfl⟩ : syracuseStep 3227981 = 1210493) (by norm_num)
theorem B2151987 : Blo 2151435 2151987 := bstep (se 1 (by rfl) ⟨1613990, by rfl⟩ : syracuseStep 2151987 = 3227981) B3227981
theorem B4841981 : Blo 2151435 4841981 := bbase (se 3 (by rfl) ⟨907871, by rfl⟩ : syracuseStep 4841981 = 1815743) (by norm_num)
theorem B3227987 : Blo 2151435 3227987 := bstep (se 1 (by rfl) ⟨2420990, by rfl⟩ : syracuseStep 3227987 = 4841981) B4841981
theorem B2151991 : Blo 2151435 2151991 := bstep (se 1 (by rfl) ⟨1613993, by rfl⟩ : syracuseStep 2151991 = 3227987) B3227987
theorem B3631493 : Blo 2151435 3631493 := bbase (se 4 (by rfl) ⟨340452, by rfl⟩ : syracuseStep 3631493 = 680905) (by norm_num)
theorem B2420995 : Blo 2151435 2420995 := bstep (se 1 (by rfl) ⟨1815746, by rfl⟩ : syracuseStep 2420995 = 3631493) B3631493
theorem B3227993 : Blo 2151435 3227993 := bstep (se 2 (by rfl) ⟨1210497, by rfl⟩ : syracuseStep 3227993 = 2420995) B2420995
theorem B2151995 : Blo 2151435 2151995 := bstep (se 1 (by rfl) ⟨1613996, by rfl⟩ : syracuseStep 2151995 = 3227993) B3227993
theorem B16341749 : Blo 2151435 16341749 := bbase (se 5 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 16341749 = 1532039) (by norm_num)
theorem B10894499 : Blo 2151435 10894499 := bstep (se 1 (by rfl) ⟨8170874, by rfl⟩ : syracuseStep 10894499 = 16341749) B16341749
theorem B7262999 : Blo 2151435 7262999 := bstep (se 1 (by rfl) ⟨5447249, by rfl⟩ : syracuseStep 7262999 = 10894499) B10894499
theorem B4841999 : Blo 2151435 4841999 := bstep (se 1 (by rfl) ⟨3631499, by rfl⟩ : syracuseStep 4841999 = 7262999) B7262999
theorem B3227999 : Blo 2151435 3227999 := bstep (se 1 (by rfl) ⟨2420999, by rfl⟩ : syracuseStep 3227999 = 4841999) B4841999
theorem B2151999 : Blo 2151435 2151999 := bstep (se 1 (by rfl) ⟨1613999, by rfl⟩ : syracuseStep 2151999 = 3227999) B3227999
theorem B3228005 : Blo 2151435 3228005 := bbase (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) (by norm_num)
theorem B2152003 : Blo 2151435 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B4085453 : Blo 2151435 4085453 := bbase (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) (by norm_num)
theorem B2723635 : Blo 2151435 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B3631513 : Blo 2151435 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B4842017 : Blo 2151435 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B3228011 : Blo 2151435 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B2152007 : Blo 2151435 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B2421013 : Blo 2151435 2421013 := bbase (se 6 (by rfl) ⟨56742, by rfl⟩ : syracuseStep 2421013 = 113485) (by norm_num)
theorem B3228017 : Blo 2151435 3228017 := bstep (se 2 (by rfl) ⟨1210506, by rfl⟩ : syracuseStep 3228017 = 2421013) B2421013
theorem B2152011 : Blo 2151435 2152011 := bstep (se 1 (by rfl) ⟨1614008, by rfl⟩ : syracuseStep 2152011 = 3228017) B3228017
theorem B2723645 : Blo 2151435 2723645 := bbase (se 3 (by rfl) ⟨510683, by rfl⟩ : syracuseStep 2723645 = 1021367) (by norm_num)
theorem B7263053 : Blo 2151435 7263053 := bstep (se 3 (by rfl) ⟨1361822, by rfl⟩ : syracuseStep 7263053 = 2723645) B2723645
theorem B4842035 : Blo 2151435 4842035 := bstep (se 1 (by rfl) ⟨3631526, by rfl⟩ : syracuseStep 4842035 = 7263053) B7263053
theorem B3228023 : Blo 2151435 3228023 := bstep (se 1 (by rfl) ⟨2421017, by rfl⟩ : syracuseStep 3228023 = 4842035) B4842035
theorem B2152015 : Blo 2151435 2152015 := bstep (se 1 (by rfl) ⟨1614011, by rfl⟩ : syracuseStep 2152015 = 3228023) B3228023
theorem B3228029 : Blo 2151435 3228029 := bbase (se 3 (by rfl) ⟨605255, by rfl⟩ : syracuseStep 3228029 = 1210511) (by norm_num)
theorem B2152019 : Blo 2151435 2152019 := bstep (se 1 (by rfl) ⟨1614014, by rfl⟩ : syracuseStep 2152019 = 3228029) B3228029
theorem B4842053 : Blo 2151435 4842053 := bbase (se 4 (by rfl) ⟨453942, by rfl⟩ : syracuseStep 4842053 = 907885) (by norm_num)
theorem B3228035 : Blo 2151435 3228035 := bstep (se 1 (by rfl) ⟨2421026, by rfl⟩ : syracuseStep 3228035 = 4842053) B4842053
theorem B2152023 : Blo 2151435 2152023 := bstep (se 1 (by rfl) ⟨1614017, by rfl⟩ : syracuseStep 2152023 = 3228035) B3228035
theorem B2298089 : Blo 2151435 2298089 := bbase (se 2 (by rfl) ⟨861783, by rfl⟩ : syracuseStep 2298089 = 1723567) (by norm_num)
theorem B6128237 : Blo 2151435 6128237 := bstep (se 3 (by rfl) ⟨1149044, by rfl⟩ : syracuseStep 6128237 = 2298089) B2298089
theorem B4085491 : Blo 2151435 4085491 := bstep (se 1 (by rfl) ⟨3064118, by rfl⟩ : syracuseStep 4085491 = 6128237) B6128237
theorem B5447321 : Blo 2151435 5447321 := bstep (se 2 (by rfl) ⟨2042745, by rfl⟩ : syracuseStep 5447321 = 4085491) B4085491
theorem B3631547 : Blo 2151435 3631547 := bstep (se 1 (by rfl) ⟨2723660, by rfl⟩ : syracuseStep 3631547 = 5447321) B5447321
theorem B2421031 : Blo 2151435 2421031 := bstep (se 1 (by rfl) ⟨1815773, by rfl⟩ : syracuseStep 2421031 = 3631547) B3631547
theorem B3228041 : Blo 2151435 3228041 := bstep (se 2 (by rfl) ⟨1210515, by rfl⟩ : syracuseStep 3228041 = 2421031) B2421031
theorem B2152027 : Blo 2151435 2152027 := bstep (se 1 (by rfl) ⟨1614020, by rfl⟩ : syracuseStep 2152027 = 3228041) B3228041
theorem B10894661 : Blo 2151435 10894661 := bbase (se 4 (by rfl) ⟨1021374, by rfl⟩ : syracuseStep 10894661 = 2042749) (by norm_num)
theorem B7263107 : Blo 2151435 7263107 := bstep (se 1 (by rfl) ⟨5447330, by rfl⟩ : syracuseStep 7263107 = 10894661) B10894661
theorem B4842071 : Blo 2151435 4842071 := bstep (se 1 (by rfl) ⟨3631553, by rfl⟩ : syracuseStep 4842071 = 7263107) B7263107
theorem B3228047 : Blo 2151435 3228047 := bstep (se 1 (by rfl) ⟨2421035, by rfl⟩ : syracuseStep 3228047 = 4842071) B4842071
theorem B2152031 : Blo 2151435 2152031 := bstep (se 1 (by rfl) ⟨1614023, by rfl⟩ : syracuseStep 2152031 = 3228047) B3228047
theorem B3228053 : Blo 2151435 3228053 := bbase (se 6 (by rfl) ⟨75657, by rfl⟩ : syracuseStep 3228053 = 151315) (by norm_num)
theorem B2152035 : Blo 2151435 2152035 := bstep (se 1 (by rfl) ⟨1614026, by rfl⟩ : syracuseStep 2152035 = 3228053) B3228053
theorem B10625573 : Blo 2151435 10625573 := bbase (se 4 (by rfl) ⟨996147, by rfl⟩ : syracuseStep 10625573 = 1992295) (by norm_num)
theorem B7083715 : Blo 2151435 7083715 := bstep (se 1 (by rfl) ⟨5312786, by rfl⟩ : syracuseStep 7083715 = 10625573) B10625573
theorem B9444953 : Blo 2151435 9444953 := bstep (se 2 (by rfl) ⟨3541857, by rfl⟩ : syracuseStep 9444953 = 7083715) B7083715
theorem B6296635 : Blo 2151435 6296635 := bstep (se 1 (by rfl) ⟨4722476, by rfl⟩ : syracuseStep 6296635 = 9444953) B9444953
theorem B33582053 : Blo 2151435 33582053 := bstep (se 4 (by rfl) ⟨3148317, by rfl⟩ : syracuseStep 33582053 = 6296635) B6296635
theorem B22388035 : Blo 2151435 22388035 := bstep (se 1 (by rfl) ⟨16791026, by rfl⟩ : syracuseStep 22388035 = 33582053) B33582053
theorem B29850713 : Blo 2151435 29850713 := bstep (se 2 (by rfl) ⟨11194017, by rfl⟩ : syracuseStep 29850713 = 22388035) B22388035
theorem B19900475 : Blo 2151435 19900475 := bstep (se 1 (by rfl) ⟨14925356, by rfl⟩ : syracuseStep 19900475 = 29850713) B29850713
theorem B13266983 : Blo 2151435 13266983 := bstep (se 1 (by rfl) ⟨9950237, by rfl⟩ : syracuseStep 13266983 = 19900475) B19900475
theorem B8844655 : Blo 2151435 8844655 := bstep (se 1 (by rfl) ⟨6633491, by rfl⟩ : syracuseStep 8844655 = 13266983) B13266983
theorem B11792873 : Blo 2151435 11792873 := bstep (se 2 (by rfl) ⟨4422327, by rfl⟩ : syracuseStep 11792873 = 8844655) B8844655
theorem B7861915 : Blo 2151435 7861915 := bstep (se 1 (by rfl) ⟨5896436, by rfl⟩ : syracuseStep 7861915 = 11792873) B11792873
theorem B10482553 : Blo 2151435 10482553 := bstep (se 2 (by rfl) ⟨3930957, by rfl⟩ : syracuseStep 10482553 = 7861915) B7861915
theorem B55906949 : Blo 2151435 55906949 := bstep (se 4 (by rfl) ⟨5241276, by rfl⟩ : syracuseStep 55906949 = 10482553) B10482553
theorem B37271299 : Blo 2151435 37271299 := bstep (se 1 (by rfl) ⟨27953474, by rfl⟩ : syracuseStep 37271299 = 55906949) B55906949
theorem B49695065 : Blo 2151435 49695065 := bstep (se 2 (by rfl) ⟨18635649, by rfl⟩ : syracuseStep 49695065 = 37271299) B37271299
theorem B33130043 : Blo 2151435 33130043 := bstep (se 1 (by rfl) ⟨24847532, by rfl⟩ : syracuseStep 33130043 = 49695065) B49695065
theorem B22086695 : Blo 2151435 22086695 := bstep (se 1 (by rfl) ⟨16565021, by rfl⟩ : syracuseStep 22086695 = 33130043) B33130043
theorem B14724463 : Blo 2151435 14724463 := bstep (se 1 (by rfl) ⟨11043347, by rfl⟩ : syracuseStep 14724463 = 22086695) B22086695
theorem B19632617 : Blo 2151435 19632617 := bstep (se 2 (by rfl) ⟨7362231, by rfl⟩ : syracuseStep 19632617 = 14724463) B14724463
theorem B13088411 : Blo 2151435 13088411 := bstep (se 1 (by rfl) ⟨9816308, by rfl⟩ : syracuseStep 13088411 = 19632617) B19632617
theorem B8725607 : Blo 2151435 8725607 := bstep (se 1 (by rfl) ⟨6544205, by rfl⟩ : syracuseStep 8725607 = 13088411) B13088411
theorem B5817071 : Blo 2151435 5817071 := bstep (se 1 (by rfl) ⟨4362803, by rfl⟩ : syracuseStep 5817071 = 8725607) B8725607
theorem B3878047 : Blo 2151435 3878047 := bstep (se 1 (by rfl) ⟨2908535, by rfl⟩ : syracuseStep 3878047 = 5817071) B5817071
theorem B5170729 : Blo 2151435 5170729 := bstep (se 2 (by rfl) ⟨1939023, by rfl⟩ : syracuseStep 5170729 = 3878047) B3878047
theorem B6894305 : Blo 2151435 6894305 := bstep (se 2 (by rfl) ⟨2585364, by rfl⟩ : syracuseStep 6894305 = 5170729) B5170729
theorem B4596203 : Blo 2151435 4596203 := bstep (se 1 (by rfl) ⟨3447152, by rfl⟩ : syracuseStep 4596203 = 6894305) B6894305
theorem B12256541 : Blo 2151435 12256541 := bstep (se 3 (by rfl) ⟨2298101, by rfl⟩ : syracuseStep 12256541 = 4596203) B4596203
theorem B8171027 : Blo 2151435 8171027 := bstep (se 1 (by rfl) ⟨6128270, by rfl⟩ : syracuseStep 8171027 = 12256541) B12256541
theorem B5447351 : Blo 2151435 5447351 := bstep (se 1 (by rfl) ⟨4085513, by rfl⟩ : syracuseStep 5447351 = 8171027) B8171027
theorem B3631567 : Blo 2151435 3631567 := bstep (se 1 (by rfl) ⟨2723675, by rfl⟩ : syracuseStep 3631567 = 5447351) B5447351
theorem B4842089 : Blo 2151435 4842089 := bstep (se 2 (by rfl) ⟨1815783, by rfl⟩ : syracuseStep 4842089 = 3631567) B3631567
theorem B3228059 : Blo 2151435 3228059 := bstep (se 1 (by rfl) ⟨2421044, by rfl⟩ : syracuseStep 3228059 = 4842089) B4842089
theorem B2152039 : Blo 2151435 2152039 := bstep (se 1 (by rfl) ⟨1614029, by rfl⟩ : syracuseStep 2152039 = 3228059) B3228059
theorem B2421049 : Blo 2151435 2421049 := bbase (se 2 (by rfl) ⟨907893, by rfl⟩ : syracuseStep 2421049 = 1815787) (by norm_num)
theorem B3228065 : Blo 2151435 3228065 := bstep (se 2 (by rfl) ⟨1210524, by rfl⟩ : syracuseStep 3228065 = 2421049) B2421049
theorem B2152043 : Blo 2151435 2152043 := bstep (se 1 (by rfl) ⟨1614032, by rfl⟩ : syracuseStep 2152043 = 3228065) B3228065
theorem B6128293 : Blo 2151435 6128293 := bbase (se 4 (by rfl) ⟨574527, by rfl⟩ : syracuseStep 6128293 = 1149055) (by norm_num)
theorem B8171057 : Blo 2151435 8171057 := bstep (se 2 (by rfl) ⟨3064146, by rfl⟩ : syracuseStep 8171057 = 6128293) B6128293
theorem B5447371 : Blo 2151435 5447371 := bstep (se 1 (by rfl) ⟨4085528, by rfl⟩ : syracuseStep 5447371 = 8171057) B8171057
theorem B7263161 : Blo 2151435 7263161 := bstep (se 2 (by rfl) ⟨2723685, by rfl⟩ : syracuseStep 7263161 = 5447371) B5447371
theorem B4842107 : Blo 2151435 4842107 := bstep (se 1 (by rfl) ⟨3631580, by rfl⟩ : syracuseStep 4842107 = 7263161) B7263161
theorem B3228071 : Blo 2151435 3228071 := bstep (se 1 (by rfl) ⟨2421053, by rfl⟩ : syracuseStep 3228071 = 4842107) B4842107
theorem B2152047 : Blo 2151435 2152047 := bstep (se 1 (by rfl) ⟨1614035, by rfl⟩ : syracuseStep 2152047 = 3228071) B3228071
theorem B3228077 : Blo 2151435 3228077 := bbase (se 3 (by rfl) ⟨605264, by rfl⟩ : syracuseStep 3228077 = 1210529) (by norm_num)
theorem B2152051 : Blo 2151435 2152051 := bstep (se 1 (by rfl) ⟨1614038, by rfl⟩ : syracuseStep 2152051 = 3228077) B3228077
theorem B4842125 : Blo 2151435 4842125 := bbase (se 3 (by rfl) ⟨907898, by rfl⟩ : syracuseStep 4842125 = 1815797) (by norm_num)
theorem B3228083 : Blo 2151435 3228083 := bstep (se 1 (by rfl) ⟨2421062, by rfl⟩ : syracuseStep 3228083 = 4842125) B4842125
theorem B2152055 : Blo 2151435 2152055 := bstep (se 1 (by rfl) ⟨1614041, by rfl⟩ : syracuseStep 2152055 = 3228083) B3228083
theorem B2723701 : Blo 2151435 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B3631601 : Blo 2151435 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B2421067 : Blo 2151435 2421067 := bstep (se 1 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 2421067 = 3631601) B3631601
theorem B3228089 : Blo 2151435 3228089 := bstep (se 2 (by rfl) ⟨1210533, by rfl⟩ : syracuseStep 3228089 = 2421067) B2421067
theorem B2152059 : Blo 2151435 2152059 := bstep (se 1 (by rfl) ⟨1614044, by rfl⟩ : syracuseStep 2152059 = 3228089) B3228089
theorem B6544277 : Blo 2151435 6544277 := bbase (se 6 (by rfl) ⟨153381, by rfl⟩ : syracuseStep 6544277 = 306763) (by norm_num)
theorem B4362851 : Blo 2151435 4362851 := bstep (se 1 (by rfl) ⟨3272138, by rfl⟩ : syracuseStep 4362851 = 6544277) B6544277
theorem B2908567 : Blo 2151435 2908567 := bstep (se 1 (by rfl) ⟨2181425, by rfl⟩ : syracuseStep 2908567 = 4362851) B4362851
theorem B15512357 : Blo 2151435 15512357 := bstep (se 4 (by rfl) ⟨1454283, by rfl⟩ : syracuseStep 15512357 = 2908567) B2908567
theorem B41366285 : Blo 2151435 41366285 := bstep (se 3 (by rfl) ⟨7756178, by rfl⟩ : syracuseStep 41366285 = 15512357) B15512357
theorem B27577523 : Blo 2151435 27577523 := bstep (se 1 (by rfl) ⟨20683142, by rfl⟩ : syracuseStep 27577523 = 41366285) B41366285
theorem B18385015 : Blo 2151435 18385015 := bstep (se 1 (by rfl) ⟨13788761, by rfl⟩ : syracuseStep 18385015 = 27577523) B27577523
theorem B24513353 : Blo 2151435 24513353 := bstep (se 2 (by rfl) ⟨9192507, by rfl⟩ : syracuseStep 24513353 = 18385015) B18385015
theorem B16342235 : Blo 2151435 16342235 := bstep (se 1 (by rfl) ⟨12256676, by rfl⟩ : syracuseStep 16342235 = 24513353) B24513353
theorem B10894823 : Blo 2151435 10894823 := bstep (se 1 (by rfl) ⟨8171117, by rfl⟩ : syracuseStep 10894823 = 16342235) B16342235
theorem B7263215 : Blo 2151435 7263215 := bstep (se 1 (by rfl) ⟨5447411, by rfl⟩ : syracuseStep 7263215 = 10894823) B10894823
theorem B4842143 : Blo 2151435 4842143 := bstep (se 1 (by rfl) ⟨3631607, by rfl⟩ : syracuseStep 4842143 = 7263215) B7263215
theorem B3228095 : Blo 2151435 3228095 := bstep (se 1 (by rfl) ⟨2421071, by rfl⟩ : syracuseStep 3228095 = 4842143) B4842143
theorem B2152063 : Blo 2151435 2152063 := bstep (se 1 (by rfl) ⟨1614047, by rfl⟩ : syracuseStep 2152063 = 3228095) B3228095
theorem B3228101 : Blo 2151435 3228101 := bbase (se 4 (by rfl) ⟨302634, by rfl⟩ : syracuseStep 3228101 = 605269) (by norm_num)
theorem B2152067 : Blo 2151435 2152067 := bstep (se 1 (by rfl) ⟨1614050, by rfl⟩ : syracuseStep 2152067 = 3228101) B3228101
theorem B3631621 : Blo 2151435 3631621 := bbase (se 4 (by rfl) ⟨340464, by rfl⟩ : syracuseStep 3631621 = 680929) (by norm_num)
theorem B4842161 : Blo 2151435 4842161 := bstep (se 2 (by rfl) ⟨1815810, by rfl⟩ : syracuseStep 4842161 = 3631621) B3631621
theorem B3228107 : Blo 2151435 3228107 := bstep (se 1 (by rfl) ⟨2421080, by rfl⟩ : syracuseStep 3228107 = 4842161) B4842161
theorem B2152071 : Blo 2151435 2152071 := bstep (se 1 (by rfl) ⟨1614053, by rfl⟩ : syracuseStep 2152071 = 3228107) B3228107
theorem B2421085 : Blo 2151435 2421085 := bbase (se 3 (by rfl) ⟨453953, by rfl⟩ : syracuseStep 2421085 = 907907) (by norm_num)
theorem B3228113 : Blo 2151435 3228113 := bstep (se 2 (by rfl) ⟨1210542, by rfl⟩ : syracuseStep 3228113 = 2421085) B2421085
theorem B2152075 : Blo 2151435 2152075 := bstep (se 1 (by rfl) ⟨1614056, by rfl⟩ : syracuseStep 2152075 = 3228113) B3228113
theorem B7263269 : Blo 2151435 7263269 := bbase (se 4 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 7263269 = 1361863) (by norm_num)
theorem B4842179 : Blo 2151435 4842179 := bstep (se 1 (by rfl) ⟨3631634, by rfl⟩ : syracuseStep 4842179 = 7263269) B7263269
theorem B3228119 : Blo 2151435 3228119 := bstep (se 1 (by rfl) ⟨2421089, by rfl⟩ : syracuseStep 3228119 = 4842179) B4842179
theorem B2152079 : Blo 2151435 2152079 := bstep (se 1 (by rfl) ⟨1614059, by rfl⟩ : syracuseStep 2152079 = 3228119) B3228119
theorem B3228125 : Blo 2151435 3228125 := bbase (se 3 (by rfl) ⟨605273, by rfl⟩ : syracuseStep 3228125 = 1210547) (by norm_num)
theorem B2152083 : Blo 2151435 2152083 := bstep (se 1 (by rfl) ⟨1614062, by rfl⟩ : syracuseStep 2152083 = 3228125) B3228125
theorem B4842197 : Blo 2151435 4842197 := bbase (se 7 (by rfl) ⟨56744, by rfl⟩ : syracuseStep 4842197 = 113489) (by norm_num)
theorem B3228131 : Blo 2151435 3228131 := bstep (se 1 (by rfl) ⟨2421098, by rfl⟩ : syracuseStep 3228131 = 4842197) B4842197
theorem B2152087 : Blo 2151435 2152087 := bstep (se 1 (by rfl) ⟨1614065, by rfl⟩ : syracuseStep 2152087 = 3228131) B3228131
theorem B9192629 : Blo 2151435 9192629 := bbase (se 5 (by rfl) ⟨430904, by rfl⟩ : syracuseStep 9192629 = 861809) (by norm_num)
theorem B6128419 : Blo 2151435 6128419 := bstep (se 1 (by rfl) ⟨4596314, by rfl⟩ : syracuseStep 6128419 = 9192629) B9192629
theorem B8171225 : Blo 2151435 8171225 := bstep (se 2 (by rfl) ⟨3064209, by rfl⟩ : syracuseStep 8171225 = 6128419) B6128419
theorem B5447483 : Blo 2151435 5447483 := bstep (se 1 (by rfl) ⟨4085612, by rfl⟩ : syracuseStep 5447483 = 8171225) B8171225
theorem B3631655 : Blo 2151435 3631655 := bstep (se 1 (by rfl) ⟨2723741, by rfl⟩ : syracuseStep 3631655 = 5447483) B5447483
theorem B2421103 : Blo 2151435 2421103 := bstep (se 1 (by rfl) ⟨1815827, by rfl⟩ : syracuseStep 2421103 = 3631655) B3631655
theorem B3228137 : Blo 2151435 3228137 := bstep (se 2 (by rfl) ⟨1210551, by rfl⟩ : syracuseStep 3228137 = 2421103) B2421103
theorem B2152091 : Blo 2151435 2152091 := bstep (se 1 (by rfl) ⟨1614068, by rfl⟩ : syracuseStep 2152091 = 3228137) B3228137
theorem B7862117 : Blo 2151435 7862117 := bbase (se 4 (by rfl) ⟨737073, by rfl⟩ : syracuseStep 7862117 = 1474147) (by norm_num)
theorem B20965645 : Blo 2151435 20965645 := bstep (se 3 (by rfl) ⟨3931058, by rfl⟩ : syracuseStep 20965645 = 7862117) B7862117
theorem B27954193 : Blo 2151435 27954193 := bstep (se 2 (by rfl) ⟨10482822, by rfl⟩ : syracuseStep 27954193 = 20965645) B20965645
theorem B37272257 : Blo 2151435 37272257 := bstep (se 2 (by rfl) ⟨13977096, by rfl⟩ : syracuseStep 37272257 = 27954193) B27954193
theorem B24848171 : Blo 2151435 24848171 := bstep (se 1 (by rfl) ⟨18636128, by rfl⟩ : syracuseStep 24848171 = 37272257) B37272257
theorem B16565447 : Blo 2151435 16565447 := bstep (se 1 (by rfl) ⟨12424085, by rfl⟩ : syracuseStep 16565447 = 24848171) B24848171
theorem B11043631 : Blo 2151435 11043631 := bstep (se 1 (by rfl) ⟨8282723, by rfl⟩ : syracuseStep 11043631 = 16565447) B16565447
theorem B14724841 : Blo 2151435 14724841 := bstep (se 2 (by rfl) ⟨5521815, by rfl⟩ : syracuseStep 14724841 = 11043631) B11043631
theorem B19633121 : Blo 2151435 19633121 := bstep (se 2 (by rfl) ⟨7362420, by rfl⟩ : syracuseStep 19633121 = 14724841) B14724841
theorem B13088747 : Blo 2151435 13088747 := bstep (se 1 (by rfl) ⟨9816560, by rfl⟩ : syracuseStep 13088747 = 19633121) B19633121
theorem B34903325 : Blo 2151435 34903325 := bstep (se 3 (by rfl) ⟨6544373, by rfl⟩ : syracuseStep 34903325 = 13088747) B13088747
theorem B23268883 : Blo 2151435 23268883 := bstep (se 1 (by rfl) ⟨17451662, by rfl⟩ : syracuseStep 23268883 = 34903325) B34903325
theorem B31025177 : Blo 2151435 31025177 := bstep (se 2 (by rfl) ⟨11634441, by rfl⟩ : syracuseStep 31025177 = 23268883) B23268883
theorem B20683451 : Blo 2151435 20683451 := bstep (se 1 (by rfl) ⟨15512588, by rfl⟩ : syracuseStep 20683451 = 31025177) B31025177
theorem B13788967 : Blo 2151435 13788967 := bstep (se 1 (by rfl) ⟨10341725, by rfl⟩ : syracuseStep 13788967 = 20683451) B20683451
theorem B18385289 : Blo 2151435 18385289 := bstep (se 2 (by rfl) ⟨6894483, by rfl⟩ : syracuseStep 18385289 = 13788967) B13788967
theorem B12256859 : Blo 2151435 12256859 := bstep (se 1 (by rfl) ⟨9192644, by rfl⟩ : syracuseStep 12256859 = 18385289) B18385289
theorem B8171239 : Blo 2151435 8171239 := bstep (se 1 (by rfl) ⟨6128429, by rfl⟩ : syracuseStep 8171239 = 12256859) B12256859
theorem B10894985 : Blo 2151435 10894985 := bstep (se 2 (by rfl) ⟨4085619, by rfl⟩ : syracuseStep 10894985 = 8171239) B8171239
theorem B7263323 : Blo 2151435 7263323 := bstep (se 1 (by rfl) ⟨5447492, by rfl⟩ : syracuseStep 7263323 = 10894985) B10894985
theorem B4842215 : Blo 2151435 4842215 := bstep (se 1 (by rfl) ⟨3631661, by rfl⟩ : syracuseStep 4842215 = 7263323) B7263323
theorem B3228143 : Blo 2151435 3228143 := bstep (se 1 (by rfl) ⟨2421107, by rfl⟩ : syracuseStep 3228143 = 4842215) B4842215
theorem B2152095 : Blo 2151435 2152095 := bstep (se 1 (by rfl) ⟨1614071, by rfl⟩ : syracuseStep 2152095 = 3228143) B3228143
theorem B3228149 : Blo 2151435 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B2152099 : Blo 2151435 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B6128453 : Blo 2151435 6128453 := bbase (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) (by norm_num)
theorem B4085635 : Blo 2151435 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B5447513 : Blo 2151435 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B3631675 : Blo 2151435 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B4842233 : Blo 2151435 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B3228155 : Blo 2151435 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B2152103 : Blo 2151435 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B2421121 : Blo 2151435 2421121 := bbase (se 2 (by rfl) ⟨907920, by rfl⟩ : syracuseStep 2421121 = 1815841) (by norm_num)
theorem B3228161 : Blo 2151435 3228161 := bstep (se 2 (by rfl) ⟨1210560, by rfl⟩ : syracuseStep 3228161 = 2421121) B2421121
theorem B2152107 : Blo 2151435 2152107 := bstep (se 1 (by rfl) ⟨1614080, by rfl⟩ : syracuseStep 2152107 = 3228161) B3228161
theorem B5447533 : Blo 2151435 5447533 := bbase (se 3 (by rfl) ⟨1021412, by rfl⟩ : syracuseStep 5447533 = 2042825) (by norm_num)
theorem B7263377 : Blo 2151435 7263377 := bstep (se 2 (by rfl) ⟨2723766, by rfl⟩ : syracuseStep 7263377 = 5447533) B5447533
theorem B4842251 : Blo 2151435 4842251 := bstep (se 1 (by rfl) ⟨3631688, by rfl⟩ : syracuseStep 4842251 = 7263377) B7263377
theorem B3228167 : Blo 2151435 3228167 := bstep (se 1 (by rfl) ⟨2421125, by rfl⟩ : syracuseStep 3228167 = 4842251) B4842251
theorem B2152111 : Blo 2151435 2152111 := bstep (se 1 (by rfl) ⟨1614083, by rfl⟩ : syracuseStep 2152111 = 3228167) B3228167
theorem B3228173 : Blo 2151435 3228173 := bbase (se 3 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 3228173 = 1210565) (by norm_num)
theorem B2152115 : Blo 2151435 2152115 := bstep (se 1 (by rfl) ⟨1614086, by rfl⟩ : syracuseStep 2152115 = 3228173) B3228173
theorem B4842269 : Blo 2151435 4842269 := bbase (se 3 (by rfl) ⟨907925, by rfl⟩ : syracuseStep 4842269 = 1815851) (by norm_num)
theorem B3228179 : Blo 2151435 3228179 := bstep (se 1 (by rfl) ⟨2421134, by rfl⟩ : syracuseStep 3228179 = 4842269) B4842269
theorem B2152119 : Blo 2151435 2152119 := bstep (se 1 (by rfl) ⟨1614089, by rfl⟩ : syracuseStep 2152119 = 3228179) B3228179
theorem B3631709 : Blo 2151435 3631709 := bbase (se 3 (by rfl) ⟨680945, by rfl⟩ : syracuseStep 3631709 = 1361891) (by norm_num)
theorem B2421139 : Blo 2151435 2421139 := bstep (se 1 (by rfl) ⟨1815854, by rfl⟩ : syracuseStep 2421139 = 3631709) B3631709
theorem B3228185 : Blo 2151435 3228185 := bstep (se 2 (by rfl) ⟨1210569, by rfl⟩ : syracuseStep 3228185 = 2421139) B2421139
theorem B2152123 : Blo 2151435 2152123 := bstep (se 1 (by rfl) ⟨1614092, by rfl⟩ : syracuseStep 2152123 = 3228185) B3228185
theorem B3447293 : Blo 2151435 3447293 := bbase (se 3 (by rfl) ⟨646367, by rfl⟩ : syracuseStep 3447293 = 1292735) (by norm_num)
theorem B9192781 : Blo 2151435 9192781 := bstep (se 3 (by rfl) ⟨1723646, by rfl⟩ : syracuseStep 9192781 = 3447293) B3447293
theorem B12257041 : Blo 2151435 12257041 := bstep (se 2 (by rfl) ⟨4596390, by rfl⟩ : syracuseStep 12257041 = 9192781) B9192781
theorem B16342721 : Blo 2151435 16342721 := bstep (se 2 (by rfl) ⟨6128520, by rfl⟩ : syracuseStep 16342721 = 12257041) B12257041
theorem B10895147 : Blo 2151435 10895147 := bstep (se 1 (by rfl) ⟨8171360, by rfl⟩ : syracuseStep 10895147 = 16342721) B16342721
theorem B7263431 : Blo 2151435 7263431 := bstep (se 1 (by rfl) ⟨5447573, by rfl⟩ : syracuseStep 7263431 = 10895147) B10895147
theorem B4842287 : Blo 2151435 4842287 := bstep (se 1 (by rfl) ⟨3631715, by rfl⟩ : syracuseStep 4842287 = 7263431) B7263431
theorem B3228191 : Blo 2151435 3228191 := bstep (se 1 (by rfl) ⟨2421143, by rfl⟩ : syracuseStep 3228191 = 4842287) B4842287
theorem B2152127 : Blo 2151435 2152127 := bstep (se 1 (by rfl) ⟨1614095, by rfl⟩ : syracuseStep 2152127 = 3228191) B3228191
theorem B3228197 : Blo 2151435 3228197 := bbase (se 4 (by rfl) ⟨302643, by rfl⟩ : syracuseStep 3228197 = 605287) (by norm_num)
theorem B2152131 : Blo 2151435 2152131 := bstep (se 1 (by rfl) ⟨1614098, by rfl⟩ : syracuseStep 2152131 = 3228197) B3228197
theorem B2723797 : Blo 2151435 2723797 := bbase (se 7 (by rfl) ⟨31919, by rfl⟩ : syracuseStep 2723797 = 63839) (by norm_num)
theorem B3631729 : Blo 2151435 3631729 := bstep (se 2 (by rfl) ⟨1361898, by rfl⟩ : syracuseStep 3631729 = 2723797) B2723797
theorem B4842305 : Blo 2151435 4842305 := bstep (se 2 (by rfl) ⟨1815864, by rfl⟩ : syracuseStep 4842305 = 3631729) B3631729
theorem B3228203 : Blo 2151435 3228203 := bstep (se 1 (by rfl) ⟨2421152, by rfl⟩ : syracuseStep 3228203 = 4842305) B4842305
theorem B2152135 : Blo 2151435 2152135 := bstep (se 1 (by rfl) ⟨1614101, by rfl⟩ : syracuseStep 2152135 = 3228203) B3228203
theorem B2421157 : Blo 2151435 2421157 := bbase (se 4 (by rfl) ⟨226983, by rfl⟩ : syracuseStep 2421157 = 453967) (by norm_num)
theorem B3228209 : Blo 2151435 3228209 := bstep (se 2 (by rfl) ⟨1210578, by rfl⟩ : syracuseStep 3228209 = 2421157) B2421157
theorem B2152139 : Blo 2151435 2152139 := bstep (se 1 (by rfl) ⟨1614104, by rfl⟩ : syracuseStep 2152139 = 3228209) B3228209
theorem B7756469 : Blo 2151435 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B5170979 : Blo 2151435 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B13789277 : Blo 2151435 13789277 := bstep (se 3 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 13789277 = 5170979) B5170979
theorem B9192851 : Blo 2151435 9192851 := bstep (se 1 (by rfl) ⟨6894638, by rfl⟩ : syracuseStep 9192851 = 13789277) B13789277
theorem B6128567 : Blo 2151435 6128567 := bstep (se 1 (by rfl) ⟨4596425, by rfl⟩ : syracuseStep 6128567 = 9192851) B9192851
theorem B4085711 : Blo 2151435 4085711 := bstep (se 1 (by rfl) ⟨3064283, by rfl⟩ : syracuseStep 4085711 = 6128567) B6128567
theorem B2723807 : Blo 2151435 2723807 := bstep (se 1 (by rfl) ⟨2042855, by rfl⟩ : syracuseStep 2723807 = 4085711) B4085711
theorem B7263485 : Blo 2151435 7263485 := bstep (se 3 (by rfl) ⟨1361903, by rfl⟩ : syracuseStep 7263485 = 2723807) B2723807
theorem B4842323 : Blo 2151435 4842323 := bstep (se 1 (by rfl) ⟨3631742, by rfl⟩ : syracuseStep 4842323 = 7263485) B7263485
theorem B3228215 : Blo 2151435 3228215 := bstep (se 1 (by rfl) ⟨2421161, by rfl⟩ : syracuseStep 3228215 = 4842323) B4842323
theorem B2152143 : Blo 2151435 2152143 := bstep (se 1 (by rfl) ⟨1614107, by rfl⟩ : syracuseStep 2152143 = 3228215) B3228215
theorem B3228221 : Blo 2151435 3228221 := bbase (se 3 (by rfl) ⟨605291, by rfl⟩ : syracuseStep 3228221 = 1210583) (by norm_num)
theorem B2152147 : Blo 2151435 2152147 := bstep (se 1 (by rfl) ⟨1614110, by rfl⟩ : syracuseStep 2152147 = 3228221) B3228221
theorem B4842341 : Blo 2151435 4842341 := bbase (se 4 (by rfl) ⟨453969, by rfl⟩ : syracuseStep 4842341 = 907939) (by norm_num)
theorem B3228227 : Blo 2151435 3228227 := bstep (se 1 (by rfl) ⟨2421170, by rfl⟩ : syracuseStep 3228227 = 4842341) B4842341
theorem B2152151 : Blo 2151435 2152151 := bstep (se 1 (by rfl) ⟨1614113, by rfl⟩ : syracuseStep 2152151 = 3228227) B3228227
theorem B5447645 : Blo 2151435 5447645 := bbase (se 3 (by rfl) ⟨1021433, by rfl⟩ : syracuseStep 5447645 = 2042867) (by norm_num)
theorem B3631763 : Blo 2151435 3631763 := bstep (se 1 (by rfl) ⟨2723822, by rfl⟩ : syracuseStep 3631763 = 5447645) B5447645
theorem B2421175 : Blo 2151435 2421175 := bstep (se 1 (by rfl) ⟨1815881, by rfl⟩ : syracuseStep 2421175 = 3631763) B3631763
theorem B3228233 : Blo 2151435 3228233 := bstep (se 2 (by rfl) ⟨1210587, by rfl⟩ : syracuseStep 3228233 = 2421175) B2421175
theorem B2152155 : Blo 2151435 2152155 := bstep (se 1 (by rfl) ⟨1614116, by rfl⟩ : syracuseStep 2152155 = 3228233) B3228233
theorem B4085741 : Blo 2151435 4085741 := bbase (se 3 (by rfl) ⟨766076, by rfl⟩ : syracuseStep 4085741 = 1532153) (by norm_num)
theorem B10895309 : Blo 2151435 10895309 := bstep (se 3 (by rfl) ⟨2042870, by rfl⟩ : syracuseStep 10895309 = 4085741) B4085741
theorem B7263539 : Blo 2151435 7263539 := bstep (se 1 (by rfl) ⟨5447654, by rfl⟩ : syracuseStep 7263539 = 10895309) B10895309
theorem B4842359 : Blo 2151435 4842359 := bstep (se 1 (by rfl) ⟨3631769, by rfl⟩ : syracuseStep 4842359 = 7263539) B7263539
theorem B3228239 : Blo 2151435 3228239 := bstep (se 1 (by rfl) ⟨2421179, by rfl⟩ : syracuseStep 3228239 = 4842359) B4842359
theorem B2152159 : Blo 2151435 2152159 := bstep (se 1 (by rfl) ⟨1614119, by rfl⟩ : syracuseStep 2152159 = 3228239) B3228239
theorem B3228245 : Blo 2151435 3228245 := bbase (se 8 (by rfl) ⟨18915, by rfl⟩ : syracuseStep 3228245 = 37831) (by norm_num)
theorem B2152163 : Blo 2151435 2152163 := bstep (se 1 (by rfl) ⟨1614122, by rfl⟩ : syracuseStep 2152163 = 3228245) B3228245
theorem B2487709 : Blo 2151435 2487709 := bbase (se 3 (by rfl) ⟨466445, by rfl⟩ : syracuseStep 2487709 = 932891) (by norm_num)
theorem B3316945 : Blo 2151435 3316945 := bstep (se 2 (by rfl) ⟨1243854, by rfl⟩ : syracuseStep 3316945 = 2487709) B2487709
theorem B4422593 : Blo 2151435 4422593 := bstep (se 2 (by rfl) ⟨1658472, by rfl⟩ : syracuseStep 4422593 = 3316945) B3316945
theorem B2948395 : Blo 2151435 2948395 := bstep (se 1 (by rfl) ⟨2211296, by rfl⟩ : syracuseStep 2948395 = 4422593) B4422593
theorem B3931193 : Blo 2151435 3931193 := bstep (se 2 (by rfl) ⟨1474197, by rfl⟩ : syracuseStep 3931193 = 2948395) B2948395
theorem B10483181 : Blo 2151435 10483181 := bstep (se 3 (by rfl) ⟨1965596, by rfl⟩ : syracuseStep 10483181 = 3931193) B3931193
theorem B6988787 : Blo 2151435 6988787 := bstep (se 1 (by rfl) ⟨5241590, by rfl⟩ : syracuseStep 6988787 = 10483181) B10483181
theorem B4659191 : Blo 2151435 4659191 := bstep (se 1 (by rfl) ⟨3494393, by rfl⟩ : syracuseStep 4659191 = 6988787) B6988787
theorem B3106127 : Blo 2151435 3106127 := bstep (se 1 (by rfl) ⟨2329595, by rfl⟩ : syracuseStep 3106127 = 4659191) B4659191
theorem B8283005 : Blo 2151435 8283005 := bstep (se 3 (by rfl) ⟨1553063, by rfl⟩ : syracuseStep 8283005 = 3106127) B3106127
theorem B5522003 : Blo 2151435 5522003 := bstep (se 1 (by rfl) ⟨4141502, by rfl⟩ : syracuseStep 5522003 = 8283005) B8283005
theorem B3681335 : Blo 2151435 3681335 := bstep (se 1 (by rfl) ⟨2761001, by rfl⟩ : syracuseStep 3681335 = 5522003) B5522003
theorem B2454223 : Blo 2151435 2454223 := bstep (se 1 (by rfl) ⟨1840667, by rfl⟩ : syracuseStep 2454223 = 3681335) B3681335
theorem B3272297 : Blo 2151435 3272297 := bstep (se 2 (by rfl) ⟨1227111, by rfl⟩ : syracuseStep 3272297 = 2454223) B2454223
theorem B8726125 : Blo 2151435 8726125 := bstep (se 3 (by rfl) ⟨1636148, by rfl⟩ : syracuseStep 8726125 = 3272297) B3272297
theorem B11634833 : Blo 2151435 11634833 := bstep (se 2 (by rfl) ⟨4363062, by rfl⟩ : syracuseStep 11634833 = 8726125) B8726125
theorem B7756555 : Blo 2151435 7756555 := bstep (se 1 (by rfl) ⟨5817416, by rfl⟩ : syracuseStep 7756555 = 11634833) B11634833
theorem B10342073 : Blo 2151435 10342073 := bstep (se 2 (by rfl) ⟨3878277, by rfl⟩ : syracuseStep 10342073 = 7756555) B7756555
theorem B6894715 : Blo 2151435 6894715 := bstep (se 1 (by rfl) ⟨5171036, by rfl⟩ : syracuseStep 6894715 = 10342073) B10342073
theorem B9192953 : Blo 2151435 9192953 := bstep (se 2 (by rfl) ⟨3447357, by rfl⟩ : syracuseStep 9192953 = 6894715) B6894715
theorem B6128635 : Blo 2151435 6128635 := bstep (se 1 (by rfl) ⟨4596476, by rfl⟩ : syracuseStep 6128635 = 9192953) B9192953
theorem B8171513 : Blo 2151435 8171513 := bstep (se 2 (by rfl) ⟨3064317, by rfl⟩ : syracuseStep 8171513 = 6128635) B6128635
theorem B5447675 : Blo 2151435 5447675 := bstep (se 1 (by rfl) ⟨4085756, by rfl⟩ : syracuseStep 5447675 = 8171513) B8171513
theorem B3631783 : Blo 2151435 3631783 := bstep (se 1 (by rfl) ⟨2723837, by rfl⟩ : syracuseStep 3631783 = 5447675) B5447675
theorem B4842377 : Blo 2151435 4842377 := bstep (se 2 (by rfl) ⟨1815891, by rfl⟩ : syracuseStep 4842377 = 3631783) B3631783
theorem B3228251 : Blo 2151435 3228251 := bstep (se 1 (by rfl) ⟨2421188, by rfl⟩ : syracuseStep 3228251 = 4842377) B4842377
theorem B2152167 : Blo 2151435 2152167 := bstep (se 1 (by rfl) ⟨1614125, by rfl⟩ : syracuseStep 2152167 = 3228251) B3228251
theorem B2421193 : Blo 2151435 2421193 := bbase (se 2 (by rfl) ⟨907947, by rfl⟩ : syracuseStep 2421193 = 1815895) (by norm_num)
theorem B3228257 : Blo 2151435 3228257 := bstep (se 2 (by rfl) ⟨1210596, by rfl⟩ : syracuseStep 3228257 = 2421193) B2421193
theorem B2152171 : Blo 2151435 2152171 := bstep (se 1 (by rfl) ⟨1614128, by rfl⟩ : syracuseStep 2152171 = 3228257) B3228257
theorem B18385973 : Blo 2151435 18385973 := bbase (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) (by norm_num)
theorem B12257315 : Blo 2151435 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B8171543 : Blo 2151435 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B5447695 : Blo 2151435 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B7263593 : Blo 2151435 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B4842395 : Blo 2151435 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B3228263 : Blo 2151435 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B2152175 : Blo 2151435 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B3228269 : Blo 2151435 3228269 := bbase (se 3 (by rfl) ⟨605300, by rfl⟩ : syracuseStep 3228269 = 1210601) (by norm_num)
theorem B2152179 : Blo 2151435 2152179 := bstep (se 1 (by rfl) ⟨1614134, by rfl⟩ : syracuseStep 2152179 = 3228269) B3228269
theorem B4842413 : Blo 2151435 4842413 := bbase (se 3 (by rfl) ⟨907952, by rfl⟩ : syracuseStep 4842413 = 1815905) (by norm_num)
theorem B3228275 : Blo 2151435 3228275 := bstep (se 1 (by rfl) ⟨2421206, by rfl⟩ : syracuseStep 3228275 = 4842413) B4842413
theorem B2152183 : Blo 2151435 2152183 := bstep (se 1 (by rfl) ⟨1614137, by rfl⟩ : syracuseStep 2152183 = 3228275) B3228275
theorem B6128693 : Blo 2151435 6128693 := bbase (se 5 (by rfl) ⟨287282, by rfl⟩ : syracuseStep 6128693 = 574565) (by norm_num)
theorem B4085795 : Blo 2151435 4085795 := bstep (se 1 (by rfl) ⟨3064346, by rfl⟩ : syracuseStep 4085795 = 6128693) B6128693
theorem B2723863 : Blo 2151435 2723863 := bstep (se 1 (by rfl) ⟨2042897, by rfl⟩ : syracuseStep 2723863 = 4085795) B4085795
theorem B3631817 : Blo 2151435 3631817 := bstep (se 2 (by rfl) ⟨1361931, by rfl⟩ : syracuseStep 3631817 = 2723863) B2723863
theorem B2421211 : Blo 2151435 2421211 := bstep (se 1 (by rfl) ⟨1815908, by rfl⟩ : syracuseStep 2421211 = 3631817) B3631817
theorem B3228281 : Blo 2151435 3228281 := bstep (se 2 (by rfl) ⟨1210605, by rfl⟩ : syracuseStep 3228281 = 2421211) B2421211
theorem B2152187 : Blo 2151435 2152187 := bstep (se 1 (by rfl) ⟨1614140, by rfl⟩ : syracuseStep 2152187 = 3228281) B3228281
theorem B8396101 : Blo 2151435 8396101 := bbase (se 4 (by rfl) ⟨787134, by rfl⟩ : syracuseStep 8396101 = 1574269) (by norm_num)
theorem B44779205 : Blo 2151435 44779205 := bstep (se 4 (by rfl) ⟨4198050, by rfl⟩ : syracuseStep 44779205 = 8396101) B8396101
theorem B29852803 : Blo 2151435 29852803 := bstep (se 1 (by rfl) ⟨22389602, by rfl⟩ : syracuseStep 29852803 = 44779205) B44779205
theorem B39803737 : Blo 2151435 39803737 := bstep (se 2 (by rfl) ⟨14926401, by rfl⟩ : syracuseStep 39803737 = 29852803) B29852803
theorem B53071649 : Blo 2151435 53071649 := bstep (se 2 (by rfl) ⟨19901868, by rfl⟩ : syracuseStep 53071649 = 39803737) B39803737
theorem B35381099 : Blo 2151435 35381099 := bstep (se 1 (by rfl) ⟨26535824, by rfl⟩ : syracuseStep 35381099 = 53071649) B53071649
theorem B23587399 : Blo 2151435 23587399 := bstep (se 1 (by rfl) ⟨17690549, by rfl⟩ : syracuseStep 23587399 = 35381099) B35381099
theorem B31449865 : Blo 2151435 31449865 := bstep (se 2 (by rfl) ⟨11793699, by rfl⟩ : syracuseStep 31449865 = 23587399) B23587399
theorem B41933153 : Blo 2151435 41933153 := bstep (se 2 (by rfl) ⟨15724932, by rfl⟩ : syracuseStep 41933153 = 31449865) B31449865
theorem B27955435 : Blo 2151435 27955435 := bstep (se 1 (by rfl) ⟨20966576, by rfl⟩ : syracuseStep 27955435 = 41933153) B41933153
theorem B37273913 : Blo 2151435 37273913 := bstep (se 2 (by rfl) ⟨13977717, by rfl⟩ : syracuseStep 37273913 = 27955435) B27955435
theorem B24849275 : Blo 2151435 24849275 := bstep (se 1 (by rfl) ⟨18636956, by rfl⟩ : syracuseStep 24849275 = 37273913) B37273913
theorem B66264733 : Blo 2151435 66264733 := bstep (se 3 (by rfl) ⟨12424637, by rfl⟩ : syracuseStep 66264733 = 24849275) B24849275
theorem B353411909 : Blo 2151435 353411909 := bstep (se 4 (by rfl) ⟨33132366, by rfl⟩ : syracuseStep 353411909 = 66264733) B66264733
theorem B235607939 : Blo 2151435 235607939 := bstep (se 1 (by rfl) ⟨176705954, by rfl⟩ : syracuseStep 235607939 = 353411909) B353411909
theorem B157071959 : Blo 2151435 157071959 := bstep (se 1 (by rfl) ⟨117803969, by rfl⟩ : syracuseStep 157071959 = 235607939) B235607939
theorem B104714639 : Blo 2151435 104714639 := bstep (se 1 (by rfl) ⟨78535979, by rfl⟩ : syracuseStep 104714639 = 157071959) B157071959
theorem B69809759 : Blo 2151435 69809759 := bstep (se 1 (by rfl) ⟨52357319, by rfl⟩ : syracuseStep 69809759 = 104714639) B104714639
theorem B46539839 : Blo 2151435 46539839 := bstep (se 1 (by rfl) ⟨34904879, by rfl⟩ : syracuseStep 46539839 = 69809759) B69809759
theorem B31026559 : Blo 2151435 31026559 := bstep (se 1 (by rfl) ⟨23269919, by rfl⟩ : syracuseStep 31026559 = 46539839) B46539839
theorem B41368745 : Blo 2151435 41368745 := bstep (se 2 (by rfl) ⟨15513279, by rfl⟩ : syracuseStep 41368745 = 31026559) B31026559
theorem B27579163 : Blo 2151435 27579163 := bstep (se 1 (by rfl) ⟨20684372, by rfl⟩ : syracuseStep 27579163 = 41368745) B41368745
theorem B36772217 : Blo 2151435 36772217 := bstep (se 2 (by rfl) ⟨13789581, by rfl⟩ : syracuseStep 36772217 = 27579163) B27579163
theorem B24514811 : Blo 2151435 24514811 := bstep (se 1 (by rfl) ⟨18386108, by rfl⟩ : syracuseStep 24514811 = 36772217) B36772217
theorem B16343207 : Blo 2151435 16343207 := bstep (se 1 (by rfl) ⟨12257405, by rfl⟩ : syracuseStep 16343207 = 24514811) B24514811
theorem B10895471 : Blo 2151435 10895471 := bstep (se 1 (by rfl) ⟨8171603, by rfl⟩ : syracuseStep 10895471 = 16343207) B16343207
theorem B7263647 : Blo 2151435 7263647 := bstep (se 1 (by rfl) ⟨5447735, by rfl⟩ : syracuseStep 7263647 = 10895471) B10895471
theorem B4842431 : Blo 2151435 4842431 := bstep (se 1 (by rfl) ⟨3631823, by rfl⟩ : syracuseStep 4842431 = 7263647) B7263647
theorem B3228287 : Blo 2151435 3228287 := bstep (se 1 (by rfl) ⟨2421215, by rfl⟩ : syracuseStep 3228287 = 4842431) B4842431
theorem B2152191 : Blo 2151435 2152191 := bstep (se 1 (by rfl) ⟨1614143, by rfl⟩ : syracuseStep 2152191 = 3228287) B3228287
theorem B3228293 : Blo 2151435 3228293 := bbase (se 4 (by rfl) ⟨302652, by rfl⟩ : syracuseStep 3228293 = 605305) (by norm_num)
theorem B2152195 : Blo 2151435 2152195 := bstep (se 1 (by rfl) ⟨1614146, by rfl⟩ : syracuseStep 2152195 = 3228293) B3228293
theorem B3631837 : Blo 2151435 3631837 := bbase (se 3 (by rfl) ⟨680969, by rfl⟩ : syracuseStep 3631837 = 1361939) (by norm_num)
theorem B4842449 : Blo 2151435 4842449 := bstep (se 2 (by rfl) ⟨1815918, by rfl⟩ : syracuseStep 4842449 = 3631837) B3631837
theorem B3228299 : Blo 2151435 3228299 := bstep (se 1 (by rfl) ⟨2421224, by rfl⟩ : syracuseStep 3228299 = 4842449) B4842449
theorem B2152199 : Blo 2151435 2152199 := bstep (se 1 (by rfl) ⟨1614149, by rfl⟩ : syracuseStep 2152199 = 3228299) B3228299
theorem B2421229 : Blo 2151435 2421229 := bbase (se 3 (by rfl) ⟨453980, by rfl⟩ : syracuseStep 2421229 = 907961) (by norm_num)
theorem B3228305 : Blo 2151435 3228305 := bstep (se 2 (by rfl) ⟨1210614, by rfl⟩ : syracuseStep 3228305 = 2421229) B2421229
theorem B2152203 : Blo 2151435 2152203 := bstep (se 1 (by rfl) ⟨1614152, by rfl⟩ : syracuseStep 2152203 = 3228305) B3228305
theorem B7263701 : Blo 2151435 7263701 := bbase (se 7 (by rfl) ⟨85121, by rfl⟩ : syracuseStep 7263701 = 170243) (by norm_num)
theorem B4842467 : Blo 2151435 4842467 := bstep (se 1 (by rfl) ⟨3631850, by rfl⟩ : syracuseStep 4842467 = 7263701) B7263701
theorem B3228311 : Blo 2151435 3228311 := bstep (se 1 (by rfl) ⟨2421233, by rfl⟩ : syracuseStep 3228311 = 4842467) B4842467
theorem B2152207 : Blo 2151435 2152207 := bstep (se 1 (by rfl) ⟨1614155, by rfl⟩ : syracuseStep 2152207 = 3228311) B3228311
theorem B3228317 : Blo 2151435 3228317 := bbase (se 3 (by rfl) ⟨605309, by rfl⟩ : syracuseStep 3228317 = 1210619) (by norm_num)
theorem B2152211 : Blo 2151435 2152211 := bstep (se 1 (by rfl) ⟨1614158, by rfl⟩ : syracuseStep 2152211 = 3228317) B3228317
theorem B4842485 : Blo 2151435 4842485 := bbase (se 5 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 4842485 = 453983) (by norm_num)
theorem B3228323 : Blo 2151435 3228323 := bstep (se 1 (by rfl) ⟨2421242, by rfl⟩ : syracuseStep 3228323 = 4842485) B4842485
theorem B2152215 : Blo 2151435 2152215 := bstep (se 1 (by rfl) ⟨1614161, by rfl⟩ : syracuseStep 2152215 = 3228323) B3228323
theorem B4659301 : Blo 2151435 4659301 := bbase (se 4 (by rfl) ⟨436809, by rfl⟩ : syracuseStep 4659301 = 873619) (by norm_num)
theorem B24849605 : Blo 2151435 24849605 := bstep (se 4 (by rfl) ⟨2329650, by rfl⟩ : syracuseStep 24849605 = 4659301) B4659301
theorem B66265613 : Blo 2151435 66265613 := bstep (se 3 (by rfl) ⟨12424802, by rfl⟩ : syracuseStep 66265613 = 24849605) B24849605
theorem B44177075 : Blo 2151435 44177075 := bstep (se 1 (by rfl) ⟨33132806, by rfl⟩ : syracuseStep 44177075 = 66265613) B66265613
theorem B29451383 : Blo 2151435 29451383 := bstep (se 1 (by rfl) ⟨22088537, by rfl⟩ : syracuseStep 29451383 = 44177075) B44177075
theorem B19634255 : Blo 2151435 19634255 := bstep (se 1 (by rfl) ⟨14725691, by rfl⟩ : syracuseStep 19634255 = 29451383) B29451383
theorem B13089503 : Blo 2151435 13089503 := bstep (se 1 (by rfl) ⟨9817127, by rfl⟩ : syracuseStep 13089503 = 19634255) B19634255
theorem B8726335 : Blo 2151435 8726335 := bstep (se 1 (by rfl) ⟨6544751, by rfl⟩ : syracuseStep 8726335 = 13089503) B13089503
theorem B46540453 : Blo 2151435 46540453 := bstep (se 4 (by rfl) ⟨4363167, by rfl⟩ : syracuseStep 46540453 = 8726335) B8726335
theorem B62053937 : Blo 2151435 62053937 := bstep (se 2 (by rfl) ⟨23270226, by rfl⟩ : syracuseStep 62053937 = 46540453) B46540453
theorem B41369291 : Blo 2151435 41369291 := bstep (se 1 (by rfl) ⟨31026968, by rfl⟩ : syracuseStep 41369291 = 62053937) B62053937
theorem B27579527 : Blo 2151435 27579527 := bstep (se 1 (by rfl) ⟨20684645, by rfl⟩ : syracuseStep 27579527 = 41369291) B41369291
theorem B18386351 : Blo 2151435 18386351 := bstep (se 1 (by rfl) ⟨13789763, by rfl⟩ : syracuseStep 18386351 = 27579527) B27579527
theorem B12257567 : Blo 2151435 12257567 := bstep (se 1 (by rfl) ⟨9193175, by rfl⟩ : syracuseStep 12257567 = 18386351) B18386351
theorem B8171711 : Blo 2151435 8171711 := bstep (se 1 (by rfl) ⟨6128783, by rfl⟩ : syracuseStep 8171711 = 12257567) B12257567
theorem B5447807 : Blo 2151435 5447807 := bstep (se 1 (by rfl) ⟨4085855, by rfl⟩ : syracuseStep 5447807 = 8171711) B8171711
theorem B3631871 : Blo 2151435 3631871 := bstep (se 1 (by rfl) ⟨2723903, by rfl⟩ : syracuseStep 3631871 = 5447807) B5447807
theorem B2421247 : Blo 2151435 2421247 := bstep (se 1 (by rfl) ⟨1815935, by rfl⟩ : syracuseStep 2421247 = 3631871) B3631871
theorem B3228329 : Blo 2151435 3228329 := bstep (se 2 (by rfl) ⟨1210623, by rfl⟩ : syracuseStep 3228329 = 2421247) B2421247
theorem B2152219 : Blo 2151435 2152219 := bstep (se 1 (by rfl) ⟨1614164, by rfl⟩ : syracuseStep 2152219 = 3228329) B3228329
theorem B3064397 : Blo 2151435 3064397 := bbase (se 3 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 3064397 = 1149149) (by norm_num)
theorem B8171725 : Blo 2151435 8171725 := bstep (se 3 (by rfl) ⟨1532198, by rfl⟩ : syracuseStep 8171725 = 3064397) B3064397
theorem B10895633 : Blo 2151435 10895633 := bstep (se 2 (by rfl) ⟨4085862, by rfl⟩ : syracuseStep 10895633 = 8171725) B8171725
theorem B7263755 : Blo 2151435 7263755 := bstep (se 1 (by rfl) ⟨5447816, by rfl⟩ : syracuseStep 7263755 = 10895633) B10895633
theorem B4842503 : Blo 2151435 4842503 := bstep (se 1 (by rfl) ⟨3631877, by rfl⟩ : syracuseStep 4842503 = 7263755) B7263755
theorem B3228335 : Blo 2151435 3228335 := bstep (se 1 (by rfl) ⟨2421251, by rfl⟩ : syracuseStep 3228335 = 4842503) B4842503
theorem B2152223 : Blo 2151435 2152223 := bstep (se 1 (by rfl) ⟨1614167, by rfl⟩ : syracuseStep 2152223 = 3228335) B3228335
theorem B3228341 : Blo 2151435 3228341 := bbase (se 5 (by rfl) ⟨151328, by rfl⟩ : syracuseStep 3228341 = 302657) (by norm_num)
theorem B2152227 : Blo 2151435 2152227 := bstep (se 1 (by rfl) ⟨1614170, by rfl⟩ : syracuseStep 2152227 = 3228341) B3228341
theorem B5447837 : Blo 2151435 5447837 := bbase (se 3 (by rfl) ⟨1021469, by rfl⟩ : syracuseStep 5447837 = 2042939) (by norm_num)
theorem B3631891 : Blo 2151435 3631891 := bstep (se 1 (by rfl) ⟨2723918, by rfl⟩ : syracuseStep 3631891 = 5447837) B5447837
theorem B4842521 : Blo 2151435 4842521 := bstep (se 2 (by rfl) ⟨1815945, by rfl⟩ : syracuseStep 4842521 = 3631891) B3631891
theorem B3228347 : Blo 2151435 3228347 := bstep (se 1 (by rfl) ⟨2421260, by rfl⟩ : syracuseStep 3228347 = 4842521) B4842521
theorem B2152231 : Blo 2151435 2152231 := bstep (se 1 (by rfl) ⟨1614173, by rfl⟩ : syracuseStep 2152231 = 3228347) B3228347
theorem B2421265 : Blo 2151435 2421265 := bbase (se 2 (by rfl) ⟨907974, by rfl⟩ : syracuseStep 2421265 = 1815949) (by norm_num)
theorem B3228353 : Blo 2151435 3228353 := bstep (se 2 (by rfl) ⟨1210632, by rfl⟩ : syracuseStep 3228353 = 2421265) B2421265
theorem B2152235 : Blo 2151435 2152235 := bstep (se 1 (by rfl) ⟨1614176, by rfl⟩ : syracuseStep 2152235 = 3228353) B3228353
theorem B4085893 : Blo 2151435 4085893 := bbase (se 4 (by rfl) ⟨383052, by rfl⟩ : syracuseStep 4085893 = 766105) (by norm_num)
theorem B5447857 : Blo 2151435 5447857 := bstep (se 2 (by rfl) ⟨2042946, by rfl⟩ : syracuseStep 5447857 = 4085893) B4085893
theorem B7263809 : Blo 2151435 7263809 := bstep (se 2 (by rfl) ⟨2723928, by rfl⟩ : syracuseStep 7263809 = 5447857) B5447857
theorem B4842539 : Blo 2151435 4842539 := bstep (se 1 (by rfl) ⟨3631904, by rfl⟩ : syracuseStep 4842539 = 7263809) B7263809
theorem B3228359 : Blo 2151435 3228359 := bstep (se 1 (by rfl) ⟨2421269, by rfl⟩ : syracuseStep 3228359 = 4842539) B4842539
theorem B2152239 : Blo 2151435 2152239 := bstep (se 1 (by rfl) ⟨1614179, by rfl⟩ : syracuseStep 2152239 = 3228359) B3228359
theorem B3228365 : Blo 2151435 3228365 := bbase (se 3 (by rfl) ⟨605318, by rfl⟩ : syracuseStep 3228365 = 1210637) (by norm_num)
theorem B2152243 : Blo 2151435 2152243 := bstep (se 1 (by rfl) ⟨1614182, by rfl⟩ : syracuseStep 2152243 = 3228365) B3228365
theorem B4842557 : Blo 2151435 4842557 := bbase (se 3 (by rfl) ⟨907979, by rfl⟩ : syracuseStep 4842557 = 1815959) (by norm_num)
theorem B3228371 : Blo 2151435 3228371 := bstep (se 1 (by rfl) ⟨2421278, by rfl⟩ : syracuseStep 3228371 = 4842557) B4842557
theorem B2152247 : Blo 2151435 2152247 := bstep (se 1 (by rfl) ⟨1614185, by rfl⟩ : syracuseStep 2152247 = 3228371) B3228371
theorem B3631925 : Blo 2151435 3631925 := bbase (se 5 (by rfl) ⟨170246, by rfl⟩ : syracuseStep 3631925 = 340493) (by norm_num)
theorem B2421283 : Blo 2151435 2421283 := bstep (se 1 (by rfl) ⟨1815962, by rfl⟩ : syracuseStep 2421283 = 3631925) B3631925
theorem B3228377 : Blo 2151435 3228377 := bstep (se 2 (by rfl) ⟨1210641, by rfl⟩ : syracuseStep 3228377 = 2421283) B2421283
theorem B2152251 : Blo 2151435 2152251 := bstep (se 1 (by rfl) ⟨1614188, by rfl⟩ : syracuseStep 2152251 = 3228377) B3228377
theorem B6128885 : Blo 2151435 6128885 := bbase (se 5 (by rfl) ⟨287291, by rfl⟩ : syracuseStep 6128885 = 574583) (by norm_num)
theorem B16343693 : Blo 2151435 16343693 := bstep (se 3 (by rfl) ⟨3064442, by rfl⟩ : syracuseStep 16343693 = 6128885) B6128885
theorem B10895795 : Blo 2151435 10895795 := bstep (se 1 (by rfl) ⟨8171846, by rfl⟩ : syracuseStep 10895795 = 16343693) B16343693
theorem B7263863 : Blo 2151435 7263863 := bstep (se 1 (by rfl) ⟨5447897, by rfl⟩ : syracuseStep 7263863 = 10895795) B10895795
theorem B4842575 : Blo 2151435 4842575 := bstep (se 1 (by rfl) ⟨3631931, by rfl⟩ : syracuseStep 4842575 = 7263863) B7263863
theorem B3228383 : Blo 2151435 3228383 := bstep (se 1 (by rfl) ⟨2421287, by rfl⟩ : syracuseStep 3228383 = 4842575) B4842575
theorem B2152255 : Blo 2151435 2152255 := bstep (se 1 (by rfl) ⟨1614191, by rfl⟩ : syracuseStep 2152255 = 3228383) B3228383
theorem B3228389 : Blo 2151435 3228389 := bbase (se 4 (by rfl) ⟨302661, by rfl⟩ : syracuseStep 3228389 = 605323) (by norm_num)
theorem B2152259 : Blo 2151435 2152259 := bstep (se 1 (by rfl) ⟨1614194, by rfl⟩ : syracuseStep 2152259 = 3228389) B3228389
theorem B2298341 : Blo 2151435 2298341 := bbase (se 4 (by rfl) ⟨215469, by rfl⟩ : syracuseStep 2298341 = 430939) (by norm_num)
theorem B6128909 : Blo 2151435 6128909 := bstep (se 3 (by rfl) ⟨1149170, by rfl⟩ : syracuseStep 6128909 = 2298341) B2298341
theorem B4085939 : Blo 2151435 4085939 := bstep (se 1 (by rfl) ⟨3064454, by rfl⟩ : syracuseStep 4085939 = 6128909) B6128909
theorem B2723959 : Blo 2151435 2723959 := bstep (se 1 (by rfl) ⟨2042969, by rfl⟩ : syracuseStep 2723959 = 4085939) B4085939
theorem B3631945 : Blo 2151435 3631945 := bstep (se 2 (by rfl) ⟨1361979, by rfl⟩ : syracuseStep 3631945 = 2723959) B2723959
theorem B4842593 : Blo 2151435 4842593 := bstep (se 2 (by rfl) ⟨1815972, by rfl⟩ : syracuseStep 4842593 = 3631945) B3631945
theorem B3228395 : Blo 2151435 3228395 := bstep (se 1 (by rfl) ⟨2421296, by rfl⟩ : syracuseStep 3228395 = 4842593) B4842593
theorem B2152263 : Blo 2151435 2152263 := bstep (se 1 (by rfl) ⟨1614197, by rfl⟩ : syracuseStep 2152263 = 3228395) B3228395
theorem B2421301 : Blo 2151435 2421301 := bbase (se 5 (by rfl) ⟨113498, by rfl⟩ : syracuseStep 2421301 = 226997) (by norm_num)
theorem B3228401 : Blo 2151435 3228401 := bstep (se 2 (by rfl) ⟨1210650, by rfl⟩ : syracuseStep 3228401 = 2421301) B2421301
theorem B2152267 : Blo 2151435 2152267 := bstep (se 1 (by rfl) ⟨1614200, by rfl⟩ : syracuseStep 2152267 = 3228401) B3228401
theorem B2723969 : Blo 2151435 2723969 := bbase (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) (by norm_num)
theorem B7263917 : Blo 2151435 7263917 := bstep (se 3 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 7263917 = 2723969) B2723969
theorem B4842611 : Blo 2151435 4842611 := bstep (se 1 (by rfl) ⟨3631958, by rfl⟩ : syracuseStep 4842611 = 7263917) B7263917
theorem B3228407 : Blo 2151435 3228407 := bstep (se 1 (by rfl) ⟨2421305, by rfl⟩ : syracuseStep 3228407 = 4842611) B4842611
theorem B2152271 : Blo 2151435 2152271 := bstep (se 1 (by rfl) ⟨1614203, by rfl⟩ : syracuseStep 2152271 = 3228407) B3228407
theorem B3228413 : Blo 2151435 3228413 := bbase (se 3 (by rfl) ⟨605327, by rfl⟩ : syracuseStep 3228413 = 1210655) (by norm_num)
theorem B2152275 : Blo 2151435 2152275 := bstep (se 1 (by rfl) ⟨1614206, by rfl⟩ : syracuseStep 2152275 = 3228413) B3228413
theorem B4842629 : Blo 2151435 4842629 := bbase (se 4 (by rfl) ⟨453996, by rfl⟩ : syracuseStep 4842629 = 907993) (by norm_num)
theorem B3228419 : Blo 2151435 3228419 := bstep (se 1 (by rfl) ⟨2421314, by rfl⟩ : syracuseStep 3228419 = 4842629) B4842629
theorem B2152279 : Blo 2151435 2152279 := bstep (se 1 (by rfl) ⟨1614209, by rfl⟩ : syracuseStep 2152279 = 3228419) B3228419
theorem B4596725 : Blo 2151435 4596725 := bbase (se 5 (by rfl) ⟨215471, by rfl⟩ : syracuseStep 4596725 = 430943) (by norm_num)
theorem B3064483 : Blo 2151435 3064483 := bstep (se 1 (by rfl) ⟨2298362, by rfl⟩ : syracuseStep 3064483 = 4596725) B4596725
theorem B4085977 : Blo 2151435 4085977 := bstep (se 2 (by rfl) ⟨1532241, by rfl⟩ : syracuseStep 4085977 = 3064483) B3064483
theorem B5447969 : Blo 2151435 5447969 := bstep (se 2 (by rfl) ⟨2042988, by rfl⟩ : syracuseStep 5447969 = 4085977) B4085977
theorem B3631979 : Blo 2151435 3631979 := bstep (se 1 (by rfl) ⟨2723984, by rfl⟩ : syracuseStep 3631979 = 5447969) B5447969
theorem B2421319 : Blo 2151435 2421319 := bstep (se 1 (by rfl) ⟨1815989, by rfl⟩ : syracuseStep 2421319 = 3631979) B3631979
theorem B3228425 : Blo 2151435 3228425 := bstep (se 2 (by rfl) ⟨1210659, by rfl⟩ : syracuseStep 3228425 = 2421319) B2421319
theorem B2152283 : Blo 2151435 2152283 := bstep (se 1 (by rfl) ⟨1614212, by rfl⟩ : syracuseStep 2152283 = 3228425) B3228425
theorem B10895957 : Blo 2151435 10895957 := bbase (se 8 (by rfl) ⟨63843, by rfl⟩ : syracuseStep 10895957 = 127687) (by norm_num)
theorem B7263971 : Blo 2151435 7263971 := bstep (se 1 (by rfl) ⟨5447978, by rfl⟩ : syracuseStep 7263971 = 10895957) B10895957
theorem B4842647 : Blo 2151435 4842647 := bstep (se 1 (by rfl) ⟨3631985, by rfl⟩ : syracuseStep 4842647 = 7263971) B7263971
theorem B3228431 : Blo 2151435 3228431 := bstep (se 1 (by rfl) ⟨2421323, by rfl⟩ : syracuseStep 3228431 = 4842647) B4842647
theorem B2152287 : Blo 2151435 2152287 := bstep (se 1 (by rfl) ⟨1614215, by rfl⟩ : syracuseStep 2152287 = 3228431) B3228431
theorem B3228437 : Blo 2151435 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B2152291 : Blo 2151435 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B2329733 : Blo 2151435 2329733 := bbase (se 4 (by rfl) ⟨218412, by rfl⟩ : syracuseStep 2329733 = 436825) (by norm_num)
theorem B6212621 : Blo 2151435 6212621 := bstep (se 3 (by rfl) ⟨1164866, by rfl⟩ : syracuseStep 6212621 = 2329733) B2329733
theorem B4141747 : Blo 2151435 4141747 := bstep (se 1 (by rfl) ⟨3106310, by rfl⟩ : syracuseStep 4141747 = 6212621) B6212621
theorem B5522329 : Blo 2151435 5522329 := bstep (se 2 (by rfl) ⟨2070873, by rfl⟩ : syracuseStep 5522329 = 4141747) B4141747
theorem B7363105 : Blo 2151435 7363105 := bstep (se 2 (by rfl) ⟨2761164, by rfl⟩ : syracuseStep 7363105 = 5522329) B5522329
theorem B39269893 : Blo 2151435 39269893 := bstep (se 4 (by rfl) ⟨3681552, by rfl⟩ : syracuseStep 39269893 = 7363105) B7363105
theorem B52359857 : Blo 2151435 52359857 := bstep (se 2 (by rfl) ⟨19634946, by rfl⟩ : syracuseStep 52359857 = 39269893) B39269893
theorem B34906571 : Blo 2151435 34906571 := bstep (se 1 (by rfl) ⟨26179928, by rfl⟩ : syracuseStep 34906571 = 52359857) B52359857
theorem B23271047 : Blo 2151435 23271047 := bstep (se 1 (by rfl) ⟨17453285, by rfl⟩ : syracuseStep 23271047 = 34906571) B34906571
theorem B15514031 : Blo 2151435 15514031 := bstep (se 1 (by rfl) ⟨11635523, by rfl⟩ : syracuseStep 15514031 = 23271047) B23271047
theorem B41370749 : Blo 2151435 41370749 := bstep (se 3 (by rfl) ⟨7757015, by rfl⟩ : syracuseStep 41370749 = 15514031) B15514031
theorem B27580499 : Blo 2151435 27580499 := bstep (se 1 (by rfl) ⟨20685374, by rfl⟩ : syracuseStep 27580499 = 41370749) B41370749
theorem B18386999 : Blo 2151435 18386999 := bstep (se 1 (by rfl) ⟨13790249, by rfl⟩ : syracuseStep 18386999 = 27580499) B27580499
theorem B12257999 : Blo 2151435 12257999 := bstep (se 1 (by rfl) ⟨9193499, by rfl⟩ : syracuseStep 12257999 = 18386999) B18386999
theorem B8171999 : Blo 2151435 8171999 := bstep (se 1 (by rfl) ⟨6128999, by rfl⟩ : syracuseStep 8171999 = 12257999) B12257999
theorem B5447999 : Blo 2151435 5447999 := bstep (se 1 (by rfl) ⟨4085999, by rfl⟩ : syracuseStep 5447999 = 8171999) B8171999
theorem B3631999 : Blo 2151435 3631999 := bstep (se 1 (by rfl) ⟨2723999, by rfl⟩ : syracuseStep 3631999 = 5447999) B5447999
theorem B4842665 : Blo 2151435 4842665 := bstep (se 2 (by rfl) ⟨1815999, by rfl⟩ : syracuseStep 4842665 = 3631999) B3631999
theorem B3228443 : Blo 2151435 3228443 := bstep (se 1 (by rfl) ⟨2421332, by rfl⟩ : syracuseStep 3228443 = 4842665) B4842665
theorem B2152295 : Blo 2151435 2152295 := bstep (se 1 (by rfl) ⟨1614221, by rfl⟩ : syracuseStep 2152295 = 3228443) B3228443
theorem B2421337 : Blo 2151435 2421337 := bbase (se 2 (by rfl) ⟨908001, by rfl⟩ : syracuseStep 2421337 = 1816003) (by norm_num)
theorem B3228449 : Blo 2151435 3228449 := bstep (se 2 (by rfl) ⟨1210668, by rfl⟩ : syracuseStep 3228449 = 2421337) B2421337
theorem B2152299 : Blo 2151435 2152299 := bstep (se 1 (by rfl) ⟨1614224, by rfl⟩ : syracuseStep 2152299 = 3228449) B3228449
theorem B2766949 : Blo 2151435 2766949 := bbase (se 4 (by rfl) ⟨259401, by rfl⟩ : syracuseStep 2766949 = 518803) (by norm_num)
theorem B14757061 : Blo 2151435 14757061 := bstep (se 4 (by rfl) ⟨1383474, by rfl⟩ : syracuseStep 14757061 = 2766949) B2766949
theorem B19676081 : Blo 2151435 19676081 := bstep (se 2 (by rfl) ⟨7378530, by rfl⟩ : syracuseStep 19676081 = 14757061) B14757061
theorem B13117387 : Blo 2151435 13117387 := bstep (se 1 (by rfl) ⟨9838040, by rfl⟩ : syracuseStep 13117387 = 19676081) B19676081
theorem B17489849 : Blo 2151435 17489849 := bstep (se 2 (by rfl) ⟨6558693, by rfl⟩ : syracuseStep 17489849 = 13117387) B13117387
theorem B46639597 : Blo 2151435 46639597 := bstep (se 3 (by rfl) ⟨8744924, by rfl⟩ : syracuseStep 46639597 = 17489849) B17489849
theorem B62186129 : Blo 2151435 62186129 := bstep (se 2 (by rfl) ⟨23319798, by rfl⟩ : syracuseStep 62186129 = 46639597) B46639597
theorem B41457419 : Blo 2151435 41457419 := bstep (se 1 (by rfl) ⟨31093064, by rfl⟩ : syracuseStep 41457419 = 62186129) B62186129
theorem B27638279 : Blo 2151435 27638279 := bstep (se 1 (by rfl) ⟨20728709, by rfl⟩ : syracuseStep 27638279 = 41457419) B41457419
theorem B18425519 : Blo 2151435 18425519 := bstep (se 1 (by rfl) ⟨13819139, by rfl⟩ : syracuseStep 18425519 = 27638279) B27638279
theorem B12283679 : Blo 2151435 12283679 := bstep (se 1 (by rfl) ⟨9212759, by rfl⟩ : syracuseStep 12283679 = 18425519) B18425519
theorem B8189119 : Blo 2151435 8189119 := bstep (se 1 (by rfl) ⟨6141839, by rfl⟩ : syracuseStep 8189119 = 12283679) B12283679
theorem B43675301 : Blo 2151435 43675301 := bstep (se 4 (by rfl) ⟨4094559, by rfl⟩ : syracuseStep 43675301 = 8189119) B8189119
theorem B116467469 : Blo 2151435 116467469 := bstep (se 3 (by rfl) ⟨21837650, by rfl⟩ : syracuseStep 116467469 = 43675301) B43675301
theorem B77644979 : Blo 2151435 77644979 := bstep (se 1 (by rfl) ⟨58233734, by rfl⟩ : syracuseStep 77644979 = 116467469) B116467469
theorem B51763319 : Blo 2151435 51763319 := bstep (se 1 (by rfl) ⟨38822489, by rfl⟩ : syracuseStep 51763319 = 77644979) B77644979
theorem B34508879 : Blo 2151435 34508879 := bstep (se 1 (by rfl) ⟨25881659, by rfl⟩ : syracuseStep 34508879 = 51763319) B51763319
theorem B23005919 : Blo 2151435 23005919 := bstep (se 1 (by rfl) ⟨17254439, by rfl⟩ : syracuseStep 23005919 = 34508879) B34508879
theorem B61349117 : Blo 2151435 61349117 := bstep (se 3 (by rfl) ⟨11502959, by rfl⟩ : syracuseStep 61349117 = 23005919) B23005919
theorem B163597645 : Blo 2151435 163597645 := bstep (se 3 (by rfl) ⟨30674558, by rfl⟩ : syracuseStep 163597645 = 61349117) B61349117
theorem B218130193 : Blo 2151435 218130193 := bstep (se 2 (by rfl) ⟨81798822, by rfl⟩ : syracuseStep 218130193 = 163597645) B163597645
theorem B290840257 : Blo 2151435 290840257 := bstep (se 2 (by rfl) ⟨109065096, by rfl⟩ : syracuseStep 290840257 = 218130193) B218130193
theorem B387787009 : Blo 2151435 387787009 := bstep (se 2 (by rfl) ⟨145420128, by rfl⟩ : syracuseStep 387787009 = 290840257) B290840257
theorem B517049345 : Blo 2151435 517049345 := bstep (se 2 (by rfl) ⟨193893504, by rfl⟩ : syracuseStep 517049345 = 387787009) B387787009
theorem B344699563 : Blo 2151435 344699563 := bstep (se 1 (by rfl) ⟨258524672, by rfl⟩ : syracuseStep 344699563 = 517049345) B517049345
theorem B459599417 : Blo 2151435 459599417 := bstep (se 2 (by rfl) ⟨172349781, by rfl⟩ : syracuseStep 459599417 = 344699563) B344699563
theorem B306399611 : Blo 2151435 306399611 := bstep (se 1 (by rfl) ⟨229799708, by rfl⟩ : syracuseStep 306399611 = 459599417) B459599417
theorem B817065629 : Blo 2151435 817065629 := bstep (se 3 (by rfl) ⟨153199805, by rfl⟩ : syracuseStep 817065629 = 306399611) B306399611
theorem B544710419 : Blo 2151435 544710419 := bstep (se 1 (by rfl) ⟨408532814, by rfl⟩ : syracuseStep 544710419 = 817065629) B817065629
theorem B363140279 : Blo 2151435 363140279 := bstep (se 1 (by rfl) ⟨272355209, by rfl⟩ : syracuseStep 363140279 = 544710419) B544710419
theorem B242093519 : Blo 2151435 242093519 := bstep (se 1 (by rfl) ⟨181570139, by rfl⟩ : syracuseStep 242093519 = 363140279) B363140279
theorem B161395679 : Blo 2151435 161395679 := bstep (se 1 (by rfl) ⟨121046759, by rfl⟩ : syracuseStep 161395679 = 242093519) B242093519
theorem B107597119 : Blo 2151435 107597119 := bstep (se 1 (by rfl) ⟨80697839, by rfl⟩ : syracuseStep 107597119 = 161395679) B161395679
theorem B143462825 : Blo 2151435 143462825 := bstep (se 2 (by rfl) ⟨53798559, by rfl⟩ : syracuseStep 143462825 = 107597119) B107597119
theorem B95641883 : Blo 2151435 95641883 := bstep (se 1 (by rfl) ⟨71731412, by rfl⟩ : syracuseStep 95641883 = 143462825) B143462825
theorem B63761255 : Blo 2151435 63761255 := bstep (se 1 (by rfl) ⟨47820941, by rfl⟩ : syracuseStep 63761255 = 95641883) B95641883
theorem B42507503 : Blo 2151435 42507503 := bstep (se 1 (by rfl) ⟨31880627, by rfl⟩ : syracuseStep 42507503 = 63761255) B63761255
theorem B28338335 : Blo 2151435 28338335 := bstep (se 1 (by rfl) ⟨21253751, by rfl⟩ : syracuseStep 28338335 = 42507503) B42507503
theorem B18892223 : Blo 2151435 18892223 := bstep (se 1 (by rfl) ⟨14169167, by rfl⟩ : syracuseStep 18892223 = 28338335) B28338335
theorem B12594815 : Blo 2151435 12594815 := bstep (se 1 (by rfl) ⟨9446111, by rfl⟩ : syracuseStep 12594815 = 18892223) B18892223
theorem B8396543 : Blo 2151435 8396543 := bstep (se 1 (by rfl) ⟨6297407, by rfl⟩ : syracuseStep 8396543 = 12594815) B12594815
theorem B5597695 : Blo 2151435 5597695 := bstep (se 1 (by rfl) ⟨4198271, by rfl⟩ : syracuseStep 5597695 = 8396543) B8396543
theorem B7463593 : Blo 2151435 7463593 := bstep (se 2 (by rfl) ⟨2798847, by rfl⟩ : syracuseStep 7463593 = 5597695) B5597695
theorem B39805829 : Blo 2151435 39805829 := bstep (se 4 (by rfl) ⟨3731796, by rfl⟩ : syracuseStep 39805829 = 7463593) B7463593
theorem B26537219 : Blo 2151435 26537219 := bstep (se 1 (by rfl) ⟨19902914, by rfl⟩ : syracuseStep 26537219 = 39805829) B39805829
theorem B17691479 : Blo 2151435 17691479 := bstep (se 1 (by rfl) ⟨13268609, by rfl⟩ : syracuseStep 17691479 = 26537219) B26537219
theorem B11794319 : Blo 2151435 11794319 := bstep (se 1 (by rfl) ⟨8845739, by rfl⟩ : syracuseStep 11794319 = 17691479) B17691479
theorem B7862879 : Blo 2151435 7862879 := bstep (se 1 (by rfl) ⟨5897159, by rfl⟩ : syracuseStep 7862879 = 11794319) B11794319
theorem B5241919 : Blo 2151435 5241919 := bstep (se 1 (by rfl) ⟨3931439, by rfl⟩ : syracuseStep 5241919 = 7862879) B7862879
theorem B6989225 : Blo 2151435 6989225 := bstep (se 2 (by rfl) ⟨2620959, by rfl⟩ : syracuseStep 6989225 = 5241919) B5241919
theorem B18637933 : Blo 2151435 18637933 := bstep (se 3 (by rfl) ⟨3494612, by rfl⟩ : syracuseStep 18637933 = 6989225) B6989225
theorem B24850577 : Blo 2151435 24850577 := bstep (se 2 (by rfl) ⟨9318966, by rfl⟩ : syracuseStep 24850577 = 18637933) B18637933
theorem B66268205 : Blo 2151435 66268205 := bstep (se 3 (by rfl) ⟨12425288, by rfl⟩ : syracuseStep 66268205 = 24850577) B24850577
theorem B44178803 : Blo 2151435 44178803 := bstep (se 1 (by rfl) ⟨33134102, by rfl⟩ : syracuseStep 44178803 = 66268205) B66268205
theorem B29452535 : Blo 2151435 29452535 := bstep (se 1 (by rfl) ⟨22089401, by rfl⟩ : syracuseStep 29452535 = 44178803) B44178803
theorem B19635023 : Blo 2151435 19635023 := bstep (se 1 (by rfl) ⟨14726267, by rfl⟩ : syracuseStep 19635023 = 29452535) B29452535
theorem B13090015 : Blo 2151435 13090015 := bstep (se 1 (by rfl) ⟨9817511, by rfl⟩ : syracuseStep 13090015 = 19635023) B19635023
theorem B17453353 : Blo 2151435 17453353 := bstep (se 2 (by rfl) ⟨6545007, by rfl⟩ : syracuseStep 17453353 = 13090015) B13090015
theorem B23271137 : Blo 2151435 23271137 := bstep (se 2 (by rfl) ⟨8726676, by rfl⟩ : syracuseStep 23271137 = 17453353) B17453353
theorem B15514091 : Blo 2151435 15514091 := bstep (se 1 (by rfl) ⟨11635568, by rfl⟩ : syracuseStep 15514091 = 23271137) B23271137
theorem B10342727 : Blo 2151435 10342727 := bstep (se 1 (by rfl) ⟨7757045, by rfl⟩ : syracuseStep 10342727 = 15514091) B15514091
theorem B6895151 : Blo 2151435 6895151 := bstep (se 1 (by rfl) ⟨5171363, by rfl⟩ : syracuseStep 6895151 = 10342727) B10342727
theorem B4596767 : Blo 2151435 4596767 := bstep (se 1 (by rfl) ⟨3447575, by rfl⟩ : syracuseStep 4596767 = 6895151) B6895151
theorem B3064511 : Blo 2151435 3064511 := bstep (se 1 (by rfl) ⟨2298383, by rfl⟩ : syracuseStep 3064511 = 4596767) B4596767
theorem B8172029 : Blo 2151435 8172029 := bstep (se 3 (by rfl) ⟨1532255, by rfl⟩ : syracuseStep 8172029 = 3064511) B3064511
theorem B5448019 : Blo 2151435 5448019 := bstep (se 1 (by rfl) ⟨4086014, by rfl⟩ : syracuseStep 5448019 = 8172029) B8172029
theorem B7264025 : Blo 2151435 7264025 := bstep (se 2 (by rfl) ⟨2724009, by rfl⟩ : syracuseStep 7264025 = 5448019) B5448019
theorem B4842683 : Blo 2151435 4842683 := bstep (se 1 (by rfl) ⟨3632012, by rfl⟩ : syracuseStep 4842683 = 7264025) B7264025
theorem B3228455 : Blo 2151435 3228455 := bstep (se 1 (by rfl) ⟨2421341, by rfl⟩ : syracuseStep 3228455 = 4842683) B4842683
theorem B2152303 : Blo 2151435 2152303 := bstep (se 1 (by rfl) ⟨1614227, by rfl⟩ : syracuseStep 2152303 = 3228455) B3228455
theorem B3228461 : Blo 2151435 3228461 := bbase (se 3 (by rfl) ⟨605336, by rfl⟩ : syracuseStep 3228461 = 1210673) (by norm_num)
theorem B2152307 : Blo 2151435 2152307 := bstep (se 1 (by rfl) ⟨1614230, by rfl⟩ : syracuseStep 2152307 = 3228461) B3228461
theorem B4842701 : Blo 2151435 4842701 := bbase (se 3 (by rfl) ⟨908006, by rfl⟩ : syracuseStep 4842701 = 1816013) (by norm_num)
theorem B3228467 : Blo 2151435 3228467 := bstep (se 1 (by rfl) ⟨2421350, by rfl⟩ : syracuseStep 3228467 = 4842701) B4842701
theorem B2152311 : Blo 2151435 2152311 := bstep (se 1 (by rfl) ⟨1614233, by rfl⟩ : syracuseStep 2152311 = 3228467) B3228467
theorem B2724025 : Blo 2151435 2724025 := bbase (se 2 (by rfl) ⟨1021509, by rfl⟩ : syracuseStep 2724025 = 2043019) (by norm_num)
theorem B3632033 : Blo 2151435 3632033 := bstep (se 2 (by rfl) ⟨1362012, by rfl⟩ : syracuseStep 3632033 = 2724025) B2724025
theorem B2421355 : Blo 2151435 2421355 := bstep (se 1 (by rfl) ⟨1816016, by rfl⟩ : syracuseStep 2421355 = 3632033) B3632033
theorem B3228473 : Blo 2151435 3228473 := bstep (se 2 (by rfl) ⟨1210677, by rfl⟩ : syracuseStep 3228473 = 2421355) B2421355
theorem B2152315 : Blo 2151435 2152315 := bstep (se 1 (by rfl) ⟨1614236, by rfl⟩ : syracuseStep 2152315 = 3228473) B3228473
theorem B8726741 : Blo 2151435 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B5817827 : Blo 2151435 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B3878551 : Blo 2151435 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B5171401 : Blo 2151435 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B6895201 : Blo 2151435 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B9193601 : Blo 2151435 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B24516269 : Blo 2151435 24516269 := bstep (se 3 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 24516269 = 9193601) B9193601
theorem B16344179 : Blo 2151435 16344179 := bstep (se 1 (by rfl) ⟨12258134, by rfl⟩ : syracuseStep 16344179 = 24516269) B24516269
theorem B10896119 : Blo 2151435 10896119 := bstep (se 1 (by rfl) ⟨8172089, by rfl⟩ : syracuseStep 10896119 = 16344179) B16344179
theorem B7264079 : Blo 2151435 7264079 := bstep (se 1 (by rfl) ⟨5448059, by rfl⟩ : syracuseStep 7264079 = 10896119) B10896119
theorem B4842719 : Blo 2151435 4842719 := bstep (se 1 (by rfl) ⟨3632039, by rfl⟩ : syracuseStep 4842719 = 7264079) B7264079
theorem B3228479 : Blo 2151435 3228479 := bstep (se 1 (by rfl) ⟨2421359, by rfl⟩ : syracuseStep 3228479 = 4842719) B4842719
theorem B2152319 : Blo 2151435 2152319 := bstep (se 1 (by rfl) ⟨1614239, by rfl⟩ : syracuseStep 2152319 = 3228479) B3228479
theorem B3228485 : Blo 2151435 3228485 := bbase (se 4 (by rfl) ⟨302670, by rfl⟩ : syracuseStep 3228485 = 605341) (by norm_num)
theorem B2152323 : Blo 2151435 2152323 := bstep (se 1 (by rfl) ⟨1614242, by rfl⟩ : syracuseStep 2152323 = 3228485) B3228485
theorem B3632053 : Blo 2151435 3632053 := bbase (se 5 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 3632053 = 340505) (by norm_num)
theorem B4842737 : Blo 2151435 4842737 := bstep (se 2 (by rfl) ⟨1816026, by rfl⟩ : syracuseStep 4842737 = 3632053) B3632053
theorem B3228491 : Blo 2151435 3228491 := bstep (se 1 (by rfl) ⟨2421368, by rfl⟩ : syracuseStep 3228491 = 4842737) B4842737
theorem B2152327 : Blo 2151435 2152327 := bstep (se 1 (by rfl) ⟨1614245, by rfl⟩ : syracuseStep 2152327 = 3228491) B3228491
theorem B2421373 : Blo 2151435 2421373 := bbase (se 3 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 2421373 = 908015) (by norm_num)
theorem B3228497 : Blo 2151435 3228497 := bstep (se 2 (by rfl) ⟨1210686, by rfl⟩ : syracuseStep 3228497 = 2421373) B2421373
theorem B2152331 : Blo 2151435 2152331 := bstep (se 1 (by rfl) ⟨1614248, by rfl⟩ : syracuseStep 2152331 = 3228497) B3228497
theorem B7264133 : Blo 2151435 7264133 := bbase (se 4 (by rfl) ⟨681012, by rfl⟩ : syracuseStep 7264133 = 1362025) (by norm_num)
theorem B4842755 : Blo 2151435 4842755 := bstep (se 1 (by rfl) ⟨3632066, by rfl⟩ : syracuseStep 4842755 = 7264133) B7264133
theorem B3228503 : Blo 2151435 3228503 := bstep (se 1 (by rfl) ⟨2421377, by rfl⟩ : syracuseStep 3228503 = 4842755) B4842755
theorem B2152335 : Blo 2151435 2152335 := bstep (se 1 (by rfl) ⟨1614251, by rfl⟩ : syracuseStep 2152335 = 3228503) B3228503
theorem B3228509 : Blo 2151435 3228509 := bbase (se 3 (by rfl) ⟨605345, by rfl⟩ : syracuseStep 3228509 = 1210691) (by norm_num)
theorem B2152339 : Blo 2151435 2152339 := bstep (se 1 (by rfl) ⟨1614254, by rfl⟩ : syracuseStep 2152339 = 3228509) B3228509
theorem B4842773 : Blo 2151435 4842773 := bbase (se 6 (by rfl) ⟨113502, by rfl⟩ : syracuseStep 4842773 = 227005) (by norm_num)
theorem B3228515 : Blo 2151435 3228515 := bstep (se 1 (by rfl) ⟨2421386, by rfl⟩ : syracuseStep 3228515 = 4842773) B4842773
theorem B2152343 : Blo 2151435 2152343 := bstep (se 1 (by rfl) ⟨1614257, by rfl⟩ : syracuseStep 2152343 = 3228515) B3228515
theorem B8172197 : Blo 2151435 8172197 := bbase (se 4 (by rfl) ⟨766143, by rfl⟩ : syracuseStep 8172197 = 1532287) (by norm_num)
theorem B5448131 : Blo 2151435 5448131 := bstep (se 1 (by rfl) ⟨4086098, by rfl⟩ : syracuseStep 5448131 = 8172197) B8172197
theorem B3632087 : Blo 2151435 3632087 := bstep (se 1 (by rfl) ⟨2724065, by rfl⟩ : syracuseStep 3632087 = 5448131) B5448131
theorem B2421391 : Blo 2151435 2421391 := bstep (se 1 (by rfl) ⟨1816043, by rfl⟩ : syracuseStep 2421391 = 3632087) B3632087
theorem B3228521 : Blo 2151435 3228521 := bstep (se 2 (by rfl) ⟨1210695, by rfl⟩ : syracuseStep 3228521 = 2421391) B2421391
theorem B2152347 : Blo 2151435 2152347 := bstep (se 1 (by rfl) ⟨1614260, by rfl⟩ : syracuseStep 2152347 = 3228521) B3228521
theorem B4596869 : Blo 2151435 4596869 := bbase (se 4 (by rfl) ⟨430956, by rfl⟩ : syracuseStep 4596869 = 861913) (by norm_num)
theorem B12258317 : Blo 2151435 12258317 := bstep (se 3 (by rfl) ⟨2298434, by rfl⟩ : syracuseStep 12258317 = 4596869) B4596869
theorem B8172211 : Blo 2151435 8172211 := bstep (se 1 (by rfl) ⟨6129158, by rfl⟩ : syracuseStep 8172211 = 12258317) B12258317
theorem B10896281 : Blo 2151435 10896281 := bstep (se 2 (by rfl) ⟨4086105, by rfl⟩ : syracuseStep 10896281 = 8172211) B8172211
theorem B7264187 : Blo 2151435 7264187 := bstep (se 1 (by rfl) ⟨5448140, by rfl⟩ : syracuseStep 7264187 = 10896281) B10896281
theorem B4842791 : Blo 2151435 4842791 := bstep (se 1 (by rfl) ⟨3632093, by rfl⟩ : syracuseStep 4842791 = 7264187) B7264187
theorem B3228527 : Blo 2151435 3228527 := bstep (se 1 (by rfl) ⟨2421395, by rfl⟩ : syracuseStep 3228527 = 4842791) B4842791
theorem B2152351 : Blo 2151435 2152351 := bstep (se 1 (by rfl) ⟨1614263, by rfl⟩ : syracuseStep 2152351 = 3228527) B3228527
theorem B3228533 : Blo 2151435 3228533 := bbase (se 5 (by rfl) ⟨151337, by rfl⟩ : syracuseStep 3228533 = 302675) (by norm_num)
theorem B2152355 : Blo 2151435 2152355 := bstep (se 1 (by rfl) ⟨1614266, by rfl⟩ : syracuseStep 2152355 = 3228533) B3228533
theorem B10342997 : Blo 2151435 10342997 := bbase (se 8 (by rfl) ⟨60603, by rfl⟩ : syracuseStep 10342997 = 121207) (by norm_num)
theorem B6895331 : Blo 2151435 6895331 := bstep (se 1 (by rfl) ⟨5171498, by rfl⟩ : syracuseStep 6895331 = 10342997) B10342997
theorem B4596887 : Blo 2151435 4596887 := bstep (se 1 (by rfl) ⟨3447665, by rfl⟩ : syracuseStep 4596887 = 6895331) B6895331
theorem B3064591 : Blo 2151435 3064591 := bstep (se 1 (by rfl) ⟨2298443, by rfl⟩ : syracuseStep 3064591 = 4596887) B4596887
theorem B4086121 : Blo 2151435 4086121 := bstep (se 2 (by rfl) ⟨1532295, by rfl⟩ : syracuseStep 4086121 = 3064591) B3064591
theorem B5448161 : Blo 2151435 5448161 := bstep (se 2 (by rfl) ⟨2043060, by rfl⟩ : syracuseStep 5448161 = 4086121) B4086121
theorem B3632107 : Blo 2151435 3632107 := bstep (se 1 (by rfl) ⟨2724080, by rfl⟩ : syracuseStep 3632107 = 5448161) B5448161
theorem B4842809 : Blo 2151435 4842809 := bstep (se 2 (by rfl) ⟨1816053, by rfl⟩ : syracuseStep 4842809 = 3632107) B3632107
theorem B3228539 : Blo 2151435 3228539 := bstep (se 1 (by rfl) ⟨2421404, by rfl⟩ : syracuseStep 3228539 = 4842809) B4842809
theorem B2152359 : Blo 2151435 2152359 := bstep (se 1 (by rfl) ⟨1614269, by rfl⟩ : syracuseStep 2152359 = 3228539) B3228539
theorem B2421409 : Blo 2151435 2421409 := bbase (se 2 (by rfl) ⟨908028, by rfl⟩ : syracuseStep 2421409 = 1816057) (by norm_num)
theorem B3228545 : Blo 2151435 3228545 := bstep (se 2 (by rfl) ⟨1210704, by rfl⟩ : syracuseStep 3228545 = 2421409) B2421409
theorem B2152363 : Blo 2151435 2152363 := bstep (se 1 (by rfl) ⟨1614272, by rfl⟩ : syracuseStep 2152363 = 3228545) B3228545
theorem B5448181 : Blo 2151435 5448181 := bbase (se 5 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 5448181 = 510767) (by norm_num)
theorem B7264241 : Blo 2151435 7264241 := bstep (se 2 (by rfl) ⟨2724090, by rfl⟩ : syracuseStep 7264241 = 5448181) B5448181
theorem B4842827 : Blo 2151435 4842827 := bstep (se 1 (by rfl) ⟨3632120, by rfl⟩ : syracuseStep 4842827 = 7264241) B7264241
theorem B3228551 : Blo 2151435 3228551 := bstep (se 1 (by rfl) ⟨2421413, by rfl⟩ : syracuseStep 3228551 = 4842827) B4842827
theorem B2152367 : Blo 2151435 2152367 := bstep (se 1 (by rfl) ⟨1614275, by rfl⟩ : syracuseStep 2152367 = 3228551) B3228551
theorem B3228557 : Blo 2151435 3228557 := bbase (se 3 (by rfl) ⟨605354, by rfl⟩ : syracuseStep 3228557 = 1210709) (by norm_num)
theorem B2152371 : Blo 2151435 2152371 := bstep (se 1 (by rfl) ⟨1614278, by rfl⟩ : syracuseStep 2152371 = 3228557) B3228557
theorem B4842845 : Blo 2151435 4842845 := bbase (se 3 (by rfl) ⟨908033, by rfl⟩ : syracuseStep 4842845 = 1816067) (by norm_num)
theorem B3228563 : Blo 2151435 3228563 := bstep (se 1 (by rfl) ⟨2421422, by rfl⟩ : syracuseStep 3228563 = 4842845) B4842845
theorem B2152375 : Blo 2151435 2152375 := bstep (se 1 (by rfl) ⟨1614281, by rfl⟩ : syracuseStep 2152375 = 3228563) B3228563
theorem B3632141 : Blo 2151435 3632141 := bbase (se 3 (by rfl) ⟨681026, by rfl⟩ : syracuseStep 3632141 = 1362053) (by norm_num)
theorem B2421427 : Blo 2151435 2421427 := bstep (se 1 (by rfl) ⟨1816070, by rfl⟩ : syracuseStep 2421427 = 3632141) B3632141
theorem B3228569 : Blo 2151435 3228569 := bstep (se 2 (by rfl) ⟨1210713, by rfl⟩ : syracuseStep 3228569 = 2421427) B2421427
theorem B2152379 : Blo 2151435 2152379 := bstep (se 1 (by rfl) ⟨1614284, by rfl⟩ : syracuseStep 2152379 = 3228569) B3228569
theorem B7757333 : Blo 2151435 7757333 := bbase (se 6 (by rfl) ⟨181812, by rfl⟩ : syracuseStep 7757333 = 363625) (by norm_num)
theorem B5171555 : Blo 2151435 5171555 := bstep (se 1 (by rfl) ⟨3878666, by rfl⟩ : syracuseStep 5171555 = 7757333) B7757333
theorem B3447703 : Blo 2151435 3447703 := bstep (se 1 (by rfl) ⟨2585777, by rfl⟩ : syracuseStep 3447703 = 5171555) B5171555
theorem B18387749 : Blo 2151435 18387749 := bstep (se 4 (by rfl) ⟨1723851, by rfl⟩ : syracuseStep 18387749 = 3447703) B3447703
theorem B12258499 : Blo 2151435 12258499 := bstep (se 1 (by rfl) ⟨9193874, by rfl⟩ : syracuseStep 12258499 = 18387749) B18387749
theorem B16344665 : Blo 2151435 16344665 := bstep (se 2 (by rfl) ⟨6129249, by rfl⟩ : syracuseStep 16344665 = 12258499) B12258499
theorem B10896443 : Blo 2151435 10896443 := bstep (se 1 (by rfl) ⟨8172332, by rfl⟩ : syracuseStep 10896443 = 16344665) B16344665
theorem B7264295 : Blo 2151435 7264295 := bstep (se 1 (by rfl) ⟨5448221, by rfl⟩ : syracuseStep 7264295 = 10896443) B10896443
theorem B4842863 : Blo 2151435 4842863 := bstep (se 1 (by rfl) ⟨3632147, by rfl⟩ : syracuseStep 4842863 = 7264295) B7264295
theorem B3228575 : Blo 2151435 3228575 := bstep (se 1 (by rfl) ⟨2421431, by rfl⟩ : syracuseStep 3228575 = 4842863) B4842863
theorem B2152383 : Blo 2151435 2152383 := bstep (se 1 (by rfl) ⟨1614287, by rfl⟩ : syracuseStep 2152383 = 3228575) B3228575
theorem B3228581 : Blo 2151435 3228581 := bbase (se 4 (by rfl) ⟨302679, by rfl⟩ : syracuseStep 3228581 = 605359) (by norm_num)
theorem B2152387 : Blo 2151435 2152387 := bstep (se 1 (by rfl) ⟨1614290, by rfl⟩ : syracuseStep 2152387 = 3228581) B3228581
theorem B2724121 : Blo 2151435 2724121 := bbase (se 2 (by rfl) ⟨1021545, by rfl⟩ : syracuseStep 2724121 = 2043091) (by norm_num)
theorem B3632161 : Blo 2151435 3632161 := bstep (se 2 (by rfl) ⟨1362060, by rfl⟩ : syracuseStep 3632161 = 2724121) B2724121
theorem B4842881 : Blo 2151435 4842881 := bstep (se 2 (by rfl) ⟨1816080, by rfl⟩ : syracuseStep 4842881 = 3632161) B3632161
theorem B3228587 : Blo 2151435 3228587 := bstep (se 1 (by rfl) ⟨2421440, by rfl⟩ : syracuseStep 3228587 = 4842881) B4842881
theorem B2152391 : Blo 2151435 2152391 := bstep (se 1 (by rfl) ⟨1614293, by rfl⟩ : syracuseStep 2152391 = 3228587) B3228587
theorem B2421445 : Blo 2151435 2421445 := bbase (se 4 (by rfl) ⟨227010, by rfl⟩ : syracuseStep 2421445 = 454021) (by norm_num)
theorem B3228593 : Blo 2151435 3228593 := bstep (se 2 (by rfl) ⟨1210722, by rfl⟩ : syracuseStep 3228593 = 2421445) B2421445
theorem B2152395 : Blo 2151435 2152395 := bstep (se 1 (by rfl) ⟨1614296, by rfl⟩ : syracuseStep 2152395 = 3228593) B3228593
theorem B4086197 : Blo 2151435 4086197 := bbase (se 5 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 4086197 = 383081) (by norm_num)
theorem B2724131 : Blo 2151435 2724131 := bstep (se 1 (by rfl) ⟨2043098, by rfl⟩ : syracuseStep 2724131 = 4086197) B4086197
theorem B7264349 : Blo 2151435 7264349 := bstep (se 3 (by rfl) ⟨1362065, by rfl⟩ : syracuseStep 7264349 = 2724131) B2724131
theorem B4842899 : Blo 2151435 4842899 := bstep (se 1 (by rfl) ⟨3632174, by rfl⟩ : syracuseStep 4842899 = 7264349) B7264349
theorem B3228599 : Blo 2151435 3228599 := bstep (se 1 (by rfl) ⟨2421449, by rfl⟩ : syracuseStep 3228599 = 4842899) B4842899
theorem B2152399 : Blo 2151435 2152399 := bstep (se 1 (by rfl) ⟨1614299, by rfl⟩ : syracuseStep 2152399 = 3228599) B3228599
theorem B3228605 : Blo 2151435 3228605 := bbase (se 3 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 3228605 = 1210727) (by norm_num)
theorem B2152403 : Blo 2151435 2152403 := bstep (se 1 (by rfl) ⟨1614302, by rfl⟩ : syracuseStep 2152403 = 3228605) B3228605
theorem B4842917 : Blo 2151435 4842917 := bbase (se 4 (by rfl) ⟨454023, by rfl⟩ : syracuseStep 4842917 = 908047) (by norm_num)
theorem B3228611 : Blo 2151435 3228611 := bstep (se 1 (by rfl) ⟨2421458, by rfl⟩ : syracuseStep 3228611 = 4842917) B4842917
theorem B2152407 : Blo 2151435 2152407 := bstep (se 1 (by rfl) ⟨1614305, by rfl⟩ : syracuseStep 2152407 = 3228611) B3228611
theorem B5448293 : Blo 2151435 5448293 := bbase (se 4 (by rfl) ⟨510777, by rfl⟩ : syracuseStep 5448293 = 1021555) (by norm_num)
theorem B3632195 : Blo 2151435 3632195 := bstep (se 1 (by rfl) ⟨2724146, by rfl⟩ : syracuseStep 3632195 = 5448293) B5448293
theorem B2421463 : Blo 2151435 2421463 := bstep (se 1 (by rfl) ⟨1816097, by rfl⟩ : syracuseStep 2421463 = 3632195) B3632195
theorem B3228617 : Blo 2151435 3228617 := bstep (se 2 (by rfl) ⟨1210731, by rfl⟩ : syracuseStep 3228617 = 2421463) B2421463
theorem B2152411 : Blo 2151435 2152411 := bstep (se 1 (by rfl) ⟨1614308, by rfl⟩ : syracuseStep 2152411 = 3228617) B3228617
theorem B3878725 : Blo 2151435 3878725 := bbase (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) (by norm_num)
theorem B5171633 : Blo 2151435 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B3447755 : Blo 2151435 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B2298503 : Blo 2151435 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B6129341 : Blo 2151435 6129341 := bstep (se 3 (by rfl) ⟨1149251, by rfl⟩ : syracuseStep 6129341 = 2298503) B2298503
theorem B4086227 : Blo 2151435 4086227 := bstep (se 1 (by rfl) ⟨3064670, by rfl⟩ : syracuseStep 4086227 = 6129341) B6129341
theorem B10896605 : Blo 2151435 10896605 := bstep (se 3 (by rfl) ⟨2043113, by rfl⟩ : syracuseStep 10896605 = 4086227) B4086227
theorem B7264403 : Blo 2151435 7264403 := bstep (se 1 (by rfl) ⟨5448302, by rfl⟩ : syracuseStep 7264403 = 10896605) B10896605
theorem B4842935 : Blo 2151435 4842935 := bstep (se 1 (by rfl) ⟨3632201, by rfl⟩ : syracuseStep 4842935 = 7264403) B7264403
theorem B3228623 : Blo 2151435 3228623 := bstep (se 1 (by rfl) ⟨2421467, by rfl⟩ : syracuseStep 3228623 = 4842935) B4842935
theorem B2152415 : Blo 2151435 2152415 := bstep (se 1 (by rfl) ⟨1614311, by rfl⟩ : syracuseStep 2152415 = 3228623) B3228623
theorem B3228629 : Blo 2151435 3228629 := bbase (se 7 (by rfl) ⟨37835, by rfl⟩ : syracuseStep 3228629 = 75671) (by norm_num)
theorem B2152419 : Blo 2151435 2152419 := bstep (se 1 (by rfl) ⟨1614314, by rfl⟩ : syracuseStep 2152419 = 3228629) B3228629
theorem B8172485 : Blo 2151435 8172485 := bbase (se 4 (by rfl) ⟨766170, by rfl⟩ : syracuseStep 8172485 = 1532341) (by norm_num)
theorem B5448323 : Blo 2151435 5448323 := bstep (se 1 (by rfl) ⟨4086242, by rfl⟩ : syracuseStep 5448323 = 8172485) B8172485
theorem B3632215 : Blo 2151435 3632215 := bstep (se 1 (by rfl) ⟨2724161, by rfl⟩ : syracuseStep 3632215 = 5448323) B5448323
theorem B4842953 : Blo 2151435 4842953 := bstep (se 2 (by rfl) ⟨1816107, by rfl⟩ : syracuseStep 4842953 = 3632215) B3632215
theorem B3228635 : Blo 2151435 3228635 := bstep (se 1 (by rfl) ⟨2421476, by rfl⟩ : syracuseStep 3228635 = 4842953) B4842953
theorem B2152423 : Blo 2151435 2152423 := bstep (se 1 (by rfl) ⟨1614317, by rfl⟩ : syracuseStep 2152423 = 3228635) B3228635
theorem B2421481 : Blo 2151435 2421481 := bbase (se 2 (by rfl) ⟨908055, by rfl⟩ : syracuseStep 2421481 = 1816111) (by norm_num)
theorem B3228641 : Blo 2151435 3228641 := bstep (se 2 (by rfl) ⟨1210740, by rfl⟩ : syracuseStep 3228641 = 2421481) B2421481
theorem B2152427 : Blo 2151435 2152427 := bstep (se 1 (by rfl) ⟨1614320, by rfl⟩ : syracuseStep 2152427 = 3228641) B3228641
theorem B12258773 : Blo 2151435 12258773 := bbase (se 7 (by rfl) ⟨143657, by rfl⟩ : syracuseStep 12258773 = 287315) (by norm_num)
theorem B8172515 : Blo 2151435 8172515 := bstep (se 1 (by rfl) ⟨6129386, by rfl⟩ : syracuseStep 8172515 = 12258773) B12258773
theorem B5448343 : Blo 2151435 5448343 := bstep (se 1 (by rfl) ⟨4086257, by rfl⟩ : syracuseStep 5448343 = 8172515) B8172515
theorem B7264457 : Blo 2151435 7264457 := bstep (se 2 (by rfl) ⟨2724171, by rfl⟩ : syracuseStep 7264457 = 5448343) B5448343
theorem B4842971 : Blo 2151435 4842971 := bstep (se 1 (by rfl) ⟨3632228, by rfl⟩ : syracuseStep 4842971 = 7264457) B7264457
theorem B3228647 : Blo 2151435 3228647 := bstep (se 1 (by rfl) ⟨2421485, by rfl⟩ : syracuseStep 3228647 = 4842971) B4842971
theorem B2152431 : Blo 2151435 2152431 := bstep (se 1 (by rfl) ⟨1614323, by rfl⟩ : syracuseStep 2152431 = 3228647) B3228647
theorem B3228653 : Blo 2151435 3228653 := bbase (se 3 (by rfl) ⟨605372, by rfl⟩ : syracuseStep 3228653 = 1210745) (by norm_num)
theorem B2152435 : Blo 2151435 2152435 := bstep (se 1 (by rfl) ⟨1614326, by rfl⟩ : syracuseStep 2152435 = 3228653) B3228653
theorem B4842989 : Blo 2151435 4842989 := bbase (se 3 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 4842989 = 1816121) (by norm_num)
theorem B3228659 : Blo 2151435 3228659 := bstep (se 1 (by rfl) ⟨2421494, by rfl⟩ : syracuseStep 3228659 = 4842989) B4842989
theorem B2152439 : Blo 2151435 2152439 := bstep (se 1 (by rfl) ⟨1614329, by rfl⟩ : syracuseStep 2152439 = 3228659) B3228659
theorem B5171701 : Blo 2151435 5171701 := bbase (se 5 (by rfl) ⟨242423, by rfl⟩ : syracuseStep 5171701 = 484847) (by norm_num)
theorem B6895601 : Blo 2151435 6895601 := bstep (se 2 (by rfl) ⟨2585850, by rfl⟩ : syracuseStep 6895601 = 5171701) B5171701
theorem B4597067 : Blo 2151435 4597067 := bstep (se 1 (by rfl) ⟨3447800, by rfl⟩ : syracuseStep 4597067 = 6895601) B6895601
theorem B3064711 : Blo 2151435 3064711 := bstep (se 1 (by rfl) ⟨2298533, by rfl⟩ : syracuseStep 3064711 = 4597067) B4597067
theorem B4086281 : Blo 2151435 4086281 := bstep (se 2 (by rfl) ⟨1532355, by rfl⟩ : syracuseStep 4086281 = 3064711) B3064711
theorem B2724187 : Blo 2151435 2724187 := bstep (se 1 (by rfl) ⟨2043140, by rfl⟩ : syracuseStep 2724187 = 4086281) B4086281
theorem B3632249 : Blo 2151435 3632249 := bstep (se 2 (by rfl) ⟨1362093, by rfl⟩ : syracuseStep 3632249 = 2724187) B2724187
theorem B2421499 : Blo 2151435 2421499 := bstep (se 1 (by rfl) ⟨1816124, by rfl⟩ : syracuseStep 2421499 = 3632249) B3632249
theorem B3228665 : Blo 2151435 3228665 := bstep (se 2 (by rfl) ⟨1210749, by rfl⟩ : syracuseStep 3228665 = 2421499) B2421499
theorem B2152443 : Blo 2151435 2152443 := bstep (se 1 (by rfl) ⟨1614332, by rfl⟩ : syracuseStep 2152443 = 3228665) B3228665
theorem B9575621 : Blo 2151435 9575621 := bbase (se 4 (by rfl) ⟨897714, by rfl⟩ : syracuseStep 9575621 = 1795429) (by norm_num)
theorem B102139957 : Blo 2151435 102139957 := bstep (se 5 (by rfl) ⟨4787810, by rfl⟩ : syracuseStep 102139957 = 9575621) B9575621
theorem B136186609 : Blo 2151435 136186609 := bstep (se 2 (by rfl) ⟨51069978, by rfl⟩ : syracuseStep 136186609 = 102139957) B102139957
theorem B181582145 : Blo 2151435 181582145 := bstep (se 2 (by rfl) ⟨68093304, by rfl⟩ : syracuseStep 181582145 = 136186609) B136186609
theorem B121054763 : Blo 2151435 121054763 := bstep (se 1 (by rfl) ⟨90791072, by rfl⟩ : syracuseStep 121054763 = 181582145) B181582145
theorem B80703175 : Blo 2151435 80703175 := bstep (se 1 (by rfl) ⟨60527381, by rfl⟩ : syracuseStep 80703175 = 121054763) B121054763
theorem B107604233 : Blo 2151435 107604233 := bstep (se 2 (by rfl) ⟨40351587, by rfl⟩ : syracuseStep 107604233 = 80703175) B80703175
theorem B71736155 : Blo 2151435 71736155 := bstep (se 1 (by rfl) ⟨53802116, by rfl⟩ : syracuseStep 71736155 = 107604233) B107604233
theorem B47824103 : Blo 2151435 47824103 := bstep (se 1 (by rfl) ⟨35868077, by rfl⟩ : syracuseStep 47824103 = 71736155) B71736155
theorem B127530941 : Blo 2151435 127530941 := bstep (se 3 (by rfl) ⟨23912051, by rfl⟩ : syracuseStep 127530941 = 47824103) B47824103
theorem B340082509 : Blo 2151435 340082509 := bstep (se 3 (by rfl) ⟨63765470, by rfl⟩ : syracuseStep 340082509 = 127530941) B127530941
theorem B453443345 : Blo 2151435 453443345 := bstep (se 2 (by rfl) ⟨170041254, by rfl⟩ : syracuseStep 453443345 = 340082509) B340082509
theorem B302295563 : Blo 2151435 302295563 := bstep (se 1 (by rfl) ⟨226721672, by rfl⟩ : syracuseStep 302295563 = 453443345) B453443345
theorem B201530375 : Blo 2151435 201530375 := bstep (se 1 (by rfl) ⟨151147781, by rfl⟩ : syracuseStep 201530375 = 302295563) B302295563
theorem B134353583 : Blo 2151435 134353583 := bstep (se 1 (by rfl) ⟨100765187, by rfl⟩ : syracuseStep 134353583 = 201530375) B201530375
theorem B89569055 : Blo 2151435 89569055 := bstep (se 1 (by rfl) ⟨67176791, by rfl⟩ : syracuseStep 89569055 = 134353583) B134353583
theorem B238850813 : Blo 2151435 238850813 := bstep (se 3 (by rfl) ⟨44784527, by rfl⟩ : syracuseStep 238850813 = 89569055) B89569055
theorem B636935501 : Blo 2151435 636935501 := bstep (se 3 (by rfl) ⟨119425406, by rfl⟩ : syracuseStep 636935501 = 238850813) B238850813
theorem B424623667 : Blo 2151435 424623667 := bstep (se 1 (by rfl) ⟨318467750, by rfl⟩ : syracuseStep 424623667 = 636935501) B636935501
theorem B566164889 : Blo 2151435 566164889 := bstep (se 2 (by rfl) ⟨212311833, by rfl⟩ : syracuseStep 566164889 = 424623667) B424623667
theorem B377443259 : Blo 2151435 377443259 := bstep (se 1 (by rfl) ⟨283082444, by rfl⟩ : syracuseStep 377443259 = 566164889) B566164889
theorem B251628839 : Blo 2151435 251628839 := bstep (se 1 (by rfl) ⟨188721629, by rfl⟩ : syracuseStep 251628839 = 377443259) B377443259
theorem B167752559 : Blo 2151435 167752559 := bstep (se 1 (by rfl) ⟨125814419, by rfl⟩ : syracuseStep 167752559 = 251628839) B251628839
theorem B447340157 : Blo 2151435 447340157 := bstep (se 3 (by rfl) ⟨83876279, by rfl⟩ : syracuseStep 447340157 = 167752559) B167752559
theorem B298226771 : Blo 2151435 298226771 := bstep (se 1 (by rfl) ⟨223670078, by rfl⟩ : syracuseStep 298226771 = 447340157) B447340157
theorem B198817847 : Blo 2151435 198817847 := bstep (se 1 (by rfl) ⟨149113385, by rfl⟩ : syracuseStep 198817847 = 298226771) B298226771
theorem B132545231 : Blo 2151435 132545231 := bstep (se 1 (by rfl) ⟨99408923, by rfl⟩ : syracuseStep 132545231 = 198817847) B198817847
theorem B88363487 : Blo 2151435 88363487 := bstep (se 1 (by rfl) ⟨66272615, by rfl⟩ : syracuseStep 88363487 = 132545231) B132545231
theorem B58908991 : Blo 2151435 58908991 := bstep (se 1 (by rfl) ⟨44181743, by rfl⟩ : syracuseStep 58908991 = 88363487) B88363487
theorem B78545321 : Blo 2151435 78545321 := bstep (se 2 (by rfl) ⟨29454495, by rfl⟩ : syracuseStep 78545321 = 58908991) B58908991
theorem B52363547 : Blo 2151435 52363547 := bstep (se 1 (by rfl) ⟨39272660, by rfl⟩ : syracuseStep 52363547 = 78545321) B78545321
theorem B34909031 : Blo 2151435 34909031 := bstep (se 1 (by rfl) ⟨26181773, by rfl⟩ : syracuseStep 34909031 = 52363547) B52363547
theorem B23272687 : Blo 2151435 23272687 := bstep (se 1 (by rfl) ⟨17454515, by rfl⟩ : syracuseStep 23272687 = 34909031) B34909031
theorem B124120997 : Blo 2151435 124120997 := bstep (se 4 (by rfl) ⟨11636343, by rfl⟩ : syracuseStep 124120997 = 23272687) B23272687
theorem B82747331 : Blo 2151435 82747331 := bstep (se 1 (by rfl) ⟨62060498, by rfl⟩ : syracuseStep 82747331 = 124120997) B124120997
theorem B55164887 : Blo 2151435 55164887 := bstep (se 1 (by rfl) ⟨41373665, by rfl⟩ : syracuseStep 55164887 = 82747331) B82747331
theorem B36776591 : Blo 2151435 36776591 := bstep (se 1 (by rfl) ⟨27582443, by rfl⟩ : syracuseStep 36776591 = 55164887) B55164887
theorem B24517727 : Blo 2151435 24517727 := bstep (se 1 (by rfl) ⟨18388295, by rfl⟩ : syracuseStep 24517727 = 36776591) B36776591
theorem B16345151 : Blo 2151435 16345151 := bstep (se 1 (by rfl) ⟨12258863, by rfl⟩ : syracuseStep 16345151 = 24517727) B24517727
theorem B10896767 : Blo 2151435 10896767 := bstep (se 1 (by rfl) ⟨8172575, by rfl⟩ : syracuseStep 10896767 = 16345151) B16345151
theorem B7264511 : Blo 2151435 7264511 := bstep (se 1 (by rfl) ⟨5448383, by rfl⟩ : syracuseStep 7264511 = 10896767) B10896767
theorem B4843007 : Blo 2151435 4843007 := bstep (se 1 (by rfl) ⟨3632255, by rfl⟩ : syracuseStep 4843007 = 7264511) B7264511
theorem B3228671 : Blo 2151435 3228671 := bstep (se 1 (by rfl) ⟨2421503, by rfl⟩ : syracuseStep 3228671 = 4843007) B4843007
theorem B2152447 : Blo 2151435 2152447 := bstep (se 1 (by rfl) ⟨1614335, by rfl⟩ : syracuseStep 2152447 = 3228671) B3228671
theorem B3228677 : Blo 2151435 3228677 := bbase (se 4 (by rfl) ⟨302688, by rfl⟩ : syracuseStep 3228677 = 605377) (by norm_num)
theorem B2152451 : Blo 2151435 2152451 := bstep (se 1 (by rfl) ⟨1614338, by rfl⟩ : syracuseStep 2152451 = 3228677) B3228677
theorem B3632269 : Blo 2151435 3632269 := bbase (se 3 (by rfl) ⟨681050, by rfl⟩ : syracuseStep 3632269 = 1362101) (by norm_num)
theorem B4843025 : Blo 2151435 4843025 := bstep (se 2 (by rfl) ⟨1816134, by rfl⟩ : syracuseStep 4843025 = 3632269) B3632269
theorem B3228683 : Blo 2151435 3228683 := bstep (se 1 (by rfl) ⟨2421512, by rfl⟩ : syracuseStep 3228683 = 4843025) B4843025
theorem B2152455 : Blo 2151435 2152455 := bstep (se 1 (by rfl) ⟨1614341, by rfl⟩ : syracuseStep 2152455 = 3228683) B3228683
theorem B2421517 : Blo 2151435 2421517 := bbase (se 3 (by rfl) ⟨454034, by rfl⟩ : syracuseStep 2421517 = 908069) (by norm_num)
theorem B3228689 : Blo 2151435 3228689 := bstep (se 2 (by rfl) ⟨1210758, by rfl⟩ : syracuseStep 3228689 = 2421517) B2421517
theorem B2152459 : Blo 2151435 2152459 := bstep (se 1 (by rfl) ⟨1614344, by rfl⟩ : syracuseStep 2152459 = 3228689) B3228689
theorem B7264565 : Blo 2151435 7264565 := bbase (se 5 (by rfl) ⟨340526, by rfl⟩ : syracuseStep 7264565 = 681053) (by norm_num)
theorem B4843043 : Blo 2151435 4843043 := bstep (se 1 (by rfl) ⟨3632282, by rfl⟩ : syracuseStep 4843043 = 7264565) B7264565
theorem B3228695 : Blo 2151435 3228695 := bstep (se 1 (by rfl) ⟨2421521, by rfl⟩ : syracuseStep 3228695 = 4843043) B4843043
theorem B2152463 : Blo 2151435 2152463 := bstep (se 1 (by rfl) ⟨1614347, by rfl⟩ : syracuseStep 2152463 = 3228695) B3228695
theorem B3228701 : Blo 2151435 3228701 := bbase (se 3 (by rfl) ⟨605381, by rfl⟩ : syracuseStep 3228701 = 1210763) (by norm_num)
theorem B2152467 : Blo 2151435 2152467 := bstep (se 1 (by rfl) ⟨1614350, by rfl⟩ : syracuseStep 2152467 = 3228701) B3228701
theorem B4843061 : Blo 2151435 4843061 := bbase (se 5 (by rfl) ⟨227018, by rfl⟩ : syracuseStep 4843061 = 454037) (by norm_num)
theorem B3228707 : Blo 2151435 3228707 := bstep (se 1 (by rfl) ⟨2421530, by rfl⟩ : syracuseStep 3228707 = 4843061) B4843061
theorem B2152471 : Blo 2151435 2152471 := bstep (se 1 (by rfl) ⟨1614353, by rfl⟩ : syracuseStep 2152471 = 3228707) B3228707
theorem B2909125 : Blo 2151435 2909125 := bbase (se 4 (by rfl) ⟨272730, by rfl⟩ : syracuseStep 2909125 = 545461) (by norm_num)
theorem B3878833 : Blo 2151435 3878833 := bstep (se 2 (by rfl) ⟨1454562, by rfl⟩ : syracuseStep 3878833 = 2909125) B2909125
theorem B5171777 : Blo 2151435 5171777 := bstep (se 2 (by rfl) ⟨1939416, by rfl⟩ : syracuseStep 5171777 = 3878833) B3878833
theorem B3447851 : Blo 2151435 3447851 := bstep (se 1 (by rfl) ⟨2585888, by rfl⟩ : syracuseStep 3447851 = 5171777) B5171777
theorem B9194269 : Blo 2151435 9194269 := bstep (se 3 (by rfl) ⟨1723925, by rfl⟩ : syracuseStep 9194269 = 3447851) B3447851
theorem B12259025 : Blo 2151435 12259025 := bstep (se 2 (by rfl) ⟨4597134, by rfl⟩ : syracuseStep 12259025 = 9194269) B9194269
theorem B8172683 : Blo 2151435 8172683 := bstep (se 1 (by rfl) ⟨6129512, by rfl⟩ : syracuseStep 8172683 = 12259025) B12259025
theorem B5448455 : Blo 2151435 5448455 := bstep (se 1 (by rfl) ⟨4086341, by rfl⟩ : syracuseStep 5448455 = 8172683) B8172683
theorem B3632303 : Blo 2151435 3632303 := bstep (se 1 (by rfl) ⟨2724227, by rfl⟩ : syracuseStep 3632303 = 5448455) B5448455
theorem B2421535 : Blo 2151435 2421535 := bstep (se 1 (by rfl) ⟨1816151, by rfl⟩ : syracuseStep 2421535 = 3632303) B3632303
theorem B3228713 : Blo 2151435 3228713 := bstep (se 2 (by rfl) ⟨1210767, by rfl⟩ : syracuseStep 3228713 = 2421535) B2421535
theorem B2152475 : Blo 2151435 2152475 := bstep (se 1 (by rfl) ⟨1614356, by rfl⟩ : syracuseStep 2152475 = 3228713) B3228713
theorem B2585893 : Blo 2151435 2585893 := bbase (se 4 (by rfl) ⟨242427, by rfl⟩ : syracuseStep 2585893 = 484855) (by norm_num)
theorem B3447857 : Blo 2151435 3447857 := bstep (se 2 (by rfl) ⟨1292946, by rfl⟩ : syracuseStep 3447857 = 2585893) B2585893
theorem B9194285 : Blo 2151435 9194285 := bstep (se 3 (by rfl) ⟨1723928, by rfl⟩ : syracuseStep 9194285 = 3447857) B3447857
theorem B6129523 : Blo 2151435 6129523 := bstep (se 1 (by rfl) ⟨4597142, by rfl⟩ : syracuseStep 6129523 = 9194285) B9194285
theorem B8172697 : Blo 2151435 8172697 := bstep (se 2 (by rfl) ⟨3064761, by rfl⟩ : syracuseStep 8172697 = 6129523) B6129523
theorem B10896929 : Blo 2151435 10896929 := bstep (se 2 (by rfl) ⟨4086348, by rfl⟩ : syracuseStep 10896929 = 8172697) B8172697
theorem B7264619 : Blo 2151435 7264619 := bstep (se 1 (by rfl) ⟨5448464, by rfl⟩ : syracuseStep 7264619 = 10896929) B10896929
theorem B4843079 : Blo 2151435 4843079 := bstep (se 1 (by rfl) ⟨3632309, by rfl⟩ : syracuseStep 4843079 = 7264619) B7264619
theorem B3228719 : Blo 2151435 3228719 := bstep (se 1 (by rfl) ⟨2421539, by rfl⟩ : syracuseStep 3228719 = 4843079) B4843079
theorem B2152479 : Blo 2151435 2152479 := bstep (se 1 (by rfl) ⟨1614359, by rfl⟩ : syracuseStep 2152479 = 3228719) B3228719
theorem B3228725 : Blo 2151435 3228725 := bbase (se 5 (by rfl) ⟨151346, by rfl⟩ : syracuseStep 3228725 = 302693) (by norm_num)
theorem B2152483 : Blo 2151435 2152483 := bstep (se 1 (by rfl) ⟨1614362, by rfl⟩ : syracuseStep 2152483 = 3228725) B3228725
theorem B5448485 : Blo 2151435 5448485 := bbase (se 4 (by rfl) ⟨510795, by rfl⟩ : syracuseStep 5448485 = 1021591) (by norm_num)
theorem B3632323 : Blo 2151435 3632323 := bstep (se 1 (by rfl) ⟨2724242, by rfl⟩ : syracuseStep 3632323 = 5448485) B5448485
theorem B4843097 : Blo 2151435 4843097 := bstep (se 2 (by rfl) ⟨1816161, by rfl⟩ : syracuseStep 4843097 = 3632323) B3632323
theorem B3228731 : Blo 2151435 3228731 := bstep (se 1 (by rfl) ⟨2421548, by rfl⟩ : syracuseStep 3228731 = 4843097) B4843097
theorem B2152487 : Blo 2151435 2152487 := bstep (se 1 (by rfl) ⟨1614365, by rfl⟩ : syracuseStep 2152487 = 3228731) B3228731
theorem B2421553 : Blo 2151435 2421553 := bbase (se 2 (by rfl) ⟨908082, by rfl⟩ : syracuseStep 2421553 = 1816165) (by norm_num)
theorem B3228737 : Blo 2151435 3228737 := bstep (se 2 (by rfl) ⟨1210776, by rfl⟩ : syracuseStep 3228737 = 2421553) B2421553
theorem B2152491 : Blo 2151435 2152491 := bstep (se 1 (by rfl) ⟨1614368, by rfl⟩ : syracuseStep 2152491 = 3228737) B3228737
theorem B3878869 : Blo 2151435 3878869 := bbase (se 7 (by rfl) ⟨45455, by rfl⟩ : syracuseStep 3878869 = 90911) (by norm_num)
theorem B5171825 : Blo 2151435 5171825 := bstep (se 2 (by rfl) ⟨1939434, by rfl⟩ : syracuseStep 5171825 = 3878869) B3878869
theorem B3447883 : Blo 2151435 3447883 := bstep (se 1 (by rfl) ⟨2585912, by rfl⟩ : syracuseStep 3447883 = 5171825) B5171825
theorem B4597177 : Blo 2151435 4597177 := bstep (se 2 (by rfl) ⟨1723941, by rfl⟩ : syracuseStep 4597177 = 3447883) B3447883
theorem B6129569 : Blo 2151435 6129569 := bstep (se 2 (by rfl) ⟨2298588, by rfl⟩ : syracuseStep 6129569 = 4597177) B4597177
theorem B4086379 : Blo 2151435 4086379 := bstep (se 1 (by rfl) ⟨3064784, by rfl⟩ : syracuseStep 4086379 = 6129569) B6129569
theorem B5448505 : Blo 2151435 5448505 := bstep (se 2 (by rfl) ⟨2043189, by rfl⟩ : syracuseStep 5448505 = 4086379) B4086379
theorem B7264673 : Blo 2151435 7264673 := bstep (se 2 (by rfl) ⟨2724252, by rfl⟩ : syracuseStep 7264673 = 5448505) B5448505
theorem B4843115 : Blo 2151435 4843115 := bstep (se 1 (by rfl) ⟨3632336, by rfl⟩ : syracuseStep 4843115 = 7264673) B7264673
theorem B3228743 : Blo 2151435 3228743 := bstep (se 1 (by rfl) ⟨2421557, by rfl⟩ : syracuseStep 3228743 = 4843115) B4843115
theorem B2152495 : Blo 2151435 2152495 := bstep (se 1 (by rfl) ⟨1614371, by rfl⟩ : syracuseStep 2152495 = 3228743) B3228743
theorem B3228749 : Blo 2151435 3228749 := bbase (se 3 (by rfl) ⟨605390, by rfl⟩ : syracuseStep 3228749 = 1210781) (by norm_num)
theorem B2152499 : Blo 2151435 2152499 := bstep (se 1 (by rfl) ⟨1614374, by rfl⟩ : syracuseStep 2152499 = 3228749) B3228749
theorem B4843133 : Blo 2151435 4843133 := bbase (se 3 (by rfl) ⟨908087, by rfl⟩ : syracuseStep 4843133 = 1816175) (by norm_num)
theorem B3228755 : Blo 2151435 3228755 := bstep (se 1 (by rfl) ⟨2421566, by rfl⟩ : syracuseStep 3228755 = 4843133) B4843133
theorem B2152503 : Blo 2151435 2152503 := bstep (se 1 (by rfl) ⟨1614377, by rfl⟩ : syracuseStep 2152503 = 3228755) B3228755
theorem B3632357 : Blo 2151435 3632357 := bbase (se 4 (by rfl) ⟨340533, by rfl⟩ : syracuseStep 3632357 = 681067) (by norm_num)
theorem B2421571 : Blo 2151435 2421571 := bstep (se 1 (by rfl) ⟨1816178, by rfl⟩ : syracuseStep 2421571 = 3632357) B3632357
theorem B3228761 : Blo 2151435 3228761 := bstep (se 2 (by rfl) ⟨1210785, by rfl⟩ : syracuseStep 3228761 = 2421571) B2421571
theorem B2152507 : Blo 2151435 2152507 := bstep (se 1 (by rfl) ⟨1614380, by rfl⟩ : syracuseStep 2152507 = 3228761) B3228761
theorem B11636693 : Blo 2151435 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B7757795 : Blo 2151435 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B5171863 : Blo 2151435 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B6895817 : Blo 2151435 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B4597211 : Blo 2151435 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B3064807 : Blo 2151435 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B16345637 : Blo 2151435 16345637 := bstep (se 4 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 16345637 = 3064807) B3064807
theorem B10897091 : Blo 2151435 10897091 := bstep (se 1 (by rfl) ⟨8172818, by rfl⟩ : syracuseStep 10897091 = 16345637) B16345637
theorem B7264727 : Blo 2151435 7264727 := bstep (se 1 (by rfl) ⟨5448545, by rfl⟩ : syracuseStep 7264727 = 10897091) B10897091
theorem B4843151 : Blo 2151435 4843151 := bstep (se 1 (by rfl) ⟨3632363, by rfl⟩ : syracuseStep 4843151 = 7264727) B7264727
theorem B3228767 : Blo 2151435 3228767 := bstep (se 1 (by rfl) ⟨2421575, by rfl⟩ : syracuseStep 3228767 = 4843151) B4843151
theorem B2152511 : Blo 2151435 2152511 := bstep (se 1 (by rfl) ⟨1614383, by rfl⟩ : syracuseStep 2152511 = 3228767) B3228767
theorem B3228773 : Blo 2151435 3228773 := bbase (se 4 (by rfl) ⟨302697, by rfl⟩ : syracuseStep 3228773 = 605395) (by norm_num)
theorem B2152515 : Blo 2151435 2152515 := bstep (se 1 (by rfl) ⟨1614386, by rfl⟩ : syracuseStep 2152515 = 3228773) B3228773
theorem B4597229 : Blo 2151435 4597229 := bbase (se 3 (by rfl) ⟨861980, by rfl⟩ : syracuseStep 4597229 = 1723961) (by norm_num)
theorem B3064819 : Blo 2151435 3064819 := bstep (se 1 (by rfl) ⟨2298614, by rfl⟩ : syracuseStep 3064819 = 4597229) B4597229
theorem B4086425 : Blo 2151435 4086425 := bstep (se 2 (by rfl) ⟨1532409, by rfl⟩ : syracuseStep 4086425 = 3064819) B3064819
theorem B2724283 : Blo 2151435 2724283 := bstep (se 1 (by rfl) ⟨2043212, by rfl⟩ : syracuseStep 2724283 = 4086425) B4086425
theorem B3632377 : Blo 2151435 3632377 := bstep (se 2 (by rfl) ⟨1362141, by rfl⟩ : syracuseStep 3632377 = 2724283) B2724283
theorem B4843169 : Blo 2151435 4843169 := bstep (se 2 (by rfl) ⟨1816188, by rfl⟩ : syracuseStep 4843169 = 3632377) B3632377
theorem B3228779 : Blo 2151435 3228779 := bstep (se 1 (by rfl) ⟨2421584, by rfl⟩ : syracuseStep 3228779 = 4843169) B4843169
theorem B2152519 : Blo 2151435 2152519 := bstep (se 1 (by rfl) ⟨1614389, by rfl⟩ : syracuseStep 2152519 = 3228779) B3228779
theorem B2421589 : Blo 2151435 2421589 := bbase (se 9 (by rfl) ⟨7094, by rfl⟩ : syracuseStep 2421589 = 14189) (by norm_num)
theorem B3228785 : Blo 2151435 3228785 := bstep (se 2 (by rfl) ⟨1210794, by rfl⟩ : syracuseStep 3228785 = 2421589) B2421589
theorem B2152523 : Blo 2151435 2152523 := bstep (se 1 (by rfl) ⟨1614392, by rfl⟩ : syracuseStep 2152523 = 3228785) B3228785
theorem B2724293 : Blo 2151435 2724293 := bbase (se 4 (by rfl) ⟨255402, by rfl⟩ : syracuseStep 2724293 = 510805) (by norm_num)
theorem B7264781 : Blo 2151435 7264781 := bstep (se 3 (by rfl) ⟨1362146, by rfl⟩ : syracuseStep 7264781 = 2724293) B2724293
theorem B4843187 : Blo 2151435 4843187 := bstep (se 1 (by rfl) ⟨3632390, by rfl⟩ : syracuseStep 4843187 = 7264781) B7264781
theorem B3228791 : Blo 2151435 3228791 := bstep (se 1 (by rfl) ⟨2421593, by rfl⟩ : syracuseStep 3228791 = 4843187) B4843187
theorem B2152527 : Blo 2151435 2152527 := bstep (se 1 (by rfl) ⟨1614395, by rfl⟩ : syracuseStep 2152527 = 3228791) B3228791
theorem B3228797 : Blo 2151435 3228797 := bbase (se 3 (by rfl) ⟨605399, by rfl⟩ : syracuseStep 3228797 = 1210799) (by norm_num)
theorem B2152531 : Blo 2151435 2152531 := bstep (se 1 (by rfl) ⟨1614398, by rfl⟩ : syracuseStep 2152531 = 3228797) B3228797
theorem B4843205 : Blo 2151435 4843205 := bbase (se 4 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 4843205 = 908101) (by norm_num)
theorem B3228803 : Blo 2151435 3228803 := bstep (se 1 (by rfl) ⟨2421602, by rfl⟩ : syracuseStep 3228803 = 4843205) B4843205
theorem B2152535 : Blo 2151435 2152535 := bstep (se 1 (by rfl) ⟨1614401, by rfl⟩ : syracuseStep 2152535 = 3228803) B3228803
theorem B5522957 : Blo 2151435 5522957 := bbase (se 3 (by rfl) ⟨1035554, by rfl⟩ : syracuseStep 5522957 = 2071109) (by norm_num)
theorem B3681971 : Blo 2151435 3681971 := bstep (se 1 (by rfl) ⟨2761478, by rfl⟩ : syracuseStep 3681971 = 5522957) B5522957
theorem B2454647 : Blo 2151435 2454647 := bstep (se 1 (by rfl) ⟨1840985, by rfl⟩ : syracuseStep 2454647 = 3681971) B3681971
theorem B26182901 : Blo 2151435 26182901 := bstep (se 5 (by rfl) ⟨1227323, by rfl⟩ : syracuseStep 26182901 = 2454647) B2454647
theorem B17455267 : Blo 2151435 17455267 := bstep (se 1 (by rfl) ⟨13091450, by rfl⟩ : syracuseStep 17455267 = 26182901) B26182901
theorem B23273689 : Blo 2151435 23273689 := bstep (se 2 (by rfl) ⟨8727633, by rfl⟩ : syracuseStep 23273689 = 17455267) B17455267
theorem B31031585 : Blo 2151435 31031585 := bstep (se 2 (by rfl) ⟨11636844, by rfl⟩ : syracuseStep 31031585 = 23273689) B23273689
theorem B20687723 : Blo 2151435 20687723 := bstep (se 1 (by rfl) ⟨15515792, by rfl⟩ : syracuseStep 20687723 = 31031585) B31031585
theorem B13791815 : Blo 2151435 13791815 := bstep (se 1 (by rfl) ⟨10343861, by rfl⟩ : syracuseStep 13791815 = 20687723) B20687723
theorem B9194543 : Blo 2151435 9194543 := bstep (se 1 (by rfl) ⟨6895907, by rfl⟩ : syracuseStep 9194543 = 13791815) B13791815
theorem B6129695 : Blo 2151435 6129695 := bstep (se 1 (by rfl) ⟨4597271, by rfl⟩ : syracuseStep 6129695 = 9194543) B9194543
theorem B4086463 : Blo 2151435 4086463 := bstep (se 1 (by rfl) ⟨3064847, by rfl⟩ : syracuseStep 4086463 = 6129695) B6129695
theorem B5448617 : Blo 2151435 5448617 := bstep (se 2 (by rfl) ⟨2043231, by rfl⟩ : syracuseStep 5448617 = 4086463) B4086463
theorem B3632411 : Blo 2151435 3632411 := bstep (se 1 (by rfl) ⟨2724308, by rfl⟩ : syracuseStep 3632411 = 5448617) B5448617
theorem B2421607 : Blo 2151435 2421607 := bstep (se 1 (by rfl) ⟨1816205, by rfl⟩ : syracuseStep 2421607 = 3632411) B3632411
theorem B3228809 : Blo 2151435 3228809 := bstep (se 2 (by rfl) ⟨1210803, by rfl⟩ : syracuseStep 3228809 = 2421607) B2421607
theorem B2152539 : Blo 2151435 2152539 := bstep (se 1 (by rfl) ⟨1614404, by rfl⟩ : syracuseStep 2152539 = 3228809) B3228809
theorem B10897253 : Blo 2151435 10897253 := bbase (se 4 (by rfl) ⟨1021617, by rfl⟩ : syracuseStep 10897253 = 2043235) (by norm_num)
theorem B7264835 : Blo 2151435 7264835 := bstep (se 1 (by rfl) ⟨5448626, by rfl⟩ : syracuseStep 7264835 = 10897253) B10897253
theorem B4843223 : Blo 2151435 4843223 := bstep (se 1 (by rfl) ⟨3632417, by rfl⟩ : syracuseStep 4843223 = 7264835) B7264835
theorem B3228815 : Blo 2151435 3228815 := bstep (se 1 (by rfl) ⟨2421611, by rfl⟩ : syracuseStep 3228815 = 4843223) B4843223
theorem B2152543 : Blo 2151435 2152543 := bstep (se 1 (by rfl) ⟨1614407, by rfl⟩ : syracuseStep 2152543 = 3228815) B3228815
theorem B3228821 : Blo 2151435 3228821 := bbase (se 6 (by rfl) ⟨75675, by rfl⟩ : syracuseStep 3228821 = 151351) (by norm_num)
theorem B2152547 : Blo 2151435 2152547 := bstep (se 1 (by rfl) ⟨1614410, by rfl⟩ : syracuseStep 2152547 = 3228821) B3228821
theorem B2454661 : Blo 2151435 2454661 := bbase (se 4 (by rfl) ⟨230124, by rfl⟩ : syracuseStep 2454661 = 460249) (by norm_num)
theorem B3272881 : Blo 2151435 3272881 := bstep (se 2 (by rfl) ⟨1227330, by rfl⟩ : syracuseStep 3272881 = 2454661) B2454661
theorem B4363841 : Blo 2151435 4363841 := bstep (se 2 (by rfl) ⟨1636440, by rfl⟩ : syracuseStep 4363841 = 3272881) B3272881
theorem B11636909 : Blo 2151435 11636909 := bstep (se 3 (by rfl) ⟨2181920, by rfl⟩ : syracuseStep 11636909 = 4363841) B4363841
theorem B7757939 : Blo 2151435 7757939 := bstep (se 1 (by rfl) ⟨5818454, by rfl⟩ : syracuseStep 7757939 = 11636909) B11636909
theorem B5171959 : Blo 2151435 5171959 := bstep (se 1 (by rfl) ⟨3878969, by rfl⟩ : syracuseStep 5171959 = 7757939) B7757939
theorem B6895945 : Blo 2151435 6895945 := bstep (se 2 (by rfl) ⟨2585979, by rfl⟩ : syracuseStep 6895945 = 5171959) B5171959
theorem B9194593 : Blo 2151435 9194593 := bstep (se 2 (by rfl) ⟨3447972, by rfl⟩ : syracuseStep 9194593 = 6895945) B6895945
theorem B12259457 : Blo 2151435 12259457 := bstep (se 2 (by rfl) ⟨4597296, by rfl⟩ : syracuseStep 12259457 = 9194593) B9194593
theorem B8172971 : Blo 2151435 8172971 := bstep (se 1 (by rfl) ⟨6129728, by rfl⟩ : syracuseStep 8172971 = 12259457) B12259457
theorem B5448647 : Blo 2151435 5448647 := bstep (se 1 (by rfl) ⟨4086485, by rfl⟩ : syracuseStep 5448647 = 8172971) B8172971
theorem B3632431 : Blo 2151435 3632431 := bstep (se 1 (by rfl) ⟨2724323, by rfl⟩ : syracuseStep 3632431 = 5448647) B5448647
theorem B4843241 : Blo 2151435 4843241 := bstep (se 2 (by rfl) ⟨1816215, by rfl⟩ : syracuseStep 4843241 = 3632431) B3632431
theorem B3228827 : Blo 2151435 3228827 := bstep (se 1 (by rfl) ⟨2421620, by rfl⟩ : syracuseStep 3228827 = 4843241) B4843241
theorem B2152551 : Blo 2151435 2152551 := bstep (se 1 (by rfl) ⟨1614413, by rfl⟩ : syracuseStep 2152551 = 3228827) B3228827
theorem B2421625 : Blo 2151435 2421625 := bbase (se 2 (by rfl) ⟨908109, by rfl⟩ : syracuseStep 2421625 = 1816219) (by norm_num)
theorem B3228833 : Blo 2151435 3228833 := bstep (se 2 (by rfl) ⟨1210812, by rfl⟩ : syracuseStep 3228833 = 2421625) B2421625
theorem B2152555 : Blo 2151435 2152555 := bstep (se 1 (by rfl) ⟨1614416, by rfl⟩ : syracuseStep 2152555 = 3228833) B3228833
theorem B2585989 : Blo 2151435 2585989 := bbase (se 4 (by rfl) ⟨242436, by rfl⟩ : syracuseStep 2585989 = 484873) (by norm_num)
theorem B13791941 : Blo 2151435 13791941 := bstep (se 4 (by rfl) ⟨1292994, by rfl⟩ : syracuseStep 13791941 = 2585989) B2585989
theorem B9194627 : Blo 2151435 9194627 := bstep (se 1 (by rfl) ⟨6895970, by rfl⟩ : syracuseStep 9194627 = 13791941) B13791941
theorem B6129751 : Blo 2151435 6129751 := bstep (se 1 (by rfl) ⟨4597313, by rfl⟩ : syracuseStep 6129751 = 9194627) B9194627
theorem B8173001 : Blo 2151435 8173001 := bstep (se 2 (by rfl) ⟨3064875, by rfl⟩ : syracuseStep 8173001 = 6129751) B6129751
theorem B5448667 : Blo 2151435 5448667 := bstep (se 1 (by rfl) ⟨4086500, by rfl⟩ : syracuseStep 5448667 = 8173001) B8173001
theorem B7264889 : Blo 2151435 7264889 := bstep (se 2 (by rfl) ⟨2724333, by rfl⟩ : syracuseStep 7264889 = 5448667) B5448667
theorem B4843259 : Blo 2151435 4843259 := bstep (se 1 (by rfl) ⟨3632444, by rfl⟩ : syracuseStep 4843259 = 7264889) B7264889
theorem B3228839 : Blo 2151435 3228839 := bstep (se 1 (by rfl) ⟨2421629, by rfl⟩ : syracuseStep 3228839 = 4843259) B4843259
theorem B2152559 : Blo 2151435 2152559 := bstep (se 1 (by rfl) ⟨1614419, by rfl⟩ : syracuseStep 2152559 = 3228839) B3228839
theorem B3228845 : Blo 2151435 3228845 := bbase (se 3 (by rfl) ⟨605408, by rfl⟩ : syracuseStep 3228845 = 1210817) (by norm_num)
theorem B2152563 : Blo 2151435 2152563 := bstep (se 1 (by rfl) ⟨1614422, by rfl⟩ : syracuseStep 2152563 = 3228845) B3228845
theorem B4843277 : Blo 2151435 4843277 := bbase (se 3 (by rfl) ⟨908114, by rfl⟩ : syracuseStep 4843277 = 1816229) (by norm_num)
theorem B3228851 : Blo 2151435 3228851 := bstep (se 1 (by rfl) ⟨2421638, by rfl⟩ : syracuseStep 3228851 = 4843277) B4843277
theorem B2152567 : Blo 2151435 2152567 := bstep (se 1 (by rfl) ⟨1614425, by rfl⟩ : syracuseStep 2152567 = 3228851) B3228851
theorem B2724349 : Blo 2151435 2724349 := bbase (se 3 (by rfl) ⟨510815, by rfl⟩ : syracuseStep 2724349 = 1021631) (by norm_num)
theorem B3632465 : Blo 2151435 3632465 := bstep (se 2 (by rfl) ⟨1362174, by rfl⟩ : syracuseStep 3632465 = 2724349) B2724349
theorem B2421643 : Blo 2151435 2421643 := bstep (se 1 (by rfl) ⟨1816232, by rfl⟩ : syracuseStep 2421643 = 3632465) B3632465
theorem B3228857 : Blo 2151435 3228857 := bstep (se 2 (by rfl) ⟨1210821, by rfl⟩ : syracuseStep 3228857 = 2421643) B2421643
theorem B2152571 : Blo 2151435 2152571 := bstep (se 1 (by rfl) ⟨1614428, by rfl⟩ : syracuseStep 2152571 = 3228857) B3228857
theorem B6896021 : Blo 2151435 6896021 := bbase (se 6 (by rfl) ⟨161625, by rfl⟩ : syracuseStep 6896021 = 323251) (by norm_num)
theorem B18389389 : Blo 2151435 18389389 := bstep (se 3 (by rfl) ⟨3448010, by rfl⟩ : syracuseStep 18389389 = 6896021) B6896021
theorem B24519185 : Blo 2151435 24519185 := bstep (se 2 (by rfl) ⟨9194694, by rfl⟩ : syracuseStep 24519185 = 18389389) B18389389
theorem B16346123 : Blo 2151435 16346123 := bstep (se 1 (by rfl) ⟨12259592, by rfl⟩ : syracuseStep 16346123 = 24519185) B24519185
theorem B10897415 : Blo 2151435 10897415 := bstep (se 1 (by rfl) ⟨8173061, by rfl⟩ : syracuseStep 10897415 = 16346123) B16346123
theorem B7264943 : Blo 2151435 7264943 := bstep (se 1 (by rfl) ⟨5448707, by rfl⟩ : syracuseStep 7264943 = 10897415) B10897415
theorem B4843295 : Blo 2151435 4843295 := bstep (se 1 (by rfl) ⟨3632471, by rfl⟩ : syracuseStep 4843295 = 7264943) B7264943
theorem B3228863 : Blo 2151435 3228863 := bstep (se 1 (by rfl) ⟨2421647, by rfl⟩ : syracuseStep 3228863 = 4843295) B4843295
theorem B2152575 : Blo 2151435 2152575 := bstep (se 1 (by rfl) ⟨1614431, by rfl⟩ : syracuseStep 2152575 = 3228863) B3228863
theorem B3228869 : Blo 2151435 3228869 := bbase (se 4 (by rfl) ⟨302706, by rfl⟩ : syracuseStep 3228869 = 605413) (by norm_num)
theorem B2152579 : Blo 2151435 2152579 := bstep (se 1 (by rfl) ⟨1614434, by rfl⟩ : syracuseStep 2152579 = 3228869) B3228869
theorem B3632485 : Blo 2151435 3632485 := bbase (se 4 (by rfl) ⟨340545, by rfl⟩ : syracuseStep 3632485 = 681091) (by norm_num)
theorem B4843313 : Blo 2151435 4843313 := bstep (se 2 (by rfl) ⟨1816242, by rfl⟩ : syracuseStep 4843313 = 3632485) B3632485
theorem B3228875 : Blo 2151435 3228875 := bstep (se 1 (by rfl) ⟨2421656, by rfl⟩ : syracuseStep 3228875 = 4843313) B4843313
theorem B2152583 : Blo 2151435 2152583 := bstep (se 1 (by rfl) ⟨1614437, by rfl⟩ : syracuseStep 2152583 = 3228875) B3228875
theorem B2421661 : Blo 2151435 2421661 := bbase (se 3 (by rfl) ⟨454061, by rfl⟩ : syracuseStep 2421661 = 908123) (by norm_num)
theorem B3228881 : Blo 2151435 3228881 := bstep (se 2 (by rfl) ⟨1210830, by rfl⟩ : syracuseStep 3228881 = 2421661) B2421661
theorem B2152587 : Blo 2151435 2152587 := bstep (se 1 (by rfl) ⟨1614440, by rfl⟩ : syracuseStep 2152587 = 3228881) B3228881
theorem B7264997 : Blo 2151435 7264997 := bbase (se 4 (by rfl) ⟨681093, by rfl⟩ : syracuseStep 7264997 = 1362187) (by norm_num)
theorem B4843331 : Blo 2151435 4843331 := bstep (se 1 (by rfl) ⟨3632498, by rfl⟩ : syracuseStep 4843331 = 7264997) B7264997
theorem B3228887 : Blo 2151435 3228887 := bstep (se 1 (by rfl) ⟨2421665, by rfl⟩ : syracuseStep 3228887 = 4843331) B4843331
theorem B2152591 : Blo 2151435 2152591 := bstep (se 1 (by rfl) ⟨1614443, by rfl⟩ : syracuseStep 2152591 = 3228887) B3228887
theorem B3228893 : Blo 2151435 3228893 := bbase (se 3 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 3228893 = 1210835) (by norm_num)
theorem B2152595 : Blo 2151435 2152595 := bstep (se 1 (by rfl) ⟨1614446, by rfl⟩ : syracuseStep 2152595 = 3228893) B3228893
theorem B4843349 : Blo 2151435 4843349 := bbase (se 9 (by rfl) ⟨14189, by rfl⟩ : syracuseStep 4843349 = 28379) (by norm_num)
theorem B3228899 : Blo 2151435 3228899 := bstep (se 1 (by rfl) ⟨2421674, by rfl⟩ : syracuseStep 3228899 = 4843349) B4843349
theorem B2152599 : Blo 2151435 2152599 := bstep (se 1 (by rfl) ⟨1614449, by rfl⟩ : syracuseStep 2152599 = 3228899) B3228899
theorem B6129877 : Blo 2151435 6129877 := bbase (se 7 (by rfl) ⟨71834, by rfl⟩ : syracuseStep 6129877 = 143669) (by norm_num)
theorem B8173169 : Blo 2151435 8173169 := bstep (se 2 (by rfl) ⟨3064938, by rfl⟩ : syracuseStep 8173169 = 6129877) B6129877
theorem B5448779 : Blo 2151435 5448779 := bstep (se 1 (by rfl) ⟨4086584, by rfl⟩ : syracuseStep 5448779 = 8173169) B8173169
theorem B3632519 : Blo 2151435 3632519 := bstep (se 1 (by rfl) ⟨2724389, by rfl⟩ : syracuseStep 3632519 = 5448779) B5448779
theorem B2421679 : Blo 2151435 2421679 := bstep (se 1 (by rfl) ⟨1816259, by rfl⟩ : syracuseStep 2421679 = 3632519) B3632519
theorem B3228905 : Blo 2151435 3228905 := bstep (se 2 (by rfl) ⟨1210839, by rfl⟩ : syracuseStep 3228905 = 2421679) B2421679
theorem B2152603 : Blo 2151435 2152603 := bstep (se 1 (by rfl) ⟨1614452, by rfl⟩ : syracuseStep 2152603 = 3228905) B3228905
theorem B33138773 : Blo 2151435 33138773 := bbase (se 8 (by rfl) ⟨194172, by rfl⟩ : syracuseStep 33138773 = 388345) (by norm_num)
theorem B22092515 : Blo 2151435 22092515 := bstep (se 1 (by rfl) ⟨16569386, by rfl⟩ : syracuseStep 22092515 = 33138773) B33138773
theorem B14728343 : Blo 2151435 14728343 := bstep (se 1 (by rfl) ⟨11046257, by rfl⟩ : syracuseStep 14728343 = 22092515) B22092515
theorem B157102325 : Blo 2151435 157102325 := bstep (se 5 (by rfl) ⟨7364171, by rfl⟩ : syracuseStep 157102325 = 14728343) B14728343
theorem B104734883 : Blo 2151435 104734883 := bstep (se 1 (by rfl) ⟨78551162, by rfl⟩ : syracuseStep 104734883 = 157102325) B157102325
theorem B69823255 : Blo 2151435 69823255 := bstep (se 1 (by rfl) ⟨52367441, by rfl⟩ : syracuseStep 69823255 = 104734883) B104734883
theorem B93097673 : Blo 2151435 93097673 := bstep (se 2 (by rfl) ⟨34911627, by rfl⟩ : syracuseStep 93097673 = 69823255) B69823255
theorem B62065115 : Blo 2151435 62065115 := bstep (se 1 (by rfl) ⟨46548836, by rfl⟩ : syracuseStep 62065115 = 93097673) B93097673
theorem B41376743 : Blo 2151435 41376743 := bstep (se 1 (by rfl) ⟨31032557, by rfl⟩ : syracuseStep 41376743 = 62065115) B62065115
theorem B27584495 : Blo 2151435 27584495 := bstep (se 1 (by rfl) ⟨20688371, by rfl⟩ : syracuseStep 27584495 = 41376743) B41376743
theorem B18389663 : Blo 2151435 18389663 := bstep (se 1 (by rfl) ⟨13792247, by rfl⟩ : syracuseStep 18389663 = 27584495) B27584495
theorem B12259775 : Blo 2151435 12259775 := bstep (se 1 (by rfl) ⟨9194831, by rfl⟩ : syracuseStep 12259775 = 18389663) B18389663
theorem B8173183 : Blo 2151435 8173183 := bstep (se 1 (by rfl) ⟨6129887, by rfl⟩ : syracuseStep 8173183 = 12259775) B12259775
theorem B10897577 : Blo 2151435 10897577 := bstep (se 2 (by rfl) ⟨4086591, by rfl⟩ : syracuseStep 10897577 = 8173183) B8173183
theorem B7265051 : Blo 2151435 7265051 := bstep (se 1 (by rfl) ⟨5448788, by rfl⟩ : syracuseStep 7265051 = 10897577) B10897577
theorem B4843367 : Blo 2151435 4843367 := bstep (se 1 (by rfl) ⟨3632525, by rfl⟩ : syracuseStep 4843367 = 7265051) B7265051
theorem B3228911 : Blo 2151435 3228911 := bstep (se 1 (by rfl) ⟨2421683, by rfl⟩ : syracuseStep 3228911 = 4843367) B4843367
theorem B2152607 : Blo 2151435 2152607 := bstep (se 1 (by rfl) ⟨1614455, by rfl⟩ : syracuseStep 2152607 = 3228911) B3228911
theorem B3228917 : Blo 2151435 3228917 := bbase (se 5 (by rfl) ⟨151355, by rfl⟩ : syracuseStep 3228917 = 302711) (by norm_num)
theorem B2152611 : Blo 2151435 2152611 := bstep (se 1 (by rfl) ⟨1614458, by rfl⟩ : syracuseStep 2152611 = 3228917) B3228917
theorem B3879085 : Blo 2151435 3879085 := bbase (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) (by norm_num)
theorem B5172113 : Blo 2151435 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B13792301 : Blo 2151435 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B9194867 : Blo 2151435 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B6129911 : Blo 2151435 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B4086607 : Blo 2151435 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B5448809 : Blo 2151435 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B3632539 : Blo 2151435 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B4843385 : Blo 2151435 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B3228923 : Blo 2151435 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B2152615 : Blo 2151435 2152615 := bstep (se 1 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 2152615 = 3228923) B3228923
theorem B2421697 : Blo 2151435 2421697 := bbase (se 2 (by rfl) ⟨908136, by rfl⟩ : syracuseStep 2421697 = 1816273) (by norm_num)
theorem B3228929 : Blo 2151435 3228929 := bstep (se 2 (by rfl) ⟨1210848, by rfl⟩ : syracuseStep 3228929 = 2421697) B2421697
theorem B2152619 : Blo 2151435 2152619 := bstep (se 1 (by rfl) ⟨1614464, by rfl⟩ : syracuseStep 2152619 = 3228929) B3228929
theorem B5448829 : Blo 2151435 5448829 := bbase (se 3 (by rfl) ⟨1021655, by rfl⟩ : syracuseStep 5448829 = 2043311) (by norm_num)
theorem B7265105 : Blo 2151435 7265105 := bstep (se 2 (by rfl) ⟨2724414, by rfl⟩ : syracuseStep 7265105 = 5448829) B5448829
theorem B4843403 : Blo 2151435 4843403 := bstep (se 1 (by rfl) ⟨3632552, by rfl⟩ : syracuseStep 4843403 = 7265105) B7265105
theorem B3228935 : Blo 2151435 3228935 := bstep (se 1 (by rfl) ⟨2421701, by rfl⟩ : syracuseStep 3228935 = 4843403) B4843403
theorem B2152623 : Blo 2151435 2152623 := bstep (se 1 (by rfl) ⟨1614467, by rfl⟩ : syracuseStep 2152623 = 3228935) B3228935
theorem B3228941 : Blo 2151435 3228941 := bbase (se 3 (by rfl) ⟨605426, by rfl⟩ : syracuseStep 3228941 = 1210853) (by norm_num)
theorem B2152627 : Blo 2151435 2152627 := bstep (se 1 (by rfl) ⟨1614470, by rfl⟩ : syracuseStep 2152627 = 3228941) B3228941
theorem B4843421 : Blo 2151435 4843421 := bbase (se 3 (by rfl) ⟨908141, by rfl⟩ : syracuseStep 4843421 = 1816283) (by norm_num)
theorem B3228947 : Blo 2151435 3228947 := bstep (se 1 (by rfl) ⟨2421710, by rfl⟩ : syracuseStep 3228947 = 4843421) B4843421
theorem B2152631 : Blo 2151435 2152631 := bstep (se 1 (by rfl) ⟨1614473, by rfl⟩ : syracuseStep 2152631 = 3228947) B3228947
theorem B3632573 : Blo 2151435 3632573 := bbase (se 3 (by rfl) ⟨681107, by rfl⟩ : syracuseStep 3632573 = 1362215) (by norm_num)
theorem B2421715 : Blo 2151435 2421715 := bstep (se 1 (by rfl) ⟨1816286, by rfl⟩ : syracuseStep 2421715 = 3632573) B3632573
theorem B3228953 : Blo 2151435 3228953 := bstep (se 2 (by rfl) ⟨1210857, by rfl⟩ : syracuseStep 3228953 = 2421715) B2421715
theorem B2152635 : Blo 2151435 2152635 := bstep (se 1 (by rfl) ⟨1614476, by rfl⟩ : syracuseStep 2152635 = 3228953) B3228953
theorem B12259957 : Blo 2151435 12259957 := bbase (se 5 (by rfl) ⟨574685, by rfl⟩ : syracuseStep 12259957 = 1149371) (by norm_num)
theorem B16346609 : Blo 2151435 16346609 := bstep (se 2 (by rfl) ⟨6129978, by rfl⟩ : syracuseStep 16346609 = 12259957) B12259957
theorem B10897739 : Blo 2151435 10897739 := bstep (se 1 (by rfl) ⟨8173304, by rfl⟩ : syracuseStep 10897739 = 16346609) B16346609
theorem B7265159 : Blo 2151435 7265159 := bstep (se 1 (by rfl) ⟨5448869, by rfl⟩ : syracuseStep 7265159 = 10897739) B10897739
theorem B4843439 : Blo 2151435 4843439 := bstep (se 1 (by rfl) ⟨3632579, by rfl⟩ : syracuseStep 4843439 = 7265159) B7265159
theorem B3228959 : Blo 2151435 3228959 := bstep (se 1 (by rfl) ⟨2421719, by rfl⟩ : syracuseStep 3228959 = 4843439) B4843439
theorem B2152639 : Blo 2151435 2152639 := bstep (se 1 (by rfl) ⟨1614479, by rfl⟩ : syracuseStep 2152639 = 3228959) B3228959
theorem B3228965 : Blo 2151435 3228965 := bbase (se 4 (by rfl) ⟨302715, by rfl⟩ : syracuseStep 3228965 = 605431) (by norm_num)
theorem B2152643 : Blo 2151435 2152643 := bstep (se 1 (by rfl) ⟨1614482, by rfl⟩ : syracuseStep 2152643 = 3228965) B3228965
theorem B2724445 : Blo 2151435 2724445 := bbase (se 3 (by rfl) ⟨510833, by rfl⟩ : syracuseStep 2724445 = 1021667) (by norm_num)
theorem B3632593 : Blo 2151435 3632593 := bstep (se 2 (by rfl) ⟨1362222, by rfl⟩ : syracuseStep 3632593 = 2724445) B2724445
theorem B4843457 : Blo 2151435 4843457 := bstep (se 2 (by rfl) ⟨1816296, by rfl⟩ : syracuseStep 4843457 = 3632593) B3632593
theorem B3228971 : Blo 2151435 3228971 := bstep (se 1 (by rfl) ⟨2421728, by rfl⟩ : syracuseStep 3228971 = 4843457) B4843457
theorem B2152647 : Blo 2151435 2152647 := bstep (se 1 (by rfl) ⟨1614485, by rfl⟩ : syracuseStep 2152647 = 3228971) B3228971
theorem B2421733 : Blo 2151435 2421733 := bbase (se 4 (by rfl) ⟨227037, by rfl⟩ : syracuseStep 2421733 = 454075) (by norm_num)
theorem B3228977 : Blo 2151435 3228977 := bstep (se 2 (by rfl) ⟨1210866, by rfl⟩ : syracuseStep 3228977 = 2421733) B2421733
theorem B2152651 : Blo 2151435 2152651 := bstep (se 1 (by rfl) ⟨1614488, by rfl⟩ : syracuseStep 2152651 = 3228977) B3228977
theorem B15516629 : Blo 2151435 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B10344419 : Blo 2151435 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B6896279 : Blo 2151435 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B4597519 : Blo 2151435 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B6130025 : Blo 2151435 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B4086683 : Blo 2151435 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B2724455 : Blo 2151435 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B7265213 : Blo 2151435 7265213 := bstep (se 3 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 7265213 = 2724455) B2724455
theorem B4843475 : Blo 2151435 4843475 := bstep (se 1 (by rfl) ⟨3632606, by rfl⟩ : syracuseStep 4843475 = 7265213) B7265213
theorem B3228983 : Blo 2151435 3228983 := bstep (se 1 (by rfl) ⟨2421737, by rfl⟩ : syracuseStep 3228983 = 4843475) B4843475
theorem B2152655 : Blo 2151435 2152655 := bstep (se 1 (by rfl) ⟨1614491, by rfl⟩ : syracuseStep 2152655 = 3228983) B3228983
theorem B3228989 : Blo 2151435 3228989 := bbase (se 3 (by rfl) ⟨605435, by rfl⟩ : syracuseStep 3228989 = 1210871) (by norm_num)
theorem B2152659 : Blo 2151435 2152659 := bstep (se 1 (by rfl) ⟨1614494, by rfl⟩ : syracuseStep 2152659 = 3228989) B3228989
theorem B4843493 : Blo 2151435 4843493 := bbase (se 4 (by rfl) ⟨454077, by rfl⟩ : syracuseStep 4843493 = 908155) (by norm_num)
theorem B3228995 : Blo 2151435 3228995 := bstep (se 1 (by rfl) ⟨2421746, by rfl⟩ : syracuseStep 3228995 = 4843493) B4843493
theorem B2152663 : Blo 2151435 2152663 := bstep (se 1 (by rfl) ⟨1614497, by rfl⟩ : syracuseStep 2152663 = 3228995) B3228995
theorem B5448941 : Blo 2151435 5448941 := bbase (se 3 (by rfl) ⟨1021676, by rfl⟩ : syracuseStep 5448941 = 2043353) (by norm_num)
theorem B3632627 : Blo 2151435 3632627 := bstep (se 1 (by rfl) ⟨2724470, by rfl⟩ : syracuseStep 3632627 = 5448941) B5448941
theorem B2421751 : Blo 2151435 2421751 := bstep (se 1 (by rfl) ⟨1816313, by rfl⟩ : syracuseStep 2421751 = 3632627) B3632627
theorem B3229001 : Blo 2151435 3229001 := bstep (se 2 (by rfl) ⟨1210875, by rfl⟩ : syracuseStep 3229001 = 2421751) B2421751
theorem B2152667 : Blo 2151435 2152667 := bstep (se 1 (by rfl) ⟨1614500, by rfl⟩ : syracuseStep 2152667 = 3229001) B3229001
theorem B3448165 : Blo 2151435 3448165 := bbase (se 4 (by rfl) ⟨323265, by rfl⟩ : syracuseStep 3448165 = 646531) (by norm_num)
theorem B4597553 : Blo 2151435 4597553 := bstep (se 2 (by rfl) ⟨1724082, by rfl⟩ : syracuseStep 4597553 = 3448165) B3448165
theorem B3065035 : Blo 2151435 3065035 := bstep (se 1 (by rfl) ⟨2298776, by rfl⟩ : syracuseStep 3065035 = 4597553) B4597553
theorem B4086713 : Blo 2151435 4086713 := bstep (se 2 (by rfl) ⟨1532517, by rfl⟩ : syracuseStep 4086713 = 3065035) B3065035
theorem B10897901 : Blo 2151435 10897901 := bstep (se 3 (by rfl) ⟨2043356, by rfl⟩ : syracuseStep 10897901 = 4086713) B4086713
theorem B7265267 : Blo 2151435 7265267 := bstep (se 1 (by rfl) ⟨5448950, by rfl⟩ : syracuseStep 7265267 = 10897901) B10897901
theorem B4843511 : Blo 2151435 4843511 := bstep (se 1 (by rfl) ⟨3632633, by rfl⟩ : syracuseStep 4843511 = 7265267) B7265267
theorem B3229007 : Blo 2151435 3229007 := bstep (se 1 (by rfl) ⟨2421755, by rfl⟩ : syracuseStep 3229007 = 4843511) B4843511
theorem B2152671 : Blo 2151435 2152671 := bstep (se 1 (by rfl) ⟨1614503, by rfl⟩ : syracuseStep 2152671 = 3229007) B3229007
theorem B3229013 : Blo 2151435 3229013 := bbase (se 12 (by rfl) ⟨1182, by rfl⟩ : syracuseStep 3229013 = 2365) (by norm_num)
theorem B2152675 : Blo 2151435 2152675 := bstep (se 1 (by rfl) ⟨1614506, by rfl⟩ : syracuseStep 2152675 = 3229013) B3229013
theorem B2298785 : Blo 2151435 2298785 := bbase (se 2 (by rfl) ⟨862044, by rfl⟩ : syracuseStep 2298785 = 1724089) (by norm_num)
theorem B6130093 : Blo 2151435 6130093 := bstep (se 3 (by rfl) ⟨1149392, by rfl⟩ : syracuseStep 6130093 = 2298785) B2298785
theorem B8173457 : Blo 2151435 8173457 := bstep (se 2 (by rfl) ⟨3065046, by rfl⟩ : syracuseStep 8173457 = 6130093) B6130093
theorem B5448971 : Blo 2151435 5448971 := bstep (se 1 (by rfl) ⟨4086728, by rfl⟩ : syracuseStep 5448971 = 8173457) B8173457
theorem B3632647 : Blo 2151435 3632647 := bstep (se 1 (by rfl) ⟨2724485, by rfl⟩ : syracuseStep 3632647 = 5448971) B5448971
theorem B4843529 : Blo 2151435 4843529 := bstep (se 2 (by rfl) ⟨1816323, by rfl⟩ : syracuseStep 4843529 = 3632647) B3632647
theorem B3229019 : Blo 2151435 3229019 := bstep (se 1 (by rfl) ⟨2421764, by rfl⟩ : syracuseStep 3229019 = 4843529) B4843529
theorem B2152679 : Blo 2151435 2152679 := bstep (se 1 (by rfl) ⟨1614509, by rfl⟩ : syracuseStep 2152679 = 3229019) B3229019
theorem B2421769 : Blo 2151435 2421769 := bbase (se 2 (by rfl) ⟨908163, by rfl⟩ : syracuseStep 2421769 = 1816327) (by norm_num)
theorem B3229025 : Blo 2151435 3229025 := bstep (se 2 (by rfl) ⟨1210884, by rfl⟩ : syracuseStep 3229025 = 2421769) B2421769
theorem B2152683 : Blo 2151435 2152683 := bstep (se 1 (by rfl) ⟨1614512, by rfl⟩ : syracuseStep 2152683 = 3229025) B3229025
theorem B20689141 : Blo 2151435 20689141 := bbase (se 5 (by rfl) ⟨969803, by rfl⟩ : syracuseStep 20689141 = 1939607) (by norm_num)
theorem B27585521 : Blo 2151435 27585521 := bstep (se 2 (by rfl) ⟨10344570, by rfl⟩ : syracuseStep 27585521 = 20689141) B20689141
theorem B18390347 : Blo 2151435 18390347 := bstep (se 1 (by rfl) ⟨13792760, by rfl⟩ : syracuseStep 18390347 = 27585521) B27585521
theorem B12260231 : Blo 2151435 12260231 := bstep (se 1 (by rfl) ⟨9195173, by rfl⟩ : syracuseStep 12260231 = 18390347) B18390347
theorem B8173487 : Blo 2151435 8173487 := bstep (se 1 (by rfl) ⟨6130115, by rfl⟩ : syracuseStep 8173487 = 12260231) B12260231
theorem B5448991 : Blo 2151435 5448991 := bstep (se 1 (by rfl) ⟨4086743, by rfl⟩ : syracuseStep 5448991 = 8173487) B8173487
theorem B7265321 : Blo 2151435 7265321 := bstep (se 2 (by rfl) ⟨2724495, by rfl⟩ : syracuseStep 7265321 = 5448991) B5448991
theorem B4843547 : Blo 2151435 4843547 := bstep (se 1 (by rfl) ⟨3632660, by rfl⟩ : syracuseStep 4843547 = 7265321) B7265321
theorem B3229031 : Blo 2151435 3229031 := bstep (se 1 (by rfl) ⟨2421773, by rfl⟩ : syracuseStep 3229031 = 4843547) B4843547
theorem B2152687 : Blo 2151435 2152687 := bstep (se 1 (by rfl) ⟨1614515, by rfl⟩ : syracuseStep 2152687 = 3229031) B3229031
theorem B3229037 : Blo 2151435 3229037 := bbase (se 3 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 3229037 = 1210889) (by norm_num)
theorem B2152691 : Blo 2151435 2152691 := bstep (se 1 (by rfl) ⟨1614518, by rfl⟩ : syracuseStep 2152691 = 3229037) B3229037
theorem B4843565 : Blo 2151435 4843565 := bbase (se 3 (by rfl) ⟨908168, by rfl⟩ : syracuseStep 4843565 = 1816337) (by norm_num)
theorem B3229043 : Blo 2151435 3229043 := bstep (se 1 (by rfl) ⟨2421782, by rfl⟩ : syracuseStep 3229043 = 4843565) B4843565
theorem B2152695 : Blo 2151435 2152695 := bstep (se 1 (by rfl) ⟨1614521, by rfl⟩ : syracuseStep 2152695 = 3229043) B3229043
theorem B4976645 : Blo 2151435 4976645 := bbase (se 4 (by rfl) ⟨466560, by rfl⟩ : syracuseStep 4976645 = 933121) (by norm_num)
theorem B13271053 : Blo 2151435 13271053 := bstep (se 3 (by rfl) ⟨2488322, by rfl⟩ : syracuseStep 13271053 = 4976645) B4976645
theorem B17694737 : Blo 2151435 17694737 := bstep (se 2 (by rfl) ⟨6635526, by rfl⟩ : syracuseStep 17694737 = 13271053) B13271053
theorem B11796491 : Blo 2151435 11796491 := bstep (se 1 (by rfl) ⟨8847368, by rfl⟩ : syracuseStep 11796491 = 17694737) B17694737
theorem B7864327 : Blo 2151435 7864327 := bstep (se 1 (by rfl) ⟨5898245, by rfl⟩ : syracuseStep 7864327 = 11796491) B11796491
theorem B10485769 : Blo 2151435 10485769 := bstep (se 2 (by rfl) ⟨3932163, by rfl⟩ : syracuseStep 10485769 = 7864327) B7864327
theorem B13981025 : Blo 2151435 13981025 := bstep (se 2 (by rfl) ⟨5242884, by rfl⟩ : syracuseStep 13981025 = 10485769) B10485769
theorem B9320683 : Blo 2151435 9320683 := bstep (se 1 (by rfl) ⟨6990512, by rfl⟩ : syracuseStep 9320683 = 13981025) B13981025
theorem B12427577 : Blo 2151435 12427577 := bstep (se 2 (by rfl) ⟨4660341, by rfl⟩ : syracuseStep 12427577 = 9320683) B9320683
theorem B8285051 : Blo 2151435 8285051 := bstep (se 1 (by rfl) ⟨6213788, by rfl⟩ : syracuseStep 8285051 = 12427577) B12427577
theorem B22093469 : Blo 2151435 22093469 := bstep (se 3 (by rfl) ⟨4142525, by rfl⟩ : syracuseStep 22093469 = 8285051) B8285051
theorem B14728979 : Blo 2151435 14728979 := bstep (se 1 (by rfl) ⟨11046734, by rfl⟩ : syracuseStep 14728979 = 22093469) B22093469
theorem B9819319 : Blo 2151435 9819319 := bstep (se 1 (by rfl) ⟨7364489, by rfl⟩ : syracuseStep 9819319 = 14728979) B14728979
theorem B13092425 : Blo 2151435 13092425 := bstep (se 2 (by rfl) ⟨4909659, by rfl⟩ : syracuseStep 13092425 = 9819319) B9819319
theorem B8728283 : Blo 2151435 8728283 := bstep (se 1 (by rfl) ⟨6546212, by rfl⟩ : syracuseStep 8728283 = 13092425) B13092425
theorem B23275421 : Blo 2151435 23275421 := bstep (se 3 (by rfl) ⟨4364141, by rfl⟩ : syracuseStep 23275421 = 8728283) B8728283
theorem B15516947 : Blo 2151435 15516947 := bstep (se 1 (by rfl) ⟨11637710, by rfl⟩ : syracuseStep 15516947 = 23275421) B23275421
theorem B10344631 : Blo 2151435 10344631 := bstep (se 1 (by rfl) ⟨7758473, by rfl⟩ : syracuseStep 10344631 = 15516947) B15516947
theorem B13792841 : Blo 2151435 13792841 := bstep (se 2 (by rfl) ⟨5172315, by rfl⟩ : syracuseStep 13792841 = 10344631) B10344631
theorem B9195227 : Blo 2151435 9195227 := bstep (se 1 (by rfl) ⟨6896420, by rfl⟩ : syracuseStep 9195227 = 13792841) B13792841
theorem B6130151 : Blo 2151435 6130151 := bstep (se 1 (by rfl) ⟨4597613, by rfl⟩ : syracuseStep 6130151 = 9195227) B9195227
theorem B4086767 : Blo 2151435 4086767 := bstep (se 1 (by rfl) ⟨3065075, by rfl⟩ : syracuseStep 4086767 = 6130151) B6130151
theorem B2724511 : Blo 2151435 2724511 := bstep (se 1 (by rfl) ⟨2043383, by rfl⟩ : syracuseStep 2724511 = 4086767) B4086767
theorem B3632681 : Blo 2151435 3632681 := bstep (se 2 (by rfl) ⟨1362255, by rfl⟩ : syracuseStep 3632681 = 2724511) B2724511
theorem B2421787 : Blo 2151435 2421787 := bstep (se 1 (by rfl) ⟨1816340, by rfl⟩ : syracuseStep 2421787 = 3632681) B3632681
theorem B3229049 : Blo 2151435 3229049 := bstep (se 2 (by rfl) ⟨1210893, by rfl⟩ : syracuseStep 3229049 = 2421787) B2421787
theorem B2152699 : Blo 2151435 2152699 := bstep (se 1 (by rfl) ⟨1614524, by rfl⟩ : syracuseStep 2152699 = 3229049) B3229049
theorem B7364501 : Blo 2151435 7364501 := bbase (se 6 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 7364501 = 345211) (by norm_num)
theorem B4909667 : Blo 2151435 4909667 := bstep (se 1 (by rfl) ⟨3682250, by rfl⟩ : syracuseStep 4909667 = 7364501) B7364501
theorem B13092445 : Blo 2151435 13092445 := bstep (se 3 (by rfl) ⟨2454833, by rfl⟩ : syracuseStep 13092445 = 4909667) B4909667
theorem B17456593 : Blo 2151435 17456593 := bstep (se 2 (by rfl) ⟨6546222, by rfl⟩ : syracuseStep 17456593 = 13092445) B13092445
theorem B23275457 : Blo 2151435 23275457 := bstep (se 2 (by rfl) ⟨8728296, by rfl⟩ : syracuseStep 23275457 = 17456593) B17456593
theorem B15516971 : Blo 2151435 15516971 := bstep (se 1 (by rfl) ⟨11637728, by rfl⟩ : syracuseStep 15516971 = 23275457) B23275457
theorem B10344647 : Blo 2151435 10344647 := bstep (se 1 (by rfl) ⟨7758485, by rfl⟩ : syracuseStep 10344647 = 15516971) B15516971
theorem B6896431 : Blo 2151435 6896431 := bstep (se 1 (by rfl) ⟨5172323, by rfl⟩ : syracuseStep 6896431 = 10344647) B10344647
theorem B36780965 : Blo 2151435 36780965 := bstep (se 4 (by rfl) ⟨3448215, by rfl⟩ : syracuseStep 36780965 = 6896431) B6896431
theorem B24520643 : Blo 2151435 24520643 := bstep (se 1 (by rfl) ⟨18390482, by rfl⟩ : syracuseStep 24520643 = 36780965) B36780965
theorem B16347095 : Blo 2151435 16347095 := bstep (se 1 (by rfl) ⟨12260321, by rfl⟩ : syracuseStep 16347095 = 24520643) B24520643
theorem B10898063 : Blo 2151435 10898063 := bstep (se 1 (by rfl) ⟨8173547, by rfl⟩ : syracuseStep 10898063 = 16347095) B16347095
theorem B7265375 : Blo 2151435 7265375 := bstep (se 1 (by rfl) ⟨5449031, by rfl⟩ : syracuseStep 7265375 = 10898063) B10898063
theorem B4843583 : Blo 2151435 4843583 := bstep (se 1 (by rfl) ⟨3632687, by rfl⟩ : syracuseStep 4843583 = 7265375) B7265375
theorem B3229055 : Blo 2151435 3229055 := bstep (se 1 (by rfl) ⟨2421791, by rfl⟩ : syracuseStep 3229055 = 4843583) B4843583
theorem B2152703 : Blo 2151435 2152703 := bstep (se 1 (by rfl) ⟨1614527, by rfl⟩ : syracuseStep 2152703 = 3229055) B3229055
theorem B3229061 : Blo 2151435 3229061 := bbase (se 4 (by rfl) ⟨302724, by rfl⟩ : syracuseStep 3229061 = 605449) (by norm_num)
theorem B2152707 : Blo 2151435 2152707 := bstep (se 1 (by rfl) ⟨1614530, by rfl⟩ : syracuseStep 2152707 = 3229061) B3229061
theorem B3632701 : Blo 2151435 3632701 := bbase (se 3 (by rfl) ⟨681131, by rfl⟩ : syracuseStep 3632701 = 1362263) (by norm_num)
theorem B4843601 : Blo 2151435 4843601 := bstep (se 2 (by rfl) ⟨1816350, by rfl⟩ : syracuseStep 4843601 = 3632701) B3632701
theorem B3229067 : Blo 2151435 3229067 := bstep (se 1 (by rfl) ⟨2421800, by rfl⟩ : syracuseStep 3229067 = 4843601) B4843601
theorem B2152711 : Blo 2151435 2152711 := bstep (se 1 (by rfl) ⟨1614533, by rfl⟩ : syracuseStep 2152711 = 3229067) B3229067
theorem B2421805 : Blo 2151435 2421805 := bbase (se 3 (by rfl) ⟨454088, by rfl⟩ : syracuseStep 2421805 = 908177) (by norm_num)
theorem B3229073 : Blo 2151435 3229073 := bstep (se 2 (by rfl) ⟨1210902, by rfl⟩ : syracuseStep 3229073 = 2421805) B2421805
theorem B2152715 : Blo 2151435 2152715 := bstep (se 1 (by rfl) ⟨1614536, by rfl⟩ : syracuseStep 2152715 = 3229073) B3229073
theorem B7265429 : Blo 2151435 7265429 := bbase (se 6 (by rfl) ⟨170283, by rfl⟩ : syracuseStep 7265429 = 340567) (by norm_num)
theorem B4843619 : Blo 2151435 4843619 := bstep (se 1 (by rfl) ⟨3632714, by rfl⟩ : syracuseStep 4843619 = 7265429) B7265429
theorem B3229079 : Blo 2151435 3229079 := bstep (se 1 (by rfl) ⟨2421809, by rfl⟩ : syracuseStep 3229079 = 4843619) B4843619
theorem B2152719 : Blo 2151435 2152719 := bstep (se 1 (by rfl) ⟨1614539, by rfl⟩ : syracuseStep 2152719 = 3229079) B3229079
theorem B3229085 : Blo 2151435 3229085 := bbase (se 3 (by rfl) ⟨605453, by rfl⟩ : syracuseStep 3229085 = 1210907) (by norm_num)
theorem B2152723 : Blo 2151435 2152723 := bstep (se 1 (by rfl) ⟨1614542, by rfl⟩ : syracuseStep 2152723 = 3229085) B3229085
theorem B4843637 : Blo 2151435 4843637 := bbase (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) (by norm_num)
theorem B3229091 : Blo 2151435 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B2152727 : Blo 2151435 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B3448261 : Blo 2151435 3448261 := bbase (se 4 (by rfl) ⟨323274, by rfl⟩ : syracuseStep 3448261 = 646549) (by norm_num)
theorem B18390725 : Blo 2151435 18390725 := bstep (se 4 (by rfl) ⟨1724130, by rfl⟩ : syracuseStep 18390725 = 3448261) B3448261
theorem B12260483 : Blo 2151435 12260483 := bstep (se 1 (by rfl) ⟨9195362, by rfl⟩ : syracuseStep 12260483 = 18390725) B18390725
theorem B8173655 : Blo 2151435 8173655 := bstep (se 1 (by rfl) ⟨6130241, by rfl⟩ : syracuseStep 8173655 = 12260483) B12260483
theorem B5449103 : Blo 2151435 5449103 := bstep (se 1 (by rfl) ⟨4086827, by rfl⟩ : syracuseStep 5449103 = 8173655) B8173655
theorem B3632735 : Blo 2151435 3632735 := bstep (se 1 (by rfl) ⟨2724551, by rfl⟩ : syracuseStep 3632735 = 5449103) B5449103
theorem B2421823 : Blo 2151435 2421823 := bstep (se 1 (by rfl) ⟨1816367, by rfl⟩ : syracuseStep 2421823 = 3632735) B3632735
theorem B3229097 : Blo 2151435 3229097 := bstep (se 2 (by rfl) ⟨1210911, by rfl⟩ : syracuseStep 3229097 = 2421823) B2421823
theorem B2152731 : Blo 2151435 2152731 := bstep (se 1 (by rfl) ⟨1614548, by rfl⟩ : syracuseStep 2152731 = 3229097) B3229097
theorem B8173669 : Blo 2151435 8173669 := bbase (se 4 (by rfl) ⟨766281, by rfl⟩ : syracuseStep 8173669 = 1532563) (by norm_num)
theorem B10898225 : Blo 2151435 10898225 := bstep (se 2 (by rfl) ⟨4086834, by rfl⟩ : syracuseStep 10898225 = 8173669) B8173669
theorem B7265483 : Blo 2151435 7265483 := bstep (se 1 (by rfl) ⟨5449112, by rfl⟩ : syracuseStep 7265483 = 10898225) B10898225
theorem B4843655 : Blo 2151435 4843655 := bstep (se 1 (by rfl) ⟨3632741, by rfl⟩ : syracuseStep 4843655 = 7265483) B7265483
theorem B3229103 : Blo 2151435 3229103 := bstep (se 1 (by rfl) ⟨2421827, by rfl⟩ : syracuseStep 3229103 = 4843655) B4843655
theorem B2152735 : Blo 2151435 2152735 := bstep (se 1 (by rfl) ⟨1614551, by rfl⟩ : syracuseStep 2152735 = 3229103) B3229103
theorem B3229109 : Blo 2151435 3229109 := bbase (se 5 (by rfl) ⟨151364, by rfl⟩ : syracuseStep 3229109 = 302729) (by norm_num)
theorem B2152739 : Blo 2151435 2152739 := bstep (se 1 (by rfl) ⟨1614554, by rfl⟩ : syracuseStep 2152739 = 3229109) B3229109
theorem B5449133 : Blo 2151435 5449133 := bbase (se 3 (by rfl) ⟨1021712, by rfl⟩ : syracuseStep 5449133 = 2043425) (by norm_num)
theorem B3632755 : Blo 2151435 3632755 := bstep (se 1 (by rfl) ⟨2724566, by rfl⟩ : syracuseStep 3632755 = 5449133) B5449133
theorem B4843673 : Blo 2151435 4843673 := bstep (se 2 (by rfl) ⟨1816377, by rfl⟩ : syracuseStep 4843673 = 3632755) B3632755
theorem B3229115 : Blo 2151435 3229115 := bstep (se 1 (by rfl) ⟨2421836, by rfl⟩ : syracuseStep 3229115 = 4843673) B4843673
theorem B2152743 : Blo 2151435 2152743 := bstep (se 1 (by rfl) ⟨1614557, by rfl⟩ : syracuseStep 2152743 = 3229115) B3229115
theorem B2421841 : Blo 2151435 2421841 := bbase (se 2 (by rfl) ⟨908190, by rfl⟩ : syracuseStep 2421841 = 1816381) (by norm_num)
theorem B3229121 : Blo 2151435 3229121 := bstep (se 2 (by rfl) ⟨1210920, by rfl⟩ : syracuseStep 3229121 = 2421841) B2421841
theorem B2152747 : Blo 2151435 2152747 := bstep (se 1 (by rfl) ⟨1614560, by rfl⟩ : syracuseStep 2152747 = 3229121) B3229121
theorem B3065149 : Blo 2151435 3065149 := bbase (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) (by norm_num)
theorem B4086865 : Blo 2151435 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B5449153 : Blo 2151435 5449153 := bstep (se 2 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 5449153 = 4086865) B4086865
theorem B7265537 : Blo 2151435 7265537 := bstep (se 2 (by rfl) ⟨2724576, by rfl⟩ : syracuseStep 7265537 = 5449153) B5449153
theorem B4843691 : Blo 2151435 4843691 := bstep (se 1 (by rfl) ⟨3632768, by rfl⟩ : syracuseStep 4843691 = 7265537) B7265537
theorem B3229127 : Blo 2151435 3229127 := bstep (se 1 (by rfl) ⟨2421845, by rfl⟩ : syracuseStep 3229127 = 4843691) B4843691
theorem B2152751 : Blo 2151435 2152751 := bstep (se 1 (by rfl) ⟨1614563, by rfl⟩ : syracuseStep 2152751 = 3229127) B3229127
theorem B3229133 : Blo 2151435 3229133 := bbase (se 3 (by rfl) ⟨605462, by rfl⟩ : syracuseStep 3229133 = 1210925) (by norm_num)
theorem B2152755 : Blo 2151435 2152755 := bstep (se 1 (by rfl) ⟨1614566, by rfl⟩ : syracuseStep 2152755 = 3229133) B3229133
theorem B4843709 : Blo 2151435 4843709 := bbase (se 3 (by rfl) ⟨908195, by rfl⟩ : syracuseStep 4843709 = 1816391) (by norm_num)
theorem B3229139 : Blo 2151435 3229139 := bstep (se 1 (by rfl) ⟨2421854, by rfl⟩ : syracuseStep 3229139 = 4843709) B4843709
theorem B2152759 : Blo 2151435 2152759 := bstep (se 1 (by rfl) ⟨1614569, by rfl⟩ : syracuseStep 2152759 = 3229139) B3229139
theorem B3632789 : Blo 2151435 3632789 := bbase (se 6 (by rfl) ⟨85143, by rfl⟩ : syracuseStep 3632789 = 170287) (by norm_num)
theorem B2421859 : Blo 2151435 2421859 := bstep (se 1 (by rfl) ⟨1816394, by rfl⟩ : syracuseStep 2421859 = 3632789) B3632789
theorem B3229145 : Blo 2151435 3229145 := bstep (se 2 (by rfl) ⟨1210929, by rfl⟩ : syracuseStep 3229145 = 2421859) B2421859
theorem B2152763 : Blo 2151435 2152763 := bstep (se 1 (by rfl) ⟨1614572, by rfl⟩ : syracuseStep 2152763 = 3229145) B3229145
theorem B19639253 : Blo 2151435 19639253 := bbase (se 7 (by rfl) ⟨230147, by rfl⟩ : syracuseStep 19639253 = 460295) (by norm_num)
theorem B13092835 : Blo 2151435 13092835 := bstep (se 1 (by rfl) ⟨9819626, by rfl⟩ : syracuseStep 13092835 = 19639253) B19639253
theorem B17457113 : Blo 2151435 17457113 := bstep (se 2 (by rfl) ⟨6546417, by rfl⟩ : syracuseStep 17457113 = 13092835) B13092835
theorem B11638075 : Blo 2151435 11638075 := bstep (se 1 (by rfl) ⟨8728556, by rfl⟩ : syracuseStep 11638075 = 17457113) B17457113
theorem B15517433 : Blo 2151435 15517433 := bstep (se 2 (by rfl) ⟨5819037, by rfl⟩ : syracuseStep 15517433 = 11638075) B11638075
theorem B10344955 : Blo 2151435 10344955 := bstep (se 1 (by rfl) ⟨7758716, by rfl⟩ : syracuseStep 10344955 = 15517433) B15517433
theorem B13793273 : Blo 2151435 13793273 := bstep (se 2 (by rfl) ⟨5172477, by rfl⟩ : syracuseStep 13793273 = 10344955) B10344955
theorem B9195515 : Blo 2151435 9195515 := bstep (se 1 (by rfl) ⟨6896636, by rfl⟩ : syracuseStep 9195515 = 13793273) B13793273
theorem B6130343 : Blo 2151435 6130343 := bstep (se 1 (by rfl) ⟨4597757, by rfl⟩ : syracuseStep 6130343 = 9195515) B9195515
theorem B16347581 : Blo 2151435 16347581 := bstep (se 3 (by rfl) ⟨3065171, by rfl⟩ : syracuseStep 16347581 = 6130343) B6130343
theorem B10898387 : Blo 2151435 10898387 := bstep (se 1 (by rfl) ⟨8173790, by rfl⟩ : syracuseStep 10898387 = 16347581) B16347581
theorem B7265591 : Blo 2151435 7265591 := bstep (se 1 (by rfl) ⟨5449193, by rfl⟩ : syracuseStep 7265591 = 10898387) B10898387
theorem B4843727 : Blo 2151435 4843727 := bstep (se 1 (by rfl) ⟨3632795, by rfl⟩ : syracuseStep 4843727 = 7265591) B7265591
theorem B3229151 : Blo 2151435 3229151 := bstep (se 1 (by rfl) ⟨2421863, by rfl⟩ : syracuseStep 3229151 = 4843727) B4843727
theorem B2152767 : Blo 2151435 2152767 := bstep (se 1 (by rfl) ⟨1614575, by rfl⟩ : syracuseStep 2152767 = 3229151) B3229151
theorem B3229157 : Blo 2151435 3229157 := bbase (se 4 (by rfl) ⟨302733, by rfl⟩ : syracuseStep 3229157 = 605467) (by norm_num)
theorem B2152771 : Blo 2151435 2152771 := bstep (se 1 (by rfl) ⟨1614578, by rfl⟩ : syracuseStep 2152771 = 3229157) B3229157
theorem B5243069 : Blo 2151435 5243069 := bbase (se 3 (by rfl) ⟨983075, by rfl⟩ : syracuseStep 5243069 = 1966151) (by norm_num)
theorem B13981517 : Blo 2151435 13981517 := bstep (se 3 (by rfl) ⟨2621534, by rfl⟩ : syracuseStep 13981517 = 5243069) B5243069
theorem B9321011 : Blo 2151435 9321011 := bstep (se 1 (by rfl) ⟨6990758, by rfl⟩ : syracuseStep 9321011 = 13981517) B13981517
theorem B6214007 : Blo 2151435 6214007 := bstep (se 1 (by rfl) ⟨4660505, by rfl⟩ : syracuseStep 6214007 = 9321011) B9321011
theorem B4142671 : Blo 2151435 4142671 := bstep (se 1 (by rfl) ⟨3107003, by rfl⟩ : syracuseStep 4142671 = 6214007) B6214007
theorem B22094245 : Blo 2151435 22094245 := bstep (se 4 (by rfl) ⟨2071335, by rfl⟩ : syracuseStep 22094245 = 4142671) B4142671
theorem B29458993 : Blo 2151435 29458993 := bstep (se 2 (by rfl) ⟨11047122, by rfl⟩ : syracuseStep 29458993 = 22094245) B22094245
theorem B39278657 : Blo 2151435 39278657 := bstep (se 2 (by rfl) ⟨14729496, by rfl⟩ : syracuseStep 39278657 = 29458993) B29458993
theorem B26185771 : Blo 2151435 26185771 := bstep (se 1 (by rfl) ⟨19639328, by rfl⟩ : syracuseStep 26185771 = 39278657) B39278657
theorem B34914361 : Blo 2151435 34914361 := bstep (se 2 (by rfl) ⟨13092885, by rfl⟩ : syracuseStep 34914361 = 26185771) B26185771
theorem B46552481 : Blo 2151435 46552481 := bstep (se 2 (by rfl) ⟨17457180, by rfl⟩ : syracuseStep 46552481 = 34914361) B34914361
theorem B31034987 : Blo 2151435 31034987 := bstep (se 1 (by rfl) ⟨23276240, by rfl⟩ : syracuseStep 31034987 = 46552481) B46552481
theorem B20689991 : Blo 2151435 20689991 := bstep (se 1 (by rfl) ⟨15517493, by rfl⟩ : syracuseStep 20689991 = 31034987) B31034987
theorem B13793327 : Blo 2151435 13793327 := bstep (se 1 (by rfl) ⟨10344995, by rfl⟩ : syracuseStep 13793327 = 20689991) B20689991
theorem B9195551 : Blo 2151435 9195551 := bstep (se 1 (by rfl) ⟨6896663, by rfl⟩ : syracuseStep 9195551 = 13793327) B13793327
theorem B6130367 : Blo 2151435 6130367 := bstep (se 1 (by rfl) ⟨4597775, by rfl⟩ : syracuseStep 6130367 = 9195551) B9195551
theorem B4086911 : Blo 2151435 4086911 := bstep (se 1 (by rfl) ⟨3065183, by rfl⟩ : syracuseStep 4086911 = 6130367) B6130367
theorem B2724607 : Blo 2151435 2724607 := bstep (se 1 (by rfl) ⟨2043455, by rfl⟩ : syracuseStep 2724607 = 4086911) B4086911
theorem B3632809 : Blo 2151435 3632809 := bstep (se 2 (by rfl) ⟨1362303, by rfl⟩ : syracuseStep 3632809 = 2724607) B2724607
theorem B4843745 : Blo 2151435 4843745 := bstep (se 2 (by rfl) ⟨1816404, by rfl⟩ : syracuseStep 4843745 = 3632809) B3632809
theorem B3229163 : Blo 2151435 3229163 := bstep (se 1 (by rfl) ⟨2421872, by rfl⟩ : syracuseStep 3229163 = 4843745) B4843745
theorem B2152775 : Blo 2151435 2152775 := bstep (se 1 (by rfl) ⟨1614581, by rfl⟩ : syracuseStep 2152775 = 3229163) B3229163
theorem B2421877 : Blo 2151435 2421877 := bbase (se 5 (by rfl) ⟨113525, by rfl⟩ : syracuseStep 2421877 = 227051) (by norm_num)
theorem B3229169 : Blo 2151435 3229169 := bstep (se 2 (by rfl) ⟨1210938, by rfl⟩ : syracuseStep 3229169 = 2421877) B2421877
theorem B2152779 : Blo 2151435 2152779 := bstep (se 1 (by rfl) ⟨1614584, by rfl⟩ : syracuseStep 2152779 = 3229169) B3229169
theorem B2724617 : Blo 2151435 2724617 := bbase (se 2 (by rfl) ⟨1021731, by rfl⟩ : syracuseStep 2724617 = 2043463) (by norm_num)
theorem B7265645 : Blo 2151435 7265645 := bstep (se 3 (by rfl) ⟨1362308, by rfl⟩ : syracuseStep 7265645 = 2724617) B2724617
theorem B4843763 : Blo 2151435 4843763 := bstep (se 1 (by rfl) ⟨3632822, by rfl⟩ : syracuseStep 4843763 = 7265645) B7265645
theorem B3229175 : Blo 2151435 3229175 := bstep (se 1 (by rfl) ⟨2421881, by rfl⟩ : syracuseStep 3229175 = 4843763) B4843763
theorem B2152783 : Blo 2151435 2152783 := bstep (se 1 (by rfl) ⟨1614587, by rfl⟩ : syracuseStep 2152783 = 3229175) B3229175
theorem B3229181 : Blo 2151435 3229181 := bbase (se 3 (by rfl) ⟨605471, by rfl⟩ : syracuseStep 3229181 = 1210943) (by norm_num)
theorem B2152787 : Blo 2151435 2152787 := bstep (se 1 (by rfl) ⟨1614590, by rfl⟩ : syracuseStep 2152787 = 3229181) B3229181
theorem B4843781 : Blo 2151435 4843781 := bbase (se 4 (by rfl) ⟨454104, by rfl⟩ : syracuseStep 4843781 = 908209) (by norm_num)
theorem B3229187 : Blo 2151435 3229187 := bstep (se 1 (by rfl) ⟨2421890, by rfl⟩ : syracuseStep 3229187 = 4843781) B4843781
theorem B2152791 : Blo 2151435 2152791 := bstep (se 1 (by rfl) ⟨1614593, by rfl⟩ : syracuseStep 2152791 = 3229187) B3229187
theorem B4086949 : Blo 2151435 4086949 := bbase (se 4 (by rfl) ⟨383151, by rfl⟩ : syracuseStep 4086949 = 766303) (by norm_num)
theorem B5449265 : Blo 2151435 5449265 := bstep (se 2 (by rfl) ⟨2043474, by rfl⟩ : syracuseStep 5449265 = 4086949) B4086949
theorem B3632843 : Blo 2151435 3632843 := bstep (se 1 (by rfl) ⟨2724632, by rfl⟩ : syracuseStep 3632843 = 5449265) B5449265
theorem B2421895 : Blo 2151435 2421895 := bstep (se 1 (by rfl) ⟨1816421, by rfl⟩ : syracuseStep 2421895 = 3632843) B3632843
theorem B3229193 : Blo 2151435 3229193 := bstep (se 2 (by rfl) ⟨1210947, by rfl⟩ : syracuseStep 3229193 = 2421895) B2421895
theorem B2152795 : Blo 2151435 2152795 := bstep (se 1 (by rfl) ⟨1614596, by rfl⟩ : syracuseStep 2152795 = 3229193) B3229193
theorem B10898549 : Blo 2151435 10898549 := bbase (se 5 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 10898549 = 1021739) (by norm_num)
theorem B7265699 : Blo 2151435 7265699 := bstep (se 1 (by rfl) ⟨5449274, by rfl⟩ : syracuseStep 7265699 = 10898549) B10898549
theorem B4843799 : Blo 2151435 4843799 := bstep (se 1 (by rfl) ⟨3632849, by rfl⟩ : syracuseStep 4843799 = 7265699) B7265699
theorem B3229199 : Blo 2151435 3229199 := bstep (se 1 (by rfl) ⟨2421899, by rfl⟩ : syracuseStep 3229199 = 4843799) B4843799
theorem B2152799 : Blo 2151435 2152799 := bstep (se 1 (by rfl) ⟨1614599, by rfl⟩ : syracuseStep 2152799 = 3229199) B3229199
theorem B3229205 : Blo 2151435 3229205 := bbase (se 6 (by rfl) ⟨75684, by rfl⟩ : syracuseStep 3229205 = 151369) (by norm_num)
theorem B2152803 : Blo 2151435 2152803 := bstep (se 1 (by rfl) ⟨1614602, by rfl⟩ : syracuseStep 2152803 = 3229205) B3229205
theorem B2454953 : Blo 2151435 2454953 := bbase (se 2 (by rfl) ⟨920607, by rfl⟩ : syracuseStep 2454953 = 1841215) (by norm_num)
theorem B6546541 : Blo 2151435 6546541 := bstep (se 3 (by rfl) ⟨1227476, by rfl⟩ : syracuseStep 6546541 = 2454953) B2454953
theorem B8728721 : Blo 2151435 8728721 := bstep (se 2 (by rfl) ⟨3273270, by rfl⟩ : syracuseStep 8728721 = 6546541) B6546541
theorem B5819147 : Blo 2151435 5819147 := bstep (se 1 (by rfl) ⟨4364360, by rfl⟩ : syracuseStep 5819147 = 8728721) B8728721
theorem B3879431 : Blo 2151435 3879431 := bstep (se 1 (by rfl) ⟨2909573, by rfl⟩ : syracuseStep 3879431 = 5819147) B5819147
theorem B2586287 : Blo 2151435 2586287 := bstep (se 1 (by rfl) ⟨1939715, by rfl⟩ : syracuseStep 2586287 = 3879431) B3879431
theorem B6896765 : Blo 2151435 6896765 := bstep (se 3 (by rfl) ⟨1293143, by rfl⟩ : syracuseStep 6896765 = 2586287) B2586287
theorem B18391373 : Blo 2151435 18391373 := bstep (se 3 (by rfl) ⟨3448382, by rfl⟩ : syracuseStep 18391373 = 6896765) B6896765
theorem B12260915 : Blo 2151435 12260915 := bstep (se 1 (by rfl) ⟨9195686, by rfl⟩ : syracuseStep 12260915 = 18391373) B18391373
theorem B8173943 : Blo 2151435 8173943 := bstep (se 1 (by rfl) ⟨6130457, by rfl⟩ : syracuseStep 8173943 = 12260915) B12260915
theorem B5449295 : Blo 2151435 5449295 := bstep (se 1 (by rfl) ⟨4086971, by rfl⟩ : syracuseStep 5449295 = 8173943) B8173943
theorem B3632863 : Blo 2151435 3632863 := bstep (se 1 (by rfl) ⟨2724647, by rfl⟩ : syracuseStep 3632863 = 5449295) B5449295
theorem B4843817 : Blo 2151435 4843817 := bstep (se 2 (by rfl) ⟨1816431, by rfl⟩ : syracuseStep 4843817 = 3632863) B3632863
theorem B3229211 : Blo 2151435 3229211 := bstep (se 1 (by rfl) ⟨2421908, by rfl⟩ : syracuseStep 3229211 = 4843817) B4843817
theorem B2152807 : Blo 2151435 2152807 := bstep (se 1 (by rfl) ⟨1614605, by rfl⟩ : syracuseStep 2152807 = 3229211) B3229211
theorem B2421913 : Blo 2151435 2421913 := bbase (se 2 (by rfl) ⟨908217, by rfl⟩ : syracuseStep 2421913 = 1816435) (by norm_num)
theorem B3229217 : Blo 2151435 3229217 := bstep (se 2 (by rfl) ⟨1210956, by rfl⟩ : syracuseStep 3229217 = 2421913) B2421913
theorem B2152811 : Blo 2151435 2152811 := bstep (se 1 (by rfl) ⟨1614608, by rfl⟩ : syracuseStep 2152811 = 3229217) B3229217
theorem B8173973 : Blo 2151435 8173973 := bbase (se 6 (by rfl) ⟨191577, by rfl⟩ : syracuseStep 8173973 = 383155) (by norm_num)
theorem B5449315 : Blo 2151435 5449315 := bstep (se 1 (by rfl) ⟨4086986, by rfl⟩ : syracuseStep 5449315 = 8173973) B8173973
theorem B7265753 : Blo 2151435 7265753 := bstep (se 2 (by rfl) ⟨2724657, by rfl⟩ : syracuseStep 7265753 = 5449315) B5449315
theorem B4843835 : Blo 2151435 4843835 := bstep (se 1 (by rfl) ⟨3632876, by rfl⟩ : syracuseStep 4843835 = 7265753) B7265753
theorem B3229223 : Blo 2151435 3229223 := bstep (se 1 (by rfl) ⟨2421917, by rfl⟩ : syracuseStep 3229223 = 4843835) B4843835
theorem B2152815 : Blo 2151435 2152815 := bstep (se 1 (by rfl) ⟨1614611, by rfl⟩ : syracuseStep 2152815 = 3229223) B3229223
theorem B3229229 : Blo 2151435 3229229 := bbase (se 3 (by rfl) ⟨605480, by rfl⟩ : syracuseStep 3229229 = 1210961) (by norm_num)
theorem B2152819 : Blo 2151435 2152819 := bstep (se 1 (by rfl) ⟨1614614, by rfl⟩ : syracuseStep 2152819 = 3229229) B3229229
theorem B4843853 : Blo 2151435 4843853 := bbase (se 3 (by rfl) ⟨908222, by rfl⟩ : syracuseStep 4843853 = 1816445) (by norm_num)
theorem B3229235 : Blo 2151435 3229235 := bstep (se 1 (by rfl) ⟨2421926, by rfl⟩ : syracuseStep 3229235 = 4843853) B4843853
theorem B2152823 : Blo 2151435 2152823 := bstep (se 1 (by rfl) ⟨1614617, by rfl⟩ : syracuseStep 2152823 = 3229235) B3229235
theorem B2724673 : Blo 2151435 2724673 := bbase (se 2 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 2724673 = 2043505) (by norm_num)
theorem B3632897 : Blo 2151435 3632897 := bstep (se 2 (by rfl) ⟨1362336, by rfl⟩ : syracuseStep 3632897 = 2724673) B2724673
theorem B2421931 : Blo 2151435 2421931 := bstep (se 1 (by rfl) ⟨1816448, by rfl⟩ : syracuseStep 2421931 = 3632897) B3632897
theorem B3229241 : Blo 2151435 3229241 := bstep (se 2 (by rfl) ⟨1210965, by rfl⟩ : syracuseStep 3229241 = 2421931) B2421931
theorem B2152827 : Blo 2151435 2152827 := bstep (se 1 (by rfl) ⟨1614620, by rfl⟩ : syracuseStep 2152827 = 3229241) B3229241
theorem B3448421 : Blo 2151435 3448421 := bbase (se 4 (by rfl) ⟨323289, by rfl⟩ : syracuseStep 3448421 = 646579) (by norm_num)
theorem B2298947 : Blo 2151435 2298947 := bstep (se 1 (by rfl) ⟨1724210, by rfl⟩ : syracuseStep 2298947 = 3448421) B3448421
theorem B24522101 : Blo 2151435 24522101 := bstep (se 5 (by rfl) ⟨1149473, by rfl⟩ : syracuseStep 24522101 = 2298947) B2298947
theorem B16348067 : Blo 2151435 16348067 := bstep (se 1 (by rfl) ⟨12261050, by rfl⟩ : syracuseStep 16348067 = 24522101) B24522101
theorem B10898711 : Blo 2151435 10898711 := bstep (se 1 (by rfl) ⟨8174033, by rfl⟩ : syracuseStep 10898711 = 16348067) B16348067
theorem B7265807 : Blo 2151435 7265807 := bstep (se 1 (by rfl) ⟨5449355, by rfl⟩ : syracuseStep 7265807 = 10898711) B10898711
theorem B4843871 : Blo 2151435 4843871 := bstep (se 1 (by rfl) ⟨3632903, by rfl⟩ : syracuseStep 4843871 = 7265807) B7265807
theorem B3229247 : Blo 2151435 3229247 := bstep (se 1 (by rfl) ⟨2421935, by rfl⟩ : syracuseStep 3229247 = 4843871) B4843871
theorem B2152831 : Blo 2151435 2152831 := bstep (se 1 (by rfl) ⟨1614623, by rfl⟩ : syracuseStep 2152831 = 3229247) B3229247
theorem B3229253 : Blo 2151435 3229253 := bbase (se 4 (by rfl) ⟨302742, by rfl⟩ : syracuseStep 3229253 = 605485) (by norm_num)
theorem B2152835 : Blo 2151435 2152835 := bstep (se 1 (by rfl) ⟨1614626, by rfl⟩ : syracuseStep 2152835 = 3229253) B3229253
theorem B3632917 : Blo 2151435 3632917 := bbase (se 6 (by rfl) ⟨85146, by rfl⟩ : syracuseStep 3632917 = 170293) (by norm_num)
theorem B4843889 : Blo 2151435 4843889 := bstep (se 2 (by rfl) ⟨1816458, by rfl⟩ : syracuseStep 4843889 = 3632917) B3632917
theorem B3229259 : Blo 2151435 3229259 := bstep (se 1 (by rfl) ⟨2421944, by rfl⟩ : syracuseStep 3229259 = 4843889) B4843889
theorem B2152839 : Blo 2151435 2152839 := bstep (se 1 (by rfl) ⟨1614629, by rfl⟩ : syracuseStep 2152839 = 3229259) B3229259
theorem B2421949 : Blo 2151435 2421949 := bbase (se 3 (by rfl) ⟨454115, by rfl⟩ : syracuseStep 2421949 = 908231) (by norm_num)
theorem B3229265 : Blo 2151435 3229265 := bstep (se 2 (by rfl) ⟨1210974, by rfl⟩ : syracuseStep 3229265 = 2421949) B2421949
theorem B2152843 : Blo 2151435 2152843 := bstep (se 1 (by rfl) ⟨1614632, by rfl⟩ : syracuseStep 2152843 = 3229265) B3229265
theorem B7265861 : Blo 2151435 7265861 := bbase (se 4 (by rfl) ⟨681174, by rfl⟩ : syracuseStep 7265861 = 1362349) (by norm_num)
theorem B4843907 : Blo 2151435 4843907 := bstep (se 1 (by rfl) ⟨3632930, by rfl⟩ : syracuseStep 4843907 = 7265861) B7265861
theorem B3229271 : Blo 2151435 3229271 := bstep (se 1 (by rfl) ⟨2421953, by rfl⟩ : syracuseStep 3229271 = 4843907) B4843907
theorem B2152847 : Blo 2151435 2152847 := bstep (se 1 (by rfl) ⟨1614635, by rfl⟩ : syracuseStep 2152847 = 3229271) B3229271
theorem B3229277 : Blo 2151435 3229277 := bbase (se 3 (by rfl) ⟨605489, by rfl⟩ : syracuseStep 3229277 = 1210979) (by norm_num)
theorem B2152851 : Blo 2151435 2152851 := bstep (se 1 (by rfl) ⟨1614638, by rfl⟩ : syracuseStep 2152851 = 3229277) B3229277
theorem B4843925 : Blo 2151435 4843925 := bbase (se 6 (by rfl) ⟨113529, by rfl⟩ : syracuseStep 4843925 = 227059) (by norm_num)
theorem B3229283 : Blo 2151435 3229283 := bstep (se 1 (by rfl) ⟨2421962, by rfl⟩ : syracuseStep 3229283 = 4843925) B4843925
theorem B2152855 : Blo 2151435 2152855 := bstep (se 1 (by rfl) ⟨1614641, by rfl⟩ : syracuseStep 2152855 = 3229283) B3229283
theorem B6896933 : Blo 2151435 6896933 := bbase (se 4 (by rfl) ⟨646587, by rfl⟩ : syracuseStep 6896933 = 1293175) (by norm_num)
theorem B4597955 : Blo 2151435 4597955 := bstep (se 1 (by rfl) ⟨3448466, by rfl⟩ : syracuseStep 4597955 = 6896933) B6896933
theorem B3065303 : Blo 2151435 3065303 := bstep (se 1 (by rfl) ⟨2298977, by rfl⟩ : syracuseStep 3065303 = 4597955) B4597955
theorem B8174141 : Blo 2151435 8174141 := bstep (se 3 (by rfl) ⟨1532651, by rfl⟩ : syracuseStep 8174141 = 3065303) B3065303
theorem B5449427 : Blo 2151435 5449427 := bstep (se 1 (by rfl) ⟨4087070, by rfl⟩ : syracuseStep 5449427 = 8174141) B8174141
theorem B3632951 : Blo 2151435 3632951 := bstep (se 1 (by rfl) ⟨2724713, by rfl⟩ : syracuseStep 3632951 = 5449427) B5449427
theorem B2421967 : Blo 2151435 2421967 := bstep (se 1 (by rfl) ⟨1816475, by rfl⟩ : syracuseStep 2421967 = 3632951) B3632951
theorem B3229289 : Blo 2151435 3229289 := bstep (se 2 (by rfl) ⟨1210983, by rfl⟩ : syracuseStep 3229289 = 2421967) B2421967
theorem B2152859 : Blo 2151435 2152859 := bstep (se 1 (by rfl) ⟨1614644, by rfl⟩ : syracuseStep 2152859 = 3229289) B3229289
theorem B9195925 : Blo 2151435 9195925 := bbase (se 6 (by rfl) ⟨215529, by rfl⟩ : syracuseStep 9195925 = 431059) (by norm_num)
theorem B12261233 : Blo 2151435 12261233 := bstep (se 2 (by rfl) ⟨4597962, by rfl⟩ : syracuseStep 12261233 = 9195925) B9195925
theorem B8174155 : Blo 2151435 8174155 := bstep (se 1 (by rfl) ⟨6130616, by rfl⟩ : syracuseStep 8174155 = 12261233) B12261233
theorem B10898873 : Blo 2151435 10898873 := bstep (se 2 (by rfl) ⟨4087077, by rfl⟩ : syracuseStep 10898873 = 8174155) B8174155
theorem B7265915 : Blo 2151435 7265915 := bstep (se 1 (by rfl) ⟨5449436, by rfl⟩ : syracuseStep 7265915 = 10898873) B10898873
theorem B4843943 : Blo 2151435 4843943 := bstep (se 1 (by rfl) ⟨3632957, by rfl⟩ : syracuseStep 4843943 = 7265915) B7265915
theorem B3229295 : Blo 2151435 3229295 := bstep (se 1 (by rfl) ⟨2421971, by rfl⟩ : syracuseStep 3229295 = 4843943) B4843943
theorem B2152863 : Blo 2151435 2152863 := bstep (se 1 (by rfl) ⟨1614647, by rfl⟩ : syracuseStep 2152863 = 3229295) B3229295
theorem B3229301 : Blo 2151435 3229301 := bbase (se 5 (by rfl) ⟨151373, by rfl⟩ : syracuseStep 3229301 = 302747) (by norm_num)
theorem B2152867 : Blo 2151435 2152867 := bstep (se 1 (by rfl) ⟨1614650, by rfl⟩ : syracuseStep 2152867 = 3229301) B3229301
theorem B4087093 : Blo 2151435 4087093 := bbase (se 5 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 4087093 = 383165) (by norm_num)
theorem B5449457 : Blo 2151435 5449457 := bstep (se 2 (by rfl) ⟨2043546, by rfl⟩ : syracuseStep 5449457 = 4087093) B4087093
theorem B3632971 : Blo 2151435 3632971 := bstep (se 1 (by rfl) ⟨2724728, by rfl⟩ : syracuseStep 3632971 = 5449457) B5449457
theorem B4843961 : Blo 2151435 4843961 := bstep (se 2 (by rfl) ⟨1816485, by rfl⟩ : syracuseStep 4843961 = 3632971) B3632971
theorem B3229307 : Blo 2151435 3229307 := bstep (se 1 (by rfl) ⟨2421980, by rfl⟩ : syracuseStep 3229307 = 4843961) B4843961
theorem B2152871 : Blo 2151435 2152871 := bstep (se 1 (by rfl) ⟨1614653, by rfl⟩ : syracuseStep 2152871 = 3229307) B3229307
theorem B2421985 : Blo 2151435 2421985 := bbase (se 2 (by rfl) ⟨908244, by rfl⟩ : syracuseStep 2421985 = 1816489) (by norm_num)
theorem B3229313 : Blo 2151435 3229313 := bstep (se 2 (by rfl) ⟨1210992, by rfl⟩ : syracuseStep 3229313 = 2421985) B2421985
theorem B2152875 : Blo 2151435 2152875 := bstep (se 1 (by rfl) ⟨1614656, by rfl⟩ : syracuseStep 2152875 = 3229313) B3229313
theorem B5449477 : Blo 2151435 5449477 := bbase (se 4 (by rfl) ⟨510888, by rfl⟩ : syracuseStep 5449477 = 1021777) (by norm_num)
theorem B7265969 : Blo 2151435 7265969 := bstep (se 2 (by rfl) ⟨2724738, by rfl⟩ : syracuseStep 7265969 = 5449477) B5449477
theorem B4843979 : Blo 2151435 4843979 := bstep (se 1 (by rfl) ⟨3632984, by rfl⟩ : syracuseStep 4843979 = 7265969) B7265969
theorem B3229319 : Blo 2151435 3229319 := bstep (se 1 (by rfl) ⟨2421989, by rfl⟩ : syracuseStep 3229319 = 4843979) B4843979
theorem B2152879 : Blo 2151435 2152879 := bstep (se 1 (by rfl) ⟨1614659, by rfl⟩ : syracuseStep 2152879 = 3229319) B3229319
theorem B3229325 : Blo 2151435 3229325 := bbase (se 3 (by rfl) ⟨605498, by rfl⟩ : syracuseStep 3229325 = 1210997) (by norm_num)
theorem B2152883 : Blo 2151435 2152883 := bstep (se 1 (by rfl) ⟨1614662, by rfl⟩ : syracuseStep 2152883 = 3229325) B3229325
theorem B4843997 : Blo 2151435 4843997 := bbase (se 3 (by rfl) ⟨908249, by rfl⟩ : syracuseStep 4843997 = 1816499) (by norm_num)
theorem B3229331 : Blo 2151435 3229331 := bstep (se 1 (by rfl) ⟨2421998, by rfl⟩ : syracuseStep 3229331 = 4843997) B4843997
theorem B2152887 : Blo 2151435 2152887 := bstep (se 1 (by rfl) ⟨1614665, by rfl⟩ : syracuseStep 2152887 = 3229331) B3229331
theorem B3633005 : Blo 2151435 3633005 := bbase (se 3 (by rfl) ⟨681188, by rfl⟩ : syracuseStep 3633005 = 1362377) (by norm_num)
theorem B2422003 : Blo 2151435 2422003 := bstep (se 1 (by rfl) ⟨1816502, by rfl⟩ : syracuseStep 2422003 = 3633005) B3633005
theorem B3229337 : Blo 2151435 3229337 := bstep (se 2 (by rfl) ⟨1211001, by rfl⟩ : syracuseStep 3229337 = 2422003) B2422003
theorem B2152891 : Blo 2151435 2152891 := bstep (se 1 (by rfl) ⟨1614668, by rfl⟩ : syracuseStep 2152891 = 3229337) B3229337
theorem B5523869 : Blo 2151435 5523869 := bbase (se 3 (by rfl) ⟨1035725, by rfl⟩ : syracuseStep 5523869 = 2071451) (by norm_num)
theorem B3682579 : Blo 2151435 3682579 := bstep (se 1 (by rfl) ⟨2761934, by rfl⟩ : syracuseStep 3682579 = 5523869) B5523869
theorem B4910105 : Blo 2151435 4910105 := bstep (se 2 (by rfl) ⟨1841289, by rfl⟩ : syracuseStep 4910105 = 3682579) B3682579
theorem B13093613 : Blo 2151435 13093613 := bstep (se 3 (by rfl) ⟨2455052, by rfl⟩ : syracuseStep 13093613 = 4910105) B4910105
theorem B8729075 : Blo 2151435 8729075 := bstep (se 1 (by rfl) ⟨6546806, by rfl⟩ : syracuseStep 8729075 = 13093613) B13093613
theorem B5819383 : Blo 2151435 5819383 := bstep (se 1 (by rfl) ⟨4364537, by rfl⟩ : syracuseStep 5819383 = 8729075) B8729075
theorem B31036709 : Blo 2151435 31036709 := bstep (se 4 (by rfl) ⟨2909691, by rfl⟩ : syracuseStep 31036709 = 5819383) B5819383
theorem B20691139 : Blo 2151435 20691139 := bstep (se 1 (by rfl) ⟨15518354, by rfl⟩ : syracuseStep 20691139 = 31036709) B31036709
theorem B27588185 : Blo 2151435 27588185 := bstep (se 2 (by rfl) ⟨10345569, by rfl⟩ : syracuseStep 27588185 = 20691139) B20691139
theorem B18392123 : Blo 2151435 18392123 := bstep (se 1 (by rfl) ⟨13794092, by rfl⟩ : syracuseStep 18392123 = 27588185) B27588185
theorem B12261415 : Blo 2151435 12261415 := bstep (se 1 (by rfl) ⟨9196061, by rfl⟩ : syracuseStep 12261415 = 18392123) B18392123
theorem B16348553 : Blo 2151435 16348553 := bstep (se 2 (by rfl) ⟨6130707, by rfl⟩ : syracuseStep 16348553 = 12261415) B12261415
theorem B10899035 : Blo 2151435 10899035 := bstep (se 1 (by rfl) ⟨8174276, by rfl⟩ : syracuseStep 10899035 = 16348553) B16348553
theorem B7266023 : Blo 2151435 7266023 := bstep (se 1 (by rfl) ⟨5449517, by rfl⟩ : syracuseStep 7266023 = 10899035) B10899035
theorem B4844015 : Blo 2151435 4844015 := bstep (se 1 (by rfl) ⟨3633011, by rfl⟩ : syracuseStep 4844015 = 7266023) B7266023
theorem B3229343 : Blo 2151435 3229343 := bstep (se 1 (by rfl) ⟨2422007, by rfl⟩ : syracuseStep 3229343 = 4844015) B4844015
theorem B2152895 : Blo 2151435 2152895 := bstep (se 1 (by rfl) ⟨1614671, by rfl⟩ : syracuseStep 2152895 = 3229343) B3229343
theorem B3229349 : Blo 2151435 3229349 := bbase (se 4 (by rfl) ⟨302751, by rfl⟩ : syracuseStep 3229349 = 605503) (by norm_num)
theorem B2152899 : Blo 2151435 2152899 := bstep (se 1 (by rfl) ⟨1614674, by rfl⟩ : syracuseStep 2152899 = 3229349) B3229349
theorem B2724769 : Blo 2151435 2724769 := bbase (se 2 (by rfl) ⟨1021788, by rfl⟩ : syracuseStep 2724769 = 2043577) (by norm_num)
theorem B3633025 : Blo 2151435 3633025 := bstep (se 2 (by rfl) ⟨1362384, by rfl⟩ : syracuseStep 3633025 = 2724769) B2724769
theorem B4844033 : Blo 2151435 4844033 := bstep (se 2 (by rfl) ⟨1816512, by rfl⟩ : syracuseStep 4844033 = 3633025) B3633025
theorem B3229355 : Blo 2151435 3229355 := bstep (se 1 (by rfl) ⟨2422016, by rfl⟩ : syracuseStep 3229355 = 4844033) B4844033
theorem B2152903 : Blo 2151435 2152903 := bstep (se 1 (by rfl) ⟨1614677, by rfl⟩ : syracuseStep 2152903 = 3229355) B3229355
theorem B2422021 : Blo 2151435 2422021 := bbase (se 4 (by rfl) ⟨227064, by rfl⟩ : syracuseStep 2422021 = 454129) (by norm_num)
theorem B3229361 : Blo 2151435 3229361 := bstep (se 2 (by rfl) ⟨1211010, by rfl⟩ : syracuseStep 3229361 = 2422021) B2422021
theorem B2152907 : Blo 2151435 2152907 := bstep (se 1 (by rfl) ⟨1614680, by rfl⟩ : syracuseStep 2152907 = 3229361) B3229361
theorem B2299033 : Blo 2151435 2299033 := bbase (se 2 (by rfl) ⟨862137, by rfl⟩ : syracuseStep 2299033 = 1724275) (by norm_num)
theorem B3065377 : Blo 2151435 3065377 := bstep (se 2 (by rfl) ⟨1149516, by rfl⟩ : syracuseStep 3065377 = 2299033) B2299033
theorem B4087169 : Blo 2151435 4087169 := bstep (se 2 (by rfl) ⟨1532688, by rfl⟩ : syracuseStep 4087169 = 3065377) B3065377
theorem B2724779 : Blo 2151435 2724779 := bstep (se 1 (by rfl) ⟨2043584, by rfl⟩ : syracuseStep 2724779 = 4087169) B4087169
theorem B7266077 : Blo 2151435 7266077 := bstep (se 3 (by rfl) ⟨1362389, by rfl⟩ : syracuseStep 7266077 = 2724779) B2724779
theorem B4844051 : Blo 2151435 4844051 := bstep (se 1 (by rfl) ⟨3633038, by rfl⟩ : syracuseStep 4844051 = 7266077) B7266077
theorem B3229367 : Blo 2151435 3229367 := bstep (se 1 (by rfl) ⟨2422025, by rfl⟩ : syracuseStep 3229367 = 4844051) B4844051
theorem B2152911 : Blo 2151435 2152911 := bstep (se 1 (by rfl) ⟨1614683, by rfl⟩ : syracuseStep 2152911 = 3229367) B3229367
theorem B3229373 : Blo 2151435 3229373 := bbase (se 3 (by rfl) ⟨605507, by rfl⟩ : syracuseStep 3229373 = 1211015) (by norm_num)
theorem B2152915 : Blo 2151435 2152915 := bstep (se 1 (by rfl) ⟨1614686, by rfl⟩ : syracuseStep 2152915 = 3229373) B3229373
theorem B4844069 : Blo 2151435 4844069 := bbase (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) (by norm_num)
theorem B3229379 : Blo 2151435 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B2152919 : Blo 2151435 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B5449589 : Blo 2151435 5449589 := bbase (se 5 (by rfl) ⟨255449, by rfl⟩ : syracuseStep 5449589 = 510899) (by norm_num)
theorem B3633059 : Blo 2151435 3633059 := bstep (se 1 (by rfl) ⟨2724794, by rfl⟩ : syracuseStep 3633059 = 5449589) B5449589
theorem B2422039 : Blo 2151435 2422039 := bstep (se 1 (by rfl) ⟨1816529, by rfl⟩ : syracuseStep 2422039 = 3633059) B3633059
theorem B3229385 : Blo 2151435 3229385 := bstep (se 2 (by rfl) ⟨1211019, by rfl⟩ : syracuseStep 3229385 = 2422039) B2422039
theorem B2152923 : Blo 2151435 2152923 := bstep (se 1 (by rfl) ⟨1614692, by rfl⟩ : syracuseStep 2152923 = 3229385) B3229385
theorem B5898869 : Blo 2151435 5898869 := bbase (se 5 (by rfl) ⟨276509, by rfl⟩ : syracuseStep 5898869 = 553019) (by norm_num)
theorem B3932579 : Blo 2151435 3932579 := bstep (se 1 (by rfl) ⟨2949434, by rfl⟩ : syracuseStep 3932579 = 5898869) B5898869
theorem B2621719 : Blo 2151435 2621719 := bstep (se 1 (by rfl) ⟨1966289, by rfl⟩ : syracuseStep 2621719 = 3932579) B3932579
theorem B13982501 : Blo 2151435 13982501 := bstep (se 4 (by rfl) ⟨1310859, by rfl⟩ : syracuseStep 13982501 = 2621719) B2621719
theorem B37286669 : Blo 2151435 37286669 := bstep (se 3 (by rfl) ⟨6991250, by rfl⟩ : syracuseStep 37286669 = 13982501) B13982501
theorem B24857779 : Blo 2151435 24857779 := bstep (se 1 (by rfl) ⟨18643334, by rfl⟩ : syracuseStep 24857779 = 37286669) B37286669
theorem B33143705 : Blo 2151435 33143705 := bstep (se 2 (by rfl) ⟨12428889, by rfl⟩ : syracuseStep 33143705 = 24857779) B24857779
theorem B22095803 : Blo 2151435 22095803 := bstep (se 1 (by rfl) ⟨16571852, by rfl⟩ : syracuseStep 22095803 = 33143705) B33143705
theorem B14730535 : Blo 2151435 14730535 := bstep (se 1 (by rfl) ⟨11047901, by rfl⟩ : syracuseStep 14730535 = 22095803) B22095803
theorem B19640713 : Blo 2151435 19640713 := bstep (se 2 (by rfl) ⟨7365267, by rfl⟩ : syracuseStep 19640713 = 14730535) B14730535
theorem B26187617 : Blo 2151435 26187617 := bstep (se 2 (by rfl) ⟨9820356, by rfl⟩ : syracuseStep 26187617 = 19640713) B19640713
theorem B17458411 : Blo 2151435 17458411 := bstep (se 1 (by rfl) ⟨13093808, by rfl⟩ : syracuseStep 17458411 = 26187617) B26187617
theorem B23277881 : Blo 2151435 23277881 := bstep (se 2 (by rfl) ⟨8729205, by rfl⟩ : syracuseStep 23277881 = 17458411) B17458411
theorem B15518587 : Blo 2151435 15518587 := bstep (se 1 (by rfl) ⟨11638940, by rfl⟩ : syracuseStep 15518587 = 23277881) B23277881
theorem B20691449 : Blo 2151435 20691449 := bstep (se 2 (by rfl) ⟨7759293, by rfl⟩ : syracuseStep 20691449 = 15518587) B15518587
theorem B13794299 : Blo 2151435 13794299 := bstep (se 1 (by rfl) ⟨10345724, by rfl⟩ : syracuseStep 13794299 = 20691449) B20691449
theorem B9196199 : Blo 2151435 9196199 := bstep (se 1 (by rfl) ⟨6897149, by rfl⟩ : syracuseStep 9196199 = 13794299) B13794299
theorem B6130799 : Blo 2151435 6130799 := bstep (se 1 (by rfl) ⟨4598099, by rfl⟩ : syracuseStep 6130799 = 9196199) B9196199
theorem B4087199 : Blo 2151435 4087199 := bstep (se 1 (by rfl) ⟨3065399, by rfl⟩ : syracuseStep 4087199 = 6130799) B6130799
theorem B10899197 : Blo 2151435 10899197 := bstep (se 3 (by rfl) ⟨2043599, by rfl⟩ : syracuseStep 10899197 = 4087199) B4087199
theorem B7266131 : Blo 2151435 7266131 := bstep (se 1 (by rfl) ⟨5449598, by rfl⟩ : syracuseStep 7266131 = 10899197) B10899197
theorem B4844087 : Blo 2151435 4844087 := bstep (se 1 (by rfl) ⟨3633065, by rfl⟩ : syracuseStep 4844087 = 7266131) B7266131
theorem B3229391 : Blo 2151435 3229391 := bstep (se 1 (by rfl) ⟨2422043, by rfl⟩ : syracuseStep 3229391 = 4844087) B4844087
theorem B2152927 : Blo 2151435 2152927 := bstep (se 1 (by rfl) ⟨1614695, by rfl⟩ : syracuseStep 2152927 = 3229391) B3229391
theorem B3229397 : Blo 2151435 3229397 := bbase (se 7 (by rfl) ⟨37844, by rfl⟩ : syracuseStep 3229397 = 75689) (by norm_num)
theorem B2152931 : Blo 2151435 2152931 := bstep (se 1 (by rfl) ⟨1614698, by rfl⟩ : syracuseStep 2152931 = 3229397) B3229397
theorem B4598117 : Blo 2151435 4598117 := bbase (se 4 (by rfl) ⟨431073, by rfl⟩ : syracuseStep 4598117 = 862147) (by norm_num)
theorem B3065411 : Blo 2151435 3065411 := bstep (se 1 (by rfl) ⟨2299058, by rfl⟩ : syracuseStep 3065411 = 4598117) B4598117
theorem B8174429 : Blo 2151435 8174429 := bstep (se 3 (by rfl) ⟨1532705, by rfl⟩ : syracuseStep 8174429 = 3065411) B3065411
theorem B5449619 : Blo 2151435 5449619 := bstep (se 1 (by rfl) ⟨4087214, by rfl⟩ : syracuseStep 5449619 = 8174429) B8174429
theorem B3633079 : Blo 2151435 3633079 := bstep (se 1 (by rfl) ⟨2724809, by rfl⟩ : syracuseStep 3633079 = 5449619) B5449619
theorem B4844105 : Blo 2151435 4844105 := bstep (se 2 (by rfl) ⟨1816539, by rfl⟩ : syracuseStep 4844105 = 3633079) B3633079
theorem B3229403 : Blo 2151435 3229403 := bstep (se 1 (by rfl) ⟨2422052, by rfl⟩ : syracuseStep 3229403 = 4844105) B4844105
theorem B2152935 : Blo 2151435 2152935 := bstep (se 1 (by rfl) ⟨1614701, by rfl⟩ : syracuseStep 2152935 = 3229403) B3229403
theorem B2422057 : Blo 2151435 2422057 := bbase (se 2 (by rfl) ⟨908271, by rfl⟩ : syracuseStep 2422057 = 1816543) (by norm_num)
theorem B3229409 : Blo 2151435 3229409 := bstep (se 2 (by rfl) ⟨1211028, by rfl⟩ : syracuseStep 3229409 = 2422057) B2422057
theorem B2152939 : Blo 2151435 2152939 := bstep (se 1 (by rfl) ⟨1614704, by rfl⟩ : syracuseStep 2152939 = 3229409) B3229409
theorem B8285989 : Blo 2151435 8285989 := bbase (se 4 (by rfl) ⟨776811, by rfl⟩ : syracuseStep 8285989 = 1553623) (by norm_num)
theorem B11047985 : Blo 2151435 11047985 := bstep (se 2 (by rfl) ⟨4142994, by rfl⟩ : syracuseStep 11047985 = 8285989) B8285989
theorem B7365323 : Blo 2151435 7365323 := bstep (se 1 (by rfl) ⟨5523992, by rfl⟩ : syracuseStep 7365323 = 11047985) B11047985
theorem B4910215 : Blo 2151435 4910215 := bstep (se 1 (by rfl) ⟨3682661, by rfl⟩ : syracuseStep 4910215 = 7365323) B7365323
theorem B6546953 : Blo 2151435 6546953 := bstep (se 2 (by rfl) ⟨2455107, by rfl⟩ : syracuseStep 6546953 = 4910215) B4910215
theorem B17458541 : Blo 2151435 17458541 := bstep (se 3 (by rfl) ⟨3273476, by rfl⟩ : syracuseStep 17458541 = 6546953) B6546953
theorem B11639027 : Blo 2151435 11639027 := bstep (se 1 (by rfl) ⟨8729270, by rfl⟩ : syracuseStep 11639027 = 17458541) B17458541
theorem B7759351 : Blo 2151435 7759351 := bstep (se 1 (by rfl) ⟨5819513, by rfl⟩ : syracuseStep 7759351 = 11639027) B11639027
theorem B10345801 : Blo 2151435 10345801 := bstep (se 2 (by rfl) ⟨3879675, by rfl⟩ : syracuseStep 10345801 = 7759351) B7759351
theorem B13794401 : Blo 2151435 13794401 := bstep (se 2 (by rfl) ⟨5172900, by rfl⟩ : syracuseStep 13794401 = 10345801) B10345801
theorem B9196267 : Blo 2151435 9196267 := bstep (se 1 (by rfl) ⟨6897200, by rfl⟩ : syracuseStep 9196267 = 13794401) B13794401
theorem B12261689 : Blo 2151435 12261689 := bstep (se 2 (by rfl) ⟨4598133, by rfl⟩ : syracuseStep 12261689 = 9196267) B9196267
theorem B8174459 : Blo 2151435 8174459 := bstep (se 1 (by rfl) ⟨6130844, by rfl⟩ : syracuseStep 8174459 = 12261689) B12261689
theorem B5449639 : Blo 2151435 5449639 := bstep (se 1 (by rfl) ⟨4087229, by rfl⟩ : syracuseStep 5449639 = 8174459) B8174459
theorem B7266185 : Blo 2151435 7266185 := bstep (se 2 (by rfl) ⟨2724819, by rfl⟩ : syracuseStep 7266185 = 5449639) B5449639
theorem B4844123 : Blo 2151435 4844123 := bstep (se 1 (by rfl) ⟨3633092, by rfl⟩ : syracuseStep 4844123 = 7266185) B7266185
theorem B3229415 : Blo 2151435 3229415 := bstep (se 1 (by rfl) ⟨2422061, by rfl⟩ : syracuseStep 3229415 = 4844123) B4844123
theorem B2152943 : Blo 2151435 2152943 := bstep (se 1 (by rfl) ⟨1614707, by rfl⟩ : syracuseStep 2152943 = 3229415) B3229415
theorem B3229421 : Blo 2151435 3229421 := bbase (se 3 (by rfl) ⟨605516, by rfl⟩ : syracuseStep 3229421 = 1211033) (by norm_num)
theorem B2152947 : Blo 2151435 2152947 := bstep (se 1 (by rfl) ⟨1614710, by rfl⟩ : syracuseStep 2152947 = 3229421) B3229421
theorem B4844141 : Blo 2151435 4844141 := bbase (se 3 (by rfl) ⟨908276, by rfl⟩ : syracuseStep 4844141 = 1816553) (by norm_num)
theorem B3229427 : Blo 2151435 3229427 := bstep (se 1 (by rfl) ⟨2422070, by rfl⟩ : syracuseStep 3229427 = 4844141) B4844141
theorem B2152951 : Blo 2151435 2152951 := bstep (se 1 (by rfl) ⟨1614713, by rfl⟩ : syracuseStep 2152951 = 3229427) B3229427
theorem B4087253 : Blo 2151435 4087253 := bbase (se 7 (by rfl) ⟨47897, by rfl⟩ : syracuseStep 4087253 = 95795) (by norm_num)
theorem B2724835 : Blo 2151435 2724835 := bstep (se 1 (by rfl) ⟨2043626, by rfl⟩ : syracuseStep 2724835 = 4087253) B4087253
theorem B3633113 : Blo 2151435 3633113 := bstep (se 2 (by rfl) ⟨1362417, by rfl⟩ : syracuseStep 3633113 = 2724835) B2724835
theorem B2422075 : Blo 2151435 2422075 := bstep (se 1 (by rfl) ⟨1816556, by rfl⟩ : syracuseStep 2422075 = 3633113) B3633113
theorem B3229433 : Blo 2151435 3229433 := bstep (se 2 (by rfl) ⟨1211037, by rfl⟩ : syracuseStep 3229433 = 2422075) B2422075
theorem B2152955 : Blo 2151435 2152955 := bstep (se 1 (by rfl) ⟨1614716, by rfl⟩ : syracuseStep 2152955 = 3229433) B3229433
theorem B5045149 : Blo 2151435 5045149 := bbase (se 3 (by rfl) ⟨945965, by rfl⟩ : syracuseStep 5045149 = 1891931) (by norm_num)
theorem B6726865 : Blo 2151435 6726865 := bstep (se 2 (by rfl) ⟨2522574, by rfl⟩ : syracuseStep 6726865 = 5045149) B5045149
theorem B8969153 : Blo 2151435 8969153 := bstep (se 2 (by rfl) ⟨3363432, by rfl⟩ : syracuseStep 8969153 = 6726865) B6726865
theorem B95670965 : Blo 2151435 95670965 := bstep (se 5 (by rfl) ⟨4484576, by rfl⟩ : syracuseStep 95670965 = 8969153) B8969153
theorem B63780643 : Blo 2151435 63780643 := bstep (se 1 (by rfl) ⟨47835482, by rfl⟩ : syracuseStep 63780643 = 95670965) B95670965
theorem B85040857 : Blo 2151435 85040857 := bstep (se 2 (by rfl) ⟨31890321, by rfl⟩ : syracuseStep 85040857 = 63780643) B63780643
theorem B453551237 : Blo 2151435 453551237 := bstep (se 4 (by rfl) ⟨42520428, by rfl⟩ : syracuseStep 453551237 = 85040857) B85040857
theorem B302367491 : Blo 2151435 302367491 := bstep (se 1 (by rfl) ⟨226775618, by rfl⟩ : syracuseStep 302367491 = 453551237) B453551237
theorem B201578327 : Blo 2151435 201578327 := bstep (se 1 (by rfl) ⟨151183745, by rfl⟩ : syracuseStep 201578327 = 302367491) B302367491
theorem B134385551 : Blo 2151435 134385551 := bstep (se 1 (by rfl) ⟨100789163, by rfl⟩ : syracuseStep 134385551 = 201578327) B201578327
theorem B89590367 : Blo 2151435 89590367 := bstep (se 1 (by rfl) ⟨67192775, by rfl⟩ : syracuseStep 89590367 = 134385551) B134385551
theorem B59726911 : Blo 2151435 59726911 := bstep (se 1 (by rfl) ⟨44795183, by rfl⟩ : syracuseStep 59726911 = 89590367) B89590367
theorem B79635881 : Blo 2151435 79635881 := bstep (se 2 (by rfl) ⟨29863455, by rfl⟩ : syracuseStep 79635881 = 59726911) B59726911
theorem B53090587 : Blo 2151435 53090587 := bstep (se 1 (by rfl) ⟨39817940, by rfl⟩ : syracuseStep 53090587 = 79635881) B79635881
theorem B70787449 : Blo 2151435 70787449 := bstep (se 2 (by rfl) ⟨26545293, by rfl⟩ : syracuseStep 70787449 = 53090587) B53090587
theorem B377533061 : Blo 2151435 377533061 := bstep (se 4 (by rfl) ⟨35393724, by rfl⟩ : syracuseStep 377533061 = 70787449) B70787449
theorem B251688707 : Blo 2151435 251688707 := bstep (se 1 (by rfl) ⟨188766530, by rfl⟩ : syracuseStep 251688707 = 377533061) B377533061
theorem B167792471 : Blo 2151435 167792471 := bstep (se 1 (by rfl) ⟨125844353, by rfl⟩ : syracuseStep 167792471 = 251688707) B251688707
theorem B111861647 : Blo 2151435 111861647 := bstep (se 1 (by rfl) ⟨83896235, by rfl⟩ : syracuseStep 111861647 = 167792471) B167792471
theorem B74574431 : Blo 2151435 74574431 := bstep (se 1 (by rfl) ⟨55930823, by rfl⟩ : syracuseStep 74574431 = 111861647) B111861647
theorem B49716287 : Blo 2151435 49716287 := bstep (se 1 (by rfl) ⟨37287215, by rfl⟩ : syracuseStep 49716287 = 74574431) B74574431
theorem B33144191 : Blo 2151435 33144191 := bstep (se 1 (by rfl) ⟨24858143, by rfl⟩ : syracuseStep 33144191 = 49716287) B49716287
theorem B22096127 : Blo 2151435 22096127 := bstep (se 1 (by rfl) ⟨16572095, by rfl⟩ : syracuseStep 22096127 = 33144191) B33144191
theorem B14730751 : Blo 2151435 14730751 := bstep (se 1 (by rfl) ⟨11048063, by rfl⟩ : syracuseStep 14730751 = 22096127) B22096127
theorem B78564005 : Blo 2151435 78564005 := bstep (se 4 (by rfl) ⟨7365375, by rfl⟩ : syracuseStep 78564005 = 14730751) B14730751
theorem B52376003 : Blo 2151435 52376003 := bstep (se 1 (by rfl) ⟨39282002, by rfl⟩ : syracuseStep 52376003 = 78564005) B78564005
theorem B34917335 : Blo 2151435 34917335 := bstep (se 1 (by rfl) ⟨26188001, by rfl⟩ : syracuseStep 34917335 = 52376003) B52376003
theorem B23278223 : Blo 2151435 23278223 := bstep (se 1 (by rfl) ⟨17458667, by rfl⟩ : syracuseStep 23278223 = 34917335) B34917335
theorem B62075261 : Blo 2151435 62075261 := bstep (se 3 (by rfl) ⟨11639111, by rfl⟩ : syracuseStep 62075261 = 23278223) B23278223
theorem B41383507 : Blo 2151435 41383507 := bstep (se 1 (by rfl) ⟨31037630, by rfl⟩ : syracuseStep 41383507 = 62075261) B62075261
theorem B55178009 : Blo 2151435 55178009 := bstep (se 2 (by rfl) ⟨20691753, by rfl⟩ : syracuseStep 55178009 = 41383507) B41383507
theorem B36785339 : Blo 2151435 36785339 := bstep (se 1 (by rfl) ⟨27589004, by rfl⟩ : syracuseStep 36785339 = 55178009) B55178009
theorem B24523559 : Blo 2151435 24523559 := bstep (se 1 (by rfl) ⟨18392669, by rfl⟩ : syracuseStep 24523559 = 36785339) B36785339
theorem B16349039 : Blo 2151435 16349039 := bstep (se 1 (by rfl) ⟨12261779, by rfl⟩ : syracuseStep 16349039 = 24523559) B24523559
theorem B10899359 : Blo 2151435 10899359 := bstep (se 1 (by rfl) ⟨8174519, by rfl⟩ : syracuseStep 10899359 = 16349039) B16349039
theorem B7266239 : Blo 2151435 7266239 := bstep (se 1 (by rfl) ⟨5449679, by rfl⟩ : syracuseStep 7266239 = 10899359) B10899359
theorem B4844159 : Blo 2151435 4844159 := bstep (se 1 (by rfl) ⟨3633119, by rfl⟩ : syracuseStep 4844159 = 7266239) B7266239
theorem B3229439 : Blo 2151435 3229439 := bstep (se 1 (by rfl) ⟨2422079, by rfl⟩ : syracuseStep 3229439 = 4844159) B4844159
theorem B2152959 : Blo 2151435 2152959 := bstep (se 1 (by rfl) ⟨1614719, by rfl⟩ : syracuseStep 2152959 = 3229439) B3229439
theorem B3229445 : Blo 2151435 3229445 := bbase (se 4 (by rfl) ⟨302760, by rfl⟩ : syracuseStep 3229445 = 605521) (by norm_num)
theorem B2152963 : Blo 2151435 2152963 := bstep (se 1 (by rfl) ⟨1614722, by rfl⟩ : syracuseStep 2152963 = 3229445) B3229445
theorem B3633133 : Blo 2151435 3633133 := bbase (se 3 (by rfl) ⟨681212, by rfl⟩ : syracuseStep 3633133 = 1362425) (by norm_num)
theorem B4844177 : Blo 2151435 4844177 := bstep (se 2 (by rfl) ⟨1816566, by rfl⟩ : syracuseStep 4844177 = 3633133) B3633133
theorem B3229451 : Blo 2151435 3229451 := bstep (se 1 (by rfl) ⟨2422088, by rfl⟩ : syracuseStep 3229451 = 4844177) B4844177
theorem B2152967 : Blo 2151435 2152967 := bstep (se 1 (by rfl) ⟨1614725, by rfl⟩ : syracuseStep 2152967 = 3229451) B3229451
theorem B2422093 : Blo 2151435 2422093 := bbase (se 3 (by rfl) ⟨454142, by rfl⟩ : syracuseStep 2422093 = 908285) (by norm_num)
theorem B3229457 : Blo 2151435 3229457 := bstep (se 2 (by rfl) ⟨1211046, by rfl⟩ : syracuseStep 3229457 = 2422093) B2422093
theorem B2152971 : Blo 2151435 2152971 := bstep (se 1 (by rfl) ⟨1614728, by rfl⟩ : syracuseStep 2152971 = 3229457) B3229457
theorem B7266293 : Blo 2151435 7266293 := bbase (se 5 (by rfl) ⟨340607, by rfl⟩ : syracuseStep 7266293 = 681215) (by norm_num)
theorem B4844195 : Blo 2151435 4844195 := bstep (se 1 (by rfl) ⟨3633146, by rfl⟩ : syracuseStep 4844195 = 7266293) B7266293
theorem B3229463 : Blo 2151435 3229463 := bstep (se 1 (by rfl) ⟨2422097, by rfl⟩ : syracuseStep 3229463 = 4844195) B4844195
theorem B2152975 : Blo 2151435 2152975 := bstep (se 1 (by rfl) ⟨1614731, by rfl⟩ : syracuseStep 2152975 = 3229463) B3229463
theorem B3229469 : Blo 2151435 3229469 := bbase (se 3 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 3229469 = 1211051) (by norm_num)
theorem B2152979 : Blo 2151435 2152979 := bstep (se 1 (by rfl) ⟨1614734, by rfl⟩ : syracuseStep 2152979 = 3229469) B3229469
theorem B4844213 : Blo 2151435 4844213 := bbase (se 5 (by rfl) ⟨227072, by rfl⟩ : syracuseStep 4844213 = 454145) (by norm_num)
theorem B3229475 : Blo 2151435 3229475 := bstep (se 1 (by rfl) ⟨2422106, by rfl⟩ : syracuseStep 3229475 = 4844213) B4844213
theorem B2152983 : Blo 2151435 2152983 := bstep (se 1 (by rfl) ⟨1614737, by rfl⟩ : syracuseStep 2152983 = 3229475) B3229475
theorem B12261941 : Blo 2151435 12261941 := bbase (se 5 (by rfl) ⟨574778, by rfl⟩ : syracuseStep 12261941 = 1149557) (by norm_num)
theorem B8174627 : Blo 2151435 8174627 := bstep (se 1 (by rfl) ⟨6130970, by rfl⟩ : syracuseStep 8174627 = 12261941) B12261941
theorem B5449751 : Blo 2151435 5449751 := bstep (se 1 (by rfl) ⟨4087313, by rfl⟩ : syracuseStep 5449751 = 8174627) B8174627
theorem B3633167 : Blo 2151435 3633167 := bstep (se 1 (by rfl) ⟨2724875, by rfl⟩ : syracuseStep 3633167 = 5449751) B5449751
theorem B2422111 : Blo 2151435 2422111 := bstep (se 1 (by rfl) ⟨1816583, by rfl⟩ : syracuseStep 2422111 = 3633167) B3633167
theorem B3229481 : Blo 2151435 3229481 := bstep (se 2 (by rfl) ⟨1211055, by rfl⟩ : syracuseStep 3229481 = 2422111) B2422111
theorem B2152987 : Blo 2151435 2152987 := bstep (se 1 (by rfl) ⟨1614740, by rfl⟩ : syracuseStep 2152987 = 3229481) B3229481
theorem B6130981 : Blo 2151435 6130981 := bbase (se 4 (by rfl) ⟨574779, by rfl⟩ : syracuseStep 6130981 = 1149559) (by norm_num)
theorem B8174641 : Blo 2151435 8174641 := bstep (se 2 (by rfl) ⟨3065490, by rfl⟩ : syracuseStep 8174641 = 6130981) B6130981
theorem B10899521 : Blo 2151435 10899521 := bstep (se 2 (by rfl) ⟨4087320, by rfl⟩ : syracuseStep 10899521 = 8174641) B8174641
theorem B7266347 : Blo 2151435 7266347 := bstep (se 1 (by rfl) ⟨5449760, by rfl⟩ : syracuseStep 7266347 = 10899521) B10899521
theorem B4844231 : Blo 2151435 4844231 := bstep (se 1 (by rfl) ⟨3633173, by rfl⟩ : syracuseStep 4844231 = 7266347) B7266347
theorem B3229487 : Blo 2151435 3229487 := bstep (se 1 (by rfl) ⟨2422115, by rfl⟩ : syracuseStep 3229487 = 4844231) B4844231
theorem B2152991 : Blo 2151435 2152991 := bstep (se 1 (by rfl) ⟨1614743, by rfl⟩ : syracuseStep 2152991 = 3229487) B3229487
theorem B3229493 : Blo 2151435 3229493 := bbase (se 5 (by rfl) ⟨151382, by rfl⟩ : syracuseStep 3229493 = 302765) (by norm_num)
theorem B2152995 : Blo 2151435 2152995 := bstep (se 1 (by rfl) ⟨1614746, by rfl⟩ : syracuseStep 2152995 = 3229493) B3229493
theorem B5449781 : Blo 2151435 5449781 := bbase (se 5 (by rfl) ⟨255458, by rfl⟩ : syracuseStep 5449781 = 510917) (by norm_num)
theorem B3633187 : Blo 2151435 3633187 := bstep (se 1 (by rfl) ⟨2724890, by rfl⟩ : syracuseStep 3633187 = 5449781) B5449781
theorem B4844249 : Blo 2151435 4844249 := bstep (se 2 (by rfl) ⟨1816593, by rfl⟩ : syracuseStep 4844249 = 3633187) B3633187
theorem B3229499 : Blo 2151435 3229499 := bstep (se 1 (by rfl) ⟨2422124, by rfl⟩ : syracuseStep 3229499 = 4844249) B4844249
theorem B2152999 : Blo 2151435 2152999 := bstep (se 1 (by rfl) ⟨1614749, by rfl⟩ : syracuseStep 2152999 = 3229499) B3229499
theorem B2422129 : Blo 2151435 2422129 := bbase (se 2 (by rfl) ⟨908298, by rfl⟩ : syracuseStep 2422129 = 1816597) (by norm_num)
theorem B3229505 : Blo 2151435 3229505 := bstep (se 2 (by rfl) ⟨1211064, by rfl⟩ : syracuseStep 3229505 = 2422129) B2422129
theorem B2153003 : Blo 2151435 2153003 := bstep (se 1 (by rfl) ⟨1614752, by rfl⟩ : syracuseStep 2153003 = 3229505) B3229505
theorem B5524157 : Blo 2151435 5524157 := bbase (se 3 (by rfl) ⟨1035779, by rfl⟩ : syracuseStep 5524157 = 2071559) (by norm_num)
theorem B14731085 : Blo 2151435 14731085 := bstep (se 3 (by rfl) ⟨2762078, by rfl⟩ : syracuseStep 14731085 = 5524157) B5524157
theorem B39282893 : Blo 2151435 39282893 := bstep (se 3 (by rfl) ⟨7365542, by rfl⟩ : syracuseStep 39282893 = 14731085) B14731085
theorem B26188595 : Blo 2151435 26188595 := bstep (se 1 (by rfl) ⟨19641446, by rfl⟩ : syracuseStep 26188595 = 39282893) B39282893
theorem B17459063 : Blo 2151435 17459063 := bstep (se 1 (by rfl) ⟨13094297, by rfl⟩ : syracuseStep 17459063 = 26188595) B26188595
theorem B11639375 : Blo 2151435 11639375 := bstep (se 1 (by rfl) ⟨8729531, by rfl⟩ : syracuseStep 11639375 = 17459063) B17459063
theorem B7759583 : Blo 2151435 7759583 := bstep (se 1 (by rfl) ⟨5819687, by rfl⟩ : syracuseStep 7759583 = 11639375) B11639375
theorem B5173055 : Blo 2151435 5173055 := bstep (se 1 (by rfl) ⟨3879791, by rfl⟩ : syracuseStep 5173055 = 7759583) B7759583
theorem B3448703 : Blo 2151435 3448703 := bstep (se 1 (by rfl) ⟨2586527, by rfl⟩ : syracuseStep 3448703 = 5173055) B5173055
theorem B9196541 : Blo 2151435 9196541 := bstep (se 3 (by rfl) ⟨1724351, by rfl⟩ : syracuseStep 9196541 = 3448703) B3448703
theorem B6131027 : Blo 2151435 6131027 := bstep (se 1 (by rfl) ⟨4598270, by rfl⟩ : syracuseStep 6131027 = 9196541) B9196541
theorem B4087351 : Blo 2151435 4087351 := bstep (se 1 (by rfl) ⟨3065513, by rfl⟩ : syracuseStep 4087351 = 6131027) B6131027
theorem B5449801 : Blo 2151435 5449801 := bstep (se 2 (by rfl) ⟨2043675, by rfl⟩ : syracuseStep 5449801 = 4087351) B4087351
theorem B7266401 : Blo 2151435 7266401 := bstep (se 2 (by rfl) ⟨2724900, by rfl⟩ : syracuseStep 7266401 = 5449801) B5449801
theorem B4844267 : Blo 2151435 4844267 := bstep (se 1 (by rfl) ⟨3633200, by rfl⟩ : syracuseStep 4844267 = 7266401) B7266401
theorem B3229511 : Blo 2151435 3229511 := bstep (se 1 (by rfl) ⟨2422133, by rfl⟩ : syracuseStep 3229511 = 4844267) B4844267
theorem B2153007 : Blo 2151435 2153007 := bstep (se 1 (by rfl) ⟨1614755, by rfl⟩ : syracuseStep 2153007 = 3229511) B3229511
theorem B3229517 : Blo 2151435 3229517 := bbase (se 3 (by rfl) ⟨605534, by rfl⟩ : syracuseStep 3229517 = 1211069) (by norm_num)
theorem B2153011 : Blo 2151435 2153011 := bstep (se 1 (by rfl) ⟨1614758, by rfl⟩ : syracuseStep 2153011 = 3229517) B3229517
theorem B4844285 : Blo 2151435 4844285 := bbase (se 3 (by rfl) ⟨908303, by rfl⟩ : syracuseStep 4844285 = 1816607) (by norm_num)
theorem B3229523 : Blo 2151435 3229523 := bstep (se 1 (by rfl) ⟨2422142, by rfl⟩ : syracuseStep 3229523 = 4844285) B4844285
theorem B2153015 : Blo 2151435 2153015 := bstep (se 1 (by rfl) ⟨1614761, by rfl⟩ : syracuseStep 2153015 = 3229523) B3229523
theorem B3633221 : Blo 2151435 3633221 := bbase (se 4 (by rfl) ⟨340614, by rfl⟩ : syracuseStep 3633221 = 681229) (by norm_num)
theorem B2422147 : Blo 2151435 2422147 := bstep (se 1 (by rfl) ⟨1816610, by rfl⟩ : syracuseStep 2422147 = 3633221) B3633221
theorem B3229529 : Blo 2151435 3229529 := bstep (se 2 (by rfl) ⟨1211073, by rfl⟩ : syracuseStep 3229529 = 2422147) B2422147
theorem B2153019 : Blo 2151435 2153019 := bstep (se 1 (by rfl) ⟨1614764, by rfl⟩ : syracuseStep 2153019 = 3229529) B3229529
theorem B16349525 : Blo 2151435 16349525 := bbase (se 10 (by rfl) ⟨23949, by rfl⟩ : syracuseStep 16349525 = 47899) (by norm_num)
theorem B10899683 : Blo 2151435 10899683 := bstep (se 1 (by rfl) ⟨8174762, by rfl⟩ : syracuseStep 10899683 = 16349525) B16349525
theorem B7266455 : Blo 2151435 7266455 := bstep (se 1 (by rfl) ⟨5449841, by rfl⟩ : syracuseStep 7266455 = 10899683) B10899683
theorem B4844303 : Blo 2151435 4844303 := bstep (se 1 (by rfl) ⟨3633227, by rfl⟩ : syracuseStep 4844303 = 7266455) B7266455
theorem B3229535 : Blo 2151435 3229535 := bstep (se 1 (by rfl) ⟨2422151, by rfl⟩ : syracuseStep 3229535 = 4844303) B4844303
theorem B2153023 : Blo 2151435 2153023 := bstep (se 1 (by rfl) ⟨1614767, by rfl⟩ : syracuseStep 2153023 = 3229535) B3229535
theorem B3229541 : Blo 2151435 3229541 := bbase (se 4 (by rfl) ⟨302769, by rfl⟩ : syracuseStep 3229541 = 605539) (by norm_num)
theorem B2153027 : Blo 2151435 2153027 := bstep (se 1 (by rfl) ⟨1614770, by rfl⟩ : syracuseStep 2153027 = 3229541) B3229541
theorem B4087397 : Blo 2151435 4087397 := bbase (se 4 (by rfl) ⟨383193, by rfl⟩ : syracuseStep 4087397 = 766387) (by norm_num)
theorem B2724931 : Blo 2151435 2724931 := bstep (se 1 (by rfl) ⟨2043698, by rfl⟩ : syracuseStep 2724931 = 4087397) B4087397
theorem B3633241 : Blo 2151435 3633241 := bstep (se 2 (by rfl) ⟨1362465, by rfl⟩ : syracuseStep 3633241 = 2724931) B2724931
theorem B4844321 : Blo 2151435 4844321 := bstep (se 2 (by rfl) ⟨1816620, by rfl⟩ : syracuseStep 4844321 = 3633241) B3633241
theorem B3229547 : Blo 2151435 3229547 := bstep (se 1 (by rfl) ⟨2422160, by rfl⟩ : syracuseStep 3229547 = 4844321) B4844321
theorem B2153031 : Blo 2151435 2153031 := bstep (se 1 (by rfl) ⟨1614773, by rfl⟩ : syracuseStep 2153031 = 3229547) B3229547
theorem B2422165 : Blo 2151435 2422165 := bbase (se 6 (by rfl) ⟨56769, by rfl⟩ : syracuseStep 2422165 = 113539) (by norm_num)
theorem B3229553 : Blo 2151435 3229553 := bstep (se 2 (by rfl) ⟨1211082, by rfl⟩ : syracuseStep 3229553 = 2422165) B2422165
theorem B2153035 : Blo 2151435 2153035 := bstep (se 1 (by rfl) ⟨1614776, by rfl⟩ : syracuseStep 2153035 = 3229553) B3229553
theorem B2724941 : Blo 2151435 2724941 := bbase (se 3 (by rfl) ⟨510926, by rfl⟩ : syracuseStep 2724941 = 1021853) (by norm_num)
theorem B7266509 : Blo 2151435 7266509 := bstep (se 3 (by rfl) ⟨1362470, by rfl⟩ : syracuseStep 7266509 = 2724941) B2724941
theorem B4844339 : Blo 2151435 4844339 := bstep (se 1 (by rfl) ⟨3633254, by rfl⟩ : syracuseStep 4844339 = 7266509) B7266509
theorem B3229559 : Blo 2151435 3229559 := bstep (se 1 (by rfl) ⟨2422169, by rfl⟩ : syracuseStep 3229559 = 4844339) B4844339
theorem B2153039 : Blo 2151435 2153039 := bstep (se 1 (by rfl) ⟨1614779, by rfl⟩ : syracuseStep 2153039 = 3229559) B3229559
theorem B3229565 : Blo 2151435 3229565 := bbase (se 3 (by rfl) ⟨605543, by rfl⟩ : syracuseStep 3229565 = 1211087) (by norm_num)
theorem B2153043 : Blo 2151435 2153043 := bstep (se 1 (by rfl) ⟨1614782, by rfl⟩ : syracuseStep 2153043 = 3229565) B3229565
theorem B4844357 : Blo 2151435 4844357 := bbase (se 4 (by rfl) ⟨454158, by rfl⟩ : syracuseStep 4844357 = 908317) (by norm_num)
theorem B3229571 : Blo 2151435 3229571 := bstep (se 1 (by rfl) ⟨2422178, by rfl⟩ : syracuseStep 3229571 = 4844357) B4844357
theorem B2153047 : Blo 2151435 2153047 := bstep (se 1 (by rfl) ⟨1614785, by rfl⟩ : syracuseStep 2153047 = 3229571) B3229571
theorem B4598365 : Blo 2151435 4598365 := bbase (se 3 (by rfl) ⟨862193, by rfl⟩ : syracuseStep 4598365 = 1724387) (by norm_num)
theorem B6131153 : Blo 2151435 6131153 := bstep (se 2 (by rfl) ⟨2299182, by rfl⟩ : syracuseStep 6131153 = 4598365) B4598365
theorem B4087435 : Blo 2151435 4087435 := bstep (se 1 (by rfl) ⟨3065576, by rfl⟩ : syracuseStep 4087435 = 6131153) B6131153
theorem B5449913 : Blo 2151435 5449913 := bstep (se 2 (by rfl) ⟨2043717, by rfl⟩ : syracuseStep 5449913 = 4087435) B4087435
theorem B3633275 : Blo 2151435 3633275 := bstep (se 1 (by rfl) ⟨2724956, by rfl⟩ : syracuseStep 3633275 = 5449913) B5449913
theorem B2422183 : Blo 2151435 2422183 := bstep (se 1 (by rfl) ⟨1816637, by rfl⟩ : syracuseStep 2422183 = 3633275) B3633275
theorem B3229577 : Blo 2151435 3229577 := bstep (se 2 (by rfl) ⟨1211091, by rfl⟩ : syracuseStep 3229577 = 2422183) B2422183
theorem B2153051 : Blo 2151435 2153051 := bstep (se 1 (by rfl) ⟨1614788, by rfl⟩ : syracuseStep 2153051 = 3229577) B3229577
theorem B10899845 : Blo 2151435 10899845 := bbase (se 4 (by rfl) ⟨1021860, by rfl⟩ : syracuseStep 10899845 = 2043721) (by norm_num)
theorem B7266563 : Blo 2151435 7266563 := bstep (se 1 (by rfl) ⟨5449922, by rfl⟩ : syracuseStep 7266563 = 10899845) B10899845
theorem B4844375 : Blo 2151435 4844375 := bstep (se 1 (by rfl) ⟨3633281, by rfl⟩ : syracuseStep 4844375 = 7266563) B7266563
theorem B3229583 : Blo 2151435 3229583 := bstep (se 1 (by rfl) ⟨2422187, by rfl⟩ : syracuseStep 3229583 = 4844375) B4844375
theorem B2153055 : Blo 2151435 2153055 := bstep (se 1 (by rfl) ⟨1614791, by rfl⟩ : syracuseStep 2153055 = 3229583) B3229583
theorem B3229589 : Blo 2151435 3229589 := bbase (se 6 (by rfl) ⟨75693, by rfl⟩ : syracuseStep 3229589 = 151387) (by norm_num)
theorem B2153059 : Blo 2151435 2153059 := bstep (se 1 (by rfl) ⟨1614794, by rfl⟩ : syracuseStep 2153059 = 3229589) B3229589
theorem B3879893 : Blo 2151435 3879893 := bbase (se 7 (by rfl) ⟨45467, by rfl⟩ : syracuseStep 3879893 = 90935) (by norm_num)
theorem B2586595 : Blo 2151435 2586595 := bstep (se 1 (by rfl) ⟨1939946, by rfl⟩ : syracuseStep 2586595 = 3879893) B3879893
theorem B3448793 : Blo 2151435 3448793 := bstep (se 2 (by rfl) ⟨1293297, by rfl⟩ : syracuseStep 3448793 = 2586595) B2586595
theorem B2299195 : Blo 2151435 2299195 := bstep (se 1 (by rfl) ⟨1724396, by rfl⟩ : syracuseStep 2299195 = 3448793) B3448793
theorem B12262373 : Blo 2151435 12262373 := bstep (se 4 (by rfl) ⟨1149597, by rfl⟩ : syracuseStep 12262373 = 2299195) B2299195
theorem B8174915 : Blo 2151435 8174915 := bstep (se 1 (by rfl) ⟨6131186, by rfl⟩ : syracuseStep 8174915 = 12262373) B12262373
theorem B5449943 : Blo 2151435 5449943 := bstep (se 1 (by rfl) ⟨4087457, by rfl⟩ : syracuseStep 5449943 = 8174915) B8174915
theorem B3633295 : Blo 2151435 3633295 := bstep (se 1 (by rfl) ⟨2724971, by rfl⟩ : syracuseStep 3633295 = 5449943) B5449943
theorem B4844393 : Blo 2151435 4844393 := bstep (se 2 (by rfl) ⟨1816647, by rfl⟩ : syracuseStep 4844393 = 3633295) B3633295
theorem B3229595 : Blo 2151435 3229595 := bstep (se 1 (by rfl) ⟨2422196, by rfl⟩ : syracuseStep 3229595 = 4844393) B4844393
theorem B2153063 : Blo 2151435 2153063 := bstep (se 1 (by rfl) ⟨1614797, by rfl⟩ : syracuseStep 2153063 = 3229595) B3229595
theorem B2422201 : Blo 2151435 2422201 := bbase (se 2 (by rfl) ⟨908325, by rfl⟩ : syracuseStep 2422201 = 1816651) (by norm_num)
theorem B3229601 : Blo 2151435 3229601 := bstep (se 2 (by rfl) ⟨1211100, by rfl⟩ : syracuseStep 3229601 = 2422201) B2422201
theorem B2153067 : Blo 2151435 2153067 := bstep (se 1 (by rfl) ⟨1614800, by rfl⟩ : syracuseStep 2153067 = 3229601) B3229601
theorem B7759813 : Blo 2151435 7759813 := bbase (se 4 (by rfl) ⟨727482, by rfl⟩ : syracuseStep 7759813 = 1454965) (by norm_num)
theorem B10346417 : Blo 2151435 10346417 := bstep (se 2 (by rfl) ⟨3879906, by rfl⟩ : syracuseStep 10346417 = 7759813) B7759813
theorem B6897611 : Blo 2151435 6897611 := bstep (se 1 (by rfl) ⟨5173208, by rfl⟩ : syracuseStep 6897611 = 10346417) B10346417
theorem B4598407 : Blo 2151435 4598407 := bstep (se 1 (by rfl) ⟨3448805, by rfl⟩ : syracuseStep 4598407 = 6897611) B6897611
theorem B6131209 : Blo 2151435 6131209 := bstep (se 2 (by rfl) ⟨2299203, by rfl⟩ : syracuseStep 6131209 = 4598407) B4598407
theorem B8174945 : Blo 2151435 8174945 := bstep (se 2 (by rfl) ⟨3065604, by rfl⟩ : syracuseStep 8174945 = 6131209) B6131209
theorem B5449963 : Blo 2151435 5449963 := bstep (se 1 (by rfl) ⟨4087472, by rfl⟩ : syracuseStep 5449963 = 8174945) B8174945
theorem B7266617 : Blo 2151435 7266617 := bstep (se 2 (by rfl) ⟨2724981, by rfl⟩ : syracuseStep 7266617 = 5449963) B5449963
theorem B4844411 : Blo 2151435 4844411 := bstep (se 1 (by rfl) ⟨3633308, by rfl⟩ : syracuseStep 4844411 = 7266617) B7266617
theorem B3229607 : Blo 2151435 3229607 := bstep (se 1 (by rfl) ⟨2422205, by rfl⟩ : syracuseStep 3229607 = 4844411) B4844411
theorem B2153071 : Blo 2151435 2153071 := bstep (se 1 (by rfl) ⟨1614803, by rfl⟩ : syracuseStep 2153071 = 3229607) B3229607
theorem B3229613 : Blo 2151435 3229613 := bbase (se 3 (by rfl) ⟨605552, by rfl⟩ : syracuseStep 3229613 = 1211105) (by norm_num)
theorem B2153075 : Blo 2151435 2153075 := bstep (se 1 (by rfl) ⟨1614806, by rfl⟩ : syracuseStep 2153075 = 3229613) B3229613
theorem B4844429 : Blo 2151435 4844429 := bbase (se 3 (by rfl) ⟨908330, by rfl⟩ : syracuseStep 4844429 = 1816661) (by norm_num)
theorem B3229619 : Blo 2151435 3229619 := bstep (se 1 (by rfl) ⟨2422214, by rfl⟩ : syracuseStep 3229619 = 4844429) B4844429
theorem B2153079 : Blo 2151435 2153079 := bstep (se 1 (by rfl) ⟨1614809, by rfl⟩ : syracuseStep 2153079 = 3229619) B3229619
theorem B2724997 : Blo 2151435 2724997 := bbase (se 4 (by rfl) ⟨255468, by rfl⟩ : syracuseStep 2724997 = 510937) (by norm_num)
theorem B3633329 : Blo 2151435 3633329 := bstep (se 2 (by rfl) ⟨1362498, by rfl⟩ : syracuseStep 3633329 = 2724997) B2724997
theorem B2422219 : Blo 2151435 2422219 := bstep (se 1 (by rfl) ⟨1816664, by rfl⟩ : syracuseStep 2422219 = 3633329) B3633329
theorem B3229625 : Blo 2151435 3229625 := bstep (se 2 (by rfl) ⟨1211109, by rfl⟩ : syracuseStep 3229625 = 2422219) B2422219
theorem B2153083 : Blo 2151435 2153083 := bstep (se 1 (by rfl) ⟨1614812, by rfl⟩ : syracuseStep 2153083 = 3229625) B3229625
theorem B55934165 : Blo 2151435 55934165 := bbase (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) (by norm_num)
theorem B149157773 : Blo 2151435 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B99438515 : Blo 2151435 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B66292343 : Blo 2151435 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B44194895 : Blo 2151435 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B29463263 : Blo 2151435 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B19642175 : Blo 2151435 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B13094783 : Blo 2151435 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B8729855 : Blo 2151435 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B5819903 : Blo 2151435 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B3879935 : Blo 2151435 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B2586623 : Blo 2151435 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B27590645 : Blo 2151435 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B18393763 : Blo 2151435 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B24525017 : Blo 2151435 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B16350011 : Blo 2151435 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B10900007 : Blo 2151435 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B7266671 : Blo 2151435 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B4844447 : Blo 2151435 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B3229631 : Blo 2151435 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B2153087 : Blo 2151435 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B3229637 : Blo 2151435 3229637 := bbase (se 4 (by rfl) ⟨302778, by rfl⟩ : syracuseStep 3229637 = 605557) (by norm_num)
theorem B2153091 : Blo 2151435 2153091 := bstep (se 1 (by rfl) ⟨1614818, by rfl⟩ : syracuseStep 2153091 = 3229637) B3229637
theorem B3633349 : Blo 2151435 3633349 := bbase (se 4 (by rfl) ⟨340626, by rfl⟩ : syracuseStep 3633349 = 681253) (by norm_num)
theorem B4844465 : Blo 2151435 4844465 := bstep (se 2 (by rfl) ⟨1816674, by rfl⟩ : syracuseStep 4844465 = 3633349) B3633349
theorem B3229643 : Blo 2151435 3229643 := bstep (se 1 (by rfl) ⟨2422232, by rfl⟩ : syracuseStep 3229643 = 4844465) B4844465
theorem B2153095 : Blo 2151435 2153095 := bstep (se 1 (by rfl) ⟨1614821, by rfl⟩ : syracuseStep 2153095 = 3229643) B3229643
theorem B2422237 : Blo 2151435 2422237 := bbase (se 3 (by rfl) ⟨454169, by rfl⟩ : syracuseStep 2422237 = 908339) (by norm_num)
theorem B3229649 : Blo 2151435 3229649 := bstep (se 2 (by rfl) ⟨1211118, by rfl⟩ : syracuseStep 3229649 = 2422237) B2422237
theorem B2153099 : Blo 2151435 2153099 := bstep (se 1 (by rfl) ⟨1614824, by rfl⟩ : syracuseStep 2153099 = 3229649) B3229649
theorem B7266725 : Blo 2151435 7266725 := bbase (se 4 (by rfl) ⟨681255, by rfl⟩ : syracuseStep 7266725 = 1362511) (by norm_num)
theorem B4844483 : Blo 2151435 4844483 := bstep (se 1 (by rfl) ⟨3633362, by rfl⟩ : syracuseStep 4844483 = 7266725) B7266725
theorem B3229655 : Blo 2151435 3229655 := bstep (se 1 (by rfl) ⟨2422241, by rfl⟩ : syracuseStep 3229655 = 4844483) B4844483
theorem B2153103 : Blo 2151435 2153103 := bstep (se 1 (by rfl) ⟨1614827, by rfl⟩ : syracuseStep 2153103 = 3229655) B3229655
theorem B3229661 : Blo 2151435 3229661 := bbase (se 3 (by rfl) ⟨605561, by rfl⟩ : syracuseStep 3229661 = 1211123) (by norm_num)
theorem B2153107 : Blo 2151435 2153107 := bstep (se 1 (by rfl) ⟨1614830, by rfl⟩ : syracuseStep 2153107 = 3229661) B3229661
theorem B4844501 : Blo 2151435 4844501 := bbase (se 7 (by rfl) ⟨56771, by rfl⟩ : syracuseStep 4844501 = 113543) (by norm_num)
theorem B3229667 : Blo 2151435 3229667 := bstep (se 1 (by rfl) ⟨2422250, by rfl⟩ : syracuseStep 3229667 = 4844501) B4844501
theorem B2153111 : Blo 2151435 2153111 := bstep (se 1 (by rfl) ⟨1614833, by rfl⟩ : syracuseStep 2153111 = 3229667) B3229667
theorem B10346629 : Blo 2151435 10346629 := bbase (se 4 (by rfl) ⟨969996, by rfl⟩ : syracuseStep 10346629 = 1939993) (by norm_num)
theorem B13795505 : Blo 2151435 13795505 := bstep (se 2 (by rfl) ⟨5173314, by rfl⟩ : syracuseStep 13795505 = 10346629) B10346629
theorem B9197003 : Blo 2151435 9197003 := bstep (se 1 (by rfl) ⟨6897752, by rfl⟩ : syracuseStep 9197003 = 13795505) B13795505
theorem B6131335 : Blo 2151435 6131335 := bstep (se 1 (by rfl) ⟨4598501, by rfl⟩ : syracuseStep 6131335 = 9197003) B9197003
theorem B8175113 : Blo 2151435 8175113 := bstep (se 2 (by rfl) ⟨3065667, by rfl⟩ : syracuseStep 8175113 = 6131335) B6131335
theorem B5450075 : Blo 2151435 5450075 := bstep (se 1 (by rfl) ⟨4087556, by rfl⟩ : syracuseStep 5450075 = 8175113) B8175113
theorem B3633383 : Blo 2151435 3633383 := bstep (se 1 (by rfl) ⟨2725037, by rfl⟩ : syracuseStep 3633383 = 5450075) B5450075
theorem B2422255 : Blo 2151435 2422255 := bstep (se 1 (by rfl) ⟨1816691, by rfl⟩ : syracuseStep 2422255 = 3633383) B3633383
theorem B3229673 : Blo 2151435 3229673 := bstep (se 2 (by rfl) ⟨1211127, by rfl⟩ : syracuseStep 3229673 = 2422255) B2422255
theorem B2153115 : Blo 2151435 2153115 := bstep (se 1 (by rfl) ⟨1614836, by rfl⟩ : syracuseStep 2153115 = 3229673) B3229673
theorem B18394037 : Blo 2151435 18394037 := bbase (se 5 (by rfl) ⟨862220, by rfl⟩ : syracuseStep 18394037 = 1724441) (by norm_num)
theorem B12262691 : Blo 2151435 12262691 := bstep (se 1 (by rfl) ⟨9197018, by rfl⟩ : syracuseStep 12262691 = 18394037) B18394037
theorem B8175127 : Blo 2151435 8175127 := bstep (se 1 (by rfl) ⟨6131345, by rfl⟩ : syracuseStep 8175127 = 12262691) B12262691
theorem B10900169 : Blo 2151435 10900169 := bstep (se 2 (by rfl) ⟨4087563, by rfl⟩ : syracuseStep 10900169 = 8175127) B8175127
theorem B7266779 : Blo 2151435 7266779 := bstep (se 1 (by rfl) ⟨5450084, by rfl⟩ : syracuseStep 7266779 = 10900169) B10900169
theorem B4844519 : Blo 2151435 4844519 := bstep (se 1 (by rfl) ⟨3633389, by rfl⟩ : syracuseStep 4844519 = 7266779) B7266779
theorem B3229679 : Blo 2151435 3229679 := bstep (se 1 (by rfl) ⟨2422259, by rfl⟩ : syracuseStep 3229679 = 4844519) B4844519
theorem B2153119 : Blo 2151435 2153119 := bstep (se 1 (by rfl) ⟨1614839, by rfl⟩ : syracuseStep 2153119 = 3229679) B3229679
theorem B3229685 : Blo 2151435 3229685 := bbase (se 5 (by rfl) ⟨151391, by rfl⟩ : syracuseStep 3229685 = 302783) (by norm_num)
theorem B2153123 : Blo 2151435 2153123 := bstep (se 1 (by rfl) ⟨1614842, by rfl⟩ : syracuseStep 2153123 = 3229685) B3229685
theorem B2488817 : Blo 2151435 2488817 := bbase (se 2 (by rfl) ⟨933306, by rfl⟩ : syracuseStep 2488817 = 1866613) (by norm_num)
theorem B6636845 : Blo 2151435 6636845 := bstep (se 3 (by rfl) ⟨1244408, by rfl⟩ : syracuseStep 6636845 = 2488817) B2488817
theorem B4424563 : Blo 2151435 4424563 := bstep (se 1 (by rfl) ⟨3318422, by rfl⟩ : syracuseStep 4424563 = 6636845) B6636845
theorem B23597669 : Blo 2151435 23597669 := bstep (se 4 (by rfl) ⟨2212281, by rfl⟩ : syracuseStep 23597669 = 4424563) B4424563
theorem B15731779 : Blo 2151435 15731779 := bstep (se 1 (by rfl) ⟨11798834, by rfl⟩ : syracuseStep 15731779 = 23597669) B23597669
theorem B20975705 : Blo 2151435 20975705 := bstep (se 2 (by rfl) ⟨7865889, by rfl⟩ : syracuseStep 20975705 = 15731779) B15731779
theorem B13983803 : Blo 2151435 13983803 := bstep (se 1 (by rfl) ⟨10487852, by rfl⟩ : syracuseStep 13983803 = 20975705) B20975705
theorem B9322535 : Blo 2151435 9322535 := bstep (se 1 (by rfl) ⟨6991901, by rfl⟩ : syracuseStep 9322535 = 13983803) B13983803
theorem B6215023 : Blo 2151435 6215023 := bstep (se 1 (by rfl) ⟨4661267, by rfl⟩ : syracuseStep 6215023 = 9322535) B9322535
theorem B8286697 : Blo 2151435 8286697 := bstep (se 2 (by rfl) ⟨3107511, by rfl⟩ : syracuseStep 8286697 = 6215023) B6215023
theorem B11048929 : Blo 2151435 11048929 := bstep (se 2 (by rfl) ⟨4143348, by rfl⟩ : syracuseStep 11048929 = 8286697) B8286697
theorem B58927621 : Blo 2151435 58927621 := bstep (se 4 (by rfl) ⟨5524464, by rfl⟩ : syracuseStep 58927621 = 11048929) B11048929
theorem B78570161 : Blo 2151435 78570161 := bstep (se 2 (by rfl) ⟨29463810, by rfl⟩ : syracuseStep 78570161 = 58927621) B58927621
theorem B52380107 : Blo 2151435 52380107 := bstep (se 1 (by rfl) ⟨39285080, by rfl⟩ : syracuseStep 52380107 = 78570161) B78570161
theorem B34920071 : Blo 2151435 34920071 := bstep (se 1 (by rfl) ⟨26190053, by rfl⟩ : syracuseStep 34920071 = 52380107) B52380107
theorem B23280047 : Blo 2151435 23280047 := bstep (se 1 (by rfl) ⟨17460035, by rfl⟩ : syracuseStep 23280047 = 34920071) B34920071
theorem B15520031 : Blo 2151435 15520031 := bstep (se 1 (by rfl) ⟨11640023, by rfl⟩ : syracuseStep 15520031 = 23280047) B23280047
theorem B10346687 : Blo 2151435 10346687 := bstep (se 1 (by rfl) ⟨7760015, by rfl⟩ : syracuseStep 10346687 = 15520031) B15520031
theorem B6897791 : Blo 2151435 6897791 := bstep (se 1 (by rfl) ⟨5173343, by rfl⟩ : syracuseStep 6897791 = 10346687) B10346687
theorem B4598527 : Blo 2151435 4598527 := bstep (se 1 (by rfl) ⟨3448895, by rfl⟩ : syracuseStep 4598527 = 6897791) B6897791
theorem B6131369 : Blo 2151435 6131369 := bstep (se 2 (by rfl) ⟨2299263, by rfl⟩ : syracuseStep 6131369 = 4598527) B4598527
theorem B4087579 : Blo 2151435 4087579 := bstep (se 1 (by rfl) ⟨3065684, by rfl⟩ : syracuseStep 4087579 = 6131369) B6131369
theorem B5450105 : Blo 2151435 5450105 := bstep (se 2 (by rfl) ⟨2043789, by rfl⟩ : syracuseStep 5450105 = 4087579) B4087579
theorem B3633403 : Blo 2151435 3633403 := bstep (se 1 (by rfl) ⟨2725052, by rfl⟩ : syracuseStep 3633403 = 5450105) B5450105
theorem B4844537 : Blo 2151435 4844537 := bstep (se 2 (by rfl) ⟨1816701, by rfl⟩ : syracuseStep 4844537 = 3633403) B3633403
theorem B3229691 : Blo 2151435 3229691 := bstep (se 1 (by rfl) ⟨2422268, by rfl⟩ : syracuseStep 3229691 = 4844537) B4844537
theorem B2153127 : Blo 2151435 2153127 := bstep (se 1 (by rfl) ⟨1614845, by rfl⟩ : syracuseStep 2153127 = 3229691) B3229691
theorem B2422273 : Blo 2151435 2422273 := bbase (se 2 (by rfl) ⟨908352, by rfl⟩ : syracuseStep 2422273 = 1816705) (by norm_num)
theorem B3229697 : Blo 2151435 3229697 := bstep (se 2 (by rfl) ⟨1211136, by rfl⟩ : syracuseStep 3229697 = 2422273) B2422273
theorem B2153131 : Blo 2151435 2153131 := bstep (se 1 (by rfl) ⟨1614848, by rfl⟩ : syracuseStep 2153131 = 3229697) B3229697
theorem B5450125 : Blo 2151435 5450125 := bbase (se 3 (by rfl) ⟨1021898, by rfl⟩ : syracuseStep 5450125 = 2043797) (by norm_num)
theorem B7266833 : Blo 2151435 7266833 := bstep (se 2 (by rfl) ⟨2725062, by rfl⟩ : syracuseStep 7266833 = 5450125) B5450125
theorem B4844555 : Blo 2151435 4844555 := bstep (se 1 (by rfl) ⟨3633416, by rfl⟩ : syracuseStep 4844555 = 7266833) B7266833
theorem B3229703 : Blo 2151435 3229703 := bstep (se 1 (by rfl) ⟨2422277, by rfl⟩ : syracuseStep 3229703 = 4844555) B4844555
theorem B2153135 : Blo 2151435 2153135 := bstep (se 1 (by rfl) ⟨1614851, by rfl⟩ : syracuseStep 2153135 = 3229703) B3229703
theorem B3229709 : Blo 2151435 3229709 := bbase (se 3 (by rfl) ⟨605570, by rfl⟩ : syracuseStep 3229709 = 1211141) (by norm_num)
theorem B2153139 : Blo 2151435 2153139 := bstep (se 1 (by rfl) ⟨1614854, by rfl⟩ : syracuseStep 2153139 = 3229709) B3229709
theorem B4844573 : Blo 2151435 4844573 := bbase (se 3 (by rfl) ⟨908357, by rfl⟩ : syracuseStep 4844573 = 1816715) (by norm_num)
theorem B3229715 : Blo 2151435 3229715 := bstep (se 1 (by rfl) ⟨2422286, by rfl⟩ : syracuseStep 3229715 = 4844573) B4844573
theorem B2153143 : Blo 2151435 2153143 := bstep (se 1 (by rfl) ⟨1614857, by rfl⟩ : syracuseStep 2153143 = 3229715) B3229715
theorem B3633437 : Blo 2151435 3633437 := bbase (se 3 (by rfl) ⟨681269, by rfl⟩ : syracuseStep 3633437 = 1362539) (by norm_num)
theorem B2422291 : Blo 2151435 2422291 := bstep (se 1 (by rfl) ⟨1816718, by rfl⟩ : syracuseStep 2422291 = 3633437) B3633437
theorem B3229721 : Blo 2151435 3229721 := bstep (se 2 (by rfl) ⟨1211145, by rfl⟩ : syracuseStep 3229721 = 2422291) B2422291
theorem B2153147 : Blo 2151435 2153147 := bstep (se 1 (by rfl) ⟨1614860, by rfl⟩ : syracuseStep 2153147 = 3229721) B3229721
theorem B13795733 : Blo 2151435 13795733 := bbase (se 6 (by rfl) ⟨323337, by rfl⟩ : syracuseStep 13795733 = 646675) (by norm_num)
theorem B9197155 : Blo 2151435 9197155 := bstep (se 1 (by rfl) ⟨6897866, by rfl⟩ : syracuseStep 9197155 = 13795733) B13795733
theorem B12262873 : Blo 2151435 12262873 := bstep (se 2 (by rfl) ⟨4598577, by rfl⟩ : syracuseStep 12262873 = 9197155) B9197155
theorem B16350497 : Blo 2151435 16350497 := bstep (se 2 (by rfl) ⟨6131436, by rfl⟩ : syracuseStep 16350497 = 12262873) B12262873
theorem B10900331 : Blo 2151435 10900331 := bstep (se 1 (by rfl) ⟨8175248, by rfl⟩ : syracuseStep 10900331 = 16350497) B16350497
theorem B7266887 : Blo 2151435 7266887 := bstep (se 1 (by rfl) ⟨5450165, by rfl⟩ : syracuseStep 7266887 = 10900331) B10900331
theorem B4844591 : Blo 2151435 4844591 := bstep (se 1 (by rfl) ⟨3633443, by rfl⟩ : syracuseStep 4844591 = 7266887) B7266887
theorem B3229727 : Blo 2151435 3229727 := bstep (se 1 (by rfl) ⟨2422295, by rfl⟩ : syracuseStep 3229727 = 4844591) B4844591
theorem B2153151 : Blo 2151435 2153151 := bstep (se 1 (by rfl) ⟨1614863, by rfl⟩ : syracuseStep 2153151 = 3229727) B3229727
theorem B3229733 : Blo 2151435 3229733 := bbase (se 4 (by rfl) ⟨302787, by rfl⟩ : syracuseStep 3229733 = 605575) (by norm_num)
theorem B2153155 : Blo 2151435 2153155 := bstep (se 1 (by rfl) ⟨1614866, by rfl⟩ : syracuseStep 2153155 = 3229733) B3229733
theorem B2725093 : Blo 2151435 2725093 := bbase (se 4 (by rfl) ⟨255477, by rfl⟩ : syracuseStep 2725093 = 510955) (by norm_num)
theorem B3633457 : Blo 2151435 3633457 := bstep (se 2 (by rfl) ⟨1362546, by rfl⟩ : syracuseStep 3633457 = 2725093) B2725093
theorem B4844609 : Blo 2151435 4844609 := bstep (se 2 (by rfl) ⟨1816728, by rfl⟩ : syracuseStep 4844609 = 3633457) B3633457
theorem B3229739 : Blo 2151435 3229739 := bstep (se 1 (by rfl) ⟨2422304, by rfl⟩ : syracuseStep 3229739 = 4844609) B4844609
theorem B2153159 : Blo 2151435 2153159 := bstep (se 1 (by rfl) ⟨1614869, by rfl⟩ : syracuseStep 2153159 = 3229739) B3229739
theorem B2422309 : Blo 2151435 2422309 := bbase (se 4 (by rfl) ⟨227091, by rfl⟩ : syracuseStep 2422309 = 454183) (by norm_num)
theorem B3229745 : Blo 2151435 3229745 := bstep (se 2 (by rfl) ⟨1211154, by rfl⟩ : syracuseStep 3229745 = 2422309) B2422309
theorem B2153163 : Blo 2151435 2153163 := bstep (se 1 (by rfl) ⟨1614872, by rfl⟩ : syracuseStep 2153163 = 3229745) B3229745
theorem B2330677 : Blo 2151435 2330677 := bbase (se 5 (by rfl) ⟨109250, by rfl⟩ : syracuseStep 2330677 = 218501) (by norm_num)
theorem B12430277 : Blo 2151435 12430277 := bstep (se 4 (by rfl) ⟨1165338, by rfl⟩ : syracuseStep 12430277 = 2330677) B2330677
theorem B8286851 : Blo 2151435 8286851 := bstep (se 1 (by rfl) ⟨6215138, by rfl⟩ : syracuseStep 8286851 = 12430277) B12430277
theorem B5524567 : Blo 2151435 5524567 := bstep (se 1 (by rfl) ⟨4143425, by rfl⟩ : syracuseStep 5524567 = 8286851) B8286851
theorem B117857429 : Blo 2151435 117857429 := bstep (se 6 (by rfl) ⟨2762283, by rfl⟩ : syracuseStep 117857429 = 5524567) B5524567
theorem B78571619 : Blo 2151435 78571619 := bstep (se 1 (by rfl) ⟨58928714, by rfl⟩ : syracuseStep 78571619 = 117857429) B117857429
theorem B52381079 : Blo 2151435 52381079 := bstep (se 1 (by rfl) ⟨39285809, by rfl⟩ : syracuseStep 52381079 = 78571619) B78571619
theorem B34920719 : Blo 2151435 34920719 := bstep (se 1 (by rfl) ⟨26190539, by rfl⟩ : syracuseStep 34920719 = 52381079) B52381079
theorem B23280479 : Blo 2151435 23280479 := bstep (se 1 (by rfl) ⟨17460359, by rfl⟩ : syracuseStep 23280479 = 34920719) B34920719
theorem B15520319 : Blo 2151435 15520319 := bstep (se 1 (by rfl) ⟨11640239, by rfl⟩ : syracuseStep 15520319 = 23280479) B23280479
theorem B10346879 : Blo 2151435 10346879 := bstep (se 1 (by rfl) ⟨7760159, by rfl⟩ : syracuseStep 10346879 = 15520319) B15520319
theorem B6897919 : Blo 2151435 6897919 := bstep (se 1 (by rfl) ⟨5173439, by rfl⟩ : syracuseStep 6897919 = 10346879) B10346879
theorem B9197225 : Blo 2151435 9197225 := bstep (se 2 (by rfl) ⟨3448959, by rfl⟩ : syracuseStep 9197225 = 6897919) B6897919
theorem B6131483 : Blo 2151435 6131483 := bstep (se 1 (by rfl) ⟨4598612, by rfl⟩ : syracuseStep 6131483 = 9197225) B9197225
theorem B4087655 : Blo 2151435 4087655 := bstep (se 1 (by rfl) ⟨3065741, by rfl⟩ : syracuseStep 4087655 = 6131483) B6131483
theorem B2725103 : Blo 2151435 2725103 := bstep (se 1 (by rfl) ⟨2043827, by rfl⟩ : syracuseStep 2725103 = 4087655) B4087655
theorem B7266941 : Blo 2151435 7266941 := bstep (se 3 (by rfl) ⟨1362551, by rfl⟩ : syracuseStep 7266941 = 2725103) B2725103
theorem B4844627 : Blo 2151435 4844627 := bstep (se 1 (by rfl) ⟨3633470, by rfl⟩ : syracuseStep 4844627 = 7266941) B7266941
theorem B3229751 : Blo 2151435 3229751 := bstep (se 1 (by rfl) ⟨2422313, by rfl⟩ : syracuseStep 3229751 = 4844627) B4844627
theorem B2153167 : Blo 2151435 2153167 := bstep (se 1 (by rfl) ⟨1614875, by rfl⟩ : syracuseStep 2153167 = 3229751) B3229751
theorem B3229757 : Blo 2151435 3229757 := bbase (se 3 (by rfl) ⟨605579, by rfl⟩ : syracuseStep 3229757 = 1211159) (by norm_num)
theorem B2153171 : Blo 2151435 2153171 := bstep (se 1 (by rfl) ⟨1614878, by rfl⟩ : syracuseStep 2153171 = 3229757) B3229757
theorem B4844645 : Blo 2151435 4844645 := bbase (se 4 (by rfl) ⟨454185, by rfl⟩ : syracuseStep 4844645 = 908371) (by norm_num)
theorem B3229763 : Blo 2151435 3229763 := bstep (se 1 (by rfl) ⟨2422322, by rfl⟩ : syracuseStep 3229763 = 4844645) B4844645
theorem B2153175 : Blo 2151435 2153175 := bstep (se 1 (by rfl) ⟨1614881, by rfl⟩ : syracuseStep 2153175 = 3229763) B3229763
theorem B5450237 : Blo 2151435 5450237 := bbase (se 3 (by rfl) ⟨1021919, by rfl⟩ : syracuseStep 5450237 = 2043839) (by norm_num)
theorem B3633491 : Blo 2151435 3633491 := bstep (se 1 (by rfl) ⟨2725118, by rfl⟩ : syracuseStep 3633491 = 5450237) B5450237
theorem B2422327 : Blo 2151435 2422327 := bstep (se 1 (by rfl) ⟨1816745, by rfl⟩ : syracuseStep 2422327 = 3633491) B3633491
theorem B3229769 : Blo 2151435 3229769 := bstep (se 2 (by rfl) ⟨1211163, by rfl⟩ : syracuseStep 3229769 = 2422327) B2422327
theorem B2153179 : Blo 2151435 2153179 := bstep (se 1 (by rfl) ⟨1614884, by rfl⟩ : syracuseStep 2153179 = 3229769) B3229769
theorem B4087685 : Blo 2151435 4087685 := bbase (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) (by norm_num)
theorem B10900493 : Blo 2151435 10900493 := bstep (se 3 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 10900493 = 4087685) B4087685
theorem B7266995 : Blo 2151435 7266995 := bstep (se 1 (by rfl) ⟨5450246, by rfl⟩ : syracuseStep 7266995 = 10900493) B10900493
theorem B4844663 : Blo 2151435 4844663 := bstep (se 1 (by rfl) ⟨3633497, by rfl⟩ : syracuseStep 4844663 = 7266995) B7266995
theorem B3229775 : Blo 2151435 3229775 := bstep (se 1 (by rfl) ⟨2422331, by rfl⟩ : syracuseStep 3229775 = 4844663) B4844663
theorem B2153183 : Blo 2151435 2153183 := bstep (se 1 (by rfl) ⟨1614887, by rfl⟩ : syracuseStep 2153183 = 3229775) B3229775
theorem B3229781 : Blo 2151435 3229781 := bbase (se 8 (by rfl) ⟨18924, by rfl⟩ : syracuseStep 3229781 = 37849) (by norm_num)
theorem B2153187 : Blo 2151435 2153187 := bstep (se 1 (by rfl) ⟨1614890, by rfl⟩ : syracuseStep 2153187 = 3229781) B3229781
theorem B31040981 : Blo 2151435 31040981 := bbase (se 7 (by rfl) ⟨363761, by rfl⟩ : syracuseStep 31040981 = 727523) (by norm_num)
theorem B20693987 : Blo 2151435 20693987 := bstep (se 1 (by rfl) ⟨15520490, by rfl⟩ : syracuseStep 20693987 = 31040981) B31040981
theorem B13795991 : Blo 2151435 13795991 := bstep (se 1 (by rfl) ⟨10346993, by rfl⟩ : syracuseStep 13795991 = 20693987) B20693987
theorem B9197327 : Blo 2151435 9197327 := bstep (se 1 (by rfl) ⟨6897995, by rfl⟩ : syracuseStep 9197327 = 13795991) B13795991
theorem B6131551 : Blo 2151435 6131551 := bstep (se 1 (by rfl) ⟨4598663, by rfl⟩ : syracuseStep 6131551 = 9197327) B9197327
theorem B8175401 : Blo 2151435 8175401 := bstep (se 2 (by rfl) ⟨3065775, by rfl⟩ : syracuseStep 8175401 = 6131551) B6131551
theorem B5450267 : Blo 2151435 5450267 := bstep (se 1 (by rfl) ⟨4087700, by rfl⟩ : syracuseStep 5450267 = 8175401) B8175401
theorem B3633511 : Blo 2151435 3633511 := bstep (se 1 (by rfl) ⟨2725133, by rfl⟩ : syracuseStep 3633511 = 5450267) B5450267
theorem B4844681 : Blo 2151435 4844681 := bstep (se 2 (by rfl) ⟨1816755, by rfl⟩ : syracuseStep 4844681 = 3633511) B3633511
theorem B3229787 : Blo 2151435 3229787 := bstep (se 1 (by rfl) ⟨2422340, by rfl⟩ : syracuseStep 3229787 = 4844681) B4844681
theorem B2153191 : Blo 2151435 2153191 := bstep (se 1 (by rfl) ⟨1614893, by rfl⟩ : syracuseStep 2153191 = 3229787) B3229787
theorem B2422345 : Blo 2151435 2422345 := bbase (se 2 (by rfl) ⟨908379, by rfl⟩ : syracuseStep 2422345 = 1816759) (by norm_num)
theorem B3229793 : Blo 2151435 3229793 := bstep (se 2 (by rfl) ⟨1211172, by rfl⟩ : syracuseStep 3229793 = 2422345) B2422345
theorem B2153195 : Blo 2151435 2153195 := bstep (se 1 (by rfl) ⟨1614896, by rfl⟩ : syracuseStep 2153195 = 3229793) B3229793
theorem B2182577 : Blo 2151435 2182577 := bbase (se 2 (by rfl) ⟨818466, by rfl⟩ : syracuseStep 2182577 = 1636933) (by norm_num)
theorem B23280821 : Blo 2151435 23280821 := bstep (se 5 (by rfl) ⟨1091288, by rfl⟩ : syracuseStep 23280821 = 2182577) B2182577
theorem B15520547 : Blo 2151435 15520547 := bstep (se 1 (by rfl) ⟨11640410, by rfl⟩ : syracuseStep 15520547 = 23280821) B23280821
theorem B10347031 : Blo 2151435 10347031 := bstep (se 1 (by rfl) ⟨7760273, by rfl⟩ : syracuseStep 10347031 = 15520547) B15520547
theorem B13796041 : Blo 2151435 13796041 := bstep (se 2 (by rfl) ⟨5173515, by rfl⟩ : syracuseStep 13796041 = 10347031) B10347031
theorem B18394721 : Blo 2151435 18394721 := bstep (se 2 (by rfl) ⟨6898020, by rfl⟩ : syracuseStep 18394721 = 13796041) B13796041
theorem B12263147 : Blo 2151435 12263147 := bstep (se 1 (by rfl) ⟨9197360, by rfl⟩ : syracuseStep 12263147 = 18394721) B18394721
theorem B8175431 : Blo 2151435 8175431 := bstep (se 1 (by rfl) ⟨6131573, by rfl⟩ : syracuseStep 8175431 = 12263147) B12263147
theorem B5450287 : Blo 2151435 5450287 := bstep (se 1 (by rfl) ⟨4087715, by rfl⟩ : syracuseStep 5450287 = 8175431) B8175431
theorem B7267049 : Blo 2151435 7267049 := bstep (se 2 (by rfl) ⟨2725143, by rfl⟩ : syracuseStep 7267049 = 5450287) B5450287
theorem B4844699 : Blo 2151435 4844699 := bstep (se 1 (by rfl) ⟨3633524, by rfl⟩ : syracuseStep 4844699 = 7267049) B7267049
theorem B3229799 : Blo 2151435 3229799 := bstep (se 1 (by rfl) ⟨2422349, by rfl⟩ : syracuseStep 3229799 = 4844699) B4844699
theorem B2153199 : Blo 2151435 2153199 := bstep (se 1 (by rfl) ⟨1614899, by rfl⟩ : syracuseStep 2153199 = 3229799) B3229799
theorem B3229805 : Blo 2151435 3229805 := bbase (se 3 (by rfl) ⟨605588, by rfl⟩ : syracuseStep 3229805 = 1211177) (by norm_num)
theorem B2153203 : Blo 2151435 2153203 := bstep (se 1 (by rfl) ⟨1614902, by rfl⟩ : syracuseStep 2153203 = 3229805) B3229805
theorem B4844717 : Blo 2151435 4844717 := bbase (se 3 (by rfl) ⟨908384, by rfl⟩ : syracuseStep 4844717 = 1816769) (by norm_num)
theorem B3229811 : Blo 2151435 3229811 := bstep (se 1 (by rfl) ⟨2422358, by rfl⟩ : syracuseStep 3229811 = 4844717) B4844717
theorem B2153207 : Blo 2151435 2153207 := bstep (se 1 (by rfl) ⟨1614905, by rfl⟩ : syracuseStep 2153207 = 3229811) B3229811
theorem B2586773 : Blo 2151435 2586773 := bbase (se 6 (by rfl) ⟨60627, by rfl⟩ : syracuseStep 2586773 = 121255) (by norm_num)
theorem B6898061 : Blo 2151435 6898061 := bstep (se 3 (by rfl) ⟨1293386, by rfl⟩ : syracuseStep 6898061 = 2586773) B2586773
theorem B4598707 : Blo 2151435 4598707 := bstep (se 1 (by rfl) ⟨3449030, by rfl⟩ : syracuseStep 4598707 = 6898061) B6898061
theorem B6131609 : Blo 2151435 6131609 := bstep (se 2 (by rfl) ⟨2299353, by rfl⟩ : syracuseStep 6131609 = 4598707) B4598707
theorem B4087739 : Blo 2151435 4087739 := bstep (se 1 (by rfl) ⟨3065804, by rfl⟩ : syracuseStep 4087739 = 6131609) B6131609
theorem B2725159 : Blo 2151435 2725159 := bstep (se 1 (by rfl) ⟨2043869, by rfl⟩ : syracuseStep 2725159 = 4087739) B4087739
theorem B3633545 : Blo 2151435 3633545 := bstep (se 2 (by rfl) ⟨1362579, by rfl⟩ : syracuseStep 3633545 = 2725159) B2725159
theorem B2422363 : Blo 2151435 2422363 := bstep (se 1 (by rfl) ⟨1816772, by rfl⟩ : syracuseStep 2422363 = 3633545) B3633545
theorem B3229817 : Blo 2151435 3229817 := bstep (se 2 (by rfl) ⟨1211181, by rfl⟩ : syracuseStep 3229817 = 2422363) B2422363
theorem B2153211 : Blo 2151435 2153211 := bstep (se 1 (by rfl) ⟨1614908, by rfl⟩ : syracuseStep 2153211 = 3229817) B3229817
theorem B15520661 : Blo 2151435 15520661 := bbase (se 6 (by rfl) ⟨363765, by rfl⟩ : syracuseStep 15520661 = 727531) (by norm_num)
theorem B10347107 : Blo 2151435 10347107 := bstep (se 1 (by rfl) ⟨7760330, by rfl⟩ : syracuseStep 10347107 = 15520661) B15520661
theorem B27592285 : Blo 2151435 27592285 := bstep (se 3 (by rfl) ⟨5173553, by rfl⟩ : syracuseStep 27592285 = 10347107) B10347107
theorem B36789713 : Blo 2151435 36789713 := bstep (se 2 (by rfl) ⟨13796142, by rfl⟩ : syracuseStep 36789713 = 27592285) B27592285
theorem B24526475 : Blo 2151435 24526475 := bstep (se 1 (by rfl) ⟨18394856, by rfl⟩ : syracuseStep 24526475 = 36789713) B36789713
theorem B16350983 : Blo 2151435 16350983 := bstep (se 1 (by rfl) ⟨12263237, by rfl⟩ : syracuseStep 16350983 = 24526475) B24526475
theorem B10900655 : Blo 2151435 10900655 := bstep (se 1 (by rfl) ⟨8175491, by rfl⟩ : syracuseStep 10900655 = 16350983) B16350983
theorem B7267103 : Blo 2151435 7267103 := bstep (se 1 (by rfl) ⟨5450327, by rfl⟩ : syracuseStep 7267103 = 10900655) B10900655
theorem B4844735 : Blo 2151435 4844735 := bstep (se 1 (by rfl) ⟨3633551, by rfl⟩ : syracuseStep 4844735 = 7267103) B7267103
theorem B3229823 : Blo 2151435 3229823 := bstep (se 1 (by rfl) ⟨2422367, by rfl⟩ : syracuseStep 3229823 = 4844735) B4844735
theorem B2153215 : Blo 2151435 2153215 := bstep (se 1 (by rfl) ⟨1614911, by rfl⟩ : syracuseStep 2153215 = 3229823) B3229823
theorem B3229829 : Blo 2151435 3229829 := bbase (se 4 (by rfl) ⟨302796, by rfl⟩ : syracuseStep 3229829 = 605593) (by norm_num)
theorem B2153219 : Blo 2151435 2153219 := bstep (se 1 (by rfl) ⟨1614914, by rfl⟩ : syracuseStep 2153219 = 3229829) B3229829
theorem B3633565 : Blo 2151435 3633565 := bbase (se 3 (by rfl) ⟨681293, by rfl⟩ : syracuseStep 3633565 = 1362587) (by norm_num)
theorem B4844753 : Blo 2151435 4844753 := bstep (se 2 (by rfl) ⟨1816782, by rfl⟩ : syracuseStep 4844753 = 3633565) B3633565
theorem B3229835 : Blo 2151435 3229835 := bstep (se 1 (by rfl) ⟨2422376, by rfl⟩ : syracuseStep 3229835 = 4844753) B4844753
theorem B2153223 : Blo 2151435 2153223 := bstep (se 1 (by rfl) ⟨1614917, by rfl⟩ : syracuseStep 2153223 = 3229835) B3229835
theorem B2422381 : Blo 2151435 2422381 := bbase (se 3 (by rfl) ⟨454196, by rfl⟩ : syracuseStep 2422381 = 908393) (by norm_num)
theorem B3229841 : Blo 2151435 3229841 := bstep (se 2 (by rfl) ⟨1211190, by rfl⟩ : syracuseStep 3229841 = 2422381) B2422381
theorem B2153227 : Blo 2151435 2153227 := bstep (se 1 (by rfl) ⟨1614920, by rfl⟩ : syracuseStep 2153227 = 3229841) B3229841
theorem B7267157 : Blo 2151435 7267157 := bbase (se 9 (by rfl) ⟨21290, by rfl⟩ : syracuseStep 7267157 = 42581) (by norm_num)
theorem B4844771 : Blo 2151435 4844771 := bstep (se 1 (by rfl) ⟨3633578, by rfl⟩ : syracuseStep 4844771 = 7267157) B7267157
theorem B3229847 : Blo 2151435 3229847 := bstep (se 1 (by rfl) ⟨2422385, by rfl⟩ : syracuseStep 3229847 = 4844771) B4844771
theorem B2153231 : Blo 2151435 2153231 := bstep (se 1 (by rfl) ⟨1614923, by rfl⟩ : syracuseStep 2153231 = 3229847) B3229847
theorem B3229853 : Blo 2151435 3229853 := bbase (se 3 (by rfl) ⟨605597, by rfl⟩ : syracuseStep 3229853 = 1211195) (by norm_num)
theorem B2153235 : Blo 2151435 2153235 := bstep (se 1 (by rfl) ⟨1614926, by rfl⟩ : syracuseStep 2153235 = 3229853) B3229853
theorem B4844789 : Blo 2151435 4844789 := bbase (se 5 (by rfl) ⟨227099, by rfl⟩ : syracuseStep 4844789 = 454199) (by norm_num)
theorem B3229859 : Blo 2151435 3229859 := bstep (se 1 (by rfl) ⟨2422394, by rfl⟩ : syracuseStep 3229859 = 4844789) B4844789
theorem B2153239 : Blo 2151435 2153239 := bstep (se 1 (by rfl) ⟨1614929, by rfl⟩ : syracuseStep 2153239 = 3229859) B3229859
theorem B2762381 : Blo 2151435 2762381 := bbase (se 3 (by rfl) ⟨517946, by rfl⟩ : syracuseStep 2762381 = 1035893) (by norm_num)
theorem B7366349 : Blo 2151435 7366349 := bstep (se 3 (by rfl) ⟨1381190, by rfl⟩ : syracuseStep 7366349 = 2762381) B2762381
theorem B19643597 : Blo 2151435 19643597 := bstep (se 3 (by rfl) ⟨3683174, by rfl⟩ : syracuseStep 19643597 = 7366349) B7366349
theorem B13095731 : Blo 2151435 13095731 := bstep (se 1 (by rfl) ⟨9821798, by rfl⟩ : syracuseStep 13095731 = 19643597) B19643597
theorem B8730487 : Blo 2151435 8730487 := bstep (se 1 (by rfl) ⟨6547865, by rfl⟩ : syracuseStep 8730487 = 13095731) B13095731
theorem B46562597 : Blo 2151435 46562597 := bstep (se 4 (by rfl) ⟨4365243, by rfl⟩ : syracuseStep 46562597 = 8730487) B8730487
theorem B31041731 : Blo 2151435 31041731 := bstep (se 1 (by rfl) ⟨23281298, by rfl⟩ : syracuseStep 31041731 = 46562597) B46562597
theorem B20694487 : Blo 2151435 20694487 := bstep (se 1 (by rfl) ⟨15520865, by rfl⟩ : syracuseStep 20694487 = 31041731) B31041731
theorem B27592649 : Blo 2151435 27592649 := bstep (se 2 (by rfl) ⟨10347243, by rfl⟩ : syracuseStep 27592649 = 20694487) B20694487
theorem B18395099 : Blo 2151435 18395099 := bstep (se 1 (by rfl) ⟨13796324, by rfl⟩ : syracuseStep 18395099 = 27592649) B27592649
theorem B12263399 : Blo 2151435 12263399 := bstep (se 1 (by rfl) ⟨9197549, by rfl⟩ : syracuseStep 12263399 = 18395099) B18395099
theorem B8175599 : Blo 2151435 8175599 := bstep (se 1 (by rfl) ⟨6131699, by rfl⟩ : syracuseStep 8175599 = 12263399) B12263399
theorem B5450399 : Blo 2151435 5450399 := bstep (se 1 (by rfl) ⟨4087799, by rfl⟩ : syracuseStep 5450399 = 8175599) B8175599
theorem B3633599 : Blo 2151435 3633599 := bstep (se 1 (by rfl) ⟨2725199, by rfl⟩ : syracuseStep 3633599 = 5450399) B5450399
theorem B2422399 : Blo 2151435 2422399 := bstep (se 1 (by rfl) ⟨1816799, by rfl⟩ : syracuseStep 2422399 = 3633599) B3633599
theorem B3229865 : Blo 2151435 3229865 := bstep (se 2 (by rfl) ⟨1211199, by rfl⟩ : syracuseStep 3229865 = 2422399) B2422399
theorem B2153243 : Blo 2151435 2153243 := bstep (se 1 (by rfl) ⟨1614932, by rfl⟩ : syracuseStep 2153243 = 3229865) B3229865
theorem B7184389 : Blo 2151435 7184389 := bbase (se 4 (by rfl) ⟨673536, by rfl⟩ : syracuseStep 7184389 = 1347073) (by norm_num)
theorem B9579185 : Blo 2151435 9579185 := bstep (se 2 (by rfl) ⟨3592194, by rfl⟩ : syracuseStep 9579185 = 7184389) B7184389
theorem B6386123 : Blo 2151435 6386123 := bstep (se 1 (by rfl) ⟨4789592, by rfl⟩ : syracuseStep 6386123 = 9579185) B9579185
theorem B4257415 : Blo 2151435 4257415 := bstep (se 1 (by rfl) ⟨3193061, by rfl⟩ : syracuseStep 4257415 = 6386123) B6386123
theorem B5676553 : Blo 2151435 5676553 := bstep (se 2 (by rfl) ⟨2128707, by rfl⟩ : syracuseStep 5676553 = 4257415) B4257415
theorem B30274949 : Blo 2151435 30274949 := bstep (se 4 (by rfl) ⟨2838276, by rfl⟩ : syracuseStep 30274949 = 5676553) B5676553
theorem B20183299 : Blo 2151435 20183299 := bstep (se 1 (by rfl) ⟨15137474, by rfl⟩ : syracuseStep 20183299 = 30274949) B30274949
theorem B107644261 : Blo 2151435 107644261 := bstep (se 4 (by rfl) ⟨10091649, by rfl⟩ : syracuseStep 107644261 = 20183299) B20183299
theorem B143525681 : Blo 2151435 143525681 := bstep (se 2 (by rfl) ⟨53822130, by rfl⟩ : syracuseStep 143525681 = 107644261) B107644261
theorem B95683787 : Blo 2151435 95683787 := bstep (se 1 (by rfl) ⟨71762840, by rfl⟩ : syracuseStep 95683787 = 143525681) B143525681
theorem B63789191 : Blo 2151435 63789191 := bstep (se 1 (by rfl) ⟨47841893, by rfl⟩ : syracuseStep 63789191 = 95683787) B95683787
theorem B42526127 : Blo 2151435 42526127 := bstep (se 1 (by rfl) ⟨31894595, by rfl⟩ : syracuseStep 42526127 = 63789191) B63789191
theorem B28350751 : Blo 2151435 28350751 := bstep (se 1 (by rfl) ⟨21263063, by rfl⟩ : syracuseStep 28350751 = 42526127) B42526127
theorem B37801001 : Blo 2151435 37801001 := bstep (se 2 (by rfl) ⟨14175375, by rfl⟩ : syracuseStep 37801001 = 28350751) B28350751
theorem B25200667 : Blo 2151435 25200667 := bstep (se 1 (by rfl) ⟨18900500, by rfl⟩ : syracuseStep 25200667 = 37801001) B37801001
theorem B33600889 : Blo 2151435 33600889 := bstep (se 2 (by rfl) ⟨12600333, by rfl⟩ : syracuseStep 33600889 = 25200667) B25200667
theorem B44801185 : Blo 2151435 44801185 := bstep (se 2 (by rfl) ⟨16800444, by rfl⟩ : syracuseStep 44801185 = 33600889) B33600889
theorem B59734913 : Blo 2151435 59734913 := bstep (se 2 (by rfl) ⟨22400592, by rfl⟩ : syracuseStep 59734913 = 44801185) B44801185
theorem B637172405 : Blo 2151435 637172405 := bstep (se 5 (by rfl) ⟨29867456, by rfl⟩ : syracuseStep 637172405 = 59734913) B59734913
theorem B424781603 : Blo 2151435 424781603 := bstep (se 1 (by rfl) ⟨318586202, by rfl⟩ : syracuseStep 424781603 = 637172405) B637172405
theorem B283187735 : Blo 2151435 283187735 := bstep (se 1 (by rfl) ⟨212390801, by rfl⟩ : syracuseStep 283187735 = 424781603) B424781603
theorem B188791823 : Blo 2151435 188791823 := bstep (se 1 (by rfl) ⟨141593867, by rfl⟩ : syracuseStep 188791823 = 283187735) B283187735
theorem B125861215 : Blo 2151435 125861215 := bstep (se 1 (by rfl) ⟨94395911, by rfl⟩ : syracuseStep 125861215 = 188791823) B188791823
theorem B167814953 : Blo 2151435 167814953 := bstep (se 2 (by rfl) ⟨62930607, by rfl⟩ : syracuseStep 167814953 = 125861215) B125861215
theorem B111876635 : Blo 2151435 111876635 := bstep (se 1 (by rfl) ⟨83907476, by rfl⟩ : syracuseStep 111876635 = 167814953) B167814953
theorem B74584423 : Blo 2151435 74584423 := bstep (se 1 (by rfl) ⟨55938317, by rfl⟩ : syracuseStep 74584423 = 111876635) B111876635
theorem B99445897 : Blo 2151435 99445897 := bstep (se 2 (by rfl) ⟨37292211, by rfl⟩ : syracuseStep 99445897 = 74584423) B74584423
theorem B132594529 : Blo 2151435 132594529 := bstep (se 2 (by rfl) ⟨49722948, by rfl⟩ : syracuseStep 132594529 = 99445897) B99445897
theorem B176792705 : Blo 2151435 176792705 := bstep (se 2 (by rfl) ⟨66297264, by rfl⟩ : syracuseStep 176792705 = 132594529) B132594529
theorem B117861803 : Blo 2151435 117861803 := bstep (se 1 (by rfl) ⟨88396352, by rfl⟩ : syracuseStep 117861803 = 176792705) B176792705
theorem B78574535 : Blo 2151435 78574535 := bstep (se 1 (by rfl) ⟨58930901, by rfl⟩ : syracuseStep 78574535 = 117861803) B117861803
theorem B52383023 : Blo 2151435 52383023 := bstep (se 1 (by rfl) ⟨39287267, by rfl⟩ : syracuseStep 52383023 = 78574535) B78574535
theorem B34922015 : Blo 2151435 34922015 := bstep (se 1 (by rfl) ⟨26191511, by rfl⟩ : syracuseStep 34922015 = 52383023) B52383023
theorem B23281343 : Blo 2151435 23281343 := bstep (se 1 (by rfl) ⟨17461007, by rfl⟩ : syracuseStep 23281343 = 34922015) B34922015
theorem B15520895 : Blo 2151435 15520895 := bstep (se 1 (by rfl) ⟨11640671, by rfl⟩ : syracuseStep 15520895 = 23281343) B23281343
theorem B10347263 : Blo 2151435 10347263 := bstep (se 1 (by rfl) ⟨7760447, by rfl⟩ : syracuseStep 10347263 = 15520895) B15520895
theorem B6898175 : Blo 2151435 6898175 := bstep (se 1 (by rfl) ⟨5173631, by rfl⟩ : syracuseStep 6898175 = 10347263) B10347263
theorem B4598783 : Blo 2151435 4598783 := bstep (se 1 (by rfl) ⟨3449087, by rfl⟩ : syracuseStep 4598783 = 6898175) B6898175
theorem B3065855 : Blo 2151435 3065855 := bstep (se 1 (by rfl) ⟨2299391, by rfl⟩ : syracuseStep 3065855 = 4598783) B4598783
theorem B8175613 : Blo 2151435 8175613 := bstep (se 3 (by rfl) ⟨1532927, by rfl⟩ : syracuseStep 8175613 = 3065855) B3065855
theorem B10900817 : Blo 2151435 10900817 := bstep (se 2 (by rfl) ⟨4087806, by rfl⟩ : syracuseStep 10900817 = 8175613) B8175613
theorem B7267211 : Blo 2151435 7267211 := bstep (se 1 (by rfl) ⟨5450408, by rfl⟩ : syracuseStep 7267211 = 10900817) B10900817
theorem B4844807 : Blo 2151435 4844807 := bstep (se 1 (by rfl) ⟨3633605, by rfl⟩ : syracuseStep 4844807 = 7267211) B7267211
theorem B3229871 : Blo 2151435 3229871 := bstep (se 1 (by rfl) ⟨2422403, by rfl⟩ : syracuseStep 3229871 = 4844807) B4844807
theorem B2153247 : Blo 2151435 2153247 := bstep (se 1 (by rfl) ⟨1614935, by rfl⟩ : syracuseStep 2153247 = 3229871) B3229871
theorem B3229877 : Blo 2151435 3229877 := bbase (se 5 (by rfl) ⟨151400, by rfl⟩ : syracuseStep 3229877 = 302801) (by norm_num)
theorem B2153251 : Blo 2151435 2153251 := bstep (se 1 (by rfl) ⟨1614938, by rfl⟩ : syracuseStep 2153251 = 3229877) B3229877
theorem B5450429 : Blo 2151435 5450429 := bbase (se 3 (by rfl) ⟨1021955, by rfl⟩ : syracuseStep 5450429 = 2043911) (by norm_num)
theorem B3633619 : Blo 2151435 3633619 := bstep (se 1 (by rfl) ⟨2725214, by rfl⟩ : syracuseStep 3633619 = 5450429) B5450429
theorem B4844825 : Blo 2151435 4844825 := bstep (se 2 (by rfl) ⟨1816809, by rfl⟩ : syracuseStep 4844825 = 3633619) B3633619
theorem B3229883 : Blo 2151435 3229883 := bstep (se 1 (by rfl) ⟨2422412, by rfl⟩ : syracuseStep 3229883 = 4844825) B4844825
theorem B2153255 : Blo 2151435 2153255 := bstep (se 1 (by rfl) ⟨1614941, by rfl⟩ : syracuseStep 2153255 = 3229883) B3229883
theorem B2422417 : Blo 2151435 2422417 := bbase (se 2 (by rfl) ⟨908406, by rfl⟩ : syracuseStep 2422417 = 1816813) (by norm_num)
theorem B3229889 : Blo 2151435 3229889 := bstep (se 2 (by rfl) ⟨1211208, by rfl⟩ : syracuseStep 3229889 = 2422417) B2422417
theorem B2153259 : Blo 2151435 2153259 := bstep (se 1 (by rfl) ⟨1614944, by rfl⟩ : syracuseStep 2153259 = 3229889) B3229889
theorem B4087837 : Blo 2151435 4087837 := bbase (se 3 (by rfl) ⟨766469, by rfl⟩ : syracuseStep 4087837 = 1532939) (by norm_num)
theorem B5450449 : Blo 2151435 5450449 := bstep (se 2 (by rfl) ⟨2043918, by rfl⟩ : syracuseStep 5450449 = 4087837) B4087837
theorem B7267265 : Blo 2151435 7267265 := bstep (se 2 (by rfl) ⟨2725224, by rfl⟩ : syracuseStep 7267265 = 5450449) B5450449
theorem B4844843 : Blo 2151435 4844843 := bstep (se 1 (by rfl) ⟨3633632, by rfl⟩ : syracuseStep 4844843 = 7267265) B7267265
theorem B3229895 : Blo 2151435 3229895 := bstep (se 1 (by rfl) ⟨2422421, by rfl⟩ : syracuseStep 3229895 = 4844843) B4844843
theorem B2153263 : Blo 2151435 2153263 := bstep (se 1 (by rfl) ⟨1614947, by rfl⟩ : syracuseStep 2153263 = 3229895) B3229895
theorem B3229901 : Blo 2151435 3229901 := bbase (se 3 (by rfl) ⟨605606, by rfl⟩ : syracuseStep 3229901 = 1211213) (by norm_num)
theorem B2153267 : Blo 2151435 2153267 := bstep (se 1 (by rfl) ⟨1614950, by rfl⟩ : syracuseStep 2153267 = 3229901) B3229901
theorem B4844861 : Blo 2151435 4844861 := bbase (se 3 (by rfl) ⟨908411, by rfl⟩ : syracuseStep 4844861 = 1816823) (by norm_num)
theorem B3229907 : Blo 2151435 3229907 := bstep (se 1 (by rfl) ⟨2422430, by rfl⟩ : syracuseStep 3229907 = 4844861) B4844861
theorem B2153271 : Blo 2151435 2153271 := bstep (se 1 (by rfl) ⟨1614953, by rfl⟩ : syracuseStep 2153271 = 3229907) B3229907
theorem B3633653 : Blo 2151435 3633653 := bbase (se 5 (by rfl) ⟨170327, by rfl⟩ : syracuseStep 3633653 = 340655) (by norm_num)
theorem B2422435 : Blo 2151435 2422435 := bstep (se 1 (by rfl) ⟨1816826, by rfl⟩ : syracuseStep 2422435 = 3633653) B3633653
theorem B3229913 : Blo 2151435 3229913 := bstep (se 2 (by rfl) ⟨1211217, by rfl⟩ : syracuseStep 3229913 = 2422435) B2422435
theorem B2153275 : Blo 2151435 2153275 := bstep (se 1 (by rfl) ⟨1614956, by rfl⟩ : syracuseStep 2153275 = 3229913) B3229913
theorem B6898277 : Blo 2151435 6898277 := bbase (se 4 (by rfl) ⟨646713, by rfl⟩ : syracuseStep 6898277 = 1293427) (by norm_num)
theorem B4598851 : Blo 2151435 4598851 := bstep (se 1 (by rfl) ⟨3449138, by rfl⟩ : syracuseStep 4598851 = 6898277) B6898277
theorem B6131801 : Blo 2151435 6131801 := bstep (se 2 (by rfl) ⟨2299425, by rfl⟩ : syracuseStep 6131801 = 4598851) B4598851
theorem B16351469 : Blo 2151435 16351469 := bstep (se 3 (by rfl) ⟨3065900, by rfl⟩ : syracuseStep 16351469 = 6131801) B6131801
theorem B10900979 : Blo 2151435 10900979 := bstep (se 1 (by rfl) ⟨8175734, by rfl⟩ : syracuseStep 10900979 = 16351469) B16351469
theorem B7267319 : Blo 2151435 7267319 := bstep (se 1 (by rfl) ⟨5450489, by rfl⟩ : syracuseStep 7267319 = 10900979) B10900979
theorem B4844879 : Blo 2151435 4844879 := bstep (se 1 (by rfl) ⟨3633659, by rfl⟩ : syracuseStep 4844879 = 7267319) B7267319
theorem B3229919 : Blo 2151435 3229919 := bstep (se 1 (by rfl) ⟨2422439, by rfl⟩ : syracuseStep 3229919 = 4844879) B4844879
theorem B2153279 : Blo 2151435 2153279 := bstep (se 1 (by rfl) ⟨1614959, by rfl⟩ : syracuseStep 2153279 = 3229919) B3229919
theorem B3229925 : Blo 2151435 3229925 := bbase (se 4 (by rfl) ⟨302805, by rfl⟩ : syracuseStep 3229925 = 605611) (by norm_num)
theorem B2153283 : Blo 2151435 2153283 := bstep (se 1 (by rfl) ⟨1614962, by rfl⟩ : syracuseStep 2153283 = 3229925) B3229925
theorem B4598869 : Blo 2151435 4598869 := bbase (se 8 (by rfl) ⟨26946, by rfl⟩ : syracuseStep 4598869 = 53893) (by norm_num)
theorem B6131825 : Blo 2151435 6131825 := bstep (se 2 (by rfl) ⟨2299434, by rfl⟩ : syracuseStep 6131825 = 4598869) B4598869
theorem B4087883 : Blo 2151435 4087883 := bstep (se 1 (by rfl) ⟨3065912, by rfl⟩ : syracuseStep 4087883 = 6131825) B6131825
theorem B2725255 : Blo 2151435 2725255 := bstep (se 1 (by rfl) ⟨2043941, by rfl⟩ : syracuseStep 2725255 = 4087883) B4087883
theorem B3633673 : Blo 2151435 3633673 := bstep (se 2 (by rfl) ⟨1362627, by rfl⟩ : syracuseStep 3633673 = 2725255) B2725255
theorem B4844897 : Blo 2151435 4844897 := bstep (se 2 (by rfl) ⟨1816836, by rfl⟩ : syracuseStep 4844897 = 3633673) B3633673
theorem B3229931 : Blo 2151435 3229931 := bstep (se 1 (by rfl) ⟨2422448, by rfl⟩ : syracuseStep 3229931 = 4844897) B4844897
theorem B2153287 : Blo 2151435 2153287 := bstep (se 1 (by rfl) ⟨1614965, by rfl⟩ : syracuseStep 2153287 = 3229931) B3229931
theorem B2422453 : Blo 2151435 2422453 := bbase (se 5 (by rfl) ⟨113552, by rfl⟩ : syracuseStep 2422453 = 227105) (by norm_num)
theorem B3229937 : Blo 2151435 3229937 := bstep (se 2 (by rfl) ⟨1211226, by rfl⟩ : syracuseStep 3229937 = 2422453) B2422453
theorem B2153291 : Blo 2151435 2153291 := bstep (se 1 (by rfl) ⟨1614968, by rfl⟩ : syracuseStep 2153291 = 3229937) B3229937
theorem B2725265 : Blo 2151435 2725265 := bbase (se 2 (by rfl) ⟨1021974, by rfl⟩ : syracuseStep 2725265 = 2043949) (by norm_num)
theorem B7267373 : Blo 2151435 7267373 := bstep (se 3 (by rfl) ⟨1362632, by rfl⟩ : syracuseStep 7267373 = 2725265) B2725265
theorem B4844915 : Blo 2151435 4844915 := bstep (se 1 (by rfl) ⟨3633686, by rfl⟩ : syracuseStep 4844915 = 7267373) B7267373
theorem B3229943 : Blo 2151435 3229943 := bstep (se 1 (by rfl) ⟨2422457, by rfl⟩ : syracuseStep 3229943 = 4844915) B4844915
theorem B2153295 : Blo 2151435 2153295 := bstep (se 1 (by rfl) ⟨1614971, by rfl⟩ : syracuseStep 2153295 = 3229943) B3229943
theorem B3229949 : Blo 2151435 3229949 := bbase (se 3 (by rfl) ⟨605615, by rfl⟩ : syracuseStep 3229949 = 1211231) (by norm_num)
theorem B2153299 : Blo 2151435 2153299 := bstep (se 1 (by rfl) ⟨1614974, by rfl⟩ : syracuseStep 2153299 = 3229949) B3229949
theorem B4844933 : Blo 2151435 4844933 := bbase (se 4 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 4844933 = 908425) (by norm_num)
theorem B3229955 : Blo 2151435 3229955 := bstep (se 1 (by rfl) ⟨2422466, by rfl⟩ : syracuseStep 3229955 = 4844933) B4844933
theorem B2153303 : Blo 2151435 2153303 := bstep (se 1 (by rfl) ⟨1614977, by rfl⟩ : syracuseStep 2153303 = 3229955) B3229955
theorem B3065941 : Blo 2151435 3065941 := bbase (se 8 (by rfl) ⟨17964, by rfl⟩ : syracuseStep 3065941 = 35929) (by norm_num)
theorem B4087921 : Blo 2151435 4087921 := bstep (se 2 (by rfl) ⟨1532970, by rfl⟩ : syracuseStep 4087921 = 3065941) B3065941
theorem B5450561 : Blo 2151435 5450561 := bstep (se 2 (by rfl) ⟨2043960, by rfl⟩ : syracuseStep 5450561 = 4087921) B4087921
theorem B3633707 : Blo 2151435 3633707 := bstep (se 1 (by rfl) ⟨2725280, by rfl⟩ : syracuseStep 3633707 = 5450561) B5450561
theorem B2422471 : Blo 2151435 2422471 := bstep (se 1 (by rfl) ⟨1816853, by rfl⟩ : syracuseStep 2422471 = 3633707) B3633707
theorem B3229961 : Blo 2151435 3229961 := bstep (se 2 (by rfl) ⟨1211235, by rfl⟩ : syracuseStep 3229961 = 2422471) B2422471
theorem B2153307 : Blo 2151435 2153307 := bstep (se 1 (by rfl) ⟨1614980, by rfl⟩ : syracuseStep 2153307 = 3229961) B3229961
theorem B10901141 : Blo 2151435 10901141 := bbase (se 6 (by rfl) ⟨255495, by rfl⟩ : syracuseStep 10901141 = 510991) (by norm_num)
theorem B7267427 : Blo 2151435 7267427 := bstep (se 1 (by rfl) ⟨5450570, by rfl⟩ : syracuseStep 7267427 = 10901141) B10901141
theorem B4844951 : Blo 2151435 4844951 := bstep (se 1 (by rfl) ⟨3633713, by rfl⟩ : syracuseStep 4844951 = 7267427) B7267427
theorem B3229967 : Blo 2151435 3229967 := bstep (se 1 (by rfl) ⟨2422475, by rfl⟩ : syracuseStep 3229967 = 4844951) B4844951
theorem B2153311 : Blo 2151435 2153311 := bstep (se 1 (by rfl) ⟨1614983, by rfl⟩ : syracuseStep 2153311 = 3229967) B3229967
theorem B3229973 : Blo 2151435 3229973 := bbase (se 6 (by rfl) ⟨75702, by rfl⟩ : syracuseStep 3229973 = 151405) (by norm_num)
theorem B2153315 : Blo 2151435 2153315 := bstep (se 1 (by rfl) ⟨1614986, by rfl⟩ : syracuseStep 2153315 = 3229973) B3229973
theorem B27593621 : Blo 2151435 27593621 := bbase (se 6 (by rfl) ⟨646725, by rfl⟩ : syracuseStep 27593621 = 1293451) (by norm_num)
theorem B18395747 : Blo 2151435 18395747 := bstep (se 1 (by rfl) ⟨13796810, by rfl⟩ : syracuseStep 18395747 = 27593621) B27593621
theorem B12263831 : Blo 2151435 12263831 := bstep (se 1 (by rfl) ⟨9197873, by rfl⟩ : syracuseStep 12263831 = 18395747) B18395747
theorem B8175887 : Blo 2151435 8175887 := bstep (se 1 (by rfl) ⟨6131915, by rfl⟩ : syracuseStep 8175887 = 12263831) B12263831
theorem B5450591 : Blo 2151435 5450591 := bstep (se 1 (by rfl) ⟨4087943, by rfl⟩ : syracuseStep 5450591 = 8175887) B8175887
theorem B3633727 : Blo 2151435 3633727 := bstep (se 1 (by rfl) ⟨2725295, by rfl⟩ : syracuseStep 3633727 = 5450591) B5450591
theorem B4844969 : Blo 2151435 4844969 := bstep (se 2 (by rfl) ⟨1816863, by rfl⟩ : syracuseStep 4844969 = 3633727) B3633727
theorem B3229979 : Blo 2151435 3229979 := bstep (se 1 (by rfl) ⟨2422484, by rfl⟩ : syracuseStep 3229979 = 4844969) B4844969
theorem B2153319 : Blo 2151435 2153319 := bstep (se 1 (by rfl) ⟨1614989, by rfl⟩ : syracuseStep 2153319 = 3229979) B3229979
theorem B2422489 : Blo 2151435 2422489 := bbase (se 2 (by rfl) ⟨908433, by rfl⟩ : syracuseStep 2422489 = 1816867) (by norm_num)
theorem B3229985 : Blo 2151435 3229985 := bstep (se 2 (by rfl) ⟨1211244, by rfl⟩ : syracuseStep 3229985 = 2422489) B2422489
theorem B2153323 : Blo 2151435 2153323 := bstep (se 1 (by rfl) ⟨1614992, by rfl⟩ : syracuseStep 2153323 = 3229985) B3229985
theorem B2299477 : Blo 2151435 2299477 := bbase (se 8 (by rfl) ⟨13473, by rfl⟩ : syracuseStep 2299477 = 26947) (by norm_num)
theorem B3065969 : Blo 2151435 3065969 := bstep (se 2 (by rfl) ⟨1149738, by rfl⟩ : syracuseStep 3065969 = 2299477) B2299477
theorem B8175917 : Blo 2151435 8175917 := bstep (se 3 (by rfl) ⟨1532984, by rfl⟩ : syracuseStep 8175917 = 3065969) B3065969
theorem B5450611 : Blo 2151435 5450611 := bstep (se 1 (by rfl) ⟨4087958, by rfl⟩ : syracuseStep 5450611 = 8175917) B8175917
theorem B7267481 : Blo 2151435 7267481 := bstep (se 2 (by rfl) ⟨2725305, by rfl⟩ : syracuseStep 7267481 = 5450611) B5450611
theorem B4844987 : Blo 2151435 4844987 := bstep (se 1 (by rfl) ⟨3633740, by rfl⟩ : syracuseStep 4844987 = 7267481) B7267481
theorem B3229991 : Blo 2151435 3229991 := bstep (se 1 (by rfl) ⟨2422493, by rfl⟩ : syracuseStep 3229991 = 4844987) B4844987
theorem B2153327 : Blo 2151435 2153327 := bstep (se 1 (by rfl) ⟨1614995, by rfl⟩ : syracuseStep 2153327 = 3229991) B3229991
theorem B3229997 : Blo 2151435 3229997 := bbase (se 3 (by rfl) ⟨605624, by rfl⟩ : syracuseStep 3229997 = 1211249) (by norm_num)
theorem B2153331 : Blo 2151435 2153331 := bstep (se 1 (by rfl) ⟨1614998, by rfl⟩ : syracuseStep 2153331 = 3229997) B3229997
theorem B4845005 : Blo 2151435 4845005 := bbase (se 3 (by rfl) ⟨908438, by rfl⟩ : syracuseStep 4845005 = 1816877) (by norm_num)
theorem B3230003 : Blo 2151435 3230003 := bstep (se 1 (by rfl) ⟨2422502, by rfl⟩ : syracuseStep 3230003 = 4845005) B4845005
theorem B2153335 : Blo 2151435 2153335 := bstep (se 1 (by rfl) ⟨1615001, by rfl⟩ : syracuseStep 2153335 = 3230003) B3230003
theorem B2725321 : Blo 2151435 2725321 := bbase (se 2 (by rfl) ⟨1021995, by rfl⟩ : syracuseStep 2725321 = 2043991) (by norm_num)
theorem B3633761 : Blo 2151435 3633761 := bstep (se 2 (by rfl) ⟨1362660, by rfl⟩ : syracuseStep 3633761 = 2725321) B2725321
theorem B2422507 : Blo 2151435 2422507 := bstep (se 1 (by rfl) ⟨1816880, by rfl⟩ : syracuseStep 2422507 = 3633761) B3633761
theorem B3230009 : Blo 2151435 3230009 := bstep (se 2 (by rfl) ⟨1211253, by rfl⟩ : syracuseStep 3230009 = 2422507) B2422507
theorem B2153339 : Blo 2151435 2153339 := bstep (se 1 (by rfl) ⟨1615004, by rfl⟩ : syracuseStep 2153339 = 3230009) B3230009
theorem B20695445 : Blo 2151435 20695445 := bbase (se 6 (by rfl) ⟨485049, by rfl⟩ : syracuseStep 20695445 = 970099) (by norm_num)
theorem B13796963 : Blo 2151435 13796963 := bstep (se 1 (by rfl) ⟨10347722, by rfl⟩ : syracuseStep 13796963 = 20695445) B20695445
theorem B9197975 : Blo 2151435 9197975 := bstep (se 1 (by rfl) ⟨6898481, by rfl⟩ : syracuseStep 9197975 = 13796963) B13796963
theorem B24527933 : Blo 2151435 24527933 := bstep (se 3 (by rfl) ⟨4598987, by rfl⟩ : syracuseStep 24527933 = 9197975) B9197975
theorem B16351955 : Blo 2151435 16351955 := bstep (se 1 (by rfl) ⟨12263966, by rfl⟩ : syracuseStep 16351955 = 24527933) B24527933
theorem B10901303 : Blo 2151435 10901303 := bstep (se 1 (by rfl) ⟨8175977, by rfl⟩ : syracuseStep 10901303 = 16351955) B16351955
theorem B7267535 : Blo 2151435 7267535 := bstep (se 1 (by rfl) ⟨5450651, by rfl⟩ : syracuseStep 7267535 = 10901303) B10901303
theorem B4845023 : Blo 2151435 4845023 := bstep (se 1 (by rfl) ⟨3633767, by rfl⟩ : syracuseStep 4845023 = 7267535) B7267535
theorem B3230015 : Blo 2151435 3230015 := bstep (se 1 (by rfl) ⟨2422511, by rfl⟩ : syracuseStep 3230015 = 4845023) B4845023
theorem B2153343 : Blo 2151435 2153343 := bstep (se 1 (by rfl) ⟨1615007, by rfl⟩ : syracuseStep 2153343 = 3230015) B3230015
theorem B3230021 : Blo 2151435 3230021 := bbase (se 4 (by rfl) ⟨302814, by rfl⟩ : syracuseStep 3230021 = 605629) (by norm_num)
theorem B2153347 : Blo 2151435 2153347 := bstep (se 1 (by rfl) ⟨1615010, by rfl⟩ : syracuseStep 2153347 = 3230021) B3230021
theorem B3633781 : Blo 2151435 3633781 := bbase (se 5 (by rfl) ⟨170333, by rfl⟩ : syracuseStep 3633781 = 340667) (by norm_num)
theorem B4845041 : Blo 2151435 4845041 := bstep (se 2 (by rfl) ⟨1816890, by rfl⟩ : syracuseStep 4845041 = 3633781) B3633781
theorem B3230027 : Blo 2151435 3230027 := bstep (se 1 (by rfl) ⟨2422520, by rfl⟩ : syracuseStep 3230027 = 4845041) B4845041
theorem B2153351 : Blo 2151435 2153351 := bstep (se 1 (by rfl) ⟨1615013, by rfl⟩ : syracuseStep 2153351 = 3230027) B3230027
theorem B2422525 : Blo 2151435 2422525 := bbase (se 3 (by rfl) ⟨454223, by rfl⟩ : syracuseStep 2422525 = 908447) (by norm_num)
theorem B3230033 : Blo 2151435 3230033 := bstep (se 2 (by rfl) ⟨1211262, by rfl⟩ : syracuseStep 3230033 = 2422525) B2422525
theorem B2153355 : Blo 2151435 2153355 := bstep (se 1 (by rfl) ⟨1615016, by rfl⟩ : syracuseStep 2153355 = 3230033) B3230033
theorem B7267589 : Blo 2151435 7267589 := bbase (se 4 (by rfl) ⟨681336, by rfl⟩ : syracuseStep 7267589 = 1362673) (by norm_num)
theorem B4845059 : Blo 2151435 4845059 := bstep (se 1 (by rfl) ⟨3633794, by rfl⟩ : syracuseStep 4845059 = 7267589) B7267589
theorem B3230039 : Blo 2151435 3230039 := bstep (se 1 (by rfl) ⟨2422529, by rfl⟩ : syracuseStep 3230039 = 4845059) B4845059
theorem B2153359 : Blo 2151435 2153359 := bstep (se 1 (by rfl) ⟨1615019, by rfl⟩ : syracuseStep 2153359 = 3230039) B3230039
theorem B3230045 : Blo 2151435 3230045 := bbase (se 3 (by rfl) ⟨605633, by rfl⟩ : syracuseStep 3230045 = 1211267) (by norm_num)
theorem B2153363 : Blo 2151435 2153363 := bstep (se 1 (by rfl) ⟨1615022, by rfl⟩ : syracuseStep 2153363 = 3230045) B3230045
theorem B4845077 : Blo 2151435 4845077 := bbase (se 6 (by rfl) ⟨113556, by rfl⟩ : syracuseStep 4845077 = 227113) (by norm_num)
theorem B3230051 : Blo 2151435 3230051 := bstep (se 1 (by rfl) ⟨2422538, by rfl⟩ : syracuseStep 3230051 = 4845077) B4845077
theorem B2153367 : Blo 2151435 2153367 := bstep (se 1 (by rfl) ⟨1615025, by rfl⟩ : syracuseStep 2153367 = 3230051) B3230051
theorem B8176085 : Blo 2151435 8176085 := bbase (se 7 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 8176085 = 191627) (by norm_num)
theorem B5450723 : Blo 2151435 5450723 := bstep (se 1 (by rfl) ⟨4088042, by rfl⟩ : syracuseStep 5450723 = 8176085) B8176085
theorem B3633815 : Blo 2151435 3633815 := bstep (se 1 (by rfl) ⟨2725361, by rfl⟩ : syracuseStep 3633815 = 5450723) B5450723
theorem B2422543 : Blo 2151435 2422543 := bstep (se 1 (by rfl) ⟨1816907, by rfl⟩ : syracuseStep 2422543 = 3633815) B3633815
theorem B3230057 : Blo 2151435 3230057 := bstep (se 2 (by rfl) ⟨1211271, by rfl⟩ : syracuseStep 3230057 = 2422543) B2422543
theorem B2153371 : Blo 2151435 2153371 := bstep (se 1 (by rfl) ⟨1615028, by rfl⟩ : syracuseStep 2153371 = 3230057) B3230057
theorem B12264149 : Blo 2151435 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B8176099 : Blo 2151435 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B10901465 : Blo 2151435 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B7267643 : Blo 2151435 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B4845095 : Blo 2151435 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B3230063 : Blo 2151435 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B2153375 : Blo 2151435 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B3230069 : Blo 2151435 3230069 := bbase (se 5 (by rfl) ⟨151409, by rfl⟩ : syracuseStep 3230069 = 302819) (by norm_num)
theorem B2153379 : Blo 2151435 2153379 := bstep (se 1 (by rfl) ⟨1615034, by rfl⟩ : syracuseStep 2153379 = 3230069) B3230069
theorem B2299537 : Blo 2151435 2299537 := bbase (se 2 (by rfl) ⟨862326, by rfl⟩ : syracuseStep 2299537 = 1724653) (by norm_num)
theorem B3066049 : Blo 2151435 3066049 := bstep (se 2 (by rfl) ⟨1149768, by rfl⟩ : syracuseStep 3066049 = 2299537) B2299537
theorem B4088065 : Blo 2151435 4088065 := bstep (se 2 (by rfl) ⟨1533024, by rfl⟩ : syracuseStep 4088065 = 3066049) B3066049
theorem B5450753 : Blo 2151435 5450753 := bstep (se 2 (by rfl) ⟨2044032, by rfl⟩ : syracuseStep 5450753 = 4088065) B4088065
theorem B3633835 : Blo 2151435 3633835 := bstep (se 1 (by rfl) ⟨2725376, by rfl⟩ : syracuseStep 3633835 = 5450753) B5450753
theorem B4845113 : Blo 2151435 4845113 := bstep (se 2 (by rfl) ⟨1816917, by rfl⟩ : syracuseStep 4845113 = 3633835) B3633835
theorem B3230075 : Blo 2151435 3230075 := bstep (se 1 (by rfl) ⟨2422556, by rfl⟩ : syracuseStep 3230075 = 4845113) B4845113
theorem B2153383 : Blo 2151435 2153383 := bstep (se 1 (by rfl) ⟨1615037, by rfl⟩ : syracuseStep 2153383 = 3230075) B3230075
theorem B2422561 : Blo 2151435 2422561 := bbase (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) (by norm_num)
theorem B3230081 : Blo 2151435 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B2153387 : Blo 2151435 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B5450773 : Blo 2151435 5450773 := bbase (se 6 (by rfl) ⟨127752, by rfl⟩ : syracuseStep 5450773 = 255505) (by norm_num)
theorem B7267697 : Blo 2151435 7267697 := bstep (se 2 (by rfl) ⟨2725386, by rfl⟩ : syracuseStep 7267697 = 5450773) B5450773
theorem B4845131 : Blo 2151435 4845131 := bstep (se 1 (by rfl) ⟨3633848, by rfl⟩ : syracuseStep 4845131 = 7267697) B7267697
theorem B3230087 : Blo 2151435 3230087 := bstep (se 1 (by rfl) ⟨2422565, by rfl⟩ : syracuseStep 3230087 = 4845131) B4845131
theorem B2153391 : Blo 2151435 2153391 := bstep (se 1 (by rfl) ⟨1615043, by rfl⟩ : syracuseStep 2153391 = 3230087) B3230087
theorem B3230093 : Blo 2151435 3230093 := bbase (se 3 (by rfl) ⟨605642, by rfl⟩ : syracuseStep 3230093 = 1211285) (by norm_num)
theorem B2153395 : Blo 2151435 2153395 := bstep (se 1 (by rfl) ⟨1615046, by rfl⟩ : syracuseStep 2153395 = 3230093) B3230093
theorem B4845149 : Blo 2151435 4845149 := bbase (se 3 (by rfl) ⟨908465, by rfl⟩ : syracuseStep 4845149 = 1816931) (by norm_num)
theorem B3230099 : Blo 2151435 3230099 := bstep (se 1 (by rfl) ⟨2422574, by rfl⟩ : syracuseStep 3230099 = 4845149) B4845149
theorem B2153399 : Blo 2151435 2153399 := bstep (se 1 (by rfl) ⟨1615049, by rfl⟩ : syracuseStep 2153399 = 3230099) B3230099
theorem B3633869 : Blo 2151435 3633869 := bbase (se 3 (by rfl) ⟨681350, by rfl⟩ : syracuseStep 3633869 = 1362701) (by norm_num)
theorem B2422579 : Blo 2151435 2422579 := bstep (se 1 (by rfl) ⟨1816934, by rfl⟩ : syracuseStep 2422579 = 3633869) B3633869
theorem B3230105 : Blo 2151435 3230105 := bstep (se 2 (by rfl) ⟨1211289, by rfl⟩ : syracuseStep 3230105 = 2422579) B2422579
theorem B2153403 : Blo 2151435 2153403 := bstep (se 1 (by rfl) ⟨1615052, by rfl⟩ : syracuseStep 2153403 = 3230105) B3230105
theorem B2990341 : Blo 2151435 2990341 := bbase (se 4 (by rfl) ⟨280344, by rfl⟩ : syracuseStep 2990341 = 560689) (by norm_num)
theorem B15948485 : Blo 2151435 15948485 := bstep (se 4 (by rfl) ⟨1495170, by rfl⟩ : syracuseStep 15948485 = 2990341) B2990341
theorem B10632323 : Blo 2151435 10632323 := bstep (se 1 (by rfl) ⟨7974242, by rfl⟩ : syracuseStep 10632323 = 15948485) B15948485
theorem B28352861 : Blo 2151435 28352861 := bstep (se 3 (by rfl) ⟨5316161, by rfl⟩ : syracuseStep 28352861 = 10632323) B10632323
theorem B18901907 : Blo 2151435 18901907 := bstep (se 1 (by rfl) ⟨14176430, by rfl⟩ : syracuseStep 18901907 = 28352861) B28352861
theorem B12601271 : Blo 2151435 12601271 := bstep (se 1 (by rfl) ⟨9450953, by rfl⟩ : syracuseStep 12601271 = 18901907) B18901907
theorem B8400847 : Blo 2151435 8400847 := bstep (se 1 (by rfl) ⟨6300635, by rfl⟩ : syracuseStep 8400847 = 12601271) B12601271
theorem B11201129 : Blo 2151435 11201129 := bstep (se 2 (by rfl) ⟨4200423, by rfl⟩ : syracuseStep 11201129 = 8400847) B8400847
theorem B7467419 : Blo 2151435 7467419 := bstep (se 1 (by rfl) ⟨5600564, by rfl⟩ : syracuseStep 7467419 = 11201129) B11201129
theorem B4978279 : Blo 2151435 4978279 := bstep (se 1 (by rfl) ⟨3733709, by rfl⟩ : syracuseStep 4978279 = 7467419) B7467419
theorem B26550821 : Blo 2151435 26550821 := bstep (se 4 (by rfl) ⟨2489139, by rfl⟩ : syracuseStep 26550821 = 4978279) B4978279
theorem B70802189 : Blo 2151435 70802189 := bstep (se 3 (by rfl) ⟨13275410, by rfl⟩ : syracuseStep 70802189 = 26550821) B26550821
theorem B47201459 : Blo 2151435 47201459 := bstep (se 1 (by rfl) ⟨35401094, by rfl⟩ : syracuseStep 47201459 = 70802189) B70802189
theorem B125870557 : Blo 2151435 125870557 := bstep (se 3 (by rfl) ⟨23600729, by rfl⟩ : syracuseStep 125870557 = 47201459) B47201459
theorem B167827409 : Blo 2151435 167827409 := bstep (se 2 (by rfl) ⟨62935278, by rfl⟩ : syracuseStep 167827409 = 125870557) B125870557
theorem B111884939 : Blo 2151435 111884939 := bstep (se 1 (by rfl) ⟨83913704, by rfl⟩ : syracuseStep 111884939 = 167827409) B167827409
theorem B74589959 : Blo 2151435 74589959 := bstep (se 1 (by rfl) ⟨55942469, by rfl⟩ : syracuseStep 74589959 = 111884939) B111884939
theorem B49726639 : Blo 2151435 49726639 := bstep (se 1 (by rfl) ⟨37294979, by rfl⟩ : syracuseStep 49726639 = 74589959) B74589959
theorem B66302185 : Blo 2151435 66302185 := bstep (se 2 (by rfl) ⟨24863319, by rfl⟩ : syracuseStep 66302185 = 49726639) B49726639
theorem B88402913 : Blo 2151435 88402913 := bstep (se 2 (by rfl) ⟨33151092, by rfl⟩ : syracuseStep 88402913 = 66302185) B66302185
theorem B58935275 : Blo 2151435 58935275 := bstep (se 1 (by rfl) ⟨44201456, by rfl⟩ : syracuseStep 58935275 = 88402913) B88402913
theorem B39290183 : Blo 2151435 39290183 := bstep (se 1 (by rfl) ⟨29467637, by rfl⟩ : syracuseStep 39290183 = 58935275) B58935275
theorem B26193455 : Blo 2151435 26193455 := bstep (se 1 (by rfl) ⟨19645091, by rfl⟩ : syracuseStep 26193455 = 39290183) B39290183
theorem B17462303 : Blo 2151435 17462303 := bstep (se 1 (by rfl) ⟨13096727, by rfl⟩ : syracuseStep 17462303 = 26193455) B26193455
theorem B11641535 : Blo 2151435 11641535 := bstep (se 1 (by rfl) ⟨8731151, by rfl⟩ : syracuseStep 11641535 = 17462303) B17462303
theorem B7761023 : Blo 2151435 7761023 := bstep (se 1 (by rfl) ⟨5820767, by rfl⟩ : syracuseStep 7761023 = 11641535) B11641535
theorem B5174015 : Blo 2151435 5174015 := bstep (se 1 (by rfl) ⟨3880511, by rfl⟩ : syracuseStep 5174015 = 7761023) B7761023
theorem B13797373 : Blo 2151435 13797373 := bstep (se 3 (by rfl) ⟨2587007, by rfl⟩ : syracuseStep 13797373 = 5174015) B5174015
theorem B18396497 : Blo 2151435 18396497 := bstep (se 2 (by rfl) ⟨6898686, by rfl⟩ : syracuseStep 18396497 = 13797373) B13797373
theorem B12264331 : Blo 2151435 12264331 := bstep (se 1 (by rfl) ⟨9198248, by rfl⟩ : syracuseStep 12264331 = 18396497) B18396497
theorem B16352441 : Blo 2151435 16352441 := bstep (se 2 (by rfl) ⟨6132165, by rfl⟩ : syracuseStep 16352441 = 12264331) B12264331
theorem B10901627 : Blo 2151435 10901627 := bstep (se 1 (by rfl) ⟨8176220, by rfl⟩ : syracuseStep 10901627 = 16352441) B16352441
theorem B7267751 : Blo 2151435 7267751 := bstep (se 1 (by rfl) ⟨5450813, by rfl⟩ : syracuseStep 7267751 = 10901627) B10901627
theorem B4845167 : Blo 2151435 4845167 := bstep (se 1 (by rfl) ⟨3633875, by rfl⟩ : syracuseStep 4845167 = 7267751) B7267751
theorem B3230111 : Blo 2151435 3230111 := bstep (se 1 (by rfl) ⟨2422583, by rfl⟩ : syracuseStep 3230111 = 4845167) B4845167
theorem B2153407 : Blo 2151435 2153407 := bstep (se 1 (by rfl) ⟨1615055, by rfl⟩ : syracuseStep 2153407 = 3230111) B3230111
theorem B3230117 : Blo 2151435 3230117 := bbase (se 4 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 3230117 = 605647) (by norm_num)
theorem B2153411 : Blo 2151435 2153411 := bstep (se 1 (by rfl) ⟨1615058, by rfl⟩ : syracuseStep 2153411 = 3230117) B3230117
theorem B2725417 : Blo 2151435 2725417 := bbase (se 2 (by rfl) ⟨1022031, by rfl⟩ : syracuseStep 2725417 = 2044063) (by norm_num)
theorem B3633889 : Blo 2151435 3633889 := bstep (se 2 (by rfl) ⟨1362708, by rfl⟩ : syracuseStep 3633889 = 2725417) B2725417
theorem B4845185 : Blo 2151435 4845185 := bstep (se 2 (by rfl) ⟨1816944, by rfl⟩ : syracuseStep 4845185 = 3633889) B3633889
theorem B3230123 : Blo 2151435 3230123 := bstep (se 1 (by rfl) ⟨2422592, by rfl⟩ : syracuseStep 3230123 = 4845185) B4845185
theorem B2153415 : Blo 2151435 2153415 := bstep (se 1 (by rfl) ⟨1615061, by rfl⟩ : syracuseStep 2153415 = 3230123) B3230123
theorem B2422597 : Blo 2151435 2422597 := bbase (se 4 (by rfl) ⟨227118, by rfl⟩ : syracuseStep 2422597 = 454237) (by norm_num)
theorem B3230129 : Blo 2151435 3230129 := bstep (se 2 (by rfl) ⟨1211298, by rfl⟩ : syracuseStep 3230129 = 2422597) B2422597
theorem B2153419 : Blo 2151435 2153419 := bstep (se 1 (by rfl) ⟨1615064, by rfl⟩ : syracuseStep 2153419 = 3230129) B3230129
theorem B4088141 : Blo 2151435 4088141 := bbase (se 3 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 4088141 = 1533053) (by norm_num)
theorem B2725427 : Blo 2151435 2725427 := bstep (se 1 (by rfl) ⟨2044070, by rfl⟩ : syracuseStep 2725427 = 4088141) B4088141
theorem B7267805 : Blo 2151435 7267805 := bstep (se 3 (by rfl) ⟨1362713, by rfl⟩ : syracuseStep 7267805 = 2725427) B2725427
theorem B4845203 : Blo 2151435 4845203 := bstep (se 1 (by rfl) ⟨3633902, by rfl⟩ : syracuseStep 4845203 = 7267805) B7267805
theorem B3230135 : Blo 2151435 3230135 := bstep (se 1 (by rfl) ⟨2422601, by rfl⟩ : syracuseStep 3230135 = 4845203) B4845203
theorem B2153423 : Blo 2151435 2153423 := bstep (se 1 (by rfl) ⟨1615067, by rfl⟩ : syracuseStep 2153423 = 3230135) B3230135
theorem B3230141 : Blo 2151435 3230141 := bbase (se 3 (by rfl) ⟨605651, by rfl⟩ : syracuseStep 3230141 = 1211303) (by norm_num)
theorem B2153427 : Blo 2151435 2153427 := bstep (se 1 (by rfl) ⟨1615070, by rfl⟩ : syracuseStep 2153427 = 3230141) B3230141
theorem B4845221 : Blo 2151435 4845221 := bbase (se 4 (by rfl) ⟨454239, by rfl⟩ : syracuseStep 4845221 = 908479) (by norm_num)
theorem B3230147 : Blo 2151435 3230147 := bstep (se 1 (by rfl) ⟨2422610, by rfl⟩ : syracuseStep 3230147 = 4845221) B4845221
theorem B2153431 : Blo 2151435 2153431 := bstep (se 1 (by rfl) ⟨1615073, by rfl⟩ : syracuseStep 2153431 = 3230147) B3230147
theorem B5450885 : Blo 2151435 5450885 := bbase (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) (by norm_num)
theorem B3633923 : Blo 2151435 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B2422615 : Blo 2151435 2422615 := bstep (se 1 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 2422615 = 3633923) B3633923
theorem B3230153 : Blo 2151435 3230153 := bstep (se 2 (by rfl) ⟨1211307, by rfl⟩ : syracuseStep 3230153 = 2422615) B2422615
theorem B2153435 : Blo 2151435 2153435 := bstep (se 1 (by rfl) ⟨1615076, by rfl⟩ : syracuseStep 2153435 = 3230153) B3230153
theorem C0 (j : ℕ) (h1 : 537858 ≤ j) (h2 : j ≤ 538358) : Blo 2151435 (4 * j + 3) := by
  interval_cases j
  · exact B2151435
  · exact B2151439
  · exact B2151443
  · exact B2151447
  · exact B2151451
  · exact B2151455
  · exact B2151459
  · exact B2151463
  · exact B2151467
  · exact B2151471
  · exact B2151475
  · exact B2151479
  · exact B2151483
  · exact B2151487
  · exact B2151491
  · exact B2151495
  · exact B2151499
  · exact B2151503
  · exact B2151507
  · exact B2151511
  · exact B2151515
  · exact B2151519
  · exact B2151523
  · exact B2151527
  · exact B2151531
  · exact B2151535
  · exact B2151539
  · exact B2151543
  · exact B2151547
  · exact B2151551
  · exact B2151555
  · exact B2151559
  · exact B2151563
  · exact B2151567
  · exact B2151571
  · exact B2151575
  · exact B2151579
  · exact B2151583
  · exact B2151587
  · exact B2151591
  · exact B2151595
  · exact B2151599
  · exact B2151603
  · exact B2151607
  · exact B2151611
  · exact B2151615
  · exact B2151619
  · exact B2151623
  · exact B2151627
  · exact B2151631
  · exact B2151635
  · exact B2151639
  · exact B2151643
  · exact B2151647
  · exact B2151651
  · exact B2151655
  · exact B2151659
  · exact B2151663
  · exact B2151667
  · exact B2151671
  · exact B2151675
  · exact B2151679
  · exact B2151683
  · exact B2151687
  · exact B2151691
  · exact B2151695
  · exact B2151699
  · exact B2151703
  · exact B2151707
  · exact B2151711
  · exact B2151715
  · exact B2151719
  · exact B2151723
  · exact B2151727
  · exact B2151731
  · exact B2151735
  · exact B2151739
  · exact B2151743
  · exact B2151747
  · exact B2151751
  · exact B2151755
  · exact B2151759
  · exact B2151763
  · exact B2151767
  · exact B2151771
  · exact B2151775
  · exact B2151779
  · exact B2151783
  · exact B2151787
  · exact B2151791
  · exact B2151795
  · exact B2151799
  · exact B2151803
  · exact B2151807
  · exact B2151811
  · exact B2151815
  · exact B2151819
  · exact B2151823
  · exact B2151827
  · exact B2151831
  · exact B2151835
  · exact B2151839
  · exact B2151843
  · exact B2151847
  · exact B2151851
  · exact B2151855
  · exact B2151859
  · exact B2151863
  · exact B2151867
  · exact B2151871
  · exact B2151875
  · exact B2151879
  · exact B2151883
  · exact B2151887
  · exact B2151891
  · exact B2151895
  · exact B2151899
  · exact B2151903
  · exact B2151907
  · exact B2151911
  · exact B2151915
  · exact B2151919
  · exact B2151923
  · exact B2151927
  · exact B2151931
  · exact B2151935
  · exact B2151939
  · exact B2151943
  · exact B2151947
  · exact B2151951
  · exact B2151955
  · exact B2151959
  · exact B2151963
  · exact B2151967
  · exact B2151971
  · exact B2151975
  · exact B2151979
  · exact B2151983
  · exact B2151987
  · exact B2151991
  · exact B2151995
  · exact B2151999
  · exact B2152003
  · exact B2152007
  · exact B2152011
  · exact B2152015
  · exact B2152019
  · exact B2152023
  · exact B2152027
  · exact B2152031
  · exact B2152035
  · exact B2152039
  · exact B2152043
  · exact B2152047
  · exact B2152051
  · exact B2152055
  · exact B2152059
  · exact B2152063
  · exact B2152067
  · exact B2152071
  · exact B2152075
  · exact B2152079
  · exact B2152083
  · exact B2152087
  · exact B2152091
  · exact B2152095
  · exact B2152099
  · exact B2152103
  · exact B2152107
  · exact B2152111
  · exact B2152115
  · exact B2152119
  · exact B2152123
  · exact B2152127
  · exact B2152131
  · exact B2152135
  · exact B2152139
  · exact B2152143
  · exact B2152147
  · exact B2152151
  · exact B2152155
  · exact B2152159
  · exact B2152163
  · exact B2152167
  · exact B2152171
  · exact B2152175
  · exact B2152179
  · exact B2152183
  · exact B2152187
  · exact B2152191
  · exact B2152195
  · exact B2152199
  · exact B2152203
  · exact B2152207
  · exact B2152211
  · exact B2152215
  · exact B2152219
  · exact B2152223
  · exact B2152227
  · exact B2152231
  · exact B2152235
  · exact B2152239
  · exact B2152243
  · exact B2152247
  · exact B2152251
  · exact B2152255
  · exact B2152259
  · exact B2152263
  · exact B2152267
  · exact B2152271
  · exact B2152275
  · exact B2152279
  · exact B2152283
  · exact B2152287
  · exact B2152291
  · exact B2152295
  · exact B2152299
  · exact B2152303
  · exact B2152307
  · exact B2152311
  · exact B2152315
  · exact B2152319
  · exact B2152323
  · exact B2152327
  · exact B2152331
  · exact B2152335
  · exact B2152339
  · exact B2152343
  · exact B2152347
  · exact B2152351
  · exact B2152355
  · exact B2152359
  · exact B2152363
  · exact B2152367
  · exact B2152371
  · exact B2152375
  · exact B2152379
  · exact B2152383
  · exact B2152387
  · exact B2152391
  · exact B2152395
  · exact B2152399
  · exact B2152403
  · exact B2152407
  · exact B2152411
  · exact B2152415
  · exact B2152419
  · exact B2152423
  · exact B2152427
  · exact B2152431
  · exact B2152435
  · exact B2152439
  · exact B2152443
  · exact B2152447
  · exact B2152451
  · exact B2152455
  · exact B2152459
  · exact B2152463
  · exact B2152467
  · exact B2152471
  · exact B2152475
  · exact B2152479
  · exact B2152483
  · exact B2152487
  · exact B2152491
  · exact B2152495
  · exact B2152499
  · exact B2152503
  · exact B2152507
  · exact B2152511
  · exact B2152515
  · exact B2152519
  · exact B2152523
  · exact B2152527
  · exact B2152531
  · exact B2152535
  · exact B2152539
  · exact B2152543
  · exact B2152547
  · exact B2152551
  · exact B2152555
  · exact B2152559
  · exact B2152563
  · exact B2152567
  · exact B2152571
  · exact B2152575
  · exact B2152579
  · exact B2152583
  · exact B2152587
  · exact B2152591
  · exact B2152595
  · exact B2152599
  · exact B2152603
  · exact B2152607
  · exact B2152611
  · exact B2152615
  · exact B2152619
  · exact B2152623
  · exact B2152627
  · exact B2152631
  · exact B2152635
  · exact B2152639
  · exact B2152643
  · exact B2152647
  · exact B2152651
  · exact B2152655
  · exact B2152659
  · exact B2152663
  · exact B2152667
  · exact B2152671
  · exact B2152675
  · exact B2152679
  · exact B2152683
  · exact B2152687
  · exact B2152691
  · exact B2152695
  · exact B2152699
  · exact B2152703
  · exact B2152707
  · exact B2152711
  · exact B2152715
  · exact B2152719
  · exact B2152723
  · exact B2152727
  · exact B2152731
  · exact B2152735
  · exact B2152739
  · exact B2152743
  · exact B2152747
  · exact B2152751
  · exact B2152755
  · exact B2152759
  · exact B2152763
  · exact B2152767
  · exact B2152771
  · exact B2152775
  · exact B2152779
  · exact B2152783
  · exact B2152787
  · exact B2152791
  · exact B2152795
  · exact B2152799
  · exact B2152803
  · exact B2152807
  · exact B2152811
  · exact B2152815
  · exact B2152819
  · exact B2152823
  · exact B2152827
  · exact B2152831
  · exact B2152835
  · exact B2152839
  · exact B2152843
  · exact B2152847
  · exact B2152851
  · exact B2152855
  · exact B2152859
  · exact B2152863
  · exact B2152867
  · exact B2152871
  · exact B2152875
  · exact B2152879
  · exact B2152883
  · exact B2152887
  · exact B2152891
  · exact B2152895
  · exact B2152899
  · exact B2152903
  · exact B2152907
  · exact B2152911
  · exact B2152915
  · exact B2152919
  · exact B2152923
  · exact B2152927
  · exact B2152931
  · exact B2152935
  · exact B2152939
  · exact B2152943
  · exact B2152947
  · exact B2152951
  · exact B2152955
  · exact B2152959
  · exact B2152963
  · exact B2152967
  · exact B2152971
  · exact B2152975
  · exact B2152979
  · exact B2152983
  · exact B2152987
  · exact B2152991
  · exact B2152995
  · exact B2152999
  · exact B2153003
  · exact B2153007
  · exact B2153011
  · exact B2153015
  · exact B2153019
  · exact B2153023
  · exact B2153027
  · exact B2153031
  · exact B2153035
  · exact B2153039
  · exact B2153043
  · exact B2153047
  · exact B2153051
  · exact B2153055
  · exact B2153059
  · exact B2153063
  · exact B2153067
  · exact B2153071
  · exact B2153075
  · exact B2153079
  · exact B2153083
  · exact B2153087
  · exact B2153091
  · exact B2153095
  · exact B2153099
  · exact B2153103
  · exact B2153107
  · exact B2153111
  · exact B2153115
  · exact B2153119
  · exact B2153123
  · exact B2153127
  · exact B2153131
  · exact B2153135
  · exact B2153139
  · exact B2153143
  · exact B2153147
  · exact B2153151
  · exact B2153155
  · exact B2153159
  · exact B2153163
  · exact B2153167
  · exact B2153171
  · exact B2153175
  · exact B2153179
  · exact B2153183
  · exact B2153187
  · exact B2153191
  · exact B2153195
  · exact B2153199
  · exact B2153203
  · exact B2153207
  · exact B2153211
  · exact B2153215
  · exact B2153219
  · exact B2153223
  · exact B2153227
  · exact B2153231
  · exact B2153235
  · exact B2153239
  · exact B2153243
  · exact B2153247
  · exact B2153251
  · exact B2153255
  · exact B2153259
  · exact B2153263
  · exact B2153267
  · exact B2153271
  · exact B2153275
  · exact B2153279
  · exact B2153283
  · exact B2153287
  · exact B2153291
  · exact B2153295
  · exact B2153299
  · exact B2153303
  · exact B2153307
  · exact B2153311
  · exact B2153315
  · exact B2153319
  · exact B2153323
  · exact B2153327
  · exact B2153331
  · exact B2153335
  · exact B2153339
  · exact B2153343
  · exact B2153347
  · exact B2153351
  · exact B2153355
  · exact B2153359
  · exact B2153363
  · exact B2153367
  · exact B2153371
  · exact B2153375
  · exact B2153379
  · exact B2153383
  · exact B2153387
  · exact B2153391
  · exact B2153395
  · exact B2153399
  · exact B2153403
  · exact B2153407
  · exact B2153411
  · exact B2153415
  · exact B2153419
  · exact B2153423
  · exact B2153427
  · exact B2153431
  · exact B2153435
theorem solution (m : ℕ) (hlo : 2151435 ≤ m) (hhi : m ≤ 2153435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 537858 ≤ j := by omega
    have hj2 : j ≤ 538358 := by omega
    have hb : Blo 2151435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
