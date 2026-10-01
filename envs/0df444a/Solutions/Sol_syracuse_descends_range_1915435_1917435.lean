-- Prove2me | solution 1 for syracuse_descends_range_1915435_1917435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:05.047151+00:00
-- url     : https://prove2.me/submissions/69139421-3a87-4f6b-953d-f59c6b0c4030

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

theorem B2154865 : Blo 1915435 2154865 := bbase (se 2 (by rfl) ⟨808074, by rfl⟩ : syracuseStep 2154865 = 1616149) (by norm_num)
theorem B2873153 : Blo 1915435 2873153 := bstep (se 2 (by rfl) ⟨1077432, by rfl⟩ : syracuseStep 2873153 = 2154865) B2154865
theorem B1915435 : Blo 1915435 1915435 := bstep (se 1 (by rfl) ⟨1436576, by rfl⟩ : syracuseStep 1915435 = 2873153) B2873153
theorem B3068165 : Blo 1915435 3068165 := bbase (se 4 (by rfl) ⟨287640, by rfl⟩ : syracuseStep 3068165 = 575281) (by norm_num)
theorem B8181773 : Blo 1915435 8181773 := bstep (se 3 (by rfl) ⟨1534082, by rfl⟩ : syracuseStep 8181773 = 3068165) B3068165
theorem B5454515 : Blo 1915435 5454515 := bstep (se 1 (by rfl) ⟨4090886, by rfl⟩ : syracuseStep 5454515 = 8181773) B8181773
theorem B3636343 : Blo 1915435 3636343 := bstep (se 1 (by rfl) ⟨2727257, by rfl⟩ : syracuseStep 3636343 = 5454515) B5454515
theorem B4848457 : Blo 1915435 4848457 := bstep (se 2 (by rfl) ⟨1818171, by rfl⟩ : syracuseStep 4848457 = 3636343) B3636343
theorem B6464609 : Blo 1915435 6464609 := bstep (se 2 (by rfl) ⟨2424228, by rfl⟩ : syracuseStep 6464609 = 4848457) B4848457
theorem B4309739 : Blo 1915435 4309739 := bstep (se 1 (by rfl) ⟨3232304, by rfl⟩ : syracuseStep 4309739 = 6464609) B6464609
theorem B2873159 : Blo 1915435 2873159 := bstep (se 1 (by rfl) ⟨2154869, by rfl⟩ : syracuseStep 2873159 = 4309739) B4309739
theorem B1915439 : Blo 1915435 1915439 := bstep (se 1 (by rfl) ⟨1436579, by rfl⟩ : syracuseStep 1915439 = 2873159) B2873159
theorem B2873165 : Blo 1915435 2873165 := bbase (se 3 (by rfl) ⟨538718, by rfl⟩ : syracuseStep 2873165 = 1077437) (by norm_num)
theorem B1915443 : Blo 1915435 1915443 := bstep (se 1 (by rfl) ⟨1436582, by rfl⟩ : syracuseStep 1915443 = 2873165) B2873165
theorem B4309757 : Blo 1915435 4309757 := bbase (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) (by norm_num)
theorem B2873171 : Blo 1915435 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1915447 : Blo 1915435 1915447 := bstep (se 1 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 1915447 = 2873171) B2873171
theorem B3232325 : Blo 1915435 3232325 := bbase (se 4 (by rfl) ⟨303030, by rfl⟩ : syracuseStep 3232325 = 606061) (by norm_num)
theorem B2154883 : Blo 1915435 2154883 := bstep (se 1 (by rfl) ⟨1616162, by rfl⟩ : syracuseStep 2154883 = 3232325) B3232325
theorem B2873177 : Blo 1915435 2873177 := bstep (se 2 (by rfl) ⟨1077441, by rfl⟩ : syracuseStep 2873177 = 2154883) B2154883
theorem B1915451 : Blo 1915435 1915451 := bstep (se 1 (by rfl) ⟨1436588, by rfl⟩ : syracuseStep 1915451 = 2873177) B2873177
theorem B14545493 : Blo 1915435 14545493 := bbase (se 8 (by rfl) ⟨85227, by rfl⟩ : syracuseStep 14545493 = 170455) (by norm_num)
theorem B9696995 : Blo 1915435 9696995 := bstep (se 1 (by rfl) ⟨7272746, by rfl⟩ : syracuseStep 9696995 = 14545493) B14545493
theorem B6464663 : Blo 1915435 6464663 := bstep (se 1 (by rfl) ⟨4848497, by rfl⟩ : syracuseStep 6464663 = 9696995) B9696995
theorem B4309775 : Blo 1915435 4309775 := bstep (se 1 (by rfl) ⟨3232331, by rfl⟩ : syracuseStep 4309775 = 6464663) B6464663
theorem B2873183 : Blo 1915435 2873183 := bstep (se 1 (by rfl) ⟨2154887, by rfl⟩ : syracuseStep 2873183 = 4309775) B4309775
theorem B1915455 : Blo 1915435 1915455 := bstep (se 1 (by rfl) ⟨1436591, by rfl⟩ : syracuseStep 1915455 = 2873183) B2873183
theorem B2873189 : Blo 1915435 2873189 := bbase (se 4 (by rfl) ⟨269361, by rfl⟩ : syracuseStep 2873189 = 538723) (by norm_num)
theorem B1915459 : Blo 1915435 1915459 := bstep (se 1 (by rfl) ⟨1436594, by rfl⟩ : syracuseStep 1915459 = 2873189) B2873189
theorem B3636389 : Blo 1915435 3636389 := bbase (se 4 (by rfl) ⟨340911, by rfl⟩ : syracuseStep 3636389 = 681823) (by norm_num)
theorem B2424259 : Blo 1915435 2424259 := bstep (se 1 (by rfl) ⟨1818194, by rfl⟩ : syracuseStep 2424259 = 3636389) B3636389
theorem B3232345 : Blo 1915435 3232345 := bstep (se 2 (by rfl) ⟨1212129, by rfl⟩ : syracuseStep 3232345 = 2424259) B2424259
theorem B4309793 : Blo 1915435 4309793 := bstep (se 2 (by rfl) ⟨1616172, by rfl⟩ : syracuseStep 4309793 = 3232345) B3232345
theorem B2873195 : Blo 1915435 2873195 := bstep (se 1 (by rfl) ⟨2154896, by rfl⟩ : syracuseStep 2873195 = 4309793) B4309793
theorem B1915463 : Blo 1915435 1915463 := bstep (se 1 (by rfl) ⟨1436597, by rfl⟩ : syracuseStep 1915463 = 2873195) B2873195
theorem B2154901 : Blo 1915435 2154901 := bbase (se 6 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 2154901 = 101011) (by norm_num)
theorem B2873201 : Blo 1915435 2873201 := bstep (se 2 (by rfl) ⟨1077450, by rfl⟩ : syracuseStep 2873201 = 2154901) B2154901
theorem B1915467 : Blo 1915435 1915467 := bstep (se 1 (by rfl) ⟨1436600, by rfl⟩ : syracuseStep 1915467 = 2873201) B2873201
theorem B2424269 : Blo 1915435 2424269 := bbase (se 3 (by rfl) ⟨454550, by rfl⟩ : syracuseStep 2424269 = 909101) (by norm_num)
theorem B6464717 : Blo 1915435 6464717 := bstep (se 3 (by rfl) ⟨1212134, by rfl⟩ : syracuseStep 6464717 = 2424269) B2424269
theorem B4309811 : Blo 1915435 4309811 := bstep (se 1 (by rfl) ⟨3232358, by rfl⟩ : syracuseStep 4309811 = 6464717) B6464717
theorem B2873207 : Blo 1915435 2873207 := bstep (se 1 (by rfl) ⟨2154905, by rfl⟩ : syracuseStep 2873207 = 4309811) B4309811
theorem B1915471 : Blo 1915435 1915471 := bstep (se 1 (by rfl) ⟨1436603, by rfl⟩ : syracuseStep 1915471 = 2873207) B2873207
theorem B2873213 : Blo 1915435 2873213 := bbase (se 3 (by rfl) ⟨538727, by rfl⟩ : syracuseStep 2873213 = 1077455) (by norm_num)
theorem B1915475 : Blo 1915435 1915475 := bstep (se 1 (by rfl) ⟨1436606, by rfl⟩ : syracuseStep 1915475 = 2873213) B2873213
theorem B4309829 : Blo 1915435 4309829 := bbase (se 4 (by rfl) ⟨404046, by rfl⟩ : syracuseStep 4309829 = 808093) (by norm_num)
theorem B2873219 : Blo 1915435 2873219 := bstep (se 1 (by rfl) ⟨2154914, by rfl⟩ : syracuseStep 2873219 = 4309829) B4309829
theorem B1915479 : Blo 1915435 1915479 := bstep (se 1 (by rfl) ⟨1436609, by rfl⟩ : syracuseStep 1915479 = 2873219) B2873219
theorem B4090981 : Blo 1915435 4090981 := bbase (se 4 (by rfl) ⟨383529, by rfl⟩ : syracuseStep 4090981 = 767059) (by norm_num)
theorem B5454641 : Blo 1915435 5454641 := bstep (se 2 (by rfl) ⟨2045490, by rfl⟩ : syracuseStep 5454641 = 4090981) B4090981
theorem B3636427 : Blo 1915435 3636427 := bstep (se 1 (by rfl) ⟨2727320, by rfl⟩ : syracuseStep 3636427 = 5454641) B5454641
theorem B4848569 : Blo 1915435 4848569 := bstep (se 2 (by rfl) ⟨1818213, by rfl⟩ : syracuseStep 4848569 = 3636427) B3636427
theorem B3232379 : Blo 1915435 3232379 := bstep (se 1 (by rfl) ⟨2424284, by rfl⟩ : syracuseStep 3232379 = 4848569) B4848569
theorem B2154919 : Blo 1915435 2154919 := bstep (se 1 (by rfl) ⟨1616189, by rfl⟩ : syracuseStep 2154919 = 3232379) B3232379
theorem B2873225 : Blo 1915435 2873225 := bstep (se 2 (by rfl) ⟨1077459, by rfl⟩ : syracuseStep 2873225 = 2154919) B2154919
theorem B1915483 : Blo 1915435 1915483 := bstep (se 1 (by rfl) ⟨1436612, by rfl⟩ : syracuseStep 1915483 = 2873225) B2873225
theorem B9697157 : Blo 1915435 9697157 := bbase (se 4 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 9697157 = 1818217) (by norm_num)
theorem B6464771 : Blo 1915435 6464771 := bstep (se 1 (by rfl) ⟨4848578, by rfl⟩ : syracuseStep 6464771 = 9697157) B9697157
theorem B4309847 : Blo 1915435 4309847 := bstep (se 1 (by rfl) ⟨3232385, by rfl⟩ : syracuseStep 4309847 = 6464771) B6464771
theorem B2873231 : Blo 1915435 2873231 := bstep (se 1 (by rfl) ⟨2154923, by rfl⟩ : syracuseStep 2873231 = 4309847) B4309847
theorem B1915487 : Blo 1915435 1915487 := bstep (se 1 (by rfl) ⟨1436615, by rfl⟩ : syracuseStep 1915487 = 2873231) B2873231
theorem B2873237 : Blo 1915435 2873237 := bbase (se 6 (by rfl) ⟨67341, by rfl⟩ : syracuseStep 2873237 = 134683) (by norm_num)
theorem B1915491 : Blo 1915435 1915491 := bstep (se 1 (by rfl) ⟨1436618, by rfl⟩ : syracuseStep 1915491 = 2873237) B2873237
theorem B15533045 : Blo 1915435 15533045 := bbase (se 5 (by rfl) ⟨728111, by rfl⟩ : syracuseStep 15533045 = 1456223) (by norm_num)
theorem B10355363 : Blo 1915435 10355363 := bstep (se 1 (by rfl) ⟨7766522, by rfl⟩ : syracuseStep 10355363 = 15533045) B15533045
theorem B6903575 : Blo 1915435 6903575 := bstep (se 1 (by rfl) ⟨5177681, by rfl⟩ : syracuseStep 6903575 = 10355363) B10355363
theorem B4602383 : Blo 1915435 4602383 := bstep (se 1 (by rfl) ⟨3451787, by rfl⟩ : syracuseStep 4602383 = 6903575) B6903575
theorem B3068255 : Blo 1915435 3068255 := bstep (se 1 (by rfl) ⟨2301191, by rfl⟩ : syracuseStep 3068255 = 4602383) B4602383
theorem B2045503 : Blo 1915435 2045503 := bstep (se 1 (by rfl) ⟨1534127, by rfl⟩ : syracuseStep 2045503 = 3068255) B3068255
theorem B10909349 : Blo 1915435 10909349 := bstep (se 4 (by rfl) ⟨1022751, by rfl⟩ : syracuseStep 10909349 = 2045503) B2045503
theorem B7272899 : Blo 1915435 7272899 := bstep (se 1 (by rfl) ⟨5454674, by rfl⟩ : syracuseStep 7272899 = 10909349) B10909349
theorem B4848599 : Blo 1915435 4848599 := bstep (se 1 (by rfl) ⟨3636449, by rfl⟩ : syracuseStep 4848599 = 7272899) B7272899
theorem B3232399 : Blo 1915435 3232399 := bstep (se 1 (by rfl) ⟨2424299, by rfl⟩ : syracuseStep 3232399 = 4848599) B4848599
theorem B4309865 : Blo 1915435 4309865 := bstep (se 2 (by rfl) ⟨1616199, by rfl⟩ : syracuseStep 4309865 = 3232399) B3232399
theorem B2873243 : Blo 1915435 2873243 := bstep (se 1 (by rfl) ⟨2154932, by rfl⟩ : syracuseStep 2873243 = 4309865) B4309865
theorem B1915495 : Blo 1915435 1915495 := bstep (se 1 (by rfl) ⟨1436621, by rfl⟩ : syracuseStep 1915495 = 2873243) B2873243
theorem B2154937 : Blo 1915435 2154937 := bbase (se 2 (by rfl) ⟨808101, by rfl⟩ : syracuseStep 2154937 = 1616203) (by norm_num)
theorem B2873249 : Blo 1915435 2873249 := bstep (se 2 (by rfl) ⟨1077468, by rfl⟩ : syracuseStep 2873249 = 2154937) B2154937
theorem B1915499 : Blo 1915435 1915499 := bstep (se 1 (by rfl) ⟨1436624, by rfl⟩ : syracuseStep 1915499 = 2873249) B2873249
theorem B3883277 : Blo 1915435 3883277 := bbase (se 3 (by rfl) ⟨728114, by rfl⟩ : syracuseStep 3883277 = 1456229) (by norm_num)
theorem B2588851 : Blo 1915435 2588851 := bstep (se 1 (by rfl) ⟨1941638, by rfl⟩ : syracuseStep 2588851 = 3883277) B3883277
theorem B13807205 : Blo 1915435 13807205 := bstep (se 4 (by rfl) ⟨1294425, by rfl⟩ : syracuseStep 13807205 = 2588851) B2588851
theorem B9204803 : Blo 1915435 9204803 := bstep (se 1 (by rfl) ⟨6903602, by rfl⟩ : syracuseStep 9204803 = 13807205) B13807205
theorem B6136535 : Blo 1915435 6136535 := bstep (se 1 (by rfl) ⟨4602401, by rfl⟩ : syracuseStep 6136535 = 9204803) B9204803
theorem B4091023 : Blo 1915435 4091023 := bstep (se 1 (by rfl) ⟨3068267, by rfl⟩ : syracuseStep 4091023 = 6136535) B6136535
theorem B5454697 : Blo 1915435 5454697 := bstep (se 2 (by rfl) ⟨2045511, by rfl⟩ : syracuseStep 5454697 = 4091023) B4091023
theorem B7272929 : Blo 1915435 7272929 := bstep (se 2 (by rfl) ⟨2727348, by rfl⟩ : syracuseStep 7272929 = 5454697) B5454697
theorem B4848619 : Blo 1915435 4848619 := bstep (se 1 (by rfl) ⟨3636464, by rfl⟩ : syracuseStep 4848619 = 7272929) B7272929
theorem B6464825 : Blo 1915435 6464825 := bstep (se 2 (by rfl) ⟨2424309, by rfl⟩ : syracuseStep 6464825 = 4848619) B4848619
theorem B4309883 : Blo 1915435 4309883 := bstep (se 1 (by rfl) ⟨3232412, by rfl⟩ : syracuseStep 4309883 = 6464825) B6464825
theorem B2873255 : Blo 1915435 2873255 := bstep (se 1 (by rfl) ⟨2154941, by rfl⟩ : syracuseStep 2873255 = 4309883) B4309883
theorem B1915503 : Blo 1915435 1915503 := bstep (se 1 (by rfl) ⟨1436627, by rfl⟩ : syracuseStep 1915503 = 2873255) B2873255
theorem B2873261 : Blo 1915435 2873261 := bbase (se 3 (by rfl) ⟨538736, by rfl⟩ : syracuseStep 2873261 = 1077473) (by norm_num)
theorem B1915507 : Blo 1915435 1915507 := bstep (se 1 (by rfl) ⟨1436630, by rfl⟩ : syracuseStep 1915507 = 2873261) B2873261
theorem B4309901 : Blo 1915435 4309901 := bbase (se 3 (by rfl) ⟨808106, by rfl⟩ : syracuseStep 4309901 = 1616213) (by norm_num)
theorem B2873267 : Blo 1915435 2873267 := bstep (se 1 (by rfl) ⟨2154950, by rfl⟩ : syracuseStep 2873267 = 4309901) B4309901
theorem B1915511 : Blo 1915435 1915511 := bstep (se 1 (by rfl) ⟨1436633, by rfl⟩ : syracuseStep 1915511 = 2873267) B2873267
theorem B2424325 : Blo 1915435 2424325 := bbase (se 4 (by rfl) ⟨227280, by rfl⟩ : syracuseStep 2424325 = 454561) (by norm_num)
theorem B3232433 : Blo 1915435 3232433 := bstep (se 2 (by rfl) ⟨1212162, by rfl⟩ : syracuseStep 3232433 = 2424325) B2424325
theorem B2154955 : Blo 1915435 2154955 := bstep (se 1 (by rfl) ⟨1616216, by rfl⟩ : syracuseStep 2154955 = 3232433) B3232433
theorem B2873273 : Blo 1915435 2873273 := bstep (se 2 (by rfl) ⟨1077477, by rfl⟩ : syracuseStep 2873273 = 2154955) B2154955
theorem B1915515 : Blo 1915435 1915515 := bstep (se 1 (by rfl) ⟨1436636, by rfl⟩ : syracuseStep 1915515 = 2873273) B2873273
theorem B8737445 : Blo 1915435 8737445 := bbase (se 4 (by rfl) ⟨819135, by rfl⟩ : syracuseStep 8737445 = 1638271) (by norm_num)
theorem B5824963 : Blo 1915435 5824963 := bstep (se 1 (by rfl) ⟨4368722, by rfl⟩ : syracuseStep 5824963 = 8737445) B8737445
theorem B7766617 : Blo 1915435 7766617 := bstep (se 2 (by rfl) ⟨2912481, by rfl⟩ : syracuseStep 7766617 = 5824963) B5824963
theorem B10355489 : Blo 1915435 10355489 := bstep (se 2 (by rfl) ⟨3883308, by rfl⟩ : syracuseStep 10355489 = 7766617) B7766617
theorem B6903659 : Blo 1915435 6903659 := bstep (se 1 (by rfl) ⟨5177744, by rfl⟩ : syracuseStep 6903659 = 10355489) B10355489
theorem B4602439 : Blo 1915435 4602439 := bstep (se 1 (by rfl) ⟨3451829, by rfl⟩ : syracuseStep 4602439 = 6903659) B6903659
theorem B24546341 : Blo 1915435 24546341 := bstep (se 4 (by rfl) ⟨2301219, by rfl⟩ : syracuseStep 24546341 = 4602439) B4602439
theorem B16364227 : Blo 1915435 16364227 := bstep (se 1 (by rfl) ⟨12273170, by rfl⟩ : syracuseStep 16364227 = 24546341) B24546341
theorem B21818969 : Blo 1915435 21818969 := bstep (se 2 (by rfl) ⟨8182113, by rfl⟩ : syracuseStep 21818969 = 16364227) B16364227
theorem B14545979 : Blo 1915435 14545979 := bstep (se 1 (by rfl) ⟨10909484, by rfl⟩ : syracuseStep 14545979 = 21818969) B21818969
theorem B9697319 : Blo 1915435 9697319 := bstep (se 1 (by rfl) ⟨7272989, by rfl⟩ : syracuseStep 9697319 = 14545979) B14545979
theorem B6464879 : Blo 1915435 6464879 := bstep (se 1 (by rfl) ⟨4848659, by rfl⟩ : syracuseStep 6464879 = 9697319) B9697319
theorem B4309919 : Blo 1915435 4309919 := bstep (se 1 (by rfl) ⟨3232439, by rfl⟩ : syracuseStep 4309919 = 6464879) B6464879
theorem B2873279 : Blo 1915435 2873279 := bstep (se 1 (by rfl) ⟨2154959, by rfl⟩ : syracuseStep 2873279 = 4309919) B4309919
theorem B1915519 : Blo 1915435 1915519 := bstep (se 1 (by rfl) ⟨1436639, by rfl⟩ : syracuseStep 1915519 = 2873279) B2873279
theorem B2873285 : Blo 1915435 2873285 := bbase (se 4 (by rfl) ⟨269370, by rfl⟩ : syracuseStep 2873285 = 538741) (by norm_num)
theorem B1915523 : Blo 1915435 1915523 := bstep (se 1 (by rfl) ⟨1436642, by rfl⟩ : syracuseStep 1915523 = 2873285) B2873285
theorem B3232453 : Blo 1915435 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B4309937 : Blo 1915435 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B2873291 : Blo 1915435 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B1915527 : Blo 1915435 1915527 := bstep (se 1 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 1915527 = 2873291) B2873291
theorem B2154973 : Blo 1915435 2154973 := bbase (se 3 (by rfl) ⟨404057, by rfl⟩ : syracuseStep 2154973 = 808115) (by norm_num)
theorem B2873297 : Blo 1915435 2873297 := bstep (se 2 (by rfl) ⟨1077486, by rfl⟩ : syracuseStep 2873297 = 2154973) B2154973
theorem B1915531 : Blo 1915435 1915531 := bstep (se 1 (by rfl) ⟨1436648, by rfl⟩ : syracuseStep 1915531 = 2873297) B2873297
theorem B6464933 : Blo 1915435 6464933 := bbase (se 4 (by rfl) ⟨606087, by rfl⟩ : syracuseStep 6464933 = 1212175) (by norm_num)
theorem B4309955 : Blo 1915435 4309955 := bstep (se 1 (by rfl) ⟨3232466, by rfl⟩ : syracuseStep 4309955 = 6464933) B6464933
theorem B2873303 : Blo 1915435 2873303 := bstep (se 1 (by rfl) ⟨2154977, by rfl⟩ : syracuseStep 2873303 = 4309955) B4309955
theorem B1915535 : Blo 1915435 1915535 := bstep (se 1 (by rfl) ⟨1436651, by rfl⟩ : syracuseStep 1915535 = 2873303) B2873303
theorem B2873309 : Blo 1915435 2873309 := bbase (se 3 (by rfl) ⟨538745, by rfl⟩ : syracuseStep 2873309 = 1077491) (by norm_num)
theorem B1915539 : Blo 1915435 1915539 := bstep (se 1 (by rfl) ⟨1436654, by rfl⟩ : syracuseStep 1915539 = 2873309) B2873309
theorem B4309973 : Blo 1915435 4309973 := bbase (se 7 (by rfl) ⟨50507, by rfl⟩ : syracuseStep 4309973 = 101015) (by norm_num)
theorem B2873315 : Blo 1915435 2873315 := bstep (se 1 (by rfl) ⟨2154986, by rfl⟩ : syracuseStep 2873315 = 4309973) B4309973
theorem B1915543 : Blo 1915435 1915543 := bstep (se 1 (by rfl) ⟨1436657, by rfl⟩ : syracuseStep 1915543 = 2873315) B2873315
theorem B2912525 : Blo 1915435 2912525 := bbase (se 3 (by rfl) ⟨546098, by rfl⟩ : syracuseStep 2912525 = 1092197) (by norm_num)
theorem B1941683 : Blo 1915435 1941683 := bstep (se 1 (by rfl) ⟨1456262, by rfl⟩ : syracuseStep 1941683 = 2912525) B2912525
theorem B20711285 : Blo 1915435 20711285 := bstep (se 5 (by rfl) ⟨970841, by rfl⟩ : syracuseStep 20711285 = 1941683) B1941683
theorem B13807523 : Blo 1915435 13807523 := bstep (se 1 (by rfl) ⟨10355642, by rfl⟩ : syracuseStep 13807523 = 20711285) B20711285
theorem B9205015 : Blo 1915435 9205015 := bstep (se 1 (by rfl) ⟨6903761, by rfl⟩ : syracuseStep 9205015 = 13807523) B13807523
theorem B12273353 : Blo 1915435 12273353 := bstep (se 2 (by rfl) ⟨4602507, by rfl⟩ : syracuseStep 12273353 = 9205015) B9205015
theorem B8182235 : Blo 1915435 8182235 := bstep (se 1 (by rfl) ⟨6136676, by rfl⟩ : syracuseStep 8182235 = 12273353) B12273353
theorem B5454823 : Blo 1915435 5454823 := bstep (se 1 (by rfl) ⟨4091117, by rfl⟩ : syracuseStep 5454823 = 8182235) B8182235
theorem B7273097 : Blo 1915435 7273097 := bstep (se 2 (by rfl) ⟨2727411, by rfl⟩ : syracuseStep 7273097 = 5454823) B5454823
theorem B4848731 : Blo 1915435 4848731 := bstep (se 1 (by rfl) ⟨3636548, by rfl⟩ : syracuseStep 4848731 = 7273097) B7273097
theorem B3232487 : Blo 1915435 3232487 := bstep (se 1 (by rfl) ⟨2424365, by rfl⟩ : syracuseStep 3232487 = 4848731) B4848731
theorem B2154991 : Blo 1915435 2154991 := bstep (se 1 (by rfl) ⟨1616243, by rfl⟩ : syracuseStep 2154991 = 3232487) B3232487
theorem B2873321 : Blo 1915435 2873321 := bstep (se 2 (by rfl) ⟨1077495, by rfl⟩ : syracuseStep 2873321 = 2154991) B2154991
theorem B1915547 : Blo 1915435 1915547 := bstep (se 1 (by rfl) ⟨1436660, by rfl⟩ : syracuseStep 1915547 = 2873321) B2873321
theorem B16364501 : Blo 1915435 16364501 := bbase (se 7 (by rfl) ⟨191771, by rfl⟩ : syracuseStep 16364501 = 383543) (by norm_num)
theorem B10909667 : Blo 1915435 10909667 := bstep (se 1 (by rfl) ⟨8182250, by rfl⟩ : syracuseStep 10909667 = 16364501) B16364501
theorem B7273111 : Blo 1915435 7273111 := bstep (se 1 (by rfl) ⟨5454833, by rfl⟩ : syracuseStep 7273111 = 10909667) B10909667
theorem B9697481 : Blo 1915435 9697481 := bstep (se 2 (by rfl) ⟨3636555, by rfl⟩ : syracuseStep 9697481 = 7273111) B7273111
theorem B6464987 : Blo 1915435 6464987 := bstep (se 1 (by rfl) ⟨4848740, by rfl⟩ : syracuseStep 6464987 = 9697481) B9697481
theorem B4309991 : Blo 1915435 4309991 := bstep (se 1 (by rfl) ⟨3232493, by rfl⟩ : syracuseStep 4309991 = 6464987) B6464987
theorem B2873327 : Blo 1915435 2873327 := bstep (se 1 (by rfl) ⟨2154995, by rfl⟩ : syracuseStep 2873327 = 4309991) B4309991
theorem B1915551 : Blo 1915435 1915551 := bstep (se 1 (by rfl) ⟨1436663, by rfl⟩ : syracuseStep 1915551 = 2873327) B2873327
theorem B2873333 : Blo 1915435 2873333 := bbase (se 5 (by rfl) ⟨134687, by rfl⟩ : syracuseStep 2873333 = 269375) (by norm_num)
theorem B1915555 : Blo 1915435 1915555 := bstep (se 1 (by rfl) ⟨1436666, by rfl⟩ : syracuseStep 1915555 = 2873333) B2873333
theorem B2073481 : Blo 1915435 2073481 := bbase (se 2 (by rfl) ⟨777555, by rfl⟩ : syracuseStep 2073481 = 1555111) (by norm_num)
theorem B44234261 : Blo 1915435 44234261 := bstep (se 6 (by rfl) ⟨1036740, by rfl⟩ : syracuseStep 44234261 = 2073481) B2073481
theorem B29489507 : Blo 1915435 29489507 := bstep (se 1 (by rfl) ⟨22117130, by rfl⟩ : syracuseStep 29489507 = 44234261) B44234261
theorem B19659671 : Blo 1915435 19659671 := bstep (se 1 (by rfl) ⟨14744753, by rfl⟩ : syracuseStep 19659671 = 29489507) B29489507
theorem B13106447 : Blo 1915435 13106447 := bstep (se 1 (by rfl) ⟨9829835, by rfl⟩ : syracuseStep 13106447 = 19659671) B19659671
theorem B8737631 : Blo 1915435 8737631 := bstep (se 1 (by rfl) ⟨6553223, by rfl⟩ : syracuseStep 8737631 = 13106447) B13106447
theorem B5825087 : Blo 1915435 5825087 := bstep (se 1 (by rfl) ⟨4368815, by rfl⟩ : syracuseStep 5825087 = 8737631) B8737631
theorem B3883391 : Blo 1915435 3883391 := bstep (se 1 (by rfl) ⟨2912543, by rfl⟩ : syracuseStep 3883391 = 5825087) B5825087
theorem B2588927 : Blo 1915435 2588927 := bstep (se 1 (by rfl) ⟨1941695, by rfl⟩ : syracuseStep 2588927 = 3883391) B3883391
theorem B6903805 : Blo 1915435 6903805 := bstep (se 3 (by rfl) ⟨1294463, by rfl⟩ : syracuseStep 6903805 = 2588927) B2588927
theorem B9205073 : Blo 1915435 9205073 := bstep (se 2 (by rfl) ⟨3451902, by rfl⟩ : syracuseStep 9205073 = 6903805) B6903805
theorem B6136715 : Blo 1915435 6136715 := bstep (se 1 (by rfl) ⟨4602536, by rfl⟩ : syracuseStep 6136715 = 9205073) B9205073
theorem B4091143 : Blo 1915435 4091143 := bstep (se 1 (by rfl) ⟨3068357, by rfl⟩ : syracuseStep 4091143 = 6136715) B6136715
theorem B5454857 : Blo 1915435 5454857 := bstep (se 2 (by rfl) ⟨2045571, by rfl⟩ : syracuseStep 5454857 = 4091143) B4091143
theorem B3636571 : Blo 1915435 3636571 := bstep (se 1 (by rfl) ⟨2727428, by rfl⟩ : syracuseStep 3636571 = 5454857) B5454857
theorem B4848761 : Blo 1915435 4848761 := bstep (se 2 (by rfl) ⟨1818285, by rfl⟩ : syracuseStep 4848761 = 3636571) B3636571
theorem B3232507 : Blo 1915435 3232507 := bstep (se 1 (by rfl) ⟨2424380, by rfl⟩ : syracuseStep 3232507 = 4848761) B4848761
theorem B4310009 : Blo 1915435 4310009 := bstep (se 2 (by rfl) ⟨1616253, by rfl⟩ : syracuseStep 4310009 = 3232507) B3232507
theorem B2873339 : Blo 1915435 2873339 := bstep (se 1 (by rfl) ⟨2155004, by rfl⟩ : syracuseStep 2873339 = 4310009) B4310009
theorem B1915559 : Blo 1915435 1915559 := bstep (se 1 (by rfl) ⟨1436669, by rfl⟩ : syracuseStep 1915559 = 2873339) B2873339
theorem B2155009 : Blo 1915435 2155009 := bbase (se 2 (by rfl) ⟨808128, by rfl⟩ : syracuseStep 2155009 = 1616257) (by norm_num)
theorem B2873345 : Blo 1915435 2873345 := bstep (se 2 (by rfl) ⟨1077504, by rfl⟩ : syracuseStep 2873345 = 2155009) B2155009
theorem B1915563 : Blo 1915435 1915563 := bstep (se 1 (by rfl) ⟨1436672, by rfl⟩ : syracuseStep 1915563 = 2873345) B2873345
theorem B4848781 : Blo 1915435 4848781 := bbase (se 3 (by rfl) ⟨909146, by rfl⟩ : syracuseStep 4848781 = 1818293) (by norm_num)
theorem B6465041 : Blo 1915435 6465041 := bstep (se 2 (by rfl) ⟨2424390, by rfl⟩ : syracuseStep 6465041 = 4848781) B4848781
theorem B4310027 : Blo 1915435 4310027 := bstep (se 1 (by rfl) ⟨3232520, by rfl⟩ : syracuseStep 4310027 = 6465041) B6465041
theorem B2873351 : Blo 1915435 2873351 := bstep (se 1 (by rfl) ⟨2155013, by rfl⟩ : syracuseStep 2873351 = 4310027) B4310027
theorem B1915567 : Blo 1915435 1915567 := bstep (se 1 (by rfl) ⟨1436675, by rfl⟩ : syracuseStep 1915567 = 2873351) B2873351
theorem B2873357 : Blo 1915435 2873357 := bbase (se 3 (by rfl) ⟨538754, by rfl⟩ : syracuseStep 2873357 = 1077509) (by norm_num)
theorem B1915571 : Blo 1915435 1915571 := bstep (se 1 (by rfl) ⟨1436678, by rfl⟩ : syracuseStep 1915571 = 2873357) B2873357
theorem B4310045 : Blo 1915435 4310045 := bbase (se 3 (by rfl) ⟨808133, by rfl⟩ : syracuseStep 4310045 = 1616267) (by norm_num)
theorem B2873363 : Blo 1915435 2873363 := bstep (se 1 (by rfl) ⟨2155022, by rfl⟩ : syracuseStep 2873363 = 4310045) B4310045
theorem B1915575 : Blo 1915435 1915575 := bstep (se 1 (by rfl) ⟨1436681, by rfl⟩ : syracuseStep 1915575 = 2873363) B2873363
theorem B3232541 : Blo 1915435 3232541 := bbase (se 3 (by rfl) ⟨606101, by rfl⟩ : syracuseStep 3232541 = 1212203) (by norm_num)
theorem B2155027 : Blo 1915435 2155027 := bstep (se 1 (by rfl) ⟨1616270, by rfl⟩ : syracuseStep 2155027 = 3232541) B3232541
theorem B2873369 : Blo 1915435 2873369 := bstep (se 2 (by rfl) ⟨1077513, by rfl⟩ : syracuseStep 2873369 = 2155027) B2155027
theorem B1915579 : Blo 1915435 1915579 := bstep (se 1 (by rfl) ⟨1436684, by rfl⟩ : syracuseStep 1915579 = 2873369) B2873369
theorem B9829957 : Blo 1915435 9829957 := bbase (se 4 (by rfl) ⟨921558, by rfl⟩ : syracuseStep 9829957 = 1843117) (by norm_num)
theorem B13106609 : Blo 1915435 13106609 := bstep (se 2 (by rfl) ⟨4914978, by rfl⟩ : syracuseStep 13106609 = 9829957) B9829957
theorem B8737739 : Blo 1915435 8737739 := bstep (se 1 (by rfl) ⟨6553304, by rfl⟩ : syracuseStep 8737739 = 13106609) B13106609
theorem B5825159 : Blo 1915435 5825159 := bstep (se 1 (by rfl) ⟨4368869, by rfl⟩ : syracuseStep 5825159 = 8737739) B8737739
theorem B3883439 : Blo 1915435 3883439 := bstep (se 1 (by rfl) ⟨2912579, by rfl⟩ : syracuseStep 3883439 = 5825159) B5825159
theorem B2588959 : Blo 1915435 2588959 := bstep (se 1 (by rfl) ⟨1941719, by rfl⟩ : syracuseStep 2588959 = 3883439) B3883439
theorem B3451945 : Blo 1915435 3451945 := bstep (se 2 (by rfl) ⟨1294479, by rfl⟩ : syracuseStep 3451945 = 2588959) B2588959
theorem B4602593 : Blo 1915435 4602593 := bstep (se 2 (by rfl) ⟨1725972, by rfl⟩ : syracuseStep 4602593 = 3451945) B3451945
theorem B12273581 : Blo 1915435 12273581 := bstep (se 3 (by rfl) ⟨2301296, by rfl⟩ : syracuseStep 12273581 = 4602593) B4602593
theorem B8182387 : Blo 1915435 8182387 := bstep (se 1 (by rfl) ⟨6136790, by rfl⟩ : syracuseStep 8182387 = 12273581) B12273581
theorem B10909849 : Blo 1915435 10909849 := bstep (se 2 (by rfl) ⟨4091193, by rfl⟩ : syracuseStep 10909849 = 8182387) B8182387
theorem B14546465 : Blo 1915435 14546465 := bstep (se 2 (by rfl) ⟨5454924, by rfl⟩ : syracuseStep 14546465 = 10909849) B10909849
theorem B9697643 : Blo 1915435 9697643 := bstep (se 1 (by rfl) ⟨7273232, by rfl⟩ : syracuseStep 9697643 = 14546465) B14546465
theorem B6465095 : Blo 1915435 6465095 := bstep (se 1 (by rfl) ⟨4848821, by rfl⟩ : syracuseStep 6465095 = 9697643) B9697643
theorem B4310063 : Blo 1915435 4310063 := bstep (se 1 (by rfl) ⟨3232547, by rfl⟩ : syracuseStep 4310063 = 6465095) B6465095
theorem B2873375 : Blo 1915435 2873375 := bstep (se 1 (by rfl) ⟨2155031, by rfl⟩ : syracuseStep 2873375 = 4310063) B4310063
theorem B1915583 : Blo 1915435 1915583 := bstep (se 1 (by rfl) ⟨1436687, by rfl⟩ : syracuseStep 1915583 = 2873375) B2873375
theorem B2873381 : Blo 1915435 2873381 := bbase (se 4 (by rfl) ⟨269379, by rfl⟩ : syracuseStep 2873381 = 538759) (by norm_num)
theorem B1915587 : Blo 1915435 1915587 := bstep (se 1 (by rfl) ⟨1436690, by rfl⟩ : syracuseStep 1915587 = 2873381) B2873381
theorem B2424421 : Blo 1915435 2424421 := bbase (se 4 (by rfl) ⟨227289, by rfl⟩ : syracuseStep 2424421 = 454579) (by norm_num)
theorem B3232561 : Blo 1915435 3232561 := bstep (se 2 (by rfl) ⟨1212210, by rfl⟩ : syracuseStep 3232561 = 2424421) B2424421
theorem B4310081 : Blo 1915435 4310081 := bstep (se 2 (by rfl) ⟨1616280, by rfl⟩ : syracuseStep 4310081 = 3232561) B3232561
theorem B2873387 : Blo 1915435 2873387 := bstep (se 1 (by rfl) ⟨2155040, by rfl⟩ : syracuseStep 2873387 = 4310081) B4310081
theorem B1915591 : Blo 1915435 1915591 := bstep (se 1 (by rfl) ⟨1436693, by rfl⟩ : syracuseStep 1915591 = 2873387) B2873387
theorem B2155045 : Blo 1915435 2155045 := bbase (se 4 (by rfl) ⟨202035, by rfl⟩ : syracuseStep 2155045 = 404071) (by norm_num)
theorem B2873393 : Blo 1915435 2873393 := bstep (se 2 (by rfl) ⟨1077522, by rfl⟩ : syracuseStep 2873393 = 2155045) B2155045
theorem B1915595 : Blo 1915435 1915595 := bstep (se 1 (by rfl) ⟨1436696, by rfl⟩ : syracuseStep 1915595 = 2873393) B2873393
theorem B2588981 : Blo 1915435 2588981 := bbase (se 5 (by rfl) ⟨121358, by rfl⟩ : syracuseStep 2588981 = 242717) (by norm_num)
theorem B6903949 : Blo 1915435 6903949 := bstep (se 3 (by rfl) ⟨1294490, by rfl⟩ : syracuseStep 6903949 = 2588981) B2588981
theorem B9205265 : Blo 1915435 9205265 := bstep (se 2 (by rfl) ⟨3451974, by rfl⟩ : syracuseStep 9205265 = 6903949) B6903949
theorem B6136843 : Blo 1915435 6136843 := bstep (se 1 (by rfl) ⟨4602632, by rfl⟩ : syracuseStep 6136843 = 9205265) B9205265
theorem B8182457 : Blo 1915435 8182457 := bstep (se 2 (by rfl) ⟨3068421, by rfl⟩ : syracuseStep 8182457 = 6136843) B6136843
theorem B5454971 : Blo 1915435 5454971 := bstep (se 1 (by rfl) ⟨4091228, by rfl⟩ : syracuseStep 5454971 = 8182457) B8182457
theorem B3636647 : Blo 1915435 3636647 := bstep (se 1 (by rfl) ⟨2727485, by rfl⟩ : syracuseStep 3636647 = 5454971) B5454971
theorem B2424431 : Blo 1915435 2424431 := bstep (se 1 (by rfl) ⟨1818323, by rfl⟩ : syracuseStep 2424431 = 3636647) B3636647
theorem B6465149 : Blo 1915435 6465149 := bstep (se 3 (by rfl) ⟨1212215, by rfl⟩ : syracuseStep 6465149 = 2424431) B2424431
theorem B4310099 : Blo 1915435 4310099 := bstep (se 1 (by rfl) ⟨3232574, by rfl⟩ : syracuseStep 4310099 = 6465149) B6465149
theorem B2873399 : Blo 1915435 2873399 := bstep (se 1 (by rfl) ⟨2155049, by rfl⟩ : syracuseStep 2873399 = 4310099) B4310099
theorem B1915599 : Blo 1915435 1915599 := bstep (se 1 (by rfl) ⟨1436699, by rfl⟩ : syracuseStep 1915599 = 2873399) B2873399
theorem B2873405 : Blo 1915435 2873405 := bbase (se 3 (by rfl) ⟨538763, by rfl⟩ : syracuseStep 2873405 = 1077527) (by norm_num)
theorem B1915603 : Blo 1915435 1915603 := bstep (se 1 (by rfl) ⟨1436702, by rfl⟩ : syracuseStep 1915603 = 2873405) B2873405
theorem B4310117 : Blo 1915435 4310117 := bbase (se 4 (by rfl) ⟨404073, by rfl⟩ : syracuseStep 4310117 = 808147) (by norm_num)
theorem B2873411 : Blo 1915435 2873411 := bstep (se 1 (by rfl) ⟨2155058, by rfl⟩ : syracuseStep 2873411 = 4310117) B4310117
theorem B1915607 : Blo 1915435 1915607 := bstep (se 1 (by rfl) ⟨1436705, by rfl⟩ : syracuseStep 1915607 = 2873411) B2873411
theorem B4848893 : Blo 1915435 4848893 := bbase (se 3 (by rfl) ⟨909167, by rfl⟩ : syracuseStep 4848893 = 1818335) (by norm_num)
theorem B3232595 : Blo 1915435 3232595 := bstep (se 1 (by rfl) ⟨2424446, by rfl⟩ : syracuseStep 3232595 = 4848893) B4848893
theorem B2155063 : Blo 1915435 2155063 := bstep (se 1 (by rfl) ⟨1616297, by rfl⟩ : syracuseStep 2155063 = 3232595) B3232595
theorem B2873417 : Blo 1915435 2873417 := bstep (se 2 (by rfl) ⟨1077531, by rfl⟩ : syracuseStep 2873417 = 2155063) B2155063
theorem B1915611 : Blo 1915435 1915611 := bstep (se 1 (by rfl) ⟨1436708, by rfl⟩ : syracuseStep 1915611 = 2873417) B2873417
theorem B3636677 : Blo 1915435 3636677 := bbase (se 4 (by rfl) ⟨340938, by rfl⟩ : syracuseStep 3636677 = 681877) (by norm_num)
theorem B9697805 : Blo 1915435 9697805 := bstep (se 3 (by rfl) ⟨1818338, by rfl⟩ : syracuseStep 9697805 = 3636677) B3636677
theorem B6465203 : Blo 1915435 6465203 := bstep (se 1 (by rfl) ⟨4848902, by rfl⟩ : syracuseStep 6465203 = 9697805) B9697805
theorem B4310135 : Blo 1915435 4310135 := bstep (se 1 (by rfl) ⟨3232601, by rfl⟩ : syracuseStep 4310135 = 6465203) B6465203
theorem B2873423 : Blo 1915435 2873423 := bstep (se 1 (by rfl) ⟨2155067, by rfl⟩ : syracuseStep 2873423 = 4310135) B4310135
theorem B1915615 : Blo 1915435 1915615 := bstep (se 1 (by rfl) ⟨1436711, by rfl⟩ : syracuseStep 1915615 = 2873423) B2873423
theorem B2873429 : Blo 1915435 2873429 := bbase (se 8 (by rfl) ⟨16836, by rfl⟩ : syracuseStep 2873429 = 33673) (by norm_num)
theorem B1915619 : Blo 1915435 1915619 := bstep (se 1 (by rfl) ⟨1436714, by rfl⟩ : syracuseStep 1915619 = 2873429) B2873429
theorem B5985317 : Blo 1915435 5985317 := bbase (se 4 (by rfl) ⟨561123, by rfl⟩ : syracuseStep 5985317 = 1122247) (by norm_num)
theorem B3990211 : Blo 1915435 3990211 := bstep (se 1 (by rfl) ⟨2992658, by rfl⟩ : syracuseStep 3990211 = 5985317) B5985317
theorem B21281125 : Blo 1915435 21281125 := bstep (se 4 (by rfl) ⟨1995105, by rfl⟩ : syracuseStep 21281125 = 3990211) B3990211
theorem B28374833 : Blo 1915435 28374833 := bstep (se 2 (by rfl) ⟨10640562, by rfl⟩ : syracuseStep 28374833 = 21281125) B21281125
theorem B18916555 : Blo 1915435 18916555 := bstep (se 1 (by rfl) ⟨14187416, by rfl⟩ : syracuseStep 18916555 = 28374833) B28374833
theorem B25222073 : Blo 1915435 25222073 := bstep (se 2 (by rfl) ⟨9458277, by rfl⟩ : syracuseStep 25222073 = 18916555) B18916555
theorem B269035445 : Blo 1915435 269035445 := bstep (se 5 (by rfl) ⟨12611036, by rfl⟩ : syracuseStep 269035445 = 25222073) B25222073
theorem B717427853 : Blo 1915435 717427853 := bstep (se 3 (by rfl) ⟨134517722, by rfl⟩ : syracuseStep 717427853 = 269035445) B269035445
theorem B478285235 : Blo 1915435 478285235 := bstep (se 1 (by rfl) ⟨358713926, by rfl⟩ : syracuseStep 478285235 = 717427853) B717427853
theorem B318856823 : Blo 1915435 318856823 := bstep (se 1 (by rfl) ⟨239142617, by rfl⟩ : syracuseStep 318856823 = 478285235) B478285235
theorem B212571215 : Blo 1915435 212571215 := bstep (se 1 (by rfl) ⟨159428411, by rfl⟩ : syracuseStep 212571215 = 318856823) B318856823
theorem B141714143 : Blo 1915435 141714143 := bstep (se 1 (by rfl) ⟨106285607, by rfl⟩ : syracuseStep 141714143 = 212571215) B212571215
theorem B94476095 : Blo 1915435 94476095 := bstep (se 1 (by rfl) ⟨70857071, by rfl⟩ : syracuseStep 94476095 = 141714143) B141714143
theorem B62984063 : Blo 1915435 62984063 := bstep (se 1 (by rfl) ⟨47238047, by rfl⟩ : syracuseStep 62984063 = 94476095) B94476095
theorem B41989375 : Blo 1915435 41989375 := bstep (se 1 (by rfl) ⟨31492031, by rfl⟩ : syracuseStep 41989375 = 62984063) B62984063
theorem B55985833 : Blo 1915435 55985833 := bstep (se 2 (by rfl) ⟨20994687, by rfl⟩ : syracuseStep 55985833 = 41989375) B41989375
theorem B298591109 : Blo 1915435 298591109 := bstep (se 4 (by rfl) ⟨27992916, by rfl⟩ : syracuseStep 298591109 = 55985833) B55985833
theorem B199060739 : Blo 1915435 199060739 := bstep (se 1 (by rfl) ⟨149295554, by rfl⟩ : syracuseStep 199060739 = 298591109) B298591109
theorem B132707159 : Blo 1915435 132707159 := bstep (se 1 (by rfl) ⟨99530369, by rfl⟩ : syracuseStep 132707159 = 199060739) B199060739
theorem B88471439 : Blo 1915435 88471439 := bstep (se 1 (by rfl) ⟨66353579, by rfl⟩ : syracuseStep 88471439 = 132707159) B132707159
theorem B58980959 : Blo 1915435 58980959 := bstep (se 1 (by rfl) ⟨44235719, by rfl⟩ : syracuseStep 58980959 = 88471439) B88471439
theorem B39320639 : Blo 1915435 39320639 := bstep (se 1 (by rfl) ⟨29490479, by rfl⟩ : syracuseStep 39320639 = 58980959) B58980959
theorem B26213759 : Blo 1915435 26213759 := bstep (se 1 (by rfl) ⟨19660319, by rfl⟩ : syracuseStep 26213759 = 39320639) B39320639
theorem B17475839 : Blo 1915435 17475839 := bstep (se 1 (by rfl) ⟨13106879, by rfl⟩ : syracuseStep 17475839 = 26213759) B26213759
theorem B11650559 : Blo 1915435 11650559 := bstep (se 1 (by rfl) ⟨8737919, by rfl⟩ : syracuseStep 11650559 = 17475839) B17475839
theorem B31068157 : Blo 1915435 31068157 := bstep (se 3 (by rfl) ⟨5825279, by rfl⟩ : syracuseStep 31068157 = 11650559) B11650559
theorem B41424209 : Blo 1915435 41424209 := bstep (se 2 (by rfl) ⟨15534078, by rfl⟩ : syracuseStep 41424209 = 31068157) B31068157
theorem B27616139 : Blo 1915435 27616139 := bstep (se 1 (by rfl) ⟨20712104, by rfl⟩ : syracuseStep 27616139 = 41424209) B41424209
theorem B18410759 : Blo 1915435 18410759 := bstep (se 1 (by rfl) ⟨13808069, by rfl⟩ : syracuseStep 18410759 = 27616139) B27616139
theorem B12273839 : Blo 1915435 12273839 := bstep (se 1 (by rfl) ⟨9205379, by rfl⟩ : syracuseStep 12273839 = 18410759) B18410759
theorem B8182559 : Blo 1915435 8182559 := bstep (se 1 (by rfl) ⟨6136919, by rfl⟩ : syracuseStep 8182559 = 12273839) B12273839
theorem B5455039 : Blo 1915435 5455039 := bstep (se 1 (by rfl) ⟨4091279, by rfl⟩ : syracuseStep 5455039 = 8182559) B8182559
theorem B7273385 : Blo 1915435 7273385 := bstep (se 2 (by rfl) ⟨2727519, by rfl⟩ : syracuseStep 7273385 = 5455039) B5455039
theorem B4848923 : Blo 1915435 4848923 := bstep (se 1 (by rfl) ⟨3636692, by rfl⟩ : syracuseStep 4848923 = 7273385) B7273385
theorem B3232615 : Blo 1915435 3232615 := bstep (se 1 (by rfl) ⟨2424461, by rfl⟩ : syracuseStep 3232615 = 4848923) B4848923
theorem B4310153 : Blo 1915435 4310153 := bstep (se 2 (by rfl) ⟨1616307, by rfl⟩ : syracuseStep 4310153 = 3232615) B3232615
theorem B2873435 : Blo 1915435 2873435 := bstep (se 1 (by rfl) ⟨2155076, by rfl⟩ : syracuseStep 2873435 = 4310153) B4310153
theorem B1915623 : Blo 1915435 1915623 := bstep (se 1 (by rfl) ⟨1436717, by rfl⟩ : syracuseStep 1915623 = 2873435) B2873435
theorem B2155081 : Blo 1915435 2155081 := bbase (se 2 (by rfl) ⟨808155, by rfl⟩ : syracuseStep 2155081 = 1616311) (by norm_num)
theorem B2873441 : Blo 1915435 2873441 := bstep (se 2 (by rfl) ⟨1077540, by rfl⟩ : syracuseStep 2873441 = 2155081) B2155081
theorem B1915627 : Blo 1915435 1915627 := bstep (se 1 (by rfl) ⟨1436720, by rfl⟩ : syracuseStep 1915627 = 2873441) B2873441
theorem B3152773 : Blo 1915435 3152773 := bbase (se 4 (by rfl) ⟨295572, by rfl⟩ : syracuseStep 3152773 = 591145) (by norm_num)
theorem B16814789 : Blo 1915435 16814789 := bstep (se 4 (by rfl) ⟨1576386, by rfl⟩ : syracuseStep 16814789 = 3152773) B3152773
theorem B11209859 : Blo 1915435 11209859 := bstep (se 1 (by rfl) ⟨8407394, by rfl⟩ : syracuseStep 11209859 = 16814789) B16814789
theorem B7473239 : Blo 1915435 7473239 := bstep (se 1 (by rfl) ⟨5604929, by rfl⟩ : syracuseStep 7473239 = 11209859) B11209859
theorem B4982159 : Blo 1915435 4982159 := bstep (se 1 (by rfl) ⟨3736619, by rfl⟩ : syracuseStep 4982159 = 7473239) B7473239
theorem B13285757 : Blo 1915435 13285757 := bstep (se 3 (by rfl) ⟨2491079, by rfl⟩ : syracuseStep 13285757 = 4982159) B4982159
theorem B8857171 : Blo 1915435 8857171 := bstep (se 1 (by rfl) ⟨6642878, by rfl⟩ : syracuseStep 8857171 = 13285757) B13285757
theorem B11809561 : Blo 1915435 11809561 := bstep (se 2 (by rfl) ⟨4428585, by rfl⟩ : syracuseStep 11809561 = 8857171) B8857171
theorem B15746081 : Blo 1915435 15746081 := bstep (se 2 (by rfl) ⟨5904780, by rfl⟩ : syracuseStep 15746081 = 11809561) B11809561
theorem B167958197 : Blo 1915435 167958197 := bstep (se 5 (by rfl) ⟨7873040, by rfl⟩ : syracuseStep 167958197 = 15746081) B15746081
theorem B111972131 : Blo 1915435 111972131 := bstep (se 1 (by rfl) ⟨83979098, by rfl⟩ : syracuseStep 111972131 = 167958197) B167958197
theorem B74648087 : Blo 1915435 74648087 := bstep (se 1 (by rfl) ⟨55986065, by rfl⟩ : syracuseStep 74648087 = 111972131) B111972131
theorem B49765391 : Blo 1915435 49765391 := bstep (se 1 (by rfl) ⟨37324043, by rfl⟩ : syracuseStep 49765391 = 74648087) B74648087
theorem B33176927 : Blo 1915435 33176927 := bstep (se 1 (by rfl) ⟨24882695, by rfl⟩ : syracuseStep 33176927 = 49765391) B49765391
theorem B22117951 : Blo 1915435 22117951 := bstep (se 1 (by rfl) ⟨16588463, by rfl⟩ : syracuseStep 22117951 = 33176927) B33176927
theorem B117962405 : Blo 1915435 117962405 := bstep (se 4 (by rfl) ⟨11058975, by rfl⟩ : syracuseStep 117962405 = 22117951) B22117951
theorem B78641603 : Blo 1915435 78641603 := bstep (se 1 (by rfl) ⟨58981202, by rfl⟩ : syracuseStep 78641603 = 117962405) B117962405
theorem B52427735 : Blo 1915435 52427735 := bstep (se 1 (by rfl) ⟨39320801, by rfl⟩ : syracuseStep 52427735 = 78641603) B78641603
theorem B34951823 : Blo 1915435 34951823 := bstep (se 1 (by rfl) ⟨26213867, by rfl⟩ : syracuseStep 34951823 = 52427735) B52427735
theorem B23301215 : Blo 1915435 23301215 := bstep (se 1 (by rfl) ⟨17475911, by rfl⟩ : syracuseStep 23301215 = 34951823) B34951823
theorem B15534143 : Blo 1915435 15534143 := bstep (se 1 (by rfl) ⟨11650607, by rfl⟩ : syracuseStep 15534143 = 23301215) B23301215
theorem B10356095 : Blo 1915435 10356095 := bstep (se 1 (by rfl) ⟨7767071, by rfl⟩ : syracuseStep 10356095 = 15534143) B15534143
theorem B6904063 : Blo 1915435 6904063 := bstep (se 1 (by rfl) ⟨5178047, by rfl⟩ : syracuseStep 6904063 = 10356095) B10356095
theorem B9205417 : Blo 1915435 9205417 := bstep (se 2 (by rfl) ⟨3452031, by rfl⟩ : syracuseStep 9205417 = 6904063) B6904063
theorem B12273889 : Blo 1915435 12273889 := bstep (se 2 (by rfl) ⟨4602708, by rfl⟩ : syracuseStep 12273889 = 9205417) B9205417
theorem B16365185 : Blo 1915435 16365185 := bstep (se 2 (by rfl) ⟨6136944, by rfl⟩ : syracuseStep 16365185 = 12273889) B12273889
theorem B10910123 : Blo 1915435 10910123 := bstep (se 1 (by rfl) ⟨8182592, by rfl⟩ : syracuseStep 10910123 = 16365185) B16365185
theorem B7273415 : Blo 1915435 7273415 := bstep (se 1 (by rfl) ⟨5455061, by rfl⟩ : syracuseStep 7273415 = 10910123) B10910123
theorem B4848943 : Blo 1915435 4848943 := bstep (se 1 (by rfl) ⟨3636707, by rfl⟩ : syracuseStep 4848943 = 7273415) B7273415
theorem B6465257 : Blo 1915435 6465257 := bstep (se 2 (by rfl) ⟨2424471, by rfl⟩ : syracuseStep 6465257 = 4848943) B4848943
theorem B4310171 : Blo 1915435 4310171 := bstep (se 1 (by rfl) ⟨3232628, by rfl⟩ : syracuseStep 4310171 = 6465257) B6465257
theorem B2873447 : Blo 1915435 2873447 := bstep (se 1 (by rfl) ⟨2155085, by rfl⟩ : syracuseStep 2873447 = 4310171) B4310171
theorem B1915631 : Blo 1915435 1915631 := bstep (se 1 (by rfl) ⟨1436723, by rfl⟩ : syracuseStep 1915631 = 2873447) B2873447
theorem B2873453 : Blo 1915435 2873453 := bbase (se 3 (by rfl) ⟨538772, by rfl⟩ : syracuseStep 2873453 = 1077545) (by norm_num)
theorem B1915635 : Blo 1915435 1915635 := bstep (se 1 (by rfl) ⟨1436726, by rfl⟩ : syracuseStep 1915635 = 2873453) B2873453
theorem B4310189 : Blo 1915435 4310189 := bbase (se 3 (by rfl) ⟨808160, by rfl⟩ : syracuseStep 4310189 = 1616321) (by norm_num)
theorem B2873459 : Blo 1915435 2873459 := bstep (se 1 (by rfl) ⟨2155094, by rfl⟩ : syracuseStep 2873459 = 4310189) B4310189
theorem B1915639 : Blo 1915435 1915639 := bstep (se 1 (by rfl) ⟨1436729, by rfl⟩ : syracuseStep 1915639 = 2873459) B2873459
theorem B1941781 : Blo 1915435 1941781 := bbase (se 6 (by rfl) ⟨45510, by rfl⟩ : syracuseStep 1941781 = 91021) (by norm_num)
theorem B2589041 : Blo 1915435 2589041 := bstep (se 2 (by rfl) ⟨970890, by rfl⟩ : syracuseStep 2589041 = 1941781) B1941781
theorem B6904109 : Blo 1915435 6904109 := bstep (se 3 (by rfl) ⟨1294520, by rfl⟩ : syracuseStep 6904109 = 2589041) B2589041
theorem B4602739 : Blo 1915435 4602739 := bstep (se 1 (by rfl) ⟨3452054, by rfl⟩ : syracuseStep 4602739 = 6904109) B6904109
theorem B6136985 : Blo 1915435 6136985 := bstep (se 2 (by rfl) ⟨2301369, by rfl⟩ : syracuseStep 6136985 = 4602739) B4602739
theorem B4091323 : Blo 1915435 4091323 := bstep (se 1 (by rfl) ⟨3068492, by rfl⟩ : syracuseStep 4091323 = 6136985) B6136985
theorem B5455097 : Blo 1915435 5455097 := bstep (se 2 (by rfl) ⟨2045661, by rfl⟩ : syracuseStep 5455097 = 4091323) B4091323
theorem B3636731 : Blo 1915435 3636731 := bstep (se 1 (by rfl) ⟨2727548, by rfl⟩ : syracuseStep 3636731 = 5455097) B5455097
theorem B2424487 : Blo 1915435 2424487 := bstep (se 1 (by rfl) ⟨1818365, by rfl⟩ : syracuseStep 2424487 = 3636731) B3636731
theorem B3232649 : Blo 1915435 3232649 := bstep (se 2 (by rfl) ⟨1212243, by rfl⟩ : syracuseStep 3232649 = 2424487) B2424487
theorem B2155099 : Blo 1915435 2155099 := bstep (se 1 (by rfl) ⟨1616324, by rfl⟩ : syracuseStep 2155099 = 3232649) B3232649
theorem B2873465 : Blo 1915435 2873465 := bstep (se 2 (by rfl) ⟨1077549, by rfl⟩ : syracuseStep 2873465 = 2155099) B2155099
theorem B1915643 : Blo 1915435 1915643 := bstep (se 1 (by rfl) ⟨1436732, by rfl⟩ : syracuseStep 1915643 = 2873465) B2873465
theorem B9205493 : Blo 1915435 9205493 := bbase (se 5 (by rfl) ⟨431507, by rfl⟩ : syracuseStep 9205493 = 863015) (by norm_num)
theorem B24547981 : Blo 1915435 24547981 := bstep (se 3 (by rfl) ⟨4602746, by rfl⟩ : syracuseStep 24547981 = 9205493) B9205493
theorem B32730641 : Blo 1915435 32730641 := bstep (se 2 (by rfl) ⟨12273990, by rfl⟩ : syracuseStep 32730641 = 24547981) B24547981
theorem B21820427 : Blo 1915435 21820427 := bstep (se 1 (by rfl) ⟨16365320, by rfl⟩ : syracuseStep 21820427 = 32730641) B32730641
theorem B14546951 : Blo 1915435 14546951 := bstep (se 1 (by rfl) ⟨10910213, by rfl⟩ : syracuseStep 14546951 = 21820427) B21820427
theorem B9697967 : Blo 1915435 9697967 := bstep (se 1 (by rfl) ⟨7273475, by rfl⟩ : syracuseStep 9697967 = 14546951) B14546951
theorem B6465311 : Blo 1915435 6465311 := bstep (se 1 (by rfl) ⟨4848983, by rfl⟩ : syracuseStep 6465311 = 9697967) B9697967
theorem B4310207 : Blo 1915435 4310207 := bstep (se 1 (by rfl) ⟨3232655, by rfl⟩ : syracuseStep 4310207 = 6465311) B6465311
theorem B2873471 : Blo 1915435 2873471 := bstep (se 1 (by rfl) ⟨2155103, by rfl⟩ : syracuseStep 2873471 = 4310207) B4310207
theorem B1915647 : Blo 1915435 1915647 := bstep (se 1 (by rfl) ⟨1436735, by rfl⟩ : syracuseStep 1915647 = 2873471) B2873471
theorem B2873477 : Blo 1915435 2873477 := bbase (se 4 (by rfl) ⟨269388, by rfl⟩ : syracuseStep 2873477 = 538777) (by norm_num)
theorem B1915651 : Blo 1915435 1915651 := bstep (se 1 (by rfl) ⟨1436738, by rfl⟩ : syracuseStep 1915651 = 2873477) B2873477
theorem B3232669 : Blo 1915435 3232669 := bbase (se 3 (by rfl) ⟨606125, by rfl⟩ : syracuseStep 3232669 = 1212251) (by norm_num)
theorem B4310225 : Blo 1915435 4310225 := bstep (se 2 (by rfl) ⟨1616334, by rfl⟩ : syracuseStep 4310225 = 3232669) B3232669
theorem B2873483 : Blo 1915435 2873483 := bstep (se 1 (by rfl) ⟨2155112, by rfl⟩ : syracuseStep 2873483 = 4310225) B4310225
theorem B1915655 : Blo 1915435 1915655 := bstep (se 1 (by rfl) ⟨1436741, by rfl⟩ : syracuseStep 1915655 = 2873483) B2873483
theorem B2155117 : Blo 1915435 2155117 := bbase (se 3 (by rfl) ⟨404084, by rfl⟩ : syracuseStep 2155117 = 808169) (by norm_num)
theorem B2873489 : Blo 1915435 2873489 := bstep (se 2 (by rfl) ⟨1077558, by rfl⟩ : syracuseStep 2873489 = 2155117) B2155117
theorem B1915659 : Blo 1915435 1915659 := bstep (se 1 (by rfl) ⟨1436744, by rfl⟩ : syracuseStep 1915659 = 2873489) B2873489
theorem B6465365 : Blo 1915435 6465365 := bbase (se 9 (by rfl) ⟨18941, by rfl⟩ : syracuseStep 6465365 = 37883) (by norm_num)
theorem B4310243 : Blo 1915435 4310243 := bstep (se 1 (by rfl) ⟨3232682, by rfl⟩ : syracuseStep 4310243 = 6465365) B6465365
theorem B2873495 : Blo 1915435 2873495 := bstep (se 1 (by rfl) ⟨2155121, by rfl⟩ : syracuseStep 2873495 = 4310243) B4310243
theorem B1915663 : Blo 1915435 1915663 := bstep (se 1 (by rfl) ⟨1436747, by rfl⟩ : syracuseStep 1915663 = 2873495) B2873495
theorem B2873501 : Blo 1915435 2873501 := bbase (se 3 (by rfl) ⟨538781, by rfl⟩ : syracuseStep 2873501 = 1077563) (by norm_num)
theorem B1915667 : Blo 1915435 1915667 := bstep (se 1 (by rfl) ⟨1436750, by rfl⟩ : syracuseStep 1915667 = 2873501) B2873501
theorem B4310261 : Blo 1915435 4310261 := bbase (se 5 (by rfl) ⟨202043, by rfl⟩ : syracuseStep 4310261 = 404087) (by norm_num)
theorem B2873507 : Blo 1915435 2873507 := bstep (se 1 (by rfl) ⟨2155130, by rfl⟩ : syracuseStep 2873507 = 4310261) B4310261
theorem B1915671 : Blo 1915435 1915671 := bstep (se 1 (by rfl) ⟨1436753, by rfl⟩ : syracuseStep 1915671 = 2873507) B2873507
theorem B19660853 : Blo 1915435 19660853 := bbase (se 5 (by rfl) ⟨921602, by rfl⟩ : syracuseStep 19660853 = 1843205) (by norm_num)
theorem B52428941 : Blo 1915435 52428941 := bstep (se 3 (by rfl) ⟨9830426, by rfl⟩ : syracuseStep 52428941 = 19660853) B19660853
theorem B34952627 : Blo 1915435 34952627 := bstep (se 1 (by rfl) ⟨26214470, by rfl⟩ : syracuseStep 34952627 = 52428941) B52428941
theorem B23301751 : Blo 1915435 23301751 := bstep (se 1 (by rfl) ⟨17476313, by rfl⟩ : syracuseStep 23301751 = 34952627) B34952627
theorem B31069001 : Blo 1915435 31069001 := bstep (se 2 (by rfl) ⟨11650875, by rfl⟩ : syracuseStep 31069001 = 23301751) B23301751
theorem B20712667 : Blo 1915435 20712667 := bstep (se 1 (by rfl) ⟨15534500, by rfl⟩ : syracuseStep 20712667 = 31069001) B31069001
theorem B27616889 : Blo 1915435 27616889 := bstep (se 2 (by rfl) ⟨10356333, by rfl⟩ : syracuseStep 27616889 = 20712667) B20712667
theorem B18411259 : Blo 1915435 18411259 := bstep (se 1 (by rfl) ⟨13808444, by rfl⟩ : syracuseStep 18411259 = 27616889) B27616889
theorem B24548345 : Blo 1915435 24548345 := bstep (se 2 (by rfl) ⟨9205629, by rfl⟩ : syracuseStep 24548345 = 18411259) B18411259
theorem B16365563 : Blo 1915435 16365563 := bstep (se 1 (by rfl) ⟨12274172, by rfl⟩ : syracuseStep 16365563 = 24548345) B24548345
theorem B10910375 : Blo 1915435 10910375 := bstep (se 1 (by rfl) ⟨8182781, by rfl⟩ : syracuseStep 10910375 = 16365563) B16365563
theorem B7273583 : Blo 1915435 7273583 := bstep (se 1 (by rfl) ⟨5455187, by rfl⟩ : syracuseStep 7273583 = 10910375) B10910375
theorem B4849055 : Blo 1915435 4849055 := bstep (se 1 (by rfl) ⟨3636791, by rfl⟩ : syracuseStep 4849055 = 7273583) B7273583
theorem B3232703 : Blo 1915435 3232703 := bstep (se 1 (by rfl) ⟨2424527, by rfl⟩ : syracuseStep 3232703 = 4849055) B4849055
theorem B2155135 : Blo 1915435 2155135 := bstep (se 1 (by rfl) ⟨1616351, by rfl⟩ : syracuseStep 2155135 = 3232703) B3232703
theorem B2873513 : Blo 1915435 2873513 := bstep (se 2 (by rfl) ⟨1077567, by rfl⟩ : syracuseStep 2873513 = 2155135) B2155135
theorem B1915675 : Blo 1915435 1915675 := bstep (se 1 (by rfl) ⟨1436756, by rfl⟩ : syracuseStep 1915675 = 2873513) B2873513
theorem B1941817 : Blo 1915435 1941817 := bbase (se 2 (by rfl) ⟨728181, by rfl⟩ : syracuseStep 1941817 = 1456363) (by norm_num)
theorem B2589089 : Blo 1915435 2589089 := bstep (se 2 (by rfl) ⟨970908, by rfl⟩ : syracuseStep 2589089 = 1941817) B1941817
theorem B6904237 : Blo 1915435 6904237 := bstep (se 3 (by rfl) ⟨1294544, by rfl⟩ : syracuseStep 6904237 = 2589089) B2589089
theorem B9205649 : Blo 1915435 9205649 := bstep (se 2 (by rfl) ⟨3452118, by rfl⟩ : syracuseStep 9205649 = 6904237) B6904237
theorem B6137099 : Blo 1915435 6137099 := bstep (se 1 (by rfl) ⟨4602824, by rfl⟩ : syracuseStep 6137099 = 9205649) B9205649
theorem B4091399 : Blo 1915435 4091399 := bstep (se 1 (by rfl) ⟨3068549, by rfl⟩ : syracuseStep 4091399 = 6137099) B6137099
theorem B2727599 : Blo 1915435 2727599 := bstep (se 1 (by rfl) ⟨2045699, by rfl⟩ : syracuseStep 2727599 = 4091399) B4091399
theorem B7273597 : Blo 1915435 7273597 := bstep (se 3 (by rfl) ⟨1363799, by rfl⟩ : syracuseStep 7273597 = 2727599) B2727599
theorem B9698129 : Blo 1915435 9698129 := bstep (se 2 (by rfl) ⟨3636798, by rfl⟩ : syracuseStep 9698129 = 7273597) B7273597
theorem B6465419 : Blo 1915435 6465419 := bstep (se 1 (by rfl) ⟨4849064, by rfl⟩ : syracuseStep 6465419 = 9698129) B9698129
theorem B4310279 : Blo 1915435 4310279 := bstep (se 1 (by rfl) ⟨3232709, by rfl⟩ : syracuseStep 4310279 = 6465419) B6465419
theorem B2873519 : Blo 1915435 2873519 := bstep (se 1 (by rfl) ⟨2155139, by rfl⟩ : syracuseStep 2873519 = 4310279) B4310279
theorem B1915679 : Blo 1915435 1915679 := bstep (se 1 (by rfl) ⟨1436759, by rfl⟩ : syracuseStep 1915679 = 2873519) B2873519
theorem B2873525 : Blo 1915435 2873525 := bbase (se 5 (by rfl) ⟨134696, by rfl⟩ : syracuseStep 2873525 = 269393) (by norm_num)
theorem B1915683 : Blo 1915435 1915683 := bstep (se 1 (by rfl) ⟨1436762, by rfl⟩ : syracuseStep 1915683 = 2873525) B2873525
theorem B4849085 : Blo 1915435 4849085 := bbase (se 3 (by rfl) ⟨909203, by rfl⟩ : syracuseStep 4849085 = 1818407) (by norm_num)
theorem B3232723 : Blo 1915435 3232723 := bstep (se 1 (by rfl) ⟨2424542, by rfl⟩ : syracuseStep 3232723 = 4849085) B4849085
theorem B4310297 : Blo 1915435 4310297 := bstep (se 2 (by rfl) ⟨1616361, by rfl⟩ : syracuseStep 4310297 = 3232723) B3232723
theorem B2873531 : Blo 1915435 2873531 := bstep (se 1 (by rfl) ⟨2155148, by rfl⟩ : syracuseStep 2873531 = 4310297) B4310297
theorem B1915687 : Blo 1915435 1915687 := bstep (se 1 (by rfl) ⟨1436765, by rfl⟩ : syracuseStep 1915687 = 2873531) B2873531
theorem B2155153 : Blo 1915435 2155153 := bbase (se 2 (by rfl) ⟨808182, by rfl⟩ : syracuseStep 2155153 = 1616365) (by norm_num)
theorem B2873537 : Blo 1915435 2873537 := bstep (se 2 (by rfl) ⟨1077576, by rfl⟩ : syracuseStep 2873537 = 2155153) B2155153
theorem B1915691 : Blo 1915435 1915691 := bstep (se 1 (by rfl) ⟨1436768, by rfl⟩ : syracuseStep 1915691 = 2873537) B2873537
theorem B3636829 : Blo 1915435 3636829 := bbase (se 3 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 3636829 = 1363811) (by norm_num)
theorem B4849105 : Blo 1915435 4849105 := bstep (se 2 (by rfl) ⟨1818414, by rfl⟩ : syracuseStep 4849105 = 3636829) B3636829
theorem B6465473 : Blo 1915435 6465473 := bstep (se 2 (by rfl) ⟨2424552, by rfl⟩ : syracuseStep 6465473 = 4849105) B4849105
theorem B4310315 : Blo 1915435 4310315 := bstep (se 1 (by rfl) ⟨3232736, by rfl⟩ : syracuseStep 4310315 = 6465473) B6465473
theorem B2873543 : Blo 1915435 2873543 := bstep (se 1 (by rfl) ⟨2155157, by rfl⟩ : syracuseStep 2873543 = 4310315) B4310315
theorem B1915695 : Blo 1915435 1915695 := bstep (se 1 (by rfl) ⟨1436771, by rfl⟩ : syracuseStep 1915695 = 2873543) B2873543
theorem B2873549 : Blo 1915435 2873549 := bbase (se 3 (by rfl) ⟨538790, by rfl⟩ : syracuseStep 2873549 = 1077581) (by norm_num)
theorem B1915699 : Blo 1915435 1915699 := bstep (se 1 (by rfl) ⟨1436774, by rfl⟩ : syracuseStep 1915699 = 2873549) B2873549
theorem B4310333 : Blo 1915435 4310333 := bbase (se 3 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 4310333 = 1616375) (by norm_num)
theorem B2873555 : Blo 1915435 2873555 := bstep (se 1 (by rfl) ⟨2155166, by rfl⟩ : syracuseStep 2873555 = 4310333) B4310333
theorem B1915703 : Blo 1915435 1915703 := bstep (se 1 (by rfl) ⟨1436777, by rfl⟩ : syracuseStep 1915703 = 2873555) B2873555
theorem B3232757 : Blo 1915435 3232757 := bbase (se 5 (by rfl) ⟨151535, by rfl⟩ : syracuseStep 3232757 = 303071) (by norm_num)
theorem B2155171 : Blo 1915435 2155171 := bstep (se 1 (by rfl) ⟨1616378, by rfl⟩ : syracuseStep 2155171 = 3232757) B3232757
theorem B2873561 : Blo 1915435 2873561 := bstep (se 2 (by rfl) ⟨1077585, by rfl⟩ : syracuseStep 2873561 = 2155171) B2155171
theorem B1915707 : Blo 1915435 1915707 := bstep (se 1 (by rfl) ⟨1436780, by rfl⟩ : syracuseStep 1915707 = 2873561) B2873561
theorem B4602901 : Blo 1915435 4602901 := bbase (se 6 (by rfl) ⟨107880, by rfl⟩ : syracuseStep 4602901 = 215761) (by norm_num)
theorem B6137201 : Blo 1915435 6137201 := bstep (se 2 (by rfl) ⟨2301450, by rfl⟩ : syracuseStep 6137201 = 4602901) B4602901
theorem B4091467 : Blo 1915435 4091467 := bstep (se 1 (by rfl) ⟨3068600, by rfl⟩ : syracuseStep 4091467 = 6137201) B6137201
theorem B5455289 : Blo 1915435 5455289 := bstep (se 2 (by rfl) ⟨2045733, by rfl⟩ : syracuseStep 5455289 = 4091467) B4091467
theorem B14547437 : Blo 1915435 14547437 := bstep (se 3 (by rfl) ⟨2727644, by rfl⟩ : syracuseStep 14547437 = 5455289) B5455289
theorem B9698291 : Blo 1915435 9698291 := bstep (se 1 (by rfl) ⟨7273718, by rfl⟩ : syracuseStep 9698291 = 14547437) B14547437
theorem B6465527 : Blo 1915435 6465527 := bstep (se 1 (by rfl) ⟨4849145, by rfl⟩ : syracuseStep 6465527 = 9698291) B9698291
theorem B4310351 : Blo 1915435 4310351 := bstep (se 1 (by rfl) ⟨3232763, by rfl⟩ : syracuseStep 4310351 = 6465527) B6465527
theorem B2873567 : Blo 1915435 2873567 := bstep (se 1 (by rfl) ⟨2155175, by rfl⟩ : syracuseStep 2873567 = 4310351) B4310351
theorem B1915711 : Blo 1915435 1915711 := bstep (se 1 (by rfl) ⟨1436783, by rfl⟩ : syracuseStep 1915711 = 2873567) B2873567
theorem B2873573 : Blo 1915435 2873573 := bbase (se 4 (by rfl) ⟨269397, by rfl⟩ : syracuseStep 2873573 = 538795) (by norm_num)
theorem B1915715 : Blo 1915435 1915715 := bstep (se 1 (by rfl) ⟨1436786, by rfl⟩ : syracuseStep 1915715 = 2873573) B2873573
theorem B4091485 : Blo 1915435 4091485 := bbase (se 3 (by rfl) ⟨767153, by rfl⟩ : syracuseStep 4091485 = 1534307) (by norm_num)
theorem B5455313 : Blo 1915435 5455313 := bstep (se 2 (by rfl) ⟨2045742, by rfl⟩ : syracuseStep 5455313 = 4091485) B4091485
theorem B3636875 : Blo 1915435 3636875 := bstep (se 1 (by rfl) ⟨2727656, by rfl⟩ : syracuseStep 3636875 = 5455313) B5455313
theorem B2424583 : Blo 1915435 2424583 := bstep (se 1 (by rfl) ⟨1818437, by rfl⟩ : syracuseStep 2424583 = 3636875) B3636875
theorem B3232777 : Blo 1915435 3232777 := bstep (se 2 (by rfl) ⟨1212291, by rfl⟩ : syracuseStep 3232777 = 2424583) B2424583
theorem B4310369 : Blo 1915435 4310369 := bstep (se 2 (by rfl) ⟨1616388, by rfl⟩ : syracuseStep 4310369 = 3232777) B3232777
theorem B2873579 : Blo 1915435 2873579 := bstep (se 1 (by rfl) ⟨2155184, by rfl⟩ : syracuseStep 2873579 = 4310369) B4310369
theorem B1915719 : Blo 1915435 1915719 := bstep (se 1 (by rfl) ⟨1436789, by rfl⟩ : syracuseStep 1915719 = 2873579) B2873579
theorem B2155189 : Blo 1915435 2155189 := bbase (se 5 (by rfl) ⟨101024, by rfl⟩ : syracuseStep 2155189 = 202049) (by norm_num)
theorem B2873585 : Blo 1915435 2873585 := bstep (se 2 (by rfl) ⟨1077594, by rfl⟩ : syracuseStep 2873585 = 2155189) B2155189
theorem B1915723 : Blo 1915435 1915723 := bstep (se 1 (by rfl) ⟨1436792, by rfl⟩ : syracuseStep 1915723 = 2873585) B2873585
theorem B2424593 : Blo 1915435 2424593 := bbase (se 2 (by rfl) ⟨909222, by rfl⟩ : syracuseStep 2424593 = 1818445) (by norm_num)
theorem B6465581 : Blo 1915435 6465581 := bstep (se 3 (by rfl) ⟨1212296, by rfl⟩ : syracuseStep 6465581 = 2424593) B2424593
theorem B4310387 : Blo 1915435 4310387 := bstep (se 1 (by rfl) ⟨3232790, by rfl⟩ : syracuseStep 4310387 = 6465581) B6465581
theorem B2873591 : Blo 1915435 2873591 := bstep (se 1 (by rfl) ⟨2155193, by rfl⟩ : syracuseStep 2873591 = 4310387) B4310387
theorem B1915727 : Blo 1915435 1915727 := bstep (se 1 (by rfl) ⟨1436795, by rfl⟩ : syracuseStep 1915727 = 2873591) B2873591
theorem B2873597 : Blo 1915435 2873597 := bbase (se 3 (by rfl) ⟨538799, by rfl⟩ : syracuseStep 2873597 = 1077599) (by norm_num)
theorem B1915731 : Blo 1915435 1915731 := bstep (se 1 (by rfl) ⟨1436798, by rfl⟩ : syracuseStep 1915731 = 2873597) B2873597
theorem B4310405 : Blo 1915435 4310405 := bbase (se 4 (by rfl) ⟨404100, by rfl⟩ : syracuseStep 4310405 = 808201) (by norm_num)
theorem B2873603 : Blo 1915435 2873603 := bstep (se 1 (by rfl) ⟨2155202, by rfl⟩ : syracuseStep 2873603 = 4310405) B4310405
theorem B1915735 : Blo 1915435 1915735 := bstep (se 1 (by rfl) ⟨1436801, by rfl⟩ : syracuseStep 1915735 = 2873603) B2873603
theorem B2727685 : Blo 1915435 2727685 := bbase (se 4 (by rfl) ⟨255720, by rfl⟩ : syracuseStep 2727685 = 511441) (by norm_num)
theorem B3636913 : Blo 1915435 3636913 := bstep (se 2 (by rfl) ⟨1363842, by rfl⟩ : syracuseStep 3636913 = 2727685) B2727685
theorem B4849217 : Blo 1915435 4849217 := bstep (se 2 (by rfl) ⟨1818456, by rfl⟩ : syracuseStep 4849217 = 3636913) B3636913
theorem B3232811 : Blo 1915435 3232811 := bstep (se 1 (by rfl) ⟨2424608, by rfl⟩ : syracuseStep 3232811 = 4849217) B4849217
theorem B2155207 : Blo 1915435 2155207 := bstep (se 1 (by rfl) ⟨1616405, by rfl⟩ : syracuseStep 2155207 = 3232811) B3232811
theorem B2873609 : Blo 1915435 2873609 := bstep (se 2 (by rfl) ⟨1077603, by rfl⟩ : syracuseStep 2873609 = 2155207) B2155207
theorem B1915739 : Blo 1915435 1915739 := bstep (se 1 (by rfl) ⟨1436804, by rfl⟩ : syracuseStep 1915739 = 2873609) B2873609
theorem B9698453 : Blo 1915435 9698453 := bbase (se 6 (by rfl) ⟨227307, by rfl⟩ : syracuseStep 9698453 = 454615) (by norm_num)
theorem B6465635 : Blo 1915435 6465635 := bstep (se 1 (by rfl) ⟨4849226, by rfl⟩ : syracuseStep 6465635 = 9698453) B9698453
theorem B4310423 : Blo 1915435 4310423 := bstep (se 1 (by rfl) ⟨3232817, by rfl⟩ : syracuseStep 4310423 = 6465635) B6465635
theorem B2873615 : Blo 1915435 2873615 := bstep (se 1 (by rfl) ⟨2155211, by rfl⟩ : syracuseStep 2873615 = 4310423) B4310423
theorem B1915743 : Blo 1915435 1915743 := bstep (se 1 (by rfl) ⟨1436807, by rfl⟩ : syracuseStep 1915743 = 2873615) B2873615
theorem B2873621 : Blo 1915435 2873621 := bbase (se 6 (by rfl) ⟨67350, by rfl⟩ : syracuseStep 2873621 = 134701) (by norm_num)
theorem B1915747 : Blo 1915435 1915747 := bstep (se 1 (by rfl) ⟨1436810, by rfl⟩ : syracuseStep 1915747 = 2873621) B2873621
theorem B4602997 : Blo 1915435 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B24549317 : Blo 1915435 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B16366211 : Blo 1915435 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B10910807 : Blo 1915435 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B7273871 : Blo 1915435 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B4849247 : Blo 1915435 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B3232831 : Blo 1915435 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B4310441 : Blo 1915435 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B2873627 : Blo 1915435 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B1915751 : Blo 1915435 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B2155225 : Blo 1915435 2155225 := bbase (se 2 (by rfl) ⟨808209, by rfl⟩ : syracuseStep 2155225 = 1616419) (by norm_num)
theorem B2873633 : Blo 1915435 2873633 := bstep (se 2 (by rfl) ⟨1077612, by rfl⟩ : syracuseStep 2873633 = 2155225) B2155225
theorem B1915755 : Blo 1915435 1915755 := bstep (se 1 (by rfl) ⟨1436816, by rfl⟩ : syracuseStep 1915755 = 2873633) B2873633
theorem B2045785 : Blo 1915435 2045785 := bbase (se 2 (by rfl) ⟨767169, by rfl⟩ : syracuseStep 2045785 = 1534339) (by norm_num)
theorem B2727713 : Blo 1915435 2727713 := bstep (se 2 (by rfl) ⟨1022892, by rfl⟩ : syracuseStep 2727713 = 2045785) B2045785
theorem B7273901 : Blo 1915435 7273901 := bstep (se 3 (by rfl) ⟨1363856, by rfl⟩ : syracuseStep 7273901 = 2727713) B2727713
theorem B4849267 : Blo 1915435 4849267 := bstep (se 1 (by rfl) ⟨3636950, by rfl⟩ : syracuseStep 4849267 = 7273901) B7273901
theorem B6465689 : Blo 1915435 6465689 := bstep (se 2 (by rfl) ⟨2424633, by rfl⟩ : syracuseStep 6465689 = 4849267) B4849267
theorem B4310459 : Blo 1915435 4310459 := bstep (se 1 (by rfl) ⟨3232844, by rfl⟩ : syracuseStep 4310459 = 6465689) B6465689
theorem B2873639 : Blo 1915435 2873639 := bstep (se 1 (by rfl) ⟨2155229, by rfl⟩ : syracuseStep 2873639 = 4310459) B4310459
theorem B1915759 : Blo 1915435 1915759 := bstep (se 1 (by rfl) ⟨1436819, by rfl⟩ : syracuseStep 1915759 = 2873639) B2873639
theorem B2873645 : Blo 1915435 2873645 := bbase (se 3 (by rfl) ⟨538808, by rfl⟩ : syracuseStep 2873645 = 1077617) (by norm_num)
theorem B1915763 : Blo 1915435 1915763 := bstep (se 1 (by rfl) ⟨1436822, by rfl⟩ : syracuseStep 1915763 = 2873645) B2873645
theorem B4310477 : Blo 1915435 4310477 := bbase (se 3 (by rfl) ⟨808214, by rfl⟩ : syracuseStep 4310477 = 1616429) (by norm_num)
theorem B2873651 : Blo 1915435 2873651 := bstep (se 1 (by rfl) ⟨2155238, by rfl⟩ : syracuseStep 2873651 = 4310477) B4310477
theorem B1915767 : Blo 1915435 1915767 := bstep (se 1 (by rfl) ⟨1436825, by rfl⟩ : syracuseStep 1915767 = 2873651) B2873651
theorem B2424649 : Blo 1915435 2424649 := bbase (se 2 (by rfl) ⟨909243, by rfl⟩ : syracuseStep 2424649 = 1818487) (by norm_num)
theorem B3232865 : Blo 1915435 3232865 := bstep (se 2 (by rfl) ⟨1212324, by rfl⟩ : syracuseStep 3232865 = 2424649) B2424649
theorem B2155243 : Blo 1915435 2155243 := bstep (se 1 (by rfl) ⟨1616432, by rfl⟩ : syracuseStep 2155243 = 3232865) B3232865
theorem B2873657 : Blo 1915435 2873657 := bstep (se 2 (by rfl) ⟨1077621, by rfl⟩ : syracuseStep 2873657 = 2155243) B2155243
theorem B1915771 : Blo 1915435 1915771 := bstep (se 1 (by rfl) ⟨1436828, by rfl⟩ : syracuseStep 1915771 = 2873657) B2873657
theorem B2184653 : Blo 1915435 2184653 := bbase (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) (by norm_num)
theorem B5825741 : Blo 1915435 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B15535309 : Blo 1915435 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B20713745 : Blo 1915435 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B13809163 : Blo 1915435 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B18412217 : Blo 1915435 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B12274811 : Blo 1915435 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B8183207 : Blo 1915435 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B21821885 : Blo 1915435 21821885 := bstep (se 3 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 21821885 = 8183207) B8183207
theorem B14547923 : Blo 1915435 14547923 := bstep (se 1 (by rfl) ⟨10910942, by rfl⟩ : syracuseStep 14547923 = 21821885) B21821885
theorem B9698615 : Blo 1915435 9698615 := bstep (se 1 (by rfl) ⟨7273961, by rfl⟩ : syracuseStep 9698615 = 14547923) B14547923
theorem B6465743 : Blo 1915435 6465743 := bstep (se 1 (by rfl) ⟨4849307, by rfl⟩ : syracuseStep 6465743 = 9698615) B9698615
theorem B4310495 : Blo 1915435 4310495 := bstep (se 1 (by rfl) ⟨3232871, by rfl⟩ : syracuseStep 4310495 = 6465743) B6465743
theorem B2873663 : Blo 1915435 2873663 := bstep (se 1 (by rfl) ⟨2155247, by rfl⟩ : syracuseStep 2873663 = 4310495) B4310495
theorem B1915775 : Blo 1915435 1915775 := bstep (se 1 (by rfl) ⟨1436831, by rfl⟩ : syracuseStep 1915775 = 2873663) B2873663
theorem B2873669 : Blo 1915435 2873669 := bbase (se 4 (by rfl) ⟨269406, by rfl⟩ : syracuseStep 2873669 = 538813) (by norm_num)
theorem B1915779 : Blo 1915435 1915779 := bstep (se 1 (by rfl) ⟨1436834, by rfl⟩ : syracuseStep 1915779 = 2873669) B2873669
theorem B3232885 : Blo 1915435 3232885 := bbase (se 5 (by rfl) ⟨151541, by rfl⟩ : syracuseStep 3232885 = 303083) (by norm_num)
theorem B4310513 : Blo 1915435 4310513 := bstep (se 2 (by rfl) ⟨1616442, by rfl⟩ : syracuseStep 4310513 = 3232885) B3232885
theorem B2873675 : Blo 1915435 2873675 := bstep (se 1 (by rfl) ⟨2155256, by rfl⟩ : syracuseStep 2873675 = 4310513) B4310513
theorem B1915783 : Blo 1915435 1915783 := bstep (se 1 (by rfl) ⟨1436837, by rfl⟩ : syracuseStep 1915783 = 2873675) B2873675
theorem B2155261 : Blo 1915435 2155261 := bbase (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) (by norm_num)
theorem B2873681 : Blo 1915435 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B1915787 : Blo 1915435 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B6465797 : Blo 1915435 6465797 := bbase (se 4 (by rfl) ⟨606168, by rfl⟩ : syracuseStep 6465797 = 1212337) (by norm_num)
theorem B4310531 : Blo 1915435 4310531 := bstep (se 1 (by rfl) ⟨3232898, by rfl⟩ : syracuseStep 4310531 = 6465797) B6465797
theorem B2873687 : Blo 1915435 2873687 := bstep (se 1 (by rfl) ⟨2155265, by rfl⟩ : syracuseStep 2873687 = 4310531) B4310531
theorem B1915791 : Blo 1915435 1915791 := bstep (se 1 (by rfl) ⟨1436843, by rfl⟩ : syracuseStep 1915791 = 2873687) B2873687
theorem B2873693 : Blo 1915435 2873693 := bbase (se 3 (by rfl) ⟨538817, by rfl⟩ : syracuseStep 2873693 = 1077635) (by norm_num)
theorem B1915795 : Blo 1915435 1915795 := bstep (se 1 (by rfl) ⟨1436846, by rfl⟩ : syracuseStep 1915795 = 2873693) B2873693
theorem B4310549 : Blo 1915435 4310549 := bbase (se 6 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 4310549 = 202057) (by norm_num)
theorem B2873699 : Blo 1915435 2873699 := bstep (se 1 (by rfl) ⟨2155274, by rfl⟩ : syracuseStep 2873699 = 4310549) B4310549
theorem B1915799 : Blo 1915435 1915799 := bstep (se 1 (by rfl) ⟨1436849, by rfl⟩ : syracuseStep 1915799 = 2873699) B2873699
theorem B7274069 : Blo 1915435 7274069 := bbase (se 8 (by rfl) ⟨42621, by rfl⟩ : syracuseStep 7274069 = 85243) (by norm_num)
theorem B4849379 : Blo 1915435 4849379 := bstep (se 1 (by rfl) ⟨3637034, by rfl⟩ : syracuseStep 4849379 = 7274069) B7274069
theorem B3232919 : Blo 1915435 3232919 := bstep (se 1 (by rfl) ⟨2424689, by rfl⟩ : syracuseStep 3232919 = 4849379) B4849379
theorem B2155279 : Blo 1915435 2155279 := bstep (se 1 (by rfl) ⟨1616459, by rfl⟩ : syracuseStep 2155279 = 3232919) B3232919
theorem B2873705 : Blo 1915435 2873705 := bstep (se 2 (by rfl) ⟨1077639, by rfl⟩ : syracuseStep 2873705 = 2155279) B2155279
theorem B1915803 : Blo 1915435 1915803 := bstep (se 1 (by rfl) ⟨1436852, by rfl⟩ : syracuseStep 1915803 = 2873705) B2873705
theorem B10911125 : Blo 1915435 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B7274083 : Blo 1915435 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B9698777 : Blo 1915435 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B6465851 : Blo 1915435 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B4310567 : Blo 1915435 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B2873711 : Blo 1915435 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B1915807 : Blo 1915435 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B2873717 : Blo 1915435 2873717 := bbase (se 5 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 2873717 = 269411) (by norm_num)
theorem B1915811 : Blo 1915435 1915811 := bstep (se 1 (by rfl) ⟨1436858, by rfl⟩ : syracuseStep 1915811 = 2873717) B2873717
theorem B2045845 : Blo 1915435 2045845 := bbase (se 6 (by rfl) ⟨47949, by rfl⟩ : syracuseStep 2045845 = 95899) (by norm_num)
theorem B2727793 : Blo 1915435 2727793 := bstep (se 2 (by rfl) ⟨1022922, by rfl⟩ : syracuseStep 2727793 = 2045845) B2045845
theorem B3637057 : Blo 1915435 3637057 := bstep (se 2 (by rfl) ⟨1363896, by rfl⟩ : syracuseStep 3637057 = 2727793) B2727793
theorem B4849409 : Blo 1915435 4849409 := bstep (se 2 (by rfl) ⟨1818528, by rfl⟩ : syracuseStep 4849409 = 3637057) B3637057
theorem B3232939 : Blo 1915435 3232939 := bstep (se 1 (by rfl) ⟨2424704, by rfl⟩ : syracuseStep 3232939 = 4849409) B4849409
theorem B4310585 : Blo 1915435 4310585 := bstep (se 2 (by rfl) ⟨1616469, by rfl⟩ : syracuseStep 4310585 = 3232939) B3232939
theorem B2873723 : Blo 1915435 2873723 := bstep (se 1 (by rfl) ⟨2155292, by rfl⟩ : syracuseStep 2873723 = 4310585) B4310585
theorem B1915815 : Blo 1915435 1915815 := bstep (se 1 (by rfl) ⟨1436861, by rfl⟩ : syracuseStep 1915815 = 2873723) B2873723
theorem B2155297 : Blo 1915435 2155297 := bbase (se 2 (by rfl) ⟨808236, by rfl⟩ : syracuseStep 2155297 = 1616473) (by norm_num)
theorem B2873729 : Blo 1915435 2873729 := bstep (se 2 (by rfl) ⟨1077648, by rfl⟩ : syracuseStep 2873729 = 2155297) B2155297
theorem B1915819 : Blo 1915435 1915819 := bstep (se 1 (by rfl) ⟨1436864, by rfl⟩ : syracuseStep 1915819 = 2873729) B2873729
theorem B4849429 : Blo 1915435 4849429 := bbase (se 6 (by rfl) ⟨113658, by rfl⟩ : syracuseStep 4849429 = 227317) (by norm_num)
theorem B6465905 : Blo 1915435 6465905 := bstep (se 2 (by rfl) ⟨2424714, by rfl⟩ : syracuseStep 6465905 = 4849429) B4849429
theorem B4310603 : Blo 1915435 4310603 := bstep (se 1 (by rfl) ⟨3232952, by rfl⟩ : syracuseStep 4310603 = 6465905) B6465905
theorem B2873735 : Blo 1915435 2873735 := bstep (se 1 (by rfl) ⟨2155301, by rfl⟩ : syracuseStep 2873735 = 4310603) B4310603
theorem B1915823 : Blo 1915435 1915823 := bstep (se 1 (by rfl) ⟨1436867, by rfl⟩ : syracuseStep 1915823 = 2873735) B2873735
theorem B2873741 : Blo 1915435 2873741 := bbase (se 3 (by rfl) ⟨538826, by rfl⟩ : syracuseStep 2873741 = 1077653) (by norm_num)
theorem B1915827 : Blo 1915435 1915827 := bstep (se 1 (by rfl) ⟨1436870, by rfl⟩ : syracuseStep 1915827 = 2873741) B2873741
theorem B4310621 : Blo 1915435 4310621 := bbase (se 3 (by rfl) ⟨808241, by rfl⟩ : syracuseStep 4310621 = 1616483) (by norm_num)
theorem B2873747 : Blo 1915435 2873747 := bstep (se 1 (by rfl) ⟨2155310, by rfl⟩ : syracuseStep 2873747 = 4310621) B4310621
theorem B1915831 : Blo 1915435 1915831 := bstep (se 1 (by rfl) ⟨1436873, by rfl⟩ : syracuseStep 1915831 = 2873747) B2873747
theorem B3232973 : Blo 1915435 3232973 := bbase (se 3 (by rfl) ⟨606182, by rfl⟩ : syracuseStep 3232973 = 1212365) (by norm_num)
theorem B2155315 : Blo 1915435 2155315 := bstep (se 1 (by rfl) ⟨1616486, by rfl⟩ : syracuseStep 2155315 = 3232973) B3232973
theorem B2873753 : Blo 1915435 2873753 := bstep (se 2 (by rfl) ⟨1077657, by rfl⟩ : syracuseStep 2873753 = 2155315) B2155315
theorem B1915835 : Blo 1915435 1915835 := bstep (se 1 (by rfl) ⟨1436876, by rfl⟩ : syracuseStep 1915835 = 2873753) B2873753
theorem B12275221 : Blo 1915435 12275221 := bbase (se 6 (by rfl) ⟨287700, by rfl⟩ : syracuseStep 12275221 = 575401) (by norm_num)
theorem B16366961 : Blo 1915435 16366961 := bstep (se 2 (by rfl) ⟨6137610, by rfl⟩ : syracuseStep 16366961 = 12275221) B12275221
theorem B10911307 : Blo 1915435 10911307 := bstep (se 1 (by rfl) ⟨8183480, by rfl⟩ : syracuseStep 10911307 = 16366961) B16366961
theorem B14548409 : Blo 1915435 14548409 := bstep (se 2 (by rfl) ⟨5455653, by rfl⟩ : syracuseStep 14548409 = 10911307) B10911307
theorem B9698939 : Blo 1915435 9698939 := bstep (se 1 (by rfl) ⟨7274204, by rfl⟩ : syracuseStep 9698939 = 14548409) B14548409
theorem B6465959 : Blo 1915435 6465959 := bstep (se 1 (by rfl) ⟨4849469, by rfl⟩ : syracuseStep 6465959 = 9698939) B9698939
theorem B4310639 : Blo 1915435 4310639 := bstep (se 1 (by rfl) ⟨3232979, by rfl⟩ : syracuseStep 4310639 = 6465959) B6465959
theorem B2873759 : Blo 1915435 2873759 := bstep (se 1 (by rfl) ⟨2155319, by rfl⟩ : syracuseStep 2873759 = 4310639) B4310639
theorem B1915839 : Blo 1915435 1915839 := bstep (se 1 (by rfl) ⟨1436879, by rfl⟩ : syracuseStep 1915839 = 2873759) B2873759
theorem B2873765 : Blo 1915435 2873765 := bbase (se 4 (by rfl) ⟨269415, by rfl⟩ : syracuseStep 2873765 = 538831) (by norm_num)
theorem B1915843 : Blo 1915435 1915843 := bstep (se 1 (by rfl) ⟨1436882, by rfl⟩ : syracuseStep 1915843 = 2873765) B2873765
theorem B2424745 : Blo 1915435 2424745 := bbase (se 2 (by rfl) ⟨909279, by rfl⟩ : syracuseStep 2424745 = 1818559) (by norm_num)
theorem B3232993 : Blo 1915435 3232993 := bstep (se 2 (by rfl) ⟨1212372, by rfl⟩ : syracuseStep 3232993 = 2424745) B2424745
theorem B4310657 : Blo 1915435 4310657 := bstep (se 2 (by rfl) ⟨1616496, by rfl⟩ : syracuseStep 4310657 = 3232993) B3232993
theorem B2873771 : Blo 1915435 2873771 := bstep (se 1 (by rfl) ⟨2155328, by rfl⟩ : syracuseStep 2873771 = 4310657) B4310657
theorem B1915847 : Blo 1915435 1915847 := bstep (se 1 (by rfl) ⟨1436885, by rfl⟩ : syracuseStep 1915847 = 2873771) B2873771
theorem B2155333 : Blo 1915435 2155333 := bbase (se 4 (by rfl) ⟨202062, by rfl⟩ : syracuseStep 2155333 = 404125) (by norm_num)
theorem B2873777 : Blo 1915435 2873777 := bstep (se 2 (by rfl) ⟨1077666, by rfl⟩ : syracuseStep 2873777 = 2155333) B2155333
theorem B1915851 : Blo 1915435 1915851 := bstep (se 1 (by rfl) ⟨1436888, by rfl⟩ : syracuseStep 1915851 = 2873777) B2873777
theorem B3637133 : Blo 1915435 3637133 := bbase (se 3 (by rfl) ⟨681962, by rfl⟩ : syracuseStep 3637133 = 1363925) (by norm_num)
theorem B2424755 : Blo 1915435 2424755 := bstep (se 1 (by rfl) ⟨1818566, by rfl⟩ : syracuseStep 2424755 = 3637133) B3637133
theorem B6466013 : Blo 1915435 6466013 := bstep (se 3 (by rfl) ⟨1212377, by rfl⟩ : syracuseStep 6466013 = 2424755) B2424755
theorem B4310675 : Blo 1915435 4310675 := bstep (se 1 (by rfl) ⟨3233006, by rfl⟩ : syracuseStep 4310675 = 6466013) B6466013
theorem B2873783 : Blo 1915435 2873783 := bstep (se 1 (by rfl) ⟨2155337, by rfl⟩ : syracuseStep 2873783 = 4310675) B4310675
theorem B1915855 : Blo 1915435 1915855 := bstep (se 1 (by rfl) ⟨1436891, by rfl⟩ : syracuseStep 1915855 = 2873783) B2873783
theorem B2873789 : Blo 1915435 2873789 := bbase (se 3 (by rfl) ⟨538835, by rfl⟩ : syracuseStep 2873789 = 1077671) (by norm_num)
theorem B1915859 : Blo 1915435 1915859 := bstep (se 1 (by rfl) ⟨1436894, by rfl⟩ : syracuseStep 1915859 = 2873789) B2873789
theorem B4310693 : Blo 1915435 4310693 := bbase (se 4 (by rfl) ⟨404127, by rfl⟩ : syracuseStep 4310693 = 808255) (by norm_num)
theorem B2873795 : Blo 1915435 2873795 := bstep (se 1 (by rfl) ⟨2155346, by rfl⟩ : syracuseStep 2873795 = 4310693) B4310693
theorem B1915863 : Blo 1915435 1915863 := bstep (se 1 (by rfl) ⟨1436897, by rfl⟩ : syracuseStep 1915863 = 2873795) B2873795
theorem B4849541 : Blo 1915435 4849541 := bbase (se 4 (by rfl) ⟨454644, by rfl⟩ : syracuseStep 4849541 = 909289) (by norm_num)
theorem B3233027 : Blo 1915435 3233027 := bstep (se 1 (by rfl) ⟨2424770, by rfl⟩ : syracuseStep 3233027 = 4849541) B4849541
theorem B2155351 : Blo 1915435 2155351 := bstep (se 1 (by rfl) ⟨1616513, by rfl⟩ : syracuseStep 2155351 = 3233027) B3233027
theorem B2873801 : Blo 1915435 2873801 := bstep (se 2 (by rfl) ⟨1077675, by rfl⟩ : syracuseStep 2873801 = 2155351) B2155351
theorem B1915867 : Blo 1915435 1915867 := bstep (se 1 (by rfl) ⟨1436900, by rfl⟩ : syracuseStep 1915867 = 2873801) B2873801
theorem B2589349 : Blo 1915435 2589349 := bbase (se 4 (by rfl) ⟨242751, by rfl⟩ : syracuseStep 2589349 = 485503) (by norm_num)
theorem B3452465 : Blo 1915435 3452465 := bstep (se 2 (by rfl) ⟨1294674, by rfl⟩ : syracuseStep 3452465 = 2589349) B2589349
theorem B2301643 : Blo 1915435 2301643 := bstep (se 1 (by rfl) ⟨1726232, by rfl⟩ : syracuseStep 2301643 = 3452465) B3452465
theorem B3068857 : Blo 1915435 3068857 := bstep (se 2 (by rfl) ⟨1150821, by rfl⟩ : syracuseStep 3068857 = 2301643) B2301643
theorem B4091809 : Blo 1915435 4091809 := bstep (se 2 (by rfl) ⟨1534428, by rfl⟩ : syracuseStep 4091809 = 3068857) B3068857
theorem B5455745 : Blo 1915435 5455745 := bstep (se 2 (by rfl) ⟨2045904, by rfl⟩ : syracuseStep 5455745 = 4091809) B4091809
theorem B3637163 : Blo 1915435 3637163 := bstep (se 1 (by rfl) ⟨2727872, by rfl⟩ : syracuseStep 3637163 = 5455745) B5455745
theorem B9699101 : Blo 1915435 9699101 := bstep (se 3 (by rfl) ⟨1818581, by rfl⟩ : syracuseStep 9699101 = 3637163) B3637163
theorem B6466067 : Blo 1915435 6466067 := bstep (se 1 (by rfl) ⟨4849550, by rfl⟩ : syracuseStep 6466067 = 9699101) B9699101
theorem B4310711 : Blo 1915435 4310711 := bstep (se 1 (by rfl) ⟨3233033, by rfl⟩ : syracuseStep 4310711 = 6466067) B6466067
theorem B2873807 : Blo 1915435 2873807 := bstep (se 1 (by rfl) ⟨2155355, by rfl⟩ : syracuseStep 2873807 = 4310711) B4310711
theorem B1915871 : Blo 1915435 1915871 := bstep (se 1 (by rfl) ⟨1436903, by rfl⟩ : syracuseStep 1915871 = 2873807) B2873807
theorem B2873813 : Blo 1915435 2873813 := bbase (se 7 (by rfl) ⟨33677, by rfl⟩ : syracuseStep 2873813 = 67355) (by norm_num)
theorem B1915875 : Blo 1915435 1915875 := bstep (se 1 (by rfl) ⟨1436906, by rfl⟩ : syracuseStep 1915875 = 2873813) B2873813
theorem B7274357 : Blo 1915435 7274357 := bbase (se 5 (by rfl) ⟨340985, by rfl⟩ : syracuseStep 7274357 = 681971) (by norm_num)
theorem B4849571 : Blo 1915435 4849571 := bstep (se 1 (by rfl) ⟨3637178, by rfl⟩ : syracuseStep 4849571 = 7274357) B7274357
theorem B3233047 : Blo 1915435 3233047 := bstep (se 1 (by rfl) ⟨2424785, by rfl⟩ : syracuseStep 3233047 = 4849571) B4849571
theorem B4310729 : Blo 1915435 4310729 := bstep (se 2 (by rfl) ⟨1616523, by rfl⟩ : syracuseStep 4310729 = 3233047) B3233047
theorem B2873819 : Blo 1915435 2873819 := bstep (se 1 (by rfl) ⟨2155364, by rfl⟩ : syracuseStep 2873819 = 4310729) B4310729
theorem B1915879 : Blo 1915435 1915879 := bstep (se 1 (by rfl) ⟨1436909, by rfl⟩ : syracuseStep 1915879 = 2873819) B2873819
theorem B2155369 : Blo 1915435 2155369 := bbase (se 2 (by rfl) ⟨808263, by rfl⟩ : syracuseStep 2155369 = 1616527) (by norm_num)
theorem B2873825 : Blo 1915435 2873825 := bstep (se 2 (by rfl) ⟨1077684, by rfl⟩ : syracuseStep 2873825 = 2155369) B2155369
theorem B1915883 : Blo 1915435 1915883 := bstep (se 1 (by rfl) ⟨1436912, by rfl⟩ : syracuseStep 1915883 = 2873825) B2873825
theorem B6137765 : Blo 1915435 6137765 := bbase (se 4 (by rfl) ⟨575415, by rfl⟩ : syracuseStep 6137765 = 1150831) (by norm_num)
theorem B4091843 : Blo 1915435 4091843 := bstep (se 1 (by rfl) ⟨3068882, by rfl⟩ : syracuseStep 4091843 = 6137765) B6137765
theorem B10911581 : Blo 1915435 10911581 := bstep (se 3 (by rfl) ⟨2045921, by rfl⟩ : syracuseStep 10911581 = 4091843) B4091843
theorem B7274387 : Blo 1915435 7274387 := bstep (se 1 (by rfl) ⟨5455790, by rfl⟩ : syracuseStep 7274387 = 10911581) B10911581
theorem B4849591 : Blo 1915435 4849591 := bstep (se 1 (by rfl) ⟨3637193, by rfl⟩ : syracuseStep 4849591 = 7274387) B7274387
theorem B6466121 : Blo 1915435 6466121 := bstep (se 2 (by rfl) ⟨2424795, by rfl⟩ : syracuseStep 6466121 = 4849591) B4849591
theorem B4310747 : Blo 1915435 4310747 := bstep (se 1 (by rfl) ⟨3233060, by rfl⟩ : syracuseStep 4310747 = 6466121) B6466121
theorem B2873831 : Blo 1915435 2873831 := bstep (se 1 (by rfl) ⟨2155373, by rfl⟩ : syracuseStep 2873831 = 4310747) B4310747
theorem B1915887 : Blo 1915435 1915887 := bstep (se 1 (by rfl) ⟨1436915, by rfl⟩ : syracuseStep 1915887 = 2873831) B2873831
theorem B2873837 : Blo 1915435 2873837 := bbase (se 3 (by rfl) ⟨538844, by rfl⟩ : syracuseStep 2873837 = 1077689) (by norm_num)
theorem B1915891 : Blo 1915435 1915891 := bstep (se 1 (by rfl) ⟨1436918, by rfl⟩ : syracuseStep 1915891 = 2873837) B2873837
theorem B4310765 : Blo 1915435 4310765 := bbase (se 3 (by rfl) ⟨808268, by rfl⟩ : syracuseStep 4310765 = 1616537) (by norm_num)
theorem B2873843 : Blo 1915435 2873843 := bstep (se 1 (by rfl) ⟨2155382, by rfl⟩ : syracuseStep 2873843 = 4310765) B4310765
theorem B1915895 : Blo 1915435 1915895 := bstep (se 1 (by rfl) ⟨1436921, by rfl⟩ : syracuseStep 1915895 = 2873843) B2873843
theorem B11652245 : Blo 1915435 11652245 := bbase (se 6 (by rfl) ⟨273099, by rfl⟩ : syracuseStep 11652245 = 546199) (by norm_num)
theorem B7768163 : Blo 1915435 7768163 := bstep (se 1 (by rfl) ⟨5826122, by rfl⟩ : syracuseStep 7768163 = 11652245) B11652245
theorem B5178775 : Blo 1915435 5178775 := bstep (se 1 (by rfl) ⟨3884081, by rfl⟩ : syracuseStep 5178775 = 7768163) B7768163
theorem B6905033 : Blo 1915435 6905033 := bstep (se 2 (by rfl) ⟨2589387, by rfl⟩ : syracuseStep 6905033 = 5178775) B5178775
theorem B4603355 : Blo 1915435 4603355 := bstep (se 1 (by rfl) ⟨3452516, by rfl⟩ : syracuseStep 4603355 = 6905033) B6905033
theorem B3068903 : Blo 1915435 3068903 := bstep (se 1 (by rfl) ⟨2301677, by rfl⟩ : syracuseStep 3068903 = 4603355) B4603355
theorem B2045935 : Blo 1915435 2045935 := bstep (se 1 (by rfl) ⟨1534451, by rfl⟩ : syracuseStep 2045935 = 3068903) B3068903
theorem B2727913 : Blo 1915435 2727913 := bstep (se 2 (by rfl) ⟨1022967, by rfl⟩ : syracuseStep 2727913 = 2045935) B2045935
theorem B3637217 : Blo 1915435 3637217 := bstep (se 2 (by rfl) ⟨1363956, by rfl⟩ : syracuseStep 3637217 = 2727913) B2727913
theorem B2424811 : Blo 1915435 2424811 := bstep (se 1 (by rfl) ⟨1818608, by rfl⟩ : syracuseStep 2424811 = 3637217) B3637217
theorem B3233081 : Blo 1915435 3233081 := bstep (se 2 (by rfl) ⟨1212405, by rfl⟩ : syracuseStep 3233081 = 2424811) B2424811
theorem B2155387 : Blo 1915435 2155387 := bstep (se 1 (by rfl) ⟨1616540, by rfl⟩ : syracuseStep 2155387 = 3233081) B3233081
theorem B2873849 : Blo 1915435 2873849 := bstep (se 2 (by rfl) ⟨1077693, by rfl⟩ : syracuseStep 2873849 = 2155387) B2155387
theorem B1915899 : Blo 1915435 1915899 := bstep (se 1 (by rfl) ⟨1436924, by rfl⟩ : syracuseStep 1915899 = 2873849) B2873849
theorem B17478389 : Blo 1915435 17478389 := bbase (se 5 (by rfl) ⟨819299, by rfl⟩ : syracuseStep 17478389 = 1638599) (by norm_num)
theorem B46609037 : Blo 1915435 46609037 := bstep (se 3 (by rfl) ⟨8739194, by rfl⟩ : syracuseStep 46609037 = 17478389) B17478389
theorem B31072691 : Blo 1915435 31072691 := bstep (se 1 (by rfl) ⟨23304518, by rfl⟩ : syracuseStep 31072691 = 46609037) B46609037
theorem B82860509 : Blo 1915435 82860509 := bstep (se 3 (by rfl) ⟨15536345, by rfl⟩ : syracuseStep 82860509 = 31072691) B31072691
theorem B55240339 : Blo 1915435 55240339 := bstep (se 1 (by rfl) ⟨41430254, by rfl⟩ : syracuseStep 55240339 = 82860509) B82860509
theorem B73653785 : Blo 1915435 73653785 := bstep (se 2 (by rfl) ⟨27620169, by rfl⟩ : syracuseStep 73653785 = 55240339) B55240339
theorem B49102523 : Blo 1915435 49102523 := bstep (se 1 (by rfl) ⟨36826892, by rfl⟩ : syracuseStep 49102523 = 73653785) B73653785
theorem B32735015 : Blo 1915435 32735015 := bstep (se 1 (by rfl) ⟨24551261, by rfl⟩ : syracuseStep 32735015 = 49102523) B49102523
theorem B21823343 : Blo 1915435 21823343 := bstep (se 1 (by rfl) ⟨16367507, by rfl⟩ : syracuseStep 21823343 = 32735015) B32735015
theorem B14548895 : Blo 1915435 14548895 := bstep (se 1 (by rfl) ⟨10911671, by rfl⟩ : syracuseStep 14548895 = 21823343) B21823343
theorem B9699263 : Blo 1915435 9699263 := bstep (se 1 (by rfl) ⟨7274447, by rfl⟩ : syracuseStep 9699263 = 14548895) B14548895
theorem B6466175 : Blo 1915435 6466175 := bstep (se 1 (by rfl) ⟨4849631, by rfl⟩ : syracuseStep 6466175 = 9699263) B9699263
theorem B4310783 : Blo 1915435 4310783 := bstep (se 1 (by rfl) ⟨3233087, by rfl⟩ : syracuseStep 4310783 = 6466175) B6466175
theorem B2873855 : Blo 1915435 2873855 := bstep (se 1 (by rfl) ⟨2155391, by rfl⟩ : syracuseStep 2873855 = 4310783) B4310783
theorem B1915903 : Blo 1915435 1915903 := bstep (se 1 (by rfl) ⟨1436927, by rfl⟩ : syracuseStep 1915903 = 2873855) B2873855
theorem B2873861 : Blo 1915435 2873861 := bbase (se 4 (by rfl) ⟨269424, by rfl⟩ : syracuseStep 2873861 = 538849) (by norm_num)
theorem B1915907 : Blo 1915435 1915907 := bstep (se 1 (by rfl) ⟨1436930, by rfl⟩ : syracuseStep 1915907 = 2873861) B2873861
theorem B3233101 : Blo 1915435 3233101 := bbase (se 3 (by rfl) ⟨606206, by rfl⟩ : syracuseStep 3233101 = 1212413) (by norm_num)
theorem B4310801 : Blo 1915435 4310801 := bstep (se 2 (by rfl) ⟨1616550, by rfl⟩ : syracuseStep 4310801 = 3233101) B3233101
theorem B2873867 : Blo 1915435 2873867 := bstep (se 1 (by rfl) ⟨2155400, by rfl⟩ : syracuseStep 2873867 = 4310801) B4310801
theorem B1915911 : Blo 1915435 1915911 := bstep (se 1 (by rfl) ⟨1436933, by rfl⟩ : syracuseStep 1915911 = 2873867) B2873867
theorem B2155405 : Blo 1915435 2155405 := bbase (se 3 (by rfl) ⟨404138, by rfl⟩ : syracuseStep 2155405 = 808277) (by norm_num)
theorem B2873873 : Blo 1915435 2873873 := bstep (se 2 (by rfl) ⟨1077702, by rfl⟩ : syracuseStep 2873873 = 2155405) B2155405
theorem B1915915 : Blo 1915435 1915915 := bstep (se 1 (by rfl) ⟨1436936, by rfl⟩ : syracuseStep 1915915 = 2873873) B2873873
theorem B6466229 : Blo 1915435 6466229 := bbase (se 5 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 6466229 = 606209) (by norm_num)
theorem B4310819 : Blo 1915435 4310819 := bstep (se 1 (by rfl) ⟨3233114, by rfl⟩ : syracuseStep 4310819 = 6466229) B6466229
theorem B2873879 : Blo 1915435 2873879 := bstep (se 1 (by rfl) ⟨2155409, by rfl⟩ : syracuseStep 2873879 = 4310819) B4310819
theorem B1915919 : Blo 1915435 1915919 := bstep (se 1 (by rfl) ⟨1436939, by rfl⟩ : syracuseStep 1915919 = 2873879) B2873879
theorem B2873885 : Blo 1915435 2873885 := bbase (se 3 (by rfl) ⟨538853, by rfl⟩ : syracuseStep 2873885 = 1077707) (by norm_num)
theorem B1915923 : Blo 1915435 1915923 := bstep (se 1 (by rfl) ⟨1436942, by rfl⟩ : syracuseStep 1915923 = 2873885) B2873885
theorem B4310837 : Blo 1915435 4310837 := bbase (se 5 (by rfl) ⟨202070, by rfl⟩ : syracuseStep 4310837 = 404141) (by norm_num)
theorem B2873891 : Blo 1915435 2873891 := bstep (se 1 (by rfl) ⟨2155418, by rfl⟩ : syracuseStep 2873891 = 4310837) B4310837
theorem B1915927 : Blo 1915435 1915927 := bstep (se 1 (by rfl) ⟨1436945, by rfl⟩ : syracuseStep 1915927 = 2873891) B2873891
theorem B3452573 : Blo 1915435 3452573 := bbase (se 3 (by rfl) ⟨647357, by rfl⟩ : syracuseStep 3452573 = 1294715) (by norm_num)
theorem B2301715 : Blo 1915435 2301715 := bstep (se 1 (by rfl) ⟨1726286, by rfl⟩ : syracuseStep 2301715 = 3452573) B3452573
theorem B12275813 : Blo 1915435 12275813 := bstep (se 4 (by rfl) ⟨1150857, by rfl⟩ : syracuseStep 12275813 = 2301715) B2301715
theorem B8183875 : Blo 1915435 8183875 := bstep (se 1 (by rfl) ⟨6137906, by rfl⟩ : syracuseStep 8183875 = 12275813) B12275813
theorem B10911833 : Blo 1915435 10911833 := bstep (se 2 (by rfl) ⟨4091937, by rfl⟩ : syracuseStep 10911833 = 8183875) B8183875
theorem B7274555 : Blo 1915435 7274555 := bstep (se 1 (by rfl) ⟨5455916, by rfl⟩ : syracuseStep 7274555 = 10911833) B10911833
theorem B4849703 : Blo 1915435 4849703 := bstep (se 1 (by rfl) ⟨3637277, by rfl⟩ : syracuseStep 4849703 = 7274555) B7274555
theorem B3233135 : Blo 1915435 3233135 := bstep (se 1 (by rfl) ⟨2424851, by rfl⟩ : syracuseStep 3233135 = 4849703) B4849703
theorem B2155423 : Blo 1915435 2155423 := bstep (se 1 (by rfl) ⟨1616567, by rfl⟩ : syracuseStep 2155423 = 3233135) B3233135
theorem B2873897 : Blo 1915435 2873897 := bstep (se 2 (by rfl) ⟨1077711, by rfl⟩ : syracuseStep 2873897 = 2155423) B2155423
theorem B1915931 : Blo 1915435 1915931 := bstep (se 1 (by rfl) ⟨1436948, by rfl⟩ : syracuseStep 1915931 = 2873897) B2873897
theorem B31497173 : Blo 1915435 31497173 := bbase (se 7 (by rfl) ⟨369107, by rfl⟩ : syracuseStep 31497173 = 738215) (by norm_num)
theorem B20998115 : Blo 1915435 20998115 := bstep (se 1 (by rfl) ⟨15748586, by rfl⟩ : syracuseStep 20998115 = 31497173) B31497173
theorem B13998743 : Blo 1915435 13998743 := bstep (se 1 (by rfl) ⟨10499057, by rfl⟩ : syracuseStep 13998743 = 20998115) B20998115
theorem B9332495 : Blo 1915435 9332495 := bstep (se 1 (by rfl) ⟨6999371, by rfl⟩ : syracuseStep 9332495 = 13998743) B13998743
theorem B6221663 : Blo 1915435 6221663 := bstep (se 1 (by rfl) ⟨4666247, by rfl⟩ : syracuseStep 6221663 = 9332495) B9332495
theorem B4147775 : Blo 1915435 4147775 := bstep (se 1 (by rfl) ⟨3110831, by rfl⟩ : syracuseStep 4147775 = 6221663) B6221663
theorem B2765183 : Blo 1915435 2765183 := bstep (se 1 (by rfl) ⟨2073887, by rfl⟩ : syracuseStep 2765183 = 4147775) B4147775
theorem B29495285 : Blo 1915435 29495285 := bstep (se 5 (by rfl) ⟨1382591, by rfl⟩ : syracuseStep 29495285 = 2765183) B2765183
theorem B19663523 : Blo 1915435 19663523 := bstep (se 1 (by rfl) ⟨14747642, by rfl⟩ : syracuseStep 19663523 = 29495285) B29495285
theorem B13109015 : Blo 1915435 13109015 := bstep (se 1 (by rfl) ⟨9831761, by rfl⟩ : syracuseStep 13109015 = 19663523) B19663523
theorem B8739343 : Blo 1915435 8739343 := bstep (se 1 (by rfl) ⟨6554507, by rfl⟩ : syracuseStep 8739343 = 13109015) B13109015
theorem B11652457 : Blo 1915435 11652457 := bstep (se 2 (by rfl) ⟨4369671, by rfl⟩ : syracuseStep 11652457 = 8739343) B8739343
theorem B15536609 : Blo 1915435 15536609 := bstep (se 2 (by rfl) ⟨5826228, by rfl⟩ : syracuseStep 15536609 = 11652457) B11652457
theorem B10357739 : Blo 1915435 10357739 := bstep (se 1 (by rfl) ⟨7768304, by rfl⟩ : syracuseStep 10357739 = 15536609) B15536609
theorem B6905159 : Blo 1915435 6905159 := bstep (se 1 (by rfl) ⟨5178869, by rfl⟩ : syracuseStep 6905159 = 10357739) B10357739
theorem B4603439 : Blo 1915435 4603439 := bstep (se 1 (by rfl) ⟨3452579, by rfl⟩ : syracuseStep 4603439 = 6905159) B6905159
theorem B12275837 : Blo 1915435 12275837 := bstep (se 3 (by rfl) ⟨2301719, by rfl⟩ : syracuseStep 12275837 = 4603439) B4603439
theorem B8183891 : Blo 1915435 8183891 := bstep (se 1 (by rfl) ⟨6137918, by rfl⟩ : syracuseStep 8183891 = 12275837) B12275837
theorem B5455927 : Blo 1915435 5455927 := bstep (se 1 (by rfl) ⟨4091945, by rfl⟩ : syracuseStep 5455927 = 8183891) B8183891
theorem B7274569 : Blo 1915435 7274569 := bstep (se 2 (by rfl) ⟨2727963, by rfl⟩ : syracuseStep 7274569 = 5455927) B5455927
theorem B9699425 : Blo 1915435 9699425 := bstep (se 2 (by rfl) ⟨3637284, by rfl⟩ : syracuseStep 9699425 = 7274569) B7274569
theorem B6466283 : Blo 1915435 6466283 := bstep (se 1 (by rfl) ⟨4849712, by rfl⟩ : syracuseStep 6466283 = 9699425) B9699425
theorem B4310855 : Blo 1915435 4310855 := bstep (se 1 (by rfl) ⟨3233141, by rfl⟩ : syracuseStep 4310855 = 6466283) B6466283
theorem B2873903 : Blo 1915435 2873903 := bstep (se 1 (by rfl) ⟨2155427, by rfl⟩ : syracuseStep 2873903 = 4310855) B4310855
theorem B1915935 : Blo 1915435 1915935 := bstep (se 1 (by rfl) ⟨1436951, by rfl⟩ : syracuseStep 1915935 = 2873903) B2873903
theorem B2873909 : Blo 1915435 2873909 := bbase (se 5 (by rfl) ⟨134714, by rfl⟩ : syracuseStep 2873909 = 269429) (by norm_num)
theorem B1915939 : Blo 1915435 1915939 := bstep (se 1 (by rfl) ⟨1436954, by rfl⟩ : syracuseStep 1915939 = 2873909) B2873909
theorem B4849733 : Blo 1915435 4849733 := bbase (se 4 (by rfl) ⟨454662, by rfl⟩ : syracuseStep 4849733 = 909325) (by norm_num)
theorem B3233155 : Blo 1915435 3233155 := bstep (se 1 (by rfl) ⟨2424866, by rfl⟩ : syracuseStep 3233155 = 4849733) B4849733
theorem B4310873 : Blo 1915435 4310873 := bstep (se 2 (by rfl) ⟨1616577, by rfl⟩ : syracuseStep 4310873 = 3233155) B3233155
theorem B2873915 : Blo 1915435 2873915 := bstep (se 1 (by rfl) ⟨2155436, by rfl⟩ : syracuseStep 2873915 = 4310873) B4310873
theorem B1915943 : Blo 1915435 1915943 := bstep (se 1 (by rfl) ⟨1436957, by rfl⟩ : syracuseStep 1915943 = 2873915) B2873915
theorem B2155441 : Blo 1915435 2155441 := bbase (se 2 (by rfl) ⟨808290, by rfl⟩ : syracuseStep 2155441 = 1616581) (by norm_num)
theorem B2873921 : Blo 1915435 2873921 := bstep (se 2 (by rfl) ⟨1077720, by rfl⟩ : syracuseStep 2873921 = 2155441) B2155441
theorem B1915947 : Blo 1915435 1915947 := bstep (se 1 (by rfl) ⟨1436960, by rfl⟩ : syracuseStep 1915947 = 2873921) B2873921
theorem B5455973 : Blo 1915435 5455973 := bbase (se 4 (by rfl) ⟨511497, by rfl⟩ : syracuseStep 5455973 = 1022995) (by norm_num)
theorem B3637315 : Blo 1915435 3637315 := bstep (se 1 (by rfl) ⟨2727986, by rfl⟩ : syracuseStep 3637315 = 5455973) B5455973
theorem B4849753 : Blo 1915435 4849753 := bstep (se 2 (by rfl) ⟨1818657, by rfl⟩ : syracuseStep 4849753 = 3637315) B3637315
theorem B6466337 : Blo 1915435 6466337 := bstep (se 2 (by rfl) ⟨2424876, by rfl⟩ : syracuseStep 6466337 = 4849753) B4849753
theorem B4310891 : Blo 1915435 4310891 := bstep (se 1 (by rfl) ⟨3233168, by rfl⟩ : syracuseStep 4310891 = 6466337) B6466337
theorem B2873927 : Blo 1915435 2873927 := bstep (se 1 (by rfl) ⟨2155445, by rfl⟩ : syracuseStep 2873927 = 4310891) B4310891
theorem B1915951 : Blo 1915435 1915951 := bstep (se 1 (by rfl) ⟨1436963, by rfl⟩ : syracuseStep 1915951 = 2873927) B2873927
theorem B2873933 : Blo 1915435 2873933 := bbase (se 3 (by rfl) ⟨538862, by rfl⟩ : syracuseStep 2873933 = 1077725) (by norm_num)
theorem B1915955 : Blo 1915435 1915955 := bstep (se 1 (by rfl) ⟨1436966, by rfl⟩ : syracuseStep 1915955 = 2873933) B2873933
theorem B4310909 : Blo 1915435 4310909 := bbase (se 3 (by rfl) ⟨808295, by rfl⟩ : syracuseStep 4310909 = 1616591) (by norm_num)
theorem B2873939 : Blo 1915435 2873939 := bstep (se 1 (by rfl) ⟨2155454, by rfl⟩ : syracuseStep 2873939 = 4310909) B4310909
theorem B1915959 : Blo 1915435 1915959 := bstep (se 1 (by rfl) ⟨1436969, by rfl⟩ : syracuseStep 1915959 = 2873939) B2873939
theorem B3233189 : Blo 1915435 3233189 := bbase (se 4 (by rfl) ⟨303111, by rfl⟩ : syracuseStep 3233189 = 606223) (by norm_num)
theorem B2155459 : Blo 1915435 2155459 := bstep (se 1 (by rfl) ⟨1616594, by rfl⟩ : syracuseStep 2155459 = 3233189) B3233189
theorem B2873945 : Blo 1915435 2873945 := bstep (se 2 (by rfl) ⟨1077729, by rfl⟩ : syracuseStep 2873945 = 2155459) B2155459
theorem B1915963 : Blo 1915435 1915963 := bstep (se 1 (by rfl) ⟨1436972, by rfl⟩ : syracuseStep 1915963 = 2873945) B2873945
theorem B4603517 : Blo 1915435 4603517 := bbase (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) (by norm_num)
theorem B3069011 : Blo 1915435 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B2046007 : Blo 1915435 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B2728009 : Blo 1915435 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B14549381 : Blo 1915435 14549381 := bstep (se 4 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 14549381 = 2728009) B2728009
theorem B9699587 : Blo 1915435 9699587 := bstep (se 1 (by rfl) ⟨7274690, by rfl⟩ : syracuseStep 9699587 = 14549381) B14549381
theorem B6466391 : Blo 1915435 6466391 := bstep (se 1 (by rfl) ⟨4849793, by rfl⟩ : syracuseStep 6466391 = 9699587) B9699587
theorem B4310927 : Blo 1915435 4310927 := bstep (se 1 (by rfl) ⟨3233195, by rfl⟩ : syracuseStep 4310927 = 6466391) B6466391
theorem B2873951 : Blo 1915435 2873951 := bstep (se 1 (by rfl) ⟨2155463, by rfl⟩ : syracuseStep 2873951 = 4310927) B4310927
theorem B1915967 : Blo 1915435 1915967 := bstep (se 1 (by rfl) ⟨1436975, by rfl⟩ : syracuseStep 1915967 = 2873951) B2873951
theorem B2873957 : Blo 1915435 2873957 := bbase (se 4 (by rfl) ⟨269433, by rfl⟩ : syracuseStep 2873957 = 538867) (by norm_num)
theorem B1915971 : Blo 1915435 1915971 := bstep (se 1 (by rfl) ⟨1436978, by rfl⟩ : syracuseStep 1915971 = 2873957) B2873957
theorem B2728021 : Blo 1915435 2728021 := bbase (se 8 (by rfl) ⟨15984, by rfl⟩ : syracuseStep 2728021 = 31969) (by norm_num)
theorem B3637361 : Blo 1915435 3637361 := bstep (se 2 (by rfl) ⟨1364010, by rfl⟩ : syracuseStep 3637361 = 2728021) B2728021
theorem B2424907 : Blo 1915435 2424907 := bstep (se 1 (by rfl) ⟨1818680, by rfl⟩ : syracuseStep 2424907 = 3637361) B3637361
theorem B3233209 : Blo 1915435 3233209 := bstep (se 2 (by rfl) ⟨1212453, by rfl⟩ : syracuseStep 3233209 = 2424907) B2424907
theorem B4310945 : Blo 1915435 4310945 := bstep (se 2 (by rfl) ⟨1616604, by rfl⟩ : syracuseStep 4310945 = 3233209) B3233209
theorem B2873963 : Blo 1915435 2873963 := bstep (se 1 (by rfl) ⟨2155472, by rfl⟩ : syracuseStep 2873963 = 4310945) B4310945
theorem B1915975 : Blo 1915435 1915975 := bstep (se 1 (by rfl) ⟨1436981, by rfl⟩ : syracuseStep 1915975 = 2873963) B2873963
theorem B2155477 : Blo 1915435 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B2873969 : Blo 1915435 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B1915979 : Blo 1915435 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B2424917 : Blo 1915435 2424917 := bbase (se 8 (by rfl) ⟨14208, by rfl⟩ : syracuseStep 2424917 = 28417) (by norm_num)
theorem B6466445 : Blo 1915435 6466445 := bstep (se 3 (by rfl) ⟨1212458, by rfl⟩ : syracuseStep 6466445 = 2424917) B2424917
theorem B4310963 : Blo 1915435 4310963 := bstep (se 1 (by rfl) ⟨3233222, by rfl⟩ : syracuseStep 4310963 = 6466445) B6466445
theorem B2873975 : Blo 1915435 2873975 := bstep (se 1 (by rfl) ⟨2155481, by rfl⟩ : syracuseStep 2873975 = 4310963) B4310963
theorem B1915983 : Blo 1915435 1915983 := bstep (se 1 (by rfl) ⟨1436987, by rfl⟩ : syracuseStep 1915983 = 2873975) B2873975
theorem B2873981 : Blo 1915435 2873981 := bbase (se 3 (by rfl) ⟨538871, by rfl⟩ : syracuseStep 2873981 = 1077743) (by norm_num)
theorem B1915987 : Blo 1915435 1915987 := bstep (se 1 (by rfl) ⟨1436990, by rfl⟩ : syracuseStep 1915987 = 2873981) B2873981
theorem B4310981 : Blo 1915435 4310981 := bbase (se 4 (by rfl) ⟨404154, by rfl⟩ : syracuseStep 4310981 = 808309) (by norm_num)
theorem B2873987 : Blo 1915435 2873987 := bstep (se 1 (by rfl) ⟨2155490, by rfl⟩ : syracuseStep 2873987 = 4310981) B4310981
theorem B1915991 : Blo 1915435 1915991 := bstep (se 1 (by rfl) ⟨1436993, by rfl⟩ : syracuseStep 1915991 = 2873987) B2873987
theorem B8184149 : Blo 1915435 8184149 := bbase (se 10 (by rfl) ⟨11988, by rfl⟩ : syracuseStep 8184149 = 23977) (by norm_num)
theorem B5456099 : Blo 1915435 5456099 := bstep (se 1 (by rfl) ⟨4092074, by rfl⟩ : syracuseStep 5456099 = 8184149) B8184149
theorem B3637399 : Blo 1915435 3637399 := bstep (se 1 (by rfl) ⟨2728049, by rfl⟩ : syracuseStep 3637399 = 5456099) B5456099
theorem B4849865 : Blo 1915435 4849865 := bstep (se 2 (by rfl) ⟨1818699, by rfl⟩ : syracuseStep 4849865 = 3637399) B3637399
theorem B3233243 : Blo 1915435 3233243 := bstep (se 1 (by rfl) ⟨2424932, by rfl⟩ : syracuseStep 3233243 = 4849865) B4849865
theorem B2155495 : Blo 1915435 2155495 := bstep (se 1 (by rfl) ⟨1616621, by rfl⟩ : syracuseStep 2155495 = 3233243) B3233243
theorem B2873993 : Blo 1915435 2873993 := bstep (se 2 (by rfl) ⟨1077747, by rfl⟩ : syracuseStep 2873993 = 2155495) B2155495
theorem B1915995 : Blo 1915435 1915995 := bstep (se 1 (by rfl) ⟨1436996, by rfl⟩ : syracuseStep 1915995 = 2873993) B2873993
theorem B9699749 : Blo 1915435 9699749 := bbase (se 4 (by rfl) ⟨909351, by rfl⟩ : syracuseStep 9699749 = 1818703) (by norm_num)
theorem B6466499 : Blo 1915435 6466499 := bstep (se 1 (by rfl) ⟨4849874, by rfl⟩ : syracuseStep 6466499 = 9699749) B9699749
theorem B4310999 : Blo 1915435 4310999 := bstep (se 1 (by rfl) ⟨3233249, by rfl⟩ : syracuseStep 4310999 = 6466499) B6466499
theorem B2873999 : Blo 1915435 2873999 := bstep (se 1 (by rfl) ⟨2155499, by rfl⟩ : syracuseStep 2873999 = 4310999) B4310999
theorem B1915999 : Blo 1915435 1915999 := bstep (se 1 (by rfl) ⟨1436999, by rfl⟩ : syracuseStep 1915999 = 2873999) B2873999
theorem B2874005 : Blo 1915435 2874005 := bbase (se 6 (by rfl) ⟨67359, by rfl⟩ : syracuseStep 2874005 = 134719) (by norm_num)
theorem B1916003 : Blo 1915435 1916003 := bstep (se 1 (by rfl) ⟨1437002, by rfl⟩ : syracuseStep 1916003 = 2874005) B2874005
theorem B13810837 : Blo 1915435 13810837 := bbase (se 6 (by rfl) ⟨323691, by rfl⟩ : syracuseStep 13810837 = 647383) (by norm_num)
theorem B18414449 : Blo 1915435 18414449 := bstep (se 2 (by rfl) ⟨6905418, by rfl⟩ : syracuseStep 18414449 = 13810837) B13810837
theorem B12276299 : Blo 1915435 12276299 := bstep (se 1 (by rfl) ⟨9207224, by rfl⟩ : syracuseStep 12276299 = 18414449) B18414449
theorem B8184199 : Blo 1915435 8184199 := bstep (se 1 (by rfl) ⟨6138149, by rfl⟩ : syracuseStep 8184199 = 12276299) B12276299
theorem B10912265 : Blo 1915435 10912265 := bstep (se 2 (by rfl) ⟨4092099, by rfl⟩ : syracuseStep 10912265 = 8184199) B8184199
theorem B7274843 : Blo 1915435 7274843 := bstep (se 1 (by rfl) ⟨5456132, by rfl⟩ : syracuseStep 7274843 = 10912265) B10912265
theorem B4849895 : Blo 1915435 4849895 := bstep (se 1 (by rfl) ⟨3637421, by rfl⟩ : syracuseStep 4849895 = 7274843) B7274843
theorem B3233263 : Blo 1915435 3233263 := bstep (se 1 (by rfl) ⟨2424947, by rfl⟩ : syracuseStep 3233263 = 4849895) B4849895
theorem B4311017 : Blo 1915435 4311017 := bstep (se 2 (by rfl) ⟨1616631, by rfl⟩ : syracuseStep 4311017 = 3233263) B3233263
theorem B2874011 : Blo 1915435 2874011 := bstep (se 1 (by rfl) ⟨2155508, by rfl⟩ : syracuseStep 2874011 = 4311017) B4311017
theorem B1916007 : Blo 1915435 1916007 := bstep (se 1 (by rfl) ⟨1437005, by rfl⟩ : syracuseStep 1916007 = 2874011) B2874011
theorem B2155513 : Blo 1915435 2155513 := bbase (se 2 (by rfl) ⟨808317, by rfl⟩ : syracuseStep 2155513 = 1616635) (by norm_num)
theorem B2874017 : Blo 1915435 2874017 := bstep (se 2 (by rfl) ⟨1077756, by rfl⟩ : syracuseStep 2874017 = 2155513) B2155513
theorem B1916011 : Blo 1915435 1916011 := bstep (se 1 (by rfl) ⟨1437008, by rfl⟩ : syracuseStep 1916011 = 2874017) B2874017
theorem B6644213 : Blo 1915435 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B4429475 : Blo 1915435 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B2952983 : Blo 1915435 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B7874621 : Blo 1915435 7874621 := bstep (se 3 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 7874621 = 2952983) B2952983
theorem B5249747 : Blo 1915435 5249747 := bstep (se 1 (by rfl) ⟨3937310, by rfl⟩ : syracuseStep 5249747 = 7874621) B7874621
theorem B3499831 : Blo 1915435 3499831 := bstep (se 1 (by rfl) ⟨2624873, by rfl⟩ : syracuseStep 3499831 = 5249747) B5249747
theorem B18665765 : Blo 1915435 18665765 := bstep (se 4 (by rfl) ⟨1749915, by rfl⟩ : syracuseStep 18665765 = 3499831) B3499831
theorem B12443843 : Blo 1915435 12443843 := bstep (se 1 (by rfl) ⟨9332882, by rfl⟩ : syracuseStep 12443843 = 18665765) B18665765
theorem B8295895 : Blo 1915435 8295895 := bstep (se 1 (by rfl) ⟨6221921, by rfl⟩ : syracuseStep 8295895 = 12443843) B12443843
theorem B11061193 : Blo 1915435 11061193 := bstep (se 2 (by rfl) ⟨4147947, by rfl⟩ : syracuseStep 11061193 = 8295895) B8295895
theorem B14748257 : Blo 1915435 14748257 := bstep (se 2 (by rfl) ⟨5530596, by rfl⟩ : syracuseStep 14748257 = 11061193) B11061193
theorem B39328685 : Blo 1915435 39328685 := bstep (se 3 (by rfl) ⟨7374128, by rfl⟩ : syracuseStep 39328685 = 14748257) B14748257
theorem B26219123 : Blo 1915435 26219123 := bstep (se 1 (by rfl) ⟨19664342, by rfl⟩ : syracuseStep 26219123 = 39328685) B39328685
theorem B17479415 : Blo 1915435 17479415 := bstep (se 1 (by rfl) ⟨13109561, by rfl⟩ : syracuseStep 17479415 = 26219123) B26219123
theorem B46611773 : Blo 1915435 46611773 := bstep (se 3 (by rfl) ⟨8739707, by rfl⟩ : syracuseStep 46611773 = 17479415) B17479415
theorem B31074515 : Blo 1915435 31074515 := bstep (se 1 (by rfl) ⟨23305886, by rfl⟩ : syracuseStep 31074515 = 46611773) B46611773
theorem B20716343 : Blo 1915435 20716343 := bstep (se 1 (by rfl) ⟨15537257, by rfl⟩ : syracuseStep 20716343 = 31074515) B31074515
theorem B13810895 : Blo 1915435 13810895 := bstep (se 1 (by rfl) ⟨10358171, by rfl⟩ : syracuseStep 13810895 = 20716343) B20716343
theorem B9207263 : Blo 1915435 9207263 := bstep (se 1 (by rfl) ⟨6905447, by rfl⟩ : syracuseStep 9207263 = 13810895) B13810895
theorem B6138175 : Blo 1915435 6138175 := bstep (se 1 (by rfl) ⟨4603631, by rfl⟩ : syracuseStep 6138175 = 9207263) B9207263
theorem B8184233 : Blo 1915435 8184233 := bstep (se 2 (by rfl) ⟨3069087, by rfl⟩ : syracuseStep 8184233 = 6138175) B6138175
theorem B5456155 : Blo 1915435 5456155 := bstep (se 1 (by rfl) ⟨4092116, by rfl⟩ : syracuseStep 5456155 = 8184233) B8184233
theorem B7274873 : Blo 1915435 7274873 := bstep (se 2 (by rfl) ⟨2728077, by rfl⟩ : syracuseStep 7274873 = 5456155) B5456155
theorem B4849915 : Blo 1915435 4849915 := bstep (se 1 (by rfl) ⟨3637436, by rfl⟩ : syracuseStep 4849915 = 7274873) B7274873
theorem B6466553 : Blo 1915435 6466553 := bstep (se 2 (by rfl) ⟨2424957, by rfl⟩ : syracuseStep 6466553 = 4849915) B4849915
theorem B4311035 : Blo 1915435 4311035 := bstep (se 1 (by rfl) ⟨3233276, by rfl⟩ : syracuseStep 4311035 = 6466553) B6466553
theorem B2874023 : Blo 1915435 2874023 := bstep (se 1 (by rfl) ⟨2155517, by rfl⟩ : syracuseStep 2874023 = 4311035) B4311035
theorem B1916015 : Blo 1915435 1916015 := bstep (se 1 (by rfl) ⟨1437011, by rfl⟩ : syracuseStep 1916015 = 2874023) B2874023
theorem B2874029 : Blo 1915435 2874029 := bbase (se 3 (by rfl) ⟨538880, by rfl⟩ : syracuseStep 2874029 = 1077761) (by norm_num)
theorem B1916019 : Blo 1915435 1916019 := bstep (se 1 (by rfl) ⟨1437014, by rfl⟩ : syracuseStep 1916019 = 2874029) B2874029
theorem B4311053 : Blo 1915435 4311053 := bbase (se 3 (by rfl) ⟨808322, by rfl⟩ : syracuseStep 4311053 = 1616645) (by norm_num)
theorem B2874035 : Blo 1915435 2874035 := bstep (se 1 (by rfl) ⟨2155526, by rfl⟩ : syracuseStep 2874035 = 4311053) B4311053
theorem B1916023 : Blo 1915435 1916023 := bstep (se 1 (by rfl) ⟨1437017, by rfl⟩ : syracuseStep 1916023 = 2874035) B2874035
theorem B2424973 : Blo 1915435 2424973 := bbase (se 3 (by rfl) ⟨454682, by rfl⟩ : syracuseStep 2424973 = 909365) (by norm_num)
theorem B3233297 : Blo 1915435 3233297 := bstep (se 2 (by rfl) ⟨1212486, by rfl⟩ : syracuseStep 3233297 = 2424973) B2424973
theorem B2155531 : Blo 1915435 2155531 := bstep (se 1 (by rfl) ⟨1616648, by rfl⟩ : syracuseStep 2155531 = 3233297) B3233297
theorem B2874041 : Blo 1915435 2874041 := bstep (se 2 (by rfl) ⟨1077765, by rfl⟩ : syracuseStep 2874041 = 2155531) B2155531
theorem B1916027 : Blo 1915435 1916027 := bstep (se 1 (by rfl) ⟨1437020, by rfl⟩ : syracuseStep 1916027 = 2874041) B2874041
theorem B18414677 : Blo 1915435 18414677 := bbase (se 8 (by rfl) ⟨107898, by rfl⟩ : syracuseStep 18414677 = 215797) (by norm_num)
theorem B12276451 : Blo 1915435 12276451 := bstep (se 1 (by rfl) ⟨9207338, by rfl⟩ : syracuseStep 12276451 = 18414677) B18414677
theorem B16368601 : Blo 1915435 16368601 := bstep (se 2 (by rfl) ⟨6138225, by rfl⟩ : syracuseStep 16368601 = 12276451) B12276451
theorem B21824801 : Blo 1915435 21824801 := bstep (se 2 (by rfl) ⟨8184300, by rfl⟩ : syracuseStep 21824801 = 16368601) B16368601
theorem B14549867 : Blo 1915435 14549867 := bstep (se 1 (by rfl) ⟨10912400, by rfl⟩ : syracuseStep 14549867 = 21824801) B21824801
theorem B9699911 : Blo 1915435 9699911 := bstep (se 1 (by rfl) ⟨7274933, by rfl⟩ : syracuseStep 9699911 = 14549867) B14549867
theorem B6466607 : Blo 1915435 6466607 := bstep (se 1 (by rfl) ⟨4849955, by rfl⟩ : syracuseStep 6466607 = 9699911) B9699911
theorem B4311071 : Blo 1915435 4311071 := bstep (se 1 (by rfl) ⟨3233303, by rfl⟩ : syracuseStep 4311071 = 6466607) B6466607
theorem B2874047 : Blo 1915435 2874047 := bstep (se 1 (by rfl) ⟨2155535, by rfl⟩ : syracuseStep 2874047 = 4311071) B4311071
theorem B1916031 : Blo 1915435 1916031 := bstep (se 1 (by rfl) ⟨1437023, by rfl⟩ : syracuseStep 1916031 = 2874047) B2874047
theorem B2874053 : Blo 1915435 2874053 := bbase (se 4 (by rfl) ⟨269442, by rfl⟩ : syracuseStep 2874053 = 538885) (by norm_num)
theorem B1916035 : Blo 1915435 1916035 := bstep (se 1 (by rfl) ⟨1437026, by rfl⟩ : syracuseStep 1916035 = 2874053) B2874053
theorem B3233317 : Blo 1915435 3233317 := bbase (se 4 (by rfl) ⟨303123, by rfl⟩ : syracuseStep 3233317 = 606247) (by norm_num)
theorem B4311089 : Blo 1915435 4311089 := bstep (se 2 (by rfl) ⟨1616658, by rfl⟩ : syracuseStep 4311089 = 3233317) B3233317
theorem B2874059 : Blo 1915435 2874059 := bstep (se 1 (by rfl) ⟨2155544, by rfl⟩ : syracuseStep 2874059 = 4311089) B4311089
theorem B1916039 : Blo 1915435 1916039 := bstep (se 1 (by rfl) ⟨1437029, by rfl⟩ : syracuseStep 1916039 = 2874059) B2874059
theorem B2155549 : Blo 1915435 2155549 := bbase (se 3 (by rfl) ⟨404165, by rfl⟩ : syracuseStep 2155549 = 808331) (by norm_num)
theorem B2874065 : Blo 1915435 2874065 := bstep (se 2 (by rfl) ⟨1077774, by rfl⟩ : syracuseStep 2874065 = 2155549) B2155549
theorem B1916043 : Blo 1915435 1916043 := bstep (se 1 (by rfl) ⟨1437032, by rfl⟩ : syracuseStep 1916043 = 2874065) B2874065
theorem B6466661 : Blo 1915435 6466661 := bbase (se 4 (by rfl) ⟨606249, by rfl⟩ : syracuseStep 6466661 = 1212499) (by norm_num)
theorem B4311107 : Blo 1915435 4311107 := bstep (se 1 (by rfl) ⟨3233330, by rfl⟩ : syracuseStep 4311107 = 6466661) B6466661
theorem B2874071 : Blo 1915435 2874071 := bstep (se 1 (by rfl) ⟨2155553, by rfl⟩ : syracuseStep 2874071 = 4311107) B4311107
theorem B1916047 : Blo 1915435 1916047 := bstep (se 1 (by rfl) ⟨1437035, by rfl⟩ : syracuseStep 1916047 = 2874071) B2874071
theorem B2874077 : Blo 1915435 2874077 := bbase (se 3 (by rfl) ⟨538889, by rfl⟩ : syracuseStep 2874077 = 1077779) (by norm_num)
theorem B1916051 : Blo 1915435 1916051 := bstep (se 1 (by rfl) ⟨1437038, by rfl⟩ : syracuseStep 1916051 = 2874077) B2874077
theorem B4311125 : Blo 1915435 4311125 := bbase (se 8 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 4311125 = 50521) (by norm_num)
theorem B2874083 : Blo 1915435 2874083 := bstep (se 1 (by rfl) ⟨2155562, by rfl⟩ : syracuseStep 2874083 = 4311125) B4311125
theorem B1916055 : Blo 1915435 1916055 := bstep (se 1 (by rfl) ⟨1437041, by rfl⟩ : syracuseStep 1916055 = 2874083) B2874083
theorem B2301869 : Blo 1915435 2301869 := bbase (se 3 (by rfl) ⟨431600, by rfl⟩ : syracuseStep 2301869 = 863201) (by norm_num)
theorem B6138317 : Blo 1915435 6138317 := bstep (se 3 (by rfl) ⟨1150934, by rfl⟩ : syracuseStep 6138317 = 2301869) B2301869
theorem B4092211 : Blo 1915435 4092211 := bstep (se 1 (by rfl) ⟨3069158, by rfl⟩ : syracuseStep 4092211 = 6138317) B6138317
theorem B5456281 : Blo 1915435 5456281 := bstep (se 2 (by rfl) ⟨2046105, by rfl⟩ : syracuseStep 5456281 = 4092211) B4092211
theorem B7275041 : Blo 1915435 7275041 := bstep (se 2 (by rfl) ⟨2728140, by rfl⟩ : syracuseStep 7275041 = 5456281) B5456281
theorem B4850027 : Blo 1915435 4850027 := bstep (se 1 (by rfl) ⟨3637520, by rfl⟩ : syracuseStep 4850027 = 7275041) B7275041
theorem B3233351 : Blo 1915435 3233351 := bstep (se 1 (by rfl) ⟨2425013, by rfl⟩ : syracuseStep 3233351 = 4850027) B4850027
theorem B2155567 : Blo 1915435 2155567 := bstep (se 1 (by rfl) ⟨1616675, by rfl⟩ : syracuseStep 2155567 = 3233351) B3233351
theorem B2874089 : Blo 1915435 2874089 := bstep (se 2 (by rfl) ⟨1077783, by rfl⟩ : syracuseStep 2874089 = 2155567) B2155567
theorem B1916059 : Blo 1915435 1916059 := bstep (se 1 (by rfl) ⟨1437044, by rfl⟩ : syracuseStep 1916059 = 2874089) B2874089
theorem B34959701 : Blo 1915435 34959701 := bbase (se 10 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 34959701 = 102421) (by norm_num)
theorem B23306467 : Blo 1915435 23306467 := bstep (se 1 (by rfl) ⟨17479850, by rfl⟩ : syracuseStep 23306467 = 34959701) B34959701
theorem B31075289 : Blo 1915435 31075289 := bstep (se 2 (by rfl) ⟨11653233, by rfl⟩ : syracuseStep 31075289 = 23306467) B23306467
theorem B20716859 : Blo 1915435 20716859 := bstep (se 1 (by rfl) ⟨15537644, by rfl⟩ : syracuseStep 20716859 = 31075289) B31075289
theorem B13811239 : Blo 1915435 13811239 := bstep (se 1 (by rfl) ⟨10358429, by rfl⟩ : syracuseStep 13811239 = 20716859) B20716859
theorem B18414985 : Blo 1915435 18414985 := bstep (se 2 (by rfl) ⟨6905619, by rfl⟩ : syracuseStep 18414985 = 13811239) B13811239
theorem B24553313 : Blo 1915435 24553313 := bstep (se 2 (by rfl) ⟨9207492, by rfl⟩ : syracuseStep 24553313 = 18414985) B18414985
theorem B16368875 : Blo 1915435 16368875 := bstep (se 1 (by rfl) ⟨12276656, by rfl⟩ : syracuseStep 16368875 = 24553313) B24553313
theorem B10912583 : Blo 1915435 10912583 := bstep (se 1 (by rfl) ⟨8184437, by rfl⟩ : syracuseStep 10912583 = 16368875) B16368875
theorem B7275055 : Blo 1915435 7275055 := bstep (se 1 (by rfl) ⟨5456291, by rfl⟩ : syracuseStep 7275055 = 10912583) B10912583
theorem B9700073 : Blo 1915435 9700073 := bstep (se 2 (by rfl) ⟨3637527, by rfl⟩ : syracuseStep 9700073 = 7275055) B7275055
theorem B6466715 : Blo 1915435 6466715 := bstep (se 1 (by rfl) ⟨4850036, by rfl⟩ : syracuseStep 6466715 = 9700073) B9700073
theorem B4311143 : Blo 1915435 4311143 := bstep (se 1 (by rfl) ⟨3233357, by rfl⟩ : syracuseStep 4311143 = 6466715) B6466715
theorem B2874095 : Blo 1915435 2874095 := bstep (se 1 (by rfl) ⟨2155571, by rfl⟩ : syracuseStep 2874095 = 4311143) B4311143
theorem B1916063 : Blo 1915435 1916063 := bstep (se 1 (by rfl) ⟨1437047, by rfl⟩ : syracuseStep 1916063 = 2874095) B2874095
theorem B2874101 : Blo 1915435 2874101 := bbase (se 5 (by rfl) ⟨134723, by rfl⟩ : syracuseStep 2874101 = 269447) (by norm_num)
theorem B1916067 : Blo 1915435 1916067 := bstep (se 1 (by rfl) ⟨1437050, by rfl⟩ : syracuseStep 1916067 = 2874101) B2874101
theorem B3884429 : Blo 1915435 3884429 := bbase (se 3 (by rfl) ⟨728330, by rfl⟩ : syracuseStep 3884429 = 1456661) (by norm_num)
theorem B2589619 : Blo 1915435 2589619 := bstep (se 1 (by rfl) ⟨1942214, by rfl⟩ : syracuseStep 2589619 = 3884429) B3884429
theorem B3452825 : Blo 1915435 3452825 := bstep (se 2 (by rfl) ⟨1294809, by rfl⟩ : syracuseStep 3452825 = 2589619) B2589619
theorem B9207533 : Blo 1915435 9207533 := bstep (se 3 (by rfl) ⟨1726412, by rfl⟩ : syracuseStep 9207533 = 3452825) B3452825
theorem B6138355 : Blo 1915435 6138355 := bstep (se 1 (by rfl) ⟨4603766, by rfl⟩ : syracuseStep 6138355 = 9207533) B9207533
theorem B8184473 : Blo 1915435 8184473 := bstep (se 2 (by rfl) ⟨3069177, by rfl⟩ : syracuseStep 8184473 = 6138355) B6138355
theorem B5456315 : Blo 1915435 5456315 := bstep (se 1 (by rfl) ⟨4092236, by rfl⟩ : syracuseStep 5456315 = 8184473) B8184473
theorem B3637543 : Blo 1915435 3637543 := bstep (se 1 (by rfl) ⟨2728157, by rfl⟩ : syracuseStep 3637543 = 5456315) B5456315
theorem B4850057 : Blo 1915435 4850057 := bstep (se 2 (by rfl) ⟨1818771, by rfl⟩ : syracuseStep 4850057 = 3637543) B3637543
theorem B3233371 : Blo 1915435 3233371 := bstep (se 1 (by rfl) ⟨2425028, by rfl⟩ : syracuseStep 3233371 = 4850057) B4850057
theorem B4311161 : Blo 1915435 4311161 := bstep (se 2 (by rfl) ⟨1616685, by rfl⟩ : syracuseStep 4311161 = 3233371) B3233371
theorem B2874107 : Blo 1915435 2874107 := bstep (se 1 (by rfl) ⟨2155580, by rfl⟩ : syracuseStep 2874107 = 4311161) B4311161
theorem B1916071 : Blo 1915435 1916071 := bstep (se 1 (by rfl) ⟨1437053, by rfl⟩ : syracuseStep 1916071 = 2874107) B2874107
theorem B2155585 : Blo 1915435 2155585 := bbase (se 2 (by rfl) ⟨808344, by rfl⟩ : syracuseStep 2155585 = 1616689) (by norm_num)
theorem B2874113 : Blo 1915435 2874113 := bstep (se 2 (by rfl) ⟨1077792, by rfl⟩ : syracuseStep 2874113 = 2155585) B2155585
theorem B1916075 : Blo 1915435 1916075 := bstep (se 1 (by rfl) ⟨1437056, by rfl⟩ : syracuseStep 1916075 = 2874113) B2874113
theorem B4850077 : Blo 1915435 4850077 := bbase (se 3 (by rfl) ⟨909389, by rfl⟩ : syracuseStep 4850077 = 1818779) (by norm_num)
theorem B6466769 : Blo 1915435 6466769 := bstep (se 2 (by rfl) ⟨2425038, by rfl⟩ : syracuseStep 6466769 = 4850077) B4850077
theorem B4311179 : Blo 1915435 4311179 := bstep (se 1 (by rfl) ⟨3233384, by rfl⟩ : syracuseStep 4311179 = 6466769) B6466769
theorem B2874119 : Blo 1915435 2874119 := bstep (se 1 (by rfl) ⟨2155589, by rfl⟩ : syracuseStep 2874119 = 4311179) B4311179
theorem B1916079 : Blo 1915435 1916079 := bstep (se 1 (by rfl) ⟨1437059, by rfl⟩ : syracuseStep 1916079 = 2874119) B2874119
theorem B2874125 : Blo 1915435 2874125 := bbase (se 3 (by rfl) ⟨538898, by rfl⟩ : syracuseStep 2874125 = 1077797) (by norm_num)
theorem B1916083 : Blo 1915435 1916083 := bstep (se 1 (by rfl) ⟨1437062, by rfl⟩ : syracuseStep 1916083 = 2874125) B2874125
theorem B4311197 : Blo 1915435 4311197 := bbase (se 3 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 4311197 = 1616699) (by norm_num)
theorem B2874131 : Blo 1915435 2874131 := bstep (se 1 (by rfl) ⟨2155598, by rfl⟩ : syracuseStep 2874131 = 4311197) B4311197
theorem B1916087 : Blo 1915435 1916087 := bstep (se 1 (by rfl) ⟨1437065, by rfl⟩ : syracuseStep 1916087 = 2874131) B2874131
theorem B3233405 : Blo 1915435 3233405 := bbase (se 3 (by rfl) ⟨606263, by rfl⟩ : syracuseStep 3233405 = 1212527) (by norm_num)
theorem B2155603 : Blo 1915435 2155603 := bstep (se 1 (by rfl) ⟨1616702, by rfl⟩ : syracuseStep 2155603 = 3233405) B3233405
theorem B2874137 : Blo 1915435 2874137 := bstep (se 2 (by rfl) ⟨1077801, by rfl⟩ : syracuseStep 2874137 = 2155603) B2155603
theorem B1916091 : Blo 1915435 1916091 := bstep (se 1 (by rfl) ⟨1437068, by rfl⟩ : syracuseStep 1916091 = 2874137) B2874137
theorem B46613717 : Blo 1915435 46613717 := bbase (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) (by norm_num)
theorem B31075811 : Blo 1915435 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B20717207 : Blo 1915435 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B13811471 : Blo 1915435 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B9207647 : Blo 1915435 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B6138431 : Blo 1915435 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B4092287 : Blo 1915435 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B10912765 : Blo 1915435 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B14550353 : Blo 1915435 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B9700235 : Blo 1915435 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B6466823 : Blo 1915435 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B4311215 : Blo 1915435 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B2874143 : Blo 1915435 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B1916095 : Blo 1915435 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B2874149 : Blo 1915435 2874149 := bbase (se 4 (by rfl) ⟨269451, by rfl⟩ : syracuseStep 2874149 = 538903) (by norm_num)
theorem B1916099 : Blo 1915435 1916099 := bstep (se 1 (by rfl) ⟨1437074, by rfl⟩ : syracuseStep 1916099 = 2874149) B2874149
theorem B2425069 : Blo 1915435 2425069 := bbase (se 3 (by rfl) ⟨454700, by rfl⟩ : syracuseStep 2425069 = 909401) (by norm_num)
theorem B3233425 : Blo 1915435 3233425 := bstep (se 2 (by rfl) ⟨1212534, by rfl⟩ : syracuseStep 3233425 = 2425069) B2425069
theorem B4311233 : Blo 1915435 4311233 := bstep (se 2 (by rfl) ⟨1616712, by rfl⟩ : syracuseStep 4311233 = 3233425) B3233425
theorem B2874155 : Blo 1915435 2874155 := bstep (se 1 (by rfl) ⟨2155616, by rfl⟩ : syracuseStep 2874155 = 4311233) B4311233
theorem B1916103 : Blo 1915435 1916103 := bstep (se 1 (by rfl) ⟨1437077, by rfl⟩ : syracuseStep 1916103 = 2874155) B2874155
theorem B2155621 : Blo 1915435 2155621 := bbase (se 4 (by rfl) ⟨202089, by rfl⟩ : syracuseStep 2155621 = 404179) (by norm_num)
theorem B2874161 : Blo 1915435 2874161 := bstep (se 2 (by rfl) ⟨1077810, by rfl⟩ : syracuseStep 2874161 = 2155621) B2155621
theorem B1916107 : Blo 1915435 1916107 := bstep (se 1 (by rfl) ⟨1437080, by rfl⟩ : syracuseStep 1916107 = 2874161) B2874161
theorem B2046161 : Blo 1915435 2046161 := bbase (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) (by norm_num)
theorem B5456429 : Blo 1915435 5456429 := bstep (se 3 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 5456429 = 2046161) B2046161
theorem B3637619 : Blo 1915435 3637619 := bstep (se 1 (by rfl) ⟨2728214, by rfl⟩ : syracuseStep 3637619 = 5456429) B5456429
theorem B2425079 : Blo 1915435 2425079 := bstep (se 1 (by rfl) ⟨1818809, by rfl⟩ : syracuseStep 2425079 = 3637619) B3637619
theorem B6466877 : Blo 1915435 6466877 := bstep (se 3 (by rfl) ⟨1212539, by rfl⟩ : syracuseStep 6466877 = 2425079) B2425079
theorem B4311251 : Blo 1915435 4311251 := bstep (se 1 (by rfl) ⟨3233438, by rfl⟩ : syracuseStep 4311251 = 6466877) B6466877
theorem B2874167 : Blo 1915435 2874167 := bstep (se 1 (by rfl) ⟨2155625, by rfl⟩ : syracuseStep 2874167 = 4311251) B4311251
theorem B1916111 : Blo 1915435 1916111 := bstep (se 1 (by rfl) ⟨1437083, by rfl⟩ : syracuseStep 1916111 = 2874167) B2874167
theorem B2874173 : Blo 1915435 2874173 := bbase (se 3 (by rfl) ⟨538907, by rfl⟩ : syracuseStep 2874173 = 1077815) (by norm_num)
theorem B1916115 : Blo 1915435 1916115 := bstep (se 1 (by rfl) ⟨1437086, by rfl⟩ : syracuseStep 1916115 = 2874173) B2874173
theorem B4311269 : Blo 1915435 4311269 := bbase (se 4 (by rfl) ⟨404181, by rfl⟩ : syracuseStep 4311269 = 808363) (by norm_num)
theorem B2874179 : Blo 1915435 2874179 := bstep (se 1 (by rfl) ⟨2155634, by rfl⟩ : syracuseStep 2874179 = 4311269) B4311269
theorem B1916119 : Blo 1915435 1916119 := bstep (se 1 (by rfl) ⟨1437089, by rfl⟩ : syracuseStep 1916119 = 2874179) B2874179
theorem B4850189 : Blo 1915435 4850189 := bbase (se 3 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 4850189 = 1818821) (by norm_num)
theorem B3233459 : Blo 1915435 3233459 := bstep (se 1 (by rfl) ⟨2425094, by rfl⟩ : syracuseStep 3233459 = 4850189) B4850189
theorem B2155639 : Blo 1915435 2155639 := bstep (se 1 (by rfl) ⟨1616729, by rfl⟩ : syracuseStep 2155639 = 3233459) B3233459
theorem B2874185 : Blo 1915435 2874185 := bstep (se 2 (by rfl) ⟨1077819, by rfl⟩ : syracuseStep 2874185 = 2155639) B2155639
theorem B1916123 : Blo 1915435 1916123 := bstep (se 1 (by rfl) ⟨1437092, by rfl⟩ : syracuseStep 1916123 = 2874185) B2874185
theorem B2728237 : Blo 1915435 2728237 := bbase (se 3 (by rfl) ⟨511544, by rfl⟩ : syracuseStep 2728237 = 1023089) (by norm_num)
theorem B3637649 : Blo 1915435 3637649 := bstep (se 2 (by rfl) ⟨1364118, by rfl⟩ : syracuseStep 3637649 = 2728237) B2728237
theorem B9700397 : Blo 1915435 9700397 := bstep (se 3 (by rfl) ⟨1818824, by rfl⟩ : syracuseStep 9700397 = 3637649) B3637649
theorem B6466931 : Blo 1915435 6466931 := bstep (se 1 (by rfl) ⟨4850198, by rfl⟩ : syracuseStep 6466931 = 9700397) B9700397
theorem B4311287 : Blo 1915435 4311287 := bstep (se 1 (by rfl) ⟨3233465, by rfl⟩ : syracuseStep 4311287 = 6466931) B6466931
theorem B2874191 : Blo 1915435 2874191 := bstep (se 1 (by rfl) ⟨2155643, by rfl⟩ : syracuseStep 2874191 = 4311287) B4311287
theorem B1916127 : Blo 1915435 1916127 := bstep (se 1 (by rfl) ⟨1437095, by rfl⟩ : syracuseStep 1916127 = 2874191) B2874191
theorem B2874197 : Blo 1915435 2874197 := bbase (se 9 (by rfl) ⟨8420, by rfl⟩ : syracuseStep 2874197 = 16841) (by norm_num)
theorem B1916131 : Blo 1915435 1916131 := bstep (se 1 (by rfl) ⟨1437098, by rfl⟩ : syracuseStep 1916131 = 2874197) B2874197
theorem B4092373 : Blo 1915435 4092373 := bbase (se 7 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 4092373 = 95915) (by norm_num)
theorem B5456497 : Blo 1915435 5456497 := bstep (se 2 (by rfl) ⟨2046186, by rfl⟩ : syracuseStep 5456497 = 4092373) B4092373
theorem B7275329 : Blo 1915435 7275329 := bstep (se 2 (by rfl) ⟨2728248, by rfl⟩ : syracuseStep 7275329 = 5456497) B5456497
theorem B4850219 : Blo 1915435 4850219 := bstep (se 1 (by rfl) ⟨3637664, by rfl⟩ : syracuseStep 4850219 = 7275329) B7275329
theorem B3233479 : Blo 1915435 3233479 := bstep (se 1 (by rfl) ⟨2425109, by rfl⟩ : syracuseStep 3233479 = 4850219) B4850219
theorem B4311305 : Blo 1915435 4311305 := bstep (se 2 (by rfl) ⟨1616739, by rfl⟩ : syracuseStep 4311305 = 3233479) B3233479
theorem B2874203 : Blo 1915435 2874203 := bstep (se 1 (by rfl) ⟨2155652, by rfl⟩ : syracuseStep 2874203 = 4311305) B4311305
theorem B1916135 : Blo 1915435 1916135 := bstep (se 1 (by rfl) ⟨1437101, by rfl⟩ : syracuseStep 1916135 = 2874203) B2874203
theorem B2155657 : Blo 1915435 2155657 := bbase (se 2 (by rfl) ⟨808371, by rfl⟩ : syracuseStep 2155657 = 1616743) (by norm_num)
theorem B2874209 : Blo 1915435 2874209 := bstep (se 2 (by rfl) ⟨1077828, by rfl⟩ : syracuseStep 2874209 = 2155657) B2155657
theorem B1916139 : Blo 1915435 1916139 := bstep (se 1 (by rfl) ⟨1437104, by rfl⟩ : syracuseStep 1916139 = 2874209) B2874209
theorem B36831509 : Blo 1915435 36831509 := bbase (se 6 (by rfl) ⟨863238, by rfl⟩ : syracuseStep 36831509 = 1726477) (by norm_num)
theorem B24554339 : Blo 1915435 24554339 := bstep (se 1 (by rfl) ⟨18415754, by rfl⟩ : syracuseStep 24554339 = 36831509) B36831509
theorem B16369559 : Blo 1915435 16369559 := bstep (se 1 (by rfl) ⟨12277169, by rfl⟩ : syracuseStep 16369559 = 24554339) B24554339
theorem B10913039 : Blo 1915435 10913039 := bstep (se 1 (by rfl) ⟨8184779, by rfl⟩ : syracuseStep 10913039 = 16369559) B16369559
theorem B7275359 : Blo 1915435 7275359 := bstep (se 1 (by rfl) ⟨5456519, by rfl⟩ : syracuseStep 7275359 = 10913039) B10913039
theorem B4850239 : Blo 1915435 4850239 := bstep (se 1 (by rfl) ⟨3637679, by rfl⟩ : syracuseStep 4850239 = 7275359) B7275359
theorem B6466985 : Blo 1915435 6466985 := bstep (se 2 (by rfl) ⟨2425119, by rfl⟩ : syracuseStep 6466985 = 4850239) B4850239
theorem B4311323 : Blo 1915435 4311323 := bstep (se 1 (by rfl) ⟨3233492, by rfl⟩ : syracuseStep 4311323 = 6466985) B6466985
theorem B2874215 : Blo 1915435 2874215 := bstep (se 1 (by rfl) ⟨2155661, by rfl⟩ : syracuseStep 2874215 = 4311323) B4311323
theorem B1916143 : Blo 1915435 1916143 := bstep (se 1 (by rfl) ⟨1437107, by rfl⟩ : syracuseStep 1916143 = 2874215) B2874215
theorem B2874221 : Blo 1915435 2874221 := bbase (se 3 (by rfl) ⟨538916, by rfl⟩ : syracuseStep 2874221 = 1077833) (by norm_num)
theorem B1916147 : Blo 1915435 1916147 := bstep (se 1 (by rfl) ⟨1437110, by rfl⟩ : syracuseStep 1916147 = 2874221) B2874221
theorem B4311341 : Blo 1915435 4311341 := bbase (se 3 (by rfl) ⟨808376, by rfl⟩ : syracuseStep 4311341 = 1616753) (by norm_num)
theorem B2874227 : Blo 1915435 2874227 := bstep (se 1 (by rfl) ⟨2155670, by rfl⟩ : syracuseStep 2874227 = 4311341) B4311341
theorem B1916151 : Blo 1915435 1916151 := bstep (se 1 (by rfl) ⟨1437113, by rfl⟩ : syracuseStep 1916151 = 2874227) B2874227
theorem B2589733 : Blo 1915435 2589733 := bbase (se 4 (by rfl) ⟨242787, by rfl⟩ : syracuseStep 2589733 = 485575) (by norm_num)
theorem B3452977 : Blo 1915435 3452977 := bstep (se 2 (by rfl) ⟨1294866, by rfl⟩ : syracuseStep 3452977 = 2589733) B2589733
theorem B4603969 : Blo 1915435 4603969 := bstep (se 2 (by rfl) ⟨1726488, by rfl⟩ : syracuseStep 4603969 = 3452977) B3452977
theorem B6138625 : Blo 1915435 6138625 := bstep (se 2 (by rfl) ⟨2301984, by rfl⟩ : syracuseStep 6138625 = 4603969) B4603969
theorem B8184833 : Blo 1915435 8184833 := bstep (se 2 (by rfl) ⟨3069312, by rfl⟩ : syracuseStep 8184833 = 6138625) B6138625
theorem B5456555 : Blo 1915435 5456555 := bstep (se 1 (by rfl) ⟨4092416, by rfl⟩ : syracuseStep 5456555 = 8184833) B8184833
theorem B3637703 : Blo 1915435 3637703 := bstep (se 1 (by rfl) ⟨2728277, by rfl⟩ : syracuseStep 3637703 = 5456555) B5456555
theorem B2425135 : Blo 1915435 2425135 := bstep (se 1 (by rfl) ⟨1818851, by rfl⟩ : syracuseStep 2425135 = 3637703) B3637703
theorem B3233513 : Blo 1915435 3233513 := bstep (se 2 (by rfl) ⟨1212567, by rfl⟩ : syracuseStep 3233513 = 2425135) B2425135
theorem B2155675 : Blo 1915435 2155675 := bstep (se 1 (by rfl) ⟨1616756, by rfl⟩ : syracuseStep 2155675 = 3233513) B3233513
theorem B2874233 : Blo 1915435 2874233 := bstep (se 2 (by rfl) ⟨1077837, by rfl⟩ : syracuseStep 2874233 = 2155675) B2155675
theorem B1916155 : Blo 1915435 1916155 := bstep (se 1 (by rfl) ⟨1437116, by rfl⟩ : syracuseStep 1916155 = 2874233) B2874233
theorem B4148261 : Blo 1915435 4148261 := bbase (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) (by norm_num)
theorem B2765507 : Blo 1915435 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B7374685 : Blo 1915435 7374685 := bstep (se 3 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 7374685 = 2765507) B2765507
theorem B9832913 : Blo 1915435 9832913 := bstep (se 2 (by rfl) ⟨3687342, by rfl⟩ : syracuseStep 9832913 = 7374685) B7374685
theorem B6555275 : Blo 1915435 6555275 := bstep (se 1 (by rfl) ⟨4916456, by rfl⟩ : syracuseStep 6555275 = 9832913) B9832913
theorem B4370183 : Blo 1915435 4370183 := bstep (se 1 (by rfl) ⟨3277637, by rfl⟩ : syracuseStep 4370183 = 6555275) B6555275
theorem B2913455 : Blo 1915435 2913455 := bstep (se 1 (by rfl) ⟨2185091, by rfl⟩ : syracuseStep 2913455 = 4370183) B4370183
theorem B1942303 : Blo 1915435 1942303 := bstep (se 1 (by rfl) ⟨1456727, by rfl⟩ : syracuseStep 1942303 = 2913455) B2913455
theorem B2589737 : Blo 1915435 2589737 := bstep (se 2 (by rfl) ⟨971151, by rfl⟩ : syracuseStep 2589737 = 1942303) B1942303
theorem B27623861 : Blo 1915435 27623861 := bstep (se 5 (by rfl) ⟨1294868, by rfl⟩ : syracuseStep 27623861 = 2589737) B2589737
theorem B18415907 : Blo 1915435 18415907 := bstep (se 1 (by rfl) ⟨13811930, by rfl⟩ : syracuseStep 18415907 = 27623861) B27623861
theorem B12277271 : Blo 1915435 12277271 := bstep (se 1 (by rfl) ⟨9207953, by rfl⟩ : syracuseStep 12277271 = 18415907) B18415907
theorem B32739389 : Blo 1915435 32739389 := bstep (se 3 (by rfl) ⟨6138635, by rfl⟩ : syracuseStep 32739389 = 12277271) B12277271
theorem B21826259 : Blo 1915435 21826259 := bstep (se 1 (by rfl) ⟨16369694, by rfl⟩ : syracuseStep 21826259 = 32739389) B32739389
theorem B14550839 : Blo 1915435 14550839 := bstep (se 1 (by rfl) ⟨10913129, by rfl⟩ : syracuseStep 14550839 = 21826259) B21826259
theorem B9700559 : Blo 1915435 9700559 := bstep (se 1 (by rfl) ⟨7275419, by rfl⟩ : syracuseStep 9700559 = 14550839) B14550839
theorem B6467039 : Blo 1915435 6467039 := bstep (se 1 (by rfl) ⟨4850279, by rfl⟩ : syracuseStep 6467039 = 9700559) B9700559
theorem B4311359 : Blo 1915435 4311359 := bstep (se 1 (by rfl) ⟨3233519, by rfl⟩ : syracuseStep 4311359 = 6467039) B6467039
theorem B2874239 : Blo 1915435 2874239 := bstep (se 1 (by rfl) ⟨2155679, by rfl⟩ : syracuseStep 2874239 = 4311359) B4311359
theorem B1916159 : Blo 1915435 1916159 := bstep (se 1 (by rfl) ⟨1437119, by rfl⟩ : syracuseStep 1916159 = 2874239) B2874239
theorem B2874245 : Blo 1915435 2874245 := bbase (se 4 (by rfl) ⟨269460, by rfl⟩ : syracuseStep 2874245 = 538921) (by norm_num)
theorem B1916163 : Blo 1915435 1916163 := bstep (se 1 (by rfl) ⟨1437122, by rfl⟩ : syracuseStep 1916163 = 2874245) B2874245
theorem B3233533 : Blo 1915435 3233533 := bbase (se 3 (by rfl) ⟨606287, by rfl⟩ : syracuseStep 3233533 = 1212575) (by norm_num)
theorem B4311377 : Blo 1915435 4311377 := bstep (se 2 (by rfl) ⟨1616766, by rfl⟩ : syracuseStep 4311377 = 3233533) B3233533
theorem B2874251 : Blo 1915435 2874251 := bstep (se 1 (by rfl) ⟨2155688, by rfl⟩ : syracuseStep 2874251 = 4311377) B4311377
theorem B1916167 : Blo 1915435 1916167 := bstep (se 1 (by rfl) ⟨1437125, by rfl⟩ : syracuseStep 1916167 = 2874251) B2874251
theorem B2155693 : Blo 1915435 2155693 := bbase (se 3 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 2155693 = 808385) (by norm_num)
theorem B2874257 : Blo 1915435 2874257 := bstep (se 2 (by rfl) ⟨1077846, by rfl⟩ : syracuseStep 2874257 = 2155693) B2155693
theorem B1916171 : Blo 1915435 1916171 := bstep (se 1 (by rfl) ⟨1437128, by rfl⟩ : syracuseStep 1916171 = 2874257) B2874257
theorem B6467093 : Blo 1915435 6467093 := bbase (se 6 (by rfl) ⟨151572, by rfl⟩ : syracuseStep 6467093 = 303145) (by norm_num)
theorem B4311395 : Blo 1915435 4311395 := bstep (se 1 (by rfl) ⟨3233546, by rfl⟩ : syracuseStep 4311395 = 6467093) B6467093
theorem B2874263 : Blo 1915435 2874263 := bstep (se 1 (by rfl) ⟨2155697, by rfl⟩ : syracuseStep 2874263 = 4311395) B4311395
theorem B1916175 : Blo 1915435 1916175 := bstep (se 1 (by rfl) ⟨1437131, by rfl⟩ : syracuseStep 1916175 = 2874263) B2874263
theorem B2874269 : Blo 1915435 2874269 := bbase (se 3 (by rfl) ⟨538925, by rfl⟩ : syracuseStep 2874269 = 1077851) (by norm_num)
theorem B1916179 : Blo 1915435 1916179 := bstep (se 1 (by rfl) ⟨1437134, by rfl⟩ : syracuseStep 1916179 = 2874269) B2874269
theorem B4311413 : Blo 1915435 4311413 := bbase (se 5 (by rfl) ⟨202097, by rfl⟩ : syracuseStep 4311413 = 404195) (by norm_num)
theorem B2874275 : Blo 1915435 2874275 := bstep (se 1 (by rfl) ⟨2155706, by rfl⟩ : syracuseStep 2874275 = 4311413) B4311413
theorem B1916183 : Blo 1915435 1916183 := bstep (se 1 (by rfl) ⟨1437137, by rfl⟩ : syracuseStep 1916183 = 2874275) B2874275
theorem B4604045 : Blo 1915435 4604045 := bbase (se 3 (by rfl) ⟨863258, by rfl⟩ : syracuseStep 4604045 = 1726517) (by norm_num)
theorem B12277453 : Blo 1915435 12277453 := bstep (se 3 (by rfl) ⟨2302022, by rfl⟩ : syracuseStep 12277453 = 4604045) B4604045
theorem B16369937 : Blo 1915435 16369937 := bstep (se 2 (by rfl) ⟨6138726, by rfl⟩ : syracuseStep 16369937 = 12277453) B12277453
theorem B10913291 : Blo 1915435 10913291 := bstep (se 1 (by rfl) ⟨8184968, by rfl⟩ : syracuseStep 10913291 = 16369937) B16369937
theorem B7275527 : Blo 1915435 7275527 := bstep (se 1 (by rfl) ⟨5456645, by rfl⟩ : syracuseStep 7275527 = 10913291) B10913291
theorem B4850351 : Blo 1915435 4850351 := bstep (se 1 (by rfl) ⟨3637763, by rfl⟩ : syracuseStep 4850351 = 7275527) B7275527
theorem B3233567 : Blo 1915435 3233567 := bstep (se 1 (by rfl) ⟨2425175, by rfl⟩ : syracuseStep 3233567 = 4850351) B4850351
theorem B2155711 : Blo 1915435 2155711 := bstep (se 1 (by rfl) ⟨1616783, by rfl⟩ : syracuseStep 2155711 = 3233567) B3233567
theorem B2874281 : Blo 1915435 2874281 := bstep (se 2 (by rfl) ⟨1077855, by rfl⟩ : syracuseStep 2874281 = 2155711) B2155711
theorem B1916187 : Blo 1915435 1916187 := bstep (se 1 (by rfl) ⟨1437140, by rfl⟩ : syracuseStep 1916187 = 2874281) B2874281
theorem B7275541 : Blo 1915435 7275541 := bbase (se 6 (by rfl) ⟨170520, by rfl⟩ : syracuseStep 7275541 = 341041) (by norm_num)
theorem B9700721 : Blo 1915435 9700721 := bstep (se 2 (by rfl) ⟨3637770, by rfl⟩ : syracuseStep 9700721 = 7275541) B7275541
theorem B6467147 : Blo 1915435 6467147 := bstep (se 1 (by rfl) ⟨4850360, by rfl⟩ : syracuseStep 6467147 = 9700721) B9700721
theorem B4311431 : Blo 1915435 4311431 := bstep (se 1 (by rfl) ⟨3233573, by rfl⟩ : syracuseStep 4311431 = 6467147) B6467147
theorem B2874287 : Blo 1915435 2874287 := bstep (se 1 (by rfl) ⟨2155715, by rfl⟩ : syracuseStep 2874287 = 4311431) B4311431
theorem B1916191 : Blo 1915435 1916191 := bstep (se 1 (by rfl) ⟨1437143, by rfl⟩ : syracuseStep 1916191 = 2874287) B2874287
theorem B2874293 : Blo 1915435 2874293 := bbase (se 5 (by rfl) ⟨134732, by rfl⟩ : syracuseStep 2874293 = 269465) (by norm_num)
theorem B1916195 : Blo 1915435 1916195 := bstep (se 1 (by rfl) ⟨1437146, by rfl⟩ : syracuseStep 1916195 = 2874293) B2874293
theorem B4850381 : Blo 1915435 4850381 := bbase (se 3 (by rfl) ⟨909446, by rfl⟩ : syracuseStep 4850381 = 1818893) (by norm_num)
theorem B3233587 : Blo 1915435 3233587 := bstep (se 1 (by rfl) ⟨2425190, by rfl⟩ : syracuseStep 3233587 = 4850381) B4850381
theorem B4311449 : Blo 1915435 4311449 := bstep (se 2 (by rfl) ⟨1616793, by rfl⟩ : syracuseStep 4311449 = 3233587) B3233587
theorem B2874299 : Blo 1915435 2874299 := bstep (se 1 (by rfl) ⟨2155724, by rfl⟩ : syracuseStep 2874299 = 4311449) B4311449
theorem B1916199 : Blo 1915435 1916199 := bstep (se 1 (by rfl) ⟨1437149, by rfl⟩ : syracuseStep 1916199 = 2874299) B2874299
theorem B2155729 : Blo 1915435 2155729 := bbase (se 2 (by rfl) ⟨808398, by rfl⟩ : syracuseStep 2155729 = 1616797) (by norm_num)
theorem B2874305 : Blo 1915435 2874305 := bstep (se 2 (by rfl) ⟨1077864, by rfl⟩ : syracuseStep 2874305 = 2155729) B2155729
theorem B1916203 : Blo 1915435 1916203 := bstep (se 1 (by rfl) ⟨1437152, by rfl⟩ : syracuseStep 1916203 = 2874305) B2874305
theorem B7875413 : Blo 1915435 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B5250275 : Blo 1915435 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B3500183 : Blo 1915435 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B2333455 : Blo 1915435 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B12445093 : Blo 1915435 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B16593457 : Blo 1915435 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B22124609 : Blo 1915435 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B14749739 : Blo 1915435 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B9833159 : Blo 1915435 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B6555439 : Blo 1915435 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B8740585 : Blo 1915435 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B11654113 : Blo 1915435 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B15538817 : Blo 1915435 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B10359211 : Blo 1915435 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B13812281 : Blo 1915435 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B9208187 : Blo 1915435 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B6138791 : Blo 1915435 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B4092527 : Blo 1915435 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B2728351 : Blo 1915435 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B3637801 : Blo 1915435 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B4850401 : Blo 1915435 4850401 := bstep (se 2 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 4850401 = 3637801) B3637801
theorem B6467201 : Blo 1915435 6467201 := bstep (se 2 (by rfl) ⟨2425200, by rfl⟩ : syracuseStep 6467201 = 4850401) B4850401
theorem B4311467 : Blo 1915435 4311467 := bstep (se 1 (by rfl) ⟨3233600, by rfl⟩ : syracuseStep 4311467 = 6467201) B6467201
theorem B2874311 : Blo 1915435 2874311 := bstep (se 1 (by rfl) ⟨2155733, by rfl⟩ : syracuseStep 2874311 = 4311467) B4311467
theorem B1916207 : Blo 1915435 1916207 := bstep (se 1 (by rfl) ⟨1437155, by rfl⟩ : syracuseStep 1916207 = 2874311) B2874311
theorem B2874317 : Blo 1915435 2874317 := bbase (se 3 (by rfl) ⟨538934, by rfl⟩ : syracuseStep 2874317 = 1077869) (by norm_num)
theorem B1916211 : Blo 1915435 1916211 := bstep (se 1 (by rfl) ⟨1437158, by rfl⟩ : syracuseStep 1916211 = 2874317) B2874317
theorem B4311485 : Blo 1915435 4311485 := bbase (se 3 (by rfl) ⟨808403, by rfl⟩ : syracuseStep 4311485 = 1616807) (by norm_num)
theorem B2874323 : Blo 1915435 2874323 := bstep (se 1 (by rfl) ⟨2155742, by rfl⟩ : syracuseStep 2874323 = 4311485) B4311485
theorem B1916215 : Blo 1915435 1916215 := bstep (se 1 (by rfl) ⟨1437161, by rfl⟩ : syracuseStep 1916215 = 2874323) B2874323
theorem B3233621 : Blo 1915435 3233621 := bbase (se 9 (by rfl) ⟨9473, by rfl⟩ : syracuseStep 3233621 = 18947) (by norm_num)
theorem B2155747 : Blo 1915435 2155747 := bstep (se 1 (by rfl) ⟨1616810, by rfl⟩ : syracuseStep 2155747 = 3233621) B3233621
theorem B2874329 : Blo 1915435 2874329 := bstep (se 2 (by rfl) ⟨1077873, by rfl⟩ : syracuseStep 2874329 = 2155747) B2155747
theorem B1916219 : Blo 1915435 1916219 := bstep (se 1 (by rfl) ⟨1437164, by rfl⟩ : syracuseStep 1916219 = 2874329) B2874329
theorem B6906197 : Blo 1915435 6906197 := bbase (se 10 (by rfl) ⟨10116, by rfl⟩ : syracuseStep 6906197 = 20233) (by norm_num)
theorem B4604131 : Blo 1915435 4604131 := bstep (se 1 (by rfl) ⟨3453098, by rfl⟩ : syracuseStep 4604131 = 6906197) B6906197
theorem B6138841 : Blo 1915435 6138841 := bstep (se 2 (by rfl) ⟨2302065, by rfl⟩ : syracuseStep 6138841 = 4604131) B4604131
theorem B8185121 : Blo 1915435 8185121 := bstep (se 2 (by rfl) ⟨3069420, by rfl⟩ : syracuseStep 8185121 = 6138841) B6138841
theorem B5456747 : Blo 1915435 5456747 := bstep (se 1 (by rfl) ⟨4092560, by rfl⟩ : syracuseStep 5456747 = 8185121) B8185121
theorem B14551325 : Blo 1915435 14551325 := bstep (se 3 (by rfl) ⟨2728373, by rfl⟩ : syracuseStep 14551325 = 5456747) B5456747
theorem B9700883 : Blo 1915435 9700883 := bstep (se 1 (by rfl) ⟨7275662, by rfl⟩ : syracuseStep 9700883 = 14551325) B14551325
theorem B6467255 : Blo 1915435 6467255 := bstep (se 1 (by rfl) ⟨4850441, by rfl⟩ : syracuseStep 6467255 = 9700883) B9700883
theorem B4311503 : Blo 1915435 4311503 := bstep (se 1 (by rfl) ⟨3233627, by rfl⟩ : syracuseStep 4311503 = 6467255) B6467255
theorem B2874335 : Blo 1915435 2874335 := bstep (se 1 (by rfl) ⟨2155751, by rfl⟩ : syracuseStep 2874335 = 4311503) B4311503
theorem B1916223 : Blo 1915435 1916223 := bstep (se 1 (by rfl) ⟨1437167, by rfl⟩ : syracuseStep 1916223 = 2874335) B2874335
theorem B2874341 : Blo 1915435 2874341 := bbase (se 4 (by rfl) ⟨269469, by rfl⟩ : syracuseStep 2874341 = 538939) (by norm_num)
theorem B1916227 : Blo 1915435 1916227 := bstep (se 1 (by rfl) ⟨1437170, by rfl⟩ : syracuseStep 1916227 = 2874341) B2874341
theorem B8185157 : Blo 1915435 8185157 := bbase (se 4 (by rfl) ⟨767358, by rfl⟩ : syracuseStep 8185157 = 1534717) (by norm_num)
theorem B5456771 : Blo 1915435 5456771 := bstep (se 1 (by rfl) ⟨4092578, by rfl⟩ : syracuseStep 5456771 = 8185157) B8185157
theorem B3637847 : Blo 1915435 3637847 := bstep (se 1 (by rfl) ⟨2728385, by rfl⟩ : syracuseStep 3637847 = 5456771) B5456771
theorem B2425231 : Blo 1915435 2425231 := bstep (se 1 (by rfl) ⟨1818923, by rfl⟩ : syracuseStep 2425231 = 3637847) B3637847
theorem B3233641 : Blo 1915435 3233641 := bstep (se 2 (by rfl) ⟨1212615, by rfl⟩ : syracuseStep 3233641 = 2425231) B2425231
theorem B4311521 : Blo 1915435 4311521 := bstep (se 2 (by rfl) ⟨1616820, by rfl⟩ : syracuseStep 4311521 = 3233641) B3233641
theorem B2874347 : Blo 1915435 2874347 := bstep (se 1 (by rfl) ⟨2155760, by rfl⟩ : syracuseStep 2874347 = 4311521) B4311521
theorem B1916231 : Blo 1915435 1916231 := bstep (se 1 (by rfl) ⟨1437173, by rfl⟩ : syracuseStep 1916231 = 2874347) B2874347
theorem B2155765 : Blo 1915435 2155765 := bbase (se 5 (by rfl) ⟨101051, by rfl⟩ : syracuseStep 2155765 = 202103) (by norm_num)
theorem B2874353 : Blo 1915435 2874353 := bstep (se 2 (by rfl) ⟨1077882, by rfl⟩ : syracuseStep 2874353 = 2155765) B2155765
theorem B1916235 : Blo 1915435 1916235 := bstep (se 1 (by rfl) ⟨1437176, by rfl⟩ : syracuseStep 1916235 = 2874353) B2874353
theorem B2425241 : Blo 1915435 2425241 := bbase (se 2 (by rfl) ⟨909465, by rfl⟩ : syracuseStep 2425241 = 1818931) (by norm_num)
theorem B6467309 : Blo 1915435 6467309 := bstep (se 3 (by rfl) ⟨1212620, by rfl⟩ : syracuseStep 6467309 = 2425241) B2425241
theorem B4311539 : Blo 1915435 4311539 := bstep (se 1 (by rfl) ⟨3233654, by rfl⟩ : syracuseStep 4311539 = 6467309) B6467309
theorem B2874359 : Blo 1915435 2874359 := bstep (se 1 (by rfl) ⟨2155769, by rfl⟩ : syracuseStep 2874359 = 4311539) B4311539
theorem B1916239 : Blo 1915435 1916239 := bstep (se 1 (by rfl) ⟨1437179, by rfl⟩ : syracuseStep 1916239 = 2874359) B2874359
theorem B2874365 : Blo 1915435 2874365 := bbase (se 3 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 2874365 = 1077887) (by norm_num)
theorem B1916243 : Blo 1915435 1916243 := bstep (se 1 (by rfl) ⟨1437182, by rfl⟩ : syracuseStep 1916243 = 2874365) B2874365
theorem B4311557 : Blo 1915435 4311557 := bbase (se 4 (by rfl) ⟨404208, by rfl⟩ : syracuseStep 4311557 = 808417) (by norm_num)
theorem B2874371 : Blo 1915435 2874371 := bstep (se 1 (by rfl) ⟨2155778, by rfl⟩ : syracuseStep 2874371 = 4311557) B4311557
theorem B1916247 : Blo 1915435 1916247 := bstep (se 1 (by rfl) ⟨1437185, by rfl⟩ : syracuseStep 1916247 = 2874371) B2874371
theorem B3637885 : Blo 1915435 3637885 := bbase (se 3 (by rfl) ⟨682103, by rfl⟩ : syracuseStep 3637885 = 1364207) (by norm_num)
theorem B4850513 : Blo 1915435 4850513 := bstep (se 2 (by rfl) ⟨1818942, by rfl⟩ : syracuseStep 4850513 = 3637885) B3637885
theorem B3233675 : Blo 1915435 3233675 := bstep (se 1 (by rfl) ⟨2425256, by rfl⟩ : syracuseStep 3233675 = 4850513) B4850513
theorem B2155783 : Blo 1915435 2155783 := bstep (se 1 (by rfl) ⟨1616837, by rfl⟩ : syracuseStep 2155783 = 3233675) B3233675
theorem B2874377 : Blo 1915435 2874377 := bstep (se 2 (by rfl) ⟨1077891, by rfl⟩ : syracuseStep 2874377 = 2155783) B2155783
theorem B1916251 : Blo 1915435 1916251 := bstep (se 1 (by rfl) ⟨1437188, by rfl⟩ : syracuseStep 1916251 = 2874377) B2874377
theorem B9701045 : Blo 1915435 9701045 := bbase (se 5 (by rfl) ⟨454736, by rfl⟩ : syracuseStep 9701045 = 909473) (by norm_num)
theorem B6467363 : Blo 1915435 6467363 := bstep (se 1 (by rfl) ⟨4850522, by rfl⟩ : syracuseStep 6467363 = 9701045) B9701045
theorem B4311575 : Blo 1915435 4311575 := bstep (se 1 (by rfl) ⟨3233681, by rfl⟩ : syracuseStep 4311575 = 6467363) B6467363
theorem B2874383 : Blo 1915435 2874383 := bstep (se 1 (by rfl) ⟨2155787, by rfl⟩ : syracuseStep 2874383 = 4311575) B4311575
theorem B1916255 : Blo 1915435 1916255 := bstep (se 1 (by rfl) ⟨1437191, by rfl⟩ : syracuseStep 1916255 = 2874383) B2874383
theorem B2874389 : Blo 1915435 2874389 := bbase (se 6 (by rfl) ⟨67368, by rfl⟩ : syracuseStep 2874389 = 134737) (by norm_num)
theorem B1916259 : Blo 1915435 1916259 := bstep (se 1 (by rfl) ⟨1437194, by rfl⟩ : syracuseStep 1916259 = 2874389) B2874389
theorem B6906341 : Blo 1915435 6906341 := bbase (se 4 (by rfl) ⟨647469, by rfl⟩ : syracuseStep 6906341 = 1294939) (by norm_num)
theorem B18416909 : Blo 1915435 18416909 := bstep (se 3 (by rfl) ⟨3453170, by rfl⟩ : syracuseStep 18416909 = 6906341) B6906341
theorem B12277939 : Blo 1915435 12277939 := bstep (se 1 (by rfl) ⟨9208454, by rfl⟩ : syracuseStep 12277939 = 18416909) B18416909
theorem B16370585 : Blo 1915435 16370585 := bstep (se 2 (by rfl) ⟨6138969, by rfl⟩ : syracuseStep 16370585 = 12277939) B12277939
theorem B10913723 : Blo 1915435 10913723 := bstep (se 1 (by rfl) ⟨8185292, by rfl⟩ : syracuseStep 10913723 = 16370585) B16370585
theorem B7275815 : Blo 1915435 7275815 := bstep (se 1 (by rfl) ⟨5456861, by rfl⟩ : syracuseStep 7275815 = 10913723) B10913723
theorem B4850543 : Blo 1915435 4850543 := bstep (se 1 (by rfl) ⟨3637907, by rfl⟩ : syracuseStep 4850543 = 7275815) B7275815
theorem B3233695 : Blo 1915435 3233695 := bstep (se 1 (by rfl) ⟨2425271, by rfl⟩ : syracuseStep 3233695 = 4850543) B4850543
theorem B4311593 : Blo 1915435 4311593 := bstep (se 2 (by rfl) ⟨1616847, by rfl⟩ : syracuseStep 4311593 = 3233695) B3233695
theorem B2874395 : Blo 1915435 2874395 := bstep (se 1 (by rfl) ⟨2155796, by rfl⟩ : syracuseStep 2874395 = 4311593) B4311593
theorem B1916263 : Blo 1915435 1916263 := bstep (se 1 (by rfl) ⟨1437197, by rfl⟩ : syracuseStep 1916263 = 2874395) B2874395
theorem B2155801 : Blo 1915435 2155801 := bbase (se 2 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 2155801 = 1616851) (by norm_num)
theorem B2874401 : Blo 1915435 2874401 := bstep (se 2 (by rfl) ⟨1077900, by rfl⟩ : syracuseStep 2874401 = 2155801) B2155801
theorem B1916267 : Blo 1915435 1916267 := bstep (se 1 (by rfl) ⟨1437200, by rfl⟩ : syracuseStep 1916267 = 2874401) B2874401
theorem B7275845 : Blo 1915435 7275845 := bbase (se 4 (by rfl) ⟨682110, by rfl⟩ : syracuseStep 7275845 = 1364221) (by norm_num)
theorem B4850563 : Blo 1915435 4850563 := bstep (se 1 (by rfl) ⟨3637922, by rfl⟩ : syracuseStep 4850563 = 7275845) B7275845
theorem B6467417 : Blo 1915435 6467417 := bstep (se 2 (by rfl) ⟨2425281, by rfl⟩ : syracuseStep 6467417 = 4850563) B4850563
theorem B4311611 : Blo 1915435 4311611 := bstep (se 1 (by rfl) ⟨3233708, by rfl⟩ : syracuseStep 4311611 = 6467417) B6467417
theorem B2874407 : Blo 1915435 2874407 := bstep (se 1 (by rfl) ⟨2155805, by rfl⟩ : syracuseStep 2874407 = 4311611) B4311611
theorem B1916271 : Blo 1915435 1916271 := bstep (se 1 (by rfl) ⟨1437203, by rfl⟩ : syracuseStep 1916271 = 2874407) B2874407
theorem B2874413 : Blo 1915435 2874413 := bbase (se 3 (by rfl) ⟨538952, by rfl⟩ : syracuseStep 2874413 = 1077905) (by norm_num)
theorem B1916275 : Blo 1915435 1916275 := bstep (se 1 (by rfl) ⟨1437206, by rfl⟩ : syracuseStep 1916275 = 2874413) B2874413
theorem B4311629 : Blo 1915435 4311629 := bbase (se 3 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 4311629 = 1616861) (by norm_num)
theorem B2874419 : Blo 1915435 2874419 := bstep (se 1 (by rfl) ⟨2155814, by rfl⟩ : syracuseStep 2874419 = 4311629) B4311629
theorem B1916279 : Blo 1915435 1916279 := bstep (se 1 (by rfl) ⟨1437209, by rfl⟩ : syracuseStep 1916279 = 2874419) B2874419
theorem B2425297 : Blo 1915435 2425297 := bbase (se 2 (by rfl) ⟨909486, by rfl⟩ : syracuseStep 2425297 = 1818973) (by norm_num)
theorem B3233729 : Blo 1915435 3233729 := bstep (se 2 (by rfl) ⟨1212648, by rfl⟩ : syracuseStep 3233729 = 2425297) B2425297
theorem B2155819 : Blo 1915435 2155819 := bstep (se 1 (by rfl) ⟨1616864, by rfl⟩ : syracuseStep 2155819 = 3233729) B3233729
theorem B2874425 : Blo 1915435 2874425 := bstep (se 2 (by rfl) ⟨1077909, by rfl⟩ : syracuseStep 2874425 = 2155819) B2155819
theorem B1916283 : Blo 1915435 1916283 := bstep (se 1 (by rfl) ⟨1437212, by rfl⟩ : syracuseStep 1916283 = 2874425) B2874425
theorem B4604285 : Blo 1915435 4604285 := bbase (se 3 (by rfl) ⟨863303, by rfl⟩ : syracuseStep 4604285 = 1726607) (by norm_num)
theorem B3069523 : Blo 1915435 3069523 := bstep (se 1 (by rfl) ⟨2302142, by rfl⟩ : syracuseStep 3069523 = 4604285) B4604285
theorem B4092697 : Blo 1915435 4092697 := bstep (se 2 (by rfl) ⟨1534761, by rfl⟩ : syracuseStep 4092697 = 3069523) B3069523
theorem B21827717 : Blo 1915435 21827717 := bstep (se 4 (by rfl) ⟨2046348, by rfl⟩ : syracuseStep 21827717 = 4092697) B4092697
theorem B14551811 : Blo 1915435 14551811 := bstep (se 1 (by rfl) ⟨10913858, by rfl⟩ : syracuseStep 14551811 = 21827717) B21827717
theorem B9701207 : Blo 1915435 9701207 := bstep (se 1 (by rfl) ⟨7275905, by rfl⟩ : syracuseStep 9701207 = 14551811) B14551811
theorem B6467471 : Blo 1915435 6467471 := bstep (se 1 (by rfl) ⟨4850603, by rfl⟩ : syracuseStep 6467471 = 9701207) B9701207
theorem B4311647 : Blo 1915435 4311647 := bstep (se 1 (by rfl) ⟨3233735, by rfl⟩ : syracuseStep 4311647 = 6467471) B6467471
theorem B2874431 : Blo 1915435 2874431 := bstep (se 1 (by rfl) ⟨2155823, by rfl⟩ : syracuseStep 2874431 = 4311647) B4311647
theorem B1916287 : Blo 1915435 1916287 := bstep (se 1 (by rfl) ⟨1437215, by rfl⟩ : syracuseStep 1916287 = 2874431) B2874431
theorem B2874437 : Blo 1915435 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B1916291 : Blo 1915435 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B3233749 : Blo 1915435 3233749 := bbase (se 7 (by rfl) ⟨37895, by rfl⟩ : syracuseStep 3233749 = 75791) (by norm_num)
theorem B4311665 : Blo 1915435 4311665 := bstep (se 2 (by rfl) ⟨1616874, by rfl⟩ : syracuseStep 4311665 = 3233749) B3233749
theorem B2874443 : Blo 1915435 2874443 := bstep (se 1 (by rfl) ⟨2155832, by rfl⟩ : syracuseStep 2874443 = 4311665) B4311665
theorem B1916295 : Blo 1915435 1916295 := bstep (se 1 (by rfl) ⟨1437221, by rfl⟩ : syracuseStep 1916295 = 2874443) B2874443
theorem B2155837 : Blo 1915435 2155837 := bbase (se 3 (by rfl) ⟨404219, by rfl⟩ : syracuseStep 2155837 = 808439) (by norm_num)
theorem B2874449 : Blo 1915435 2874449 := bstep (se 2 (by rfl) ⟨1077918, by rfl⟩ : syracuseStep 2874449 = 2155837) B2155837
theorem B1916299 : Blo 1915435 1916299 := bstep (se 1 (by rfl) ⟨1437224, by rfl⟩ : syracuseStep 1916299 = 2874449) B2874449
theorem B6467525 : Blo 1915435 6467525 := bbase (se 4 (by rfl) ⟨606330, by rfl⟩ : syracuseStep 6467525 = 1212661) (by norm_num)
theorem B4311683 : Blo 1915435 4311683 := bstep (se 1 (by rfl) ⟨3233762, by rfl⟩ : syracuseStep 4311683 = 6467525) B6467525
theorem B2874455 : Blo 1915435 2874455 := bstep (se 1 (by rfl) ⟨2155841, by rfl⟩ : syracuseStep 2874455 = 4311683) B4311683
theorem B1916303 : Blo 1915435 1916303 := bstep (se 1 (by rfl) ⟨1437227, by rfl⟩ : syracuseStep 1916303 = 2874455) B2874455
theorem B2874461 : Blo 1915435 2874461 := bbase (se 3 (by rfl) ⟨538961, by rfl⟩ : syracuseStep 2874461 = 1077923) (by norm_num)
theorem B1916307 : Blo 1915435 1916307 := bstep (se 1 (by rfl) ⟨1437230, by rfl⟩ : syracuseStep 1916307 = 2874461) B2874461
theorem B4311701 : Blo 1915435 4311701 := bbase (se 6 (by rfl) ⟨101055, by rfl⟩ : syracuseStep 4311701 = 202111) (by norm_num)
theorem B2874467 : Blo 1915435 2874467 := bstep (se 1 (by rfl) ⟨2155850, by rfl⟩ : syracuseStep 2874467 = 4311701) B4311701
theorem B1916311 : Blo 1915435 1916311 := bstep (se 1 (by rfl) ⟨1437233, by rfl⟩ : syracuseStep 1916311 = 2874467) B2874467
theorem B2302177 : Blo 1915435 2302177 := bbase (se 2 (by rfl) ⟨863316, by rfl⟩ : syracuseStep 2302177 = 1726633) (by norm_num)
theorem B3069569 : Blo 1915435 3069569 := bstep (se 2 (by rfl) ⟨1151088, by rfl⟩ : syracuseStep 3069569 = 2302177) B2302177
theorem B2046379 : Blo 1915435 2046379 := bstep (se 1 (by rfl) ⟨1534784, by rfl⟩ : syracuseStep 2046379 = 3069569) B3069569
theorem B2728505 : Blo 1915435 2728505 := bstep (se 2 (by rfl) ⟨1023189, by rfl⟩ : syracuseStep 2728505 = 2046379) B2046379
theorem B7276013 : Blo 1915435 7276013 := bstep (se 3 (by rfl) ⟨1364252, by rfl⟩ : syracuseStep 7276013 = 2728505) B2728505
theorem B4850675 : Blo 1915435 4850675 := bstep (se 1 (by rfl) ⟨3638006, by rfl⟩ : syracuseStep 4850675 = 7276013) B7276013
theorem B3233783 : Blo 1915435 3233783 := bstep (se 1 (by rfl) ⟨2425337, by rfl⟩ : syracuseStep 3233783 = 4850675) B4850675
theorem B2155855 : Blo 1915435 2155855 := bstep (se 1 (by rfl) ⟨1616891, by rfl⟩ : syracuseStep 2155855 = 3233783) B3233783
theorem B2874473 : Blo 1915435 2874473 := bstep (se 2 (by rfl) ⟨1077927, by rfl⟩ : syracuseStep 2874473 = 2155855) B2155855
theorem B1916315 : Blo 1915435 1916315 := bstep (se 1 (by rfl) ⟨1437236, by rfl⟩ : syracuseStep 1916315 = 2874473) B2874473
theorem B7769861 : Blo 1915435 7769861 := bbase (se 4 (by rfl) ⟨728424, by rfl⟩ : syracuseStep 7769861 = 1456849) (by norm_num)
theorem B5179907 : Blo 1915435 5179907 := bstep (se 1 (by rfl) ⟨3884930, by rfl⟩ : syracuseStep 5179907 = 7769861) B7769861
theorem B13813085 : Blo 1915435 13813085 := bstep (se 3 (by rfl) ⟨2589953, by rfl⟩ : syracuseStep 13813085 = 5179907) B5179907
theorem B9208723 : Blo 1915435 9208723 := bstep (se 1 (by rfl) ⟨6906542, by rfl⟩ : syracuseStep 9208723 = 13813085) B13813085
theorem B12278297 : Blo 1915435 12278297 := bstep (se 2 (by rfl) ⟨4604361, by rfl⟩ : syracuseStep 12278297 = 9208723) B9208723
theorem B8185531 : Blo 1915435 8185531 := bstep (se 1 (by rfl) ⟨6139148, by rfl⟩ : syracuseStep 8185531 = 12278297) B12278297
theorem B10914041 : Blo 1915435 10914041 := bstep (se 2 (by rfl) ⟨4092765, by rfl⟩ : syracuseStep 10914041 = 8185531) B8185531
theorem B7276027 : Blo 1915435 7276027 := bstep (se 1 (by rfl) ⟨5457020, by rfl⟩ : syracuseStep 7276027 = 10914041) B10914041
theorem B9701369 : Blo 1915435 9701369 := bstep (se 2 (by rfl) ⟨3638013, by rfl⟩ : syracuseStep 9701369 = 7276027) B7276027
theorem B6467579 : Blo 1915435 6467579 := bstep (se 1 (by rfl) ⟨4850684, by rfl⟩ : syracuseStep 6467579 = 9701369) B9701369
theorem B4311719 : Blo 1915435 4311719 := bstep (se 1 (by rfl) ⟨3233789, by rfl⟩ : syracuseStep 4311719 = 6467579) B6467579
theorem B2874479 : Blo 1915435 2874479 := bstep (se 1 (by rfl) ⟨2155859, by rfl⟩ : syracuseStep 2874479 = 4311719) B4311719
theorem B1916319 : Blo 1915435 1916319 := bstep (se 1 (by rfl) ⟨1437239, by rfl⟩ : syracuseStep 1916319 = 2874479) B2874479
theorem B2874485 : Blo 1915435 2874485 := bbase (se 5 (by rfl) ⟨134741, by rfl⟩ : syracuseStep 2874485 = 269483) (by norm_num)
theorem B1916323 : Blo 1915435 1916323 := bstep (se 1 (by rfl) ⟨1437242, by rfl⟩ : syracuseStep 1916323 = 2874485) B2874485
theorem B3638029 : Blo 1915435 3638029 := bbase (se 3 (by rfl) ⟨682130, by rfl⟩ : syracuseStep 3638029 = 1364261) (by norm_num)
theorem B4850705 : Blo 1915435 4850705 := bstep (se 2 (by rfl) ⟨1819014, by rfl⟩ : syracuseStep 4850705 = 3638029) B3638029
theorem B3233803 : Blo 1915435 3233803 := bstep (se 1 (by rfl) ⟨2425352, by rfl⟩ : syracuseStep 3233803 = 4850705) B4850705
theorem B4311737 : Blo 1915435 4311737 := bstep (se 2 (by rfl) ⟨1616901, by rfl⟩ : syracuseStep 4311737 = 3233803) B3233803
theorem B2874491 : Blo 1915435 2874491 := bstep (se 1 (by rfl) ⟨2155868, by rfl⟩ : syracuseStep 2874491 = 4311737) B4311737
theorem B1916327 : Blo 1915435 1916327 := bstep (se 1 (by rfl) ⟨1437245, by rfl⟩ : syracuseStep 1916327 = 2874491) B2874491
theorem B2155873 : Blo 1915435 2155873 := bbase (se 2 (by rfl) ⟨808452, by rfl⟩ : syracuseStep 2155873 = 1616905) (by norm_num)
theorem B2874497 : Blo 1915435 2874497 := bstep (se 2 (by rfl) ⟨1077936, by rfl⟩ : syracuseStep 2874497 = 2155873) B2155873
theorem B1916331 : Blo 1915435 1916331 := bstep (se 1 (by rfl) ⟨1437248, by rfl⟩ : syracuseStep 1916331 = 2874497) B2874497
theorem B4850725 : Blo 1915435 4850725 := bbase (se 4 (by rfl) ⟨454755, by rfl⟩ : syracuseStep 4850725 = 909511) (by norm_num)
theorem B6467633 : Blo 1915435 6467633 := bstep (se 2 (by rfl) ⟨2425362, by rfl⟩ : syracuseStep 6467633 = 4850725) B4850725
theorem B4311755 : Blo 1915435 4311755 := bstep (se 1 (by rfl) ⟨3233816, by rfl⟩ : syracuseStep 4311755 = 6467633) B6467633
theorem B2874503 : Blo 1915435 2874503 := bstep (se 1 (by rfl) ⟨2155877, by rfl⟩ : syracuseStep 2874503 = 4311755) B4311755
theorem B1916335 : Blo 1915435 1916335 := bstep (se 1 (by rfl) ⟨1437251, by rfl⟩ : syracuseStep 1916335 = 2874503) B2874503
theorem B2874509 : Blo 1915435 2874509 := bbase (se 3 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 2874509 = 1077941) (by norm_num)
theorem B1916339 : Blo 1915435 1916339 := bstep (se 1 (by rfl) ⟨1437254, by rfl⟩ : syracuseStep 1916339 = 2874509) B2874509
theorem B4311773 : Blo 1915435 4311773 := bbase (se 3 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 4311773 = 1616915) (by norm_num)
theorem B2874515 : Blo 1915435 2874515 := bstep (se 1 (by rfl) ⟨2155886, by rfl⟩ : syracuseStep 2874515 = 4311773) B4311773
theorem B1916343 : Blo 1915435 1916343 := bstep (se 1 (by rfl) ⟨1437257, by rfl⟩ : syracuseStep 1916343 = 2874515) B2874515
theorem B3233837 : Blo 1915435 3233837 := bbase (se 3 (by rfl) ⟨606344, by rfl⟩ : syracuseStep 3233837 = 1212689) (by norm_num)
theorem B2155891 : Blo 1915435 2155891 := bstep (se 1 (by rfl) ⟨1616918, by rfl⟩ : syracuseStep 2155891 = 3233837) B3233837
theorem B2874521 : Blo 1915435 2874521 := bstep (se 2 (by rfl) ⟨1077945, by rfl⟩ : syracuseStep 2874521 = 2155891) B2155891
theorem B1916347 : Blo 1915435 1916347 := bstep (se 1 (by rfl) ⟨1437260, by rfl⟩ : syracuseStep 1916347 = 2874521) B2874521
theorem B5827493 : Blo 1915435 5827493 := bbase (se 4 (by rfl) ⟨546327, by rfl⟩ : syracuseStep 5827493 = 1092655) (by norm_num)
theorem B3884995 : Blo 1915435 3884995 := bstep (se 1 (by rfl) ⟨2913746, by rfl⟩ : syracuseStep 3884995 = 5827493) B5827493
theorem B5179993 : Blo 1915435 5179993 := bstep (se 2 (by rfl) ⟨1942497, by rfl⟩ : syracuseStep 5179993 = 3884995) B3884995
theorem B27626629 : Blo 1915435 27626629 := bstep (se 4 (by rfl) ⟨2589996, by rfl⟩ : syracuseStep 27626629 = 5179993) B5179993
theorem B36835505 : Blo 1915435 36835505 := bstep (se 2 (by rfl) ⟨13813314, by rfl⟩ : syracuseStep 36835505 = 27626629) B27626629
theorem B24557003 : Blo 1915435 24557003 := bstep (se 1 (by rfl) ⟨18417752, by rfl⟩ : syracuseStep 24557003 = 36835505) B36835505
theorem B16371335 : Blo 1915435 16371335 := bstep (se 1 (by rfl) ⟨12278501, by rfl⟩ : syracuseStep 16371335 = 24557003) B24557003
theorem B10914223 : Blo 1915435 10914223 := bstep (se 1 (by rfl) ⟨8185667, by rfl⟩ : syracuseStep 10914223 = 16371335) B16371335
theorem B14552297 : Blo 1915435 14552297 := bstep (se 2 (by rfl) ⟨5457111, by rfl⟩ : syracuseStep 14552297 = 10914223) B10914223
theorem B9701531 : Blo 1915435 9701531 := bstep (se 1 (by rfl) ⟨7276148, by rfl⟩ : syracuseStep 9701531 = 14552297) B14552297
theorem B6467687 : Blo 1915435 6467687 := bstep (se 1 (by rfl) ⟨4850765, by rfl⟩ : syracuseStep 6467687 = 9701531) B9701531
theorem B4311791 : Blo 1915435 4311791 := bstep (se 1 (by rfl) ⟨3233843, by rfl⟩ : syracuseStep 4311791 = 6467687) B6467687
theorem B2874527 : Blo 1915435 2874527 := bstep (se 1 (by rfl) ⟨2155895, by rfl⟩ : syracuseStep 2874527 = 4311791) B4311791
theorem B1916351 : Blo 1915435 1916351 := bstep (se 1 (by rfl) ⟨1437263, by rfl⟩ : syracuseStep 1916351 = 2874527) B2874527
theorem B2874533 : Blo 1915435 2874533 := bbase (se 4 (by rfl) ⟨269487, by rfl⟩ : syracuseStep 2874533 = 538975) (by norm_num)
theorem B1916355 : Blo 1915435 1916355 := bstep (se 1 (by rfl) ⟨1437266, by rfl⟩ : syracuseStep 1916355 = 2874533) B2874533
theorem B2425393 : Blo 1915435 2425393 := bbase (se 2 (by rfl) ⟨909522, by rfl⟩ : syracuseStep 2425393 = 1819045) (by norm_num)
theorem B3233857 : Blo 1915435 3233857 := bstep (se 2 (by rfl) ⟨1212696, by rfl⟩ : syracuseStep 3233857 = 2425393) B2425393
theorem B4311809 : Blo 1915435 4311809 := bstep (se 2 (by rfl) ⟨1616928, by rfl⟩ : syracuseStep 4311809 = 3233857) B3233857
theorem B2874539 : Blo 1915435 2874539 := bstep (se 1 (by rfl) ⟨2155904, by rfl⟩ : syracuseStep 2874539 = 4311809) B4311809
theorem B1916359 : Blo 1915435 1916359 := bstep (se 1 (by rfl) ⟨1437269, by rfl⟩ : syracuseStep 1916359 = 2874539) B2874539
theorem B2155909 : Blo 1915435 2155909 := bbase (se 4 (by rfl) ⟨202116, by rfl⟩ : syracuseStep 2155909 = 404233) (by norm_num)
theorem B2874545 : Blo 1915435 2874545 := bstep (se 2 (by rfl) ⟨1077954, by rfl⟩ : syracuseStep 2874545 = 2155909) B2155909
theorem B1916363 : Blo 1915435 1916363 := bstep (se 1 (by rfl) ⟨1437272, by rfl⟩ : syracuseStep 1916363 = 2874545) B2874545
theorem B4092869 : Blo 1915435 4092869 := bbase (se 4 (by rfl) ⟨383706, by rfl⟩ : syracuseStep 4092869 = 767413) (by norm_num)
theorem B2728579 : Blo 1915435 2728579 := bstep (se 1 (by rfl) ⟨2046434, by rfl⟩ : syracuseStep 2728579 = 4092869) B4092869
theorem B3638105 : Blo 1915435 3638105 := bstep (se 2 (by rfl) ⟨1364289, by rfl⟩ : syracuseStep 3638105 = 2728579) B2728579
theorem B2425403 : Blo 1915435 2425403 := bstep (se 1 (by rfl) ⟨1819052, by rfl⟩ : syracuseStep 2425403 = 3638105) B3638105
theorem B6467741 : Blo 1915435 6467741 := bstep (se 3 (by rfl) ⟨1212701, by rfl⟩ : syracuseStep 6467741 = 2425403) B2425403
theorem B4311827 : Blo 1915435 4311827 := bstep (se 1 (by rfl) ⟨3233870, by rfl⟩ : syracuseStep 4311827 = 6467741) B6467741
theorem B2874551 : Blo 1915435 2874551 := bstep (se 1 (by rfl) ⟨2155913, by rfl⟩ : syracuseStep 2874551 = 4311827) B4311827
theorem B1916367 : Blo 1915435 1916367 := bstep (se 1 (by rfl) ⟨1437275, by rfl⟩ : syracuseStep 1916367 = 2874551) B2874551
theorem B2874557 : Blo 1915435 2874557 := bbase (se 3 (by rfl) ⟨538979, by rfl⟩ : syracuseStep 2874557 = 1077959) (by norm_num)
theorem B1916371 : Blo 1915435 1916371 := bstep (se 1 (by rfl) ⟨1437278, by rfl⟩ : syracuseStep 1916371 = 2874557) B2874557
theorem B4311845 : Blo 1915435 4311845 := bbase (se 4 (by rfl) ⟨404235, by rfl⟩ : syracuseStep 4311845 = 808471) (by norm_num)
theorem B2874563 : Blo 1915435 2874563 := bstep (se 1 (by rfl) ⟨2155922, by rfl⟩ : syracuseStep 2874563 = 4311845) B4311845
theorem B1916375 : Blo 1915435 1916375 := bstep (se 1 (by rfl) ⟨1437281, by rfl⟩ : syracuseStep 1916375 = 2874563) B2874563
theorem B4850837 : Blo 1915435 4850837 := bbase (se 6 (by rfl) ⟨113691, by rfl⟩ : syracuseStep 4850837 = 227383) (by norm_num)
theorem B3233891 : Blo 1915435 3233891 := bstep (se 1 (by rfl) ⟨2425418, by rfl⟩ : syracuseStep 3233891 = 4850837) B4850837
theorem B2155927 : Blo 1915435 2155927 := bstep (se 1 (by rfl) ⟨1616945, by rfl⟩ : syracuseStep 2155927 = 3233891) B3233891
theorem B2874569 : Blo 1915435 2874569 := bstep (se 2 (by rfl) ⟨1077963, by rfl⟩ : syracuseStep 2874569 = 2155927) B2155927
theorem B1916379 : Blo 1915435 1916379 := bstep (se 1 (by rfl) ⟨1437284, by rfl⟩ : syracuseStep 1916379 = 2874569) B2874569
theorem B3069677 : Blo 1915435 3069677 := bbase (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) (by norm_num)
theorem B8185805 : Blo 1915435 8185805 := bstep (se 3 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 8185805 = 3069677) B3069677
theorem B5457203 : Blo 1915435 5457203 := bstep (se 1 (by rfl) ⟨4092902, by rfl⟩ : syracuseStep 5457203 = 8185805) B8185805
theorem B3638135 : Blo 1915435 3638135 := bstep (se 1 (by rfl) ⟨2728601, by rfl⟩ : syracuseStep 3638135 = 5457203) B5457203
theorem B9701693 : Blo 1915435 9701693 := bstep (se 3 (by rfl) ⟨1819067, by rfl⟩ : syracuseStep 9701693 = 3638135) B3638135
theorem B6467795 : Blo 1915435 6467795 := bstep (se 1 (by rfl) ⟨4850846, by rfl⟩ : syracuseStep 6467795 = 9701693) B9701693
theorem B4311863 : Blo 1915435 4311863 := bstep (se 1 (by rfl) ⟨3233897, by rfl⟩ : syracuseStep 4311863 = 6467795) B6467795
theorem B2874575 : Blo 1915435 2874575 := bstep (se 1 (by rfl) ⟨2155931, by rfl⟩ : syracuseStep 2874575 = 4311863) B4311863
theorem B1916383 : Blo 1915435 1916383 := bstep (se 1 (by rfl) ⟨1437287, by rfl⟩ : syracuseStep 1916383 = 2874575) B2874575
theorem B2874581 : Blo 1915435 2874581 := bbase (se 7 (by rfl) ⟨33686, by rfl⟩ : syracuseStep 2874581 = 67373) (by norm_num)
theorem B1916387 : Blo 1915435 1916387 := bstep (se 1 (by rfl) ⟨1437290, by rfl⟩ : syracuseStep 1916387 = 2874581) B2874581
theorem B2728613 : Blo 1915435 2728613 := bbase (se 4 (by rfl) ⟨255807, by rfl⟩ : syracuseStep 2728613 = 511615) (by norm_num)
theorem B7276301 : Blo 1915435 7276301 := bstep (se 3 (by rfl) ⟨1364306, by rfl⟩ : syracuseStep 7276301 = 2728613) B2728613
theorem B4850867 : Blo 1915435 4850867 := bstep (se 1 (by rfl) ⟨3638150, by rfl⟩ : syracuseStep 4850867 = 7276301) B7276301
theorem B3233911 : Blo 1915435 3233911 := bstep (se 1 (by rfl) ⟨2425433, by rfl⟩ : syracuseStep 3233911 = 4850867) B4850867
theorem B4311881 : Blo 1915435 4311881 := bstep (se 2 (by rfl) ⟨1616955, by rfl⟩ : syracuseStep 4311881 = 3233911) B3233911
theorem B2874587 : Blo 1915435 2874587 := bstep (se 1 (by rfl) ⟨2155940, by rfl⟩ : syracuseStep 2874587 = 4311881) B4311881
theorem B1916391 : Blo 1915435 1916391 := bstep (se 1 (by rfl) ⟨1437293, by rfl⟩ : syracuseStep 1916391 = 2874587) B2874587
theorem B2155945 : Blo 1915435 2155945 := bbase (se 2 (by rfl) ⟨808479, by rfl⟩ : syracuseStep 2155945 = 1616959) (by norm_num)
theorem B2874593 : Blo 1915435 2874593 := bstep (se 2 (by rfl) ⟨1077972, by rfl⟩ : syracuseStep 2874593 = 2155945) B2155945
theorem B1916395 : Blo 1915435 1916395 := bstep (se 1 (by rfl) ⟨1437296, by rfl⟩ : syracuseStep 1916395 = 2874593) B2874593
theorem B2302277 : Blo 1915435 2302277 := bbase (se 4 (by rfl) ⟨215838, by rfl⟩ : syracuseStep 2302277 = 431677) (by norm_num)
theorem B6139405 : Blo 1915435 6139405 := bstep (se 3 (by rfl) ⟨1151138, by rfl⟩ : syracuseStep 6139405 = 2302277) B2302277
theorem B8185873 : Blo 1915435 8185873 := bstep (se 2 (by rfl) ⟨3069702, by rfl⟩ : syracuseStep 8185873 = 6139405) B6139405
theorem B10914497 : Blo 1915435 10914497 := bstep (se 2 (by rfl) ⟨4092936, by rfl⟩ : syracuseStep 10914497 = 8185873) B8185873
theorem B7276331 : Blo 1915435 7276331 := bstep (se 1 (by rfl) ⟨5457248, by rfl⟩ : syracuseStep 7276331 = 10914497) B10914497
theorem B4850887 : Blo 1915435 4850887 := bstep (se 1 (by rfl) ⟨3638165, by rfl⟩ : syracuseStep 4850887 = 7276331) B7276331
theorem B6467849 : Blo 1915435 6467849 := bstep (se 2 (by rfl) ⟨2425443, by rfl⟩ : syracuseStep 6467849 = 4850887) B4850887
theorem B4311899 : Blo 1915435 4311899 := bstep (se 1 (by rfl) ⟨3233924, by rfl⟩ : syracuseStep 4311899 = 6467849) B6467849
theorem B2874599 : Blo 1915435 2874599 := bstep (se 1 (by rfl) ⟨2155949, by rfl⟩ : syracuseStep 2874599 = 4311899) B4311899
theorem B1916399 : Blo 1915435 1916399 := bstep (se 1 (by rfl) ⟨1437299, by rfl⟩ : syracuseStep 1916399 = 2874599) B2874599
theorem B2874605 : Blo 1915435 2874605 := bbase (se 3 (by rfl) ⟨538988, by rfl⟩ : syracuseStep 2874605 = 1077977) (by norm_num)
theorem B1916403 : Blo 1915435 1916403 := bstep (se 1 (by rfl) ⟨1437302, by rfl⟩ : syracuseStep 1916403 = 2874605) B2874605
theorem B4311917 : Blo 1915435 4311917 := bbase (se 3 (by rfl) ⟨808484, by rfl⟩ : syracuseStep 4311917 = 1616969) (by norm_num)
theorem B2874611 : Blo 1915435 2874611 := bstep (se 1 (by rfl) ⟨2155958, by rfl⟩ : syracuseStep 2874611 = 4311917) B4311917
theorem B1916407 : Blo 1915435 1916407 := bstep (se 1 (by rfl) ⟨1437305, by rfl⟩ : syracuseStep 1916407 = 2874611) B2874611
theorem B3638189 : Blo 1915435 3638189 := bbase (se 3 (by rfl) ⟨682160, by rfl⟩ : syracuseStep 3638189 = 1364321) (by norm_num)
theorem B2425459 : Blo 1915435 2425459 := bstep (se 1 (by rfl) ⟨1819094, by rfl⟩ : syracuseStep 2425459 = 3638189) B3638189
theorem B3233945 : Blo 1915435 3233945 := bstep (se 2 (by rfl) ⟨1212729, by rfl⟩ : syracuseStep 3233945 = 2425459) B2425459
theorem B2155963 : Blo 1915435 2155963 := bstep (se 1 (by rfl) ⟨1616972, by rfl⟩ : syracuseStep 2155963 = 3233945) B3233945
theorem B2874617 : Blo 1915435 2874617 := bstep (se 2 (by rfl) ⟨1077981, by rfl⟩ : syracuseStep 2874617 = 2155963) B2155963
theorem B1916411 : Blo 1915435 1916411 := bstep (se 1 (by rfl) ⟨1437308, by rfl⟩ : syracuseStep 1916411 = 2874617) B2874617
theorem B7876261 : Blo 1915435 7876261 := bbase (se 4 (by rfl) ⟨738399, by rfl⟩ : syracuseStep 7876261 = 1476799) (by norm_num)
theorem B42006725 : Blo 1915435 42006725 := bstep (se 4 (by rfl) ⟨3938130, by rfl⟩ : syracuseStep 42006725 = 7876261) B7876261
theorem B28004483 : Blo 1915435 28004483 := bstep (se 1 (by rfl) ⟨21003362, by rfl⟩ : syracuseStep 28004483 = 42006725) B42006725
theorem B18669655 : Blo 1915435 18669655 := bstep (se 1 (by rfl) ⟨14002241, by rfl⟩ : syracuseStep 18669655 = 28004483) B28004483
theorem B99571493 : Blo 1915435 99571493 := bstep (se 4 (by rfl) ⟨9334827, by rfl⟩ : syracuseStep 99571493 = 18669655) B18669655
theorem B66380995 : Blo 1915435 66380995 := bstep (se 1 (by rfl) ⟨49785746, by rfl⟩ : syracuseStep 66380995 = 99571493) B99571493
theorem B88507993 : Blo 1915435 88507993 := bstep (se 2 (by rfl) ⟨33190497, by rfl⟩ : syracuseStep 88507993 = 66380995) B66380995
theorem B118010657 : Blo 1915435 118010657 := bstep (se 2 (by rfl) ⟨44253996, by rfl⟩ : syracuseStep 118010657 = 88507993) B88507993
theorem B78673771 : Blo 1915435 78673771 := bstep (se 1 (by rfl) ⟨59005328, by rfl⟩ : syracuseStep 78673771 = 118010657) B118010657
theorem B104898361 : Blo 1915435 104898361 := bstep (se 2 (by rfl) ⟨39336885, by rfl⟩ : syracuseStep 104898361 = 78673771) B78673771
theorem B139864481 : Blo 1915435 139864481 := bstep (se 2 (by rfl) ⟨52449180, by rfl⟩ : syracuseStep 139864481 = 104898361) B104898361
theorem B93242987 : Blo 1915435 93242987 := bstep (se 1 (by rfl) ⟨69932240, by rfl⟩ : syracuseStep 93242987 = 139864481) B139864481
theorem B62161991 : Blo 1915435 62161991 := bstep (se 1 (by rfl) ⟨46621493, by rfl⟩ : syracuseStep 62161991 = 93242987) B93242987
theorem B41441327 : Blo 1915435 41441327 := bstep (se 1 (by rfl) ⟨31080995, by rfl⟩ : syracuseStep 41441327 = 62161991) B62161991
theorem B27627551 : Blo 1915435 27627551 := bstep (se 1 (by rfl) ⟨20720663, by rfl⟩ : syracuseStep 27627551 = 41441327) B41441327
theorem B18418367 : Blo 1915435 18418367 := bstep (se 1 (by rfl) ⟨13813775, by rfl⟩ : syracuseStep 18418367 = 27627551) B27627551
theorem B49115645 : Blo 1915435 49115645 := bstep (se 3 (by rfl) ⟨9209183, by rfl⟩ : syracuseStep 49115645 = 18418367) B18418367
theorem B32743763 : Blo 1915435 32743763 := bstep (se 1 (by rfl) ⟨24557822, by rfl⟩ : syracuseStep 32743763 = 49115645) B49115645
theorem B21829175 : Blo 1915435 21829175 := bstep (se 1 (by rfl) ⟨16371881, by rfl⟩ : syracuseStep 21829175 = 32743763) B32743763
theorem B14552783 : Blo 1915435 14552783 := bstep (se 1 (by rfl) ⟨10914587, by rfl⟩ : syracuseStep 14552783 = 21829175) B21829175
theorem B9701855 : Blo 1915435 9701855 := bstep (se 1 (by rfl) ⟨7276391, by rfl⟩ : syracuseStep 9701855 = 14552783) B14552783
theorem B6467903 : Blo 1915435 6467903 := bstep (se 1 (by rfl) ⟨4850927, by rfl⟩ : syracuseStep 6467903 = 9701855) B9701855
theorem B4311935 : Blo 1915435 4311935 := bstep (se 1 (by rfl) ⟨3233951, by rfl⟩ : syracuseStep 4311935 = 6467903) B6467903
theorem B2874623 : Blo 1915435 2874623 := bstep (se 1 (by rfl) ⟨2155967, by rfl⟩ : syracuseStep 2874623 = 4311935) B4311935
theorem B1916415 : Blo 1915435 1916415 := bstep (se 1 (by rfl) ⟨1437311, by rfl⟩ : syracuseStep 1916415 = 2874623) B2874623
theorem B2874629 : Blo 1915435 2874629 := bbase (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) (by norm_num)
theorem B1916419 : Blo 1915435 1916419 := bstep (se 1 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 1916419 = 2874629) B2874629
theorem B3233965 : Blo 1915435 3233965 := bbase (se 3 (by rfl) ⟨606368, by rfl⟩ : syracuseStep 3233965 = 1212737) (by norm_num)
theorem B4311953 : Blo 1915435 4311953 := bstep (se 2 (by rfl) ⟨1616982, by rfl⟩ : syracuseStep 4311953 = 3233965) B3233965
theorem B2874635 : Blo 1915435 2874635 := bstep (se 1 (by rfl) ⟨2155976, by rfl⟩ : syracuseStep 2874635 = 4311953) B4311953
theorem B1916423 : Blo 1915435 1916423 := bstep (se 1 (by rfl) ⟨1437317, by rfl⟩ : syracuseStep 1916423 = 2874635) B2874635
theorem B2155981 : Blo 1915435 2155981 := bbase (se 3 (by rfl) ⟨404246, by rfl⟩ : syracuseStep 2155981 = 808493) (by norm_num)
theorem B2874641 : Blo 1915435 2874641 := bstep (se 2 (by rfl) ⟨1077990, by rfl⟩ : syracuseStep 2874641 = 2155981) B2155981
theorem B1916427 : Blo 1915435 1916427 := bstep (se 1 (by rfl) ⟨1437320, by rfl⟩ : syracuseStep 1916427 = 2874641) B2874641
theorem B6467957 : Blo 1915435 6467957 := bbase (se 5 (by rfl) ⟨303185, by rfl⟩ : syracuseStep 6467957 = 606371) (by norm_num)
theorem B4311971 : Blo 1915435 4311971 := bstep (se 1 (by rfl) ⟨3233978, by rfl⟩ : syracuseStep 4311971 = 6467957) B6467957
theorem B2874647 : Blo 1915435 2874647 := bstep (se 1 (by rfl) ⟨2155985, by rfl⟩ : syracuseStep 2874647 = 4311971) B4311971
theorem B1916431 : Blo 1915435 1916431 := bstep (se 1 (by rfl) ⟨1437323, by rfl⟩ : syracuseStep 1916431 = 2874647) B2874647
theorem B2874653 : Blo 1915435 2874653 := bbase (se 3 (by rfl) ⟨538997, by rfl⟩ : syracuseStep 2874653 = 1077995) (by norm_num)
theorem B1916435 : Blo 1915435 1916435 := bstep (se 1 (by rfl) ⟨1437326, by rfl⟩ : syracuseStep 1916435 = 2874653) B2874653
theorem B4311989 : Blo 1915435 4311989 := bbase (se 5 (by rfl) ⟨202124, by rfl⟩ : syracuseStep 4311989 = 404249) (by norm_num)
theorem B2874659 : Blo 1915435 2874659 := bstep (se 1 (by rfl) ⟨2155994, by rfl⟩ : syracuseStep 2874659 = 4311989) B4311989
theorem B1916439 : Blo 1915435 1916439 := bstep (se 1 (by rfl) ⟨1437329, by rfl⟩ : syracuseStep 1916439 = 2874659) B2874659
theorem B4667485 : Blo 1915435 4667485 := bbase (se 3 (by rfl) ⟨875153, by rfl⟩ : syracuseStep 4667485 = 1750307) (by norm_num)
theorem B6223313 : Blo 1915435 6223313 := bstep (se 2 (by rfl) ⟨2333742, by rfl⟩ : syracuseStep 6223313 = 4667485) B4667485
theorem B4148875 : Blo 1915435 4148875 := bstep (se 1 (by rfl) ⟨3111656, by rfl⟩ : syracuseStep 4148875 = 6223313) B6223313
theorem B5531833 : Blo 1915435 5531833 := bstep (se 2 (by rfl) ⟨2074437, by rfl⟩ : syracuseStep 5531833 = 4148875) B4148875
theorem B29503109 : Blo 1915435 29503109 := bstep (se 4 (by rfl) ⟨2765916, by rfl⟩ : syracuseStep 29503109 = 5531833) B5531833
theorem B19668739 : Blo 1915435 19668739 := bstep (se 1 (by rfl) ⟨14751554, by rfl⟩ : syracuseStep 19668739 = 29503109) B29503109
theorem B26224985 : Blo 1915435 26224985 := bstep (se 2 (by rfl) ⟨9834369, by rfl⟩ : syracuseStep 26224985 = 19668739) B19668739
theorem B17483323 : Blo 1915435 17483323 := bstep (se 1 (by rfl) ⟨13112492, by rfl⟩ : syracuseStep 17483323 = 26224985) B26224985
theorem B23311097 : Blo 1915435 23311097 := bstep (se 2 (by rfl) ⟨8741661, by rfl⟩ : syracuseStep 23311097 = 17483323) B17483323
theorem B15540731 : Blo 1915435 15540731 := bstep (se 1 (by rfl) ⟨11655548, by rfl⟩ : syracuseStep 15540731 = 23311097) B23311097
theorem B10360487 : Blo 1915435 10360487 := bstep (se 1 (by rfl) ⟨7770365, by rfl⟩ : syracuseStep 10360487 = 15540731) B15540731
theorem B6906991 : Blo 1915435 6906991 := bstep (se 1 (by rfl) ⟨5180243, by rfl⟩ : syracuseStep 6906991 = 10360487) B10360487
theorem B9209321 : Blo 1915435 9209321 := bstep (se 2 (by rfl) ⟨3453495, by rfl⟩ : syracuseStep 9209321 = 6906991) B6906991
theorem B6139547 : Blo 1915435 6139547 := bstep (se 1 (by rfl) ⟨4604660, by rfl⟩ : syracuseStep 6139547 = 9209321) B9209321
theorem B4093031 : Blo 1915435 4093031 := bstep (se 1 (by rfl) ⟨3069773, by rfl⟩ : syracuseStep 4093031 = 6139547) B6139547
theorem B10914749 : Blo 1915435 10914749 := bstep (se 3 (by rfl) ⟨2046515, by rfl⟩ : syracuseStep 10914749 = 4093031) B4093031
theorem B7276499 : Blo 1915435 7276499 := bstep (se 1 (by rfl) ⟨5457374, by rfl⟩ : syracuseStep 7276499 = 10914749) B10914749
theorem B4850999 : Blo 1915435 4850999 := bstep (se 1 (by rfl) ⟨3638249, by rfl⟩ : syracuseStep 4850999 = 7276499) B7276499
theorem B3233999 : Blo 1915435 3233999 := bstep (se 1 (by rfl) ⟨2425499, by rfl⟩ : syracuseStep 3233999 = 4850999) B4850999
theorem B2155999 : Blo 1915435 2155999 := bstep (se 1 (by rfl) ⟨1616999, by rfl⟩ : syracuseStep 2155999 = 3233999) B3233999
theorem B2874665 : Blo 1915435 2874665 := bstep (se 2 (by rfl) ⟨1077999, by rfl⟩ : syracuseStep 2874665 = 2155999) B2155999
theorem B1916443 : Blo 1915435 1916443 := bstep (se 1 (by rfl) ⟨1437332, by rfl⟩ : syracuseStep 1916443 = 2874665) B2874665
theorem B9834389 : Blo 1915435 9834389 := bbase (se 6 (by rfl) ⟨230493, by rfl⟩ : syracuseStep 9834389 = 460987) (by norm_num)
theorem B6556259 : Blo 1915435 6556259 := bstep (se 1 (by rfl) ⟨4917194, by rfl⟩ : syracuseStep 6556259 = 9834389) B9834389
theorem B17483357 : Blo 1915435 17483357 := bstep (se 3 (by rfl) ⟨3278129, by rfl⟩ : syracuseStep 17483357 = 6556259) B6556259
theorem B11655571 : Blo 1915435 11655571 := bstep (se 1 (by rfl) ⟨8741678, by rfl⟩ : syracuseStep 11655571 = 17483357) B17483357
theorem B15540761 : Blo 1915435 15540761 := bstep (se 2 (by rfl) ⟨5827785, by rfl⟩ : syracuseStep 15540761 = 11655571) B11655571
theorem B10360507 : Blo 1915435 10360507 := bstep (se 1 (by rfl) ⟨7770380, by rfl⟩ : syracuseStep 10360507 = 15540761) B15540761
theorem B13814009 : Blo 1915435 13814009 := bstep (se 2 (by rfl) ⟨5180253, by rfl⟩ : syracuseStep 13814009 = 10360507) B10360507
theorem B9209339 : Blo 1915435 9209339 := bstep (se 1 (by rfl) ⟨6907004, by rfl⟩ : syracuseStep 9209339 = 13814009) B13814009
theorem B6139559 : Blo 1915435 6139559 := bstep (se 1 (by rfl) ⟨4604669, by rfl⟩ : syracuseStep 6139559 = 9209339) B9209339
theorem B4093039 : Blo 1915435 4093039 := bstep (se 1 (by rfl) ⟨3069779, by rfl⟩ : syracuseStep 4093039 = 6139559) B6139559
theorem B5457385 : Blo 1915435 5457385 := bstep (se 2 (by rfl) ⟨2046519, by rfl⟩ : syracuseStep 5457385 = 4093039) B4093039
theorem B7276513 : Blo 1915435 7276513 := bstep (se 2 (by rfl) ⟨2728692, by rfl⟩ : syracuseStep 7276513 = 5457385) B5457385
theorem B9702017 : Blo 1915435 9702017 := bstep (se 2 (by rfl) ⟨3638256, by rfl⟩ : syracuseStep 9702017 = 7276513) B7276513
theorem B6468011 : Blo 1915435 6468011 := bstep (se 1 (by rfl) ⟨4851008, by rfl⟩ : syracuseStep 6468011 = 9702017) B9702017
theorem B4312007 : Blo 1915435 4312007 := bstep (se 1 (by rfl) ⟨3234005, by rfl⟩ : syracuseStep 4312007 = 6468011) B6468011
theorem B2874671 : Blo 1915435 2874671 := bstep (se 1 (by rfl) ⟨2156003, by rfl⟩ : syracuseStep 2874671 = 4312007) B4312007
theorem B1916447 : Blo 1915435 1916447 := bstep (se 1 (by rfl) ⟨1437335, by rfl⟩ : syracuseStep 1916447 = 2874671) B2874671
theorem B2874677 : Blo 1915435 2874677 := bbase (se 5 (by rfl) ⟨134750, by rfl⟩ : syracuseStep 2874677 = 269501) (by norm_num)
theorem B1916451 : Blo 1915435 1916451 := bstep (se 1 (by rfl) ⟨1437338, by rfl⟩ : syracuseStep 1916451 = 2874677) B2874677
theorem B4851029 : Blo 1915435 4851029 := bbase (se 12 (by rfl) ⟨1776, by rfl⟩ : syracuseStep 4851029 = 3553) (by norm_num)
theorem B3234019 : Blo 1915435 3234019 := bstep (se 1 (by rfl) ⟨2425514, by rfl⟩ : syracuseStep 3234019 = 4851029) B4851029
theorem B4312025 : Blo 1915435 4312025 := bstep (se 2 (by rfl) ⟨1617009, by rfl⟩ : syracuseStep 4312025 = 3234019) B3234019
theorem B2874683 : Blo 1915435 2874683 := bstep (se 1 (by rfl) ⟨2156012, by rfl⟩ : syracuseStep 2874683 = 4312025) B4312025
theorem B1916455 : Blo 1915435 1916455 := bstep (se 1 (by rfl) ⟨1437341, by rfl⟩ : syracuseStep 1916455 = 2874683) B2874683
theorem B2156017 : Blo 1915435 2156017 := bbase (se 2 (by rfl) ⟨808506, by rfl⟩ : syracuseStep 2156017 = 1617013) (by norm_num)
theorem B2874689 : Blo 1915435 2874689 := bstep (se 2 (by rfl) ⟨1078008, by rfl⟩ : syracuseStep 2874689 = 2156017) B2156017
theorem B1916459 : Blo 1915435 1916459 := bstep (se 1 (by rfl) ⟨1437344, by rfl⟩ : syracuseStep 1916459 = 2874689) B2874689
theorem B12279221 : Blo 1915435 12279221 := bbase (se 5 (by rfl) ⟨575588, by rfl⟩ : syracuseStep 12279221 = 1151177) (by norm_num)
theorem B8186147 : Blo 1915435 8186147 := bstep (se 1 (by rfl) ⟨6139610, by rfl⟩ : syracuseStep 8186147 = 12279221) B12279221
theorem B5457431 : Blo 1915435 5457431 := bstep (se 1 (by rfl) ⟨4093073, by rfl⟩ : syracuseStep 5457431 = 8186147) B8186147
theorem B3638287 : Blo 1915435 3638287 := bstep (se 1 (by rfl) ⟨2728715, by rfl⟩ : syracuseStep 3638287 = 5457431) B5457431
theorem B4851049 : Blo 1915435 4851049 := bstep (se 2 (by rfl) ⟨1819143, by rfl⟩ : syracuseStep 4851049 = 3638287) B3638287
theorem B6468065 : Blo 1915435 6468065 := bstep (se 2 (by rfl) ⟨2425524, by rfl⟩ : syracuseStep 6468065 = 4851049) B4851049
theorem B4312043 : Blo 1915435 4312043 := bstep (se 1 (by rfl) ⟨3234032, by rfl⟩ : syracuseStep 4312043 = 6468065) B6468065
theorem B2874695 : Blo 1915435 2874695 := bstep (se 1 (by rfl) ⟨2156021, by rfl⟩ : syracuseStep 2874695 = 4312043) B4312043
theorem B1916463 : Blo 1915435 1916463 := bstep (se 1 (by rfl) ⟨1437347, by rfl⟩ : syracuseStep 1916463 = 2874695) B2874695
theorem B2874701 : Blo 1915435 2874701 := bbase (se 3 (by rfl) ⟨539006, by rfl⟩ : syracuseStep 2874701 = 1078013) (by norm_num)
theorem B1916467 : Blo 1915435 1916467 := bstep (se 1 (by rfl) ⟨1437350, by rfl⟩ : syracuseStep 1916467 = 2874701) B2874701
theorem B4312061 : Blo 1915435 4312061 := bbase (se 3 (by rfl) ⟨808511, by rfl⟩ : syracuseStep 4312061 = 1617023) (by norm_num)
theorem B2874707 : Blo 1915435 2874707 := bstep (se 1 (by rfl) ⟨2156030, by rfl⟩ : syracuseStep 2874707 = 4312061) B4312061
theorem B1916471 : Blo 1915435 1916471 := bstep (se 1 (by rfl) ⟨1437353, by rfl⟩ : syracuseStep 1916471 = 2874707) B2874707
theorem B3234053 : Blo 1915435 3234053 := bbase (se 4 (by rfl) ⟨303192, by rfl⟩ : syracuseStep 3234053 = 606385) (by norm_num)
theorem B2156035 : Blo 1915435 2156035 := bstep (se 1 (by rfl) ⟨1617026, by rfl⟩ : syracuseStep 2156035 = 3234053) B3234053
theorem B2874713 : Blo 1915435 2874713 := bstep (se 2 (by rfl) ⟨1078017, by rfl⟩ : syracuseStep 2874713 = 2156035) B2156035
theorem B1916475 : Blo 1915435 1916475 := bstep (se 1 (by rfl) ⟨1437356, by rfl⟩ : syracuseStep 1916475 = 2874713) B2874713
theorem B14553269 : Blo 1915435 14553269 := bbase (se 5 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 14553269 = 1364369) (by norm_num)
theorem B9702179 : Blo 1915435 9702179 := bstep (se 1 (by rfl) ⟨7276634, by rfl⟩ : syracuseStep 9702179 = 14553269) B14553269
theorem B6468119 : Blo 1915435 6468119 := bstep (se 1 (by rfl) ⟨4851089, by rfl⟩ : syracuseStep 6468119 = 9702179) B9702179
theorem B4312079 : Blo 1915435 4312079 := bstep (se 1 (by rfl) ⟨3234059, by rfl⟩ : syracuseStep 4312079 = 6468119) B6468119
theorem B2874719 : Blo 1915435 2874719 := bstep (se 1 (by rfl) ⟨2156039, by rfl⟩ : syracuseStep 2874719 = 4312079) B4312079
theorem B1916479 : Blo 1915435 1916479 := bstep (se 1 (by rfl) ⟨1437359, by rfl⟩ : syracuseStep 1916479 = 2874719) B2874719
theorem B2874725 : Blo 1915435 2874725 := bbase (se 4 (by rfl) ⟨269505, by rfl⟩ : syracuseStep 2874725 = 539011) (by norm_num)
theorem B1916483 : Blo 1915435 1916483 := bstep (se 1 (by rfl) ⟨1437362, by rfl⟩ : syracuseStep 1916483 = 2874725) B2874725
theorem B3638333 : Blo 1915435 3638333 := bbase (se 3 (by rfl) ⟨682187, by rfl⟩ : syracuseStep 3638333 = 1364375) (by norm_num)
theorem B2425555 : Blo 1915435 2425555 := bstep (se 1 (by rfl) ⟨1819166, by rfl⟩ : syracuseStep 2425555 = 3638333) B3638333
theorem B3234073 : Blo 1915435 3234073 := bstep (se 2 (by rfl) ⟨1212777, by rfl⟩ : syracuseStep 3234073 = 2425555) B2425555
theorem B4312097 : Blo 1915435 4312097 := bstep (se 2 (by rfl) ⟨1617036, by rfl⟩ : syracuseStep 4312097 = 3234073) B3234073
theorem B2874731 : Blo 1915435 2874731 := bstep (se 1 (by rfl) ⟨2156048, by rfl⟩ : syracuseStep 2874731 = 4312097) B4312097
theorem B1916487 : Blo 1915435 1916487 := bstep (se 1 (by rfl) ⟨1437365, by rfl⟩ : syracuseStep 1916487 = 2874731) B2874731
theorem B2156053 : Blo 1915435 2156053 := bbase (se 6 (by rfl) ⟨50532, by rfl⟩ : syracuseStep 2156053 = 101065) (by norm_num)
theorem B2874737 : Blo 1915435 2874737 := bstep (se 2 (by rfl) ⟨1078026, by rfl⟩ : syracuseStep 2874737 = 2156053) B2156053
theorem B1916491 : Blo 1915435 1916491 := bstep (se 1 (by rfl) ⟨1437368, by rfl⟩ : syracuseStep 1916491 = 2874737) B2874737
theorem B2425565 : Blo 1915435 2425565 := bbase (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) (by norm_num)
theorem B6468173 : Blo 1915435 6468173 := bstep (se 3 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 6468173 = 2425565) B2425565
theorem B4312115 : Blo 1915435 4312115 := bstep (se 1 (by rfl) ⟨3234086, by rfl⟩ : syracuseStep 4312115 = 6468173) B6468173
theorem B2874743 : Blo 1915435 2874743 := bstep (se 1 (by rfl) ⟨2156057, by rfl⟩ : syracuseStep 2874743 = 4312115) B4312115
theorem B1916495 : Blo 1915435 1916495 := bstep (se 1 (by rfl) ⟨1437371, by rfl⟩ : syracuseStep 1916495 = 2874743) B2874743
theorem B2874749 : Blo 1915435 2874749 := bbase (se 3 (by rfl) ⟨539015, by rfl⟩ : syracuseStep 2874749 = 1078031) (by norm_num)
theorem B1916499 : Blo 1915435 1916499 := bstep (se 1 (by rfl) ⟨1437374, by rfl⟩ : syracuseStep 1916499 = 2874749) B2874749
theorem B4312133 : Blo 1915435 4312133 := bbase (se 4 (by rfl) ⟨404262, by rfl⟩ : syracuseStep 4312133 = 808525) (by norm_num)
theorem B2874755 : Blo 1915435 2874755 := bstep (se 1 (by rfl) ⟨2156066, by rfl⟩ : syracuseStep 2874755 = 4312133) B4312133
theorem B1916503 : Blo 1915435 1916503 := bstep (se 1 (by rfl) ⟨1437377, by rfl⟩ : syracuseStep 1916503 = 2874755) B2874755
theorem B5457557 : Blo 1915435 5457557 := bbase (se 6 (by rfl) ⟨127911, by rfl⟩ : syracuseStep 5457557 = 255823) (by norm_num)
theorem B3638371 : Blo 1915435 3638371 := bstep (se 1 (by rfl) ⟨2728778, by rfl⟩ : syracuseStep 3638371 = 5457557) B5457557
theorem B4851161 : Blo 1915435 4851161 := bstep (se 2 (by rfl) ⟨1819185, by rfl⟩ : syracuseStep 4851161 = 3638371) B3638371
theorem B3234107 : Blo 1915435 3234107 := bstep (se 1 (by rfl) ⟨2425580, by rfl⟩ : syracuseStep 3234107 = 4851161) B4851161
theorem B2156071 : Blo 1915435 2156071 := bstep (se 1 (by rfl) ⟨1617053, by rfl⟩ : syracuseStep 2156071 = 3234107) B3234107
theorem B2874761 : Blo 1915435 2874761 := bstep (se 2 (by rfl) ⟨1078035, by rfl⟩ : syracuseStep 2874761 = 2156071) B2156071
theorem B1916507 : Blo 1915435 1916507 := bstep (se 1 (by rfl) ⟨1437380, by rfl⟩ : syracuseStep 1916507 = 2874761) B2874761
theorem B9702341 : Blo 1915435 9702341 := bbase (se 4 (by rfl) ⟨909594, by rfl⟩ : syracuseStep 9702341 = 1819189) (by norm_num)
theorem B6468227 : Blo 1915435 6468227 := bstep (se 1 (by rfl) ⟨4851170, by rfl⟩ : syracuseStep 6468227 = 9702341) B9702341
theorem B4312151 : Blo 1915435 4312151 := bstep (se 1 (by rfl) ⟨3234113, by rfl⟩ : syracuseStep 4312151 = 6468227) B6468227
theorem B2874767 : Blo 1915435 2874767 := bstep (se 1 (by rfl) ⟨2156075, by rfl⟩ : syracuseStep 2874767 = 4312151) B4312151
theorem B1916511 : Blo 1915435 1916511 := bstep (se 1 (by rfl) ⟨1437383, by rfl⟩ : syracuseStep 1916511 = 2874767) B2874767
theorem B2874773 : Blo 1915435 2874773 := bbase (se 6 (by rfl) ⟨67377, by rfl⟩ : syracuseStep 2874773 = 134755) (by norm_num)
theorem B1916515 : Blo 1915435 1916515 := bstep (se 1 (by rfl) ⟨1437386, by rfl⟩ : syracuseStep 1916515 = 2874773) B2874773
theorem B4371005 : Blo 1915435 4371005 := bbase (se 3 (by rfl) ⟨819563, by rfl⟩ : syracuseStep 4371005 = 1639127) (by norm_num)
theorem B2914003 : Blo 1915435 2914003 := bstep (se 1 (by rfl) ⟨2185502, by rfl⟩ : syracuseStep 2914003 = 4371005) B4371005
theorem B3885337 : Blo 1915435 3885337 := bstep (se 2 (by rfl) ⟨1457001, by rfl⟩ : syracuseStep 3885337 = 2914003) B2914003
theorem B5180449 : Blo 1915435 5180449 := bstep (se 2 (by rfl) ⟨1942668, by rfl⟩ : syracuseStep 5180449 = 3885337) B3885337
theorem B6907265 : Blo 1915435 6907265 := bstep (se 2 (by rfl) ⟨2590224, by rfl⟩ : syracuseStep 6907265 = 5180449) B5180449
theorem B4604843 : Blo 1915435 4604843 := bstep (se 1 (by rfl) ⟨3453632, by rfl⟩ : syracuseStep 4604843 = 6907265) B6907265
theorem B3069895 : Blo 1915435 3069895 := bstep (se 1 (by rfl) ⟨2302421, by rfl⟩ : syracuseStep 3069895 = 4604843) B4604843
theorem B4093193 : Blo 1915435 4093193 := bstep (se 2 (by rfl) ⟨1534947, by rfl⟩ : syracuseStep 4093193 = 3069895) B3069895
theorem B10915181 : Blo 1915435 10915181 := bstep (se 3 (by rfl) ⟨2046596, by rfl⟩ : syracuseStep 10915181 = 4093193) B4093193
theorem B7276787 : Blo 1915435 7276787 := bstep (se 1 (by rfl) ⟨5457590, by rfl⟩ : syracuseStep 7276787 = 10915181) B10915181
theorem B4851191 : Blo 1915435 4851191 := bstep (se 1 (by rfl) ⟨3638393, by rfl⟩ : syracuseStep 4851191 = 7276787) B7276787
theorem B3234127 : Blo 1915435 3234127 := bstep (se 1 (by rfl) ⟨2425595, by rfl⟩ : syracuseStep 3234127 = 4851191) B4851191
theorem B4312169 : Blo 1915435 4312169 := bstep (se 2 (by rfl) ⟨1617063, by rfl⟩ : syracuseStep 4312169 = 3234127) B3234127
theorem B2874779 : Blo 1915435 2874779 := bstep (se 1 (by rfl) ⟨2156084, by rfl⟩ : syracuseStep 2874779 = 4312169) B4312169
theorem B1916519 : Blo 1915435 1916519 := bstep (se 1 (by rfl) ⟨1437389, by rfl⟩ : syracuseStep 1916519 = 2874779) B2874779
theorem B2156089 : Blo 1915435 2156089 := bbase (se 2 (by rfl) ⟨808533, by rfl⟩ : syracuseStep 2156089 = 1617067) (by norm_num)
theorem B2874785 : Blo 1915435 2874785 := bstep (se 2 (by rfl) ⟨1078044, by rfl⟩ : syracuseStep 2874785 = 2156089) B2156089
theorem B1916523 : Blo 1915435 1916523 := bstep (se 1 (by rfl) ⟨1437392, by rfl⟩ : syracuseStep 1916523 = 2874785) B2874785
theorem B2046605 : Blo 1915435 2046605 := bbase (se 3 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 2046605 = 767477) (by norm_num)
theorem B5457613 : Blo 1915435 5457613 := bstep (se 3 (by rfl) ⟨1023302, by rfl⟩ : syracuseStep 5457613 = 2046605) B2046605
theorem B7276817 : Blo 1915435 7276817 := bstep (se 2 (by rfl) ⟨2728806, by rfl⟩ : syracuseStep 7276817 = 5457613) B5457613
theorem B4851211 : Blo 1915435 4851211 := bstep (se 1 (by rfl) ⟨3638408, by rfl⟩ : syracuseStep 4851211 = 7276817) B7276817
theorem B6468281 : Blo 1915435 6468281 := bstep (se 2 (by rfl) ⟨2425605, by rfl⟩ : syracuseStep 6468281 = 4851211) B4851211
theorem B4312187 : Blo 1915435 4312187 := bstep (se 1 (by rfl) ⟨3234140, by rfl⟩ : syracuseStep 4312187 = 6468281) B6468281
theorem B2874791 : Blo 1915435 2874791 := bstep (se 1 (by rfl) ⟨2156093, by rfl⟩ : syracuseStep 2874791 = 4312187) B4312187
theorem B1916527 : Blo 1915435 1916527 := bstep (se 1 (by rfl) ⟨1437395, by rfl⟩ : syracuseStep 1916527 = 2874791) B2874791
theorem B2874797 : Blo 1915435 2874797 := bbase (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) (by norm_num)
theorem B1916531 : Blo 1915435 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B4312205 : Blo 1915435 4312205 := bbase (se 3 (by rfl) ⟨808538, by rfl⟩ : syracuseStep 4312205 = 1617077) (by norm_num)
theorem B2874803 : Blo 1915435 2874803 := bstep (se 1 (by rfl) ⟨2156102, by rfl⟩ : syracuseStep 2874803 = 4312205) B4312205
theorem B1916535 : Blo 1915435 1916535 := bstep (se 1 (by rfl) ⟨1437401, by rfl⟩ : syracuseStep 1916535 = 2874803) B2874803
theorem B2425621 : Blo 1915435 2425621 := bbase (se 6 (by rfl) ⟨56850, by rfl⟩ : syracuseStep 2425621 = 113701) (by norm_num)
theorem B3234161 : Blo 1915435 3234161 := bstep (se 2 (by rfl) ⟨1212810, by rfl⟩ : syracuseStep 3234161 = 2425621) B2425621
theorem B2156107 : Blo 1915435 2156107 := bstep (se 1 (by rfl) ⟨1617080, by rfl⟩ : syracuseStep 2156107 = 3234161) B3234161
theorem B2874809 : Blo 1915435 2874809 := bstep (se 2 (by rfl) ⟨1078053, by rfl⟩ : syracuseStep 2874809 = 2156107) B2156107
theorem B1916539 : Blo 1915435 1916539 := bstep (se 1 (by rfl) ⟨1437404, by rfl⟩ : syracuseStep 1916539 = 2874809) B2874809
theorem B3548557 : Blo 1915435 3548557 := bbase (se 3 (by rfl) ⟨665354, by rfl⟩ : syracuseStep 3548557 = 1330709) (by norm_num)
theorem B4731409 : Blo 1915435 4731409 := bstep (se 2 (by rfl) ⟨1774278, by rfl⟩ : syracuseStep 4731409 = 3548557) B3548557
theorem B6308545 : Blo 1915435 6308545 := bstep (se 2 (by rfl) ⟨2365704, by rfl⟩ : syracuseStep 6308545 = 4731409) B4731409
theorem B8411393 : Blo 1915435 8411393 := bstep (se 2 (by rfl) ⟨3154272, by rfl⟩ : syracuseStep 8411393 = 6308545) B6308545
theorem B22430381 : Blo 1915435 22430381 := bstep (se 3 (by rfl) ⟨4205696, by rfl⟩ : syracuseStep 22430381 = 8411393) B8411393
theorem B59814349 : Blo 1915435 59814349 := bstep (se 3 (by rfl) ⟨11215190, by rfl⟩ : syracuseStep 59814349 = 22430381) B22430381
theorem B319009861 : Blo 1915435 319009861 := bstep (se 4 (by rfl) ⟨29907174, by rfl⟩ : syracuseStep 319009861 = 59814349) B59814349
theorem B425346481 : Blo 1915435 425346481 := bstep (se 2 (by rfl) ⟨159504930, by rfl⟩ : syracuseStep 425346481 = 319009861) B319009861
theorem B567128641 : Blo 1915435 567128641 := bstep (se 2 (by rfl) ⟨212673240, by rfl⟩ : syracuseStep 567128641 = 425346481) B425346481
theorem B756171521 : Blo 1915435 756171521 := bstep (se 2 (by rfl) ⟨283564320, by rfl⟩ : syracuseStep 756171521 = 567128641) B567128641
theorem B504114347 : Blo 1915435 504114347 := bstep (se 1 (by rfl) ⟨378085760, by rfl⟩ : syracuseStep 504114347 = 756171521) B756171521
theorem B336076231 : Blo 1915435 336076231 := bstep (se 1 (by rfl) ⟨252057173, by rfl⟩ : syracuseStep 336076231 = 504114347) B504114347
theorem B448101641 : Blo 1915435 448101641 := bstep (se 2 (by rfl) ⟨168038115, by rfl⟩ : syracuseStep 448101641 = 336076231) B336076231
theorem B298734427 : Blo 1915435 298734427 := bstep (se 1 (by rfl) ⟨224050820, by rfl⟩ : syracuseStep 298734427 = 448101641) B448101641
theorem B398312569 : Blo 1915435 398312569 := bstep (se 2 (by rfl) ⟨149367213, by rfl⟩ : syracuseStep 398312569 = 298734427) B298734427
theorem B531083425 : Blo 1915435 531083425 := bstep (se 2 (by rfl) ⟨199156284, by rfl⟩ : syracuseStep 531083425 = 398312569) B398312569
theorem B708111233 : Blo 1915435 708111233 := bstep (se 2 (by rfl) ⟨265541712, by rfl⟩ : syracuseStep 708111233 = 531083425) B531083425
theorem B472074155 : Blo 1915435 472074155 := bstep (se 1 (by rfl) ⟨354055616, by rfl⟩ : syracuseStep 472074155 = 708111233) B708111233
theorem B314716103 : Blo 1915435 314716103 := bstep (se 1 (by rfl) ⟨236037077, by rfl⟩ : syracuseStep 314716103 = 472074155) B472074155
theorem B209810735 : Blo 1915435 209810735 := bstep (se 1 (by rfl) ⟨157358051, by rfl⟩ : syracuseStep 209810735 = 314716103) B314716103
theorem B139873823 : Blo 1915435 139873823 := bstep (se 1 (by rfl) ⟨104905367, by rfl⟩ : syracuseStep 139873823 = 209810735) B209810735
theorem B93249215 : Blo 1915435 93249215 := bstep (se 1 (by rfl) ⟨69936911, by rfl⟩ : syracuseStep 93249215 = 139873823) B139873823
theorem B62166143 : Blo 1915435 62166143 := bstep (se 1 (by rfl) ⟨46624607, by rfl⟩ : syracuseStep 62166143 = 93249215) B93249215
theorem B41444095 : Blo 1915435 41444095 := bstep (se 1 (by rfl) ⟨31083071, by rfl⟩ : syracuseStep 41444095 = 62166143) B62166143
theorem B55258793 : Blo 1915435 55258793 := bstep (se 2 (by rfl) ⟨20722047, by rfl⟩ : syracuseStep 55258793 = 41444095) B41444095
theorem B36839195 : Blo 1915435 36839195 := bstep (se 1 (by rfl) ⟨27629396, by rfl⟩ : syracuseStep 36839195 = 55258793) B55258793
theorem B24559463 : Blo 1915435 24559463 := bstep (se 1 (by rfl) ⟨18419597, by rfl⟩ : syracuseStep 24559463 = 36839195) B36839195
theorem B16372975 : Blo 1915435 16372975 := bstep (se 1 (by rfl) ⟨12279731, by rfl⟩ : syracuseStep 16372975 = 24559463) B24559463
theorem B21830633 : Blo 1915435 21830633 := bstep (se 2 (by rfl) ⟨8186487, by rfl⟩ : syracuseStep 21830633 = 16372975) B16372975
theorem B14553755 : Blo 1915435 14553755 := bstep (se 1 (by rfl) ⟨10915316, by rfl⟩ : syracuseStep 14553755 = 21830633) B21830633
theorem B9702503 : Blo 1915435 9702503 := bstep (se 1 (by rfl) ⟨7276877, by rfl⟩ : syracuseStep 9702503 = 14553755) B14553755
theorem B6468335 : Blo 1915435 6468335 := bstep (se 1 (by rfl) ⟨4851251, by rfl⟩ : syracuseStep 6468335 = 9702503) B9702503
theorem B4312223 : Blo 1915435 4312223 := bstep (se 1 (by rfl) ⟨3234167, by rfl⟩ : syracuseStep 4312223 = 6468335) B6468335
theorem B2874815 : Blo 1915435 2874815 := bstep (se 1 (by rfl) ⟨2156111, by rfl⟩ : syracuseStep 2874815 = 4312223) B4312223
theorem B1916543 : Blo 1915435 1916543 := bstep (se 1 (by rfl) ⟨1437407, by rfl⟩ : syracuseStep 1916543 = 2874815) B2874815
theorem B2874821 : Blo 1915435 2874821 := bbase (se 4 (by rfl) ⟨269514, by rfl⟩ : syracuseStep 2874821 = 539029) (by norm_num)
theorem B1916547 : Blo 1915435 1916547 := bstep (se 1 (by rfl) ⟨1437410, by rfl⟩ : syracuseStep 1916547 = 2874821) B2874821
theorem B3234181 : Blo 1915435 3234181 := bbase (se 4 (by rfl) ⟨303204, by rfl⟩ : syracuseStep 3234181 = 606409) (by norm_num)
theorem B4312241 : Blo 1915435 4312241 := bstep (se 2 (by rfl) ⟨1617090, by rfl⟩ : syracuseStep 4312241 = 3234181) B3234181
theorem B2874827 : Blo 1915435 2874827 := bstep (se 1 (by rfl) ⟨2156120, by rfl⟩ : syracuseStep 2874827 = 4312241) B4312241
theorem B1916551 : Blo 1915435 1916551 := bstep (se 1 (by rfl) ⟨1437413, by rfl⟩ : syracuseStep 1916551 = 2874827) B2874827
theorem B2156125 : Blo 1915435 2156125 := bbase (se 3 (by rfl) ⟨404273, by rfl⟩ : syracuseStep 2156125 = 808547) (by norm_num)
theorem B2874833 : Blo 1915435 2874833 := bstep (se 2 (by rfl) ⟨1078062, by rfl⟩ : syracuseStep 2874833 = 2156125) B2156125
theorem B1916555 : Blo 1915435 1916555 := bstep (se 1 (by rfl) ⟨1437416, by rfl⟩ : syracuseStep 1916555 = 2874833) B2874833
theorem B6468389 : Blo 1915435 6468389 := bbase (se 4 (by rfl) ⟨606411, by rfl⟩ : syracuseStep 6468389 = 1212823) (by norm_num)
theorem B4312259 : Blo 1915435 4312259 := bstep (se 1 (by rfl) ⟨3234194, by rfl⟩ : syracuseStep 4312259 = 6468389) B6468389
theorem B2874839 : Blo 1915435 2874839 := bstep (se 1 (by rfl) ⟨2156129, by rfl⟩ : syracuseStep 2874839 = 4312259) B4312259
theorem B1916559 : Blo 1915435 1916559 := bstep (se 1 (by rfl) ⟨1437419, by rfl⟩ : syracuseStep 1916559 = 2874839) B2874839
theorem B2874845 : Blo 1915435 2874845 := bbase (se 3 (by rfl) ⟨539033, by rfl⟩ : syracuseStep 2874845 = 1078067) (by norm_num)
theorem B1916563 : Blo 1915435 1916563 := bstep (se 1 (by rfl) ⟨1437422, by rfl⟩ : syracuseStep 1916563 = 2874845) B2874845
theorem B4312277 : Blo 1915435 4312277 := bbase (se 7 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 4312277 = 101069) (by norm_num)
theorem B2874851 : Blo 1915435 2874851 := bstep (se 1 (by rfl) ⟨2156138, by rfl⟩ : syracuseStep 2874851 = 4312277) B4312277
theorem B1916567 : Blo 1915435 1916567 := bstep (se 1 (by rfl) ⟨1437425, by rfl⟩ : syracuseStep 1916567 = 2874851) B2874851
theorem B6139957 : Blo 1915435 6139957 := bbase (se 5 (by rfl) ⟨287810, by rfl⟩ : syracuseStep 6139957 = 575621) (by norm_num)
theorem B8186609 : Blo 1915435 8186609 := bstep (se 2 (by rfl) ⟨3069978, by rfl⟩ : syracuseStep 8186609 = 6139957) B6139957
theorem B5457739 : Blo 1915435 5457739 := bstep (se 1 (by rfl) ⟨4093304, by rfl⟩ : syracuseStep 5457739 = 8186609) B8186609
theorem B7276985 : Blo 1915435 7276985 := bstep (se 2 (by rfl) ⟨2728869, by rfl⟩ : syracuseStep 7276985 = 5457739) B5457739
theorem B4851323 : Blo 1915435 4851323 := bstep (se 1 (by rfl) ⟨3638492, by rfl⟩ : syracuseStep 4851323 = 7276985) B7276985
theorem B3234215 : Blo 1915435 3234215 := bstep (se 1 (by rfl) ⟨2425661, by rfl⟩ : syracuseStep 3234215 = 4851323) B4851323
theorem B2156143 : Blo 1915435 2156143 := bstep (se 1 (by rfl) ⟨1617107, by rfl⟩ : syracuseStep 2156143 = 3234215) B3234215
theorem B2874857 : Blo 1915435 2874857 := bstep (se 2 (by rfl) ⟨1078071, by rfl⟩ : syracuseStep 2874857 = 2156143) B2156143
theorem B1916571 : Blo 1915435 1916571 := bstep (se 1 (by rfl) ⟨1437428, by rfl⟩ : syracuseStep 1916571 = 2874857) B2874857
theorem B18925973 : Blo 1915435 18925973 := bbase (se 6 (by rfl) ⟨443577, by rfl⟩ : syracuseStep 18925973 = 887155) (by norm_num)
theorem B12617315 : Blo 1915435 12617315 := bstep (se 1 (by rfl) ⟨9462986, by rfl⟩ : syracuseStep 12617315 = 18925973) B18925973
theorem B8411543 : Blo 1915435 8411543 := bstep (se 1 (by rfl) ⟨6308657, by rfl⟩ : syracuseStep 8411543 = 12617315) B12617315
theorem B5607695 : Blo 1915435 5607695 := bstep (se 1 (by rfl) ⟨4205771, by rfl⟩ : syracuseStep 5607695 = 8411543) B8411543
theorem B3738463 : Blo 1915435 3738463 := bstep (se 1 (by rfl) ⟨2803847, by rfl⟩ : syracuseStep 3738463 = 5607695) B5607695
theorem B19938469 : Blo 1915435 19938469 := bstep (se 4 (by rfl) ⟨1869231, by rfl⟩ : syracuseStep 19938469 = 3738463) B3738463
theorem B26584625 : Blo 1915435 26584625 := bstep (se 2 (by rfl) ⟨9969234, by rfl⟩ : syracuseStep 26584625 = 19938469) B19938469
theorem B17723083 : Blo 1915435 17723083 := bstep (se 1 (by rfl) ⟨13292312, by rfl⟩ : syracuseStep 17723083 = 26584625) B26584625
theorem B23630777 : Blo 1915435 23630777 := bstep (se 2 (by rfl) ⟨8861541, by rfl⟩ : syracuseStep 23630777 = 17723083) B17723083
theorem B15753851 : Blo 1915435 15753851 := bstep (se 1 (by rfl) ⟨11815388, by rfl⟩ : syracuseStep 15753851 = 23630777) B23630777
theorem B10502567 : Blo 1915435 10502567 := bstep (se 1 (by rfl) ⟨7876925, by rfl⟩ : syracuseStep 10502567 = 15753851) B15753851
theorem B7001711 : Blo 1915435 7001711 := bstep (se 1 (by rfl) ⟨5251283, by rfl⟩ : syracuseStep 7001711 = 10502567) B10502567
theorem B4667807 : Blo 1915435 4667807 := bstep (se 1 (by rfl) ⟨3500855, by rfl⟩ : syracuseStep 4667807 = 7001711) B7001711
theorem B3111871 : Blo 1915435 3111871 := bstep (se 1 (by rfl) ⟨2333903, by rfl⟩ : syracuseStep 3111871 = 4667807) B4667807
theorem B4149161 : Blo 1915435 4149161 := bstep (se 2 (by rfl) ⟨1555935, by rfl⟩ : syracuseStep 4149161 = 3111871) B3111871
theorem B2766107 : Blo 1915435 2766107 := bstep (se 1 (by rfl) ⟨2074580, by rfl⟩ : syracuseStep 2766107 = 4149161) B4149161
theorem B7376285 : Blo 1915435 7376285 := bstep (se 3 (by rfl) ⟨1383053, by rfl⟩ : syracuseStep 7376285 = 2766107) B2766107
theorem B4917523 : Blo 1915435 4917523 := bstep (se 1 (by rfl) ⟨3688142, by rfl⟩ : syracuseStep 4917523 = 7376285) B7376285
theorem B6556697 : Blo 1915435 6556697 := bstep (se 2 (by rfl) ⟨2458761, by rfl⟩ : syracuseStep 6556697 = 4917523) B4917523
theorem B4371131 : Blo 1915435 4371131 := bstep (se 1 (by rfl) ⟨3278348, by rfl⟩ : syracuseStep 4371131 = 6556697) B6556697
theorem B11656349 : Blo 1915435 11656349 := bstep (se 3 (by rfl) ⟨2185565, by rfl⟩ : syracuseStep 11656349 = 4371131) B4371131
theorem B7770899 : Blo 1915435 7770899 := bstep (se 1 (by rfl) ⟨5828174, by rfl⟩ : syracuseStep 7770899 = 11656349) B11656349
theorem B5180599 : Blo 1915435 5180599 := bstep (se 1 (by rfl) ⟨3885449, by rfl⟩ : syracuseStep 5180599 = 7770899) B7770899
theorem B6907465 : Blo 1915435 6907465 := bstep (se 2 (by rfl) ⟨2590299, by rfl⟩ : syracuseStep 6907465 = 5180599) B5180599
theorem B9209953 : Blo 1915435 9209953 := bstep (se 2 (by rfl) ⟨3453732, by rfl⟩ : syracuseStep 9209953 = 6907465) B6907465
theorem B12279937 : Blo 1915435 12279937 := bstep (se 2 (by rfl) ⟨4604976, by rfl⟩ : syracuseStep 12279937 = 9209953) B9209953
theorem B16373249 : Blo 1915435 16373249 := bstep (se 2 (by rfl) ⟨6139968, by rfl⟩ : syracuseStep 16373249 = 12279937) B12279937
theorem B10915499 : Blo 1915435 10915499 := bstep (se 1 (by rfl) ⟨8186624, by rfl⟩ : syracuseStep 10915499 = 16373249) B16373249
theorem B7276999 : Blo 1915435 7276999 := bstep (se 1 (by rfl) ⟨5457749, by rfl⟩ : syracuseStep 7276999 = 10915499) B10915499
theorem B9702665 : Blo 1915435 9702665 := bstep (se 2 (by rfl) ⟨3638499, by rfl⟩ : syracuseStep 9702665 = 7276999) B7276999
theorem B6468443 : Blo 1915435 6468443 := bstep (se 1 (by rfl) ⟨4851332, by rfl⟩ : syracuseStep 6468443 = 9702665) B9702665
theorem B4312295 : Blo 1915435 4312295 := bstep (se 1 (by rfl) ⟨3234221, by rfl⟩ : syracuseStep 4312295 = 6468443) B6468443
theorem B2874863 : Blo 1915435 2874863 := bstep (se 1 (by rfl) ⟨2156147, by rfl⟩ : syracuseStep 2874863 = 4312295) B4312295
theorem B1916575 : Blo 1915435 1916575 := bstep (se 1 (by rfl) ⟨1437431, by rfl⟩ : syracuseStep 1916575 = 2874863) B2874863
theorem B2874869 : Blo 1915435 2874869 := bbase (se 5 (by rfl) ⟨134759, by rfl⟩ : syracuseStep 2874869 = 269519) (by norm_num)
theorem B1916579 : Blo 1915435 1916579 := bstep (se 1 (by rfl) ⟨1437434, by rfl⟩ : syracuseStep 1916579 = 2874869) B2874869
theorem B2046665 : Blo 1915435 2046665 := bbase (se 2 (by rfl) ⟨767499, by rfl⟩ : syracuseStep 2046665 = 1534999) (by norm_num)
theorem B5457773 : Blo 1915435 5457773 := bstep (se 3 (by rfl) ⟨1023332, by rfl⟩ : syracuseStep 5457773 = 2046665) B2046665
theorem B3638515 : Blo 1915435 3638515 := bstep (se 1 (by rfl) ⟨2728886, by rfl⟩ : syracuseStep 3638515 = 5457773) B5457773
theorem B4851353 : Blo 1915435 4851353 := bstep (se 2 (by rfl) ⟨1819257, by rfl⟩ : syracuseStep 4851353 = 3638515) B3638515
theorem B3234235 : Blo 1915435 3234235 := bstep (se 1 (by rfl) ⟨2425676, by rfl⟩ : syracuseStep 3234235 = 4851353) B4851353
theorem B4312313 : Blo 1915435 4312313 := bstep (se 2 (by rfl) ⟨1617117, by rfl⟩ : syracuseStep 4312313 = 3234235) B3234235
theorem B2874875 : Blo 1915435 2874875 := bstep (se 1 (by rfl) ⟨2156156, by rfl⟩ : syracuseStep 2874875 = 4312313) B4312313
theorem B1916583 : Blo 1915435 1916583 := bstep (se 1 (by rfl) ⟨1437437, by rfl⟩ : syracuseStep 1916583 = 2874875) B2874875
theorem B2156161 : Blo 1915435 2156161 := bbase (se 2 (by rfl) ⟨808560, by rfl⟩ : syracuseStep 2156161 = 1617121) (by norm_num)
theorem B2874881 : Blo 1915435 2874881 := bstep (se 2 (by rfl) ⟨1078080, by rfl⟩ : syracuseStep 2874881 = 2156161) B2156161
theorem B1916587 : Blo 1915435 1916587 := bstep (se 1 (by rfl) ⟨1437440, by rfl⟩ : syracuseStep 1916587 = 2874881) B2874881
theorem B4851373 : Blo 1915435 4851373 := bbase (se 3 (by rfl) ⟨909632, by rfl⟩ : syracuseStep 4851373 = 1819265) (by norm_num)
theorem B6468497 : Blo 1915435 6468497 := bstep (se 2 (by rfl) ⟨2425686, by rfl⟩ : syracuseStep 6468497 = 4851373) B4851373
theorem B4312331 : Blo 1915435 4312331 := bstep (se 1 (by rfl) ⟨3234248, by rfl⟩ : syracuseStep 4312331 = 6468497) B6468497
theorem B2874887 : Blo 1915435 2874887 := bstep (se 1 (by rfl) ⟨2156165, by rfl⟩ : syracuseStep 2874887 = 4312331) B4312331
theorem B1916591 : Blo 1915435 1916591 := bstep (se 1 (by rfl) ⟨1437443, by rfl⟩ : syracuseStep 1916591 = 2874887) B2874887
theorem B2874893 : Blo 1915435 2874893 := bbase (se 3 (by rfl) ⟨539042, by rfl⟩ : syracuseStep 2874893 = 1078085) (by norm_num)
theorem B1916595 : Blo 1915435 1916595 := bstep (se 1 (by rfl) ⟨1437446, by rfl⟩ : syracuseStep 1916595 = 2874893) B2874893
theorem B4312349 : Blo 1915435 4312349 := bbase (se 3 (by rfl) ⟨808565, by rfl⟩ : syracuseStep 4312349 = 1617131) (by norm_num)
theorem B2874899 : Blo 1915435 2874899 := bstep (se 1 (by rfl) ⟨2156174, by rfl⟩ : syracuseStep 2874899 = 4312349) B4312349
theorem B1916599 : Blo 1915435 1916599 := bstep (se 1 (by rfl) ⟨1437449, by rfl⟩ : syracuseStep 1916599 = 2874899) B2874899
theorem B3234269 : Blo 1915435 3234269 := bbase (se 3 (by rfl) ⟨606425, by rfl⟩ : syracuseStep 3234269 = 1212851) (by norm_num)
theorem B2156179 : Blo 1915435 2156179 := bstep (se 1 (by rfl) ⟨1617134, by rfl⟩ : syracuseStep 2156179 = 3234269) B3234269
theorem B2874905 : Blo 1915435 2874905 := bstep (se 2 (by rfl) ⟨1078089, by rfl⟩ : syracuseStep 2874905 = 2156179) B2156179
theorem B1916603 : Blo 1915435 1916603 := bstep (se 1 (by rfl) ⟨1437452, by rfl⟩ : syracuseStep 1916603 = 2874905) B2874905
theorem B4149229 : Blo 1915435 4149229 := bbase (se 3 (by rfl) ⟨777980, by rfl⟩ : syracuseStep 4149229 = 1555961) (by norm_num)
theorem B5532305 : Blo 1915435 5532305 := bstep (se 2 (by rfl) ⟨2074614, by rfl⟩ : syracuseStep 5532305 = 4149229) B4149229
theorem B59011253 : Blo 1915435 59011253 := bstep (se 5 (by rfl) ⟨2766152, by rfl⟩ : syracuseStep 59011253 = 5532305) B5532305
theorem B39340835 : Blo 1915435 39340835 := bstep (se 1 (by rfl) ⟨29505626, by rfl⟩ : syracuseStep 39340835 = 59011253) B59011253
theorem B26227223 : Blo 1915435 26227223 := bstep (se 1 (by rfl) ⟨19670417, by rfl⟩ : syracuseStep 26227223 = 39340835) B39340835
theorem B17484815 : Blo 1915435 17484815 := bstep (se 1 (by rfl) ⟨13113611, by rfl⟩ : syracuseStep 17484815 = 26227223) B26227223
theorem B11656543 : Blo 1915435 11656543 := bstep (se 1 (by rfl) ⟨8742407, by rfl⟩ : syracuseStep 11656543 = 17484815) B17484815
theorem B15542057 : Blo 1915435 15542057 := bstep (se 2 (by rfl) ⟨5828271, by rfl⟩ : syracuseStep 15542057 = 11656543) B11656543
theorem B10361371 : Blo 1915435 10361371 := bstep (se 1 (by rfl) ⟨7771028, by rfl⟩ : syracuseStep 10361371 = 15542057) B15542057
theorem B13815161 : Blo 1915435 13815161 := bstep (se 2 (by rfl) ⟨5180685, by rfl⟩ : syracuseStep 13815161 = 10361371) B10361371
theorem B9210107 : Blo 1915435 9210107 := bstep (se 1 (by rfl) ⟨6907580, by rfl⟩ : syracuseStep 9210107 = 13815161) B13815161
theorem B6140071 : Blo 1915435 6140071 := bstep (se 1 (by rfl) ⟨4605053, by rfl⟩ : syracuseStep 6140071 = 9210107) B9210107
theorem B8186761 : Blo 1915435 8186761 := bstep (se 2 (by rfl) ⟨3070035, by rfl⟩ : syracuseStep 8186761 = 6140071) B6140071
theorem B10915681 : Blo 1915435 10915681 := bstep (se 2 (by rfl) ⟨4093380, by rfl⟩ : syracuseStep 10915681 = 8186761) B8186761
theorem B14554241 : Blo 1915435 14554241 := bstep (se 2 (by rfl) ⟨5457840, by rfl⟩ : syracuseStep 14554241 = 10915681) B10915681
theorem B9702827 : Blo 1915435 9702827 := bstep (se 1 (by rfl) ⟨7277120, by rfl⟩ : syracuseStep 9702827 = 14554241) B14554241
theorem B6468551 : Blo 1915435 6468551 := bstep (se 1 (by rfl) ⟨4851413, by rfl⟩ : syracuseStep 6468551 = 9702827) B9702827
theorem B4312367 : Blo 1915435 4312367 := bstep (se 1 (by rfl) ⟨3234275, by rfl⟩ : syracuseStep 4312367 = 6468551) B6468551
theorem B2874911 : Blo 1915435 2874911 := bstep (se 1 (by rfl) ⟨2156183, by rfl⟩ : syracuseStep 2874911 = 4312367) B4312367
theorem B1916607 : Blo 1915435 1916607 := bstep (se 1 (by rfl) ⟨1437455, by rfl⟩ : syracuseStep 1916607 = 2874911) B2874911
theorem B2874917 : Blo 1915435 2874917 := bbase (se 4 (by rfl) ⟨269523, by rfl⟩ : syracuseStep 2874917 = 539047) (by norm_num)
theorem B1916611 : Blo 1915435 1916611 := bstep (se 1 (by rfl) ⟨1437458, by rfl⟩ : syracuseStep 1916611 = 2874917) B2874917
theorem B2425717 : Blo 1915435 2425717 := bbase (se 5 (by rfl) ⟨113705, by rfl⟩ : syracuseStep 2425717 = 227411) (by norm_num)
theorem B3234289 : Blo 1915435 3234289 := bstep (se 2 (by rfl) ⟨1212858, by rfl⟩ : syracuseStep 3234289 = 2425717) B2425717
theorem B4312385 : Blo 1915435 4312385 := bstep (se 2 (by rfl) ⟨1617144, by rfl⟩ : syracuseStep 4312385 = 3234289) B3234289
theorem B2874923 : Blo 1915435 2874923 := bstep (se 1 (by rfl) ⟨2156192, by rfl⟩ : syracuseStep 2874923 = 4312385) B4312385
theorem B1916615 : Blo 1915435 1916615 := bstep (se 1 (by rfl) ⟨1437461, by rfl⟩ : syracuseStep 1916615 = 2874923) B2874923
theorem B2156197 : Blo 1915435 2156197 := bbase (se 4 (by rfl) ⟨202143, by rfl⟩ : syracuseStep 2156197 = 404287) (by norm_num)
theorem B2874929 : Blo 1915435 2874929 := bstep (se 2 (by rfl) ⟨1078098, by rfl⟩ : syracuseStep 2874929 = 2156197) B2156197
theorem B1916619 : Blo 1915435 1916619 := bstep (se 1 (by rfl) ⟨1437464, by rfl⟩ : syracuseStep 1916619 = 2874929) B2874929
theorem B3111949 : Blo 1915435 3111949 := bbase (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) (by norm_num)
theorem B16597061 : Blo 1915435 16597061 := bstep (se 4 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 16597061 = 3111949) B3111949
theorem B11064707 : Blo 1915435 11064707 := bstep (se 1 (by rfl) ⟨8298530, by rfl⟩ : syracuseStep 11064707 = 16597061) B16597061
theorem B7376471 : Blo 1915435 7376471 := bstep (se 1 (by rfl) ⟨5532353, by rfl⟩ : syracuseStep 7376471 = 11064707) B11064707
theorem B4917647 : Blo 1915435 4917647 := bstep (se 1 (by rfl) ⟨3688235, by rfl⟩ : syracuseStep 4917647 = 7376471) B7376471
theorem B3278431 : Blo 1915435 3278431 := bstep (se 1 (by rfl) ⟨2458823, by rfl⟩ : syracuseStep 3278431 = 4917647) B4917647
theorem B4371241 : Blo 1915435 4371241 := bstep (se 2 (by rfl) ⟨1639215, by rfl⟩ : syracuseStep 4371241 = 3278431) B3278431
theorem B5828321 : Blo 1915435 5828321 := bstep (se 2 (by rfl) ⟨2185620, by rfl⟩ : syracuseStep 5828321 = 4371241) B4371241
theorem B15542189 : Blo 1915435 15542189 := bstep (se 3 (by rfl) ⟨2914160, by rfl⟩ : syracuseStep 15542189 = 5828321) B5828321
theorem B10361459 : Blo 1915435 10361459 := bstep (se 1 (by rfl) ⟨7771094, by rfl⟩ : syracuseStep 10361459 = 15542189) B15542189
theorem B27630557 : Blo 1915435 27630557 := bstep (se 3 (by rfl) ⟨5180729, by rfl⟩ : syracuseStep 27630557 = 10361459) B10361459
theorem B18420371 : Blo 1915435 18420371 := bstep (se 1 (by rfl) ⟨13815278, by rfl⟩ : syracuseStep 18420371 = 27630557) B27630557
theorem B12280247 : Blo 1915435 12280247 := bstep (se 1 (by rfl) ⟨9210185, by rfl⟩ : syracuseStep 12280247 = 18420371) B18420371
theorem B8186831 : Blo 1915435 8186831 := bstep (se 1 (by rfl) ⟨6140123, by rfl⟩ : syracuseStep 8186831 = 12280247) B12280247
theorem B5457887 : Blo 1915435 5457887 := bstep (se 1 (by rfl) ⟨4093415, by rfl⟩ : syracuseStep 5457887 = 8186831) B8186831
theorem B3638591 : Blo 1915435 3638591 := bstep (se 1 (by rfl) ⟨2728943, by rfl⟩ : syracuseStep 3638591 = 5457887) B5457887
theorem B2425727 : Blo 1915435 2425727 := bstep (se 1 (by rfl) ⟨1819295, by rfl⟩ : syracuseStep 2425727 = 3638591) B3638591
theorem B6468605 : Blo 1915435 6468605 := bstep (se 3 (by rfl) ⟨1212863, by rfl⟩ : syracuseStep 6468605 = 2425727) B2425727
theorem B4312403 : Blo 1915435 4312403 := bstep (se 1 (by rfl) ⟨3234302, by rfl⟩ : syracuseStep 4312403 = 6468605) B6468605
theorem B2874935 : Blo 1915435 2874935 := bstep (se 1 (by rfl) ⟨2156201, by rfl⟩ : syracuseStep 2874935 = 4312403) B4312403
theorem B1916623 : Blo 1915435 1916623 := bstep (se 1 (by rfl) ⟨1437467, by rfl⟩ : syracuseStep 1916623 = 2874935) B2874935
theorem B2874941 : Blo 1915435 2874941 := bbase (se 3 (by rfl) ⟨539051, by rfl⟩ : syracuseStep 2874941 = 1078103) (by norm_num)
theorem B1916627 : Blo 1915435 1916627 := bstep (se 1 (by rfl) ⟨1437470, by rfl⟩ : syracuseStep 1916627 = 2874941) B2874941
theorem B4312421 : Blo 1915435 4312421 := bbase (se 4 (by rfl) ⟨404289, by rfl⟩ : syracuseStep 4312421 = 808579) (by norm_num)
theorem B2874947 : Blo 1915435 2874947 := bstep (se 1 (by rfl) ⟨2156210, by rfl⟩ : syracuseStep 2874947 = 4312421) B4312421
theorem B1916631 : Blo 1915435 1916631 := bstep (se 1 (by rfl) ⟨1437473, by rfl⟩ : syracuseStep 1916631 = 2874947) B2874947
theorem B4851485 : Blo 1915435 4851485 := bbase (se 3 (by rfl) ⟨909653, by rfl⟩ : syracuseStep 4851485 = 1819307) (by norm_num)
theorem B3234323 : Blo 1915435 3234323 := bstep (se 1 (by rfl) ⟨2425742, by rfl⟩ : syracuseStep 3234323 = 4851485) B4851485
theorem B2156215 : Blo 1915435 2156215 := bstep (se 1 (by rfl) ⟨1617161, by rfl⟩ : syracuseStep 2156215 = 3234323) B3234323
theorem B2874953 : Blo 1915435 2874953 := bstep (se 2 (by rfl) ⟨1078107, by rfl⟩ : syracuseStep 2874953 = 2156215) B2156215
theorem B1916635 : Blo 1915435 1916635 := bstep (se 1 (by rfl) ⟨1437476, by rfl⟩ : syracuseStep 1916635 = 2874953) B2874953
theorem B3638621 : Blo 1915435 3638621 := bbase (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) (by norm_num)
theorem B9702989 : Blo 1915435 9702989 := bstep (se 3 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 9702989 = 3638621) B3638621
theorem B6468659 : Blo 1915435 6468659 := bstep (se 1 (by rfl) ⟨4851494, by rfl⟩ : syracuseStep 6468659 = 9702989) B9702989
theorem B4312439 : Blo 1915435 4312439 := bstep (se 1 (by rfl) ⟨3234329, by rfl⟩ : syracuseStep 4312439 = 6468659) B6468659
theorem B2874959 : Blo 1915435 2874959 := bstep (se 1 (by rfl) ⟨2156219, by rfl⟩ : syracuseStep 2874959 = 4312439) B4312439
theorem B1916639 : Blo 1915435 1916639 := bstep (se 1 (by rfl) ⟨1437479, by rfl⟩ : syracuseStep 1916639 = 2874959) B2874959
theorem B2874965 : Blo 1915435 2874965 := bbase (se 8 (by rfl) ⟨16845, by rfl⟩ : syracuseStep 2874965 = 33691) (by norm_num)
theorem B1916643 : Blo 1915435 1916643 := bstep (se 1 (by rfl) ⟨1437482, by rfl⟩ : syracuseStep 1916643 = 2874965) B2874965
theorem B8186933 : Blo 1915435 8186933 := bbase (se 5 (by rfl) ⟨383762, by rfl⟩ : syracuseStep 8186933 = 767525) (by norm_num)
theorem B5457955 : Blo 1915435 5457955 := bstep (se 1 (by rfl) ⟨4093466, by rfl⟩ : syracuseStep 5457955 = 8186933) B8186933
theorem B7277273 : Blo 1915435 7277273 := bstep (se 2 (by rfl) ⟨2728977, by rfl⟩ : syracuseStep 7277273 = 5457955) B5457955
theorem B4851515 : Blo 1915435 4851515 := bstep (se 1 (by rfl) ⟨3638636, by rfl⟩ : syracuseStep 4851515 = 7277273) B7277273
theorem B3234343 : Blo 1915435 3234343 := bstep (se 1 (by rfl) ⟨2425757, by rfl⟩ : syracuseStep 3234343 = 4851515) B4851515
theorem B4312457 : Blo 1915435 4312457 := bstep (se 2 (by rfl) ⟨1617171, by rfl⟩ : syracuseStep 4312457 = 3234343) B3234343
theorem B2874971 : Blo 1915435 2874971 := bstep (se 1 (by rfl) ⟨2156228, by rfl⟩ : syracuseStep 2874971 = 4312457) B4312457
theorem B1916647 : Blo 1915435 1916647 := bstep (se 1 (by rfl) ⟨1437485, by rfl⟩ : syracuseStep 1916647 = 2874971) B2874971
theorem B2156233 : Blo 1915435 2156233 := bbase (se 2 (by rfl) ⟨808587, by rfl⟩ : syracuseStep 2156233 = 1617175) (by norm_num)
theorem B2874977 : Blo 1915435 2874977 := bstep (se 2 (by rfl) ⟨1078116, by rfl⟩ : syracuseStep 2874977 = 2156233) B2156233
theorem B1916651 : Blo 1915435 1916651 := bstep (se 1 (by rfl) ⟨1437488, by rfl⟩ : syracuseStep 1916651 = 2874977) B2874977
theorem B3453877 : Blo 1915435 3453877 := bbase (se 5 (by rfl) ⟨161900, by rfl⟩ : syracuseStep 3453877 = 323801) (by norm_num)
theorem B4605169 : Blo 1915435 4605169 := bstep (se 2 (by rfl) ⟨1726938, by rfl⟩ : syracuseStep 4605169 = 3453877) B3453877
theorem B6140225 : Blo 1915435 6140225 := bstep (se 2 (by rfl) ⟨2302584, by rfl⟩ : syracuseStep 6140225 = 4605169) B4605169
theorem B16373933 : Blo 1915435 16373933 := bstep (se 3 (by rfl) ⟨3070112, by rfl⟩ : syracuseStep 16373933 = 6140225) B6140225
theorem B10915955 : Blo 1915435 10915955 := bstep (se 1 (by rfl) ⟨8186966, by rfl⟩ : syracuseStep 10915955 = 16373933) B16373933
theorem B7277303 : Blo 1915435 7277303 := bstep (se 1 (by rfl) ⟨5457977, by rfl⟩ : syracuseStep 7277303 = 10915955) B10915955
theorem B4851535 : Blo 1915435 4851535 := bstep (se 1 (by rfl) ⟨3638651, by rfl⟩ : syracuseStep 4851535 = 7277303) B7277303
theorem B6468713 : Blo 1915435 6468713 := bstep (se 2 (by rfl) ⟨2425767, by rfl⟩ : syracuseStep 6468713 = 4851535) B4851535
theorem B4312475 : Blo 1915435 4312475 := bstep (se 1 (by rfl) ⟨3234356, by rfl⟩ : syracuseStep 4312475 = 6468713) B6468713
theorem B2874983 : Blo 1915435 2874983 := bstep (se 1 (by rfl) ⟨2156237, by rfl⟩ : syracuseStep 2874983 = 4312475) B4312475
theorem B1916655 : Blo 1915435 1916655 := bstep (se 1 (by rfl) ⟨1437491, by rfl⟩ : syracuseStep 1916655 = 2874983) B2874983
theorem B2874989 : Blo 1915435 2874989 := bbase (se 3 (by rfl) ⟨539060, by rfl⟩ : syracuseStep 2874989 = 1078121) (by norm_num)
theorem B1916659 : Blo 1915435 1916659 := bstep (se 1 (by rfl) ⟨1437494, by rfl⟩ : syracuseStep 1916659 = 2874989) B2874989
theorem B4312493 : Blo 1915435 4312493 := bbase (se 3 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 4312493 = 1617185) (by norm_num)
theorem B2874995 : Blo 1915435 2874995 := bstep (se 1 (by rfl) ⟨2156246, by rfl⟩ : syracuseStep 2874995 = 4312493) B4312493
theorem B1916663 : Blo 1915435 1916663 := bstep (se 1 (by rfl) ⟨1437497, by rfl⟩ : syracuseStep 1916663 = 2874995) B2874995
theorem B3070133 : Blo 1915435 3070133 := bbase (se 5 (by rfl) ⟨143912, by rfl⟩ : syracuseStep 3070133 = 287825) (by norm_num)
theorem B2046755 : Blo 1915435 2046755 := bstep (se 1 (by rfl) ⟨1535066, by rfl⟩ : syracuseStep 2046755 = 3070133) B3070133
theorem B5458013 : Blo 1915435 5458013 := bstep (se 3 (by rfl) ⟨1023377, by rfl⟩ : syracuseStep 5458013 = 2046755) B2046755
theorem B3638675 : Blo 1915435 3638675 := bstep (se 1 (by rfl) ⟨2729006, by rfl⟩ : syracuseStep 3638675 = 5458013) B5458013
theorem B2425783 : Blo 1915435 2425783 := bstep (se 1 (by rfl) ⟨1819337, by rfl⟩ : syracuseStep 2425783 = 3638675) B3638675
theorem B3234377 : Blo 1915435 3234377 := bstep (se 2 (by rfl) ⟨1212891, by rfl⟩ : syracuseStep 3234377 = 2425783) B2425783
theorem B2156251 : Blo 1915435 2156251 := bstep (se 1 (by rfl) ⟨1617188, by rfl⟩ : syracuseStep 2156251 = 3234377) B3234377
theorem B2875001 : Blo 1915435 2875001 := bstep (se 2 (by rfl) ⟨1078125, by rfl⟩ : syracuseStep 2875001 = 2156251) B2156251
theorem B1916667 : Blo 1915435 1916667 := bstep (se 1 (by rfl) ⟨1437500, by rfl⟩ : syracuseStep 1916667 = 2875001) B2875001
theorem B15365429 : Blo 1915435 15365429 := bbase (se 5 (by rfl) ⟨720254, by rfl⟩ : syracuseStep 15365429 = 1440509) (by norm_num)
theorem B655591637 : Blo 1915435 655591637 := bstep (se 7 (by rfl) ⟨7682714, by rfl⟩ : syracuseStep 655591637 = 15365429) B15365429
theorem B437061091 : Blo 1915435 437061091 := bstep (se 1 (by rfl) ⟨327795818, by rfl⟩ : syracuseStep 437061091 = 655591637) B655591637
theorem B582748121 : Blo 1915435 582748121 := bstep (se 2 (by rfl) ⟨218530545, by rfl⟩ : syracuseStep 582748121 = 437061091) B437061091
theorem B388498747 : Blo 1915435 388498747 := bstep (se 1 (by rfl) ⟨291374060, by rfl⟩ : syracuseStep 388498747 = 582748121) B582748121
theorem B517998329 : Blo 1915435 517998329 := bstep (se 2 (by rfl) ⟨194249373, by rfl⟩ : syracuseStep 517998329 = 388498747) B388498747
theorem B345332219 : Blo 1915435 345332219 := bstep (se 1 (by rfl) ⟨258999164, by rfl⟩ : syracuseStep 345332219 = 517998329) B517998329
theorem B920885917 : Blo 1915435 920885917 := bstep (se 3 (by rfl) ⟨172666109, by rfl⟩ : syracuseStep 920885917 = 345332219) B345332219
theorem B1227847889 : Blo 1915435 1227847889 := bstep (se 2 (by rfl) ⟨460442958, by rfl⟩ : syracuseStep 1227847889 = 920885917) B920885917
theorem B818565259 : Blo 1915435 818565259 := bstep (se 1 (by rfl) ⟨613923944, by rfl⟩ : syracuseStep 818565259 = 1227847889) B1227847889
theorem B1091420345 : Blo 1915435 1091420345 := bstep (se 2 (by rfl) ⟨409282629, by rfl⟩ : syracuseStep 1091420345 = 818565259) B818565259
theorem B727613563 : Blo 1915435 727613563 := bstep (se 1 (by rfl) ⟨545710172, by rfl⟩ : syracuseStep 727613563 = 1091420345) B1091420345
theorem B970151417 : Blo 1915435 970151417 := bstep (se 2 (by rfl) ⟨363806781, by rfl⟩ : syracuseStep 970151417 = 727613563) B727613563
theorem B646767611 : Blo 1915435 646767611 := bstep (se 1 (by rfl) ⟨485075708, by rfl⟩ : syracuseStep 646767611 = 970151417) B970151417
theorem B431178407 : Blo 1915435 431178407 := bstep (se 1 (by rfl) ⟨323383805, by rfl⟩ : syracuseStep 431178407 = 646767611) B646767611
theorem B287452271 : Blo 1915435 287452271 := bstep (se 1 (by rfl) ⟨215589203, by rfl⟩ : syracuseStep 287452271 = 431178407) B431178407
theorem B766539389 : Blo 1915435 766539389 := bstep (se 3 (by rfl) ⟨143726135, by rfl⟩ : syracuseStep 766539389 = 287452271) B287452271
theorem B511026259 : Blo 1915435 511026259 := bstep (se 1 (by rfl) ⟨383269694, by rfl⟩ : syracuseStep 511026259 = 766539389) B766539389
theorem B681368345 : Blo 1915435 681368345 := bstep (se 2 (by rfl) ⟨255513129, by rfl⟩ : syracuseStep 681368345 = 511026259) B511026259
theorem B454245563 : Blo 1915435 454245563 := bstep (se 1 (by rfl) ⟨340684172, by rfl⟩ : syracuseStep 454245563 = 681368345) B681368345
theorem B302830375 : Blo 1915435 302830375 := bstep (se 1 (by rfl) ⟨227122781, by rfl⟩ : syracuseStep 302830375 = 454245563) B454245563
theorem B403773833 : Blo 1915435 403773833 := bstep (se 2 (by rfl) ⟨151415187, by rfl⟩ : syracuseStep 403773833 = 302830375) B302830375
theorem B1076730221 : Blo 1915435 1076730221 := bstep (se 3 (by rfl) ⟨201886916, by rfl⟩ : syracuseStep 1076730221 = 403773833) B403773833
theorem B717820147 : Blo 1915435 717820147 := bstep (se 1 (by rfl) ⟨538365110, by rfl⟩ : syracuseStep 717820147 = 1076730221) B1076730221
theorem B957093529 : Blo 1915435 957093529 := bstep (se 2 (by rfl) ⟨358910073, by rfl⟩ : syracuseStep 957093529 = 717820147) B717820147
theorem B1276124705 : Blo 1915435 1276124705 := bstep (se 2 (by rfl) ⟨478546764, by rfl⟩ : syracuseStep 1276124705 = 957093529) B957093529
theorem B850749803 : Blo 1915435 850749803 := bstep (se 1 (by rfl) ⟨638062352, by rfl⟩ : syracuseStep 850749803 = 1276124705) B1276124705
theorem B567166535 : Blo 1915435 567166535 := bstep (se 1 (by rfl) ⟨425374901, by rfl⟩ : syracuseStep 567166535 = 850749803) B850749803
theorem B378111023 : Blo 1915435 378111023 := bstep (se 1 (by rfl) ⟨283583267, by rfl⟩ : syracuseStep 378111023 = 567166535) B567166535
theorem B252074015 : Blo 1915435 252074015 := bstep (se 1 (by rfl) ⟨189055511, by rfl⟩ : syracuseStep 252074015 = 378111023) B378111023
theorem B168049343 : Blo 1915435 168049343 := bstep (se 1 (by rfl) ⟨126037007, by rfl⟩ : syracuseStep 168049343 = 252074015) B252074015
theorem B112032895 : Blo 1915435 112032895 := bstep (se 1 (by rfl) ⟨84024671, by rfl⟩ : syracuseStep 112032895 = 168049343) B168049343
theorem B149377193 : Blo 1915435 149377193 := bstep (se 2 (by rfl) ⟨56016447, by rfl⟩ : syracuseStep 149377193 = 112032895) B112032895
theorem B99584795 : Blo 1915435 99584795 := bstep (se 1 (by rfl) ⟨74688596, by rfl⟩ : syracuseStep 99584795 = 149377193) B149377193
theorem B66389863 : Blo 1915435 66389863 := bstep (se 1 (by rfl) ⟨49792397, by rfl⟩ : syracuseStep 66389863 = 99584795) B99584795
theorem B88519817 : Blo 1915435 88519817 := bstep (se 2 (by rfl) ⟨33194931, by rfl⟩ : syracuseStep 88519817 = 66389863) B66389863
theorem B59013211 : Blo 1915435 59013211 := bstep (se 1 (by rfl) ⟨44259908, by rfl⟩ : syracuseStep 59013211 = 88519817) B88519817
theorem B78684281 : Blo 1915435 78684281 := bstep (se 2 (by rfl) ⟨29506605, by rfl⟩ : syracuseStep 78684281 = 59013211) B59013211
theorem B52456187 : Blo 1915435 52456187 := bstep (se 1 (by rfl) ⟨39342140, by rfl⟩ : syracuseStep 52456187 = 78684281) B78684281
theorem B34970791 : Blo 1915435 34970791 := bstep (se 1 (by rfl) ⟨26228093, by rfl⟩ : syracuseStep 34970791 = 52456187) B52456187
theorem B46627721 : Blo 1915435 46627721 := bstep (se 2 (by rfl) ⟨17485395, by rfl⟩ : syracuseStep 46627721 = 34970791) B34970791
theorem B31085147 : Blo 1915435 31085147 := bstep (se 1 (by rfl) ⟨23313860, by rfl⟩ : syracuseStep 31085147 = 46627721) B46627721
theorem B82893725 : Blo 1915435 82893725 := bstep (se 3 (by rfl) ⟨15542573, by rfl⟩ : syracuseStep 82893725 = 31085147) B31085147
theorem B55262483 : Blo 1915435 55262483 := bstep (se 1 (by rfl) ⟨41446862, by rfl⟩ : syracuseStep 55262483 = 82893725) B82893725
theorem B36841655 : Blo 1915435 36841655 := bstep (se 1 (by rfl) ⟨27631241, by rfl⟩ : syracuseStep 36841655 = 55262483) B55262483
theorem B24561103 : Blo 1915435 24561103 := bstep (se 1 (by rfl) ⟨18420827, by rfl⟩ : syracuseStep 24561103 = 36841655) B36841655
theorem B32748137 : Blo 1915435 32748137 := bstep (se 2 (by rfl) ⟨12280551, by rfl⟩ : syracuseStep 32748137 = 24561103) B24561103
theorem B21832091 : Blo 1915435 21832091 := bstep (se 1 (by rfl) ⟨16374068, by rfl⟩ : syracuseStep 21832091 = 32748137) B32748137
theorem B14554727 : Blo 1915435 14554727 := bstep (se 1 (by rfl) ⟨10916045, by rfl⟩ : syracuseStep 14554727 = 21832091) B21832091
theorem B9703151 : Blo 1915435 9703151 := bstep (se 1 (by rfl) ⟨7277363, by rfl⟩ : syracuseStep 9703151 = 14554727) B14554727
theorem B6468767 : Blo 1915435 6468767 := bstep (se 1 (by rfl) ⟨4851575, by rfl⟩ : syracuseStep 6468767 = 9703151) B9703151
theorem B4312511 : Blo 1915435 4312511 := bstep (se 1 (by rfl) ⟨3234383, by rfl⟩ : syracuseStep 4312511 = 6468767) B6468767
theorem B2875007 : Blo 1915435 2875007 := bstep (se 1 (by rfl) ⟨2156255, by rfl⟩ : syracuseStep 2875007 = 4312511) B4312511
theorem B1916671 : Blo 1915435 1916671 := bstep (se 1 (by rfl) ⟨1437503, by rfl⟩ : syracuseStep 1916671 = 2875007) B2875007
theorem B2875013 : Blo 1915435 2875013 := bbase (se 4 (by rfl) ⟨269532, by rfl⟩ : syracuseStep 2875013 = 539065) (by norm_num)
theorem B1916675 : Blo 1915435 1916675 := bstep (se 1 (by rfl) ⟨1437506, by rfl⟩ : syracuseStep 1916675 = 2875013) B2875013
theorem B3234397 : Blo 1915435 3234397 := bbase (se 3 (by rfl) ⟨606449, by rfl⟩ : syracuseStep 3234397 = 1212899) (by norm_num)
theorem B4312529 : Blo 1915435 4312529 := bstep (se 2 (by rfl) ⟨1617198, by rfl⟩ : syracuseStep 4312529 = 3234397) B3234397
theorem B2875019 : Blo 1915435 2875019 := bstep (se 1 (by rfl) ⟨2156264, by rfl⟩ : syracuseStep 2875019 = 4312529) B4312529
theorem B1916679 : Blo 1915435 1916679 := bstep (se 1 (by rfl) ⟨1437509, by rfl⟩ : syracuseStep 1916679 = 2875019) B2875019
theorem B2156269 : Blo 1915435 2156269 := bbase (se 3 (by rfl) ⟨404300, by rfl⟩ : syracuseStep 2156269 = 808601) (by norm_num)
theorem B2875025 : Blo 1915435 2875025 := bstep (se 2 (by rfl) ⟨1078134, by rfl⟩ : syracuseStep 2875025 = 2156269) B2156269
theorem B1916683 : Blo 1915435 1916683 := bstep (se 1 (by rfl) ⟨1437512, by rfl⟩ : syracuseStep 1916683 = 2875025) B2875025
theorem B6468821 : Blo 1915435 6468821 := bbase (se 7 (by rfl) ⟨75806, by rfl⟩ : syracuseStep 6468821 = 151613) (by norm_num)
theorem B4312547 : Blo 1915435 4312547 := bstep (se 1 (by rfl) ⟨3234410, by rfl⟩ : syracuseStep 4312547 = 6468821) B6468821
theorem B2875031 : Blo 1915435 2875031 := bstep (se 1 (by rfl) ⟨2156273, by rfl⟩ : syracuseStep 2875031 = 4312547) B4312547
theorem B1916687 : Blo 1915435 1916687 := bstep (se 1 (by rfl) ⟨1437515, by rfl⟩ : syracuseStep 1916687 = 2875031) B2875031
theorem B2875037 : Blo 1915435 2875037 := bbase (se 3 (by rfl) ⟨539069, by rfl⟩ : syracuseStep 2875037 = 1078139) (by norm_num)
theorem B1916691 : Blo 1915435 1916691 := bstep (se 1 (by rfl) ⟨1437518, by rfl⟩ : syracuseStep 1916691 = 2875037) B2875037
theorem B4312565 : Blo 1915435 4312565 := bbase (se 5 (by rfl) ⟨202151, by rfl⟩ : syracuseStep 4312565 = 404303) (by norm_num)
theorem B2875043 : Blo 1915435 2875043 := bstep (se 1 (by rfl) ⟨2156282, by rfl⟩ : syracuseStep 2875043 = 4312565) B4312565
theorem B1916695 : Blo 1915435 1916695 := bstep (se 1 (by rfl) ⟨1437521, by rfl⟩ : syracuseStep 1916695 = 2875043) B2875043
theorem B3885701 : Blo 1915435 3885701 := bbase (se 4 (by rfl) ⟨364284, by rfl⟩ : syracuseStep 3885701 = 728569) (by norm_num)
theorem B41447477 : Blo 1915435 41447477 := bstep (se 5 (by rfl) ⟨1942850, by rfl⟩ : syracuseStep 41447477 = 3885701) B3885701
theorem B27631651 : Blo 1915435 27631651 := bstep (se 1 (by rfl) ⟨20723738, by rfl⟩ : syracuseStep 27631651 = 41447477) B41447477
theorem B36842201 : Blo 1915435 36842201 := bstep (se 2 (by rfl) ⟨13815825, by rfl⟩ : syracuseStep 36842201 = 27631651) B27631651
theorem B24561467 : Blo 1915435 24561467 := bstep (se 1 (by rfl) ⟨18421100, by rfl⟩ : syracuseStep 24561467 = 36842201) B36842201
theorem B16374311 : Blo 1915435 16374311 := bstep (se 1 (by rfl) ⟨12280733, by rfl⟩ : syracuseStep 16374311 = 24561467) B24561467
theorem B10916207 : Blo 1915435 10916207 := bstep (se 1 (by rfl) ⟨8187155, by rfl⟩ : syracuseStep 10916207 = 16374311) B16374311
theorem B7277471 : Blo 1915435 7277471 := bstep (se 1 (by rfl) ⟨5458103, by rfl⟩ : syracuseStep 7277471 = 10916207) B10916207
theorem B4851647 : Blo 1915435 4851647 := bstep (se 1 (by rfl) ⟨3638735, by rfl⟩ : syracuseStep 4851647 = 7277471) B7277471
theorem B3234431 : Blo 1915435 3234431 := bstep (se 1 (by rfl) ⟨2425823, by rfl⟩ : syracuseStep 3234431 = 4851647) B4851647
theorem B2156287 : Blo 1915435 2156287 := bstep (se 1 (by rfl) ⟨1617215, by rfl⟩ : syracuseStep 2156287 = 3234431) B3234431
theorem B2875049 : Blo 1915435 2875049 := bstep (se 2 (by rfl) ⟨1078143, by rfl⟩ : syracuseStep 2875049 = 2156287) B2156287
theorem B1916699 : Blo 1915435 1916699 := bstep (se 1 (by rfl) ⟨1437524, by rfl⟩ : syracuseStep 1916699 = 2875049) B2875049
theorem B2046793 : Blo 1915435 2046793 := bbase (se 2 (by rfl) ⟨767547, by rfl⟩ : syracuseStep 2046793 = 1535095) (by norm_num)
theorem B2729057 : Blo 1915435 2729057 := bstep (se 2 (by rfl) ⟨1023396, by rfl⟩ : syracuseStep 2729057 = 2046793) B2046793
theorem B7277485 : Blo 1915435 7277485 := bstep (se 3 (by rfl) ⟨1364528, by rfl⟩ : syracuseStep 7277485 = 2729057) B2729057
theorem B9703313 : Blo 1915435 9703313 := bstep (se 2 (by rfl) ⟨3638742, by rfl⟩ : syracuseStep 9703313 = 7277485) B7277485
theorem B6468875 : Blo 1915435 6468875 := bstep (se 1 (by rfl) ⟨4851656, by rfl⟩ : syracuseStep 6468875 = 9703313) B9703313
theorem B4312583 : Blo 1915435 4312583 := bstep (se 1 (by rfl) ⟨3234437, by rfl⟩ : syracuseStep 4312583 = 6468875) B6468875
theorem B2875055 : Blo 1915435 2875055 := bstep (se 1 (by rfl) ⟨2156291, by rfl⟩ : syracuseStep 2875055 = 4312583) B4312583
theorem B1916703 : Blo 1915435 1916703 := bstep (se 1 (by rfl) ⟨1437527, by rfl⟩ : syracuseStep 1916703 = 2875055) B2875055
theorem B2875061 : Blo 1915435 2875061 := bbase (se 5 (by rfl) ⟨134768, by rfl⟩ : syracuseStep 2875061 = 269537) (by norm_num)
theorem B1916707 : Blo 1915435 1916707 := bstep (se 1 (by rfl) ⟨1437530, by rfl⟩ : syracuseStep 1916707 = 2875061) B2875061
theorem B4851677 : Blo 1915435 4851677 := bbase (se 3 (by rfl) ⟨909689, by rfl⟩ : syracuseStep 4851677 = 1819379) (by norm_num)
theorem B3234451 : Blo 1915435 3234451 := bstep (se 1 (by rfl) ⟨2425838, by rfl⟩ : syracuseStep 3234451 = 4851677) B4851677
theorem B4312601 : Blo 1915435 4312601 := bstep (se 2 (by rfl) ⟨1617225, by rfl⟩ : syracuseStep 4312601 = 3234451) B3234451
theorem B2875067 : Blo 1915435 2875067 := bstep (se 1 (by rfl) ⟨2156300, by rfl⟩ : syracuseStep 2875067 = 4312601) B4312601
theorem B1916711 : Blo 1915435 1916711 := bstep (se 1 (by rfl) ⟨1437533, by rfl⟩ : syracuseStep 1916711 = 2875067) B2875067
theorem B2156305 : Blo 1915435 2156305 := bbase (se 2 (by rfl) ⟨808614, by rfl⟩ : syracuseStep 2156305 = 1617229) (by norm_num)
theorem B2875073 : Blo 1915435 2875073 := bstep (se 2 (by rfl) ⟨1078152, by rfl⟩ : syracuseStep 2875073 = 2156305) B2156305
theorem B1916715 : Blo 1915435 1916715 := bstep (se 1 (by rfl) ⟨1437536, by rfl⟩ : syracuseStep 1916715 = 2875073) B2875073
theorem B3638773 : Blo 1915435 3638773 := bbase (se 5 (by rfl) ⟨170567, by rfl⟩ : syracuseStep 3638773 = 341135) (by norm_num)
theorem B4851697 : Blo 1915435 4851697 := bstep (se 2 (by rfl) ⟨1819386, by rfl⟩ : syracuseStep 4851697 = 3638773) B3638773
theorem B6468929 : Blo 1915435 6468929 := bstep (se 2 (by rfl) ⟨2425848, by rfl⟩ : syracuseStep 6468929 = 4851697) B4851697
theorem B4312619 : Blo 1915435 4312619 := bstep (se 1 (by rfl) ⟨3234464, by rfl⟩ : syracuseStep 4312619 = 6468929) B6468929
theorem B2875079 : Blo 1915435 2875079 := bstep (se 1 (by rfl) ⟨2156309, by rfl⟩ : syracuseStep 2875079 = 4312619) B4312619
theorem B1916719 : Blo 1915435 1916719 := bstep (se 1 (by rfl) ⟨1437539, by rfl⟩ : syracuseStep 1916719 = 2875079) B2875079
theorem B2875085 : Blo 1915435 2875085 := bbase (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) (by norm_num)
theorem B1916723 : Blo 1915435 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B4312637 : Blo 1915435 4312637 := bbase (se 3 (by rfl) ⟨808619, by rfl⟩ : syracuseStep 4312637 = 1617239) (by norm_num)
theorem B2875091 : Blo 1915435 2875091 := bstep (se 1 (by rfl) ⟨2156318, by rfl⟩ : syracuseStep 2875091 = 4312637) B4312637
theorem B1916727 : Blo 1915435 1916727 := bstep (se 1 (by rfl) ⟨1437545, by rfl⟩ : syracuseStep 1916727 = 2875091) B2875091
theorem B3234485 : Blo 1915435 3234485 := bbase (se 5 (by rfl) ⟨151616, by rfl⟩ : syracuseStep 3234485 = 303233) (by norm_num)
theorem B2156323 : Blo 1915435 2156323 := bstep (se 1 (by rfl) ⟨1617242, by rfl⟩ : syracuseStep 2156323 = 3234485) B3234485
theorem B2875097 : Blo 1915435 2875097 := bstep (se 2 (by rfl) ⟨1078161, by rfl⟩ : syracuseStep 2875097 = 2156323) B2156323
theorem B1916731 : Blo 1915435 1916731 := bstep (se 1 (by rfl) ⟨1437548, by rfl⟩ : syracuseStep 1916731 = 2875097) B2875097
theorem B2302681 : Blo 1915435 2302681 := bbase (se 2 (by rfl) ⟨863505, by rfl⟩ : syracuseStep 2302681 = 1727011) (by norm_num)
theorem B3070241 : Blo 1915435 3070241 := bstep (se 2 (by rfl) ⟨1151340, by rfl⟩ : syracuseStep 3070241 = 2302681) B2302681
theorem B2046827 : Blo 1915435 2046827 := bstep (se 1 (by rfl) ⟨1535120, by rfl⟩ : syracuseStep 2046827 = 3070241) B3070241
theorem B5458205 : Blo 1915435 5458205 := bstep (se 3 (by rfl) ⟨1023413, by rfl⟩ : syracuseStep 5458205 = 2046827) B2046827
theorem B14555213 : Blo 1915435 14555213 := bstep (se 3 (by rfl) ⟨2729102, by rfl⟩ : syracuseStep 14555213 = 5458205) B5458205
theorem B9703475 : Blo 1915435 9703475 := bstep (se 1 (by rfl) ⟨7277606, by rfl⟩ : syracuseStep 9703475 = 14555213) B14555213
theorem B6468983 : Blo 1915435 6468983 := bstep (se 1 (by rfl) ⟨4851737, by rfl⟩ : syracuseStep 6468983 = 9703475) B9703475
theorem B4312655 : Blo 1915435 4312655 := bstep (se 1 (by rfl) ⟨3234491, by rfl⟩ : syracuseStep 4312655 = 6468983) B6468983
theorem B2875103 : Blo 1915435 2875103 := bstep (se 1 (by rfl) ⟨2156327, by rfl⟩ : syracuseStep 2875103 = 4312655) B4312655
theorem B1916735 : Blo 1915435 1916735 := bstep (se 1 (by rfl) ⟨1437551, by rfl⟩ : syracuseStep 1916735 = 2875103) B2875103
theorem B2875109 : Blo 1915435 2875109 := bbase (se 4 (by rfl) ⟨269541, by rfl⟩ : syracuseStep 2875109 = 539083) (by norm_num)
theorem B1916739 : Blo 1915435 1916739 := bstep (se 1 (by rfl) ⟨1437554, by rfl⟩ : syracuseStep 1916739 = 2875109) B2875109
theorem B5458229 : Blo 1915435 5458229 := bbase (se 5 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 5458229 = 511709) (by norm_num)
theorem B3638819 : Blo 1915435 3638819 := bstep (se 1 (by rfl) ⟨2729114, by rfl⟩ : syracuseStep 3638819 = 5458229) B5458229
theorem B2425879 : Blo 1915435 2425879 := bstep (se 1 (by rfl) ⟨1819409, by rfl⟩ : syracuseStep 2425879 = 3638819) B3638819
theorem B3234505 : Blo 1915435 3234505 := bstep (se 2 (by rfl) ⟨1212939, by rfl⟩ : syracuseStep 3234505 = 2425879) B2425879
theorem B4312673 : Blo 1915435 4312673 := bstep (se 2 (by rfl) ⟨1617252, by rfl⟩ : syracuseStep 4312673 = 3234505) B3234505
theorem B2875115 : Blo 1915435 2875115 := bstep (se 1 (by rfl) ⟨2156336, by rfl⟩ : syracuseStep 2875115 = 4312673) B4312673
theorem B1916743 : Blo 1915435 1916743 := bstep (se 1 (by rfl) ⟨1437557, by rfl⟩ : syracuseStep 1916743 = 2875115) B2875115
theorem B2156341 : Blo 1915435 2156341 := bbase (se 5 (by rfl) ⟨101078, by rfl⟩ : syracuseStep 2156341 = 202157) (by norm_num)
theorem B2875121 : Blo 1915435 2875121 := bstep (se 2 (by rfl) ⟨1078170, by rfl⟩ : syracuseStep 2875121 = 2156341) B2156341
theorem B1916747 : Blo 1915435 1916747 := bstep (se 1 (by rfl) ⟨1437560, by rfl⟩ : syracuseStep 1916747 = 2875121) B2875121
theorem B2425889 : Blo 1915435 2425889 := bbase (se 2 (by rfl) ⟨909708, by rfl⟩ : syracuseStep 2425889 = 1819417) (by norm_num)
theorem B6469037 : Blo 1915435 6469037 := bstep (se 3 (by rfl) ⟨1212944, by rfl⟩ : syracuseStep 6469037 = 2425889) B2425889
theorem B4312691 : Blo 1915435 4312691 := bstep (se 1 (by rfl) ⟨3234518, by rfl⟩ : syracuseStep 4312691 = 6469037) B6469037
theorem B2875127 : Blo 1915435 2875127 := bstep (se 1 (by rfl) ⟨2156345, by rfl⟩ : syracuseStep 2875127 = 4312691) B4312691
theorem B1916751 : Blo 1915435 1916751 := bstep (se 1 (by rfl) ⟨1437563, by rfl⟩ : syracuseStep 1916751 = 2875127) B2875127
theorem B2875133 : Blo 1915435 2875133 := bbase (se 3 (by rfl) ⟨539087, by rfl⟩ : syracuseStep 2875133 = 1078175) (by norm_num)
theorem B1916755 : Blo 1915435 1916755 := bstep (se 1 (by rfl) ⟨1437566, by rfl⟩ : syracuseStep 1916755 = 2875133) B2875133
theorem B4312709 : Blo 1915435 4312709 := bbase (se 4 (by rfl) ⟨404316, by rfl⟩ : syracuseStep 4312709 = 808633) (by norm_num)
theorem B2875139 : Blo 1915435 2875139 := bstep (se 1 (by rfl) ⟨2156354, by rfl⟩ : syracuseStep 2875139 = 4312709) B4312709
theorem B1916759 : Blo 1915435 1916759 := bstep (se 1 (by rfl) ⟨1437569, by rfl⟩ : syracuseStep 1916759 = 2875139) B2875139
theorem B6224357 : Blo 1915435 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B4149571 : Blo 1915435 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B5532761 : Blo 1915435 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B3688507 : Blo 1915435 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B4918009 : Blo 1915435 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B6557345 : Blo 1915435 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B4371563 : Blo 1915435 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B2914375 : Blo 1915435 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B3885833 : Blo 1915435 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B2590555 : Blo 1915435 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B3454073 : Blo 1915435 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B2302715 : Blo 1915435 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B6140573 : Blo 1915435 6140573 := bstep (se 3 (by rfl) ⟨1151357, by rfl⟩ : syracuseStep 6140573 = 2302715) B2302715
theorem B4093715 : Blo 1915435 4093715 := bstep (se 1 (by rfl) ⟨3070286, by rfl⟩ : syracuseStep 4093715 = 6140573) B6140573
theorem B2729143 : Blo 1915435 2729143 := bstep (se 1 (by rfl) ⟨2046857, by rfl⟩ : syracuseStep 2729143 = 4093715) B4093715
theorem B3638857 : Blo 1915435 3638857 := bstep (se 2 (by rfl) ⟨1364571, by rfl⟩ : syracuseStep 3638857 = 2729143) B2729143
theorem B4851809 : Blo 1915435 4851809 := bstep (se 2 (by rfl) ⟨1819428, by rfl⟩ : syracuseStep 4851809 = 3638857) B3638857
theorem B3234539 : Blo 1915435 3234539 := bstep (se 1 (by rfl) ⟨2425904, by rfl⟩ : syracuseStep 3234539 = 4851809) B4851809
theorem B2156359 : Blo 1915435 2156359 := bstep (se 1 (by rfl) ⟨1617269, by rfl⟩ : syracuseStep 2156359 = 3234539) B3234539
theorem B2875145 : Blo 1915435 2875145 := bstep (se 2 (by rfl) ⟨1078179, by rfl⟩ : syracuseStep 2875145 = 2156359) B2156359
theorem B1916763 : Blo 1915435 1916763 := bstep (se 1 (by rfl) ⟨1437572, by rfl⟩ : syracuseStep 1916763 = 2875145) B2875145
theorem B9703637 : Blo 1915435 9703637 := bbase (se 7 (by rfl) ⟨113714, by rfl⟩ : syracuseStep 9703637 = 227429) (by norm_num)
theorem B6469091 : Blo 1915435 6469091 := bstep (se 1 (by rfl) ⟨4851818, by rfl⟩ : syracuseStep 6469091 = 9703637) B9703637
theorem B4312727 : Blo 1915435 4312727 := bstep (se 1 (by rfl) ⟨3234545, by rfl⟩ : syracuseStep 4312727 = 6469091) B6469091
theorem B2875151 : Blo 1915435 2875151 := bstep (se 1 (by rfl) ⟨2156363, by rfl⟩ : syracuseStep 2875151 = 4312727) B4312727
theorem B1916767 : Blo 1915435 1916767 := bstep (se 1 (by rfl) ⟨1437575, by rfl⟩ : syracuseStep 1916767 = 2875151) B2875151
theorem B2875157 : Blo 1915435 2875157 := bbase (se 6 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 2875157 = 134773) (by norm_num)
theorem B1916771 : Blo 1915435 1916771 := bstep (se 1 (by rfl) ⟨1437578, by rfl⟩ : syracuseStep 1916771 = 2875157) B2875157
theorem B4668293 : Blo 1915435 4668293 := bbase (se 4 (by rfl) ⟨437652, by rfl⟩ : syracuseStep 4668293 = 875305) (by norm_num)
theorem B3112195 : Blo 1915435 3112195 := bstep (se 1 (by rfl) ⟨2334146, by rfl⟩ : syracuseStep 3112195 = 4668293) B4668293
theorem B4149593 : Blo 1915435 4149593 := bstep (se 2 (by rfl) ⟨1556097, by rfl⟩ : syracuseStep 4149593 = 3112195) B3112195
theorem B2766395 : Blo 1915435 2766395 := bstep (se 1 (by rfl) ⟨2074796, by rfl⟩ : syracuseStep 2766395 = 4149593) B4149593
theorem B7377053 : Blo 1915435 7377053 := bstep (se 3 (by rfl) ⟨1383197, by rfl⟩ : syracuseStep 7377053 = 2766395) B2766395
theorem B19672141 : Blo 1915435 19672141 := bstep (se 3 (by rfl) ⟨3688526, by rfl⟩ : syracuseStep 19672141 = 7377053) B7377053
theorem B26229521 : Blo 1915435 26229521 := bstep (se 2 (by rfl) ⟨9836070, by rfl⟩ : syracuseStep 26229521 = 19672141) B19672141
theorem B17486347 : Blo 1915435 17486347 := bstep (se 1 (by rfl) ⟨13114760, by rfl⟩ : syracuseStep 17486347 = 26229521) B26229521
theorem B23315129 : Blo 1915435 23315129 := bstep (se 2 (by rfl) ⟨8743173, by rfl⟩ : syracuseStep 23315129 = 17486347) B17486347
theorem B15543419 : Blo 1915435 15543419 := bstep (se 1 (by rfl) ⟨11657564, by rfl⟩ : syracuseStep 15543419 = 23315129) B23315129
theorem B41449117 : Blo 1915435 41449117 := bstep (se 3 (by rfl) ⟨7771709, by rfl⟩ : syracuseStep 41449117 = 15543419) B15543419
theorem B55265489 : Blo 1915435 55265489 := bstep (se 2 (by rfl) ⟨20724558, by rfl⟩ : syracuseStep 55265489 = 41449117) B41449117
theorem B36843659 : Blo 1915435 36843659 := bstep (se 1 (by rfl) ⟨27632744, by rfl⟩ : syracuseStep 36843659 = 55265489) B55265489
theorem B24562439 : Blo 1915435 24562439 := bstep (se 1 (by rfl) ⟨18421829, by rfl⟩ : syracuseStep 24562439 = 36843659) B36843659
theorem B16374959 : Blo 1915435 16374959 := bstep (se 1 (by rfl) ⟨12281219, by rfl⟩ : syracuseStep 16374959 = 24562439) B24562439
theorem B10916639 : Blo 1915435 10916639 := bstep (se 1 (by rfl) ⟨8187479, by rfl⟩ : syracuseStep 10916639 = 16374959) B16374959
theorem B7277759 : Blo 1915435 7277759 := bstep (se 1 (by rfl) ⟨5458319, by rfl⟩ : syracuseStep 7277759 = 10916639) B10916639
theorem B4851839 : Blo 1915435 4851839 := bstep (se 1 (by rfl) ⟨3638879, by rfl⟩ : syracuseStep 4851839 = 7277759) B7277759
theorem B3234559 : Blo 1915435 3234559 := bstep (se 1 (by rfl) ⟨2425919, by rfl⟩ : syracuseStep 3234559 = 4851839) B4851839
theorem B4312745 : Blo 1915435 4312745 := bstep (se 2 (by rfl) ⟨1617279, by rfl⟩ : syracuseStep 4312745 = 3234559) B3234559
theorem B2875163 : Blo 1915435 2875163 := bstep (se 1 (by rfl) ⟨2156372, by rfl⟩ : syracuseStep 2875163 = 4312745) B4312745
theorem B1916775 : Blo 1915435 1916775 := bstep (se 1 (by rfl) ⟨1437581, by rfl⟩ : syracuseStep 1916775 = 2875163) B2875163
theorem B2156377 : Blo 1915435 2156377 := bbase (se 2 (by rfl) ⟨808641, by rfl⟩ : syracuseStep 2156377 = 1617283) (by norm_num)
theorem B2875169 : Blo 1915435 2875169 := bstep (se 2 (by rfl) ⟨1078188, by rfl⟩ : syracuseStep 2875169 = 2156377) B2156377
theorem B1916779 : Blo 1915435 1916779 := bstep (se 1 (by rfl) ⟨1437584, by rfl⟩ : syracuseStep 1916779 = 2875169) B2875169
theorem B4093757 : Blo 1915435 4093757 := bbase (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) (by norm_num)
theorem B2729171 : Blo 1915435 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B7277789 : Blo 1915435 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B4851859 : Blo 1915435 4851859 := bstep (se 1 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 4851859 = 7277789) B7277789
theorem B6469145 : Blo 1915435 6469145 := bstep (se 2 (by rfl) ⟨2425929, by rfl⟩ : syracuseStep 6469145 = 4851859) B4851859
theorem B4312763 : Blo 1915435 4312763 := bstep (se 1 (by rfl) ⟨3234572, by rfl⟩ : syracuseStep 4312763 = 6469145) B6469145
theorem B2875175 : Blo 1915435 2875175 := bstep (se 1 (by rfl) ⟨2156381, by rfl⟩ : syracuseStep 2875175 = 4312763) B4312763
theorem B1916783 : Blo 1915435 1916783 := bstep (se 1 (by rfl) ⟨1437587, by rfl⟩ : syracuseStep 1916783 = 2875175) B2875175
theorem B2875181 : Blo 1915435 2875181 := bbase (se 3 (by rfl) ⟨539096, by rfl⟩ : syracuseStep 2875181 = 1078193) (by norm_num)
theorem B1916787 : Blo 1915435 1916787 := bstep (se 1 (by rfl) ⟨1437590, by rfl⟩ : syracuseStep 1916787 = 2875181) B2875181
theorem B4312781 : Blo 1915435 4312781 := bbase (se 3 (by rfl) ⟨808646, by rfl⟩ : syracuseStep 4312781 = 1617293) (by norm_num)
theorem B2875187 : Blo 1915435 2875187 := bstep (se 1 (by rfl) ⟨2156390, by rfl⟩ : syracuseStep 2875187 = 4312781) B4312781
theorem B1916791 : Blo 1915435 1916791 := bstep (se 1 (by rfl) ⟨1437593, by rfl⟩ : syracuseStep 1916791 = 2875187) B2875187
theorem B2425945 : Blo 1915435 2425945 := bbase (se 2 (by rfl) ⟨909729, by rfl⟩ : syracuseStep 2425945 = 1819459) (by norm_num)
theorem B3234593 : Blo 1915435 3234593 := bstep (se 2 (by rfl) ⟨1212972, by rfl⟩ : syracuseStep 3234593 = 2425945) B2425945
theorem B2156395 : Blo 1915435 2156395 := bstep (se 1 (by rfl) ⟨1617296, by rfl⟩ : syracuseStep 2156395 = 3234593) B3234593
theorem B2875193 : Blo 1915435 2875193 := bstep (se 2 (by rfl) ⟨1078197, by rfl⟩ : syracuseStep 2875193 = 2156395) B2156395
theorem B1916795 : Blo 1915435 1916795 := bstep (se 1 (by rfl) ⟨1437596, by rfl⟩ : syracuseStep 1916795 = 2875193) B2875193
theorem B5181205 : Blo 1915435 5181205 := bbase (se 6 (by rfl) ⟨121434, by rfl⟩ : syracuseStep 5181205 = 242869) (by norm_num)
theorem B6908273 : Blo 1915435 6908273 := bstep (se 2 (by rfl) ⟨2590602, by rfl⟩ : syracuseStep 6908273 = 5181205) B5181205
theorem B4605515 : Blo 1915435 4605515 := bstep (se 1 (by rfl) ⟨3454136, by rfl⟩ : syracuseStep 4605515 = 6908273) B6908273
theorem B3070343 : Blo 1915435 3070343 := bstep (se 1 (by rfl) ⟨2302757, by rfl⟩ : syracuseStep 3070343 = 4605515) B4605515
theorem B8187581 : Blo 1915435 8187581 := bstep (se 3 (by rfl) ⟨1535171, by rfl⟩ : syracuseStep 8187581 = 3070343) B3070343
theorem B21833549 : Blo 1915435 21833549 := bstep (se 3 (by rfl) ⟨4093790, by rfl⟩ : syracuseStep 21833549 = 8187581) B8187581
theorem B14555699 : Blo 1915435 14555699 := bstep (se 1 (by rfl) ⟨10916774, by rfl⟩ : syracuseStep 14555699 = 21833549) B21833549
theorem B9703799 : Blo 1915435 9703799 := bstep (se 1 (by rfl) ⟨7277849, by rfl⟩ : syracuseStep 9703799 = 14555699) B14555699
theorem B6469199 : Blo 1915435 6469199 := bstep (se 1 (by rfl) ⟨4851899, by rfl⟩ : syracuseStep 6469199 = 9703799) B9703799
theorem B4312799 : Blo 1915435 4312799 := bstep (se 1 (by rfl) ⟨3234599, by rfl⟩ : syracuseStep 4312799 = 6469199) B6469199
theorem B2875199 : Blo 1915435 2875199 := bstep (se 1 (by rfl) ⟨2156399, by rfl⟩ : syracuseStep 2875199 = 4312799) B4312799
theorem B1916799 : Blo 1915435 1916799 := bstep (se 1 (by rfl) ⟨1437599, by rfl⟩ : syracuseStep 1916799 = 2875199) B2875199
theorem B2875205 : Blo 1915435 2875205 := bbase (se 4 (by rfl) ⟨269550, by rfl⟩ : syracuseStep 2875205 = 539101) (by norm_num)
theorem B1916803 : Blo 1915435 1916803 := bstep (se 1 (by rfl) ⟨1437602, by rfl⟩ : syracuseStep 1916803 = 2875205) B2875205
theorem B3234613 : Blo 1915435 3234613 := bbase (se 5 (by rfl) ⟨151622, by rfl⟩ : syracuseStep 3234613 = 303245) (by norm_num)
theorem B4312817 : Blo 1915435 4312817 := bstep (se 2 (by rfl) ⟨1617306, by rfl⟩ : syracuseStep 4312817 = 3234613) B3234613
theorem B2875211 : Blo 1915435 2875211 := bstep (se 1 (by rfl) ⟨2156408, by rfl⟩ : syracuseStep 2875211 = 4312817) B4312817
theorem B1916807 : Blo 1915435 1916807 := bstep (se 1 (by rfl) ⟨1437605, by rfl⟩ : syracuseStep 1916807 = 2875211) B2875211
theorem B2156413 : Blo 1915435 2156413 := bbase (se 3 (by rfl) ⟨404327, by rfl⟩ : syracuseStep 2156413 = 808655) (by norm_num)
theorem B2875217 : Blo 1915435 2875217 := bstep (se 2 (by rfl) ⟨1078206, by rfl⟩ : syracuseStep 2875217 = 2156413) B2156413
theorem B1916811 : Blo 1915435 1916811 := bstep (se 1 (by rfl) ⟨1437608, by rfl⟩ : syracuseStep 1916811 = 2875217) B2875217
theorem B6469253 : Blo 1915435 6469253 := bbase (se 4 (by rfl) ⟨606492, by rfl⟩ : syracuseStep 6469253 = 1212985) (by norm_num)
theorem B4312835 : Blo 1915435 4312835 := bstep (se 1 (by rfl) ⟨3234626, by rfl⟩ : syracuseStep 4312835 = 6469253) B6469253
theorem B2875223 : Blo 1915435 2875223 := bstep (se 1 (by rfl) ⟨2156417, by rfl⟩ : syracuseStep 2875223 = 4312835) B4312835
theorem B1916815 : Blo 1915435 1916815 := bstep (se 1 (by rfl) ⟨1437611, by rfl⟩ : syracuseStep 1916815 = 2875223) B2875223
theorem B2875229 : Blo 1915435 2875229 := bbase (se 3 (by rfl) ⟨539105, by rfl⟩ : syracuseStep 2875229 = 1078211) (by norm_num)
theorem B1916819 : Blo 1915435 1916819 := bstep (se 1 (by rfl) ⟨1437614, by rfl⟩ : syracuseStep 1916819 = 2875229) B2875229
theorem B4312853 : Blo 1915435 4312853 := bbase (se 6 (by rfl) ⟨101082, by rfl⟩ : syracuseStep 4312853 = 202165) (by norm_num)
theorem B2875235 : Blo 1915435 2875235 := bstep (se 1 (by rfl) ⟨2156426, by rfl⟩ : syracuseStep 2875235 = 4312853) B4312853
theorem B1916823 : Blo 1915435 1916823 := bstep (se 1 (by rfl) ⟨1437617, by rfl⟩ : syracuseStep 1916823 = 2875235) B2875235
theorem B7277957 : Blo 1915435 7277957 := bbase (se 4 (by rfl) ⟨682308, by rfl⟩ : syracuseStep 7277957 = 1364617) (by norm_num)
theorem B4851971 : Blo 1915435 4851971 := bstep (se 1 (by rfl) ⟨3638978, by rfl⟩ : syracuseStep 4851971 = 7277957) B7277957
theorem B3234647 : Blo 1915435 3234647 := bstep (se 1 (by rfl) ⟨2425985, by rfl⟩ : syracuseStep 3234647 = 4851971) B4851971
theorem B2156431 : Blo 1915435 2156431 := bstep (se 1 (by rfl) ⟨1617323, by rfl⟩ : syracuseStep 2156431 = 3234647) B3234647
theorem B2875241 : Blo 1915435 2875241 := bstep (se 2 (by rfl) ⟨1078215, by rfl⟩ : syracuseStep 2875241 = 2156431) B2156431
theorem B1916827 : Blo 1915435 1916827 := bstep (se 1 (by rfl) ⟨1437620, by rfl⟩ : syracuseStep 1916827 = 2875241) B2875241
theorem B6140789 : Blo 1915435 6140789 := bbase (se 5 (by rfl) ⟨287849, by rfl⟩ : syracuseStep 6140789 = 575699) (by norm_num)
theorem B4093859 : Blo 1915435 4093859 := bstep (se 1 (by rfl) ⟨3070394, by rfl⟩ : syracuseStep 4093859 = 6140789) B6140789
theorem B10916957 : Blo 1915435 10916957 := bstep (se 3 (by rfl) ⟨2046929, by rfl⟩ : syracuseStep 10916957 = 4093859) B4093859
theorem B7277971 : Blo 1915435 7277971 := bstep (se 1 (by rfl) ⟨5458478, by rfl⟩ : syracuseStep 7277971 = 10916957) B10916957
theorem B9703961 : Blo 1915435 9703961 := bstep (se 2 (by rfl) ⟨3638985, by rfl⟩ : syracuseStep 9703961 = 7277971) B7277971
theorem B6469307 : Blo 1915435 6469307 := bstep (se 1 (by rfl) ⟨4851980, by rfl⟩ : syracuseStep 6469307 = 9703961) B9703961
theorem B4312871 : Blo 1915435 4312871 := bstep (se 1 (by rfl) ⟨3234653, by rfl⟩ : syracuseStep 4312871 = 6469307) B6469307
theorem B2875247 : Blo 1915435 2875247 := bstep (se 1 (by rfl) ⟨2156435, by rfl⟩ : syracuseStep 2875247 = 4312871) B4312871
theorem B1916831 : Blo 1915435 1916831 := bstep (se 1 (by rfl) ⟨1437623, by rfl⟩ : syracuseStep 1916831 = 2875247) B2875247
theorem B2875253 : Blo 1915435 2875253 := bbase (se 5 (by rfl) ⟨134777, by rfl⟩ : syracuseStep 2875253 = 269555) (by norm_num)
theorem B1916835 : Blo 1915435 1916835 := bstep (se 1 (by rfl) ⟨1437626, by rfl⟩ : syracuseStep 1916835 = 2875253) B2875253
theorem B4093877 : Blo 1915435 4093877 := bbase (se 5 (by rfl) ⟨191900, by rfl⟩ : syracuseStep 4093877 = 383801) (by norm_num)
theorem B2729251 : Blo 1915435 2729251 := bstep (se 1 (by rfl) ⟨2046938, by rfl⟩ : syracuseStep 2729251 = 4093877) B4093877
theorem B3639001 : Blo 1915435 3639001 := bstep (se 2 (by rfl) ⟨1364625, by rfl⟩ : syracuseStep 3639001 = 2729251) B2729251
theorem B4852001 : Blo 1915435 4852001 := bstep (se 2 (by rfl) ⟨1819500, by rfl⟩ : syracuseStep 4852001 = 3639001) B3639001
theorem B3234667 : Blo 1915435 3234667 := bstep (se 1 (by rfl) ⟨2426000, by rfl⟩ : syracuseStep 3234667 = 4852001) B4852001
theorem B4312889 : Blo 1915435 4312889 := bstep (se 2 (by rfl) ⟨1617333, by rfl⟩ : syracuseStep 4312889 = 3234667) B3234667
theorem B2875259 : Blo 1915435 2875259 := bstep (se 1 (by rfl) ⟨2156444, by rfl⟩ : syracuseStep 2875259 = 4312889) B4312889
theorem B1916839 : Blo 1915435 1916839 := bstep (se 1 (by rfl) ⟨1437629, by rfl⟩ : syracuseStep 1916839 = 2875259) B2875259
theorem B2156449 : Blo 1915435 2156449 := bbase (se 2 (by rfl) ⟨808668, by rfl⟩ : syracuseStep 2156449 = 1617337) (by norm_num)
theorem B2875265 : Blo 1915435 2875265 := bstep (se 2 (by rfl) ⟨1078224, by rfl⟩ : syracuseStep 2875265 = 2156449) B2156449
theorem B1916843 : Blo 1915435 1916843 := bstep (se 1 (by rfl) ⟨1437632, by rfl⟩ : syracuseStep 1916843 = 2875265) B2875265
theorem B4852021 : Blo 1915435 4852021 := bbase (se 5 (by rfl) ⟨227438, by rfl⟩ : syracuseStep 4852021 = 454877) (by norm_num)
theorem B6469361 : Blo 1915435 6469361 := bstep (se 2 (by rfl) ⟨2426010, by rfl⟩ : syracuseStep 6469361 = 4852021) B4852021
theorem B4312907 : Blo 1915435 4312907 := bstep (se 1 (by rfl) ⟨3234680, by rfl⟩ : syracuseStep 4312907 = 6469361) B6469361
theorem B2875271 : Blo 1915435 2875271 := bstep (se 1 (by rfl) ⟨2156453, by rfl⟩ : syracuseStep 2875271 = 4312907) B4312907
theorem B1916847 : Blo 1915435 1916847 := bstep (se 1 (by rfl) ⟨1437635, by rfl⟩ : syracuseStep 1916847 = 2875271) B2875271
theorem B2875277 : Blo 1915435 2875277 := bbase (se 3 (by rfl) ⟨539114, by rfl⟩ : syracuseStep 2875277 = 1078229) (by norm_num)
theorem B1916851 : Blo 1915435 1916851 := bstep (se 1 (by rfl) ⟨1437638, by rfl⟩ : syracuseStep 1916851 = 2875277) B2875277
theorem B4312925 : Blo 1915435 4312925 := bbase (se 3 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 4312925 = 1617347) (by norm_num)
theorem B2875283 : Blo 1915435 2875283 := bstep (se 1 (by rfl) ⟨2156462, by rfl⟩ : syracuseStep 2875283 = 4312925) B4312925
theorem B1916855 : Blo 1915435 1916855 := bstep (se 1 (by rfl) ⟨1437641, by rfl⟩ : syracuseStep 1916855 = 2875283) B2875283
theorem B3234701 : Blo 1915435 3234701 := bbase (se 3 (by rfl) ⟨606506, by rfl⟩ : syracuseStep 3234701 = 1213013) (by norm_num)
theorem B2156467 : Blo 1915435 2156467 := bstep (se 1 (by rfl) ⟨1617350, by rfl⟩ : syracuseStep 2156467 = 3234701) B3234701
theorem B2875289 : Blo 1915435 2875289 := bstep (se 2 (by rfl) ⟨1078233, by rfl⟩ : syracuseStep 2875289 = 2156467) B2156467
theorem B1916859 : Blo 1915435 1916859 := bstep (se 1 (by rfl) ⟨1437644, by rfl⟩ : syracuseStep 1916859 = 2875289) B2875289
theorem B2914525 : Blo 1915435 2914525 := bbase (se 3 (by rfl) ⟨546473, by rfl⟩ : syracuseStep 2914525 = 1092947) (by norm_num)
theorem B15544133 : Blo 1915435 15544133 := bstep (se 4 (by rfl) ⟨1457262, by rfl⟩ : syracuseStep 15544133 = 2914525) B2914525
theorem B10362755 : Blo 1915435 10362755 := bstep (se 1 (by rfl) ⟨7772066, by rfl⟩ : syracuseStep 10362755 = 15544133) B15544133
theorem B6908503 : Blo 1915435 6908503 := bstep (se 1 (by rfl) ⟨5181377, by rfl⟩ : syracuseStep 6908503 = 10362755) B10362755
theorem B9211337 : Blo 1915435 9211337 := bstep (se 2 (by rfl) ⟨3454251, by rfl⟩ : syracuseStep 9211337 = 6908503) B6908503
theorem B6140891 : Blo 1915435 6140891 := bstep (se 1 (by rfl) ⟨4605668, by rfl⟩ : syracuseStep 6140891 = 9211337) B9211337
theorem B16375709 : Blo 1915435 16375709 := bstep (se 3 (by rfl) ⟨3070445, by rfl⟩ : syracuseStep 16375709 = 6140891) B6140891
theorem B10917139 : Blo 1915435 10917139 := bstep (se 1 (by rfl) ⟨8187854, by rfl⟩ : syracuseStep 10917139 = 16375709) B16375709
theorem B14556185 : Blo 1915435 14556185 := bstep (se 2 (by rfl) ⟨5458569, by rfl⟩ : syracuseStep 14556185 = 10917139) B10917139
theorem B9704123 : Blo 1915435 9704123 := bstep (se 1 (by rfl) ⟨7278092, by rfl⟩ : syracuseStep 9704123 = 14556185) B14556185
theorem B6469415 : Blo 1915435 6469415 := bstep (se 1 (by rfl) ⟨4852061, by rfl⟩ : syracuseStep 6469415 = 9704123) B9704123
theorem B4312943 : Blo 1915435 4312943 := bstep (se 1 (by rfl) ⟨3234707, by rfl⟩ : syracuseStep 4312943 = 6469415) B6469415
theorem B2875295 : Blo 1915435 2875295 := bstep (se 1 (by rfl) ⟨2156471, by rfl⟩ : syracuseStep 2875295 = 4312943) B4312943
theorem B1916863 : Blo 1915435 1916863 := bstep (se 1 (by rfl) ⟨1437647, by rfl⟩ : syracuseStep 1916863 = 2875295) B2875295
theorem B2875301 : Blo 1915435 2875301 := bbase (se 4 (by rfl) ⟨269559, by rfl⟩ : syracuseStep 2875301 = 539119) (by norm_num)
theorem B1916867 : Blo 1915435 1916867 := bstep (se 1 (by rfl) ⟨1437650, by rfl⟩ : syracuseStep 1916867 = 2875301) B2875301
theorem B2426041 : Blo 1915435 2426041 := bbase (se 2 (by rfl) ⟨909765, by rfl⟩ : syracuseStep 2426041 = 1819531) (by norm_num)
theorem B3234721 : Blo 1915435 3234721 := bstep (se 2 (by rfl) ⟨1213020, by rfl⟩ : syracuseStep 3234721 = 2426041) B2426041
theorem B4312961 : Blo 1915435 4312961 := bstep (se 2 (by rfl) ⟨1617360, by rfl⟩ : syracuseStep 4312961 = 3234721) B3234721
theorem B2875307 : Blo 1915435 2875307 := bstep (se 1 (by rfl) ⟨2156480, by rfl⟩ : syracuseStep 2875307 = 4312961) B4312961
theorem B1916871 : Blo 1915435 1916871 := bstep (se 1 (by rfl) ⟨1437653, by rfl⟩ : syracuseStep 1916871 = 2875307) B2875307
theorem B2156485 : Blo 1915435 2156485 := bbase (se 4 (by rfl) ⟨202170, by rfl⟩ : syracuseStep 2156485 = 404341) (by norm_num)
theorem B2875313 : Blo 1915435 2875313 := bstep (se 2 (by rfl) ⟨1078242, by rfl⟩ : syracuseStep 2875313 = 2156485) B2156485
theorem B1916875 : Blo 1915435 1916875 := bstep (se 1 (by rfl) ⟨1437656, by rfl⟩ : syracuseStep 1916875 = 2875313) B2875313
theorem B3639077 : Blo 1915435 3639077 := bbase (se 4 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 3639077 = 682327) (by norm_num)
theorem B2426051 : Blo 1915435 2426051 := bstep (se 1 (by rfl) ⟨1819538, by rfl⟩ : syracuseStep 2426051 = 3639077) B3639077
theorem B6469469 : Blo 1915435 6469469 := bstep (se 3 (by rfl) ⟨1213025, by rfl⟩ : syracuseStep 6469469 = 2426051) B2426051
theorem B4312979 : Blo 1915435 4312979 := bstep (se 1 (by rfl) ⟨3234734, by rfl⟩ : syracuseStep 4312979 = 6469469) B6469469
theorem B2875319 : Blo 1915435 2875319 := bstep (se 1 (by rfl) ⟨2156489, by rfl⟩ : syracuseStep 2875319 = 4312979) B4312979
theorem B1916879 : Blo 1915435 1916879 := bstep (se 1 (by rfl) ⟨1437659, by rfl⟩ : syracuseStep 1916879 = 2875319) B2875319
theorem B2875325 : Blo 1915435 2875325 := bbase (se 3 (by rfl) ⟨539123, by rfl⟩ : syracuseStep 2875325 = 1078247) (by norm_num)
theorem B1916883 : Blo 1915435 1916883 := bstep (se 1 (by rfl) ⟨1437662, by rfl⟩ : syracuseStep 1916883 = 2875325) B2875325
theorem B4312997 : Blo 1915435 4312997 := bbase (se 4 (by rfl) ⟨404343, by rfl⟩ : syracuseStep 4312997 = 808687) (by norm_num)
theorem B2875331 : Blo 1915435 2875331 := bstep (se 1 (by rfl) ⟨2156498, by rfl⟩ : syracuseStep 2875331 = 4312997) B4312997
theorem B1916887 : Blo 1915435 1916887 := bstep (se 1 (by rfl) ⟨1437665, by rfl⟩ : syracuseStep 1916887 = 2875331) B2875331
theorem B4852133 : Blo 1915435 4852133 := bbase (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) (by norm_num)
theorem B3234755 : Blo 1915435 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B2156503 : Blo 1915435 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B2875337 : Blo 1915435 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B1916891 : Blo 1915435 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B5458661 : Blo 1915435 5458661 := bbase (se 4 (by rfl) ⟨511749, by rfl⟩ : syracuseStep 5458661 = 1023499) (by norm_num)
theorem B3639107 : Blo 1915435 3639107 := bstep (se 1 (by rfl) ⟨2729330, by rfl⟩ : syracuseStep 3639107 = 5458661) B5458661
theorem B9704285 : Blo 1915435 9704285 := bstep (se 3 (by rfl) ⟨1819553, by rfl⟩ : syracuseStep 9704285 = 3639107) B3639107
theorem B6469523 : Blo 1915435 6469523 := bstep (se 1 (by rfl) ⟨4852142, by rfl⟩ : syracuseStep 6469523 = 9704285) B9704285
theorem B4313015 : Blo 1915435 4313015 := bstep (se 1 (by rfl) ⟨3234761, by rfl⟩ : syracuseStep 4313015 = 6469523) B6469523
theorem B2875343 : Blo 1915435 2875343 := bstep (se 1 (by rfl) ⟨2156507, by rfl⟩ : syracuseStep 2875343 = 4313015) B4313015
theorem B1916895 : Blo 1915435 1916895 := bstep (se 1 (by rfl) ⟨1437671, by rfl⟩ : syracuseStep 1916895 = 2875343) B2875343
theorem B2875349 : Blo 1915435 2875349 := bbase (se 7 (by rfl) ⟨33695, by rfl⟩ : syracuseStep 2875349 = 67391) (by norm_num)
theorem B1916899 : Blo 1915435 1916899 := bstep (se 1 (by rfl) ⟨1437674, by rfl⟩ : syracuseStep 1916899 = 2875349) B2875349
theorem B7278245 : Blo 1915435 7278245 := bbase (se 4 (by rfl) ⟨682335, by rfl⟩ : syracuseStep 7278245 = 1364671) (by norm_num)
theorem B4852163 : Blo 1915435 4852163 := bstep (se 1 (by rfl) ⟨3639122, by rfl⟩ : syracuseStep 4852163 = 7278245) B7278245
theorem B3234775 : Blo 1915435 3234775 := bstep (se 1 (by rfl) ⟨2426081, by rfl⟩ : syracuseStep 3234775 = 4852163) B4852163
theorem B4313033 : Blo 1915435 4313033 := bstep (se 2 (by rfl) ⟨1617387, by rfl⟩ : syracuseStep 4313033 = 3234775) B3234775
theorem B2875355 : Blo 1915435 2875355 := bstep (se 1 (by rfl) ⟨2156516, by rfl⟩ : syracuseStep 2875355 = 4313033) B4313033
theorem B1916903 : Blo 1915435 1916903 := bstep (se 1 (by rfl) ⟨1437677, by rfl⟩ : syracuseStep 1916903 = 2875355) B2875355
theorem B2156521 : Blo 1915435 2156521 := bbase (se 2 (by rfl) ⟨808695, by rfl⟩ : syracuseStep 2156521 = 1617391) (by norm_num)
theorem B2875361 : Blo 1915435 2875361 := bstep (se 2 (by rfl) ⟨1078260, by rfl⟩ : syracuseStep 2875361 = 2156521) B2156521
theorem B1916907 : Blo 1915435 1916907 := bstep (se 1 (by rfl) ⟨1437680, by rfl⟩ : syracuseStep 1916907 = 2875361) B2875361
theorem B5181509 : Blo 1915435 5181509 := bbase (se 4 (by rfl) ⟨485766, by rfl⟩ : syracuseStep 5181509 = 971533) (by norm_num)
theorem B3454339 : Blo 1915435 3454339 := bstep (se 1 (by rfl) ⟨2590754, by rfl⟩ : syracuseStep 3454339 = 5181509) B5181509
theorem B4605785 : Blo 1915435 4605785 := bstep (se 2 (by rfl) ⟨1727169, by rfl⟩ : syracuseStep 4605785 = 3454339) B3454339
theorem B3070523 : Blo 1915435 3070523 := bstep (se 1 (by rfl) ⟨2302892, by rfl⟩ : syracuseStep 3070523 = 4605785) B4605785
theorem B2047015 : Blo 1915435 2047015 := bstep (se 1 (by rfl) ⟨1535261, by rfl⟩ : syracuseStep 2047015 = 3070523) B3070523
theorem B10917413 : Blo 1915435 10917413 := bstep (se 4 (by rfl) ⟨1023507, by rfl⟩ : syracuseStep 10917413 = 2047015) B2047015
theorem B7278275 : Blo 1915435 7278275 := bstep (se 1 (by rfl) ⟨5458706, by rfl⟩ : syracuseStep 7278275 = 10917413) B10917413
theorem B4852183 : Blo 1915435 4852183 := bstep (se 1 (by rfl) ⟨3639137, by rfl⟩ : syracuseStep 4852183 = 7278275) B7278275
theorem B6469577 : Blo 1915435 6469577 := bstep (se 2 (by rfl) ⟨2426091, by rfl⟩ : syracuseStep 6469577 = 4852183) B4852183
theorem B4313051 : Blo 1915435 4313051 := bstep (se 1 (by rfl) ⟨3234788, by rfl⟩ : syracuseStep 4313051 = 6469577) B6469577
theorem B2875367 : Blo 1915435 2875367 := bstep (se 1 (by rfl) ⟨2156525, by rfl⟩ : syracuseStep 2875367 = 4313051) B4313051
theorem B1916911 : Blo 1915435 1916911 := bstep (se 1 (by rfl) ⟨1437683, by rfl⟩ : syracuseStep 1916911 = 2875367) B2875367
theorem B2875373 : Blo 1915435 2875373 := bbase (se 3 (by rfl) ⟨539132, by rfl⟩ : syracuseStep 2875373 = 1078265) (by norm_num)
theorem B1916915 : Blo 1915435 1916915 := bstep (se 1 (by rfl) ⟨1437686, by rfl⟩ : syracuseStep 1916915 = 2875373) B2875373
theorem B4313069 : Blo 1915435 4313069 := bbase (se 3 (by rfl) ⟨808700, by rfl⟩ : syracuseStep 4313069 = 1617401) (by norm_num)
theorem B2875379 : Blo 1915435 2875379 := bstep (se 1 (by rfl) ⟨2156534, by rfl⟩ : syracuseStep 2875379 = 4313069) B4313069
theorem B1916919 : Blo 1915435 1916919 := bstep (se 1 (by rfl) ⟨1437689, by rfl⟩ : syracuseStep 1916919 = 2875379) B2875379
theorem B3886157 : Blo 1915435 3886157 := bbase (se 3 (by rfl) ⟨728654, by rfl⟩ : syracuseStep 3886157 = 1457309) (by norm_num)
theorem B10363085 : Blo 1915435 10363085 := bstep (se 3 (by rfl) ⟨1943078, by rfl⟩ : syracuseStep 10363085 = 3886157) B3886157
theorem B6908723 : Blo 1915435 6908723 := bstep (se 1 (by rfl) ⟨5181542, by rfl⟩ : syracuseStep 6908723 = 10363085) B10363085
theorem B4605815 : Blo 1915435 4605815 := bstep (se 1 (by rfl) ⟨3454361, by rfl⟩ : syracuseStep 4605815 = 6908723) B6908723
theorem B3070543 : Blo 1915435 3070543 := bstep (se 1 (by rfl) ⟨2302907, by rfl⟩ : syracuseStep 3070543 = 4605815) B4605815
theorem B4094057 : Blo 1915435 4094057 := bstep (se 2 (by rfl) ⟨1535271, by rfl⟩ : syracuseStep 4094057 = 3070543) B3070543
theorem B2729371 : Blo 1915435 2729371 := bstep (se 1 (by rfl) ⟨2047028, by rfl⟩ : syracuseStep 2729371 = 4094057) B4094057
theorem B3639161 : Blo 1915435 3639161 := bstep (se 2 (by rfl) ⟨1364685, by rfl⟩ : syracuseStep 3639161 = 2729371) B2729371
theorem B2426107 : Blo 1915435 2426107 := bstep (se 1 (by rfl) ⟨1819580, by rfl⟩ : syracuseStep 2426107 = 3639161) B3639161
theorem B3234809 : Blo 1915435 3234809 := bstep (se 2 (by rfl) ⟨1213053, by rfl⟩ : syracuseStep 3234809 = 2426107) B2426107
theorem B2156539 : Blo 1915435 2156539 := bstep (se 1 (by rfl) ⟨1617404, by rfl⟩ : syracuseStep 2156539 = 3234809) B3234809
theorem B2875385 : Blo 1915435 2875385 := bstep (se 2 (by rfl) ⟨1078269, by rfl⟩ : syracuseStep 2875385 = 2156539) B2156539
theorem B1916923 : Blo 1915435 1916923 := bstep (se 1 (by rfl) ⟨1437692, by rfl⟩ : syracuseStep 1916923 = 2875385) B2875385
theorem B4668661 : Blo 1915435 4668661 := bbase (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) (by norm_num)
theorem B6224881 : Blo 1915435 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B8299841 : Blo 1915435 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B22132909 : Blo 1915435 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B118042181 : Blo 1915435 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B78694787 : Blo 1915435 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B209852765 : Blo 1915435 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B139901843 : Blo 1915435 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B373071581 : Blo 1915435 373071581 := bstep (se 3 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 373071581 = 139901843) B139901843
theorem B248714387 : Blo 1915435 248714387 := bstep (se 1 (by rfl) ⟨186535790, by rfl⟩ : syracuseStep 248714387 = 373071581) B373071581
theorem B165809591 : Blo 1915435 165809591 := bstep (se 1 (by rfl) ⟨124357193, by rfl⟩ : syracuseStep 165809591 = 248714387) B248714387
theorem B110539727 : Blo 1915435 110539727 := bstep (se 1 (by rfl) ⟨82904795, by rfl⟩ : syracuseStep 110539727 = 165809591) B165809591
theorem B73693151 : Blo 1915435 73693151 := bstep (se 1 (by rfl) ⟨55269863, by rfl⟩ : syracuseStep 73693151 = 110539727) B110539727
theorem B49128767 : Blo 1915435 49128767 := bstep (se 1 (by rfl) ⟨36846575, by rfl⟩ : syracuseStep 49128767 = 73693151) B73693151
theorem B32752511 : Blo 1915435 32752511 := bstep (se 1 (by rfl) ⟨24564383, by rfl⟩ : syracuseStep 32752511 = 49128767) B49128767
theorem B21835007 : Blo 1915435 21835007 := bstep (se 1 (by rfl) ⟨16376255, by rfl⟩ : syracuseStep 21835007 = 32752511) B32752511
theorem B14556671 : Blo 1915435 14556671 := bstep (se 1 (by rfl) ⟨10917503, by rfl⟩ : syracuseStep 14556671 = 21835007) B21835007
theorem B9704447 : Blo 1915435 9704447 := bstep (se 1 (by rfl) ⟨7278335, by rfl⟩ : syracuseStep 9704447 = 14556671) B14556671
theorem B6469631 : Blo 1915435 6469631 := bstep (se 1 (by rfl) ⟨4852223, by rfl⟩ : syracuseStep 6469631 = 9704447) B9704447
theorem B4313087 : Blo 1915435 4313087 := bstep (se 1 (by rfl) ⟨3234815, by rfl⟩ : syracuseStep 4313087 = 6469631) B6469631
theorem B2875391 : Blo 1915435 2875391 := bstep (se 1 (by rfl) ⟨2156543, by rfl⟩ : syracuseStep 2875391 = 4313087) B4313087
theorem B1916927 : Blo 1915435 1916927 := bstep (se 1 (by rfl) ⟨1437695, by rfl⟩ : syracuseStep 1916927 = 2875391) B2875391
theorem B2875397 : Blo 1915435 2875397 := bbase (se 4 (by rfl) ⟨269568, by rfl⟩ : syracuseStep 2875397 = 539137) (by norm_num)
theorem B1916931 : Blo 1915435 1916931 := bstep (se 1 (by rfl) ⟨1437698, by rfl⟩ : syracuseStep 1916931 = 2875397) B2875397
theorem B3234829 : Blo 1915435 3234829 := bbase (se 3 (by rfl) ⟨606530, by rfl⟩ : syracuseStep 3234829 = 1213061) (by norm_num)
theorem B4313105 : Blo 1915435 4313105 := bstep (se 2 (by rfl) ⟨1617414, by rfl⟩ : syracuseStep 4313105 = 3234829) B3234829
theorem B2875403 : Blo 1915435 2875403 := bstep (se 1 (by rfl) ⟨2156552, by rfl⟩ : syracuseStep 2875403 = 4313105) B4313105
theorem B1916935 : Blo 1915435 1916935 := bstep (se 1 (by rfl) ⟨1437701, by rfl⟩ : syracuseStep 1916935 = 2875403) B2875403
theorem B2156557 : Blo 1915435 2156557 := bbase (se 3 (by rfl) ⟨404354, by rfl⟩ : syracuseStep 2156557 = 808709) (by norm_num)
theorem B2875409 : Blo 1915435 2875409 := bstep (se 2 (by rfl) ⟨1078278, by rfl⟩ : syracuseStep 2875409 = 2156557) B2156557
theorem B1916939 : Blo 1915435 1916939 := bstep (se 1 (by rfl) ⟨1437704, by rfl⟩ : syracuseStep 1916939 = 2875409) B2875409
theorem B6469685 : Blo 1915435 6469685 := bbase (se 5 (by rfl) ⟨303266, by rfl⟩ : syracuseStep 6469685 = 606533) (by norm_num)
theorem B4313123 : Blo 1915435 4313123 := bstep (se 1 (by rfl) ⟨3234842, by rfl⟩ : syracuseStep 4313123 = 6469685) B6469685
theorem B2875415 : Blo 1915435 2875415 := bstep (se 1 (by rfl) ⟨2156561, by rfl⟩ : syracuseStep 2875415 = 4313123) B4313123
theorem B1916943 : Blo 1915435 1916943 := bstep (se 1 (by rfl) ⟨1437707, by rfl⟩ : syracuseStep 1916943 = 2875415) B2875415
theorem B2875421 : Blo 1915435 2875421 := bbase (se 3 (by rfl) ⟨539141, by rfl⟩ : syracuseStep 2875421 = 1078283) (by norm_num)
theorem B1916947 : Blo 1915435 1916947 := bstep (se 1 (by rfl) ⟨1437710, by rfl⟩ : syracuseStep 1916947 = 2875421) B2875421
theorem B4313141 : Blo 1915435 4313141 := bbase (se 5 (by rfl) ⟨202178, by rfl⟩ : syracuseStep 4313141 = 404357) (by norm_num)
theorem B2875427 : Blo 1915435 2875427 := bstep (se 1 (by rfl) ⟨2156570, by rfl⟩ : syracuseStep 2875427 = 4313141) B4313141
theorem B1916951 : Blo 1915435 1916951 := bstep (se 1 (by rfl) ⟨1437713, by rfl⟩ : syracuseStep 1916951 = 2875427) B2875427
theorem B9211781 : Blo 1915435 9211781 := bbase (se 4 (by rfl) ⟨863604, by rfl⟩ : syracuseStep 9211781 = 1727209) (by norm_num)
theorem B6141187 : Blo 1915435 6141187 := bstep (se 1 (by rfl) ⟨4605890, by rfl⟩ : syracuseStep 6141187 = 9211781) B9211781
theorem B8188249 : Blo 1915435 8188249 := bstep (se 2 (by rfl) ⟨3070593, by rfl⟩ : syracuseStep 8188249 = 6141187) B6141187
theorem B10917665 : Blo 1915435 10917665 := bstep (se 2 (by rfl) ⟨4094124, by rfl⟩ : syracuseStep 10917665 = 8188249) B8188249
theorem B7278443 : Blo 1915435 7278443 := bstep (se 1 (by rfl) ⟨5458832, by rfl⟩ : syracuseStep 7278443 = 10917665) B10917665
theorem B4852295 : Blo 1915435 4852295 := bstep (se 1 (by rfl) ⟨3639221, by rfl⟩ : syracuseStep 4852295 = 7278443) B7278443
theorem B3234863 : Blo 1915435 3234863 := bstep (se 1 (by rfl) ⟨2426147, by rfl⟩ : syracuseStep 3234863 = 4852295) B4852295
theorem B2156575 : Blo 1915435 2156575 := bstep (se 1 (by rfl) ⟨1617431, by rfl⟩ : syracuseStep 2156575 = 3234863) B3234863
theorem B2875433 : Blo 1915435 2875433 := bstep (se 2 (by rfl) ⟨1078287, by rfl⟩ : syracuseStep 2875433 = 2156575) B2156575
theorem B1916955 : Blo 1915435 1916955 := bstep (se 1 (by rfl) ⟨1437716, by rfl⟩ : syracuseStep 1916955 = 2875433) B2875433
theorem B20726549 : Blo 1915435 20726549 := bbase (se 6 (by rfl) ⟨485778, by rfl⟩ : syracuseStep 20726549 = 971557) (by norm_num)
theorem B13817699 : Blo 1915435 13817699 := bstep (se 1 (by rfl) ⟨10363274, by rfl⟩ : syracuseStep 13817699 = 20726549) B20726549
theorem B9211799 : Blo 1915435 9211799 := bstep (se 1 (by rfl) ⟨6908849, by rfl⟩ : syracuseStep 9211799 = 13817699) B13817699
theorem B6141199 : Blo 1915435 6141199 := bstep (se 1 (by rfl) ⟨4605899, by rfl⟩ : syracuseStep 6141199 = 9211799) B9211799
theorem B8188265 : Blo 1915435 8188265 := bstep (se 2 (by rfl) ⟨3070599, by rfl⟩ : syracuseStep 8188265 = 6141199) B6141199
theorem B5458843 : Blo 1915435 5458843 := bstep (se 1 (by rfl) ⟨4094132, by rfl⟩ : syracuseStep 5458843 = 8188265) B8188265
theorem B7278457 : Blo 1915435 7278457 := bstep (se 2 (by rfl) ⟨2729421, by rfl⟩ : syracuseStep 7278457 = 5458843) B5458843
theorem B9704609 : Blo 1915435 9704609 := bstep (se 2 (by rfl) ⟨3639228, by rfl⟩ : syracuseStep 9704609 = 7278457) B7278457
theorem B6469739 : Blo 1915435 6469739 := bstep (se 1 (by rfl) ⟨4852304, by rfl⟩ : syracuseStep 6469739 = 9704609) B9704609
theorem B4313159 : Blo 1915435 4313159 := bstep (se 1 (by rfl) ⟨3234869, by rfl⟩ : syracuseStep 4313159 = 6469739) B6469739
theorem B2875439 : Blo 1915435 2875439 := bstep (se 1 (by rfl) ⟨2156579, by rfl⟩ : syracuseStep 2875439 = 4313159) B4313159
theorem B1916959 : Blo 1915435 1916959 := bstep (se 1 (by rfl) ⟨1437719, by rfl⟩ : syracuseStep 1916959 = 2875439) B2875439
theorem B2875445 : Blo 1915435 2875445 := bbase (se 5 (by rfl) ⟨134786, by rfl⟩ : syracuseStep 2875445 = 269573) (by norm_num)
theorem B1916963 : Blo 1915435 1916963 := bstep (se 1 (by rfl) ⟨1437722, by rfl⟩ : syracuseStep 1916963 = 2875445) B2875445
theorem B4852325 : Blo 1915435 4852325 := bbase (se 4 (by rfl) ⟨454905, by rfl⟩ : syracuseStep 4852325 = 909811) (by norm_num)
theorem B3234883 : Blo 1915435 3234883 := bstep (se 1 (by rfl) ⟨2426162, by rfl⟩ : syracuseStep 3234883 = 4852325) B4852325
theorem B4313177 : Blo 1915435 4313177 := bstep (se 2 (by rfl) ⟨1617441, by rfl⟩ : syracuseStep 4313177 = 3234883) B3234883
theorem B2875451 : Blo 1915435 2875451 := bstep (se 1 (by rfl) ⟨2156588, by rfl⟩ : syracuseStep 2875451 = 4313177) B4313177
theorem B1916967 : Blo 1915435 1916967 := bstep (se 1 (by rfl) ⟨1437725, by rfl⟩ : syracuseStep 1916967 = 2875451) B2875451
theorem B2156593 : Blo 1915435 2156593 := bbase (se 2 (by rfl) ⟨808722, by rfl⟩ : syracuseStep 2156593 = 1617445) (by norm_num)
theorem B2875457 : Blo 1915435 2875457 := bstep (se 2 (by rfl) ⟨1078296, by rfl⟩ : syracuseStep 2875457 = 2156593) B2156593
theorem B1916971 : Blo 1915435 1916971 := bstep (se 1 (by rfl) ⟨1437728, by rfl⟩ : syracuseStep 1916971 = 2875457) B2875457
theorem B9211877 : Blo 1915435 9211877 := bbase (se 4 (by rfl) ⟨863613, by rfl⟩ : syracuseStep 9211877 = 1727227) (by norm_num)
theorem B6141251 : Blo 1915435 6141251 := bstep (se 1 (by rfl) ⟨4605938, by rfl⟩ : syracuseStep 6141251 = 9211877) B9211877
theorem B4094167 : Blo 1915435 4094167 := bstep (se 1 (by rfl) ⟨3070625, by rfl⟩ : syracuseStep 4094167 = 6141251) B6141251
theorem B5458889 : Blo 1915435 5458889 := bstep (se 2 (by rfl) ⟨2047083, by rfl⟩ : syracuseStep 5458889 = 4094167) B4094167
theorem B3639259 : Blo 1915435 3639259 := bstep (se 1 (by rfl) ⟨2729444, by rfl⟩ : syracuseStep 3639259 = 5458889) B5458889
theorem B4852345 : Blo 1915435 4852345 := bstep (se 2 (by rfl) ⟨1819629, by rfl⟩ : syracuseStep 4852345 = 3639259) B3639259
theorem B6469793 : Blo 1915435 6469793 := bstep (se 2 (by rfl) ⟨2426172, by rfl⟩ : syracuseStep 6469793 = 4852345) B4852345
theorem B4313195 : Blo 1915435 4313195 := bstep (se 1 (by rfl) ⟨3234896, by rfl⟩ : syracuseStep 4313195 = 6469793) B6469793
theorem B2875463 : Blo 1915435 2875463 := bstep (se 1 (by rfl) ⟨2156597, by rfl⟩ : syracuseStep 2875463 = 4313195) B4313195
theorem B1916975 : Blo 1915435 1916975 := bstep (se 1 (by rfl) ⟨1437731, by rfl⟩ : syracuseStep 1916975 = 2875463) B2875463
theorem B2875469 : Blo 1915435 2875469 := bbase (se 3 (by rfl) ⟨539150, by rfl⟩ : syracuseStep 2875469 = 1078301) (by norm_num)
theorem B1916979 : Blo 1915435 1916979 := bstep (se 1 (by rfl) ⟨1437734, by rfl⟩ : syracuseStep 1916979 = 2875469) B2875469
theorem B4313213 : Blo 1915435 4313213 := bbase (se 3 (by rfl) ⟨808727, by rfl⟩ : syracuseStep 4313213 = 1617455) (by norm_num)
theorem B2875475 : Blo 1915435 2875475 := bstep (se 1 (by rfl) ⟨2156606, by rfl⟩ : syracuseStep 2875475 = 4313213) B4313213
theorem B1916983 : Blo 1915435 1916983 := bstep (se 1 (by rfl) ⟨1437737, by rfl⟩ : syracuseStep 1916983 = 2875475) B2875475
theorem B3234917 : Blo 1915435 3234917 := bbase (se 4 (by rfl) ⟨303273, by rfl⟩ : syracuseStep 3234917 = 606547) (by norm_num)
theorem B2156611 : Blo 1915435 2156611 := bstep (se 1 (by rfl) ⟨1617458, by rfl⟩ : syracuseStep 2156611 = 3234917) B3234917
theorem B2875481 : Blo 1915435 2875481 := bstep (se 2 (by rfl) ⟨1078305, by rfl⟩ : syracuseStep 2875481 = 2156611) B2156611
theorem B1916987 : Blo 1915435 1916987 := bstep (se 1 (by rfl) ⟨1437740, by rfl⟩ : syracuseStep 1916987 = 2875481) B2875481
theorem B2186041 : Blo 1915435 2186041 := bbase (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) (by norm_num)
theorem B2914721 : Blo 1915435 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B1943147 : Blo 1915435 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B5181725 : Blo 1915435 5181725 := bstep (se 3 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 5181725 = 1943147) B1943147
theorem B3454483 : Blo 1915435 3454483 := bstep (se 1 (by rfl) ⟨2590862, by rfl⟩ : syracuseStep 3454483 = 5181725) B5181725
theorem B4605977 : Blo 1915435 4605977 := bstep (se 2 (by rfl) ⟨1727241, by rfl⟩ : syracuseStep 4605977 = 3454483) B3454483
theorem B3070651 : Blo 1915435 3070651 := bstep (se 1 (by rfl) ⟨2302988, by rfl⟩ : syracuseStep 3070651 = 4605977) B4605977
theorem B4094201 : Blo 1915435 4094201 := bstep (se 2 (by rfl) ⟨1535325, by rfl⟩ : syracuseStep 4094201 = 3070651) B3070651
theorem B2729467 : Blo 1915435 2729467 := bstep (se 1 (by rfl) ⟨2047100, by rfl⟩ : syracuseStep 2729467 = 4094201) B4094201
theorem B14557157 : Blo 1915435 14557157 := bstep (se 4 (by rfl) ⟨1364733, by rfl⟩ : syracuseStep 14557157 = 2729467) B2729467
theorem B9704771 : Blo 1915435 9704771 := bstep (se 1 (by rfl) ⟨7278578, by rfl⟩ : syracuseStep 9704771 = 14557157) B14557157
theorem B6469847 : Blo 1915435 6469847 := bstep (se 1 (by rfl) ⟨4852385, by rfl⟩ : syracuseStep 6469847 = 9704771) B9704771
theorem B4313231 : Blo 1915435 4313231 := bstep (se 1 (by rfl) ⟨3234923, by rfl⟩ : syracuseStep 4313231 = 6469847) B6469847
theorem B2875487 : Blo 1915435 2875487 := bstep (se 1 (by rfl) ⟨2156615, by rfl⟩ : syracuseStep 2875487 = 4313231) B4313231
theorem B1916991 : Blo 1915435 1916991 := bstep (se 1 (by rfl) ⟨1437743, by rfl⟩ : syracuseStep 1916991 = 2875487) B2875487
theorem B2875493 : Blo 1915435 2875493 := bbase (se 4 (by rfl) ⟨269577, by rfl⟩ : syracuseStep 2875493 = 539155) (by norm_num)
theorem B1916995 : Blo 1915435 1916995 := bstep (se 1 (by rfl) ⟨1437746, by rfl⟩ : syracuseStep 1916995 = 2875493) B2875493
theorem B4605997 : Blo 1915435 4605997 := bbase (se 3 (by rfl) ⟨863624, by rfl⟩ : syracuseStep 4605997 = 1727249) (by norm_num)
theorem B6141329 : Blo 1915435 6141329 := bstep (se 2 (by rfl) ⟨2302998, by rfl⟩ : syracuseStep 6141329 = 4605997) B4605997
theorem B4094219 : Blo 1915435 4094219 := bstep (se 1 (by rfl) ⟨3070664, by rfl⟩ : syracuseStep 4094219 = 6141329) B6141329
theorem B2729479 : Blo 1915435 2729479 := bstep (se 1 (by rfl) ⟨2047109, by rfl⟩ : syracuseStep 2729479 = 4094219) B4094219
theorem B3639305 : Blo 1915435 3639305 := bstep (se 2 (by rfl) ⟨1364739, by rfl⟩ : syracuseStep 3639305 = 2729479) B2729479
theorem B2426203 : Blo 1915435 2426203 := bstep (se 1 (by rfl) ⟨1819652, by rfl⟩ : syracuseStep 2426203 = 3639305) B3639305
theorem B3234937 : Blo 1915435 3234937 := bstep (se 2 (by rfl) ⟨1213101, by rfl⟩ : syracuseStep 3234937 = 2426203) B2426203
theorem B4313249 : Blo 1915435 4313249 := bstep (se 2 (by rfl) ⟨1617468, by rfl⟩ : syracuseStep 4313249 = 3234937) B3234937
theorem B2875499 : Blo 1915435 2875499 := bstep (se 1 (by rfl) ⟨2156624, by rfl⟩ : syracuseStep 2875499 = 4313249) B4313249
theorem B1916999 : Blo 1915435 1916999 := bstep (se 1 (by rfl) ⟨1437749, by rfl⟩ : syracuseStep 1916999 = 2875499) B2875499
theorem B2156629 : Blo 1915435 2156629 := bbase (se 8 (by rfl) ⟨12636, by rfl⟩ : syracuseStep 2156629 = 25273) (by norm_num)
theorem B2875505 : Blo 1915435 2875505 := bstep (se 2 (by rfl) ⟨1078314, by rfl⟩ : syracuseStep 2875505 = 2156629) B2156629
theorem B1917003 : Blo 1915435 1917003 := bstep (se 1 (by rfl) ⟨1437752, by rfl⟩ : syracuseStep 1917003 = 2875505) B2875505
theorem B2426213 : Blo 1915435 2426213 := bbase (se 4 (by rfl) ⟨227457, by rfl⟩ : syracuseStep 2426213 = 454915) (by norm_num)
theorem B6469901 : Blo 1915435 6469901 := bstep (se 3 (by rfl) ⟨1213106, by rfl⟩ : syracuseStep 6469901 = 2426213) B2426213
theorem B4313267 : Blo 1915435 4313267 := bstep (se 1 (by rfl) ⟨3234950, by rfl⟩ : syracuseStep 4313267 = 6469901) B6469901
theorem B2875511 : Blo 1915435 2875511 := bstep (se 1 (by rfl) ⟨2156633, by rfl⟩ : syracuseStep 2875511 = 4313267) B4313267
theorem B1917007 : Blo 1915435 1917007 := bstep (se 1 (by rfl) ⟨1437755, by rfl⟩ : syracuseStep 1917007 = 2875511) B2875511
theorem B2875517 : Blo 1915435 2875517 := bbase (se 3 (by rfl) ⟨539159, by rfl⟩ : syracuseStep 2875517 = 1078319) (by norm_num)
theorem B1917011 : Blo 1915435 1917011 := bstep (se 1 (by rfl) ⟨1437758, by rfl⟩ : syracuseStep 1917011 = 2875517) B2875517
theorem B4313285 : Blo 1915435 4313285 := bbase (se 4 (by rfl) ⟨404370, by rfl⟩ : syracuseStep 4313285 = 808741) (by norm_num)
theorem B2875523 : Blo 1915435 2875523 := bstep (se 1 (by rfl) ⟨2156642, by rfl⟩ : syracuseStep 2875523 = 4313285) B4313285
theorem B1917015 : Blo 1915435 1917015 := bstep (se 1 (by rfl) ⟨1437761, by rfl⟩ : syracuseStep 1917015 = 2875523) B2875523
theorem B3279109 : Blo 1915435 3279109 := bbase (se 4 (by rfl) ⟨307416, by rfl⟩ : syracuseStep 3279109 = 614833) (by norm_num)
theorem B4372145 : Blo 1915435 4372145 := bstep (se 2 (by rfl) ⟨1639554, by rfl⟩ : syracuseStep 4372145 = 3279109) B3279109
theorem B2914763 : Blo 1915435 2914763 := bstep (se 1 (by rfl) ⟨2186072, by rfl⟩ : syracuseStep 2914763 = 4372145) B4372145
theorem B7772701 : Blo 1915435 7772701 := bstep (se 3 (by rfl) ⟨1457381, by rfl⟩ : syracuseStep 7772701 = 2914763) B2914763
theorem B10363601 : Blo 1915435 10363601 := bstep (se 2 (by rfl) ⟨3886350, by rfl⟩ : syracuseStep 10363601 = 7772701) B7772701
theorem B6909067 : Blo 1915435 6909067 := bstep (se 1 (by rfl) ⟨5181800, by rfl⟩ : syracuseStep 6909067 = 10363601) B10363601
theorem B9212089 : Blo 1915435 9212089 := bstep (se 2 (by rfl) ⟨3454533, by rfl⟩ : syracuseStep 9212089 = 6909067) B6909067
theorem B12282785 : Blo 1915435 12282785 := bstep (se 2 (by rfl) ⟨4606044, by rfl⟩ : syracuseStep 12282785 = 9212089) B9212089
theorem B8188523 : Blo 1915435 8188523 := bstep (se 1 (by rfl) ⟨6141392, by rfl⟩ : syracuseStep 8188523 = 12282785) B12282785
theorem B5459015 : Blo 1915435 5459015 := bstep (se 1 (by rfl) ⟨4094261, by rfl⟩ : syracuseStep 5459015 = 8188523) B8188523
theorem B3639343 : Blo 1915435 3639343 := bstep (se 1 (by rfl) ⟨2729507, by rfl⟩ : syracuseStep 3639343 = 5459015) B5459015
theorem B4852457 : Blo 1915435 4852457 := bstep (se 2 (by rfl) ⟨1819671, by rfl⟩ : syracuseStep 4852457 = 3639343) B3639343
theorem B3234971 : Blo 1915435 3234971 := bstep (se 1 (by rfl) ⟨2426228, by rfl⟩ : syracuseStep 3234971 = 4852457) B4852457
theorem B2156647 : Blo 1915435 2156647 := bstep (se 1 (by rfl) ⟨1617485, by rfl⟩ : syracuseStep 2156647 = 3234971) B3234971
theorem B2875529 : Blo 1915435 2875529 := bstep (se 2 (by rfl) ⟨1078323, by rfl⟩ : syracuseStep 2875529 = 2156647) B2156647
theorem B1917019 : Blo 1915435 1917019 := bstep (se 1 (by rfl) ⟨1437764, by rfl⟩ : syracuseStep 1917019 = 2875529) B2875529
theorem B9704933 : Blo 1915435 9704933 := bbase (se 4 (by rfl) ⟨909837, by rfl⟩ : syracuseStep 9704933 = 1819675) (by norm_num)
theorem B6469955 : Blo 1915435 6469955 := bstep (se 1 (by rfl) ⟨4852466, by rfl⟩ : syracuseStep 6469955 = 9704933) B9704933
theorem B4313303 : Blo 1915435 4313303 := bstep (se 1 (by rfl) ⟨3234977, by rfl⟩ : syracuseStep 4313303 = 6469955) B6469955
theorem B2875535 : Blo 1915435 2875535 := bstep (se 1 (by rfl) ⟨2156651, by rfl⟩ : syracuseStep 2875535 = 4313303) B4313303
theorem B1917023 : Blo 1915435 1917023 := bstep (se 1 (by rfl) ⟨1437767, by rfl⟩ : syracuseStep 1917023 = 2875535) B2875535
theorem B2875541 : Blo 1915435 2875541 := bbase (se 6 (by rfl) ⟨67395, by rfl⟩ : syracuseStep 2875541 = 134791) (by norm_num)
theorem B1917027 : Blo 1915435 1917027 := bstep (se 1 (by rfl) ⟨1437770, by rfl⟩ : syracuseStep 1917027 = 2875541) B2875541
theorem B3689021 : Blo 1915435 3689021 := bbase (se 3 (by rfl) ⟨691691, by rfl⟩ : syracuseStep 3689021 = 1383383) (by norm_num)
theorem B9837389 : Blo 1915435 9837389 := bstep (se 3 (by rfl) ⟨1844510, by rfl⟩ : syracuseStep 9837389 = 3689021) B3689021
theorem B6558259 : Blo 1915435 6558259 := bstep (se 1 (by rfl) ⟨4918694, by rfl⟩ : syracuseStep 6558259 = 9837389) B9837389
theorem B8744345 : Blo 1915435 8744345 := bstep (se 2 (by rfl) ⟨3279129, by rfl⟩ : syracuseStep 8744345 = 6558259) B6558259
theorem B5829563 : Blo 1915435 5829563 := bstep (se 1 (by rfl) ⟨4372172, by rfl⟩ : syracuseStep 5829563 = 8744345) B8744345
theorem B3886375 : Blo 1915435 3886375 := bstep (se 1 (by rfl) ⟨2914781, by rfl⟩ : syracuseStep 3886375 = 5829563) B5829563
theorem B5181833 : Blo 1915435 5181833 := bstep (se 2 (by rfl) ⟨1943187, by rfl⟩ : syracuseStep 5181833 = 3886375) B3886375
theorem B3454555 : Blo 1915435 3454555 := bstep (se 1 (by rfl) ⟨2590916, by rfl⟩ : syracuseStep 3454555 = 5181833) B5181833
theorem B4606073 : Blo 1915435 4606073 := bstep (se 2 (by rfl) ⟨1727277, by rfl⟩ : syracuseStep 4606073 = 3454555) B3454555
theorem B3070715 : Blo 1915435 3070715 := bstep (se 1 (by rfl) ⟨2303036, by rfl⟩ : syracuseStep 3070715 = 4606073) B4606073
theorem B8188573 : Blo 1915435 8188573 := bstep (se 3 (by rfl) ⟨1535357, by rfl⟩ : syracuseStep 8188573 = 3070715) B3070715
theorem B10918097 : Blo 1915435 10918097 := bstep (se 2 (by rfl) ⟨4094286, by rfl⟩ : syracuseStep 10918097 = 8188573) B8188573
theorem B7278731 : Blo 1915435 7278731 := bstep (se 1 (by rfl) ⟨5459048, by rfl⟩ : syracuseStep 7278731 = 10918097) B10918097
theorem B4852487 : Blo 1915435 4852487 := bstep (se 1 (by rfl) ⟨3639365, by rfl⟩ : syracuseStep 4852487 = 7278731) B7278731
theorem B3234991 : Blo 1915435 3234991 := bstep (se 1 (by rfl) ⟨2426243, by rfl⟩ : syracuseStep 3234991 = 4852487) B4852487
theorem B4313321 : Blo 1915435 4313321 := bstep (se 2 (by rfl) ⟨1617495, by rfl⟩ : syracuseStep 4313321 = 3234991) B3234991
theorem B2875547 : Blo 1915435 2875547 := bstep (se 1 (by rfl) ⟨2156660, by rfl⟩ : syracuseStep 2875547 = 4313321) B4313321
theorem B1917031 : Blo 1915435 1917031 := bstep (se 1 (by rfl) ⟨1437773, by rfl⟩ : syracuseStep 1917031 = 2875547) B2875547
theorem B2156665 : Blo 1915435 2156665 := bbase (se 2 (by rfl) ⟨808749, by rfl⟩ : syracuseStep 2156665 = 1617499) (by norm_num)
theorem B2875553 : Blo 1915435 2875553 := bstep (se 2 (by rfl) ⟨1078332, by rfl⟩ : syracuseStep 2875553 = 2156665) B2156665
theorem B1917035 : Blo 1915435 1917035 := bstep (se 1 (by rfl) ⟨1437776, by rfl⟩ : syracuseStep 1917035 = 2875553) B2875553
theorem B252122453 : Blo 1915435 252122453 := bbase (se 14 (by rfl) ⟨23082, by rfl⟩ : syracuseStep 252122453 = 46165) (by norm_num)
theorem B168081635 : Blo 1915435 168081635 := bstep (se 1 (by rfl) ⟨126061226, by rfl⟩ : syracuseStep 168081635 = 252122453) B252122453
theorem B112054423 : Blo 1915435 112054423 := bstep (se 1 (by rfl) ⟨84040817, by rfl⟩ : syracuseStep 112054423 = 168081635) B168081635
theorem B149405897 : Blo 1915435 149405897 := bstep (se 2 (by rfl) ⟨56027211, by rfl⟩ : syracuseStep 149405897 = 112054423) B112054423
theorem B99603931 : Blo 1915435 99603931 := bstep (se 1 (by rfl) ⟨74702948, by rfl⟩ : syracuseStep 99603931 = 149405897) B149405897
theorem B132805241 : Blo 1915435 132805241 := bstep (se 2 (by rfl) ⟨49801965, by rfl⟩ : syracuseStep 132805241 = 99603931) B99603931
theorem B88536827 : Blo 1915435 88536827 := bstep (se 1 (by rfl) ⟨66402620, by rfl⟩ : syracuseStep 88536827 = 132805241) B132805241
theorem B59024551 : Blo 1915435 59024551 := bstep (se 1 (by rfl) ⟨44268413, by rfl⟩ : syracuseStep 59024551 = 88536827) B88536827
theorem B78699401 : Blo 1915435 78699401 := bstep (se 2 (by rfl) ⟨29512275, by rfl⟩ : syracuseStep 78699401 = 59024551) B59024551
theorem B52466267 : Blo 1915435 52466267 := bstep (se 1 (by rfl) ⟨39349700, by rfl⟩ : syracuseStep 52466267 = 78699401) B78699401
theorem B34977511 : Blo 1915435 34977511 := bstep (se 1 (by rfl) ⟨26233133, by rfl⟩ : syracuseStep 34977511 = 52466267) B52466267
theorem B46636681 : Blo 1915435 46636681 := bstep (se 2 (by rfl) ⟨17488755, by rfl⟩ : syracuseStep 46636681 = 34977511) B34977511
theorem B62182241 : Blo 1915435 62182241 := bstep (se 2 (by rfl) ⟨23318340, by rfl⟩ : syracuseStep 62182241 = 46636681) B46636681
theorem B41454827 : Blo 1915435 41454827 := bstep (se 1 (by rfl) ⟨31091120, by rfl⟩ : syracuseStep 41454827 = 62182241) B62182241
theorem B27636551 : Blo 1915435 27636551 := bstep (se 1 (by rfl) ⟨20727413, by rfl⟩ : syracuseStep 27636551 = 41454827) B41454827
theorem B18424367 : Blo 1915435 18424367 := bstep (se 1 (by rfl) ⟨13818275, by rfl⟩ : syracuseStep 18424367 = 27636551) B27636551
theorem B12282911 : Blo 1915435 12282911 := bstep (se 1 (by rfl) ⟨9212183, by rfl⟩ : syracuseStep 12282911 = 18424367) B18424367
theorem B8188607 : Blo 1915435 8188607 := bstep (se 1 (by rfl) ⟨6141455, by rfl⟩ : syracuseStep 8188607 = 12282911) B12282911
theorem B5459071 : Blo 1915435 5459071 := bstep (se 1 (by rfl) ⟨4094303, by rfl⟩ : syracuseStep 5459071 = 8188607) B8188607
theorem B7278761 : Blo 1915435 7278761 := bstep (se 2 (by rfl) ⟨2729535, by rfl⟩ : syracuseStep 7278761 = 5459071) B5459071
theorem B4852507 : Blo 1915435 4852507 := bstep (se 1 (by rfl) ⟨3639380, by rfl⟩ : syracuseStep 4852507 = 7278761) B7278761
theorem B6470009 : Blo 1915435 6470009 := bstep (se 2 (by rfl) ⟨2426253, by rfl⟩ : syracuseStep 6470009 = 4852507) B4852507
theorem B4313339 : Blo 1915435 4313339 := bstep (se 1 (by rfl) ⟨3235004, by rfl⟩ : syracuseStep 4313339 = 6470009) B6470009
theorem B2875559 : Blo 1915435 2875559 := bstep (se 1 (by rfl) ⟨2156669, by rfl⟩ : syracuseStep 2875559 = 4313339) B4313339
theorem B1917039 : Blo 1915435 1917039 := bstep (se 1 (by rfl) ⟨1437779, by rfl⟩ : syracuseStep 1917039 = 2875559) B2875559
theorem B2875565 : Blo 1915435 2875565 := bbase (se 3 (by rfl) ⟨539168, by rfl⟩ : syracuseStep 2875565 = 1078337) (by norm_num)
theorem B1917043 : Blo 1915435 1917043 := bstep (se 1 (by rfl) ⟨1437782, by rfl⟩ : syracuseStep 1917043 = 2875565) B2875565
theorem B4313357 : Blo 1915435 4313357 := bbase (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) (by norm_num)
theorem B2875571 : Blo 1915435 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B1917047 : Blo 1915435 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B2426269 : Blo 1915435 2426269 := bbase (se 3 (by rfl) ⟨454925, by rfl⟩ : syracuseStep 2426269 = 909851) (by norm_num)
theorem B3235025 : Blo 1915435 3235025 := bstep (se 2 (by rfl) ⟨1213134, by rfl⟩ : syracuseStep 3235025 = 2426269) B2426269
theorem B2156683 : Blo 1915435 2156683 := bstep (se 1 (by rfl) ⟨1617512, by rfl⟩ : syracuseStep 2156683 = 3235025) B3235025
theorem B2875577 : Blo 1915435 2875577 := bstep (se 2 (by rfl) ⟨1078341, by rfl⟩ : syracuseStep 2875577 = 2156683) B2156683
theorem B1917051 : Blo 1915435 1917051 := bstep (se 1 (by rfl) ⟨1437788, by rfl⟩ : syracuseStep 1917051 = 2875577) B2875577
theorem B2303065 : Blo 1915435 2303065 := bbase (se 2 (by rfl) ⟨863649, by rfl⟩ : syracuseStep 2303065 = 1727299) (by norm_num)
theorem B3070753 : Blo 1915435 3070753 := bstep (se 2 (by rfl) ⟨1151532, by rfl⟩ : syracuseStep 3070753 = 2303065) B2303065
theorem B16377349 : Blo 1915435 16377349 := bstep (se 4 (by rfl) ⟨1535376, by rfl⟩ : syracuseStep 16377349 = 3070753) B3070753
theorem B21836465 : Blo 1915435 21836465 := bstep (se 2 (by rfl) ⟨8188674, by rfl⟩ : syracuseStep 21836465 = 16377349) B16377349
theorem B14557643 : Blo 1915435 14557643 := bstep (se 1 (by rfl) ⟨10918232, by rfl⟩ : syracuseStep 14557643 = 21836465) B21836465
theorem B9705095 : Blo 1915435 9705095 := bstep (se 1 (by rfl) ⟨7278821, by rfl⟩ : syracuseStep 9705095 = 14557643) B14557643
theorem B6470063 : Blo 1915435 6470063 := bstep (se 1 (by rfl) ⟨4852547, by rfl⟩ : syracuseStep 6470063 = 9705095) B9705095
theorem B4313375 : Blo 1915435 4313375 := bstep (se 1 (by rfl) ⟨3235031, by rfl⟩ : syracuseStep 4313375 = 6470063) B6470063
theorem B2875583 : Blo 1915435 2875583 := bstep (se 1 (by rfl) ⟨2156687, by rfl⟩ : syracuseStep 2875583 = 4313375) B4313375
theorem B1917055 : Blo 1915435 1917055 := bstep (se 1 (by rfl) ⟨1437791, by rfl⟩ : syracuseStep 1917055 = 2875583) B2875583
theorem B2875589 : Blo 1915435 2875589 := bbase (se 4 (by rfl) ⟨269586, by rfl⟩ : syracuseStep 2875589 = 539173) (by norm_num)
theorem B1917059 : Blo 1915435 1917059 := bstep (se 1 (by rfl) ⟨1437794, by rfl⟩ : syracuseStep 1917059 = 2875589) B2875589
theorem B3235045 : Blo 1915435 3235045 := bbase (se 4 (by rfl) ⟨303285, by rfl⟩ : syracuseStep 3235045 = 606571) (by norm_num)
theorem B4313393 : Blo 1915435 4313393 := bstep (se 2 (by rfl) ⟨1617522, by rfl⟩ : syracuseStep 4313393 = 3235045) B3235045
theorem B2875595 : Blo 1915435 2875595 := bstep (se 1 (by rfl) ⟨2156696, by rfl⟩ : syracuseStep 2875595 = 4313393) B4313393
theorem B1917063 : Blo 1915435 1917063 := bstep (se 1 (by rfl) ⟨1437797, by rfl⟩ : syracuseStep 1917063 = 2875595) B2875595
theorem B2156701 : Blo 1915435 2156701 := bbase (se 3 (by rfl) ⟨404381, by rfl⟩ : syracuseStep 2156701 = 808763) (by norm_num)
theorem B2875601 : Blo 1915435 2875601 := bstep (se 2 (by rfl) ⟨1078350, by rfl⟩ : syracuseStep 2875601 = 2156701) B2156701
theorem B1917067 : Blo 1915435 1917067 := bstep (se 1 (by rfl) ⟨1437800, by rfl⟩ : syracuseStep 1917067 = 2875601) B2875601
theorem B6470117 : Blo 1915435 6470117 := bbase (se 4 (by rfl) ⟨606573, by rfl⟩ : syracuseStep 6470117 = 1213147) (by norm_num)
theorem B4313411 : Blo 1915435 4313411 := bstep (se 1 (by rfl) ⟨3235058, by rfl⟩ : syracuseStep 4313411 = 6470117) B6470117
theorem B2875607 : Blo 1915435 2875607 := bstep (se 1 (by rfl) ⟨2156705, by rfl⟩ : syracuseStep 2875607 = 4313411) B4313411
theorem B1917071 : Blo 1915435 1917071 := bstep (se 1 (by rfl) ⟨1437803, by rfl⟩ : syracuseStep 1917071 = 2875607) B2875607
theorem B2875613 : Blo 1915435 2875613 := bbase (se 3 (by rfl) ⟨539177, by rfl⟩ : syracuseStep 2875613 = 1078355) (by norm_num)
theorem B1917075 : Blo 1915435 1917075 := bstep (se 1 (by rfl) ⟨1437806, by rfl⟩ : syracuseStep 1917075 = 2875613) B2875613
theorem B4313429 : Blo 1915435 4313429 := bbase (se 10 (by rfl) ⟨6318, by rfl⟩ : syracuseStep 4313429 = 12637) (by norm_num)
theorem B2875619 : Blo 1915435 2875619 := bstep (se 1 (by rfl) ⟨2156714, by rfl⟩ : syracuseStep 2875619 = 4313429) B4313429
theorem B1917079 : Blo 1915435 1917079 := bstep (se 1 (by rfl) ⟨1437809, by rfl⟩ : syracuseStep 1917079 = 2875619) B2875619
theorem B2914861 : Blo 1915435 2914861 := bbase (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) (by norm_num)
theorem B3886481 : Blo 1915435 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B10363949 : Blo 1915435 10363949 := bstep (se 3 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 10363949 = 3886481) B3886481
theorem B6909299 : Blo 1915435 6909299 := bstep (se 1 (by rfl) ⟨5181974, by rfl⟩ : syracuseStep 6909299 = 10363949) B10363949
theorem B4606199 : Blo 1915435 4606199 := bstep (se 1 (by rfl) ⟨3454649, by rfl⟩ : syracuseStep 4606199 = 6909299) B6909299
theorem B3070799 : Blo 1915435 3070799 := bstep (se 1 (by rfl) ⟨2303099, by rfl⟩ : syracuseStep 3070799 = 4606199) B4606199
theorem B2047199 : Blo 1915435 2047199 := bstep (se 1 (by rfl) ⟨1535399, by rfl⟩ : syracuseStep 2047199 = 3070799) B3070799
theorem B5459197 : Blo 1915435 5459197 := bstep (se 3 (by rfl) ⟨1023599, by rfl⟩ : syracuseStep 5459197 = 2047199) B2047199
theorem B7278929 : Blo 1915435 7278929 := bstep (se 2 (by rfl) ⟨2729598, by rfl⟩ : syracuseStep 7278929 = 5459197) B5459197
theorem B4852619 : Blo 1915435 4852619 := bstep (se 1 (by rfl) ⟨3639464, by rfl⟩ : syracuseStep 4852619 = 7278929) B7278929
theorem B3235079 : Blo 1915435 3235079 := bstep (se 1 (by rfl) ⟨2426309, by rfl⟩ : syracuseStep 3235079 = 4852619) B4852619
theorem B2156719 : Blo 1915435 2156719 := bstep (se 1 (by rfl) ⟨1617539, by rfl⟩ : syracuseStep 2156719 = 3235079) B3235079
theorem B2875625 : Blo 1915435 2875625 := bstep (se 2 (by rfl) ⟨1078359, by rfl⟩ : syracuseStep 2875625 = 2156719) B2156719
theorem B1917083 : Blo 1915435 1917083 := bstep (se 1 (by rfl) ⟨1437812, by rfl⟩ : syracuseStep 1917083 = 2875625) B2875625
theorem B3323965 : Blo 1915435 3323965 := bbase (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) (by norm_num)
theorem B4431953 : Blo 1915435 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B11818541 : Blo 1915435 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B7879027 : Blo 1915435 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B10505369 : Blo 1915435 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B7003579 : Blo 1915435 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B9338105 : Blo 1915435 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B6225403 : Blo 1915435 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B8300537 : Blo 1915435 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B5533691 : Blo 1915435 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B14756509 : Blo 1915435 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B19675345 : Blo 1915435 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B26233793 : Blo 1915435 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B17489195 : Blo 1915435 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B11659463 : Blo 1915435 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B7772975 : Blo 1915435 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B5181983 : Blo 1915435 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B3454655 : Blo 1915435 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B36849653 : Blo 1915435 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B24566435 : Blo 1915435 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B16377623 : Blo 1915435 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B10918415 : Blo 1915435 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B7278943 : Blo 1915435 7278943 := bstep (se 1 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 7278943 = 10918415) B10918415
theorem B9705257 : Blo 1915435 9705257 := bstep (se 2 (by rfl) ⟨3639471, by rfl⟩ : syracuseStep 9705257 = 7278943) B7278943
theorem B6470171 : Blo 1915435 6470171 := bstep (se 1 (by rfl) ⟨4852628, by rfl⟩ : syracuseStep 6470171 = 9705257) B9705257
theorem B4313447 : Blo 1915435 4313447 := bstep (se 1 (by rfl) ⟨3235085, by rfl⟩ : syracuseStep 4313447 = 6470171) B6470171
theorem B2875631 : Blo 1915435 2875631 := bstep (se 1 (by rfl) ⟨2156723, by rfl⟩ : syracuseStep 2875631 = 4313447) B4313447
theorem B1917087 : Blo 1915435 1917087 := bstep (se 1 (by rfl) ⟨1437815, by rfl⟩ : syracuseStep 1917087 = 2875631) B2875631
theorem B2875637 : Blo 1915435 2875637 := bbase (se 5 (by rfl) ⟨134795, by rfl⟩ : syracuseStep 2875637 = 269591) (by norm_num)
theorem B1917091 : Blo 1915435 1917091 := bstep (se 1 (by rfl) ⟨1437818, by rfl⟩ : syracuseStep 1917091 = 2875637) B2875637
theorem B20728021 : Blo 1915435 20728021 := bbase (se 7 (by rfl) ⟨242906, by rfl⟩ : syracuseStep 20728021 = 485813) (by norm_num)
theorem B27637361 : Blo 1915435 27637361 := bstep (se 2 (by rfl) ⟨10364010, by rfl⟩ : syracuseStep 27637361 = 20728021) B20728021
theorem B18424907 : Blo 1915435 18424907 := bstep (se 1 (by rfl) ⟨13818680, by rfl⟩ : syracuseStep 18424907 = 27637361) B27637361
theorem B12283271 : Blo 1915435 12283271 := bstep (se 1 (by rfl) ⟨9212453, by rfl⟩ : syracuseStep 12283271 = 18424907) B18424907
theorem B8188847 : Blo 1915435 8188847 := bstep (se 1 (by rfl) ⟨6141635, by rfl⟩ : syracuseStep 8188847 = 12283271) B12283271
theorem B5459231 : Blo 1915435 5459231 := bstep (se 1 (by rfl) ⟨4094423, by rfl⟩ : syracuseStep 5459231 = 8188847) B8188847
theorem B3639487 : Blo 1915435 3639487 := bstep (se 1 (by rfl) ⟨2729615, by rfl⟩ : syracuseStep 3639487 = 5459231) B5459231
theorem B4852649 : Blo 1915435 4852649 := bstep (se 2 (by rfl) ⟨1819743, by rfl⟩ : syracuseStep 4852649 = 3639487) B3639487
theorem B3235099 : Blo 1915435 3235099 := bstep (se 1 (by rfl) ⟨2426324, by rfl⟩ : syracuseStep 3235099 = 4852649) B4852649
theorem B4313465 : Blo 1915435 4313465 := bstep (se 2 (by rfl) ⟨1617549, by rfl⟩ : syracuseStep 4313465 = 3235099) B3235099
theorem B2875643 : Blo 1915435 2875643 := bstep (se 1 (by rfl) ⟨2156732, by rfl⟩ : syracuseStep 2875643 = 4313465) B4313465
theorem B1917095 : Blo 1915435 1917095 := bstep (se 1 (by rfl) ⟨1437821, by rfl⟩ : syracuseStep 1917095 = 2875643) B2875643
theorem B2156737 : Blo 1915435 2156737 := bbase (se 2 (by rfl) ⟨808776, by rfl⟩ : syracuseStep 2156737 = 1617553) (by norm_num)
theorem B2875649 : Blo 1915435 2875649 := bstep (se 2 (by rfl) ⟨1078368, by rfl⟩ : syracuseStep 2875649 = 2156737) B2156737
theorem B1917099 : Blo 1915435 1917099 := bstep (se 1 (by rfl) ⟨1437824, by rfl⟩ : syracuseStep 1917099 = 2875649) B2875649
theorem B4852669 : Blo 1915435 4852669 := bbase (se 3 (by rfl) ⟨909875, by rfl⟩ : syracuseStep 4852669 = 1819751) (by norm_num)
theorem B6470225 : Blo 1915435 6470225 := bstep (se 2 (by rfl) ⟨2426334, by rfl⟩ : syracuseStep 6470225 = 4852669) B4852669
theorem B4313483 : Blo 1915435 4313483 := bstep (se 1 (by rfl) ⟨3235112, by rfl⟩ : syracuseStep 4313483 = 6470225) B6470225
theorem B2875655 : Blo 1915435 2875655 := bstep (se 1 (by rfl) ⟨2156741, by rfl⟩ : syracuseStep 2875655 = 4313483) B4313483
theorem B1917103 : Blo 1915435 1917103 := bstep (se 1 (by rfl) ⟨1437827, by rfl⟩ : syracuseStep 1917103 = 2875655) B2875655
theorem B2875661 : Blo 1915435 2875661 := bbase (se 3 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 2875661 = 1078373) (by norm_num)
theorem B1917107 : Blo 1915435 1917107 := bstep (se 1 (by rfl) ⟨1437830, by rfl⟩ : syracuseStep 1917107 = 2875661) B2875661
theorem B4313501 : Blo 1915435 4313501 := bbase (se 3 (by rfl) ⟨808781, by rfl⟩ : syracuseStep 4313501 = 1617563) (by norm_num)
theorem B2875667 : Blo 1915435 2875667 := bstep (se 1 (by rfl) ⟨2156750, by rfl⟩ : syracuseStep 2875667 = 4313501) B4313501
theorem B1917111 : Blo 1915435 1917111 := bstep (se 1 (by rfl) ⟨1437833, by rfl⟩ : syracuseStep 1917111 = 2875667) B2875667
theorem B3235133 : Blo 1915435 3235133 := bbase (se 3 (by rfl) ⟨606587, by rfl⟩ : syracuseStep 3235133 = 1213175) (by norm_num)
theorem B2156755 : Blo 1915435 2156755 := bstep (se 1 (by rfl) ⟨1617566, by rfl⟩ : syracuseStep 2156755 = 3235133) B3235133
theorem B2875673 : Blo 1915435 2875673 := bstep (se 2 (by rfl) ⟨1078377, by rfl⟩ : syracuseStep 2875673 = 2156755) B2156755
theorem B1917115 : Blo 1915435 1917115 := bstep (se 1 (by rfl) ⟨1437836, by rfl⟩ : syracuseStep 1917115 = 2875673) B2875673
theorem B2047237 : Blo 1915435 2047237 := bbase (se 4 (by rfl) ⟨191928, by rfl⟩ : syracuseStep 2047237 = 383857) (by norm_num)
theorem B10918597 : Blo 1915435 10918597 := bstep (se 4 (by rfl) ⟨1023618, by rfl⟩ : syracuseStep 10918597 = 2047237) B2047237
theorem B14558129 : Blo 1915435 14558129 := bstep (se 2 (by rfl) ⟨5459298, by rfl⟩ : syracuseStep 14558129 = 10918597) B10918597
theorem B9705419 : Blo 1915435 9705419 := bstep (se 1 (by rfl) ⟨7279064, by rfl⟩ : syracuseStep 9705419 = 14558129) B14558129
theorem B6470279 : Blo 1915435 6470279 := bstep (se 1 (by rfl) ⟨4852709, by rfl⟩ : syracuseStep 6470279 = 9705419) B9705419
theorem B4313519 : Blo 1915435 4313519 := bstep (se 1 (by rfl) ⟨3235139, by rfl⟩ : syracuseStep 4313519 = 6470279) B6470279
theorem B2875679 : Blo 1915435 2875679 := bstep (se 1 (by rfl) ⟨2156759, by rfl⟩ : syracuseStep 2875679 = 4313519) B4313519
theorem B1917119 : Blo 1915435 1917119 := bstep (se 1 (by rfl) ⟨1437839, by rfl⟩ : syracuseStep 1917119 = 2875679) B2875679
theorem B2875685 : Blo 1915435 2875685 := bbase (se 4 (by rfl) ⟨269595, by rfl⟩ : syracuseStep 2875685 = 539191) (by norm_num)
theorem B1917123 : Blo 1915435 1917123 := bstep (se 1 (by rfl) ⟨1437842, by rfl⟩ : syracuseStep 1917123 = 2875685) B2875685
theorem B2426365 : Blo 1915435 2426365 := bbase (se 3 (by rfl) ⟨454943, by rfl⟩ : syracuseStep 2426365 = 909887) (by norm_num)
theorem B3235153 : Blo 1915435 3235153 := bstep (se 2 (by rfl) ⟨1213182, by rfl⟩ : syracuseStep 3235153 = 2426365) B2426365
theorem B4313537 : Blo 1915435 4313537 := bstep (se 2 (by rfl) ⟨1617576, by rfl⟩ : syracuseStep 4313537 = 3235153) B3235153
theorem B2875691 : Blo 1915435 2875691 := bstep (se 1 (by rfl) ⟨2156768, by rfl⟩ : syracuseStep 2875691 = 4313537) B4313537
theorem B1917127 : Blo 1915435 1917127 := bstep (se 1 (by rfl) ⟨1437845, by rfl⟩ : syracuseStep 1917127 = 2875691) B2875691
theorem B2156773 : Blo 1915435 2156773 := bbase (se 4 (by rfl) ⟨202197, by rfl⟩ : syracuseStep 2156773 = 404395) (by norm_num)
theorem B2875697 : Blo 1915435 2875697 := bstep (se 2 (by rfl) ⟨1078386, by rfl⟩ : syracuseStep 2875697 = 2156773) B2156773
theorem B1917131 : Blo 1915435 1917131 := bstep (se 1 (by rfl) ⟨1437848, by rfl⟩ : syracuseStep 1917131 = 2875697) B2875697
theorem B4094509 : Blo 1915435 4094509 := bbase (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) (by norm_num)
theorem B5459345 : Blo 1915435 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B3639563 : Blo 1915435 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B2426375 : Blo 1915435 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B6470333 : Blo 1915435 6470333 := bstep (se 3 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 6470333 = 2426375) B2426375
theorem B4313555 : Blo 1915435 4313555 := bstep (se 1 (by rfl) ⟨3235166, by rfl⟩ : syracuseStep 4313555 = 6470333) B6470333
theorem B2875703 : Blo 1915435 2875703 := bstep (se 1 (by rfl) ⟨2156777, by rfl⟩ : syracuseStep 2875703 = 4313555) B4313555
theorem B1917135 : Blo 1915435 1917135 := bstep (se 1 (by rfl) ⟨1437851, by rfl⟩ : syracuseStep 1917135 = 2875703) B2875703
theorem B2875709 : Blo 1915435 2875709 := bbase (se 3 (by rfl) ⟨539195, by rfl⟩ : syracuseStep 2875709 = 1078391) (by norm_num)
theorem B1917139 : Blo 1915435 1917139 := bstep (se 1 (by rfl) ⟨1437854, by rfl⟩ : syracuseStep 1917139 = 2875709) B2875709
theorem B4313573 : Blo 1915435 4313573 := bbase (se 4 (by rfl) ⟨404397, by rfl⟩ : syracuseStep 4313573 = 808795) (by norm_num)
theorem B2875715 : Blo 1915435 2875715 := bstep (se 1 (by rfl) ⟨2156786, by rfl⟩ : syracuseStep 2875715 = 4313573) B4313573
theorem B1917143 : Blo 1915435 1917143 := bstep (se 1 (by rfl) ⟨1437857, by rfl⟩ : syracuseStep 1917143 = 2875715) B2875715
theorem B4852781 : Blo 1915435 4852781 := bbase (se 3 (by rfl) ⟨909896, by rfl⟩ : syracuseStep 4852781 = 1819793) (by norm_num)
theorem B3235187 : Blo 1915435 3235187 := bstep (se 1 (by rfl) ⟨2426390, by rfl⟩ : syracuseStep 3235187 = 4852781) B4852781
theorem B2156791 : Blo 1915435 2156791 := bstep (se 1 (by rfl) ⟨1617593, by rfl⟩ : syracuseStep 2156791 = 3235187) B3235187
theorem B2875721 : Blo 1915435 2875721 := bstep (se 2 (by rfl) ⟨1078395, by rfl⟩ : syracuseStep 2875721 = 2156791) B2156791
theorem B1917147 : Blo 1915435 1917147 := bstep (se 1 (by rfl) ⟨1437860, by rfl⟩ : syracuseStep 1917147 = 2875721) B2875721
theorem B1943309 : Blo 1915435 1943309 := bbase (se 3 (by rfl) ⟨364370, by rfl⟩ : syracuseStep 1943309 = 728741) (by norm_num)
theorem B5182157 : Blo 1915435 5182157 := bstep (se 3 (by rfl) ⟨971654, by rfl⟩ : syracuseStep 5182157 = 1943309) B1943309
theorem B13819085 : Blo 1915435 13819085 := bstep (se 3 (by rfl) ⟨2591078, by rfl⟩ : syracuseStep 13819085 = 5182157) B5182157
theorem B9212723 : Blo 1915435 9212723 := bstep (se 1 (by rfl) ⟨6909542, by rfl⟩ : syracuseStep 9212723 = 13819085) B13819085
theorem B6141815 : Blo 1915435 6141815 := bstep (se 1 (by rfl) ⟨4606361, by rfl⟩ : syracuseStep 6141815 = 9212723) B9212723
theorem B4094543 : Blo 1915435 4094543 := bstep (se 1 (by rfl) ⟨3070907, by rfl⟩ : syracuseStep 4094543 = 6141815) B6141815
theorem B2729695 : Blo 1915435 2729695 := bstep (se 1 (by rfl) ⟨2047271, by rfl⟩ : syracuseStep 2729695 = 4094543) B4094543
theorem B3639593 : Blo 1915435 3639593 := bstep (se 2 (by rfl) ⟨1364847, by rfl⟩ : syracuseStep 3639593 = 2729695) B2729695
theorem B9705581 : Blo 1915435 9705581 := bstep (se 3 (by rfl) ⟨1819796, by rfl⟩ : syracuseStep 9705581 = 3639593) B3639593
theorem B6470387 : Blo 1915435 6470387 := bstep (se 1 (by rfl) ⟨4852790, by rfl⟩ : syracuseStep 6470387 = 9705581) B9705581
theorem B4313591 : Blo 1915435 4313591 := bstep (se 1 (by rfl) ⟨3235193, by rfl⟩ : syracuseStep 4313591 = 6470387) B6470387
theorem B2875727 : Blo 1915435 2875727 := bstep (se 1 (by rfl) ⟨2156795, by rfl⟩ : syracuseStep 2875727 = 4313591) B4313591
theorem B1917151 : Blo 1915435 1917151 := bstep (se 1 (by rfl) ⟨1437863, by rfl⟩ : syracuseStep 1917151 = 2875727) B2875727
theorem B2875733 : Blo 1915435 2875733 := bbase (se 10 (by rfl) ⟨4212, by rfl⟩ : syracuseStep 2875733 = 8425) (by norm_num)
theorem B1917155 : Blo 1915435 1917155 := bstep (se 1 (by rfl) ⟨1437866, by rfl⟩ : syracuseStep 1917155 = 2875733) B2875733
theorem B5459413 : Blo 1915435 5459413 := bbase (se 7 (by rfl) ⟨63977, by rfl⟩ : syracuseStep 5459413 = 127955) (by norm_num)
theorem B7279217 : Blo 1915435 7279217 := bstep (se 2 (by rfl) ⟨2729706, by rfl⟩ : syracuseStep 7279217 = 5459413) B5459413
theorem B4852811 : Blo 1915435 4852811 := bstep (se 1 (by rfl) ⟨3639608, by rfl⟩ : syracuseStep 4852811 = 7279217) B7279217
theorem B3235207 : Blo 1915435 3235207 := bstep (se 1 (by rfl) ⟨2426405, by rfl⟩ : syracuseStep 3235207 = 4852811) B4852811
theorem B4313609 : Blo 1915435 4313609 := bstep (se 2 (by rfl) ⟨1617603, by rfl⟩ : syracuseStep 4313609 = 3235207) B3235207
theorem B2875739 : Blo 1915435 2875739 := bstep (se 1 (by rfl) ⟨2156804, by rfl⟩ : syracuseStep 2875739 = 4313609) B4313609
theorem B1917159 : Blo 1915435 1917159 := bstep (se 1 (by rfl) ⟨1437869, by rfl⟩ : syracuseStep 1917159 = 2875739) B2875739
theorem B2156809 : Blo 1915435 2156809 := bbase (se 2 (by rfl) ⟨808803, by rfl⟩ : syracuseStep 2156809 = 1617607) (by norm_num)
theorem B2875745 : Blo 1915435 2875745 := bstep (se 2 (by rfl) ⟨1078404, by rfl⟩ : syracuseStep 2875745 = 2156809) B2156809
theorem B1917163 : Blo 1915435 1917163 := bstep (se 1 (by rfl) ⟨1437872, by rfl⟩ : syracuseStep 1917163 = 2875745) B2875745
theorem B4207069 : Blo 1915435 4207069 := bbase (se 3 (by rfl) ⟨788825, by rfl⟩ : syracuseStep 4207069 = 1577651) (by norm_num)
theorem B5609425 : Blo 1915435 5609425 := bstep (se 2 (by rfl) ⟨2103534, by rfl⟩ : syracuseStep 5609425 = 4207069) B4207069
theorem B7479233 : Blo 1915435 7479233 := bstep (se 2 (by rfl) ⟨2804712, by rfl⟩ : syracuseStep 7479233 = 5609425) B5609425
theorem B4986155 : Blo 1915435 4986155 := bstep (se 1 (by rfl) ⟨3739616, by rfl⟩ : syracuseStep 4986155 = 7479233) B7479233
theorem B13296413 : Blo 1915435 13296413 := bstep (se 3 (by rfl) ⟨2493077, by rfl⟩ : syracuseStep 13296413 = 4986155) B4986155
theorem B35457101 : Blo 1915435 35457101 := bstep (se 3 (by rfl) ⟨6648206, by rfl⟩ : syracuseStep 35457101 = 13296413) B13296413
theorem B23638067 : Blo 1915435 23638067 := bstep (se 1 (by rfl) ⟨17728550, by rfl⟩ : syracuseStep 23638067 = 35457101) B35457101
theorem B15758711 : Blo 1915435 15758711 := bstep (se 1 (by rfl) ⟨11819033, by rfl⟩ : syracuseStep 15758711 = 23638067) B23638067
theorem B10505807 : Blo 1915435 10505807 := bstep (se 1 (by rfl) ⟨7879355, by rfl⟩ : syracuseStep 10505807 = 15758711) B15758711
theorem B7003871 : Blo 1915435 7003871 := bstep (se 1 (by rfl) ⟨5252903, by rfl⟩ : syracuseStep 7003871 = 10505807) B10505807
theorem B4669247 : Blo 1915435 4669247 := bstep (se 1 (by rfl) ⟨3501935, by rfl⟩ : syracuseStep 4669247 = 7003871) B7003871
theorem B3112831 : Blo 1915435 3112831 := bstep (se 1 (by rfl) ⟨2334623, by rfl⟩ : syracuseStep 3112831 = 4669247) B4669247
theorem B16601765 : Blo 1915435 16601765 := bstep (se 4 (by rfl) ⟨1556415, by rfl⟩ : syracuseStep 16601765 = 3112831) B3112831
theorem B44271373 : Blo 1915435 44271373 := bstep (se 3 (by rfl) ⟨8300882, by rfl⟩ : syracuseStep 44271373 = 16601765) B16601765
theorem B59028497 : Blo 1915435 59028497 := bstep (se 2 (by rfl) ⟨22135686, by rfl⟩ : syracuseStep 59028497 = 44271373) B44271373
theorem B39352331 : Blo 1915435 39352331 := bstep (se 1 (by rfl) ⟨29514248, by rfl⟩ : syracuseStep 39352331 = 59028497) B59028497
theorem B26234887 : Blo 1915435 26234887 := bstep (se 1 (by rfl) ⟨19676165, by rfl⟩ : syracuseStep 26234887 = 39352331) B39352331
theorem B34979849 : Blo 1915435 34979849 := bstep (se 2 (by rfl) ⟨13117443, by rfl⟩ : syracuseStep 34979849 = 26234887) B26234887
theorem B23319899 : Blo 1915435 23319899 := bstep (se 1 (by rfl) ⟨17489924, by rfl⟩ : syracuseStep 23319899 = 34979849) B34979849
theorem B15546599 : Blo 1915435 15546599 := bstep (se 1 (by rfl) ⟨11659949, by rfl⟩ : syracuseStep 15546599 = 23319899) B23319899
theorem B10364399 : Blo 1915435 10364399 := bstep (se 1 (by rfl) ⟨7773299, by rfl⟩ : syracuseStep 10364399 = 15546599) B15546599
theorem B6909599 : Blo 1915435 6909599 := bstep (se 1 (by rfl) ⟨5182199, by rfl⟩ : syracuseStep 6909599 = 10364399) B10364399
theorem B4606399 : Blo 1915435 4606399 := bstep (se 1 (by rfl) ⟨3454799, by rfl⟩ : syracuseStep 4606399 = 6909599) B6909599
theorem B24567461 : Blo 1915435 24567461 := bstep (se 4 (by rfl) ⟨2303199, by rfl⟩ : syracuseStep 24567461 = 4606399) B4606399
theorem B16378307 : Blo 1915435 16378307 := bstep (se 1 (by rfl) ⟨12283730, by rfl⟩ : syracuseStep 16378307 = 24567461) B24567461
theorem B10918871 : Blo 1915435 10918871 := bstep (se 1 (by rfl) ⟨8189153, by rfl⟩ : syracuseStep 10918871 = 16378307) B16378307
theorem B7279247 : Blo 1915435 7279247 := bstep (se 1 (by rfl) ⟨5459435, by rfl⟩ : syracuseStep 7279247 = 10918871) B10918871
theorem B4852831 : Blo 1915435 4852831 := bstep (se 1 (by rfl) ⟨3639623, by rfl⟩ : syracuseStep 4852831 = 7279247) B7279247
theorem B6470441 : Blo 1915435 6470441 := bstep (se 2 (by rfl) ⟨2426415, by rfl⟩ : syracuseStep 6470441 = 4852831) B4852831
theorem B4313627 : Blo 1915435 4313627 := bstep (se 1 (by rfl) ⟨3235220, by rfl⟩ : syracuseStep 4313627 = 6470441) B6470441
theorem B2875751 : Blo 1915435 2875751 := bstep (se 1 (by rfl) ⟨2156813, by rfl⟩ : syracuseStep 2875751 = 4313627) B4313627
theorem B1917167 : Blo 1915435 1917167 := bstep (se 1 (by rfl) ⟨1437875, by rfl⟩ : syracuseStep 1917167 = 2875751) B2875751
theorem B2875757 : Blo 1915435 2875757 := bbase (se 3 (by rfl) ⟨539204, by rfl⟩ : syracuseStep 2875757 = 1078409) (by norm_num)
theorem B1917171 : Blo 1915435 1917171 := bstep (se 1 (by rfl) ⟨1437878, by rfl⟩ : syracuseStep 1917171 = 2875757) B2875757
theorem B4313645 : Blo 1915435 4313645 := bbase (se 3 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 4313645 = 1617617) (by norm_num)
theorem B2875763 : Blo 1915435 2875763 := bstep (se 1 (by rfl) ⟨2156822, by rfl⟩ : syracuseStep 2875763 = 4313645) B4313645
theorem B1917175 : Blo 1915435 1917175 := bstep (se 1 (by rfl) ⟨1437881, by rfl⟩ : syracuseStep 1917175 = 2875763) B2875763
theorem B18425717 : Blo 1915435 18425717 := bbase (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) (by norm_num)
theorem B12283811 : Blo 1915435 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B8189207 : Blo 1915435 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B5459471 : Blo 1915435 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B3639647 : Blo 1915435 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B2426431 : Blo 1915435 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B3235241 : Blo 1915435 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B2156827 : Blo 1915435 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B2875769 : Blo 1915435 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B1917179 : Blo 1915435 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B32756885 : Blo 1915435 32756885 := bbase (se 6 (by rfl) ⟨767739, by rfl⟩ : syracuseStep 32756885 = 1535479) (by norm_num)
theorem B21837923 : Blo 1915435 21837923 := bstep (se 1 (by rfl) ⟨16378442, by rfl⟩ : syracuseStep 21837923 = 32756885) B32756885
theorem B14558615 : Blo 1915435 14558615 := bstep (se 1 (by rfl) ⟨10918961, by rfl⟩ : syracuseStep 14558615 = 21837923) B21837923
theorem B9705743 : Blo 1915435 9705743 := bstep (se 1 (by rfl) ⟨7279307, by rfl⟩ : syracuseStep 9705743 = 14558615) B14558615
theorem B6470495 : Blo 1915435 6470495 := bstep (se 1 (by rfl) ⟨4852871, by rfl⟩ : syracuseStep 6470495 = 9705743) B9705743
theorem B4313663 : Blo 1915435 4313663 := bstep (se 1 (by rfl) ⟨3235247, by rfl⟩ : syracuseStep 4313663 = 6470495) B6470495
theorem B2875775 : Blo 1915435 2875775 := bstep (se 1 (by rfl) ⟨2156831, by rfl⟩ : syracuseStep 2875775 = 4313663) B4313663
theorem B1917183 : Blo 1915435 1917183 := bstep (se 1 (by rfl) ⟨1437887, by rfl⟩ : syracuseStep 1917183 = 2875775) B2875775
theorem B2875781 : Blo 1915435 2875781 := bbase (se 4 (by rfl) ⟨269604, by rfl⟩ : syracuseStep 2875781 = 539209) (by norm_num)
theorem B1917187 : Blo 1915435 1917187 := bstep (se 1 (by rfl) ⟨1437890, by rfl⟩ : syracuseStep 1917187 = 2875781) B2875781
theorem B3235261 : Blo 1915435 3235261 := bbase (se 3 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 3235261 = 1213223) (by norm_num)
theorem B4313681 : Blo 1915435 4313681 := bstep (se 2 (by rfl) ⟨1617630, by rfl⟩ : syracuseStep 4313681 = 3235261) B3235261
theorem B2875787 : Blo 1915435 2875787 := bstep (se 1 (by rfl) ⟨2156840, by rfl⟩ : syracuseStep 2875787 = 4313681) B4313681
theorem B1917191 : Blo 1915435 1917191 := bstep (se 1 (by rfl) ⟨1437893, by rfl⟩ : syracuseStep 1917191 = 2875787) B2875787
theorem B2156845 : Blo 1915435 2156845 := bbase (se 3 (by rfl) ⟨404408, by rfl⟩ : syracuseStep 2156845 = 808817) (by norm_num)
theorem B2875793 : Blo 1915435 2875793 := bstep (se 2 (by rfl) ⟨1078422, by rfl⟩ : syracuseStep 2875793 = 2156845) B2156845
theorem B1917195 : Blo 1915435 1917195 := bstep (se 1 (by rfl) ⟨1437896, by rfl⟩ : syracuseStep 1917195 = 2875793) B2875793
theorem B6470549 : Blo 1915435 6470549 := bbase (se 6 (by rfl) ⟨151653, by rfl⟩ : syracuseStep 6470549 = 303307) (by norm_num)
theorem B4313699 : Blo 1915435 4313699 := bstep (se 1 (by rfl) ⟨3235274, by rfl⟩ : syracuseStep 4313699 = 6470549) B6470549
theorem B2875799 : Blo 1915435 2875799 := bstep (se 1 (by rfl) ⟨2156849, by rfl⟩ : syracuseStep 2875799 = 4313699) B4313699
theorem B1917199 : Blo 1915435 1917199 := bstep (se 1 (by rfl) ⟨1437899, by rfl⟩ : syracuseStep 1917199 = 2875799) B2875799
theorem B2875805 : Blo 1915435 2875805 := bbase (se 3 (by rfl) ⟨539213, by rfl⟩ : syracuseStep 2875805 = 1078427) (by norm_num)
theorem B1917203 : Blo 1915435 1917203 := bstep (se 1 (by rfl) ⟨1437902, by rfl⟩ : syracuseStep 1917203 = 2875805) B2875805
theorem B4313717 : Blo 1915435 4313717 := bbase (se 5 (by rfl) ⟨202205, by rfl⟩ : syracuseStep 4313717 = 404411) (by norm_num)
theorem B2875811 : Blo 1915435 2875811 := bstep (se 1 (by rfl) ⟨2156858, by rfl⟩ : syracuseStep 2875811 = 4313717) B4313717
theorem B1917207 : Blo 1915435 1917207 := bstep (se 1 (by rfl) ⟨1437905, by rfl⟩ : syracuseStep 1917207 = 2875811) B2875811
theorem B2075269 : Blo 1915435 2075269 := bbase (se 4 (by rfl) ⟨194556, by rfl⟩ : syracuseStep 2075269 = 389113) (by norm_num)
theorem B2767025 : Blo 1915435 2767025 := bstep (se 2 (by rfl) ⟨1037634, by rfl⟩ : syracuseStep 2767025 = 2075269) B2075269
theorem B7378733 : Blo 1915435 7378733 := bstep (se 3 (by rfl) ⟨1383512, by rfl⟩ : syracuseStep 7378733 = 2767025) B2767025
theorem B19676621 : Blo 1915435 19676621 := bstep (se 3 (by rfl) ⟨3689366, by rfl⟩ : syracuseStep 19676621 = 7378733) B7378733
theorem B13117747 : Blo 1915435 13117747 := bstep (se 1 (by rfl) ⟨9838310, by rfl⟩ : syracuseStep 13117747 = 19676621) B19676621
theorem B17490329 : Blo 1915435 17490329 := bstep (se 2 (by rfl) ⟨6558873, by rfl⟩ : syracuseStep 17490329 = 13117747) B13117747
theorem B11660219 : Blo 1915435 11660219 := bstep (se 1 (by rfl) ⟨8745164, by rfl⟩ : syracuseStep 11660219 = 17490329) B17490329
theorem B7773479 : Blo 1915435 7773479 := bstep (se 1 (by rfl) ⟨5830109, by rfl⟩ : syracuseStep 7773479 = 11660219) B11660219
theorem B5182319 : Blo 1915435 5182319 := bstep (se 1 (by rfl) ⟨3886739, by rfl⟩ : syracuseStep 5182319 = 7773479) B7773479
theorem B13819517 : Blo 1915435 13819517 := bstep (se 3 (by rfl) ⟨2591159, by rfl⟩ : syracuseStep 13819517 = 5182319) B5182319
theorem B9213011 : Blo 1915435 9213011 := bstep (se 1 (by rfl) ⟨6909758, by rfl⟩ : syracuseStep 9213011 = 13819517) B13819517
theorem B6142007 : Blo 1915435 6142007 := bstep (se 1 (by rfl) ⟨4606505, by rfl⟩ : syracuseStep 6142007 = 9213011) B9213011
theorem B16378685 : Blo 1915435 16378685 := bstep (se 3 (by rfl) ⟨3071003, by rfl⟩ : syracuseStep 16378685 = 6142007) B6142007
theorem B10919123 : Blo 1915435 10919123 := bstep (se 1 (by rfl) ⟨8189342, by rfl⟩ : syracuseStep 10919123 = 16378685) B16378685
theorem B7279415 : Blo 1915435 7279415 := bstep (se 1 (by rfl) ⟨5459561, by rfl⟩ : syracuseStep 7279415 = 10919123) B10919123
theorem B4852943 : Blo 1915435 4852943 := bstep (se 1 (by rfl) ⟨3639707, by rfl⟩ : syracuseStep 4852943 = 7279415) B7279415
theorem B3235295 : Blo 1915435 3235295 := bstep (se 1 (by rfl) ⟨2426471, by rfl⟩ : syracuseStep 3235295 = 4852943) B4852943
theorem B2156863 : Blo 1915435 2156863 := bstep (se 1 (by rfl) ⟨1617647, by rfl⟩ : syracuseStep 2156863 = 3235295) B3235295
theorem B2875817 : Blo 1915435 2875817 := bstep (se 2 (by rfl) ⟨1078431, by rfl⟩ : syracuseStep 2875817 = 2156863) B2156863
theorem B1917211 : Blo 1915435 1917211 := bstep (se 1 (by rfl) ⟨1437908, by rfl⟩ : syracuseStep 1917211 = 2875817) B2875817
theorem B7279429 : Blo 1915435 7279429 := bbase (se 4 (by rfl) ⟨682446, by rfl⟩ : syracuseStep 7279429 = 1364893) (by norm_num)
theorem B9705905 : Blo 1915435 9705905 := bstep (se 2 (by rfl) ⟨3639714, by rfl⟩ : syracuseStep 9705905 = 7279429) B7279429
theorem B6470603 : Blo 1915435 6470603 := bstep (se 1 (by rfl) ⟨4852952, by rfl⟩ : syracuseStep 6470603 = 9705905) B9705905
theorem B4313735 : Blo 1915435 4313735 := bstep (se 1 (by rfl) ⟨3235301, by rfl⟩ : syracuseStep 4313735 = 6470603) B6470603
theorem B2875823 : Blo 1915435 2875823 := bstep (se 1 (by rfl) ⟨2156867, by rfl⟩ : syracuseStep 2875823 = 4313735) B4313735
theorem B1917215 : Blo 1915435 1917215 := bstep (se 1 (by rfl) ⟨1437911, by rfl⟩ : syracuseStep 1917215 = 2875823) B2875823
theorem B2875829 : Blo 1915435 2875829 := bbase (se 5 (by rfl) ⟨134804, by rfl⟩ : syracuseStep 2875829 = 269609) (by norm_num)
theorem B1917219 : Blo 1915435 1917219 := bstep (se 1 (by rfl) ⟨1437914, by rfl⟩ : syracuseStep 1917219 = 2875829) B2875829
theorem B4852973 : Blo 1915435 4852973 := bbase (se 3 (by rfl) ⟨909932, by rfl⟩ : syracuseStep 4852973 = 1819865) (by norm_num)
theorem B3235315 : Blo 1915435 3235315 := bstep (se 1 (by rfl) ⟨2426486, by rfl⟩ : syracuseStep 3235315 = 4852973) B4852973
theorem B4313753 : Blo 1915435 4313753 := bstep (se 2 (by rfl) ⟨1617657, by rfl⟩ : syracuseStep 4313753 = 3235315) B3235315
theorem B2875835 : Blo 1915435 2875835 := bstep (se 1 (by rfl) ⟨2156876, by rfl⟩ : syracuseStep 2875835 = 4313753) B4313753
theorem B1917223 : Blo 1915435 1917223 := bstep (se 1 (by rfl) ⟨1437917, by rfl⟩ : syracuseStep 1917223 = 2875835) B2875835
theorem B2156881 : Blo 1915435 2156881 := bbase (se 2 (by rfl) ⟨808830, by rfl⟩ : syracuseStep 2156881 = 1617661) (by norm_num)
theorem B2875841 : Blo 1915435 2875841 := bstep (se 2 (by rfl) ⟨1078440, by rfl⟩ : syracuseStep 2875841 = 2156881) B2156881
theorem B1917227 : Blo 1915435 1917227 := bstep (se 1 (by rfl) ⟨1437920, by rfl⟩ : syracuseStep 1917227 = 2875841) B2875841
theorem B2047357 : Blo 1915435 2047357 := bbase (se 3 (by rfl) ⟨383879, by rfl⟩ : syracuseStep 2047357 = 767759) (by norm_num)
theorem B2729809 : Blo 1915435 2729809 := bstep (se 2 (by rfl) ⟨1023678, by rfl⟩ : syracuseStep 2729809 = 2047357) B2047357
theorem B3639745 : Blo 1915435 3639745 := bstep (se 2 (by rfl) ⟨1364904, by rfl⟩ : syracuseStep 3639745 = 2729809) B2729809
theorem B4852993 : Blo 1915435 4852993 := bstep (se 2 (by rfl) ⟨1819872, by rfl⟩ : syracuseStep 4852993 = 3639745) B3639745
theorem B6470657 : Blo 1915435 6470657 := bstep (se 2 (by rfl) ⟨2426496, by rfl⟩ : syracuseStep 6470657 = 4852993) B4852993
theorem B4313771 : Blo 1915435 4313771 := bstep (se 1 (by rfl) ⟨3235328, by rfl⟩ : syracuseStep 4313771 = 6470657) B6470657
theorem B2875847 : Blo 1915435 2875847 := bstep (se 1 (by rfl) ⟨2156885, by rfl⟩ : syracuseStep 2875847 = 4313771) B4313771
theorem B1917231 : Blo 1915435 1917231 := bstep (se 1 (by rfl) ⟨1437923, by rfl⟩ : syracuseStep 1917231 = 2875847) B2875847
theorem B2875853 : Blo 1915435 2875853 := bbase (se 3 (by rfl) ⟨539222, by rfl⟩ : syracuseStep 2875853 = 1078445) (by norm_num)
theorem B1917235 : Blo 1915435 1917235 := bstep (se 1 (by rfl) ⟨1437926, by rfl⟩ : syracuseStep 1917235 = 2875853) B2875853
theorem B4313789 : Blo 1915435 4313789 := bbase (se 3 (by rfl) ⟨808835, by rfl⟩ : syracuseStep 4313789 = 1617671) (by norm_num)
theorem B2875859 : Blo 1915435 2875859 := bstep (se 1 (by rfl) ⟨2156894, by rfl⟩ : syracuseStep 2875859 = 4313789) B4313789
theorem B1917239 : Blo 1915435 1917239 := bstep (se 1 (by rfl) ⟨1437929, by rfl⟩ : syracuseStep 1917239 = 2875859) B2875859
theorem B3235349 : Blo 1915435 3235349 := bbase (se 6 (by rfl) ⟨75828, by rfl⟩ : syracuseStep 3235349 = 151657) (by norm_num)
theorem B2156899 : Blo 1915435 2156899 := bstep (se 1 (by rfl) ⟨1617674, by rfl⟩ : syracuseStep 2156899 = 3235349) B3235349
theorem B2875865 : Blo 1915435 2875865 := bstep (se 2 (by rfl) ⟨1078449, by rfl⟩ : syracuseStep 2875865 = 2156899) B2156899
theorem B1917243 : Blo 1915435 1917243 := bstep (se 1 (by rfl) ⟨1437932, by rfl⟩ : syracuseStep 1917243 = 2875865) B2875865
theorem B1969921 : Blo 1915435 1969921 := bbase (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) (by norm_num)
theorem B2626561 : Blo 1915435 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B3502081 : Blo 1915435 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B18677765 : Blo 1915435 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B12451843 : Blo 1915435 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B16602457 : Blo 1915435 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B22136609 : Blo 1915435 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B59030957 : Blo 1915435 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B39353971 : Blo 1915435 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B52471961 : Blo 1915435 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B34981307 : Blo 1915435 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B23320871 : Blo 1915435 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B15547247 : Blo 1915435 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B10364831 : Blo 1915435 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B6909887 : Blo 1915435 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B18426365 : Blo 1915435 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B12284243 : Blo 1915435 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B8189495 : Blo 1915435 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B5459663 : Blo 1915435 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B14559101 : Blo 1915435 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B9706067 : Blo 1915435 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B6470711 : Blo 1915435 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B4313807 : Blo 1915435 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B2875871 : Blo 1915435 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B1917247 : Blo 1915435 1917247 := bstep (se 1 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 1917247 = 2875871) B2875871
theorem B2875877 : Blo 1915435 2875877 := bbase (se 4 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 2875877 = 539227) (by norm_num)
theorem B1917251 : Blo 1915435 1917251 := bstep (se 1 (by rfl) ⟨1437938, by rfl⟩ : syracuseStep 1917251 = 2875877) B2875877
theorem B8745365 : Blo 1915435 8745365 := bbase (se 6 (by rfl) ⟨204969, by rfl⟩ : syracuseStep 8745365 = 409939) (by norm_num)
theorem B23320973 : Blo 1915435 23320973 := bstep (se 3 (by rfl) ⟨4372682, by rfl⟩ : syracuseStep 23320973 = 8745365) B8745365
theorem B15547315 : Blo 1915435 15547315 := bstep (se 1 (by rfl) ⟨11660486, by rfl⟩ : syracuseStep 15547315 = 23320973) B23320973
theorem B20729753 : Blo 1915435 20729753 := bstep (se 2 (by rfl) ⟨7773657, by rfl⟩ : syracuseStep 20729753 = 15547315) B15547315
theorem B13819835 : Blo 1915435 13819835 := bstep (se 1 (by rfl) ⟨10364876, by rfl⟩ : syracuseStep 13819835 = 20729753) B20729753
theorem B9213223 : Blo 1915435 9213223 := bstep (se 1 (by rfl) ⟨6909917, by rfl⟩ : syracuseStep 9213223 = 13819835) B13819835
theorem B12284297 : Blo 1915435 12284297 := bstep (se 2 (by rfl) ⟨4606611, by rfl⟩ : syracuseStep 12284297 = 9213223) B9213223
theorem B8189531 : Blo 1915435 8189531 := bstep (se 1 (by rfl) ⟨6142148, by rfl⟩ : syracuseStep 8189531 = 12284297) B12284297
theorem B5459687 : Blo 1915435 5459687 := bstep (se 1 (by rfl) ⟨4094765, by rfl⟩ : syracuseStep 5459687 = 8189531) B8189531
theorem B3639791 : Blo 1915435 3639791 := bstep (se 1 (by rfl) ⟨2729843, by rfl⟩ : syracuseStep 3639791 = 5459687) B5459687
theorem B2426527 : Blo 1915435 2426527 := bstep (se 1 (by rfl) ⟨1819895, by rfl⟩ : syracuseStep 2426527 = 3639791) B3639791
theorem B3235369 : Blo 1915435 3235369 := bstep (se 2 (by rfl) ⟨1213263, by rfl⟩ : syracuseStep 3235369 = 2426527) B2426527
theorem B4313825 : Blo 1915435 4313825 := bstep (se 2 (by rfl) ⟨1617684, by rfl⟩ : syracuseStep 4313825 = 3235369) B3235369
theorem B2875883 : Blo 1915435 2875883 := bstep (se 1 (by rfl) ⟨2156912, by rfl⟩ : syracuseStep 2875883 = 4313825) B4313825
theorem B1917255 : Blo 1915435 1917255 := bstep (se 1 (by rfl) ⟨1437941, by rfl⟩ : syracuseStep 1917255 = 2875883) B2875883
theorem B2156917 : Blo 1915435 2156917 := bbase (se 5 (by rfl) ⟨101105, by rfl⟩ : syracuseStep 2156917 = 202211) (by norm_num)
theorem B2875889 : Blo 1915435 2875889 := bstep (se 2 (by rfl) ⟨1078458, by rfl⟩ : syracuseStep 2875889 = 2156917) B2156917
theorem B1917259 : Blo 1915435 1917259 := bstep (se 1 (by rfl) ⟨1437944, by rfl⟩ : syracuseStep 1917259 = 2875889) B2875889
theorem B2426537 : Blo 1915435 2426537 := bbase (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) (by norm_num)
theorem B6470765 : Blo 1915435 6470765 := bstep (se 3 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 6470765 = 2426537) B2426537
theorem B4313843 : Blo 1915435 4313843 := bstep (se 1 (by rfl) ⟨3235382, by rfl⟩ : syracuseStep 4313843 = 6470765) B6470765
theorem B2875895 : Blo 1915435 2875895 := bstep (se 1 (by rfl) ⟨2156921, by rfl⟩ : syracuseStep 2875895 = 4313843) B4313843
theorem B1917263 : Blo 1915435 1917263 := bstep (se 1 (by rfl) ⟨1437947, by rfl⟩ : syracuseStep 1917263 = 2875895) B2875895
theorem B2875901 : Blo 1915435 2875901 := bbase (se 3 (by rfl) ⟨539231, by rfl⟩ : syracuseStep 2875901 = 1078463) (by norm_num)
theorem B1917267 : Blo 1915435 1917267 := bstep (se 1 (by rfl) ⟨1437950, by rfl⟩ : syracuseStep 1917267 = 2875901) B2875901
theorem B4313861 : Blo 1915435 4313861 := bbase (se 4 (by rfl) ⟨404424, by rfl⟩ : syracuseStep 4313861 = 808849) (by norm_num)
theorem B2875907 : Blo 1915435 2875907 := bstep (se 1 (by rfl) ⟨2156930, by rfl⟩ : syracuseStep 2875907 = 4313861) B4313861
theorem B1917271 : Blo 1915435 1917271 := bstep (se 1 (by rfl) ⟨1437953, by rfl⟩ : syracuseStep 1917271 = 2875907) B2875907
theorem B3639829 : Blo 1915435 3639829 := bbase (se 6 (by rfl) ⟨85308, by rfl⟩ : syracuseStep 3639829 = 170617) (by norm_num)
theorem B4853105 : Blo 1915435 4853105 := bstep (se 2 (by rfl) ⟨1819914, by rfl⟩ : syracuseStep 4853105 = 3639829) B3639829
theorem B3235403 : Blo 1915435 3235403 := bstep (se 1 (by rfl) ⟨2426552, by rfl⟩ : syracuseStep 3235403 = 4853105) B4853105
theorem B2156935 : Blo 1915435 2156935 := bstep (se 1 (by rfl) ⟨1617701, by rfl⟩ : syracuseStep 2156935 = 3235403) B3235403
theorem B2875913 : Blo 1915435 2875913 := bstep (se 2 (by rfl) ⟨1078467, by rfl⟩ : syracuseStep 2875913 = 2156935) B2156935
theorem B1917275 : Blo 1915435 1917275 := bstep (se 1 (by rfl) ⟨1437956, by rfl⟩ : syracuseStep 1917275 = 2875913) B2875913
theorem B9706229 : Blo 1915435 9706229 := bbase (se 5 (by rfl) ⟨454979, by rfl⟩ : syracuseStep 9706229 = 909959) (by norm_num)
theorem B6470819 : Blo 1915435 6470819 := bstep (se 1 (by rfl) ⟨4853114, by rfl⟩ : syracuseStep 6470819 = 9706229) B9706229
theorem B4313879 : Blo 1915435 4313879 := bstep (se 1 (by rfl) ⟨3235409, by rfl⟩ : syracuseStep 4313879 = 6470819) B6470819
theorem B2875919 : Blo 1915435 2875919 := bstep (se 1 (by rfl) ⟨2156939, by rfl⟩ : syracuseStep 2875919 = 4313879) B4313879
theorem B1917279 : Blo 1915435 1917279 := bstep (se 1 (by rfl) ⟨1437959, by rfl⟩ : syracuseStep 1917279 = 2875919) B2875919
theorem B2875925 : Blo 1915435 2875925 := bbase (se 6 (by rfl) ⟨67404, by rfl⟩ : syracuseStep 2875925 = 134809) (by norm_num)
theorem B1917283 : Blo 1915435 1917283 := bstep (se 1 (by rfl) ⟨1437962, by rfl⟩ : syracuseStep 1917283 = 2875925) B2875925
theorem B3071125 : Blo 1915435 3071125 := bbase (se 6 (by rfl) ⟨71979, by rfl⟩ : syracuseStep 3071125 = 143959) (by norm_num)
theorem B16379333 : Blo 1915435 16379333 := bstep (se 4 (by rfl) ⟨1535562, by rfl⟩ : syracuseStep 16379333 = 3071125) B3071125
theorem B10919555 : Blo 1915435 10919555 := bstep (se 1 (by rfl) ⟨8189666, by rfl⟩ : syracuseStep 10919555 = 16379333) B16379333
theorem B7279703 : Blo 1915435 7279703 := bstep (se 1 (by rfl) ⟨5459777, by rfl⟩ : syracuseStep 7279703 = 10919555) B10919555
theorem B4853135 : Blo 1915435 4853135 := bstep (se 1 (by rfl) ⟨3639851, by rfl⟩ : syracuseStep 4853135 = 7279703) B7279703
theorem B3235423 : Blo 1915435 3235423 := bstep (se 1 (by rfl) ⟨2426567, by rfl⟩ : syracuseStep 3235423 = 4853135) B4853135
theorem B4313897 : Blo 1915435 4313897 := bstep (se 2 (by rfl) ⟨1617711, by rfl⟩ : syracuseStep 4313897 = 3235423) B3235423
theorem B2875931 : Blo 1915435 2875931 := bstep (se 1 (by rfl) ⟨2156948, by rfl⟩ : syracuseStep 2875931 = 4313897) B4313897
theorem B1917287 : Blo 1915435 1917287 := bstep (se 1 (by rfl) ⟨1437965, by rfl⟩ : syracuseStep 1917287 = 2875931) B2875931
theorem B2156953 : Blo 1915435 2156953 := bbase (se 2 (by rfl) ⟨808857, by rfl⟩ : syracuseStep 2156953 = 1617715) (by norm_num)
theorem B2875937 : Blo 1915435 2875937 := bstep (se 2 (by rfl) ⟨1078476, by rfl⟩ : syracuseStep 2875937 = 2156953) B2156953
theorem B1917291 : Blo 1915435 1917291 := bstep (se 1 (by rfl) ⟨1437968, by rfl⟩ : syracuseStep 1917291 = 2875937) B2875937
theorem B7279733 : Blo 1915435 7279733 := bbase (se 5 (by rfl) ⟨341237, by rfl⟩ : syracuseStep 7279733 = 682475) (by norm_num)
theorem B4853155 : Blo 1915435 4853155 := bstep (se 1 (by rfl) ⟨3639866, by rfl⟩ : syracuseStep 4853155 = 7279733) B7279733
theorem B6470873 : Blo 1915435 6470873 := bstep (se 2 (by rfl) ⟨2426577, by rfl⟩ : syracuseStep 6470873 = 4853155) B4853155
theorem B4313915 : Blo 1915435 4313915 := bstep (se 1 (by rfl) ⟨3235436, by rfl⟩ : syracuseStep 4313915 = 6470873) B6470873
theorem B2875943 : Blo 1915435 2875943 := bstep (se 1 (by rfl) ⟨2156957, by rfl⟩ : syracuseStep 2875943 = 4313915) B4313915
theorem B1917295 : Blo 1915435 1917295 := bstep (se 1 (by rfl) ⟨1437971, by rfl⟩ : syracuseStep 1917295 = 2875943) B2875943
theorem B2875949 : Blo 1915435 2875949 := bbase (se 3 (by rfl) ⟨539240, by rfl⟩ : syracuseStep 2875949 = 1078481) (by norm_num)
theorem B1917299 : Blo 1915435 1917299 := bstep (se 1 (by rfl) ⟨1437974, by rfl⟩ : syracuseStep 1917299 = 2875949) B2875949
theorem B4313933 : Blo 1915435 4313933 := bbase (se 3 (by rfl) ⟨808862, by rfl⟩ : syracuseStep 4313933 = 1617725) (by norm_num)
theorem B2875955 : Blo 1915435 2875955 := bstep (se 1 (by rfl) ⟨2156966, by rfl⟩ : syracuseStep 2875955 = 4313933) B4313933
theorem B1917303 : Blo 1915435 1917303 := bstep (se 1 (by rfl) ⟨1437977, by rfl⟩ : syracuseStep 1917303 = 2875955) B2875955
theorem B2426593 : Blo 1915435 2426593 := bbase (se 2 (by rfl) ⟨909972, by rfl⟩ : syracuseStep 2426593 = 1819945) (by norm_num)
theorem B3235457 : Blo 1915435 3235457 := bstep (se 2 (by rfl) ⟨1213296, by rfl⟩ : syracuseStep 3235457 = 2426593) B2426593
theorem B2156971 : Blo 1915435 2156971 := bstep (se 1 (by rfl) ⟨1617728, by rfl⟩ : syracuseStep 2156971 = 3235457) B3235457
theorem B2875961 : Blo 1915435 2875961 := bstep (se 2 (by rfl) ⟨1078485, by rfl⟩ : syracuseStep 2875961 = 2156971) B2156971
theorem B1917307 : Blo 1915435 1917307 := bstep (se 1 (by rfl) ⟨1437980, by rfl⟩ : syracuseStep 1917307 = 2875961) B2875961
theorem B21839381 : Blo 1915435 21839381 := bbase (se 6 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 21839381 = 1023721) (by norm_num)
theorem B14559587 : Blo 1915435 14559587 := bstep (se 1 (by rfl) ⟨10919690, by rfl⟩ : syracuseStep 14559587 = 21839381) B21839381
theorem B9706391 : Blo 1915435 9706391 := bstep (se 1 (by rfl) ⟨7279793, by rfl⟩ : syracuseStep 9706391 = 14559587) B14559587
theorem B6470927 : Blo 1915435 6470927 := bstep (se 1 (by rfl) ⟨4853195, by rfl⟩ : syracuseStep 6470927 = 9706391) B9706391
theorem B4313951 : Blo 1915435 4313951 := bstep (se 1 (by rfl) ⟨3235463, by rfl⟩ : syracuseStep 4313951 = 6470927) B6470927
theorem B2875967 : Blo 1915435 2875967 := bstep (se 1 (by rfl) ⟨2156975, by rfl⟩ : syracuseStep 2875967 = 4313951) B4313951
theorem B1917311 : Blo 1915435 1917311 := bstep (se 1 (by rfl) ⟨1437983, by rfl⟩ : syracuseStep 1917311 = 2875967) B2875967
theorem B2875973 : Blo 1915435 2875973 := bbase (se 4 (by rfl) ⟨269622, by rfl⟩ : syracuseStep 2875973 = 539245) (by norm_num)
theorem B1917315 : Blo 1915435 1917315 := bstep (se 1 (by rfl) ⟨1437986, by rfl⟩ : syracuseStep 1917315 = 2875973) B2875973
theorem B3235477 : Blo 1915435 3235477 := bbase (se 6 (by rfl) ⟨75831, by rfl⟩ : syracuseStep 3235477 = 151663) (by norm_num)
theorem B4313969 : Blo 1915435 4313969 := bstep (se 2 (by rfl) ⟨1617738, by rfl⟩ : syracuseStep 4313969 = 3235477) B3235477
theorem B2875979 : Blo 1915435 2875979 := bstep (se 1 (by rfl) ⟨2156984, by rfl⟩ : syracuseStep 2875979 = 4313969) B4313969
theorem B1917319 : Blo 1915435 1917319 := bstep (se 1 (by rfl) ⟨1437989, by rfl⟩ : syracuseStep 1917319 = 2875979) B2875979
theorem B2156989 : Blo 1915435 2156989 := bbase (se 3 (by rfl) ⟨404435, by rfl⟩ : syracuseStep 2156989 = 808871) (by norm_num)
theorem B2875985 : Blo 1915435 2875985 := bstep (se 2 (by rfl) ⟨1078494, by rfl⟩ : syracuseStep 2875985 = 2156989) B2156989
theorem B1917323 : Blo 1915435 1917323 := bstep (se 1 (by rfl) ⟨1437992, by rfl⟩ : syracuseStep 1917323 = 2875985) B2875985
theorem B6470981 : Blo 1915435 6470981 := bbase (se 4 (by rfl) ⟨606654, by rfl⟩ : syracuseStep 6470981 = 1213309) (by norm_num)
theorem B4313987 : Blo 1915435 4313987 := bstep (se 1 (by rfl) ⟨3235490, by rfl⟩ : syracuseStep 4313987 = 6470981) B6470981
theorem B2875991 : Blo 1915435 2875991 := bstep (se 1 (by rfl) ⟨2156993, by rfl⟩ : syracuseStep 2875991 = 4313987) B4313987
theorem B1917327 : Blo 1915435 1917327 := bstep (se 1 (by rfl) ⟨1437995, by rfl⟩ : syracuseStep 1917327 = 2875991) B2875991
theorem B2875997 : Blo 1915435 2875997 := bbase (se 3 (by rfl) ⟨539249, by rfl⟩ : syracuseStep 2875997 = 1078499) (by norm_num)
theorem B1917331 : Blo 1915435 1917331 := bstep (se 1 (by rfl) ⟨1437998, by rfl⟩ : syracuseStep 1917331 = 2875997) B2875997
theorem B4314005 : Blo 1915435 4314005 := bbase (se 6 (by rfl) ⟨101109, by rfl⟩ : syracuseStep 4314005 = 202219) (by norm_num)
theorem B2876003 : Blo 1915435 2876003 := bstep (se 1 (by rfl) ⟨2157002, by rfl⟩ : syracuseStep 2876003 = 4314005) B4314005
theorem B1917335 : Blo 1915435 1917335 := bstep (se 1 (by rfl) ⟨1438001, by rfl⟩ : syracuseStep 1917335 = 2876003) B2876003
theorem B5830501 : Blo 1915435 5830501 := bbase (se 4 (by rfl) ⟨546609, by rfl⟩ : syracuseStep 5830501 = 1093219) (by norm_num)
theorem B7774001 : Blo 1915435 7774001 := bstep (se 2 (by rfl) ⟨2915250, by rfl⟩ : syracuseStep 7774001 = 5830501) B5830501
theorem B5182667 : Blo 1915435 5182667 := bstep (se 1 (by rfl) ⟨3887000, by rfl⟩ : syracuseStep 5182667 = 7774001) B7774001
theorem B3455111 : Blo 1915435 3455111 := bstep (se 1 (by rfl) ⟨2591333, by rfl⟩ : syracuseStep 3455111 = 5182667) B5182667
theorem B2303407 : Blo 1915435 2303407 := bstep (se 1 (by rfl) ⟨1727555, by rfl⟩ : syracuseStep 2303407 = 3455111) B3455111
theorem B3071209 : Blo 1915435 3071209 := bstep (se 2 (by rfl) ⟨1151703, by rfl⟩ : syracuseStep 3071209 = 2303407) B2303407
theorem B4094945 : Blo 1915435 4094945 := bstep (se 2 (by rfl) ⟨1535604, by rfl⟩ : syracuseStep 4094945 = 3071209) B3071209
theorem B2729963 : Blo 1915435 2729963 := bstep (se 1 (by rfl) ⟨2047472, by rfl⟩ : syracuseStep 2729963 = 4094945) B4094945
theorem B7279901 : Blo 1915435 7279901 := bstep (se 3 (by rfl) ⟨1364981, by rfl⟩ : syracuseStep 7279901 = 2729963) B2729963
theorem B4853267 : Blo 1915435 4853267 := bstep (se 1 (by rfl) ⟨3639950, by rfl⟩ : syracuseStep 4853267 = 7279901) B7279901
theorem B3235511 : Blo 1915435 3235511 := bstep (se 1 (by rfl) ⟨2426633, by rfl⟩ : syracuseStep 3235511 = 4853267) B4853267
theorem B2157007 : Blo 1915435 2157007 := bstep (se 1 (by rfl) ⟨1617755, by rfl⟩ : syracuseStep 2157007 = 3235511) B3235511
theorem B2876009 : Blo 1915435 2876009 := bstep (se 2 (by rfl) ⟨1078503, by rfl⟩ : syracuseStep 2876009 = 2157007) B2157007
theorem B1917339 : Blo 1915435 1917339 := bstep (se 1 (by rfl) ⟨1438004, by rfl⟩ : syracuseStep 1917339 = 2876009) B2876009
theorem B3455117 : Blo 1915435 3455117 := bbase (se 3 (by rfl) ⟨647834, by rfl⟩ : syracuseStep 3455117 = 1295669) (by norm_num)
theorem B2303411 : Blo 1915435 2303411 := bstep (se 1 (by rfl) ⟨1727558, by rfl⟩ : syracuseStep 2303411 = 3455117) B3455117
theorem B6142429 : Blo 1915435 6142429 := bstep (se 3 (by rfl) ⟨1151705, by rfl⟩ : syracuseStep 6142429 = 2303411) B2303411
theorem B8189905 : Blo 1915435 8189905 := bstep (se 2 (by rfl) ⟨3071214, by rfl⟩ : syracuseStep 8189905 = 6142429) B6142429
theorem B10919873 : Blo 1915435 10919873 := bstep (se 2 (by rfl) ⟨4094952, by rfl⟩ : syracuseStep 10919873 = 8189905) B8189905
theorem B7279915 : Blo 1915435 7279915 := bstep (se 1 (by rfl) ⟨5459936, by rfl⟩ : syracuseStep 7279915 = 10919873) B10919873
theorem B9706553 : Blo 1915435 9706553 := bstep (se 2 (by rfl) ⟨3639957, by rfl⟩ : syracuseStep 9706553 = 7279915) B7279915
theorem B6471035 : Blo 1915435 6471035 := bstep (se 1 (by rfl) ⟨4853276, by rfl⟩ : syracuseStep 6471035 = 9706553) B9706553
theorem B4314023 : Blo 1915435 4314023 := bstep (se 1 (by rfl) ⟨3235517, by rfl⟩ : syracuseStep 4314023 = 6471035) B6471035
theorem B2876015 : Blo 1915435 2876015 := bstep (se 1 (by rfl) ⟨2157011, by rfl⟩ : syracuseStep 2876015 = 4314023) B4314023
theorem B1917343 : Blo 1915435 1917343 := bstep (se 1 (by rfl) ⟨1438007, by rfl⟩ : syracuseStep 1917343 = 2876015) B2876015
theorem B2876021 : Blo 1915435 2876021 := bbase (se 5 (by rfl) ⟨134813, by rfl⟩ : syracuseStep 2876021 = 269627) (by norm_num)
theorem B1917347 : Blo 1915435 1917347 := bstep (se 1 (by rfl) ⟨1438010, by rfl⟩ : syracuseStep 1917347 = 2876021) B2876021
theorem B3639973 : Blo 1915435 3639973 := bbase (se 4 (by rfl) ⟨341247, by rfl⟩ : syracuseStep 3639973 = 682495) (by norm_num)
theorem B4853297 : Blo 1915435 4853297 := bstep (se 2 (by rfl) ⟨1819986, by rfl⟩ : syracuseStep 4853297 = 3639973) B3639973
theorem B3235531 : Blo 1915435 3235531 := bstep (se 1 (by rfl) ⟨2426648, by rfl⟩ : syracuseStep 3235531 = 4853297) B4853297
theorem B4314041 : Blo 1915435 4314041 := bstep (se 2 (by rfl) ⟨1617765, by rfl⟩ : syracuseStep 4314041 = 3235531) B3235531
theorem B2876027 : Blo 1915435 2876027 := bstep (se 1 (by rfl) ⟨2157020, by rfl⟩ : syracuseStep 2876027 = 4314041) B4314041
theorem B1917351 : Blo 1915435 1917351 := bstep (se 1 (by rfl) ⟨1438013, by rfl⟩ : syracuseStep 1917351 = 2876027) B2876027
theorem B2157025 : Blo 1915435 2157025 := bbase (se 2 (by rfl) ⟨808884, by rfl⟩ : syracuseStep 2157025 = 1617769) (by norm_num)
theorem B2876033 : Blo 1915435 2876033 := bstep (se 2 (by rfl) ⟨1078512, by rfl⟩ : syracuseStep 2876033 = 2157025) B2157025
theorem B1917355 : Blo 1915435 1917355 := bstep (se 1 (by rfl) ⟨1438016, by rfl⟩ : syracuseStep 1917355 = 2876033) B2876033
theorem B4853317 : Blo 1915435 4853317 := bbase (se 4 (by rfl) ⟨454998, by rfl⟩ : syracuseStep 4853317 = 909997) (by norm_num)
theorem B6471089 : Blo 1915435 6471089 := bstep (se 2 (by rfl) ⟨2426658, by rfl⟩ : syracuseStep 6471089 = 4853317) B4853317
theorem B4314059 : Blo 1915435 4314059 := bstep (se 1 (by rfl) ⟨3235544, by rfl⟩ : syracuseStep 4314059 = 6471089) B6471089
theorem B2876039 : Blo 1915435 2876039 := bstep (se 1 (by rfl) ⟨2157029, by rfl⟩ : syracuseStep 2876039 = 4314059) B4314059
theorem B1917359 : Blo 1915435 1917359 := bstep (se 1 (by rfl) ⟨1438019, by rfl⟩ : syracuseStep 1917359 = 2876039) B2876039
theorem B2876045 : Blo 1915435 2876045 := bbase (se 3 (by rfl) ⟨539258, by rfl⟩ : syracuseStep 2876045 = 1078517) (by norm_num)
theorem B1917363 : Blo 1915435 1917363 := bstep (se 1 (by rfl) ⟨1438022, by rfl⟩ : syracuseStep 1917363 = 2876045) B2876045
theorem B4314077 : Blo 1915435 4314077 := bbase (se 3 (by rfl) ⟨808889, by rfl⟩ : syracuseStep 4314077 = 1617779) (by norm_num)
theorem B2876051 : Blo 1915435 2876051 := bstep (se 1 (by rfl) ⟨2157038, by rfl⟩ : syracuseStep 2876051 = 4314077) B4314077
theorem B1917367 : Blo 1915435 1917367 := bstep (se 1 (by rfl) ⟨1438025, by rfl⟩ : syracuseStep 1917367 = 2876051) B2876051
theorem B3235565 : Blo 1915435 3235565 := bbase (se 3 (by rfl) ⟨606668, by rfl⟩ : syracuseStep 3235565 = 1213337) (by norm_num)
theorem B2157043 : Blo 1915435 2157043 := bstep (se 1 (by rfl) ⟨1617782, by rfl⟩ : syracuseStep 2157043 = 3235565) B3235565
theorem B2876057 : Blo 1915435 2876057 := bstep (se 2 (by rfl) ⟨1078521, by rfl⟩ : syracuseStep 2876057 = 2157043) B2157043
theorem B1917371 : Blo 1915435 1917371 := bstep (se 1 (by rfl) ⟨1438028, by rfl⟩ : syracuseStep 1917371 = 2876057) B2876057
theorem B9213797 : Blo 1915435 9213797 := bbase (se 4 (by rfl) ⟨863793, by rfl⟩ : syracuseStep 9213797 = 1727587) (by norm_num)
theorem B24570125 : Blo 1915435 24570125 := bstep (se 3 (by rfl) ⟨4606898, by rfl⟩ : syracuseStep 24570125 = 9213797) B9213797
theorem B16380083 : Blo 1915435 16380083 := bstep (se 1 (by rfl) ⟨12285062, by rfl⟩ : syracuseStep 16380083 = 24570125) B24570125
theorem B10920055 : Blo 1915435 10920055 := bstep (se 1 (by rfl) ⟨8190041, by rfl⟩ : syracuseStep 10920055 = 16380083) B16380083
theorem B14560073 : Blo 1915435 14560073 := bstep (se 2 (by rfl) ⟨5460027, by rfl⟩ : syracuseStep 14560073 = 10920055) B10920055
theorem B9706715 : Blo 1915435 9706715 := bstep (se 1 (by rfl) ⟨7280036, by rfl⟩ : syracuseStep 9706715 = 14560073) B14560073
theorem B6471143 : Blo 1915435 6471143 := bstep (se 1 (by rfl) ⟨4853357, by rfl⟩ : syracuseStep 6471143 = 9706715) B9706715
theorem B4314095 : Blo 1915435 4314095 := bstep (se 1 (by rfl) ⟨3235571, by rfl⟩ : syracuseStep 4314095 = 6471143) B6471143
theorem B2876063 : Blo 1915435 2876063 := bstep (se 1 (by rfl) ⟨2157047, by rfl⟩ : syracuseStep 2876063 = 4314095) B4314095
theorem B1917375 : Blo 1915435 1917375 := bstep (se 1 (by rfl) ⟨1438031, by rfl⟩ : syracuseStep 1917375 = 2876063) B2876063
theorem B2876069 : Blo 1915435 2876069 := bbase (se 4 (by rfl) ⟨269631, by rfl⟩ : syracuseStep 2876069 = 539263) (by norm_num)
theorem B1917379 : Blo 1915435 1917379 := bstep (se 1 (by rfl) ⟨1438034, by rfl⟩ : syracuseStep 1917379 = 2876069) B2876069
theorem B2426689 : Blo 1915435 2426689 := bbase (se 2 (by rfl) ⟨910008, by rfl⟩ : syracuseStep 2426689 = 1820017) (by norm_num)
theorem B3235585 : Blo 1915435 3235585 := bstep (se 2 (by rfl) ⟨1213344, by rfl⟩ : syracuseStep 3235585 = 2426689) B2426689
theorem B4314113 : Blo 1915435 4314113 := bstep (se 2 (by rfl) ⟨1617792, by rfl⟩ : syracuseStep 4314113 = 3235585) B3235585
theorem B2876075 : Blo 1915435 2876075 := bstep (se 1 (by rfl) ⟨2157056, by rfl⟩ : syracuseStep 2876075 = 4314113) B4314113
theorem B1917383 : Blo 1915435 1917383 := bstep (se 1 (by rfl) ⟨1438037, by rfl⟩ : syracuseStep 1917383 = 2876075) B2876075
theorem B2157061 : Blo 1915435 2157061 := bbase (se 4 (by rfl) ⟨202224, by rfl⟩ : syracuseStep 2157061 = 404449) (by norm_num)
theorem B2876081 : Blo 1915435 2876081 := bstep (se 2 (by rfl) ⟨1078530, by rfl⟩ : syracuseStep 2876081 = 2157061) B2157061
theorem B1917387 : Blo 1915435 1917387 := bstep (se 1 (by rfl) ⟨1438040, by rfl⟩ : syracuseStep 1917387 = 2876081) B2876081
theorem B2730037 : Blo 1915435 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B3640049 : Blo 1915435 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B2426699 : Blo 1915435 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B6471197 : Blo 1915435 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B4314131 : Blo 1915435 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B2876087 : Blo 1915435 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B1917391 : Blo 1915435 1917391 := bstep (se 1 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 1917391 = 2876087) B2876087
theorem B2876093 : Blo 1915435 2876093 := bbase (se 3 (by rfl) ⟨539267, by rfl⟩ : syracuseStep 2876093 = 1078535) (by norm_num)
theorem B1917395 : Blo 1915435 1917395 := bstep (se 1 (by rfl) ⟨1438046, by rfl⟩ : syracuseStep 1917395 = 2876093) B2876093
theorem B4314149 : Blo 1915435 4314149 := bbase (se 4 (by rfl) ⟨404451, by rfl⟩ : syracuseStep 4314149 = 808903) (by norm_num)
theorem B2876099 : Blo 1915435 2876099 := bstep (se 1 (by rfl) ⟨2157074, by rfl⟩ : syracuseStep 2876099 = 4314149) B4314149
theorem B1917399 : Blo 1915435 1917399 := bstep (se 1 (by rfl) ⟨1438049, by rfl⟩ : syracuseStep 1917399 = 2876099) B2876099
theorem B4853429 : Blo 1915435 4853429 := bbase (se 5 (by rfl) ⟨227504, by rfl⟩ : syracuseStep 4853429 = 455009) (by norm_num)
theorem B3235619 : Blo 1915435 3235619 := bstep (se 1 (by rfl) ⟨2426714, by rfl⟩ : syracuseStep 3235619 = 4853429) B4853429
theorem B2157079 : Blo 1915435 2157079 := bstep (se 1 (by rfl) ⟨1617809, by rfl⟩ : syracuseStep 2157079 = 3235619) B3235619
theorem B2876105 : Blo 1915435 2876105 := bstep (se 2 (by rfl) ⟨1078539, by rfl⟩ : syracuseStep 2876105 = 2157079) B2157079
theorem B1917403 : Blo 1915435 1917403 := bstep (se 1 (by rfl) ⟨1438052, by rfl⟩ : syracuseStep 1917403 = 2876105) B2876105
theorem B12285269 : Blo 1915435 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B8190179 : Blo 1915435 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B5460119 : Blo 1915435 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B3640079 : Blo 1915435 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B9706877 : Blo 1915435 9706877 := bstep (se 3 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 9706877 = 3640079) B3640079
theorem B6471251 : Blo 1915435 6471251 := bstep (se 1 (by rfl) ⟨4853438, by rfl⟩ : syracuseStep 6471251 = 9706877) B9706877
theorem B4314167 : Blo 1915435 4314167 := bstep (se 1 (by rfl) ⟨3235625, by rfl⟩ : syracuseStep 4314167 = 6471251) B6471251
theorem B2876111 : Blo 1915435 2876111 := bstep (se 1 (by rfl) ⟨2157083, by rfl⟩ : syracuseStep 2876111 = 4314167) B4314167
theorem B1917407 : Blo 1915435 1917407 := bstep (se 1 (by rfl) ⟨1438055, by rfl⟩ : syracuseStep 1917407 = 2876111) B2876111
theorem B2876117 : Blo 1915435 2876117 := bbase (se 7 (by rfl) ⟨33704, by rfl⟩ : syracuseStep 2876117 = 67409) (by norm_num)
theorem B1917411 : Blo 1915435 1917411 := bstep (se 1 (by rfl) ⟨1438058, by rfl⟩ : syracuseStep 1917411 = 2876117) B2876117
theorem B6142661 : Blo 1915435 6142661 := bbase (se 4 (by rfl) ⟨575874, by rfl⟩ : syracuseStep 6142661 = 1151749) (by norm_num)
theorem B4095107 : Blo 1915435 4095107 := bstep (se 1 (by rfl) ⟨3071330, by rfl⟩ : syracuseStep 4095107 = 6142661) B6142661
theorem B2730071 : Blo 1915435 2730071 := bstep (se 1 (by rfl) ⟨2047553, by rfl⟩ : syracuseStep 2730071 = 4095107) B4095107
theorem B7280189 : Blo 1915435 7280189 := bstep (se 3 (by rfl) ⟨1365035, by rfl⟩ : syracuseStep 7280189 = 2730071) B2730071
theorem B4853459 : Blo 1915435 4853459 := bstep (se 1 (by rfl) ⟨3640094, by rfl⟩ : syracuseStep 4853459 = 7280189) B7280189
theorem B3235639 : Blo 1915435 3235639 := bstep (se 1 (by rfl) ⟨2426729, by rfl⟩ : syracuseStep 3235639 = 4853459) B4853459
theorem B4314185 : Blo 1915435 4314185 := bstep (se 2 (by rfl) ⟨1617819, by rfl⟩ : syracuseStep 4314185 = 3235639) B3235639
theorem B2876123 : Blo 1915435 2876123 := bstep (se 1 (by rfl) ⟨2157092, by rfl⟩ : syracuseStep 2876123 = 4314185) B4314185
theorem B1917415 : Blo 1915435 1917415 := bstep (se 1 (by rfl) ⟨1438061, by rfl⟩ : syracuseStep 1917415 = 2876123) B2876123
theorem B2157097 : Blo 1915435 2157097 := bbase (se 2 (by rfl) ⟨808911, by rfl⟩ : syracuseStep 2157097 = 1617823) (by norm_num)
theorem B2876129 : Blo 1915435 2876129 := bstep (se 2 (by rfl) ⟨1078548, by rfl⟩ : syracuseStep 2876129 = 2157097) B2157097
theorem B1917419 : Blo 1915435 1917419 := bstep (se 1 (by rfl) ⟨1438064, by rfl⟩ : syracuseStep 1917419 = 2876129) B2876129
theorem B4150997 : Blo 1915435 4150997 := bbase (se 7 (by rfl) ⟨48644, by rfl⟩ : syracuseStep 4150997 = 97289) (by norm_num)
theorem B2767331 : Blo 1915435 2767331 := bstep (se 1 (by rfl) ⟨2075498, by rfl⟩ : syracuseStep 2767331 = 4150997) B4150997
theorem B7379549 : Blo 1915435 7379549 := bstep (se 3 (by rfl) ⟨1383665, by rfl⟩ : syracuseStep 7379549 = 2767331) B2767331
theorem B4919699 : Blo 1915435 4919699 := bstep (se 1 (by rfl) ⟨3689774, by rfl⟩ : syracuseStep 4919699 = 7379549) B7379549
theorem B3279799 : Blo 1915435 3279799 := bstep (se 1 (by rfl) ⟨2459849, by rfl⟩ : syracuseStep 3279799 = 4919699) B4919699
theorem B4373065 : Blo 1915435 4373065 := bstep (se 2 (by rfl) ⟨1639899, by rfl⟩ : syracuseStep 4373065 = 3279799) B3279799
theorem B5830753 : Blo 1915435 5830753 := bstep (se 2 (by rfl) ⟨2186532, by rfl⟩ : syracuseStep 5830753 = 4373065) B4373065
theorem B7774337 : Blo 1915435 7774337 := bstep (se 2 (by rfl) ⟨2915376, by rfl⟩ : syracuseStep 7774337 = 5830753) B5830753
theorem B20731565 : Blo 1915435 20731565 := bstep (se 3 (by rfl) ⟨3887168, by rfl⟩ : syracuseStep 20731565 = 7774337) B7774337
theorem B13821043 : Blo 1915435 13821043 := bstep (se 1 (by rfl) ⟨10365782, by rfl⟩ : syracuseStep 13821043 = 20731565) B20731565
theorem B18428057 : Blo 1915435 18428057 := bstep (se 2 (by rfl) ⟨6910521, by rfl⟩ : syracuseStep 18428057 = 13821043) B13821043
theorem B12285371 : Blo 1915435 12285371 := bstep (se 1 (by rfl) ⟨9214028, by rfl⟩ : syracuseStep 12285371 = 18428057) B18428057
theorem B8190247 : Blo 1915435 8190247 := bstep (se 1 (by rfl) ⟨6142685, by rfl⟩ : syracuseStep 8190247 = 12285371) B12285371
theorem B10920329 : Blo 1915435 10920329 := bstep (se 2 (by rfl) ⟨4095123, by rfl⟩ : syracuseStep 10920329 = 8190247) B8190247
theorem B7280219 : Blo 1915435 7280219 := bstep (se 1 (by rfl) ⟨5460164, by rfl⟩ : syracuseStep 7280219 = 10920329) B10920329
theorem B4853479 : Blo 1915435 4853479 := bstep (se 1 (by rfl) ⟨3640109, by rfl⟩ : syracuseStep 4853479 = 7280219) B7280219
theorem B6471305 : Blo 1915435 6471305 := bstep (se 2 (by rfl) ⟨2426739, by rfl⟩ : syracuseStep 6471305 = 4853479) B4853479
theorem B4314203 : Blo 1915435 4314203 := bstep (se 1 (by rfl) ⟨3235652, by rfl⟩ : syracuseStep 4314203 = 6471305) B6471305
theorem B2876135 : Blo 1915435 2876135 := bstep (se 1 (by rfl) ⟨2157101, by rfl⟩ : syracuseStep 2876135 = 4314203) B4314203
theorem B1917423 : Blo 1915435 1917423 := bstep (se 1 (by rfl) ⟨1438067, by rfl⟩ : syracuseStep 1917423 = 2876135) B2876135
theorem B2876141 : Blo 1915435 2876141 := bbase (se 3 (by rfl) ⟨539276, by rfl⟩ : syracuseStep 2876141 = 1078553) (by norm_num)
theorem B1917427 : Blo 1915435 1917427 := bstep (se 1 (by rfl) ⟨1438070, by rfl⟩ : syracuseStep 1917427 = 2876141) B2876141
theorem B4314221 : Blo 1915435 4314221 := bbase (se 3 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 4314221 = 1617833) (by norm_num)
theorem B2876147 : Blo 1915435 2876147 := bstep (se 1 (by rfl) ⟨2157110, by rfl⟩ : syracuseStep 2876147 = 4314221) B4314221
theorem B1917431 : Blo 1915435 1917431 := bstep (se 1 (by rfl) ⟨1438073, by rfl⟩ : syracuseStep 1917431 = 2876147) B2876147
theorem B3640133 : Blo 1915435 3640133 := bbase (se 4 (by rfl) ⟨341262, by rfl⟩ : syracuseStep 3640133 = 682525) (by norm_num)
theorem B2426755 : Blo 1915435 2426755 := bstep (se 1 (by rfl) ⟨1820066, by rfl⟩ : syracuseStep 2426755 = 3640133) B3640133
theorem B3235673 : Blo 1915435 3235673 := bstep (se 2 (by rfl) ⟨1213377, by rfl⟩ : syracuseStep 3235673 = 2426755) B2426755
theorem B2157115 : Blo 1915435 2157115 := bstep (se 1 (by rfl) ⟨1617836, by rfl⟩ : syracuseStep 2157115 = 3235673) B3235673
theorem B2876153 : Blo 1915435 2876153 := bstep (se 2 (by rfl) ⟨1078557, by rfl⟩ : syracuseStep 2876153 = 2157115) B2157115
theorem B1917435 : Blo 1915435 1917435 := bstep (se 1 (by rfl) ⟨1438076, by rfl⟩ : syracuseStep 1917435 = 2876153) B2876153
theorem C0 (j : ℕ) (h1 : 478858 ≤ j) (h2 : j ≤ 479358) : Blo 1915435 (4 * j + 3) := by
  interval_cases j
  · exact B1915435
  · exact B1915439
  · exact B1915443
  · exact B1915447
  · exact B1915451
  · exact B1915455
  · exact B1915459
  · exact B1915463
  · exact B1915467
  · exact B1915471
  · exact B1915475
  · exact B1915479
  · exact B1915483
  · exact B1915487
  · exact B1915491
  · exact B1915495
  · exact B1915499
  · exact B1915503
  · exact B1915507
  · exact B1915511
  · exact B1915515
  · exact B1915519
  · exact B1915523
  · exact B1915527
  · exact B1915531
  · exact B1915535
  · exact B1915539
  · exact B1915543
  · exact B1915547
  · exact B1915551
  · exact B1915555
  · exact B1915559
  · exact B1915563
  · exact B1915567
  · exact B1915571
  · exact B1915575
  · exact B1915579
  · exact B1915583
  · exact B1915587
  · exact B1915591
  · exact B1915595
  · exact B1915599
  · exact B1915603
  · exact B1915607
  · exact B1915611
  · exact B1915615
  · exact B1915619
  · exact B1915623
  · exact B1915627
  · exact B1915631
  · exact B1915635
  · exact B1915639
  · exact B1915643
  · exact B1915647
  · exact B1915651
  · exact B1915655
  · exact B1915659
  · exact B1915663
  · exact B1915667
  · exact B1915671
  · exact B1915675
  · exact B1915679
  · exact B1915683
  · exact B1915687
  · exact B1915691
  · exact B1915695
  · exact B1915699
  · exact B1915703
  · exact B1915707
  · exact B1915711
  · exact B1915715
  · exact B1915719
  · exact B1915723
  · exact B1915727
  · exact B1915731
  · exact B1915735
  · exact B1915739
  · exact B1915743
  · exact B1915747
  · exact B1915751
  · exact B1915755
  · exact B1915759
  · exact B1915763
  · exact B1915767
  · exact B1915771
  · exact B1915775
  · exact B1915779
  · exact B1915783
  · exact B1915787
  · exact B1915791
  · exact B1915795
  · exact B1915799
  · exact B1915803
  · exact B1915807
  · exact B1915811
  · exact B1915815
  · exact B1915819
  · exact B1915823
  · exact B1915827
  · exact B1915831
  · exact B1915835
  · exact B1915839
  · exact B1915843
  · exact B1915847
  · exact B1915851
  · exact B1915855
  · exact B1915859
  · exact B1915863
  · exact B1915867
  · exact B1915871
  · exact B1915875
  · exact B1915879
  · exact B1915883
  · exact B1915887
  · exact B1915891
  · exact B1915895
  · exact B1915899
  · exact B1915903
  · exact B1915907
  · exact B1915911
  · exact B1915915
  · exact B1915919
  · exact B1915923
  · exact B1915927
  · exact B1915931
  · exact B1915935
  · exact B1915939
  · exact B1915943
  · exact B1915947
  · exact B1915951
  · exact B1915955
  · exact B1915959
  · exact B1915963
  · exact B1915967
  · exact B1915971
  · exact B1915975
  · exact B1915979
  · exact B1915983
  · exact B1915987
  · exact B1915991
  · exact B1915995
  · exact B1915999
  · exact B1916003
  · exact B1916007
  · exact B1916011
  · exact B1916015
  · exact B1916019
  · exact B1916023
  · exact B1916027
  · exact B1916031
  · exact B1916035
  · exact B1916039
  · exact B1916043
  · exact B1916047
  · exact B1916051
  · exact B1916055
  · exact B1916059
  · exact B1916063
  · exact B1916067
  · exact B1916071
  · exact B1916075
  · exact B1916079
  · exact B1916083
  · exact B1916087
  · exact B1916091
  · exact B1916095
  · exact B1916099
  · exact B1916103
  · exact B1916107
  · exact B1916111
  · exact B1916115
  · exact B1916119
  · exact B1916123
  · exact B1916127
  · exact B1916131
  · exact B1916135
  · exact B1916139
  · exact B1916143
  · exact B1916147
  · exact B1916151
  · exact B1916155
  · exact B1916159
  · exact B1916163
  · exact B1916167
  · exact B1916171
  · exact B1916175
  · exact B1916179
  · exact B1916183
  · exact B1916187
  · exact B1916191
  · exact B1916195
  · exact B1916199
  · exact B1916203
  · exact B1916207
  · exact B1916211
  · exact B1916215
  · exact B1916219
  · exact B1916223
  · exact B1916227
  · exact B1916231
  · exact B1916235
  · exact B1916239
  · exact B1916243
  · exact B1916247
  · exact B1916251
  · exact B1916255
  · exact B1916259
  · exact B1916263
  · exact B1916267
  · exact B1916271
  · exact B1916275
  · exact B1916279
  · exact B1916283
  · exact B1916287
  · exact B1916291
  · exact B1916295
  · exact B1916299
  · exact B1916303
  · exact B1916307
  · exact B1916311
  · exact B1916315
  · exact B1916319
  · exact B1916323
  · exact B1916327
  · exact B1916331
  · exact B1916335
  · exact B1916339
  · exact B1916343
  · exact B1916347
  · exact B1916351
  · exact B1916355
  · exact B1916359
  · exact B1916363
  · exact B1916367
  · exact B1916371
  · exact B1916375
  · exact B1916379
  · exact B1916383
  · exact B1916387
  · exact B1916391
  · exact B1916395
  · exact B1916399
  · exact B1916403
  · exact B1916407
  · exact B1916411
  · exact B1916415
  · exact B1916419
  · exact B1916423
  · exact B1916427
  · exact B1916431
  · exact B1916435
  · exact B1916439
  · exact B1916443
  · exact B1916447
  · exact B1916451
  · exact B1916455
  · exact B1916459
  · exact B1916463
  · exact B1916467
  · exact B1916471
  · exact B1916475
  · exact B1916479
  · exact B1916483
  · exact B1916487
  · exact B1916491
  · exact B1916495
  · exact B1916499
  · exact B1916503
  · exact B1916507
  · exact B1916511
  · exact B1916515
  · exact B1916519
  · exact B1916523
  · exact B1916527
  · exact B1916531
  · exact B1916535
  · exact B1916539
  · exact B1916543
  · exact B1916547
  · exact B1916551
  · exact B1916555
  · exact B1916559
  · exact B1916563
  · exact B1916567
  · exact B1916571
  · exact B1916575
  · exact B1916579
  · exact B1916583
  · exact B1916587
  · exact B1916591
  · exact B1916595
  · exact B1916599
  · exact B1916603
  · exact B1916607
  · exact B1916611
  · exact B1916615
  · exact B1916619
  · exact B1916623
  · exact B1916627
  · exact B1916631
  · exact B1916635
  · exact B1916639
  · exact B1916643
  · exact B1916647
  · exact B1916651
  · exact B1916655
  · exact B1916659
  · exact B1916663
  · exact B1916667
  · exact B1916671
  · exact B1916675
  · exact B1916679
  · exact B1916683
  · exact B1916687
  · exact B1916691
  · exact B1916695
  · exact B1916699
  · exact B1916703
  · exact B1916707
  · exact B1916711
  · exact B1916715
  · exact B1916719
  · exact B1916723
  · exact B1916727
  · exact B1916731
  · exact B1916735
  · exact B1916739
  · exact B1916743
  · exact B1916747
  · exact B1916751
  · exact B1916755
  · exact B1916759
  · exact B1916763
  · exact B1916767
  · exact B1916771
  · exact B1916775
  · exact B1916779
  · exact B1916783
  · exact B1916787
  · exact B1916791
  · exact B1916795
  · exact B1916799
  · exact B1916803
  · exact B1916807
  · exact B1916811
  · exact B1916815
  · exact B1916819
  · exact B1916823
  · exact B1916827
  · exact B1916831
  · exact B1916835
  · exact B1916839
  · exact B1916843
  · exact B1916847
  · exact B1916851
  · exact B1916855
  · exact B1916859
  · exact B1916863
  · exact B1916867
  · exact B1916871
  · exact B1916875
  · exact B1916879
  · exact B1916883
  · exact B1916887
  · exact B1916891
  · exact B1916895
  · exact B1916899
  · exact B1916903
  · exact B1916907
  · exact B1916911
  · exact B1916915
  · exact B1916919
  · exact B1916923
  · exact B1916927
  · exact B1916931
  · exact B1916935
  · exact B1916939
  · exact B1916943
  · exact B1916947
  · exact B1916951
  · exact B1916955
  · exact B1916959
  · exact B1916963
  · exact B1916967
  · exact B1916971
  · exact B1916975
  · exact B1916979
  · exact B1916983
  · exact B1916987
  · exact B1916991
  · exact B1916995
  · exact B1916999
  · exact B1917003
  · exact B1917007
  · exact B1917011
  · exact B1917015
  · exact B1917019
  · exact B1917023
  · exact B1917027
  · exact B1917031
  · exact B1917035
  · exact B1917039
  · exact B1917043
  · exact B1917047
  · exact B1917051
  · exact B1917055
  · exact B1917059
  · exact B1917063
  · exact B1917067
  · exact B1917071
  · exact B1917075
  · exact B1917079
  · exact B1917083
  · exact B1917087
  · exact B1917091
  · exact B1917095
  · exact B1917099
  · exact B1917103
  · exact B1917107
  · exact B1917111
  · exact B1917115
  · exact B1917119
  · exact B1917123
  · exact B1917127
  · exact B1917131
  · exact B1917135
  · exact B1917139
  · exact B1917143
  · exact B1917147
  · exact B1917151
  · exact B1917155
  · exact B1917159
  · exact B1917163
  · exact B1917167
  · exact B1917171
  · exact B1917175
  · exact B1917179
  · exact B1917183
  · exact B1917187
  · exact B1917191
  · exact B1917195
  · exact B1917199
  · exact B1917203
  · exact B1917207
  · exact B1917211
  · exact B1917215
  · exact B1917219
  · exact B1917223
  · exact B1917227
  · exact B1917231
  · exact B1917235
  · exact B1917239
  · exact B1917243
  · exact B1917247
  · exact B1917251
  · exact B1917255
  · exact B1917259
  · exact B1917263
  · exact B1917267
  · exact B1917271
  · exact B1917275
  · exact B1917279
  · exact B1917283
  · exact B1917287
  · exact B1917291
  · exact B1917295
  · exact B1917299
  · exact B1917303
  · exact B1917307
  · exact B1917311
  · exact B1917315
  · exact B1917319
  · exact B1917323
  · exact B1917327
  · exact B1917331
  · exact B1917335
  · exact B1917339
  · exact B1917343
  · exact B1917347
  · exact B1917351
  · exact B1917355
  · exact B1917359
  · exact B1917363
  · exact B1917367
  · exact B1917371
  · exact B1917375
  · exact B1917379
  · exact B1917383
  · exact B1917387
  · exact B1917391
  · exact B1917395
  · exact B1917399
  · exact B1917403
  · exact B1917407
  · exact B1917411
  · exact B1917415
  · exact B1917419
  · exact B1917423
  · exact B1917427
  · exact B1917431
  · exact B1917435
theorem solution (m : ℕ) (hlo : 1915435 ≤ m) (hhi : m ≤ 1917435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 478858 ≤ j := by omega
    have hj2 : j ≤ 479358 := by omega
    have hb : Blo 1915435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
