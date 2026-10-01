-- Prove2me | solution 1 for syracuse_descends_range_1887435_1889435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:37.731381+00:00
-- url     : https://prove2.me/submissions/cd39b7cc-b638-465a-b2fb-f95c16b363c4

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

theorem B2123365 : Blo 1887435 2123365 := bbase (se 4 (by rfl) ⟨199065, by rfl⟩ : syracuseStep 2123365 = 398131) (by norm_num)
theorem B2831153 : Blo 1887435 2831153 := bstep (se 2 (by rfl) ⟨1061682, by rfl⟩ : syracuseStep 2831153 = 2123365) B2123365
theorem B1887435 : Blo 1887435 1887435 := bstep (se 1 (by rfl) ⟨1415576, by rfl⟩ : syracuseStep 1887435 = 2831153) B2831153
theorem B4534973 : Blo 1887435 4534973 := bbase (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) (by norm_num)
theorem B3023315 : Blo 1887435 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B2015543 : Blo 1887435 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B5374781 : Blo 1887435 5374781 := bstep (se 3 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 5374781 = 2015543) B2015543
theorem B3583187 : Blo 1887435 3583187 := bstep (se 1 (by rfl) ⟨2687390, by rfl⟩ : syracuseStep 3583187 = 5374781) B5374781
theorem B2388791 : Blo 1887435 2388791 := bstep (se 1 (by rfl) ⟨1791593, by rfl⟩ : syracuseStep 2388791 = 3583187) B3583187
theorem B6370109 : Blo 1887435 6370109 := bstep (se 3 (by rfl) ⟨1194395, by rfl⟩ : syracuseStep 6370109 = 2388791) B2388791
theorem B4246739 : Blo 1887435 4246739 := bstep (se 1 (by rfl) ⟨3185054, by rfl⟩ : syracuseStep 4246739 = 6370109) B6370109
theorem B2831159 : Blo 1887435 2831159 := bstep (se 1 (by rfl) ⟨2123369, by rfl⟩ : syracuseStep 2831159 = 4246739) B4246739
theorem B1887439 : Blo 1887435 1887439 := bstep (se 1 (by rfl) ⟨1415579, by rfl⟩ : syracuseStep 1887439 = 2831159) B2831159
theorem B2831165 : Blo 1887435 2831165 := bbase (se 3 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 2831165 = 1061687) (by norm_num)
theorem B1887443 : Blo 1887435 1887443 := bstep (se 1 (by rfl) ⟨1415582, by rfl⟩ : syracuseStep 1887443 = 2831165) B2831165
theorem B4246757 : Blo 1887435 4246757 := bbase (se 4 (by rfl) ⟨398133, by rfl⟩ : syracuseStep 4246757 = 796267) (by norm_num)
theorem B2831171 : Blo 1887435 2831171 := bstep (se 1 (by rfl) ⟨2123378, by rfl⟩ : syracuseStep 2831171 = 4246757) B4246757
theorem B1887447 : Blo 1887435 1887447 := bstep (se 1 (by rfl) ⟨1415585, by rfl⟩ : syracuseStep 1887447 = 2831171) B2831171
theorem B4777613 : Blo 1887435 4777613 := bbase (se 3 (by rfl) ⟨895802, by rfl⟩ : syracuseStep 4777613 = 1791605) (by norm_num)
theorem B3185075 : Blo 1887435 3185075 := bstep (se 1 (by rfl) ⟨2388806, by rfl⟩ : syracuseStep 3185075 = 4777613) B4777613
theorem B2123383 : Blo 1887435 2123383 := bstep (se 1 (by rfl) ⟨1592537, by rfl⟩ : syracuseStep 2123383 = 3185075) B3185075
theorem B2831177 : Blo 1887435 2831177 := bstep (se 2 (by rfl) ⟨1061691, by rfl⟩ : syracuseStep 2831177 = 2123383) B2123383
theorem B1887451 : Blo 1887435 1887451 := bstep (se 1 (by rfl) ⟨1415588, by rfl⟩ : syracuseStep 1887451 = 2831177) B2831177
theorem B2687413 : Blo 1887435 2687413 := bbase (se 5 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 2687413 = 251945) (by norm_num)
theorem B3583217 : Blo 1887435 3583217 := bstep (se 2 (by rfl) ⟨1343706, by rfl⟩ : syracuseStep 3583217 = 2687413) B2687413
theorem B9555245 : Blo 1887435 9555245 := bstep (se 3 (by rfl) ⟨1791608, by rfl⟩ : syracuseStep 9555245 = 3583217) B3583217
theorem B6370163 : Blo 1887435 6370163 := bstep (se 1 (by rfl) ⟨4777622, by rfl⟩ : syracuseStep 6370163 = 9555245) B9555245
theorem B4246775 : Blo 1887435 4246775 := bstep (se 1 (by rfl) ⟨3185081, by rfl⟩ : syracuseStep 4246775 = 6370163) B6370163
theorem B2831183 : Blo 1887435 2831183 := bstep (se 1 (by rfl) ⟨2123387, by rfl⟩ : syracuseStep 2831183 = 4246775) B4246775
theorem B1887455 : Blo 1887435 1887455 := bstep (se 1 (by rfl) ⟨1415591, by rfl⟩ : syracuseStep 1887455 = 2831183) B2831183
theorem B2831189 : Blo 1887435 2831189 := bbase (se 9 (by rfl) ⟨8294, by rfl⟩ : syracuseStep 2831189 = 16589) (by norm_num)
theorem B1887459 : Blo 1887435 1887459 := bstep (se 1 (by rfl) ⟨1415594, by rfl⟩ : syracuseStep 1887459 = 2831189) B2831189
theorem B2152369 : Blo 1887435 2152369 := bbase (se 2 (by rfl) ⟨807138, by rfl⟩ : syracuseStep 2152369 = 1614277) (by norm_num)
theorem B2869825 : Blo 1887435 2869825 := bstep (se 2 (by rfl) ⟨1076184, by rfl⟩ : syracuseStep 2869825 = 2152369) B2152369
theorem B3826433 : Blo 1887435 3826433 := bstep (se 2 (by rfl) ⟨1434912, by rfl⟩ : syracuseStep 3826433 = 2869825) B2869825
theorem B2550955 : Blo 1887435 2550955 := bstep (se 1 (by rfl) ⟨1913216, by rfl⟩ : syracuseStep 2550955 = 3826433) B3826433
theorem B3401273 : Blo 1887435 3401273 := bstep (se 2 (by rfl) ⟨1275477, by rfl⟩ : syracuseStep 3401273 = 2550955) B2550955
theorem B2267515 : Blo 1887435 2267515 := bstep (se 1 (by rfl) ⟨1700636, by rfl⟩ : syracuseStep 2267515 = 3401273) B3401273
theorem B3023353 : Blo 1887435 3023353 := bstep (se 2 (by rfl) ⟨1133757, by rfl⟩ : syracuseStep 3023353 = 2267515) B2267515
theorem B4031137 : Blo 1887435 4031137 := bstep (se 2 (by rfl) ⟨1511676, by rfl⟩ : syracuseStep 4031137 = 3023353) B3023353
theorem B5374849 : Blo 1887435 5374849 := bstep (se 2 (by rfl) ⟨2015568, by rfl⟩ : syracuseStep 5374849 = 4031137) B4031137
theorem B7166465 : Blo 1887435 7166465 := bstep (se 2 (by rfl) ⟨2687424, by rfl⟩ : syracuseStep 7166465 = 5374849) B5374849
theorem B4777643 : Blo 1887435 4777643 := bstep (se 1 (by rfl) ⟨3583232, by rfl⟩ : syracuseStep 4777643 = 7166465) B7166465
theorem B3185095 : Blo 1887435 3185095 := bstep (se 1 (by rfl) ⟨2388821, by rfl⟩ : syracuseStep 3185095 = 4777643) B4777643
theorem B4246793 : Blo 1887435 4246793 := bstep (se 2 (by rfl) ⟨1592547, by rfl⟩ : syracuseStep 4246793 = 3185095) B3185095
theorem B2831195 : Blo 1887435 2831195 := bstep (se 1 (by rfl) ⟨2123396, by rfl⟩ : syracuseStep 2831195 = 4246793) B4246793
theorem B1887463 : Blo 1887435 1887463 := bstep (se 1 (by rfl) ⟨1415597, by rfl⟩ : syracuseStep 1887463 = 2831195) B2831195
theorem B2123401 : Blo 1887435 2123401 := bbase (se 2 (by rfl) ⟨796275, by rfl⟩ : syracuseStep 2123401 = 1592551) (by norm_num)
theorem B2831201 : Blo 1887435 2831201 := bstep (se 2 (by rfl) ⟨1061700, by rfl⟩ : syracuseStep 2831201 = 2123401) B2123401
theorem B1887467 : Blo 1887435 1887467 := bstep (se 1 (by rfl) ⟨1415600, by rfl⟩ : syracuseStep 1887467 = 2831201) B2831201
theorem B12914261 : Blo 1887435 12914261 := bbase (se 8 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 12914261 = 151339) (by norm_num)
theorem B8609507 : Blo 1887435 8609507 := bstep (se 1 (by rfl) ⟨6457130, by rfl⟩ : syracuseStep 8609507 = 12914261) B12914261
theorem B5739671 : Blo 1887435 5739671 := bstep (se 1 (by rfl) ⟨4304753, by rfl⟩ : syracuseStep 5739671 = 8609507) B8609507
theorem B3826447 : Blo 1887435 3826447 := bstep (se 1 (by rfl) ⟨2869835, by rfl⟩ : syracuseStep 3826447 = 5739671) B5739671
theorem B20407717 : Blo 1887435 20407717 := bstep (se 4 (by rfl) ⟨1913223, by rfl⟩ : syracuseStep 20407717 = 3826447) B3826447
theorem B27210289 : Blo 1887435 27210289 := bstep (se 2 (by rfl) ⟨10203858, by rfl⟩ : syracuseStep 27210289 = 20407717) B20407717
theorem B36280385 : Blo 1887435 36280385 := bstep (se 2 (by rfl) ⟨13605144, by rfl⟩ : syracuseStep 36280385 = 27210289) B27210289
theorem B24186923 : Blo 1887435 24186923 := bstep (se 1 (by rfl) ⟨18140192, by rfl⟩ : syracuseStep 24186923 = 36280385) B36280385
theorem B16124615 : Blo 1887435 16124615 := bstep (se 1 (by rfl) ⟨12093461, by rfl⟩ : syracuseStep 16124615 = 24186923) B24186923
theorem B10749743 : Blo 1887435 10749743 := bstep (se 1 (by rfl) ⟨8062307, by rfl⟩ : syracuseStep 10749743 = 16124615) B16124615
theorem B7166495 : Blo 1887435 7166495 := bstep (se 1 (by rfl) ⟨5374871, by rfl⟩ : syracuseStep 7166495 = 10749743) B10749743
theorem B4777663 : Blo 1887435 4777663 := bstep (se 1 (by rfl) ⟨3583247, by rfl⟩ : syracuseStep 4777663 = 7166495) B7166495
theorem B6370217 : Blo 1887435 6370217 := bstep (se 2 (by rfl) ⟨2388831, by rfl⟩ : syracuseStep 6370217 = 4777663) B4777663
theorem B4246811 : Blo 1887435 4246811 := bstep (se 1 (by rfl) ⟨3185108, by rfl⟩ : syracuseStep 4246811 = 6370217) B6370217
theorem B2831207 : Blo 1887435 2831207 := bstep (se 1 (by rfl) ⟨2123405, by rfl⟩ : syracuseStep 2831207 = 4246811) B4246811
theorem B1887471 : Blo 1887435 1887471 := bstep (se 1 (by rfl) ⟨1415603, by rfl⟩ : syracuseStep 1887471 = 2831207) B2831207
theorem B2831213 : Blo 1887435 2831213 := bbase (se 3 (by rfl) ⟨530852, by rfl⟩ : syracuseStep 2831213 = 1061705) (by norm_num)
theorem B1887475 : Blo 1887435 1887475 := bstep (se 1 (by rfl) ⟨1415606, by rfl⟩ : syracuseStep 1887475 = 2831213) B2831213
theorem B4246829 : Blo 1887435 4246829 := bbase (se 3 (by rfl) ⟨796280, by rfl⟩ : syracuseStep 4246829 = 1592561) (by norm_num)
theorem B2831219 : Blo 1887435 2831219 := bstep (se 1 (by rfl) ⟨2123414, by rfl⟩ : syracuseStep 2831219 = 4246829) B4246829
theorem B1887479 : Blo 1887435 1887479 := bstep (se 1 (by rfl) ⟨1415609, by rfl⟩ : syracuseStep 1887479 = 2831219) B2831219
theorem B3401309 : Blo 1887435 3401309 := bbase (se 3 (by rfl) ⟨637745, by rfl⟩ : syracuseStep 3401309 = 1275491) (by norm_num)
theorem B9070157 : Blo 1887435 9070157 := bstep (se 3 (by rfl) ⟨1700654, by rfl⟩ : syracuseStep 9070157 = 3401309) B3401309
theorem B6046771 : Blo 1887435 6046771 := bstep (se 1 (by rfl) ⟨4535078, by rfl⟩ : syracuseStep 6046771 = 9070157) B9070157
theorem B8062361 : Blo 1887435 8062361 := bstep (se 2 (by rfl) ⟨3023385, by rfl⟩ : syracuseStep 8062361 = 6046771) B6046771
theorem B5374907 : Blo 1887435 5374907 := bstep (se 1 (by rfl) ⟨4031180, by rfl⟩ : syracuseStep 5374907 = 8062361) B8062361
theorem B3583271 : Blo 1887435 3583271 := bstep (se 1 (by rfl) ⟨2687453, by rfl⟩ : syracuseStep 3583271 = 5374907) B5374907
theorem B2388847 : Blo 1887435 2388847 := bstep (se 1 (by rfl) ⟨1791635, by rfl⟩ : syracuseStep 2388847 = 3583271) B3583271
theorem B3185129 : Blo 1887435 3185129 := bstep (se 2 (by rfl) ⟨1194423, by rfl⟩ : syracuseStep 3185129 = 2388847) B2388847
theorem B2123419 : Blo 1887435 2123419 := bstep (se 1 (by rfl) ⟨1592564, by rfl⟩ : syracuseStep 2123419 = 3185129) B3185129
theorem B2831225 : Blo 1887435 2831225 := bstep (se 2 (by rfl) ⟨1061709, by rfl⟩ : syracuseStep 2831225 = 2123419) B2123419
theorem B1887483 : Blo 1887435 1887483 := bstep (se 1 (by rfl) ⟨1415612, by rfl⟩ : syracuseStep 1887483 = 2831225) B2831225
theorem B2724125 : Blo 1887435 2724125 := bbase (se 3 (by rfl) ⟨510773, by rfl⟩ : syracuseStep 2724125 = 1021547) (by norm_num)
theorem B7264333 : Blo 1887435 7264333 := bstep (se 3 (by rfl) ⟨1362062, by rfl⟩ : syracuseStep 7264333 = 2724125) B2724125
theorem B9685777 : Blo 1887435 9685777 := bstep (se 2 (by rfl) ⟨3632166, by rfl⟩ : syracuseStep 9685777 = 7264333) B7264333
theorem B12914369 : Blo 1887435 12914369 := bstep (se 2 (by rfl) ⟨4842888, by rfl⟩ : syracuseStep 12914369 = 9685777) B9685777
theorem B8609579 : Blo 1887435 8609579 := bstep (se 1 (by rfl) ⟨6457184, by rfl⟩ : syracuseStep 8609579 = 12914369) B12914369
theorem B5739719 : Blo 1887435 5739719 := bstep (se 1 (by rfl) ⟨4304789, by rfl⟩ : syracuseStep 5739719 = 8609579) B8609579
theorem B15305917 : Blo 1887435 15305917 := bstep (se 3 (by rfl) ⟨2869859, by rfl⟩ : syracuseStep 15305917 = 5739719) B5739719
theorem B20407889 : Blo 1887435 20407889 := bstep (se 2 (by rfl) ⟨7652958, by rfl⟩ : syracuseStep 20407889 = 15305917) B15305917
theorem B13605259 : Blo 1887435 13605259 := bstep (se 1 (by rfl) ⟨10203944, by rfl⟩ : syracuseStep 13605259 = 20407889) B20407889
theorem B18140345 : Blo 1887435 18140345 := bstep (se 2 (by rfl) ⟨6802629, by rfl⟩ : syracuseStep 18140345 = 13605259) B13605259
theorem B12093563 : Blo 1887435 12093563 := bstep (se 1 (by rfl) ⟨9070172, by rfl⟩ : syracuseStep 12093563 = 18140345) B18140345
theorem B32249501 : Blo 1887435 32249501 := bstep (se 3 (by rfl) ⟨6046781, by rfl⟩ : syracuseStep 32249501 = 12093563) B12093563
theorem B21499667 : Blo 1887435 21499667 := bstep (se 1 (by rfl) ⟨16124750, by rfl⟩ : syracuseStep 21499667 = 32249501) B32249501
theorem B14333111 : Blo 1887435 14333111 := bstep (se 1 (by rfl) ⟨10749833, by rfl⟩ : syracuseStep 14333111 = 21499667) B21499667
theorem B9555407 : Blo 1887435 9555407 := bstep (se 1 (by rfl) ⟨7166555, by rfl⟩ : syracuseStep 9555407 = 14333111) B14333111
theorem B6370271 : Blo 1887435 6370271 := bstep (se 1 (by rfl) ⟨4777703, by rfl⟩ : syracuseStep 6370271 = 9555407) B9555407
theorem B4246847 : Blo 1887435 4246847 := bstep (se 1 (by rfl) ⟨3185135, by rfl⟩ : syracuseStep 4246847 = 6370271) B6370271
theorem B2831231 : Blo 1887435 2831231 := bstep (se 1 (by rfl) ⟨2123423, by rfl⟩ : syracuseStep 2831231 = 4246847) B4246847
theorem B1887487 : Blo 1887435 1887487 := bstep (se 1 (by rfl) ⟨1415615, by rfl⟩ : syracuseStep 1887487 = 2831231) B2831231
theorem B2831237 : Blo 1887435 2831237 := bbase (se 4 (by rfl) ⟨265428, by rfl⟩ : syracuseStep 2831237 = 530857) (by norm_num)
theorem B1887491 : Blo 1887435 1887491 := bstep (se 1 (by rfl) ⟨1415618, by rfl⟩ : syracuseStep 1887491 = 2831237) B2831237
theorem B3185149 : Blo 1887435 3185149 := bbase (se 3 (by rfl) ⟨597215, by rfl⟩ : syracuseStep 3185149 = 1194431) (by norm_num)
theorem B4246865 : Blo 1887435 4246865 := bstep (se 2 (by rfl) ⟨1592574, by rfl⟩ : syracuseStep 4246865 = 3185149) B3185149
theorem B2831243 : Blo 1887435 2831243 := bstep (se 1 (by rfl) ⟨2123432, by rfl⟩ : syracuseStep 2831243 = 4246865) B4246865
theorem B1887495 : Blo 1887435 1887495 := bstep (se 1 (by rfl) ⟨1415621, by rfl⟩ : syracuseStep 1887495 = 2831243) B2831243
theorem B2123437 : Blo 1887435 2123437 := bbase (se 3 (by rfl) ⟨398144, by rfl⟩ : syracuseStep 2123437 = 796289) (by norm_num)
theorem B2831249 : Blo 1887435 2831249 := bstep (se 2 (by rfl) ⟨1061718, by rfl⟩ : syracuseStep 2831249 = 2123437) B2123437
theorem B1887499 : Blo 1887435 1887499 := bstep (se 1 (by rfl) ⟨1415624, by rfl⟩ : syracuseStep 1887499 = 2831249) B2831249
theorem B6370325 : Blo 1887435 6370325 := bbase (se 6 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 6370325 = 298609) (by norm_num)
theorem B4246883 : Blo 1887435 4246883 := bstep (se 1 (by rfl) ⟨3185162, by rfl⟩ : syracuseStep 4246883 = 6370325) B6370325
theorem B2831255 : Blo 1887435 2831255 := bstep (se 1 (by rfl) ⟨2123441, by rfl⟩ : syracuseStep 2831255 = 4246883) B4246883
theorem B1887503 : Blo 1887435 1887503 := bstep (se 1 (by rfl) ⟨1415627, by rfl⟩ : syracuseStep 1887503 = 2831255) B2831255
theorem B2831261 : Blo 1887435 2831261 := bbase (se 3 (by rfl) ⟨530861, by rfl⟩ : syracuseStep 2831261 = 1061723) (by norm_num)
theorem B1887507 : Blo 1887435 1887507 := bstep (se 1 (by rfl) ⟨1415630, by rfl⟩ : syracuseStep 1887507 = 2831261) B2831261
theorem B4246901 : Blo 1887435 4246901 := bbase (se 5 (by rfl) ⟨199073, by rfl⟩ : syracuseStep 4246901 = 398147) (by norm_num)
theorem B2831267 : Blo 1887435 2831267 := bstep (se 1 (by rfl) ⟨2123450, by rfl⟩ : syracuseStep 2831267 = 4246901) B4246901
theorem B1887511 : Blo 1887435 1887511 := bstep (se 1 (by rfl) ⟨1415633, by rfl⟩ : syracuseStep 1887511 = 2831267) B2831267
theorem B9070309 : Blo 1887435 9070309 := bbase (se 4 (by rfl) ⟨850341, by rfl⟩ : syracuseStep 9070309 = 1700683) (by norm_num)
theorem B12093745 : Blo 1887435 12093745 := bstep (se 2 (by rfl) ⟨4535154, by rfl⟩ : syracuseStep 12093745 = 9070309) B9070309
theorem B16124993 : Blo 1887435 16124993 := bstep (se 2 (by rfl) ⟨6046872, by rfl⟩ : syracuseStep 16124993 = 12093745) B12093745
theorem B10749995 : Blo 1887435 10749995 := bstep (se 1 (by rfl) ⟨8062496, by rfl⟩ : syracuseStep 10749995 = 16124993) B16124993
theorem B7166663 : Blo 1887435 7166663 := bstep (se 1 (by rfl) ⟨5374997, by rfl⟩ : syracuseStep 7166663 = 10749995) B10749995
theorem B4777775 : Blo 1887435 4777775 := bstep (se 1 (by rfl) ⟨3583331, by rfl⟩ : syracuseStep 4777775 = 7166663) B7166663
theorem B3185183 : Blo 1887435 3185183 := bstep (se 1 (by rfl) ⟨2388887, by rfl⟩ : syracuseStep 3185183 = 4777775) B4777775
theorem B2123455 : Blo 1887435 2123455 := bstep (se 1 (by rfl) ⟨1592591, by rfl⟩ : syracuseStep 2123455 = 3185183) B3185183
theorem B2831273 : Blo 1887435 2831273 := bstep (se 2 (by rfl) ⟨1061727, by rfl⟩ : syracuseStep 2831273 = 2123455) B2123455
theorem B1887515 : Blo 1887435 1887515 := bstep (se 1 (by rfl) ⟨1415636, by rfl⟩ : syracuseStep 1887515 = 2831273) B2831273
theorem B7166677 : Blo 1887435 7166677 := bbase (se 7 (by rfl) ⟨83984, by rfl⟩ : syracuseStep 7166677 = 167969) (by norm_num)
theorem B9555569 : Blo 1887435 9555569 := bstep (se 2 (by rfl) ⟨3583338, by rfl⟩ : syracuseStep 9555569 = 7166677) B7166677
theorem B6370379 : Blo 1887435 6370379 := bstep (se 1 (by rfl) ⟨4777784, by rfl⟩ : syracuseStep 6370379 = 9555569) B9555569
theorem B4246919 : Blo 1887435 4246919 := bstep (se 1 (by rfl) ⟨3185189, by rfl⟩ : syracuseStep 4246919 = 6370379) B6370379
theorem B2831279 : Blo 1887435 2831279 := bstep (se 1 (by rfl) ⟨2123459, by rfl⟩ : syracuseStep 2831279 = 4246919) B4246919
theorem B1887519 : Blo 1887435 1887519 := bstep (se 1 (by rfl) ⟨1415639, by rfl⟩ : syracuseStep 1887519 = 2831279) B2831279
theorem B2831285 : Blo 1887435 2831285 := bbase (se 5 (by rfl) ⟨132716, by rfl⟩ : syracuseStep 2831285 = 265433) (by norm_num)
theorem B1887523 : Blo 1887435 1887523 := bstep (se 1 (by rfl) ⟨1415642, by rfl⟩ : syracuseStep 1887523 = 2831285) B2831285
theorem B4777805 : Blo 1887435 4777805 := bbase (se 3 (by rfl) ⟨895838, by rfl⟩ : syracuseStep 4777805 = 1791677) (by norm_num)
theorem B3185203 : Blo 1887435 3185203 := bstep (se 1 (by rfl) ⟨2388902, by rfl⟩ : syracuseStep 3185203 = 4777805) B4777805
theorem B4246937 : Blo 1887435 4246937 := bstep (se 2 (by rfl) ⟨1592601, by rfl⟩ : syracuseStep 4246937 = 3185203) B3185203
theorem B2831291 : Blo 1887435 2831291 := bstep (se 1 (by rfl) ⟨2123468, by rfl⟩ : syracuseStep 2831291 = 4246937) B4246937
theorem B1887527 : Blo 1887435 1887527 := bstep (se 1 (by rfl) ⟨1415645, by rfl⟩ : syracuseStep 1887527 = 2831291) B2831291
theorem B2123473 : Blo 1887435 2123473 := bbase (se 2 (by rfl) ⟨796302, by rfl⟩ : syracuseStep 2123473 = 1592605) (by norm_num)
theorem B2831297 : Blo 1887435 2831297 := bstep (se 2 (by rfl) ⟨1061736, by rfl⟩ : syracuseStep 2831297 = 2123473) B2123473
theorem B1887531 : Blo 1887435 1887531 := bstep (se 1 (by rfl) ⟨1415648, by rfl⟩ : syracuseStep 1887531 = 2831297) B2831297
theorem B6802805 : Blo 1887435 6802805 := bbase (se 5 (by rfl) ⟨318881, by rfl⟩ : syracuseStep 6802805 = 637763) (by norm_num)
theorem B4535203 : Blo 1887435 4535203 := bstep (se 1 (by rfl) ⟨3401402, by rfl⟩ : syracuseStep 4535203 = 6802805) B6802805
theorem B6046937 : Blo 1887435 6046937 := bstep (se 2 (by rfl) ⟨2267601, by rfl⟩ : syracuseStep 6046937 = 4535203) B4535203
theorem B4031291 : Blo 1887435 4031291 := bstep (se 1 (by rfl) ⟨3023468, by rfl⟩ : syracuseStep 4031291 = 6046937) B6046937
theorem B2687527 : Blo 1887435 2687527 := bstep (se 1 (by rfl) ⟨2015645, by rfl⟩ : syracuseStep 2687527 = 4031291) B4031291
theorem B3583369 : Blo 1887435 3583369 := bstep (se 2 (by rfl) ⟨1343763, by rfl⟩ : syracuseStep 3583369 = 2687527) B2687527
theorem B4777825 : Blo 1887435 4777825 := bstep (se 2 (by rfl) ⟨1791684, by rfl⟩ : syracuseStep 4777825 = 3583369) B3583369
theorem B6370433 : Blo 1887435 6370433 := bstep (se 2 (by rfl) ⟨2388912, by rfl⟩ : syracuseStep 6370433 = 4777825) B4777825
theorem B4246955 : Blo 1887435 4246955 := bstep (se 1 (by rfl) ⟨3185216, by rfl⟩ : syracuseStep 4246955 = 6370433) B6370433
theorem B2831303 : Blo 1887435 2831303 := bstep (se 1 (by rfl) ⟨2123477, by rfl⟩ : syracuseStep 2831303 = 4246955) B4246955
theorem B1887535 : Blo 1887435 1887535 := bstep (se 1 (by rfl) ⟨1415651, by rfl⟩ : syracuseStep 1887535 = 2831303) B2831303
theorem B2831309 : Blo 1887435 2831309 := bbase (se 3 (by rfl) ⟨530870, by rfl⟩ : syracuseStep 2831309 = 1061741) (by norm_num)
theorem B1887539 : Blo 1887435 1887539 := bstep (se 1 (by rfl) ⟨1415654, by rfl⟩ : syracuseStep 1887539 = 2831309) B2831309
theorem B4246973 : Blo 1887435 4246973 := bbase (se 3 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 4246973 = 1592615) (by norm_num)
theorem B2831315 : Blo 1887435 2831315 := bstep (se 1 (by rfl) ⟨2123486, by rfl⟩ : syracuseStep 2831315 = 4246973) B4246973
theorem B1887543 : Blo 1887435 1887543 := bstep (se 1 (by rfl) ⟨1415657, by rfl⟩ : syracuseStep 1887543 = 2831315) B2831315
theorem B3185237 : Blo 1887435 3185237 := bbase (se 8 (by rfl) ⟨18663, by rfl⟩ : syracuseStep 3185237 = 37327) (by norm_num)
theorem B2123491 : Blo 1887435 2123491 := bstep (se 1 (by rfl) ⟨1592618, by rfl⟩ : syracuseStep 2123491 = 3185237) B3185237
theorem B2831321 : Blo 1887435 2831321 := bstep (se 2 (by rfl) ⟨1061745, by rfl⟩ : syracuseStep 2831321 = 2123491) B2123491
theorem B1887547 : Blo 1887435 1887547 := bstep (se 1 (by rfl) ⟨1415660, by rfl⟩ : syracuseStep 1887547 = 2831321) B2831321
theorem B1913305 : Blo 1887435 1913305 := bbase (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) (by norm_num)
theorem B2551073 : Blo 1887435 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B6802861 : Blo 1887435 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B9070481 : Blo 1887435 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B6046987 : Blo 1887435 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B8062649 : Blo 1887435 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B5375099 : Blo 1887435 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B14333597 : Blo 1887435 14333597 := bstep (se 3 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 14333597 = 5375099) B5375099
theorem B9555731 : Blo 1887435 9555731 := bstep (se 1 (by rfl) ⟨7166798, by rfl⟩ : syracuseStep 9555731 = 14333597) B14333597
theorem B6370487 : Blo 1887435 6370487 := bstep (se 1 (by rfl) ⟨4777865, by rfl⟩ : syracuseStep 6370487 = 9555731) B9555731
theorem B4246991 : Blo 1887435 4246991 := bstep (se 1 (by rfl) ⟨3185243, by rfl⟩ : syracuseStep 4246991 = 6370487) B6370487
theorem B2831327 : Blo 1887435 2831327 := bstep (se 1 (by rfl) ⟨2123495, by rfl⟩ : syracuseStep 2831327 = 4246991) B4246991
theorem B1887551 : Blo 1887435 1887551 := bstep (se 1 (by rfl) ⟨1415663, by rfl⟩ : syracuseStep 1887551 = 2831327) B2831327
theorem B2831333 : Blo 1887435 2831333 := bbase (se 4 (by rfl) ⟨265437, by rfl⟩ : syracuseStep 2831333 = 530875) (by norm_num)
theorem B1887555 : Blo 1887435 1887555 := bstep (se 1 (by rfl) ⟨1415666, by rfl⟩ : syracuseStep 1887555 = 2831333) B2831333
theorem B4535261 : Blo 1887435 4535261 := bbase (se 3 (by rfl) ⟨850361, by rfl⟩ : syracuseStep 4535261 = 1700723) (by norm_num)
theorem B3023507 : Blo 1887435 3023507 := bstep (se 1 (by rfl) ⟨2267630, by rfl⟩ : syracuseStep 3023507 = 4535261) B4535261
theorem B8062685 : Blo 1887435 8062685 := bstep (se 3 (by rfl) ⟨1511753, by rfl⟩ : syracuseStep 8062685 = 3023507) B3023507
theorem B5375123 : Blo 1887435 5375123 := bstep (se 1 (by rfl) ⟨4031342, by rfl⟩ : syracuseStep 5375123 = 8062685) B8062685
theorem B3583415 : Blo 1887435 3583415 := bstep (se 1 (by rfl) ⟨2687561, by rfl⟩ : syracuseStep 3583415 = 5375123) B5375123
theorem B2388943 : Blo 1887435 2388943 := bstep (se 1 (by rfl) ⟨1791707, by rfl⟩ : syracuseStep 2388943 = 3583415) B3583415
theorem B3185257 : Blo 1887435 3185257 := bstep (se 2 (by rfl) ⟨1194471, by rfl⟩ : syracuseStep 3185257 = 2388943) B2388943
theorem B4247009 : Blo 1887435 4247009 := bstep (se 2 (by rfl) ⟨1592628, by rfl⟩ : syracuseStep 4247009 = 3185257) B3185257
theorem B2831339 : Blo 1887435 2831339 := bstep (se 1 (by rfl) ⟨2123504, by rfl⟩ : syracuseStep 2831339 = 4247009) B4247009
theorem B1887559 : Blo 1887435 1887559 := bstep (se 1 (by rfl) ⟨1415669, by rfl⟩ : syracuseStep 1887559 = 2831339) B2831339
theorem B2123509 : Blo 1887435 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B2831345 : Blo 1887435 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B1887563 : Blo 1887435 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B2388953 : Blo 1887435 2388953 := bbase (se 2 (by rfl) ⟨895857, by rfl⟩ : syracuseStep 2388953 = 1791715) (by norm_num)
theorem B6370541 : Blo 1887435 6370541 := bstep (se 3 (by rfl) ⟨1194476, by rfl⟩ : syracuseStep 6370541 = 2388953) B2388953
theorem B4247027 : Blo 1887435 4247027 := bstep (se 1 (by rfl) ⟨3185270, by rfl⟩ : syracuseStep 4247027 = 6370541) B6370541
theorem B2831351 : Blo 1887435 2831351 := bstep (se 1 (by rfl) ⟨2123513, by rfl⟩ : syracuseStep 2831351 = 4247027) B4247027
theorem B1887567 : Blo 1887435 1887567 := bstep (se 1 (by rfl) ⟨1415675, by rfl⟩ : syracuseStep 1887567 = 2831351) B2831351
theorem B2831357 : Blo 1887435 2831357 := bbase (se 3 (by rfl) ⟨530879, by rfl⟩ : syracuseStep 2831357 = 1061759) (by norm_num)
theorem B1887571 : Blo 1887435 1887571 := bstep (se 1 (by rfl) ⟨1415678, by rfl⟩ : syracuseStep 1887571 = 2831357) B2831357
theorem B4247045 : Blo 1887435 4247045 := bbase (se 4 (by rfl) ⟨398160, by rfl⟩ : syracuseStep 4247045 = 796321) (by norm_num)
theorem B2831363 : Blo 1887435 2831363 := bstep (se 1 (by rfl) ⟨2123522, by rfl⟩ : syracuseStep 2831363 = 4247045) B4247045
theorem B1887575 : Blo 1887435 1887575 := bstep (se 1 (by rfl) ⟨1415681, by rfl⟩ : syracuseStep 1887575 = 2831363) B2831363
theorem B3583453 : Blo 1887435 3583453 := bbase (se 3 (by rfl) ⟨671897, by rfl⟩ : syracuseStep 3583453 = 1343795) (by norm_num)
theorem B4777937 : Blo 1887435 4777937 := bstep (se 2 (by rfl) ⟨1791726, by rfl⟩ : syracuseStep 4777937 = 3583453) B3583453
theorem B3185291 : Blo 1887435 3185291 := bstep (se 1 (by rfl) ⟨2388968, by rfl⟩ : syracuseStep 3185291 = 4777937) B4777937
theorem B2123527 : Blo 1887435 2123527 := bstep (se 1 (by rfl) ⟨1592645, by rfl⟩ : syracuseStep 2123527 = 3185291) B3185291
theorem B2831369 : Blo 1887435 2831369 := bstep (se 2 (by rfl) ⟨1061763, by rfl⟩ : syracuseStep 2831369 = 2123527) B2123527
theorem B1887579 : Blo 1887435 1887579 := bstep (se 1 (by rfl) ⟨1415684, by rfl⟩ : syracuseStep 1887579 = 2831369) B2831369
theorem B9555893 : Blo 1887435 9555893 := bbase (se 5 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 9555893 = 895865) (by norm_num)
theorem B6370595 : Blo 1887435 6370595 := bstep (se 1 (by rfl) ⟨4777946, by rfl⟩ : syracuseStep 6370595 = 9555893) B9555893
theorem B4247063 : Blo 1887435 4247063 := bstep (se 1 (by rfl) ⟨3185297, by rfl⟩ : syracuseStep 4247063 = 6370595) B6370595
theorem B2831375 : Blo 1887435 2831375 := bstep (se 1 (by rfl) ⟨2123531, by rfl⟩ : syracuseStep 2831375 = 4247063) B4247063
theorem B1887583 : Blo 1887435 1887583 := bstep (se 1 (by rfl) ⟨1415687, by rfl⟩ : syracuseStep 1887583 = 2831375) B2831375
theorem B2831381 : Blo 1887435 2831381 := bbase (se 6 (by rfl) ⟨66360, by rfl⟩ : syracuseStep 2831381 = 132721) (by norm_num)
theorem B1887587 : Blo 1887435 1887587 := bstep (se 1 (by rfl) ⟨1415690, by rfl⟩ : syracuseStep 1887587 = 2831381) B2831381
theorem B5740037 : Blo 1887435 5740037 := bbase (se 4 (by rfl) ⟨538128, by rfl⟩ : syracuseStep 5740037 = 1076257) (by norm_num)
theorem B3826691 : Blo 1887435 3826691 := bstep (se 1 (by rfl) ⟨2870018, by rfl⟩ : syracuseStep 3826691 = 5740037) B5740037
theorem B2551127 : Blo 1887435 2551127 := bstep (se 1 (by rfl) ⟨1913345, by rfl⟩ : syracuseStep 2551127 = 3826691) B3826691
theorem B27212021 : Blo 1887435 27212021 := bstep (se 5 (by rfl) ⟨1275563, by rfl⟩ : syracuseStep 27212021 = 2551127) B2551127
theorem B18141347 : Blo 1887435 18141347 := bstep (se 1 (by rfl) ⟨13606010, by rfl⟩ : syracuseStep 18141347 = 27212021) B27212021
theorem B12094231 : Blo 1887435 12094231 := bstep (se 1 (by rfl) ⟨9070673, by rfl⟩ : syracuseStep 12094231 = 18141347) B18141347
theorem B16125641 : Blo 1887435 16125641 := bstep (se 2 (by rfl) ⟨6047115, by rfl⟩ : syracuseStep 16125641 = 12094231) B12094231
theorem B10750427 : Blo 1887435 10750427 := bstep (se 1 (by rfl) ⟨8062820, by rfl⟩ : syracuseStep 10750427 = 16125641) B16125641
theorem B7166951 : Blo 1887435 7166951 := bstep (se 1 (by rfl) ⟨5375213, by rfl⟩ : syracuseStep 7166951 = 10750427) B10750427
theorem B4777967 : Blo 1887435 4777967 := bstep (se 1 (by rfl) ⟨3583475, by rfl⟩ : syracuseStep 4777967 = 7166951) B7166951
theorem B3185311 : Blo 1887435 3185311 := bstep (se 1 (by rfl) ⟨2388983, by rfl⟩ : syracuseStep 3185311 = 4777967) B4777967
theorem B4247081 : Blo 1887435 4247081 := bstep (se 2 (by rfl) ⟨1592655, by rfl⟩ : syracuseStep 4247081 = 3185311) B3185311
theorem B2831387 : Blo 1887435 2831387 := bstep (se 1 (by rfl) ⟨2123540, by rfl⟩ : syracuseStep 2831387 = 4247081) B4247081
theorem B1887591 : Blo 1887435 1887591 := bstep (se 1 (by rfl) ⟨1415693, by rfl⟩ : syracuseStep 1887591 = 2831387) B2831387
theorem B2123545 : Blo 1887435 2123545 := bbase (se 2 (by rfl) ⟨796329, by rfl⟩ : syracuseStep 2123545 = 1592659) (by norm_num)
theorem B2831393 : Blo 1887435 2831393 := bstep (se 2 (by rfl) ⟨1061772, by rfl⟩ : syracuseStep 2831393 = 2123545) B2123545
theorem B1887595 : Blo 1887435 1887595 := bstep (se 1 (by rfl) ⟨1415696, by rfl⟩ : syracuseStep 1887595 = 2831393) B2831393
theorem B7166981 : Blo 1887435 7166981 := bbase (se 4 (by rfl) ⟨671904, by rfl⟩ : syracuseStep 7166981 = 1343809) (by norm_num)
theorem B4777987 : Blo 1887435 4777987 := bstep (se 1 (by rfl) ⟨3583490, by rfl⟩ : syracuseStep 4777987 = 7166981) B7166981
theorem B6370649 : Blo 1887435 6370649 := bstep (se 2 (by rfl) ⟨2388993, by rfl⟩ : syracuseStep 6370649 = 4777987) B4777987
theorem B4247099 : Blo 1887435 4247099 := bstep (se 1 (by rfl) ⟨3185324, by rfl⟩ : syracuseStep 4247099 = 6370649) B6370649
theorem B2831399 : Blo 1887435 2831399 := bstep (se 1 (by rfl) ⟨2123549, by rfl⟩ : syracuseStep 2831399 = 4247099) B4247099
theorem B1887599 : Blo 1887435 1887599 := bstep (se 1 (by rfl) ⟨1415699, by rfl⟩ : syracuseStep 1887599 = 2831399) B2831399
theorem B2831405 : Blo 1887435 2831405 := bbase (se 3 (by rfl) ⟨530888, by rfl⟩ : syracuseStep 2831405 = 1061777) (by norm_num)
theorem B1887603 : Blo 1887435 1887603 := bstep (se 1 (by rfl) ⟨1415702, by rfl⟩ : syracuseStep 1887603 = 2831405) B2831405
theorem B4247117 : Blo 1887435 4247117 := bbase (se 3 (by rfl) ⟨796334, by rfl⟩ : syracuseStep 4247117 = 1592669) (by norm_num)
theorem B2831411 : Blo 1887435 2831411 := bstep (se 1 (by rfl) ⟨2123558, by rfl⟩ : syracuseStep 2831411 = 4247117) B4247117
theorem B1887607 : Blo 1887435 1887607 := bstep (se 1 (by rfl) ⟨1415705, by rfl⟩ : syracuseStep 1887607 = 2831411) B2831411
theorem B2389009 : Blo 1887435 2389009 := bbase (se 2 (by rfl) ⟨895878, by rfl⟩ : syracuseStep 2389009 = 1791757) (by norm_num)
theorem B3185345 : Blo 1887435 3185345 := bstep (se 2 (by rfl) ⟨1194504, by rfl⟩ : syracuseStep 3185345 = 2389009) B2389009
theorem B2123563 : Blo 1887435 2123563 := bstep (se 1 (by rfl) ⟨1592672, by rfl⟩ : syracuseStep 2123563 = 3185345) B3185345
theorem B2831417 : Blo 1887435 2831417 := bstep (se 2 (by rfl) ⟨1061781, by rfl⟩ : syracuseStep 2831417 = 2123563) B2123563
theorem B1887611 : Blo 1887435 1887611 := bstep (se 1 (by rfl) ⟨1415708, by rfl⟩ : syracuseStep 1887611 = 2831417) B2831417
theorem B4031461 : Blo 1887435 4031461 := bbase (se 4 (by rfl) ⟨377949, by rfl⟩ : syracuseStep 4031461 = 755899) (by norm_num)
theorem B21501125 : Blo 1887435 21501125 := bstep (se 4 (by rfl) ⟨2015730, by rfl⟩ : syracuseStep 21501125 = 4031461) B4031461
theorem B14334083 : Blo 1887435 14334083 := bstep (se 1 (by rfl) ⟨10750562, by rfl⟩ : syracuseStep 14334083 = 21501125) B21501125
theorem B9556055 : Blo 1887435 9556055 := bstep (se 1 (by rfl) ⟨7167041, by rfl⟩ : syracuseStep 9556055 = 14334083) B14334083
theorem B6370703 : Blo 1887435 6370703 := bstep (se 1 (by rfl) ⟨4778027, by rfl⟩ : syracuseStep 6370703 = 9556055) B9556055
theorem B4247135 : Blo 1887435 4247135 := bstep (se 1 (by rfl) ⟨3185351, by rfl⟩ : syracuseStep 4247135 = 6370703) B6370703
theorem B2831423 : Blo 1887435 2831423 := bstep (se 1 (by rfl) ⟨2123567, by rfl⟩ : syracuseStep 2831423 = 4247135) B4247135
theorem B1887615 : Blo 1887435 1887615 := bstep (se 1 (by rfl) ⟨1415711, by rfl⟩ : syracuseStep 1887615 = 2831423) B2831423
theorem B2831429 : Blo 1887435 2831429 := bbase (se 4 (by rfl) ⟨265446, by rfl⟩ : syracuseStep 2831429 = 530893) (by norm_num)
theorem B1887619 : Blo 1887435 1887619 := bstep (se 1 (by rfl) ⟨1415714, by rfl⟩ : syracuseStep 1887619 = 2831429) B2831429
theorem B3185365 : Blo 1887435 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B4247153 : Blo 1887435 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B2831435 : Blo 1887435 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B1887623 : Blo 1887435 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B2123581 : Blo 1887435 2123581 := bbase (se 3 (by rfl) ⟨398171, by rfl⟩ : syracuseStep 2123581 = 796343) (by norm_num)
theorem B2831441 : Blo 1887435 2831441 := bstep (se 2 (by rfl) ⟨1061790, by rfl⟩ : syracuseStep 2831441 = 2123581) B2123581
theorem B1887627 : Blo 1887435 1887627 := bstep (se 1 (by rfl) ⟨1415720, by rfl⟩ : syracuseStep 1887627 = 2831441) B2831441
theorem B6370757 : Blo 1887435 6370757 := bbase (se 4 (by rfl) ⟨597258, by rfl⟩ : syracuseStep 6370757 = 1194517) (by norm_num)
theorem B4247171 : Blo 1887435 4247171 := bstep (se 1 (by rfl) ⟨3185378, by rfl⟩ : syracuseStep 4247171 = 6370757) B6370757
theorem B2831447 : Blo 1887435 2831447 := bstep (se 1 (by rfl) ⟨2123585, by rfl⟩ : syracuseStep 2831447 = 4247171) B4247171
theorem B1887631 : Blo 1887435 1887631 := bstep (se 1 (by rfl) ⟨1415723, by rfl⟩ : syracuseStep 1887631 = 2831447) B2831447
theorem B2831453 : Blo 1887435 2831453 := bbase (se 3 (by rfl) ⟨530897, by rfl⟩ : syracuseStep 2831453 = 1061795) (by norm_num)
theorem B1887635 : Blo 1887435 1887635 := bstep (se 1 (by rfl) ⟨1415726, by rfl⟩ : syracuseStep 1887635 = 2831453) B2831453
theorem B4247189 : Blo 1887435 4247189 := bbase (se 6 (by rfl) ⟨99543, by rfl⟩ : syracuseStep 4247189 = 199087) (by norm_num)
theorem B2831459 : Blo 1887435 2831459 := bstep (se 1 (by rfl) ⟨2123594, by rfl⟩ : syracuseStep 2831459 = 4247189) B4247189
theorem B1887639 : Blo 1887435 1887639 := bstep (se 1 (by rfl) ⟨1415729, by rfl⟩ : syracuseStep 1887639 = 2831459) B2831459
theorem B2015761 : Blo 1887435 2015761 := bbase (se 2 (by rfl) ⟨755910, by rfl⟩ : syracuseStep 2015761 = 1511821) (by norm_num)
theorem B2687681 : Blo 1887435 2687681 := bstep (se 2 (by rfl) ⟨1007880, by rfl⟩ : syracuseStep 2687681 = 2015761) B2015761
theorem B7167149 : Blo 1887435 7167149 := bstep (se 3 (by rfl) ⟨1343840, by rfl⟩ : syracuseStep 7167149 = 2687681) B2687681
theorem B4778099 : Blo 1887435 4778099 := bstep (se 1 (by rfl) ⟨3583574, by rfl⟩ : syracuseStep 4778099 = 7167149) B7167149
theorem B3185399 : Blo 1887435 3185399 := bstep (se 1 (by rfl) ⟨2389049, by rfl⟩ : syracuseStep 3185399 = 4778099) B4778099
theorem B2123599 : Blo 1887435 2123599 := bstep (se 1 (by rfl) ⟨1592699, by rfl⟩ : syracuseStep 2123599 = 3185399) B3185399
theorem B2831465 : Blo 1887435 2831465 := bstep (se 2 (by rfl) ⟨1061799, by rfl⟩ : syracuseStep 2831465 = 2123599) B2123599
theorem B1887643 : Blo 1887435 1887643 := bstep (se 1 (by rfl) ⟨1415732, by rfl⟩ : syracuseStep 1887643 = 2831465) B2831465
theorem B6457733 : Blo 1887435 6457733 := bbase (se 4 (by rfl) ⟨605412, by rfl⟩ : syracuseStep 6457733 = 1210825) (by norm_num)
theorem B4305155 : Blo 1887435 4305155 := bstep (se 1 (by rfl) ⟨3228866, by rfl⟩ : syracuseStep 4305155 = 6457733) B6457733
theorem B11480413 : Blo 1887435 11480413 := bstep (se 3 (by rfl) ⟨2152577, by rfl⟩ : syracuseStep 11480413 = 4305155) B4305155
theorem B15307217 : Blo 1887435 15307217 := bstep (se 2 (by rfl) ⟨5740206, by rfl⟩ : syracuseStep 15307217 = 11480413) B11480413
theorem B10204811 : Blo 1887435 10204811 := bstep (se 1 (by rfl) ⟨7653608, by rfl⟩ : syracuseStep 10204811 = 15307217) B15307217
theorem B6803207 : Blo 1887435 6803207 := bstep (se 1 (by rfl) ⟨5102405, by rfl⟩ : syracuseStep 6803207 = 10204811) B10204811
theorem B4535471 : Blo 1887435 4535471 := bstep (se 1 (by rfl) ⟨3401603, by rfl⟩ : syracuseStep 4535471 = 6803207) B6803207
theorem B12094589 : Blo 1887435 12094589 := bstep (se 3 (by rfl) ⟨2267735, by rfl⟩ : syracuseStep 12094589 = 4535471) B4535471
theorem B8063059 : Blo 1887435 8063059 := bstep (se 1 (by rfl) ⟨6047294, by rfl⟩ : syracuseStep 8063059 = 12094589) B12094589
theorem B10750745 : Blo 1887435 10750745 := bstep (se 2 (by rfl) ⟨4031529, by rfl⟩ : syracuseStep 10750745 = 8063059) B8063059
theorem B7167163 : Blo 1887435 7167163 := bstep (se 1 (by rfl) ⟨5375372, by rfl⟩ : syracuseStep 7167163 = 10750745) B10750745
theorem B9556217 : Blo 1887435 9556217 := bstep (se 2 (by rfl) ⟨3583581, by rfl⟩ : syracuseStep 9556217 = 7167163) B7167163
theorem B6370811 : Blo 1887435 6370811 := bstep (se 1 (by rfl) ⟨4778108, by rfl⟩ : syracuseStep 6370811 = 9556217) B9556217
theorem B4247207 : Blo 1887435 4247207 := bstep (se 1 (by rfl) ⟨3185405, by rfl⟩ : syracuseStep 4247207 = 6370811) B6370811
theorem B2831471 : Blo 1887435 2831471 := bstep (se 1 (by rfl) ⟨2123603, by rfl⟩ : syracuseStep 2831471 = 4247207) B4247207
theorem B1887647 : Blo 1887435 1887647 := bstep (se 1 (by rfl) ⟨1415735, by rfl⟩ : syracuseStep 1887647 = 2831471) B2831471
theorem B2831477 : Blo 1887435 2831477 := bbase (se 5 (by rfl) ⟨132725, by rfl⟩ : syracuseStep 2831477 = 265451) (by norm_num)
theorem B1887651 : Blo 1887435 1887651 := bstep (se 1 (by rfl) ⟨1415738, by rfl⟩ : syracuseStep 1887651 = 2831477) B2831477
theorem B3583597 : Blo 1887435 3583597 := bbase (se 3 (by rfl) ⟨671924, by rfl⟩ : syracuseStep 3583597 = 1343849) (by norm_num)
theorem B4778129 : Blo 1887435 4778129 := bstep (se 2 (by rfl) ⟨1791798, by rfl⟩ : syracuseStep 4778129 = 3583597) B3583597
theorem B3185419 : Blo 1887435 3185419 := bstep (se 1 (by rfl) ⟨2389064, by rfl⟩ : syracuseStep 3185419 = 4778129) B4778129
theorem B4247225 : Blo 1887435 4247225 := bstep (se 2 (by rfl) ⟨1592709, by rfl⟩ : syracuseStep 4247225 = 3185419) B3185419
theorem B2831483 : Blo 1887435 2831483 := bstep (se 1 (by rfl) ⟨2123612, by rfl⟩ : syracuseStep 2831483 = 4247225) B4247225
theorem B1887655 : Blo 1887435 1887655 := bstep (se 1 (by rfl) ⟨1415741, by rfl⟩ : syracuseStep 1887655 = 2831483) B2831483
theorem B2123617 : Blo 1887435 2123617 := bbase (se 2 (by rfl) ⟨796356, by rfl⟩ : syracuseStep 2123617 = 1592713) (by norm_num)
theorem B2831489 : Blo 1887435 2831489 := bstep (se 2 (by rfl) ⟨1061808, by rfl⟩ : syracuseStep 2831489 = 2123617) B2123617
theorem B1887659 : Blo 1887435 1887659 := bstep (se 1 (by rfl) ⟨1415744, by rfl⟩ : syracuseStep 1887659 = 2831489) B2831489
theorem B4778149 : Blo 1887435 4778149 := bbase (se 4 (by rfl) ⟨447951, by rfl⟩ : syracuseStep 4778149 = 895903) (by norm_num)
theorem B6370865 : Blo 1887435 6370865 := bstep (se 2 (by rfl) ⟨2389074, by rfl⟩ : syracuseStep 6370865 = 4778149) B4778149
theorem B4247243 : Blo 1887435 4247243 := bstep (se 1 (by rfl) ⟨3185432, by rfl⟩ : syracuseStep 4247243 = 6370865) B6370865
theorem B2831495 : Blo 1887435 2831495 := bstep (se 1 (by rfl) ⟨2123621, by rfl⟩ : syracuseStep 2831495 = 4247243) B4247243
theorem B1887663 : Blo 1887435 1887663 := bstep (se 1 (by rfl) ⟨1415747, by rfl⟩ : syracuseStep 1887663 = 2831495) B2831495
theorem B2831501 : Blo 1887435 2831501 := bbase (se 3 (by rfl) ⟨530906, by rfl⟩ : syracuseStep 2831501 = 1061813) (by norm_num)
theorem B1887667 : Blo 1887435 1887667 := bstep (se 1 (by rfl) ⟨1415750, by rfl⟩ : syracuseStep 1887667 = 2831501) B2831501
theorem B4247261 : Blo 1887435 4247261 := bbase (se 3 (by rfl) ⟨796361, by rfl⟩ : syracuseStep 4247261 = 1592723) (by norm_num)
theorem B2831507 : Blo 1887435 2831507 := bstep (se 1 (by rfl) ⟨2123630, by rfl⟩ : syracuseStep 2831507 = 4247261) B4247261
theorem B1887671 : Blo 1887435 1887671 := bstep (se 1 (by rfl) ⟨1415753, by rfl⟩ : syracuseStep 1887671 = 2831507) B2831507
theorem B3185453 : Blo 1887435 3185453 := bbase (se 3 (by rfl) ⟨597272, by rfl⟩ : syracuseStep 3185453 = 1194545) (by norm_num)
theorem B2123635 : Blo 1887435 2123635 := bstep (se 1 (by rfl) ⟨1592726, by rfl⟩ : syracuseStep 2123635 = 3185453) B3185453
theorem B2831513 : Blo 1887435 2831513 := bstep (se 2 (by rfl) ⟨1061817, by rfl⟩ : syracuseStep 2831513 = 2123635) B2123635
theorem B1887675 : Blo 1887435 1887675 := bstep (se 1 (by rfl) ⟨1415756, by rfl⟩ : syracuseStep 1887675 = 2831513) B2831513
theorem B19373525 : Blo 1887435 19373525 := bbase (se 7 (by rfl) ⟨227033, by rfl⟩ : syracuseStep 19373525 = 454067) (by norm_num)
theorem B12915683 : Blo 1887435 12915683 := bstep (se 1 (by rfl) ⟨9686762, by rfl⟩ : syracuseStep 12915683 = 19373525) B19373525
theorem B8610455 : Blo 1887435 8610455 := bstep (se 1 (by rfl) ⟨6457841, by rfl⟩ : syracuseStep 8610455 = 12915683) B12915683
theorem B5740303 : Blo 1887435 5740303 := bstep (se 1 (by rfl) ⟨4305227, by rfl⟩ : syracuseStep 5740303 = 8610455) B8610455
theorem B7653737 : Blo 1887435 7653737 := bstep (se 2 (by rfl) ⟨2870151, by rfl⟩ : syracuseStep 7653737 = 5740303) B5740303
theorem B20409965 : Blo 1887435 20409965 := bstep (se 3 (by rfl) ⟨3826868, by rfl⟩ : syracuseStep 20409965 = 7653737) B7653737
theorem B13606643 : Blo 1887435 13606643 := bstep (se 1 (by rfl) ⟨10204982, by rfl⟩ : syracuseStep 13606643 = 20409965) B20409965
theorem B36284381 : Blo 1887435 36284381 := bstep (se 3 (by rfl) ⟨6803321, by rfl⟩ : syracuseStep 36284381 = 13606643) B13606643
theorem B24189587 : Blo 1887435 24189587 := bstep (se 1 (by rfl) ⟨18142190, by rfl⟩ : syracuseStep 24189587 = 36284381) B36284381
theorem B16126391 : Blo 1887435 16126391 := bstep (se 1 (by rfl) ⟨12094793, by rfl⟩ : syracuseStep 16126391 = 24189587) B24189587
theorem B10750927 : Blo 1887435 10750927 := bstep (se 1 (by rfl) ⟨8063195, by rfl⟩ : syracuseStep 10750927 = 16126391) B16126391
theorem B14334569 : Blo 1887435 14334569 := bstep (se 2 (by rfl) ⟨5375463, by rfl⟩ : syracuseStep 14334569 = 10750927) B10750927
theorem B9556379 : Blo 1887435 9556379 := bstep (se 1 (by rfl) ⟨7167284, by rfl⟩ : syracuseStep 9556379 = 14334569) B14334569
theorem B6370919 : Blo 1887435 6370919 := bstep (se 1 (by rfl) ⟨4778189, by rfl⟩ : syracuseStep 6370919 = 9556379) B9556379
theorem B4247279 : Blo 1887435 4247279 := bstep (se 1 (by rfl) ⟨3185459, by rfl⟩ : syracuseStep 4247279 = 6370919) B6370919
theorem B2831519 : Blo 1887435 2831519 := bstep (se 1 (by rfl) ⟨2123639, by rfl⟩ : syracuseStep 2831519 = 4247279) B4247279
theorem B1887679 : Blo 1887435 1887679 := bstep (se 1 (by rfl) ⟨1415759, by rfl⟩ : syracuseStep 1887679 = 2831519) B2831519
theorem B2831525 : Blo 1887435 2831525 := bbase (se 4 (by rfl) ⟨265455, by rfl⟩ : syracuseStep 2831525 = 530911) (by norm_num)
theorem B1887683 : Blo 1887435 1887683 := bstep (se 1 (by rfl) ⟨1415762, by rfl⟩ : syracuseStep 1887683 = 2831525) B2831525
theorem B2389105 : Blo 1887435 2389105 := bbase (se 2 (by rfl) ⟨895914, by rfl⟩ : syracuseStep 2389105 = 1791829) (by norm_num)
theorem B3185473 : Blo 1887435 3185473 := bstep (se 2 (by rfl) ⟨1194552, by rfl⟩ : syracuseStep 3185473 = 2389105) B2389105
theorem B4247297 : Blo 1887435 4247297 := bstep (se 2 (by rfl) ⟨1592736, by rfl⟩ : syracuseStep 4247297 = 3185473) B3185473
theorem B2831531 : Blo 1887435 2831531 := bstep (se 1 (by rfl) ⟨2123648, by rfl⟩ : syracuseStep 2831531 = 4247297) B4247297
theorem B1887687 : Blo 1887435 1887687 := bstep (se 1 (by rfl) ⟨1415765, by rfl⟩ : syracuseStep 1887687 = 2831531) B2831531
theorem B2123653 : Blo 1887435 2123653 := bbase (se 4 (by rfl) ⟨199092, by rfl⟩ : syracuseStep 2123653 = 398185) (by norm_num)
theorem B2831537 : Blo 1887435 2831537 := bstep (se 2 (by rfl) ⟨1061826, by rfl⟩ : syracuseStep 2831537 = 2123653) B2123653
theorem B1887691 : Blo 1887435 1887691 := bstep (se 1 (by rfl) ⟨1415768, by rfl⟩ : syracuseStep 1887691 = 2831537) B2831537
theorem B3023725 : Blo 1887435 3023725 := bbase (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) (by norm_num)
theorem B4031633 : Blo 1887435 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B2687755 : Blo 1887435 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B3583673 : Blo 1887435 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B2389115 : Blo 1887435 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B6370973 : Blo 1887435 6370973 := bstep (se 3 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 6370973 = 2389115) B2389115
theorem B4247315 : Blo 1887435 4247315 := bstep (se 1 (by rfl) ⟨3185486, by rfl⟩ : syracuseStep 4247315 = 6370973) B6370973
theorem B2831543 : Blo 1887435 2831543 := bstep (se 1 (by rfl) ⟨2123657, by rfl⟩ : syracuseStep 2831543 = 4247315) B4247315
theorem B1887695 : Blo 1887435 1887695 := bstep (se 1 (by rfl) ⟨1415771, by rfl⟩ : syracuseStep 1887695 = 2831543) B2831543
theorem B2831549 : Blo 1887435 2831549 := bbase (se 3 (by rfl) ⟨530915, by rfl⟩ : syracuseStep 2831549 = 1061831) (by norm_num)
theorem B1887699 : Blo 1887435 1887699 := bstep (se 1 (by rfl) ⟨1415774, by rfl⟩ : syracuseStep 1887699 = 2831549) B2831549
theorem B4247333 : Blo 1887435 4247333 := bbase (se 4 (by rfl) ⟨398187, by rfl⟩ : syracuseStep 4247333 = 796375) (by norm_num)
theorem B2831555 : Blo 1887435 2831555 := bstep (se 1 (by rfl) ⟨2123666, by rfl⟩ : syracuseStep 2831555 = 4247333) B4247333
theorem B1887703 : Blo 1887435 1887703 := bstep (se 1 (by rfl) ⟨1415777, by rfl⟩ : syracuseStep 1887703 = 2831555) B2831555
theorem B4778261 : Blo 1887435 4778261 := bbase (se 6 (by rfl) ⟨111990, by rfl⟩ : syracuseStep 4778261 = 223981) (by norm_num)
theorem B3185507 : Blo 1887435 3185507 := bstep (se 1 (by rfl) ⟨2389130, by rfl⟩ : syracuseStep 3185507 = 4778261) B4778261
theorem B2123671 : Blo 1887435 2123671 := bstep (se 1 (by rfl) ⟨1592753, by rfl⟩ : syracuseStep 2123671 = 3185507) B3185507
theorem B2831561 : Blo 1887435 2831561 := bstep (se 2 (by rfl) ⟨1061835, by rfl⟩ : syracuseStep 2831561 = 2123671) B2123671
theorem B1887707 : Blo 1887435 1887707 := bstep (se 1 (by rfl) ⟨1415780, by rfl⟩ : syracuseStep 1887707 = 2831561) B2831561
theorem B8063333 : Blo 1887435 8063333 := bbase (se 4 (by rfl) ⟨755937, by rfl⟩ : syracuseStep 8063333 = 1511875) (by norm_num)
theorem B5375555 : Blo 1887435 5375555 := bstep (se 1 (by rfl) ⟨4031666, by rfl⟩ : syracuseStep 5375555 = 8063333) B8063333
theorem B3583703 : Blo 1887435 3583703 := bstep (se 1 (by rfl) ⟨2687777, by rfl⟩ : syracuseStep 3583703 = 5375555) B5375555
theorem B9556541 : Blo 1887435 9556541 := bstep (se 3 (by rfl) ⟨1791851, by rfl⟩ : syracuseStep 9556541 = 3583703) B3583703
theorem B6371027 : Blo 1887435 6371027 := bstep (se 1 (by rfl) ⟨4778270, by rfl⟩ : syracuseStep 6371027 = 9556541) B9556541
theorem B4247351 : Blo 1887435 4247351 := bstep (se 1 (by rfl) ⟨3185513, by rfl⟩ : syracuseStep 4247351 = 6371027) B6371027
theorem B2831567 : Blo 1887435 2831567 := bstep (se 1 (by rfl) ⟨2123675, by rfl⟩ : syracuseStep 2831567 = 4247351) B4247351
theorem B1887711 : Blo 1887435 1887711 := bstep (se 1 (by rfl) ⟨1415783, by rfl⟩ : syracuseStep 1887711 = 2831567) B2831567
theorem B2831573 : Blo 1887435 2831573 := bbase (se 7 (by rfl) ⟨33182, by rfl⟩ : syracuseStep 2831573 = 66365) (by norm_num)
theorem B1887715 : Blo 1887435 1887715 := bstep (se 1 (by rfl) ⟨1415786, by rfl⟩ : syracuseStep 1887715 = 2831573) B2831573
theorem B2687789 : Blo 1887435 2687789 := bbase (se 3 (by rfl) ⟨503960, by rfl⟩ : syracuseStep 2687789 = 1007921) (by norm_num)
theorem B7167437 : Blo 1887435 7167437 := bstep (se 3 (by rfl) ⟨1343894, by rfl⟩ : syracuseStep 7167437 = 2687789) B2687789
theorem B4778291 : Blo 1887435 4778291 := bstep (se 1 (by rfl) ⟨3583718, by rfl⟩ : syracuseStep 4778291 = 7167437) B7167437
theorem B3185527 : Blo 1887435 3185527 := bstep (se 1 (by rfl) ⟨2389145, by rfl⟩ : syracuseStep 3185527 = 4778291) B4778291
theorem B4247369 : Blo 1887435 4247369 := bstep (se 2 (by rfl) ⟨1592763, by rfl⟩ : syracuseStep 4247369 = 3185527) B3185527
theorem B2831579 : Blo 1887435 2831579 := bstep (se 1 (by rfl) ⟨2123684, by rfl⟩ : syracuseStep 2831579 = 4247369) B4247369
theorem B1887719 : Blo 1887435 1887719 := bstep (se 1 (by rfl) ⟨1415789, by rfl⟩ : syracuseStep 1887719 = 2831579) B2831579
theorem B2123689 : Blo 1887435 2123689 := bbase (se 2 (by rfl) ⟨796383, by rfl⟩ : syracuseStep 2123689 = 1592767) (by norm_num)
theorem B2831585 : Blo 1887435 2831585 := bstep (se 2 (by rfl) ⟨1061844, by rfl⟩ : syracuseStep 2831585 = 2123689) B2123689
theorem B1887723 : Blo 1887435 1887723 := bstep (se 1 (by rfl) ⟨1415792, by rfl⟩ : syracuseStep 1887723 = 2831585) B2831585
theorem B3632629 : Blo 1887435 3632629 := bbase (se 5 (by rfl) ⟨170279, by rfl⟩ : syracuseStep 3632629 = 340559) (by norm_num)
theorem B4843505 : Blo 1887435 4843505 := bstep (se 2 (by rfl) ⟨1816314, by rfl⟩ : syracuseStep 4843505 = 3632629) B3632629
theorem B3229003 : Blo 1887435 3229003 := bstep (se 1 (by rfl) ⟨2421752, by rfl⟩ : syracuseStep 3229003 = 4843505) B4843505
theorem B17221349 : Blo 1887435 17221349 := bstep (se 4 (by rfl) ⟨1614501, by rfl⟩ : syracuseStep 17221349 = 3229003) B3229003
theorem B45923597 : Blo 1887435 45923597 := bstep (se 3 (by rfl) ⟨8610674, by rfl⟩ : syracuseStep 45923597 = 17221349) B17221349
theorem B30615731 : Blo 1887435 30615731 := bstep (se 1 (by rfl) ⟨22961798, by rfl⟩ : syracuseStep 30615731 = 45923597) B45923597
theorem B20410487 : Blo 1887435 20410487 := bstep (se 1 (by rfl) ⟨15307865, by rfl⟩ : syracuseStep 20410487 = 30615731) B30615731
theorem B13606991 : Blo 1887435 13606991 := bstep (se 1 (by rfl) ⟨10205243, by rfl⟩ : syracuseStep 13606991 = 20410487) B20410487
theorem B9071327 : Blo 1887435 9071327 := bstep (se 1 (by rfl) ⟨6803495, by rfl⟩ : syracuseStep 9071327 = 13606991) B13606991
theorem B6047551 : Blo 1887435 6047551 := bstep (se 1 (by rfl) ⟨4535663, by rfl⟩ : syracuseStep 6047551 = 9071327) B9071327
theorem B8063401 : Blo 1887435 8063401 := bstep (se 2 (by rfl) ⟨3023775, by rfl⟩ : syracuseStep 8063401 = 6047551) B6047551
theorem B10751201 : Blo 1887435 10751201 := bstep (se 2 (by rfl) ⟨4031700, by rfl⟩ : syracuseStep 10751201 = 8063401) B8063401
theorem B7167467 : Blo 1887435 7167467 := bstep (se 1 (by rfl) ⟨5375600, by rfl⟩ : syracuseStep 7167467 = 10751201) B10751201
theorem B4778311 : Blo 1887435 4778311 := bstep (se 1 (by rfl) ⟨3583733, by rfl⟩ : syracuseStep 4778311 = 7167467) B7167467
theorem B6371081 : Blo 1887435 6371081 := bstep (se 2 (by rfl) ⟨2389155, by rfl⟩ : syracuseStep 6371081 = 4778311) B4778311
theorem B4247387 : Blo 1887435 4247387 := bstep (se 1 (by rfl) ⟨3185540, by rfl⟩ : syracuseStep 4247387 = 6371081) B6371081
theorem B2831591 : Blo 1887435 2831591 := bstep (se 1 (by rfl) ⟨2123693, by rfl⟩ : syracuseStep 2831591 = 4247387) B4247387
theorem B1887727 : Blo 1887435 1887727 := bstep (se 1 (by rfl) ⟨1415795, by rfl⟩ : syracuseStep 1887727 = 2831591) B2831591
theorem B2831597 : Blo 1887435 2831597 := bbase (se 3 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 2831597 = 1061849) (by norm_num)
theorem B1887731 : Blo 1887435 1887731 := bstep (se 1 (by rfl) ⟨1415798, by rfl⟩ : syracuseStep 1887731 = 2831597) B2831597
theorem B4247405 : Blo 1887435 4247405 := bbase (se 3 (by rfl) ⟨796388, by rfl⟩ : syracuseStep 4247405 = 1592777) (by norm_num)
theorem B2831603 : Blo 1887435 2831603 := bstep (se 1 (by rfl) ⟨2123702, by rfl⟩ : syracuseStep 2831603 = 4247405) B4247405
theorem B1887735 : Blo 1887435 1887735 := bstep (se 1 (by rfl) ⟨1415801, by rfl⟩ : syracuseStep 1887735 = 2831603) B2831603
theorem B3583757 : Blo 1887435 3583757 := bbase (se 3 (by rfl) ⟨671954, by rfl⟩ : syracuseStep 3583757 = 1343909) (by norm_num)
theorem B2389171 : Blo 1887435 2389171 := bstep (se 1 (by rfl) ⟨1791878, by rfl⟩ : syracuseStep 2389171 = 3583757) B3583757
theorem B3185561 : Blo 1887435 3185561 := bstep (se 2 (by rfl) ⟨1194585, by rfl⟩ : syracuseStep 3185561 = 2389171) B2389171
theorem B2123707 : Blo 1887435 2123707 := bstep (se 1 (by rfl) ⟨1592780, by rfl⟩ : syracuseStep 2123707 = 3185561) B3185561
theorem B2831609 : Blo 1887435 2831609 := bstep (se 2 (by rfl) ⟨1061853, by rfl⟩ : syracuseStep 2831609 = 2123707) B2123707
theorem B1887739 : Blo 1887435 1887739 := bstep (se 1 (by rfl) ⟨1415804, by rfl⟩ : syracuseStep 1887739 = 2831609) B2831609
theorem B18142805 : Blo 1887435 18142805 := bbase (se 8 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 18142805 = 212611) (by norm_num)
theorem B48380813 : Blo 1887435 48380813 := bstep (se 3 (by rfl) ⟨9071402, by rfl⟩ : syracuseStep 48380813 = 18142805) B18142805
theorem B32253875 : Blo 1887435 32253875 := bstep (se 1 (by rfl) ⟨24190406, by rfl⟩ : syracuseStep 32253875 = 48380813) B48380813
theorem B21502583 : Blo 1887435 21502583 := bstep (se 1 (by rfl) ⟨16126937, by rfl⟩ : syracuseStep 21502583 = 32253875) B32253875
theorem B14335055 : Blo 1887435 14335055 := bstep (se 1 (by rfl) ⟨10751291, by rfl⟩ : syracuseStep 14335055 = 21502583) B21502583
theorem B9556703 : Blo 1887435 9556703 := bstep (se 1 (by rfl) ⟨7167527, by rfl⟩ : syracuseStep 9556703 = 14335055) B14335055
theorem B6371135 : Blo 1887435 6371135 := bstep (se 1 (by rfl) ⟨4778351, by rfl⟩ : syracuseStep 6371135 = 9556703) B9556703
theorem B4247423 : Blo 1887435 4247423 := bstep (se 1 (by rfl) ⟨3185567, by rfl⟩ : syracuseStep 4247423 = 6371135) B6371135
theorem B2831615 : Blo 1887435 2831615 := bstep (se 1 (by rfl) ⟨2123711, by rfl⟩ : syracuseStep 2831615 = 4247423) B4247423
theorem B1887743 : Blo 1887435 1887743 := bstep (se 1 (by rfl) ⟨1415807, by rfl⟩ : syracuseStep 1887743 = 2831615) B2831615
theorem B2831621 : Blo 1887435 2831621 := bbase (se 4 (by rfl) ⟨265464, by rfl⟩ : syracuseStep 2831621 = 530929) (by norm_num)
theorem B1887747 : Blo 1887435 1887747 := bstep (se 1 (by rfl) ⟨1415810, by rfl⟩ : syracuseStep 1887747 = 2831621) B2831621
theorem B3185581 : Blo 1887435 3185581 := bbase (se 3 (by rfl) ⟨597296, by rfl⟩ : syracuseStep 3185581 = 1194593) (by norm_num)
theorem B4247441 : Blo 1887435 4247441 := bstep (se 2 (by rfl) ⟨1592790, by rfl⟩ : syracuseStep 4247441 = 3185581) B3185581
theorem B2831627 : Blo 1887435 2831627 := bstep (se 1 (by rfl) ⟨2123720, by rfl⟩ : syracuseStep 2831627 = 4247441) B4247441
theorem B1887751 : Blo 1887435 1887751 := bstep (se 1 (by rfl) ⟨1415813, by rfl⟩ : syracuseStep 1887751 = 2831627) B2831627
theorem B2123725 : Blo 1887435 2123725 := bbase (se 3 (by rfl) ⟨398198, by rfl⟩ : syracuseStep 2123725 = 796397) (by norm_num)
theorem B2831633 : Blo 1887435 2831633 := bstep (se 2 (by rfl) ⟨1061862, by rfl⟩ : syracuseStep 2831633 = 2123725) B2123725
theorem B1887755 : Blo 1887435 1887755 := bstep (se 1 (by rfl) ⟨1415816, by rfl⟩ : syracuseStep 1887755 = 2831633) B2831633
theorem B6371189 : Blo 1887435 6371189 := bbase (se 5 (by rfl) ⟨298649, by rfl⟩ : syracuseStep 6371189 = 597299) (by norm_num)
theorem B4247459 : Blo 1887435 4247459 := bstep (se 1 (by rfl) ⟨3185594, by rfl⟩ : syracuseStep 4247459 = 6371189) B6371189
theorem B2831639 : Blo 1887435 2831639 := bstep (se 1 (by rfl) ⟨2123729, by rfl⟩ : syracuseStep 2831639 = 4247459) B4247459
theorem B1887759 : Blo 1887435 1887759 := bstep (se 1 (by rfl) ⟨1415819, by rfl⟩ : syracuseStep 1887759 = 2831639) B2831639
theorem B2831645 : Blo 1887435 2831645 := bbase (se 3 (by rfl) ⟨530933, by rfl⟩ : syracuseStep 2831645 = 1061867) (by norm_num)
theorem B1887763 : Blo 1887435 1887763 := bstep (se 1 (by rfl) ⟨1415822, by rfl⟩ : syracuseStep 1887763 = 2831645) B2831645
theorem B4247477 : Blo 1887435 4247477 := bbase (se 5 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 4247477 = 398201) (by norm_num)
theorem B2831651 : Blo 1887435 2831651 := bstep (se 1 (by rfl) ⟨2123738, by rfl⟩ : syracuseStep 2831651 = 4247477) B4247477
theorem B1887767 : Blo 1887435 1887767 := bstep (se 1 (by rfl) ⟨1415825, by rfl⟩ : syracuseStep 1887767 = 2831651) B2831651
theorem B2267885 : Blo 1887435 2267885 := bbase (se 3 (by rfl) ⟨425228, by rfl⟩ : syracuseStep 2267885 = 850457) (by norm_num)
theorem B6047693 : Blo 1887435 6047693 := bstep (se 3 (by rfl) ⟨1133942, by rfl⟩ : syracuseStep 6047693 = 2267885) B2267885
theorem B4031795 : Blo 1887435 4031795 := bstep (se 1 (by rfl) ⟨3023846, by rfl⟩ : syracuseStep 4031795 = 6047693) B6047693
theorem B10751453 : Blo 1887435 10751453 := bstep (se 3 (by rfl) ⟨2015897, by rfl⟩ : syracuseStep 10751453 = 4031795) B4031795
theorem B7167635 : Blo 1887435 7167635 := bstep (se 1 (by rfl) ⟨5375726, by rfl⟩ : syracuseStep 7167635 = 10751453) B10751453
theorem B4778423 : Blo 1887435 4778423 := bstep (se 1 (by rfl) ⟨3583817, by rfl⟩ : syracuseStep 4778423 = 7167635) B7167635
theorem B3185615 : Blo 1887435 3185615 := bstep (se 1 (by rfl) ⟨2389211, by rfl⟩ : syracuseStep 3185615 = 4778423) B4778423
theorem B2123743 : Blo 1887435 2123743 := bstep (se 1 (by rfl) ⟨1592807, by rfl⟩ : syracuseStep 2123743 = 3185615) B3185615
theorem B2831657 : Blo 1887435 2831657 := bstep (se 2 (by rfl) ⟨1061871, by rfl⟩ : syracuseStep 2831657 = 2123743) B2123743
theorem B1887771 : Blo 1887435 1887771 := bstep (se 1 (by rfl) ⟨1415828, by rfl⟩ : syracuseStep 1887771 = 2831657) B2831657
theorem B6803669 : Blo 1887435 6803669 := bbase (se 7 (by rfl) ⟨79730, by rfl⟩ : syracuseStep 6803669 = 159461) (by norm_num)
theorem B4535779 : Blo 1887435 4535779 := bstep (se 1 (by rfl) ⟨3401834, by rfl⟩ : syracuseStep 4535779 = 6803669) B6803669
theorem B6047705 : Blo 1887435 6047705 := bstep (se 2 (by rfl) ⟨2267889, by rfl⟩ : syracuseStep 6047705 = 4535779) B4535779
theorem B4031803 : Blo 1887435 4031803 := bstep (se 1 (by rfl) ⟨3023852, by rfl⟩ : syracuseStep 4031803 = 6047705) B6047705
theorem B5375737 : Blo 1887435 5375737 := bstep (se 2 (by rfl) ⟨2015901, by rfl⟩ : syracuseStep 5375737 = 4031803) B4031803
theorem B7167649 : Blo 1887435 7167649 := bstep (se 2 (by rfl) ⟨2687868, by rfl⟩ : syracuseStep 7167649 = 5375737) B5375737
theorem B9556865 : Blo 1887435 9556865 := bstep (se 2 (by rfl) ⟨3583824, by rfl⟩ : syracuseStep 9556865 = 7167649) B7167649
theorem B6371243 : Blo 1887435 6371243 := bstep (se 1 (by rfl) ⟨4778432, by rfl⟩ : syracuseStep 6371243 = 9556865) B9556865
theorem B4247495 : Blo 1887435 4247495 := bstep (se 1 (by rfl) ⟨3185621, by rfl⟩ : syracuseStep 4247495 = 6371243) B6371243
theorem B2831663 : Blo 1887435 2831663 := bstep (se 1 (by rfl) ⟨2123747, by rfl⟩ : syracuseStep 2831663 = 4247495) B4247495
theorem B1887775 : Blo 1887435 1887775 := bstep (se 1 (by rfl) ⟨1415831, by rfl⟩ : syracuseStep 1887775 = 2831663) B2831663
theorem B2831669 : Blo 1887435 2831669 := bbase (se 5 (by rfl) ⟨132734, by rfl⟩ : syracuseStep 2831669 = 265469) (by norm_num)
theorem B1887779 : Blo 1887435 1887779 := bstep (se 1 (by rfl) ⟨1415834, by rfl⟩ : syracuseStep 1887779 = 2831669) B2831669
theorem B4778453 : Blo 1887435 4778453 := bbase (se 7 (by rfl) ⟨55997, by rfl⟩ : syracuseStep 4778453 = 111995) (by norm_num)
theorem B3185635 : Blo 1887435 3185635 := bstep (se 1 (by rfl) ⟨2389226, by rfl⟩ : syracuseStep 3185635 = 4778453) B4778453
theorem B4247513 : Blo 1887435 4247513 := bstep (se 2 (by rfl) ⟨1592817, by rfl⟩ : syracuseStep 4247513 = 3185635) B3185635
theorem B2831675 : Blo 1887435 2831675 := bstep (se 1 (by rfl) ⟨2123756, by rfl⟩ : syracuseStep 2831675 = 4247513) B4247513
theorem B1887783 : Blo 1887435 1887783 := bstep (se 1 (by rfl) ⟨1415837, by rfl⟩ : syracuseStep 1887783 = 2831675) B2831675
theorem B2123761 : Blo 1887435 2123761 := bbase (se 2 (by rfl) ⟨796410, by rfl⟩ : syracuseStep 2123761 = 1592821) (by norm_num)
theorem B2831681 : Blo 1887435 2831681 := bstep (se 2 (by rfl) ⟨1061880, by rfl⟩ : syracuseStep 2831681 = 2123761) B2123761
theorem B1887787 : Blo 1887435 1887787 := bstep (se 1 (by rfl) ⟨1415840, by rfl⟩ : syracuseStep 1887787 = 2831681) B2831681
theorem B5740645 : Blo 1887435 5740645 := bbase (se 4 (by rfl) ⟨538185, by rfl⟩ : syracuseStep 5740645 = 1076371) (by norm_num)
theorem B7654193 : Blo 1887435 7654193 := bstep (se 2 (by rfl) ⟨2870322, by rfl⟩ : syracuseStep 7654193 = 5740645) B5740645
theorem B5102795 : Blo 1887435 5102795 := bstep (se 1 (by rfl) ⟨3827096, by rfl⟩ : syracuseStep 5102795 = 7654193) B7654193
theorem B13607453 : Blo 1887435 13607453 := bstep (se 3 (by rfl) ⟨2551397, by rfl⟩ : syracuseStep 13607453 = 5102795) B5102795
theorem B9071635 : Blo 1887435 9071635 := bstep (se 1 (by rfl) ⟨6803726, by rfl⟩ : syracuseStep 9071635 = 13607453) B13607453
theorem B12095513 : Blo 1887435 12095513 := bstep (se 2 (by rfl) ⟨4535817, by rfl⟩ : syracuseStep 12095513 = 9071635) B9071635
theorem B8063675 : Blo 1887435 8063675 := bstep (se 1 (by rfl) ⟨6047756, by rfl⟩ : syracuseStep 8063675 = 12095513) B12095513
theorem B5375783 : Blo 1887435 5375783 := bstep (se 1 (by rfl) ⟨4031837, by rfl⟩ : syracuseStep 5375783 = 8063675) B8063675
theorem B3583855 : Blo 1887435 3583855 := bstep (se 1 (by rfl) ⟨2687891, by rfl⟩ : syracuseStep 3583855 = 5375783) B5375783
theorem B4778473 : Blo 1887435 4778473 := bstep (se 2 (by rfl) ⟨1791927, by rfl⟩ : syracuseStep 4778473 = 3583855) B3583855
theorem B6371297 : Blo 1887435 6371297 := bstep (se 2 (by rfl) ⟨2389236, by rfl⟩ : syracuseStep 6371297 = 4778473) B4778473
theorem B4247531 : Blo 1887435 4247531 := bstep (se 1 (by rfl) ⟨3185648, by rfl⟩ : syracuseStep 4247531 = 6371297) B6371297
theorem B2831687 : Blo 1887435 2831687 := bstep (se 1 (by rfl) ⟨2123765, by rfl⟩ : syracuseStep 2831687 = 4247531) B4247531
theorem B1887791 : Blo 1887435 1887791 := bstep (se 1 (by rfl) ⟨1415843, by rfl⟩ : syracuseStep 1887791 = 2831687) B2831687
theorem B2831693 : Blo 1887435 2831693 := bbase (se 3 (by rfl) ⟨530942, by rfl⟩ : syracuseStep 2831693 = 1061885) (by norm_num)
theorem B1887795 : Blo 1887435 1887795 := bstep (se 1 (by rfl) ⟨1415846, by rfl⟩ : syracuseStep 1887795 = 2831693) B2831693
theorem B4247549 : Blo 1887435 4247549 := bbase (se 3 (by rfl) ⟨796415, by rfl⟩ : syracuseStep 4247549 = 1592831) (by norm_num)
theorem B2831699 : Blo 1887435 2831699 := bstep (se 1 (by rfl) ⟨2123774, by rfl⟩ : syracuseStep 2831699 = 4247549) B4247549
theorem B1887799 : Blo 1887435 1887799 := bstep (se 1 (by rfl) ⟨1415849, by rfl⟩ : syracuseStep 1887799 = 2831699) B2831699
theorem B3185669 : Blo 1887435 3185669 := bbase (se 4 (by rfl) ⟨298656, by rfl⟩ : syracuseStep 3185669 = 597313) (by norm_num)
theorem B2123779 : Blo 1887435 2123779 := bstep (se 1 (by rfl) ⟨1592834, by rfl⟩ : syracuseStep 2123779 = 3185669) B3185669
theorem B2831705 : Blo 1887435 2831705 := bstep (se 2 (by rfl) ⟨1061889, by rfl⟩ : syracuseStep 2831705 = 2123779) B2123779
theorem B1887803 : Blo 1887435 1887803 := bstep (se 1 (by rfl) ⟨1415852, by rfl⟩ : syracuseStep 1887803 = 2831705) B2831705
theorem B14335541 : Blo 1887435 14335541 := bbase (se 5 (by rfl) ⟨671978, by rfl⟩ : syracuseStep 14335541 = 1343957) (by norm_num)
theorem B9557027 : Blo 1887435 9557027 := bstep (se 1 (by rfl) ⟨7167770, by rfl⟩ : syracuseStep 9557027 = 14335541) B14335541
theorem B6371351 : Blo 1887435 6371351 := bstep (se 1 (by rfl) ⟨4778513, by rfl⟩ : syracuseStep 6371351 = 9557027) B9557027
theorem B4247567 : Blo 1887435 4247567 := bstep (se 1 (by rfl) ⟨3185675, by rfl⟩ : syracuseStep 4247567 = 6371351) B6371351
theorem B2831711 : Blo 1887435 2831711 := bstep (se 1 (by rfl) ⟨2123783, by rfl⟩ : syracuseStep 2831711 = 4247567) B4247567
theorem B1887807 : Blo 1887435 1887807 := bstep (se 1 (by rfl) ⟨1415855, by rfl⟩ : syracuseStep 1887807 = 2831711) B2831711
theorem B2831717 : Blo 1887435 2831717 := bbase (se 4 (by rfl) ⟨265473, by rfl⟩ : syracuseStep 2831717 = 530947) (by norm_num)
theorem B1887811 : Blo 1887435 1887811 := bstep (se 1 (by rfl) ⟨1415858, by rfl⟩ : syracuseStep 1887811 = 2831717) B2831717
theorem B3583901 : Blo 1887435 3583901 := bbase (se 3 (by rfl) ⟨671981, by rfl⟩ : syracuseStep 3583901 = 1343963) (by norm_num)
theorem B2389267 : Blo 1887435 2389267 := bstep (se 1 (by rfl) ⟨1791950, by rfl⟩ : syracuseStep 2389267 = 3583901) B3583901
theorem B3185689 : Blo 1887435 3185689 := bstep (se 2 (by rfl) ⟨1194633, by rfl⟩ : syracuseStep 3185689 = 2389267) B2389267
theorem B4247585 : Blo 1887435 4247585 := bstep (se 2 (by rfl) ⟨1592844, by rfl⟩ : syracuseStep 4247585 = 3185689) B3185689
theorem B2831723 : Blo 1887435 2831723 := bstep (se 1 (by rfl) ⟨2123792, by rfl⟩ : syracuseStep 2831723 = 4247585) B4247585
theorem B1887815 : Blo 1887435 1887815 := bstep (se 1 (by rfl) ⟨1415861, by rfl⟩ : syracuseStep 1887815 = 2831723) B2831723
theorem B2123797 : Blo 1887435 2123797 := bbase (se 6 (by rfl) ⟨49776, by rfl⟩ : syracuseStep 2123797 = 99553) (by norm_num)
theorem B2831729 : Blo 1887435 2831729 := bstep (se 2 (by rfl) ⟨1061898, by rfl⟩ : syracuseStep 2831729 = 2123797) B2123797
theorem B1887819 : Blo 1887435 1887819 := bstep (se 1 (by rfl) ⟨1415864, by rfl⟩ : syracuseStep 1887819 = 2831729) B2831729
theorem B2389277 : Blo 1887435 2389277 := bbase (se 3 (by rfl) ⟨447989, by rfl⟩ : syracuseStep 2389277 = 895979) (by norm_num)
theorem B6371405 : Blo 1887435 6371405 := bstep (se 3 (by rfl) ⟨1194638, by rfl⟩ : syracuseStep 6371405 = 2389277) B2389277
theorem B4247603 : Blo 1887435 4247603 := bstep (se 1 (by rfl) ⟨3185702, by rfl⟩ : syracuseStep 4247603 = 6371405) B6371405
theorem B2831735 : Blo 1887435 2831735 := bstep (se 1 (by rfl) ⟨2123801, by rfl⟩ : syracuseStep 2831735 = 4247603) B4247603
theorem B1887823 : Blo 1887435 1887823 := bstep (se 1 (by rfl) ⟨1415867, by rfl⟩ : syracuseStep 1887823 = 2831735) B2831735
theorem B2831741 : Blo 1887435 2831741 := bbase (se 3 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 2831741 = 1061903) (by norm_num)
theorem B1887827 : Blo 1887435 1887827 := bstep (se 1 (by rfl) ⟨1415870, by rfl⟩ : syracuseStep 1887827 = 2831741) B2831741
theorem B4247621 : Blo 1887435 4247621 := bbase (se 4 (by rfl) ⟨398214, by rfl⟩ : syracuseStep 4247621 = 796429) (by norm_num)
theorem B2831747 : Blo 1887435 2831747 := bstep (se 1 (by rfl) ⟨2123810, by rfl⟩ : syracuseStep 2831747 = 4247621) B4247621
theorem B1887831 : Blo 1887435 1887831 := bstep (se 1 (by rfl) ⟨1415873, by rfl⟩ : syracuseStep 1887831 = 2831747) B2831747
theorem B5375909 : Blo 1887435 5375909 := bbase (se 4 (by rfl) ⟨503991, by rfl⟩ : syracuseStep 5375909 = 1007983) (by norm_num)
theorem B3583939 : Blo 1887435 3583939 := bstep (se 1 (by rfl) ⟨2687954, by rfl⟩ : syracuseStep 3583939 = 5375909) B5375909
theorem B4778585 : Blo 1887435 4778585 := bstep (se 2 (by rfl) ⟨1791969, by rfl⟩ : syracuseStep 4778585 = 3583939) B3583939
theorem B3185723 : Blo 1887435 3185723 := bstep (se 1 (by rfl) ⟨2389292, by rfl⟩ : syracuseStep 3185723 = 4778585) B4778585
theorem B2123815 : Blo 1887435 2123815 := bstep (se 1 (by rfl) ⟨1592861, by rfl⟩ : syracuseStep 2123815 = 3185723) B3185723
theorem B2831753 : Blo 1887435 2831753 := bstep (se 2 (by rfl) ⟨1061907, by rfl⟩ : syracuseStep 2831753 = 2123815) B2123815
theorem B1887835 : Blo 1887435 1887835 := bstep (se 1 (by rfl) ⟨1415876, by rfl⟩ : syracuseStep 1887835 = 2831753) B2831753
theorem B9557189 : Blo 1887435 9557189 := bbase (se 4 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 9557189 = 1791973) (by norm_num)
theorem B6371459 : Blo 1887435 6371459 := bstep (se 1 (by rfl) ⟨4778594, by rfl⟩ : syracuseStep 6371459 = 9557189) B9557189
theorem B4247639 : Blo 1887435 4247639 := bstep (se 1 (by rfl) ⟨3185729, by rfl⟩ : syracuseStep 4247639 = 6371459) B6371459
theorem B2831759 : Blo 1887435 2831759 := bstep (se 1 (by rfl) ⟨2123819, by rfl⟩ : syracuseStep 2831759 = 4247639) B4247639
theorem B1887839 : Blo 1887435 1887839 := bstep (se 1 (by rfl) ⟨1415879, by rfl⟩ : syracuseStep 1887839 = 2831759) B2831759
theorem B2831765 : Blo 1887435 2831765 := bbase (se 6 (by rfl) ⟨66369, by rfl⟩ : syracuseStep 2831765 = 132739) (by norm_num)
theorem B1887843 : Blo 1887435 1887843 := bstep (se 1 (by rfl) ⟨1415882, by rfl⟩ : syracuseStep 1887843 = 2831765) B2831765
theorem B4031957 : Blo 1887435 4031957 := bbase (se 7 (by rfl) ⟨47249, by rfl⟩ : syracuseStep 4031957 = 94499) (by norm_num)
theorem B10751885 : Blo 1887435 10751885 := bstep (se 3 (by rfl) ⟨2015978, by rfl⟩ : syracuseStep 10751885 = 4031957) B4031957
theorem B7167923 : Blo 1887435 7167923 := bstep (se 1 (by rfl) ⟨5375942, by rfl⟩ : syracuseStep 7167923 = 10751885) B10751885
theorem B4778615 : Blo 1887435 4778615 := bstep (se 1 (by rfl) ⟨3583961, by rfl⟩ : syracuseStep 4778615 = 7167923) B7167923
theorem B3185743 : Blo 1887435 3185743 := bstep (se 1 (by rfl) ⟨2389307, by rfl⟩ : syracuseStep 3185743 = 4778615) B4778615
theorem B4247657 : Blo 1887435 4247657 := bstep (se 2 (by rfl) ⟨1592871, by rfl⟩ : syracuseStep 4247657 = 3185743) B3185743
theorem B2831771 : Blo 1887435 2831771 := bstep (se 1 (by rfl) ⟨2123828, by rfl⟩ : syracuseStep 2831771 = 4247657) B4247657
theorem B1887847 : Blo 1887435 1887847 := bstep (se 1 (by rfl) ⟨1415885, by rfl⟩ : syracuseStep 1887847 = 2831771) B2831771
theorem B2123833 : Blo 1887435 2123833 := bbase (se 2 (by rfl) ⟨796437, by rfl⟩ : syracuseStep 2123833 = 1592875) (by norm_num)
theorem B2831777 : Blo 1887435 2831777 := bstep (se 2 (by rfl) ⟨1061916, by rfl⟩ : syracuseStep 2831777 = 2123833) B2123833
theorem B1887851 : Blo 1887435 1887851 := bstep (se 1 (by rfl) ⟨1415888, by rfl⟩ : syracuseStep 1887851 = 2831777) B2831777
theorem B3023981 : Blo 1887435 3023981 := bbase (se 3 (by rfl) ⟨566996, by rfl⟩ : syracuseStep 3023981 = 1133993) (by norm_num)
theorem B2015987 : Blo 1887435 2015987 := bstep (se 1 (by rfl) ⟨1511990, by rfl⟩ : syracuseStep 2015987 = 3023981) B3023981
theorem B5375965 : Blo 1887435 5375965 := bstep (se 3 (by rfl) ⟨1007993, by rfl⟩ : syracuseStep 5375965 = 2015987) B2015987
theorem B7167953 : Blo 1887435 7167953 := bstep (se 2 (by rfl) ⟨2687982, by rfl⟩ : syracuseStep 7167953 = 5375965) B5375965
theorem B4778635 : Blo 1887435 4778635 := bstep (se 1 (by rfl) ⟨3583976, by rfl⟩ : syracuseStep 4778635 = 7167953) B7167953
theorem B6371513 : Blo 1887435 6371513 := bstep (se 2 (by rfl) ⟨2389317, by rfl⟩ : syracuseStep 6371513 = 4778635) B4778635
theorem B4247675 : Blo 1887435 4247675 := bstep (se 1 (by rfl) ⟨3185756, by rfl⟩ : syracuseStep 4247675 = 6371513) B6371513
theorem B2831783 : Blo 1887435 2831783 := bstep (se 1 (by rfl) ⟨2123837, by rfl⟩ : syracuseStep 2831783 = 4247675) B4247675
theorem B1887855 : Blo 1887435 1887855 := bstep (se 1 (by rfl) ⟨1415891, by rfl⟩ : syracuseStep 1887855 = 2831783) B2831783
theorem B2831789 : Blo 1887435 2831789 := bbase (se 3 (by rfl) ⟨530960, by rfl⟩ : syracuseStep 2831789 = 1061921) (by norm_num)
theorem B1887859 : Blo 1887435 1887859 := bstep (se 1 (by rfl) ⟨1415894, by rfl⟩ : syracuseStep 1887859 = 2831789) B2831789
theorem B4247693 : Blo 1887435 4247693 := bbase (se 3 (by rfl) ⟨796442, by rfl⟩ : syracuseStep 4247693 = 1592885) (by norm_num)
theorem B2831795 : Blo 1887435 2831795 := bstep (se 1 (by rfl) ⟨2123846, by rfl⟩ : syracuseStep 2831795 = 4247693) B4247693
theorem B1887863 : Blo 1887435 1887863 := bstep (se 1 (by rfl) ⟨1415897, by rfl⟩ : syracuseStep 1887863 = 2831795) B2831795
theorem B2389333 : Blo 1887435 2389333 := bbase (se 13 (by rfl) ⟨437, by rfl⟩ : syracuseStep 2389333 = 875) (by norm_num)
theorem B3185777 : Blo 1887435 3185777 := bstep (se 2 (by rfl) ⟨1194666, by rfl⟩ : syracuseStep 3185777 = 2389333) B2389333
theorem B2123851 : Blo 1887435 2123851 := bstep (se 1 (by rfl) ⟨1592888, by rfl⟩ : syracuseStep 2123851 = 3185777) B3185777
theorem B2831801 : Blo 1887435 2831801 := bstep (se 2 (by rfl) ⟨1061925, by rfl⟩ : syracuseStep 2831801 = 2123851) B2123851
theorem B1887867 : Blo 1887435 1887867 := bstep (se 1 (by rfl) ⟨1415900, by rfl⟩ : syracuseStep 1887867 = 2831801) B2831801
theorem B10486421 : Blo 1887435 10486421 := bbase (se 6 (by rfl) ⟨245775, by rfl⟩ : syracuseStep 10486421 = 491551) (by norm_num)
theorem B6990947 : Blo 1887435 6990947 := bstep (se 1 (by rfl) ⟨5243210, by rfl⟩ : syracuseStep 6990947 = 10486421) B10486421
theorem B4660631 : Blo 1887435 4660631 := bstep (se 1 (by rfl) ⟨3495473, by rfl⟩ : syracuseStep 4660631 = 6990947) B6990947
theorem B3107087 : Blo 1887435 3107087 := bstep (se 1 (by rfl) ⟨2330315, by rfl⟩ : syracuseStep 3107087 = 4660631) B4660631
theorem B2071391 : Blo 1887435 2071391 := bstep (se 1 (by rfl) ⟨1553543, by rfl⟩ : syracuseStep 2071391 = 3107087) B3107087
theorem B5523709 : Blo 1887435 5523709 := bstep (se 3 (by rfl) ⟨1035695, by rfl⟩ : syracuseStep 5523709 = 2071391) B2071391
theorem B7364945 : Blo 1887435 7364945 := bstep (se 2 (by rfl) ⟨2761854, by rfl⟩ : syracuseStep 7364945 = 5523709) B5523709
theorem B19639853 : Blo 1887435 19639853 := bstep (se 3 (by rfl) ⟨3682472, by rfl⟩ : syracuseStep 19639853 = 7364945) B7364945
theorem B13093235 : Blo 1887435 13093235 := bstep (se 1 (by rfl) ⟨9819926, by rfl⟩ : syracuseStep 13093235 = 19639853) B19639853
theorem B8728823 : Blo 1887435 8728823 := bstep (se 1 (by rfl) ⟨6546617, by rfl⟩ : syracuseStep 8728823 = 13093235) B13093235
theorem B5819215 : Blo 1887435 5819215 := bstep (se 1 (by rfl) ⟨4364411, by rfl⟩ : syracuseStep 5819215 = 8728823) B8728823
theorem B7758953 : Blo 1887435 7758953 := bstep (se 2 (by rfl) ⟨2909607, by rfl⟩ : syracuseStep 7758953 = 5819215) B5819215
theorem B5172635 : Blo 1887435 5172635 := bstep (se 1 (by rfl) ⟨3879476, by rfl⟩ : syracuseStep 5172635 = 7758953) B7758953
theorem B3448423 : Blo 1887435 3448423 := bstep (se 1 (by rfl) ⟨2586317, by rfl⟩ : syracuseStep 3448423 = 5172635) B5172635
theorem B4597897 : Blo 1887435 4597897 := bstep (se 2 (by rfl) ⟨1724211, by rfl⟩ : syracuseStep 4597897 = 3448423) B3448423
theorem B6130529 : Blo 1887435 6130529 := bstep (se 2 (by rfl) ⟨2298948, by rfl⟩ : syracuseStep 6130529 = 4597897) B4597897
theorem B4087019 : Blo 1887435 4087019 := bstep (se 1 (by rfl) ⟨3065264, by rfl⟩ : syracuseStep 4087019 = 6130529) B6130529
theorem B2724679 : Blo 1887435 2724679 := bstep (se 1 (by rfl) ⟨2043509, by rfl⟩ : syracuseStep 2724679 = 4087019) B4087019
theorem B3632905 : Blo 1887435 3632905 := bstep (se 2 (by rfl) ⟨1362339, by rfl⟩ : syracuseStep 3632905 = 2724679) B2724679
theorem B4843873 : Blo 1887435 4843873 := bstep (se 2 (by rfl) ⟨1816452, by rfl⟩ : syracuseStep 4843873 = 3632905) B3632905
theorem B25833989 : Blo 1887435 25833989 := bstep (se 4 (by rfl) ⟨2421936, by rfl⟩ : syracuseStep 25833989 = 4843873) B4843873
theorem B68890637 : Blo 1887435 68890637 := bstep (se 3 (by rfl) ⟨12916994, by rfl⟩ : syracuseStep 68890637 = 25833989) B25833989
theorem B45927091 : Blo 1887435 45927091 := bstep (se 1 (by rfl) ⟨34445318, by rfl⟩ : syracuseStep 45927091 = 68890637) B68890637
theorem B61236121 : Blo 1887435 61236121 := bstep (se 2 (by rfl) ⟨22963545, by rfl⟩ : syracuseStep 61236121 = 45927091) B45927091
theorem B81648161 : Blo 1887435 81648161 := bstep (se 2 (by rfl) ⟨30618060, by rfl⟩ : syracuseStep 81648161 = 61236121) B61236121
theorem B54432107 : Blo 1887435 54432107 := bstep (se 1 (by rfl) ⟨40824080, by rfl⟩ : syracuseStep 54432107 = 81648161) B81648161
theorem B36288071 : Blo 1887435 36288071 := bstep (se 1 (by rfl) ⟨27216053, by rfl⟩ : syracuseStep 36288071 = 54432107) B54432107
theorem B24192047 : Blo 1887435 24192047 := bstep (se 1 (by rfl) ⟨18144035, by rfl⟩ : syracuseStep 24192047 = 36288071) B36288071
theorem B16128031 : Blo 1887435 16128031 := bstep (se 1 (by rfl) ⟨12096023, by rfl⟩ : syracuseStep 16128031 = 24192047) B24192047
theorem B21504041 : Blo 1887435 21504041 := bstep (se 2 (by rfl) ⟨8064015, by rfl⟩ : syracuseStep 21504041 = 16128031) B16128031
theorem B14336027 : Blo 1887435 14336027 := bstep (se 1 (by rfl) ⟨10752020, by rfl⟩ : syracuseStep 14336027 = 21504041) B21504041
theorem B9557351 : Blo 1887435 9557351 := bstep (se 1 (by rfl) ⟨7168013, by rfl⟩ : syracuseStep 9557351 = 14336027) B14336027
theorem B6371567 : Blo 1887435 6371567 := bstep (se 1 (by rfl) ⟨4778675, by rfl⟩ : syracuseStep 6371567 = 9557351) B9557351
theorem B4247711 : Blo 1887435 4247711 := bstep (se 1 (by rfl) ⟨3185783, by rfl⟩ : syracuseStep 4247711 = 6371567) B6371567
theorem B2831807 : Blo 1887435 2831807 := bstep (se 1 (by rfl) ⟨2123855, by rfl⟩ : syracuseStep 2831807 = 4247711) B4247711
theorem B1887871 : Blo 1887435 1887871 := bstep (se 1 (by rfl) ⟨1415903, by rfl⟩ : syracuseStep 1887871 = 2831807) B2831807
theorem B2831813 : Blo 1887435 2831813 := bbase (se 4 (by rfl) ⟨265482, by rfl⟩ : syracuseStep 2831813 = 530965) (by norm_num)
theorem B1887875 : Blo 1887435 1887875 := bstep (se 1 (by rfl) ⟨1415906, by rfl⟩ : syracuseStep 1887875 = 2831813) B2831813
theorem B3185797 : Blo 1887435 3185797 := bbase (se 4 (by rfl) ⟨298668, by rfl⟩ : syracuseStep 3185797 = 597337) (by norm_num)
theorem B4247729 : Blo 1887435 4247729 := bstep (se 2 (by rfl) ⟨1592898, by rfl⟩ : syracuseStep 4247729 = 3185797) B3185797
theorem B2831819 : Blo 1887435 2831819 := bstep (se 1 (by rfl) ⟨2123864, by rfl⟩ : syracuseStep 2831819 = 4247729) B4247729
theorem B1887879 : Blo 1887435 1887879 := bstep (se 1 (by rfl) ⟨1415909, by rfl⟩ : syracuseStep 1887879 = 2831819) B2831819
theorem B2123869 : Blo 1887435 2123869 := bbase (se 3 (by rfl) ⟨398225, by rfl⟩ : syracuseStep 2123869 = 796451) (by norm_num)
theorem B2831825 : Blo 1887435 2831825 := bstep (se 2 (by rfl) ⟨1061934, by rfl⟩ : syracuseStep 2831825 = 2123869) B2123869
theorem B1887883 : Blo 1887435 1887883 := bstep (se 1 (by rfl) ⟨1415912, by rfl⟩ : syracuseStep 1887883 = 2831825) B2831825
theorem B6371621 : Blo 1887435 6371621 := bbase (se 4 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 6371621 = 1194679) (by norm_num)
theorem B4247747 : Blo 1887435 4247747 := bstep (se 1 (by rfl) ⟨3185810, by rfl⟩ : syracuseStep 4247747 = 6371621) B6371621
theorem B2831831 : Blo 1887435 2831831 := bstep (se 1 (by rfl) ⟨2123873, by rfl⟩ : syracuseStep 2831831 = 4247747) B4247747
theorem B1887887 : Blo 1887435 1887887 := bstep (se 1 (by rfl) ⟨1415915, by rfl⟩ : syracuseStep 1887887 = 2831831) B2831831
theorem B2831837 : Blo 1887435 2831837 := bbase (se 3 (by rfl) ⟨530969, by rfl⟩ : syracuseStep 2831837 = 1061939) (by norm_num)
theorem B1887891 : Blo 1887435 1887891 := bstep (se 1 (by rfl) ⟨1415918, by rfl⟩ : syracuseStep 1887891 = 2831837) B2831837
theorem B4247765 : Blo 1887435 4247765 := bbase (se 7 (by rfl) ⟨49778, by rfl⟩ : syracuseStep 4247765 = 99557) (by norm_num)
theorem B2831843 : Blo 1887435 2831843 := bstep (se 1 (by rfl) ⟨2123882, by rfl⟩ : syracuseStep 2831843 = 4247765) B4247765
theorem B1887895 : Blo 1887435 1887895 := bstep (se 1 (by rfl) ⟨1415921, by rfl⟩ : syracuseStep 1887895 = 2831843) B2831843
theorem B11797397 : Blo 1887435 11797397 := bbase (se 6 (by rfl) ⟨276501, by rfl⟩ : syracuseStep 11797397 = 553003) (by norm_num)
theorem B7864931 : Blo 1887435 7864931 := bstep (se 1 (by rfl) ⟨5898698, by rfl⟩ : syracuseStep 7864931 = 11797397) B11797397
theorem B5243287 : Blo 1887435 5243287 := bstep (se 1 (by rfl) ⟨3932465, by rfl⟩ : syracuseStep 5243287 = 7864931) B7864931
theorem B6991049 : Blo 1887435 6991049 := bstep (se 2 (by rfl) ⟨2621643, by rfl⟩ : syracuseStep 6991049 = 5243287) B5243287
theorem B4660699 : Blo 1887435 4660699 := bstep (se 1 (by rfl) ⟨3495524, by rfl⟩ : syracuseStep 4660699 = 6991049) B6991049
theorem B6214265 : Blo 1887435 6214265 := bstep (se 2 (by rfl) ⟨2330349, by rfl⟩ : syracuseStep 6214265 = 4660699) B4660699
theorem B4142843 : Blo 1887435 4142843 := bstep (se 1 (by rfl) ⟨3107132, by rfl⟩ : syracuseStep 4142843 = 6214265) B6214265
theorem B2761895 : Blo 1887435 2761895 := bstep (se 1 (by rfl) ⟨2071421, by rfl⟩ : syracuseStep 2761895 = 4142843) B4142843
theorem B7365053 : Blo 1887435 7365053 := bstep (se 3 (by rfl) ⟨1380947, by rfl⟩ : syracuseStep 7365053 = 2761895) B2761895
theorem B19640141 : Blo 1887435 19640141 := bstep (se 3 (by rfl) ⟨3682526, by rfl⟩ : syracuseStep 19640141 = 7365053) B7365053
theorem B13093427 : Blo 1887435 13093427 := bstep (se 1 (by rfl) ⟨9820070, by rfl⟩ : syracuseStep 13093427 = 19640141) B19640141
theorem B34915805 : Blo 1887435 34915805 := bstep (se 3 (by rfl) ⟨6546713, by rfl⟩ : syracuseStep 34915805 = 13093427) B13093427
theorem B23277203 : Blo 1887435 23277203 := bstep (se 1 (by rfl) ⟨17457902, by rfl⟩ : syracuseStep 23277203 = 34915805) B34915805
theorem B15518135 : Blo 1887435 15518135 := bstep (se 1 (by rfl) ⟨11638601, by rfl⟩ : syracuseStep 15518135 = 23277203) B23277203
theorem B10345423 : Blo 1887435 10345423 := bstep (se 1 (by rfl) ⟨7759067, by rfl⟩ : syracuseStep 10345423 = 15518135) B15518135
theorem B13793897 : Blo 1887435 13793897 := bstep (se 2 (by rfl) ⟨5172711, by rfl⟩ : syracuseStep 13793897 = 10345423) B10345423
theorem B9195931 : Blo 1887435 9195931 := bstep (se 1 (by rfl) ⟨6896948, by rfl⟩ : syracuseStep 9195931 = 13793897) B13793897
theorem B12261241 : Blo 1887435 12261241 := bstep (se 2 (by rfl) ⟨4597965, by rfl⟩ : syracuseStep 12261241 = 9195931) B9195931
theorem B16348321 : Blo 1887435 16348321 := bstep (se 2 (by rfl) ⟨6130620, by rfl⟩ : syracuseStep 16348321 = 12261241) B12261241
theorem B21797761 : Blo 1887435 21797761 := bstep (se 2 (by rfl) ⟨8174160, by rfl⟩ : syracuseStep 21797761 = 16348321) B16348321
theorem B29063681 : Blo 1887435 29063681 := bstep (se 2 (by rfl) ⟨10898880, by rfl⟩ : syracuseStep 29063681 = 21797761) B21797761
theorem B19375787 : Blo 1887435 19375787 := bstep (se 1 (by rfl) ⟨14531840, by rfl⟩ : syracuseStep 19375787 = 29063681) B29063681
theorem B51668765 : Blo 1887435 51668765 := bstep (se 3 (by rfl) ⟨9687893, by rfl⟩ : syracuseStep 51668765 = 19375787) B19375787
theorem B34445843 : Blo 1887435 34445843 := bstep (se 1 (by rfl) ⟨25834382, by rfl⟩ : syracuseStep 34445843 = 51668765) B51668765
theorem B22963895 : Blo 1887435 22963895 := bstep (se 1 (by rfl) ⟨17222921, by rfl⟩ : syracuseStep 22963895 = 34445843) B34445843
theorem B15309263 : Blo 1887435 15309263 := bstep (se 1 (by rfl) ⟨11481947, by rfl⟩ : syracuseStep 15309263 = 22963895) B22963895
theorem B10206175 : Blo 1887435 10206175 := bstep (se 1 (by rfl) ⟨7654631, by rfl⟩ : syracuseStep 10206175 = 15309263) B15309263
theorem B13608233 : Blo 1887435 13608233 := bstep (se 2 (by rfl) ⟨5103087, by rfl⟩ : syracuseStep 13608233 = 10206175) B10206175
theorem B9072155 : Blo 1887435 9072155 := bstep (se 1 (by rfl) ⟨6804116, by rfl⟩ : syracuseStep 9072155 = 13608233) B13608233
theorem B6048103 : Blo 1887435 6048103 := bstep (se 1 (by rfl) ⟨4536077, by rfl⟩ : syracuseStep 6048103 = 9072155) B9072155
theorem B8064137 : Blo 1887435 8064137 := bstep (se 2 (by rfl) ⟨3024051, by rfl⟩ : syracuseStep 8064137 = 6048103) B6048103
theorem B5376091 : Blo 1887435 5376091 := bstep (se 1 (by rfl) ⟨4032068, by rfl⟩ : syracuseStep 5376091 = 8064137) B8064137
theorem B7168121 : Blo 1887435 7168121 := bstep (se 2 (by rfl) ⟨2688045, by rfl⟩ : syracuseStep 7168121 = 5376091) B5376091
theorem B4778747 : Blo 1887435 4778747 := bstep (se 1 (by rfl) ⟨3584060, by rfl⟩ : syracuseStep 4778747 = 7168121) B7168121
theorem B3185831 : Blo 1887435 3185831 := bstep (se 1 (by rfl) ⟨2389373, by rfl⟩ : syracuseStep 3185831 = 4778747) B4778747
theorem B2123887 : Blo 1887435 2123887 := bstep (se 1 (by rfl) ⟨1592915, by rfl⟩ : syracuseStep 2123887 = 3185831) B3185831
theorem B2831849 : Blo 1887435 2831849 := bstep (se 2 (by rfl) ⟨1061943, by rfl⟩ : syracuseStep 2831849 = 2123887) B2123887
theorem B1887899 : Blo 1887435 1887899 := bstep (se 1 (by rfl) ⟨1415924, by rfl⟩ : syracuseStep 1887899 = 2831849) B2831849
theorem B2551549 : Blo 1887435 2551549 := bbase (se 3 (by rfl) ⟨478415, by rfl⟩ : syracuseStep 2551549 = 956831) (by norm_num)
theorem B3402065 : Blo 1887435 3402065 := bstep (se 2 (by rfl) ⟨1275774, by rfl⟩ : syracuseStep 3402065 = 2551549) B2551549
theorem B2268043 : Blo 1887435 2268043 := bstep (se 1 (by rfl) ⟨1701032, by rfl⟩ : syracuseStep 2268043 = 3402065) B3402065
theorem B12096229 : Blo 1887435 12096229 := bstep (se 4 (by rfl) ⟨1134021, by rfl⟩ : syracuseStep 12096229 = 2268043) B2268043
theorem B16128305 : Blo 1887435 16128305 := bstep (se 2 (by rfl) ⟨6048114, by rfl⟩ : syracuseStep 16128305 = 12096229) B12096229
theorem B10752203 : Blo 1887435 10752203 := bstep (se 1 (by rfl) ⟨8064152, by rfl⟩ : syracuseStep 10752203 = 16128305) B16128305
theorem B7168135 : Blo 1887435 7168135 := bstep (se 1 (by rfl) ⟨5376101, by rfl⟩ : syracuseStep 7168135 = 10752203) B10752203
theorem B9557513 : Blo 1887435 9557513 := bstep (se 2 (by rfl) ⟨3584067, by rfl⟩ : syracuseStep 9557513 = 7168135) B7168135
theorem B6371675 : Blo 1887435 6371675 := bstep (se 1 (by rfl) ⟨4778756, by rfl⟩ : syracuseStep 6371675 = 9557513) B9557513
theorem B4247783 : Blo 1887435 4247783 := bstep (se 1 (by rfl) ⟨3185837, by rfl⟩ : syracuseStep 4247783 = 6371675) B6371675
theorem B2831855 : Blo 1887435 2831855 := bstep (se 1 (by rfl) ⟨2123891, by rfl⟩ : syracuseStep 2831855 = 4247783) B4247783
theorem B1887903 : Blo 1887435 1887903 := bstep (se 1 (by rfl) ⟨1415927, by rfl⟩ : syracuseStep 1887903 = 2831855) B2831855
theorem B2831861 : Blo 1887435 2831861 := bbase (se 5 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 2831861 = 265487) (by norm_num)
theorem B1887907 : Blo 1887435 1887907 := bstep (se 1 (by rfl) ⟨1415930, by rfl⟩ : syracuseStep 1887907 = 2831861) B2831861
theorem B3827341 : Blo 1887435 3827341 := bbase (se 3 (by rfl) ⟨717626, by rfl⟩ : syracuseStep 3827341 = 1435253) (by norm_num)
theorem B5103121 : Blo 1887435 5103121 := bstep (se 2 (by rfl) ⟨1913670, by rfl⟩ : syracuseStep 5103121 = 3827341) B3827341
theorem B6804161 : Blo 1887435 6804161 := bstep (se 2 (by rfl) ⟨2551560, by rfl⟩ : syracuseStep 6804161 = 5103121) B5103121
theorem B4536107 : Blo 1887435 4536107 := bstep (se 1 (by rfl) ⟨3402080, by rfl⟩ : syracuseStep 4536107 = 6804161) B6804161
theorem B3024071 : Blo 1887435 3024071 := bstep (se 1 (by rfl) ⟨2268053, by rfl⟩ : syracuseStep 3024071 = 4536107) B4536107
theorem B2016047 : Blo 1887435 2016047 := bstep (se 1 (by rfl) ⟨1512035, by rfl⟩ : syracuseStep 2016047 = 3024071) B3024071
theorem B5376125 : Blo 1887435 5376125 := bstep (se 3 (by rfl) ⟨1008023, by rfl⟩ : syracuseStep 5376125 = 2016047) B2016047
theorem B3584083 : Blo 1887435 3584083 := bstep (se 1 (by rfl) ⟨2688062, by rfl⟩ : syracuseStep 3584083 = 5376125) B5376125
theorem B4778777 : Blo 1887435 4778777 := bstep (se 2 (by rfl) ⟨1792041, by rfl⟩ : syracuseStep 4778777 = 3584083) B3584083
theorem B3185851 : Blo 1887435 3185851 := bstep (se 1 (by rfl) ⟨2389388, by rfl⟩ : syracuseStep 3185851 = 4778777) B4778777
theorem B4247801 : Blo 1887435 4247801 := bstep (se 2 (by rfl) ⟨1592925, by rfl⟩ : syracuseStep 4247801 = 3185851) B3185851
theorem B2831867 : Blo 1887435 2831867 := bstep (se 1 (by rfl) ⟨2123900, by rfl⟩ : syracuseStep 2831867 = 4247801) B4247801
theorem B1887911 : Blo 1887435 1887911 := bstep (se 1 (by rfl) ⟨1415933, by rfl⟩ : syracuseStep 1887911 = 2831867) B2831867
theorem B2123905 : Blo 1887435 2123905 := bbase (se 2 (by rfl) ⟨796464, by rfl⟩ : syracuseStep 2123905 = 1592929) (by norm_num)
theorem B2831873 : Blo 1887435 2831873 := bstep (se 2 (by rfl) ⟨1061952, by rfl⟩ : syracuseStep 2831873 = 2123905) B2123905
theorem B1887915 : Blo 1887435 1887915 := bstep (se 1 (by rfl) ⟨1415936, by rfl⟩ : syracuseStep 1887915 = 2831873) B2831873
theorem B4778797 : Blo 1887435 4778797 := bbase (se 3 (by rfl) ⟨896024, by rfl⟩ : syracuseStep 4778797 = 1792049) (by norm_num)
theorem B6371729 : Blo 1887435 6371729 := bstep (se 2 (by rfl) ⟨2389398, by rfl⟩ : syracuseStep 6371729 = 4778797) B4778797
theorem B4247819 : Blo 1887435 4247819 := bstep (se 1 (by rfl) ⟨3185864, by rfl⟩ : syracuseStep 4247819 = 6371729) B6371729
theorem B2831879 : Blo 1887435 2831879 := bstep (se 1 (by rfl) ⟨2123909, by rfl⟩ : syracuseStep 2831879 = 4247819) B4247819
theorem B1887919 : Blo 1887435 1887919 := bstep (se 1 (by rfl) ⟨1415939, by rfl⟩ : syracuseStep 1887919 = 2831879) B2831879
theorem B2831885 : Blo 1887435 2831885 := bbase (se 3 (by rfl) ⟨530978, by rfl⟩ : syracuseStep 2831885 = 1061957) (by norm_num)
theorem B1887923 : Blo 1887435 1887923 := bstep (se 1 (by rfl) ⟨1415942, by rfl⟩ : syracuseStep 1887923 = 2831885) B2831885
theorem B4247837 : Blo 1887435 4247837 := bbase (se 3 (by rfl) ⟨796469, by rfl⟩ : syracuseStep 4247837 = 1592939) (by norm_num)
theorem B2831891 : Blo 1887435 2831891 := bstep (se 1 (by rfl) ⟨2123918, by rfl⟩ : syracuseStep 2831891 = 4247837) B4247837
theorem B1887927 : Blo 1887435 1887927 := bstep (se 1 (by rfl) ⟨1415945, by rfl⟩ : syracuseStep 1887927 = 2831891) B2831891
theorem B3185885 : Blo 1887435 3185885 := bbase (se 3 (by rfl) ⟨597353, by rfl⟩ : syracuseStep 3185885 = 1194707) (by norm_num)
theorem B2123923 : Blo 1887435 2123923 := bstep (se 1 (by rfl) ⟨1592942, by rfl⟩ : syracuseStep 2123923 = 3185885) B3185885
theorem B2831897 : Blo 1887435 2831897 := bstep (se 2 (by rfl) ⟨1061961, by rfl⟩ : syracuseStep 2831897 = 2123923) B2123923
theorem B1887931 : Blo 1887435 1887931 := bstep (se 1 (by rfl) ⟨1415948, by rfl⟩ : syracuseStep 1887931 = 2831897) B2831897
theorem B6804245 : Blo 1887435 6804245 := bbase (se 6 (by rfl) ⟨159474, by rfl⟩ : syracuseStep 6804245 = 318949) (by norm_num)
theorem B4536163 : Blo 1887435 4536163 := bstep (se 1 (by rfl) ⟨3402122, by rfl⟩ : syracuseStep 4536163 = 6804245) B6804245
theorem B6048217 : Blo 1887435 6048217 := bstep (se 2 (by rfl) ⟨2268081, by rfl⟩ : syracuseStep 6048217 = 4536163) B4536163
theorem B8064289 : Blo 1887435 8064289 := bstep (se 2 (by rfl) ⟨3024108, by rfl⟩ : syracuseStep 8064289 = 6048217) B6048217
theorem B10752385 : Blo 1887435 10752385 := bstep (se 2 (by rfl) ⟨4032144, by rfl⟩ : syracuseStep 10752385 = 8064289) B8064289
theorem B14336513 : Blo 1887435 14336513 := bstep (se 2 (by rfl) ⟨5376192, by rfl⟩ : syracuseStep 14336513 = 10752385) B10752385
theorem B9557675 : Blo 1887435 9557675 := bstep (se 1 (by rfl) ⟨7168256, by rfl⟩ : syracuseStep 9557675 = 14336513) B14336513
theorem B6371783 : Blo 1887435 6371783 := bstep (se 1 (by rfl) ⟨4778837, by rfl⟩ : syracuseStep 6371783 = 9557675) B9557675
theorem B4247855 : Blo 1887435 4247855 := bstep (se 1 (by rfl) ⟨3185891, by rfl⟩ : syracuseStep 4247855 = 6371783) B6371783
theorem B2831903 : Blo 1887435 2831903 := bstep (se 1 (by rfl) ⟨2123927, by rfl⟩ : syracuseStep 2831903 = 4247855) B4247855
theorem B1887935 : Blo 1887435 1887935 := bstep (se 1 (by rfl) ⟨1415951, by rfl⟩ : syracuseStep 1887935 = 2831903) B2831903
theorem B2831909 : Blo 1887435 2831909 := bbase (se 4 (by rfl) ⟨265491, by rfl⟩ : syracuseStep 2831909 = 530983) (by norm_num)
theorem B1887939 : Blo 1887435 1887939 := bstep (se 1 (by rfl) ⟨1415954, by rfl⟩ : syracuseStep 1887939 = 2831909) B2831909
theorem B2389429 : Blo 1887435 2389429 := bbase (se 5 (by rfl) ⟨112004, by rfl⟩ : syracuseStep 2389429 = 224009) (by norm_num)
theorem B3185905 : Blo 1887435 3185905 := bstep (se 2 (by rfl) ⟨1194714, by rfl⟩ : syracuseStep 3185905 = 2389429) B2389429
theorem B4247873 : Blo 1887435 4247873 := bstep (se 2 (by rfl) ⟨1592952, by rfl⟩ : syracuseStep 4247873 = 3185905) B3185905
theorem B2831915 : Blo 1887435 2831915 := bstep (se 1 (by rfl) ⟨2123936, by rfl⟩ : syracuseStep 2831915 = 4247873) B4247873
theorem B1887943 : Blo 1887435 1887943 := bstep (se 1 (by rfl) ⟨1415957, by rfl⟩ : syracuseStep 1887943 = 2831915) B2831915
theorem B2123941 : Blo 1887435 2123941 := bbase (se 4 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 2123941 = 398239) (by norm_num)
theorem B2831921 : Blo 1887435 2831921 := bstep (se 2 (by rfl) ⟨1061970, by rfl⟩ : syracuseStep 2831921 = 2123941) B2123941
theorem B1887947 : Blo 1887435 1887947 := bstep (se 1 (by rfl) ⟨1415960, by rfl⟩ : syracuseStep 1887947 = 2831921) B2831921
theorem B6991237 : Blo 1887435 6991237 := bbase (se 4 (by rfl) ⟨655428, by rfl⟩ : syracuseStep 6991237 = 1310857) (by norm_num)
theorem B9321649 : Blo 1887435 9321649 := bstep (se 2 (by rfl) ⟨3495618, by rfl⟩ : syracuseStep 9321649 = 6991237) B6991237
theorem B49715461 : Blo 1887435 49715461 := bstep (se 4 (by rfl) ⟨4660824, by rfl⟩ : syracuseStep 49715461 = 9321649) B9321649
theorem B265149125 : Blo 1887435 265149125 := bstep (se 4 (by rfl) ⟨24857730, by rfl⟩ : syracuseStep 265149125 = 49715461) B49715461
theorem B176766083 : Blo 1887435 176766083 := bstep (se 1 (by rfl) ⟨132574562, by rfl⟩ : syracuseStep 176766083 = 265149125) B265149125
theorem B117844055 : Blo 1887435 117844055 := bstep (se 1 (by rfl) ⟨88383041, by rfl⟩ : syracuseStep 117844055 = 176766083) B176766083
theorem B78562703 : Blo 1887435 78562703 := bstep (se 1 (by rfl) ⟨58922027, by rfl⟩ : syracuseStep 78562703 = 117844055) B117844055
theorem B52375135 : Blo 1887435 52375135 := bstep (se 1 (by rfl) ⟨39281351, by rfl⟩ : syracuseStep 52375135 = 78562703) B78562703
theorem B69833513 : Blo 1887435 69833513 := bstep (se 2 (by rfl) ⟨26187567, by rfl⟩ : syracuseStep 69833513 = 52375135) B52375135
theorem B186222701 : Blo 1887435 186222701 := bstep (se 3 (by rfl) ⟨34916756, by rfl⟩ : syracuseStep 186222701 = 69833513) B69833513
theorem B124148467 : Blo 1887435 124148467 := bstep (se 1 (by rfl) ⟨93111350, by rfl⟩ : syracuseStep 124148467 = 186222701) B186222701
theorem B165531289 : Blo 1887435 165531289 := bstep (se 2 (by rfl) ⟨62074233, by rfl⟩ : syracuseStep 165531289 = 124148467) B124148467
theorem B220708385 : Blo 1887435 220708385 := bstep (se 2 (by rfl) ⟨82765644, by rfl⟩ : syracuseStep 220708385 = 165531289) B165531289
theorem B147138923 : Blo 1887435 147138923 := bstep (se 1 (by rfl) ⟨110354192, by rfl⟩ : syracuseStep 147138923 = 220708385) B220708385
theorem B98092615 : Blo 1887435 98092615 := bstep (se 1 (by rfl) ⟨73569461, by rfl⟩ : syracuseStep 98092615 = 147138923) B147138923
theorem B130790153 : Blo 1887435 130790153 := bstep (se 2 (by rfl) ⟨49046307, by rfl⟩ : syracuseStep 130790153 = 98092615) B98092615
theorem B87193435 : Blo 1887435 87193435 := bstep (se 1 (by rfl) ⟨65395076, by rfl⟩ : syracuseStep 87193435 = 130790153) B130790153
theorem B116257913 : Blo 1887435 116257913 := bstep (se 2 (by rfl) ⟨43596717, by rfl⟩ : syracuseStep 116257913 = 87193435) B87193435
theorem B77505275 : Blo 1887435 77505275 := bstep (se 1 (by rfl) ⟨58128956, by rfl⟩ : syracuseStep 77505275 = 116257913) B116257913
theorem B51670183 : Blo 1887435 51670183 := bstep (se 1 (by rfl) ⟨38752637, by rfl⟩ : syracuseStep 51670183 = 77505275) B77505275
theorem B68893577 : Blo 1887435 68893577 := bstep (se 2 (by rfl) ⟨25835091, by rfl⟩ : syracuseStep 68893577 = 51670183) B51670183
theorem B45929051 : Blo 1887435 45929051 := bstep (se 1 (by rfl) ⟨34446788, by rfl⟩ : syracuseStep 45929051 = 68893577) B68893577
theorem B30619367 : Blo 1887435 30619367 := bstep (se 1 (by rfl) ⟨22964525, by rfl⟩ : syracuseStep 30619367 = 45929051) B45929051
theorem B20412911 : Blo 1887435 20412911 := bstep (se 1 (by rfl) ⟨15309683, by rfl⟩ : syracuseStep 20412911 = 30619367) B30619367
theorem B13608607 : Blo 1887435 13608607 := bstep (se 1 (by rfl) ⟨10206455, by rfl⟩ : syracuseStep 13608607 = 20412911) B20412911
theorem B18144809 : Blo 1887435 18144809 := bstep (se 2 (by rfl) ⟨6804303, by rfl⟩ : syracuseStep 18144809 = 13608607) B13608607
theorem B12096539 : Blo 1887435 12096539 := bstep (se 1 (by rfl) ⟨9072404, by rfl⟩ : syracuseStep 12096539 = 18144809) B18144809
theorem B8064359 : Blo 1887435 8064359 := bstep (se 1 (by rfl) ⟨6048269, by rfl⟩ : syracuseStep 8064359 = 12096539) B12096539
theorem B5376239 : Blo 1887435 5376239 := bstep (se 1 (by rfl) ⟨4032179, by rfl⟩ : syracuseStep 5376239 = 8064359) B8064359
theorem B3584159 : Blo 1887435 3584159 := bstep (se 1 (by rfl) ⟨2688119, by rfl⟩ : syracuseStep 3584159 = 5376239) B5376239
theorem B2389439 : Blo 1887435 2389439 := bstep (se 1 (by rfl) ⟨1792079, by rfl⟩ : syracuseStep 2389439 = 3584159) B3584159
theorem B6371837 : Blo 1887435 6371837 := bstep (se 3 (by rfl) ⟨1194719, by rfl⟩ : syracuseStep 6371837 = 2389439) B2389439
theorem B4247891 : Blo 1887435 4247891 := bstep (se 1 (by rfl) ⟨3185918, by rfl⟩ : syracuseStep 4247891 = 6371837) B6371837
theorem B2831927 : Blo 1887435 2831927 := bstep (se 1 (by rfl) ⟨2123945, by rfl⟩ : syracuseStep 2831927 = 4247891) B4247891
theorem B1887951 : Blo 1887435 1887951 := bstep (se 1 (by rfl) ⟨1415963, by rfl⟩ : syracuseStep 1887951 = 2831927) B2831927
theorem B2831933 : Blo 1887435 2831933 := bbase (se 3 (by rfl) ⟨530987, by rfl⟩ : syracuseStep 2831933 = 1061975) (by norm_num)
theorem B1887955 : Blo 1887435 1887955 := bstep (se 1 (by rfl) ⟨1415966, by rfl⟩ : syracuseStep 1887955 = 2831933) B2831933
theorem B4247909 : Blo 1887435 4247909 := bbase (se 4 (by rfl) ⟨398241, by rfl⟩ : syracuseStep 4247909 = 796483) (by norm_num)
theorem B2831939 : Blo 1887435 2831939 := bstep (se 1 (by rfl) ⟨2123954, by rfl⟩ : syracuseStep 2831939 = 4247909) B4247909
theorem B1887959 : Blo 1887435 1887959 := bstep (se 1 (by rfl) ⟨1415969, by rfl⟩ : syracuseStep 1887959 = 2831939) B2831939
theorem B4778909 : Blo 1887435 4778909 := bbase (se 3 (by rfl) ⟨896045, by rfl⟩ : syracuseStep 4778909 = 1792091) (by norm_num)
theorem B3185939 : Blo 1887435 3185939 := bstep (se 1 (by rfl) ⟨2389454, by rfl⟩ : syracuseStep 3185939 = 4778909) B4778909
theorem B2123959 : Blo 1887435 2123959 := bstep (se 1 (by rfl) ⟨1592969, by rfl⟩ : syracuseStep 2123959 = 3185939) B3185939
theorem B2831945 : Blo 1887435 2831945 := bstep (se 2 (by rfl) ⟨1061979, by rfl⟩ : syracuseStep 2831945 = 2123959) B2123959
theorem B1887963 : Blo 1887435 1887963 := bstep (se 1 (by rfl) ⟨1415972, by rfl⟩ : syracuseStep 1887963 = 2831945) B2831945
theorem B3584189 : Blo 1887435 3584189 := bbase (se 3 (by rfl) ⟨672035, by rfl⟩ : syracuseStep 3584189 = 1344071) (by norm_num)
theorem B9557837 : Blo 1887435 9557837 := bstep (se 3 (by rfl) ⟨1792094, by rfl⟩ : syracuseStep 9557837 = 3584189) B3584189
theorem B6371891 : Blo 1887435 6371891 := bstep (se 1 (by rfl) ⟨4778918, by rfl⟩ : syracuseStep 6371891 = 9557837) B9557837
theorem B4247927 : Blo 1887435 4247927 := bstep (se 1 (by rfl) ⟨3185945, by rfl⟩ : syracuseStep 4247927 = 6371891) B6371891
theorem B2831951 : Blo 1887435 2831951 := bstep (se 1 (by rfl) ⟨2123963, by rfl⟩ : syracuseStep 2831951 = 4247927) B4247927
theorem B1887967 : Blo 1887435 1887967 := bstep (se 1 (by rfl) ⟨1415975, by rfl⟩ : syracuseStep 1887967 = 2831951) B2831951
theorem B2831957 : Blo 1887435 2831957 := bbase (se 8 (by rfl) ⟨16593, by rfl⟩ : syracuseStep 2831957 = 33187) (by norm_num)
theorem B1887971 : Blo 1887435 1887971 := bstep (se 1 (by rfl) ⟨1415978, by rfl⟩ : syracuseStep 1887971 = 2831957) B2831957
theorem B3024173 : Blo 1887435 3024173 := bbase (se 3 (by rfl) ⟨567032, by rfl⟩ : syracuseStep 3024173 = 1134065) (by norm_num)
theorem B8064461 : Blo 1887435 8064461 := bstep (se 3 (by rfl) ⟨1512086, by rfl⟩ : syracuseStep 8064461 = 3024173) B3024173
theorem B5376307 : Blo 1887435 5376307 := bstep (se 1 (by rfl) ⟨4032230, by rfl⟩ : syracuseStep 5376307 = 8064461) B8064461
theorem B7168409 : Blo 1887435 7168409 := bstep (se 2 (by rfl) ⟨2688153, by rfl⟩ : syracuseStep 7168409 = 5376307) B5376307
theorem B4778939 : Blo 1887435 4778939 := bstep (se 1 (by rfl) ⟨3584204, by rfl⟩ : syracuseStep 4778939 = 7168409) B7168409
theorem B3185959 : Blo 1887435 3185959 := bstep (se 1 (by rfl) ⟨2389469, by rfl⟩ : syracuseStep 3185959 = 4778939) B4778939
theorem B4247945 : Blo 1887435 4247945 := bstep (se 2 (by rfl) ⟨1592979, by rfl⟩ : syracuseStep 4247945 = 3185959) B3185959
theorem B2831963 : Blo 1887435 2831963 := bstep (se 1 (by rfl) ⟨2123972, by rfl⟩ : syracuseStep 2831963 = 4247945) B4247945
theorem B1887975 : Blo 1887435 1887975 := bstep (se 1 (by rfl) ⟨1415981, by rfl⟩ : syracuseStep 1887975 = 2831963) B2831963
theorem B2123977 : Blo 1887435 2123977 := bbase (se 2 (by rfl) ⟨796491, by rfl⟩ : syracuseStep 2123977 = 1592983) (by norm_num)
theorem B2831969 : Blo 1887435 2831969 := bstep (se 2 (by rfl) ⟨1061988, by rfl⟩ : syracuseStep 2831969 = 2123977) B2123977
theorem B1887979 : Blo 1887435 1887979 := bstep (se 1 (by rfl) ⟨1415984, by rfl⟩ : syracuseStep 1887979 = 2831969) B2831969
theorem B6458885 : Blo 1887435 6458885 := bbase (se 4 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 6458885 = 1211041) (by norm_num)
theorem B4305923 : Blo 1887435 4305923 := bstep (se 1 (by rfl) ⟨3229442, by rfl⟩ : syracuseStep 4305923 = 6458885) B6458885
theorem B2870615 : Blo 1887435 2870615 := bstep (se 1 (by rfl) ⟨2152961, by rfl⟩ : syracuseStep 2870615 = 4305923) B4305923
theorem B1913743 : Blo 1887435 1913743 := bstep (se 1 (by rfl) ⟨1435307, by rfl⟩ : syracuseStep 1913743 = 2870615) B2870615
theorem B2551657 : Blo 1887435 2551657 := bstep (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) B1913743
theorem B3402209 : Blo 1887435 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B9072557 : Blo 1887435 9072557 := bstep (se 3 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 9072557 = 3402209) B3402209
theorem B6048371 : Blo 1887435 6048371 := bstep (se 1 (by rfl) ⟨4536278, by rfl⟩ : syracuseStep 6048371 = 9072557) B9072557
theorem B16128989 : Blo 1887435 16128989 := bstep (se 3 (by rfl) ⟨3024185, by rfl⟩ : syracuseStep 16128989 = 6048371) B6048371
theorem B10752659 : Blo 1887435 10752659 := bstep (se 1 (by rfl) ⟨8064494, by rfl⟩ : syracuseStep 10752659 = 16128989) B16128989
theorem B7168439 : Blo 1887435 7168439 := bstep (se 1 (by rfl) ⟨5376329, by rfl⟩ : syracuseStep 7168439 = 10752659) B10752659
theorem B4778959 : Blo 1887435 4778959 := bstep (se 1 (by rfl) ⟨3584219, by rfl⟩ : syracuseStep 4778959 = 7168439) B7168439
theorem B6371945 : Blo 1887435 6371945 := bstep (se 2 (by rfl) ⟨2389479, by rfl⟩ : syracuseStep 6371945 = 4778959) B4778959
theorem B4247963 : Blo 1887435 4247963 := bstep (se 1 (by rfl) ⟨3185972, by rfl⟩ : syracuseStep 4247963 = 6371945) B6371945
theorem B2831975 : Blo 1887435 2831975 := bstep (se 1 (by rfl) ⟨2123981, by rfl⟩ : syracuseStep 2831975 = 4247963) B4247963
theorem B1887983 : Blo 1887435 1887983 := bstep (se 1 (by rfl) ⟨1415987, by rfl⟩ : syracuseStep 1887983 = 2831975) B2831975
theorem B2831981 : Blo 1887435 2831981 := bbase (se 3 (by rfl) ⟨530996, by rfl⟩ : syracuseStep 2831981 = 1061993) (by norm_num)
theorem B1887987 : Blo 1887435 1887987 := bstep (se 1 (by rfl) ⟨1415990, by rfl⟩ : syracuseStep 1887987 = 2831981) B2831981
theorem B4247981 : Blo 1887435 4247981 := bbase (se 3 (by rfl) ⟨796496, by rfl⟩ : syracuseStep 4247981 = 1592993) (by norm_num)
theorem B2831987 : Blo 1887435 2831987 := bstep (se 1 (by rfl) ⟨2123990, by rfl⟩ : syracuseStep 2831987 = 4247981) B4247981
theorem B1887991 : Blo 1887435 1887991 := bstep (se 1 (by rfl) ⟨1415993, by rfl⟩ : syracuseStep 1887991 = 2831987) B2831987
theorem B2016137 : Blo 1887435 2016137 := bbase (se 2 (by rfl) ⟨756051, by rfl⟩ : syracuseStep 2016137 = 1512103) (by norm_num)
theorem B5376365 : Blo 1887435 5376365 := bstep (se 3 (by rfl) ⟨1008068, by rfl⟩ : syracuseStep 5376365 = 2016137) B2016137
theorem B3584243 : Blo 1887435 3584243 := bstep (se 1 (by rfl) ⟨2688182, by rfl⟩ : syracuseStep 3584243 = 5376365) B5376365
theorem B2389495 : Blo 1887435 2389495 := bstep (se 1 (by rfl) ⟨1792121, by rfl⟩ : syracuseStep 2389495 = 3584243) B3584243
theorem B3185993 : Blo 1887435 3185993 := bstep (se 2 (by rfl) ⟨1194747, by rfl⟩ : syracuseStep 3185993 = 2389495) B2389495
theorem B2123995 : Blo 1887435 2123995 := bstep (se 1 (by rfl) ⟨1592996, by rfl⟩ : syracuseStep 2123995 = 3185993) B3185993
theorem B2831993 : Blo 1887435 2831993 := bstep (se 2 (by rfl) ⟨1061997, by rfl⟩ : syracuseStep 2831993 = 2123995) B2123995
theorem B1887995 : Blo 1887435 1887995 := bstep (se 1 (by rfl) ⟨1415996, by rfl⟩ : syracuseStep 1887995 = 2831993) B2831993
theorem B54435797 : Blo 1887435 54435797 := bbase (se 7 (by rfl) ⟨637919, by rfl⟩ : syracuseStep 54435797 = 1275839) (by norm_num)
theorem B36290531 : Blo 1887435 36290531 := bstep (se 1 (by rfl) ⟨27217898, by rfl⟩ : syracuseStep 36290531 = 54435797) B54435797
theorem B24193687 : Blo 1887435 24193687 := bstep (se 1 (by rfl) ⟨18145265, by rfl⟩ : syracuseStep 24193687 = 36290531) B36290531
theorem B32258249 : Blo 1887435 32258249 := bstep (se 2 (by rfl) ⟨12096843, by rfl⟩ : syracuseStep 32258249 = 24193687) B24193687
theorem B21505499 : Blo 1887435 21505499 := bstep (se 1 (by rfl) ⟨16129124, by rfl⟩ : syracuseStep 21505499 = 32258249) B32258249
theorem B14336999 : Blo 1887435 14336999 := bstep (se 1 (by rfl) ⟨10752749, by rfl⟩ : syracuseStep 14336999 = 21505499) B21505499
theorem B9557999 : Blo 1887435 9557999 := bstep (se 1 (by rfl) ⟨7168499, by rfl⟩ : syracuseStep 9557999 = 14336999) B14336999
theorem B6371999 : Blo 1887435 6371999 := bstep (se 1 (by rfl) ⟨4778999, by rfl⟩ : syracuseStep 6371999 = 9557999) B9557999
theorem B4247999 : Blo 1887435 4247999 := bstep (se 1 (by rfl) ⟨3185999, by rfl⟩ : syracuseStep 4247999 = 6371999) B6371999
theorem B2831999 : Blo 1887435 2831999 := bstep (se 1 (by rfl) ⟨2123999, by rfl⟩ : syracuseStep 2831999 = 4247999) B4247999
theorem B1887999 : Blo 1887435 1887999 := bstep (se 1 (by rfl) ⟨1415999, by rfl⟩ : syracuseStep 1887999 = 2831999) B2831999
theorem B2832005 : Blo 1887435 2832005 := bbase (se 4 (by rfl) ⟨265500, by rfl⟩ : syracuseStep 2832005 = 531001) (by norm_num)
theorem B1888003 : Blo 1887435 1888003 := bstep (se 1 (by rfl) ⟨1416002, by rfl⟩ : syracuseStep 1888003 = 2832005) B2832005
theorem B3186013 : Blo 1887435 3186013 := bbase (se 3 (by rfl) ⟨597377, by rfl⟩ : syracuseStep 3186013 = 1194755) (by norm_num)
theorem B4248017 : Blo 1887435 4248017 := bstep (se 2 (by rfl) ⟨1593006, by rfl⟩ : syracuseStep 4248017 = 3186013) B3186013
theorem B2832011 : Blo 1887435 2832011 := bstep (se 1 (by rfl) ⟨2124008, by rfl⟩ : syracuseStep 2832011 = 4248017) B4248017
theorem B1888007 : Blo 1887435 1888007 := bstep (se 1 (by rfl) ⟨1416005, by rfl⟩ : syracuseStep 1888007 = 2832011) B2832011
theorem B2124013 : Blo 1887435 2124013 := bbase (se 3 (by rfl) ⟨398252, by rfl⟩ : syracuseStep 2124013 = 796505) (by norm_num)
theorem B2832017 : Blo 1887435 2832017 := bstep (se 2 (by rfl) ⟨1062006, by rfl⟩ : syracuseStep 2832017 = 2124013) B2124013
theorem B1888011 : Blo 1887435 1888011 := bstep (se 1 (by rfl) ⟨1416008, by rfl⟩ : syracuseStep 1888011 = 2832017) B2832017
theorem B6372053 : Blo 1887435 6372053 := bbase (se 7 (by rfl) ⟨74672, by rfl⟩ : syracuseStep 6372053 = 149345) (by norm_num)
theorem B4248035 : Blo 1887435 4248035 := bstep (se 1 (by rfl) ⟨3186026, by rfl⟩ : syracuseStep 4248035 = 6372053) B6372053
theorem B2832023 : Blo 1887435 2832023 := bstep (se 1 (by rfl) ⟨2124017, by rfl⟩ : syracuseStep 2832023 = 4248035) B4248035
theorem B1888015 : Blo 1887435 1888015 := bstep (se 1 (by rfl) ⟨1416011, by rfl⟩ : syracuseStep 1888015 = 2832023) B2832023
theorem B2832029 : Blo 1887435 2832029 := bbase (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) (by norm_num)
theorem B1888019 : Blo 1887435 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B4248053 : Blo 1887435 4248053 := bbase (se 5 (by rfl) ⟨199127, by rfl⟩ : syracuseStep 4248053 = 398255) (by norm_num)
theorem B2832035 : Blo 1887435 2832035 := bstep (se 1 (by rfl) ⟨2124026, by rfl⟩ : syracuseStep 2832035 = 4248053) B4248053
theorem B1888023 : Blo 1887435 1888023 := bstep (se 1 (by rfl) ⟨1416017, by rfl⟩ : syracuseStep 1888023 = 2832035) B2832035
theorem B3229517 : Blo 1887435 3229517 := bbase (se 3 (by rfl) ⟨605534, by rfl⟩ : syracuseStep 3229517 = 1211069) (by norm_num)
theorem B8612045 : Blo 1887435 8612045 := bstep (se 3 (by rfl) ⟨1614758, by rfl⟩ : syracuseStep 8612045 = 3229517) B3229517
theorem B5741363 : Blo 1887435 5741363 := bstep (se 1 (by rfl) ⟨4306022, by rfl⟩ : syracuseStep 5741363 = 8612045) B8612045
theorem B3827575 : Blo 1887435 3827575 := bstep (se 1 (by rfl) ⟨2870681, by rfl⟩ : syracuseStep 3827575 = 5741363) B5741363
theorem B5103433 : Blo 1887435 5103433 := bstep (se 2 (by rfl) ⟨1913787, by rfl⟩ : syracuseStep 5103433 = 3827575) B3827575
theorem B6804577 : Blo 1887435 6804577 := bstep (se 2 (by rfl) ⟨2551716, by rfl⟩ : syracuseStep 6804577 = 5103433) B5103433
theorem B36291077 : Blo 1887435 36291077 := bstep (se 4 (by rfl) ⟨3402288, by rfl⟩ : syracuseStep 36291077 = 6804577) B6804577
theorem B24194051 : Blo 1887435 24194051 := bstep (se 1 (by rfl) ⟨18145538, by rfl⟩ : syracuseStep 24194051 = 36291077) B36291077
theorem B16129367 : Blo 1887435 16129367 := bstep (se 1 (by rfl) ⟨12097025, by rfl⟩ : syracuseStep 16129367 = 24194051) B24194051
theorem B10752911 : Blo 1887435 10752911 := bstep (se 1 (by rfl) ⟨8064683, by rfl⟩ : syracuseStep 10752911 = 16129367) B16129367
theorem B7168607 : Blo 1887435 7168607 := bstep (se 1 (by rfl) ⟨5376455, by rfl⟩ : syracuseStep 7168607 = 10752911) B10752911
theorem B4779071 : Blo 1887435 4779071 := bstep (se 1 (by rfl) ⟨3584303, by rfl⟩ : syracuseStep 4779071 = 7168607) B7168607
theorem B3186047 : Blo 1887435 3186047 := bstep (se 1 (by rfl) ⟨2389535, by rfl⟩ : syracuseStep 3186047 = 4779071) B4779071
theorem B2124031 : Blo 1887435 2124031 := bstep (se 1 (by rfl) ⟨1593023, by rfl⟩ : syracuseStep 2124031 = 3186047) B3186047
theorem B2832041 : Blo 1887435 2832041 := bstep (se 2 (by rfl) ⟨1062015, by rfl⟩ : syracuseStep 2832041 = 2124031) B2124031
theorem B1888027 : Blo 1887435 1888027 := bstep (se 1 (by rfl) ⟨1416020, by rfl⟩ : syracuseStep 1888027 = 2832041) B2832041
theorem B5103445 : Blo 1887435 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B6804593 : Blo 1887435 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B4536395 : Blo 1887435 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B3024263 : Blo 1887435 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B2016175 : Blo 1887435 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B2688233 : Blo 1887435 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B7168621 : Blo 1887435 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B9558161 : Blo 1887435 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B6372107 : Blo 1887435 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B4248071 : Blo 1887435 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B2832047 : Blo 1887435 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B1888031 : Blo 1887435 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B2832053 : Blo 1887435 2832053 := bbase (se 5 (by rfl) ⟨132752, by rfl⟩ : syracuseStep 2832053 = 265505) (by norm_num)
theorem B1888035 : Blo 1887435 1888035 := bstep (se 1 (by rfl) ⟨1416026, by rfl⟩ : syracuseStep 1888035 = 2832053) B2832053
theorem B4779101 : Blo 1887435 4779101 := bbase (se 3 (by rfl) ⟨896081, by rfl⟩ : syracuseStep 4779101 = 1792163) (by norm_num)
theorem B3186067 : Blo 1887435 3186067 := bstep (se 1 (by rfl) ⟨2389550, by rfl⟩ : syracuseStep 3186067 = 4779101) B4779101
theorem B4248089 : Blo 1887435 4248089 := bstep (se 2 (by rfl) ⟨1593033, by rfl⟩ : syracuseStep 4248089 = 3186067) B3186067
theorem B2832059 : Blo 1887435 2832059 := bstep (se 1 (by rfl) ⟨2124044, by rfl⟩ : syracuseStep 2832059 = 4248089) B4248089
theorem B1888039 : Blo 1887435 1888039 := bstep (se 1 (by rfl) ⟨1416029, by rfl⟩ : syracuseStep 1888039 = 2832059) B2832059
theorem B2124049 : Blo 1887435 2124049 := bbase (se 2 (by rfl) ⟨796518, by rfl⟩ : syracuseStep 2124049 = 1593037) (by norm_num)
theorem B2832065 : Blo 1887435 2832065 := bstep (se 2 (by rfl) ⟨1062024, by rfl⟩ : syracuseStep 2832065 = 2124049) B2124049
theorem B1888043 : Blo 1887435 1888043 := bstep (se 1 (by rfl) ⟨1416032, by rfl⟩ : syracuseStep 1888043 = 2832065) B2832065
theorem B3584341 : Blo 1887435 3584341 := bbase (se 10 (by rfl) ⟨5250, by rfl⟩ : syracuseStep 3584341 = 10501) (by norm_num)
theorem B4779121 : Blo 1887435 4779121 := bstep (se 2 (by rfl) ⟨1792170, by rfl⟩ : syracuseStep 4779121 = 3584341) B3584341
theorem B6372161 : Blo 1887435 6372161 := bstep (se 2 (by rfl) ⟨2389560, by rfl⟩ : syracuseStep 6372161 = 4779121) B4779121
theorem B4248107 : Blo 1887435 4248107 := bstep (se 1 (by rfl) ⟨3186080, by rfl⟩ : syracuseStep 4248107 = 6372161) B6372161
theorem B2832071 : Blo 1887435 2832071 := bstep (se 1 (by rfl) ⟨2124053, by rfl⟩ : syracuseStep 2832071 = 4248107) B4248107
theorem B1888047 : Blo 1887435 1888047 := bstep (se 1 (by rfl) ⟨1416035, by rfl⟩ : syracuseStep 1888047 = 2832071) B2832071
theorem B2832077 : Blo 1887435 2832077 := bbase (se 3 (by rfl) ⟨531014, by rfl⟩ : syracuseStep 2832077 = 1062029) (by norm_num)
theorem B1888051 : Blo 1887435 1888051 := bstep (se 1 (by rfl) ⟨1416038, by rfl⟩ : syracuseStep 1888051 = 2832077) B2832077
theorem B4248125 : Blo 1887435 4248125 := bbase (se 3 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 4248125 = 1593047) (by norm_num)
theorem B2832083 : Blo 1887435 2832083 := bstep (se 1 (by rfl) ⟨2124062, by rfl⟩ : syracuseStep 2832083 = 4248125) B4248125
theorem B1888055 : Blo 1887435 1888055 := bstep (se 1 (by rfl) ⟨1416041, by rfl⟩ : syracuseStep 1888055 = 2832083) B2832083
theorem B3186101 : Blo 1887435 3186101 := bbase (se 5 (by rfl) ⟨149348, by rfl⟩ : syracuseStep 3186101 = 298697) (by norm_num)
theorem B2124067 : Blo 1887435 2124067 := bstep (se 1 (by rfl) ⟨1593050, by rfl⟩ : syracuseStep 2124067 = 3186101) B3186101
theorem B2832089 : Blo 1887435 2832089 := bstep (se 2 (by rfl) ⟨1062033, by rfl⟩ : syracuseStep 2832089 = 2124067) B2124067
theorem B1888059 : Blo 1887435 1888059 := bstep (se 1 (by rfl) ⟨1416044, by rfl⟩ : syracuseStep 1888059 = 2832089) B2832089
theorem B2016209 : Blo 1887435 2016209 := bbase (se 2 (by rfl) ⟨756078, by rfl⟩ : syracuseStep 2016209 = 1512157) (by norm_num)
theorem B5376557 : Blo 1887435 5376557 := bstep (se 3 (by rfl) ⟨1008104, by rfl⟩ : syracuseStep 5376557 = 2016209) B2016209
theorem B14337485 : Blo 1887435 14337485 := bstep (se 3 (by rfl) ⟨2688278, by rfl⟩ : syracuseStep 14337485 = 5376557) B5376557
theorem B9558323 : Blo 1887435 9558323 := bstep (se 1 (by rfl) ⟨7168742, by rfl⟩ : syracuseStep 9558323 = 14337485) B14337485
theorem B6372215 : Blo 1887435 6372215 := bstep (se 1 (by rfl) ⟨4779161, by rfl⟩ : syracuseStep 6372215 = 9558323) B9558323
theorem B4248143 : Blo 1887435 4248143 := bstep (se 1 (by rfl) ⟨3186107, by rfl⟩ : syracuseStep 4248143 = 6372215) B6372215
theorem B2832095 : Blo 1887435 2832095 := bstep (se 1 (by rfl) ⟨2124071, by rfl⟩ : syracuseStep 2832095 = 4248143) B4248143
theorem B1888063 : Blo 1887435 1888063 := bstep (se 1 (by rfl) ⟨1416047, by rfl⟩ : syracuseStep 1888063 = 2832095) B2832095
theorem B2832101 : Blo 1887435 2832101 := bbase (se 4 (by rfl) ⟨265509, by rfl⟩ : syracuseStep 2832101 = 531019) (by norm_num)
theorem B1888067 : Blo 1887435 1888067 := bstep (se 1 (by rfl) ⟨1416050, by rfl⟩ : syracuseStep 1888067 = 2832101) B2832101
theorem B5376581 : Blo 1887435 5376581 := bbase (se 4 (by rfl) ⟨504054, by rfl⟩ : syracuseStep 5376581 = 1008109) (by norm_num)
theorem B3584387 : Blo 1887435 3584387 := bstep (se 1 (by rfl) ⟨2688290, by rfl⟩ : syracuseStep 3584387 = 5376581) B5376581
theorem B2389591 : Blo 1887435 2389591 := bstep (se 1 (by rfl) ⟨1792193, by rfl⟩ : syracuseStep 2389591 = 3584387) B3584387
theorem B3186121 : Blo 1887435 3186121 := bstep (se 2 (by rfl) ⟨1194795, by rfl⟩ : syracuseStep 3186121 = 2389591) B2389591
theorem B4248161 : Blo 1887435 4248161 := bstep (se 2 (by rfl) ⟨1593060, by rfl⟩ : syracuseStep 4248161 = 3186121) B3186121
theorem B2832107 : Blo 1887435 2832107 := bstep (se 1 (by rfl) ⟨2124080, by rfl⟩ : syracuseStep 2832107 = 4248161) B4248161
theorem B1888071 : Blo 1887435 1888071 := bstep (se 1 (by rfl) ⟨1416053, by rfl⟩ : syracuseStep 1888071 = 2832107) B2832107
theorem B2124085 : Blo 1887435 2124085 := bbase (se 5 (by rfl) ⟨99566, by rfl⟩ : syracuseStep 2124085 = 199133) (by norm_num)
theorem B2832113 : Blo 1887435 2832113 := bstep (se 2 (by rfl) ⟨1062042, by rfl⟩ : syracuseStep 2832113 = 2124085) B2124085
theorem B1888075 : Blo 1887435 1888075 := bstep (se 1 (by rfl) ⟨1416056, by rfl⟩ : syracuseStep 1888075 = 2832113) B2832113
theorem B2389601 : Blo 1887435 2389601 := bbase (se 2 (by rfl) ⟨896100, by rfl⟩ : syracuseStep 2389601 = 1792201) (by norm_num)
theorem B6372269 : Blo 1887435 6372269 := bstep (se 3 (by rfl) ⟨1194800, by rfl⟩ : syracuseStep 6372269 = 2389601) B2389601
theorem B4248179 : Blo 1887435 4248179 := bstep (se 1 (by rfl) ⟨3186134, by rfl⟩ : syracuseStep 4248179 = 6372269) B6372269
theorem B2832119 : Blo 1887435 2832119 := bstep (se 1 (by rfl) ⟨2124089, by rfl⟩ : syracuseStep 2832119 = 4248179) B4248179
theorem B1888079 : Blo 1887435 1888079 := bstep (se 1 (by rfl) ⟨1416059, by rfl⟩ : syracuseStep 1888079 = 2832119) B2832119
theorem B2832125 : Blo 1887435 2832125 := bbase (se 3 (by rfl) ⟨531023, by rfl⟩ : syracuseStep 2832125 = 1062047) (by norm_num)
theorem B1888083 : Blo 1887435 1888083 := bstep (se 1 (by rfl) ⟨1416062, by rfl⟩ : syracuseStep 1888083 = 2832125) B2832125
theorem B4248197 : Blo 1887435 4248197 := bbase (se 4 (by rfl) ⟨398268, by rfl⟩ : syracuseStep 4248197 = 796537) (by norm_num)
theorem B2832131 : Blo 1887435 2832131 := bstep (se 1 (by rfl) ⟨2124098, by rfl⟩ : syracuseStep 2832131 = 4248197) B4248197
theorem B1888087 : Blo 1887435 1888087 := bstep (se 1 (by rfl) ⟨1416065, by rfl⟩ : syracuseStep 1888087 = 2832131) B2832131
theorem B2043749 : Blo 1887435 2043749 := bbase (se 4 (by rfl) ⟨191601, by rfl⟩ : syracuseStep 2043749 = 383203) (by norm_num)
theorem B5449997 : Blo 1887435 5449997 := bstep (se 3 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 5449997 = 2043749) B2043749
theorem B3633331 : Blo 1887435 3633331 := bstep (se 1 (by rfl) ⟨2724998, by rfl⟩ : syracuseStep 3633331 = 5449997) B5449997
theorem B4844441 : Blo 1887435 4844441 := bstep (se 2 (by rfl) ⟨1816665, by rfl⟩ : syracuseStep 4844441 = 3633331) B3633331
theorem B3229627 : Blo 1887435 3229627 := bstep (se 1 (by rfl) ⟨2422220, by rfl⟩ : syracuseStep 3229627 = 4844441) B4844441
theorem B4306169 : Blo 1887435 4306169 := bstep (se 2 (by rfl) ⟨1614813, by rfl⟩ : syracuseStep 4306169 = 3229627) B3229627
theorem B11483117 : Blo 1887435 11483117 := bstep (se 3 (by rfl) ⟨2153084, by rfl⟩ : syracuseStep 11483117 = 4306169) B4306169
theorem B7655411 : Blo 1887435 7655411 := bstep (se 1 (by rfl) ⟨5741558, by rfl⟩ : syracuseStep 7655411 = 11483117) B11483117
theorem B20414429 : Blo 1887435 20414429 := bstep (se 3 (by rfl) ⟨3827705, by rfl⟩ : syracuseStep 20414429 = 7655411) B7655411
theorem B13609619 : Blo 1887435 13609619 := bstep (se 1 (by rfl) ⟨10207214, by rfl⟩ : syracuseStep 13609619 = 20414429) B20414429
theorem B9073079 : Blo 1887435 9073079 := bstep (se 1 (by rfl) ⟨6804809, by rfl⟩ : syracuseStep 9073079 = 13609619) B13609619
theorem B6048719 : Blo 1887435 6048719 := bstep (se 1 (by rfl) ⟨4536539, by rfl⟩ : syracuseStep 6048719 = 9073079) B9073079
theorem B4032479 : Blo 1887435 4032479 := bstep (se 1 (by rfl) ⟨3024359, by rfl⟩ : syracuseStep 4032479 = 6048719) B6048719
theorem B2688319 : Blo 1887435 2688319 := bstep (se 1 (by rfl) ⟨2016239, by rfl⟩ : syracuseStep 2688319 = 4032479) B4032479
theorem B3584425 : Blo 1887435 3584425 := bstep (se 2 (by rfl) ⟨1344159, by rfl⟩ : syracuseStep 3584425 = 2688319) B2688319
theorem B4779233 : Blo 1887435 4779233 := bstep (se 2 (by rfl) ⟨1792212, by rfl⟩ : syracuseStep 4779233 = 3584425) B3584425
theorem B3186155 : Blo 1887435 3186155 := bstep (se 1 (by rfl) ⟨2389616, by rfl⟩ : syracuseStep 3186155 = 4779233) B4779233
theorem B2124103 : Blo 1887435 2124103 := bstep (se 1 (by rfl) ⟨1593077, by rfl⟩ : syracuseStep 2124103 = 3186155) B3186155
theorem B2832137 : Blo 1887435 2832137 := bstep (se 2 (by rfl) ⟨1062051, by rfl⟩ : syracuseStep 2832137 = 2124103) B2124103
theorem B1888091 : Blo 1887435 1888091 := bstep (se 1 (by rfl) ⟨1416068, by rfl⟩ : syracuseStep 1888091 = 2832137) B2832137
theorem B9558485 : Blo 1887435 9558485 := bbase (se 7 (by rfl) ⟨112013, by rfl⟩ : syracuseStep 9558485 = 224027) (by norm_num)
theorem B6372323 : Blo 1887435 6372323 := bstep (se 1 (by rfl) ⟨4779242, by rfl⟩ : syracuseStep 6372323 = 9558485) B9558485
theorem B4248215 : Blo 1887435 4248215 := bstep (se 1 (by rfl) ⟨3186161, by rfl⟩ : syracuseStep 4248215 = 6372323) B6372323
theorem B2832143 : Blo 1887435 2832143 := bstep (se 1 (by rfl) ⟨2124107, by rfl⟩ : syracuseStep 2832143 = 4248215) B4248215
theorem B1888095 : Blo 1887435 1888095 := bstep (se 1 (by rfl) ⟨1416071, by rfl⟩ : syracuseStep 1888095 = 2832143) B2832143
theorem B2832149 : Blo 1887435 2832149 := bbase (se 6 (by rfl) ⟨66378, by rfl⟩ : syracuseStep 2832149 = 132757) (by norm_num)
theorem B1888099 : Blo 1887435 1888099 := bstep (se 1 (by rfl) ⟨1416074, by rfl⟩ : syracuseStep 1888099 = 2832149) B2832149
theorem B8612389 : Blo 1887435 8612389 := bbase (se 4 (by rfl) ⟨807411, by rfl⟩ : syracuseStep 8612389 = 1614823) (by norm_num)
theorem B45932741 : Blo 1887435 45932741 := bstep (se 4 (by rfl) ⟨4306194, by rfl⟩ : syracuseStep 45932741 = 8612389) B8612389
theorem B30621827 : Blo 1887435 30621827 := bstep (se 1 (by rfl) ⟨22966370, by rfl⟩ : syracuseStep 30621827 = 45932741) B45932741
theorem B81658205 : Blo 1887435 81658205 := bstep (se 3 (by rfl) ⟨15310913, by rfl⟩ : syracuseStep 81658205 = 30621827) B30621827
theorem B54438803 : Blo 1887435 54438803 := bstep (se 1 (by rfl) ⟨40829102, by rfl⟩ : syracuseStep 54438803 = 81658205) B81658205
theorem B36292535 : Blo 1887435 36292535 := bstep (se 1 (by rfl) ⟨27219401, by rfl⟩ : syracuseStep 36292535 = 54438803) B54438803
theorem B24195023 : Blo 1887435 24195023 := bstep (se 1 (by rfl) ⟨18146267, by rfl⟩ : syracuseStep 24195023 = 36292535) B36292535
theorem B16130015 : Blo 1887435 16130015 := bstep (se 1 (by rfl) ⟨12097511, by rfl⟩ : syracuseStep 16130015 = 24195023) B24195023
theorem B10753343 : Blo 1887435 10753343 := bstep (se 1 (by rfl) ⟨8065007, by rfl⟩ : syracuseStep 10753343 = 16130015) B16130015
theorem B7168895 : Blo 1887435 7168895 := bstep (se 1 (by rfl) ⟨5376671, by rfl⟩ : syracuseStep 7168895 = 10753343) B10753343
theorem B4779263 : Blo 1887435 4779263 := bstep (se 1 (by rfl) ⟨3584447, by rfl⟩ : syracuseStep 4779263 = 7168895) B7168895
theorem B3186175 : Blo 1887435 3186175 := bstep (se 1 (by rfl) ⟨2389631, by rfl⟩ : syracuseStep 3186175 = 4779263) B4779263
theorem B4248233 : Blo 1887435 4248233 := bstep (se 2 (by rfl) ⟨1593087, by rfl⟩ : syracuseStep 4248233 = 3186175) B3186175
theorem B2832155 : Blo 1887435 2832155 := bstep (se 1 (by rfl) ⟨2124116, by rfl⟩ : syracuseStep 2832155 = 4248233) B4248233
theorem B1888103 : Blo 1887435 1888103 := bstep (se 1 (by rfl) ⟨1416077, by rfl⟩ : syracuseStep 1888103 = 2832155) B2832155
theorem B2124121 : Blo 1887435 2124121 := bbase (se 2 (by rfl) ⟨796545, by rfl⟩ : syracuseStep 2124121 = 1593091) (by norm_num)
theorem B2832161 : Blo 1887435 2832161 := bstep (se 2 (by rfl) ⟨1062060, by rfl⟩ : syracuseStep 2832161 = 2124121) B2124121
theorem B1888107 : Blo 1887435 1888107 := bstep (se 1 (by rfl) ⟨1416080, by rfl⟩ : syracuseStep 1888107 = 2832161) B2832161
theorem B1913873 : Blo 1887435 1913873 := bbase (se 2 (by rfl) ⟨717702, by rfl⟩ : syracuseStep 1913873 = 1435405) (by norm_num)
theorem B5103661 : Blo 1887435 5103661 := bstep (se 3 (by rfl) ⟨956936, by rfl⟩ : syracuseStep 5103661 = 1913873) B1913873
theorem B6804881 : Blo 1887435 6804881 := bstep (se 2 (by rfl) ⟨2551830, by rfl⟩ : syracuseStep 6804881 = 5103661) B5103661
theorem B4536587 : Blo 1887435 4536587 := bstep (se 1 (by rfl) ⟨3402440, by rfl⟩ : syracuseStep 4536587 = 6804881) B6804881
theorem B3024391 : Blo 1887435 3024391 := bstep (se 1 (by rfl) ⟨2268293, by rfl⟩ : syracuseStep 3024391 = 4536587) B4536587
theorem B4032521 : Blo 1887435 4032521 := bstep (se 2 (by rfl) ⟨1512195, by rfl⟩ : syracuseStep 4032521 = 3024391) B3024391
theorem B2688347 : Blo 1887435 2688347 := bstep (se 1 (by rfl) ⟨2016260, by rfl⟩ : syracuseStep 2688347 = 4032521) B4032521
theorem B7168925 : Blo 1887435 7168925 := bstep (se 3 (by rfl) ⟨1344173, by rfl⟩ : syracuseStep 7168925 = 2688347) B2688347
theorem B4779283 : Blo 1887435 4779283 := bstep (se 1 (by rfl) ⟨3584462, by rfl⟩ : syracuseStep 4779283 = 7168925) B7168925
theorem B6372377 : Blo 1887435 6372377 := bstep (se 2 (by rfl) ⟨2389641, by rfl⟩ : syracuseStep 6372377 = 4779283) B4779283
theorem B4248251 : Blo 1887435 4248251 := bstep (se 1 (by rfl) ⟨3186188, by rfl⟩ : syracuseStep 4248251 = 6372377) B6372377
theorem B2832167 : Blo 1887435 2832167 := bstep (se 1 (by rfl) ⟨2124125, by rfl⟩ : syracuseStep 2832167 = 4248251) B4248251
theorem B1888111 : Blo 1887435 1888111 := bstep (se 1 (by rfl) ⟨1416083, by rfl⟩ : syracuseStep 1888111 = 2832167) B2832167
theorem B2832173 : Blo 1887435 2832173 := bbase (se 3 (by rfl) ⟨531032, by rfl⟩ : syracuseStep 2832173 = 1062065) (by norm_num)
theorem B1888115 : Blo 1887435 1888115 := bstep (se 1 (by rfl) ⟨1416086, by rfl⟩ : syracuseStep 1888115 = 2832173) B2832173
theorem B4248269 : Blo 1887435 4248269 := bbase (se 3 (by rfl) ⟨796550, by rfl⟩ : syracuseStep 4248269 = 1593101) (by norm_num)
theorem B2832179 : Blo 1887435 2832179 := bstep (se 1 (by rfl) ⟨2124134, by rfl⟩ : syracuseStep 2832179 = 4248269) B4248269
theorem B1888119 : Blo 1887435 1888119 := bstep (se 1 (by rfl) ⟨1416089, by rfl⟩ : syracuseStep 1888119 = 2832179) B2832179
theorem B2389657 : Blo 1887435 2389657 := bbase (se 2 (by rfl) ⟨896121, by rfl⟩ : syracuseStep 2389657 = 1792243) (by norm_num)
theorem B3186209 : Blo 1887435 3186209 := bstep (se 2 (by rfl) ⟨1194828, by rfl⟩ : syracuseStep 3186209 = 2389657) B2389657
theorem B2124139 : Blo 1887435 2124139 := bstep (se 1 (by rfl) ⟨1593104, by rfl⟩ : syracuseStep 2124139 = 3186209) B3186209
theorem B2832185 : Blo 1887435 2832185 := bstep (se 2 (by rfl) ⟨1062069, by rfl⟩ : syracuseStep 2832185 = 2124139) B2124139
theorem B1888123 : Blo 1887435 1888123 := bstep (se 1 (by rfl) ⟨1416092, by rfl⟩ : syracuseStep 1888123 = 2832185) B2832185
theorem B8065109 : Blo 1887435 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B21506957 : Blo 1887435 21506957 := bstep (se 3 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 21506957 = 8065109) B8065109
theorem B14337971 : Blo 1887435 14337971 := bstep (se 1 (by rfl) ⟨10753478, by rfl⟩ : syracuseStep 14337971 = 21506957) B21506957
theorem B9558647 : Blo 1887435 9558647 := bstep (se 1 (by rfl) ⟨7168985, by rfl⟩ : syracuseStep 9558647 = 14337971) B14337971
theorem B6372431 : Blo 1887435 6372431 := bstep (se 1 (by rfl) ⟨4779323, by rfl⟩ : syracuseStep 6372431 = 9558647) B9558647
theorem B4248287 : Blo 1887435 4248287 := bstep (se 1 (by rfl) ⟨3186215, by rfl⟩ : syracuseStep 4248287 = 6372431) B6372431
theorem B2832191 : Blo 1887435 2832191 := bstep (se 1 (by rfl) ⟨2124143, by rfl⟩ : syracuseStep 2832191 = 4248287) B4248287
theorem B1888127 : Blo 1887435 1888127 := bstep (se 1 (by rfl) ⟨1416095, by rfl⟩ : syracuseStep 1888127 = 2832191) B2832191
theorem B2832197 : Blo 1887435 2832197 := bbase (se 4 (by rfl) ⟨265518, by rfl⟩ : syracuseStep 2832197 = 531037) (by norm_num)
theorem B1888131 : Blo 1887435 1888131 := bstep (se 1 (by rfl) ⟨1416098, by rfl⟩ : syracuseStep 1888131 = 2832197) B2832197
theorem B3186229 : Blo 1887435 3186229 := bbase (se 5 (by rfl) ⟨149354, by rfl⟩ : syracuseStep 3186229 = 298709) (by norm_num)
theorem B4248305 : Blo 1887435 4248305 := bstep (se 2 (by rfl) ⟨1593114, by rfl⟩ : syracuseStep 4248305 = 3186229) B3186229
theorem B2832203 : Blo 1887435 2832203 := bstep (se 1 (by rfl) ⟨2124152, by rfl⟩ : syracuseStep 2832203 = 4248305) B4248305
theorem B1888135 : Blo 1887435 1888135 := bstep (se 1 (by rfl) ⟨1416101, by rfl⟩ : syracuseStep 1888135 = 2832203) B2832203
theorem B2124157 : Blo 1887435 2124157 := bbase (se 3 (by rfl) ⟨398279, by rfl⟩ : syracuseStep 2124157 = 796559) (by norm_num)
theorem B2832209 : Blo 1887435 2832209 := bstep (se 2 (by rfl) ⟨1062078, by rfl⟩ : syracuseStep 2832209 = 2124157) B2124157
theorem B1888139 : Blo 1887435 1888139 := bstep (se 1 (by rfl) ⟨1416104, by rfl⟩ : syracuseStep 1888139 = 2832209) B2832209
theorem B6372485 : Blo 1887435 6372485 := bbase (se 4 (by rfl) ⟨597420, by rfl⟩ : syracuseStep 6372485 = 1194841) (by norm_num)
theorem B4248323 : Blo 1887435 4248323 := bstep (se 1 (by rfl) ⟨3186242, by rfl⟩ : syracuseStep 4248323 = 6372485) B6372485
theorem B2832215 : Blo 1887435 2832215 := bstep (se 1 (by rfl) ⟨2124161, by rfl⟩ : syracuseStep 2832215 = 4248323) B4248323
theorem B1888143 : Blo 1887435 1888143 := bstep (se 1 (by rfl) ⟨1416107, by rfl⟩ : syracuseStep 1888143 = 2832215) B2832215
theorem B2832221 : Blo 1887435 2832221 := bbase (se 3 (by rfl) ⟨531041, by rfl⟩ : syracuseStep 2832221 = 1062083) (by norm_num)
theorem B1888147 : Blo 1887435 1888147 := bstep (se 1 (by rfl) ⟨1416110, by rfl⟩ : syracuseStep 1888147 = 2832221) B2832221
theorem B4248341 : Blo 1887435 4248341 := bbase (se 6 (by rfl) ⟨99570, by rfl⟩ : syracuseStep 4248341 = 199141) (by norm_num)
theorem B2832227 : Blo 1887435 2832227 := bstep (se 1 (by rfl) ⟨2124170, by rfl⟩ : syracuseStep 2832227 = 4248341) B4248341
theorem B1888151 : Blo 1887435 1888151 := bstep (se 1 (by rfl) ⟨1416113, by rfl⟩ : syracuseStep 1888151 = 2832227) B2832227
theorem B7169093 : Blo 1887435 7169093 := bbase (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) (by norm_num)
theorem B4779395 : Blo 1887435 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B3186263 : Blo 1887435 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B2124175 : Blo 1887435 2124175 := bstep (se 1 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 2124175 = 3186263) B3186263
theorem B2832233 : Blo 1887435 2832233 := bstep (se 2 (by rfl) ⟨1062087, by rfl⟩ : syracuseStep 2832233 = 2124175) B2124175
theorem B1888155 : Blo 1887435 1888155 := bstep (se 1 (by rfl) ⟨1416116, by rfl⟩ : syracuseStep 1888155 = 2832233) B2832233
theorem B19378453 : Blo 1887435 19378453 := bbase (se 6 (by rfl) ⟨454182, by rfl⟩ : syracuseStep 19378453 = 908365) (by norm_num)
theorem B25837937 : Blo 1887435 25837937 := bstep (se 2 (by rfl) ⟨9689226, by rfl⟩ : syracuseStep 25837937 = 19378453) B19378453
theorem B17225291 : Blo 1887435 17225291 := bstep (se 1 (by rfl) ⟨12918968, by rfl⟩ : syracuseStep 17225291 = 25837937) B25837937
theorem B11483527 : Blo 1887435 11483527 := bstep (se 1 (by rfl) ⟨8612645, by rfl⟩ : syracuseStep 11483527 = 17225291) B17225291
theorem B15311369 : Blo 1887435 15311369 := bstep (se 2 (by rfl) ⟨5741763, by rfl⟩ : syracuseStep 15311369 = 11483527) B11483527
theorem B10207579 : Blo 1887435 10207579 := bstep (se 1 (by rfl) ⟨7655684, by rfl⟩ : syracuseStep 10207579 = 15311369) B15311369
theorem B13610105 : Blo 1887435 13610105 := bstep (se 2 (by rfl) ⟨5103789, by rfl⟩ : syracuseStep 13610105 = 10207579) B10207579
theorem B9073403 : Blo 1887435 9073403 := bstep (se 1 (by rfl) ⟨6805052, by rfl⟩ : syracuseStep 9073403 = 13610105) B13610105
theorem B6048935 : Blo 1887435 6048935 := bstep (se 1 (by rfl) ⟨4536701, by rfl⟩ : syracuseStep 6048935 = 9073403) B9073403
theorem B4032623 : Blo 1887435 4032623 := bstep (se 1 (by rfl) ⟨3024467, by rfl⟩ : syracuseStep 4032623 = 6048935) B6048935
theorem B10753661 : Blo 1887435 10753661 := bstep (se 3 (by rfl) ⟨2016311, by rfl⟩ : syracuseStep 10753661 = 4032623) B4032623
theorem B7169107 : Blo 1887435 7169107 := bstep (se 1 (by rfl) ⟨5376830, by rfl⟩ : syracuseStep 7169107 = 10753661) B10753661
theorem B9558809 : Blo 1887435 9558809 := bstep (se 2 (by rfl) ⟨3584553, by rfl⟩ : syracuseStep 9558809 = 7169107) B7169107
theorem B6372539 : Blo 1887435 6372539 := bstep (se 1 (by rfl) ⟨4779404, by rfl⟩ : syracuseStep 6372539 = 9558809) B9558809
theorem B4248359 : Blo 1887435 4248359 := bstep (se 1 (by rfl) ⟨3186269, by rfl⟩ : syracuseStep 4248359 = 6372539) B6372539
theorem B2832239 : Blo 1887435 2832239 := bstep (se 1 (by rfl) ⟨2124179, by rfl⟩ : syracuseStep 2832239 = 4248359) B4248359
theorem B1888159 : Blo 1887435 1888159 := bstep (se 1 (by rfl) ⟨1416119, by rfl⟩ : syracuseStep 1888159 = 2832239) B2832239
theorem B2832245 : Blo 1887435 2832245 := bbase (se 5 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 2832245 = 265523) (by norm_num)
theorem B1888163 : Blo 1887435 1888163 := bstep (se 1 (by rfl) ⟨1416122, by rfl⟩ : syracuseStep 1888163 = 2832245) B2832245
theorem B2268361 : Blo 1887435 2268361 := bbase (se 2 (by rfl) ⟨850635, by rfl⟩ : syracuseStep 2268361 = 1701271) (by norm_num)
theorem B3024481 : Blo 1887435 3024481 := bstep (se 2 (by rfl) ⟨1134180, by rfl⟩ : syracuseStep 3024481 = 2268361) B2268361
theorem B4032641 : Blo 1887435 4032641 := bstep (se 2 (by rfl) ⟨1512240, by rfl⟩ : syracuseStep 4032641 = 3024481) B3024481
theorem B2688427 : Blo 1887435 2688427 := bstep (se 1 (by rfl) ⟨2016320, by rfl⟩ : syracuseStep 2688427 = 4032641) B4032641
theorem B3584569 : Blo 1887435 3584569 := bstep (se 2 (by rfl) ⟨1344213, by rfl⟩ : syracuseStep 3584569 = 2688427) B2688427
theorem B4779425 : Blo 1887435 4779425 := bstep (se 2 (by rfl) ⟨1792284, by rfl⟩ : syracuseStep 4779425 = 3584569) B3584569
theorem B3186283 : Blo 1887435 3186283 := bstep (se 1 (by rfl) ⟨2389712, by rfl⟩ : syracuseStep 3186283 = 4779425) B4779425
theorem B4248377 : Blo 1887435 4248377 := bstep (se 2 (by rfl) ⟨1593141, by rfl⟩ : syracuseStep 4248377 = 3186283) B3186283
theorem B2832251 : Blo 1887435 2832251 := bstep (se 1 (by rfl) ⟨2124188, by rfl⟩ : syracuseStep 2832251 = 4248377) B4248377
theorem B1888167 : Blo 1887435 1888167 := bstep (se 1 (by rfl) ⟨1416125, by rfl⟩ : syracuseStep 1888167 = 2832251) B2832251
theorem B2124193 : Blo 1887435 2124193 := bbase (se 2 (by rfl) ⟨796572, by rfl⟩ : syracuseStep 2124193 = 1593145) (by norm_num)
theorem B2832257 : Blo 1887435 2832257 := bstep (se 2 (by rfl) ⟨1062096, by rfl⟩ : syracuseStep 2832257 = 2124193) B2124193
theorem B1888171 : Blo 1887435 1888171 := bstep (se 1 (by rfl) ⟨1416128, by rfl⟩ : syracuseStep 1888171 = 2832257) B2832257
theorem B4779445 : Blo 1887435 4779445 := bbase (se 5 (by rfl) ⟨224036, by rfl⟩ : syracuseStep 4779445 = 448073) (by norm_num)
theorem B6372593 : Blo 1887435 6372593 := bstep (se 2 (by rfl) ⟨2389722, by rfl⟩ : syracuseStep 6372593 = 4779445) B4779445
theorem B4248395 : Blo 1887435 4248395 := bstep (se 1 (by rfl) ⟨3186296, by rfl⟩ : syracuseStep 4248395 = 6372593) B6372593
theorem B2832263 : Blo 1887435 2832263 := bstep (se 1 (by rfl) ⟨2124197, by rfl⟩ : syracuseStep 2832263 = 4248395) B4248395
theorem B1888175 : Blo 1887435 1888175 := bstep (se 1 (by rfl) ⟨1416131, by rfl⟩ : syracuseStep 1888175 = 2832263) B2832263
theorem B2832269 : Blo 1887435 2832269 := bbase (se 3 (by rfl) ⟨531050, by rfl⟩ : syracuseStep 2832269 = 1062101) (by norm_num)
theorem B1888179 : Blo 1887435 1888179 := bstep (se 1 (by rfl) ⟨1416134, by rfl⟩ : syracuseStep 1888179 = 2832269) B2832269
theorem B4248413 : Blo 1887435 4248413 := bbase (se 3 (by rfl) ⟨796577, by rfl⟩ : syracuseStep 4248413 = 1593155) (by norm_num)
theorem B2832275 : Blo 1887435 2832275 := bstep (se 1 (by rfl) ⟨2124206, by rfl⟩ : syracuseStep 2832275 = 4248413) B4248413
theorem B1888183 : Blo 1887435 1888183 := bstep (se 1 (by rfl) ⟨1416137, by rfl⟩ : syracuseStep 1888183 = 2832275) B2832275
theorem B3186317 : Blo 1887435 3186317 := bbase (se 3 (by rfl) ⟨597434, by rfl⟩ : syracuseStep 3186317 = 1194869) (by norm_num)
theorem B2124211 : Blo 1887435 2124211 := bstep (se 1 (by rfl) ⟨1593158, by rfl⟩ : syracuseStep 2124211 = 3186317) B3186317
theorem B2832281 : Blo 1887435 2832281 := bstep (se 2 (by rfl) ⟨1062105, by rfl⟩ : syracuseStep 2832281 = 2124211) B2124211
theorem B1888187 : Blo 1887435 1888187 := bstep (se 1 (by rfl) ⟨1416140, by rfl⟩ : syracuseStep 1888187 = 2832281) B2832281
theorem B2268389 : Blo 1887435 2268389 := bbase (se 4 (by rfl) ⟨212661, by rfl⟩ : syracuseStep 2268389 = 425323) (by norm_num)
theorem B6049037 : Blo 1887435 6049037 := bstep (se 3 (by rfl) ⟨1134194, by rfl⟩ : syracuseStep 6049037 = 2268389) B2268389
theorem B16130765 : Blo 1887435 16130765 := bstep (se 3 (by rfl) ⟨3024518, by rfl⟩ : syracuseStep 16130765 = 6049037) B6049037
theorem B10753843 : Blo 1887435 10753843 := bstep (se 1 (by rfl) ⟨8065382, by rfl⟩ : syracuseStep 10753843 = 16130765) B16130765
theorem B14338457 : Blo 1887435 14338457 := bstep (se 2 (by rfl) ⟨5376921, by rfl⟩ : syracuseStep 14338457 = 10753843) B10753843
theorem B9558971 : Blo 1887435 9558971 := bstep (se 1 (by rfl) ⟨7169228, by rfl⟩ : syracuseStep 9558971 = 14338457) B14338457
theorem B6372647 : Blo 1887435 6372647 := bstep (se 1 (by rfl) ⟨4779485, by rfl⟩ : syracuseStep 6372647 = 9558971) B9558971
theorem B4248431 : Blo 1887435 4248431 := bstep (se 1 (by rfl) ⟨3186323, by rfl⟩ : syracuseStep 4248431 = 6372647) B6372647
theorem B2832287 : Blo 1887435 2832287 := bstep (se 1 (by rfl) ⟨2124215, by rfl⟩ : syracuseStep 2832287 = 4248431) B4248431
theorem B1888191 : Blo 1887435 1888191 := bstep (se 1 (by rfl) ⟨1416143, by rfl⟩ : syracuseStep 1888191 = 2832287) B2832287
theorem B2832293 : Blo 1887435 2832293 := bbase (se 4 (by rfl) ⟨265527, by rfl⟩ : syracuseStep 2832293 = 531055) (by norm_num)
theorem B1888195 : Blo 1887435 1888195 := bstep (se 1 (by rfl) ⟨1416146, by rfl⟩ : syracuseStep 1888195 = 2832293) B2832293
theorem B2389753 : Blo 1887435 2389753 := bbase (se 2 (by rfl) ⟨896157, by rfl⟩ : syracuseStep 2389753 = 1792315) (by norm_num)
theorem B3186337 : Blo 1887435 3186337 := bstep (se 2 (by rfl) ⟨1194876, by rfl⟩ : syracuseStep 3186337 = 2389753) B2389753
theorem B4248449 : Blo 1887435 4248449 := bstep (se 2 (by rfl) ⟨1593168, by rfl⟩ : syracuseStep 4248449 = 3186337) B3186337
theorem B2832299 : Blo 1887435 2832299 := bstep (se 1 (by rfl) ⟨2124224, by rfl⟩ : syracuseStep 2832299 = 4248449) B4248449
theorem B1888199 : Blo 1887435 1888199 := bstep (se 1 (by rfl) ⟨1416149, by rfl⟩ : syracuseStep 1888199 = 2832299) B2832299
theorem B2124229 : Blo 1887435 2124229 := bbase (se 4 (by rfl) ⟨199146, by rfl⟩ : syracuseStep 2124229 = 398293) (by norm_num)
theorem B2832305 : Blo 1887435 2832305 := bstep (se 2 (by rfl) ⟨1062114, by rfl⟩ : syracuseStep 2832305 = 2124229) B2124229
theorem B1888203 : Blo 1887435 1888203 := bstep (se 1 (by rfl) ⟨1416152, by rfl⟩ : syracuseStep 1888203 = 2832305) B2832305
theorem B3584645 : Blo 1887435 3584645 := bbase (se 4 (by rfl) ⟨336060, by rfl⟩ : syracuseStep 3584645 = 672121) (by norm_num)
theorem B2389763 : Blo 1887435 2389763 := bstep (se 1 (by rfl) ⟨1792322, by rfl⟩ : syracuseStep 2389763 = 3584645) B3584645
theorem B6372701 : Blo 1887435 6372701 := bstep (se 3 (by rfl) ⟨1194881, by rfl⟩ : syracuseStep 6372701 = 2389763) B2389763
theorem B4248467 : Blo 1887435 4248467 := bstep (se 1 (by rfl) ⟨3186350, by rfl⟩ : syracuseStep 4248467 = 6372701) B6372701
theorem B2832311 : Blo 1887435 2832311 := bstep (se 1 (by rfl) ⟨2124233, by rfl⟩ : syracuseStep 2832311 = 4248467) B4248467
theorem B1888207 : Blo 1887435 1888207 := bstep (se 1 (by rfl) ⟨1416155, by rfl⟩ : syracuseStep 1888207 = 2832311) B2832311
theorem B2832317 : Blo 1887435 2832317 := bbase (se 3 (by rfl) ⟨531059, by rfl⟩ : syracuseStep 2832317 = 1062119) (by norm_num)
theorem B1888211 : Blo 1887435 1888211 := bstep (se 1 (by rfl) ⟨1416158, by rfl⟩ : syracuseStep 1888211 = 2832317) B2832317
theorem B4248485 : Blo 1887435 4248485 := bbase (se 4 (by rfl) ⟨398295, by rfl⟩ : syracuseStep 4248485 = 796591) (by norm_num)
theorem B2832323 : Blo 1887435 2832323 := bstep (se 1 (by rfl) ⟨2124242, by rfl⟩ : syracuseStep 2832323 = 4248485) B4248485
theorem B1888215 : Blo 1887435 1888215 := bstep (se 1 (by rfl) ⟨1416161, by rfl⟩ : syracuseStep 1888215 = 2832323) B2832323
theorem B4779557 : Blo 1887435 4779557 := bbase (se 4 (by rfl) ⟨448083, by rfl⟩ : syracuseStep 4779557 = 896167) (by norm_num)
theorem B3186371 : Blo 1887435 3186371 := bstep (se 1 (by rfl) ⟨2389778, by rfl⟩ : syracuseStep 3186371 = 4779557) B4779557
theorem B2124247 : Blo 1887435 2124247 := bstep (se 1 (by rfl) ⟨1593185, by rfl⟩ : syracuseStep 2124247 = 3186371) B3186371
theorem B2832329 : Blo 1887435 2832329 := bstep (se 2 (by rfl) ⟨1062123, by rfl⟩ : syracuseStep 2832329 = 2124247) B2124247
theorem B1888219 : Blo 1887435 1888219 := bstep (se 1 (by rfl) ⟨1416164, by rfl⟩ : syracuseStep 1888219 = 2832329) B2832329
theorem B5377013 : Blo 1887435 5377013 := bbase (se 5 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 5377013 = 504095) (by norm_num)
theorem B3584675 : Blo 1887435 3584675 := bstep (se 1 (by rfl) ⟨2688506, by rfl⟩ : syracuseStep 3584675 = 5377013) B5377013
theorem B9559133 : Blo 1887435 9559133 := bstep (se 3 (by rfl) ⟨1792337, by rfl⟩ : syracuseStep 9559133 = 3584675) B3584675
theorem B6372755 : Blo 1887435 6372755 := bstep (se 1 (by rfl) ⟨4779566, by rfl⟩ : syracuseStep 6372755 = 9559133) B9559133
theorem B4248503 : Blo 1887435 4248503 := bstep (se 1 (by rfl) ⟨3186377, by rfl⟩ : syracuseStep 4248503 = 6372755) B6372755
theorem B2832335 : Blo 1887435 2832335 := bstep (se 1 (by rfl) ⟨2124251, by rfl⟩ : syracuseStep 2832335 = 4248503) B4248503
theorem B1888223 : Blo 1887435 1888223 := bstep (se 1 (by rfl) ⟨1416167, by rfl⟩ : syracuseStep 1888223 = 2832335) B2832335
theorem B2832341 : Blo 1887435 2832341 := bbase (se 7 (by rfl) ⟨33191, by rfl⟩ : syracuseStep 2832341 = 66383) (by norm_num)
theorem B1888227 : Blo 1887435 1888227 := bstep (se 1 (by rfl) ⟨1416170, by rfl⟩ : syracuseStep 1888227 = 2832341) B2832341
theorem B7169381 : Blo 1887435 7169381 := bbase (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) (by norm_num)
theorem B4779587 : Blo 1887435 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B3186391 : Blo 1887435 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B4248521 : Blo 1887435 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B2832347 : Blo 1887435 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B1888231 : Blo 1887435 1888231 := bstep (se 1 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 1888231 = 2832347) B2832347
theorem B2124265 : Blo 1887435 2124265 := bbase (se 2 (by rfl) ⟨796599, by rfl⟩ : syracuseStep 2124265 = 1593199) (by norm_num)
theorem B2832353 : Blo 1887435 2832353 := bstep (se 2 (by rfl) ⟨1062132, by rfl⟩ : syracuseStep 2832353 = 2124265) B2124265
theorem B1888235 : Blo 1887435 1888235 := bstep (se 1 (by rfl) ⟨1416176, by rfl⟩ : syracuseStep 1888235 = 2832353) B2832353
theorem B2016397 : Blo 1887435 2016397 := bbase (se 3 (by rfl) ⟨378074, by rfl⟩ : syracuseStep 2016397 = 756149) (by norm_num)
theorem B10754117 : Blo 1887435 10754117 := bstep (se 4 (by rfl) ⟨1008198, by rfl⟩ : syracuseStep 10754117 = 2016397) B2016397
theorem B7169411 : Blo 1887435 7169411 := bstep (se 1 (by rfl) ⟨5377058, by rfl⟩ : syracuseStep 7169411 = 10754117) B10754117
theorem B4779607 : Blo 1887435 4779607 := bstep (se 1 (by rfl) ⟨3584705, by rfl⟩ : syracuseStep 4779607 = 7169411) B7169411
theorem B6372809 : Blo 1887435 6372809 := bstep (se 2 (by rfl) ⟨2389803, by rfl⟩ : syracuseStep 6372809 = 4779607) B4779607
theorem B4248539 : Blo 1887435 4248539 := bstep (se 1 (by rfl) ⟨3186404, by rfl⟩ : syracuseStep 4248539 = 6372809) B6372809
theorem B2832359 : Blo 1887435 2832359 := bstep (se 1 (by rfl) ⟨2124269, by rfl⟩ : syracuseStep 2832359 = 4248539) B4248539
theorem B1888239 : Blo 1887435 1888239 := bstep (se 1 (by rfl) ⟨1416179, by rfl⟩ : syracuseStep 1888239 = 2832359) B2832359
theorem B2832365 : Blo 1887435 2832365 := bbase (se 3 (by rfl) ⟨531068, by rfl⟩ : syracuseStep 2832365 = 1062137) (by norm_num)
theorem B1888243 : Blo 1887435 1888243 := bstep (se 1 (by rfl) ⟨1416182, by rfl⟩ : syracuseStep 1888243 = 2832365) B2832365
theorem B4248557 : Blo 1887435 4248557 := bbase (se 3 (by rfl) ⟨796604, by rfl⟩ : syracuseStep 4248557 = 1593209) (by norm_num)
theorem B2832371 : Blo 1887435 2832371 := bstep (se 1 (by rfl) ⟨2124278, by rfl⟩ : syracuseStep 2832371 = 4248557) B4248557
theorem B1888247 : Blo 1887435 1888247 := bstep (se 1 (by rfl) ⟨1416185, by rfl⟩ : syracuseStep 1888247 = 2832371) B2832371
theorem B4032821 : Blo 1887435 4032821 := bbase (se 5 (by rfl) ⟨189038, by rfl⟩ : syracuseStep 4032821 = 378077) (by norm_num)
theorem B2688547 : Blo 1887435 2688547 := bstep (se 1 (by rfl) ⟨2016410, by rfl⟩ : syracuseStep 2688547 = 4032821) B4032821
theorem B3584729 : Blo 1887435 3584729 := bstep (se 2 (by rfl) ⟨1344273, by rfl⟩ : syracuseStep 3584729 = 2688547) B2688547
theorem B2389819 : Blo 1887435 2389819 := bstep (se 1 (by rfl) ⟨1792364, by rfl⟩ : syracuseStep 2389819 = 3584729) B3584729
theorem B3186425 : Blo 1887435 3186425 := bstep (se 2 (by rfl) ⟨1194909, by rfl⟩ : syracuseStep 3186425 = 2389819) B2389819
theorem B2124283 : Blo 1887435 2124283 := bstep (se 1 (by rfl) ⟨1593212, by rfl⟩ : syracuseStep 2124283 = 3186425) B3186425
theorem B2832377 : Blo 1887435 2832377 := bstep (se 2 (by rfl) ⟨1062141, by rfl⟩ : syracuseStep 2832377 = 2124283) B2124283
theorem B1888251 : Blo 1887435 1888251 := bstep (se 1 (by rfl) ⟨1416188, by rfl⟩ : syracuseStep 1888251 = 2832377) B2832377
theorem B13095893 : Blo 1887435 13095893 := bbase (se 7 (by rfl) ⟨153467, by rfl⟩ : syracuseStep 13095893 = 306935) (by norm_num)
theorem B8730595 : Blo 1887435 8730595 := bstep (se 1 (by rfl) ⟨6547946, by rfl⟩ : syracuseStep 8730595 = 13095893) B13095893
theorem B11640793 : Blo 1887435 11640793 := bstep (se 2 (by rfl) ⟨4365297, by rfl⟩ : syracuseStep 11640793 = 8730595) B8730595
theorem B15521057 : Blo 1887435 15521057 := bstep (se 2 (by rfl) ⟨5820396, by rfl⟩ : syracuseStep 15521057 = 11640793) B11640793
theorem B10347371 : Blo 1887435 10347371 := bstep (se 1 (by rfl) ⟨7760528, by rfl⟩ : syracuseStep 10347371 = 15521057) B15521057
theorem B6898247 : Blo 1887435 6898247 := bstep (se 1 (by rfl) ⟨5173685, by rfl⟩ : syracuseStep 6898247 = 10347371) B10347371
theorem B4598831 : Blo 1887435 4598831 := bstep (se 1 (by rfl) ⟨3449123, by rfl⟩ : syracuseStep 4598831 = 6898247) B6898247
theorem B3065887 : Blo 1887435 3065887 := bstep (se 1 (by rfl) ⟨2299415, by rfl⟩ : syracuseStep 3065887 = 4598831) B4598831
theorem B4087849 : Blo 1887435 4087849 := bstep (se 2 (by rfl) ⟨1532943, by rfl⟩ : syracuseStep 4087849 = 3065887) B3065887
theorem B87207445 : Blo 1887435 87207445 := bstep (se 6 (by rfl) ⟨2043924, by rfl⟩ : syracuseStep 87207445 = 4087849) B4087849
theorem B465106373 : Blo 1887435 465106373 := bstep (se 4 (by rfl) ⟨43603722, by rfl⟩ : syracuseStep 465106373 = 87207445) B87207445
theorem B310070915 : Blo 1887435 310070915 := bstep (se 1 (by rfl) ⟨232553186, by rfl⟩ : syracuseStep 310070915 = 465106373) B465106373
theorem B206713943 : Blo 1887435 206713943 := bstep (se 1 (by rfl) ⟨155035457, by rfl⟩ : syracuseStep 206713943 = 310070915) B310070915
theorem B137809295 : Blo 1887435 137809295 := bstep (se 1 (by rfl) ⟨103356971, by rfl⟩ : syracuseStep 137809295 = 206713943) B206713943
theorem B91872863 : Blo 1887435 91872863 := bstep (se 1 (by rfl) ⟨68904647, by rfl⟩ : syracuseStep 91872863 = 137809295) B137809295
theorem B61248575 : Blo 1887435 61248575 := bstep (se 1 (by rfl) ⟨45936431, by rfl⟩ : syracuseStep 61248575 = 91872863) B91872863
theorem B163329533 : Blo 1887435 163329533 := bstep (se 3 (by rfl) ⟨30624287, by rfl⟩ : syracuseStep 163329533 = 61248575) B61248575
theorem B108886355 : Blo 1887435 108886355 := bstep (se 1 (by rfl) ⟨81664766, by rfl⟩ : syracuseStep 108886355 = 163329533) B163329533
theorem B72590903 : Blo 1887435 72590903 := bstep (se 1 (by rfl) ⟨54443177, by rfl⟩ : syracuseStep 72590903 = 108886355) B108886355
theorem B48393935 : Blo 1887435 48393935 := bstep (se 1 (by rfl) ⟨36295451, by rfl⟩ : syracuseStep 48393935 = 72590903) B72590903
theorem B32262623 : Blo 1887435 32262623 := bstep (se 1 (by rfl) ⟨24196967, by rfl⟩ : syracuseStep 32262623 = 48393935) B48393935
theorem B21508415 : Blo 1887435 21508415 := bstep (se 1 (by rfl) ⟨16131311, by rfl⟩ : syracuseStep 21508415 = 32262623) B32262623
theorem B14338943 : Blo 1887435 14338943 := bstep (se 1 (by rfl) ⟨10754207, by rfl⟩ : syracuseStep 14338943 = 21508415) B21508415
theorem B9559295 : Blo 1887435 9559295 := bstep (se 1 (by rfl) ⟨7169471, by rfl⟩ : syracuseStep 9559295 = 14338943) B14338943
theorem B6372863 : Blo 1887435 6372863 := bstep (se 1 (by rfl) ⟨4779647, by rfl⟩ : syracuseStep 6372863 = 9559295) B9559295
theorem B4248575 : Blo 1887435 4248575 := bstep (se 1 (by rfl) ⟨3186431, by rfl⟩ : syracuseStep 4248575 = 6372863) B6372863
theorem B2832383 : Blo 1887435 2832383 := bstep (se 1 (by rfl) ⟨2124287, by rfl⟩ : syracuseStep 2832383 = 4248575) B4248575
theorem B1888255 : Blo 1887435 1888255 := bstep (se 1 (by rfl) ⟨1416191, by rfl⟩ : syracuseStep 1888255 = 2832383) B2832383
theorem B2832389 : Blo 1887435 2832389 := bbase (se 4 (by rfl) ⟨265536, by rfl⟩ : syracuseStep 2832389 = 531073) (by norm_num)
theorem B1888259 : Blo 1887435 1888259 := bstep (se 1 (by rfl) ⟨1416194, by rfl⟩ : syracuseStep 1888259 = 2832389) B2832389
theorem B3186445 : Blo 1887435 3186445 := bbase (se 3 (by rfl) ⟨597458, by rfl⟩ : syracuseStep 3186445 = 1194917) (by norm_num)
theorem B4248593 : Blo 1887435 4248593 := bstep (se 2 (by rfl) ⟨1593222, by rfl⟩ : syracuseStep 4248593 = 3186445) B3186445
theorem B2832395 : Blo 1887435 2832395 := bstep (se 1 (by rfl) ⟨2124296, by rfl⟩ : syracuseStep 2832395 = 4248593) B4248593
theorem B1888263 : Blo 1887435 1888263 := bstep (se 1 (by rfl) ⟨1416197, by rfl⟩ : syracuseStep 1888263 = 2832395) B2832395
theorem B2124301 : Blo 1887435 2124301 := bbase (se 3 (by rfl) ⟨398306, by rfl⟩ : syracuseStep 2124301 = 796613) (by norm_num)
theorem B2832401 : Blo 1887435 2832401 := bstep (se 2 (by rfl) ⟨1062150, by rfl⟩ : syracuseStep 2832401 = 2124301) B2124301
theorem B1888267 : Blo 1887435 1888267 := bstep (se 1 (by rfl) ⟨1416200, by rfl⟩ : syracuseStep 1888267 = 2832401) B2832401
theorem B6372917 : Blo 1887435 6372917 := bbase (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) (by norm_num)
theorem B4248611 : Blo 1887435 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B2832407 : Blo 1887435 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B1888271 : Blo 1887435 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B2832413 : Blo 1887435 2832413 := bbase (se 3 (by rfl) ⟨531077, by rfl⟩ : syracuseStep 2832413 = 1062155) (by norm_num)
theorem B1888275 : Blo 1887435 1888275 := bstep (se 1 (by rfl) ⟨1416206, by rfl⟩ : syracuseStep 1888275 = 2832413) B2832413
theorem B4248629 : Blo 1887435 4248629 := bbase (se 5 (by rfl) ⟨199154, by rfl⟩ : syracuseStep 4248629 = 398309) (by norm_num)
theorem B2832419 : Blo 1887435 2832419 := bstep (se 1 (by rfl) ⟨2124314, by rfl⟩ : syracuseStep 2832419 = 4248629) B4248629
theorem B1888279 : Blo 1887435 1888279 := bstep (se 1 (by rfl) ⟨1416209, by rfl⟩ : syracuseStep 1888279 = 2832419) B2832419
theorem B6049333 : Blo 1887435 6049333 := bbase (se 5 (by rfl) ⟨283562, by rfl⟩ : syracuseStep 6049333 = 567125) (by norm_num)
theorem B8065777 : Blo 1887435 8065777 := bstep (se 2 (by rfl) ⟨3024666, by rfl⟩ : syracuseStep 8065777 = 6049333) B6049333
theorem B10754369 : Blo 1887435 10754369 := bstep (se 2 (by rfl) ⟨4032888, by rfl⟩ : syracuseStep 10754369 = 8065777) B8065777
theorem B7169579 : Blo 1887435 7169579 := bstep (se 1 (by rfl) ⟨5377184, by rfl⟩ : syracuseStep 7169579 = 10754369) B10754369
theorem B4779719 : Blo 1887435 4779719 := bstep (se 1 (by rfl) ⟨3584789, by rfl⟩ : syracuseStep 4779719 = 7169579) B7169579
theorem B3186479 : Blo 1887435 3186479 := bstep (se 1 (by rfl) ⟨2389859, by rfl⟩ : syracuseStep 3186479 = 4779719) B4779719
theorem B2124319 : Blo 1887435 2124319 := bstep (se 1 (by rfl) ⟨1593239, by rfl⟩ : syracuseStep 2124319 = 3186479) B3186479
theorem B2832425 : Blo 1887435 2832425 := bstep (se 2 (by rfl) ⟨1062159, by rfl⟩ : syracuseStep 2832425 = 2124319) B2124319
theorem B1888283 : Blo 1887435 1888283 := bstep (se 1 (by rfl) ⟨1416212, by rfl⟩ : syracuseStep 1888283 = 2832425) B2832425
theorem B3402757 : Blo 1887435 3402757 := bbase (se 4 (by rfl) ⟨319008, by rfl⟩ : syracuseStep 3402757 = 638017) (by norm_num)
theorem B4537009 : Blo 1887435 4537009 := bstep (se 2 (by rfl) ⟨1701378, by rfl⟩ : syracuseStep 4537009 = 3402757) B3402757
theorem B6049345 : Blo 1887435 6049345 := bstep (se 2 (by rfl) ⟨2268504, by rfl⟩ : syracuseStep 6049345 = 4537009) B4537009
theorem B8065793 : Blo 1887435 8065793 := bstep (se 2 (by rfl) ⟨3024672, by rfl⟩ : syracuseStep 8065793 = 6049345) B6049345
theorem B5377195 : Blo 1887435 5377195 := bstep (se 1 (by rfl) ⟨4032896, by rfl⟩ : syracuseStep 5377195 = 8065793) B8065793
theorem B7169593 : Blo 1887435 7169593 := bstep (se 2 (by rfl) ⟨2688597, by rfl⟩ : syracuseStep 7169593 = 5377195) B5377195
theorem B9559457 : Blo 1887435 9559457 := bstep (se 2 (by rfl) ⟨3584796, by rfl⟩ : syracuseStep 9559457 = 7169593) B7169593
theorem B6372971 : Blo 1887435 6372971 := bstep (se 1 (by rfl) ⟨4779728, by rfl⟩ : syracuseStep 6372971 = 9559457) B9559457
theorem B4248647 : Blo 1887435 4248647 := bstep (se 1 (by rfl) ⟨3186485, by rfl⟩ : syracuseStep 4248647 = 6372971) B6372971
theorem B2832431 : Blo 1887435 2832431 := bstep (se 1 (by rfl) ⟨2124323, by rfl⟩ : syracuseStep 2832431 = 4248647) B4248647
theorem B1888287 : Blo 1887435 1888287 := bstep (se 1 (by rfl) ⟨1416215, by rfl⟩ : syracuseStep 1888287 = 2832431) B2832431
theorem B2832437 : Blo 1887435 2832437 := bbase (se 5 (by rfl) ⟨132770, by rfl⟩ : syracuseStep 2832437 = 265541) (by norm_num)
theorem B1888291 : Blo 1887435 1888291 := bstep (se 1 (by rfl) ⟨1416218, by rfl⟩ : syracuseStep 1888291 = 2832437) B2832437
theorem B4779749 : Blo 1887435 4779749 := bbase (se 4 (by rfl) ⟨448101, by rfl⟩ : syracuseStep 4779749 = 896203) (by norm_num)
theorem B3186499 : Blo 1887435 3186499 := bstep (se 1 (by rfl) ⟨2389874, by rfl⟩ : syracuseStep 3186499 = 4779749) B4779749
theorem B4248665 : Blo 1887435 4248665 := bstep (se 2 (by rfl) ⟨1593249, by rfl⟩ : syracuseStep 4248665 = 3186499) B3186499
theorem B2832443 : Blo 1887435 2832443 := bstep (se 1 (by rfl) ⟨2124332, by rfl⟩ : syracuseStep 2832443 = 4248665) B4248665
theorem B1888295 : Blo 1887435 1888295 := bstep (se 1 (by rfl) ⟨1416221, by rfl⟩ : syracuseStep 1888295 = 2832443) B2832443
theorem B2124337 : Blo 1887435 2124337 := bbase (se 2 (by rfl) ⟨796626, by rfl⟩ : syracuseStep 2124337 = 1593253) (by norm_num)
theorem B2832449 : Blo 1887435 2832449 := bstep (se 2 (by rfl) ⟨1062168, by rfl⟩ : syracuseStep 2832449 = 2124337) B2124337
theorem B1888299 : Blo 1887435 1888299 := bstep (se 1 (by rfl) ⟨1416224, by rfl⟩ : syracuseStep 1888299 = 2832449) B2832449
theorem B6049397 : Blo 1887435 6049397 := bbase (se 5 (by rfl) ⟨283565, by rfl⟩ : syracuseStep 6049397 = 567131) (by norm_num)
theorem B4032931 : Blo 1887435 4032931 := bstep (se 1 (by rfl) ⟨3024698, by rfl⟩ : syracuseStep 4032931 = 6049397) B6049397
theorem B5377241 : Blo 1887435 5377241 := bstep (se 2 (by rfl) ⟨2016465, by rfl⟩ : syracuseStep 5377241 = 4032931) B4032931
theorem B3584827 : Blo 1887435 3584827 := bstep (se 1 (by rfl) ⟨2688620, by rfl⟩ : syracuseStep 3584827 = 5377241) B5377241
theorem B4779769 : Blo 1887435 4779769 := bstep (se 2 (by rfl) ⟨1792413, by rfl⟩ : syracuseStep 4779769 = 3584827) B3584827
theorem B6373025 : Blo 1887435 6373025 := bstep (se 2 (by rfl) ⟨2389884, by rfl⟩ : syracuseStep 6373025 = 4779769) B4779769
theorem B4248683 : Blo 1887435 4248683 := bstep (se 1 (by rfl) ⟨3186512, by rfl⟩ : syracuseStep 4248683 = 6373025) B6373025
theorem B2832455 : Blo 1887435 2832455 := bstep (se 1 (by rfl) ⟨2124341, by rfl⟩ : syracuseStep 2832455 = 4248683) B4248683
theorem B1888303 : Blo 1887435 1888303 := bstep (se 1 (by rfl) ⟨1416227, by rfl⟩ : syracuseStep 1888303 = 2832455) B2832455
theorem B2832461 : Blo 1887435 2832461 := bbase (se 3 (by rfl) ⟨531086, by rfl⟩ : syracuseStep 2832461 = 1062173) (by norm_num)
theorem B1888307 : Blo 1887435 1888307 := bstep (se 1 (by rfl) ⟨1416230, by rfl⟩ : syracuseStep 1888307 = 2832461) B2832461
theorem B4248701 : Blo 1887435 4248701 := bbase (se 3 (by rfl) ⟨796631, by rfl⟩ : syracuseStep 4248701 = 1593263) (by norm_num)
theorem B2832467 : Blo 1887435 2832467 := bstep (se 1 (by rfl) ⟨2124350, by rfl⟩ : syracuseStep 2832467 = 4248701) B4248701
theorem B1888311 : Blo 1887435 1888311 := bstep (se 1 (by rfl) ⟨1416233, by rfl⟩ : syracuseStep 1888311 = 2832467) B2832467
theorem B3186533 : Blo 1887435 3186533 := bbase (se 4 (by rfl) ⟨298737, by rfl⟩ : syracuseStep 3186533 = 597475) (by norm_num)
theorem B2124355 : Blo 1887435 2124355 := bstep (se 1 (by rfl) ⟨1593266, by rfl⟩ : syracuseStep 2124355 = 3186533) B3186533
theorem B2832473 : Blo 1887435 2832473 := bstep (se 2 (by rfl) ⟨1062177, by rfl⟩ : syracuseStep 2832473 = 2124355) B2124355
theorem B1888315 : Blo 1887435 1888315 := bstep (se 1 (by rfl) ⟨1416236, by rfl⟩ : syracuseStep 1888315 = 2832473) B2832473
theorem B4032965 : Blo 1887435 4032965 := bbase (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) (by norm_num)
theorem B2688643 : Blo 1887435 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B14339429 : Blo 1887435 14339429 := bstep (se 4 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 14339429 = 2688643) B2688643
theorem B9559619 : Blo 1887435 9559619 := bstep (se 1 (by rfl) ⟨7169714, by rfl⟩ : syracuseStep 9559619 = 14339429) B14339429
theorem B6373079 : Blo 1887435 6373079 := bstep (se 1 (by rfl) ⟨4779809, by rfl⟩ : syracuseStep 6373079 = 9559619) B9559619
theorem B4248719 : Blo 1887435 4248719 := bstep (se 1 (by rfl) ⟨3186539, by rfl⟩ : syracuseStep 4248719 = 6373079) B6373079
theorem B2832479 : Blo 1887435 2832479 := bstep (se 1 (by rfl) ⟨2124359, by rfl⟩ : syracuseStep 2832479 = 4248719) B4248719
theorem B1888319 : Blo 1887435 1888319 := bstep (se 1 (by rfl) ⟨1416239, by rfl⟩ : syracuseStep 1888319 = 2832479) B2832479
theorem B2832485 : Blo 1887435 2832485 := bbase (se 4 (by rfl) ⟨265545, by rfl⟩ : syracuseStep 2832485 = 531091) (by norm_num)
theorem B1888323 : Blo 1887435 1888323 := bstep (se 1 (by rfl) ⟨1416242, by rfl⟩ : syracuseStep 1888323 = 2832485) B2832485
theorem B9074213 : Blo 1887435 9074213 := bbase (se 4 (by rfl) ⟨850707, by rfl⟩ : syracuseStep 9074213 = 1701415) (by norm_num)
theorem B6049475 : Blo 1887435 6049475 := bstep (se 1 (by rfl) ⟨4537106, by rfl⟩ : syracuseStep 6049475 = 9074213) B9074213
theorem B4032983 : Blo 1887435 4032983 := bstep (se 1 (by rfl) ⟨3024737, by rfl⟩ : syracuseStep 4032983 = 6049475) B6049475
theorem B2688655 : Blo 1887435 2688655 := bstep (se 1 (by rfl) ⟨2016491, by rfl⟩ : syracuseStep 2688655 = 4032983) B4032983
theorem B3584873 : Blo 1887435 3584873 := bstep (se 2 (by rfl) ⟨1344327, by rfl⟩ : syracuseStep 3584873 = 2688655) B2688655
theorem B2389915 : Blo 1887435 2389915 := bstep (se 1 (by rfl) ⟨1792436, by rfl⟩ : syracuseStep 2389915 = 3584873) B3584873
theorem B3186553 : Blo 1887435 3186553 := bstep (se 2 (by rfl) ⟨1194957, by rfl⟩ : syracuseStep 3186553 = 2389915) B2389915
theorem B4248737 : Blo 1887435 4248737 := bstep (se 2 (by rfl) ⟨1593276, by rfl⟩ : syracuseStep 4248737 = 3186553) B3186553
theorem B2832491 : Blo 1887435 2832491 := bstep (se 1 (by rfl) ⟨2124368, by rfl⟩ : syracuseStep 2832491 = 4248737) B4248737
theorem B1888327 : Blo 1887435 1888327 := bstep (se 1 (by rfl) ⟨1416245, by rfl⟩ : syracuseStep 1888327 = 2832491) B2832491
theorem B2124373 : Blo 1887435 2124373 := bbase (se 8 (by rfl) ⟨12447, by rfl⟩ : syracuseStep 2124373 = 24895) (by norm_num)
theorem B2832497 : Blo 1887435 2832497 := bstep (se 2 (by rfl) ⟨1062186, by rfl⟩ : syracuseStep 2832497 = 2124373) B2124373
theorem B1888331 : Blo 1887435 1888331 := bstep (se 1 (by rfl) ⟨1416248, by rfl⟩ : syracuseStep 1888331 = 2832497) B2832497
theorem B2389925 : Blo 1887435 2389925 := bbase (se 4 (by rfl) ⟨224055, by rfl⟩ : syracuseStep 2389925 = 448111) (by norm_num)
theorem B6373133 : Blo 1887435 6373133 := bstep (se 3 (by rfl) ⟨1194962, by rfl⟩ : syracuseStep 6373133 = 2389925) B2389925
theorem B4248755 : Blo 1887435 4248755 := bstep (se 1 (by rfl) ⟨3186566, by rfl⟩ : syracuseStep 4248755 = 6373133) B6373133
theorem B2832503 : Blo 1887435 2832503 := bstep (se 1 (by rfl) ⟨2124377, by rfl⟩ : syracuseStep 2832503 = 4248755) B4248755
theorem B1888335 : Blo 1887435 1888335 := bstep (se 1 (by rfl) ⟨1416251, by rfl⟩ : syracuseStep 1888335 = 2832503) B2832503
theorem B2832509 : Blo 1887435 2832509 := bbase (se 3 (by rfl) ⟨531095, by rfl⟩ : syracuseStep 2832509 = 1062191) (by norm_num)
theorem B1888339 : Blo 1887435 1888339 := bstep (se 1 (by rfl) ⟨1416254, by rfl⟩ : syracuseStep 1888339 = 2832509) B2832509
theorem B4248773 : Blo 1887435 4248773 := bbase (se 4 (by rfl) ⟨398322, by rfl⟩ : syracuseStep 4248773 = 796645) (by norm_num)
theorem B2832515 : Blo 1887435 2832515 := bstep (se 1 (by rfl) ⟨2124386, by rfl⟩ : syracuseStep 2832515 = 4248773) B4248773
theorem B1888343 : Blo 1887435 1888343 := bstep (se 1 (by rfl) ⟨1416257, by rfl⟩ : syracuseStep 1888343 = 2832515) B2832515
theorem B2268577 : Blo 1887435 2268577 := bbase (se 2 (by rfl) ⟨850716, by rfl⟩ : syracuseStep 2268577 = 1701433) (by norm_num)
theorem B12099077 : Blo 1887435 12099077 := bstep (se 4 (by rfl) ⟨1134288, by rfl⟩ : syracuseStep 12099077 = 2268577) B2268577
theorem B8066051 : Blo 1887435 8066051 := bstep (se 1 (by rfl) ⟨6049538, by rfl⟩ : syracuseStep 8066051 = 12099077) B12099077
theorem B5377367 : Blo 1887435 5377367 := bstep (se 1 (by rfl) ⟨4033025, by rfl⟩ : syracuseStep 5377367 = 8066051) B8066051
theorem B3584911 : Blo 1887435 3584911 := bstep (se 1 (by rfl) ⟨2688683, by rfl⟩ : syracuseStep 3584911 = 5377367) B5377367
theorem B4779881 : Blo 1887435 4779881 := bstep (se 2 (by rfl) ⟨1792455, by rfl⟩ : syracuseStep 4779881 = 3584911) B3584911
theorem B3186587 : Blo 1887435 3186587 := bstep (se 1 (by rfl) ⟨2389940, by rfl⟩ : syracuseStep 3186587 = 4779881) B4779881
theorem B2124391 : Blo 1887435 2124391 := bstep (se 1 (by rfl) ⟨1593293, by rfl⟩ : syracuseStep 2124391 = 3186587) B3186587
theorem B2832521 : Blo 1887435 2832521 := bstep (se 2 (by rfl) ⟨1062195, by rfl⟩ : syracuseStep 2832521 = 2124391) B2124391
theorem B1888347 : Blo 1887435 1888347 := bstep (se 1 (by rfl) ⟨1416260, by rfl⟩ : syracuseStep 1888347 = 2832521) B2832521
theorem B9559781 : Blo 1887435 9559781 := bbase (se 4 (by rfl) ⟨896229, by rfl⟩ : syracuseStep 9559781 = 1792459) (by norm_num)
theorem B6373187 : Blo 1887435 6373187 := bstep (se 1 (by rfl) ⟨4779890, by rfl⟩ : syracuseStep 6373187 = 9559781) B9559781
theorem B4248791 : Blo 1887435 4248791 := bstep (se 1 (by rfl) ⟨3186593, by rfl⟩ : syracuseStep 4248791 = 6373187) B6373187
theorem B2832527 : Blo 1887435 2832527 := bstep (se 1 (by rfl) ⟨2124395, by rfl⟩ : syracuseStep 2832527 = 4248791) B4248791
theorem B1888351 : Blo 1887435 1888351 := bstep (se 1 (by rfl) ⟨1416263, by rfl⟩ : syracuseStep 1888351 = 2832527) B2832527
theorem B2832533 : Blo 1887435 2832533 := bbase (se 6 (by rfl) ⟨66387, by rfl⟩ : syracuseStep 2832533 = 132775) (by norm_num)
theorem B1888355 : Blo 1887435 1888355 := bstep (se 1 (by rfl) ⟨1416266, by rfl⟩ : syracuseStep 1888355 = 2832533) B2832533
theorem B8066101 : Blo 1887435 8066101 := bbase (se 5 (by rfl) ⟨378098, by rfl⟩ : syracuseStep 8066101 = 756197) (by norm_num)
theorem B10754801 : Blo 1887435 10754801 := bstep (se 2 (by rfl) ⟨4033050, by rfl⟩ : syracuseStep 10754801 = 8066101) B8066101
theorem B7169867 : Blo 1887435 7169867 := bstep (se 1 (by rfl) ⟨5377400, by rfl⟩ : syracuseStep 7169867 = 10754801) B10754801
theorem B4779911 : Blo 1887435 4779911 := bstep (se 1 (by rfl) ⟨3584933, by rfl⟩ : syracuseStep 4779911 = 7169867) B7169867
theorem B3186607 : Blo 1887435 3186607 := bstep (se 1 (by rfl) ⟨2389955, by rfl⟩ : syracuseStep 3186607 = 4779911) B4779911
theorem B4248809 : Blo 1887435 4248809 := bstep (se 2 (by rfl) ⟨1593303, by rfl⟩ : syracuseStep 4248809 = 3186607) B3186607
theorem B2832539 : Blo 1887435 2832539 := bstep (se 1 (by rfl) ⟨2124404, by rfl⟩ : syracuseStep 2832539 = 4248809) B4248809
theorem B1888359 : Blo 1887435 1888359 := bstep (se 1 (by rfl) ⟨1416269, by rfl⟩ : syracuseStep 1888359 = 2832539) B2832539
theorem B2124409 : Blo 1887435 2124409 := bbase (se 2 (by rfl) ⟨796653, by rfl⟩ : syracuseStep 2124409 = 1593307) (by norm_num)
theorem B2832545 : Blo 1887435 2832545 := bstep (se 2 (by rfl) ⟨1062204, by rfl⟩ : syracuseStep 2832545 = 2124409) B2124409
theorem B1888363 : Blo 1887435 1888363 := bstep (se 1 (by rfl) ⟨1416272, by rfl⟩ : syracuseStep 1888363 = 2832545) B2832545
theorem B3402901 : Blo 1887435 3402901 := bbase (se 6 (by rfl) ⟨79755, by rfl⟩ : syracuseStep 3402901 = 159511) (by norm_num)
theorem B18148805 : Blo 1887435 18148805 := bstep (se 4 (by rfl) ⟨1701450, by rfl⟩ : syracuseStep 18148805 = 3402901) B3402901
theorem B12099203 : Blo 1887435 12099203 := bstep (se 1 (by rfl) ⟨9074402, by rfl⟩ : syracuseStep 12099203 = 18148805) B18148805
theorem B8066135 : Blo 1887435 8066135 := bstep (se 1 (by rfl) ⟨6049601, by rfl⟩ : syracuseStep 8066135 = 12099203) B12099203
theorem B5377423 : Blo 1887435 5377423 := bstep (se 1 (by rfl) ⟨4033067, by rfl⟩ : syracuseStep 5377423 = 8066135) B8066135
theorem B7169897 : Blo 1887435 7169897 := bstep (se 2 (by rfl) ⟨2688711, by rfl⟩ : syracuseStep 7169897 = 5377423) B5377423
theorem B4779931 : Blo 1887435 4779931 := bstep (se 1 (by rfl) ⟨3584948, by rfl⟩ : syracuseStep 4779931 = 7169897) B7169897
theorem B6373241 : Blo 1887435 6373241 := bstep (se 2 (by rfl) ⟨2389965, by rfl⟩ : syracuseStep 6373241 = 4779931) B4779931
theorem B4248827 : Blo 1887435 4248827 := bstep (se 1 (by rfl) ⟨3186620, by rfl⟩ : syracuseStep 4248827 = 6373241) B6373241
theorem B2832551 : Blo 1887435 2832551 := bstep (se 1 (by rfl) ⟨2124413, by rfl⟩ : syracuseStep 2832551 = 4248827) B4248827
theorem B1888367 : Blo 1887435 1888367 := bstep (se 1 (by rfl) ⟨1416275, by rfl⟩ : syracuseStep 1888367 = 2832551) B2832551
theorem B2832557 : Blo 1887435 2832557 := bbase (se 3 (by rfl) ⟨531104, by rfl⟩ : syracuseStep 2832557 = 1062209) (by norm_num)
theorem B1888371 : Blo 1887435 1888371 := bstep (se 1 (by rfl) ⟨1416278, by rfl⟩ : syracuseStep 1888371 = 2832557) B2832557
theorem B4248845 : Blo 1887435 4248845 := bbase (se 3 (by rfl) ⟨796658, by rfl⟩ : syracuseStep 4248845 = 1593317) (by norm_num)
theorem B2832563 : Blo 1887435 2832563 := bstep (se 1 (by rfl) ⟨2124422, by rfl⟩ : syracuseStep 2832563 = 4248845) B4248845
theorem B1888375 : Blo 1887435 1888375 := bstep (se 1 (by rfl) ⟨1416281, by rfl⟩ : syracuseStep 1888375 = 2832563) B2832563
theorem B2389981 : Blo 1887435 2389981 := bbase (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) (by norm_num)
theorem B3186641 : Blo 1887435 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B2124427 : Blo 1887435 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B2832569 : Blo 1887435 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B1888379 : Blo 1887435 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B16132405 : Blo 1887435 16132405 := bbase (se 5 (by rfl) ⟨756206, by rfl⟩ : syracuseStep 16132405 = 1512413) (by norm_num)
theorem B21509873 : Blo 1887435 21509873 := bstep (se 2 (by rfl) ⟨8066202, by rfl⟩ : syracuseStep 21509873 = 16132405) B16132405
theorem B14339915 : Blo 1887435 14339915 := bstep (se 1 (by rfl) ⟨10754936, by rfl⟩ : syracuseStep 14339915 = 21509873) B21509873
theorem B9559943 : Blo 1887435 9559943 := bstep (se 1 (by rfl) ⟨7169957, by rfl⟩ : syracuseStep 9559943 = 14339915) B14339915
theorem B6373295 : Blo 1887435 6373295 := bstep (se 1 (by rfl) ⟨4779971, by rfl⟩ : syracuseStep 6373295 = 9559943) B9559943
theorem B4248863 : Blo 1887435 4248863 := bstep (se 1 (by rfl) ⟨3186647, by rfl⟩ : syracuseStep 4248863 = 6373295) B6373295
theorem B2832575 : Blo 1887435 2832575 := bstep (se 1 (by rfl) ⟨2124431, by rfl⟩ : syracuseStep 2832575 = 4248863) B4248863
theorem B1888383 : Blo 1887435 1888383 := bstep (se 1 (by rfl) ⟨1416287, by rfl⟩ : syracuseStep 1888383 = 2832575) B2832575
theorem B2832581 : Blo 1887435 2832581 := bbase (se 4 (by rfl) ⟨265554, by rfl⟩ : syracuseStep 2832581 = 531109) (by norm_num)
theorem B1888387 : Blo 1887435 1888387 := bstep (se 1 (by rfl) ⟨1416290, by rfl⟩ : syracuseStep 1888387 = 2832581) B2832581
theorem B3186661 : Blo 1887435 3186661 := bbase (se 4 (by rfl) ⟨298749, by rfl⟩ : syracuseStep 3186661 = 597499) (by norm_num)
theorem B4248881 : Blo 1887435 4248881 := bstep (se 2 (by rfl) ⟨1593330, by rfl⟩ : syracuseStep 4248881 = 3186661) B3186661
theorem B2832587 : Blo 1887435 2832587 := bstep (se 1 (by rfl) ⟨2124440, by rfl⟩ : syracuseStep 2832587 = 4248881) B4248881
theorem B1888391 : Blo 1887435 1888391 := bstep (se 1 (by rfl) ⟨1416293, by rfl⟩ : syracuseStep 1888391 = 2832587) B2832587
theorem B2124445 : Blo 1887435 2124445 := bbase (se 3 (by rfl) ⟨398333, by rfl⟩ : syracuseStep 2124445 = 796667) (by norm_num)
theorem B2832593 : Blo 1887435 2832593 := bstep (se 2 (by rfl) ⟨1062222, by rfl⟩ : syracuseStep 2832593 = 2124445) B2124445
theorem B1888395 : Blo 1887435 1888395 := bstep (se 1 (by rfl) ⟨1416296, by rfl⟩ : syracuseStep 1888395 = 2832593) B2832593
theorem B6373349 : Blo 1887435 6373349 := bbase (se 4 (by rfl) ⟨597501, by rfl⟩ : syracuseStep 6373349 = 1195003) (by norm_num)
theorem B4248899 : Blo 1887435 4248899 := bstep (se 1 (by rfl) ⟨3186674, by rfl⟩ : syracuseStep 4248899 = 6373349) B6373349
theorem B2832599 : Blo 1887435 2832599 := bstep (se 1 (by rfl) ⟨2124449, by rfl⟩ : syracuseStep 2832599 = 4248899) B4248899
theorem B1888399 : Blo 1887435 1888399 := bstep (se 1 (by rfl) ⟨1416299, by rfl⟩ : syracuseStep 1888399 = 2832599) B2832599
theorem B2832605 : Blo 1887435 2832605 := bbase (se 3 (by rfl) ⟨531113, by rfl⟩ : syracuseStep 2832605 = 1062227) (by norm_num)
theorem B1888403 : Blo 1887435 1888403 := bstep (se 1 (by rfl) ⟨1416302, by rfl⟩ : syracuseStep 1888403 = 2832605) B2832605
theorem B4248917 : Blo 1887435 4248917 := bbase (se 15 (by rfl) ⟨194, by rfl⟩ : syracuseStep 4248917 = 389) (by norm_num)
theorem B2832611 : Blo 1887435 2832611 := bstep (se 1 (by rfl) ⟨2124458, by rfl⟩ : syracuseStep 2832611 = 4248917) B4248917
theorem B1888407 : Blo 1887435 1888407 := bstep (se 1 (by rfl) ⟨1416305, by rfl⟩ : syracuseStep 1888407 = 2832611) B2832611
theorem B2016581 : Blo 1887435 2016581 := bbase (se 4 (by rfl) ⟨189054, by rfl⟩ : syracuseStep 2016581 = 378109) (by norm_num)
theorem B5377549 : Blo 1887435 5377549 := bstep (se 3 (by rfl) ⟨1008290, by rfl⟩ : syracuseStep 5377549 = 2016581) B2016581
theorem B7170065 : Blo 1887435 7170065 := bstep (se 2 (by rfl) ⟨2688774, by rfl⟩ : syracuseStep 7170065 = 5377549) B5377549
theorem B4780043 : Blo 1887435 4780043 := bstep (se 1 (by rfl) ⟨3585032, by rfl⟩ : syracuseStep 4780043 = 7170065) B7170065
theorem B3186695 : Blo 1887435 3186695 := bstep (se 1 (by rfl) ⟨2390021, by rfl⟩ : syracuseStep 3186695 = 4780043) B4780043
theorem B2124463 : Blo 1887435 2124463 := bstep (se 1 (by rfl) ⟨1593347, by rfl⟩ : syracuseStep 2124463 = 3186695) B3186695
theorem B2832617 : Blo 1887435 2832617 := bstep (se 2 (by rfl) ⟨1062231, by rfl⟩ : syracuseStep 2832617 = 2124463) B2124463
theorem B1888411 : Blo 1887435 1888411 := bstep (se 1 (by rfl) ⟨1416308, by rfl⟩ : syracuseStep 1888411 = 2832617) B2832617
theorem B2153453 : Blo 1887435 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B5742541 : Blo 1887435 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B30626885 : Blo 1887435 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B20417923 : Blo 1887435 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B27223897 : Blo 1887435 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B36298529 : Blo 1887435 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B24199019 : Blo 1887435 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B16132679 : Blo 1887435 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B10755119 : Blo 1887435 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B7170079 : Blo 1887435 7170079 := bstep (se 1 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 7170079 = 10755119) B10755119
theorem B9560105 : Blo 1887435 9560105 := bstep (se 2 (by rfl) ⟨3585039, by rfl⟩ : syracuseStep 9560105 = 7170079) B7170079
theorem B6373403 : Blo 1887435 6373403 := bstep (se 1 (by rfl) ⟨4780052, by rfl⟩ : syracuseStep 6373403 = 9560105) B9560105
theorem B4248935 : Blo 1887435 4248935 := bstep (se 1 (by rfl) ⟨3186701, by rfl⟩ : syracuseStep 4248935 = 6373403) B6373403
theorem B2832623 : Blo 1887435 2832623 := bstep (se 1 (by rfl) ⟨2124467, by rfl⟩ : syracuseStep 2832623 = 4248935) B4248935
theorem B1888415 : Blo 1887435 1888415 := bstep (se 1 (by rfl) ⟨1416311, by rfl⟩ : syracuseStep 1888415 = 2832623) B2832623
theorem B2832629 : Blo 1887435 2832629 := bbase (se 5 (by rfl) ⟨132779, by rfl⟩ : syracuseStep 2832629 = 265559) (by norm_num)
theorem B1888419 : Blo 1887435 1888419 := bstep (se 1 (by rfl) ⟨1416314, by rfl⟩ : syracuseStep 1888419 = 2832629) B2832629
theorem B7761221 : Blo 1887435 7761221 := bbase (se 4 (by rfl) ⟨727614, by rfl⟩ : syracuseStep 7761221 = 1455229) (by norm_num)
theorem B5174147 : Blo 1887435 5174147 := bstep (se 1 (by rfl) ⟨3880610, by rfl⟩ : syracuseStep 5174147 = 7761221) B7761221
theorem B3449431 : Blo 1887435 3449431 := bstep (se 1 (by rfl) ⟨2587073, by rfl⟩ : syracuseStep 3449431 = 5174147) B5174147
theorem B18396965 : Blo 1887435 18396965 := bstep (se 4 (by rfl) ⟨1724715, by rfl⟩ : syracuseStep 18396965 = 3449431) B3449431
theorem B12264643 : Blo 1887435 12264643 := bstep (se 1 (by rfl) ⟨9198482, by rfl⟩ : syracuseStep 12264643 = 18396965) B18396965
theorem B16352857 : Blo 1887435 16352857 := bstep (se 2 (by rfl) ⟨6132321, by rfl⟩ : syracuseStep 16352857 = 12264643) B12264643
theorem B87215237 : Blo 1887435 87215237 := bstep (se 4 (by rfl) ⟨8176428, by rfl⟩ : syracuseStep 87215237 = 16352857) B16352857
theorem B58143491 : Blo 1887435 58143491 := bstep (se 1 (by rfl) ⟨43607618, by rfl⟩ : syracuseStep 58143491 = 87215237) B87215237
theorem B38762327 : Blo 1887435 38762327 := bstep (se 1 (by rfl) ⟨29071745, by rfl⟩ : syracuseStep 38762327 = 58143491) B58143491
theorem B25841551 : Blo 1887435 25841551 := bstep (se 1 (by rfl) ⟨19381163, by rfl⟩ : syracuseStep 25841551 = 38762327) B38762327
theorem B34455401 : Blo 1887435 34455401 := bstep (se 2 (by rfl) ⟨12920775, by rfl⟩ : syracuseStep 34455401 = 25841551) B25841551
theorem B22970267 : Blo 1887435 22970267 := bstep (se 1 (by rfl) ⟨17227700, by rfl⟩ : syracuseStep 22970267 = 34455401) B34455401
theorem B15313511 : Blo 1887435 15313511 := bstep (se 1 (by rfl) ⟨11485133, by rfl⟩ : syracuseStep 15313511 = 22970267) B22970267
theorem B10209007 : Blo 1887435 10209007 := bstep (se 1 (by rfl) ⟨7656755, by rfl⟩ : syracuseStep 10209007 = 15313511) B15313511
theorem B13612009 : Blo 1887435 13612009 := bstep (se 2 (by rfl) ⟨5104503, by rfl⟩ : syracuseStep 13612009 = 10209007) B10209007
theorem B18149345 : Blo 1887435 18149345 := bstep (se 2 (by rfl) ⟨6806004, by rfl⟩ : syracuseStep 18149345 = 13612009) B13612009
theorem B12099563 : Blo 1887435 12099563 := bstep (se 1 (by rfl) ⟨9074672, by rfl⟩ : syracuseStep 12099563 = 18149345) B18149345
theorem B8066375 : Blo 1887435 8066375 := bstep (se 1 (by rfl) ⟨6049781, by rfl⟩ : syracuseStep 8066375 = 12099563) B12099563
theorem B5377583 : Blo 1887435 5377583 := bstep (se 1 (by rfl) ⟨4033187, by rfl⟩ : syracuseStep 5377583 = 8066375) B8066375
theorem B3585055 : Blo 1887435 3585055 := bstep (se 1 (by rfl) ⟨2688791, by rfl⟩ : syracuseStep 3585055 = 5377583) B5377583
theorem B4780073 : Blo 1887435 4780073 := bstep (se 2 (by rfl) ⟨1792527, by rfl⟩ : syracuseStep 4780073 = 3585055) B3585055
theorem B3186715 : Blo 1887435 3186715 := bstep (se 1 (by rfl) ⟨2390036, by rfl⟩ : syracuseStep 3186715 = 4780073) B4780073
theorem B4248953 : Blo 1887435 4248953 := bstep (se 2 (by rfl) ⟨1593357, by rfl⟩ : syracuseStep 4248953 = 3186715) B3186715
theorem B2832635 : Blo 1887435 2832635 := bstep (se 1 (by rfl) ⟨2124476, by rfl⟩ : syracuseStep 2832635 = 4248953) B4248953
theorem B1888423 : Blo 1887435 1888423 := bstep (se 1 (by rfl) ⟨1416317, by rfl⟩ : syracuseStep 1888423 = 2832635) B2832635
theorem B2124481 : Blo 1887435 2124481 := bbase (se 2 (by rfl) ⟨796680, by rfl⟩ : syracuseStep 2124481 = 1593361) (by norm_num)
theorem B2832641 : Blo 1887435 2832641 := bstep (se 2 (by rfl) ⟨1062240, by rfl⟩ : syracuseStep 2832641 = 2124481) B2124481
theorem B1888427 : Blo 1887435 1888427 := bstep (se 1 (by rfl) ⟨1416320, by rfl⟩ : syracuseStep 1888427 = 2832641) B2832641
theorem B4780093 : Blo 1887435 4780093 := bbase (se 3 (by rfl) ⟨896267, by rfl⟩ : syracuseStep 4780093 = 1792535) (by norm_num)
theorem B6373457 : Blo 1887435 6373457 := bstep (se 2 (by rfl) ⟨2390046, by rfl⟩ : syracuseStep 6373457 = 4780093) B4780093
theorem B4248971 : Blo 1887435 4248971 := bstep (se 1 (by rfl) ⟨3186728, by rfl⟩ : syracuseStep 4248971 = 6373457) B6373457
theorem B2832647 : Blo 1887435 2832647 := bstep (se 1 (by rfl) ⟨2124485, by rfl⟩ : syracuseStep 2832647 = 4248971) B4248971
theorem B1888431 : Blo 1887435 1888431 := bstep (se 1 (by rfl) ⟨1416323, by rfl⟩ : syracuseStep 1888431 = 2832647) B2832647
theorem B2832653 : Blo 1887435 2832653 := bbase (se 3 (by rfl) ⟨531122, by rfl⟩ : syracuseStep 2832653 = 1062245) (by norm_num)
theorem B1888435 : Blo 1887435 1888435 := bstep (se 1 (by rfl) ⟨1416326, by rfl⟩ : syracuseStep 1888435 = 2832653) B2832653
theorem B4248989 : Blo 1887435 4248989 := bbase (se 3 (by rfl) ⟨796685, by rfl⟩ : syracuseStep 4248989 = 1593371) (by norm_num)
theorem B2832659 : Blo 1887435 2832659 := bstep (se 1 (by rfl) ⟨2124494, by rfl⟩ : syracuseStep 2832659 = 4248989) B4248989
theorem B1888439 : Blo 1887435 1888439 := bstep (se 1 (by rfl) ⟨1416329, by rfl⟩ : syracuseStep 1888439 = 2832659) B2832659
theorem B3186749 : Blo 1887435 3186749 := bbase (se 3 (by rfl) ⟨597515, by rfl⟩ : syracuseStep 3186749 = 1195031) (by norm_num)
theorem B2124499 : Blo 1887435 2124499 := bstep (se 1 (by rfl) ⟨1593374, by rfl⟩ : syracuseStep 2124499 = 3186749) B3186749
theorem B2832665 : Blo 1887435 2832665 := bstep (se 2 (by rfl) ⟨1062249, by rfl⟩ : syracuseStep 2832665 = 2124499) B2124499
theorem B1888443 : Blo 1887435 1888443 := bstep (se 1 (by rfl) ⟨1416332, by rfl⟩ : syracuseStep 1888443 = 2832665) B2832665
theorem B2268697 : Blo 1887435 2268697 := bbase (se 2 (by rfl) ⟨850761, by rfl⟩ : syracuseStep 2268697 = 1701523) (by norm_num)
theorem B3024929 : Blo 1887435 3024929 := bstep (se 2 (by rfl) ⟨1134348, by rfl⟩ : syracuseStep 3024929 = 2268697) B2268697
theorem B2016619 : Blo 1887435 2016619 := bstep (se 1 (by rfl) ⟨1512464, by rfl⟩ : syracuseStep 2016619 = 3024929) B3024929
theorem B10755301 : Blo 1887435 10755301 := bstep (se 4 (by rfl) ⟨1008309, by rfl⟩ : syracuseStep 10755301 = 2016619) B2016619
theorem B14340401 : Blo 1887435 14340401 := bstep (se 2 (by rfl) ⟨5377650, by rfl⟩ : syracuseStep 14340401 = 10755301) B10755301
theorem B9560267 : Blo 1887435 9560267 := bstep (se 1 (by rfl) ⟨7170200, by rfl⟩ : syracuseStep 9560267 = 14340401) B14340401
theorem B6373511 : Blo 1887435 6373511 := bstep (se 1 (by rfl) ⟨4780133, by rfl⟩ : syracuseStep 6373511 = 9560267) B9560267
theorem B4249007 : Blo 1887435 4249007 := bstep (se 1 (by rfl) ⟨3186755, by rfl⟩ : syracuseStep 4249007 = 6373511) B6373511
theorem B2832671 : Blo 1887435 2832671 := bstep (se 1 (by rfl) ⟨2124503, by rfl⟩ : syracuseStep 2832671 = 4249007) B4249007
theorem B1888447 : Blo 1887435 1888447 := bstep (se 1 (by rfl) ⟨1416335, by rfl⟩ : syracuseStep 1888447 = 2832671) B2832671
theorem B2832677 : Blo 1887435 2832677 := bbase (se 4 (by rfl) ⟨265563, by rfl⟩ : syracuseStep 2832677 = 531127) (by norm_num)
theorem B1888451 : Blo 1887435 1888451 := bstep (se 1 (by rfl) ⟨1416338, by rfl⟩ : syracuseStep 1888451 = 2832677) B2832677
theorem B2390077 : Blo 1887435 2390077 := bbase (se 3 (by rfl) ⟨448139, by rfl⟩ : syracuseStep 2390077 = 896279) (by norm_num)
theorem B3186769 : Blo 1887435 3186769 := bstep (se 2 (by rfl) ⟨1195038, by rfl⟩ : syracuseStep 3186769 = 2390077) B2390077
theorem B4249025 : Blo 1887435 4249025 := bstep (se 2 (by rfl) ⟨1593384, by rfl⟩ : syracuseStep 4249025 = 3186769) B3186769
theorem B2832683 : Blo 1887435 2832683 := bstep (se 1 (by rfl) ⟨2124512, by rfl⟩ : syracuseStep 2832683 = 4249025) B4249025
theorem B1888455 : Blo 1887435 1888455 := bstep (se 1 (by rfl) ⟨1416341, by rfl⟩ : syracuseStep 1888455 = 2832683) B2832683
theorem B2124517 : Blo 1887435 2124517 := bbase (se 4 (by rfl) ⟨199173, by rfl⟩ : syracuseStep 2124517 = 398347) (by norm_num)
theorem B2832689 : Blo 1887435 2832689 := bstep (se 2 (by rfl) ⟨1062258, by rfl⟩ : syracuseStep 2832689 = 2124517) B2124517
theorem B1888459 : Blo 1887435 1888459 := bstep (se 1 (by rfl) ⟨1416344, by rfl⟩ : syracuseStep 1888459 = 2832689) B2832689
theorem B5104613 : Blo 1887435 5104613 := bbase (se 4 (by rfl) ⟨478557, by rfl⟩ : syracuseStep 5104613 = 957115) (by norm_num)
theorem B3403075 : Blo 1887435 3403075 := bstep (se 1 (by rfl) ⟨2552306, by rfl⟩ : syracuseStep 3403075 = 5104613) B5104613
theorem B4537433 : Blo 1887435 4537433 := bstep (se 2 (by rfl) ⟨1701537, by rfl⟩ : syracuseStep 4537433 = 3403075) B3403075
theorem B3024955 : Blo 1887435 3024955 := bstep (se 1 (by rfl) ⟨2268716, by rfl⟩ : syracuseStep 3024955 = 4537433) B4537433
theorem B4033273 : Blo 1887435 4033273 := bstep (se 2 (by rfl) ⟨1512477, by rfl⟩ : syracuseStep 4033273 = 3024955) B3024955
theorem B5377697 : Blo 1887435 5377697 := bstep (se 2 (by rfl) ⟨2016636, by rfl⟩ : syracuseStep 5377697 = 4033273) B4033273
theorem B3585131 : Blo 1887435 3585131 := bstep (se 1 (by rfl) ⟨2688848, by rfl⟩ : syracuseStep 3585131 = 5377697) B5377697
theorem B2390087 : Blo 1887435 2390087 := bstep (se 1 (by rfl) ⟨1792565, by rfl⟩ : syracuseStep 2390087 = 3585131) B3585131
theorem B6373565 : Blo 1887435 6373565 := bstep (se 3 (by rfl) ⟨1195043, by rfl⟩ : syracuseStep 6373565 = 2390087) B2390087
theorem B4249043 : Blo 1887435 4249043 := bstep (se 1 (by rfl) ⟨3186782, by rfl⟩ : syracuseStep 4249043 = 6373565) B6373565
theorem B2832695 : Blo 1887435 2832695 := bstep (se 1 (by rfl) ⟨2124521, by rfl⟩ : syracuseStep 2832695 = 4249043) B4249043
theorem B1888463 : Blo 1887435 1888463 := bstep (se 1 (by rfl) ⟨1416347, by rfl⟩ : syracuseStep 1888463 = 2832695) B2832695
theorem B2832701 : Blo 1887435 2832701 := bbase (se 3 (by rfl) ⟨531131, by rfl⟩ : syracuseStep 2832701 = 1062263) (by norm_num)
theorem B1888467 : Blo 1887435 1888467 := bstep (se 1 (by rfl) ⟨1416350, by rfl⟩ : syracuseStep 1888467 = 2832701) B2832701
theorem B4249061 : Blo 1887435 4249061 := bbase (se 4 (by rfl) ⟨398349, by rfl⟩ : syracuseStep 4249061 = 796699) (by norm_num)
theorem B2832707 : Blo 1887435 2832707 := bstep (se 1 (by rfl) ⟨2124530, by rfl⟩ : syracuseStep 2832707 = 4249061) B4249061
theorem B1888471 : Blo 1887435 1888471 := bstep (se 1 (by rfl) ⟨1416353, by rfl⟩ : syracuseStep 1888471 = 2832707) B2832707
theorem B4780205 : Blo 1887435 4780205 := bbase (se 3 (by rfl) ⟨896288, by rfl⟩ : syracuseStep 4780205 = 1792577) (by norm_num)
theorem B3186803 : Blo 1887435 3186803 := bstep (se 1 (by rfl) ⟨2390102, by rfl⟩ : syracuseStep 3186803 = 4780205) B4780205
theorem B2124535 : Blo 1887435 2124535 := bstep (se 1 (by rfl) ⟨1593401, by rfl⟩ : syracuseStep 2124535 = 3186803) B3186803
theorem B2832713 : Blo 1887435 2832713 := bstep (se 2 (by rfl) ⟨1062267, by rfl⟩ : syracuseStep 2832713 = 2124535) B2124535
theorem B1888475 : Blo 1887435 1888475 := bstep (se 1 (by rfl) ⟨1416356, by rfl⟩ : syracuseStep 1888475 = 2832713) B2832713
theorem B43608917 : Blo 1887435 43608917 := bbase (se 9 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 43608917 = 255521) (by norm_num)
theorem B29072611 : Blo 1887435 29072611 := bstep (se 1 (by rfl) ⟨21804458, by rfl⟩ : syracuseStep 29072611 = 43608917) B43608917
theorem B38763481 : Blo 1887435 38763481 := bstep (se 2 (by rfl) ⟨14536305, by rfl⟩ : syracuseStep 38763481 = 29072611) B29072611
theorem B51684641 : Blo 1887435 51684641 := bstep (se 2 (by rfl) ⟨19381740, by rfl⟩ : syracuseStep 51684641 = 38763481) B38763481
theorem B34456427 : Blo 1887435 34456427 := bstep (se 1 (by rfl) ⟨25842320, by rfl⟩ : syracuseStep 34456427 = 51684641) B51684641
theorem B22970951 : Blo 1887435 22970951 := bstep (se 1 (by rfl) ⟨17228213, by rfl⟩ : syracuseStep 22970951 = 34456427) B34456427
theorem B15313967 : Blo 1887435 15313967 := bstep (se 1 (by rfl) ⟨11485475, by rfl⟩ : syracuseStep 15313967 = 22970951) B22970951
theorem B10209311 : Blo 1887435 10209311 := bstep (se 1 (by rfl) ⟨7656983, by rfl⟩ : syracuseStep 10209311 = 15313967) B15313967
theorem B6806207 : Blo 1887435 6806207 := bstep (se 1 (by rfl) ⟨5104655, by rfl⟩ : syracuseStep 6806207 = 10209311) B10209311
theorem B4537471 : Blo 1887435 4537471 := bstep (se 1 (by rfl) ⟨3403103, by rfl⟩ : syracuseStep 4537471 = 6806207) B6806207
theorem B6049961 : Blo 1887435 6049961 := bstep (se 2 (by rfl) ⟨2268735, by rfl⟩ : syracuseStep 6049961 = 4537471) B4537471
theorem B4033307 : Blo 1887435 4033307 := bstep (se 1 (by rfl) ⟨3024980, by rfl⟩ : syracuseStep 4033307 = 6049961) B6049961
theorem B2688871 : Blo 1887435 2688871 := bstep (se 1 (by rfl) ⟨2016653, by rfl⟩ : syracuseStep 2688871 = 4033307) B4033307
theorem B3585161 : Blo 1887435 3585161 := bstep (se 2 (by rfl) ⟨1344435, by rfl⟩ : syracuseStep 3585161 = 2688871) B2688871
theorem B9560429 : Blo 1887435 9560429 := bstep (se 3 (by rfl) ⟨1792580, by rfl⟩ : syracuseStep 9560429 = 3585161) B3585161
theorem B6373619 : Blo 1887435 6373619 := bstep (se 1 (by rfl) ⟨4780214, by rfl⟩ : syracuseStep 6373619 = 9560429) B9560429
theorem B4249079 : Blo 1887435 4249079 := bstep (se 1 (by rfl) ⟨3186809, by rfl⟩ : syracuseStep 4249079 = 6373619) B6373619
theorem B2832719 : Blo 1887435 2832719 := bstep (se 1 (by rfl) ⟨2124539, by rfl⟩ : syracuseStep 2832719 = 4249079) B4249079
theorem B1888479 : Blo 1887435 1888479 := bstep (se 1 (by rfl) ⟨1416359, by rfl⟩ : syracuseStep 1888479 = 2832719) B2832719
theorem B2832725 : Blo 1887435 2832725 := bbase (se 10 (by rfl) ⟨4149, by rfl⟩ : syracuseStep 2832725 = 8299) (by norm_num)
theorem B1888483 : Blo 1887435 1888483 := bstep (se 1 (by rfl) ⟨1416362, by rfl⟩ : syracuseStep 1888483 = 2832725) B2832725
theorem B5377765 : Blo 1887435 5377765 := bbase (se 4 (by rfl) ⟨504165, by rfl⟩ : syracuseStep 5377765 = 1008331) (by norm_num)
theorem B7170353 : Blo 1887435 7170353 := bstep (se 2 (by rfl) ⟨2688882, by rfl⟩ : syracuseStep 7170353 = 5377765) B5377765
theorem B4780235 : Blo 1887435 4780235 := bstep (se 1 (by rfl) ⟨3585176, by rfl⟩ : syracuseStep 4780235 = 7170353) B7170353
theorem B3186823 : Blo 1887435 3186823 := bstep (se 1 (by rfl) ⟨2390117, by rfl⟩ : syracuseStep 3186823 = 4780235) B4780235
theorem B4249097 : Blo 1887435 4249097 := bstep (se 2 (by rfl) ⟨1593411, by rfl⟩ : syracuseStep 4249097 = 3186823) B3186823
theorem B2832731 : Blo 1887435 2832731 := bstep (se 1 (by rfl) ⟨2124548, by rfl⟩ : syracuseStep 2832731 = 4249097) B4249097
theorem B1888487 : Blo 1887435 1888487 := bstep (se 1 (by rfl) ⟨1416365, by rfl⟩ : syracuseStep 1888487 = 2832731) B2832731
theorem B2124553 : Blo 1887435 2124553 := bbase (se 2 (by rfl) ⟨796707, by rfl⟩ : syracuseStep 2124553 = 1593415) (by norm_num)
theorem B2832737 : Blo 1887435 2832737 := bstep (se 2 (by rfl) ⟨1062276, by rfl⟩ : syracuseStep 2832737 = 2124553) B2124553
theorem B1888491 : Blo 1887435 1888491 := bstep (se 1 (by rfl) ⟨1416368, by rfl⟩ : syracuseStep 1888491 = 2832737) B2832737
theorem B3230317 : Blo 1887435 3230317 := bbase (se 3 (by rfl) ⟨605684, by rfl⟩ : syracuseStep 3230317 = 1211369) (by norm_num)
theorem B4307089 : Blo 1887435 4307089 := bstep (se 2 (by rfl) ⟨1615158, by rfl⟩ : syracuseStep 4307089 = 3230317) B3230317
theorem B5742785 : Blo 1887435 5742785 := bstep (se 2 (by rfl) ⟨2153544, by rfl⟩ : syracuseStep 5742785 = 4307089) B4307089
theorem B15314093 : Blo 1887435 15314093 := bstep (se 3 (by rfl) ⟨2871392, by rfl⟩ : syracuseStep 15314093 = 5742785) B5742785
theorem B10209395 : Blo 1887435 10209395 := bstep (se 1 (by rfl) ⟨7657046, by rfl⟩ : syracuseStep 10209395 = 15314093) B15314093
theorem B6806263 : Blo 1887435 6806263 := bstep (se 1 (by rfl) ⟨5104697, by rfl⟩ : syracuseStep 6806263 = 10209395) B10209395
theorem B9075017 : Blo 1887435 9075017 := bstep (se 2 (by rfl) ⟨3403131, by rfl⟩ : syracuseStep 9075017 = 6806263) B6806263
theorem B24200045 : Blo 1887435 24200045 := bstep (se 3 (by rfl) ⟨4537508, by rfl⟩ : syracuseStep 24200045 = 9075017) B9075017
theorem B16133363 : Blo 1887435 16133363 := bstep (se 1 (by rfl) ⟨12100022, by rfl⟩ : syracuseStep 16133363 = 24200045) B24200045
theorem B10755575 : Blo 1887435 10755575 := bstep (se 1 (by rfl) ⟨8066681, by rfl⟩ : syracuseStep 10755575 = 16133363) B16133363
theorem B7170383 : Blo 1887435 7170383 := bstep (se 1 (by rfl) ⟨5377787, by rfl⟩ : syracuseStep 7170383 = 10755575) B10755575
theorem B4780255 : Blo 1887435 4780255 := bstep (se 1 (by rfl) ⟨3585191, by rfl⟩ : syracuseStep 4780255 = 7170383) B7170383
theorem B6373673 : Blo 1887435 6373673 := bstep (se 2 (by rfl) ⟨2390127, by rfl⟩ : syracuseStep 6373673 = 4780255) B4780255
theorem B4249115 : Blo 1887435 4249115 := bstep (se 1 (by rfl) ⟨3186836, by rfl⟩ : syracuseStep 4249115 = 6373673) B6373673
theorem B2832743 : Blo 1887435 2832743 := bstep (se 1 (by rfl) ⟨2124557, by rfl⟩ : syracuseStep 2832743 = 4249115) B4249115
theorem B1888495 : Blo 1887435 1888495 := bstep (se 1 (by rfl) ⟨1416371, by rfl⟩ : syracuseStep 1888495 = 2832743) B2832743
theorem B2832749 : Blo 1887435 2832749 := bbase (se 3 (by rfl) ⟨531140, by rfl⟩ : syracuseStep 2832749 = 1062281) (by norm_num)
theorem B1888499 : Blo 1887435 1888499 := bstep (se 1 (by rfl) ⟨1416374, by rfl⟩ : syracuseStep 1888499 = 2832749) B2832749
theorem B4249133 : Blo 1887435 4249133 := bbase (se 3 (by rfl) ⟨796712, by rfl⟩ : syracuseStep 4249133 = 1593425) (by norm_num)
theorem B2832755 : Blo 1887435 2832755 := bstep (se 1 (by rfl) ⟨2124566, by rfl⟩ : syracuseStep 2832755 = 4249133) B4249133
theorem B1888503 : Blo 1887435 1888503 := bstep (se 1 (by rfl) ⟨1416377, by rfl⟩ : syracuseStep 1888503 = 2832755) B2832755
theorem B16353589 : Blo 1887435 16353589 := bbase (se 5 (by rfl) ⟨766574, by rfl⟩ : syracuseStep 16353589 = 1533149) (by norm_num)
theorem B21804785 : Blo 1887435 21804785 := bstep (se 2 (by rfl) ⟨8176794, by rfl⟩ : syracuseStep 21804785 = 16353589) B16353589
theorem B14536523 : Blo 1887435 14536523 := bstep (se 1 (by rfl) ⟨10902392, by rfl⟩ : syracuseStep 14536523 = 21804785) B21804785
theorem B9691015 : Blo 1887435 9691015 := bstep (se 1 (by rfl) ⟨7268261, by rfl⟩ : syracuseStep 9691015 = 14536523) B14536523
theorem B12921353 : Blo 1887435 12921353 := bstep (se 2 (by rfl) ⟨4845507, by rfl⟩ : syracuseStep 12921353 = 9691015) B9691015
theorem B8614235 : Blo 1887435 8614235 := bstep (se 1 (by rfl) ⟨6460676, by rfl⟩ : syracuseStep 8614235 = 12921353) B12921353
theorem B5742823 : Blo 1887435 5742823 := bstep (se 1 (by rfl) ⟨4307117, by rfl⟩ : syracuseStep 5742823 = 8614235) B8614235
theorem B7657097 : Blo 1887435 7657097 := bstep (se 2 (by rfl) ⟨2871411, by rfl⟩ : syracuseStep 7657097 = 5742823) B5742823
theorem B20418925 : Blo 1887435 20418925 := bstep (se 3 (by rfl) ⟨3828548, by rfl⟩ : syracuseStep 20418925 = 7657097) B7657097
theorem B27225233 : Blo 1887435 27225233 := bstep (se 2 (by rfl) ⟨10209462, by rfl⟩ : syracuseStep 27225233 = 20418925) B20418925
theorem B18150155 : Blo 1887435 18150155 := bstep (se 1 (by rfl) ⟨13612616, by rfl⟩ : syracuseStep 18150155 = 27225233) B27225233
theorem B12100103 : Blo 1887435 12100103 := bstep (se 1 (by rfl) ⟨9075077, by rfl⟩ : syracuseStep 12100103 = 18150155) B18150155
theorem B8066735 : Blo 1887435 8066735 := bstep (se 1 (by rfl) ⟨6050051, by rfl⟩ : syracuseStep 8066735 = 12100103) B12100103
theorem B5377823 : Blo 1887435 5377823 := bstep (se 1 (by rfl) ⟨4033367, by rfl⟩ : syracuseStep 5377823 = 8066735) B8066735
theorem B3585215 : Blo 1887435 3585215 := bstep (se 1 (by rfl) ⟨2688911, by rfl⟩ : syracuseStep 3585215 = 5377823) B5377823
theorem B2390143 : Blo 1887435 2390143 := bstep (se 1 (by rfl) ⟨1792607, by rfl⟩ : syracuseStep 2390143 = 3585215) B3585215
theorem B3186857 : Blo 1887435 3186857 := bstep (se 2 (by rfl) ⟨1195071, by rfl⟩ : syracuseStep 3186857 = 2390143) B2390143
theorem B2124571 : Blo 1887435 2124571 := bstep (se 1 (by rfl) ⟨1593428, by rfl⟩ : syracuseStep 2124571 = 3186857) B3186857
theorem B2832761 : Blo 1887435 2832761 := bstep (se 2 (by rfl) ⟨1062285, by rfl⟩ : syracuseStep 2832761 = 2124571) B2124571
theorem B1888507 : Blo 1887435 1888507 := bstep (se 1 (by rfl) ⟨1416380, by rfl⟩ : syracuseStep 1888507 = 2832761) B2832761
theorem B5104741 : Blo 1887435 5104741 := bbase (se 4 (by rfl) ⟨478569, by rfl⟩ : syracuseStep 5104741 = 957139) (by norm_num)
theorem B6806321 : Blo 1887435 6806321 := bstep (se 2 (by rfl) ⟨2552370, by rfl⟩ : syracuseStep 6806321 = 5104741) B5104741
theorem B4537547 : Blo 1887435 4537547 := bstep (se 1 (by rfl) ⟨3403160, by rfl⟩ : syracuseStep 4537547 = 6806321) B6806321
theorem B3025031 : Blo 1887435 3025031 := bstep (se 1 (by rfl) ⟨2268773, by rfl⟩ : syracuseStep 3025031 = 4537547) B4537547
theorem B32266997 : Blo 1887435 32266997 := bstep (se 5 (by rfl) ⟨1512515, by rfl⟩ : syracuseStep 32266997 = 3025031) B3025031
theorem B21511331 : Blo 1887435 21511331 := bstep (se 1 (by rfl) ⟨16133498, by rfl⟩ : syracuseStep 21511331 = 32266997) B32266997
theorem B14340887 : Blo 1887435 14340887 := bstep (se 1 (by rfl) ⟨10755665, by rfl⟩ : syracuseStep 14340887 = 21511331) B21511331
theorem B9560591 : Blo 1887435 9560591 := bstep (se 1 (by rfl) ⟨7170443, by rfl⟩ : syracuseStep 9560591 = 14340887) B14340887
theorem B6373727 : Blo 1887435 6373727 := bstep (se 1 (by rfl) ⟨4780295, by rfl⟩ : syracuseStep 6373727 = 9560591) B9560591
theorem B4249151 : Blo 1887435 4249151 := bstep (se 1 (by rfl) ⟨3186863, by rfl⟩ : syracuseStep 4249151 = 6373727) B6373727
theorem B2832767 : Blo 1887435 2832767 := bstep (se 1 (by rfl) ⟨2124575, by rfl⟩ : syracuseStep 2832767 = 4249151) B4249151
theorem B1888511 : Blo 1887435 1888511 := bstep (se 1 (by rfl) ⟨1416383, by rfl⟩ : syracuseStep 1888511 = 2832767) B2832767
theorem B2832773 : Blo 1887435 2832773 := bbase (se 4 (by rfl) ⟨265572, by rfl⟩ : syracuseStep 2832773 = 531145) (by norm_num)
theorem B1888515 : Blo 1887435 1888515 := bstep (se 1 (by rfl) ⟨1416386, by rfl⟩ : syracuseStep 1888515 = 2832773) B2832773
theorem B3186877 : Blo 1887435 3186877 := bbase (se 3 (by rfl) ⟨597539, by rfl⟩ : syracuseStep 3186877 = 1195079) (by norm_num)
theorem B4249169 : Blo 1887435 4249169 := bstep (se 2 (by rfl) ⟨1593438, by rfl⟩ : syracuseStep 4249169 = 3186877) B3186877
theorem B2832779 : Blo 1887435 2832779 := bstep (se 1 (by rfl) ⟨2124584, by rfl⟩ : syracuseStep 2832779 = 4249169) B4249169
theorem B1888519 : Blo 1887435 1888519 := bstep (se 1 (by rfl) ⟨1416389, by rfl⟩ : syracuseStep 1888519 = 2832779) B2832779
theorem B2124589 : Blo 1887435 2124589 := bbase (se 3 (by rfl) ⟨398360, by rfl⟩ : syracuseStep 2124589 = 796721) (by norm_num)
theorem B2832785 : Blo 1887435 2832785 := bstep (se 2 (by rfl) ⟨1062294, by rfl⟩ : syracuseStep 2832785 = 2124589) B2124589
theorem B1888523 : Blo 1887435 1888523 := bstep (se 1 (by rfl) ⟨1416392, by rfl⟩ : syracuseStep 1888523 = 2832785) B2832785
theorem B6373781 : Blo 1887435 6373781 := bbase (se 6 (by rfl) ⟨149385, by rfl⟩ : syracuseStep 6373781 = 298771) (by norm_num)
theorem B4249187 : Blo 1887435 4249187 := bstep (se 1 (by rfl) ⟨3186890, by rfl⟩ : syracuseStep 4249187 = 6373781) B6373781
theorem B2832791 : Blo 1887435 2832791 := bstep (se 1 (by rfl) ⟨2124593, by rfl⟩ : syracuseStep 2832791 = 4249187) B4249187
theorem B1888527 : Blo 1887435 1888527 := bstep (se 1 (by rfl) ⟨1416395, by rfl⟩ : syracuseStep 1888527 = 2832791) B2832791
theorem B2832797 : Blo 1887435 2832797 := bbase (se 3 (by rfl) ⟨531149, by rfl⟩ : syracuseStep 2832797 = 1062299) (by norm_num)
theorem B1888531 : Blo 1887435 1888531 := bstep (se 1 (by rfl) ⟨1416398, by rfl⟩ : syracuseStep 1888531 = 2832797) B2832797
theorem B4249205 : Blo 1887435 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B2832803 : Blo 1887435 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B1888535 : Blo 1887435 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B15314453 : Blo 1887435 15314453 := bbase (se 6 (by rfl) ⟨358932, by rfl⟩ : syracuseStep 15314453 = 717865) (by norm_num)
theorem B10209635 : Blo 1887435 10209635 := bstep (se 1 (by rfl) ⟨7657226, by rfl⟩ : syracuseStep 10209635 = 15314453) B15314453
theorem B6806423 : Blo 1887435 6806423 := bstep (se 1 (by rfl) ⟨5104817, by rfl⟩ : syracuseStep 6806423 = 10209635) B10209635
theorem B4537615 : Blo 1887435 4537615 := bstep (se 1 (by rfl) ⟨3403211, by rfl⟩ : syracuseStep 4537615 = 6806423) B6806423
theorem B6050153 : Blo 1887435 6050153 := bstep (se 2 (by rfl) ⟨2268807, by rfl⟩ : syracuseStep 6050153 = 4537615) B4537615
theorem B16133741 : Blo 1887435 16133741 := bstep (se 3 (by rfl) ⟨3025076, by rfl⟩ : syracuseStep 16133741 = 6050153) B6050153
theorem B10755827 : Blo 1887435 10755827 := bstep (se 1 (by rfl) ⟨8066870, by rfl⟩ : syracuseStep 10755827 = 16133741) B16133741
theorem B7170551 : Blo 1887435 7170551 := bstep (se 1 (by rfl) ⟨5377913, by rfl⟩ : syracuseStep 7170551 = 10755827) B10755827
theorem B4780367 : Blo 1887435 4780367 := bstep (se 1 (by rfl) ⟨3585275, by rfl⟩ : syracuseStep 4780367 = 7170551) B7170551
theorem B3186911 : Blo 1887435 3186911 := bstep (se 1 (by rfl) ⟨2390183, by rfl⟩ : syracuseStep 3186911 = 4780367) B4780367
theorem B2124607 : Blo 1887435 2124607 := bstep (se 1 (by rfl) ⟨1593455, by rfl⟩ : syracuseStep 2124607 = 3186911) B3186911
theorem B2832809 : Blo 1887435 2832809 := bstep (se 2 (by rfl) ⟨1062303, by rfl⟩ : syracuseStep 2832809 = 2124607) B2124607
theorem B1888539 : Blo 1887435 1888539 := bstep (se 1 (by rfl) ⟨1416404, by rfl⟩ : syracuseStep 1888539 = 2832809) B2832809
theorem B7170565 : Blo 1887435 7170565 := bbase (se 4 (by rfl) ⟨672240, by rfl⟩ : syracuseStep 7170565 = 1344481) (by norm_num)
theorem B9560753 : Blo 1887435 9560753 := bstep (se 2 (by rfl) ⟨3585282, by rfl⟩ : syracuseStep 9560753 = 7170565) B7170565
theorem B6373835 : Blo 1887435 6373835 := bstep (se 1 (by rfl) ⟨4780376, by rfl⟩ : syracuseStep 6373835 = 9560753) B9560753
theorem B4249223 : Blo 1887435 4249223 := bstep (se 1 (by rfl) ⟨3186917, by rfl⟩ : syracuseStep 4249223 = 6373835) B6373835
theorem B2832815 : Blo 1887435 2832815 := bstep (se 1 (by rfl) ⟨2124611, by rfl⟩ : syracuseStep 2832815 = 4249223) B4249223
theorem B1888543 : Blo 1887435 1888543 := bstep (se 1 (by rfl) ⟨1416407, by rfl⟩ : syracuseStep 1888543 = 2832815) B2832815
theorem B2832821 : Blo 1887435 2832821 := bbase (se 5 (by rfl) ⟨132788, by rfl⟩ : syracuseStep 2832821 = 265577) (by norm_num)
theorem B1888547 : Blo 1887435 1888547 := bstep (se 1 (by rfl) ⟨1416410, by rfl⟩ : syracuseStep 1888547 = 2832821) B2832821
theorem B4780397 : Blo 1887435 4780397 := bbase (se 3 (by rfl) ⟨896324, by rfl⟩ : syracuseStep 4780397 = 1792649) (by norm_num)
theorem B3186931 : Blo 1887435 3186931 := bstep (se 1 (by rfl) ⟨2390198, by rfl⟩ : syracuseStep 3186931 = 4780397) B4780397
theorem B4249241 : Blo 1887435 4249241 := bstep (se 2 (by rfl) ⟨1593465, by rfl⟩ : syracuseStep 4249241 = 3186931) B3186931
theorem B2832827 : Blo 1887435 2832827 := bstep (se 1 (by rfl) ⟨2124620, by rfl⟩ : syracuseStep 2832827 = 4249241) B4249241
theorem B1888551 : Blo 1887435 1888551 := bstep (se 1 (by rfl) ⟨1416413, by rfl⟩ : syracuseStep 1888551 = 2832827) B2832827
theorem B2124625 : Blo 1887435 2124625 := bbase (se 2 (by rfl) ⟨796734, by rfl⟩ : syracuseStep 2124625 = 1593469) (by norm_num)
theorem B2832833 : Blo 1887435 2832833 := bstep (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) B2124625
theorem B1888555 : Blo 1887435 1888555 := bstep (se 1 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 1888555 = 2832833) B2832833
theorem B3025109 : Blo 1887435 3025109 := bbase (se 7 (by rfl) ⟨35450, by rfl⟩ : syracuseStep 3025109 = 70901) (by norm_num)
theorem B2016739 : Blo 1887435 2016739 := bstep (se 1 (by rfl) ⟨1512554, by rfl⟩ : syracuseStep 2016739 = 3025109) B3025109
theorem B2688985 : Blo 1887435 2688985 := bstep (se 2 (by rfl) ⟨1008369, by rfl⟩ : syracuseStep 2688985 = 2016739) B2016739
theorem B3585313 : Blo 1887435 3585313 := bstep (se 2 (by rfl) ⟨1344492, by rfl⟩ : syracuseStep 3585313 = 2688985) B2688985
theorem B4780417 : Blo 1887435 4780417 := bstep (se 2 (by rfl) ⟨1792656, by rfl⟩ : syracuseStep 4780417 = 3585313) B3585313
theorem B6373889 : Blo 1887435 6373889 := bstep (se 2 (by rfl) ⟨2390208, by rfl⟩ : syracuseStep 6373889 = 4780417) B4780417
theorem B4249259 : Blo 1887435 4249259 := bstep (se 1 (by rfl) ⟨3186944, by rfl⟩ : syracuseStep 4249259 = 6373889) B6373889
theorem B2832839 : Blo 1887435 2832839 := bstep (se 1 (by rfl) ⟨2124629, by rfl⟩ : syracuseStep 2832839 = 4249259) B4249259
theorem B1888559 : Blo 1887435 1888559 := bstep (se 1 (by rfl) ⟨1416419, by rfl⟩ : syracuseStep 1888559 = 2832839) B2832839
theorem B2832845 : Blo 1887435 2832845 := bbase (se 3 (by rfl) ⟨531158, by rfl⟩ : syracuseStep 2832845 = 1062317) (by norm_num)
theorem B1888563 : Blo 1887435 1888563 := bstep (se 1 (by rfl) ⟨1416422, by rfl⟩ : syracuseStep 1888563 = 2832845) B2832845
theorem B4249277 : Blo 1887435 4249277 := bbase (se 3 (by rfl) ⟨796739, by rfl⟩ : syracuseStep 4249277 = 1593479) (by norm_num)
theorem B2832851 : Blo 1887435 2832851 := bstep (se 1 (by rfl) ⟨2124638, by rfl⟩ : syracuseStep 2832851 = 4249277) B4249277
theorem B1888567 : Blo 1887435 1888567 := bstep (se 1 (by rfl) ⟨1416425, by rfl⟩ : syracuseStep 1888567 = 2832851) B2832851
theorem B3186965 : Blo 1887435 3186965 := bbase (se 6 (by rfl) ⟨74694, by rfl⟩ : syracuseStep 3186965 = 149389) (by norm_num)
theorem B2124643 : Blo 1887435 2124643 := bstep (se 1 (by rfl) ⟨1593482, by rfl⟩ : syracuseStep 2124643 = 3186965) B3186965
theorem B2832857 : Blo 1887435 2832857 := bstep (se 2 (by rfl) ⟨1062321, by rfl⟩ : syracuseStep 2832857 = 2124643) B2124643
theorem B1888571 : Blo 1887435 1888571 := bstep (se 1 (by rfl) ⟨1416428, by rfl⟩ : syracuseStep 1888571 = 2832857) B2832857
theorem B15314741 : Blo 1887435 15314741 := bbase (se 5 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 15314741 = 1435757) (by norm_num)
theorem B10209827 : Blo 1887435 10209827 := bstep (se 1 (by rfl) ⟨7657370, by rfl⟩ : syracuseStep 10209827 = 15314741) B15314741
theorem B27226205 : Blo 1887435 27226205 := bstep (se 3 (by rfl) ⟨5104913, by rfl⟩ : syracuseStep 27226205 = 10209827) B10209827
theorem B18150803 : Blo 1887435 18150803 := bstep (se 1 (by rfl) ⟨13613102, by rfl⟩ : syracuseStep 18150803 = 27226205) B27226205
theorem B12100535 : Blo 1887435 12100535 := bstep (se 1 (by rfl) ⟨9075401, by rfl⟩ : syracuseStep 12100535 = 18150803) B18150803
theorem B8067023 : Blo 1887435 8067023 := bstep (se 1 (by rfl) ⟨6050267, by rfl⟩ : syracuseStep 8067023 = 12100535) B12100535
theorem B5378015 : Blo 1887435 5378015 := bstep (se 1 (by rfl) ⟨4033511, by rfl⟩ : syracuseStep 5378015 = 8067023) B8067023
theorem B14341373 : Blo 1887435 14341373 := bstep (se 3 (by rfl) ⟨2689007, by rfl⟩ : syracuseStep 14341373 = 5378015) B5378015
theorem B9560915 : Blo 1887435 9560915 := bstep (se 1 (by rfl) ⟨7170686, by rfl⟩ : syracuseStep 9560915 = 14341373) B14341373
theorem B6373943 : Blo 1887435 6373943 := bstep (se 1 (by rfl) ⟨4780457, by rfl⟩ : syracuseStep 6373943 = 9560915) B9560915
theorem B4249295 : Blo 1887435 4249295 := bstep (se 1 (by rfl) ⟨3186971, by rfl⟩ : syracuseStep 4249295 = 6373943) B6373943
theorem B2832863 : Blo 1887435 2832863 := bstep (se 1 (by rfl) ⟨2124647, by rfl⟩ : syracuseStep 2832863 = 4249295) B4249295
theorem B1888575 : Blo 1887435 1888575 := bstep (se 1 (by rfl) ⟨1416431, by rfl⟩ : syracuseStep 1888575 = 2832863) B2832863
theorem B2832869 : Blo 1887435 2832869 := bbase (se 4 (by rfl) ⟨265581, by rfl⟩ : syracuseStep 2832869 = 531163) (by norm_num)
theorem B1888579 : Blo 1887435 1888579 := bstep (se 1 (by rfl) ⟨1416434, by rfl⟩ : syracuseStep 1888579 = 2832869) B2832869
theorem B8177125 : Blo 1887435 8177125 := bbase (se 4 (by rfl) ⟨766605, by rfl⟩ : syracuseStep 8177125 = 1533211) (by norm_num)
theorem B10902833 : Blo 1887435 10902833 := bstep (se 2 (by rfl) ⟨4088562, by rfl⟩ : syracuseStep 10902833 = 8177125) B8177125
theorem B7268555 : Blo 1887435 7268555 := bstep (se 1 (by rfl) ⟨5451416, by rfl⟩ : syracuseStep 7268555 = 10902833) B10902833
theorem B19382813 : Blo 1887435 19382813 := bstep (se 3 (by rfl) ⟨3634277, by rfl⟩ : syracuseStep 19382813 = 7268555) B7268555
theorem B12921875 : Blo 1887435 12921875 := bstep (se 1 (by rfl) ⟨9691406, by rfl⟩ : syracuseStep 12921875 = 19382813) B19382813
theorem B8614583 : Blo 1887435 8614583 := bstep (se 1 (by rfl) ⟨6460937, by rfl⟩ : syracuseStep 8614583 = 12921875) B12921875
theorem B5743055 : Blo 1887435 5743055 := bstep (se 1 (by rfl) ⟨4307291, by rfl⟩ : syracuseStep 5743055 = 8614583) B8614583
theorem B3828703 : Blo 1887435 3828703 := bstep (se 1 (by rfl) ⟨2871527, by rfl⟩ : syracuseStep 3828703 = 5743055) B5743055
theorem B5104937 : Blo 1887435 5104937 := bstep (se 2 (by rfl) ⟨1914351, by rfl⟩ : syracuseStep 5104937 = 3828703) B3828703
theorem B3403291 : Blo 1887435 3403291 := bstep (se 1 (by rfl) ⟨2552468, by rfl⟩ : syracuseStep 3403291 = 5104937) B5104937
theorem B4537721 : Blo 1887435 4537721 := bstep (se 2 (by rfl) ⟨1701645, by rfl⟩ : syracuseStep 4537721 = 3403291) B3403291
theorem B12100589 : Blo 1887435 12100589 := bstep (se 3 (by rfl) ⟨2268860, by rfl⟩ : syracuseStep 12100589 = 4537721) B4537721
theorem B8067059 : Blo 1887435 8067059 := bstep (se 1 (by rfl) ⟨6050294, by rfl⟩ : syracuseStep 8067059 = 12100589) B12100589
theorem B5378039 : Blo 1887435 5378039 := bstep (se 1 (by rfl) ⟨4033529, by rfl⟩ : syracuseStep 5378039 = 8067059) B8067059
theorem B3585359 : Blo 1887435 3585359 := bstep (se 1 (by rfl) ⟨2689019, by rfl⟩ : syracuseStep 3585359 = 5378039) B5378039
theorem B2390239 : Blo 1887435 2390239 := bstep (se 1 (by rfl) ⟨1792679, by rfl⟩ : syracuseStep 2390239 = 3585359) B3585359
theorem B3186985 : Blo 1887435 3186985 := bstep (se 2 (by rfl) ⟨1195119, by rfl⟩ : syracuseStep 3186985 = 2390239) B2390239
theorem B4249313 : Blo 1887435 4249313 := bstep (se 2 (by rfl) ⟨1593492, by rfl⟩ : syracuseStep 4249313 = 3186985) B3186985
theorem B2832875 : Blo 1887435 2832875 := bstep (se 1 (by rfl) ⟨2124656, by rfl⟩ : syracuseStep 2832875 = 4249313) B4249313
theorem B1888583 : Blo 1887435 1888583 := bstep (se 1 (by rfl) ⟨1416437, by rfl⟩ : syracuseStep 1888583 = 2832875) B2832875
theorem B2124661 : Blo 1887435 2124661 := bbase (se 5 (by rfl) ⟨99593, by rfl⟩ : syracuseStep 2124661 = 199187) (by norm_num)
theorem B2832881 : Blo 1887435 2832881 := bstep (se 2 (by rfl) ⟨1062330, by rfl⟩ : syracuseStep 2832881 = 2124661) B2124661
theorem B1888587 : Blo 1887435 1888587 := bstep (se 1 (by rfl) ⟨1416440, by rfl⟩ : syracuseStep 1888587 = 2832881) B2832881
theorem B2390249 : Blo 1887435 2390249 := bbase (se 2 (by rfl) ⟨896343, by rfl⟩ : syracuseStep 2390249 = 1792687) (by norm_num)
theorem B6373997 : Blo 1887435 6373997 := bstep (se 3 (by rfl) ⟨1195124, by rfl⟩ : syracuseStep 6373997 = 2390249) B2390249
theorem B4249331 : Blo 1887435 4249331 := bstep (se 1 (by rfl) ⟨3186998, by rfl⟩ : syracuseStep 4249331 = 6373997) B6373997
theorem B2832887 : Blo 1887435 2832887 := bstep (se 1 (by rfl) ⟨2124665, by rfl⟩ : syracuseStep 2832887 = 4249331) B4249331
theorem B1888591 : Blo 1887435 1888591 := bstep (se 1 (by rfl) ⟨1416443, by rfl⟩ : syracuseStep 1888591 = 2832887) B2832887
theorem B2832893 : Blo 1887435 2832893 := bbase (se 3 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 2832893 = 1062335) (by norm_num)
theorem B1888595 : Blo 1887435 1888595 := bstep (se 1 (by rfl) ⟨1416446, by rfl⟩ : syracuseStep 1888595 = 2832893) B2832893
theorem B4249349 : Blo 1887435 4249349 := bbase (se 4 (by rfl) ⟨398376, by rfl⟩ : syracuseStep 4249349 = 796753) (by norm_num)
theorem B2832899 : Blo 1887435 2832899 := bstep (se 1 (by rfl) ⟨2124674, by rfl⟩ : syracuseStep 2832899 = 4249349) B4249349
theorem B1888599 : Blo 1887435 1888599 := bstep (se 1 (by rfl) ⟨1416449, by rfl⟩ : syracuseStep 1888599 = 2832899) B2832899
theorem B3585397 : Blo 1887435 3585397 := bbase (se 5 (by rfl) ⟨168065, by rfl⟩ : syracuseStep 3585397 = 336131) (by norm_num)
theorem B4780529 : Blo 1887435 4780529 := bstep (se 2 (by rfl) ⟨1792698, by rfl⟩ : syracuseStep 4780529 = 3585397) B3585397
theorem B3187019 : Blo 1887435 3187019 := bstep (se 1 (by rfl) ⟨2390264, by rfl⟩ : syracuseStep 3187019 = 4780529) B4780529
theorem B2124679 : Blo 1887435 2124679 := bstep (se 1 (by rfl) ⟨1593509, by rfl⟩ : syracuseStep 2124679 = 3187019) B3187019
theorem B2832905 : Blo 1887435 2832905 := bstep (se 2 (by rfl) ⟨1062339, by rfl⟩ : syracuseStep 2832905 = 2124679) B2124679
theorem B1888603 : Blo 1887435 1888603 := bstep (se 1 (by rfl) ⟨1416452, by rfl⟩ : syracuseStep 1888603 = 2832905) B2832905
theorem B9561077 : Blo 1887435 9561077 := bbase (se 5 (by rfl) ⟨448175, by rfl⟩ : syracuseStep 9561077 = 896351) (by norm_num)
theorem B6374051 : Blo 1887435 6374051 := bstep (se 1 (by rfl) ⟨4780538, by rfl⟩ : syracuseStep 6374051 = 9561077) B9561077
theorem B4249367 : Blo 1887435 4249367 := bstep (se 1 (by rfl) ⟨3187025, by rfl⟩ : syracuseStep 4249367 = 6374051) B6374051
theorem B2832911 : Blo 1887435 2832911 := bstep (se 1 (by rfl) ⟨2124683, by rfl⟩ : syracuseStep 2832911 = 4249367) B4249367
theorem B1888607 : Blo 1887435 1888607 := bstep (se 1 (by rfl) ⟨1416455, by rfl⟩ : syracuseStep 1888607 = 2832911) B2832911
theorem B2832917 : Blo 1887435 2832917 := bbase (se 6 (by rfl) ⟨66396, by rfl⟩ : syracuseStep 2832917 = 132793) (by norm_num)
theorem B1888611 : Blo 1887435 1888611 := bstep (se 1 (by rfl) ⟨1416458, by rfl⟩ : syracuseStep 1888611 = 2832917) B2832917
theorem B16134389 : Blo 1887435 16134389 := bbase (se 5 (by rfl) ⟨756299, by rfl⟩ : syracuseStep 16134389 = 1512599) (by norm_num)
theorem B10756259 : Blo 1887435 10756259 := bstep (se 1 (by rfl) ⟨8067194, by rfl⟩ : syracuseStep 10756259 = 16134389) B16134389
theorem B7170839 : Blo 1887435 7170839 := bstep (se 1 (by rfl) ⟨5378129, by rfl⟩ : syracuseStep 7170839 = 10756259) B10756259
theorem B4780559 : Blo 1887435 4780559 := bstep (se 1 (by rfl) ⟨3585419, by rfl⟩ : syracuseStep 4780559 = 7170839) B7170839
theorem B3187039 : Blo 1887435 3187039 := bstep (se 1 (by rfl) ⟨2390279, by rfl⟩ : syracuseStep 3187039 = 4780559) B4780559
theorem B4249385 : Blo 1887435 4249385 := bstep (se 2 (by rfl) ⟨1593519, by rfl⟩ : syracuseStep 4249385 = 3187039) B3187039
theorem B2832923 : Blo 1887435 2832923 := bstep (se 1 (by rfl) ⟨2124692, by rfl⟩ : syracuseStep 2832923 = 4249385) B4249385
theorem B1888615 : Blo 1887435 1888615 := bstep (se 1 (by rfl) ⟨1416461, by rfl⟩ : syracuseStep 1888615 = 2832923) B2832923
theorem B2124697 : Blo 1887435 2124697 := bbase (se 2 (by rfl) ⟨796761, by rfl⟩ : syracuseStep 2124697 = 1593523) (by norm_num)
theorem B2832929 : Blo 1887435 2832929 := bstep (se 2 (by rfl) ⟨1062348, by rfl⟩ : syracuseStep 2832929 = 2124697) B2124697
theorem B1888619 : Blo 1887435 1888619 := bstep (se 1 (by rfl) ⟨1416464, by rfl⟩ : syracuseStep 1888619 = 2832929) B2832929
theorem B7170869 : Blo 1887435 7170869 := bbase (se 5 (by rfl) ⟨336134, by rfl⟩ : syracuseStep 7170869 = 672269) (by norm_num)
theorem B4780579 : Blo 1887435 4780579 := bstep (se 1 (by rfl) ⟨3585434, by rfl⟩ : syracuseStep 4780579 = 7170869) B7170869
theorem B6374105 : Blo 1887435 6374105 := bstep (se 2 (by rfl) ⟨2390289, by rfl⟩ : syracuseStep 6374105 = 4780579) B4780579
theorem B4249403 : Blo 1887435 4249403 := bstep (se 1 (by rfl) ⟨3187052, by rfl⟩ : syracuseStep 4249403 = 6374105) B6374105
theorem B2832935 : Blo 1887435 2832935 := bstep (se 1 (by rfl) ⟨2124701, by rfl⟩ : syracuseStep 2832935 = 4249403) B4249403
theorem B1888623 : Blo 1887435 1888623 := bstep (se 1 (by rfl) ⟨1416467, by rfl⟩ : syracuseStep 1888623 = 2832935) B2832935
theorem B2832941 : Blo 1887435 2832941 := bbase (se 3 (by rfl) ⟨531176, by rfl⟩ : syracuseStep 2832941 = 1062353) (by norm_num)
theorem B1888627 : Blo 1887435 1888627 := bstep (se 1 (by rfl) ⟨1416470, by rfl⟩ : syracuseStep 1888627 = 2832941) B2832941
theorem B4249421 : Blo 1887435 4249421 := bbase (se 3 (by rfl) ⟨796766, by rfl⟩ : syracuseStep 4249421 = 1593533) (by norm_num)
theorem B2832947 : Blo 1887435 2832947 := bstep (se 1 (by rfl) ⟨2124710, by rfl⟩ : syracuseStep 2832947 = 4249421) B4249421
theorem B1888631 : Blo 1887435 1888631 := bstep (se 1 (by rfl) ⟨1416473, by rfl⟩ : syracuseStep 1888631 = 2832947) B2832947
theorem B2390305 : Blo 1887435 2390305 := bbase (se 2 (by rfl) ⟨896364, by rfl⟩ : syracuseStep 2390305 = 1792729) (by norm_num)
theorem B3187073 : Blo 1887435 3187073 := bstep (se 2 (by rfl) ⟨1195152, by rfl⟩ : syracuseStep 3187073 = 2390305) B2390305
theorem B2124715 : Blo 1887435 2124715 := bstep (se 1 (by rfl) ⟨1593536, by rfl⟩ : syracuseStep 2124715 = 3187073) B3187073
theorem B2832953 : Blo 1887435 2832953 := bstep (se 2 (by rfl) ⟨1062357, by rfl⟩ : syracuseStep 2832953 = 2124715) B2124715
theorem B1888635 : Blo 1887435 1888635 := bstep (se 1 (by rfl) ⟨1416476, by rfl⟩ : syracuseStep 1888635 = 2832953) B2832953
theorem B21512789 : Blo 1887435 21512789 := bbase (se 8 (by rfl) ⟨126051, by rfl⟩ : syracuseStep 21512789 = 252103) (by norm_num)
theorem B14341859 : Blo 1887435 14341859 := bstep (se 1 (by rfl) ⟨10756394, by rfl⟩ : syracuseStep 14341859 = 21512789) B21512789
theorem B9561239 : Blo 1887435 9561239 := bstep (se 1 (by rfl) ⟨7170929, by rfl⟩ : syracuseStep 9561239 = 14341859) B14341859
theorem B6374159 : Blo 1887435 6374159 := bstep (se 1 (by rfl) ⟨4780619, by rfl⟩ : syracuseStep 6374159 = 9561239) B9561239
theorem B4249439 : Blo 1887435 4249439 := bstep (se 1 (by rfl) ⟨3187079, by rfl⟩ : syracuseStep 4249439 = 6374159) B6374159
theorem B2832959 : Blo 1887435 2832959 := bstep (se 1 (by rfl) ⟨2124719, by rfl⟩ : syracuseStep 2832959 = 4249439) B4249439
theorem B1888639 : Blo 1887435 1888639 := bstep (se 1 (by rfl) ⟨1416479, by rfl⟩ : syracuseStep 1888639 = 2832959) B2832959
theorem B2832965 : Blo 1887435 2832965 := bbase (se 4 (by rfl) ⟨265590, by rfl⟩ : syracuseStep 2832965 = 531181) (by norm_num)
theorem B1888643 : Blo 1887435 1888643 := bstep (se 1 (by rfl) ⟨1416482, by rfl⟩ : syracuseStep 1888643 = 2832965) B2832965
theorem B3187093 : Blo 1887435 3187093 := bbase (se 6 (by rfl) ⟨74697, by rfl⟩ : syracuseStep 3187093 = 149395) (by norm_num)
theorem B4249457 : Blo 1887435 4249457 := bstep (se 2 (by rfl) ⟨1593546, by rfl⟩ : syracuseStep 4249457 = 3187093) B3187093
theorem B2832971 : Blo 1887435 2832971 := bstep (se 1 (by rfl) ⟨2124728, by rfl⟩ : syracuseStep 2832971 = 4249457) B4249457
theorem B1888647 : Blo 1887435 1888647 := bstep (se 1 (by rfl) ⟨1416485, by rfl⟩ : syracuseStep 1888647 = 2832971) B2832971
theorem B2124733 : Blo 1887435 2124733 := bbase (se 3 (by rfl) ⟨398387, by rfl⟩ : syracuseStep 2124733 = 796775) (by norm_num)
theorem B2832977 : Blo 1887435 2832977 := bstep (se 2 (by rfl) ⟨1062366, by rfl⟩ : syracuseStep 2832977 = 2124733) B2124733
theorem B1888651 : Blo 1887435 1888651 := bstep (se 1 (by rfl) ⟨1416488, by rfl⟩ : syracuseStep 1888651 = 2832977) B2832977
theorem B6374213 : Blo 1887435 6374213 := bbase (se 4 (by rfl) ⟨597582, by rfl⟩ : syracuseStep 6374213 = 1195165) (by norm_num)
theorem B4249475 : Blo 1887435 4249475 := bstep (se 1 (by rfl) ⟨3187106, by rfl⟩ : syracuseStep 4249475 = 6374213) B6374213
theorem B2832983 : Blo 1887435 2832983 := bstep (se 1 (by rfl) ⟨2124737, by rfl⟩ : syracuseStep 2832983 = 4249475) B4249475
theorem B1888655 : Blo 1887435 1888655 := bstep (se 1 (by rfl) ⟨1416491, by rfl⟩ : syracuseStep 1888655 = 2832983) B2832983
theorem B2832989 : Blo 1887435 2832989 := bbase (se 3 (by rfl) ⟨531185, by rfl⟩ : syracuseStep 2832989 = 1062371) (by norm_num)
theorem B1888659 : Blo 1887435 1888659 := bstep (se 1 (by rfl) ⟨1416494, by rfl⟩ : syracuseStep 1888659 = 2832989) B2832989
theorem B4249493 : Blo 1887435 4249493 := bbase (se 6 (by rfl) ⟨99597, by rfl⟩ : syracuseStep 4249493 = 199195) (by norm_num)
theorem B2832995 : Blo 1887435 2832995 := bstep (se 1 (by rfl) ⟨2124746, by rfl⟩ : syracuseStep 2832995 = 4249493) B4249493
theorem B1888663 : Blo 1887435 1888663 := bstep (se 1 (by rfl) ⟨1416497, by rfl⟩ : syracuseStep 1888663 = 2832995) B2832995
theorem B4033709 : Blo 1887435 4033709 := bbase (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) (by norm_num)
theorem B2689139 : Blo 1887435 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B7171037 : Blo 1887435 7171037 := bstep (se 3 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 7171037 = 2689139) B2689139
theorem B4780691 : Blo 1887435 4780691 := bstep (se 1 (by rfl) ⟨3585518, by rfl⟩ : syracuseStep 4780691 = 7171037) B7171037
theorem B3187127 : Blo 1887435 3187127 := bstep (se 1 (by rfl) ⟨2390345, by rfl⟩ : syracuseStep 3187127 = 4780691) B4780691
theorem B2124751 : Blo 1887435 2124751 := bstep (se 1 (by rfl) ⟨1593563, by rfl⟩ : syracuseStep 2124751 = 3187127) B3187127
theorem B2833001 : Blo 1887435 2833001 := bstep (se 2 (by rfl) ⟨1062375, by rfl⟩ : syracuseStep 2833001 = 2124751) B2124751
theorem B1888667 : Blo 1887435 1888667 := bstep (se 1 (by rfl) ⟨1416500, by rfl⟩ : syracuseStep 1888667 = 2833001) B2833001
theorem B20420693 : Blo 1887435 20420693 := bbase (se 8 (by rfl) ⟨119652, by rfl⟩ : syracuseStep 20420693 = 239305) (by norm_num)
theorem B13613795 : Blo 1887435 13613795 := bstep (se 1 (by rfl) ⟨10210346, by rfl⟩ : syracuseStep 13613795 = 20420693) B20420693
theorem B9075863 : Blo 1887435 9075863 := bstep (se 1 (by rfl) ⟨6806897, by rfl⟩ : syracuseStep 9075863 = 13613795) B13613795
theorem B6050575 : Blo 1887435 6050575 := bstep (se 1 (by rfl) ⟨4537931, by rfl⟩ : syracuseStep 6050575 = 9075863) B9075863
theorem B8067433 : Blo 1887435 8067433 := bstep (se 2 (by rfl) ⟨3025287, by rfl⟩ : syracuseStep 8067433 = 6050575) B6050575
theorem B10756577 : Blo 1887435 10756577 := bstep (se 2 (by rfl) ⟨4033716, by rfl⟩ : syracuseStep 10756577 = 8067433) B8067433
theorem B7171051 : Blo 1887435 7171051 := bstep (se 1 (by rfl) ⟨5378288, by rfl⟩ : syracuseStep 7171051 = 10756577) B10756577
theorem B9561401 : Blo 1887435 9561401 := bstep (se 2 (by rfl) ⟨3585525, by rfl⟩ : syracuseStep 9561401 = 7171051) B7171051
theorem B6374267 : Blo 1887435 6374267 := bstep (se 1 (by rfl) ⟨4780700, by rfl⟩ : syracuseStep 6374267 = 9561401) B9561401
theorem B4249511 : Blo 1887435 4249511 := bstep (se 1 (by rfl) ⟨3187133, by rfl⟩ : syracuseStep 4249511 = 6374267) B6374267
theorem B2833007 : Blo 1887435 2833007 := bstep (se 1 (by rfl) ⟨2124755, by rfl⟩ : syracuseStep 2833007 = 4249511) B4249511
theorem B1888671 : Blo 1887435 1888671 := bstep (se 1 (by rfl) ⟨1416503, by rfl⟩ : syracuseStep 1888671 = 2833007) B2833007
theorem B2833013 : Blo 1887435 2833013 := bbase (se 5 (by rfl) ⟨132797, by rfl⟩ : syracuseStep 2833013 = 265595) (by norm_num)
theorem B1888675 : Blo 1887435 1888675 := bstep (se 1 (by rfl) ⟨1416506, by rfl⟩ : syracuseStep 1888675 = 2833013) B2833013
theorem B3585541 : Blo 1887435 3585541 := bbase (se 4 (by rfl) ⟨336144, by rfl⟩ : syracuseStep 3585541 = 672289) (by norm_num)
theorem B4780721 : Blo 1887435 4780721 := bstep (se 2 (by rfl) ⟨1792770, by rfl⟩ : syracuseStep 4780721 = 3585541) B3585541
theorem B3187147 : Blo 1887435 3187147 := bstep (se 1 (by rfl) ⟨2390360, by rfl⟩ : syracuseStep 3187147 = 4780721) B4780721
theorem B4249529 : Blo 1887435 4249529 := bstep (se 2 (by rfl) ⟨1593573, by rfl⟩ : syracuseStep 4249529 = 3187147) B3187147
theorem B2833019 : Blo 1887435 2833019 := bstep (se 1 (by rfl) ⟨2124764, by rfl⟩ : syracuseStep 2833019 = 4249529) B4249529
theorem B1888679 : Blo 1887435 1888679 := bstep (se 1 (by rfl) ⟨1416509, by rfl⟩ : syracuseStep 1888679 = 2833019) B2833019
theorem B2124769 : Blo 1887435 2124769 := bbase (se 2 (by rfl) ⟨796788, by rfl⟩ : syracuseStep 2124769 = 1593577) (by norm_num)
theorem B2833025 : Blo 1887435 2833025 := bstep (se 2 (by rfl) ⟨1062384, by rfl⟩ : syracuseStep 2833025 = 2124769) B2124769
theorem B1888683 : Blo 1887435 1888683 := bstep (se 1 (by rfl) ⟨1416512, by rfl⟩ : syracuseStep 1888683 = 2833025) B2833025
theorem B4780741 : Blo 1887435 4780741 := bbase (se 4 (by rfl) ⟨448194, by rfl⟩ : syracuseStep 4780741 = 896389) (by norm_num)
theorem B6374321 : Blo 1887435 6374321 := bstep (se 2 (by rfl) ⟨2390370, by rfl⟩ : syracuseStep 6374321 = 4780741) B4780741
theorem B4249547 : Blo 1887435 4249547 := bstep (se 1 (by rfl) ⟨3187160, by rfl⟩ : syracuseStep 4249547 = 6374321) B6374321
theorem B2833031 : Blo 1887435 2833031 := bstep (se 1 (by rfl) ⟨2124773, by rfl⟩ : syracuseStep 2833031 = 4249547) B4249547
theorem B1888687 : Blo 1887435 1888687 := bstep (se 1 (by rfl) ⟨1416515, by rfl⟩ : syracuseStep 1888687 = 2833031) B2833031
theorem B2833037 : Blo 1887435 2833037 := bbase (se 3 (by rfl) ⟨531194, by rfl⟩ : syracuseStep 2833037 = 1062389) (by norm_num)
theorem B1888691 : Blo 1887435 1888691 := bstep (se 1 (by rfl) ⟨1416518, by rfl⟩ : syracuseStep 1888691 = 2833037) B2833037
theorem B4249565 : Blo 1887435 4249565 := bbase (se 3 (by rfl) ⟨796793, by rfl⟩ : syracuseStep 4249565 = 1593587) (by norm_num)
theorem B2833043 : Blo 1887435 2833043 := bstep (se 1 (by rfl) ⟨2124782, by rfl⟩ : syracuseStep 2833043 = 4249565) B4249565
theorem B1888695 : Blo 1887435 1888695 := bstep (se 1 (by rfl) ⟨1416521, by rfl⟩ : syracuseStep 1888695 = 2833043) B2833043
theorem B3187181 : Blo 1887435 3187181 := bbase (se 3 (by rfl) ⟨597596, by rfl⟩ : syracuseStep 3187181 = 1195193) (by norm_num)
theorem B2124787 : Blo 1887435 2124787 := bstep (se 1 (by rfl) ⟨1593590, by rfl⟩ : syracuseStep 2124787 = 3187181) B3187181
theorem B2833049 : Blo 1887435 2833049 := bstep (se 2 (by rfl) ⟨1062393, by rfl⟩ : syracuseStep 2833049 = 2124787) B2124787
theorem B1888699 : Blo 1887435 1888699 := bstep (se 1 (by rfl) ⟨1416524, by rfl⟩ : syracuseStep 1888699 = 2833049) B2833049
theorem B24202709 : Blo 1887435 24202709 := bbase (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) (by norm_num)
theorem B16135139 : Blo 1887435 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B10756759 : Blo 1887435 10756759 := bstep (se 1 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 10756759 = 16135139) B16135139
theorem B14342345 : Blo 1887435 14342345 := bstep (se 2 (by rfl) ⟨5378379, by rfl⟩ : syracuseStep 14342345 = 10756759) B10756759
theorem B9561563 : Blo 1887435 9561563 := bstep (se 1 (by rfl) ⟨7171172, by rfl⟩ : syracuseStep 9561563 = 14342345) B14342345
theorem B6374375 : Blo 1887435 6374375 := bstep (se 1 (by rfl) ⟨4780781, by rfl⟩ : syracuseStep 6374375 = 9561563) B9561563
theorem B4249583 : Blo 1887435 4249583 := bstep (se 1 (by rfl) ⟨3187187, by rfl⟩ : syracuseStep 4249583 = 6374375) B6374375
theorem B2833055 : Blo 1887435 2833055 := bstep (se 1 (by rfl) ⟨2124791, by rfl⟩ : syracuseStep 2833055 = 4249583) B4249583
theorem B1888703 : Blo 1887435 1888703 := bstep (se 1 (by rfl) ⟨1416527, by rfl⟩ : syracuseStep 1888703 = 2833055) B2833055
theorem B2833061 : Blo 1887435 2833061 := bbase (se 4 (by rfl) ⟨265599, by rfl⟩ : syracuseStep 2833061 = 531199) (by norm_num)
theorem B1888707 : Blo 1887435 1888707 := bstep (se 1 (by rfl) ⟨1416530, by rfl⟩ : syracuseStep 1888707 = 2833061) B2833061
theorem B2390401 : Blo 1887435 2390401 := bbase (se 2 (by rfl) ⟨896400, by rfl⟩ : syracuseStep 2390401 = 1792801) (by norm_num)
theorem B3187201 : Blo 1887435 3187201 := bstep (se 2 (by rfl) ⟨1195200, by rfl⟩ : syracuseStep 3187201 = 2390401) B2390401
theorem B4249601 : Blo 1887435 4249601 := bstep (se 2 (by rfl) ⟨1593600, by rfl⟩ : syracuseStep 4249601 = 3187201) B3187201
theorem B2833067 : Blo 1887435 2833067 := bstep (se 1 (by rfl) ⟨2124800, by rfl⟩ : syracuseStep 2833067 = 4249601) B4249601
theorem B1888711 : Blo 1887435 1888711 := bstep (se 1 (by rfl) ⟨1416533, by rfl⟩ : syracuseStep 1888711 = 2833067) B2833067
theorem B2124805 : Blo 1887435 2124805 := bbase (se 4 (by rfl) ⟨199200, by rfl⟩ : syracuseStep 2124805 = 398401) (by norm_num)
theorem B2833073 : Blo 1887435 2833073 := bstep (se 2 (by rfl) ⟨1062402, by rfl⟩ : syracuseStep 2833073 = 2124805) B2124805
theorem B1888715 : Blo 1887435 1888715 := bstep (se 1 (by rfl) ⟨1416536, by rfl⟩ : syracuseStep 1888715 = 2833073) B2833073
theorem B2689213 : Blo 1887435 2689213 := bbase (se 3 (by rfl) ⟨504227, by rfl⟩ : syracuseStep 2689213 = 1008455) (by norm_num)
theorem B3585617 : Blo 1887435 3585617 := bstep (se 2 (by rfl) ⟨1344606, by rfl⟩ : syracuseStep 3585617 = 2689213) B2689213
theorem B2390411 : Blo 1887435 2390411 := bstep (se 1 (by rfl) ⟨1792808, by rfl⟩ : syracuseStep 2390411 = 3585617) B3585617
theorem B6374429 : Blo 1887435 6374429 := bstep (se 3 (by rfl) ⟨1195205, by rfl⟩ : syracuseStep 6374429 = 2390411) B2390411
theorem B4249619 : Blo 1887435 4249619 := bstep (se 1 (by rfl) ⟨3187214, by rfl⟩ : syracuseStep 4249619 = 6374429) B6374429
theorem B2833079 : Blo 1887435 2833079 := bstep (se 1 (by rfl) ⟨2124809, by rfl⟩ : syracuseStep 2833079 = 4249619) B4249619
theorem B1888719 : Blo 1887435 1888719 := bstep (se 1 (by rfl) ⟨1416539, by rfl⟩ : syracuseStep 1888719 = 2833079) B2833079
theorem B2833085 : Blo 1887435 2833085 := bbase (se 3 (by rfl) ⟨531203, by rfl⟩ : syracuseStep 2833085 = 1062407) (by norm_num)
theorem B1888723 : Blo 1887435 1888723 := bstep (se 1 (by rfl) ⟨1416542, by rfl⟩ : syracuseStep 1888723 = 2833085) B2833085
theorem B4249637 : Blo 1887435 4249637 := bbase (se 4 (by rfl) ⟨398403, by rfl⟩ : syracuseStep 4249637 = 796807) (by norm_num)
theorem B2833091 : Blo 1887435 2833091 := bstep (se 1 (by rfl) ⟨2124818, by rfl⟩ : syracuseStep 2833091 = 4249637) B4249637
theorem B1888727 : Blo 1887435 1888727 := bstep (se 1 (by rfl) ⟨1416545, by rfl⟩ : syracuseStep 1888727 = 2833091) B2833091
theorem B4780853 : Blo 1887435 4780853 := bbase (se 5 (by rfl) ⟨224102, by rfl⟩ : syracuseStep 4780853 = 448205) (by norm_num)
theorem B3187235 : Blo 1887435 3187235 := bstep (se 1 (by rfl) ⟨2390426, by rfl⟩ : syracuseStep 3187235 = 4780853) B4780853
theorem B2124823 : Blo 1887435 2124823 := bstep (se 1 (by rfl) ⟨1593617, by rfl⟩ : syracuseStep 2124823 = 3187235) B3187235
theorem B2833097 : Blo 1887435 2833097 := bstep (se 2 (by rfl) ⟨1062411, by rfl⟩ : syracuseStep 2833097 = 2124823) B2124823
theorem B1888731 : Blo 1887435 1888731 := bstep (se 1 (by rfl) ⟨1416548, by rfl⟩ : syracuseStep 1888731 = 2833097) B2833097
theorem B1914505 : Blo 1887435 1914505 := bbase (se 2 (by rfl) ⟨717939, by rfl⟩ : syracuseStep 1914505 = 1435879) (by norm_num)
theorem B10210693 : Blo 1887435 10210693 := bstep (se 4 (by rfl) ⟨957252, by rfl⟩ : syracuseStep 10210693 = 1914505) B1914505
theorem B13614257 : Blo 1887435 13614257 := bstep (se 2 (by rfl) ⟨5105346, by rfl⟩ : syracuseStep 13614257 = 10210693) B10210693
theorem B9076171 : Blo 1887435 9076171 := bstep (se 1 (by rfl) ⟨6807128, by rfl⟩ : syracuseStep 9076171 = 13614257) B13614257
theorem B12101561 : Blo 1887435 12101561 := bstep (se 2 (by rfl) ⟨4538085, by rfl⟩ : syracuseStep 12101561 = 9076171) B9076171
theorem B8067707 : Blo 1887435 8067707 := bstep (se 1 (by rfl) ⟨6050780, by rfl⟩ : syracuseStep 8067707 = 12101561) B12101561
theorem B5378471 : Blo 1887435 5378471 := bstep (se 1 (by rfl) ⟨4033853, by rfl⟩ : syracuseStep 5378471 = 8067707) B8067707
theorem B3585647 : Blo 1887435 3585647 := bstep (se 1 (by rfl) ⟨2689235, by rfl⟩ : syracuseStep 3585647 = 5378471) B5378471
theorem B9561725 : Blo 1887435 9561725 := bstep (se 3 (by rfl) ⟨1792823, by rfl⟩ : syracuseStep 9561725 = 3585647) B3585647
theorem B6374483 : Blo 1887435 6374483 := bstep (se 1 (by rfl) ⟨4780862, by rfl⟩ : syracuseStep 6374483 = 9561725) B9561725
theorem B4249655 : Blo 1887435 4249655 := bstep (se 1 (by rfl) ⟨3187241, by rfl⟩ : syracuseStep 4249655 = 6374483) B6374483
theorem B2833103 : Blo 1887435 2833103 := bstep (se 1 (by rfl) ⟨2124827, by rfl⟩ : syracuseStep 2833103 = 4249655) B4249655
theorem B1888735 : Blo 1887435 1888735 := bstep (se 1 (by rfl) ⟨1416551, by rfl⟩ : syracuseStep 1888735 = 2833103) B2833103
theorem B2833109 : Blo 1887435 2833109 := bbase (se 7 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 2833109 = 66401) (by norm_num)
theorem B1888739 : Blo 1887435 1888739 := bstep (se 1 (by rfl) ⟨1416554, by rfl⟩ : syracuseStep 1888739 = 2833109) B2833109
theorem B5743541 : Blo 1887435 5743541 := bbase (se 5 (by rfl) ⟨269228, by rfl⟩ : syracuseStep 5743541 = 538457) (by norm_num)
theorem B3829027 : Blo 1887435 3829027 := bstep (se 1 (by rfl) ⟨2871770, by rfl⟩ : syracuseStep 3829027 = 5743541) B5743541
theorem B5105369 : Blo 1887435 5105369 := bstep (se 2 (by rfl) ⟨1914513, by rfl⟩ : syracuseStep 5105369 = 3829027) B3829027
theorem B13614317 : Blo 1887435 13614317 := bstep (se 3 (by rfl) ⟨2552684, by rfl⟩ : syracuseStep 13614317 = 5105369) B5105369
theorem B9076211 : Blo 1887435 9076211 := bstep (se 1 (by rfl) ⟨6807158, by rfl⟩ : syracuseStep 9076211 = 13614317) B13614317
theorem B6050807 : Blo 1887435 6050807 := bstep (se 1 (by rfl) ⟨4538105, by rfl⟩ : syracuseStep 6050807 = 9076211) B9076211
theorem B4033871 : Blo 1887435 4033871 := bstep (se 1 (by rfl) ⟨3025403, by rfl⟩ : syracuseStep 4033871 = 6050807) B6050807
theorem B2689247 : Blo 1887435 2689247 := bstep (se 1 (by rfl) ⟨2016935, by rfl⟩ : syracuseStep 2689247 = 4033871) B4033871
theorem B7171325 : Blo 1887435 7171325 := bstep (se 3 (by rfl) ⟨1344623, by rfl⟩ : syracuseStep 7171325 = 2689247) B2689247
theorem B4780883 : Blo 1887435 4780883 := bstep (se 1 (by rfl) ⟨3585662, by rfl⟩ : syracuseStep 4780883 = 7171325) B7171325
theorem B3187255 : Blo 1887435 3187255 := bstep (se 1 (by rfl) ⟨2390441, by rfl⟩ : syracuseStep 3187255 = 4780883) B4780883
theorem B4249673 : Blo 1887435 4249673 := bstep (se 2 (by rfl) ⟨1593627, by rfl⟩ : syracuseStep 4249673 = 3187255) B3187255
theorem B2833115 : Blo 1887435 2833115 := bstep (se 1 (by rfl) ⟨2124836, by rfl⟩ : syracuseStep 2833115 = 4249673) B4249673
theorem B1888743 : Blo 1887435 1888743 := bstep (se 1 (by rfl) ⟨1416557, by rfl⟩ : syracuseStep 1888743 = 2833115) B2833115
theorem B2124841 : Blo 1887435 2124841 := bbase (se 2 (by rfl) ⟨796815, by rfl⟩ : syracuseStep 2124841 = 1593631) (by norm_num)
theorem B2833121 : Blo 1887435 2833121 := bstep (se 2 (by rfl) ⟨1062420, by rfl⟩ : syracuseStep 2833121 = 2124841) B2124841
theorem B1888747 : Blo 1887435 1888747 := bstep (se 1 (by rfl) ⟨1416560, by rfl⟩ : syracuseStep 1888747 = 2833121) B2833121
theorem B5821925 : Blo 1887435 5821925 := bbase (se 4 (by rfl) ⟨545805, by rfl⟩ : syracuseStep 5821925 = 1091611) (by norm_num)
theorem B62100533 : Blo 1887435 62100533 := bstep (se 5 (by rfl) ⟨2910962, by rfl⟩ : syracuseStep 62100533 = 5821925) B5821925
theorem B41400355 : Blo 1887435 41400355 := bstep (se 1 (by rfl) ⟨31050266, by rfl⟩ : syracuseStep 41400355 = 62100533) B62100533
theorem B55200473 : Blo 1887435 55200473 := bstep (se 2 (by rfl) ⟨20700177, by rfl⟩ : syracuseStep 55200473 = 41400355) B41400355
theorem B36800315 : Blo 1887435 36800315 := bstep (se 1 (by rfl) ⟨27600236, by rfl⟩ : syracuseStep 36800315 = 55200473) B55200473
theorem B24533543 : Blo 1887435 24533543 := bstep (se 1 (by rfl) ⟨18400157, by rfl⟩ : syracuseStep 24533543 = 36800315) B36800315
theorem B16355695 : Blo 1887435 16355695 := bstep (se 1 (by rfl) ⟨12266771, by rfl⟩ : syracuseStep 16355695 = 24533543) B24533543
theorem B21807593 : Blo 1887435 21807593 := bstep (se 2 (by rfl) ⟨8177847, by rfl⟩ : syracuseStep 21807593 = 16355695) B16355695
theorem B14538395 : Blo 1887435 14538395 := bstep (se 1 (by rfl) ⟨10903796, by rfl⟩ : syracuseStep 14538395 = 21807593) B21807593
theorem B9692263 : Blo 1887435 9692263 := bstep (se 1 (by rfl) ⟨7269197, by rfl⟩ : syracuseStep 9692263 = 14538395) B14538395
theorem B51692069 : Blo 1887435 51692069 := bstep (se 4 (by rfl) ⟨4846131, by rfl⟩ : syracuseStep 51692069 = 9692263) B9692263
theorem B34461379 : Blo 1887435 34461379 := bstep (se 1 (by rfl) ⟨25846034, by rfl⟩ : syracuseStep 34461379 = 51692069) B51692069
theorem B45948505 : Blo 1887435 45948505 := bstep (se 2 (by rfl) ⟨17230689, by rfl⟩ : syracuseStep 45948505 = 34461379) B34461379
theorem B61264673 : Blo 1887435 61264673 := bstep (se 2 (by rfl) ⟨22974252, by rfl⟩ : syracuseStep 61264673 = 45948505) B45948505
theorem B40843115 : Blo 1887435 40843115 := bstep (se 1 (by rfl) ⟨30632336, by rfl⟩ : syracuseStep 40843115 = 61264673) B61264673
theorem B27228743 : Blo 1887435 27228743 := bstep (se 1 (by rfl) ⟨20421557, by rfl⟩ : syracuseStep 27228743 = 40843115) B40843115
theorem B18152495 : Blo 1887435 18152495 := bstep (se 1 (by rfl) ⟨13614371, by rfl⟩ : syracuseStep 18152495 = 27228743) B27228743
theorem B12101663 : Blo 1887435 12101663 := bstep (se 1 (by rfl) ⟨9076247, by rfl⟩ : syracuseStep 12101663 = 18152495) B18152495
theorem B8067775 : Blo 1887435 8067775 := bstep (se 1 (by rfl) ⟨6050831, by rfl⟩ : syracuseStep 8067775 = 12101663) B12101663
theorem B10757033 : Blo 1887435 10757033 := bstep (se 2 (by rfl) ⟨4033887, by rfl⟩ : syracuseStep 10757033 = 8067775) B8067775
theorem B7171355 : Blo 1887435 7171355 := bstep (se 1 (by rfl) ⟨5378516, by rfl⟩ : syracuseStep 7171355 = 10757033) B10757033
theorem B4780903 : Blo 1887435 4780903 := bstep (se 1 (by rfl) ⟨3585677, by rfl⟩ : syracuseStep 4780903 = 7171355) B7171355
theorem B6374537 : Blo 1887435 6374537 := bstep (se 2 (by rfl) ⟨2390451, by rfl⟩ : syracuseStep 6374537 = 4780903) B4780903
theorem B4249691 : Blo 1887435 4249691 := bstep (se 1 (by rfl) ⟨3187268, by rfl⟩ : syracuseStep 4249691 = 6374537) B6374537
theorem B2833127 : Blo 1887435 2833127 := bstep (se 1 (by rfl) ⟨2124845, by rfl⟩ : syracuseStep 2833127 = 4249691) B4249691
theorem B1888751 : Blo 1887435 1888751 := bstep (se 1 (by rfl) ⟨1416563, by rfl⟩ : syracuseStep 1888751 = 2833127) B2833127
theorem B2833133 : Blo 1887435 2833133 := bbase (se 3 (by rfl) ⟨531212, by rfl⟩ : syracuseStep 2833133 = 1062425) (by norm_num)
theorem B1888755 : Blo 1887435 1888755 := bstep (se 1 (by rfl) ⟨1416566, by rfl⟩ : syracuseStep 1888755 = 2833133) B2833133
theorem B4249709 : Blo 1887435 4249709 := bbase (se 3 (by rfl) ⟨796820, by rfl⟩ : syracuseStep 4249709 = 1593641) (by norm_num)
theorem B2833139 : Blo 1887435 2833139 := bstep (se 1 (by rfl) ⟨2124854, by rfl⟩ : syracuseStep 2833139 = 4249709) B4249709
theorem B1888759 : Blo 1887435 1888759 := bstep (se 1 (by rfl) ⟨1416569, by rfl⟩ : syracuseStep 1888759 = 2833139) B2833139
theorem B3585701 : Blo 1887435 3585701 := bbase (se 4 (by rfl) ⟨336159, by rfl⟩ : syracuseStep 3585701 = 672319) (by norm_num)
theorem B2390467 : Blo 1887435 2390467 := bstep (se 1 (by rfl) ⟨1792850, by rfl⟩ : syracuseStep 2390467 = 3585701) B3585701
theorem B3187289 : Blo 1887435 3187289 := bstep (se 2 (by rfl) ⟨1195233, by rfl⟩ : syracuseStep 3187289 = 2390467) B2390467
theorem B2124859 : Blo 1887435 2124859 := bstep (se 1 (by rfl) ⟨1593644, by rfl⟩ : syracuseStep 2124859 = 3187289) B3187289
theorem B2833145 : Blo 1887435 2833145 := bstep (se 2 (by rfl) ⟨1062429, by rfl⟩ : syracuseStep 2833145 = 2124859) B2124859
theorem B1888763 : Blo 1887435 1888763 := bstep (se 1 (by rfl) ⟨1416572, by rfl⟩ : syracuseStep 1888763 = 2833145) B2833145
theorem B13614485 : Blo 1887435 13614485 := bbase (se 6 (by rfl) ⟨319089, by rfl⟩ : syracuseStep 13614485 = 638179) (by norm_num)
theorem B36305293 : Blo 1887435 36305293 := bstep (se 3 (by rfl) ⟨6807242, by rfl⟩ : syracuseStep 36305293 = 13614485) B13614485
theorem B48407057 : Blo 1887435 48407057 := bstep (se 2 (by rfl) ⟨18152646, by rfl⟩ : syracuseStep 48407057 = 36305293) B36305293
theorem B32271371 : Blo 1887435 32271371 := bstep (se 1 (by rfl) ⟨24203528, by rfl⟩ : syracuseStep 32271371 = 48407057) B48407057
theorem B21514247 : Blo 1887435 21514247 := bstep (se 1 (by rfl) ⟨16135685, by rfl⟩ : syracuseStep 21514247 = 32271371) B32271371
theorem B14342831 : Blo 1887435 14342831 := bstep (se 1 (by rfl) ⟨10757123, by rfl⟩ : syracuseStep 14342831 = 21514247) B21514247
theorem B9561887 : Blo 1887435 9561887 := bstep (se 1 (by rfl) ⟨7171415, by rfl⟩ : syracuseStep 9561887 = 14342831) B14342831
theorem B6374591 : Blo 1887435 6374591 := bstep (se 1 (by rfl) ⟨4780943, by rfl⟩ : syracuseStep 6374591 = 9561887) B9561887
theorem B4249727 : Blo 1887435 4249727 := bstep (se 1 (by rfl) ⟨3187295, by rfl⟩ : syracuseStep 4249727 = 6374591) B6374591
theorem B2833151 : Blo 1887435 2833151 := bstep (se 1 (by rfl) ⟨2124863, by rfl⟩ : syracuseStep 2833151 = 4249727) B4249727
theorem B1888767 : Blo 1887435 1888767 := bstep (se 1 (by rfl) ⟨1416575, by rfl⟩ : syracuseStep 1888767 = 2833151) B2833151
theorem B2833157 : Blo 1887435 2833157 := bbase (se 4 (by rfl) ⟨265608, by rfl⟩ : syracuseStep 2833157 = 531217) (by norm_num)
theorem B1888771 : Blo 1887435 1888771 := bstep (se 1 (by rfl) ⟨1416578, by rfl⟩ : syracuseStep 1888771 = 2833157) B2833157
theorem B3187309 : Blo 1887435 3187309 := bbase (se 3 (by rfl) ⟨597620, by rfl⟩ : syracuseStep 3187309 = 1195241) (by norm_num)
theorem B4249745 : Blo 1887435 4249745 := bstep (se 2 (by rfl) ⟨1593654, by rfl⟩ : syracuseStep 4249745 = 3187309) B3187309
theorem B2833163 : Blo 1887435 2833163 := bstep (se 1 (by rfl) ⟨2124872, by rfl⟩ : syracuseStep 2833163 = 4249745) B4249745
theorem B1888775 : Blo 1887435 1888775 := bstep (se 1 (by rfl) ⟨1416581, by rfl⟩ : syracuseStep 1888775 = 2833163) B2833163
theorem B2124877 : Blo 1887435 2124877 := bbase (se 3 (by rfl) ⟨398414, by rfl⟩ : syracuseStep 2124877 = 796829) (by norm_num)
theorem B2833169 : Blo 1887435 2833169 := bstep (se 2 (by rfl) ⟨1062438, by rfl⟩ : syracuseStep 2833169 = 2124877) B2124877
theorem B1888779 : Blo 1887435 1888779 := bstep (se 1 (by rfl) ⟨1416584, by rfl⟩ : syracuseStep 1888779 = 2833169) B2833169
theorem B6374645 : Blo 1887435 6374645 := bbase (se 5 (by rfl) ⟨298811, by rfl⟩ : syracuseStep 6374645 = 597623) (by norm_num)
theorem B4249763 : Blo 1887435 4249763 := bstep (se 1 (by rfl) ⟨3187322, by rfl⟩ : syracuseStep 4249763 = 6374645) B6374645
theorem B2833175 : Blo 1887435 2833175 := bstep (se 1 (by rfl) ⟨2124881, by rfl⟩ : syracuseStep 2833175 = 4249763) B4249763
theorem B1888783 : Blo 1887435 1888783 := bstep (se 1 (by rfl) ⟨1416587, by rfl⟩ : syracuseStep 1888783 = 2833175) B2833175
theorem B2833181 : Blo 1887435 2833181 := bbase (se 3 (by rfl) ⟨531221, by rfl⟩ : syracuseStep 2833181 = 1062443) (by norm_num)
theorem B1888787 : Blo 1887435 1888787 := bstep (se 1 (by rfl) ⟨1416590, by rfl⟩ : syracuseStep 1888787 = 2833181) B2833181
theorem B4249781 : Blo 1887435 4249781 := bbase (se 5 (by rfl) ⟨199208, by rfl⟩ : syracuseStep 4249781 = 398417) (by norm_num)
theorem B2833187 : Blo 1887435 2833187 := bstep (se 1 (by rfl) ⟨2124890, by rfl⟩ : syracuseStep 2833187 = 4249781) B4249781
theorem B1888791 : Blo 1887435 1888791 := bstep (se 1 (by rfl) ⟨1416593, by rfl⟩ : syracuseStep 1888791 = 2833187) B2833187
theorem B3829133 : Blo 1887435 3829133 := bbase (se 3 (by rfl) ⟨717962, by rfl⟩ : syracuseStep 3829133 = 1435925) (by norm_num)
theorem B10211021 : Blo 1887435 10211021 := bstep (se 3 (by rfl) ⟨1914566, by rfl⟩ : syracuseStep 10211021 = 3829133) B3829133
theorem B6807347 : Blo 1887435 6807347 := bstep (se 1 (by rfl) ⟨5105510, by rfl⟩ : syracuseStep 6807347 = 10211021) B10211021
theorem B4538231 : Blo 1887435 4538231 := bstep (se 1 (by rfl) ⟨3403673, by rfl⟩ : syracuseStep 4538231 = 6807347) B6807347
theorem B3025487 : Blo 1887435 3025487 := bstep (se 1 (by rfl) ⟨2269115, by rfl⟩ : syracuseStep 3025487 = 4538231) B4538231
theorem B2016991 : Blo 1887435 2016991 := bstep (se 1 (by rfl) ⟨1512743, by rfl⟩ : syracuseStep 2016991 = 3025487) B3025487
theorem B10757285 : Blo 1887435 10757285 := bstep (se 4 (by rfl) ⟨1008495, by rfl⟩ : syracuseStep 10757285 = 2016991) B2016991
theorem B7171523 : Blo 1887435 7171523 := bstep (se 1 (by rfl) ⟨5378642, by rfl⟩ : syracuseStep 7171523 = 10757285) B10757285
theorem B4781015 : Blo 1887435 4781015 := bstep (se 1 (by rfl) ⟨3585761, by rfl⟩ : syracuseStep 4781015 = 7171523) B7171523
theorem B3187343 : Blo 1887435 3187343 := bstep (se 1 (by rfl) ⟨2390507, by rfl⟩ : syracuseStep 3187343 = 4781015) B4781015
theorem B2124895 : Blo 1887435 2124895 := bstep (se 1 (by rfl) ⟨1593671, by rfl⟩ : syracuseStep 2124895 = 3187343) B3187343
theorem B2833193 : Blo 1887435 2833193 := bstep (se 2 (by rfl) ⟨1062447, by rfl⟩ : syracuseStep 2833193 = 2124895) B2124895
theorem B1888795 : Blo 1887435 1888795 := bstep (se 1 (by rfl) ⟨1416596, by rfl⟩ : syracuseStep 1888795 = 2833193) B2833193
theorem B3025493 : Blo 1887435 3025493 := bbase (se 8 (by rfl) ⟨17727, by rfl⟩ : syracuseStep 3025493 = 35455) (by norm_num)
theorem B2016995 : Blo 1887435 2016995 := bstep (se 1 (by rfl) ⟨1512746, by rfl⟩ : syracuseStep 2016995 = 3025493) B3025493
theorem B5378653 : Blo 1887435 5378653 := bstep (se 3 (by rfl) ⟨1008497, by rfl⟩ : syracuseStep 5378653 = 2016995) B2016995
theorem B7171537 : Blo 1887435 7171537 := bstep (se 2 (by rfl) ⟨2689326, by rfl⟩ : syracuseStep 7171537 = 5378653) B5378653
theorem B9562049 : Blo 1887435 9562049 := bstep (se 2 (by rfl) ⟨3585768, by rfl⟩ : syracuseStep 9562049 = 7171537) B7171537
theorem B6374699 : Blo 1887435 6374699 := bstep (se 1 (by rfl) ⟨4781024, by rfl⟩ : syracuseStep 6374699 = 9562049) B9562049
theorem B4249799 : Blo 1887435 4249799 := bstep (se 1 (by rfl) ⟨3187349, by rfl⟩ : syracuseStep 4249799 = 6374699) B6374699
theorem B2833199 : Blo 1887435 2833199 := bstep (se 1 (by rfl) ⟨2124899, by rfl⟩ : syracuseStep 2833199 = 4249799) B4249799
theorem B1888799 : Blo 1887435 1888799 := bstep (se 1 (by rfl) ⟨1416599, by rfl⟩ : syracuseStep 1888799 = 2833199) B2833199
theorem B2833205 : Blo 1887435 2833205 := bbase (se 5 (by rfl) ⟨132806, by rfl⟩ : syracuseStep 2833205 = 265613) (by norm_num)
theorem B1888803 : Blo 1887435 1888803 := bstep (se 1 (by rfl) ⟨1416602, by rfl⟩ : syracuseStep 1888803 = 2833205) B2833205
theorem B4781045 : Blo 1887435 4781045 := bbase (se 5 (by rfl) ⟨224111, by rfl⟩ : syracuseStep 4781045 = 448223) (by norm_num)
theorem B3187363 : Blo 1887435 3187363 := bstep (se 1 (by rfl) ⟨2390522, by rfl⟩ : syracuseStep 3187363 = 4781045) B4781045
theorem B4249817 : Blo 1887435 4249817 := bstep (se 2 (by rfl) ⟨1593681, by rfl⟩ : syracuseStep 4249817 = 3187363) B3187363
theorem B2833211 : Blo 1887435 2833211 := bstep (se 1 (by rfl) ⟨2124908, by rfl⟩ : syracuseStep 2833211 = 4249817) B4249817
theorem B1888807 : Blo 1887435 1888807 := bstep (se 1 (by rfl) ⟨1416605, by rfl⟩ : syracuseStep 1888807 = 2833211) B2833211
theorem B2124913 : Blo 1887435 2124913 := bbase (se 2 (by rfl) ⟨796842, by rfl⟩ : syracuseStep 2124913 = 1593685) (by norm_num)
theorem B2833217 : Blo 1887435 2833217 := bstep (se 2 (by rfl) ⟨1062456, by rfl⟩ : syracuseStep 2833217 = 2124913) B2124913
theorem B1888811 : Blo 1887435 1888811 := bstep (se 1 (by rfl) ⟨1416608, by rfl⟩ : syracuseStep 1888811 = 2833217) B2833217
theorem B3403709 : Blo 1887435 3403709 := bbase (se 3 (by rfl) ⟨638195, by rfl⟩ : syracuseStep 3403709 = 1276391) (by norm_num)
theorem B2269139 : Blo 1887435 2269139 := bstep (se 1 (by rfl) ⟨1701854, by rfl⟩ : syracuseStep 2269139 = 3403709) B3403709
theorem B6051037 : Blo 1887435 6051037 := bstep (se 3 (by rfl) ⟨1134569, by rfl⟩ : syracuseStep 6051037 = 2269139) B2269139
theorem B8068049 : Blo 1887435 8068049 := bstep (se 2 (by rfl) ⟨3025518, by rfl⟩ : syracuseStep 8068049 = 6051037) B6051037
theorem B5378699 : Blo 1887435 5378699 := bstep (se 1 (by rfl) ⟨4034024, by rfl⟩ : syracuseStep 5378699 = 8068049) B8068049
theorem B3585799 : Blo 1887435 3585799 := bstep (se 1 (by rfl) ⟨2689349, by rfl⟩ : syracuseStep 3585799 = 5378699) B5378699
theorem B4781065 : Blo 1887435 4781065 := bstep (se 2 (by rfl) ⟨1792899, by rfl⟩ : syracuseStep 4781065 = 3585799) B3585799
theorem B6374753 : Blo 1887435 6374753 := bstep (se 2 (by rfl) ⟨2390532, by rfl⟩ : syracuseStep 6374753 = 4781065) B4781065
theorem B4249835 : Blo 1887435 4249835 := bstep (se 1 (by rfl) ⟨3187376, by rfl⟩ : syracuseStep 4249835 = 6374753) B6374753
theorem B2833223 : Blo 1887435 2833223 := bstep (se 1 (by rfl) ⟨2124917, by rfl⟩ : syracuseStep 2833223 = 4249835) B4249835
theorem B1888815 : Blo 1887435 1888815 := bstep (se 1 (by rfl) ⟨1416611, by rfl⟩ : syracuseStep 1888815 = 2833223) B2833223
theorem B2833229 : Blo 1887435 2833229 := bbase (se 3 (by rfl) ⟨531230, by rfl⟩ : syracuseStep 2833229 = 1062461) (by norm_num)
theorem B1888819 : Blo 1887435 1888819 := bstep (se 1 (by rfl) ⟨1416614, by rfl⟩ : syracuseStep 1888819 = 2833229) B2833229
theorem B4249853 : Blo 1887435 4249853 := bbase (se 3 (by rfl) ⟨796847, by rfl⟩ : syracuseStep 4249853 = 1593695) (by norm_num)
theorem B2833235 : Blo 1887435 2833235 := bstep (se 1 (by rfl) ⟨2124926, by rfl⟩ : syracuseStep 2833235 = 4249853) B4249853
theorem B1888823 : Blo 1887435 1888823 := bstep (se 1 (by rfl) ⟨1416617, by rfl⟩ : syracuseStep 1888823 = 2833235) B2833235
theorem B3187397 : Blo 1887435 3187397 := bbase (se 4 (by rfl) ⟨298818, by rfl⟩ : syracuseStep 3187397 = 597637) (by norm_num)
theorem B2124931 : Blo 1887435 2124931 := bstep (se 1 (by rfl) ⟨1593698, by rfl⟩ : syracuseStep 2124931 = 3187397) B3187397
theorem B2833241 : Blo 1887435 2833241 := bstep (se 2 (by rfl) ⟨1062465, by rfl⟩ : syracuseStep 2833241 = 2124931) B2124931
theorem B1888827 : Blo 1887435 1888827 := bstep (se 1 (by rfl) ⟨1416620, by rfl⟩ : syracuseStep 1888827 = 2833241) B2833241
theorem B14343317 : Blo 1887435 14343317 := bbase (se 6 (by rfl) ⟨336171, by rfl⟩ : syracuseStep 14343317 = 672343) (by norm_num)
theorem B9562211 : Blo 1887435 9562211 := bstep (se 1 (by rfl) ⟨7171658, by rfl⟩ : syracuseStep 9562211 = 14343317) B14343317
theorem B6374807 : Blo 1887435 6374807 := bstep (se 1 (by rfl) ⟨4781105, by rfl⟩ : syracuseStep 6374807 = 9562211) B9562211
theorem B4249871 : Blo 1887435 4249871 := bstep (se 1 (by rfl) ⟨3187403, by rfl⟩ : syracuseStep 4249871 = 6374807) B6374807
theorem B2833247 : Blo 1887435 2833247 := bstep (se 1 (by rfl) ⟨2124935, by rfl⟩ : syracuseStep 2833247 = 4249871) B4249871
theorem B1888831 : Blo 1887435 1888831 := bstep (se 1 (by rfl) ⟨1416623, by rfl⟩ : syracuseStep 1888831 = 2833247) B2833247
theorem B2833253 : Blo 1887435 2833253 := bbase (se 4 (by rfl) ⟨265617, by rfl⟩ : syracuseStep 2833253 = 531235) (by norm_num)
theorem B1888835 : Blo 1887435 1888835 := bstep (se 1 (by rfl) ⟨1416626, by rfl⟩ : syracuseStep 1888835 = 2833253) B2833253
theorem B3585845 : Blo 1887435 3585845 := bbase (se 5 (by rfl) ⟨168086, by rfl⟩ : syracuseStep 3585845 = 336173) (by norm_num)
theorem B2390563 : Blo 1887435 2390563 := bstep (se 1 (by rfl) ⟨1792922, by rfl⟩ : syracuseStep 2390563 = 3585845) B3585845
theorem B3187417 : Blo 1887435 3187417 := bstep (se 2 (by rfl) ⟨1195281, by rfl⟩ : syracuseStep 3187417 = 2390563) B2390563
theorem B4249889 : Blo 1887435 4249889 := bstep (se 2 (by rfl) ⟨1593708, by rfl⟩ : syracuseStep 4249889 = 3187417) B3187417
theorem B2833259 : Blo 1887435 2833259 := bstep (se 1 (by rfl) ⟨2124944, by rfl⟩ : syracuseStep 2833259 = 4249889) B4249889
theorem B1888839 : Blo 1887435 1888839 := bstep (se 1 (by rfl) ⟨1416629, by rfl⟩ : syracuseStep 1888839 = 2833259) B2833259
theorem B2124949 : Blo 1887435 2124949 := bbase (se 6 (by rfl) ⟨49803, by rfl⟩ : syracuseStep 2124949 = 99607) (by norm_num)
theorem B2833265 : Blo 1887435 2833265 := bstep (se 2 (by rfl) ⟨1062474, by rfl⟩ : syracuseStep 2833265 = 2124949) B2124949
theorem B1888843 : Blo 1887435 1888843 := bstep (se 1 (by rfl) ⟨1416632, by rfl⟩ : syracuseStep 1888843 = 2833265) B2833265
theorem B2390573 : Blo 1887435 2390573 := bbase (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) (by norm_num)
theorem B6374861 : Blo 1887435 6374861 := bstep (se 3 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 6374861 = 2390573) B2390573
theorem B4249907 : Blo 1887435 4249907 := bstep (se 1 (by rfl) ⟨3187430, by rfl⟩ : syracuseStep 4249907 = 6374861) B6374861
theorem B2833271 : Blo 1887435 2833271 := bstep (se 1 (by rfl) ⟨2124953, by rfl⟩ : syracuseStep 2833271 = 4249907) B4249907
theorem B1888847 : Blo 1887435 1888847 := bstep (se 1 (by rfl) ⟨1416635, by rfl⟩ : syracuseStep 1888847 = 2833271) B2833271
theorem B2833277 : Blo 1887435 2833277 := bbase (se 3 (by rfl) ⟨531239, by rfl⟩ : syracuseStep 2833277 = 1062479) (by norm_num)
theorem B1888851 : Blo 1887435 1888851 := bstep (se 1 (by rfl) ⟨1416638, by rfl⟩ : syracuseStep 1888851 = 2833277) B2833277
theorem B4249925 : Blo 1887435 4249925 := bbase (se 4 (by rfl) ⟨398430, by rfl⟩ : syracuseStep 4249925 = 796861) (by norm_num)
theorem B2833283 : Blo 1887435 2833283 := bstep (se 1 (by rfl) ⟨2124962, by rfl⟩ : syracuseStep 2833283 = 4249925) B4249925
theorem B1888855 : Blo 1887435 1888855 := bstep (se 1 (by rfl) ⟨1416641, by rfl⟩ : syracuseStep 1888855 = 2833283) B2833283
theorem B3230941 : Blo 1887435 3230941 := bbase (se 3 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 3230941 = 1211603) (by norm_num)
theorem B4307921 : Blo 1887435 4307921 := bstep (se 2 (by rfl) ⟨1615470, by rfl⟩ : syracuseStep 4307921 = 3230941) B3230941
theorem B2871947 : Blo 1887435 2871947 := bstep (se 1 (by rfl) ⟨2153960, by rfl⟩ : syracuseStep 2871947 = 4307921) B4307921
theorem B7658525 : Blo 1887435 7658525 := bstep (se 3 (by rfl) ⟨1435973, by rfl⟩ : syracuseStep 7658525 = 2871947) B2871947
theorem B5105683 : Blo 1887435 5105683 := bstep (se 1 (by rfl) ⟨3829262, by rfl⟩ : syracuseStep 5105683 = 7658525) B7658525
theorem B6807577 : Blo 1887435 6807577 := bstep (se 2 (by rfl) ⟨2552841, by rfl⟩ : syracuseStep 6807577 = 5105683) B5105683
theorem B9076769 : Blo 1887435 9076769 := bstep (se 2 (by rfl) ⟨3403788, by rfl⟩ : syracuseStep 9076769 = 6807577) B6807577
theorem B6051179 : Blo 1887435 6051179 := bstep (se 1 (by rfl) ⟨4538384, by rfl⟩ : syracuseStep 6051179 = 9076769) B9076769
theorem B4034119 : Blo 1887435 4034119 := bstep (se 1 (by rfl) ⟨3025589, by rfl⟩ : syracuseStep 4034119 = 6051179) B6051179
theorem B5378825 : Blo 1887435 5378825 := bstep (se 2 (by rfl) ⟨2017059, by rfl⟩ : syracuseStep 5378825 = 4034119) B4034119
theorem B3585883 : Blo 1887435 3585883 := bstep (se 1 (by rfl) ⟨2689412, by rfl⟩ : syracuseStep 3585883 = 5378825) B5378825
theorem B4781177 : Blo 1887435 4781177 := bstep (se 2 (by rfl) ⟨1792941, by rfl⟩ : syracuseStep 4781177 = 3585883) B3585883
theorem B3187451 : Blo 1887435 3187451 := bstep (se 1 (by rfl) ⟨2390588, by rfl⟩ : syracuseStep 3187451 = 4781177) B4781177
theorem B2124967 : Blo 1887435 2124967 := bstep (se 1 (by rfl) ⟨1593725, by rfl⟩ : syracuseStep 2124967 = 3187451) B3187451
theorem B2833289 : Blo 1887435 2833289 := bstep (se 2 (by rfl) ⟨1062483, by rfl⟩ : syracuseStep 2833289 = 2124967) B2124967
theorem B1888859 : Blo 1887435 1888859 := bstep (se 1 (by rfl) ⟨1416644, by rfl⟩ : syracuseStep 1888859 = 2833289) B2833289
theorem B9562373 : Blo 1887435 9562373 := bbase (se 4 (by rfl) ⟨896472, by rfl⟩ : syracuseStep 9562373 = 1792945) (by norm_num)
theorem B6374915 : Blo 1887435 6374915 := bstep (se 1 (by rfl) ⟨4781186, by rfl⟩ : syracuseStep 6374915 = 9562373) B9562373
theorem B4249943 : Blo 1887435 4249943 := bstep (se 1 (by rfl) ⟨3187457, by rfl⟩ : syracuseStep 4249943 = 6374915) B6374915
theorem B2833295 : Blo 1887435 2833295 := bstep (se 1 (by rfl) ⟨2124971, by rfl⟩ : syracuseStep 2833295 = 4249943) B4249943
theorem B1888863 : Blo 1887435 1888863 := bstep (se 1 (by rfl) ⟨1416647, by rfl⟩ : syracuseStep 1888863 = 2833295) B2833295
theorem B2833301 : Blo 1887435 2833301 := bbase (se 6 (by rfl) ⟨66405, by rfl⟩ : syracuseStep 2833301 = 132811) (by norm_num)
theorem B1888867 : Blo 1887435 1888867 := bstep (se 1 (by rfl) ⟨1416650, by rfl⟩ : syracuseStep 1888867 = 2833301) B2833301
theorem B10757717 : Blo 1887435 10757717 := bbase (se 8 (by rfl) ⟨63033, by rfl⟩ : syracuseStep 10757717 = 126067) (by norm_num)
theorem B7171811 : Blo 1887435 7171811 := bstep (se 1 (by rfl) ⟨5378858, by rfl⟩ : syracuseStep 7171811 = 10757717) B10757717
theorem B4781207 : Blo 1887435 4781207 := bstep (se 1 (by rfl) ⟨3585905, by rfl⟩ : syracuseStep 4781207 = 7171811) B7171811
theorem B3187471 : Blo 1887435 3187471 := bstep (se 1 (by rfl) ⟨2390603, by rfl⟩ : syracuseStep 3187471 = 4781207) B4781207
theorem B4249961 : Blo 1887435 4249961 := bstep (se 2 (by rfl) ⟨1593735, by rfl⟩ : syracuseStep 4249961 = 3187471) B3187471
theorem B2833307 : Blo 1887435 2833307 := bstep (se 1 (by rfl) ⟨2124980, by rfl⟩ : syracuseStep 2833307 = 4249961) B4249961
theorem B1888871 : Blo 1887435 1888871 := bstep (se 1 (by rfl) ⟨1416653, by rfl⟩ : syracuseStep 1888871 = 2833307) B2833307
theorem B2124985 : Blo 1887435 2124985 := bbase (se 2 (by rfl) ⟨796869, by rfl⟩ : syracuseStep 2124985 = 1593739) (by norm_num)
theorem B2833313 : Blo 1887435 2833313 := bstep (se 2 (by rfl) ⟨1062492, by rfl⟩ : syracuseStep 2833313 = 2124985) B2124985
theorem B1888875 : Blo 1887435 1888875 := bstep (se 1 (by rfl) ⟨1416656, by rfl⟩ : syracuseStep 1888875 = 2833313) B2833313
theorem B3025621 : Blo 1887435 3025621 := bbase (se 7 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 3025621 = 70913) (by norm_num)
theorem B4034161 : Blo 1887435 4034161 := bstep (se 2 (by rfl) ⟨1512810, by rfl⟩ : syracuseStep 4034161 = 3025621) B3025621
theorem B5378881 : Blo 1887435 5378881 := bstep (se 2 (by rfl) ⟨2017080, by rfl⟩ : syracuseStep 5378881 = 4034161) B4034161
theorem B7171841 : Blo 1887435 7171841 := bstep (se 2 (by rfl) ⟨2689440, by rfl⟩ : syracuseStep 7171841 = 5378881) B5378881
theorem B4781227 : Blo 1887435 4781227 := bstep (se 1 (by rfl) ⟨3585920, by rfl⟩ : syracuseStep 4781227 = 7171841) B7171841
theorem B6374969 : Blo 1887435 6374969 := bstep (se 2 (by rfl) ⟨2390613, by rfl⟩ : syracuseStep 6374969 = 4781227) B4781227
theorem B4249979 : Blo 1887435 4249979 := bstep (se 1 (by rfl) ⟨3187484, by rfl⟩ : syracuseStep 4249979 = 6374969) B6374969
theorem B2833319 : Blo 1887435 2833319 := bstep (se 1 (by rfl) ⟨2124989, by rfl⟩ : syracuseStep 2833319 = 4249979) B4249979
theorem B1888879 : Blo 1887435 1888879 := bstep (se 1 (by rfl) ⟨1416659, by rfl⟩ : syracuseStep 1888879 = 2833319) B2833319
theorem B2833325 : Blo 1887435 2833325 := bbase (se 3 (by rfl) ⟨531248, by rfl⟩ : syracuseStep 2833325 = 1062497) (by norm_num)
theorem B1888883 : Blo 1887435 1888883 := bstep (se 1 (by rfl) ⟨1416662, by rfl⟩ : syracuseStep 1888883 = 2833325) B2833325
theorem B4249997 : Blo 1887435 4249997 := bbase (se 3 (by rfl) ⟨796874, by rfl⟩ : syracuseStep 4249997 = 1593749) (by norm_num)
theorem B2833331 : Blo 1887435 2833331 := bstep (se 1 (by rfl) ⟨2124998, by rfl⟩ : syracuseStep 2833331 = 4249997) B4249997
theorem B1888887 : Blo 1887435 1888887 := bstep (se 1 (by rfl) ⟨1416665, by rfl⟩ : syracuseStep 1888887 = 2833331) B2833331
theorem B2390629 : Blo 1887435 2390629 := bbase (se 4 (by rfl) ⟨224121, by rfl⟩ : syracuseStep 2390629 = 448243) (by norm_num)
theorem B3187505 : Blo 1887435 3187505 := bstep (se 2 (by rfl) ⟨1195314, by rfl⟩ : syracuseStep 3187505 = 2390629) B2390629
theorem B2125003 : Blo 1887435 2125003 := bstep (se 1 (by rfl) ⟨1593752, by rfl⟩ : syracuseStep 2125003 = 3187505) B3187505
theorem B2833337 : Blo 1887435 2833337 := bstep (se 2 (by rfl) ⟨1062501, by rfl⟩ : syracuseStep 2833337 = 2125003) B2125003
theorem B1888891 : Blo 1887435 1888891 := bstep (se 1 (by rfl) ⟨1416668, by rfl⟩ : syracuseStep 1888891 = 2833337) B2833337
theorem B18153877 : Blo 1887435 18153877 := bbase (se 6 (by rfl) ⟨425481, by rfl⟩ : syracuseStep 18153877 = 850963) (by norm_num)
theorem B24205169 : Blo 1887435 24205169 := bstep (se 2 (by rfl) ⟨9076938, by rfl⟩ : syracuseStep 24205169 = 18153877) B18153877
theorem B16136779 : Blo 1887435 16136779 := bstep (se 1 (by rfl) ⟨12102584, by rfl⟩ : syracuseStep 16136779 = 24205169) B24205169
theorem B21515705 : Blo 1887435 21515705 := bstep (se 2 (by rfl) ⟨8068389, by rfl⟩ : syracuseStep 21515705 = 16136779) B16136779
theorem B14343803 : Blo 1887435 14343803 := bstep (se 1 (by rfl) ⟨10757852, by rfl⟩ : syracuseStep 14343803 = 21515705) B21515705
theorem B9562535 : Blo 1887435 9562535 := bstep (se 1 (by rfl) ⟨7171901, by rfl⟩ : syracuseStep 9562535 = 14343803) B14343803
theorem B6375023 : Blo 1887435 6375023 := bstep (se 1 (by rfl) ⟨4781267, by rfl⟩ : syracuseStep 6375023 = 9562535) B9562535
theorem B4250015 : Blo 1887435 4250015 := bstep (se 1 (by rfl) ⟨3187511, by rfl⟩ : syracuseStep 4250015 = 6375023) B6375023
theorem B2833343 : Blo 1887435 2833343 := bstep (se 1 (by rfl) ⟨2125007, by rfl⟩ : syracuseStep 2833343 = 4250015) B4250015
theorem B1888895 : Blo 1887435 1888895 := bstep (se 1 (by rfl) ⟨1416671, by rfl⟩ : syracuseStep 1888895 = 2833343) B2833343
theorem B2833349 : Blo 1887435 2833349 := bbase (se 4 (by rfl) ⟨265626, by rfl⟩ : syracuseStep 2833349 = 531253) (by norm_num)
theorem B1888899 : Blo 1887435 1888899 := bstep (se 1 (by rfl) ⟨1416674, by rfl⟩ : syracuseStep 1888899 = 2833349) B2833349
theorem B3187525 : Blo 1887435 3187525 := bbase (se 4 (by rfl) ⟨298830, by rfl⟩ : syracuseStep 3187525 = 597661) (by norm_num)
theorem B4250033 : Blo 1887435 4250033 := bstep (se 2 (by rfl) ⟨1593762, by rfl⟩ : syracuseStep 4250033 = 3187525) B3187525
theorem B2833355 : Blo 1887435 2833355 := bstep (se 1 (by rfl) ⟨2125016, by rfl⟩ : syracuseStep 2833355 = 4250033) B4250033
theorem B1888903 : Blo 1887435 1888903 := bstep (se 1 (by rfl) ⟨1416677, by rfl⟩ : syracuseStep 1888903 = 2833355) B2833355
theorem B2125021 : Blo 1887435 2125021 := bbase (se 3 (by rfl) ⟨398441, by rfl⟩ : syracuseStep 2125021 = 796883) (by norm_num)
theorem B2833361 : Blo 1887435 2833361 := bstep (se 2 (by rfl) ⟨1062510, by rfl⟩ : syracuseStep 2833361 = 2125021) B2125021
theorem B1888907 : Blo 1887435 1888907 := bstep (se 1 (by rfl) ⟨1416680, by rfl⟩ : syracuseStep 1888907 = 2833361) B2833361
theorem B6375077 : Blo 1887435 6375077 := bbase (se 4 (by rfl) ⟨597663, by rfl⟩ : syracuseStep 6375077 = 1195327) (by norm_num)
theorem B4250051 : Blo 1887435 4250051 := bstep (se 1 (by rfl) ⟨3187538, by rfl⟩ : syracuseStep 4250051 = 6375077) B6375077
theorem B2833367 : Blo 1887435 2833367 := bstep (se 1 (by rfl) ⟨2125025, by rfl⟩ : syracuseStep 2833367 = 4250051) B4250051
theorem B1888911 : Blo 1887435 1888911 := bstep (se 1 (by rfl) ⟨1416683, by rfl⟩ : syracuseStep 1888911 = 2833367) B2833367
theorem B2833373 : Blo 1887435 2833373 := bbase (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) (by norm_num)
theorem B1888915 : Blo 1887435 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B4250069 : Blo 1887435 4250069 := bbase (se 7 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 4250069 = 99611) (by norm_num)
theorem B2833379 : Blo 1887435 2833379 := bstep (se 1 (by rfl) ⟨2125034, by rfl⟩ : syracuseStep 2833379 = 4250069) B4250069
theorem B1888919 : Blo 1887435 1888919 := bstep (se 1 (by rfl) ⟨1416689, by rfl⟩ : syracuseStep 1888919 = 2833379) B2833379
theorem B2911229 : Blo 1887435 2911229 := bbase (se 3 (by rfl) ⟨545855, by rfl⟩ : syracuseStep 2911229 = 1091711) (by norm_num)
theorem B1940819 : Blo 1887435 1940819 := bstep (se 1 (by rfl) ⟨1455614, by rfl⟩ : syracuseStep 1940819 = 2911229) B2911229
theorem B5175517 : Blo 1887435 5175517 := bstep (se 3 (by rfl) ⟨970409, by rfl⟩ : syracuseStep 5175517 = 1940819) B1940819
theorem B6900689 : Blo 1887435 6900689 := bstep (se 2 (by rfl) ⟨2587758, by rfl⟩ : syracuseStep 6900689 = 5175517) B5175517
theorem B4600459 : Blo 1887435 4600459 := bstep (se 1 (by rfl) ⟨3450344, by rfl⟩ : syracuseStep 4600459 = 6900689) B6900689
theorem B24535781 : Blo 1887435 24535781 := bstep (se 4 (by rfl) ⟨2300229, by rfl⟩ : syracuseStep 24535781 = 4600459) B4600459
theorem B16357187 : Blo 1887435 16357187 := bstep (se 1 (by rfl) ⟨12267890, by rfl⟩ : syracuseStep 16357187 = 24535781) B24535781
theorem B10904791 : Blo 1887435 10904791 := bstep (se 1 (by rfl) ⟨8178593, by rfl⟩ : syracuseStep 10904791 = 16357187) B16357187
theorem B14539721 : Blo 1887435 14539721 := bstep (se 2 (by rfl) ⟨5452395, by rfl⟩ : syracuseStep 14539721 = 10904791) B10904791
theorem B38772589 : Blo 1887435 38772589 := bstep (se 3 (by rfl) ⟨7269860, by rfl⟩ : syracuseStep 38772589 = 14539721) B14539721
theorem B51696785 : Blo 1887435 51696785 := bstep (se 2 (by rfl) ⟨19386294, by rfl⟩ : syracuseStep 51696785 = 38772589) B38772589
theorem B34464523 : Blo 1887435 34464523 := bstep (se 1 (by rfl) ⟨25848392, by rfl⟩ : syracuseStep 34464523 = 51696785) B51696785
theorem B45952697 : Blo 1887435 45952697 := bstep (se 2 (by rfl) ⟨17232261, by rfl⟩ : syracuseStep 45952697 = 34464523) B34464523
theorem B30635131 : Blo 1887435 30635131 := bstep (se 1 (by rfl) ⟨22976348, by rfl⟩ : syracuseStep 30635131 = 45952697) B45952697
theorem B40846841 : Blo 1887435 40846841 := bstep (se 2 (by rfl) ⟨15317565, by rfl⟩ : syracuseStep 40846841 = 30635131) B30635131
theorem B27231227 : Blo 1887435 27231227 := bstep (se 1 (by rfl) ⟨20423420, by rfl⟩ : syracuseStep 27231227 = 40846841) B40846841
theorem B18154151 : Blo 1887435 18154151 := bstep (se 1 (by rfl) ⟨13615613, by rfl⟩ : syracuseStep 18154151 = 27231227) B27231227
theorem B12102767 : Blo 1887435 12102767 := bstep (se 1 (by rfl) ⟨9077075, by rfl⟩ : syracuseStep 12102767 = 18154151) B18154151
theorem B8068511 : Blo 1887435 8068511 := bstep (se 1 (by rfl) ⟨6051383, by rfl⟩ : syracuseStep 8068511 = 12102767) B12102767
theorem B5379007 : Blo 1887435 5379007 := bstep (se 1 (by rfl) ⟨4034255, by rfl⟩ : syracuseStep 5379007 = 8068511) B8068511
theorem B7172009 : Blo 1887435 7172009 := bstep (se 2 (by rfl) ⟨2689503, by rfl⟩ : syracuseStep 7172009 = 5379007) B5379007
theorem B4781339 : Blo 1887435 4781339 := bstep (se 1 (by rfl) ⟨3586004, by rfl⟩ : syracuseStep 4781339 = 7172009) B7172009
theorem B3187559 : Blo 1887435 3187559 := bstep (se 1 (by rfl) ⟨2390669, by rfl⟩ : syracuseStep 3187559 = 4781339) B4781339
theorem B2125039 : Blo 1887435 2125039 := bstep (se 1 (by rfl) ⟨1593779, by rfl⟩ : syracuseStep 2125039 = 3187559) B3187559
theorem B2833385 : Blo 1887435 2833385 := bstep (se 2 (by rfl) ⟨1062519, by rfl⟩ : syracuseStep 2833385 = 2125039) B2125039
theorem B1888923 : Blo 1887435 1888923 := bstep (se 1 (by rfl) ⟨1416692, by rfl⟩ : syracuseStep 1888923 = 2833385) B2833385
theorem B9077093 : Blo 1887435 9077093 := bbase (se 4 (by rfl) ⟨850977, by rfl⟩ : syracuseStep 9077093 = 1701955) (by norm_num)
theorem B6051395 : Blo 1887435 6051395 := bstep (se 1 (by rfl) ⟨4538546, by rfl⟩ : syracuseStep 6051395 = 9077093) B9077093
theorem B16137053 : Blo 1887435 16137053 := bstep (se 3 (by rfl) ⟨3025697, by rfl⟩ : syracuseStep 16137053 = 6051395) B6051395
theorem B10758035 : Blo 1887435 10758035 := bstep (se 1 (by rfl) ⟨8068526, by rfl⟩ : syracuseStep 10758035 = 16137053) B16137053
theorem B7172023 : Blo 1887435 7172023 := bstep (se 1 (by rfl) ⟨5379017, by rfl⟩ : syracuseStep 7172023 = 10758035) B10758035
theorem B9562697 : Blo 1887435 9562697 := bstep (se 2 (by rfl) ⟨3586011, by rfl⟩ : syracuseStep 9562697 = 7172023) B7172023
theorem B6375131 : Blo 1887435 6375131 := bstep (se 1 (by rfl) ⟨4781348, by rfl⟩ : syracuseStep 6375131 = 9562697) B9562697
theorem B4250087 : Blo 1887435 4250087 := bstep (se 1 (by rfl) ⟨3187565, by rfl⟩ : syracuseStep 4250087 = 6375131) B6375131
theorem B2833391 : Blo 1887435 2833391 := bstep (se 1 (by rfl) ⟨2125043, by rfl⟩ : syracuseStep 2833391 = 4250087) B4250087
theorem B1888927 : Blo 1887435 1888927 := bstep (se 1 (by rfl) ⟨1416695, by rfl⟩ : syracuseStep 1888927 = 2833391) B2833391
theorem B2833397 : Blo 1887435 2833397 := bbase (se 5 (by rfl) ⟨132815, by rfl⟩ : syracuseStep 2833397 = 265631) (by norm_num)
theorem B1888931 : Blo 1887435 1888931 := bstep (se 1 (by rfl) ⟨1416698, by rfl⟩ : syracuseStep 1888931 = 2833397) B2833397
theorem B16357301 : Blo 1887435 16357301 := bbase (se 5 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 16357301 = 1533497) (by norm_num)
theorem B10904867 : Blo 1887435 10904867 := bstep (se 1 (by rfl) ⟨8178650, by rfl⟩ : syracuseStep 10904867 = 16357301) B16357301
theorem B7269911 : Blo 1887435 7269911 := bstep (se 1 (by rfl) ⟨5452433, by rfl⟩ : syracuseStep 7269911 = 10904867) B10904867
theorem B4846607 : Blo 1887435 4846607 := bstep (se 1 (by rfl) ⟨3634955, by rfl⟩ : syracuseStep 4846607 = 7269911) B7269911
theorem B3231071 : Blo 1887435 3231071 := bstep (se 1 (by rfl) ⟨2423303, by rfl⟩ : syracuseStep 3231071 = 4846607) B4846607
theorem B2154047 : Blo 1887435 2154047 := bstep (se 1 (by rfl) ⟨1615535, by rfl⟩ : syracuseStep 2154047 = 3231071) B3231071
theorem B5744125 : Blo 1887435 5744125 := bstep (se 3 (by rfl) ⟨1077023, by rfl⟩ : syracuseStep 5744125 = 2154047) B2154047
theorem B7658833 : Blo 1887435 7658833 := bstep (se 2 (by rfl) ⟨2872062, by rfl⟩ : syracuseStep 7658833 = 5744125) B5744125
theorem B10211777 : Blo 1887435 10211777 := bstep (se 2 (by rfl) ⟨3829416, by rfl⟩ : syracuseStep 10211777 = 7658833) B7658833
theorem B6807851 : Blo 1887435 6807851 := bstep (se 1 (by rfl) ⟨5105888, by rfl⟩ : syracuseStep 6807851 = 10211777) B10211777
theorem B4538567 : Blo 1887435 4538567 := bstep (se 1 (by rfl) ⟨3403925, by rfl⟩ : syracuseStep 4538567 = 6807851) B6807851
theorem B3025711 : Blo 1887435 3025711 := bstep (se 1 (by rfl) ⟨2269283, by rfl⟩ : syracuseStep 3025711 = 4538567) B4538567
theorem B4034281 : Blo 1887435 4034281 := bstep (se 2 (by rfl) ⟨1512855, by rfl⟩ : syracuseStep 4034281 = 3025711) B3025711
theorem B5379041 : Blo 1887435 5379041 := bstep (se 2 (by rfl) ⟨2017140, by rfl⟩ : syracuseStep 5379041 = 4034281) B4034281
theorem B3586027 : Blo 1887435 3586027 := bstep (se 1 (by rfl) ⟨2689520, by rfl⟩ : syracuseStep 3586027 = 5379041) B5379041
theorem B4781369 : Blo 1887435 4781369 := bstep (se 2 (by rfl) ⟨1793013, by rfl⟩ : syracuseStep 4781369 = 3586027) B3586027
theorem B3187579 : Blo 1887435 3187579 := bstep (se 1 (by rfl) ⟨2390684, by rfl⟩ : syracuseStep 3187579 = 4781369) B4781369
theorem B4250105 : Blo 1887435 4250105 := bstep (se 2 (by rfl) ⟨1593789, by rfl⟩ : syracuseStep 4250105 = 3187579) B3187579
theorem B2833403 : Blo 1887435 2833403 := bstep (se 1 (by rfl) ⟨2125052, by rfl⟩ : syracuseStep 2833403 = 4250105) B4250105
theorem B1888935 : Blo 1887435 1888935 := bstep (se 1 (by rfl) ⟨1416701, by rfl⟩ : syracuseStep 1888935 = 2833403) B2833403
theorem B2125057 : Blo 1887435 2125057 := bbase (se 2 (by rfl) ⟨796896, by rfl⟩ : syracuseStep 2125057 = 1593793) (by norm_num)
theorem B2833409 : Blo 1887435 2833409 := bstep (se 2 (by rfl) ⟨1062528, by rfl⟩ : syracuseStep 2833409 = 2125057) B2125057
theorem B1888939 : Blo 1887435 1888939 := bstep (se 1 (by rfl) ⟨1416704, by rfl⟩ : syracuseStep 1888939 = 2833409) B2833409
theorem B4781389 : Blo 1887435 4781389 := bbase (se 3 (by rfl) ⟨896510, by rfl⟩ : syracuseStep 4781389 = 1793021) (by norm_num)
theorem B6375185 : Blo 1887435 6375185 := bstep (se 2 (by rfl) ⟨2390694, by rfl⟩ : syracuseStep 6375185 = 4781389) B4781389
theorem B4250123 : Blo 1887435 4250123 := bstep (se 1 (by rfl) ⟨3187592, by rfl⟩ : syracuseStep 4250123 = 6375185) B6375185
theorem B2833415 : Blo 1887435 2833415 := bstep (se 1 (by rfl) ⟨2125061, by rfl⟩ : syracuseStep 2833415 = 4250123) B4250123
theorem B1888943 : Blo 1887435 1888943 := bstep (se 1 (by rfl) ⟨1416707, by rfl⟩ : syracuseStep 1888943 = 2833415) B2833415
theorem B2833421 : Blo 1887435 2833421 := bbase (se 3 (by rfl) ⟨531266, by rfl⟩ : syracuseStep 2833421 = 1062533) (by norm_num)
theorem B1888947 : Blo 1887435 1888947 := bstep (se 1 (by rfl) ⟨1416710, by rfl⟩ : syracuseStep 1888947 = 2833421) B2833421
theorem B4250141 : Blo 1887435 4250141 := bbase (se 3 (by rfl) ⟨796901, by rfl⟩ : syracuseStep 4250141 = 1593803) (by norm_num)
theorem B2833427 : Blo 1887435 2833427 := bstep (se 1 (by rfl) ⟨2125070, by rfl⟩ : syracuseStep 2833427 = 4250141) B4250141
theorem B1888951 : Blo 1887435 1888951 := bstep (se 1 (by rfl) ⟨1416713, by rfl⟩ : syracuseStep 1888951 = 2833427) B2833427
theorem B3187613 : Blo 1887435 3187613 := bbase (se 3 (by rfl) ⟨597677, by rfl⟩ : syracuseStep 3187613 = 1195355) (by norm_num)
theorem B2125075 : Blo 1887435 2125075 := bstep (se 1 (by rfl) ⟨1593806, by rfl⟩ : syracuseStep 2125075 = 3187613) B3187613
theorem B2833433 : Blo 1887435 2833433 := bstep (se 2 (by rfl) ⟨1062537, by rfl⟩ : syracuseStep 2833433 = 2125075) B2125075
theorem B1888955 : Blo 1887435 1888955 := bstep (se 1 (by rfl) ⟨1416716, by rfl⟩ : syracuseStep 1888955 = 2833433) B2833433
theorem B6900821 : Blo 1887435 6900821 := bbase (se 8 (by rfl) ⟨40434, by rfl⟩ : syracuseStep 6900821 = 80869) (by norm_num)
theorem B4600547 : Blo 1887435 4600547 := bstep (se 1 (by rfl) ⟨3450410, by rfl⟩ : syracuseStep 4600547 = 6900821) B6900821
theorem B3067031 : Blo 1887435 3067031 := bstep (se 1 (by rfl) ⟨2300273, by rfl⟩ : syracuseStep 3067031 = 4600547) B4600547
theorem B8178749 : Blo 1887435 8178749 := bstep (se 3 (by rfl) ⟨1533515, by rfl⟩ : syracuseStep 8178749 = 3067031) B3067031
theorem B5452499 : Blo 1887435 5452499 := bstep (se 1 (by rfl) ⟨4089374, by rfl⟩ : syracuseStep 5452499 = 8178749) B8178749
theorem B3634999 : Blo 1887435 3634999 := bstep (se 1 (by rfl) ⟨2726249, by rfl⟩ : syracuseStep 3634999 = 5452499) B5452499
theorem B77546645 : Blo 1887435 77546645 := bstep (se 6 (by rfl) ⟨1817499, by rfl⟩ : syracuseStep 77546645 = 3634999) B3634999
theorem B51697763 : Blo 1887435 51697763 := bstep (se 1 (by rfl) ⟨38773322, by rfl⟩ : syracuseStep 51697763 = 77546645) B77546645
theorem B34465175 : Blo 1887435 34465175 := bstep (se 1 (by rfl) ⟨25848881, by rfl⟩ : syracuseStep 34465175 = 51697763) B51697763
theorem B22976783 : Blo 1887435 22976783 := bstep (se 1 (by rfl) ⟨17232587, by rfl⟩ : syracuseStep 22976783 = 34465175) B34465175
theorem B15317855 : Blo 1887435 15317855 := bstep (se 1 (by rfl) ⟨11488391, by rfl⟩ : syracuseStep 15317855 = 22976783) B22976783
theorem B10211903 : Blo 1887435 10211903 := bstep (se 1 (by rfl) ⟨7658927, by rfl⟩ : syracuseStep 10211903 = 15317855) B15317855
theorem B6807935 : Blo 1887435 6807935 := bstep (se 1 (by rfl) ⟨5105951, by rfl⟩ : syracuseStep 6807935 = 10211903) B10211903
theorem B18154493 : Blo 1887435 18154493 := bstep (se 3 (by rfl) ⟨3403967, by rfl⟩ : syracuseStep 18154493 = 6807935) B6807935
theorem B12102995 : Blo 1887435 12102995 := bstep (se 1 (by rfl) ⟨9077246, by rfl⟩ : syracuseStep 12102995 = 18154493) B18154493
theorem B8068663 : Blo 1887435 8068663 := bstep (se 1 (by rfl) ⟨6051497, by rfl⟩ : syracuseStep 8068663 = 12102995) B12102995
theorem B10758217 : Blo 1887435 10758217 := bstep (se 2 (by rfl) ⟨4034331, by rfl⟩ : syracuseStep 10758217 = 8068663) B8068663
theorem B14344289 : Blo 1887435 14344289 := bstep (se 2 (by rfl) ⟨5379108, by rfl⟩ : syracuseStep 14344289 = 10758217) B10758217
theorem B9562859 : Blo 1887435 9562859 := bstep (se 1 (by rfl) ⟨7172144, by rfl⟩ : syracuseStep 9562859 = 14344289) B14344289
theorem B6375239 : Blo 1887435 6375239 := bstep (se 1 (by rfl) ⟨4781429, by rfl⟩ : syracuseStep 6375239 = 9562859) B9562859
theorem B4250159 : Blo 1887435 4250159 := bstep (se 1 (by rfl) ⟨3187619, by rfl⟩ : syracuseStep 4250159 = 6375239) B6375239
theorem B2833439 : Blo 1887435 2833439 := bstep (se 1 (by rfl) ⟨2125079, by rfl⟩ : syracuseStep 2833439 = 4250159) B4250159
theorem B1888959 : Blo 1887435 1888959 := bstep (se 1 (by rfl) ⟨1416719, by rfl⟩ : syracuseStep 1888959 = 2833439) B2833439
theorem B2833445 : Blo 1887435 2833445 := bbase (se 4 (by rfl) ⟨265635, by rfl⟩ : syracuseStep 2833445 = 531271) (by norm_num)
theorem B1888963 : Blo 1887435 1888963 := bstep (se 1 (by rfl) ⟨1416722, by rfl⟩ : syracuseStep 1888963 = 2833445) B2833445
theorem B2390725 : Blo 1887435 2390725 := bbase (se 4 (by rfl) ⟨224130, by rfl⟩ : syracuseStep 2390725 = 448261) (by norm_num)
theorem B3187633 : Blo 1887435 3187633 := bstep (se 2 (by rfl) ⟨1195362, by rfl⟩ : syracuseStep 3187633 = 2390725) B2390725
theorem B4250177 : Blo 1887435 4250177 := bstep (se 2 (by rfl) ⟨1593816, by rfl⟩ : syracuseStep 4250177 = 3187633) B3187633
theorem B2833451 : Blo 1887435 2833451 := bstep (se 1 (by rfl) ⟨2125088, by rfl⟩ : syracuseStep 2833451 = 4250177) B4250177
theorem B1888967 : Blo 1887435 1888967 := bstep (se 1 (by rfl) ⟨1416725, by rfl⟩ : syracuseStep 1888967 = 2833451) B2833451
theorem B2125093 : Blo 1887435 2125093 := bbase (se 4 (by rfl) ⟨199227, by rfl⟩ : syracuseStep 2125093 = 398455) (by norm_num)
theorem B2833457 : Blo 1887435 2833457 := bstep (se 2 (by rfl) ⟨1062546, by rfl⟩ : syracuseStep 2833457 = 2125093) B2125093
theorem B1888971 : Blo 1887435 1888971 := bstep (se 1 (by rfl) ⟨1416728, by rfl⟩ : syracuseStep 1888971 = 2833457) B2833457
theorem B4846709 : Blo 1887435 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B3231139 : Blo 1887435 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B4308185 : Blo 1887435 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B11488493 : Blo 1887435 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B7658995 : Blo 1887435 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B10211993 : Blo 1887435 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B6807995 : Blo 1887435 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B4538663 : Blo 1887435 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B3025775 : Blo 1887435 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B8068733 : Blo 1887435 8068733 := bstep (se 3 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 8068733 = 3025775) B3025775
theorem B5379155 : Blo 1887435 5379155 := bstep (se 1 (by rfl) ⟨4034366, by rfl⟩ : syracuseStep 5379155 = 8068733) B8068733
theorem B3586103 : Blo 1887435 3586103 := bstep (se 1 (by rfl) ⟨2689577, by rfl⟩ : syracuseStep 3586103 = 5379155) B5379155
theorem B2390735 : Blo 1887435 2390735 := bstep (se 1 (by rfl) ⟨1793051, by rfl⟩ : syracuseStep 2390735 = 3586103) B3586103
theorem B6375293 : Blo 1887435 6375293 := bstep (se 3 (by rfl) ⟨1195367, by rfl⟩ : syracuseStep 6375293 = 2390735) B2390735
theorem B4250195 : Blo 1887435 4250195 := bstep (se 1 (by rfl) ⟨3187646, by rfl⟩ : syracuseStep 4250195 = 6375293) B6375293
theorem B2833463 : Blo 1887435 2833463 := bstep (se 1 (by rfl) ⟨2125097, by rfl⟩ : syracuseStep 2833463 = 4250195) B4250195
theorem B1888975 : Blo 1887435 1888975 := bstep (se 1 (by rfl) ⟨1416731, by rfl⟩ : syracuseStep 1888975 = 2833463) B2833463
theorem B2833469 : Blo 1887435 2833469 := bbase (se 3 (by rfl) ⟨531275, by rfl⟩ : syracuseStep 2833469 = 1062551) (by norm_num)
theorem B1888979 : Blo 1887435 1888979 := bstep (se 1 (by rfl) ⟨1416734, by rfl⟩ : syracuseStep 1888979 = 2833469) B2833469
theorem B4250213 : Blo 1887435 4250213 := bbase (se 4 (by rfl) ⟨398457, by rfl⟩ : syracuseStep 4250213 = 796915) (by norm_num)
theorem B2833475 : Blo 1887435 2833475 := bstep (se 1 (by rfl) ⟨2125106, by rfl⟩ : syracuseStep 2833475 = 4250213) B4250213
theorem B1888983 : Blo 1887435 1888983 := bstep (se 1 (by rfl) ⟨1416737, by rfl⟩ : syracuseStep 1888983 = 2833475) B2833475
theorem B4781501 : Blo 1887435 4781501 := bbase (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) (by norm_num)
theorem B3187667 : Blo 1887435 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B2125111 : Blo 1887435 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2833481 : Blo 1887435 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B1888987 : Blo 1887435 1888987 := bstep (se 1 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 1888987 = 2833481) B2833481
theorem B3586133 : Blo 1887435 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B9563021 : Blo 1887435 9563021 := bstep (se 3 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 9563021 = 3586133) B3586133
theorem B6375347 : Blo 1887435 6375347 := bstep (se 1 (by rfl) ⟨4781510, by rfl⟩ : syracuseStep 6375347 = 9563021) B9563021
theorem B4250231 : Blo 1887435 4250231 := bstep (se 1 (by rfl) ⟨3187673, by rfl⟩ : syracuseStep 4250231 = 6375347) B6375347
theorem B2833487 : Blo 1887435 2833487 := bstep (se 1 (by rfl) ⟨2125115, by rfl⟩ : syracuseStep 2833487 = 4250231) B4250231
theorem B1888991 : Blo 1887435 1888991 := bstep (se 1 (by rfl) ⟨1416743, by rfl⟩ : syracuseStep 1888991 = 2833487) B2833487
theorem B2833493 : Blo 1887435 2833493 := bbase (se 8 (by rfl) ⟨16602, by rfl⟩ : syracuseStep 2833493 = 33205) (by norm_num)
theorem B1888995 : Blo 1887435 1888995 := bstep (se 1 (by rfl) ⟨1416746, by rfl⟩ : syracuseStep 1888995 = 2833493) B2833493
theorem B12103253 : Blo 1887435 12103253 := bbase (se 8 (by rfl) ⟨70917, by rfl⟩ : syracuseStep 12103253 = 141835) (by norm_num)
theorem B8068835 : Blo 1887435 8068835 := bstep (se 1 (by rfl) ⟨6051626, by rfl⟩ : syracuseStep 8068835 = 12103253) B12103253
theorem B5379223 : Blo 1887435 5379223 := bstep (se 1 (by rfl) ⟨4034417, by rfl⟩ : syracuseStep 5379223 = 8068835) B8068835
theorem B7172297 : Blo 1887435 7172297 := bstep (se 2 (by rfl) ⟨2689611, by rfl⟩ : syracuseStep 7172297 = 5379223) B5379223
theorem B4781531 : Blo 1887435 4781531 := bstep (se 1 (by rfl) ⟨3586148, by rfl⟩ : syracuseStep 4781531 = 7172297) B7172297
theorem B3187687 : Blo 1887435 3187687 := bstep (se 1 (by rfl) ⟨2390765, by rfl⟩ : syracuseStep 3187687 = 4781531) B4781531
theorem B4250249 : Blo 1887435 4250249 := bstep (se 2 (by rfl) ⟨1593843, by rfl⟩ : syracuseStep 4250249 = 3187687) B3187687
theorem B2833499 : Blo 1887435 2833499 := bstep (se 1 (by rfl) ⟨2125124, by rfl⟩ : syracuseStep 2833499 = 4250249) B4250249
theorem B1888999 : Blo 1887435 1888999 := bstep (se 1 (by rfl) ⟨1416749, by rfl⟩ : syracuseStep 1888999 = 2833499) B2833499
theorem B2125129 : Blo 1887435 2125129 := bbase (se 2 (by rfl) ⟨796923, by rfl⟩ : syracuseStep 2125129 = 1593847) (by norm_num)
theorem B2833505 : Blo 1887435 2833505 := bstep (se 2 (by rfl) ⟨1062564, by rfl⟩ : syracuseStep 2833505 = 2125129) B2125129
theorem B1889003 : Blo 1887435 1889003 := bstep (se 1 (by rfl) ⟨1416752, by rfl⟩ : syracuseStep 1889003 = 2833505) B2833505
theorem B3635093 : Blo 1887435 3635093 := bbase (se 6 (by rfl) ⟨85197, by rfl⟩ : syracuseStep 3635093 = 170395) (by norm_num)
theorem B2423395 : Blo 1887435 2423395 := bstep (se 1 (by rfl) ⟨1817546, by rfl⟩ : syracuseStep 2423395 = 3635093) B3635093
theorem B3231193 : Blo 1887435 3231193 := bstep (se 2 (by rfl) ⟨1211697, by rfl⟩ : syracuseStep 3231193 = 2423395) B2423395
theorem B4308257 : Blo 1887435 4308257 := bstep (se 2 (by rfl) ⟨1615596, by rfl⟩ : syracuseStep 4308257 = 3231193) B3231193
theorem B2872171 : Blo 1887435 2872171 := bstep (se 1 (by rfl) ⟨2154128, by rfl⟩ : syracuseStep 2872171 = 4308257) B4308257
theorem B3829561 : Blo 1887435 3829561 := bstep (se 2 (by rfl) ⟨1436085, by rfl⟩ : syracuseStep 3829561 = 2872171) B2872171
theorem B20424325 : Blo 1887435 20424325 := bstep (se 4 (by rfl) ⟨1914780, by rfl⟩ : syracuseStep 20424325 = 3829561) B3829561
theorem B27232433 : Blo 1887435 27232433 := bstep (se 2 (by rfl) ⟨10212162, by rfl⟩ : syracuseStep 27232433 = 20424325) B20424325
theorem B18154955 : Blo 1887435 18154955 := bstep (se 1 (by rfl) ⟨13616216, by rfl⟩ : syracuseStep 18154955 = 27232433) B27232433
theorem B12103303 : Blo 1887435 12103303 := bstep (se 1 (by rfl) ⟨9077477, by rfl⟩ : syracuseStep 12103303 = 18154955) B18154955
theorem B16137737 : Blo 1887435 16137737 := bstep (se 2 (by rfl) ⟨6051651, by rfl⟩ : syracuseStep 16137737 = 12103303) B12103303
theorem B10758491 : Blo 1887435 10758491 := bstep (se 1 (by rfl) ⟨8068868, by rfl⟩ : syracuseStep 10758491 = 16137737) B16137737
theorem B7172327 : Blo 1887435 7172327 := bstep (se 1 (by rfl) ⟨5379245, by rfl⟩ : syracuseStep 7172327 = 10758491) B10758491
theorem B4781551 : Blo 1887435 4781551 := bstep (se 1 (by rfl) ⟨3586163, by rfl⟩ : syracuseStep 4781551 = 7172327) B7172327
theorem B6375401 : Blo 1887435 6375401 := bstep (se 2 (by rfl) ⟨2390775, by rfl⟩ : syracuseStep 6375401 = 4781551) B4781551
theorem B4250267 : Blo 1887435 4250267 := bstep (se 1 (by rfl) ⟨3187700, by rfl⟩ : syracuseStep 4250267 = 6375401) B6375401
theorem B2833511 : Blo 1887435 2833511 := bstep (se 1 (by rfl) ⟨2125133, by rfl⟩ : syracuseStep 2833511 = 4250267) B4250267
theorem B1889007 : Blo 1887435 1889007 := bstep (se 1 (by rfl) ⟨1416755, by rfl⟩ : syracuseStep 1889007 = 2833511) B2833511
theorem B2833517 : Blo 1887435 2833517 := bbase (se 3 (by rfl) ⟨531284, by rfl⟩ : syracuseStep 2833517 = 1062569) (by norm_num)
theorem B1889011 : Blo 1887435 1889011 := bstep (se 1 (by rfl) ⟨1416758, by rfl⟩ : syracuseStep 1889011 = 2833517) B2833517
theorem B4250285 : Blo 1887435 4250285 := bbase (se 3 (by rfl) ⟨796928, by rfl⟩ : syracuseStep 4250285 = 1593857) (by norm_num)
theorem B2833523 : Blo 1887435 2833523 := bstep (se 1 (by rfl) ⟨2125142, by rfl⟩ : syracuseStep 2833523 = 4250285) B4250285
theorem B1889015 : Blo 1887435 1889015 := bstep (se 1 (by rfl) ⟨1416761, by rfl⟩ : syracuseStep 1889015 = 2833523) B2833523
theorem B4034461 : Blo 1887435 4034461 := bbase (se 3 (by rfl) ⟨756461, by rfl⟩ : syracuseStep 4034461 = 1512923) (by norm_num)
theorem B5379281 : Blo 1887435 5379281 := bstep (se 2 (by rfl) ⟨2017230, by rfl⟩ : syracuseStep 5379281 = 4034461) B4034461
theorem B3586187 : Blo 1887435 3586187 := bstep (se 1 (by rfl) ⟨2689640, by rfl⟩ : syracuseStep 3586187 = 5379281) B5379281
theorem B2390791 : Blo 1887435 2390791 := bstep (se 1 (by rfl) ⟨1793093, by rfl⟩ : syracuseStep 2390791 = 3586187) B3586187
theorem B3187721 : Blo 1887435 3187721 := bstep (se 2 (by rfl) ⟨1195395, by rfl⟩ : syracuseStep 3187721 = 2390791) B2390791
theorem B2125147 : Blo 1887435 2125147 := bstep (se 1 (by rfl) ⟨1593860, by rfl⟩ : syracuseStep 2125147 = 3187721) B3187721
theorem B2833529 : Blo 1887435 2833529 := bstep (se 2 (by rfl) ⟨1062573, by rfl⟩ : syracuseStep 2833529 = 2125147) B2125147
theorem B1889019 : Blo 1887435 1889019 := bstep (se 1 (by rfl) ⟨1416764, by rfl⟩ : syracuseStep 1889019 = 2833529) B2833529
theorem B27232661 : Blo 1887435 27232661 := bbase (se 6 (by rfl) ⟨638265, by rfl⟩ : syracuseStep 27232661 = 1276531) (by norm_num)
theorem B18155107 : Blo 1887435 18155107 := bstep (se 1 (by rfl) ⟨13616330, by rfl⟩ : syracuseStep 18155107 = 27232661) B27232661
theorem B24206809 : Blo 1887435 24206809 := bstep (se 2 (by rfl) ⟨9077553, by rfl⟩ : syracuseStep 24206809 = 18155107) B18155107
theorem B32275745 : Blo 1887435 32275745 := bstep (se 2 (by rfl) ⟨12103404, by rfl⟩ : syracuseStep 32275745 = 24206809) B24206809
theorem B21517163 : Blo 1887435 21517163 := bstep (se 1 (by rfl) ⟨16137872, by rfl⟩ : syracuseStep 21517163 = 32275745) B32275745
theorem B14344775 : Blo 1887435 14344775 := bstep (se 1 (by rfl) ⟨10758581, by rfl⟩ : syracuseStep 14344775 = 21517163) B21517163
theorem B9563183 : Blo 1887435 9563183 := bstep (se 1 (by rfl) ⟨7172387, by rfl⟩ : syracuseStep 9563183 = 14344775) B14344775
theorem B6375455 : Blo 1887435 6375455 := bstep (se 1 (by rfl) ⟨4781591, by rfl⟩ : syracuseStep 6375455 = 9563183) B9563183
theorem B4250303 : Blo 1887435 4250303 := bstep (se 1 (by rfl) ⟨3187727, by rfl⟩ : syracuseStep 4250303 = 6375455) B6375455
theorem B2833535 : Blo 1887435 2833535 := bstep (se 1 (by rfl) ⟨2125151, by rfl⟩ : syracuseStep 2833535 = 4250303) B4250303
theorem B1889023 : Blo 1887435 1889023 := bstep (se 1 (by rfl) ⟨1416767, by rfl⟩ : syracuseStep 1889023 = 2833535) B2833535
theorem B2833541 : Blo 1887435 2833541 := bbase (se 4 (by rfl) ⟨265644, by rfl⟩ : syracuseStep 2833541 = 531289) (by norm_num)
theorem B1889027 : Blo 1887435 1889027 := bstep (se 1 (by rfl) ⟨1416770, by rfl⟩ : syracuseStep 1889027 = 2833541) B2833541
theorem B3187741 : Blo 1887435 3187741 := bbase (se 3 (by rfl) ⟨597701, by rfl⟩ : syracuseStep 3187741 = 1195403) (by norm_num)
theorem B4250321 : Blo 1887435 4250321 := bstep (se 2 (by rfl) ⟨1593870, by rfl⟩ : syracuseStep 4250321 = 3187741) B3187741
theorem B2833547 : Blo 1887435 2833547 := bstep (se 1 (by rfl) ⟨2125160, by rfl⟩ : syracuseStep 2833547 = 4250321) B4250321
theorem B1889031 : Blo 1887435 1889031 := bstep (se 1 (by rfl) ⟨1416773, by rfl⟩ : syracuseStep 1889031 = 2833547) B2833547
theorem B2125165 : Blo 1887435 2125165 := bbase (se 3 (by rfl) ⟨398468, by rfl⟩ : syracuseStep 2125165 = 796937) (by norm_num)
theorem B2833553 : Blo 1887435 2833553 := bstep (se 2 (by rfl) ⟨1062582, by rfl⟩ : syracuseStep 2833553 = 2125165) B2125165
theorem B1889035 : Blo 1887435 1889035 := bstep (se 1 (by rfl) ⟨1416776, by rfl⟩ : syracuseStep 1889035 = 2833553) B2833553
theorem B6375509 : Blo 1887435 6375509 := bbase (se 8 (by rfl) ⟨37356, by rfl⟩ : syracuseStep 6375509 = 74713) (by norm_num)
theorem B4250339 : Blo 1887435 4250339 := bstep (se 1 (by rfl) ⟨3187754, by rfl⟩ : syracuseStep 4250339 = 6375509) B6375509
theorem B2833559 : Blo 1887435 2833559 := bstep (se 1 (by rfl) ⟨2125169, by rfl⟩ : syracuseStep 2833559 = 4250339) B4250339
theorem B1889039 : Blo 1887435 1889039 := bstep (se 1 (by rfl) ⟨1416779, by rfl⟩ : syracuseStep 1889039 = 2833559) B2833559
theorem B2833565 : Blo 1887435 2833565 := bbase (se 3 (by rfl) ⟨531293, by rfl⟩ : syracuseStep 2833565 = 1062587) (by norm_num)
theorem B1889043 : Blo 1887435 1889043 := bstep (se 1 (by rfl) ⟨1416782, by rfl⟩ : syracuseStep 1889043 = 2833565) B2833565
theorem B4250357 : Blo 1887435 4250357 := bbase (se 5 (by rfl) ⟨199235, by rfl⟩ : syracuseStep 4250357 = 398471) (by norm_num)
theorem B2833571 : Blo 1887435 2833571 := bstep (se 1 (by rfl) ⟨2125178, by rfl⟩ : syracuseStep 2833571 = 4250357) B4250357
theorem B1889047 : Blo 1887435 1889047 := bstep (se 1 (by rfl) ⟨1416785, by rfl⟩ : syracuseStep 1889047 = 2833571) B2833571
theorem B4538845 : Blo 1887435 4538845 := bbase (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) (by norm_num)
theorem B24207173 : Blo 1887435 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B16138115 : Blo 1887435 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B10758743 : Blo 1887435 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B7172495 : Blo 1887435 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B4781663 : Blo 1887435 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B3187775 : Blo 1887435 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B2125183 : Blo 1887435 2125183 := bstep (se 1 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 2125183 = 3187775) B3187775
theorem B2833577 : Blo 1887435 2833577 := bstep (se 2 (by rfl) ⟨1062591, by rfl⟩ : syracuseStep 2833577 = 2125183) B2125183
theorem B1889051 : Blo 1887435 1889051 := bstep (se 1 (by rfl) ⟨1416788, by rfl⟩ : syracuseStep 1889051 = 2833577) B2833577
theorem B2726389 : Blo 1887435 2726389 := bbase (se 5 (by rfl) ⟨127799, by rfl⟩ : syracuseStep 2726389 = 255599) (by norm_num)
theorem B14540741 : Blo 1887435 14540741 := bstep (se 4 (by rfl) ⟨1363194, by rfl⟩ : syracuseStep 14540741 = 2726389) B2726389
theorem B9693827 : Blo 1887435 9693827 := bstep (se 1 (by rfl) ⟨7270370, by rfl⟩ : syracuseStep 9693827 = 14540741) B14540741
theorem B6462551 : Blo 1887435 6462551 := bstep (se 1 (by rfl) ⟨4846913, by rfl⟩ : syracuseStep 6462551 = 9693827) B9693827
theorem B17233469 : Blo 1887435 17233469 := bstep (se 3 (by rfl) ⟨3231275, by rfl⟩ : syracuseStep 17233469 = 6462551) B6462551
theorem B11488979 : Blo 1887435 11488979 := bstep (se 1 (by rfl) ⟨8616734, by rfl⟩ : syracuseStep 11488979 = 17233469) B17233469
theorem B7659319 : Blo 1887435 7659319 := bstep (se 1 (by rfl) ⟨5744489, by rfl⟩ : syracuseStep 7659319 = 11488979) B11488979
theorem B10212425 : Blo 1887435 10212425 := bstep (se 2 (by rfl) ⟨3829659, by rfl⟩ : syracuseStep 10212425 = 7659319) B7659319
theorem B6808283 : Blo 1887435 6808283 := bstep (se 1 (by rfl) ⟨5106212, by rfl⟩ : syracuseStep 6808283 = 10212425) B10212425
theorem B4538855 : Blo 1887435 4538855 := bstep (se 1 (by rfl) ⟨3404141, by rfl⟩ : syracuseStep 4538855 = 6808283) B6808283
theorem B3025903 : Blo 1887435 3025903 := bstep (se 1 (by rfl) ⟨2269427, by rfl⟩ : syracuseStep 3025903 = 4538855) B4538855
theorem B4034537 : Blo 1887435 4034537 := bstep (se 2 (by rfl) ⟨1512951, by rfl⟩ : syracuseStep 4034537 = 3025903) B3025903
theorem B2689691 : Blo 1887435 2689691 := bstep (se 1 (by rfl) ⟨2017268, by rfl⟩ : syracuseStep 2689691 = 4034537) B4034537
theorem B7172509 : Blo 1887435 7172509 := bstep (se 3 (by rfl) ⟨1344845, by rfl⟩ : syracuseStep 7172509 = 2689691) B2689691
theorem B9563345 : Blo 1887435 9563345 := bstep (se 2 (by rfl) ⟨3586254, by rfl⟩ : syracuseStep 9563345 = 7172509) B7172509
theorem B6375563 : Blo 1887435 6375563 := bstep (se 1 (by rfl) ⟨4781672, by rfl⟩ : syracuseStep 6375563 = 9563345) B9563345
theorem B4250375 : Blo 1887435 4250375 := bstep (se 1 (by rfl) ⟨3187781, by rfl⟩ : syracuseStep 4250375 = 6375563) B6375563
theorem B2833583 : Blo 1887435 2833583 := bstep (se 1 (by rfl) ⟨2125187, by rfl⟩ : syracuseStep 2833583 = 4250375) B4250375
theorem B1889055 : Blo 1887435 1889055 := bstep (se 1 (by rfl) ⟨1416791, by rfl⟩ : syracuseStep 1889055 = 2833583) B2833583
theorem B2833589 : Blo 1887435 2833589 := bbase (se 5 (by rfl) ⟨132824, by rfl⟩ : syracuseStep 2833589 = 265649) (by norm_num)
theorem B1889059 : Blo 1887435 1889059 := bstep (se 1 (by rfl) ⟨1416794, by rfl⟩ : syracuseStep 1889059 = 2833589) B2833589
theorem B4781693 : Blo 1887435 4781693 := bbase (se 3 (by rfl) ⟨896567, by rfl⟩ : syracuseStep 4781693 = 1793135) (by norm_num)
theorem B3187795 : Blo 1887435 3187795 := bstep (se 1 (by rfl) ⟨2390846, by rfl⟩ : syracuseStep 3187795 = 4781693) B4781693
theorem B4250393 : Blo 1887435 4250393 := bstep (se 2 (by rfl) ⟨1593897, by rfl⟩ : syracuseStep 4250393 = 3187795) B3187795
theorem B2833595 : Blo 1887435 2833595 := bstep (se 1 (by rfl) ⟨2125196, by rfl⟩ : syracuseStep 2833595 = 4250393) B4250393
theorem B1889063 : Blo 1887435 1889063 := bstep (se 1 (by rfl) ⟨1416797, by rfl⟩ : syracuseStep 1889063 = 2833595) B2833595
theorem B2125201 : Blo 1887435 2125201 := bbase (se 2 (by rfl) ⟨796950, by rfl⟩ : syracuseStep 2125201 = 1593901) (by norm_num)
theorem B2833601 : Blo 1887435 2833601 := bstep (se 2 (by rfl) ⟨1062600, by rfl⟩ : syracuseStep 2833601 = 2125201) B2125201
theorem B1889067 : Blo 1887435 1889067 := bstep (se 1 (by rfl) ⟨1416800, by rfl⟩ : syracuseStep 1889067 = 2833601) B2833601
theorem B3586285 : Blo 1887435 3586285 := bbase (se 3 (by rfl) ⟨672428, by rfl⟩ : syracuseStep 3586285 = 1344857) (by norm_num)
theorem B4781713 : Blo 1887435 4781713 := bstep (se 2 (by rfl) ⟨1793142, by rfl⟩ : syracuseStep 4781713 = 3586285) B3586285
theorem B6375617 : Blo 1887435 6375617 := bstep (se 2 (by rfl) ⟨2390856, by rfl⟩ : syracuseStep 6375617 = 4781713) B4781713
theorem B4250411 : Blo 1887435 4250411 := bstep (se 1 (by rfl) ⟨3187808, by rfl⟩ : syracuseStep 4250411 = 6375617) B6375617
theorem B2833607 : Blo 1887435 2833607 := bstep (se 1 (by rfl) ⟨2125205, by rfl⟩ : syracuseStep 2833607 = 4250411) B4250411
theorem B1889071 : Blo 1887435 1889071 := bstep (se 1 (by rfl) ⟨1416803, by rfl⟩ : syracuseStep 1889071 = 2833607) B2833607
theorem B2833613 : Blo 1887435 2833613 := bbase (se 3 (by rfl) ⟨531302, by rfl⟩ : syracuseStep 2833613 = 1062605) (by norm_num)
theorem B1889075 : Blo 1887435 1889075 := bstep (se 1 (by rfl) ⟨1416806, by rfl⟩ : syracuseStep 1889075 = 2833613) B2833613
theorem B4250429 : Blo 1887435 4250429 := bbase (se 3 (by rfl) ⟨796955, by rfl⟩ : syracuseStep 4250429 = 1593911) (by norm_num)
theorem B2833619 : Blo 1887435 2833619 := bstep (se 1 (by rfl) ⟨2125214, by rfl⟩ : syracuseStep 2833619 = 4250429) B4250429
theorem B1889079 : Blo 1887435 1889079 := bstep (se 1 (by rfl) ⟨1416809, by rfl⟩ : syracuseStep 1889079 = 2833619) B2833619
theorem B3187829 : Blo 1887435 3187829 := bbase (se 5 (by rfl) ⟨149429, by rfl⟩ : syracuseStep 3187829 = 298859) (by norm_num)
theorem B2125219 : Blo 1887435 2125219 := bstep (se 1 (by rfl) ⟨1593914, by rfl⟩ : syracuseStep 2125219 = 3187829) B3187829
theorem B2833625 : Blo 1887435 2833625 := bstep (se 2 (by rfl) ⟨1062609, by rfl⟩ : syracuseStep 2833625 = 2125219) B2125219
theorem B1889083 : Blo 1887435 1889083 := bstep (se 1 (by rfl) ⟨1416812, by rfl⟩ : syracuseStep 1889083 = 2833625) B2833625
theorem B4034605 : Blo 1887435 4034605 := bbase (se 3 (by rfl) ⟨756488, by rfl⟩ : syracuseStep 4034605 = 1512977) (by norm_num)
theorem B5379473 : Blo 1887435 5379473 := bstep (se 2 (by rfl) ⟨2017302, by rfl⟩ : syracuseStep 5379473 = 4034605) B4034605
theorem B14345261 : Blo 1887435 14345261 := bstep (se 3 (by rfl) ⟨2689736, by rfl⟩ : syracuseStep 14345261 = 5379473) B5379473
theorem B9563507 : Blo 1887435 9563507 := bstep (se 1 (by rfl) ⟨7172630, by rfl⟩ : syracuseStep 9563507 = 14345261) B14345261
theorem B6375671 : Blo 1887435 6375671 := bstep (se 1 (by rfl) ⟨4781753, by rfl⟩ : syracuseStep 6375671 = 9563507) B9563507
theorem B4250447 : Blo 1887435 4250447 := bstep (se 1 (by rfl) ⟨3187835, by rfl⟩ : syracuseStep 4250447 = 6375671) B6375671
theorem B2833631 : Blo 1887435 2833631 := bstep (se 1 (by rfl) ⟨2125223, by rfl⟩ : syracuseStep 2833631 = 4250447) B4250447
theorem B1889087 : Blo 1887435 1889087 := bstep (se 1 (by rfl) ⟨1416815, by rfl⟩ : syracuseStep 1889087 = 2833631) B2833631
theorem B2833637 : Blo 1887435 2833637 := bbase (se 4 (by rfl) ⟨265653, by rfl⟩ : syracuseStep 2833637 = 531307) (by norm_num)
theorem B1889091 : Blo 1887435 1889091 := bstep (se 1 (by rfl) ⟨1416818, by rfl⟩ : syracuseStep 1889091 = 2833637) B2833637
theorem B8616917 : Blo 1887435 8616917 := bbase (se 7 (by rfl) ⟨100979, by rfl⟩ : syracuseStep 8616917 = 201959) (by norm_num)
theorem B5744611 : Blo 1887435 5744611 := bstep (se 1 (by rfl) ⟨4308458, by rfl⟩ : syracuseStep 5744611 = 8616917) B8616917
theorem B30637925 : Blo 1887435 30637925 := bstep (se 4 (by rfl) ⟨2872305, by rfl⟩ : syracuseStep 30637925 = 5744611) B5744611
theorem B20425283 : Blo 1887435 20425283 := bstep (se 1 (by rfl) ⟨15318962, by rfl⟩ : syracuseStep 20425283 = 30637925) B30637925
theorem B13616855 : Blo 1887435 13616855 := bstep (se 1 (by rfl) ⟨10212641, by rfl⟩ : syracuseStep 13616855 = 20425283) B20425283
theorem B9077903 : Blo 1887435 9077903 := bstep (se 1 (by rfl) ⟨6808427, by rfl⟩ : syracuseStep 9077903 = 13616855) B13616855
theorem B6051935 : Blo 1887435 6051935 := bstep (se 1 (by rfl) ⟨4538951, by rfl⟩ : syracuseStep 6051935 = 9077903) B9077903
theorem B4034623 : Blo 1887435 4034623 := bstep (se 1 (by rfl) ⟨3025967, by rfl⟩ : syracuseStep 4034623 = 6051935) B6051935
theorem B5379497 : Blo 1887435 5379497 := bstep (se 2 (by rfl) ⟨2017311, by rfl⟩ : syracuseStep 5379497 = 4034623) B4034623
theorem B3586331 : Blo 1887435 3586331 := bstep (se 1 (by rfl) ⟨2689748, by rfl⟩ : syracuseStep 3586331 = 5379497) B5379497
theorem B2390887 : Blo 1887435 2390887 := bstep (se 1 (by rfl) ⟨1793165, by rfl⟩ : syracuseStep 2390887 = 3586331) B3586331
theorem B3187849 : Blo 1887435 3187849 := bstep (se 2 (by rfl) ⟨1195443, by rfl⟩ : syracuseStep 3187849 = 2390887) B2390887
theorem B4250465 : Blo 1887435 4250465 := bstep (se 2 (by rfl) ⟨1593924, by rfl⟩ : syracuseStep 4250465 = 3187849) B3187849
theorem B2833643 : Blo 1887435 2833643 := bstep (se 1 (by rfl) ⟨2125232, by rfl⟩ : syracuseStep 2833643 = 4250465) B4250465
theorem B1889095 : Blo 1887435 1889095 := bstep (se 1 (by rfl) ⟨1416821, by rfl⟩ : syracuseStep 1889095 = 2833643) B2833643
theorem B2125237 : Blo 1887435 2125237 := bbase (se 5 (by rfl) ⟨99620, by rfl⟩ : syracuseStep 2125237 = 199241) (by norm_num)
theorem B2833649 : Blo 1887435 2833649 := bstep (se 2 (by rfl) ⟨1062618, by rfl⟩ : syracuseStep 2833649 = 2125237) B2125237
theorem B1889099 : Blo 1887435 1889099 := bstep (se 1 (by rfl) ⟨1416824, by rfl⟩ : syracuseStep 1889099 = 2833649) B2833649
theorem B2390897 : Blo 1887435 2390897 := bbase (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) (by norm_num)
theorem B6375725 : Blo 1887435 6375725 := bstep (se 3 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 6375725 = 2390897) B2390897
theorem B4250483 : Blo 1887435 4250483 := bstep (se 1 (by rfl) ⟨3187862, by rfl⟩ : syracuseStep 4250483 = 6375725) B6375725
theorem B2833655 : Blo 1887435 2833655 := bstep (se 1 (by rfl) ⟨2125241, by rfl⟩ : syracuseStep 2833655 = 4250483) B4250483
theorem B1889103 : Blo 1887435 1889103 := bstep (se 1 (by rfl) ⟨1416827, by rfl⟩ : syracuseStep 1889103 = 2833655) B2833655
theorem B2833661 : Blo 1887435 2833661 := bbase (se 3 (by rfl) ⟨531311, by rfl⟩ : syracuseStep 2833661 = 1062623) (by norm_num)
theorem B1889107 : Blo 1887435 1889107 := bstep (se 1 (by rfl) ⟨1416830, by rfl⟩ : syracuseStep 1889107 = 2833661) B2833661
theorem B4250501 : Blo 1887435 4250501 := bbase (se 4 (by rfl) ⟨398484, by rfl⟩ : syracuseStep 4250501 = 796969) (by norm_num)
theorem B2833667 : Blo 1887435 2833667 := bstep (se 1 (by rfl) ⟨2125250, by rfl⟩ : syracuseStep 2833667 = 4250501) B4250501
theorem B1889111 : Blo 1887435 1889111 := bstep (se 1 (by rfl) ⟨1416833, by rfl⟩ : syracuseStep 1889111 = 2833667) B2833667
theorem B2017333 : Blo 1887435 2017333 := bbase (se 5 (by rfl) ⟨94562, by rfl⟩ : syracuseStep 2017333 = 189125) (by norm_num)
theorem B2689777 : Blo 1887435 2689777 := bstep (se 2 (by rfl) ⟨1008666, by rfl⟩ : syracuseStep 2689777 = 2017333) B2017333
theorem B3586369 : Blo 1887435 3586369 := bstep (se 2 (by rfl) ⟨1344888, by rfl⟩ : syracuseStep 3586369 = 2689777) B2689777
theorem B4781825 : Blo 1887435 4781825 := bstep (se 2 (by rfl) ⟨1793184, by rfl⟩ : syracuseStep 4781825 = 3586369) B3586369
theorem B3187883 : Blo 1887435 3187883 := bstep (se 1 (by rfl) ⟨2390912, by rfl⟩ : syracuseStep 3187883 = 4781825) B4781825
theorem B2125255 : Blo 1887435 2125255 := bstep (se 1 (by rfl) ⟨1593941, by rfl⟩ : syracuseStep 2125255 = 3187883) B3187883
theorem B2833673 : Blo 1887435 2833673 := bstep (se 2 (by rfl) ⟨1062627, by rfl⟩ : syracuseStep 2833673 = 2125255) B2125255
theorem B1889115 : Blo 1887435 1889115 := bstep (se 1 (by rfl) ⟨1416836, by rfl⟩ : syracuseStep 1889115 = 2833673) B2833673
theorem B9563669 : Blo 1887435 9563669 := bbase (se 6 (by rfl) ⟨224148, by rfl⟩ : syracuseStep 9563669 = 448297) (by norm_num)
theorem B6375779 : Blo 1887435 6375779 := bstep (se 1 (by rfl) ⟨4781834, by rfl⟩ : syracuseStep 6375779 = 9563669) B9563669
theorem B4250519 : Blo 1887435 4250519 := bstep (se 1 (by rfl) ⟨3187889, by rfl⟩ : syracuseStep 4250519 = 6375779) B6375779
theorem B2833679 : Blo 1887435 2833679 := bstep (se 1 (by rfl) ⟨2125259, by rfl⟩ : syracuseStep 2833679 = 4250519) B4250519
theorem B1889119 : Blo 1887435 1889119 := bstep (se 1 (by rfl) ⟨1416839, by rfl⟩ : syracuseStep 1889119 = 2833679) B2833679
theorem B2833685 : Blo 1887435 2833685 := bbase (se 6 (by rfl) ⟨66414, by rfl⟩ : syracuseStep 2833685 = 132829) (by norm_num)
theorem B1889123 : Blo 1887435 1889123 := bstep (se 1 (by rfl) ⟨1416842, by rfl⟩ : syracuseStep 1889123 = 2833685) B2833685
theorem B3829805 : Blo 1887435 3829805 := bbase (se 3 (by rfl) ⟨718088, by rfl⟩ : syracuseStep 3829805 = 1436177) (by norm_num)
theorem B2553203 : Blo 1887435 2553203 := bstep (se 1 (by rfl) ⟨1914902, by rfl⟩ : syracuseStep 2553203 = 3829805) B3829805
theorem B6808541 : Blo 1887435 6808541 := bstep (se 3 (by rfl) ⟨1276601, by rfl⟩ : syracuseStep 6808541 = 2553203) B2553203
theorem B18156109 : Blo 1887435 18156109 := bstep (se 3 (by rfl) ⟨3404270, by rfl⟩ : syracuseStep 18156109 = 6808541) B6808541
theorem B24208145 : Blo 1887435 24208145 := bstep (se 2 (by rfl) ⟨9078054, by rfl⟩ : syracuseStep 24208145 = 18156109) B18156109
theorem B16138763 : Blo 1887435 16138763 := bstep (se 1 (by rfl) ⟨12104072, by rfl⟩ : syracuseStep 16138763 = 24208145) B24208145
theorem B10759175 : Blo 1887435 10759175 := bstep (se 1 (by rfl) ⟨8069381, by rfl⟩ : syracuseStep 10759175 = 16138763) B16138763
theorem B7172783 : Blo 1887435 7172783 := bstep (se 1 (by rfl) ⟨5379587, by rfl⟩ : syracuseStep 7172783 = 10759175) B10759175
theorem B4781855 : Blo 1887435 4781855 := bstep (se 1 (by rfl) ⟨3586391, by rfl⟩ : syracuseStep 4781855 = 7172783) B7172783
theorem B3187903 : Blo 1887435 3187903 := bstep (se 1 (by rfl) ⟨2390927, by rfl⟩ : syracuseStep 3187903 = 4781855) B4781855
theorem B4250537 : Blo 1887435 4250537 := bstep (se 2 (by rfl) ⟨1593951, by rfl⟩ : syracuseStep 4250537 = 3187903) B3187903
theorem B2833691 : Blo 1887435 2833691 := bstep (se 1 (by rfl) ⟨2125268, by rfl⟩ : syracuseStep 2833691 = 4250537) B4250537
theorem B1889127 : Blo 1887435 1889127 := bstep (se 1 (by rfl) ⟨1416845, by rfl⟩ : syracuseStep 1889127 = 2833691) B2833691
theorem B2125273 : Blo 1887435 2125273 := bbase (se 2 (by rfl) ⟨796977, by rfl⟩ : syracuseStep 2125273 = 1593955) (by norm_num)
theorem B2833697 : Blo 1887435 2833697 := bstep (se 2 (by rfl) ⟨1062636, by rfl⟩ : syracuseStep 2833697 = 2125273) B2125273
theorem B1889131 : Blo 1887435 1889131 := bstep (se 1 (by rfl) ⟨1416848, by rfl⟩ : syracuseStep 1889131 = 2833697) B2833697
theorem B2689805 : Blo 1887435 2689805 := bbase (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) (by norm_num)
theorem B7172813 : Blo 1887435 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B4781875 : Blo 1887435 4781875 := bstep (se 1 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 4781875 = 7172813) B7172813
theorem B6375833 : Blo 1887435 6375833 := bstep (se 2 (by rfl) ⟨2390937, by rfl⟩ : syracuseStep 6375833 = 4781875) B4781875
theorem B4250555 : Blo 1887435 4250555 := bstep (se 1 (by rfl) ⟨3187916, by rfl⟩ : syracuseStep 4250555 = 6375833) B6375833
theorem B2833703 : Blo 1887435 2833703 := bstep (se 1 (by rfl) ⟨2125277, by rfl⟩ : syracuseStep 2833703 = 4250555) B4250555
theorem B1889135 : Blo 1887435 1889135 := bstep (se 1 (by rfl) ⟨1416851, by rfl⟩ : syracuseStep 1889135 = 2833703) B2833703
theorem B2833709 : Blo 1887435 2833709 := bbase (se 3 (by rfl) ⟨531320, by rfl⟩ : syracuseStep 2833709 = 1062641) (by norm_num)
theorem B1889139 : Blo 1887435 1889139 := bstep (se 1 (by rfl) ⟨1416854, by rfl⟩ : syracuseStep 1889139 = 2833709) B2833709
theorem B4250573 : Blo 1887435 4250573 := bbase (se 3 (by rfl) ⟨796982, by rfl⟩ : syracuseStep 4250573 = 1593965) (by norm_num)
theorem B2833715 : Blo 1887435 2833715 := bstep (se 1 (by rfl) ⟨2125286, by rfl⟩ : syracuseStep 2833715 = 4250573) B4250573
theorem B1889143 : Blo 1887435 1889143 := bstep (se 1 (by rfl) ⟨1416857, by rfl⟩ : syracuseStep 1889143 = 2833715) B2833715
theorem B2390953 : Blo 1887435 2390953 := bbase (se 2 (by rfl) ⟨896607, by rfl⟩ : syracuseStep 2390953 = 1793215) (by norm_num)
theorem B3187937 : Blo 1887435 3187937 := bstep (se 2 (by rfl) ⟨1195476, by rfl⟩ : syracuseStep 3187937 = 2390953) B2390953
theorem B2125291 : Blo 1887435 2125291 := bstep (se 1 (by rfl) ⟨1593968, by rfl⟩ : syracuseStep 2125291 = 3187937) B3187937
theorem B2833721 : Blo 1887435 2833721 := bstep (se 2 (by rfl) ⟨1062645, by rfl⟩ : syracuseStep 2833721 = 2125291) B2125291
theorem B1889147 : Blo 1887435 1889147 := bstep (se 1 (by rfl) ⟨1416860, by rfl⟩ : syracuseStep 1889147 = 2833721) B2833721
theorem B3829853 : Blo 1887435 3829853 := bbase (se 3 (by rfl) ⟨718097, by rfl⟩ : syracuseStep 3829853 = 1436195) (by norm_num)
theorem B10212941 : Blo 1887435 10212941 := bstep (se 3 (by rfl) ⟨1914926, by rfl⟩ : syracuseStep 10212941 = 3829853) B3829853
theorem B6808627 : Blo 1887435 6808627 := bstep (se 1 (by rfl) ⟨5106470, by rfl⟩ : syracuseStep 6808627 = 10212941) B10212941
theorem B9078169 : Blo 1887435 9078169 := bstep (se 2 (by rfl) ⟨3404313, by rfl⟩ : syracuseStep 9078169 = 6808627) B6808627
theorem B12104225 : Blo 1887435 12104225 := bstep (se 2 (by rfl) ⟨4539084, by rfl⟩ : syracuseStep 12104225 = 9078169) B9078169
theorem B8069483 : Blo 1887435 8069483 := bstep (se 1 (by rfl) ⟨6052112, by rfl⟩ : syracuseStep 8069483 = 12104225) B12104225
theorem B21518621 : Blo 1887435 21518621 := bstep (se 3 (by rfl) ⟨4034741, by rfl⟩ : syracuseStep 21518621 = 8069483) B8069483
theorem B14345747 : Blo 1887435 14345747 := bstep (se 1 (by rfl) ⟨10759310, by rfl⟩ : syracuseStep 14345747 = 21518621) B21518621
theorem B9563831 : Blo 1887435 9563831 := bstep (se 1 (by rfl) ⟨7172873, by rfl⟩ : syracuseStep 9563831 = 14345747) B14345747
theorem B6375887 : Blo 1887435 6375887 := bstep (se 1 (by rfl) ⟨4781915, by rfl⟩ : syracuseStep 6375887 = 9563831) B9563831
theorem B4250591 : Blo 1887435 4250591 := bstep (se 1 (by rfl) ⟨3187943, by rfl⟩ : syracuseStep 4250591 = 6375887) B6375887
theorem B2833727 : Blo 1887435 2833727 := bstep (se 1 (by rfl) ⟨2125295, by rfl⟩ : syracuseStep 2833727 = 4250591) B4250591
theorem B1889151 : Blo 1887435 1889151 := bstep (se 1 (by rfl) ⟨1416863, by rfl⟩ : syracuseStep 1889151 = 2833727) B2833727
theorem B2833733 : Blo 1887435 2833733 := bbase (se 4 (by rfl) ⟨265662, by rfl⟩ : syracuseStep 2833733 = 531325) (by norm_num)
theorem B1889155 : Blo 1887435 1889155 := bstep (se 1 (by rfl) ⟨1416866, by rfl⟩ : syracuseStep 1889155 = 2833733) B2833733
theorem B3187957 : Blo 1887435 3187957 := bbase (se 5 (by rfl) ⟨149435, by rfl⟩ : syracuseStep 3187957 = 298871) (by norm_num)
theorem B4250609 : Blo 1887435 4250609 := bstep (se 2 (by rfl) ⟨1593978, by rfl⟩ : syracuseStep 4250609 = 3187957) B3187957
theorem B2833739 : Blo 1887435 2833739 := bstep (se 1 (by rfl) ⟨2125304, by rfl⟩ : syracuseStep 2833739 = 4250609) B4250609
theorem B1889159 : Blo 1887435 1889159 := bstep (se 1 (by rfl) ⟨1416869, by rfl⟩ : syracuseStep 1889159 = 2833739) B2833739
theorem B2125309 : Blo 1887435 2125309 := bbase (se 3 (by rfl) ⟨398495, by rfl⟩ : syracuseStep 2125309 = 796991) (by norm_num)
theorem B2833745 : Blo 1887435 2833745 := bstep (se 2 (by rfl) ⟨1062654, by rfl⟩ : syracuseStep 2833745 = 2125309) B2125309
theorem B1889163 : Blo 1887435 1889163 := bstep (se 1 (by rfl) ⟨1416872, by rfl⟩ : syracuseStep 1889163 = 2833745) B2833745
theorem B6375941 : Blo 1887435 6375941 := bbase (se 4 (by rfl) ⟨597744, by rfl⟩ : syracuseStep 6375941 = 1195489) (by norm_num)
theorem B4250627 : Blo 1887435 4250627 := bstep (se 1 (by rfl) ⟨3187970, by rfl⟩ : syracuseStep 4250627 = 6375941) B6375941
theorem B2833751 : Blo 1887435 2833751 := bstep (se 1 (by rfl) ⟨2125313, by rfl⟩ : syracuseStep 2833751 = 4250627) B4250627
theorem B1889167 : Blo 1887435 1889167 := bstep (se 1 (by rfl) ⟨1416875, by rfl⟩ : syracuseStep 1889167 = 2833751) B2833751
theorem B2833757 : Blo 1887435 2833757 := bbase (se 3 (by rfl) ⟨531329, by rfl⟩ : syracuseStep 2833757 = 1062659) (by norm_num)
theorem B1889171 : Blo 1887435 1889171 := bstep (se 1 (by rfl) ⟨1416878, by rfl⟩ : syracuseStep 1889171 = 2833757) B2833757
theorem B4250645 : Blo 1887435 4250645 := bbase (se 6 (by rfl) ⟨99624, by rfl⟩ : syracuseStep 4250645 = 199249) (by norm_num)
theorem B2833763 : Blo 1887435 2833763 := bstep (se 1 (by rfl) ⟨2125322, by rfl⟩ : syracuseStep 2833763 = 4250645) B4250645
theorem B1889175 : Blo 1887435 1889175 := bstep (se 1 (by rfl) ⟨1416881, by rfl⟩ : syracuseStep 1889175 = 2833763) B2833763
theorem B7172981 : Blo 1887435 7172981 := bbase (se 5 (by rfl) ⟨336233, by rfl⟩ : syracuseStep 7172981 = 672467) (by norm_num)
theorem B4781987 : Blo 1887435 4781987 := bstep (se 1 (by rfl) ⟨3586490, by rfl⟩ : syracuseStep 4781987 = 7172981) B7172981
theorem B3187991 : Blo 1887435 3187991 := bstep (se 1 (by rfl) ⟨2390993, by rfl⟩ : syracuseStep 3187991 = 4781987) B4781987
theorem B2125327 : Blo 1887435 2125327 := bstep (se 1 (by rfl) ⟨1593995, by rfl⟩ : syracuseStep 2125327 = 3187991) B3187991
theorem B2833769 : Blo 1887435 2833769 := bstep (se 2 (by rfl) ⟨1062663, by rfl⟩ : syracuseStep 2833769 = 2125327) B2125327
theorem B1889179 : Blo 1887435 1889179 := bstep (se 1 (by rfl) ⟨1416884, by rfl⟩ : syracuseStep 1889179 = 2833769) B2833769
theorem B2017405 : Blo 1887435 2017405 := bbase (se 3 (by rfl) ⟨378263, by rfl⟩ : syracuseStep 2017405 = 756527) (by norm_num)
theorem B10759493 : Blo 1887435 10759493 := bstep (se 4 (by rfl) ⟨1008702, by rfl⟩ : syracuseStep 10759493 = 2017405) B2017405
theorem B7172995 : Blo 1887435 7172995 := bstep (se 1 (by rfl) ⟨5379746, by rfl⟩ : syracuseStep 7172995 = 10759493) B10759493
theorem B9563993 : Blo 1887435 9563993 := bstep (se 2 (by rfl) ⟨3586497, by rfl⟩ : syracuseStep 9563993 = 7172995) B7172995
theorem B6375995 : Blo 1887435 6375995 := bstep (se 1 (by rfl) ⟨4781996, by rfl⟩ : syracuseStep 6375995 = 9563993) B9563993
theorem B4250663 : Blo 1887435 4250663 := bstep (se 1 (by rfl) ⟨3187997, by rfl⟩ : syracuseStep 4250663 = 6375995) B6375995
theorem B2833775 : Blo 1887435 2833775 := bstep (se 1 (by rfl) ⟨2125331, by rfl⟩ : syracuseStep 2833775 = 4250663) B4250663
theorem B1889183 : Blo 1887435 1889183 := bstep (se 1 (by rfl) ⟨1416887, by rfl⟩ : syracuseStep 1889183 = 2833775) B2833775
theorem B2833781 : Blo 1887435 2833781 := bbase (se 5 (by rfl) ⟨132833, by rfl⟩ : syracuseStep 2833781 = 265667) (by norm_num)
theorem B1889187 : Blo 1887435 1889187 := bstep (se 1 (by rfl) ⟨1416890, by rfl⟩ : syracuseStep 1889187 = 2833781) B2833781
theorem B2689885 : Blo 1887435 2689885 := bbase (se 3 (by rfl) ⟨504353, by rfl⟩ : syracuseStep 2689885 = 1008707) (by norm_num)
theorem B3586513 : Blo 1887435 3586513 := bstep (se 2 (by rfl) ⟨1344942, by rfl⟩ : syracuseStep 3586513 = 2689885) B2689885
theorem B4782017 : Blo 1887435 4782017 := bstep (se 2 (by rfl) ⟨1793256, by rfl⟩ : syracuseStep 4782017 = 3586513) B3586513
theorem B3188011 : Blo 1887435 3188011 := bstep (se 1 (by rfl) ⟨2391008, by rfl⟩ : syracuseStep 3188011 = 4782017) B4782017
theorem B4250681 : Blo 1887435 4250681 := bstep (se 2 (by rfl) ⟨1594005, by rfl⟩ : syracuseStep 4250681 = 3188011) B3188011
theorem B2833787 : Blo 1887435 2833787 := bstep (se 1 (by rfl) ⟨2125340, by rfl⟩ : syracuseStep 2833787 = 4250681) B4250681
theorem B1889191 : Blo 1887435 1889191 := bstep (se 1 (by rfl) ⟨1416893, by rfl⟩ : syracuseStep 1889191 = 2833787) B2833787
theorem B2125345 : Blo 1887435 2125345 := bbase (se 2 (by rfl) ⟨797004, by rfl⟩ : syracuseStep 2125345 = 1594009) (by norm_num)
theorem B2833793 : Blo 1887435 2833793 := bstep (se 2 (by rfl) ⟨1062672, by rfl⟩ : syracuseStep 2833793 = 2125345) B2125345
theorem B1889195 : Blo 1887435 1889195 := bstep (se 1 (by rfl) ⟨1416896, by rfl⟩ : syracuseStep 1889195 = 2833793) B2833793
theorem B4782037 : Blo 1887435 4782037 := bbase (se 7 (by rfl) ⟨56039, by rfl⟩ : syracuseStep 4782037 = 112079) (by norm_num)
theorem B6376049 : Blo 1887435 6376049 := bstep (se 2 (by rfl) ⟨2391018, by rfl⟩ : syracuseStep 6376049 = 4782037) B4782037
theorem B4250699 : Blo 1887435 4250699 := bstep (se 1 (by rfl) ⟨3188024, by rfl⟩ : syracuseStep 4250699 = 6376049) B6376049
theorem B2833799 : Blo 1887435 2833799 := bstep (se 1 (by rfl) ⟨2125349, by rfl⟩ : syracuseStep 2833799 = 4250699) B4250699
theorem B1889199 : Blo 1887435 1889199 := bstep (se 1 (by rfl) ⟨1416899, by rfl⟩ : syracuseStep 1889199 = 2833799) B2833799
theorem B2833805 : Blo 1887435 2833805 := bbase (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) (by norm_num)
theorem B1889203 : Blo 1887435 1889203 := bstep (se 1 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 1889203 = 2833805) B2833805
theorem B4250717 : Blo 1887435 4250717 := bbase (se 3 (by rfl) ⟨797009, by rfl⟩ : syracuseStep 4250717 = 1594019) (by norm_num)
theorem B2833811 : Blo 1887435 2833811 := bstep (se 1 (by rfl) ⟨2125358, by rfl⟩ : syracuseStep 2833811 = 4250717) B4250717
theorem B1889207 : Blo 1887435 1889207 := bstep (se 1 (by rfl) ⟨1416905, by rfl⟩ : syracuseStep 1889207 = 2833811) B2833811
theorem B3188045 : Blo 1887435 3188045 := bbase (se 3 (by rfl) ⟨597758, by rfl⟩ : syracuseStep 3188045 = 1195517) (by norm_num)
theorem B2125363 : Blo 1887435 2125363 := bstep (se 1 (by rfl) ⟨1594022, by rfl⟩ : syracuseStep 2125363 = 3188045) B3188045
theorem B2833817 : Blo 1887435 2833817 := bstep (se 2 (by rfl) ⟨1062681, by rfl⟩ : syracuseStep 2833817 = 2125363) B2125363
theorem B1889211 : Blo 1887435 1889211 := bstep (se 1 (by rfl) ⟨1416908, by rfl⟩ : syracuseStep 1889211 = 2833817) B2833817
theorem B14941493 : Blo 1887435 14941493 := bbase (se 5 (by rfl) ⟨700382, by rfl⟩ : syracuseStep 14941493 = 1400765) (by norm_num)
theorem B9960995 : Blo 1887435 9960995 := bstep (se 1 (by rfl) ⟨7470746, by rfl⟩ : syracuseStep 9960995 = 14941493) B14941493
theorem B6640663 : Blo 1887435 6640663 := bstep (se 1 (by rfl) ⟨4980497, by rfl⟩ : syracuseStep 6640663 = 9960995) B9960995
theorem B8854217 : Blo 1887435 8854217 := bstep (se 2 (by rfl) ⟨3320331, by rfl⟩ : syracuseStep 8854217 = 6640663) B6640663
theorem B5902811 : Blo 1887435 5902811 := bstep (se 1 (by rfl) ⟨4427108, by rfl⟩ : syracuseStep 5902811 = 8854217) B8854217
theorem B3935207 : Blo 1887435 3935207 := bstep (se 1 (by rfl) ⟨2951405, by rfl⟩ : syracuseStep 3935207 = 5902811) B5902811
theorem B2623471 : Blo 1887435 2623471 := bstep (se 1 (by rfl) ⟨1967603, by rfl⟩ : syracuseStep 2623471 = 3935207) B3935207
theorem B55967381 : Blo 1887435 55967381 := bstep (se 6 (by rfl) ⟨1311735, by rfl⟩ : syracuseStep 55967381 = 2623471) B2623471
theorem B37311587 : Blo 1887435 37311587 := bstep (se 1 (by rfl) ⟨27983690, by rfl⟩ : syracuseStep 37311587 = 55967381) B55967381
theorem B24874391 : Blo 1887435 24874391 := bstep (se 1 (by rfl) ⟨18655793, by rfl⟩ : syracuseStep 24874391 = 37311587) B37311587
theorem B66331709 : Blo 1887435 66331709 := bstep (se 3 (by rfl) ⟨12437195, by rfl⟩ : syracuseStep 66331709 = 24874391) B24874391
theorem B44221139 : Blo 1887435 44221139 := bstep (se 1 (by rfl) ⟨33165854, by rfl⟩ : syracuseStep 44221139 = 66331709) B66331709
theorem B29480759 : Blo 1887435 29480759 := bstep (se 1 (by rfl) ⟨22110569, by rfl⟩ : syracuseStep 29480759 = 44221139) B44221139
theorem B19653839 : Blo 1887435 19653839 := bstep (se 1 (by rfl) ⟨14740379, by rfl⟩ : syracuseStep 19653839 = 29480759) B29480759
theorem B13102559 : Blo 1887435 13102559 := bstep (se 1 (by rfl) ⟨9826919, by rfl⟩ : syracuseStep 13102559 = 19653839) B19653839
theorem B8735039 : Blo 1887435 8735039 := bstep (se 1 (by rfl) ⟨6551279, by rfl⟩ : syracuseStep 8735039 = 13102559) B13102559
theorem B5823359 : Blo 1887435 5823359 := bstep (se 1 (by rfl) ⟨4367519, by rfl⟩ : syracuseStep 5823359 = 8735039) B8735039
theorem B3882239 : Blo 1887435 3882239 := bstep (se 1 (by rfl) ⟨2911679, by rfl⟩ : syracuseStep 3882239 = 5823359) B5823359
theorem B2588159 : Blo 1887435 2588159 := bstep (se 1 (by rfl) ⟨1941119, by rfl⟩ : syracuseStep 2588159 = 3882239) B3882239
theorem B6901757 : Blo 1887435 6901757 := bstep (se 3 (by rfl) ⟨1294079, by rfl⟩ : syracuseStep 6901757 = 2588159) B2588159
theorem B4601171 : Blo 1887435 4601171 := bstep (se 1 (by rfl) ⟨3450878, by rfl⟩ : syracuseStep 4601171 = 6901757) B6901757
theorem B12269789 : Blo 1887435 12269789 := bstep (se 3 (by rfl) ⟨2300585, by rfl⟩ : syracuseStep 12269789 = 4601171) B4601171
theorem B8179859 : Blo 1887435 8179859 := bstep (se 1 (by rfl) ⟨6134894, by rfl⟩ : syracuseStep 8179859 = 12269789) B12269789
theorem B5453239 : Blo 1887435 5453239 := bstep (se 1 (by rfl) ⟨4089929, by rfl⟩ : syracuseStep 5453239 = 8179859) B8179859
theorem B7270985 : Blo 1887435 7270985 := bstep (se 2 (by rfl) ⟨2726619, by rfl⟩ : syracuseStep 7270985 = 5453239) B5453239
theorem B4847323 : Blo 1887435 4847323 := bstep (se 1 (by rfl) ⟨3635492, by rfl⟩ : syracuseStep 4847323 = 7270985) B7270985
theorem B6463097 : Blo 1887435 6463097 := bstep (se 2 (by rfl) ⟨2423661, by rfl⟩ : syracuseStep 6463097 = 4847323) B4847323
theorem B4308731 : Blo 1887435 4308731 := bstep (se 1 (by rfl) ⟨3231548, by rfl⟩ : syracuseStep 4308731 = 6463097) B6463097
theorem B2872487 : Blo 1887435 2872487 := bstep (se 1 (by rfl) ⟨2154365, by rfl⟩ : syracuseStep 2872487 = 4308731) B4308731
theorem B7659965 : Blo 1887435 7659965 := bstep (se 3 (by rfl) ⟨1436243, by rfl⟩ : syracuseStep 7659965 = 2872487) B2872487
theorem B20426573 : Blo 1887435 20426573 := bstep (se 3 (by rfl) ⟨3829982, by rfl⟩ : syracuseStep 20426573 = 7659965) B7659965
theorem B13617715 : Blo 1887435 13617715 := bstep (se 1 (by rfl) ⟨10213286, by rfl⟩ : syracuseStep 13617715 = 20426573) B20426573
theorem B18156953 : Blo 1887435 18156953 := bstep (se 2 (by rfl) ⟨6808857, by rfl⟩ : syracuseStep 18156953 = 13617715) B13617715
theorem B12104635 : Blo 1887435 12104635 := bstep (se 1 (by rfl) ⟨9078476, by rfl⟩ : syracuseStep 12104635 = 18156953) B18156953
theorem B16139513 : Blo 1887435 16139513 := bstep (se 2 (by rfl) ⟨6052317, by rfl⟩ : syracuseStep 16139513 = 12104635) B12104635
theorem B10759675 : Blo 1887435 10759675 := bstep (se 1 (by rfl) ⟨8069756, by rfl⟩ : syracuseStep 10759675 = 16139513) B16139513
theorem B14346233 : Blo 1887435 14346233 := bstep (se 2 (by rfl) ⟨5379837, by rfl⟩ : syracuseStep 14346233 = 10759675) B10759675
theorem B9564155 : Blo 1887435 9564155 := bstep (se 1 (by rfl) ⟨7173116, by rfl⟩ : syracuseStep 9564155 = 14346233) B14346233
theorem B6376103 : Blo 1887435 6376103 := bstep (se 1 (by rfl) ⟨4782077, by rfl⟩ : syracuseStep 6376103 = 9564155) B9564155
theorem B4250735 : Blo 1887435 4250735 := bstep (se 1 (by rfl) ⟨3188051, by rfl⟩ : syracuseStep 4250735 = 6376103) B6376103
theorem B2833823 : Blo 1887435 2833823 := bstep (se 1 (by rfl) ⟨2125367, by rfl⟩ : syracuseStep 2833823 = 4250735) B4250735
theorem B1889215 : Blo 1887435 1889215 := bstep (se 1 (by rfl) ⟨1416911, by rfl⟩ : syracuseStep 1889215 = 2833823) B2833823
theorem B2833829 : Blo 1887435 2833829 := bbase (se 4 (by rfl) ⟨265671, by rfl⟩ : syracuseStep 2833829 = 531343) (by norm_num)
theorem B1889219 : Blo 1887435 1889219 := bstep (se 1 (by rfl) ⟨1416914, by rfl⟩ : syracuseStep 1889219 = 2833829) B2833829
theorem B2391049 : Blo 1887435 2391049 := bbase (se 2 (by rfl) ⟨896643, by rfl⟩ : syracuseStep 2391049 = 1793287) (by norm_num)
theorem B3188065 : Blo 1887435 3188065 := bstep (se 2 (by rfl) ⟨1195524, by rfl⟩ : syracuseStep 3188065 = 2391049) B2391049
theorem B4250753 : Blo 1887435 4250753 := bstep (se 2 (by rfl) ⟨1594032, by rfl⟩ : syracuseStep 4250753 = 3188065) B3188065
theorem B2833835 : Blo 1887435 2833835 := bstep (se 1 (by rfl) ⟨2125376, by rfl⟩ : syracuseStep 2833835 = 4250753) B4250753
theorem B1889223 : Blo 1887435 1889223 := bstep (se 1 (by rfl) ⟨1416917, by rfl⟩ : syracuseStep 1889223 = 2833835) B2833835
theorem B2125381 : Blo 1887435 2125381 := bbase (se 4 (by rfl) ⟨199254, by rfl⟩ : syracuseStep 2125381 = 398509) (by norm_num)
theorem B2833841 : Blo 1887435 2833841 := bstep (se 2 (by rfl) ⟨1062690, by rfl⟩ : syracuseStep 2833841 = 2125381) B2125381
theorem B1889227 : Blo 1887435 1889227 := bstep (se 1 (by rfl) ⟨1416920, by rfl⟩ : syracuseStep 1889227 = 2833841) B2833841
theorem B3586589 : Blo 1887435 3586589 := bbase (se 3 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 3586589 = 1344971) (by norm_num)
theorem B2391059 : Blo 1887435 2391059 := bstep (se 1 (by rfl) ⟨1793294, by rfl⟩ : syracuseStep 2391059 = 3586589) B3586589
theorem B6376157 : Blo 1887435 6376157 := bstep (se 3 (by rfl) ⟨1195529, by rfl⟩ : syracuseStep 6376157 = 2391059) B2391059
theorem B4250771 : Blo 1887435 4250771 := bstep (se 1 (by rfl) ⟨3188078, by rfl⟩ : syracuseStep 4250771 = 6376157) B6376157
theorem B2833847 : Blo 1887435 2833847 := bstep (se 1 (by rfl) ⟨2125385, by rfl⟩ : syracuseStep 2833847 = 4250771) B4250771
theorem B1889231 : Blo 1887435 1889231 := bstep (se 1 (by rfl) ⟨1416923, by rfl⟩ : syracuseStep 1889231 = 2833847) B2833847
theorem B2833853 : Blo 1887435 2833853 := bbase (se 3 (by rfl) ⟨531347, by rfl⟩ : syracuseStep 2833853 = 1062695) (by norm_num)
theorem B1889235 : Blo 1887435 1889235 := bstep (se 1 (by rfl) ⟨1416926, by rfl⟩ : syracuseStep 1889235 = 2833853) B2833853
theorem B4250789 : Blo 1887435 4250789 := bbase (se 4 (by rfl) ⟨398511, by rfl⟩ : syracuseStep 4250789 = 797023) (by norm_num)
theorem B2833859 : Blo 1887435 2833859 := bstep (se 1 (by rfl) ⟨2125394, by rfl⟩ : syracuseStep 2833859 = 4250789) B4250789
theorem B1889239 : Blo 1887435 1889239 := bstep (se 1 (by rfl) ⟨1416929, by rfl⟩ : syracuseStep 1889239 = 2833859) B2833859
theorem B4782149 : Blo 1887435 4782149 := bbase (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) (by norm_num)
theorem B3188099 : Blo 1887435 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B2125399 : Blo 1887435 2125399 := bstep (se 1 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 2125399 = 3188099) B3188099
theorem B2833865 : Blo 1887435 2833865 := bstep (se 2 (by rfl) ⟨1062699, by rfl⟩ : syracuseStep 2833865 = 2125399) B2125399
theorem B1889243 : Blo 1887435 1889243 := bstep (se 1 (by rfl) ⟨1416932, by rfl⟩ : syracuseStep 1889243 = 2833865) B2833865
theorem B6052421 : Blo 1887435 6052421 := bbase (se 4 (by rfl) ⟨567414, by rfl⟩ : syracuseStep 6052421 = 1134829) (by norm_num)
theorem B4034947 : Blo 1887435 4034947 := bstep (se 1 (by rfl) ⟨3026210, by rfl⟩ : syracuseStep 4034947 = 6052421) B6052421
theorem B5379929 : Blo 1887435 5379929 := bstep (se 2 (by rfl) ⟨2017473, by rfl⟩ : syracuseStep 5379929 = 4034947) B4034947
theorem B3586619 : Blo 1887435 3586619 := bstep (se 1 (by rfl) ⟨2689964, by rfl⟩ : syracuseStep 3586619 = 5379929) B5379929
theorem B9564317 : Blo 1887435 9564317 := bstep (se 3 (by rfl) ⟨1793309, by rfl⟩ : syracuseStep 9564317 = 3586619) B3586619
theorem B6376211 : Blo 1887435 6376211 := bstep (se 1 (by rfl) ⟨4782158, by rfl⟩ : syracuseStep 6376211 = 9564317) B9564317
theorem B4250807 : Blo 1887435 4250807 := bstep (se 1 (by rfl) ⟨3188105, by rfl⟩ : syracuseStep 4250807 = 6376211) B6376211
theorem B2833871 : Blo 1887435 2833871 := bstep (se 1 (by rfl) ⟨2125403, by rfl⟩ : syracuseStep 2833871 = 4250807) B4250807
theorem B1889247 : Blo 1887435 1889247 := bstep (se 1 (by rfl) ⟨1416935, by rfl⟩ : syracuseStep 1889247 = 2833871) B2833871
theorem B2833877 : Blo 1887435 2833877 := bbase (se 7 (by rfl) ⟨33209, by rfl⟩ : syracuseStep 2833877 = 66419) (by norm_num)
theorem B1889251 : Blo 1887435 1889251 := bstep (se 1 (by rfl) ⟨1416938, by rfl⟩ : syracuseStep 1889251 = 2833877) B2833877
theorem B7173269 : Blo 1887435 7173269 := bbase (se 6 (by rfl) ⟨168123, by rfl⟩ : syracuseStep 7173269 = 336247) (by norm_num)
theorem B4782179 : Blo 1887435 4782179 := bstep (se 1 (by rfl) ⟨3586634, by rfl⟩ : syracuseStep 4782179 = 7173269) B7173269
theorem B3188119 : Blo 1887435 3188119 := bstep (se 1 (by rfl) ⟨2391089, by rfl⟩ : syracuseStep 3188119 = 4782179) B4782179
theorem B4250825 : Blo 1887435 4250825 := bstep (se 2 (by rfl) ⟨1594059, by rfl⟩ : syracuseStep 4250825 = 3188119) B3188119
theorem B2833883 : Blo 1887435 2833883 := bstep (se 1 (by rfl) ⟨2125412, by rfl⟩ : syracuseStep 2833883 = 4250825) B4250825
theorem B1889255 : Blo 1887435 1889255 := bstep (se 1 (by rfl) ⟨1416941, by rfl⟩ : syracuseStep 1889255 = 2833883) B2833883
theorem B2125417 : Blo 1887435 2125417 := bbase (se 2 (by rfl) ⟨797031, by rfl⟩ : syracuseStep 2125417 = 1594063) (by norm_num)
theorem B2833889 : Blo 1887435 2833889 := bstep (se 2 (by rfl) ⟨1062708, by rfl⟩ : syracuseStep 2833889 = 2125417) B2125417
theorem B1889259 : Blo 1887435 1889259 := bstep (se 1 (by rfl) ⟨1416944, by rfl⟩ : syracuseStep 1889259 = 2833889) B2833889
theorem B4034981 : Blo 1887435 4034981 := bbase (se 4 (by rfl) ⟨378279, by rfl⟩ : syracuseStep 4034981 = 756559) (by norm_num)
theorem B10759949 : Blo 1887435 10759949 := bstep (se 3 (by rfl) ⟨2017490, by rfl⟩ : syracuseStep 10759949 = 4034981) B4034981
theorem B7173299 : Blo 1887435 7173299 := bstep (se 1 (by rfl) ⟨5379974, by rfl⟩ : syracuseStep 7173299 = 10759949) B10759949
theorem B4782199 : Blo 1887435 4782199 := bstep (se 1 (by rfl) ⟨3586649, by rfl⟩ : syracuseStep 4782199 = 7173299) B7173299
theorem B6376265 : Blo 1887435 6376265 := bstep (se 2 (by rfl) ⟨2391099, by rfl⟩ : syracuseStep 6376265 = 4782199) B4782199
theorem B4250843 : Blo 1887435 4250843 := bstep (se 1 (by rfl) ⟨3188132, by rfl⟩ : syracuseStep 4250843 = 6376265) B6376265
theorem B2833895 : Blo 1887435 2833895 := bstep (se 1 (by rfl) ⟨2125421, by rfl⟩ : syracuseStep 2833895 = 4250843) B4250843
theorem B1889263 : Blo 1887435 1889263 := bstep (se 1 (by rfl) ⟨1416947, by rfl⟩ : syracuseStep 1889263 = 2833895) B2833895
theorem B2833901 : Blo 1887435 2833901 := bbase (se 3 (by rfl) ⟨531356, by rfl⟩ : syracuseStep 2833901 = 1062713) (by norm_num)
theorem B1889267 : Blo 1887435 1889267 := bstep (se 1 (by rfl) ⟨1416950, by rfl⟩ : syracuseStep 1889267 = 2833901) B2833901
theorem B4250861 : Blo 1887435 4250861 := bbase (se 3 (by rfl) ⟨797036, by rfl⟩ : syracuseStep 4250861 = 1594073) (by norm_num)
theorem B2833907 : Blo 1887435 2833907 := bstep (se 1 (by rfl) ⟨2125430, by rfl⟩ : syracuseStep 2833907 = 4250861) B4250861
theorem B1889271 : Blo 1887435 1889271 := bstep (se 1 (by rfl) ⟨1416953, by rfl⟩ : syracuseStep 1889271 = 2833907) B2833907
theorem B2690005 : Blo 1887435 2690005 := bbase (se 7 (by rfl) ⟨31523, by rfl⟩ : syracuseStep 2690005 = 63047) (by norm_num)
theorem B3586673 : Blo 1887435 3586673 := bstep (se 2 (by rfl) ⟨1345002, by rfl⟩ : syracuseStep 3586673 = 2690005) B2690005
theorem B2391115 : Blo 1887435 2391115 := bstep (se 1 (by rfl) ⟨1793336, by rfl⟩ : syracuseStep 2391115 = 3586673) B3586673
theorem B3188153 : Blo 1887435 3188153 := bstep (se 2 (by rfl) ⟨1195557, by rfl⟩ : syracuseStep 3188153 = 2391115) B2391115
theorem B2125435 : Blo 1887435 2125435 := bstep (se 1 (by rfl) ⟨1594076, by rfl⟩ : syracuseStep 2125435 = 3188153) B3188153
theorem B2833913 : Blo 1887435 2833913 := bstep (se 2 (by rfl) ⟨1062717, by rfl⟩ : syracuseStep 2833913 = 2125435) B2125435
theorem B1889275 : Blo 1887435 1889275 := bstep (se 1 (by rfl) ⟨1416956, by rfl⟩ : syracuseStep 1889275 = 2833913) B2833913
theorem B41976917 : Blo 1887435 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B27984611 : Blo 1887435 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B18656407 : Blo 1887435 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B24875209 : Blo 1887435 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B33166945 : Blo 1887435 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B44222593 : Blo 1887435 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B58963457 : Blo 1887435 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B39308971 : Blo 1887435 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B52411961 : Blo 1887435 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B34941307 : Blo 1887435 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B46588409 : Blo 1887435 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B31058939 : Blo 1887435 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B20705959 : Blo 1887435 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B27607945 : Blo 1887435 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B36810593 : Blo 1887435 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B1570585301 : Blo 1887435 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B1047056867 : Blo 1887435 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B698037911 : Blo 1887435 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B465358607 : Blo 1887435 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B310239071 : Blo 1887435 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B206826047 : Blo 1887435 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B137884031 : Blo 1887435 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B91922687 : Blo 1887435 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B61281791 : Blo 1887435 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B40854527 : Blo 1887435 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B27236351 : Blo 1887435 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B72630269 : Blo 1887435 72630269 := bstep (se 3 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 72630269 = 27236351) B27236351
theorem B48420179 : Blo 1887435 48420179 := bstep (se 1 (by rfl) ⟨36315134, by rfl⟩ : syracuseStep 48420179 = 72630269) B72630269
theorem B32280119 : Blo 1887435 32280119 := bstep (se 1 (by rfl) ⟨24210089, by rfl⟩ : syracuseStep 32280119 = 48420179) B48420179
theorem B21520079 : Blo 1887435 21520079 := bstep (se 1 (by rfl) ⟨16140059, by rfl⟩ : syracuseStep 21520079 = 32280119) B32280119
theorem B14346719 : Blo 1887435 14346719 := bstep (se 1 (by rfl) ⟨10760039, by rfl⟩ : syracuseStep 14346719 = 21520079) B21520079
theorem B9564479 : Blo 1887435 9564479 := bstep (se 1 (by rfl) ⟨7173359, by rfl⟩ : syracuseStep 9564479 = 14346719) B14346719
theorem B6376319 : Blo 1887435 6376319 := bstep (se 1 (by rfl) ⟨4782239, by rfl⟩ : syracuseStep 6376319 = 9564479) B9564479
theorem B4250879 : Blo 1887435 4250879 := bstep (se 1 (by rfl) ⟨3188159, by rfl⟩ : syracuseStep 4250879 = 6376319) B6376319
theorem B2833919 : Blo 1887435 2833919 := bstep (se 1 (by rfl) ⟨2125439, by rfl⟩ : syracuseStep 2833919 = 4250879) B4250879
theorem B1889279 : Blo 1887435 1889279 := bstep (se 1 (by rfl) ⟨1416959, by rfl⟩ : syracuseStep 1889279 = 2833919) B2833919
theorem B2833925 : Blo 1887435 2833925 := bbase (se 4 (by rfl) ⟨265680, by rfl⟩ : syracuseStep 2833925 = 531361) (by norm_num)
theorem B1889283 : Blo 1887435 1889283 := bstep (se 1 (by rfl) ⟨1416962, by rfl⟩ : syracuseStep 1889283 = 2833925) B2833925
theorem B3188173 : Blo 1887435 3188173 := bbase (se 3 (by rfl) ⟨597782, by rfl⟩ : syracuseStep 3188173 = 1195565) (by norm_num)
theorem B4250897 : Blo 1887435 4250897 := bstep (se 2 (by rfl) ⟨1594086, by rfl⟩ : syracuseStep 4250897 = 3188173) B3188173
theorem B2833931 : Blo 1887435 2833931 := bstep (se 1 (by rfl) ⟨2125448, by rfl⟩ : syracuseStep 2833931 = 4250897) B4250897
theorem B1889287 : Blo 1887435 1889287 := bstep (se 1 (by rfl) ⟨1416965, by rfl⟩ : syracuseStep 1889287 = 2833931) B2833931
theorem B2125453 : Blo 1887435 2125453 := bbase (se 3 (by rfl) ⟨398522, by rfl⟩ : syracuseStep 2125453 = 797045) (by norm_num)
theorem B2833937 : Blo 1887435 2833937 := bstep (se 2 (by rfl) ⟨1062726, by rfl⟩ : syracuseStep 2833937 = 2125453) B2125453
theorem B1889291 : Blo 1887435 1889291 := bstep (se 1 (by rfl) ⟨1416968, by rfl⟩ : syracuseStep 1889291 = 2833937) B2833937
theorem B6376373 : Blo 1887435 6376373 := bbase (se 5 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 6376373 = 597785) (by norm_num)
theorem B4250915 : Blo 1887435 4250915 := bstep (se 1 (by rfl) ⟨3188186, by rfl⟩ : syracuseStep 4250915 = 6376373) B6376373
theorem B2833943 : Blo 1887435 2833943 := bstep (se 1 (by rfl) ⟨2125457, by rfl⟩ : syracuseStep 2833943 = 4250915) B4250915
theorem B1889295 : Blo 1887435 1889295 := bstep (se 1 (by rfl) ⟨1416971, by rfl⟩ : syracuseStep 1889295 = 2833943) B2833943
theorem B2833949 : Blo 1887435 2833949 := bbase (se 3 (by rfl) ⟨531365, by rfl⟩ : syracuseStep 2833949 = 1062731) (by norm_num)
theorem B1889299 : Blo 1887435 1889299 := bstep (se 1 (by rfl) ⟨1416974, by rfl⟩ : syracuseStep 1889299 = 2833949) B2833949
theorem B4250933 : Blo 1887435 4250933 := bbase (se 5 (by rfl) ⟨199262, by rfl⟩ : syracuseStep 4250933 = 398525) (by norm_num)
theorem B2833955 : Blo 1887435 2833955 := bstep (se 1 (by rfl) ⟨2125466, by rfl⟩ : syracuseStep 2833955 = 4250933) B4250933
theorem B1889303 : Blo 1887435 1889303 := bstep (se 1 (by rfl) ⟨1416977, by rfl⟩ : syracuseStep 1889303 = 2833955) B2833955
theorem B1915085 : Blo 1887435 1915085 := bbase (se 3 (by rfl) ⟨359078, by rfl⟩ : syracuseStep 1915085 = 718157) (by norm_num)
theorem B5106893 : Blo 1887435 5106893 := bstep (se 3 (by rfl) ⟨957542, by rfl⟩ : syracuseStep 5106893 = 1915085) B1915085
theorem B13618381 : Blo 1887435 13618381 := bstep (se 3 (by rfl) ⟨2553446, by rfl⟩ : syracuseStep 13618381 = 5106893) B5106893
theorem B18157841 : Blo 1887435 18157841 := bstep (se 2 (by rfl) ⟨6809190, by rfl⟩ : syracuseStep 18157841 = 13618381) B13618381
theorem B12105227 : Blo 1887435 12105227 := bstep (se 1 (by rfl) ⟨9078920, by rfl⟩ : syracuseStep 12105227 = 18157841) B18157841
theorem B8070151 : Blo 1887435 8070151 := bstep (se 1 (by rfl) ⟨6052613, by rfl⟩ : syracuseStep 8070151 = 12105227) B12105227
theorem B10760201 : Blo 1887435 10760201 := bstep (se 2 (by rfl) ⟨4035075, by rfl⟩ : syracuseStep 10760201 = 8070151) B8070151
theorem B7173467 : Blo 1887435 7173467 := bstep (se 1 (by rfl) ⟨5380100, by rfl⟩ : syracuseStep 7173467 = 10760201) B10760201
theorem B4782311 : Blo 1887435 4782311 := bstep (se 1 (by rfl) ⟨3586733, by rfl⟩ : syracuseStep 4782311 = 7173467) B7173467
theorem B3188207 : Blo 1887435 3188207 := bstep (se 1 (by rfl) ⟨2391155, by rfl⟩ : syracuseStep 3188207 = 4782311) B4782311
theorem B2125471 : Blo 1887435 2125471 := bstep (se 1 (by rfl) ⟨1594103, by rfl⟩ : syracuseStep 2125471 = 3188207) B3188207
theorem B2833961 : Blo 1887435 2833961 := bstep (se 2 (by rfl) ⟨1062735, by rfl⟩ : syracuseStep 2833961 = 2125471) B2125471
theorem B1889307 : Blo 1887435 1889307 := bstep (se 1 (by rfl) ⟨1416980, by rfl⟩ : syracuseStep 1889307 = 2833961) B2833961
theorem B18157877 : Blo 1887435 18157877 := bbase (se 5 (by rfl) ⟨851150, by rfl⟩ : syracuseStep 18157877 = 1702301) (by norm_num)
theorem B12105251 : Blo 1887435 12105251 := bstep (se 1 (by rfl) ⟨9078938, by rfl⟩ : syracuseStep 12105251 = 18157877) B18157877
theorem B8070167 : Blo 1887435 8070167 := bstep (se 1 (by rfl) ⟨6052625, by rfl⟩ : syracuseStep 8070167 = 12105251) B12105251
theorem B5380111 : Blo 1887435 5380111 := bstep (se 1 (by rfl) ⟨4035083, by rfl⟩ : syracuseStep 5380111 = 8070167) B8070167
theorem B7173481 : Blo 1887435 7173481 := bstep (se 2 (by rfl) ⟨2690055, by rfl⟩ : syracuseStep 7173481 = 5380111) B5380111
theorem B9564641 : Blo 1887435 9564641 := bstep (se 2 (by rfl) ⟨3586740, by rfl⟩ : syracuseStep 9564641 = 7173481) B7173481
theorem B6376427 : Blo 1887435 6376427 := bstep (se 1 (by rfl) ⟨4782320, by rfl⟩ : syracuseStep 6376427 = 9564641) B9564641
theorem B4250951 : Blo 1887435 4250951 := bstep (se 1 (by rfl) ⟨3188213, by rfl⟩ : syracuseStep 4250951 = 6376427) B6376427
theorem B2833967 : Blo 1887435 2833967 := bstep (se 1 (by rfl) ⟨2125475, by rfl⟩ : syracuseStep 2833967 = 4250951) B4250951
theorem B1889311 : Blo 1887435 1889311 := bstep (se 1 (by rfl) ⟨1416983, by rfl⟩ : syracuseStep 1889311 = 2833967) B2833967
theorem B2833973 : Blo 1887435 2833973 := bbase (se 5 (by rfl) ⟨132842, by rfl⟩ : syracuseStep 2833973 = 265685) (by norm_num)
theorem B1889315 : Blo 1887435 1889315 := bstep (se 1 (by rfl) ⟨1416986, by rfl⟩ : syracuseStep 1889315 = 2833973) B2833973
theorem B4782341 : Blo 1887435 4782341 := bbase (se 4 (by rfl) ⟨448344, by rfl⟩ : syracuseStep 4782341 = 896689) (by norm_num)
theorem B3188227 : Blo 1887435 3188227 := bstep (se 1 (by rfl) ⟨2391170, by rfl⟩ : syracuseStep 3188227 = 4782341) B4782341
theorem B4250969 : Blo 1887435 4250969 := bstep (se 2 (by rfl) ⟨1594113, by rfl⟩ : syracuseStep 4250969 = 3188227) B3188227
theorem B2833979 : Blo 1887435 2833979 := bstep (se 1 (by rfl) ⟨2125484, by rfl⟩ : syracuseStep 2833979 = 4250969) B4250969
theorem B1889319 : Blo 1887435 1889319 := bstep (se 1 (by rfl) ⟨1416989, by rfl⟩ : syracuseStep 1889319 = 2833979) B2833979
theorem B2125489 : Blo 1887435 2125489 := bbase (se 2 (by rfl) ⟨797058, by rfl⟩ : syracuseStep 2125489 = 1594117) (by norm_num)
theorem B2833985 : Blo 1887435 2833985 := bstep (se 2 (by rfl) ⟨1062744, by rfl⟩ : syracuseStep 2833985 = 2125489) B2125489
theorem B1889323 : Blo 1887435 1889323 := bstep (se 1 (by rfl) ⟨1416992, by rfl⟩ : syracuseStep 1889323 = 2833985) B2833985
theorem B4539509 : Blo 1887435 4539509 := bbase (se 5 (by rfl) ⟨212789, by rfl⟩ : syracuseStep 4539509 = 425579) (by norm_num)
theorem B3026339 : Blo 1887435 3026339 := bstep (se 1 (by rfl) ⟨2269754, by rfl⟩ : syracuseStep 3026339 = 4539509) B4539509
theorem B2017559 : Blo 1887435 2017559 := bstep (se 1 (by rfl) ⟨1513169, by rfl⟩ : syracuseStep 2017559 = 3026339) B3026339
theorem B5380157 : Blo 1887435 5380157 := bstep (se 3 (by rfl) ⟨1008779, by rfl⟩ : syracuseStep 5380157 = 2017559) B2017559
theorem B3586771 : Blo 1887435 3586771 := bstep (se 1 (by rfl) ⟨2690078, by rfl⟩ : syracuseStep 3586771 = 5380157) B5380157
theorem B4782361 : Blo 1887435 4782361 := bstep (se 2 (by rfl) ⟨1793385, by rfl⟩ : syracuseStep 4782361 = 3586771) B3586771
theorem B6376481 : Blo 1887435 6376481 := bstep (se 2 (by rfl) ⟨2391180, by rfl⟩ : syracuseStep 6376481 = 4782361) B4782361
theorem B4250987 : Blo 1887435 4250987 := bstep (se 1 (by rfl) ⟨3188240, by rfl⟩ : syracuseStep 4250987 = 6376481) B6376481
theorem B2833991 : Blo 1887435 2833991 := bstep (se 1 (by rfl) ⟨2125493, by rfl⟩ : syracuseStep 2833991 = 4250987) B4250987
theorem B1889327 : Blo 1887435 1889327 := bstep (se 1 (by rfl) ⟨1416995, by rfl⟩ : syracuseStep 1889327 = 2833991) B2833991
theorem B2833997 : Blo 1887435 2833997 := bbase (se 3 (by rfl) ⟨531374, by rfl⟩ : syracuseStep 2833997 = 1062749) (by norm_num)
theorem B1889331 : Blo 1887435 1889331 := bstep (se 1 (by rfl) ⟨1416998, by rfl⟩ : syracuseStep 1889331 = 2833997) B2833997
theorem B4251005 : Blo 1887435 4251005 := bbase (se 3 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 4251005 = 1594127) (by norm_num)
theorem B2834003 : Blo 1887435 2834003 := bstep (se 1 (by rfl) ⟨2125502, by rfl⟩ : syracuseStep 2834003 = 4251005) B4251005
theorem B1889335 : Blo 1887435 1889335 := bstep (se 1 (by rfl) ⟨1417001, by rfl⟩ : syracuseStep 1889335 = 2834003) B2834003
theorem B3188261 : Blo 1887435 3188261 := bbase (se 4 (by rfl) ⟨298899, by rfl⟩ : syracuseStep 3188261 = 597799) (by norm_num)
theorem B2125507 : Blo 1887435 2125507 := bstep (se 1 (by rfl) ⟨1594130, by rfl⟩ : syracuseStep 2125507 = 3188261) B3188261
theorem B2834009 : Blo 1887435 2834009 := bstep (se 2 (by rfl) ⟨1062753, by rfl⟩ : syracuseStep 2834009 = 2125507) B2125507
theorem B1889339 : Blo 1887435 1889339 := bstep (se 1 (by rfl) ⟨1417004, by rfl⟩ : syracuseStep 1889339 = 2834009) B2834009
theorem B2690101 : Blo 1887435 2690101 := bbase (se 5 (by rfl) ⟨126098, by rfl⟩ : syracuseStep 2690101 = 252197) (by norm_num)
theorem B14347205 : Blo 1887435 14347205 := bstep (se 4 (by rfl) ⟨1345050, by rfl⟩ : syracuseStep 14347205 = 2690101) B2690101
theorem B9564803 : Blo 1887435 9564803 := bstep (se 1 (by rfl) ⟨7173602, by rfl⟩ : syracuseStep 9564803 = 14347205) B14347205
theorem B6376535 : Blo 1887435 6376535 := bstep (se 1 (by rfl) ⟨4782401, by rfl⟩ : syracuseStep 6376535 = 9564803) B9564803
theorem B4251023 : Blo 1887435 4251023 := bstep (se 1 (by rfl) ⟨3188267, by rfl⟩ : syracuseStep 4251023 = 6376535) B6376535
theorem B2834015 : Blo 1887435 2834015 := bstep (se 1 (by rfl) ⟨2125511, by rfl⟩ : syracuseStep 2834015 = 4251023) B4251023
theorem B1889343 : Blo 1887435 1889343 := bstep (se 1 (by rfl) ⟨1417007, by rfl⟩ : syracuseStep 1889343 = 2834015) B2834015
theorem B2834021 : Blo 1887435 2834021 := bbase (se 4 (by rfl) ⟨265689, by rfl⟩ : syracuseStep 2834021 = 531379) (by norm_num)
theorem B1889347 : Blo 1887435 1889347 := bstep (se 1 (by rfl) ⟨1417010, by rfl⟩ : syracuseStep 1889347 = 2834021) B2834021
theorem B2017585 : Blo 1887435 2017585 := bbase (se 2 (by rfl) ⟨756594, by rfl⟩ : syracuseStep 2017585 = 1513189) (by norm_num)
theorem B2690113 : Blo 1887435 2690113 := bstep (se 2 (by rfl) ⟨1008792, by rfl⟩ : syracuseStep 2690113 = 2017585) B2017585
theorem B3586817 : Blo 1887435 3586817 := bstep (se 2 (by rfl) ⟨1345056, by rfl⟩ : syracuseStep 3586817 = 2690113) B2690113
theorem B2391211 : Blo 1887435 2391211 := bstep (se 1 (by rfl) ⟨1793408, by rfl⟩ : syracuseStep 2391211 = 3586817) B3586817
theorem B3188281 : Blo 1887435 3188281 := bstep (se 2 (by rfl) ⟨1195605, by rfl⟩ : syracuseStep 3188281 = 2391211) B2391211
theorem B4251041 : Blo 1887435 4251041 := bstep (se 2 (by rfl) ⟨1594140, by rfl⟩ : syracuseStep 4251041 = 3188281) B3188281
theorem B2834027 : Blo 1887435 2834027 := bstep (se 1 (by rfl) ⟨2125520, by rfl⟩ : syracuseStep 2834027 = 4251041) B4251041
theorem B1889351 : Blo 1887435 1889351 := bstep (se 1 (by rfl) ⟨1417013, by rfl⟩ : syracuseStep 1889351 = 2834027) B2834027
theorem B2125525 : Blo 1887435 2125525 := bbase (se 7 (by rfl) ⟨24908, by rfl⟩ : syracuseStep 2125525 = 49817) (by norm_num)
theorem B2834033 : Blo 1887435 2834033 := bstep (se 2 (by rfl) ⟨1062762, by rfl⟩ : syracuseStep 2834033 = 2125525) B2125525
theorem B1889355 : Blo 1887435 1889355 := bstep (se 1 (by rfl) ⟨1417016, by rfl⟩ : syracuseStep 1889355 = 2834033) B2834033
theorem B2391221 : Blo 1887435 2391221 := bbase (se 5 (by rfl) ⟨112088, by rfl⟩ : syracuseStep 2391221 = 224177) (by norm_num)
theorem B6376589 : Blo 1887435 6376589 := bstep (se 3 (by rfl) ⟨1195610, by rfl⟩ : syracuseStep 6376589 = 2391221) B2391221
theorem B4251059 : Blo 1887435 4251059 := bstep (se 1 (by rfl) ⟨3188294, by rfl⟩ : syracuseStep 4251059 = 6376589) B6376589
theorem B2834039 : Blo 1887435 2834039 := bstep (se 1 (by rfl) ⟨2125529, by rfl⟩ : syracuseStep 2834039 = 4251059) B4251059
theorem B1889359 : Blo 1887435 1889359 := bstep (se 1 (by rfl) ⟨1417019, by rfl⟩ : syracuseStep 1889359 = 2834039) B2834039
theorem B2834045 : Blo 1887435 2834045 := bbase (se 3 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 2834045 = 1062767) (by norm_num)
theorem B1889363 : Blo 1887435 1889363 := bstep (se 1 (by rfl) ⟨1417022, by rfl⟩ : syracuseStep 1889363 = 2834045) B2834045
theorem B4251077 : Blo 1887435 4251077 := bbase (se 4 (by rfl) ⟨398538, by rfl⟩ : syracuseStep 4251077 = 797077) (by norm_num)
theorem B2834051 : Blo 1887435 2834051 := bstep (se 1 (by rfl) ⟨2125538, by rfl⟩ : syracuseStep 2834051 = 4251077) B4251077
theorem B1889367 : Blo 1887435 1889367 := bstep (se 1 (by rfl) ⟨1417025, by rfl⟩ : syracuseStep 1889367 = 2834051) B2834051
theorem B4847725 : Blo 1887435 4847725 := bbase (se 3 (by rfl) ⟨908948, by rfl⟩ : syracuseStep 4847725 = 1817897) (by norm_num)
theorem B6463633 : Blo 1887435 6463633 := bstep (se 2 (by rfl) ⟨2423862, by rfl⟩ : syracuseStep 6463633 = 4847725) B4847725
theorem B8618177 : Blo 1887435 8618177 := bstep (se 2 (by rfl) ⟨3231816, by rfl⟩ : syracuseStep 8618177 = 6463633) B6463633
theorem B5745451 : Blo 1887435 5745451 := bstep (se 1 (by rfl) ⟨4309088, by rfl⟩ : syracuseStep 5745451 = 8618177) B8618177
theorem B7660601 : Blo 1887435 7660601 := bstep (se 2 (by rfl) ⟨2872725, by rfl⟩ : syracuseStep 7660601 = 5745451) B5745451
theorem B5107067 : Blo 1887435 5107067 := bstep (se 1 (by rfl) ⟨3830300, by rfl⟩ : syracuseStep 5107067 = 7660601) B7660601
theorem B3404711 : Blo 1887435 3404711 := bstep (se 1 (by rfl) ⟨2553533, by rfl⟩ : syracuseStep 3404711 = 5107067) B5107067
theorem B9079229 : Blo 1887435 9079229 := bstep (se 3 (by rfl) ⟨1702355, by rfl⟩ : syracuseStep 9079229 = 3404711) B3404711
theorem B6052819 : Blo 1887435 6052819 := bstep (se 1 (by rfl) ⟨4539614, by rfl⟩ : syracuseStep 6052819 = 9079229) B9079229
theorem B8070425 : Blo 1887435 8070425 := bstep (se 2 (by rfl) ⟨3026409, by rfl⟩ : syracuseStep 8070425 = 6052819) B6052819
theorem B5380283 : Blo 1887435 5380283 := bstep (se 1 (by rfl) ⟨4035212, by rfl⟩ : syracuseStep 5380283 = 8070425) B8070425
theorem B3586855 : Blo 1887435 3586855 := bstep (se 1 (by rfl) ⟨2690141, by rfl⟩ : syracuseStep 3586855 = 5380283) B5380283
theorem B4782473 : Blo 1887435 4782473 := bstep (se 2 (by rfl) ⟨1793427, by rfl⟩ : syracuseStep 4782473 = 3586855) B3586855
theorem B3188315 : Blo 1887435 3188315 := bstep (se 1 (by rfl) ⟨2391236, by rfl⟩ : syracuseStep 3188315 = 4782473) B4782473
theorem B2125543 : Blo 1887435 2125543 := bstep (se 1 (by rfl) ⟨1594157, by rfl⟩ : syracuseStep 2125543 = 3188315) B3188315
theorem B2834057 : Blo 1887435 2834057 := bstep (se 2 (by rfl) ⟨1062771, by rfl⟩ : syracuseStep 2834057 = 2125543) B2125543
theorem B1889371 : Blo 1887435 1889371 := bstep (se 1 (by rfl) ⟨1417028, by rfl⟩ : syracuseStep 1889371 = 2834057) B2834057
theorem B9564965 : Blo 1887435 9564965 := bbase (se 4 (by rfl) ⟨896715, by rfl⟩ : syracuseStep 9564965 = 1793431) (by norm_num)
theorem B6376643 : Blo 1887435 6376643 := bstep (se 1 (by rfl) ⟨4782482, by rfl⟩ : syracuseStep 6376643 = 9564965) B9564965
theorem B4251095 : Blo 1887435 4251095 := bstep (se 1 (by rfl) ⟨3188321, by rfl⟩ : syracuseStep 4251095 = 6376643) B6376643
theorem B2834063 : Blo 1887435 2834063 := bstep (se 1 (by rfl) ⟨2125547, by rfl⟩ : syracuseStep 2834063 = 4251095) B4251095
theorem B1889375 : Blo 1887435 1889375 := bstep (se 1 (by rfl) ⟨1417031, by rfl⟩ : syracuseStep 1889375 = 2834063) B2834063
theorem B2834069 : Blo 1887435 2834069 := bbase (se 6 (by rfl) ⟨66423, by rfl⟩ : syracuseStep 2834069 = 132847) (by norm_num)
theorem B1889379 : Blo 1887435 1889379 := bstep (se 1 (by rfl) ⟨1417034, by rfl⟩ : syracuseStep 1889379 = 2834069) B2834069
theorem B9079285 : Blo 1887435 9079285 := bbase (se 5 (by rfl) ⟨425591, by rfl⟩ : syracuseStep 9079285 = 851183) (by norm_num)
theorem B12105713 : Blo 1887435 12105713 := bstep (se 2 (by rfl) ⟨4539642, by rfl⟩ : syracuseStep 12105713 = 9079285) B9079285
theorem B8070475 : Blo 1887435 8070475 := bstep (se 1 (by rfl) ⟨6052856, by rfl⟩ : syracuseStep 8070475 = 12105713) B12105713
theorem B10760633 : Blo 1887435 10760633 := bstep (se 2 (by rfl) ⟨4035237, by rfl⟩ : syracuseStep 10760633 = 8070475) B8070475
theorem B7173755 : Blo 1887435 7173755 := bstep (se 1 (by rfl) ⟨5380316, by rfl⟩ : syracuseStep 7173755 = 10760633) B10760633
theorem B4782503 : Blo 1887435 4782503 := bstep (se 1 (by rfl) ⟨3586877, by rfl⟩ : syracuseStep 4782503 = 7173755) B7173755
theorem B3188335 : Blo 1887435 3188335 := bstep (se 1 (by rfl) ⟨2391251, by rfl⟩ : syracuseStep 3188335 = 4782503) B4782503
theorem B4251113 : Blo 1887435 4251113 := bstep (se 2 (by rfl) ⟨1594167, by rfl⟩ : syracuseStep 4251113 = 3188335) B3188335
theorem B2834075 : Blo 1887435 2834075 := bstep (se 1 (by rfl) ⟨2125556, by rfl⟩ : syracuseStep 2834075 = 4251113) B4251113
theorem B1889383 : Blo 1887435 1889383 := bstep (se 1 (by rfl) ⟨1417037, by rfl⟩ : syracuseStep 1889383 = 2834075) B2834075
theorem B2125561 : Blo 1887435 2125561 := bbase (se 2 (by rfl) ⟨797085, by rfl⟩ : syracuseStep 2125561 = 1594171) (by norm_num)
theorem B2834081 : Blo 1887435 2834081 := bstep (se 2 (by rfl) ⟨1062780, by rfl⟩ : syracuseStep 2834081 = 2125561) B2125561
theorem B1889387 : Blo 1887435 1889387 := bstep (se 1 (by rfl) ⟨1417040, by rfl⟩ : syracuseStep 1889387 = 2834081) B2834081
theorem B3830341 : Blo 1887435 3830341 := bbase (se 4 (by rfl) ⟨359094, by rfl⟩ : syracuseStep 3830341 = 718189) (by norm_num)
theorem B5107121 : Blo 1887435 5107121 := bstep (se 2 (by rfl) ⟨1915170, by rfl⟩ : syracuseStep 5107121 = 3830341) B3830341
theorem B3404747 : Blo 1887435 3404747 := bstep (se 1 (by rfl) ⟨2553560, by rfl⟩ : syracuseStep 3404747 = 5107121) B5107121
theorem B2269831 : Blo 1887435 2269831 := bstep (se 1 (by rfl) ⟨1702373, by rfl⟩ : syracuseStep 2269831 = 3404747) B3404747
theorem B3026441 : Blo 1887435 3026441 := bstep (se 2 (by rfl) ⟨1134915, by rfl⟩ : syracuseStep 3026441 = 2269831) B2269831
theorem B8070509 : Blo 1887435 8070509 := bstep (se 3 (by rfl) ⟨1513220, by rfl⟩ : syracuseStep 8070509 = 3026441) B3026441
theorem B5380339 : Blo 1887435 5380339 := bstep (se 1 (by rfl) ⟨4035254, by rfl⟩ : syracuseStep 5380339 = 8070509) B8070509
theorem B7173785 : Blo 1887435 7173785 := bstep (se 2 (by rfl) ⟨2690169, by rfl⟩ : syracuseStep 7173785 = 5380339) B5380339
theorem B4782523 : Blo 1887435 4782523 := bstep (se 1 (by rfl) ⟨3586892, by rfl⟩ : syracuseStep 4782523 = 7173785) B7173785
theorem B6376697 : Blo 1887435 6376697 := bstep (se 2 (by rfl) ⟨2391261, by rfl⟩ : syracuseStep 6376697 = 4782523) B4782523
theorem B4251131 : Blo 1887435 4251131 := bstep (se 1 (by rfl) ⟨3188348, by rfl⟩ : syracuseStep 4251131 = 6376697) B6376697
theorem B2834087 : Blo 1887435 2834087 := bstep (se 1 (by rfl) ⟨2125565, by rfl⟩ : syracuseStep 2834087 = 4251131) B4251131
theorem B1889391 : Blo 1887435 1889391 := bstep (se 1 (by rfl) ⟨1417043, by rfl⟩ : syracuseStep 1889391 = 2834087) B2834087
theorem B2834093 : Blo 1887435 2834093 := bbase (se 3 (by rfl) ⟨531392, by rfl⟩ : syracuseStep 2834093 = 1062785) (by norm_num)
theorem B1889395 : Blo 1887435 1889395 := bstep (se 1 (by rfl) ⟨1417046, by rfl⟩ : syracuseStep 1889395 = 2834093) B2834093
theorem B4251149 : Blo 1887435 4251149 := bbase (se 3 (by rfl) ⟨797090, by rfl⟩ : syracuseStep 4251149 = 1594181) (by norm_num)
theorem B2834099 : Blo 1887435 2834099 := bstep (se 1 (by rfl) ⟨2125574, by rfl⟩ : syracuseStep 2834099 = 4251149) B4251149
theorem B1889399 : Blo 1887435 1889399 := bstep (se 1 (by rfl) ⟨1417049, by rfl⟩ : syracuseStep 1889399 = 2834099) B2834099
theorem B2391277 : Blo 1887435 2391277 := bbase (se 3 (by rfl) ⟨448364, by rfl⟩ : syracuseStep 2391277 = 896729) (by norm_num)
theorem B3188369 : Blo 1887435 3188369 := bstep (se 2 (by rfl) ⟨1195638, by rfl⟩ : syracuseStep 3188369 = 2391277) B2391277
theorem B2125579 : Blo 1887435 2125579 := bstep (se 1 (by rfl) ⟨1594184, by rfl⟩ : syracuseStep 2125579 = 3188369) B3188369
theorem B2834105 : Blo 1887435 2834105 := bstep (se 2 (by rfl) ⟨1062789, by rfl⟩ : syracuseStep 2834105 = 2125579) B2125579
theorem B1889403 : Blo 1887435 1889403 := bstep (se 1 (by rfl) ⟨1417052, by rfl⟩ : syracuseStep 1889403 = 2834105) B2834105
theorem B3635861 : Blo 1887435 3635861 := bbase (se 6 (by rfl) ⟨85215, by rfl⟩ : syracuseStep 3635861 = 170431) (by norm_num)
theorem B9695629 : Blo 1887435 9695629 := bstep (se 3 (by rfl) ⟨1817930, by rfl⟩ : syracuseStep 9695629 = 3635861) B3635861
theorem B51710021 : Blo 1887435 51710021 := bstep (se 4 (by rfl) ⟨4847814, by rfl⟩ : syracuseStep 51710021 = 9695629) B9695629
theorem B34473347 : Blo 1887435 34473347 := bstep (se 1 (by rfl) ⟨25855010, by rfl⟩ : syracuseStep 34473347 = 51710021) B51710021
theorem B22982231 : Blo 1887435 22982231 := bstep (se 1 (by rfl) ⟨17236673, by rfl⟩ : syracuseStep 22982231 = 34473347) B34473347
theorem B15321487 : Blo 1887435 15321487 := bstep (se 1 (by rfl) ⟨11491115, by rfl⟩ : syracuseStep 15321487 = 22982231) B22982231
theorem B20428649 : Blo 1887435 20428649 := bstep (se 2 (by rfl) ⟨7660743, by rfl⟩ : syracuseStep 20428649 = 15321487) B15321487
theorem B13619099 : Blo 1887435 13619099 := bstep (se 1 (by rfl) ⟨10214324, by rfl⟩ : syracuseStep 13619099 = 20428649) B20428649
theorem B9079399 : Blo 1887435 9079399 := bstep (se 1 (by rfl) ⟨6809549, by rfl⟩ : syracuseStep 9079399 = 13619099) B13619099
theorem B12105865 : Blo 1887435 12105865 := bstep (se 2 (by rfl) ⟨4539699, by rfl⟩ : syracuseStep 12105865 = 9079399) B9079399
theorem B16141153 : Blo 1887435 16141153 := bstep (se 2 (by rfl) ⟨6052932, by rfl⟩ : syracuseStep 16141153 = 12105865) B12105865
theorem B21521537 : Blo 1887435 21521537 := bstep (se 2 (by rfl) ⟨8070576, by rfl⟩ : syracuseStep 21521537 = 16141153) B16141153
theorem B14347691 : Blo 1887435 14347691 := bstep (se 1 (by rfl) ⟨10760768, by rfl⟩ : syracuseStep 14347691 = 21521537) B21521537
theorem B9565127 : Blo 1887435 9565127 := bstep (se 1 (by rfl) ⟨7173845, by rfl⟩ : syracuseStep 9565127 = 14347691) B14347691
theorem B6376751 : Blo 1887435 6376751 := bstep (se 1 (by rfl) ⟨4782563, by rfl⟩ : syracuseStep 6376751 = 9565127) B9565127
theorem B4251167 : Blo 1887435 4251167 := bstep (se 1 (by rfl) ⟨3188375, by rfl⟩ : syracuseStep 4251167 = 6376751) B6376751
theorem B2834111 : Blo 1887435 2834111 := bstep (se 1 (by rfl) ⟨2125583, by rfl⟩ : syracuseStep 2834111 = 4251167) B4251167
theorem B1889407 : Blo 1887435 1889407 := bstep (se 1 (by rfl) ⟨1417055, by rfl⟩ : syracuseStep 1889407 = 2834111) B2834111
theorem B2834117 : Blo 1887435 2834117 := bbase (se 4 (by rfl) ⟨265698, by rfl⟩ : syracuseStep 2834117 = 531397) (by norm_num)
theorem B1889411 : Blo 1887435 1889411 := bstep (se 1 (by rfl) ⟨1417058, by rfl⟩ : syracuseStep 1889411 = 2834117) B2834117
theorem B3188389 : Blo 1887435 3188389 := bbase (se 4 (by rfl) ⟨298911, by rfl⟩ : syracuseStep 3188389 = 597823) (by norm_num)
theorem B4251185 : Blo 1887435 4251185 := bstep (se 2 (by rfl) ⟨1594194, by rfl⟩ : syracuseStep 4251185 = 3188389) B3188389
theorem B2834123 : Blo 1887435 2834123 := bstep (se 1 (by rfl) ⟨2125592, by rfl⟩ : syracuseStep 2834123 = 4251185) B4251185
theorem B1889415 : Blo 1887435 1889415 := bstep (se 1 (by rfl) ⟨1417061, by rfl⟩ : syracuseStep 1889415 = 2834123) B2834123
theorem B2125597 : Blo 1887435 2125597 := bbase (se 3 (by rfl) ⟨398549, by rfl⟩ : syracuseStep 2125597 = 797099) (by norm_num)
theorem B2834129 : Blo 1887435 2834129 := bstep (se 2 (by rfl) ⟨1062798, by rfl⟩ : syracuseStep 2834129 = 2125597) B2125597
theorem B1889419 : Blo 1887435 1889419 := bstep (se 1 (by rfl) ⟨1417064, by rfl⟩ : syracuseStep 1889419 = 2834129) B2834129
theorem B6376805 : Blo 1887435 6376805 := bbase (se 4 (by rfl) ⟨597825, by rfl⟩ : syracuseStep 6376805 = 1195651) (by norm_num)
theorem B4251203 : Blo 1887435 4251203 := bstep (se 1 (by rfl) ⟨3188402, by rfl⟩ : syracuseStep 4251203 = 6376805) B6376805
theorem B2834135 : Blo 1887435 2834135 := bstep (se 1 (by rfl) ⟨2125601, by rfl⟩ : syracuseStep 2834135 = 4251203) B4251203
theorem B1889423 : Blo 1887435 1889423 := bstep (se 1 (by rfl) ⟨1417067, by rfl⟩ : syracuseStep 1889423 = 2834135) B2834135
theorem B2834141 : Blo 1887435 2834141 := bbase (se 3 (by rfl) ⟨531401, by rfl⟩ : syracuseStep 2834141 = 1062803) (by norm_num)
theorem B1889427 : Blo 1887435 1889427 := bstep (se 1 (by rfl) ⟨1417070, by rfl⟩ : syracuseStep 1889427 = 2834141) B2834141
theorem B4251221 : Blo 1887435 4251221 := bbase (se 8 (by rfl) ⟨24909, by rfl⟩ : syracuseStep 4251221 = 49819) (by norm_num)
theorem B2834147 : Blo 1887435 2834147 := bstep (se 1 (by rfl) ⟨2125610, by rfl⟩ : syracuseStep 2834147 = 4251221) B4251221
theorem B1889431 : Blo 1887435 1889431 := bstep (se 1 (by rfl) ⟨1417073, by rfl⟩ : syracuseStep 1889431 = 2834147) B2834147
theorem B4035349 : Blo 1887435 4035349 := bbase (se 6 (by rfl) ⟨94578, by rfl⟩ : syracuseStep 4035349 = 189157) (by norm_num)
theorem B5380465 : Blo 1887435 5380465 := bstep (se 2 (by rfl) ⟨2017674, by rfl⟩ : syracuseStep 5380465 = 4035349) B4035349
theorem B7173953 : Blo 1887435 7173953 := bstep (se 2 (by rfl) ⟨2690232, by rfl⟩ : syracuseStep 7173953 = 5380465) B5380465
theorem B4782635 : Blo 1887435 4782635 := bstep (se 1 (by rfl) ⟨3586976, by rfl⟩ : syracuseStep 4782635 = 7173953) B7173953
theorem B3188423 : Blo 1887435 3188423 := bstep (se 1 (by rfl) ⟨2391317, by rfl⟩ : syracuseStep 3188423 = 4782635) B4782635
theorem B2125615 : Blo 1887435 2125615 := bstep (se 1 (by rfl) ⟨1594211, by rfl⟩ : syracuseStep 2125615 = 3188423) B3188423
theorem B2834153 : Blo 1887435 2834153 := bstep (se 2 (by rfl) ⟨1062807, by rfl⟩ : syracuseStep 2834153 = 2125615) B2125615
theorem B1889435 : Blo 1887435 1889435 := bstep (se 1 (by rfl) ⟨1417076, by rfl⟩ : syracuseStep 1889435 = 2834153) B2834153
theorem C0 (j : ℕ) (h1 : 471858 ≤ j) (h2 : j ≤ 472358) : Blo 1887435 (4 * j + 3) := by
  interval_cases j
  · exact B1887435
  · exact B1887439
  · exact B1887443
  · exact B1887447
  · exact B1887451
  · exact B1887455
  · exact B1887459
  · exact B1887463
  · exact B1887467
  · exact B1887471
  · exact B1887475
  · exact B1887479
  · exact B1887483
  · exact B1887487
  · exact B1887491
  · exact B1887495
  · exact B1887499
  · exact B1887503
  · exact B1887507
  · exact B1887511
  · exact B1887515
  · exact B1887519
  · exact B1887523
  · exact B1887527
  · exact B1887531
  · exact B1887535
  · exact B1887539
  · exact B1887543
  · exact B1887547
  · exact B1887551
  · exact B1887555
  · exact B1887559
  · exact B1887563
  · exact B1887567
  · exact B1887571
  · exact B1887575
  · exact B1887579
  · exact B1887583
  · exact B1887587
  · exact B1887591
  · exact B1887595
  · exact B1887599
  · exact B1887603
  · exact B1887607
  · exact B1887611
  · exact B1887615
  · exact B1887619
  · exact B1887623
  · exact B1887627
  · exact B1887631
  · exact B1887635
  · exact B1887639
  · exact B1887643
  · exact B1887647
  · exact B1887651
  · exact B1887655
  · exact B1887659
  · exact B1887663
  · exact B1887667
  · exact B1887671
  · exact B1887675
  · exact B1887679
  · exact B1887683
  · exact B1887687
  · exact B1887691
  · exact B1887695
  · exact B1887699
  · exact B1887703
  · exact B1887707
  · exact B1887711
  · exact B1887715
  · exact B1887719
  · exact B1887723
  · exact B1887727
  · exact B1887731
  · exact B1887735
  · exact B1887739
  · exact B1887743
  · exact B1887747
  · exact B1887751
  · exact B1887755
  · exact B1887759
  · exact B1887763
  · exact B1887767
  · exact B1887771
  · exact B1887775
  · exact B1887779
  · exact B1887783
  · exact B1887787
  · exact B1887791
  · exact B1887795
  · exact B1887799
  · exact B1887803
  · exact B1887807
  · exact B1887811
  · exact B1887815
  · exact B1887819
  · exact B1887823
  · exact B1887827
  · exact B1887831
  · exact B1887835
  · exact B1887839
  · exact B1887843
  · exact B1887847
  · exact B1887851
  · exact B1887855
  · exact B1887859
  · exact B1887863
  · exact B1887867
  · exact B1887871
  · exact B1887875
  · exact B1887879
  · exact B1887883
  · exact B1887887
  · exact B1887891
  · exact B1887895
  · exact B1887899
  · exact B1887903
  · exact B1887907
  · exact B1887911
  · exact B1887915
  · exact B1887919
  · exact B1887923
  · exact B1887927
  · exact B1887931
  · exact B1887935
  · exact B1887939
  · exact B1887943
  · exact B1887947
  · exact B1887951
  · exact B1887955
  · exact B1887959
  · exact B1887963
  · exact B1887967
  · exact B1887971
  · exact B1887975
  · exact B1887979
  · exact B1887983
  · exact B1887987
  · exact B1887991
  · exact B1887995
  · exact B1887999
  · exact B1888003
  · exact B1888007
  · exact B1888011
  · exact B1888015
  · exact B1888019
  · exact B1888023
  · exact B1888027
  · exact B1888031
  · exact B1888035
  · exact B1888039
  · exact B1888043
  · exact B1888047
  · exact B1888051
  · exact B1888055
  · exact B1888059
  · exact B1888063
  · exact B1888067
  · exact B1888071
  · exact B1888075
  · exact B1888079
  · exact B1888083
  · exact B1888087
  · exact B1888091
  · exact B1888095
  · exact B1888099
  · exact B1888103
  · exact B1888107
  · exact B1888111
  · exact B1888115
  · exact B1888119
  · exact B1888123
  · exact B1888127
  · exact B1888131
  · exact B1888135
  · exact B1888139
  · exact B1888143
  · exact B1888147
  · exact B1888151
  · exact B1888155
  · exact B1888159
  · exact B1888163
  · exact B1888167
  · exact B1888171
  · exact B1888175
  · exact B1888179
  · exact B1888183
  · exact B1888187
  · exact B1888191
  · exact B1888195
  · exact B1888199
  · exact B1888203
  · exact B1888207
  · exact B1888211
  · exact B1888215
  · exact B1888219
  · exact B1888223
  · exact B1888227
  · exact B1888231
  · exact B1888235
  · exact B1888239
  · exact B1888243
  · exact B1888247
  · exact B1888251
  · exact B1888255
  · exact B1888259
  · exact B1888263
  · exact B1888267
  · exact B1888271
  · exact B1888275
  · exact B1888279
  · exact B1888283
  · exact B1888287
  · exact B1888291
  · exact B1888295
  · exact B1888299
  · exact B1888303
  · exact B1888307
  · exact B1888311
  · exact B1888315
  · exact B1888319
  · exact B1888323
  · exact B1888327
  · exact B1888331
  · exact B1888335
  · exact B1888339
  · exact B1888343
  · exact B1888347
  · exact B1888351
  · exact B1888355
  · exact B1888359
  · exact B1888363
  · exact B1888367
  · exact B1888371
  · exact B1888375
  · exact B1888379
  · exact B1888383
  · exact B1888387
  · exact B1888391
  · exact B1888395
  · exact B1888399
  · exact B1888403
  · exact B1888407
  · exact B1888411
  · exact B1888415
  · exact B1888419
  · exact B1888423
  · exact B1888427
  · exact B1888431
  · exact B1888435
  · exact B1888439
  · exact B1888443
  · exact B1888447
  · exact B1888451
  · exact B1888455
  · exact B1888459
  · exact B1888463
  · exact B1888467
  · exact B1888471
  · exact B1888475
  · exact B1888479
  · exact B1888483
  · exact B1888487
  · exact B1888491
  · exact B1888495
  · exact B1888499
  · exact B1888503
  · exact B1888507
  · exact B1888511
  · exact B1888515
  · exact B1888519
  · exact B1888523
  · exact B1888527
  · exact B1888531
  · exact B1888535
  · exact B1888539
  · exact B1888543
  · exact B1888547
  · exact B1888551
  · exact B1888555
  · exact B1888559
  · exact B1888563
  · exact B1888567
  · exact B1888571
  · exact B1888575
  · exact B1888579
  · exact B1888583
  · exact B1888587
  · exact B1888591
  · exact B1888595
  · exact B1888599
  · exact B1888603
  · exact B1888607
  · exact B1888611
  · exact B1888615
  · exact B1888619
  · exact B1888623
  · exact B1888627
  · exact B1888631
  · exact B1888635
  · exact B1888639
  · exact B1888643
  · exact B1888647
  · exact B1888651
  · exact B1888655
  · exact B1888659
  · exact B1888663
  · exact B1888667
  · exact B1888671
  · exact B1888675
  · exact B1888679
  · exact B1888683
  · exact B1888687
  · exact B1888691
  · exact B1888695
  · exact B1888699
  · exact B1888703
  · exact B1888707
  · exact B1888711
  · exact B1888715
  · exact B1888719
  · exact B1888723
  · exact B1888727
  · exact B1888731
  · exact B1888735
  · exact B1888739
  · exact B1888743
  · exact B1888747
  · exact B1888751
  · exact B1888755
  · exact B1888759
  · exact B1888763
  · exact B1888767
  · exact B1888771
  · exact B1888775
  · exact B1888779
  · exact B1888783
  · exact B1888787
  · exact B1888791
  · exact B1888795
  · exact B1888799
  · exact B1888803
  · exact B1888807
  · exact B1888811
  · exact B1888815
  · exact B1888819
  · exact B1888823
  · exact B1888827
  · exact B1888831
  · exact B1888835
  · exact B1888839
  · exact B1888843
  · exact B1888847
  · exact B1888851
  · exact B1888855
  · exact B1888859
  · exact B1888863
  · exact B1888867
  · exact B1888871
  · exact B1888875
  · exact B1888879
  · exact B1888883
  · exact B1888887
  · exact B1888891
  · exact B1888895
  · exact B1888899
  · exact B1888903
  · exact B1888907
  · exact B1888911
  · exact B1888915
  · exact B1888919
  · exact B1888923
  · exact B1888927
  · exact B1888931
  · exact B1888935
  · exact B1888939
  · exact B1888943
  · exact B1888947
  · exact B1888951
  · exact B1888955
  · exact B1888959
  · exact B1888963
  · exact B1888967
  · exact B1888971
  · exact B1888975
  · exact B1888979
  · exact B1888983
  · exact B1888987
  · exact B1888991
  · exact B1888995
  · exact B1888999
  · exact B1889003
  · exact B1889007
  · exact B1889011
  · exact B1889015
  · exact B1889019
  · exact B1889023
  · exact B1889027
  · exact B1889031
  · exact B1889035
  · exact B1889039
  · exact B1889043
  · exact B1889047
  · exact B1889051
  · exact B1889055
  · exact B1889059
  · exact B1889063
  · exact B1889067
  · exact B1889071
  · exact B1889075
  · exact B1889079
  · exact B1889083
  · exact B1889087
  · exact B1889091
  · exact B1889095
  · exact B1889099
  · exact B1889103
  · exact B1889107
  · exact B1889111
  · exact B1889115
  · exact B1889119
  · exact B1889123
  · exact B1889127
  · exact B1889131
  · exact B1889135
  · exact B1889139
  · exact B1889143
  · exact B1889147
  · exact B1889151
  · exact B1889155
  · exact B1889159
  · exact B1889163
  · exact B1889167
  · exact B1889171
  · exact B1889175
  · exact B1889179
  · exact B1889183
  · exact B1889187
  · exact B1889191
  · exact B1889195
  · exact B1889199
  · exact B1889203
  · exact B1889207
  · exact B1889211
  · exact B1889215
  · exact B1889219
  · exact B1889223
  · exact B1889227
  · exact B1889231
  · exact B1889235
  · exact B1889239
  · exact B1889243
  · exact B1889247
  · exact B1889251
  · exact B1889255
  · exact B1889259
  · exact B1889263
  · exact B1889267
  · exact B1889271
  · exact B1889275
  · exact B1889279
  · exact B1889283
  · exact B1889287
  · exact B1889291
  · exact B1889295
  · exact B1889299
  · exact B1889303
  · exact B1889307
  · exact B1889311
  · exact B1889315
  · exact B1889319
  · exact B1889323
  · exact B1889327
  · exact B1889331
  · exact B1889335
  · exact B1889339
  · exact B1889343
  · exact B1889347
  · exact B1889351
  · exact B1889355
  · exact B1889359
  · exact B1889363
  · exact B1889367
  · exact B1889371
  · exact B1889375
  · exact B1889379
  · exact B1889383
  · exact B1889387
  · exact B1889391
  · exact B1889395
  · exact B1889399
  · exact B1889403
  · exact B1889407
  · exact B1889411
  · exact B1889415
  · exact B1889419
  · exact B1889423
  · exact B1889427
  · exact B1889431
  · exact B1889435
theorem solution (m : ℕ) (hlo : 1887435 ≤ m) (hhi : m ≤ 1889435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 471858 ≤ j := by omega
    have hj2 : j ≤ 472358 := by omega
    have hb : Blo 1887435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
