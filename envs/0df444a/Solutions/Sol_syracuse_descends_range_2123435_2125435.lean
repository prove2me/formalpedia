-- Prove2me | solution 1 for syracuse_descends_range_2123435_2125435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:59.217121+00:00
-- url     : https://prove2.me/submissions/db3d3b03-14b1-459d-95cf-71a2c6871c12

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

theorem B2388865 : Blo 2123435 2388865 := bbase (se 2 (by rfl) ⟨895824, by rfl⟩ : syracuseStep 2388865 = 1791649) (by norm_num)
theorem B3185153 : Blo 2123435 3185153 := bstep (se 2 (by rfl) ⟨1194432, by rfl⟩ : syracuseStep 3185153 = 2388865) B2388865
theorem B2123435 : Blo 2123435 2123435 := bstep (se 1 (by rfl) ⟨1592576, by rfl⟩ : syracuseStep 2123435 = 3185153) B3185153
theorem B5374957 : Blo 2123435 5374957 := bbase (se 3 (by rfl) ⟨1007804, by rfl⟩ : syracuseStep 5374957 = 2015609) (by norm_num)
theorem B7166609 : Blo 2123435 7166609 := bstep (se 2 (by rfl) ⟨2687478, by rfl⟩ : syracuseStep 7166609 = 5374957) B5374957
theorem B4777739 : Blo 2123435 4777739 := bstep (se 1 (by rfl) ⟨3583304, by rfl⟩ : syracuseStep 4777739 = 7166609) B7166609
theorem B3185159 : Blo 2123435 3185159 := bstep (se 1 (by rfl) ⟨2388869, by rfl⟩ : syracuseStep 3185159 = 4777739) B4777739
theorem B2123439 : Blo 2123435 2123439 := bstep (se 1 (by rfl) ⟨1592579, by rfl⟩ : syracuseStep 2123439 = 3185159) B3185159
theorem B3185165 : Blo 2123435 3185165 := bbase (se 3 (by rfl) ⟨597218, by rfl⟩ : syracuseStep 3185165 = 1194437) (by norm_num)
theorem B2123443 : Blo 2123435 2123443 := bstep (se 1 (by rfl) ⟨1592582, by rfl⟩ : syracuseStep 2123443 = 3185165) B3185165
theorem B4777757 : Blo 2123435 4777757 := bbase (se 3 (by rfl) ⟨895829, by rfl⟩ : syracuseStep 4777757 = 1791659) (by norm_num)
theorem B3185171 : Blo 2123435 3185171 := bstep (se 1 (by rfl) ⟨2388878, by rfl⟩ : syracuseStep 3185171 = 4777757) B4777757
theorem B2123447 : Blo 2123435 2123447 := bstep (se 1 (by rfl) ⟨1592585, by rfl⟩ : syracuseStep 2123447 = 3185171) B3185171
theorem B3583325 : Blo 2123435 3583325 := bbase (se 3 (by rfl) ⟨671873, by rfl⟩ : syracuseStep 3583325 = 1343747) (by norm_num)
theorem B2388883 : Blo 2123435 2388883 := bstep (se 1 (by rfl) ⟨1791662, by rfl⟩ : syracuseStep 2388883 = 3583325) B3583325
theorem B3185177 : Blo 2123435 3185177 := bstep (se 2 (by rfl) ⟨1194441, by rfl⟩ : syracuseStep 3185177 = 2388883) B2388883
theorem B2123451 : Blo 2123435 2123451 := bstep (se 1 (by rfl) ⟨1592588, by rfl⟩ : syracuseStep 2123451 = 3185177) B3185177
theorem B9070309 : Blo 2123435 9070309 := bbase (se 4 (by rfl) ⟨850341, by rfl⟩ : syracuseStep 9070309 = 1700683) (by norm_num)
theorem B12093745 : Blo 2123435 12093745 := bstep (se 2 (by rfl) ⟨4535154, by rfl⟩ : syracuseStep 12093745 = 9070309) B9070309
theorem B16124993 : Blo 2123435 16124993 := bstep (se 2 (by rfl) ⟨6046872, by rfl⟩ : syracuseStep 16124993 = 12093745) B12093745
theorem B10749995 : Blo 2123435 10749995 := bstep (se 1 (by rfl) ⟨8062496, by rfl⟩ : syracuseStep 10749995 = 16124993) B16124993
theorem B7166663 : Blo 2123435 7166663 := bstep (se 1 (by rfl) ⟨5374997, by rfl⟩ : syracuseStep 7166663 = 10749995) B10749995
theorem B4777775 : Blo 2123435 4777775 := bstep (se 1 (by rfl) ⟨3583331, by rfl⟩ : syracuseStep 4777775 = 7166663) B7166663
theorem B3185183 : Blo 2123435 3185183 := bstep (se 1 (by rfl) ⟨2388887, by rfl⟩ : syracuseStep 3185183 = 4777775) B4777775
theorem B2123455 : Blo 2123435 2123455 := bstep (se 1 (by rfl) ⟨1592591, by rfl⟩ : syracuseStep 2123455 = 3185183) B3185183
theorem B3185189 : Blo 2123435 3185189 := bbase (se 4 (by rfl) ⟨298611, by rfl⟩ : syracuseStep 3185189 = 597223) (by norm_num)
theorem B2123459 : Blo 2123435 2123459 := bstep (se 1 (by rfl) ⟨1592594, by rfl⟩ : syracuseStep 2123459 = 3185189) B3185189
theorem B2687509 : Blo 2123435 2687509 := bbase (se 6 (by rfl) ⟨62988, by rfl⟩ : syracuseStep 2687509 = 125977) (by norm_num)
theorem B3583345 : Blo 2123435 3583345 := bstep (se 2 (by rfl) ⟨1343754, by rfl⟩ : syracuseStep 3583345 = 2687509) B2687509
theorem B4777793 : Blo 2123435 4777793 := bstep (se 2 (by rfl) ⟨1791672, by rfl⟩ : syracuseStep 4777793 = 3583345) B3583345
theorem B3185195 : Blo 2123435 3185195 := bstep (se 1 (by rfl) ⟨2388896, by rfl⟩ : syracuseStep 3185195 = 4777793) B4777793
theorem B2123463 : Blo 2123435 2123463 := bstep (se 1 (by rfl) ⟨1592597, by rfl⟩ : syracuseStep 2123463 = 3185195) B3185195
theorem B2388901 : Blo 2123435 2388901 := bbase (se 4 (by rfl) ⟨223959, by rfl⟩ : syracuseStep 2388901 = 447919) (by norm_num)
theorem B3185201 : Blo 2123435 3185201 := bstep (se 2 (by rfl) ⟨1194450, by rfl⟩ : syracuseStep 3185201 = 2388901) B2388901
theorem B2123467 : Blo 2123435 2123467 := bstep (se 1 (by rfl) ⟨1592600, by rfl⟩ : syracuseStep 2123467 = 3185201) B3185201
theorem B2869925 : Blo 2123435 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B7653133 : Blo 2123435 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B10204177 : Blo 2123435 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B13605569 : Blo 2123435 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B9070379 : Blo 2123435 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B6046919 : Blo 2123435 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B4031279 : Blo 2123435 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B2687519 : Blo 2123435 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B7166717 : Blo 2123435 7166717 := bstep (se 3 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 7166717 = 2687519) B2687519
theorem B4777811 : Blo 2123435 4777811 := bstep (se 1 (by rfl) ⟨3583358, by rfl⟩ : syracuseStep 4777811 = 7166717) B7166717
theorem B3185207 : Blo 2123435 3185207 := bstep (se 1 (by rfl) ⟨2388905, by rfl⟩ : syracuseStep 3185207 = 4777811) B4777811
theorem B2123471 : Blo 2123435 2123471 := bstep (se 1 (by rfl) ⟨1592603, by rfl⟩ : syracuseStep 2123471 = 3185207) B3185207
theorem B3185213 : Blo 2123435 3185213 := bbase (se 3 (by rfl) ⟨597227, by rfl⟩ : syracuseStep 3185213 = 1194455) (by norm_num)
theorem B2123475 : Blo 2123435 2123475 := bstep (se 1 (by rfl) ⟨1592606, by rfl⟩ : syracuseStep 2123475 = 3185213) B3185213
theorem B4777829 : Blo 2123435 4777829 := bbase (se 4 (by rfl) ⟨447921, by rfl⟩ : syracuseStep 4777829 = 895843) (by norm_num)
theorem B3185219 : Blo 2123435 3185219 := bstep (se 1 (by rfl) ⟨2388914, by rfl⟩ : syracuseStep 3185219 = 4777829) B4777829
theorem B2123479 : Blo 2123435 2123479 := bstep (se 1 (by rfl) ⟨1592609, by rfl⟩ : syracuseStep 2123479 = 3185219) B3185219
theorem B5375069 : Blo 2123435 5375069 := bbase (se 3 (by rfl) ⟨1007825, by rfl⟩ : syracuseStep 5375069 = 2015651) (by norm_num)
theorem B3583379 : Blo 2123435 3583379 := bstep (se 1 (by rfl) ⟨2687534, by rfl⟩ : syracuseStep 3583379 = 5375069) B5375069
theorem B2388919 : Blo 2123435 2388919 := bstep (se 1 (by rfl) ⟨1791689, by rfl⟩ : syracuseStep 2388919 = 3583379) B3583379
theorem B3185225 : Blo 2123435 3185225 := bstep (se 2 (by rfl) ⟨1194459, by rfl⟩ : syracuseStep 3185225 = 2388919) B2388919
theorem B2123483 : Blo 2123435 2123483 := bstep (se 1 (by rfl) ⟨1592612, by rfl⟩ : syracuseStep 2123483 = 3185225) B3185225
theorem B4031309 : Blo 2123435 4031309 := bbase (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) (by norm_num)
theorem B10750157 : Blo 2123435 10750157 := bstep (se 3 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 10750157 = 4031309) B4031309
theorem B7166771 : Blo 2123435 7166771 := bstep (se 1 (by rfl) ⟨5375078, by rfl⟩ : syracuseStep 7166771 = 10750157) B10750157
theorem B4777847 : Blo 2123435 4777847 := bstep (se 1 (by rfl) ⟨3583385, by rfl⟩ : syracuseStep 4777847 = 7166771) B7166771
theorem B3185231 : Blo 2123435 3185231 := bstep (se 1 (by rfl) ⟨2388923, by rfl⟩ : syracuseStep 3185231 = 4777847) B4777847
theorem B2123487 : Blo 2123435 2123487 := bstep (se 1 (by rfl) ⟨1592615, by rfl⟩ : syracuseStep 2123487 = 3185231) B3185231
theorem B3185237 : Blo 2123435 3185237 := bbase (se 8 (by rfl) ⟨18663, by rfl⟩ : syracuseStep 3185237 = 37327) (by norm_num)
theorem B2123491 : Blo 2123435 2123491 := bstep (se 1 (by rfl) ⟨1592618, by rfl⟩ : syracuseStep 2123491 = 3185237) B3185237
theorem B2551073 : Blo 2123435 2551073 := bbase (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) (by norm_num)
theorem B6802861 : Blo 2123435 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B9070481 : Blo 2123435 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B6046987 : Blo 2123435 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B8062649 : Blo 2123435 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B5375099 : Blo 2123435 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B3583399 : Blo 2123435 3583399 := bstep (se 1 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 3583399 = 5375099) B5375099
theorem B4777865 : Blo 2123435 4777865 := bstep (se 2 (by rfl) ⟨1791699, by rfl⟩ : syracuseStep 4777865 = 3583399) B3583399
theorem B3185243 : Blo 2123435 3185243 := bstep (se 1 (by rfl) ⟨2388932, by rfl⟩ : syracuseStep 3185243 = 4777865) B4777865
theorem B2123495 : Blo 2123435 2123495 := bstep (se 1 (by rfl) ⟨1592621, by rfl⟩ : syracuseStep 2123495 = 3185243) B3185243
theorem B2388937 : Blo 2123435 2388937 := bbase (se 2 (by rfl) ⟨895851, by rfl⟩ : syracuseStep 2388937 = 1791703) (by norm_num)
theorem B3185249 : Blo 2123435 3185249 := bstep (se 2 (by rfl) ⟨1194468, by rfl⟩ : syracuseStep 3185249 = 2388937) B2388937
theorem B2123499 : Blo 2123435 2123499 := bstep (se 1 (by rfl) ⟨1592624, by rfl⟩ : syracuseStep 2123499 = 3185249) B3185249
theorem B5102165 : Blo 2123435 5102165 := bbase (se 8 (by rfl) ⟨29895, by rfl⟩ : syracuseStep 5102165 = 59791) (by norm_num)
theorem B3401443 : Blo 2123435 3401443 := bstep (se 1 (by rfl) ⟨2551082, by rfl⟩ : syracuseStep 3401443 = 5102165) B5102165
theorem B18141029 : Blo 2123435 18141029 := bstep (se 4 (by rfl) ⟨1700721, by rfl⟩ : syracuseStep 18141029 = 3401443) B3401443
theorem B12094019 : Blo 2123435 12094019 := bstep (se 1 (by rfl) ⟨9070514, by rfl⟩ : syracuseStep 12094019 = 18141029) B18141029
theorem B8062679 : Blo 2123435 8062679 := bstep (se 1 (by rfl) ⟨6047009, by rfl⟩ : syracuseStep 8062679 = 12094019) B12094019
theorem B5375119 : Blo 2123435 5375119 := bstep (se 1 (by rfl) ⟨4031339, by rfl⟩ : syracuseStep 5375119 = 8062679) B8062679
theorem B7166825 : Blo 2123435 7166825 := bstep (se 2 (by rfl) ⟨2687559, by rfl⟩ : syracuseStep 7166825 = 5375119) B5375119
theorem B4777883 : Blo 2123435 4777883 := bstep (se 1 (by rfl) ⟨3583412, by rfl⟩ : syracuseStep 4777883 = 7166825) B7166825
theorem B3185255 : Blo 2123435 3185255 := bstep (se 1 (by rfl) ⟨2388941, by rfl⟩ : syracuseStep 3185255 = 4777883) B4777883
theorem B2123503 : Blo 2123435 2123503 := bstep (se 1 (by rfl) ⟨1592627, by rfl⟩ : syracuseStep 2123503 = 3185255) B3185255
theorem B3185261 : Blo 2123435 3185261 := bbase (se 3 (by rfl) ⟨597236, by rfl⟩ : syracuseStep 3185261 = 1194473) (by norm_num)
theorem B2123507 : Blo 2123435 2123507 := bstep (se 1 (by rfl) ⟨1592630, by rfl⟩ : syracuseStep 2123507 = 3185261) B3185261
theorem B4777901 : Blo 2123435 4777901 := bbase (se 3 (by rfl) ⟨895856, by rfl⟩ : syracuseStep 4777901 = 1791713) (by norm_num)
theorem B3185267 : Blo 2123435 3185267 := bstep (se 1 (by rfl) ⟨2388950, by rfl⟩ : syracuseStep 3185267 = 4777901) B4777901
theorem B2123511 : Blo 2123435 2123511 := bstep (se 1 (by rfl) ⟨1592633, by rfl⟩ : syracuseStep 2123511 = 3185267) B3185267
theorem B6047045 : Blo 2123435 6047045 := bbase (se 4 (by rfl) ⟨566910, by rfl⟩ : syracuseStep 6047045 = 1133821) (by norm_num)
theorem B4031363 : Blo 2123435 4031363 := bstep (se 1 (by rfl) ⟨3023522, by rfl⟩ : syracuseStep 4031363 = 6047045) B6047045
theorem B2687575 : Blo 2123435 2687575 := bstep (se 1 (by rfl) ⟨2015681, by rfl⟩ : syracuseStep 2687575 = 4031363) B4031363
theorem B3583433 : Blo 2123435 3583433 := bstep (se 2 (by rfl) ⟨1343787, by rfl⟩ : syracuseStep 3583433 = 2687575) B2687575
theorem B2388955 : Blo 2123435 2388955 := bstep (se 1 (by rfl) ⟨1791716, by rfl⟩ : syracuseStep 2388955 = 3583433) B3583433
theorem B3185273 : Blo 2123435 3185273 := bstep (se 2 (by rfl) ⟨1194477, by rfl⟩ : syracuseStep 3185273 = 2388955) B2388955
theorem B2123515 : Blo 2123435 2123515 := bstep (se 1 (by rfl) ⟨1592636, by rfl⟩ : syracuseStep 2123515 = 3185273) B3185273
theorem B40817621 : Blo 2123435 40817621 := bbase (se 7 (by rfl) ⟨478331, by rfl⟩ : syracuseStep 40817621 = 956663) (by norm_num)
theorem B27211747 : Blo 2123435 27211747 := bstep (se 1 (by rfl) ⟨20408810, by rfl⟩ : syracuseStep 27211747 = 40817621) B40817621
theorem B36282329 : Blo 2123435 36282329 := bstep (se 2 (by rfl) ⟨13605873, by rfl⟩ : syracuseStep 36282329 = 27211747) B27211747
theorem B24188219 : Blo 2123435 24188219 := bstep (se 1 (by rfl) ⟨18141164, by rfl⟩ : syracuseStep 24188219 = 36282329) B36282329
theorem B16125479 : Blo 2123435 16125479 := bstep (se 1 (by rfl) ⟨12094109, by rfl⟩ : syracuseStep 16125479 = 24188219) B24188219
theorem B10750319 : Blo 2123435 10750319 := bstep (se 1 (by rfl) ⟨8062739, by rfl⟩ : syracuseStep 10750319 = 16125479) B16125479
theorem B7166879 : Blo 2123435 7166879 := bstep (se 1 (by rfl) ⟨5375159, by rfl⟩ : syracuseStep 7166879 = 10750319) B10750319
theorem B4777919 : Blo 2123435 4777919 := bstep (se 1 (by rfl) ⟨3583439, by rfl⟩ : syracuseStep 4777919 = 7166879) B7166879
theorem B3185279 : Blo 2123435 3185279 := bstep (se 1 (by rfl) ⟨2388959, by rfl⟩ : syracuseStep 3185279 = 4777919) B4777919
theorem B2123519 : Blo 2123435 2123519 := bstep (se 1 (by rfl) ⟨1592639, by rfl⟩ : syracuseStep 2123519 = 3185279) B3185279
theorem B3185285 : Blo 2123435 3185285 := bbase (se 4 (by rfl) ⟨298620, by rfl⟩ : syracuseStep 3185285 = 597241) (by norm_num)
theorem B2123523 : Blo 2123435 2123523 := bstep (se 1 (by rfl) ⟨1592642, by rfl⟩ : syracuseStep 2123523 = 3185285) B3185285
theorem B3583453 : Blo 2123435 3583453 := bbase (se 3 (by rfl) ⟨671897, by rfl⟩ : syracuseStep 3583453 = 1343795) (by norm_num)
theorem B4777937 : Blo 2123435 4777937 := bstep (se 2 (by rfl) ⟨1791726, by rfl⟩ : syracuseStep 4777937 = 3583453) B3583453
theorem B3185291 : Blo 2123435 3185291 := bstep (se 1 (by rfl) ⟨2388968, by rfl⟩ : syracuseStep 3185291 = 4777937) B4777937
theorem B2123527 : Blo 2123435 2123527 := bstep (se 1 (by rfl) ⟨1592645, by rfl⟩ : syracuseStep 2123527 = 3185291) B3185291
theorem B2388973 : Blo 2123435 2388973 := bbase (se 3 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 2388973 = 895865) (by norm_num)
theorem B3185297 : Blo 2123435 3185297 := bstep (se 2 (by rfl) ⟨1194486, by rfl⟩ : syracuseStep 3185297 = 2388973) B2388973
theorem B2123531 : Blo 2123435 2123531 := bstep (se 1 (by rfl) ⟨1592648, by rfl⟩ : syracuseStep 2123531 = 3185297) B3185297
theorem B7166933 : Blo 2123435 7166933 := bbase (se 7 (by rfl) ⟨83987, by rfl⟩ : syracuseStep 7166933 = 167975) (by norm_num)
theorem B4777955 : Blo 2123435 4777955 := bstep (se 1 (by rfl) ⟨3583466, by rfl⟩ : syracuseStep 4777955 = 7166933) B7166933
theorem B3185303 : Blo 2123435 3185303 := bstep (se 1 (by rfl) ⟨2388977, by rfl⟩ : syracuseStep 3185303 = 4777955) B4777955
theorem B2123535 : Blo 2123435 2123535 := bstep (se 1 (by rfl) ⟨1592651, by rfl⟩ : syracuseStep 2123535 = 3185303) B3185303
theorem B3185309 : Blo 2123435 3185309 := bbase (se 3 (by rfl) ⟨597245, by rfl⟩ : syracuseStep 3185309 = 1194491) (by norm_num)
theorem B2123539 : Blo 2123435 2123539 := bstep (se 1 (by rfl) ⟨1592654, by rfl⟩ : syracuseStep 2123539 = 3185309) B3185309
theorem B4777973 : Blo 2123435 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B3185315 : Blo 2123435 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B2123543 : Blo 2123435 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B8284357 : Blo 2123435 8284357 := bbase (se 4 (by rfl) ⟨776658, by rfl⟩ : syracuseStep 8284357 = 1553317) (by norm_num)
theorem B11045809 : Blo 2123435 11045809 := bstep (se 2 (by rfl) ⟨4142178, by rfl⟩ : syracuseStep 11045809 = 8284357) B8284357
theorem B14727745 : Blo 2123435 14727745 := bstep (se 2 (by rfl) ⟨5522904, by rfl⟩ : syracuseStep 14727745 = 11045809) B11045809
theorem B19636993 : Blo 2123435 19636993 := bstep (se 2 (by rfl) ⟨7363872, by rfl⟩ : syracuseStep 19636993 = 14727745) B14727745
theorem B104730629 : Blo 2123435 104730629 := bstep (se 4 (by rfl) ⟨9818496, by rfl⟩ : syracuseStep 104730629 = 19636993) B19636993
theorem B279281677 : Blo 2123435 279281677 := bstep (se 3 (by rfl) ⟨52365314, by rfl⟩ : syracuseStep 279281677 = 104730629) B104730629
theorem B372375569 : Blo 2123435 372375569 := bstep (se 2 (by rfl) ⟨139640838, by rfl⟩ : syracuseStep 372375569 = 279281677) B279281677
theorem B248250379 : Blo 2123435 248250379 := bstep (se 1 (by rfl) ⟨186187784, by rfl⟩ : syracuseStep 248250379 = 372375569) B372375569
theorem B331000505 : Blo 2123435 331000505 := bstep (se 2 (by rfl) ⟨124125189, by rfl⟩ : syracuseStep 331000505 = 248250379) B248250379
theorem B220667003 : Blo 2123435 220667003 := bstep (se 1 (by rfl) ⟨165500252, by rfl⟩ : syracuseStep 220667003 = 331000505) B331000505
theorem B147111335 : Blo 2123435 147111335 := bstep (se 1 (by rfl) ⟨110333501, by rfl⟩ : syracuseStep 147111335 = 220667003) B220667003
theorem B98074223 : Blo 2123435 98074223 := bstep (se 1 (by rfl) ⟨73555667, by rfl⟩ : syracuseStep 98074223 = 147111335) B147111335
theorem B65382815 : Blo 2123435 65382815 := bstep (se 1 (by rfl) ⟨49037111, by rfl⟩ : syracuseStep 65382815 = 98074223) B98074223
theorem B43588543 : Blo 2123435 43588543 := bstep (se 1 (by rfl) ⟨32691407, by rfl⟩ : syracuseStep 43588543 = 65382815) B65382815
theorem B58118057 : Blo 2123435 58118057 := bstep (se 2 (by rfl) ⟨21794271, by rfl⟩ : syracuseStep 58118057 = 43588543) B43588543
theorem B38745371 : Blo 2123435 38745371 := bstep (se 1 (by rfl) ⟨29059028, by rfl⟩ : syracuseStep 38745371 = 58118057) B58118057
theorem B25830247 : Blo 2123435 25830247 := bstep (se 1 (by rfl) ⟨19372685, by rfl⟩ : syracuseStep 25830247 = 38745371) B38745371
theorem B34440329 : Blo 2123435 34440329 := bstep (se 2 (by rfl) ⟨12915123, by rfl⟩ : syracuseStep 34440329 = 25830247) B25830247
theorem B91840877 : Blo 2123435 91840877 := bstep (se 3 (by rfl) ⟨17220164, by rfl⟩ : syracuseStep 91840877 = 34440329) B34440329
theorem B61227251 : Blo 2123435 61227251 := bstep (se 1 (by rfl) ⟨45920438, by rfl⟩ : syracuseStep 61227251 = 91840877) B91840877
theorem B40818167 : Blo 2123435 40818167 := bstep (se 1 (by rfl) ⟨30613625, by rfl⟩ : syracuseStep 40818167 = 61227251) B61227251
theorem B27212111 : Blo 2123435 27212111 := bstep (se 1 (by rfl) ⟨20409083, by rfl⟩ : syracuseStep 27212111 = 40818167) B40818167
theorem B18141407 : Blo 2123435 18141407 := bstep (se 1 (by rfl) ⟨13606055, by rfl⟩ : syracuseStep 18141407 = 27212111) B27212111
theorem B12094271 : Blo 2123435 12094271 := bstep (se 1 (by rfl) ⟨9070703, by rfl⟩ : syracuseStep 12094271 = 18141407) B18141407
theorem B8062847 : Blo 2123435 8062847 := bstep (se 1 (by rfl) ⟨6047135, by rfl⟩ : syracuseStep 8062847 = 12094271) B12094271
theorem B5375231 : Blo 2123435 5375231 := bstep (se 1 (by rfl) ⟨4031423, by rfl⟩ : syracuseStep 5375231 = 8062847) B8062847
theorem B3583487 : Blo 2123435 3583487 := bstep (se 1 (by rfl) ⟨2687615, by rfl⟩ : syracuseStep 3583487 = 5375231) B5375231
theorem B2388991 : Blo 2123435 2388991 := bstep (se 1 (by rfl) ⟨1791743, by rfl⟩ : syracuseStep 2388991 = 3583487) B3583487
theorem B3185321 : Blo 2123435 3185321 := bstep (se 2 (by rfl) ⟨1194495, by rfl⟩ : syracuseStep 3185321 = 2388991) B2388991
theorem B2123547 : Blo 2123435 2123547 := bstep (se 1 (by rfl) ⟨1592660, by rfl⟩ : syracuseStep 2123547 = 3185321) B3185321
theorem B3023573 : Blo 2123435 3023573 := bbase (se 7 (by rfl) ⟨35432, by rfl⟩ : syracuseStep 3023573 = 70865) (by norm_num)
theorem B8062861 : Blo 2123435 8062861 := bstep (se 3 (by rfl) ⟨1511786, by rfl⟩ : syracuseStep 8062861 = 3023573) B3023573
theorem B10750481 : Blo 2123435 10750481 := bstep (se 2 (by rfl) ⟨4031430, by rfl⟩ : syracuseStep 10750481 = 8062861) B8062861
theorem B7166987 : Blo 2123435 7166987 := bstep (se 1 (by rfl) ⟨5375240, by rfl⟩ : syracuseStep 7166987 = 10750481) B10750481
theorem B4777991 : Blo 2123435 4777991 := bstep (se 1 (by rfl) ⟨3583493, by rfl⟩ : syracuseStep 4777991 = 7166987) B7166987
theorem B3185327 : Blo 2123435 3185327 := bstep (se 1 (by rfl) ⟨2388995, by rfl⟩ : syracuseStep 3185327 = 4777991) B4777991
theorem B2123551 : Blo 2123435 2123551 := bstep (se 1 (by rfl) ⟨1592663, by rfl⟩ : syracuseStep 2123551 = 3185327) B3185327
theorem B3185333 : Blo 2123435 3185333 := bbase (se 5 (by rfl) ⟨149312, by rfl⟩ : syracuseStep 3185333 = 298625) (by norm_num)
theorem B2123555 : Blo 2123435 2123555 := bstep (se 1 (by rfl) ⟨1592666, by rfl⟩ : syracuseStep 2123555 = 3185333) B3185333
theorem B5375261 : Blo 2123435 5375261 := bbase (se 3 (by rfl) ⟨1007861, by rfl⟩ : syracuseStep 5375261 = 2015723) (by norm_num)
theorem B3583507 : Blo 2123435 3583507 := bstep (se 1 (by rfl) ⟨2687630, by rfl⟩ : syracuseStep 3583507 = 5375261) B5375261
theorem B4778009 : Blo 2123435 4778009 := bstep (se 2 (by rfl) ⟨1791753, by rfl⟩ : syracuseStep 4778009 = 3583507) B3583507
theorem B3185339 : Blo 2123435 3185339 := bstep (se 1 (by rfl) ⟨2389004, by rfl⟩ : syracuseStep 3185339 = 4778009) B4778009
theorem B2123559 : Blo 2123435 2123559 := bstep (se 1 (by rfl) ⟨1592669, by rfl⟩ : syracuseStep 2123559 = 3185339) B3185339
theorem B2389009 : Blo 2123435 2389009 := bbase (se 2 (by rfl) ⟨895878, by rfl⟩ : syracuseStep 2389009 = 1791757) (by norm_num)
theorem B3185345 : Blo 2123435 3185345 := bstep (se 2 (by rfl) ⟨1194504, by rfl⟩ : syracuseStep 3185345 = 2389009) B2389009
theorem B2123563 : Blo 2123435 2123563 := bstep (se 1 (by rfl) ⟨1592672, by rfl⟩ : syracuseStep 2123563 = 3185345) B3185345
theorem B4031461 : Blo 2123435 4031461 := bbase (se 4 (by rfl) ⟨377949, by rfl⟩ : syracuseStep 4031461 = 755899) (by norm_num)
theorem B5375281 : Blo 2123435 5375281 := bstep (se 2 (by rfl) ⟨2015730, by rfl⟩ : syracuseStep 5375281 = 4031461) B4031461
theorem B7167041 : Blo 2123435 7167041 := bstep (se 2 (by rfl) ⟨2687640, by rfl⟩ : syracuseStep 7167041 = 5375281) B5375281
theorem B4778027 : Blo 2123435 4778027 := bstep (se 1 (by rfl) ⟨3583520, by rfl⟩ : syracuseStep 4778027 = 7167041) B7167041
theorem B3185351 : Blo 2123435 3185351 := bstep (se 1 (by rfl) ⟨2389013, by rfl⟩ : syracuseStep 3185351 = 4778027) B4778027
theorem B2123567 : Blo 2123435 2123567 := bstep (se 1 (by rfl) ⟨1592675, by rfl⟩ : syracuseStep 2123567 = 3185351) B3185351
theorem B3185357 : Blo 2123435 3185357 := bbase (se 3 (by rfl) ⟨597254, by rfl⟩ : syracuseStep 3185357 = 1194509) (by norm_num)
theorem B2123571 : Blo 2123435 2123571 := bstep (se 1 (by rfl) ⟨1592678, by rfl⟩ : syracuseStep 2123571 = 3185357) B3185357
theorem B4778045 : Blo 2123435 4778045 := bbase (se 3 (by rfl) ⟨895883, by rfl⟩ : syracuseStep 4778045 = 1791767) (by norm_num)
theorem B3185363 : Blo 2123435 3185363 := bstep (se 1 (by rfl) ⟨2389022, by rfl⟩ : syracuseStep 3185363 = 4778045) B4778045
theorem B2123575 : Blo 2123435 2123575 := bstep (se 1 (by rfl) ⟨1592681, by rfl⟩ : syracuseStep 2123575 = 3185363) B3185363
theorem B3583541 : Blo 2123435 3583541 := bbase (se 5 (by rfl) ⟨167978, by rfl⟩ : syracuseStep 3583541 = 335957) (by norm_num)
theorem B2389027 : Blo 2123435 2389027 := bstep (se 1 (by rfl) ⟨1791770, by rfl⟩ : syracuseStep 2389027 = 3583541) B3583541
theorem B3185369 : Blo 2123435 3185369 := bstep (se 2 (by rfl) ⟨1194513, by rfl⟩ : syracuseStep 3185369 = 2389027) B2389027
theorem B2123579 : Blo 2123435 2123579 := bstep (se 1 (by rfl) ⟨1592684, by rfl⟩ : syracuseStep 2123579 = 3185369) B3185369
theorem B6047237 : Blo 2123435 6047237 := bbase (se 4 (by rfl) ⟨566928, by rfl⟩ : syracuseStep 6047237 = 1133857) (by norm_num)
theorem B16125965 : Blo 2123435 16125965 := bstep (se 3 (by rfl) ⟨3023618, by rfl⟩ : syracuseStep 16125965 = 6047237) B6047237
theorem B10750643 : Blo 2123435 10750643 := bstep (se 1 (by rfl) ⟨8062982, by rfl⟩ : syracuseStep 10750643 = 16125965) B16125965
theorem B7167095 : Blo 2123435 7167095 := bstep (se 1 (by rfl) ⟨5375321, by rfl⟩ : syracuseStep 7167095 = 10750643) B10750643
theorem B4778063 : Blo 2123435 4778063 := bstep (se 1 (by rfl) ⟨3583547, by rfl⟩ : syracuseStep 4778063 = 7167095) B7167095
theorem B3185375 : Blo 2123435 3185375 := bstep (se 1 (by rfl) ⟨2389031, by rfl⟩ : syracuseStep 3185375 = 4778063) B4778063
theorem B2123583 : Blo 2123435 2123583 := bstep (se 1 (by rfl) ⟨1592687, by rfl⟩ : syracuseStep 2123583 = 3185375) B3185375
theorem B3185381 : Blo 2123435 3185381 := bbase (se 4 (by rfl) ⟨298629, by rfl⟩ : syracuseStep 3185381 = 597259) (by norm_num)
theorem B2123587 : Blo 2123435 2123587 := bstep (se 1 (by rfl) ⟨1592690, by rfl⟩ : syracuseStep 2123587 = 3185381) B3185381
theorem B2551189 : Blo 2123435 2551189 := bbase (se 6 (by rfl) ⟨59793, by rfl⟩ : syracuseStep 2551189 = 119587) (by norm_num)
theorem B3401585 : Blo 2123435 3401585 := bstep (se 2 (by rfl) ⟨1275594, by rfl⟩ : syracuseStep 3401585 = 2551189) B2551189
theorem B2267723 : Blo 2123435 2267723 := bstep (se 1 (by rfl) ⟨1700792, by rfl⟩ : syracuseStep 2267723 = 3401585) B3401585
theorem B6047261 : Blo 2123435 6047261 := bstep (se 3 (by rfl) ⟨1133861, by rfl⟩ : syracuseStep 6047261 = 2267723) B2267723
theorem B4031507 : Blo 2123435 4031507 := bstep (se 1 (by rfl) ⟨3023630, by rfl⟩ : syracuseStep 4031507 = 6047261) B6047261
theorem B2687671 : Blo 2123435 2687671 := bstep (se 1 (by rfl) ⟨2015753, by rfl⟩ : syracuseStep 2687671 = 4031507) B4031507
theorem B3583561 : Blo 2123435 3583561 := bstep (se 2 (by rfl) ⟨1343835, by rfl⟩ : syracuseStep 3583561 = 2687671) B2687671
theorem B4778081 : Blo 2123435 4778081 := bstep (se 2 (by rfl) ⟨1791780, by rfl⟩ : syracuseStep 4778081 = 3583561) B3583561
theorem B3185387 : Blo 2123435 3185387 := bstep (se 1 (by rfl) ⟨2389040, by rfl⟩ : syracuseStep 3185387 = 4778081) B4778081
theorem B2123591 : Blo 2123435 2123591 := bstep (se 1 (by rfl) ⟨1592693, by rfl⟩ : syracuseStep 2123591 = 3185387) B3185387
theorem B2389045 : Blo 2123435 2389045 := bbase (se 5 (by rfl) ⟨111986, by rfl⟩ : syracuseStep 2389045 = 223973) (by norm_num)
theorem B3185393 : Blo 2123435 3185393 := bstep (se 2 (by rfl) ⟨1194522, by rfl⟩ : syracuseStep 3185393 = 2389045) B2389045
theorem B2123595 : Blo 2123435 2123595 := bstep (se 1 (by rfl) ⟨1592696, by rfl⟩ : syracuseStep 2123595 = 3185393) B3185393
theorem B2687681 : Blo 2123435 2687681 := bbase (se 2 (by rfl) ⟨1007880, by rfl⟩ : syracuseStep 2687681 = 2015761) (by norm_num)
theorem B7167149 : Blo 2123435 7167149 := bstep (se 3 (by rfl) ⟨1343840, by rfl⟩ : syracuseStep 7167149 = 2687681) B2687681
theorem B4778099 : Blo 2123435 4778099 := bstep (se 1 (by rfl) ⟨3583574, by rfl⟩ : syracuseStep 4778099 = 7167149) B7167149
theorem B3185399 : Blo 2123435 3185399 := bstep (se 1 (by rfl) ⟨2389049, by rfl⟩ : syracuseStep 3185399 = 4778099) B4778099
theorem B2123599 : Blo 2123435 2123599 := bstep (se 1 (by rfl) ⟨1592699, by rfl⟩ : syracuseStep 2123599 = 3185399) B3185399
theorem B3185405 : Blo 2123435 3185405 := bbase (se 3 (by rfl) ⟨597263, by rfl⟩ : syracuseStep 3185405 = 1194527) (by norm_num)
theorem B2123603 : Blo 2123435 2123603 := bstep (se 1 (by rfl) ⟨1592702, by rfl⟩ : syracuseStep 2123603 = 3185405) B3185405
theorem B4778117 : Blo 2123435 4778117 := bbase (se 4 (by rfl) ⟨447948, by rfl⟩ : syracuseStep 4778117 = 895897) (by norm_num)
theorem B3185411 : Blo 2123435 3185411 := bstep (se 1 (by rfl) ⟨2389058, by rfl⟩ : syracuseStep 3185411 = 4778117) B4778117
theorem B2123607 : Blo 2123435 2123607 := bstep (se 1 (by rfl) ⟨1592705, by rfl⟩ : syracuseStep 2123607 = 3185411) B3185411
theorem B2551213 : Blo 2123435 2551213 := bbase (se 3 (by rfl) ⟨478352, by rfl⟩ : syracuseStep 2551213 = 956705) (by norm_num)
theorem B3401617 : Blo 2123435 3401617 := bstep (se 2 (by rfl) ⟨1275606, by rfl⟩ : syracuseStep 3401617 = 2551213) B2551213
theorem B4535489 : Blo 2123435 4535489 := bstep (se 2 (by rfl) ⟨1700808, by rfl⟩ : syracuseStep 4535489 = 3401617) B3401617
theorem B3023659 : Blo 2123435 3023659 := bstep (se 1 (by rfl) ⟨2267744, by rfl⟩ : syracuseStep 3023659 = 4535489) B4535489
theorem B4031545 : Blo 2123435 4031545 := bstep (se 2 (by rfl) ⟨1511829, by rfl⟩ : syracuseStep 4031545 = 3023659) B3023659
theorem B5375393 : Blo 2123435 5375393 := bstep (se 2 (by rfl) ⟨2015772, by rfl⟩ : syracuseStep 5375393 = 4031545) B4031545
theorem B3583595 : Blo 2123435 3583595 := bstep (se 1 (by rfl) ⟨2687696, by rfl⟩ : syracuseStep 3583595 = 5375393) B5375393
theorem B2389063 : Blo 2123435 2389063 := bstep (se 1 (by rfl) ⟨1791797, by rfl⟩ : syracuseStep 2389063 = 3583595) B3583595
theorem B3185417 : Blo 2123435 3185417 := bstep (se 2 (by rfl) ⟨1194531, by rfl⟩ : syracuseStep 3185417 = 2389063) B2389063
theorem B2123611 : Blo 2123435 2123611 := bstep (se 1 (by rfl) ⟨1592708, by rfl⟩ : syracuseStep 2123611 = 3185417) B3185417
theorem B10750805 : Blo 2123435 10750805 := bbase (se 9 (by rfl) ⟨31496, by rfl⟩ : syracuseStep 10750805 = 62993) (by norm_num)
theorem B7167203 : Blo 2123435 7167203 := bstep (se 1 (by rfl) ⟨5375402, by rfl⟩ : syracuseStep 7167203 = 10750805) B10750805
theorem B4778135 : Blo 2123435 4778135 := bstep (se 1 (by rfl) ⟨3583601, by rfl⟩ : syracuseStep 4778135 = 7167203) B7167203
theorem B3185423 : Blo 2123435 3185423 := bstep (se 1 (by rfl) ⟨2389067, by rfl⟩ : syracuseStep 3185423 = 4778135) B4778135
theorem B2123615 : Blo 2123435 2123615 := bstep (se 1 (by rfl) ⟨1592711, by rfl⟩ : syracuseStep 2123615 = 3185423) B3185423
theorem B3185429 : Blo 2123435 3185429 := bbase (se 6 (by rfl) ⟨74658, by rfl⟩ : syracuseStep 3185429 = 149317) (by norm_num)
theorem B2123619 : Blo 2123435 2123619 := bstep (se 1 (by rfl) ⟨1592714, by rfl⟩ : syracuseStep 2123619 = 3185429) B3185429
theorem B13091797 : Blo 2123435 13091797 := bbase (se 7 (by rfl) ⟨153419, by rfl⟩ : syracuseStep 13091797 = 306839) (by norm_num)
theorem B17455729 : Blo 2123435 17455729 := bstep (se 2 (by rfl) ⟨6545898, by rfl⟩ : syracuseStep 17455729 = 13091797) B13091797
theorem B23274305 : Blo 2123435 23274305 := bstep (se 2 (by rfl) ⟨8727864, by rfl⟩ : syracuseStep 23274305 = 17455729) B17455729
theorem B15516203 : Blo 2123435 15516203 := bstep (se 1 (by rfl) ⟨11637152, by rfl⟩ : syracuseStep 15516203 = 23274305) B23274305
theorem B41376541 : Blo 2123435 41376541 := bstep (se 3 (by rfl) ⟨7758101, by rfl⟩ : syracuseStep 41376541 = 15516203) B15516203
theorem B55168721 : Blo 2123435 55168721 := bstep (se 2 (by rfl) ⟨20688270, by rfl⟩ : syracuseStep 55168721 = 41376541) B41376541
theorem B36779147 : Blo 2123435 36779147 := bstep (se 1 (by rfl) ⟨27584360, by rfl⟩ : syracuseStep 36779147 = 55168721) B55168721
theorem B24519431 : Blo 2123435 24519431 := bstep (se 1 (by rfl) ⟨18389573, by rfl⟩ : syracuseStep 24519431 = 36779147) B36779147
theorem B65385149 : Blo 2123435 65385149 := bstep (se 3 (by rfl) ⟨12259715, by rfl⟩ : syracuseStep 65385149 = 24519431) B24519431
theorem B174360397 : Blo 2123435 174360397 := bstep (se 3 (by rfl) ⟨32692574, by rfl⟩ : syracuseStep 174360397 = 65385149) B65385149
theorem B232480529 : Blo 2123435 232480529 := bstep (se 2 (by rfl) ⟨87180198, by rfl⟩ : syracuseStep 232480529 = 174360397) B174360397
theorem B154987019 : Blo 2123435 154987019 := bstep (se 1 (by rfl) ⟨116240264, by rfl⟩ : syracuseStep 154987019 = 232480529) B232480529
theorem B103324679 : Blo 2123435 103324679 := bstep (se 1 (by rfl) ⟨77493509, by rfl⟩ : syracuseStep 103324679 = 154987019) B154987019
theorem B68883119 : Blo 2123435 68883119 := bstep (se 1 (by rfl) ⟨51662339, by rfl⟩ : syracuseStep 68883119 = 103324679) B103324679
theorem B45922079 : Blo 2123435 45922079 := bstep (se 1 (by rfl) ⟨34441559, by rfl⟩ : syracuseStep 45922079 = 68883119) B68883119
theorem B30614719 : Blo 2123435 30614719 := bstep (se 1 (by rfl) ⟨22961039, by rfl⟩ : syracuseStep 30614719 = 45922079) B45922079
theorem B40819625 : Blo 2123435 40819625 := bstep (se 2 (by rfl) ⟨15307359, by rfl⟩ : syracuseStep 40819625 = 30614719) B30614719
theorem B27213083 : Blo 2123435 27213083 := bstep (se 1 (by rfl) ⟨20409812, by rfl⟩ : syracuseStep 27213083 = 40819625) B40819625
theorem B18142055 : Blo 2123435 18142055 := bstep (se 1 (by rfl) ⟨13606541, by rfl⟩ : syracuseStep 18142055 = 27213083) B27213083
theorem B12094703 : Blo 2123435 12094703 := bstep (se 1 (by rfl) ⟨9071027, by rfl⟩ : syracuseStep 12094703 = 18142055) B18142055
theorem B8063135 : Blo 2123435 8063135 := bstep (se 1 (by rfl) ⟨6047351, by rfl⟩ : syracuseStep 8063135 = 12094703) B12094703
theorem B5375423 : Blo 2123435 5375423 := bstep (se 1 (by rfl) ⟨4031567, by rfl⟩ : syracuseStep 5375423 = 8063135) B8063135
theorem B3583615 : Blo 2123435 3583615 := bstep (se 1 (by rfl) ⟨2687711, by rfl⟩ : syracuseStep 3583615 = 5375423) B5375423
theorem B4778153 : Blo 2123435 4778153 := bstep (se 2 (by rfl) ⟨1791807, by rfl⟩ : syracuseStep 4778153 = 3583615) B3583615
theorem B3185435 : Blo 2123435 3185435 := bstep (se 1 (by rfl) ⟨2389076, by rfl⟩ : syracuseStep 3185435 = 4778153) B4778153
theorem B2123623 : Blo 2123435 2123623 := bstep (se 1 (by rfl) ⟨1592717, by rfl⟩ : syracuseStep 2123623 = 3185435) B3185435
theorem B2389081 : Blo 2123435 2389081 := bbase (se 2 (by rfl) ⟨895905, by rfl⟩ : syracuseStep 2389081 = 1791811) (by norm_num)
theorem B3185441 : Blo 2123435 3185441 := bstep (se 2 (by rfl) ⟨1194540, by rfl⟩ : syracuseStep 3185441 = 2389081) B2389081
theorem B2123627 : Blo 2123435 2123627 := bstep (se 1 (by rfl) ⟨1592720, by rfl⟩ : syracuseStep 2123627 = 3185441) B3185441
theorem B16346357 : Blo 2123435 16346357 := bbase (se 5 (by rfl) ⟨766235, by rfl⟩ : syracuseStep 16346357 = 1532471) (by norm_num)
theorem B10897571 : Blo 2123435 10897571 := bstep (se 1 (by rfl) ⟨8173178, by rfl⟩ : syracuseStep 10897571 = 16346357) B16346357
theorem B7265047 : Blo 2123435 7265047 := bstep (se 1 (by rfl) ⟨5448785, by rfl⟩ : syracuseStep 7265047 = 10897571) B10897571
theorem B9686729 : Blo 2123435 9686729 := bstep (se 2 (by rfl) ⟨3632523, by rfl⟩ : syracuseStep 9686729 = 7265047) B7265047
theorem B6457819 : Blo 2123435 6457819 := bstep (se 1 (by rfl) ⟨4843364, by rfl⟩ : syracuseStep 6457819 = 9686729) B9686729
theorem B8610425 : Blo 2123435 8610425 := bstep (se 2 (by rfl) ⟨3228909, by rfl⟩ : syracuseStep 8610425 = 6457819) B6457819
theorem B5740283 : Blo 2123435 5740283 := bstep (se 1 (by rfl) ⟨4305212, by rfl⟩ : syracuseStep 5740283 = 8610425) B8610425
theorem B3826855 : Blo 2123435 3826855 := bstep (se 1 (by rfl) ⟨2870141, by rfl⟩ : syracuseStep 3826855 = 5740283) B5740283
theorem B5102473 : Blo 2123435 5102473 := bstep (se 2 (by rfl) ⟨1913427, by rfl⟩ : syracuseStep 5102473 = 3826855) B3826855
theorem B6803297 : Blo 2123435 6803297 := bstep (se 2 (by rfl) ⟨2551236, by rfl⟩ : syracuseStep 6803297 = 5102473) B5102473
theorem B4535531 : Blo 2123435 4535531 := bstep (se 1 (by rfl) ⟨3401648, by rfl⟩ : syracuseStep 4535531 = 6803297) B6803297
theorem B3023687 : Blo 2123435 3023687 := bstep (se 1 (by rfl) ⟨2267765, by rfl⟩ : syracuseStep 3023687 = 4535531) B4535531
theorem B8063165 : Blo 2123435 8063165 := bstep (se 3 (by rfl) ⟨1511843, by rfl⟩ : syracuseStep 8063165 = 3023687) B3023687
theorem B5375443 : Blo 2123435 5375443 := bstep (se 1 (by rfl) ⟨4031582, by rfl⟩ : syracuseStep 5375443 = 8063165) B8063165
theorem B7167257 : Blo 2123435 7167257 := bstep (se 2 (by rfl) ⟨2687721, by rfl⟩ : syracuseStep 7167257 = 5375443) B5375443
theorem B4778171 : Blo 2123435 4778171 := bstep (se 1 (by rfl) ⟨3583628, by rfl⟩ : syracuseStep 4778171 = 7167257) B7167257
theorem B3185447 : Blo 2123435 3185447 := bstep (se 1 (by rfl) ⟨2389085, by rfl⟩ : syracuseStep 3185447 = 4778171) B4778171
theorem B2123631 : Blo 2123435 2123631 := bstep (se 1 (by rfl) ⟨1592723, by rfl⟩ : syracuseStep 2123631 = 3185447) B3185447
theorem B3185453 : Blo 2123435 3185453 := bbase (se 3 (by rfl) ⟨597272, by rfl⟩ : syracuseStep 3185453 = 1194545) (by norm_num)
theorem B2123635 : Blo 2123435 2123635 := bstep (se 1 (by rfl) ⟨1592726, by rfl⟩ : syracuseStep 2123635 = 3185453) B3185453
theorem B4778189 : Blo 2123435 4778189 := bbase (se 3 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 4778189 = 1791821) (by norm_num)
theorem B3185459 : Blo 2123435 3185459 := bstep (se 1 (by rfl) ⟨2389094, by rfl⟩ : syracuseStep 3185459 = 4778189) B4778189
theorem B2123639 : Blo 2123435 2123639 := bstep (se 1 (by rfl) ⟨1592729, by rfl⟩ : syracuseStep 2123639 = 3185459) B3185459
theorem B2687737 : Blo 2123435 2687737 := bbase (se 2 (by rfl) ⟨1007901, by rfl⟩ : syracuseStep 2687737 = 2015803) (by norm_num)
theorem B3583649 : Blo 2123435 3583649 := bstep (se 2 (by rfl) ⟨1343868, by rfl⟩ : syracuseStep 3583649 = 2687737) B2687737
theorem B2389099 : Blo 2123435 2389099 := bstep (se 1 (by rfl) ⟨1791824, by rfl⟩ : syracuseStep 2389099 = 3583649) B3583649
theorem B3185465 : Blo 2123435 3185465 := bstep (se 2 (by rfl) ⟨1194549, by rfl⟩ : syracuseStep 3185465 = 2389099) B2389099
theorem B2123643 : Blo 2123435 2123643 := bstep (se 1 (by rfl) ⟨1592732, by rfl⟩ : syracuseStep 2123643 = 3185465) B3185465
theorem B5740325 : Blo 2123435 5740325 := bbase (se 4 (by rfl) ⟨538155, by rfl⟩ : syracuseStep 5740325 = 1076311) (by norm_num)
theorem B3826883 : Blo 2123435 3826883 := bstep (se 1 (by rfl) ⟨2870162, by rfl⟩ : syracuseStep 3826883 = 5740325) B5740325
theorem B10205021 : Blo 2123435 10205021 := bstep (se 3 (by rfl) ⟨1913441, by rfl⟩ : syracuseStep 10205021 = 3826883) B3826883
theorem B6803347 : Blo 2123435 6803347 := bstep (se 1 (by rfl) ⟨5102510, by rfl⟩ : syracuseStep 6803347 = 10205021) B10205021
theorem B9071129 : Blo 2123435 9071129 := bstep (se 2 (by rfl) ⟨3401673, by rfl⟩ : syracuseStep 9071129 = 6803347) B6803347
theorem B24189677 : Blo 2123435 24189677 := bstep (se 3 (by rfl) ⟨4535564, by rfl⟩ : syracuseStep 24189677 = 9071129) B9071129
theorem B16126451 : Blo 2123435 16126451 := bstep (se 1 (by rfl) ⟨12094838, by rfl⟩ : syracuseStep 16126451 = 24189677) B24189677
theorem B10750967 : Blo 2123435 10750967 := bstep (se 1 (by rfl) ⟨8063225, by rfl⟩ : syracuseStep 10750967 = 16126451) B16126451
theorem B7167311 : Blo 2123435 7167311 := bstep (se 1 (by rfl) ⟨5375483, by rfl⟩ : syracuseStep 7167311 = 10750967) B10750967
theorem B4778207 : Blo 2123435 4778207 := bstep (se 1 (by rfl) ⟨3583655, by rfl⟩ : syracuseStep 4778207 = 7167311) B7167311
theorem B3185471 : Blo 2123435 3185471 := bstep (se 1 (by rfl) ⟨2389103, by rfl⟩ : syracuseStep 3185471 = 4778207) B4778207
theorem B2123647 : Blo 2123435 2123647 := bstep (se 1 (by rfl) ⟨1592735, by rfl⟩ : syracuseStep 2123647 = 3185471) B3185471
theorem B3185477 : Blo 2123435 3185477 := bbase (se 4 (by rfl) ⟨298638, by rfl⟩ : syracuseStep 3185477 = 597277) (by norm_num)
theorem B2123651 : Blo 2123435 2123651 := bstep (se 1 (by rfl) ⟨1592738, by rfl⟩ : syracuseStep 2123651 = 3185477) B3185477
theorem B3583669 : Blo 2123435 3583669 := bbase (se 5 (by rfl) ⟨167984, by rfl⟩ : syracuseStep 3583669 = 335969) (by norm_num)
theorem B4778225 : Blo 2123435 4778225 := bstep (se 2 (by rfl) ⟨1791834, by rfl⟩ : syracuseStep 4778225 = 3583669) B3583669
theorem B3185483 : Blo 2123435 3185483 := bstep (se 1 (by rfl) ⟨2389112, by rfl⟩ : syracuseStep 3185483 = 4778225) B4778225
theorem B2123655 : Blo 2123435 2123655 := bstep (se 1 (by rfl) ⟨1592741, by rfl⟩ : syracuseStep 2123655 = 3185483) B3185483
theorem B2389117 : Blo 2123435 2389117 := bbase (se 3 (by rfl) ⟨447959, by rfl⟩ : syracuseStep 2389117 = 895919) (by norm_num)
theorem B3185489 : Blo 2123435 3185489 := bstep (se 2 (by rfl) ⟨1194558, by rfl⟩ : syracuseStep 3185489 = 2389117) B2389117
theorem B2123659 : Blo 2123435 2123659 := bstep (se 1 (by rfl) ⟨1592744, by rfl⟩ : syracuseStep 2123659 = 3185489) B3185489
theorem B7167365 : Blo 2123435 7167365 := bbase (se 4 (by rfl) ⟨671940, by rfl⟩ : syracuseStep 7167365 = 1343881) (by norm_num)
theorem B4778243 : Blo 2123435 4778243 := bstep (se 1 (by rfl) ⟨3583682, by rfl⟩ : syracuseStep 4778243 = 7167365) B7167365
theorem B3185495 : Blo 2123435 3185495 := bstep (se 1 (by rfl) ⟨2389121, by rfl⟩ : syracuseStep 3185495 = 4778243) B4778243
theorem B2123663 : Blo 2123435 2123663 := bstep (se 1 (by rfl) ⟨1592747, by rfl⟩ : syracuseStep 2123663 = 3185495) B3185495
theorem B3185501 : Blo 2123435 3185501 := bbase (se 3 (by rfl) ⟨597281, by rfl⟩ : syracuseStep 3185501 = 1194563) (by norm_num)
theorem B2123667 : Blo 2123435 2123667 := bstep (se 1 (by rfl) ⟨1592750, by rfl⟩ : syracuseStep 2123667 = 3185501) B3185501
theorem B4778261 : Blo 2123435 4778261 := bbase (se 6 (by rfl) ⟨111990, by rfl⟩ : syracuseStep 4778261 = 223981) (by norm_num)
theorem B3185507 : Blo 2123435 3185507 := bstep (se 1 (by rfl) ⟨2389130, by rfl⟩ : syracuseStep 3185507 = 4778261) B4778261
theorem B2123671 : Blo 2123435 2123671 := bstep (se 1 (by rfl) ⟨1592753, by rfl⟩ : syracuseStep 2123671 = 3185507) B3185507
theorem B8063333 : Blo 2123435 8063333 := bbase (se 4 (by rfl) ⟨755937, by rfl⟩ : syracuseStep 8063333 = 1511875) (by norm_num)
theorem B5375555 : Blo 2123435 5375555 := bstep (se 1 (by rfl) ⟨4031666, by rfl⟩ : syracuseStep 5375555 = 8063333) B8063333
theorem B3583703 : Blo 2123435 3583703 := bstep (se 1 (by rfl) ⟨2687777, by rfl⟩ : syracuseStep 3583703 = 5375555) B5375555
theorem B2389135 : Blo 2123435 2389135 := bstep (se 1 (by rfl) ⟨1791851, by rfl⟩ : syracuseStep 2389135 = 3583703) B3583703
theorem B3185513 : Blo 2123435 3185513 := bstep (se 2 (by rfl) ⟨1194567, by rfl⟩ : syracuseStep 3185513 = 2389135) B2389135
theorem B2123675 : Blo 2123435 2123675 := bstep (se 1 (by rfl) ⟨1592756, by rfl⟩ : syracuseStep 2123675 = 3185513) B3185513
theorem B3401725 : Blo 2123435 3401725 := bbase (se 3 (by rfl) ⟨637823, by rfl⟩ : syracuseStep 3401725 = 1275647) (by norm_num)
theorem B4535633 : Blo 2123435 4535633 := bstep (se 2 (by rfl) ⟨1700862, by rfl⟩ : syracuseStep 4535633 = 3401725) B3401725
theorem B12095021 : Blo 2123435 12095021 := bstep (se 3 (by rfl) ⟨2267816, by rfl⟩ : syracuseStep 12095021 = 4535633) B4535633
theorem B8063347 : Blo 2123435 8063347 := bstep (se 1 (by rfl) ⟨6047510, by rfl⟩ : syracuseStep 8063347 = 12095021) B12095021
theorem B10751129 : Blo 2123435 10751129 := bstep (se 2 (by rfl) ⟨4031673, by rfl⟩ : syracuseStep 10751129 = 8063347) B8063347
theorem B7167419 : Blo 2123435 7167419 := bstep (se 1 (by rfl) ⟨5375564, by rfl⟩ : syracuseStep 7167419 = 10751129) B10751129
theorem B4778279 : Blo 2123435 4778279 := bstep (se 1 (by rfl) ⟨3583709, by rfl⟩ : syracuseStep 4778279 = 7167419) B7167419
theorem B3185519 : Blo 2123435 3185519 := bstep (se 1 (by rfl) ⟨2389139, by rfl⟩ : syracuseStep 3185519 = 4778279) B4778279
theorem B2123679 : Blo 2123435 2123679 := bstep (se 1 (by rfl) ⟨1592759, by rfl⟩ : syracuseStep 2123679 = 3185519) B3185519
theorem B3185525 : Blo 2123435 3185525 := bbase (se 5 (by rfl) ⟨149321, by rfl⟩ : syracuseStep 3185525 = 298643) (by norm_num)
theorem B2123683 : Blo 2123435 2123683 := bstep (se 1 (by rfl) ⟨1592762, by rfl⟩ : syracuseStep 2123683 = 3185525) B3185525
theorem B6803477 : Blo 2123435 6803477 := bbase (se 6 (by rfl) ⟨159456, by rfl⟩ : syracuseStep 6803477 = 318913) (by norm_num)
theorem B4535651 : Blo 2123435 4535651 := bstep (se 1 (by rfl) ⟨3401738, by rfl⟩ : syracuseStep 4535651 = 6803477) B6803477
theorem B3023767 : Blo 2123435 3023767 := bstep (se 1 (by rfl) ⟨2267825, by rfl⟩ : syracuseStep 3023767 = 4535651) B4535651
theorem B4031689 : Blo 2123435 4031689 := bstep (se 2 (by rfl) ⟨1511883, by rfl⟩ : syracuseStep 4031689 = 3023767) B3023767
theorem B5375585 : Blo 2123435 5375585 := bstep (se 2 (by rfl) ⟨2015844, by rfl⟩ : syracuseStep 5375585 = 4031689) B4031689
theorem B3583723 : Blo 2123435 3583723 := bstep (se 1 (by rfl) ⟨2687792, by rfl⟩ : syracuseStep 3583723 = 5375585) B5375585
theorem B4778297 : Blo 2123435 4778297 := bstep (se 2 (by rfl) ⟨1791861, by rfl⟩ : syracuseStep 4778297 = 3583723) B3583723
theorem B3185531 : Blo 2123435 3185531 := bstep (se 1 (by rfl) ⟨2389148, by rfl⟩ : syracuseStep 3185531 = 4778297) B4778297
theorem B2123687 : Blo 2123435 2123687 := bstep (se 1 (by rfl) ⟨1592765, by rfl⟩ : syracuseStep 2123687 = 3185531) B3185531
theorem B2389153 : Blo 2123435 2389153 := bbase (se 2 (by rfl) ⟨895932, by rfl⟩ : syracuseStep 2389153 = 1791865) (by norm_num)
theorem B3185537 : Blo 2123435 3185537 := bstep (se 2 (by rfl) ⟨1194576, by rfl⟩ : syracuseStep 3185537 = 2389153) B2389153
theorem B2123691 : Blo 2123435 2123691 := bstep (se 1 (by rfl) ⟨1592768, by rfl⟩ : syracuseStep 2123691 = 3185537) B3185537
theorem B5375605 : Blo 2123435 5375605 := bbase (se 5 (by rfl) ⟨251981, by rfl⟩ : syracuseStep 5375605 = 503963) (by norm_num)
theorem B7167473 : Blo 2123435 7167473 := bstep (se 2 (by rfl) ⟨2687802, by rfl⟩ : syracuseStep 7167473 = 5375605) B5375605
theorem B4778315 : Blo 2123435 4778315 := bstep (se 1 (by rfl) ⟨3583736, by rfl⟩ : syracuseStep 4778315 = 7167473) B7167473
theorem B3185543 : Blo 2123435 3185543 := bstep (se 1 (by rfl) ⟨2389157, by rfl⟩ : syracuseStep 3185543 = 4778315) B4778315
theorem B2123695 : Blo 2123435 2123695 := bstep (se 1 (by rfl) ⟨1592771, by rfl⟩ : syracuseStep 2123695 = 3185543) B3185543
theorem B3185549 : Blo 2123435 3185549 := bbase (se 3 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 3185549 = 1194581) (by norm_num)
theorem B2123699 : Blo 2123435 2123699 := bstep (se 1 (by rfl) ⟨1592774, by rfl⟩ : syracuseStep 2123699 = 3185549) B3185549
theorem B4778333 : Blo 2123435 4778333 := bbase (se 3 (by rfl) ⟨895937, by rfl⟩ : syracuseStep 4778333 = 1791875) (by norm_num)
theorem B3185555 : Blo 2123435 3185555 := bstep (se 1 (by rfl) ⟨2389166, by rfl⟩ : syracuseStep 3185555 = 4778333) B4778333
theorem B2123703 : Blo 2123435 2123703 := bstep (se 1 (by rfl) ⟨1592777, by rfl⟩ : syracuseStep 2123703 = 3185555) B3185555
theorem B3583757 : Blo 2123435 3583757 := bbase (se 3 (by rfl) ⟨671954, by rfl⟩ : syracuseStep 3583757 = 1343909) (by norm_num)
theorem B2389171 : Blo 2123435 2389171 := bstep (se 1 (by rfl) ⟨1791878, by rfl⟩ : syracuseStep 2389171 = 3583757) B3583757
theorem B3185561 : Blo 2123435 3185561 := bstep (se 2 (by rfl) ⟨1194585, by rfl⟩ : syracuseStep 3185561 = 2389171) B2389171
theorem B2123707 : Blo 2123435 2123707 := bstep (se 1 (by rfl) ⟨1592780, by rfl⟩ : syracuseStep 2123707 = 3185561) B3185561
theorem B18142805 : Blo 2123435 18142805 := bbase (se 8 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 18142805 = 212611) (by norm_num)
theorem B12095203 : Blo 2123435 12095203 := bstep (se 1 (by rfl) ⟨9071402, by rfl⟩ : syracuseStep 12095203 = 18142805) B18142805
theorem B16126937 : Blo 2123435 16126937 := bstep (se 2 (by rfl) ⟨6047601, by rfl⟩ : syracuseStep 16126937 = 12095203) B12095203
theorem B10751291 : Blo 2123435 10751291 := bstep (se 1 (by rfl) ⟨8063468, by rfl⟩ : syracuseStep 10751291 = 16126937) B16126937
theorem B7167527 : Blo 2123435 7167527 := bstep (se 1 (by rfl) ⟨5375645, by rfl⟩ : syracuseStep 7167527 = 10751291) B10751291
theorem B4778351 : Blo 2123435 4778351 := bstep (se 1 (by rfl) ⟨3583763, by rfl⟩ : syracuseStep 4778351 = 7167527) B7167527
theorem B3185567 : Blo 2123435 3185567 := bstep (se 1 (by rfl) ⟨2389175, by rfl⟩ : syracuseStep 3185567 = 4778351) B4778351
theorem B2123711 : Blo 2123435 2123711 := bstep (se 1 (by rfl) ⟨1592783, by rfl⟩ : syracuseStep 2123711 = 3185567) B3185567
theorem B3185573 : Blo 2123435 3185573 := bbase (se 4 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 3185573 = 597295) (by norm_num)
theorem B2123715 : Blo 2123435 2123715 := bstep (se 1 (by rfl) ⟨1592786, by rfl⟩ : syracuseStep 2123715 = 3185573) B3185573
theorem B2687833 : Blo 2123435 2687833 := bbase (se 2 (by rfl) ⟨1007937, by rfl⟩ : syracuseStep 2687833 = 2015875) (by norm_num)
theorem B3583777 : Blo 2123435 3583777 := bstep (se 2 (by rfl) ⟨1343916, by rfl⟩ : syracuseStep 3583777 = 2687833) B2687833
theorem B4778369 : Blo 2123435 4778369 := bstep (se 2 (by rfl) ⟨1791888, by rfl⟩ : syracuseStep 4778369 = 3583777) B3583777
theorem B3185579 : Blo 2123435 3185579 := bstep (se 1 (by rfl) ⟨2389184, by rfl⟩ : syracuseStep 3185579 = 4778369) B4778369
theorem B2123719 : Blo 2123435 2123719 := bstep (se 1 (by rfl) ⟨1592789, by rfl⟩ : syracuseStep 2123719 = 3185579) B3185579
theorem B2389189 : Blo 2123435 2389189 := bbase (se 4 (by rfl) ⟨223986, by rfl⟩ : syracuseStep 2389189 = 447973) (by norm_num)
theorem B3185585 : Blo 2123435 3185585 := bstep (se 2 (by rfl) ⟨1194594, by rfl⟩ : syracuseStep 3185585 = 2389189) B2389189
theorem B2123723 : Blo 2123435 2123723 := bstep (se 1 (by rfl) ⟨1592792, by rfl⟩ : syracuseStep 2123723 = 3185585) B3185585
theorem B4031765 : Blo 2123435 4031765 := bbase (se 6 (by rfl) ⟨94494, by rfl⟩ : syracuseStep 4031765 = 188989) (by norm_num)
theorem B2687843 : Blo 2123435 2687843 := bstep (se 1 (by rfl) ⟨2015882, by rfl⟩ : syracuseStep 2687843 = 4031765) B4031765
theorem B7167581 : Blo 2123435 7167581 := bstep (se 3 (by rfl) ⟨1343921, by rfl⟩ : syracuseStep 7167581 = 2687843) B2687843
theorem B4778387 : Blo 2123435 4778387 := bstep (se 1 (by rfl) ⟨3583790, by rfl⟩ : syracuseStep 4778387 = 7167581) B7167581
theorem B3185591 : Blo 2123435 3185591 := bstep (se 1 (by rfl) ⟨2389193, by rfl⟩ : syracuseStep 3185591 = 4778387) B4778387
theorem B2123727 : Blo 2123435 2123727 := bstep (se 1 (by rfl) ⟨1592795, by rfl⟩ : syracuseStep 2123727 = 3185591) B3185591
theorem B3185597 : Blo 2123435 3185597 := bbase (se 3 (by rfl) ⟨597299, by rfl⟩ : syracuseStep 3185597 = 1194599) (by norm_num)
theorem B2123731 : Blo 2123435 2123731 := bstep (se 1 (by rfl) ⟨1592798, by rfl⟩ : syracuseStep 2123731 = 3185597) B3185597
theorem B4778405 : Blo 2123435 4778405 := bbase (se 4 (by rfl) ⟨447975, by rfl⟩ : syracuseStep 4778405 = 895951) (by norm_num)
theorem B3185603 : Blo 2123435 3185603 := bstep (se 1 (by rfl) ⟨2389202, by rfl⟩ : syracuseStep 3185603 = 4778405) B4778405
theorem B2123735 : Blo 2123435 2123735 := bstep (se 1 (by rfl) ⟨1592801, by rfl⟩ : syracuseStep 2123735 = 3185603) B3185603
theorem B5375717 : Blo 2123435 5375717 := bbase (se 4 (by rfl) ⟨503973, by rfl⟩ : syracuseStep 5375717 = 1007947) (by norm_num)
theorem B3583811 : Blo 2123435 3583811 := bstep (se 1 (by rfl) ⟨2687858, by rfl⟩ : syracuseStep 3583811 = 5375717) B5375717
theorem B2389207 : Blo 2123435 2389207 := bstep (se 1 (by rfl) ⟨1791905, by rfl⟩ : syracuseStep 2389207 = 3583811) B3583811
theorem B3185609 : Blo 2123435 3185609 := bstep (se 2 (by rfl) ⟨1194603, by rfl⟩ : syracuseStep 3185609 = 2389207) B2389207
theorem B2123739 : Blo 2123435 2123739 := bstep (se 1 (by rfl) ⟨1592804, by rfl⟩ : syracuseStep 2123739 = 3185609) B3185609
theorem B2267885 : Blo 2123435 2267885 := bbase (se 3 (by rfl) ⟨425228, by rfl⟩ : syracuseStep 2267885 = 850457) (by norm_num)
theorem B6047693 : Blo 2123435 6047693 := bstep (se 3 (by rfl) ⟨1133942, by rfl⟩ : syracuseStep 6047693 = 2267885) B2267885
theorem B4031795 : Blo 2123435 4031795 := bstep (se 1 (by rfl) ⟨3023846, by rfl⟩ : syracuseStep 4031795 = 6047693) B6047693
theorem B10751453 : Blo 2123435 10751453 := bstep (se 3 (by rfl) ⟨2015897, by rfl⟩ : syracuseStep 10751453 = 4031795) B4031795
theorem B7167635 : Blo 2123435 7167635 := bstep (se 1 (by rfl) ⟨5375726, by rfl⟩ : syracuseStep 7167635 = 10751453) B10751453
theorem B4778423 : Blo 2123435 4778423 := bstep (se 1 (by rfl) ⟨3583817, by rfl⟩ : syracuseStep 4778423 = 7167635) B7167635
theorem B3185615 : Blo 2123435 3185615 := bstep (se 1 (by rfl) ⟨2389211, by rfl⟩ : syracuseStep 3185615 = 4778423) B4778423
theorem B2123743 : Blo 2123435 2123743 := bstep (se 1 (by rfl) ⟨1592807, by rfl⟩ : syracuseStep 2123743 = 3185615) B3185615
theorem B3185621 : Blo 2123435 3185621 := bbase (se 7 (by rfl) ⟨37331, by rfl⟩ : syracuseStep 3185621 = 74663) (by norm_num)
theorem B2123747 : Blo 2123435 2123747 := bstep (se 1 (by rfl) ⟨1592810, by rfl⟩ : syracuseStep 2123747 = 3185621) B3185621
theorem B8063621 : Blo 2123435 8063621 := bbase (se 4 (by rfl) ⟨755964, by rfl⟩ : syracuseStep 8063621 = 1511929) (by norm_num)
theorem B5375747 : Blo 2123435 5375747 := bstep (se 1 (by rfl) ⟨4031810, by rfl⟩ : syracuseStep 5375747 = 8063621) B8063621
theorem B3583831 : Blo 2123435 3583831 := bstep (se 1 (by rfl) ⟨2687873, by rfl⟩ : syracuseStep 3583831 = 5375747) B5375747
theorem B4778441 : Blo 2123435 4778441 := bstep (se 2 (by rfl) ⟨1791915, by rfl⟩ : syracuseStep 4778441 = 3583831) B3583831
theorem B3185627 : Blo 2123435 3185627 := bstep (se 1 (by rfl) ⟨2389220, by rfl⟩ : syracuseStep 3185627 = 4778441) B4778441
theorem B2123751 : Blo 2123435 2123751 := bstep (se 1 (by rfl) ⟨1592813, by rfl⟩ : syracuseStep 2123751 = 3185627) B3185627
theorem B2389225 : Blo 2123435 2389225 := bbase (se 2 (by rfl) ⟨895959, by rfl⟩ : syracuseStep 2389225 = 1791919) (by norm_num)
theorem B3185633 : Blo 2123435 3185633 := bstep (se 2 (by rfl) ⟨1194612, by rfl⟩ : syracuseStep 3185633 = 2389225) B2389225
theorem B2123755 : Blo 2123435 2123755 := bstep (se 1 (by rfl) ⟨1592816, by rfl⟩ : syracuseStep 2123755 = 3185633) B3185633
theorem B12095477 : Blo 2123435 12095477 := bbase (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) (by norm_num)
theorem B8063651 : Blo 2123435 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B5375767 : Blo 2123435 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B7167689 : Blo 2123435 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B4778459 : Blo 2123435 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B3185639 : Blo 2123435 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B2123759 : Blo 2123435 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B3185645 : Blo 2123435 3185645 := bbase (se 3 (by rfl) ⟨597308, by rfl⟩ : syracuseStep 3185645 = 1194617) (by norm_num)
theorem B2123763 : Blo 2123435 2123763 := bstep (se 1 (by rfl) ⟨1592822, by rfl⟩ : syracuseStep 2123763 = 3185645) B3185645
theorem B4778477 : Blo 2123435 4778477 := bbase (se 3 (by rfl) ⟨895964, by rfl⟩ : syracuseStep 4778477 = 1791929) (by norm_num)
theorem B3185651 : Blo 2123435 3185651 := bstep (se 1 (by rfl) ⟨2389238, by rfl⟩ : syracuseStep 3185651 = 4778477) B4778477
theorem B2123767 : Blo 2123435 2123767 := bstep (se 1 (by rfl) ⟨1592825, by rfl⟩ : syracuseStep 2123767 = 3185651) B3185651
theorem B10205621 : Blo 2123435 10205621 := bbase (se 5 (by rfl) ⟨478388, by rfl⟩ : syracuseStep 10205621 = 956777) (by norm_num)
theorem B6803747 : Blo 2123435 6803747 := bstep (se 1 (by rfl) ⟨5102810, by rfl⟩ : syracuseStep 6803747 = 10205621) B10205621
theorem B4535831 : Blo 2123435 4535831 := bstep (se 1 (by rfl) ⟨3401873, by rfl⟩ : syracuseStep 4535831 = 6803747) B6803747
theorem B3023887 : Blo 2123435 3023887 := bstep (se 1 (by rfl) ⟨2267915, by rfl⟩ : syracuseStep 3023887 = 4535831) B4535831
theorem B4031849 : Blo 2123435 4031849 := bstep (se 2 (by rfl) ⟨1511943, by rfl⟩ : syracuseStep 4031849 = 3023887) B3023887
theorem B2687899 : Blo 2123435 2687899 := bstep (se 1 (by rfl) ⟨2015924, by rfl⟩ : syracuseStep 2687899 = 4031849) B4031849
theorem B3583865 : Blo 2123435 3583865 := bstep (se 2 (by rfl) ⟨1343949, by rfl⟩ : syracuseStep 3583865 = 2687899) B2687899
theorem B2389243 : Blo 2123435 2389243 := bstep (se 1 (by rfl) ⟨1791932, by rfl⟩ : syracuseStep 2389243 = 3583865) B3583865
theorem B3185657 : Blo 2123435 3185657 := bstep (se 2 (by rfl) ⟨1194621, by rfl⟩ : syracuseStep 3185657 = 2389243) B2389243
theorem B2123771 : Blo 2123435 2123771 := bstep (se 1 (by rfl) ⟨1592828, by rfl⟩ : syracuseStep 2123771 = 3185657) B3185657
theorem B117834581 : Blo 2123435 117834581 := bbase (se 9 (by rfl) ⟨345218, by rfl⟩ : syracuseStep 117834581 = 690437) (by norm_num)
theorem B78556387 : Blo 2123435 78556387 := bstep (se 1 (by rfl) ⟨58917290, by rfl⟩ : syracuseStep 78556387 = 117834581) B117834581
theorem B104741849 : Blo 2123435 104741849 := bstep (se 2 (by rfl) ⟨39278193, by rfl⟩ : syracuseStep 104741849 = 78556387) B78556387
theorem B279311597 : Blo 2123435 279311597 := bstep (se 3 (by rfl) ⟨52370924, by rfl⟩ : syracuseStep 279311597 = 104741849) B104741849
theorem B186207731 : Blo 2123435 186207731 := bstep (se 1 (by rfl) ⟨139655798, by rfl⟩ : syracuseStep 186207731 = 279311597) B279311597
theorem B124138487 : Blo 2123435 124138487 := bstep (se 1 (by rfl) ⟨93103865, by rfl⟩ : syracuseStep 124138487 = 186207731) B186207731
theorem B82758991 : Blo 2123435 82758991 := bstep (se 1 (by rfl) ⟨62069243, by rfl⟩ : syracuseStep 82758991 = 124138487) B124138487
theorem B110345321 : Blo 2123435 110345321 := bstep (se 2 (by rfl) ⟨41379495, by rfl⟩ : syracuseStep 110345321 = 82758991) B82758991
theorem B73563547 : Blo 2123435 73563547 := bstep (se 1 (by rfl) ⟨55172660, by rfl⟩ : syracuseStep 73563547 = 110345321) B110345321
theorem B98084729 : Blo 2123435 98084729 := bstep (se 2 (by rfl) ⟨36781773, by rfl⟩ : syracuseStep 98084729 = 73563547) B73563547
theorem B261559277 : Blo 2123435 261559277 := bstep (se 3 (by rfl) ⟨49042364, by rfl⟩ : syracuseStep 261559277 = 98084729) B98084729
theorem B174372851 : Blo 2123435 174372851 := bstep (se 1 (by rfl) ⟨130779638, by rfl⟩ : syracuseStep 174372851 = 261559277) B261559277
theorem B464994269 : Blo 2123435 464994269 := bstep (se 3 (by rfl) ⟨87186425, by rfl⟩ : syracuseStep 464994269 = 174372851) B174372851
theorem B309996179 : Blo 2123435 309996179 := bstep (se 1 (by rfl) ⟨232497134, by rfl⟩ : syracuseStep 309996179 = 464994269) B464994269
theorem B206664119 : Blo 2123435 206664119 := bstep (se 1 (by rfl) ⟨154998089, by rfl⟩ : syracuseStep 206664119 = 309996179) B309996179
theorem B137776079 : Blo 2123435 137776079 := bstep (se 1 (by rfl) ⟨103332059, by rfl⟩ : syracuseStep 137776079 = 206664119) B206664119
theorem B91850719 : Blo 2123435 91850719 := bstep (se 1 (by rfl) ⟨68888039, by rfl⟩ : syracuseStep 91850719 = 137776079) B137776079
theorem B122467625 : Blo 2123435 122467625 := bstep (se 2 (by rfl) ⟨45925359, by rfl⟩ : syracuseStep 122467625 = 91850719) B91850719
theorem B81645083 : Blo 2123435 81645083 := bstep (se 1 (by rfl) ⟨61233812, by rfl⟩ : syracuseStep 81645083 = 122467625) B122467625
theorem B54430055 : Blo 2123435 54430055 := bstep (se 1 (by rfl) ⟨40822541, by rfl⟩ : syracuseStep 54430055 = 81645083) B81645083
theorem B36286703 : Blo 2123435 36286703 := bstep (se 1 (by rfl) ⟨27215027, by rfl⟩ : syracuseStep 36286703 = 54430055) B54430055
theorem B24191135 : Blo 2123435 24191135 := bstep (se 1 (by rfl) ⟨18143351, by rfl⟩ : syracuseStep 24191135 = 36286703) B36286703
theorem B16127423 : Blo 2123435 16127423 := bstep (se 1 (by rfl) ⟨12095567, by rfl⟩ : syracuseStep 16127423 = 24191135) B24191135
theorem B10751615 : Blo 2123435 10751615 := bstep (se 1 (by rfl) ⟨8063711, by rfl⟩ : syracuseStep 10751615 = 16127423) B16127423
theorem B7167743 : Blo 2123435 7167743 := bstep (se 1 (by rfl) ⟨5375807, by rfl⟩ : syracuseStep 7167743 = 10751615) B10751615
theorem B4778495 : Blo 2123435 4778495 := bstep (se 1 (by rfl) ⟨3583871, by rfl⟩ : syracuseStep 4778495 = 7167743) B7167743
theorem B3185663 : Blo 2123435 3185663 := bstep (se 1 (by rfl) ⟨2389247, by rfl⟩ : syracuseStep 3185663 = 4778495) B4778495
theorem B2123775 : Blo 2123435 2123775 := bstep (se 1 (by rfl) ⟨1592831, by rfl⟩ : syracuseStep 2123775 = 3185663) B3185663
theorem B3185669 : Blo 2123435 3185669 := bbase (se 4 (by rfl) ⟨298656, by rfl⟩ : syracuseStep 3185669 = 597313) (by norm_num)
theorem B2123779 : Blo 2123435 2123779 := bstep (se 1 (by rfl) ⟨1592834, by rfl⟩ : syracuseStep 2123779 = 3185669) B3185669
theorem B3583885 : Blo 2123435 3583885 := bbase (se 3 (by rfl) ⟨671978, by rfl⟩ : syracuseStep 3583885 = 1343957) (by norm_num)
theorem B4778513 : Blo 2123435 4778513 := bstep (se 2 (by rfl) ⟨1791942, by rfl⟩ : syracuseStep 4778513 = 3583885) B3583885
theorem B3185675 : Blo 2123435 3185675 := bstep (se 1 (by rfl) ⟨2389256, by rfl⟩ : syracuseStep 3185675 = 4778513) B4778513
theorem B2123783 : Blo 2123435 2123783 := bstep (se 1 (by rfl) ⟨1592837, by rfl⟩ : syracuseStep 2123783 = 3185675) B3185675
theorem B2389261 : Blo 2123435 2389261 := bbase (se 3 (by rfl) ⟨447986, by rfl⟩ : syracuseStep 2389261 = 895973) (by norm_num)
theorem B3185681 : Blo 2123435 3185681 := bstep (se 2 (by rfl) ⟨1194630, by rfl⟩ : syracuseStep 3185681 = 2389261) B2389261
theorem B2123787 : Blo 2123435 2123787 := bstep (se 1 (by rfl) ⟨1592840, by rfl⟩ : syracuseStep 2123787 = 3185681) B3185681
theorem B7167797 : Blo 2123435 7167797 := bbase (se 5 (by rfl) ⟨335990, by rfl⟩ : syracuseStep 7167797 = 671981) (by norm_num)
theorem B4778531 : Blo 2123435 4778531 := bstep (se 1 (by rfl) ⟨3583898, by rfl⟩ : syracuseStep 4778531 = 7167797) B7167797
theorem B3185687 : Blo 2123435 3185687 := bstep (se 1 (by rfl) ⟨2389265, by rfl⟩ : syracuseStep 3185687 = 4778531) B4778531
theorem B2123791 : Blo 2123435 2123791 := bstep (se 1 (by rfl) ⟨1592843, by rfl⟩ : syracuseStep 2123791 = 3185687) B3185687
theorem B3185693 : Blo 2123435 3185693 := bbase (se 3 (by rfl) ⟨597317, by rfl⟩ : syracuseStep 3185693 = 1194635) (by norm_num)
theorem B2123795 : Blo 2123435 2123795 := bstep (se 1 (by rfl) ⟨1592846, by rfl⟩ : syracuseStep 2123795 = 3185693) B3185693
theorem B4778549 : Blo 2123435 4778549 := bbase (se 5 (by rfl) ⟨223994, by rfl⟩ : syracuseStep 4778549 = 447989) (by norm_num)
theorem B3185699 : Blo 2123435 3185699 := bstep (se 1 (by rfl) ⟨2389274, by rfl⟩ : syracuseStep 3185699 = 4778549) B4778549
theorem B2123799 : Blo 2123435 2123799 := bstep (se 1 (by rfl) ⟨1592849, by rfl⟩ : syracuseStep 2123799 = 3185699) B3185699
theorem B9071797 : Blo 2123435 9071797 := bbase (se 5 (by rfl) ⟨425240, by rfl⟩ : syracuseStep 9071797 = 850481) (by norm_num)
theorem B12095729 : Blo 2123435 12095729 := bstep (se 2 (by rfl) ⟨4535898, by rfl⟩ : syracuseStep 12095729 = 9071797) B9071797
theorem B8063819 : Blo 2123435 8063819 := bstep (se 1 (by rfl) ⟨6047864, by rfl⟩ : syracuseStep 8063819 = 12095729) B12095729
theorem B5375879 : Blo 2123435 5375879 := bstep (se 1 (by rfl) ⟨4031909, by rfl⟩ : syracuseStep 5375879 = 8063819) B8063819
theorem B3583919 : Blo 2123435 3583919 := bstep (se 1 (by rfl) ⟨2687939, by rfl⟩ : syracuseStep 3583919 = 5375879) B5375879
theorem B2389279 : Blo 2123435 2389279 := bstep (se 1 (by rfl) ⟨1791959, by rfl⟩ : syracuseStep 2389279 = 3583919) B3583919
theorem B3185705 : Blo 2123435 3185705 := bstep (se 2 (by rfl) ⟨1194639, by rfl⟩ : syracuseStep 3185705 = 2389279) B2389279
theorem B2123803 : Blo 2123435 2123803 := bstep (se 1 (by rfl) ⟨1592852, by rfl⟩ : syracuseStep 2123803 = 3185705) B3185705
theorem B9071813 : Blo 2123435 9071813 := bbase (se 4 (by rfl) ⟨850482, by rfl⟩ : syracuseStep 9071813 = 1700965) (by norm_num)
theorem B6047875 : Blo 2123435 6047875 := bstep (se 1 (by rfl) ⟨4535906, by rfl⟩ : syracuseStep 6047875 = 9071813) B9071813
theorem B8063833 : Blo 2123435 8063833 := bstep (se 2 (by rfl) ⟨3023937, by rfl⟩ : syracuseStep 8063833 = 6047875) B6047875
theorem B10751777 : Blo 2123435 10751777 := bstep (se 2 (by rfl) ⟨4031916, by rfl⟩ : syracuseStep 10751777 = 8063833) B8063833
theorem B7167851 : Blo 2123435 7167851 := bstep (se 1 (by rfl) ⟨5375888, by rfl⟩ : syracuseStep 7167851 = 10751777) B10751777
theorem B4778567 : Blo 2123435 4778567 := bstep (se 1 (by rfl) ⟨3583925, by rfl⟩ : syracuseStep 4778567 = 7167851) B7167851
theorem B3185711 : Blo 2123435 3185711 := bstep (se 1 (by rfl) ⟨2389283, by rfl⟩ : syracuseStep 3185711 = 4778567) B4778567
theorem B2123807 : Blo 2123435 2123807 := bstep (se 1 (by rfl) ⟨1592855, by rfl⟩ : syracuseStep 2123807 = 3185711) B3185711
theorem B3185717 : Blo 2123435 3185717 := bbase (se 5 (by rfl) ⟨149330, by rfl⟩ : syracuseStep 3185717 = 298661) (by norm_num)
theorem B2123811 : Blo 2123435 2123811 := bstep (se 1 (by rfl) ⟨1592858, by rfl⟩ : syracuseStep 2123811 = 3185717) B3185717
theorem B5375909 : Blo 2123435 5375909 := bbase (se 4 (by rfl) ⟨503991, by rfl⟩ : syracuseStep 5375909 = 1007983) (by norm_num)
theorem B3583939 : Blo 2123435 3583939 := bstep (se 1 (by rfl) ⟨2687954, by rfl⟩ : syracuseStep 3583939 = 5375909) B5375909
theorem B4778585 : Blo 2123435 4778585 := bstep (se 2 (by rfl) ⟨1791969, by rfl⟩ : syracuseStep 4778585 = 3583939) B3583939
theorem B3185723 : Blo 2123435 3185723 := bstep (se 1 (by rfl) ⟨2389292, by rfl⟩ : syracuseStep 3185723 = 4778585) B4778585
theorem B2123815 : Blo 2123435 2123815 := bstep (se 1 (by rfl) ⟨1592861, by rfl⟩ : syracuseStep 2123815 = 3185723) B3185723
theorem B2389297 : Blo 2123435 2389297 := bbase (se 2 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 2389297 = 1791973) (by norm_num)
theorem B3185729 : Blo 2123435 3185729 := bstep (se 2 (by rfl) ⟨1194648, by rfl⟩ : syracuseStep 3185729 = 2389297) B2389297
theorem B2123819 : Blo 2123435 2123819 := bstep (se 1 (by rfl) ⟨1592864, by rfl⟩ : syracuseStep 2123819 = 3185729) B3185729
theorem B4535941 : Blo 2123435 4535941 := bbase (se 4 (by rfl) ⟨425244, by rfl⟩ : syracuseStep 4535941 = 850489) (by norm_num)
theorem B6047921 : Blo 2123435 6047921 := bstep (se 2 (by rfl) ⟨2267970, by rfl⟩ : syracuseStep 6047921 = 4535941) B4535941
theorem B4031947 : Blo 2123435 4031947 := bstep (se 1 (by rfl) ⟨3023960, by rfl⟩ : syracuseStep 4031947 = 6047921) B6047921
theorem B5375929 : Blo 2123435 5375929 := bstep (se 2 (by rfl) ⟨2015973, by rfl⟩ : syracuseStep 5375929 = 4031947) B4031947
theorem B7167905 : Blo 2123435 7167905 := bstep (se 2 (by rfl) ⟨2687964, by rfl⟩ : syracuseStep 7167905 = 5375929) B5375929
theorem B4778603 : Blo 2123435 4778603 := bstep (se 1 (by rfl) ⟨3583952, by rfl⟩ : syracuseStep 4778603 = 7167905) B7167905
theorem B3185735 : Blo 2123435 3185735 := bstep (se 1 (by rfl) ⟨2389301, by rfl⟩ : syracuseStep 3185735 = 4778603) B4778603
theorem B2123823 : Blo 2123435 2123823 := bstep (se 1 (by rfl) ⟨1592867, by rfl⟩ : syracuseStep 2123823 = 3185735) B3185735
theorem B3185741 : Blo 2123435 3185741 := bbase (se 3 (by rfl) ⟨597326, by rfl⟩ : syracuseStep 3185741 = 1194653) (by norm_num)
theorem B2123827 : Blo 2123435 2123827 := bstep (se 1 (by rfl) ⟨1592870, by rfl⟩ : syracuseStep 2123827 = 3185741) B3185741
theorem B4778621 : Blo 2123435 4778621 := bbase (se 3 (by rfl) ⟨895991, by rfl⟩ : syracuseStep 4778621 = 1791983) (by norm_num)
theorem B3185747 : Blo 2123435 3185747 := bstep (se 1 (by rfl) ⟨2389310, by rfl⟩ : syracuseStep 3185747 = 4778621) B4778621
theorem B2123831 : Blo 2123435 2123831 := bstep (se 1 (by rfl) ⟨1592873, by rfl⟩ : syracuseStep 2123831 = 3185747) B3185747
theorem B3583973 : Blo 2123435 3583973 := bbase (se 4 (by rfl) ⟨335997, by rfl⟩ : syracuseStep 3583973 = 671995) (by norm_num)
theorem B2389315 : Blo 2123435 2389315 := bstep (se 1 (by rfl) ⟨1791986, by rfl⟩ : syracuseStep 2389315 = 3583973) B3583973
theorem B3185753 : Blo 2123435 3185753 := bstep (se 2 (by rfl) ⟨1194657, by rfl⟩ : syracuseStep 3185753 = 2389315) B2389315
theorem B2123835 : Blo 2123435 2123835 := bstep (se 1 (by rfl) ⟨1592876, by rfl⟩ : syracuseStep 2123835 = 3185753) B3185753
theorem B2621585 : Blo 2123435 2621585 := bbase (se 2 (by rfl) ⟨983094, by rfl⟩ : syracuseStep 2621585 = 1966189) (by norm_num)
theorem B6990893 : Blo 2123435 6990893 := bstep (se 3 (by rfl) ⟨1310792, by rfl⟩ : syracuseStep 6990893 = 2621585) B2621585
theorem B4660595 : Blo 2123435 4660595 := bstep (se 1 (by rfl) ⟨3495446, by rfl⟩ : syracuseStep 4660595 = 6990893) B6990893
theorem B3107063 : Blo 2123435 3107063 := bstep (se 1 (by rfl) ⟨2330297, by rfl⟩ : syracuseStep 3107063 = 4660595) B4660595
theorem B8285501 : Blo 2123435 8285501 := bstep (se 3 (by rfl) ⟨1553531, by rfl⟩ : syracuseStep 8285501 = 3107063) B3107063
theorem B22094669 : Blo 2123435 22094669 := bstep (se 3 (by rfl) ⟨4142750, by rfl⟩ : syracuseStep 22094669 = 8285501) B8285501
theorem B14729779 : Blo 2123435 14729779 := bstep (se 1 (by rfl) ⟨11047334, by rfl⟩ : syracuseStep 14729779 = 22094669) B22094669
theorem B19639705 : Blo 2123435 19639705 := bstep (se 2 (by rfl) ⟨7364889, by rfl⟩ : syracuseStep 19639705 = 14729779) B14729779
theorem B26186273 : Blo 2123435 26186273 := bstep (se 2 (by rfl) ⟨9819852, by rfl⟩ : syracuseStep 26186273 = 19639705) B19639705
theorem B17457515 : Blo 2123435 17457515 := bstep (se 1 (by rfl) ⟨13093136, by rfl⟩ : syracuseStep 17457515 = 26186273) B26186273
theorem B11638343 : Blo 2123435 11638343 := bstep (se 1 (by rfl) ⟨8728757, by rfl⟩ : syracuseStep 11638343 = 17457515) B17457515
theorem B31035581 : Blo 2123435 31035581 := bstep (se 3 (by rfl) ⟨5819171, by rfl⟩ : syracuseStep 31035581 = 11638343) B11638343
theorem B20690387 : Blo 2123435 20690387 := bstep (se 1 (by rfl) ⟨15517790, by rfl⟩ : syracuseStep 20690387 = 31035581) B31035581
theorem B13793591 : Blo 2123435 13793591 := bstep (se 1 (by rfl) ⟨10345193, by rfl⟩ : syracuseStep 13793591 = 20690387) B20690387
theorem B9195727 : Blo 2123435 9195727 := bstep (se 1 (by rfl) ⟨6896795, by rfl⟩ : syracuseStep 9195727 = 13793591) B13793591
theorem B12260969 : Blo 2123435 12260969 := bstep (se 2 (by rfl) ⟨4597863, by rfl⟩ : syracuseStep 12260969 = 9195727) B9195727
theorem B8173979 : Blo 2123435 8173979 := bstep (se 1 (by rfl) ⟨6130484, by rfl⟩ : syracuseStep 8173979 = 12260969) B12260969
theorem B5449319 : Blo 2123435 5449319 := bstep (se 1 (by rfl) ⟨4086989, by rfl⟩ : syracuseStep 5449319 = 8173979) B8173979
theorem B3632879 : Blo 2123435 3632879 := bstep (se 1 (by rfl) ⟨2724659, by rfl⟩ : syracuseStep 3632879 = 5449319) B5449319
theorem B2421919 : Blo 2123435 2421919 := bstep (se 1 (by rfl) ⟨1816439, by rfl⟩ : syracuseStep 2421919 = 3632879) B3632879
theorem B12916901 : Blo 2123435 12916901 := bstep (se 4 (by rfl) ⟨1210959, by rfl⟩ : syracuseStep 12916901 = 2421919) B2421919
theorem B8611267 : Blo 2123435 8611267 := bstep (se 1 (by rfl) ⟨6458450, by rfl⟩ : syracuseStep 8611267 = 12916901) B12916901
theorem B11481689 : Blo 2123435 11481689 := bstep (se 2 (by rfl) ⟨4305633, by rfl⟩ : syracuseStep 11481689 = 8611267) B8611267
theorem B7654459 : Blo 2123435 7654459 := bstep (se 1 (by rfl) ⟨5740844, by rfl⟩ : syracuseStep 7654459 = 11481689) B11481689
theorem B10205945 : Blo 2123435 10205945 := bstep (se 2 (by rfl) ⟨3827229, by rfl⟩ : syracuseStep 10205945 = 7654459) B7654459
theorem B6803963 : Blo 2123435 6803963 := bstep (se 1 (by rfl) ⟨5102972, by rfl⟩ : syracuseStep 6803963 = 10205945) B10205945
theorem B4535975 : Blo 2123435 4535975 := bstep (se 1 (by rfl) ⟨3401981, by rfl⟩ : syracuseStep 4535975 = 6803963) B6803963
theorem B3023983 : Blo 2123435 3023983 := bstep (se 1 (by rfl) ⟨2267987, by rfl⟩ : syracuseStep 3023983 = 4535975) B4535975
theorem B16127909 : Blo 2123435 16127909 := bstep (se 4 (by rfl) ⟨1511991, by rfl⟩ : syracuseStep 16127909 = 3023983) B3023983
theorem B10751939 : Blo 2123435 10751939 := bstep (se 1 (by rfl) ⟨8063954, by rfl⟩ : syracuseStep 10751939 = 16127909) B16127909
theorem B7167959 : Blo 2123435 7167959 := bstep (se 1 (by rfl) ⟨5375969, by rfl⟩ : syracuseStep 7167959 = 10751939) B10751939
theorem B4778639 : Blo 2123435 4778639 := bstep (se 1 (by rfl) ⟨3583979, by rfl⟩ : syracuseStep 4778639 = 7167959) B7167959
theorem B3185759 : Blo 2123435 3185759 := bstep (se 1 (by rfl) ⟨2389319, by rfl⟩ : syracuseStep 3185759 = 4778639) B4778639
theorem B2123839 : Blo 2123435 2123839 := bstep (se 1 (by rfl) ⟨1592879, by rfl⟩ : syracuseStep 2123839 = 3185759) B3185759
theorem B3185765 : Blo 2123435 3185765 := bbase (se 4 (by rfl) ⟨298665, by rfl⟩ : syracuseStep 3185765 = 597331) (by norm_num)
theorem B2123843 : Blo 2123435 2123843 := bstep (se 1 (by rfl) ⟨1592882, by rfl⟩ : syracuseStep 2123843 = 3185765) B3185765
theorem B3827245 : Blo 2123435 3827245 := bbase (se 3 (by rfl) ⟨717608, by rfl⟩ : syracuseStep 3827245 = 1435217) (by norm_num)
theorem B5102993 : Blo 2123435 5102993 := bstep (se 2 (by rfl) ⟨1913622, by rfl⟩ : syracuseStep 5102993 = 3827245) B3827245
theorem B3401995 : Blo 2123435 3401995 := bstep (se 1 (by rfl) ⟨2551496, by rfl⟩ : syracuseStep 3401995 = 5102993) B5102993
theorem B4535993 : Blo 2123435 4535993 := bstep (se 2 (by rfl) ⟨1700997, by rfl⟩ : syracuseStep 4535993 = 3401995) B3401995
theorem B3023995 : Blo 2123435 3023995 := bstep (se 1 (by rfl) ⟨2267996, by rfl⟩ : syracuseStep 3023995 = 4535993) B4535993
theorem B4031993 : Blo 2123435 4031993 := bstep (se 2 (by rfl) ⟨1511997, by rfl⟩ : syracuseStep 4031993 = 3023995) B3023995
theorem B2687995 : Blo 2123435 2687995 := bstep (se 1 (by rfl) ⟨2015996, by rfl⟩ : syracuseStep 2687995 = 4031993) B4031993
theorem B3583993 : Blo 2123435 3583993 := bstep (se 2 (by rfl) ⟨1343997, by rfl⟩ : syracuseStep 3583993 = 2687995) B2687995
theorem B4778657 : Blo 2123435 4778657 := bstep (se 2 (by rfl) ⟨1791996, by rfl⟩ : syracuseStep 4778657 = 3583993) B3583993
theorem B3185771 : Blo 2123435 3185771 := bstep (se 1 (by rfl) ⟨2389328, by rfl⟩ : syracuseStep 3185771 = 4778657) B4778657
theorem B2123847 : Blo 2123435 2123847 := bstep (se 1 (by rfl) ⟨1592885, by rfl⟩ : syracuseStep 2123847 = 3185771) B3185771
theorem B2389333 : Blo 2123435 2389333 := bbase (se 13 (by rfl) ⟨437, by rfl⟩ : syracuseStep 2389333 = 875) (by norm_num)
theorem B3185777 : Blo 2123435 3185777 := bstep (se 2 (by rfl) ⟨1194666, by rfl⟩ : syracuseStep 3185777 = 2389333) B2389333
theorem B2123851 : Blo 2123435 2123851 := bstep (se 1 (by rfl) ⟨1592888, by rfl⟩ : syracuseStep 2123851 = 3185777) B3185777
theorem B2688005 : Blo 2123435 2688005 := bbase (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) (by norm_num)
theorem B7168013 : Blo 2123435 7168013 := bstep (se 3 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 7168013 = 2688005) B2688005
theorem B4778675 : Blo 2123435 4778675 := bstep (se 1 (by rfl) ⟨3584006, by rfl⟩ : syracuseStep 4778675 = 7168013) B7168013
theorem B3185783 : Blo 2123435 3185783 := bstep (se 1 (by rfl) ⟨2389337, by rfl⟩ : syracuseStep 3185783 = 4778675) B4778675
theorem B2123855 : Blo 2123435 2123855 := bstep (se 1 (by rfl) ⟨1592891, by rfl⟩ : syracuseStep 2123855 = 3185783) B3185783
theorem B3185789 : Blo 2123435 3185789 := bbase (se 3 (by rfl) ⟨597335, by rfl⟩ : syracuseStep 3185789 = 1194671) (by norm_num)
theorem B2123859 : Blo 2123435 2123859 := bstep (se 1 (by rfl) ⟨1592894, by rfl⟩ : syracuseStep 2123859 = 3185789) B3185789
theorem B4778693 : Blo 2123435 4778693 := bbase (se 4 (by rfl) ⟨448002, by rfl⟩ : syracuseStep 4778693 = 896005) (by norm_num)
theorem B3185795 : Blo 2123435 3185795 := bstep (se 1 (by rfl) ⟨2389346, by rfl⟩ : syracuseStep 3185795 = 4778693) B4778693
theorem B2123863 : Blo 2123435 2123863 := bstep (se 1 (by rfl) ⟨1592897, by rfl⟩ : syracuseStep 2123863 = 3185795) B3185795
theorem B8611381 : Blo 2123435 8611381 := bbase (se 5 (by rfl) ⟨403658, by rfl⟩ : syracuseStep 8611381 = 807317) (by norm_num)
theorem B11481841 : Blo 2123435 11481841 := bstep (se 2 (by rfl) ⟨4305690, by rfl⟩ : syracuseStep 11481841 = 8611381) B8611381
theorem B15309121 : Blo 2123435 15309121 := bstep (se 2 (by rfl) ⟨5740920, by rfl⟩ : syracuseStep 15309121 = 11481841) B11481841
theorem B20412161 : Blo 2123435 20412161 := bstep (se 2 (by rfl) ⟨7654560, by rfl⟩ : syracuseStep 20412161 = 15309121) B15309121
theorem B13608107 : Blo 2123435 13608107 := bstep (se 1 (by rfl) ⟨10206080, by rfl⟩ : syracuseStep 13608107 = 20412161) B20412161
theorem B9072071 : Blo 2123435 9072071 := bstep (se 1 (by rfl) ⟨6804053, by rfl⟩ : syracuseStep 9072071 = 13608107) B13608107
theorem B6048047 : Blo 2123435 6048047 := bstep (se 1 (by rfl) ⟨4536035, by rfl⟩ : syracuseStep 6048047 = 9072071) B9072071
theorem B4032031 : Blo 2123435 4032031 := bstep (se 1 (by rfl) ⟨3024023, by rfl⟩ : syracuseStep 4032031 = 6048047) B6048047
theorem B5376041 : Blo 2123435 5376041 := bstep (se 2 (by rfl) ⟨2016015, by rfl⟩ : syracuseStep 5376041 = 4032031) B4032031
theorem B3584027 : Blo 2123435 3584027 := bstep (se 1 (by rfl) ⟨2688020, by rfl⟩ : syracuseStep 3584027 = 5376041) B5376041
theorem B2389351 : Blo 2123435 2389351 := bstep (se 1 (by rfl) ⟨1792013, by rfl⟩ : syracuseStep 2389351 = 3584027) B3584027
theorem B3185801 : Blo 2123435 3185801 := bstep (se 2 (by rfl) ⟨1194675, by rfl⟩ : syracuseStep 3185801 = 2389351) B2389351
theorem B2123867 : Blo 2123435 2123867 := bstep (se 1 (by rfl) ⟨1592900, by rfl⟩ : syracuseStep 2123867 = 3185801) B3185801
theorem B10752101 : Blo 2123435 10752101 := bbase (se 4 (by rfl) ⟨1008009, by rfl⟩ : syracuseStep 10752101 = 2016019) (by norm_num)
theorem B7168067 : Blo 2123435 7168067 := bstep (se 1 (by rfl) ⟨5376050, by rfl⟩ : syracuseStep 7168067 = 10752101) B10752101
theorem B4778711 : Blo 2123435 4778711 := bstep (se 1 (by rfl) ⟨3584033, by rfl⟩ : syracuseStep 4778711 = 7168067) B7168067
theorem B3185807 : Blo 2123435 3185807 := bstep (se 1 (by rfl) ⟨2389355, by rfl⟩ : syracuseStep 3185807 = 4778711) B4778711
theorem B2123871 : Blo 2123435 2123871 := bstep (se 1 (by rfl) ⟨1592903, by rfl⟩ : syracuseStep 2123871 = 3185807) B3185807
theorem B3185813 : Blo 2123435 3185813 := bbase (se 6 (by rfl) ⟨74667, by rfl⟩ : syracuseStep 3185813 = 149335) (by norm_num)
theorem B2123875 : Blo 2123435 2123875 := bstep (se 1 (by rfl) ⟨1592906, by rfl⟩ : syracuseStep 2123875 = 3185813) B3185813
theorem B8611429 : Blo 2123435 8611429 := bbase (se 4 (by rfl) ⟨807321, by rfl⟩ : syracuseStep 8611429 = 1614643) (by norm_num)
theorem B11481905 : Blo 2123435 11481905 := bstep (se 2 (by rfl) ⟨4305714, by rfl⟩ : syracuseStep 11481905 = 8611429) B8611429
theorem B7654603 : Blo 2123435 7654603 := bstep (se 1 (by rfl) ⟨5740952, by rfl⟩ : syracuseStep 7654603 = 11481905) B11481905
theorem B10206137 : Blo 2123435 10206137 := bstep (se 2 (by rfl) ⟨3827301, by rfl⟩ : syracuseStep 10206137 = 7654603) B7654603
theorem B6804091 : Blo 2123435 6804091 := bstep (se 1 (by rfl) ⟨5103068, by rfl⟩ : syracuseStep 6804091 = 10206137) B10206137
theorem B9072121 : Blo 2123435 9072121 := bstep (se 2 (by rfl) ⟨3402045, by rfl⟩ : syracuseStep 9072121 = 6804091) B6804091
theorem B12096161 : Blo 2123435 12096161 := bstep (se 2 (by rfl) ⟨4536060, by rfl⟩ : syracuseStep 12096161 = 9072121) B9072121
theorem B8064107 : Blo 2123435 8064107 := bstep (se 1 (by rfl) ⟨6048080, by rfl⟩ : syracuseStep 8064107 = 12096161) B12096161
theorem B5376071 : Blo 2123435 5376071 := bstep (se 1 (by rfl) ⟨4032053, by rfl⟩ : syracuseStep 5376071 = 8064107) B8064107
theorem B3584047 : Blo 2123435 3584047 := bstep (se 1 (by rfl) ⟨2688035, by rfl⟩ : syracuseStep 3584047 = 5376071) B5376071
theorem B4778729 : Blo 2123435 4778729 := bstep (se 2 (by rfl) ⟨1792023, by rfl⟩ : syracuseStep 4778729 = 3584047) B3584047
theorem B3185819 : Blo 2123435 3185819 := bstep (se 1 (by rfl) ⟨2389364, by rfl⟩ : syracuseStep 3185819 = 4778729) B4778729
theorem B2123879 : Blo 2123435 2123879 := bstep (se 1 (by rfl) ⟨1592909, by rfl⟩ : syracuseStep 2123879 = 3185819) B3185819
theorem B2389369 : Blo 2123435 2389369 := bbase (se 2 (by rfl) ⟨896013, by rfl⟩ : syracuseStep 2389369 = 1792027) (by norm_num)
theorem B3185825 : Blo 2123435 3185825 := bstep (se 2 (by rfl) ⟨1194684, by rfl⟩ : syracuseStep 3185825 = 2389369) B2389369
theorem B2123883 : Blo 2123435 2123883 := bstep (se 1 (by rfl) ⟨1592912, by rfl⟩ : syracuseStep 2123883 = 3185825) B3185825
theorem B11797397 : Blo 2123435 11797397 := bbase (se 6 (by rfl) ⟨276501, by rfl⟩ : syracuseStep 11797397 = 553003) (by norm_num)
theorem B7864931 : Blo 2123435 7864931 := bstep (se 1 (by rfl) ⟨5898698, by rfl⟩ : syracuseStep 7864931 = 11797397) B11797397
theorem B5243287 : Blo 2123435 5243287 := bstep (se 1 (by rfl) ⟨3932465, by rfl⟩ : syracuseStep 5243287 = 7864931) B7864931
theorem B6991049 : Blo 2123435 6991049 := bstep (se 2 (by rfl) ⟨2621643, by rfl⟩ : syracuseStep 6991049 = 5243287) B5243287
theorem B4660699 : Blo 2123435 4660699 := bstep (se 1 (by rfl) ⟨3495524, by rfl⟩ : syracuseStep 4660699 = 6991049) B6991049
theorem B6214265 : Blo 2123435 6214265 := bstep (se 2 (by rfl) ⟨2330349, by rfl⟩ : syracuseStep 6214265 = 4660699) B4660699
theorem B4142843 : Blo 2123435 4142843 := bstep (se 1 (by rfl) ⟨3107132, by rfl⟩ : syracuseStep 4142843 = 6214265) B6214265
theorem B2761895 : Blo 2123435 2761895 := bstep (se 1 (by rfl) ⟨2071421, by rfl⟩ : syracuseStep 2761895 = 4142843) B4142843
theorem B7365053 : Blo 2123435 7365053 := bstep (se 3 (by rfl) ⟨1380947, by rfl⟩ : syracuseStep 7365053 = 2761895) B2761895
theorem B19640141 : Blo 2123435 19640141 := bstep (se 3 (by rfl) ⟨3682526, by rfl⟩ : syracuseStep 19640141 = 7365053) B7365053
theorem B13093427 : Blo 2123435 13093427 := bstep (se 1 (by rfl) ⟨9820070, by rfl⟩ : syracuseStep 13093427 = 19640141) B19640141
theorem B34915805 : Blo 2123435 34915805 := bstep (se 3 (by rfl) ⟨6546713, by rfl⟩ : syracuseStep 34915805 = 13093427) B13093427
theorem B23277203 : Blo 2123435 23277203 := bstep (se 1 (by rfl) ⟨17457902, by rfl⟩ : syracuseStep 23277203 = 34915805) B34915805
theorem B15518135 : Blo 2123435 15518135 := bstep (se 1 (by rfl) ⟨11638601, by rfl⟩ : syracuseStep 15518135 = 23277203) B23277203
theorem B10345423 : Blo 2123435 10345423 := bstep (se 1 (by rfl) ⟨7759067, by rfl⟩ : syracuseStep 10345423 = 15518135) B15518135
theorem B13793897 : Blo 2123435 13793897 := bstep (se 2 (by rfl) ⟨5172711, by rfl⟩ : syracuseStep 13793897 = 10345423) B10345423
theorem B9195931 : Blo 2123435 9195931 := bstep (se 1 (by rfl) ⟨6896948, by rfl⟩ : syracuseStep 9195931 = 13793897) B13793897
theorem B12261241 : Blo 2123435 12261241 := bstep (se 2 (by rfl) ⟨4597965, by rfl⟩ : syracuseStep 12261241 = 9195931) B9195931
theorem B16348321 : Blo 2123435 16348321 := bstep (se 2 (by rfl) ⟨6130620, by rfl⟩ : syracuseStep 16348321 = 12261241) B12261241
theorem B21797761 : Blo 2123435 21797761 := bstep (se 2 (by rfl) ⟨8174160, by rfl⟩ : syracuseStep 21797761 = 16348321) B16348321
theorem B29063681 : Blo 2123435 29063681 := bstep (se 2 (by rfl) ⟨10898880, by rfl⟩ : syracuseStep 29063681 = 21797761) B21797761
theorem B19375787 : Blo 2123435 19375787 := bstep (se 1 (by rfl) ⟨14531840, by rfl⟩ : syracuseStep 19375787 = 29063681) B29063681
theorem B51668765 : Blo 2123435 51668765 := bstep (se 3 (by rfl) ⟨9687893, by rfl⟩ : syracuseStep 51668765 = 19375787) B19375787
theorem B34445843 : Blo 2123435 34445843 := bstep (se 1 (by rfl) ⟨25834382, by rfl⟩ : syracuseStep 34445843 = 51668765) B51668765
theorem B22963895 : Blo 2123435 22963895 := bstep (se 1 (by rfl) ⟨17222921, by rfl⟩ : syracuseStep 22963895 = 34445843) B34445843
theorem B15309263 : Blo 2123435 15309263 := bstep (se 1 (by rfl) ⟨11481947, by rfl⟩ : syracuseStep 15309263 = 22963895) B22963895
theorem B10206175 : Blo 2123435 10206175 := bstep (se 1 (by rfl) ⟨7654631, by rfl⟩ : syracuseStep 10206175 = 15309263) B15309263
theorem B13608233 : Blo 2123435 13608233 := bstep (se 2 (by rfl) ⟨5103087, by rfl⟩ : syracuseStep 13608233 = 10206175) B10206175
theorem B9072155 : Blo 2123435 9072155 := bstep (se 1 (by rfl) ⟨6804116, by rfl⟩ : syracuseStep 9072155 = 13608233) B13608233
theorem B6048103 : Blo 2123435 6048103 := bstep (se 1 (by rfl) ⟨4536077, by rfl⟩ : syracuseStep 6048103 = 9072155) B9072155
theorem B8064137 : Blo 2123435 8064137 := bstep (se 2 (by rfl) ⟨3024051, by rfl⟩ : syracuseStep 8064137 = 6048103) B6048103
theorem B5376091 : Blo 2123435 5376091 := bstep (se 1 (by rfl) ⟨4032068, by rfl⟩ : syracuseStep 5376091 = 8064137) B8064137
theorem B7168121 : Blo 2123435 7168121 := bstep (se 2 (by rfl) ⟨2688045, by rfl⟩ : syracuseStep 7168121 = 5376091) B5376091
theorem B4778747 : Blo 2123435 4778747 := bstep (se 1 (by rfl) ⟨3584060, by rfl⟩ : syracuseStep 4778747 = 7168121) B7168121
theorem B3185831 : Blo 2123435 3185831 := bstep (se 1 (by rfl) ⟨2389373, by rfl⟩ : syracuseStep 3185831 = 4778747) B4778747
theorem B2123887 : Blo 2123435 2123887 := bstep (se 1 (by rfl) ⟨1592915, by rfl⟩ : syracuseStep 2123887 = 3185831) B3185831
theorem B3185837 : Blo 2123435 3185837 := bbase (se 3 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 3185837 = 1194689) (by norm_num)
theorem B2123891 : Blo 2123435 2123891 := bstep (se 1 (by rfl) ⟨1592918, by rfl⟩ : syracuseStep 2123891 = 3185837) B3185837
theorem B4778765 : Blo 2123435 4778765 := bbase (se 3 (by rfl) ⟨896018, by rfl⟩ : syracuseStep 4778765 = 1792037) (by norm_num)
theorem B3185843 : Blo 2123435 3185843 := bstep (se 1 (by rfl) ⟨2389382, by rfl⟩ : syracuseStep 3185843 = 4778765) B4778765
theorem B2123895 : Blo 2123435 2123895 := bstep (se 1 (by rfl) ⟨1592921, by rfl⟩ : syracuseStep 2123895 = 3185843) B3185843
theorem B2688061 : Blo 2123435 2688061 := bbase (se 3 (by rfl) ⟨504011, by rfl⟩ : syracuseStep 2688061 = 1008023) (by norm_num)
theorem B3584081 : Blo 2123435 3584081 := bstep (se 2 (by rfl) ⟨1344030, by rfl⟩ : syracuseStep 3584081 = 2688061) B2688061
theorem B2389387 : Blo 2123435 2389387 := bstep (se 1 (by rfl) ⟨1792040, by rfl⟩ : syracuseStep 2389387 = 3584081) B3584081
theorem B3185849 : Blo 2123435 3185849 := bstep (se 2 (by rfl) ⟨1194693, by rfl⟩ : syracuseStep 3185849 = 2389387) B2389387
theorem B2123899 : Blo 2123435 2123899 := bstep (se 1 (by rfl) ⟨1592924, by rfl⟩ : syracuseStep 2123899 = 3185849) B3185849
theorem B8611525 : Blo 2123435 8611525 := bbase (se 4 (by rfl) ⟨807330, by rfl⟩ : syracuseStep 8611525 = 1614661) (by norm_num)
theorem B11482033 : Blo 2123435 11482033 := bstep (se 2 (by rfl) ⟨4305762, by rfl⟩ : syracuseStep 11482033 = 8611525) B8611525
theorem B15309377 : Blo 2123435 15309377 := bstep (se 2 (by rfl) ⟨5741016, by rfl⟩ : syracuseStep 15309377 = 11482033) B11482033
theorem B10206251 : Blo 2123435 10206251 := bstep (se 1 (by rfl) ⟨7654688, by rfl⟩ : syracuseStep 10206251 = 15309377) B15309377
theorem B6804167 : Blo 2123435 6804167 := bstep (se 1 (by rfl) ⟨5103125, by rfl⟩ : syracuseStep 6804167 = 10206251) B10206251
theorem B18144445 : Blo 2123435 18144445 := bstep (se 3 (by rfl) ⟨3402083, by rfl⟩ : syracuseStep 18144445 = 6804167) B6804167
theorem B24192593 : Blo 2123435 24192593 := bstep (se 2 (by rfl) ⟨9072222, by rfl⟩ : syracuseStep 24192593 = 18144445) B18144445
theorem B16128395 : Blo 2123435 16128395 := bstep (se 1 (by rfl) ⟨12096296, by rfl⟩ : syracuseStep 16128395 = 24192593) B24192593
theorem B10752263 : Blo 2123435 10752263 := bstep (se 1 (by rfl) ⟨8064197, by rfl⟩ : syracuseStep 10752263 = 16128395) B16128395
theorem B7168175 : Blo 2123435 7168175 := bstep (se 1 (by rfl) ⟨5376131, by rfl⟩ : syracuseStep 7168175 = 10752263) B10752263
theorem B4778783 : Blo 2123435 4778783 := bstep (se 1 (by rfl) ⟨3584087, by rfl⟩ : syracuseStep 4778783 = 7168175) B7168175
theorem B3185855 : Blo 2123435 3185855 := bstep (se 1 (by rfl) ⟨2389391, by rfl⟩ : syracuseStep 3185855 = 4778783) B4778783
theorem B2123903 : Blo 2123435 2123903 := bstep (se 1 (by rfl) ⟨1592927, by rfl⟩ : syracuseStep 2123903 = 3185855) B3185855
theorem B3185861 : Blo 2123435 3185861 := bbase (se 4 (by rfl) ⟨298674, by rfl⟩ : syracuseStep 3185861 = 597349) (by norm_num)
theorem B2123907 : Blo 2123435 2123907 := bstep (se 1 (by rfl) ⟨1592930, by rfl⟩ : syracuseStep 2123907 = 3185861) B3185861
theorem B3584101 : Blo 2123435 3584101 := bbase (se 4 (by rfl) ⟨336009, by rfl⟩ : syracuseStep 3584101 = 672019) (by norm_num)
theorem B4778801 : Blo 2123435 4778801 := bstep (se 2 (by rfl) ⟨1792050, by rfl⟩ : syracuseStep 4778801 = 3584101) B3584101
theorem B3185867 : Blo 2123435 3185867 := bstep (se 1 (by rfl) ⟨2389400, by rfl⟩ : syracuseStep 3185867 = 4778801) B4778801
theorem B2123911 : Blo 2123435 2123911 := bstep (se 1 (by rfl) ⟨1592933, by rfl⟩ : syracuseStep 2123911 = 3185867) B3185867
theorem B2389405 : Blo 2123435 2389405 := bbase (se 3 (by rfl) ⟨448013, by rfl⟩ : syracuseStep 2389405 = 896027) (by norm_num)
theorem B3185873 : Blo 2123435 3185873 := bstep (se 2 (by rfl) ⟨1194702, by rfl⟩ : syracuseStep 3185873 = 2389405) B2389405
theorem B2123915 : Blo 2123435 2123915 := bstep (se 1 (by rfl) ⟨1592936, by rfl⟩ : syracuseStep 2123915 = 3185873) B3185873
theorem B7168229 : Blo 2123435 7168229 := bbase (se 4 (by rfl) ⟨672021, by rfl⟩ : syracuseStep 7168229 = 1344043) (by norm_num)
theorem B4778819 : Blo 2123435 4778819 := bstep (se 1 (by rfl) ⟨3584114, by rfl⟩ : syracuseStep 4778819 = 7168229) B7168229
theorem B3185879 : Blo 2123435 3185879 := bstep (se 1 (by rfl) ⟨2389409, by rfl⟩ : syracuseStep 3185879 = 4778819) B4778819
theorem B2123919 : Blo 2123435 2123919 := bstep (se 1 (by rfl) ⟨1592939, by rfl⟩ : syracuseStep 2123919 = 3185879) B3185879
theorem B3185885 : Blo 2123435 3185885 := bbase (se 3 (by rfl) ⟨597353, by rfl⟩ : syracuseStep 3185885 = 1194707) (by norm_num)
theorem B2123923 : Blo 2123435 2123923 := bstep (se 1 (by rfl) ⟨1592942, by rfl⟩ : syracuseStep 2123923 = 3185885) B3185885
theorem B4778837 : Blo 2123435 4778837 := bbase (se 9 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 4778837 = 28001) (by norm_num)
theorem B3185891 : Blo 2123435 3185891 := bstep (se 1 (by rfl) ⟨2389418, by rfl⟩ : syracuseStep 3185891 = 4778837) B4778837
theorem B2123927 : Blo 2123435 2123927 := bstep (se 1 (by rfl) ⟨1592945, by rfl⟩ : syracuseStep 2123927 = 3185891) B3185891
theorem B6048229 : Blo 2123435 6048229 := bbase (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) (by norm_num)
theorem B8064305 : Blo 2123435 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B5376203 : Blo 2123435 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B3584135 : Blo 2123435 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B2389423 : Blo 2123435 2389423 := bstep (se 1 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 2389423 = 3584135) B3584135
theorem B3185897 : Blo 2123435 3185897 := bstep (se 2 (by rfl) ⟨1194711, by rfl⟩ : syracuseStep 3185897 = 2389423) B2389423
theorem B2123931 : Blo 2123435 2123931 := bstep (se 1 (by rfl) ⟨1592948, by rfl⟩ : syracuseStep 2123931 = 3185897) B3185897
theorem B2761957 : Blo 2123435 2761957 := bbase (se 4 (by rfl) ⟨258933, by rfl⟩ : syracuseStep 2761957 = 517867) (by norm_num)
theorem B14730437 : Blo 2123435 14730437 := bstep (se 4 (by rfl) ⟨1380978, by rfl⟩ : syracuseStep 14730437 = 2761957) B2761957
theorem B9820291 : Blo 2123435 9820291 := bstep (se 1 (by rfl) ⟨7365218, by rfl⟩ : syracuseStep 9820291 = 14730437) B14730437
theorem B13093721 : Blo 2123435 13093721 := bstep (se 2 (by rfl) ⟨4910145, by rfl⟩ : syracuseStep 13093721 = 9820291) B9820291
theorem B8729147 : Blo 2123435 8729147 := bstep (se 1 (by rfl) ⟨6546860, by rfl⟩ : syracuseStep 8729147 = 13093721) B13093721
theorem B23277725 : Blo 2123435 23277725 := bstep (se 3 (by rfl) ⟨4364573, by rfl⟩ : syracuseStep 23277725 = 8729147) B8729147
theorem B15518483 : Blo 2123435 15518483 := bstep (se 1 (by rfl) ⟨11638862, by rfl⟩ : syracuseStep 15518483 = 23277725) B23277725
theorem B10345655 : Blo 2123435 10345655 := bstep (se 1 (by rfl) ⟨7759241, by rfl⟩ : syracuseStep 10345655 = 15518483) B15518483
theorem B27588413 : Blo 2123435 27588413 := bstep (se 3 (by rfl) ⟨5172827, by rfl⟩ : syracuseStep 27588413 = 10345655) B10345655
theorem B18392275 : Blo 2123435 18392275 := bstep (se 1 (by rfl) ⟨13794206, by rfl⟩ : syracuseStep 18392275 = 27588413) B27588413
theorem B24523033 : Blo 2123435 24523033 := bstep (se 2 (by rfl) ⟨9196137, by rfl⟩ : syracuseStep 24523033 = 18392275) B18392275
theorem B32697377 : Blo 2123435 32697377 := bstep (se 2 (by rfl) ⟨12261516, by rfl⟩ : syracuseStep 32697377 = 24523033) B24523033
theorem B21798251 : Blo 2123435 21798251 := bstep (se 1 (by rfl) ⟨16348688, by rfl⟩ : syracuseStep 21798251 = 32697377) B32697377
theorem B14532167 : Blo 2123435 14532167 := bstep (se 1 (by rfl) ⟨10899125, by rfl⟩ : syracuseStep 14532167 = 21798251) B21798251
theorem B38752445 : Blo 2123435 38752445 := bstep (se 3 (by rfl) ⟨7266083, by rfl⟩ : syracuseStep 38752445 = 14532167) B14532167
theorem B25834963 : Blo 2123435 25834963 := bstep (se 1 (by rfl) ⟨19376222, by rfl⟩ : syracuseStep 25834963 = 38752445) B38752445
theorem B34446617 : Blo 2123435 34446617 := bstep (se 2 (by rfl) ⟨12917481, by rfl⟩ : syracuseStep 34446617 = 25834963) B25834963
theorem B22964411 : Blo 2123435 22964411 := bstep (se 1 (by rfl) ⟨17223308, by rfl⟩ : syracuseStep 22964411 = 34446617) B34446617
theorem B61238429 : Blo 2123435 61238429 := bstep (se 3 (by rfl) ⟨11482205, by rfl⟩ : syracuseStep 61238429 = 22964411) B22964411
theorem B40825619 : Blo 2123435 40825619 := bstep (se 1 (by rfl) ⟨30619214, by rfl⟩ : syracuseStep 40825619 = 61238429) B61238429
theorem B27217079 : Blo 2123435 27217079 := bstep (se 1 (by rfl) ⟨20412809, by rfl⟩ : syracuseStep 27217079 = 40825619) B40825619
theorem B18144719 : Blo 2123435 18144719 := bstep (se 1 (by rfl) ⟨13608539, by rfl⟩ : syracuseStep 18144719 = 27217079) B27217079
theorem B12096479 : Blo 2123435 12096479 := bstep (se 1 (by rfl) ⟨9072359, by rfl⟩ : syracuseStep 12096479 = 18144719) B18144719
theorem B8064319 : Blo 2123435 8064319 := bstep (se 1 (by rfl) ⟨6048239, by rfl⟩ : syracuseStep 8064319 = 12096479) B12096479
theorem B10752425 : Blo 2123435 10752425 := bstep (se 2 (by rfl) ⟨4032159, by rfl⟩ : syracuseStep 10752425 = 8064319) B8064319
theorem B7168283 : Blo 2123435 7168283 := bstep (se 1 (by rfl) ⟨5376212, by rfl⟩ : syracuseStep 7168283 = 10752425) B10752425
theorem B4778855 : Blo 2123435 4778855 := bstep (se 1 (by rfl) ⟨3584141, by rfl⟩ : syracuseStep 4778855 = 7168283) B7168283
theorem B3185903 : Blo 2123435 3185903 := bstep (se 1 (by rfl) ⟨2389427, by rfl⟩ : syracuseStep 3185903 = 4778855) B4778855
theorem B2123935 : Blo 2123435 2123935 := bstep (se 1 (by rfl) ⟨1592951, by rfl⟩ : syracuseStep 2123935 = 3185903) B3185903
theorem B3185909 : Blo 2123435 3185909 := bbase (se 5 (by rfl) ⟨149339, by rfl⟩ : syracuseStep 3185909 = 298679) (by norm_num)
theorem B2123939 : Blo 2123435 2123939 := bstep (se 1 (by rfl) ⟨1592954, by rfl⟩ : syracuseStep 2123939 = 3185909) B3185909
theorem B4305845 : Blo 2123435 4305845 := bbase (se 5 (by rfl) ⟨201836, by rfl⟩ : syracuseStep 4305845 = 403673) (by norm_num)
theorem B2870563 : Blo 2123435 2870563 := bstep (se 1 (by rfl) ⟨2152922, by rfl⟩ : syracuseStep 2870563 = 4305845) B4305845
theorem B3827417 : Blo 2123435 3827417 := bstep (se 2 (by rfl) ⟨1435281, by rfl⟩ : syracuseStep 3827417 = 2870563) B2870563
theorem B10206445 : Blo 2123435 10206445 := bstep (se 3 (by rfl) ⟨1913708, by rfl⟩ : syracuseStep 10206445 = 3827417) B3827417
theorem B13608593 : Blo 2123435 13608593 := bstep (se 2 (by rfl) ⟨5103222, by rfl⟩ : syracuseStep 13608593 = 10206445) B10206445
theorem B9072395 : Blo 2123435 9072395 := bstep (se 1 (by rfl) ⟨6804296, by rfl⟩ : syracuseStep 9072395 = 13608593) B13608593
theorem B6048263 : Blo 2123435 6048263 := bstep (se 1 (by rfl) ⟨4536197, by rfl⟩ : syracuseStep 6048263 = 9072395) B9072395
theorem B4032175 : Blo 2123435 4032175 := bstep (se 1 (by rfl) ⟨3024131, by rfl⟩ : syracuseStep 4032175 = 6048263) B6048263
theorem B5376233 : Blo 2123435 5376233 := bstep (se 2 (by rfl) ⟨2016087, by rfl⟩ : syracuseStep 5376233 = 4032175) B4032175
theorem B3584155 : Blo 2123435 3584155 := bstep (se 1 (by rfl) ⟨2688116, by rfl⟩ : syracuseStep 3584155 = 5376233) B5376233
theorem B4778873 : Blo 2123435 4778873 := bstep (se 2 (by rfl) ⟨1792077, by rfl⟩ : syracuseStep 4778873 = 3584155) B3584155
theorem B3185915 : Blo 2123435 3185915 := bstep (se 1 (by rfl) ⟨2389436, by rfl⟩ : syracuseStep 3185915 = 4778873) B4778873
theorem B2123943 : Blo 2123435 2123943 := bstep (se 1 (by rfl) ⟨1592957, by rfl⟩ : syracuseStep 2123943 = 3185915) B3185915
theorem B2389441 : Blo 2123435 2389441 := bbase (se 2 (by rfl) ⟨896040, by rfl⟩ : syracuseStep 2389441 = 1792081) (by norm_num)
theorem B3185921 : Blo 2123435 3185921 := bstep (se 2 (by rfl) ⟨1194720, by rfl⟩ : syracuseStep 3185921 = 2389441) B2389441
theorem B2123947 : Blo 2123435 2123947 := bstep (se 1 (by rfl) ⟨1592960, by rfl⟩ : syracuseStep 2123947 = 3185921) B3185921
theorem B5376253 : Blo 2123435 5376253 := bbase (se 3 (by rfl) ⟨1008047, by rfl⟩ : syracuseStep 5376253 = 2016095) (by norm_num)
theorem B7168337 : Blo 2123435 7168337 := bstep (se 2 (by rfl) ⟨2688126, by rfl⟩ : syracuseStep 7168337 = 5376253) B5376253
theorem B4778891 : Blo 2123435 4778891 := bstep (se 1 (by rfl) ⟨3584168, by rfl⟩ : syracuseStep 4778891 = 7168337) B7168337
theorem B3185927 : Blo 2123435 3185927 := bstep (se 1 (by rfl) ⟨2389445, by rfl⟩ : syracuseStep 3185927 = 4778891) B4778891
theorem B2123951 : Blo 2123435 2123951 := bstep (se 1 (by rfl) ⟨1592963, by rfl⟩ : syracuseStep 2123951 = 3185927) B3185927
theorem B3185933 : Blo 2123435 3185933 := bbase (se 3 (by rfl) ⟨597362, by rfl⟩ : syracuseStep 3185933 = 1194725) (by norm_num)
theorem B2123955 : Blo 2123435 2123955 := bstep (se 1 (by rfl) ⟨1592966, by rfl⟩ : syracuseStep 2123955 = 3185933) B3185933
theorem B4778909 : Blo 2123435 4778909 := bbase (se 3 (by rfl) ⟨896045, by rfl⟩ : syracuseStep 4778909 = 1792091) (by norm_num)
theorem B3185939 : Blo 2123435 3185939 := bstep (se 1 (by rfl) ⟨2389454, by rfl⟩ : syracuseStep 3185939 = 4778909) B4778909
theorem B2123959 : Blo 2123435 2123959 := bstep (se 1 (by rfl) ⟨1592969, by rfl⟩ : syracuseStep 2123959 = 3185939) B3185939
theorem B3584189 : Blo 2123435 3584189 := bbase (se 3 (by rfl) ⟨672035, by rfl⟩ : syracuseStep 3584189 = 1344071) (by norm_num)
theorem B2389459 : Blo 2123435 2389459 := bstep (se 1 (by rfl) ⟨1792094, by rfl⟩ : syracuseStep 2389459 = 3584189) B3584189
theorem B3185945 : Blo 2123435 3185945 := bstep (se 2 (by rfl) ⟨1194729, by rfl⟩ : syracuseStep 3185945 = 2389459) B2389459
theorem B2123963 : Blo 2123435 2123963 := bstep (se 1 (by rfl) ⟨1592972, by rfl⟩ : syracuseStep 2123963 = 3185945) B3185945
theorem B12096661 : Blo 2123435 12096661 := bbase (se 6 (by rfl) ⟨283515, by rfl⟩ : syracuseStep 12096661 = 567031) (by norm_num)
theorem B16128881 : Blo 2123435 16128881 := bstep (se 2 (by rfl) ⟨6048330, by rfl⟩ : syracuseStep 16128881 = 12096661) B12096661
theorem B10752587 : Blo 2123435 10752587 := bstep (se 1 (by rfl) ⟨8064440, by rfl⟩ : syracuseStep 10752587 = 16128881) B16128881
theorem B7168391 : Blo 2123435 7168391 := bstep (se 1 (by rfl) ⟨5376293, by rfl⟩ : syracuseStep 7168391 = 10752587) B10752587
theorem B4778927 : Blo 2123435 4778927 := bstep (se 1 (by rfl) ⟨3584195, by rfl⟩ : syracuseStep 4778927 = 7168391) B7168391
theorem B3185951 : Blo 2123435 3185951 := bstep (se 1 (by rfl) ⟨2389463, by rfl⟩ : syracuseStep 3185951 = 4778927) B4778927
theorem B2123967 : Blo 2123435 2123967 := bstep (se 1 (by rfl) ⟨1592975, by rfl⟩ : syracuseStep 2123967 = 3185951) B3185951
theorem B3185957 : Blo 2123435 3185957 := bbase (se 4 (by rfl) ⟨298683, by rfl⟩ : syracuseStep 3185957 = 597367) (by norm_num)
theorem B2123971 : Blo 2123435 2123971 := bstep (se 1 (by rfl) ⟨1592978, by rfl⟩ : syracuseStep 2123971 = 3185957) B3185957
theorem B2688157 : Blo 2123435 2688157 := bbase (se 3 (by rfl) ⟨504029, by rfl⟩ : syracuseStep 2688157 = 1008059) (by norm_num)
theorem B3584209 : Blo 2123435 3584209 := bstep (se 2 (by rfl) ⟨1344078, by rfl⟩ : syracuseStep 3584209 = 2688157) B2688157
theorem B4778945 : Blo 2123435 4778945 := bstep (se 2 (by rfl) ⟨1792104, by rfl⟩ : syracuseStep 4778945 = 3584209) B3584209
theorem B3185963 : Blo 2123435 3185963 := bstep (se 1 (by rfl) ⟨2389472, by rfl⟩ : syracuseStep 3185963 = 4778945) B4778945
theorem B2123975 : Blo 2123435 2123975 := bstep (se 1 (by rfl) ⟨1592981, by rfl⟩ : syracuseStep 2123975 = 3185963) B3185963
theorem B2389477 : Blo 2123435 2389477 := bbase (se 4 (by rfl) ⟨224013, by rfl⟩ : syracuseStep 2389477 = 448027) (by norm_num)
theorem B3185969 : Blo 2123435 3185969 := bstep (se 2 (by rfl) ⟨1194738, by rfl⟩ : syracuseStep 3185969 = 2389477) B2389477
theorem B2123979 : Blo 2123435 2123979 := bstep (se 1 (by rfl) ⟨1592984, by rfl⟩ : syracuseStep 2123979 = 3185969) B3185969
theorem B3229445 : Blo 2123435 3229445 := bbase (se 4 (by rfl) ⟨302760, by rfl⟩ : syracuseStep 3229445 = 605521) (by norm_num)
theorem B2152963 : Blo 2123435 2152963 := bstep (se 1 (by rfl) ⟨1614722, by rfl⟩ : syracuseStep 2152963 = 3229445) B3229445
theorem B11482469 : Blo 2123435 11482469 := bstep (se 4 (by rfl) ⟨1076481, by rfl⟩ : syracuseStep 11482469 = 2152963) B2152963
theorem B7654979 : Blo 2123435 7654979 := bstep (se 1 (by rfl) ⟨5741234, by rfl⟩ : syracuseStep 7654979 = 11482469) B11482469
theorem B5103319 : Blo 2123435 5103319 := bstep (se 1 (by rfl) ⟨3827489, by rfl⟩ : syracuseStep 5103319 = 7654979) B7654979
theorem B6804425 : Blo 2123435 6804425 := bstep (se 2 (by rfl) ⟨2551659, by rfl⟩ : syracuseStep 6804425 = 5103319) B5103319
theorem B4536283 : Blo 2123435 4536283 := bstep (se 1 (by rfl) ⟨3402212, by rfl⟩ : syracuseStep 4536283 = 6804425) B6804425
theorem B6048377 : Blo 2123435 6048377 := bstep (se 2 (by rfl) ⟨2268141, by rfl⟩ : syracuseStep 6048377 = 4536283) B4536283
theorem B4032251 : Blo 2123435 4032251 := bstep (se 1 (by rfl) ⟨3024188, by rfl⟩ : syracuseStep 4032251 = 6048377) B6048377
theorem B2688167 : Blo 2123435 2688167 := bstep (se 1 (by rfl) ⟨2016125, by rfl⟩ : syracuseStep 2688167 = 4032251) B4032251
theorem B7168445 : Blo 2123435 7168445 := bstep (se 3 (by rfl) ⟨1344083, by rfl⟩ : syracuseStep 7168445 = 2688167) B2688167
theorem B4778963 : Blo 2123435 4778963 := bstep (se 1 (by rfl) ⟨3584222, by rfl⟩ : syracuseStep 4778963 = 7168445) B7168445
theorem B3185975 : Blo 2123435 3185975 := bstep (se 1 (by rfl) ⟨2389481, by rfl⟩ : syracuseStep 3185975 = 4778963) B4778963
theorem B2123983 : Blo 2123435 2123983 := bstep (se 1 (by rfl) ⟨1592987, by rfl⟩ : syracuseStep 2123983 = 3185975) B3185975
theorem B3185981 : Blo 2123435 3185981 := bbase (se 3 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 3185981 = 1194743) (by norm_num)
theorem B2123987 : Blo 2123435 2123987 := bstep (se 1 (by rfl) ⟨1592990, by rfl⟩ : syracuseStep 2123987 = 3185981) B3185981
theorem B4778981 : Blo 2123435 4778981 := bbase (se 4 (by rfl) ⟨448029, by rfl⟩ : syracuseStep 4778981 = 896059) (by norm_num)
theorem B3185987 : Blo 2123435 3185987 := bstep (se 1 (by rfl) ⟨2389490, by rfl⟩ : syracuseStep 3185987 = 4778981) B4778981
theorem B2123991 : Blo 2123435 2123991 := bstep (se 1 (by rfl) ⟨1592993, by rfl⟩ : syracuseStep 2123991 = 3185987) B3185987
theorem B5376365 : Blo 2123435 5376365 := bbase (se 3 (by rfl) ⟨1008068, by rfl⟩ : syracuseStep 5376365 = 2016137) (by norm_num)
theorem B3584243 : Blo 2123435 3584243 := bstep (se 1 (by rfl) ⟨2688182, by rfl⟩ : syracuseStep 3584243 = 5376365) B5376365
theorem B2389495 : Blo 2123435 2389495 := bstep (se 1 (by rfl) ⟨1792121, by rfl⟩ : syracuseStep 2389495 = 3584243) B3584243
theorem B3185993 : Blo 2123435 3185993 := bstep (se 2 (by rfl) ⟨1194747, by rfl⟩ : syracuseStep 3185993 = 2389495) B2389495
theorem B2123995 : Blo 2123435 2123995 := bstep (se 1 (by rfl) ⟨1592996, by rfl⟩ : syracuseStep 2123995 = 3185993) B3185993
theorem B4536317 : Blo 2123435 4536317 := bbase (se 3 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 4536317 = 1701119) (by norm_num)
theorem B3024211 : Blo 2123435 3024211 := bstep (se 1 (by rfl) ⟨2268158, by rfl⟩ : syracuseStep 3024211 = 4536317) B4536317
theorem B4032281 : Blo 2123435 4032281 := bstep (se 2 (by rfl) ⟨1512105, by rfl⟩ : syracuseStep 4032281 = 3024211) B3024211
theorem B10752749 : Blo 2123435 10752749 := bstep (se 3 (by rfl) ⟨2016140, by rfl⟩ : syracuseStep 10752749 = 4032281) B4032281
theorem B7168499 : Blo 2123435 7168499 := bstep (se 1 (by rfl) ⟨5376374, by rfl⟩ : syracuseStep 7168499 = 10752749) B10752749
theorem B4778999 : Blo 2123435 4778999 := bstep (se 1 (by rfl) ⟨3584249, by rfl⟩ : syracuseStep 4778999 = 7168499) B7168499
theorem B3185999 : Blo 2123435 3185999 := bstep (se 1 (by rfl) ⟨2389499, by rfl⟩ : syracuseStep 3185999 = 4778999) B4778999
theorem B2123999 : Blo 2123435 2123999 := bstep (se 1 (by rfl) ⟨1592999, by rfl⟩ : syracuseStep 2123999 = 3185999) B3185999
theorem B3186005 : Blo 2123435 3186005 := bbase (se 11 (by rfl) ⟨2333, by rfl⟩ : syracuseStep 3186005 = 4667) (by norm_num)
theorem B2124003 : Blo 2123435 2124003 := bstep (se 1 (by rfl) ⟨1593002, by rfl⟩ : syracuseStep 2124003 = 3186005) B3186005
theorem B3827533 : Blo 2123435 3827533 := bbase (se 3 (by rfl) ⟨717662, by rfl⟩ : syracuseStep 3827533 = 1435325) (by norm_num)
theorem B5103377 : Blo 2123435 5103377 := bstep (se 2 (by rfl) ⟨1913766, by rfl⟩ : syracuseStep 5103377 = 3827533) B3827533
theorem B3402251 : Blo 2123435 3402251 := bstep (se 1 (by rfl) ⟨2551688, by rfl⟩ : syracuseStep 3402251 = 5103377) B5103377
theorem B2268167 : Blo 2123435 2268167 := bstep (se 1 (by rfl) ⟨1701125, by rfl⟩ : syracuseStep 2268167 = 3402251) B3402251
theorem B6048445 : Blo 2123435 6048445 := bstep (se 3 (by rfl) ⟨1134083, by rfl⟩ : syracuseStep 6048445 = 2268167) B2268167
theorem B8064593 : Blo 2123435 8064593 := bstep (se 2 (by rfl) ⟨3024222, by rfl⟩ : syracuseStep 8064593 = 6048445) B6048445
theorem B5376395 : Blo 2123435 5376395 := bstep (se 1 (by rfl) ⟨4032296, by rfl⟩ : syracuseStep 5376395 = 8064593) B8064593
theorem B3584263 : Blo 2123435 3584263 := bstep (se 1 (by rfl) ⟨2688197, by rfl⟩ : syracuseStep 3584263 = 5376395) B5376395
theorem B4779017 : Blo 2123435 4779017 := bstep (se 2 (by rfl) ⟨1792131, by rfl⟩ : syracuseStep 4779017 = 3584263) B3584263
theorem B3186011 : Blo 2123435 3186011 := bstep (se 1 (by rfl) ⟨2389508, by rfl⟩ : syracuseStep 3186011 = 4779017) B4779017
theorem B2124007 : Blo 2123435 2124007 := bstep (se 1 (by rfl) ⟨1593005, by rfl⟩ : syracuseStep 2124007 = 3186011) B3186011
theorem B2389513 : Blo 2123435 2389513 := bbase (se 2 (by rfl) ⟨896067, by rfl⟩ : syracuseStep 2389513 = 1792135) (by norm_num)
theorem B3186017 : Blo 2123435 3186017 := bstep (se 2 (by rfl) ⟨1194756, by rfl⟩ : syracuseStep 3186017 = 2389513) B2389513
theorem B2124011 : Blo 2123435 2124011 := bstep (se 1 (by rfl) ⟨1593008, by rfl⟩ : syracuseStep 2124011 = 3186017) B3186017
theorem B14730997 : Blo 2123435 14730997 := bbase (se 5 (by rfl) ⟨690515, by rfl⟩ : syracuseStep 14730997 = 1381031) (by norm_num)
theorem B19641329 : Blo 2123435 19641329 := bstep (se 2 (by rfl) ⟨7365498, by rfl⟩ : syracuseStep 19641329 = 14730997) B14730997
theorem B13094219 : Blo 2123435 13094219 := bstep (se 1 (by rfl) ⟨9820664, by rfl⟩ : syracuseStep 13094219 = 19641329) B19641329
theorem B8729479 : Blo 2123435 8729479 := bstep (se 1 (by rfl) ⟨6547109, by rfl⟩ : syracuseStep 8729479 = 13094219) B13094219
theorem B11639305 : Blo 2123435 11639305 := bstep (se 2 (by rfl) ⟨4364739, by rfl⟩ : syracuseStep 11639305 = 8729479) B8729479
theorem B15519073 : Blo 2123435 15519073 := bstep (se 2 (by rfl) ⟨5819652, by rfl⟩ : syracuseStep 15519073 = 11639305) B11639305
theorem B20692097 : Blo 2123435 20692097 := bstep (se 2 (by rfl) ⟨7759536, by rfl⟩ : syracuseStep 20692097 = 15519073) B15519073
theorem B13794731 : Blo 2123435 13794731 := bstep (se 1 (by rfl) ⟨10346048, by rfl⟩ : syracuseStep 13794731 = 20692097) B20692097
theorem B9196487 : Blo 2123435 9196487 := bstep (se 1 (by rfl) ⟨6897365, by rfl⟩ : syracuseStep 9196487 = 13794731) B13794731
theorem B6130991 : Blo 2123435 6130991 := bstep (se 1 (by rfl) ⟨4598243, by rfl⟩ : syracuseStep 6130991 = 9196487) B9196487
theorem B4087327 : Blo 2123435 4087327 := bstep (se 1 (by rfl) ⟨3065495, by rfl⟩ : syracuseStep 4087327 = 6130991) B6130991
theorem B5449769 : Blo 2123435 5449769 := bstep (se 2 (by rfl) ⟨2043663, by rfl⟩ : syracuseStep 5449769 = 4087327) B4087327
theorem B3633179 : Blo 2123435 3633179 := bstep (se 1 (by rfl) ⟨2724884, by rfl⟩ : syracuseStep 3633179 = 5449769) B5449769
theorem B9688477 : Blo 2123435 9688477 := bstep (se 3 (by rfl) ⟨1816589, by rfl⟩ : syracuseStep 9688477 = 3633179) B3633179
theorem B12917969 : Blo 2123435 12917969 := bstep (se 2 (by rfl) ⟨4844238, by rfl⟩ : syracuseStep 12917969 = 9688477) B9688477
theorem B8611979 : Blo 2123435 8611979 := bstep (se 1 (by rfl) ⟨6458984, by rfl⟩ : syracuseStep 8611979 = 12917969) B12917969
theorem B22965277 : Blo 2123435 22965277 := bstep (se 3 (by rfl) ⟨4305989, by rfl⟩ : syracuseStep 22965277 = 8611979) B8611979
theorem B30620369 : Blo 2123435 30620369 := bstep (se 2 (by rfl) ⟨11482638, by rfl⟩ : syracuseStep 30620369 = 22965277) B22965277
theorem B20413579 : Blo 2123435 20413579 := bstep (se 1 (by rfl) ⟨15310184, by rfl⟩ : syracuseStep 20413579 = 30620369) B30620369
theorem B27218105 : Blo 2123435 27218105 := bstep (se 2 (by rfl) ⟨10206789, by rfl⟩ : syracuseStep 27218105 = 20413579) B20413579
theorem B18145403 : Blo 2123435 18145403 := bstep (se 1 (by rfl) ⟨13609052, by rfl⟩ : syracuseStep 18145403 = 27218105) B27218105
theorem B12096935 : Blo 2123435 12096935 := bstep (se 1 (by rfl) ⟨9072701, by rfl⟩ : syracuseStep 12096935 = 18145403) B18145403
theorem B8064623 : Blo 2123435 8064623 := bstep (se 1 (by rfl) ⟨6048467, by rfl⟩ : syracuseStep 8064623 = 12096935) B12096935
theorem B5376415 : Blo 2123435 5376415 := bstep (se 1 (by rfl) ⟨4032311, by rfl⟩ : syracuseStep 5376415 = 8064623) B8064623
theorem B7168553 : Blo 2123435 7168553 := bstep (se 2 (by rfl) ⟨2688207, by rfl⟩ : syracuseStep 7168553 = 5376415) B5376415
theorem B4779035 : Blo 2123435 4779035 := bstep (se 1 (by rfl) ⟨3584276, by rfl⟩ : syracuseStep 4779035 = 7168553) B7168553
theorem B3186023 : Blo 2123435 3186023 := bstep (se 1 (by rfl) ⟨2389517, by rfl⟩ : syracuseStep 3186023 = 4779035) B4779035
theorem B2124015 : Blo 2123435 2124015 := bstep (se 1 (by rfl) ⟨1593011, by rfl⟩ : syracuseStep 2124015 = 3186023) B3186023
theorem B3186029 : Blo 2123435 3186029 := bbase (se 3 (by rfl) ⟨597380, by rfl⟩ : syracuseStep 3186029 = 1194761) (by norm_num)
theorem B2124019 : Blo 2123435 2124019 := bstep (se 1 (by rfl) ⟨1593014, by rfl⟩ : syracuseStep 2124019 = 3186029) B3186029
theorem B4779053 : Blo 2123435 4779053 := bbase (se 3 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 4779053 = 1792145) (by norm_num)
theorem B3186035 : Blo 2123435 3186035 := bstep (se 1 (by rfl) ⟨2389526, by rfl⟩ : syracuseStep 3186035 = 4779053) B4779053
theorem B2124023 : Blo 2123435 2124023 := bstep (se 1 (by rfl) ⟨1593017, by rfl⟩ : syracuseStep 2124023 = 3186035) B3186035
theorem B2870677 : Blo 2123435 2870677 := bbase (se 6 (by rfl) ⟨67281, by rfl⟩ : syracuseStep 2870677 = 134563) (by norm_num)
theorem B3827569 : Blo 2123435 3827569 := bstep (se 2 (by rfl) ⟨1435338, by rfl⟩ : syracuseStep 3827569 = 2870677) B2870677
theorem B5103425 : Blo 2123435 5103425 := bstep (se 2 (by rfl) ⟨1913784, by rfl⟩ : syracuseStep 5103425 = 3827569) B3827569
theorem B13609133 : Blo 2123435 13609133 := bstep (se 3 (by rfl) ⟨2551712, by rfl⟩ : syracuseStep 13609133 = 5103425) B5103425
theorem B9072755 : Blo 2123435 9072755 := bstep (se 1 (by rfl) ⟨6804566, by rfl⟩ : syracuseStep 9072755 = 13609133) B13609133
theorem B6048503 : Blo 2123435 6048503 := bstep (se 1 (by rfl) ⟨4536377, by rfl⟩ : syracuseStep 6048503 = 9072755) B9072755
theorem B4032335 : Blo 2123435 4032335 := bstep (se 1 (by rfl) ⟨3024251, by rfl⟩ : syracuseStep 4032335 = 6048503) B6048503
theorem B2688223 : Blo 2123435 2688223 := bstep (se 1 (by rfl) ⟨2016167, by rfl⟩ : syracuseStep 2688223 = 4032335) B4032335
theorem B3584297 : Blo 2123435 3584297 := bstep (se 2 (by rfl) ⟨1344111, by rfl⟩ : syracuseStep 3584297 = 2688223) B2688223
theorem B2389531 : Blo 2123435 2389531 := bstep (se 1 (by rfl) ⟨1792148, by rfl⟩ : syracuseStep 2389531 = 3584297) B3584297
theorem B3186041 : Blo 2123435 3186041 := bstep (se 2 (by rfl) ⟨1194765, by rfl⟩ : syracuseStep 3186041 = 2389531) B2389531
theorem B2124027 : Blo 2123435 2124027 := bstep (se 1 (by rfl) ⟨1593020, by rfl⟩ : syracuseStep 2124027 = 3186041) B3186041
theorem B3229517 : Blo 2123435 3229517 := bbase (se 3 (by rfl) ⟨605534, by rfl⟩ : syracuseStep 3229517 = 1211069) (by norm_num)
theorem B8612045 : Blo 2123435 8612045 := bstep (se 3 (by rfl) ⟨1614758, by rfl⟩ : syracuseStep 8612045 = 3229517) B3229517
theorem B5741363 : Blo 2123435 5741363 := bstep (se 1 (by rfl) ⟨4306022, by rfl⟩ : syracuseStep 5741363 = 8612045) B8612045
theorem B3827575 : Blo 2123435 3827575 := bstep (se 1 (by rfl) ⟨2870681, by rfl⟩ : syracuseStep 3827575 = 5741363) B5741363
theorem B5103433 : Blo 2123435 5103433 := bstep (se 2 (by rfl) ⟨1913787, by rfl⟩ : syracuseStep 5103433 = 3827575) B3827575
theorem B6804577 : Blo 2123435 6804577 := bstep (se 2 (by rfl) ⟨2551716, by rfl⟩ : syracuseStep 6804577 = 5103433) B5103433
theorem B36291077 : Blo 2123435 36291077 := bstep (se 4 (by rfl) ⟨3402288, by rfl⟩ : syracuseStep 36291077 = 6804577) B6804577
theorem B24194051 : Blo 2123435 24194051 := bstep (se 1 (by rfl) ⟨18145538, by rfl⟩ : syracuseStep 24194051 = 36291077) B36291077
theorem B16129367 : Blo 2123435 16129367 := bstep (se 1 (by rfl) ⟨12097025, by rfl⟩ : syracuseStep 16129367 = 24194051) B24194051
theorem B10752911 : Blo 2123435 10752911 := bstep (se 1 (by rfl) ⟨8064683, by rfl⟩ : syracuseStep 10752911 = 16129367) B16129367
theorem B7168607 : Blo 2123435 7168607 := bstep (se 1 (by rfl) ⟨5376455, by rfl⟩ : syracuseStep 7168607 = 10752911) B10752911
theorem B4779071 : Blo 2123435 4779071 := bstep (se 1 (by rfl) ⟨3584303, by rfl⟩ : syracuseStep 4779071 = 7168607) B7168607
theorem B3186047 : Blo 2123435 3186047 := bstep (se 1 (by rfl) ⟨2389535, by rfl⟩ : syracuseStep 3186047 = 4779071) B4779071
theorem B2124031 : Blo 2123435 2124031 := bstep (se 1 (by rfl) ⟨1593023, by rfl⟩ : syracuseStep 2124031 = 3186047) B3186047
theorem B3186053 : Blo 2123435 3186053 := bbase (se 4 (by rfl) ⟨298692, by rfl⟩ : syracuseStep 3186053 = 597385) (by norm_num)
theorem B2124035 : Blo 2123435 2124035 := bstep (se 1 (by rfl) ⟨1593026, by rfl⟩ : syracuseStep 2124035 = 3186053) B3186053
theorem B3584317 : Blo 2123435 3584317 := bbase (se 3 (by rfl) ⟨672059, by rfl⟩ : syracuseStep 3584317 = 1344119) (by norm_num)
theorem B4779089 : Blo 2123435 4779089 := bstep (se 2 (by rfl) ⟨1792158, by rfl⟩ : syracuseStep 4779089 = 3584317) B3584317
theorem B3186059 : Blo 2123435 3186059 := bstep (se 1 (by rfl) ⟨2389544, by rfl⟩ : syracuseStep 3186059 = 4779089) B4779089
theorem B2124039 : Blo 2123435 2124039 := bstep (se 1 (by rfl) ⟨1593029, by rfl⟩ : syracuseStep 2124039 = 3186059) B3186059
theorem B2389549 : Blo 2123435 2389549 := bbase (se 3 (by rfl) ⟨448040, by rfl⟩ : syracuseStep 2389549 = 896081) (by norm_num)
theorem B3186065 : Blo 2123435 3186065 := bstep (se 2 (by rfl) ⟨1194774, by rfl⟩ : syracuseStep 3186065 = 2389549) B2389549
theorem B2124043 : Blo 2123435 2124043 := bstep (se 1 (by rfl) ⟨1593032, by rfl⟩ : syracuseStep 2124043 = 3186065) B3186065
theorem B7168661 : Blo 2123435 7168661 := bbase (se 6 (by rfl) ⟨168015, by rfl⟩ : syracuseStep 7168661 = 336031) (by norm_num)
theorem B4779107 : Blo 2123435 4779107 := bstep (se 1 (by rfl) ⟨3584330, by rfl⟩ : syracuseStep 4779107 = 7168661) B7168661
theorem B3186071 : Blo 2123435 3186071 := bstep (se 1 (by rfl) ⟨2389553, by rfl⟩ : syracuseStep 3186071 = 4779107) B4779107
theorem B2124047 : Blo 2123435 2124047 := bstep (se 1 (by rfl) ⟨1593035, by rfl⟩ : syracuseStep 2124047 = 3186071) B3186071
theorem B3186077 : Blo 2123435 3186077 := bbase (se 3 (by rfl) ⟨597389, by rfl⟩ : syracuseStep 3186077 = 1194779) (by norm_num)
theorem B2124051 : Blo 2123435 2124051 := bstep (se 1 (by rfl) ⟨1593038, by rfl⟩ : syracuseStep 2124051 = 3186077) B3186077
theorem B4779125 : Blo 2123435 4779125 := bbase (se 5 (by rfl) ⟨224021, by rfl⟩ : syracuseStep 4779125 = 448043) (by norm_num)
theorem B3186083 : Blo 2123435 3186083 := bstep (se 1 (by rfl) ⟨2389562, by rfl⟩ : syracuseStep 3186083 = 4779125) B4779125
theorem B2124055 : Blo 2123435 2124055 := bstep (se 1 (by rfl) ⟨1593041, by rfl⟩ : syracuseStep 2124055 = 3186083) B3186083
theorem B18145781 : Blo 2123435 18145781 := bbase (se 5 (by rfl) ⟨850583, by rfl⟩ : syracuseStep 18145781 = 1701167) (by norm_num)
theorem B12097187 : Blo 2123435 12097187 := bstep (se 1 (by rfl) ⟨9072890, by rfl⟩ : syracuseStep 12097187 = 18145781) B18145781
theorem B8064791 : Blo 2123435 8064791 := bstep (se 1 (by rfl) ⟨6048593, by rfl⟩ : syracuseStep 8064791 = 12097187) B12097187
theorem B5376527 : Blo 2123435 5376527 := bstep (se 1 (by rfl) ⟨4032395, by rfl⟩ : syracuseStep 5376527 = 8064791) B8064791
theorem B3584351 : Blo 2123435 3584351 := bstep (se 1 (by rfl) ⟨2688263, by rfl⟩ : syracuseStep 3584351 = 5376527) B5376527
theorem B2389567 : Blo 2123435 2389567 := bstep (se 1 (by rfl) ⟨1792175, by rfl⟩ : syracuseStep 2389567 = 3584351) B3584351
theorem B3186089 : Blo 2123435 3186089 := bstep (se 2 (by rfl) ⟨1194783, by rfl⟩ : syracuseStep 3186089 = 2389567) B2389567
theorem B2124059 : Blo 2123435 2124059 := bstep (se 1 (by rfl) ⟨1593044, by rfl⟩ : syracuseStep 2124059 = 3186089) B3186089
theorem B8064805 : Blo 2123435 8064805 := bbase (se 4 (by rfl) ⟨756075, by rfl⟩ : syracuseStep 8064805 = 1512151) (by norm_num)
theorem B10753073 : Blo 2123435 10753073 := bstep (se 2 (by rfl) ⟨4032402, by rfl⟩ : syracuseStep 10753073 = 8064805) B8064805
theorem B7168715 : Blo 2123435 7168715 := bstep (se 1 (by rfl) ⟨5376536, by rfl⟩ : syracuseStep 7168715 = 10753073) B10753073
theorem B4779143 : Blo 2123435 4779143 := bstep (se 1 (by rfl) ⟨3584357, by rfl⟩ : syracuseStep 4779143 = 7168715) B7168715
theorem B3186095 : Blo 2123435 3186095 := bstep (se 1 (by rfl) ⟨2389571, by rfl⟩ : syracuseStep 3186095 = 4779143) B4779143
theorem B2124063 : Blo 2123435 2124063 := bstep (se 1 (by rfl) ⟨1593047, by rfl⟩ : syracuseStep 2124063 = 3186095) B3186095
theorem B3186101 : Blo 2123435 3186101 := bbase (se 5 (by rfl) ⟨149348, by rfl⟩ : syracuseStep 3186101 = 298697) (by norm_num)
theorem B2124067 : Blo 2123435 2124067 := bstep (se 1 (by rfl) ⟨1593050, by rfl⟩ : syracuseStep 2124067 = 3186101) B3186101
theorem B5376557 : Blo 2123435 5376557 := bbase (se 3 (by rfl) ⟨1008104, by rfl⟩ : syracuseStep 5376557 = 2016209) (by norm_num)
theorem B3584371 : Blo 2123435 3584371 := bstep (se 1 (by rfl) ⟨2688278, by rfl⟩ : syracuseStep 3584371 = 5376557) B5376557
theorem B4779161 : Blo 2123435 4779161 := bstep (se 2 (by rfl) ⟨1792185, by rfl⟩ : syracuseStep 4779161 = 3584371) B3584371
theorem B3186107 : Blo 2123435 3186107 := bstep (se 1 (by rfl) ⟨2389580, by rfl⟩ : syracuseStep 3186107 = 4779161) B4779161
theorem B2124071 : Blo 2123435 2124071 := bstep (se 1 (by rfl) ⟨1593053, by rfl⟩ : syracuseStep 2124071 = 3186107) B3186107
theorem B2389585 : Blo 2123435 2389585 := bbase (se 2 (by rfl) ⟨896094, by rfl⟩ : syracuseStep 2389585 = 1792189) (by norm_num)
theorem B3186113 : Blo 2123435 3186113 := bstep (se 2 (by rfl) ⟨1194792, by rfl⟩ : syracuseStep 3186113 = 2389585) B2389585
theorem B2124075 : Blo 2123435 2124075 := bstep (se 1 (by rfl) ⟨1593056, by rfl⟩ : syracuseStep 2124075 = 3186113) B3186113
theorem B3024325 : Blo 2123435 3024325 := bbase (se 4 (by rfl) ⟨283530, by rfl⟩ : syracuseStep 3024325 = 567061) (by norm_num)
theorem B4032433 : Blo 2123435 4032433 := bstep (se 2 (by rfl) ⟨1512162, by rfl⟩ : syracuseStep 4032433 = 3024325) B3024325
theorem B5376577 : Blo 2123435 5376577 := bstep (se 2 (by rfl) ⟨2016216, by rfl⟩ : syracuseStep 5376577 = 4032433) B4032433
theorem B7168769 : Blo 2123435 7168769 := bstep (se 2 (by rfl) ⟨2688288, by rfl⟩ : syracuseStep 7168769 = 5376577) B5376577
theorem B4779179 : Blo 2123435 4779179 := bstep (se 1 (by rfl) ⟨3584384, by rfl⟩ : syracuseStep 4779179 = 7168769) B7168769
theorem B3186119 : Blo 2123435 3186119 := bstep (se 1 (by rfl) ⟨2389589, by rfl⟩ : syracuseStep 3186119 = 4779179) B4779179
theorem B2124079 : Blo 2123435 2124079 := bstep (se 1 (by rfl) ⟨1593059, by rfl⟩ : syracuseStep 2124079 = 3186119) B3186119
theorem B3186125 : Blo 2123435 3186125 := bbase (se 3 (by rfl) ⟨597398, by rfl⟩ : syracuseStep 3186125 = 1194797) (by norm_num)
theorem B2124083 : Blo 2123435 2124083 := bstep (se 1 (by rfl) ⟨1593062, by rfl⟩ : syracuseStep 2124083 = 3186125) B3186125
theorem B4779197 : Blo 2123435 4779197 := bbase (se 3 (by rfl) ⟨896099, by rfl⟩ : syracuseStep 4779197 = 1792199) (by norm_num)
theorem B3186131 : Blo 2123435 3186131 := bstep (se 1 (by rfl) ⟨2389598, by rfl⟩ : syracuseStep 3186131 = 4779197) B4779197
theorem B2124087 : Blo 2123435 2124087 := bstep (se 1 (by rfl) ⟨1593065, by rfl⟩ : syracuseStep 2124087 = 3186131) B3186131
theorem B3584405 : Blo 2123435 3584405 := bbase (se 6 (by rfl) ⟨84009, by rfl⟩ : syracuseStep 3584405 = 168019) (by norm_num)
theorem B2389603 : Blo 2123435 2389603 := bstep (se 1 (by rfl) ⟨1792202, by rfl⟩ : syracuseStep 2389603 = 3584405) B3584405
theorem B3186137 : Blo 2123435 3186137 := bstep (se 2 (by rfl) ⟨1194801, by rfl⟩ : syracuseStep 3186137 = 2389603) B2389603
theorem B2124091 : Blo 2123435 2124091 := bstep (se 1 (by rfl) ⟨1593068, by rfl⟩ : syracuseStep 2124091 = 3186137) B3186137
theorem B7655381 : Blo 2123435 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B5103587 : Blo 2123435 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B13609565 : Blo 2123435 13609565 := bstep (se 3 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 13609565 = 5103587) B5103587
theorem B9073043 : Blo 2123435 9073043 := bstep (se 1 (by rfl) ⟨6804782, by rfl⟩ : syracuseStep 9073043 = 13609565) B13609565
theorem B6048695 : Blo 2123435 6048695 := bstep (se 1 (by rfl) ⟨4536521, by rfl⟩ : syracuseStep 6048695 = 9073043) B9073043
theorem B16129853 : Blo 2123435 16129853 := bstep (se 3 (by rfl) ⟨3024347, by rfl⟩ : syracuseStep 16129853 = 6048695) B6048695
theorem B10753235 : Blo 2123435 10753235 := bstep (se 1 (by rfl) ⟨8064926, by rfl⟩ : syracuseStep 10753235 = 16129853) B16129853
theorem B7168823 : Blo 2123435 7168823 := bstep (se 1 (by rfl) ⟨5376617, by rfl⟩ : syracuseStep 7168823 = 10753235) B10753235
theorem B4779215 : Blo 2123435 4779215 := bstep (se 1 (by rfl) ⟨3584411, by rfl⟩ : syracuseStep 4779215 = 7168823) B7168823
theorem B3186143 : Blo 2123435 3186143 := bstep (se 1 (by rfl) ⟨2389607, by rfl⟩ : syracuseStep 3186143 = 4779215) B4779215
theorem B2124095 : Blo 2123435 2124095 := bstep (se 1 (by rfl) ⟨1593071, by rfl⟩ : syracuseStep 2124095 = 3186143) B3186143
theorem B3186149 : Blo 2123435 3186149 := bbase (se 4 (by rfl) ⟨298701, by rfl⟩ : syracuseStep 3186149 = 597403) (by norm_num)
theorem B2124099 : Blo 2123435 2124099 := bstep (se 1 (by rfl) ⟨1593074, by rfl⟩ : syracuseStep 2124099 = 3186149) B3186149
theorem B5449997 : Blo 2123435 5449997 := bbase (se 3 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 5449997 = 2043749) (by norm_num)
theorem B3633331 : Blo 2123435 3633331 := bstep (se 1 (by rfl) ⟨2724998, by rfl⟩ : syracuseStep 3633331 = 5449997) B5449997
theorem B4844441 : Blo 2123435 4844441 := bstep (se 2 (by rfl) ⟨1816665, by rfl⟩ : syracuseStep 4844441 = 3633331) B3633331
theorem B3229627 : Blo 2123435 3229627 := bstep (se 1 (by rfl) ⟨2422220, by rfl⟩ : syracuseStep 3229627 = 4844441) B4844441
theorem B4306169 : Blo 2123435 4306169 := bstep (se 2 (by rfl) ⟨1614813, by rfl⟩ : syracuseStep 4306169 = 3229627) B3229627
theorem B11483117 : Blo 2123435 11483117 := bstep (se 3 (by rfl) ⟨2153084, by rfl⟩ : syracuseStep 11483117 = 4306169) B4306169
theorem B7655411 : Blo 2123435 7655411 := bstep (se 1 (by rfl) ⟨5741558, by rfl⟩ : syracuseStep 7655411 = 11483117) B11483117
theorem B20414429 : Blo 2123435 20414429 := bstep (se 3 (by rfl) ⟨3827705, by rfl⟩ : syracuseStep 20414429 = 7655411) B7655411
theorem B13609619 : Blo 2123435 13609619 := bstep (se 1 (by rfl) ⟨10207214, by rfl⟩ : syracuseStep 13609619 = 20414429) B20414429
theorem B9073079 : Blo 2123435 9073079 := bstep (se 1 (by rfl) ⟨6804809, by rfl⟩ : syracuseStep 9073079 = 13609619) B13609619
theorem B6048719 : Blo 2123435 6048719 := bstep (se 1 (by rfl) ⟨4536539, by rfl⟩ : syracuseStep 6048719 = 9073079) B9073079
theorem B4032479 : Blo 2123435 4032479 := bstep (se 1 (by rfl) ⟨3024359, by rfl⟩ : syracuseStep 4032479 = 6048719) B6048719
theorem B2688319 : Blo 2123435 2688319 := bstep (se 1 (by rfl) ⟨2016239, by rfl⟩ : syracuseStep 2688319 = 4032479) B4032479
theorem B3584425 : Blo 2123435 3584425 := bstep (se 2 (by rfl) ⟨1344159, by rfl⟩ : syracuseStep 3584425 = 2688319) B2688319
theorem B4779233 : Blo 2123435 4779233 := bstep (se 2 (by rfl) ⟨1792212, by rfl⟩ : syracuseStep 4779233 = 3584425) B3584425
theorem B3186155 : Blo 2123435 3186155 := bstep (se 1 (by rfl) ⟨2389616, by rfl⟩ : syracuseStep 3186155 = 4779233) B4779233
theorem B2124103 : Blo 2123435 2124103 := bstep (se 1 (by rfl) ⟨1593077, by rfl⟩ : syracuseStep 2124103 = 3186155) B3186155
theorem B2389621 : Blo 2123435 2389621 := bbase (se 5 (by rfl) ⟨112013, by rfl⟩ : syracuseStep 2389621 = 224027) (by norm_num)
theorem B3186161 : Blo 2123435 3186161 := bstep (se 2 (by rfl) ⟨1194810, by rfl⟩ : syracuseStep 3186161 = 2389621) B2389621
theorem B2124107 : Blo 2123435 2124107 := bstep (se 1 (by rfl) ⟨1593080, by rfl⟩ : syracuseStep 2124107 = 3186161) B3186161
theorem B2688329 : Blo 2123435 2688329 := bbase (se 2 (by rfl) ⟨1008123, by rfl⟩ : syracuseStep 2688329 = 2016247) (by norm_num)
theorem B7168877 : Blo 2123435 7168877 := bstep (se 3 (by rfl) ⟨1344164, by rfl⟩ : syracuseStep 7168877 = 2688329) B2688329
theorem B4779251 : Blo 2123435 4779251 := bstep (se 1 (by rfl) ⟨3584438, by rfl⟩ : syracuseStep 4779251 = 7168877) B7168877
theorem B3186167 : Blo 2123435 3186167 := bstep (se 1 (by rfl) ⟨2389625, by rfl⟩ : syracuseStep 3186167 = 4779251) B4779251
theorem B2124111 : Blo 2123435 2124111 := bstep (se 1 (by rfl) ⟨1593083, by rfl⟩ : syracuseStep 2124111 = 3186167) B3186167
theorem B3186173 : Blo 2123435 3186173 := bbase (se 3 (by rfl) ⟨597407, by rfl⟩ : syracuseStep 3186173 = 1194815) (by norm_num)
theorem B2124115 : Blo 2123435 2124115 := bstep (se 1 (by rfl) ⟨1593086, by rfl⟩ : syracuseStep 2124115 = 3186173) B3186173
theorem B4779269 : Blo 2123435 4779269 := bbase (se 4 (by rfl) ⟨448056, by rfl⟩ : syracuseStep 4779269 = 896113) (by norm_num)
theorem B3186179 : Blo 2123435 3186179 := bstep (se 1 (by rfl) ⟨2389634, by rfl⟩ : syracuseStep 3186179 = 4779269) B4779269
theorem B2124119 : Blo 2123435 2124119 := bstep (se 1 (by rfl) ⟨1593089, by rfl⟩ : syracuseStep 2124119 = 3186179) B3186179
theorem B4032517 : Blo 2123435 4032517 := bbase (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) (by norm_num)
theorem B5376689 : Blo 2123435 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B3584459 : Blo 2123435 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B2389639 : Blo 2123435 2389639 := bstep (se 1 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 2389639 = 3584459) B3584459
theorem B3186185 : Blo 2123435 3186185 := bstep (se 2 (by rfl) ⟨1194819, by rfl⟩ : syracuseStep 3186185 = 2389639) B2389639
theorem B2124123 : Blo 2123435 2124123 := bstep (se 1 (by rfl) ⟨1593092, by rfl⟩ : syracuseStep 2124123 = 3186185) B3186185
theorem B10753397 : Blo 2123435 10753397 := bbase (se 5 (by rfl) ⟨504065, by rfl⟩ : syracuseStep 10753397 = 1008131) (by norm_num)
theorem B7168931 : Blo 2123435 7168931 := bstep (se 1 (by rfl) ⟨5376698, by rfl⟩ : syracuseStep 7168931 = 10753397) B10753397
theorem B4779287 : Blo 2123435 4779287 := bstep (se 1 (by rfl) ⟨3584465, by rfl⟩ : syracuseStep 4779287 = 7168931) B7168931
theorem B3186191 : Blo 2123435 3186191 := bstep (se 1 (by rfl) ⟨2389643, by rfl⟩ : syracuseStep 3186191 = 4779287) B4779287
theorem B2124127 : Blo 2123435 2124127 := bstep (se 1 (by rfl) ⟨1593095, by rfl⟩ : syracuseStep 2124127 = 3186191) B3186191
theorem B3186197 : Blo 2123435 3186197 := bbase (se 6 (by rfl) ⟨74676, by rfl⟩ : syracuseStep 3186197 = 149353) (by norm_num)
theorem B2124131 : Blo 2123435 2124131 := bstep (se 1 (by rfl) ⟨1593098, by rfl⟩ : syracuseStep 2124131 = 3186197) B3186197
theorem B3879989 : Blo 2123435 3879989 := bbase (se 5 (by rfl) ⟨181874, by rfl⟩ : syracuseStep 3879989 = 363749) (by norm_num)
theorem B2586659 : Blo 2123435 2586659 := bstep (se 1 (by rfl) ⟨1939994, by rfl⟩ : syracuseStep 2586659 = 3879989) B3879989
theorem B6897757 : Blo 2123435 6897757 := bstep (se 3 (by rfl) ⟨1293329, by rfl⟩ : syracuseStep 6897757 = 2586659) B2586659
theorem B9197009 : Blo 2123435 9197009 := bstep (se 2 (by rfl) ⟨3448878, by rfl⟩ : syracuseStep 9197009 = 6897757) B6897757
theorem B6131339 : Blo 2123435 6131339 := bstep (se 1 (by rfl) ⟨4598504, by rfl⟩ : syracuseStep 6131339 = 9197009) B9197009
theorem B4087559 : Blo 2123435 4087559 := bstep (se 1 (by rfl) ⟨3065669, by rfl⟩ : syracuseStep 4087559 = 6131339) B6131339
theorem B2725039 : Blo 2123435 2725039 := bstep (se 1 (by rfl) ⟨2043779, by rfl⟩ : syracuseStep 2725039 = 4087559) B4087559
theorem B3633385 : Blo 2123435 3633385 := bstep (se 2 (by rfl) ⟨1362519, by rfl⟩ : syracuseStep 3633385 = 2725039) B2725039
theorem B4844513 : Blo 2123435 4844513 := bstep (se 2 (by rfl) ⟨1816692, by rfl⟩ : syracuseStep 4844513 = 3633385) B3633385
theorem B3229675 : Blo 2123435 3229675 := bstep (se 1 (by rfl) ⟨2422256, by rfl⟩ : syracuseStep 3229675 = 4844513) B4844513
theorem B17224933 : Blo 2123435 17224933 := bstep (se 4 (by rfl) ⟨1614837, by rfl⟩ : syracuseStep 17224933 = 3229675) B3229675
theorem B22966577 : Blo 2123435 22966577 := bstep (se 2 (by rfl) ⟨8612466, by rfl⟩ : syracuseStep 22966577 = 17224933) B17224933
theorem B15311051 : Blo 2123435 15311051 := bstep (se 1 (by rfl) ⟨11483288, by rfl⟩ : syracuseStep 15311051 = 22966577) B22966577
theorem B10207367 : Blo 2123435 10207367 := bstep (se 1 (by rfl) ⟨7655525, by rfl⟩ : syracuseStep 10207367 = 15311051) B15311051
theorem B6804911 : Blo 2123435 6804911 := bstep (se 1 (by rfl) ⟨5103683, by rfl⟩ : syracuseStep 6804911 = 10207367) B10207367
theorem B18146429 : Blo 2123435 18146429 := bstep (se 3 (by rfl) ⟨3402455, by rfl⟩ : syracuseStep 18146429 = 6804911) B6804911
theorem B12097619 : Blo 2123435 12097619 := bstep (se 1 (by rfl) ⟨9073214, by rfl⟩ : syracuseStep 12097619 = 18146429) B18146429
theorem B8065079 : Blo 2123435 8065079 := bstep (se 1 (by rfl) ⟨6048809, by rfl⟩ : syracuseStep 8065079 = 12097619) B12097619
theorem B5376719 : Blo 2123435 5376719 := bstep (se 1 (by rfl) ⟨4032539, by rfl⟩ : syracuseStep 5376719 = 8065079) B8065079
theorem B3584479 : Blo 2123435 3584479 := bstep (se 1 (by rfl) ⟨2688359, by rfl⟩ : syracuseStep 3584479 = 5376719) B5376719
theorem B4779305 : Blo 2123435 4779305 := bstep (se 2 (by rfl) ⟨1792239, by rfl⟩ : syracuseStep 4779305 = 3584479) B3584479
theorem B3186203 : Blo 2123435 3186203 := bstep (se 1 (by rfl) ⟨2389652, by rfl⟩ : syracuseStep 3186203 = 4779305) B4779305
theorem B2124135 : Blo 2123435 2124135 := bstep (se 1 (by rfl) ⟨1593101, by rfl⟩ : syracuseStep 2124135 = 3186203) B3186203
theorem B2389657 : Blo 2123435 2389657 := bbase (se 2 (by rfl) ⟨896121, by rfl⟩ : syracuseStep 2389657 = 1792243) (by norm_num)
theorem B3186209 : Blo 2123435 3186209 := bstep (se 2 (by rfl) ⟨1194828, by rfl⟩ : syracuseStep 3186209 = 2389657) B2389657
theorem B2124139 : Blo 2123435 2124139 := bstep (se 1 (by rfl) ⟨1593104, by rfl⟩ : syracuseStep 2124139 = 3186209) B3186209
theorem B8065109 : Blo 2123435 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B5376739 : Blo 2123435 5376739 := bstep (se 1 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 5376739 = 8065109) B8065109
theorem B7168985 : Blo 2123435 7168985 := bstep (se 2 (by rfl) ⟨2688369, by rfl⟩ : syracuseStep 7168985 = 5376739) B5376739
theorem B4779323 : Blo 2123435 4779323 := bstep (se 1 (by rfl) ⟨3584492, by rfl⟩ : syracuseStep 4779323 = 7168985) B7168985
theorem B3186215 : Blo 2123435 3186215 := bstep (se 1 (by rfl) ⟨2389661, by rfl⟩ : syracuseStep 3186215 = 4779323) B4779323
theorem B2124143 : Blo 2123435 2124143 := bstep (se 1 (by rfl) ⟨1593107, by rfl⟩ : syracuseStep 2124143 = 3186215) B3186215
theorem B3186221 : Blo 2123435 3186221 := bbase (se 3 (by rfl) ⟨597416, by rfl⟩ : syracuseStep 3186221 = 1194833) (by norm_num)
theorem B2124147 : Blo 2123435 2124147 := bstep (se 1 (by rfl) ⟨1593110, by rfl⟩ : syracuseStep 2124147 = 3186221) B3186221
theorem B4779341 : Blo 2123435 4779341 := bbase (se 3 (by rfl) ⟨896126, by rfl⟩ : syracuseStep 4779341 = 1792253) (by norm_num)
theorem B3186227 : Blo 2123435 3186227 := bstep (se 1 (by rfl) ⟨2389670, by rfl⟩ : syracuseStep 3186227 = 4779341) B4779341
theorem B2124151 : Blo 2123435 2124151 := bstep (se 1 (by rfl) ⟨1593113, by rfl⟩ : syracuseStep 2124151 = 3186227) B3186227
theorem B2688385 : Blo 2123435 2688385 := bbase (se 2 (by rfl) ⟨1008144, by rfl⟩ : syracuseStep 2688385 = 2016289) (by norm_num)
theorem B3584513 : Blo 2123435 3584513 := bstep (se 2 (by rfl) ⟨1344192, by rfl⟩ : syracuseStep 3584513 = 2688385) B2688385
theorem B2389675 : Blo 2123435 2389675 := bstep (se 1 (by rfl) ⟨1792256, by rfl⟩ : syracuseStep 2389675 = 3584513) B3584513
theorem B3186233 : Blo 2123435 3186233 := bstep (se 2 (by rfl) ⟨1194837, by rfl⟩ : syracuseStep 3186233 = 2389675) B2389675
theorem B2124155 : Blo 2123435 2124155 := bstep (se 1 (by rfl) ⟨1593116, by rfl⟩ : syracuseStep 2124155 = 3186233) B3186233
theorem B2268329 : Blo 2123435 2268329 := bbase (se 2 (by rfl) ⟨850623, by rfl⟩ : syracuseStep 2268329 = 1701247) (by norm_num)
theorem B24195509 : Blo 2123435 24195509 := bstep (se 5 (by rfl) ⟨1134164, by rfl⟩ : syracuseStep 24195509 = 2268329) B2268329
theorem B16130339 : Blo 2123435 16130339 := bstep (se 1 (by rfl) ⟨12097754, by rfl⟩ : syracuseStep 16130339 = 24195509) B24195509
theorem B10753559 : Blo 2123435 10753559 := bstep (se 1 (by rfl) ⟨8065169, by rfl⟩ : syracuseStep 10753559 = 16130339) B16130339
theorem B7169039 : Blo 2123435 7169039 := bstep (se 1 (by rfl) ⟨5376779, by rfl⟩ : syracuseStep 7169039 = 10753559) B10753559
theorem B4779359 : Blo 2123435 4779359 := bstep (se 1 (by rfl) ⟨3584519, by rfl⟩ : syracuseStep 4779359 = 7169039) B7169039
theorem B3186239 : Blo 2123435 3186239 := bstep (se 1 (by rfl) ⟨2389679, by rfl⟩ : syracuseStep 3186239 = 4779359) B4779359
theorem B2124159 : Blo 2123435 2124159 := bstep (se 1 (by rfl) ⟨1593119, by rfl⟩ : syracuseStep 2124159 = 3186239) B3186239
theorem B3186245 : Blo 2123435 3186245 := bbase (se 4 (by rfl) ⟨298710, by rfl⟩ : syracuseStep 3186245 = 597421) (by norm_num)
theorem B2124163 : Blo 2123435 2124163 := bstep (se 1 (by rfl) ⟨1593122, by rfl⟩ : syracuseStep 2124163 = 3186245) B3186245
theorem B3584533 : Blo 2123435 3584533 := bbase (se 6 (by rfl) ⟨84012, by rfl⟩ : syracuseStep 3584533 = 168025) (by norm_num)
theorem B4779377 : Blo 2123435 4779377 := bstep (se 2 (by rfl) ⟨1792266, by rfl⟩ : syracuseStep 4779377 = 3584533) B3584533
theorem B3186251 : Blo 2123435 3186251 := bstep (se 1 (by rfl) ⟨2389688, by rfl⟩ : syracuseStep 3186251 = 4779377) B4779377
theorem B2124167 : Blo 2123435 2124167 := bstep (se 1 (by rfl) ⟨1593125, by rfl⟩ : syracuseStep 2124167 = 3186251) B3186251
theorem B2389693 : Blo 2123435 2389693 := bbase (se 3 (by rfl) ⟨448067, by rfl⟩ : syracuseStep 2389693 = 896135) (by norm_num)
theorem B3186257 : Blo 2123435 3186257 := bstep (se 2 (by rfl) ⟨1194846, by rfl⟩ : syracuseStep 3186257 = 2389693) B2389693
theorem B2124171 : Blo 2123435 2124171 := bstep (se 1 (by rfl) ⟨1593128, by rfl⟩ : syracuseStep 2124171 = 3186257) B3186257
theorem B7169093 : Blo 2123435 7169093 := bbase (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) (by norm_num)
theorem B4779395 : Blo 2123435 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B3186263 : Blo 2123435 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B2124175 : Blo 2123435 2124175 := bstep (se 1 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 2124175 = 3186263) B3186263
theorem B3186269 : Blo 2123435 3186269 := bbase (se 3 (by rfl) ⟨597425, by rfl⟩ : syracuseStep 3186269 = 1194851) (by norm_num)
theorem B2124179 : Blo 2123435 2124179 := bstep (se 1 (by rfl) ⟨1593134, by rfl⟩ : syracuseStep 2124179 = 3186269) B3186269
theorem B4779413 : Blo 2123435 4779413 := bbase (se 6 (by rfl) ⟨112017, by rfl⟩ : syracuseStep 4779413 = 224035) (by norm_num)
theorem B3186275 : Blo 2123435 3186275 := bstep (se 1 (by rfl) ⟨2389706, by rfl⟩ : syracuseStep 3186275 = 4779413) B4779413
theorem B2124183 : Blo 2123435 2124183 := bstep (se 1 (by rfl) ⟨1593137, by rfl⟩ : syracuseStep 2124183 = 3186275) B3186275
theorem B2870893 : Blo 2123435 2870893 := bbase (se 3 (by rfl) ⟨538292, by rfl⟩ : syracuseStep 2870893 = 1076585) (by norm_num)
theorem B15311429 : Blo 2123435 15311429 := bstep (se 4 (by rfl) ⟨1435446, by rfl⟩ : syracuseStep 15311429 = 2870893) B2870893
theorem B10207619 : Blo 2123435 10207619 := bstep (se 1 (by rfl) ⟨7655714, by rfl⟩ : syracuseStep 10207619 = 15311429) B15311429
theorem B6805079 : Blo 2123435 6805079 := bstep (se 1 (by rfl) ⟨5103809, by rfl⟩ : syracuseStep 6805079 = 10207619) B10207619
theorem B4536719 : Blo 2123435 4536719 := bstep (se 1 (by rfl) ⟨3402539, by rfl⟩ : syracuseStep 4536719 = 6805079) B6805079
theorem B3024479 : Blo 2123435 3024479 := bstep (se 1 (by rfl) ⟨2268359, by rfl⟩ : syracuseStep 3024479 = 4536719) B4536719
theorem B8065277 : Blo 2123435 8065277 := bstep (se 3 (by rfl) ⟨1512239, by rfl⟩ : syracuseStep 8065277 = 3024479) B3024479
theorem B5376851 : Blo 2123435 5376851 := bstep (se 1 (by rfl) ⟨4032638, by rfl⟩ : syracuseStep 5376851 = 8065277) B8065277
theorem B3584567 : Blo 2123435 3584567 := bstep (se 1 (by rfl) ⟨2688425, by rfl⟩ : syracuseStep 3584567 = 5376851) B5376851
theorem B2389711 : Blo 2123435 2389711 := bstep (se 1 (by rfl) ⟨1792283, by rfl⟩ : syracuseStep 2389711 = 3584567) B3584567
theorem B3186281 : Blo 2123435 3186281 := bstep (se 2 (by rfl) ⟨1194855, by rfl⟩ : syracuseStep 3186281 = 2389711) B2389711
theorem B2124187 : Blo 2123435 2124187 := bstep (se 1 (by rfl) ⟨1593140, by rfl⟩ : syracuseStep 2124187 = 3186281) B3186281
theorem B2551909 : Blo 2123435 2551909 := bbase (se 4 (by rfl) ⟨239241, by rfl⟩ : syracuseStep 2551909 = 478483) (by norm_num)
theorem B3402545 : Blo 2123435 3402545 := bstep (se 2 (by rfl) ⟨1275954, by rfl⟩ : syracuseStep 3402545 = 2551909) B2551909
theorem B9073453 : Blo 2123435 9073453 := bstep (se 3 (by rfl) ⟨1701272, by rfl⟩ : syracuseStep 9073453 = 3402545) B3402545
theorem B12097937 : Blo 2123435 12097937 := bstep (se 2 (by rfl) ⟨4536726, by rfl⟩ : syracuseStep 12097937 = 9073453) B9073453
theorem B8065291 : Blo 2123435 8065291 := bstep (se 1 (by rfl) ⟨6048968, by rfl⟩ : syracuseStep 8065291 = 12097937) B12097937
theorem B10753721 : Blo 2123435 10753721 := bstep (se 2 (by rfl) ⟨4032645, by rfl⟩ : syracuseStep 10753721 = 8065291) B8065291
theorem B7169147 : Blo 2123435 7169147 := bstep (se 1 (by rfl) ⟨5376860, by rfl⟩ : syracuseStep 7169147 = 10753721) B10753721
theorem B4779431 : Blo 2123435 4779431 := bstep (se 1 (by rfl) ⟨3584573, by rfl⟩ : syracuseStep 4779431 = 7169147) B7169147
theorem B3186287 : Blo 2123435 3186287 := bstep (se 1 (by rfl) ⟨2389715, by rfl⟩ : syracuseStep 3186287 = 4779431) B4779431
theorem B2124191 : Blo 2123435 2124191 := bstep (se 1 (by rfl) ⟨1593143, by rfl⟩ : syracuseStep 2124191 = 3186287) B3186287
theorem B3186293 : Blo 2123435 3186293 := bbase (se 5 (by rfl) ⟨149357, by rfl⟩ : syracuseStep 3186293 = 298715) (by norm_num)
theorem B2124195 : Blo 2123435 2124195 := bstep (se 1 (by rfl) ⟨1593146, by rfl⟩ : syracuseStep 2124195 = 3186293) B3186293
theorem B4032661 : Blo 2123435 4032661 := bbase (se 6 (by rfl) ⟨94515, by rfl⟩ : syracuseStep 4032661 = 189031) (by norm_num)
theorem B5376881 : Blo 2123435 5376881 := bstep (se 2 (by rfl) ⟨2016330, by rfl⟩ : syracuseStep 5376881 = 4032661) B4032661
theorem B3584587 : Blo 2123435 3584587 := bstep (se 1 (by rfl) ⟨2688440, by rfl⟩ : syracuseStep 3584587 = 5376881) B5376881
theorem B4779449 : Blo 2123435 4779449 := bstep (se 2 (by rfl) ⟨1792293, by rfl⟩ : syracuseStep 4779449 = 3584587) B3584587
theorem B3186299 : Blo 2123435 3186299 := bstep (se 1 (by rfl) ⟨2389724, by rfl⟩ : syracuseStep 3186299 = 4779449) B4779449
theorem B2124199 : Blo 2123435 2124199 := bstep (se 1 (by rfl) ⟨1593149, by rfl⟩ : syracuseStep 2124199 = 3186299) B3186299
theorem B2389729 : Blo 2123435 2389729 := bbase (se 2 (by rfl) ⟨896148, by rfl⟩ : syracuseStep 2389729 = 1792297) (by norm_num)
theorem B3186305 : Blo 2123435 3186305 := bstep (se 2 (by rfl) ⟨1194864, by rfl⟩ : syracuseStep 3186305 = 2389729) B2389729
theorem B2124203 : Blo 2123435 2124203 := bstep (se 1 (by rfl) ⟨1593152, by rfl⟩ : syracuseStep 2124203 = 3186305) B3186305
theorem B5376901 : Blo 2123435 5376901 := bbase (se 4 (by rfl) ⟨504084, by rfl⟩ : syracuseStep 5376901 = 1008169) (by norm_num)
theorem B7169201 : Blo 2123435 7169201 := bstep (se 2 (by rfl) ⟨2688450, by rfl⟩ : syracuseStep 7169201 = 5376901) B5376901
theorem B4779467 : Blo 2123435 4779467 := bstep (se 1 (by rfl) ⟨3584600, by rfl⟩ : syracuseStep 4779467 = 7169201) B7169201
theorem B3186311 : Blo 2123435 3186311 := bstep (se 1 (by rfl) ⟨2389733, by rfl⟩ : syracuseStep 3186311 = 4779467) B4779467
theorem B2124207 : Blo 2123435 2124207 := bstep (se 1 (by rfl) ⟨1593155, by rfl⟩ : syracuseStep 2124207 = 3186311) B3186311
theorem B3186317 : Blo 2123435 3186317 := bbase (se 3 (by rfl) ⟨597434, by rfl⟩ : syracuseStep 3186317 = 1194869) (by norm_num)
theorem B2124211 : Blo 2123435 2124211 := bstep (se 1 (by rfl) ⟨1593158, by rfl⟩ : syracuseStep 2124211 = 3186317) B3186317
theorem B4779485 : Blo 2123435 4779485 := bbase (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) (by norm_num)
theorem B3186323 : Blo 2123435 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B2124215 : Blo 2123435 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B3584621 : Blo 2123435 3584621 := bbase (se 3 (by rfl) ⟨672116, by rfl⟩ : syracuseStep 3584621 = 1344233) (by norm_num)
theorem B2389747 : Blo 2123435 2389747 := bstep (se 1 (by rfl) ⟨1792310, by rfl⟩ : syracuseStep 2389747 = 3584621) B3584621
theorem B3186329 : Blo 2123435 3186329 := bstep (se 2 (by rfl) ⟨1194873, by rfl⟩ : syracuseStep 3186329 = 2389747) B2389747
theorem B2124219 : Blo 2123435 2124219 := bstep (se 1 (by rfl) ⟨1593164, by rfl⟩ : syracuseStep 2124219 = 3186329) B3186329
theorem B41388245 : Blo 2123435 41388245 := bbase (se 7 (by rfl) ⟨485018, by rfl⟩ : syracuseStep 41388245 = 970037) (by norm_num)
theorem B27592163 : Blo 2123435 27592163 := bstep (se 1 (by rfl) ⟨20694122, by rfl⟩ : syracuseStep 27592163 = 41388245) B41388245
theorem B18394775 : Blo 2123435 18394775 := bstep (se 1 (by rfl) ⟨13796081, by rfl⟩ : syracuseStep 18394775 = 27592163) B27592163
theorem B12263183 : Blo 2123435 12263183 := bstep (se 1 (by rfl) ⟨9197387, by rfl⟩ : syracuseStep 12263183 = 18394775) B18394775
theorem B8175455 : Blo 2123435 8175455 := bstep (se 1 (by rfl) ⟨6131591, by rfl⟩ : syracuseStep 8175455 = 12263183) B12263183
theorem B5450303 : Blo 2123435 5450303 := bstep (se 1 (by rfl) ⟨4087727, by rfl⟩ : syracuseStep 5450303 = 8175455) B8175455
theorem B3633535 : Blo 2123435 3633535 := bstep (se 1 (by rfl) ⟨2725151, by rfl⟩ : syracuseStep 3633535 = 5450303) B5450303
theorem B4844713 : Blo 2123435 4844713 := bstep (se 2 (by rfl) ⟨1816767, by rfl⟩ : syracuseStep 4844713 = 3633535) B3633535
theorem B6459617 : Blo 2123435 6459617 := bstep (se 2 (by rfl) ⟨2422356, by rfl⟩ : syracuseStep 6459617 = 4844713) B4844713
theorem B4306411 : Blo 2123435 4306411 := bstep (se 1 (by rfl) ⟨3229808, by rfl⟩ : syracuseStep 4306411 = 6459617) B6459617
theorem B22967525 : Blo 2123435 22967525 := bstep (se 4 (by rfl) ⟨2153205, by rfl⟩ : syracuseStep 22967525 = 4306411) B4306411
theorem B15311683 : Blo 2123435 15311683 := bstep (se 1 (by rfl) ⟨11483762, by rfl⟩ : syracuseStep 15311683 = 22967525) B22967525
theorem B20415577 : Blo 2123435 20415577 := bstep (se 2 (by rfl) ⟨7655841, by rfl⟩ : syracuseStep 20415577 = 15311683) B15311683
theorem B27220769 : Blo 2123435 27220769 := bstep (se 2 (by rfl) ⟨10207788, by rfl⟩ : syracuseStep 27220769 = 20415577) B20415577
theorem B18147179 : Blo 2123435 18147179 := bstep (se 1 (by rfl) ⟨13610384, by rfl⟩ : syracuseStep 18147179 = 27220769) B27220769
theorem B12098119 : Blo 2123435 12098119 := bstep (se 1 (by rfl) ⟨9073589, by rfl⟩ : syracuseStep 12098119 = 18147179) B18147179
theorem B16130825 : Blo 2123435 16130825 := bstep (se 2 (by rfl) ⟨6049059, by rfl⟩ : syracuseStep 16130825 = 12098119) B12098119
theorem B10753883 : Blo 2123435 10753883 := bstep (se 1 (by rfl) ⟨8065412, by rfl⟩ : syracuseStep 10753883 = 16130825) B16130825
theorem B7169255 : Blo 2123435 7169255 := bstep (se 1 (by rfl) ⟨5376941, by rfl⟩ : syracuseStep 7169255 = 10753883) B10753883
theorem B4779503 : Blo 2123435 4779503 := bstep (se 1 (by rfl) ⟨3584627, by rfl⟩ : syracuseStep 4779503 = 7169255) B7169255
theorem B3186335 : Blo 2123435 3186335 := bstep (se 1 (by rfl) ⟨2389751, by rfl⟩ : syracuseStep 3186335 = 4779503) B4779503
theorem B2124223 : Blo 2123435 2124223 := bstep (se 1 (by rfl) ⟨1593167, by rfl⟩ : syracuseStep 2124223 = 3186335) B3186335
theorem B3186341 : Blo 2123435 3186341 := bbase (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) (by norm_num)
theorem B2124227 : Blo 2123435 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B2688481 : Blo 2123435 2688481 := bbase (se 2 (by rfl) ⟨1008180, by rfl⟩ : syracuseStep 2688481 = 2016361) (by norm_num)
theorem B3584641 : Blo 2123435 3584641 := bstep (se 2 (by rfl) ⟨1344240, by rfl⟩ : syracuseStep 3584641 = 2688481) B2688481
theorem B4779521 : Blo 2123435 4779521 := bstep (se 2 (by rfl) ⟨1792320, by rfl⟩ : syracuseStep 4779521 = 3584641) B3584641
theorem B3186347 : Blo 2123435 3186347 := bstep (se 1 (by rfl) ⟨2389760, by rfl⟩ : syracuseStep 3186347 = 4779521) B4779521
theorem B2124231 : Blo 2123435 2124231 := bstep (se 1 (by rfl) ⟨1593173, by rfl⟩ : syracuseStep 2124231 = 3186347) B3186347
theorem B2389765 : Blo 2123435 2389765 := bbase (se 4 (by rfl) ⟨224040, by rfl⟩ : syracuseStep 2389765 = 448081) (by norm_num)
theorem B3186353 : Blo 2123435 3186353 := bstep (se 2 (by rfl) ⟨1194882, by rfl⟩ : syracuseStep 3186353 = 2389765) B2389765
theorem B2124235 : Blo 2123435 2124235 := bstep (se 1 (by rfl) ⟨1593176, by rfl⟩ : syracuseStep 2124235 = 3186353) B3186353
theorem B41388565 : Blo 2123435 41388565 := bbase (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) (by norm_num)
theorem B55184753 : Blo 2123435 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B36789835 : Blo 2123435 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B49053113 : Blo 2123435 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B32702075 : Blo 2123435 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B21801383 : Blo 2123435 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B14534255 : Blo 2123435 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B38758013 : Blo 2123435 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B25838675 : Blo 2123435 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B17225783 : Blo 2123435 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B11483855 : Blo 2123435 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B7655903 : Blo 2123435 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B5103935 : Blo 2123435 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B3402623 : Blo 2123435 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B2268415 : Blo 2123435 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B3024553 : Blo 2123435 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B4032737 : Blo 2123435 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B2688491 : Blo 2123435 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B7169309 : Blo 2123435 7169309 := bstep (se 3 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 7169309 = 2688491) B2688491
theorem B4779539 : Blo 2123435 4779539 := bstep (se 1 (by rfl) ⟨3584654, by rfl⟩ : syracuseStep 4779539 = 7169309) B7169309
theorem B3186359 : Blo 2123435 3186359 := bstep (se 1 (by rfl) ⟨2389769, by rfl⟩ : syracuseStep 3186359 = 4779539) B4779539
theorem B2124239 : Blo 2123435 2124239 := bstep (se 1 (by rfl) ⟨1593179, by rfl⟩ : syracuseStep 2124239 = 3186359) B3186359
theorem B3186365 : Blo 2123435 3186365 := bbase (se 3 (by rfl) ⟨597443, by rfl⟩ : syracuseStep 3186365 = 1194887) (by norm_num)
theorem B2124243 : Blo 2123435 2124243 := bstep (se 1 (by rfl) ⟨1593182, by rfl⟩ : syracuseStep 2124243 = 3186365) B3186365
theorem B4779557 : Blo 2123435 4779557 := bbase (se 4 (by rfl) ⟨448083, by rfl⟩ : syracuseStep 4779557 = 896167) (by norm_num)
theorem B3186371 : Blo 2123435 3186371 := bstep (se 1 (by rfl) ⟨2389778, by rfl⟩ : syracuseStep 3186371 = 4779557) B4779557
theorem B2124247 : Blo 2123435 2124247 := bstep (se 1 (by rfl) ⟨1593185, by rfl⟩ : syracuseStep 2124247 = 3186371) B3186371
theorem B5377013 : Blo 2123435 5377013 := bbase (se 5 (by rfl) ⟨252047, by rfl⟩ : syracuseStep 5377013 = 504095) (by norm_num)
theorem B3584675 : Blo 2123435 3584675 := bstep (se 1 (by rfl) ⟨2688506, by rfl⟩ : syracuseStep 3584675 = 5377013) B5377013
theorem B2389783 : Blo 2123435 2389783 := bstep (se 1 (by rfl) ⟨1792337, by rfl⟩ : syracuseStep 2389783 = 3584675) B3584675
theorem B3186377 : Blo 2123435 3186377 := bstep (se 2 (by rfl) ⟨1194891, by rfl⟩ : syracuseStep 3186377 = 2389783) B2389783
theorem B2124251 : Blo 2123435 2124251 := bstep (se 1 (by rfl) ⟨1593188, by rfl⟩ : syracuseStep 2124251 = 3186377) B3186377
theorem B2422393 : Blo 2123435 2422393 := bbase (se 2 (by rfl) ⟨908397, by rfl⟩ : syracuseStep 2422393 = 1816795) (by norm_num)
theorem B12919429 : Blo 2123435 12919429 := bstep (se 4 (by rfl) ⟨1211196, by rfl⟩ : syracuseStep 12919429 = 2422393) B2422393
theorem B68903621 : Blo 2123435 68903621 := bstep (se 4 (by rfl) ⟨6459714, by rfl⟩ : syracuseStep 68903621 = 12919429) B12919429
theorem B45935747 : Blo 2123435 45935747 := bstep (se 1 (by rfl) ⟨34451810, by rfl⟩ : syracuseStep 45935747 = 68903621) B68903621
theorem B30623831 : Blo 2123435 30623831 := bstep (se 1 (by rfl) ⟨22967873, by rfl⟩ : syracuseStep 30623831 = 45935747) B45935747
theorem B20415887 : Blo 2123435 20415887 := bstep (se 1 (by rfl) ⟨15311915, by rfl⟩ : syracuseStep 20415887 = 30623831) B30623831
theorem B13610591 : Blo 2123435 13610591 := bstep (se 1 (by rfl) ⟨10207943, by rfl⟩ : syracuseStep 13610591 = 20415887) B20415887
theorem B9073727 : Blo 2123435 9073727 := bstep (se 1 (by rfl) ⟨6805295, by rfl⟩ : syracuseStep 9073727 = 13610591) B13610591
theorem B6049151 : Blo 2123435 6049151 := bstep (se 1 (by rfl) ⟨4536863, by rfl⟩ : syracuseStep 6049151 = 9073727) B9073727
theorem B4032767 : Blo 2123435 4032767 := bstep (se 1 (by rfl) ⟨3024575, by rfl⟩ : syracuseStep 4032767 = 6049151) B6049151
theorem B10754045 : Blo 2123435 10754045 := bstep (se 3 (by rfl) ⟨2016383, by rfl⟩ : syracuseStep 10754045 = 4032767) B4032767
theorem B7169363 : Blo 2123435 7169363 := bstep (se 1 (by rfl) ⟨5377022, by rfl⟩ : syracuseStep 7169363 = 10754045) B10754045
theorem B4779575 : Blo 2123435 4779575 := bstep (se 1 (by rfl) ⟨3584681, by rfl⟩ : syracuseStep 4779575 = 7169363) B7169363
theorem B3186383 : Blo 2123435 3186383 := bstep (se 1 (by rfl) ⟨2389787, by rfl⟩ : syracuseStep 3186383 = 4779575) B4779575
theorem B2124255 : Blo 2123435 2124255 := bstep (se 1 (by rfl) ⟨1593191, by rfl⟩ : syracuseStep 2124255 = 3186383) B3186383
theorem B3186389 : Blo 2123435 3186389 := bbase (se 7 (by rfl) ⟨37340, by rfl⟩ : syracuseStep 3186389 = 74681) (by norm_num)
theorem B2124259 : Blo 2123435 2124259 := bstep (se 1 (by rfl) ⟨1593194, by rfl⟩ : syracuseStep 2124259 = 3186389) B3186389
theorem B3402661 : Blo 2123435 3402661 := bbase (se 4 (by rfl) ⟨318999, by rfl⟩ : syracuseStep 3402661 = 637999) (by norm_num)
theorem B4536881 : Blo 2123435 4536881 := bstep (se 2 (by rfl) ⟨1701330, by rfl⟩ : syracuseStep 4536881 = 3402661) B3402661
theorem B3024587 : Blo 2123435 3024587 := bstep (se 1 (by rfl) ⟨2268440, by rfl⟩ : syracuseStep 3024587 = 4536881) B4536881
theorem B8065565 : Blo 2123435 8065565 := bstep (se 3 (by rfl) ⟨1512293, by rfl⟩ : syracuseStep 8065565 = 3024587) B3024587
theorem B5377043 : Blo 2123435 5377043 := bstep (se 1 (by rfl) ⟨4032782, by rfl⟩ : syracuseStep 5377043 = 8065565) B8065565
theorem B3584695 : Blo 2123435 3584695 := bstep (se 1 (by rfl) ⟨2688521, by rfl⟩ : syracuseStep 3584695 = 5377043) B5377043
theorem B4779593 : Blo 2123435 4779593 := bstep (se 2 (by rfl) ⟨1792347, by rfl⟩ : syracuseStep 4779593 = 3584695) B3584695
theorem B3186395 : Blo 2123435 3186395 := bstep (se 1 (by rfl) ⟨2389796, by rfl⟩ : syracuseStep 3186395 = 4779593) B4779593
theorem B2124263 : Blo 2123435 2124263 := bstep (se 1 (by rfl) ⟨1593197, by rfl⟩ : syracuseStep 2124263 = 3186395) B3186395
theorem B2389801 : Blo 2123435 2389801 := bbase (se 2 (by rfl) ⟨896175, by rfl⟩ : syracuseStep 2389801 = 1792351) (by norm_num)
theorem B3186401 : Blo 2123435 3186401 := bstep (se 2 (by rfl) ⟨1194900, by rfl⟩ : syracuseStep 3186401 = 2389801) B2389801
theorem B2124267 : Blo 2123435 2124267 := bstep (se 1 (by rfl) ⟨1593200, by rfl⟩ : syracuseStep 2124267 = 3186401) B3186401
theorem B2552005 : Blo 2123435 2552005 := bbase (se 4 (by rfl) ⟨239250, by rfl⟩ : syracuseStep 2552005 = 478501) (by norm_num)
theorem B13610693 : Blo 2123435 13610693 := bstep (se 4 (by rfl) ⟨1276002, by rfl⟩ : syracuseStep 13610693 = 2552005) B2552005
theorem B9073795 : Blo 2123435 9073795 := bstep (se 1 (by rfl) ⟨6805346, by rfl⟩ : syracuseStep 9073795 = 13610693) B13610693
theorem B12098393 : Blo 2123435 12098393 := bstep (se 2 (by rfl) ⟨4536897, by rfl⟩ : syracuseStep 12098393 = 9073795) B9073795
theorem B8065595 : Blo 2123435 8065595 := bstep (se 1 (by rfl) ⟨6049196, by rfl⟩ : syracuseStep 8065595 = 12098393) B12098393
theorem B5377063 : Blo 2123435 5377063 := bstep (se 1 (by rfl) ⟨4032797, by rfl⟩ : syracuseStep 5377063 = 8065595) B8065595
theorem B7169417 : Blo 2123435 7169417 := bstep (se 2 (by rfl) ⟨2688531, by rfl⟩ : syracuseStep 7169417 = 5377063) B5377063
theorem B4779611 : Blo 2123435 4779611 := bstep (se 1 (by rfl) ⟨3584708, by rfl⟩ : syracuseStep 4779611 = 7169417) B7169417
theorem B3186407 : Blo 2123435 3186407 := bstep (se 1 (by rfl) ⟨2389805, by rfl⟩ : syracuseStep 3186407 = 4779611) B4779611
theorem B2124271 : Blo 2123435 2124271 := bstep (se 1 (by rfl) ⟨1593203, by rfl⟩ : syracuseStep 2124271 = 3186407) B3186407
theorem B3186413 : Blo 2123435 3186413 := bbase (se 3 (by rfl) ⟨597452, by rfl⟩ : syracuseStep 3186413 = 1194905) (by norm_num)
theorem B2124275 : Blo 2123435 2124275 := bstep (se 1 (by rfl) ⟨1593206, by rfl⟩ : syracuseStep 2124275 = 3186413) B3186413
theorem B4779629 : Blo 2123435 4779629 := bbase (se 3 (by rfl) ⟨896180, by rfl⟩ : syracuseStep 4779629 = 1792361) (by norm_num)
theorem B3186419 : Blo 2123435 3186419 := bstep (se 1 (by rfl) ⟨2389814, by rfl⟩ : syracuseStep 3186419 = 4779629) B4779629
theorem B2124279 : Blo 2123435 2124279 := bstep (se 1 (by rfl) ⟨1593209, by rfl⟩ : syracuseStep 2124279 = 3186419) B3186419
theorem B4032821 : Blo 2123435 4032821 := bbase (se 5 (by rfl) ⟨189038, by rfl⟩ : syracuseStep 4032821 = 378077) (by norm_num)
theorem B2688547 : Blo 2123435 2688547 := bstep (se 1 (by rfl) ⟨2016410, by rfl⟩ : syracuseStep 2688547 = 4032821) B4032821
theorem B3584729 : Blo 2123435 3584729 := bstep (se 2 (by rfl) ⟨1344273, by rfl⟩ : syracuseStep 3584729 = 2688547) B2688547
theorem B2389819 : Blo 2123435 2389819 := bstep (se 1 (by rfl) ⟨1792364, by rfl⟩ : syracuseStep 2389819 = 3584729) B3584729
theorem B3186425 : Blo 2123435 3186425 := bstep (se 2 (by rfl) ⟨1194909, by rfl⟩ : syracuseStep 3186425 = 2389819) B2389819
theorem B2124283 : Blo 2123435 2124283 := bstep (se 1 (by rfl) ⟨1593212, by rfl⟩ : syracuseStep 2124283 = 3186425) B3186425
theorem B13095893 : Blo 2123435 13095893 := bbase (se 7 (by rfl) ⟨153467, by rfl⟩ : syracuseStep 13095893 = 306935) (by norm_num)
theorem B8730595 : Blo 2123435 8730595 := bstep (se 1 (by rfl) ⟨6547946, by rfl⟩ : syracuseStep 8730595 = 13095893) B13095893
theorem B11640793 : Blo 2123435 11640793 := bstep (se 2 (by rfl) ⟨4365297, by rfl⟩ : syracuseStep 11640793 = 8730595) B8730595
theorem B15521057 : Blo 2123435 15521057 := bstep (se 2 (by rfl) ⟨5820396, by rfl⟩ : syracuseStep 15521057 = 11640793) B11640793
theorem B10347371 : Blo 2123435 10347371 := bstep (se 1 (by rfl) ⟨7760528, by rfl⟩ : syracuseStep 10347371 = 15521057) B15521057
theorem B6898247 : Blo 2123435 6898247 := bstep (se 1 (by rfl) ⟨5173685, by rfl⟩ : syracuseStep 6898247 = 10347371) B10347371
theorem B4598831 : Blo 2123435 4598831 := bstep (se 1 (by rfl) ⟨3449123, by rfl⟩ : syracuseStep 4598831 = 6898247) B6898247
theorem B3065887 : Blo 2123435 3065887 := bstep (se 1 (by rfl) ⟨2299415, by rfl⟩ : syracuseStep 3065887 = 4598831) B4598831
theorem B4087849 : Blo 2123435 4087849 := bstep (se 2 (by rfl) ⟨1532943, by rfl⟩ : syracuseStep 4087849 = 3065887) B3065887
theorem B87207445 : Blo 2123435 87207445 := bstep (se 6 (by rfl) ⟨2043924, by rfl⟩ : syracuseStep 87207445 = 4087849) B4087849
theorem B465106373 : Blo 2123435 465106373 := bstep (se 4 (by rfl) ⟨43603722, by rfl⟩ : syracuseStep 465106373 = 87207445) B87207445
theorem B310070915 : Blo 2123435 310070915 := bstep (se 1 (by rfl) ⟨232553186, by rfl⟩ : syracuseStep 310070915 = 465106373) B465106373
theorem B206713943 : Blo 2123435 206713943 := bstep (se 1 (by rfl) ⟨155035457, by rfl⟩ : syracuseStep 206713943 = 310070915) B310070915
theorem B137809295 : Blo 2123435 137809295 := bstep (se 1 (by rfl) ⟨103356971, by rfl⟩ : syracuseStep 137809295 = 206713943) B206713943
theorem B91872863 : Blo 2123435 91872863 := bstep (se 1 (by rfl) ⟨68904647, by rfl⟩ : syracuseStep 91872863 = 137809295) B137809295
theorem B61248575 : Blo 2123435 61248575 := bstep (se 1 (by rfl) ⟨45936431, by rfl⟩ : syracuseStep 61248575 = 91872863) B91872863
theorem B40832383 : Blo 2123435 40832383 := bstep (se 1 (by rfl) ⟨30624287, by rfl⟩ : syracuseStep 40832383 = 61248575) B61248575
theorem B54443177 : Blo 2123435 54443177 := bstep (se 2 (by rfl) ⟨20416191, by rfl⟩ : syracuseStep 54443177 = 40832383) B40832383
theorem B36295451 : Blo 2123435 36295451 := bstep (se 1 (by rfl) ⟨27221588, by rfl⟩ : syracuseStep 36295451 = 54443177) B54443177
theorem B24196967 : Blo 2123435 24196967 := bstep (se 1 (by rfl) ⟨18147725, by rfl⟩ : syracuseStep 24196967 = 36295451) B36295451
theorem B16131311 : Blo 2123435 16131311 := bstep (se 1 (by rfl) ⟨12098483, by rfl⟩ : syracuseStep 16131311 = 24196967) B24196967
theorem B10754207 : Blo 2123435 10754207 := bstep (se 1 (by rfl) ⟨8065655, by rfl⟩ : syracuseStep 10754207 = 16131311) B16131311
theorem B7169471 : Blo 2123435 7169471 := bstep (se 1 (by rfl) ⟨5377103, by rfl⟩ : syracuseStep 7169471 = 10754207) B10754207
theorem B4779647 : Blo 2123435 4779647 := bstep (se 1 (by rfl) ⟨3584735, by rfl⟩ : syracuseStep 4779647 = 7169471) B7169471
theorem B3186431 : Blo 2123435 3186431 := bstep (se 1 (by rfl) ⟨2389823, by rfl⟩ : syracuseStep 3186431 = 4779647) B4779647
theorem B2124287 : Blo 2123435 2124287 := bstep (se 1 (by rfl) ⟨1593215, by rfl⟩ : syracuseStep 2124287 = 3186431) B3186431
theorem B3186437 : Blo 2123435 3186437 := bbase (se 4 (by rfl) ⟨298728, by rfl⟩ : syracuseStep 3186437 = 597457) (by norm_num)
theorem B2124291 : Blo 2123435 2124291 := bstep (se 1 (by rfl) ⟨1593218, by rfl⟩ : syracuseStep 2124291 = 3186437) B3186437
theorem B3584749 : Blo 2123435 3584749 := bbase (se 3 (by rfl) ⟨672140, by rfl⟩ : syracuseStep 3584749 = 1344281) (by norm_num)
theorem B4779665 : Blo 2123435 4779665 := bstep (se 2 (by rfl) ⟨1792374, by rfl⟩ : syracuseStep 4779665 = 3584749) B3584749
theorem B3186443 : Blo 2123435 3186443 := bstep (se 1 (by rfl) ⟨2389832, by rfl⟩ : syracuseStep 3186443 = 4779665) B4779665
theorem B2124295 : Blo 2123435 2124295 := bstep (se 1 (by rfl) ⟨1593221, by rfl⟩ : syracuseStep 2124295 = 3186443) B3186443
theorem B2389837 : Blo 2123435 2389837 := bbase (se 3 (by rfl) ⟨448094, by rfl⟩ : syracuseStep 2389837 = 896189) (by norm_num)
theorem B3186449 : Blo 2123435 3186449 := bstep (se 2 (by rfl) ⟨1194918, by rfl⟩ : syracuseStep 3186449 = 2389837) B2389837
theorem B2124299 : Blo 2123435 2124299 := bstep (se 1 (by rfl) ⟨1593224, by rfl⟩ : syracuseStep 2124299 = 3186449) B3186449
theorem B7169525 : Blo 2123435 7169525 := bbase (se 5 (by rfl) ⟨336071, by rfl⟩ : syracuseStep 7169525 = 672143) (by norm_num)
theorem B4779683 : Blo 2123435 4779683 := bstep (se 1 (by rfl) ⟨3584762, by rfl⟩ : syracuseStep 4779683 = 7169525) B7169525
theorem B3186455 : Blo 2123435 3186455 := bstep (se 1 (by rfl) ⟨2389841, by rfl⟩ : syracuseStep 3186455 = 4779683) B4779683
theorem B2124303 : Blo 2123435 2124303 := bstep (se 1 (by rfl) ⟨1593227, by rfl⟩ : syracuseStep 2124303 = 3186455) B3186455
theorem B3186461 : Blo 2123435 3186461 := bbase (se 3 (by rfl) ⟨597461, by rfl⟩ : syracuseStep 3186461 = 1194923) (by norm_num)
theorem B2124307 : Blo 2123435 2124307 := bstep (se 1 (by rfl) ⟨1593230, by rfl⟩ : syracuseStep 2124307 = 3186461) B3186461
theorem B4779701 : Blo 2123435 4779701 := bbase (se 5 (by rfl) ⟨224048, by rfl⟩ : syracuseStep 4779701 = 448097) (by norm_num)
theorem B3186467 : Blo 2123435 3186467 := bstep (se 1 (by rfl) ⟨2389850, by rfl⟩ : syracuseStep 3186467 = 4779701) B4779701
theorem B2124311 : Blo 2123435 2124311 := bstep (se 1 (by rfl) ⟨1593233, by rfl⟩ : syracuseStep 2124311 = 3186467) B3186467
theorem B12098645 : Blo 2123435 12098645 := bbase (se 8 (by rfl) ⟨70890, by rfl⟩ : syracuseStep 12098645 = 141781) (by norm_num)
theorem B8065763 : Blo 2123435 8065763 := bstep (se 1 (by rfl) ⟨6049322, by rfl⟩ : syracuseStep 8065763 = 12098645) B12098645
theorem B5377175 : Blo 2123435 5377175 := bstep (se 1 (by rfl) ⟨4032881, by rfl⟩ : syracuseStep 5377175 = 8065763) B8065763
theorem B3584783 : Blo 2123435 3584783 := bstep (se 1 (by rfl) ⟨2688587, by rfl⟩ : syracuseStep 3584783 = 5377175) B5377175
theorem B2389855 : Blo 2123435 2389855 := bstep (se 1 (by rfl) ⟨1792391, by rfl⟩ : syracuseStep 2389855 = 3584783) B3584783
theorem B3186473 : Blo 2123435 3186473 := bstep (se 2 (by rfl) ⟨1194927, by rfl⟩ : syracuseStep 3186473 = 2389855) B2389855
theorem B2124315 : Blo 2123435 2124315 := bstep (se 1 (by rfl) ⟨1593236, by rfl⟩ : syracuseStep 2124315 = 3186473) B3186473
theorem B6049333 : Blo 2123435 6049333 := bbase (se 5 (by rfl) ⟨283562, by rfl⟩ : syracuseStep 6049333 = 567125) (by norm_num)
theorem B8065777 : Blo 2123435 8065777 := bstep (se 2 (by rfl) ⟨3024666, by rfl⟩ : syracuseStep 8065777 = 6049333) B6049333
theorem B10754369 : Blo 2123435 10754369 := bstep (se 2 (by rfl) ⟨4032888, by rfl⟩ : syracuseStep 10754369 = 8065777) B8065777
theorem B7169579 : Blo 2123435 7169579 := bstep (se 1 (by rfl) ⟨5377184, by rfl⟩ : syracuseStep 7169579 = 10754369) B10754369
theorem B4779719 : Blo 2123435 4779719 := bstep (se 1 (by rfl) ⟨3584789, by rfl⟩ : syracuseStep 4779719 = 7169579) B7169579
theorem B3186479 : Blo 2123435 3186479 := bstep (se 1 (by rfl) ⟨2389859, by rfl⟩ : syracuseStep 3186479 = 4779719) B4779719
theorem B2124319 : Blo 2123435 2124319 := bstep (se 1 (by rfl) ⟨1593239, by rfl⟩ : syracuseStep 2124319 = 3186479) B3186479
theorem B3186485 : Blo 2123435 3186485 := bbase (se 5 (by rfl) ⟨149366, by rfl⟩ : syracuseStep 3186485 = 298733) (by norm_num)
theorem B2124323 : Blo 2123435 2124323 := bstep (se 1 (by rfl) ⟨1593242, by rfl⟩ : syracuseStep 2124323 = 3186485) B3186485
theorem B5377205 : Blo 2123435 5377205 := bbase (se 5 (by rfl) ⟨252056, by rfl⟩ : syracuseStep 5377205 = 504113) (by norm_num)
theorem B3584803 : Blo 2123435 3584803 := bstep (se 1 (by rfl) ⟨2688602, by rfl⟩ : syracuseStep 3584803 = 5377205) B5377205
theorem B4779737 : Blo 2123435 4779737 := bstep (se 2 (by rfl) ⟨1792401, by rfl⟩ : syracuseStep 4779737 = 3584803) B3584803
theorem B3186491 : Blo 2123435 3186491 := bstep (se 1 (by rfl) ⟨2389868, by rfl⟩ : syracuseStep 3186491 = 4779737) B4779737
theorem B2124327 : Blo 2123435 2124327 := bstep (se 1 (by rfl) ⟨1593245, by rfl⟩ : syracuseStep 2124327 = 3186491) B3186491
theorem B2389873 : Blo 2123435 2389873 := bbase (se 2 (by rfl) ⟨896202, by rfl⟩ : syracuseStep 2389873 = 1792405) (by norm_num)
theorem B3186497 : Blo 2123435 3186497 := bstep (se 2 (by rfl) ⟨1194936, by rfl⟩ : syracuseStep 3186497 = 2389873) B2389873
theorem B2124331 : Blo 2123435 2124331 := bstep (se 1 (by rfl) ⟨1593248, by rfl⟩ : syracuseStep 2124331 = 3186497) B3186497
theorem B9074069 : Blo 2123435 9074069 := bbase (se 6 (by rfl) ⟨212673, by rfl⟩ : syracuseStep 9074069 = 425347) (by norm_num)
theorem B6049379 : Blo 2123435 6049379 := bstep (se 1 (by rfl) ⟨4537034, by rfl⟩ : syracuseStep 6049379 = 9074069) B9074069
theorem B4032919 : Blo 2123435 4032919 := bstep (se 1 (by rfl) ⟨3024689, by rfl⟩ : syracuseStep 4032919 = 6049379) B6049379
theorem B5377225 : Blo 2123435 5377225 := bstep (se 2 (by rfl) ⟨2016459, by rfl⟩ : syracuseStep 5377225 = 4032919) B4032919
theorem B7169633 : Blo 2123435 7169633 := bstep (se 2 (by rfl) ⟨2688612, by rfl⟩ : syracuseStep 7169633 = 5377225) B5377225
theorem B4779755 : Blo 2123435 4779755 := bstep (se 1 (by rfl) ⟨3584816, by rfl⟩ : syracuseStep 4779755 = 7169633) B7169633
theorem B3186503 : Blo 2123435 3186503 := bstep (se 1 (by rfl) ⟨2389877, by rfl⟩ : syracuseStep 3186503 = 4779755) B4779755
theorem B2124335 : Blo 2123435 2124335 := bstep (se 1 (by rfl) ⟨1593251, by rfl⟩ : syracuseStep 2124335 = 3186503) B3186503
theorem B3186509 : Blo 2123435 3186509 := bbase (se 3 (by rfl) ⟨597470, by rfl⟩ : syracuseStep 3186509 = 1194941) (by norm_num)
theorem B2124339 : Blo 2123435 2124339 := bstep (se 1 (by rfl) ⟨1593254, by rfl⟩ : syracuseStep 2124339 = 3186509) B3186509
theorem B4779773 : Blo 2123435 4779773 := bbase (se 3 (by rfl) ⟨896207, by rfl⟩ : syracuseStep 4779773 = 1792415) (by norm_num)
theorem B3186515 : Blo 2123435 3186515 := bstep (se 1 (by rfl) ⟨2389886, by rfl⟩ : syracuseStep 3186515 = 4779773) B4779773
theorem B2124343 : Blo 2123435 2124343 := bstep (se 1 (by rfl) ⟨1593257, by rfl⟩ : syracuseStep 2124343 = 3186515) B3186515
theorem B3584837 : Blo 2123435 3584837 := bbase (se 4 (by rfl) ⟨336078, by rfl⟩ : syracuseStep 3584837 = 672157) (by norm_num)
theorem B2389891 : Blo 2123435 2389891 := bstep (se 1 (by rfl) ⟨1792418, by rfl⟩ : syracuseStep 2389891 = 3584837) B3584837
theorem B3186521 : Blo 2123435 3186521 := bstep (se 2 (by rfl) ⟨1194945, by rfl⟩ : syracuseStep 3186521 = 2389891) B2389891
theorem B2124347 : Blo 2123435 2124347 := bstep (se 1 (by rfl) ⟨1593260, by rfl⟩ : syracuseStep 2124347 = 3186521) B3186521
theorem B16131797 : Blo 2123435 16131797 := bbase (se 7 (by rfl) ⟨189044, by rfl⟩ : syracuseStep 16131797 = 378089) (by norm_num)
theorem B10754531 : Blo 2123435 10754531 := bstep (se 1 (by rfl) ⟨8065898, by rfl⟩ : syracuseStep 10754531 = 16131797) B16131797
theorem B7169687 : Blo 2123435 7169687 := bstep (se 1 (by rfl) ⟨5377265, by rfl⟩ : syracuseStep 7169687 = 10754531) B10754531
theorem B4779791 : Blo 2123435 4779791 := bstep (se 1 (by rfl) ⟨3584843, by rfl⟩ : syracuseStep 4779791 = 7169687) B7169687
theorem B3186527 : Blo 2123435 3186527 := bstep (se 1 (by rfl) ⟨2389895, by rfl⟩ : syracuseStep 3186527 = 4779791) B4779791
theorem B2124351 : Blo 2123435 2124351 := bstep (se 1 (by rfl) ⟨1593263, by rfl⟩ : syracuseStep 2124351 = 3186527) B3186527
theorem B3186533 : Blo 2123435 3186533 := bbase (se 4 (by rfl) ⟨298737, by rfl⟩ : syracuseStep 3186533 = 597475) (by norm_num)
theorem B2124355 : Blo 2123435 2124355 := bstep (se 1 (by rfl) ⟨1593266, by rfl⟩ : syracuseStep 2124355 = 3186533) B3186533
theorem B4032965 : Blo 2123435 4032965 := bbase (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) (by norm_num)
theorem B2688643 : Blo 2123435 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B3584857 : Blo 2123435 3584857 := bstep (se 2 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 3584857 = 2688643) B2688643
theorem B4779809 : Blo 2123435 4779809 := bstep (se 2 (by rfl) ⟨1792428, by rfl⟩ : syracuseStep 4779809 = 3584857) B3584857
theorem B3186539 : Blo 2123435 3186539 := bstep (se 1 (by rfl) ⟨2389904, by rfl⟩ : syracuseStep 3186539 = 4779809) B4779809
theorem B2124359 : Blo 2123435 2124359 := bstep (se 1 (by rfl) ⟨1593269, by rfl⟩ : syracuseStep 2124359 = 3186539) B3186539
theorem B2389909 : Blo 2123435 2389909 := bbase (se 6 (by rfl) ⟨56013, by rfl⟩ : syracuseStep 2389909 = 112027) (by norm_num)
theorem B3186545 : Blo 2123435 3186545 := bstep (se 2 (by rfl) ⟨1194954, by rfl⟩ : syracuseStep 3186545 = 2389909) B2389909
theorem B2124363 : Blo 2123435 2124363 := bstep (se 1 (by rfl) ⟨1593272, by rfl⟩ : syracuseStep 2124363 = 3186545) B3186545
theorem B2688653 : Blo 2123435 2688653 := bbase (se 3 (by rfl) ⟨504122, by rfl⟩ : syracuseStep 2688653 = 1008245) (by norm_num)
theorem B7169741 : Blo 2123435 7169741 := bstep (se 3 (by rfl) ⟨1344326, by rfl⟩ : syracuseStep 7169741 = 2688653) B2688653
theorem B4779827 : Blo 2123435 4779827 := bstep (se 1 (by rfl) ⟨3584870, by rfl⟩ : syracuseStep 4779827 = 7169741) B7169741
theorem B3186551 : Blo 2123435 3186551 := bstep (se 1 (by rfl) ⟨2389913, by rfl⟩ : syracuseStep 3186551 = 4779827) B4779827
theorem B2124367 : Blo 2123435 2124367 := bstep (se 1 (by rfl) ⟨1593275, by rfl⟩ : syracuseStep 2124367 = 3186551) B3186551
theorem B3186557 : Blo 2123435 3186557 := bbase (se 3 (by rfl) ⟨597479, by rfl⟩ : syracuseStep 3186557 = 1194959) (by norm_num)
theorem B2124371 : Blo 2123435 2124371 := bstep (se 1 (by rfl) ⟨1593278, by rfl⟩ : syracuseStep 2124371 = 3186557) B3186557
theorem B4779845 : Blo 2123435 4779845 := bbase (se 4 (by rfl) ⟨448110, by rfl⟩ : syracuseStep 4779845 = 896221) (by norm_num)
theorem B3186563 : Blo 2123435 3186563 := bstep (se 1 (by rfl) ⟨2389922, by rfl⟩ : syracuseStep 3186563 = 4779845) B4779845
theorem B2124375 : Blo 2123435 2124375 := bstep (se 1 (by rfl) ⟨1593281, by rfl⟩ : syracuseStep 2124375 = 3186563) B3186563
theorem B16352117 : Blo 2123435 16352117 := bbase (se 5 (by rfl) ⟨766505, by rfl⟩ : syracuseStep 16352117 = 1533011) (by norm_num)
theorem B10901411 : Blo 2123435 10901411 := bstep (se 1 (by rfl) ⟨8176058, by rfl⟩ : syracuseStep 10901411 = 16352117) B16352117
theorem B7267607 : Blo 2123435 7267607 := bstep (se 1 (by rfl) ⟨5450705, by rfl⟩ : syracuseStep 7267607 = 10901411) B10901411
theorem B4845071 : Blo 2123435 4845071 := bstep (se 1 (by rfl) ⟨3633803, by rfl⟩ : syracuseStep 4845071 = 7267607) B7267607
theorem B3230047 : Blo 2123435 3230047 := bstep (se 1 (by rfl) ⟨2422535, by rfl⟩ : syracuseStep 3230047 = 4845071) B4845071
theorem B17226917 : Blo 2123435 17226917 := bstep (se 4 (by rfl) ⟨1615023, by rfl⟩ : syracuseStep 17226917 = 3230047) B3230047
theorem B11484611 : Blo 2123435 11484611 := bstep (se 1 (by rfl) ⟨8613458, by rfl⟩ : syracuseStep 11484611 = 17226917) B17226917
theorem B7656407 : Blo 2123435 7656407 := bstep (se 1 (by rfl) ⟨5742305, by rfl⟩ : syracuseStep 7656407 = 11484611) B11484611
theorem B5104271 : Blo 2123435 5104271 := bstep (se 1 (by rfl) ⟨3828203, by rfl⟩ : syracuseStep 5104271 = 7656407) B7656407
theorem B3402847 : Blo 2123435 3402847 := bstep (se 1 (by rfl) ⟨2552135, by rfl⟩ : syracuseStep 3402847 = 5104271) B5104271
theorem B4537129 : Blo 2123435 4537129 := bstep (se 2 (by rfl) ⟨1701423, by rfl⟩ : syracuseStep 4537129 = 3402847) B3402847
theorem B6049505 : Blo 2123435 6049505 := bstep (se 2 (by rfl) ⟨2268564, by rfl⟩ : syracuseStep 6049505 = 4537129) B4537129
theorem B4033003 : Blo 2123435 4033003 := bstep (se 1 (by rfl) ⟨3024752, by rfl⟩ : syracuseStep 4033003 = 6049505) B6049505
theorem B5377337 : Blo 2123435 5377337 := bstep (se 2 (by rfl) ⟨2016501, by rfl⟩ : syracuseStep 5377337 = 4033003) B4033003
theorem B3584891 : Blo 2123435 3584891 := bstep (se 1 (by rfl) ⟨2688668, by rfl⟩ : syracuseStep 3584891 = 5377337) B5377337
theorem B2389927 : Blo 2123435 2389927 := bstep (se 1 (by rfl) ⟨1792445, by rfl⟩ : syracuseStep 2389927 = 3584891) B3584891
theorem B3186569 : Blo 2123435 3186569 := bstep (se 2 (by rfl) ⟨1194963, by rfl⟩ : syracuseStep 3186569 = 2389927) B2389927
theorem B2124379 : Blo 2123435 2124379 := bstep (se 1 (by rfl) ⟨1593284, by rfl⟩ : syracuseStep 2124379 = 3186569) B3186569
theorem B10754693 : Blo 2123435 10754693 := bbase (se 4 (by rfl) ⟨1008252, by rfl⟩ : syracuseStep 10754693 = 2016505) (by norm_num)
theorem B7169795 : Blo 2123435 7169795 := bstep (se 1 (by rfl) ⟨5377346, by rfl⟩ : syracuseStep 7169795 = 10754693) B10754693
theorem B4779863 : Blo 2123435 4779863 := bstep (se 1 (by rfl) ⟨3584897, by rfl⟩ : syracuseStep 4779863 = 7169795) B7169795
theorem B3186575 : Blo 2123435 3186575 := bstep (se 1 (by rfl) ⟨2389931, by rfl⟩ : syracuseStep 3186575 = 4779863) B4779863
theorem B2124383 : Blo 2123435 2124383 := bstep (se 1 (by rfl) ⟨1593287, by rfl⟩ : syracuseStep 2124383 = 3186575) B3186575
theorem B3186581 : Blo 2123435 3186581 := bbase (se 6 (by rfl) ⟨74685, by rfl⟩ : syracuseStep 3186581 = 149371) (by norm_num)
theorem B2124387 : Blo 2123435 2124387 := bstep (se 1 (by rfl) ⟨1593290, by rfl⟩ : syracuseStep 2124387 = 3186581) B3186581
theorem B2268577 : Blo 2123435 2268577 := bbase (se 2 (by rfl) ⟨850716, by rfl⟩ : syracuseStep 2268577 = 1701433) (by norm_num)
theorem B12099077 : Blo 2123435 12099077 := bstep (se 4 (by rfl) ⟨1134288, by rfl⟩ : syracuseStep 12099077 = 2268577) B2268577
theorem B8066051 : Blo 2123435 8066051 := bstep (se 1 (by rfl) ⟨6049538, by rfl⟩ : syracuseStep 8066051 = 12099077) B12099077
theorem B5377367 : Blo 2123435 5377367 := bstep (se 1 (by rfl) ⟨4033025, by rfl⟩ : syracuseStep 5377367 = 8066051) B8066051
theorem B3584911 : Blo 2123435 3584911 := bstep (se 1 (by rfl) ⟨2688683, by rfl⟩ : syracuseStep 3584911 = 5377367) B5377367
theorem B4779881 : Blo 2123435 4779881 := bstep (se 2 (by rfl) ⟨1792455, by rfl⟩ : syracuseStep 4779881 = 3584911) B3584911
theorem B3186587 : Blo 2123435 3186587 := bstep (se 1 (by rfl) ⟨2389940, by rfl⟩ : syracuseStep 3186587 = 4779881) B4779881
theorem B2124391 : Blo 2123435 2124391 := bstep (se 1 (by rfl) ⟨1593293, by rfl⟩ : syracuseStep 2124391 = 3186587) B3186587
theorem B2389945 : Blo 2123435 2389945 := bbase (se 2 (by rfl) ⟨896229, by rfl⟩ : syracuseStep 2389945 = 1792459) (by norm_num)
theorem B3186593 : Blo 2123435 3186593 := bstep (se 2 (by rfl) ⟨1194972, by rfl⟩ : syracuseStep 3186593 = 2389945) B2389945
theorem B2124395 : Blo 2123435 2124395 := bstep (se 1 (by rfl) ⟨1593296, by rfl⟩ : syracuseStep 2124395 = 3186593) B3186593
theorem B12920309 : Blo 2123435 12920309 := bbase (se 5 (by rfl) ⟨605639, by rfl⟩ : syracuseStep 12920309 = 1211279) (by norm_num)
theorem B8613539 : Blo 2123435 8613539 := bstep (se 1 (by rfl) ⟨6460154, by rfl⟩ : syracuseStep 8613539 = 12920309) B12920309
theorem B5742359 : Blo 2123435 5742359 := bstep (se 1 (by rfl) ⟨4306769, by rfl⟩ : syracuseStep 5742359 = 8613539) B8613539
theorem B3828239 : Blo 2123435 3828239 := bstep (se 1 (by rfl) ⟨2871179, by rfl⟩ : syracuseStep 3828239 = 5742359) B5742359
theorem B2552159 : Blo 2123435 2552159 := bstep (se 1 (by rfl) ⟨1914119, by rfl⟩ : syracuseStep 2552159 = 3828239) B3828239
theorem B6805757 : Blo 2123435 6805757 := bstep (se 3 (by rfl) ⟨1276079, by rfl⟩ : syracuseStep 6805757 = 2552159) B2552159
theorem B4537171 : Blo 2123435 4537171 := bstep (se 1 (by rfl) ⟨3402878, by rfl⟩ : syracuseStep 4537171 = 6805757) B6805757
theorem B6049561 : Blo 2123435 6049561 := bstep (se 2 (by rfl) ⟨2268585, by rfl⟩ : syracuseStep 6049561 = 4537171) B4537171
theorem B8066081 : Blo 2123435 8066081 := bstep (se 2 (by rfl) ⟨3024780, by rfl⟩ : syracuseStep 8066081 = 6049561) B6049561
theorem B5377387 : Blo 2123435 5377387 := bstep (se 1 (by rfl) ⟨4033040, by rfl⟩ : syracuseStep 5377387 = 8066081) B8066081
theorem B7169849 : Blo 2123435 7169849 := bstep (se 2 (by rfl) ⟨2688693, by rfl⟩ : syracuseStep 7169849 = 5377387) B5377387
theorem B4779899 : Blo 2123435 4779899 := bstep (se 1 (by rfl) ⟨3584924, by rfl⟩ : syracuseStep 4779899 = 7169849) B7169849
theorem B3186599 : Blo 2123435 3186599 := bstep (se 1 (by rfl) ⟨2389949, by rfl⟩ : syracuseStep 3186599 = 4779899) B4779899
theorem B2124399 : Blo 2123435 2124399 := bstep (se 1 (by rfl) ⟨1593299, by rfl⟩ : syracuseStep 2124399 = 3186599) B3186599
theorem B3186605 : Blo 2123435 3186605 := bbase (se 3 (by rfl) ⟨597488, by rfl⟩ : syracuseStep 3186605 = 1194977) (by norm_num)
theorem B2124403 : Blo 2123435 2124403 := bstep (se 1 (by rfl) ⟨1593302, by rfl⟩ : syracuseStep 2124403 = 3186605) B3186605
theorem B4779917 : Blo 2123435 4779917 := bbase (se 3 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 4779917 = 1792469) (by norm_num)
theorem B3186611 : Blo 2123435 3186611 := bstep (se 1 (by rfl) ⟨2389958, by rfl⟩ : syracuseStep 3186611 = 4779917) B4779917
theorem B2124407 : Blo 2123435 2124407 := bstep (se 1 (by rfl) ⟨1593305, by rfl⟩ : syracuseStep 2124407 = 3186611) B3186611
theorem B2688709 : Blo 2123435 2688709 := bbase (se 4 (by rfl) ⟨252066, by rfl⟩ : syracuseStep 2688709 = 504133) (by norm_num)
theorem B3584945 : Blo 2123435 3584945 := bstep (se 2 (by rfl) ⟨1344354, by rfl⟩ : syracuseStep 3584945 = 2688709) B2688709
theorem B2389963 : Blo 2123435 2389963 := bstep (se 1 (by rfl) ⟨1792472, by rfl⟩ : syracuseStep 2389963 = 3584945) B3584945
theorem B3186617 : Blo 2123435 3186617 := bstep (se 2 (by rfl) ⟨1194981, by rfl⟩ : syracuseStep 3186617 = 2389963) B2389963
theorem B2124411 : Blo 2123435 2124411 := bstep (se 1 (by rfl) ⟨1593308, by rfl⟩ : syracuseStep 2124411 = 3186617) B3186617
theorem B4599109 : Blo 2123435 4599109 := bbase (se 4 (by rfl) ⟨431166, by rfl⟩ : syracuseStep 4599109 = 862333) (by norm_num)
theorem B6132145 : Blo 2123435 6132145 := bstep (se 2 (by rfl) ⟨2299554, by rfl⟩ : syracuseStep 6132145 = 4599109) B4599109
theorem B8176193 : Blo 2123435 8176193 := bstep (se 2 (by rfl) ⟨3066072, by rfl⟩ : syracuseStep 8176193 = 6132145) B6132145
theorem B5450795 : Blo 2123435 5450795 := bstep (se 1 (by rfl) ⟨4088096, by rfl⟩ : syracuseStep 5450795 = 8176193) B8176193
theorem B3633863 : Blo 2123435 3633863 := bstep (se 1 (by rfl) ⟨2725397, by rfl⟩ : syracuseStep 3633863 = 5450795) B5450795
theorem B9690301 : Blo 2123435 9690301 := bstep (se 3 (by rfl) ⟨1816931, by rfl⟩ : syracuseStep 9690301 = 3633863) B3633863
theorem B12920401 : Blo 2123435 12920401 := bstep (se 2 (by rfl) ⟨4845150, by rfl⟩ : syracuseStep 12920401 = 9690301) B9690301
theorem B17227201 : Blo 2123435 17227201 := bstep (se 2 (by rfl) ⟨6460200, by rfl⟩ : syracuseStep 17227201 = 12920401) B12920401
theorem B22969601 : Blo 2123435 22969601 := bstep (se 2 (by rfl) ⟨8613600, by rfl⟩ : syracuseStep 22969601 = 17227201) B17227201
theorem B15313067 : Blo 2123435 15313067 := bstep (se 1 (by rfl) ⟨11484800, by rfl⟩ : syracuseStep 15313067 = 22969601) B22969601
theorem B10208711 : Blo 2123435 10208711 := bstep (se 1 (by rfl) ⟨7656533, by rfl⟩ : syracuseStep 10208711 = 15313067) B15313067
theorem B27223229 : Blo 2123435 27223229 := bstep (se 3 (by rfl) ⟨5104355, by rfl⟩ : syracuseStep 27223229 = 10208711) B10208711
theorem B18148819 : Blo 2123435 18148819 := bstep (se 1 (by rfl) ⟨13611614, by rfl⟩ : syracuseStep 18148819 = 27223229) B27223229
theorem B24198425 : Blo 2123435 24198425 := bstep (se 2 (by rfl) ⟨9074409, by rfl⟩ : syracuseStep 24198425 = 18148819) B18148819
theorem B16132283 : Blo 2123435 16132283 := bstep (se 1 (by rfl) ⟨12099212, by rfl⟩ : syracuseStep 16132283 = 24198425) B24198425
theorem B10754855 : Blo 2123435 10754855 := bstep (se 1 (by rfl) ⟨8066141, by rfl⟩ : syracuseStep 10754855 = 16132283) B16132283
theorem B7169903 : Blo 2123435 7169903 := bstep (se 1 (by rfl) ⟨5377427, by rfl⟩ : syracuseStep 7169903 = 10754855) B10754855
theorem B4779935 : Blo 2123435 4779935 := bstep (se 1 (by rfl) ⟨3584951, by rfl⟩ : syracuseStep 4779935 = 7169903) B7169903
theorem B3186623 : Blo 2123435 3186623 := bstep (se 1 (by rfl) ⟨2389967, by rfl⟩ : syracuseStep 3186623 = 4779935) B4779935
theorem B2124415 : Blo 2123435 2124415 := bstep (se 1 (by rfl) ⟨1593311, by rfl⟩ : syracuseStep 2124415 = 3186623) B3186623
theorem B3186629 : Blo 2123435 3186629 := bbase (se 4 (by rfl) ⟨298746, by rfl⟩ : syracuseStep 3186629 = 597493) (by norm_num)
theorem B2124419 : Blo 2123435 2124419 := bstep (se 1 (by rfl) ⟨1593314, by rfl⟩ : syracuseStep 2124419 = 3186629) B3186629
theorem B3584965 : Blo 2123435 3584965 := bbase (se 4 (by rfl) ⟨336090, by rfl⟩ : syracuseStep 3584965 = 672181) (by norm_num)
theorem B4779953 : Blo 2123435 4779953 := bstep (se 2 (by rfl) ⟨1792482, by rfl⟩ : syracuseStep 4779953 = 3584965) B3584965
theorem B3186635 : Blo 2123435 3186635 := bstep (se 1 (by rfl) ⟨2389976, by rfl⟩ : syracuseStep 3186635 = 4779953) B4779953
theorem B2124423 : Blo 2123435 2124423 := bstep (se 1 (by rfl) ⟨1593317, by rfl⟩ : syracuseStep 2124423 = 3186635) B3186635
theorem B2389981 : Blo 2123435 2389981 := bbase (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) (by norm_num)
theorem B3186641 : Blo 2123435 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B2124427 : Blo 2123435 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B7169957 : Blo 2123435 7169957 := bbase (se 4 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 7169957 = 1344367) (by norm_num)
theorem B4779971 : Blo 2123435 4779971 := bstep (se 1 (by rfl) ⟨3584978, by rfl⟩ : syracuseStep 4779971 = 7169957) B7169957
theorem B3186647 : Blo 2123435 3186647 := bstep (se 1 (by rfl) ⟨2389985, by rfl⟩ : syracuseStep 3186647 = 4779971) B4779971
theorem B2124431 : Blo 2123435 2124431 := bstep (se 1 (by rfl) ⟨1593323, by rfl⟩ : syracuseStep 2124431 = 3186647) B3186647
theorem B3186653 : Blo 2123435 3186653 := bbase (se 3 (by rfl) ⟨597497, by rfl⟩ : syracuseStep 3186653 = 1194995) (by norm_num)
theorem B2124435 : Blo 2123435 2124435 := bstep (se 1 (by rfl) ⟨1593326, by rfl⟩ : syracuseStep 2124435 = 3186653) B3186653
theorem B4779989 : Blo 2123435 4779989 := bbase (se 7 (by rfl) ⟨56015, by rfl⟩ : syracuseStep 4779989 = 112031) (by norm_num)
theorem B3186659 : Blo 2123435 3186659 := bstep (se 1 (by rfl) ⟨2389994, by rfl⟩ : syracuseStep 3186659 = 4779989) B4779989
theorem B2124439 : Blo 2123435 2124439 := bstep (se 1 (by rfl) ⟨1593329, by rfl⟩ : syracuseStep 2124439 = 3186659) B3186659
theorem B13611797 : Blo 2123435 13611797 := bbase (se 6 (by rfl) ⟨319026, by rfl⟩ : syracuseStep 13611797 = 638053) (by norm_num)
theorem B9074531 : Blo 2123435 9074531 := bstep (se 1 (by rfl) ⟨6805898, by rfl⟩ : syracuseStep 9074531 = 13611797) B13611797
theorem B6049687 : Blo 2123435 6049687 := bstep (se 1 (by rfl) ⟨4537265, by rfl⟩ : syracuseStep 6049687 = 9074531) B9074531
theorem B8066249 : Blo 2123435 8066249 := bstep (se 2 (by rfl) ⟨3024843, by rfl⟩ : syracuseStep 8066249 = 6049687) B6049687
theorem B5377499 : Blo 2123435 5377499 := bstep (se 1 (by rfl) ⟨4033124, by rfl⟩ : syracuseStep 5377499 = 8066249) B8066249
theorem B3584999 : Blo 2123435 3584999 := bstep (se 1 (by rfl) ⟨2688749, by rfl⟩ : syracuseStep 3584999 = 5377499) B5377499
theorem B2389999 : Blo 2123435 2389999 := bstep (se 1 (by rfl) ⟨1792499, by rfl⟩ : syracuseStep 2389999 = 3584999) B3584999
theorem B3186665 : Blo 2123435 3186665 := bstep (se 2 (by rfl) ⟨1194999, by rfl⟩ : syracuseStep 3186665 = 2389999) B2389999
theorem B2124443 : Blo 2123435 2124443 := bstep (se 1 (by rfl) ⟨1593332, by rfl⟩ : syracuseStep 2124443 = 3186665) B3186665
theorem B3828325 : Blo 2123435 3828325 := bbase (se 4 (by rfl) ⟨358905, by rfl⟩ : syracuseStep 3828325 = 717811) (by norm_num)
theorem B5104433 : Blo 2123435 5104433 := bstep (se 2 (by rfl) ⟨1914162, by rfl⟩ : syracuseStep 5104433 = 3828325) B3828325
theorem B3402955 : Blo 2123435 3402955 := bstep (se 1 (by rfl) ⟨2552216, by rfl⟩ : syracuseStep 3402955 = 5104433) B5104433
theorem B18149093 : Blo 2123435 18149093 := bstep (se 4 (by rfl) ⟨1701477, by rfl⟩ : syracuseStep 18149093 = 3402955) B3402955
theorem B12099395 : Blo 2123435 12099395 := bstep (se 1 (by rfl) ⟨9074546, by rfl⟩ : syracuseStep 12099395 = 18149093) B18149093
theorem B8066263 : Blo 2123435 8066263 := bstep (se 1 (by rfl) ⟨6049697, by rfl⟩ : syracuseStep 8066263 = 12099395) B12099395
theorem B10755017 : Blo 2123435 10755017 := bstep (se 2 (by rfl) ⟨4033131, by rfl⟩ : syracuseStep 10755017 = 8066263) B8066263
theorem B7170011 : Blo 2123435 7170011 := bstep (se 1 (by rfl) ⟨5377508, by rfl⟩ : syracuseStep 7170011 = 10755017) B10755017
theorem B4780007 : Blo 2123435 4780007 := bstep (se 1 (by rfl) ⟨3585005, by rfl⟩ : syracuseStep 4780007 = 7170011) B7170011
theorem B3186671 : Blo 2123435 3186671 := bstep (se 1 (by rfl) ⟨2390003, by rfl⟩ : syracuseStep 3186671 = 4780007) B4780007
theorem B2124447 : Blo 2123435 2124447 := bstep (se 1 (by rfl) ⟨1593335, by rfl⟩ : syracuseStep 2124447 = 3186671) B3186671
theorem B3186677 : Blo 2123435 3186677 := bbase (se 5 (by rfl) ⟨149375, by rfl⟩ : syracuseStep 3186677 = 298751) (by norm_num)
theorem B2124451 : Blo 2123435 2124451 := bstep (se 1 (by rfl) ⟨1593338, by rfl⟩ : syracuseStep 2124451 = 3186677) B3186677
theorem B5104453 : Blo 2123435 5104453 := bbase (se 4 (by rfl) ⟨478542, by rfl⟩ : syracuseStep 5104453 = 957085) (by norm_num)
theorem B6805937 : Blo 2123435 6805937 := bstep (se 2 (by rfl) ⟨2552226, by rfl⟩ : syracuseStep 6805937 = 5104453) B5104453
theorem B4537291 : Blo 2123435 4537291 := bstep (se 1 (by rfl) ⟨3402968, by rfl⟩ : syracuseStep 4537291 = 6805937) B6805937
theorem B6049721 : Blo 2123435 6049721 := bstep (se 2 (by rfl) ⟨2268645, by rfl⟩ : syracuseStep 6049721 = 4537291) B4537291
theorem B4033147 : Blo 2123435 4033147 := bstep (se 1 (by rfl) ⟨3024860, by rfl⟩ : syracuseStep 4033147 = 6049721) B6049721
theorem B5377529 : Blo 2123435 5377529 := bstep (se 2 (by rfl) ⟨2016573, by rfl⟩ : syracuseStep 5377529 = 4033147) B4033147
theorem B3585019 : Blo 2123435 3585019 := bstep (se 1 (by rfl) ⟨2688764, by rfl⟩ : syracuseStep 3585019 = 5377529) B5377529
theorem B4780025 : Blo 2123435 4780025 := bstep (se 2 (by rfl) ⟨1792509, by rfl⟩ : syracuseStep 4780025 = 3585019) B3585019
theorem B3186683 : Blo 2123435 3186683 := bstep (se 1 (by rfl) ⟨2390012, by rfl⟩ : syracuseStep 3186683 = 4780025) B4780025
theorem B2124455 : Blo 2123435 2124455 := bstep (se 1 (by rfl) ⟨1593341, by rfl⟩ : syracuseStep 2124455 = 3186683) B3186683
theorem B2390017 : Blo 2123435 2390017 := bbase (se 2 (by rfl) ⟨896256, by rfl⟩ : syracuseStep 2390017 = 1792513) (by norm_num)
theorem B3186689 : Blo 2123435 3186689 := bstep (se 2 (by rfl) ⟨1195008, by rfl⟩ : syracuseStep 3186689 = 2390017) B2390017
theorem B2124459 : Blo 2123435 2124459 := bstep (se 1 (by rfl) ⟨1593344, by rfl⟩ : syracuseStep 2124459 = 3186689) B3186689
theorem B5377549 : Blo 2123435 5377549 := bbase (se 3 (by rfl) ⟨1008290, by rfl⟩ : syracuseStep 5377549 = 2016581) (by norm_num)
theorem B7170065 : Blo 2123435 7170065 := bstep (se 2 (by rfl) ⟨2688774, by rfl⟩ : syracuseStep 7170065 = 5377549) B5377549
theorem B4780043 : Blo 2123435 4780043 := bstep (se 1 (by rfl) ⟨3585032, by rfl⟩ : syracuseStep 4780043 = 7170065) B7170065
theorem B3186695 : Blo 2123435 3186695 := bstep (se 1 (by rfl) ⟨2390021, by rfl⟩ : syracuseStep 3186695 = 4780043) B4780043
theorem B2124463 : Blo 2123435 2124463 := bstep (se 1 (by rfl) ⟨1593347, by rfl⟩ : syracuseStep 2124463 = 3186695) B3186695
theorem B3186701 : Blo 2123435 3186701 := bbase (se 3 (by rfl) ⟨597506, by rfl⟩ : syracuseStep 3186701 = 1195013) (by norm_num)
theorem B2124467 : Blo 2123435 2124467 := bstep (se 1 (by rfl) ⟨1593350, by rfl⟩ : syracuseStep 2124467 = 3186701) B3186701
theorem B4780061 : Blo 2123435 4780061 := bbase (se 3 (by rfl) ⟨896261, by rfl⟩ : syracuseStep 4780061 = 1792523) (by norm_num)
theorem B3186707 : Blo 2123435 3186707 := bstep (se 1 (by rfl) ⟨2390030, by rfl⟩ : syracuseStep 3186707 = 4780061) B4780061
theorem B2124471 : Blo 2123435 2124471 := bstep (se 1 (by rfl) ⟨1593353, by rfl⟩ : syracuseStep 2124471 = 3186707) B3186707
theorem B3585053 : Blo 2123435 3585053 := bbase (se 3 (by rfl) ⟨672197, by rfl⟩ : syracuseStep 3585053 = 1344395) (by norm_num)
theorem B2390035 : Blo 2123435 2390035 := bstep (se 1 (by rfl) ⟨1792526, by rfl⟩ : syracuseStep 2390035 = 3585053) B3585053
theorem B3186713 : Blo 2123435 3186713 := bstep (se 2 (by rfl) ⟨1195017, by rfl⟩ : syracuseStep 3186713 = 2390035) B2390035
theorem B2124475 : Blo 2123435 2124475 := bstep (se 1 (by rfl) ⟨1593356, by rfl⟩ : syracuseStep 2124475 = 3186713) B3186713
theorem B11050661 : Blo 2123435 11050661 := bbase (se 4 (by rfl) ⟨1035999, by rfl⟩ : syracuseStep 11050661 = 2071999) (by norm_num)
theorem B7367107 : Blo 2123435 7367107 := bstep (se 1 (by rfl) ⟨5525330, by rfl⟩ : syracuseStep 7367107 = 11050661) B11050661
theorem B9822809 : Blo 2123435 9822809 := bstep (se 2 (by rfl) ⟨3683553, by rfl⟩ : syracuseStep 9822809 = 7367107) B7367107
theorem B6548539 : Blo 2123435 6548539 := bstep (se 1 (by rfl) ⟨4911404, by rfl⟩ : syracuseStep 6548539 = 9822809) B9822809
theorem B8731385 : Blo 2123435 8731385 := bstep (se 2 (by rfl) ⟨3274269, by rfl⟩ : syracuseStep 8731385 = 6548539) B6548539
theorem B5820923 : Blo 2123435 5820923 := bstep (se 1 (by rfl) ⟨4365692, by rfl⟩ : syracuseStep 5820923 = 8731385) B8731385
theorem B15522461 : Blo 2123435 15522461 := bstep (se 3 (by rfl) ⟨2910461, by rfl⟩ : syracuseStep 15522461 = 5820923) B5820923
theorem B10348307 : Blo 2123435 10348307 := bstep (se 1 (by rfl) ⟨7761230, by rfl⟩ : syracuseStep 10348307 = 15522461) B15522461
theorem B6898871 : Blo 2123435 6898871 := bstep (se 1 (by rfl) ⟨5174153, by rfl⟩ : syracuseStep 6898871 = 10348307) B10348307
theorem B18396989 : Blo 2123435 18396989 := bstep (se 3 (by rfl) ⟨3449435, by rfl⟩ : syracuseStep 18396989 = 6898871) B6898871
theorem B12264659 : Blo 2123435 12264659 := bstep (se 1 (by rfl) ⟨9198494, by rfl⟩ : syracuseStep 12264659 = 18396989) B18396989
theorem B8176439 : Blo 2123435 8176439 := bstep (se 1 (by rfl) ⟨6132329, by rfl⟩ : syracuseStep 8176439 = 12264659) B12264659
theorem B5450959 : Blo 2123435 5450959 := bstep (se 1 (by rfl) ⟨4088219, by rfl⟩ : syracuseStep 5450959 = 8176439) B8176439
theorem B29071781 : Blo 2123435 29071781 := bstep (se 4 (by rfl) ⟨2725479, by rfl⟩ : syracuseStep 29071781 = 5450959) B5450959
theorem B19381187 : Blo 2123435 19381187 := bstep (se 1 (by rfl) ⟨14535890, by rfl⟩ : syracuseStep 19381187 = 29071781) B29071781
theorem B12920791 : Blo 2123435 12920791 := bstep (se 1 (by rfl) ⟨9690593, by rfl⟩ : syracuseStep 12920791 = 19381187) B19381187
theorem B17227721 : Blo 2123435 17227721 := bstep (se 2 (by rfl) ⟨6460395, by rfl⟩ : syracuseStep 17227721 = 12920791) B12920791
theorem B11485147 : Blo 2123435 11485147 := bstep (se 1 (by rfl) ⟨8613860, by rfl⟩ : syracuseStep 11485147 = 17227721) B17227721
theorem B15313529 : Blo 2123435 15313529 := bstep (se 2 (by rfl) ⟨5742573, by rfl⟩ : syracuseStep 15313529 = 11485147) B11485147
theorem B10209019 : Blo 2123435 10209019 := bstep (se 1 (by rfl) ⟨7656764, by rfl⟩ : syracuseStep 10209019 = 15313529) B15313529
theorem B13612025 : Blo 2123435 13612025 := bstep (se 2 (by rfl) ⟨5104509, by rfl⟩ : syracuseStep 13612025 = 10209019) B10209019
theorem B9074683 : Blo 2123435 9074683 := bstep (se 1 (by rfl) ⟨6806012, by rfl⟩ : syracuseStep 9074683 = 13612025) B13612025
theorem B12099577 : Blo 2123435 12099577 := bstep (se 2 (by rfl) ⟨4537341, by rfl⟩ : syracuseStep 12099577 = 9074683) B9074683
theorem B16132769 : Blo 2123435 16132769 := bstep (se 2 (by rfl) ⟨6049788, by rfl⟩ : syracuseStep 16132769 = 12099577) B12099577
theorem B10755179 : Blo 2123435 10755179 := bstep (se 1 (by rfl) ⟨8066384, by rfl⟩ : syracuseStep 10755179 = 16132769) B16132769
theorem B7170119 : Blo 2123435 7170119 := bstep (se 1 (by rfl) ⟨5377589, by rfl⟩ : syracuseStep 7170119 = 10755179) B10755179
theorem B4780079 : Blo 2123435 4780079 := bstep (se 1 (by rfl) ⟨3585059, by rfl⟩ : syracuseStep 4780079 = 7170119) B7170119
theorem B3186719 : Blo 2123435 3186719 := bstep (se 1 (by rfl) ⟨2390039, by rfl⟩ : syracuseStep 3186719 = 4780079) B4780079
theorem B2124479 : Blo 2123435 2124479 := bstep (se 1 (by rfl) ⟨1593359, by rfl⟩ : syracuseStep 2124479 = 3186719) B3186719
theorem B3186725 : Blo 2123435 3186725 := bbase (se 4 (by rfl) ⟨298755, by rfl⟩ : syracuseStep 3186725 = 597511) (by norm_num)
theorem B2124483 : Blo 2123435 2124483 := bstep (se 1 (by rfl) ⟨1593362, by rfl⟩ : syracuseStep 2124483 = 3186725) B3186725
theorem B2688805 : Blo 2123435 2688805 := bbase (se 4 (by rfl) ⟨252075, by rfl⟩ : syracuseStep 2688805 = 504151) (by norm_num)
theorem B3585073 : Blo 2123435 3585073 := bstep (se 2 (by rfl) ⟨1344402, by rfl⟩ : syracuseStep 3585073 = 2688805) B2688805
theorem B4780097 : Blo 2123435 4780097 := bstep (se 2 (by rfl) ⟨1792536, by rfl⟩ : syracuseStep 4780097 = 3585073) B3585073
theorem B3186731 : Blo 2123435 3186731 := bstep (se 1 (by rfl) ⟨2390048, by rfl⟩ : syracuseStep 3186731 = 4780097) B4780097
theorem B2124487 : Blo 2123435 2124487 := bstep (se 1 (by rfl) ⟨1593365, by rfl⟩ : syracuseStep 2124487 = 3186731) B3186731
theorem B2390053 : Blo 2123435 2390053 := bbase (se 4 (by rfl) ⟨224067, by rfl⟩ : syracuseStep 2390053 = 448135) (by norm_num)
theorem B3186737 : Blo 2123435 3186737 := bstep (se 2 (by rfl) ⟨1195026, by rfl⟩ : syracuseStep 3186737 = 2390053) B2390053
theorem B2124491 : Blo 2123435 2124491 := bstep (se 1 (by rfl) ⟨1593368, by rfl⟩ : syracuseStep 2124491 = 3186737) B3186737
theorem B5104549 : Blo 2123435 5104549 := bbase (se 4 (by rfl) ⟨478551, by rfl⟩ : syracuseStep 5104549 = 957103) (by norm_num)
theorem B6806065 : Blo 2123435 6806065 := bstep (se 2 (by rfl) ⟨2552274, by rfl⟩ : syracuseStep 6806065 = 5104549) B5104549
theorem B9074753 : Blo 2123435 9074753 := bstep (se 2 (by rfl) ⟨3403032, by rfl⟩ : syracuseStep 9074753 = 6806065) B6806065
theorem B6049835 : Blo 2123435 6049835 := bstep (se 1 (by rfl) ⟨4537376, by rfl⟩ : syracuseStep 6049835 = 9074753) B9074753
theorem B4033223 : Blo 2123435 4033223 := bstep (se 1 (by rfl) ⟨3024917, by rfl⟩ : syracuseStep 4033223 = 6049835) B6049835
theorem B2688815 : Blo 2123435 2688815 := bstep (se 1 (by rfl) ⟨2016611, by rfl⟩ : syracuseStep 2688815 = 4033223) B4033223
theorem B7170173 : Blo 2123435 7170173 := bstep (se 3 (by rfl) ⟨1344407, by rfl⟩ : syracuseStep 7170173 = 2688815) B2688815
theorem B4780115 : Blo 2123435 4780115 := bstep (se 1 (by rfl) ⟨3585086, by rfl⟩ : syracuseStep 4780115 = 7170173) B7170173
theorem B3186743 : Blo 2123435 3186743 := bstep (se 1 (by rfl) ⟨2390057, by rfl⟩ : syracuseStep 3186743 = 4780115) B4780115
theorem B2124495 : Blo 2123435 2124495 := bstep (se 1 (by rfl) ⟨1593371, by rfl⟩ : syracuseStep 2124495 = 3186743) B3186743
theorem B3186749 : Blo 2123435 3186749 := bbase (se 3 (by rfl) ⟨597515, by rfl⟩ : syracuseStep 3186749 = 1195031) (by norm_num)
theorem B2124499 : Blo 2123435 2124499 := bstep (se 1 (by rfl) ⟨1593374, by rfl⟩ : syracuseStep 2124499 = 3186749) B3186749
theorem B4780133 : Blo 2123435 4780133 := bbase (se 4 (by rfl) ⟨448137, by rfl⟩ : syracuseStep 4780133 = 896275) (by norm_num)
theorem B3186755 : Blo 2123435 3186755 := bstep (se 1 (by rfl) ⟨2390066, by rfl⟩ : syracuseStep 3186755 = 4780133) B4780133
theorem B2124503 : Blo 2123435 2124503 := bstep (se 1 (by rfl) ⟨1593377, by rfl⟩ : syracuseStep 2124503 = 3186755) B3186755
theorem B5377661 : Blo 2123435 5377661 := bbase (se 3 (by rfl) ⟨1008311, by rfl⟩ : syracuseStep 5377661 = 2016623) (by norm_num)
theorem B3585107 : Blo 2123435 3585107 := bstep (se 1 (by rfl) ⟨2688830, by rfl⟩ : syracuseStep 3585107 = 5377661) B5377661
theorem B2390071 : Blo 2123435 2390071 := bstep (se 1 (by rfl) ⟨1792553, by rfl⟩ : syracuseStep 2390071 = 3585107) B3585107
theorem B3186761 : Blo 2123435 3186761 := bstep (se 2 (by rfl) ⟨1195035, by rfl⟩ : syracuseStep 3186761 = 2390071) B2390071
theorem B2124507 : Blo 2123435 2124507 := bstep (se 1 (by rfl) ⟨1593380, by rfl⟩ : syracuseStep 2124507 = 3186761) B3186761
theorem B4033253 : Blo 2123435 4033253 := bbase (se 4 (by rfl) ⟨378117, by rfl⟩ : syracuseStep 4033253 = 756235) (by norm_num)
theorem B10755341 : Blo 2123435 10755341 := bstep (se 3 (by rfl) ⟨2016626, by rfl⟩ : syracuseStep 10755341 = 4033253) B4033253
theorem B7170227 : Blo 2123435 7170227 := bstep (se 1 (by rfl) ⟨5377670, by rfl⟩ : syracuseStep 7170227 = 10755341) B10755341
theorem B4780151 : Blo 2123435 4780151 := bstep (se 1 (by rfl) ⟨3585113, by rfl⟩ : syracuseStep 4780151 = 7170227) B7170227
theorem B3186767 : Blo 2123435 3186767 := bstep (se 1 (by rfl) ⟨2390075, by rfl⟩ : syracuseStep 3186767 = 4780151) B4780151
theorem B2124511 : Blo 2123435 2124511 := bstep (se 1 (by rfl) ⟨1593383, by rfl⟩ : syracuseStep 2124511 = 3186767) B3186767
theorem B3186773 : Blo 2123435 3186773 := bbase (se 8 (by rfl) ⟨18672, by rfl⟩ : syracuseStep 3186773 = 37345) (by norm_num)
theorem B2124515 : Blo 2123435 2124515 := bstep (se 1 (by rfl) ⟨1593386, by rfl⟩ : syracuseStep 2124515 = 3186773) B3186773
theorem B11642069 : Blo 2123435 11642069 := bbase (se 7 (by rfl) ⟨136430, by rfl⟩ : syracuseStep 11642069 = 272861) (by norm_num)
theorem B7761379 : Blo 2123435 7761379 := bstep (se 1 (by rfl) ⟨5821034, by rfl⟩ : syracuseStep 7761379 = 11642069) B11642069
theorem B10348505 : Blo 2123435 10348505 := bstep (se 2 (by rfl) ⟨3880689, by rfl⟩ : syracuseStep 10348505 = 7761379) B7761379
theorem B6899003 : Blo 2123435 6899003 := bstep (se 1 (by rfl) ⟨5174252, by rfl⟩ : syracuseStep 6899003 = 10348505) B10348505
theorem B4599335 : Blo 2123435 4599335 := bstep (se 1 (by rfl) ⟨3449501, by rfl⟩ : syracuseStep 4599335 = 6899003) B6899003
theorem B3066223 : Blo 2123435 3066223 := bstep (se 1 (by rfl) ⟨2299667, by rfl⟩ : syracuseStep 3066223 = 4599335) B4599335
theorem B4088297 : Blo 2123435 4088297 := bstep (se 2 (by rfl) ⟨1533111, by rfl⟩ : syracuseStep 4088297 = 3066223) B3066223
theorem B2725531 : Blo 2123435 2725531 := bstep (se 1 (by rfl) ⟨2044148, by rfl⟩ : syracuseStep 2725531 = 4088297) B4088297
theorem B58144661 : Blo 2123435 58144661 := bstep (se 6 (by rfl) ⟨1362765, by rfl⟩ : syracuseStep 58144661 = 2725531) B2725531
theorem B38763107 : Blo 2123435 38763107 := bstep (se 1 (by rfl) ⟨29072330, by rfl⟩ : syracuseStep 38763107 = 58144661) B58144661
theorem B25842071 : Blo 2123435 25842071 := bstep (se 1 (by rfl) ⟨19381553, by rfl⟩ : syracuseStep 25842071 = 38763107) B38763107
theorem B17228047 : Blo 2123435 17228047 := bstep (se 1 (by rfl) ⟨12921035, by rfl⟩ : syracuseStep 17228047 = 25842071) B25842071
theorem B22970729 : Blo 2123435 22970729 := bstep (se 2 (by rfl) ⟨8614023, by rfl⟩ : syracuseStep 22970729 = 17228047) B17228047
theorem B15313819 : Blo 2123435 15313819 := bstep (se 1 (by rfl) ⟨11485364, by rfl⟩ : syracuseStep 15313819 = 22970729) B22970729
theorem B20418425 : Blo 2123435 20418425 := bstep (se 2 (by rfl) ⟨7656909, by rfl⟩ : syracuseStep 20418425 = 15313819) B15313819
theorem B13612283 : Blo 2123435 13612283 := bstep (se 1 (by rfl) ⟨10209212, by rfl⟩ : syracuseStep 13612283 = 20418425) B20418425
theorem B9074855 : Blo 2123435 9074855 := bstep (se 1 (by rfl) ⟨6806141, by rfl⟩ : syracuseStep 9074855 = 13612283) B13612283
theorem B6049903 : Blo 2123435 6049903 := bstep (se 1 (by rfl) ⟨4537427, by rfl⟩ : syracuseStep 6049903 = 9074855) B9074855
theorem B8066537 : Blo 2123435 8066537 := bstep (se 2 (by rfl) ⟨3024951, by rfl⟩ : syracuseStep 8066537 = 6049903) B6049903
theorem B5377691 : Blo 2123435 5377691 := bstep (se 1 (by rfl) ⟨4033268, by rfl⟩ : syracuseStep 5377691 = 8066537) B8066537
theorem B3585127 : Blo 2123435 3585127 := bstep (se 1 (by rfl) ⟨2688845, by rfl⟩ : syracuseStep 3585127 = 5377691) B5377691
theorem B4780169 : Blo 2123435 4780169 := bstep (se 2 (by rfl) ⟨1792563, by rfl⟩ : syracuseStep 4780169 = 3585127) B3585127
theorem B3186779 : Blo 2123435 3186779 := bstep (se 1 (by rfl) ⟨2390084, by rfl⟩ : syracuseStep 3186779 = 4780169) B4780169
theorem B2124519 : Blo 2123435 2124519 := bstep (se 1 (by rfl) ⟨1593389, by rfl⟩ : syracuseStep 2124519 = 3186779) B3186779
theorem B2390089 : Blo 2123435 2390089 := bbase (se 2 (by rfl) ⟨896283, by rfl⟩ : syracuseStep 2390089 = 1792567) (by norm_num)
theorem B3186785 : Blo 2123435 3186785 := bstep (se 2 (by rfl) ⟨1195044, by rfl⟩ : syracuseStep 3186785 = 2390089) B2390089
theorem B2124523 : Blo 2123435 2124523 := bstep (se 1 (by rfl) ⟨1593392, by rfl⟩ : syracuseStep 2124523 = 3186785) B3186785
theorem B3828469 : Blo 2123435 3828469 := bbase (se 5 (by rfl) ⟨179459, by rfl⟩ : syracuseStep 3828469 = 358919) (by norm_num)
theorem B5104625 : Blo 2123435 5104625 := bstep (se 2 (by rfl) ⟨1914234, by rfl⟩ : syracuseStep 5104625 = 3828469) B3828469
theorem B13612333 : Blo 2123435 13612333 := bstep (se 3 (by rfl) ⟨2552312, by rfl⟩ : syracuseStep 13612333 = 5104625) B5104625
theorem B18149777 : Blo 2123435 18149777 := bstep (se 2 (by rfl) ⟨6806166, by rfl⟩ : syracuseStep 18149777 = 13612333) B13612333
theorem B12099851 : Blo 2123435 12099851 := bstep (se 1 (by rfl) ⟨9074888, by rfl⟩ : syracuseStep 12099851 = 18149777) B18149777
theorem B8066567 : Blo 2123435 8066567 := bstep (se 1 (by rfl) ⟨6049925, by rfl⟩ : syracuseStep 8066567 = 12099851) B12099851
theorem B5377711 : Blo 2123435 5377711 := bstep (se 1 (by rfl) ⟨4033283, by rfl⟩ : syracuseStep 5377711 = 8066567) B8066567
theorem B7170281 : Blo 2123435 7170281 := bstep (se 2 (by rfl) ⟨2688855, by rfl⟩ : syracuseStep 7170281 = 5377711) B5377711
theorem B4780187 : Blo 2123435 4780187 := bstep (se 1 (by rfl) ⟨3585140, by rfl⟩ : syracuseStep 4780187 = 7170281) B7170281
theorem B3186791 : Blo 2123435 3186791 := bstep (se 1 (by rfl) ⟨2390093, by rfl⟩ : syracuseStep 3186791 = 4780187) B4780187
theorem B2124527 : Blo 2123435 2124527 := bstep (se 1 (by rfl) ⟨1593395, by rfl⟩ : syracuseStep 2124527 = 3186791) B3186791
theorem B3186797 : Blo 2123435 3186797 := bbase (se 3 (by rfl) ⟨597524, by rfl⟩ : syracuseStep 3186797 = 1195049) (by norm_num)
theorem B2124531 : Blo 2123435 2124531 := bstep (se 1 (by rfl) ⟨1593398, by rfl⟩ : syracuseStep 2124531 = 3186797) B3186797
theorem B4780205 : Blo 2123435 4780205 := bbase (se 3 (by rfl) ⟨896288, by rfl⟩ : syracuseStep 4780205 = 1792577) (by norm_num)
theorem B3186803 : Blo 2123435 3186803 := bstep (se 1 (by rfl) ⟨2390102, by rfl⟩ : syracuseStep 3186803 = 4780205) B4780205
theorem B2124535 : Blo 2123435 2124535 := bstep (se 1 (by rfl) ⟨1593401, by rfl⟩ : syracuseStep 2124535 = 3186803) B3186803
theorem B43608917 : Blo 2123435 43608917 := bbase (se 9 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 43608917 = 255521) (by norm_num)
theorem B29072611 : Blo 2123435 29072611 := bstep (se 1 (by rfl) ⟨21804458, by rfl⟩ : syracuseStep 29072611 = 43608917) B43608917
theorem B38763481 : Blo 2123435 38763481 := bstep (se 2 (by rfl) ⟨14536305, by rfl⟩ : syracuseStep 38763481 = 29072611) B29072611
theorem B51684641 : Blo 2123435 51684641 := bstep (se 2 (by rfl) ⟨19381740, by rfl⟩ : syracuseStep 51684641 = 38763481) B38763481
theorem B34456427 : Blo 2123435 34456427 := bstep (se 1 (by rfl) ⟨25842320, by rfl⟩ : syracuseStep 34456427 = 51684641) B51684641
theorem B22970951 : Blo 2123435 22970951 := bstep (se 1 (by rfl) ⟨17228213, by rfl⟩ : syracuseStep 22970951 = 34456427) B34456427
theorem B15313967 : Blo 2123435 15313967 := bstep (se 1 (by rfl) ⟨11485475, by rfl⟩ : syracuseStep 15313967 = 22970951) B22970951
theorem B10209311 : Blo 2123435 10209311 := bstep (se 1 (by rfl) ⟨7656983, by rfl⟩ : syracuseStep 10209311 = 15313967) B15313967
theorem B6806207 : Blo 2123435 6806207 := bstep (se 1 (by rfl) ⟨5104655, by rfl⟩ : syracuseStep 6806207 = 10209311) B10209311
theorem B4537471 : Blo 2123435 4537471 := bstep (se 1 (by rfl) ⟨3403103, by rfl⟩ : syracuseStep 4537471 = 6806207) B6806207
theorem B6049961 : Blo 2123435 6049961 := bstep (se 2 (by rfl) ⟨2268735, by rfl⟩ : syracuseStep 6049961 = 4537471) B4537471
theorem B4033307 : Blo 2123435 4033307 := bstep (se 1 (by rfl) ⟨3024980, by rfl⟩ : syracuseStep 4033307 = 6049961) B6049961
theorem B2688871 : Blo 2123435 2688871 := bstep (se 1 (by rfl) ⟨2016653, by rfl⟩ : syracuseStep 2688871 = 4033307) B4033307
theorem B3585161 : Blo 2123435 3585161 := bstep (se 2 (by rfl) ⟨1344435, by rfl⟩ : syracuseStep 3585161 = 2688871) B2688871
theorem B2390107 : Blo 2123435 2390107 := bstep (se 1 (by rfl) ⟨1792580, by rfl⟩ : syracuseStep 2390107 = 3585161) B3585161
theorem B3186809 : Blo 2123435 3186809 := bstep (se 2 (by rfl) ⟨1195053, by rfl⟩ : syracuseStep 3186809 = 2390107) B2390107
theorem B2124539 : Blo 2123435 2124539 := bstep (se 1 (by rfl) ⟨1593404, by rfl⟩ : syracuseStep 2124539 = 3186809) B3186809
theorem B11485493 : Blo 2123435 11485493 := bbase (se 5 (by rfl) ⟨538382, by rfl⟩ : syracuseStep 11485493 = 1076765) (by norm_num)
theorem B7656995 : Blo 2123435 7656995 := bstep (se 1 (by rfl) ⟨5742746, by rfl⟩ : syracuseStep 7656995 = 11485493) B11485493
theorem B5104663 : Blo 2123435 5104663 := bstep (se 1 (by rfl) ⟨3828497, by rfl⟩ : syracuseStep 5104663 = 7656995) B7656995
theorem B27224869 : Blo 2123435 27224869 := bstep (se 4 (by rfl) ⟨2552331, by rfl⟩ : syracuseStep 27224869 = 5104663) B5104663
theorem B36299825 : Blo 2123435 36299825 := bstep (se 2 (by rfl) ⟨13612434, by rfl⟩ : syracuseStep 36299825 = 27224869) B27224869
theorem B24199883 : Blo 2123435 24199883 := bstep (se 1 (by rfl) ⟨18149912, by rfl⟩ : syracuseStep 24199883 = 36299825) B36299825
theorem B16133255 : Blo 2123435 16133255 := bstep (se 1 (by rfl) ⟨12099941, by rfl⟩ : syracuseStep 16133255 = 24199883) B24199883
theorem B10755503 : Blo 2123435 10755503 := bstep (se 1 (by rfl) ⟨8066627, by rfl⟩ : syracuseStep 10755503 = 16133255) B16133255
theorem B7170335 : Blo 2123435 7170335 := bstep (se 1 (by rfl) ⟨5377751, by rfl⟩ : syracuseStep 7170335 = 10755503) B10755503
theorem B4780223 : Blo 2123435 4780223 := bstep (se 1 (by rfl) ⟨3585167, by rfl⟩ : syracuseStep 4780223 = 7170335) B7170335
theorem B3186815 : Blo 2123435 3186815 := bstep (se 1 (by rfl) ⟨2390111, by rfl⟩ : syracuseStep 3186815 = 4780223) B4780223
theorem B2124543 : Blo 2123435 2124543 := bstep (se 1 (by rfl) ⟨1593407, by rfl⟩ : syracuseStep 2124543 = 3186815) B3186815
theorem B3186821 : Blo 2123435 3186821 := bbase (se 4 (by rfl) ⟨298764, by rfl⟩ : syracuseStep 3186821 = 597529) (by norm_num)
theorem B2124547 : Blo 2123435 2124547 := bstep (se 1 (by rfl) ⟨1593410, by rfl⟩ : syracuseStep 2124547 = 3186821) B3186821
theorem B3585181 : Blo 2123435 3585181 := bbase (se 3 (by rfl) ⟨672221, by rfl⟩ : syracuseStep 3585181 = 1344443) (by norm_num)
theorem B4780241 : Blo 2123435 4780241 := bstep (se 2 (by rfl) ⟨1792590, by rfl⟩ : syracuseStep 4780241 = 3585181) B3585181
theorem B3186827 : Blo 2123435 3186827 := bstep (se 1 (by rfl) ⟨2390120, by rfl⟩ : syracuseStep 3186827 = 4780241) B4780241
theorem B2124551 : Blo 2123435 2124551 := bstep (se 1 (by rfl) ⟨1593413, by rfl⟩ : syracuseStep 2124551 = 3186827) B3186827
theorem B2390125 : Blo 2123435 2390125 := bbase (se 3 (by rfl) ⟨448148, by rfl⟩ : syracuseStep 2390125 = 896297) (by norm_num)
theorem B3186833 : Blo 2123435 3186833 := bstep (se 2 (by rfl) ⟨1195062, by rfl⟩ : syracuseStep 3186833 = 2390125) B2390125
theorem B2124555 : Blo 2123435 2124555 := bstep (se 1 (by rfl) ⟨1593416, by rfl⟩ : syracuseStep 2124555 = 3186833) B3186833
theorem B7170389 : Blo 2123435 7170389 := bbase (se 10 (by rfl) ⟨10503, by rfl⟩ : syracuseStep 7170389 = 21007) (by norm_num)
theorem B4780259 : Blo 2123435 4780259 := bstep (se 1 (by rfl) ⟨3585194, by rfl⟩ : syracuseStep 4780259 = 7170389) B7170389
theorem B3186839 : Blo 2123435 3186839 := bstep (se 1 (by rfl) ⟨2390129, by rfl⟩ : syracuseStep 3186839 = 4780259) B4780259
theorem B2124559 : Blo 2123435 2124559 := bstep (se 1 (by rfl) ⟨1593419, by rfl⟩ : syracuseStep 2124559 = 3186839) B3186839
theorem B3186845 : Blo 2123435 3186845 := bbase (se 3 (by rfl) ⟨597533, by rfl⟩ : syracuseStep 3186845 = 1195067) (by norm_num)
theorem B2124563 : Blo 2123435 2124563 := bstep (se 1 (by rfl) ⟨1593422, by rfl⟩ : syracuseStep 2124563 = 3186845) B3186845
theorem B4780277 : Blo 2123435 4780277 := bbase (se 5 (by rfl) ⟨224075, by rfl⟩ : syracuseStep 4780277 = 448151) (by norm_num)
theorem B3186851 : Blo 2123435 3186851 := bstep (se 1 (by rfl) ⟨2390138, by rfl⟩ : syracuseStep 3186851 = 4780277) B4780277
theorem B2124567 : Blo 2123435 2124567 := bstep (se 1 (by rfl) ⟨1593425, by rfl⟩ : syracuseStep 2124567 = 3186851) B3186851
theorem B16353589 : Blo 2123435 16353589 := bbase (se 5 (by rfl) ⟨766574, by rfl⟩ : syracuseStep 16353589 = 1533149) (by norm_num)
theorem B21804785 : Blo 2123435 21804785 := bstep (se 2 (by rfl) ⟨8176794, by rfl⟩ : syracuseStep 21804785 = 16353589) B16353589
theorem B14536523 : Blo 2123435 14536523 := bstep (se 1 (by rfl) ⟨10902392, by rfl⟩ : syracuseStep 14536523 = 21804785) B21804785
theorem B9691015 : Blo 2123435 9691015 := bstep (se 1 (by rfl) ⟨7268261, by rfl⟩ : syracuseStep 9691015 = 14536523) B14536523
theorem B12921353 : Blo 2123435 12921353 := bstep (se 2 (by rfl) ⟨4845507, by rfl⟩ : syracuseStep 12921353 = 9691015) B9691015
theorem B8614235 : Blo 2123435 8614235 := bstep (se 1 (by rfl) ⟨6460676, by rfl⟩ : syracuseStep 8614235 = 12921353) B12921353
theorem B5742823 : Blo 2123435 5742823 := bstep (se 1 (by rfl) ⟨4307117, by rfl⟩ : syracuseStep 5742823 = 8614235) B8614235
theorem B7657097 : Blo 2123435 7657097 := bstep (se 2 (by rfl) ⟨2871411, by rfl⟩ : syracuseStep 7657097 = 5742823) B5742823
theorem B20418925 : Blo 2123435 20418925 := bstep (se 3 (by rfl) ⟨3828548, by rfl⟩ : syracuseStep 20418925 = 7657097) B7657097
theorem B27225233 : Blo 2123435 27225233 := bstep (se 2 (by rfl) ⟨10209462, by rfl⟩ : syracuseStep 27225233 = 20418925) B20418925
theorem B18150155 : Blo 2123435 18150155 := bstep (se 1 (by rfl) ⟨13612616, by rfl⟩ : syracuseStep 18150155 = 27225233) B27225233
theorem B12100103 : Blo 2123435 12100103 := bstep (se 1 (by rfl) ⟨9075077, by rfl⟩ : syracuseStep 12100103 = 18150155) B18150155
theorem B8066735 : Blo 2123435 8066735 := bstep (se 1 (by rfl) ⟨6050051, by rfl⟩ : syracuseStep 8066735 = 12100103) B12100103
theorem B5377823 : Blo 2123435 5377823 := bstep (se 1 (by rfl) ⟨4033367, by rfl⟩ : syracuseStep 5377823 = 8066735) B8066735
theorem B3585215 : Blo 2123435 3585215 := bstep (se 1 (by rfl) ⟨2688911, by rfl⟩ : syracuseStep 3585215 = 5377823) B5377823
theorem B2390143 : Blo 2123435 2390143 := bstep (se 1 (by rfl) ⟨1792607, by rfl⟩ : syracuseStep 2390143 = 3585215) B3585215
theorem B3186857 : Blo 2123435 3186857 := bstep (se 2 (by rfl) ⟨1195071, by rfl⟩ : syracuseStep 3186857 = 2390143) B2390143
theorem B2124571 : Blo 2123435 2124571 := bstep (se 1 (by rfl) ⟨1593428, by rfl⟩ : syracuseStep 2124571 = 3186857) B3186857
theorem B5104741 : Blo 2123435 5104741 := bbase (se 4 (by rfl) ⟨478569, by rfl⟩ : syracuseStep 5104741 = 957139) (by norm_num)
theorem B6806321 : Blo 2123435 6806321 := bstep (se 2 (by rfl) ⟨2552370, by rfl⟩ : syracuseStep 6806321 = 5104741) B5104741
theorem B4537547 : Blo 2123435 4537547 := bstep (se 1 (by rfl) ⟨3403160, by rfl⟩ : syracuseStep 4537547 = 6806321) B6806321
theorem B3025031 : Blo 2123435 3025031 := bstep (se 1 (by rfl) ⟨2268773, by rfl⟩ : syracuseStep 3025031 = 4537547) B4537547
theorem B8066749 : Blo 2123435 8066749 := bstep (se 3 (by rfl) ⟨1512515, by rfl⟩ : syracuseStep 8066749 = 3025031) B3025031
theorem B10755665 : Blo 2123435 10755665 := bstep (se 2 (by rfl) ⟨4033374, by rfl⟩ : syracuseStep 10755665 = 8066749) B8066749
theorem B7170443 : Blo 2123435 7170443 := bstep (se 1 (by rfl) ⟨5377832, by rfl⟩ : syracuseStep 7170443 = 10755665) B10755665
theorem B4780295 : Blo 2123435 4780295 := bstep (se 1 (by rfl) ⟨3585221, by rfl⟩ : syracuseStep 4780295 = 7170443) B7170443
theorem B3186863 : Blo 2123435 3186863 := bstep (se 1 (by rfl) ⟨2390147, by rfl⟩ : syracuseStep 3186863 = 4780295) B4780295
theorem B2124575 : Blo 2123435 2124575 := bstep (se 1 (by rfl) ⟨1593431, by rfl⟩ : syracuseStep 2124575 = 3186863) B3186863
theorem B3186869 : Blo 2123435 3186869 := bbase (se 5 (by rfl) ⟨149384, by rfl⟩ : syracuseStep 3186869 = 298769) (by norm_num)
theorem B2124579 : Blo 2123435 2124579 := bstep (se 1 (by rfl) ⟨1593434, by rfl⟩ : syracuseStep 2124579 = 3186869) B3186869
theorem B5377853 : Blo 2123435 5377853 := bbase (se 3 (by rfl) ⟨1008347, by rfl⟩ : syracuseStep 5377853 = 2016695) (by norm_num)
theorem B3585235 : Blo 2123435 3585235 := bstep (se 1 (by rfl) ⟨2688926, by rfl⟩ : syracuseStep 3585235 = 5377853) B5377853
theorem B4780313 : Blo 2123435 4780313 := bstep (se 2 (by rfl) ⟨1792617, by rfl⟩ : syracuseStep 4780313 = 3585235) B3585235
theorem B3186875 : Blo 2123435 3186875 := bstep (se 1 (by rfl) ⟨2390156, by rfl⟩ : syracuseStep 3186875 = 4780313) B4780313
theorem B2124583 : Blo 2123435 2124583 := bstep (se 1 (by rfl) ⟨1593437, by rfl⟩ : syracuseStep 2124583 = 3186875) B3186875
theorem B2390161 : Blo 2123435 2390161 := bbase (se 2 (by rfl) ⟨896310, by rfl⟩ : syracuseStep 2390161 = 1792621) (by norm_num)
theorem B3186881 : Blo 2123435 3186881 := bstep (se 2 (by rfl) ⟨1195080, by rfl⟩ : syracuseStep 3186881 = 2390161) B2390161
theorem B2124587 : Blo 2123435 2124587 := bstep (se 1 (by rfl) ⟨1593440, by rfl⟩ : syracuseStep 2124587 = 3186881) B3186881
theorem B4033405 : Blo 2123435 4033405 := bbase (se 3 (by rfl) ⟨756263, by rfl⟩ : syracuseStep 4033405 = 1512527) (by norm_num)
theorem B5377873 : Blo 2123435 5377873 := bstep (se 2 (by rfl) ⟨2016702, by rfl⟩ : syracuseStep 5377873 = 4033405) B4033405
theorem B7170497 : Blo 2123435 7170497 := bstep (se 2 (by rfl) ⟨2688936, by rfl⟩ : syracuseStep 7170497 = 5377873) B5377873
theorem B4780331 : Blo 2123435 4780331 := bstep (se 1 (by rfl) ⟨3585248, by rfl⟩ : syracuseStep 4780331 = 7170497) B7170497
theorem B3186887 : Blo 2123435 3186887 := bstep (se 1 (by rfl) ⟨2390165, by rfl⟩ : syracuseStep 3186887 = 4780331) B4780331
theorem B2124591 : Blo 2123435 2124591 := bstep (se 1 (by rfl) ⟨1593443, by rfl⟩ : syracuseStep 2124591 = 3186887) B3186887
theorem B3186893 : Blo 2123435 3186893 := bbase (se 3 (by rfl) ⟨597542, by rfl⟩ : syracuseStep 3186893 = 1195085) (by norm_num)
theorem B2124595 : Blo 2123435 2124595 := bstep (se 1 (by rfl) ⟨1593446, by rfl⟩ : syracuseStep 2124595 = 3186893) B3186893
theorem B4780349 : Blo 2123435 4780349 := bbase (se 3 (by rfl) ⟨896315, by rfl⟩ : syracuseStep 4780349 = 1792631) (by norm_num)
theorem B3186899 : Blo 2123435 3186899 := bstep (se 1 (by rfl) ⟨2390174, by rfl⟩ : syracuseStep 3186899 = 4780349) B4780349
theorem B2124599 : Blo 2123435 2124599 := bstep (se 1 (by rfl) ⟨1593449, by rfl⟩ : syracuseStep 2124599 = 3186899) B3186899
theorem B3585269 : Blo 2123435 3585269 := bbase (se 5 (by rfl) ⟨168059, by rfl⟩ : syracuseStep 3585269 = 336119) (by norm_num)
theorem B2390179 : Blo 2123435 2390179 := bstep (se 1 (by rfl) ⟨1792634, by rfl⟩ : syracuseStep 2390179 = 3585269) B3585269
theorem B3186905 : Blo 2123435 3186905 := bstep (se 2 (by rfl) ⟨1195089, by rfl⟩ : syracuseStep 3186905 = 2390179) B2390179
theorem B2124603 : Blo 2123435 2124603 := bstep (se 1 (by rfl) ⟨1593452, by rfl⟩ : syracuseStep 2124603 = 3186905) B3186905
theorem B15314453 : Blo 2123435 15314453 := bbase (se 6 (by rfl) ⟨358932, by rfl⟩ : syracuseStep 15314453 = 717865) (by norm_num)
theorem B10209635 : Blo 2123435 10209635 := bstep (se 1 (by rfl) ⟨7657226, by rfl⟩ : syracuseStep 10209635 = 15314453) B15314453
theorem B6806423 : Blo 2123435 6806423 := bstep (se 1 (by rfl) ⟨5104817, by rfl⟩ : syracuseStep 6806423 = 10209635) B10209635
theorem B4537615 : Blo 2123435 4537615 := bstep (se 1 (by rfl) ⟨3403211, by rfl⟩ : syracuseStep 4537615 = 6806423) B6806423
theorem B6050153 : Blo 2123435 6050153 := bstep (se 2 (by rfl) ⟨2268807, by rfl⟩ : syracuseStep 6050153 = 4537615) B4537615
theorem B16133741 : Blo 2123435 16133741 := bstep (se 3 (by rfl) ⟨3025076, by rfl⟩ : syracuseStep 16133741 = 6050153) B6050153
theorem B10755827 : Blo 2123435 10755827 := bstep (se 1 (by rfl) ⟨8066870, by rfl⟩ : syracuseStep 10755827 = 16133741) B16133741
theorem B7170551 : Blo 2123435 7170551 := bstep (se 1 (by rfl) ⟨5377913, by rfl⟩ : syracuseStep 7170551 = 10755827) B10755827
theorem B4780367 : Blo 2123435 4780367 := bstep (se 1 (by rfl) ⟨3585275, by rfl⟩ : syracuseStep 4780367 = 7170551) B7170551
theorem B3186911 : Blo 2123435 3186911 := bstep (se 1 (by rfl) ⟨2390183, by rfl⟩ : syracuseStep 3186911 = 4780367) B4780367
theorem B2124607 : Blo 2123435 2124607 := bstep (se 1 (by rfl) ⟨1593455, by rfl⟩ : syracuseStep 2124607 = 3186911) B3186911
theorem B3186917 : Blo 2123435 3186917 := bbase (se 4 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 3186917 = 597547) (by norm_num)
theorem B2124611 : Blo 2123435 2124611 := bstep (se 1 (by rfl) ⟨1593458, by rfl⟩ : syracuseStep 2124611 = 3186917) B3186917
theorem B3828629 : Blo 2123435 3828629 := bbase (se 6 (by rfl) ⟨89733, by rfl⟩ : syracuseStep 3828629 = 179467) (by norm_num)
theorem B2552419 : Blo 2123435 2552419 := bstep (se 1 (by rfl) ⟨1914314, by rfl⟩ : syracuseStep 2552419 = 3828629) B3828629
theorem B3403225 : Blo 2123435 3403225 := bstep (se 2 (by rfl) ⟨1276209, by rfl⟩ : syracuseStep 3403225 = 2552419) B2552419
theorem B4537633 : Blo 2123435 4537633 := bstep (se 2 (by rfl) ⟨1701612, by rfl⟩ : syracuseStep 4537633 = 3403225) B3403225
theorem B6050177 : Blo 2123435 6050177 := bstep (se 2 (by rfl) ⟨2268816, by rfl⟩ : syracuseStep 6050177 = 4537633) B4537633
theorem B4033451 : Blo 2123435 4033451 := bstep (se 1 (by rfl) ⟨3025088, by rfl⟩ : syracuseStep 4033451 = 6050177) B6050177
theorem B2688967 : Blo 2123435 2688967 := bstep (se 1 (by rfl) ⟨2016725, by rfl⟩ : syracuseStep 2688967 = 4033451) B4033451
theorem B3585289 : Blo 2123435 3585289 := bstep (se 2 (by rfl) ⟨1344483, by rfl⟩ : syracuseStep 3585289 = 2688967) B2688967
theorem B4780385 : Blo 2123435 4780385 := bstep (se 2 (by rfl) ⟨1792644, by rfl⟩ : syracuseStep 4780385 = 3585289) B3585289
theorem B3186923 : Blo 2123435 3186923 := bstep (se 1 (by rfl) ⟨2390192, by rfl⟩ : syracuseStep 3186923 = 4780385) B4780385
theorem B2124615 : Blo 2123435 2124615 := bstep (se 1 (by rfl) ⟨1593461, by rfl⟩ : syracuseStep 2124615 = 3186923) B3186923
theorem B2390197 : Blo 2123435 2390197 := bbase (se 5 (by rfl) ⟨112040, by rfl⟩ : syracuseStep 2390197 = 224081) (by norm_num)
theorem B3186929 : Blo 2123435 3186929 := bstep (se 2 (by rfl) ⟨1195098, by rfl⟩ : syracuseStep 3186929 = 2390197) B2390197
theorem B2124619 : Blo 2123435 2124619 := bstep (se 1 (by rfl) ⟨1593464, by rfl⟩ : syracuseStep 2124619 = 3186929) B3186929
theorem B2688977 : Blo 2123435 2688977 := bbase (se 2 (by rfl) ⟨1008366, by rfl⟩ : syracuseStep 2688977 = 2016733) (by norm_num)
theorem B7170605 : Blo 2123435 7170605 := bstep (se 3 (by rfl) ⟨1344488, by rfl⟩ : syracuseStep 7170605 = 2688977) B2688977
theorem B4780403 : Blo 2123435 4780403 := bstep (se 1 (by rfl) ⟨3585302, by rfl⟩ : syracuseStep 4780403 = 7170605) B7170605
theorem B3186935 : Blo 2123435 3186935 := bstep (se 1 (by rfl) ⟨2390201, by rfl⟩ : syracuseStep 3186935 = 4780403) B4780403
theorem B2124623 : Blo 2123435 2124623 := bstep (se 1 (by rfl) ⟨1593467, by rfl⟩ : syracuseStep 2124623 = 3186935) B3186935
theorem B3186941 : Blo 2123435 3186941 := bbase (se 3 (by rfl) ⟨597551, by rfl⟩ : syracuseStep 3186941 = 1195103) (by norm_num)
theorem B2124627 : Blo 2123435 2124627 := bstep (se 1 (by rfl) ⟨1593470, by rfl⟩ : syracuseStep 2124627 = 3186941) B3186941
theorem B4780421 : Blo 2123435 4780421 := bbase (se 4 (by rfl) ⟨448164, by rfl⟩ : syracuseStep 4780421 = 896329) (by norm_num)
theorem B3186947 : Blo 2123435 3186947 := bstep (se 1 (by rfl) ⟨2390210, by rfl⟩ : syracuseStep 3186947 = 4780421) B4780421
theorem B2124631 : Blo 2123435 2124631 := bstep (se 1 (by rfl) ⟨1593473, by rfl⟩ : syracuseStep 2124631 = 3186947) B3186947
theorem B3025117 : Blo 2123435 3025117 := bbase (se 3 (by rfl) ⟨567209, by rfl⟩ : syracuseStep 3025117 = 1134419) (by norm_num)
theorem B4033489 : Blo 2123435 4033489 := bstep (se 2 (by rfl) ⟨1512558, by rfl⟩ : syracuseStep 4033489 = 3025117) B3025117
theorem B5377985 : Blo 2123435 5377985 := bstep (se 2 (by rfl) ⟨2016744, by rfl⟩ : syracuseStep 5377985 = 4033489) B4033489
theorem B3585323 : Blo 2123435 3585323 := bstep (se 1 (by rfl) ⟨2688992, by rfl⟩ : syracuseStep 3585323 = 5377985) B5377985
theorem B2390215 : Blo 2123435 2390215 := bstep (se 1 (by rfl) ⟨1792661, by rfl⟩ : syracuseStep 2390215 = 3585323) B3585323
theorem B3186953 : Blo 2123435 3186953 := bstep (se 2 (by rfl) ⟨1195107, by rfl⟩ : syracuseStep 3186953 = 2390215) B2390215
theorem B2124635 : Blo 2123435 2124635 := bstep (se 1 (by rfl) ⟨1593476, by rfl⟩ : syracuseStep 2124635 = 3186953) B3186953
theorem B10755989 : Blo 2123435 10755989 := bbase (se 6 (by rfl) ⟨252093, by rfl⟩ : syracuseStep 10755989 = 504187) (by norm_num)
theorem B7170659 : Blo 2123435 7170659 := bstep (se 1 (by rfl) ⟨5377994, by rfl⟩ : syracuseStep 7170659 = 10755989) B10755989
theorem B4780439 : Blo 2123435 4780439 := bstep (se 1 (by rfl) ⟨3585329, by rfl⟩ : syracuseStep 4780439 = 7170659) B7170659
theorem B3186959 : Blo 2123435 3186959 := bstep (se 1 (by rfl) ⟨2390219, by rfl⟩ : syracuseStep 3186959 = 4780439) B4780439
theorem B2124639 : Blo 2123435 2124639 := bstep (se 1 (by rfl) ⟨1593479, by rfl⟩ : syracuseStep 2124639 = 3186959) B3186959
theorem B3186965 : Blo 2123435 3186965 := bbase (se 6 (by rfl) ⟨74694, by rfl⟩ : syracuseStep 3186965 = 149389) (by norm_num)
theorem B2124643 : Blo 2123435 2124643 := bstep (se 1 (by rfl) ⟨1593482, by rfl⟩ : syracuseStep 2124643 = 3186965) B3186965
theorem B15314741 : Blo 2123435 15314741 := bbase (se 5 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 15314741 = 1435757) (by norm_num)
theorem B10209827 : Blo 2123435 10209827 := bstep (se 1 (by rfl) ⟨7657370, by rfl⟩ : syracuseStep 10209827 = 15314741) B15314741
theorem B27226205 : Blo 2123435 27226205 := bstep (se 3 (by rfl) ⟨5104913, by rfl⟩ : syracuseStep 27226205 = 10209827) B10209827
theorem B18150803 : Blo 2123435 18150803 := bstep (se 1 (by rfl) ⟨13613102, by rfl⟩ : syracuseStep 18150803 = 27226205) B27226205
theorem B12100535 : Blo 2123435 12100535 := bstep (se 1 (by rfl) ⟨9075401, by rfl⟩ : syracuseStep 12100535 = 18150803) B18150803
theorem B8067023 : Blo 2123435 8067023 := bstep (se 1 (by rfl) ⟨6050267, by rfl⟩ : syracuseStep 8067023 = 12100535) B12100535
theorem B5378015 : Blo 2123435 5378015 := bstep (se 1 (by rfl) ⟨4033511, by rfl⟩ : syracuseStep 5378015 = 8067023) B8067023
theorem B3585343 : Blo 2123435 3585343 := bstep (se 1 (by rfl) ⟨2689007, by rfl⟩ : syracuseStep 3585343 = 5378015) B5378015
theorem B4780457 : Blo 2123435 4780457 := bstep (se 2 (by rfl) ⟨1792671, by rfl⟩ : syracuseStep 4780457 = 3585343) B3585343
theorem B3186971 : Blo 2123435 3186971 := bstep (se 1 (by rfl) ⟨2390228, by rfl⟩ : syracuseStep 3186971 = 4780457) B4780457
theorem B2124647 : Blo 2123435 2124647 := bstep (se 1 (by rfl) ⟨1593485, by rfl⟩ : syracuseStep 2124647 = 3186971) B3186971
theorem B2390233 : Blo 2123435 2390233 := bbase (se 2 (by rfl) ⟨896337, by rfl⟩ : syracuseStep 2390233 = 1792675) (by norm_num)
theorem B3186977 : Blo 2123435 3186977 := bstep (se 2 (by rfl) ⟨1195116, by rfl⟩ : syracuseStep 3186977 = 2390233) B2390233
theorem B2124651 : Blo 2123435 2124651 := bstep (se 1 (by rfl) ⟨1593488, by rfl⟩ : syracuseStep 2124651 = 3186977) B3186977
theorem B3828701 : Blo 2123435 3828701 := bbase (se 3 (by rfl) ⟨717881, by rfl⟩ : syracuseStep 3828701 = 1435763) (by norm_num)
theorem B2552467 : Blo 2123435 2552467 := bstep (se 1 (by rfl) ⟨1914350, by rfl⟩ : syracuseStep 2552467 = 3828701) B3828701
theorem B3403289 : Blo 2123435 3403289 := bstep (se 2 (by rfl) ⟨1276233, by rfl⟩ : syracuseStep 3403289 = 2552467) B2552467
theorem B2268859 : Blo 2123435 2268859 := bstep (se 1 (by rfl) ⟨1701644, by rfl⟩ : syracuseStep 2268859 = 3403289) B3403289
theorem B3025145 : Blo 2123435 3025145 := bstep (se 2 (by rfl) ⟨1134429, by rfl⟩ : syracuseStep 3025145 = 2268859) B2268859
theorem B8067053 : Blo 2123435 8067053 := bstep (se 3 (by rfl) ⟨1512572, by rfl⟩ : syracuseStep 8067053 = 3025145) B3025145
theorem B5378035 : Blo 2123435 5378035 := bstep (se 1 (by rfl) ⟨4033526, by rfl⟩ : syracuseStep 5378035 = 8067053) B8067053
theorem B7170713 : Blo 2123435 7170713 := bstep (se 2 (by rfl) ⟨2689017, by rfl⟩ : syracuseStep 7170713 = 5378035) B5378035
theorem B4780475 : Blo 2123435 4780475 := bstep (se 1 (by rfl) ⟨3585356, by rfl⟩ : syracuseStep 4780475 = 7170713) B7170713
theorem B3186983 : Blo 2123435 3186983 := bstep (se 1 (by rfl) ⟨2390237, by rfl⟩ : syracuseStep 3186983 = 4780475) B4780475
theorem B2124655 : Blo 2123435 2124655 := bstep (se 1 (by rfl) ⟨1593491, by rfl⟩ : syracuseStep 2124655 = 3186983) B3186983
theorem B3186989 : Blo 2123435 3186989 := bbase (se 3 (by rfl) ⟨597560, by rfl⟩ : syracuseStep 3186989 = 1195121) (by norm_num)
theorem B2124659 : Blo 2123435 2124659 := bstep (se 1 (by rfl) ⟨1593494, by rfl⟩ : syracuseStep 2124659 = 3186989) B3186989
theorem B4780493 : Blo 2123435 4780493 := bbase (se 3 (by rfl) ⟨896342, by rfl⟩ : syracuseStep 4780493 = 1792685) (by norm_num)
theorem B3186995 : Blo 2123435 3186995 := bstep (se 1 (by rfl) ⟨2390246, by rfl⟩ : syracuseStep 3186995 = 4780493) B4780493
theorem B2124663 : Blo 2123435 2124663 := bstep (se 1 (by rfl) ⟨1593497, by rfl⟩ : syracuseStep 2124663 = 3186995) B3186995
theorem B2689033 : Blo 2123435 2689033 := bbase (se 2 (by rfl) ⟨1008387, by rfl⟩ : syracuseStep 2689033 = 2016775) (by norm_num)
theorem B3585377 : Blo 2123435 3585377 := bstep (se 2 (by rfl) ⟨1344516, by rfl⟩ : syracuseStep 3585377 = 2689033) B2689033
theorem B2390251 : Blo 2123435 2390251 := bstep (se 1 (by rfl) ⟨1792688, by rfl⟩ : syracuseStep 2390251 = 3585377) B3585377
theorem B3187001 : Blo 2123435 3187001 := bstep (se 2 (by rfl) ⟨1195125, by rfl⟩ : syracuseStep 3187001 = 2390251) B2390251
theorem B2124667 : Blo 2123435 2124667 := bstep (se 1 (by rfl) ⟨1593500, by rfl⟩ : syracuseStep 2124667 = 3187001) B3187001
theorem B3634301 : Blo 2123435 3634301 := bbase (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) (by norm_num)
theorem B9691469 : Blo 2123435 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B6460979 : Blo 2123435 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B17229277 : Blo 2123435 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B22972369 : Blo 2123435 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B30629825 : Blo 2123435 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B20419883 : Blo 2123435 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B13613255 : Blo 2123435 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B9075503 : Blo 2123435 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B24201341 : Blo 2123435 24201341 := bstep (se 3 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 24201341 = 9075503) B9075503
theorem B16134227 : Blo 2123435 16134227 := bstep (se 1 (by rfl) ⟨12100670, by rfl⟩ : syracuseStep 16134227 = 24201341) B24201341
theorem B10756151 : Blo 2123435 10756151 := bstep (se 1 (by rfl) ⟨8067113, by rfl⟩ : syracuseStep 10756151 = 16134227) B16134227
theorem B7170767 : Blo 2123435 7170767 := bstep (se 1 (by rfl) ⟨5378075, by rfl⟩ : syracuseStep 7170767 = 10756151) B10756151
theorem B4780511 : Blo 2123435 4780511 := bstep (se 1 (by rfl) ⟨3585383, by rfl⟩ : syracuseStep 4780511 = 7170767) B7170767
theorem B3187007 : Blo 2123435 3187007 := bstep (se 1 (by rfl) ⟨2390255, by rfl⟩ : syracuseStep 3187007 = 4780511) B4780511
theorem B2124671 : Blo 2123435 2124671 := bstep (se 1 (by rfl) ⟨1593503, by rfl⟩ : syracuseStep 2124671 = 3187007) B3187007
theorem B3187013 : Blo 2123435 3187013 := bbase (se 4 (by rfl) ⟨298782, by rfl⟩ : syracuseStep 3187013 = 597565) (by norm_num)
theorem B2124675 : Blo 2123435 2124675 := bstep (se 1 (by rfl) ⟨1593506, by rfl⟩ : syracuseStep 2124675 = 3187013) B3187013
theorem B3585397 : Blo 2123435 3585397 := bbase (se 5 (by rfl) ⟨168065, by rfl⟩ : syracuseStep 3585397 = 336131) (by norm_num)
theorem B4780529 : Blo 2123435 4780529 := bstep (se 2 (by rfl) ⟨1792698, by rfl⟩ : syracuseStep 4780529 = 3585397) B3585397
theorem B3187019 : Blo 2123435 3187019 := bstep (se 1 (by rfl) ⟨2390264, by rfl⟩ : syracuseStep 3187019 = 4780529) B4780529
theorem B2124679 : Blo 2123435 2124679 := bstep (se 1 (by rfl) ⟨1593509, by rfl⟩ : syracuseStep 2124679 = 3187019) B3187019
theorem B2390269 : Blo 2123435 2390269 := bbase (se 3 (by rfl) ⟨448175, by rfl⟩ : syracuseStep 2390269 = 896351) (by norm_num)
theorem B3187025 : Blo 2123435 3187025 := bstep (se 2 (by rfl) ⟨1195134, by rfl⟩ : syracuseStep 3187025 = 2390269) B2390269
theorem B2124683 : Blo 2123435 2124683 := bstep (se 1 (by rfl) ⟨1593512, by rfl⟩ : syracuseStep 2124683 = 3187025) B3187025
theorem B7170821 : Blo 2123435 7170821 := bbase (se 4 (by rfl) ⟨672264, by rfl⟩ : syracuseStep 7170821 = 1344529) (by norm_num)
theorem B4780547 : Blo 2123435 4780547 := bstep (se 1 (by rfl) ⟨3585410, by rfl⟩ : syracuseStep 4780547 = 7170821) B7170821
theorem B3187031 : Blo 2123435 3187031 := bstep (se 1 (by rfl) ⟨2390273, by rfl⟩ : syracuseStep 3187031 = 4780547) B4780547
theorem B2124687 : Blo 2123435 2124687 := bstep (se 1 (by rfl) ⟨1593515, by rfl⟩ : syracuseStep 2124687 = 3187031) B3187031
theorem B3187037 : Blo 2123435 3187037 := bbase (se 3 (by rfl) ⟨597569, by rfl⟩ : syracuseStep 3187037 = 1195139) (by norm_num)
theorem B2124691 : Blo 2123435 2124691 := bstep (se 1 (by rfl) ⟨1593518, by rfl⟩ : syracuseStep 2124691 = 3187037) B3187037
theorem B4780565 : Blo 2123435 4780565 := bbase (se 6 (by rfl) ⟨112044, by rfl⟩ : syracuseStep 4780565 = 224089) (by norm_num)
theorem B3187043 : Blo 2123435 3187043 := bstep (se 1 (by rfl) ⟨2390282, by rfl⟩ : syracuseStep 3187043 = 4780565) B4780565
theorem B2124695 : Blo 2123435 2124695 := bstep (se 1 (by rfl) ⟨1593521, by rfl⟩ : syracuseStep 2124695 = 3187043) B3187043
theorem B8067221 : Blo 2123435 8067221 := bbase (se 6 (by rfl) ⟨189075, by rfl⟩ : syracuseStep 8067221 = 378151) (by norm_num)
theorem B5378147 : Blo 2123435 5378147 := bstep (se 1 (by rfl) ⟨4033610, by rfl⟩ : syracuseStep 5378147 = 8067221) B8067221
theorem B3585431 : Blo 2123435 3585431 := bstep (se 1 (by rfl) ⟨2689073, by rfl⟩ : syracuseStep 3585431 = 5378147) B5378147
theorem B2390287 : Blo 2123435 2390287 := bstep (se 1 (by rfl) ⟨1792715, by rfl⟩ : syracuseStep 2390287 = 3585431) B3585431
theorem B3187049 : Blo 2123435 3187049 := bstep (se 2 (by rfl) ⟨1195143, by rfl⟩ : syracuseStep 3187049 = 2390287) B2390287
theorem B2124699 : Blo 2123435 2124699 := bstep (se 1 (by rfl) ⟨1593524, by rfl⟩ : syracuseStep 2124699 = 3187049) B3187049
theorem B12100853 : Blo 2123435 12100853 := bbase (se 5 (by rfl) ⟨567227, by rfl⟩ : syracuseStep 12100853 = 1134455) (by norm_num)
theorem B8067235 : Blo 2123435 8067235 := bstep (se 1 (by rfl) ⟨6050426, by rfl⟩ : syracuseStep 8067235 = 12100853) B12100853
theorem B10756313 : Blo 2123435 10756313 := bstep (se 2 (by rfl) ⟨4033617, by rfl⟩ : syracuseStep 10756313 = 8067235) B8067235
theorem B7170875 : Blo 2123435 7170875 := bstep (se 1 (by rfl) ⟨5378156, by rfl⟩ : syracuseStep 7170875 = 10756313) B10756313
theorem B4780583 : Blo 2123435 4780583 := bstep (se 1 (by rfl) ⟨3585437, by rfl⟩ : syracuseStep 4780583 = 7170875) B7170875
theorem B3187055 : Blo 2123435 3187055 := bstep (se 1 (by rfl) ⟨2390291, by rfl⟩ : syracuseStep 3187055 = 4780583) B4780583
theorem B2124703 : Blo 2123435 2124703 := bstep (se 1 (by rfl) ⟨1593527, by rfl⟩ : syracuseStep 2124703 = 3187055) B3187055
theorem B3187061 : Blo 2123435 3187061 := bbase (se 5 (by rfl) ⟨149393, by rfl⟩ : syracuseStep 3187061 = 298787) (by norm_num)
theorem B2124707 : Blo 2123435 2124707 := bstep (se 1 (by rfl) ⟨1593530, by rfl⟩ : syracuseStep 2124707 = 3187061) B3187061
theorem B5105069 : Blo 2123435 5105069 := bbase (se 3 (by rfl) ⟨957200, by rfl⟩ : syracuseStep 5105069 = 1914401) (by norm_num)
theorem B3403379 : Blo 2123435 3403379 := bstep (se 1 (by rfl) ⟨2552534, by rfl⟩ : syracuseStep 3403379 = 5105069) B5105069
theorem B2268919 : Blo 2123435 2268919 := bstep (se 1 (by rfl) ⟨1701689, by rfl⟩ : syracuseStep 2268919 = 3403379) B3403379
theorem B3025225 : Blo 2123435 3025225 := bstep (se 2 (by rfl) ⟨1134459, by rfl⟩ : syracuseStep 3025225 = 2268919) B2268919
theorem B4033633 : Blo 2123435 4033633 := bstep (se 2 (by rfl) ⟨1512612, by rfl⟩ : syracuseStep 4033633 = 3025225) B3025225
theorem B5378177 : Blo 2123435 5378177 := bstep (se 2 (by rfl) ⟨2016816, by rfl⟩ : syracuseStep 5378177 = 4033633) B4033633
theorem B3585451 : Blo 2123435 3585451 := bstep (se 1 (by rfl) ⟨2689088, by rfl⟩ : syracuseStep 3585451 = 5378177) B5378177
theorem B4780601 : Blo 2123435 4780601 := bstep (se 2 (by rfl) ⟨1792725, by rfl⟩ : syracuseStep 4780601 = 3585451) B3585451
theorem B3187067 : Blo 2123435 3187067 := bstep (se 1 (by rfl) ⟨2390300, by rfl⟩ : syracuseStep 3187067 = 4780601) B4780601
theorem B2124711 : Blo 2123435 2124711 := bstep (se 1 (by rfl) ⟨1593533, by rfl⟩ : syracuseStep 2124711 = 3187067) B3187067
theorem B2390305 : Blo 2123435 2390305 := bbase (se 2 (by rfl) ⟨896364, by rfl⟩ : syracuseStep 2390305 = 1792729) (by norm_num)
theorem B3187073 : Blo 2123435 3187073 := bstep (se 2 (by rfl) ⟨1195152, by rfl⟩ : syracuseStep 3187073 = 2390305) B2390305
theorem B2124715 : Blo 2123435 2124715 := bstep (se 1 (by rfl) ⟨1593536, by rfl⟩ : syracuseStep 2124715 = 3187073) B3187073
theorem B5378197 : Blo 2123435 5378197 := bbase (se 6 (by rfl) ⟨126051, by rfl⟩ : syracuseStep 5378197 = 252103) (by norm_num)
theorem B7170929 : Blo 2123435 7170929 := bstep (se 2 (by rfl) ⟨2689098, by rfl⟩ : syracuseStep 7170929 = 5378197) B5378197
theorem B4780619 : Blo 2123435 4780619 := bstep (se 1 (by rfl) ⟨3585464, by rfl⟩ : syracuseStep 4780619 = 7170929) B7170929
theorem B3187079 : Blo 2123435 3187079 := bstep (se 1 (by rfl) ⟨2390309, by rfl⟩ : syracuseStep 3187079 = 4780619) B4780619
theorem B2124719 : Blo 2123435 2124719 := bstep (se 1 (by rfl) ⟨1593539, by rfl⟩ : syracuseStep 2124719 = 3187079) B3187079
theorem B3187085 : Blo 2123435 3187085 := bbase (se 3 (by rfl) ⟨597578, by rfl⟩ : syracuseStep 3187085 = 1195157) (by norm_num)
theorem B2124723 : Blo 2123435 2124723 := bstep (se 1 (by rfl) ⟨1593542, by rfl⟩ : syracuseStep 2124723 = 3187085) B3187085
theorem B4780637 : Blo 2123435 4780637 := bbase (se 3 (by rfl) ⟨896369, by rfl⟩ : syracuseStep 4780637 = 1792739) (by norm_num)
theorem B3187091 : Blo 2123435 3187091 := bstep (se 1 (by rfl) ⟨2390318, by rfl⟩ : syracuseStep 3187091 = 4780637) B4780637
theorem B2124727 : Blo 2123435 2124727 := bstep (se 1 (by rfl) ⟨1593545, by rfl⟩ : syracuseStep 2124727 = 3187091) B3187091
theorem B3585485 : Blo 2123435 3585485 := bbase (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) (by norm_num)
theorem B2390323 : Blo 2123435 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B3187097 : Blo 2123435 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B2124731 : Blo 2123435 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B25550165 : Blo 2123435 25550165 := bbase (se 11 (by rfl) ⟨18713, by rfl⟩ : syracuseStep 25550165 = 37427) (by norm_num)
theorem B17033443 : Blo 2123435 17033443 := bstep (se 1 (by rfl) ⟨12775082, by rfl⟩ : syracuseStep 17033443 = 25550165) B25550165
theorem B90845029 : Blo 2123435 90845029 := bstep (se 4 (by rfl) ⟨8516721, by rfl⟩ : syracuseStep 90845029 = 17033443) B17033443
theorem B484506821 : Blo 2123435 484506821 := bstep (se 4 (by rfl) ⟨45422514, by rfl⟩ : syracuseStep 484506821 = 90845029) B90845029
theorem B323004547 : Blo 2123435 323004547 := bstep (se 1 (by rfl) ⟨242253410, by rfl⟩ : syracuseStep 323004547 = 484506821) B484506821
theorem B430672729 : Blo 2123435 430672729 := bstep (se 2 (by rfl) ⟨161502273, by rfl⟩ : syracuseStep 430672729 = 323004547) B323004547
theorem B574230305 : Blo 2123435 574230305 := bstep (se 2 (by rfl) ⟨215336364, by rfl⟩ : syracuseStep 574230305 = 430672729) B430672729
theorem B382820203 : Blo 2123435 382820203 := bstep (se 1 (by rfl) ⟨287115152, by rfl⟩ : syracuseStep 382820203 = 574230305) B574230305
theorem B510426937 : Blo 2123435 510426937 := bstep (se 2 (by rfl) ⟨191410101, by rfl⟩ : syracuseStep 510426937 = 382820203) B382820203
theorem B680569249 : Blo 2123435 680569249 := bstep (se 2 (by rfl) ⟨255213468, by rfl⟩ : syracuseStep 680569249 = 510426937) B510426937
theorem B907425665 : Blo 2123435 907425665 := bstep (se 2 (by rfl) ⟨340284624, by rfl⟩ : syracuseStep 907425665 = 680569249) B680569249
theorem B604950443 : Blo 2123435 604950443 := bstep (se 1 (by rfl) ⟨453712832, by rfl⟩ : syracuseStep 604950443 = 907425665) B907425665
theorem B403300295 : Blo 2123435 403300295 := bstep (se 1 (by rfl) ⟨302475221, by rfl⟩ : syracuseStep 403300295 = 604950443) B604950443
theorem B268866863 : Blo 2123435 268866863 := bstep (se 1 (by rfl) ⟨201650147, by rfl⟩ : syracuseStep 268866863 = 403300295) B403300295
theorem B179244575 : Blo 2123435 179244575 := bstep (se 1 (by rfl) ⟨134433431, by rfl⟩ : syracuseStep 179244575 = 268866863) B268866863
theorem B119496383 : Blo 2123435 119496383 := bstep (se 1 (by rfl) ⟨89622287, by rfl⟩ : syracuseStep 119496383 = 179244575) B179244575
theorem B79664255 : Blo 2123435 79664255 := bstep (se 1 (by rfl) ⟨59748191, by rfl⟩ : syracuseStep 79664255 = 119496383) B119496383
theorem B53109503 : Blo 2123435 53109503 := bstep (se 1 (by rfl) ⟨39832127, by rfl⟩ : syracuseStep 53109503 = 79664255) B79664255
theorem B35406335 : Blo 2123435 35406335 := bstep (se 1 (by rfl) ⟨26554751, by rfl⟩ : syracuseStep 35406335 = 53109503) B53109503
theorem B23604223 : Blo 2123435 23604223 := bstep (se 1 (by rfl) ⟨17703167, by rfl⟩ : syracuseStep 23604223 = 35406335) B35406335
theorem B31472297 : Blo 2123435 31472297 := bstep (se 2 (by rfl) ⟨11802111, by rfl⟩ : syracuseStep 31472297 = 23604223) B23604223
theorem B20981531 : Blo 2123435 20981531 := bstep (se 1 (by rfl) ⟨15736148, by rfl⟩ : syracuseStep 20981531 = 31472297) B31472297
theorem B13987687 : Blo 2123435 13987687 := bstep (se 1 (by rfl) ⟨10490765, by rfl⟩ : syracuseStep 13987687 = 20981531) B20981531
theorem B18650249 : Blo 2123435 18650249 := bstep (se 2 (by rfl) ⟨6993843, by rfl⟩ : syracuseStep 18650249 = 13987687) B13987687
theorem B12433499 : Blo 2123435 12433499 := bstep (se 1 (by rfl) ⟨9325124, by rfl⟩ : syracuseStep 12433499 = 18650249) B18650249
theorem B8288999 : Blo 2123435 8288999 := bstep (se 1 (by rfl) ⟨6216749, by rfl⟩ : syracuseStep 8288999 = 12433499) B12433499
theorem B5525999 : Blo 2123435 5525999 := bstep (se 1 (by rfl) ⟨4144499, by rfl⟩ : syracuseStep 5525999 = 8288999) B8288999
theorem B3683999 : Blo 2123435 3683999 := bstep (se 1 (by rfl) ⟨2762999, by rfl⟩ : syracuseStep 3683999 = 5525999) B5525999
theorem B9823997 : Blo 2123435 9823997 := bstep (se 3 (by rfl) ⟨1841999, by rfl⟩ : syracuseStep 9823997 = 3683999) B3683999
theorem B6549331 : Blo 2123435 6549331 := bstep (se 1 (by rfl) ⟨4911998, by rfl⟩ : syracuseStep 6549331 = 9823997) B9823997
theorem B8732441 : Blo 2123435 8732441 := bstep (se 2 (by rfl) ⟨3274665, by rfl⟩ : syracuseStep 8732441 = 6549331) B6549331
theorem B5821627 : Blo 2123435 5821627 := bstep (se 1 (by rfl) ⟨4366220, by rfl⟩ : syracuseStep 5821627 = 8732441) B8732441
theorem B7762169 : Blo 2123435 7762169 := bstep (se 2 (by rfl) ⟨2910813, by rfl⟩ : syracuseStep 7762169 = 5821627) B5821627
theorem B5174779 : Blo 2123435 5174779 := bstep (se 1 (by rfl) ⟨3881084, by rfl⟩ : syracuseStep 5174779 = 7762169) B7762169
theorem B6899705 : Blo 2123435 6899705 := bstep (se 2 (by rfl) ⟨2587389, by rfl⟩ : syracuseStep 6899705 = 5174779) B5174779
theorem B4599803 : Blo 2123435 4599803 := bstep (se 1 (by rfl) ⟨3449852, by rfl⟩ : syracuseStep 4599803 = 6899705) B6899705
theorem B3066535 : Blo 2123435 3066535 := bstep (se 1 (by rfl) ⟨2299901, by rfl⟩ : syracuseStep 3066535 = 4599803) B4599803
theorem B4088713 : Blo 2123435 4088713 := bstep (se 2 (by rfl) ⟨1533267, by rfl⟩ : syracuseStep 4088713 = 3066535) B3066535
theorem B5451617 : Blo 2123435 5451617 := bstep (se 2 (by rfl) ⟨2044356, by rfl⟩ : syracuseStep 5451617 = 4088713) B4088713
theorem B3634411 : Blo 2123435 3634411 := bstep (se 1 (by rfl) ⟨2725808, by rfl⟩ : syracuseStep 3634411 = 5451617) B5451617
theorem B4845881 : Blo 2123435 4845881 := bstep (se 2 (by rfl) ⟨1817205, by rfl⟩ : syracuseStep 4845881 = 3634411) B3634411
theorem B3230587 : Blo 2123435 3230587 := bstep (se 1 (by rfl) ⟨2422940, by rfl⟩ : syracuseStep 3230587 = 4845881) B4845881
theorem B17229797 : Blo 2123435 17229797 := bstep (se 4 (by rfl) ⟨1615293, by rfl⟩ : syracuseStep 17229797 = 3230587) B3230587
theorem B11486531 : Blo 2123435 11486531 := bstep (se 1 (by rfl) ⟨8614898, by rfl⟩ : syracuseStep 11486531 = 17229797) B17229797
theorem B7657687 : Blo 2123435 7657687 := bstep (se 1 (by rfl) ⟨5743265, by rfl⟩ : syracuseStep 7657687 = 11486531) B11486531
theorem B10210249 : Blo 2123435 10210249 := bstep (se 2 (by rfl) ⟨3828843, by rfl⟩ : syracuseStep 10210249 = 7657687) B7657687
theorem B13613665 : Blo 2123435 13613665 := bstep (se 2 (by rfl) ⟨5105124, by rfl⟩ : syracuseStep 13613665 = 10210249) B10210249
theorem B18151553 : Blo 2123435 18151553 := bstep (se 2 (by rfl) ⟨6806832, by rfl⟩ : syracuseStep 18151553 = 13613665) B13613665
theorem B12101035 : Blo 2123435 12101035 := bstep (se 1 (by rfl) ⟨9075776, by rfl⟩ : syracuseStep 12101035 = 18151553) B18151553
theorem B16134713 : Blo 2123435 16134713 := bstep (se 2 (by rfl) ⟨6050517, by rfl⟩ : syracuseStep 16134713 = 12101035) B12101035
theorem B10756475 : Blo 2123435 10756475 := bstep (se 1 (by rfl) ⟨8067356, by rfl⟩ : syracuseStep 10756475 = 16134713) B16134713
theorem B7170983 : Blo 2123435 7170983 := bstep (se 1 (by rfl) ⟨5378237, by rfl⟩ : syracuseStep 7170983 = 10756475) B10756475
theorem B4780655 : Blo 2123435 4780655 := bstep (se 1 (by rfl) ⟨3585491, by rfl⟩ : syracuseStep 4780655 = 7170983) B7170983
theorem B3187103 : Blo 2123435 3187103 := bstep (se 1 (by rfl) ⟨2390327, by rfl⟩ : syracuseStep 3187103 = 4780655) B4780655
theorem B2124735 : Blo 2123435 2124735 := bstep (se 1 (by rfl) ⟨1593551, by rfl⟩ : syracuseStep 2124735 = 3187103) B3187103
theorem B3187109 : Blo 2123435 3187109 := bbase (se 4 (by rfl) ⟨298791, by rfl⟩ : syracuseStep 3187109 = 597583) (by norm_num)
theorem B2124739 : Blo 2123435 2124739 := bstep (se 1 (by rfl) ⟨1593554, by rfl⟩ : syracuseStep 2124739 = 3187109) B3187109
theorem B2689129 : Blo 2123435 2689129 := bbase (se 2 (by rfl) ⟨1008423, by rfl⟩ : syracuseStep 2689129 = 2016847) (by norm_num)
theorem B3585505 : Blo 2123435 3585505 := bstep (se 2 (by rfl) ⟨1344564, by rfl⟩ : syracuseStep 3585505 = 2689129) B2689129
theorem B4780673 : Blo 2123435 4780673 := bstep (se 2 (by rfl) ⟨1792752, by rfl⟩ : syracuseStep 4780673 = 3585505) B3585505
theorem B3187115 : Blo 2123435 3187115 := bstep (se 1 (by rfl) ⟨2390336, by rfl⟩ : syracuseStep 3187115 = 4780673) B4780673
theorem B2124743 : Blo 2123435 2124743 := bstep (se 1 (by rfl) ⟨1593557, by rfl⟩ : syracuseStep 2124743 = 3187115) B3187115
theorem B2390341 : Blo 2123435 2390341 := bbase (se 4 (by rfl) ⟨224094, by rfl⟩ : syracuseStep 2390341 = 448189) (by norm_num)
theorem B3187121 : Blo 2123435 3187121 := bstep (se 2 (by rfl) ⟨1195170, by rfl⟩ : syracuseStep 3187121 = 2390341) B2390341
theorem B2124747 : Blo 2123435 2124747 := bstep (se 1 (by rfl) ⟨1593560, by rfl⟩ : syracuseStep 2124747 = 3187121) B3187121
theorem B4033709 : Blo 2123435 4033709 := bbase (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) (by norm_num)
theorem B2689139 : Blo 2123435 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B7171037 : Blo 2123435 7171037 := bstep (se 3 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 7171037 = 2689139) B2689139
theorem B4780691 : Blo 2123435 4780691 := bstep (se 1 (by rfl) ⟨3585518, by rfl⟩ : syracuseStep 4780691 = 7171037) B7171037
theorem B3187127 : Blo 2123435 3187127 := bstep (se 1 (by rfl) ⟨2390345, by rfl⟩ : syracuseStep 3187127 = 4780691) B4780691
theorem B2124751 : Blo 2123435 2124751 := bstep (se 1 (by rfl) ⟨1593563, by rfl⟩ : syracuseStep 2124751 = 3187127) B3187127
theorem B3187133 : Blo 2123435 3187133 := bbase (se 3 (by rfl) ⟨597587, by rfl⟩ : syracuseStep 3187133 = 1195175) (by norm_num)
theorem B2124755 : Blo 2123435 2124755 := bstep (se 1 (by rfl) ⟨1593566, by rfl⟩ : syracuseStep 2124755 = 3187133) B3187133
theorem B4780709 : Blo 2123435 4780709 := bbase (se 4 (by rfl) ⟨448191, by rfl⟩ : syracuseStep 4780709 = 896383) (by norm_num)
theorem B3187139 : Blo 2123435 3187139 := bstep (se 1 (by rfl) ⟨2390354, by rfl⟩ : syracuseStep 3187139 = 4780709) B4780709
theorem B2124759 : Blo 2123435 2124759 := bstep (se 1 (by rfl) ⟨1593569, by rfl⟩ : syracuseStep 2124759 = 3187139) B3187139
theorem B5378309 : Blo 2123435 5378309 := bbase (se 4 (by rfl) ⟨504216, by rfl⟩ : syracuseStep 5378309 = 1008433) (by norm_num)
theorem B3585539 : Blo 2123435 3585539 := bstep (se 1 (by rfl) ⟨2689154, by rfl⟩ : syracuseStep 3585539 = 5378309) B5378309
theorem B2390359 : Blo 2123435 2390359 := bstep (se 1 (by rfl) ⟨1792769, by rfl⟩ : syracuseStep 2390359 = 3585539) B3585539
theorem B3187145 : Blo 2123435 3187145 := bstep (se 2 (by rfl) ⟨1195179, by rfl⟩ : syracuseStep 3187145 = 2390359) B2390359
theorem B2124763 : Blo 2123435 2124763 := bstep (se 1 (by rfl) ⟨1593572, by rfl⟩ : syracuseStep 2124763 = 3187145) B3187145
theorem B4537957 : Blo 2123435 4537957 := bbase (se 4 (by rfl) ⟨425433, by rfl⟩ : syracuseStep 4537957 = 850867) (by norm_num)
theorem B6050609 : Blo 2123435 6050609 := bstep (se 2 (by rfl) ⟨2268978, by rfl⟩ : syracuseStep 6050609 = 4537957) B4537957
theorem B4033739 : Blo 2123435 4033739 := bstep (se 1 (by rfl) ⟨3025304, by rfl⟩ : syracuseStep 4033739 = 6050609) B6050609
theorem B10756637 : Blo 2123435 10756637 := bstep (se 3 (by rfl) ⟨2016869, by rfl⟩ : syracuseStep 10756637 = 4033739) B4033739
theorem B7171091 : Blo 2123435 7171091 := bstep (se 1 (by rfl) ⟨5378318, by rfl⟩ : syracuseStep 7171091 = 10756637) B10756637
theorem B4780727 : Blo 2123435 4780727 := bstep (se 1 (by rfl) ⟨3585545, by rfl⟩ : syracuseStep 4780727 = 7171091) B7171091
theorem B3187151 : Blo 2123435 3187151 := bstep (se 1 (by rfl) ⟨2390363, by rfl⟩ : syracuseStep 3187151 = 4780727) B4780727
theorem B2124767 : Blo 2123435 2124767 := bstep (se 1 (by rfl) ⟨1593575, by rfl⟩ : syracuseStep 2124767 = 3187151) B3187151
theorem B3187157 : Blo 2123435 3187157 := bbase (se 7 (by rfl) ⟨37349, by rfl⟩ : syracuseStep 3187157 = 74699) (by norm_num)
theorem B2124771 : Blo 2123435 2124771 := bstep (se 1 (by rfl) ⟨1593578, by rfl⟩ : syracuseStep 2124771 = 3187157) B3187157
theorem B8067509 : Blo 2123435 8067509 := bbase (se 5 (by rfl) ⟨378164, by rfl⟩ : syracuseStep 8067509 = 756329) (by norm_num)
theorem B5378339 : Blo 2123435 5378339 := bstep (se 1 (by rfl) ⟨4033754, by rfl⟩ : syracuseStep 5378339 = 8067509) B8067509
theorem B3585559 : Blo 2123435 3585559 := bstep (se 1 (by rfl) ⟨2689169, by rfl⟩ : syracuseStep 3585559 = 5378339) B5378339
theorem B4780745 : Blo 2123435 4780745 := bstep (se 2 (by rfl) ⟨1792779, by rfl⟩ : syracuseStep 4780745 = 3585559) B3585559
theorem B3187163 : Blo 2123435 3187163 := bstep (se 1 (by rfl) ⟨2390372, by rfl⟩ : syracuseStep 3187163 = 4780745) B4780745
theorem B2124775 : Blo 2123435 2124775 := bstep (se 1 (by rfl) ⟨1593581, by rfl⟩ : syracuseStep 2124775 = 3187163) B3187163
theorem B2390377 : Blo 2123435 2390377 := bbase (se 2 (by rfl) ⟨896391, by rfl⟩ : syracuseStep 2390377 = 1792783) (by norm_num)
theorem B3187169 : Blo 2123435 3187169 := bstep (se 2 (by rfl) ⟨1195188, by rfl⟩ : syracuseStep 3187169 = 2390377) B2390377
theorem B2124779 : Blo 2123435 2124779 := bstep (se 1 (by rfl) ⟨1593584, by rfl⟩ : syracuseStep 2124779 = 3187169) B3187169
theorem B7657861 : Blo 2123435 7657861 := bbase (se 4 (by rfl) ⟨717924, by rfl⟩ : syracuseStep 7657861 = 1435849) (by norm_num)
theorem B10210481 : Blo 2123435 10210481 := bstep (se 2 (by rfl) ⟨3828930, by rfl⟩ : syracuseStep 10210481 = 7657861) B7657861
theorem B6806987 : Blo 2123435 6806987 := bstep (se 1 (by rfl) ⟨5105240, by rfl⟩ : syracuseStep 6806987 = 10210481) B10210481
theorem B4537991 : Blo 2123435 4537991 := bstep (se 1 (by rfl) ⟨3403493, by rfl⟩ : syracuseStep 4537991 = 6806987) B6806987
theorem B12101309 : Blo 2123435 12101309 := bstep (se 3 (by rfl) ⟨2268995, by rfl⟩ : syracuseStep 12101309 = 4537991) B4537991
theorem B8067539 : Blo 2123435 8067539 := bstep (se 1 (by rfl) ⟨6050654, by rfl⟩ : syracuseStep 8067539 = 12101309) B12101309
theorem B5378359 : Blo 2123435 5378359 := bstep (se 1 (by rfl) ⟨4033769, by rfl⟩ : syracuseStep 5378359 = 8067539) B8067539
theorem B7171145 : Blo 2123435 7171145 := bstep (se 2 (by rfl) ⟨2689179, by rfl⟩ : syracuseStep 7171145 = 5378359) B5378359
theorem B4780763 : Blo 2123435 4780763 := bstep (se 1 (by rfl) ⟨3585572, by rfl⟩ : syracuseStep 4780763 = 7171145) B7171145
theorem B3187175 : Blo 2123435 3187175 := bstep (se 1 (by rfl) ⟨2390381, by rfl⟩ : syracuseStep 3187175 = 4780763) B4780763
theorem B2124783 : Blo 2123435 2124783 := bstep (se 1 (by rfl) ⟨1593587, by rfl⟩ : syracuseStep 2124783 = 3187175) B3187175
theorem B3187181 : Blo 2123435 3187181 := bbase (se 3 (by rfl) ⟨597596, by rfl⟩ : syracuseStep 3187181 = 1195193) (by norm_num)
theorem B2124787 : Blo 2123435 2124787 := bstep (se 1 (by rfl) ⟨1593590, by rfl⟩ : syracuseStep 2124787 = 3187181) B3187181
theorem B4780781 : Blo 2123435 4780781 := bbase (se 3 (by rfl) ⟨896396, by rfl⟩ : syracuseStep 4780781 = 1792793) (by norm_num)
theorem B3187187 : Blo 2123435 3187187 := bstep (se 1 (by rfl) ⟨2390390, by rfl⟩ : syracuseStep 3187187 = 4780781) B4780781
theorem B2124791 : Blo 2123435 2124791 := bstep (se 1 (by rfl) ⟨1593593, by rfl⟩ : syracuseStep 2124791 = 3187187) B3187187
theorem B2269009 : Blo 2123435 2269009 := bbase (se 2 (by rfl) ⟨850878, by rfl⟩ : syracuseStep 2269009 = 1701757) (by norm_num)
theorem B3025345 : Blo 2123435 3025345 := bstep (se 2 (by rfl) ⟨1134504, by rfl⟩ : syracuseStep 3025345 = 2269009) B2269009
theorem B4033793 : Blo 2123435 4033793 := bstep (se 2 (by rfl) ⟨1512672, by rfl⟩ : syracuseStep 4033793 = 3025345) B3025345
theorem B2689195 : Blo 2123435 2689195 := bstep (se 1 (by rfl) ⟨2016896, by rfl⟩ : syracuseStep 2689195 = 4033793) B4033793
theorem B3585593 : Blo 2123435 3585593 := bstep (se 2 (by rfl) ⟨1344597, by rfl⟩ : syracuseStep 3585593 = 2689195) B2689195
theorem B2390395 : Blo 2123435 2390395 := bstep (se 1 (by rfl) ⟨1792796, by rfl⟩ : syracuseStep 2390395 = 3585593) B3585593
theorem B3187193 : Blo 2123435 3187193 := bstep (se 2 (by rfl) ⟨1195197, by rfl⟩ : syracuseStep 3187193 = 2390395) B2390395
theorem B2124795 : Blo 2123435 2124795 := bstep (se 1 (by rfl) ⟨1593596, by rfl⟩ : syracuseStep 2124795 = 3187193) B3187193
theorem B5601557 : Blo 2123435 5601557 := bbase (se 6 (by rfl) ⟨131286, by rfl⟩ : syracuseStep 5601557 = 262573) (by norm_num)
theorem B3734371 : Blo 2123435 3734371 := bstep (se 1 (by rfl) ⟨2800778, by rfl⟩ : syracuseStep 3734371 = 5601557) B5601557
theorem B4979161 : Blo 2123435 4979161 := bstep (se 2 (by rfl) ⟨1867185, by rfl⟩ : syracuseStep 4979161 = 3734371) B3734371
theorem B26555525 : Blo 2123435 26555525 := bstep (se 4 (by rfl) ⟨2489580, by rfl⟩ : syracuseStep 26555525 = 4979161) B4979161
theorem B17703683 : Blo 2123435 17703683 := bstep (se 1 (by rfl) ⟨13277762, by rfl⟩ : syracuseStep 17703683 = 26555525) B26555525
theorem B11802455 : Blo 2123435 11802455 := bstep (se 1 (by rfl) ⟨8851841, by rfl⟩ : syracuseStep 11802455 = 17703683) B17703683
theorem B7868303 : Blo 2123435 7868303 := bstep (se 1 (by rfl) ⟨5901227, by rfl⟩ : syracuseStep 7868303 = 11802455) B11802455
theorem B5245535 : Blo 2123435 5245535 := bstep (se 1 (by rfl) ⟨3934151, by rfl⟩ : syracuseStep 5245535 = 7868303) B7868303
theorem B3497023 : Blo 2123435 3497023 := bstep (se 1 (by rfl) ⟨2622767, by rfl⟩ : syracuseStep 3497023 = 5245535) B5245535
theorem B18650789 : Blo 2123435 18650789 := bstep (se 4 (by rfl) ⟨1748511, by rfl⟩ : syracuseStep 18650789 = 3497023) B3497023
theorem B12433859 : Blo 2123435 12433859 := bstep (se 1 (by rfl) ⟨9325394, by rfl⟩ : syracuseStep 12433859 = 18650789) B18650789
theorem B8289239 : Blo 2123435 8289239 := bstep (se 1 (by rfl) ⟨6216929, by rfl⟩ : syracuseStep 8289239 = 12433859) B12433859
theorem B22104637 : Blo 2123435 22104637 := bstep (se 3 (by rfl) ⟨4144619, by rfl⟩ : syracuseStep 22104637 = 8289239) B8289239
theorem B117891397 : Blo 2123435 117891397 := bstep (se 4 (by rfl) ⟨11052318, by rfl⟩ : syracuseStep 117891397 = 22104637) B22104637
theorem B157188529 : Blo 2123435 157188529 := bstep (se 2 (by rfl) ⟨58945698, by rfl⟩ : syracuseStep 157188529 = 117891397) B117891397
theorem B209584705 : Blo 2123435 209584705 := bstep (se 2 (by rfl) ⟨78594264, by rfl⟩ : syracuseStep 209584705 = 157188529) B157188529
theorem B279446273 : Blo 2123435 279446273 := bstep (se 2 (by rfl) ⟨104792352, by rfl⟩ : syracuseStep 279446273 = 209584705) B209584705
theorem B186297515 : Blo 2123435 186297515 := bstep (se 1 (by rfl) ⟨139723136, by rfl⟩ : syracuseStep 186297515 = 279446273) B279446273
theorem B124198343 : Blo 2123435 124198343 := bstep (se 1 (by rfl) ⟨93148757, by rfl⟩ : syracuseStep 124198343 = 186297515) B186297515
theorem B82798895 : Blo 2123435 82798895 := bstep (se 1 (by rfl) ⟨62099171, by rfl⟩ : syracuseStep 82798895 = 124198343) B124198343
theorem B220797053 : Blo 2123435 220797053 := bstep (se 3 (by rfl) ⟨41399447, by rfl⟩ : syracuseStep 220797053 = 82798895) B82798895
theorem B147198035 : Blo 2123435 147198035 := bstep (se 1 (by rfl) ⟨110398526, by rfl⟩ : syracuseStep 147198035 = 220797053) B220797053
theorem B98132023 : Blo 2123435 98132023 := bstep (se 1 (by rfl) ⟨73599017, by rfl⟩ : syracuseStep 98132023 = 147198035) B147198035
theorem B130842697 : Blo 2123435 130842697 := bstep (se 2 (by rfl) ⟨49066011, by rfl⟩ : syracuseStep 130842697 = 98132023) B98132023
theorem B174456929 : Blo 2123435 174456929 := bstep (se 2 (by rfl) ⟨65421348, by rfl⟩ : syracuseStep 174456929 = 130842697) B130842697
theorem B116304619 : Blo 2123435 116304619 := bstep (se 1 (by rfl) ⟨87228464, by rfl⟩ : syracuseStep 116304619 = 174456929) B174456929
theorem B155072825 : Blo 2123435 155072825 := bstep (se 2 (by rfl) ⟨58152309, by rfl⟩ : syracuseStep 155072825 = 116304619) B116304619
theorem B103381883 : Blo 2123435 103381883 := bstep (se 1 (by rfl) ⟨77536412, by rfl⟩ : syracuseStep 103381883 = 155072825) B155072825
theorem B68921255 : Blo 2123435 68921255 := bstep (se 1 (by rfl) ⟨51690941, by rfl⟩ : syracuseStep 68921255 = 103381883) B103381883
theorem B45947503 : Blo 2123435 45947503 := bstep (se 1 (by rfl) ⟨34460627, by rfl⟩ : syracuseStep 45947503 = 68921255) B68921255
theorem B61263337 : Blo 2123435 61263337 := bstep (se 2 (by rfl) ⟨22973751, by rfl⟩ : syracuseStep 61263337 = 45947503) B45947503
theorem B81684449 : Blo 2123435 81684449 := bstep (se 2 (by rfl) ⟨30631668, by rfl⟩ : syracuseStep 81684449 = 61263337) B61263337
theorem B54456299 : Blo 2123435 54456299 := bstep (se 1 (by rfl) ⟨40842224, by rfl⟩ : syracuseStep 54456299 = 81684449) B81684449
theorem B36304199 : Blo 2123435 36304199 := bstep (se 1 (by rfl) ⟨27228149, by rfl⟩ : syracuseStep 36304199 = 54456299) B54456299
theorem B24202799 : Blo 2123435 24202799 := bstep (se 1 (by rfl) ⟨18152099, by rfl⟩ : syracuseStep 24202799 = 36304199) B36304199
theorem B16135199 : Blo 2123435 16135199 := bstep (se 1 (by rfl) ⟨12101399, by rfl⟩ : syracuseStep 16135199 = 24202799) B24202799
theorem B10756799 : Blo 2123435 10756799 := bstep (se 1 (by rfl) ⟨8067599, by rfl⟩ : syracuseStep 10756799 = 16135199) B16135199
theorem B7171199 : Blo 2123435 7171199 := bstep (se 1 (by rfl) ⟨5378399, by rfl⟩ : syracuseStep 7171199 = 10756799) B10756799
theorem B4780799 : Blo 2123435 4780799 := bstep (se 1 (by rfl) ⟨3585599, by rfl⟩ : syracuseStep 4780799 = 7171199) B7171199
theorem B3187199 : Blo 2123435 3187199 := bstep (se 1 (by rfl) ⟨2390399, by rfl⟩ : syracuseStep 3187199 = 4780799) B4780799
theorem B2124799 : Blo 2123435 2124799 := bstep (se 1 (by rfl) ⟨1593599, by rfl⟩ : syracuseStep 2124799 = 3187199) B3187199
theorem B3187205 : Blo 2123435 3187205 := bbase (se 4 (by rfl) ⟨298800, by rfl⟩ : syracuseStep 3187205 = 597601) (by norm_num)
theorem B2124803 : Blo 2123435 2124803 := bstep (se 1 (by rfl) ⟨1593602, by rfl⟩ : syracuseStep 2124803 = 3187205) B3187205
theorem B3585613 : Blo 2123435 3585613 := bbase (se 3 (by rfl) ⟨672302, by rfl⟩ : syracuseStep 3585613 = 1344605) (by norm_num)
theorem B4780817 : Blo 2123435 4780817 := bstep (se 2 (by rfl) ⟨1792806, by rfl⟩ : syracuseStep 4780817 = 3585613) B3585613
theorem B3187211 : Blo 2123435 3187211 := bstep (se 1 (by rfl) ⟨2390408, by rfl⟩ : syracuseStep 3187211 = 4780817) B4780817
theorem B2124807 : Blo 2123435 2124807 := bstep (se 1 (by rfl) ⟨1593605, by rfl⟩ : syracuseStep 2124807 = 3187211) B3187211
theorem B2390413 : Blo 2123435 2390413 := bbase (se 3 (by rfl) ⟨448202, by rfl⟩ : syracuseStep 2390413 = 896405) (by norm_num)
theorem B3187217 : Blo 2123435 3187217 := bstep (se 2 (by rfl) ⟨1195206, by rfl⟩ : syracuseStep 3187217 = 2390413) B2390413
theorem B2124811 : Blo 2123435 2124811 := bstep (se 1 (by rfl) ⟨1593608, by rfl⟩ : syracuseStep 2124811 = 3187217) B3187217
theorem B7171253 : Blo 2123435 7171253 := bbase (se 5 (by rfl) ⟨336152, by rfl⟩ : syracuseStep 7171253 = 672305) (by norm_num)
theorem B4780835 : Blo 2123435 4780835 := bstep (se 1 (by rfl) ⟨3585626, by rfl⟩ : syracuseStep 4780835 = 7171253) B7171253
theorem B3187223 : Blo 2123435 3187223 := bstep (se 1 (by rfl) ⟨2390417, by rfl⟩ : syracuseStep 3187223 = 4780835) B4780835
theorem B2124815 : Blo 2123435 2124815 := bstep (se 1 (by rfl) ⟨1593611, by rfl⟩ : syracuseStep 2124815 = 3187223) B3187223
theorem B3187229 : Blo 2123435 3187229 := bbase (se 3 (by rfl) ⟨597605, by rfl⟩ : syracuseStep 3187229 = 1195211) (by norm_num)
theorem B2124819 : Blo 2123435 2124819 := bstep (se 1 (by rfl) ⟨1593614, by rfl⟩ : syracuseStep 2124819 = 3187229) B3187229
theorem B4780853 : Blo 2123435 4780853 := bbase (se 5 (by rfl) ⟨224102, by rfl⟩ : syracuseStep 4780853 = 448205) (by norm_num)
theorem B3187235 : Blo 2123435 3187235 := bstep (se 1 (by rfl) ⟨2390426, by rfl⟩ : syracuseStep 3187235 = 4780853) B4780853
theorem B2124823 : Blo 2123435 2124823 := bstep (se 1 (by rfl) ⟨1593617, by rfl⟩ : syracuseStep 2124823 = 3187235) B3187235
theorem B10210693 : Blo 2123435 10210693 := bbase (se 4 (by rfl) ⟨957252, by rfl⟩ : syracuseStep 10210693 = 1914505) (by norm_num)
theorem B13614257 : Blo 2123435 13614257 := bstep (se 2 (by rfl) ⟨5105346, by rfl⟩ : syracuseStep 13614257 = 10210693) B10210693
theorem B9076171 : Blo 2123435 9076171 := bstep (se 1 (by rfl) ⟨6807128, by rfl⟩ : syracuseStep 9076171 = 13614257) B13614257
theorem B12101561 : Blo 2123435 12101561 := bstep (se 2 (by rfl) ⟨4538085, by rfl⟩ : syracuseStep 12101561 = 9076171) B9076171
theorem B8067707 : Blo 2123435 8067707 := bstep (se 1 (by rfl) ⟨6050780, by rfl⟩ : syracuseStep 8067707 = 12101561) B12101561
theorem B5378471 : Blo 2123435 5378471 := bstep (se 1 (by rfl) ⟨4033853, by rfl⟩ : syracuseStep 5378471 = 8067707) B8067707
theorem B3585647 : Blo 2123435 3585647 := bstep (se 1 (by rfl) ⟨2689235, by rfl⟩ : syracuseStep 3585647 = 5378471) B5378471
theorem B2390431 : Blo 2123435 2390431 := bstep (se 1 (by rfl) ⟨1792823, by rfl⟩ : syracuseStep 2390431 = 3585647) B3585647
theorem B3187241 : Blo 2123435 3187241 := bstep (se 2 (by rfl) ⟨1195215, by rfl⟩ : syracuseStep 3187241 = 2390431) B2390431
theorem B2124827 : Blo 2123435 2124827 := bstep (se 1 (by rfl) ⟨1593620, by rfl⟩ : syracuseStep 2124827 = 3187241) B3187241
theorem B22974101 : Blo 2123435 22974101 := bbase (se 6 (by rfl) ⟨538455, by rfl⟩ : syracuseStep 22974101 = 1076911) (by norm_num)
theorem B15316067 : Blo 2123435 15316067 := bstep (se 1 (by rfl) ⟨11487050, by rfl⟩ : syracuseStep 15316067 = 22974101) B22974101
theorem B10210711 : Blo 2123435 10210711 := bstep (se 1 (by rfl) ⟨7658033, by rfl⟩ : syracuseStep 10210711 = 15316067) B15316067
theorem B13614281 : Blo 2123435 13614281 := bstep (se 2 (by rfl) ⟨5105355, by rfl⟩ : syracuseStep 13614281 = 10210711) B10210711
theorem B9076187 : Blo 2123435 9076187 := bstep (se 1 (by rfl) ⟨6807140, by rfl⟩ : syracuseStep 9076187 = 13614281) B13614281
theorem B6050791 : Blo 2123435 6050791 := bstep (se 1 (by rfl) ⟨4538093, by rfl⟩ : syracuseStep 6050791 = 9076187) B9076187
theorem B8067721 : Blo 2123435 8067721 := bstep (se 2 (by rfl) ⟨3025395, by rfl⟩ : syracuseStep 8067721 = 6050791) B6050791
theorem B10756961 : Blo 2123435 10756961 := bstep (se 2 (by rfl) ⟨4033860, by rfl⟩ : syracuseStep 10756961 = 8067721) B8067721
theorem B7171307 : Blo 2123435 7171307 := bstep (se 1 (by rfl) ⟨5378480, by rfl⟩ : syracuseStep 7171307 = 10756961) B10756961
theorem B4780871 : Blo 2123435 4780871 := bstep (se 1 (by rfl) ⟨3585653, by rfl⟩ : syracuseStep 4780871 = 7171307) B7171307
theorem B3187247 : Blo 2123435 3187247 := bstep (se 1 (by rfl) ⟨2390435, by rfl⟩ : syracuseStep 3187247 = 4780871) B4780871
theorem B2124831 : Blo 2123435 2124831 := bstep (se 1 (by rfl) ⟨1593623, by rfl⟩ : syracuseStep 2124831 = 3187247) B3187247
theorem B3187253 : Blo 2123435 3187253 := bbase (se 5 (by rfl) ⟨149402, by rfl⟩ : syracuseStep 3187253 = 298805) (by norm_num)
theorem B2124835 : Blo 2123435 2124835 := bstep (se 1 (by rfl) ⟨1593626, by rfl⟩ : syracuseStep 2124835 = 3187253) B3187253
theorem B5378501 : Blo 2123435 5378501 := bbase (se 4 (by rfl) ⟨504234, by rfl⟩ : syracuseStep 5378501 = 1008469) (by norm_num)
theorem B3585667 : Blo 2123435 3585667 := bstep (se 1 (by rfl) ⟨2689250, by rfl⟩ : syracuseStep 3585667 = 5378501) B5378501
theorem B4780889 : Blo 2123435 4780889 := bstep (se 2 (by rfl) ⟨1792833, by rfl⟩ : syracuseStep 4780889 = 3585667) B3585667
theorem B3187259 : Blo 2123435 3187259 := bstep (se 1 (by rfl) ⟨2390444, by rfl⟩ : syracuseStep 3187259 = 4780889) B4780889
theorem B2124839 : Blo 2123435 2124839 := bstep (se 1 (by rfl) ⟨1593629, by rfl⟩ : syracuseStep 2124839 = 3187259) B3187259
theorem B2390449 : Blo 2123435 2390449 := bbase (se 2 (by rfl) ⟨896418, by rfl⟩ : syracuseStep 2390449 = 1792837) (by norm_num)
theorem B3187265 : Blo 2123435 3187265 := bstep (se 2 (by rfl) ⟨1195224, by rfl⟩ : syracuseStep 3187265 = 2390449) B2390449
theorem B2124843 : Blo 2123435 2124843 := bstep (se 1 (by rfl) ⟨1593632, by rfl⟩ : syracuseStep 2124843 = 3187265) B3187265
theorem B6050837 : Blo 2123435 6050837 := bbase (se 6 (by rfl) ⟨141816, by rfl⟩ : syracuseStep 6050837 = 283633) (by norm_num)
theorem B4033891 : Blo 2123435 4033891 := bstep (se 1 (by rfl) ⟨3025418, by rfl⟩ : syracuseStep 4033891 = 6050837) B6050837
theorem B5378521 : Blo 2123435 5378521 := bstep (se 2 (by rfl) ⟨2016945, by rfl⟩ : syracuseStep 5378521 = 4033891) B4033891
theorem B7171361 : Blo 2123435 7171361 := bstep (se 2 (by rfl) ⟨2689260, by rfl⟩ : syracuseStep 7171361 = 5378521) B5378521
theorem B4780907 : Blo 2123435 4780907 := bstep (se 1 (by rfl) ⟨3585680, by rfl⟩ : syracuseStep 4780907 = 7171361) B7171361
theorem B3187271 : Blo 2123435 3187271 := bstep (se 1 (by rfl) ⟨2390453, by rfl⟩ : syracuseStep 3187271 = 4780907) B4780907
theorem B2124847 : Blo 2123435 2124847 := bstep (se 1 (by rfl) ⟨1593635, by rfl⟩ : syracuseStep 2124847 = 3187271) B3187271
theorem B3187277 : Blo 2123435 3187277 := bbase (se 3 (by rfl) ⟨597614, by rfl⟩ : syracuseStep 3187277 = 1195229) (by norm_num)
theorem B2124851 : Blo 2123435 2124851 := bstep (se 1 (by rfl) ⟨1593638, by rfl⟩ : syracuseStep 2124851 = 3187277) B3187277
theorem B4780925 : Blo 2123435 4780925 := bbase (se 3 (by rfl) ⟨896423, by rfl⟩ : syracuseStep 4780925 = 1792847) (by norm_num)
theorem B3187283 : Blo 2123435 3187283 := bstep (se 1 (by rfl) ⟨2390462, by rfl⟩ : syracuseStep 3187283 = 4780925) B4780925
theorem B2124855 : Blo 2123435 2124855 := bstep (se 1 (by rfl) ⟨1593641, by rfl⟩ : syracuseStep 2124855 = 3187283) B3187283
theorem B3585701 : Blo 2123435 3585701 := bbase (se 4 (by rfl) ⟨336159, by rfl⟩ : syracuseStep 3585701 = 672319) (by norm_num)
theorem B2390467 : Blo 2123435 2390467 := bstep (se 1 (by rfl) ⟨1792850, by rfl⟩ : syracuseStep 2390467 = 3585701) B3585701
theorem B3187289 : Blo 2123435 3187289 := bstep (se 2 (by rfl) ⟨1195233, by rfl⟩ : syracuseStep 3187289 = 2390467) B2390467
theorem B2124859 : Blo 2123435 2124859 := bstep (se 1 (by rfl) ⟨1593644, by rfl⟩ : syracuseStep 2124859 = 3187289) B3187289
theorem B2269081 : Blo 2123435 2269081 := bbase (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) (by norm_num)
theorem B3025441 : Blo 2123435 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B16135685 : Blo 2123435 16135685 := bstep (se 4 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 16135685 = 3025441) B3025441
theorem B10757123 : Blo 2123435 10757123 := bstep (se 1 (by rfl) ⟨8067842, by rfl⟩ : syracuseStep 10757123 = 16135685) B16135685
theorem B7171415 : Blo 2123435 7171415 := bstep (se 1 (by rfl) ⟨5378561, by rfl⟩ : syracuseStep 7171415 = 10757123) B10757123
theorem B4780943 : Blo 2123435 4780943 := bstep (se 1 (by rfl) ⟨3585707, by rfl⟩ : syracuseStep 4780943 = 7171415) B7171415
theorem B3187295 : Blo 2123435 3187295 := bstep (se 1 (by rfl) ⟨2390471, by rfl⟩ : syracuseStep 3187295 = 4780943) B4780943
theorem B2124863 : Blo 2123435 2124863 := bstep (se 1 (by rfl) ⟨1593647, by rfl⟩ : syracuseStep 2124863 = 3187295) B3187295
theorem B3187301 : Blo 2123435 3187301 := bbase (se 4 (by rfl) ⟨298809, by rfl⟩ : syracuseStep 3187301 = 597619) (by norm_num)
theorem B2124867 : Blo 2123435 2124867 := bstep (se 1 (by rfl) ⟨1593650, by rfl⟩ : syracuseStep 2124867 = 3187301) B3187301
theorem B3025453 : Blo 2123435 3025453 := bbase (se 3 (by rfl) ⟨567272, by rfl⟩ : syracuseStep 3025453 = 1134545) (by norm_num)
theorem B4033937 : Blo 2123435 4033937 := bstep (se 2 (by rfl) ⟨1512726, by rfl⟩ : syracuseStep 4033937 = 3025453) B3025453
theorem B2689291 : Blo 2123435 2689291 := bstep (se 1 (by rfl) ⟨2016968, by rfl⟩ : syracuseStep 2689291 = 4033937) B4033937
theorem B3585721 : Blo 2123435 3585721 := bstep (se 2 (by rfl) ⟨1344645, by rfl⟩ : syracuseStep 3585721 = 2689291) B2689291
theorem B4780961 : Blo 2123435 4780961 := bstep (se 2 (by rfl) ⟨1792860, by rfl⟩ : syracuseStep 4780961 = 3585721) B3585721
theorem B3187307 : Blo 2123435 3187307 := bstep (se 1 (by rfl) ⟨2390480, by rfl⟩ : syracuseStep 3187307 = 4780961) B4780961
theorem B2124871 : Blo 2123435 2124871 := bstep (se 1 (by rfl) ⟨1593653, by rfl⟩ : syracuseStep 2124871 = 3187307) B3187307
theorem B2390485 : Blo 2123435 2390485 := bbase (se 7 (by rfl) ⟨28013, by rfl⟩ : syracuseStep 2390485 = 56027) (by norm_num)
theorem B3187313 : Blo 2123435 3187313 := bstep (se 2 (by rfl) ⟨1195242, by rfl⟩ : syracuseStep 3187313 = 2390485) B2390485
theorem B2124875 : Blo 2123435 2124875 := bstep (se 1 (by rfl) ⟨1593656, by rfl⟩ : syracuseStep 2124875 = 3187313) B3187313
theorem B2689301 : Blo 2123435 2689301 := bbase (se 6 (by rfl) ⟨63030, by rfl⟩ : syracuseStep 2689301 = 126061) (by norm_num)
theorem B7171469 : Blo 2123435 7171469 := bstep (se 3 (by rfl) ⟨1344650, by rfl⟩ : syracuseStep 7171469 = 2689301) B2689301
theorem B4780979 : Blo 2123435 4780979 := bstep (se 1 (by rfl) ⟨3585734, by rfl⟩ : syracuseStep 4780979 = 7171469) B7171469
theorem B3187319 : Blo 2123435 3187319 := bstep (se 1 (by rfl) ⟨2390489, by rfl⟩ : syracuseStep 3187319 = 4780979) B4780979
theorem B2124879 : Blo 2123435 2124879 := bstep (se 1 (by rfl) ⟨1593659, by rfl⟩ : syracuseStep 2124879 = 3187319) B3187319
theorem B3187325 : Blo 2123435 3187325 := bbase (se 3 (by rfl) ⟨597623, by rfl⟩ : syracuseStep 3187325 = 1195247) (by norm_num)
theorem B2124883 : Blo 2123435 2124883 := bstep (se 1 (by rfl) ⟨1593662, by rfl⟩ : syracuseStep 2124883 = 3187325) B3187325
theorem B4780997 : Blo 2123435 4780997 := bbase (se 4 (by rfl) ⟨448218, by rfl⟩ : syracuseStep 4780997 = 896437) (by norm_num)
theorem B3187331 : Blo 2123435 3187331 := bstep (se 1 (by rfl) ⟨2390498, by rfl⟩ : syracuseStep 3187331 = 4780997) B4780997
theorem B2124887 : Blo 2123435 2124887 := bstep (se 1 (by rfl) ⟨1593665, by rfl⟩ : syracuseStep 2124887 = 3187331) B3187331
theorem B5105501 : Blo 2123435 5105501 := bbase (se 3 (by rfl) ⟨957281, by rfl⟩ : syracuseStep 5105501 = 1914563) (by norm_num)
theorem B3403667 : Blo 2123435 3403667 := bstep (se 1 (by rfl) ⟨2552750, by rfl⟩ : syracuseStep 3403667 = 5105501) B5105501
theorem B9076445 : Blo 2123435 9076445 := bstep (se 3 (by rfl) ⟨1701833, by rfl⟩ : syracuseStep 9076445 = 3403667) B3403667
theorem B6050963 : Blo 2123435 6050963 := bstep (se 1 (by rfl) ⟨4538222, by rfl⟩ : syracuseStep 6050963 = 9076445) B9076445
theorem B4033975 : Blo 2123435 4033975 := bstep (se 1 (by rfl) ⟨3025481, by rfl⟩ : syracuseStep 4033975 = 6050963) B6050963
theorem B5378633 : Blo 2123435 5378633 := bstep (se 2 (by rfl) ⟨2016987, by rfl⟩ : syracuseStep 5378633 = 4033975) B4033975
theorem B3585755 : Blo 2123435 3585755 := bstep (se 1 (by rfl) ⟨2689316, by rfl⟩ : syracuseStep 3585755 = 5378633) B5378633
theorem B2390503 : Blo 2123435 2390503 := bstep (se 1 (by rfl) ⟨1792877, by rfl⟩ : syracuseStep 2390503 = 3585755) B3585755
theorem B3187337 : Blo 2123435 3187337 := bstep (se 2 (by rfl) ⟨1195251, by rfl⟩ : syracuseStep 3187337 = 2390503) B2390503
theorem B2124891 : Blo 2123435 2124891 := bstep (se 1 (by rfl) ⟨1593668, by rfl⟩ : syracuseStep 2124891 = 3187337) B3187337
theorem B10757285 : Blo 2123435 10757285 := bbase (se 4 (by rfl) ⟨1008495, by rfl⟩ : syracuseStep 10757285 = 2016991) (by norm_num)
theorem B7171523 : Blo 2123435 7171523 := bstep (se 1 (by rfl) ⟨5378642, by rfl⟩ : syracuseStep 7171523 = 10757285) B10757285
theorem B4781015 : Blo 2123435 4781015 := bstep (se 1 (by rfl) ⟨3585761, by rfl⟩ : syracuseStep 4781015 = 7171523) B7171523
theorem B3187343 : Blo 2123435 3187343 := bstep (se 1 (by rfl) ⟨2390507, by rfl⟩ : syracuseStep 3187343 = 4781015) B4781015
theorem B2124895 : Blo 2123435 2124895 := bstep (se 1 (by rfl) ⟨1593671, by rfl⟩ : syracuseStep 2124895 = 3187343) B3187343
theorem B3187349 : Blo 2123435 3187349 := bbase (se 6 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 3187349 = 149407) (by norm_num)
theorem B2124899 : Blo 2123435 2124899 := bstep (se 1 (by rfl) ⟨1593674, by rfl⟩ : syracuseStep 2124899 = 3187349) B3187349
theorem B30633173 : Blo 2123435 30633173 := bbase (se 7 (by rfl) ⟨358982, by rfl⟩ : syracuseStep 30633173 = 717965) (by norm_num)
theorem B20422115 : Blo 2123435 20422115 := bstep (se 1 (by rfl) ⟨15316586, by rfl⟩ : syracuseStep 20422115 = 30633173) B30633173
theorem B13614743 : Blo 2123435 13614743 := bstep (se 1 (by rfl) ⟨10211057, by rfl⟩ : syracuseStep 13614743 = 20422115) B20422115
theorem B9076495 : Blo 2123435 9076495 := bstep (se 1 (by rfl) ⟨6807371, by rfl⟩ : syracuseStep 9076495 = 13614743) B13614743
theorem B12101993 : Blo 2123435 12101993 := bstep (se 2 (by rfl) ⟨4538247, by rfl⟩ : syracuseStep 12101993 = 9076495) B9076495
theorem B8067995 : Blo 2123435 8067995 := bstep (se 1 (by rfl) ⟨6050996, by rfl⟩ : syracuseStep 8067995 = 12101993) B12101993
theorem B5378663 : Blo 2123435 5378663 := bstep (se 1 (by rfl) ⟨4033997, by rfl⟩ : syracuseStep 5378663 = 8067995) B8067995
theorem B3585775 : Blo 2123435 3585775 := bstep (se 1 (by rfl) ⟨2689331, by rfl⟩ : syracuseStep 3585775 = 5378663) B5378663
theorem B4781033 : Blo 2123435 4781033 := bstep (se 2 (by rfl) ⟨1792887, by rfl⟩ : syracuseStep 4781033 = 3585775) B3585775
theorem B3187355 : Blo 2123435 3187355 := bstep (se 1 (by rfl) ⟨2390516, by rfl⟩ : syracuseStep 3187355 = 4781033) B4781033
theorem B2124903 : Blo 2123435 2124903 := bstep (se 1 (by rfl) ⟨1593677, by rfl⟩ : syracuseStep 2124903 = 3187355) B3187355
theorem B2390521 : Blo 2123435 2390521 := bbase (se 2 (by rfl) ⟨896445, by rfl⟩ : syracuseStep 2390521 = 1792891) (by norm_num)
theorem B3187361 : Blo 2123435 3187361 := bstep (se 2 (by rfl) ⟨1195260, by rfl⟩ : syracuseStep 3187361 = 2390521) B2390521
theorem B2124907 : Blo 2123435 2124907 := bstep (se 1 (by rfl) ⟨1593680, by rfl⟩ : syracuseStep 2124907 = 3187361) B3187361
theorem B6807397 : Blo 2123435 6807397 := bbase (se 4 (by rfl) ⟨638193, by rfl⟩ : syracuseStep 6807397 = 1276387) (by norm_num)
theorem B9076529 : Blo 2123435 9076529 := bstep (se 2 (by rfl) ⟨3403698, by rfl⟩ : syracuseStep 9076529 = 6807397) B6807397
theorem B6051019 : Blo 2123435 6051019 := bstep (se 1 (by rfl) ⟨4538264, by rfl⟩ : syracuseStep 6051019 = 9076529) B9076529
theorem B8068025 : Blo 2123435 8068025 := bstep (se 2 (by rfl) ⟨3025509, by rfl⟩ : syracuseStep 8068025 = 6051019) B6051019
theorem B5378683 : Blo 2123435 5378683 := bstep (se 1 (by rfl) ⟨4034012, by rfl⟩ : syracuseStep 5378683 = 8068025) B8068025
theorem B7171577 : Blo 2123435 7171577 := bstep (se 2 (by rfl) ⟨2689341, by rfl⟩ : syracuseStep 7171577 = 5378683) B5378683
theorem B4781051 : Blo 2123435 4781051 := bstep (se 1 (by rfl) ⟨3585788, by rfl⟩ : syracuseStep 4781051 = 7171577) B7171577
theorem B3187367 : Blo 2123435 3187367 := bstep (se 1 (by rfl) ⟨2390525, by rfl⟩ : syracuseStep 3187367 = 4781051) B4781051
theorem B2124911 : Blo 2123435 2124911 := bstep (se 1 (by rfl) ⟨1593683, by rfl⟩ : syracuseStep 2124911 = 3187367) B3187367
theorem B3187373 : Blo 2123435 3187373 := bbase (se 3 (by rfl) ⟨597632, by rfl⟩ : syracuseStep 3187373 = 1195265) (by norm_num)
theorem B2124915 : Blo 2123435 2124915 := bstep (se 1 (by rfl) ⟨1593686, by rfl⟩ : syracuseStep 2124915 = 3187373) B3187373
theorem B4781069 : Blo 2123435 4781069 := bbase (se 3 (by rfl) ⟨896450, by rfl⟩ : syracuseStep 4781069 = 1792901) (by norm_num)
theorem B3187379 : Blo 2123435 3187379 := bstep (se 1 (by rfl) ⟨2390534, by rfl⟩ : syracuseStep 3187379 = 4781069) B4781069
theorem B2124919 : Blo 2123435 2124919 := bstep (se 1 (by rfl) ⟨1593689, by rfl⟩ : syracuseStep 2124919 = 3187379) B3187379
theorem B2689357 : Blo 2123435 2689357 := bbase (se 3 (by rfl) ⟨504254, by rfl⟩ : syracuseStep 2689357 = 1008509) (by norm_num)
theorem B3585809 : Blo 2123435 3585809 := bstep (se 2 (by rfl) ⟨1344678, by rfl⟩ : syracuseStep 3585809 = 2689357) B2689357
theorem B2390539 : Blo 2123435 2390539 := bstep (se 1 (by rfl) ⟨1792904, by rfl⟩ : syracuseStep 2390539 = 3585809) B3585809
theorem B3187385 : Blo 2123435 3187385 := bstep (se 2 (by rfl) ⟨1195269, by rfl⟩ : syracuseStep 3187385 = 2390539) B2390539
theorem B2124923 : Blo 2123435 2124923 := bstep (se 1 (by rfl) ⟨1593692, by rfl⟩ : syracuseStep 2124923 = 3187385) B3187385
theorem B5452109 : Blo 2123435 5452109 := bbase (se 3 (by rfl) ⟨1022270, by rfl⟩ : syracuseStep 5452109 = 2044541) (by norm_num)
theorem B3634739 : Blo 2123435 3634739 := bstep (se 1 (by rfl) ⟨2726054, by rfl⟩ : syracuseStep 3634739 = 5452109) B5452109
theorem B2423159 : Blo 2123435 2423159 := bstep (se 1 (by rfl) ⟨1817369, by rfl⟩ : syracuseStep 2423159 = 3634739) B3634739
theorem B25847029 : Blo 2123435 25847029 := bstep (se 5 (by rfl) ⟨1211579, by rfl⟩ : syracuseStep 25847029 = 2423159) B2423159
theorem B34462705 : Blo 2123435 34462705 := bstep (se 2 (by rfl) ⟨12923514, by rfl⟩ : syracuseStep 34462705 = 25847029) B25847029
theorem B45950273 : Blo 2123435 45950273 := bstep (se 2 (by rfl) ⟨17231352, by rfl⟩ : syracuseStep 45950273 = 34462705) B34462705
theorem B30633515 : Blo 2123435 30633515 := bstep (se 1 (by rfl) ⟨22975136, by rfl⟩ : syracuseStep 30633515 = 45950273) B45950273
theorem B20422343 : Blo 2123435 20422343 := bstep (se 1 (by rfl) ⟨15316757, by rfl⟩ : syracuseStep 20422343 = 30633515) B30633515
theorem B13614895 : Blo 2123435 13614895 := bstep (se 1 (by rfl) ⟨10211171, by rfl⟩ : syracuseStep 13614895 = 20422343) B20422343
theorem B18153193 : Blo 2123435 18153193 := bstep (se 2 (by rfl) ⟨6807447, by rfl⟩ : syracuseStep 18153193 = 13614895) B13614895
theorem B24204257 : Blo 2123435 24204257 := bstep (se 2 (by rfl) ⟨9076596, by rfl⟩ : syracuseStep 24204257 = 18153193) B18153193
theorem B16136171 : Blo 2123435 16136171 := bstep (se 1 (by rfl) ⟨12102128, by rfl⟩ : syracuseStep 16136171 = 24204257) B24204257
theorem B10757447 : Blo 2123435 10757447 := bstep (se 1 (by rfl) ⟨8068085, by rfl⟩ : syracuseStep 10757447 = 16136171) B16136171
theorem B7171631 : Blo 2123435 7171631 := bstep (se 1 (by rfl) ⟨5378723, by rfl⟩ : syracuseStep 7171631 = 10757447) B10757447
theorem B4781087 : Blo 2123435 4781087 := bstep (se 1 (by rfl) ⟨3585815, by rfl⟩ : syracuseStep 4781087 = 7171631) B7171631
theorem B3187391 : Blo 2123435 3187391 := bstep (se 1 (by rfl) ⟨2390543, by rfl⟩ : syracuseStep 3187391 = 4781087) B4781087
theorem B2124927 : Blo 2123435 2124927 := bstep (se 1 (by rfl) ⟨1593695, by rfl⟩ : syracuseStep 2124927 = 3187391) B3187391
theorem B3187397 : Blo 2123435 3187397 := bbase (se 4 (by rfl) ⟨298818, by rfl⟩ : syracuseStep 3187397 = 597637) (by norm_num)
theorem B2124931 : Blo 2123435 2124931 := bstep (se 1 (by rfl) ⟨1593698, by rfl⟩ : syracuseStep 2124931 = 3187397) B3187397
theorem B3585829 : Blo 2123435 3585829 := bbase (se 4 (by rfl) ⟨336171, by rfl⟩ : syracuseStep 3585829 = 672343) (by norm_num)
theorem B4781105 : Blo 2123435 4781105 := bstep (se 2 (by rfl) ⟨1792914, by rfl⟩ : syracuseStep 4781105 = 3585829) B3585829
theorem B3187403 : Blo 2123435 3187403 := bstep (se 1 (by rfl) ⟨2390552, by rfl⟩ : syracuseStep 3187403 = 4781105) B4781105
theorem B2124935 : Blo 2123435 2124935 := bstep (se 1 (by rfl) ⟨1593701, by rfl⟩ : syracuseStep 2124935 = 3187403) B3187403
theorem B2390557 : Blo 2123435 2390557 := bbase (se 3 (by rfl) ⟨448229, by rfl⟩ : syracuseStep 2390557 = 896459) (by norm_num)
theorem B3187409 : Blo 2123435 3187409 := bstep (se 2 (by rfl) ⟨1195278, by rfl⟩ : syracuseStep 3187409 = 2390557) B2390557
theorem B2124939 : Blo 2123435 2124939 := bstep (se 1 (by rfl) ⟨1593704, by rfl⟩ : syracuseStep 2124939 = 3187409) B3187409
theorem B7171685 : Blo 2123435 7171685 := bbase (se 4 (by rfl) ⟨672345, by rfl⟩ : syracuseStep 7171685 = 1344691) (by norm_num)
theorem B4781123 : Blo 2123435 4781123 := bstep (se 1 (by rfl) ⟨3585842, by rfl⟩ : syracuseStep 4781123 = 7171685) B7171685
theorem B3187415 : Blo 2123435 3187415 := bstep (se 1 (by rfl) ⟨2390561, by rfl⟩ : syracuseStep 3187415 = 4781123) B4781123
theorem B2124943 : Blo 2123435 2124943 := bstep (se 1 (by rfl) ⟨1593707, by rfl⟩ : syracuseStep 2124943 = 3187415) B3187415
theorem B3187421 : Blo 2123435 3187421 := bbase (se 3 (by rfl) ⟨597641, by rfl⟩ : syracuseStep 3187421 = 1195283) (by norm_num)
theorem B2124947 : Blo 2123435 2124947 := bstep (se 1 (by rfl) ⟨1593710, by rfl⟩ : syracuseStep 2124947 = 3187421) B3187421
theorem B4781141 : Blo 2123435 4781141 := bbase (se 8 (by rfl) ⟨28014, by rfl⟩ : syracuseStep 4781141 = 56029) (by norm_num)
theorem B3187427 : Blo 2123435 3187427 := bstep (se 1 (by rfl) ⟨2390570, by rfl⟩ : syracuseStep 3187427 = 4781141) B4781141
theorem B2124951 : Blo 2123435 2124951 := bstep (se 1 (by rfl) ⟨1593713, by rfl⟩ : syracuseStep 2124951 = 3187427) B3187427
theorem B3634789 : Blo 2123435 3634789 := bbase (se 4 (by rfl) ⟨340761, by rfl⟩ : syracuseStep 3634789 = 681523) (by norm_num)
theorem B4846385 : Blo 2123435 4846385 := bstep (se 2 (by rfl) ⟨1817394, by rfl⟩ : syracuseStep 4846385 = 3634789) B3634789
theorem B3230923 : Blo 2123435 3230923 := bstep (se 1 (by rfl) ⟨2423192, by rfl⟩ : syracuseStep 3230923 = 4846385) B4846385
theorem B4307897 : Blo 2123435 4307897 := bstep (se 2 (by rfl) ⟨1615461, by rfl⟩ : syracuseStep 4307897 = 3230923) B3230923
theorem B2871931 : Blo 2123435 2871931 := bstep (se 1 (by rfl) ⟨2153948, by rfl⟩ : syracuseStep 2871931 = 4307897) B4307897
theorem B3829241 : Blo 2123435 3829241 := bstep (se 2 (by rfl) ⟨1435965, by rfl⟩ : syracuseStep 3829241 = 2871931) B2871931
theorem B10211309 : Blo 2123435 10211309 := bstep (se 3 (by rfl) ⟨1914620, by rfl⟩ : syracuseStep 10211309 = 3829241) B3829241
theorem B6807539 : Blo 2123435 6807539 := bstep (se 1 (by rfl) ⟨5105654, by rfl⟩ : syracuseStep 6807539 = 10211309) B10211309
theorem B4538359 : Blo 2123435 4538359 := bstep (se 1 (by rfl) ⟨3403769, by rfl⟩ : syracuseStep 4538359 = 6807539) B6807539
theorem B6051145 : Blo 2123435 6051145 := bstep (se 2 (by rfl) ⟨2269179, by rfl⟩ : syracuseStep 6051145 = 4538359) B4538359
theorem B8068193 : Blo 2123435 8068193 := bstep (se 2 (by rfl) ⟨3025572, by rfl⟩ : syracuseStep 8068193 = 6051145) B6051145
theorem B5378795 : Blo 2123435 5378795 := bstep (se 1 (by rfl) ⟨4034096, by rfl⟩ : syracuseStep 5378795 = 8068193) B8068193
theorem B3585863 : Blo 2123435 3585863 := bstep (se 1 (by rfl) ⟨2689397, by rfl⟩ : syracuseStep 3585863 = 5378795) B5378795
theorem B2390575 : Blo 2123435 2390575 := bstep (se 1 (by rfl) ⟨1792931, by rfl⟩ : syracuseStep 2390575 = 3585863) B3585863
theorem B3187433 : Blo 2123435 3187433 := bstep (se 2 (by rfl) ⟨1195287, by rfl⟩ : syracuseStep 3187433 = 2390575) B2390575
theorem B2124955 : Blo 2123435 2124955 := bstep (se 1 (by rfl) ⟨1593716, by rfl⟩ : syracuseStep 2124955 = 3187433) B3187433
theorem B3108701 : Blo 2123435 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B8289869 : Blo 2123435 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B22106317 : Blo 2123435 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B29475089 : Blo 2123435 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B19650059 : Blo 2123435 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B13100039 : Blo 2123435 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B8733359 : Blo 2123435 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B5822239 : Blo 2123435 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B7762985 : Blo 2123435 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B5175323 : Blo 2123435 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B3450215 : Blo 2123435 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B2300143 : Blo 2123435 2300143 := bstep (se 1 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 2300143 = 3450215) B3450215
theorem B3066857 : Blo 2123435 3066857 := bstep (se 2 (by rfl) ⟨1150071, by rfl⟩ : syracuseStep 3066857 = 2300143) B2300143
theorem B32713141 : Blo 2123435 32713141 := bstep (se 5 (by rfl) ⟨1533428, by rfl⟩ : syracuseStep 32713141 = 3066857) B3066857
theorem B43617521 : Blo 2123435 43617521 := bstep (se 2 (by rfl) ⟨16356570, by rfl⟩ : syracuseStep 43617521 = 32713141) B32713141
theorem B29078347 : Blo 2123435 29078347 := bstep (se 1 (by rfl) ⟨21808760, by rfl⟩ : syracuseStep 29078347 = 43617521) B43617521
theorem B38771129 : Blo 2123435 38771129 := bstep (se 2 (by rfl) ⟨14539173, by rfl⟩ : syracuseStep 38771129 = 29078347) B29078347
theorem B25847419 : Blo 2123435 25847419 := bstep (se 1 (by rfl) ⟨19385564, by rfl⟩ : syracuseStep 25847419 = 38771129) B38771129
theorem B34463225 : Blo 2123435 34463225 := bstep (se 2 (by rfl) ⟨12923709, by rfl⟩ : syracuseStep 34463225 = 25847419) B25847419
theorem B22975483 : Blo 2123435 22975483 := bstep (se 1 (by rfl) ⟨17231612, by rfl⟩ : syracuseStep 22975483 = 34463225) B34463225
theorem B30633977 : Blo 2123435 30633977 := bstep (se 2 (by rfl) ⟨11487741, by rfl⟩ : syracuseStep 30633977 = 22975483) B22975483
theorem B20422651 : Blo 2123435 20422651 := bstep (se 1 (by rfl) ⟨15316988, by rfl⟩ : syracuseStep 20422651 = 30633977) B30633977
theorem B27230201 : Blo 2123435 27230201 := bstep (se 2 (by rfl) ⟨10211325, by rfl⟩ : syracuseStep 27230201 = 20422651) B20422651
theorem B18153467 : Blo 2123435 18153467 := bstep (se 1 (by rfl) ⟨13615100, by rfl⟩ : syracuseStep 18153467 = 27230201) B27230201
theorem B12102311 : Blo 2123435 12102311 := bstep (se 1 (by rfl) ⟨9076733, by rfl⟩ : syracuseStep 12102311 = 18153467) B18153467
theorem B8068207 : Blo 2123435 8068207 := bstep (se 1 (by rfl) ⟨6051155, by rfl⟩ : syracuseStep 8068207 = 12102311) B12102311
theorem B10757609 : Blo 2123435 10757609 := bstep (se 2 (by rfl) ⟨4034103, by rfl⟩ : syracuseStep 10757609 = 8068207) B8068207
theorem B7171739 : Blo 2123435 7171739 := bstep (se 1 (by rfl) ⟨5378804, by rfl⟩ : syracuseStep 7171739 = 10757609) B10757609
theorem B4781159 : Blo 2123435 4781159 := bstep (se 1 (by rfl) ⟨3585869, by rfl⟩ : syracuseStep 4781159 = 7171739) B7171739
theorem B3187439 : Blo 2123435 3187439 := bstep (se 1 (by rfl) ⟨2390579, by rfl⟩ : syracuseStep 3187439 = 4781159) B4781159
theorem B2124959 : Blo 2123435 2124959 := bstep (se 1 (by rfl) ⟨1593719, by rfl⟩ : syracuseStep 2124959 = 3187439) B3187439
theorem B3187445 : Blo 2123435 3187445 := bbase (se 5 (by rfl) ⟨149411, by rfl⟩ : syracuseStep 3187445 = 298823) (by norm_num)
theorem B2124963 : Blo 2123435 2124963 := bstep (se 1 (by rfl) ⟨1593722, by rfl⟩ : syracuseStep 2124963 = 3187445) B3187445
theorem B3230941 : Blo 2123435 3230941 := bbase (se 3 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 3230941 = 1211603) (by norm_num)
theorem B4307921 : Blo 2123435 4307921 := bstep (se 2 (by rfl) ⟨1615470, by rfl⟩ : syracuseStep 4307921 = 3230941) B3230941
theorem B2871947 : Blo 2123435 2871947 := bstep (se 1 (by rfl) ⟨2153960, by rfl⟩ : syracuseStep 2871947 = 4307921) B4307921
theorem B7658525 : Blo 2123435 7658525 := bstep (se 3 (by rfl) ⟨1435973, by rfl⟩ : syracuseStep 7658525 = 2871947) B2871947
theorem B5105683 : Blo 2123435 5105683 := bstep (se 1 (by rfl) ⟨3829262, by rfl⟩ : syracuseStep 5105683 = 7658525) B7658525
theorem B6807577 : Blo 2123435 6807577 := bstep (se 2 (by rfl) ⟨2552841, by rfl⟩ : syracuseStep 6807577 = 5105683) B5105683
theorem B9076769 : Blo 2123435 9076769 := bstep (se 2 (by rfl) ⟨3403788, by rfl⟩ : syracuseStep 9076769 = 6807577) B6807577
theorem B6051179 : Blo 2123435 6051179 := bstep (se 1 (by rfl) ⟨4538384, by rfl⟩ : syracuseStep 6051179 = 9076769) B9076769
theorem B4034119 : Blo 2123435 4034119 := bstep (se 1 (by rfl) ⟨3025589, by rfl⟩ : syracuseStep 4034119 = 6051179) B6051179
theorem B5378825 : Blo 2123435 5378825 := bstep (se 2 (by rfl) ⟨2017059, by rfl⟩ : syracuseStep 5378825 = 4034119) B4034119
theorem B3585883 : Blo 2123435 3585883 := bstep (se 1 (by rfl) ⟨2689412, by rfl⟩ : syracuseStep 3585883 = 5378825) B5378825
theorem B4781177 : Blo 2123435 4781177 := bstep (se 2 (by rfl) ⟨1792941, by rfl⟩ : syracuseStep 4781177 = 3585883) B3585883
theorem B3187451 : Blo 2123435 3187451 := bstep (se 1 (by rfl) ⟨2390588, by rfl⟩ : syracuseStep 3187451 = 4781177) B4781177
theorem B2124967 : Blo 2123435 2124967 := bstep (se 1 (by rfl) ⟨1593725, by rfl⟩ : syracuseStep 2124967 = 3187451) B3187451
theorem B2390593 : Blo 2123435 2390593 := bbase (se 2 (by rfl) ⟨896472, by rfl⟩ : syracuseStep 2390593 = 1792945) (by norm_num)
theorem B3187457 : Blo 2123435 3187457 := bstep (se 2 (by rfl) ⟨1195296, by rfl⟩ : syracuseStep 3187457 = 2390593) B2390593
theorem B2124971 : Blo 2123435 2124971 := bstep (se 1 (by rfl) ⟨1593728, by rfl⟩ : syracuseStep 2124971 = 3187457) B3187457
theorem B5378845 : Blo 2123435 5378845 := bbase (se 3 (by rfl) ⟨1008533, by rfl⟩ : syracuseStep 5378845 = 2017067) (by norm_num)
theorem B7171793 : Blo 2123435 7171793 := bstep (se 2 (by rfl) ⟨2689422, by rfl⟩ : syracuseStep 7171793 = 5378845) B5378845
theorem B4781195 : Blo 2123435 4781195 := bstep (se 1 (by rfl) ⟨3585896, by rfl⟩ : syracuseStep 4781195 = 7171793) B7171793
theorem B3187463 : Blo 2123435 3187463 := bstep (se 1 (by rfl) ⟨2390597, by rfl⟩ : syracuseStep 3187463 = 4781195) B4781195
theorem B2124975 : Blo 2123435 2124975 := bstep (se 1 (by rfl) ⟨1593731, by rfl⟩ : syracuseStep 2124975 = 3187463) B3187463
theorem B3187469 : Blo 2123435 3187469 := bbase (se 3 (by rfl) ⟨597650, by rfl⟩ : syracuseStep 3187469 = 1195301) (by norm_num)
theorem B2124979 : Blo 2123435 2124979 := bstep (se 1 (by rfl) ⟨1593734, by rfl⟩ : syracuseStep 2124979 = 3187469) B3187469
theorem B4781213 : Blo 2123435 4781213 := bbase (se 3 (by rfl) ⟨896477, by rfl⟩ : syracuseStep 4781213 = 1792955) (by norm_num)
theorem B3187475 : Blo 2123435 3187475 := bstep (se 1 (by rfl) ⟨2390606, by rfl⟩ : syracuseStep 3187475 = 4781213) B4781213
theorem B2124983 : Blo 2123435 2124983 := bstep (se 1 (by rfl) ⟨1593737, by rfl⟩ : syracuseStep 2124983 = 3187475) B3187475
theorem B3585917 : Blo 2123435 3585917 := bbase (se 3 (by rfl) ⟨672359, by rfl⟩ : syracuseStep 3585917 = 1344719) (by norm_num)
theorem B2390611 : Blo 2123435 2390611 := bstep (se 1 (by rfl) ⟨1792958, by rfl⟩ : syracuseStep 2390611 = 3585917) B3585917
theorem B3187481 : Blo 2123435 3187481 := bstep (se 2 (by rfl) ⟨1195305, by rfl⟩ : syracuseStep 3187481 = 2390611) B2390611
theorem B2124987 : Blo 2123435 2124987 := bstep (se 1 (by rfl) ⟨1593740, by rfl⟩ : syracuseStep 2124987 = 3187481) B3187481
theorem B6807653 : Blo 2123435 6807653 := bbase (se 4 (by rfl) ⟨638217, by rfl⟩ : syracuseStep 6807653 = 1276435) (by norm_num)
theorem B4538435 : Blo 2123435 4538435 := bstep (se 1 (by rfl) ⟨3403826, by rfl⟩ : syracuseStep 4538435 = 6807653) B6807653
theorem B12102493 : Blo 2123435 12102493 := bstep (se 3 (by rfl) ⟨2269217, by rfl⟩ : syracuseStep 12102493 = 4538435) B4538435
theorem B16136657 : Blo 2123435 16136657 := bstep (se 2 (by rfl) ⟨6051246, by rfl⟩ : syracuseStep 16136657 = 12102493) B12102493
theorem B10757771 : Blo 2123435 10757771 := bstep (se 1 (by rfl) ⟨8068328, by rfl⟩ : syracuseStep 10757771 = 16136657) B16136657
theorem B7171847 : Blo 2123435 7171847 := bstep (se 1 (by rfl) ⟨5378885, by rfl⟩ : syracuseStep 7171847 = 10757771) B10757771
theorem B4781231 : Blo 2123435 4781231 := bstep (se 1 (by rfl) ⟨3585923, by rfl⟩ : syracuseStep 4781231 = 7171847) B7171847
theorem B3187487 : Blo 2123435 3187487 := bstep (se 1 (by rfl) ⟨2390615, by rfl⟩ : syracuseStep 3187487 = 4781231) B4781231
theorem B2124991 : Blo 2123435 2124991 := bstep (se 1 (by rfl) ⟨1593743, by rfl⟩ : syracuseStep 2124991 = 3187487) B3187487
theorem B3187493 : Blo 2123435 3187493 := bbase (se 4 (by rfl) ⟨298827, by rfl⟩ : syracuseStep 3187493 = 597655) (by norm_num)
theorem B2124995 : Blo 2123435 2124995 := bstep (se 1 (by rfl) ⟨1593746, by rfl⟩ : syracuseStep 2124995 = 3187493) B3187493
theorem B2689453 : Blo 2123435 2689453 := bbase (se 3 (by rfl) ⟨504272, by rfl⟩ : syracuseStep 2689453 = 1008545) (by norm_num)
theorem B3585937 : Blo 2123435 3585937 := bstep (se 2 (by rfl) ⟨1344726, by rfl⟩ : syracuseStep 3585937 = 2689453) B2689453
theorem B4781249 : Blo 2123435 4781249 := bstep (se 2 (by rfl) ⟨1792968, by rfl⟩ : syracuseStep 4781249 = 3585937) B3585937
theorem B3187499 : Blo 2123435 3187499 := bstep (se 1 (by rfl) ⟨2390624, by rfl⟩ : syracuseStep 3187499 = 4781249) B4781249
theorem B2124999 : Blo 2123435 2124999 := bstep (se 1 (by rfl) ⟨1593749, by rfl⟩ : syracuseStep 2124999 = 3187499) B3187499
theorem B2390629 : Blo 2123435 2390629 := bbase (se 4 (by rfl) ⟨224121, by rfl⟩ : syracuseStep 2390629 = 448243) (by norm_num)
theorem B3187505 : Blo 2123435 3187505 := bstep (se 2 (by rfl) ⟨1195314, by rfl⟩ : syracuseStep 3187505 = 2390629) B2390629
theorem B2125003 : Blo 2123435 2125003 := bstep (se 1 (by rfl) ⟨1593752, by rfl⟩ : syracuseStep 2125003 = 3187505) B3187505
theorem B3403853 : Blo 2123435 3403853 := bbase (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) (by norm_num)
theorem B2269235 : Blo 2123435 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B6051293 : Blo 2123435 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B4034195 : Blo 2123435 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B2689463 : Blo 2123435 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B7171901 : Blo 2123435 7171901 := bstep (se 3 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 7171901 = 2689463) B2689463
theorem B4781267 : Blo 2123435 4781267 := bstep (se 1 (by rfl) ⟨3585950, by rfl⟩ : syracuseStep 4781267 = 7171901) B7171901
theorem B3187511 : Blo 2123435 3187511 := bstep (se 1 (by rfl) ⟨2390633, by rfl⟩ : syracuseStep 3187511 = 4781267) B4781267
theorem B2125007 : Blo 2123435 2125007 := bstep (se 1 (by rfl) ⟨1593755, by rfl⟩ : syracuseStep 2125007 = 3187511) B3187511
theorem B3187517 : Blo 2123435 3187517 := bbase (se 3 (by rfl) ⟨597659, by rfl⟩ : syracuseStep 3187517 = 1195319) (by norm_num)
theorem B2125011 : Blo 2123435 2125011 := bstep (se 1 (by rfl) ⟨1593758, by rfl⟩ : syracuseStep 2125011 = 3187517) B3187517
theorem B4781285 : Blo 2123435 4781285 := bbase (se 4 (by rfl) ⟨448245, by rfl⟩ : syracuseStep 4781285 = 896491) (by norm_num)
theorem B3187523 : Blo 2123435 3187523 := bstep (se 1 (by rfl) ⟨2390642, by rfl⟩ : syracuseStep 3187523 = 4781285) B4781285
theorem B2125015 : Blo 2123435 2125015 := bstep (se 1 (by rfl) ⟨1593761, by rfl⟩ : syracuseStep 2125015 = 3187523) B3187523
theorem B5378957 : Blo 2123435 5378957 := bbase (se 3 (by rfl) ⟨1008554, by rfl⟩ : syracuseStep 5378957 = 2017109) (by norm_num)
theorem B3585971 : Blo 2123435 3585971 := bstep (se 1 (by rfl) ⟨2689478, by rfl⟩ : syracuseStep 3585971 = 5378957) B5378957
theorem B2390647 : Blo 2123435 2390647 := bstep (se 1 (by rfl) ⟨1792985, by rfl⟩ : syracuseStep 2390647 = 3585971) B3585971
theorem B3187529 : Blo 2123435 3187529 := bstep (se 2 (by rfl) ⟨1195323, by rfl⟩ : syracuseStep 3187529 = 2390647) B2390647
theorem B2125019 : Blo 2123435 2125019 := bstep (se 1 (by rfl) ⟨1593764, by rfl⟩ : syracuseStep 2125019 = 3187529) B3187529
theorem B3025669 : Blo 2123435 3025669 := bbase (se 4 (by rfl) ⟨283656, by rfl⟩ : syracuseStep 3025669 = 567313) (by norm_num)
theorem B4034225 : Blo 2123435 4034225 := bstep (se 2 (by rfl) ⟨1512834, by rfl⟩ : syracuseStep 4034225 = 3025669) B3025669
theorem B10757933 : Blo 2123435 10757933 := bstep (se 3 (by rfl) ⟨2017112, by rfl⟩ : syracuseStep 10757933 = 4034225) B4034225
theorem B7171955 : Blo 2123435 7171955 := bstep (se 1 (by rfl) ⟨5378966, by rfl⟩ : syracuseStep 7171955 = 10757933) B10757933
theorem B4781303 : Blo 2123435 4781303 := bstep (se 1 (by rfl) ⟨3585977, by rfl⟩ : syracuseStep 4781303 = 7171955) B7171955
theorem B3187535 : Blo 2123435 3187535 := bstep (se 1 (by rfl) ⟨2390651, by rfl⟩ : syracuseStep 3187535 = 4781303) B4781303
theorem B2125023 : Blo 2123435 2125023 := bstep (se 1 (by rfl) ⟨1593767, by rfl⟩ : syracuseStep 2125023 = 3187535) B3187535
theorem B3187541 : Blo 2123435 3187541 := bbase (se 9 (by rfl) ⟨9338, by rfl⟩ : syracuseStep 3187541 = 18677) (by norm_num)
theorem B2125027 : Blo 2123435 2125027 := bstep (se 1 (by rfl) ⟨1593770, by rfl⟩ : syracuseStep 2125027 = 3187541) B3187541
theorem B5105837 : Blo 2123435 5105837 := bbase (se 3 (by rfl) ⟨957344, by rfl⟩ : syracuseStep 5105837 = 1914689) (by norm_num)
theorem B3403891 : Blo 2123435 3403891 := bstep (se 1 (by rfl) ⟨2552918, by rfl⟩ : syracuseStep 3403891 = 5105837) B5105837
theorem B4538521 : Blo 2123435 4538521 := bstep (se 2 (by rfl) ⟨1701945, by rfl⟩ : syracuseStep 4538521 = 3403891) B3403891
theorem B6051361 : Blo 2123435 6051361 := bstep (se 2 (by rfl) ⟨2269260, by rfl⟩ : syracuseStep 6051361 = 4538521) B4538521
theorem B8068481 : Blo 2123435 8068481 := bstep (se 2 (by rfl) ⟨3025680, by rfl⟩ : syracuseStep 8068481 = 6051361) B6051361
theorem B5378987 : Blo 2123435 5378987 := bstep (se 1 (by rfl) ⟨4034240, by rfl⟩ : syracuseStep 5378987 = 8068481) B8068481
theorem B3585991 : Blo 2123435 3585991 := bstep (se 1 (by rfl) ⟨2689493, by rfl⟩ : syracuseStep 3585991 = 5378987) B5378987
theorem B4781321 : Blo 2123435 4781321 := bstep (se 2 (by rfl) ⟨1792995, by rfl⟩ : syracuseStep 4781321 = 3585991) B3585991
theorem B3187547 : Blo 2123435 3187547 := bstep (se 1 (by rfl) ⟨2390660, by rfl⟩ : syracuseStep 3187547 = 4781321) B4781321
theorem B2125031 : Blo 2123435 2125031 := bstep (se 1 (by rfl) ⟨1593773, by rfl⟩ : syracuseStep 2125031 = 3187547) B3187547
theorem B2390665 : Blo 2123435 2390665 := bbase (se 2 (by rfl) ⟨896499, by rfl⟩ : syracuseStep 2390665 = 1792999) (by norm_num)
theorem B3187553 : Blo 2123435 3187553 := bstep (se 2 (by rfl) ⟨1195332, by rfl⟩ : syracuseStep 3187553 = 2390665) B2390665
theorem B2125035 : Blo 2123435 2125035 := bstep (se 1 (by rfl) ⟨1593776, by rfl⟩ : syracuseStep 2125035 = 3187553) B3187553
theorem B5175517 : Blo 2123435 5175517 := bbase (se 3 (by rfl) ⟨970409, by rfl⟩ : syracuseStep 5175517 = 1940819) (by norm_num)
theorem B6900689 : Blo 2123435 6900689 := bstep (se 2 (by rfl) ⟨2587758, by rfl⟩ : syracuseStep 6900689 = 5175517) B5175517
theorem B4600459 : Blo 2123435 4600459 := bstep (se 1 (by rfl) ⟨3450344, by rfl⟩ : syracuseStep 4600459 = 6900689) B6900689
theorem B24535781 : Blo 2123435 24535781 := bstep (se 4 (by rfl) ⟨2300229, by rfl⟩ : syracuseStep 24535781 = 4600459) B4600459
theorem B16357187 : Blo 2123435 16357187 := bstep (se 1 (by rfl) ⟨12267890, by rfl⟩ : syracuseStep 16357187 = 24535781) B24535781
theorem B10904791 : Blo 2123435 10904791 := bstep (se 1 (by rfl) ⟨8178593, by rfl⟩ : syracuseStep 10904791 = 16357187) B16357187
theorem B14539721 : Blo 2123435 14539721 := bstep (se 2 (by rfl) ⟨5452395, by rfl⟩ : syracuseStep 14539721 = 10904791) B10904791
theorem B38772589 : Blo 2123435 38772589 := bstep (se 3 (by rfl) ⟨7269860, by rfl⟩ : syracuseStep 38772589 = 14539721) B14539721
theorem B51696785 : Blo 2123435 51696785 := bstep (se 2 (by rfl) ⟨19386294, by rfl⟩ : syracuseStep 51696785 = 38772589) B38772589
theorem B34464523 : Blo 2123435 34464523 := bstep (se 1 (by rfl) ⟨25848392, by rfl⟩ : syracuseStep 34464523 = 51696785) B51696785
theorem B45952697 : Blo 2123435 45952697 := bstep (se 2 (by rfl) ⟨17232261, by rfl⟩ : syracuseStep 45952697 = 34464523) B34464523
theorem B30635131 : Blo 2123435 30635131 := bstep (se 1 (by rfl) ⟨22976348, by rfl⟩ : syracuseStep 30635131 = 45952697) B45952697
theorem B40846841 : Blo 2123435 40846841 := bstep (se 2 (by rfl) ⟨15317565, by rfl⟩ : syracuseStep 40846841 = 30635131) B30635131
theorem B27231227 : Blo 2123435 27231227 := bstep (se 1 (by rfl) ⟨20423420, by rfl⟩ : syracuseStep 27231227 = 40846841) B40846841
theorem B18154151 : Blo 2123435 18154151 := bstep (se 1 (by rfl) ⟨13615613, by rfl⟩ : syracuseStep 18154151 = 27231227) B27231227
theorem B12102767 : Blo 2123435 12102767 := bstep (se 1 (by rfl) ⟨9077075, by rfl⟩ : syracuseStep 12102767 = 18154151) B18154151
theorem B8068511 : Blo 2123435 8068511 := bstep (se 1 (by rfl) ⟨6051383, by rfl⟩ : syracuseStep 8068511 = 12102767) B12102767
theorem B5379007 : Blo 2123435 5379007 := bstep (se 1 (by rfl) ⟨4034255, by rfl⟩ : syracuseStep 5379007 = 8068511) B8068511
theorem B7172009 : Blo 2123435 7172009 := bstep (se 2 (by rfl) ⟨2689503, by rfl⟩ : syracuseStep 7172009 = 5379007) B5379007
theorem B4781339 : Blo 2123435 4781339 := bstep (se 1 (by rfl) ⟨3586004, by rfl⟩ : syracuseStep 4781339 = 7172009) B7172009
theorem B3187559 : Blo 2123435 3187559 := bstep (se 1 (by rfl) ⟨2390669, by rfl⟩ : syracuseStep 3187559 = 4781339) B4781339
theorem B2125039 : Blo 2123435 2125039 := bstep (se 1 (by rfl) ⟨1593779, by rfl⟩ : syracuseStep 2125039 = 3187559) B3187559
theorem B3187565 : Blo 2123435 3187565 := bbase (se 3 (by rfl) ⟨597668, by rfl⟩ : syracuseStep 3187565 = 1195337) (by norm_num)
theorem B2125043 : Blo 2123435 2125043 := bstep (se 1 (by rfl) ⟨1593782, by rfl⟩ : syracuseStep 2125043 = 3187565) B3187565
theorem B4781357 : Blo 2123435 4781357 := bbase (se 3 (by rfl) ⟨896504, by rfl⟩ : syracuseStep 4781357 = 1793009) (by norm_num)
theorem B3187571 : Blo 2123435 3187571 := bstep (se 1 (by rfl) ⟨2390678, by rfl⟩ : syracuseStep 3187571 = 4781357) B4781357
theorem B2125047 : Blo 2123435 2125047 := bstep (se 1 (by rfl) ⟨1593785, by rfl⟩ : syracuseStep 2125047 = 3187571) B3187571
theorem B5452429 : Blo 2123435 5452429 := bbase (se 3 (by rfl) ⟨1022330, by rfl⟩ : syracuseStep 5452429 = 2044661) (by norm_num)
theorem B7269905 : Blo 2123435 7269905 := bstep (se 2 (by rfl) ⟨2726214, by rfl⟩ : syracuseStep 7269905 = 5452429) B5452429
theorem B4846603 : Blo 2123435 4846603 := bstep (se 1 (by rfl) ⟨3634952, by rfl⟩ : syracuseStep 4846603 = 7269905) B7269905
theorem B6462137 : Blo 2123435 6462137 := bstep (se 2 (by rfl) ⟨2423301, by rfl⟩ : syracuseStep 6462137 = 4846603) B4846603
theorem B17232365 : Blo 2123435 17232365 := bstep (se 3 (by rfl) ⟨3231068, by rfl⟩ : syracuseStep 17232365 = 6462137) B6462137
theorem B11488243 : Blo 2123435 11488243 := bstep (se 1 (by rfl) ⟨8616182, by rfl⟩ : syracuseStep 11488243 = 17232365) B17232365
theorem B15317657 : Blo 2123435 15317657 := bstep (se 2 (by rfl) ⟨5744121, by rfl⟩ : syracuseStep 15317657 = 11488243) B11488243
theorem B10211771 : Blo 2123435 10211771 := bstep (se 1 (by rfl) ⟨7658828, by rfl⟩ : syracuseStep 10211771 = 15317657) B15317657
theorem B6807847 : Blo 2123435 6807847 := bstep (se 1 (by rfl) ⟨5105885, by rfl⟩ : syracuseStep 6807847 = 10211771) B10211771
theorem B9077129 : Blo 2123435 9077129 := bstep (se 2 (by rfl) ⟨3403923, by rfl⟩ : syracuseStep 9077129 = 6807847) B6807847
theorem B6051419 : Blo 2123435 6051419 := bstep (se 1 (by rfl) ⟨4538564, by rfl⟩ : syracuseStep 6051419 = 9077129) B9077129
theorem B4034279 : Blo 2123435 4034279 := bstep (se 1 (by rfl) ⟨3025709, by rfl⟩ : syracuseStep 4034279 = 6051419) B6051419
theorem B2689519 : Blo 2123435 2689519 := bstep (se 1 (by rfl) ⟨2017139, by rfl⟩ : syracuseStep 2689519 = 4034279) B4034279
theorem B3586025 : Blo 2123435 3586025 := bstep (se 2 (by rfl) ⟨1344759, by rfl⟩ : syracuseStep 3586025 = 2689519) B2689519
theorem B2390683 : Blo 2123435 2390683 := bstep (se 1 (by rfl) ⟨1793012, by rfl⟩ : syracuseStep 2390683 = 3586025) B3586025
theorem B3187577 : Blo 2123435 3187577 := bstep (se 2 (by rfl) ⟨1195341, by rfl⟩ : syracuseStep 3187577 = 2390683) B2390683
theorem B2125051 : Blo 2123435 2125051 := bstep (se 1 (by rfl) ⟨1593788, by rfl⟩ : syracuseStep 2125051 = 3187577) B3187577
theorem B20423573 : Blo 2123435 20423573 := bbase (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) (by norm_num)
theorem B13615715 : Blo 2123435 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B36308573 : Blo 2123435 36308573 := bstep (se 3 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 36308573 = 13615715) B13615715
theorem B24205715 : Blo 2123435 24205715 := bstep (se 1 (by rfl) ⟨18154286, by rfl⟩ : syracuseStep 24205715 = 36308573) B36308573
theorem B16137143 : Blo 2123435 16137143 := bstep (se 1 (by rfl) ⟨12102857, by rfl⟩ : syracuseStep 16137143 = 24205715) B24205715
theorem B10758095 : Blo 2123435 10758095 := bstep (se 1 (by rfl) ⟨8068571, by rfl⟩ : syracuseStep 10758095 = 16137143) B16137143
theorem B7172063 : Blo 2123435 7172063 := bstep (se 1 (by rfl) ⟨5379047, by rfl⟩ : syracuseStep 7172063 = 10758095) B10758095
theorem B4781375 : Blo 2123435 4781375 := bstep (se 1 (by rfl) ⟨3586031, by rfl⟩ : syracuseStep 4781375 = 7172063) B7172063
theorem B3187583 : Blo 2123435 3187583 := bstep (se 1 (by rfl) ⟨2390687, by rfl⟩ : syracuseStep 3187583 = 4781375) B4781375
theorem B2125055 : Blo 2123435 2125055 := bstep (se 1 (by rfl) ⟨1593791, by rfl⟩ : syracuseStep 2125055 = 3187583) B3187583
theorem B3187589 : Blo 2123435 3187589 := bbase (se 4 (by rfl) ⟨298836, by rfl⟩ : syracuseStep 3187589 = 597673) (by norm_num)
theorem B2125059 : Blo 2123435 2125059 := bstep (se 1 (by rfl) ⟨1593794, by rfl⟩ : syracuseStep 2125059 = 3187589) B3187589
theorem B3586045 : Blo 2123435 3586045 := bbase (se 3 (by rfl) ⟨672383, by rfl⟩ : syracuseStep 3586045 = 1344767) (by norm_num)
theorem B4781393 : Blo 2123435 4781393 := bstep (se 2 (by rfl) ⟨1793022, by rfl⟩ : syracuseStep 4781393 = 3586045) B3586045
theorem B3187595 : Blo 2123435 3187595 := bstep (se 1 (by rfl) ⟨2390696, by rfl⟩ : syracuseStep 3187595 = 4781393) B4781393
theorem B2125063 : Blo 2123435 2125063 := bstep (se 1 (by rfl) ⟨1593797, by rfl⟩ : syracuseStep 2125063 = 3187595) B3187595
theorem B2390701 : Blo 2123435 2390701 := bbase (se 3 (by rfl) ⟨448256, by rfl⟩ : syracuseStep 2390701 = 896513) (by norm_num)
theorem B3187601 : Blo 2123435 3187601 := bstep (se 2 (by rfl) ⟨1195350, by rfl⟩ : syracuseStep 3187601 = 2390701) B2390701
theorem B2125067 : Blo 2123435 2125067 := bstep (se 1 (by rfl) ⟨1593800, by rfl⟩ : syracuseStep 2125067 = 3187601) B3187601
theorem B7172117 : Blo 2123435 7172117 := bbase (se 6 (by rfl) ⟨168096, by rfl⟩ : syracuseStep 7172117 = 336193) (by norm_num)
theorem B4781411 : Blo 2123435 4781411 := bstep (se 1 (by rfl) ⟨3586058, by rfl⟩ : syracuseStep 4781411 = 7172117) B7172117
theorem B3187607 : Blo 2123435 3187607 := bstep (se 1 (by rfl) ⟨2390705, by rfl⟩ : syracuseStep 3187607 = 4781411) B4781411
theorem B2125071 : Blo 2123435 2125071 := bstep (se 1 (by rfl) ⟨1593803, by rfl⟩ : syracuseStep 2125071 = 3187607) B3187607
theorem B3187613 : Blo 2123435 3187613 := bbase (se 3 (by rfl) ⟨597677, by rfl⟩ : syracuseStep 3187613 = 1195355) (by norm_num)
theorem B2125075 : Blo 2123435 2125075 := bstep (se 1 (by rfl) ⟨1593806, by rfl⟩ : syracuseStep 2125075 = 3187613) B3187613
theorem B4781429 : Blo 2123435 4781429 := bbase (se 5 (by rfl) ⟨224129, by rfl⟩ : syracuseStep 4781429 = 448259) (by norm_num)
theorem B3187619 : Blo 2123435 3187619 := bstep (se 1 (by rfl) ⟨2390714, by rfl⟩ : syracuseStep 3187619 = 4781429) B4781429
theorem B2125079 : Blo 2123435 2125079 := bstep (se 1 (by rfl) ⟨1593809, by rfl⟩ : syracuseStep 2125079 = 3187619) B3187619
theorem B10351253 : Blo 2123435 10351253 := bbase (se 6 (by rfl) ⟨242607, by rfl⟩ : syracuseStep 10351253 = 485215) (by norm_num)
theorem B6900835 : Blo 2123435 6900835 := bstep (se 1 (by rfl) ⟨5175626, by rfl⟩ : syracuseStep 6900835 = 10351253) B10351253
theorem B9201113 : Blo 2123435 9201113 := bstep (se 2 (by rfl) ⟨3450417, by rfl⟩ : syracuseStep 9201113 = 6900835) B6900835
theorem B6134075 : Blo 2123435 6134075 := bstep (se 1 (by rfl) ⟨4600556, by rfl⟩ : syracuseStep 6134075 = 9201113) B9201113
theorem B4089383 : Blo 2123435 4089383 := bstep (se 1 (by rfl) ⟨3067037, by rfl⟩ : syracuseStep 4089383 = 6134075) B6134075
theorem B2726255 : Blo 2123435 2726255 := bstep (se 1 (by rfl) ⟨2044691, by rfl⟩ : syracuseStep 2726255 = 4089383) B4089383
theorem B7270013 : Blo 2123435 7270013 := bstep (se 3 (by rfl) ⟨1363127, by rfl⟩ : syracuseStep 7270013 = 2726255) B2726255
theorem B19386701 : Blo 2123435 19386701 := bstep (se 3 (by rfl) ⟨3635006, by rfl⟩ : syracuseStep 19386701 = 7270013) B7270013
theorem B12924467 : Blo 2123435 12924467 := bstep (se 1 (by rfl) ⟨9693350, by rfl⟩ : syracuseStep 12924467 = 19386701) B19386701
theorem B8616311 : Blo 2123435 8616311 := bstep (se 1 (by rfl) ⟨6462233, by rfl⟩ : syracuseStep 8616311 = 12924467) B12924467
theorem B5744207 : Blo 2123435 5744207 := bstep (se 1 (by rfl) ⟨4308155, by rfl⟩ : syracuseStep 5744207 = 8616311) B8616311
theorem B15317885 : Blo 2123435 15317885 := bstep (se 3 (by rfl) ⟨2872103, by rfl⟩ : syracuseStep 15317885 = 5744207) B5744207
theorem B10211923 : Blo 2123435 10211923 := bstep (se 1 (by rfl) ⟨7658942, by rfl⟩ : syracuseStep 10211923 = 15317885) B15317885
theorem B13615897 : Blo 2123435 13615897 := bstep (se 2 (by rfl) ⟨5105961, by rfl⟩ : syracuseStep 13615897 = 10211923) B10211923
theorem B18154529 : Blo 2123435 18154529 := bstep (se 2 (by rfl) ⟨6807948, by rfl⟩ : syracuseStep 18154529 = 13615897) B13615897
theorem B12103019 : Blo 2123435 12103019 := bstep (se 1 (by rfl) ⟨9077264, by rfl⟩ : syracuseStep 12103019 = 18154529) B18154529
theorem B8068679 : Blo 2123435 8068679 := bstep (se 1 (by rfl) ⟨6051509, by rfl⟩ : syracuseStep 8068679 = 12103019) B12103019
theorem B5379119 : Blo 2123435 5379119 := bstep (se 1 (by rfl) ⟨4034339, by rfl⟩ : syracuseStep 5379119 = 8068679) B8068679
theorem B3586079 : Blo 2123435 3586079 := bstep (se 1 (by rfl) ⟨2689559, by rfl⟩ : syracuseStep 3586079 = 5379119) B5379119
theorem B2390719 : Blo 2123435 2390719 := bstep (se 1 (by rfl) ⟨1793039, by rfl⟩ : syracuseStep 2390719 = 3586079) B3586079
theorem B3187625 : Blo 2123435 3187625 := bstep (se 2 (by rfl) ⟨1195359, by rfl⟩ : syracuseStep 3187625 = 2390719) B2390719
theorem B2125083 : Blo 2123435 2125083 := bstep (se 1 (by rfl) ⟨1593812, by rfl⟩ : syracuseStep 2125083 = 3187625) B3187625
theorem B8068693 : Blo 2123435 8068693 := bbase (se 8 (by rfl) ⟨47277, by rfl⟩ : syracuseStep 8068693 = 94555) (by norm_num)
theorem B10758257 : Blo 2123435 10758257 := bstep (se 2 (by rfl) ⟨4034346, by rfl⟩ : syracuseStep 10758257 = 8068693) B8068693
theorem B7172171 : Blo 2123435 7172171 := bstep (se 1 (by rfl) ⟨5379128, by rfl⟩ : syracuseStep 7172171 = 10758257) B10758257
theorem B4781447 : Blo 2123435 4781447 := bstep (se 1 (by rfl) ⟨3586085, by rfl⟩ : syracuseStep 4781447 = 7172171) B7172171
theorem B3187631 : Blo 2123435 3187631 := bstep (se 1 (by rfl) ⟨2390723, by rfl⟩ : syracuseStep 3187631 = 4781447) B4781447
theorem B2125087 : Blo 2123435 2125087 := bstep (se 1 (by rfl) ⟨1593815, by rfl⟩ : syracuseStep 2125087 = 3187631) B3187631
theorem B3187637 : Blo 2123435 3187637 := bbase (se 5 (by rfl) ⟨149420, by rfl⟩ : syracuseStep 3187637 = 298841) (by norm_num)
theorem B2125091 : Blo 2123435 2125091 := bstep (se 1 (by rfl) ⟨1593818, by rfl⟩ : syracuseStep 2125091 = 3187637) B3187637
theorem B5379149 : Blo 2123435 5379149 := bbase (se 3 (by rfl) ⟨1008590, by rfl⟩ : syracuseStep 5379149 = 2017181) (by norm_num)
theorem B3586099 : Blo 2123435 3586099 := bstep (se 1 (by rfl) ⟨2689574, by rfl⟩ : syracuseStep 3586099 = 5379149) B5379149
theorem B4781465 : Blo 2123435 4781465 := bstep (se 2 (by rfl) ⟨1793049, by rfl⟩ : syracuseStep 4781465 = 3586099) B3586099
theorem B3187643 : Blo 2123435 3187643 := bstep (se 1 (by rfl) ⟨2390732, by rfl⟩ : syracuseStep 3187643 = 4781465) B4781465
theorem B2125095 : Blo 2123435 2125095 := bstep (se 1 (by rfl) ⟨1593821, by rfl⟩ : syracuseStep 2125095 = 3187643) B3187643
theorem B2390737 : Blo 2123435 2390737 := bbase (se 2 (by rfl) ⟨896526, by rfl⟩ : syracuseStep 2390737 = 1793053) (by norm_num)
theorem B3187649 : Blo 2123435 3187649 := bstep (se 2 (by rfl) ⟨1195368, by rfl⟩ : syracuseStep 3187649 = 2390737) B2390737
theorem B2125099 : Blo 2123435 2125099 := bstep (se 1 (by rfl) ⟨1593824, by rfl⟩ : syracuseStep 2125099 = 3187649) B3187649
theorem B2553005 : Blo 2123435 2553005 := bbase (se 3 (by rfl) ⟨478688, by rfl⟩ : syracuseStep 2553005 = 957377) (by norm_num)
theorem B6808013 : Blo 2123435 6808013 := bstep (se 3 (by rfl) ⟨1276502, by rfl⟩ : syracuseStep 6808013 = 2553005) B2553005
theorem B4538675 : Blo 2123435 4538675 := bstep (se 1 (by rfl) ⟨3404006, by rfl⟩ : syracuseStep 4538675 = 6808013) B6808013
theorem B3025783 : Blo 2123435 3025783 := bstep (se 1 (by rfl) ⟨2269337, by rfl⟩ : syracuseStep 3025783 = 4538675) B4538675
theorem B4034377 : Blo 2123435 4034377 := bstep (se 2 (by rfl) ⟨1512891, by rfl⟩ : syracuseStep 4034377 = 3025783) B3025783
theorem B5379169 : Blo 2123435 5379169 := bstep (se 2 (by rfl) ⟨2017188, by rfl⟩ : syracuseStep 5379169 = 4034377) B4034377
theorem B7172225 : Blo 2123435 7172225 := bstep (se 2 (by rfl) ⟨2689584, by rfl⟩ : syracuseStep 7172225 = 5379169) B5379169
theorem B4781483 : Blo 2123435 4781483 := bstep (se 1 (by rfl) ⟨3586112, by rfl⟩ : syracuseStep 4781483 = 7172225) B7172225
theorem B3187655 : Blo 2123435 3187655 := bstep (se 1 (by rfl) ⟨2390741, by rfl⟩ : syracuseStep 3187655 = 4781483) B4781483
theorem B2125103 : Blo 2123435 2125103 := bstep (se 1 (by rfl) ⟨1593827, by rfl⟩ : syracuseStep 2125103 = 3187655) B3187655
theorem B3187661 : Blo 2123435 3187661 := bbase (se 3 (by rfl) ⟨597686, by rfl⟩ : syracuseStep 3187661 = 1195373) (by norm_num)
theorem B2125107 : Blo 2123435 2125107 := bstep (se 1 (by rfl) ⟨1593830, by rfl⟩ : syracuseStep 2125107 = 3187661) B3187661
theorem B4781501 : Blo 2123435 4781501 := bbase (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) (by norm_num)
theorem B3187667 : Blo 2123435 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B2125111 : Blo 2123435 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B3586133 : Blo 2123435 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B2390755 : Blo 2123435 2390755 := bstep (se 1 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 2390755 = 3586133) B3586133
theorem B3187673 : Blo 2123435 3187673 := bstep (se 2 (by rfl) ⟨1195377, by rfl⟩ : syracuseStep 3187673 = 2390755) B2390755
theorem B2125115 : Blo 2123435 2125115 := bstep (se 1 (by rfl) ⟨1593836, by rfl⟩ : syracuseStep 2125115 = 3187673) B3187673
theorem B4145245 : Blo 2123435 4145245 := bbase (se 3 (by rfl) ⟨777233, by rfl⟩ : syracuseStep 4145245 = 1554467) (by norm_num)
theorem B22107973 : Blo 2123435 22107973 := bstep (se 4 (by rfl) ⟨2072622, by rfl⟩ : syracuseStep 22107973 = 4145245) B4145245
theorem B29477297 : Blo 2123435 29477297 := bstep (se 2 (by rfl) ⟨11053986, by rfl⟩ : syracuseStep 29477297 = 22107973) B22107973
theorem B19651531 : Blo 2123435 19651531 := bstep (se 1 (by rfl) ⟨14738648, by rfl⟩ : syracuseStep 19651531 = 29477297) B29477297
theorem B26202041 : Blo 2123435 26202041 := bstep (se 2 (by rfl) ⟨9825765, by rfl⟩ : syracuseStep 26202041 = 19651531) B19651531
theorem B17468027 : Blo 2123435 17468027 := bstep (se 1 (by rfl) ⟨13101020, by rfl⟩ : syracuseStep 17468027 = 26202041) B26202041
theorem B11645351 : Blo 2123435 11645351 := bstep (se 1 (by rfl) ⟨8734013, by rfl⟩ : syracuseStep 11645351 = 17468027) B17468027
theorem B7763567 : Blo 2123435 7763567 := bstep (se 1 (by rfl) ⟨5822675, by rfl⟩ : syracuseStep 7763567 = 11645351) B11645351
theorem B20702845 : Blo 2123435 20702845 := bstep (se 3 (by rfl) ⟨3881783, by rfl⟩ : syracuseStep 20702845 = 7763567) B7763567
theorem B27603793 : Blo 2123435 27603793 := bstep (se 2 (by rfl) ⟨10351422, by rfl⟩ : syracuseStep 27603793 = 20702845) B20702845
theorem B147220229 : Blo 2123435 147220229 := bstep (se 4 (by rfl) ⟨13801896, by rfl⟩ : syracuseStep 147220229 = 27603793) B27603793
theorem B98146819 : Blo 2123435 98146819 := bstep (se 1 (by rfl) ⟨73610114, by rfl⟩ : syracuseStep 98146819 = 147220229) B147220229
theorem B130862425 : Blo 2123435 130862425 := bstep (se 2 (by rfl) ⟨49073409, by rfl⟩ : syracuseStep 130862425 = 98146819) B98146819
theorem B174483233 : Blo 2123435 174483233 := bstep (se 2 (by rfl) ⟨65431212, by rfl⟩ : syracuseStep 174483233 = 130862425) B130862425
theorem B116322155 : Blo 2123435 116322155 := bstep (se 1 (by rfl) ⟨87241616, by rfl⟩ : syracuseStep 116322155 = 174483233) B174483233
theorem B77548103 : Blo 2123435 77548103 := bstep (se 1 (by rfl) ⟨58161077, by rfl⟩ : syracuseStep 77548103 = 116322155) B116322155
theorem B51698735 : Blo 2123435 51698735 := bstep (se 1 (by rfl) ⟨38774051, by rfl⟩ : syracuseStep 51698735 = 77548103) B77548103
theorem B34465823 : Blo 2123435 34465823 := bstep (se 1 (by rfl) ⟨25849367, by rfl⟩ : syracuseStep 34465823 = 51698735) B51698735
theorem B22977215 : Blo 2123435 22977215 := bstep (se 1 (by rfl) ⟨17232911, by rfl⟩ : syracuseStep 22977215 = 34465823) B34465823
theorem B15318143 : Blo 2123435 15318143 := bstep (se 1 (by rfl) ⟨11488607, by rfl⟩ : syracuseStep 15318143 = 22977215) B22977215
theorem B10212095 : Blo 2123435 10212095 := bstep (se 1 (by rfl) ⟨7659071, by rfl⟩ : syracuseStep 10212095 = 15318143) B15318143
theorem B6808063 : Blo 2123435 6808063 := bstep (se 1 (by rfl) ⟨5106047, by rfl⟩ : syracuseStep 6808063 = 10212095) B10212095
theorem B9077417 : Blo 2123435 9077417 := bstep (se 2 (by rfl) ⟨3404031, by rfl⟩ : syracuseStep 9077417 = 6808063) B6808063
theorem B6051611 : Blo 2123435 6051611 := bstep (se 1 (by rfl) ⟨4538708, by rfl⟩ : syracuseStep 6051611 = 9077417) B9077417
theorem B16137629 : Blo 2123435 16137629 := bstep (se 3 (by rfl) ⟨3025805, by rfl⟩ : syracuseStep 16137629 = 6051611) B6051611
theorem B10758419 : Blo 2123435 10758419 := bstep (se 1 (by rfl) ⟨8068814, by rfl⟩ : syracuseStep 10758419 = 16137629) B16137629
theorem B7172279 : Blo 2123435 7172279 := bstep (se 1 (by rfl) ⟨5379209, by rfl⟩ : syracuseStep 7172279 = 10758419) B10758419
theorem B4781519 : Blo 2123435 4781519 := bstep (se 1 (by rfl) ⟨3586139, by rfl⟩ : syracuseStep 4781519 = 7172279) B7172279
theorem B3187679 : Blo 2123435 3187679 := bstep (se 1 (by rfl) ⟨2390759, by rfl⟩ : syracuseStep 3187679 = 4781519) B4781519
theorem B2125119 : Blo 2123435 2125119 := bstep (se 1 (by rfl) ⟨1593839, by rfl⟩ : syracuseStep 2125119 = 3187679) B3187679
theorem B3187685 : Blo 2123435 3187685 := bbase (se 4 (by rfl) ⟨298845, by rfl⟩ : syracuseStep 3187685 = 597691) (by norm_num)
theorem B2125123 : Blo 2123435 2125123 := bstep (se 1 (by rfl) ⟨1593842, by rfl⟩ : syracuseStep 2125123 = 3187685) B3187685
theorem B3404045 : Blo 2123435 3404045 := bbase (se 3 (by rfl) ⟨638258, by rfl⟩ : syracuseStep 3404045 = 1276517) (by norm_num)
theorem B9077453 : Blo 2123435 9077453 := bstep (se 3 (by rfl) ⟨1702022, by rfl⟩ : syracuseStep 9077453 = 3404045) B3404045
theorem B6051635 : Blo 2123435 6051635 := bstep (se 1 (by rfl) ⟨4538726, by rfl⟩ : syracuseStep 6051635 = 9077453) B9077453
theorem B4034423 : Blo 2123435 4034423 := bstep (se 1 (by rfl) ⟨3025817, by rfl⟩ : syracuseStep 4034423 = 6051635) B6051635
theorem B2689615 : Blo 2123435 2689615 := bstep (se 1 (by rfl) ⟨2017211, by rfl⟩ : syracuseStep 2689615 = 4034423) B4034423
theorem B3586153 : Blo 2123435 3586153 := bstep (se 2 (by rfl) ⟨1344807, by rfl⟩ : syracuseStep 3586153 = 2689615) B2689615
theorem B4781537 : Blo 2123435 4781537 := bstep (se 2 (by rfl) ⟨1793076, by rfl⟩ : syracuseStep 4781537 = 3586153) B3586153
theorem B3187691 : Blo 2123435 3187691 := bstep (se 1 (by rfl) ⟨2390768, by rfl⟩ : syracuseStep 3187691 = 4781537) B4781537
theorem B2125127 : Blo 2123435 2125127 := bstep (se 1 (by rfl) ⟨1593845, by rfl⟩ : syracuseStep 2125127 = 3187691) B3187691
theorem B2390773 : Blo 2123435 2390773 := bbase (se 5 (by rfl) ⟨112067, by rfl⟩ : syracuseStep 2390773 = 224135) (by norm_num)
theorem B3187697 : Blo 2123435 3187697 := bstep (se 2 (by rfl) ⟨1195386, by rfl⟩ : syracuseStep 3187697 = 2390773) B2390773
theorem B2125131 : Blo 2123435 2125131 := bstep (se 1 (by rfl) ⟨1593848, by rfl⟩ : syracuseStep 2125131 = 3187697) B3187697
theorem B2689625 : Blo 2123435 2689625 := bbase (se 2 (by rfl) ⟨1008609, by rfl⟩ : syracuseStep 2689625 = 2017219) (by norm_num)
theorem B7172333 : Blo 2123435 7172333 := bstep (se 3 (by rfl) ⟨1344812, by rfl⟩ : syracuseStep 7172333 = 2689625) B2689625
theorem B4781555 : Blo 2123435 4781555 := bstep (se 1 (by rfl) ⟨3586166, by rfl⟩ : syracuseStep 4781555 = 7172333) B7172333
theorem B3187703 : Blo 2123435 3187703 := bstep (se 1 (by rfl) ⟨2390777, by rfl⟩ : syracuseStep 3187703 = 4781555) B4781555
theorem B2125135 : Blo 2123435 2125135 := bstep (se 1 (by rfl) ⟨1593851, by rfl⟩ : syracuseStep 2125135 = 3187703) B3187703
theorem B3187709 : Blo 2123435 3187709 := bbase (se 3 (by rfl) ⟨597695, by rfl⟩ : syracuseStep 3187709 = 1195391) (by norm_num)
theorem B2125139 : Blo 2123435 2125139 := bstep (se 1 (by rfl) ⟨1593854, by rfl⟩ : syracuseStep 2125139 = 3187709) B3187709
theorem B4781573 : Blo 2123435 4781573 := bbase (se 4 (by rfl) ⟨448272, by rfl⟩ : syracuseStep 4781573 = 896545) (by norm_num)
theorem B3187715 : Blo 2123435 3187715 := bstep (se 1 (by rfl) ⟨2390786, by rfl⟩ : syracuseStep 3187715 = 4781573) B4781573
theorem B2125143 : Blo 2123435 2125143 := bstep (se 1 (by rfl) ⟨1593857, by rfl⟩ : syracuseStep 2125143 = 3187715) B3187715
theorem B4034461 : Blo 2123435 4034461 := bbase (se 3 (by rfl) ⟨756461, by rfl⟩ : syracuseStep 4034461 = 1512923) (by norm_num)
theorem B5379281 : Blo 2123435 5379281 := bstep (se 2 (by rfl) ⟨2017230, by rfl⟩ : syracuseStep 5379281 = 4034461) B4034461
theorem B3586187 : Blo 2123435 3586187 := bstep (se 1 (by rfl) ⟨2689640, by rfl⟩ : syracuseStep 3586187 = 5379281) B5379281
theorem B2390791 : Blo 2123435 2390791 := bstep (se 1 (by rfl) ⟨1793093, by rfl⟩ : syracuseStep 2390791 = 3586187) B3586187
theorem B3187721 : Blo 2123435 3187721 := bstep (se 2 (by rfl) ⟨1195395, by rfl⟩ : syracuseStep 3187721 = 2390791) B2390791
theorem B2125147 : Blo 2123435 2125147 := bstep (se 1 (by rfl) ⟨1593860, by rfl⟩ : syracuseStep 2125147 = 3187721) B3187721
theorem B10758581 : Blo 2123435 10758581 := bbase (se 5 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 10758581 = 1008617) (by norm_num)
theorem B7172387 : Blo 2123435 7172387 := bstep (se 1 (by rfl) ⟨5379290, by rfl⟩ : syracuseStep 7172387 = 10758581) B10758581
theorem B4781591 : Blo 2123435 4781591 := bstep (se 1 (by rfl) ⟨3586193, by rfl⟩ : syracuseStep 4781591 = 7172387) B7172387
theorem B3187727 : Blo 2123435 3187727 := bstep (se 1 (by rfl) ⟨2390795, by rfl⟩ : syracuseStep 3187727 = 4781591) B4781591
theorem B2125151 : Blo 2123435 2125151 := bstep (se 1 (by rfl) ⟨1593863, by rfl⟩ : syracuseStep 2125151 = 3187727) B3187727
theorem B3187733 : Blo 2123435 3187733 := bbase (se 6 (by rfl) ⟨74712, by rfl⟩ : syracuseStep 3187733 = 149425) (by norm_num)
theorem B2125155 : Blo 2123435 2125155 := bstep (se 1 (by rfl) ⟨1593866, by rfl⟩ : syracuseStep 2125155 = 3187733) B3187733
theorem B2623213 : Blo 2123435 2623213 := bbase (se 3 (by rfl) ⟨491852, by rfl⟩ : syracuseStep 2623213 = 983705) (by norm_num)
theorem B3497617 : Blo 2123435 3497617 := bstep (se 2 (by rfl) ⟨1311606, by rfl⟩ : syracuseStep 3497617 = 2623213) B2623213
theorem B4663489 : Blo 2123435 4663489 := bstep (se 2 (by rfl) ⟨1748808, by rfl⟩ : syracuseStep 4663489 = 3497617) B3497617
theorem B6217985 : Blo 2123435 6217985 := bstep (se 2 (by rfl) ⟨2331744, by rfl⟩ : syracuseStep 6217985 = 4663489) B4663489
theorem B4145323 : Blo 2123435 4145323 := bstep (se 1 (by rfl) ⟨3108992, by rfl⟩ : syracuseStep 4145323 = 6217985) B6217985
theorem B5527097 : Blo 2123435 5527097 := bstep (se 2 (by rfl) ⟨2072661, by rfl⟩ : syracuseStep 5527097 = 4145323) B4145323
theorem B3684731 : Blo 2123435 3684731 := bstep (se 1 (by rfl) ⟨2763548, by rfl⟩ : syracuseStep 3684731 = 5527097) B5527097
theorem B39303797 : Blo 2123435 39303797 := bstep (se 5 (by rfl) ⟨1842365, by rfl⟩ : syracuseStep 39303797 = 3684731) B3684731
theorem B104810125 : Blo 2123435 104810125 := bstep (se 3 (by rfl) ⟨19651898, by rfl⟩ : syracuseStep 104810125 = 39303797) B39303797
theorem B139746833 : Blo 2123435 139746833 := bstep (se 2 (by rfl) ⟨52405062, by rfl⟩ : syracuseStep 139746833 = 104810125) B104810125
theorem B93164555 : Blo 2123435 93164555 := bstep (se 1 (by rfl) ⟨69873416, by rfl⟩ : syracuseStep 93164555 = 139746833) B139746833
theorem B62109703 : Blo 2123435 62109703 := bstep (se 1 (by rfl) ⟨46582277, by rfl⟩ : syracuseStep 62109703 = 93164555) B93164555
theorem B82812937 : Blo 2123435 82812937 := bstep (se 2 (by rfl) ⟨31054851, by rfl⟩ : syracuseStep 82812937 = 62109703) B62109703
theorem B110417249 : Blo 2123435 110417249 := bstep (se 2 (by rfl) ⟨41406468, by rfl⟩ : syracuseStep 110417249 = 82812937) B82812937
theorem B73611499 : Blo 2123435 73611499 := bstep (se 1 (by rfl) ⟨55208624, by rfl⟩ : syracuseStep 73611499 = 110417249) B110417249
theorem B98148665 : Blo 2123435 98148665 := bstep (se 2 (by rfl) ⟨36805749, by rfl⟩ : syracuseStep 98148665 = 73611499) B73611499
theorem B65432443 : Blo 2123435 65432443 := bstep (se 1 (by rfl) ⟨49074332, by rfl⟩ : syracuseStep 65432443 = 98148665) B98148665
theorem B87243257 : Blo 2123435 87243257 := bstep (se 2 (by rfl) ⟨32716221, by rfl⟩ : syracuseStep 87243257 = 65432443) B65432443
theorem B232648685 : Blo 2123435 232648685 := bstep (se 3 (by rfl) ⟨43621628, by rfl⟩ : syracuseStep 232648685 = 87243257) B87243257
theorem B155099123 : Blo 2123435 155099123 := bstep (se 1 (by rfl) ⟨116324342, by rfl⟩ : syracuseStep 155099123 = 232648685) B232648685
theorem B103399415 : Blo 2123435 103399415 := bstep (se 1 (by rfl) ⟨77549561, by rfl⟩ : syracuseStep 103399415 = 155099123) B155099123
theorem B68932943 : Blo 2123435 68932943 := bstep (se 1 (by rfl) ⟨51699707, by rfl⟩ : syracuseStep 68932943 = 103399415) B103399415
theorem B45955295 : Blo 2123435 45955295 := bstep (se 1 (by rfl) ⟨34466471, by rfl⟩ : syracuseStep 45955295 = 68932943) B68932943
theorem B30636863 : Blo 2123435 30636863 := bstep (se 1 (by rfl) ⟨22977647, by rfl⟩ : syracuseStep 30636863 = 45955295) B45955295
theorem B20424575 : Blo 2123435 20424575 := bstep (se 1 (by rfl) ⟨15318431, by rfl⟩ : syracuseStep 20424575 = 30636863) B30636863
theorem B13616383 : Blo 2123435 13616383 := bstep (se 1 (by rfl) ⟨10212287, by rfl⟩ : syracuseStep 13616383 = 20424575) B20424575
theorem B18155177 : Blo 2123435 18155177 := bstep (se 2 (by rfl) ⟨6808191, by rfl⟩ : syracuseStep 18155177 = 13616383) B13616383
theorem B12103451 : Blo 2123435 12103451 := bstep (se 1 (by rfl) ⟨9077588, by rfl⟩ : syracuseStep 12103451 = 18155177) B18155177
theorem B8068967 : Blo 2123435 8068967 := bstep (se 1 (by rfl) ⟨6051725, by rfl⟩ : syracuseStep 8068967 = 12103451) B12103451
theorem B5379311 : Blo 2123435 5379311 := bstep (se 1 (by rfl) ⟨4034483, by rfl⟩ : syracuseStep 5379311 = 8068967) B8068967
theorem B3586207 : Blo 2123435 3586207 := bstep (se 1 (by rfl) ⟨2689655, by rfl⟩ : syracuseStep 3586207 = 5379311) B5379311
theorem B4781609 : Blo 2123435 4781609 := bstep (se 2 (by rfl) ⟨1793103, by rfl⟩ : syracuseStep 4781609 = 3586207) B3586207
theorem B3187739 : Blo 2123435 3187739 := bstep (se 1 (by rfl) ⟨2390804, by rfl⟩ : syracuseStep 3187739 = 4781609) B4781609
theorem B2125159 : Blo 2123435 2125159 := bstep (se 1 (by rfl) ⟨1593869, by rfl⟩ : syracuseStep 2125159 = 3187739) B3187739
theorem B2390809 : Blo 2123435 2390809 := bbase (se 2 (by rfl) ⟨896553, by rfl⟩ : syracuseStep 2390809 = 1793107) (by norm_num)
theorem B3187745 : Blo 2123435 3187745 := bstep (se 2 (by rfl) ⟨1195404, by rfl⟩ : syracuseStep 3187745 = 2390809) B2390809
theorem B2125163 : Blo 2123435 2125163 := bstep (se 1 (by rfl) ⟨1593872, by rfl⟩ : syracuseStep 2125163 = 3187745) B3187745
theorem B8068997 : Blo 2123435 8068997 := bbase (se 4 (by rfl) ⟨756468, by rfl⟩ : syracuseStep 8068997 = 1512937) (by norm_num)
theorem B5379331 : Blo 2123435 5379331 := bstep (se 1 (by rfl) ⟨4034498, by rfl⟩ : syracuseStep 5379331 = 8068997) B8068997
theorem B7172441 : Blo 2123435 7172441 := bstep (se 2 (by rfl) ⟨2689665, by rfl⟩ : syracuseStep 7172441 = 5379331) B5379331
theorem B4781627 : Blo 2123435 4781627 := bstep (se 1 (by rfl) ⟨3586220, by rfl⟩ : syracuseStep 4781627 = 7172441) B7172441
theorem B3187751 : Blo 2123435 3187751 := bstep (se 1 (by rfl) ⟨2390813, by rfl⟩ : syracuseStep 3187751 = 4781627) B4781627
theorem B2125167 : Blo 2123435 2125167 := bstep (se 1 (by rfl) ⟨1593875, by rfl⟩ : syracuseStep 2125167 = 3187751) B3187751
theorem B3187757 : Blo 2123435 3187757 := bbase (se 3 (by rfl) ⟨597704, by rfl⟩ : syracuseStep 3187757 = 1195409) (by norm_num)
theorem B2125171 : Blo 2123435 2125171 := bstep (se 1 (by rfl) ⟨1593878, by rfl⟩ : syracuseStep 2125171 = 3187757) B3187757
theorem B4781645 : Blo 2123435 4781645 := bbase (se 3 (by rfl) ⟨896558, by rfl⟩ : syracuseStep 4781645 = 1793117) (by norm_num)
theorem B3187763 : Blo 2123435 3187763 := bstep (se 1 (by rfl) ⟨2390822, by rfl⟩ : syracuseStep 3187763 = 4781645) B4781645
theorem B2125175 : Blo 2123435 2125175 := bstep (se 1 (by rfl) ⟨1593881, by rfl⟩ : syracuseStep 2125175 = 3187763) B3187763
theorem B2689681 : Blo 2123435 2689681 := bbase (se 2 (by rfl) ⟨1008630, by rfl⟩ : syracuseStep 2689681 = 2017261) (by norm_num)
theorem B3586241 : Blo 2123435 3586241 := bstep (se 2 (by rfl) ⟨1344840, by rfl⟩ : syracuseStep 3586241 = 2689681) B2689681
theorem B2390827 : Blo 2123435 2390827 := bstep (se 1 (by rfl) ⟨1793120, by rfl⟩ : syracuseStep 2390827 = 3586241) B3586241
theorem B3187769 : Blo 2123435 3187769 := bstep (se 2 (by rfl) ⟨1195413, by rfl⟩ : syracuseStep 3187769 = 2390827) B2390827
theorem B2125179 : Blo 2123435 2125179 := bstep (se 1 (by rfl) ⟨1593884, by rfl⟩ : syracuseStep 2125179 = 3187769) B3187769
theorem B4538845 : Blo 2123435 4538845 := bbase (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) (by norm_num)
theorem B24207173 : Blo 2123435 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B16138115 : Blo 2123435 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B10758743 : Blo 2123435 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B7172495 : Blo 2123435 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B4781663 : Blo 2123435 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B3187775 : Blo 2123435 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B2125183 : Blo 2123435 2125183 := bstep (se 1 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 2125183 = 3187775) B3187775
theorem B3187781 : Blo 2123435 3187781 := bbase (se 4 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 3187781 = 597709) (by norm_num)
theorem B2125187 : Blo 2123435 2125187 := bstep (se 1 (by rfl) ⟨1593890, by rfl⟩ : syracuseStep 2125187 = 3187781) B3187781
theorem B3586261 : Blo 2123435 3586261 := bbase (se 7 (by rfl) ⟨42026, by rfl⟩ : syracuseStep 3586261 = 84053) (by norm_num)
theorem B4781681 : Blo 2123435 4781681 := bstep (se 2 (by rfl) ⟨1793130, by rfl⟩ : syracuseStep 4781681 = 3586261) B3586261
theorem B3187787 : Blo 2123435 3187787 := bstep (se 1 (by rfl) ⟨2390840, by rfl⟩ : syracuseStep 3187787 = 4781681) B4781681
theorem B2125191 : Blo 2123435 2125191 := bstep (se 1 (by rfl) ⟨1593893, by rfl⟩ : syracuseStep 2125191 = 3187787) B3187787
theorem B2390845 : Blo 2123435 2390845 := bbase (se 3 (by rfl) ⟨448283, by rfl⟩ : syracuseStep 2390845 = 896567) (by norm_num)
theorem B3187793 : Blo 2123435 3187793 := bstep (se 2 (by rfl) ⟨1195422, by rfl⟩ : syracuseStep 3187793 = 2390845) B2390845
theorem B2125195 : Blo 2123435 2125195 := bstep (se 1 (by rfl) ⟨1593896, by rfl⟩ : syracuseStep 2125195 = 3187793) B3187793
theorem B7172549 : Blo 2123435 7172549 := bbase (se 4 (by rfl) ⟨672426, by rfl⟩ : syracuseStep 7172549 = 1344853) (by norm_num)
theorem B4781699 : Blo 2123435 4781699 := bstep (se 1 (by rfl) ⟨3586274, by rfl⟩ : syracuseStep 4781699 = 7172549) B7172549
theorem B3187799 : Blo 2123435 3187799 := bstep (se 1 (by rfl) ⟨2390849, by rfl⟩ : syracuseStep 3187799 = 4781699) B4781699
theorem B2125199 : Blo 2123435 2125199 := bstep (se 1 (by rfl) ⟨1593899, by rfl⟩ : syracuseStep 2125199 = 3187799) B3187799
theorem B3187805 : Blo 2123435 3187805 := bbase (se 3 (by rfl) ⟨597713, by rfl⟩ : syracuseStep 3187805 = 1195427) (by norm_num)
theorem B2125203 : Blo 2123435 2125203 := bstep (se 1 (by rfl) ⟨1593902, by rfl⟩ : syracuseStep 2125203 = 3187805) B3187805
theorem B4781717 : Blo 2123435 4781717 := bbase (se 6 (by rfl) ⟨112071, by rfl⟩ : syracuseStep 4781717 = 224143) (by norm_num)
theorem B3187811 : Blo 2123435 3187811 := bstep (se 1 (by rfl) ⟨2390858, by rfl⟩ : syracuseStep 3187811 = 4781717) B4781717
theorem B2125207 : Blo 2123435 2125207 := bstep (se 1 (by rfl) ⟨1593905, by rfl⟩ : syracuseStep 2125207 = 3187811) B3187811
theorem B2269453 : Blo 2123435 2269453 := bbase (se 3 (by rfl) ⟨425522, by rfl⟩ : syracuseStep 2269453 = 851045) (by norm_num)
theorem B3025937 : Blo 2123435 3025937 := bstep (se 2 (by rfl) ⟨1134726, by rfl⟩ : syracuseStep 3025937 = 2269453) B2269453
theorem B8069165 : Blo 2123435 8069165 := bstep (se 3 (by rfl) ⟨1512968, by rfl⟩ : syracuseStep 8069165 = 3025937) B3025937
theorem B5379443 : Blo 2123435 5379443 := bstep (se 1 (by rfl) ⟨4034582, by rfl⟩ : syracuseStep 5379443 = 8069165) B8069165
theorem B3586295 : Blo 2123435 3586295 := bstep (se 1 (by rfl) ⟨2689721, by rfl⟩ : syracuseStep 3586295 = 5379443) B5379443
theorem B2390863 : Blo 2123435 2390863 := bstep (se 1 (by rfl) ⟨1793147, by rfl⟩ : syracuseStep 2390863 = 3586295) B3586295
theorem B3187817 : Blo 2123435 3187817 := bstep (se 2 (by rfl) ⟨1195431, by rfl⟩ : syracuseStep 3187817 = 2390863) B2390863
theorem B2125211 : Blo 2123435 2125211 := bstep (se 1 (by rfl) ⟨1593908, by rfl⟩ : syracuseStep 2125211 = 3187817) B3187817
theorem B3829709 : Blo 2123435 3829709 := bbase (se 3 (by rfl) ⟨718070, by rfl⟩ : syracuseStep 3829709 = 1436141) (by norm_num)
theorem B2553139 : Blo 2123435 2553139 := bstep (se 1 (by rfl) ⟨1914854, by rfl⟩ : syracuseStep 2553139 = 3829709) B3829709
theorem B13616741 : Blo 2123435 13616741 := bstep (se 4 (by rfl) ⟨1276569, by rfl⟩ : syracuseStep 13616741 = 2553139) B2553139
theorem B9077827 : Blo 2123435 9077827 := bstep (se 1 (by rfl) ⟨6808370, by rfl⟩ : syracuseStep 9077827 = 13616741) B13616741
theorem B12103769 : Blo 2123435 12103769 := bstep (se 2 (by rfl) ⟨4538913, by rfl⟩ : syracuseStep 12103769 = 9077827) B9077827
theorem B8069179 : Blo 2123435 8069179 := bstep (se 1 (by rfl) ⟨6051884, by rfl⟩ : syracuseStep 8069179 = 12103769) B12103769
theorem B10758905 : Blo 2123435 10758905 := bstep (se 2 (by rfl) ⟨4034589, by rfl⟩ : syracuseStep 10758905 = 8069179) B8069179
theorem B7172603 : Blo 2123435 7172603 := bstep (se 1 (by rfl) ⟨5379452, by rfl⟩ : syracuseStep 7172603 = 10758905) B10758905
theorem B4781735 : Blo 2123435 4781735 := bstep (se 1 (by rfl) ⟨3586301, by rfl⟩ : syracuseStep 4781735 = 7172603) B7172603
theorem B3187823 : Blo 2123435 3187823 := bstep (se 1 (by rfl) ⟨2390867, by rfl⟩ : syracuseStep 3187823 = 4781735) B4781735
theorem B2125215 : Blo 2123435 2125215 := bstep (se 1 (by rfl) ⟨1593911, by rfl⟩ : syracuseStep 2125215 = 3187823) B3187823
theorem B3187829 : Blo 2123435 3187829 := bbase (se 5 (by rfl) ⟨149429, by rfl⟩ : syracuseStep 3187829 = 298859) (by norm_num)
theorem B2125219 : Blo 2123435 2125219 := bstep (se 1 (by rfl) ⟨1593914, by rfl⟩ : syracuseStep 2125219 = 3187829) B3187829
theorem B4034605 : Blo 2123435 4034605 := bbase (se 3 (by rfl) ⟨756488, by rfl⟩ : syracuseStep 4034605 = 1512977) (by norm_num)
theorem B5379473 : Blo 2123435 5379473 := bstep (se 2 (by rfl) ⟨2017302, by rfl⟩ : syracuseStep 5379473 = 4034605) B4034605
theorem B3586315 : Blo 2123435 3586315 := bstep (se 1 (by rfl) ⟨2689736, by rfl⟩ : syracuseStep 3586315 = 5379473) B5379473
theorem B4781753 : Blo 2123435 4781753 := bstep (se 2 (by rfl) ⟨1793157, by rfl⟩ : syracuseStep 4781753 = 3586315) B3586315
theorem B3187835 : Blo 2123435 3187835 := bstep (se 1 (by rfl) ⟨2390876, by rfl⟩ : syracuseStep 3187835 = 4781753) B4781753
theorem B2125223 : Blo 2123435 2125223 := bstep (se 1 (by rfl) ⟨1593917, by rfl⟩ : syracuseStep 2125223 = 3187835) B3187835
theorem B2390881 : Blo 2123435 2390881 := bbase (se 2 (by rfl) ⟨896580, by rfl⟩ : syracuseStep 2390881 = 1793161) (by norm_num)
theorem B3187841 : Blo 2123435 3187841 := bstep (se 2 (by rfl) ⟨1195440, by rfl⟩ : syracuseStep 3187841 = 2390881) B2390881
theorem B2125227 : Blo 2123435 2125227 := bstep (se 1 (by rfl) ⟨1593920, by rfl⟩ : syracuseStep 2125227 = 3187841) B3187841
theorem B5379493 : Blo 2123435 5379493 := bbase (se 4 (by rfl) ⟨504327, by rfl⟩ : syracuseStep 5379493 = 1008655) (by norm_num)
theorem B7172657 : Blo 2123435 7172657 := bstep (se 2 (by rfl) ⟨2689746, by rfl⟩ : syracuseStep 7172657 = 5379493) B5379493
theorem B4781771 : Blo 2123435 4781771 := bstep (se 1 (by rfl) ⟨3586328, by rfl⟩ : syracuseStep 4781771 = 7172657) B7172657
theorem B3187847 : Blo 2123435 3187847 := bstep (se 1 (by rfl) ⟨2390885, by rfl⟩ : syracuseStep 3187847 = 4781771) B4781771
theorem B2125231 : Blo 2123435 2125231 := bstep (se 1 (by rfl) ⟨1593923, by rfl⟩ : syracuseStep 2125231 = 3187847) B3187847
theorem B3187853 : Blo 2123435 3187853 := bbase (se 3 (by rfl) ⟨597722, by rfl⟩ : syracuseStep 3187853 = 1195445) (by norm_num)
theorem B2125235 : Blo 2123435 2125235 := bstep (se 1 (by rfl) ⟨1593926, by rfl⟩ : syracuseStep 2125235 = 3187853) B3187853
theorem B4781789 : Blo 2123435 4781789 := bbase (se 3 (by rfl) ⟨896585, by rfl⟩ : syracuseStep 4781789 = 1793171) (by norm_num)
theorem B3187859 : Blo 2123435 3187859 := bstep (se 1 (by rfl) ⟨2390894, by rfl⟩ : syracuseStep 3187859 = 4781789) B4781789
theorem B2125239 : Blo 2123435 2125239 := bstep (se 1 (by rfl) ⟨1593929, by rfl⟩ : syracuseStep 2125239 = 3187859) B3187859
theorem B3586349 : Blo 2123435 3586349 := bbase (se 3 (by rfl) ⟨672440, by rfl⟩ : syracuseStep 3586349 = 1344881) (by norm_num)
theorem B2390899 : Blo 2123435 2390899 := bstep (se 1 (by rfl) ⟨1793174, by rfl⟩ : syracuseStep 2390899 = 3586349) B3586349
theorem B3187865 : Blo 2123435 3187865 := bstep (se 2 (by rfl) ⟨1195449, by rfl⟩ : syracuseStep 3187865 = 2390899) B2390899
theorem B2125243 : Blo 2123435 2125243 := bstep (se 1 (by rfl) ⟨1593932, by rfl⟩ : syracuseStep 2125243 = 3187865) B3187865
theorem B40850837 : Blo 2123435 40850837 := bbase (se 6 (by rfl) ⟨957441, by rfl⟩ : syracuseStep 40850837 = 1914883) (by norm_num)
theorem B27233891 : Blo 2123435 27233891 := bstep (se 1 (by rfl) ⟨20425418, by rfl⟩ : syracuseStep 27233891 = 40850837) B40850837
theorem B18155927 : Blo 2123435 18155927 := bstep (se 1 (by rfl) ⟨13616945, by rfl⟩ : syracuseStep 18155927 = 27233891) B27233891
theorem B12103951 : Blo 2123435 12103951 := bstep (se 1 (by rfl) ⟨9077963, by rfl⟩ : syracuseStep 12103951 = 18155927) B18155927
theorem B16138601 : Blo 2123435 16138601 := bstep (se 2 (by rfl) ⟨6051975, by rfl⟩ : syracuseStep 16138601 = 12103951) B12103951
theorem B10759067 : Blo 2123435 10759067 := bstep (se 1 (by rfl) ⟨8069300, by rfl⟩ : syracuseStep 10759067 = 16138601) B16138601
theorem B7172711 : Blo 2123435 7172711 := bstep (se 1 (by rfl) ⟨5379533, by rfl⟩ : syracuseStep 7172711 = 10759067) B10759067
theorem B4781807 : Blo 2123435 4781807 := bstep (se 1 (by rfl) ⟨3586355, by rfl⟩ : syracuseStep 4781807 = 7172711) B7172711
theorem B3187871 : Blo 2123435 3187871 := bstep (se 1 (by rfl) ⟨2390903, by rfl⟩ : syracuseStep 3187871 = 4781807) B4781807
theorem B2125247 : Blo 2123435 2125247 := bstep (se 1 (by rfl) ⟨1593935, by rfl⟩ : syracuseStep 2125247 = 3187871) B3187871
theorem B3187877 : Blo 2123435 3187877 := bbase (se 4 (by rfl) ⟨298863, by rfl⟩ : syracuseStep 3187877 = 597727) (by norm_num)
theorem B2125251 : Blo 2123435 2125251 := bstep (se 1 (by rfl) ⟨1593938, by rfl⟩ : syracuseStep 2125251 = 3187877) B3187877
theorem B2689777 : Blo 2123435 2689777 := bbase (se 2 (by rfl) ⟨1008666, by rfl⟩ : syracuseStep 2689777 = 2017333) (by norm_num)
theorem B3586369 : Blo 2123435 3586369 := bstep (se 2 (by rfl) ⟨1344888, by rfl⟩ : syracuseStep 3586369 = 2689777) B2689777
theorem B4781825 : Blo 2123435 4781825 := bstep (se 2 (by rfl) ⟨1793184, by rfl⟩ : syracuseStep 4781825 = 3586369) B3586369
theorem B3187883 : Blo 2123435 3187883 := bstep (se 1 (by rfl) ⟨2390912, by rfl⟩ : syracuseStep 3187883 = 4781825) B4781825
theorem B2125255 : Blo 2123435 2125255 := bstep (se 1 (by rfl) ⟨1593941, by rfl⟩ : syracuseStep 2125255 = 3187883) B3187883
theorem B2390917 : Blo 2123435 2390917 := bbase (se 4 (by rfl) ⟨224148, by rfl⟩ : syracuseStep 2390917 = 448297) (by norm_num)
theorem B3187889 : Blo 2123435 3187889 := bstep (se 2 (by rfl) ⟨1195458, by rfl⟩ : syracuseStep 3187889 = 2390917) B2390917
theorem B2125259 : Blo 2123435 2125259 := bstep (se 1 (by rfl) ⟨1593944, by rfl⟩ : syracuseStep 2125259 = 3187889) B3187889
theorem B2183653 : Blo 2123435 2183653 := bbase (se 4 (by rfl) ⟨204717, by rfl⟩ : syracuseStep 2183653 = 409435) (by norm_num)
theorem B2911537 : Blo 2123435 2911537 := bstep (se 2 (by rfl) ⟨1091826, by rfl⟩ : syracuseStep 2911537 = 2183653) B2183653
theorem B3882049 : Blo 2123435 3882049 := bstep (se 2 (by rfl) ⟨1455768, by rfl⟩ : syracuseStep 3882049 = 2911537) B2911537
theorem B20704261 : Blo 2123435 20704261 := bstep (se 4 (by rfl) ⟨1941024, by rfl⟩ : syracuseStep 20704261 = 3882049) B3882049
theorem B27605681 : Blo 2123435 27605681 := bstep (se 2 (by rfl) ⟨10352130, by rfl⟩ : syracuseStep 27605681 = 20704261) B20704261
theorem B18403787 : Blo 2123435 18403787 := bstep (se 1 (by rfl) ⟨13802840, by rfl⟩ : syracuseStep 18403787 = 27605681) B27605681
theorem B12269191 : Blo 2123435 12269191 := bstep (se 1 (by rfl) ⟨9201893, by rfl⟩ : syracuseStep 12269191 = 18403787) B18403787
theorem B16358921 : Blo 2123435 16358921 := bstep (se 2 (by rfl) ⟨6134595, by rfl⟩ : syracuseStep 16358921 = 12269191) B12269191
theorem B10905947 : Blo 2123435 10905947 := bstep (se 1 (by rfl) ⟨8179460, by rfl⟩ : syracuseStep 10905947 = 16358921) B16358921
theorem B7270631 : Blo 2123435 7270631 := bstep (se 1 (by rfl) ⟨5452973, by rfl⟩ : syracuseStep 7270631 = 10905947) B10905947
theorem B4847087 : Blo 2123435 4847087 := bstep (se 1 (by rfl) ⟨3635315, by rfl⟩ : syracuseStep 4847087 = 7270631) B7270631
theorem B12925565 : Blo 2123435 12925565 := bstep (se 3 (by rfl) ⟨2423543, by rfl⟩ : syracuseStep 12925565 = 4847087) B4847087
theorem B8617043 : Blo 2123435 8617043 := bstep (se 1 (by rfl) ⟨6462782, by rfl⟩ : syracuseStep 8617043 = 12925565) B12925565
theorem B5744695 : Blo 2123435 5744695 := bstep (se 1 (by rfl) ⟨4308521, by rfl⟩ : syracuseStep 5744695 = 8617043) B8617043
theorem B7659593 : Blo 2123435 7659593 := bstep (se 2 (by rfl) ⟨2872347, by rfl⟩ : syracuseStep 7659593 = 5744695) B5744695
theorem B5106395 : Blo 2123435 5106395 := bstep (se 1 (by rfl) ⟨3829796, by rfl⟩ : syracuseStep 5106395 = 7659593) B7659593
theorem B3404263 : Blo 2123435 3404263 := bstep (se 1 (by rfl) ⟨2553197, by rfl⟩ : syracuseStep 3404263 = 5106395) B5106395
theorem B4539017 : Blo 2123435 4539017 := bstep (se 2 (by rfl) ⟨1702131, by rfl⟩ : syracuseStep 4539017 = 3404263) B3404263
theorem B3026011 : Blo 2123435 3026011 := bstep (se 1 (by rfl) ⟨2269508, by rfl⟩ : syracuseStep 3026011 = 4539017) B4539017
theorem B4034681 : Blo 2123435 4034681 := bstep (se 2 (by rfl) ⟨1513005, by rfl⟩ : syracuseStep 4034681 = 3026011) B3026011
theorem B2689787 : Blo 2123435 2689787 := bstep (se 1 (by rfl) ⟨2017340, by rfl⟩ : syracuseStep 2689787 = 4034681) B4034681
theorem B7172765 : Blo 2123435 7172765 := bstep (se 3 (by rfl) ⟨1344893, by rfl⟩ : syracuseStep 7172765 = 2689787) B2689787
theorem B4781843 : Blo 2123435 4781843 := bstep (se 1 (by rfl) ⟨3586382, by rfl⟩ : syracuseStep 4781843 = 7172765) B7172765
theorem B3187895 : Blo 2123435 3187895 := bstep (se 1 (by rfl) ⟨2390921, by rfl⟩ : syracuseStep 3187895 = 4781843) B4781843
theorem B2125263 : Blo 2123435 2125263 := bstep (se 1 (by rfl) ⟨1593947, by rfl⟩ : syracuseStep 2125263 = 3187895) B3187895
theorem B3187901 : Blo 2123435 3187901 := bbase (se 3 (by rfl) ⟨597731, by rfl⟩ : syracuseStep 3187901 = 1195463) (by norm_num)
theorem B2125267 : Blo 2123435 2125267 := bstep (se 1 (by rfl) ⟨1593950, by rfl⟩ : syracuseStep 2125267 = 3187901) B3187901
theorem B4781861 : Blo 2123435 4781861 := bbase (se 4 (by rfl) ⟨448299, by rfl⟩ : syracuseStep 4781861 = 896599) (by norm_num)
theorem B3187907 : Blo 2123435 3187907 := bstep (se 1 (by rfl) ⟨2390930, by rfl⟩ : syracuseStep 3187907 = 4781861) B4781861
theorem B2125271 : Blo 2123435 2125271 := bstep (se 1 (by rfl) ⟨1593953, by rfl⟩ : syracuseStep 2125271 = 3187907) B3187907
theorem B5379605 : Blo 2123435 5379605 := bbase (se 6 (by rfl) ⟨126084, by rfl⟩ : syracuseStep 5379605 = 252169) (by norm_num)
theorem B3586403 : Blo 2123435 3586403 := bstep (se 1 (by rfl) ⟨2689802, by rfl⟩ : syracuseStep 3586403 = 5379605) B5379605
theorem B2390935 : Blo 2123435 2390935 := bstep (se 1 (by rfl) ⟨1793201, by rfl⟩ : syracuseStep 2390935 = 3586403) B3586403
theorem B3187913 : Blo 2123435 3187913 := bstep (se 2 (by rfl) ⟨1195467, by rfl⟩ : syracuseStep 3187913 = 2390935) B2390935
theorem B2125275 : Blo 2123435 2125275 := bstep (se 1 (by rfl) ⟨1593956, by rfl⟩ : syracuseStep 2125275 = 3187913) B3187913
theorem B9078101 : Blo 2123435 9078101 := bbase (se 12 (by rfl) ⟨3324, by rfl⟩ : syracuseStep 9078101 = 6649) (by norm_num)
theorem B6052067 : Blo 2123435 6052067 := bstep (se 1 (by rfl) ⟨4539050, by rfl⟩ : syracuseStep 6052067 = 9078101) B9078101
theorem B4034711 : Blo 2123435 4034711 := bstep (se 1 (by rfl) ⟨3026033, by rfl⟩ : syracuseStep 4034711 = 6052067) B6052067
theorem B10759229 : Blo 2123435 10759229 := bstep (se 3 (by rfl) ⟨2017355, by rfl⟩ : syracuseStep 10759229 = 4034711) B4034711
theorem B7172819 : Blo 2123435 7172819 := bstep (se 1 (by rfl) ⟨5379614, by rfl⟩ : syracuseStep 7172819 = 10759229) B10759229
theorem B4781879 : Blo 2123435 4781879 := bstep (se 1 (by rfl) ⟨3586409, by rfl⟩ : syracuseStep 4781879 = 7172819) B7172819
theorem B3187919 : Blo 2123435 3187919 := bstep (se 1 (by rfl) ⟨2390939, by rfl⟩ : syracuseStep 3187919 = 4781879) B4781879
theorem B2125279 : Blo 2123435 2125279 := bstep (se 1 (by rfl) ⟨1593959, by rfl⟩ : syracuseStep 2125279 = 3187919) B3187919
theorem B3187925 : Blo 2123435 3187925 := bbase (se 7 (by rfl) ⟨37358, by rfl⟩ : syracuseStep 3187925 = 74717) (by norm_num)
theorem B2125283 : Blo 2123435 2125283 := bstep (se 1 (by rfl) ⟨1593962, by rfl⟩ : syracuseStep 2125283 = 3187925) B3187925
theorem B3026045 : Blo 2123435 3026045 := bbase (se 3 (by rfl) ⟨567383, by rfl⟩ : syracuseStep 3026045 = 1134767) (by norm_num)
theorem B8069453 : Blo 2123435 8069453 := bstep (se 3 (by rfl) ⟨1513022, by rfl⟩ : syracuseStep 8069453 = 3026045) B3026045
theorem B5379635 : Blo 2123435 5379635 := bstep (se 1 (by rfl) ⟨4034726, by rfl⟩ : syracuseStep 5379635 = 8069453) B8069453
theorem B3586423 : Blo 2123435 3586423 := bstep (se 1 (by rfl) ⟨2689817, by rfl⟩ : syracuseStep 3586423 = 5379635) B5379635
theorem B4781897 : Blo 2123435 4781897 := bstep (se 2 (by rfl) ⟨1793211, by rfl⟩ : syracuseStep 4781897 = 3586423) B3586423
theorem B3187931 : Blo 2123435 3187931 := bstep (se 1 (by rfl) ⟨2390948, by rfl⟩ : syracuseStep 3187931 = 4781897) B4781897
theorem B2125287 : Blo 2123435 2125287 := bstep (se 1 (by rfl) ⟨1593965, by rfl⟩ : syracuseStep 2125287 = 3187931) B3187931
theorem B2390953 : Blo 2123435 2390953 := bbase (se 2 (by rfl) ⟨896607, by rfl⟩ : syracuseStep 2390953 = 1793215) (by norm_num)
theorem B3187937 : Blo 2123435 3187937 := bstep (se 2 (by rfl) ⟨1195476, by rfl⟩ : syracuseStep 3187937 = 2390953) B2390953
theorem B2125291 : Blo 2123435 2125291 := bstep (se 1 (by rfl) ⟨1593968, by rfl⟩ : syracuseStep 2125291 = 3187937) B3187937
theorem B3829853 : Blo 2123435 3829853 := bbase (se 3 (by rfl) ⟨718097, by rfl⟩ : syracuseStep 3829853 = 1436195) (by norm_num)
theorem B10212941 : Blo 2123435 10212941 := bstep (se 3 (by rfl) ⟨1914926, by rfl⟩ : syracuseStep 10212941 = 3829853) B3829853
theorem B6808627 : Blo 2123435 6808627 := bstep (se 1 (by rfl) ⟨5106470, by rfl⟩ : syracuseStep 6808627 = 10212941) B10212941
theorem B9078169 : Blo 2123435 9078169 := bstep (se 2 (by rfl) ⟨3404313, by rfl⟩ : syracuseStep 9078169 = 6808627) B6808627
theorem B12104225 : Blo 2123435 12104225 := bstep (se 2 (by rfl) ⟨4539084, by rfl⟩ : syracuseStep 12104225 = 9078169) B9078169
theorem B8069483 : Blo 2123435 8069483 := bstep (se 1 (by rfl) ⟨6052112, by rfl⟩ : syracuseStep 8069483 = 12104225) B12104225
theorem B5379655 : Blo 2123435 5379655 := bstep (se 1 (by rfl) ⟨4034741, by rfl⟩ : syracuseStep 5379655 = 8069483) B8069483
theorem B7172873 : Blo 2123435 7172873 := bstep (se 2 (by rfl) ⟨2689827, by rfl⟩ : syracuseStep 7172873 = 5379655) B5379655
theorem B4781915 : Blo 2123435 4781915 := bstep (se 1 (by rfl) ⟨3586436, by rfl⟩ : syracuseStep 4781915 = 7172873) B7172873
theorem B3187943 : Blo 2123435 3187943 := bstep (se 1 (by rfl) ⟨2390957, by rfl⟩ : syracuseStep 3187943 = 4781915) B4781915
theorem B2125295 : Blo 2123435 2125295 := bstep (se 1 (by rfl) ⟨1593971, by rfl⟩ : syracuseStep 2125295 = 3187943) B3187943
theorem B3187949 : Blo 2123435 3187949 := bbase (se 3 (by rfl) ⟨597740, by rfl⟩ : syracuseStep 3187949 = 1195481) (by norm_num)
theorem B2125299 : Blo 2123435 2125299 := bstep (se 1 (by rfl) ⟨1593974, by rfl⟩ : syracuseStep 2125299 = 3187949) B3187949
theorem B4781933 : Blo 2123435 4781933 := bbase (se 3 (by rfl) ⟨896612, by rfl⟩ : syracuseStep 4781933 = 1793225) (by norm_num)
theorem B3187955 : Blo 2123435 3187955 := bstep (se 1 (by rfl) ⟨2390966, by rfl⟩ : syracuseStep 3187955 = 4781933) B4781933
theorem B2125303 : Blo 2123435 2125303 := bstep (se 1 (by rfl) ⟨1593977, by rfl⟩ : syracuseStep 2125303 = 3187955) B3187955
theorem B4034765 : Blo 2123435 4034765 := bbase (se 3 (by rfl) ⟨756518, by rfl⟩ : syracuseStep 4034765 = 1513037) (by norm_num)
theorem B2689843 : Blo 2123435 2689843 := bstep (se 1 (by rfl) ⟨2017382, by rfl⟩ : syracuseStep 2689843 = 4034765) B4034765
theorem B3586457 : Blo 2123435 3586457 := bstep (se 2 (by rfl) ⟨1344921, by rfl⟩ : syracuseStep 3586457 = 2689843) B2689843
theorem B2390971 : Blo 2123435 2390971 := bstep (se 1 (by rfl) ⟨1793228, by rfl⟩ : syracuseStep 2390971 = 3586457) B3586457
theorem B3187961 : Blo 2123435 3187961 := bstep (se 2 (by rfl) ⟨1195485, by rfl⟩ : syracuseStep 3187961 = 2390971) B2390971
theorem B2125307 : Blo 2123435 2125307 := bstep (se 1 (by rfl) ⟨1593980, by rfl⟩ : syracuseStep 2125307 = 3187961) B3187961
theorem B5176181 : Blo 2123435 5176181 := bbase (se 5 (by rfl) ⟨242633, by rfl⟩ : syracuseStep 5176181 = 485267) (by norm_num)
theorem B13803149 : Blo 2123435 13803149 := bstep (se 3 (by rfl) ⟨2588090, by rfl⟩ : syracuseStep 13803149 = 5176181) B5176181
theorem B9202099 : Blo 2123435 9202099 := bstep (se 1 (by rfl) ⟨6901574, by rfl⟩ : syracuseStep 9202099 = 13803149) B13803149
theorem B12269465 : Blo 2123435 12269465 := bstep (se 2 (by rfl) ⟨4601049, by rfl⟩ : syracuseStep 12269465 = 9202099) B9202099
theorem B8179643 : Blo 2123435 8179643 := bstep (se 1 (by rfl) ⟨6134732, by rfl⟩ : syracuseStep 8179643 = 12269465) B12269465
theorem B5453095 : Blo 2123435 5453095 := bstep (se 1 (by rfl) ⟨4089821, by rfl⟩ : syracuseStep 5453095 = 8179643) B8179643
theorem B7270793 : Blo 2123435 7270793 := bstep (se 2 (by rfl) ⟨2726547, by rfl⟩ : syracuseStep 7270793 = 5453095) B5453095
theorem B4847195 : Blo 2123435 4847195 := bstep (se 1 (by rfl) ⟨3635396, by rfl⟩ : syracuseStep 4847195 = 7270793) B7270793
theorem B3231463 : Blo 2123435 3231463 := bstep (se 1 (by rfl) ⟨2423597, by rfl⟩ : syracuseStep 3231463 = 4847195) B4847195
theorem B4308617 : Blo 2123435 4308617 := bstep (se 2 (by rfl) ⟨1615731, by rfl⟩ : syracuseStep 4308617 = 3231463) B3231463
theorem B2872411 : Blo 2123435 2872411 := bstep (se 1 (by rfl) ⟨2154308, by rfl⟩ : syracuseStep 2872411 = 4308617) B4308617
theorem B15319525 : Blo 2123435 15319525 := bstep (se 4 (by rfl) ⟨1436205, by rfl⟩ : syracuseStep 15319525 = 2872411) B2872411
theorem B20426033 : Blo 2123435 20426033 := bstep (se 2 (by rfl) ⟨7659762, by rfl⟩ : syracuseStep 20426033 = 15319525) B15319525
theorem B54469421 : Blo 2123435 54469421 := bstep (se 3 (by rfl) ⟨10213016, by rfl⟩ : syracuseStep 54469421 = 20426033) B20426033
theorem B36312947 : Blo 2123435 36312947 := bstep (se 1 (by rfl) ⟨27234710, by rfl⟩ : syracuseStep 36312947 = 54469421) B54469421
theorem B24208631 : Blo 2123435 24208631 := bstep (se 1 (by rfl) ⟨18156473, by rfl⟩ : syracuseStep 24208631 = 36312947) B36312947
theorem B16139087 : Blo 2123435 16139087 := bstep (se 1 (by rfl) ⟨12104315, by rfl⟩ : syracuseStep 16139087 = 24208631) B24208631
theorem B10759391 : Blo 2123435 10759391 := bstep (se 1 (by rfl) ⟨8069543, by rfl⟩ : syracuseStep 10759391 = 16139087) B16139087
theorem B7172927 : Blo 2123435 7172927 := bstep (se 1 (by rfl) ⟨5379695, by rfl⟩ : syracuseStep 7172927 = 10759391) B10759391
theorem B4781951 : Blo 2123435 4781951 := bstep (se 1 (by rfl) ⟨3586463, by rfl⟩ : syracuseStep 4781951 = 7172927) B7172927
theorem B3187967 : Blo 2123435 3187967 := bstep (se 1 (by rfl) ⟨2390975, by rfl⟩ : syracuseStep 3187967 = 4781951) B4781951
theorem B2125311 : Blo 2123435 2125311 := bstep (se 1 (by rfl) ⟨1593983, by rfl⟩ : syracuseStep 2125311 = 3187967) B3187967
theorem B3187973 : Blo 2123435 3187973 := bbase (se 4 (by rfl) ⟨298872, by rfl⟩ : syracuseStep 3187973 = 597745) (by norm_num)
theorem B2125315 : Blo 2123435 2125315 := bstep (se 1 (by rfl) ⟨1593986, by rfl⟩ : syracuseStep 2125315 = 3187973) B3187973
theorem B3586477 : Blo 2123435 3586477 := bbase (se 3 (by rfl) ⟨672464, by rfl⟩ : syracuseStep 3586477 = 1344929) (by norm_num)
theorem B4781969 : Blo 2123435 4781969 := bstep (se 2 (by rfl) ⟨1793238, by rfl⟩ : syracuseStep 4781969 = 3586477) B3586477
theorem B3187979 : Blo 2123435 3187979 := bstep (se 1 (by rfl) ⟨2390984, by rfl⟩ : syracuseStep 3187979 = 4781969) B4781969
theorem B2125319 : Blo 2123435 2125319 := bstep (se 1 (by rfl) ⟨1593989, by rfl⟩ : syracuseStep 2125319 = 3187979) B3187979
theorem B2390989 : Blo 2123435 2390989 := bbase (se 3 (by rfl) ⟨448310, by rfl⟩ : syracuseStep 2390989 = 896621) (by norm_num)
theorem B3187985 : Blo 2123435 3187985 := bstep (se 2 (by rfl) ⟨1195494, by rfl⟩ : syracuseStep 3187985 = 2390989) B2390989
theorem B2125323 : Blo 2123435 2125323 := bstep (se 1 (by rfl) ⟨1593992, by rfl⟩ : syracuseStep 2125323 = 3187985) B3187985
theorem B7172981 : Blo 2123435 7172981 := bbase (se 5 (by rfl) ⟨336233, by rfl⟩ : syracuseStep 7172981 = 672467) (by norm_num)
theorem B4781987 : Blo 2123435 4781987 := bstep (se 1 (by rfl) ⟨3586490, by rfl⟩ : syracuseStep 4781987 = 7172981) B7172981
theorem B3187991 : Blo 2123435 3187991 := bstep (se 1 (by rfl) ⟨2390993, by rfl⟩ : syracuseStep 3187991 = 4781987) B4781987
theorem B2125327 : Blo 2123435 2125327 := bstep (se 1 (by rfl) ⟨1593995, by rfl⟩ : syracuseStep 2125327 = 3187991) B3187991
theorem B3187997 : Blo 2123435 3187997 := bbase (se 3 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 3187997 = 1195499) (by norm_num)
theorem B2125331 : Blo 2123435 2125331 := bstep (se 1 (by rfl) ⟨1593998, by rfl⟩ : syracuseStep 2125331 = 3187997) B3187997
theorem B4782005 : Blo 2123435 4782005 := bbase (se 5 (by rfl) ⟨224156, by rfl⟩ : syracuseStep 4782005 = 448313) (by norm_num)
theorem B3188003 : Blo 2123435 3188003 := bstep (se 1 (by rfl) ⟨2391002, by rfl⟩ : syracuseStep 3188003 = 4782005) B4782005
theorem B2125335 : Blo 2123435 2125335 := bstep (se 1 (by rfl) ⟨1594001, by rfl⟩ : syracuseStep 2125335 = 3188003) B3188003
theorem B3829933 : Blo 2123435 3829933 := bbase (se 3 (by rfl) ⟨718112, by rfl⟩ : syracuseStep 3829933 = 1436225) (by norm_num)
theorem B5106577 : Blo 2123435 5106577 := bstep (se 2 (by rfl) ⟨1914966, by rfl⟩ : syracuseStep 5106577 = 3829933) B3829933
theorem B6808769 : Blo 2123435 6808769 := bstep (se 2 (by rfl) ⟨2553288, by rfl⟩ : syracuseStep 6808769 = 5106577) B5106577
theorem B4539179 : Blo 2123435 4539179 := bstep (se 1 (by rfl) ⟨3404384, by rfl⟩ : syracuseStep 4539179 = 6808769) B6808769
theorem B12104477 : Blo 2123435 12104477 := bstep (se 3 (by rfl) ⟨2269589, by rfl⟩ : syracuseStep 12104477 = 4539179) B4539179
theorem B8069651 : Blo 2123435 8069651 := bstep (se 1 (by rfl) ⟨6052238, by rfl⟩ : syracuseStep 8069651 = 12104477) B12104477
theorem B5379767 : Blo 2123435 5379767 := bstep (se 1 (by rfl) ⟨4034825, by rfl⟩ : syracuseStep 5379767 = 8069651) B8069651
theorem B3586511 : Blo 2123435 3586511 := bstep (se 1 (by rfl) ⟨2689883, by rfl⟩ : syracuseStep 3586511 = 5379767) B5379767
theorem B2391007 : Blo 2123435 2391007 := bstep (se 1 (by rfl) ⟨1793255, by rfl⟩ : syracuseStep 2391007 = 3586511) B3586511
theorem B3188009 : Blo 2123435 3188009 := bstep (se 2 (by rfl) ⟨1195503, by rfl⟩ : syracuseStep 3188009 = 2391007) B2391007
theorem B2125339 : Blo 2123435 2125339 := bstep (se 1 (by rfl) ⟨1594004, by rfl⟩ : syracuseStep 2125339 = 3188009) B3188009
theorem B2553293 : Blo 2123435 2553293 := bbase (se 3 (by rfl) ⟨478742, by rfl⟩ : syracuseStep 2553293 = 957485) (by norm_num)
theorem B6808781 : Blo 2123435 6808781 := bstep (se 3 (by rfl) ⟨1276646, by rfl⟩ : syracuseStep 6808781 = 2553293) B2553293
theorem B4539187 : Blo 2123435 4539187 := bstep (se 1 (by rfl) ⟨3404390, by rfl⟩ : syracuseStep 4539187 = 6808781) B6808781
theorem B6052249 : Blo 2123435 6052249 := bstep (se 2 (by rfl) ⟨2269593, by rfl⟩ : syracuseStep 6052249 = 4539187) B4539187
theorem B8069665 : Blo 2123435 8069665 := bstep (se 2 (by rfl) ⟨3026124, by rfl⟩ : syracuseStep 8069665 = 6052249) B6052249
theorem B10759553 : Blo 2123435 10759553 := bstep (se 2 (by rfl) ⟨4034832, by rfl⟩ : syracuseStep 10759553 = 8069665) B8069665
theorem B7173035 : Blo 2123435 7173035 := bstep (se 1 (by rfl) ⟨5379776, by rfl⟩ : syracuseStep 7173035 = 10759553) B10759553
theorem B4782023 : Blo 2123435 4782023 := bstep (se 1 (by rfl) ⟨3586517, by rfl⟩ : syracuseStep 4782023 = 7173035) B7173035
theorem B3188015 : Blo 2123435 3188015 := bstep (se 1 (by rfl) ⟨2391011, by rfl⟩ : syracuseStep 3188015 = 4782023) B4782023
theorem B2125343 : Blo 2123435 2125343 := bstep (se 1 (by rfl) ⟨1594007, by rfl⟩ : syracuseStep 2125343 = 3188015) B3188015
theorem B3188021 : Blo 2123435 3188021 := bbase (se 5 (by rfl) ⟨149438, by rfl⟩ : syracuseStep 3188021 = 298877) (by norm_num)
theorem B2125347 : Blo 2123435 2125347 := bstep (se 1 (by rfl) ⟨1594010, by rfl⟩ : syracuseStep 2125347 = 3188021) B3188021
theorem B5379797 : Blo 2123435 5379797 := bbase (se 7 (by rfl) ⟨63044, by rfl⟩ : syracuseStep 5379797 = 126089) (by norm_num)
theorem B3586531 : Blo 2123435 3586531 := bstep (se 1 (by rfl) ⟨2689898, by rfl⟩ : syracuseStep 3586531 = 5379797) B5379797
theorem B4782041 : Blo 2123435 4782041 := bstep (se 2 (by rfl) ⟨1793265, by rfl⟩ : syracuseStep 4782041 = 3586531) B3586531
theorem B3188027 : Blo 2123435 3188027 := bstep (se 1 (by rfl) ⟨2391020, by rfl⟩ : syracuseStep 3188027 = 4782041) B4782041
theorem B2125351 : Blo 2123435 2125351 := bstep (se 1 (by rfl) ⟨1594013, by rfl⟩ : syracuseStep 2125351 = 3188027) B3188027
theorem B2391025 : Blo 2123435 2391025 := bbase (se 2 (by rfl) ⟨896634, by rfl⟩ : syracuseStep 2391025 = 1793269) (by norm_num)
theorem B3188033 : Blo 2123435 3188033 := bstep (se 2 (by rfl) ⟨1195512, by rfl⟩ : syracuseStep 3188033 = 2391025) B2391025
theorem B2125355 : Blo 2123435 2125355 := bstep (se 1 (by rfl) ⟨1594016, by rfl⟩ : syracuseStep 2125355 = 3188033) B3188033
theorem B8179829 : Blo 2123435 8179829 := bbase (se 5 (by rfl) ⟨383429, by rfl⟩ : syracuseStep 8179829 = 766859) (by norm_num)
theorem B5453219 : Blo 2123435 5453219 := bstep (se 1 (by rfl) ⟨4089914, by rfl⟩ : syracuseStep 5453219 = 8179829) B8179829
theorem B3635479 : Blo 2123435 3635479 := bstep (se 1 (by rfl) ⟨2726609, by rfl⟩ : syracuseStep 3635479 = 5453219) B5453219
theorem B4847305 : Blo 2123435 4847305 := bstep (se 2 (by rfl) ⟨1817739, by rfl⟩ : syracuseStep 4847305 = 3635479) B3635479
theorem B6463073 : Blo 2123435 6463073 := bstep (se 2 (by rfl) ⟨2423652, by rfl⟩ : syracuseStep 6463073 = 4847305) B4847305
theorem B4308715 : Blo 2123435 4308715 := bstep (se 1 (by rfl) ⟨3231536, by rfl⟩ : syracuseStep 4308715 = 6463073) B6463073
theorem B5744953 : Blo 2123435 5744953 := bstep (se 2 (by rfl) ⟨2154357, by rfl⟩ : syracuseStep 5744953 = 4308715) B4308715
theorem B7659937 : Blo 2123435 7659937 := bstep (se 2 (by rfl) ⟨2872476, by rfl⟩ : syracuseStep 7659937 = 5744953) B5744953
theorem B10213249 : Blo 2123435 10213249 := bstep (se 2 (by rfl) ⟨3829968, by rfl⟩ : syracuseStep 10213249 = 7659937) B7659937
theorem B13617665 : Blo 2123435 13617665 := bstep (se 2 (by rfl) ⟨5106624, by rfl⟩ : syracuseStep 13617665 = 10213249) B10213249
theorem B9078443 : Blo 2123435 9078443 := bstep (se 1 (by rfl) ⟨6808832, by rfl⟩ : syracuseStep 9078443 = 13617665) B13617665
theorem B6052295 : Blo 2123435 6052295 := bstep (se 1 (by rfl) ⟨4539221, by rfl⟩ : syracuseStep 6052295 = 9078443) B9078443
theorem B4034863 : Blo 2123435 4034863 := bstep (se 1 (by rfl) ⟨3026147, by rfl⟩ : syracuseStep 4034863 = 6052295) B6052295
theorem B5379817 : Blo 2123435 5379817 := bstep (se 2 (by rfl) ⟨2017431, by rfl⟩ : syracuseStep 5379817 = 4034863) B4034863
theorem B7173089 : Blo 2123435 7173089 := bstep (se 2 (by rfl) ⟨2689908, by rfl⟩ : syracuseStep 7173089 = 5379817) B5379817
theorem B4782059 : Blo 2123435 4782059 := bstep (se 1 (by rfl) ⟨3586544, by rfl⟩ : syracuseStep 4782059 = 7173089) B7173089
theorem B3188039 : Blo 2123435 3188039 := bstep (se 1 (by rfl) ⟨2391029, by rfl⟩ : syracuseStep 3188039 = 4782059) B4782059
theorem B2125359 : Blo 2123435 2125359 := bstep (se 1 (by rfl) ⟨1594019, by rfl⟩ : syracuseStep 2125359 = 3188039) B3188039
theorem B3188045 : Blo 2123435 3188045 := bbase (se 3 (by rfl) ⟨597758, by rfl⟩ : syracuseStep 3188045 = 1195517) (by norm_num)
theorem B2125363 : Blo 2123435 2125363 := bstep (se 1 (by rfl) ⟨1594022, by rfl⟩ : syracuseStep 2125363 = 3188045) B3188045
theorem B4782077 : Blo 2123435 4782077 := bbase (se 3 (by rfl) ⟨896639, by rfl⟩ : syracuseStep 4782077 = 1793279) (by norm_num)
theorem B3188051 : Blo 2123435 3188051 := bstep (se 1 (by rfl) ⟨2391038, by rfl⟩ : syracuseStep 3188051 = 4782077) B4782077
theorem B2125367 : Blo 2123435 2125367 := bstep (se 1 (by rfl) ⟨1594025, by rfl⟩ : syracuseStep 2125367 = 3188051) B3188051
theorem B3586565 : Blo 2123435 3586565 := bbase (se 4 (by rfl) ⟨336240, by rfl⟩ : syracuseStep 3586565 = 672481) (by norm_num)
theorem B2391043 : Blo 2123435 2391043 := bstep (se 1 (by rfl) ⟨1793282, by rfl⟩ : syracuseStep 2391043 = 3586565) B3586565
theorem B3188057 : Blo 2123435 3188057 := bstep (se 2 (by rfl) ⟨1195521, by rfl⟩ : syracuseStep 3188057 = 2391043) B2391043
theorem B2125371 : Blo 2123435 2125371 := bstep (se 1 (by rfl) ⟨1594028, by rfl⟩ : syracuseStep 2125371 = 3188057) B3188057
theorem B16139573 : Blo 2123435 16139573 := bbase (se 5 (by rfl) ⟨756542, by rfl⟩ : syracuseStep 16139573 = 1513085) (by norm_num)
theorem B10759715 : Blo 2123435 10759715 := bstep (se 1 (by rfl) ⟨8069786, by rfl⟩ : syracuseStep 10759715 = 16139573) B16139573
theorem B7173143 : Blo 2123435 7173143 := bstep (se 1 (by rfl) ⟨5379857, by rfl⟩ : syracuseStep 7173143 = 10759715) B10759715
theorem B4782095 : Blo 2123435 4782095 := bstep (se 1 (by rfl) ⟨3586571, by rfl⟩ : syracuseStep 4782095 = 7173143) B7173143
theorem B3188063 : Blo 2123435 3188063 := bstep (se 1 (by rfl) ⟨2391047, by rfl⟩ : syracuseStep 3188063 = 4782095) B4782095
theorem B2125375 : Blo 2123435 2125375 := bstep (se 1 (by rfl) ⟨1594031, by rfl⟩ : syracuseStep 2125375 = 3188063) B3188063
theorem B3188069 : Blo 2123435 3188069 := bbase (se 4 (by rfl) ⟨298881, by rfl⟩ : syracuseStep 3188069 = 597763) (by norm_num)
theorem B2125379 : Blo 2123435 2125379 := bstep (se 1 (by rfl) ⟨1594034, by rfl⟩ : syracuseStep 2125379 = 3188069) B3188069
theorem B4034909 : Blo 2123435 4034909 := bbase (se 3 (by rfl) ⟨756545, by rfl⟩ : syracuseStep 4034909 = 1513091) (by norm_num)
theorem B2689939 : Blo 2123435 2689939 := bstep (se 1 (by rfl) ⟨2017454, by rfl⟩ : syracuseStep 2689939 = 4034909) B4034909
theorem B3586585 : Blo 2123435 3586585 := bstep (se 2 (by rfl) ⟨1344969, by rfl⟩ : syracuseStep 3586585 = 2689939) B2689939
theorem B4782113 : Blo 2123435 4782113 := bstep (se 2 (by rfl) ⟨1793292, by rfl⟩ : syracuseStep 4782113 = 3586585) B3586585
theorem B3188075 : Blo 2123435 3188075 := bstep (se 1 (by rfl) ⟨2391056, by rfl⟩ : syracuseStep 3188075 = 4782113) B4782113
theorem B2125383 : Blo 2123435 2125383 := bstep (se 1 (by rfl) ⟨1594037, by rfl⟩ : syracuseStep 2125383 = 3188075) B3188075
theorem B2391061 : Blo 2123435 2391061 := bbase (se 6 (by rfl) ⟨56040, by rfl⟩ : syracuseStep 2391061 = 112081) (by norm_num)
theorem B3188081 : Blo 2123435 3188081 := bstep (se 2 (by rfl) ⟨1195530, by rfl⟩ : syracuseStep 3188081 = 2391061) B2391061
theorem B2125387 : Blo 2123435 2125387 := bstep (se 1 (by rfl) ⟨1594040, by rfl⟩ : syracuseStep 2125387 = 3188081) B3188081
theorem B2689949 : Blo 2123435 2689949 := bbase (se 3 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 2689949 = 1008731) (by norm_num)
theorem B7173197 : Blo 2123435 7173197 := bstep (se 3 (by rfl) ⟨1344974, by rfl⟩ : syracuseStep 7173197 = 2689949) B2689949
theorem B4782131 : Blo 2123435 4782131 := bstep (se 1 (by rfl) ⟨3586598, by rfl⟩ : syracuseStep 4782131 = 7173197) B7173197
theorem B3188087 : Blo 2123435 3188087 := bstep (se 1 (by rfl) ⟨2391065, by rfl⟩ : syracuseStep 3188087 = 4782131) B4782131
theorem B2125391 : Blo 2123435 2125391 := bstep (se 1 (by rfl) ⟨1594043, by rfl⟩ : syracuseStep 2125391 = 3188087) B3188087
theorem B3188093 : Blo 2123435 3188093 := bbase (se 3 (by rfl) ⟨597767, by rfl⟩ : syracuseStep 3188093 = 1195535) (by norm_num)
theorem B2125395 : Blo 2123435 2125395 := bstep (se 1 (by rfl) ⟨1594046, by rfl⟩ : syracuseStep 2125395 = 3188093) B3188093
theorem B4782149 : Blo 2123435 4782149 := bbase (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) (by norm_num)
theorem B3188099 : Blo 2123435 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B2125399 : Blo 2123435 2125399 := bstep (se 1 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 2125399 = 3188099) B3188099
theorem B6052421 : Blo 2123435 6052421 := bbase (se 4 (by rfl) ⟨567414, by rfl⟩ : syracuseStep 6052421 = 1134829) (by norm_num)
theorem B4034947 : Blo 2123435 4034947 := bstep (se 1 (by rfl) ⟨3026210, by rfl⟩ : syracuseStep 4034947 = 6052421) B6052421
theorem B5379929 : Blo 2123435 5379929 := bstep (se 2 (by rfl) ⟨2017473, by rfl⟩ : syracuseStep 5379929 = 4034947) B4034947
theorem B3586619 : Blo 2123435 3586619 := bstep (se 1 (by rfl) ⟨2689964, by rfl⟩ : syracuseStep 3586619 = 5379929) B5379929
theorem B2391079 : Blo 2123435 2391079 := bstep (se 1 (by rfl) ⟨1793309, by rfl⟩ : syracuseStep 2391079 = 3586619) B3586619
theorem B3188105 : Blo 2123435 3188105 := bstep (se 2 (by rfl) ⟨1195539, by rfl⟩ : syracuseStep 3188105 = 2391079) B2391079
theorem B2125403 : Blo 2123435 2125403 := bstep (se 1 (by rfl) ⟨1594052, by rfl⟩ : syracuseStep 2125403 = 3188105) B3188105
theorem B10759877 : Blo 2123435 10759877 := bbase (se 4 (by rfl) ⟨1008738, by rfl⟩ : syracuseStep 10759877 = 2017477) (by norm_num)
theorem B7173251 : Blo 2123435 7173251 := bstep (se 1 (by rfl) ⟨5379938, by rfl⟩ : syracuseStep 7173251 = 10759877) B10759877
theorem B4782167 : Blo 2123435 4782167 := bstep (se 1 (by rfl) ⟨3586625, by rfl⟩ : syracuseStep 4782167 = 7173251) B7173251
theorem B3188111 : Blo 2123435 3188111 := bstep (se 1 (by rfl) ⟨2391083, by rfl⟩ : syracuseStep 3188111 = 4782167) B4782167
theorem B2125407 : Blo 2123435 2125407 := bstep (se 1 (by rfl) ⟨1594055, by rfl⟩ : syracuseStep 2125407 = 3188111) B3188111
theorem B3188117 : Blo 2123435 3188117 := bbase (se 6 (by rfl) ⟨74721, by rfl⟩ : syracuseStep 3188117 = 149443) (by norm_num)
theorem B2125411 : Blo 2123435 2125411 := bstep (se 1 (by rfl) ⟨1594058, by rfl⟩ : syracuseStep 2125411 = 3188117) B3188117
theorem B4539341 : Blo 2123435 4539341 := bbase (se 3 (by rfl) ⟨851126, by rfl⟩ : syracuseStep 4539341 = 1702253) (by norm_num)
theorem B12104909 : Blo 2123435 12104909 := bstep (se 3 (by rfl) ⟨2269670, by rfl⟩ : syracuseStep 12104909 = 4539341) B4539341
theorem B8069939 : Blo 2123435 8069939 := bstep (se 1 (by rfl) ⟨6052454, by rfl⟩ : syracuseStep 8069939 = 12104909) B12104909
theorem B5379959 : Blo 2123435 5379959 := bstep (se 1 (by rfl) ⟨4034969, by rfl⟩ : syracuseStep 5379959 = 8069939) B8069939
theorem B3586639 : Blo 2123435 3586639 := bstep (se 1 (by rfl) ⟨2689979, by rfl⟩ : syracuseStep 3586639 = 5379959) B5379959
theorem B4782185 : Blo 2123435 4782185 := bstep (se 2 (by rfl) ⟨1793319, by rfl⟩ : syracuseStep 4782185 = 3586639) B3586639
theorem B3188123 : Blo 2123435 3188123 := bstep (se 1 (by rfl) ⟨2391092, by rfl⟩ : syracuseStep 3188123 = 4782185) B4782185
theorem B2125415 : Blo 2123435 2125415 := bstep (se 1 (by rfl) ⟨1594061, by rfl⟩ : syracuseStep 2125415 = 3188123) B3188123
theorem B2391097 : Blo 2123435 2391097 := bbase (se 2 (by rfl) ⟨896661, by rfl⟩ : syracuseStep 2391097 = 1793323) (by norm_num)
theorem B3188129 : Blo 2123435 3188129 := bstep (se 2 (by rfl) ⟨1195548, by rfl⟩ : syracuseStep 3188129 = 2391097) B2391097
theorem B2125419 : Blo 2123435 2125419 := bstep (se 1 (by rfl) ⟨1594064, by rfl⟩ : syracuseStep 2125419 = 3188129) B3188129
theorem B3882341 : Blo 2123435 3882341 := bbase (se 4 (by rfl) ⟨363969, by rfl⟩ : syracuseStep 3882341 = 727939) (by norm_num)
theorem B10352909 : Blo 2123435 10352909 := bstep (se 3 (by rfl) ⟨1941170, by rfl⟩ : syracuseStep 10352909 = 3882341) B3882341
theorem B6901939 : Blo 2123435 6901939 := bstep (se 1 (by rfl) ⟨5176454, by rfl⟩ : syracuseStep 6901939 = 10352909) B10352909
theorem B9202585 : Blo 2123435 9202585 := bstep (se 2 (by rfl) ⟨3450969, by rfl⟩ : syracuseStep 9202585 = 6901939) B6901939
theorem B12270113 : Blo 2123435 12270113 := bstep (se 2 (by rfl) ⟨4601292, by rfl⟩ : syracuseStep 12270113 = 9202585) B9202585
theorem B8180075 : Blo 2123435 8180075 := bstep (se 1 (by rfl) ⟨6135056, by rfl⟩ : syracuseStep 8180075 = 12270113) B12270113
theorem B21813533 : Blo 2123435 21813533 := bstep (se 3 (by rfl) ⟨4090037, by rfl⟩ : syracuseStep 21813533 = 8180075) B8180075
theorem B14542355 : Blo 2123435 14542355 := bstep (se 1 (by rfl) ⟨10906766, by rfl⟩ : syracuseStep 14542355 = 21813533) B21813533
theorem B9694903 : Blo 2123435 9694903 := bstep (se 1 (by rfl) ⟨7271177, by rfl⟩ : syracuseStep 9694903 = 14542355) B14542355
theorem B12926537 : Blo 2123435 12926537 := bstep (se 2 (by rfl) ⟨4847451, by rfl⟩ : syracuseStep 12926537 = 9694903) B9694903
theorem B8617691 : Blo 2123435 8617691 := bstep (se 1 (by rfl) ⟨6463268, by rfl⟩ : syracuseStep 8617691 = 12926537) B12926537
theorem B5745127 : Blo 2123435 5745127 := bstep (se 1 (by rfl) ⟨4308845, by rfl⟩ : syracuseStep 5745127 = 8617691) B8617691
theorem B7660169 : Blo 2123435 7660169 := bstep (se 2 (by rfl) ⟨2872563, by rfl⟩ : syracuseStep 7660169 = 5745127) B5745127
theorem B5106779 : Blo 2123435 5106779 := bstep (se 1 (by rfl) ⟨3830084, by rfl⟩ : syracuseStep 5106779 = 7660169) B7660169
theorem B3404519 : Blo 2123435 3404519 := bstep (se 1 (by rfl) ⟨2553389, by rfl⟩ : syracuseStep 3404519 = 5106779) B5106779
theorem B2269679 : Blo 2123435 2269679 := bstep (se 1 (by rfl) ⟨1702259, by rfl⟩ : syracuseStep 2269679 = 3404519) B3404519
theorem B6052477 : Blo 2123435 6052477 := bstep (se 3 (by rfl) ⟨1134839, by rfl⟩ : syracuseStep 6052477 = 2269679) B2269679
theorem B8069969 : Blo 2123435 8069969 := bstep (se 2 (by rfl) ⟨3026238, by rfl⟩ : syracuseStep 8069969 = 6052477) B6052477
theorem B5379979 : Blo 2123435 5379979 := bstep (se 1 (by rfl) ⟨4034984, by rfl⟩ : syracuseStep 5379979 = 8069969) B8069969
theorem B7173305 : Blo 2123435 7173305 := bstep (se 2 (by rfl) ⟨2689989, by rfl⟩ : syracuseStep 7173305 = 5379979) B5379979
theorem B4782203 : Blo 2123435 4782203 := bstep (se 1 (by rfl) ⟨3586652, by rfl⟩ : syracuseStep 4782203 = 7173305) B7173305
theorem B3188135 : Blo 2123435 3188135 := bstep (se 1 (by rfl) ⟨2391101, by rfl⟩ : syracuseStep 3188135 = 4782203) B4782203
theorem B2125423 : Blo 2123435 2125423 := bstep (se 1 (by rfl) ⟨1594067, by rfl⟩ : syracuseStep 2125423 = 3188135) B3188135
theorem B3188141 : Blo 2123435 3188141 := bbase (se 3 (by rfl) ⟨597776, by rfl⟩ : syracuseStep 3188141 = 1195553) (by norm_num)
theorem B2125427 : Blo 2123435 2125427 := bstep (se 1 (by rfl) ⟨1594070, by rfl⟩ : syracuseStep 2125427 = 3188141) B3188141
theorem B4782221 : Blo 2123435 4782221 := bbase (se 3 (by rfl) ⟨896666, by rfl⟩ : syracuseStep 4782221 = 1793333) (by norm_num)
theorem B3188147 : Blo 2123435 3188147 := bstep (se 1 (by rfl) ⟨2391110, by rfl⟩ : syracuseStep 3188147 = 4782221) B4782221
theorem B2125431 : Blo 2123435 2125431 := bstep (se 1 (by rfl) ⟨1594073, by rfl⟩ : syracuseStep 2125431 = 3188147) B3188147
theorem B2690005 : Blo 2123435 2690005 := bbase (se 7 (by rfl) ⟨31523, by rfl⟩ : syracuseStep 2690005 = 63047) (by norm_num)
theorem B3586673 : Blo 2123435 3586673 := bstep (se 2 (by rfl) ⟨1345002, by rfl⟩ : syracuseStep 3586673 = 2690005) B2690005
theorem B2391115 : Blo 2123435 2391115 := bstep (se 1 (by rfl) ⟨1793336, by rfl⟩ : syracuseStep 2391115 = 3586673) B3586673
theorem B3188153 : Blo 2123435 3188153 := bstep (se 2 (by rfl) ⟨1195557, by rfl⟩ : syracuseStep 3188153 = 2391115) B2391115
theorem B2125435 : Blo 2123435 2125435 := bstep (se 1 (by rfl) ⟨1594076, by rfl⟩ : syracuseStep 2125435 = 3188153) B3188153
theorem C0 (j : ℕ) (h1 : 530858 ≤ j) (h2 : j ≤ 531358) : Blo 2123435 (4 * j + 3) := by
  interval_cases j
  · exact B2123435
  · exact B2123439
  · exact B2123443
  · exact B2123447
  · exact B2123451
  · exact B2123455
  · exact B2123459
  · exact B2123463
  · exact B2123467
  · exact B2123471
  · exact B2123475
  · exact B2123479
  · exact B2123483
  · exact B2123487
  · exact B2123491
  · exact B2123495
  · exact B2123499
  · exact B2123503
  · exact B2123507
  · exact B2123511
  · exact B2123515
  · exact B2123519
  · exact B2123523
  · exact B2123527
  · exact B2123531
  · exact B2123535
  · exact B2123539
  · exact B2123543
  · exact B2123547
  · exact B2123551
  · exact B2123555
  · exact B2123559
  · exact B2123563
  · exact B2123567
  · exact B2123571
  · exact B2123575
  · exact B2123579
  · exact B2123583
  · exact B2123587
  · exact B2123591
  · exact B2123595
  · exact B2123599
  · exact B2123603
  · exact B2123607
  · exact B2123611
  · exact B2123615
  · exact B2123619
  · exact B2123623
  · exact B2123627
  · exact B2123631
  · exact B2123635
  · exact B2123639
  · exact B2123643
  · exact B2123647
  · exact B2123651
  · exact B2123655
  · exact B2123659
  · exact B2123663
  · exact B2123667
  · exact B2123671
  · exact B2123675
  · exact B2123679
  · exact B2123683
  · exact B2123687
  · exact B2123691
  · exact B2123695
  · exact B2123699
  · exact B2123703
  · exact B2123707
  · exact B2123711
  · exact B2123715
  · exact B2123719
  · exact B2123723
  · exact B2123727
  · exact B2123731
  · exact B2123735
  · exact B2123739
  · exact B2123743
  · exact B2123747
  · exact B2123751
  · exact B2123755
  · exact B2123759
  · exact B2123763
  · exact B2123767
  · exact B2123771
  · exact B2123775
  · exact B2123779
  · exact B2123783
  · exact B2123787
  · exact B2123791
  · exact B2123795
  · exact B2123799
  · exact B2123803
  · exact B2123807
  · exact B2123811
  · exact B2123815
  · exact B2123819
  · exact B2123823
  · exact B2123827
  · exact B2123831
  · exact B2123835
  · exact B2123839
  · exact B2123843
  · exact B2123847
  · exact B2123851
  · exact B2123855
  · exact B2123859
  · exact B2123863
  · exact B2123867
  · exact B2123871
  · exact B2123875
  · exact B2123879
  · exact B2123883
  · exact B2123887
  · exact B2123891
  · exact B2123895
  · exact B2123899
  · exact B2123903
  · exact B2123907
  · exact B2123911
  · exact B2123915
  · exact B2123919
  · exact B2123923
  · exact B2123927
  · exact B2123931
  · exact B2123935
  · exact B2123939
  · exact B2123943
  · exact B2123947
  · exact B2123951
  · exact B2123955
  · exact B2123959
  · exact B2123963
  · exact B2123967
  · exact B2123971
  · exact B2123975
  · exact B2123979
  · exact B2123983
  · exact B2123987
  · exact B2123991
  · exact B2123995
  · exact B2123999
  · exact B2124003
  · exact B2124007
  · exact B2124011
  · exact B2124015
  · exact B2124019
  · exact B2124023
  · exact B2124027
  · exact B2124031
  · exact B2124035
  · exact B2124039
  · exact B2124043
  · exact B2124047
  · exact B2124051
  · exact B2124055
  · exact B2124059
  · exact B2124063
  · exact B2124067
  · exact B2124071
  · exact B2124075
  · exact B2124079
  · exact B2124083
  · exact B2124087
  · exact B2124091
  · exact B2124095
  · exact B2124099
  · exact B2124103
  · exact B2124107
  · exact B2124111
  · exact B2124115
  · exact B2124119
  · exact B2124123
  · exact B2124127
  · exact B2124131
  · exact B2124135
  · exact B2124139
  · exact B2124143
  · exact B2124147
  · exact B2124151
  · exact B2124155
  · exact B2124159
  · exact B2124163
  · exact B2124167
  · exact B2124171
  · exact B2124175
  · exact B2124179
  · exact B2124183
  · exact B2124187
  · exact B2124191
  · exact B2124195
  · exact B2124199
  · exact B2124203
  · exact B2124207
  · exact B2124211
  · exact B2124215
  · exact B2124219
  · exact B2124223
  · exact B2124227
  · exact B2124231
  · exact B2124235
  · exact B2124239
  · exact B2124243
  · exact B2124247
  · exact B2124251
  · exact B2124255
  · exact B2124259
  · exact B2124263
  · exact B2124267
  · exact B2124271
  · exact B2124275
  · exact B2124279
  · exact B2124283
  · exact B2124287
  · exact B2124291
  · exact B2124295
  · exact B2124299
  · exact B2124303
  · exact B2124307
  · exact B2124311
  · exact B2124315
  · exact B2124319
  · exact B2124323
  · exact B2124327
  · exact B2124331
  · exact B2124335
  · exact B2124339
  · exact B2124343
  · exact B2124347
  · exact B2124351
  · exact B2124355
  · exact B2124359
  · exact B2124363
  · exact B2124367
  · exact B2124371
  · exact B2124375
  · exact B2124379
  · exact B2124383
  · exact B2124387
  · exact B2124391
  · exact B2124395
  · exact B2124399
  · exact B2124403
  · exact B2124407
  · exact B2124411
  · exact B2124415
  · exact B2124419
  · exact B2124423
  · exact B2124427
  · exact B2124431
  · exact B2124435
  · exact B2124439
  · exact B2124443
  · exact B2124447
  · exact B2124451
  · exact B2124455
  · exact B2124459
  · exact B2124463
  · exact B2124467
  · exact B2124471
  · exact B2124475
  · exact B2124479
  · exact B2124483
  · exact B2124487
  · exact B2124491
  · exact B2124495
  · exact B2124499
  · exact B2124503
  · exact B2124507
  · exact B2124511
  · exact B2124515
  · exact B2124519
  · exact B2124523
  · exact B2124527
  · exact B2124531
  · exact B2124535
  · exact B2124539
  · exact B2124543
  · exact B2124547
  · exact B2124551
  · exact B2124555
  · exact B2124559
  · exact B2124563
  · exact B2124567
  · exact B2124571
  · exact B2124575
  · exact B2124579
  · exact B2124583
  · exact B2124587
  · exact B2124591
  · exact B2124595
  · exact B2124599
  · exact B2124603
  · exact B2124607
  · exact B2124611
  · exact B2124615
  · exact B2124619
  · exact B2124623
  · exact B2124627
  · exact B2124631
  · exact B2124635
  · exact B2124639
  · exact B2124643
  · exact B2124647
  · exact B2124651
  · exact B2124655
  · exact B2124659
  · exact B2124663
  · exact B2124667
  · exact B2124671
  · exact B2124675
  · exact B2124679
  · exact B2124683
  · exact B2124687
  · exact B2124691
  · exact B2124695
  · exact B2124699
  · exact B2124703
  · exact B2124707
  · exact B2124711
  · exact B2124715
  · exact B2124719
  · exact B2124723
  · exact B2124727
  · exact B2124731
  · exact B2124735
  · exact B2124739
  · exact B2124743
  · exact B2124747
  · exact B2124751
  · exact B2124755
  · exact B2124759
  · exact B2124763
  · exact B2124767
  · exact B2124771
  · exact B2124775
  · exact B2124779
  · exact B2124783
  · exact B2124787
  · exact B2124791
  · exact B2124795
  · exact B2124799
  · exact B2124803
  · exact B2124807
  · exact B2124811
  · exact B2124815
  · exact B2124819
  · exact B2124823
  · exact B2124827
  · exact B2124831
  · exact B2124835
  · exact B2124839
  · exact B2124843
  · exact B2124847
  · exact B2124851
  · exact B2124855
  · exact B2124859
  · exact B2124863
  · exact B2124867
  · exact B2124871
  · exact B2124875
  · exact B2124879
  · exact B2124883
  · exact B2124887
  · exact B2124891
  · exact B2124895
  · exact B2124899
  · exact B2124903
  · exact B2124907
  · exact B2124911
  · exact B2124915
  · exact B2124919
  · exact B2124923
  · exact B2124927
  · exact B2124931
  · exact B2124935
  · exact B2124939
  · exact B2124943
  · exact B2124947
  · exact B2124951
  · exact B2124955
  · exact B2124959
  · exact B2124963
  · exact B2124967
  · exact B2124971
  · exact B2124975
  · exact B2124979
  · exact B2124983
  · exact B2124987
  · exact B2124991
  · exact B2124995
  · exact B2124999
  · exact B2125003
  · exact B2125007
  · exact B2125011
  · exact B2125015
  · exact B2125019
  · exact B2125023
  · exact B2125027
  · exact B2125031
  · exact B2125035
  · exact B2125039
  · exact B2125043
  · exact B2125047
  · exact B2125051
  · exact B2125055
  · exact B2125059
  · exact B2125063
  · exact B2125067
  · exact B2125071
  · exact B2125075
  · exact B2125079
  · exact B2125083
  · exact B2125087
  · exact B2125091
  · exact B2125095
  · exact B2125099
  · exact B2125103
  · exact B2125107
  · exact B2125111
  · exact B2125115
  · exact B2125119
  · exact B2125123
  · exact B2125127
  · exact B2125131
  · exact B2125135
  · exact B2125139
  · exact B2125143
  · exact B2125147
  · exact B2125151
  · exact B2125155
  · exact B2125159
  · exact B2125163
  · exact B2125167
  · exact B2125171
  · exact B2125175
  · exact B2125179
  · exact B2125183
  · exact B2125187
  · exact B2125191
  · exact B2125195
  · exact B2125199
  · exact B2125203
  · exact B2125207
  · exact B2125211
  · exact B2125215
  · exact B2125219
  · exact B2125223
  · exact B2125227
  · exact B2125231
  · exact B2125235
  · exact B2125239
  · exact B2125243
  · exact B2125247
  · exact B2125251
  · exact B2125255
  · exact B2125259
  · exact B2125263
  · exact B2125267
  · exact B2125271
  · exact B2125275
  · exact B2125279
  · exact B2125283
  · exact B2125287
  · exact B2125291
  · exact B2125295
  · exact B2125299
  · exact B2125303
  · exact B2125307
  · exact B2125311
  · exact B2125315
  · exact B2125319
  · exact B2125323
  · exact B2125327
  · exact B2125331
  · exact B2125335
  · exact B2125339
  · exact B2125343
  · exact B2125347
  · exact B2125351
  · exact B2125355
  · exact B2125359
  · exact B2125363
  · exact B2125367
  · exact B2125371
  · exact B2125375
  · exact B2125379
  · exact B2125383
  · exact B2125387
  · exact B2125391
  · exact B2125395
  · exact B2125399
  · exact B2125403
  · exact B2125407
  · exact B2125411
  · exact B2125415
  · exact B2125419
  · exact B2125423
  · exact B2125427
  · exact B2125431
  · exact B2125435
theorem solution (m : ℕ) (hlo : 2123435 ≤ m) (hhi : m ≤ 2125435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 530858 ≤ j := by omega
    have hj2 : j ≤ 531358 := by omega
    have hb : Blo 2123435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
