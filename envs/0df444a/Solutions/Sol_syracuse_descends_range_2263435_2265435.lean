-- Prove2me | solution 1 for syracuse_descends_range_2263435_2265435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:20.587176+00:00
-- url     : https://prove2.me/submissions/68afff62-fc24-41db-a294-7aac0dc05dc8

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

theorem B2546365 : Blo 2263435 2546365 := bbase (se 3 (by rfl) ⟨477443, by rfl⟩ : syracuseStep 2546365 = 954887) (by norm_num)
theorem B3395153 : Blo 2263435 3395153 := bstep (se 2 (by rfl) ⟨1273182, by rfl⟩ : syracuseStep 3395153 = 2546365) B2546365
theorem B2263435 : Blo 2263435 2263435 := bstep (se 1 (by rfl) ⟨1697576, by rfl⟩ : syracuseStep 2263435 = 3395153) B3395153
theorem B7639109 : Blo 2263435 7639109 := bbase (se 4 (by rfl) ⟨716166, by rfl⟩ : syracuseStep 7639109 = 1432333) (by norm_num)
theorem B5092739 : Blo 2263435 5092739 := bstep (se 1 (by rfl) ⟨3819554, by rfl⟩ : syracuseStep 5092739 = 7639109) B7639109
theorem B3395159 : Blo 2263435 3395159 := bstep (se 1 (by rfl) ⟨2546369, by rfl⟩ : syracuseStep 3395159 = 5092739) B5092739
theorem B2263439 : Blo 2263435 2263439 := bstep (se 1 (by rfl) ⟨1697579, by rfl⟩ : syracuseStep 2263439 = 3395159) B3395159
theorem B3395165 : Blo 2263435 3395165 := bbase (se 3 (by rfl) ⟨636593, by rfl⟩ : syracuseStep 3395165 = 1273187) (by norm_num)
theorem B2263443 : Blo 2263435 2263443 := bstep (se 1 (by rfl) ⟨1697582, by rfl⟩ : syracuseStep 2263443 = 3395165) B3395165
theorem B5092757 : Blo 2263435 5092757 := bbase (se 6 (by rfl) ⟨119361, by rfl⟩ : syracuseStep 5092757 = 238723) (by norm_num)
theorem B3395171 : Blo 2263435 3395171 := bstep (se 1 (by rfl) ⟨2546378, by rfl⟩ : syracuseStep 3395171 = 5092757) B5092757
theorem B2263447 : Blo 2263435 2263447 := bstep (se 1 (by rfl) ⟨1697585, by rfl⟩ : syracuseStep 2263447 = 3395171) B3395171
theorem B2983541 : Blo 2263435 2983541 := bbase (se 5 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 2983541 = 279707) (by norm_num)
theorem B7956109 : Blo 2263435 7956109 := bstep (se 3 (by rfl) ⟨1491770, by rfl⟩ : syracuseStep 7956109 = 2983541) B2983541
theorem B42432581 : Blo 2263435 42432581 := bstep (se 4 (by rfl) ⟨3978054, by rfl⟩ : syracuseStep 42432581 = 7956109) B7956109
theorem B28288387 : Blo 2263435 28288387 := bstep (se 1 (by rfl) ⟨21216290, by rfl⟩ : syracuseStep 28288387 = 42432581) B42432581
theorem B37717849 : Blo 2263435 37717849 := bstep (se 2 (by rfl) ⟨14144193, by rfl⟩ : syracuseStep 37717849 = 28288387) B28288387
theorem B50290465 : Blo 2263435 50290465 := bstep (se 2 (by rfl) ⟨18858924, by rfl⟩ : syracuseStep 50290465 = 37717849) B37717849
theorem B67053953 : Blo 2263435 67053953 := bstep (se 2 (by rfl) ⟨25145232, by rfl⟩ : syracuseStep 67053953 = 50290465) B50290465
theorem B178810541 : Blo 2263435 178810541 := bstep (se 3 (by rfl) ⟨33526976, by rfl⟩ : syracuseStep 178810541 = 67053953) B67053953
theorem B119207027 : Blo 2263435 119207027 := bstep (se 1 (by rfl) ⟨89405270, by rfl⟩ : syracuseStep 119207027 = 178810541) B178810541
theorem B317885405 : Blo 2263435 317885405 := bstep (se 3 (by rfl) ⟨59603513, by rfl⟩ : syracuseStep 317885405 = 119207027) B119207027
theorem B847694413 : Blo 2263435 847694413 := bstep (se 3 (by rfl) ⟨158942702, by rfl⟩ : syracuseStep 847694413 = 317885405) B317885405
theorem B1130259217 : Blo 2263435 1130259217 := bstep (se 2 (by rfl) ⟨423847206, by rfl⟩ : syracuseStep 1130259217 = 847694413) B847694413
theorem B1507012289 : Blo 2263435 1507012289 := bstep (se 2 (by rfl) ⟨565129608, by rfl⟩ : syracuseStep 1507012289 = 1130259217) B1130259217
theorem B1004674859 : Blo 2263435 1004674859 := bstep (se 1 (by rfl) ⟨753506144, by rfl⟩ : syracuseStep 1004674859 = 1507012289) B1507012289
theorem B669783239 : Blo 2263435 669783239 := bstep (se 1 (by rfl) ⟨502337429, by rfl⟩ : syracuseStep 669783239 = 1004674859) B1004674859
theorem B446522159 : Blo 2263435 446522159 := bstep (se 1 (by rfl) ⟨334891619, by rfl⟩ : syracuseStep 446522159 = 669783239) B669783239
theorem B297681439 : Blo 2263435 297681439 := bstep (se 1 (by rfl) ⟨223261079, by rfl⟩ : syracuseStep 297681439 = 446522159) B446522159
theorem B396908585 : Blo 2263435 396908585 := bstep (se 2 (by rfl) ⟨148840719, by rfl⟩ : syracuseStep 396908585 = 297681439) B297681439
theorem B264605723 : Blo 2263435 264605723 := bstep (se 1 (by rfl) ⟨198454292, by rfl⟩ : syracuseStep 264605723 = 396908585) B396908585
theorem B176403815 : Blo 2263435 176403815 := bstep (se 1 (by rfl) ⟨132302861, by rfl⟩ : syracuseStep 176403815 = 264605723) B264605723
theorem B117602543 : Blo 2263435 117602543 := bstep (se 1 (by rfl) ⟨88201907, by rfl⟩ : syracuseStep 117602543 = 176403815) B176403815
theorem B78401695 : Blo 2263435 78401695 := bstep (se 1 (by rfl) ⟨58801271, by rfl⟩ : syracuseStep 78401695 = 117602543) B117602543
theorem B104535593 : Blo 2263435 104535593 := bstep (se 2 (by rfl) ⟨39200847, by rfl⟩ : syracuseStep 104535593 = 78401695) B78401695
theorem B69690395 : Blo 2263435 69690395 := bstep (se 1 (by rfl) ⟨52267796, by rfl⟩ : syracuseStep 69690395 = 104535593) B104535593
theorem B46460263 : Blo 2263435 46460263 := bstep (se 1 (by rfl) ⟨34845197, by rfl⟩ : syracuseStep 46460263 = 69690395) B69690395
theorem B61947017 : Blo 2263435 61947017 := bstep (se 2 (by rfl) ⟨23230131, by rfl⟩ : syracuseStep 61947017 = 46460263) B46460263
theorem B41298011 : Blo 2263435 41298011 := bstep (se 1 (by rfl) ⟨30973508, by rfl⟩ : syracuseStep 41298011 = 61947017) B61947017
theorem B27532007 : Blo 2263435 27532007 := bstep (se 1 (by rfl) ⟨20649005, by rfl⟩ : syracuseStep 27532007 = 41298011) B41298011
theorem B18354671 : Blo 2263435 18354671 := bstep (se 1 (by rfl) ⟨13766003, by rfl⟩ : syracuseStep 18354671 = 27532007) B27532007
theorem B12236447 : Blo 2263435 12236447 := bstep (se 1 (by rfl) ⟨9177335, by rfl⟩ : syracuseStep 12236447 = 18354671) B18354671
theorem B8157631 : Blo 2263435 8157631 := bstep (se 1 (by rfl) ⟨6118223, by rfl⟩ : syracuseStep 8157631 = 12236447) B12236447
theorem B10876841 : Blo 2263435 10876841 := bstep (se 2 (by rfl) ⟨4078815, by rfl⟩ : syracuseStep 10876841 = 8157631) B8157631
theorem B7251227 : Blo 2263435 7251227 := bstep (se 1 (by rfl) ⟨5438420, by rfl⟩ : syracuseStep 7251227 = 10876841) B10876841
theorem B4834151 : Blo 2263435 4834151 := bstep (se 1 (by rfl) ⟨3625613, by rfl⟩ : syracuseStep 4834151 = 7251227) B7251227
theorem B3222767 : Blo 2263435 3222767 := bstep (se 1 (by rfl) ⟨2417075, by rfl⟩ : syracuseStep 3222767 = 4834151) B4834151
theorem B8594045 : Blo 2263435 8594045 := bstep (se 3 (by rfl) ⟨1611383, by rfl⟩ : syracuseStep 8594045 = 3222767) B3222767
theorem B5729363 : Blo 2263435 5729363 := bstep (se 1 (by rfl) ⟨4297022, by rfl⟩ : syracuseStep 5729363 = 8594045) B8594045
theorem B3819575 : Blo 2263435 3819575 := bstep (se 1 (by rfl) ⟨2864681, by rfl⟩ : syracuseStep 3819575 = 5729363) B5729363
theorem B2546383 : Blo 2263435 2546383 := bstep (se 1 (by rfl) ⟨1909787, by rfl⟩ : syracuseStep 2546383 = 3819575) B3819575
theorem B3395177 : Blo 2263435 3395177 := bstep (se 2 (by rfl) ⟨1273191, by rfl⟩ : syracuseStep 3395177 = 2546383) B2546383
theorem B2263451 : Blo 2263435 2263451 := bstep (se 1 (by rfl) ⟨1697588, by rfl⟩ : syracuseStep 2263451 = 3395177) B3395177
theorem B5438429 : Blo 2263435 5438429 := bbase (se 3 (by rfl) ⟨1019705, by rfl⟩ : syracuseStep 5438429 = 2039411) (by norm_num)
theorem B3625619 : Blo 2263435 3625619 := bstep (se 1 (by rfl) ⟨2719214, by rfl⟩ : syracuseStep 3625619 = 5438429) B5438429
theorem B9668317 : Blo 2263435 9668317 := bstep (se 3 (by rfl) ⟨1812809, by rfl⟩ : syracuseStep 9668317 = 3625619) B3625619
theorem B12891089 : Blo 2263435 12891089 := bstep (se 2 (by rfl) ⟨4834158, by rfl⟩ : syracuseStep 12891089 = 9668317) B9668317
theorem B8594059 : Blo 2263435 8594059 := bstep (se 1 (by rfl) ⟨6445544, by rfl⟩ : syracuseStep 8594059 = 12891089) B12891089
theorem B11458745 : Blo 2263435 11458745 := bstep (se 2 (by rfl) ⟨4297029, by rfl⟩ : syracuseStep 11458745 = 8594059) B8594059
theorem B7639163 : Blo 2263435 7639163 := bstep (se 1 (by rfl) ⟨5729372, by rfl⟩ : syracuseStep 7639163 = 11458745) B11458745
theorem B5092775 : Blo 2263435 5092775 := bstep (se 1 (by rfl) ⟨3819581, by rfl⟩ : syracuseStep 5092775 = 7639163) B7639163
theorem B3395183 : Blo 2263435 3395183 := bstep (se 1 (by rfl) ⟨2546387, by rfl⟩ : syracuseStep 3395183 = 5092775) B5092775
theorem B2263455 : Blo 2263435 2263455 := bstep (se 1 (by rfl) ⟨1697591, by rfl⟩ : syracuseStep 2263455 = 3395183) B3395183
theorem B3395189 : Blo 2263435 3395189 := bbase (se 5 (by rfl) ⟨159149, by rfl⟩ : syracuseStep 3395189 = 318299) (by norm_num)
theorem B2263459 : Blo 2263435 2263459 := bstep (se 1 (by rfl) ⟨1697594, by rfl⟩ : syracuseStep 2263459 = 3395189) B3395189
theorem B4297045 : Blo 2263435 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B5729393 : Blo 2263435 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B3819595 : Blo 2263435 3819595 := bstep (se 1 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 3819595 = 5729393) B5729393
theorem B5092793 : Blo 2263435 5092793 := bstep (se 2 (by rfl) ⟨1909797, by rfl⟩ : syracuseStep 5092793 = 3819595) B3819595
theorem B3395195 : Blo 2263435 3395195 := bstep (se 1 (by rfl) ⟨2546396, by rfl⟩ : syracuseStep 3395195 = 5092793) B5092793
theorem B2263463 : Blo 2263435 2263463 := bstep (se 1 (by rfl) ⟨1697597, by rfl⟩ : syracuseStep 2263463 = 3395195) B3395195
theorem B2546401 : Blo 2263435 2546401 := bbase (se 2 (by rfl) ⟨954900, by rfl⟩ : syracuseStep 2546401 = 1909801) (by norm_num)
theorem B3395201 : Blo 2263435 3395201 := bstep (se 2 (by rfl) ⟨1273200, by rfl⟩ : syracuseStep 3395201 = 2546401) B2546401
theorem B2263467 : Blo 2263435 2263467 := bstep (se 1 (by rfl) ⟨1697600, by rfl⟩ : syracuseStep 2263467 = 3395201) B3395201
theorem B5729413 : Blo 2263435 5729413 := bbase (se 4 (by rfl) ⟨537132, by rfl⟩ : syracuseStep 5729413 = 1074265) (by norm_num)
theorem B7639217 : Blo 2263435 7639217 := bstep (se 2 (by rfl) ⟨2864706, by rfl⟩ : syracuseStep 7639217 = 5729413) B5729413
theorem B5092811 : Blo 2263435 5092811 := bstep (se 1 (by rfl) ⟨3819608, by rfl⟩ : syracuseStep 5092811 = 7639217) B7639217
theorem B3395207 : Blo 2263435 3395207 := bstep (se 1 (by rfl) ⟨2546405, by rfl⟩ : syracuseStep 3395207 = 5092811) B5092811
theorem B2263471 : Blo 2263435 2263471 := bstep (se 1 (by rfl) ⟨1697603, by rfl⟩ : syracuseStep 2263471 = 3395207) B3395207
theorem B3395213 : Blo 2263435 3395213 := bbase (se 3 (by rfl) ⟨636602, by rfl⟩ : syracuseStep 3395213 = 1273205) (by norm_num)
theorem B2263475 : Blo 2263435 2263475 := bstep (se 1 (by rfl) ⟨1697606, by rfl⟩ : syracuseStep 2263475 = 3395213) B3395213
theorem B5092829 : Blo 2263435 5092829 := bbase (se 3 (by rfl) ⟨954905, by rfl⟩ : syracuseStep 5092829 = 1909811) (by norm_num)
theorem B3395219 : Blo 2263435 3395219 := bstep (se 1 (by rfl) ⟨2546414, by rfl⟩ : syracuseStep 3395219 = 5092829) B5092829
theorem B2263479 : Blo 2263435 2263479 := bstep (se 1 (by rfl) ⟨1697609, by rfl⟩ : syracuseStep 2263479 = 3395219) B3395219
theorem B3819629 : Blo 2263435 3819629 := bbase (se 3 (by rfl) ⟨716180, by rfl⟩ : syracuseStep 3819629 = 1432361) (by norm_num)
theorem B2546419 : Blo 2263435 2546419 := bstep (se 1 (by rfl) ⟨1909814, by rfl⟩ : syracuseStep 2546419 = 3819629) B3819629
theorem B3395225 : Blo 2263435 3395225 := bstep (se 2 (by rfl) ⟨1273209, by rfl⟩ : syracuseStep 3395225 = 2546419) B2546419
theorem B2263483 : Blo 2263435 2263483 := bstep (se 1 (by rfl) ⟨1697612, by rfl⟩ : syracuseStep 2263483 = 3395225) B3395225
theorem B15486997 : Blo 2263435 15486997 := bbase (se 6 (by rfl) ⟨362976, by rfl⟩ : syracuseStep 15486997 = 725953) (by norm_num)
theorem B20649329 : Blo 2263435 20649329 := bstep (se 2 (by rfl) ⟨7743498, by rfl⟩ : syracuseStep 20649329 = 15486997) B15486997
theorem B13766219 : Blo 2263435 13766219 := bstep (se 1 (by rfl) ⟨10324664, by rfl⟩ : syracuseStep 13766219 = 20649329) B20649329
theorem B9177479 : Blo 2263435 9177479 := bstep (se 1 (by rfl) ⟨6883109, by rfl⟩ : syracuseStep 9177479 = 13766219) B13766219
theorem B6118319 : Blo 2263435 6118319 := bstep (se 1 (by rfl) ⟨4588739, by rfl⟩ : syracuseStep 6118319 = 9177479) B9177479
theorem B4078879 : Blo 2263435 4078879 := bstep (se 1 (by rfl) ⟨3059159, by rfl⟩ : syracuseStep 4078879 = 6118319) B6118319
theorem B21754021 : Blo 2263435 21754021 := bstep (se 4 (by rfl) ⟨2039439, by rfl⟩ : syracuseStep 21754021 = 4078879) B4078879
theorem B29005361 : Blo 2263435 29005361 := bstep (se 2 (by rfl) ⟨10877010, by rfl⟩ : syracuseStep 29005361 = 21754021) B21754021
theorem B19336907 : Blo 2263435 19336907 := bstep (se 1 (by rfl) ⟨14502680, by rfl⟩ : syracuseStep 19336907 = 29005361) B29005361
theorem B12891271 : Blo 2263435 12891271 := bstep (se 1 (by rfl) ⟨9668453, by rfl⟩ : syracuseStep 12891271 = 19336907) B19336907
theorem B17188361 : Blo 2263435 17188361 := bstep (se 2 (by rfl) ⟨6445635, by rfl⟩ : syracuseStep 17188361 = 12891271) B12891271
theorem B11458907 : Blo 2263435 11458907 := bstep (se 1 (by rfl) ⟨8594180, by rfl⟩ : syracuseStep 11458907 = 17188361) B17188361
theorem B7639271 : Blo 2263435 7639271 := bstep (se 1 (by rfl) ⟨5729453, by rfl⟩ : syracuseStep 7639271 = 11458907) B11458907
theorem B5092847 : Blo 2263435 5092847 := bstep (se 1 (by rfl) ⟨3819635, by rfl⟩ : syracuseStep 5092847 = 7639271) B7639271
theorem B3395231 : Blo 2263435 3395231 := bstep (se 1 (by rfl) ⟨2546423, by rfl⟩ : syracuseStep 3395231 = 5092847) B5092847
theorem B2263487 : Blo 2263435 2263487 := bstep (se 1 (by rfl) ⟨1697615, by rfl⟩ : syracuseStep 2263487 = 3395231) B3395231
theorem B3395237 : Blo 2263435 3395237 := bbase (se 4 (by rfl) ⟨318303, by rfl⟩ : syracuseStep 3395237 = 636607) (by norm_num)
theorem B2263491 : Blo 2263435 2263491 := bstep (se 1 (by rfl) ⟨1697618, by rfl⟩ : syracuseStep 2263491 = 3395237) B3395237
theorem B2864737 : Blo 2263435 2864737 := bbase (se 2 (by rfl) ⟨1074276, by rfl⟩ : syracuseStep 2864737 = 2148553) (by norm_num)
theorem B3819649 : Blo 2263435 3819649 := bstep (se 2 (by rfl) ⟨1432368, by rfl⟩ : syracuseStep 3819649 = 2864737) B2864737
theorem B5092865 : Blo 2263435 5092865 := bstep (se 2 (by rfl) ⟨1909824, by rfl⟩ : syracuseStep 5092865 = 3819649) B3819649
theorem B3395243 : Blo 2263435 3395243 := bstep (se 1 (by rfl) ⟨2546432, by rfl⟩ : syracuseStep 3395243 = 5092865) B5092865
theorem B2263495 : Blo 2263435 2263495 := bstep (se 1 (by rfl) ⟨1697621, by rfl⟩ : syracuseStep 2263495 = 3395243) B3395243
theorem B2546437 : Blo 2263435 2546437 := bbase (se 4 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 2546437 = 477457) (by norm_num)
theorem B3395249 : Blo 2263435 3395249 := bstep (se 2 (by rfl) ⟨1273218, by rfl⟩ : syracuseStep 3395249 = 2546437) B2546437
theorem B2263499 : Blo 2263435 2263499 := bstep (se 1 (by rfl) ⟨1697624, by rfl⟩ : syracuseStep 2263499 = 3395249) B3395249
theorem B2719273 : Blo 2263435 2719273 := bbase (se 2 (by rfl) ⟨1019727, by rfl⟩ : syracuseStep 2719273 = 2039455) (by norm_num)
theorem B3625697 : Blo 2263435 3625697 := bstep (se 2 (by rfl) ⟨1359636, by rfl⟩ : syracuseStep 3625697 = 2719273) B2719273
theorem B2417131 : Blo 2263435 2417131 := bstep (se 1 (by rfl) ⟨1812848, by rfl⟩ : syracuseStep 2417131 = 3625697) B3625697
theorem B3222841 : Blo 2263435 3222841 := bstep (se 2 (by rfl) ⟨1208565, by rfl⟩ : syracuseStep 3222841 = 2417131) B2417131
theorem B4297121 : Blo 2263435 4297121 := bstep (se 2 (by rfl) ⟨1611420, by rfl⟩ : syracuseStep 4297121 = 3222841) B3222841
theorem B2864747 : Blo 2263435 2864747 := bstep (se 1 (by rfl) ⟨2148560, by rfl⟩ : syracuseStep 2864747 = 4297121) B4297121
theorem B7639325 : Blo 2263435 7639325 := bstep (se 3 (by rfl) ⟨1432373, by rfl⟩ : syracuseStep 7639325 = 2864747) B2864747
theorem B5092883 : Blo 2263435 5092883 := bstep (se 1 (by rfl) ⟨3819662, by rfl⟩ : syracuseStep 5092883 = 7639325) B7639325
theorem B3395255 : Blo 2263435 3395255 := bstep (se 1 (by rfl) ⟨2546441, by rfl⟩ : syracuseStep 3395255 = 5092883) B5092883
theorem B2263503 : Blo 2263435 2263503 := bstep (se 1 (by rfl) ⟨1697627, by rfl⟩ : syracuseStep 2263503 = 3395255) B3395255
theorem B3395261 : Blo 2263435 3395261 := bbase (se 3 (by rfl) ⟨636611, by rfl⟩ : syracuseStep 3395261 = 1273223) (by norm_num)
theorem B2263507 : Blo 2263435 2263507 := bstep (se 1 (by rfl) ⟨1697630, by rfl⟩ : syracuseStep 2263507 = 3395261) B3395261
theorem B5092901 : Blo 2263435 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B3395267 : Blo 2263435 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B2263511 : Blo 2263435 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B5729525 : Blo 2263435 5729525 := bbase (se 5 (by rfl) ⟨268571, by rfl⟩ : syracuseStep 5729525 = 537143) (by norm_num)
theorem B3819683 : Blo 2263435 3819683 := bstep (se 1 (by rfl) ⟨2864762, by rfl⟩ : syracuseStep 3819683 = 5729525) B5729525
theorem B2546455 : Blo 2263435 2546455 := bstep (se 1 (by rfl) ⟨1909841, by rfl⟩ : syracuseStep 2546455 = 3819683) B3819683
theorem B3395273 : Blo 2263435 3395273 := bstep (se 2 (by rfl) ⟨1273227, by rfl⟩ : syracuseStep 3395273 = 2546455) B2546455
theorem B2263515 : Blo 2263435 2263515 := bstep (se 1 (by rfl) ⟨1697636, by rfl⟩ : syracuseStep 2263515 = 3395273) B3395273
theorem B5162405 : Blo 2263435 5162405 := bbase (se 4 (by rfl) ⟨483975, by rfl⟩ : syracuseStep 5162405 = 967951) (by norm_num)
theorem B55065653 : Blo 2263435 55065653 := bstep (se 5 (by rfl) ⟨2581202, by rfl⟩ : syracuseStep 55065653 = 5162405) B5162405
theorem B36710435 : Blo 2263435 36710435 := bstep (se 1 (by rfl) ⟨27532826, by rfl⟩ : syracuseStep 36710435 = 55065653) B55065653
theorem B24473623 : Blo 2263435 24473623 := bstep (se 1 (by rfl) ⟨18355217, by rfl⟩ : syracuseStep 24473623 = 36710435) B36710435
theorem B32631497 : Blo 2263435 32631497 := bstep (se 2 (by rfl) ⟨12236811, by rfl⟩ : syracuseStep 32631497 = 24473623) B24473623
theorem B21754331 : Blo 2263435 21754331 := bstep (se 1 (by rfl) ⟨16315748, by rfl⟩ : syracuseStep 21754331 = 32631497) B32631497
theorem B14502887 : Blo 2263435 14502887 := bstep (se 1 (by rfl) ⟨10877165, by rfl⟩ : syracuseStep 14502887 = 21754331) B21754331
theorem B9668591 : Blo 2263435 9668591 := bstep (se 1 (by rfl) ⟨7251443, by rfl⟩ : syracuseStep 9668591 = 14502887) B14502887
theorem B6445727 : Blo 2263435 6445727 := bstep (se 1 (by rfl) ⟨4834295, by rfl⟩ : syracuseStep 6445727 = 9668591) B9668591
theorem B4297151 : Blo 2263435 4297151 := bstep (se 1 (by rfl) ⟨3222863, by rfl⟩ : syracuseStep 4297151 = 6445727) B6445727
theorem B11459069 : Blo 2263435 11459069 := bstep (se 3 (by rfl) ⟨2148575, by rfl⟩ : syracuseStep 11459069 = 4297151) B4297151
theorem B7639379 : Blo 2263435 7639379 := bstep (se 1 (by rfl) ⟨5729534, by rfl⟩ : syracuseStep 7639379 = 11459069) B11459069
theorem B5092919 : Blo 2263435 5092919 := bstep (se 1 (by rfl) ⟨3819689, by rfl⟩ : syracuseStep 5092919 = 7639379) B7639379
theorem B3395279 : Blo 2263435 3395279 := bstep (se 1 (by rfl) ⟨2546459, by rfl⟩ : syracuseStep 3395279 = 5092919) B5092919
theorem B2263519 : Blo 2263435 2263519 := bstep (se 1 (by rfl) ⟨1697639, by rfl⟩ : syracuseStep 2263519 = 3395279) B3395279
theorem B3395285 : Blo 2263435 3395285 := bbase (se 7 (by rfl) ⟨39788, by rfl⟩ : syracuseStep 3395285 = 79577) (by norm_num)
theorem B2263523 : Blo 2263435 2263523 := bstep (se 1 (by rfl) ⟨1697642, by rfl⟩ : syracuseStep 2263523 = 3395285) B3395285
theorem B2581213 : Blo 2263435 2581213 := bbase (se 3 (by rfl) ⟨483977, by rfl⟩ : syracuseStep 2581213 = 967955) (by norm_num)
theorem B3441617 : Blo 2263435 3441617 := bstep (se 2 (by rfl) ⟨1290606, by rfl⟩ : syracuseStep 3441617 = 2581213) B2581213
theorem B2294411 : Blo 2263435 2294411 := bstep (se 1 (by rfl) ⟨1720808, by rfl⟩ : syracuseStep 2294411 = 3441617) B3441617
theorem B6118429 : Blo 2263435 6118429 := bstep (se 3 (by rfl) ⟨1147205, by rfl⟩ : syracuseStep 6118429 = 2294411) B2294411
theorem B8157905 : Blo 2263435 8157905 := bstep (se 2 (by rfl) ⟨3059214, by rfl⟩ : syracuseStep 8157905 = 6118429) B6118429
theorem B5438603 : Blo 2263435 5438603 := bstep (se 1 (by rfl) ⟨4078952, by rfl⟩ : syracuseStep 5438603 = 8157905) B8157905
theorem B3625735 : Blo 2263435 3625735 := bstep (se 1 (by rfl) ⟨2719301, by rfl⟩ : syracuseStep 3625735 = 5438603) B5438603
theorem B4834313 : Blo 2263435 4834313 := bstep (se 2 (by rfl) ⟨1812867, by rfl⟩ : syracuseStep 4834313 = 3625735) B3625735
theorem B3222875 : Blo 2263435 3222875 := bstep (se 1 (by rfl) ⟨2417156, by rfl⟩ : syracuseStep 3222875 = 4834313) B4834313
theorem B8594333 : Blo 2263435 8594333 := bstep (se 3 (by rfl) ⟨1611437, by rfl⟩ : syracuseStep 8594333 = 3222875) B3222875
theorem B5729555 : Blo 2263435 5729555 := bstep (se 1 (by rfl) ⟨4297166, by rfl⟩ : syracuseStep 5729555 = 8594333) B8594333
theorem B3819703 : Blo 2263435 3819703 := bstep (se 1 (by rfl) ⟨2864777, by rfl⟩ : syracuseStep 3819703 = 5729555) B5729555
theorem B5092937 : Blo 2263435 5092937 := bstep (se 2 (by rfl) ⟨1909851, by rfl⟩ : syracuseStep 5092937 = 3819703) B3819703
theorem B3395291 : Blo 2263435 3395291 := bstep (se 1 (by rfl) ⟨2546468, by rfl⟩ : syracuseStep 3395291 = 5092937) B5092937
theorem B2263527 : Blo 2263435 2263527 := bstep (se 1 (by rfl) ⟨1697645, by rfl⟩ : syracuseStep 2263527 = 3395291) B3395291
theorem B2546473 : Blo 2263435 2546473 := bbase (se 2 (by rfl) ⟨954927, by rfl⟩ : syracuseStep 2546473 = 1909855) (by norm_num)
theorem B3395297 : Blo 2263435 3395297 := bstep (se 2 (by rfl) ⟨1273236, by rfl⟩ : syracuseStep 3395297 = 2546473) B2546473
theorem B2263531 : Blo 2263435 2263531 := bstep (se 1 (by rfl) ⟨1697648, by rfl⟩ : syracuseStep 2263531 = 3395297) B3395297
theorem B5438621 : Blo 2263435 5438621 := bbase (se 3 (by rfl) ⟨1019741, by rfl⟩ : syracuseStep 5438621 = 2039483) (by norm_num)
theorem B14502989 : Blo 2263435 14502989 := bstep (se 3 (by rfl) ⟨2719310, by rfl⟩ : syracuseStep 14502989 = 5438621) B5438621
theorem B9668659 : Blo 2263435 9668659 := bstep (se 1 (by rfl) ⟨7251494, by rfl⟩ : syracuseStep 9668659 = 14502989) B14502989
theorem B12891545 : Blo 2263435 12891545 := bstep (se 2 (by rfl) ⟨4834329, by rfl⟩ : syracuseStep 12891545 = 9668659) B9668659
theorem B8594363 : Blo 2263435 8594363 := bstep (se 1 (by rfl) ⟨6445772, by rfl⟩ : syracuseStep 8594363 = 12891545) B12891545
theorem B5729575 : Blo 2263435 5729575 := bstep (se 1 (by rfl) ⟨4297181, by rfl⟩ : syracuseStep 5729575 = 8594363) B8594363
theorem B7639433 : Blo 2263435 7639433 := bstep (se 2 (by rfl) ⟨2864787, by rfl⟩ : syracuseStep 7639433 = 5729575) B5729575
theorem B5092955 : Blo 2263435 5092955 := bstep (se 1 (by rfl) ⟨3819716, by rfl⟩ : syracuseStep 5092955 = 7639433) B7639433
theorem B3395303 : Blo 2263435 3395303 := bstep (se 1 (by rfl) ⟨2546477, by rfl⟩ : syracuseStep 3395303 = 5092955) B5092955
theorem B2263535 : Blo 2263435 2263535 := bstep (se 1 (by rfl) ⟨1697651, by rfl⟩ : syracuseStep 2263535 = 3395303) B3395303
theorem B3395309 : Blo 2263435 3395309 := bbase (se 3 (by rfl) ⟨636620, by rfl⟩ : syracuseStep 3395309 = 1273241) (by norm_num)
theorem B2263539 : Blo 2263435 2263539 := bstep (se 1 (by rfl) ⟨1697654, by rfl⟩ : syracuseStep 2263539 = 3395309) B3395309
theorem B5092973 : Blo 2263435 5092973 := bbase (se 3 (by rfl) ⟨954932, by rfl⟩ : syracuseStep 5092973 = 1909865) (by norm_num)
theorem B3395315 : Blo 2263435 3395315 := bstep (se 1 (by rfl) ⟨2546486, by rfl⟩ : syracuseStep 3395315 = 5092973) B5092973
theorem B2263543 : Blo 2263435 2263543 := bstep (se 1 (by rfl) ⟨1697657, by rfl⟩ : syracuseStep 2263543 = 3395315) B3395315
theorem B4297205 : Blo 2263435 4297205 := bbase (se 5 (by rfl) ⟨201431, by rfl⟩ : syracuseStep 4297205 = 402863) (by norm_num)
theorem B2864803 : Blo 2263435 2864803 := bstep (se 1 (by rfl) ⟨2148602, by rfl⟩ : syracuseStep 2864803 = 4297205) B4297205
theorem B3819737 : Blo 2263435 3819737 := bstep (se 2 (by rfl) ⟨1432401, by rfl⟩ : syracuseStep 3819737 = 2864803) B2864803
theorem B2546491 : Blo 2263435 2546491 := bstep (se 1 (by rfl) ⟨1909868, by rfl⟩ : syracuseStep 2546491 = 3819737) B3819737
theorem B3395321 : Blo 2263435 3395321 := bstep (se 2 (by rfl) ⟨1273245, by rfl⟩ : syracuseStep 3395321 = 2546491) B2546491
theorem B2263547 : Blo 2263435 2263547 := bstep (se 1 (by rfl) ⟨1697660, by rfl⟩ : syracuseStep 2263547 = 3395321) B3395321
theorem B2616457 : Blo 2263435 2616457 := bbase (se 2 (by rfl) ⟨981171, by rfl⟩ : syracuseStep 2616457 = 1962343) (by norm_num)
theorem B3488609 : Blo 2263435 3488609 := bstep (se 2 (by rfl) ⟨1308228, by rfl⟩ : syracuseStep 3488609 = 2616457) B2616457
theorem B9302957 : Blo 2263435 9302957 := bstep (se 3 (by rfl) ⟨1744304, by rfl⟩ : syracuseStep 9302957 = 3488609) B3488609
theorem B6201971 : Blo 2263435 6201971 := bstep (se 1 (by rfl) ⟨4651478, by rfl⟩ : syracuseStep 6201971 = 9302957) B9302957
theorem B4134647 : Blo 2263435 4134647 := bstep (se 1 (by rfl) ⟨3100985, by rfl⟩ : syracuseStep 4134647 = 6201971) B6201971
theorem B2756431 : Blo 2263435 2756431 := bstep (se 1 (by rfl) ⟨2067323, by rfl⟩ : syracuseStep 2756431 = 4134647) B4134647
theorem B3675241 : Blo 2263435 3675241 := bstep (se 2 (by rfl) ⟨1378215, by rfl⟩ : syracuseStep 3675241 = 2756431) B2756431
theorem B4900321 : Blo 2263435 4900321 := bstep (se 2 (by rfl) ⟨1837620, by rfl⟩ : syracuseStep 4900321 = 3675241) B3675241
theorem B26135045 : Blo 2263435 26135045 := bstep (se 4 (by rfl) ⟨2450160, by rfl⟩ : syracuseStep 26135045 = 4900321) B4900321
theorem B17423363 : Blo 2263435 17423363 := bstep (se 1 (by rfl) ⟨13067522, by rfl⟩ : syracuseStep 17423363 = 26135045) B26135045
theorem B11615575 : Blo 2263435 11615575 := bstep (se 1 (by rfl) ⟨8711681, by rfl⟩ : syracuseStep 11615575 = 17423363) B17423363
theorem B15487433 : Blo 2263435 15487433 := bstep (se 2 (by rfl) ⟨5807787, by rfl⟩ : syracuseStep 15487433 = 11615575) B11615575
theorem B10324955 : Blo 2263435 10324955 := bstep (se 1 (by rfl) ⟨7743716, by rfl⟩ : syracuseStep 10324955 = 15487433) B15487433
theorem B6883303 : Blo 2263435 6883303 := bstep (se 1 (by rfl) ⟨5162477, by rfl⟩ : syracuseStep 6883303 = 10324955) B10324955
theorem B9177737 : Blo 2263435 9177737 := bstep (se 2 (by rfl) ⟨3441651, by rfl⟩ : syracuseStep 9177737 = 6883303) B6883303
theorem B97895861 : Blo 2263435 97895861 := bstep (se 5 (by rfl) ⟨4588868, by rfl⟩ : syracuseStep 97895861 = 9177737) B9177737
theorem B65263907 : Blo 2263435 65263907 := bstep (se 1 (by rfl) ⟨48947930, by rfl⟩ : syracuseStep 65263907 = 97895861) B97895861
theorem B43509271 : Blo 2263435 43509271 := bstep (se 1 (by rfl) ⟨32631953, by rfl⟩ : syracuseStep 43509271 = 65263907) B65263907
theorem B58012361 : Blo 2263435 58012361 := bstep (se 2 (by rfl) ⟨21754635, by rfl⟩ : syracuseStep 58012361 = 43509271) B43509271
theorem B38674907 : Blo 2263435 38674907 := bstep (se 1 (by rfl) ⟨29006180, by rfl⟩ : syracuseStep 38674907 = 58012361) B58012361
theorem B25783271 : Blo 2263435 25783271 := bstep (se 1 (by rfl) ⟨19337453, by rfl⟩ : syracuseStep 25783271 = 38674907) B38674907
theorem B17188847 : Blo 2263435 17188847 := bstep (se 1 (by rfl) ⟨12891635, by rfl⟩ : syracuseStep 17188847 = 25783271) B25783271
theorem B11459231 : Blo 2263435 11459231 := bstep (se 1 (by rfl) ⟨8594423, by rfl⟩ : syracuseStep 11459231 = 17188847) B17188847
theorem B7639487 : Blo 2263435 7639487 := bstep (se 1 (by rfl) ⟨5729615, by rfl⟩ : syracuseStep 7639487 = 11459231) B11459231
theorem B5092991 : Blo 2263435 5092991 := bstep (se 1 (by rfl) ⟨3819743, by rfl⟩ : syracuseStep 5092991 = 7639487) B7639487
theorem B3395327 : Blo 2263435 3395327 := bstep (se 1 (by rfl) ⟨2546495, by rfl⟩ : syracuseStep 3395327 = 5092991) B5092991
theorem B2263551 : Blo 2263435 2263551 := bstep (se 1 (by rfl) ⟨1697663, by rfl⟩ : syracuseStep 2263551 = 3395327) B3395327
theorem B3395333 : Blo 2263435 3395333 := bbase (se 4 (by rfl) ⟨318312, by rfl⟩ : syracuseStep 3395333 = 636625) (by norm_num)
theorem B2263555 : Blo 2263435 2263555 := bstep (se 1 (by rfl) ⟨1697666, by rfl⟩ : syracuseStep 2263555 = 3395333) B3395333
theorem B3819757 : Blo 2263435 3819757 := bbase (se 3 (by rfl) ⟨716204, by rfl⟩ : syracuseStep 3819757 = 1432409) (by norm_num)
theorem B5093009 : Blo 2263435 5093009 := bstep (se 2 (by rfl) ⟨1909878, by rfl⟩ : syracuseStep 5093009 = 3819757) B3819757
theorem B3395339 : Blo 2263435 3395339 := bstep (se 1 (by rfl) ⟨2546504, by rfl⟩ : syracuseStep 3395339 = 5093009) B5093009
theorem B2263559 : Blo 2263435 2263559 := bstep (se 1 (by rfl) ⟨1697669, by rfl⟩ : syracuseStep 2263559 = 3395339) B3395339
theorem B2546509 : Blo 2263435 2546509 := bbase (se 3 (by rfl) ⟨477470, by rfl⟩ : syracuseStep 2546509 = 954941) (by norm_num)
theorem B3395345 : Blo 2263435 3395345 := bstep (se 2 (by rfl) ⟨1273254, by rfl⟩ : syracuseStep 3395345 = 2546509) B2546509
theorem B2263563 : Blo 2263435 2263563 := bstep (se 1 (by rfl) ⟨1697672, by rfl⟩ : syracuseStep 2263563 = 3395345) B3395345
theorem B7639541 : Blo 2263435 7639541 := bbase (se 5 (by rfl) ⟨358103, by rfl⟩ : syracuseStep 7639541 = 716207) (by norm_num)
theorem B5093027 : Blo 2263435 5093027 := bstep (se 1 (by rfl) ⟨3819770, by rfl⟩ : syracuseStep 5093027 = 7639541) B7639541
theorem B3395351 : Blo 2263435 3395351 := bstep (se 1 (by rfl) ⟨2546513, by rfl⟩ : syracuseStep 3395351 = 5093027) B5093027
theorem B2263567 : Blo 2263435 2263567 := bstep (se 1 (by rfl) ⟨1697675, by rfl⟩ : syracuseStep 2263567 = 3395351) B3395351
theorem B3395357 : Blo 2263435 3395357 := bbase (se 3 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 3395357 = 1273259) (by norm_num)
theorem B2263571 : Blo 2263435 2263571 := bstep (se 1 (by rfl) ⟨1697678, by rfl⟩ : syracuseStep 2263571 = 3395357) B3395357
theorem B5093045 : Blo 2263435 5093045 := bbase (se 5 (by rfl) ⟨238736, by rfl⟩ : syracuseStep 5093045 = 477473) (by norm_num)
theorem B3395363 : Blo 2263435 3395363 := bstep (se 1 (by rfl) ⟨2546522, by rfl⟩ : syracuseStep 3395363 = 5093045) B5093045
theorem B2263575 : Blo 2263435 2263575 := bstep (se 1 (by rfl) ⟨1697681, by rfl⟩ : syracuseStep 2263575 = 3395363) B3395363
theorem B12891797 : Blo 2263435 12891797 := bbase (se 6 (by rfl) ⟨302151, by rfl⟩ : syracuseStep 12891797 = 604303) (by norm_num)
theorem B8594531 : Blo 2263435 8594531 := bstep (se 1 (by rfl) ⟨6445898, by rfl⟩ : syracuseStep 8594531 = 12891797) B12891797
theorem B5729687 : Blo 2263435 5729687 := bstep (se 1 (by rfl) ⟨4297265, by rfl⟩ : syracuseStep 5729687 = 8594531) B8594531
theorem B3819791 : Blo 2263435 3819791 := bstep (se 1 (by rfl) ⟨2864843, by rfl⟩ : syracuseStep 3819791 = 5729687) B5729687
theorem B2546527 : Blo 2263435 2546527 := bstep (se 1 (by rfl) ⟨1909895, by rfl⟩ : syracuseStep 2546527 = 3819791) B3819791
theorem B3395369 : Blo 2263435 3395369 := bstep (se 2 (by rfl) ⟨1273263, by rfl⟩ : syracuseStep 3395369 = 2546527) B2546527
theorem B2263579 : Blo 2263435 2263579 := bstep (se 1 (by rfl) ⟨1697684, by rfl⟩ : syracuseStep 2263579 = 3395369) B3395369
theorem B6445909 : Blo 2263435 6445909 := bbase (se 9 (by rfl) ⟨18884, by rfl⟩ : syracuseStep 6445909 = 37769) (by norm_num)
theorem B8594545 : Blo 2263435 8594545 := bstep (se 2 (by rfl) ⟨3222954, by rfl⟩ : syracuseStep 8594545 = 6445909) B6445909
theorem B11459393 : Blo 2263435 11459393 := bstep (se 2 (by rfl) ⟨4297272, by rfl⟩ : syracuseStep 11459393 = 8594545) B8594545
theorem B7639595 : Blo 2263435 7639595 := bstep (se 1 (by rfl) ⟨5729696, by rfl⟩ : syracuseStep 7639595 = 11459393) B11459393
theorem B5093063 : Blo 2263435 5093063 := bstep (se 1 (by rfl) ⟨3819797, by rfl⟩ : syracuseStep 5093063 = 7639595) B7639595
theorem B3395375 : Blo 2263435 3395375 := bstep (se 1 (by rfl) ⟨2546531, by rfl⟩ : syracuseStep 3395375 = 5093063) B5093063
theorem B2263583 : Blo 2263435 2263583 := bstep (se 1 (by rfl) ⟨1697687, by rfl⟩ : syracuseStep 2263583 = 3395375) B3395375
theorem B3395381 : Blo 2263435 3395381 := bbase (se 5 (by rfl) ⟨159158, by rfl⟩ : syracuseStep 3395381 = 318317) (by norm_num)
theorem B2263587 : Blo 2263435 2263587 := bstep (se 1 (by rfl) ⟨1697690, by rfl⟩ : syracuseStep 2263587 = 3395381) B3395381
theorem B5729717 : Blo 2263435 5729717 := bbase (se 5 (by rfl) ⟨268580, by rfl⟩ : syracuseStep 5729717 = 537161) (by norm_num)
theorem B3819811 : Blo 2263435 3819811 := bstep (se 1 (by rfl) ⟨2864858, by rfl⟩ : syracuseStep 3819811 = 5729717) B5729717
theorem B5093081 : Blo 2263435 5093081 := bstep (se 2 (by rfl) ⟨1909905, by rfl⟩ : syracuseStep 5093081 = 3819811) B3819811
theorem B3395387 : Blo 2263435 3395387 := bstep (se 1 (by rfl) ⟨2546540, by rfl⟩ : syracuseStep 3395387 = 5093081) B5093081
theorem B2263591 : Blo 2263435 2263591 := bstep (se 1 (by rfl) ⟨1697693, by rfl⟩ : syracuseStep 2263591 = 3395387) B3395387
theorem B2546545 : Blo 2263435 2546545 := bbase (se 2 (by rfl) ⟨954954, by rfl⟩ : syracuseStep 2546545 = 1909909) (by norm_num)
theorem B3395393 : Blo 2263435 3395393 := bstep (se 2 (by rfl) ⟨1273272, by rfl⟩ : syracuseStep 3395393 = 2546545) B2546545
theorem B2263595 : Blo 2263435 2263595 := bstep (se 1 (by rfl) ⟨1697696, by rfl⟩ : syracuseStep 2263595 = 3395393) B3395393
theorem B9668933 : Blo 2263435 9668933 := bbase (se 4 (by rfl) ⟨906462, by rfl⟩ : syracuseStep 9668933 = 1812925) (by norm_num)
theorem B6445955 : Blo 2263435 6445955 := bstep (se 1 (by rfl) ⟨4834466, by rfl⟩ : syracuseStep 6445955 = 9668933) B9668933
theorem B4297303 : Blo 2263435 4297303 := bstep (se 1 (by rfl) ⟨3222977, by rfl⟩ : syracuseStep 4297303 = 6445955) B6445955
theorem B5729737 : Blo 2263435 5729737 := bstep (se 2 (by rfl) ⟨2148651, by rfl⟩ : syracuseStep 5729737 = 4297303) B4297303
theorem B7639649 : Blo 2263435 7639649 := bstep (se 2 (by rfl) ⟨2864868, by rfl⟩ : syracuseStep 7639649 = 5729737) B5729737
theorem B5093099 : Blo 2263435 5093099 := bstep (se 1 (by rfl) ⟨3819824, by rfl⟩ : syracuseStep 5093099 = 7639649) B7639649
theorem B3395399 : Blo 2263435 3395399 := bstep (se 1 (by rfl) ⟨2546549, by rfl⟩ : syracuseStep 3395399 = 5093099) B5093099
theorem B2263599 : Blo 2263435 2263599 := bstep (se 1 (by rfl) ⟨1697699, by rfl⟩ : syracuseStep 2263599 = 3395399) B3395399
theorem B3395405 : Blo 2263435 3395405 := bbase (se 3 (by rfl) ⟨636638, by rfl⟩ : syracuseStep 3395405 = 1273277) (by norm_num)
theorem B2263603 : Blo 2263435 2263603 := bstep (se 1 (by rfl) ⟨1697702, by rfl⟩ : syracuseStep 2263603 = 3395405) B3395405
theorem B5093117 : Blo 2263435 5093117 := bbase (se 3 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 5093117 = 1909919) (by norm_num)
theorem B3395411 : Blo 2263435 3395411 := bstep (se 1 (by rfl) ⟨2546558, by rfl⟩ : syracuseStep 3395411 = 5093117) B5093117
theorem B2263607 : Blo 2263435 2263607 := bstep (se 1 (by rfl) ⟨1697705, by rfl⟩ : syracuseStep 2263607 = 3395411) B3395411
theorem B3819845 : Blo 2263435 3819845 := bbase (se 4 (by rfl) ⟨358110, by rfl⟩ : syracuseStep 3819845 = 716221) (by norm_num)
theorem B2546563 : Blo 2263435 2546563 := bstep (se 1 (by rfl) ⟨1909922, by rfl⟩ : syracuseStep 2546563 = 3819845) B3819845
theorem B3395417 : Blo 2263435 3395417 := bstep (se 2 (by rfl) ⟨1273281, by rfl⟩ : syracuseStep 3395417 = 2546563) B2546563
theorem B2263611 : Blo 2263435 2263611 := bstep (se 1 (by rfl) ⟨1697708, by rfl⟩ : syracuseStep 2263611 = 3395417) B3395417
theorem B17189333 : Blo 2263435 17189333 := bbase (se 7 (by rfl) ⟨201437, by rfl⟩ : syracuseStep 17189333 = 402875) (by norm_num)
theorem B11459555 : Blo 2263435 11459555 := bstep (se 1 (by rfl) ⟨8594666, by rfl⟩ : syracuseStep 11459555 = 17189333) B17189333
theorem B7639703 : Blo 2263435 7639703 := bstep (se 1 (by rfl) ⟨5729777, by rfl⟩ : syracuseStep 7639703 = 11459555) B11459555
theorem B5093135 : Blo 2263435 5093135 := bstep (se 1 (by rfl) ⟨3819851, by rfl⟩ : syracuseStep 5093135 = 7639703) B7639703
theorem B3395423 : Blo 2263435 3395423 := bstep (se 1 (by rfl) ⟨2546567, by rfl⟩ : syracuseStep 3395423 = 5093135) B5093135
theorem B2263615 : Blo 2263435 2263615 := bstep (se 1 (by rfl) ⟨1697711, by rfl⟩ : syracuseStep 2263615 = 3395423) B3395423
theorem B3395429 : Blo 2263435 3395429 := bbase (se 4 (by rfl) ⟨318321, by rfl⟩ : syracuseStep 3395429 = 636643) (by norm_num)
theorem B2263619 : Blo 2263435 2263619 := bstep (se 1 (by rfl) ⟨1697714, by rfl⟩ : syracuseStep 2263619 = 3395429) B3395429
theorem B4297349 : Blo 2263435 4297349 := bbase (se 4 (by rfl) ⟨402876, by rfl⟩ : syracuseStep 4297349 = 805753) (by norm_num)
theorem B2864899 : Blo 2263435 2864899 := bstep (se 1 (by rfl) ⟨2148674, by rfl⟩ : syracuseStep 2864899 = 4297349) B4297349
theorem B3819865 : Blo 2263435 3819865 := bstep (se 2 (by rfl) ⟨1432449, by rfl⟩ : syracuseStep 3819865 = 2864899) B2864899
theorem B5093153 : Blo 2263435 5093153 := bstep (se 2 (by rfl) ⟨1909932, by rfl⟩ : syracuseStep 5093153 = 3819865) B3819865
theorem B3395435 : Blo 2263435 3395435 := bstep (se 1 (by rfl) ⟨2546576, by rfl⟩ : syracuseStep 3395435 = 5093153) B5093153
theorem B2263623 : Blo 2263435 2263623 := bstep (se 1 (by rfl) ⟨1697717, by rfl⟩ : syracuseStep 2263623 = 3395435) B3395435
theorem B2546581 : Blo 2263435 2546581 := bbase (se 6 (by rfl) ⟨59685, by rfl⟩ : syracuseStep 2546581 = 119371) (by norm_num)
theorem B3395441 : Blo 2263435 3395441 := bstep (se 2 (by rfl) ⟨1273290, by rfl⟩ : syracuseStep 3395441 = 2546581) B2546581
theorem B2263627 : Blo 2263435 2263627 := bstep (se 1 (by rfl) ⟨1697720, by rfl⟩ : syracuseStep 2263627 = 3395441) B3395441
theorem B2864909 : Blo 2263435 2864909 := bbase (se 3 (by rfl) ⟨537170, by rfl⟩ : syracuseStep 2864909 = 1074341) (by norm_num)
theorem B7639757 : Blo 2263435 7639757 := bstep (se 3 (by rfl) ⟨1432454, by rfl⟩ : syracuseStep 7639757 = 2864909) B2864909
theorem B5093171 : Blo 2263435 5093171 := bstep (se 1 (by rfl) ⟨3819878, by rfl⟩ : syracuseStep 5093171 = 7639757) B7639757
theorem B3395447 : Blo 2263435 3395447 := bstep (se 1 (by rfl) ⟨2546585, by rfl⟩ : syracuseStep 3395447 = 5093171) B5093171
theorem B2263631 : Blo 2263435 2263631 := bstep (se 1 (by rfl) ⟨1697723, by rfl⟩ : syracuseStep 2263631 = 3395447) B3395447
theorem B3395453 : Blo 2263435 3395453 := bbase (se 3 (by rfl) ⟨636647, by rfl⟩ : syracuseStep 3395453 = 1273295) (by norm_num)
theorem B2263635 : Blo 2263435 2263635 := bstep (se 1 (by rfl) ⟨1697726, by rfl⟩ : syracuseStep 2263635 = 3395453) B3395453
theorem B5093189 : Blo 2263435 5093189 := bbase (se 4 (by rfl) ⟨477486, by rfl⟩ : syracuseStep 5093189 = 954973) (by norm_num)
theorem B3395459 : Blo 2263435 3395459 := bstep (se 1 (by rfl) ⟨2546594, by rfl⟩ : syracuseStep 3395459 = 5093189) B5093189
theorem B2263639 : Blo 2263435 2263639 := bstep (se 1 (by rfl) ⟨1697729, by rfl⟩ : syracuseStep 2263639 = 3395459) B3395459
theorem B2719441 : Blo 2263435 2719441 := bbase (se 2 (by rfl) ⟨1019790, by rfl⟩ : syracuseStep 2719441 = 2039581) (by norm_num)
theorem B3625921 : Blo 2263435 3625921 := bstep (se 2 (by rfl) ⟨1359720, by rfl⟩ : syracuseStep 3625921 = 2719441) B2719441
theorem B4834561 : Blo 2263435 4834561 := bstep (se 2 (by rfl) ⟨1812960, by rfl⟩ : syracuseStep 4834561 = 3625921) B3625921
theorem B6446081 : Blo 2263435 6446081 := bstep (se 2 (by rfl) ⟨2417280, by rfl⟩ : syracuseStep 6446081 = 4834561) B4834561
theorem B4297387 : Blo 2263435 4297387 := bstep (se 1 (by rfl) ⟨3223040, by rfl⟩ : syracuseStep 4297387 = 6446081) B6446081
theorem B5729849 : Blo 2263435 5729849 := bstep (se 2 (by rfl) ⟨2148693, by rfl⟩ : syracuseStep 5729849 = 4297387) B4297387
theorem B3819899 : Blo 2263435 3819899 := bstep (se 1 (by rfl) ⟨2864924, by rfl⟩ : syracuseStep 3819899 = 5729849) B5729849
theorem B2546599 : Blo 2263435 2546599 := bstep (se 1 (by rfl) ⟨1909949, by rfl⟩ : syracuseStep 2546599 = 3819899) B3819899
theorem B3395465 : Blo 2263435 3395465 := bstep (se 2 (by rfl) ⟨1273299, by rfl⟩ : syracuseStep 3395465 = 2546599) B2546599
theorem B2263643 : Blo 2263435 2263643 := bstep (se 1 (by rfl) ⟨1697732, by rfl⟩ : syracuseStep 2263643 = 3395465) B3395465
theorem B11459717 : Blo 2263435 11459717 := bbase (se 4 (by rfl) ⟨1074348, by rfl⟩ : syracuseStep 11459717 = 2148697) (by norm_num)
theorem B7639811 : Blo 2263435 7639811 := bstep (se 1 (by rfl) ⟨5729858, by rfl⟩ : syracuseStep 7639811 = 11459717) B11459717
theorem B5093207 : Blo 2263435 5093207 := bstep (se 1 (by rfl) ⟨3819905, by rfl⟩ : syracuseStep 5093207 = 7639811) B7639811
theorem B3395471 : Blo 2263435 3395471 := bstep (se 1 (by rfl) ⟨2546603, by rfl⟩ : syracuseStep 3395471 = 5093207) B5093207
theorem B2263647 : Blo 2263435 2263647 := bstep (se 1 (by rfl) ⟨1697735, by rfl⟩ : syracuseStep 2263647 = 3395471) B3395471
theorem B3395477 : Blo 2263435 3395477 := bbase (se 6 (by rfl) ⟨79581, by rfl⟩ : syracuseStep 3395477 = 159163) (by norm_num)
theorem B2263651 : Blo 2263435 2263651 := bstep (se 1 (by rfl) ⟨1697738, by rfl⟩ : syracuseStep 2263651 = 3395477) B3395477
theorem B2417293 : Blo 2263435 2417293 := bbase (se 3 (by rfl) ⟨453242, by rfl⟩ : syracuseStep 2417293 = 906485) (by norm_num)
theorem B12892229 : Blo 2263435 12892229 := bstep (se 4 (by rfl) ⟨1208646, by rfl⟩ : syracuseStep 12892229 = 2417293) B2417293
theorem B8594819 : Blo 2263435 8594819 := bstep (se 1 (by rfl) ⟨6446114, by rfl⟩ : syracuseStep 8594819 = 12892229) B12892229
theorem B5729879 : Blo 2263435 5729879 := bstep (se 1 (by rfl) ⟨4297409, by rfl⟩ : syracuseStep 5729879 = 8594819) B8594819
theorem B3819919 : Blo 2263435 3819919 := bstep (se 1 (by rfl) ⟨2864939, by rfl⟩ : syracuseStep 3819919 = 5729879) B5729879
theorem B5093225 : Blo 2263435 5093225 := bstep (se 2 (by rfl) ⟨1909959, by rfl⟩ : syracuseStep 5093225 = 3819919) B3819919
theorem B3395483 : Blo 2263435 3395483 := bstep (se 1 (by rfl) ⟨2546612, by rfl⟩ : syracuseStep 3395483 = 5093225) B5093225
theorem B2263655 : Blo 2263435 2263655 := bstep (se 1 (by rfl) ⟨1697741, by rfl⟩ : syracuseStep 2263655 = 3395483) B3395483
theorem B2546617 : Blo 2263435 2546617 := bbase (se 2 (by rfl) ⟨954981, by rfl⟩ : syracuseStep 2546617 = 1909963) (by norm_num)
theorem B3395489 : Blo 2263435 3395489 := bstep (se 2 (by rfl) ⟨1273308, by rfl⟩ : syracuseStep 3395489 = 2546617) B2546617
theorem B2263659 : Blo 2263435 2263659 := bstep (se 1 (by rfl) ⟨1697744, by rfl⟩ : syracuseStep 2263659 = 3395489) B3395489
theorem B4079197 : Blo 2263435 4079197 := bbase (se 3 (by rfl) ⟨764849, by rfl⟩ : syracuseStep 4079197 = 1529699) (by norm_num)
theorem B5438929 : Blo 2263435 5438929 := bstep (se 2 (by rfl) ⟨2039598, by rfl⟩ : syracuseStep 5438929 = 4079197) B4079197
theorem B7251905 : Blo 2263435 7251905 := bstep (se 2 (by rfl) ⟨2719464, by rfl⟩ : syracuseStep 7251905 = 5438929) B5438929
theorem B4834603 : Blo 2263435 4834603 := bstep (se 1 (by rfl) ⟨3625952, by rfl⟩ : syracuseStep 4834603 = 7251905) B7251905
theorem B6446137 : Blo 2263435 6446137 := bstep (se 2 (by rfl) ⟨2417301, by rfl⟩ : syracuseStep 6446137 = 4834603) B4834603
theorem B8594849 : Blo 2263435 8594849 := bstep (se 2 (by rfl) ⟨3223068, by rfl⟩ : syracuseStep 8594849 = 6446137) B6446137
theorem B5729899 : Blo 2263435 5729899 := bstep (se 1 (by rfl) ⟨4297424, by rfl⟩ : syracuseStep 5729899 = 8594849) B8594849
theorem B7639865 : Blo 2263435 7639865 := bstep (se 2 (by rfl) ⟨2864949, by rfl⟩ : syracuseStep 7639865 = 5729899) B5729899
theorem B5093243 : Blo 2263435 5093243 := bstep (se 1 (by rfl) ⟨3819932, by rfl⟩ : syracuseStep 5093243 = 7639865) B7639865
theorem B3395495 : Blo 2263435 3395495 := bstep (se 1 (by rfl) ⟨2546621, by rfl⟩ : syracuseStep 3395495 = 5093243) B5093243
theorem B2263663 : Blo 2263435 2263663 := bstep (se 1 (by rfl) ⟨1697747, by rfl⟩ : syracuseStep 2263663 = 3395495) B3395495
theorem B3395501 : Blo 2263435 3395501 := bbase (se 3 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 3395501 = 1273313) (by norm_num)
theorem B2263667 : Blo 2263435 2263667 := bstep (se 1 (by rfl) ⟨1697750, by rfl⟩ : syracuseStep 2263667 = 3395501) B3395501
theorem B5093261 : Blo 2263435 5093261 := bbase (se 3 (by rfl) ⟨954986, by rfl⟩ : syracuseStep 5093261 = 1909973) (by norm_num)
theorem B3395507 : Blo 2263435 3395507 := bstep (se 1 (by rfl) ⟨2546630, by rfl⟩ : syracuseStep 3395507 = 5093261) B5093261
theorem B2263671 : Blo 2263435 2263671 := bstep (se 1 (by rfl) ⟨1697753, by rfl⟩ : syracuseStep 2263671 = 3395507) B3395507
theorem B2864965 : Blo 2263435 2864965 := bbase (se 4 (by rfl) ⟨268590, by rfl⟩ : syracuseStep 2864965 = 537181) (by norm_num)
theorem B3819953 : Blo 2263435 3819953 := bstep (se 2 (by rfl) ⟨1432482, by rfl⟩ : syracuseStep 3819953 = 2864965) B2864965
theorem B2546635 : Blo 2263435 2546635 := bstep (se 1 (by rfl) ⟨1909976, by rfl⟩ : syracuseStep 2546635 = 3819953) B3819953
theorem B3395513 : Blo 2263435 3395513 := bstep (se 2 (by rfl) ⟨1273317, by rfl⟩ : syracuseStep 3395513 = 2546635) B2546635
theorem B2263675 : Blo 2263435 2263675 := bstep (se 1 (by rfl) ⟨1697756, by rfl⟩ : syracuseStep 2263675 = 3395513) B3395513
theorem B6202325 : Blo 2263435 6202325 := bbase (se 7 (by rfl) ⟨72683, by rfl⟩ : syracuseStep 6202325 = 145367) (by norm_num)
theorem B4134883 : Blo 2263435 4134883 := bstep (se 1 (by rfl) ⟨3101162, by rfl⟩ : syracuseStep 4134883 = 6202325) B6202325
theorem B5513177 : Blo 2263435 5513177 := bstep (se 2 (by rfl) ⟨2067441, by rfl⟩ : syracuseStep 5513177 = 4134883) B4134883
theorem B3675451 : Blo 2263435 3675451 := bstep (se 1 (by rfl) ⟨2756588, by rfl⟩ : syracuseStep 3675451 = 5513177) B5513177
theorem B4900601 : Blo 2263435 4900601 := bstep (se 2 (by rfl) ⟨1837725, by rfl⟩ : syracuseStep 4900601 = 3675451) B3675451
theorem B3267067 : Blo 2263435 3267067 := bstep (se 1 (by rfl) ⟨2450300, by rfl⟩ : syracuseStep 3267067 = 4900601) B4900601
theorem B4356089 : Blo 2263435 4356089 := bstep (se 2 (by rfl) ⟨1633533, by rfl⟩ : syracuseStep 4356089 = 3267067) B3267067
theorem B2904059 : Blo 2263435 2904059 := bstep (se 1 (by rfl) ⟨2178044, by rfl⟩ : syracuseStep 2904059 = 4356089) B4356089
theorem B7744157 : Blo 2263435 7744157 := bstep (se 3 (by rfl) ⟨1452029, by rfl⟩ : syracuseStep 7744157 = 2904059) B2904059
theorem B5162771 : Blo 2263435 5162771 := bstep (se 1 (by rfl) ⟨3872078, by rfl⟩ : syracuseStep 5162771 = 7744157) B7744157
theorem B3441847 : Blo 2263435 3441847 := bstep (se 1 (by rfl) ⟨2581385, by rfl⟩ : syracuseStep 3441847 = 5162771) B5162771
theorem B4589129 : Blo 2263435 4589129 := bstep (se 2 (by rfl) ⟨1720923, by rfl⟩ : syracuseStep 4589129 = 3441847) B3441847
theorem B3059419 : Blo 2263435 3059419 := bstep (se 1 (by rfl) ⟨2294564, by rfl⟩ : syracuseStep 3059419 = 4589129) B4589129
theorem B4079225 : Blo 2263435 4079225 := bstep (se 2 (by rfl) ⟨1529709, by rfl⟩ : syracuseStep 4079225 = 3059419) B3059419
theorem B10877933 : Blo 2263435 10877933 := bstep (se 3 (by rfl) ⟨2039612, by rfl⟩ : syracuseStep 10877933 = 4079225) B4079225
theorem B29007821 : Blo 2263435 29007821 := bstep (se 3 (by rfl) ⟨5438966, by rfl⟩ : syracuseStep 29007821 = 10877933) B10877933
theorem B19338547 : Blo 2263435 19338547 := bstep (se 1 (by rfl) ⟨14503910, by rfl⟩ : syracuseStep 19338547 = 29007821) B29007821
theorem B25784729 : Blo 2263435 25784729 := bstep (se 2 (by rfl) ⟨9669273, by rfl⟩ : syracuseStep 25784729 = 19338547) B19338547
theorem B17189819 : Blo 2263435 17189819 := bstep (se 1 (by rfl) ⟨12892364, by rfl⟩ : syracuseStep 17189819 = 25784729) B25784729
theorem B11459879 : Blo 2263435 11459879 := bstep (se 1 (by rfl) ⟨8594909, by rfl⟩ : syracuseStep 11459879 = 17189819) B17189819
theorem B7639919 : Blo 2263435 7639919 := bstep (se 1 (by rfl) ⟨5729939, by rfl⟩ : syracuseStep 7639919 = 11459879) B11459879
theorem B5093279 : Blo 2263435 5093279 := bstep (se 1 (by rfl) ⟨3819959, by rfl⟩ : syracuseStep 5093279 = 7639919) B7639919
theorem B3395519 : Blo 2263435 3395519 := bstep (se 1 (by rfl) ⟨2546639, by rfl⟩ : syracuseStep 3395519 = 5093279) B5093279
theorem B2263679 : Blo 2263435 2263679 := bstep (se 1 (by rfl) ⟨1697759, by rfl⟩ : syracuseStep 2263679 = 3395519) B3395519
theorem B3395525 : Blo 2263435 3395525 := bbase (se 4 (by rfl) ⟨318330, by rfl⟩ : syracuseStep 3395525 = 636661) (by norm_num)
theorem B2263683 : Blo 2263435 2263683 := bstep (se 1 (by rfl) ⟨1697762, by rfl⟩ : syracuseStep 2263683 = 3395525) B3395525
theorem B3819973 : Blo 2263435 3819973 := bbase (se 4 (by rfl) ⟨358122, by rfl⟩ : syracuseStep 3819973 = 716245) (by norm_num)
theorem B5093297 : Blo 2263435 5093297 := bstep (se 2 (by rfl) ⟨1909986, by rfl⟩ : syracuseStep 5093297 = 3819973) B3819973
theorem B3395531 : Blo 2263435 3395531 := bstep (se 1 (by rfl) ⟨2546648, by rfl⟩ : syracuseStep 3395531 = 5093297) B5093297
theorem B2263687 : Blo 2263435 2263687 := bstep (se 1 (by rfl) ⟨1697765, by rfl⟩ : syracuseStep 2263687 = 3395531) B3395531
theorem B2546653 : Blo 2263435 2546653 := bbase (se 3 (by rfl) ⟨477497, by rfl⟩ : syracuseStep 2546653 = 954995) (by norm_num)
theorem B3395537 : Blo 2263435 3395537 := bstep (se 2 (by rfl) ⟨1273326, by rfl⟩ : syracuseStep 3395537 = 2546653) B2546653
theorem B2263691 : Blo 2263435 2263691 := bstep (se 1 (by rfl) ⟨1697768, by rfl⟩ : syracuseStep 2263691 = 3395537) B3395537
theorem B7639973 : Blo 2263435 7639973 := bbase (se 4 (by rfl) ⟨716247, by rfl⟩ : syracuseStep 7639973 = 1432495) (by norm_num)
theorem B5093315 : Blo 2263435 5093315 := bstep (se 1 (by rfl) ⟨3819986, by rfl⟩ : syracuseStep 5093315 = 7639973) B7639973
theorem B3395543 : Blo 2263435 3395543 := bstep (se 1 (by rfl) ⟨2546657, by rfl⟩ : syracuseStep 3395543 = 5093315) B5093315
theorem B2263695 : Blo 2263435 2263695 := bstep (se 1 (by rfl) ⟨1697771, by rfl⟩ : syracuseStep 2263695 = 3395543) B3395543
theorem B3395549 : Blo 2263435 3395549 := bbase (se 3 (by rfl) ⟨636665, by rfl⟩ : syracuseStep 3395549 = 1273331) (by norm_num)
theorem B2263699 : Blo 2263435 2263699 := bstep (se 1 (by rfl) ⟨1697774, by rfl⟩ : syracuseStep 2263699 = 3395549) B3395549
theorem B5093333 : Blo 2263435 5093333 := bbase (se 7 (by rfl) ⟨59687, by rfl⟩ : syracuseStep 5093333 = 119375) (by norm_num)
theorem B3395555 : Blo 2263435 3395555 := bstep (se 1 (by rfl) ⟨2546666, by rfl⟩ : syracuseStep 3395555 = 5093333) B5093333
theorem B2263703 : Blo 2263435 2263703 := bstep (se 1 (by rfl) ⟨1697777, by rfl⟩ : syracuseStep 2263703 = 3395555) B3395555
theorem B9178373 : Blo 2263435 9178373 := bbase (se 4 (by rfl) ⟨860472, by rfl⟩ : syracuseStep 9178373 = 1720945) (by norm_num)
theorem B6118915 : Blo 2263435 6118915 := bstep (se 1 (by rfl) ⟨4589186, by rfl⟩ : syracuseStep 6118915 = 9178373) B9178373
theorem B8158553 : Blo 2263435 8158553 := bstep (se 2 (by rfl) ⟨3059457, by rfl⟩ : syracuseStep 8158553 = 6118915) B6118915
theorem B5439035 : Blo 2263435 5439035 := bstep (se 1 (by rfl) ⟨4079276, by rfl⟩ : syracuseStep 5439035 = 8158553) B8158553
theorem B14504093 : Blo 2263435 14504093 := bstep (se 3 (by rfl) ⟨2719517, by rfl⟩ : syracuseStep 14504093 = 5439035) B5439035
theorem B9669395 : Blo 2263435 9669395 := bstep (se 1 (by rfl) ⟨7252046, by rfl⟩ : syracuseStep 9669395 = 14504093) B14504093
theorem B6446263 : Blo 2263435 6446263 := bstep (se 1 (by rfl) ⟨4834697, by rfl⟩ : syracuseStep 6446263 = 9669395) B9669395
theorem B8595017 : Blo 2263435 8595017 := bstep (se 2 (by rfl) ⟨3223131, by rfl⟩ : syracuseStep 8595017 = 6446263) B6446263
theorem B5730011 : Blo 2263435 5730011 := bstep (se 1 (by rfl) ⟨4297508, by rfl⟩ : syracuseStep 5730011 = 8595017) B8595017
theorem B3820007 : Blo 2263435 3820007 := bstep (se 1 (by rfl) ⟨2865005, by rfl⟩ : syracuseStep 3820007 = 5730011) B5730011
theorem B2546671 : Blo 2263435 2546671 := bstep (se 1 (by rfl) ⟨1910003, by rfl⟩ : syracuseStep 2546671 = 3820007) B3820007
theorem B3395561 : Blo 2263435 3395561 := bstep (se 2 (by rfl) ⟨1273335, by rfl⟩ : syracuseStep 3395561 = 2546671) B2546671
theorem B2263707 : Blo 2263435 2263707 := bstep (se 1 (by rfl) ⟨1697780, by rfl⟩ : syracuseStep 2263707 = 3395561) B3395561
theorem B3626029 : Blo 2263435 3626029 := bbase (se 3 (by rfl) ⟨679880, by rfl⟩ : syracuseStep 3626029 = 1359761) (by norm_num)
theorem B19338821 : Blo 2263435 19338821 := bstep (se 4 (by rfl) ⟨1813014, by rfl⟩ : syracuseStep 19338821 = 3626029) B3626029
theorem B12892547 : Blo 2263435 12892547 := bstep (se 1 (by rfl) ⟨9669410, by rfl⟩ : syracuseStep 12892547 = 19338821) B19338821
theorem B8595031 : Blo 2263435 8595031 := bstep (se 1 (by rfl) ⟨6446273, by rfl⟩ : syracuseStep 8595031 = 12892547) B12892547
theorem B11460041 : Blo 2263435 11460041 := bstep (se 2 (by rfl) ⟨4297515, by rfl⟩ : syracuseStep 11460041 = 8595031) B8595031
theorem B7640027 : Blo 2263435 7640027 := bstep (se 1 (by rfl) ⟨5730020, by rfl⟩ : syracuseStep 7640027 = 11460041) B11460041
theorem B5093351 : Blo 2263435 5093351 := bstep (se 1 (by rfl) ⟨3820013, by rfl⟩ : syracuseStep 5093351 = 7640027) B7640027
theorem B3395567 : Blo 2263435 3395567 := bstep (se 1 (by rfl) ⟨2546675, by rfl⟩ : syracuseStep 3395567 = 5093351) B5093351
theorem B2263711 : Blo 2263435 2263711 := bstep (se 1 (by rfl) ⟨1697783, by rfl⟩ : syracuseStep 2263711 = 3395567) B3395567
theorem B3395573 : Blo 2263435 3395573 := bbase (se 5 (by rfl) ⟨159167, by rfl⟩ : syracuseStep 3395573 = 318335) (by norm_num)
theorem B2263715 : Blo 2263435 2263715 := bstep (se 1 (by rfl) ⟨1697786, by rfl⟩ : syracuseStep 2263715 = 3395573) B3395573
theorem B7252085 : Blo 2263435 7252085 := bbase (se 5 (by rfl) ⟨339941, by rfl⟩ : syracuseStep 7252085 = 679883) (by norm_num)
theorem B4834723 : Blo 2263435 4834723 := bstep (se 1 (by rfl) ⟨3626042, by rfl⟩ : syracuseStep 4834723 = 7252085) B7252085
theorem B6446297 : Blo 2263435 6446297 := bstep (se 2 (by rfl) ⟨2417361, by rfl⟩ : syracuseStep 6446297 = 4834723) B4834723
theorem B4297531 : Blo 2263435 4297531 := bstep (se 1 (by rfl) ⟨3223148, by rfl⟩ : syracuseStep 4297531 = 6446297) B6446297
theorem B5730041 : Blo 2263435 5730041 := bstep (se 2 (by rfl) ⟨2148765, by rfl⟩ : syracuseStep 5730041 = 4297531) B4297531
theorem B3820027 : Blo 2263435 3820027 := bstep (se 1 (by rfl) ⟨2865020, by rfl⟩ : syracuseStep 3820027 = 5730041) B5730041
theorem B5093369 : Blo 2263435 5093369 := bstep (se 2 (by rfl) ⟨1910013, by rfl⟩ : syracuseStep 5093369 = 3820027) B3820027
theorem B3395579 : Blo 2263435 3395579 := bstep (se 1 (by rfl) ⟨2546684, by rfl⟩ : syracuseStep 3395579 = 5093369) B5093369
theorem B2263719 : Blo 2263435 2263719 := bstep (se 1 (by rfl) ⟨1697789, by rfl⟩ : syracuseStep 2263719 = 3395579) B3395579
theorem B2546689 : Blo 2263435 2546689 := bbase (se 2 (by rfl) ⟨955008, by rfl⟩ : syracuseStep 2546689 = 1910017) (by norm_num)
theorem B3395585 : Blo 2263435 3395585 := bstep (se 2 (by rfl) ⟨1273344, by rfl⟩ : syracuseStep 3395585 = 2546689) B2546689
theorem B2263723 : Blo 2263435 2263723 := bstep (se 1 (by rfl) ⟨1697792, by rfl⟩ : syracuseStep 2263723 = 3395585) B3395585
theorem B5730061 : Blo 2263435 5730061 := bbase (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) (by norm_num)
theorem B7640081 : Blo 2263435 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B5093387 : Blo 2263435 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B3395591 : Blo 2263435 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B2263727 : Blo 2263435 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B3395597 : Blo 2263435 3395597 := bbase (se 3 (by rfl) ⟨636674, by rfl⟩ : syracuseStep 3395597 = 1273349) (by norm_num)
theorem B2263731 : Blo 2263435 2263731 := bstep (se 1 (by rfl) ⟨1697798, by rfl⟩ : syracuseStep 2263731 = 3395597) B3395597
theorem B5093405 : Blo 2263435 5093405 := bbase (se 3 (by rfl) ⟨955013, by rfl⟩ : syracuseStep 5093405 = 1910027) (by norm_num)
theorem B3395603 : Blo 2263435 3395603 := bstep (se 1 (by rfl) ⟨2546702, by rfl⟩ : syracuseStep 3395603 = 5093405) B5093405
theorem B2263735 : Blo 2263435 2263735 := bstep (se 1 (by rfl) ⟨1697801, by rfl⟩ : syracuseStep 2263735 = 3395603) B3395603
theorem B3820061 : Blo 2263435 3820061 := bbase (se 3 (by rfl) ⟨716261, by rfl⟩ : syracuseStep 3820061 = 1432523) (by norm_num)
theorem B2546707 : Blo 2263435 2546707 := bstep (se 1 (by rfl) ⟨1910030, by rfl⟩ : syracuseStep 2546707 = 3820061) B3820061
theorem B3395609 : Blo 2263435 3395609 := bstep (se 2 (by rfl) ⟨1273353, by rfl⟩ : syracuseStep 3395609 = 2546707) B2546707
theorem B2263739 : Blo 2263435 2263739 := bstep (se 1 (by rfl) ⟨1697804, by rfl⟩ : syracuseStep 2263739 = 3395609) B3395609
theorem B9178517 : Blo 2263435 9178517 := bbase (se 6 (by rfl) ⟨215121, by rfl⟩ : syracuseStep 9178517 = 430243) (by norm_num)
theorem B6119011 : Blo 2263435 6119011 := bstep (se 1 (by rfl) ⟨4589258, by rfl⟩ : syracuseStep 6119011 = 9178517) B9178517
theorem B8158681 : Blo 2263435 8158681 := bstep (se 2 (by rfl) ⟨3059505, by rfl⟩ : syracuseStep 8158681 = 6119011) B6119011
theorem B10878241 : Blo 2263435 10878241 := bstep (se 2 (by rfl) ⟨4079340, by rfl⟩ : syracuseStep 10878241 = 8158681) B8158681
theorem B14504321 : Blo 2263435 14504321 := bstep (se 2 (by rfl) ⟨5439120, by rfl⟩ : syracuseStep 14504321 = 10878241) B10878241
theorem B9669547 : Blo 2263435 9669547 := bstep (se 1 (by rfl) ⟨7252160, by rfl⟩ : syracuseStep 9669547 = 14504321) B14504321
theorem B12892729 : Blo 2263435 12892729 := bstep (se 2 (by rfl) ⟨4834773, by rfl⟩ : syracuseStep 12892729 = 9669547) B9669547
theorem B17190305 : Blo 2263435 17190305 := bstep (se 2 (by rfl) ⟨6446364, by rfl⟩ : syracuseStep 17190305 = 12892729) B12892729
theorem B11460203 : Blo 2263435 11460203 := bstep (se 1 (by rfl) ⟨8595152, by rfl⟩ : syracuseStep 11460203 = 17190305) B17190305
theorem B7640135 : Blo 2263435 7640135 := bstep (se 1 (by rfl) ⟨5730101, by rfl⟩ : syracuseStep 7640135 = 11460203) B11460203
theorem B5093423 : Blo 2263435 5093423 := bstep (se 1 (by rfl) ⟨3820067, by rfl⟩ : syracuseStep 5093423 = 7640135) B7640135
theorem B3395615 : Blo 2263435 3395615 := bstep (se 1 (by rfl) ⟨2546711, by rfl⟩ : syracuseStep 3395615 = 5093423) B5093423
theorem B2263743 : Blo 2263435 2263743 := bstep (se 1 (by rfl) ⟨1697807, by rfl⟩ : syracuseStep 2263743 = 3395615) B3395615
theorem B3395621 : Blo 2263435 3395621 := bbase (se 4 (by rfl) ⟨318339, by rfl⟩ : syracuseStep 3395621 = 636679) (by norm_num)
theorem B2263747 : Blo 2263435 2263747 := bstep (se 1 (by rfl) ⟨1697810, by rfl⟩ : syracuseStep 2263747 = 3395621) B3395621
theorem B2865061 : Blo 2263435 2865061 := bbase (se 4 (by rfl) ⟨268599, by rfl⟩ : syracuseStep 2865061 = 537199) (by norm_num)
theorem B3820081 : Blo 2263435 3820081 := bstep (se 2 (by rfl) ⟨1432530, by rfl⟩ : syracuseStep 3820081 = 2865061) B2865061
theorem B5093441 : Blo 2263435 5093441 := bstep (se 2 (by rfl) ⟨1910040, by rfl⟩ : syracuseStep 5093441 = 3820081) B3820081
theorem B3395627 : Blo 2263435 3395627 := bstep (se 1 (by rfl) ⟨2546720, by rfl⟩ : syracuseStep 3395627 = 5093441) B5093441
theorem B2263751 : Blo 2263435 2263751 := bstep (se 1 (by rfl) ⟨1697813, by rfl⟩ : syracuseStep 2263751 = 3395627) B3395627
theorem B2546725 : Blo 2263435 2546725 := bbase (se 4 (by rfl) ⟨238755, by rfl⟩ : syracuseStep 2546725 = 477511) (by norm_num)
theorem B3395633 : Blo 2263435 3395633 := bstep (se 2 (by rfl) ⟨1273362, by rfl⟩ : syracuseStep 3395633 = 2546725) B2546725
theorem B2263755 : Blo 2263435 2263755 := bstep (se 1 (by rfl) ⟨1697816, by rfl⟩ : syracuseStep 2263755 = 3395633) B3395633
theorem B7252213 : Blo 2263435 7252213 := bbase (se 5 (by rfl) ⟨339947, by rfl⟩ : syracuseStep 7252213 = 679895) (by norm_num)
theorem B9669617 : Blo 2263435 9669617 := bstep (se 2 (by rfl) ⟨3626106, by rfl⟩ : syracuseStep 9669617 = 7252213) B7252213
theorem B6446411 : Blo 2263435 6446411 := bstep (se 1 (by rfl) ⟨4834808, by rfl⟩ : syracuseStep 6446411 = 9669617) B9669617
theorem B4297607 : Blo 2263435 4297607 := bstep (se 1 (by rfl) ⟨3223205, by rfl⟩ : syracuseStep 4297607 = 6446411) B6446411
theorem B2865071 : Blo 2263435 2865071 := bstep (se 1 (by rfl) ⟨2148803, by rfl⟩ : syracuseStep 2865071 = 4297607) B4297607
theorem B7640189 : Blo 2263435 7640189 := bstep (se 3 (by rfl) ⟨1432535, by rfl⟩ : syracuseStep 7640189 = 2865071) B2865071
theorem B5093459 : Blo 2263435 5093459 := bstep (se 1 (by rfl) ⟨3820094, by rfl⟩ : syracuseStep 5093459 = 7640189) B7640189
theorem B3395639 : Blo 2263435 3395639 := bstep (se 1 (by rfl) ⟨2546729, by rfl⟩ : syracuseStep 3395639 = 5093459) B5093459
theorem B2263759 : Blo 2263435 2263759 := bstep (se 1 (by rfl) ⟨1697819, by rfl⟩ : syracuseStep 2263759 = 3395639) B3395639
theorem B3395645 : Blo 2263435 3395645 := bbase (se 3 (by rfl) ⟨636683, by rfl⟩ : syracuseStep 3395645 = 1273367) (by norm_num)
theorem B2263763 : Blo 2263435 2263763 := bstep (se 1 (by rfl) ⟨1697822, by rfl⟩ : syracuseStep 2263763 = 3395645) B3395645
theorem B5093477 : Blo 2263435 5093477 := bbase (se 4 (by rfl) ⟨477513, by rfl⟩ : syracuseStep 5093477 = 955027) (by norm_num)
theorem B3395651 : Blo 2263435 3395651 := bstep (se 1 (by rfl) ⟨2546738, by rfl⟩ : syracuseStep 3395651 = 5093477) B5093477
theorem B2263767 : Blo 2263435 2263767 := bstep (se 1 (by rfl) ⟨1697825, by rfl⟩ : syracuseStep 2263767 = 3395651) B3395651
theorem B5730173 : Blo 2263435 5730173 := bbase (se 3 (by rfl) ⟨1074407, by rfl⟩ : syracuseStep 5730173 = 2148815) (by norm_num)
theorem B3820115 : Blo 2263435 3820115 := bstep (se 1 (by rfl) ⟨2865086, by rfl⟩ : syracuseStep 3820115 = 5730173) B5730173
theorem B2546743 : Blo 2263435 2546743 := bstep (se 1 (by rfl) ⟨1910057, by rfl⟩ : syracuseStep 2546743 = 3820115) B3820115
theorem B3395657 : Blo 2263435 3395657 := bstep (se 2 (by rfl) ⟨1273371, by rfl⟩ : syracuseStep 3395657 = 2546743) B2546743
theorem B2263771 : Blo 2263435 2263771 := bstep (se 1 (by rfl) ⟨1697828, by rfl⟩ : syracuseStep 2263771 = 3395657) B3395657
theorem B4297637 : Blo 2263435 4297637 := bbase (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) (by norm_num)
theorem B11460365 : Blo 2263435 11460365 := bstep (se 3 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 11460365 = 4297637) B4297637
theorem B7640243 : Blo 2263435 7640243 := bstep (se 1 (by rfl) ⟨5730182, by rfl⟩ : syracuseStep 7640243 = 11460365) B11460365
theorem B5093495 : Blo 2263435 5093495 := bstep (se 1 (by rfl) ⟨3820121, by rfl⟩ : syracuseStep 5093495 = 7640243) B7640243
theorem B3395663 : Blo 2263435 3395663 := bstep (se 1 (by rfl) ⟨2546747, by rfl⟩ : syracuseStep 3395663 = 5093495) B5093495
theorem B2263775 : Blo 2263435 2263775 := bstep (se 1 (by rfl) ⟨1697831, by rfl⟩ : syracuseStep 2263775 = 3395663) B3395663
theorem B3395669 : Blo 2263435 3395669 := bbase (se 8 (by rfl) ⟨19896, by rfl⟩ : syracuseStep 3395669 = 39793) (by norm_num)
theorem B2263779 : Blo 2263435 2263779 := bstep (se 1 (by rfl) ⟨1697834, by rfl⟩ : syracuseStep 2263779 = 3395669) B3395669
theorem B4079413 : Blo 2263435 4079413 := bbase (se 5 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 4079413 = 382445) (by norm_num)
theorem B21756869 : Blo 2263435 21756869 := bstep (se 4 (by rfl) ⟨2039706, by rfl⟩ : syracuseStep 21756869 = 4079413) B4079413
theorem B14504579 : Blo 2263435 14504579 := bstep (se 1 (by rfl) ⟨10878434, by rfl⟩ : syracuseStep 14504579 = 21756869) B21756869
theorem B9669719 : Blo 2263435 9669719 := bstep (se 1 (by rfl) ⟨7252289, by rfl⟩ : syracuseStep 9669719 = 14504579) B14504579
theorem B6446479 : Blo 2263435 6446479 := bstep (se 1 (by rfl) ⟨4834859, by rfl⟩ : syracuseStep 6446479 = 9669719) B9669719
theorem B8595305 : Blo 2263435 8595305 := bstep (se 2 (by rfl) ⟨3223239, by rfl⟩ : syracuseStep 8595305 = 6446479) B6446479
theorem B5730203 : Blo 2263435 5730203 := bstep (se 1 (by rfl) ⟨4297652, by rfl⟩ : syracuseStep 5730203 = 8595305) B8595305
theorem B3820135 : Blo 2263435 3820135 := bstep (se 1 (by rfl) ⟨2865101, by rfl⟩ : syracuseStep 3820135 = 5730203) B5730203
theorem B5093513 : Blo 2263435 5093513 := bstep (se 2 (by rfl) ⟨1910067, by rfl⟩ : syracuseStep 5093513 = 3820135) B3820135
theorem B3395675 : Blo 2263435 3395675 := bstep (se 1 (by rfl) ⟨2546756, by rfl⟩ : syracuseStep 3395675 = 5093513) B5093513
theorem B2263783 : Blo 2263435 2263783 := bstep (se 1 (by rfl) ⟨1697837, by rfl⟩ : syracuseStep 2263783 = 3395675) B3395675
theorem B2546761 : Blo 2263435 2546761 := bbase (se 2 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 2546761 = 1910071) (by norm_num)
theorem B3395681 : Blo 2263435 3395681 := bstep (se 2 (by rfl) ⟨1273380, by rfl⟩ : syracuseStep 3395681 = 2546761) B2546761
theorem B2263787 : Blo 2263435 2263787 := bstep (se 1 (by rfl) ⟨1697840, by rfl⟩ : syracuseStep 2263787 = 3395681) B3395681
theorem B14504629 : Blo 2263435 14504629 := bbase (se 5 (by rfl) ⟨679904, by rfl⟩ : syracuseStep 14504629 = 1359809) (by norm_num)
theorem B19339505 : Blo 2263435 19339505 := bstep (se 2 (by rfl) ⟨7252314, by rfl⟩ : syracuseStep 19339505 = 14504629) B14504629
theorem B12893003 : Blo 2263435 12893003 := bstep (se 1 (by rfl) ⟨9669752, by rfl⟩ : syracuseStep 12893003 = 19339505) B19339505
theorem B8595335 : Blo 2263435 8595335 := bstep (se 1 (by rfl) ⟨6446501, by rfl⟩ : syracuseStep 8595335 = 12893003) B12893003
theorem B5730223 : Blo 2263435 5730223 := bstep (se 1 (by rfl) ⟨4297667, by rfl⟩ : syracuseStep 5730223 = 8595335) B8595335
theorem B7640297 : Blo 2263435 7640297 := bstep (se 2 (by rfl) ⟨2865111, by rfl⟩ : syracuseStep 7640297 = 5730223) B5730223
theorem B5093531 : Blo 2263435 5093531 := bstep (se 1 (by rfl) ⟨3820148, by rfl⟩ : syracuseStep 5093531 = 7640297) B7640297
theorem B3395687 : Blo 2263435 3395687 := bstep (se 1 (by rfl) ⟨2546765, by rfl⟩ : syracuseStep 3395687 = 5093531) B5093531
theorem B2263791 : Blo 2263435 2263791 := bstep (se 1 (by rfl) ⟨1697843, by rfl⟩ : syracuseStep 2263791 = 3395687) B3395687
theorem B3395693 : Blo 2263435 3395693 := bbase (se 3 (by rfl) ⟨636692, by rfl⟩ : syracuseStep 3395693 = 1273385) (by norm_num)
theorem B2263795 : Blo 2263435 2263795 := bstep (se 1 (by rfl) ⟨1697846, by rfl⟩ : syracuseStep 2263795 = 3395693) B3395693
theorem B5093549 : Blo 2263435 5093549 := bbase (se 3 (by rfl) ⟨955040, by rfl⟩ : syracuseStep 5093549 = 1910081) (by norm_num)
theorem B3395699 : Blo 2263435 3395699 := bstep (se 1 (by rfl) ⟨2546774, by rfl⟩ : syracuseStep 3395699 = 5093549) B5093549
theorem B2263799 : Blo 2263435 2263799 := bstep (se 1 (by rfl) ⟨1697849, by rfl⟩ : syracuseStep 2263799 = 3395699) B3395699
theorem B10878533 : Blo 2263435 10878533 := bbase (se 4 (by rfl) ⟨1019862, by rfl⟩ : syracuseStep 10878533 = 2039725) (by norm_num)
theorem B7252355 : Blo 2263435 7252355 := bstep (se 1 (by rfl) ⟨5439266, by rfl⟩ : syracuseStep 7252355 = 10878533) B10878533
theorem B4834903 : Blo 2263435 4834903 := bstep (se 1 (by rfl) ⟨3626177, by rfl⟩ : syracuseStep 4834903 = 7252355) B7252355
theorem B6446537 : Blo 2263435 6446537 := bstep (se 2 (by rfl) ⟨2417451, by rfl⟩ : syracuseStep 6446537 = 4834903) B4834903
theorem B4297691 : Blo 2263435 4297691 := bstep (se 1 (by rfl) ⟨3223268, by rfl⟩ : syracuseStep 4297691 = 6446537) B6446537
theorem B2865127 : Blo 2263435 2865127 := bstep (se 1 (by rfl) ⟨2148845, by rfl⟩ : syracuseStep 2865127 = 4297691) B4297691
theorem B3820169 : Blo 2263435 3820169 := bstep (se 2 (by rfl) ⟨1432563, by rfl⟩ : syracuseStep 3820169 = 2865127) B2865127
theorem B2546779 : Blo 2263435 2546779 := bstep (se 1 (by rfl) ⟨1910084, by rfl⟩ : syracuseStep 2546779 = 3820169) B3820169
theorem B3395705 : Blo 2263435 3395705 := bstep (se 2 (by rfl) ⟨1273389, by rfl⟩ : syracuseStep 3395705 = 2546779) B2546779
theorem B2263803 : Blo 2263435 2263803 := bstep (se 1 (by rfl) ⟨1697852, by rfl⟩ : syracuseStep 2263803 = 3395705) B3395705
theorem B2719637 : Blo 2263435 2719637 := bbase (se 6 (by rfl) ⟨63741, by rfl⟩ : syracuseStep 2719637 = 127483) (by norm_num)
theorem B29009461 : Blo 2263435 29009461 := bstep (se 5 (by rfl) ⟨1359818, by rfl⟩ : syracuseStep 29009461 = 2719637) B2719637
theorem B38679281 : Blo 2263435 38679281 := bstep (se 2 (by rfl) ⟨14504730, by rfl⟩ : syracuseStep 38679281 = 29009461) B29009461
theorem B25786187 : Blo 2263435 25786187 := bstep (se 1 (by rfl) ⟨19339640, by rfl⟩ : syracuseStep 25786187 = 38679281) B38679281
theorem B17190791 : Blo 2263435 17190791 := bstep (se 1 (by rfl) ⟨12893093, by rfl⟩ : syracuseStep 17190791 = 25786187) B25786187
theorem B11460527 : Blo 2263435 11460527 := bstep (se 1 (by rfl) ⟨8595395, by rfl⟩ : syracuseStep 11460527 = 17190791) B17190791
theorem B7640351 : Blo 2263435 7640351 := bstep (se 1 (by rfl) ⟨5730263, by rfl⟩ : syracuseStep 7640351 = 11460527) B11460527
theorem B5093567 : Blo 2263435 5093567 := bstep (se 1 (by rfl) ⟨3820175, by rfl⟩ : syracuseStep 5093567 = 7640351) B7640351
theorem B3395711 : Blo 2263435 3395711 := bstep (se 1 (by rfl) ⟨2546783, by rfl⟩ : syracuseStep 3395711 = 5093567) B5093567
theorem B2263807 : Blo 2263435 2263807 := bstep (se 1 (by rfl) ⟨1697855, by rfl⟩ : syracuseStep 2263807 = 3395711) B3395711
theorem B3395717 : Blo 2263435 3395717 := bbase (se 4 (by rfl) ⟨318348, by rfl⟩ : syracuseStep 3395717 = 636697) (by norm_num)
theorem B2263811 : Blo 2263435 2263811 := bstep (se 1 (by rfl) ⟨1697858, by rfl⟩ : syracuseStep 2263811 = 3395717) B3395717
theorem B3820189 : Blo 2263435 3820189 := bbase (se 3 (by rfl) ⟨716285, by rfl⟩ : syracuseStep 3820189 = 1432571) (by norm_num)
theorem B5093585 : Blo 2263435 5093585 := bstep (se 2 (by rfl) ⟨1910094, by rfl⟩ : syracuseStep 5093585 = 3820189) B3820189
theorem B3395723 : Blo 2263435 3395723 := bstep (se 1 (by rfl) ⟨2546792, by rfl⟩ : syracuseStep 3395723 = 5093585) B5093585
theorem B2263815 : Blo 2263435 2263815 := bstep (se 1 (by rfl) ⟨1697861, by rfl⟩ : syracuseStep 2263815 = 3395723) B3395723
theorem B2546797 : Blo 2263435 2546797 := bbase (se 3 (by rfl) ⟨477524, by rfl⟩ : syracuseStep 2546797 = 955049) (by norm_num)
theorem B3395729 : Blo 2263435 3395729 := bstep (se 2 (by rfl) ⟨1273398, by rfl⟩ : syracuseStep 3395729 = 2546797) B2546797
theorem B2263819 : Blo 2263435 2263819 := bstep (se 1 (by rfl) ⟨1697864, by rfl⟩ : syracuseStep 2263819 = 3395729) B3395729
theorem B7640405 : Blo 2263435 7640405 := bbase (se 14 (by rfl) ⟨699, by rfl⟩ : syracuseStep 7640405 = 1399) (by norm_num)
theorem B5093603 : Blo 2263435 5093603 := bstep (se 1 (by rfl) ⟨3820202, by rfl⟩ : syracuseStep 5093603 = 7640405) B7640405
theorem B3395735 : Blo 2263435 3395735 := bstep (se 1 (by rfl) ⟨2546801, by rfl⟩ : syracuseStep 3395735 = 5093603) B5093603
theorem B2263823 : Blo 2263435 2263823 := bstep (se 1 (by rfl) ⟨1697867, by rfl⟩ : syracuseStep 2263823 = 3395735) B3395735
theorem B3395741 : Blo 2263435 3395741 := bbase (se 3 (by rfl) ⟨636701, by rfl⟩ : syracuseStep 3395741 = 1273403) (by norm_num)
theorem B2263827 : Blo 2263435 2263827 := bstep (se 1 (by rfl) ⟨1697870, by rfl⟩ : syracuseStep 2263827 = 3395741) B3395741
theorem B5093621 : Blo 2263435 5093621 := bbase (se 5 (by rfl) ⟨238763, by rfl⟩ : syracuseStep 5093621 = 477527) (by norm_num)
theorem B3395747 : Blo 2263435 3395747 := bstep (se 1 (by rfl) ⟨2546810, by rfl⟩ : syracuseStep 3395747 = 5093621) B5093621
theorem B2263831 : Blo 2263435 2263831 := bstep (se 1 (by rfl) ⟨1697873, by rfl⟩ : syracuseStep 2263831 = 3395747) B3395747
theorem B18357781 : Blo 2263435 18357781 := bbase (se 6 (by rfl) ⟨430260, by rfl⟩ : syracuseStep 18357781 = 860521) (by norm_num)
theorem B24477041 : Blo 2263435 24477041 := bstep (se 2 (by rfl) ⟨9178890, by rfl⟩ : syracuseStep 24477041 = 18357781) B18357781
theorem B16318027 : Blo 2263435 16318027 := bstep (se 1 (by rfl) ⟨12238520, by rfl⟩ : syracuseStep 16318027 = 24477041) B24477041
theorem B21757369 : Blo 2263435 21757369 := bstep (se 2 (by rfl) ⟨8159013, by rfl⟩ : syracuseStep 21757369 = 16318027) B16318027
theorem B29009825 : Blo 2263435 29009825 := bstep (se 2 (by rfl) ⟨10878684, by rfl⟩ : syracuseStep 29009825 = 21757369) B21757369
theorem B19339883 : Blo 2263435 19339883 := bstep (se 1 (by rfl) ⟨14504912, by rfl⟩ : syracuseStep 19339883 = 29009825) B29009825
theorem B12893255 : Blo 2263435 12893255 := bstep (se 1 (by rfl) ⟨9669941, by rfl⟩ : syracuseStep 12893255 = 19339883) B19339883
theorem B8595503 : Blo 2263435 8595503 := bstep (se 1 (by rfl) ⟨6446627, by rfl⟩ : syracuseStep 8595503 = 12893255) B12893255
theorem B5730335 : Blo 2263435 5730335 := bstep (se 1 (by rfl) ⟨4297751, by rfl⟩ : syracuseStep 5730335 = 8595503) B8595503
theorem B3820223 : Blo 2263435 3820223 := bstep (se 1 (by rfl) ⟨2865167, by rfl⟩ : syracuseStep 3820223 = 5730335) B5730335
theorem B2546815 : Blo 2263435 2546815 := bstep (se 1 (by rfl) ⟨1910111, by rfl⟩ : syracuseStep 2546815 = 3820223) B3820223
theorem B3395753 : Blo 2263435 3395753 := bstep (se 2 (by rfl) ⟨1273407, by rfl⟩ : syracuseStep 3395753 = 2546815) B2546815
theorem B2263835 : Blo 2263435 2263835 := bstep (se 1 (by rfl) ⟨1697876, by rfl⟩ : syracuseStep 2263835 = 3395753) B3395753
theorem B7252469 : Blo 2263435 7252469 := bbase (se 5 (by rfl) ⟨339959, by rfl⟩ : syracuseStep 7252469 = 679919) (by norm_num)
theorem B4834979 : Blo 2263435 4834979 := bstep (se 1 (by rfl) ⟨3626234, by rfl⟩ : syracuseStep 4834979 = 7252469) B7252469
theorem B3223319 : Blo 2263435 3223319 := bstep (se 1 (by rfl) ⟨2417489, by rfl⟩ : syracuseStep 3223319 = 4834979) B4834979
theorem B8595517 : Blo 2263435 8595517 := bstep (se 3 (by rfl) ⟨1611659, by rfl⟩ : syracuseStep 8595517 = 3223319) B3223319
theorem B11460689 : Blo 2263435 11460689 := bstep (se 2 (by rfl) ⟨4297758, by rfl⟩ : syracuseStep 11460689 = 8595517) B8595517
theorem B7640459 : Blo 2263435 7640459 := bstep (se 1 (by rfl) ⟨5730344, by rfl⟩ : syracuseStep 7640459 = 11460689) B11460689
theorem B5093639 : Blo 2263435 5093639 := bstep (se 1 (by rfl) ⟨3820229, by rfl⟩ : syracuseStep 5093639 = 7640459) B7640459
theorem B3395759 : Blo 2263435 3395759 := bstep (se 1 (by rfl) ⟨2546819, by rfl⟩ : syracuseStep 3395759 = 5093639) B5093639
theorem B2263839 : Blo 2263435 2263839 := bstep (se 1 (by rfl) ⟨1697879, by rfl⟩ : syracuseStep 2263839 = 3395759) B3395759
theorem B3395765 : Blo 2263435 3395765 := bbase (se 5 (by rfl) ⟨159176, by rfl⟩ : syracuseStep 3395765 = 318353) (by norm_num)
theorem B2263843 : Blo 2263435 2263843 := bstep (se 1 (by rfl) ⟨1697882, by rfl⟩ : syracuseStep 2263843 = 3395765) B3395765
theorem B5730365 : Blo 2263435 5730365 := bbase (se 3 (by rfl) ⟨1074443, by rfl⟩ : syracuseStep 5730365 = 2148887) (by norm_num)
theorem B3820243 : Blo 2263435 3820243 := bstep (se 1 (by rfl) ⟨2865182, by rfl⟩ : syracuseStep 3820243 = 5730365) B5730365
theorem B5093657 : Blo 2263435 5093657 := bstep (se 2 (by rfl) ⟨1910121, by rfl⟩ : syracuseStep 5093657 = 3820243) B3820243
theorem B3395771 : Blo 2263435 3395771 := bstep (se 1 (by rfl) ⟨2546828, by rfl⟩ : syracuseStep 3395771 = 5093657) B5093657
theorem B2263847 : Blo 2263435 2263847 := bstep (se 1 (by rfl) ⟨1697885, by rfl⟩ : syracuseStep 2263847 = 3395771) B3395771
theorem B2546833 : Blo 2263435 2546833 := bbase (se 2 (by rfl) ⟨955062, by rfl⟩ : syracuseStep 2546833 = 1910125) (by norm_num)
theorem B3395777 : Blo 2263435 3395777 := bstep (se 2 (by rfl) ⟨1273416, by rfl⟩ : syracuseStep 3395777 = 2546833) B2546833
theorem B2263851 : Blo 2263435 2263851 := bstep (se 1 (by rfl) ⟨1697888, by rfl⟩ : syracuseStep 2263851 = 3395777) B3395777
theorem B4297789 : Blo 2263435 4297789 := bbase (se 3 (by rfl) ⟨805835, by rfl⟩ : syracuseStep 4297789 = 1611671) (by norm_num)
theorem B5730385 : Blo 2263435 5730385 := bstep (se 2 (by rfl) ⟨2148894, by rfl⟩ : syracuseStep 5730385 = 4297789) B4297789
theorem B7640513 : Blo 2263435 7640513 := bstep (se 2 (by rfl) ⟨2865192, by rfl⟩ : syracuseStep 7640513 = 5730385) B5730385
theorem B5093675 : Blo 2263435 5093675 := bstep (se 1 (by rfl) ⟨3820256, by rfl⟩ : syracuseStep 5093675 = 7640513) B7640513
theorem B3395783 : Blo 2263435 3395783 := bstep (se 1 (by rfl) ⟨2546837, by rfl⟩ : syracuseStep 3395783 = 5093675) B5093675
theorem B2263855 : Blo 2263435 2263855 := bstep (se 1 (by rfl) ⟨1697891, by rfl⟩ : syracuseStep 2263855 = 3395783) B3395783
theorem B3395789 : Blo 2263435 3395789 := bbase (se 3 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 3395789 = 1273421) (by norm_num)
theorem B2263859 : Blo 2263435 2263859 := bstep (se 1 (by rfl) ⟨1697894, by rfl⟩ : syracuseStep 2263859 = 3395789) B3395789
theorem B5093693 : Blo 2263435 5093693 := bbase (se 3 (by rfl) ⟨955067, by rfl⟩ : syracuseStep 5093693 = 1910135) (by norm_num)
theorem B3395795 : Blo 2263435 3395795 := bstep (se 1 (by rfl) ⟨2546846, by rfl⟩ : syracuseStep 3395795 = 5093693) B5093693
theorem B2263863 : Blo 2263435 2263863 := bstep (se 1 (by rfl) ⟨1697897, by rfl⟩ : syracuseStep 2263863 = 3395795) B3395795
theorem B3820277 : Blo 2263435 3820277 := bbase (se 5 (by rfl) ⟨179075, by rfl⟩ : syracuseStep 3820277 = 358151) (by norm_num)
theorem B2546851 : Blo 2263435 2546851 := bstep (se 1 (by rfl) ⟨1910138, by rfl⟩ : syracuseStep 2546851 = 3820277) B3820277
theorem B3395801 : Blo 2263435 3395801 := bstep (se 2 (by rfl) ⟨1273425, by rfl⟩ : syracuseStep 3395801 = 2546851) B2546851
theorem B2263867 : Blo 2263435 2263867 := bstep (se 1 (by rfl) ⟨1697900, by rfl⟩ : syracuseStep 2263867 = 3395801) B3395801
theorem B11027285 : Blo 2263435 11027285 := bbase (se 9 (by rfl) ⟨32306, by rfl⟩ : syracuseStep 11027285 = 64613) (by norm_num)
theorem B7351523 : Blo 2263435 7351523 := bstep (se 1 (by rfl) ⟨5513642, by rfl⟩ : syracuseStep 7351523 = 11027285) B11027285
theorem B4901015 : Blo 2263435 4901015 := bstep (se 1 (by rfl) ⟨3675761, by rfl⟩ : syracuseStep 4901015 = 7351523) B7351523
theorem B3267343 : Blo 2263435 3267343 := bstep (se 1 (by rfl) ⟨2450507, by rfl⟩ : syracuseStep 3267343 = 4901015) B4901015
theorem B17425829 : Blo 2263435 17425829 := bstep (se 4 (by rfl) ⟨1633671, by rfl⟩ : syracuseStep 17425829 = 3267343) B3267343
theorem B11617219 : Blo 2263435 11617219 := bstep (se 1 (by rfl) ⟨8712914, by rfl⟩ : syracuseStep 11617219 = 17425829) B17425829
theorem B15489625 : Blo 2263435 15489625 := bstep (se 2 (by rfl) ⟨5808609, by rfl⟩ : syracuseStep 15489625 = 11617219) B11617219
theorem B20652833 : Blo 2263435 20652833 := bstep (se 2 (by rfl) ⟨7744812, by rfl⟩ : syracuseStep 20652833 = 15489625) B15489625
theorem B13768555 : Blo 2263435 13768555 := bstep (se 1 (by rfl) ⟨10326416, by rfl⟩ : syracuseStep 13768555 = 20652833) B20652833
theorem B18358073 : Blo 2263435 18358073 := bstep (se 2 (by rfl) ⟨6884277, by rfl⟩ : syracuseStep 18358073 = 13768555) B13768555
theorem B12238715 : Blo 2263435 12238715 := bstep (se 1 (by rfl) ⟨9179036, by rfl⟩ : syracuseStep 12238715 = 18358073) B18358073
theorem B8159143 : Blo 2263435 8159143 := bstep (se 1 (by rfl) ⟨6119357, by rfl⟩ : syracuseStep 8159143 = 12238715) B12238715
theorem B10878857 : Blo 2263435 10878857 := bstep (se 2 (by rfl) ⟨4079571, by rfl⟩ : syracuseStep 10878857 = 8159143) B8159143
theorem B7252571 : Blo 2263435 7252571 := bstep (se 1 (by rfl) ⟨5439428, by rfl⟩ : syracuseStep 7252571 = 10878857) B10878857
theorem B4835047 : Blo 2263435 4835047 := bstep (se 1 (by rfl) ⟨3626285, by rfl⟩ : syracuseStep 4835047 = 7252571) B7252571
theorem B6446729 : Blo 2263435 6446729 := bstep (se 2 (by rfl) ⟨2417523, by rfl⟩ : syracuseStep 6446729 = 4835047) B4835047
theorem B17191277 : Blo 2263435 17191277 := bstep (se 3 (by rfl) ⟨3223364, by rfl⟩ : syracuseStep 17191277 = 6446729) B6446729
theorem B11460851 : Blo 2263435 11460851 := bstep (se 1 (by rfl) ⟨8595638, by rfl⟩ : syracuseStep 11460851 = 17191277) B17191277
theorem B7640567 : Blo 2263435 7640567 := bstep (se 1 (by rfl) ⟨5730425, by rfl⟩ : syracuseStep 7640567 = 11460851) B11460851
theorem B5093711 : Blo 2263435 5093711 := bstep (se 1 (by rfl) ⟨3820283, by rfl⟩ : syracuseStep 5093711 = 7640567) B7640567
theorem B3395807 : Blo 2263435 3395807 := bstep (se 1 (by rfl) ⟨2546855, by rfl⟩ : syracuseStep 3395807 = 5093711) B5093711
theorem B2263871 : Blo 2263435 2263871 := bstep (se 1 (by rfl) ⟨1697903, by rfl⟩ : syracuseStep 2263871 = 3395807) B3395807
theorem B3395813 : Blo 2263435 3395813 := bbase (se 4 (by rfl) ⟨318357, by rfl⟩ : syracuseStep 3395813 = 636715) (by norm_num)
theorem B2263875 : Blo 2263435 2263875 := bstep (se 1 (by rfl) ⟨1697906, by rfl⟩ : syracuseStep 2263875 = 3395813) B3395813
theorem B6119381 : Blo 2263435 6119381 := bbase (se 7 (by rfl) ⟨71711, by rfl⟩ : syracuseStep 6119381 = 143423) (by norm_num)
theorem B4079587 : Blo 2263435 4079587 := bstep (se 1 (by rfl) ⟨3059690, by rfl⟩ : syracuseStep 4079587 = 6119381) B6119381
theorem B5439449 : Blo 2263435 5439449 := bstep (se 2 (by rfl) ⟨2039793, by rfl⟩ : syracuseStep 5439449 = 4079587) B4079587
theorem B3626299 : Blo 2263435 3626299 := bstep (se 1 (by rfl) ⟨2719724, by rfl⟩ : syracuseStep 3626299 = 5439449) B5439449
theorem B4835065 : Blo 2263435 4835065 := bstep (se 2 (by rfl) ⟨1813149, by rfl⟩ : syracuseStep 4835065 = 3626299) B3626299
theorem B6446753 : Blo 2263435 6446753 := bstep (se 2 (by rfl) ⟨2417532, by rfl⟩ : syracuseStep 6446753 = 4835065) B4835065
theorem B4297835 : Blo 2263435 4297835 := bstep (se 1 (by rfl) ⟨3223376, by rfl⟩ : syracuseStep 4297835 = 6446753) B6446753
theorem B2865223 : Blo 2263435 2865223 := bstep (se 1 (by rfl) ⟨2148917, by rfl⟩ : syracuseStep 2865223 = 4297835) B4297835
theorem B3820297 : Blo 2263435 3820297 := bstep (se 2 (by rfl) ⟨1432611, by rfl⟩ : syracuseStep 3820297 = 2865223) B2865223
theorem B5093729 : Blo 2263435 5093729 := bstep (se 2 (by rfl) ⟨1910148, by rfl⟩ : syracuseStep 5093729 = 3820297) B3820297
theorem B3395819 : Blo 2263435 3395819 := bstep (se 1 (by rfl) ⟨2546864, by rfl⟩ : syracuseStep 3395819 = 5093729) B5093729
theorem B2263879 : Blo 2263435 2263879 := bstep (se 1 (by rfl) ⟨1697909, by rfl⟩ : syracuseStep 2263879 = 3395819) B3395819
theorem B2546869 : Blo 2263435 2546869 := bbase (se 5 (by rfl) ⟨119384, by rfl⟩ : syracuseStep 2546869 = 238769) (by norm_num)
theorem B3395825 : Blo 2263435 3395825 := bstep (se 2 (by rfl) ⟨1273434, by rfl⟩ : syracuseStep 3395825 = 2546869) B2546869
theorem B2263883 : Blo 2263435 2263883 := bstep (se 1 (by rfl) ⟨1697912, by rfl⟩ : syracuseStep 2263883 = 3395825) B3395825
theorem B2865233 : Blo 2263435 2865233 := bbase (se 2 (by rfl) ⟨1074462, by rfl⟩ : syracuseStep 2865233 = 2148925) (by norm_num)
theorem B7640621 : Blo 2263435 7640621 := bstep (se 3 (by rfl) ⟨1432616, by rfl⟩ : syracuseStep 7640621 = 2865233) B2865233
theorem B5093747 : Blo 2263435 5093747 := bstep (se 1 (by rfl) ⟨3820310, by rfl⟩ : syracuseStep 5093747 = 7640621) B7640621
theorem B3395831 : Blo 2263435 3395831 := bstep (se 1 (by rfl) ⟨2546873, by rfl⟩ : syracuseStep 3395831 = 5093747) B5093747
theorem B2263887 : Blo 2263435 2263887 := bstep (se 1 (by rfl) ⟨1697915, by rfl⟩ : syracuseStep 2263887 = 3395831) B3395831
theorem B3395837 : Blo 2263435 3395837 := bbase (se 3 (by rfl) ⟨636719, by rfl⟩ : syracuseStep 3395837 = 1273439) (by norm_num)
theorem B2263891 : Blo 2263435 2263891 := bstep (se 1 (by rfl) ⟨1697918, by rfl⟩ : syracuseStep 2263891 = 3395837) B3395837
theorem B5093765 : Blo 2263435 5093765 := bbase (se 4 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 5093765 = 955081) (by norm_num)
theorem B3395843 : Blo 2263435 3395843 := bstep (se 1 (by rfl) ⟨2546882, by rfl⟩ : syracuseStep 3395843 = 5093765) B5093765
theorem B2263895 : Blo 2263435 2263895 := bstep (se 1 (by rfl) ⟨1697921, by rfl⟩ : syracuseStep 2263895 = 3395843) B3395843
theorem B3223405 : Blo 2263435 3223405 := bbase (se 3 (by rfl) ⟨604388, by rfl⟩ : syracuseStep 3223405 = 1208777) (by norm_num)
theorem B4297873 : Blo 2263435 4297873 := bstep (se 2 (by rfl) ⟨1611702, by rfl⟩ : syracuseStep 4297873 = 3223405) B3223405
theorem B5730497 : Blo 2263435 5730497 := bstep (se 2 (by rfl) ⟨2148936, by rfl⟩ : syracuseStep 5730497 = 4297873) B4297873
theorem B3820331 : Blo 2263435 3820331 := bstep (se 1 (by rfl) ⟨2865248, by rfl⟩ : syracuseStep 3820331 = 5730497) B5730497
theorem B2546887 : Blo 2263435 2546887 := bstep (se 1 (by rfl) ⟨1910165, by rfl⟩ : syracuseStep 2546887 = 3820331) B3820331
theorem B3395849 : Blo 2263435 3395849 := bstep (se 2 (by rfl) ⟨1273443, by rfl⟩ : syracuseStep 3395849 = 2546887) B2546887
theorem B2263899 : Blo 2263435 2263899 := bstep (se 1 (by rfl) ⟨1697924, by rfl⟩ : syracuseStep 2263899 = 3395849) B3395849
theorem B11461013 : Blo 2263435 11461013 := bbase (se 6 (by rfl) ⟨268617, by rfl⟩ : syracuseStep 11461013 = 537235) (by norm_num)
theorem B7640675 : Blo 2263435 7640675 := bstep (se 1 (by rfl) ⟨5730506, by rfl⟩ : syracuseStep 7640675 = 11461013) B11461013
theorem B5093783 : Blo 2263435 5093783 := bstep (se 1 (by rfl) ⟨3820337, by rfl⟩ : syracuseStep 5093783 = 7640675) B7640675
theorem B3395855 : Blo 2263435 3395855 := bstep (se 1 (by rfl) ⟨2546891, by rfl⟩ : syracuseStep 3395855 = 5093783) B5093783
theorem B2263903 : Blo 2263435 2263903 := bstep (se 1 (by rfl) ⟨1697927, by rfl⟩ : syracuseStep 2263903 = 3395855) B3395855
theorem B3395861 : Blo 2263435 3395861 := bbase (se 6 (by rfl) ⟨79590, by rfl⟩ : syracuseStep 3395861 = 159181) (by norm_num)
theorem B2263907 : Blo 2263435 2263907 := bstep (se 1 (by rfl) ⟨1697930, by rfl⟩ : syracuseStep 2263907 = 3395861) B3395861
theorem B19604405 : Blo 2263435 19604405 := bbase (se 5 (by rfl) ⟨918956, by rfl⟩ : syracuseStep 19604405 = 1837913) (by norm_num)
theorem B13069603 : Blo 2263435 13069603 := bstep (se 1 (by rfl) ⟨9802202, by rfl⟩ : syracuseStep 13069603 = 19604405) B19604405
theorem B17426137 : Blo 2263435 17426137 := bstep (se 2 (by rfl) ⟨6534801, by rfl⟩ : syracuseStep 17426137 = 13069603) B13069603
theorem B23234849 : Blo 2263435 23234849 := bstep (se 2 (by rfl) ⟨8713068, by rfl⟩ : syracuseStep 23234849 = 17426137) B17426137
theorem B15489899 : Blo 2263435 15489899 := bstep (se 1 (by rfl) ⟨11617424, by rfl⟩ : syracuseStep 15489899 = 23234849) B23234849
theorem B10326599 : Blo 2263435 10326599 := bstep (se 1 (by rfl) ⟨7744949, by rfl⟩ : syracuseStep 10326599 = 15489899) B15489899
theorem B6884399 : Blo 2263435 6884399 := bstep (se 1 (by rfl) ⟨5163299, by rfl⟩ : syracuseStep 6884399 = 10326599) B10326599
theorem B18358397 : Blo 2263435 18358397 := bstep (se 3 (by rfl) ⟨3442199, by rfl⟩ : syracuseStep 18358397 = 6884399) B6884399
theorem B12238931 : Blo 2263435 12238931 := bstep (se 1 (by rfl) ⟨9179198, by rfl⟩ : syracuseStep 12238931 = 18358397) B18358397
theorem B8159287 : Blo 2263435 8159287 := bstep (se 1 (by rfl) ⟨6119465, by rfl⟩ : syracuseStep 8159287 = 12238931) B12238931
theorem B10879049 : Blo 2263435 10879049 := bstep (se 2 (by rfl) ⟨4079643, by rfl⟩ : syracuseStep 10879049 = 8159287) B8159287
theorem B29010797 : Blo 2263435 29010797 := bstep (se 3 (by rfl) ⟨5439524, by rfl⟩ : syracuseStep 29010797 = 10879049) B10879049
theorem B19340531 : Blo 2263435 19340531 := bstep (se 1 (by rfl) ⟨14505398, by rfl⟩ : syracuseStep 19340531 = 29010797) B29010797
theorem B12893687 : Blo 2263435 12893687 := bstep (se 1 (by rfl) ⟨9670265, by rfl⟩ : syracuseStep 12893687 = 19340531) B19340531
theorem B8595791 : Blo 2263435 8595791 := bstep (se 1 (by rfl) ⟨6446843, by rfl⟩ : syracuseStep 8595791 = 12893687) B12893687
theorem B5730527 : Blo 2263435 5730527 := bstep (se 1 (by rfl) ⟨4297895, by rfl⟩ : syracuseStep 5730527 = 8595791) B8595791
theorem B3820351 : Blo 2263435 3820351 := bstep (se 1 (by rfl) ⟨2865263, by rfl⟩ : syracuseStep 3820351 = 5730527) B5730527
theorem B5093801 : Blo 2263435 5093801 := bstep (se 2 (by rfl) ⟨1910175, by rfl⟩ : syracuseStep 5093801 = 3820351) B3820351
theorem B3395867 : Blo 2263435 3395867 := bstep (se 1 (by rfl) ⟨2546900, by rfl⟩ : syracuseStep 3395867 = 5093801) B5093801
theorem B2263911 : Blo 2263435 2263911 := bstep (se 1 (by rfl) ⟨1697933, by rfl⟩ : syracuseStep 2263911 = 3395867) B3395867
theorem B2546905 : Blo 2263435 2546905 := bbase (se 2 (by rfl) ⟨955089, by rfl⟩ : syracuseStep 2546905 = 1910179) (by norm_num)
theorem B3395873 : Blo 2263435 3395873 := bstep (se 2 (by rfl) ⟨1273452, by rfl⟩ : syracuseStep 3395873 = 2546905) B2546905
theorem B2263915 : Blo 2263435 2263915 := bstep (se 1 (by rfl) ⟨1697936, by rfl⟩ : syracuseStep 2263915 = 3395873) B3395873
theorem B3442213 : Blo 2263435 3442213 := bbase (se 4 (by rfl) ⟨322707, by rfl⟩ : syracuseStep 3442213 = 645415) (by norm_num)
theorem B4589617 : Blo 2263435 4589617 := bstep (se 2 (by rfl) ⟨1721106, by rfl⟩ : syracuseStep 4589617 = 3442213) B3442213
theorem B6119489 : Blo 2263435 6119489 := bstep (se 2 (by rfl) ⟨2294808, by rfl⟩ : syracuseStep 6119489 = 4589617) B4589617
theorem B4079659 : Blo 2263435 4079659 := bstep (se 1 (by rfl) ⟨3059744, by rfl⟩ : syracuseStep 4079659 = 6119489) B6119489
theorem B5439545 : Blo 2263435 5439545 := bstep (se 2 (by rfl) ⟨2039829, by rfl⟩ : syracuseStep 5439545 = 4079659) B4079659
theorem B3626363 : Blo 2263435 3626363 := bstep (se 1 (by rfl) ⟨2719772, by rfl⟩ : syracuseStep 3626363 = 5439545) B5439545
theorem B2417575 : Blo 2263435 2417575 := bstep (se 1 (by rfl) ⟨1813181, by rfl⟩ : syracuseStep 2417575 = 3626363) B3626363
theorem B3223433 : Blo 2263435 3223433 := bstep (se 2 (by rfl) ⟨1208787, by rfl⟩ : syracuseStep 3223433 = 2417575) B2417575
theorem B8595821 : Blo 2263435 8595821 := bstep (se 3 (by rfl) ⟨1611716, by rfl⟩ : syracuseStep 8595821 = 3223433) B3223433
theorem B5730547 : Blo 2263435 5730547 := bstep (se 1 (by rfl) ⟨4297910, by rfl⟩ : syracuseStep 5730547 = 8595821) B8595821
theorem B7640729 : Blo 2263435 7640729 := bstep (se 2 (by rfl) ⟨2865273, by rfl⟩ : syracuseStep 7640729 = 5730547) B5730547
theorem B5093819 : Blo 2263435 5093819 := bstep (se 1 (by rfl) ⟨3820364, by rfl⟩ : syracuseStep 5093819 = 7640729) B7640729
theorem B3395879 : Blo 2263435 3395879 := bstep (se 1 (by rfl) ⟨2546909, by rfl⟩ : syracuseStep 3395879 = 5093819) B5093819
theorem B2263919 : Blo 2263435 2263919 := bstep (se 1 (by rfl) ⟨1697939, by rfl⟩ : syracuseStep 2263919 = 3395879) B3395879
theorem B3395885 : Blo 2263435 3395885 := bbase (se 3 (by rfl) ⟨636728, by rfl⟩ : syracuseStep 3395885 = 1273457) (by norm_num)
theorem B2263923 : Blo 2263435 2263923 := bstep (se 1 (by rfl) ⟨1697942, by rfl⟩ : syracuseStep 2263923 = 3395885) B3395885
theorem B5093837 : Blo 2263435 5093837 := bbase (se 3 (by rfl) ⟨955094, by rfl⟩ : syracuseStep 5093837 = 1910189) (by norm_num)
theorem B3395891 : Blo 2263435 3395891 := bstep (se 1 (by rfl) ⟨2546918, by rfl⟩ : syracuseStep 3395891 = 5093837) B5093837
theorem B2263927 : Blo 2263435 2263927 := bstep (se 1 (by rfl) ⟨1697945, by rfl⟩ : syracuseStep 2263927 = 3395891) B3395891
theorem B2865289 : Blo 2263435 2865289 := bbase (se 2 (by rfl) ⟨1074483, by rfl⟩ : syracuseStep 2865289 = 2148967) (by norm_num)
theorem B3820385 : Blo 2263435 3820385 := bstep (se 2 (by rfl) ⟨1432644, by rfl⟩ : syracuseStep 3820385 = 2865289) B2865289
theorem B2546923 : Blo 2263435 2546923 := bstep (se 1 (by rfl) ⟨1910192, by rfl⟩ : syracuseStep 2546923 = 3820385) B3820385
theorem B3395897 : Blo 2263435 3395897 := bstep (se 2 (by rfl) ⟨1273461, by rfl⟩ : syracuseStep 3395897 = 2546923) B2546923
theorem B2263931 : Blo 2263435 2263931 := bstep (se 1 (by rfl) ⟨1697948, by rfl⟩ : syracuseStep 2263931 = 3395897) B3395897
theorem B5808773 : Blo 2263435 5808773 := bbase (se 4 (by rfl) ⟨544572, by rfl⟩ : syracuseStep 5808773 = 1089145) (by norm_num)
theorem B15490061 : Blo 2263435 15490061 := bstep (se 3 (by rfl) ⟨2904386, by rfl⟩ : syracuseStep 15490061 = 5808773) B5808773
theorem B10326707 : Blo 2263435 10326707 := bstep (se 1 (by rfl) ⟨7745030, by rfl⟩ : syracuseStep 10326707 = 15490061) B15490061
theorem B6884471 : Blo 2263435 6884471 := bstep (se 1 (by rfl) ⟨5163353, by rfl⟩ : syracuseStep 6884471 = 10326707) B10326707
theorem B18358589 : Blo 2263435 18358589 := bstep (se 3 (by rfl) ⟨3442235, by rfl⟩ : syracuseStep 18358589 = 6884471) B6884471
theorem B48956237 : Blo 2263435 48956237 := bstep (se 3 (by rfl) ⟨9179294, by rfl⟩ : syracuseStep 48956237 = 18358589) B18358589
theorem B32637491 : Blo 2263435 32637491 := bstep (se 1 (by rfl) ⟨24478118, by rfl⟩ : syracuseStep 32637491 = 48956237) B48956237
theorem B21758327 : Blo 2263435 21758327 := bstep (se 1 (by rfl) ⟨16318745, by rfl⟩ : syracuseStep 21758327 = 32637491) B32637491
theorem B14505551 : Blo 2263435 14505551 := bstep (se 1 (by rfl) ⟨10879163, by rfl⟩ : syracuseStep 14505551 = 21758327) B21758327
theorem B9670367 : Blo 2263435 9670367 := bstep (se 1 (by rfl) ⟨7252775, by rfl⟩ : syracuseStep 9670367 = 14505551) B14505551
theorem B25787645 : Blo 2263435 25787645 := bstep (se 3 (by rfl) ⟨4835183, by rfl⟩ : syracuseStep 25787645 = 9670367) B9670367
theorem B17191763 : Blo 2263435 17191763 := bstep (se 1 (by rfl) ⟨12893822, by rfl⟩ : syracuseStep 17191763 = 25787645) B25787645
theorem B11461175 : Blo 2263435 11461175 := bstep (se 1 (by rfl) ⟨8595881, by rfl⟩ : syracuseStep 11461175 = 17191763) B17191763
theorem B7640783 : Blo 2263435 7640783 := bstep (se 1 (by rfl) ⟨5730587, by rfl⟩ : syracuseStep 7640783 = 11461175) B11461175
theorem B5093855 : Blo 2263435 5093855 := bstep (se 1 (by rfl) ⟨3820391, by rfl⟩ : syracuseStep 5093855 = 7640783) B7640783
theorem B3395903 : Blo 2263435 3395903 := bstep (se 1 (by rfl) ⟨2546927, by rfl⟩ : syracuseStep 3395903 = 5093855) B5093855
theorem B2263935 : Blo 2263435 2263935 := bstep (se 1 (by rfl) ⟨1697951, by rfl⟩ : syracuseStep 2263935 = 3395903) B3395903
theorem B3395909 : Blo 2263435 3395909 := bbase (se 4 (by rfl) ⟨318366, by rfl⟩ : syracuseStep 3395909 = 636733) (by norm_num)
theorem B2263939 : Blo 2263435 2263939 := bstep (se 1 (by rfl) ⟨1697954, by rfl⟩ : syracuseStep 2263939 = 3395909) B3395909
theorem B3820405 : Blo 2263435 3820405 := bbase (se 5 (by rfl) ⟨179081, by rfl⟩ : syracuseStep 3820405 = 358163) (by norm_num)
theorem B5093873 : Blo 2263435 5093873 := bstep (se 2 (by rfl) ⟨1910202, by rfl⟩ : syracuseStep 5093873 = 3820405) B3820405
theorem B3395915 : Blo 2263435 3395915 := bstep (se 1 (by rfl) ⟨2546936, by rfl⟩ : syracuseStep 3395915 = 5093873) B5093873
theorem B2263943 : Blo 2263435 2263943 := bstep (se 1 (by rfl) ⟨1697957, by rfl⟩ : syracuseStep 2263943 = 3395915) B3395915
theorem B2546941 : Blo 2263435 2546941 := bbase (se 3 (by rfl) ⟨477551, by rfl⟩ : syracuseStep 2546941 = 955103) (by norm_num)
theorem B3395921 : Blo 2263435 3395921 := bstep (se 2 (by rfl) ⟨1273470, by rfl⟩ : syracuseStep 3395921 = 2546941) B2546941
theorem B2263947 : Blo 2263435 2263947 := bstep (se 1 (by rfl) ⟨1697960, by rfl⟩ : syracuseStep 2263947 = 3395921) B3395921
theorem B7640837 : Blo 2263435 7640837 := bbase (se 4 (by rfl) ⟨716328, by rfl⟩ : syracuseStep 7640837 = 1432657) (by norm_num)
theorem B5093891 : Blo 2263435 5093891 := bstep (se 1 (by rfl) ⟨3820418, by rfl⟩ : syracuseStep 5093891 = 7640837) B7640837
theorem B3395927 : Blo 2263435 3395927 := bstep (se 1 (by rfl) ⟨2546945, by rfl⟩ : syracuseStep 3395927 = 5093891) B5093891
theorem B2263951 : Blo 2263435 2263951 := bstep (se 1 (by rfl) ⟨1697963, by rfl⟩ : syracuseStep 2263951 = 3395927) B3395927
theorem B3395933 : Blo 2263435 3395933 := bbase (se 3 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 3395933 = 1273475) (by norm_num)
theorem B2263955 : Blo 2263435 2263955 := bstep (se 1 (by rfl) ⟨1697966, by rfl⟩ : syracuseStep 2263955 = 3395933) B3395933
theorem B5093909 : Blo 2263435 5093909 := bbase (se 6 (by rfl) ⟨119388, by rfl⟩ : syracuseStep 5093909 = 238777) (by norm_num)
theorem B3395939 : Blo 2263435 3395939 := bstep (se 1 (by rfl) ⟨2546954, by rfl⟩ : syracuseStep 3395939 = 5093909) B5093909
theorem B2263959 : Blo 2263435 2263959 := bstep (se 1 (by rfl) ⟨1697969, by rfl⟩ : syracuseStep 2263959 = 3395939) B3395939
theorem B8595989 : Blo 2263435 8595989 := bbase (se 6 (by rfl) ⟨201468, by rfl⟩ : syracuseStep 8595989 = 402937) (by norm_num)
theorem B5730659 : Blo 2263435 5730659 := bstep (se 1 (by rfl) ⟨4297994, by rfl⟩ : syracuseStep 5730659 = 8595989) B8595989
theorem B3820439 : Blo 2263435 3820439 := bstep (se 1 (by rfl) ⟨2865329, by rfl⟩ : syracuseStep 3820439 = 5730659) B5730659
theorem B2546959 : Blo 2263435 2546959 := bstep (se 1 (by rfl) ⟨1910219, by rfl⟩ : syracuseStep 2546959 = 3820439) B3820439
theorem B3395945 : Blo 2263435 3395945 := bstep (se 2 (by rfl) ⟨1273479, by rfl⟩ : syracuseStep 3395945 = 2546959) B2546959
theorem B2263963 : Blo 2263435 2263963 := bstep (se 1 (by rfl) ⟨1697972, by rfl⟩ : syracuseStep 2263963 = 3395945) B3395945
theorem B12894005 : Blo 2263435 12894005 := bbase (se 5 (by rfl) ⟨604406, by rfl⟩ : syracuseStep 12894005 = 1208813) (by norm_num)
theorem B8596003 : Blo 2263435 8596003 := bstep (se 1 (by rfl) ⟨6447002, by rfl⟩ : syracuseStep 8596003 = 12894005) B12894005
theorem B11461337 : Blo 2263435 11461337 := bstep (se 2 (by rfl) ⟨4298001, by rfl⟩ : syracuseStep 11461337 = 8596003) B8596003
theorem B7640891 : Blo 2263435 7640891 := bstep (se 1 (by rfl) ⟨5730668, by rfl⟩ : syracuseStep 7640891 = 11461337) B11461337
theorem B5093927 : Blo 2263435 5093927 := bstep (se 1 (by rfl) ⟨3820445, by rfl⟩ : syracuseStep 5093927 = 7640891) B7640891
theorem B3395951 : Blo 2263435 3395951 := bstep (se 1 (by rfl) ⟨2546963, by rfl⟩ : syracuseStep 3395951 = 5093927) B5093927
theorem B2263967 : Blo 2263435 2263967 := bstep (se 1 (by rfl) ⟨1697975, by rfl⟩ : syracuseStep 2263967 = 3395951) B3395951
theorem B3395957 : Blo 2263435 3395957 := bbase (se 5 (by rfl) ⟨159185, by rfl⟩ : syracuseStep 3395957 = 318371) (by norm_num)
theorem B2263971 : Blo 2263435 2263971 := bstep (se 1 (by rfl) ⟨1697978, by rfl⟩ : syracuseStep 2263971 = 3395957) B3395957
theorem B3626453 : Blo 2263435 3626453 := bbase (se 7 (by rfl) ⟨42497, by rfl⟩ : syracuseStep 3626453 = 84995) (by norm_num)
theorem B2417635 : Blo 2263435 2417635 := bstep (se 1 (by rfl) ⟨1813226, by rfl⟩ : syracuseStep 2417635 = 3626453) B3626453
theorem B3223513 : Blo 2263435 3223513 := bstep (se 2 (by rfl) ⟨1208817, by rfl⟩ : syracuseStep 3223513 = 2417635) B2417635
theorem B4298017 : Blo 2263435 4298017 := bstep (se 2 (by rfl) ⟨1611756, by rfl⟩ : syracuseStep 4298017 = 3223513) B3223513
theorem B5730689 : Blo 2263435 5730689 := bstep (se 2 (by rfl) ⟨2149008, by rfl⟩ : syracuseStep 5730689 = 4298017) B4298017
theorem B3820459 : Blo 2263435 3820459 := bstep (se 1 (by rfl) ⟨2865344, by rfl⟩ : syracuseStep 3820459 = 5730689) B5730689
theorem B5093945 : Blo 2263435 5093945 := bstep (se 2 (by rfl) ⟨1910229, by rfl⟩ : syracuseStep 5093945 = 3820459) B3820459
theorem B3395963 : Blo 2263435 3395963 := bstep (se 1 (by rfl) ⟨2546972, by rfl⟩ : syracuseStep 3395963 = 5093945) B5093945
theorem B2263975 : Blo 2263435 2263975 := bstep (se 1 (by rfl) ⟨1697981, by rfl⟩ : syracuseStep 2263975 = 3395963) B3395963
theorem B2546977 : Blo 2263435 2546977 := bbase (se 2 (by rfl) ⟨955116, by rfl⟩ : syracuseStep 2546977 = 1910233) (by norm_num)
theorem B3395969 : Blo 2263435 3395969 := bstep (se 2 (by rfl) ⟨1273488, by rfl⟩ : syracuseStep 3395969 = 2546977) B2546977
theorem B2263979 : Blo 2263435 2263979 := bstep (se 1 (by rfl) ⟨1697984, by rfl⟩ : syracuseStep 2263979 = 3395969) B3395969
theorem B5730709 : Blo 2263435 5730709 := bbase (se 6 (by rfl) ⟨134313, by rfl⟩ : syracuseStep 5730709 = 268627) (by norm_num)
theorem B7640945 : Blo 2263435 7640945 := bstep (se 2 (by rfl) ⟨2865354, by rfl⟩ : syracuseStep 7640945 = 5730709) B5730709
theorem B5093963 : Blo 2263435 5093963 := bstep (se 1 (by rfl) ⟨3820472, by rfl⟩ : syracuseStep 5093963 = 7640945) B7640945
theorem B3395975 : Blo 2263435 3395975 := bstep (se 1 (by rfl) ⟨2546981, by rfl⟩ : syracuseStep 3395975 = 5093963) B5093963
theorem B2263983 : Blo 2263435 2263983 := bstep (se 1 (by rfl) ⟨1697987, by rfl⟩ : syracuseStep 2263983 = 3395975) B3395975
theorem B3395981 : Blo 2263435 3395981 := bbase (se 3 (by rfl) ⟨636746, by rfl⟩ : syracuseStep 3395981 = 1273493) (by norm_num)
theorem B2263987 : Blo 2263435 2263987 := bstep (se 1 (by rfl) ⟨1697990, by rfl⟩ : syracuseStep 2263987 = 3395981) B3395981
theorem B5093981 : Blo 2263435 5093981 := bbase (se 3 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 5093981 = 1910243) (by norm_num)
theorem B3395987 : Blo 2263435 3395987 := bstep (se 1 (by rfl) ⟨2546990, by rfl⟩ : syracuseStep 3395987 = 5093981) B5093981
theorem B2263991 : Blo 2263435 2263991 := bstep (se 1 (by rfl) ⟨1697993, by rfl⟩ : syracuseStep 2263991 = 3395987) B3395987
theorem B3820493 : Blo 2263435 3820493 := bbase (se 3 (by rfl) ⟨716342, by rfl⟩ : syracuseStep 3820493 = 1432685) (by norm_num)
theorem B2546995 : Blo 2263435 2546995 := bstep (se 1 (by rfl) ⟨1910246, by rfl⟩ : syracuseStep 2546995 = 3820493) B3820493
theorem B3395993 : Blo 2263435 3395993 := bstep (se 2 (by rfl) ⟨1273497, by rfl⟩ : syracuseStep 3395993 = 2546995) B2546995
theorem B2263995 : Blo 2263435 2263995 := bstep (se 1 (by rfl) ⟨1697996, by rfl⟩ : syracuseStep 2263995 = 3395993) B3395993
theorem B16767541 : Blo 2263435 16767541 := bbase (se 5 (by rfl) ⟨785978, by rfl⟩ : syracuseStep 16767541 = 1571957) (by norm_num)
theorem B89426885 : Blo 2263435 89426885 := bstep (se 4 (by rfl) ⟨8383770, by rfl⟩ : syracuseStep 89426885 = 16767541) B16767541
theorem B953886773 : Blo 2263435 953886773 := bstep (se 5 (by rfl) ⟨44713442, by rfl⟩ : syracuseStep 953886773 = 89426885) B89426885
theorem B635924515 : Blo 2263435 635924515 := bstep (se 1 (by rfl) ⟨476943386, by rfl⟩ : syracuseStep 635924515 = 953886773) B953886773
theorem B847899353 : Blo 2263435 847899353 := bstep (se 2 (by rfl) ⟨317962257, by rfl⟩ : syracuseStep 847899353 = 635924515) B635924515
theorem B2261064941 : Blo 2263435 2261064941 := bstep (se 3 (by rfl) ⟨423949676, by rfl⟩ : syracuseStep 2261064941 = 847899353) B847899353
theorem B1507376627 : Blo 2263435 1507376627 := bstep (se 1 (by rfl) ⟨1130532470, by rfl⟩ : syracuseStep 1507376627 = 2261064941) B2261064941
theorem B1004917751 : Blo 2263435 1004917751 := bstep (se 1 (by rfl) ⟨753688313, by rfl⟩ : syracuseStep 1004917751 = 1507376627) B1507376627
theorem B669945167 : Blo 2263435 669945167 := bstep (se 1 (by rfl) ⟨502458875, by rfl⟩ : syracuseStep 669945167 = 1004917751) B1004917751
theorem B446630111 : Blo 2263435 446630111 := bstep (se 1 (by rfl) ⟨334972583, by rfl⟩ : syracuseStep 446630111 = 669945167) B669945167
theorem B297753407 : Blo 2263435 297753407 := bstep (se 1 (by rfl) ⟨223315055, by rfl⟩ : syracuseStep 297753407 = 446630111) B446630111
theorem B198502271 : Blo 2263435 198502271 := bstep (se 1 (by rfl) ⟨148876703, by rfl⟩ : syracuseStep 198502271 = 297753407) B297753407
theorem B132334847 : Blo 2263435 132334847 := bstep (se 1 (by rfl) ⟨99251135, by rfl⟩ : syracuseStep 132334847 = 198502271) B198502271
theorem B88223231 : Blo 2263435 88223231 := bstep (se 1 (by rfl) ⟨66167423, by rfl⟩ : syracuseStep 88223231 = 132334847) B132334847
theorem B58815487 : Blo 2263435 58815487 := bstep (se 1 (by rfl) ⟨44111615, by rfl⟩ : syracuseStep 58815487 = 88223231) B88223231
theorem B78420649 : Blo 2263435 78420649 := bstep (se 2 (by rfl) ⟨29407743, by rfl⟩ : syracuseStep 78420649 = 58815487) B58815487
theorem B104560865 : Blo 2263435 104560865 := bstep (se 2 (by rfl) ⟨39210324, by rfl⟩ : syracuseStep 104560865 = 78420649) B78420649
theorem B69707243 : Blo 2263435 69707243 := bstep (se 1 (by rfl) ⟨52280432, by rfl⟩ : syracuseStep 69707243 = 104560865) B104560865
theorem B46471495 : Blo 2263435 46471495 := bstep (se 1 (by rfl) ⟨34853621, by rfl⟩ : syracuseStep 46471495 = 69707243) B69707243
theorem B61961993 : Blo 2263435 61961993 := bstep (se 2 (by rfl) ⟨23235747, by rfl⟩ : syracuseStep 61961993 = 46471495) B46471495
theorem B41307995 : Blo 2263435 41307995 := bstep (se 1 (by rfl) ⟨30980996, by rfl⟩ : syracuseStep 41307995 = 61961993) B61961993
theorem B27538663 : Blo 2263435 27538663 := bstep (se 1 (by rfl) ⟨20653997, by rfl⟩ : syracuseStep 27538663 = 41307995) B41307995
theorem B36718217 : Blo 2263435 36718217 := bstep (se 2 (by rfl) ⟨13769331, by rfl⟩ : syracuseStep 36718217 = 27538663) B27538663
theorem B24478811 : Blo 2263435 24478811 := bstep (se 1 (by rfl) ⟨18359108, by rfl⟩ : syracuseStep 24478811 = 36718217) B36718217
theorem B16319207 : Blo 2263435 16319207 := bstep (se 1 (by rfl) ⟨12239405, by rfl⟩ : syracuseStep 16319207 = 24478811) B24478811
theorem B10879471 : Blo 2263435 10879471 := bstep (se 1 (by rfl) ⟨8159603, by rfl⟩ : syracuseStep 10879471 = 16319207) B16319207
theorem B14505961 : Blo 2263435 14505961 := bstep (se 2 (by rfl) ⟨5439735, by rfl⟩ : syracuseStep 14505961 = 10879471) B10879471
theorem B19341281 : Blo 2263435 19341281 := bstep (se 2 (by rfl) ⟨7252980, by rfl⟩ : syracuseStep 19341281 = 14505961) B14505961
theorem B12894187 : Blo 2263435 12894187 := bstep (se 1 (by rfl) ⟨9670640, by rfl⟩ : syracuseStep 12894187 = 19341281) B19341281
theorem B17192249 : Blo 2263435 17192249 := bstep (se 2 (by rfl) ⟨6447093, by rfl⟩ : syracuseStep 17192249 = 12894187) B12894187
theorem B11461499 : Blo 2263435 11461499 := bstep (se 1 (by rfl) ⟨8596124, by rfl⟩ : syracuseStep 11461499 = 17192249) B17192249
theorem B7640999 : Blo 2263435 7640999 := bstep (se 1 (by rfl) ⟨5730749, by rfl⟩ : syracuseStep 7640999 = 11461499) B11461499
theorem B5093999 : Blo 2263435 5093999 := bstep (se 1 (by rfl) ⟨3820499, by rfl⟩ : syracuseStep 5093999 = 7640999) B7640999
theorem B3395999 : Blo 2263435 3395999 := bstep (se 1 (by rfl) ⟨2546999, by rfl⟩ : syracuseStep 3395999 = 5093999) B5093999
theorem B2263999 : Blo 2263435 2263999 := bstep (se 1 (by rfl) ⟨1697999, by rfl⟩ : syracuseStep 2263999 = 3395999) B3395999
theorem B3396005 : Blo 2263435 3396005 := bbase (se 4 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 3396005 = 636751) (by norm_num)
theorem B2264003 : Blo 2263435 2264003 := bstep (se 1 (by rfl) ⟨1698002, by rfl⟩ : syracuseStep 2264003 = 3396005) B3396005
theorem B2865385 : Blo 2263435 2865385 := bbase (se 2 (by rfl) ⟨1074519, by rfl⟩ : syracuseStep 2865385 = 2149039) (by norm_num)
theorem B3820513 : Blo 2263435 3820513 := bstep (se 2 (by rfl) ⟨1432692, by rfl⟩ : syracuseStep 3820513 = 2865385) B2865385
theorem B5094017 : Blo 2263435 5094017 := bstep (se 2 (by rfl) ⟨1910256, by rfl⟩ : syracuseStep 5094017 = 3820513) B3820513
theorem B3396011 : Blo 2263435 3396011 := bstep (se 1 (by rfl) ⟨2547008, by rfl⟩ : syracuseStep 3396011 = 5094017) B5094017
theorem B2264007 : Blo 2263435 2264007 := bstep (se 1 (by rfl) ⟨1698005, by rfl⟩ : syracuseStep 2264007 = 3396011) B3396011
theorem B2547013 : Blo 2263435 2547013 := bbase (se 4 (by rfl) ⟨238782, by rfl⟩ : syracuseStep 2547013 = 477565) (by norm_num)
theorem B3396017 : Blo 2263435 3396017 := bstep (se 2 (by rfl) ⟨1273506, by rfl⟩ : syracuseStep 3396017 = 2547013) B2547013
theorem B2264011 : Blo 2263435 2264011 := bstep (se 1 (by rfl) ⟨1698008, by rfl⟩ : syracuseStep 2264011 = 3396017) B3396017
theorem B4298093 : Blo 2263435 4298093 := bbase (se 3 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 4298093 = 1611785) (by norm_num)
theorem B2865395 : Blo 2263435 2865395 := bstep (se 1 (by rfl) ⟨2149046, by rfl⟩ : syracuseStep 2865395 = 4298093) B4298093
theorem B7641053 : Blo 2263435 7641053 := bstep (se 3 (by rfl) ⟨1432697, by rfl⟩ : syracuseStep 7641053 = 2865395) B2865395
theorem B5094035 : Blo 2263435 5094035 := bstep (se 1 (by rfl) ⟨3820526, by rfl⟩ : syracuseStep 5094035 = 7641053) B7641053
theorem B3396023 : Blo 2263435 3396023 := bstep (se 1 (by rfl) ⟨2547017, by rfl⟩ : syracuseStep 3396023 = 5094035) B5094035
theorem B2264015 : Blo 2263435 2264015 := bstep (se 1 (by rfl) ⟨1698011, by rfl⟩ : syracuseStep 2264015 = 3396023) B3396023
theorem B3396029 : Blo 2263435 3396029 := bbase (se 3 (by rfl) ⟨636755, by rfl⟩ : syracuseStep 3396029 = 1273511) (by norm_num)
theorem B2264019 : Blo 2263435 2264019 := bstep (se 1 (by rfl) ⟨1698014, by rfl⟩ : syracuseStep 2264019 = 3396029) B3396029
theorem B5094053 : Blo 2263435 5094053 := bbase (se 4 (by rfl) ⟨477567, by rfl⟩ : syracuseStep 5094053 = 955135) (by norm_num)
theorem B3396035 : Blo 2263435 3396035 := bstep (se 1 (by rfl) ⟨2547026, by rfl⟩ : syracuseStep 3396035 = 5094053) B5094053
theorem B2264023 : Blo 2263435 2264023 := bstep (se 1 (by rfl) ⟨1698017, by rfl⟩ : syracuseStep 2264023 = 3396035) B3396035
theorem B5730821 : Blo 2263435 5730821 := bbase (se 4 (by rfl) ⟨537264, by rfl⟩ : syracuseStep 5730821 = 1074529) (by norm_num)
theorem B3820547 : Blo 2263435 3820547 := bstep (se 1 (by rfl) ⟨2865410, by rfl⟩ : syracuseStep 3820547 = 5730821) B5730821
theorem B2547031 : Blo 2263435 2547031 := bstep (se 1 (by rfl) ⟨1910273, by rfl⟩ : syracuseStep 2547031 = 3820547) B3820547
theorem B3396041 : Blo 2263435 3396041 := bstep (se 2 (by rfl) ⟨1273515, by rfl⟩ : syracuseStep 3396041 = 2547031) B2547031
theorem B2264027 : Blo 2263435 2264027 := bstep (se 1 (by rfl) ⟨1698020, by rfl⟩ : syracuseStep 2264027 = 3396041) B3396041
theorem B4835389 : Blo 2263435 4835389 := bbase (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) (by norm_num)
theorem B6447185 : Blo 2263435 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B4298123 : Blo 2263435 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B11461661 : Blo 2263435 11461661 := bstep (se 3 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 11461661 = 4298123) B4298123
theorem B7641107 : Blo 2263435 7641107 := bstep (se 1 (by rfl) ⟨5730830, by rfl⟩ : syracuseStep 7641107 = 11461661) B11461661
theorem B5094071 : Blo 2263435 5094071 := bstep (se 1 (by rfl) ⟨3820553, by rfl⟩ : syracuseStep 5094071 = 7641107) B7641107
theorem B3396047 : Blo 2263435 3396047 := bstep (se 1 (by rfl) ⟨2547035, by rfl⟩ : syracuseStep 3396047 = 5094071) B5094071
theorem B2264031 : Blo 2263435 2264031 := bstep (se 1 (by rfl) ⟨1698023, by rfl⟩ : syracuseStep 2264031 = 3396047) B3396047
theorem B3396053 : Blo 2263435 3396053 := bbase (se 7 (by rfl) ⟨39797, by rfl⟩ : syracuseStep 3396053 = 79595) (by norm_num)
theorem B2264035 : Blo 2263435 2264035 := bstep (se 1 (by rfl) ⟨1698026, by rfl⟩ : syracuseStep 2264035 = 3396053) B3396053
theorem B8596277 : Blo 2263435 8596277 := bbase (se 5 (by rfl) ⟨402950, by rfl⟩ : syracuseStep 8596277 = 805901) (by norm_num)
theorem B5730851 : Blo 2263435 5730851 := bstep (se 1 (by rfl) ⟨4298138, by rfl⟩ : syracuseStep 5730851 = 8596277) B8596277
theorem B3820567 : Blo 2263435 3820567 := bstep (se 1 (by rfl) ⟨2865425, by rfl⟩ : syracuseStep 3820567 = 5730851) B5730851
theorem B5094089 : Blo 2263435 5094089 := bstep (se 2 (by rfl) ⟨1910283, by rfl⟩ : syracuseStep 5094089 = 3820567) B3820567
theorem B3396059 : Blo 2263435 3396059 := bstep (se 1 (by rfl) ⟨2547044, by rfl⟩ : syracuseStep 3396059 = 5094089) B5094089
theorem B2264039 : Blo 2263435 2264039 := bstep (se 1 (by rfl) ⟨1698029, by rfl⟩ : syracuseStep 2264039 = 3396059) B3396059
theorem B2547049 : Blo 2263435 2547049 := bbase (se 2 (by rfl) ⟨955143, by rfl⟩ : syracuseStep 2547049 = 1910287) (by norm_num)
theorem B3396065 : Blo 2263435 3396065 := bstep (se 2 (by rfl) ⟨1273524, by rfl⟩ : syracuseStep 3396065 = 2547049) B2547049
theorem B2264043 : Blo 2263435 2264043 := bstep (se 1 (by rfl) ⟨1698032, by rfl⟩ : syracuseStep 2264043 = 3396065) B3396065
theorem B2581805 : Blo 2263435 2581805 := bbase (se 3 (by rfl) ⟨484088, by rfl⟩ : syracuseStep 2581805 = 968177) (by norm_num)
theorem B6884813 : Blo 2263435 6884813 := bstep (se 3 (by rfl) ⟨1290902, by rfl⟩ : syracuseStep 6884813 = 2581805) B2581805
theorem B4589875 : Blo 2263435 4589875 := bstep (se 1 (by rfl) ⟨3442406, by rfl⟩ : syracuseStep 4589875 = 6884813) B6884813
theorem B24479333 : Blo 2263435 24479333 := bstep (se 4 (by rfl) ⟨2294937, by rfl⟩ : syracuseStep 24479333 = 4589875) B4589875
theorem B16319555 : Blo 2263435 16319555 := bstep (se 1 (by rfl) ⟨12239666, by rfl⟩ : syracuseStep 16319555 = 24479333) B24479333
theorem B10879703 : Blo 2263435 10879703 := bstep (se 1 (by rfl) ⟨8159777, by rfl⟩ : syracuseStep 10879703 = 16319555) B16319555
theorem B7253135 : Blo 2263435 7253135 := bstep (se 1 (by rfl) ⟨5439851, by rfl⟩ : syracuseStep 7253135 = 10879703) B10879703
theorem B4835423 : Blo 2263435 4835423 := bstep (se 1 (by rfl) ⟨3626567, by rfl⟩ : syracuseStep 4835423 = 7253135) B7253135
theorem B12894461 : Blo 2263435 12894461 := bstep (se 3 (by rfl) ⟨2417711, by rfl⟩ : syracuseStep 12894461 = 4835423) B4835423
theorem B8596307 : Blo 2263435 8596307 := bstep (se 1 (by rfl) ⟨6447230, by rfl⟩ : syracuseStep 8596307 = 12894461) B12894461
theorem B5730871 : Blo 2263435 5730871 := bstep (se 1 (by rfl) ⟨4298153, by rfl⟩ : syracuseStep 5730871 = 8596307) B8596307
theorem B7641161 : Blo 2263435 7641161 := bstep (se 2 (by rfl) ⟨2865435, by rfl⟩ : syracuseStep 7641161 = 5730871) B5730871
theorem B5094107 : Blo 2263435 5094107 := bstep (se 1 (by rfl) ⟨3820580, by rfl⟩ : syracuseStep 5094107 = 7641161) B7641161
theorem B3396071 : Blo 2263435 3396071 := bstep (se 1 (by rfl) ⟨2547053, by rfl⟩ : syracuseStep 3396071 = 5094107) B5094107
theorem B2264047 : Blo 2263435 2264047 := bstep (se 1 (by rfl) ⟨1698035, by rfl⟩ : syracuseStep 2264047 = 3396071) B3396071
theorem B3396077 : Blo 2263435 3396077 := bbase (se 3 (by rfl) ⟨636764, by rfl⟩ : syracuseStep 3396077 = 1273529) (by norm_num)
theorem B2264051 : Blo 2263435 2264051 := bstep (se 1 (by rfl) ⟨1698038, by rfl⟩ : syracuseStep 2264051 = 3396077) B3396077
theorem B5094125 : Blo 2263435 5094125 := bbase (se 3 (by rfl) ⟨955148, by rfl⟩ : syracuseStep 5094125 = 1910297) (by norm_num)
theorem B3396083 : Blo 2263435 3396083 := bstep (se 1 (by rfl) ⟨2547062, by rfl⟩ : syracuseStep 3396083 = 5094125) B5094125
theorem B2264055 : Blo 2263435 2264055 := bstep (se 1 (by rfl) ⟨1698041, by rfl⟩ : syracuseStep 2264055 = 3396083) B3396083
theorem B2417725 : Blo 2263435 2417725 := bbase (se 3 (by rfl) ⟨453323, by rfl⟩ : syracuseStep 2417725 = 906647) (by norm_num)
theorem B3223633 : Blo 2263435 3223633 := bstep (se 2 (by rfl) ⟨1208862, by rfl⟩ : syracuseStep 3223633 = 2417725) B2417725
theorem B4298177 : Blo 2263435 4298177 := bstep (se 2 (by rfl) ⟨1611816, by rfl⟩ : syracuseStep 4298177 = 3223633) B3223633
theorem B2865451 : Blo 2263435 2865451 := bstep (se 1 (by rfl) ⟨2149088, by rfl⟩ : syracuseStep 2865451 = 4298177) B4298177
theorem B3820601 : Blo 2263435 3820601 := bstep (se 2 (by rfl) ⟨1432725, by rfl⟩ : syracuseStep 3820601 = 2865451) B2865451
theorem B2547067 : Blo 2263435 2547067 := bstep (se 1 (by rfl) ⟨1910300, by rfl⟩ : syracuseStep 2547067 = 3820601) B3820601
theorem B3396089 : Blo 2263435 3396089 := bstep (se 2 (by rfl) ⟨1273533, by rfl⟩ : syracuseStep 3396089 = 2547067) B2547067
theorem B2264059 : Blo 2263435 2264059 := bstep (se 1 (by rfl) ⟨1698044, by rfl⟩ : syracuseStep 2264059 = 3396089) B3396089
theorem B9179813 : Blo 2263435 9179813 := bbase (se 4 (by rfl) ⟨860607, by rfl⟩ : syracuseStep 9179813 = 1721215) (by norm_num)
theorem B24479501 : Blo 2263435 24479501 := bstep (se 3 (by rfl) ⟨4589906, by rfl⟩ : syracuseStep 24479501 = 9179813) B9179813
theorem B65278669 : Blo 2263435 65278669 := bstep (se 3 (by rfl) ⟨12239750, by rfl⟩ : syracuseStep 65278669 = 24479501) B24479501
theorem B87038225 : Blo 2263435 87038225 := bstep (se 2 (by rfl) ⟨32639334, by rfl⟩ : syracuseStep 87038225 = 65278669) B65278669
theorem B58025483 : Blo 2263435 58025483 := bstep (se 1 (by rfl) ⟨43519112, by rfl⟩ : syracuseStep 58025483 = 87038225) B87038225
theorem B38683655 : Blo 2263435 38683655 := bstep (se 1 (by rfl) ⟨29012741, by rfl⟩ : syracuseStep 38683655 = 58025483) B58025483
theorem B25789103 : Blo 2263435 25789103 := bstep (se 1 (by rfl) ⟨19341827, by rfl⟩ : syracuseStep 25789103 = 38683655) B38683655
theorem B17192735 : Blo 2263435 17192735 := bstep (se 1 (by rfl) ⟨12894551, by rfl⟩ : syracuseStep 17192735 = 25789103) B25789103
theorem B11461823 : Blo 2263435 11461823 := bstep (se 1 (by rfl) ⟨8596367, by rfl⟩ : syracuseStep 11461823 = 17192735) B17192735
theorem B7641215 : Blo 2263435 7641215 := bstep (se 1 (by rfl) ⟨5730911, by rfl⟩ : syracuseStep 7641215 = 11461823) B11461823
theorem B5094143 : Blo 2263435 5094143 := bstep (se 1 (by rfl) ⟨3820607, by rfl⟩ : syracuseStep 5094143 = 7641215) B7641215
theorem B3396095 : Blo 2263435 3396095 := bstep (se 1 (by rfl) ⟨2547071, by rfl⟩ : syracuseStep 3396095 = 5094143) B5094143
theorem B2264063 : Blo 2263435 2264063 := bstep (se 1 (by rfl) ⟨1698047, by rfl⟩ : syracuseStep 2264063 = 3396095) B3396095
theorem B3396101 : Blo 2263435 3396101 := bbase (se 4 (by rfl) ⟨318384, by rfl⟩ : syracuseStep 3396101 = 636769) (by norm_num)
theorem B2264067 : Blo 2263435 2264067 := bstep (se 1 (by rfl) ⟨1698050, by rfl⟩ : syracuseStep 2264067 = 3396101) B3396101
theorem B3820621 : Blo 2263435 3820621 := bbase (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) (by norm_num)
theorem B5094161 : Blo 2263435 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B3396107 : Blo 2263435 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B2264071 : Blo 2263435 2264071 := bstep (se 1 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 2264071 = 3396107) B3396107
theorem B2547085 : Blo 2263435 2547085 := bbase (se 3 (by rfl) ⟨477578, by rfl⟩ : syracuseStep 2547085 = 955157) (by norm_num)
theorem B3396113 : Blo 2263435 3396113 := bstep (se 2 (by rfl) ⟨1273542, by rfl⟩ : syracuseStep 3396113 = 2547085) B2547085
theorem B2264075 : Blo 2263435 2264075 := bstep (se 1 (by rfl) ⟨1698056, by rfl⟩ : syracuseStep 2264075 = 3396113) B3396113
theorem B7641269 : Blo 2263435 7641269 := bbase (se 5 (by rfl) ⟨358184, by rfl⟩ : syracuseStep 7641269 = 716369) (by norm_num)
theorem B5094179 : Blo 2263435 5094179 := bstep (se 1 (by rfl) ⟨3820634, by rfl⟩ : syracuseStep 5094179 = 7641269) B7641269
theorem B3396119 : Blo 2263435 3396119 := bstep (se 1 (by rfl) ⟨2547089, by rfl⟩ : syracuseStep 3396119 = 5094179) B5094179
theorem B2264079 : Blo 2263435 2264079 := bstep (se 1 (by rfl) ⟨1698059, by rfl⟩ : syracuseStep 2264079 = 3396119) B3396119
theorem B3396125 : Blo 2263435 3396125 := bbase (se 3 (by rfl) ⟨636773, by rfl⟩ : syracuseStep 3396125 = 1273547) (by norm_num)
theorem B2264083 : Blo 2263435 2264083 := bstep (se 1 (by rfl) ⟨1698062, by rfl⟩ : syracuseStep 2264083 = 3396125) B3396125
theorem B5094197 : Blo 2263435 5094197 := bbase (se 5 (by rfl) ⟨238790, by rfl⟩ : syracuseStep 5094197 = 477581) (by norm_num)
theorem B3396131 : Blo 2263435 3396131 := bstep (se 1 (by rfl) ⟨2547098, by rfl⟩ : syracuseStep 3396131 = 5094197) B5094197
theorem B2264087 : Blo 2263435 2264087 := bstep (se 1 (by rfl) ⟨1698065, by rfl⟩ : syracuseStep 2264087 = 3396131) B3396131
theorem B13070645 : Blo 2263435 13070645 := bbase (se 5 (by rfl) ⟨612686, by rfl⟩ : syracuseStep 13070645 = 1225373) (by norm_num)
theorem B8713763 : Blo 2263435 8713763 := bstep (se 1 (by rfl) ⟨6535322, by rfl⟩ : syracuseStep 8713763 = 13070645) B13070645
theorem B5809175 : Blo 2263435 5809175 := bstep (se 1 (by rfl) ⟨4356881, by rfl⟩ : syracuseStep 5809175 = 8713763) B8713763
theorem B3872783 : Blo 2263435 3872783 := bstep (se 1 (by rfl) ⟨2904587, by rfl⟩ : syracuseStep 3872783 = 5809175) B5809175
theorem B10327421 : Blo 2263435 10327421 := bstep (se 3 (by rfl) ⟨1936391, by rfl⟩ : syracuseStep 10327421 = 3872783) B3872783
theorem B6884947 : Blo 2263435 6884947 := bstep (se 1 (by rfl) ⟨5163710, by rfl⟩ : syracuseStep 6884947 = 10327421) B10327421
theorem B9179929 : Blo 2263435 9179929 := bstep (se 2 (by rfl) ⟨3442473, by rfl⟩ : syracuseStep 9179929 = 6884947) B6884947
theorem B12239905 : Blo 2263435 12239905 := bstep (se 2 (by rfl) ⟨4589964, by rfl⟩ : syracuseStep 12239905 = 9179929) B9179929
theorem B16319873 : Blo 2263435 16319873 := bstep (se 2 (by rfl) ⟨6119952, by rfl⟩ : syracuseStep 16319873 = 12239905) B12239905
theorem B10879915 : Blo 2263435 10879915 := bstep (se 1 (by rfl) ⟨8159936, by rfl⟩ : syracuseStep 10879915 = 16319873) B16319873
theorem B14506553 : Blo 2263435 14506553 := bstep (se 2 (by rfl) ⟨5439957, by rfl⟩ : syracuseStep 14506553 = 10879915) B10879915
theorem B9671035 : Blo 2263435 9671035 := bstep (se 1 (by rfl) ⟨7253276, by rfl⟩ : syracuseStep 9671035 = 14506553) B14506553
theorem B12894713 : Blo 2263435 12894713 := bstep (se 2 (by rfl) ⟨4835517, by rfl⟩ : syracuseStep 12894713 = 9671035) B9671035
theorem B8596475 : Blo 2263435 8596475 := bstep (se 1 (by rfl) ⟨6447356, by rfl⟩ : syracuseStep 8596475 = 12894713) B12894713
theorem B5730983 : Blo 2263435 5730983 := bstep (se 1 (by rfl) ⟨4298237, by rfl⟩ : syracuseStep 5730983 = 8596475) B8596475
theorem B3820655 : Blo 2263435 3820655 := bstep (se 1 (by rfl) ⟨2865491, by rfl⟩ : syracuseStep 3820655 = 5730983) B5730983
theorem B2547103 : Blo 2263435 2547103 := bstep (se 1 (by rfl) ⟨1910327, by rfl⟩ : syracuseStep 2547103 = 3820655) B3820655
theorem B3396137 : Blo 2263435 3396137 := bstep (se 2 (by rfl) ⟨1273551, by rfl⟩ : syracuseStep 3396137 = 2547103) B2547103
theorem B2264091 : Blo 2263435 2264091 := bstep (se 1 (by rfl) ⟨1698068, by rfl⟩ : syracuseStep 2264091 = 3396137) B3396137
theorem B6535333 : Blo 2263435 6535333 := bbase (se 4 (by rfl) ⟨612687, by rfl⟩ : syracuseStep 6535333 = 1225375) (by norm_num)
theorem B34855109 : Blo 2263435 34855109 := bstep (se 4 (by rfl) ⟨3267666, by rfl⟩ : syracuseStep 34855109 = 6535333) B6535333
theorem B23236739 : Blo 2263435 23236739 := bstep (se 1 (by rfl) ⟨17427554, by rfl⟩ : syracuseStep 23236739 = 34855109) B34855109
theorem B15491159 : Blo 2263435 15491159 := bstep (se 1 (by rfl) ⟨11618369, by rfl⟩ : syracuseStep 15491159 = 23236739) B23236739
theorem B10327439 : Blo 2263435 10327439 := bstep (se 1 (by rfl) ⟨7745579, by rfl⟩ : syracuseStep 10327439 = 15491159) B15491159
theorem B6884959 : Blo 2263435 6884959 := bstep (se 1 (by rfl) ⟨5163719, by rfl⟩ : syracuseStep 6884959 = 10327439) B10327439
theorem B9179945 : Blo 2263435 9179945 := bstep (se 2 (by rfl) ⟨3442479, by rfl⟩ : syracuseStep 9179945 = 6884959) B6884959
theorem B6119963 : Blo 2263435 6119963 := bstep (se 1 (by rfl) ⟨4589972, by rfl⟩ : syracuseStep 6119963 = 9179945) B9179945
theorem B4079975 : Blo 2263435 4079975 := bstep (se 1 (by rfl) ⟨3059981, by rfl⟩ : syracuseStep 4079975 = 6119963) B6119963
theorem B10879933 : Blo 2263435 10879933 := bstep (se 3 (by rfl) ⟨2039987, by rfl⟩ : syracuseStep 10879933 = 4079975) B4079975
theorem B14506577 : Blo 2263435 14506577 := bstep (se 2 (by rfl) ⟨5439966, by rfl⟩ : syracuseStep 14506577 = 10879933) B10879933
theorem B9671051 : Blo 2263435 9671051 := bstep (se 1 (by rfl) ⟨7253288, by rfl⟩ : syracuseStep 9671051 = 14506577) B14506577
theorem B6447367 : Blo 2263435 6447367 := bstep (se 1 (by rfl) ⟨4835525, by rfl⟩ : syracuseStep 6447367 = 9671051) B9671051
theorem B8596489 : Blo 2263435 8596489 := bstep (se 2 (by rfl) ⟨3223683, by rfl⟩ : syracuseStep 8596489 = 6447367) B6447367
theorem B11461985 : Blo 2263435 11461985 := bstep (se 2 (by rfl) ⟨4298244, by rfl⟩ : syracuseStep 11461985 = 8596489) B8596489
theorem B7641323 : Blo 2263435 7641323 := bstep (se 1 (by rfl) ⟨5730992, by rfl⟩ : syracuseStep 7641323 = 11461985) B11461985
theorem B5094215 : Blo 2263435 5094215 := bstep (se 1 (by rfl) ⟨3820661, by rfl⟩ : syracuseStep 5094215 = 7641323) B7641323
theorem B3396143 : Blo 2263435 3396143 := bstep (se 1 (by rfl) ⟨2547107, by rfl⟩ : syracuseStep 3396143 = 5094215) B5094215
theorem B2264095 : Blo 2263435 2264095 := bstep (se 1 (by rfl) ⟨1698071, by rfl⟩ : syracuseStep 2264095 = 3396143) B3396143
theorem B3396149 : Blo 2263435 3396149 := bbase (se 5 (by rfl) ⟨159194, by rfl⟩ : syracuseStep 3396149 = 318389) (by norm_num)
theorem B2264099 : Blo 2263435 2264099 := bstep (se 1 (by rfl) ⟨1698074, by rfl⟩ : syracuseStep 2264099 = 3396149) B3396149
theorem B5731013 : Blo 2263435 5731013 := bbase (se 4 (by rfl) ⟨537282, by rfl⟩ : syracuseStep 5731013 = 1074565) (by norm_num)
theorem B3820675 : Blo 2263435 3820675 := bstep (se 1 (by rfl) ⟨2865506, by rfl⟩ : syracuseStep 3820675 = 5731013) B5731013
theorem B5094233 : Blo 2263435 5094233 := bstep (se 2 (by rfl) ⟨1910337, by rfl⟩ : syracuseStep 5094233 = 3820675) B3820675
theorem B3396155 : Blo 2263435 3396155 := bstep (se 1 (by rfl) ⟨2547116, by rfl⟩ : syracuseStep 3396155 = 5094233) B5094233
theorem B2264103 : Blo 2263435 2264103 := bstep (se 1 (by rfl) ⟨1698077, by rfl⟩ : syracuseStep 2264103 = 3396155) B3396155
theorem B2547121 : Blo 2263435 2547121 := bbase (se 2 (by rfl) ⟨955170, by rfl⟩ : syracuseStep 2547121 = 1910341) (by norm_num)
theorem B3396161 : Blo 2263435 3396161 := bstep (se 2 (by rfl) ⟨1273560, by rfl⟩ : syracuseStep 3396161 = 2547121) B2547121
theorem B2264107 : Blo 2263435 2264107 := bstep (se 1 (by rfl) ⟨1698080, by rfl⟩ : syracuseStep 2264107 = 3396161) B3396161
theorem B6447413 : Blo 2263435 6447413 := bbase (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) (by norm_num)
theorem B4298275 : Blo 2263435 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B5731033 : Blo 2263435 5731033 := bstep (se 2 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 5731033 = 4298275) B4298275
theorem B7641377 : Blo 2263435 7641377 := bstep (se 2 (by rfl) ⟨2865516, by rfl⟩ : syracuseStep 7641377 = 5731033) B5731033
theorem B5094251 : Blo 2263435 5094251 := bstep (se 1 (by rfl) ⟨3820688, by rfl⟩ : syracuseStep 5094251 = 7641377) B7641377
theorem B3396167 : Blo 2263435 3396167 := bstep (se 1 (by rfl) ⟨2547125, by rfl⟩ : syracuseStep 3396167 = 5094251) B5094251
theorem B2264111 : Blo 2263435 2264111 := bstep (se 1 (by rfl) ⟨1698083, by rfl⟩ : syracuseStep 2264111 = 3396167) B3396167
theorem B3396173 : Blo 2263435 3396173 := bbase (se 3 (by rfl) ⟨636782, by rfl⟩ : syracuseStep 3396173 = 1273565) (by norm_num)
theorem B2264115 : Blo 2263435 2264115 := bstep (se 1 (by rfl) ⟨1698086, by rfl⟩ : syracuseStep 2264115 = 3396173) B3396173
theorem B5094269 : Blo 2263435 5094269 := bbase (se 3 (by rfl) ⟨955175, by rfl⟩ : syracuseStep 5094269 = 1910351) (by norm_num)
theorem B3396179 : Blo 2263435 3396179 := bstep (se 1 (by rfl) ⟨2547134, by rfl⟩ : syracuseStep 3396179 = 5094269) B5094269
theorem B2264119 : Blo 2263435 2264119 := bstep (se 1 (by rfl) ⟨1698089, by rfl⟩ : syracuseStep 2264119 = 3396179) B3396179
theorem B3820709 : Blo 2263435 3820709 := bbase (se 4 (by rfl) ⟨358191, by rfl⟩ : syracuseStep 3820709 = 716383) (by norm_num)
theorem B2547139 : Blo 2263435 2547139 := bstep (se 1 (by rfl) ⟨1910354, by rfl⟩ : syracuseStep 2547139 = 3820709) B3820709
theorem B3396185 : Blo 2263435 3396185 := bstep (se 2 (by rfl) ⟨1273569, by rfl⟩ : syracuseStep 3396185 = 2547139) B2547139
theorem B2264123 : Blo 2263435 2264123 := bstep (se 1 (by rfl) ⟨1698092, by rfl⟩ : syracuseStep 2264123 = 3396185) B3396185
theorem B2417797 : Blo 2263435 2417797 := bbase (se 4 (by rfl) ⟨226668, by rfl⟩ : syracuseStep 2417797 = 453337) (by norm_num)
theorem B3223729 : Blo 2263435 3223729 := bstep (se 2 (by rfl) ⟨1208898, by rfl⟩ : syracuseStep 3223729 = 2417797) B2417797
theorem B17193221 : Blo 2263435 17193221 := bstep (se 4 (by rfl) ⟨1611864, by rfl⟩ : syracuseStep 17193221 = 3223729) B3223729
theorem B11462147 : Blo 2263435 11462147 := bstep (se 1 (by rfl) ⟨8596610, by rfl⟩ : syracuseStep 11462147 = 17193221) B17193221
theorem B7641431 : Blo 2263435 7641431 := bstep (se 1 (by rfl) ⟨5731073, by rfl⟩ : syracuseStep 7641431 = 11462147) B11462147
theorem B5094287 : Blo 2263435 5094287 := bstep (se 1 (by rfl) ⟨3820715, by rfl⟩ : syracuseStep 5094287 = 7641431) B7641431
theorem B3396191 : Blo 2263435 3396191 := bstep (se 1 (by rfl) ⟨2547143, by rfl⟩ : syracuseStep 3396191 = 5094287) B5094287
theorem B2264127 : Blo 2263435 2264127 := bstep (se 1 (by rfl) ⟨1698095, by rfl⟩ : syracuseStep 2264127 = 3396191) B3396191
theorem B3396197 : Blo 2263435 3396197 := bbase (se 4 (by rfl) ⟨318393, by rfl⟩ : syracuseStep 3396197 = 636787) (by norm_num)
theorem B2264131 : Blo 2263435 2264131 := bstep (se 1 (by rfl) ⟨1698098, by rfl⟩ : syracuseStep 2264131 = 3396197) B3396197
theorem B3223741 : Blo 2263435 3223741 := bbase (se 3 (by rfl) ⟨604451, by rfl⟩ : syracuseStep 3223741 = 1208903) (by norm_num)
theorem B4298321 : Blo 2263435 4298321 := bstep (se 2 (by rfl) ⟨1611870, by rfl⟩ : syracuseStep 4298321 = 3223741) B3223741
theorem B2865547 : Blo 2263435 2865547 := bstep (se 1 (by rfl) ⟨2149160, by rfl⟩ : syracuseStep 2865547 = 4298321) B4298321
theorem B3820729 : Blo 2263435 3820729 := bstep (se 2 (by rfl) ⟨1432773, by rfl⟩ : syracuseStep 3820729 = 2865547) B2865547
theorem B5094305 : Blo 2263435 5094305 := bstep (se 2 (by rfl) ⟨1910364, by rfl⟩ : syracuseStep 5094305 = 3820729) B3820729
theorem B3396203 : Blo 2263435 3396203 := bstep (se 1 (by rfl) ⟨2547152, by rfl⟩ : syracuseStep 3396203 = 5094305) B5094305
theorem B2264135 : Blo 2263435 2264135 := bstep (se 1 (by rfl) ⟨1698101, by rfl⟩ : syracuseStep 2264135 = 3396203) B3396203
theorem B2547157 : Blo 2263435 2547157 := bbase (se 7 (by rfl) ⟨29849, by rfl⟩ : syracuseStep 2547157 = 59699) (by norm_num)
theorem B3396209 : Blo 2263435 3396209 := bstep (se 2 (by rfl) ⟨1273578, by rfl⟩ : syracuseStep 3396209 = 2547157) B2547157
theorem B2264139 : Blo 2263435 2264139 := bstep (se 1 (by rfl) ⟨1698104, by rfl⟩ : syracuseStep 2264139 = 3396209) B3396209
theorem B2865557 : Blo 2263435 2865557 := bbase (se 6 (by rfl) ⟨67161, by rfl⟩ : syracuseStep 2865557 = 134323) (by norm_num)
theorem B7641485 : Blo 2263435 7641485 := bstep (se 3 (by rfl) ⟨1432778, by rfl⟩ : syracuseStep 7641485 = 2865557) B2865557
theorem B5094323 : Blo 2263435 5094323 := bstep (se 1 (by rfl) ⟨3820742, by rfl⟩ : syracuseStep 5094323 = 7641485) B7641485
theorem B3396215 : Blo 2263435 3396215 := bstep (se 1 (by rfl) ⟨2547161, by rfl⟩ : syracuseStep 3396215 = 5094323) B5094323
theorem B2264143 : Blo 2263435 2264143 := bstep (se 1 (by rfl) ⟨1698107, by rfl⟩ : syracuseStep 2264143 = 3396215) B3396215
theorem B3396221 : Blo 2263435 3396221 := bbase (se 3 (by rfl) ⟨636791, by rfl⟩ : syracuseStep 3396221 = 1273583) (by norm_num)
theorem B2264147 : Blo 2263435 2264147 := bstep (se 1 (by rfl) ⟨1698110, by rfl⟩ : syracuseStep 2264147 = 3396221) B3396221
theorem B5094341 : Blo 2263435 5094341 := bbase (se 4 (by rfl) ⟨477594, by rfl⟩ : syracuseStep 5094341 = 955189) (by norm_num)
theorem B3396227 : Blo 2263435 3396227 := bstep (se 1 (by rfl) ⟨2547170, by rfl⟩ : syracuseStep 3396227 = 5094341) B5094341
theorem B2264151 : Blo 2263435 2264151 := bstep (se 1 (by rfl) ⟨1698113, by rfl⟩ : syracuseStep 2264151 = 3396227) B3396227
theorem B3626741 : Blo 2263435 3626741 := bbase (se 5 (by rfl) ⟨170003, by rfl⟩ : syracuseStep 3626741 = 340007) (by norm_num)
theorem B9671309 : Blo 2263435 9671309 := bstep (se 3 (by rfl) ⟨1813370, by rfl⟩ : syracuseStep 9671309 = 3626741) B3626741
theorem B6447539 : Blo 2263435 6447539 := bstep (se 1 (by rfl) ⟨4835654, by rfl⟩ : syracuseStep 6447539 = 9671309) B9671309
theorem B4298359 : Blo 2263435 4298359 := bstep (se 1 (by rfl) ⟨3223769, by rfl⟩ : syracuseStep 4298359 = 6447539) B6447539
theorem B5731145 : Blo 2263435 5731145 := bstep (se 2 (by rfl) ⟨2149179, by rfl⟩ : syracuseStep 5731145 = 4298359) B4298359
theorem B3820763 : Blo 2263435 3820763 := bstep (se 1 (by rfl) ⟨2865572, by rfl⟩ : syracuseStep 3820763 = 5731145) B5731145
theorem B2547175 : Blo 2263435 2547175 := bstep (se 1 (by rfl) ⟨1910381, by rfl⟩ : syracuseStep 2547175 = 3820763) B3820763
theorem B3396233 : Blo 2263435 3396233 := bstep (se 2 (by rfl) ⟨1273587, by rfl⟩ : syracuseStep 3396233 = 2547175) B2547175
theorem B2264155 : Blo 2263435 2264155 := bstep (se 1 (by rfl) ⟨1698116, by rfl⟩ : syracuseStep 2264155 = 3396233) B3396233
theorem B11462309 : Blo 2263435 11462309 := bbase (se 4 (by rfl) ⟨1074591, by rfl⟩ : syracuseStep 11462309 = 2149183) (by norm_num)
theorem B7641539 : Blo 2263435 7641539 := bstep (se 1 (by rfl) ⟨5731154, by rfl⟩ : syracuseStep 7641539 = 11462309) B11462309
theorem B5094359 : Blo 2263435 5094359 := bstep (se 1 (by rfl) ⟨3820769, by rfl⟩ : syracuseStep 5094359 = 7641539) B7641539
theorem B3396239 : Blo 2263435 3396239 := bstep (se 1 (by rfl) ⟨2547179, by rfl⟩ : syracuseStep 3396239 = 5094359) B5094359
theorem B2264159 : Blo 2263435 2264159 := bstep (se 1 (by rfl) ⟨1698119, by rfl⟩ : syracuseStep 2264159 = 3396239) B3396239
theorem B3396245 : Blo 2263435 3396245 := bbase (se 6 (by rfl) ⟨79599, by rfl⟩ : syracuseStep 3396245 = 159199) (by norm_num)
theorem B2264163 : Blo 2263435 2264163 := bstep (se 1 (by rfl) ⟨1698122, by rfl⟩ : syracuseStep 2264163 = 3396245) B3396245
theorem B8498789 : Blo 2263435 8498789 := bbase (se 4 (by rfl) ⟨796761, by rfl⟩ : syracuseStep 8498789 = 1593523) (by norm_num)
theorem B5665859 : Blo 2263435 5665859 := bstep (se 1 (by rfl) ⟨4249394, by rfl⟩ : syracuseStep 5665859 = 8498789) B8498789
theorem B3777239 : Blo 2263435 3777239 := bstep (se 1 (by rfl) ⟨2832929, by rfl⟩ : syracuseStep 3777239 = 5665859) B5665859
theorem B2518159 : Blo 2263435 2518159 := bstep (se 1 (by rfl) ⟨1888619, by rfl⟩ : syracuseStep 2518159 = 3777239) B3777239
theorem B3357545 : Blo 2263435 3357545 := bstep (se 2 (by rfl) ⟨1259079, by rfl⟩ : syracuseStep 3357545 = 2518159) B2518159
theorem B8953453 : Blo 2263435 8953453 := bstep (se 3 (by rfl) ⟨1678772, by rfl⟩ : syracuseStep 8953453 = 3357545) B3357545
theorem B11937937 : Blo 2263435 11937937 := bstep (se 2 (by rfl) ⟨4476726, by rfl⟩ : syracuseStep 11937937 = 8953453) B8953453
theorem B15917249 : Blo 2263435 15917249 := bstep (se 2 (by rfl) ⟨5968968, by rfl⟩ : syracuseStep 15917249 = 11937937) B11937937
theorem B42445997 : Blo 2263435 42445997 := bstep (se 3 (by rfl) ⟨7958624, by rfl⟩ : syracuseStep 42445997 = 15917249) B15917249
theorem B28297331 : Blo 2263435 28297331 := bstep (se 1 (by rfl) ⟨21222998, by rfl⟩ : syracuseStep 28297331 = 42445997) B42445997
theorem B18864887 : Blo 2263435 18864887 := bstep (se 1 (by rfl) ⟨14148665, by rfl⟩ : syracuseStep 18864887 = 28297331) B28297331
theorem B50306365 : Blo 2263435 50306365 := bstep (se 3 (by rfl) ⟨9432443, by rfl⟩ : syracuseStep 50306365 = 18864887) B18864887
theorem B268300613 : Blo 2263435 268300613 := bstep (se 4 (by rfl) ⟨25153182, by rfl⟩ : syracuseStep 268300613 = 50306365) B50306365
theorem B178867075 : Blo 2263435 178867075 := bstep (se 1 (by rfl) ⟨134150306, by rfl⟩ : syracuseStep 178867075 = 268300613) B268300613
theorem B238489433 : Blo 2263435 238489433 := bstep (se 2 (by rfl) ⟨89433537, by rfl⟩ : syracuseStep 238489433 = 178867075) B178867075
theorem B158992955 : Blo 2263435 158992955 := bstep (se 1 (by rfl) ⟨119244716, by rfl⟩ : syracuseStep 158992955 = 238489433) B238489433
theorem B105995303 : Blo 2263435 105995303 := bstep (se 1 (by rfl) ⟨79496477, by rfl⟩ : syracuseStep 105995303 = 158992955) B158992955
theorem B70663535 : Blo 2263435 70663535 := bstep (se 1 (by rfl) ⟨52997651, by rfl⟩ : syracuseStep 70663535 = 105995303) B105995303
theorem B47109023 : Blo 2263435 47109023 := bstep (se 1 (by rfl) ⟨35331767, by rfl⟩ : syracuseStep 47109023 = 70663535) B70663535
theorem B31406015 : Blo 2263435 31406015 := bstep (se 1 (by rfl) ⟨23554511, by rfl⟩ : syracuseStep 31406015 = 47109023) B47109023
theorem B83749373 : Blo 2263435 83749373 := bstep (se 3 (by rfl) ⟨15703007, by rfl⟩ : syracuseStep 83749373 = 31406015) B31406015
theorem B55832915 : Blo 2263435 55832915 := bstep (se 1 (by rfl) ⟨41874686, by rfl⟩ : syracuseStep 55832915 = 83749373) B83749373
theorem B37221943 : Blo 2263435 37221943 := bstep (se 1 (by rfl) ⟨27916457, by rfl⟩ : syracuseStep 37221943 = 55832915) B55832915
theorem B49629257 : Blo 2263435 49629257 := bstep (se 2 (by rfl) ⟨18610971, by rfl⟩ : syracuseStep 49629257 = 37221943) B37221943
theorem B33086171 : Blo 2263435 33086171 := bstep (se 1 (by rfl) ⟨24814628, by rfl⟩ : syracuseStep 33086171 = 49629257) B49629257
theorem B22057447 : Blo 2263435 22057447 := bstep (se 1 (by rfl) ⟨16543085, by rfl⟩ : syracuseStep 22057447 = 33086171) B33086171
theorem B29409929 : Blo 2263435 29409929 := bstep (se 2 (by rfl) ⟨11028723, by rfl⟩ : syracuseStep 29409929 = 22057447) B22057447
theorem B19606619 : Blo 2263435 19606619 := bstep (se 1 (by rfl) ⟨14704964, by rfl⟩ : syracuseStep 19606619 = 29409929) B29409929
theorem B13071079 : Blo 2263435 13071079 := bstep (se 1 (by rfl) ⟨9803309, by rfl⟩ : syracuseStep 13071079 = 19606619) B19606619
theorem B17428105 : Blo 2263435 17428105 := bstep (se 2 (by rfl) ⟨6535539, by rfl⟩ : syracuseStep 17428105 = 13071079) B13071079
theorem B92949893 : Blo 2263435 92949893 := bstep (se 4 (by rfl) ⟨8714052, by rfl⟩ : syracuseStep 92949893 = 17428105) B17428105
theorem B61966595 : Blo 2263435 61966595 := bstep (se 1 (by rfl) ⟨46474946, by rfl⟩ : syracuseStep 61966595 = 92949893) B92949893
theorem B41311063 : Blo 2263435 41311063 := bstep (se 1 (by rfl) ⟨30983297, by rfl⟩ : syracuseStep 41311063 = 61966595) B61966595
theorem B55081417 : Blo 2263435 55081417 := bstep (se 2 (by rfl) ⟨20655531, by rfl⟩ : syracuseStep 55081417 = 41311063) B41311063
theorem B73441889 : Blo 2263435 73441889 := bstep (se 2 (by rfl) ⟨27540708, by rfl⟩ : syracuseStep 73441889 = 55081417) B55081417
theorem B48961259 : Blo 2263435 48961259 := bstep (se 1 (by rfl) ⟨36720944, by rfl⟩ : syracuseStep 48961259 = 73441889) B73441889
theorem B32640839 : Blo 2263435 32640839 := bstep (se 1 (by rfl) ⟨24480629, by rfl⟩ : syracuseStep 32640839 = 48961259) B48961259
theorem B21760559 : Blo 2263435 21760559 := bstep (se 1 (by rfl) ⟨16320419, by rfl⟩ : syracuseStep 21760559 = 32640839) B32640839
theorem B14507039 : Blo 2263435 14507039 := bstep (se 1 (by rfl) ⟨10880279, by rfl⟩ : syracuseStep 14507039 = 21760559) B21760559
theorem B9671359 : Blo 2263435 9671359 := bstep (se 1 (by rfl) ⟨7253519, by rfl⟩ : syracuseStep 9671359 = 14507039) B14507039
theorem B12895145 : Blo 2263435 12895145 := bstep (se 2 (by rfl) ⟨4835679, by rfl⟩ : syracuseStep 12895145 = 9671359) B9671359
theorem B8596763 : Blo 2263435 8596763 := bstep (se 1 (by rfl) ⟨6447572, by rfl⟩ : syracuseStep 8596763 = 12895145) B12895145
theorem B5731175 : Blo 2263435 5731175 := bstep (se 1 (by rfl) ⟨4298381, by rfl⟩ : syracuseStep 5731175 = 8596763) B8596763
theorem B3820783 : Blo 2263435 3820783 := bstep (se 1 (by rfl) ⟨2865587, by rfl⟩ : syracuseStep 3820783 = 5731175) B5731175
theorem B5094377 : Blo 2263435 5094377 := bstep (se 2 (by rfl) ⟨1910391, by rfl⟩ : syracuseStep 5094377 = 3820783) B3820783
theorem B3396251 : Blo 2263435 3396251 := bstep (se 1 (by rfl) ⟨2547188, by rfl⟩ : syracuseStep 3396251 = 5094377) B5094377
theorem B2264167 : Blo 2263435 2264167 := bstep (se 1 (by rfl) ⟨1698125, by rfl⟩ : syracuseStep 2264167 = 3396251) B3396251
theorem B2547193 : Blo 2263435 2547193 := bbase (se 2 (by rfl) ⟨955197, by rfl⟩ : syracuseStep 2547193 = 1910395) (by norm_num)
theorem B3396257 : Blo 2263435 3396257 := bstep (se 2 (by rfl) ⟨1273596, by rfl⟩ : syracuseStep 3396257 = 2547193) B2547193
theorem B2264171 : Blo 2263435 2264171 := bstep (se 1 (by rfl) ⟨1698128, by rfl⟩ : syracuseStep 2264171 = 3396257) B3396257
theorem B5234357 : Blo 2263435 5234357 := bbase (se 5 (by rfl) ⟨245360, by rfl⟩ : syracuseStep 5234357 = 490721) (by norm_num)
theorem B3489571 : Blo 2263435 3489571 := bstep (se 1 (by rfl) ⟨2617178, by rfl⟩ : syracuseStep 3489571 = 5234357) B5234357
theorem B4652761 : Blo 2263435 4652761 := bstep (se 2 (by rfl) ⟨1744785, by rfl⟩ : syracuseStep 4652761 = 3489571) B3489571
theorem B6203681 : Blo 2263435 6203681 := bstep (se 2 (by rfl) ⟨2326380, by rfl⟩ : syracuseStep 6203681 = 4652761) B4652761
theorem B4135787 : Blo 2263435 4135787 := bstep (se 1 (by rfl) ⟨3101840, by rfl⟩ : syracuseStep 4135787 = 6203681) B6203681
theorem B2757191 : Blo 2263435 2757191 := bstep (se 1 (by rfl) ⟨2067893, by rfl⟩ : syracuseStep 2757191 = 4135787) B4135787
theorem B29410037 : Blo 2263435 29410037 := bstep (se 5 (by rfl) ⟨1378595, by rfl⟩ : syracuseStep 29410037 = 2757191) B2757191
theorem B19606691 : Blo 2263435 19606691 := bstep (se 1 (by rfl) ⟨14705018, by rfl⟩ : syracuseStep 19606691 = 29410037) B29410037
theorem B13071127 : Blo 2263435 13071127 := bstep (se 1 (by rfl) ⟨9803345, by rfl⟩ : syracuseStep 13071127 = 19606691) B19606691
theorem B17428169 : Blo 2263435 17428169 := bstep (se 2 (by rfl) ⟨6535563, by rfl⟩ : syracuseStep 17428169 = 13071127) B13071127
theorem B46475117 : Blo 2263435 46475117 := bstep (se 3 (by rfl) ⟨8714084, by rfl⟩ : syracuseStep 46475117 = 17428169) B17428169
theorem B30983411 : Blo 2263435 30983411 := bstep (se 1 (by rfl) ⟨23237558, by rfl⟩ : syracuseStep 30983411 = 46475117) B46475117
theorem B20655607 : Blo 2263435 20655607 := bstep (se 1 (by rfl) ⟨15491705, by rfl⟩ : syracuseStep 20655607 = 30983411) B30983411
theorem B27540809 : Blo 2263435 27540809 := bstep (se 2 (by rfl) ⟨10327803, by rfl⟩ : syracuseStep 27540809 = 20655607) B20655607
theorem B18360539 : Blo 2263435 18360539 := bstep (se 1 (by rfl) ⟨13770404, by rfl⟩ : syracuseStep 18360539 = 27540809) B27540809
theorem B12240359 : Blo 2263435 12240359 := bstep (se 1 (by rfl) ⟨9180269, by rfl⟩ : syracuseStep 12240359 = 18360539) B18360539
theorem B8160239 : Blo 2263435 8160239 := bstep (se 1 (by rfl) ⟨6120179, by rfl⟩ : syracuseStep 8160239 = 12240359) B12240359
theorem B5440159 : Blo 2263435 5440159 := bstep (se 1 (by rfl) ⟨4080119, by rfl⟩ : syracuseStep 5440159 = 8160239) B8160239
theorem B7253545 : Blo 2263435 7253545 := bstep (se 2 (by rfl) ⟨2720079, by rfl⟩ : syracuseStep 7253545 = 5440159) B5440159
theorem B9671393 : Blo 2263435 9671393 := bstep (se 2 (by rfl) ⟨3626772, by rfl⟩ : syracuseStep 9671393 = 7253545) B7253545
theorem B6447595 : Blo 2263435 6447595 := bstep (se 1 (by rfl) ⟨4835696, by rfl⟩ : syracuseStep 6447595 = 9671393) B9671393
theorem B8596793 : Blo 2263435 8596793 := bstep (se 2 (by rfl) ⟨3223797, by rfl⟩ : syracuseStep 8596793 = 6447595) B6447595
theorem B5731195 : Blo 2263435 5731195 := bstep (se 1 (by rfl) ⟨4298396, by rfl⟩ : syracuseStep 5731195 = 8596793) B8596793
theorem B7641593 : Blo 2263435 7641593 := bstep (se 2 (by rfl) ⟨2865597, by rfl⟩ : syracuseStep 7641593 = 5731195) B5731195
theorem B5094395 : Blo 2263435 5094395 := bstep (se 1 (by rfl) ⟨3820796, by rfl⟩ : syracuseStep 5094395 = 7641593) B7641593
theorem B3396263 : Blo 2263435 3396263 := bstep (se 1 (by rfl) ⟨2547197, by rfl⟩ : syracuseStep 3396263 = 5094395) B5094395
theorem B2264175 : Blo 2263435 2264175 := bstep (se 1 (by rfl) ⟨1698131, by rfl⟩ : syracuseStep 2264175 = 3396263) B3396263
theorem B3396269 : Blo 2263435 3396269 := bbase (se 3 (by rfl) ⟨636800, by rfl⟩ : syracuseStep 3396269 = 1273601) (by norm_num)
theorem B2264179 : Blo 2263435 2264179 := bstep (se 1 (by rfl) ⟨1698134, by rfl⟩ : syracuseStep 2264179 = 3396269) B3396269
theorem B5094413 : Blo 2263435 5094413 := bbase (se 3 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 5094413 = 1910405) (by norm_num)
theorem B3396275 : Blo 2263435 3396275 := bstep (se 1 (by rfl) ⟨2547206, by rfl⟩ : syracuseStep 3396275 = 5094413) B5094413
theorem B2264183 : Blo 2263435 2264183 := bstep (se 1 (by rfl) ⟨1698137, by rfl⟩ : syracuseStep 2264183 = 3396275) B3396275
theorem B2865613 : Blo 2263435 2865613 := bbase (se 3 (by rfl) ⟨537302, by rfl⟩ : syracuseStep 2865613 = 1074605) (by norm_num)
theorem B3820817 : Blo 2263435 3820817 := bstep (se 2 (by rfl) ⟨1432806, by rfl⟩ : syracuseStep 3820817 = 2865613) B2865613
theorem B2547211 : Blo 2263435 2547211 := bstep (se 1 (by rfl) ⟨1910408, by rfl⟩ : syracuseStep 2547211 = 3820817) B3820817
theorem B3396281 : Blo 2263435 3396281 := bstep (se 2 (by rfl) ⟨1273605, by rfl⟩ : syracuseStep 3396281 = 2547211) B2547211
theorem B2264187 : Blo 2263435 2264187 := bstep (se 1 (by rfl) ⟨1698140, by rfl⟩ : syracuseStep 2264187 = 3396281) B3396281
theorem B3267805 : Blo 2263435 3267805 := bbase (se 3 (by rfl) ⟨612713, by rfl⟩ : syracuseStep 3267805 = 1225427) (by norm_num)
theorem B4357073 : Blo 2263435 4357073 := bstep (se 2 (by rfl) ⟨1633902, by rfl⟩ : syracuseStep 4357073 = 3267805) B3267805
theorem B2904715 : Blo 2263435 2904715 := bstep (se 1 (by rfl) ⟨2178536, by rfl⟩ : syracuseStep 2904715 = 4357073) B4357073
theorem B3872953 : Blo 2263435 3872953 := bstep (se 2 (by rfl) ⟨1452357, by rfl⟩ : syracuseStep 3872953 = 2904715) B2904715
theorem B20655749 : Blo 2263435 20655749 := bstep (se 4 (by rfl) ⟨1936476, by rfl⟩ : syracuseStep 20655749 = 3872953) B3872953
theorem B13770499 : Blo 2263435 13770499 := bstep (se 1 (by rfl) ⟨10327874, by rfl⟩ : syracuseStep 13770499 = 20655749) B20655749
theorem B18360665 : Blo 2263435 18360665 := bstep (se 2 (by rfl) ⟨6885249, by rfl⟩ : syracuseStep 18360665 = 13770499) B13770499
theorem B12240443 : Blo 2263435 12240443 := bstep (se 1 (by rfl) ⟨9180332, by rfl⟩ : syracuseStep 12240443 = 18360665) B18360665
theorem B32641181 : Blo 2263435 32641181 := bstep (se 3 (by rfl) ⟨6120221, by rfl⟩ : syracuseStep 32641181 = 12240443) B12240443
theorem B21760787 : Blo 2263435 21760787 := bstep (se 1 (by rfl) ⟨16320590, by rfl⟩ : syracuseStep 21760787 = 32641181) B32641181
theorem B14507191 : Blo 2263435 14507191 := bstep (se 1 (by rfl) ⟨10880393, by rfl⟩ : syracuseStep 14507191 = 21760787) B21760787
theorem B19342921 : Blo 2263435 19342921 := bstep (se 2 (by rfl) ⟨7253595, by rfl⟩ : syracuseStep 19342921 = 14507191) B14507191
theorem B25790561 : Blo 2263435 25790561 := bstep (se 2 (by rfl) ⟨9671460, by rfl⟩ : syracuseStep 25790561 = 19342921) B19342921
theorem B17193707 : Blo 2263435 17193707 := bstep (se 1 (by rfl) ⟨12895280, by rfl⟩ : syracuseStep 17193707 = 25790561) B25790561
theorem B11462471 : Blo 2263435 11462471 := bstep (se 1 (by rfl) ⟨8596853, by rfl⟩ : syracuseStep 11462471 = 17193707) B17193707
theorem B7641647 : Blo 2263435 7641647 := bstep (se 1 (by rfl) ⟨5731235, by rfl⟩ : syracuseStep 7641647 = 11462471) B11462471
theorem B5094431 : Blo 2263435 5094431 := bstep (se 1 (by rfl) ⟨3820823, by rfl⟩ : syracuseStep 5094431 = 7641647) B7641647
theorem B3396287 : Blo 2263435 3396287 := bstep (se 1 (by rfl) ⟨2547215, by rfl⟩ : syracuseStep 3396287 = 5094431) B5094431
theorem B2264191 : Blo 2263435 2264191 := bstep (se 1 (by rfl) ⟨1698143, by rfl⟩ : syracuseStep 2264191 = 3396287) B3396287
theorem B3396293 : Blo 2263435 3396293 := bbase (se 4 (by rfl) ⟨318402, by rfl⟩ : syracuseStep 3396293 = 636805) (by norm_num)
theorem B2264195 : Blo 2263435 2264195 := bstep (se 1 (by rfl) ⟨1698146, by rfl⟩ : syracuseStep 2264195 = 3396293) B3396293
theorem B3820837 : Blo 2263435 3820837 := bbase (se 4 (by rfl) ⟨358203, by rfl⟩ : syracuseStep 3820837 = 716407) (by norm_num)
theorem B5094449 : Blo 2263435 5094449 := bstep (se 2 (by rfl) ⟨1910418, by rfl⟩ : syracuseStep 5094449 = 3820837) B3820837
theorem B3396299 : Blo 2263435 3396299 := bstep (se 1 (by rfl) ⟨2547224, by rfl⟩ : syracuseStep 3396299 = 5094449) B5094449
theorem B2264199 : Blo 2263435 2264199 := bstep (se 1 (by rfl) ⟨1698149, by rfl⟩ : syracuseStep 2264199 = 3396299) B3396299
theorem B2547229 : Blo 2263435 2547229 := bbase (se 3 (by rfl) ⟨477605, by rfl⟩ : syracuseStep 2547229 = 955211) (by norm_num)
theorem B3396305 : Blo 2263435 3396305 := bstep (se 2 (by rfl) ⟨1273614, by rfl⟩ : syracuseStep 3396305 = 2547229) B2547229
theorem B2264203 : Blo 2263435 2264203 := bstep (se 1 (by rfl) ⟨1698152, by rfl⟩ : syracuseStep 2264203 = 3396305) B3396305
theorem B7641701 : Blo 2263435 7641701 := bbase (se 4 (by rfl) ⟨716409, by rfl⟩ : syracuseStep 7641701 = 1432819) (by norm_num)
theorem B5094467 : Blo 2263435 5094467 := bstep (se 1 (by rfl) ⟨3820850, by rfl⟩ : syracuseStep 5094467 = 7641701) B7641701
theorem B3396311 : Blo 2263435 3396311 := bstep (se 1 (by rfl) ⟨2547233, by rfl⟩ : syracuseStep 3396311 = 5094467) B5094467
theorem B2264207 : Blo 2263435 2264207 := bstep (se 1 (by rfl) ⟨1698155, by rfl⟩ : syracuseStep 2264207 = 3396311) B3396311
theorem B3396317 : Blo 2263435 3396317 := bbase (se 3 (by rfl) ⟨636809, by rfl⟩ : syracuseStep 3396317 = 1273619) (by norm_num)
theorem B2264211 : Blo 2263435 2264211 := bstep (se 1 (by rfl) ⟨1698158, by rfl⟩ : syracuseStep 2264211 = 3396317) B3396317
theorem B5094485 : Blo 2263435 5094485 := bbase (se 8 (by rfl) ⟨29850, by rfl⟩ : syracuseStep 5094485 = 59701) (by norm_num)
theorem B3396323 : Blo 2263435 3396323 := bstep (se 1 (by rfl) ⟨2547242, by rfl⟩ : syracuseStep 3396323 = 5094485) B5094485
theorem B2264215 : Blo 2263435 2264215 := bstep (se 1 (by rfl) ⟨1698161, by rfl⟩ : syracuseStep 2264215 = 3396323) B3396323
theorem B7746005 : Blo 2263435 7746005 := bbase (se 7 (by rfl) ⟨90773, by rfl⟩ : syracuseStep 7746005 = 181547) (by norm_num)
theorem B5164003 : Blo 2263435 5164003 := bstep (se 1 (by rfl) ⟨3873002, by rfl⟩ : syracuseStep 5164003 = 7746005) B7746005
theorem B6885337 : Blo 2263435 6885337 := bstep (se 2 (by rfl) ⟨2582001, by rfl⟩ : syracuseStep 6885337 = 5164003) B5164003
theorem B9180449 : Blo 2263435 9180449 := bstep (se 2 (by rfl) ⟨3442668, by rfl⟩ : syracuseStep 9180449 = 6885337) B6885337
theorem B6120299 : Blo 2263435 6120299 := bstep (se 1 (by rfl) ⟨4590224, by rfl⟩ : syracuseStep 6120299 = 9180449) B9180449
theorem B16320797 : Blo 2263435 16320797 := bstep (se 3 (by rfl) ⟨3060149, by rfl⟩ : syracuseStep 16320797 = 6120299) B6120299
theorem B10880531 : Blo 2263435 10880531 := bstep (se 1 (by rfl) ⟨8160398, by rfl⟩ : syracuseStep 10880531 = 16320797) B16320797
theorem B7253687 : Blo 2263435 7253687 := bstep (se 1 (by rfl) ⟨5440265, by rfl⟩ : syracuseStep 7253687 = 10880531) B10880531
theorem B4835791 : Blo 2263435 4835791 := bstep (se 1 (by rfl) ⟨3626843, by rfl⟩ : syracuseStep 4835791 = 7253687) B7253687
theorem B6447721 : Blo 2263435 6447721 := bstep (se 2 (by rfl) ⟨2417895, by rfl⟩ : syracuseStep 6447721 = 4835791) B4835791
theorem B8596961 : Blo 2263435 8596961 := bstep (se 2 (by rfl) ⟨3223860, by rfl⟩ : syracuseStep 8596961 = 6447721) B6447721
theorem B5731307 : Blo 2263435 5731307 := bstep (se 1 (by rfl) ⟨4298480, by rfl⟩ : syracuseStep 5731307 = 8596961) B8596961
theorem B3820871 : Blo 2263435 3820871 := bstep (se 1 (by rfl) ⟨2865653, by rfl⟩ : syracuseStep 3820871 = 5731307) B5731307
theorem B2547247 : Blo 2263435 2547247 := bstep (se 1 (by rfl) ⟨1910435, by rfl⟩ : syracuseStep 2547247 = 3820871) B3820871
theorem B3396329 : Blo 2263435 3396329 := bstep (se 2 (by rfl) ⟨1273623, by rfl⟩ : syracuseStep 3396329 = 2547247) B2547247
theorem B2264219 : Blo 2263435 2264219 := bstep (se 1 (by rfl) ⟨1698164, by rfl⟩ : syracuseStep 2264219 = 3396329) B3396329
theorem B4416581 : Blo 2263435 4416581 := bbase (se 4 (by rfl) ⟨414054, by rfl⟩ : syracuseStep 4416581 = 828109) (by norm_num)
theorem B2944387 : Blo 2263435 2944387 := bstep (se 1 (by rfl) ⟨2208290, by rfl⟩ : syracuseStep 2944387 = 4416581) B4416581
theorem B3925849 : Blo 2263435 3925849 := bstep (se 2 (by rfl) ⟨1472193, by rfl⟩ : syracuseStep 3925849 = 2944387) B2944387
theorem B5234465 : Blo 2263435 5234465 := bstep (se 2 (by rfl) ⟨1962924, by rfl⟩ : syracuseStep 5234465 = 3925849) B3925849
theorem B13958573 : Blo 2263435 13958573 := bstep (se 3 (by rfl) ⟨2617232, by rfl⟩ : syracuseStep 13958573 = 5234465) B5234465
theorem B37222861 : Blo 2263435 37222861 := bstep (se 3 (by rfl) ⟨6979286, by rfl⟩ : syracuseStep 37222861 = 13958573) B13958573
theorem B49630481 : Blo 2263435 49630481 := bstep (se 2 (by rfl) ⟨18611430, by rfl⟩ : syracuseStep 49630481 = 37222861) B37222861
theorem B33086987 : Blo 2263435 33086987 := bstep (se 1 (by rfl) ⟨24815240, by rfl⟩ : syracuseStep 33086987 = 49630481) B49630481
theorem B22057991 : Blo 2263435 22057991 := bstep (se 1 (by rfl) ⟨16543493, by rfl⟩ : syracuseStep 22057991 = 33086987) B33086987
theorem B14705327 : Blo 2263435 14705327 := bstep (se 1 (by rfl) ⟨11028995, by rfl⟩ : syracuseStep 14705327 = 22057991) B22057991
theorem B39214205 : Blo 2263435 39214205 := bstep (se 3 (by rfl) ⟨7352663, by rfl⟩ : syracuseStep 39214205 = 14705327) B14705327
theorem B26142803 : Blo 2263435 26142803 := bstep (se 1 (by rfl) ⟨19607102, by rfl⟩ : syracuseStep 26142803 = 39214205) B39214205
theorem B17428535 : Blo 2263435 17428535 := bstep (se 1 (by rfl) ⟨13071401, by rfl⟩ : syracuseStep 17428535 = 26142803) B26142803
theorem B11619023 : Blo 2263435 11619023 := bstep (se 1 (by rfl) ⟨8714267, by rfl⟩ : syracuseStep 11619023 = 17428535) B17428535
theorem B30984061 : Blo 2263435 30984061 := bstep (se 3 (by rfl) ⟨5809511, by rfl⟩ : syracuseStep 30984061 = 11619023) B11619023
theorem B41312081 : Blo 2263435 41312081 := bstep (se 2 (by rfl) ⟨15492030, by rfl⟩ : syracuseStep 41312081 = 30984061) B30984061
theorem B27541387 : Blo 2263435 27541387 := bstep (se 1 (by rfl) ⟨20656040, by rfl⟩ : syracuseStep 27541387 = 41312081) B41312081
theorem B36721849 : Blo 2263435 36721849 := bstep (se 2 (by rfl) ⟨13770693, by rfl⟩ : syracuseStep 36721849 = 27541387) B27541387
theorem B48962465 : Blo 2263435 48962465 := bstep (se 2 (by rfl) ⟨18360924, by rfl⟩ : syracuseStep 48962465 = 36721849) B36721849
theorem B32641643 : Blo 2263435 32641643 := bstep (se 1 (by rfl) ⟨24481232, by rfl⟩ : syracuseStep 32641643 = 48962465) B48962465
theorem B21761095 : Blo 2263435 21761095 := bstep (se 1 (by rfl) ⟨16320821, by rfl⟩ : syracuseStep 21761095 = 32641643) B32641643
theorem B29014793 : Blo 2263435 29014793 := bstep (se 2 (by rfl) ⟨10880547, by rfl⟩ : syracuseStep 29014793 = 21761095) B21761095
theorem B19343195 : Blo 2263435 19343195 := bstep (se 1 (by rfl) ⟨14507396, by rfl⟩ : syracuseStep 19343195 = 29014793) B29014793
theorem B12895463 : Blo 2263435 12895463 := bstep (se 1 (by rfl) ⟨9671597, by rfl⟩ : syracuseStep 12895463 = 19343195) B19343195
theorem B8596975 : Blo 2263435 8596975 := bstep (se 1 (by rfl) ⟨6447731, by rfl⟩ : syracuseStep 8596975 = 12895463) B12895463
theorem B11462633 : Blo 2263435 11462633 := bstep (se 2 (by rfl) ⟨4298487, by rfl⟩ : syracuseStep 11462633 = 8596975) B8596975
theorem B7641755 : Blo 2263435 7641755 := bstep (se 1 (by rfl) ⟨5731316, by rfl⟩ : syracuseStep 7641755 = 11462633) B11462633
theorem B5094503 : Blo 2263435 5094503 := bstep (se 1 (by rfl) ⟨3820877, by rfl⟩ : syracuseStep 5094503 = 7641755) B7641755
theorem B3396335 : Blo 2263435 3396335 := bstep (se 1 (by rfl) ⟨2547251, by rfl⟩ : syracuseStep 3396335 = 5094503) B5094503
theorem B2264223 : Blo 2263435 2264223 := bstep (se 1 (by rfl) ⟨1698167, by rfl⟩ : syracuseStep 2264223 = 3396335) B3396335
theorem B3396341 : Blo 2263435 3396341 := bbase (se 5 (by rfl) ⟨159203, by rfl⟩ : syracuseStep 3396341 = 318407) (by norm_num)
theorem B2264227 : Blo 2263435 2264227 := bstep (se 1 (by rfl) ⟨1698170, by rfl⟩ : syracuseStep 2264227 = 3396341) B3396341
theorem B4080221 : Blo 2263435 4080221 := bbase (se 3 (by rfl) ⟨765041, by rfl⟩ : syracuseStep 4080221 = 1530083) (by norm_num)
theorem B2720147 : Blo 2263435 2720147 := bstep (se 1 (by rfl) ⟨2040110, by rfl⟩ : syracuseStep 2720147 = 4080221) B4080221
theorem B7253725 : Blo 2263435 7253725 := bstep (se 3 (by rfl) ⟨1360073, by rfl⟩ : syracuseStep 7253725 = 2720147) B2720147
theorem B9671633 : Blo 2263435 9671633 := bstep (se 2 (by rfl) ⟨3626862, by rfl⟩ : syracuseStep 9671633 = 7253725) B7253725
theorem B6447755 : Blo 2263435 6447755 := bstep (se 1 (by rfl) ⟨4835816, by rfl⟩ : syracuseStep 6447755 = 9671633) B9671633
theorem B4298503 : Blo 2263435 4298503 := bstep (se 1 (by rfl) ⟨3223877, by rfl⟩ : syracuseStep 4298503 = 6447755) B6447755
theorem B5731337 : Blo 2263435 5731337 := bstep (se 2 (by rfl) ⟨2149251, by rfl⟩ : syracuseStep 5731337 = 4298503) B4298503
theorem B3820891 : Blo 2263435 3820891 := bstep (se 1 (by rfl) ⟨2865668, by rfl⟩ : syracuseStep 3820891 = 5731337) B5731337
theorem B5094521 : Blo 2263435 5094521 := bstep (se 2 (by rfl) ⟨1910445, by rfl⟩ : syracuseStep 5094521 = 3820891) B3820891
theorem B3396347 : Blo 2263435 3396347 := bstep (se 1 (by rfl) ⟨2547260, by rfl⟩ : syracuseStep 3396347 = 5094521) B5094521
theorem B2264231 : Blo 2263435 2264231 := bstep (se 1 (by rfl) ⟨1698173, by rfl⟩ : syracuseStep 2264231 = 3396347) B3396347
theorem B2547265 : Blo 2263435 2547265 := bbase (se 2 (by rfl) ⟨955224, by rfl⟩ : syracuseStep 2547265 = 1910449) (by norm_num)
theorem B3396353 : Blo 2263435 3396353 := bstep (se 2 (by rfl) ⟨1273632, by rfl⟩ : syracuseStep 3396353 = 2547265) B2547265
theorem B2264235 : Blo 2263435 2264235 := bstep (se 1 (by rfl) ⟨1698176, by rfl⟩ : syracuseStep 2264235 = 3396353) B3396353
theorem B5731357 : Blo 2263435 5731357 := bbase (se 3 (by rfl) ⟨1074629, by rfl⟩ : syracuseStep 5731357 = 2149259) (by norm_num)
theorem B7641809 : Blo 2263435 7641809 := bstep (se 2 (by rfl) ⟨2865678, by rfl⟩ : syracuseStep 7641809 = 5731357) B5731357
theorem B5094539 : Blo 2263435 5094539 := bstep (se 1 (by rfl) ⟨3820904, by rfl⟩ : syracuseStep 5094539 = 7641809) B7641809
theorem B3396359 : Blo 2263435 3396359 := bstep (se 1 (by rfl) ⟨2547269, by rfl⟩ : syracuseStep 3396359 = 5094539) B5094539
theorem B2264239 : Blo 2263435 2264239 := bstep (se 1 (by rfl) ⟨1698179, by rfl⟩ : syracuseStep 2264239 = 3396359) B3396359
theorem B3396365 : Blo 2263435 3396365 := bbase (se 3 (by rfl) ⟨636818, by rfl⟩ : syracuseStep 3396365 = 1273637) (by norm_num)
theorem B2264243 : Blo 2263435 2264243 := bstep (se 1 (by rfl) ⟨1698182, by rfl⟩ : syracuseStep 2264243 = 3396365) B3396365
theorem B5094557 : Blo 2263435 5094557 := bbase (se 3 (by rfl) ⟨955229, by rfl⟩ : syracuseStep 5094557 = 1910459) (by norm_num)
theorem B3396371 : Blo 2263435 3396371 := bstep (se 1 (by rfl) ⟨2547278, by rfl⟩ : syracuseStep 3396371 = 5094557) B5094557
theorem B2264247 : Blo 2263435 2264247 := bstep (se 1 (by rfl) ⟨1698185, by rfl⟩ : syracuseStep 2264247 = 3396371) B3396371
theorem B3820925 : Blo 2263435 3820925 := bbase (se 3 (by rfl) ⟨716423, by rfl⟩ : syracuseStep 3820925 = 1432847) (by norm_num)
theorem B2547283 : Blo 2263435 2547283 := bstep (se 1 (by rfl) ⟨1910462, by rfl⟩ : syracuseStep 2547283 = 3820925) B3820925
theorem B3396377 : Blo 2263435 3396377 := bstep (se 2 (by rfl) ⟨1273641, by rfl⟩ : syracuseStep 3396377 = 2547283) B2547283
theorem B2264251 : Blo 2263435 2264251 := bstep (se 1 (by rfl) ⟨1698188, by rfl⟩ : syracuseStep 2264251 = 3396377) B3396377
theorem B27541781 : Blo 2263435 27541781 := bbase (se 6 (by rfl) ⟨645510, by rfl⟩ : syracuseStep 27541781 = 1291021) (by norm_num)
theorem B18361187 : Blo 2263435 18361187 := bstep (se 1 (by rfl) ⟨13770890, by rfl⟩ : syracuseStep 18361187 = 27541781) B27541781
theorem B12240791 : Blo 2263435 12240791 := bstep (se 1 (by rfl) ⟨9180593, by rfl⟩ : syracuseStep 12240791 = 18361187) B18361187
theorem B8160527 : Blo 2263435 8160527 := bstep (se 1 (by rfl) ⟨6120395, by rfl⟩ : syracuseStep 8160527 = 12240791) B12240791
theorem B5440351 : Blo 2263435 5440351 := bstep (se 1 (by rfl) ⟨4080263, by rfl⟩ : syracuseStep 5440351 = 8160527) B8160527
theorem B7253801 : Blo 2263435 7253801 := bstep (se 2 (by rfl) ⟨2720175, by rfl⟩ : syracuseStep 7253801 = 5440351) B5440351
theorem B4835867 : Blo 2263435 4835867 := bstep (se 1 (by rfl) ⟨3626900, by rfl⟩ : syracuseStep 4835867 = 7253801) B7253801
theorem B12895645 : Blo 2263435 12895645 := bstep (se 3 (by rfl) ⟨2417933, by rfl⟩ : syracuseStep 12895645 = 4835867) B4835867
theorem B17194193 : Blo 2263435 17194193 := bstep (se 2 (by rfl) ⟨6447822, by rfl⟩ : syracuseStep 17194193 = 12895645) B12895645
theorem B11462795 : Blo 2263435 11462795 := bstep (se 1 (by rfl) ⟨8597096, by rfl⟩ : syracuseStep 11462795 = 17194193) B17194193
theorem B7641863 : Blo 2263435 7641863 := bstep (se 1 (by rfl) ⟨5731397, by rfl⟩ : syracuseStep 7641863 = 11462795) B11462795
theorem B5094575 : Blo 2263435 5094575 := bstep (se 1 (by rfl) ⟨3820931, by rfl⟩ : syracuseStep 5094575 = 7641863) B7641863
theorem B3396383 : Blo 2263435 3396383 := bstep (se 1 (by rfl) ⟨2547287, by rfl⟩ : syracuseStep 3396383 = 5094575) B5094575
theorem B2264255 : Blo 2263435 2264255 := bstep (se 1 (by rfl) ⟨1698191, by rfl⟩ : syracuseStep 2264255 = 3396383) B3396383
theorem B3396389 : Blo 2263435 3396389 := bbase (se 4 (by rfl) ⟨318411, by rfl⟩ : syracuseStep 3396389 = 636823) (by norm_num)
theorem B2264259 : Blo 2263435 2264259 := bstep (se 1 (by rfl) ⟨1698194, by rfl⟩ : syracuseStep 2264259 = 3396389) B3396389
theorem B2865709 : Blo 2263435 2865709 := bbase (se 3 (by rfl) ⟨537320, by rfl⟩ : syracuseStep 2865709 = 1074641) (by norm_num)
theorem B3820945 : Blo 2263435 3820945 := bstep (se 2 (by rfl) ⟨1432854, by rfl⟩ : syracuseStep 3820945 = 2865709) B2865709
theorem B5094593 : Blo 2263435 5094593 := bstep (se 2 (by rfl) ⟨1910472, by rfl⟩ : syracuseStep 5094593 = 3820945) B3820945
theorem B3396395 : Blo 2263435 3396395 := bstep (se 1 (by rfl) ⟨2547296, by rfl⟩ : syracuseStep 3396395 = 5094593) B5094593
theorem B2264263 : Blo 2263435 2264263 := bstep (se 1 (by rfl) ⟨1698197, by rfl⟩ : syracuseStep 2264263 = 3396395) B3396395
theorem B2547301 : Blo 2263435 2547301 := bbase (se 4 (by rfl) ⟨238809, by rfl⟩ : syracuseStep 2547301 = 477619) (by norm_num)
theorem B3396401 : Blo 2263435 3396401 := bstep (se 2 (by rfl) ⟨1273650, by rfl⟩ : syracuseStep 3396401 = 2547301) B2547301
theorem B2264267 : Blo 2263435 2264267 := bstep (se 1 (by rfl) ⟨1698200, by rfl⟩ : syracuseStep 2264267 = 3396401) B3396401
theorem B9180661 : Blo 2263435 9180661 := bbase (se 5 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 9180661 = 860687) (by norm_num)
theorem B12240881 : Blo 2263435 12240881 := bstep (se 2 (by rfl) ⟨4590330, by rfl⟩ : syracuseStep 12240881 = 9180661) B9180661
theorem B8160587 : Blo 2263435 8160587 := bstep (se 1 (by rfl) ⟨6120440, by rfl⟩ : syracuseStep 8160587 = 12240881) B12240881
theorem B5440391 : Blo 2263435 5440391 := bstep (se 1 (by rfl) ⟨4080293, by rfl⟩ : syracuseStep 5440391 = 8160587) B8160587
theorem B3626927 : Blo 2263435 3626927 := bstep (se 1 (by rfl) ⟨2720195, by rfl⟩ : syracuseStep 3626927 = 5440391) B5440391
theorem B2417951 : Blo 2263435 2417951 := bstep (se 1 (by rfl) ⟨1813463, by rfl⟩ : syracuseStep 2417951 = 3626927) B3626927
theorem B6447869 : Blo 2263435 6447869 := bstep (se 3 (by rfl) ⟨1208975, by rfl⟩ : syracuseStep 6447869 = 2417951) B2417951
theorem B4298579 : Blo 2263435 4298579 := bstep (se 1 (by rfl) ⟨3223934, by rfl⟩ : syracuseStep 4298579 = 6447869) B6447869
theorem B2865719 : Blo 2263435 2865719 := bstep (se 1 (by rfl) ⟨2149289, by rfl⟩ : syracuseStep 2865719 = 4298579) B4298579
theorem B7641917 : Blo 2263435 7641917 := bstep (se 3 (by rfl) ⟨1432859, by rfl⟩ : syracuseStep 7641917 = 2865719) B2865719
theorem B5094611 : Blo 2263435 5094611 := bstep (se 1 (by rfl) ⟨3820958, by rfl⟩ : syracuseStep 5094611 = 7641917) B7641917
theorem B3396407 : Blo 2263435 3396407 := bstep (se 1 (by rfl) ⟨2547305, by rfl⟩ : syracuseStep 3396407 = 5094611) B5094611
theorem B2264271 : Blo 2263435 2264271 := bstep (se 1 (by rfl) ⟨1698203, by rfl⟩ : syracuseStep 2264271 = 3396407) B3396407
theorem B3396413 : Blo 2263435 3396413 := bbase (se 3 (by rfl) ⟨636827, by rfl⟩ : syracuseStep 3396413 = 1273655) (by norm_num)
theorem B2264275 : Blo 2263435 2264275 := bstep (se 1 (by rfl) ⟨1698206, by rfl⟩ : syracuseStep 2264275 = 3396413) B3396413
theorem B5094629 : Blo 2263435 5094629 := bbase (se 4 (by rfl) ⟨477621, by rfl⟩ : syracuseStep 5094629 = 955243) (by norm_num)
theorem B3396419 : Blo 2263435 3396419 := bstep (se 1 (by rfl) ⟨2547314, by rfl⟩ : syracuseStep 3396419 = 5094629) B5094629
theorem B2264279 : Blo 2263435 2264279 := bstep (se 1 (by rfl) ⟨1698209, by rfl⟩ : syracuseStep 2264279 = 3396419) B3396419
theorem B5731469 : Blo 2263435 5731469 := bbase (se 3 (by rfl) ⟨1074650, by rfl⟩ : syracuseStep 5731469 = 2149301) (by norm_num)
theorem B3820979 : Blo 2263435 3820979 := bstep (se 1 (by rfl) ⟨2865734, by rfl⟩ : syracuseStep 3820979 = 5731469) B5731469
theorem B2547319 : Blo 2263435 2547319 := bstep (se 1 (by rfl) ⟨1910489, by rfl⟩ : syracuseStep 2547319 = 3820979) B3820979
theorem B3396425 : Blo 2263435 3396425 := bstep (se 2 (by rfl) ⟨1273659, by rfl⟩ : syracuseStep 3396425 = 2547319) B2547319
theorem B2264283 : Blo 2263435 2264283 := bstep (se 1 (by rfl) ⟨1698212, by rfl⟩ : syracuseStep 2264283 = 3396425) B3396425
theorem B3223957 : Blo 2263435 3223957 := bbase (se 6 (by rfl) ⟨75561, by rfl⟩ : syracuseStep 3223957 = 151123) (by norm_num)
theorem B4298609 : Blo 2263435 4298609 := bstep (se 2 (by rfl) ⟨1611978, by rfl⟩ : syracuseStep 4298609 = 3223957) B3223957
theorem B11462957 : Blo 2263435 11462957 := bstep (se 3 (by rfl) ⟨2149304, by rfl⟩ : syracuseStep 11462957 = 4298609) B4298609
theorem B7641971 : Blo 2263435 7641971 := bstep (se 1 (by rfl) ⟨5731478, by rfl⟩ : syracuseStep 7641971 = 11462957) B11462957
theorem B5094647 : Blo 2263435 5094647 := bstep (se 1 (by rfl) ⟨3820985, by rfl⟩ : syracuseStep 5094647 = 7641971) B7641971
theorem B3396431 : Blo 2263435 3396431 := bstep (se 1 (by rfl) ⟨2547323, by rfl⟩ : syracuseStep 3396431 = 5094647) B5094647
theorem B2264287 : Blo 2263435 2264287 := bstep (se 1 (by rfl) ⟨1698215, by rfl⟩ : syracuseStep 2264287 = 3396431) B3396431
theorem B3396437 : Blo 2263435 3396437 := bbase (se 9 (by rfl) ⟨9950, by rfl⟩ : syracuseStep 3396437 = 19901) (by norm_num)
theorem B2264291 : Blo 2263435 2264291 := bstep (se 1 (by rfl) ⟨1698218, by rfl⟩ : syracuseStep 2264291 = 3396437) B3396437
theorem B3626965 : Blo 2263435 3626965 := bbase (se 7 (by rfl) ⟨42503, by rfl⟩ : syracuseStep 3626965 = 85007) (by norm_num)
theorem B4835953 : Blo 2263435 4835953 := bstep (se 2 (by rfl) ⟨1813482, by rfl⟩ : syracuseStep 4835953 = 3626965) B3626965
theorem B6447937 : Blo 2263435 6447937 := bstep (se 2 (by rfl) ⟨2417976, by rfl⟩ : syracuseStep 6447937 = 4835953) B4835953
theorem B8597249 : Blo 2263435 8597249 := bstep (se 2 (by rfl) ⟨3223968, by rfl⟩ : syracuseStep 8597249 = 6447937) B6447937
theorem B5731499 : Blo 2263435 5731499 := bstep (se 1 (by rfl) ⟨4298624, by rfl⟩ : syracuseStep 5731499 = 8597249) B8597249
theorem B3820999 : Blo 2263435 3820999 := bstep (se 1 (by rfl) ⟨2865749, by rfl⟩ : syracuseStep 3820999 = 5731499) B5731499
theorem B5094665 : Blo 2263435 5094665 := bstep (se 2 (by rfl) ⟨1910499, by rfl⟩ : syracuseStep 5094665 = 3820999) B3820999
theorem B3396443 : Blo 2263435 3396443 := bstep (se 1 (by rfl) ⟨2547332, by rfl⟩ : syracuseStep 3396443 = 5094665) B5094665
theorem B2264295 : Blo 2263435 2264295 := bstep (se 1 (by rfl) ⟨1698221, by rfl⟩ : syracuseStep 2264295 = 3396443) B3396443
theorem B2547337 : Blo 2263435 2547337 := bbase (se 2 (by rfl) ⟨955251, by rfl⟩ : syracuseStep 2547337 = 1910503) (by norm_num)
theorem B3396449 : Blo 2263435 3396449 := bstep (se 2 (by rfl) ⟨1273668, by rfl⟩ : syracuseStep 3396449 = 2547337) B2547337
theorem B2264299 : Blo 2263435 2264299 := bstep (se 1 (by rfl) ⟨1698224, by rfl⟩ : syracuseStep 2264299 = 3396449) B3396449
theorem B5234653 : Blo 2263435 5234653 := bbase (se 3 (by rfl) ⟨981497, by rfl⟩ : syracuseStep 5234653 = 1962995) (by norm_num)
theorem B6979537 : Blo 2263435 6979537 := bstep (se 2 (by rfl) ⟨2617326, by rfl⟩ : syracuseStep 6979537 = 5234653) B5234653
theorem B37224197 : Blo 2263435 37224197 := bstep (se 4 (by rfl) ⟨3489768, by rfl⟩ : syracuseStep 37224197 = 6979537) B6979537
theorem B24816131 : Blo 2263435 24816131 := bstep (se 1 (by rfl) ⟨18612098, by rfl⟩ : syracuseStep 24816131 = 37224197) B37224197
theorem B16544087 : Blo 2263435 16544087 := bstep (se 1 (by rfl) ⟨12408065, by rfl⟩ : syracuseStep 16544087 = 24816131) B24816131
theorem B11029391 : Blo 2263435 11029391 := bstep (se 1 (by rfl) ⟨8272043, by rfl⟩ : syracuseStep 11029391 = 16544087) B16544087
theorem B7352927 : Blo 2263435 7352927 := bstep (se 1 (by rfl) ⟨5514695, by rfl⟩ : syracuseStep 7352927 = 11029391) B11029391
theorem B4901951 : Blo 2263435 4901951 := bstep (se 1 (by rfl) ⟨3676463, by rfl⟩ : syracuseStep 4901951 = 7352927) B7352927
theorem B3267967 : Blo 2263435 3267967 := bstep (se 1 (by rfl) ⟨2450975, by rfl⟩ : syracuseStep 3267967 = 4901951) B4901951
theorem B4357289 : Blo 2263435 4357289 := bstep (se 2 (by rfl) ⟨1633983, by rfl⟩ : syracuseStep 4357289 = 3267967) B3267967
theorem B2904859 : Blo 2263435 2904859 := bstep (se 1 (by rfl) ⟨2178644, by rfl⟩ : syracuseStep 2904859 = 4357289) B4357289
theorem B3873145 : Blo 2263435 3873145 := bstep (se 2 (by rfl) ⟨1452429, by rfl⟩ : syracuseStep 3873145 = 2904859) B2904859
theorem B5164193 : Blo 2263435 5164193 := bstep (se 2 (by rfl) ⟨1936572, by rfl⟩ : syracuseStep 5164193 = 3873145) B3873145
theorem B13771181 : Blo 2263435 13771181 := bstep (se 3 (by rfl) ⟨2582096, by rfl⟩ : syracuseStep 13771181 = 5164193) B5164193
theorem B9180787 : Blo 2263435 9180787 := bstep (se 1 (by rfl) ⟨6885590, by rfl⟩ : syracuseStep 9180787 = 13771181) B13771181
theorem B12241049 : Blo 2263435 12241049 := bstep (se 2 (by rfl) ⟨4590393, by rfl⟩ : syracuseStep 12241049 = 9180787) B9180787
theorem B32642797 : Blo 2263435 32642797 := bstep (se 3 (by rfl) ⟨6120524, by rfl⟩ : syracuseStep 32642797 = 12241049) B12241049
theorem B43523729 : Blo 2263435 43523729 := bstep (se 2 (by rfl) ⟨16321398, by rfl⟩ : syracuseStep 43523729 = 32642797) B32642797
theorem B29015819 : Blo 2263435 29015819 := bstep (se 1 (by rfl) ⟨21761864, by rfl⟩ : syracuseStep 29015819 = 43523729) B43523729
theorem B19343879 : Blo 2263435 19343879 := bstep (se 1 (by rfl) ⟨14507909, by rfl⟩ : syracuseStep 19343879 = 29015819) B29015819
theorem B12895919 : Blo 2263435 12895919 := bstep (se 1 (by rfl) ⟨9671939, by rfl⟩ : syracuseStep 12895919 = 19343879) B19343879
theorem B8597279 : Blo 2263435 8597279 := bstep (se 1 (by rfl) ⟨6447959, by rfl⟩ : syracuseStep 8597279 = 12895919) B12895919
theorem B5731519 : Blo 2263435 5731519 := bstep (se 1 (by rfl) ⟨4298639, by rfl⟩ : syracuseStep 5731519 = 8597279) B8597279
theorem B7642025 : Blo 2263435 7642025 := bstep (se 2 (by rfl) ⟨2865759, by rfl⟩ : syracuseStep 7642025 = 5731519) B5731519
theorem B5094683 : Blo 2263435 5094683 := bstep (se 1 (by rfl) ⟨3821012, by rfl⟩ : syracuseStep 5094683 = 7642025) B7642025
theorem B3396455 : Blo 2263435 3396455 := bstep (se 1 (by rfl) ⟨2547341, by rfl⟩ : syracuseStep 3396455 = 5094683) B5094683
theorem B2264303 : Blo 2263435 2264303 := bstep (se 1 (by rfl) ⟨1698227, by rfl⟩ : syracuseStep 2264303 = 3396455) B3396455
theorem B3396461 : Blo 2263435 3396461 := bbase (se 3 (by rfl) ⟨636836, by rfl⟩ : syracuseStep 3396461 = 1273673) (by norm_num)
theorem B2264307 : Blo 2263435 2264307 := bstep (se 1 (by rfl) ⟨1698230, by rfl⟩ : syracuseStep 2264307 = 3396461) B3396461
theorem B5094701 : Blo 2263435 5094701 := bbase (se 3 (by rfl) ⟨955256, by rfl⟩ : syracuseStep 5094701 = 1910513) (by norm_num)
theorem B3396467 : Blo 2263435 3396467 := bstep (se 1 (by rfl) ⟨2547350, by rfl⟩ : syracuseStep 3396467 = 5094701) B5094701
theorem B2264311 : Blo 2263435 2264311 := bstep (se 1 (by rfl) ⟨1698233, by rfl⟩ : syracuseStep 2264311 = 3396467) B3396467
theorem B5514725 : Blo 2263435 5514725 := bbase (se 4 (by rfl) ⟨517005, by rfl⟩ : syracuseStep 5514725 = 1034011) (by norm_num)
theorem B3676483 : Blo 2263435 3676483 := bstep (se 1 (by rfl) ⟨2757362, by rfl⟩ : syracuseStep 3676483 = 5514725) B5514725
theorem B4901977 : Blo 2263435 4901977 := bstep (se 2 (by rfl) ⟨1838241, by rfl⟩ : syracuseStep 4901977 = 3676483) B3676483
theorem B26143877 : Blo 2263435 26143877 := bstep (se 4 (by rfl) ⟨2450988, by rfl⟩ : syracuseStep 26143877 = 4901977) B4901977
theorem B17429251 : Blo 2263435 17429251 := bstep (se 1 (by rfl) ⟨13071938, by rfl⟩ : syracuseStep 17429251 = 26143877) B26143877
theorem B23239001 : Blo 2263435 23239001 := bstep (se 2 (by rfl) ⟨8714625, by rfl⟩ : syracuseStep 23239001 = 17429251) B17429251
theorem B15492667 : Blo 2263435 15492667 := bstep (se 1 (by rfl) ⟨11619500, by rfl⟩ : syracuseStep 15492667 = 23239001) B23239001
theorem B20656889 : Blo 2263435 20656889 := bstep (se 2 (by rfl) ⟨7746333, by rfl⟩ : syracuseStep 20656889 = 15492667) B15492667
theorem B13771259 : Blo 2263435 13771259 := bstep (se 1 (by rfl) ⟨10328444, by rfl⟩ : syracuseStep 13771259 = 20656889) B20656889
theorem B9180839 : Blo 2263435 9180839 := bstep (se 1 (by rfl) ⟨6885629, by rfl⟩ : syracuseStep 9180839 = 13771259) B13771259
theorem B6120559 : Blo 2263435 6120559 := bstep (se 1 (by rfl) ⟨4590419, by rfl⟩ : syracuseStep 6120559 = 9180839) B9180839
theorem B8160745 : Blo 2263435 8160745 := bstep (se 2 (by rfl) ⟨3060279, by rfl⟩ : syracuseStep 8160745 = 6120559) B6120559
theorem B10880993 : Blo 2263435 10880993 := bstep (se 2 (by rfl) ⟨4080372, by rfl⟩ : syracuseStep 10880993 = 8160745) B8160745
theorem B7253995 : Blo 2263435 7253995 := bstep (se 1 (by rfl) ⟨5440496, by rfl⟩ : syracuseStep 7253995 = 10880993) B10880993
theorem B9671993 : Blo 2263435 9671993 := bstep (se 2 (by rfl) ⟨3626997, by rfl⟩ : syracuseStep 9671993 = 7253995) B7253995
theorem B6447995 : Blo 2263435 6447995 := bstep (se 1 (by rfl) ⟨4835996, by rfl⟩ : syracuseStep 6447995 = 9671993) B9671993
theorem B4298663 : Blo 2263435 4298663 := bstep (se 1 (by rfl) ⟨3223997, by rfl⟩ : syracuseStep 4298663 = 6447995) B6447995
theorem B2865775 : Blo 2263435 2865775 := bstep (se 1 (by rfl) ⟨2149331, by rfl⟩ : syracuseStep 2865775 = 4298663) B4298663
theorem B3821033 : Blo 2263435 3821033 := bstep (se 2 (by rfl) ⟨1432887, by rfl⟩ : syracuseStep 3821033 = 2865775) B2865775
theorem B2547355 : Blo 2263435 2547355 := bstep (se 1 (by rfl) ⟨1910516, by rfl⟩ : syracuseStep 2547355 = 3821033) B3821033
theorem B3396473 : Blo 2263435 3396473 := bstep (se 2 (by rfl) ⟨1273677, by rfl⟩ : syracuseStep 3396473 = 2547355) B2547355
theorem B2264315 : Blo 2263435 2264315 := bstep (se 1 (by rfl) ⟨1698236, by rfl⟩ : syracuseStep 2264315 = 3396473) B3396473
theorem B6715541 : Blo 2263435 6715541 := bbase (se 6 (by rfl) ⟨157395, by rfl⟩ : syracuseStep 6715541 = 314791) (by norm_num)
theorem B4477027 : Blo 2263435 4477027 := bstep (se 1 (by rfl) ⟨3357770, by rfl⟩ : syracuseStep 4477027 = 6715541) B6715541
theorem B5969369 : Blo 2263435 5969369 := bstep (se 2 (by rfl) ⟨2238513, by rfl⟩ : syracuseStep 5969369 = 4477027) B4477027
theorem B3979579 : Blo 2263435 3979579 := bstep (se 1 (by rfl) ⟨2984684, by rfl⟩ : syracuseStep 3979579 = 5969369) B5969369
theorem B5306105 : Blo 2263435 5306105 := bstep (se 2 (by rfl) ⟨1989789, by rfl⟩ : syracuseStep 5306105 = 3979579) B3979579
theorem B14149613 : Blo 2263435 14149613 := bstep (se 3 (by rfl) ⟨2653052, by rfl⟩ : syracuseStep 14149613 = 5306105) B5306105
theorem B9433075 : Blo 2263435 9433075 := bstep (se 1 (by rfl) ⟨7074806, by rfl⟩ : syracuseStep 9433075 = 14149613) B14149613
theorem B12577433 : Blo 2263435 12577433 := bstep (se 2 (by rfl) ⟨4716537, by rfl⟩ : syracuseStep 12577433 = 9433075) B9433075
theorem B134159285 : Blo 2263435 134159285 := bstep (se 5 (by rfl) ⟨6288716, by rfl⟩ : syracuseStep 134159285 = 12577433) B12577433
theorem B357758093 : Blo 2263435 357758093 := bstep (se 3 (by rfl) ⟨67079642, by rfl⟩ : syracuseStep 357758093 = 134159285) B134159285
theorem B954021581 : Blo 2263435 954021581 := bstep (se 3 (by rfl) ⟨178879046, by rfl⟩ : syracuseStep 954021581 = 357758093) B357758093
theorem B636014387 : Blo 2263435 636014387 := bstep (se 1 (by rfl) ⟨477010790, by rfl⟩ : syracuseStep 636014387 = 954021581) B954021581
theorem B1696038365 : Blo 2263435 1696038365 := bstep (se 3 (by rfl) ⟨318007193, by rfl⟩ : syracuseStep 1696038365 = 636014387) B636014387
theorem B1130692243 : Blo 2263435 1130692243 := bstep (se 1 (by rfl) ⟨848019182, by rfl⟩ : syracuseStep 1130692243 = 1696038365) B1696038365
theorem B1507589657 : Blo 2263435 1507589657 := bstep (se 2 (by rfl) ⟨565346121, by rfl⟩ : syracuseStep 1507589657 = 1130692243) B1130692243
theorem B1005059771 : Blo 2263435 1005059771 := bstep (se 1 (by rfl) ⟨753794828, by rfl⟩ : syracuseStep 1005059771 = 1507589657) B1507589657
theorem B670039847 : Blo 2263435 670039847 := bstep (se 1 (by rfl) ⟨502529885, by rfl⟩ : syracuseStep 670039847 = 1005059771) B1005059771
theorem B446693231 : Blo 2263435 446693231 := bstep (se 1 (by rfl) ⟨335019923, by rfl⟩ : syracuseStep 446693231 = 670039847) B670039847
theorem B297795487 : Blo 2263435 297795487 := bstep (se 1 (by rfl) ⟨223346615, by rfl⟩ : syracuseStep 297795487 = 446693231) B446693231
theorem B397060649 : Blo 2263435 397060649 := bstep (se 2 (by rfl) ⟨148897743, by rfl⟩ : syracuseStep 397060649 = 297795487) B297795487
theorem B264707099 : Blo 2263435 264707099 := bstep (se 1 (by rfl) ⟨198530324, by rfl⟩ : syracuseStep 264707099 = 397060649) B397060649
theorem B176471399 : Blo 2263435 176471399 := bstep (se 1 (by rfl) ⟨132353549, by rfl⟩ : syracuseStep 176471399 = 264707099) B264707099
theorem B117647599 : Blo 2263435 117647599 := bstep (se 1 (by rfl) ⟨88235699, by rfl⟩ : syracuseStep 117647599 = 176471399) B176471399
theorem B156863465 : Blo 2263435 156863465 := bstep (se 2 (by rfl) ⟨58823799, by rfl⟩ : syracuseStep 156863465 = 117647599) B117647599
theorem B104575643 : Blo 2263435 104575643 := bstep (se 1 (by rfl) ⟨78431732, by rfl⟩ : syracuseStep 104575643 = 156863465) B156863465
theorem B69717095 : Blo 2263435 69717095 := bstep (se 1 (by rfl) ⟨52287821, by rfl⟩ : syracuseStep 69717095 = 104575643) B104575643
theorem B46478063 : Blo 2263435 46478063 := bstep (se 1 (by rfl) ⟨34858547, by rfl⟩ : syracuseStep 46478063 = 69717095) B69717095
theorem B30985375 : Blo 2263435 30985375 := bstep (se 1 (by rfl) ⟨23239031, by rfl⟩ : syracuseStep 30985375 = 46478063) B46478063
theorem B41313833 : Blo 2263435 41313833 := bstep (se 2 (by rfl) ⟨15492687, by rfl⟩ : syracuseStep 41313833 = 30985375) B30985375
theorem B27542555 : Blo 2263435 27542555 := bstep (se 1 (by rfl) ⟨20656916, by rfl⟩ : syracuseStep 27542555 = 41313833) B41313833
theorem B18361703 : Blo 2263435 18361703 := bstep (se 1 (by rfl) ⟨13771277, by rfl⟩ : syracuseStep 18361703 = 27542555) B27542555
theorem B12241135 : Blo 2263435 12241135 := bstep (se 1 (by rfl) ⟨9180851, by rfl⟩ : syracuseStep 12241135 = 18361703) B18361703
theorem B16321513 : Blo 2263435 16321513 := bstep (se 2 (by rfl) ⟨6120567, by rfl⟩ : syracuseStep 16321513 = 12241135) B12241135
theorem B21762017 : Blo 2263435 21762017 := bstep (se 2 (by rfl) ⟨8160756, by rfl⟩ : syracuseStep 21762017 = 16321513) B16321513
theorem B14508011 : Blo 2263435 14508011 := bstep (se 1 (by rfl) ⟨10881008, by rfl⟩ : syracuseStep 14508011 = 21762017) B21762017
theorem B38688029 : Blo 2263435 38688029 := bstep (se 3 (by rfl) ⟨7254005, by rfl⟩ : syracuseStep 38688029 = 14508011) B14508011
theorem B25792019 : Blo 2263435 25792019 := bstep (se 1 (by rfl) ⟨19344014, by rfl⟩ : syracuseStep 25792019 = 38688029) B38688029
theorem B17194679 : Blo 2263435 17194679 := bstep (se 1 (by rfl) ⟨12896009, by rfl⟩ : syracuseStep 17194679 = 25792019) B25792019
theorem B11463119 : Blo 2263435 11463119 := bstep (se 1 (by rfl) ⟨8597339, by rfl⟩ : syracuseStep 11463119 = 17194679) B17194679
theorem B7642079 : Blo 2263435 7642079 := bstep (se 1 (by rfl) ⟨5731559, by rfl⟩ : syracuseStep 7642079 = 11463119) B11463119
theorem B5094719 : Blo 2263435 5094719 := bstep (se 1 (by rfl) ⟨3821039, by rfl⟩ : syracuseStep 5094719 = 7642079) B7642079
theorem B3396479 : Blo 2263435 3396479 := bstep (se 1 (by rfl) ⟨2547359, by rfl⟩ : syracuseStep 3396479 = 5094719) B5094719
theorem B2264319 : Blo 2263435 2264319 := bstep (se 1 (by rfl) ⟨1698239, by rfl⟩ : syracuseStep 2264319 = 3396479) B3396479
theorem B3396485 : Blo 2263435 3396485 := bbase (se 4 (by rfl) ⟨318420, by rfl⟩ : syracuseStep 3396485 = 636841) (by norm_num)
theorem B2264323 : Blo 2263435 2264323 := bstep (se 1 (by rfl) ⟨1698242, by rfl⟩ : syracuseStep 2264323 = 3396485) B3396485
theorem B3821053 : Blo 2263435 3821053 := bbase (se 3 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 3821053 = 1432895) (by norm_num)
theorem B5094737 : Blo 2263435 5094737 := bstep (se 2 (by rfl) ⟨1910526, by rfl⟩ : syracuseStep 5094737 = 3821053) B3821053
theorem B3396491 : Blo 2263435 3396491 := bstep (se 1 (by rfl) ⟨2547368, by rfl⟩ : syracuseStep 3396491 = 5094737) B5094737
theorem B2264327 : Blo 2263435 2264327 := bstep (se 1 (by rfl) ⟨1698245, by rfl⟩ : syracuseStep 2264327 = 3396491) B3396491
theorem B2547373 : Blo 2263435 2547373 := bbase (se 3 (by rfl) ⟨477632, by rfl⟩ : syracuseStep 2547373 = 955265) (by norm_num)
theorem B3396497 : Blo 2263435 3396497 := bstep (se 2 (by rfl) ⟨1273686, by rfl⟩ : syracuseStep 3396497 = 2547373) B2547373
theorem B2264331 : Blo 2263435 2264331 := bstep (se 1 (by rfl) ⟨1698248, by rfl⟩ : syracuseStep 2264331 = 3396497) B3396497
theorem B7642133 : Blo 2263435 7642133 := bbase (se 6 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 7642133 = 358225) (by norm_num)
theorem B5094755 : Blo 2263435 5094755 := bstep (se 1 (by rfl) ⟨3821066, by rfl⟩ : syracuseStep 5094755 = 7642133) B7642133
theorem B3396503 : Blo 2263435 3396503 := bstep (se 1 (by rfl) ⟨2547377, by rfl⟩ : syracuseStep 3396503 = 5094755) B5094755
theorem B2264335 : Blo 2263435 2264335 := bstep (se 1 (by rfl) ⟨1698251, by rfl⟩ : syracuseStep 2264335 = 3396503) B3396503
theorem B3396509 : Blo 2263435 3396509 := bbase (se 3 (by rfl) ⟨636845, by rfl⟩ : syracuseStep 3396509 = 1273691) (by norm_num)
theorem B2264339 : Blo 2263435 2264339 := bstep (se 1 (by rfl) ⟨1698254, by rfl⟩ : syracuseStep 2264339 = 3396509) B3396509
theorem B5094773 : Blo 2263435 5094773 := bbase (se 5 (by rfl) ⟨238817, by rfl⟩ : syracuseStep 5094773 = 477635) (by norm_num)
theorem B3396515 : Blo 2263435 3396515 := bstep (se 1 (by rfl) ⟨2547386, by rfl⟩ : syracuseStep 3396515 = 5094773) B5094773
theorem B2264343 : Blo 2263435 2264343 := bstep (se 1 (by rfl) ⟨1698257, by rfl⟩ : syracuseStep 2264343 = 3396515) B3396515
theorem B16544405 : Blo 2263435 16544405 := bbase (se 6 (by rfl) ⟨387759, by rfl⟩ : syracuseStep 16544405 = 775519) (by norm_num)
theorem B11029603 : Blo 2263435 11029603 := bstep (se 1 (by rfl) ⟨8272202, by rfl⟩ : syracuseStep 11029603 = 16544405) B16544405
theorem B14706137 : Blo 2263435 14706137 := bstep (se 2 (by rfl) ⟨5514801, by rfl⟩ : syracuseStep 14706137 = 11029603) B11029603
theorem B9804091 : Blo 2263435 9804091 := bstep (se 1 (by rfl) ⟨7353068, by rfl⟩ : syracuseStep 9804091 = 14706137) B14706137
theorem B13072121 : Blo 2263435 13072121 := bstep (se 2 (by rfl) ⟨4902045, by rfl⟩ : syracuseStep 13072121 = 9804091) B9804091
theorem B8714747 : Blo 2263435 8714747 := bstep (se 1 (by rfl) ⟨6536060, by rfl⟩ : syracuseStep 8714747 = 13072121) B13072121
theorem B23239325 : Blo 2263435 23239325 := bstep (se 3 (by rfl) ⟨4357373, by rfl⟩ : syracuseStep 23239325 = 8714747) B8714747
theorem B15492883 : Blo 2263435 15492883 := bstep (se 1 (by rfl) ⟨11619662, by rfl⟩ : syracuseStep 15492883 = 23239325) B23239325
theorem B20657177 : Blo 2263435 20657177 := bstep (se 2 (by rfl) ⟨7746441, by rfl⟩ : syracuseStep 20657177 = 15492883) B15492883
theorem B13771451 : Blo 2263435 13771451 := bstep (se 1 (by rfl) ⟨10328588, by rfl⟩ : syracuseStep 13771451 = 20657177) B20657177
theorem B9180967 : Blo 2263435 9180967 := bstep (se 1 (by rfl) ⟨6885725, by rfl⟩ : syracuseStep 9180967 = 13771451) B13771451
theorem B12241289 : Blo 2263435 12241289 := bstep (se 2 (by rfl) ⟨4590483, by rfl⟩ : syracuseStep 12241289 = 9180967) B9180967
theorem B8160859 : Blo 2263435 8160859 := bstep (se 1 (by rfl) ⟨6120644, by rfl⟩ : syracuseStep 8160859 = 12241289) B12241289
theorem B10881145 : Blo 2263435 10881145 := bstep (se 2 (by rfl) ⟨4080429, by rfl⟩ : syracuseStep 10881145 = 8160859) B8160859
theorem B14508193 : Blo 2263435 14508193 := bstep (se 2 (by rfl) ⟨5440572, by rfl⟩ : syracuseStep 14508193 = 10881145) B10881145
theorem B19344257 : Blo 2263435 19344257 := bstep (se 2 (by rfl) ⟨7254096, by rfl⟩ : syracuseStep 19344257 = 14508193) B14508193
theorem B12896171 : Blo 2263435 12896171 := bstep (se 1 (by rfl) ⟨9672128, by rfl⟩ : syracuseStep 12896171 = 19344257) B19344257
theorem B8597447 : Blo 2263435 8597447 := bstep (se 1 (by rfl) ⟨6448085, by rfl⟩ : syracuseStep 8597447 = 12896171) B12896171
theorem B5731631 : Blo 2263435 5731631 := bstep (se 1 (by rfl) ⟨4298723, by rfl⟩ : syracuseStep 5731631 = 8597447) B8597447
theorem B3821087 : Blo 2263435 3821087 := bstep (se 1 (by rfl) ⟨2865815, by rfl⟩ : syracuseStep 3821087 = 5731631) B5731631
theorem B2547391 : Blo 2263435 2547391 := bstep (se 1 (by rfl) ⟨1910543, by rfl⟩ : syracuseStep 2547391 = 3821087) B3821087
theorem B3396521 : Blo 2263435 3396521 := bstep (se 2 (by rfl) ⟨1273695, by rfl⟩ : syracuseStep 3396521 = 2547391) B2547391
theorem B2264347 : Blo 2263435 2264347 := bstep (se 1 (by rfl) ⟨1698260, by rfl⟩ : syracuseStep 2264347 = 3396521) B3396521
theorem B8597461 : Blo 2263435 8597461 := bbase (se 7 (by rfl) ⟨100751, by rfl⟩ : syracuseStep 8597461 = 201503) (by norm_num)
theorem B11463281 : Blo 2263435 11463281 := bstep (se 2 (by rfl) ⟨4298730, by rfl⟩ : syracuseStep 11463281 = 8597461) B8597461
theorem B7642187 : Blo 2263435 7642187 := bstep (se 1 (by rfl) ⟨5731640, by rfl⟩ : syracuseStep 7642187 = 11463281) B11463281
theorem B5094791 : Blo 2263435 5094791 := bstep (se 1 (by rfl) ⟨3821093, by rfl⟩ : syracuseStep 5094791 = 7642187) B7642187
theorem B3396527 : Blo 2263435 3396527 := bstep (se 1 (by rfl) ⟨2547395, by rfl⟩ : syracuseStep 3396527 = 5094791) B5094791
theorem B2264351 : Blo 2263435 2264351 := bstep (se 1 (by rfl) ⟨1698263, by rfl⟩ : syracuseStep 2264351 = 3396527) B3396527
theorem B3396533 : Blo 2263435 3396533 := bbase (se 5 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 3396533 = 318425) (by norm_num)
theorem B2264355 : Blo 2263435 2264355 := bstep (se 1 (by rfl) ⟨1698266, by rfl⟩ : syracuseStep 2264355 = 3396533) B3396533
theorem B5731661 : Blo 2263435 5731661 := bbase (se 3 (by rfl) ⟨1074686, by rfl⟩ : syracuseStep 5731661 = 2149373) (by norm_num)
theorem B3821107 : Blo 2263435 3821107 := bstep (se 1 (by rfl) ⟨2865830, by rfl⟩ : syracuseStep 3821107 = 5731661) B5731661
theorem B5094809 : Blo 2263435 5094809 := bstep (se 2 (by rfl) ⟨1910553, by rfl⟩ : syracuseStep 5094809 = 3821107) B3821107
theorem B3396539 : Blo 2263435 3396539 := bstep (se 1 (by rfl) ⟨2547404, by rfl⟩ : syracuseStep 3396539 = 5094809) B5094809
theorem B2264359 : Blo 2263435 2264359 := bstep (se 1 (by rfl) ⟨1698269, by rfl⟩ : syracuseStep 2264359 = 3396539) B3396539
theorem B2547409 : Blo 2263435 2547409 := bbase (se 2 (by rfl) ⟨955278, by rfl⟩ : syracuseStep 2547409 = 1910557) (by norm_num)
theorem B3396545 : Blo 2263435 3396545 := bstep (se 2 (by rfl) ⟨1273704, by rfl⟩ : syracuseStep 3396545 = 2547409) B2547409
theorem B2264363 : Blo 2263435 2264363 := bstep (se 1 (by rfl) ⟨1698272, by rfl⟩ : syracuseStep 2264363 = 3396545) B3396545
theorem B5440621 : Blo 2263435 5440621 := bbase (se 3 (by rfl) ⟨1020116, by rfl⟩ : syracuseStep 5440621 = 2040233) (by norm_num)
theorem B7254161 : Blo 2263435 7254161 := bstep (se 2 (by rfl) ⟨2720310, by rfl⟩ : syracuseStep 7254161 = 5440621) B5440621
theorem B4836107 : Blo 2263435 4836107 := bstep (se 1 (by rfl) ⟨3627080, by rfl⟩ : syracuseStep 4836107 = 7254161) B7254161
theorem B3224071 : Blo 2263435 3224071 := bstep (se 1 (by rfl) ⟨2418053, by rfl⟩ : syracuseStep 3224071 = 4836107) B4836107
theorem B4298761 : Blo 2263435 4298761 := bstep (se 2 (by rfl) ⟨1612035, by rfl⟩ : syracuseStep 4298761 = 3224071) B3224071
theorem B5731681 : Blo 2263435 5731681 := bstep (se 2 (by rfl) ⟨2149380, by rfl⟩ : syracuseStep 5731681 = 4298761) B4298761
theorem B7642241 : Blo 2263435 7642241 := bstep (se 2 (by rfl) ⟨2865840, by rfl⟩ : syracuseStep 7642241 = 5731681) B5731681
theorem B5094827 : Blo 2263435 5094827 := bstep (se 1 (by rfl) ⟨3821120, by rfl⟩ : syracuseStep 5094827 = 7642241) B7642241
theorem B3396551 : Blo 2263435 3396551 := bstep (se 1 (by rfl) ⟨2547413, by rfl⟩ : syracuseStep 3396551 = 5094827) B5094827
theorem B2264367 : Blo 2263435 2264367 := bstep (se 1 (by rfl) ⟨1698275, by rfl⟩ : syracuseStep 2264367 = 3396551) B3396551
theorem B3396557 : Blo 2263435 3396557 := bbase (se 3 (by rfl) ⟨636854, by rfl⟩ : syracuseStep 3396557 = 1273709) (by norm_num)
theorem B2264371 : Blo 2263435 2264371 := bstep (se 1 (by rfl) ⟨1698278, by rfl⟩ : syracuseStep 2264371 = 3396557) B3396557
theorem B5094845 : Blo 2263435 5094845 := bbase (se 3 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 5094845 = 1910567) (by norm_num)
theorem B3396563 : Blo 2263435 3396563 := bstep (se 1 (by rfl) ⟨2547422, by rfl⟩ : syracuseStep 3396563 = 5094845) B5094845
theorem B2264375 : Blo 2263435 2264375 := bstep (se 1 (by rfl) ⟨1698281, by rfl⟩ : syracuseStep 2264375 = 3396563) B3396563
theorem B3821141 : Blo 2263435 3821141 := bbase (se 8 (by rfl) ⟨22389, by rfl⟩ : syracuseStep 3821141 = 44779) (by norm_num)
theorem B2547427 : Blo 2263435 2547427 := bstep (se 1 (by rfl) ⟨1910570, by rfl⟩ : syracuseStep 2547427 = 3821141) B3821141
theorem B3396569 : Blo 2263435 3396569 := bstep (se 2 (by rfl) ⟨1273713, by rfl⟩ : syracuseStep 3396569 = 2547427) B2547427
theorem B2264379 : Blo 2263435 2264379 := bstep (se 1 (by rfl) ⟨1698284, by rfl⟩ : syracuseStep 2264379 = 3396569) B3396569
theorem B10881317 : Blo 2263435 10881317 := bbase (se 4 (by rfl) ⟨1020123, by rfl⟩ : syracuseStep 10881317 = 2040247) (by norm_num)
theorem B7254211 : Blo 2263435 7254211 := bstep (se 1 (by rfl) ⟨5440658, by rfl⟩ : syracuseStep 7254211 = 10881317) B10881317
theorem B9672281 : Blo 2263435 9672281 := bstep (se 2 (by rfl) ⟨3627105, by rfl⟩ : syracuseStep 9672281 = 7254211) B7254211
theorem B6448187 : Blo 2263435 6448187 := bstep (se 1 (by rfl) ⟨4836140, by rfl⟩ : syracuseStep 6448187 = 9672281) B9672281
theorem B17195165 : Blo 2263435 17195165 := bstep (se 3 (by rfl) ⟨3224093, by rfl⟩ : syracuseStep 17195165 = 6448187) B6448187
theorem B11463443 : Blo 2263435 11463443 := bstep (se 1 (by rfl) ⟨8597582, by rfl⟩ : syracuseStep 11463443 = 17195165) B17195165
theorem B7642295 : Blo 2263435 7642295 := bstep (se 1 (by rfl) ⟨5731721, by rfl⟩ : syracuseStep 7642295 = 11463443) B11463443
theorem B5094863 : Blo 2263435 5094863 := bstep (se 1 (by rfl) ⟨3821147, by rfl⟩ : syracuseStep 5094863 = 7642295) B7642295
theorem B3396575 : Blo 2263435 3396575 := bstep (se 1 (by rfl) ⟨2547431, by rfl⟩ : syracuseStep 3396575 = 5094863) B5094863
theorem B2264383 : Blo 2263435 2264383 := bstep (se 1 (by rfl) ⟨1698287, by rfl⟩ : syracuseStep 2264383 = 3396575) B3396575
theorem B3396581 : Blo 2263435 3396581 := bbase (se 4 (by rfl) ⟨318429, by rfl⟩ : syracuseStep 3396581 = 636859) (by norm_num)
theorem B2264387 : Blo 2263435 2264387 := bstep (se 1 (by rfl) ⟨1698290, by rfl⟩ : syracuseStep 2264387 = 3396581) B3396581
theorem B17466293 : Blo 2263435 17466293 := bbase (se 5 (by rfl) ⟨818732, by rfl⟩ : syracuseStep 17466293 = 1637465) (by norm_num)
theorem B46576781 : Blo 2263435 46576781 := bstep (se 3 (by rfl) ⟨8733146, by rfl⟩ : syracuseStep 46576781 = 17466293) B17466293
theorem B31051187 : Blo 2263435 31051187 := bstep (se 1 (by rfl) ⟨23288390, by rfl⟩ : syracuseStep 31051187 = 46576781) B46576781
theorem B20700791 : Blo 2263435 20700791 := bstep (se 1 (by rfl) ⟨15525593, by rfl⟩ : syracuseStep 20700791 = 31051187) B31051187
theorem B13800527 : Blo 2263435 13800527 := bstep (se 1 (by rfl) ⟨10350395, by rfl⟩ : syracuseStep 13800527 = 20700791) B20700791
theorem B9200351 : Blo 2263435 9200351 := bstep (se 1 (by rfl) ⟨6900263, by rfl⟩ : syracuseStep 9200351 = 13800527) B13800527
theorem B6133567 : Blo 2263435 6133567 := bstep (se 1 (by rfl) ⟨4600175, by rfl⟩ : syracuseStep 6133567 = 9200351) B9200351
theorem B8178089 : Blo 2263435 8178089 := bstep (se 2 (by rfl) ⟨3066783, by rfl⟩ : syracuseStep 8178089 = 6133567) B6133567
theorem B21808237 : Blo 2263435 21808237 := bstep (se 3 (by rfl) ⟨4089044, by rfl⟩ : syracuseStep 21808237 = 8178089) B8178089
theorem B29077649 : Blo 2263435 29077649 := bstep (se 2 (by rfl) ⟨10904118, by rfl⟩ : syracuseStep 29077649 = 21808237) B21808237
theorem B19385099 : Blo 2263435 19385099 := bstep (se 1 (by rfl) ⟨14538824, by rfl⟩ : syracuseStep 19385099 = 29077649) B29077649
theorem B12923399 : Blo 2263435 12923399 := bstep (se 1 (by rfl) ⟨9692549, by rfl⟩ : syracuseStep 12923399 = 19385099) B19385099
theorem B8615599 : Blo 2263435 8615599 := bstep (se 1 (by rfl) ⟨6461699, by rfl⟩ : syracuseStep 8615599 = 12923399) B12923399
theorem B45949861 : Blo 2263435 45949861 := bstep (se 4 (by rfl) ⟨4307799, by rfl⟩ : syracuseStep 45949861 = 8615599) B8615599
theorem B245065925 : Blo 2263435 245065925 := bstep (se 4 (by rfl) ⟨22974930, by rfl⟩ : syracuseStep 245065925 = 45949861) B45949861
theorem B163377283 : Blo 2263435 163377283 := bstep (se 1 (by rfl) ⟨122532962, by rfl⟩ : syracuseStep 163377283 = 245065925) B245065925
theorem B217836377 : Blo 2263435 217836377 := bstep (se 2 (by rfl) ⟨81688641, by rfl⟩ : syracuseStep 217836377 = 163377283) B163377283
theorem B145224251 : Blo 2263435 145224251 := bstep (se 1 (by rfl) ⟨108918188, by rfl⟩ : syracuseStep 145224251 = 217836377) B217836377
theorem B96816167 : Blo 2263435 96816167 := bstep (se 1 (by rfl) ⟨72612125, by rfl⟩ : syracuseStep 96816167 = 145224251) B145224251
theorem B64544111 : Blo 2263435 64544111 := bstep (se 1 (by rfl) ⟨48408083, by rfl⟩ : syracuseStep 64544111 = 96816167) B96816167
theorem B43029407 : Blo 2263435 43029407 := bstep (se 1 (by rfl) ⟨32272055, by rfl⟩ : syracuseStep 43029407 = 64544111) B64544111
theorem B28686271 : Blo 2263435 28686271 := bstep (se 1 (by rfl) ⟨21514703, by rfl⟩ : syracuseStep 28686271 = 43029407) B43029407
theorem B38248361 : Blo 2263435 38248361 := bstep (se 2 (by rfl) ⟨14343135, by rfl⟩ : syracuseStep 38248361 = 28686271) B28686271
theorem B25498907 : Blo 2263435 25498907 := bstep (se 1 (by rfl) ⟨19124180, by rfl⟩ : syracuseStep 25498907 = 38248361) B38248361
theorem B16999271 : Blo 2263435 16999271 := bstep (se 1 (by rfl) ⟨12749453, by rfl⟩ : syracuseStep 16999271 = 25498907) B25498907
theorem B11332847 : Blo 2263435 11332847 := bstep (se 1 (by rfl) ⟨8499635, by rfl⟩ : syracuseStep 11332847 = 16999271) B16999271
theorem B7555231 : Blo 2263435 7555231 := bstep (se 1 (by rfl) ⟨5666423, by rfl⟩ : syracuseStep 7555231 = 11332847) B11332847
theorem B10073641 : Blo 2263435 10073641 := bstep (se 2 (by rfl) ⟨3777615, by rfl⟩ : syracuseStep 10073641 = 7555231) B7555231
theorem B13431521 : Blo 2263435 13431521 := bstep (se 2 (by rfl) ⟨5036820, by rfl⟩ : syracuseStep 13431521 = 10073641) B10073641
theorem B35817389 : Blo 2263435 35817389 := bstep (se 3 (by rfl) ⟨6715760, by rfl⟩ : syracuseStep 35817389 = 13431521) B13431521
theorem B23878259 : Blo 2263435 23878259 := bstep (se 1 (by rfl) ⟨17908694, by rfl⟩ : syracuseStep 23878259 = 35817389) B35817389
theorem B15918839 : Blo 2263435 15918839 := bstep (se 1 (by rfl) ⟨11939129, by rfl⟩ : syracuseStep 15918839 = 23878259) B23878259
theorem B10612559 : Blo 2263435 10612559 := bstep (se 1 (by rfl) ⟨7959419, by rfl⟩ : syracuseStep 10612559 = 15918839) B15918839
theorem B7075039 : Blo 2263435 7075039 := bstep (se 1 (by rfl) ⟨5306279, by rfl⟩ : syracuseStep 7075039 = 10612559) B10612559
theorem B9433385 : Blo 2263435 9433385 := bstep (se 2 (by rfl) ⟨3537519, by rfl⟩ : syracuseStep 9433385 = 7075039) B7075039
theorem B6288923 : Blo 2263435 6288923 := bstep (se 1 (by rfl) ⟨4716692, by rfl⟩ : syracuseStep 6288923 = 9433385) B9433385
theorem B16770461 : Blo 2263435 16770461 := bstep (se 3 (by rfl) ⟨3144461, by rfl⟩ : syracuseStep 16770461 = 6288923) B6288923
theorem B44721229 : Blo 2263435 44721229 := bstep (se 3 (by rfl) ⟨8385230, by rfl⟩ : syracuseStep 44721229 = 16770461) B16770461
theorem B59628305 : Blo 2263435 59628305 := bstep (se 2 (by rfl) ⟨22360614, by rfl⟩ : syracuseStep 59628305 = 44721229) B44721229
theorem B39752203 : Blo 2263435 39752203 := bstep (se 1 (by rfl) ⟨29814152, by rfl⟩ : syracuseStep 39752203 = 59628305) B59628305
theorem B53002937 : Blo 2263435 53002937 := bstep (se 2 (by rfl) ⟨19876101, by rfl⟩ : syracuseStep 53002937 = 39752203) B39752203
theorem B35335291 : Blo 2263435 35335291 := bstep (se 1 (by rfl) ⟨26501468, by rfl⟩ : syracuseStep 35335291 = 53002937) B53002937
theorem B47113721 : Blo 2263435 47113721 := bstep (se 2 (by rfl) ⟨17667645, by rfl⟩ : syracuseStep 47113721 = 35335291) B35335291
theorem B31409147 : Blo 2263435 31409147 := bstep (se 1 (by rfl) ⟨23556860, by rfl⟩ : syracuseStep 31409147 = 47113721) B47113721
theorem B20939431 : Blo 2263435 20939431 := bstep (se 1 (by rfl) ⟨15704573, by rfl⟩ : syracuseStep 20939431 = 31409147) B31409147
theorem B27919241 : Blo 2263435 27919241 := bstep (se 2 (by rfl) ⟨10469715, by rfl⟩ : syracuseStep 27919241 = 20939431) B20939431
theorem B18612827 : Blo 2263435 18612827 := bstep (se 1 (by rfl) ⟨13959620, by rfl⟩ : syracuseStep 18612827 = 27919241) B27919241
theorem B12408551 : Blo 2263435 12408551 := bstep (se 1 (by rfl) ⟨9306413, by rfl⟩ : syracuseStep 12408551 = 18612827) B18612827
theorem B8272367 : Blo 2263435 8272367 := bstep (se 1 (by rfl) ⟨6204275, by rfl⟩ : syracuseStep 8272367 = 12408551) B12408551
theorem B5514911 : Blo 2263435 5514911 := bstep (se 1 (by rfl) ⟨4136183, by rfl⟩ : syracuseStep 5514911 = 8272367) B8272367
theorem B3676607 : Blo 2263435 3676607 := bstep (se 1 (by rfl) ⟨2757455, by rfl⟩ : syracuseStep 3676607 = 5514911) B5514911
theorem B2451071 : Blo 2263435 2451071 := bstep (se 1 (by rfl) ⟨1838303, by rfl⟩ : syracuseStep 2451071 = 3676607) B3676607
theorem B6536189 : Blo 2263435 6536189 := bstep (se 3 (by rfl) ⟨1225535, by rfl⟩ : syracuseStep 6536189 = 2451071) B2451071
theorem B4357459 : Blo 2263435 4357459 := bstep (se 1 (by rfl) ⟨3268094, by rfl⟩ : syracuseStep 4357459 = 6536189) B6536189
theorem B23239781 : Blo 2263435 23239781 := bstep (se 4 (by rfl) ⟨2178729, by rfl⟩ : syracuseStep 23239781 = 4357459) B4357459
theorem B15493187 : Blo 2263435 15493187 := bstep (se 1 (by rfl) ⟨11619890, by rfl⟩ : syracuseStep 15493187 = 23239781) B23239781
theorem B10328791 : Blo 2263435 10328791 := bstep (se 1 (by rfl) ⟨7746593, by rfl⟩ : syracuseStep 10328791 = 15493187) B15493187
theorem B13771721 : Blo 2263435 13771721 := bstep (se 2 (by rfl) ⟨5164395, by rfl⟩ : syracuseStep 13771721 = 10328791) B10328791
theorem B9181147 : Blo 2263435 9181147 := bstep (se 1 (by rfl) ⟨6885860, by rfl⟩ : syracuseStep 9181147 = 13771721) B13771721
theorem B12241529 : Blo 2263435 12241529 := bstep (se 2 (by rfl) ⟨4590573, by rfl⟩ : syracuseStep 12241529 = 9181147) B9181147
theorem B8161019 : Blo 2263435 8161019 := bstep (se 1 (by rfl) ⟨6120764, by rfl⟩ : syracuseStep 8161019 = 12241529) B12241529
theorem B5440679 : Blo 2263435 5440679 := bstep (se 1 (by rfl) ⟨4080509, by rfl⟩ : syracuseStep 5440679 = 8161019) B8161019
theorem B3627119 : Blo 2263435 3627119 := bstep (se 1 (by rfl) ⟨2720339, by rfl⟩ : syracuseStep 3627119 = 5440679) B5440679
theorem B9672317 : Blo 2263435 9672317 := bstep (se 3 (by rfl) ⟨1813559, by rfl⟩ : syracuseStep 9672317 = 3627119) B3627119
theorem B6448211 : Blo 2263435 6448211 := bstep (se 1 (by rfl) ⟨4836158, by rfl⟩ : syracuseStep 6448211 = 9672317) B9672317
theorem B4298807 : Blo 2263435 4298807 := bstep (se 1 (by rfl) ⟨3224105, by rfl⟩ : syracuseStep 4298807 = 6448211) B6448211
theorem B2865871 : Blo 2263435 2865871 := bstep (se 1 (by rfl) ⟨2149403, by rfl⟩ : syracuseStep 2865871 = 4298807) B4298807
theorem B3821161 : Blo 2263435 3821161 := bstep (se 2 (by rfl) ⟨1432935, by rfl⟩ : syracuseStep 3821161 = 2865871) B2865871
theorem B5094881 : Blo 2263435 5094881 := bstep (se 2 (by rfl) ⟨1910580, by rfl⟩ : syracuseStep 5094881 = 3821161) B3821161
theorem B3396587 : Blo 2263435 3396587 := bstep (se 1 (by rfl) ⟨2547440, by rfl⟩ : syracuseStep 3396587 = 5094881) B5094881
theorem B2264391 : Blo 2263435 2264391 := bstep (se 1 (by rfl) ⟨1698293, by rfl⟩ : syracuseStep 2264391 = 3396587) B3396587
theorem B2547445 : Blo 2263435 2547445 := bbase (se 5 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 2547445 = 238823) (by norm_num)
theorem B3396593 : Blo 2263435 3396593 := bstep (se 2 (by rfl) ⟨1273722, by rfl⟩ : syracuseStep 3396593 = 2547445) B2547445
theorem B2264395 : Blo 2263435 2264395 := bstep (se 1 (by rfl) ⟨1698296, by rfl⟩ : syracuseStep 2264395 = 3396593) B3396593
theorem B2865881 : Blo 2263435 2865881 := bbase (se 2 (by rfl) ⟨1074705, by rfl⟩ : syracuseStep 2865881 = 2149411) (by norm_num)
theorem B7642349 : Blo 2263435 7642349 := bstep (se 3 (by rfl) ⟨1432940, by rfl⟩ : syracuseStep 7642349 = 2865881) B2865881
theorem B5094899 : Blo 2263435 5094899 := bstep (se 1 (by rfl) ⟨3821174, by rfl⟩ : syracuseStep 5094899 = 7642349) B7642349
theorem B3396599 : Blo 2263435 3396599 := bstep (se 1 (by rfl) ⟨2547449, by rfl⟩ : syracuseStep 3396599 = 5094899) B5094899
theorem B2264399 : Blo 2263435 2264399 := bstep (se 1 (by rfl) ⟨1698299, by rfl⟩ : syracuseStep 2264399 = 3396599) B3396599
theorem B3396605 : Blo 2263435 3396605 := bbase (se 3 (by rfl) ⟨636863, by rfl⟩ : syracuseStep 3396605 = 1273727) (by norm_num)
theorem B2264403 : Blo 2263435 2264403 := bstep (se 1 (by rfl) ⟨1698302, by rfl⟩ : syracuseStep 2264403 = 3396605) B3396605
theorem B5094917 : Blo 2263435 5094917 := bbase (se 4 (by rfl) ⟨477648, by rfl⟩ : syracuseStep 5094917 = 955297) (by norm_num)
theorem B3396611 : Blo 2263435 3396611 := bstep (se 1 (by rfl) ⟨2547458, by rfl⟩ : syracuseStep 3396611 = 5094917) B5094917
theorem B2264407 : Blo 2263435 2264407 := bstep (se 1 (by rfl) ⟨1698305, by rfl⟩ : syracuseStep 2264407 = 3396611) B3396611
theorem B4298845 : Blo 2263435 4298845 := bbase (se 3 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 4298845 = 1612067) (by norm_num)
theorem B5731793 : Blo 2263435 5731793 := bstep (se 2 (by rfl) ⟨2149422, by rfl⟩ : syracuseStep 5731793 = 4298845) B4298845
theorem B3821195 : Blo 2263435 3821195 := bstep (se 1 (by rfl) ⟨2865896, by rfl⟩ : syracuseStep 3821195 = 5731793) B5731793
theorem B2547463 : Blo 2263435 2547463 := bstep (se 1 (by rfl) ⟨1910597, by rfl⟩ : syracuseStep 2547463 = 3821195) B3821195
theorem B3396617 : Blo 2263435 3396617 := bstep (se 2 (by rfl) ⟨1273731, by rfl⟩ : syracuseStep 3396617 = 2547463) B2547463
theorem B2264411 : Blo 2263435 2264411 := bstep (se 1 (by rfl) ⟨1698308, by rfl⟩ : syracuseStep 2264411 = 3396617) B3396617
theorem B11463605 : Blo 2263435 11463605 := bbase (se 5 (by rfl) ⟨537356, by rfl⟩ : syracuseStep 11463605 = 1074713) (by norm_num)
theorem B7642403 : Blo 2263435 7642403 := bstep (se 1 (by rfl) ⟨5731802, by rfl⟩ : syracuseStep 7642403 = 11463605) B11463605
theorem B5094935 : Blo 2263435 5094935 := bstep (se 1 (by rfl) ⟨3821201, by rfl⟩ : syracuseStep 5094935 = 7642403) B7642403
theorem B3396623 : Blo 2263435 3396623 := bstep (se 1 (by rfl) ⟨2547467, by rfl⟩ : syracuseStep 3396623 = 5094935) B5094935
theorem B2264415 : Blo 2263435 2264415 := bstep (se 1 (by rfl) ⟨1698311, by rfl⟩ : syracuseStep 2264415 = 3396623) B3396623
theorem B3396629 : Blo 2263435 3396629 := bbase (se 6 (by rfl) ⟨79608, by rfl⟩ : syracuseStep 3396629 = 159217) (by norm_num)
theorem B2264419 : Blo 2263435 2264419 := bstep (se 1 (by rfl) ⟨1698314, by rfl⟩ : syracuseStep 2264419 = 3396629) B3396629
theorem B4590637 : Blo 2263435 4590637 := bbase (se 3 (by rfl) ⟨860744, by rfl⟩ : syracuseStep 4590637 = 1721489) (by norm_num)
theorem B24483397 : Blo 2263435 24483397 := bstep (se 4 (by rfl) ⟨2295318, by rfl⟩ : syracuseStep 24483397 = 4590637) B4590637
theorem B32644529 : Blo 2263435 32644529 := bstep (se 2 (by rfl) ⟨12241698, by rfl⟩ : syracuseStep 32644529 = 24483397) B24483397
theorem B21763019 : Blo 2263435 21763019 := bstep (se 1 (by rfl) ⟨16322264, by rfl⟩ : syracuseStep 21763019 = 32644529) B32644529
theorem B14508679 : Blo 2263435 14508679 := bstep (se 1 (by rfl) ⟨10881509, by rfl⟩ : syracuseStep 14508679 = 21763019) B21763019
theorem B19344905 : Blo 2263435 19344905 := bstep (se 2 (by rfl) ⟨7254339, by rfl⟩ : syracuseStep 19344905 = 14508679) B14508679
theorem B12896603 : Blo 2263435 12896603 := bstep (se 1 (by rfl) ⟨9672452, by rfl⟩ : syracuseStep 12896603 = 19344905) B19344905
theorem B8597735 : Blo 2263435 8597735 := bstep (se 1 (by rfl) ⟨6448301, by rfl⟩ : syracuseStep 8597735 = 12896603) B12896603
theorem B5731823 : Blo 2263435 5731823 := bstep (se 1 (by rfl) ⟨4298867, by rfl⟩ : syracuseStep 5731823 = 8597735) B8597735
theorem B3821215 : Blo 2263435 3821215 := bstep (se 1 (by rfl) ⟨2865911, by rfl⟩ : syracuseStep 3821215 = 5731823) B5731823
theorem B5094953 : Blo 2263435 5094953 := bstep (se 2 (by rfl) ⟨1910607, by rfl⟩ : syracuseStep 5094953 = 3821215) B3821215
theorem B3396635 : Blo 2263435 3396635 := bstep (se 1 (by rfl) ⟨2547476, by rfl⟩ : syracuseStep 3396635 = 5094953) B5094953
theorem B2264423 : Blo 2263435 2264423 := bstep (se 1 (by rfl) ⟨1698317, by rfl⟩ : syracuseStep 2264423 = 3396635) B3396635
theorem B2547481 : Blo 2263435 2547481 := bbase (se 2 (by rfl) ⟨955305, by rfl⟩ : syracuseStep 2547481 = 1910611) (by norm_num)
theorem B3396641 : Blo 2263435 3396641 := bstep (se 2 (by rfl) ⟨1273740, by rfl⟩ : syracuseStep 3396641 = 2547481) B2547481
theorem B2264427 : Blo 2263435 2264427 := bstep (se 1 (by rfl) ⟨1698320, by rfl⟩ : syracuseStep 2264427 = 3396641) B3396641
theorem B8597765 : Blo 2263435 8597765 := bbase (se 4 (by rfl) ⟨806040, by rfl⟩ : syracuseStep 8597765 = 1612081) (by norm_num)
theorem B5731843 : Blo 2263435 5731843 := bstep (se 1 (by rfl) ⟨4298882, by rfl⟩ : syracuseStep 5731843 = 8597765) B8597765
theorem B7642457 : Blo 2263435 7642457 := bstep (se 2 (by rfl) ⟨2865921, by rfl⟩ : syracuseStep 7642457 = 5731843) B5731843
theorem B5094971 : Blo 2263435 5094971 := bstep (se 1 (by rfl) ⟨3821228, by rfl⟩ : syracuseStep 5094971 = 7642457) B7642457
theorem B3396647 : Blo 2263435 3396647 := bstep (se 1 (by rfl) ⟨2547485, by rfl⟩ : syracuseStep 3396647 = 5094971) B5094971
theorem B2264431 : Blo 2263435 2264431 := bstep (se 1 (by rfl) ⟨1698323, by rfl⟩ : syracuseStep 2264431 = 3396647) B3396647
theorem B3396653 : Blo 2263435 3396653 := bbase (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) (by norm_num)
theorem B2264435 : Blo 2263435 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B5094989 : Blo 2263435 5094989 := bbase (se 3 (by rfl) ⟨955310, by rfl⟩ : syracuseStep 5094989 = 1910621) (by norm_num)
theorem B3396659 : Blo 2263435 3396659 := bstep (se 1 (by rfl) ⟨2547494, by rfl⟩ : syracuseStep 3396659 = 5094989) B5094989
theorem B2264439 : Blo 2263435 2264439 := bstep (se 1 (by rfl) ⟨1698329, by rfl⟩ : syracuseStep 2264439 = 3396659) B3396659
theorem B2865937 : Blo 2263435 2865937 := bbase (se 2 (by rfl) ⟨1074726, by rfl⟩ : syracuseStep 2865937 = 2149453) (by norm_num)
theorem B3821249 : Blo 2263435 3821249 := bstep (se 2 (by rfl) ⟨1432968, by rfl⟩ : syracuseStep 3821249 = 2865937) B2865937
theorem B2547499 : Blo 2263435 2547499 := bstep (se 1 (by rfl) ⟨1910624, by rfl⟩ : syracuseStep 2547499 = 3821249) B3821249
theorem B3396665 : Blo 2263435 3396665 := bstep (se 2 (by rfl) ⟨1273749, by rfl⟩ : syracuseStep 3396665 = 2547499) B2547499
theorem B2264443 : Blo 2263435 2264443 := bstep (se 1 (by rfl) ⟨1698332, by rfl⟩ : syracuseStep 2264443 = 3396665) B3396665
theorem B4836277 : Blo 2263435 4836277 := bbase (se 5 (by rfl) ⟨226700, by rfl⟩ : syracuseStep 4836277 = 453401) (by norm_num)
theorem B25793477 : Blo 2263435 25793477 := bstep (se 4 (by rfl) ⟨2418138, by rfl⟩ : syracuseStep 25793477 = 4836277) B4836277
theorem B17195651 : Blo 2263435 17195651 := bstep (se 1 (by rfl) ⟨12896738, by rfl⟩ : syracuseStep 17195651 = 25793477) B25793477
theorem B11463767 : Blo 2263435 11463767 := bstep (se 1 (by rfl) ⟨8597825, by rfl⟩ : syracuseStep 11463767 = 17195651) B17195651
theorem B7642511 : Blo 2263435 7642511 := bstep (se 1 (by rfl) ⟨5731883, by rfl⟩ : syracuseStep 7642511 = 11463767) B11463767
theorem B5095007 : Blo 2263435 5095007 := bstep (se 1 (by rfl) ⟨3821255, by rfl⟩ : syracuseStep 5095007 = 7642511) B7642511
theorem B3396671 : Blo 2263435 3396671 := bstep (se 1 (by rfl) ⟨2547503, by rfl⟩ : syracuseStep 3396671 = 5095007) B5095007
theorem B2264447 : Blo 2263435 2264447 := bstep (se 1 (by rfl) ⟨1698335, by rfl⟩ : syracuseStep 2264447 = 3396671) B3396671
theorem B3396677 : Blo 2263435 3396677 := bbase (se 4 (by rfl) ⟨318438, by rfl⟩ : syracuseStep 3396677 = 636877) (by norm_num)
theorem B2264451 : Blo 2263435 2264451 := bstep (se 1 (by rfl) ⟨1698338, by rfl⟩ : syracuseStep 2264451 = 3396677) B3396677
theorem B3821269 : Blo 2263435 3821269 := bbase (se 7 (by rfl) ⟨44780, by rfl⟩ : syracuseStep 3821269 = 89561) (by norm_num)
theorem B5095025 : Blo 2263435 5095025 := bstep (se 2 (by rfl) ⟨1910634, by rfl⟩ : syracuseStep 5095025 = 3821269) B3821269
theorem B3396683 : Blo 2263435 3396683 := bstep (se 1 (by rfl) ⟨2547512, by rfl⟩ : syracuseStep 3396683 = 5095025) B5095025
theorem B2264455 : Blo 2263435 2264455 := bstep (se 1 (by rfl) ⟨1698341, by rfl⟩ : syracuseStep 2264455 = 3396683) B3396683
theorem B2547517 : Blo 2263435 2547517 := bbase (se 3 (by rfl) ⟨477659, by rfl⟩ : syracuseStep 2547517 = 955319) (by norm_num)
theorem B3396689 : Blo 2263435 3396689 := bstep (se 2 (by rfl) ⟨1273758, by rfl⟩ : syracuseStep 3396689 = 2547517) B2547517
theorem B2264459 : Blo 2263435 2264459 := bstep (se 1 (by rfl) ⟨1698344, by rfl⟩ : syracuseStep 2264459 = 3396689) B3396689
theorem B7642565 : Blo 2263435 7642565 := bbase (se 4 (by rfl) ⟨716490, by rfl⟩ : syracuseStep 7642565 = 1432981) (by norm_num)
theorem B5095043 : Blo 2263435 5095043 := bstep (se 1 (by rfl) ⟨3821282, by rfl⟩ : syracuseStep 5095043 = 7642565) B7642565
theorem B3396695 : Blo 2263435 3396695 := bstep (se 1 (by rfl) ⟨2547521, by rfl⟩ : syracuseStep 3396695 = 5095043) B5095043
theorem B2264463 : Blo 2263435 2264463 := bstep (se 1 (by rfl) ⟨1698347, by rfl⟩ : syracuseStep 2264463 = 3396695) B3396695
theorem B3396701 : Blo 2263435 3396701 := bbase (se 3 (by rfl) ⟨636881, by rfl⟩ : syracuseStep 3396701 = 1273763) (by norm_num)
theorem B2264467 : Blo 2263435 2264467 := bstep (se 1 (by rfl) ⟨1698350, by rfl⟩ : syracuseStep 2264467 = 3396701) B3396701
theorem B5095061 : Blo 2263435 5095061 := bbase (se 6 (by rfl) ⟨119415, by rfl⟩ : syracuseStep 5095061 = 238831) (by norm_num)
theorem B3396707 : Blo 2263435 3396707 := bstep (se 1 (by rfl) ⟨2547530, by rfl⟩ : syracuseStep 3396707 = 5095061) B5095061
theorem B2264471 : Blo 2263435 2264471 := bstep (se 1 (by rfl) ⟨1698353, by rfl⟩ : syracuseStep 2264471 = 3396707) B3396707
theorem B2418169 : Blo 2263435 2418169 := bbase (se 2 (by rfl) ⟨906813, by rfl⟩ : syracuseStep 2418169 = 1813627) (by norm_num)
theorem B3224225 : Blo 2263435 3224225 := bstep (se 2 (by rfl) ⟨1209084, by rfl⟩ : syracuseStep 3224225 = 2418169) B2418169
theorem B8597933 : Blo 2263435 8597933 := bstep (se 3 (by rfl) ⟨1612112, by rfl⟩ : syracuseStep 8597933 = 3224225) B3224225
theorem B5731955 : Blo 2263435 5731955 := bstep (se 1 (by rfl) ⟨4298966, by rfl⟩ : syracuseStep 5731955 = 8597933) B8597933
theorem B3821303 : Blo 2263435 3821303 := bstep (se 1 (by rfl) ⟨2865977, by rfl⟩ : syracuseStep 3821303 = 5731955) B5731955
theorem B2547535 : Blo 2263435 2547535 := bstep (se 1 (by rfl) ⟨1910651, by rfl⟩ : syracuseStep 2547535 = 3821303) B3821303
theorem B3396713 : Blo 2263435 3396713 := bstep (se 2 (by rfl) ⟨1273767, by rfl⟩ : syracuseStep 3396713 = 2547535) B2547535
theorem B2264475 : Blo 2263435 2264475 := bstep (se 1 (by rfl) ⟨1698356, by rfl⟩ : syracuseStep 2264475 = 3396713) B3396713
theorem B2944721 : Blo 2263435 2944721 := bbase (se 2 (by rfl) ⟨1104270, by rfl⟩ : syracuseStep 2944721 = 2208541) (by norm_num)
theorem B7852589 : Blo 2263435 7852589 := bstep (se 3 (by rfl) ⟨1472360, by rfl⟩ : syracuseStep 7852589 = 2944721) B2944721
theorem B5235059 : Blo 2263435 5235059 := bstep (se 1 (by rfl) ⟨3926294, by rfl⟩ : syracuseStep 5235059 = 7852589) B7852589
theorem B3490039 : Blo 2263435 3490039 := bstep (se 1 (by rfl) ⟨2617529, by rfl⟩ : syracuseStep 3490039 = 5235059) B5235059
theorem B4653385 : Blo 2263435 4653385 := bstep (se 2 (by rfl) ⟨1745019, by rfl⟩ : syracuseStep 4653385 = 3490039) B3490039
theorem B99272213 : Blo 2263435 99272213 := bstep (se 6 (by rfl) ⟨2326692, by rfl⟩ : syracuseStep 99272213 = 4653385) B4653385
theorem B66181475 : Blo 2263435 66181475 := bstep (se 1 (by rfl) ⟨49636106, by rfl⟩ : syracuseStep 66181475 = 99272213) B99272213
theorem B44120983 : Blo 2263435 44120983 := bstep (se 1 (by rfl) ⟨33090737, by rfl⟩ : syracuseStep 44120983 = 66181475) B66181475
theorem B58827977 : Blo 2263435 58827977 := bstep (se 2 (by rfl) ⟨22060491, by rfl⟩ : syracuseStep 58827977 = 44120983) B44120983
theorem B39218651 : Blo 2263435 39218651 := bstep (se 1 (by rfl) ⟨29413988, by rfl⟩ : syracuseStep 39218651 = 58827977) B58827977
theorem B26145767 : Blo 2263435 26145767 := bstep (se 1 (by rfl) ⟨19609325, by rfl⟩ : syracuseStep 26145767 = 39218651) B39218651
theorem B17430511 : Blo 2263435 17430511 := bstep (se 1 (by rfl) ⟨13072883, by rfl⟩ : syracuseStep 17430511 = 26145767) B26145767
theorem B23240681 : Blo 2263435 23240681 := bstep (se 2 (by rfl) ⟨8715255, by rfl⟩ : syracuseStep 23240681 = 17430511) B17430511
theorem B15493787 : Blo 2263435 15493787 := bstep (se 1 (by rfl) ⟨11620340, by rfl⟩ : syracuseStep 15493787 = 23240681) B23240681
theorem B10329191 : Blo 2263435 10329191 := bstep (se 1 (by rfl) ⟨7746893, by rfl⟩ : syracuseStep 10329191 = 15493787) B15493787
theorem B6886127 : Blo 2263435 6886127 := bstep (se 1 (by rfl) ⟨5164595, by rfl⟩ : syracuseStep 6886127 = 10329191) B10329191
theorem B4590751 : Blo 2263435 4590751 := bstep (se 1 (by rfl) ⟨3443063, by rfl⟩ : syracuseStep 4590751 = 6886127) B6886127
theorem B6121001 : Blo 2263435 6121001 := bstep (se 2 (by rfl) ⟨2295375, by rfl⟩ : syracuseStep 6121001 = 4590751) B4590751
theorem B4080667 : Blo 2263435 4080667 := bstep (se 1 (by rfl) ⟨3060500, by rfl⟩ : syracuseStep 4080667 = 6121001) B6121001
theorem B5440889 : Blo 2263435 5440889 := bstep (se 2 (by rfl) ⟨2040333, by rfl⟩ : syracuseStep 5440889 = 4080667) B4080667
theorem B14509037 : Blo 2263435 14509037 := bstep (se 3 (by rfl) ⟨2720444, by rfl⟩ : syracuseStep 14509037 = 5440889) B5440889
theorem B9672691 : Blo 2263435 9672691 := bstep (se 1 (by rfl) ⟨7254518, by rfl⟩ : syracuseStep 9672691 = 14509037) B14509037
theorem B12896921 : Blo 2263435 12896921 := bstep (se 2 (by rfl) ⟨4836345, by rfl⟩ : syracuseStep 12896921 = 9672691) B9672691
theorem B8597947 : Blo 2263435 8597947 := bstep (se 1 (by rfl) ⟨6448460, by rfl⟩ : syracuseStep 8597947 = 12896921) B12896921
theorem B11463929 : Blo 2263435 11463929 := bstep (se 2 (by rfl) ⟨4298973, by rfl⟩ : syracuseStep 11463929 = 8597947) B8597947
theorem B7642619 : Blo 2263435 7642619 := bstep (se 1 (by rfl) ⟨5731964, by rfl⟩ : syracuseStep 7642619 = 11463929) B11463929
theorem B5095079 : Blo 2263435 5095079 := bstep (se 1 (by rfl) ⟨3821309, by rfl⟩ : syracuseStep 5095079 = 7642619) B7642619
theorem B3396719 : Blo 2263435 3396719 := bstep (se 1 (by rfl) ⟨2547539, by rfl⟩ : syracuseStep 3396719 = 5095079) B5095079
theorem B2264479 : Blo 2263435 2264479 := bstep (se 1 (by rfl) ⟨1698359, by rfl⟩ : syracuseStep 2264479 = 3396719) B3396719
theorem B3396725 : Blo 2263435 3396725 := bbase (se 5 (by rfl) ⟨159221, by rfl⟩ : syracuseStep 3396725 = 318443) (by norm_num)
theorem B2264483 : Blo 2263435 2264483 := bstep (se 1 (by rfl) ⟨1698362, by rfl⟩ : syracuseStep 2264483 = 3396725) B3396725
theorem B4298989 : Blo 2263435 4298989 := bbase (se 3 (by rfl) ⟨806060, by rfl⟩ : syracuseStep 4298989 = 1612121) (by norm_num)
theorem B5731985 : Blo 2263435 5731985 := bstep (se 2 (by rfl) ⟨2149494, by rfl⟩ : syracuseStep 5731985 = 4298989) B4298989
theorem B3821323 : Blo 2263435 3821323 := bstep (se 1 (by rfl) ⟨2865992, by rfl⟩ : syracuseStep 3821323 = 5731985) B5731985
theorem B5095097 : Blo 2263435 5095097 := bstep (se 2 (by rfl) ⟨1910661, by rfl⟩ : syracuseStep 5095097 = 3821323) B3821323
theorem B3396731 : Blo 2263435 3396731 := bstep (se 1 (by rfl) ⟨2547548, by rfl⟩ : syracuseStep 3396731 = 5095097) B5095097
theorem B2264487 : Blo 2263435 2264487 := bstep (se 1 (by rfl) ⟨1698365, by rfl⟩ : syracuseStep 2264487 = 3396731) B3396731
theorem B2547553 : Blo 2263435 2547553 := bbase (se 2 (by rfl) ⟨955332, by rfl⟩ : syracuseStep 2547553 = 1910665) (by norm_num)
theorem B3396737 : Blo 2263435 3396737 := bstep (se 2 (by rfl) ⟨1273776, by rfl⟩ : syracuseStep 3396737 = 2547553) B2547553
theorem B2264491 : Blo 2263435 2264491 := bstep (se 1 (by rfl) ⟨1698368, by rfl⟩ : syracuseStep 2264491 = 3396737) B3396737
theorem B5732005 : Blo 2263435 5732005 := bbase (se 4 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 5732005 = 1074751) (by norm_num)
theorem B7642673 : Blo 2263435 7642673 := bstep (se 2 (by rfl) ⟨2866002, by rfl⟩ : syracuseStep 7642673 = 5732005) B5732005
theorem B5095115 : Blo 2263435 5095115 := bstep (se 1 (by rfl) ⟨3821336, by rfl⟩ : syracuseStep 5095115 = 7642673) B7642673
theorem B3396743 : Blo 2263435 3396743 := bstep (se 1 (by rfl) ⟨2547557, by rfl⟩ : syracuseStep 3396743 = 5095115) B5095115
theorem B2264495 : Blo 2263435 2264495 := bstep (se 1 (by rfl) ⟨1698371, by rfl⟩ : syracuseStep 2264495 = 3396743) B3396743
theorem B3396749 : Blo 2263435 3396749 := bbase (se 3 (by rfl) ⟨636890, by rfl⟩ : syracuseStep 3396749 = 1273781) (by norm_num)
theorem B2264499 : Blo 2263435 2264499 := bstep (se 1 (by rfl) ⟨1698374, by rfl⟩ : syracuseStep 2264499 = 3396749) B3396749
theorem B5095133 : Blo 2263435 5095133 := bbase (se 3 (by rfl) ⟨955337, by rfl⟩ : syracuseStep 5095133 = 1910675) (by norm_num)
theorem B3396755 : Blo 2263435 3396755 := bstep (se 1 (by rfl) ⟨2547566, by rfl⟩ : syracuseStep 3396755 = 5095133) B5095133
theorem B2264503 : Blo 2263435 2264503 := bstep (se 1 (by rfl) ⟨1698377, by rfl⟩ : syracuseStep 2264503 = 3396755) B3396755
theorem B3821357 : Blo 2263435 3821357 := bbase (se 3 (by rfl) ⟨716504, by rfl⟩ : syracuseStep 3821357 = 1433009) (by norm_num)
theorem B2547571 : Blo 2263435 2547571 := bstep (se 1 (by rfl) ⟨1910678, by rfl⟩ : syracuseStep 2547571 = 3821357) B3821357
theorem B3396761 : Blo 2263435 3396761 := bstep (se 2 (by rfl) ⟨1273785, by rfl⟩ : syracuseStep 3396761 = 2547571) B2547571
theorem B2264507 : Blo 2263435 2264507 := bstep (se 1 (by rfl) ⟨1698380, by rfl⟩ : syracuseStep 2264507 = 3396761) B3396761
theorem B6536533 : Blo 2263435 6536533 := bbase (se 11 (by rfl) ⟨4787, by rfl⟩ : syracuseStep 6536533 = 9575) (by norm_num)
theorem B8715377 : Blo 2263435 8715377 := bstep (se 2 (by rfl) ⟨3268266, by rfl⟩ : syracuseStep 8715377 = 6536533) B6536533
theorem B23241005 : Blo 2263435 23241005 := bstep (se 3 (by rfl) ⟨4357688, by rfl⟩ : syracuseStep 23241005 = 8715377) B8715377
theorem B15494003 : Blo 2263435 15494003 := bstep (se 1 (by rfl) ⟨11620502, by rfl⟩ : syracuseStep 15494003 = 23241005) B23241005
theorem B10329335 : Blo 2263435 10329335 := bstep (se 1 (by rfl) ⟨7747001, by rfl⟩ : syracuseStep 10329335 = 15494003) B15494003
theorem B6886223 : Blo 2263435 6886223 := bstep (se 1 (by rfl) ⟨5164667, by rfl⟩ : syracuseStep 6886223 = 10329335) B10329335
theorem B4590815 : Blo 2263435 4590815 := bstep (se 1 (by rfl) ⟨3443111, by rfl⟩ : syracuseStep 4590815 = 6886223) B6886223
theorem B12242173 : Blo 2263435 12242173 := bstep (se 3 (by rfl) ⟨2295407, by rfl⟩ : syracuseStep 12242173 = 4590815) B4590815
theorem B16322897 : Blo 2263435 16322897 := bstep (se 2 (by rfl) ⟨6121086, by rfl⟩ : syracuseStep 16322897 = 12242173) B12242173
theorem B43527725 : Blo 2263435 43527725 := bstep (se 3 (by rfl) ⟨8161448, by rfl⟩ : syracuseStep 43527725 = 16322897) B16322897
theorem B29018483 : Blo 2263435 29018483 := bstep (se 1 (by rfl) ⟨21763862, by rfl⟩ : syracuseStep 29018483 = 43527725) B43527725
theorem B19345655 : Blo 2263435 19345655 := bstep (se 1 (by rfl) ⟨14509241, by rfl⟩ : syracuseStep 19345655 = 29018483) B29018483
theorem B12897103 : Blo 2263435 12897103 := bstep (se 1 (by rfl) ⟨9672827, by rfl⟩ : syracuseStep 12897103 = 19345655) B19345655
theorem B17196137 : Blo 2263435 17196137 := bstep (se 2 (by rfl) ⟨6448551, by rfl⟩ : syracuseStep 17196137 = 12897103) B12897103
theorem B11464091 : Blo 2263435 11464091 := bstep (se 1 (by rfl) ⟨8598068, by rfl⟩ : syracuseStep 11464091 = 17196137) B17196137
theorem B7642727 : Blo 2263435 7642727 := bstep (se 1 (by rfl) ⟨5732045, by rfl⟩ : syracuseStep 7642727 = 11464091) B11464091
theorem B5095151 : Blo 2263435 5095151 := bstep (se 1 (by rfl) ⟨3821363, by rfl⟩ : syracuseStep 5095151 = 7642727) B7642727
theorem B3396767 : Blo 2263435 3396767 := bstep (se 1 (by rfl) ⟨2547575, by rfl⟩ : syracuseStep 3396767 = 5095151) B5095151
theorem B2264511 : Blo 2263435 2264511 := bstep (se 1 (by rfl) ⟨1698383, by rfl⟩ : syracuseStep 2264511 = 3396767) B3396767
theorem B3396773 : Blo 2263435 3396773 := bbase (se 4 (by rfl) ⟨318447, by rfl⟩ : syracuseStep 3396773 = 636895) (by norm_num)
theorem B2264515 : Blo 2263435 2264515 := bstep (se 1 (by rfl) ⟨1698386, by rfl⟩ : syracuseStep 2264515 = 3396773) B3396773
theorem B2866033 : Blo 2263435 2866033 := bbase (se 2 (by rfl) ⟨1074762, by rfl⟩ : syracuseStep 2866033 = 2149525) (by norm_num)
theorem B3821377 : Blo 2263435 3821377 := bstep (se 2 (by rfl) ⟨1433016, by rfl⟩ : syracuseStep 3821377 = 2866033) B2866033
theorem B5095169 : Blo 2263435 5095169 := bstep (se 2 (by rfl) ⟨1910688, by rfl⟩ : syracuseStep 5095169 = 3821377) B3821377
theorem B3396779 : Blo 2263435 3396779 := bstep (se 1 (by rfl) ⟨2547584, by rfl⟩ : syracuseStep 3396779 = 5095169) B5095169
theorem B2264519 : Blo 2263435 2264519 := bstep (se 1 (by rfl) ⟨1698389, by rfl⟩ : syracuseStep 2264519 = 3396779) B3396779
theorem B2547589 : Blo 2263435 2547589 := bbase (se 4 (by rfl) ⟨238836, by rfl⟩ : syracuseStep 2547589 = 477673) (by norm_num)
theorem B3396785 : Blo 2263435 3396785 := bstep (se 2 (by rfl) ⟨1273794, by rfl⟩ : syracuseStep 3396785 = 2547589) B2547589
theorem B2264523 : Blo 2263435 2264523 := bstep (se 1 (by rfl) ⟨1698392, by rfl⟩ : syracuseStep 2264523 = 3396785) B3396785
theorem B2295425 : Blo 2263435 2295425 := bbase (se 2 (by rfl) ⟨860784, by rfl⟩ : syracuseStep 2295425 = 1721569) (by norm_num)
theorem B6121133 : Blo 2263435 6121133 := bstep (se 3 (by rfl) ⟨1147712, by rfl⟩ : syracuseStep 6121133 = 2295425) B2295425
theorem B4080755 : Blo 2263435 4080755 := bstep (se 1 (by rfl) ⟨3060566, by rfl⟩ : syracuseStep 4080755 = 6121133) B6121133
theorem B2720503 : Blo 2263435 2720503 := bstep (se 1 (by rfl) ⟨2040377, by rfl⟩ : syracuseStep 2720503 = 4080755) B4080755
theorem B3627337 : Blo 2263435 3627337 := bstep (se 2 (by rfl) ⟨1360251, by rfl⟩ : syracuseStep 3627337 = 2720503) B2720503
theorem B4836449 : Blo 2263435 4836449 := bstep (se 2 (by rfl) ⟨1813668, by rfl⟩ : syracuseStep 4836449 = 3627337) B3627337
theorem B3224299 : Blo 2263435 3224299 := bstep (se 1 (by rfl) ⟨2418224, by rfl⟩ : syracuseStep 3224299 = 4836449) B4836449
theorem B4299065 : Blo 2263435 4299065 := bstep (se 2 (by rfl) ⟨1612149, by rfl⟩ : syracuseStep 4299065 = 3224299) B3224299
theorem B2866043 : Blo 2263435 2866043 := bstep (se 1 (by rfl) ⟨2149532, by rfl⟩ : syracuseStep 2866043 = 4299065) B4299065
theorem B7642781 : Blo 2263435 7642781 := bstep (se 3 (by rfl) ⟨1433021, by rfl⟩ : syracuseStep 7642781 = 2866043) B2866043
theorem B5095187 : Blo 2263435 5095187 := bstep (se 1 (by rfl) ⟨3821390, by rfl⟩ : syracuseStep 5095187 = 7642781) B7642781
theorem B3396791 : Blo 2263435 3396791 := bstep (se 1 (by rfl) ⟨2547593, by rfl⟩ : syracuseStep 3396791 = 5095187) B5095187
theorem B2264527 : Blo 2263435 2264527 := bstep (se 1 (by rfl) ⟨1698395, by rfl⟩ : syracuseStep 2264527 = 3396791) B3396791
theorem B3396797 : Blo 2263435 3396797 := bbase (se 3 (by rfl) ⟨636899, by rfl⟩ : syracuseStep 3396797 = 1273799) (by norm_num)
theorem B2264531 : Blo 2263435 2264531 := bstep (se 1 (by rfl) ⟨1698398, by rfl⟩ : syracuseStep 2264531 = 3396797) B3396797
theorem B5095205 : Blo 2263435 5095205 := bbase (se 4 (by rfl) ⟨477675, by rfl⟩ : syracuseStep 5095205 = 955351) (by norm_num)
theorem B3396803 : Blo 2263435 3396803 := bstep (se 1 (by rfl) ⟨2547602, by rfl⟩ : syracuseStep 3396803 = 5095205) B5095205
theorem B2264535 : Blo 2263435 2264535 := bstep (se 1 (by rfl) ⟨1698401, by rfl⟩ : syracuseStep 2264535 = 3396803) B3396803
theorem B5732117 : Blo 2263435 5732117 := bbase (se 6 (by rfl) ⟨134346, by rfl⟩ : syracuseStep 5732117 = 268693) (by norm_num)
theorem B3821411 : Blo 2263435 3821411 := bstep (se 1 (by rfl) ⟨2866058, by rfl⟩ : syracuseStep 3821411 = 5732117) B5732117
theorem B2547607 : Blo 2263435 2547607 := bstep (se 1 (by rfl) ⟨1910705, by rfl⟩ : syracuseStep 2547607 = 3821411) B3821411
theorem B3396809 : Blo 2263435 3396809 := bstep (se 2 (by rfl) ⟨1273803, by rfl⟩ : syracuseStep 3396809 = 2547607) B2547607
theorem B2264539 : Blo 2263435 2264539 := bstep (se 1 (by rfl) ⟨1698404, by rfl⟩ : syracuseStep 2264539 = 3396809) B3396809
theorem B9672965 : Blo 2263435 9672965 := bbase (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) (by norm_num)
theorem B6448643 : Blo 2263435 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B4299095 : Blo 2263435 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B11464253 : Blo 2263435 11464253 := bstep (se 3 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 11464253 = 4299095) B4299095
theorem B7642835 : Blo 2263435 7642835 := bstep (se 1 (by rfl) ⟨5732126, by rfl⟩ : syracuseStep 7642835 = 11464253) B11464253
theorem B5095223 : Blo 2263435 5095223 := bstep (se 1 (by rfl) ⟨3821417, by rfl⟩ : syracuseStep 5095223 = 7642835) B7642835
theorem B3396815 : Blo 2263435 3396815 := bstep (se 1 (by rfl) ⟨2547611, by rfl⟩ : syracuseStep 3396815 = 5095223) B5095223
theorem B2264543 : Blo 2263435 2264543 := bstep (se 1 (by rfl) ⟨1698407, by rfl⟩ : syracuseStep 2264543 = 3396815) B3396815
theorem B3396821 : Blo 2263435 3396821 := bbase (se 7 (by rfl) ⟨39806, by rfl⟩ : syracuseStep 3396821 = 79613) (by norm_num)
theorem B2264547 : Blo 2263435 2264547 := bstep (se 1 (by rfl) ⟨1698410, by rfl⟩ : syracuseStep 2264547 = 3396821) B3396821
theorem B3224333 : Blo 2263435 3224333 := bbase (se 3 (by rfl) ⟨604562, by rfl⟩ : syracuseStep 3224333 = 1209125) (by norm_num)
theorem B8598221 : Blo 2263435 8598221 := bstep (se 3 (by rfl) ⟨1612166, by rfl⟩ : syracuseStep 8598221 = 3224333) B3224333
theorem B5732147 : Blo 2263435 5732147 := bstep (se 1 (by rfl) ⟨4299110, by rfl⟩ : syracuseStep 5732147 = 8598221) B8598221
theorem B3821431 : Blo 2263435 3821431 := bstep (se 1 (by rfl) ⟨2866073, by rfl⟩ : syracuseStep 3821431 = 5732147) B5732147
theorem B5095241 : Blo 2263435 5095241 := bstep (se 2 (by rfl) ⟨1910715, by rfl⟩ : syracuseStep 5095241 = 3821431) B3821431
theorem B3396827 : Blo 2263435 3396827 := bstep (se 1 (by rfl) ⟨2547620, by rfl⟩ : syracuseStep 3396827 = 5095241) B5095241
theorem B2264551 : Blo 2263435 2264551 := bstep (se 1 (by rfl) ⟨1698413, by rfl⟩ : syracuseStep 2264551 = 3396827) B3396827
theorem B2547625 : Blo 2263435 2547625 := bbase (se 2 (by rfl) ⟨955359, by rfl⟩ : syracuseStep 2547625 = 1910719) (by norm_num)
theorem B3396833 : Blo 2263435 3396833 := bstep (se 2 (by rfl) ⟨1273812, by rfl⟩ : syracuseStep 3396833 = 2547625) B2547625
theorem B2264555 : Blo 2263435 2264555 := bstep (se 1 (by rfl) ⟨1698416, by rfl⟩ : syracuseStep 2264555 = 3396833) B3396833
theorem B2582389 : Blo 2263435 2582389 := bbase (se 5 (by rfl) ⟨121049, by rfl⟩ : syracuseStep 2582389 = 242099) (by norm_num)
theorem B3443185 : Blo 2263435 3443185 := bstep (se 2 (by rfl) ⟨1291194, by rfl⟩ : syracuseStep 3443185 = 2582389) B2582389
theorem B4590913 : Blo 2263435 4590913 := bstep (se 2 (by rfl) ⟨1721592, by rfl⟩ : syracuseStep 4590913 = 3443185) B3443185
theorem B6121217 : Blo 2263435 6121217 := bstep (se 2 (by rfl) ⟨2295456, by rfl⟩ : syracuseStep 6121217 = 4590913) B4590913
theorem B16323245 : Blo 2263435 16323245 := bstep (se 3 (by rfl) ⟨3060608, by rfl⟩ : syracuseStep 16323245 = 6121217) B6121217
theorem B10882163 : Blo 2263435 10882163 := bstep (se 1 (by rfl) ⟨8161622, by rfl⟩ : syracuseStep 10882163 = 16323245) B16323245
theorem B7254775 : Blo 2263435 7254775 := bstep (se 1 (by rfl) ⟨5441081, by rfl⟩ : syracuseStep 7254775 = 10882163) B10882163
theorem B9673033 : Blo 2263435 9673033 := bstep (se 2 (by rfl) ⟨3627387, by rfl⟩ : syracuseStep 9673033 = 7254775) B7254775
theorem B12897377 : Blo 2263435 12897377 := bstep (se 2 (by rfl) ⟨4836516, by rfl⟩ : syracuseStep 12897377 = 9673033) B9673033
theorem B8598251 : Blo 2263435 8598251 := bstep (se 1 (by rfl) ⟨6448688, by rfl⟩ : syracuseStep 8598251 = 12897377) B12897377
theorem B5732167 : Blo 2263435 5732167 := bstep (se 1 (by rfl) ⟨4299125, by rfl⟩ : syracuseStep 5732167 = 8598251) B8598251
theorem B7642889 : Blo 2263435 7642889 := bstep (se 2 (by rfl) ⟨2866083, by rfl⟩ : syracuseStep 7642889 = 5732167) B5732167
theorem B5095259 : Blo 2263435 5095259 := bstep (se 1 (by rfl) ⟨3821444, by rfl⟩ : syracuseStep 5095259 = 7642889) B7642889
theorem B3396839 : Blo 2263435 3396839 := bstep (se 1 (by rfl) ⟨2547629, by rfl⟩ : syracuseStep 3396839 = 5095259) B5095259
theorem B2264559 : Blo 2263435 2264559 := bstep (se 1 (by rfl) ⟨1698419, by rfl⟩ : syracuseStep 2264559 = 3396839) B3396839
theorem B3396845 : Blo 2263435 3396845 := bbase (se 3 (by rfl) ⟨636908, by rfl⟩ : syracuseStep 3396845 = 1273817) (by norm_num)
theorem B2264563 : Blo 2263435 2264563 := bstep (se 1 (by rfl) ⟨1698422, by rfl⟩ : syracuseStep 2264563 = 3396845) B3396845
theorem B5095277 : Blo 2263435 5095277 := bbase (se 3 (by rfl) ⟨955364, by rfl⟩ : syracuseStep 5095277 = 1910729) (by norm_num)
theorem B3396851 : Blo 2263435 3396851 := bstep (se 1 (by rfl) ⟨2547638, by rfl⟩ : syracuseStep 3396851 = 5095277) B5095277
theorem B2264567 : Blo 2263435 2264567 := bstep (se 1 (by rfl) ⟨1698425, by rfl⟩ : syracuseStep 2264567 = 3396851) B3396851
theorem B4299149 : Blo 2263435 4299149 := bbase (se 3 (by rfl) ⟨806090, by rfl⟩ : syracuseStep 4299149 = 1612181) (by norm_num)
theorem B2866099 : Blo 2263435 2866099 := bstep (se 1 (by rfl) ⟨2149574, by rfl⟩ : syracuseStep 2866099 = 4299149) B4299149
theorem B3821465 : Blo 2263435 3821465 := bstep (se 2 (by rfl) ⟨1433049, by rfl⟩ : syracuseStep 3821465 = 2866099) B2866099
theorem B2547643 : Blo 2263435 2547643 := bstep (se 1 (by rfl) ⟨1910732, by rfl⟩ : syracuseStep 2547643 = 3821465) B3821465
theorem B3396857 : Blo 2263435 3396857 := bstep (se 2 (by rfl) ⟨1273821, by rfl⟩ : syracuseStep 3396857 = 2547643) B2547643
theorem B2264571 : Blo 2263435 2264571 := bstep (se 1 (by rfl) ⟨1698428, by rfl⟩ : syracuseStep 2264571 = 3396857) B3396857
theorem B5164813 : Blo 2263435 5164813 := bbase (se 3 (by rfl) ⟨968402, by rfl⟩ : syracuseStep 5164813 = 1936805) (by norm_num)
theorem B27545669 : Blo 2263435 27545669 := bstep (se 4 (by rfl) ⟨2582406, by rfl⟩ : syracuseStep 27545669 = 5164813) B5164813
theorem B18363779 : Blo 2263435 18363779 := bstep (se 1 (by rfl) ⟨13772834, by rfl⟩ : syracuseStep 18363779 = 27545669) B27545669
theorem B12242519 : Blo 2263435 12242519 := bstep (se 1 (by rfl) ⟨9181889, by rfl⟩ : syracuseStep 12242519 = 18363779) B18363779
theorem B8161679 : Blo 2263435 8161679 := bstep (se 1 (by rfl) ⟨6121259, by rfl⟩ : syracuseStep 8161679 = 12242519) B12242519
theorem B21764477 : Blo 2263435 21764477 := bstep (se 3 (by rfl) ⟨4080839, by rfl⟩ : syracuseStep 21764477 = 8161679) B8161679
theorem B58038605 : Blo 2263435 58038605 := bstep (se 3 (by rfl) ⟨10882238, by rfl⟩ : syracuseStep 58038605 = 21764477) B21764477
theorem B38692403 : Blo 2263435 38692403 := bstep (se 1 (by rfl) ⟨29019302, by rfl⟩ : syracuseStep 38692403 = 58038605) B58038605
theorem B25794935 : Blo 2263435 25794935 := bstep (se 1 (by rfl) ⟨19346201, by rfl⟩ : syracuseStep 25794935 = 38692403) B38692403
theorem B17196623 : Blo 2263435 17196623 := bstep (se 1 (by rfl) ⟨12897467, by rfl⟩ : syracuseStep 17196623 = 25794935) B25794935
theorem B11464415 : Blo 2263435 11464415 := bstep (se 1 (by rfl) ⟨8598311, by rfl⟩ : syracuseStep 11464415 = 17196623) B17196623
theorem B7642943 : Blo 2263435 7642943 := bstep (se 1 (by rfl) ⟨5732207, by rfl⟩ : syracuseStep 7642943 = 11464415) B11464415
theorem B5095295 : Blo 2263435 5095295 := bstep (se 1 (by rfl) ⟨3821471, by rfl⟩ : syracuseStep 5095295 = 7642943) B7642943
theorem B3396863 : Blo 2263435 3396863 := bstep (se 1 (by rfl) ⟨2547647, by rfl⟩ : syracuseStep 3396863 = 5095295) B5095295
theorem B2264575 : Blo 2263435 2264575 := bstep (se 1 (by rfl) ⟨1698431, by rfl⟩ : syracuseStep 2264575 = 3396863) B3396863
theorem B3396869 : Blo 2263435 3396869 := bbase (se 4 (by rfl) ⟨318456, by rfl⟩ : syracuseStep 3396869 = 636913) (by norm_num)
theorem B2264579 : Blo 2263435 2264579 := bstep (se 1 (by rfl) ⟨1698434, by rfl⟩ : syracuseStep 2264579 = 3396869) B3396869
theorem B3821485 : Blo 2263435 3821485 := bbase (se 3 (by rfl) ⟨716528, by rfl⟩ : syracuseStep 3821485 = 1433057) (by norm_num)
theorem B5095313 : Blo 2263435 5095313 := bstep (se 2 (by rfl) ⟨1910742, by rfl⟩ : syracuseStep 5095313 = 3821485) B3821485
theorem B3396875 : Blo 2263435 3396875 := bstep (se 1 (by rfl) ⟨2547656, by rfl⟩ : syracuseStep 3396875 = 5095313) B5095313
theorem B2264583 : Blo 2263435 2264583 := bstep (se 1 (by rfl) ⟨1698437, by rfl⟩ : syracuseStep 2264583 = 3396875) B3396875
theorem B2547661 : Blo 2263435 2547661 := bbase (se 3 (by rfl) ⟨477686, by rfl⟩ : syracuseStep 2547661 = 955373) (by norm_num)
theorem B3396881 : Blo 2263435 3396881 := bstep (se 2 (by rfl) ⟨1273830, by rfl⟩ : syracuseStep 3396881 = 2547661) B2547661
theorem B2264587 : Blo 2263435 2264587 := bstep (se 1 (by rfl) ⟨1698440, by rfl⟩ : syracuseStep 2264587 = 3396881) B3396881
theorem B7642997 : Blo 2263435 7642997 := bbase (se 5 (by rfl) ⟨358265, by rfl⟩ : syracuseStep 7642997 = 716531) (by norm_num)
theorem B5095331 : Blo 2263435 5095331 := bstep (se 1 (by rfl) ⟨3821498, by rfl⟩ : syracuseStep 5095331 = 7642997) B7642997
theorem B3396887 : Blo 2263435 3396887 := bstep (se 1 (by rfl) ⟨2547665, by rfl⟩ : syracuseStep 3396887 = 5095331) B5095331
theorem B2264591 : Blo 2263435 2264591 := bstep (se 1 (by rfl) ⟨1698443, by rfl⟩ : syracuseStep 2264591 = 3396887) B3396887
theorem B3396893 : Blo 2263435 3396893 := bbase (se 3 (by rfl) ⟨636917, by rfl⟩ : syracuseStep 3396893 = 1273835) (by norm_num)
theorem B2264595 : Blo 2263435 2264595 := bstep (se 1 (by rfl) ⟨1698446, by rfl⟩ : syracuseStep 2264595 = 3396893) B3396893
theorem B5095349 : Blo 2263435 5095349 := bbase (se 5 (by rfl) ⟨238844, by rfl⟩ : syracuseStep 5095349 = 477689) (by norm_num)
theorem B3396899 : Blo 2263435 3396899 := bstep (se 1 (by rfl) ⟨2547674, by rfl⟩ : syracuseStep 3396899 = 5095349) B5095349
theorem B2264599 : Blo 2263435 2264599 := bstep (se 1 (by rfl) ⟨1698449, by rfl⟩ : syracuseStep 2264599 = 3396899) B3396899
theorem B7254917 : Blo 2263435 7254917 := bbase (se 4 (by rfl) ⟨680148, by rfl⟩ : syracuseStep 7254917 = 1360297) (by norm_num)
theorem B4836611 : Blo 2263435 4836611 := bstep (se 1 (by rfl) ⟨3627458, by rfl⟩ : syracuseStep 4836611 = 7254917) B7254917
theorem B12897629 : Blo 2263435 12897629 := bstep (se 3 (by rfl) ⟨2418305, by rfl⟩ : syracuseStep 12897629 = 4836611) B4836611
theorem B8598419 : Blo 2263435 8598419 := bstep (se 1 (by rfl) ⟨6448814, by rfl⟩ : syracuseStep 8598419 = 12897629) B12897629
theorem B5732279 : Blo 2263435 5732279 := bstep (se 1 (by rfl) ⟨4299209, by rfl⟩ : syracuseStep 5732279 = 8598419) B8598419
theorem B3821519 : Blo 2263435 3821519 := bstep (se 1 (by rfl) ⟨2866139, by rfl⟩ : syracuseStep 3821519 = 5732279) B5732279
theorem B2547679 : Blo 2263435 2547679 := bstep (se 1 (by rfl) ⟨1910759, by rfl⟩ : syracuseStep 2547679 = 3821519) B3821519
theorem B3396905 : Blo 2263435 3396905 := bstep (se 2 (by rfl) ⟨1273839, by rfl⟩ : syracuseStep 3396905 = 2547679) B2547679
theorem B2264603 : Blo 2263435 2264603 := bstep (se 1 (by rfl) ⟨1698452, by rfl⟩ : syracuseStep 2264603 = 3396905) B3396905
theorem B5441197 : Blo 2263435 5441197 := bbase (se 3 (by rfl) ⟨1020224, by rfl⟩ : syracuseStep 5441197 = 2040449) (by norm_num)
theorem B7254929 : Blo 2263435 7254929 := bstep (se 2 (by rfl) ⟨2720598, by rfl⟩ : syracuseStep 7254929 = 5441197) B5441197
theorem B4836619 : Blo 2263435 4836619 := bstep (se 1 (by rfl) ⟨3627464, by rfl⟩ : syracuseStep 4836619 = 7254929) B7254929
theorem B6448825 : Blo 2263435 6448825 := bstep (se 2 (by rfl) ⟨2418309, by rfl⟩ : syracuseStep 6448825 = 4836619) B4836619
theorem B8598433 : Blo 2263435 8598433 := bstep (se 2 (by rfl) ⟨3224412, by rfl⟩ : syracuseStep 8598433 = 6448825) B6448825
theorem B11464577 : Blo 2263435 11464577 := bstep (se 2 (by rfl) ⟨4299216, by rfl⟩ : syracuseStep 11464577 = 8598433) B8598433
theorem B7643051 : Blo 2263435 7643051 := bstep (se 1 (by rfl) ⟨5732288, by rfl⟩ : syracuseStep 7643051 = 11464577) B11464577
theorem B5095367 : Blo 2263435 5095367 := bstep (se 1 (by rfl) ⟨3821525, by rfl⟩ : syracuseStep 5095367 = 7643051) B7643051
theorem B3396911 : Blo 2263435 3396911 := bstep (se 1 (by rfl) ⟨2547683, by rfl⟩ : syracuseStep 3396911 = 5095367) B5095367
theorem B2264607 : Blo 2263435 2264607 := bstep (se 1 (by rfl) ⟨1698455, by rfl⟩ : syracuseStep 2264607 = 3396911) B3396911
theorem B3396917 : Blo 2263435 3396917 := bbase (se 5 (by rfl) ⟨159230, by rfl⟩ : syracuseStep 3396917 = 318461) (by norm_num)
theorem B2264611 : Blo 2263435 2264611 := bstep (se 1 (by rfl) ⟨1698458, by rfl⟩ : syracuseStep 2264611 = 3396917) B3396917
theorem B5732309 : Blo 2263435 5732309 := bbase (se 7 (by rfl) ⟨67175, by rfl⟩ : syracuseStep 5732309 = 134351) (by norm_num)
theorem B3821539 : Blo 2263435 3821539 := bstep (se 1 (by rfl) ⟨2866154, by rfl⟩ : syracuseStep 3821539 = 5732309) B5732309
theorem B5095385 : Blo 2263435 5095385 := bstep (se 2 (by rfl) ⟨1910769, by rfl⟩ : syracuseStep 5095385 = 3821539) B3821539
theorem B3396923 : Blo 2263435 3396923 := bstep (se 1 (by rfl) ⟨2547692, by rfl⟩ : syracuseStep 3396923 = 5095385) B5095385
theorem B2264615 : Blo 2263435 2264615 := bstep (se 1 (by rfl) ⟨1698461, by rfl⟩ : syracuseStep 2264615 = 3396923) B3396923
theorem B2547697 : Blo 2263435 2547697 := bbase (se 2 (by rfl) ⟨955386, by rfl⟩ : syracuseStep 2547697 = 1910773) (by norm_num)
theorem B3396929 : Blo 2263435 3396929 := bstep (se 2 (by rfl) ⟨1273848, by rfl⟩ : syracuseStep 3396929 = 2547697) B2547697
theorem B2264619 : Blo 2263435 2264619 := bstep (se 1 (by rfl) ⟨1698464, by rfl⟩ : syracuseStep 2264619 = 3396929) B3396929
theorem B2757737 : Blo 2263435 2757737 := bbase (se 2 (by rfl) ⟨1034151, by rfl⟩ : syracuseStep 2757737 = 2068303) (by norm_num)
theorem B7353965 : Blo 2263435 7353965 := bstep (se 3 (by rfl) ⟨1378868, by rfl⟩ : syracuseStep 7353965 = 2757737) B2757737
theorem B4902643 : Blo 2263435 4902643 := bstep (se 1 (by rfl) ⟨3676982, by rfl⟩ : syracuseStep 4902643 = 7353965) B7353965
theorem B6536857 : Blo 2263435 6536857 := bstep (se 2 (by rfl) ⟨2451321, by rfl⟩ : syracuseStep 6536857 = 4902643) B4902643
theorem B8715809 : Blo 2263435 8715809 := bstep (se 2 (by rfl) ⟨3268428, by rfl⟩ : syracuseStep 8715809 = 6536857) B6536857
theorem B5810539 : Blo 2263435 5810539 := bstep (se 1 (by rfl) ⟨4357904, by rfl⟩ : syracuseStep 5810539 = 8715809) B8715809
theorem B7747385 : Blo 2263435 7747385 := bstep (se 2 (by rfl) ⟨2905269, by rfl⟩ : syracuseStep 7747385 = 5810539) B5810539
theorem B20659693 : Blo 2263435 20659693 := bstep (se 3 (by rfl) ⟨3873692, by rfl⟩ : syracuseStep 20659693 = 7747385) B7747385
theorem B27546257 : Blo 2263435 27546257 := bstep (se 2 (by rfl) ⟨10329846, by rfl⟩ : syracuseStep 27546257 = 20659693) B20659693
theorem B18364171 : Blo 2263435 18364171 := bstep (se 1 (by rfl) ⟨13773128, by rfl⟩ : syracuseStep 18364171 = 27546257) B27546257
theorem B24485561 : Blo 2263435 24485561 := bstep (se 2 (by rfl) ⟨9182085, by rfl⟩ : syracuseStep 24485561 = 18364171) B18364171
theorem B16323707 : Blo 2263435 16323707 := bstep (se 1 (by rfl) ⟨12242780, by rfl⟩ : syracuseStep 16323707 = 24485561) B24485561
theorem B10882471 : Blo 2263435 10882471 := bstep (se 1 (by rfl) ⟨8161853, by rfl⟩ : syracuseStep 10882471 = 16323707) B16323707
theorem B14509961 : Blo 2263435 14509961 := bstep (se 2 (by rfl) ⟨5441235, by rfl⟩ : syracuseStep 14509961 = 10882471) B10882471
theorem B9673307 : Blo 2263435 9673307 := bstep (se 1 (by rfl) ⟨7254980, by rfl⟩ : syracuseStep 9673307 = 14509961) B14509961
theorem B6448871 : Blo 2263435 6448871 := bstep (se 1 (by rfl) ⟨4836653, by rfl⟩ : syracuseStep 6448871 = 9673307) B9673307
theorem B4299247 : Blo 2263435 4299247 := bstep (se 1 (by rfl) ⟨3224435, by rfl⟩ : syracuseStep 4299247 = 6448871) B6448871
theorem B5732329 : Blo 2263435 5732329 := bstep (se 2 (by rfl) ⟨2149623, by rfl⟩ : syracuseStep 5732329 = 4299247) B4299247
theorem B7643105 : Blo 2263435 7643105 := bstep (se 2 (by rfl) ⟨2866164, by rfl⟩ : syracuseStep 7643105 = 5732329) B5732329
theorem B5095403 : Blo 2263435 5095403 := bstep (se 1 (by rfl) ⟨3821552, by rfl⟩ : syracuseStep 5095403 = 7643105) B7643105
theorem B3396935 : Blo 2263435 3396935 := bstep (se 1 (by rfl) ⟨2547701, by rfl⟩ : syracuseStep 3396935 = 5095403) B5095403
theorem B2264623 : Blo 2263435 2264623 := bstep (se 1 (by rfl) ⟨1698467, by rfl⟩ : syracuseStep 2264623 = 3396935) B3396935
theorem B3396941 : Blo 2263435 3396941 := bbase (se 3 (by rfl) ⟨636926, by rfl⟩ : syracuseStep 3396941 = 1273853) (by norm_num)
theorem B2264627 : Blo 2263435 2264627 := bstep (se 1 (by rfl) ⟨1698470, by rfl⟩ : syracuseStep 2264627 = 3396941) B3396941
theorem B5095421 : Blo 2263435 5095421 := bbase (se 3 (by rfl) ⟨955391, by rfl⟩ : syracuseStep 5095421 = 1910783) (by norm_num)
theorem B3396947 : Blo 2263435 3396947 := bstep (se 1 (by rfl) ⟨2547710, by rfl⟩ : syracuseStep 3396947 = 5095421) B5095421
theorem B2264631 : Blo 2263435 2264631 := bstep (se 1 (by rfl) ⟨1698473, by rfl⟩ : syracuseStep 2264631 = 3396947) B3396947
theorem B3821573 : Blo 2263435 3821573 := bbase (se 4 (by rfl) ⟨358272, by rfl⟩ : syracuseStep 3821573 = 716545) (by norm_num)
theorem B2547715 : Blo 2263435 2547715 := bstep (se 1 (by rfl) ⟨1910786, by rfl⟩ : syracuseStep 2547715 = 3821573) B3821573
theorem B3396953 : Blo 2263435 3396953 := bstep (se 2 (by rfl) ⟨1273857, by rfl⟩ : syracuseStep 3396953 = 2547715) B2547715
theorem B2264635 : Blo 2263435 2264635 := bstep (se 1 (by rfl) ⟨1698476, by rfl⟩ : syracuseStep 2264635 = 3396953) B3396953
theorem B17197109 : Blo 2263435 17197109 := bbase (se 5 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 17197109 = 1612229) (by norm_num)
theorem B11464739 : Blo 2263435 11464739 := bstep (se 1 (by rfl) ⟨8598554, by rfl⟩ : syracuseStep 11464739 = 17197109) B17197109
theorem B7643159 : Blo 2263435 7643159 := bstep (se 1 (by rfl) ⟨5732369, by rfl⟩ : syracuseStep 7643159 = 11464739) B11464739
theorem B5095439 : Blo 2263435 5095439 := bstep (se 1 (by rfl) ⟨3821579, by rfl⟩ : syracuseStep 5095439 = 7643159) B7643159
theorem B3396959 : Blo 2263435 3396959 := bstep (se 1 (by rfl) ⟨2547719, by rfl⟩ : syracuseStep 3396959 = 5095439) B5095439
theorem B2264639 : Blo 2263435 2264639 := bstep (se 1 (by rfl) ⟨1698479, by rfl⟩ : syracuseStep 2264639 = 3396959) B3396959
theorem B3396965 : Blo 2263435 3396965 := bbase (se 4 (by rfl) ⟨318465, by rfl⟩ : syracuseStep 3396965 = 636931) (by norm_num)
theorem B2264643 : Blo 2263435 2264643 := bstep (se 1 (by rfl) ⟨1698482, by rfl⟩ : syracuseStep 2264643 = 3396965) B3396965
theorem B4299293 : Blo 2263435 4299293 := bbase (se 3 (by rfl) ⟨806117, by rfl⟩ : syracuseStep 4299293 = 1612235) (by norm_num)
theorem B2866195 : Blo 2263435 2866195 := bstep (se 1 (by rfl) ⟨2149646, by rfl⟩ : syracuseStep 2866195 = 4299293) B4299293
theorem B3821593 : Blo 2263435 3821593 := bstep (se 2 (by rfl) ⟨1433097, by rfl⟩ : syracuseStep 3821593 = 2866195) B2866195
theorem B5095457 : Blo 2263435 5095457 := bstep (se 2 (by rfl) ⟨1910796, by rfl⟩ : syracuseStep 5095457 = 3821593) B3821593
theorem B3396971 : Blo 2263435 3396971 := bstep (se 1 (by rfl) ⟨2547728, by rfl⟩ : syracuseStep 3396971 = 5095457) B5095457
theorem B2264647 : Blo 2263435 2264647 := bstep (se 1 (by rfl) ⟨1698485, by rfl⟩ : syracuseStep 2264647 = 3396971) B3396971
theorem B2547733 : Blo 2263435 2547733 := bbase (se 6 (by rfl) ⟨59712, by rfl⟩ : syracuseStep 2547733 = 119425) (by norm_num)
theorem B3396977 : Blo 2263435 3396977 := bstep (se 2 (by rfl) ⟨1273866, by rfl⟩ : syracuseStep 3396977 = 2547733) B2547733
theorem B2264651 : Blo 2263435 2264651 := bstep (se 1 (by rfl) ⟨1698488, by rfl⟩ : syracuseStep 2264651 = 3396977) B3396977
theorem B2866205 : Blo 2263435 2866205 := bbase (se 3 (by rfl) ⟨537413, by rfl⟩ : syracuseStep 2866205 = 1074827) (by norm_num)
theorem B7643213 : Blo 2263435 7643213 := bstep (se 3 (by rfl) ⟨1433102, by rfl⟩ : syracuseStep 7643213 = 2866205) B2866205
theorem B5095475 : Blo 2263435 5095475 := bstep (se 1 (by rfl) ⟨3821606, by rfl⟩ : syracuseStep 5095475 = 7643213) B7643213
theorem B3396983 : Blo 2263435 3396983 := bstep (se 1 (by rfl) ⟨2547737, by rfl⟩ : syracuseStep 3396983 = 5095475) B5095475
theorem B2264655 : Blo 2263435 2264655 := bstep (se 1 (by rfl) ⟨1698491, by rfl⟩ : syracuseStep 2264655 = 3396983) B3396983
theorem B3396989 : Blo 2263435 3396989 := bbase (se 3 (by rfl) ⟨636935, by rfl⟩ : syracuseStep 3396989 = 1273871) (by norm_num)
theorem B2264659 : Blo 2263435 2264659 := bstep (se 1 (by rfl) ⟨1698494, by rfl⟩ : syracuseStep 2264659 = 3396989) B3396989
theorem B5095493 : Blo 2263435 5095493 := bbase (se 4 (by rfl) ⟨477702, by rfl⟩ : syracuseStep 5095493 = 955405) (by norm_num)
theorem B3396995 : Blo 2263435 3396995 := bstep (se 1 (by rfl) ⟨2547746, by rfl⟩ : syracuseStep 3396995 = 5095493) B5095493
theorem B2264663 : Blo 2263435 2264663 := bstep (se 1 (by rfl) ⟨1698497, by rfl⟩ : syracuseStep 2264663 = 3396995) B3396995
theorem B6448997 : Blo 2263435 6448997 := bbase (se 4 (by rfl) ⟨604593, by rfl⟩ : syracuseStep 6448997 = 1209187) (by norm_num)
theorem B4299331 : Blo 2263435 4299331 := bstep (se 1 (by rfl) ⟨3224498, by rfl⟩ : syracuseStep 4299331 = 6448997) B6448997
theorem B5732441 : Blo 2263435 5732441 := bstep (se 2 (by rfl) ⟨2149665, by rfl⟩ : syracuseStep 5732441 = 4299331) B4299331
theorem B3821627 : Blo 2263435 3821627 := bstep (se 1 (by rfl) ⟨2866220, by rfl⟩ : syracuseStep 3821627 = 5732441) B5732441
theorem B2547751 : Blo 2263435 2547751 := bstep (se 1 (by rfl) ⟨1910813, by rfl⟩ : syracuseStep 2547751 = 3821627) B3821627
theorem B3397001 : Blo 2263435 3397001 := bstep (se 2 (by rfl) ⟨1273875, by rfl⟩ : syracuseStep 3397001 = 2547751) B2547751
theorem B2264667 : Blo 2263435 2264667 := bstep (se 1 (by rfl) ⟨1698500, by rfl⟩ : syracuseStep 2264667 = 3397001) B3397001
theorem B11464901 : Blo 2263435 11464901 := bbase (se 4 (by rfl) ⟨1074834, by rfl⟩ : syracuseStep 11464901 = 2149669) (by norm_num)
theorem B7643267 : Blo 2263435 7643267 := bstep (se 1 (by rfl) ⟨5732450, by rfl⟩ : syracuseStep 7643267 = 11464901) B11464901
theorem B5095511 : Blo 2263435 5095511 := bstep (se 1 (by rfl) ⟨3821633, by rfl⟩ : syracuseStep 5095511 = 7643267) B7643267
theorem B3397007 : Blo 2263435 3397007 := bstep (se 1 (by rfl) ⟨2547755, by rfl⟩ : syracuseStep 3397007 = 5095511) B5095511
theorem B2264671 : Blo 2263435 2264671 := bstep (se 1 (by rfl) ⟨1698503, by rfl⟩ : syracuseStep 2264671 = 3397007) B3397007
theorem B3397013 : Blo 2263435 3397013 := bbase (se 6 (by rfl) ⟨79617, by rfl⟩ : syracuseStep 3397013 = 159235) (by norm_num)
theorem B2264675 : Blo 2263435 2264675 := bstep (se 1 (by rfl) ⟨1698506, by rfl⟩ : syracuseStep 2264675 = 3397013) B3397013
theorem B4836773 : Blo 2263435 4836773 := bbase (se 4 (by rfl) ⟨453447, by rfl⟩ : syracuseStep 4836773 = 906895) (by norm_num)
theorem B12898061 : Blo 2263435 12898061 := bstep (se 3 (by rfl) ⟨2418386, by rfl⟩ : syracuseStep 12898061 = 4836773) B4836773
theorem B8598707 : Blo 2263435 8598707 := bstep (se 1 (by rfl) ⟨6449030, by rfl⟩ : syracuseStep 8598707 = 12898061) B12898061
theorem B5732471 : Blo 2263435 5732471 := bstep (se 1 (by rfl) ⟨4299353, by rfl⟩ : syracuseStep 5732471 = 8598707) B8598707
theorem B3821647 : Blo 2263435 3821647 := bstep (se 1 (by rfl) ⟨2866235, by rfl⟩ : syracuseStep 3821647 = 5732471) B5732471
theorem B5095529 : Blo 2263435 5095529 := bstep (se 2 (by rfl) ⟨1910823, by rfl⟩ : syracuseStep 5095529 = 3821647) B3821647
theorem B3397019 : Blo 2263435 3397019 := bstep (se 1 (by rfl) ⟨2547764, by rfl⟩ : syracuseStep 3397019 = 5095529) B5095529
theorem B2264679 : Blo 2263435 2264679 := bstep (se 1 (by rfl) ⟨1698509, by rfl⟩ : syracuseStep 2264679 = 3397019) B3397019
theorem B2547769 : Blo 2263435 2547769 := bbase (se 2 (by rfl) ⟨955413, by rfl⟩ : syracuseStep 2547769 = 1910827) (by norm_num)
theorem B3397025 : Blo 2263435 3397025 := bstep (se 2 (by rfl) ⟨1273884, by rfl⟩ : syracuseStep 3397025 = 2547769) B2547769
theorem B2264683 : Blo 2263435 2264683 := bstep (se 1 (by rfl) ⟨1698512, by rfl⟩ : syracuseStep 2264683 = 3397025) B3397025
theorem B3443381 : Blo 2263435 3443381 := bbase (se 5 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 3443381 = 322817) (by norm_num)
theorem B2295587 : Blo 2263435 2295587 := bstep (se 1 (by rfl) ⟨1721690, by rfl⟩ : syracuseStep 2295587 = 3443381) B3443381
theorem B6121565 : Blo 2263435 6121565 := bstep (se 3 (by rfl) ⟨1147793, by rfl⟩ : syracuseStep 6121565 = 2295587) B2295587
theorem B4081043 : Blo 2263435 4081043 := bstep (se 1 (by rfl) ⟨3060782, by rfl⟩ : syracuseStep 4081043 = 6121565) B6121565
theorem B2720695 : Blo 2263435 2720695 := bstep (se 1 (by rfl) ⟨2040521, by rfl⟩ : syracuseStep 2720695 = 4081043) B4081043
theorem B3627593 : Blo 2263435 3627593 := bstep (se 2 (by rfl) ⟨1360347, by rfl⟩ : syracuseStep 3627593 = 2720695) B2720695
theorem B2418395 : Blo 2263435 2418395 := bstep (se 1 (by rfl) ⟨1813796, by rfl⟩ : syracuseStep 2418395 = 3627593) B3627593
theorem B6449053 : Blo 2263435 6449053 := bstep (se 3 (by rfl) ⟨1209197, by rfl⟩ : syracuseStep 6449053 = 2418395) B2418395
theorem B8598737 : Blo 2263435 8598737 := bstep (se 2 (by rfl) ⟨3224526, by rfl⟩ : syracuseStep 8598737 = 6449053) B6449053
theorem B5732491 : Blo 2263435 5732491 := bstep (se 1 (by rfl) ⟨4299368, by rfl⟩ : syracuseStep 5732491 = 8598737) B8598737
theorem B7643321 : Blo 2263435 7643321 := bstep (se 2 (by rfl) ⟨2866245, by rfl⟩ : syracuseStep 7643321 = 5732491) B5732491
theorem B5095547 : Blo 2263435 5095547 := bstep (se 1 (by rfl) ⟨3821660, by rfl⟩ : syracuseStep 5095547 = 7643321) B7643321
theorem B3397031 : Blo 2263435 3397031 := bstep (se 1 (by rfl) ⟨2547773, by rfl⟩ : syracuseStep 3397031 = 5095547) B5095547
theorem B2264687 : Blo 2263435 2264687 := bstep (se 1 (by rfl) ⟨1698515, by rfl⟩ : syracuseStep 2264687 = 3397031) B3397031
theorem B3397037 : Blo 2263435 3397037 := bbase (se 3 (by rfl) ⟨636944, by rfl⟩ : syracuseStep 3397037 = 1273889) (by norm_num)
theorem B2264691 : Blo 2263435 2264691 := bstep (se 1 (by rfl) ⟨1698518, by rfl⟩ : syracuseStep 2264691 = 3397037) B3397037
theorem B5095565 : Blo 2263435 5095565 := bbase (se 3 (by rfl) ⟨955418, by rfl⟩ : syracuseStep 5095565 = 1910837) (by norm_num)
theorem B3397043 : Blo 2263435 3397043 := bstep (se 1 (by rfl) ⟨2547782, by rfl⟩ : syracuseStep 3397043 = 5095565) B5095565
theorem B2264695 : Blo 2263435 2264695 := bstep (se 1 (by rfl) ⟨1698521, by rfl⟩ : syracuseStep 2264695 = 3397043) B3397043
theorem B2866261 : Blo 2263435 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B3821681 : Blo 2263435 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B2547787 : Blo 2263435 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B3397049 : Blo 2263435 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B2264699 : Blo 2263435 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B97945685 : Blo 2263435 97945685 := bbase (se 8 (by rfl) ⟨573900, by rfl⟩ : syracuseStep 97945685 = 1147801) (by norm_num)
theorem B65297123 : Blo 2263435 65297123 := bstep (se 1 (by rfl) ⟨48972842, by rfl⟩ : syracuseStep 65297123 = 97945685) B97945685
theorem B43531415 : Blo 2263435 43531415 := bstep (se 1 (by rfl) ⟨32648561, by rfl⟩ : syracuseStep 43531415 = 65297123) B65297123
theorem B29020943 : Blo 2263435 29020943 := bstep (se 1 (by rfl) ⟨21765707, by rfl⟩ : syracuseStep 29020943 = 43531415) B43531415
theorem B19347295 : Blo 2263435 19347295 := bstep (se 1 (by rfl) ⟨14510471, by rfl⟩ : syracuseStep 19347295 = 29020943) B29020943
theorem B25796393 : Blo 2263435 25796393 := bstep (se 2 (by rfl) ⟨9673647, by rfl⟩ : syracuseStep 25796393 = 19347295) B19347295
theorem B17197595 : Blo 2263435 17197595 := bstep (se 1 (by rfl) ⟨12898196, by rfl⟩ : syracuseStep 17197595 = 25796393) B25796393
theorem B11465063 : Blo 2263435 11465063 := bstep (se 1 (by rfl) ⟨8598797, by rfl⟩ : syracuseStep 11465063 = 17197595) B17197595
theorem B7643375 : Blo 2263435 7643375 := bstep (se 1 (by rfl) ⟨5732531, by rfl⟩ : syracuseStep 7643375 = 11465063) B11465063
theorem B5095583 : Blo 2263435 5095583 := bstep (se 1 (by rfl) ⟨3821687, by rfl⟩ : syracuseStep 5095583 = 7643375) B7643375
theorem B3397055 : Blo 2263435 3397055 := bstep (se 1 (by rfl) ⟨2547791, by rfl⟩ : syracuseStep 3397055 = 5095583) B5095583
theorem B2264703 : Blo 2263435 2264703 := bstep (se 1 (by rfl) ⟨1698527, by rfl⟩ : syracuseStep 2264703 = 3397055) B3397055
theorem B3397061 : Blo 2263435 3397061 := bbase (se 4 (by rfl) ⟨318474, by rfl⟩ : syracuseStep 3397061 = 636949) (by norm_num)
theorem B2264707 : Blo 2263435 2264707 := bstep (se 1 (by rfl) ⟨1698530, by rfl⟩ : syracuseStep 2264707 = 3397061) B3397061
theorem B3821701 : Blo 2263435 3821701 := bbase (se 4 (by rfl) ⟨358284, by rfl⟩ : syracuseStep 3821701 = 716569) (by norm_num)
theorem B5095601 : Blo 2263435 5095601 := bstep (se 2 (by rfl) ⟨1910850, by rfl⟩ : syracuseStep 5095601 = 3821701) B3821701
theorem B3397067 : Blo 2263435 3397067 := bstep (se 1 (by rfl) ⟨2547800, by rfl⟩ : syracuseStep 3397067 = 5095601) B5095601
theorem B2264711 : Blo 2263435 2264711 := bstep (se 1 (by rfl) ⟨1698533, by rfl⟩ : syracuseStep 2264711 = 3397067) B3397067
theorem B2547805 : Blo 2263435 2547805 := bbase (se 3 (by rfl) ⟨477713, by rfl⟩ : syracuseStep 2547805 = 955427) (by norm_num)
theorem B3397073 : Blo 2263435 3397073 := bstep (se 2 (by rfl) ⟨1273902, by rfl⟩ : syracuseStep 3397073 = 2547805) B2547805
theorem B2264715 : Blo 2263435 2264715 := bstep (se 1 (by rfl) ⟨1698536, by rfl⟩ : syracuseStep 2264715 = 3397073) B3397073
theorem B7643429 : Blo 2263435 7643429 := bbase (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) (by norm_num)
theorem B5095619 : Blo 2263435 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B3397079 : Blo 2263435 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B2264719 : Blo 2263435 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B3397085 : Blo 2263435 3397085 := bbase (se 3 (by rfl) ⟨636953, by rfl⟩ : syracuseStep 3397085 = 1273907) (by norm_num)
theorem B2264723 : Blo 2263435 2264723 := bstep (se 1 (by rfl) ⟨1698542, by rfl⟩ : syracuseStep 2264723 = 3397085) B3397085
theorem B5095637 : Blo 2263435 5095637 := bbase (se 7 (by rfl) ⟨59714, by rfl⟩ : syracuseStep 5095637 = 119429) (by norm_num)
theorem B3397091 : Blo 2263435 3397091 := bstep (se 1 (by rfl) ⟨2547818, by rfl⟩ : syracuseStep 3397091 = 5095637) B5095637
theorem B2264727 : Blo 2263435 2264727 := bstep (se 1 (by rfl) ⟨1698545, by rfl⟩ : syracuseStep 2264727 = 3397091) B3397091
theorem B2582585 : Blo 2263435 2582585 := bbase (se 2 (by rfl) ⟨968469, by rfl⟩ : syracuseStep 2582585 = 1936939) (by norm_num)
theorem B27547573 : Blo 2263435 27547573 := bstep (se 5 (by rfl) ⟨1291292, by rfl⟩ : syracuseStep 27547573 = 2582585) B2582585
theorem B36730097 : Blo 2263435 36730097 := bstep (se 2 (by rfl) ⟨13773786, by rfl⟩ : syracuseStep 36730097 = 27547573) B27547573
theorem B24486731 : Blo 2263435 24486731 := bstep (se 1 (by rfl) ⟨18365048, by rfl⟩ : syracuseStep 24486731 = 36730097) B36730097
theorem B16324487 : Blo 2263435 16324487 := bstep (se 1 (by rfl) ⟨12243365, by rfl⟩ : syracuseStep 16324487 = 24486731) B24486731
theorem B10882991 : Blo 2263435 10882991 := bstep (se 1 (by rfl) ⟨8162243, by rfl⟩ : syracuseStep 10882991 = 16324487) B16324487
theorem B7255327 : Blo 2263435 7255327 := bstep (se 1 (by rfl) ⟨5441495, by rfl⟩ : syracuseStep 7255327 = 10882991) B10882991
theorem B9673769 : Blo 2263435 9673769 := bstep (se 2 (by rfl) ⟨3627663, by rfl⟩ : syracuseStep 9673769 = 7255327) B7255327
theorem B6449179 : Blo 2263435 6449179 := bstep (se 1 (by rfl) ⟨4836884, by rfl⟩ : syracuseStep 6449179 = 9673769) B9673769
theorem B8598905 : Blo 2263435 8598905 := bstep (se 2 (by rfl) ⟨3224589, by rfl⟩ : syracuseStep 8598905 = 6449179) B6449179
theorem B5732603 : Blo 2263435 5732603 := bstep (se 1 (by rfl) ⟨4299452, by rfl⟩ : syracuseStep 5732603 = 8598905) B8598905
theorem B3821735 : Blo 2263435 3821735 := bstep (se 1 (by rfl) ⟨2866301, by rfl⟩ : syracuseStep 3821735 = 5732603) B5732603
theorem B2547823 : Blo 2263435 2547823 := bstep (se 1 (by rfl) ⟨1910867, by rfl⟩ : syracuseStep 2547823 = 3821735) B3821735
theorem B3397097 : Blo 2263435 3397097 := bstep (se 2 (by rfl) ⟨1273911, by rfl⟩ : syracuseStep 3397097 = 2547823) B2547823
theorem B2264731 : Blo 2263435 2264731 := bstep (se 1 (by rfl) ⟨1698548, by rfl⟩ : syracuseStep 2264731 = 3397097) B3397097
theorem B14510677 : Blo 2263435 14510677 := bbase (se 8 (by rfl) ⟨85023, by rfl⟩ : syracuseStep 14510677 = 170047) (by norm_num)
theorem B19347569 : Blo 2263435 19347569 := bstep (se 2 (by rfl) ⟨7255338, by rfl⟩ : syracuseStep 19347569 = 14510677) B14510677
theorem B12898379 : Blo 2263435 12898379 := bstep (se 1 (by rfl) ⟨9673784, by rfl⟩ : syracuseStep 12898379 = 19347569) B19347569
theorem B8598919 : Blo 2263435 8598919 := bstep (se 1 (by rfl) ⟨6449189, by rfl⟩ : syracuseStep 8598919 = 12898379) B12898379
theorem B11465225 : Blo 2263435 11465225 := bstep (se 2 (by rfl) ⟨4299459, by rfl⟩ : syracuseStep 11465225 = 8598919) B8598919
theorem B7643483 : Blo 2263435 7643483 := bstep (se 1 (by rfl) ⟨5732612, by rfl⟩ : syracuseStep 7643483 = 11465225) B11465225
theorem B5095655 : Blo 2263435 5095655 := bstep (se 1 (by rfl) ⟨3821741, by rfl⟩ : syracuseStep 5095655 = 7643483) B7643483
theorem B3397103 : Blo 2263435 3397103 := bstep (se 1 (by rfl) ⟨2547827, by rfl⟩ : syracuseStep 3397103 = 5095655) B5095655
theorem B2264735 : Blo 2263435 2264735 := bstep (se 1 (by rfl) ⟨1698551, by rfl⟩ : syracuseStep 2264735 = 3397103) B3397103
theorem B3397109 : Blo 2263435 3397109 := bbase (se 5 (by rfl) ⟨159239, by rfl⟩ : syracuseStep 3397109 = 318479) (by norm_num)
theorem B2264739 : Blo 2263435 2264739 := bstep (se 1 (by rfl) ⟨1698554, by rfl⟩ : syracuseStep 2264739 = 3397109) B3397109
theorem B5441525 : Blo 2263435 5441525 := bbase (se 5 (by rfl) ⟨255071, by rfl⟩ : syracuseStep 5441525 = 510143) (by norm_num)
theorem B3627683 : Blo 2263435 3627683 := bstep (se 1 (by rfl) ⟨2720762, by rfl⟩ : syracuseStep 3627683 = 5441525) B5441525
theorem B2418455 : Blo 2263435 2418455 := bstep (se 1 (by rfl) ⟨1813841, by rfl⟩ : syracuseStep 2418455 = 3627683) B3627683
theorem B6449213 : Blo 2263435 6449213 := bstep (se 3 (by rfl) ⟨1209227, by rfl⟩ : syracuseStep 6449213 = 2418455) B2418455
theorem B4299475 : Blo 2263435 4299475 := bstep (se 1 (by rfl) ⟨3224606, by rfl⟩ : syracuseStep 4299475 = 6449213) B6449213
theorem B5732633 : Blo 2263435 5732633 := bstep (se 2 (by rfl) ⟨2149737, by rfl⟩ : syracuseStep 5732633 = 4299475) B4299475
theorem B3821755 : Blo 2263435 3821755 := bstep (se 1 (by rfl) ⟨2866316, by rfl⟩ : syracuseStep 3821755 = 5732633) B5732633
theorem B5095673 : Blo 2263435 5095673 := bstep (se 2 (by rfl) ⟨1910877, by rfl⟩ : syracuseStep 5095673 = 3821755) B3821755
theorem B3397115 : Blo 2263435 3397115 := bstep (se 1 (by rfl) ⟨2547836, by rfl⟩ : syracuseStep 3397115 = 5095673) B5095673
theorem B2264743 : Blo 2263435 2264743 := bstep (se 1 (by rfl) ⟨1698557, by rfl⟩ : syracuseStep 2264743 = 3397115) B3397115
theorem B2547841 : Blo 2263435 2547841 := bbase (se 2 (by rfl) ⟨955440, by rfl⟩ : syracuseStep 2547841 = 1910881) (by norm_num)
theorem B3397121 : Blo 2263435 3397121 := bstep (se 2 (by rfl) ⟨1273920, by rfl⟩ : syracuseStep 3397121 = 2547841) B2547841
theorem B2264747 : Blo 2263435 2264747 := bstep (se 1 (by rfl) ⟨1698560, by rfl⟩ : syracuseStep 2264747 = 3397121) B3397121
theorem B5732653 : Blo 2263435 5732653 := bbase (se 3 (by rfl) ⟨1074872, by rfl⟩ : syracuseStep 5732653 = 2149745) (by norm_num)
theorem B7643537 : Blo 2263435 7643537 := bstep (se 2 (by rfl) ⟨2866326, by rfl⟩ : syracuseStep 7643537 = 5732653) B5732653
theorem B5095691 : Blo 2263435 5095691 := bstep (se 1 (by rfl) ⟨3821768, by rfl⟩ : syracuseStep 5095691 = 7643537) B7643537
theorem B3397127 : Blo 2263435 3397127 := bstep (se 1 (by rfl) ⟨2547845, by rfl⟩ : syracuseStep 3397127 = 5095691) B5095691
theorem B2264751 : Blo 2263435 2264751 := bstep (se 1 (by rfl) ⟨1698563, by rfl⟩ : syracuseStep 2264751 = 3397127) B3397127
theorem B3397133 : Blo 2263435 3397133 := bbase (se 3 (by rfl) ⟨636962, by rfl⟩ : syracuseStep 3397133 = 1273925) (by norm_num)
theorem B2264755 : Blo 2263435 2264755 := bstep (se 1 (by rfl) ⟨1698566, by rfl⟩ : syracuseStep 2264755 = 3397133) B3397133
theorem B5095709 : Blo 2263435 5095709 := bbase (se 3 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 5095709 = 1910891) (by norm_num)
theorem B3397139 : Blo 2263435 3397139 := bstep (se 1 (by rfl) ⟨2547854, by rfl⟩ : syracuseStep 3397139 = 5095709) B5095709
theorem B2264759 : Blo 2263435 2264759 := bstep (se 1 (by rfl) ⟨1698569, by rfl⟩ : syracuseStep 2264759 = 3397139) B3397139
theorem B3821789 : Blo 2263435 3821789 := bbase (se 3 (by rfl) ⟨716585, by rfl⟩ : syracuseStep 3821789 = 1433171) (by norm_num)
theorem B2547859 : Blo 2263435 2547859 := bstep (se 1 (by rfl) ⟨1910894, by rfl⟩ : syracuseStep 2547859 = 3821789) B3821789
theorem B3397145 : Blo 2263435 3397145 := bstep (se 2 (by rfl) ⟨1273929, by rfl⟩ : syracuseStep 3397145 = 2547859) B2547859
theorem B2264763 : Blo 2263435 2264763 := bstep (se 1 (by rfl) ⟨1698572, by rfl⟩ : syracuseStep 2264763 = 3397145) B3397145
theorem B5441581 : Blo 2263435 5441581 := bbase (se 3 (by rfl) ⟨1020296, by rfl⟩ : syracuseStep 5441581 = 2040593) (by norm_num)
theorem B7255441 : Blo 2263435 7255441 := bstep (se 2 (by rfl) ⟨2720790, by rfl⟩ : syracuseStep 7255441 = 5441581) B5441581
theorem B9673921 : Blo 2263435 9673921 := bstep (se 2 (by rfl) ⟨3627720, by rfl⟩ : syracuseStep 9673921 = 7255441) B7255441
theorem B12898561 : Blo 2263435 12898561 := bstep (se 2 (by rfl) ⟨4836960, by rfl⟩ : syracuseStep 12898561 = 9673921) B9673921
theorem B17198081 : Blo 2263435 17198081 := bstep (se 2 (by rfl) ⟨6449280, by rfl⟩ : syracuseStep 17198081 = 12898561) B12898561
theorem B11465387 : Blo 2263435 11465387 := bstep (se 1 (by rfl) ⟨8599040, by rfl⟩ : syracuseStep 11465387 = 17198081) B17198081
theorem B7643591 : Blo 2263435 7643591 := bstep (se 1 (by rfl) ⟨5732693, by rfl⟩ : syracuseStep 7643591 = 11465387) B11465387
theorem B5095727 : Blo 2263435 5095727 := bstep (se 1 (by rfl) ⟨3821795, by rfl⟩ : syracuseStep 5095727 = 7643591) B7643591
theorem B3397151 : Blo 2263435 3397151 := bstep (se 1 (by rfl) ⟨2547863, by rfl⟩ : syracuseStep 3397151 = 5095727) B5095727
theorem B2264767 : Blo 2263435 2264767 := bstep (se 1 (by rfl) ⟨1698575, by rfl⟩ : syracuseStep 2264767 = 3397151) B3397151
theorem B3397157 : Blo 2263435 3397157 := bbase (se 4 (by rfl) ⟨318483, by rfl⟩ : syracuseStep 3397157 = 636967) (by norm_num)
theorem B2264771 : Blo 2263435 2264771 := bstep (se 1 (by rfl) ⟨1698578, by rfl⟩ : syracuseStep 2264771 = 3397157) B3397157
theorem B2866357 : Blo 2263435 2866357 := bbase (se 5 (by rfl) ⟨134360, by rfl⟩ : syracuseStep 2866357 = 268721) (by norm_num)
theorem B3821809 : Blo 2263435 3821809 := bstep (se 2 (by rfl) ⟨1433178, by rfl⟩ : syracuseStep 3821809 = 2866357) B2866357
theorem B5095745 : Blo 2263435 5095745 := bstep (se 2 (by rfl) ⟨1910904, by rfl⟩ : syracuseStep 5095745 = 3821809) B3821809
theorem B3397163 : Blo 2263435 3397163 := bstep (se 1 (by rfl) ⟨2547872, by rfl⟩ : syracuseStep 3397163 = 5095745) B5095745
theorem B2264775 : Blo 2263435 2264775 := bstep (se 1 (by rfl) ⟨1698581, by rfl⟩ : syracuseStep 2264775 = 3397163) B3397163
theorem B2547877 : Blo 2263435 2547877 := bbase (se 4 (by rfl) ⟨238863, by rfl⟩ : syracuseStep 2547877 = 477727) (by norm_num)
theorem B3397169 : Blo 2263435 3397169 := bstep (se 2 (by rfl) ⟨1273938, by rfl⟩ : syracuseStep 3397169 = 2547877) B2547877
theorem B2264779 : Blo 2263435 2264779 := bstep (se 1 (by rfl) ⟨1698584, by rfl⟩ : syracuseStep 2264779 = 3397169) B3397169
theorem B4358213 : Blo 2263435 4358213 := bbase (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) (by norm_num)
theorem B2905475 : Blo 2263435 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B30991733 : Blo 2263435 30991733 := bstep (se 5 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 30991733 = 2905475) B2905475
theorem B20661155 : Blo 2263435 20661155 := bstep (se 1 (by rfl) ⟨15495866, by rfl⟩ : syracuseStep 20661155 = 30991733) B30991733
theorem B13774103 : Blo 2263435 13774103 := bstep (se 1 (by rfl) ⟨10330577, by rfl⟩ : syracuseStep 13774103 = 20661155) B20661155
theorem B9182735 : Blo 2263435 9182735 := bstep (se 1 (by rfl) ⟨6887051, by rfl⟩ : syracuseStep 9182735 = 13774103) B13774103
theorem B6121823 : Blo 2263435 6121823 := bstep (se 1 (by rfl) ⟨4591367, by rfl⟩ : syracuseStep 6121823 = 9182735) B9182735
theorem B16324861 : Blo 2263435 16324861 := bstep (se 3 (by rfl) ⟨3060911, by rfl⟩ : syracuseStep 16324861 = 6121823) B6121823
theorem B21766481 : Blo 2263435 21766481 := bstep (se 2 (by rfl) ⟨8162430, by rfl⟩ : syracuseStep 21766481 = 16324861) B16324861
theorem B14510987 : Blo 2263435 14510987 := bstep (se 1 (by rfl) ⟨10883240, by rfl⟩ : syracuseStep 14510987 = 21766481) B21766481
theorem B9673991 : Blo 2263435 9673991 := bstep (se 1 (by rfl) ⟨7255493, by rfl⟩ : syracuseStep 9673991 = 14510987) B14510987
theorem B6449327 : Blo 2263435 6449327 := bstep (se 1 (by rfl) ⟨4836995, by rfl⟩ : syracuseStep 6449327 = 9673991) B9673991
theorem B4299551 : Blo 2263435 4299551 := bstep (se 1 (by rfl) ⟨3224663, by rfl⟩ : syracuseStep 4299551 = 6449327) B6449327
theorem B2866367 : Blo 2263435 2866367 := bstep (se 1 (by rfl) ⟨2149775, by rfl⟩ : syracuseStep 2866367 = 4299551) B4299551
theorem B7643645 : Blo 2263435 7643645 := bstep (se 3 (by rfl) ⟨1433183, by rfl⟩ : syracuseStep 7643645 = 2866367) B2866367
theorem B5095763 : Blo 2263435 5095763 := bstep (se 1 (by rfl) ⟨3821822, by rfl⟩ : syracuseStep 5095763 = 7643645) B7643645
theorem B3397175 : Blo 2263435 3397175 := bstep (se 1 (by rfl) ⟨2547881, by rfl⟩ : syracuseStep 3397175 = 5095763) B5095763
theorem B2264783 : Blo 2263435 2264783 := bstep (se 1 (by rfl) ⟨1698587, by rfl⟩ : syracuseStep 2264783 = 3397175) B3397175
theorem B3397181 : Blo 2263435 3397181 := bbase (se 3 (by rfl) ⟨636971, by rfl⟩ : syracuseStep 3397181 = 1273943) (by norm_num)
theorem B2264787 : Blo 2263435 2264787 := bstep (se 1 (by rfl) ⟨1698590, by rfl⟩ : syracuseStep 2264787 = 3397181) B3397181
theorem B5095781 : Blo 2263435 5095781 := bbase (se 4 (by rfl) ⟨477729, by rfl⟩ : syracuseStep 5095781 = 955459) (by norm_num)
theorem B3397187 : Blo 2263435 3397187 := bstep (se 1 (by rfl) ⟨2547890, by rfl⟩ : syracuseStep 3397187 = 5095781) B5095781
theorem B2264791 : Blo 2263435 2264791 := bstep (se 1 (by rfl) ⟨1698593, by rfl⟩ : syracuseStep 2264791 = 3397187) B3397187
theorem B5732765 : Blo 2263435 5732765 := bbase (se 3 (by rfl) ⟨1074893, by rfl⟩ : syracuseStep 5732765 = 2149787) (by norm_num)
theorem B3821843 : Blo 2263435 3821843 := bstep (se 1 (by rfl) ⟨2866382, by rfl⟩ : syracuseStep 3821843 = 5732765) B5732765
theorem B2547895 : Blo 2263435 2547895 := bstep (se 1 (by rfl) ⟨1910921, by rfl⟩ : syracuseStep 2547895 = 3821843) B3821843
theorem B3397193 : Blo 2263435 3397193 := bstep (se 2 (by rfl) ⟨1273947, by rfl⟩ : syracuseStep 3397193 = 2547895) B2547895
theorem B2264795 : Blo 2263435 2264795 := bstep (se 1 (by rfl) ⟨1698596, by rfl⟩ : syracuseStep 2264795 = 3397193) B3397193
theorem B4299581 : Blo 2263435 4299581 := bbase (se 3 (by rfl) ⟨806171, by rfl⟩ : syracuseStep 4299581 = 1612343) (by norm_num)
theorem B11465549 : Blo 2263435 11465549 := bstep (se 3 (by rfl) ⟨2149790, by rfl⟩ : syracuseStep 11465549 = 4299581) B4299581
theorem B7643699 : Blo 2263435 7643699 := bstep (se 1 (by rfl) ⟨5732774, by rfl⟩ : syracuseStep 7643699 = 11465549) B11465549
theorem B5095799 : Blo 2263435 5095799 := bstep (se 1 (by rfl) ⟨3821849, by rfl⟩ : syracuseStep 5095799 = 7643699) B7643699
theorem B3397199 : Blo 2263435 3397199 := bstep (se 1 (by rfl) ⟨2547899, by rfl⟩ : syracuseStep 3397199 = 5095799) B5095799
theorem B2264799 : Blo 2263435 2264799 := bstep (se 1 (by rfl) ⟨1698599, by rfl⟩ : syracuseStep 2264799 = 3397199) B3397199
theorem B3397205 : Blo 2263435 3397205 := bbase (se 8 (by rfl) ⟨19905, by rfl⟩ : syracuseStep 3397205 = 39811) (by norm_num)
theorem B2264803 : Blo 2263435 2264803 := bstep (se 1 (by rfl) ⟨1698602, by rfl⟩ : syracuseStep 2264803 = 3397205) B3397205
theorem B4358261 : Blo 2263435 4358261 := bbase (se 5 (by rfl) ⟨204293, by rfl⟩ : syracuseStep 4358261 = 408587) (by norm_num)
theorem B2905507 : Blo 2263435 2905507 := bstep (se 1 (by rfl) ⟨2179130, by rfl⟩ : syracuseStep 2905507 = 4358261) B4358261
theorem B3874009 : Blo 2263435 3874009 := bstep (se 2 (by rfl) ⟨1452753, by rfl⟩ : syracuseStep 3874009 = 2905507) B2905507
theorem B5165345 : Blo 2263435 5165345 := bstep (se 2 (by rfl) ⟨1937004, by rfl⟩ : syracuseStep 5165345 = 3874009) B3874009
theorem B3443563 : Blo 2263435 3443563 := bstep (se 1 (by rfl) ⟨2582672, by rfl⟩ : syracuseStep 3443563 = 5165345) B5165345
theorem B4591417 : Blo 2263435 4591417 := bstep (se 2 (by rfl) ⟨1721781, by rfl⟩ : syracuseStep 4591417 = 3443563) B3443563
theorem B6121889 : Blo 2263435 6121889 := bstep (se 2 (by rfl) ⟨2295708, by rfl⟩ : syracuseStep 6121889 = 4591417) B4591417
theorem B4081259 : Blo 2263435 4081259 := bstep (se 1 (by rfl) ⟨3060944, by rfl⟩ : syracuseStep 4081259 = 6121889) B6121889
theorem B2720839 : Blo 2263435 2720839 := bstep (se 1 (by rfl) ⟨2040629, by rfl⟩ : syracuseStep 2720839 = 4081259) B4081259
theorem B3627785 : Blo 2263435 3627785 := bstep (se 2 (by rfl) ⟨1360419, by rfl⟩ : syracuseStep 3627785 = 2720839) B2720839
theorem B9674093 : Blo 2263435 9674093 := bstep (se 3 (by rfl) ⟨1813892, by rfl⟩ : syracuseStep 9674093 = 3627785) B3627785
theorem B6449395 : Blo 2263435 6449395 := bstep (se 1 (by rfl) ⟨4837046, by rfl⟩ : syracuseStep 6449395 = 9674093) B9674093
theorem B8599193 : Blo 2263435 8599193 := bstep (se 2 (by rfl) ⟨3224697, by rfl⟩ : syracuseStep 8599193 = 6449395) B6449395
theorem B5732795 : Blo 2263435 5732795 := bstep (se 1 (by rfl) ⟨4299596, by rfl⟩ : syracuseStep 5732795 = 8599193) B8599193
theorem B3821863 : Blo 2263435 3821863 := bstep (se 1 (by rfl) ⟨2866397, by rfl⟩ : syracuseStep 3821863 = 5732795) B5732795
theorem B5095817 : Blo 2263435 5095817 := bstep (se 2 (by rfl) ⟨1910931, by rfl⟩ : syracuseStep 5095817 = 3821863) B3821863
theorem B3397211 : Blo 2263435 3397211 := bstep (se 1 (by rfl) ⟨2547908, by rfl⟩ : syracuseStep 3397211 = 5095817) B5095817
theorem B2264807 : Blo 2263435 2264807 := bstep (se 1 (by rfl) ⟨1698605, by rfl⟩ : syracuseStep 2264807 = 3397211) B3397211
theorem B2547913 : Blo 2263435 2547913 := bbase (se 2 (by rfl) ⟨955467, by rfl⟩ : syracuseStep 2547913 = 1910935) (by norm_num)
theorem B3397217 : Blo 2263435 3397217 := bstep (se 2 (by rfl) ⟨1273956, by rfl⟩ : syracuseStep 3397217 = 2547913) B2547913
theorem B2264811 : Blo 2263435 2264811 := bstep (se 1 (by rfl) ⟨1698608, by rfl⟩ : syracuseStep 2264811 = 3397217) B3397217
theorem B6121909 : Blo 2263435 6121909 := bbase (se 5 (by rfl) ⟨286964, by rfl⟩ : syracuseStep 6121909 = 573929) (by norm_num)
theorem B8162545 : Blo 2263435 8162545 := bstep (se 2 (by rfl) ⟨3060954, by rfl⟩ : syracuseStep 8162545 = 6121909) B6121909
theorem B10883393 : Blo 2263435 10883393 := bstep (se 2 (by rfl) ⟨4081272, by rfl⟩ : syracuseStep 10883393 = 8162545) B8162545
theorem B7255595 : Blo 2263435 7255595 := bstep (se 1 (by rfl) ⟨5441696, by rfl⟩ : syracuseStep 7255595 = 10883393) B10883393
theorem B19348253 : Blo 2263435 19348253 := bstep (se 3 (by rfl) ⟨3627797, by rfl⟩ : syracuseStep 19348253 = 7255595) B7255595
theorem B12898835 : Blo 2263435 12898835 := bstep (se 1 (by rfl) ⟨9674126, by rfl⟩ : syracuseStep 12898835 = 19348253) B19348253
theorem B8599223 : Blo 2263435 8599223 := bstep (se 1 (by rfl) ⟨6449417, by rfl⟩ : syracuseStep 8599223 = 12898835) B12898835
theorem B5732815 : Blo 2263435 5732815 := bstep (se 1 (by rfl) ⟨4299611, by rfl⟩ : syracuseStep 5732815 = 8599223) B8599223
theorem B7643753 : Blo 2263435 7643753 := bstep (se 2 (by rfl) ⟨2866407, by rfl⟩ : syracuseStep 7643753 = 5732815) B5732815
theorem B5095835 : Blo 2263435 5095835 := bstep (se 1 (by rfl) ⟨3821876, by rfl⟩ : syracuseStep 5095835 = 7643753) B7643753
theorem B3397223 : Blo 2263435 3397223 := bstep (se 1 (by rfl) ⟨2547917, by rfl⟩ : syracuseStep 3397223 = 5095835) B5095835
theorem B2264815 : Blo 2263435 2264815 := bstep (se 1 (by rfl) ⟨1698611, by rfl⟩ : syracuseStep 2264815 = 3397223) B3397223
theorem B3397229 : Blo 2263435 3397229 := bbase (se 3 (by rfl) ⟨636980, by rfl⟩ : syracuseStep 3397229 = 1273961) (by norm_num)
theorem B2264819 : Blo 2263435 2264819 := bstep (se 1 (by rfl) ⟨1698614, by rfl⟩ : syracuseStep 2264819 = 3397229) B3397229
theorem B5095853 : Blo 2263435 5095853 := bbase (se 3 (by rfl) ⟨955472, by rfl⟩ : syracuseStep 5095853 = 1910945) (by norm_num)
theorem B3397235 : Blo 2263435 3397235 := bstep (se 1 (by rfl) ⟨2547926, by rfl⟩ : syracuseStep 3397235 = 5095853) B5095853
theorem B2264823 : Blo 2263435 2264823 := bstep (se 1 (by rfl) ⟨1698617, by rfl⟩ : syracuseStep 2264823 = 3397235) B3397235
theorem B2418545 : Blo 2263435 2418545 := bbase (se 2 (by rfl) ⟨906954, by rfl⟩ : syracuseStep 2418545 = 1813909) (by norm_num)
theorem B6449453 : Blo 2263435 6449453 := bstep (se 3 (by rfl) ⟨1209272, by rfl⟩ : syracuseStep 6449453 = 2418545) B2418545
theorem B4299635 : Blo 2263435 4299635 := bstep (se 1 (by rfl) ⟨3224726, by rfl⟩ : syracuseStep 4299635 = 6449453) B6449453
theorem B2866423 : Blo 2263435 2866423 := bstep (se 1 (by rfl) ⟨2149817, by rfl⟩ : syracuseStep 2866423 = 4299635) B4299635
theorem B3821897 : Blo 2263435 3821897 := bstep (se 2 (by rfl) ⟨1433211, by rfl⟩ : syracuseStep 3821897 = 2866423) B2866423
theorem B2547931 : Blo 2263435 2547931 := bstep (se 1 (by rfl) ⟨1910948, by rfl⟩ : syracuseStep 2547931 = 3821897) B3821897
theorem B3397241 : Blo 2263435 3397241 := bstep (se 2 (by rfl) ⟨1273965, by rfl⟩ : syracuseStep 3397241 = 2547931) B2547931
theorem B2264827 : Blo 2263435 2264827 := bstep (se 1 (by rfl) ⟨1698620, by rfl⟩ : syracuseStep 2264827 = 3397241) B3397241
theorem B14345909 : Blo 2263435 14345909 := bbase (se 5 (by rfl) ⟨672464, by rfl⟩ : syracuseStep 14345909 = 1344929) (by norm_num)
theorem B9563939 : Blo 2263435 9563939 := bstep (se 1 (by rfl) ⟨7172954, by rfl⟩ : syracuseStep 9563939 = 14345909) B14345909
theorem B6375959 : Blo 2263435 6375959 := bstep (se 1 (by rfl) ⟨4781969, by rfl⟩ : syracuseStep 6375959 = 9563939) B9563939
theorem B4250639 : Blo 2263435 4250639 := bstep (se 1 (by rfl) ⟨3187979, by rfl⟩ : syracuseStep 4250639 = 6375959) B6375959
theorem B2833759 : Blo 2263435 2833759 := bstep (se 1 (by rfl) ⟨2125319, by rfl⟩ : syracuseStep 2833759 = 4250639) B4250639
theorem B3778345 : Blo 2263435 3778345 := bstep (se 2 (by rfl) ⟨1416879, by rfl⟩ : syracuseStep 3778345 = 2833759) B2833759
theorem B20151173 : Blo 2263435 20151173 := bstep (se 4 (by rfl) ⟨1889172, by rfl⟩ : syracuseStep 20151173 = 3778345) B3778345
theorem B13434115 : Blo 2263435 13434115 := bstep (se 1 (by rfl) ⟨10075586, by rfl⟩ : syracuseStep 13434115 = 20151173) B20151173
theorem B286594453 : Blo 2263435 286594453 := bstep (se 6 (by rfl) ⟨6717057, by rfl⟩ : syracuseStep 286594453 = 13434115) B13434115
theorem B382125937 : Blo 2263435 382125937 := bstep (se 2 (by rfl) ⟨143297226, by rfl⟩ : syracuseStep 382125937 = 286594453) B286594453
theorem B509501249 : Blo 2263435 509501249 := bstep (se 2 (by rfl) ⟨191062968, by rfl⟩ : syracuseStep 509501249 = 382125937) B382125937
theorem B339667499 : Blo 2263435 339667499 := bstep (se 1 (by rfl) ⟨254750624, by rfl⟩ : syracuseStep 339667499 = 509501249) B509501249
theorem B226444999 : Blo 2263435 226444999 := bstep (se 1 (by rfl) ⟨169833749, by rfl⟩ : syracuseStep 226444999 = 339667499) B339667499
theorem B301926665 : Blo 2263435 301926665 := bstep (se 2 (by rfl) ⟨113222499, by rfl⟩ : syracuseStep 301926665 = 226444999) B226444999
theorem B201284443 : Blo 2263435 201284443 := bstep (se 1 (by rfl) ⟨150963332, by rfl⟩ : syracuseStep 201284443 = 301926665) B301926665
theorem B268379257 : Blo 2263435 268379257 := bstep (se 2 (by rfl) ⟨100642221, by rfl⟩ : syracuseStep 268379257 = 201284443) B201284443
theorem B357839009 : Blo 2263435 357839009 := bstep (se 2 (by rfl) ⟨134189628, by rfl⟩ : syracuseStep 357839009 = 268379257) B268379257
theorem B238559339 : Blo 2263435 238559339 := bstep (se 1 (by rfl) ⟨178919504, by rfl⟩ : syracuseStep 238559339 = 357839009) B357839009
theorem B159039559 : Blo 2263435 159039559 := bstep (se 1 (by rfl) ⟨119279669, by rfl⟩ : syracuseStep 159039559 = 238559339) B238559339
theorem B212052745 : Blo 2263435 212052745 := bstep (se 2 (by rfl) ⟨79519779, by rfl⟩ : syracuseStep 212052745 = 159039559) B159039559
theorem B282736993 : Blo 2263435 282736993 := bstep (se 2 (by rfl) ⟨106026372, by rfl⟩ : syracuseStep 282736993 = 212052745) B212052745
theorem B376982657 : Blo 2263435 376982657 := bstep (se 2 (by rfl) ⟨141368496, by rfl⟩ : syracuseStep 376982657 = 282736993) B282736993
theorem B251321771 : Blo 2263435 251321771 := bstep (se 1 (by rfl) ⟨188491328, by rfl⟩ : syracuseStep 251321771 = 376982657) B376982657
theorem B167547847 : Blo 2263435 167547847 := bstep (se 1 (by rfl) ⟨125660885, by rfl⟩ : syracuseStep 167547847 = 251321771) B251321771
theorem B223397129 : Blo 2263435 223397129 := bstep (se 2 (by rfl) ⟨83773923, by rfl⟩ : syracuseStep 223397129 = 167547847) B167547847
theorem B148931419 : Blo 2263435 148931419 := bstep (se 1 (by rfl) ⟨111698564, by rfl⟩ : syracuseStep 148931419 = 223397129) B223397129
theorem B198575225 : Blo 2263435 198575225 := bstep (se 2 (by rfl) ⟨74465709, by rfl⟩ : syracuseStep 198575225 = 148931419) B148931419
theorem B132383483 : Blo 2263435 132383483 := bstep (se 1 (by rfl) ⟨99287612, by rfl⟩ : syracuseStep 132383483 = 198575225) B198575225
theorem B88255655 : Blo 2263435 88255655 := bstep (se 1 (by rfl) ⟨66191741, by rfl⟩ : syracuseStep 88255655 = 132383483) B132383483
theorem B58837103 : Blo 2263435 58837103 := bstep (se 1 (by rfl) ⟨44127827, by rfl⟩ : syracuseStep 58837103 = 88255655) B88255655
theorem B39224735 : Blo 2263435 39224735 := bstep (se 1 (by rfl) ⟨29418551, by rfl⟩ : syracuseStep 39224735 = 58837103) B58837103
theorem B26149823 : Blo 2263435 26149823 := bstep (se 1 (by rfl) ⟨19612367, by rfl⟩ : syracuseStep 26149823 = 39224735) B39224735
theorem B17433215 : Blo 2263435 17433215 := bstep (se 1 (by rfl) ⟨13074911, by rfl⟩ : syracuseStep 17433215 = 26149823) B26149823
theorem B11622143 : Blo 2263435 11622143 := bstep (se 1 (by rfl) ⟨8716607, by rfl⟩ : syracuseStep 11622143 = 17433215) B17433215
theorem B30992381 : Blo 2263435 30992381 := bstep (se 3 (by rfl) ⟨5811071, by rfl⟩ : syracuseStep 30992381 = 11622143) B11622143
theorem B20661587 : Blo 2263435 20661587 := bstep (se 1 (by rfl) ⟨15496190, by rfl⟩ : syracuseStep 20661587 = 30992381) B30992381
theorem B13774391 : Blo 2263435 13774391 := bstep (se 1 (by rfl) ⟨10330793, by rfl⟩ : syracuseStep 13774391 = 20661587) B20661587
theorem B9182927 : Blo 2263435 9182927 := bstep (se 1 (by rfl) ⟨6887195, by rfl⟩ : syracuseStep 9182927 = 13774391) B13774391
theorem B24487805 : Blo 2263435 24487805 := bstep (se 3 (by rfl) ⟨4591463, by rfl⟩ : syracuseStep 24487805 = 9182927) B9182927
theorem B65300813 : Blo 2263435 65300813 := bstep (se 3 (by rfl) ⟨12243902, by rfl⟩ : syracuseStep 65300813 = 24487805) B24487805
theorem B43533875 : Blo 2263435 43533875 := bstep (se 1 (by rfl) ⟨32650406, by rfl⟩ : syracuseStep 43533875 = 65300813) B65300813
theorem B29022583 : Blo 2263435 29022583 := bstep (se 1 (by rfl) ⟨21766937, by rfl⟩ : syracuseStep 29022583 = 43533875) B43533875
theorem B38696777 : Blo 2263435 38696777 := bstep (se 2 (by rfl) ⟨14511291, by rfl⟩ : syracuseStep 38696777 = 29022583) B29022583
theorem B25797851 : Blo 2263435 25797851 := bstep (se 1 (by rfl) ⟨19348388, by rfl⟩ : syracuseStep 25797851 = 38696777) B38696777
theorem B17198567 : Blo 2263435 17198567 := bstep (se 1 (by rfl) ⟨12898925, by rfl⟩ : syracuseStep 17198567 = 25797851) B25797851
theorem B11465711 : Blo 2263435 11465711 := bstep (se 1 (by rfl) ⟨8599283, by rfl⟩ : syracuseStep 11465711 = 17198567) B17198567
theorem B7643807 : Blo 2263435 7643807 := bstep (se 1 (by rfl) ⟨5732855, by rfl⟩ : syracuseStep 7643807 = 11465711) B11465711
theorem B5095871 : Blo 2263435 5095871 := bstep (se 1 (by rfl) ⟨3821903, by rfl⟩ : syracuseStep 5095871 = 7643807) B7643807
theorem B3397247 : Blo 2263435 3397247 := bstep (se 1 (by rfl) ⟨2547935, by rfl⟩ : syracuseStep 3397247 = 5095871) B5095871
theorem B2264831 : Blo 2263435 2264831 := bstep (se 1 (by rfl) ⟨1698623, by rfl⟩ : syracuseStep 2264831 = 3397247) B3397247
theorem B3397253 : Blo 2263435 3397253 := bbase (se 4 (by rfl) ⟨318492, by rfl⟩ : syracuseStep 3397253 = 636985) (by norm_num)
theorem B2264835 : Blo 2263435 2264835 := bstep (se 1 (by rfl) ⟨1698626, by rfl⟩ : syracuseStep 2264835 = 3397253) B3397253
theorem B3821917 : Blo 2263435 3821917 := bbase (se 3 (by rfl) ⟨716609, by rfl⟩ : syracuseStep 3821917 = 1433219) (by norm_num)
theorem B5095889 : Blo 2263435 5095889 := bstep (se 2 (by rfl) ⟨1910958, by rfl⟩ : syracuseStep 5095889 = 3821917) B3821917
theorem B3397259 : Blo 2263435 3397259 := bstep (se 1 (by rfl) ⟨2547944, by rfl⟩ : syracuseStep 3397259 = 5095889) B5095889
theorem B2264839 : Blo 2263435 2264839 := bstep (se 1 (by rfl) ⟨1698629, by rfl⟩ : syracuseStep 2264839 = 3397259) B3397259
theorem B2547949 : Blo 2263435 2547949 := bbase (se 3 (by rfl) ⟨477740, by rfl⟩ : syracuseStep 2547949 = 955481) (by norm_num)
theorem B3397265 : Blo 2263435 3397265 := bstep (se 2 (by rfl) ⟨1273974, by rfl⟩ : syracuseStep 3397265 = 2547949) B2547949
theorem B2264843 : Blo 2263435 2264843 := bstep (se 1 (by rfl) ⟨1698632, by rfl⟩ : syracuseStep 2264843 = 3397265) B3397265
theorem B7643861 : Blo 2263435 7643861 := bbase (se 7 (by rfl) ⟨89576, by rfl⟩ : syracuseStep 7643861 = 179153) (by norm_num)
theorem B5095907 : Blo 2263435 5095907 := bstep (se 1 (by rfl) ⟨3821930, by rfl⟩ : syracuseStep 5095907 = 7643861) B7643861
theorem B3397271 : Blo 2263435 3397271 := bstep (se 1 (by rfl) ⟨2547953, by rfl⟩ : syracuseStep 3397271 = 5095907) B5095907
theorem B2264847 : Blo 2263435 2264847 := bstep (se 1 (by rfl) ⟨1698635, by rfl⟩ : syracuseStep 2264847 = 3397271) B3397271
theorem B3397277 : Blo 2263435 3397277 := bbase (se 3 (by rfl) ⟨636989, by rfl⟩ : syracuseStep 3397277 = 1273979) (by norm_num)
theorem B2264851 : Blo 2263435 2264851 := bstep (se 1 (by rfl) ⟨1698638, by rfl⟩ : syracuseStep 2264851 = 3397277) B3397277
theorem B5095925 : Blo 2263435 5095925 := bbase (se 5 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 5095925 = 477743) (by norm_num)
theorem B3397283 : Blo 2263435 3397283 := bstep (se 1 (by rfl) ⟨2547962, by rfl⟩ : syracuseStep 3397283 = 5095925) B5095925
theorem B2264855 : Blo 2263435 2264855 := bstep (se 1 (by rfl) ⟨1698641, by rfl⟩ : syracuseStep 2264855 = 3397283) B3397283
theorem B43534421 : Blo 2263435 43534421 := bbase (se 8 (by rfl) ⟨255084, by rfl⟩ : syracuseStep 43534421 = 510169) (by norm_num)
theorem B29022947 : Blo 2263435 29022947 := bstep (se 1 (by rfl) ⟨21767210, by rfl⟩ : syracuseStep 29022947 = 43534421) B43534421
theorem B19348631 : Blo 2263435 19348631 := bstep (se 1 (by rfl) ⟨14511473, by rfl⟩ : syracuseStep 19348631 = 29022947) B29022947
theorem B12899087 : Blo 2263435 12899087 := bstep (se 1 (by rfl) ⟨9674315, by rfl⟩ : syracuseStep 12899087 = 19348631) B19348631
theorem B8599391 : Blo 2263435 8599391 := bstep (se 1 (by rfl) ⟨6449543, by rfl⟩ : syracuseStep 8599391 = 12899087) B12899087
theorem B5732927 : Blo 2263435 5732927 := bstep (se 1 (by rfl) ⟨4299695, by rfl⟩ : syracuseStep 5732927 = 8599391) B8599391
theorem B3821951 : Blo 2263435 3821951 := bstep (se 1 (by rfl) ⟨2866463, by rfl⟩ : syracuseStep 3821951 = 5732927) B5732927
theorem B2547967 : Blo 2263435 2547967 := bstep (se 1 (by rfl) ⟨1910975, by rfl⟩ : syracuseStep 2547967 = 3821951) B3821951
theorem B3397289 : Blo 2263435 3397289 := bstep (se 2 (by rfl) ⟨1273983, by rfl⟩ : syracuseStep 3397289 = 2547967) B2547967
theorem B2264859 : Blo 2263435 2264859 := bstep (se 1 (by rfl) ⟨1698644, by rfl⟩ : syracuseStep 2264859 = 3397289) B3397289
theorem B5441813 : Blo 2263435 5441813 := bbase (se 6 (by rfl) ⟨127542, by rfl⟩ : syracuseStep 5441813 = 255085) (by norm_num)
theorem B3627875 : Blo 2263435 3627875 := bstep (se 1 (by rfl) ⟨2720906, by rfl⟩ : syracuseStep 3627875 = 5441813) B5441813
theorem B2418583 : Blo 2263435 2418583 := bstep (se 1 (by rfl) ⟨1813937, by rfl⟩ : syracuseStep 2418583 = 3627875) B3627875
theorem B3224777 : Blo 2263435 3224777 := bstep (se 2 (by rfl) ⟨1209291, by rfl⟩ : syracuseStep 3224777 = 2418583) B2418583
theorem B8599405 : Blo 2263435 8599405 := bstep (se 3 (by rfl) ⟨1612388, by rfl⟩ : syracuseStep 8599405 = 3224777) B3224777
theorem B11465873 : Blo 2263435 11465873 := bstep (se 2 (by rfl) ⟨4299702, by rfl⟩ : syracuseStep 11465873 = 8599405) B8599405
theorem B7643915 : Blo 2263435 7643915 := bstep (se 1 (by rfl) ⟨5732936, by rfl⟩ : syracuseStep 7643915 = 11465873) B11465873
theorem B5095943 : Blo 2263435 5095943 := bstep (se 1 (by rfl) ⟨3821957, by rfl⟩ : syracuseStep 5095943 = 7643915) B7643915
theorem B3397295 : Blo 2263435 3397295 := bstep (se 1 (by rfl) ⟨2547971, by rfl⟩ : syracuseStep 3397295 = 5095943) B5095943
theorem B2264863 : Blo 2263435 2264863 := bstep (se 1 (by rfl) ⟨1698647, by rfl⟩ : syracuseStep 2264863 = 3397295) B3397295
theorem B3397301 : Blo 2263435 3397301 := bbase (se 5 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 3397301 = 318497) (by norm_num)
theorem B2264867 : Blo 2263435 2264867 := bstep (se 1 (by rfl) ⟨1698650, by rfl⟩ : syracuseStep 2264867 = 3397301) B3397301
theorem B5732957 : Blo 2263435 5732957 := bbase (se 3 (by rfl) ⟨1074929, by rfl⟩ : syracuseStep 5732957 = 2149859) (by norm_num)
theorem B3821971 : Blo 2263435 3821971 := bstep (se 1 (by rfl) ⟨2866478, by rfl⟩ : syracuseStep 3821971 = 5732957) B5732957
theorem B5095961 : Blo 2263435 5095961 := bstep (se 2 (by rfl) ⟨1910985, by rfl⟩ : syracuseStep 5095961 = 3821971) B3821971
theorem B3397307 : Blo 2263435 3397307 := bstep (se 1 (by rfl) ⟨2547980, by rfl⟩ : syracuseStep 3397307 = 5095961) B5095961
theorem B2264871 : Blo 2263435 2264871 := bstep (se 1 (by rfl) ⟨1698653, by rfl⟩ : syracuseStep 2264871 = 3397307) B3397307
theorem B2547985 : Blo 2263435 2547985 := bbase (se 2 (by rfl) ⟨955494, by rfl⟩ : syracuseStep 2547985 = 1910989) (by norm_num)
theorem B3397313 : Blo 2263435 3397313 := bstep (se 2 (by rfl) ⟨1273992, by rfl⟩ : syracuseStep 3397313 = 2547985) B2547985
theorem B2264875 : Blo 2263435 2264875 := bstep (se 1 (by rfl) ⟨1698656, by rfl⟩ : syracuseStep 2264875 = 3397313) B3397313
theorem B4299733 : Blo 2263435 4299733 := bbase (se 7 (by rfl) ⟨50387, by rfl⟩ : syracuseStep 4299733 = 100775) (by norm_num)
theorem B5732977 : Blo 2263435 5732977 := bstep (se 2 (by rfl) ⟨2149866, by rfl⟩ : syracuseStep 5732977 = 4299733) B4299733
theorem B7643969 : Blo 2263435 7643969 := bstep (se 2 (by rfl) ⟨2866488, by rfl⟩ : syracuseStep 7643969 = 5732977) B5732977
theorem B5095979 : Blo 2263435 5095979 := bstep (se 1 (by rfl) ⟨3821984, by rfl⟩ : syracuseStep 5095979 = 7643969) B7643969
theorem B3397319 : Blo 2263435 3397319 := bstep (se 1 (by rfl) ⟨2547989, by rfl⟩ : syracuseStep 3397319 = 5095979) B5095979
theorem B2264879 : Blo 2263435 2264879 := bstep (se 1 (by rfl) ⟨1698659, by rfl⟩ : syracuseStep 2264879 = 3397319) B3397319
theorem B3397325 : Blo 2263435 3397325 := bbase (se 3 (by rfl) ⟨636998, by rfl⟩ : syracuseStep 3397325 = 1273997) (by norm_num)
theorem B2264883 : Blo 2263435 2264883 := bstep (se 1 (by rfl) ⟨1698662, by rfl⟩ : syracuseStep 2264883 = 3397325) B3397325
theorem B5095997 : Blo 2263435 5095997 := bbase (se 3 (by rfl) ⟨955499, by rfl⟩ : syracuseStep 5095997 = 1910999) (by norm_num)
theorem B3397331 : Blo 2263435 3397331 := bstep (se 1 (by rfl) ⟨2547998, by rfl⟩ : syracuseStep 3397331 = 5095997) B5095997
theorem B2264887 : Blo 2263435 2264887 := bstep (se 1 (by rfl) ⟨1698665, by rfl⟩ : syracuseStep 2264887 = 3397331) B3397331
theorem B3822005 : Blo 2263435 3822005 := bbase (se 5 (by rfl) ⟨179156, by rfl⟩ : syracuseStep 3822005 = 358313) (by norm_num)
theorem B2548003 : Blo 2263435 2548003 := bstep (se 1 (by rfl) ⟨1911002, by rfl⟩ : syracuseStep 2548003 = 3822005) B3822005
theorem B3397337 : Blo 2263435 3397337 := bstep (se 2 (by rfl) ⟨1274001, by rfl⟩ : syracuseStep 3397337 = 2548003) B2548003
theorem B2264891 : Blo 2263435 2264891 := bstep (se 1 (by rfl) ⟨1698668, by rfl⟩ : syracuseStep 2264891 = 3397337) B3397337
theorem B2418617 : Blo 2263435 2418617 := bbase (se 2 (by rfl) ⟨906981, by rfl⟩ : syracuseStep 2418617 = 1813963) (by norm_num)
theorem B6449645 : Blo 2263435 6449645 := bstep (se 3 (by rfl) ⟨1209308, by rfl⟩ : syracuseStep 6449645 = 2418617) B2418617
theorem B17199053 : Blo 2263435 17199053 := bstep (se 3 (by rfl) ⟨3224822, by rfl⟩ : syracuseStep 17199053 = 6449645) B6449645
theorem B11466035 : Blo 2263435 11466035 := bstep (se 1 (by rfl) ⟨8599526, by rfl⟩ : syracuseStep 11466035 = 17199053) B17199053
theorem B7644023 : Blo 2263435 7644023 := bstep (se 1 (by rfl) ⟨5733017, by rfl⟩ : syracuseStep 7644023 = 11466035) B11466035
theorem B5096015 : Blo 2263435 5096015 := bstep (se 1 (by rfl) ⟨3822011, by rfl⟩ : syracuseStep 5096015 = 7644023) B7644023
theorem B3397343 : Blo 2263435 3397343 := bstep (se 1 (by rfl) ⟨2548007, by rfl⟩ : syracuseStep 3397343 = 5096015) B5096015
theorem B2264895 : Blo 2263435 2264895 := bstep (se 1 (by rfl) ⟨1698671, by rfl⟩ : syracuseStep 2264895 = 3397343) B3397343
theorem B3397349 : Blo 2263435 3397349 := bbase (se 4 (by rfl) ⟨318501, by rfl⟩ : syracuseStep 3397349 = 637003) (by norm_num)
theorem B2264899 : Blo 2263435 2264899 := bstep (se 1 (by rfl) ⟨1698674, by rfl⟩ : syracuseStep 2264899 = 3397349) B3397349
theorem B6449669 : Blo 2263435 6449669 := bbase (se 4 (by rfl) ⟨604656, by rfl⟩ : syracuseStep 6449669 = 1209313) (by norm_num)
theorem B4299779 : Blo 2263435 4299779 := bstep (se 1 (by rfl) ⟨3224834, by rfl⟩ : syracuseStep 4299779 = 6449669) B6449669
theorem B2866519 : Blo 2263435 2866519 := bstep (se 1 (by rfl) ⟨2149889, by rfl⟩ : syracuseStep 2866519 = 4299779) B4299779
theorem B3822025 : Blo 2263435 3822025 := bstep (se 2 (by rfl) ⟨1433259, by rfl⟩ : syracuseStep 3822025 = 2866519) B2866519
theorem B5096033 : Blo 2263435 5096033 := bstep (se 2 (by rfl) ⟨1911012, by rfl⟩ : syracuseStep 5096033 = 3822025) B3822025
theorem B3397355 : Blo 2263435 3397355 := bstep (se 1 (by rfl) ⟨2548016, by rfl⟩ : syracuseStep 3397355 = 5096033) B5096033
theorem B2264903 : Blo 2263435 2264903 := bstep (se 1 (by rfl) ⟨1698677, by rfl⟩ : syracuseStep 2264903 = 3397355) B3397355
theorem B2548021 : Blo 2263435 2548021 := bbase (se 5 (by rfl) ⟨119438, by rfl⟩ : syracuseStep 2548021 = 238877) (by norm_num)
theorem B3397361 : Blo 2263435 3397361 := bstep (se 2 (by rfl) ⟨1274010, by rfl⟩ : syracuseStep 3397361 = 2548021) B2548021
theorem B2264907 : Blo 2263435 2264907 := bstep (se 1 (by rfl) ⟨1698680, by rfl⟩ : syracuseStep 2264907 = 3397361) B3397361
theorem B2866529 : Blo 2263435 2866529 := bbase (se 2 (by rfl) ⟨1074948, by rfl⟩ : syracuseStep 2866529 = 2149897) (by norm_num)
theorem B7644077 : Blo 2263435 7644077 := bstep (se 3 (by rfl) ⟨1433264, by rfl⟩ : syracuseStep 7644077 = 2866529) B2866529
theorem B5096051 : Blo 2263435 5096051 := bstep (se 1 (by rfl) ⟨3822038, by rfl⟩ : syracuseStep 5096051 = 7644077) B7644077
theorem B3397367 : Blo 2263435 3397367 := bstep (se 1 (by rfl) ⟨2548025, by rfl⟩ : syracuseStep 3397367 = 5096051) B5096051
theorem B2264911 : Blo 2263435 2264911 := bstep (se 1 (by rfl) ⟨1698683, by rfl⟩ : syracuseStep 2264911 = 3397367) B3397367
theorem B3397373 : Blo 2263435 3397373 := bbase (se 3 (by rfl) ⟨637007, by rfl⟩ : syracuseStep 3397373 = 1274015) (by norm_num)
theorem B2264915 : Blo 2263435 2264915 := bstep (se 1 (by rfl) ⟨1698686, by rfl⟩ : syracuseStep 2264915 = 3397373) B3397373
theorem B5096069 : Blo 2263435 5096069 := bbase (se 4 (by rfl) ⟨477756, by rfl⟩ : syracuseStep 5096069 = 955513) (by norm_num)
theorem B3397379 : Blo 2263435 3397379 := bstep (se 1 (by rfl) ⟨2548034, by rfl⟩ : syracuseStep 3397379 = 5096069) B5096069
theorem B2264919 : Blo 2263435 2264919 := bstep (se 1 (by rfl) ⟨1698689, by rfl⟩ : syracuseStep 2264919 = 3397379) B3397379
theorem B12244405 : Blo 2263435 12244405 := bbase (se 5 (by rfl) ⟨573956, by rfl⟩ : syracuseStep 12244405 = 1147913) (by norm_num)
theorem B16325873 : Blo 2263435 16325873 := bstep (se 2 (by rfl) ⟨6122202, by rfl⟩ : syracuseStep 16325873 = 12244405) B12244405
theorem B10883915 : Blo 2263435 10883915 := bstep (se 1 (by rfl) ⟨8162936, by rfl⟩ : syracuseStep 10883915 = 16325873) B16325873
theorem B7255943 : Blo 2263435 7255943 := bstep (se 1 (by rfl) ⟨5441957, by rfl⟩ : syracuseStep 7255943 = 10883915) B10883915
theorem B4837295 : Blo 2263435 4837295 := bstep (se 1 (by rfl) ⟨3627971, by rfl⟩ : syracuseStep 4837295 = 7255943) B7255943
theorem B3224863 : Blo 2263435 3224863 := bstep (se 1 (by rfl) ⟨2418647, by rfl⟩ : syracuseStep 3224863 = 4837295) B4837295
theorem B4299817 : Blo 2263435 4299817 := bstep (se 2 (by rfl) ⟨1612431, by rfl⟩ : syracuseStep 4299817 = 3224863) B3224863
theorem B5733089 : Blo 2263435 5733089 := bstep (se 2 (by rfl) ⟨2149908, by rfl⟩ : syracuseStep 5733089 = 4299817) B4299817
theorem B3822059 : Blo 2263435 3822059 := bstep (se 1 (by rfl) ⟨2866544, by rfl⟩ : syracuseStep 3822059 = 5733089) B5733089
theorem B2548039 : Blo 2263435 2548039 := bstep (se 1 (by rfl) ⟨1911029, by rfl⟩ : syracuseStep 2548039 = 3822059) B3822059
theorem B3397385 : Blo 2263435 3397385 := bstep (se 2 (by rfl) ⟨1274019, by rfl⟩ : syracuseStep 3397385 = 2548039) B2548039
theorem B2264923 : Blo 2263435 2264923 := bstep (se 1 (by rfl) ⟨1698692, by rfl⟩ : syracuseStep 2264923 = 3397385) B3397385
theorem B11466197 : Blo 2263435 11466197 := bbase (se 7 (by rfl) ⟨134369, by rfl⟩ : syracuseStep 11466197 = 268739) (by norm_num)
theorem B7644131 : Blo 2263435 7644131 := bstep (se 1 (by rfl) ⟨5733098, by rfl⟩ : syracuseStep 7644131 = 11466197) B11466197
theorem B5096087 : Blo 2263435 5096087 := bstep (se 1 (by rfl) ⟨3822065, by rfl⟩ : syracuseStep 5096087 = 7644131) B7644131
theorem B3397391 : Blo 2263435 3397391 := bstep (se 1 (by rfl) ⟨2548043, by rfl⟩ : syracuseStep 3397391 = 5096087) B5096087
theorem B2264927 : Blo 2263435 2264927 := bstep (se 1 (by rfl) ⟨1698695, by rfl⟩ : syracuseStep 2264927 = 3397391) B3397391
theorem B3397397 : Blo 2263435 3397397 := bbase (se 6 (by rfl) ⟨79626, by rfl⟩ : syracuseStep 3397397 = 159253) (by norm_num)
theorem B2264931 : Blo 2263435 2264931 := bstep (se 1 (by rfl) ⟨1698698, by rfl⟩ : syracuseStep 2264931 = 3397397) B3397397
theorem B19613269 : Blo 2263435 19613269 := bbase (se 8 (by rfl) ⟨114921, by rfl⟩ : syracuseStep 19613269 = 229843) (by norm_num)
theorem B26151025 : Blo 2263435 26151025 := bstep (se 2 (by rfl) ⟨9806634, by rfl⟩ : syracuseStep 26151025 = 19613269) B19613269
theorem B34868033 : Blo 2263435 34868033 := bstep (se 2 (by rfl) ⟨13075512, by rfl⟩ : syracuseStep 34868033 = 26151025) B26151025
theorem B23245355 : Blo 2263435 23245355 := bstep (se 1 (by rfl) ⟨17434016, by rfl⟩ : syracuseStep 23245355 = 34868033) B34868033
theorem B15496903 : Blo 2263435 15496903 := bstep (se 1 (by rfl) ⟨11622677, by rfl⟩ : syracuseStep 15496903 = 23245355) B23245355
theorem B20662537 : Blo 2263435 20662537 := bstep (se 2 (by rfl) ⟨7748451, by rfl⟩ : syracuseStep 20662537 = 15496903) B15496903
theorem B27550049 : Blo 2263435 27550049 := bstep (se 2 (by rfl) ⟨10331268, by rfl⟩ : syracuseStep 27550049 = 20662537) B20662537
theorem B73466797 : Blo 2263435 73466797 := bstep (se 3 (by rfl) ⟨13775024, by rfl⟩ : syracuseStep 73466797 = 27550049) B27550049
theorem B97955729 : Blo 2263435 97955729 := bstep (se 2 (by rfl) ⟨36733398, by rfl⟩ : syracuseStep 97955729 = 73466797) B73466797
theorem B65303819 : Blo 2263435 65303819 := bstep (se 1 (by rfl) ⟨48977864, by rfl⟩ : syracuseStep 65303819 = 97955729) B97955729
theorem B43535879 : Blo 2263435 43535879 := bstep (se 1 (by rfl) ⟨32651909, by rfl⟩ : syracuseStep 43535879 = 65303819) B65303819
theorem B29023919 : Blo 2263435 29023919 := bstep (se 1 (by rfl) ⟨21767939, by rfl⟩ : syracuseStep 29023919 = 43535879) B43535879
theorem B19349279 : Blo 2263435 19349279 := bstep (se 1 (by rfl) ⟨14511959, by rfl⟩ : syracuseStep 19349279 = 29023919) B29023919
theorem B12899519 : Blo 2263435 12899519 := bstep (se 1 (by rfl) ⟨9674639, by rfl⟩ : syracuseStep 12899519 = 19349279) B19349279
theorem B8599679 : Blo 2263435 8599679 := bstep (se 1 (by rfl) ⟨6449759, by rfl⟩ : syracuseStep 8599679 = 12899519) B12899519
theorem B5733119 : Blo 2263435 5733119 := bstep (se 1 (by rfl) ⟨4299839, by rfl⟩ : syracuseStep 5733119 = 8599679) B8599679
theorem B3822079 : Blo 2263435 3822079 := bstep (se 1 (by rfl) ⟨2866559, by rfl⟩ : syracuseStep 3822079 = 5733119) B5733119
theorem B5096105 : Blo 2263435 5096105 := bstep (se 2 (by rfl) ⟨1911039, by rfl⟩ : syracuseStep 5096105 = 3822079) B3822079
theorem B3397403 : Blo 2263435 3397403 := bstep (se 1 (by rfl) ⟨2548052, by rfl⟩ : syracuseStep 3397403 = 5096105) B5096105
theorem B2264935 : Blo 2263435 2264935 := bstep (se 1 (by rfl) ⟨1698701, by rfl⟩ : syracuseStep 2264935 = 3397403) B3397403
theorem B2548057 : Blo 2263435 2548057 := bbase (se 2 (by rfl) ⟨955521, by rfl⟩ : syracuseStep 2548057 = 1911043) (by norm_num)
theorem B3397409 : Blo 2263435 3397409 := bstep (se 2 (by rfl) ⟨1274028, by rfl⟩ : syracuseStep 3397409 = 2548057) B2548057
theorem B2264939 : Blo 2263435 2264939 := bstep (se 1 (by rfl) ⟨1698704, by rfl⟩ : syracuseStep 2264939 = 3397409) B3397409
theorem B5442005 : Blo 2263435 5442005 := bbase (se 7 (by rfl) ⟨63773, by rfl⟩ : syracuseStep 5442005 = 127547) (by norm_num)
theorem B3628003 : Blo 2263435 3628003 := bstep (se 1 (by rfl) ⟨2721002, by rfl⟩ : syracuseStep 3628003 = 5442005) B5442005
theorem B4837337 : Blo 2263435 4837337 := bstep (se 2 (by rfl) ⟨1814001, by rfl⟩ : syracuseStep 4837337 = 3628003) B3628003
theorem B3224891 : Blo 2263435 3224891 := bstep (se 1 (by rfl) ⟨2418668, by rfl⟩ : syracuseStep 3224891 = 4837337) B4837337
theorem B8599709 : Blo 2263435 8599709 := bstep (se 3 (by rfl) ⟨1612445, by rfl⟩ : syracuseStep 8599709 = 3224891) B3224891
theorem B5733139 : Blo 2263435 5733139 := bstep (se 1 (by rfl) ⟨4299854, by rfl⟩ : syracuseStep 5733139 = 8599709) B8599709
theorem B7644185 : Blo 2263435 7644185 := bstep (se 2 (by rfl) ⟨2866569, by rfl⟩ : syracuseStep 7644185 = 5733139) B5733139
theorem B5096123 : Blo 2263435 5096123 := bstep (se 1 (by rfl) ⟨3822092, by rfl⟩ : syracuseStep 5096123 = 7644185) B7644185
theorem B3397415 : Blo 2263435 3397415 := bstep (se 1 (by rfl) ⟨2548061, by rfl⟩ : syracuseStep 3397415 = 5096123) B5096123
theorem B2264943 : Blo 2263435 2264943 := bstep (se 1 (by rfl) ⟨1698707, by rfl⟩ : syracuseStep 2264943 = 3397415) B3397415
theorem B3397421 : Blo 2263435 3397421 := bbase (se 3 (by rfl) ⟨637016, by rfl⟩ : syracuseStep 3397421 = 1274033) (by norm_num)
theorem B2264947 : Blo 2263435 2264947 := bstep (se 1 (by rfl) ⟨1698710, by rfl⟩ : syracuseStep 2264947 = 3397421) B3397421
theorem B5096141 : Blo 2263435 5096141 := bbase (se 3 (by rfl) ⟨955526, by rfl⟩ : syracuseStep 5096141 = 1911053) (by norm_num)
theorem B3397427 : Blo 2263435 3397427 := bstep (se 1 (by rfl) ⟨2548070, by rfl⟩ : syracuseStep 3397427 = 5096141) B5096141
theorem B2264951 : Blo 2263435 2264951 := bstep (se 1 (by rfl) ⟨1698713, by rfl⟩ : syracuseStep 2264951 = 3397427) B3397427
theorem B2866585 : Blo 2263435 2866585 := bbase (se 2 (by rfl) ⟨1074969, by rfl⟩ : syracuseStep 2866585 = 2149939) (by norm_num)
theorem B3822113 : Blo 2263435 3822113 := bstep (se 2 (by rfl) ⟨1433292, by rfl⟩ : syracuseStep 3822113 = 2866585) B2866585
theorem B2548075 : Blo 2263435 2548075 := bstep (se 1 (by rfl) ⟨1911056, by rfl⟩ : syracuseStep 2548075 = 3822113) B3822113
theorem B3397433 : Blo 2263435 3397433 := bstep (se 2 (by rfl) ⟨1274037, by rfl⟩ : syracuseStep 3397433 = 2548075) B2548075
theorem B2264955 : Blo 2263435 2264955 := bstep (se 1 (by rfl) ⟨1698716, by rfl⟩ : syracuseStep 2264955 = 3397433) B3397433
theorem B9674741 : Blo 2263435 9674741 := bbase (se 5 (by rfl) ⟨453503, by rfl⟩ : syracuseStep 9674741 = 907007) (by norm_num)
theorem B25799309 : Blo 2263435 25799309 := bstep (se 3 (by rfl) ⟨4837370, by rfl⟩ : syracuseStep 25799309 = 9674741) B9674741
theorem B17199539 : Blo 2263435 17199539 := bstep (se 1 (by rfl) ⟨12899654, by rfl⟩ : syracuseStep 17199539 = 25799309) B25799309
theorem B11466359 : Blo 2263435 11466359 := bstep (se 1 (by rfl) ⟨8599769, by rfl⟩ : syracuseStep 11466359 = 17199539) B17199539
theorem B7644239 : Blo 2263435 7644239 := bstep (se 1 (by rfl) ⟨5733179, by rfl⟩ : syracuseStep 7644239 = 11466359) B11466359
theorem B5096159 : Blo 2263435 5096159 := bstep (se 1 (by rfl) ⟨3822119, by rfl⟩ : syracuseStep 5096159 = 7644239) B7644239
theorem B3397439 : Blo 2263435 3397439 := bstep (se 1 (by rfl) ⟨2548079, by rfl⟩ : syracuseStep 3397439 = 5096159) B5096159
theorem B2264959 : Blo 2263435 2264959 := bstep (se 1 (by rfl) ⟨1698719, by rfl⟩ : syracuseStep 2264959 = 3397439) B3397439
theorem B3397445 : Blo 2263435 3397445 := bbase (se 4 (by rfl) ⟨318510, by rfl⟩ : syracuseStep 3397445 = 637021) (by norm_num)
theorem B2264963 : Blo 2263435 2264963 := bstep (se 1 (by rfl) ⟨1698722, by rfl⟩ : syracuseStep 2264963 = 3397445) B3397445
theorem B3822133 : Blo 2263435 3822133 := bbase (se 5 (by rfl) ⟨179162, by rfl⟩ : syracuseStep 3822133 = 358325) (by norm_num)
theorem B5096177 : Blo 2263435 5096177 := bstep (se 2 (by rfl) ⟨1911066, by rfl⟩ : syracuseStep 5096177 = 3822133) B3822133
theorem B3397451 : Blo 2263435 3397451 := bstep (se 1 (by rfl) ⟨2548088, by rfl⟩ : syracuseStep 3397451 = 5096177) B5096177
theorem B2264967 : Blo 2263435 2264967 := bstep (se 1 (by rfl) ⟨1698725, by rfl⟩ : syracuseStep 2264967 = 3397451) B3397451
theorem B2548093 : Blo 2263435 2548093 := bbase (se 3 (by rfl) ⟨477767, by rfl⟩ : syracuseStep 2548093 = 955535) (by norm_num)
theorem B3397457 : Blo 2263435 3397457 := bstep (se 2 (by rfl) ⟨1274046, by rfl⟩ : syracuseStep 3397457 = 2548093) B2548093
theorem B2264971 : Blo 2263435 2264971 := bstep (se 1 (by rfl) ⟨1698728, by rfl⟩ : syracuseStep 2264971 = 3397457) B3397457
theorem B7644293 : Blo 2263435 7644293 := bbase (se 4 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 7644293 = 1433305) (by norm_num)
theorem B5096195 : Blo 2263435 5096195 := bstep (se 1 (by rfl) ⟨3822146, by rfl⟩ : syracuseStep 5096195 = 7644293) B7644293
theorem B3397463 : Blo 2263435 3397463 := bstep (se 1 (by rfl) ⟨2548097, by rfl⟩ : syracuseStep 3397463 = 5096195) B5096195
theorem B2264975 : Blo 2263435 2264975 := bstep (se 1 (by rfl) ⟨1698731, by rfl⟩ : syracuseStep 2264975 = 3397463) B3397463
theorem B3397469 : Blo 2263435 3397469 := bbase (se 3 (by rfl) ⟨637025, by rfl⟩ : syracuseStep 3397469 = 1274051) (by norm_num)
theorem B2264979 : Blo 2263435 2264979 := bstep (se 1 (by rfl) ⟨1698734, by rfl⟩ : syracuseStep 2264979 = 3397469) B3397469
theorem B5096213 : Blo 2263435 5096213 := bbase (se 6 (by rfl) ⟨119442, by rfl⟩ : syracuseStep 5096213 = 238885) (by norm_num)
theorem B3397475 : Blo 2263435 3397475 := bstep (se 1 (by rfl) ⟨2548106, by rfl⟩ : syracuseStep 3397475 = 5096213) B5096213
theorem B2264983 : Blo 2263435 2264983 := bstep (se 1 (by rfl) ⟨1698737, by rfl⟩ : syracuseStep 2264983 = 3397475) B3397475
theorem B8599877 : Blo 2263435 8599877 := bbase (se 4 (by rfl) ⟨806238, by rfl⟩ : syracuseStep 8599877 = 1612477) (by norm_num)
theorem B5733251 : Blo 2263435 5733251 := bstep (se 1 (by rfl) ⟨4299938, by rfl⟩ : syracuseStep 5733251 = 8599877) B8599877
theorem B3822167 : Blo 2263435 3822167 := bstep (se 1 (by rfl) ⟨2866625, by rfl⟩ : syracuseStep 3822167 = 5733251) B5733251
theorem B2548111 : Blo 2263435 2548111 := bstep (se 1 (by rfl) ⟨1911083, by rfl⟩ : syracuseStep 2548111 = 3822167) B3822167
theorem B3397481 : Blo 2263435 3397481 := bstep (se 2 (by rfl) ⟨1274055, by rfl⟩ : syracuseStep 3397481 = 2548111) B2548111
theorem B2264987 : Blo 2263435 2264987 := bstep (se 1 (by rfl) ⟨1698740, by rfl⟩ : syracuseStep 2264987 = 3397481) B3397481
theorem B10331525 : Blo 2263435 10331525 := bbase (se 4 (by rfl) ⟨968580, by rfl⟩ : syracuseStep 10331525 = 1937161) (by norm_num)
theorem B6887683 : Blo 2263435 6887683 := bstep (se 1 (by rfl) ⟨5165762, by rfl⟩ : syracuseStep 6887683 = 10331525) B10331525
theorem B36734309 : Blo 2263435 36734309 := bstep (se 4 (by rfl) ⟨3443841, by rfl⟩ : syracuseStep 36734309 = 6887683) B6887683
theorem B24489539 : Blo 2263435 24489539 := bstep (se 1 (by rfl) ⟨18367154, by rfl⟩ : syracuseStep 24489539 = 36734309) B36734309
theorem B16326359 : Blo 2263435 16326359 := bstep (se 1 (by rfl) ⟨12244769, by rfl⟩ : syracuseStep 16326359 = 24489539) B24489539
theorem B10884239 : Blo 2263435 10884239 := bstep (se 1 (by rfl) ⟨8163179, by rfl⟩ : syracuseStep 10884239 = 16326359) B16326359
theorem B7256159 : Blo 2263435 7256159 := bstep (se 1 (by rfl) ⟨5442119, by rfl⟩ : syracuseStep 7256159 = 10884239) B10884239
theorem B4837439 : Blo 2263435 4837439 := bstep (se 1 (by rfl) ⟨3628079, by rfl⟩ : syracuseStep 4837439 = 7256159) B7256159
theorem B12899837 : Blo 2263435 12899837 := bstep (se 3 (by rfl) ⟨2418719, by rfl⟩ : syracuseStep 12899837 = 4837439) B4837439
theorem B8599891 : Blo 2263435 8599891 := bstep (se 1 (by rfl) ⟨6449918, by rfl⟩ : syracuseStep 8599891 = 12899837) B12899837
theorem B11466521 : Blo 2263435 11466521 := bstep (se 2 (by rfl) ⟨4299945, by rfl⟩ : syracuseStep 11466521 = 8599891) B8599891
theorem B7644347 : Blo 2263435 7644347 := bstep (se 1 (by rfl) ⟨5733260, by rfl⟩ : syracuseStep 7644347 = 11466521) B11466521
theorem B5096231 : Blo 2263435 5096231 := bstep (se 1 (by rfl) ⟨3822173, by rfl⟩ : syracuseStep 5096231 = 7644347) B7644347
theorem B3397487 : Blo 2263435 3397487 := bstep (se 1 (by rfl) ⟨2548115, by rfl⟩ : syracuseStep 3397487 = 5096231) B5096231
theorem B2264991 : Blo 2263435 2264991 := bstep (se 1 (by rfl) ⟨1698743, by rfl⟩ : syracuseStep 2264991 = 3397487) B3397487
theorem B3397493 : Blo 2263435 3397493 := bbase (se 5 (by rfl) ⟨159257, by rfl⟩ : syracuseStep 3397493 = 318515) (by norm_num)
theorem B2264995 : Blo 2263435 2264995 := bstep (se 1 (by rfl) ⟨1698746, by rfl⟩ : syracuseStep 2264995 = 3397493) B3397493
theorem B3628093 : Blo 2263435 3628093 := bbase (se 3 (by rfl) ⟨680267, by rfl⟩ : syracuseStep 3628093 = 1360535) (by norm_num)
theorem B4837457 : Blo 2263435 4837457 := bstep (se 2 (by rfl) ⟨1814046, by rfl⟩ : syracuseStep 4837457 = 3628093) B3628093
theorem B3224971 : Blo 2263435 3224971 := bstep (se 1 (by rfl) ⟨2418728, by rfl⟩ : syracuseStep 3224971 = 4837457) B4837457
theorem B4299961 : Blo 2263435 4299961 := bstep (se 2 (by rfl) ⟨1612485, by rfl⟩ : syracuseStep 4299961 = 3224971) B3224971
theorem B5733281 : Blo 2263435 5733281 := bstep (se 2 (by rfl) ⟨2149980, by rfl⟩ : syracuseStep 5733281 = 4299961) B4299961
theorem B3822187 : Blo 2263435 3822187 := bstep (se 1 (by rfl) ⟨2866640, by rfl⟩ : syracuseStep 3822187 = 5733281) B5733281
theorem B5096249 : Blo 2263435 5096249 := bstep (se 2 (by rfl) ⟨1911093, by rfl⟩ : syracuseStep 5096249 = 3822187) B3822187
theorem B3397499 : Blo 2263435 3397499 := bstep (se 1 (by rfl) ⟨2548124, by rfl⟩ : syracuseStep 3397499 = 5096249) B5096249
theorem B2264999 : Blo 2263435 2264999 := bstep (se 1 (by rfl) ⟨1698749, by rfl⟩ : syracuseStep 2264999 = 3397499) B3397499
theorem B2548129 : Blo 2263435 2548129 := bbase (se 2 (by rfl) ⟨955548, by rfl⟩ : syracuseStep 2548129 = 1911097) (by norm_num)
theorem B3397505 : Blo 2263435 3397505 := bstep (se 2 (by rfl) ⟨1274064, by rfl⟩ : syracuseStep 3397505 = 2548129) B2548129
theorem B2265003 : Blo 2263435 2265003 := bstep (se 1 (by rfl) ⟨1698752, by rfl⟩ : syracuseStep 2265003 = 3397505) B3397505
theorem B5733301 : Blo 2263435 5733301 := bbase (se 5 (by rfl) ⟨268748, by rfl⟩ : syracuseStep 5733301 = 537497) (by norm_num)
theorem B7644401 : Blo 2263435 7644401 := bstep (se 2 (by rfl) ⟨2866650, by rfl⟩ : syracuseStep 7644401 = 5733301) B5733301
theorem B5096267 : Blo 2263435 5096267 := bstep (se 1 (by rfl) ⟨3822200, by rfl⟩ : syracuseStep 5096267 = 7644401) B7644401
theorem B3397511 : Blo 2263435 3397511 := bstep (se 1 (by rfl) ⟨2548133, by rfl⟩ : syracuseStep 3397511 = 5096267) B5096267
theorem B2265007 : Blo 2263435 2265007 := bstep (se 1 (by rfl) ⟨1698755, by rfl⟩ : syracuseStep 2265007 = 3397511) B3397511
theorem B3397517 : Blo 2263435 3397517 := bbase (se 3 (by rfl) ⟨637034, by rfl⟩ : syracuseStep 3397517 = 1274069) (by norm_num)
theorem B2265011 : Blo 2263435 2265011 := bstep (se 1 (by rfl) ⟨1698758, by rfl⟩ : syracuseStep 2265011 = 3397517) B3397517
theorem B5096285 : Blo 2263435 5096285 := bbase (se 3 (by rfl) ⟨955553, by rfl⟩ : syracuseStep 5096285 = 1911107) (by norm_num)
theorem B3397523 : Blo 2263435 3397523 := bstep (se 1 (by rfl) ⟨2548142, by rfl⟩ : syracuseStep 3397523 = 5096285) B5096285
theorem B2265015 : Blo 2263435 2265015 := bstep (se 1 (by rfl) ⟨1698761, by rfl⟩ : syracuseStep 2265015 = 3397523) B3397523
theorem B3822221 : Blo 2263435 3822221 := bbase (se 3 (by rfl) ⟨716666, by rfl⟩ : syracuseStep 3822221 = 1433333) (by norm_num)
theorem B2548147 : Blo 2263435 2548147 := bstep (se 1 (by rfl) ⟨1911110, by rfl⟩ : syracuseStep 2548147 = 3822221) B3822221
theorem B3397529 : Blo 2263435 3397529 := bstep (se 2 (by rfl) ⟨1274073, by rfl⟩ : syracuseStep 3397529 = 2548147) B2548147
theorem B2265019 : Blo 2263435 2265019 := bstep (se 1 (by rfl) ⟨1698764, by rfl⟩ : syracuseStep 2265019 = 3397529) B3397529
theorem B7256261 : Blo 2263435 7256261 := bbase (se 4 (by rfl) ⟨680274, by rfl⟩ : syracuseStep 7256261 = 1360549) (by norm_num)
theorem B19350029 : Blo 2263435 19350029 := bstep (se 3 (by rfl) ⟨3628130, by rfl⟩ : syracuseStep 19350029 = 7256261) B7256261
theorem B12900019 : Blo 2263435 12900019 := bstep (se 1 (by rfl) ⟨9675014, by rfl⟩ : syracuseStep 12900019 = 19350029) B19350029
theorem B17200025 : Blo 2263435 17200025 := bstep (se 2 (by rfl) ⟨6450009, by rfl⟩ : syracuseStep 17200025 = 12900019) B12900019
theorem B11466683 : Blo 2263435 11466683 := bstep (se 1 (by rfl) ⟨8600012, by rfl⟩ : syracuseStep 11466683 = 17200025) B17200025
theorem B7644455 : Blo 2263435 7644455 := bstep (se 1 (by rfl) ⟨5733341, by rfl⟩ : syracuseStep 7644455 = 11466683) B11466683
theorem B5096303 : Blo 2263435 5096303 := bstep (se 1 (by rfl) ⟨3822227, by rfl⟩ : syracuseStep 5096303 = 7644455) B7644455
theorem B3397535 : Blo 2263435 3397535 := bstep (se 1 (by rfl) ⟨2548151, by rfl⟩ : syracuseStep 3397535 = 5096303) B5096303
theorem B2265023 : Blo 2263435 2265023 := bstep (se 1 (by rfl) ⟨1698767, by rfl⟩ : syracuseStep 2265023 = 3397535) B3397535
theorem B3397541 : Blo 2263435 3397541 := bbase (se 4 (by rfl) ⟨318519, by rfl⟩ : syracuseStep 3397541 = 637039) (by norm_num)
theorem B2265027 : Blo 2263435 2265027 := bstep (se 1 (by rfl) ⟨1698770, by rfl⟩ : syracuseStep 2265027 = 3397541) B3397541
theorem B2866681 : Blo 2263435 2866681 := bbase (se 2 (by rfl) ⟨1075005, by rfl⟩ : syracuseStep 2866681 = 2150011) (by norm_num)
theorem B3822241 : Blo 2263435 3822241 := bstep (se 2 (by rfl) ⟨1433340, by rfl⟩ : syracuseStep 3822241 = 2866681) B2866681
theorem B5096321 : Blo 2263435 5096321 := bstep (se 2 (by rfl) ⟨1911120, by rfl⟩ : syracuseStep 5096321 = 3822241) B3822241
theorem B3397547 : Blo 2263435 3397547 := bstep (se 1 (by rfl) ⟨2548160, by rfl⟩ : syracuseStep 3397547 = 5096321) B5096321
theorem B2265031 : Blo 2263435 2265031 := bstep (se 1 (by rfl) ⟨1698773, by rfl⟩ : syracuseStep 2265031 = 3397547) B3397547
theorem B2548165 : Blo 2263435 2548165 := bbase (se 4 (by rfl) ⟨238890, by rfl⟩ : syracuseStep 2548165 = 477781) (by norm_num)
theorem B3397553 : Blo 2263435 3397553 := bstep (se 2 (by rfl) ⟨1274082, by rfl⟩ : syracuseStep 3397553 = 2548165) B2548165
theorem B2265035 : Blo 2263435 2265035 := bstep (se 1 (by rfl) ⟨1698776, by rfl⟩ : syracuseStep 2265035 = 3397553) B3397553
theorem B4300037 : Blo 2263435 4300037 := bbase (se 4 (by rfl) ⟨403128, by rfl⟩ : syracuseStep 4300037 = 806257) (by norm_num)
theorem B2866691 : Blo 2263435 2866691 := bstep (se 1 (by rfl) ⟨2150018, by rfl⟩ : syracuseStep 2866691 = 4300037) B4300037
theorem B7644509 : Blo 2263435 7644509 := bstep (se 3 (by rfl) ⟨1433345, by rfl⟩ : syracuseStep 7644509 = 2866691) B2866691
theorem B5096339 : Blo 2263435 5096339 := bstep (se 1 (by rfl) ⟨3822254, by rfl⟩ : syracuseStep 5096339 = 7644509) B7644509
theorem B3397559 : Blo 2263435 3397559 := bstep (se 1 (by rfl) ⟨2548169, by rfl⟩ : syracuseStep 3397559 = 5096339) B5096339
theorem B2265039 : Blo 2263435 2265039 := bstep (se 1 (by rfl) ⟨1698779, by rfl⟩ : syracuseStep 2265039 = 3397559) B3397559
theorem B3397565 : Blo 2263435 3397565 := bbase (se 3 (by rfl) ⟨637043, by rfl⟩ : syracuseStep 3397565 = 1274087) (by norm_num)
theorem B2265043 : Blo 2263435 2265043 := bstep (se 1 (by rfl) ⟨1698782, by rfl⟩ : syracuseStep 2265043 = 3397565) B3397565
theorem B5096357 : Blo 2263435 5096357 := bbase (se 4 (by rfl) ⟨477783, by rfl⟩ : syracuseStep 5096357 = 955567) (by norm_num)
theorem B3397571 : Blo 2263435 3397571 := bstep (se 1 (by rfl) ⟨2548178, by rfl⟩ : syracuseStep 3397571 = 5096357) B5096357
theorem B2265047 : Blo 2263435 2265047 := bstep (se 1 (by rfl) ⟨1698785, by rfl⟩ : syracuseStep 2265047 = 3397571) B3397571
theorem B5733413 : Blo 2263435 5733413 := bbase (se 4 (by rfl) ⟨537507, by rfl⟩ : syracuseStep 5733413 = 1075015) (by norm_num)
theorem B3822275 : Blo 2263435 3822275 := bstep (se 1 (by rfl) ⟨2866706, by rfl⟩ : syracuseStep 3822275 = 5733413) B5733413
theorem B2548183 : Blo 2263435 2548183 := bstep (se 1 (by rfl) ⟨1911137, by rfl⟩ : syracuseStep 2548183 = 3822275) B3822275
theorem B3397577 : Blo 2263435 3397577 := bstep (se 2 (by rfl) ⟨1274091, by rfl⟩ : syracuseStep 3397577 = 2548183) B2548183
theorem B2265051 : Blo 2263435 2265051 := bstep (se 1 (by rfl) ⟨1698788, by rfl⟩ : syracuseStep 2265051 = 3397577) B3397577
theorem B6450101 : Blo 2263435 6450101 := bbase (se 5 (by rfl) ⟨302348, by rfl⟩ : syracuseStep 6450101 = 604697) (by norm_num)
theorem B4300067 : Blo 2263435 4300067 := bstep (se 1 (by rfl) ⟨3225050, by rfl⟩ : syracuseStep 4300067 = 6450101) B6450101
theorem B11466845 : Blo 2263435 11466845 := bstep (se 3 (by rfl) ⟨2150033, by rfl⟩ : syracuseStep 11466845 = 4300067) B4300067
theorem B7644563 : Blo 2263435 7644563 := bstep (se 1 (by rfl) ⟨5733422, by rfl⟩ : syracuseStep 7644563 = 11466845) B11466845
theorem B5096375 : Blo 2263435 5096375 := bstep (se 1 (by rfl) ⟨3822281, by rfl⟩ : syracuseStep 5096375 = 7644563) B7644563
theorem B3397583 : Blo 2263435 3397583 := bstep (se 1 (by rfl) ⟨2548187, by rfl⟩ : syracuseStep 3397583 = 5096375) B5096375
theorem B2265055 : Blo 2263435 2265055 := bstep (se 1 (by rfl) ⟨1698791, by rfl⟩ : syracuseStep 2265055 = 3397583) B3397583
theorem B3397589 : Blo 2263435 3397589 := bbase (se 7 (by rfl) ⟨39815, by rfl⟩ : syracuseStep 3397589 = 79631) (by norm_num)
theorem B2265059 : Blo 2263435 2265059 := bstep (se 1 (by rfl) ⟨1698794, by rfl⟩ : syracuseStep 2265059 = 3397589) B3397589
theorem B8600165 : Blo 2263435 8600165 := bbase (se 4 (by rfl) ⟨806265, by rfl⟩ : syracuseStep 8600165 = 1612531) (by norm_num)
theorem B5733443 : Blo 2263435 5733443 := bstep (se 1 (by rfl) ⟨4300082, by rfl⟩ : syracuseStep 5733443 = 8600165) B8600165
theorem B3822295 : Blo 2263435 3822295 := bstep (se 1 (by rfl) ⟨2866721, by rfl⟩ : syracuseStep 3822295 = 5733443) B5733443
theorem B5096393 : Blo 2263435 5096393 := bstep (se 2 (by rfl) ⟨1911147, by rfl⟩ : syracuseStep 5096393 = 3822295) B3822295
theorem B3397595 : Blo 2263435 3397595 := bstep (se 1 (by rfl) ⟨2548196, by rfl⟩ : syracuseStep 3397595 = 5096393) B5096393
theorem B2265063 : Blo 2263435 2265063 := bstep (se 1 (by rfl) ⟨1698797, by rfl⟩ : syracuseStep 2265063 = 3397595) B3397595
theorem B2548201 : Blo 2263435 2548201 := bbase (se 2 (by rfl) ⟨955575, by rfl⟩ : syracuseStep 2548201 = 1911151) (by norm_num)
theorem B3397601 : Blo 2263435 3397601 := bstep (se 2 (by rfl) ⟨1274100, by rfl⟩ : syracuseStep 3397601 = 2548201) B2548201
theorem B2265067 : Blo 2263435 2265067 := bstep (se 1 (by rfl) ⟨1698800, by rfl⟩ : syracuseStep 2265067 = 3397601) B3397601
theorem B2418805 : Blo 2263435 2418805 := bbase (se 5 (by rfl) ⟨113381, by rfl⟩ : syracuseStep 2418805 = 226763) (by norm_num)
theorem B12900293 : Blo 2263435 12900293 := bstep (se 4 (by rfl) ⟨1209402, by rfl⟩ : syracuseStep 12900293 = 2418805) B2418805
theorem B8600195 : Blo 2263435 8600195 := bstep (se 1 (by rfl) ⟨6450146, by rfl⟩ : syracuseStep 8600195 = 12900293) B12900293
theorem B5733463 : Blo 2263435 5733463 := bstep (se 1 (by rfl) ⟨4300097, by rfl⟩ : syracuseStep 5733463 = 8600195) B8600195
theorem B7644617 : Blo 2263435 7644617 := bstep (se 2 (by rfl) ⟨2866731, by rfl⟩ : syracuseStep 7644617 = 5733463) B5733463
theorem B5096411 : Blo 2263435 5096411 := bstep (se 1 (by rfl) ⟨3822308, by rfl⟩ : syracuseStep 5096411 = 7644617) B7644617
theorem B3397607 : Blo 2263435 3397607 := bstep (se 1 (by rfl) ⟨2548205, by rfl⟩ : syracuseStep 3397607 = 5096411) B5096411
theorem B2265071 : Blo 2263435 2265071 := bstep (se 1 (by rfl) ⟨1698803, by rfl⟩ : syracuseStep 2265071 = 3397607) B3397607
theorem B3397613 : Blo 2263435 3397613 := bbase (se 3 (by rfl) ⟨637052, by rfl⟩ : syracuseStep 3397613 = 1274105) (by norm_num)
theorem B2265075 : Blo 2263435 2265075 := bstep (se 1 (by rfl) ⟨1698806, by rfl⟩ : syracuseStep 2265075 = 3397613) B3397613
theorem B5096429 : Blo 2263435 5096429 := bbase (se 3 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 5096429 = 1911161) (by norm_num)
theorem B3397619 : Blo 2263435 3397619 := bstep (se 1 (by rfl) ⟨2548214, by rfl⟩ : syracuseStep 3397619 = 5096429) B5096429
theorem B2265079 : Blo 2263435 2265079 := bstep (se 1 (by rfl) ⟨1698809, by rfl⟩ : syracuseStep 2265079 = 3397619) B3397619
theorem B4837637 : Blo 2263435 4837637 := bbase (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) (by norm_num)
theorem B3225091 : Blo 2263435 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B4300121 : Blo 2263435 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B2866747 : Blo 2263435 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B3822329 : Blo 2263435 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B2548219 : Blo 2263435 2548219 := bstep (se 1 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 2548219 = 3822329) B3822329
theorem B3397625 : Blo 2263435 3397625 := bstep (se 2 (by rfl) ⟨1274109, by rfl⟩ : syracuseStep 3397625 = 2548219) B2548219
theorem B2265083 : Blo 2263435 2265083 := bstep (se 1 (by rfl) ⟨1698812, by rfl⟩ : syracuseStep 2265083 = 3397625) B3397625
theorem B15497941 : Blo 2263435 15497941 := bbase (se 7 (by rfl) ⟨181616, by rfl⟩ : syracuseStep 15497941 = 363233) (by norm_num)
theorem B20663921 : Blo 2263435 20663921 := bstep (se 2 (by rfl) ⟨7748970, by rfl⟩ : syracuseStep 20663921 = 15497941) B15497941
theorem B55103789 : Blo 2263435 55103789 := bstep (se 3 (by rfl) ⟨10331960, by rfl⟩ : syracuseStep 55103789 = 20663921) B20663921
theorem B36735859 : Blo 2263435 36735859 := bstep (se 1 (by rfl) ⟨27551894, by rfl⟩ : syracuseStep 36735859 = 55103789) B55103789
theorem B195924581 : Blo 2263435 195924581 := bstep (se 4 (by rfl) ⟨18367929, by rfl⟩ : syracuseStep 195924581 = 36735859) B36735859
theorem B130616387 : Blo 2263435 130616387 := bstep (se 1 (by rfl) ⟨97962290, by rfl⟩ : syracuseStep 130616387 = 195924581) B195924581
theorem B87077591 : Blo 2263435 87077591 := bstep (se 1 (by rfl) ⟨65308193, by rfl⟩ : syracuseStep 87077591 = 130616387) B130616387
theorem B58051727 : Blo 2263435 58051727 := bstep (se 1 (by rfl) ⟨43538795, by rfl⟩ : syracuseStep 58051727 = 87077591) B87077591
theorem B38701151 : Blo 2263435 38701151 := bstep (se 1 (by rfl) ⟨29025863, by rfl⟩ : syracuseStep 38701151 = 58051727) B58051727
theorem B25800767 : Blo 2263435 25800767 := bstep (se 1 (by rfl) ⟨19350575, by rfl⟩ : syracuseStep 25800767 = 38701151) B38701151
theorem B17200511 : Blo 2263435 17200511 := bstep (se 1 (by rfl) ⟨12900383, by rfl⟩ : syracuseStep 17200511 = 25800767) B25800767
theorem B11467007 : Blo 2263435 11467007 := bstep (se 1 (by rfl) ⟨8600255, by rfl⟩ : syracuseStep 11467007 = 17200511) B17200511
theorem B7644671 : Blo 2263435 7644671 := bstep (se 1 (by rfl) ⟨5733503, by rfl⟩ : syracuseStep 7644671 = 11467007) B11467007
theorem B5096447 : Blo 2263435 5096447 := bstep (se 1 (by rfl) ⟨3822335, by rfl⟩ : syracuseStep 5096447 = 7644671) B7644671
theorem B3397631 : Blo 2263435 3397631 := bstep (se 1 (by rfl) ⟨2548223, by rfl⟩ : syracuseStep 3397631 = 5096447) B5096447
theorem B2265087 : Blo 2263435 2265087 := bstep (se 1 (by rfl) ⟨1698815, by rfl⟩ : syracuseStep 2265087 = 3397631) B3397631
theorem B3397637 : Blo 2263435 3397637 := bbase (se 4 (by rfl) ⟨318528, by rfl⟩ : syracuseStep 3397637 = 637057) (by norm_num)
theorem B2265091 : Blo 2263435 2265091 := bstep (se 1 (by rfl) ⟨1698818, by rfl⟩ : syracuseStep 2265091 = 3397637) B3397637
theorem B3822349 : Blo 2263435 3822349 := bbase (se 3 (by rfl) ⟨716690, by rfl⟩ : syracuseStep 3822349 = 1433381) (by norm_num)
theorem B5096465 : Blo 2263435 5096465 := bstep (se 2 (by rfl) ⟨1911174, by rfl⟩ : syracuseStep 5096465 = 3822349) B3822349
theorem B3397643 : Blo 2263435 3397643 := bstep (se 1 (by rfl) ⟨2548232, by rfl⟩ : syracuseStep 3397643 = 5096465) B5096465
theorem B2265095 : Blo 2263435 2265095 := bstep (se 1 (by rfl) ⟨1698821, by rfl⟩ : syracuseStep 2265095 = 3397643) B3397643
theorem B2548237 : Blo 2263435 2548237 := bbase (se 3 (by rfl) ⟨477794, by rfl⟩ : syracuseStep 2548237 = 955589) (by norm_num)
theorem B3397649 : Blo 2263435 3397649 := bstep (se 2 (by rfl) ⟨1274118, by rfl⟩ : syracuseStep 3397649 = 2548237) B2548237
theorem B2265099 : Blo 2263435 2265099 := bstep (se 1 (by rfl) ⟨1698824, by rfl⟩ : syracuseStep 2265099 = 3397649) B3397649
theorem B7644725 : Blo 2263435 7644725 := bbase (se 5 (by rfl) ⟨358346, by rfl⟩ : syracuseStep 7644725 = 716693) (by norm_num)
theorem B5096483 : Blo 2263435 5096483 := bstep (se 1 (by rfl) ⟨3822362, by rfl⟩ : syracuseStep 5096483 = 7644725) B7644725
theorem B3397655 : Blo 2263435 3397655 := bstep (se 1 (by rfl) ⟨2548241, by rfl⟩ : syracuseStep 3397655 = 5096483) B5096483
theorem B2265103 : Blo 2263435 2265103 := bstep (se 1 (by rfl) ⟨1698827, by rfl⟩ : syracuseStep 2265103 = 3397655) B3397655
theorem B3397661 : Blo 2263435 3397661 := bbase (se 3 (by rfl) ⟨637061, by rfl⟩ : syracuseStep 3397661 = 1274123) (by norm_num)
theorem B2265107 : Blo 2263435 2265107 := bstep (se 1 (by rfl) ⟨1698830, by rfl⟩ : syracuseStep 2265107 = 3397661) B3397661
theorem B5096501 : Blo 2263435 5096501 := bbase (se 5 (by rfl) ⟨238898, by rfl⟩ : syracuseStep 5096501 = 477797) (by norm_num)
theorem B3397667 : Blo 2263435 3397667 := bstep (se 1 (by rfl) ⟨2548250, by rfl⟩ : syracuseStep 3397667 = 5096501) B5096501
theorem B2265111 : Blo 2263435 2265111 := bstep (se 1 (by rfl) ⟨1698833, by rfl⟩ : syracuseStep 2265111 = 3397667) B3397667
theorem B2721209 : Blo 2263435 2721209 := bbase (se 2 (by rfl) ⟨1020453, by rfl⟩ : syracuseStep 2721209 = 2040907) (by norm_num)
theorem B7256557 : Blo 2263435 7256557 := bstep (se 3 (by rfl) ⟨1360604, by rfl⟩ : syracuseStep 7256557 = 2721209) B2721209
theorem B9675409 : Blo 2263435 9675409 := bstep (se 2 (by rfl) ⟨3628278, by rfl⟩ : syracuseStep 9675409 = 7256557) B7256557
theorem B12900545 : Blo 2263435 12900545 := bstep (se 2 (by rfl) ⟨4837704, by rfl⟩ : syracuseStep 12900545 = 9675409) B9675409
theorem B8600363 : Blo 2263435 8600363 := bstep (se 1 (by rfl) ⟨6450272, by rfl⟩ : syracuseStep 8600363 = 12900545) B12900545
theorem B5733575 : Blo 2263435 5733575 := bstep (se 1 (by rfl) ⟨4300181, by rfl⟩ : syracuseStep 5733575 = 8600363) B8600363
theorem B3822383 : Blo 2263435 3822383 := bstep (se 1 (by rfl) ⟨2866787, by rfl⟩ : syracuseStep 3822383 = 5733575) B5733575
theorem B2548255 : Blo 2263435 2548255 := bstep (se 1 (by rfl) ⟨1911191, by rfl⟩ : syracuseStep 2548255 = 3822383) B3822383
theorem B3397673 : Blo 2263435 3397673 := bstep (se 2 (by rfl) ⟨1274127, by rfl⟩ : syracuseStep 3397673 = 2548255) B2548255
theorem B2265115 : Blo 2263435 2265115 := bstep (se 1 (by rfl) ⟨1698836, by rfl⟩ : syracuseStep 2265115 = 3397673) B3397673
theorem B19614869 : Blo 2263435 19614869 := bbase (se 6 (by rfl) ⟨459723, by rfl⟩ : syracuseStep 19614869 = 919447) (by norm_num)
theorem B13076579 : Blo 2263435 13076579 := bstep (se 1 (by rfl) ⟨9807434, by rfl⟩ : syracuseStep 13076579 = 19614869) B19614869
theorem B8717719 : Blo 2263435 8717719 := bstep (se 1 (by rfl) ⟨6538289, by rfl⟩ : syracuseStep 8717719 = 13076579) B13076579
theorem B11623625 : Blo 2263435 11623625 := bstep (se 2 (by rfl) ⟨4358859, by rfl⟩ : syracuseStep 11623625 = 8717719) B8717719
theorem B7749083 : Blo 2263435 7749083 := bstep (se 1 (by rfl) ⟨5811812, by rfl⟩ : syracuseStep 7749083 = 11623625) B11623625
theorem B5166055 : Blo 2263435 5166055 := bstep (se 1 (by rfl) ⟨3874541, by rfl⟩ : syracuseStep 5166055 = 7749083) B7749083
theorem B6888073 : Blo 2263435 6888073 := bstep (se 2 (by rfl) ⟨2583027, by rfl⟩ : syracuseStep 6888073 = 5166055) B5166055
theorem B9184097 : Blo 2263435 9184097 := bstep (se 2 (by rfl) ⟨3444036, by rfl⟩ : syracuseStep 9184097 = 6888073) B6888073
theorem B6122731 : Blo 2263435 6122731 := bstep (se 1 (by rfl) ⟨4592048, by rfl⟩ : syracuseStep 6122731 = 9184097) B9184097
theorem B8163641 : Blo 2263435 8163641 := bstep (se 2 (by rfl) ⟨3061365, by rfl⟩ : syracuseStep 8163641 = 6122731) B6122731
theorem B5442427 : Blo 2263435 5442427 := bstep (se 1 (by rfl) ⟨4081820, by rfl⟩ : syracuseStep 5442427 = 8163641) B8163641
theorem B7256569 : Blo 2263435 7256569 := bstep (se 2 (by rfl) ⟨2721213, by rfl⟩ : syracuseStep 7256569 = 5442427) B5442427
theorem B9675425 : Blo 2263435 9675425 := bstep (se 2 (by rfl) ⟨3628284, by rfl⟩ : syracuseStep 9675425 = 7256569) B7256569
theorem B6450283 : Blo 2263435 6450283 := bstep (se 1 (by rfl) ⟨4837712, by rfl⟩ : syracuseStep 6450283 = 9675425) B9675425
theorem B8600377 : Blo 2263435 8600377 := bstep (se 2 (by rfl) ⟨3225141, by rfl⟩ : syracuseStep 8600377 = 6450283) B6450283
theorem B11467169 : Blo 2263435 11467169 := bstep (se 2 (by rfl) ⟨4300188, by rfl⟩ : syracuseStep 11467169 = 8600377) B8600377
theorem B7644779 : Blo 2263435 7644779 := bstep (se 1 (by rfl) ⟨5733584, by rfl⟩ : syracuseStep 7644779 = 11467169) B11467169
theorem B5096519 : Blo 2263435 5096519 := bstep (se 1 (by rfl) ⟨3822389, by rfl⟩ : syracuseStep 5096519 = 7644779) B7644779
theorem B3397679 : Blo 2263435 3397679 := bstep (se 1 (by rfl) ⟨2548259, by rfl⟩ : syracuseStep 3397679 = 5096519) B5096519
theorem B2265119 : Blo 2263435 2265119 := bstep (se 1 (by rfl) ⟨1698839, by rfl⟩ : syracuseStep 2265119 = 3397679) B3397679
theorem B3397685 : Blo 2263435 3397685 := bbase (se 5 (by rfl) ⟨159266, by rfl⟩ : syracuseStep 3397685 = 318533) (by norm_num)
theorem B2265123 : Blo 2263435 2265123 := bstep (se 1 (by rfl) ⟨1698842, by rfl⟩ : syracuseStep 2265123 = 3397685) B3397685
theorem B5733605 : Blo 2263435 5733605 := bbase (se 4 (by rfl) ⟨537525, by rfl⟩ : syracuseStep 5733605 = 1075051) (by norm_num)
theorem B3822403 : Blo 2263435 3822403 := bstep (se 1 (by rfl) ⟨2866802, by rfl⟩ : syracuseStep 3822403 = 5733605) B5733605
theorem B5096537 : Blo 2263435 5096537 := bstep (se 2 (by rfl) ⟨1911201, by rfl⟩ : syracuseStep 5096537 = 3822403) B3822403
theorem B3397691 : Blo 2263435 3397691 := bstep (se 1 (by rfl) ⟨2548268, by rfl⟩ : syracuseStep 3397691 = 5096537) B5096537
theorem B2265127 : Blo 2263435 2265127 := bstep (se 1 (by rfl) ⟨1698845, by rfl⟩ : syracuseStep 2265127 = 3397691) B3397691
theorem B2548273 : Blo 2263435 2548273 := bbase (se 2 (by rfl) ⟨955602, by rfl⟩ : syracuseStep 2548273 = 1911205) (by norm_num)
theorem B3397697 : Blo 2263435 3397697 := bstep (se 2 (by rfl) ⟨1274136, by rfl⟩ : syracuseStep 3397697 = 2548273) B2548273
theorem B2265131 : Blo 2263435 2265131 := bstep (se 1 (by rfl) ⟨1698848, by rfl⟩ : syracuseStep 2265131 = 3397697) B3397697
theorem B2721233 : Blo 2263435 2721233 := bbase (se 2 (by rfl) ⟨1020462, by rfl⟩ : syracuseStep 2721233 = 2040925) (by norm_num)
theorem B7256621 : Blo 2263435 7256621 := bstep (se 3 (by rfl) ⟨1360616, by rfl⟩ : syracuseStep 7256621 = 2721233) B2721233
theorem B4837747 : Blo 2263435 4837747 := bstep (se 1 (by rfl) ⟨3628310, by rfl⟩ : syracuseStep 4837747 = 7256621) B7256621
theorem B6450329 : Blo 2263435 6450329 := bstep (se 2 (by rfl) ⟨2418873, by rfl⟩ : syracuseStep 6450329 = 4837747) B4837747
theorem B4300219 : Blo 2263435 4300219 := bstep (se 1 (by rfl) ⟨3225164, by rfl⟩ : syracuseStep 4300219 = 6450329) B6450329
theorem B5733625 : Blo 2263435 5733625 := bstep (se 2 (by rfl) ⟨2150109, by rfl⟩ : syracuseStep 5733625 = 4300219) B4300219
theorem B7644833 : Blo 2263435 7644833 := bstep (se 2 (by rfl) ⟨2866812, by rfl⟩ : syracuseStep 7644833 = 5733625) B5733625
theorem B5096555 : Blo 2263435 5096555 := bstep (se 1 (by rfl) ⟨3822416, by rfl⟩ : syracuseStep 5096555 = 7644833) B7644833
theorem B3397703 : Blo 2263435 3397703 := bstep (se 1 (by rfl) ⟨2548277, by rfl⟩ : syracuseStep 3397703 = 5096555) B5096555
theorem B2265135 : Blo 2263435 2265135 := bstep (se 1 (by rfl) ⟨1698851, by rfl⟩ : syracuseStep 2265135 = 3397703) B3397703
theorem B3397709 : Blo 2263435 3397709 := bbase (se 3 (by rfl) ⟨637070, by rfl⟩ : syracuseStep 3397709 = 1274141) (by norm_num)
theorem B2265139 : Blo 2263435 2265139 := bstep (se 1 (by rfl) ⟨1698854, by rfl⟩ : syracuseStep 2265139 = 3397709) B3397709
theorem B5096573 : Blo 2263435 5096573 := bbase (se 3 (by rfl) ⟨955607, by rfl⟩ : syracuseStep 5096573 = 1911215) (by norm_num)
theorem B3397715 : Blo 2263435 3397715 := bstep (se 1 (by rfl) ⟨2548286, by rfl⟩ : syracuseStep 3397715 = 5096573) B5096573
theorem B2265143 : Blo 2263435 2265143 := bstep (se 1 (by rfl) ⟨1698857, by rfl⟩ : syracuseStep 2265143 = 3397715) B3397715
theorem B3822437 : Blo 2263435 3822437 := bbase (se 4 (by rfl) ⟨358353, by rfl⟩ : syracuseStep 3822437 = 716707) (by norm_num)
theorem B2548291 : Blo 2263435 2548291 := bstep (se 1 (by rfl) ⟨1911218, by rfl⟩ : syracuseStep 2548291 = 3822437) B3822437
theorem B3397721 : Blo 2263435 3397721 := bstep (se 2 (by rfl) ⟨1274145, by rfl⟩ : syracuseStep 3397721 = 2548291) B2548291
theorem B2265147 : Blo 2263435 2265147 := bstep (se 1 (by rfl) ⟨1698860, by rfl⟩ : syracuseStep 2265147 = 3397721) B3397721
theorem B4837781 : Blo 2263435 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B3225187 : Blo 2263435 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B17200997 : Blo 2263435 17200997 := bstep (se 4 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 17200997 = 3225187) B3225187
theorem B11467331 : Blo 2263435 11467331 := bstep (se 1 (by rfl) ⟨8600498, by rfl⟩ : syracuseStep 11467331 = 17200997) B17200997
theorem B7644887 : Blo 2263435 7644887 := bstep (se 1 (by rfl) ⟨5733665, by rfl⟩ : syracuseStep 7644887 = 11467331) B11467331
theorem B5096591 : Blo 2263435 5096591 := bstep (se 1 (by rfl) ⟨3822443, by rfl⟩ : syracuseStep 5096591 = 7644887) B7644887
theorem B3397727 : Blo 2263435 3397727 := bstep (se 1 (by rfl) ⟨2548295, by rfl⟩ : syracuseStep 3397727 = 5096591) B5096591
theorem B2265151 : Blo 2263435 2265151 := bstep (se 1 (by rfl) ⟨1698863, by rfl⟩ : syracuseStep 2265151 = 3397727) B3397727
theorem B3397733 : Blo 2263435 3397733 := bbase (se 4 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 3397733 = 637075) (by norm_num)
theorem B2265155 : Blo 2263435 2265155 := bstep (se 1 (by rfl) ⟨1698866, by rfl⟩ : syracuseStep 2265155 = 3397733) B3397733
theorem B9184261 : Blo 2263435 9184261 := bbase (se 4 (by rfl) ⟨861024, by rfl⟩ : syracuseStep 9184261 = 1722049) (by norm_num)
theorem B12245681 : Blo 2263435 12245681 := bstep (se 2 (by rfl) ⟨4592130, by rfl⟩ : syracuseStep 12245681 = 9184261) B9184261
theorem B8163787 : Blo 2263435 8163787 := bstep (se 1 (by rfl) ⟨6122840, by rfl⟩ : syracuseStep 8163787 = 12245681) B12245681
theorem B10885049 : Blo 2263435 10885049 := bstep (se 2 (by rfl) ⟨4081893, by rfl⟩ : syracuseStep 10885049 = 8163787) B8163787
theorem B7256699 : Blo 2263435 7256699 := bstep (se 1 (by rfl) ⟨5442524, by rfl⟩ : syracuseStep 7256699 = 10885049) B10885049
theorem B4837799 : Blo 2263435 4837799 := bstep (se 1 (by rfl) ⟨3628349, by rfl⟩ : syracuseStep 4837799 = 7256699) B7256699
theorem B3225199 : Blo 2263435 3225199 := bstep (se 1 (by rfl) ⟨2418899, by rfl⟩ : syracuseStep 3225199 = 4837799) B4837799
theorem B4300265 : Blo 2263435 4300265 := bstep (se 2 (by rfl) ⟨1612599, by rfl⟩ : syracuseStep 4300265 = 3225199) B3225199
theorem B2866843 : Blo 2263435 2866843 := bstep (se 1 (by rfl) ⟨2150132, by rfl⟩ : syracuseStep 2866843 = 4300265) B4300265
theorem B3822457 : Blo 2263435 3822457 := bstep (se 2 (by rfl) ⟨1433421, by rfl⟩ : syracuseStep 3822457 = 2866843) B2866843
theorem B5096609 : Blo 2263435 5096609 := bstep (se 2 (by rfl) ⟨1911228, by rfl⟩ : syracuseStep 5096609 = 3822457) B3822457
theorem B3397739 : Blo 2263435 3397739 := bstep (se 1 (by rfl) ⟨2548304, by rfl⟩ : syracuseStep 3397739 = 5096609) B5096609
theorem B2265159 : Blo 2263435 2265159 := bstep (se 1 (by rfl) ⟨1698869, by rfl⟩ : syracuseStep 2265159 = 3397739) B3397739
theorem B2548309 : Blo 2263435 2548309 := bbase (se 8 (by rfl) ⟨14931, by rfl⟩ : syracuseStep 2548309 = 29863) (by norm_num)
theorem B3397745 : Blo 2263435 3397745 := bstep (se 2 (by rfl) ⟨1274154, by rfl⟩ : syracuseStep 3397745 = 2548309) B2548309
theorem B2265163 : Blo 2263435 2265163 := bstep (se 1 (by rfl) ⟨1698872, by rfl⟩ : syracuseStep 2265163 = 3397745) B3397745
theorem B2866853 : Blo 2263435 2866853 := bbase (se 4 (by rfl) ⟨268767, by rfl⟩ : syracuseStep 2866853 = 537535) (by norm_num)
theorem B7644941 : Blo 2263435 7644941 := bstep (se 3 (by rfl) ⟨1433426, by rfl⟩ : syracuseStep 7644941 = 2866853) B2866853
theorem B5096627 : Blo 2263435 5096627 := bstep (se 1 (by rfl) ⟨3822470, by rfl⟩ : syracuseStep 5096627 = 7644941) B7644941
theorem B3397751 : Blo 2263435 3397751 := bstep (se 1 (by rfl) ⟨2548313, by rfl⟩ : syracuseStep 3397751 = 5096627) B5096627
theorem B2265167 : Blo 2263435 2265167 := bstep (se 1 (by rfl) ⟨1698875, by rfl⟩ : syracuseStep 2265167 = 3397751) B3397751
theorem B3397757 : Blo 2263435 3397757 := bbase (se 3 (by rfl) ⟨637079, by rfl⟩ : syracuseStep 3397757 = 1274159) (by norm_num)
theorem B2265171 : Blo 2263435 2265171 := bstep (se 1 (by rfl) ⟨1698878, by rfl⟩ : syracuseStep 2265171 = 3397757) B3397757
theorem B5096645 : Blo 2263435 5096645 := bbase (se 4 (by rfl) ⟨477810, by rfl⟩ : syracuseStep 5096645 = 955621) (by norm_num)
theorem B3397763 : Blo 2263435 3397763 := bstep (se 1 (by rfl) ⟨2548322, by rfl⟩ : syracuseStep 3397763 = 5096645) B5096645
theorem B2265175 : Blo 2263435 2265175 := bstep (se 1 (by rfl) ⟨1698881, by rfl⟩ : syracuseStep 2265175 = 3397763) B3397763
theorem B14513525 : Blo 2263435 14513525 := bbase (se 5 (by rfl) ⟨680321, by rfl⟩ : syracuseStep 14513525 = 1360643) (by norm_num)
theorem B9675683 : Blo 2263435 9675683 := bstep (se 1 (by rfl) ⟨7256762, by rfl⟩ : syracuseStep 9675683 = 14513525) B14513525
theorem B6450455 : Blo 2263435 6450455 := bstep (se 1 (by rfl) ⟨4837841, by rfl⟩ : syracuseStep 6450455 = 9675683) B9675683
theorem B4300303 : Blo 2263435 4300303 := bstep (se 1 (by rfl) ⟨3225227, by rfl⟩ : syracuseStep 4300303 = 6450455) B6450455
theorem B5733737 : Blo 2263435 5733737 := bstep (se 2 (by rfl) ⟨2150151, by rfl⟩ : syracuseStep 5733737 = 4300303) B4300303
theorem B3822491 : Blo 2263435 3822491 := bstep (se 1 (by rfl) ⟨2866868, by rfl⟩ : syracuseStep 3822491 = 5733737) B5733737
theorem B2548327 : Blo 2263435 2548327 := bstep (se 1 (by rfl) ⟨1911245, by rfl⟩ : syracuseStep 2548327 = 3822491) B3822491
theorem B3397769 : Blo 2263435 3397769 := bstep (se 2 (by rfl) ⟨1274163, by rfl⟩ : syracuseStep 3397769 = 2548327) B2548327
theorem B2265179 : Blo 2263435 2265179 := bstep (se 1 (by rfl) ⟨1698884, by rfl⟩ : syracuseStep 2265179 = 3397769) B3397769
theorem B11467493 : Blo 2263435 11467493 := bbase (se 4 (by rfl) ⟨1075077, by rfl⟩ : syracuseStep 11467493 = 2150155) (by norm_num)
theorem B7644995 : Blo 2263435 7644995 := bstep (se 1 (by rfl) ⟨5733746, by rfl⟩ : syracuseStep 7644995 = 11467493) B11467493
theorem B5096663 : Blo 2263435 5096663 := bstep (se 1 (by rfl) ⟨3822497, by rfl⟩ : syracuseStep 5096663 = 7644995) B7644995
theorem B3397775 : Blo 2263435 3397775 := bstep (se 1 (by rfl) ⟨2548331, by rfl⟩ : syracuseStep 3397775 = 5096663) B5096663
theorem B2265183 : Blo 2263435 2265183 := bstep (se 1 (by rfl) ⟨1698887, by rfl⟩ : syracuseStep 2265183 = 3397775) B3397775
theorem B3397781 : Blo 2263435 3397781 := bbase (se 6 (by rfl) ⟨79635, by rfl⟩ : syracuseStep 3397781 = 159271) (by norm_num)
theorem B2265187 : Blo 2263435 2265187 := bstep (se 1 (by rfl) ⟨1698890, by rfl⟩ : syracuseStep 2265187 = 3397781) B3397781
theorem B9675733 : Blo 2263435 9675733 := bbase (se 7 (by rfl) ⟨113387, by rfl⟩ : syracuseStep 9675733 = 226775) (by norm_num)
theorem B12900977 : Blo 2263435 12900977 := bstep (se 2 (by rfl) ⟨4837866, by rfl⟩ : syracuseStep 12900977 = 9675733) B9675733
theorem B8600651 : Blo 2263435 8600651 := bstep (se 1 (by rfl) ⟨6450488, by rfl⟩ : syracuseStep 8600651 = 12900977) B12900977
theorem B5733767 : Blo 2263435 5733767 := bstep (se 1 (by rfl) ⟨4300325, by rfl⟩ : syracuseStep 5733767 = 8600651) B8600651
theorem B3822511 : Blo 2263435 3822511 := bstep (se 1 (by rfl) ⟨2866883, by rfl⟩ : syracuseStep 3822511 = 5733767) B5733767
theorem B5096681 : Blo 2263435 5096681 := bstep (se 2 (by rfl) ⟨1911255, by rfl⟩ : syracuseStep 5096681 = 3822511) B3822511
theorem B3397787 : Blo 2263435 3397787 := bstep (se 1 (by rfl) ⟨2548340, by rfl⟩ : syracuseStep 3397787 = 5096681) B5096681
theorem B2265191 : Blo 2263435 2265191 := bstep (se 1 (by rfl) ⟨1698893, by rfl⟩ : syracuseStep 2265191 = 3397787) B3397787
theorem B2548345 : Blo 2263435 2548345 := bbase (se 2 (by rfl) ⟨955629, by rfl⟩ : syracuseStep 2548345 = 1911259) (by norm_num)
theorem B3397793 : Blo 2263435 3397793 := bstep (se 2 (by rfl) ⟨1274172, by rfl⟩ : syracuseStep 3397793 = 2548345) B2548345
theorem B2265195 : Blo 2263435 2265195 := bstep (se 1 (by rfl) ⟨1698896, by rfl⟩ : syracuseStep 2265195 = 3397793) B3397793
theorem B9184421 : Blo 2263435 9184421 := bbase (se 4 (by rfl) ⟨861039, by rfl⟩ : syracuseStep 9184421 = 1722079) (by norm_num)
theorem B6122947 : Blo 2263435 6122947 := bstep (se 1 (by rfl) ⟨4592210, by rfl⟩ : syracuseStep 6122947 = 9184421) B9184421
theorem B8163929 : Blo 2263435 8163929 := bstep (se 2 (by rfl) ⟨3061473, by rfl⟩ : syracuseStep 8163929 = 6122947) B6122947
theorem B21770477 : Blo 2263435 21770477 := bstep (se 3 (by rfl) ⟨4081964, by rfl⟩ : syracuseStep 21770477 = 8163929) B8163929
theorem B14513651 : Blo 2263435 14513651 := bstep (se 1 (by rfl) ⟨10885238, by rfl⟩ : syracuseStep 14513651 = 21770477) B21770477
theorem B9675767 : Blo 2263435 9675767 := bstep (se 1 (by rfl) ⟨7256825, by rfl⟩ : syracuseStep 9675767 = 14513651) B14513651
theorem B6450511 : Blo 2263435 6450511 := bstep (se 1 (by rfl) ⟨4837883, by rfl⟩ : syracuseStep 6450511 = 9675767) B9675767
theorem B8600681 : Blo 2263435 8600681 := bstep (se 2 (by rfl) ⟨3225255, by rfl⟩ : syracuseStep 8600681 = 6450511) B6450511
theorem B5733787 : Blo 2263435 5733787 := bstep (se 1 (by rfl) ⟨4300340, by rfl⟩ : syracuseStep 5733787 = 8600681) B8600681
theorem B7645049 : Blo 2263435 7645049 := bstep (se 2 (by rfl) ⟨2866893, by rfl⟩ : syracuseStep 7645049 = 5733787) B5733787
theorem B5096699 : Blo 2263435 5096699 := bstep (se 1 (by rfl) ⟨3822524, by rfl⟩ : syracuseStep 5096699 = 7645049) B7645049
theorem B3397799 : Blo 2263435 3397799 := bstep (se 1 (by rfl) ⟨2548349, by rfl⟩ : syracuseStep 3397799 = 5096699) B5096699
theorem B2265199 : Blo 2263435 2265199 := bstep (se 1 (by rfl) ⟨1698899, by rfl⟩ : syracuseStep 2265199 = 3397799) B3397799
theorem B3397805 : Blo 2263435 3397805 := bbase (se 3 (by rfl) ⟨637088, by rfl⟩ : syracuseStep 3397805 = 1274177) (by norm_num)
theorem B2265203 : Blo 2263435 2265203 := bstep (se 1 (by rfl) ⟨1698902, by rfl⟩ : syracuseStep 2265203 = 3397805) B3397805
theorem B5096717 : Blo 2263435 5096717 := bbase (se 3 (by rfl) ⟨955634, by rfl⟩ : syracuseStep 5096717 = 1911269) (by norm_num)
theorem B3397811 : Blo 2263435 3397811 := bstep (se 1 (by rfl) ⟨2548358, by rfl⟩ : syracuseStep 3397811 = 5096717) B5096717
theorem B2265207 : Blo 2263435 2265207 := bstep (se 1 (by rfl) ⟨1698905, by rfl⟩ : syracuseStep 2265207 = 3397811) B3397811
theorem B2866909 : Blo 2263435 2866909 := bbase (se 3 (by rfl) ⟨537545, by rfl⟩ : syracuseStep 2866909 = 1075091) (by norm_num)
theorem B3822545 : Blo 2263435 3822545 := bstep (se 2 (by rfl) ⟨1433454, by rfl⟩ : syracuseStep 3822545 = 2866909) B2866909
theorem B2548363 : Blo 2263435 2548363 := bstep (se 1 (by rfl) ⟨1911272, by rfl⟩ : syracuseStep 2548363 = 3822545) B3822545
theorem B3397817 : Blo 2263435 3397817 := bstep (se 2 (by rfl) ⟨1274181, by rfl⟩ : syracuseStep 3397817 = 2548363) B2548363
theorem B2265211 : Blo 2263435 2265211 := bstep (se 1 (by rfl) ⟨1698908, by rfl⟩ : syracuseStep 2265211 = 3397817) B3397817
theorem B19351669 : Blo 2263435 19351669 := bbase (se 5 (by rfl) ⟨907109, by rfl⟩ : syracuseStep 19351669 = 1814219) (by norm_num)
theorem B25802225 : Blo 2263435 25802225 := bstep (se 2 (by rfl) ⟨9675834, by rfl⟩ : syracuseStep 25802225 = 19351669) B19351669
theorem B17201483 : Blo 2263435 17201483 := bstep (se 1 (by rfl) ⟨12901112, by rfl⟩ : syracuseStep 17201483 = 25802225) B25802225
theorem B11467655 : Blo 2263435 11467655 := bstep (se 1 (by rfl) ⟨8600741, by rfl⟩ : syracuseStep 11467655 = 17201483) B17201483
theorem B7645103 : Blo 2263435 7645103 := bstep (se 1 (by rfl) ⟨5733827, by rfl⟩ : syracuseStep 7645103 = 11467655) B11467655
theorem B5096735 : Blo 2263435 5096735 := bstep (se 1 (by rfl) ⟨3822551, by rfl⟩ : syracuseStep 5096735 = 7645103) B7645103
theorem B3397823 : Blo 2263435 3397823 := bstep (se 1 (by rfl) ⟨2548367, by rfl⟩ : syracuseStep 3397823 = 5096735) B5096735
theorem B2265215 : Blo 2263435 2265215 := bstep (se 1 (by rfl) ⟨1698911, by rfl⟩ : syracuseStep 2265215 = 3397823) B3397823
theorem B3397829 : Blo 2263435 3397829 := bbase (se 4 (by rfl) ⟨318546, by rfl⟩ : syracuseStep 3397829 = 637093) (by norm_num)
theorem B2265219 : Blo 2263435 2265219 := bstep (se 1 (by rfl) ⟨1698914, by rfl⟩ : syracuseStep 2265219 = 3397829) B3397829
theorem B3822565 : Blo 2263435 3822565 := bbase (se 4 (by rfl) ⟨358365, by rfl⟩ : syracuseStep 3822565 = 716731) (by norm_num)
theorem B5096753 : Blo 2263435 5096753 := bstep (se 2 (by rfl) ⟨1911282, by rfl⟩ : syracuseStep 5096753 = 3822565) B3822565
theorem B3397835 : Blo 2263435 3397835 := bstep (se 1 (by rfl) ⟨2548376, by rfl⟩ : syracuseStep 3397835 = 5096753) B5096753
theorem B2265223 : Blo 2263435 2265223 := bstep (se 1 (by rfl) ⟨1698917, by rfl⟩ : syracuseStep 2265223 = 3397835) B3397835
theorem B2548381 : Blo 2263435 2548381 := bbase (se 3 (by rfl) ⟨477821, by rfl⟩ : syracuseStep 2548381 = 955643) (by norm_num)
theorem B3397841 : Blo 2263435 3397841 := bstep (se 2 (by rfl) ⟨1274190, by rfl⟩ : syracuseStep 3397841 = 2548381) B2548381
theorem B2265227 : Blo 2263435 2265227 := bstep (se 1 (by rfl) ⟨1698920, by rfl⟩ : syracuseStep 2265227 = 3397841) B3397841
theorem B7645157 : Blo 2263435 7645157 := bbase (se 4 (by rfl) ⟨716733, by rfl⟩ : syracuseStep 7645157 = 1433467) (by norm_num)
theorem B5096771 : Blo 2263435 5096771 := bstep (se 1 (by rfl) ⟨3822578, by rfl⟩ : syracuseStep 5096771 = 7645157) B7645157
theorem B3397847 : Blo 2263435 3397847 := bstep (se 1 (by rfl) ⟨2548385, by rfl⟩ : syracuseStep 3397847 = 5096771) B5096771
theorem B2265231 : Blo 2263435 2265231 := bstep (se 1 (by rfl) ⟨1698923, by rfl⟩ : syracuseStep 2265231 = 3397847) B3397847
theorem B3397853 : Blo 2263435 3397853 := bbase (se 3 (by rfl) ⟨637097, by rfl⟩ : syracuseStep 3397853 = 1274195) (by norm_num)
theorem B2265235 : Blo 2263435 2265235 := bstep (se 1 (by rfl) ⟨1698926, by rfl⟩ : syracuseStep 2265235 = 3397853) B3397853
theorem B5096789 : Blo 2263435 5096789 := bbase (se 12 (by rfl) ⟨1866, by rfl⟩ : syracuseStep 5096789 = 3733) (by norm_num)
theorem B3397859 : Blo 2263435 3397859 := bstep (se 1 (by rfl) ⟨2548394, by rfl⟩ : syracuseStep 3397859 = 5096789) B5096789
theorem B2265239 : Blo 2263435 2265239 := bstep (se 1 (by rfl) ⟨1698929, by rfl⟩ : syracuseStep 2265239 = 3397859) B3397859
theorem B2418989 : Blo 2263435 2418989 := bbase (se 3 (by rfl) ⟨453560, by rfl⟩ : syracuseStep 2418989 = 907121) (by norm_num)
theorem B6450637 : Blo 2263435 6450637 := bstep (se 3 (by rfl) ⟨1209494, by rfl⟩ : syracuseStep 6450637 = 2418989) B2418989
theorem B8600849 : Blo 2263435 8600849 := bstep (se 2 (by rfl) ⟨3225318, by rfl⟩ : syracuseStep 8600849 = 6450637) B6450637
theorem B5733899 : Blo 2263435 5733899 := bstep (se 1 (by rfl) ⟨4300424, by rfl⟩ : syracuseStep 5733899 = 8600849) B8600849
theorem B3822599 : Blo 2263435 3822599 := bstep (se 1 (by rfl) ⟨2866949, by rfl⟩ : syracuseStep 3822599 = 5733899) B5733899
theorem B2548399 : Blo 2263435 2548399 := bstep (se 1 (by rfl) ⟨1911299, by rfl⟩ : syracuseStep 2548399 = 3822599) B3822599
theorem B3397865 : Blo 2263435 3397865 := bstep (se 2 (by rfl) ⟨1274199, by rfl⟩ : syracuseStep 3397865 = 2548399) B2548399
theorem B2265243 : Blo 2263435 2265243 := bstep (se 1 (by rfl) ⟨1698932, by rfl⟩ : syracuseStep 2265243 = 3397865) B3397865
theorem B32656405 : Blo 2263435 32656405 := bbase (se 6 (by rfl) ⟨765384, by rfl⟩ : syracuseStep 32656405 = 1530769) (by norm_num)
theorem B43541873 : Blo 2263435 43541873 := bstep (se 2 (by rfl) ⟨16328202, by rfl⟩ : syracuseStep 43541873 = 32656405) B32656405
theorem B29027915 : Blo 2263435 29027915 := bstep (se 1 (by rfl) ⟨21770936, by rfl⟩ : syracuseStep 29027915 = 43541873) B43541873
theorem B19351943 : Blo 2263435 19351943 := bstep (se 1 (by rfl) ⟨14513957, by rfl⟩ : syracuseStep 19351943 = 29027915) B29027915
theorem B12901295 : Blo 2263435 12901295 := bstep (se 1 (by rfl) ⟨9675971, by rfl⟩ : syracuseStep 12901295 = 19351943) B19351943
theorem B8600863 : Blo 2263435 8600863 := bstep (se 1 (by rfl) ⟨6450647, by rfl⟩ : syracuseStep 8600863 = 12901295) B12901295
theorem B11467817 : Blo 2263435 11467817 := bstep (se 2 (by rfl) ⟨4300431, by rfl⟩ : syracuseStep 11467817 = 8600863) B8600863
theorem B7645211 : Blo 2263435 7645211 := bstep (se 1 (by rfl) ⟨5733908, by rfl⟩ : syracuseStep 7645211 = 11467817) B11467817
theorem B5096807 : Blo 2263435 5096807 := bstep (se 1 (by rfl) ⟨3822605, by rfl⟩ : syracuseStep 5096807 = 7645211) B7645211
theorem B3397871 : Blo 2263435 3397871 := bstep (se 1 (by rfl) ⟨2548403, by rfl⟩ : syracuseStep 3397871 = 5096807) B5096807
theorem B2265247 : Blo 2263435 2265247 := bstep (se 1 (by rfl) ⟨1698935, by rfl⟩ : syracuseStep 2265247 = 3397871) B3397871
theorem B3397877 : Blo 2263435 3397877 := bbase (se 5 (by rfl) ⟨159275, by rfl⟩ : syracuseStep 3397877 = 318551) (by norm_num)
theorem B2265251 : Blo 2263435 2265251 := bstep (se 1 (by rfl) ⟨1698938, by rfl⟩ : syracuseStep 2265251 = 3397877) B3397877
theorem B5517013 : Blo 2263435 5517013 := bbase (se 7 (by rfl) ⟨64652, by rfl⟩ : syracuseStep 5517013 = 129305) (by norm_num)
theorem B7356017 : Blo 2263435 7356017 := bstep (se 2 (by rfl) ⟨2758506, by rfl⟩ : syracuseStep 7356017 = 5517013) B5517013
theorem B4904011 : Blo 2263435 4904011 := bstep (se 1 (by rfl) ⟨3678008, by rfl⟩ : syracuseStep 4904011 = 7356017) B7356017
theorem B6538681 : Blo 2263435 6538681 := bstep (se 2 (by rfl) ⟨2452005, by rfl⟩ : syracuseStep 6538681 = 4904011) B4904011
theorem B8718241 : Blo 2263435 8718241 := bstep (se 2 (by rfl) ⟨3269340, by rfl⟩ : syracuseStep 8718241 = 6538681) B6538681
theorem B11624321 : Blo 2263435 11624321 := bstep (se 2 (by rfl) ⟨4359120, by rfl⟩ : syracuseStep 11624321 = 8718241) B8718241
theorem B30998189 : Blo 2263435 30998189 := bstep (se 3 (by rfl) ⟨5812160, by rfl⟩ : syracuseStep 30998189 = 11624321) B11624321
theorem B20665459 : Blo 2263435 20665459 := bstep (se 1 (by rfl) ⟨15499094, by rfl⟩ : syracuseStep 20665459 = 30998189) B30998189
theorem B27553945 : Blo 2263435 27553945 := bstep (se 2 (by rfl) ⟨10332729, by rfl⟩ : syracuseStep 27553945 = 20665459) B20665459
theorem B36738593 : Blo 2263435 36738593 := bstep (se 2 (by rfl) ⟨13776972, by rfl⟩ : syracuseStep 36738593 = 27553945) B27553945
theorem B24492395 : Blo 2263435 24492395 := bstep (se 1 (by rfl) ⟨18369296, by rfl⟩ : syracuseStep 24492395 = 36738593) B36738593
theorem B16328263 : Blo 2263435 16328263 := bstep (se 1 (by rfl) ⟨12246197, by rfl⟩ : syracuseStep 16328263 = 24492395) B24492395
theorem B21771017 : Blo 2263435 21771017 := bstep (se 2 (by rfl) ⟨8164131, by rfl⟩ : syracuseStep 21771017 = 16328263) B16328263
theorem B14514011 : Blo 2263435 14514011 := bstep (se 1 (by rfl) ⟨10885508, by rfl⟩ : syracuseStep 14514011 = 21771017) B21771017
theorem B9676007 : Blo 2263435 9676007 := bstep (se 1 (by rfl) ⟨7257005, by rfl⟩ : syracuseStep 9676007 = 14514011) B14514011
theorem B6450671 : Blo 2263435 6450671 := bstep (se 1 (by rfl) ⟨4838003, by rfl⟩ : syracuseStep 6450671 = 9676007) B9676007
theorem B4300447 : Blo 2263435 4300447 := bstep (se 1 (by rfl) ⟨3225335, by rfl⟩ : syracuseStep 4300447 = 6450671) B6450671
theorem B5733929 : Blo 2263435 5733929 := bstep (se 2 (by rfl) ⟨2150223, by rfl⟩ : syracuseStep 5733929 = 4300447) B4300447
theorem B3822619 : Blo 2263435 3822619 := bstep (se 1 (by rfl) ⟨2866964, by rfl⟩ : syracuseStep 3822619 = 5733929) B5733929
theorem B5096825 : Blo 2263435 5096825 := bstep (se 2 (by rfl) ⟨1911309, by rfl⟩ : syracuseStep 5096825 = 3822619) B3822619
theorem B3397883 : Blo 2263435 3397883 := bstep (se 1 (by rfl) ⟨2548412, by rfl⟩ : syracuseStep 3397883 = 5096825) B5096825
theorem B2265255 : Blo 2263435 2265255 := bstep (se 1 (by rfl) ⟨1698941, by rfl⟩ : syracuseStep 2265255 = 3397883) B3397883
theorem B2548417 : Blo 2263435 2548417 := bbase (se 2 (by rfl) ⟨955656, by rfl⟩ : syracuseStep 2548417 = 1911313) (by norm_num)
theorem B3397889 : Blo 2263435 3397889 := bstep (se 2 (by rfl) ⟨1274208, by rfl⟩ : syracuseStep 3397889 = 2548417) B2548417
theorem B2265259 : Blo 2263435 2265259 := bstep (se 1 (by rfl) ⟨1698944, by rfl⟩ : syracuseStep 2265259 = 3397889) B3397889
theorem B5733949 : Blo 2263435 5733949 := bbase (se 3 (by rfl) ⟨1075115, by rfl⟩ : syracuseStep 5733949 = 2150231) (by norm_num)
theorem B7645265 : Blo 2263435 7645265 := bstep (se 2 (by rfl) ⟨2866974, by rfl⟩ : syracuseStep 7645265 = 5733949) B5733949
theorem B5096843 : Blo 2263435 5096843 := bstep (se 1 (by rfl) ⟨3822632, by rfl⟩ : syracuseStep 5096843 = 7645265) B7645265
theorem B3397895 : Blo 2263435 3397895 := bstep (se 1 (by rfl) ⟨2548421, by rfl⟩ : syracuseStep 3397895 = 5096843) B5096843
theorem B2265263 : Blo 2263435 2265263 := bstep (se 1 (by rfl) ⟨1698947, by rfl⟩ : syracuseStep 2265263 = 3397895) B3397895
theorem B3397901 : Blo 2263435 3397901 := bbase (se 3 (by rfl) ⟨637106, by rfl⟩ : syracuseStep 3397901 = 1274213) (by norm_num)
theorem B2265267 : Blo 2263435 2265267 := bstep (se 1 (by rfl) ⟨1698950, by rfl⟩ : syracuseStep 2265267 = 3397901) B3397901
theorem B5096861 : Blo 2263435 5096861 := bbase (se 3 (by rfl) ⟨955661, by rfl⟩ : syracuseStep 5096861 = 1911323) (by norm_num)
theorem B3397907 : Blo 2263435 3397907 := bstep (se 1 (by rfl) ⟨2548430, by rfl⟩ : syracuseStep 3397907 = 5096861) B5096861
theorem B2265271 : Blo 2263435 2265271 := bstep (se 1 (by rfl) ⟨1698953, by rfl⟩ : syracuseStep 2265271 = 3397907) B3397907
theorem B3822653 : Blo 2263435 3822653 := bbase (se 3 (by rfl) ⟨716747, by rfl⟩ : syracuseStep 3822653 = 1433495) (by norm_num)
theorem B2548435 : Blo 2263435 2548435 := bstep (se 1 (by rfl) ⟨1911326, by rfl⟩ : syracuseStep 2548435 = 3822653) B3822653
theorem B3397913 : Blo 2263435 3397913 := bstep (se 2 (by rfl) ⟨1274217, by rfl⟩ : syracuseStep 3397913 = 2548435) B2548435
theorem B2265275 : Blo 2263435 2265275 := bstep (se 1 (by rfl) ⟨1698956, by rfl⟩ : syracuseStep 2265275 = 3397913) B3397913
theorem B3628541 : Blo 2263435 3628541 := bbase (se 3 (by rfl) ⟨680351, by rfl⟩ : syracuseStep 3628541 = 1360703) (by norm_num)
theorem B2419027 : Blo 2263435 2419027 := bstep (se 1 (by rfl) ⟨1814270, by rfl⟩ : syracuseStep 2419027 = 3628541) B3628541
theorem B12901477 : Blo 2263435 12901477 := bstep (se 4 (by rfl) ⟨1209513, by rfl⟩ : syracuseStep 12901477 = 2419027) B2419027
theorem B17201969 : Blo 2263435 17201969 := bstep (se 2 (by rfl) ⟨6450738, by rfl⟩ : syracuseStep 17201969 = 12901477) B12901477
theorem B11467979 : Blo 2263435 11467979 := bstep (se 1 (by rfl) ⟨8600984, by rfl⟩ : syracuseStep 11467979 = 17201969) B17201969
theorem B7645319 : Blo 2263435 7645319 := bstep (se 1 (by rfl) ⟨5733989, by rfl⟩ : syracuseStep 7645319 = 11467979) B11467979
theorem B5096879 : Blo 2263435 5096879 := bstep (se 1 (by rfl) ⟨3822659, by rfl⟩ : syracuseStep 5096879 = 7645319) B7645319
theorem B3397919 : Blo 2263435 3397919 := bstep (se 1 (by rfl) ⟨2548439, by rfl⟩ : syracuseStep 3397919 = 5096879) B5096879
theorem B2265279 : Blo 2263435 2265279 := bstep (se 1 (by rfl) ⟨1698959, by rfl⟩ : syracuseStep 2265279 = 3397919) B3397919
theorem B3397925 : Blo 2263435 3397925 := bbase (se 4 (by rfl) ⟨318555, by rfl⟩ : syracuseStep 3397925 = 637111) (by norm_num)
theorem B2265283 : Blo 2263435 2265283 := bstep (se 1 (by rfl) ⟨1698962, by rfl⟩ : syracuseStep 2265283 = 3397925) B3397925
theorem B2867005 : Blo 2263435 2867005 := bbase (se 3 (by rfl) ⟨537563, by rfl⟩ : syracuseStep 2867005 = 1075127) (by norm_num)
theorem B3822673 : Blo 2263435 3822673 := bstep (se 2 (by rfl) ⟨1433502, by rfl⟩ : syracuseStep 3822673 = 2867005) B2867005
theorem B5096897 : Blo 2263435 5096897 := bstep (se 2 (by rfl) ⟨1911336, by rfl⟩ : syracuseStep 5096897 = 3822673) B3822673
theorem B3397931 : Blo 2263435 3397931 := bstep (se 1 (by rfl) ⟨2548448, by rfl⟩ : syracuseStep 3397931 = 5096897) B5096897
theorem B2265287 : Blo 2263435 2265287 := bstep (se 1 (by rfl) ⟨1698965, by rfl⟩ : syracuseStep 2265287 = 3397931) B3397931
theorem B2548453 : Blo 2263435 2548453 := bbase (se 4 (by rfl) ⟨238917, by rfl⟩ : syracuseStep 2548453 = 477835) (by norm_num)
theorem B3397937 : Blo 2263435 3397937 := bstep (se 2 (by rfl) ⟨1274226, by rfl⟩ : syracuseStep 3397937 = 2548453) B2548453
theorem B2265291 : Blo 2263435 2265291 := bstep (se 1 (by rfl) ⟨1698968, by rfl⟩ : syracuseStep 2265291 = 3397937) B3397937
theorem B8164277 : Blo 2263435 8164277 := bbase (se 5 (by rfl) ⟨382700, by rfl⟩ : syracuseStep 8164277 = 765401) (by norm_num)
theorem B5442851 : Blo 2263435 5442851 := bstep (se 1 (by rfl) ⟨4082138, by rfl⟩ : syracuseStep 5442851 = 8164277) B8164277
theorem B3628567 : Blo 2263435 3628567 := bstep (se 1 (by rfl) ⟨2721425, by rfl⟩ : syracuseStep 3628567 = 5442851) B5442851
theorem B4838089 : Blo 2263435 4838089 := bstep (se 2 (by rfl) ⟨1814283, by rfl⟩ : syracuseStep 4838089 = 3628567) B3628567
theorem B6450785 : Blo 2263435 6450785 := bstep (se 2 (by rfl) ⟨2419044, by rfl⟩ : syracuseStep 6450785 = 4838089) B4838089
theorem B4300523 : Blo 2263435 4300523 := bstep (se 1 (by rfl) ⟨3225392, by rfl⟩ : syracuseStep 4300523 = 6450785) B6450785
theorem B2867015 : Blo 2263435 2867015 := bstep (se 1 (by rfl) ⟨2150261, by rfl⟩ : syracuseStep 2867015 = 4300523) B4300523
theorem B7645373 : Blo 2263435 7645373 := bstep (se 3 (by rfl) ⟨1433507, by rfl⟩ : syracuseStep 7645373 = 2867015) B2867015
theorem B5096915 : Blo 2263435 5096915 := bstep (se 1 (by rfl) ⟨3822686, by rfl⟩ : syracuseStep 5096915 = 7645373) B7645373
theorem B3397943 : Blo 2263435 3397943 := bstep (se 1 (by rfl) ⟨2548457, by rfl⟩ : syracuseStep 3397943 = 5096915) B5096915
theorem B2265295 : Blo 2263435 2265295 := bstep (se 1 (by rfl) ⟨1698971, by rfl⟩ : syracuseStep 2265295 = 3397943) B3397943
theorem B3397949 : Blo 2263435 3397949 := bbase (se 3 (by rfl) ⟨637115, by rfl⟩ : syracuseStep 3397949 = 1274231) (by norm_num)
theorem B2265299 : Blo 2263435 2265299 := bstep (se 1 (by rfl) ⟨1698974, by rfl⟩ : syracuseStep 2265299 = 3397949) B3397949
theorem B5096933 : Blo 2263435 5096933 := bbase (se 4 (by rfl) ⟨477837, by rfl⟩ : syracuseStep 5096933 = 955675) (by norm_num)
theorem B3397955 : Blo 2263435 3397955 := bstep (se 1 (by rfl) ⟨2548466, by rfl⟩ : syracuseStep 3397955 = 5096933) B5096933
theorem B2265303 : Blo 2263435 2265303 := bstep (se 1 (by rfl) ⟨1698977, by rfl⟩ : syracuseStep 2265303 = 3397955) B3397955
theorem B5734061 : Blo 2263435 5734061 := bbase (se 3 (by rfl) ⟨1075136, by rfl⟩ : syracuseStep 5734061 = 2150273) (by norm_num)
theorem B3822707 : Blo 2263435 3822707 := bstep (se 1 (by rfl) ⟨2867030, by rfl⟩ : syracuseStep 3822707 = 5734061) B5734061
theorem B2548471 : Blo 2263435 2548471 := bstep (se 1 (by rfl) ⟨1911353, by rfl⟩ : syracuseStep 2548471 = 3822707) B3822707
theorem B3397961 : Blo 2263435 3397961 := bstep (se 2 (by rfl) ⟨1274235, by rfl⟩ : syracuseStep 3397961 = 2548471) B2548471
theorem B2265307 : Blo 2263435 2265307 := bstep (se 1 (by rfl) ⟨1698980, by rfl⟩ : syracuseStep 2265307 = 3397961) B3397961
theorem B2327549 : Blo 2263435 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B6206797 : Blo 2263435 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B8275729 : Blo 2263435 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B11034305 : Blo 2263435 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B7356203 : Blo 2263435 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B4904135 : Blo 2263435 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B3269423 : Blo 2263435 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B8718461 : Blo 2263435 8718461 := bstep (se 3 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 8718461 = 3269423) B3269423
theorem B5812307 : Blo 2263435 5812307 := bstep (se 1 (by rfl) ⟨4359230, by rfl⟩ : syracuseStep 5812307 = 8718461) B8718461
theorem B3874871 : Blo 2263435 3874871 := bstep (se 1 (by rfl) ⟨2906153, by rfl⟩ : syracuseStep 3874871 = 5812307) B5812307
theorem B2583247 : Blo 2263435 2583247 := bstep (se 1 (by rfl) ⟨1937435, by rfl⟩ : syracuseStep 2583247 = 3874871) B3874871
theorem B3444329 : Blo 2263435 3444329 := bstep (se 2 (by rfl) ⟨1291623, by rfl⟩ : syracuseStep 3444329 = 2583247) B2583247
theorem B9184877 : Blo 2263435 9184877 := bstep (se 3 (by rfl) ⟨1722164, by rfl⟩ : syracuseStep 9184877 = 3444329) B3444329
theorem B6123251 : Blo 2263435 6123251 := bstep (se 1 (by rfl) ⟨4592438, by rfl⟩ : syracuseStep 6123251 = 9184877) B9184877
theorem B4082167 : Blo 2263435 4082167 := bstep (se 1 (by rfl) ⟨3061625, by rfl⟩ : syracuseStep 4082167 = 6123251) B6123251
theorem B5442889 : Blo 2263435 5442889 := bstep (se 2 (by rfl) ⟨2041083, by rfl⟩ : syracuseStep 5442889 = 4082167) B4082167
theorem B7257185 : Blo 2263435 7257185 := bstep (se 2 (by rfl) ⟨2721444, by rfl⟩ : syracuseStep 7257185 = 5442889) B5442889
theorem B4838123 : Blo 2263435 4838123 := bstep (se 1 (by rfl) ⟨3628592, by rfl⟩ : syracuseStep 4838123 = 7257185) B7257185
theorem B3225415 : Blo 2263435 3225415 := bstep (se 1 (by rfl) ⟨2419061, by rfl⟩ : syracuseStep 3225415 = 4838123) B4838123
theorem B4300553 : Blo 2263435 4300553 := bstep (se 2 (by rfl) ⟨1612707, by rfl⟩ : syracuseStep 4300553 = 3225415) B3225415
theorem B11468141 : Blo 2263435 11468141 := bstep (se 3 (by rfl) ⟨2150276, by rfl⟩ : syracuseStep 11468141 = 4300553) B4300553
theorem B7645427 : Blo 2263435 7645427 := bstep (se 1 (by rfl) ⟨5734070, by rfl⟩ : syracuseStep 7645427 = 11468141) B11468141
theorem B5096951 : Blo 2263435 5096951 := bstep (se 1 (by rfl) ⟨3822713, by rfl⟩ : syracuseStep 5096951 = 7645427) B7645427
theorem B3397967 : Blo 2263435 3397967 := bstep (se 1 (by rfl) ⟨2548475, by rfl⟩ : syracuseStep 3397967 = 5096951) B5096951
theorem B2265311 : Blo 2263435 2265311 := bstep (se 1 (by rfl) ⟨1698983, by rfl⟩ : syracuseStep 2265311 = 3397967) B3397967
theorem B3397973 : Blo 2263435 3397973 := bbase (se 10 (by rfl) ⟨4977, by rfl⟩ : syracuseStep 3397973 = 9955) (by norm_num)
theorem B2265315 : Blo 2263435 2265315 := bstep (se 1 (by rfl) ⟨1698986, by rfl⟩ : syracuseStep 2265315 = 3397973) B3397973
theorem B6450853 : Blo 2263435 6450853 := bbase (se 4 (by rfl) ⟨604767, by rfl⟩ : syracuseStep 6450853 = 1209535) (by norm_num)
theorem B8601137 : Blo 2263435 8601137 := bstep (se 2 (by rfl) ⟨3225426, by rfl⟩ : syracuseStep 8601137 = 6450853) B6450853
theorem B5734091 : Blo 2263435 5734091 := bstep (se 1 (by rfl) ⟨4300568, by rfl⟩ : syracuseStep 5734091 = 8601137) B8601137
theorem B3822727 : Blo 2263435 3822727 := bstep (se 1 (by rfl) ⟨2867045, by rfl⟩ : syracuseStep 3822727 = 5734091) B5734091
theorem B5096969 : Blo 2263435 5096969 := bstep (se 2 (by rfl) ⟨1911363, by rfl⟩ : syracuseStep 5096969 = 3822727) B3822727
theorem B3397979 : Blo 2263435 3397979 := bstep (se 1 (by rfl) ⟨2548484, by rfl⟩ : syracuseStep 3397979 = 5096969) B5096969
theorem B2265319 : Blo 2263435 2265319 := bstep (se 1 (by rfl) ⟨1698989, by rfl⟩ : syracuseStep 2265319 = 3397979) B3397979
theorem B2548489 : Blo 2263435 2548489 := bbase (se 2 (by rfl) ⟨955683, by rfl⟩ : syracuseStep 2548489 = 1911367) (by norm_num)
theorem B3397985 : Blo 2263435 3397985 := bstep (se 2 (by rfl) ⟨1274244, by rfl⟩ : syracuseStep 3397985 = 2548489) B2548489
theorem B2265323 : Blo 2263435 2265323 := bstep (se 1 (by rfl) ⟨1698992, by rfl⟩ : syracuseStep 2265323 = 3397985) B3397985
theorem B2583265 : Blo 2263435 2583265 := bbase (se 2 (by rfl) ⟨968724, by rfl⟩ : syracuseStep 2583265 = 1937449) (by norm_num)
theorem B3444353 : Blo 2263435 3444353 := bstep (se 2 (by rfl) ⟨1291632, by rfl⟩ : syracuseStep 3444353 = 2583265) B2583265
theorem B2296235 : Blo 2263435 2296235 := bstep (se 1 (by rfl) ⟨1722176, by rfl⟩ : syracuseStep 2296235 = 3444353) B3444353
theorem B6123293 : Blo 2263435 6123293 := bstep (se 3 (by rfl) ⟨1148117, by rfl⟩ : syracuseStep 6123293 = 2296235) B2296235
theorem B4082195 : Blo 2263435 4082195 := bstep (se 1 (by rfl) ⟨3061646, by rfl⟩ : syracuseStep 4082195 = 6123293) B6123293
theorem B10885853 : Blo 2263435 10885853 := bstep (se 3 (by rfl) ⟨2041097, by rfl⟩ : syracuseStep 10885853 = 4082195) B4082195
theorem B29028941 : Blo 2263435 29028941 := bstep (se 3 (by rfl) ⟨5442926, by rfl⟩ : syracuseStep 29028941 = 10885853) B10885853
theorem B19352627 : Blo 2263435 19352627 := bstep (se 1 (by rfl) ⟨14514470, by rfl⟩ : syracuseStep 19352627 = 29028941) B29028941
theorem B12901751 : Blo 2263435 12901751 := bstep (se 1 (by rfl) ⟨9676313, by rfl⟩ : syracuseStep 12901751 = 19352627) B19352627
theorem B8601167 : Blo 2263435 8601167 := bstep (se 1 (by rfl) ⟨6450875, by rfl⟩ : syracuseStep 8601167 = 12901751) B12901751
theorem B5734111 : Blo 2263435 5734111 := bstep (se 1 (by rfl) ⟨4300583, by rfl⟩ : syracuseStep 5734111 = 8601167) B8601167
theorem B7645481 : Blo 2263435 7645481 := bstep (se 2 (by rfl) ⟨2867055, by rfl⟩ : syracuseStep 7645481 = 5734111) B5734111
theorem B5096987 : Blo 2263435 5096987 := bstep (se 1 (by rfl) ⟨3822740, by rfl⟩ : syracuseStep 5096987 = 7645481) B7645481
theorem B3397991 : Blo 2263435 3397991 := bstep (se 1 (by rfl) ⟨2548493, by rfl⟩ : syracuseStep 3397991 = 5096987) B5096987
theorem B2265327 : Blo 2263435 2265327 := bstep (se 1 (by rfl) ⟨1698995, by rfl⟩ : syracuseStep 2265327 = 3397991) B3397991
theorem B3397997 : Blo 2263435 3397997 := bbase (se 3 (by rfl) ⟨637124, by rfl⟩ : syracuseStep 3397997 = 1274249) (by norm_num)
theorem B2265331 : Blo 2263435 2265331 := bstep (se 1 (by rfl) ⟨1698998, by rfl⟩ : syracuseStep 2265331 = 3397997) B3397997
theorem B5097005 : Blo 2263435 5097005 := bbase (se 3 (by rfl) ⟨955688, by rfl⟩ : syracuseStep 5097005 = 1911377) (by norm_num)
theorem B3398003 : Blo 2263435 3398003 := bstep (se 1 (by rfl) ⟨2548502, by rfl⟩ : syracuseStep 3398003 = 5097005) B5097005
theorem B2265335 : Blo 2263435 2265335 := bstep (se 1 (by rfl) ⟨1699001, by rfl⟩ : syracuseStep 2265335 = 3398003) B3398003
theorem B2452097 : Blo 2263435 2452097 := bbase (se 2 (by rfl) ⟨919536, by rfl⟩ : syracuseStep 2452097 = 1839073) (by norm_num)
theorem B6538925 : Blo 2263435 6538925 := bstep (se 3 (by rfl) ⟨1226048, by rfl⟩ : syracuseStep 6538925 = 2452097) B2452097
theorem B17437133 : Blo 2263435 17437133 := bstep (se 3 (by rfl) ⟨3269462, by rfl⟩ : syracuseStep 17437133 = 6538925) B6538925
theorem B11624755 : Blo 2263435 11624755 := bstep (se 1 (by rfl) ⟨8718566, by rfl⟩ : syracuseStep 11624755 = 17437133) B17437133
theorem B15499673 : Blo 2263435 15499673 := bstep (se 2 (by rfl) ⟨5812377, by rfl⟩ : syracuseStep 15499673 = 11624755) B11624755
theorem B10333115 : Blo 2263435 10333115 := bstep (se 1 (by rfl) ⟨7749836, by rfl⟩ : syracuseStep 10333115 = 15499673) B15499673
theorem B6888743 : Blo 2263435 6888743 := bstep (se 1 (by rfl) ⟨5166557, by rfl⟩ : syracuseStep 6888743 = 10333115) B10333115
theorem B4592495 : Blo 2263435 4592495 := bstep (se 1 (by rfl) ⟨3444371, by rfl⟩ : syracuseStep 4592495 = 6888743) B6888743
theorem B12246653 : Blo 2263435 12246653 := bstep (se 3 (by rfl) ⟨2296247, by rfl⟩ : syracuseStep 12246653 = 4592495) B4592495
theorem B32657741 : Blo 2263435 32657741 := bstep (se 3 (by rfl) ⟨6123326, by rfl⟩ : syracuseStep 32657741 = 12246653) B12246653
theorem B21771827 : Blo 2263435 21771827 := bstep (se 1 (by rfl) ⟨16328870, by rfl⟩ : syracuseStep 21771827 = 32657741) B32657741
theorem B14514551 : Blo 2263435 14514551 := bstep (se 1 (by rfl) ⟨10885913, by rfl⟩ : syracuseStep 14514551 = 21771827) B21771827
theorem B9676367 : Blo 2263435 9676367 := bstep (se 1 (by rfl) ⟨7257275, by rfl⟩ : syracuseStep 9676367 = 14514551) B14514551
theorem B6450911 : Blo 2263435 6450911 := bstep (se 1 (by rfl) ⟨4838183, by rfl⟩ : syracuseStep 6450911 = 9676367) B9676367
theorem B4300607 : Blo 2263435 4300607 := bstep (se 1 (by rfl) ⟨3225455, by rfl⟩ : syracuseStep 4300607 = 6450911) B6450911
theorem B2867071 : Blo 2263435 2867071 := bstep (se 1 (by rfl) ⟨2150303, by rfl⟩ : syracuseStep 2867071 = 4300607) B4300607
theorem B3822761 : Blo 2263435 3822761 := bstep (se 2 (by rfl) ⟨1433535, by rfl⟩ : syracuseStep 3822761 = 2867071) B2867071
theorem B2548507 : Blo 2263435 2548507 := bstep (se 1 (by rfl) ⟨1911380, by rfl⟩ : syracuseStep 2548507 = 3822761) B3822761
theorem B3398009 : Blo 2263435 3398009 := bstep (se 2 (by rfl) ⟨1274253, by rfl⟩ : syracuseStep 3398009 = 2548507) B2548507
theorem B2265339 : Blo 2263435 2265339 := bstep (se 1 (by rfl) ⟨1699004, by rfl⟩ : syracuseStep 2265339 = 3398009) B3398009
theorem B5442965 : Blo 2263435 5442965 := bbase (se 6 (by rfl) ⟨127569, by rfl⟩ : syracuseStep 5442965 = 255139) (by norm_num)
theorem B3628643 : Blo 2263435 3628643 := bstep (se 1 (by rfl) ⟨2721482, by rfl⟩ : syracuseStep 3628643 = 5442965) B5442965
theorem B38705525 : Blo 2263435 38705525 := bstep (se 5 (by rfl) ⟨1814321, by rfl⟩ : syracuseStep 38705525 = 3628643) B3628643
theorem B25803683 : Blo 2263435 25803683 := bstep (se 1 (by rfl) ⟨19352762, by rfl⟩ : syracuseStep 25803683 = 38705525) B38705525
theorem B17202455 : Blo 2263435 17202455 := bstep (se 1 (by rfl) ⟨12901841, by rfl⟩ : syracuseStep 17202455 = 25803683) B25803683
theorem B11468303 : Blo 2263435 11468303 := bstep (se 1 (by rfl) ⟨8601227, by rfl⟩ : syracuseStep 11468303 = 17202455) B17202455
theorem B7645535 : Blo 2263435 7645535 := bstep (se 1 (by rfl) ⟨5734151, by rfl⟩ : syracuseStep 7645535 = 11468303) B11468303
theorem B5097023 : Blo 2263435 5097023 := bstep (se 1 (by rfl) ⟨3822767, by rfl⟩ : syracuseStep 5097023 = 7645535) B7645535
theorem B3398015 : Blo 2263435 3398015 := bstep (se 1 (by rfl) ⟨2548511, by rfl⟩ : syracuseStep 3398015 = 5097023) B5097023
theorem B2265343 : Blo 2263435 2265343 := bstep (se 1 (by rfl) ⟨1699007, by rfl⟩ : syracuseStep 2265343 = 3398015) B3398015
theorem B3398021 : Blo 2263435 3398021 := bbase (se 4 (by rfl) ⟨318564, by rfl⟩ : syracuseStep 3398021 = 637129) (by norm_num)
theorem B2265347 : Blo 2263435 2265347 := bstep (se 1 (by rfl) ⟨1699010, by rfl⟩ : syracuseStep 2265347 = 3398021) B3398021
theorem B3822781 : Blo 2263435 3822781 := bbase (se 3 (by rfl) ⟨716771, by rfl⟩ : syracuseStep 3822781 = 1433543) (by norm_num)
theorem B5097041 : Blo 2263435 5097041 := bstep (se 2 (by rfl) ⟨1911390, by rfl⟩ : syracuseStep 5097041 = 3822781) B3822781
theorem B3398027 : Blo 2263435 3398027 := bstep (se 1 (by rfl) ⟨2548520, by rfl⟩ : syracuseStep 3398027 = 5097041) B5097041
theorem B2265351 : Blo 2263435 2265351 := bstep (se 1 (by rfl) ⟨1699013, by rfl⟩ : syracuseStep 2265351 = 3398027) B3398027
theorem B2548525 : Blo 2263435 2548525 := bbase (se 3 (by rfl) ⟨477848, by rfl⟩ : syracuseStep 2548525 = 955697) (by norm_num)
theorem B3398033 : Blo 2263435 3398033 := bstep (se 2 (by rfl) ⟨1274262, by rfl⟩ : syracuseStep 3398033 = 2548525) B2548525
theorem B2265355 : Blo 2263435 2265355 := bstep (se 1 (by rfl) ⟨1699016, by rfl⟩ : syracuseStep 2265355 = 3398033) B3398033
theorem B7645589 : Blo 2263435 7645589 := bbase (se 6 (by rfl) ⟨179193, by rfl⟩ : syracuseStep 7645589 = 358387) (by norm_num)
theorem B5097059 : Blo 2263435 5097059 := bstep (se 1 (by rfl) ⟨3822794, by rfl⟩ : syracuseStep 5097059 = 7645589) B7645589
theorem B3398039 : Blo 2263435 3398039 := bstep (se 1 (by rfl) ⟨2548529, by rfl⟩ : syracuseStep 3398039 = 5097059) B5097059
theorem B2265359 : Blo 2263435 2265359 := bstep (se 1 (by rfl) ⟨1699019, by rfl⟩ : syracuseStep 2265359 = 3398039) B3398039
theorem B3398045 : Blo 2263435 3398045 := bbase (se 3 (by rfl) ⟨637133, by rfl⟩ : syracuseStep 3398045 = 1274267) (by norm_num)
theorem B2265363 : Blo 2263435 2265363 := bstep (se 1 (by rfl) ⟨1699022, by rfl⟩ : syracuseStep 2265363 = 3398045) B3398045
theorem B5097077 : Blo 2263435 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B3398051 : Blo 2263435 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B2265367 : Blo 2263435 2265367 := bstep (se 1 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 2265367 = 3398051) B3398051
theorem B6123413 : Blo 2263435 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B4082275 : Blo 2263435 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B5443033 : Blo 2263435 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B7257377 : Blo 2263435 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B19353005 : Blo 2263435 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B12902003 : Blo 2263435 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B8601335 : Blo 2263435 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B5734223 : Blo 2263435 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B3822815 : Blo 2263435 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B2548543 : Blo 2263435 2548543 := bstep (se 1 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 2548543 = 3822815) B3822815
theorem B3398057 : Blo 2263435 3398057 := bstep (se 2 (by rfl) ⟨1274271, by rfl⟩ : syracuseStep 3398057 = 2548543) B2548543
theorem B2265371 : Blo 2263435 2265371 := bstep (se 1 (by rfl) ⟨1699028, by rfl⟩ : syracuseStep 2265371 = 3398057) B3398057
theorem B8601349 : Blo 2263435 8601349 := bbase (se 4 (by rfl) ⟨806376, by rfl⟩ : syracuseStep 8601349 = 1612753) (by norm_num)
theorem B11468465 : Blo 2263435 11468465 := bstep (se 2 (by rfl) ⟨4300674, by rfl⟩ : syracuseStep 11468465 = 8601349) B8601349
theorem B7645643 : Blo 2263435 7645643 := bstep (se 1 (by rfl) ⟨5734232, by rfl⟩ : syracuseStep 7645643 = 11468465) B11468465
theorem B5097095 : Blo 2263435 5097095 := bstep (se 1 (by rfl) ⟨3822821, by rfl⟩ : syracuseStep 5097095 = 7645643) B7645643
theorem B3398063 : Blo 2263435 3398063 := bstep (se 1 (by rfl) ⟨2548547, by rfl⟩ : syracuseStep 3398063 = 5097095) B5097095
theorem B2265375 : Blo 2263435 2265375 := bstep (se 1 (by rfl) ⟨1699031, by rfl⟩ : syracuseStep 2265375 = 3398063) B3398063
theorem B3398069 : Blo 2263435 3398069 := bbase (se 5 (by rfl) ⟨159284, by rfl⟩ : syracuseStep 3398069 = 318569) (by norm_num)
theorem B2265379 : Blo 2263435 2265379 := bstep (se 1 (by rfl) ⟨1699034, by rfl⟩ : syracuseStep 2265379 = 3398069) B3398069
theorem B5734253 : Blo 2263435 5734253 := bbase (se 3 (by rfl) ⟨1075172, by rfl⟩ : syracuseStep 5734253 = 2150345) (by norm_num)
theorem B3822835 : Blo 2263435 3822835 := bstep (se 1 (by rfl) ⟨2867126, by rfl⟩ : syracuseStep 3822835 = 5734253) B5734253
theorem B5097113 : Blo 2263435 5097113 := bstep (se 2 (by rfl) ⟨1911417, by rfl⟩ : syracuseStep 5097113 = 3822835) B3822835
theorem B3398075 : Blo 2263435 3398075 := bstep (se 1 (by rfl) ⟨2548556, by rfl⟩ : syracuseStep 3398075 = 5097113) B5097113
theorem B2265383 : Blo 2263435 2265383 := bstep (se 1 (by rfl) ⟨1699037, by rfl⟩ : syracuseStep 2265383 = 3398075) B3398075
theorem B2548561 : Blo 2263435 2548561 := bbase (se 2 (by rfl) ⟨955710, by rfl⟩ : syracuseStep 2548561 = 1911421) (by norm_num)
theorem B3398081 : Blo 2263435 3398081 := bstep (se 2 (by rfl) ⟨1274280, by rfl⟩ : syracuseStep 3398081 = 2548561) B2548561
theorem B2265387 : Blo 2263435 2265387 := bstep (se 1 (by rfl) ⟨1699040, by rfl⟩ : syracuseStep 2265387 = 3398081) B3398081
theorem B2721541 : Blo 2263435 2721541 := bbase (se 4 (by rfl) ⟨255144, by rfl⟩ : syracuseStep 2721541 = 510289) (by norm_num)
theorem B3628721 : Blo 2263435 3628721 := bstep (se 2 (by rfl) ⟨1360770, by rfl⟩ : syracuseStep 3628721 = 2721541) B2721541
theorem B2419147 : Blo 2263435 2419147 := bstep (se 1 (by rfl) ⟨1814360, by rfl⟩ : syracuseStep 2419147 = 3628721) B3628721
theorem B3225529 : Blo 2263435 3225529 := bstep (se 2 (by rfl) ⟨1209573, by rfl⟩ : syracuseStep 3225529 = 2419147) B2419147
theorem B4300705 : Blo 2263435 4300705 := bstep (se 2 (by rfl) ⟨1612764, by rfl⟩ : syracuseStep 4300705 = 3225529) B3225529
theorem B5734273 : Blo 2263435 5734273 := bstep (se 2 (by rfl) ⟨2150352, by rfl⟩ : syracuseStep 5734273 = 4300705) B4300705
theorem B7645697 : Blo 2263435 7645697 := bstep (se 2 (by rfl) ⟨2867136, by rfl⟩ : syracuseStep 7645697 = 5734273) B5734273
theorem B5097131 : Blo 2263435 5097131 := bstep (se 1 (by rfl) ⟨3822848, by rfl⟩ : syracuseStep 5097131 = 7645697) B7645697
theorem B3398087 : Blo 2263435 3398087 := bstep (se 1 (by rfl) ⟨2548565, by rfl⟩ : syracuseStep 3398087 = 5097131) B5097131
theorem B2265391 : Blo 2263435 2265391 := bstep (se 1 (by rfl) ⟨1699043, by rfl⟩ : syracuseStep 2265391 = 3398087) B3398087
theorem B3398093 : Blo 2263435 3398093 := bbase (se 3 (by rfl) ⟨637142, by rfl⟩ : syracuseStep 3398093 = 1274285) (by norm_num)
theorem B2265395 : Blo 2263435 2265395 := bstep (se 1 (by rfl) ⟨1699046, by rfl⟩ : syracuseStep 2265395 = 3398093) B3398093
theorem B5097149 : Blo 2263435 5097149 := bbase (se 3 (by rfl) ⟨955715, by rfl⟩ : syracuseStep 5097149 = 1911431) (by norm_num)
theorem B3398099 : Blo 2263435 3398099 := bstep (se 1 (by rfl) ⟨2548574, by rfl⟩ : syracuseStep 3398099 = 5097149) B5097149
theorem B2265399 : Blo 2263435 2265399 := bstep (se 1 (by rfl) ⟨1699049, by rfl⟩ : syracuseStep 2265399 = 3398099) B3398099
theorem B3822869 : Blo 2263435 3822869 := bbase (se 6 (by rfl) ⟨89598, by rfl⟩ : syracuseStep 3822869 = 179197) (by norm_num)
theorem B2548579 : Blo 2263435 2548579 := bstep (se 1 (by rfl) ⟨1911434, by rfl⟩ : syracuseStep 2548579 = 3822869) B3822869
theorem B3398105 : Blo 2263435 3398105 := bstep (se 2 (by rfl) ⟨1274289, by rfl⟩ : syracuseStep 3398105 = 2548579) B2548579
theorem B2265403 : Blo 2263435 2265403 := bstep (se 1 (by rfl) ⟨1699052, by rfl⟩ : syracuseStep 2265403 = 3398105) B3398105
theorem B4138037 : Blo 2263435 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B2758691 : Blo 2263435 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B7356509 : Blo 2263435 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B4904339 : Blo 2263435 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B52312949 : Blo 2263435 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B34875299 : Blo 2263435 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B23250199 : Blo 2263435 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B31000265 : Blo 2263435 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B20666843 : Blo 2263435 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B13777895 : Blo 2263435 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B36741053 : Blo 2263435 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B24494035 : Blo 2263435 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B32658713 : Blo 2263435 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B21772475 : Blo 2263435 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B14514983 : Blo 2263435 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B9676655 : Blo 2263435 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B6451103 : Blo 2263435 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B17202941 : Blo 2263435 17202941 := bstep (se 3 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 17202941 = 6451103) B6451103
theorem B11468627 : Blo 2263435 11468627 := bstep (se 1 (by rfl) ⟨8601470, by rfl⟩ : syracuseStep 11468627 = 17202941) B17202941
theorem B7645751 : Blo 2263435 7645751 := bstep (se 1 (by rfl) ⟨5734313, by rfl⟩ : syracuseStep 7645751 = 11468627) B11468627
theorem B5097167 : Blo 2263435 5097167 := bstep (se 1 (by rfl) ⟨3822875, by rfl⟩ : syracuseStep 5097167 = 7645751) B7645751
theorem B3398111 : Blo 2263435 3398111 := bstep (se 1 (by rfl) ⟨2548583, by rfl⟩ : syracuseStep 3398111 = 5097167) B5097167
theorem B2265407 : Blo 2263435 2265407 := bstep (se 1 (by rfl) ⟨1699055, by rfl⟩ : syracuseStep 2265407 = 3398111) B3398111
theorem B3398117 : Blo 2263435 3398117 := bbase (se 4 (by rfl) ⟨318573, by rfl⟩ : syracuseStep 3398117 = 637147) (by norm_num)
theorem B2265411 : Blo 2263435 2265411 := bstep (se 1 (by rfl) ⟨1699058, by rfl⟩ : syracuseStep 2265411 = 3398117) B3398117
theorem B8164709 : Blo 2263435 8164709 := bbase (se 4 (by rfl) ⟨765441, by rfl⟩ : syracuseStep 8164709 = 1530883) (by norm_num)
theorem B5443139 : Blo 2263435 5443139 := bstep (se 1 (by rfl) ⟨4082354, by rfl⟩ : syracuseStep 5443139 = 8164709) B8164709
theorem B14515037 : Blo 2263435 14515037 := bstep (se 3 (by rfl) ⟨2721569, by rfl⟩ : syracuseStep 14515037 = 5443139) B5443139
theorem B9676691 : Blo 2263435 9676691 := bstep (se 1 (by rfl) ⟨7257518, by rfl⟩ : syracuseStep 9676691 = 14515037) B14515037
theorem B6451127 : Blo 2263435 6451127 := bstep (se 1 (by rfl) ⟨4838345, by rfl⟩ : syracuseStep 6451127 = 9676691) B9676691
theorem B4300751 : Blo 2263435 4300751 := bstep (se 1 (by rfl) ⟨3225563, by rfl⟩ : syracuseStep 4300751 = 6451127) B6451127
theorem B2867167 : Blo 2263435 2867167 := bstep (se 1 (by rfl) ⟨2150375, by rfl⟩ : syracuseStep 2867167 = 4300751) B4300751
theorem B3822889 : Blo 2263435 3822889 := bstep (se 2 (by rfl) ⟨1433583, by rfl⟩ : syracuseStep 3822889 = 2867167) B2867167
theorem B5097185 : Blo 2263435 5097185 := bstep (se 2 (by rfl) ⟨1911444, by rfl⟩ : syracuseStep 5097185 = 3822889) B3822889
theorem B3398123 : Blo 2263435 3398123 := bstep (se 1 (by rfl) ⟨2548592, by rfl⟩ : syracuseStep 3398123 = 5097185) B5097185
theorem B2265415 : Blo 2263435 2265415 := bstep (se 1 (by rfl) ⟨1699061, by rfl⟩ : syracuseStep 2265415 = 3398123) B3398123
theorem B2548597 : Blo 2263435 2548597 := bbase (se 5 (by rfl) ⟨119465, by rfl⟩ : syracuseStep 2548597 = 238931) (by norm_num)
theorem B3398129 : Blo 2263435 3398129 := bstep (se 2 (by rfl) ⟨1274298, by rfl⟩ : syracuseStep 3398129 = 2548597) B2548597
theorem B2265419 : Blo 2263435 2265419 := bstep (se 1 (by rfl) ⟨1699064, by rfl⟩ : syracuseStep 2265419 = 3398129) B3398129
theorem B2867177 : Blo 2263435 2867177 := bbase (se 2 (by rfl) ⟨1075191, by rfl⟩ : syracuseStep 2867177 = 2150383) (by norm_num)
theorem B7645805 : Blo 2263435 7645805 := bstep (se 3 (by rfl) ⟨1433588, by rfl⟩ : syracuseStep 7645805 = 2867177) B2867177
theorem B5097203 : Blo 2263435 5097203 := bstep (se 1 (by rfl) ⟨3822902, by rfl⟩ : syracuseStep 5097203 = 7645805) B7645805
theorem B3398135 : Blo 2263435 3398135 := bstep (se 1 (by rfl) ⟨2548601, by rfl⟩ : syracuseStep 3398135 = 5097203) B5097203
theorem B2265423 : Blo 2263435 2265423 := bstep (se 1 (by rfl) ⟨1699067, by rfl⟩ : syracuseStep 2265423 = 3398135) B3398135
theorem B3398141 : Blo 2263435 3398141 := bbase (se 3 (by rfl) ⟨637151, by rfl⟩ : syracuseStep 3398141 = 1274303) (by norm_num)
theorem B2265427 : Blo 2263435 2265427 := bstep (se 1 (by rfl) ⟨1699070, by rfl⟩ : syracuseStep 2265427 = 3398141) B3398141
theorem B5097221 : Blo 2263435 5097221 := bbase (se 4 (by rfl) ⟨477864, by rfl⟩ : syracuseStep 5097221 = 955729) (by norm_num)
theorem B3398147 : Blo 2263435 3398147 := bstep (se 1 (by rfl) ⟨2548610, by rfl⟩ : syracuseStep 3398147 = 5097221) B5097221
theorem B2265431 : Blo 2263435 2265431 := bstep (se 1 (by rfl) ⟨1699073, by rfl⟩ : syracuseStep 2265431 = 3398147) B3398147
theorem B4300789 : Blo 2263435 4300789 := bbase (se 5 (by rfl) ⟨201599, by rfl⟩ : syracuseStep 4300789 = 403199) (by norm_num)
theorem B5734385 : Blo 2263435 5734385 := bstep (se 2 (by rfl) ⟨2150394, by rfl⟩ : syracuseStep 5734385 = 4300789) B4300789
theorem B3822923 : Blo 2263435 3822923 := bstep (se 1 (by rfl) ⟨2867192, by rfl⟩ : syracuseStep 3822923 = 5734385) B5734385
theorem B2548615 : Blo 2263435 2548615 := bstep (se 1 (by rfl) ⟨1911461, by rfl⟩ : syracuseStep 2548615 = 3822923) B3822923
theorem B3398153 : Blo 2263435 3398153 := bstep (se 2 (by rfl) ⟨1274307, by rfl⟩ : syracuseStep 3398153 = 2548615) B2548615
theorem B2265435 : Blo 2263435 2265435 := bstep (se 1 (by rfl) ⟨1699076, by rfl⟩ : syracuseStep 2265435 = 3398153) B3398153
theorem C0 (j : ℕ) (h1 : 565858 ≤ j) (h2 : j ≤ 566358) : Blo 2263435 (4 * j + 3) := by
  interval_cases j
  · exact B2263435
  · exact B2263439
  · exact B2263443
  · exact B2263447
  · exact B2263451
  · exact B2263455
  · exact B2263459
  · exact B2263463
  · exact B2263467
  · exact B2263471
  · exact B2263475
  · exact B2263479
  · exact B2263483
  · exact B2263487
  · exact B2263491
  · exact B2263495
  · exact B2263499
  · exact B2263503
  · exact B2263507
  · exact B2263511
  · exact B2263515
  · exact B2263519
  · exact B2263523
  · exact B2263527
  · exact B2263531
  · exact B2263535
  · exact B2263539
  · exact B2263543
  · exact B2263547
  · exact B2263551
  · exact B2263555
  · exact B2263559
  · exact B2263563
  · exact B2263567
  · exact B2263571
  · exact B2263575
  · exact B2263579
  · exact B2263583
  · exact B2263587
  · exact B2263591
  · exact B2263595
  · exact B2263599
  · exact B2263603
  · exact B2263607
  · exact B2263611
  · exact B2263615
  · exact B2263619
  · exact B2263623
  · exact B2263627
  · exact B2263631
  · exact B2263635
  · exact B2263639
  · exact B2263643
  · exact B2263647
  · exact B2263651
  · exact B2263655
  · exact B2263659
  · exact B2263663
  · exact B2263667
  · exact B2263671
  · exact B2263675
  · exact B2263679
  · exact B2263683
  · exact B2263687
  · exact B2263691
  · exact B2263695
  · exact B2263699
  · exact B2263703
  · exact B2263707
  · exact B2263711
  · exact B2263715
  · exact B2263719
  · exact B2263723
  · exact B2263727
  · exact B2263731
  · exact B2263735
  · exact B2263739
  · exact B2263743
  · exact B2263747
  · exact B2263751
  · exact B2263755
  · exact B2263759
  · exact B2263763
  · exact B2263767
  · exact B2263771
  · exact B2263775
  · exact B2263779
  · exact B2263783
  · exact B2263787
  · exact B2263791
  · exact B2263795
  · exact B2263799
  · exact B2263803
  · exact B2263807
  · exact B2263811
  · exact B2263815
  · exact B2263819
  · exact B2263823
  · exact B2263827
  · exact B2263831
  · exact B2263835
  · exact B2263839
  · exact B2263843
  · exact B2263847
  · exact B2263851
  · exact B2263855
  · exact B2263859
  · exact B2263863
  · exact B2263867
  · exact B2263871
  · exact B2263875
  · exact B2263879
  · exact B2263883
  · exact B2263887
  · exact B2263891
  · exact B2263895
  · exact B2263899
  · exact B2263903
  · exact B2263907
  · exact B2263911
  · exact B2263915
  · exact B2263919
  · exact B2263923
  · exact B2263927
  · exact B2263931
  · exact B2263935
  · exact B2263939
  · exact B2263943
  · exact B2263947
  · exact B2263951
  · exact B2263955
  · exact B2263959
  · exact B2263963
  · exact B2263967
  · exact B2263971
  · exact B2263975
  · exact B2263979
  · exact B2263983
  · exact B2263987
  · exact B2263991
  · exact B2263995
  · exact B2263999
  · exact B2264003
  · exact B2264007
  · exact B2264011
  · exact B2264015
  · exact B2264019
  · exact B2264023
  · exact B2264027
  · exact B2264031
  · exact B2264035
  · exact B2264039
  · exact B2264043
  · exact B2264047
  · exact B2264051
  · exact B2264055
  · exact B2264059
  · exact B2264063
  · exact B2264067
  · exact B2264071
  · exact B2264075
  · exact B2264079
  · exact B2264083
  · exact B2264087
  · exact B2264091
  · exact B2264095
  · exact B2264099
  · exact B2264103
  · exact B2264107
  · exact B2264111
  · exact B2264115
  · exact B2264119
  · exact B2264123
  · exact B2264127
  · exact B2264131
  · exact B2264135
  · exact B2264139
  · exact B2264143
  · exact B2264147
  · exact B2264151
  · exact B2264155
  · exact B2264159
  · exact B2264163
  · exact B2264167
  · exact B2264171
  · exact B2264175
  · exact B2264179
  · exact B2264183
  · exact B2264187
  · exact B2264191
  · exact B2264195
  · exact B2264199
  · exact B2264203
  · exact B2264207
  · exact B2264211
  · exact B2264215
  · exact B2264219
  · exact B2264223
  · exact B2264227
  · exact B2264231
  · exact B2264235
  · exact B2264239
  · exact B2264243
  · exact B2264247
  · exact B2264251
  · exact B2264255
  · exact B2264259
  · exact B2264263
  · exact B2264267
  · exact B2264271
  · exact B2264275
  · exact B2264279
  · exact B2264283
  · exact B2264287
  · exact B2264291
  · exact B2264295
  · exact B2264299
  · exact B2264303
  · exact B2264307
  · exact B2264311
  · exact B2264315
  · exact B2264319
  · exact B2264323
  · exact B2264327
  · exact B2264331
  · exact B2264335
  · exact B2264339
  · exact B2264343
  · exact B2264347
  · exact B2264351
  · exact B2264355
  · exact B2264359
  · exact B2264363
  · exact B2264367
  · exact B2264371
  · exact B2264375
  · exact B2264379
  · exact B2264383
  · exact B2264387
  · exact B2264391
  · exact B2264395
  · exact B2264399
  · exact B2264403
  · exact B2264407
  · exact B2264411
  · exact B2264415
  · exact B2264419
  · exact B2264423
  · exact B2264427
  · exact B2264431
  · exact B2264435
  · exact B2264439
  · exact B2264443
  · exact B2264447
  · exact B2264451
  · exact B2264455
  · exact B2264459
  · exact B2264463
  · exact B2264467
  · exact B2264471
  · exact B2264475
  · exact B2264479
  · exact B2264483
  · exact B2264487
  · exact B2264491
  · exact B2264495
  · exact B2264499
  · exact B2264503
  · exact B2264507
  · exact B2264511
  · exact B2264515
  · exact B2264519
  · exact B2264523
  · exact B2264527
  · exact B2264531
  · exact B2264535
  · exact B2264539
  · exact B2264543
  · exact B2264547
  · exact B2264551
  · exact B2264555
  · exact B2264559
  · exact B2264563
  · exact B2264567
  · exact B2264571
  · exact B2264575
  · exact B2264579
  · exact B2264583
  · exact B2264587
  · exact B2264591
  · exact B2264595
  · exact B2264599
  · exact B2264603
  · exact B2264607
  · exact B2264611
  · exact B2264615
  · exact B2264619
  · exact B2264623
  · exact B2264627
  · exact B2264631
  · exact B2264635
  · exact B2264639
  · exact B2264643
  · exact B2264647
  · exact B2264651
  · exact B2264655
  · exact B2264659
  · exact B2264663
  · exact B2264667
  · exact B2264671
  · exact B2264675
  · exact B2264679
  · exact B2264683
  · exact B2264687
  · exact B2264691
  · exact B2264695
  · exact B2264699
  · exact B2264703
  · exact B2264707
  · exact B2264711
  · exact B2264715
  · exact B2264719
  · exact B2264723
  · exact B2264727
  · exact B2264731
  · exact B2264735
  · exact B2264739
  · exact B2264743
  · exact B2264747
  · exact B2264751
  · exact B2264755
  · exact B2264759
  · exact B2264763
  · exact B2264767
  · exact B2264771
  · exact B2264775
  · exact B2264779
  · exact B2264783
  · exact B2264787
  · exact B2264791
  · exact B2264795
  · exact B2264799
  · exact B2264803
  · exact B2264807
  · exact B2264811
  · exact B2264815
  · exact B2264819
  · exact B2264823
  · exact B2264827
  · exact B2264831
  · exact B2264835
  · exact B2264839
  · exact B2264843
  · exact B2264847
  · exact B2264851
  · exact B2264855
  · exact B2264859
  · exact B2264863
  · exact B2264867
  · exact B2264871
  · exact B2264875
  · exact B2264879
  · exact B2264883
  · exact B2264887
  · exact B2264891
  · exact B2264895
  · exact B2264899
  · exact B2264903
  · exact B2264907
  · exact B2264911
  · exact B2264915
  · exact B2264919
  · exact B2264923
  · exact B2264927
  · exact B2264931
  · exact B2264935
  · exact B2264939
  · exact B2264943
  · exact B2264947
  · exact B2264951
  · exact B2264955
  · exact B2264959
  · exact B2264963
  · exact B2264967
  · exact B2264971
  · exact B2264975
  · exact B2264979
  · exact B2264983
  · exact B2264987
  · exact B2264991
  · exact B2264995
  · exact B2264999
  · exact B2265003
  · exact B2265007
  · exact B2265011
  · exact B2265015
  · exact B2265019
  · exact B2265023
  · exact B2265027
  · exact B2265031
  · exact B2265035
  · exact B2265039
  · exact B2265043
  · exact B2265047
  · exact B2265051
  · exact B2265055
  · exact B2265059
  · exact B2265063
  · exact B2265067
  · exact B2265071
  · exact B2265075
  · exact B2265079
  · exact B2265083
  · exact B2265087
  · exact B2265091
  · exact B2265095
  · exact B2265099
  · exact B2265103
  · exact B2265107
  · exact B2265111
  · exact B2265115
  · exact B2265119
  · exact B2265123
  · exact B2265127
  · exact B2265131
  · exact B2265135
  · exact B2265139
  · exact B2265143
  · exact B2265147
  · exact B2265151
  · exact B2265155
  · exact B2265159
  · exact B2265163
  · exact B2265167
  · exact B2265171
  · exact B2265175
  · exact B2265179
  · exact B2265183
  · exact B2265187
  · exact B2265191
  · exact B2265195
  · exact B2265199
  · exact B2265203
  · exact B2265207
  · exact B2265211
  · exact B2265215
  · exact B2265219
  · exact B2265223
  · exact B2265227
  · exact B2265231
  · exact B2265235
  · exact B2265239
  · exact B2265243
  · exact B2265247
  · exact B2265251
  · exact B2265255
  · exact B2265259
  · exact B2265263
  · exact B2265267
  · exact B2265271
  · exact B2265275
  · exact B2265279
  · exact B2265283
  · exact B2265287
  · exact B2265291
  · exact B2265295
  · exact B2265299
  · exact B2265303
  · exact B2265307
  · exact B2265311
  · exact B2265315
  · exact B2265319
  · exact B2265323
  · exact B2265327
  · exact B2265331
  · exact B2265335
  · exact B2265339
  · exact B2265343
  · exact B2265347
  · exact B2265351
  · exact B2265355
  · exact B2265359
  · exact B2265363
  · exact B2265367
  · exact B2265371
  · exact B2265375
  · exact B2265379
  · exact B2265383
  · exact B2265387
  · exact B2265391
  · exact B2265395
  · exact B2265399
  · exact B2265403
  · exact B2265407
  · exact B2265411
  · exact B2265415
  · exact B2265419
  · exact B2265423
  · exact B2265427
  · exact B2265431
  · exact B2265435
theorem solution (m : ℕ) (hlo : 2263435 ≤ m) (hhi : m ≤ 2265435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 565858 ≤ j := by omega
    have hj2 : j ≤ 566358 := by omega
    have hb : Blo 2263435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
