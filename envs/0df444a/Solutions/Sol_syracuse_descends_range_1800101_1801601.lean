-- Prove2me | solution 1 for syracuse_descends_range_1800101_1801601
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:50:13.304188+00:00
-- url     : https://prove2.me/submissions/ac45af3e-9d11-4588-9bea-00dd73beb378

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


theorem B2883605 : Blo 1800101 2883605 := bbase (se 6 (by rfl) ⟨67584, by rfl⟩ : syracuseStep 2883605 = 135169) (by norm_num)
theorem B2883637 : Blo 1800101 2883637 := bbase (se 5 (by rfl) ⟨135170, by rfl⟩ : syracuseStep 2883637 = 270341) (by norm_num)
theorem B6840389 : Blo 1800101 6840389 := bbase (se 4 (by rfl) ⟨641286, by rfl⟩ : syracuseStep 6840389 = 1282573) (by norm_num)
theorem B3039349 : Blo 1800101 3039349 := bbase (se 5 (by rfl) ⟨142469, by rfl⟩ : syracuseStep 3039349 = 284939) (by norm_num)
theorem B15384725 : Blo 1800101 15384725 := bbase (se 6 (by rfl) ⟨360579, by rfl⟩ : syracuseStep 15384725 = 721159) (by norm_num)
theorem B9117845 : Blo 1800101 9117845 := bbase (se 6 (by rfl) ⟨213699, by rfl⟩ : syracuseStep 9117845 = 427399) (by norm_num)
theorem B3039437 : Blo 1800101 3039437 := bbase (se 3 (by rfl) ⟨569894, by rfl⟩ : syracuseStep 3039437 = 1139789) (by norm_num)
theorem B6078725 : Blo 1800101 6078725 := bbase (se 4 (by rfl) ⟨569880, by rfl⟩ : syracuseStep 6078725 = 1139761) (by norm_num)
theorem B2564389 : Blo 1800101 2564389 := bbase (se 4 (by rfl) ⟨240411, by rfl⟩ : syracuseStep 2564389 = 480823) (by norm_num)
theorem B3039565 : Blo 1800101 3039565 := bbase (se 3 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 3039565 = 1139837) (by norm_num)
theorem B4620653 : Blo 1800101 4620653 := bbase (se 3 (by rfl) ⟨866372, by rfl⟩ : syracuseStep 4620653 = 1732745) (by norm_num)
theorem B3039653 : Blo 1800101 3039653 := bbase (se 4 (by rfl) ⟨284967, by rfl⟩ : syracuseStep 3039653 = 569935) (by norm_num)
theorem B3039781 : Blo 1800101 3039781 := bbase (se 4 (by rfl) ⟨284979, by rfl⟩ : syracuseStep 3039781 = 569959) (by norm_num)
theorem B6242933 : Blo 1800101 6242933 := bbase (se 5 (by rfl) ⟨292637, by rfl⟩ : syracuseStep 6242933 = 585275) (by norm_num)
theorem B2564725 : Blo 1800101 2564725 := bbase (se 5 (by rfl) ⟨120221, by rfl⟩ : syracuseStep 2564725 = 240443) (by norm_num)
theorem B3039869 : Blo 1800101 3039869 := bbase (se 3 (by rfl) ⟨569975, by rfl⟩ : syracuseStep 3039869 = 1139951) (by norm_num)
theorem B6079157 : Blo 1800101 6079157 := bbase (se 5 (by rfl) ⟨284960, by rfl⟩ : syracuseStep 6079157 = 569921) (by norm_num)
theorem B3039997 : Blo 1800101 3039997 := bbase (se 3 (by rfl) ⟨569999, by rfl⟩ : syracuseStep 3039997 = 1139999) (by norm_num)
theorem B4326205 : Blo 1800101 4326205 := bbase (se 3 (by rfl) ⟨811163, by rfl⟩ : syracuseStep 4326205 = 1622327) (by norm_num)
theorem B2564941 : Blo 1800101 2564941 := bbase (se 3 (by rfl) ⟨480926, by rfl⟩ : syracuseStep 2564941 = 961853) (by norm_num)
theorem B3040085 : Blo 1800101 3040085 := bbase (se 9 (by rfl) ⟨8906, by rfl⟩ : syracuseStep 3040085 = 17813) (by norm_num)
theorem B3900253 : Blo 1800101 3900253 := bbase (se 3 (by rfl) ⟨731297, by rfl⟩ : syracuseStep 3900253 = 1462595) (by norm_num)
theorem B14599061 : Blo 1800101 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B2278297 : Blo 1800101 2278297 := bbase (se 2 (by rfl) ⟨854361, by rfl⟩ : syracuseStep 2278297 = 1708723) (by norm_num)
theorem B11535317 : Blo 1800101 11535317 := bbase (se 7 (by rfl) ⟨135179, by rfl⟩ : syracuseStep 11535317 = 270359) (by norm_num)
theorem B2278469 : Blo 1800101 2278469 := bbase (se 4 (by rfl) ⟨213606, by rfl⟩ : syracuseStep 2278469 = 427213) (by norm_num)
theorem B7300165 : Blo 1800101 7300165 := bbase (se 4 (by rfl) ⟨684390, by rfl⟩ : syracuseStep 7300165 = 1368781) (by norm_num)
theorem B6079589 : Blo 1800101 6079589 := bbase (se 4 (by rfl) ⟨569961, by rfl⟩ : syracuseStep 6079589 = 1139923) (by norm_num)
theorem B8651893 : Blo 1800101 8651893 := bbase (se 5 (by rfl) ⟨405557, by rfl⟩ : syracuseStep 8651893 = 811115) (by norm_num)
theorem B2278525 : Blo 1800101 2278525 := bbase (se 3 (by rfl) ⟨427223, by rfl⟩ : syracuseStep 2278525 = 854447) (by norm_num)
theorem B8651909 : Blo 1800101 8651909 := bbase (se 4 (by rfl) ⟨811116, by rfl⟩ : syracuseStep 8651909 = 1622233) (by norm_num)
theorem B5129381 : Blo 1800101 5129381 := bbase (se 4 (by rfl) ⟨480879, by rfl⟩ : syracuseStep 5129381 = 961759) (by norm_num)
theorem B2163881 : Blo 1800101 2163881 := bbase (se 2 (by rfl) ⟨811455, by rfl⟩ : syracuseStep 2163881 = 1622911) (by norm_num)
theorem B7300309 : Blo 1800101 7300309 := bbase (se 7 (by rfl) ⟨85550, by rfl⟩ : syracuseStep 7300309 = 171101) (by norm_num)
theorem B2278621 : Blo 1800101 2278621 := bbase (se 3 (by rfl) ⟨427241, by rfl⟩ : syracuseStep 2278621 = 854483) (by norm_num)
theorem B3417461 : Blo 1800101 3417461 := bbase (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) (by norm_num)
theorem B2278793 : Blo 1800101 2278793 := bbase (se 2 (by rfl) ⟨854547, by rfl⟩ : syracuseStep 2278793 = 1709095) (by norm_num)
theorem B4326821 : Blo 1800101 4326821 := bbase (se 4 (by rfl) ⟨405639, by rfl⟩ : syracuseStep 4326821 = 811279) (by norm_num)
theorem B9119141 : Blo 1800101 9119141 := bbase (se 4 (by rfl) ⟨854919, by rfl⟩ : syracuseStep 9119141 = 1709839) (by norm_num)
theorem B2278849 : Blo 1800101 2278849 := bbase (se 2 (by rfl) ⟨854568, by rfl⟩ : syracuseStep 2278849 = 1709137) (by norm_num)
theorem B4326877 : Blo 1800101 4326877 := bbase (se 3 (by rfl) ⟨811289, by rfl⟩ : syracuseStep 4326877 = 1622579) (by norm_num)
theorem B10257941 : Blo 1800101 10257941 := bbase (se 6 (by rfl) ⟨240420, by rfl⟩ : syracuseStep 10257941 = 480841) (by norm_num)
theorem B6080021 : Blo 1800101 6080021 := bbase (se 6 (by rfl) ⟨142500, by rfl⟩ : syracuseStep 6080021 = 285001) (by norm_num)
theorem B2885149 : Blo 1800101 2885149 := bbase (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) (by norm_num)
theorem B2278945 : Blo 1800101 2278945 := bbase (se 2 (by rfl) ⟨854604, by rfl⟩ : syracuseStep 2278945 = 1709209) (by norm_num)
theorem B12977749 : Blo 1800101 12977749 := bbase (se 8 (by rfl) ⟨76041, by rfl⟩ : syracuseStep 12977749 = 152083) (by norm_num)
theorem B2737757 : Blo 1800101 2737757 := bbase (se 3 (by rfl) ⟨513329, by rfl⟩ : syracuseStep 2737757 = 1026659) (by norm_num)
theorem B2025121 : Blo 1800101 2025121 := bbase (se 2 (by rfl) ⟨759420, by rfl⟩ : syracuseStep 2025121 = 1518841) (by norm_num)
theorem B2025157 : Blo 1800101 2025157 := bbase (se 4 (by rfl) ⟨189858, by rfl⟩ : syracuseStep 2025157 = 379717) (by norm_num)
theorem B2279117 : Blo 1800101 2279117 := bbase (se 3 (by rfl) ⟨427334, by rfl⟩ : syracuseStep 2279117 = 854669) (by norm_num)
theorem B2025193 : Blo 1800101 2025193 := bbase (se 2 (by rfl) ⟨759447, by rfl⟩ : syracuseStep 2025193 = 1518895) (by norm_num)
theorem B4556533 : Blo 1800101 4556533 := bbase (se 5 (by rfl) ⟨213587, by rfl⟩ : syracuseStep 4556533 = 427175) (by norm_num)
theorem B2279173 : Blo 1800101 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B2025229 : Blo 1800101 2025229 := bbase (se 3 (by rfl) ⟨379730, by rfl⟩ : syracuseStep 2025229 = 759461) (by norm_num)
theorem B3245845 : Blo 1800101 3245845 := bbase (se 6 (by rfl) ⟨76074, by rfl⟩ : syracuseStep 3245845 = 152149) (by norm_num)
theorem B2025265 : Blo 1800101 2025265 := bbase (se 2 (by rfl) ⟨759474, by rfl⟩ : syracuseStep 2025265 = 1518949) (by norm_num)
theorem B2025301 : Blo 1800101 2025301 := bbase (se 9 (by rfl) ⟨5933, by rfl⟩ : syracuseStep 2025301 = 11867) (by norm_num)
theorem B4556645 : Blo 1800101 4556645 := bbase (se 4 (by rfl) ⟨427185, by rfl⟩ : syracuseStep 4556645 = 854371) (by norm_num)
theorem B2279269 : Blo 1800101 2279269 := bbase (se 4 (by rfl) ⟨213681, by rfl⟩ : syracuseStep 2279269 = 427363) (by norm_num)
theorem B2025337 : Blo 1800101 2025337 := bbase (se 2 (by rfl) ⟨759501, by rfl⟩ : syracuseStep 2025337 = 1519003) (by norm_num)
theorem B2598781 : Blo 1800101 2598781 := bbase (se 3 (by rfl) ⟨487271, by rfl⟩ : syracuseStep 2598781 = 974543) (by norm_num)
theorem B2025373 : Blo 1800101 2025373 := bbase (se 3 (by rfl) ⟨379757, by rfl⟩ : syracuseStep 2025373 = 759515) (by norm_num)
theorem B7694261 : Blo 1800101 7694261 := bbase (se 5 (by rfl) ⟨360668, by rfl⟩ : syracuseStep 7694261 = 721337) (by norm_num)
theorem B2025409 : Blo 1800101 2025409 := bbase (se 2 (by rfl) ⟨759528, by rfl⟩ : syracuseStep 2025409 = 1519057) (by norm_num)
theorem B2025445 : Blo 1800101 2025445 := bbase (se 4 (by rfl) ⟨189885, by rfl⟩ : syracuseStep 2025445 = 379771) (by norm_num)
theorem B2025481 : Blo 1800101 2025481 := bbase (se 2 (by rfl) ⟨759555, by rfl⟩ : syracuseStep 2025481 = 1519111) (by norm_num)
theorem B2279441 : Blo 1800101 2279441 := bbase (se 2 (by rfl) ⟨854790, by rfl⟩ : syracuseStep 2279441 = 1709581) (by norm_num)
theorem B4556837 : Blo 1800101 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B2025517 : Blo 1800101 2025517 := bbase (se 3 (by rfl) ⟨379784, by rfl⟩ : syracuseStep 2025517 = 759569) (by norm_num)
theorem B2279497 : Blo 1800101 2279497 := bbase (se 2 (by rfl) ⟨854811, by rfl⟩ : syracuseStep 2279497 = 1709623) (by norm_num)
theorem B2025553 : Blo 1800101 2025553 := bbase (se 2 (by rfl) ⟨759582, by rfl⟩ : syracuseStep 2025553 = 1519165) (by norm_num)
theorem B13674581 : Blo 1800101 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B3418213 : Blo 1800101 3418213 := bbase (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) (by norm_num)
theorem B2025589 : Blo 1800101 2025589 := bbase (se 5 (by rfl) ⟨94949, by rfl⟩ : syracuseStep 2025589 = 189899) (by norm_num)
theorem B9242741 : Blo 1800101 9242741 := bbase (se 5 (by rfl) ⟨433253, by rfl⟩ : syracuseStep 9242741 = 866507) (by norm_num)
theorem B4384901 : Blo 1800101 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B2025625 : Blo 1800101 2025625 := bbase (se 2 (by rfl) ⟨759609, by rfl⟩ : syracuseStep 2025625 = 1519219) (by norm_num)
theorem B7301285 : Blo 1800101 7301285 := bbase (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) (by norm_num)
theorem B2279593 : Blo 1800101 2279593 := bbase (se 2 (by rfl) ⟨854847, by rfl⟩ : syracuseStep 2279593 = 1709695) (by norm_num)
theorem B2025661 : Blo 1800101 2025661 := bbase (se 3 (by rfl) ⟨379811, by rfl⟩ : syracuseStep 2025661 = 759623) (by norm_num)
theorem B2025697 : Blo 1800101 2025697 := bbase (se 2 (by rfl) ⟨759636, by rfl⟩ : syracuseStep 2025697 = 1519273) (by norm_num)
theorem B3418357 : Blo 1800101 3418357 := bbase (se 5 (by rfl) ⟨160235, by rfl⟩ : syracuseStep 3418357 = 320471) (by norm_num)
theorem B2025733 : Blo 1800101 2025733 := bbase (se 4 (by rfl) ⟨189912, by rfl⟩ : syracuseStep 2025733 = 379825) (by norm_num)
theorem B2025769 : Blo 1800101 2025769 := bbase (se 2 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 2025769 = 1519327) (by norm_num)
theorem B2025805 : Blo 1800101 2025805 := bbase (se 3 (by rfl) ⟨379838, by rfl⟩ : syracuseStep 2025805 = 759677) (by norm_num)
theorem B2279765 : Blo 1800101 2279765 := bbase (se 10 (by rfl) ⟨3339, by rfl⟩ : syracuseStep 2279765 = 6679) (by norm_num)
theorem B2025841 : Blo 1800101 2025841 := bbase (se 2 (by rfl) ⟨759690, by rfl⟩ : syracuseStep 2025841 = 1519381) (by norm_num)
theorem B4557181 : Blo 1800101 4557181 := bbase (se 3 (by rfl) ⟨854471, by rfl⟩ : syracuseStep 4557181 = 1708943) (by norm_num)
theorem B2279821 : Blo 1800101 2279821 := bbase (se 3 (by rfl) ⟨427466, by rfl⟩ : syracuseStep 2279821 = 854933) (by norm_num)
theorem B3418517 : Blo 1800101 3418517 := bbase (se 6 (by rfl) ⟨80121, by rfl⟩ : syracuseStep 3418517 = 160243) (by norm_num)
theorem B2025877 : Blo 1800101 2025877 := bbase (se 6 (by rfl) ⟨47481, by rfl⟩ : syracuseStep 2025877 = 94963) (by norm_num)
theorem B2025913 : Blo 1800101 2025913 := bbase (se 2 (by rfl) ⟨759717, by rfl⟩ : syracuseStep 2025913 = 1519435) (by norm_num)
theorem B4327877 : Blo 1800101 4327877 := bbase (se 4 (by rfl) ⟨405738, by rfl⟩ : syracuseStep 4327877 = 811477) (by norm_num)
theorem B2025949 : Blo 1800101 2025949 := bbase (se 3 (by rfl) ⟨379865, by rfl⟩ : syracuseStep 2025949 = 759731) (by norm_num)
theorem B4557293 : Blo 1800101 4557293 := bbase (se 3 (by rfl) ⟨854492, by rfl⟩ : syracuseStep 4557293 = 1708985) (by norm_num)
theorem B2279917 : Blo 1800101 2279917 := bbase (se 3 (by rfl) ⟨427484, by rfl⟩ : syracuseStep 2279917 = 854969) (by norm_num)
theorem B2025985 : Blo 1800101 2025985 := bbase (se 2 (by rfl) ⟨759744, by rfl⟩ : syracuseStep 2025985 = 1519489) (by norm_num)
theorem B3418661 : Blo 1800101 3418661 := bbase (se 4 (by rfl) ⟨320499, by rfl⟩ : syracuseStep 3418661 = 640999) (by norm_num)
theorem B2026021 : Blo 1800101 2026021 := bbase (se 4 (by rfl) ⟨189939, by rfl⟩ : syracuseStep 2026021 = 379879) (by norm_num)
theorem B2026057 : Blo 1800101 2026057 := bbase (se 2 (by rfl) ⟨759771, by rfl⟩ : syracuseStep 2026057 = 1519543) (by norm_num)
theorem B2026093 : Blo 1800101 2026093 := bbase (se 3 (by rfl) ⟨379892, by rfl⟩ : syracuseStep 2026093 = 759785) (by norm_num)
theorem B2026129 : Blo 1800101 2026129 := bbase (se 2 (by rfl) ⟨759798, by rfl⟩ : syracuseStep 2026129 = 1519597) (by norm_num)
theorem B8440469 : Blo 1800101 8440469 := bbase (se 6 (by rfl) ⟨197823, by rfl⟩ : syracuseStep 8440469 = 395647) (by norm_num)
theorem B2280089 : Blo 1800101 2280089 := bbase (se 2 (by rfl) ⟨855033, by rfl⟩ : syracuseStep 2280089 = 1710067) (by norm_num)
theorem B4557485 : Blo 1800101 4557485 := bbase (se 3 (by rfl) ⟨854528, by rfl⟩ : syracuseStep 4557485 = 1709057) (by norm_num)
theorem B2026165 : Blo 1800101 2026165 := bbase (se 5 (by rfl) ⟨94976, by rfl⟩ : syracuseStep 2026165 = 189953) (by norm_num)
theorem B9120437 : Blo 1800101 9120437 := bbase (se 5 (by rfl) ⟨427520, by rfl⟩ : syracuseStep 9120437 = 855041) (by norm_num)
theorem B6163141 : Blo 1800101 6163141 := bbase (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) (by norm_num)
theorem B2280145 : Blo 1800101 2280145 := bbase (se 2 (by rfl) ⟨855054, by rfl⟩ : syracuseStep 2280145 = 1710109) (by norm_num)
theorem B2026201 : Blo 1800101 2026201 := bbase (se 2 (by rfl) ⟨759825, by rfl⟩ : syracuseStep 2026201 = 1519651) (by norm_num)
theorem B2026237 : Blo 1800101 2026237 := bbase (se 3 (by rfl) ⟨379919, by rfl⟩ : syracuseStep 2026237 = 759839) (by norm_num)
theorem B2026273 : Blo 1800101 2026273 := bbase (se 2 (by rfl) ⟨759852, by rfl⟩ : syracuseStep 2026273 = 1519705) (by norm_num)
theorem B3844901 : Blo 1800101 3844901 := bbase (se 4 (by rfl) ⟨360459, by rfl⟩ : syracuseStep 3844901 = 720919) (by norm_num)
theorem B6835013 : Blo 1800101 6835013 := bbase (se 4 (by rfl) ⟨640782, by rfl⟩ : syracuseStep 6835013 = 1281565) (by norm_num)
theorem B3418949 : Blo 1800101 3418949 := bbase (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) (by norm_num)
theorem B2026309 : Blo 1800101 2026309 := bbase (se 4 (by rfl) ⟨189966, by rfl⟩ : syracuseStep 2026309 = 379933) (by norm_num)
theorem B2026345 : Blo 1800101 2026345 := bbase (se 2 (by rfl) ⟨759879, by rfl⟩ : syracuseStep 2026345 = 1519759) (by norm_num)
theorem B2026381 : Blo 1800101 2026381 := bbase (se 3 (by rfl) ⟨379946, by rfl⟩ : syracuseStep 2026381 = 759893) (by norm_num)
theorem B7695269 : Blo 1800101 7695269 := bbase (se 4 (by rfl) ⟨721431, by rfl⟩ : syracuseStep 7695269 = 1442863) (by norm_num)
theorem B2026417 : Blo 1800101 2026417 := bbase (se 2 (by rfl) ⟨759906, by rfl⟩ : syracuseStep 2026417 = 1519813) (by norm_num)
theorem B2026453 : Blo 1800101 2026453 := bbase (se 7 (by rfl) ⟨23747, by rfl⟩ : syracuseStep 2026453 = 47495) (by norm_num)
theorem B3419101 : Blo 1800101 3419101 := bbase (se 3 (by rfl) ⟨641081, by rfl⟩ : syracuseStep 3419101 = 1282163) (by norm_num)
theorem B2026489 : Blo 1800101 2026489 := bbase (se 2 (by rfl) ⟨759933, by rfl⟩ : syracuseStep 2026489 = 1519867) (by norm_num)
theorem B4557829 : Blo 1800101 4557829 := bbase (se 4 (by rfl) ⟨427296, by rfl⟩ : syracuseStep 4557829 = 854593) (by norm_num)
theorem B2026525 : Blo 1800101 2026525 := bbase (se 3 (by rfl) ⟨379973, by rfl⟩ : syracuseStep 2026525 = 759947) (by norm_num)
theorem B2026561 : Blo 1800101 2026561 := bbase (se 2 (by rfl) ⟨759960, by rfl⟩ : syracuseStep 2026561 = 1519921) (by norm_num)
theorem B5270629 : Blo 1800101 5270629 := bbase (se 4 (by rfl) ⟨494121, by rfl⟩ : syracuseStep 5270629 = 988243) (by norm_num)
theorem B2026597 : Blo 1800101 2026597 := bbase (se 4 (by rfl) ⟨189993, by rfl⟩ : syracuseStep 2026597 = 379987) (by norm_num)
theorem B4557941 : Blo 1800101 4557941 := bbase (se 5 (by rfl) ⟨213653, by rfl⟩ : syracuseStep 4557941 = 427307) (by norm_num)
theorem B2026633 : Blo 1800101 2026633 := bbase (se 2 (by rfl) ⟨759987, by rfl⟩ : syracuseStep 2026633 = 1519975) (by norm_num)
theorem B2026669 : Blo 1800101 2026669 := bbase (se 3 (by rfl) ⟨380000, by rfl⟩ : syracuseStep 2026669 = 760001) (by norm_num)
theorem B2026705 : Blo 1800101 2026705 := bbase (se 2 (by rfl) ⟨760014, by rfl⟩ : syracuseStep 2026705 = 1520029) (by norm_num)
theorem B2026741 : Blo 1800101 2026741 := bbase (se 5 (by rfl) ⟨95003, by rfl⟩ : syracuseStep 2026741 = 190007) (by norm_num)
theorem B3419405 : Blo 1800101 3419405 := bbase (se 3 (by rfl) ⟨641138, by rfl⟩ : syracuseStep 3419405 = 1282277) (by norm_num)
theorem B2026777 : Blo 1800101 2026777 := bbase (se 2 (by rfl) ⟨760041, by rfl⟩ : syracuseStep 2026777 = 1520083) (by norm_num)
theorem B4558133 : Blo 1800101 4558133 := bbase (se 5 (by rfl) ⟨213662, by rfl⟩ : syracuseStep 4558133 = 427325) (by norm_num)
theorem B4050269 : Blo 1800101 4050269 := bbase (se 3 (by rfl) ⟨759425, by rfl⟩ : syracuseStep 4050269 = 1518851) (by norm_num)
theorem B24980885 : Blo 1800101 24980885 := bbase (se 6 (by rfl) ⟨585489, by rfl⟩ : syracuseStep 24980885 = 1170979) (by norm_num)
theorem B4050341 : Blo 1800101 4050341 := bbase (se 4 (by rfl) ⟨379719, by rfl⟩ : syracuseStep 4050341 = 759439) (by norm_num)
theorem B8654293 : Blo 1800101 8654293 := bbase (se 7 (by rfl) ⟨101417, by rfl⟩ : syracuseStep 8654293 = 202835) (by norm_num)
theorem B4050413 : Blo 1800101 4050413 := bbase (se 3 (by rfl) ⟨759452, by rfl⟩ : syracuseStep 4050413 = 1518905) (by norm_num)
theorem B4050485 : Blo 1800101 4050485 := bbase (se 5 (by rfl) ⟨189866, by rfl⟩ : syracuseStep 4050485 = 379733) (by norm_num)
theorem B23383637 : Blo 1800101 23383637 := bbase (se 8 (by rfl) ⟨137013, by rfl⟩ : syracuseStep 23383637 = 274027) (by norm_num)
theorem B4869749 : Blo 1800101 4869749 := bbase (se 5 (by rfl) ⟨228269, by rfl⟩ : syracuseStep 4869749 = 456539) (by norm_num)
theorem B4050557 : Blo 1800101 4050557 := bbase (se 3 (by rfl) ⟨759479, by rfl⟩ : syracuseStep 4050557 = 1518959) (by norm_num)
theorem B4558477 : Blo 1800101 4558477 := bbase (se 3 (by rfl) ⟨854714, by rfl⟩ : syracuseStep 4558477 = 1709429) (by norm_num)
theorem B5770901 : Blo 1800101 5770901 := bbase (se 6 (by rfl) ⟨135255, by rfl⟩ : syracuseStep 5770901 = 270511) (by norm_num)
theorem B3845789 : Blo 1800101 3845789 := bbase (se 3 (by rfl) ⟨721085, by rfl⟩ : syracuseStep 3845789 = 1442171) (by norm_num)
theorem B4050629 : Blo 1800101 4050629 := bbase (se 4 (by rfl) ⟨379746, by rfl⟩ : syracuseStep 4050629 = 759493) (by norm_num)
theorem B4558589 : Blo 1800101 4558589 := bbase (se 3 (by rfl) ⟨854735, by rfl⟩ : syracuseStep 4558589 = 1709471) (by norm_num)
theorem B4050701 : Blo 1800101 4050701 := bbase (se 3 (by rfl) ⟨759506, by rfl⟩ : syracuseStep 4050701 = 1519013) (by norm_num)
theorem B4050773 : Blo 1800101 4050773 := bbase (se 9 (by rfl) ⟨11867, by rfl⟩ : syracuseStep 4050773 = 23735) (by norm_num)
theorem B3846037 : Blo 1800101 3846037 := bbase (se 6 (by rfl) ⟨90141, by rfl⟩ : syracuseStep 3846037 = 180283) (by norm_num)
theorem B4050845 : Blo 1800101 4050845 := bbase (se 3 (by rfl) ⟨759533, by rfl⟩ : syracuseStep 4050845 = 1519067) (by norm_num)
theorem B4558781 : Blo 1800101 4558781 := bbase (se 3 (by rfl) ⟨854771, by rfl⟩ : syracuseStep 4558781 = 1709543) (by norm_num)
theorem B4050917 : Blo 1800101 4050917 := bbase (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) (by norm_num)
theorem B6836197 : Blo 1800101 6836197 := bbase (se 4 (by rfl) ⟨640893, by rfl⟩ : syracuseStep 6836197 = 1281787) (by norm_num)
theorem B2633717 : Blo 1800101 2633717 := bbase (se 5 (by rfl) ⟨123455, by rfl⟩ : syracuseStep 2633717 = 246911) (by norm_num)
theorem B3420157 : Blo 1800101 3420157 := bbase (se 3 (by rfl) ⟨641279, by rfl⟩ : syracuseStep 3420157 = 1282559) (by norm_num)
theorem B4050989 : Blo 1800101 4050989 := bbase (se 3 (by rfl) ⟨759560, by rfl⟩ : syracuseStep 4050989 = 1519121) (by norm_num)
theorem B3649637 : Blo 1800101 3649637 := bbase (se 4 (by rfl) ⟨342153, by rfl⟩ : syracuseStep 3649637 = 684307) (by norm_num)
theorem B4051061 : Blo 1800101 4051061 := bbase (se 5 (by rfl) ⟨189893, by rfl⟩ : syracuseStep 4051061 = 379787) (by norm_num)
theorem B4051133 : Blo 1800101 4051133 := bbase (se 3 (by rfl) ⟨759587, by rfl⟩ : syracuseStep 4051133 = 1519175) (by norm_num)
theorem B4051205 : Blo 1800101 4051205 := bbase (se 4 (by rfl) ⟨379800, by rfl⟩ : syracuseStep 4051205 = 759601) (by norm_num)
theorem B10252565 : Blo 1800101 10252565 := bbase (se 6 (by rfl) ⟨240294, by rfl⟩ : syracuseStep 10252565 = 480589) (by norm_num)
theorem B6836501 : Blo 1800101 6836501 := bbase (se 6 (by rfl) ⟨160230, by rfl⟩ : syracuseStep 6836501 = 320461) (by norm_num)
theorem B4559125 : Blo 1800101 4559125 := bbase (se 6 (by rfl) ⟨106854, by rfl⟩ : syracuseStep 4559125 = 213709) (by norm_num)
theorem B3289405 : Blo 1800101 3289405 := bbase (se 3 (by rfl) ⟨616763, by rfl⟩ : syracuseStep 3289405 = 1233527) (by norm_num)
theorem B4051277 : Blo 1800101 4051277 := bbase (se 3 (by rfl) ⟨759614, by rfl⟩ : syracuseStep 4051277 = 1519229) (by norm_num)
theorem B5476693 : Blo 1800101 5476693 := bbase (se 10 (by rfl) ⟨8022, by rfl⟩ : syracuseStep 5476693 = 16045) (by norm_num)
theorem B9113957 : Blo 1800101 9113957 := bbase (se 4 (by rfl) ⟨854433, by rfl⟩ : syracuseStep 9113957 = 1708867) (by norm_num)
theorem B17305973 : Blo 1800101 17305973 := bbase (se 5 (by rfl) ⟨811217, by rfl⟩ : syracuseStep 17305973 = 1622435) (by norm_num)
theorem B4559237 : Blo 1800101 4559237 := bbase (se 4 (by rfl) ⟨427428, by rfl⟩ : syracuseStep 4559237 = 854857) (by norm_num)
theorem B3846541 : Blo 1800101 3846541 := bbase (se 3 (by rfl) ⟨721226, by rfl⟩ : syracuseStep 3846541 = 1442453) (by norm_num)
theorem B4444565 : Blo 1800101 4444565 := bbase (se 6 (by rfl) ⟨104169, by rfl⟩ : syracuseStep 4444565 = 208339) (by norm_num)
theorem B4051349 : Blo 1800101 4051349 := bbase (se 6 (by rfl) ⟨94953, by rfl⟩ : syracuseStep 4051349 = 189907) (by norm_num)
theorem B6492565 : Blo 1800101 6492565 := bbase (se 6 (by rfl) ⟨152169, by rfl⟩ : syracuseStep 6492565 = 304339) (by norm_num)
theorem B4051421 : Blo 1800101 4051421 := bbase (se 3 (by rfl) ⟨759641, by rfl⟩ : syracuseStep 4051421 = 1519283) (by norm_num)
theorem B4051493 : Blo 1800101 4051493 := bbase (se 4 (by rfl) ⟨379827, by rfl⟩ : syracuseStep 4051493 = 759655) (by norm_num)
theorem B6492725 : Blo 1800101 6492725 := bbase (se 5 (by rfl) ⟨304346, by rfl⟩ : syracuseStep 6492725 = 608693) (by norm_num)
theorem B4559429 : Blo 1800101 4559429 := bbase (se 4 (by rfl) ⟨427446, by rfl⟩ : syracuseStep 4559429 = 854893) (by norm_num)
theorem B4051565 : Blo 1800101 4051565 := bbase (se 3 (by rfl) ⟨759668, by rfl⟩ : syracuseStep 4051565 = 1519337) (by norm_num)
theorem B4051637 : Blo 1800101 4051637 := bbase (se 5 (by rfl) ⟨189920, by rfl⟩ : syracuseStep 4051637 = 379841) (by norm_num)
theorem B3650285 : Blo 1800101 3650285 := bbase (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) (by norm_num)
theorem B4051709 : Blo 1800101 4051709 := bbase (se 3 (by rfl) ⟨759695, by rfl⟩ : syracuseStep 4051709 = 1519391) (by norm_num)
theorem B4051781 : Blo 1800101 4051781 := bbase (se 4 (by rfl) ⟨379854, by rfl⟩ : syracuseStep 4051781 = 759709) (by norm_num)
theorem B9237365 : Blo 1800101 9237365 := bbase (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) (by norm_num)
theorem B2700173 : Blo 1800101 2700173 := bbase (se 3 (by rfl) ⟨506282, by rfl⟩ : syracuseStep 2700173 = 1012565) (by norm_num)
theorem B4051853 : Blo 1800101 4051853 := bbase (se 3 (by rfl) ⟨759722, by rfl⟩ : syracuseStep 4051853 = 1519445) (by norm_num)
theorem B4559773 : Blo 1800101 4559773 := bbase (se 3 (by rfl) ⟨854957, by rfl⟩ : syracuseStep 4559773 = 1709915) (by norm_num)
theorem B2700197 : Blo 1800101 2700197 := bbase (se 4 (by rfl) ⟨253143, by rfl⟩ : syracuseStep 2700197 = 506287) (by norm_num)
theorem B2700221 : Blo 1800101 2700221 := bbase (se 3 (by rfl) ⟨506291, by rfl⟩ : syracuseStep 2700221 = 1012583) (by norm_num)
theorem B2700245 : Blo 1800101 2700245 := bbase (se 7 (by rfl) ⟨31643, by rfl⟩ : syracuseStep 2700245 = 63287) (by norm_num)
theorem B4051925 : Blo 1800101 4051925 := bbase (se 7 (by rfl) ⟨47483, by rfl⟩ : syracuseStep 4051925 = 94967) (by norm_num)
theorem B2053085 : Blo 1800101 2053085 := bbase (se 3 (by rfl) ⟨384953, by rfl⟩ : syracuseStep 2053085 = 769907) (by norm_num)
theorem B2700269 : Blo 1800101 2700269 := bbase (se 3 (by rfl) ⟨506300, by rfl⟩ : syracuseStep 2700269 = 1012601) (by norm_num)
theorem B2700293 : Blo 1800101 2700293 := bbase (se 4 (by rfl) ⟨253152, by rfl⟩ : syracuseStep 2700293 = 506305) (by norm_num)
theorem B4559885 : Blo 1800101 4559885 := bbase (se 3 (by rfl) ⟨854978, by rfl⟩ : syracuseStep 4559885 = 1709957) (by norm_num)
theorem B2700317 : Blo 1800101 2700317 := bbase (se 3 (by rfl) ⟨506309, by rfl⟩ : syracuseStep 2700317 = 1012619) (by norm_num)
theorem B4051997 : Blo 1800101 4051997 := bbase (se 3 (by rfl) ⟨759749, by rfl⟩ : syracuseStep 4051997 = 1519499) (by norm_num)
theorem B2700341 : Blo 1800101 2700341 := bbase (se 5 (by rfl) ⟨126578, by rfl⟩ : syracuseStep 2700341 = 253157) (by norm_num)
theorem B2700365 : Blo 1800101 2700365 := bbase (se 3 (by rfl) ⟨506318, by rfl⟩ : syracuseStep 2700365 = 1012637) (by norm_num)
theorem B2700389 : Blo 1800101 2700389 := bbase (se 4 (by rfl) ⟨253161, by rfl⟩ : syracuseStep 2700389 = 506323) (by norm_num)
theorem B4052069 : Blo 1800101 4052069 := bbase (se 4 (by rfl) ⟨379881, by rfl⟩ : syracuseStep 4052069 = 759763) (by norm_num)
theorem B2700413 : Blo 1800101 2700413 := bbase (se 3 (by rfl) ⟨506327, by rfl⟩ : syracuseStep 2700413 = 1012655) (by norm_num)
theorem B2700437 : Blo 1800101 2700437 := bbase (se 6 (by rfl) ⟨63291, by rfl⟩ : syracuseStep 2700437 = 126583) (by norm_num)
theorem B2700461 : Blo 1800101 2700461 := bbase (se 3 (by rfl) ⟨506336, by rfl⟩ : syracuseStep 2700461 = 1012673) (by norm_num)
theorem B4052141 : Blo 1800101 4052141 := bbase (se 3 (by rfl) ⟨759776, by rfl⟩ : syracuseStep 4052141 = 1519553) (by norm_num)
theorem B2700485 : Blo 1800101 2700485 := bbase (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) (by norm_num)
theorem B4560077 : Blo 1800101 4560077 := bbase (se 3 (by rfl) ⟨855014, by rfl⟩ : syracuseStep 4560077 = 1710029) (by norm_num)
theorem B4748501 : Blo 1800101 4748501 := bbase (se 7 (by rfl) ⟨55646, by rfl⟩ : syracuseStep 4748501 = 111293) (by norm_num)
theorem B2700509 : Blo 1800101 2700509 := bbase (se 3 (by rfl) ⟨506345, by rfl⟩ : syracuseStep 2700509 = 1012691) (by norm_num)
theorem B2700533 : Blo 1800101 2700533 := bbase (se 5 (by rfl) ⟨126587, by rfl⟩ : syracuseStep 2700533 = 253175) (by norm_num)
theorem B4052213 : Blo 1800101 4052213 := bbase (se 5 (by rfl) ⟨189947, by rfl⟩ : syracuseStep 4052213 = 379895) (by norm_num)
theorem B3847429 : Blo 1800101 3847429 := bbase (se 4 (by rfl) ⟨360696, by rfl⟩ : syracuseStep 3847429 = 721393) (by norm_num)
theorem B2700557 : Blo 1800101 2700557 := bbase (se 3 (by rfl) ⟨506354, by rfl⟩ : syracuseStep 2700557 = 1012709) (by norm_num)
theorem B2700581 : Blo 1800101 2700581 := bbase (se 4 (by rfl) ⟨253179, by rfl⟩ : syracuseStep 2700581 = 506359) (by norm_num)
theorem B3650861 : Blo 1800101 3650861 := bbase (se 3 (by rfl) ⟨684536, by rfl⟩ : syracuseStep 3650861 = 1369073) (by norm_num)
theorem B6075701 : Blo 1800101 6075701 := bbase (se 5 (by rfl) ⟨284798, by rfl⟩ : syracuseStep 6075701 = 569597) (by norm_num)
theorem B2700605 : Blo 1800101 2700605 := bbase (se 3 (by rfl) ⟨506363, by rfl⟩ : syracuseStep 2700605 = 1012727) (by norm_num)
theorem B4052285 : Blo 1800101 4052285 := bbase (se 3 (by rfl) ⟨759803, by rfl⟩ : syracuseStep 4052285 = 1519607) (by norm_num)
theorem B2700629 : Blo 1800101 2700629 := bbase (se 13 (by rfl) ⟨494, by rfl⟩ : syracuseStep 2700629 = 989) (by norm_num)
theorem B2700653 : Blo 1800101 2700653 := bbase (se 3 (by rfl) ⟨506372, by rfl⟩ : syracuseStep 2700653 = 1012745) (by norm_num)
theorem B3650933 : Blo 1800101 3650933 := bbase (se 5 (by rfl) ⟨171137, by rfl⟩ : syracuseStep 3650933 = 342275) (by norm_num)
theorem B2700677 : Blo 1800101 2700677 := bbase (se 4 (by rfl) ⟨253188, by rfl⟩ : syracuseStep 2700677 = 506377) (by norm_num)
theorem B4052357 : Blo 1800101 4052357 := bbase (se 4 (by rfl) ⟨379908, by rfl⟩ : syracuseStep 4052357 = 759817) (by norm_num)
theorem B2700701 : Blo 1800101 2700701 := bbase (se 3 (by rfl) ⟨506381, by rfl⟩ : syracuseStep 2700701 = 1012763) (by norm_num)
theorem B10253749 : Blo 1800101 10253749 := bbase (se 5 (by rfl) ⟨480644, by rfl⟩ : syracuseStep 10253749 = 961289) (by norm_num)
theorem B2700725 : Blo 1800101 2700725 := bbase (se 5 (by rfl) ⟨126596, by rfl⟩ : syracuseStep 2700725 = 253193) (by norm_num)
theorem B2700749 : Blo 1800101 2700749 := bbase (se 3 (by rfl) ⟨506390, by rfl⟩ : syracuseStep 2700749 = 1012781) (by norm_num)
theorem B4052429 : Blo 1800101 4052429 := bbase (se 3 (by rfl) ⟨759830, by rfl⟩ : syracuseStep 4052429 = 1519661) (by norm_num)
theorem B2700773 : Blo 1800101 2700773 := bbase (se 4 (by rfl) ⟨253197, by rfl⟩ : syracuseStep 2700773 = 506395) (by norm_num)
theorem B8328677 : Blo 1800101 8328677 := bbase (se 4 (by rfl) ⟨780813, by rfl⟩ : syracuseStep 8328677 = 1561627) (by norm_num)
theorem B2700797 : Blo 1800101 2700797 := bbase (se 3 (by rfl) ⟨506399, by rfl⟩ : syracuseStep 2700797 = 1012799) (by norm_num)
theorem B2700821 : Blo 1800101 2700821 := bbase (se 6 (by rfl) ⟨63300, by rfl⟩ : syracuseStep 2700821 = 126601) (by norm_num)
theorem B4052501 : Blo 1800101 4052501 := bbase (se 6 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 4052501 = 189961) (by norm_num)
theorem B2053669 : Blo 1800101 2053669 := bbase (se 4 (by rfl) ⟨192531, by rfl⟩ : syracuseStep 2053669 = 385063) (by norm_num)
theorem B2700845 : Blo 1800101 2700845 := bbase (se 3 (by rfl) ⟨506408, by rfl⟩ : syracuseStep 2700845 = 1012817) (by norm_num)
theorem B1922621 : Blo 1800101 1922621 := bbase (se 3 (by rfl) ⟨360491, by rfl⟩ : syracuseStep 1922621 = 720983) (by norm_num)
theorem B2700869 : Blo 1800101 2700869 := bbase (se 4 (by rfl) ⟨253206, by rfl⟩ : syracuseStep 2700869 = 506413) (by norm_num)
theorem B5477957 : Blo 1800101 5477957 := bbase (se 4 (by rfl) ⟨513558, by rfl⟩ : syracuseStep 5477957 = 1027117) (by norm_num)
theorem B2700893 : Blo 1800101 2700893 := bbase (se 3 (by rfl) ⟨506417, by rfl⟩ : syracuseStep 2700893 = 1012835) (by norm_num)
theorem B4052573 : Blo 1800101 4052573 := bbase (se 3 (by rfl) ⟨759857, by rfl⟩ : syracuseStep 4052573 = 1519715) (by norm_num)
theorem B9115253 : Blo 1800101 9115253 := bbase (se 5 (by rfl) ⟨427277, by rfl⟩ : syracuseStep 9115253 = 854555) (by norm_num)
theorem B2700917 : Blo 1800101 2700917 := bbase (se 5 (by rfl) ⟨126605, by rfl⟩ : syracuseStep 2700917 = 253211) (by norm_num)
theorem B2700941 : Blo 1800101 2700941 := bbase (se 3 (by rfl) ⟨506426, by rfl⟩ : syracuseStep 2700941 = 1012853) (by norm_num)
theorem B2700965 : Blo 1800101 2700965 := bbase (se 4 (by rfl) ⟨253215, by rfl⟩ : syracuseStep 2700965 = 506431) (by norm_num)
theorem B4052645 : Blo 1800101 4052645 := bbase (se 4 (by rfl) ⟨379935, by rfl⟩ : syracuseStep 4052645 = 759871) (by norm_num)
theorem B2700989 : Blo 1800101 2700989 := bbase (se 3 (by rfl) ⟨506435, by rfl⟩ : syracuseStep 2700989 = 1012871) (by norm_num)
theorem B2701013 : Blo 1800101 2701013 := bbase (se 7 (by rfl) ⟨31652, by rfl⟩ : syracuseStep 2701013 = 63305) (by norm_num)
theorem B2193113 : Blo 1800101 2193113 := bbase (se 2 (by rfl) ⟨822417, by rfl⟩ : syracuseStep 2193113 = 1644835) (by norm_num)
theorem B6076133 : Blo 1800101 6076133 := bbase (se 4 (by rfl) ⟨569637, by rfl⟩ : syracuseStep 6076133 = 1139275) (by norm_num)
theorem B2701037 : Blo 1800101 2701037 := bbase (se 3 (by rfl) ⟨506444, by rfl⟩ : syracuseStep 2701037 = 1012889) (by norm_num)
theorem B4052717 : Blo 1800101 4052717 := bbase (se 3 (by rfl) ⟨759884, by rfl⟩ : syracuseStep 4052717 = 1519769) (by norm_num)
theorem B2701061 : Blo 1800101 2701061 := bbase (se 4 (by rfl) ⟨253224, by rfl⟩ : syracuseStep 2701061 = 506449) (by norm_num)
theorem B3381005 : Blo 1800101 3381005 := bbase (se 3 (by rfl) ⟨633938, by rfl⟩ : syracuseStep 3381005 = 1267877) (by norm_num)
theorem B2701085 : Blo 1800101 2701085 := bbase (se 3 (by rfl) ⟨506453, by rfl⟩ : syracuseStep 2701085 = 1012907) (by norm_num)
theorem B1922869 : Blo 1800101 1922869 := bbase (se 5 (by rfl) ⟨90134, by rfl⟩ : syracuseStep 1922869 = 180269) (by norm_num)
theorem B2701109 : Blo 1800101 2701109 := bbase (se 5 (by rfl) ⟨126614, by rfl⟩ : syracuseStep 2701109 = 253229) (by norm_num)
theorem B4052789 : Blo 1800101 4052789 := bbase (se 5 (by rfl) ⟨189974, by rfl⟩ : syracuseStep 4052789 = 379949) (by norm_num)
theorem B2701133 : Blo 1800101 2701133 := bbase (se 3 (by rfl) ⟨506462, by rfl⟩ : syracuseStep 2701133 = 1012925) (by norm_num)
theorem B2701157 : Blo 1800101 2701157 := bbase (se 4 (by rfl) ⟨253233, by rfl⟩ : syracuseStep 2701157 = 506467) (by norm_num)
theorem B2701181 : Blo 1800101 2701181 := bbase (se 3 (by rfl) ⟨506471, by rfl⟩ : syracuseStep 2701181 = 1012943) (by norm_num)
theorem B4052861 : Blo 1800101 4052861 := bbase (se 3 (by rfl) ⟨759911, by rfl⟩ : syracuseStep 4052861 = 1519823) (by norm_num)
theorem B2701205 : Blo 1800101 2701205 := bbase (se 6 (by rfl) ⟨63309, by rfl⟩ : syracuseStep 2701205 = 126619) (by norm_num)
theorem B2701229 : Blo 1800101 2701229 := bbase (se 3 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 2701229 = 1012961) (by norm_num)
theorem B2701253 : Blo 1800101 2701253 := bbase (se 4 (by rfl) ⟨253242, by rfl⟩ : syracuseStep 2701253 = 506485) (by norm_num)
theorem B4052933 : Blo 1800101 4052933 := bbase (se 4 (by rfl) ⟨379962, by rfl⟩ : syracuseStep 4052933 = 759925) (by norm_num)
theorem B2054089 : Blo 1800101 2054089 := bbase (se 2 (by rfl) ⟨770283, by rfl⟩ : syracuseStep 2054089 = 1540567) (by norm_num)
theorem B2701277 : Blo 1800101 2701277 := bbase (se 3 (by rfl) ⟨506489, by rfl⟩ : syracuseStep 2701277 = 1012979) (by norm_num)
theorem B2701301 : Blo 1800101 2701301 := bbase (se 5 (by rfl) ⟨126623, by rfl⟩ : syracuseStep 2701301 = 253247) (by norm_num)
theorem B2701325 : Blo 1800101 2701325 := bbase (se 3 (by rfl) ⟨506498, by rfl⟩ : syracuseStep 2701325 = 1012997) (by norm_num)
theorem B4053005 : Blo 1800101 4053005 := bbase (se 3 (by rfl) ⟨759938, by rfl⟩ : syracuseStep 4053005 = 1519877) (by norm_num)
theorem B2054161 : Blo 1800101 2054161 := bbase (se 2 (by rfl) ⟨770310, by rfl⟩ : syracuseStep 2054161 = 1540621) (by norm_num)
theorem B2701349 : Blo 1800101 2701349 := bbase (se 4 (by rfl) ⟨253251, by rfl⟩ : syracuseStep 2701349 = 506503) (by norm_num)
theorem B2701373 : Blo 1800101 2701373 := bbase (se 3 (by rfl) ⟨506507, by rfl⟩ : syracuseStep 2701373 = 1013015) (by norm_num)
theorem B2701397 : Blo 1800101 2701397 := bbase (se 8 (by rfl) ⟨15828, by rfl⟩ : syracuseStep 2701397 = 31657) (by norm_num)
theorem B4053077 : Blo 1800101 4053077 := bbase (se 8 (by rfl) ⟨23748, by rfl⟩ : syracuseStep 4053077 = 47497) (by norm_num)
theorem B2701421 : Blo 1800101 2701421 := bbase (se 3 (by rfl) ⟨506516, by rfl⟩ : syracuseStep 2701421 = 1013033) (by norm_num)
theorem B2701445 : Blo 1800101 2701445 := bbase (se 4 (by rfl) ⟨253260, by rfl⟩ : syracuseStep 2701445 = 506521) (by norm_num)
theorem B6076565 : Blo 1800101 6076565 := bbase (se 6 (by rfl) ⟨142419, by rfl⟩ : syracuseStep 6076565 = 284839) (by norm_num)
theorem B2701469 : Blo 1800101 2701469 := bbase (se 3 (by rfl) ⟨506525, by rfl⟩ : syracuseStep 2701469 = 1013051) (by norm_num)
theorem B4053149 : Blo 1800101 4053149 := bbase (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) (by norm_num)
theorem B2701493 : Blo 1800101 2701493 := bbase (se 5 (by rfl) ⟨126632, by rfl⟩ : syracuseStep 2701493 = 253265) (by norm_num)
theorem B2701517 : Blo 1800101 2701517 := bbase (se 3 (by rfl) ⟨506534, by rfl⟩ : syracuseStep 2701517 = 1013069) (by norm_num)
theorem B2701541 : Blo 1800101 2701541 := bbase (se 4 (by rfl) ⟨253269, by rfl⟩ : syracuseStep 2701541 = 506539) (by norm_num)
theorem B4053221 : Blo 1800101 4053221 := bbase (se 4 (by rfl) ⟨379989, by rfl⟩ : syracuseStep 4053221 = 759979) (by norm_num)
theorem B1923313 : Blo 1800101 1923313 := bbase (se 2 (by rfl) ⟨721242, by rfl⟩ : syracuseStep 1923313 = 1442485) (by norm_num)
theorem B2701565 : Blo 1800101 2701565 := bbase (se 3 (by rfl) ⟨506543, by rfl⟩ : syracuseStep 2701565 = 1013087) (by norm_num)
theorem B2701589 : Blo 1800101 2701589 := bbase (se 6 (by rfl) ⟨63318, by rfl⟩ : syracuseStep 2701589 = 126637) (by norm_num)
theorem B2701613 : Blo 1800101 2701613 := bbase (se 3 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 2701613 = 1013105) (by norm_num)
theorem B1923373 : Blo 1800101 1923373 := bbase (se 3 (by rfl) ⟨360632, by rfl⟩ : syracuseStep 1923373 = 721265) (by norm_num)
theorem B4053293 : Blo 1800101 4053293 := bbase (se 3 (by rfl) ⟨759992, by rfl⟩ : syracuseStep 4053293 = 1519985) (by norm_num)
theorem B2701637 : Blo 1800101 2701637 := bbase (se 4 (by rfl) ⟨253278, by rfl⟩ : syracuseStep 2701637 = 506557) (by norm_num)
theorem B6838613 : Blo 1800101 6838613 := bbase (se 10 (by rfl) ⟨10017, by rfl⟩ : syracuseStep 6838613 = 20035) (by norm_num)
theorem B2701661 : Blo 1800101 2701661 := bbase (se 3 (by rfl) ⟨506561, by rfl⟩ : syracuseStep 2701661 = 1013123) (by norm_num)
theorem B2701685 : Blo 1800101 2701685 := bbase (se 5 (by rfl) ⟨126641, by rfl⟩ : syracuseStep 2701685 = 253283) (by norm_num)
theorem B4053365 : Blo 1800101 4053365 := bbase (se 5 (by rfl) ⟨190001, by rfl⟩ : syracuseStep 4053365 = 380003) (by norm_num)
theorem B2701709 : Blo 1800101 2701709 := bbase (se 3 (by rfl) ⟨506570, by rfl⟩ : syracuseStep 2701709 = 1013141) (by norm_num)
theorem B2701733 : Blo 1800101 2701733 := bbase (se 4 (by rfl) ⟨253287, by rfl⟩ : syracuseStep 2701733 = 506575) (by norm_num)
theorem B2701757 : Blo 1800101 2701757 := bbase (se 3 (by rfl) ⟨506579, by rfl⟩ : syracuseStep 2701757 = 1013159) (by norm_num)
theorem B4053437 : Blo 1800101 4053437 := bbase (se 3 (by rfl) ⟨760019, by rfl⟩ : syracuseStep 4053437 = 1520039) (by norm_num)
theorem B2701781 : Blo 1800101 2701781 := bbase (se 7 (by rfl) ⟨31661, by rfl⟩ : syracuseStep 2701781 = 63323) (by norm_num)
theorem B2701805 : Blo 1800101 2701805 := bbase (se 3 (by rfl) ⟨506588, by rfl⟩ : syracuseStep 2701805 = 1013177) (by norm_num)
theorem B11540981 : Blo 1800101 11540981 := bbase (se 5 (by rfl) ⟨540983, by rfl⟩ : syracuseStep 11540981 = 1081967) (by norm_num)
theorem B2701829 : Blo 1800101 2701829 := bbase (se 4 (by rfl) ⟨253296, by rfl⟩ : syracuseStep 2701829 = 506593) (by norm_num)
theorem B4053509 : Blo 1800101 4053509 := bbase (se 4 (by rfl) ⟨380016, by rfl⟩ : syracuseStep 4053509 = 760033) (by norm_num)
theorem B3037709 : Blo 1800101 3037709 := bbase (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) (by norm_num)
theorem B2701853 : Blo 1800101 2701853 := bbase (se 3 (by rfl) ⟨506597, by rfl⟩ : syracuseStep 2701853 = 1013195) (by norm_num)
theorem B2701877 : Blo 1800101 2701877 := bbase (se 5 (by rfl) ⟨126650, by rfl⟩ : syracuseStep 2701877 = 253301) (by norm_num)
theorem B6076997 : Blo 1800101 6076997 := bbase (se 4 (by rfl) ⟨569718, by rfl⟩ : syracuseStep 6076997 = 1139437) (by norm_num)
theorem B2923085 : Blo 1800101 2923085 := bbase (se 3 (by rfl) ⟨548078, by rfl⟩ : syracuseStep 2923085 = 1096157) (by norm_num)
theorem B2701901 : Blo 1800101 2701901 := bbase (se 3 (by rfl) ⟨506606, by rfl⟩ : syracuseStep 2701901 = 1013213) (by norm_num)
theorem B4053581 : Blo 1800101 4053581 := bbase (se 3 (by rfl) ⟨760046, by rfl⟩ : syracuseStep 4053581 = 1520093) (by norm_num)
theorem B2701925 : Blo 1800101 2701925 := bbase (se 4 (by rfl) ⟨253305, by rfl⟩ : syracuseStep 2701925 = 506611) (by norm_num)
theorem B1923689 : Blo 1800101 1923689 := bbase (se 2 (by rfl) ⟨721383, by rfl⟩ : syracuseStep 1923689 = 1442767) (by norm_num)
theorem B5126773 : Blo 1800101 5126773 := bbase (se 5 (by rfl) ⟨240317, by rfl⟩ : syracuseStep 5126773 = 480635) (by norm_num)
theorem B6838901 : Blo 1800101 6838901 := bbase (se 5 (by rfl) ⟨320573, by rfl⟩ : syracuseStep 6838901 = 641147) (by norm_num)
theorem B2701949 : Blo 1800101 2701949 := bbase (se 3 (by rfl) ⟨506615, by rfl⟩ : syracuseStep 2701949 = 1013231) (by norm_num)
theorem B3037837 : Blo 1800101 3037837 := bbase (se 3 (by rfl) ⟨569594, by rfl⟩ : syracuseStep 3037837 = 1139189) (by norm_num)
theorem B2701973 : Blo 1800101 2701973 := bbase (se 6 (by rfl) ⟨63327, by rfl⟩ : syracuseStep 2701973 = 126655) (by norm_num)
theorem B2701997 : Blo 1800101 2701997 := bbase (se 3 (by rfl) ⟨506624, by rfl⟩ : syracuseStep 2701997 = 1013249) (by norm_num)
theorem B2702021 : Blo 1800101 2702021 := bbase (se 4 (by rfl) ⟨253314, by rfl⟩ : syracuseStep 2702021 = 506629) (by norm_num)
theorem B2702045 : Blo 1800101 2702045 := bbase (se 3 (by rfl) ⟨506633, by rfl⟩ : syracuseStep 2702045 = 1013267) (by norm_num)
theorem B3037925 : Blo 1800101 3037925 := bbase (se 4 (by rfl) ⟨284805, by rfl⟩ : syracuseStep 3037925 = 569611) (by norm_num)
theorem B2702069 : Blo 1800101 2702069 := bbase (se 5 (by rfl) ⟨126659, by rfl⟩ : syracuseStep 2702069 = 253319) (by norm_num)
theorem B2702093 : Blo 1800101 2702093 := bbase (se 3 (by rfl) ⟨506642, by rfl⟩ : syracuseStep 2702093 = 1013285) (by norm_num)
theorem B2702117 : Blo 1800101 2702117 := bbase (se 4 (by rfl) ⟨253323, by rfl⟩ : syracuseStep 2702117 = 506647) (by norm_num)
theorem B2030393 : Blo 1800101 2030393 := bbase (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) (by norm_num)
theorem B2702141 : Blo 1800101 2702141 := bbase (se 3 (by rfl) ⟨506651, by rfl⟩ : syracuseStep 2702141 = 1013303) (by norm_num)
theorem B2702165 : Blo 1800101 2702165 := bbase (se 9 (by rfl) ⟨7916, by rfl⟩ : syracuseStep 2702165 = 15833) (by norm_num)
theorem B3038053 : Blo 1800101 3038053 := bbase (se 4 (by rfl) ⟨284817, by rfl⟩ : syracuseStep 3038053 = 569635) (by norm_num)
theorem B1825637 : Blo 1800101 1825637 := bbase (se 4 (by rfl) ⟨171153, by rfl⟩ : syracuseStep 1825637 = 342307) (by norm_num)
theorem B2702189 : Blo 1800101 2702189 := bbase (se 3 (by rfl) ⟨506660, by rfl⟩ : syracuseStep 2702189 = 1013321) (by norm_num)
theorem B1825661 : Blo 1800101 1825661 := bbase (se 3 (by rfl) ⟨342311, by rfl⟩ : syracuseStep 1825661 = 684623) (by norm_num)
theorem B9116549 : Blo 1800101 9116549 := bbase (se 4 (by rfl) ⟨854676, by rfl⟩ : syracuseStep 9116549 = 1709353) (by norm_num)
theorem B2702213 : Blo 1800101 2702213 := bbase (se 4 (by rfl) ⟨253332, by rfl⟩ : syracuseStep 2702213 = 506665) (by norm_num)
theorem B2702237 : Blo 1800101 2702237 := bbase (se 3 (by rfl) ⟨506669, by rfl⟩ : syracuseStep 2702237 = 1013339) (by norm_num)
theorem B3898277 : Blo 1800101 3898277 := bbase (se 4 (by rfl) ⟨365463, by rfl⟩ : syracuseStep 3898277 = 730927) (by norm_num)
theorem B2702261 : Blo 1800101 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B3038141 : Blo 1800101 3038141 := bbase (se 3 (by rfl) ⟨569651, by rfl⟩ : syracuseStep 3038141 = 1139303) (by norm_num)
theorem B2702285 : Blo 1800101 2702285 := bbase (se 3 (by rfl) ⟨506678, by rfl⟩ : syracuseStep 2702285 = 1013357) (by norm_num)
theorem B2702309 : Blo 1800101 2702309 := bbase (se 4 (by rfl) ⟨253341, by rfl⟩ : syracuseStep 2702309 = 506683) (by norm_num)
theorem B6077429 : Blo 1800101 6077429 := bbase (se 5 (by rfl) ⟨284879, by rfl⟩ : syracuseStep 6077429 = 569759) (by norm_num)
theorem B2702333 : Blo 1800101 2702333 := bbase (se 3 (by rfl) ⟨506687, by rfl⟩ : syracuseStep 2702333 = 1013375) (by norm_num)
theorem B7691269 : Blo 1800101 7691269 := bbase (se 4 (by rfl) ⟨721056, by rfl⟩ : syracuseStep 7691269 = 1442113) (by norm_num)
theorem B2702357 : Blo 1800101 2702357 := bbase (se 6 (by rfl) ⟨63336, by rfl⟩ : syracuseStep 2702357 = 126673) (by norm_num)
theorem B2702381 : Blo 1800101 2702381 := bbase (se 3 (by rfl) ⟨506696, by rfl⟩ : syracuseStep 2702381 = 1013393) (by norm_num)
theorem B3038269 : Blo 1800101 3038269 := bbase (se 3 (by rfl) ⟨569675, by rfl⟩ : syracuseStep 3038269 = 1139351) (by norm_num)
theorem B4447325 : Blo 1800101 4447325 := bbase (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) (by norm_num)
theorem B9370757 : Blo 1800101 9370757 := bbase (se 4 (by rfl) ⟨878508, by rfl⟩ : syracuseStep 9370757 = 1757017) (by norm_num)
theorem B3038357 : Blo 1800101 3038357 := bbase (se 6 (by rfl) ⟨71211, by rfl⟩ : syracuseStep 3038357 = 142423) (by norm_num)
theorem B2776213 : Blo 1800101 2776213 := bbase (se 6 (by rfl) ⟨65067, by rfl⟩ : syracuseStep 2776213 = 130135) (by norm_num)
theorem B2923733 : Blo 1800101 2923733 := bbase (se 7 (by rfl) ⟨34262, by rfl⟩ : syracuseStep 2923733 = 68525) (by norm_num)
theorem B3038485 : Blo 1800101 3038485 := bbase (se 6 (by rfl) ⟨71214, by rfl⟩ : syracuseStep 3038485 = 142429) (by norm_num)
theorem B3038573 : Blo 1800101 3038573 := bbase (se 3 (by rfl) ⟨569732, by rfl⟩ : syracuseStep 3038573 = 1139465) (by norm_num)
theorem B10255733 : Blo 1800101 10255733 := bbase (se 5 (by rfl) ⟨480737, by rfl⟩ : syracuseStep 10255733 = 961475) (by norm_num)
theorem B6077861 : Blo 1800101 6077861 := bbase (se 4 (by rfl) ⟨569799, by rfl⟩ : syracuseStep 6077861 = 1139599) (by norm_num)
theorem B3513773 : Blo 1800101 3513773 := bbase (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) (by norm_num)
theorem B4619749 : Blo 1800101 4619749 := bbase (se 4 (by rfl) ⟨433101, by rfl⟩ : syracuseStep 4619749 = 866203) (by norm_num)
theorem B3038701 : Blo 1800101 3038701 := bbase (se 3 (by rfl) ⟨569756, by rfl⟩ : syracuseStep 3038701 = 1139513) (by norm_num)
theorem B3751429 : Blo 1800101 3751429 := bbase (se 4 (by rfl) ⟨351696, by rfl⟩ : syracuseStep 3751429 = 703393) (by norm_num)
theorem B2563597 : Blo 1800101 2563597 := bbase (se 3 (by rfl) ⟨480674, by rfl⟩ : syracuseStep 2563597 = 961349) (by norm_num)
theorem B3038789 : Blo 1800101 3038789 := bbase (se 4 (by rfl) ⟨284886, by rfl⟩ : syracuseStep 3038789 = 569773) (by norm_num)
theorem B4218493 : Blo 1800101 4218493 := bbase (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) (by norm_num)
theorem B5127877 : Blo 1800101 5127877 := bbase (se 4 (by rfl) ⟨480738, by rfl⟩ : syracuseStep 5127877 = 961477) (by norm_num)
theorem B3038917 : Blo 1800101 3038917 := bbase (se 4 (by rfl) ⟨284898, by rfl⟩ : syracuseStep 3038917 = 569797) (by norm_num)
theorem B6840085 : Blo 1800101 6840085 := bbase (se 6 (by rfl) ⟨160314, by rfl⟩ : syracuseStep 6840085 = 320629) (by norm_num)
theorem B3039005 : Blo 1800101 3039005 := bbase (se 3 (by rfl) ⟨569813, by rfl⟩ : syracuseStep 3039005 = 1139627) (by norm_num)
theorem B6078293 : Blo 1800101 6078293 := bbase (se 9 (by rfl) ⟨17807, by rfl⟩ : syracuseStep 6078293 = 35615) (by norm_num)
theorem B3039133 : Blo 1800101 3039133 := bbase (se 3 (by rfl) ⟨569837, by rfl⟩ : syracuseStep 3039133 = 1139675) (by norm_num)
theorem B2162593 : Blo 1800101 2162593 := bbase (se 2 (by rfl) ⟨810972, by rfl⟩ : syracuseStep 2162593 = 1621945) (by norm_num)
theorem B2883509 : Blo 1800101 2883509 := bbase (se 5 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 2883509 = 270329) (by norm_num)
theorem B5767109 : Blo 1800101 5767109 := bbase (se 4 (by rfl) ⟨540666, by rfl⟩ : syracuseStep 5767109 = 1081333) (by norm_num)
theorem B3039221 : Blo 1800101 3039221 := bbase (se 5 (by rfl) ⟨142463, by rfl⟩ : syracuseStep 3039221 = 284927) (by norm_num)
theorem B6078509 : Blo 1800101 6078509 := bstep (se 3 (by rfl) ⟨1139720, by rfl⟩ : syracuseStep 6078509 = 2279441) B2279441
theorem B2433091 : Blo 1800101 2433091 := bstep (se 1 (by rfl) ⟨1824818, by rfl⟩ : syracuseStep 2433091 = 3649637) B3649637
theorem B3039329 : Blo 1800101 3039329 := bstep (se 2 (by rfl) ⟨1139748, by rfl⟩ : syracuseStep 3039329 = 2279497) B2279497
theorem B10256483 : Blo 1800101 10256483 := bstep (se 1 (by rfl) ⟨7692362, by rfl⟩ : syracuseStep 10256483 = 15384725) B15384725
theorem B6078563 : Blo 1800101 6078563 := bstep (se 1 (by rfl) ⟨4558922, by rfl⟩ : syracuseStep 6078563 = 9117845) B9117845
theorem B3039457 : Blo 1800101 3039457 := bstep (se 2 (by rfl) ⟨1139796, by rfl⟩ : syracuseStep 3039457 = 2279593) B2279593
theorem B3080435 : Blo 1800101 3080435 := bstep (se 1 (by rfl) ⟨2310326, by rfl⟩ : syracuseStep 3080435 = 4620653) B4620653
theorem B3039491 : Blo 1800101 3039491 := bstep (se 1 (by rfl) ⟨2279618, by rfl⟩ : syracuseStep 3039491 = 4559237) B4559237
theorem B2564417 : Blo 1800101 2564417 := bstep (se 2 (by rfl) ⟨961656, by rfl⟩ : syracuseStep 2564417 = 1923313) B1923313
theorem B6078833 : Blo 1800101 6078833 := bstep (se 2 (by rfl) ⟨2279562, by rfl⟩ : syracuseStep 6078833 = 4559125) B4559125
theorem B3039619 : Blo 1800101 3039619 := bstep (se 1 (by rfl) ⟨2279714, by rfl⟩ : syracuseStep 3039619 = 4559429) B4559429
theorem B2564497 : Blo 1800101 2564497 := bstep (se 2 (by rfl) ⟨961686, by rfl⟩ : syracuseStep 2564497 = 1923373) B1923373
theorem B5128721 : Blo 1800101 5128721 := bstep (se 2 (by rfl) ⟨1923270, by rfl⟩ : syracuseStep 5128721 = 3846541) B3846541
theorem B3039761 : Blo 1800101 3039761 := bstep (se 2 (by rfl) ⟨1139910, by rfl⟩ : syracuseStep 3039761 = 2279821) B2279821
theorem B9732707 : Blo 1800101 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B3039889 : Blo 1800101 3039889 := bstep (se 2 (by rfl) ⟨1139958, by rfl⟩ : syracuseStep 3039889 = 2279917) B2279917
theorem B3039923 : Blo 1800101 3039923 := bstep (se 1 (by rfl) ⟨2279942, by rfl⟩ : syracuseStep 3039923 = 4559885) B4559885
theorem B5767939 : Blo 1800101 5767939 := bstep (se 1 (by rfl) ⟨4325954, by rfl⟩ : syracuseStep 5767939 = 8651909) B8651909
theorem B3040051 : Blo 1800101 3040051 := bstep (se 1 (by rfl) ⟨2280038, by rfl⟩ : syracuseStep 3040051 = 4560077) B4560077
theorem B2433907 : Blo 1800101 2433907 := bstep (se 1 (by rfl) ⟨1825430, by rfl⟩ : syracuseStep 2433907 = 3650861) B3650861
theorem B6079373 : Blo 1800101 6079373 := bstep (se 3 (by rfl) ⟨1139882, by rfl⟩ : syracuseStep 6079373 = 2279765) B2279765
theorem B2278307 : Blo 1800101 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B8217521 : Blo 1800101 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B3040193 : Blo 1800101 3040193 := bstep (se 2 (by rfl) ⟨1140072, by rfl⟩ : syracuseStep 3040193 = 2280145) B2280145
theorem B2884547 : Blo 1800101 2884547 := bstep (se 1 (by rfl) ⟨2163410, by rfl⟩ : syracuseStep 2884547 = 4326821) B4326821
theorem B6079427 : Blo 1800101 6079427 := bstep (se 1 (by rfl) ⟨4559570, by rfl⟩ : syracuseStep 6079427 = 9119141) B9119141
theorem B5768273 : Blo 1800101 5768273 := bstep (se 2 (by rfl) ⟨2163102, by rfl⟩ : syracuseStep 5768273 = 4326205) B4326205
theorem B2254003 : Blo 1800101 2254003 := bstep (se 1 (by rfl) ⟨1690502, by rfl⟩ : syracuseStep 2254003 = 3381005) B3381005
theorem B6079697 : Blo 1800101 6079697 := bstep (se 2 (by rfl) ⟨2279886, by rfl⟩ : syracuseStep 6079697 = 4559773) B4559773
theorem B22209805 : Blo 1800101 22209805 := bstep (se 3 (by rfl) ⟨4164338, by rfl⟩ : syracuseStep 22209805 = 8328677) B8328677
theorem B5129507 : Blo 1800101 5129507 := bstep (se 1 (by rfl) ⟨3847130, by rfl⟩ : syracuseStep 5129507 = 7694261) B7694261
theorem B6161827 : Blo 1800101 6161827 := bstep (se 1 (by rfl) ⟨4621370, by rfl⟩ : syracuseStep 6161827 = 9242741) B9242741
theorem B9733553 : Blo 1800101 9733553 := bstep (se 2 (by rfl) ⟨3650082, by rfl⟩ : syracuseStep 9733553 = 7300165) B7300165
theorem B4867523 : Blo 1800101 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B11535857 : Blo 1800101 11535857 := bstep (se 2 (by rfl) ⟨4325946, by rfl⟩ : syracuseStep 11535857 = 8651893) B8651893
theorem B7300685 : Blo 1800101 7300685 := bstep (se 3 (by rfl) ⟨1368878, by rfl⟩ : syracuseStep 7300685 = 2737757) B2737757
theorem B2279011 : Blo 1800101 2279011 := bstep (se 1 (by rfl) ⟨1709258, by rfl⟩ : syracuseStep 2279011 = 3418517) B3418517
theorem B5129837 : Blo 1800101 5129837 := bstep (se 3 (by rfl) ⟨961844, by rfl⟩ : syracuseStep 5129837 = 1923689) B1923689
theorem B9733745 : Blo 1800101 9733745 := bstep (se 2 (by rfl) ⟨3650154, by rfl⟩ : syracuseStep 9733745 = 7300309) B7300309
theorem B16647821 : Blo 1800101 16647821 := bstep (se 3 (by rfl) ⟨3121466, by rfl⟩ : syracuseStep 16647821 = 6242933) B6242933
theorem B7693987 : Blo 1800101 7693987 := bstep (se 1 (by rfl) ⟨5770490, by rfl⟩ : syracuseStep 7693987 = 11540981) B11540981
theorem B5129905 : Blo 1800101 5129905 := bstep (se 2 (by rfl) ⟨1923714, by rfl⟩ : syracuseStep 5129905 = 3847429) B3847429
theorem B2025139 : Blo 1800101 2025139 := bstep (se 1 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 2025139 = 3037709) B3037709
theorem B2279107 : Blo 1800101 2279107 := bstep (se 1 (by rfl) ⟨1709330, by rfl⟩ : syracuseStep 2279107 = 3418661) B3418661
theorem B6080237 : Blo 1800101 6080237 := bstep (se 3 (by rfl) ⟨1140044, by rfl⟩ : syracuseStep 6080237 = 2280089) B2280089
theorem B6080291 : Blo 1800101 6080291 := bstep (se 1 (by rfl) ⟨4560218, by rfl⟩ : syracuseStep 6080291 = 9120437) B9120437
theorem B2025283 : Blo 1800101 2025283 := bstep (se 1 (by rfl) ⟨1518962, by rfl⟩ : syracuseStep 2025283 = 3037925) B3037925
theorem B4556675 : Blo 1800101 4556675 := bstep (se 1 (by rfl) ⟨3417506, by rfl⟩ : syracuseStep 4556675 = 6835013) B6835013
theorem B2598851 : Blo 1800101 2598851 := bstep (se 1 (by rfl) ⟨1949138, by rfl⟩ : syracuseStep 2598851 = 3898277) B3898277
theorem B5130179 : Blo 1800101 5130179 := bstep (se 1 (by rfl) ⟨3847634, by rfl⟩ : syracuseStep 5130179 = 7695269) B7695269
theorem B9734093 : Blo 1800101 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B2025427 : Blo 1800101 2025427 := bstep (se 1 (by rfl) ⟨1519070, by rfl⟩ : syracuseStep 2025427 = 3038141) B3038141
theorem B3418129 : Blo 1800101 3418129 := bstep (se 2 (by rfl) ⟨1281798, by rfl⟩ : syracuseStep 3418129 = 2563597) B2563597
theorem B2738225 : Blo 1800101 2738225 := bstep (se 2 (by rfl) ⟨1026834, by rfl⟩ : syracuseStep 2738225 = 2053669) B2053669
theorem B2025571 : Blo 1800101 2025571 := bstep (se 1 (by rfl) ⟨1519178, by rfl⟩ : syracuseStep 2025571 = 3038357) B3038357
theorem B17303665 : Blo 1800101 17303665 := bstep (se 2 (by rfl) ⟨6488874, by rfl⟩ : syracuseStep 17303665 = 12977749) B12977749
theorem B2279603 : Blo 1800101 2279603 := bstep (se 1 (by rfl) ⟨1709702, by rfl⟩ : syracuseStep 2279603 = 3419405) B3419405
theorem B2025715 : Blo 1800101 2025715 := bstep (se 1 (by rfl) ⟨1519286, by rfl⟩ : syracuseStep 2025715 = 3038573) B3038573
theorem B4868365 : Blo 1800101 4868365 := bstep (se 3 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 4868365 = 1825637) B1825637
theorem B4868429 : Blo 1800101 4868429 := bstep (se 3 (by rfl) ⟨912830, by rfl⟩ : syracuseStep 4868429 = 1825661) B1825661
theorem B4327793 : Blo 1800101 4327793 := bstep (se 2 (by rfl) ⟨1622922, by rfl⟩ : syracuseStep 4327793 = 3245845) B3245845
theorem B9120113 : Blo 1800101 9120113 := bstep (se 2 (by rfl) ⟨3420042, by rfl⟩ : syracuseStep 9120113 = 6840085) B6840085
theorem B2025859 : Blo 1800101 2025859 := bstep (se 1 (by rfl) ⟨1519394, by rfl⟩ : syracuseStep 2025859 = 3038789) B3038789
theorem B3246499 : Blo 1800101 3246499 := bstep (se 1 (by rfl) ⟨2434874, by rfl⟩ : syracuseStep 3246499 = 4869749) B4869749
theorem B2026003 : Blo 1800101 2026003 := bstep (se 1 (by rfl) ⟨1519502, by rfl⟩ : syracuseStep 2026003 = 3039005) B3039005
theorem B5474893 : Blo 1800101 5474893 := bstep (se 3 (by rfl) ⟨1026542, by rfl⟩ : syracuseStep 5474893 = 2053085) B2053085
theorem B2738785 : Blo 1800101 2738785 := bstep (se 2 (by rfl) ⟨1027044, by rfl⟩ : syracuseStep 2738785 = 2054089) B2054089
theorem B3844739 : Blo 1800101 3844739 := bstep (se 1 (by rfl) ⟨2883554, by rfl⟩ : syracuseStep 3844739 = 5767109) B5767109
theorem B7023245 : Blo 1800101 7023245 := bstep (se 3 (by rfl) ⟨1316858, by rfl⟩ : syracuseStep 7023245 = 2633717) B2633717
theorem B2026147 : Blo 1800101 2026147 := bstep (se 1 (by rfl) ⟨1519610, by rfl⟩ : syracuseStep 2026147 = 3039221) B3039221
theorem B2738881 : Blo 1800101 2738881 := bstep (se 2 (by rfl) ⟨1027080, by rfl⟩ : syracuseStep 2738881 = 2054161) B2054161
theorem B3844849 : Blo 1800101 3844849 := bstep (se 2 (by rfl) ⟨1441818, by rfl⟩ : syracuseStep 3844849 = 2883637) B2883637
theorem B4557617 : Blo 1800101 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B2026291 : Blo 1800101 2026291 := bstep (se 1 (by rfl) ⟨1519718, by rfl⟩ : syracuseStep 2026291 = 3039437) B3039437
theorem B6835043 : Blo 1800101 6835043 := bstep (se 1 (by rfl) ⟨5126282, by rfl⟩ : syracuseStep 6835043 = 10252565) B10252565
theorem B4557667 : Blo 1800101 4557667 := bstep (se 1 (by rfl) ⟨3418250, by rfl⟩ : syracuseStep 4557667 = 6836501) B6836501
theorem B11537315 : Blo 1800101 11537315 := bstep (se 1 (by rfl) ⟨8652986, by rfl⟩ : syracuseStep 11537315 = 17305973) B17305973
theorem B2026435 : Blo 1800101 2026435 := bstep (se 1 (by rfl) ⟨1519826, by rfl⟩ : syracuseStep 2026435 = 3039653) B3039653
theorem B4557809 : Blo 1800101 4557809 := bstep (se 2 (by rfl) ⟨1709178, by rfl⟩ : syracuseStep 4557809 = 3418357) B3418357
theorem B11693069 : Blo 1800101 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B4328483 : Blo 1800101 4328483 := bstep (se 1 (by rfl) ⟨3246362, by rfl⟩ : syracuseStep 4328483 = 6492725) B6492725
theorem B3419185 : Blo 1800101 3419185 := bstep (se 2 (by rfl) ⟨1282194, by rfl⟩ : syracuseStep 3419185 = 2564389) B2564389
theorem B4385873 : Blo 1800101 4385873 := bstep (se 2 (by rfl) ⟨1644702, by rfl⟩ : syracuseStep 4385873 = 3289405) B3289405
theorem B2026579 : Blo 1800101 2026579 := bstep (se 1 (by rfl) ⟨1519934, by rfl⟩ : syracuseStep 2026579 = 3039869) B3039869
theorem B5770349 : Blo 1800101 5770349 := bstep (se 3 (by rfl) ⟨1081940, by rfl⟩ : syracuseStep 5770349 = 2163881) B2163881
theorem B7302257 : Blo 1800101 7302257 := bstep (se 2 (by rfl) ⟨2738346, by rfl⟩ : syracuseStep 7302257 = 5476693) B5476693
theorem B2026723 : Blo 1800101 2026723 := bstep (se 1 (by rfl) ⟨1520042, by rfl⟩ : syracuseStep 2026723 = 3040085) B3040085
theorem B3419587 : Blo 1800101 3419587 := bstep (se 1 (by rfl) ⟨2564690, by rfl⟩ : syracuseStep 3419587 = 5129381) B5129381
theorem B14806469 : Blo 1800101 14806469 := bstep (se 4 (by rfl) ⟨1388106, by rfl⟩ : syracuseStep 14806469 = 2776213) B2776213
theorem B6835697 : Blo 1800101 6835697 := bstep (se 2 (by rfl) ⟨2563386, by rfl⟩ : syracuseStep 6835697 = 5126773) B5126773
theorem B3419633 : Blo 1800101 3419633 := bstep (se 2 (by rfl) ⟨1282362, by rfl⟩ : syracuseStep 3419633 = 2564725) B2564725
theorem B4050449 : Blo 1800101 4050449 := bstep (se 2 (by rfl) ⟨1518918, by rfl⟩ : syracuseStep 4050449 = 3037837) B3037837
theorem B4050467 : Blo 1800101 4050467 := bstep (se 1 (by rfl) ⟨3037850, by rfl⟩ : syracuseStep 4050467 = 6075701) B6075701
theorem B9735821 : Blo 1800101 9735821 := bstep (se 3 (by rfl) ⟨1825466, by rfl⟩ : syracuseStep 9735821 = 3650933) B3650933
theorem B3419921 : Blo 1800101 3419921 := bstep (se 2 (by rfl) ⟨1282470, by rfl⟩ : syracuseStep 3419921 = 2564941) B2564941
theorem B4050737 : Blo 1800101 4050737 := bstep (se 2 (by rfl) ⟨1519026, by rfl⟩ : syracuseStep 4050737 = 3038053) B3038053
theorem B4050755 : Blo 1800101 4050755 := bstep (se 1 (by rfl) ⟨3038066, by rfl⟩ : syracuseStep 4050755 = 6076133) B6076133
theorem B4558801 : Blo 1800101 4558801 := bstep (se 2 (by rfl) ⟨1709550, by rfl⟩ : syracuseStep 4558801 = 3419101) B3419101
theorem B4051025 : Blo 1800101 4051025 := bstep (se 2 (by rfl) ⟨1519134, by rfl⟩ : syracuseStep 4051025 = 3038269) B3038269
theorem B4051043 : Blo 1800101 4051043 := bstep (se 1 (by rfl) ⟨3038282, by rfl⟩ : syracuseStep 4051043 = 6076565) B6076565
theorem B7794893 : Blo 1800101 7794893 := bstep (se 3 (by rfl) ⟨1461542, by rfl⟩ : syracuseStep 7794893 = 2923085) B2923085
theorem B4559075 : Blo 1800101 4559075 := bstep (se 1 (by rfl) ⟨3419306, by rfl⟩ : syracuseStep 4559075 = 6838613) B6838613
theorem B4051313 : Blo 1800101 4051313 := bstep (se 2 (by rfl) ⟨1519242, by rfl⟩ : syracuseStep 4051313 = 3038485) B3038485
theorem B4051331 : Blo 1800101 4051331 := bstep (se 1 (by rfl) ⟨3038498, by rfl⟩ : syracuseStep 4051331 = 6076997) B6076997
theorem B4559267 : Blo 1800101 4559267 := bstep (se 1 (by rfl) ⟨3419450, by rfl⟩ : syracuseStep 4559267 = 6838901) B6838901
theorem B11539057 : Blo 1800101 11539057 := bstep (se 2 (by rfl) ⟨4327146, by rfl⟩ : syracuseStep 11539057 = 8654293) B8654293
theorem B4051601 : Blo 1800101 4051601 := bstep (se 2 (by rfl) ⟨1519350, by rfl⟩ : syracuseStep 4051601 = 3038701) B3038701
theorem B4051619 : Blo 1800101 4051619 := bstep (se 1 (by rfl) ⟨3038714, by rfl⟩ : syracuseStep 4051619 = 6077429) B6077429
theorem B5001905 : Blo 1800101 5001905 := bstep (se 2 (by rfl) ⟨1875714, by rfl⟩ : syracuseStep 5001905 = 3751429) B3751429
theorem B3846865 : Blo 1800101 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B6247171 : Blo 1800101 6247171 := bstep (se 1 (by rfl) ⟨4685378, by rfl⟩ : syracuseStep 6247171 = 9370757) B9370757
theorem B5624657 : Blo 1800101 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B2700161 : Blo 1800101 2700161 := bstep (se 2 (by rfl) ⟨1012560, by rfl⟩ : syracuseStep 2700161 = 2025121) B2025121
theorem B2700179 : Blo 1800101 2700179 := bstep (se 1 (by rfl) ⟨2025134, by rfl⟩ : syracuseStep 2700179 = 4050269) B4050269
theorem B6837155 : Blo 1800101 6837155 := bstep (se 1 (by rfl) ⟨5127866, by rfl⟩ : syracuseStep 6837155 = 10255733) B10255733
theorem B2700209 : Blo 1800101 2700209 := bstep (se 2 (by rfl) ⟨1012578, by rfl⟩ : syracuseStep 2700209 = 2025157) B2025157
theorem B6837169 : Blo 1800101 6837169 := bstep (se 2 (by rfl) ⟨2563938, by rfl⟩ : syracuseStep 6837169 = 5127877) B5127877
theorem B4051889 : Blo 1800101 4051889 := bstep (se 2 (by rfl) ⟨1519458, by rfl⟩ : syracuseStep 4051889 = 3038917) B3038917
theorem B2700227 : Blo 1800101 2700227 := bstep (se 1 (by rfl) ⟨2025170, by rfl⟩ : syracuseStep 2700227 = 4050341) B4050341
theorem B4051907 : Blo 1800101 4051907 := bstep (se 1 (by rfl) ⟨3038930, by rfl⟩ : syracuseStep 4051907 = 6077861) B6077861
theorem B2700257 : Blo 1800101 2700257 := bstep (se 2 (by rfl) ⟨1012596, by rfl⟩ : syracuseStep 2700257 = 2025193) B2025193
theorem B6075377 : Blo 1800101 6075377 := bstep (se 2 (by rfl) ⟨2278266, by rfl⟩ : syracuseStep 6075377 = 4556533) B4556533
theorem B2700275 : Blo 1800101 2700275 := bstep (se 1 (by rfl) ⟨2025206, by rfl⟩ : syracuseStep 2700275 = 4050413) B4050413
theorem B2700305 : Blo 1800101 2700305 := bstep (se 2 (by rfl) ⟨1012614, by rfl⟩ : syracuseStep 2700305 = 2025229) B2025229
theorem B2700323 : Blo 1800101 2700323 := bstep (se 1 (by rfl) ⟨2025242, by rfl⟩ : syracuseStep 2700323 = 4050485) B4050485
theorem B2700353 : Blo 1800101 2700353 := bstep (se 2 (by rfl) ⟨1012632, by rfl⟩ : syracuseStep 2700353 = 2025265) B2025265
theorem B2700371 : Blo 1800101 2700371 := bstep (se 1 (by rfl) ⟨2025278, by rfl⟩ : syracuseStep 2700371 = 4050557) B4050557
theorem B3847267 : Blo 1800101 3847267 := bstep (se 1 (by rfl) ⟨2885450, by rfl⟩ : syracuseStep 3847267 = 5770901) B5770901
theorem B2700401 : Blo 1800101 2700401 := bstep (se 2 (by rfl) ⟨1012650, by rfl⟩ : syracuseStep 2700401 = 2025301) B2025301
theorem B2700419 : Blo 1800101 2700419 := bstep (se 1 (by rfl) ⟨2025314, by rfl⟩ : syracuseStep 2700419 = 4050629) B4050629
theorem B2700449 : Blo 1800101 2700449 := bstep (se 2 (by rfl) ⟨1012668, by rfl⟩ : syracuseStep 2700449 = 2025337) B2025337
theorem B2700467 : Blo 1800101 2700467 := bstep (se 1 (by rfl) ⟨2025350, by rfl⟩ : syracuseStep 2700467 = 4050701) B4050701
theorem B2700497 : Blo 1800101 2700497 := bstep (se 2 (by rfl) ⟨1012686, by rfl⟩ : syracuseStep 2700497 = 2025373) B2025373
theorem B4052177 : Blo 1800101 4052177 := bstep (se 2 (by rfl) ⟨1519566, by rfl⟩ : syracuseStep 4052177 = 3039133) B3039133
theorem B2700515 : Blo 1800101 2700515 := bstep (se 1 (by rfl) ⟨2025386, by rfl⟩ : syracuseStep 2700515 = 4050773) B4050773
theorem B4052195 : Blo 1800101 4052195 := bstep (se 1 (by rfl) ⟨3039146, by rfl⟩ : syracuseStep 4052195 = 6078293) B6078293
theorem B2700545 : Blo 1800101 2700545 := bstep (se 2 (by rfl) ⟨1012704, by rfl⟩ : syracuseStep 2700545 = 2025409) B2025409
theorem B2700563 : Blo 1800101 2700563 := bstep (se 1 (by rfl) ⟨2025422, by rfl⟩ : syracuseStep 2700563 = 4050845) B4050845
theorem B1922339 : Blo 1800101 1922339 := bstep (se 1 (by rfl) ⟨1441754, by rfl⟩ : syracuseStep 1922339 = 2883509) B2883509
theorem B2700593 : Blo 1800101 2700593 := bstep (se 2 (by rfl) ⟨1012722, by rfl⟩ : syracuseStep 2700593 = 2025445) B2025445
theorem B9114929 : Blo 1800101 9114929 := bstep (se 2 (by rfl) ⟨3418098, by rfl⟩ : syracuseStep 9114929 = 6836197) B6836197
theorem B2700611 : Blo 1800101 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B4560209 : Blo 1800101 4560209 := bstep (se 2 (by rfl) ⟨1710078, by rfl⟩ : syracuseStep 4560209 = 3420157) B3420157
theorem B2700641 : Blo 1800101 2700641 := bstep (se 2 (by rfl) ⟨1012740, by rfl⟩ : syracuseStep 2700641 = 2025481) B2025481
theorem B2700659 : Blo 1800101 2700659 := bstep (se 1 (by rfl) ⟨2025494, by rfl⟩ : syracuseStep 2700659 = 4050989) B4050989
theorem B4560259 : Blo 1800101 4560259 := bstep (se 1 (by rfl) ⟨3420194, by rfl⟩ : syracuseStep 4560259 = 6840389) B6840389
theorem B7689613 : Blo 1800101 7689613 := bstep (se 3 (by rfl) ⟨1441802, by rfl⟩ : syracuseStep 7689613 = 2883605) B2883605
theorem B2700689 : Blo 1800101 2700689 := bstep (se 2 (by rfl) ⟨1012758, by rfl⟩ : syracuseStep 2700689 = 2025517) B2025517
theorem B2700707 : Blo 1800101 2700707 := bstep (se 1 (by rfl) ⟨2025530, by rfl⟩ : syracuseStep 2700707 = 4051061) B4051061
theorem B2700737 : Blo 1800101 2700737 := bstep (se 2 (by rfl) ⟨1012776, by rfl⟩ : syracuseStep 2700737 = 2025553) B2025553
theorem B2700755 : Blo 1800101 2700755 := bstep (se 1 (by rfl) ⟨2025566, by rfl⟩ : syracuseStep 2700755 = 4051133) B4051133
theorem B2700785 : Blo 1800101 2700785 := bstep (se 2 (by rfl) ⟨1012794, by rfl⟩ : syracuseStep 2700785 = 2025589) B2025589
theorem B4052465 : Blo 1800101 4052465 := bstep (se 2 (by rfl) ⟨1519674, by rfl⟩ : syracuseStep 4052465 = 3039349) B3039349
theorem B2700803 : Blo 1800101 2700803 := bstep (se 1 (by rfl) ⟨2025602, by rfl⟩ : syracuseStep 2700803 = 4051205) B4051205
theorem B4052483 : Blo 1800101 4052483 := bstep (se 1 (by rfl) ⟨3039362, by rfl⟩ : syracuseStep 4052483 = 6078725) B6078725
theorem B6075917 : Blo 1800101 6075917 := bstep (se 3 (by rfl) ⟨1139234, by rfl⟩ : syracuseStep 6075917 = 2278469) B2278469
theorem B2700833 : Blo 1800101 2700833 := bstep (se 2 (by rfl) ⟨1012812, by rfl⟩ : syracuseStep 2700833 = 2025625) B2025625
theorem B2700851 : Blo 1800101 2700851 := bstep (se 1 (by rfl) ⟨2025638, by rfl⟩ : syracuseStep 2700851 = 4051277) B4051277
theorem B6075971 : Blo 1800101 6075971 := bstep (se 1 (by rfl) ⟨4556978, by rfl⟩ : syracuseStep 6075971 = 9113957) B9113957
theorem B11859533 : Blo 1800101 11859533 := bstep (se 3 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 11859533 = 4447325) B4447325
theorem B2700881 : Blo 1800101 2700881 := bstep (se 2 (by rfl) ⟨1012830, by rfl⟩ : syracuseStep 2700881 = 2025661) B2025661
theorem B2700899 : Blo 1800101 2700899 := bstep (se 1 (by rfl) ⟨2025674, by rfl⟩ : syracuseStep 2700899 = 4051349) B4051349
theorem B2700929 : Blo 1800101 2700929 := bstep (se 2 (by rfl) ⟨1012848, by rfl⟩ : syracuseStep 2700929 = 2025697) B2025697
theorem B2700947 : Blo 1800101 2700947 := bstep (se 1 (by rfl) ⟨2025710, by rfl⟩ : syracuseStep 2700947 = 4051421) B4051421
theorem B2700977 : Blo 1800101 2700977 := bstep (se 2 (by rfl) ⟨1012866, by rfl⟩ : syracuseStep 2700977 = 2025733) B2025733
theorem B2700995 : Blo 1800101 2700995 := bstep (se 1 (by rfl) ⟨2025746, by rfl⟩ : syracuseStep 2700995 = 4051493) B4051493
theorem B2701025 : Blo 1800101 2701025 := bstep (se 2 (by rfl) ⟨1012884, by rfl⟩ : syracuseStep 2701025 = 2025769) B2025769
theorem B2701043 : Blo 1800101 2701043 := bstep (se 1 (by rfl) ⟨2025782, by rfl⟩ : syracuseStep 2701043 = 4051565) B4051565
theorem B2701073 : Blo 1800101 2701073 := bstep (se 2 (by rfl) ⟨1012902, by rfl⟩ : syracuseStep 2701073 = 2025805) B2025805
theorem B4052753 : Blo 1800101 4052753 := bstep (se 2 (by rfl) ⟨1519782, by rfl⟩ : syracuseStep 4052753 = 3039565) B3039565
theorem B2701091 : Blo 1800101 2701091 := bstep (se 1 (by rfl) ⟨2025818, by rfl⟩ : syracuseStep 2701091 = 4051637) B4051637
theorem B4052771 : Blo 1800101 4052771 := bstep (se 1 (by rfl) ⟨3039578, by rfl⟩ : syracuseStep 4052771 = 6079157) B6079157
theorem B2701121 : Blo 1800101 2701121 := bstep (se 2 (by rfl) ⟨1012920, by rfl⟩ : syracuseStep 2701121 = 2025841) B2025841
theorem B6076241 : Blo 1800101 6076241 := bstep (se 2 (by rfl) ⟨2278590, by rfl⟩ : syracuseStep 6076241 = 4557181) B4557181
theorem B2701139 : Blo 1800101 2701139 := bstep (se 1 (by rfl) ⟨2025854, by rfl⟩ : syracuseStep 2701139 = 4051709) B4051709
theorem B2701169 : Blo 1800101 2701169 := bstep (se 2 (by rfl) ⟨1012938, by rfl⟩ : syracuseStep 2701169 = 2025877) B2025877
theorem B2701187 : Blo 1800101 2701187 := bstep (se 1 (by rfl) ⟨2025890, by rfl⟩ : syracuseStep 2701187 = 4051781) B4051781
theorem B7796621 : Blo 1800101 7796621 := bstep (se 3 (by rfl) ⟨1461866, by rfl⟩ : syracuseStep 7796621 = 2923733) B2923733
theorem B12662669 : Blo 1800101 12662669 := bstep (se 3 (by rfl) ⟨2374250, by rfl⟩ : syracuseStep 12662669 = 4748501) B4748501
theorem B2701217 : Blo 1800101 2701217 := bstep (se 2 (by rfl) ⟨1012956, by rfl⟩ : syracuseStep 2701217 = 2025913) B2025913
theorem B6158243 : Blo 1800101 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B1800115 : Blo 1800101 1800115 := bstep (se 1 (by rfl) ⟨1350086, by rfl⟩ : syracuseStep 1800115 = 2700173) B2700173
theorem B2701235 : Blo 1800101 2701235 := bstep (se 1 (by rfl) ⟨2025926, by rfl⟩ : syracuseStep 2701235 = 4051853) B4051853
theorem B1800131 : Blo 1800101 1800131 := bstep (se 1 (by rfl) ⟨1350098, by rfl⟩ : syracuseStep 1800131 = 2700197) B2700197
theorem B2701265 : Blo 1800101 2701265 := bstep (se 2 (by rfl) ⟨1012974, by rfl⟩ : syracuseStep 2701265 = 2025949) B2025949
theorem B1800147 : Blo 1800101 1800147 := bstep (se 1 (by rfl) ⟨1350110, by rfl⟩ : syracuseStep 1800147 = 2700221) B2700221
theorem B1800163 : Blo 1800101 1800163 := bstep (se 1 (by rfl) ⟨1350122, by rfl⟩ : syracuseStep 1800163 = 2700245) B2700245
theorem B7690211 : Blo 1800101 7690211 := bstep (se 1 (by rfl) ⟨5767658, by rfl⟩ : syracuseStep 7690211 = 11535317) B11535317
theorem B2701283 : Blo 1800101 2701283 := bstep (se 1 (by rfl) ⟨2025962, by rfl⟩ : syracuseStep 2701283 = 4051925) B4051925
theorem B1800179 : Blo 1800101 1800179 := bstep (se 1 (by rfl) ⟨1350134, by rfl⟩ : syracuseStep 1800179 = 2700269) B2700269
theorem B2701313 : Blo 1800101 2701313 := bstep (se 2 (by rfl) ⟨1012992, by rfl⟩ : syracuseStep 2701313 = 2025985) B2025985
theorem B1800195 : Blo 1800101 1800195 := bstep (se 1 (by rfl) ⟨1350146, by rfl⟩ : syracuseStep 1800195 = 2700293) B2700293
theorem B1800211 : Blo 1800101 1800211 := bstep (se 1 (by rfl) ⟨1350158, by rfl⟩ : syracuseStep 1800211 = 2700317) B2700317
theorem B2701331 : Blo 1800101 2701331 := bstep (se 1 (by rfl) ⟨2025998, by rfl⟩ : syracuseStep 2701331 = 4051997) B4051997
theorem B1800227 : Blo 1800101 1800227 := bstep (se 1 (by rfl) ⟨1350170, by rfl⟩ : syracuseStep 1800227 = 2700341) B2700341
theorem B2701361 : Blo 1800101 2701361 := bstep (se 2 (by rfl) ⟨1013010, by rfl⟩ : syracuseStep 2701361 = 2026021) B2026021
theorem B4053041 : Blo 1800101 4053041 := bstep (se 2 (by rfl) ⟨1519890, by rfl⟩ : syracuseStep 4053041 = 3039781) B3039781
theorem B1800243 : Blo 1800101 1800243 := bstep (se 1 (by rfl) ⟨1350182, by rfl⟩ : syracuseStep 1800243 = 2700365) B2700365
theorem B1800259 : Blo 1800101 1800259 := bstep (se 1 (by rfl) ⟨1350194, by rfl⟩ : syracuseStep 1800259 = 2700389) B2700389
theorem B2701379 : Blo 1800101 2701379 := bstep (se 1 (by rfl) ⟨2026034, by rfl⟩ : syracuseStep 2701379 = 4052069) B4052069
theorem B4053059 : Blo 1800101 4053059 := bstep (se 1 (by rfl) ⟨3039794, by rfl⟩ : syracuseStep 4053059 = 6079589) B6079589
theorem B1800275 : Blo 1800101 1800275 := bstep (se 1 (by rfl) ⟨1350206, by rfl⟩ : syracuseStep 1800275 = 2700413) B2700413
theorem B1800291 : Blo 1800101 1800291 := bstep (se 1 (by rfl) ⟨1350218, by rfl⟩ : syracuseStep 1800291 = 2700437) B2700437
theorem B2701409 : Blo 1800101 2701409 := bstep (se 2 (by rfl) ⟨1013028, by rfl⟩ : syracuseStep 2701409 = 2026057) B2026057
theorem B1800307 : Blo 1800101 1800307 := bstep (se 1 (by rfl) ⟨1350230, by rfl⟩ : syracuseStep 1800307 = 2700461) B2700461
theorem B2701427 : Blo 1800101 2701427 := bstep (se 1 (by rfl) ⟨2026070, by rfl⟩ : syracuseStep 2701427 = 4052141) B4052141
theorem B1800323 : Blo 1800101 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B2701457 : Blo 1800101 2701457 := bstep (se 2 (by rfl) ⟨1013046, by rfl⟩ : syracuseStep 2701457 = 2026093) B2026093
theorem B1800339 : Blo 1800101 1800339 := bstep (se 1 (by rfl) ⟨1350254, by rfl⟩ : syracuseStep 1800339 = 2700509) B2700509
theorem B1800355 : Blo 1800101 1800355 := bstep (se 1 (by rfl) ⟨1350266, by rfl⟩ : syracuseStep 1800355 = 2700533) B2700533
theorem B2701475 : Blo 1800101 2701475 := bstep (se 1 (by rfl) ⟨2026106, by rfl⟩ : syracuseStep 2701475 = 4052213) B4052213
theorem B1800371 : Blo 1800101 1800371 := bstep (se 1 (by rfl) ⟨1350278, by rfl⟩ : syracuseStep 1800371 = 2700557) B2700557
theorem B2701505 : Blo 1800101 2701505 := bstep (se 2 (by rfl) ⟨1013064, by rfl⟩ : syracuseStep 2701505 = 2026129) B2026129
theorem B1800387 : Blo 1800101 1800387 := bstep (se 1 (by rfl) ⟨1350290, by rfl⟩ : syracuseStep 1800387 = 2700581) B2700581
theorem B1800403 : Blo 1800101 1800403 := bstep (se 1 (by rfl) ⟨1350302, by rfl⟩ : syracuseStep 1800403 = 2700605) B2700605
theorem B2701523 : Blo 1800101 2701523 := bstep (se 1 (by rfl) ⟨2026142, by rfl⟩ : syracuseStep 2701523 = 4052285) B4052285
theorem B1800419 : Blo 1800101 1800419 := bstep (se 1 (by rfl) ⟨1350314, by rfl⟩ : syracuseStep 1800419 = 2700629) B2700629
theorem B2701553 : Blo 1800101 2701553 := bstep (se 2 (by rfl) ⟨1013082, by rfl⟩ : syracuseStep 2701553 = 2026165) B2026165
theorem B1800435 : Blo 1800101 1800435 := bstep (se 1 (by rfl) ⟨1350326, by rfl⟩ : syracuseStep 1800435 = 2700653) B2700653
theorem B1800451 : Blo 1800101 1800451 := bstep (se 1 (by rfl) ⟨1350338, by rfl⟩ : syracuseStep 1800451 = 2700677) B2700677
theorem B2701571 : Blo 1800101 2701571 := bstep (se 1 (by rfl) ⟨2026178, by rfl⟩ : syracuseStep 2701571 = 4052357) B4052357
theorem B1800467 : Blo 1800101 1800467 := bstep (se 1 (by rfl) ⟨1350350, by rfl⟩ : syracuseStep 1800467 = 2700701) B2700701
theorem B2701601 : Blo 1800101 2701601 := bstep (se 2 (by rfl) ⟨1013100, by rfl⟩ : syracuseStep 2701601 = 2026201) B2026201
theorem B1800483 : Blo 1800101 1800483 := bstep (se 1 (by rfl) ⟨1350362, by rfl⟩ : syracuseStep 1800483 = 2700725) B2700725
theorem B1800499 : Blo 1800101 1800499 := bstep (se 1 (by rfl) ⟨1350374, by rfl⟩ : syracuseStep 1800499 = 2700749) B2700749
theorem B2701619 : Blo 1800101 2701619 := bstep (se 1 (by rfl) ⟨2026214, by rfl⟩ : syracuseStep 2701619 = 4052429) B4052429
theorem B1800515 : Blo 1800101 1800515 := bstep (se 1 (by rfl) ⟨1350386, by rfl⟩ : syracuseStep 1800515 = 2700773) B2700773
theorem B2701649 : Blo 1800101 2701649 := bstep (se 2 (by rfl) ⟨1013118, by rfl⟩ : syracuseStep 2701649 = 2026237) B2026237
theorem B4053329 : Blo 1800101 4053329 := bstep (se 2 (by rfl) ⟨1519998, by rfl⟩ : syracuseStep 4053329 = 3039997) B3039997
theorem B1800531 : Blo 1800101 1800531 := bstep (se 1 (by rfl) ⟨1350398, by rfl⟩ : syracuseStep 1800531 = 2700797) B2700797
theorem B1800547 : Blo 1800101 1800547 := bstep (se 1 (by rfl) ⟨1350410, by rfl⟩ : syracuseStep 1800547 = 2700821) B2700821
theorem B2701667 : Blo 1800101 2701667 := bstep (se 1 (by rfl) ⟨2026250, by rfl⟩ : syracuseStep 2701667 = 4052501) B4052501
theorem B6838627 : Blo 1800101 6838627 := bstep (se 1 (by rfl) ⟨5128970, by rfl⟩ : syracuseStep 6838627 = 10257941) B10257941
theorem B4053347 : Blo 1800101 4053347 := bstep (se 1 (by rfl) ⟨3040010, by rfl⟩ : syracuseStep 4053347 = 6080021) B6080021
theorem B6076781 : Blo 1800101 6076781 := bstep (se 3 (by rfl) ⟨1139396, by rfl⟩ : syracuseStep 6076781 = 2278793) B2278793
theorem B1800563 : Blo 1800101 1800563 := bstep (se 1 (by rfl) ⟨1350422, by rfl⟩ : syracuseStep 1800563 = 2700845) B2700845
theorem B2701697 : Blo 1800101 2701697 := bstep (se 2 (by rfl) ⟨1013136, by rfl⟩ : syracuseStep 2701697 = 2026273) B2026273
theorem B1800579 : Blo 1800101 1800579 := bstep (se 1 (by rfl) ⟨1350434, by rfl⟩ : syracuseStep 1800579 = 2700869) B2700869
theorem B3651971 : Blo 1800101 3651971 := bstep (se 1 (by rfl) ⟨2738978, by rfl⟩ : syracuseStep 3651971 = 5477957) B5477957
theorem B11852173 : Blo 1800101 11852173 := bstep (se 3 (by rfl) ⟨2222282, by rfl⟩ : syracuseStep 11852173 = 4444565) B4444565
theorem B1800595 : Blo 1800101 1800595 := bstep (se 1 (by rfl) ⟨1350446, by rfl⟩ : syracuseStep 1800595 = 2700893) B2700893
theorem B2701715 : Blo 1800101 2701715 := bstep (se 1 (by rfl) ⟨2026286, by rfl⟩ : syracuseStep 2701715 = 4052573) B4052573
theorem B6076835 : Blo 1800101 6076835 := bstep (se 1 (by rfl) ⟨4557626, by rfl⟩ : syracuseStep 6076835 = 9115253) B9115253
theorem B1800611 : Blo 1800101 1800611 := bstep (se 1 (by rfl) ⟨1350458, by rfl⟩ : syracuseStep 1800611 = 2700917) B2700917
theorem B2701745 : Blo 1800101 2701745 := bstep (se 2 (by rfl) ⟨1013154, by rfl⟩ : syracuseStep 2701745 = 2026309) B2026309
theorem B1800627 : Blo 1800101 1800627 := bstep (se 1 (by rfl) ⟨1350470, by rfl⟩ : syracuseStep 1800627 = 2700941) B2700941
theorem B1800643 : Blo 1800101 1800643 := bstep (se 1 (by rfl) ⟨1350482, by rfl⟩ : syracuseStep 1800643 = 2700965) B2700965
theorem B2701763 : Blo 1800101 2701763 := bstep (se 1 (by rfl) ⟨2026322, by rfl⟩ : syracuseStep 2701763 = 4052645) B4052645
theorem B1800659 : Blo 1800101 1800659 := bstep (se 1 (by rfl) ⟨1350494, by rfl⟩ : syracuseStep 1800659 = 2700989) B2700989
theorem B5200337 : Blo 1800101 5200337 := bstep (se 2 (by rfl) ⟨1950126, by rfl⟩ : syracuseStep 5200337 = 3900253) B3900253
theorem B2701793 : Blo 1800101 2701793 := bstep (se 2 (by rfl) ⟨1013172, by rfl⟩ : syracuseStep 2701793 = 2026345) B2026345
theorem B1800675 : Blo 1800101 1800675 := bstep (se 1 (by rfl) ⟨1350506, by rfl⟩ : syracuseStep 1800675 = 2701013) B2701013
theorem B1800691 : Blo 1800101 1800691 := bstep (se 1 (by rfl) ⟨1350518, by rfl⟩ : syracuseStep 1800691 = 2701037) B2701037
theorem B2701811 : Blo 1800101 2701811 := bstep (se 1 (by rfl) ⟨2026358, by rfl⟩ : syracuseStep 2701811 = 4052717) B4052717
theorem B1800707 : Blo 1800101 1800707 := bstep (se 1 (by rfl) ⟨1350530, by rfl⟩ : syracuseStep 1800707 = 2701061) B2701061
theorem B11541005 : Blo 1800101 11541005 := bstep (se 3 (by rfl) ⟨2163938, by rfl⟩ : syracuseStep 11541005 = 4327877) B4327877
theorem B2701841 : Blo 1800101 2701841 := bstep (se 2 (by rfl) ⟨1013190, by rfl⟩ : syracuseStep 2701841 = 2026381) B2026381
theorem B1800723 : Blo 1800101 1800723 := bstep (se 1 (by rfl) ⟨1350542, by rfl⟩ : syracuseStep 1800723 = 2701085) B2701085
theorem B3037729 : Blo 1800101 3037729 := bstep (se 2 (by rfl) ⟨1139148, by rfl⟩ : syracuseStep 3037729 = 2278297) B2278297
theorem B1800739 : Blo 1800101 1800739 := bstep (se 1 (by rfl) ⟨1350554, by rfl⟩ : syracuseStep 1800739 = 2701109) B2701109
theorem B2701859 : Blo 1800101 2701859 := bstep (se 1 (by rfl) ⟨2026394, by rfl⟩ : syracuseStep 2701859 = 4052789) B4052789
theorem B1800755 : Blo 1800101 1800755 := bstep (se 1 (by rfl) ⟨1350566, by rfl⟩ : syracuseStep 1800755 = 2701133) B2701133
theorem B2701889 : Blo 1800101 2701889 := bstep (se 2 (by rfl) ⟨1013208, by rfl⟩ : syracuseStep 2701889 = 2026417) B2026417
theorem B3037763 : Blo 1800101 3037763 := bstep (se 1 (by rfl) ⟨2278322, by rfl⟩ : syracuseStep 3037763 = 4556645) B4556645
theorem B1800771 : Blo 1800101 1800771 := bstep (se 1 (by rfl) ⟨1350578, by rfl⟩ : syracuseStep 1800771 = 2701157) B2701157
theorem B1800787 : Blo 1800101 1800787 := bstep (se 1 (by rfl) ⟨1350590, by rfl⟩ : syracuseStep 1800787 = 2701181) B2701181
theorem B2701907 : Blo 1800101 2701907 := bstep (se 1 (by rfl) ⟨2026430, by rfl⟩ : syracuseStep 2701907 = 4052861) B4052861
theorem B1800803 : Blo 1800101 1800803 := bstep (se 1 (by rfl) ⟨1350602, by rfl⟩ : syracuseStep 1800803 = 2701205) B2701205
theorem B2701937 : Blo 1800101 2701937 := bstep (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) B2026453
theorem B1800819 : Blo 1800101 1800819 := bstep (se 1 (by rfl) ⟨1350614, by rfl⟩ : syracuseStep 1800819 = 2701229) B2701229
theorem B1800835 : Blo 1800101 1800835 := bstep (se 1 (by rfl) ⟨1350626, by rfl⟩ : syracuseStep 1800835 = 2701253) B2701253
theorem B2701955 : Blo 1800101 2701955 := bstep (se 1 (by rfl) ⟨2026466, by rfl⟩ : syracuseStep 2701955 = 4052933) B4052933
theorem B1800851 : Blo 1800101 1800851 := bstep (se 1 (by rfl) ⟨1350638, by rfl⟩ : syracuseStep 1800851 = 2701277) B2701277
theorem B2701985 : Blo 1800101 2701985 := bstep (se 2 (by rfl) ⟨1013244, by rfl⟩ : syracuseStep 2701985 = 2026489) B2026489
theorem B1800867 : Blo 1800101 1800867 := bstep (se 1 (by rfl) ⟨1350650, by rfl⟩ : syracuseStep 1800867 = 2701301) B2701301
theorem B10255025 : Blo 1800101 10255025 := bstep (se 2 (by rfl) ⟨3845634, by rfl⟩ : syracuseStep 10255025 = 7691269) B7691269
theorem B6077105 : Blo 1800101 6077105 := bstep (se 2 (by rfl) ⟨2278914, by rfl⟩ : syracuseStep 6077105 = 4557829) B4557829
theorem B1800883 : Blo 1800101 1800883 := bstep (se 1 (by rfl) ⟨1350662, by rfl⟩ : syracuseStep 1800883 = 2701325) B2701325
theorem B2702003 : Blo 1800101 2702003 := bstep (se 1 (by rfl) ⟨2026502, by rfl⟩ : syracuseStep 2702003 = 4053005) B4053005
theorem B3037891 : Blo 1800101 3037891 := bstep (se 1 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 3037891 = 4556837) B4556837
theorem B1800899 : Blo 1800101 1800899 := bstep (se 1 (by rfl) ⟨1350674, by rfl⟩ : syracuseStep 1800899 = 2701349) B2701349
theorem B2702033 : Blo 1800101 2702033 := bstep (se 2 (by rfl) ⟨1013262, by rfl⟩ : syracuseStep 2702033 = 2026525) B2026525
theorem B1800915 : Blo 1800101 1800915 := bstep (se 1 (by rfl) ⟨1350686, by rfl⟩ : syracuseStep 1800915 = 2701373) B2701373
theorem B9116387 : Blo 1800101 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B1800931 : Blo 1800101 1800931 := bstep (se 1 (by rfl) ⟨1350698, by rfl⟩ : syracuseStep 1800931 = 2701397) B2701397
theorem B2702051 : Blo 1800101 2702051 := bstep (se 1 (by rfl) ⟨2026538, by rfl⟩ : syracuseStep 2702051 = 4053077) B4053077
theorem B1800947 : Blo 1800101 1800947 := bstep (se 1 (by rfl) ⟨1350710, by rfl⟩ : syracuseStep 1800947 = 2701421) B2701421
theorem B2702081 : Blo 1800101 2702081 := bstep (se 2 (by rfl) ⟨1013280, by rfl⟩ : syracuseStep 2702081 = 2026561) B2026561
theorem B1800963 : Blo 1800101 1800963 := bstep (se 1 (by rfl) ⟨1350722, by rfl⟩ : syracuseStep 1800963 = 2701445) B2701445
theorem B1800979 : Blo 1800101 1800979 := bstep (se 1 (by rfl) ⟨1350734, by rfl⟩ : syracuseStep 1800979 = 2701469) B2701469
theorem B2702099 : Blo 1800101 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B1800995 : Blo 1800101 1800995 := bstep (se 1 (by rfl) ⟨1350746, by rfl⟩ : syracuseStep 1800995 = 2701493) B2701493
theorem B7027505 : Blo 1800101 7027505 := bstep (se 2 (by rfl) ⟨2635314, by rfl⟩ : syracuseStep 7027505 = 5270629) B5270629
theorem B2702129 : Blo 1800101 2702129 := bstep (se 2 (by rfl) ⟨1013298, by rfl⟩ : syracuseStep 2702129 = 2026597) B2026597
theorem B1801011 : Blo 1800101 1801011 := bstep (se 1 (by rfl) ⟨1350758, by rfl⟩ : syracuseStep 1801011 = 2701517) B2701517
theorem B1801027 : Blo 1800101 1801027 := bstep (se 1 (by rfl) ⟨1350770, by rfl⟩ : syracuseStep 1801027 = 2701541) B2701541
theorem B2702147 : Blo 1800101 2702147 := bstep (se 1 (by rfl) ⟨2026610, by rfl⟩ : syracuseStep 2702147 = 4053221) B4053221
theorem B5126989 : Blo 1800101 5126989 := bstep (se 3 (by rfl) ⟨961310, by rfl⟩ : syracuseStep 5126989 = 1922621) B1922621
theorem B3038033 : Blo 1800101 3038033 := bstep (se 2 (by rfl) ⟨1139262, by rfl⟩ : syracuseStep 3038033 = 2278525) B2278525
theorem B1801043 : Blo 1800101 1801043 := bstep (se 1 (by rfl) ⟨1350782, by rfl⟩ : syracuseStep 1801043 = 2701565) B2701565
theorem B2702177 : Blo 1800101 2702177 := bstep (se 2 (by rfl) ⟨1013316, by rfl⟩ : syracuseStep 2702177 = 2026633) B2026633
theorem B1801059 : Blo 1800101 1801059 := bstep (se 1 (by rfl) ⟨1350794, by rfl⟩ : syracuseStep 1801059 = 2701589) B2701589
theorem B1801075 : Blo 1800101 1801075 := bstep (se 1 (by rfl) ⟨1350806, by rfl⟩ : syracuseStep 1801075 = 2701613) B2701613
theorem B2702195 : Blo 1800101 2702195 := bstep (se 1 (by rfl) ⟨2026646, by rfl⟩ : syracuseStep 2702195 = 4053293) B4053293
theorem B1801091 : Blo 1800101 1801091 := bstep (se 1 (by rfl) ⟨1350818, by rfl⟩ : syracuseStep 1801091 = 2701637) B2701637
theorem B2702225 : Blo 1800101 2702225 := bstep (se 2 (by rfl) ⟨1013334, by rfl⟩ : syracuseStep 2702225 = 2026669) B2026669
theorem B1801107 : Blo 1800101 1801107 := bstep (se 1 (by rfl) ⟨1350830, by rfl⟩ : syracuseStep 1801107 = 2701661) B2701661
theorem B1801123 : Blo 1800101 1801123 := bstep (se 1 (by rfl) ⟨1350842, by rfl⟩ : syracuseStep 1801123 = 2701685) B2701685
theorem B2702243 : Blo 1800101 2702243 := bstep (se 1 (by rfl) ⟨2026682, by rfl⟩ : syracuseStep 2702243 = 4053365) B4053365
theorem B1801139 : Blo 1800101 1801139 := bstep (se 1 (by rfl) ⟨1350854, by rfl⟩ : syracuseStep 1801139 = 2701709) B2701709
theorem B2702273 : Blo 1800101 2702273 := bstep (se 2 (by rfl) ⟨1013352, by rfl⟩ : syracuseStep 2702273 = 2026705) B2026705
theorem B1801155 : Blo 1800101 1801155 := bstep (se 1 (by rfl) ⟨1350866, by rfl⟩ : syracuseStep 1801155 = 2701733) B2701733
theorem B3038161 : Blo 1800101 3038161 := bstep (se 2 (by rfl) ⟨1139310, by rfl⟩ : syracuseStep 3038161 = 2278621) B2278621
theorem B1801171 : Blo 1800101 1801171 := bstep (se 1 (by rfl) ⟨1350878, by rfl⟩ : syracuseStep 1801171 = 2701757) B2701757
theorem B2702291 : Blo 1800101 2702291 := bstep (se 1 (by rfl) ⟨2026718, by rfl⟩ : syracuseStep 2702291 = 4053437) B4053437
theorem B1801187 : Blo 1800101 1801187 := bstep (se 1 (by rfl) ⟨1350890, by rfl⟩ : syracuseStep 1801187 = 2701781) B2701781
theorem B2702321 : Blo 1800101 2702321 := bstep (se 2 (by rfl) ⟨1013370, by rfl⟩ : syracuseStep 2702321 = 2026741) B2026741
theorem B3038195 : Blo 1800101 3038195 := bstep (se 1 (by rfl) ⟨2278646, by rfl⟩ : syracuseStep 3038195 = 4557293) B4557293
theorem B1801203 : Blo 1800101 1801203 := bstep (se 1 (by rfl) ⟨1350902, by rfl⟩ : syracuseStep 1801203 = 2701805) B2701805
theorem B1801219 : Blo 1800101 1801219 := bstep (se 1 (by rfl) ⟨1350914, by rfl⟩ : syracuseStep 1801219 = 2701829) B2701829
theorem B2702339 : Blo 1800101 2702339 := bstep (se 1 (by rfl) ⟨2026754, by rfl⟩ : syracuseStep 2702339 = 4053509) B4053509
theorem B1801235 : Blo 1800101 1801235 := bstep (se 1 (by rfl) ⟨1350926, by rfl⟩ : syracuseStep 1801235 = 2701853) B2701853
theorem B2702369 : Blo 1800101 2702369 := bstep (se 2 (by rfl) ⟨1013388, by rfl⟩ : syracuseStep 2702369 = 2026777) B2026777
theorem B1801251 : Blo 1800101 1801251 := bstep (se 1 (by rfl) ⟨1350938, by rfl⟩ : syracuseStep 1801251 = 2701877) B2701877
theorem B1801267 : Blo 1800101 1801267 := bstep (se 1 (by rfl) ⟨1350950, by rfl⟩ : syracuseStep 1801267 = 2701901) B2701901
theorem B2702387 : Blo 1800101 2702387 := bstep (se 1 (by rfl) ⟨2026790, by rfl⟩ : syracuseStep 2702387 = 4053581) B4053581
theorem B1801283 : Blo 1800101 1801283 := bstep (se 1 (by rfl) ⟨1350962, by rfl⟩ : syracuseStep 1801283 = 2701925) B2701925
theorem B1801299 : Blo 1800101 1801299 := bstep (se 1 (by rfl) ⟨1350974, by rfl⟩ : syracuseStep 1801299 = 2701949) B2701949
theorem B5626979 : Blo 1800101 5626979 := bstep (se 1 (by rfl) ⟨4220234, by rfl⟩ : syracuseStep 5626979 = 8440469) B8440469
theorem B1801315 : Blo 1800101 1801315 := bstep (se 1 (by rfl) ⟨1350986, by rfl⟩ : syracuseStep 1801315 = 2701973) B2701973
theorem B3038323 : Blo 1800101 3038323 := bstep (se 1 (by rfl) ⟨2278742, by rfl⟩ : syracuseStep 3038323 = 4557485) B4557485
theorem B1801331 : Blo 1800101 1801331 := bstep (se 1 (by rfl) ⟨1350998, by rfl⟩ : syracuseStep 1801331 = 2701997) B2701997
theorem B1801347 : Blo 1800101 1801347 := bstep (se 1 (by rfl) ⟨1351010, by rfl⟩ : syracuseStep 1801347 = 2702021) B2702021
theorem B1801363 : Blo 1800101 1801363 := bstep (se 1 (by rfl) ⟨1351022, by rfl⟩ : syracuseStep 1801363 = 2702045) B2702045
theorem B1801379 : Blo 1800101 1801379 := bstep (se 1 (by rfl) ⟨1351034, by rfl⟩ : syracuseStep 1801379 = 2702069) B2702069
theorem B1801395 : Blo 1800101 1801395 := bstep (se 1 (by rfl) ⟨1351046, by rfl⟩ : syracuseStep 1801395 = 2702093) B2702093
theorem B2563267 : Blo 1800101 2563267 := bstep (se 1 (by rfl) ⟨1922450, by rfl⟩ : syracuseStep 2563267 = 3844901) B3844901
theorem B1801411 : Blo 1800101 1801411 := bstep (se 1 (by rfl) ⟨1351058, by rfl⟩ : syracuseStep 1801411 = 2702117) B2702117
theorem B6077645 : Blo 1800101 6077645 := bstep (se 3 (by rfl) ⟨1139558, by rfl⟩ : syracuseStep 6077645 = 2279117) B2279117
theorem B1801427 : Blo 1800101 1801427 := bstep (se 1 (by rfl) ⟨1351070, by rfl⟩ : syracuseStep 1801427 = 2702141) B2702141
theorem B1801443 : Blo 1800101 1801443 := bstep (se 1 (by rfl) ⟨1351082, by rfl⟩ : syracuseStep 1801443 = 2702165) B2702165
theorem B5848301 : Blo 1800101 5848301 := bstep (se 3 (by rfl) ⟨1096556, by rfl⟩ : syracuseStep 5848301 = 2193113) B2193113
theorem B13671665 : Blo 1800101 13671665 := bstep (se 2 (by rfl) ⟨5126874, by rfl⟩ : syracuseStep 13671665 = 10253749) B10253749
theorem B1801459 : Blo 1800101 1801459 := bstep (se 1 (by rfl) ⟨1351094, by rfl⟩ : syracuseStep 1801459 = 2702189) B2702189
theorem B3038465 : Blo 1800101 3038465 := bstep (se 2 (by rfl) ⟨1139424, by rfl⟩ : syracuseStep 3038465 = 2278849) B2278849
theorem B6077699 : Blo 1800101 6077699 := bstep (se 1 (by rfl) ⟨4558274, by rfl⟩ : syracuseStep 6077699 = 9116549) B9116549
theorem B1801475 : Blo 1800101 1801475 := bstep (se 1 (by rfl) ⟨1351106, by rfl⟩ : syracuseStep 1801475 = 2702213) B2702213
theorem B1801491 : Blo 1800101 1801491 := bstep (se 1 (by rfl) ⟨1351118, by rfl⟩ : syracuseStep 1801491 = 2702237) B2702237
theorem B1801507 : Blo 1800101 1801507 := bstep (se 1 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 1801507 = 2702261) B2702261
theorem B6159665 : Blo 1800101 6159665 := bstep (se 2 (by rfl) ⟨2309874, by rfl⟩ : syracuseStep 6159665 = 4619749) B4619749
theorem B1801523 : Blo 1800101 1801523 := bstep (se 1 (by rfl) ⟨1351142, by rfl⟩ : syracuseStep 1801523 = 2702285) B2702285
theorem B1801539 : Blo 1800101 1801539 := bstep (se 1 (by rfl) ⟨1351154, by rfl⟩ : syracuseStep 1801539 = 2702309) B2702309
theorem B1801555 : Blo 1800101 1801555 := bstep (se 1 (by rfl) ⟨1351166, by rfl⟩ : syracuseStep 1801555 = 2702333) B2702333
theorem B1801571 : Blo 1800101 1801571 := bstep (se 1 (by rfl) ⟨1351178, by rfl⟩ : syracuseStep 1801571 = 2702357) B2702357
theorem B1801587 : Blo 1800101 1801587 := bstep (se 1 (by rfl) ⟨1351190, by rfl⟩ : syracuseStep 1801587 = 2702381) B2702381
theorem B3038593 : Blo 1800101 3038593 := bstep (se 2 (by rfl) ⟨1139472, by rfl⟩ : syracuseStep 3038593 = 2278945) B2278945
theorem B3038627 : Blo 1800101 3038627 := bstep (se 1 (by rfl) ⟨2278970, by rfl⟩ : syracuseStep 3038627 = 4557941) B4557941
theorem B34627013 : Blo 1800101 34627013 := bstep (se 4 (by rfl) ⟨3246282, by rfl⟩ : syracuseStep 34627013 = 6492565) B6492565
theorem B5414381 : Blo 1800101 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B9117197 : Blo 1800101 9117197 := bstep (se 3 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 9117197 = 3418949) B3418949
theorem B6077969 : Blo 1800101 6077969 := bstep (se 2 (by rfl) ⟨2279238, by rfl⟩ : syracuseStep 6077969 = 4558477) B4558477
theorem B3038755 : Blo 1800101 3038755 := bstep (se 1 (by rfl) ⟨2279066, by rfl⟩ : syracuseStep 3038755 = 4558133) B4558133
theorem B16653923 : Blo 1800101 16653923 := bstep (se 1 (by rfl) ⟨12490442, by rfl⟩ : syracuseStep 16653923 = 24980885) B24980885
theorem B2342515 : Blo 1800101 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B3038897 : Blo 1800101 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B15589091 : Blo 1800101 15589091 := bstep (se 1 (by rfl) ⟨11691818, by rfl⟩ : syracuseStep 15589091 = 23383637) B23383637
theorem B2563825 : Blo 1800101 2563825 := bstep (se 2 (by rfl) ⟨961434, by rfl⟩ : syracuseStep 2563825 = 1922869) B1922869
theorem B2563859 : Blo 1800101 2563859 := bstep (se 1 (by rfl) ⟨1922894, by rfl⟩ : syracuseStep 2563859 = 3845789) B3845789
theorem B3039025 : Blo 1800101 3039025 := bstep (se 2 (by rfl) ⟨1139634, by rfl⟩ : syracuseStep 3039025 = 2279269) B2279269
theorem B23076677 : Blo 1800101 23076677 := bstep (se 4 (by rfl) ⟨2163438, by rfl⟩ : syracuseStep 23076677 = 4326877) B4326877
theorem B3465041 : Blo 1800101 3465041 := bstep (se 2 (by rfl) ⟨1299390, by rfl⟩ : syracuseStep 3465041 = 2598781) B2598781
theorem B3039059 : Blo 1800101 3039059 := bstep (se 1 (by rfl) ⟨2279294, by rfl⟩ : syracuseStep 3039059 = 4558589) B4558589
theorem B5128049 : Blo 1800101 5128049 := bstep (se 2 (by rfl) ⟨1923018, by rfl⟩ : syracuseStep 5128049 = 3846037) B3846037
theorem B2883457 : Blo 1800101 2883457 := bstep (se 2 (by rfl) ⟨1081296, by rfl⟩ : syracuseStep 2883457 = 2162593) B2162593
theorem B3039187 : Blo 1800101 3039187 := bstep (se 1 (by rfl) ⟨2279390, by rfl⟩ : syracuseStep 3039187 = 4558781) B4558781
theorem B3244121 : Blo 1800101 3244121 := bstep (se 2 (by rfl) ⟨1216545, by rfl⟩ : syracuseStep 3244121 = 2433091) B2433091
theorem B11542621 : Blo 1800101 11542621 := bstep (se 3 (by rfl) ⟨2164241, by rfl⟩ : syracuseStep 11542621 = 4328483) B4328483
theorem B3039383 : Blo 1800101 3039383 := bstep (se 1 (by rfl) ⟨2279537, by rfl⟩ : syracuseStep 3039383 = 4559075) B4559075
theorem B3039511 : Blo 1800101 3039511 := bstep (se 1 (by rfl) ⟨2279633, by rfl⟩ : syracuseStep 3039511 = 4559267) B4559267
theorem B6488471 : Blo 1800101 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B3334603 : Blo 1800101 3334603 := bstep (se 1 (by rfl) ⟨2500952, by rfl⟩ : syracuseStep 3334603 = 5001905) B5001905
theorem B9118169 : Blo 1800101 9118169 := bstep (se 2 (by rfl) ⟨3419313, by rfl⟩ : syracuseStep 9118169 = 6838627) B6838627
theorem B6078941 : Blo 1800101 6078941 := bstep (se 3 (by rfl) ⟨1139801, by rfl⟩ : syracuseStep 6078941 = 2279603) B2279603
theorem B15802897 : Blo 1800101 15802897 := bstep (se 2 (by rfl) ⟨5926086, by rfl⟩ : syracuseStep 15802897 = 11852173) B11852173
theorem B7299857 : Blo 1800101 7299857 := bstep (se 2 (by rfl) ⟨2737446, by rfl⟩ : syracuseStep 7299857 = 5474893) B5474893
theorem B16425773 : Blo 1800101 16425773 := bstep (se 3 (by rfl) ⟨3079832, by rfl⟩ : syracuseStep 16425773 = 6159665) B6159665
theorem B15385409 : Blo 1800101 15385409 := bstep (se 2 (by rfl) ⟨5769528, by rfl⟩ : syracuseStep 15385409 = 11539057) B11539057
theorem B3040139 : Blo 1800101 3040139 := bstep (se 1 (by rfl) ⟨2280104, by rfl⟩ : syracuseStep 3040139 = 4560209) B4560209
theorem B5129153 : Blo 1800101 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B6489035 : Blo 1800101 6489035 := bstep (se 1 (by rfl) ⟨4866776, by rfl⟩ : syracuseStep 6489035 = 9733553) B9733553
theorem B3245015 : Blo 1800101 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B4867123 : Blo 1800101 4867123 := bstep (se 1 (by rfl) ⟨3650342, by rfl⟩ : syracuseStep 4867123 = 7300685) B7300685
theorem B7906355 : Blo 1800101 7906355 := bstep (se 1 (by rfl) ⟨5929766, by rfl⟩ : syracuseStep 7906355 = 11859533) B11859533
theorem B6489163 : Blo 1800101 6489163 := bstep (se 1 (by rfl) ⟨4866872, by rfl⟩ : syracuseStep 6489163 = 9733745) B9733745
theorem B4105495 : Blo 1800101 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B6489395 : Blo 1800101 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B30762341 : Blo 1800101 30762341 := bstep (se 4 (by rfl) ⟨2883969, by rfl⟩ : syracuseStep 30762341 = 5767939) B5767939
theorem B33318245 : Blo 1800101 33318245 := bstep (se 4 (by rfl) ⟨3123585, by rfl⟩ : syracuseStep 33318245 = 6247171) B6247171
theorem B5129689 : Blo 1800101 5129689 := bstep (se 2 (by rfl) ⟨1923633, by rfl⟩ : syracuseStep 5129689 = 3847267) B3847267
theorem B2885195 : Blo 1800101 2885195 := bstep (se 1 (by rfl) ⟨2163896, by rfl⟩ : syracuseStep 2885195 = 4327793) B4327793
theorem B6080075 : Blo 1800101 6080075 := bstep (se 1 (by rfl) ⟨4560056, by rfl⟩ : syracuseStep 6080075 = 9120113) B9120113
theorem B3417689 : Blo 1800101 3417689 := bstep (se 2 (by rfl) ⟨1281633, by rfl⟩ : syracuseStep 3417689 = 2563267) B2563267
theorem B3466891 : Blo 1800101 3466891 := bstep (se 1 (by rfl) ⟨2600168, by rfl⟩ : syracuseStep 3466891 = 5200337) B5200337
theorem B7694003 : Blo 1800101 7694003 := bstep (se 1 (by rfl) ⟨5770502, by rfl⟩ : syracuseStep 7694003 = 11541005) B11541005
theorem B18728653 : Blo 1800101 18728653 := bstep (se 3 (by rfl) ⟨3511622, by rfl⟩ : syracuseStep 18728653 = 7023245) B7023245
theorem B2025175 : Blo 1800101 2025175 := bstep (se 1 (by rfl) ⟨1518881, by rfl⟩ : syracuseStep 2025175 = 3037763) B3037763
theorem B6080345 : Blo 1800101 6080345 := bstep (se 2 (by rfl) ⟨2280129, by rfl⟩ : syracuseStep 6080345 = 4560259) B4560259
theorem B2025355 : Blo 1800101 2025355 := bstep (se 1 (by rfl) ⟨1519016, by rfl⟩ : syracuseStep 2025355 = 3038033) B3038033
theorem B4556695 : Blo 1800101 4556695 := bstep (se 1 (by rfl) ⟨3417521, by rfl⟩ : syracuseStep 4556695 = 6835043) B6835043
theorem B2025463 : Blo 1800101 2025463 := bstep (se 1 (by rfl) ⟨1519097, by rfl⟩ : syracuseStep 2025463 = 3038195) B3038195
theorem B15378437 : Blo 1800101 15378437 := bstep (se 4 (by rfl) ⟨1441728, by rfl⟩ : syracuseStep 15378437 = 2883457) B2883457
theorem B9119789 : Blo 1800101 9119789 := bstep (se 3 (by rfl) ⟨1709960, by rfl⟩ : syracuseStep 9119789 = 3419921) B3419921
theorem B4868171 : Blo 1800101 4868171 := bstep (se 1 (by rfl) ⟨3651128, by rfl⟩ : syracuseStep 4868171 = 7302257) B7302257
theorem B3123353 : Blo 1800101 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B2025643 : Blo 1800101 2025643 := bstep (se 1 (by rfl) ⟨1519232, by rfl⟩ : syracuseStep 2025643 = 3038465) B3038465
theorem B10258649 : Blo 1800101 10258649 := bstep (se 2 (by rfl) ⟨3846993, by rfl⟩ : syracuseStep 10258649 = 7693987) B7693987
theorem B2025751 : Blo 1800101 2025751 := bstep (se 1 (by rfl) ⟨1519313, by rfl⟩ : syracuseStep 2025751 = 3038627) B3038627
theorem B3418433 : Blo 1800101 3418433 := bstep (se 2 (by rfl) ⟨1281912, by rfl⟩ : syracuseStep 3418433 = 2563825) B2563825
theorem B4557131 : Blo 1800101 4557131 := bstep (se 1 (by rfl) ⟨3417848, by rfl⟩ : syracuseStep 4557131 = 6835697) B6835697
theorem B2279755 : Blo 1800101 2279755 := bstep (se 1 (by rfl) ⟨1709816, by rfl⟩ : syracuseStep 2279755 = 3419633) B3419633
theorem B11102615 : Blo 1800101 11102615 := bstep (se 1 (by rfl) ⟨8326961, by rfl⟩ : syracuseStep 11102615 = 16653923) B16653923
theorem B6490547 : Blo 1800101 6490547 := bstep (se 1 (by rfl) ⟨4867910, by rfl⟩ : syracuseStep 6490547 = 9735821) B9735821
theorem B2025931 : Blo 1800101 2025931 := bstep (se 1 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 2025931 = 3038897) B3038897
theorem B2026039 : Blo 1800101 2026039 := bstep (se 1 (by rfl) ⟨1519529, by rfl⟩ : syracuseStep 2026039 = 3039059) B3039059
theorem B3418699 : Blo 1800101 3418699 := bstep (se 1 (by rfl) ⟨2564024, by rfl⟩ : syracuseStep 3418699 = 5128049) B5128049
theorem B4557505 : Blo 1800101 4557505 := bstep (se 2 (by rfl) ⟨1709064, by rfl⟩ : syracuseStep 4557505 = 3418129) B3418129
theorem B2026219 : Blo 1800101 2026219 := bstep (se 1 (by rfl) ⟨1519664, by rfl⟩ : syracuseStep 2026219 = 3039329) B3039329
theorem B7301933 : Blo 1800101 7301933 := bstep (se 3 (by rfl) ⟨1369112, by rfl⟩ : syracuseStep 7301933 = 2738225) B2738225
theorem B5196595 : Blo 1800101 5196595 := bstep (se 1 (by rfl) ⟨3897446, by rfl⟩ : syracuseStep 5196595 = 7794893) B7794893
theorem B23071553 : Blo 1800101 23071553 := bstep (se 2 (by rfl) ⟨8651832, by rfl⟩ : syracuseStep 23071553 = 17303665) B17303665
theorem B2026327 : Blo 1800101 2026327 := bstep (se 1 (by rfl) ⟨1519745, by rfl⟩ : syracuseStep 2026327 = 3039491) B3039491
theorem B3419147 : Blo 1800101 3419147 := bstep (se 1 (by rfl) ⟨2564360, by rfl⟩ : syracuseStep 3419147 = 5128721) B5128721
theorem B2026507 : Blo 1800101 2026507 := bstep (se 1 (by rfl) ⟨1519880, by rfl⟩ : syracuseStep 2026507 = 3039761) B3039761
theorem B6491153 : Blo 1800101 6491153 := bstep (se 2 (by rfl) ⟨2434182, by rfl⟩ : syracuseStep 6491153 = 4868365) B4868365
theorem B2026615 : Blo 1800101 2026615 := bstep (se 1 (by rfl) ⟨1519961, by rfl⟩ : syracuseStep 2026615 = 3039923) B3039923
theorem B3419329 : Blo 1800101 3419329 := bstep (se 2 (by rfl) ⟨1282248, by rfl⟩ : syracuseStep 3419329 = 2564497) B2564497
theorem B4558103 : Blo 1800101 4558103 := bstep (se 1 (by rfl) ⟨3418577, by rfl⟩ : syracuseStep 4558103 = 6837155) B6837155
theorem B2026795 : Blo 1800101 2026795 := bstep (se 1 (by rfl) ⟨1520096, by rfl⟩ : syracuseStep 2026795 = 3040193) B3040193
theorem B4050251 : Blo 1800101 4050251 := bstep (se 1 (by rfl) ⟨3037688, by rfl⟩ : syracuseStep 4050251 = 6075377) B6075377
theorem B4050305 : Blo 1800101 4050305 := bstep (se 2 (by rfl) ⟨1518864, by rfl⟩ : syracuseStep 4050305 = 3037729) B3037729
theorem B3419671 : Blo 1800101 3419671 := bstep (se 1 (by rfl) ⟨2564753, by rfl⟩ : syracuseStep 3419671 = 5129507) B5129507
theorem B4050521 : Blo 1800101 4050521 := bstep (se 2 (by rfl) ⟨1518945, by rfl⟩ : syracuseStep 4050521 = 3037891) B3037891
theorem B4050611 : Blo 1800101 4050611 := bstep (se 1 (by rfl) ⟨3037958, by rfl⟩ : syracuseStep 4050611 = 6075917) B6075917
theorem B4050647 : Blo 1800101 4050647 := bstep (se 1 (by rfl) ⟨3037985, by rfl⟩ : syracuseStep 4050647 = 6075971) B6075971
theorem B3419891 : Blo 1800101 3419891 := bstep (se 1 (by rfl) ⟨2564918, by rfl⟩ : syracuseStep 3419891 = 5129837) B5129837
theorem B6835985 : Blo 1800101 6835985 := bstep (se 2 (by rfl) ⟨2563494, by rfl⟩ : syracuseStep 6835985 = 5126989) B5126989
theorem B4050827 : Blo 1800101 4050827 := bstep (se 1 (by rfl) ⟨3038120, by rfl⟩ : syracuseStep 4050827 = 6076241) B6076241
theorem B8441779 : Blo 1800101 8441779 := bstep (se 1 (by rfl) ⟨6331334, by rfl⟩ : syracuseStep 8441779 = 12662669) B12662669
theorem B4050881 : Blo 1800101 4050881 := bstep (se 2 (by rfl) ⟨1519080, by rfl⟩ : syracuseStep 4050881 = 3038161) B3038161
theorem B3420119 : Blo 1800101 3420119 := bstep (se 1 (by rfl) ⟨2565089, by rfl⟩ : syracuseStep 3420119 = 5130179) B5130179
theorem B4558913 : Blo 1800101 4558913 := bstep (se 2 (by rfl) ⟨1709592, by rfl⟩ : syracuseStep 4558913 = 3419185) B3419185
theorem B118452293 : Blo 1800101 118452293 := bstep (se 4 (by rfl) ⟨11104902, by rfl⟩ : syracuseStep 118452293 = 22209805) B22209805
theorem B4051097 : Blo 1800101 4051097 := bstep (se 2 (by rfl) ⟨1519161, by rfl⟩ : syracuseStep 4051097 = 3038323) B3038323
theorem B4051187 : Blo 1800101 4051187 := bstep (se 1 (by rfl) ⟨3038390, by rfl⟩ : syracuseStep 4051187 = 6076781) B6076781
theorem B4051223 : Blo 1800101 4051223 := bstep (se 1 (by rfl) ⟨3038417, by rfl⟩ : syracuseStep 4051223 = 6076835) B6076835
theorem B6836683 : Blo 1800101 6836683 := bstep (se 1 (by rfl) ⟨5127512, by rfl⟩ : syracuseStep 6836683 = 10255025) B10255025
theorem B4051403 : Blo 1800101 4051403 := bstep (se 1 (by rfl) ⟨3038552, by rfl⟩ : syracuseStep 4051403 = 6077105) B6077105
theorem B4051457 : Blo 1800101 4051457 := bstep (se 2 (by rfl) ⟨1519296, by rfl⟩ : syracuseStep 4051457 = 3038593) B3038593
theorem B10252817 : Blo 1800101 10252817 := bstep (se 2 (by rfl) ⟨3844806, by rfl⟩ : syracuseStep 10252817 = 7689613) B7689613
theorem B4559449 : Blo 1800101 4559449 := bstep (se 2 (by rfl) ⟨1709793, by rfl⟩ : syracuseStep 4559449 = 3419587) B3419587
theorem B12980837 : Blo 1800101 12980837 := bstep (se 4 (by rfl) ⟨1216953, by rfl⟩ : syracuseStep 12980837 = 2433907) B2433907
theorem B7795379 : Blo 1800101 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B4051673 : Blo 1800101 4051673 := bstep (se 2 (by rfl) ⟨1519377, by rfl⟩ : syracuseStep 4051673 = 3038755) B3038755
theorem B6836957 : Blo 1800101 6836957 := bstep (se 3 (by rfl) ⟨1281929, by rfl⟩ : syracuseStep 6836957 = 2563859) B2563859
theorem B3846899 : Blo 1800101 3846899 := bstep (se 1 (by rfl) ⟨2885174, by rfl⟩ : syracuseStep 3846899 = 5770349) B5770349
theorem B4051763 : Blo 1800101 4051763 := bstep (se 1 (by rfl) ⟨3038822, by rfl⟩ : syracuseStep 4051763 = 6077645) B6077645
theorem B9114443 : Blo 1800101 9114443 := bstep (se 1 (by rfl) ⟨6835832, by rfl⟩ : syracuseStep 9114443 = 13671665) B13671665
theorem B4051799 : Blo 1800101 4051799 := bstep (se 1 (by rfl) ⟨3038849, by rfl⟩ : syracuseStep 4051799 = 6077699) B6077699
theorem B17314661 : Blo 1800101 17314661 := bstep (se 4 (by rfl) ⟨1623249, by rfl⟩ : syracuseStep 17314661 = 3246499) B3246499
theorem B2700185 : Blo 1800101 2700185 := bstep (se 2 (by rfl) ⟨1012569, by rfl⟩ : syracuseStep 2700185 = 2025139) B2025139
theorem B3609587 : Blo 1800101 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B2700299 : Blo 1800101 2700299 := bstep (se 1 (by rfl) ⟨2025224, by rfl⟩ : syracuseStep 2700299 = 4050449) B4050449
theorem B4051979 : Blo 1800101 4051979 := bstep (se 1 (by rfl) ⟨3038984, by rfl⟩ : syracuseStep 4051979 = 6077969) B6077969
theorem B2700311 : Blo 1800101 2700311 := bstep (se 1 (by rfl) ⟨2025233, by rfl⟩ : syracuseStep 2700311 = 4050467) B4050467
theorem B4052033 : Blo 1800101 4052033 := bstep (se 2 (by rfl) ⟨1519512, by rfl⟩ : syracuseStep 4052033 = 3039025) B3039025
theorem B2700377 : Blo 1800101 2700377 := bstep (se 2 (by rfl) ⟨1012641, by rfl⟩ : syracuseStep 2700377 = 2025283) B2025283
theorem B6075485 : Blo 1800101 6075485 := bstep (se 3 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 6075485 = 2278307) B2278307
theorem B10392727 : Blo 1800101 10392727 := bstep (se 1 (by rfl) ⟨7794545, by rfl⟩ : syracuseStep 10392727 = 15589091) B15589091
theorem B2700491 : Blo 1800101 2700491 := bstep (se 1 (by rfl) ⟨2025368, by rfl⟩ : syracuseStep 2700491 = 4050737) B4050737
theorem B2700503 : Blo 1800101 2700503 := bstep (se 1 (by rfl) ⟨2025377, by rfl⟩ : syracuseStep 2700503 = 4050755) B4050755
theorem B2700569 : Blo 1800101 2700569 := bstep (se 2 (by rfl) ⟨1012713, by rfl⟩ : syracuseStep 2700569 = 2025427) B2025427
theorem B4052249 : Blo 1800101 4052249 := bstep (se 2 (by rfl) ⟨1519593, by rfl⟩ : syracuseStep 4052249 = 3039187) B3039187
theorem B4052339 : Blo 1800101 4052339 := bstep (se 1 (by rfl) ⟨3039254, by rfl⟩ : syracuseStep 4052339 = 6078509) B6078509
theorem B2700683 : Blo 1800101 2700683 := bstep (se 1 (by rfl) ⟨2025512, by rfl⟩ : syracuseStep 2700683 = 4051025) B4051025
theorem B2700695 : Blo 1800101 2700695 := bstep (se 1 (by rfl) ⟨2025521, by rfl⟩ : syracuseStep 2700695 = 4051043) B4051043
theorem B6837655 : Blo 1800101 6837655 := bstep (se 1 (by rfl) ⟨5128241, by rfl⟩ : syracuseStep 6837655 = 10256483) B10256483
theorem B4052375 : Blo 1800101 4052375 := bstep (se 1 (by rfl) ⟨3039281, by rfl⟩ : syracuseStep 4052375 = 6078563) B6078563
theorem B2700761 : Blo 1800101 2700761 := bstep (se 2 (by rfl) ⟨1012785, by rfl⟩ : syracuseStep 2700761 = 2025571) B2025571
theorem B15382061 : Blo 1800101 15382061 := bstep (se 3 (by rfl) ⟨2884136, by rfl⟩ : syracuseStep 15382061 = 5768273) B5768273
theorem B11695661 : Blo 1800101 11695661 := bstep (se 3 (by rfl) ⟨2192936, by rfl⟩ : syracuseStep 11695661 = 4385873) B4385873
theorem B2700875 : Blo 1800101 2700875 := bstep (se 1 (by rfl) ⟨2025656, by rfl⟩ : syracuseStep 2700875 = 4051313) B4051313
theorem B4052555 : Blo 1800101 4052555 := bstep (se 1 (by rfl) ⟨3039416, by rfl⟩ : syracuseStep 4052555 = 6078833) B6078833
theorem B2700887 : Blo 1800101 2700887 := bstep (se 1 (by rfl) ⟨2025665, by rfl⟩ : syracuseStep 2700887 = 4051331) B4051331
theorem B4052609 : Blo 1800101 4052609 := bstep (se 2 (by rfl) ⟨1519728, by rfl⟩ : syracuseStep 4052609 = 3039457) B3039457
theorem B2700953 : Blo 1800101 2700953 := bstep (se 2 (by rfl) ⟨1012857, by rfl⟩ : syracuseStep 2700953 = 2025715) B2025715
theorem B2701067 : Blo 1800101 2701067 := bstep (se 1 (by rfl) ⟨2025800, by rfl⟩ : syracuseStep 2701067 = 4051601) B4051601
theorem B2701079 : Blo 1800101 2701079 := bstep (se 1 (by rfl) ⟨2025809, by rfl⟩ : syracuseStep 2701079 = 4051619) B4051619
theorem B2701145 : Blo 1800101 2701145 := bstep (se 2 (by rfl) ⟨1012929, by rfl⟩ : syracuseStep 2701145 = 2025859) B2025859
theorem B4052825 : Blo 1800101 4052825 := bstep (se 2 (by rfl) ⟨1519809, by rfl⟩ : syracuseStep 4052825 = 3039619) B3039619
theorem B3749771 : Blo 1800101 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B1800107 : Blo 1800101 1800107 := bstep (se 1 (by rfl) ⟨1350080, by rfl⟩ : syracuseStep 1800107 = 2700161) B2700161
theorem B4052915 : Blo 1800101 4052915 := bstep (se 1 (by rfl) ⟨3039686, by rfl⟩ : syracuseStep 4052915 = 6079373) B6079373
theorem B1800119 : Blo 1800101 1800119 := bstep (se 1 (by rfl) ⟨1350089, by rfl⟩ : syracuseStep 1800119 = 2700179) B2700179
theorem B1800139 : Blo 1800101 1800139 := bstep (se 1 (by rfl) ⟨1350104, by rfl⟩ : syracuseStep 1800139 = 2700209) B2700209
theorem B2701259 : Blo 1800101 2701259 := bstep (se 1 (by rfl) ⟨2025944, by rfl⟩ : syracuseStep 2701259 = 4051889) B4051889
theorem B5478347 : Blo 1800101 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B1800151 : Blo 1800101 1800151 := bstep (se 1 (by rfl) ⟨1350113, by rfl⟩ : syracuseStep 1800151 = 2700227) B2700227
theorem B1923031 : Blo 1800101 1923031 := bstep (se 1 (by rfl) ⟨1442273, by rfl⟩ : syracuseStep 1923031 = 2884547) B2884547
theorem B2701271 : Blo 1800101 2701271 := bstep (se 1 (by rfl) ⟨2025953, by rfl⟩ : syracuseStep 2701271 = 4051907) B4051907
theorem B4052951 : Blo 1800101 4052951 := bstep (se 1 (by rfl) ⟨3039713, by rfl⟩ : syracuseStep 4052951 = 6079427) B6079427
theorem B8214493 : Blo 1800101 8214493 := bstep (se 3 (by rfl) ⟨1540217, by rfl⟩ : syracuseStep 8214493 = 3080435) B3080435
theorem B1800171 : Blo 1800101 1800171 := bstep (se 1 (by rfl) ⟨1350128, by rfl⟩ : syracuseStep 1800171 = 2700257) B2700257
theorem B1800183 : Blo 1800101 1800183 := bstep (se 1 (by rfl) ⟨1350137, by rfl⟩ : syracuseStep 1800183 = 2700275) B2700275
theorem B1800203 : Blo 1800101 1800203 := bstep (se 1 (by rfl) ⟨1350152, by rfl⟩ : syracuseStep 1800203 = 2700305) B2700305
theorem B1800215 : Blo 1800101 1800215 := bstep (se 1 (by rfl) ⟨1350161, by rfl⟩ : syracuseStep 1800215 = 2700323) B2700323
theorem B2701337 : Blo 1800101 2701337 := bstep (se 2 (by rfl) ⟨1013001, by rfl⟩ : syracuseStep 2701337 = 2026003) B2026003
theorem B1800235 : Blo 1800101 1800235 := bstep (se 1 (by rfl) ⟨1350176, by rfl⟩ : syracuseStep 1800235 = 2700353) B2700353
theorem B1800247 : Blo 1800101 1800247 := bstep (se 1 (by rfl) ⟨1350185, by rfl⟩ : syracuseStep 1800247 = 2700371) B2700371
theorem B1800267 : Blo 1800101 1800267 := bstep (se 1 (by rfl) ⟨1350200, by rfl⟩ : syracuseStep 1800267 = 2700401) B2700401
theorem B1800279 : Blo 1800101 1800279 := bstep (se 1 (by rfl) ⟨1350209, by rfl⟩ : syracuseStep 1800279 = 2700419) B2700419
theorem B5126237 : Blo 1800101 5126237 := bstep (se 3 (by rfl) ⟨961169, by rfl⟩ : syracuseStep 5126237 = 1922339) B1922339
theorem B1800299 : Blo 1800101 1800299 := bstep (se 1 (by rfl) ⟨1350224, by rfl⟩ : syracuseStep 1800299 = 2700449) B2700449
theorem B1800311 : Blo 1800101 1800311 := bstep (se 1 (by rfl) ⟨1350233, by rfl⟩ : syracuseStep 1800311 = 2700467) B2700467
theorem B3651713 : Blo 1800101 3651713 := bstep (se 2 (by rfl) ⟨1369392, by rfl⟩ : syracuseStep 3651713 = 2738785) B2738785
theorem B1800331 : Blo 1800101 1800331 := bstep (se 1 (by rfl) ⟨1350248, by rfl⟩ : syracuseStep 1800331 = 2700497) B2700497
theorem B2701451 : Blo 1800101 2701451 := bstep (se 1 (by rfl) ⟨2026088, by rfl⟩ : syracuseStep 2701451 = 4052177) B4052177
theorem B4053131 : Blo 1800101 4053131 := bstep (se 1 (by rfl) ⟨3039848, by rfl⟩ : syracuseStep 4053131 = 6079697) B6079697
theorem B1800343 : Blo 1800101 1800343 := bstep (se 1 (by rfl) ⟨1350257, by rfl⟩ : syracuseStep 1800343 = 2700515) B2700515
theorem B2701463 : Blo 1800101 2701463 := bstep (se 1 (by rfl) ⟨2026097, by rfl⟩ : syracuseStep 2701463 = 4052195) B4052195
theorem B1800363 : Blo 1800101 1800363 := bstep (se 1 (by rfl) ⟨1350272, by rfl⟩ : syracuseStep 1800363 = 2700545) B2700545
theorem B6838445 : Blo 1800101 6838445 := bstep (se 3 (by rfl) ⟨1282208, by rfl⟩ : syracuseStep 6838445 = 2564417) B2564417
theorem B36960437 : Blo 1800101 36960437 := bstep (se 5 (by rfl) ⟨1732520, by rfl⟩ : syracuseStep 36960437 = 3465041) B3465041
theorem B1800375 : Blo 1800101 1800375 := bstep (se 1 (by rfl) ⟨1350281, by rfl⟩ : syracuseStep 1800375 = 2700563) B2700563
theorem B4053185 : Blo 1800101 4053185 := bstep (se 2 (by rfl) ⟨1519944, by rfl⟩ : syracuseStep 4053185 = 3039889) B3039889
theorem B1800395 : Blo 1800101 1800395 := bstep (se 1 (by rfl) ⟨1350296, by rfl⟩ : syracuseStep 1800395 = 2700593) B2700593
theorem B6076619 : Blo 1800101 6076619 := bstep (se 1 (by rfl) ⟨4557464, by rfl⟩ : syracuseStep 6076619 = 9114929) B9114929
theorem B12982477 : Blo 1800101 12982477 := bstep (se 3 (by rfl) ⟨2434214, by rfl⟩ : syracuseStep 12982477 = 4868429) B4868429
theorem B1800407 : Blo 1800101 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B2701529 : Blo 1800101 2701529 := bstep (se 2 (by rfl) ⟨1013073, by rfl⟩ : syracuseStep 2701529 = 2026147) B2026147
theorem B1800427 : Blo 1800101 1800427 := bstep (se 1 (by rfl) ⟨1350320, by rfl⟩ : syracuseStep 1800427 = 2700641) B2700641
theorem B1800439 : Blo 1800101 1800439 := bstep (se 1 (by rfl) ⟨1350329, by rfl⟩ : syracuseStep 1800439 = 2700659) B2700659
theorem B3651841 : Blo 1800101 3651841 := bstep (se 2 (by rfl) ⟨1369440, by rfl⟩ : syracuseStep 3651841 = 2738881) B2738881
theorem B1800459 : Blo 1800101 1800459 := bstep (se 1 (by rfl) ⟨1350344, by rfl⟩ : syracuseStep 1800459 = 2700689) B2700689
theorem B1800471 : Blo 1800101 1800471 := bstep (se 1 (by rfl) ⟨1350353, by rfl⟩ : syracuseStep 1800471 = 2700707) B2700707
theorem B1800491 : Blo 1800101 1800491 := bstep (se 1 (by rfl) ⟨1350368, by rfl⟩ : syracuseStep 1800491 = 2700737) B2700737
theorem B1800503 : Blo 1800101 1800503 := bstep (se 1 (by rfl) ⟨1350377, by rfl⟩ : syracuseStep 1800503 = 2700755) B2700755
theorem B5126465 : Blo 1800101 5126465 := bstep (se 2 (by rfl) ⟨1922424, by rfl⟩ : syracuseStep 5126465 = 3844849) B3844849
theorem B7690571 : Blo 1800101 7690571 := bstep (se 1 (by rfl) ⟨5767928, by rfl⟩ : syracuseStep 7690571 = 11535857) B11535857
theorem B1800523 : Blo 1800101 1800523 := bstep (se 1 (by rfl) ⟨1350392, by rfl⟩ : syracuseStep 1800523 = 2700785) B2700785
theorem B2701643 : Blo 1800101 2701643 := bstep (se 1 (by rfl) ⟨2026232, by rfl⟩ : syracuseStep 2701643 = 4052465) B4052465
theorem B1800535 : Blo 1800101 1800535 := bstep (se 1 (by rfl) ⟨1350401, by rfl⟩ : syracuseStep 1800535 = 2700803) B2700803
theorem B2701655 : Blo 1800101 2701655 := bstep (se 1 (by rfl) ⟨2026241, by rfl⟩ : syracuseStep 2701655 = 4052483) B4052483
theorem B9738589 : Blo 1800101 9738589 := bstep (se 3 (by rfl) ⟨1825985, by rfl⟩ : syracuseStep 9738589 = 3651971) B3651971
theorem B1800555 : Blo 1800101 1800555 := bstep (se 1 (by rfl) ⟨1350416, by rfl⟩ : syracuseStep 1800555 = 2700833) B2700833
theorem B1800567 : Blo 1800101 1800567 := bstep (se 1 (by rfl) ⟨1350425, by rfl⟩ : syracuseStep 1800567 = 2700851) B2700851
theorem B1800587 : Blo 1800101 1800587 := bstep (se 1 (by rfl) ⟨1350440, by rfl⟩ : syracuseStep 1800587 = 2700881) B2700881
theorem B48085397 : Blo 1800101 48085397 := bstep (se 6 (by rfl) ⟨1127001, by rfl⟩ : syracuseStep 48085397 = 2254003) B2254003
theorem B1800599 : Blo 1800101 1800599 := bstep (se 1 (by rfl) ⟨1350449, by rfl⟩ : syracuseStep 1800599 = 2700899) B2700899
theorem B2701721 : Blo 1800101 2701721 := bstep (se 2 (by rfl) ⟨1013145, by rfl⟩ : syracuseStep 2701721 = 2026291) B2026291
theorem B4053401 : Blo 1800101 4053401 := bstep (se 2 (by rfl) ⟨1520025, by rfl⟩ : syracuseStep 4053401 = 3040051) B3040051
theorem B1800619 : Blo 1800101 1800619 := bstep (se 1 (by rfl) ⟨1350464, by rfl⟩ : syracuseStep 1800619 = 2700929) B2700929
theorem B11098547 : Blo 1800101 11098547 := bstep (se 1 (by rfl) ⟨8323910, by rfl⟩ : syracuseStep 11098547 = 16647821) B16647821
theorem B1800631 : Blo 1800101 1800631 := bstep (se 1 (by rfl) ⟨1350473, by rfl⟩ : syracuseStep 1800631 = 2700947) B2700947
theorem B1800651 : Blo 1800101 1800651 := bstep (se 1 (by rfl) ⟨1350488, by rfl⟩ : syracuseStep 1800651 = 2700977) B2700977
theorem B1800663 : Blo 1800101 1800663 := bstep (se 1 (by rfl) ⟨1350497, by rfl⟩ : syracuseStep 1800663 = 2700995) B2700995
theorem B6076889 : Blo 1800101 6076889 := bstep (se 2 (by rfl) ⟨2278833, by rfl⟩ : syracuseStep 6076889 = 4557667) B4557667
theorem B1800683 : Blo 1800101 1800683 := bstep (se 1 (by rfl) ⟨1350512, by rfl⟩ : syracuseStep 1800683 = 2701025) B2701025
theorem B4053491 : Blo 1800101 4053491 := bstep (se 1 (by rfl) ⟨3040118, by rfl⟩ : syracuseStep 4053491 = 6080237) B6080237
theorem B1800695 : Blo 1800101 1800695 := bstep (se 1 (by rfl) ⟨1350521, by rfl⟩ : syracuseStep 1800695 = 2701043) B2701043
theorem B1800715 : Blo 1800101 1800715 := bstep (se 1 (by rfl) ⟨1350536, by rfl⟩ : syracuseStep 1800715 = 2701073) B2701073
theorem B2701835 : Blo 1800101 2701835 := bstep (se 1 (by rfl) ⟨2026376, by rfl⟩ : syracuseStep 2701835 = 4052753) B4052753
theorem B1800727 : Blo 1800101 1800727 := bstep (se 1 (by rfl) ⟨1350545, by rfl⟩ : syracuseStep 1800727 = 2701091) B2701091
theorem B2701847 : Blo 1800101 2701847 := bstep (se 1 (by rfl) ⟨2026385, by rfl⟩ : syracuseStep 2701847 = 4052771) B4052771
theorem B4053527 : Blo 1800101 4053527 := bstep (se 1 (by rfl) ⟨3040145, by rfl⟩ : syracuseStep 4053527 = 6080291) B6080291
theorem B1800747 : Blo 1800101 1800747 := bstep (se 1 (by rfl) ⟨1350560, by rfl⟩ : syracuseStep 1800747 = 2701121) B2701121
theorem B1800759 : Blo 1800101 1800759 := bstep (se 1 (by rfl) ⟨1350569, by rfl⟩ : syracuseStep 1800759 = 2701139) B2701139
theorem B9116225 : Blo 1800101 9116225 := bstep (se 2 (by rfl) ⟨3418584, by rfl⟩ : syracuseStep 9116225 = 6837169) B6837169
theorem B1800779 : Blo 1800101 1800779 := bstep (se 1 (by rfl) ⟨1350584, by rfl⟩ : syracuseStep 1800779 = 2701169) B2701169
theorem B3037783 : Blo 1800101 3037783 := bstep (se 1 (by rfl) ⟨2278337, by rfl⟩ : syracuseStep 3037783 = 4556675) B4556675
theorem B1800791 : Blo 1800101 1800791 := bstep (se 1 (by rfl) ⟨1350593, by rfl⟩ : syracuseStep 1800791 = 2701187) B2701187
theorem B2701913 : Blo 1800101 2701913 := bstep (se 2 (by rfl) ⟨1013217, by rfl⟩ : syracuseStep 2701913 = 2026435) B2026435
theorem B1800811 : Blo 1800101 1800811 := bstep (se 1 (by rfl) ⟨1350608, by rfl⟩ : syracuseStep 1800811 = 2701217) B2701217
theorem B1800823 : Blo 1800101 1800823 := bstep (se 1 (by rfl) ⟨1350617, by rfl⟩ : syracuseStep 1800823 = 2701235) B2701235
theorem B1800843 : Blo 1800101 1800843 := bstep (se 1 (by rfl) ⟨1350632, by rfl⟩ : syracuseStep 1800843 = 2701265) B2701265
theorem B5126807 : Blo 1800101 5126807 := bstep (se 1 (by rfl) ⟨3845105, by rfl⟩ : syracuseStep 5126807 = 7690211) B7690211
theorem B1800855 : Blo 1800101 1800855 := bstep (se 1 (by rfl) ⟨1350641, by rfl⟩ : syracuseStep 1800855 = 2701283) B2701283
theorem B1800875 : Blo 1800101 1800875 := bstep (se 1 (by rfl) ⟨1350656, by rfl⟩ : syracuseStep 1800875 = 2701313) B2701313
theorem B1800887 : Blo 1800101 1800887 := bstep (se 1 (by rfl) ⟨1350665, by rfl⟩ : syracuseStep 1800887 = 2701331) B2701331
theorem B1800907 : Blo 1800101 1800907 := bstep (se 1 (by rfl) ⟨1350680, by rfl⟩ : syracuseStep 1800907 = 2701361) B2701361
theorem B2702027 : Blo 1800101 2702027 := bstep (se 1 (by rfl) ⟨2026520, by rfl⟩ : syracuseStep 2702027 = 4053041) B4053041
theorem B1800919 : Blo 1800101 1800919 := bstep (se 1 (by rfl) ⟨1350689, by rfl⟩ : syracuseStep 1800919 = 2701379) B2701379
theorem B2702039 : Blo 1800101 2702039 := bstep (se 1 (by rfl) ⟨2026529, by rfl⟩ : syracuseStep 2702039 = 4053059) B4053059
theorem B1800939 : Blo 1800101 1800939 := bstep (se 1 (by rfl) ⟨1350704, by rfl⟩ : syracuseStep 1800939 = 2701409) B2701409
theorem B1800951 : Blo 1800101 1800951 := bstep (se 1 (by rfl) ⟨1350713, by rfl⟩ : syracuseStep 1800951 = 2701427) B2701427
theorem B1800971 : Blo 1800101 1800971 := bstep (se 1 (by rfl) ⟨1350728, by rfl⟩ : syracuseStep 1800971 = 2701457) B2701457
theorem B1800983 : Blo 1800101 1800983 := bstep (se 1 (by rfl) ⟨1350737, by rfl⟩ : syracuseStep 1800983 = 2701475) B2701475
theorem B2702105 : Blo 1800101 2702105 := bstep (se 2 (by rfl) ⟨1013289, by rfl⟩ : syracuseStep 2702105 = 2026579) B2026579
theorem B1801003 : Blo 1800101 1801003 := bstep (se 1 (by rfl) ⟨1350752, by rfl⟩ : syracuseStep 1801003 = 2701505) B2701505
theorem B1801015 : Blo 1800101 1801015 := bstep (se 1 (by rfl) ⟨1350761, by rfl⟩ : syracuseStep 1801015 = 2701523) B2701523
theorem B1801035 : Blo 1800101 1801035 := bstep (se 1 (by rfl) ⟨1350776, by rfl⟩ : syracuseStep 1801035 = 2701553) B2701553
theorem B1801047 : Blo 1800101 1801047 := bstep (se 1 (by rfl) ⟨1350785, by rfl⟩ : syracuseStep 1801047 = 2701571) B2701571
theorem B1801067 : Blo 1800101 1801067 := bstep (se 1 (by rfl) ⟨1350800, by rfl⟩ : syracuseStep 1801067 = 2701601) B2701601
theorem B1801079 : Blo 1800101 1801079 := bstep (se 1 (by rfl) ⟨1350809, by rfl⟩ : syracuseStep 1801079 = 2701619) B2701619
theorem B1801099 : Blo 1800101 1801099 := bstep (se 1 (by rfl) ⟨1350824, by rfl⟩ : syracuseStep 1801099 = 2701649) B2701649
theorem B2702219 : Blo 1800101 2702219 := bstep (se 1 (by rfl) ⟨2026664, by rfl⟩ : syracuseStep 2702219 = 4053329) B4053329
theorem B1801111 : Blo 1800101 1801111 := bstep (se 1 (by rfl) ⟨1350833, by rfl⟩ : syracuseStep 1801111 = 2701667) B2701667
theorem B2702231 : Blo 1800101 2702231 := bstep (se 1 (by rfl) ⟨2026673, by rfl⟩ : syracuseStep 2702231 = 4053347) B4053347
theorem B1801131 : Blo 1800101 1801131 := bstep (se 1 (by rfl) ⟨1350848, by rfl⟩ : syracuseStep 1801131 = 2701697) B2701697
theorem B1801143 : Blo 1800101 1801143 := bstep (se 1 (by rfl) ⟨1350857, by rfl⟩ : syracuseStep 1801143 = 2701715) B2701715
theorem B1801163 : Blo 1800101 1801163 := bstep (se 1 (by rfl) ⟨1350872, by rfl⟩ : syracuseStep 1801163 = 2701745) B2701745
theorem B1801175 : Blo 1800101 1801175 := bstep (se 1 (by rfl) ⟨1350881, by rfl⟩ : syracuseStep 1801175 = 2701763) B2701763
theorem B2702297 : Blo 1800101 2702297 := bstep (se 2 (by rfl) ⟨1013361, by rfl⟩ : syracuseStep 2702297 = 2026723) B2026723
theorem B1801195 : Blo 1800101 1801195 := bstep (se 1 (by rfl) ⟨1350896, by rfl⟩ : syracuseStep 1801195 = 2701793) B2701793
theorem B1801207 : Blo 1800101 1801207 := bstep (se 1 (by rfl) ⟨1350905, by rfl⟩ : syracuseStep 1801207 = 2701811) B2701811
theorem B1801227 : Blo 1800101 1801227 := bstep (se 1 (by rfl) ⟨1350920, by rfl⟩ : syracuseStep 1801227 = 2701841) B2701841
theorem B1801239 : Blo 1800101 1801239 := bstep (se 1 (by rfl) ⟨1350929, by rfl⟩ : syracuseStep 1801239 = 2701859) B2701859
theorem B1801259 : Blo 1800101 1801259 := bstep (se 1 (by rfl) ⟨1350944, by rfl⟩ : syracuseStep 1801259 = 2701889) B2701889
theorem B1801271 : Blo 1800101 1801271 := bstep (se 1 (by rfl) ⟨1350953, by rfl⟩ : syracuseStep 1801271 = 2701907) B2701907
theorem B1801291 : Blo 1800101 1801291 := bstep (se 1 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 1801291 = 2701937) B2701937
theorem B2563159 : Blo 1800101 2563159 := bstep (se 1 (by rfl) ⟨1922369, by rfl⟩ : syracuseStep 2563159 = 3844739) B3844739
theorem B1801303 : Blo 1800101 1801303 := bstep (se 1 (by rfl) ⟨1350977, by rfl⟩ : syracuseStep 1801303 = 2701955) B2701955
theorem B1801323 : Blo 1800101 1801323 := bstep (se 1 (by rfl) ⟨1350992, by rfl⟩ : syracuseStep 1801323 = 2701985) B2701985
theorem B1801335 : Blo 1800101 1801335 := bstep (se 1 (by rfl) ⟨1351001, by rfl⟩ : syracuseStep 1801335 = 2702003) B2702003
theorem B1801355 : Blo 1800101 1801355 := bstep (se 1 (by rfl) ⟨1351016, by rfl⟩ : syracuseStep 1801355 = 2702033) B2702033
theorem B6077591 : Blo 1800101 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B1801367 : Blo 1800101 1801367 := bstep (se 1 (by rfl) ⟨1351025, by rfl⟩ : syracuseStep 1801367 = 2702051) B2702051
theorem B1801387 : Blo 1800101 1801387 := bstep (se 1 (by rfl) ⟨1351040, by rfl⟩ : syracuseStep 1801387 = 2702081) B2702081
theorem B1801399 : Blo 1800101 1801399 := bstep (se 1 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 1801399 = 2702099) B2702099
theorem B3038411 : Blo 1800101 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B4685003 : Blo 1800101 4685003 := bstep (se 1 (by rfl) ⟨3513752, by rfl⟩ : syracuseStep 4685003 = 7027505) B7027505
theorem B1801419 : Blo 1800101 1801419 := bstep (se 1 (by rfl) ⟨1351064, by rfl⟩ : syracuseStep 1801419 = 2702129) B2702129
theorem B1801431 : Blo 1800101 1801431 := bstep (se 1 (by rfl) ⟨1351073, by rfl⟩ : syracuseStep 1801431 = 2702147) B2702147
theorem B8215769 : Blo 1800101 8215769 := bstep (se 2 (by rfl) ⟨3080913, by rfl⟩ : syracuseStep 8215769 = 6161827) B6161827
theorem B1801451 : Blo 1800101 1801451 := bstep (se 1 (by rfl) ⟨1351088, by rfl⟩ : syracuseStep 1801451 = 2702177) B2702177
theorem B1801463 : Blo 1800101 1801463 := bstep (se 1 (by rfl) ⟨1351097, by rfl⟩ : syracuseStep 1801463 = 2702195) B2702195
theorem B1801483 : Blo 1800101 1801483 := bstep (se 1 (by rfl) ⟨1351112, by rfl⟩ : syracuseStep 1801483 = 2702225) B2702225
theorem B7691543 : Blo 1800101 7691543 := bstep (se 1 (by rfl) ⟨5768657, by rfl⟩ : syracuseStep 7691543 = 11537315) B11537315
theorem B1801495 : Blo 1800101 1801495 := bstep (se 1 (by rfl) ⟨1351121, by rfl⟩ : syracuseStep 1801495 = 2702243) B2702243
theorem B1801515 : Blo 1800101 1801515 := bstep (se 1 (by rfl) ⟨1351136, by rfl⟩ : syracuseStep 1801515 = 2702273) B2702273
theorem B1801527 : Blo 1800101 1801527 := bstep (se 1 (by rfl) ⟨1351145, by rfl⟩ : syracuseStep 1801527 = 2702291) B2702291
theorem B3038539 : Blo 1800101 3038539 := bstep (se 1 (by rfl) ⟨2278904, by rfl⟩ : syracuseStep 3038539 = 4557809) B4557809
theorem B1801547 : Blo 1800101 1801547 := bstep (se 1 (by rfl) ⟨1351160, by rfl⟩ : syracuseStep 1801547 = 2702321) B2702321
theorem B1801559 : Blo 1800101 1801559 := bstep (se 1 (by rfl) ⟨1351169, by rfl⟩ : syracuseStep 1801559 = 2702339) B2702339
theorem B1801579 : Blo 1800101 1801579 := bstep (se 1 (by rfl) ⟨1351184, by rfl⟩ : syracuseStep 1801579 = 2702369) B2702369
theorem B1801591 : Blo 1800101 1801591 := bstep (se 1 (by rfl) ⟨1351193, by rfl⟩ : syracuseStep 1801591 = 2702387) B2702387
theorem B3751319 : Blo 1800101 3751319 := bstep (se 1 (by rfl) ⟨2813489, by rfl⟩ : syracuseStep 3751319 = 5626979) B5626979
theorem B3038681 : Blo 1800101 3038681 := bstep (se 2 (by rfl) ⟨1139505, by rfl⟩ : syracuseStep 3038681 = 2279011) B2279011
theorem B3898867 : Blo 1800101 3898867 := bstep (se 1 (by rfl) ⟨2924150, by rfl⟩ : syracuseStep 3898867 = 5848301) B5848301
theorem B6839873 : Blo 1800101 6839873 := bstep (se 2 (by rfl) ⟨2564952, by rfl⟩ : syracuseStep 6839873 = 5129905) B5129905
theorem B3038809 : Blo 1800101 3038809 := bstep (se 2 (by rfl) ⟨1139553, by rfl⟩ : syracuseStep 3038809 = 2279107) B2279107
theorem B9870979 : Blo 1800101 9870979 := bstep (se 1 (by rfl) ⟨7403234, by rfl⟩ : syracuseStep 9870979 = 14806469) B14806469
theorem B23084675 : Blo 1800101 23084675 := bstep (se 1 (by rfl) ⟨17313506, by rfl⟩ : syracuseStep 23084675 = 34627013) B34627013
theorem B6078131 : Blo 1800101 6078131 := bstep (se 1 (by rfl) ⟨4558598, by rfl⟩ : syracuseStep 6078131 = 9117197) B9117197
theorem B20790989 : Blo 1800101 20790989 := bstep (se 3 (by rfl) ⟨3898310, by rfl⟩ : syracuseStep 20790989 = 7796621) B7796621
theorem B6930269 : Blo 1800101 6930269 := bstep (se 3 (by rfl) ⟨1299425, by rfl⟩ : syracuseStep 6930269 = 2598851) B2598851
theorem B15384451 : Blo 1800101 15384451 := bstep (se 1 (by rfl) ⟨11538338, by rfl⟩ : syracuseStep 15384451 = 23076677) B23076677
theorem B6078401 : Blo 1800101 6078401 := bstep (se 2 (by rfl) ⟨2279400, by rfl⟩ : syracuseStep 6078401 = 4558801) B4558801
theorem B3039275 : Blo 1800101 3039275 := bstep (se 1 (by rfl) ⟨2279456, by rfl⟩ : syracuseStep 3039275 = 4558913) B4558913
theorem B2162747 : Blo 1800101 2162747 := bstep (se 1 (by rfl) ⟨1622060, by rfl⟩ : syracuseStep 2162747 = 3244121) B3244121
theorem B4325647 : Blo 1800101 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B17309969 : Blo 1800101 17309969 := bstep (se 2 (by rfl) ⟨6491238, by rfl⟩ : syracuseStep 17309969 = 12982477) B12982477
theorem B6078779 : Blo 1800101 6078779 := bstep (se 1 (by rfl) ⟨4559084, by rfl⟩ : syracuseStep 6078779 = 9118169) B9118169
theorem B3039673 : Blo 1800101 3039673 := bstep (se 2 (by rfl) ⟨1139877, by rfl⟩ : syracuseStep 3039673 = 2279755) B2279755
theorem B12984785 : Blo 1800101 12984785 := bstep (se 2 (by rfl) ⟨4869294, by rfl⟩ : syracuseStep 12984785 = 9738589) B9738589
theorem B4866571 : Blo 1800101 4866571 := bstep (se 1 (by rfl) ⟨3649928, by rfl⟩ : syracuseStep 4866571 = 7299857) B7299857
theorem B10256939 : Blo 1800101 10256939 := bstep (se 1 (by rfl) ⟨7692704, by rfl⟩ : syracuseStep 10256939 = 15385409) B15385409
theorem B11543107 : Blo 1800101 11543107 := bstep (se 1 (by rfl) ⟨8657330, by rfl⟩ : syracuseStep 11543107 = 17314661) B17314661
theorem B4326023 : Blo 1800101 4326023 := bstep (se 1 (by rfl) ⟨3244517, by rfl⟩ : syracuseStep 4326023 = 6489035) B6489035
theorem B2163343 : Blo 1800101 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B21070529 : Blo 1800101 21070529 := bstep (se 2 (by rfl) ⟨7901448, by rfl⟩ : syracuseStep 21070529 = 15802897) B15802897
theorem B6079265 : Blo 1800101 6079265 := bstep (se 2 (by rfl) ⟨2279724, by rfl⟩ : syracuseStep 6079265 = 4559449) B4559449
theorem B4326263 : Blo 1800101 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B2278459 : Blo 1800101 2278459 := bstep (se 1 (by rfl) ⟨1708844, by rfl⟩ : syracuseStep 2278459 = 3417689) B3417689
theorem B10003517 : Blo 1800101 10003517 := bstep (se 3 (by rfl) ⟨1875659, by rfl⟩ : syracuseStep 10003517 = 3751319) B3751319
theorem B5129335 : Blo 1800101 5129335 := bstep (se 1 (by rfl) ⟨3847001, by rfl⟩ : syracuseStep 5129335 = 7694003) B7694003
theorem B6079859 : Blo 1800101 6079859 := bstep (se 1 (by rfl) ⟨4559894, by rfl⟩ : syracuseStep 6079859 = 9119789) B9119789
theorem B3245447 : Blo 1800101 3245447 := bstep (se 1 (by rfl) ⟨2434085, by rfl⟩ : syracuseStep 3245447 = 4868171) B4868171
theorem B3417491 : Blo 1800101 3417491 := bstep (se 1 (by rfl) ⟨2563118, by rfl⟩ : syracuseStep 3417491 = 5126237) B5126237
theorem B6489497 : Blo 1800101 6489497 := bstep (se 2 (by rfl) ⟨2433561, by rfl⟩ : syracuseStep 6489497 = 4867123) B4867123
theorem B2434475 : Blo 1800101 2434475 := bstep (se 1 (by rfl) ⟨1825856, by rfl⟩ : syracuseStep 2434475 = 3651713) B3651713
theorem B8652217 : Blo 1800101 8652217 := bstep (se 2 (by rfl) ⟨3244581, by rfl⟩ : syracuseStep 8652217 = 6489163) B6489163
theorem B2082235 : Blo 1800101 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B3417545 : Blo 1800101 3417545 := bstep (se 2 (by rfl) ⟨1281579, by rfl⟩ : syracuseStep 3417545 = 2563159) B2563159
theorem B3417643 : Blo 1800101 3417643 := bstep (se 1 (by rfl) ⟨2563232, by rfl⟩ : syracuseStep 3417643 = 5126465) B5126465
theorem B2278955 : Blo 1800101 2278955 := bstep (se 1 (by rfl) ⟨1709216, by rfl⟩ : syracuseStep 2278955 = 3418433) B3418433
theorem B32056931 : Blo 1800101 32056931 := bstep (se 1 (by rfl) ⟨24042698, by rfl⟩ : syracuseStep 32056931 = 48085397) B48085397
theorem B4327031 : Blo 1800101 4327031 := bstep (se 1 (by rfl) ⟨3245273, by rfl⟩ : syracuseStep 4327031 = 6490547) B6490547
theorem B7399031 : Blo 1800101 7399031 := bstep (se 1 (by rfl) ⟨5549273, by rfl⟩ : syracuseStep 7399031 = 11098547) B11098547
theorem B5473993 : Blo 1800101 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B3417871 : Blo 1800101 3417871 := bstep (se 1 (by rfl) ⟨2563403, by rfl⟩ : syracuseStep 3417871 = 5126807) B5126807
theorem B4867955 : Blo 1800101 4867955 := bstep (se 1 (by rfl) ⟨3650966, by rfl⟩ : syracuseStep 4867955 = 7301933) B7301933
theorem B10258397 : Blo 1800101 10258397 := bstep (se 3 (by rfl) ⟨1923449, by rfl⟩ : syracuseStep 10258397 = 3846899) B3846899
theorem B2279431 : Blo 1800101 2279431 := bstep (se 1 (by rfl) ⟨1709573, by rfl⟩ : syracuseStep 2279431 = 3419147) B3419147
theorem B4327435 : Blo 1800101 4327435 := bstep (se 1 (by rfl) ⟨3245576, by rfl⟩ : syracuseStep 4327435 = 6491153) B6491153
theorem B2025607 : Blo 1800101 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B3123335 : Blo 1800101 3123335 := bstep (se 1 (by rfl) ⟨2342501, by rfl⟩ : syracuseStep 3123335 = 4685003) B4685003
theorem B4622521 : Blo 1800101 4622521 := bstep (se 2 (by rfl) ⟨1733445, by rfl⟩ : syracuseStep 4622521 = 3466891) B3466891
theorem B24971537 : Blo 1800101 24971537 := bstep (se 2 (by rfl) ⟨9364326, by rfl⟩ : syracuseStep 24971537 = 18728653) B18728653
theorem B2025787 : Blo 1800101 2025787 := bstep (se 1 (by rfl) ⟨1519340, by rfl⟩ : syracuseStep 2025787 = 3038681) B3038681
theorem B2279927 : Blo 1800101 2279927 := bstep (se 1 (by rfl) ⟨1709945, by rfl⟩ : syracuseStep 2279927 = 3419891) B3419891
theorem B4557323 : Blo 1800101 4557323 := bstep (se 1 (by rfl) ⟨3417992, by rfl⟩ : syracuseStep 4557323 = 6835985) B6835985
theorem B2280079 : Blo 1800101 2280079 := bstep (se 1 (by rfl) ⟨1710059, by rfl⟩ : syracuseStep 2280079 = 3420119) B3420119
theorem B2026255 : Blo 1800101 2026255 := bstep (se 1 (by rfl) ⟨1519691, by rfl⟩ : syracuseStep 2026255 = 3039383) B3039383
theorem B4869121 : Blo 1800101 4869121 := bstep (se 2 (by rfl) ⟨1825920, by rfl⟩ : syracuseStep 4869121 = 3651841) B3651841
theorem B6835211 : Blo 1800101 6835211 := bstep (se 1 (by rfl) ⟨5126408, by rfl⟩ : syracuseStep 6835211 = 10252817) B10252817
theorem B8653891 : Blo 1800101 8653891 := bstep (se 1 (by rfl) ⟨6490418, by rfl⟩ : syracuseStep 8653891 = 12980837) B12980837
theorem B4557971 : Blo 1800101 4557971 := bstep (se 1 (by rfl) ⟨3418478, by rfl⟩ : syracuseStep 4557971 = 6836957) B6836957
theorem B2026759 : Blo 1800101 2026759 := bstep (se 1 (by rfl) ⟨1520069, by rfl⟩ : syracuseStep 2026759 = 3040139) B3040139
theorem B3419435 : Blo 1800101 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B5270903 : Blo 1800101 5270903 := bstep (se 1 (by rfl) ⟨3953177, by rfl⟩ : syracuseStep 5270903 = 7906355) B7906355
theorem B4050323 : Blo 1800101 4050323 := bstep (se 1 (by rfl) ⟨3037742, by rfl⟩ : syracuseStep 4050323 = 6075485) B6075485
theorem B4558265 : Blo 1800101 4558265 := bstep (se 2 (by rfl) ⟨1709349, by rfl⟩ : syracuseStep 4558265 = 3418699) B3418699
theorem B4050377 : Blo 1800101 4050377 := bstep (se 2 (by rfl) ⟨1518891, by rfl⟩ : syracuseStep 4050377 = 3037783) B3037783
theorem B20508227 : Blo 1800101 20508227 := bstep (se 1 (by rfl) ⟨15381170, by rfl⟩ : syracuseStep 20508227 = 30762341) B30762341
theorem B22212163 : Blo 1800101 22212163 := bstep (se 1 (by rfl) ⟨16659122, by rfl⟩ : syracuseStep 22212163 = 33318245) B33318245
theorem B10252291 : Blo 1800101 10252291 := bstep (se 1 (by rfl) ⟨7689218, by rfl⟩ : syracuseStep 10252291 = 15378437) B15378437
theorem B4558963 : Blo 1800101 4558963 := bstep (se 1 (by rfl) ⟨3419222, by rfl⟩ : syracuseStep 4558963 = 6838445) B6838445
theorem B4051079 : Blo 1800101 4051079 := bstep (se 1 (by rfl) ⟨3038309, by rfl⟩ : syracuseStep 4051079 = 6076619) B6076619
theorem B13856969 : Blo 1800101 13856969 := bstep (se 2 (by rfl) ⟨5196363, by rfl⟩ : syracuseStep 13856969 = 10392727) B10392727
theorem B4559105 : Blo 1800101 4559105 := bstep (se 2 (by rfl) ⟨1709664, by rfl⟩ : syracuseStep 4559105 = 3419329) B3419329
theorem B7401743 : Blo 1800101 7401743 := bstep (se 1 (by rfl) ⟨5551307, by rfl⟩ : syracuseStep 7401743 = 11102615) B11102615
theorem B4051259 : Blo 1800101 4051259 := bstep (se 1 (by rfl) ⟨3038444, by rfl⟩ : syracuseStep 4051259 = 6076889) B6076889
theorem B4051385 : Blo 1800101 4051385 := bstep (se 2 (by rfl) ⟨1519269, by rfl⟩ : syracuseStep 4051385 = 3038539) B3038539
theorem B20787677 : Blo 1800101 20787677 := bstep (se 3 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 20787677 = 7795379) B7795379
theorem B15381035 : Blo 1800101 15381035 := bstep (se 1 (by rfl) ⟨11535776, by rfl⟩ : syracuseStep 15381035 = 23071553) B23071553
theorem B5198489 : Blo 1800101 5198489 := bstep (se 2 (by rfl) ⟨1949433, by rfl⟩ : syracuseStep 5198489 = 3898867) B3898867
theorem B4559561 : Blo 1800101 4559561 := bstep (se 2 (by rfl) ⟨1709835, by rfl⟩ : syracuseStep 4559561 = 3419671) B3419671
theorem B4051727 : Blo 1800101 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B4051745 : Blo 1800101 4051745 := bstep (se 2 (by rfl) ⟨1519404, by rfl⟩ : syracuseStep 4051745 = 3038809) B3038809
theorem B5477179 : Blo 1800101 5477179 := bstep (se 1 (by rfl) ⟨4107884, by rfl⟩ : syracuseStep 5477179 = 8215769) B8215769
theorem B13161305 : Blo 1800101 13161305 := bstep (se 2 (by rfl) ⟨4935489, by rfl⟩ : syracuseStep 13161305 = 9870979) B9870979
theorem B2700167 : Blo 1800101 2700167 := bstep (se 1 (by rfl) ⟨2025125, by rfl⟩ : syracuseStep 2700167 = 4050251) B4050251
theorem B2700203 : Blo 1800101 2700203 := bstep (se 1 (by rfl) ⟨2025152, by rfl⟩ : syracuseStep 2700203 = 4050305) B4050305
theorem B2700233 : Blo 1800101 2700233 := bstep (se 2 (by rfl) ⟨1012587, by rfl⟩ : syracuseStep 2700233 = 2025175) B2025175
theorem B9999389 : Blo 1800101 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B4559915 : Blo 1800101 4559915 := bstep (se 1 (by rfl) ⟨3419936, by rfl⟩ : syracuseStep 4559915 = 6839873) B6839873
theorem B2700347 : Blo 1800101 2700347 := bstep (se 1 (by rfl) ⟨2025260, by rfl⟩ : syracuseStep 2700347 = 4050521) B4050521
theorem B15389783 : Blo 1800101 15389783 := bstep (se 1 (by rfl) ⟨11542337, by rfl⟩ : syracuseStep 15389783 = 23084675) B23084675
theorem B2700407 : Blo 1800101 2700407 := bstep (se 1 (by rfl) ⟨2025305, by rfl⟩ : syracuseStep 2700407 = 4050611) B4050611
theorem B4052087 : Blo 1800101 4052087 := bstep (se 1 (by rfl) ⟨3039065, by rfl⟩ : syracuseStep 4052087 = 6078131) B6078131
theorem B2700431 : Blo 1800101 2700431 := bstep (se 1 (by rfl) ⟨2025323, by rfl⟩ : syracuseStep 2700431 = 4050647) B4050647
theorem B2700473 : Blo 1800101 2700473 := bstep (se 2 (by rfl) ⟨1012677, by rfl⟩ : syracuseStep 2700473 = 2025355) B2025355
theorem B6075593 : Blo 1800101 6075593 := bstep (se 2 (by rfl) ⟨2278347, by rfl⟩ : syracuseStep 6075593 = 4556695) B4556695
theorem B2700551 : Blo 1800101 2700551 := bstep (se 1 (by rfl) ⟨2025413, by rfl⟩ : syracuseStep 2700551 = 4050827) B4050827
theorem B2700587 : Blo 1800101 2700587 := bstep (se 1 (by rfl) ⟨2025440, by rfl⟩ : syracuseStep 2700587 = 4050881) B4050881
theorem B4052267 : Blo 1800101 4052267 := bstep (se 1 (by rfl) ⟨3039200, by rfl⟩ : syracuseStep 4052267 = 6078401) B6078401
theorem B2700617 : Blo 1800101 2700617 := bstep (se 2 (by rfl) ⟨1012731, by rfl⟩ : syracuseStep 2700617 = 2025463) B2025463
theorem B78968195 : Blo 1800101 78968195 := bstep (se 1 (by rfl) ⟨59226146, by rfl⟩ : syracuseStep 78968195 = 118452293) B118452293
theorem B2700731 : Blo 1800101 2700731 := bstep (se 1 (by rfl) ⟨2025548, by rfl⟩ : syracuseStep 2700731 = 4051097) B4051097
theorem B15390161 : Blo 1800101 15390161 := bstep (se 2 (by rfl) ⟨5771310, by rfl⟩ : syracuseStep 15390161 = 11542621) B11542621
theorem B2700791 : Blo 1800101 2700791 := bstep (se 1 (by rfl) ⟨2025593, by rfl⟩ : syracuseStep 2700791 = 4051187) B4051187
theorem B2700815 : Blo 1800101 2700815 := bstep (se 1 (by rfl) ⟨2025611, by rfl⟩ : syracuseStep 2700815 = 4051223) B4051223
theorem B2700857 : Blo 1800101 2700857 := bstep (se 2 (by rfl) ⟨1012821, by rfl⟩ : syracuseStep 2700857 = 2025643) B2025643
theorem B2700935 : Blo 1800101 2700935 := bstep (se 1 (by rfl) ⟨2025701, by rfl⟩ : syracuseStep 2700935 = 4051403) B4051403
theorem B4052627 : Blo 1800101 4052627 := bstep (se 1 (by rfl) ⟨3039470, by rfl⟩ : syracuseStep 4052627 = 6078941) B6078941
theorem B2700971 : Blo 1800101 2700971 := bstep (se 1 (by rfl) ⟨2025728, by rfl⟩ : syracuseStep 2700971 = 4051457) B4051457
theorem B2701001 : Blo 1800101 2701001 := bstep (se 2 (by rfl) ⟨1012875, by rfl⟩ : syracuseStep 2701001 = 2025751) B2025751
theorem B4052681 : Blo 1800101 4052681 := bstep (se 2 (by rfl) ⟨1519755, by rfl⟩ : syracuseStep 4052681 = 3039511) B3039511
theorem B2701115 : Blo 1800101 2701115 := bstep (se 1 (by rfl) ⟨2025836, by rfl⟩ : syracuseStep 2701115 = 4051673) B4051673
theorem B10950515 : Blo 1800101 10950515 := bstep (se 1 (by rfl) ⟨8212886, by rfl⟩ : syracuseStep 10950515 = 16425773) B16425773
theorem B2701175 : Blo 1800101 2701175 := bstep (se 1 (by rfl) ⟨2025881, by rfl⟩ : syracuseStep 2701175 = 4051763) B4051763
theorem B6076295 : Blo 1800101 6076295 := bstep (se 1 (by rfl) ⟨4557221, by rfl⟩ : syracuseStep 6076295 = 9114443) B9114443
theorem B2701199 : Blo 1800101 2701199 := bstep (se 1 (by rfl) ⟨2025899, by rfl⟩ : syracuseStep 2701199 = 4051799) B4051799
theorem B9115577 : Blo 1800101 9115577 := bstep (se 2 (by rfl) ⟨3418341, by rfl⟩ : syracuseStep 9115577 = 6836683) B6836683
theorem B2701241 : Blo 1800101 2701241 := bstep (se 2 (by rfl) ⟨1012965, by rfl⟩ : syracuseStep 2701241 = 2025931) B2025931
theorem B1800123 : Blo 1800101 1800123 := bstep (se 1 (by rfl) ⟨1350092, by rfl⟩ : syracuseStep 1800123 = 2700185) B2700185
theorem B4446137 : Blo 1800101 4446137 := bstep (se 2 (by rfl) ⟨1667301, by rfl⟩ : syracuseStep 4446137 = 3334603) B3334603
theorem B2406391 : Blo 1800101 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B1800199 : Blo 1800101 1800199 := bstep (se 1 (by rfl) ⟨1350149, by rfl⟩ : syracuseStep 1800199 = 2700299) B2700299
theorem B2701319 : Blo 1800101 2701319 := bstep (se 1 (by rfl) ⟨2025989, by rfl⟩ : syracuseStep 2701319 = 4051979) B4051979
theorem B1800207 : Blo 1800101 1800207 := bstep (se 1 (by rfl) ⟨1350155, by rfl⟩ : syracuseStep 1800207 = 2700311) B2700311
theorem B2701355 : Blo 1800101 2701355 := bstep (se 1 (by rfl) ⟨2026016, by rfl⟩ : syracuseStep 2701355 = 4052033) B4052033
theorem B1800251 : Blo 1800101 1800251 := bstep (se 1 (by rfl) ⟨1350188, by rfl⟩ : syracuseStep 1800251 = 2700377) B2700377
theorem B2701385 : Blo 1800101 2701385 := bstep (se 2 (by rfl) ⟨1013019, by rfl⟩ : syracuseStep 2701385 = 2026039) B2026039
theorem B1800327 : Blo 1800101 1800327 := bstep (se 1 (by rfl) ⟨1350245, by rfl⟩ : syracuseStep 1800327 = 2700491) B2700491
theorem B1800335 : Blo 1800101 1800335 := bstep (se 1 (by rfl) ⟨1350251, by rfl⟩ : syracuseStep 1800335 = 2700503) B2700503
theorem B1800379 : Blo 1800101 1800379 := bstep (se 1 (by rfl) ⟨1350284, by rfl⟩ : syracuseStep 1800379 = 2700569) B2700569
theorem B2701499 : Blo 1800101 2701499 := bstep (se 1 (by rfl) ⟨2026124, by rfl⟩ : syracuseStep 2701499 = 4052249) B4052249
theorem B2701559 : Blo 1800101 2701559 := bstep (se 1 (by rfl) ⟨2026169, by rfl⟩ : syracuseStep 2701559 = 4052339) B4052339
theorem B6076673 : Blo 1800101 6076673 := bstep (se 2 (by rfl) ⟨2278752, by rfl⟩ : syracuseStep 6076673 = 4557505) B4557505
theorem B1800455 : Blo 1800101 1800455 := bstep (se 1 (by rfl) ⟨1350341, by rfl⟩ : syracuseStep 1800455 = 2700683) B2700683
theorem B1800463 : Blo 1800101 1800463 := bstep (se 1 (by rfl) ⟨1350347, by rfl⟩ : syracuseStep 1800463 = 2700695) B2700695
theorem B2701583 : Blo 1800101 2701583 := bstep (se 1 (by rfl) ⟨2026187, by rfl⟩ : syracuseStep 2701583 = 4052375) B4052375
theorem B2701625 : Blo 1800101 2701625 := bstep (se 2 (by rfl) ⟨1013109, by rfl⟩ : syracuseStep 2701625 = 2026219) B2026219
theorem B1800507 : Blo 1800101 1800507 := bstep (se 1 (by rfl) ⟨1350380, by rfl⟩ : syracuseStep 1800507 = 2700761) B2700761
theorem B10254707 : Blo 1800101 10254707 := bstep (se 1 (by rfl) ⟨7691030, by rfl⟩ : syracuseStep 10254707 = 15382061) B15382061
theorem B7797107 : Blo 1800101 7797107 := bstep (se 1 (by rfl) ⟨5847830, by rfl⟩ : syracuseStep 7797107 = 11695661) B11695661
theorem B1800583 : Blo 1800101 1800583 := bstep (se 1 (by rfl) ⟨1350437, by rfl⟩ : syracuseStep 1800583 = 2700875) B2700875
theorem B2701703 : Blo 1800101 2701703 := bstep (se 1 (by rfl) ⟨2026277, by rfl⟩ : syracuseStep 2701703 = 4052555) B4052555
theorem B1923463 : Blo 1800101 1923463 := bstep (se 1 (by rfl) ⟨1442597, by rfl⟩ : syracuseStep 1923463 = 2885195) B2885195
theorem B4053383 : Blo 1800101 4053383 := bstep (se 1 (by rfl) ⟨3040037, by rfl⟩ : syracuseStep 4053383 = 6080075) B6080075
theorem B1800591 : Blo 1800101 1800591 := bstep (se 1 (by rfl) ⟨1350443, by rfl⟩ : syracuseStep 1800591 = 2700887) B2700887
theorem B6928793 : Blo 1800101 6928793 := bstep (se 2 (by rfl) ⟨2598297, by rfl⟩ : syracuseStep 6928793 = 5196595) B5196595
theorem B2701739 : Blo 1800101 2701739 := bstep (se 1 (by rfl) ⟨2026304, by rfl⟩ : syracuseStep 2701739 = 4052609) B4052609
theorem B1800635 : Blo 1800101 1800635 := bstep (se 1 (by rfl) ⟨1350476, by rfl⟩ : syracuseStep 1800635 = 2700953) B2700953
theorem B2701769 : Blo 1800101 2701769 := bstep (se 2 (by rfl) ⟨1013163, by rfl⟩ : syracuseStep 2701769 = 2026327) B2026327
theorem B1800711 : Blo 1800101 1800711 := bstep (se 1 (by rfl) ⟨1350533, by rfl⟩ : syracuseStep 1800711 = 2701067) B2701067
theorem B1800719 : Blo 1800101 1800719 := bstep (se 1 (by rfl) ⟨1350539, by rfl⟩ : syracuseStep 1800719 = 2701079) B2701079
theorem B1800763 : Blo 1800101 1800763 := bstep (se 1 (by rfl) ⟨1350572, by rfl⟩ : syracuseStep 1800763 = 2701145) B2701145
theorem B2701883 : Blo 1800101 2701883 := bstep (se 1 (by rfl) ⟨2026412, by rfl⟩ : syracuseStep 2701883 = 4052825) B4052825
theorem B4053563 : Blo 1800101 4053563 := bstep (se 1 (by rfl) ⟨3040172, by rfl⟩ : syracuseStep 4053563 = 6080345) B6080345
theorem B2701943 : Blo 1800101 2701943 := bstep (se 1 (by rfl) ⟨2026457, by rfl⟩ : syracuseStep 2701943 = 4052915) B4052915
theorem B1800839 : Blo 1800101 1800839 := bstep (se 1 (by rfl) ⟨1350629, by rfl⟩ : syracuseStep 1800839 = 2701259) B2701259
theorem B3652231 : Blo 1800101 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B1800847 : Blo 1800101 1800847 := bstep (se 1 (by rfl) ⟨1350635, by rfl⟩ : syracuseStep 1800847 = 2701271) B2701271
theorem B2701967 : Blo 1800101 2701967 := bstep (se 1 (by rfl) ⟨2026475, by rfl⟩ : syracuseStep 2701967 = 4052951) B4052951
theorem B2702009 : Blo 1800101 2702009 := bstep (se 2 (by rfl) ⟨1013253, by rfl⟩ : syracuseStep 2702009 = 2026507) B2026507
theorem B1800891 : Blo 1800101 1800891 := bstep (se 1 (by rfl) ⟨1350668, by rfl⟩ : syracuseStep 1800891 = 2701337) B2701337
theorem B1800967 : Blo 1800101 1800967 := bstep (se 1 (by rfl) ⟨1350725, by rfl⟩ : syracuseStep 1800967 = 2701451) B2701451
theorem B2702087 : Blo 1800101 2702087 := bstep (se 1 (by rfl) ⟨2026565, by rfl⟩ : syracuseStep 2702087 = 4053131) B4053131
theorem B1800975 : Blo 1800101 1800975 := bstep (se 1 (by rfl) ⟨1350731, by rfl⟩ : syracuseStep 1800975 = 2701463) B2701463
theorem B24640291 : Blo 1800101 24640291 := bstep (se 1 (by rfl) ⟨18480218, by rfl⟩ : syracuseStep 24640291 = 36960437) B36960437
theorem B2702123 : Blo 1800101 2702123 := bstep (se 1 (by rfl) ⟨2026592, by rfl⟩ : syracuseStep 2702123 = 4053185) B4053185
theorem B1801019 : Blo 1800101 1801019 := bstep (se 1 (by rfl) ⟨1350764, by rfl⟩ : syracuseStep 1801019 = 2701529) B2701529
theorem B6839099 : Blo 1800101 6839099 := bstep (se 1 (by rfl) ⟨5129324, by rfl⟩ : syracuseStep 6839099 = 10258649) B10258649
theorem B2702153 : Blo 1800101 2702153 := bstep (se 2 (by rfl) ⟨1013307, by rfl⟩ : syracuseStep 2702153 = 2026615) B2026615
theorem B3038087 : Blo 1800101 3038087 := bstep (se 1 (by rfl) ⟨2278565, by rfl⟩ : syracuseStep 3038087 = 4557131) B4557131
theorem B5127047 : Blo 1800101 5127047 := bstep (se 1 (by rfl) ⟨3845285, by rfl⟩ : syracuseStep 5127047 = 7690571) B7690571
theorem B1801095 : Blo 1800101 1801095 := bstep (se 1 (by rfl) ⟨1350821, by rfl⟩ : syracuseStep 1801095 = 2701643) B2701643
theorem B1801103 : Blo 1800101 1801103 := bstep (se 1 (by rfl) ⟨1350827, by rfl⟩ : syracuseStep 1801103 = 2701655) B2701655
theorem B1801147 : Blo 1800101 1801147 := bstep (se 1 (by rfl) ⟨1350860, by rfl⟩ : syracuseStep 1801147 = 2701721) B2701721
theorem B2702267 : Blo 1800101 2702267 := bstep (se 1 (by rfl) ⟨2026700, by rfl⟩ : syracuseStep 2702267 = 4053401) B4053401
theorem B2702327 : Blo 1800101 2702327 := bstep (se 1 (by rfl) ⟨2026745, by rfl⟩ : syracuseStep 2702327 = 4053491) B4053491
theorem B1801223 : Blo 1800101 1801223 := bstep (se 1 (by rfl) ⟨1350917, by rfl⟩ : syracuseStep 1801223 = 2701835) B2701835
theorem B1801231 : Blo 1800101 1801231 := bstep (se 1 (by rfl) ⟨1350923, by rfl⟩ : syracuseStep 1801231 = 2701847) B2701847
theorem B2702351 : Blo 1800101 2702351 := bstep (se 1 (by rfl) ⟨2026763, by rfl⟩ : syracuseStep 2702351 = 4053527) B4053527
theorem B6077483 : Blo 1800101 6077483 := bstep (se 1 (by rfl) ⟨4558112, by rfl⟩ : syracuseStep 6077483 = 9116225) B9116225
theorem B2702393 : Blo 1800101 2702393 := bstep (se 2 (by rfl) ⟨1013397, by rfl⟩ : syracuseStep 2702393 = 2026795) B2026795
theorem B1801275 : Blo 1800101 1801275 := bstep (se 1 (by rfl) ⟨1350956, by rfl⟩ : syracuseStep 1801275 = 2701913) B2701913
theorem B1801351 : Blo 1800101 1801351 := bstep (se 1 (by rfl) ⟨1351013, by rfl⟩ : syracuseStep 1801351 = 2702027) B2702027
theorem B1801359 : Blo 1800101 1801359 := bstep (se 1 (by rfl) ⟨1351019, by rfl⟩ : syracuseStep 1801359 = 2702039) B2702039
theorem B1801403 : Blo 1800101 1801403 := bstep (se 1 (by rfl) ⟨1351052, by rfl⟩ : syracuseStep 1801403 = 2702105) B2702105
theorem B9116873 : Blo 1800101 9116873 := bstep (se 2 (by rfl) ⟨3418827, by rfl⟩ : syracuseStep 9116873 = 6837655) B6837655
theorem B1801479 : Blo 1800101 1801479 := bstep (se 1 (by rfl) ⟨1351109, by rfl⟩ : syracuseStep 1801479 = 2702219) B2702219
theorem B1801487 : Blo 1800101 1801487 := bstep (se 1 (by rfl) ⟨1351115, by rfl⟩ : syracuseStep 1801487 = 2702231) B2702231
theorem B6839585 : Blo 1800101 6839585 := bstep (se 2 (by rfl) ⟨2564844, by rfl⟩ : syracuseStep 6839585 = 5129689) B5129689
theorem B1801531 : Blo 1800101 1801531 := bstep (se 1 (by rfl) ⟨1351148, by rfl⟩ : syracuseStep 1801531 = 2702297) B2702297
theorem B5127695 : Blo 1800101 5127695 := bstep (se 1 (by rfl) ⟨3845771, by rfl⟩ : syracuseStep 5127695 = 7691543) B7691543
theorem B3038735 : Blo 1800101 3038735 := bstep (se 1 (by rfl) ⟨2279051, by rfl⟩ : syracuseStep 3038735 = 4558103) B4558103
theorem B10256165 : Blo 1800101 10256165 := bstep (se 4 (by rfl) ⟨961515, by rfl⟩ : syracuseStep 10256165 = 1923031) B1923031
theorem B13860659 : Blo 1800101 13860659 := bstep (se 1 (by rfl) ⟨10395494, by rfl⟩ : syracuseStep 13860659 = 20790989) B20790989
theorem B20512601 : Blo 1800101 20512601 := bstep (se 2 (by rfl) ⟨7692225, by rfl⟩ : syracuseStep 20512601 = 15384451) B15384451
theorem B4620179 : Blo 1800101 4620179 := bstep (se 1 (by rfl) ⟨3465134, by rfl⟩ : syracuseStep 4620179 = 6930269) B6930269
theorem B11255705 : Blo 1800101 11255705 := bstep (se 2 (by rfl) ⟨4220889, by rfl⟩ : syracuseStep 11255705 = 8441779) B8441779
theorem B10952657 : Blo 1800101 10952657 := bstep (se 2 (by rfl) ⟨4107246, by rfl⟩ : syracuseStep 10952657 = 8214493) B8214493
theorem B3039241 : Blo 1800101 3039241 := bstep (se 2 (by rfl) ⟨1139715, by rfl⟩ : syracuseStep 3039241 = 2279431) B2279431
theorem B6078617 : Blo 1800101 6078617 := bstep (se 2 (by rfl) ⟨2279481, by rfl⟩ : syracuseStep 6078617 = 4558963) B4558963
theorem B5767325 : Blo 1800101 5767325 := bstep (se 3 (by rfl) ⟨1081373, by rfl⟩ : syracuseStep 5767325 = 2162747) B2162747
theorem B3039403 : Blo 1800101 3039403 := bstep (se 1 (by rfl) ⟨2279552, by rfl⟩ : syracuseStep 3039403 = 4559105) B4559105
theorem B118464869 : Blo 1800101 118464869 := bstep (se 4 (by rfl) ⟨11106081, by rfl⟩ : syracuseStep 118464869 = 22212163) B22212163
theorem B5767529 : Blo 1800101 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B2884015 : Blo 1800101 2884015 := bstep (se 1 (by rfl) ⟨2163011, by rfl⟩ : syracuseStep 2884015 = 4326023) B4326023
theorem B3465659 : Blo 1800101 3465659 := bstep (se 1 (by rfl) ⟨2599244, by rfl⟩ : syracuseStep 3465659 = 5198489) B5198489
theorem B3039707 : Blo 1800101 3039707 := bstep (se 1 (by rfl) ⟨2279780, by rfl⟩ : syracuseStep 3039707 = 4559561) B4559561
theorem B2564617 : Blo 1800101 2564617 := bstep (se 2 (by rfl) ⟨961731, by rfl⟩ : syracuseStep 2564617 = 1923463) B1923463
theorem B8774203 : Blo 1800101 8774203 := bstep (se 1 (by rfl) ⟨6580652, by rfl⟩ : syracuseStep 8774203 = 13161305) B13161305
theorem B2884175 : Blo 1800101 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B6488761 : Blo 1800101 6488761 := bstep (se 2 (by rfl) ⟨2433285, by rfl⟩ : syracuseStep 6488761 = 4866571) B4866571
theorem B3039943 : Blo 1800101 3039943 := bstep (se 1 (by rfl) ⟨2279957, by rfl⟩ : syracuseStep 3039943 = 4559915) B4559915
theorem B6669011 : Blo 1800101 6669011 := bstep (se 1 (by rfl) ⟨5001758, by rfl⟩ : syracuseStep 6669011 = 10003517) B10003517
theorem B9118493 : Blo 1800101 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B2884457 : Blo 1800101 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B3040105 : Blo 1800101 3040105 := bstep (se 2 (by rfl) ⟨1140039, by rfl⟩ : syracuseStep 3040105 = 2280079) B2280079
theorem B4326331 : Blo 1800101 4326331 := bstep (se 1 (by rfl) ⟨3244748, by rfl⟩ : syracuseStep 4326331 = 6489497) B6489497
theorem B2278363 : Blo 1800101 2278363 := bstep (se 1 (by rfl) ⟨1708772, by rfl⟩ : syracuseStep 2278363 = 3417545) B3417545
theorem B20792285 : Blo 1800101 20792285 := bstep (se 3 (by rfl) ⟨3898553, by rfl⟩ : syracuseStep 20792285 = 7797107) B7797107
theorem B7300343 : Blo 1800101 7300343 := bstep (se 1 (by rfl) ⟨5475257, by rfl⟩ : syracuseStep 7300343 = 10950515) B10950515
theorem B3245303 : Blo 1800101 3245303 := bstep (se 1 (by rfl) ⟨2433977, by rfl⟩ : syracuseStep 3245303 = 4867955) B4867955
theorem B6079805 : Blo 1800101 6079805 := bstep (se 3 (by rfl) ⟨1139963, by rfl⟩ : syracuseStep 6079805 = 2279927) B2279927
theorem B16647691 : Blo 1800101 16647691 := bstep (se 1 (by rfl) ⟨12485768, by rfl⟩ : syracuseStep 16647691 = 24971537) B24971537
theorem B85485149 : Blo 1800101 85485149 := bstep (se 3 (by rfl) ⟨16028465, by rfl⟩ : syracuseStep 85485149 = 32056931) B32056931
theorem B11536289 : Blo 1800101 11536289 := bstep (se 2 (by rfl) ⟨4326108, by rfl⟩ : syracuseStep 11536289 = 8652217) B8652217
theorem B2025391 : Blo 1800101 2025391 := bstep (se 1 (by rfl) ⟨1519043, by rfl⟩ : syracuseStep 2025391 = 3038087) B3038087
theorem B3418031 : Blo 1800101 3418031 := bstep (se 1 (by rfl) ⟨2563523, by rfl⟩ : syracuseStep 3418031 = 5127047) B5127047
theorem B4556807 : Blo 1800101 4556807 := bstep (se 1 (by rfl) ⟨3417605, by rfl⟩ : syracuseStep 4556807 = 6835211) B6835211
theorem B4556857 : Blo 1800101 4556857 := bstep (se 2 (by rfl) ⟨1708821, by rfl⟩ : syracuseStep 4556857 = 3417643) B3417643
theorem B3418463 : Blo 1800101 3418463 := bstep (se 1 (by rfl) ⟨2563847, by rfl⟩ : syracuseStep 3418463 = 5127695) B5127695
theorem B2025823 : Blo 1800101 2025823 := bstep (se 1 (by rfl) ⟨1519367, by rfl⟩ : syracuseStep 2025823 = 3038735) B3038735
theorem B4557161 : Blo 1800101 4557161 := bstep (se 2 (by rfl) ⟨1708935, by rfl⟩ : syracuseStep 4557161 = 3417871) B3417871
theorem B11856365 : Blo 1800101 11856365 := bstep (se 3 (by rfl) ⟨2223068, by rfl⟩ : syracuseStep 11856365 = 4446137) B4446137
theorem B13675067 : Blo 1800101 13675067 := bstep (se 1 (by rfl) ⟨10256300, by rfl⟩ : syracuseStep 13675067 = 20512601) B20512601
theorem B7301771 : Blo 1800101 7301771 := bstep (se 1 (by rfl) ⟨5476328, by rfl⟩ : syracuseStep 7301771 = 10952657) B10952657
theorem B2026183 : Blo 1800101 2026183 := bstep (se 1 (by rfl) ⟨1519637, by rfl⟩ : syracuseStep 2026183 = 3039275) B3039275
theorem B23079653 : Blo 1800101 23079653 := bstep (se 4 (by rfl) ⟨2163717, by rfl⟩ : syracuseStep 23079653 = 4327435) B4327435
theorem B4934495 : Blo 1800101 4934495 := bstep (se 1 (by rfl) ⟨3700871, by rfl⟩ : syracuseStep 4934495 = 7401743) B7401743
theorem B6163361 : Blo 1800101 6163361 := bstep (se 2 (by rfl) ⟨2311260, by rfl⟩ : syracuseStep 6163361 = 4622521) B4622521
theorem B133262293 : Blo 1800101 133262293 := bstep (se 7 (by rfl) ⟨1561667, by rfl⟩ : syracuseStep 133262293 = 3123335) B3123335
theorem B10259855 : Blo 1800101 10259855 := bstep (se 1 (by rfl) ⟨7694891, by rfl⟩ : syracuseStep 10259855 = 15389783) B15389783
theorem B4050395 : Blo 1800101 4050395 := bstep (se 1 (by rfl) ⟨3037796, by rfl⟩ : syracuseStep 4050395 = 6075593) B6075593
theorem B4869641 : Blo 1800101 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B52645463 : Blo 1800101 52645463 := bstep (se 1 (by rfl) ⟨39484097, by rfl⟩ : syracuseStep 52645463 = 78968195) B78968195
theorem B10260107 : Blo 1800101 10260107 := bstep (se 1 (by rfl) ⟨7695080, by rfl⟩ : syracuseStep 10260107 = 15390161) B15390161
theorem B8654525 : Blo 1800101 8654525 := bstep (se 3 (by rfl) ⟨1622723, by rfl⟩ : syracuseStep 8654525 = 3245447) B3245447
theorem B9113309 : Blo 1800101 9113309 := bstep (se 3 (by rfl) ⟨1708745, by rfl⟩ : syracuseStep 9113309 = 3417491) B3417491
theorem B7302905 : Blo 1800101 7302905 := bstep (se 2 (by rfl) ⟨2738589, by rfl⟩ : syracuseStep 7302905 = 5477179) B5477179
theorem B6491933 : Blo 1800101 6491933 := bstep (se 3 (by rfl) ⟨1217237, by rfl⟩ : syracuseStep 6491933 = 2434475) B2434475
theorem B4050863 : Blo 1800101 4050863 := bstep (se 1 (by rfl) ⟨3038147, by rfl⟩ : syracuseStep 4050863 = 6076295) B6076295
theorem B6492161 : Blo 1800101 6492161 := bstep (se 2 (by rfl) ⟨2434560, by rfl⟩ : syracuseStep 6492161 = 4869121) B4869121
theorem B11538521 : Blo 1800101 11538521 := bstep (se 2 (by rfl) ⟨4326945, by rfl⟩ : syracuseStep 11538521 = 8653891) B8653891
theorem B4051115 : Blo 1800101 4051115 := bstep (se 1 (by rfl) ⟨3038336, by rfl⟩ : syracuseStep 4051115 = 6076673) B6076673
theorem B6836471 : Blo 1800101 6836471 := bstep (se 1 (by rfl) ⟨5127353, by rfl⟩ : syracuseStep 6836471 = 10254707) B10254707
theorem B19730749 : Blo 1800101 19730749 := bstep (se 3 (by rfl) ⟨3699515, by rfl⟩ : syracuseStep 19730749 = 7399031) B7399031
theorem B11538749 : Blo 1800101 11538749 := bstep (se 3 (by rfl) ⟨2163515, by rfl⟩ : syracuseStep 11538749 = 4327031) B4327031
theorem B4559399 : Blo 1800101 4559399 := bstep (se 1 (by rfl) ⟨3419549, by rfl⟩ : syracuseStep 4559399 = 6839099) B6839099
theorem B4051655 : Blo 1800101 4051655 := bstep (se 1 (by rfl) ⟨3038741, by rfl⟩ : syracuseStep 4051655 = 6077483) B6077483
theorem B4559723 : Blo 1800101 4559723 := bstep (se 1 (by rfl) ⟨3419792, by rfl⟩ : syracuseStep 4559723 = 6839585) B6839585
theorem B2700215 : Blo 1800101 2700215 := bstep (se 1 (by rfl) ⟨2025161, by rfl⟩ : syracuseStep 2700215 = 4050323) B4050323
theorem B2700251 : Blo 1800101 2700251 := bstep (se 1 (by rfl) ⟨2025188, by rfl⟩ : syracuseStep 2700251 = 4050377) B4050377
theorem B51336341 : Blo 1800101 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B6837443 : Blo 1800101 6837443 := bstep (se 1 (by rfl) ⟨5128082, by rfl⟩ : syracuseStep 6837443 = 10256165) B10256165
theorem B13669721 : Blo 1800101 13669721 := bstep (se 2 (by rfl) ⟨5126145, by rfl⟩ : syracuseStep 13669721 = 10252291) B10252291
theorem B2700719 : Blo 1800101 2700719 := bstep (se 1 (by rfl) ⟨2025539, by rfl⟩ : syracuseStep 2700719 = 4051079) B4051079
theorem B9237979 : Blo 1800101 9237979 := bstep (se 1 (by rfl) ⟨6928484, by rfl⟩ : syracuseStep 9237979 = 13856969) B13856969
theorem B2700809 : Blo 1800101 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B11539979 : Blo 1800101 11539979 := bstep (se 1 (by rfl) ⟨8654984, by rfl⟩ : syracuseStep 11539979 = 17309969) B17309969
theorem B2700839 : Blo 1800101 2700839 := bstep (se 1 (by rfl) ⟨2025629, by rfl⟩ : syracuseStep 2700839 = 4051259) B4051259
theorem B4052519 : Blo 1800101 4052519 := bstep (se 1 (by rfl) ⟨3039389, by rfl⟩ : syracuseStep 4052519 = 6078779) B6078779
theorem B2700923 : Blo 1800101 2700923 := bstep (se 1 (by rfl) ⟨2025692, by rfl⟩ : syracuseStep 2700923 = 4051385) B4051385
theorem B8656523 : Blo 1800101 8656523 := bstep (se 1 (by rfl) ⟨6492392, by rfl⟩ : syracuseStep 8656523 = 12984785) B12984785
theorem B13858451 : Blo 1800101 13858451 := bstep (se 1 (by rfl) ⟨10393838, by rfl⟩ : syracuseStep 13858451 = 20787677) B20787677
theorem B10254023 : Blo 1800101 10254023 := bstep (se 1 (by rfl) ⟨7690517, by rfl⟩ : syracuseStep 10254023 = 15381035) B15381035
theorem B6837959 : Blo 1800101 6837959 := bstep (se 1 (by rfl) ⟨5128469, by rfl⟩ : syracuseStep 6837959 = 10256939) B10256939
theorem B2701049 : Blo 1800101 2701049 := bstep (se 2 (by rfl) ⟨1012893, by rfl⟩ : syracuseStep 2701049 = 2025787) B2025787
theorem B14047019 : Blo 1800101 14047019 := bstep (se 1 (by rfl) ⟨10535264, by rfl⟩ : syracuseStep 14047019 = 21070529) B21070529
theorem B2701151 : Blo 1800101 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B2701163 : Blo 1800101 2701163 := bstep (se 1 (by rfl) ⟨2025872, by rfl⟩ : syracuseStep 2701163 = 4051745) B4051745
theorem B4052843 : Blo 1800101 4052843 := bstep (se 1 (by rfl) ⟨3039632, by rfl⟩ : syracuseStep 4052843 = 6079265) B6079265
theorem B4052897 : Blo 1800101 4052897 := bstep (se 2 (by rfl) ⟨1519836, by rfl⟩ : syracuseStep 4052897 = 3039673) B3039673
theorem B1800111 : Blo 1800101 1800111 := bstep (se 1 (by rfl) ⟨1350083, by rfl⟩ : syracuseStep 1800111 = 2700167) B2700167
theorem B1800135 : Blo 1800101 1800135 := bstep (se 1 (by rfl) ⟨1350101, by rfl⟩ : syracuseStep 1800135 = 2700203) B2700203
theorem B1800155 : Blo 1800101 1800155 := bstep (se 1 (by rfl) ⟨1350116, by rfl⟩ : syracuseStep 1800155 = 2700233) B2700233
theorem B6666259 : Blo 1800101 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B1800231 : Blo 1800101 1800231 := bstep (se 1 (by rfl) ⟨1350173, by rfl⟩ : syracuseStep 1800231 = 2700347) B2700347
theorem B1800271 : Blo 1800101 1800271 := bstep (se 1 (by rfl) ⟨1350203, by rfl⟩ : syracuseStep 1800271 = 2700407) B2700407
theorem B2701391 : Blo 1800101 2701391 := bstep (se 1 (by rfl) ⟨2026043, by rfl⟩ : syracuseStep 2701391 = 4052087) B4052087
theorem B15390809 : Blo 1800101 15390809 := bstep (se 2 (by rfl) ⟨5771553, by rfl⟩ : syracuseStep 15390809 = 11543107) B11543107
theorem B1800287 : Blo 1800101 1800287 := bstep (se 1 (by rfl) ⟨1350215, by rfl⟩ : syracuseStep 1800287 = 2700431) B2700431
theorem B1800315 : Blo 1800101 1800315 := bstep (se 1 (by rfl) ⟨1350236, by rfl⟩ : syracuseStep 1800315 = 2700473) B2700473
theorem B1800367 : Blo 1800101 1800367 := bstep (se 1 (by rfl) ⟨1350275, by rfl⟩ : syracuseStep 1800367 = 2700551) B2700551
theorem B1800391 : Blo 1800101 1800391 := bstep (se 1 (by rfl) ⟨1350293, by rfl⟩ : syracuseStep 1800391 = 2700587) B2700587
theorem B2701511 : Blo 1800101 2701511 := bstep (se 1 (by rfl) ⟨2026133, by rfl⟩ : syracuseStep 2701511 = 4052267) B4052267
theorem B1800411 : Blo 1800101 1800411 := bstep (se 1 (by rfl) ⟨1350308, by rfl⟩ : syracuseStep 1800411 = 2700617) B2700617
theorem B4053239 : Blo 1800101 4053239 := bstep (se 1 (by rfl) ⟨3039929, by rfl⟩ : syracuseStep 4053239 = 6079859) B6079859
theorem B1800487 : Blo 1800101 1800487 := bstep (se 1 (by rfl) ⟨1350365, by rfl⟩ : syracuseStep 1800487 = 2700731) B2700731
theorem B1800527 : Blo 1800101 1800527 := bstep (se 1 (by rfl) ⟨1350395, by rfl⟩ : syracuseStep 1800527 = 2700791) B2700791
theorem B1800543 : Blo 1800101 1800543 := bstep (se 1 (by rfl) ⟨1350407, by rfl⟩ : syracuseStep 1800543 = 2700815) B2700815
theorem B2701673 : Blo 1800101 2701673 := bstep (se 2 (by rfl) ⟨1013127, by rfl⟩ : syracuseStep 2701673 = 2026255) B2026255
theorem B1800571 : Blo 1800101 1800571 := bstep (se 1 (by rfl) ⟨1350428, by rfl⟩ : syracuseStep 1800571 = 2700857) B2700857
theorem B1800623 : Blo 1800101 1800623 := bstep (se 1 (by rfl) ⟨1350467, by rfl⟩ : syracuseStep 1800623 = 2700935) B2700935
theorem B2701751 : Blo 1800101 2701751 := bstep (se 1 (by rfl) ⟨2026313, by rfl⟩ : syracuseStep 2701751 = 4052627) B4052627
theorem B1800647 : Blo 1800101 1800647 := bstep (se 1 (by rfl) ⟨1350485, by rfl⟩ : syracuseStep 1800647 = 2700971) B2700971
theorem B1800667 : Blo 1800101 1800667 := bstep (se 1 (by rfl) ⟨1350500, by rfl⟩ : syracuseStep 1800667 = 2701001) B2701001
theorem B2701787 : Blo 1800101 2701787 := bstep (se 1 (by rfl) ⟨2026340, by rfl⟩ : syracuseStep 2701787 = 4052681) B4052681
theorem B1800743 : Blo 1800101 1800743 := bstep (se 1 (by rfl) ⟨1350557, by rfl⟩ : syracuseStep 1800743 = 2701115) B2701115
theorem B1800783 : Blo 1800101 1800783 := bstep (se 1 (by rfl) ⟨1350587, by rfl⟩ : syracuseStep 1800783 = 2701175) B2701175
theorem B1800799 : Blo 1800101 1800799 := bstep (se 1 (by rfl) ⟨1350599, by rfl⟩ : syracuseStep 1800799 = 2701199) B2701199
theorem B6077051 : Blo 1800101 6077051 := bstep (se 1 (by rfl) ⟨4557788, by rfl⟩ : syracuseStep 6077051 = 9115577) B9115577
theorem B1800827 : Blo 1800101 1800827 := bstep (se 1 (by rfl) ⟨1350620, by rfl⟩ : syracuseStep 1800827 = 2701241) B2701241
theorem B6838931 : Blo 1800101 6838931 := bstep (se 1 (by rfl) ⟨5129198, by rfl⟩ : syracuseStep 6838931 = 10258397) B10258397
theorem B1800879 : Blo 1800101 1800879 := bstep (se 1 (by rfl) ⟨1350659, by rfl⟩ : syracuseStep 1800879 = 2701319) B2701319
theorem B1800903 : Blo 1800101 1800903 := bstep (se 1 (by rfl) ⟨1350677, by rfl⟩ : syracuseStep 1800903 = 2701355) B2701355
theorem B1800923 : Blo 1800101 1800923 := bstep (se 1 (by rfl) ⟨1350692, by rfl⟩ : syracuseStep 1800923 = 2701385) B2701385
theorem B3037945 : Blo 1800101 3037945 := bstep (se 2 (by rfl) ⟨1139229, by rfl⟩ : syracuseStep 3037945 = 2278459) B2278459
theorem B6077213 : Blo 1800101 6077213 := bstep (se 3 (by rfl) ⟨1139477, by rfl⟩ : syracuseStep 6077213 = 2278955) B2278955
theorem B1800999 : Blo 1800101 1800999 := bstep (se 1 (by rfl) ⟨1350749, by rfl⟩ : syracuseStep 1800999 = 2701499) B2701499
theorem B6839113 : Blo 1800101 6839113 := bstep (se 2 (by rfl) ⟨2564667, by rfl⟩ : syracuseStep 6839113 = 5129335) B5129335
theorem B1801039 : Blo 1800101 1801039 := bstep (se 1 (by rfl) ⟨1350779, by rfl⟩ : syracuseStep 1801039 = 2701559) B2701559
theorem B1801055 : Blo 1800101 1801055 := bstep (se 1 (by rfl) ⟨1350791, by rfl⟩ : syracuseStep 1801055 = 2701583) B2701583
theorem B131414885 : Blo 1800101 131414885 := bstep (se 4 (by rfl) ⟨12320145, by rfl⟩ : syracuseStep 131414885 = 24640291) B24640291
theorem B1801083 : Blo 1800101 1801083 := bstep (se 1 (by rfl) ⟨1350812, by rfl⟩ : syracuseStep 1801083 = 2701625) B2701625
theorem B1801135 : Blo 1800101 1801135 := bstep (se 1 (by rfl) ⟨1350851, by rfl⟩ : syracuseStep 1801135 = 2701703) B2701703
theorem B2702255 : Blo 1800101 2702255 := bstep (se 1 (by rfl) ⟨2026691, by rfl⟩ : syracuseStep 2702255 = 4053383) B4053383
theorem B4619195 : Blo 1800101 4619195 := bstep (se 1 (by rfl) ⟨3464396, by rfl⟩ : syracuseStep 4619195 = 6928793) B6928793
theorem B1801159 : Blo 1800101 1801159 := bstep (se 1 (by rfl) ⟨1350869, by rfl⟩ : syracuseStep 1801159 = 2701739) B2701739
theorem B1801179 : Blo 1800101 1801179 := bstep (se 1 (by rfl) ⟨1350884, by rfl⟩ : syracuseStep 1801179 = 2701769) B2701769
theorem B3038215 : Blo 1800101 3038215 := bstep (se 1 (by rfl) ⟨2278661, by rfl⟩ : syracuseStep 3038215 = 4557323) B4557323
theorem B2702345 : Blo 1800101 2702345 := bstep (se 2 (by rfl) ⟨1013379, by rfl⟩ : syracuseStep 2702345 = 2026759) B2026759
theorem B1801255 : Blo 1800101 1801255 := bstep (se 1 (by rfl) ⟨1350941, by rfl⟩ : syracuseStep 1801255 = 2701883) B2701883
theorem B2702375 : Blo 1800101 2702375 := bstep (se 1 (by rfl) ⟨2026781, by rfl⟩ : syracuseStep 2702375 = 4053563) B4053563
theorem B1801295 : Blo 1800101 1801295 := bstep (se 1 (by rfl) ⟨1350971, by rfl⟩ : syracuseStep 1801295 = 2701943) B2701943
theorem B1801311 : Blo 1800101 1801311 := bstep (se 1 (by rfl) ⟨1350983, by rfl⟩ : syracuseStep 1801311 = 2701967) B2701967
theorem B1801339 : Blo 1800101 1801339 := bstep (se 1 (by rfl) ⟨1351004, by rfl⟩ : syracuseStep 1801339 = 2702009) B2702009
theorem B1801391 : Blo 1800101 1801391 := bstep (se 1 (by rfl) ⟨1351043, by rfl⟩ : syracuseStep 1801391 = 2702087) B2702087
theorem B1801415 : Blo 1800101 1801415 := bstep (se 1 (by rfl) ⟨1351061, by rfl⟩ : syracuseStep 1801415 = 2702123) B2702123
theorem B1801435 : Blo 1800101 1801435 := bstep (se 1 (by rfl) ⟨1351076, by rfl⟩ : syracuseStep 1801435 = 2702153) B2702153
theorem B2776313 : Blo 1800101 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B1801511 : Blo 1800101 1801511 := bstep (se 1 (by rfl) ⟨1351133, by rfl⟩ : syracuseStep 1801511 = 2702267) B2702267
theorem B1801551 : Blo 1800101 1801551 := bstep (se 1 (by rfl) ⟨1351163, by rfl⟩ : syracuseStep 1801551 = 2702327) B2702327
theorem B1801567 : Blo 1800101 1801567 := bstep (se 1 (by rfl) ⟨1351175, by rfl⟩ : syracuseStep 1801567 = 2702351) B2702351
theorem B1801595 : Blo 1800101 1801595 := bstep (se 1 (by rfl) ⟨1351196, by rfl⟩ : syracuseStep 1801595 = 2702393) B2702393
theorem B3038647 : Blo 1800101 3038647 := bstep (se 1 (by rfl) ⟨2278985, by rfl⟩ : syracuseStep 3038647 = 4557971) B4557971
theorem B6077915 : Blo 1800101 6077915 := bstep (se 1 (by rfl) ⟨4558436, by rfl⟩ : syracuseStep 6077915 = 9116873) B9116873
theorem B3513935 : Blo 1800101 3513935 := bstep (se 1 (by rfl) ⟨2635451, by rfl⟩ : syracuseStep 3513935 = 5270903) B5270903
theorem B7298657 : Blo 1800101 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B3038843 : Blo 1800101 3038843 := bstep (se 1 (by rfl) ⟨2279132, by rfl⟩ : syracuseStep 3038843 = 4558265) B4558265
theorem B13672151 : Blo 1800101 13672151 := bstep (se 1 (by rfl) ⟨10254113, by rfl⟩ : syracuseStep 13672151 = 20508227) B20508227
theorem B12320477 : Blo 1800101 12320477 := bstep (se 3 (by rfl) ⟨2310089, by rfl⟩ : syracuseStep 12320477 = 4620179) B4620179
theorem B9240439 : Blo 1800101 9240439 := bstep (se 1 (by rfl) ⟨6930329, by rfl⟩ : syracuseStep 9240439 = 13860659) B13860659
theorem B7503803 : Blo 1800101 7503803 := bstep (se 1 (by rfl) ⟨5627852, by rfl⟩ : syracuseStep 7503803 = 11255705) B11255705
theorem B8888345 : Blo 1800101 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B7692347 : Blo 1800101 7692347 := bstep (se 1 (by rfl) ⟨5769260, by rfl⟩ : syracuseStep 7692347 = 11538521) B11538521
theorem B7692499 : Blo 1800101 7692499 := bstep (se 1 (by rfl) ⟨5769374, by rfl⟩ : syracuseStep 7692499 = 11538749) B11538749
theorem B2310439 : Blo 1800101 2310439 := bstep (se 1 (by rfl) ⟨1732829, by rfl⟩ : syracuseStep 2310439 = 3465659) B3465659
theorem B3039599 : Blo 1800101 3039599 := bstep (se 1 (by rfl) ⟨2279699, by rfl⟩ : syracuseStep 3039599 = 4559399) B4559399
theorem B6078995 : Blo 1800101 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B3039815 : Blo 1800101 3039815 := bstep (se 1 (by rfl) ⟨2279861, by rfl⟩ : syracuseStep 3039815 = 4559723) B4559723
theorem B13861523 : Blo 1800101 13861523 := bstep (se 1 (by rfl) ⟨10396142, by rfl⟩ : syracuseStep 13861523 = 20792285) B20792285
theorem B11698937 : Blo 1800101 11698937 := bstep (se 2 (by rfl) ⟨4387101, by rfl⟩ : syracuseStep 11698937 = 8774203) B8774203
theorem B4866895 : Blo 1800101 4866895 := bstep (se 1 (by rfl) ⟨3650171, by rfl⟩ : syracuseStep 4866895 = 7300343) B7300343
theorem B8651681 : Blo 1800101 8651681 := bstep (se 2 (by rfl) ⟨3244380, by rfl⟩ : syracuseStep 8651681 = 6488761) B6488761
theorem B7693319 : Blo 1800101 7693319 := bstep (se 1 (by rfl) ⟨5769989, by rfl⟩ : syracuseStep 7693319 = 11539979) B11539979
theorem B9118817 : Blo 1800101 9118817 := bstep (se 2 (by rfl) ⟨3419556, by rfl⟩ : syracuseStep 9118817 = 6839113) B6839113
theorem B9364679 : Blo 1800101 9364679 := bstep (se 1 (by rfl) ⟨7023509, by rfl⟩ : syracuseStep 9364679 = 14047019) B14047019
theorem B5768441 : Blo 1800101 5768441 := bstep (se 2 (by rfl) ⟨2163165, by rfl⟩ : syracuseStep 5768441 = 4326331) B4326331
theorem B2278687 : Blo 1800101 2278687 := bstep (se 1 (by rfl) ⟨1709015, by rfl⟩ : syracuseStep 2278687 = 3418031) B3418031
theorem B4867847 : Blo 1800101 4867847 := bstep (se 1 (by rfl) ⟨3650885, by rfl⟩ : syracuseStep 4867847 = 7301771) B7301771
theorem B15386435 : Blo 1800101 15386435 := bstep (se 1 (by rfl) ⟨11539826, by rfl⟩ : syracuseStep 15386435 = 23079653) B23079653
theorem B3246427 : Blo 1800101 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B35096975 : Blo 1800101 35096975 := bstep (se 1 (by rfl) ⟨26322731, by rfl⟩ : syracuseStep 35096975 = 52645463) B52645463
theorem B2025895 : Blo 1800101 2025895 := bstep (se 1 (by rfl) ⟨1519421, by rfl⟩ : syracuseStep 2025895 = 3038843) B3038843
theorem B5769683 : Blo 1800101 5769683 := bstep (se 1 (by rfl) ⟨4327262, by rfl⟩ : syracuseStep 5769683 = 8654525) B8654525
theorem B4868603 : Blo 1800101 4868603 := bstep (se 1 (by rfl) ⟨3651452, by rfl⟩ : syracuseStep 4868603 = 7302905) B7302905
theorem B4327955 : Blo 1800101 4327955 := bstep (se 1 (by rfl) ⟨3245966, by rfl⟩ : syracuseStep 4327955 = 6491933) B6491933
theorem B17312429 : Blo 1800101 17312429 := bstep (se 3 (by rfl) ⟨3246080, by rfl⟩ : syracuseStep 17312429 = 6492161) B6492161
theorem B3844883 : Blo 1800101 3844883 := bstep (se 1 (by rfl) ⟨2883662, by rfl⟩ : syracuseStep 3844883 = 5767325) B5767325
theorem B4557647 : Blo 1800101 4557647 := bstep (se 1 (by rfl) ⟨3418235, by rfl⟩ : syracuseStep 4557647 = 6836471) B6836471
theorem B2026471 : Blo 1800101 2026471 := bstep (se 1 (by rfl) ⟨1519853, by rfl⟩ : syracuseStep 2026471 = 3039707) B3039707
theorem B26307665 : Blo 1800101 26307665 := bstep (se 2 (by rfl) ⟨9865374, by rfl⟩ : syracuseStep 26307665 = 19730749) B19730749
theorem B8654141 : Blo 1800101 8654141 := bstep (se 3 (by rfl) ⟨1622651, by rfl⟩ : syracuseStep 8654141 = 3245303) B3245303
theorem B3419489 : Blo 1800101 3419489 := bstep (se 2 (by rfl) ⟨1282308, by rfl⟩ : syracuseStep 3419489 = 2564617) B2564617
theorem B4558295 : Blo 1800101 4558295 := bstep (se 1 (by rfl) ⟨3418721, by rfl⟩ : syracuseStep 4558295 = 6837443) B6837443
theorem B9113147 : Blo 1800101 9113147 := bstep (se 1 (by rfl) ⟨6834860, by rfl⟩ : syracuseStep 9113147 = 13669721) B13669721
theorem B15380077 : Blo 1800101 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B4050593 : Blo 1800101 4050593 := bstep (se 2 (by rfl) ⟨1518972, by rfl⟩ : syracuseStep 4050593 = 3037945) B3037945
theorem B5771015 : Blo 1800101 5771015 := bstep (se 1 (by rfl) ⟨4328261, by rfl⟩ : syracuseStep 5771015 = 8656523) B8656523
theorem B6836015 : Blo 1800101 6836015 := bstep (se 1 (by rfl) ⟨5127011, by rfl⟩ : syracuseStep 6836015 = 10254023) B10254023
theorem B4558639 : Blo 1800101 4558639 := bstep (se 1 (by rfl) ⟨3418979, by rfl⟩ : syracuseStep 4558639 = 6837959) B6837959
theorem B4050953 : Blo 1800101 4050953 := bstep (se 2 (by rfl) ⟨1519107, by rfl⟩ : syracuseStep 4050953 = 3038215) B3038215
theorem B10260539 : Blo 1800101 10260539 := bstep (se 1 (by rfl) ⟨7695404, by rfl⟩ : syracuseStep 10260539 = 15390809) B15390809
theorem B4051367 : Blo 1800101 4051367 := bstep (se 1 (by rfl) ⟨3038525, by rfl⟩ : syracuseStep 4051367 = 6077051) B6077051
theorem B4559287 : Blo 1800101 4559287 := bstep (se 1 (by rfl) ⟨3419465, by rfl⟩ : syracuseStep 4559287 = 6838931) B6838931
theorem B4051475 : Blo 1800101 4051475 := bstep (se 1 (by rfl) ⟨3038606, by rfl⟩ : syracuseStep 4051475 = 6077213) B6077213
theorem B3289663 : Blo 1800101 3289663 := bstep (se 1 (by rfl) ⟨2467247, by rfl⟩ : syracuseStep 3289663 = 4934495) B4934495
theorem B87609923 : Blo 1800101 87609923 := bstep (se 1 (by rfl) ⟨65707442, by rfl⟩ : syracuseStep 87609923 = 131414885) B131414885
theorem B4051529 : Blo 1800101 4051529 := bstep (se 2 (by rfl) ⟨1519323, by rfl⟩ : syracuseStep 4051529 = 3038647) B3038647
theorem B4108907 : Blo 1800101 4108907 := bstep (se 1 (by rfl) ⟨3081680, by rfl⟩ : syracuseStep 4108907 = 6163361) B6163361
theorem B12317305 : Blo 1800101 12317305 := bstep (se 2 (by rfl) ⟨4618989, by rfl⟩ : syracuseStep 12317305 = 9237979) B9237979
theorem B22196921 : Blo 1800101 22196921 := bstep (se 2 (by rfl) ⟨8323845, by rfl⟩ : syracuseStep 22196921 = 16647691) B16647691
theorem B15381413 : Blo 1800101 15381413 := bstep (se 4 (by rfl) ⟨1442007, by rfl⟩ : syracuseStep 15381413 = 2884015) B2884015
theorem B2700263 : Blo 1800101 2700263 := bstep (se 1 (by rfl) ⟨2025197, by rfl⟩ : syracuseStep 2700263 = 4050395) B4050395
theorem B4051943 : Blo 1800101 4051943 := bstep (se 1 (by rfl) ⟨3038957, by rfl⟩ : syracuseStep 4051943 = 6077915) B6077915
theorem B9114767 : Blo 1800101 9114767 := bstep (se 1 (by rfl) ⟨6836075, by rfl⟩ : syracuseStep 9114767 = 13672151) B13672151
theorem B6075539 : Blo 1800101 6075539 := bstep (se 1 (by rfl) ⟨4556654, by rfl⟩ : syracuseStep 6075539 = 9113309) B9113309
theorem B8213651 : Blo 1800101 8213651 := bstep (se 1 (by rfl) ⟨6160238, by rfl⟩ : syracuseStep 8213651 = 12320477) B12320477
theorem B2700521 : Blo 1800101 2700521 := bstep (se 2 (by rfl) ⟨1012695, by rfl⟩ : syracuseStep 2700521 = 2025391) B2025391
theorem B2700575 : Blo 1800101 2700575 := bstep (se 1 (by rfl) ⟨2025431, by rfl⟩ : syracuseStep 2700575 = 4050863) B4050863
theorem B5002535 : Blo 1800101 5002535 := bstep (se 1 (by rfl) ⟨3751901, by rfl⟩ : syracuseStep 5002535 = 7503803) B7503803
theorem B4052321 : Blo 1800101 4052321 := bstep (se 2 (by rfl) ⟨1519620, by rfl⟩ : syracuseStep 4052321 = 3039241) B3039241
theorem B6075809 : Blo 1800101 6075809 := bstep (se 2 (by rfl) ⟨2278428, by rfl⟩ : syracuseStep 6075809 = 4556857) B4556857
theorem B4052411 : Blo 1800101 4052411 := bstep (se 1 (by rfl) ⟨3039308, by rfl⟩ : syracuseStep 4052411 = 6078617) B6078617
theorem B2700743 : Blo 1800101 2700743 := bstep (se 1 (by rfl) ⟨2025557, by rfl⟩ : syracuseStep 2700743 = 4051115) B4051115
theorem B4052537 : Blo 1800101 4052537 := bstep (se 2 (by rfl) ⟨1519701, by rfl⟩ : syracuseStep 4052537 = 3039403) B3039403
theorem B78976579 : Blo 1800101 78976579 := bstep (se 1 (by rfl) ⟨59232434, by rfl⟩ : syracuseStep 78976579 = 118464869) B118464869
theorem B1922783 : Blo 1800101 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B2701097 : Blo 1800101 2701097 := bstep (se 2 (by rfl) ⟨1012911, by rfl⟩ : syracuseStep 2701097 = 2025823) B2025823
theorem B2701103 : Blo 1800101 2701103 := bstep (se 1 (by rfl) ⟨2025827, by rfl⟩ : syracuseStep 2701103 = 4051655) B4051655
theorem B1800143 : Blo 1800101 1800143 := bstep (se 1 (by rfl) ⟨1350107, by rfl⟩ : syracuseStep 1800143 = 2700215) B2700215
theorem B1800167 : Blo 1800101 1800167 := bstep (se 1 (by rfl) ⟨1350125, by rfl⟩ : syracuseStep 1800167 = 2700251) B2700251
theorem B7403501 : Blo 1800101 7403501 := bstep (se 3 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 7403501 = 2776313) B2776313
theorem B34224227 : Blo 1800101 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B4053203 : Blo 1800101 4053203 := bstep (se 1 (by rfl) ⟨3039902, by rfl⟩ : syracuseStep 4053203 = 6079805) B6079805
theorem B9115901 : Blo 1800101 9115901 := bstep (se 3 (by rfl) ⟨1709231, by rfl⟩ : syracuseStep 9115901 = 3418463) B3418463
theorem B2701577 : Blo 1800101 2701577 := bstep (se 2 (by rfl) ⟨1013091, by rfl⟩ : syracuseStep 2701577 = 2026183) B2026183
theorem B4053257 : Blo 1800101 4053257 := bstep (se 2 (by rfl) ⟨1519971, by rfl⟩ : syracuseStep 4053257 = 3039943) B3039943
theorem B1800479 : Blo 1800101 1800479 := bstep (se 1 (by rfl) ⟨1350359, by rfl⟩ : syracuseStep 1800479 = 2700719) B2700719
theorem B1800539 : Blo 1800101 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B1800559 : Blo 1800101 1800559 := bstep (se 1 (by rfl) ⟨1350419, by rfl⟩ : syracuseStep 1800559 = 2700839) B2700839
theorem B2701679 : Blo 1800101 2701679 := bstep (se 1 (by rfl) ⟨2026259, by rfl⟩ : syracuseStep 2701679 = 4052519) B4052519
theorem B56990099 : Blo 1800101 56990099 := bstep (se 1 (by rfl) ⟨42742574, by rfl⟩ : syracuseStep 56990099 = 85485149) B85485149
theorem B1800615 : Blo 1800101 1800615 := bstep (se 1 (by rfl) ⟨1350461, by rfl⟩ : syracuseStep 1800615 = 2700923) B2700923
theorem B9238967 : Blo 1800101 9238967 := bstep (se 1 (by rfl) ⟨6929225, by rfl⟩ : syracuseStep 9238967 = 13858451) B13858451
theorem B4053473 : Blo 1800101 4053473 := bstep (se 2 (by rfl) ⟨1520052, by rfl⟩ : syracuseStep 4053473 = 3040105) B3040105
theorem B1800699 : Blo 1800101 1800699 := bstep (se 1 (by rfl) ⟨1350524, by rfl⟩ : syracuseStep 1800699 = 2701049) B2701049
theorem B1800767 : Blo 1800101 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B1800775 : Blo 1800101 1800775 := bstep (se 1 (by rfl) ⟨1350581, by rfl⟩ : syracuseStep 1800775 = 2701163) B2701163
theorem B2701895 : Blo 1800101 2701895 := bstep (se 1 (by rfl) ⟨2026421, by rfl⟩ : syracuseStep 2701895 = 4052843) B4052843
theorem B7690859 : Blo 1800101 7690859 := bstep (se 1 (by rfl) ⟨5768144, by rfl⟩ : syracuseStep 7690859 = 11536289) B11536289
theorem B2701931 : Blo 1800101 2701931 := bstep (se 1 (by rfl) ⟨2026448, by rfl⟩ : syracuseStep 2701931 = 4052897) B4052897
theorem B177683057 : Blo 1800101 177683057 := bstep (se 2 (by rfl) ⟨66631146, by rfl⟩ : syracuseStep 177683057 = 133262293) B133262293
theorem B3037817 : Blo 1800101 3037817 := bstep (se 2 (by rfl) ⟨1139181, by rfl⟩ : syracuseStep 3037817 = 2278363) B2278363
theorem B3037871 : Blo 1800101 3037871 := bstep (se 1 (by rfl) ⟨2278403, by rfl⟩ : syracuseStep 3037871 = 4556807) B4556807
theorem B1800927 : Blo 1800101 1800927 := bstep (se 1 (by rfl) ⟨1350695, by rfl⟩ : syracuseStep 1800927 = 2701391) B2701391
theorem B1801007 : Blo 1800101 1801007 := bstep (se 1 (by rfl) ⟨1350755, by rfl⟩ : syracuseStep 1801007 = 2701511) B2701511
theorem B2702159 : Blo 1800101 2702159 := bstep (se 1 (by rfl) ⟨2026619, by rfl⟩ : syracuseStep 2702159 = 4053239) B4053239
theorem B3038107 : Blo 1800101 3038107 := bstep (se 1 (by rfl) ⟨2278580, by rfl⟩ : syracuseStep 3038107 = 4557161) B4557161
theorem B1801115 : Blo 1800101 1801115 := bstep (se 1 (by rfl) ⟨1350836, by rfl⟩ : syracuseStep 1801115 = 2701673) B2701673
theorem B1801167 : Blo 1800101 1801167 := bstep (se 1 (by rfl) ⟨1350875, by rfl⟩ : syracuseStep 1801167 = 2701751) B2701751
theorem B1801191 : Blo 1800101 1801191 := bstep (se 1 (by rfl) ⟨1350893, by rfl⟩ : syracuseStep 1801191 = 2701787) B2701787
theorem B7904243 : Blo 1800101 7904243 := bstep (se 1 (by rfl) ⟨5928182, by rfl⟩ : syracuseStep 7904243 = 11856365) B11856365
theorem B9116711 : Blo 1800101 9116711 := bstep (se 1 (by rfl) ⟨6837533, by rfl⟩ : syracuseStep 9116711 = 13675067) B13675067
theorem B17784029 : Blo 1800101 17784029 := bstep (se 3 (by rfl) ⟨3334505, by rfl⟩ : syracuseStep 17784029 = 6669011) B6669011
theorem B1801503 : Blo 1800101 1801503 := bstep (se 1 (by rfl) ⟨1351127, by rfl⟩ : syracuseStep 1801503 = 2702255) B2702255
theorem B3079463 : Blo 1800101 3079463 := bstep (se 1 (by rfl) ⟨2309597, by rfl⟩ : syracuseStep 3079463 = 4619195) B4619195
theorem B1801563 : Blo 1800101 1801563 := bstep (se 1 (by rfl) ⟨1351172, by rfl⟩ : syracuseStep 1801563 = 2702345) B2702345
theorem B1801583 : Blo 1800101 1801583 := bstep (se 1 (by rfl) ⟨1351187, by rfl⟩ : syracuseStep 1801583 = 2702375) B2702375
theorem B6839903 : Blo 1800101 6839903 := bstep (se 1 (by rfl) ⟨5129927, by rfl⟩ : syracuseStep 6839903 = 10259855) B10259855
theorem B7691885 : Blo 1800101 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B2342623 : Blo 1800101 2342623 := bstep (se 1 (by rfl) ⟨1756967, by rfl⟩ : syracuseStep 2342623 = 3513935) B3513935
theorem B4865771 : Blo 1800101 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B6840071 : Blo 1800101 6840071 := bstep (se 1 (by rfl) ⟨5130053, by rfl⟩ : syracuseStep 6840071 = 10260107) B10260107
theorem B12320585 : Blo 1800101 12320585 := bstep (se 2 (by rfl) ⟨4620219, by rfl⟩ : syracuseStep 12320585 = 9240439) B9240439
theorem B5128231 : Blo 1800101 5128231 := bstep (se 1 (by rfl) ⟨3846173, by rfl⟩ : syracuseStep 5128231 = 7692347) B7692347
theorem B6840359 : Blo 1800101 6840359 := bstep (se 1 (by rfl) ⟨5130269, by rfl⟩ : syracuseStep 6840359 = 10260539) B10260539
theorem B10256665 : Blo 1800101 10256665 := bstep (se 2 (by rfl) ⟨3846249, by rfl⟩ : syracuseStep 10256665 = 7692499) B7692499
theorem B3080585 : Blo 1800101 3080585 := bstep (se 2 (by rfl) ⟨1155219, by rfl⟩ : syracuseStep 3080585 = 2310439) B2310439
theorem B9241015 : Blo 1800101 9241015 := bstep (se 1 (by rfl) ⟨6930761, by rfl⟩ : syracuseStep 9241015 = 13861523) B13861523
theorem B7799291 : Blo 1800101 7799291 := bstep (se 1 (by rfl) ⟨5849468, by rfl⟩ : syracuseStep 7799291 = 11698937) B11698937
theorem B6079049 : Blo 1800101 6079049 := bstep (se 2 (by rfl) ⟨2279643, by rfl⟩ : syracuseStep 6079049 = 4559287) B4559287
theorem B5767787 : Blo 1800101 5767787 := bstep (se 1 (by rfl) ⟨4325840, by rfl⟩ : syracuseStep 5767787 = 8651681) B8651681
theorem B6079211 : Blo 1800101 6079211 := bstep (se 1 (by rfl) ⟨4559408, by rfl⟩ : syracuseStep 6079211 = 9118817) B9118817
theorem B6243119 : Blo 1800101 6243119 := bstep (se 1 (by rfl) ⟨4682339, by rfl⟩ : syracuseStep 6243119 = 9364679) B9364679
theorem B3335023 : Blo 1800101 3335023 := bstep (se 1 (by rfl) ⟨2501267, by rfl⟩ : syracuseStep 3335023 = 5002535) B5002535
theorem B3245231 : Blo 1800101 3245231 := bstep (se 1 (by rfl) ⟨2433923, by rfl⟩ : syracuseStep 3245231 = 4867847) B4867847
theorem B10257623 : Blo 1800101 10257623 := bstep (se 1 (by rfl) ⟨7693217, by rfl⟩ : syracuseStep 10257623 = 15386435) B15386435
theorem B22816151 : Blo 1800101 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B23397983 : Blo 1800101 23397983 := bstep (se 1 (by rfl) ⟨17548487, by rfl⟩ : syracuseStep 23397983 = 35096975) B35096975
theorem B3245735 : Blo 1800101 3245735 := bstep (se 1 (by rfl) ⟨2434301, by rfl⟩ : syracuseStep 3245735 = 4868603) B4868603
theorem B2885303 : Blo 1800101 2885303 := bstep (se 1 (by rfl) ⟨2163977, by rfl⟩ : syracuseStep 2885303 = 4327955) B4327955
theorem B2025211 : Blo 1800101 2025211 := bstep (se 1 (by rfl) ⟨1518908, by rfl⟩ : syracuseStep 2025211 = 3037817) B3037817
theorem B2025247 : Blo 1800101 2025247 := bstep (se 1 (by rfl) ⟨1518935, by rfl⟩ : syracuseStep 2025247 = 3037871) B3037871
theorem B236767157 : Blo 1800101 236767157 := bstep (se 5 (by rfl) ⟨11098460, by rfl⟩ : syracuseStep 236767157 = 22196921) B22196921
theorem B5269495 : Blo 1800101 5269495 := bstep (se 1 (by rfl) ⟨3952121, by rfl⟩ : syracuseStep 5269495 = 7904243) B7904243
theorem B105302105 : Blo 1800101 105302105 := bstep (se 2 (by rfl) ⟨39488289, by rfl⟩ : syracuseStep 105302105 = 78976579) B78976579
theorem B20506769 : Blo 1800101 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B11856019 : Blo 1800101 11856019 := bstep (se 1 (by rfl) ⟨8892014, by rfl⟩ : syracuseStep 11856019 = 17784029) B17784029
theorem B5769427 : Blo 1800101 5769427 := bstep (se 1 (by rfl) ⟨4327070, by rfl⟩ : syracuseStep 5769427 = 8654141) B8654141
theorem B2279659 : Blo 1800101 2279659 := bstep (se 1 (by rfl) ⟨1709744, by rfl⟩ : syracuseStep 2279659 = 3419489) B3419489
theorem B4557343 : Blo 1800101 4557343 := bstep (se 1 (by rfl) ⟨3418007, by rfl⟩ : syracuseStep 4557343 = 6836015) B6836015
theorem B5925563 : Blo 1800101 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B20515517 : Blo 1800101 20515517 := bstep (se 3 (by rfl) ⟨3846659, by rfl⟩ : syracuseStep 20515517 = 7693319) B7693319
theorem B2026399 : Blo 1800101 2026399 := bstep (se 1 (by rfl) ⟨1519799, by rfl⟩ : syracuseStep 2026399 = 3039599) B3039599
theorem B2026543 : Blo 1800101 2026543 := bstep (se 1 (by rfl) ⟨1519907, by rfl⟩ : syracuseStep 2026543 = 3039815) B3039815
theorem B2739271 : Blo 1800101 2739271 := bstep (se 1 (by rfl) ⟨2054453, by rfl⟩ : syracuseStep 2739271 = 4108907) B4108907
theorem B4328569 : Blo 1800101 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B4386217 : Blo 1800101 4386217 := bstep (se 2 (by rfl) ⟨1644831, by rfl⟩ : syracuseStep 4386217 = 3289663) B3289663
theorem B4050359 : Blo 1800101 4050359 := bstep (se 1 (by rfl) ⟨3037769, by rfl⟩ : syracuseStep 4050359 = 6075539) B6075539
theorem B5475767 : Blo 1800101 5475767 := bstep (se 1 (by rfl) ⟨4106825, by rfl⟩ : syracuseStep 5475767 = 8213651) B8213651
theorem B8211901 : Blo 1800101 8211901 := bstep (se 3 (by rfl) ⟨1539731, by rfl⟩ : syracuseStep 8211901 = 3079463) B3079463
theorem B3845627 : Blo 1800101 3845627 := bstep (se 1 (by rfl) ⟨2884220, by rfl⟩ : syracuseStep 3845627 = 5768441) B5768441
theorem B4050539 : Blo 1800101 4050539 := bstep (se 1 (by rfl) ⟨3037904, by rfl⟩ : syracuseStep 4050539 = 6075809) B6075809
theorem B151973597 : Blo 1800101 151973597 := bstep (se 3 (by rfl) ⟨28495049, by rfl⟩ : syracuseStep 151973597 = 56990099) B56990099
theorem B4050809 : Blo 1800101 4050809 := bstep (se 2 (by rfl) ⟨1519053, by rfl⟩ : syracuseStep 4050809 = 3038107) B3038107
theorem B4935667 : Blo 1800101 4935667 := bstep (se 1 (by rfl) ⟨3701750, by rfl⟩ : syracuseStep 4935667 = 7403501) B7403501
theorem B3846455 : Blo 1800101 3846455 := bstep (se 1 (by rfl) ⟨2884841, by rfl⟩ : syracuseStep 3846455 = 5769683) B5769683
theorem B25956773 : Blo 1800101 25956773 := bstep (se 4 (by rfl) ⟨2433447, by rfl⟩ : syracuseStep 25956773 = 4866895) B4866895
theorem B49975957 : Blo 1800101 49975957 := bstep (se 6 (by rfl) ⟨1171311, by rfl⟩ : syracuseStep 49975957 = 2342623) B2342623
theorem B20509685 : Blo 1800101 20509685 := bstep (se 5 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 20509685 = 1922783) B1922783
theorem B6075431 : Blo 1800101 6075431 := bstep (se 1 (by rfl) ⟨4556573, by rfl⟩ : syracuseStep 6075431 = 9113147) B9113147
theorem B4559935 : Blo 1800101 4559935 := bstep (se 1 (by rfl) ⟨3419951, by rfl⟩ : syracuseStep 4559935 = 6839903) B6839903
theorem B2700395 : Blo 1800101 2700395 := bstep (se 1 (by rfl) ⟨2025296, by rfl⟩ : syracuseStep 2700395 = 4050593) B4050593
theorem B3847343 : Blo 1800101 3847343 := bstep (se 1 (by rfl) ⟨2885507, by rfl⟩ : syracuseStep 3847343 = 5771015) B5771015
theorem B4560047 : Blo 1800101 4560047 := bstep (se 1 (by rfl) ⟨3420035, by rfl⟩ : syracuseStep 4560047 = 6840071) B6840071
theorem B8213723 : Blo 1800101 8213723 := bstep (se 1 (by rfl) ⟨6160292, by rfl⟩ : syracuseStep 8213723 = 12320585) B12320585
theorem B2700635 : Blo 1800101 2700635 := bstep (se 1 (by rfl) ⟨2025476, by rfl⟩ : syracuseStep 2700635 = 4050953) B4050953
theorem B2700911 : Blo 1800101 2700911 := bstep (se 1 (by rfl) ⟨2025683, by rfl⟩ : syracuseStep 2700911 = 4051367) B4051367
theorem B2700983 : Blo 1800101 2700983 := bstep (se 1 (by rfl) ⟨2025737, by rfl⟩ : syracuseStep 2700983 = 4051475) B4051475
theorem B4052663 : Blo 1800101 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B58406615 : Blo 1800101 58406615 := bstep (se 1 (by rfl) ⟨43804961, by rfl⟩ : syracuseStep 58406615 = 87609923) B87609923
theorem B2701019 : Blo 1800101 2701019 := bstep (se 1 (by rfl) ⟨2025764, by rfl⟩ : syracuseStep 2701019 = 4051529) B4051529
theorem B2701193 : Blo 1800101 2701193 := bstep (se 2 (by rfl) ⟨1012947, by rfl⟩ : syracuseStep 2701193 = 2025895) B2025895
theorem B10254275 : Blo 1800101 10254275 := bstep (se 1 (by rfl) ⟨7690706, by rfl⟩ : syracuseStep 10254275 = 15381413) B15381413
theorem B1800175 : Blo 1800101 1800175 := bstep (se 1 (by rfl) ⟨1350131, by rfl⟩ : syracuseStep 1800175 = 2700263) B2700263
theorem B2701295 : Blo 1800101 2701295 := bstep (se 1 (by rfl) ⟨2025971, by rfl⟩ : syracuseStep 2701295 = 4051943) B4051943
theorem B6076511 : Blo 1800101 6076511 := bstep (se 1 (by rfl) ⟨4557383, by rfl⟩ : syracuseStep 6076511 = 9114767) B9114767
theorem B1800347 : Blo 1800101 1800347 := bstep (se 1 (by rfl) ⟨1350260, by rfl⟩ : syracuseStep 1800347 = 2700521) B2700521
theorem B16423073 : Blo 1800101 16423073 := bstep (se 2 (by rfl) ⟨6158652, by rfl⟩ : syracuseStep 16423073 = 12317305) B12317305
theorem B1800383 : Blo 1800101 1800383 := bstep (se 1 (by rfl) ⟨1350287, by rfl⟩ : syracuseStep 1800383 = 2700575) B2700575
theorem B2701547 : Blo 1800101 2701547 := bstep (se 1 (by rfl) ⟨2026160, by rfl⟩ : syracuseStep 2701547 = 4052321) B4052321
theorem B2701607 : Blo 1800101 2701607 := bstep (se 1 (by rfl) ⟨2026205, by rfl⟩ : syracuseStep 2701607 = 4052411) B4052411
theorem B1800495 : Blo 1800101 1800495 := bstep (se 1 (by rfl) ⟨1350371, by rfl⟩ : syracuseStep 1800495 = 2700743) B2700743
theorem B2701691 : Blo 1800101 2701691 := bstep (se 1 (by rfl) ⟨2026268, by rfl⟩ : syracuseStep 2701691 = 4052537) B4052537
theorem B1800731 : Blo 1800101 1800731 := bstep (se 1 (by rfl) ⟨1350548, by rfl⟩ : syracuseStep 1800731 = 2701097) B2701097
theorem B1800735 : Blo 1800101 1800735 := bstep (se 1 (by rfl) ⟨1350551, by rfl⟩ : syracuseStep 1800735 = 2701103) B2701103
theorem B2701961 : Blo 1800101 2701961 := bstep (se 2 (by rfl) ⟨1013235, by rfl⟩ : syracuseStep 2701961 = 2026471) B2026471
theorem B2702135 : Blo 1800101 2702135 := bstep (se 1 (by rfl) ⟨2026601, by rfl⟩ : syracuseStep 2702135 = 4053203) B4053203
theorem B6077267 : Blo 1800101 6077267 := bstep (se 1 (by rfl) ⟨4557950, by rfl⟩ : syracuseStep 6077267 = 9115901) B9115901
theorem B1801051 : Blo 1800101 1801051 := bstep (se 1 (by rfl) ⟨1350788, by rfl⟩ : syracuseStep 1801051 = 2701577) B2701577
theorem B2702171 : Blo 1800101 2702171 := bstep (se 1 (by rfl) ⟨2026628, by rfl⟩ : syracuseStep 2702171 = 4053257) B4053257
theorem B1801119 : Blo 1800101 1801119 := bstep (se 1 (by rfl) ⟨1350839, by rfl⟩ : syracuseStep 1801119 = 2701679) B2701679
theorem B6159311 : Blo 1800101 6159311 := bstep (se 1 (by rfl) ⟨4619483, by rfl⟩ : syracuseStep 6159311 = 9238967) B9238967
theorem B2702315 : Blo 1800101 2702315 := bstep (se 1 (by rfl) ⟨2026736, by rfl⟩ : syracuseStep 2702315 = 4053473) B4053473
theorem B3038249 : Blo 1800101 3038249 := bstep (se 2 (by rfl) ⟨1139343, by rfl⟩ : syracuseStep 3038249 = 2278687) B2278687
theorem B1801263 : Blo 1800101 1801263 := bstep (se 1 (by rfl) ⟨1350947, by rfl⟩ : syracuseStep 1801263 = 2701895) B2701895
theorem B5127239 : Blo 1800101 5127239 := bstep (se 1 (by rfl) ⟨3845429, by rfl⟩ : syracuseStep 5127239 = 7690859) B7690859
theorem B1801287 : Blo 1800101 1801287 := bstep (se 1 (by rfl) ⟨1350965, by rfl⟩ : syracuseStep 1801287 = 2701931) B2701931
theorem B118455371 : Blo 1800101 118455371 := bstep (se 1 (by rfl) ⟨88841528, by rfl⟩ : syracuseStep 118455371 = 177683057) B177683057
theorem B11541619 : Blo 1800101 11541619 := bstep (se 1 (by rfl) ⟨8656214, by rfl⟩ : syracuseStep 11541619 = 17312429) B17312429
theorem B2563255 : Blo 1800101 2563255 := bstep (se 1 (by rfl) ⟨1922441, by rfl⟩ : syracuseStep 2563255 = 3844883) B3844883
theorem B3038431 : Blo 1800101 3038431 := bstep (se 1 (by rfl) ⟨2278823, by rfl⟩ : syracuseStep 3038431 = 4557647) B4557647
theorem B1801439 : Blo 1800101 1801439 := bstep (se 1 (by rfl) ⟨1351079, by rfl⟩ : syracuseStep 1801439 = 2702159) B2702159
theorem B12975389 : Blo 1800101 12975389 := bstep (se 3 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 12975389 = 4865771) B4865771
theorem B6077807 : Blo 1800101 6077807 := bstep (se 1 (by rfl) ⟨4558355, by rfl⟩ : syracuseStep 6077807 = 9116711) B9116711
theorem B17538443 : Blo 1800101 17538443 := bstep (se 1 (by rfl) ⟨13153832, by rfl⟩ : syracuseStep 17538443 = 26307665) B26307665
theorem B3038863 : Blo 1800101 3038863 := bstep (se 1 (by rfl) ⟨2279147, by rfl⟩ : syracuseStep 3038863 = 4558295) B4558295
theorem B6078185 : Blo 1800101 6078185 := bstep (se 2 (by rfl) ⟨2279319, by rfl⟩ : syracuseStep 6078185 = 4558639) B4558639
theorem B5127923 : Blo 1800101 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B13672637 : Blo 1800101 13672637 := bstep (se 3 (by rfl) ⟨2563619, by rfl⟩ : syracuseStep 13672637 = 5127239) B5127239
theorem B2564303 : Blo 1800101 2564303 := bstep (se 1 (by rfl) ⟨1923227, by rfl⟩ : syracuseStep 2564303 = 3846455) B3846455
theorem B7692569 : Blo 1800101 7692569 := bstep (se 2 (by rfl) ⟨2884713, by rfl⟩ : syracuseStep 7692569 = 5769427) B5769427
theorem B3039545 : Blo 1800101 3039545 := bstep (se 2 (by rfl) ⟨1139829, by rfl⟩ : syracuseStep 3039545 = 2279659) B2279659
theorem B4162079 : Blo 1800101 4162079 := bstep (se 1 (by rfl) ⟨3121559, by rfl⟩ : syracuseStep 4162079 = 6243119) B6243119
theorem B12321353 : Blo 1800101 12321353 := bstep (se 2 (by rfl) ⟨4620507, by rfl⟩ : syracuseStep 12321353 = 9241015) B9241015
theorem B13673123 : Blo 1800101 13673123 := bstep (se 1 (by rfl) ⟨10254842, by rfl⟩ : syracuseStep 13673123 = 20509685) B20509685
theorem B3040031 : Blo 1800101 3040031 := bstep (se 1 (by rfl) ⟨2280023, by rfl⟩ : syracuseStep 3040031 = 4560047) B4560047
theorem B66634609 : Blo 1800101 66634609 := bstep (se 2 (by rfl) ⟨24987978, by rfl⟩ : syracuseStep 66634609 = 49975957) B49975957
theorem B15598655 : Blo 1800101 15598655 := bstep (se 1 (by rfl) ⟨11698991, by rfl⟩ : syracuseStep 15598655 = 23397983) B23397983
theorem B2163823 : Blo 1800101 2163823 := bstep (se 1 (by rfl) ⟨1622867, by rfl⟩ : syracuseStep 2163823 = 3245735) B3245735
theorem B38937743 : Blo 1800101 38937743 := bstep (se 1 (by rfl) ⟨29203307, by rfl⟩ : syracuseStep 38937743 = 58406615) B58406615
theorem B157844771 : Blo 1800101 157844771 := bstep (se 1 (by rfl) ⟨118383578, by rfl⟩ : syracuseStep 157844771 = 236767157) B236767157
theorem B6079913 : Blo 1800101 6079913 := bstep (se 2 (by rfl) ⟨2279967, by rfl⟩ : syracuseStep 6079913 = 4559935) B4559935
theorem B3950375 : Blo 1800101 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B4106207 : Blo 1800101 4106207 := bstep (se 1 (by rfl) ⟨3079655, by rfl⟩ : syracuseStep 4106207 = 6159311) B6159311
theorem B2025499 : Blo 1800101 2025499 := bstep (se 1 (by rfl) ⟨1519124, by rfl⟩ : syracuseStep 2025499 = 3038249) B3038249
theorem B11692295 : Blo 1800101 11692295 := bstep (se 1 (by rfl) ⟨8769221, by rfl⟩ : syracuseStep 11692295 = 17538443) B17538443
theorem B3418615 : Blo 1800101 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B6580889 : Blo 1800101 6580889 := bstep (se 2 (by rfl) ⟨2467833, by rfl⟩ : syracuseStep 6580889 = 4935667) B4935667
theorem B17304515 : Blo 1800101 17304515 := bstep (se 1 (by rfl) ⟨12978386, by rfl⟩ : syracuseStep 17304515 = 25956773) B25956773
theorem B13675553 : Blo 1800101 13675553 := bstep (se 2 (by rfl) ⟨5128332, by rfl⟩ : syracuseStep 13675553 = 10256665) B10256665
theorem B3845191 : Blo 1800101 3845191 := bstep (se 1 (by rfl) ⟨2883893, by rfl⟩ : syracuseStep 3845191 = 5767787) B5767787
theorem B8653949 : Blo 1800101 8653949 := bstep (se 3 (by rfl) ⟨1622615, by rfl⟩ : syracuseStep 8653949 = 3245231) B3245231
theorem B10259581 : Blo 1800101 10259581 := bstep (se 3 (by rfl) ⟨1923671, by rfl⟩ : syracuseStep 10259581 = 3847343) B3847343
theorem B4050287 : Blo 1800101 4050287 := bstep (se 1 (by rfl) ⟨3037715, by rfl⟩ : syracuseStep 4050287 = 6075431) B6075431
theorem B5475815 : Blo 1800101 5475815 := bstep (se 1 (by rfl) ⟨4106861, by rfl⟩ : syracuseStep 5475815 = 8213723) B8213723
theorem B14602045 : Blo 1800101 14602045 := bstep (se 3 (by rfl) ⟨2737883, by rfl⟩ : syracuseStep 14602045 = 5475767) B5475767
theorem B6836183 : Blo 1800101 6836183 := bstep (se 1 (by rfl) ⟨5127137, by rfl⟩ : syracuseStep 6836183 = 10254275) B10254275
theorem B70201403 : Blo 1800101 70201403 := bstep (se 1 (by rfl) ⟨52651052, by rfl⟩ : syracuseStep 70201403 = 105302105) B105302105
theorem B4051007 : Blo 1800101 4051007 := bstep (se 1 (by rfl) ⟨3038255, by rfl⟩ : syracuseStep 4051007 = 6076511) B6076511
theorem B10948715 : Blo 1800101 10948715 := bstep (se 1 (by rfl) ⟨8211536, by rfl⟩ : syracuseStep 10948715 = 16423073) B16423073
theorem B15388825 : Blo 1800101 15388825 := bstep (se 2 (by rfl) ⟨5770809, by rfl⟩ : syracuseStep 15388825 = 11541619) B11541619
theorem B5771425 : Blo 1800101 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B4051241 : Blo 1800101 4051241 := bstep (se 2 (by rfl) ⟨1519215, by rfl⟩ : syracuseStep 4051241 = 3038431) B3038431
theorem B13677011 : Blo 1800101 13677011 := bstep (se 1 (by rfl) ⟨10257758, by rfl⟩ : syracuseStep 13677011 = 20515517) B20515517
theorem B4051511 : Blo 1800101 4051511 := bstep (se 1 (by rfl) ⟨3038633, by rfl⟩ : syracuseStep 4051511 = 6077267) B6077267
theorem B405262925 : Blo 1800101 405262925 := bstep (se 3 (by rfl) ⟨75986798, by rfl⟩ : syracuseStep 405262925 = 151973597) B151973597
theorem B10949201 : Blo 1800101 10949201 := bstep (se 2 (by rfl) ⟨4105950, by rfl⟩ : syracuseStep 10949201 = 8211901) B8211901
theorem B4051817 : Blo 1800101 4051817 := bstep (se 2 (by rfl) ⟨1519431, by rfl⟩ : syracuseStep 4051817 = 3038863) B3038863
theorem B4051871 : Blo 1800101 4051871 := bstep (se 1 (by rfl) ⟨3038903, by rfl⟩ : syracuseStep 4051871 = 6077807) B6077807
theorem B2700239 : Blo 1800101 2700239 := bstep (se 1 (by rfl) ⟨2025179, by rfl⟩ : syracuseStep 2700239 = 4050359) B4050359
theorem B2700281 : Blo 1800101 2700281 := bstep (se 2 (by rfl) ⟨1012605, by rfl⟩ : syracuseStep 2700281 = 2025211) B2025211
theorem B2700329 : Blo 1800101 2700329 := bstep (se 2 (by rfl) ⟨1012623, by rfl⟩ : syracuseStep 2700329 = 2025247) B2025247
theorem B2700359 : Blo 1800101 2700359 := bstep (se 1 (by rfl) ⟨2025269, by rfl⟩ : syracuseStep 2700359 = 4050539) B4050539
theorem B4052123 : Blo 1800101 4052123 := bstep (se 1 (by rfl) ⟨3039092, by rfl⟩ : syracuseStep 4052123 = 6078185) B6078185
theorem B2700539 : Blo 1800101 2700539 := bstep (se 1 (by rfl) ⟨2025404, by rfl⟩ : syracuseStep 2700539 = 4050809) B4050809
theorem B7025993 : Blo 1800101 7025993 := bstep (se 2 (by rfl) ⟨2634747, by rfl⟩ : syracuseStep 7025993 = 5269495) B5269495
theorem B4560239 : Blo 1800101 4560239 := bstep (se 1 (by rfl) ⟨3420179, by rfl⟩ : syracuseStep 4560239 = 6840359) B6840359
theorem B6837641 : Blo 1800101 6837641 := bstep (se 2 (by rfl) ⟨2564115, by rfl⟩ : syracuseStep 6837641 = 5128231) B5128231
theorem B15808025 : Blo 1800101 15808025 := bstep (se 2 (by rfl) ⟨5928009, by rfl⟩ : syracuseStep 15808025 = 11856019) B11856019
theorem B2053723 : Blo 1800101 2053723 := bstep (se 1 (by rfl) ⟨1540292, by rfl⟩ : syracuseStep 2053723 = 3080585) B3080585
theorem B5199527 : Blo 1800101 5199527 := bstep (se 1 (by rfl) ⟨3899645, by rfl⟩ : syracuseStep 5199527 = 7799291) B7799291
theorem B4052699 : Blo 1800101 4052699 := bstep (se 1 (by rfl) ⟨3039524, by rfl⟩ : syracuseStep 4052699 = 6079049) B6079049
theorem B4052807 : Blo 1800101 4052807 := bstep (se 1 (by rfl) ⟨3039605, by rfl⟩ : syracuseStep 4052807 = 6079211) B6079211
theorem B6076457 : Blo 1800101 6076457 := bstep (se 2 (by rfl) ⟨2278671, by rfl⟩ : syracuseStep 6076457 = 4557343) B4557343
theorem B1800263 : Blo 1800101 1800263 := bstep (se 1 (by rfl) ⟨1350197, by rfl⟩ : syracuseStep 1800263 = 2700395) B2700395
theorem B6838415 : Blo 1800101 6838415 := bstep (se 1 (by rfl) ⟨5128811, by rfl⟩ : syracuseStep 6838415 = 10257623) B10257623
theorem B1800423 : Blo 1800101 1800423 := bstep (se 1 (by rfl) ⟨1350317, by rfl⟩ : syracuseStep 1800423 = 2700635) B2700635
theorem B15210767 : Blo 1800101 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B13670693 : Blo 1800101 13670693 := bstep (se 4 (by rfl) ⟨1281627, by rfl⟩ : syracuseStep 13670693 = 2563255) B2563255
theorem B1800607 : Blo 1800101 1800607 := bstep (se 1 (by rfl) ⟨1350455, by rfl⟩ : syracuseStep 1800607 = 2700911) B2700911
theorem B1800655 : Blo 1800101 1800655 := bstep (se 1 (by rfl) ⟨1350491, by rfl⟩ : syracuseStep 1800655 = 2700983) B2700983
theorem B2701775 : Blo 1800101 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B1923535 : Blo 1800101 1923535 := bstep (se 1 (by rfl) ⟨1442651, by rfl⟩ : syracuseStep 1923535 = 2885303) B2885303
theorem B1800679 : Blo 1800101 1800679 := bstep (se 1 (by rfl) ⟨1350509, by rfl⟩ : syracuseStep 1800679 = 2701019) B2701019
theorem B4446697 : Blo 1800101 4446697 := bstep (se 2 (by rfl) ⟨1667511, by rfl⟩ : syracuseStep 4446697 = 3335023) B3335023
theorem B2701865 : Blo 1800101 2701865 := bstep (se 2 (by rfl) ⟨1013199, by rfl⟩ : syracuseStep 2701865 = 2026399) B2026399
theorem B1800795 : Blo 1800101 1800795 := bstep (se 1 (by rfl) ⟨1350596, by rfl⟩ : syracuseStep 1800795 = 2701193) B2701193
theorem B1800863 : Blo 1800101 1800863 := bstep (se 1 (by rfl) ⟨1350647, by rfl⟩ : syracuseStep 1800863 = 2701295) B2701295
theorem B2702057 : Blo 1800101 2702057 := bstep (se 2 (by rfl) ⟨1013271, by rfl⟩ : syracuseStep 2702057 = 2026543) B2026543
theorem B3652361 : Blo 1800101 3652361 := bstep (se 2 (by rfl) ⟨1369635, by rfl⟩ : syracuseStep 3652361 = 2739271) B2739271
theorem B13671179 : Blo 1800101 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B1801031 : Blo 1800101 1801031 := bstep (se 1 (by rfl) ⟨1350773, by rfl⟩ : syracuseStep 1801031 = 2701547) B2701547
theorem B1801071 : Blo 1800101 1801071 := bstep (se 1 (by rfl) ⟨1350803, by rfl⟩ : syracuseStep 1801071 = 2701607) B2701607
theorem B1801127 : Blo 1800101 1801127 := bstep (se 1 (by rfl) ⟨1350845, by rfl⟩ : syracuseStep 1801127 = 2701691) B2701691
theorem B1801307 : Blo 1800101 1801307 := bstep (se 1 (by rfl) ⟨1350980, by rfl⟩ : syracuseStep 1801307 = 2701961) B2701961
theorem B1801423 : Blo 1800101 1801423 := bstep (se 1 (by rfl) ⟨1351067, by rfl⟩ : syracuseStep 1801423 = 2702135) B2702135
theorem B5848289 : Blo 1800101 5848289 := bstep (se 2 (by rfl) ⟨2193108, by rfl⟩ : syracuseStep 5848289 = 4386217) B4386217
theorem B1801447 : Blo 1800101 1801447 := bstep (se 1 (by rfl) ⟨1351085, by rfl⟩ : syracuseStep 1801447 = 2702171) B2702171
theorem B1801543 : Blo 1800101 1801543 := bstep (se 1 (by rfl) ⟨1351157, by rfl⟩ : syracuseStep 1801543 = 2702315) B2702315
theorem B78970247 : Blo 1800101 78970247 := bstep (se 1 (by rfl) ⟨59227685, by rfl⟩ : syracuseStep 78970247 = 118455371) B118455371
theorem B8650259 : Blo 1800101 8650259 := bstep (se 1 (by rfl) ⟨6487694, by rfl⟩ : syracuseStep 8650259 = 12975389) B12975389
theorem B2563751 : Blo 1800101 2563751 := bstep (se 1 (by rfl) ⟨1922813, by rfl⟩ : syracuseStep 2563751 = 3845627) B3845627
theorem B46800935 : Blo 1800101 46800935 := bstep (se 1 (by rfl) ⟨35100701, by rfl⟩ : syracuseStep 46800935 = 70201403) B70201403
theorem B7299143 : Blo 1800101 7299143 := bstep (se 1 (by rfl) ⟨5474357, by rfl⟩ : syracuseStep 7299143 = 10948715) B10948715
theorem B5128379 : Blo 1800101 5128379 := bstep (se 1 (by rfl) ⟨3846284, by rfl⟩ : syracuseStep 5128379 = 7692569) B7692569
theorem B9118007 : Blo 1800101 9118007 := bstep (se 1 (by rfl) ⟨6838505, by rfl⟩ : syracuseStep 9118007 = 13677011) B13677011
theorem B7299467 : Blo 1800101 7299467 := bstep (se 1 (by rfl) ⟨5474600, by rfl⟩ : syracuseStep 7299467 = 10949201) B10949201
theorem B2564713 : Blo 1800101 2564713 := bstep (se 2 (by rfl) ⟨961767, by rfl⟩ : syracuseStep 2564713 = 1923535) B1923535
theorem B3040159 : Blo 1800101 3040159 := bstep (se 1 (by rfl) ⟨2280119, by rfl⟩ : syracuseStep 3040159 = 4560239) B4560239
theorem B3466351 : Blo 1800101 3466351 := bstep (se 1 (by rfl) ⟨2599763, by rfl⟩ : syracuseStep 3466351 = 5199527) B5199527
theorem B2737471 : Blo 1800101 2737471 := bstep (se 1 (by rfl) ⟨2053103, by rfl⟩ : syracuseStep 2737471 = 4106207) B4106207
theorem B2434907 : Blo 1800101 2434907 := bstep (se 1 (by rfl) ⟨1826180, by rfl⟩ : syracuseStep 2434907 = 3652361) B3652361
theorem B11536343 : Blo 1800101 11536343 := bstep (se 1 (by rfl) ⟨8652257, by rfl⟩ : syracuseStep 11536343 = 17304515) B17304515
theorem B5769299 : Blo 1800101 5769299 := bstep (se 1 (by rfl) ⟨4326974, by rfl⟩ : syracuseStep 5769299 = 8653949) B8653949
theorem B2738297 : Blo 1800101 2738297 := bstep (se 2 (by rfl) ⟨1026861, by rfl⟩ : syracuseStep 2738297 = 2053723) B2053723
theorem B4557455 : Blo 1800101 4557455 := bstep (se 1 (by rfl) ⟨3418091, by rfl⟩ : syracuseStep 4557455 = 6836183) B6836183
theorem B2026363 : Blo 1800101 2026363 := bstep (se 1 (by rfl) ⟨1519772, by rfl⟩ : syracuseStep 2026363 = 3039545) B3039545
theorem B7695233 : Blo 1800101 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B270175283 : Blo 1800101 270175283 := bstep (se 1 (by rfl) ⟨202631462, by rfl⟩ : syracuseStep 270175283 = 405262925) B405262925
theorem B2026687 : Blo 1800101 2026687 := bstep (se 1 (by rfl) ⟨1520015, by rfl⟩ : syracuseStep 2026687 = 3040031) B3040031
theorem B4558153 : Blo 1800101 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B40562045 : Blo 1800101 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B10399103 : Blo 1800101 10399103 := bstep (se 1 (by rfl) ⟨7799327, by rfl⟩ : syracuseStep 10399103 = 15598655) B15598655
theorem B105229847 : Blo 1800101 105229847 := bstep (se 1 (by rfl) ⟨78922385, by rfl⟩ : syracuseStep 105229847 = 157844771) B157844771
theorem B4558427 : Blo 1800101 4558427 := bstep (se 1 (by rfl) ⟨3418820, by rfl⟩ : syracuseStep 4558427 = 6837641) B6837641
theorem B88846145 : Blo 1800101 88846145 := bstep (se 2 (by rfl) ⟨33317304, by rfl⟩ : syracuseStep 88846145 = 66634609) B66634609
theorem B4050971 : Blo 1800101 4050971 := bstep (se 1 (by rfl) ⟨3038228, by rfl⟩ : syracuseStep 4050971 = 6076457) B6076457
theorem B4558943 : Blo 1800101 4558943 := bstep (se 1 (by rfl) ⟨3419207, by rfl⟩ : syracuseStep 4558943 = 6838415) B6838415
theorem B7794863 : Blo 1800101 7794863 := bstep (se 1 (by rfl) ⟨5846147, by rfl⟩ : syracuseStep 7794863 = 11692295) B11692295
theorem B9113795 : Blo 1800101 9113795 := bstep (se 1 (by rfl) ⟨6835346, by rfl⟩ : syracuseStep 9113795 = 13670693) B13670693
theorem B4387259 : Blo 1800101 4387259 := bstep (se 1 (by rfl) ⟨3290444, by rfl⟩ : syracuseStep 4387259 = 6580889) B6580889
theorem B6836669 : Blo 1800101 6836669 := bstep (se 3 (by rfl) ⟨1281875, by rfl⟩ : syracuseStep 6836669 = 2563751) B2563751
theorem B9114119 : Blo 1800101 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B2700191 : Blo 1800101 2700191 := bstep (se 1 (by rfl) ⟨2025143, by rfl⟩ : syracuseStep 2700191 = 4050287) B4050287
theorem B52646831 : Blo 1800101 52646831 := bstep (se 1 (by rfl) ⟨39485123, by rfl⟩ : syracuseStep 52646831 = 78970247) B78970247
theorem B3650543 : Blo 1800101 3650543 := bstep (se 1 (by rfl) ⟨2737907, by rfl⟩ : syracuseStep 3650543 = 5475815) B5475815
theorem B19469393 : Blo 1800101 19469393 := bstep (se 2 (by rfl) ⟨7301022, by rfl⟩ : syracuseStep 19469393 = 14602045) B14602045
theorem B2700665 : Blo 1800101 2700665 := bstep (se 2 (by rfl) ⟨1012749, by rfl⟩ : syracuseStep 2700665 = 2025499) B2025499
theorem B2700671 : Blo 1800101 2700671 := bstep (se 1 (by rfl) ⟨2025503, by rfl⟩ : syracuseStep 2700671 = 4051007) B4051007
theorem B9115091 : Blo 1800101 9115091 := bstep (se 1 (by rfl) ⟨6836318, by rfl⟩ : syracuseStep 9115091 = 13672637) B13672637
theorem B2700827 : Blo 1800101 2700827 := bstep (se 1 (by rfl) ⟨2025620, by rfl⟩ : syracuseStep 2700827 = 4051241) B4051241
theorem B20518433 : Blo 1800101 20518433 := bstep (se 2 (by rfl) ⟨7694412, by rfl⟩ : syracuseStep 20518433 = 15388825) B15388825
theorem B2701007 : Blo 1800101 2701007 := bstep (se 1 (by rfl) ⟨2025755, by rfl⟩ : syracuseStep 2701007 = 4051511) B4051511
theorem B42137333 : Blo 1800101 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B9115415 : Blo 1800101 9115415 := bstep (se 1 (by rfl) ⟨6836561, by rfl⟩ : syracuseStep 9115415 = 13673123) B13673123
theorem B6838141 : Blo 1800101 6838141 := bstep (se 3 (by rfl) ⟨1282151, by rfl⟩ : syracuseStep 6838141 = 2564303) B2564303
theorem B2701211 : Blo 1800101 2701211 := bstep (se 1 (by rfl) ⟨2025908, by rfl⟩ : syracuseStep 2701211 = 4051817) B4051817
theorem B11540389 : Blo 1800101 11540389 := bstep (se 4 (by rfl) ⟨1081911, by rfl⟩ : syracuseStep 11540389 = 2163823) B2163823
theorem B2701247 : Blo 1800101 2701247 := bstep (se 1 (by rfl) ⟨2025935, by rfl⟩ : syracuseStep 2701247 = 4051871) B4051871
theorem B1800159 : Blo 1800101 1800159 := bstep (se 1 (by rfl) ⟨1350119, by rfl⟩ : syracuseStep 1800159 = 2700239) B2700239
theorem B5928929 : Blo 1800101 5928929 := bstep (se 2 (by rfl) ⟨2223348, by rfl⟩ : syracuseStep 5928929 = 4446697) B4446697
theorem B1800187 : Blo 1800101 1800187 := bstep (se 1 (by rfl) ⟨1350140, by rfl⟩ : syracuseStep 1800187 = 2700281) B2700281
theorem B1800219 : Blo 1800101 1800219 := bstep (se 1 (by rfl) ⟨1350164, by rfl⟩ : syracuseStep 1800219 = 2700329) B2700329
theorem B1800239 : Blo 1800101 1800239 := bstep (se 1 (by rfl) ⟨1350179, by rfl⟩ : syracuseStep 1800239 = 2700359) B2700359
theorem B25958495 : Blo 1800101 25958495 := bstep (se 1 (by rfl) ⟨19468871, by rfl⟩ : syracuseStep 25958495 = 38937743) B38937743
theorem B2701415 : Blo 1800101 2701415 := bstep (se 1 (by rfl) ⟨2026061, by rfl⟩ : syracuseStep 2701415 = 4052123) B4052123
theorem B1800359 : Blo 1800101 1800359 := bstep (se 1 (by rfl) ⟨1350269, by rfl⟩ : syracuseStep 1800359 = 2700539) B2700539
theorem B4683995 : Blo 1800101 4683995 := bstep (se 1 (by rfl) ⟨3512996, by rfl⟩ : syracuseStep 4683995 = 7025993) B7025993
theorem B4053275 : Blo 1800101 4053275 := bstep (se 1 (by rfl) ⟨3039956, by rfl⟩ : syracuseStep 4053275 = 6079913) B6079913
theorem B2701799 : Blo 1800101 2701799 := bstep (se 1 (by rfl) ⟨2026349, by rfl⟩ : syracuseStep 2701799 = 4052699) B4052699
theorem B2701871 : Blo 1800101 2701871 := bstep (se 1 (by rfl) ⟨2026403, by rfl⟩ : syracuseStep 2701871 = 4052807) B4052807
theorem B42154733 : Blo 1800101 42154733 := bstep (se 3 (by rfl) ⟨7904012, by rfl⟩ : syracuseStep 42154733 = 15808025) B15808025
theorem B11098877 : Blo 1800101 11098877 := bstep (se 3 (by rfl) ⟨2081039, by rfl⟩ : syracuseStep 11098877 = 4162079) B4162079
theorem B5126921 : Blo 1800101 5126921 := bstep (se 2 (by rfl) ⟨1922595, by rfl⟩ : syracuseStep 5126921 = 3845191) B3845191
theorem B13679441 : Blo 1800101 13679441 := bstep (se 2 (by rfl) ⟨5129790, by rfl⟩ : syracuseStep 13679441 = 10259581) B10259581
theorem B32856941 : Blo 1800101 32856941 := bstep (se 3 (by rfl) ⟨6160676, by rfl⟩ : syracuseStep 32856941 = 12321353) B12321353
theorem B1801183 : Blo 1800101 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B1801243 : Blo 1800101 1801243 := bstep (se 1 (by rfl) ⟨1350932, by rfl⟩ : syracuseStep 1801243 = 2701865) B2701865
theorem B1801371 : Blo 1800101 1801371 := bstep (se 1 (by rfl) ⟨1351028, by rfl⟩ : syracuseStep 1801371 = 2702057) B2702057
theorem B9117035 : Blo 1800101 9117035 := bstep (se 1 (by rfl) ⟨6837776, by rfl⟩ : syracuseStep 9117035 = 13675553) B13675553
theorem B3898859 : Blo 1800101 3898859 := bstep (se 1 (by rfl) ⟨2924144, by rfl⟩ : syracuseStep 3898859 = 5848289) B5848289
theorem B5766839 : Blo 1800101 5766839 := bstep (se 1 (by rfl) ⟨4325129, by rfl⟩ : syracuseStep 5766839 = 8650259) B8650259
theorem B4866095 : Blo 1800101 4866095 := bstep (se 1 (by rfl) ⟨3649571, by rfl⟩ : syracuseStep 4866095 = 7299143) B7299143
theorem B3039295 : Blo 1800101 3039295 := bstep (se 1 (by rfl) ⟨2279471, by rfl⟩ : syracuseStep 3039295 = 4558943) B4558943
theorem B6078671 : Blo 1800101 6078671 := bstep (se 1 (by rfl) ⟨4559003, by rfl⟩ : syracuseStep 6078671 = 9118007) B9118007
theorem B4866311 : Blo 1800101 4866311 := bstep (se 1 (by rfl) ⟨3649733, by rfl⟩ : syracuseStep 4866311 = 7299467) B7299467
theorem B2924839 : Blo 1800101 2924839 := bstep (se 1 (by rfl) ⟨2193629, by rfl⟩ : syracuseStep 2924839 = 4387259) B4387259
theorem B28091555 : Blo 1800101 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B10396957 : Blo 1800101 10396957 := bstep (se 3 (by rfl) ⟨1949429, by rfl⟩ : syracuseStep 10396957 = 3898859) B3898859
theorem B3122663 : Blo 1800101 3122663 := bstep (se 1 (by rfl) ⟨2341997, by rfl⟩ : syracuseStep 3122663 = 4683995) B4683995
theorem B4621801 : Blo 1800101 4621801 := bstep (se 2 (by rfl) ⟨1733175, by rfl⟩ : syracuseStep 4621801 = 3466351) B3466351
theorem B3417947 : Blo 1800101 3417947 := bstep (se 1 (by rfl) ⟨2563460, by rfl⟩ : syracuseStep 3417947 = 5126921) B5126921
theorem B9119627 : Blo 1800101 9119627 := bstep (se 1 (by rfl) ⟨6839720, by rfl⟩ : syracuseStep 9119627 = 13679441) B13679441
theorem B5130155 : Blo 1800101 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B6932735 : Blo 1800101 6932735 := bstep (se 1 (by rfl) ⟨5199551, by rfl⟩ : syracuseStep 6932735 = 10399103) B10399103
theorem B3844559 : Blo 1800101 3844559 := bstep (se 1 (by rfl) ⟨2883419, by rfl⟩ : syracuseStep 3844559 = 5766839) B5766839
theorem B38939125 : Blo 1800101 38939125 := bstep (se 5 (by rfl) ⟨1825271, by rfl⟩ : syracuseStep 38939125 = 3650543) B3650543
theorem B59230763 : Blo 1800101 59230763 := bstep (se 1 (by rfl) ⟨44423072, by rfl⟩ : syracuseStep 59230763 = 88846145) B88846145
theorem B15387185 : Blo 1800101 15387185 := bstep (se 2 (by rfl) ⟨5770194, by rfl⟩ : syracuseStep 15387185 = 11540389) B11540389
theorem B5196575 : Blo 1800101 5196575 := bstep (se 1 (by rfl) ⟨3897431, by rfl⟩ : syracuseStep 5196575 = 7794863) B7794863
theorem B3418919 : Blo 1800101 3418919 := bstep (se 1 (by rfl) ⟨2564189, by rfl⟩ : syracuseStep 3418919 = 5128379) B5128379
theorem B4557779 : Blo 1800101 4557779 := bstep (se 1 (by rfl) ⟨3418334, by rfl⟩ : syracuseStep 4557779 = 6836669) B6836669
theorem B7302125 : Blo 1800101 7302125 := bstep (se 3 (by rfl) ⟨1369148, by rfl⟩ : syracuseStep 7302125 = 2738297) B2738297
theorem B35097887 : Blo 1800101 35097887 := bstep (se 1 (by rfl) ⟨26323415, by rfl⟩ : syracuseStep 35097887 = 52646831) B52646831
theorem B12979595 : Blo 1800101 12979595 := bstep (se 1 (by rfl) ⟨9734696, by rfl⟩ : syracuseStep 12979595 = 19469393) B19469393
theorem B3952619 : Blo 1800101 3952619 := bstep (se 1 (by rfl) ⟨2964464, by rfl⟩ : syracuseStep 3952619 = 5928929) B5928929
theorem B3846199 : Blo 1800101 3846199 := bstep (se 1 (by rfl) ⟨2884649, by rfl⟩ : syracuseStep 3846199 = 5769299) B5769299
theorem B17305663 : Blo 1800101 17305663 := bstep (se 1 (by rfl) ⟨12979247, by rfl⟩ : syracuseStep 17305663 = 25958495) B25958495
theorem B3649961 : Blo 1800101 3649961 := bstep (se 2 (by rfl) ⟨1368735, by rfl⟩ : syracuseStep 3649961 = 2737471) B2737471
theorem B28103155 : Blo 1800101 28103155 := bstep (se 1 (by rfl) ⟨21077366, by rfl⟩ : syracuseStep 28103155 = 42154733) B42154733
theorem B6493085 : Blo 1800101 6493085 := bstep (se 3 (by rfl) ⟨1217453, by rfl⟩ : syracuseStep 6493085 = 2434907) B2434907
theorem B70153231 : Blo 1800101 70153231 := bstep (se 1 (by rfl) ⟨52614923, by rfl⟩ : syracuseStep 70153231 = 105229847) B105229847
theorem B2700647 : Blo 1800101 2700647 := bstep (se 1 (by rfl) ⟨2025485, by rfl⟩ : syracuseStep 2700647 = 4050971) B4050971
theorem B31200623 : Blo 1800101 31200623 := bstep (se 1 (by rfl) ⟨23400467, by rfl⟩ : syracuseStep 31200623 = 46800935) B46800935
theorem B6075863 : Blo 1800101 6075863 := bstep (se 1 (by rfl) ⟨4556897, by rfl⟩ : syracuseStep 6075863 = 9113795) B9113795
theorem B6076079 : Blo 1800101 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B13678469 : Blo 1800101 13678469 := bstep (se 4 (by rfl) ⟨1282356, by rfl⟩ : syracuseStep 13678469 = 2564713) B2564713
theorem B1800127 : Blo 1800101 1800127 := bstep (se 1 (by rfl) ⟨1350095, by rfl⟩ : syracuseStep 1800127 = 2700191) B2700191
theorem B1800443 : Blo 1800101 1800443 := bstep (se 1 (by rfl) ⟨1350332, by rfl⟩ : syracuseStep 1800443 = 2700665) B2700665
theorem B1800447 : Blo 1800101 1800447 := bstep (se 1 (by rfl) ⟨1350335, by rfl⟩ : syracuseStep 1800447 = 2700671) B2700671
theorem B6076727 : Blo 1800101 6076727 := bstep (se 1 (by rfl) ⟨4557545, by rfl⟩ : syracuseStep 6076727 = 9115091) B9115091
theorem B1800551 : Blo 1800101 1800551 := bstep (se 1 (by rfl) ⟨1350413, by rfl⟩ : syracuseStep 1800551 = 2700827) B2700827
theorem B13678955 : Blo 1800101 13678955 := bstep (se 1 (by rfl) ⟨10259216, by rfl⟩ : syracuseStep 13678955 = 20518433) B20518433
theorem B1800671 : Blo 1800101 1800671 := bstep (se 1 (by rfl) ⟨1350503, by rfl⟩ : syracuseStep 1800671 = 2701007) B2701007
theorem B2701817 : Blo 1800101 2701817 := bstep (se 2 (by rfl) ⟨1013181, by rfl⟩ : syracuseStep 2701817 = 2026363) B2026363
theorem B6076943 : Blo 1800101 6076943 := bstep (se 1 (by rfl) ⟨4557707, by rfl⟩ : syracuseStep 6076943 = 9115415) B9115415
theorem B4053545 : Blo 1800101 4053545 := bstep (se 2 (by rfl) ⟨1520079, by rfl⟩ : syracuseStep 4053545 = 3040159) B3040159
theorem B1800807 : Blo 1800101 1800807 := bstep (se 1 (by rfl) ⟨1350605, by rfl⟩ : syracuseStep 1800807 = 2701211) B2701211
theorem B1800831 : Blo 1800101 1800831 := bstep (se 1 (by rfl) ⟨1350623, by rfl⟩ : syracuseStep 1800831 = 2701247) B2701247
theorem B7690895 : Blo 1800101 7690895 := bstep (se 1 (by rfl) ⟨5768171, by rfl⟩ : syracuseStep 7690895 = 11536343) B11536343
theorem B1800943 : Blo 1800101 1800943 := bstep (se 1 (by rfl) ⟨1350707, by rfl⟩ : syracuseStep 1800943 = 2701415) B2701415
theorem B2702183 : Blo 1800101 2702183 := bstep (se 1 (by rfl) ⟨2026637, by rfl⟩ : syracuseStep 2702183 = 4053275) B4053275
theorem B2702249 : Blo 1800101 2702249 := bstep (se 2 (by rfl) ⟨1013343, by rfl⟩ : syracuseStep 2702249 = 2026687) B2026687
theorem B1801199 : Blo 1800101 1801199 := bstep (se 1 (by rfl) ⟨1350899, by rfl⟩ : syracuseStep 1801199 = 2701799) B2701799
theorem B1801247 : Blo 1800101 1801247 := bstep (se 1 (by rfl) ⟨1350935, by rfl⟩ : syracuseStep 1801247 = 2701871) B2701871
theorem B3038303 : Blo 1800101 3038303 := bstep (se 1 (by rfl) ⟨2278727, by rfl⟩ : syracuseStep 3038303 = 4557455) B4557455
theorem B6077537 : Blo 1800101 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B21904627 : Blo 1800101 21904627 := bstep (se 1 (by rfl) ⟨16428470, by rfl⟩ : syracuseStep 21904627 = 32856941) B32856941
theorem B29597005 : Blo 1800101 29597005 := bstep (se 3 (by rfl) ⟨5549438, by rfl⟩ : syracuseStep 29597005 = 11098877) B11098877
theorem B180116855 : Blo 1800101 180116855 := bstep (se 1 (by rfl) ⟨135087641, by rfl⟩ : syracuseStep 180116855 = 270175283) B270175283
theorem B6078023 : Blo 1800101 6078023 := bstep (se 1 (by rfl) ⟨4558517, by rfl⟩ : syracuseStep 6078023 = 9117035) B9117035
theorem B27041363 : Blo 1800101 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B3038951 : Blo 1800101 3038951 := bstep (se 1 (by rfl) ⟨2279213, by rfl⟩ : syracuseStep 3038951 = 4558427) B4558427
theorem B9117521 : Blo 1800101 9117521 := bstep (se 2 (by rfl) ⟨3419070, by rfl⟩ : syracuseStep 9117521 = 6838141) B6838141
theorem B3244063 : Blo 1800101 3244063 := bstep (se 1 (by rfl) ⟨2433047, by rfl⟩ : syracuseStep 3244063 = 4866095) B4866095
theorem B5128265 : Blo 1800101 5128265 := bstep (se 2 (by rfl) ⟨1923099, by rfl⟩ : syracuseStep 5128265 = 3846199) B3846199
theorem B3244207 : Blo 1800101 3244207 := bstep (se 1 (by rfl) ⟨2433155, by rfl⟩ : syracuseStep 3244207 = 4866311) B4866311
theorem B18727703 : Blo 1800101 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B20800415 : Blo 1800101 20800415 := bstep (se 1 (by rfl) ⟨15600311, by rfl⟩ : syracuseStep 20800415 = 31200623) B31200623
theorem B9733229 : Blo 1800101 9733229 := bstep (se 3 (by rfl) ⟨1824980, by rfl⟩ : syracuseStep 9733229 = 3649961) B3649961
theorem B2278631 : Blo 1800101 2278631 := bstep (se 1 (by rfl) ⟨1708973, by rfl⟩ : syracuseStep 2278631 = 3417947) B3417947
theorem B9118979 : Blo 1800101 9118979 := bstep (se 1 (by rfl) ⟨6839234, by rfl⟩ : syracuseStep 9118979 = 13678469) B13678469
theorem B6079751 : Blo 1800101 6079751 := bstep (se 1 (by rfl) ⟨4559813, by rfl⟩ : syracuseStep 6079751 = 9119627) B9119627
theorem B93537641 : Blo 1800101 93537641 := bstep (se 2 (by rfl) ⟨35076615, by rfl⟩ : syracuseStep 93537641 = 70153231) B70153231
theorem B4621823 : Blo 1800101 4621823 := bstep (se 1 (by rfl) ⟨3466367, by rfl⟩ : syracuseStep 4621823 = 6932735) B6932735
theorem B15599141 : Blo 1800101 15599141 := bstep (se 4 (by rfl) ⟨1462419, by rfl⟩ : syracuseStep 15599141 = 2924839) B2924839
theorem B9119303 : Blo 1800101 9119303 := bstep (se 1 (by rfl) ⟨6839477, by rfl⟩ : syracuseStep 9119303 = 13678955) B13678955
theorem B29206169 : Blo 1800101 29206169 := bstep (se 2 (by rfl) ⟨10952313, by rfl⟩ : syracuseStep 29206169 = 21904627) B21904627
theorem B39487175 : Blo 1800101 39487175 := bstep (se 1 (by rfl) ⟨29615381, by rfl⟩ : syracuseStep 39487175 = 59230763) B59230763
theorem B10258123 : Blo 1800101 10258123 := bstep (se 1 (by rfl) ⟨7693592, by rfl⟩ : syracuseStep 10258123 = 15387185) B15387185
theorem B13862609 : Blo 1800101 13862609 := bstep (se 2 (by rfl) ⟨5198478, by rfl⟩ : syracuseStep 13862609 = 10396957) B10396957
theorem B39462673 : Blo 1800101 39462673 := bstep (se 2 (by rfl) ⟨14798502, by rfl⟩ : syracuseStep 39462673 = 29597005) B29597005
theorem B2279279 : Blo 1800101 2279279 := bstep (se 1 (by rfl) ⟨1709459, by rfl⟩ : syracuseStep 2279279 = 3418919) B3418919
theorem B6162401 : Blo 1800101 6162401 := bstep (se 2 (by rfl) ⟨2310900, by rfl⟩ : syracuseStep 6162401 = 4621801) B4621801
theorem B4868083 : Blo 1800101 4868083 := bstep (se 1 (by rfl) ⟨3651062, by rfl⟩ : syracuseStep 4868083 = 7302125) B7302125
theorem B2025535 : Blo 1800101 2025535 := bstep (se 1 (by rfl) ⟨1519151, by rfl⟩ : syracuseStep 2025535 = 3038303) B3038303
theorem B23398591 : Blo 1800101 23398591 := bstep (se 1 (by rfl) ⟨17548943, by rfl⟩ : syracuseStep 23398591 = 35097887) B35097887
theorem B8653063 : Blo 1800101 8653063 := bstep (se 1 (by rfl) ⟨6489797, by rfl⟩ : syracuseStep 8653063 = 12979595) B12979595
theorem B2025967 : Blo 1800101 2025967 := bstep (se 1 (by rfl) ⟨1519475, by rfl⟩ : syracuseStep 2025967 = 3038951) B3038951
theorem B149883493 : Blo 1800101 149883493 := bstep (se 4 (by rfl) ⟨14051577, by rfl⟩ : syracuseStep 149883493 = 28103155) B28103155
theorem B4328723 : Blo 1800101 4328723 := bstep (se 1 (by rfl) ⟨3246542, by rfl⟩ : syracuseStep 4328723 = 6493085) B6493085
theorem B4050575 : Blo 1800101 4050575 := bstep (se 1 (by rfl) ⟨3037931, by rfl⟩ : syracuseStep 4050575 = 6075863) B6075863
theorem B4050719 : Blo 1800101 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B4051151 : Blo 1800101 4051151 := bstep (se 1 (by rfl) ⟨3038363, by rfl⟩ : syracuseStep 4051151 = 6076727) B6076727
theorem B4051295 : Blo 1800101 4051295 := bstep (se 1 (by rfl) ⟨3038471, by rfl⟩ : syracuseStep 4051295 = 6076943) B6076943
theorem B4051691 : Blo 1800101 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B4052015 : Blo 1800101 4052015 := bstep (se 1 (by rfl) ⟨3039011, by rfl⟩ : syracuseStep 4052015 = 6078023) B6078023
theorem B18027575 : Blo 1800101 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B42161269 : Blo 1800101 42161269 := bstep (se 5 (by rfl) ⟨1976309, by rfl⟩ : syracuseStep 42161269 = 3952619) B3952619
theorem B23074217 : Blo 1800101 23074217 := bstep (se 2 (by rfl) ⟨8652831, by rfl⟩ : syracuseStep 23074217 = 17305663) B17305663
theorem B4052393 : Blo 1800101 4052393 := bstep (se 2 (by rfl) ⟨1519647, by rfl⟩ : syracuseStep 4052393 = 3039295) B3039295
theorem B4052447 : Blo 1800101 4052447 := bstep (se 1 (by rfl) ⟨3039335, by rfl⟩ : syracuseStep 4052447 = 6078671) B6078671
theorem B51918833 : Blo 1800101 51918833 := bstep (se 2 (by rfl) ⟨19469562, by rfl⟩ : syracuseStep 51918833 = 38939125) B38939125
theorem B1800431 : Blo 1800101 1800431 := bstep (se 1 (by rfl) ⟨1350323, by rfl⟩ : syracuseStep 1800431 = 2700647) B2700647
theorem B2563039 : Blo 1800101 2563039 := bstep (se 1 (by rfl) ⟨1922279, by rfl⟩ : syracuseStep 2563039 = 3844559) B3844559
theorem B1801211 : Blo 1800101 1801211 := bstep (se 1 (by rfl) ⟨1350908, by rfl⟩ : syracuseStep 1801211 = 2701817) B2701817
theorem B2702363 : Blo 1800101 2702363 := bstep (se 1 (by rfl) ⟨2026772, by rfl⟩ : syracuseStep 2702363 = 4053545) B4053545
theorem B5127263 : Blo 1800101 5127263 := bstep (se 1 (by rfl) ⟨3845447, by rfl⟩ : syracuseStep 5127263 = 7690895) B7690895
theorem B3464383 : Blo 1800101 3464383 := bstep (se 1 (by rfl) ⟨2598287, by rfl⟩ : syracuseStep 3464383 = 5196575) B5196575
theorem B1801455 : Blo 1800101 1801455 := bstep (se 1 (by rfl) ⟨1351091, by rfl⟩ : syracuseStep 1801455 = 2702183) B2702183
theorem B1801499 : Blo 1800101 1801499 := bstep (se 1 (by rfl) ⟨1351124, by rfl⟩ : syracuseStep 1801499 = 2702249) B2702249
theorem B3038519 : Blo 1800101 3038519 := bstep (se 1 (by rfl) ⟨2278889, by rfl⟩ : syracuseStep 3038519 = 4557779) B4557779
theorem B120077903 : Blo 1800101 120077903 := bstep (se 1 (by rfl) ⟨90058427, by rfl⟩ : syracuseStep 120077903 = 180116855) B180116855
theorem B33308405 : Blo 1800101 33308405 := bstep (se 5 (by rfl) ⟨1561331, by rfl⟩ : syracuseStep 33308405 = 3122663) B3122663
theorem B13680413 : Blo 1800101 13680413 := bstep (se 3 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 13680413 = 5130155) B5130155
theorem B6078347 : Blo 1800101 6078347 := bstep (se 1 (by rfl) ⟨4558760, by rfl⟩ : syracuseStep 6078347 = 9117521) B9117521
theorem B4325417 : Blo 1800101 4325417 := bstep (se 2 (by rfl) ⟨1622031, by rfl⟩ : syracuseStep 4325417 = 3244063) B3244063
theorem B4325609 : Blo 1800101 4325609 := bstep (se 2 (by rfl) ⟨1622103, by rfl⟩ : syracuseStep 4325609 = 3244207) B3244207
theorem B12485135 : Blo 1800101 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B12018383 : Blo 1800101 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B6488819 : Blo 1800101 6488819 := bstep (se 1 (by rfl) ⟨4866614, by rfl⟩ : syracuseStep 6488819 = 9733229) B9733229
theorem B199844657 : Blo 1800101 199844657 := bstep (se 2 (by rfl) ⟨74941746, by rfl⟩ : syracuseStep 199844657 = 149883493) B149883493
theorem B6079319 : Blo 1800101 6079319 := bstep (se 1 (by rfl) ⟨4559489, by rfl⟩ : syracuseStep 6079319 = 9118979) B9118979
theorem B62358427 : Blo 1800101 62358427 := bstep (se 1 (by rfl) ⟨46768820, by rfl⟩ : syracuseStep 62358427 = 93537641) B93537641
theorem B3081215 : Blo 1800101 3081215 := bstep (se 1 (by rfl) ⟨2310911, by rfl⟩ : syracuseStep 3081215 = 4621823) B4621823
theorem B6079535 : Blo 1800101 6079535 := bstep (se 1 (by rfl) ⟨4559651, by rfl⟩ : syracuseStep 6079535 = 9119303) B9119303
theorem B9241739 : Blo 1800101 9241739 := bstep (se 1 (by rfl) ⟨6931304, by rfl⟩ : syracuseStep 9241739 = 13862609) B13862609
theorem B3417385 : Blo 1800101 3417385 := bstep (se 2 (by rfl) ⟨1281519, by rfl⟩ : syracuseStep 3417385 = 2563039) B2563039
theorem B34612555 : Blo 1800101 34612555 := bstep (se 1 (by rfl) ⟨25959416, by rfl⟩ : syracuseStep 34612555 = 51918833) B51918833
theorem B56215025 : Blo 1800101 56215025 := bstep (se 2 (by rfl) ⟨21080634, by rfl⟩ : syracuseStep 56215025 = 42161269) B42161269
theorem B3418175 : Blo 1800101 3418175 := bstep (se 1 (by rfl) ⟨2563631, by rfl⟩ : syracuseStep 3418175 = 5127263) B5127263
theorem B2885815 : Blo 1800101 2885815 := bstep (se 1 (by rfl) ⟨2164361, by rfl⟩ : syracuseStep 2885815 = 4328723) B4328723
theorem B2025679 : Blo 1800101 2025679 := bstep (se 1 (by rfl) ⟨1519259, by rfl⟩ : syracuseStep 2025679 = 3038519) B3038519
theorem B9120275 : Blo 1800101 9120275 := bstep (se 1 (by rfl) ⟨6840206, by rfl⟩ : syracuseStep 9120275 = 13680413) B13680413
theorem B6490777 : Blo 1800101 6490777 := bstep (se 2 (by rfl) ⟨2434041, by rfl⟩ : syracuseStep 6490777 = 4868083) B4868083
theorem B3418843 : Blo 1800101 3418843 := bstep (se 1 (by rfl) ⟨2564132, by rfl⟩ : syracuseStep 3418843 = 5128265) B5128265
theorem B31198121 : Blo 1800101 31198121 := bstep (se 2 (by rfl) ⟨11699295, by rfl⟩ : syracuseStep 31198121 = 23398591) B23398591
theorem B11537417 : Blo 1800101 11537417 := bstep (se 2 (by rfl) ⟨4326531, by rfl⟩ : syracuseStep 11537417 = 8653063) B8653063
theorem B10399427 : Blo 1800101 10399427 := bstep (se 1 (by rfl) ⟨7799570, by rfl⟩ : syracuseStep 10399427 = 15599141) B15599141
theorem B26324783 : Blo 1800101 26324783 := bstep (se 1 (by rfl) ⟨19743587, by rfl⟩ : syracuseStep 26324783 = 39487175) B39487175
theorem B4108267 : Blo 1800101 4108267 := bstep (se 1 (by rfl) ⟨3081200, by rfl⟩ : syracuseStep 4108267 = 6162401) B6162401
theorem B13677497 : Blo 1800101 13677497 := bstep (se 2 (by rfl) ⟨5129061, by rfl⟩ : syracuseStep 13677497 = 10258123) B10258123
theorem B2700383 : Blo 1800101 2700383 := bstep (se 1 (by rfl) ⟨2025287, by rfl⟩ : syracuseStep 2700383 = 4050575) B4050575
theorem B22205603 : Blo 1800101 22205603 := bstep (se 1 (by rfl) ⟨16654202, by rfl⟩ : syracuseStep 22205603 = 33308405) B33308405
theorem B2700479 : Blo 1800101 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B4052231 : Blo 1800101 4052231 := bstep (se 1 (by rfl) ⟨3039173, by rfl⟩ : syracuseStep 4052231 = 6078347) B6078347
theorem B2700713 : Blo 1800101 2700713 := bstep (se 2 (by rfl) ⟨1012767, by rfl⟩ : syracuseStep 2700713 = 2025535) B2025535
theorem B2700767 : Blo 1800101 2700767 := bstep (se 1 (by rfl) ⟨2025575, by rfl⟩ : syracuseStep 2700767 = 4051151) B4051151
theorem B2700863 : Blo 1800101 2700863 := bstep (se 1 (by rfl) ⟨2025647, by rfl⟩ : syracuseStep 2700863 = 4051295) B4051295
theorem B2701127 : Blo 1800101 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B6076349 : Blo 1800101 6076349 := bstep (se 3 (by rfl) ⟨1139315, by rfl⟩ : syracuseStep 6076349 = 2278631) B2278631
theorem B2701289 : Blo 1800101 2701289 := bstep (se 2 (by rfl) ⟨1012983, by rfl⟩ : syracuseStep 2701289 = 2025967) B2025967
theorem B2701343 : Blo 1800101 2701343 := bstep (se 1 (by rfl) ⟨2026007, by rfl⟩ : syracuseStep 2701343 = 4052015) B4052015
theorem B4053167 : Blo 1800101 4053167 := bstep (se 1 (by rfl) ⟨3039875, by rfl⟩ : syracuseStep 4053167 = 6079751) B6079751
theorem B15382811 : Blo 1800101 15382811 := bstep (se 1 (by rfl) ⟨11537108, by rfl⟩ : syracuseStep 15382811 = 23074217) B23074217
theorem B2701595 : Blo 1800101 2701595 := bstep (se 1 (by rfl) ⟨2026196, by rfl⟩ : syracuseStep 2701595 = 4052393) B4052393
theorem B2701631 : Blo 1800101 2701631 := bstep (se 1 (by rfl) ⟨2026223, by rfl⟩ : syracuseStep 2701631 = 4052447) B4052447
theorem B19470779 : Blo 1800101 19470779 := bstep (se 1 (by rfl) ⟨14603084, by rfl⟩ : syracuseStep 19470779 = 29206169) B29206169
theorem B4619177 : Blo 1800101 4619177 := bstep (se 2 (by rfl) ⟨1732191, by rfl⟩ : syracuseStep 4619177 = 3464383) B3464383
theorem B1801575 : Blo 1800101 1801575 := bstep (se 1 (by rfl) ⟨1351181, by rfl⟩ : syracuseStep 1801575 = 2702363) B2702363
theorem B6078077 : Blo 1800101 6078077 := bstep (se 3 (by rfl) ⟨1139639, by rfl⟩ : syracuseStep 6078077 = 2279279) B2279279
theorem B52616897 : Blo 1800101 52616897 := bstep (se 2 (by rfl) ⟨19731336, by rfl⟩ : syracuseStep 52616897 = 39462673) B39462673
theorem B80051935 : Blo 1800101 80051935 := bstep (se 1 (by rfl) ⟨60038951, by rfl⟩ : syracuseStep 80051935 = 120077903) B120077903
theorem B55467773 : Blo 1800101 55467773 := bstep (se 3 (by rfl) ⟨10400207, by rfl⟩ : syracuseStep 55467773 = 20800415) B20800415
theorem B2883611 : Blo 1800101 2883611 := bstep (se 1 (by rfl) ⟨2162708, by rfl⟩ : syracuseStep 2883611 = 4325417) B4325417
theorem B8012255 : Blo 1800101 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B4325879 : Blo 1800101 4325879 := bstep (se 1 (by rfl) ⟨3244409, by rfl⟩ : syracuseStep 4325879 = 6488819) B6488819
theorem B11534957 : Blo 1800101 11534957 := bstep (se 3 (by rfl) ⟨2162804, by rfl⟩ : syracuseStep 11534957 = 4325609) B4325609
theorem B9118331 : Blo 1800101 9118331 := bstep (se 1 (by rfl) ⟨6838748, by rfl⟩ : syracuseStep 9118331 = 13677497) B13677497
theorem B6161159 : Blo 1800101 6161159 := bstep (se 1 (by rfl) ⟨4620869, by rfl⟩ : syracuseStep 6161159 = 9241739) B9241739
theorem B14803735 : Blo 1800101 14803735 := bstep (se 1 (by rfl) ⟨11102801, by rfl⟩ : syracuseStep 14803735 = 22205603) B22205603
theorem B33293693 : Blo 1800101 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B2278783 : Blo 1800101 2278783 := bstep (se 1 (by rfl) ⟨1709087, by rfl⟩ : syracuseStep 2278783 = 3418175) B3418175
theorem B6080183 : Blo 1800101 6080183 := bstep (se 1 (by rfl) ⟨4560137, by rfl⟩ : syracuseStep 6080183 = 9120275) B9120275
theorem B4556513 : Blo 1800101 4556513 := bstep (se 2 (by rfl) ⟨1708692, by rfl⟩ : syracuseStep 4556513 = 3417385) B3417385
theorem B106735913 : Blo 1800101 106735913 := bstep (se 2 (by rfl) ⟨40025967, by rfl⟩ : syracuseStep 106735913 = 80051935) B80051935
theorem B6932951 : Blo 1800101 6932951 := bstep (se 1 (by rfl) ⟨5199713, by rfl⟩ : syracuseStep 6932951 = 10399427) B10399427
theorem B17549855 : Blo 1800101 17549855 := bstep (se 1 (by rfl) ⟨13162391, by rfl⟩ : syracuseStep 17549855 = 26324783) B26324783
theorem B133229771 : Blo 1800101 133229771 := bstep (se 1 (by rfl) ⟨99922328, by rfl⟩ : syracuseStep 133229771 = 199844657) B199844657
theorem B8654369 : Blo 1800101 8654369 := bstep (se 2 (by rfl) ⟨3245388, by rfl⟩ : syracuseStep 8654369 = 6490777) B6490777
theorem B4558457 : Blo 1800101 4558457 := bstep (se 2 (by rfl) ⟨1709421, by rfl⟩ : syracuseStep 4558457 = 3418843) B3418843
theorem B83144569 : Blo 1800101 83144569 := bstep (se 2 (by rfl) ⟨31179213, by rfl⟩ : syracuseStep 83144569 = 62358427) B62358427
theorem B4050899 : Blo 1800101 4050899 := bstep (se 1 (by rfl) ⟨3038174, by rfl⟩ : syracuseStep 4050899 = 6076349) B6076349
theorem B12980519 : Blo 1800101 12980519 := bstep (se 1 (by rfl) ⟨9735389, by rfl⟩ : syracuseStep 12980519 = 19470779) B19470779
theorem B46150073 : Blo 1800101 46150073 := bstep (se 2 (by rfl) ⟨17306277, by rfl⟩ : syracuseStep 46150073 = 34612555) B34612555
theorem B4052051 : Blo 1800101 4052051 := bstep (se 1 (by rfl) ⟨3039038, by rfl⟩ : syracuseStep 4052051 = 6078077) B6078077
theorem B5477689 : Blo 1800101 5477689 := bstep (se 2 (by rfl) ⟨2054133, by rfl⟩ : syracuseStep 5477689 = 4108267) B4108267
theorem B3847753 : Blo 1800101 3847753 := bstep (se 2 (by rfl) ⟨1442907, by rfl⟩ : syracuseStep 3847753 = 2885815) B2885815
theorem B2700905 : Blo 1800101 2700905 := bstep (se 2 (by rfl) ⟨1012839, by rfl⟩ : syracuseStep 2700905 = 2025679) B2025679
theorem B4052879 : Blo 1800101 4052879 := bstep (se 1 (by rfl) ⟨3039659, by rfl⟩ : syracuseStep 4052879 = 6079319) B6079319
theorem B2054143 : Blo 1800101 2054143 := bstep (se 1 (by rfl) ⟨1540607, by rfl⟩ : syracuseStep 2054143 = 3081215) B3081215
theorem B4053023 : Blo 1800101 4053023 := bstep (se 1 (by rfl) ⟨3039767, by rfl⟩ : syracuseStep 4053023 = 6079535) B6079535
theorem B1800255 : Blo 1800101 1800255 := bstep (se 1 (by rfl) ⟨1350191, by rfl⟩ : syracuseStep 1800255 = 2700383) B2700383
theorem B1800319 : Blo 1800101 1800319 := bstep (se 1 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 1800319 = 2700479) B2700479
theorem B2701487 : Blo 1800101 2701487 := bstep (se 1 (by rfl) ⟨2026115, by rfl⟩ : syracuseStep 2701487 = 4052231) B4052231
theorem B1800475 : Blo 1800101 1800475 := bstep (se 1 (by rfl) ⟨1350356, by rfl⟩ : syracuseStep 1800475 = 2700713) B2700713
theorem B1800511 : Blo 1800101 1800511 := bstep (se 1 (by rfl) ⟨1350383, by rfl⟩ : syracuseStep 1800511 = 2700767) B2700767
theorem B37476683 : Blo 1800101 37476683 := bstep (se 1 (by rfl) ⟨28107512, by rfl⟩ : syracuseStep 37476683 = 56215025) B56215025
theorem B1800575 : Blo 1800101 1800575 := bstep (se 1 (by rfl) ⟨1350431, by rfl⟩ : syracuseStep 1800575 = 2700863) B2700863
theorem B1800751 : Blo 1800101 1800751 := bstep (se 1 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 1800751 = 2701127) B2701127
theorem B1800859 : Blo 1800101 1800859 := bstep (se 1 (by rfl) ⟨1350644, by rfl⟩ : syracuseStep 1800859 = 2701289) B2701289
theorem B1800895 : Blo 1800101 1800895 := bstep (se 1 (by rfl) ⟨1350671, by rfl⟩ : syracuseStep 1800895 = 2701343) B2701343
theorem B2702111 : Blo 1800101 2702111 := bstep (se 1 (by rfl) ⟨2026583, by rfl⟩ : syracuseStep 2702111 = 4053167) B4053167
theorem B10255207 : Blo 1800101 10255207 := bstep (se 1 (by rfl) ⟨7691405, by rfl⟩ : syracuseStep 10255207 = 15382811) B15382811
theorem B1801063 : Blo 1800101 1801063 := bstep (se 1 (by rfl) ⟨1350797, by rfl⟩ : syracuseStep 1801063 = 2701595) B2701595
theorem B1801087 : Blo 1800101 1801087 := bstep (se 1 (by rfl) ⟨1350815, by rfl⟩ : syracuseStep 1801087 = 2701631) B2701631
theorem B3079451 : Blo 1800101 3079451 := bstep (se 1 (by rfl) ⟨2309588, by rfl⟩ : syracuseStep 3079451 = 4619177) B4619177
theorem B20798747 : Blo 1800101 20798747 := bstep (se 1 (by rfl) ⟨15599060, by rfl⟩ : syracuseStep 20798747 = 31198121) B31198121
theorem B7691611 : Blo 1800101 7691611 := bstep (se 1 (by rfl) ⟨5768708, by rfl⟩ : syracuseStep 7691611 = 11537417) B11537417
theorem B35077931 : Blo 1800101 35077931 := bstep (se 1 (by rfl) ⟨26308448, by rfl⟩ : syracuseStep 35077931 = 52616897) B52616897
theorem B36978515 : Blo 1800101 36978515 := bstep (se 1 (by rfl) ⟨27733886, by rfl⟩ : syracuseStep 36978515 = 55467773) B55467773
theorem B2883919 : Blo 1800101 2883919 := bstep (se 1 (by rfl) ⟨2162939, by rfl⟩ : syracuseStep 2883919 = 4325879) B4325879
theorem B20521349 : Blo 1800101 20521349 := bstep (se 4 (by rfl) ⟨1923876, by rfl⟩ : syracuseStep 20521349 = 3847753) B3847753
theorem B6078887 : Blo 1800101 6078887 := bstep (se 1 (by rfl) ⟨4559165, by rfl⟩ : syracuseStep 6078887 = 9118331) B9118331
theorem B13673609 : Blo 1800101 13673609 := bstep (se 2 (by rfl) ⟨5127603, by rfl⟩ : syracuseStep 13673609 = 10255207) B10255207
theorem B21366013 : Blo 1800101 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B23078317 : Blo 1800101 23078317 := bstep (se 3 (by rfl) ⟨4327184, by rfl⟩ : syracuseStep 23078317 = 8654369) B8654369
theorem B71157275 : Blo 1800101 71157275 := bstep (se 1 (by rfl) ⟨53367956, by rfl⟩ : syracuseStep 71157275 = 106735913) B106735913
theorem B29214341 : Blo 1800101 29214341 := bstep (se 4 (by rfl) ⟨2738844, by rfl⟩ : syracuseStep 29214341 = 5477689) B5477689
theorem B4621967 : Blo 1800101 4621967 := bstep (se 1 (by rfl) ⟨3466475, by rfl⟩ : syracuseStep 4621967 = 6932951) B6932951
theorem B11699903 : Blo 1800101 11699903 := bstep (se 1 (by rfl) ⟨8774927, by rfl⟩ : syracuseStep 11699903 = 17549855) B17549855
theorem B88819847 : Blo 1800101 88819847 := bstep (se 1 (by rfl) ⟨66614885, by rfl⟩ : syracuseStep 88819847 = 133229771) B133229771
theorem B24652343 : Blo 1800101 24652343 := bstep (se 1 (by rfl) ⟨18489257, by rfl⟩ : syracuseStep 24652343 = 36978515) B36978515
theorem B2738857 : Blo 1800101 2738857 := bstep (se 2 (by rfl) ⟨1027071, by rfl⟩ : syracuseStep 2738857 = 2054143) B2054143
theorem B8653679 : Blo 1800101 8653679 := bstep (se 1 (by rfl) ⟨6490259, by rfl⟩ : syracuseStep 8653679 = 12980519) B12980519
theorem B4107439 : Blo 1800101 4107439 := bstep (se 1 (by rfl) ⟨3080579, by rfl⟩ : syracuseStep 4107439 = 6161159) B6161159
theorem B22195795 : Blo 1800101 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B19738313 : Blo 1800101 19738313 := bstep (se 2 (by rfl) ⟨7401867, by rfl⟩ : syracuseStep 19738313 = 14803735) B14803735
theorem B2052967 : Blo 1800101 2052967 := bstep (se 1 (by rfl) ⟨1539725, by rfl⟩ : syracuseStep 2052967 = 3079451) B3079451
theorem B13865831 : Blo 1800101 13865831 := bstep (se 1 (by rfl) ⟨10399373, by rfl⟩ : syracuseStep 13865831 = 20798747) B20798747
theorem B110859425 : Blo 1800101 110859425 := bstep (se 2 (by rfl) ⟨41572284, by rfl⟩ : syracuseStep 110859425 = 83144569) B83144569
theorem B23385287 : Blo 1800101 23385287 := bstep (se 1 (by rfl) ⟨17538965, by rfl⟩ : syracuseStep 23385287 = 35077931) B35077931
theorem B2700599 : Blo 1800101 2700599 := bstep (se 1 (by rfl) ⟨2025449, by rfl⟩ : syracuseStep 2700599 = 4050899) B4050899
theorem B7689629 : Blo 1800101 7689629 := bstep (se 3 (by rfl) ⟨1441805, by rfl⟩ : syracuseStep 7689629 = 2883611) B2883611
theorem B30766715 : Blo 1800101 30766715 := bstep (se 1 (by rfl) ⟨23075036, by rfl⟩ : syracuseStep 30766715 = 46150073) B46150073
theorem B7689971 : Blo 1800101 7689971 := bstep (se 1 (by rfl) ⟨5767478, by rfl⟩ : syracuseStep 7689971 = 11534957) B11534957
theorem B2701367 : Blo 1800101 2701367 := bstep (se 1 (by rfl) ⟨2026025, by rfl⟩ : syracuseStep 2701367 = 4052051) B4052051
theorem B1800603 : Blo 1800101 1800603 := bstep (se 1 (by rfl) ⟨1350452, by rfl⟩ : syracuseStep 1800603 = 2700905) B2700905
theorem B4053455 : Blo 1800101 4053455 := bstep (se 1 (by rfl) ⟨3040091, by rfl⟩ : syracuseStep 4053455 = 6080183) B6080183
theorem B3037675 : Blo 1800101 3037675 := bstep (se 1 (by rfl) ⟨2278256, by rfl⟩ : syracuseStep 3037675 = 4556513) B4556513
theorem B2701919 : Blo 1800101 2701919 := bstep (se 1 (by rfl) ⟨2026439, by rfl⟩ : syracuseStep 2701919 = 4052879) B4052879
theorem B2702015 : Blo 1800101 2702015 := bstep (se 1 (by rfl) ⟨2026511, by rfl⟩ : syracuseStep 2702015 = 4053023) B4053023
theorem B1800991 : Blo 1800101 1800991 := bstep (se 1 (by rfl) ⟨1350743, by rfl⟩ : syracuseStep 1800991 = 2701487) B2701487
theorem B24984455 : Blo 1800101 24984455 := bstep (se 1 (by rfl) ⟨18738341, by rfl⟩ : syracuseStep 24984455 = 37476683) B37476683
theorem B10255481 : Blo 1800101 10255481 := bstep (se 2 (by rfl) ⟨3845805, by rfl⟩ : syracuseStep 10255481 = 7691611) B7691611
theorem B3038377 : Blo 1800101 3038377 := bstep (se 2 (by rfl) ⟨1139391, by rfl⟩ : syracuseStep 3038377 = 2278783) B2278783
theorem B1801407 : Blo 1800101 1801407 := bstep (se 1 (by rfl) ⟨1351055, by rfl⟩ : syracuseStep 1801407 = 2702111) B2702111
theorem B3038971 : Blo 1800101 3038971 := bstep (se 1 (by rfl) ⟨2279228, by rfl⟩ : syracuseStep 3038971 = 4558457) B4558457
theorem B13680899 : Blo 1800101 13680899 := bstep (se 1 (by rfl) ⟨10260674, by rfl⟩ : syracuseStep 13680899 = 20521349) B20521349
theorem B3081311 : Blo 1800101 3081311 := bstep (se 1 (by rfl) ⟨2310983, by rfl⟩ : syracuseStep 3081311 = 4621967) B4621967
theorem B2737289 : Blo 1800101 2737289 := bstep (se 2 (by rfl) ⟨1026483, by rfl⟩ : syracuseStep 2737289 = 2052967) B2052967
theorem B59213231 : Blo 1800101 59213231 := bstep (se 1 (by rfl) ⟨44409923, by rfl⟩ : syracuseStep 59213231 = 88819847) B88819847
theorem B16434895 : Blo 1800101 16434895 := bstep (se 1 (by rfl) ⟨12326171, by rfl⟩ : syracuseStep 16434895 = 24652343) B24652343
theorem B30771089 : Blo 1800101 30771089 := bstep (se 2 (by rfl) ⟨11539158, by rfl⟩ : syracuseStep 30771089 = 23078317) B23078317
theorem B5769119 : Blo 1800101 5769119 := bstep (se 1 (by rfl) ⟨4326839, by rfl⟩ : syracuseStep 5769119 = 8653679) B8653679
theorem B13158875 : Blo 1800101 13158875 := bstep (se 1 (by rfl) ⟨9869156, by rfl⟩ : syracuseStep 13158875 = 19738313) B19738313
theorem B3845225 : Blo 1800101 3845225 := bstep (se 2 (by rfl) ⟨1441959, by rfl⟩ : syracuseStep 3845225 = 2883919) B2883919
theorem B62360765 : Blo 1800101 62360765 := bstep (se 3 (by rfl) ⟨11692643, by rfl⟩ : syracuseStep 62360765 = 23385287) B23385287
theorem B9243887 : Blo 1800101 9243887 := bstep (se 1 (by rfl) ⟨6932915, by rfl⟩ : syracuseStep 9243887 = 13865831) B13865831
theorem B4050233 : Blo 1800101 4050233 := bstep (se 2 (by rfl) ⟨1518837, by rfl⟩ : syracuseStep 4050233 = 3037675) B3037675
theorem B19476227 : Blo 1800101 19476227 := bstep (se 1 (by rfl) ⟨14607170, by rfl⟩ : syracuseStep 19476227 = 29214341) B29214341
theorem B4051169 : Blo 1800101 4051169 := bstep (se 2 (by rfl) ⟨1519188, by rfl⟩ : syracuseStep 4051169 = 3038377) B3038377
theorem B5476585 : Blo 1800101 5476585 := bstep (se 2 (by rfl) ⟨2053719, by rfl⟩ : syracuseStep 5476585 = 4107439) B4107439
theorem B28488017 : Blo 1800101 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B31199741 : Blo 1800101 31199741 := bstep (se 3 (by rfl) ⟨5849951, by rfl⟩ : syracuseStep 31199741 = 11699903) B11699903
theorem B6836987 : Blo 1800101 6836987 := bstep (se 1 (by rfl) ⟨5127740, by rfl⟩ : syracuseStep 6836987 = 10255481) B10255481
theorem B29594393 : Blo 1800101 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B4051961 : Blo 1800101 4051961 := bstep (se 2 (by rfl) ⟨1519485, by rfl⟩ : syracuseStep 4051961 = 3038971) B3038971
theorem B4052591 : Blo 1800101 4052591 := bstep (se 1 (by rfl) ⟨3039443, by rfl⟩ : syracuseStep 4052591 = 6078887) B6078887
theorem B9115739 : Blo 1800101 9115739 := bstep (se 1 (by rfl) ⟨6836804, by rfl⟩ : syracuseStep 9115739 = 13673609) B13673609
theorem B73906283 : Blo 1800101 73906283 := bstep (se 1 (by rfl) ⟨55429712, by rfl⟩ : syracuseStep 73906283 = 110859425) B110859425
theorem B1800399 : Blo 1800101 1800399 := bstep (se 1 (by rfl) ⟨1350299, by rfl⟩ : syracuseStep 1800399 = 2700599) B2700599
theorem B3651809 : Blo 1800101 3651809 := bstep (se 2 (by rfl) ⟨1369428, by rfl⟩ : syracuseStep 3651809 = 2738857) B2738857
theorem B5126419 : Blo 1800101 5126419 := bstep (se 1 (by rfl) ⟨3844814, by rfl⟩ : syracuseStep 5126419 = 7689629) B7689629
theorem B47438183 : Blo 1800101 47438183 := bstep (se 1 (by rfl) ⟨35578637, by rfl⟩ : syracuseStep 47438183 = 71157275) B71157275
theorem B20511143 : Blo 1800101 20511143 := bstep (se 1 (by rfl) ⟨15383357, by rfl⟩ : syracuseStep 20511143 = 30766715) B30766715
theorem B5126647 : Blo 1800101 5126647 := bstep (se 1 (by rfl) ⟨3844985, by rfl⟩ : syracuseStep 5126647 = 7689971) B7689971
theorem B1800911 : Blo 1800101 1800911 := bstep (se 1 (by rfl) ⟨1350683, by rfl⟩ : syracuseStep 1800911 = 2701367) B2701367
theorem B2702303 : Blo 1800101 2702303 := bstep (se 1 (by rfl) ⟨2026727, by rfl⟩ : syracuseStep 2702303 = 4053455) B4053455
theorem B1801279 : Blo 1800101 1801279 := bstep (se 1 (by rfl) ⟨1350959, by rfl⟩ : syracuseStep 1801279 = 2701919) B2701919
theorem B1801343 : Blo 1800101 1801343 := bstep (se 1 (by rfl) ⟨1351007, by rfl⟩ : syracuseStep 1801343 = 2702015) B2702015
theorem B66625213 : Blo 1800101 66625213 := bstep (se 3 (by rfl) ⟨12492227, by rfl⟩ : syracuseStep 66625213 = 24984455) B24984455
theorem B20799827 : Blo 1800101 20799827 := bstep (se 1 (by rfl) ⟨15599870, by rfl⟩ : syracuseStep 20799827 = 31199741) B31199741
theorem B24650365 : Blo 1800101 24650365 := bstep (se 3 (by rfl) ⟨4621943, by rfl⟩ : syracuseStep 24650365 = 9243887) B9243887
theorem B126501821 : Blo 1800101 126501821 := bstep (se 3 (by rfl) ⟨23719091, by rfl⟩ : syracuseStep 126501821 = 47438183) B47438183
theorem B20514059 : Blo 1800101 20514059 := bstep (se 1 (by rfl) ⟨15385544, by rfl⟩ : syracuseStep 20514059 = 30771089) B30771089
theorem B13674095 : Blo 1800101 13674095 := bstep (se 1 (by rfl) ⟨10255571, by rfl⟩ : syracuseStep 13674095 = 20511143) B20511143
theorem B9120599 : Blo 1800101 9120599 := bstep (se 1 (by rfl) ⟨6840449, by rfl⟩ : syracuseStep 9120599 = 13680899) B13680899
theorem B18992011 : Blo 1800101 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B7302113 : Blo 1800101 7302113 := bstep (se 2 (by rfl) ⟨2738292, by rfl⟩ : syracuseStep 7302113 = 5476585) B5476585
theorem B6835225 : Blo 1800101 6835225 := bstep (se 2 (by rfl) ⟨2563209, by rfl⟩ : syracuseStep 6835225 = 5126419) B5126419
theorem B4557991 : Blo 1800101 4557991 := bstep (se 1 (by rfl) ⟨3418493, by rfl⟩ : syracuseStep 4557991 = 6836987) B6836987
theorem B19729595 : Blo 1800101 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B6835529 : Blo 1800101 6835529 := bstep (se 2 (by rfl) ⟨2563323, by rfl⟩ : syracuseStep 6835529 = 5126647) B5126647
theorem B3846079 : Blo 1800101 3846079 := bstep (se 1 (by rfl) ⟨2884559, by rfl⟩ : syracuseStep 3846079 = 5769119) B5769119
theorem B49270855 : Blo 1800101 49270855 := bstep (se 1 (by rfl) ⟨36953141, by rfl⟩ : syracuseStep 49270855 = 73906283) B73906283
theorem B2700155 : Blo 1800101 2700155 := bstep (se 1 (by rfl) ⟨2025116, by rfl⟩ : syracuseStep 2700155 = 4050233) B4050233
theorem B2700779 : Blo 1800101 2700779 := bstep (se 1 (by rfl) ⟨2025584, by rfl⟩ : syracuseStep 2700779 = 4051169) B4051169
theorem B9738157 : Blo 1800101 9738157 := bstep (se 3 (by rfl) ⟨1825904, by rfl⟩ : syracuseStep 9738157 = 3651809) B3651809
theorem B2701307 : Blo 1800101 2701307 := bstep (se 1 (by rfl) ⟨2025980, by rfl⟩ : syracuseStep 2701307 = 4051961) B4051961
theorem B2054207 : Blo 1800101 2054207 := bstep (se 1 (by rfl) ⟨1540655, by rfl⟩ : syracuseStep 2054207 = 3081311) B3081311
theorem B1824859 : Blo 1800101 1824859 := bstep (se 1 (by rfl) ⟨1368644, by rfl⟩ : syracuseStep 1824859 = 2737289) B2737289
theorem B39475487 : Blo 1800101 39475487 := bstep (se 1 (by rfl) ⟨29606615, by rfl⟩ : syracuseStep 39475487 = 59213231) B59213231
theorem B2701727 : Blo 1800101 2701727 := bstep (se 1 (by rfl) ⟨2026295, by rfl⟩ : syracuseStep 2701727 = 4052591) B4052591
theorem B6077159 : Blo 1800101 6077159 := bstep (se 1 (by rfl) ⟨4557869, by rfl⟩ : syracuseStep 6077159 = 9115739) B9115739
theorem B8772583 : Blo 1800101 8772583 := bstep (se 1 (by rfl) ⟨6579437, by rfl⟩ : syracuseStep 8772583 = 13158875) B13158875
theorem B1801535 : Blo 1800101 1801535 := bstep (se 1 (by rfl) ⟨1351151, by rfl⟩ : syracuseStep 1801535 = 2702303) B2702303
theorem B2563483 : Blo 1800101 2563483 := bstep (se 1 (by rfl) ⟨1922612, by rfl⟩ : syracuseStep 2563483 = 3845225) B3845225
theorem B41573843 : Blo 1800101 41573843 := bstep (se 1 (by rfl) ⟨31180382, by rfl⟩ : syracuseStep 41573843 = 62360765) B62360765
theorem B88833617 : Blo 1800101 88833617 := bstep (se 2 (by rfl) ⟨33312606, by rfl⟩ : syracuseStep 88833617 = 66625213) B66625213
theorem B21913193 : Blo 1800101 21913193 := bstep (se 2 (by rfl) ⟨8217447, by rfl⟩ : syracuseStep 21913193 = 16434895) B16434895
theorem B12984151 : Blo 1800101 12984151 := bstep (se 1 (by rfl) ⟨9738113, by rfl⟩ : syracuseStep 12984151 = 19476227) B19476227
theorem B2433145 : Blo 1800101 2433145 := bstep (se 2 (by rfl) ⟨912429, by rfl⟩ : syracuseStep 2433145 = 1824859) B1824859
theorem B32867153 : Blo 1800101 32867153 := bstep (se 2 (by rfl) ⟨12325182, by rfl⟩ : syracuseStep 32867153 = 24650365) B24650365
theorem B25322681 : Blo 1800101 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B3417977 : Blo 1800101 3417977 := bstep (se 2 (by rfl) ⟨1281741, by rfl⟩ : syracuseStep 3417977 = 2563483) B2563483
theorem B6080399 : Blo 1800101 6080399 := bstep (se 1 (by rfl) ⟨4560299, by rfl⟩ : syracuseStep 6080399 = 9120599) B9120599
theorem B4868075 : Blo 1800101 4868075 := bstep (se 1 (by rfl) ⟨3651056, by rfl⟩ : syracuseStep 4868075 = 7302113) B7302113
theorem B4557019 : Blo 1800101 4557019 := bstep (se 1 (by rfl) ⟨3417764, by rfl⟩ : syracuseStep 4557019 = 6835529) B6835529
theorem B27715895 : Blo 1800101 27715895 := bstep (se 1 (by rfl) ⟨20786921, by rfl⟩ : syracuseStep 27715895 = 41573843) B41573843
theorem B59222411 : Blo 1800101 59222411 := bstep (se 1 (by rfl) ⟨44416808, by rfl⟩ : syracuseStep 59222411 = 88833617) B88833617
theorem B14608795 : Blo 1800101 14608795 := bstep (se 1 (by rfl) ⟨10956596, by rfl⟩ : syracuseStep 14608795 = 21913193) B21913193
theorem B17312201 : Blo 1800101 17312201 := bstep (se 2 (by rfl) ⟨6492075, by rfl⟩ : syracuseStep 17312201 = 12984151) B12984151
theorem B65694473 : Blo 1800101 65694473 := bstep (se 2 (by rfl) ⟨24635427, by rfl⟩ : syracuseStep 65694473 = 49270855) B49270855
theorem B13676039 : Blo 1800101 13676039 := bstep (se 1 (by rfl) ⟨10257029, by rfl⟩ : syracuseStep 13676039 = 20514059) B20514059
theorem B9113633 : Blo 1800101 9113633 := bstep (se 2 (by rfl) ⟨3417612, by rfl⟩ : syracuseStep 9113633 = 6835225) B6835225
theorem B26316991 : Blo 1800101 26316991 := bstep (se 1 (by rfl) ⟨19737743, by rfl⟩ : syracuseStep 26316991 = 39475487) B39475487
theorem B4051439 : Blo 1800101 4051439 := bstep (se 1 (by rfl) ⟨3038579, by rfl⟩ : syracuseStep 4051439 = 6077159) B6077159
theorem B13153063 : Blo 1800101 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B5477885 : Blo 1800101 5477885 := bstep (se 3 (by rfl) ⟨1027103, by rfl⟩ : syracuseStep 5477885 = 2054207) B2054207
theorem B13866551 : Blo 1800101 13866551 := bstep (se 1 (by rfl) ⟨10399913, by rfl⟩ : syracuseStep 13866551 = 20799827) B20799827
theorem B1800103 : Blo 1800101 1800103 := bstep (se 1 (by rfl) ⟨1350077, by rfl⟩ : syracuseStep 1800103 = 2700155) B2700155
theorem B84334547 : Blo 1800101 84334547 := bstep (se 1 (by rfl) ⟨63250910, by rfl⟩ : syracuseStep 84334547 = 126501821) B126501821
theorem B1800519 : Blo 1800101 1800519 := bstep (se 1 (by rfl) ⟨1350389, by rfl⟩ : syracuseStep 1800519 = 2700779) B2700779
theorem B9116063 : Blo 1800101 9116063 := bstep (se 1 (by rfl) ⟨6837047, by rfl⟩ : syracuseStep 9116063 = 13674095) B13674095
theorem B11696777 : Blo 1800101 11696777 := bstep (se 2 (by rfl) ⟨4386291, by rfl⟩ : syracuseStep 11696777 = 8772583) B8772583
theorem B1800871 : Blo 1800101 1800871 := bstep (se 1 (by rfl) ⟨1350653, by rfl⟩ : syracuseStep 1800871 = 2701307) B2701307
theorem B6077321 : Blo 1800101 6077321 := bstep (se 2 (by rfl) ⟨2278995, by rfl⟩ : syracuseStep 6077321 = 4557991) B4557991
theorem B1801151 : Blo 1800101 1801151 := bstep (se 1 (by rfl) ⟨1350863, by rfl⟩ : syracuseStep 1801151 = 2701727) B2701727
theorem B12984209 : Blo 1800101 12984209 := bstep (se 2 (by rfl) ⟨4869078, by rfl⟩ : syracuseStep 12984209 = 9738157) B9738157
theorem B5128105 : Blo 1800101 5128105 := bstep (se 2 (by rfl) ⟨1923039, by rfl⟩ : syracuseStep 5128105 = 3846079) B3846079
theorem B3244193 : Blo 1800101 3244193 := bstep (se 2 (by rfl) ⟨1216572, by rfl⟩ : syracuseStep 3244193 = 2433145) B2433145
theorem B56223031 : Blo 1800101 56223031 := bstep (se 1 (by rfl) ⟨42167273, by rfl⟩ : syracuseStep 56223031 = 84334547) B84334547
theorem B3245383 : Blo 1800101 3245383 := bstep (se 1 (by rfl) ⟨2434037, by rfl⟩ : syracuseStep 3245383 = 4868075) B4868075
theorem B43796315 : Blo 1800101 43796315 := bstep (se 1 (by rfl) ⟨32847236, by rfl⟩ : syracuseStep 43796315 = 65694473) B65694473
theorem B35089321 : Blo 1800101 35089321 := bstep (se 2 (by rfl) ⟨13158495, by rfl⟩ : syracuseStep 35089321 = 26316991) B26316991
theorem B9244367 : Blo 1800101 9244367 := bstep (se 1 (by rfl) ⟨6933275, by rfl⟩ : syracuseStep 9244367 = 13866551) B13866551
theorem B18477263 : Blo 1800101 18477263 := bstep (se 1 (by rfl) ⟨13857947, by rfl⟩ : syracuseStep 18477263 = 27715895) B27715895
theorem B39481607 : Blo 1800101 39481607 := bstep (se 1 (by rfl) ⟨29611205, by rfl⟩ : syracuseStep 39481607 = 59222411) B59222411
theorem B4051547 : Blo 1800101 4051547 := bstep (se 1 (by rfl) ⟨3038660, by rfl⟩ : syracuseStep 4051547 = 6077321) B6077321
theorem B9114605 : Blo 1800101 9114605 := bstep (se 3 (by rfl) ⟨1708988, by rfl⟩ : syracuseStep 9114605 = 3417977) B3417977
theorem B6837473 : Blo 1800101 6837473 := bstep (se 2 (by rfl) ⟨2564052, by rfl⟩ : syracuseStep 6837473 = 5128105) B5128105
theorem B8656139 : Blo 1800101 8656139 := bstep (se 1 (by rfl) ⟨6492104, by rfl⟩ : syracuseStep 8656139 = 12984209) B12984209
theorem B6075755 : Blo 1800101 6075755 := bstep (se 1 (by rfl) ⟨4556816, by rfl⟩ : syracuseStep 6075755 = 9113633) B9113633
theorem B6076025 : Blo 1800101 6076025 := bstep (se 2 (by rfl) ⟨2278509, by rfl⟩ : syracuseStep 6076025 = 4557019) B4557019
theorem B2700959 : Blo 1800101 2700959 := bstep (se 1 (by rfl) ⟨2025719, by rfl⟩ : syracuseStep 2700959 = 4051439) B4051439
theorem B19478393 : Blo 1800101 19478393 := bstep (se 2 (by rfl) ⟨7304397, by rfl⟩ : syracuseStep 19478393 = 14608795) B14608795
theorem B21911435 : Blo 1800101 21911435 := bstep (se 1 (by rfl) ⟨16433576, by rfl⟩ : syracuseStep 21911435 = 32867153) B32867153
theorem B16881787 : Blo 1800101 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B3651923 : Blo 1800101 3651923 := bstep (se 1 (by rfl) ⟨2738942, by rfl⟩ : syracuseStep 3651923 = 5477885) B5477885
theorem B17537417 : Blo 1800101 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B4053599 : Blo 1800101 4053599 := bstep (se 1 (by rfl) ⟨3040199, by rfl⟩ : syracuseStep 4053599 = 6080399) B6080399
theorem B6077375 : Blo 1800101 6077375 := bstep (se 1 (by rfl) ⟨4558031, by rfl⟩ : syracuseStep 6077375 = 9116063) B9116063
theorem B11541467 : Blo 1800101 11541467 := bstep (se 1 (by rfl) ⟨8656100, by rfl⟩ : syracuseStep 11541467 = 17312201) B17312201
theorem B7797851 : Blo 1800101 7797851 := bstep (se 1 (by rfl) ⟨5848388, by rfl⟩ : syracuseStep 7797851 = 11696777) B11696777
theorem B9117359 : Blo 1800101 9117359 := bstep (se 1 (by rfl) ⟨6838019, by rfl⟩ : syracuseStep 9117359 = 13676039) B13676039
theorem B2162795 : Blo 1800101 2162795 := bstep (se 1 (by rfl) ⟨1622096, by rfl⟩ : syracuseStep 2162795 = 3244193) B3244193
theorem B105284285 : Blo 1800101 105284285 := bstep (se 3 (by rfl) ⟨19740803, by rfl⟩ : syracuseStep 105284285 = 39481607) B39481607
theorem B46785761 : Blo 1800101 46785761 := bstep (se 2 (by rfl) ⟨17544660, by rfl⟩ : syracuseStep 46785761 = 35089321) B35089321
theorem B29197543 : Blo 1800101 29197543 := bstep (se 1 (by rfl) ⟨21898157, by rfl⟩ : syracuseStep 29197543 = 43796315) B43796315
theorem B12985595 : Blo 1800101 12985595 := bstep (se 1 (by rfl) ⟨9739196, by rfl⟩ : syracuseStep 12985595 = 19478393) B19478393
theorem B14607623 : Blo 1800101 14607623 := bstep (se 1 (by rfl) ⟨10955717, by rfl⟩ : syracuseStep 14607623 = 21911435) B21911435
theorem B11691611 : Blo 1800101 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B4327177 : Blo 1800101 4327177 := bstep (se 2 (by rfl) ⟨1622691, by rfl⟩ : syracuseStep 4327177 = 3245383) B3245383
theorem B7694311 : Blo 1800101 7694311 := bstep (se 1 (by rfl) ⟨5770733, by rfl⟩ : syracuseStep 7694311 = 11541467) B11541467
theorem B6162911 : Blo 1800101 6162911 := bstep (se 1 (by rfl) ⟨4622183, by rfl⟩ : syracuseStep 6162911 = 9244367) B9244367
theorem B4558315 : Blo 1800101 4558315 := bstep (se 1 (by rfl) ⟨3418736, by rfl⟩ : syracuseStep 4558315 = 6837473) B6837473
theorem B5770759 : Blo 1800101 5770759 := bstep (se 1 (by rfl) ⟨4328069, by rfl⟩ : syracuseStep 5770759 = 8656139) B8656139
theorem B4050503 : Blo 1800101 4050503 := bstep (se 1 (by rfl) ⟨3037877, by rfl⟩ : syracuseStep 4050503 = 6075755) B6075755
theorem B83177077 : Blo 1800101 83177077 := bstep (se 5 (by rfl) ⟨3898925, by rfl⟩ : syracuseStep 83177077 = 7797851) B7797851
theorem B4050683 : Blo 1800101 4050683 := bstep (se 1 (by rfl) ⟨3038012, by rfl⟩ : syracuseStep 4050683 = 6076025) B6076025
theorem B4051583 : Blo 1800101 4051583 := bstep (se 1 (by rfl) ⟨3038687, by rfl⟩ : syracuseStep 4051583 = 6077375) B6077375
theorem B12318175 : Blo 1800101 12318175 := bstep (se 1 (by rfl) ⟨9238631, by rfl⟩ : syracuseStep 12318175 = 18477263) B18477263
theorem B22509049 : Blo 1800101 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B2701031 : Blo 1800101 2701031 := bstep (se 1 (by rfl) ⟨2025773, by rfl⟩ : syracuseStep 2701031 = 4051547) B4051547
theorem B6076403 : Blo 1800101 6076403 := bstep (se 1 (by rfl) ⟨4557302, by rfl⟩ : syracuseStep 6076403 = 9114605) B9114605
theorem B9738461 : Blo 1800101 9738461 := bstep (se 3 (by rfl) ⟨1825961, by rfl⟩ : syracuseStep 9738461 = 3651923) B3651923
theorem B1800639 : Blo 1800101 1800639 := bstep (se 1 (by rfl) ⟨1350479, by rfl⟩ : syracuseStep 1800639 = 2700959) B2700959
theorem B2702399 : Blo 1800101 2702399 := bstep (se 1 (by rfl) ⟨2026799, by rfl⟩ : syracuseStep 2702399 = 4053599) B4053599
theorem B74964041 : Blo 1800101 74964041 := bstep (se 2 (by rfl) ⟨28111515, by rfl⟩ : syracuseStep 74964041 = 56223031) B56223031
theorem B6078239 : Blo 1800101 6078239 := bstep (se 1 (by rfl) ⟨4558679, by rfl⟩ : syracuseStep 6078239 = 9117359) B9117359
theorem B5767453 : Blo 1800101 5767453 := bstep (se 3 (by rfl) ⟨1081397, by rfl⟩ : syracuseStep 5767453 = 2162795) B2162795
theorem B70189523 : Blo 1800101 70189523 := bstep (se 1 (by rfl) ⟨52642142, by rfl⟩ : syracuseStep 70189523 = 105284285) B105284285
theorem B38930057 : Blo 1800101 38930057 := bstep (se 2 (by rfl) ⟨14598771, by rfl⟩ : syracuseStep 38930057 = 29197543) B29197543
theorem B7694345 : Blo 1800101 7694345 := bstep (se 2 (by rfl) ⟨2885379, by rfl⟩ : syracuseStep 7694345 = 5770759) B5770759
theorem B5769569 : Blo 1800101 5769569 := bstep (se 2 (by rfl) ⟨2163588, by rfl⟩ : syracuseStep 5769569 = 4327177) B4327177
theorem B10259081 : Blo 1800101 10259081 := bstep (se 2 (by rfl) ⟨3847155, by rfl⟩ : syracuseStep 10259081 = 7694311) B7694311
theorem B31190507 : Blo 1800101 31190507 := bstep (se 1 (by rfl) ⟨23392880, by rfl⟩ : syracuseStep 31190507 = 46785761) B46785761
theorem B7794407 : Blo 1800101 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B4050935 : Blo 1800101 4050935 := bstep (se 1 (by rfl) ⟨3038201, by rfl⟩ : syracuseStep 4050935 = 6076403) B6076403
theorem B6492307 : Blo 1800101 6492307 := bstep (se 1 (by rfl) ⟨4869230, by rfl⟩ : syracuseStep 6492307 = 9738461) B9738461
theorem B4108607 : Blo 1800101 4108607 := bstep (se 1 (by rfl) ⟨3081455, by rfl⟩ : syracuseStep 4108607 = 6162911) B6162911
theorem B30012065 : Blo 1800101 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B49976027 : Blo 1800101 49976027 := bstep (se 1 (by rfl) ⟨37482020, by rfl⟩ : syracuseStep 49976027 = 74964041) B74964041
theorem B2700335 : Blo 1800101 2700335 := bstep (se 1 (by rfl) ⟨2025251, by rfl⟩ : syracuseStep 2700335 = 4050503) B4050503
theorem B65696933 : Blo 1800101 65696933 := bstep (se 4 (by rfl) ⟨6159087, by rfl⟩ : syracuseStep 65696933 = 12318175) B12318175
theorem B2700455 : Blo 1800101 2700455 := bstep (se 1 (by rfl) ⟨2025341, by rfl⟩ : syracuseStep 2700455 = 4050683) B4050683
theorem B4052159 : Blo 1800101 4052159 := bstep (se 1 (by rfl) ⟨3039119, by rfl⟩ : syracuseStep 4052159 = 6078239) B6078239
theorem B2701055 : Blo 1800101 2701055 := bstep (se 1 (by rfl) ⟨2025791, by rfl⟩ : syracuseStep 2701055 = 4051583) B4051583
theorem B8657063 : Blo 1800101 8657063 := bstep (se 1 (by rfl) ⟨6492797, by rfl⟩ : syracuseStep 8657063 = 12985595) B12985595
theorem B9738415 : Blo 1800101 9738415 := bstep (se 1 (by rfl) ⟨7303811, by rfl⟩ : syracuseStep 9738415 = 14607623) B14607623
theorem B1800687 : Blo 1800101 1800687 := bstep (se 1 (by rfl) ⟨1350515, by rfl⟩ : syracuseStep 1800687 = 2701031) B2701031
theorem B6077753 : Blo 1800101 6077753 := bstep (se 2 (by rfl) ⟨2279157, by rfl⟩ : syracuseStep 6077753 = 4558315) B4558315
theorem B1801599 : Blo 1800101 1801599 := bstep (se 1 (by rfl) ⟨1351199, by rfl⟩ : syracuseStep 1801599 = 2702399) B2702399
theorem B110902769 : Blo 1800101 110902769 := bstep (se 2 (by rfl) ⟨41588538, by rfl⟩ : syracuseStep 110902769 = 83177077) B83177077
theorem B12984553 : Blo 1800101 12984553 := bstep (se 2 (by rfl) ⟨4869207, by rfl⟩ : syracuseStep 12984553 = 9738415) B9738415
theorem B46793015 : Blo 1800101 46793015 := bstep (se 1 (by rfl) ⟨35094761, by rfl⟩ : syracuseStep 46793015 = 70189523) B70189523
theorem B33317351 : Blo 1800101 33317351 := bstep (se 1 (by rfl) ⟨24988013, by rfl⟩ : syracuseStep 33317351 = 49976027) B49976027
theorem B25953371 : Blo 1800101 25953371 := bstep (se 1 (by rfl) ⟨19465028, by rfl⟩ : syracuseStep 25953371 = 38930057) B38930057
theorem B5129563 : Blo 1800101 5129563 := bstep (se 1 (by rfl) ⟨3847172, by rfl⟩ : syracuseStep 5129563 = 7694345) B7694345
theorem B20793671 : Blo 1800101 20793671 := bstep (se 1 (by rfl) ⟨15595253, by rfl⟩ : syracuseStep 20793671 = 31190507) B31190507
theorem B73935179 : Blo 1800101 73935179 := bstep (se 1 (by rfl) ⟨55451384, by rfl⟩ : syracuseStep 73935179 = 110902769) B110902769
theorem B5196271 : Blo 1800101 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B2739071 : Blo 1800101 2739071 := bstep (se 1 (by rfl) ⟨2054303, by rfl⟩ : syracuseStep 2739071 = 4108607) B4108607
theorem B20008043 : Blo 1800101 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B5771375 : Blo 1800101 5771375 := bstep (se 1 (by rfl) ⟨4328531, by rfl⟩ : syracuseStep 5771375 = 8657063) B8657063
theorem B3846379 : Blo 1800101 3846379 := bstep (se 1 (by rfl) ⟨2884784, by rfl⟩ : syracuseStep 3846379 = 5769569) B5769569
theorem B4051835 : Blo 1800101 4051835 := bstep (se 1 (by rfl) ⟨3038876, by rfl⟩ : syracuseStep 4051835 = 6077753) B6077753
theorem B2700623 : Blo 1800101 2700623 := bstep (se 1 (by rfl) ⟨2025467, by rfl⟩ : syracuseStep 2700623 = 4050935) B4050935
theorem B8656409 : Blo 1800101 8656409 := bstep (se 2 (by rfl) ⟨3246153, by rfl⟩ : syracuseStep 8656409 = 6492307) B6492307
theorem B7689937 : Blo 1800101 7689937 := bstep (se 2 (by rfl) ⟨2883726, by rfl⟩ : syracuseStep 7689937 = 5767453) B5767453
theorem B175191821 : Blo 1800101 175191821 := bstep (se 3 (by rfl) ⟨32848466, by rfl⟩ : syracuseStep 175191821 = 65696933) B65696933
theorem B1800223 : Blo 1800101 1800223 := bstep (se 1 (by rfl) ⟨1350167, by rfl⟩ : syracuseStep 1800223 = 2700335) B2700335
theorem B1800303 : Blo 1800101 1800303 := bstep (se 1 (by rfl) ⟨1350227, by rfl⟩ : syracuseStep 1800303 = 2700455) B2700455
theorem B2701439 : Blo 1800101 2701439 := bstep (se 1 (by rfl) ⟨2026079, by rfl⟩ : syracuseStep 2701439 = 4052159) B4052159
theorem B1800703 : Blo 1800101 1800703 := bstep (se 1 (by rfl) ⟨1350527, by rfl⟩ : syracuseStep 1800703 = 2701055) B2701055
theorem B6839387 : Blo 1800101 6839387 := bstep (se 1 (by rfl) ⟨5129540, by rfl⟩ : syracuseStep 6839387 = 10259081) B10259081
theorem B31195343 : Blo 1800101 31195343 := bstep (se 1 (by rfl) ⟨23396507, by rfl⟩ : syracuseStep 31195343 = 46793015) B46793015
theorem B5128505 : Blo 1800101 5128505 := bstep (se 2 (by rfl) ⟨1923189, by rfl⟩ : syracuseStep 5128505 = 3846379) B3846379
theorem B17302247 : Blo 1800101 17302247 := bstep (se 1 (by rfl) ⟨12976685, by rfl⟩ : syracuseStep 17302247 = 25953371) B25953371
theorem B116794547 : Blo 1800101 116794547 := bstep (se 1 (by rfl) ⟨87595910, by rfl⟩ : syracuseStep 116794547 = 175191821) B175191821
theorem B13862447 : Blo 1800101 13862447 := bstep (se 1 (by rfl) ⟨10396835, by rfl⟩ : syracuseStep 13862447 = 20793671) B20793671
theorem B13338695 : Blo 1800101 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B17312737 : Blo 1800101 17312737 := bstep (se 2 (by rfl) ⟨6492276, by rfl⟩ : syracuseStep 17312737 = 12984553) B12984553
theorem B22211567 : Blo 1800101 22211567 := bstep (se 1 (by rfl) ⟨16658675, by rfl⟩ : syracuseStep 22211567 = 33317351) B33317351
theorem B5770939 : Blo 1800101 5770939 := bstep (se 1 (by rfl) ⟨4328204, by rfl⟩ : syracuseStep 5770939 = 8656409) B8656409
theorem B4559591 : Blo 1800101 4559591 := bstep (se 1 (by rfl) ⟨3419693, by rfl⟩ : syracuseStep 4559591 = 6839387) B6839387
theorem B10253249 : Blo 1800101 10253249 := bstep (se 2 (by rfl) ⟨3844968, by rfl⟩ : syracuseStep 10253249 = 7689937) B7689937
theorem B3847583 : Blo 1800101 3847583 := bstep (se 1 (by rfl) ⟨2885687, by rfl⟩ : syracuseStep 3847583 = 5771375) B5771375
theorem B2701223 : Blo 1800101 2701223 := bstep (se 1 (by rfl) ⟨2025917, by rfl⟩ : syracuseStep 2701223 = 4051835) B4051835
theorem B6928361 : Blo 1800101 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B1800415 : Blo 1800101 1800415 := bstep (se 1 (by rfl) ⟨1350311, by rfl⟩ : syracuseStep 1800415 = 2700623) B2700623
theorem B1800959 : Blo 1800101 1800959 := bstep (se 1 (by rfl) ⟨1350719, by rfl⟩ : syracuseStep 1800959 = 2701439) B2701439
theorem B49290119 : Blo 1800101 49290119 := bstep (se 1 (by rfl) ⟨36967589, by rfl⟩ : syracuseStep 49290119 = 73935179) B73935179
theorem B6839417 : Blo 1800101 6839417 := bstep (se 2 (by rfl) ⟨2564781, by rfl⟩ : syracuseStep 6839417 = 5129563) B5129563
theorem B1826047 : Blo 1800101 1826047 := bstep (se 1 (by rfl) ⟨1369535, by rfl⟩ : syracuseStep 1826047 = 2739071) B2739071
theorem B11534831 : Blo 1800101 11534831 := bstep (se 1 (by rfl) ⟨8651123, by rfl⟩ : syracuseStep 11534831 = 17302247) B17302247
theorem B3039727 : Blo 1800101 3039727 := bstep (se 1 (by rfl) ⟨2279795, by rfl⟩ : syracuseStep 3039727 = 4559591) B4559591
theorem B2565055 : Blo 1800101 2565055 := bstep (se 1 (by rfl) ⟨1923791, by rfl⟩ : syracuseStep 2565055 = 3847583) B3847583
theorem B9241631 : Blo 1800101 9241631 := bstep (se 1 (by rfl) ⟨6931223, by rfl⟩ : syracuseStep 9241631 = 13862447) B13862447
theorem B32860079 : Blo 1800101 32860079 := bstep (se 1 (by rfl) ⟨24645059, by rfl⟩ : syracuseStep 32860079 = 49290119) B49290119
theorem B7694585 : Blo 1800101 7694585 := bstep (se 2 (by rfl) ⟨2885469, by rfl⟩ : syracuseStep 7694585 = 5770939) B5770939
theorem B3419003 : Blo 1800101 3419003 := bstep (se 1 (by rfl) ⟨2564252, by rfl⟩ : syracuseStep 3419003 = 5128505) B5128505
theorem B6835499 : Blo 1800101 6835499 := bstep (se 1 (by rfl) ⟨5126624, by rfl⟩ : syracuseStep 6835499 = 10253249) B10253249
theorem B8892463 : Blo 1800101 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B14807711 : Blo 1800101 14807711 := bstep (se 1 (by rfl) ⟨11105783, by rfl⟩ : syracuseStep 14807711 = 22211567) B22211567
theorem B4559611 : Blo 1800101 4559611 := bstep (se 1 (by rfl) ⟨3419708, by rfl⟩ : syracuseStep 4559611 = 6839417) B6839417
theorem B20796895 : Blo 1800101 20796895 := bstep (se 1 (by rfl) ⟨15597671, by rfl⟩ : syracuseStep 20796895 = 31195343) B31195343
theorem B77863031 : Blo 1800101 77863031 := bstep (se 1 (by rfl) ⟨58397273, by rfl⟩ : syracuseStep 77863031 = 116794547) B116794547
theorem B1800815 : Blo 1800101 1800815 := bstep (se 1 (by rfl) ⟨1350611, by rfl⟩ : syracuseStep 1800815 = 2701223) B2701223
theorem B23083649 : Blo 1800101 23083649 := bstep (se 2 (by rfl) ⟨8656368, by rfl⟩ : syracuseStep 23083649 = 17312737) B17312737
theorem B4618907 : Blo 1800101 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B9738917 : Blo 1800101 9738917 := bstep (se 4 (by rfl) ⟨913023, by rfl⟩ : syracuseStep 9738917 = 1826047) B1826047
theorem B9871807 : Blo 1800101 9871807 := bstep (se 1 (by rfl) ⟨7403855, by rfl⟩ : syracuseStep 9871807 = 14807711) B14807711
theorem B6161087 : Blo 1800101 6161087 := bstep (se 1 (by rfl) ⟨4620815, by rfl⟩ : syracuseStep 6161087 = 9241631) B9241631
theorem B6079481 : Blo 1800101 6079481 := bstep (se 2 (by rfl) ⟨2279805, by rfl⟩ : syracuseStep 6079481 = 4559611) B4559611
theorem B21906719 : Blo 1800101 21906719 := bstep (se 1 (by rfl) ⟨16430039, by rfl⟩ : syracuseStep 21906719 = 32860079) B32860079
theorem B5129723 : Blo 1800101 5129723 := bstep (se 1 (by rfl) ⟨3847292, by rfl⟩ : syracuseStep 5129723 = 7694585) B7694585
theorem B2279335 : Blo 1800101 2279335 := bstep (se 1 (by rfl) ⟨1709501, by rfl⟩ : syracuseStep 2279335 = 3419003) B3419003
theorem B4556999 : Blo 1800101 4556999 := bstep (se 1 (by rfl) ⟨3417749, by rfl⟩ : syracuseStep 4556999 = 6835499) B6835499
theorem B11856617 : Blo 1800101 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B3420073 : Blo 1800101 3420073 := bstep (se 2 (by rfl) ⟨1282527, by rfl⟩ : syracuseStep 3420073 = 2565055) B2565055
theorem B51908687 : Blo 1800101 51908687 := bstep (se 1 (by rfl) ⟨38931515, by rfl⟩ : syracuseStep 51908687 = 77863031) B77863031
theorem B15389099 : Blo 1800101 15389099 := bstep (se 1 (by rfl) ⟨11541824, by rfl⟩ : syracuseStep 15389099 = 23083649) B23083649
theorem B6492611 : Blo 1800101 6492611 := bstep (se 1 (by rfl) ⟨4869458, by rfl⟩ : syracuseStep 6492611 = 9738917) B9738917
theorem B110916773 : Blo 1800101 110916773 := bstep (se 4 (by rfl) ⟨10398447, by rfl⟩ : syracuseStep 110916773 = 20796895) B20796895
theorem B7689887 : Blo 1800101 7689887 := bstep (se 1 (by rfl) ⟨5767415, by rfl⟩ : syracuseStep 7689887 = 11534831) B11534831
theorem B4052969 : Blo 1800101 4052969 := bstep (se 2 (by rfl) ⟨1519863, by rfl⟩ : syracuseStep 4052969 = 3039727) B3039727
theorem B3079271 : Blo 1800101 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B34605791 : Blo 1800101 34605791 := bstep (se 1 (by rfl) ⟨25954343, by rfl⟩ : syracuseStep 34605791 = 51908687) B51908687
theorem B10259399 : Blo 1800101 10259399 := bstep (se 1 (by rfl) ⟨7694549, by rfl⟩ : syracuseStep 10259399 = 15389099) B15389099
theorem B4328407 : Blo 1800101 4328407 := bstep (se 1 (by rfl) ⟨3246305, by rfl⟩ : syracuseStep 4328407 = 6492611) B6492611
theorem B4107391 : Blo 1800101 4107391 := bstep (se 1 (by rfl) ⟨3080543, by rfl⟩ : syracuseStep 4107391 = 6161087) B6161087
theorem B73944515 : Blo 1800101 73944515 := bstep (se 1 (by rfl) ⟨55458386, by rfl⟩ : syracuseStep 73944515 = 110916773) B110916773
theorem B3419815 : Blo 1800101 3419815 := bstep (se 1 (by rfl) ⟨2564861, by rfl⟩ : syracuseStep 3419815 = 5129723) B5129723
theorem B2052847 : Blo 1800101 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B4560097 : Blo 1800101 4560097 := bstep (se 2 (by rfl) ⟨1710036, by rfl⟩ : syracuseStep 4560097 = 3420073) B3420073
theorem B13162409 : Blo 1800101 13162409 := bstep (se 2 (by rfl) ⟨4935903, by rfl⟩ : syracuseStep 13162409 = 9871807) B9871807
theorem B4052987 : Blo 1800101 4052987 := bstep (se 1 (by rfl) ⟨3039740, by rfl⟩ : syracuseStep 4052987 = 6079481) B6079481
theorem B14604479 : Blo 1800101 14604479 := bstep (se 1 (by rfl) ⟨10953359, by rfl⟩ : syracuseStep 14604479 = 21906719) B21906719
theorem B5126591 : Blo 1800101 5126591 := bstep (se 1 (by rfl) ⟨3844943, by rfl⟩ : syracuseStep 5126591 = 7689887) B7689887
theorem B2701979 : Blo 1800101 2701979 := bstep (se 1 (by rfl) ⟨2026484, by rfl⟩ : syracuseStep 2701979 = 4052969) B4052969
theorem B3037999 : Blo 1800101 3037999 := bstep (se 1 (by rfl) ⟨2278499, by rfl⟩ : syracuseStep 3037999 = 4556999) B4556999
theorem B7904411 : Blo 1800101 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B3039113 : Blo 1800101 3039113 := bstep (se 2 (by rfl) ⟨1139667, by rfl⟩ : syracuseStep 3039113 = 2279335) B2279335
theorem B2737129 : Blo 1800101 2737129 := bstep (se 2 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 2737129 = 2052847) B2052847
theorem B8774939 : Blo 1800101 8774939 := bstep (se 1 (by rfl) ⟨6581204, by rfl⟩ : syracuseStep 8774939 = 13162409) B13162409
theorem B3417727 : Blo 1800101 3417727 := bstep (se 1 (by rfl) ⟨2563295, by rfl⟩ : syracuseStep 3417727 = 5126591) B5126591
theorem B6080129 : Blo 1800101 6080129 := bstep (se 2 (by rfl) ⟨2280048, by rfl⟩ : syracuseStep 6080129 = 4560097) B4560097
theorem B23070527 : Blo 1800101 23070527 := bstep (se 1 (by rfl) ⟨17302895, by rfl⟩ : syracuseStep 23070527 = 34605791) B34605791
theorem B5269607 : Blo 1800101 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B2026075 : Blo 1800101 2026075 := bstep (se 1 (by rfl) ⟨1519556, by rfl⟩ : syracuseStep 2026075 = 3039113) B3039113
theorem B87624341 : Blo 1800101 87624341 := bstep (se 6 (by rfl) ⟨2053695, by rfl⟩ : syracuseStep 87624341 = 4107391) B4107391
theorem B4050665 : Blo 1800101 4050665 := bstep (se 2 (by rfl) ⟨1518999, by rfl⟩ : syracuseStep 4050665 = 3037999) B3037999
theorem B197185373 : Blo 1800101 197185373 := bstep (se 3 (by rfl) ⟨36972257, by rfl⟩ : syracuseStep 197185373 = 73944515) B73944515
theorem B5771209 : Blo 1800101 5771209 := bstep (se 2 (by rfl) ⟨2164203, by rfl⟩ : syracuseStep 5771209 = 4328407) B4328407
theorem B9736319 : Blo 1800101 9736319 := bstep (se 1 (by rfl) ⟨7302239, by rfl⟩ : syracuseStep 9736319 = 14604479) B14604479
theorem B4559753 : Blo 1800101 4559753 := bstep (se 2 (by rfl) ⟨1709907, by rfl⟩ : syracuseStep 4559753 = 3419815) B3419815
theorem B2701991 : Blo 1800101 2701991 := bstep (se 1 (by rfl) ⟨2026493, by rfl⟩ : syracuseStep 2701991 = 4052987) B4052987
theorem B1801319 : Blo 1800101 1801319 := bstep (se 1 (by rfl) ⟨1350989, by rfl⟩ : syracuseStep 1801319 = 2701979) B2701979
theorem B6839599 : Blo 1800101 6839599 := bstep (se 1 (by rfl) ⟨5129699, by rfl⟩ : syracuseStep 6839599 = 10259399) B10259399
theorem B3039835 : Blo 1800101 3039835 := bstep (se 1 (by rfl) ⟨2279876, by rfl⟩ : syracuseStep 3039835 = 4559753) B4559753
theorem B9119465 : Blo 1800101 9119465 := bstep (se 2 (by rfl) ⟨3419799, by rfl⟩ : syracuseStep 9119465 = 6839599) B6839599
theorem B4556969 : Blo 1800101 4556969 := bstep (se 2 (by rfl) ⟨1708863, by rfl⟩ : syracuseStep 4556969 = 3417727) B3417727
theorem B7694945 : Blo 1800101 7694945 := bstep (se 2 (by rfl) ⟨2885604, by rfl⟩ : syracuseStep 7694945 = 5771209) B5771209
theorem B25963517 : Blo 1800101 25963517 := bstep (se 3 (by rfl) ⟨4868159, by rfl⟩ : syracuseStep 25963517 = 9736319) B9736319
theorem B23399837 : Blo 1800101 23399837 := bstep (se 3 (by rfl) ⟨4387469, by rfl⟩ : syracuseStep 23399837 = 8774939) B8774939
theorem B15380351 : Blo 1800101 15380351 := bstep (se 1 (by rfl) ⟨11535263, by rfl⟩ : syracuseStep 15380351 = 23070527) B23070527
theorem B3649505 : Blo 1800101 3649505 := bstep (se 2 (by rfl) ⟨1368564, by rfl⟩ : syracuseStep 3649505 = 2737129) B2737129
theorem B2700443 : Blo 1800101 2700443 := bstep (se 1 (by rfl) ⟨2025332, by rfl⟩ : syracuseStep 2700443 = 4050665) B4050665
theorem B2701433 : Blo 1800101 2701433 := bstep (se 2 (by rfl) ⟨1013037, by rfl⟩ : syracuseStep 2701433 = 2026075) B2026075
theorem B4053419 : Blo 1800101 4053419 := bstep (se 1 (by rfl) ⟨3040064, by rfl⟩ : syracuseStep 4053419 = 6080129) B6080129
theorem B3513071 : Blo 1800101 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B58416227 : Blo 1800101 58416227 := bstep (se 1 (by rfl) ⟨43812170, by rfl⟩ : syracuseStep 58416227 = 87624341) B87624341
theorem B1801327 : Blo 1800101 1801327 := bstep (se 1 (by rfl) ⟨1350995, by rfl⟩ : syracuseStep 1801327 = 2701991) B2701991
theorem B131456915 : Blo 1800101 131456915 := bstep (se 1 (by rfl) ⟨98592686, by rfl⟩ : syracuseStep 131456915 = 197185373) B197185373
theorem B6079643 : Blo 1800101 6079643 := bstep (se 1 (by rfl) ⟨4559732, by rfl⟩ : syracuseStep 6079643 = 9119465) B9119465
theorem B5129963 : Blo 1800101 5129963 := bstep (se 1 (by rfl) ⟨3847472, by rfl⟩ : syracuseStep 5129963 = 7694945) B7694945
theorem B15599891 : Blo 1800101 15599891 := bstep (se 1 (by rfl) ⟨11699918, by rfl⟩ : syracuseStep 15599891 = 23399837) B23399837
theorem B10253567 : Blo 1800101 10253567 := bstep (se 1 (by rfl) ⟨7690175, by rfl⟩ : syracuseStep 10253567 = 15380351) B15380351
theorem B1800295 : Blo 1800101 1800295 := bstep (se 1 (by rfl) ⟨1350221, by rfl⟩ : syracuseStep 1800295 = 2700443) B2700443
theorem B4053113 : Blo 1800101 4053113 := bstep (se 2 (by rfl) ⟨1519917, by rfl⟩ : syracuseStep 4053113 = 3039835) B3039835
theorem B1800955 : Blo 1800101 1800955 := bstep (se 1 (by rfl) ⟨1350716, by rfl⟩ : syracuseStep 1800955 = 2701433) B2701433
theorem B3037979 : Blo 1800101 3037979 := bstep (se 1 (by rfl) ⟨2278484, by rfl⟩ : syracuseStep 3037979 = 4556969) B4556969
theorem B2702279 : Blo 1800101 2702279 := bstep (se 1 (by rfl) ⟨2026709, by rfl⟩ : syracuseStep 2702279 = 4053419) B4053419
theorem B2342047 : Blo 1800101 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B17309011 : Blo 1800101 17309011 := bstep (se 1 (by rfl) ⟨12981758, by rfl⟩ : syracuseStep 17309011 = 25963517) B25963517
theorem B38944151 : Blo 1800101 38944151 := bstep (se 1 (by rfl) ⟨29208113, by rfl⟩ : syracuseStep 38944151 = 58416227) B58416227
theorem B38928053 : Blo 1800101 38928053 := bstep (se 5 (by rfl) ⟨1824752, by rfl⟩ : syracuseStep 38928053 = 3649505) B3649505
theorem B87637943 : Blo 1800101 87637943 := bstep (se 1 (by rfl) ⟨65728457, by rfl⟩ : syracuseStep 87637943 = 131456915) B131456915
theorem B3122729 : Blo 1800101 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B23078681 : Blo 1800101 23078681 := bstep (se 2 (by rfl) ⟨8654505, by rfl⟩ : syracuseStep 23078681 = 17309011) B17309011
theorem B2025319 : Blo 1800101 2025319 := bstep (se 1 (by rfl) ⟨1518989, by rfl⟩ : syracuseStep 2025319 = 3037979) B3037979
theorem B25962767 : Blo 1800101 25962767 := bstep (se 1 (by rfl) ⟨19472075, by rfl⟩ : syracuseStep 25962767 = 38944151) B38944151
theorem B6835711 : Blo 1800101 6835711 := bstep (se 1 (by rfl) ⟨5126783, by rfl⟩ : syracuseStep 6835711 = 10253567) B10253567
theorem B3419975 : Blo 1800101 3419975 := bstep (se 1 (by rfl) ⟨2564981, by rfl⟩ : syracuseStep 3419975 = 5129963) B5129963
theorem B10399927 : Blo 1800101 10399927 := bstep (se 1 (by rfl) ⟨7799945, by rfl⟩ : syracuseStep 10399927 = 15599891) B15599891
theorem B4053095 : Blo 1800101 4053095 := bstep (se 1 (by rfl) ⟨3039821, by rfl⟩ : syracuseStep 4053095 = 6079643) B6079643
theorem B2702075 : Blo 1800101 2702075 := bstep (se 1 (by rfl) ⟨2026556, by rfl⟩ : syracuseStep 2702075 = 4053113) B4053113
theorem B103808141 : Blo 1800101 103808141 := bstep (se 3 (by rfl) ⟨19464026, by rfl⟩ : syracuseStep 103808141 = 38928053) B38928053
theorem B1801519 : Blo 1800101 1801519 := bstep (se 1 (by rfl) ⟨1351139, by rfl⟩ : syracuseStep 1801519 = 2702279) B2702279
theorem B58425295 : Blo 1800101 58425295 := bstep (se 1 (by rfl) ⟨43818971, by rfl⟩ : syracuseStep 58425295 = 87637943) B87637943
theorem B2081819 : Blo 1800101 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B15385787 : Blo 1800101 15385787 := bstep (se 1 (by rfl) ⟨11539340, by rfl⟩ : syracuseStep 15385787 = 23078681) B23078681
theorem B2279983 : Blo 1800101 2279983 := bstep (se 1 (by rfl) ⟨1709987, by rfl⟩ : syracuseStep 2279983 = 3419975) B3419975
theorem B77900393 : Blo 1800101 77900393 := bstep (se 2 (by rfl) ⟨29212647, by rfl⟩ : syracuseStep 77900393 = 58425295) B58425295
theorem B9114281 : Blo 1800101 9114281 := bstep (se 2 (by rfl) ⟨3417855, by rfl⟩ : syracuseStep 9114281 = 6835711) B6835711
theorem B2700425 : Blo 1800101 2700425 := bstep (se 2 (by rfl) ⟨1012659, by rfl⟩ : syracuseStep 2700425 = 2025319) B2025319
theorem B13866569 : Blo 1800101 13866569 := bstep (se 2 (by rfl) ⟨5199963, by rfl⟩ : syracuseStep 13866569 = 10399927) B10399927
theorem B2702063 : Blo 1800101 2702063 := bstep (se 1 (by rfl) ⟨2026547, by rfl⟩ : syracuseStep 2702063 = 4053095) B4053095
theorem B17308511 : Blo 1800101 17308511 := bstep (se 1 (by rfl) ⟨12981383, by rfl⟩ : syracuseStep 17308511 = 25962767) B25962767
theorem B1801383 : Blo 1800101 1801383 := bstep (se 1 (by rfl) ⟨1351037, by rfl⟩ : syracuseStep 1801383 = 2702075) B2702075
theorem B69205427 : Blo 1800101 69205427 := bstep (se 1 (by rfl) ⟨51904070, by rfl⟩ : syracuseStep 69205427 = 103808141) B103808141
theorem B3039977 : Blo 1800101 3039977 := bstep (se 2 (by rfl) ⟨1139991, by rfl⟩ : syracuseStep 3039977 = 2279983) B2279983
theorem B10257191 : Blo 1800101 10257191 := bstep (se 1 (by rfl) ⟨7692893, by rfl⟩ : syracuseStep 10257191 = 15385787) B15385787
theorem B9244379 : Blo 1800101 9244379 := bstep (se 1 (by rfl) ⟨6933284, by rfl⟩ : syracuseStep 9244379 = 13866569) B13866569
theorem B51933595 : Blo 1800101 51933595 := bstep (se 1 (by rfl) ⟨38950196, by rfl⟩ : syracuseStep 51933595 = 77900393) B77900393
theorem B11539007 : Blo 1800101 11539007 := bstep (se 1 (by rfl) ⟨8654255, by rfl⟩ : syracuseStep 11539007 = 17308511) B17308511
theorem B5551517 : Blo 1800101 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B6076187 : Blo 1800101 6076187 := bstep (se 1 (by rfl) ⟨4557140, by rfl⟩ : syracuseStep 6076187 = 9114281) B9114281
theorem B1800283 : Blo 1800101 1800283 := bstep (se 1 (by rfl) ⟨1350212, by rfl⟩ : syracuseStep 1800283 = 2700425) B2700425
theorem B1801375 : Blo 1800101 1801375 := bstep (se 1 (by rfl) ⟨1351031, by rfl⟩ : syracuseStep 1801375 = 2702063) B2702063
theorem B46136951 : Blo 1800101 46136951 := bstep (se 1 (by rfl) ⟨34602713, by rfl⟩ : syracuseStep 46136951 = 69205427) B69205427
theorem B7692671 : Blo 1800101 7692671 := bstep (se 1 (by rfl) ⟨5769503, by rfl⟩ : syracuseStep 7692671 = 11539007) B11539007
theorem B14804045 : Blo 1800101 14804045 := bstep (se 3 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 14804045 = 5551517) B5551517
theorem B24651677 : Blo 1800101 24651677 := bstep (se 3 (by rfl) ⟨4622189, by rfl⟩ : syracuseStep 24651677 = 9244379) B9244379
theorem B2026651 : Blo 1800101 2026651 := bstep (se 1 (by rfl) ⟨1519988, by rfl⟩ : syracuseStep 2026651 = 3039977) B3039977
theorem B4050791 : Blo 1800101 4050791 := bstep (se 1 (by rfl) ⟨3038093, by rfl⟩ : syracuseStep 4050791 = 6076187) B6076187
theorem B30757967 : Blo 1800101 30757967 := bstep (se 1 (by rfl) ⟨23068475, by rfl⟩ : syracuseStep 30757967 = 46136951) B46136951
theorem B6838127 : Blo 1800101 6838127 := bstep (se 1 (by rfl) ⟨5128595, by rfl⟩ : syracuseStep 6838127 = 10257191) B10257191
theorem B69244793 : Blo 1800101 69244793 := bstep (se 2 (by rfl) ⟨25966797, by rfl⟩ : syracuseStep 69244793 = 51933595) B51933595
theorem B5128447 : Blo 1800101 5128447 := bstep (se 1 (by rfl) ⟨3846335, by rfl⟩ : syracuseStep 5128447 = 7692671) B7692671
theorem B20505311 : Blo 1800101 20505311 := bstep (se 1 (by rfl) ⟨15378983, by rfl⟩ : syracuseStep 20505311 = 30757967) B30757967
theorem B46163195 : Blo 1800101 46163195 := bstep (se 1 (by rfl) ⟨34622396, by rfl⟩ : syracuseStep 46163195 = 69244793) B69244793
theorem B16434451 : Blo 1800101 16434451 := bstep (se 1 (by rfl) ⟨12325838, by rfl⟩ : syracuseStep 16434451 = 24651677) B24651677
theorem B4558751 : Blo 1800101 4558751 := bstep (se 1 (by rfl) ⟨3419063, by rfl⟩ : syracuseStep 4558751 = 6838127) B6838127
theorem B2700527 : Blo 1800101 2700527 := bstep (se 1 (by rfl) ⟨2025395, by rfl⟩ : syracuseStep 2700527 = 4050791) B4050791
theorem B9869363 : Blo 1800101 9869363 := bstep (se 1 (by rfl) ⟨7402022, by rfl⟩ : syracuseStep 9869363 = 14804045) B14804045
theorem B2702201 : Blo 1800101 2702201 := bstep (se 2 (by rfl) ⟨1013325, by rfl⟩ : syracuseStep 2702201 = 2026651) B2026651
theorem B6579575 : Blo 1800101 6579575 := bstep (se 1 (by rfl) ⟨4934681, by rfl⟩ : syracuseStep 6579575 = 9869363) B9869363
theorem B6837929 : Blo 1800101 6837929 := bstep (se 2 (by rfl) ⟨2564223, by rfl⟩ : syracuseStep 6837929 = 5128447) B5128447
theorem B13670207 : Blo 1800101 13670207 := bstep (se 1 (by rfl) ⟨10252655, by rfl⟩ : syracuseStep 13670207 = 20505311) B20505311
theorem B1800351 : Blo 1800101 1800351 := bstep (se 1 (by rfl) ⟨1350263, by rfl⟩ : syracuseStep 1800351 = 2700527) B2700527
theorem B30775463 : Blo 1800101 30775463 := bstep (se 1 (by rfl) ⟨23081597, by rfl⟩ : syracuseStep 30775463 = 46163195) B46163195
theorem B21912601 : Blo 1800101 21912601 := bstep (se 2 (by rfl) ⟨8217225, by rfl⟩ : syracuseStep 21912601 = 16434451) B16434451
theorem B1801467 : Blo 1800101 1801467 := bstep (se 1 (by rfl) ⟨1351100, by rfl⟩ : syracuseStep 1801467 = 2702201) B2702201
theorem B3039167 : Blo 1800101 3039167 := bstep (se 1 (by rfl) ⟨2279375, by rfl⟩ : syracuseStep 3039167 = 4558751) B4558751
theorem B2026111 : Blo 1800101 2026111 := bstep (se 1 (by rfl) ⟨1519583, by rfl⟩ : syracuseStep 2026111 = 3039167) B3039167
theorem B4386383 : Blo 1800101 4386383 := bstep (se 1 (by rfl) ⟨3289787, by rfl⟩ : syracuseStep 4386383 = 6579575) B6579575
theorem B4558619 : Blo 1800101 4558619 := bstep (se 1 (by rfl) ⟨3418964, by rfl⟩ : syracuseStep 4558619 = 6837929) B6837929
theorem B9113471 : Blo 1800101 9113471 := bstep (se 1 (by rfl) ⟨6835103, by rfl⟩ : syracuseStep 9113471 = 13670207) B13670207
theorem B29216801 : Blo 1800101 29216801 := bstep (se 2 (by rfl) ⟨10956300, by rfl⟩ : syracuseStep 29216801 = 21912601) B21912601
theorem B20516975 : Blo 1800101 20516975 := bstep (se 1 (by rfl) ⟨15387731, by rfl⟩ : syracuseStep 20516975 = 30775463) B30775463
theorem B6075647 : Blo 1800101 6075647 := bstep (se 1 (by rfl) ⟨4556735, by rfl⟩ : syracuseStep 6075647 = 9113471) B9113471
theorem B19477867 : Blo 1800101 19477867 := bstep (se 1 (by rfl) ⟨14608400, by rfl⟩ : syracuseStep 19477867 = 29216801) B29216801
theorem B13677983 : Blo 1800101 13677983 := bstep (se 1 (by rfl) ⟨10258487, by rfl⟩ : syracuseStep 13677983 = 20516975) B20516975
theorem B2701481 : Blo 1800101 2701481 := bstep (se 2 (by rfl) ⟨1013055, by rfl⟩ : syracuseStep 2701481 = 2026111) B2026111
theorem B2924255 : Blo 1800101 2924255 := bstep (se 1 (by rfl) ⟨2193191, by rfl⟩ : syracuseStep 2924255 = 4386383) B4386383
theorem B3039079 : Blo 1800101 3039079 := bstep (se 1 (by rfl) ⟨2279309, by rfl⟩ : syracuseStep 3039079 = 4558619) B4558619
theorem B9118655 : Blo 1800101 9118655 := bstep (se 1 (by rfl) ⟨6838991, by rfl⟩ : syracuseStep 9118655 = 13677983) B13677983
theorem B25970489 : Blo 1800101 25970489 := bstep (se 2 (by rfl) ⟨9738933, by rfl⟩ : syracuseStep 25970489 = 19477867) B19477867
theorem B4050431 : Blo 1800101 4050431 := bstep (se 1 (by rfl) ⟨3037823, by rfl⟩ : syracuseStep 4050431 = 6075647) B6075647
theorem B4052105 : Blo 1800101 4052105 := bstep (se 2 (by rfl) ⟨1519539, by rfl⟩ : syracuseStep 4052105 = 3039079) B3039079
theorem B1800987 : Blo 1800101 1800987 := bstep (se 1 (by rfl) ⟨1350740, by rfl⟩ : syracuseStep 1800987 = 2701481) B2701481
theorem B1949503 : Blo 1800101 1949503 := bstep (se 1 (by rfl) ⟨1462127, by rfl⟩ : syracuseStep 1949503 = 2924255) B2924255
theorem B6079103 : Blo 1800101 6079103 := bstep (se 1 (by rfl) ⟨4559327, by rfl⟩ : syracuseStep 6079103 = 9118655) B9118655
theorem B2599337 : Blo 1800101 2599337 := bstep (se 2 (by rfl) ⟨974751, by rfl⟩ : syracuseStep 2599337 = 1949503) B1949503
theorem B17313659 : Blo 1800101 17313659 := bstep (se 1 (by rfl) ⟨12985244, by rfl⟩ : syracuseStep 17313659 = 25970489) B25970489
theorem B2700287 : Blo 1800101 2700287 := bstep (se 1 (by rfl) ⟨2025215, by rfl⟩ : syracuseStep 2700287 = 4050431) B4050431
theorem B2701403 : Blo 1800101 2701403 := bstep (se 1 (by rfl) ⟨2026052, by rfl⟩ : syracuseStep 2701403 = 4052105) B4052105
theorem B6931565 : Blo 1800101 6931565 := bstep (se 3 (by rfl) ⟨1299668, by rfl⟩ : syracuseStep 6931565 = 2599337) B2599337
theorem B4052735 : Blo 1800101 4052735 := bstep (se 1 (by rfl) ⟨3039551, by rfl⟩ : syracuseStep 4052735 = 6079103) B6079103
theorem B1800191 : Blo 1800101 1800191 := bstep (se 1 (by rfl) ⟨1350143, by rfl⟩ : syracuseStep 1800191 = 2700287) B2700287
theorem B1800935 : Blo 1800101 1800935 := bstep (se 1 (by rfl) ⟨1350701, by rfl⟩ : syracuseStep 1800935 = 2701403) B2701403
theorem B11542439 : Blo 1800101 11542439 := bstep (se 1 (by rfl) ⟨8656829, by rfl⟩ : syracuseStep 11542439 = 17313659) B17313659
theorem B4621043 : Blo 1800101 4621043 := bstep (se 1 (by rfl) ⟨3465782, by rfl⟩ : syracuseStep 4621043 = 6931565) B6931565
theorem B30779837 : Blo 1800101 30779837 := bstep (se 3 (by rfl) ⟨5771219, by rfl⟩ : syracuseStep 30779837 = 11542439) B11542439
theorem B2701823 : Blo 1800101 2701823 := bstep (se 1 (by rfl) ⟨2026367, by rfl⟩ : syracuseStep 2701823 = 4052735) B4052735
theorem B3080695 : Blo 1800101 3080695 := bstep (se 1 (by rfl) ⟨2310521, by rfl⟩ : syracuseStep 3080695 = 4621043) B4621043
theorem B20519891 : Blo 1800101 20519891 := bstep (se 1 (by rfl) ⟨15389918, by rfl⟩ : syracuseStep 20519891 = 30779837) B30779837
theorem B1801215 : Blo 1800101 1801215 := bstep (se 1 (by rfl) ⟨1350911, by rfl⟩ : syracuseStep 1801215 = 2701823) B2701823
theorem B4107593 : Blo 1800101 4107593 := bstep (se 2 (by rfl) ⟨1540347, by rfl⟩ : syracuseStep 4107593 = 3080695) B3080695
theorem B13679927 : Blo 1800101 13679927 := bstep (se 1 (by rfl) ⟨10259945, by rfl⟩ : syracuseStep 13679927 = 20519891) B20519891
theorem B9119951 : Blo 1800101 9119951 := bstep (se 1 (by rfl) ⟨6839963, by rfl⟩ : syracuseStep 9119951 = 13679927) B13679927
theorem B2738395 : Blo 1800101 2738395 := bstep (se 1 (by rfl) ⟨2053796, by rfl⟩ : syracuseStep 2738395 = 4107593) B4107593
theorem B6079967 : Blo 1800101 6079967 := bstep (se 1 (by rfl) ⟨4559975, by rfl⟩ : syracuseStep 6079967 = 9119951) B9119951
theorem B3651193 : Blo 1800101 3651193 := bstep (se 2 (by rfl) ⟨1369197, by rfl⟩ : syracuseStep 3651193 = 2738395) B2738395
theorem B4868257 : Blo 1800101 4868257 := bstep (se 2 (by rfl) ⟨1825596, by rfl⟩ : syracuseStep 4868257 = 3651193) B3651193
theorem B4053311 : Blo 1800101 4053311 := bstep (se 1 (by rfl) ⟨3039983, by rfl⟩ : syracuseStep 4053311 = 6079967) B6079967
theorem B6491009 : Blo 1800101 6491009 := bstep (se 2 (by rfl) ⟨2434128, by rfl⟩ : syracuseStep 6491009 = 4868257) B4868257
theorem B2702207 : Blo 1800101 2702207 := bstep (se 1 (by rfl) ⟨2026655, by rfl⟩ : syracuseStep 2702207 = 4053311) B4053311
theorem B4327339 : Blo 1800101 4327339 := bstep (se 1 (by rfl) ⟨3245504, by rfl⟩ : syracuseStep 4327339 = 6491009) B6491009
theorem B1801471 : Blo 1800101 1801471 := bstep (se 1 (by rfl) ⟨1351103, by rfl⟩ : syracuseStep 1801471 = 2702207) B2702207
theorem B5769785 : Blo 1800101 5769785 := bstep (se 2 (by rfl) ⟨2163669, by rfl⟩ : syracuseStep 5769785 = 4327339) B4327339
theorem B3846523 : Blo 1800101 3846523 := bstep (se 1 (by rfl) ⟨2884892, by rfl⟩ : syracuseStep 3846523 = 5769785) B5769785
theorem B5128697 : Blo 1800101 5128697 := bstep (se 2 (by rfl) ⟨1923261, by rfl⟩ : syracuseStep 5128697 = 3846523) B3846523
theorem B13676525 : Blo 1800101 13676525 := bstep (se 3 (by rfl) ⟨2564348, by rfl⟩ : syracuseStep 13676525 = 5128697) B5128697
theorem B9117683 : Blo 1800101 9117683 := bstep (se 1 (by rfl) ⟨6838262, by rfl⟩ : syracuseStep 9117683 = 13676525) B13676525
theorem B6078455 : Blo 1800101 6078455 := bstep (se 1 (by rfl) ⟨4558841, by rfl⟩ : syracuseStep 6078455 = 9117683) B9117683
theorem B4052303 : Blo 1800101 4052303 := bstep (se 1 (by rfl) ⟨3039227, by rfl⟩ : syracuseStep 4052303 = 6078455) B6078455
theorem B2701535 : Blo 1800101 2701535 := bstep (se 1 (by rfl) ⟨2026151, by rfl⟩ : syracuseStep 2701535 = 4052303) B4052303
theorem B1801023 : Blo 1800101 1801023 := bstep (se 1 (by rfl) ⟨1350767, by rfl⟩ : syracuseStep 1801023 = 2701535) B2701535

theorem C0 (j : ℕ) (h1 : 450025 ≤ j) (h2 : j ≤ 450399) : Blo 1800101 (4 * j + 3) := by
  interval_cases j
  · exact B1800103
  · exact B1800107
  · exact B1800111
  · exact B1800115
  · exact B1800119
  · exact B1800123
  · exact B1800127
  · exact B1800131
  · exact B1800135
  · exact B1800139
  · exact B1800143
  · exact B1800147
  · exact B1800151
  · exact B1800155
  · exact B1800159
  · exact B1800163
  · exact B1800167
  · exact B1800171
  · exact B1800175
  · exact B1800179
  · exact B1800183
  · exact B1800187
  · exact B1800191
  · exact B1800195
  · exact B1800199
  · exact B1800203
  · exact B1800207
  · exact B1800211
  · exact B1800215
  · exact B1800219
  · exact B1800223
  · exact B1800227
  · exact B1800231
  · exact B1800235
  · exact B1800239
  · exact B1800243
  · exact B1800247
  · exact B1800251
  · exact B1800255
  · exact B1800259
  · exact B1800263
  · exact B1800267
  · exact B1800271
  · exact B1800275
  · exact B1800279
  · exact B1800283
  · exact B1800287
  · exact B1800291
  · exact B1800295
  · exact B1800299
  · exact B1800303
  · exact B1800307
  · exact B1800311
  · exact B1800315
  · exact B1800319
  · exact B1800323
  · exact B1800327
  · exact B1800331
  · exact B1800335
  · exact B1800339
  · exact B1800343
  · exact B1800347
  · exact B1800351
  · exact B1800355
  · exact B1800359
  · exact B1800363
  · exact B1800367
  · exact B1800371
  · exact B1800375
  · exact B1800379
  · exact B1800383
  · exact B1800387
  · exact B1800391
  · exact B1800395
  · exact B1800399
  · exact B1800403
  · exact B1800407
  · exact B1800411
  · exact B1800415
  · exact B1800419
  · exact B1800423
  · exact B1800427
  · exact B1800431
  · exact B1800435
  · exact B1800439
  · exact B1800443
  · exact B1800447
  · exact B1800451
  · exact B1800455
  · exact B1800459
  · exact B1800463
  · exact B1800467
  · exact B1800471
  · exact B1800475
  · exact B1800479
  · exact B1800483
  · exact B1800487
  · exact B1800491
  · exact B1800495
  · exact B1800499
  · exact B1800503
  · exact B1800507
  · exact B1800511
  · exact B1800515
  · exact B1800519
  · exact B1800523
  · exact B1800527
  · exact B1800531
  · exact B1800535
  · exact B1800539
  · exact B1800543
  · exact B1800547
  · exact B1800551
  · exact B1800555
  · exact B1800559
  · exact B1800563
  · exact B1800567
  · exact B1800571
  · exact B1800575
  · exact B1800579
  · exact B1800583
  · exact B1800587
  · exact B1800591
  · exact B1800595
  · exact B1800599
  · exact B1800603
  · exact B1800607
  · exact B1800611
  · exact B1800615
  · exact B1800619
  · exact B1800623
  · exact B1800627
  · exact B1800631
  · exact B1800635
  · exact B1800639
  · exact B1800643
  · exact B1800647
  · exact B1800651
  · exact B1800655
  · exact B1800659
  · exact B1800663
  · exact B1800667
  · exact B1800671
  · exact B1800675
  · exact B1800679
  · exact B1800683
  · exact B1800687
  · exact B1800691
  · exact B1800695
  · exact B1800699
  · exact B1800703
  · exact B1800707
  · exact B1800711
  · exact B1800715
  · exact B1800719
  · exact B1800723
  · exact B1800727
  · exact B1800731
  · exact B1800735
  · exact B1800739
  · exact B1800743
  · exact B1800747
  · exact B1800751
  · exact B1800755
  · exact B1800759
  · exact B1800763
  · exact B1800767
  · exact B1800771
  · exact B1800775
  · exact B1800779
  · exact B1800783
  · exact B1800787
  · exact B1800791
  · exact B1800795
  · exact B1800799
  · exact B1800803
  · exact B1800807
  · exact B1800811
  · exact B1800815
  · exact B1800819
  · exact B1800823
  · exact B1800827
  · exact B1800831
  · exact B1800835
  · exact B1800839
  · exact B1800843
  · exact B1800847
  · exact B1800851
  · exact B1800855
  · exact B1800859
  · exact B1800863
  · exact B1800867
  · exact B1800871
  · exact B1800875
  · exact B1800879
  · exact B1800883
  · exact B1800887
  · exact B1800891
  · exact B1800895
  · exact B1800899
  · exact B1800903
  · exact B1800907
  · exact B1800911
  · exact B1800915
  · exact B1800919
  · exact B1800923
  · exact B1800927
  · exact B1800931
  · exact B1800935
  · exact B1800939
  · exact B1800943
  · exact B1800947
  · exact B1800951
  · exact B1800955
  · exact B1800959
  · exact B1800963
  · exact B1800967
  · exact B1800971
  · exact B1800975
  · exact B1800979
  · exact B1800983
  · exact B1800987
  · exact B1800991
  · exact B1800995
  · exact B1800999
  · exact B1801003
  · exact B1801007
  · exact B1801011
  · exact B1801015
  · exact B1801019
  · exact B1801023
  · exact B1801027
  · exact B1801031
  · exact B1801035
  · exact B1801039
  · exact B1801043
  · exact B1801047
  · exact B1801051
  · exact B1801055
  · exact B1801059
  · exact B1801063
  · exact B1801067
  · exact B1801071
  · exact B1801075
  · exact B1801079
  · exact B1801083
  · exact B1801087
  · exact B1801091
  · exact B1801095
  · exact B1801099
  · exact B1801103
  · exact B1801107
  · exact B1801111
  · exact B1801115
  · exact B1801119
  · exact B1801123
  · exact B1801127
  · exact B1801131
  · exact B1801135
  · exact B1801139
  · exact B1801143
  · exact B1801147
  · exact B1801151
  · exact B1801155
  · exact B1801159
  · exact B1801163
  · exact B1801167
  · exact B1801171
  · exact B1801175
  · exact B1801179
  · exact B1801183
  · exact B1801187
  · exact B1801191
  · exact B1801195
  · exact B1801199
  · exact B1801203
  · exact B1801207
  · exact B1801211
  · exact B1801215
  · exact B1801219
  · exact B1801223
  · exact B1801227
  · exact B1801231
  · exact B1801235
  · exact B1801239
  · exact B1801243
  · exact B1801247
  · exact B1801251
  · exact B1801255
  · exact B1801259
  · exact B1801263
  · exact B1801267
  · exact B1801271
  · exact B1801275
  · exact B1801279
  · exact B1801283
  · exact B1801287
  · exact B1801291
  · exact B1801295
  · exact B1801299
  · exact B1801303
  · exact B1801307
  · exact B1801311
  · exact B1801315
  · exact B1801319
  · exact B1801323
  · exact B1801327
  · exact B1801331
  · exact B1801335
  · exact B1801339
  · exact B1801343
  · exact B1801347
  · exact B1801351
  · exact B1801355
  · exact B1801359
  · exact B1801363
  · exact B1801367
  · exact B1801371
  · exact B1801375
  · exact B1801379
  · exact B1801383
  · exact B1801387
  · exact B1801391
  · exact B1801395
  · exact B1801399
  · exact B1801403
  · exact B1801407
  · exact B1801411
  · exact B1801415
  · exact B1801419
  · exact B1801423
  · exact B1801427
  · exact B1801431
  · exact B1801435
  · exact B1801439
  · exact B1801443
  · exact B1801447
  · exact B1801451
  · exact B1801455
  · exact B1801459
  · exact B1801463
  · exact B1801467
  · exact B1801471
  · exact B1801475
  · exact B1801479
  · exact B1801483
  · exact B1801487
  · exact B1801491
  · exact B1801495
  · exact B1801499
  · exact B1801503
  · exact B1801507
  · exact B1801511
  · exact B1801515
  · exact B1801519
  · exact B1801523
  · exact B1801527
  · exact B1801531
  · exact B1801535
  · exact B1801539
  · exact B1801543
  · exact B1801547
  · exact B1801551
  · exact B1801555
  · exact B1801559
  · exact B1801563
  · exact B1801567
  · exact B1801571
  · exact B1801575
  · exact B1801579
  · exact B1801583
  · exact B1801587
  · exact B1801591
  · exact B1801595
  · exact B1801599

theorem solution (m : ℕ) (hlo : 1800101 ≤ m) (hhi : m ≤ 1801601) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 450025 ≤ j := by omega
    have hj2 : j ≤ 450399 := by omega
    have hb : Blo 1800101 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
