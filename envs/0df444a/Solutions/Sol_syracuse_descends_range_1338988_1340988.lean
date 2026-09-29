-- Prove2me | solution 1 for syracuse_descends_range_1338988_1340988
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:44.493497+00:00
-- url     : https://prove2.me/submissions/77032cbb-38c3-441e-8000-830f2dd2aada

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


theorem B1695745 : Blo 1338988 1695745 := bbase (se 2 (by rfl) ⟨635904, by rfl⟩ : syracuseStep 1695745 = 1271809) (by norm_num)
theorem B1507333 : Blo 1338988 1507333 := bbase (se 4 (by rfl) ⟨141312, by rfl⟩ : syracuseStep 1507333 = 282625) (by norm_num)
theorem B3014693 : Blo 1338988 3014693 := bbase (se 4 (by rfl) ⟨282627, by rfl⟩ : syracuseStep 3014693 = 565255) (by norm_num)
theorem B1507369 : Blo 1338988 1507369 := bbase (se 2 (by rfl) ⟨565263, by rfl⟩ : syracuseStep 1507369 = 1130527) (by norm_num)
theorem B8257589 : Blo 1338988 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B3391541 : Blo 1338988 3391541 := bbase (se 5 (by rfl) ⟨158978, by rfl⟩ : syracuseStep 3391541 = 317957) (by norm_num)
theorem B3219517 : Blo 1338988 3219517 := bbase (se 3 (by rfl) ⟨603659, by rfl⟩ : syracuseStep 3219517 = 1207319) (by norm_num)
theorem B1507405 : Blo 1338988 1507405 := bbase (se 3 (by rfl) ⟨282638, by rfl⟩ : syracuseStep 1507405 = 565277) (by norm_num)
theorem B28966997 : Blo 1338988 28966997 := bbase (se 8 (by rfl) ⟨169728, by rfl⟩ : syracuseStep 28966997 = 339457) (by norm_num)
theorem B1810525 : Blo 1338988 1810525 := bbase (se 3 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 1810525 = 678947) (by norm_num)
theorem B3014765 : Blo 1338988 3014765 := bbase (se 3 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 3014765 = 1130537) (by norm_num)
theorem B2261101 : Blo 1338988 2261101 := bbase (se 3 (by rfl) ⟨423956, by rfl⟩ : syracuseStep 2261101 = 847913) (by norm_num)
theorem B1507441 : Blo 1338988 1507441 := bbase (se 2 (by rfl) ⟨565290, by rfl⟩ : syracuseStep 1507441 = 1130581) (by norm_num)
theorem B5431445 : Blo 1338988 5431445 := bbase (se 6 (by rfl) ⟨127299, by rfl⟩ : syracuseStep 5431445 = 254599) (by norm_num)
theorem B1507477 : Blo 1338988 1507477 := bbase (se 6 (by rfl) ⟨35331, by rfl⟩ : syracuseStep 1507477 = 70663) (by norm_num)
theorem B3817637 : Blo 1338988 3817637 := bbase (se 4 (by rfl) ⟨357903, by rfl⟩ : syracuseStep 3817637 = 715807) (by norm_num)
theorem B1695917 : Blo 1338988 1695917 := bbase (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) (by norm_num)
theorem B3014837 : Blo 1338988 3014837 := bbase (se 5 (by rfl) ⟨141320, by rfl⟩ : syracuseStep 3014837 = 282641) (by norm_num)
theorem B1507513 : Blo 1338988 1507513 := bbase (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) (by norm_num)
theorem B5505221 : Blo 1338988 5505221 := bbase (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) (by norm_num)
theorem B2261189 : Blo 1338988 2261189 := bbase (se 4 (by rfl) ⟨211986, by rfl⟩ : syracuseStep 2261189 = 423973) (by norm_num)
theorem B1507549 : Blo 1338988 1507549 := bbase (se 3 (by rfl) ⟨282665, by rfl⟩ : syracuseStep 1507549 = 565331) (by norm_num)
theorem B1695973 : Blo 1338988 1695973 := bbase (se 4 (by rfl) ⟨158997, by rfl⟩ : syracuseStep 1695973 = 317995) (by norm_num)
theorem B4522229 : Blo 1338988 4522229 := bbase (se 5 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 4522229 = 423959) (by norm_num)
theorem B3391733 : Blo 1338988 3391733 := bbase (se 5 (by rfl) ⟨158987, by rfl⟩ : syracuseStep 3391733 = 317975) (by norm_num)
theorem B3014909 : Blo 1338988 3014909 := bbase (se 3 (by rfl) ⟨565295, by rfl⟩ : syracuseStep 3014909 = 1130591) (by norm_num)
theorem B1507585 : Blo 1338988 1507585 := bbase (se 2 (by rfl) ⟨565344, by rfl⟩ : syracuseStep 1507585 = 1130689) (by norm_num)
theorem B1507621 : Blo 1338988 1507621 := bbase (se 4 (by rfl) ⟨141339, by rfl⟩ : syracuseStep 1507621 = 282679) (by norm_num)
theorem B6111541 : Blo 1338988 6111541 := bbase (se 5 (by rfl) ⟨286478, by rfl⟩ : syracuseStep 6111541 = 572957) (by norm_num)
theorem B3014981 : Blo 1338988 3014981 := bbase (se 4 (by rfl) ⟨282654, by rfl⟩ : syracuseStep 3014981 = 565309) (by norm_num)
theorem B2261317 : Blo 1338988 2261317 := bbase (se 4 (by rfl) ⟨211998, by rfl⟩ : syracuseStep 2261317 = 423997) (by norm_num)
theorem B1696069 : Blo 1338988 1696069 := bbase (se 4 (by rfl) ⟨159006, by rfl⟩ : syracuseStep 1696069 = 318013) (by norm_num)
theorem B1507657 : Blo 1338988 1507657 := bbase (se 2 (by rfl) ⟨565371, by rfl⟩ : syracuseStep 1507657 = 1130743) (by norm_num)
theorem B5431637 : Blo 1338988 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B1507693 : Blo 1338988 1507693 := bbase (se 3 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 1507693 = 565385) (by norm_num)
theorem B1909109 : Blo 1338988 1909109 := bbase (se 5 (by rfl) ⟨89489, by rfl⟩ : syracuseStep 1909109 = 178979) (by norm_num)
theorem B3015053 : Blo 1338988 3015053 := bbase (se 3 (by rfl) ⟨565322, by rfl⟩ : syracuseStep 3015053 = 1130645) (by norm_num)
theorem B1507729 : Blo 1338988 1507729 := bbase (se 2 (by rfl) ⟨565398, by rfl⟩ : syracuseStep 1507729 = 1130797) (by norm_num)
theorem B8151445 : Blo 1338988 8151445 := bbase (se 6 (by rfl) ⟨191049, by rfl⟩ : syracuseStep 8151445 = 382099) (by norm_num)
theorem B2261405 : Blo 1338988 2261405 := bbase (se 3 (by rfl) ⟨424013, by rfl⟩ : syracuseStep 2261405 = 848027) (by norm_num)
theorem B1507765 : Blo 1338988 1507765 := bbase (se 5 (by rfl) ⟨70676, by rfl⟩ : syracuseStep 1507765 = 141353) (by norm_num)
theorem B5726645 : Blo 1338988 5726645 := bbase (se 5 (by rfl) ⟨268436, by rfl⟩ : syracuseStep 5726645 = 536873) (by norm_num)
theorem B3015125 : Blo 1338988 3015125 := bbase (se 7 (by rfl) ⟨35333, by rfl⟩ : syracuseStep 3015125 = 70667) (by norm_num)
theorem B1507801 : Blo 1338988 1507801 := bbase (se 2 (by rfl) ⟨565425, by rfl⟩ : syracuseStep 1507801 = 1130851) (by norm_num)
theorem B1696241 : Blo 1338988 1696241 := bbase (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) (by norm_num)
theorem B1507837 : Blo 1338988 1507837 := bbase (se 3 (by rfl) ⟨282719, by rfl⟩ : syracuseStep 1507837 = 565439) (by norm_num)
theorem B3015197 : Blo 1338988 3015197 := bbase (se 3 (by rfl) ⟨565349, by rfl⟩ : syracuseStep 3015197 = 1130699) (by norm_num)
theorem B2261533 : Blo 1338988 2261533 := bbase (se 3 (by rfl) ⟨424037, by rfl⟩ : syracuseStep 2261533 = 848075) (by norm_num)
theorem B1507873 : Blo 1338988 1507873 := bbase (se 2 (by rfl) ⟨565452, by rfl⟩ : syracuseStep 1507873 = 1130905) (by norm_num)
theorem B1696297 : Blo 1338988 1696297 := bbase (se 2 (by rfl) ⟨636111, by rfl⟩ : syracuseStep 1696297 = 1272223) (by norm_num)
theorem B3310141 : Blo 1338988 3310141 := bbase (se 3 (by rfl) ⟨620651, by rfl⟩ : syracuseStep 3310141 = 1241303) (by norm_num)
theorem B1507909 : Blo 1338988 1507909 := bbase (se 4 (by rfl) ⟨141366, by rfl⟩ : syracuseStep 1507909 = 282733) (by norm_num)
theorem B3392077 : Blo 1338988 3392077 := bbase (se 3 (by rfl) ⟨636014, by rfl⟩ : syracuseStep 3392077 = 1272029) (by norm_num)
theorem B3015269 : Blo 1338988 3015269 := bbase (se 4 (by rfl) ⟨282681, by rfl⟩ : syracuseStep 3015269 = 565363) (by norm_num)
theorem B1507945 : Blo 1338988 1507945 := bbase (se 2 (by rfl) ⟨565479, by rfl⟩ : syracuseStep 1507945 = 1130959) (by norm_num)
theorem B2261621 : Blo 1338988 2261621 := bbase (se 5 (by rfl) ⟨106013, by rfl⟩ : syracuseStep 2261621 = 212027) (by norm_num)
theorem B1696393 : Blo 1338988 1696393 := bbase (se 2 (by rfl) ⟨636147, by rfl⟩ : syracuseStep 1696393 = 1272295) (by norm_num)
theorem B1507981 : Blo 1338988 1507981 := bbase (se 3 (by rfl) ⟨282746, by rfl⟩ : syracuseStep 1507981 = 565493) (by norm_num)
theorem B4522661 : Blo 1338988 4522661 := bbase (se 4 (by rfl) ⟨423999, by rfl⟩ : syracuseStep 4522661 = 847999) (by norm_num)
theorem B3015341 : Blo 1338988 3015341 := bbase (se 3 (by rfl) ⟨565376, by rfl⟩ : syracuseStep 3015341 = 1130753) (by norm_num)
theorem B1508017 : Blo 1338988 1508017 := bbase (se 2 (by rfl) ⟨565506, by rfl⟩ : syracuseStep 1508017 = 1131013) (by norm_num)
theorem B3392189 : Blo 1338988 3392189 := bbase (se 3 (by rfl) ⟨636035, by rfl⟩ : syracuseStep 3392189 = 1272071) (by norm_num)
theorem B1508053 : Blo 1338988 1508053 := bbase (se 7 (by rfl) ⟨17672, by rfl⟩ : syracuseStep 1508053 = 35345) (by norm_num)
theorem B5726933 : Blo 1338988 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B9659125 : Blo 1338988 9659125 := bbase (se 5 (by rfl) ⟨452771, by rfl⟩ : syracuseStep 9659125 = 905543) (by norm_num)
theorem B3015413 : Blo 1338988 3015413 := bbase (se 5 (by rfl) ⟨141347, by rfl⟩ : syracuseStep 3015413 = 282695) (by norm_num)
theorem B2261749 : Blo 1338988 2261749 := bbase (se 5 (by rfl) ⟨106019, by rfl⟩ : syracuseStep 2261749 = 212039) (by norm_num)
theorem B1508089 : Blo 1338988 1508089 := bbase (se 2 (by rfl) ⟨565533, by rfl⟩ : syracuseStep 1508089 = 1131067) (by norm_num)
theorem B6783749 : Blo 1338988 6783749 := bbase (se 4 (by rfl) ⟨635976, by rfl⟩ : syracuseStep 6783749 = 1271953) (by norm_num)
theorem B3138317 : Blo 1338988 3138317 := bbase (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) (by norm_num)
theorem B1508125 : Blo 1338988 1508125 := bbase (se 3 (by rfl) ⟨282773, by rfl⟩ : syracuseStep 1508125 = 565547) (by norm_num)
theorem B1696565 : Blo 1338988 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B3015485 : Blo 1338988 3015485 := bbase (se 3 (by rfl) ⟨565403, by rfl⟩ : syracuseStep 3015485 = 1130807) (by norm_num)
theorem B1508161 : Blo 1338988 1508161 := bbase (se 2 (by rfl) ⟨565560, by rfl⟩ : syracuseStep 1508161 = 1131121) (by norm_num)
theorem B2261837 : Blo 1338988 2261837 := bbase (se 3 (by rfl) ⟨424094, by rfl⟩ : syracuseStep 2261837 = 848189) (by norm_num)
theorem B6611797 : Blo 1338988 6611797 := bbase (se 9 (by rfl) ⟨19370, by rfl⟩ : syracuseStep 6611797 = 38741) (by norm_num)
theorem B2147165 : Blo 1338988 2147165 := bbase (se 3 (by rfl) ⟨402593, by rfl⟩ : syracuseStep 2147165 = 805187) (by norm_num)
theorem B1508197 : Blo 1338988 1508197 := bbase (se 4 (by rfl) ⟨141393, by rfl⟩ : syracuseStep 1508197 = 282787) (by norm_num)
theorem B1696621 : Blo 1338988 1696621 := bbase (se 3 (by rfl) ⟨318116, by rfl⟩ : syracuseStep 1696621 = 636233) (by norm_num)
theorem B3392381 : Blo 1338988 3392381 := bbase (se 3 (by rfl) ⟨636071, by rfl⟩ : syracuseStep 3392381 = 1272143) (by norm_num)
theorem B3015557 : Blo 1338988 3015557 := bbase (se 4 (by rfl) ⟨282708, by rfl⟩ : syracuseStep 3015557 = 565417) (by norm_num)
theorem B1508233 : Blo 1338988 1508233 := bbase (se 2 (by rfl) ⟨565587, by rfl⟩ : syracuseStep 1508233 = 1131175) (by norm_num)
theorem B10175381 : Blo 1338988 10175381 := bbase (se 6 (by rfl) ⟨238485, by rfl⟩ : syracuseStep 10175381 = 476971) (by norm_num)
theorem B1508269 : Blo 1338988 1508269 := bbase (se 3 (by rfl) ⟨282800, by rfl⟩ : syracuseStep 1508269 = 565601) (by norm_num)
theorem B3015629 : Blo 1338988 3015629 := bbase (se 3 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 3015629 = 1130861) (by norm_num)
theorem B2261965 : Blo 1338988 2261965 := bbase (se 3 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 2261965 = 848237) (by norm_num)
theorem B1696717 : Blo 1338988 1696717 := bbase (se 3 (by rfl) ⟨318134, by rfl⟩ : syracuseStep 1696717 = 636269) (by norm_num)
theorem B1508305 : Blo 1338988 1508305 := bbase (se 2 (by rfl) ⟨565614, by rfl⟩ : syracuseStep 1508305 = 1131229) (by norm_num)
theorem B1508341 : Blo 1338988 1508341 := bbase (se 5 (by rfl) ⟨70703, by rfl⟩ : syracuseStep 1508341 = 141407) (by norm_num)
theorem B3015701 : Blo 1338988 3015701 := bbase (se 6 (by rfl) ⟨70680, by rfl⟩ : syracuseStep 3015701 = 141361) (by norm_num)
theorem B1508377 : Blo 1338988 1508377 := bbase (se 2 (by rfl) ⟨565641, by rfl⟩ : syracuseStep 1508377 = 1131283) (by norm_num)
theorem B2147357 : Blo 1338988 2147357 := bbase (se 3 (by rfl) ⟨402629, by rfl⟩ : syracuseStep 2147357 = 805259) (by norm_num)
theorem B2262053 : Blo 1338988 2262053 := bbase (se 4 (by rfl) ⟨212067, by rfl⟩ : syracuseStep 2262053 = 424135) (by norm_num)
theorem B1508413 : Blo 1338988 1508413 := bbase (se 3 (by rfl) ⟨282827, by rfl⟩ : syracuseStep 1508413 = 565655) (by norm_num)
theorem B4523093 : Blo 1338988 4523093 := bbase (se 8 (by rfl) ⟨26502, by rfl⟩ : syracuseStep 4523093 = 53005) (by norm_num)
theorem B3015773 : Blo 1338988 3015773 := bbase (se 3 (by rfl) ⟨565457, by rfl⟩ : syracuseStep 3015773 = 1130915) (by norm_num)
theorem B1508449 : Blo 1338988 1508449 := bbase (se 2 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 1508449 = 1131337) (by norm_num)
theorem B1696889 : Blo 1338988 1696889 := bbase (se 2 (by rfl) ⟨636333, by rfl⟩ : syracuseStep 1696889 = 1272667) (by norm_num)
theorem B1508485 : Blo 1338988 1508485 := bbase (se 4 (by rfl) ⟨141420, by rfl⟩ : syracuseStep 1508485 = 282841) (by norm_num)
theorem B3015845 : Blo 1338988 3015845 := bbase (se 4 (by rfl) ⟨282735, by rfl⟩ : syracuseStep 3015845 = 565471) (by norm_num)
theorem B2262181 : Blo 1338988 2262181 := bbase (se 4 (by rfl) ⟨212079, by rfl⟩ : syracuseStep 2262181 = 424159) (by norm_num)
theorem B1508521 : Blo 1338988 1508521 := bbase (se 2 (by rfl) ⟨565695, by rfl⟩ : syracuseStep 1508521 = 1131391) (by norm_num)
theorem B1696945 : Blo 1338988 1696945 := bbase (se 2 (by rfl) ⟨636354, by rfl⟩ : syracuseStep 1696945 = 1272709) (by norm_num)
theorem B3482813 : Blo 1338988 3482813 := bbase (se 3 (by rfl) ⟨653027, by rfl⟩ : syracuseStep 3482813 = 1306055) (by norm_num)
theorem B1508557 : Blo 1338988 1508557 := bbase (se 3 (by rfl) ⟨282854, by rfl⟩ : syracuseStep 1508557 = 565709) (by norm_num)
theorem B11445461 : Blo 1338988 11445461 := bbase (se 7 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 11445461 = 268253) (by norm_num)
theorem B3392725 : Blo 1338988 3392725 := bbase (se 7 (by rfl) ⟨39758, by rfl⟩ : syracuseStep 3392725 = 79517) (by norm_num)
theorem B3015917 : Blo 1338988 3015917 := bbase (se 3 (by rfl) ⟨565484, by rfl⟩ : syracuseStep 3015917 = 1130969) (by norm_num)
theorem B1508593 : Blo 1338988 1508593 := bbase (se 2 (by rfl) ⟨565722, by rfl⟩ : syracuseStep 1508593 = 1131445) (by norm_num)
theorem B2262269 : Blo 1338988 2262269 := bbase (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) (by norm_num)
theorem B1697041 : Blo 1338988 1697041 := bbase (se 2 (by rfl) ⟨636390, by rfl⟩ : syracuseStep 1697041 = 1272781) (by norm_num)
theorem B6620437 : Blo 1338988 6620437 := bbase (se 6 (by rfl) ⟨155166, by rfl⟩ : syracuseStep 6620437 = 310333) (by norm_num)
theorem B3015989 : Blo 1338988 3015989 := bbase (se 5 (by rfl) ⟨141374, by rfl⟩ : syracuseStep 3015989 = 282749) (by norm_num)
theorem B5432645 : Blo 1338988 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B3392837 : Blo 1338988 3392837 := bbase (se 4 (by rfl) ⟨318078, by rfl⟩ : syracuseStep 3392837 = 636157) (by norm_num)
theorem B4072805 : Blo 1338988 4072805 := bbase (se 4 (by rfl) ⟨381825, by rfl⟩ : syracuseStep 4072805 = 763651) (by norm_num)
theorem B1860989 : Blo 1338988 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B3016061 : Blo 1338988 3016061 := bbase (se 3 (by rfl) ⟨565511, by rfl⟩ : syracuseStep 3016061 = 1131023) (by norm_num)
theorem B2262397 : Blo 1338988 2262397 := bbase (se 3 (by rfl) ⟨424199, by rfl⟩ : syracuseStep 2262397 = 848399) (by norm_num)
theorem B3220901 : Blo 1338988 3220901 := bbase (se 4 (by rfl) ⟨301959, by rfl⟩ : syracuseStep 3220901 = 603919) (by norm_num)
theorem B2008493 : Blo 1338988 2008493 := bbase (se 3 (by rfl) ⟨376592, by rfl⟩ : syracuseStep 2008493 = 753185) (by norm_num)
theorem B2008517 : Blo 1338988 2008517 := bbase (se 4 (by rfl) ⟨188298, by rfl⟩ : syracuseStep 2008517 = 376597) (by norm_num)
theorem B6112709 : Blo 1338988 6112709 := bbase (se 4 (by rfl) ⟨573066, by rfl⟩ : syracuseStep 6112709 = 1146133) (by norm_num)
theorem B3016133 : Blo 1338988 3016133 := bbase (se 4 (by rfl) ⟨282762, by rfl⟩ : syracuseStep 3016133 = 565525) (by norm_num)
theorem B1811909 : Blo 1338988 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B5727685 : Blo 1338988 5727685 := bbase (se 4 (by rfl) ⟨536970, by rfl⟩ : syracuseStep 5727685 = 1073941) (by norm_num)
theorem B2262485 : Blo 1338988 2262485 := bbase (se 7 (by rfl) ⟨26513, by rfl⟩ : syracuseStep 2262485 = 53027) (by norm_num)
theorem B2008541 : Blo 1338988 2008541 := bbase (se 3 (by rfl) ⟨376601, by rfl⟩ : syracuseStep 2008541 = 753203) (by norm_num)
theorem B2008565 : Blo 1338988 2008565 := bbase (se 5 (by rfl) ⟨94151, by rfl⟩ : syracuseStep 2008565 = 188303) (by norm_num)
theorem B2942453 : Blo 1338988 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B3057149 : Blo 1338988 3057149 := bbase (se 3 (by rfl) ⟨573215, by rfl⟩ : syracuseStep 3057149 = 1146431) (by norm_num)
theorem B4523525 : Blo 1338988 4523525 := bbase (se 4 (by rfl) ⟨424080, by rfl⟩ : syracuseStep 4523525 = 848161) (by norm_num)
theorem B3393029 : Blo 1338988 3393029 := bbase (se 4 (by rfl) ⟨318096, by rfl⟩ : syracuseStep 3393029 = 636193) (by norm_num)
theorem B2008589 : Blo 1338988 2008589 := bbase (se 3 (by rfl) ⟨376610, by rfl⟩ : syracuseStep 2008589 = 753221) (by norm_num)
theorem B3016205 : Blo 1338988 3016205 := bbase (se 3 (by rfl) ⟨565538, by rfl⟩ : syracuseStep 3016205 = 1131077) (by norm_num)
theorem B2008613 : Blo 1338988 2008613 := bbase (se 4 (by rfl) ⟨188307, by rfl⟩ : syracuseStep 2008613 = 376615) (by norm_num)
theorem B2860589 : Blo 1338988 2860589 := bbase (se 3 (by rfl) ⟨536360, by rfl⟩ : syracuseStep 2860589 = 1072721) (by norm_num)
theorem B2008637 : Blo 1338988 2008637 := bbase (se 3 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 2008637 = 753239) (by norm_num)
theorem B2008661 : Blo 1338988 2008661 := bbase (se 8 (by rfl) ⟨11769, by rfl⟩ : syracuseStep 2008661 = 23539) (by norm_num)
theorem B3016277 : Blo 1338988 3016277 := bbase (se 8 (by rfl) ⟨17673, by rfl⟩ : syracuseStep 3016277 = 35347) (by norm_num)
theorem B2262613 : Blo 1338988 2262613 := bbase (se 8 (by rfl) ⟨13257, by rfl⟩ : syracuseStep 2262613 = 26515) (by norm_num)
theorem B3221093 : Blo 1338988 3221093 := bbase (se 4 (by rfl) ⟨301977, by rfl⟩ : syracuseStep 3221093 = 603955) (by norm_num)
theorem B2008685 : Blo 1338988 2008685 := bbase (se 3 (by rfl) ⟨376628, by rfl⟩ : syracuseStep 2008685 = 753257) (by norm_num)
theorem B2008709 : Blo 1338988 2008709 := bbase (se 4 (by rfl) ⟨188316, by rfl⟩ : syracuseStep 2008709 = 376633) (by norm_num)
theorem B2008733 : Blo 1338988 2008733 := bbase (se 3 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 2008733 = 753275) (by norm_num)
theorem B3016349 : Blo 1338988 3016349 := bbase (se 3 (by rfl) ⟨565565, by rfl⟩ : syracuseStep 3016349 = 1131131) (by norm_num)
theorem B2262701 : Blo 1338988 2262701 := bbase (se 3 (by rfl) ⟨424256, by rfl⟩ : syracuseStep 2262701 = 848513) (by norm_num)
theorem B2008757 : Blo 1338988 2008757 := bbase (se 5 (by rfl) ⟨94160, by rfl⟩ : syracuseStep 2008757 = 188321) (by norm_num)
theorem B2860733 : Blo 1338988 2860733 := bbase (se 3 (by rfl) ⟨536387, by rfl⟩ : syracuseStep 2860733 = 1072775) (by norm_num)
theorem B2008781 : Blo 1338988 2008781 := bbase (se 3 (by rfl) ⟨376646, by rfl⟩ : syracuseStep 2008781 = 753293) (by norm_num)
theorem B2008805 : Blo 1338988 2008805 := bbase (se 4 (by rfl) ⟨188325, by rfl⟩ : syracuseStep 2008805 = 376651) (by norm_num)
theorem B3016421 : Blo 1338988 3016421 := bbase (se 4 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 3016421 = 565579) (by norm_num)
theorem B5089013 : Blo 1338988 5089013 := bbase (se 5 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 5089013 = 477095) (by norm_num)
theorem B2008829 : Blo 1338988 2008829 := bbase (se 3 (by rfl) ⟨376655, by rfl⟩ : syracuseStep 2008829 = 753311) (by norm_num)
theorem B2008853 : Blo 1338988 2008853 := bbase (se 6 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 2008853 = 94165) (by norm_num)
theorem B4351781 : Blo 1338988 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B2008877 : Blo 1338988 2008877 := bbase (se 3 (by rfl) ⟨376664, by rfl⟩ : syracuseStep 2008877 = 753329) (by norm_num)
theorem B3016493 : Blo 1338988 3016493 := bbase (se 3 (by rfl) ⟨565592, by rfl⟩ : syracuseStep 3016493 = 1131185) (by norm_num)
theorem B2262829 : Blo 1338988 2262829 := bbase (se 3 (by rfl) ⟨424280, by rfl⟩ : syracuseStep 2262829 = 848561) (by norm_num)
theorem B2008901 : Blo 1338988 2008901 := bbase (se 4 (by rfl) ⟨188334, by rfl⟩ : syracuseStep 2008901 = 376669) (by norm_num)
theorem B2008925 : Blo 1338988 2008925 := bbase (se 3 (by rfl) ⟨376673, by rfl⟩ : syracuseStep 2008925 = 753347) (by norm_num)
theorem B3393373 : Blo 1338988 3393373 := bbase (se 3 (by rfl) ⟨636257, by rfl⟩ : syracuseStep 3393373 = 1272515) (by norm_num)
theorem B1632101 : Blo 1338988 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B2008949 : Blo 1338988 2008949 := bbase (se 5 (by rfl) ⟨94169, by rfl⟩ : syracuseStep 2008949 = 188339) (by norm_num)
theorem B3016565 : Blo 1338988 3016565 := bbase (se 5 (by rfl) ⟨141401, by rfl⟩ : syracuseStep 3016565 = 282803) (by norm_num)
theorem B1812341 : Blo 1338988 1812341 := bbase (se 5 (by rfl) ⟨84953, by rfl⟩ : syracuseStep 1812341 = 169907) (by norm_num)
theorem B2262917 : Blo 1338988 2262917 := bbase (se 4 (by rfl) ⟨212148, by rfl⟩ : syracuseStep 2262917 = 424297) (by norm_num)
theorem B2008973 : Blo 1338988 2008973 := bbase (se 3 (by rfl) ⟨376682, by rfl⟩ : syracuseStep 2008973 = 753365) (by norm_num)
theorem B2008997 : Blo 1338988 2008997 := bbase (se 4 (by rfl) ⟨188343, by rfl⟩ : syracuseStep 2008997 = 376687) (by norm_num)
theorem B9168821 : Blo 1338988 9168821 := bbase (se 5 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 9168821 = 859577) (by norm_num)
theorem B4523957 : Blo 1338988 4523957 := bbase (se 5 (by rfl) ⟨212060, by rfl⟩ : syracuseStep 4523957 = 424121) (by norm_num)
theorem B2009021 : Blo 1338988 2009021 := bbase (se 3 (by rfl) ⟨376691, by rfl⟩ : syracuseStep 2009021 = 753383) (by norm_num)
theorem B3016637 : Blo 1338988 3016637 := bbase (se 3 (by rfl) ⟨565619, by rfl⟩ : syracuseStep 3016637 = 1131239) (by norm_num)
theorem B3393485 : Blo 1338988 3393485 := bbase (se 3 (by rfl) ⟨636278, by rfl⟩ : syracuseStep 3393485 = 1272557) (by norm_num)
theorem B2009045 : Blo 1338988 2009045 := bbase (se 7 (by rfl) ⟨23543, by rfl⟩ : syracuseStep 2009045 = 47087) (by norm_num)
theorem B2009069 : Blo 1338988 2009069 := bbase (se 3 (by rfl) ⟨376700, by rfl⟩ : syracuseStep 2009069 = 753401) (by norm_num)
theorem B2009093 : Blo 1338988 2009093 := bbase (se 4 (by rfl) ⟨188352, by rfl⟩ : syracuseStep 2009093 = 376705) (by norm_num)
theorem B3016709 : Blo 1338988 3016709 := bbase (se 4 (by rfl) ⟨282816, by rfl⟩ : syracuseStep 3016709 = 565633) (by norm_num)
theorem B6785045 : Blo 1338988 6785045 := bbase (se 6 (by rfl) ⟨159024, by rfl⟩ : syracuseStep 6785045 = 318049) (by norm_num)
theorem B5089301 : Blo 1338988 5089301 := bbase (se 6 (by rfl) ⟨119280, by rfl⟩ : syracuseStep 5089301 = 238561) (by norm_num)
theorem B2009117 : Blo 1338988 2009117 := bbase (se 3 (by rfl) ⟨376709, by rfl⟩ : syracuseStep 2009117 = 753419) (by norm_num)
theorem B2009141 : Blo 1338988 2009141 := bbase (se 5 (by rfl) ⟨94178, by rfl⟩ : syracuseStep 2009141 = 188357) (by norm_num)
theorem B7243829 : Blo 1338988 7243829 := bbase (se 5 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 7243829 = 679109) (by norm_num)
theorem B6113333 : Blo 1338988 6113333 := bbase (se 5 (by rfl) ⟨286562, by rfl⟩ : syracuseStep 6113333 = 573125) (by norm_num)
theorem B2009165 : Blo 1338988 2009165 := bbase (se 3 (by rfl) ⟨376718, by rfl⟩ : syracuseStep 2009165 = 753437) (by norm_num)
theorem B3016781 : Blo 1338988 3016781 := bbase (se 3 (by rfl) ⟨565646, by rfl⟩ : syracuseStep 3016781 = 1131293) (by norm_num)
theorem B2009189 : Blo 1338988 2009189 := bbase (se 4 (by rfl) ⟨188361, by rfl⟩ : syracuseStep 2009189 = 376723) (by norm_num)
theorem B2009213 : Blo 1338988 2009213 := bbase (se 3 (by rfl) ⟨376727, by rfl⟩ : syracuseStep 2009213 = 753455) (by norm_num)
theorem B3393677 : Blo 1338988 3393677 := bbase (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) (by norm_num)
theorem B2009237 : Blo 1338988 2009237 := bbase (se 6 (by rfl) ⟨47091, by rfl⟩ : syracuseStep 2009237 = 94183) (by norm_num)
theorem B3016853 : Blo 1338988 3016853 := bbase (se 6 (by rfl) ⟨70707, by rfl⟩ : syracuseStep 3016853 = 141415) (by norm_num)
theorem B2009261 : Blo 1338988 2009261 := bbase (se 3 (by rfl) ⟨376736, by rfl⟩ : syracuseStep 2009261 = 753473) (by norm_num)
theorem B2902189 : Blo 1338988 2902189 := bbase (se 3 (by rfl) ⟨544160, by rfl⟩ : syracuseStep 2902189 = 1088321) (by norm_num)
theorem B2009285 : Blo 1338988 2009285 := bbase (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) (by norm_num)
theorem B3623125 : Blo 1338988 3623125 := bbase (se 7 (by rfl) ⟨42458, by rfl⟩ : syracuseStep 3623125 = 84917) (by norm_num)
theorem B2009309 : Blo 1338988 2009309 := bbase (se 3 (by rfl) ⟨376745, by rfl⟩ : syracuseStep 2009309 = 753491) (by norm_num)
theorem B3016925 : Blo 1338988 3016925 := bbase (se 3 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 3016925 = 1131347) (by norm_num)
theorem B3262693 : Blo 1338988 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B2009333 : Blo 1338988 2009333 := bbase (se 5 (by rfl) ⟨94187, by rfl⟩ : syracuseStep 2009333 = 188375) (by norm_num)
theorem B2009357 : Blo 1338988 2009357 := bbase (se 3 (by rfl) ⟨376754, by rfl⟩ : syracuseStep 2009357 = 753509) (by norm_num)
theorem B2009381 : Blo 1338988 2009381 := bbase (se 4 (by rfl) ⟨188379, by rfl⟩ : syracuseStep 2009381 = 376759) (by norm_num)
theorem B3016997 : Blo 1338988 3016997 := bbase (se 4 (by rfl) ⟨282843, by rfl⟩ : syracuseStep 3016997 = 565687) (by norm_num)
theorem B2009405 : Blo 1338988 2009405 := bbase (se 3 (by rfl) ⟨376763, by rfl⟩ : syracuseStep 2009405 = 753527) (by norm_num)
theorem B2009429 : Blo 1338988 2009429 := bbase (se 10 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 2009429 = 5887) (by norm_num)
theorem B4524389 : Blo 1338988 4524389 := bbase (se 4 (by rfl) ⟨424161, by rfl⟩ : syracuseStep 4524389 = 848323) (by norm_num)
theorem B3221861 : Blo 1338988 3221861 := bbase (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) (by norm_num)
theorem B2009453 : Blo 1338988 2009453 := bbase (se 3 (by rfl) ⟨376772, by rfl⟩ : syracuseStep 2009453 = 753545) (by norm_num)
theorem B3017069 : Blo 1338988 3017069 := bbase (se 3 (by rfl) ⟨565700, by rfl⟩ : syracuseStep 3017069 = 1131401) (by norm_num)
theorem B2902397 : Blo 1338988 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B2009477 : Blo 1338988 2009477 := bbase (se 4 (by rfl) ⟨188388, by rfl⟩ : syracuseStep 2009477 = 376777) (by norm_num)
theorem B2009501 : Blo 1338988 2009501 := bbase (se 3 (by rfl) ⟨376781, by rfl⟩ : syracuseStep 2009501 = 753563) (by norm_num)
theorem B2861477 : Blo 1338988 2861477 := bbase (se 4 (by rfl) ⟨268263, by rfl⟩ : syracuseStep 2861477 = 536527) (by norm_num)
theorem B2009525 : Blo 1338988 2009525 := bbase (se 5 (by rfl) ⟨94196, by rfl⟩ : syracuseStep 2009525 = 188393) (by norm_num)
theorem B3017141 : Blo 1338988 3017141 := bbase (se 5 (by rfl) ⟨141428, by rfl⟩ : syracuseStep 3017141 = 282857) (by norm_num)
theorem B2009549 : Blo 1338988 2009549 := bbase (se 3 (by rfl) ⟨376790, by rfl⟩ : syracuseStep 2009549 = 753581) (by norm_num)
theorem B2009573 : Blo 1338988 2009573 := bbase (se 4 (by rfl) ⟨188397, by rfl⟩ : syracuseStep 2009573 = 376795) (by norm_num)
theorem B3394021 : Blo 1338988 3394021 := bbase (se 4 (by rfl) ⟨318189, by rfl⟩ : syracuseStep 3394021 = 636379) (by norm_num)
theorem B2009597 : Blo 1338988 2009597 := bbase (se 3 (by rfl) ⟨376799, by rfl⟩ : syracuseStep 2009597 = 753599) (by norm_num)
theorem B3017213 : Blo 1338988 3017213 := bbase (se 3 (by rfl) ⟨565727, by rfl⟩ : syracuseStep 3017213 = 1131455) (by norm_num)
theorem B3058181 : Blo 1338988 3058181 := bbase (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) (by norm_num)
theorem B2009621 : Blo 1338988 2009621 := bbase (se 6 (by rfl) ⟨47100, by rfl⟩ : syracuseStep 2009621 = 94201) (by norm_num)
theorem B2009645 : Blo 1338988 2009645 := bbase (se 3 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 2009645 = 753617) (by norm_num)
theorem B5720645 : Blo 1338988 5720645 := bbase (se 4 (by rfl) ⟨536310, by rfl⟩ : syracuseStep 5720645 = 1072621) (by norm_num)
theorem B2009669 : Blo 1338988 2009669 := bbase (se 4 (by rfl) ⟨188406, by rfl⟩ : syracuseStep 2009669 = 376813) (by norm_num)
theorem B3394133 : Blo 1338988 3394133 := bbase (se 8 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 3394133 = 39775) (by norm_num)
theorem B2009693 : Blo 1338988 2009693 := bbase (se 3 (by rfl) ⟨376817, by rfl⟩ : syracuseStep 2009693 = 753635) (by norm_num)
theorem B2009717 : Blo 1338988 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B2542205 : Blo 1338988 2542205 := bbase (se 3 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 2542205 = 953327) (by norm_num)
theorem B2009741 : Blo 1338988 2009741 := bbase (se 3 (by rfl) ⟨376826, by rfl⟩ : syracuseStep 2009741 = 753653) (by norm_num)
theorem B2009765 : Blo 1338988 2009765 := bbase (se 4 (by rfl) ⟨188415, by rfl⟩ : syracuseStep 2009765 = 376831) (by norm_num)
theorem B2009789 : Blo 1338988 2009789 := bbase (se 3 (by rfl) ⟨376835, by rfl⟩ : syracuseStep 2009789 = 753671) (by norm_num)
theorem B2009813 : Blo 1338988 2009813 := bbase (se 7 (by rfl) ⟨23552, by rfl⟩ : syracuseStep 2009813 = 47105) (by norm_num)
theorem B2009837 : Blo 1338988 2009837 := bbase (se 3 (by rfl) ⟨376844, by rfl⟩ : syracuseStep 2009837 = 753689) (by norm_num)
theorem B2009861 : Blo 1338988 2009861 := bbase (se 4 (by rfl) ⟨188424, by rfl⟩ : syracuseStep 2009861 = 376849) (by norm_num)
theorem B2542357 : Blo 1338988 2542357 := bbase (se 6 (by rfl) ⟨59586, by rfl⟩ : syracuseStep 2542357 = 119173) (by norm_num)
theorem B4524821 : Blo 1338988 4524821 := bbase (se 6 (by rfl) ⟨106050, by rfl⟩ : syracuseStep 4524821 = 212101) (by norm_num)
theorem B3394325 : Blo 1338988 3394325 := bbase (se 6 (by rfl) ⟨79554, by rfl⟩ : syracuseStep 3394325 = 159109) (by norm_num)
theorem B2009885 : Blo 1338988 2009885 := bbase (se 3 (by rfl) ⟨376853, by rfl⟩ : syracuseStep 2009885 = 753707) (by norm_num)
theorem B2009909 : Blo 1338988 2009909 := bbase (se 5 (by rfl) ⟨94214, by rfl⟩ : syracuseStep 2009909 = 188429) (by norm_num)
theorem B2009933 : Blo 1338988 2009933 := bbase (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) (by norm_num)
theorem B2009957 : Blo 1338988 2009957 := bbase (se 4 (by rfl) ⟨188433, by rfl⟩ : syracuseStep 2009957 = 376867) (by norm_num)
theorem B2009981 : Blo 1338988 2009981 := bbase (se 3 (by rfl) ⟨376871, by rfl⟩ : syracuseStep 2009981 = 753743) (by norm_num)
theorem B2010005 : Blo 1338988 2010005 := bbase (se 6 (by rfl) ⟨47109, by rfl⟩ : syracuseStep 2010005 = 94219) (by norm_num)
theorem B6441877 : Blo 1338988 6441877 := bbase (se 6 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 6441877 = 301963) (by norm_num)
theorem B2010029 : Blo 1338988 2010029 := bbase (se 3 (by rfl) ⟨376880, by rfl⟩ : syracuseStep 2010029 = 753761) (by norm_num)
theorem B2010053 : Blo 1338988 2010053 := bbase (se 4 (by rfl) ⟨188442, by rfl⟩ : syracuseStep 2010053 = 376885) (by norm_num)
theorem B2010077 : Blo 1338988 2010077 := bbase (se 3 (by rfl) ⟨376889, by rfl⟩ : syracuseStep 2010077 = 753779) (by norm_num)
theorem B1608673 : Blo 1338988 1608673 := bbase (se 2 (by rfl) ⟨603252, by rfl⟩ : syracuseStep 1608673 = 1206505) (by norm_num)
theorem B2010101 : Blo 1338988 2010101 := bbase (se 5 (by rfl) ⟨94223, by rfl⟩ : syracuseStep 2010101 = 188447) (by norm_num)
theorem B1608701 : Blo 1338988 1608701 := bbase (se 3 (by rfl) ⟨301631, by rfl⟩ : syracuseStep 1608701 = 603263) (by norm_num)
theorem B2010125 : Blo 1338988 2010125 := bbase (se 3 (by rfl) ⟨376898, by rfl⟩ : syracuseStep 2010125 = 753797) (by norm_num)
theorem B2010149 : Blo 1338988 2010149 := bbase (se 4 (by rfl) ⟨188451, by rfl⟩ : syracuseStep 2010149 = 376903) (by norm_num)
theorem B1395749 : Blo 1338988 1395749 := bbase (se 4 (by rfl) ⟨130851, by rfl⟩ : syracuseStep 1395749 = 261703) (by norm_num)
theorem B2010173 : Blo 1338988 2010173 := bbase (se 3 (by rfl) ⟨376907, by rfl⟩ : syracuseStep 2010173 = 753815) (by norm_num)
theorem B2542661 : Blo 1338988 2542661 := bbase (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) (by norm_num)
theorem B2010197 : Blo 1338988 2010197 := bbase (se 8 (by rfl) ⟨11778, by rfl⟩ : syracuseStep 2010197 = 23557) (by norm_num)
theorem B2714717 : Blo 1338988 2714717 := bbase (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) (by norm_num)
theorem B2010221 : Blo 1338988 2010221 := bbase (se 3 (by rfl) ⟨376916, by rfl⟩ : syracuseStep 2010221 = 753833) (by norm_num)
theorem B1608817 : Blo 1338988 1608817 := bbase (se 2 (by rfl) ⟨603306, by rfl⟩ : syracuseStep 1608817 = 1206613) (by norm_num)
theorem B2010245 : Blo 1338988 2010245 := bbase (se 4 (by rfl) ⟨188460, by rfl⟩ : syracuseStep 2010245 = 376921) (by norm_num)
theorem B2862229 : Blo 1338988 2862229 := bbase (se 6 (by rfl) ⟨67083, by rfl⟩ : syracuseStep 2862229 = 134167) (by norm_num)
theorem B1469593 : Blo 1338988 1469593 := bbase (se 2 (by rfl) ⟨551097, by rfl⟩ : syracuseStep 1469593 = 1102195) (by norm_num)
theorem B2010269 : Blo 1338988 2010269 := bbase (se 3 (by rfl) ⟨376925, by rfl⟩ : syracuseStep 2010269 = 753851) (by norm_num)
theorem B2010293 : Blo 1338988 2010293 := bbase (se 5 (by rfl) ⟨94232, by rfl⟩ : syracuseStep 2010293 = 188465) (by norm_num)
theorem B5090485 : Blo 1338988 5090485 := bbase (se 5 (by rfl) ⟨238616, by rfl⟩ : syracuseStep 5090485 = 477233) (by norm_num)
theorem B1526969 : Blo 1338988 1526969 := bbase (se 2 (by rfl) ⟨572613, by rfl⟩ : syracuseStep 1526969 = 1145227) (by norm_num)
theorem B4525253 : Blo 1338988 4525253 := bbase (se 4 (by rfl) ⟨424242, by rfl⟩ : syracuseStep 4525253 = 848485) (by norm_num)
theorem B2010317 : Blo 1338988 2010317 := bbase (se 3 (by rfl) ⟨376934, by rfl⟩ : syracuseStep 2010317 = 753869) (by norm_num)
theorem B1608913 : Blo 1338988 1608913 := bbase (se 2 (by rfl) ⟨603342, by rfl⟩ : syracuseStep 1608913 = 1206685) (by norm_num)
theorem B2010341 : Blo 1338988 2010341 := bbase (se 4 (by rfl) ⟨188469, by rfl⟩ : syracuseStep 2010341 = 376939) (by norm_num)
theorem B2010365 : Blo 1338988 2010365 := bbase (se 3 (by rfl) ⟨376943, by rfl⟩ : syracuseStep 2010365 = 753887) (by norm_num)
theorem B17173781 : Blo 1338988 17173781 := bbase (se 6 (by rfl) ⟨402510, by rfl⟩ : syracuseStep 17173781 = 805021) (by norm_num)
theorem B2010389 : Blo 1338988 2010389 := bbase (se 6 (by rfl) ⟨47118, by rfl⟩ : syracuseStep 2010389 = 94237) (by norm_num)
theorem B2862373 : Blo 1338988 2862373 := bbase (se 4 (by rfl) ⟨268347, by rfl⟩ : syracuseStep 2862373 = 536695) (by norm_num)
theorem B6786341 : Blo 1338988 6786341 := bbase (se 4 (by rfl) ⟨636219, by rfl⟩ : syracuseStep 6786341 = 1272439) (by norm_num)
theorem B2010413 : Blo 1338988 2010413 := bbase (se 3 (by rfl) ⟨376952, by rfl⟩ : syracuseStep 2010413 = 753905) (by norm_num)
theorem B2010437 : Blo 1338988 2010437 := bbase (se 4 (by rfl) ⟨188478, by rfl⟩ : syracuseStep 2010437 = 376957) (by norm_num)
theorem B2010461 : Blo 1338988 2010461 := bbase (se 3 (by rfl) ⟨376961, by rfl⟩ : syracuseStep 2010461 = 753923) (by norm_num)
theorem B2010485 : Blo 1338988 2010485 := bbase (se 5 (by rfl) ⟨94241, by rfl⟩ : syracuseStep 2010485 = 188483) (by norm_num)
theorem B2010509 : Blo 1338988 2010509 := bbase (se 3 (by rfl) ⟨376970, by rfl⟩ : syracuseStep 2010509 = 753941) (by norm_num)
theorem B2010533 : Blo 1338988 2010533 := bbase (se 4 (by rfl) ⟨188487, by rfl⟩ : syracuseStep 2010533 = 376975) (by norm_num)
theorem B2010557 : Blo 1338988 2010557 := bbase (se 3 (by rfl) ⟨376979, by rfl⟩ : syracuseStep 2010557 = 753959) (by norm_num)
theorem B2010581 : Blo 1338988 2010581 := bbase (se 7 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 2010581 = 47123) (by norm_num)
theorem B5090789 : Blo 1338988 5090789 := bbase (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) (by norm_num)
theorem B2010605 : Blo 1338988 2010605 := bbase (se 3 (by rfl) ⟨376988, by rfl⟩ : syracuseStep 2010605 = 753977) (by norm_num)
theorem B2010629 : Blo 1338988 2010629 := bbase (se 4 (by rfl) ⟨188496, by rfl⟩ : syracuseStep 2010629 = 376993) (by norm_num)
theorem B2010653 : Blo 1338988 2010653 := bbase (se 3 (by rfl) ⟨376997, by rfl⟩ : syracuseStep 2010653 = 753995) (by norm_num)
theorem B5721637 : Blo 1338988 5721637 := bbase (se 4 (by rfl) ⟨536403, by rfl⟩ : syracuseStep 5721637 = 1072807) (by norm_num)
theorem B2010677 : Blo 1338988 2010677 := bbase (se 5 (by rfl) ⟨94250, by rfl⟩ : syracuseStep 2010677 = 188501) (by norm_num)
theorem B2010701 : Blo 1338988 2010701 := bbase (se 3 (by rfl) ⟨377006, by rfl⟩ : syracuseStep 2010701 = 754013) (by norm_num)
theorem B2010725 : Blo 1338988 2010725 := bbase (se 4 (by rfl) ⟨188505, by rfl⟩ : syracuseStep 2010725 = 377011) (by norm_num)
theorem B4525685 : Blo 1338988 4525685 := bbase (se 5 (by rfl) ⟨212141, by rfl⟩ : syracuseStep 4525685 = 424283) (by norm_num)
theorem B2010749 : Blo 1338988 2010749 := bbase (se 3 (by rfl) ⟨377015, by rfl⟩ : syracuseStep 2010749 = 754031) (by norm_num)
theorem B2010773 : Blo 1338988 2010773 := bbase (se 6 (by rfl) ⟨47127, by rfl⟩ : syracuseStep 2010773 = 94255) (by norm_num)
theorem B2862749 : Blo 1338988 2862749 := bbase (se 3 (by rfl) ⟨536765, by rfl⟩ : syracuseStep 2862749 = 1073531) (by norm_num)
theorem B2010797 : Blo 1338988 2010797 := bbase (se 3 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 2010797 = 754049) (by norm_num)
theorem B1609393 : Blo 1338988 1609393 := bbase (se 2 (by rfl) ⟨603522, by rfl⟩ : syracuseStep 1609393 = 1207045) (by norm_num)
theorem B2010821 : Blo 1338988 2010821 := bbase (se 4 (by rfl) ⟨188514, by rfl⟩ : syracuseStep 2010821 = 377029) (by norm_num)
theorem B2010845 : Blo 1338988 2010845 := bbase (se 3 (by rfl) ⟨377033, by rfl⟩ : syracuseStep 2010845 = 754067) (by norm_num)
theorem B2010869 : Blo 1338988 2010869 := bbase (se 5 (by rfl) ⟨94259, by rfl⟩ : syracuseStep 2010869 = 188519) (by norm_num)
theorem B2010893 : Blo 1338988 2010893 := bbase (se 3 (by rfl) ⟨377042, by rfl⟩ : syracuseStep 2010893 = 754085) (by norm_num)
theorem B3624725 : Blo 1338988 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B2010917 : Blo 1338988 2010917 := bbase (se 4 (by rfl) ⟨188523, by rfl⟩ : syracuseStep 2010917 = 377047) (by norm_num)
theorem B2543413 : Blo 1338988 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B2010941 : Blo 1338988 2010941 := bbase (se 3 (by rfl) ⟨377051, by rfl⟩ : syracuseStep 2010941 = 754103) (by norm_num)
theorem B2010965 : Blo 1338988 2010965 := bbase (se 9 (by rfl) ⟨5891, by rfl⟩ : syracuseStep 2010965 = 11783) (by norm_num)
theorem B2010989 : Blo 1338988 2010989 := bbase (se 3 (by rfl) ⟨377060, by rfl⟩ : syracuseStep 2010989 = 754121) (by norm_num)
theorem B2011013 : Blo 1338988 2011013 := bbase (se 4 (by rfl) ⟨188532, by rfl⟩ : syracuseStep 2011013 = 377065) (by norm_num)
theorem B2011037 : Blo 1338988 2011037 := bbase (se 3 (by rfl) ⟨377069, by rfl⟩ : syracuseStep 2011037 = 754139) (by norm_num)
theorem B2011061 : Blo 1338988 2011061 := bbase (se 5 (by rfl) ⟨94268, by rfl⟩ : syracuseStep 2011061 = 188537) (by norm_num)
theorem B2543557 : Blo 1338988 2543557 := bbase (se 4 (by rfl) ⟨238458, by rfl⟩ : syracuseStep 2543557 = 476917) (by norm_num)
theorem B2011085 : Blo 1338988 2011085 := bbase (se 3 (by rfl) ⟨377078, by rfl⟩ : syracuseStep 2011085 = 754157) (by norm_num)
theorem B2011109 : Blo 1338988 2011109 := bbase (se 4 (by rfl) ⟨188541, by rfl⟩ : syracuseStep 2011109 = 377083) (by norm_num)
theorem B12881909 : Blo 1338988 12881909 := bbase (se 5 (by rfl) ⟨603839, by rfl⟩ : syracuseStep 12881909 = 1207679) (by norm_num)
theorem B2011133 : Blo 1338988 2011133 := bbase (se 3 (by rfl) ⟨377087, by rfl⟩ : syracuseStep 2011133 = 754175) (by norm_num)
theorem B2863117 : Blo 1338988 2863117 := bbase (se 3 (by rfl) ⟨536834, by rfl⟩ : syracuseStep 2863117 = 1073669) (by norm_num)
theorem B2011157 : Blo 1338988 2011157 := bbase (se 6 (by rfl) ⟨47136, by rfl⟩ : syracuseStep 2011157 = 94273) (by norm_num)
theorem B2011181 : Blo 1338988 2011181 := bbase (se 3 (by rfl) ⟨377096, by rfl⟩ : syracuseStep 2011181 = 754193) (by norm_num)
theorem B2011205 : Blo 1338988 2011205 := bbase (se 4 (by rfl) ⟨188550, by rfl⟩ : syracuseStep 2011205 = 377101) (by norm_num)
theorem B2011229 : Blo 1338988 2011229 := bbase (se 3 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 2011229 = 754211) (by norm_num)
theorem B2543717 : Blo 1338988 2543717 := bbase (se 4 (by rfl) ⟨238473, by rfl⟩ : syracuseStep 2543717 = 476947) (by norm_num)
theorem B2011253 : Blo 1338988 2011253 := bbase (se 5 (by rfl) ⟨94277, by rfl⟩ : syracuseStep 2011253 = 188555) (by norm_num)
theorem B2011277 : Blo 1338988 2011277 := bbase (se 3 (by rfl) ⟨377114, by rfl⟩ : syracuseStep 2011277 = 754229) (by norm_num)
theorem B2011301 : Blo 1338988 2011301 := bbase (se 4 (by rfl) ⟨188559, by rfl⟩ : syracuseStep 2011301 = 377119) (by norm_num)
theorem B3436717 : Blo 1338988 3436717 := bbase (se 3 (by rfl) ⟨644384, by rfl⟩ : syracuseStep 3436717 = 1288769) (by norm_num)
theorem B9662645 : Blo 1338988 9662645 := bbase (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) (by norm_num)
theorem B2011325 : Blo 1338988 2011325 := bbase (se 3 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 2011325 = 754247) (by norm_num)
theorem B2011349 : Blo 1338988 2011349 := bbase (se 7 (by rfl) ⟨23570, by rfl⟩ : syracuseStep 2011349 = 47141) (by norm_num)
theorem B3813605 : Blo 1338988 3813605 := bbase (se 4 (by rfl) ⟨357525, by rfl⟩ : syracuseStep 3813605 = 715051) (by norm_num)
theorem B2011373 : Blo 1338988 2011373 := bbase (se 3 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 2011373 = 754265) (by norm_num)
theorem B2543861 : Blo 1338988 2543861 := bbase (se 5 (by rfl) ⟨119243, by rfl⟩ : syracuseStep 2543861 = 238487) (by norm_num)
theorem B2011397 : Blo 1338988 2011397 := bbase (se 4 (by rfl) ⟨188568, by rfl⟩ : syracuseStep 2011397 = 377137) (by norm_num)
theorem B2011421 : Blo 1338988 2011421 := bbase (se 3 (by rfl) ⟨377141, by rfl⟩ : syracuseStep 2011421 = 754283) (by norm_num)
theorem B2011445 : Blo 1338988 2011445 := bbase (se 5 (by rfl) ⟨94286, by rfl⟩ : syracuseStep 2011445 = 188573) (by norm_num)
theorem B1528141 : Blo 1338988 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B2011469 : Blo 1338988 2011469 := bbase (se 3 (by rfl) ⟨377150, by rfl⟩ : syracuseStep 2011469 = 754301) (by norm_num)
theorem B1430021 : Blo 1338988 1430021 := bbase (se 4 (by rfl) ⟨134064, by rfl⟩ : syracuseStep 1430021 = 268129) (by norm_num)
theorem B2544149 : Blo 1338988 2544149 := bbase (se 6 (by rfl) ⟨59628, by rfl⟩ : syracuseStep 2544149 = 119257) (by norm_num)
theorem B6787637 : Blo 1338988 6787637 := bbase (se 5 (by rfl) ⟨318170, by rfl⟩ : syracuseStep 6787637 = 636341) (by norm_num)
theorem B1430093 : Blo 1338988 1430093 := bbase (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) (by norm_num)
theorem B3814037 : Blo 1338988 3814037 := bbase (se 6 (by rfl) ⟨89391, by rfl⟩ : syracuseStep 3814037 = 178783) (by norm_num)
theorem B5804693 : Blo 1338988 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B2544301 : Blo 1338988 2544301 := bbase (se 3 (by rfl) ⟨477056, by rfl⟩ : syracuseStep 2544301 = 954113) (by norm_num)
theorem B6435557 : Blo 1338988 6435557 := bbase (se 4 (by rfl) ⟨603333, by rfl⟩ : syracuseStep 6435557 = 1206667) (by norm_num)
theorem B1430281 : Blo 1338988 1430281 := bbase (se 2 (by rfl) ⟨536355, by rfl⟩ : syracuseStep 1430281 = 1072711) (by norm_num)
theorem B2716429 : Blo 1338988 2716429 := bbase (se 3 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 2716429 = 1018661) (by norm_num)
theorem B3437413 : Blo 1338988 3437413 := bbase (se 4 (by rfl) ⟨322257, by rfl⟩ : syracuseStep 3437413 = 644515) (by norm_num)
theorem B2577277 : Blo 1338988 2577277 := bbase (se 3 (by rfl) ⟨483239, by rfl⟩ : syracuseStep 2577277 = 966479) (by norm_num)
theorem B7631765 : Blo 1338988 7631765 := bbase (se 6 (by rfl) ⟨178869, by rfl⟩ : syracuseStep 7631765 = 357739) (by norm_num)
theorem B1430465 : Blo 1338988 1430465 := bbase (se 2 (by rfl) ⟨536424, by rfl⟩ : syracuseStep 1430465 = 1072849) (by norm_num)
theorem B9286613 : Blo 1338988 9286613 := bbase (se 7 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 9286613 = 217655) (by norm_num)
theorem B6779861 : Blo 1338988 6779861 := bbase (se 7 (by rfl) ⟨79451, by rfl⟩ : syracuseStep 6779861 = 158903) (by norm_num)
theorem B2544605 : Blo 1338988 2544605 := bbase (se 3 (by rfl) ⟨477113, by rfl⟩ : syracuseStep 2544605 = 954227) (by norm_num)
theorem B1610777 : Blo 1338988 1610777 := bbase (se 2 (by rfl) ⟨604041, by rfl⟩ : syracuseStep 1610777 = 1208083) (by norm_num)
theorem B1610965 : Blo 1338988 1610965 := bbase (se 7 (by rfl) ⟨18878, by rfl⟩ : syracuseStep 1610965 = 37757) (by norm_num)
theorem B1570045 : Blo 1338988 1570045 := bbase (se 3 (by rfl) ⟨294383, by rfl⟩ : syracuseStep 1570045 = 588767) (by norm_num)
theorem B4519205 : Blo 1338988 4519205 := bbase (se 4 (by rfl) ⟨423675, by rfl⟩ : syracuseStep 4519205 = 847351) (by norm_num)
theorem B2176381 : Blo 1338988 2176381 := bbase (se 3 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 2176381 = 816143) (by norm_num)
theorem B3814789 : Blo 1338988 3814789 := bbase (se 4 (by rfl) ⟨357636, by rfl⟩ : syracuseStep 3814789 = 715273) (by norm_num)
theorem B2414141 : Blo 1338988 2414141 := bbase (se 3 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 2414141 = 905303) (by norm_num)
theorem B3438197 : Blo 1338988 3438197 := bbase (se 5 (by rfl) ⟨161165, by rfl⟩ : syracuseStep 3438197 = 322331) (by norm_num)
theorem B1431217 : Blo 1338988 1431217 := bbase (se 2 (by rfl) ⟨536706, by rfl⟩ : syracuseStep 1431217 = 1073413) (by norm_num)
theorem B2545357 : Blo 1338988 2545357 := bbase (se 3 (by rfl) ⟨477254, by rfl⟩ : syracuseStep 2545357 = 954509) (by norm_num)
theorem B4519637 : Blo 1338988 4519637 := bbase (se 7 (by rfl) ⟨52964, by rfl⟩ : syracuseStep 4519637 = 105929) (by norm_num)
theorem B1431289 : Blo 1338988 1431289 := bbase (se 2 (by rfl) ⟨536733, by rfl⟩ : syracuseStep 1431289 = 1073467) (by norm_num)
theorem B3438341 : Blo 1338988 3438341 := bbase (se 4 (by rfl) ⟨322344, by rfl⟩ : syracuseStep 3438341 = 644689) (by norm_num)
theorem B5429045 : Blo 1338988 5429045 := bbase (se 5 (by rfl) ⟨254486, by rfl⟩ : syracuseStep 5429045 = 508973) (by norm_num)
theorem B2545501 : Blo 1338988 2545501 := bbase (se 3 (by rfl) ⟨477281, by rfl⟩ : syracuseStep 2545501 = 954563) (by norm_num)
theorem B3217325 : Blo 1338988 3217325 := bbase (se 3 (by rfl) ⟨603248, by rfl⟩ : syracuseStep 3217325 = 1206497) (by norm_num)
theorem B1431469 : Blo 1338988 1431469 := bbase (se 3 (by rfl) ⟨268400, by rfl⟩ : syracuseStep 1431469 = 536801) (by norm_num)
theorem B8148917 : Blo 1338988 8148917 := bbase (se 5 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 8148917 = 763961) (by norm_num)
theorem B5085125 : Blo 1338988 5085125 := bbase (se 4 (by rfl) ⟨476730, by rfl⟩ : syracuseStep 5085125 = 953461) (by norm_num)
theorem B2545661 : Blo 1338988 2545661 := bbase (se 3 (by rfl) ⟨477311, by rfl⟩ : syracuseStep 2545661 = 954623) (by norm_num)
theorem B8149013 : Blo 1338988 8149013 := bbase (se 6 (by rfl) ⟨190992, by rfl⟩ : syracuseStep 8149013 = 381985) (by norm_num)
theorem B17414165 : Blo 1338988 17414165 := bbase (se 6 (by rfl) ⟨408144, by rfl⟩ : syracuseStep 17414165 = 816289) (by norm_num)
theorem B3389485 : Blo 1338988 3389485 := bbase (se 3 (by rfl) ⟨635528, by rfl⟩ : syracuseStep 3389485 = 1271057) (by norm_num)
theorem B4520069 : Blo 1338988 4520069 := bbase (se 4 (by rfl) ⟨423756, by rfl⟩ : syracuseStep 4520069 = 847513) (by norm_num)
theorem B3012749 : Blo 1338988 3012749 := bbase (se 3 (by rfl) ⟨564890, by rfl⟩ : syracuseStep 3012749 = 1129781) (by norm_num)
theorem B3389597 : Blo 1338988 3389597 := bbase (se 3 (by rfl) ⟨635549, by rfl⟩ : syracuseStep 3389597 = 1271099) (by norm_num)
theorem B3012821 : Blo 1338988 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B5085413 : Blo 1338988 5085413 := bbase (se 4 (by rfl) ⟨476757, by rfl⟩ : syracuseStep 5085413 = 953515) (by norm_num)
theorem B6781157 : Blo 1338988 6781157 := bbase (se 4 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 6781157 = 1271467) (by norm_num)
theorem B3012893 : Blo 1338988 3012893 := bbase (se 3 (by rfl) ⟨564917, by rfl⟩ : syracuseStep 3012893 = 1129835) (by norm_num)
theorem B1743193 : Blo 1338988 1743193 := bbase (se 2 (by rfl) ⟨653697, by rfl⟩ : syracuseStep 1743193 = 1307395) (by norm_num)
theorem B3389789 : Blo 1338988 3389789 := bbase (se 3 (by rfl) ⟨635585, by rfl⟩ : syracuseStep 3389789 = 1271171) (by norm_num)
theorem B3012965 : Blo 1338988 3012965 := bbase (se 4 (by rfl) ⟨282465, by rfl⟩ : syracuseStep 3012965 = 564931) (by norm_num)
theorem B1358185 : Blo 1338988 1358185 := bbase (se 2 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 1358185 = 1018639) (by norm_num)
theorem B1431913 : Blo 1338988 1431913 := bbase (se 2 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 1431913 = 1073935) (by norm_num)
theorem B3013037 : Blo 1338988 3013037 := bbase (se 3 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 3013037 = 1129889) (by norm_num)
theorem B4290997 : Blo 1338988 4290997 := bbase (se 5 (by rfl) ⟨201140, by rfl⟩ : syracuseStep 4290997 = 402281) (by norm_num)
theorem B3013109 : Blo 1338988 3013109 := bbase (se 5 (by rfl) ⟨141239, by rfl⟩ : syracuseStep 3013109 = 282479) (by norm_num)
theorem B4520501 : Blo 1338988 4520501 := bbase (se 5 (by rfl) ⟨211898, by rfl⟩ : syracuseStep 4520501 = 423797) (by norm_num)
theorem B3013181 : Blo 1338988 3013181 := bbase (se 3 (by rfl) ⟨564971, by rfl⟩ : syracuseStep 3013181 = 1129943) (by norm_num)
theorem B2259589 : Blo 1338988 2259589 := bbase (se 4 (by rfl) ⟨211836, by rfl⟩ : syracuseStep 2259589 = 423673) (by norm_num)
theorem B3013253 : Blo 1338988 3013253 := bbase (se 4 (by rfl) ⟨282492, by rfl⟩ : syracuseStep 3013253 = 564985) (by norm_num)
theorem B3054229 : Blo 1338988 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B3390133 : Blo 1338988 3390133 := bbase (se 5 (by rfl) ⟨158912, by rfl⟩ : syracuseStep 3390133 = 317825) (by norm_num)
theorem B3013325 : Blo 1338988 3013325 := bbase (se 3 (by rfl) ⟨564998, by rfl⟩ : syracuseStep 3013325 = 1129997) (by norm_num)
theorem B8583893 : Blo 1338988 8583893 := bbase (se 7 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 8583893 = 201185) (by norm_num)
theorem B2259677 : Blo 1338988 2259677 := bbase (se 3 (by rfl) ⟨423689, by rfl⟩ : syracuseStep 2259677 = 847379) (by norm_num)
theorem B3013397 : Blo 1338988 3013397 := bbase (se 6 (by rfl) ⟨70626, by rfl⟩ : syracuseStep 3013397 = 141253) (by norm_num)
theorem B3390245 : Blo 1338988 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B2259805 : Blo 1338988 2259805 := bbase (se 3 (by rfl) ⟨423713, by rfl⟩ : syracuseStep 2259805 = 847427) (by norm_num)
theorem B3013469 : Blo 1338988 3013469 := bbase (se 3 (by rfl) ⟨565025, by rfl⟩ : syracuseStep 3013469 = 1130051) (by norm_num)
theorem B3013541 : Blo 1338988 3013541 := bbase (se 4 (by rfl) ⟨282519, by rfl⟩ : syracuseStep 3013541 = 565039) (by norm_num)
theorem B2259893 : Blo 1338988 2259893 := bbase (se 5 (by rfl) ⟨105932, by rfl⟩ : syracuseStep 2259893 = 211865) (by norm_num)
theorem B1694677 : Blo 1338988 1694677 := bbase (se 7 (by rfl) ⟨19859, by rfl⟩ : syracuseStep 1694677 = 39719) (by norm_num)
theorem B27884501 : Blo 1338988 27884501 := bbase (se 7 (by rfl) ⟨326771, by rfl⟩ : syracuseStep 27884501 = 653543) (by norm_num)
theorem B3390437 : Blo 1338988 3390437 := bbase (se 4 (by rfl) ⟨317853, by rfl⟩ : syracuseStep 3390437 = 635707) (by norm_num)
theorem B4520933 : Blo 1338988 4520933 := bbase (se 4 (by rfl) ⟨423837, by rfl⟩ : syracuseStep 4520933 = 847675) (by norm_num)
theorem B3013613 : Blo 1338988 3013613 := bbase (se 3 (by rfl) ⟨565052, by rfl⟩ : syracuseStep 3013613 = 1130105) (by norm_num)
theorem B1719281 : Blo 1338988 1719281 := bbase (se 2 (by rfl) ⟨644730, by rfl⟩ : syracuseStep 1719281 = 1289461) (by norm_num)
theorem B4832245 : Blo 1338988 4832245 := bbase (se 5 (by rfl) ⟨226511, by rfl⟩ : syracuseStep 4832245 = 453023) (by norm_num)
theorem B1907725 : Blo 1338988 1907725 := bbase (se 3 (by rfl) ⟨357698, by rfl⟩ : syracuseStep 1907725 = 715397) (by norm_num)
theorem B1694773 : Blo 1338988 1694773 := bbase (se 5 (by rfl) ⟨79442, by rfl⟩ : syracuseStep 1694773 = 158885) (by norm_num)
theorem B2260021 : Blo 1338988 2260021 := bbase (se 5 (by rfl) ⟨105938, by rfl⟩ : syracuseStep 2260021 = 211877) (by norm_num)
theorem B3013685 : Blo 1338988 3013685 := bbase (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) (by norm_num)
theorem B1506397 : Blo 1338988 1506397 := bbase (se 3 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 1506397 = 564899) (by norm_num)
theorem B2899037 : Blo 1338988 2899037 := bbase (se 3 (by rfl) ⟨543569, by rfl⟩ : syracuseStep 2899037 = 1087139) (by norm_num)
theorem B3013757 : Blo 1338988 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B1506433 : Blo 1338988 1506433 := bbase (se 2 (by rfl) ⟨564912, by rfl⟩ : syracuseStep 1506433 = 1129825) (by norm_num)
theorem B2292869 : Blo 1338988 2292869 := bbase (se 4 (by rfl) ⟨214956, by rfl⟩ : syracuseStep 2292869 = 429913) (by norm_num)
theorem B2260109 : Blo 1338988 2260109 := bbase (se 3 (by rfl) ⟨423770, by rfl⟩ : syracuseStep 2260109 = 847541) (by norm_num)
theorem B1506469 : Blo 1338988 1506469 := bbase (se 4 (by rfl) ⟨141231, by rfl⟩ : syracuseStep 1506469 = 282463) (by norm_num)
theorem B1359013 : Blo 1338988 1359013 := bbase (se 4 (by rfl) ⟨127407, by rfl⟩ : syracuseStep 1359013 = 254815) (by norm_num)
theorem B1359037 : Blo 1338988 1359037 := bbase (se 3 (by rfl) ⟨254819, by rfl⟩ : syracuseStep 1359037 = 509639) (by norm_num)
theorem B3013829 : Blo 1338988 3013829 := bbase (se 4 (by rfl) ⟨282546, by rfl⟩ : syracuseStep 3013829 = 565093) (by norm_num)
theorem B1506505 : Blo 1338988 1506505 := bbase (se 2 (by rfl) ⟨564939, by rfl⟩ : syracuseStep 1506505 = 1129879) (by norm_num)
theorem B15260885 : Blo 1338988 15260885 := bbase (se 7 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 15260885 = 357677) (by norm_num)
theorem B1694945 : Blo 1338988 1694945 := bbase (se 2 (by rfl) ⟨635604, by rfl⟩ : syracuseStep 1694945 = 1271209) (by norm_num)
theorem B1506541 : Blo 1338988 1506541 := bbase (se 3 (by rfl) ⟨282476, by rfl⟩ : syracuseStep 1506541 = 564953) (by norm_num)
theorem B2260237 : Blo 1338988 2260237 := bbase (se 3 (by rfl) ⟨423794, by rfl⟩ : syracuseStep 2260237 = 847589) (by norm_num)
theorem B3013901 : Blo 1338988 3013901 := bbase (se 3 (by rfl) ⟨565106, by rfl⟩ : syracuseStep 3013901 = 1130213) (by norm_num)
theorem B1506577 : Blo 1338988 1506577 := bbase (se 2 (by rfl) ⟨564966, by rfl⟩ : syracuseStep 1506577 = 1129933) (by norm_num)
theorem B11443477 : Blo 1338988 11443477 := bbase (se 6 (by rfl) ⟨268206, by rfl⟩ : syracuseStep 11443477 = 536413) (by norm_num)
theorem B1695001 : Blo 1338988 1695001 := bbase (se 2 (by rfl) ⟨635625, by rfl⟩ : syracuseStep 1695001 = 1271251) (by norm_num)
theorem B1506613 : Blo 1338988 1506613 := bbase (se 5 (by rfl) ⟨70622, by rfl⟩ : syracuseStep 1506613 = 141245) (by norm_num)
theorem B3390781 : Blo 1338988 3390781 := bbase (se 3 (by rfl) ⟨635771, by rfl⟩ : syracuseStep 3390781 = 1271543) (by norm_num)
theorem B3439949 : Blo 1338988 3439949 := bbase (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) (by norm_num)
theorem B3013973 : Blo 1338988 3013973 := bbase (se 11 (by rfl) ⟨2207, by rfl⟩ : syracuseStep 3013973 = 4415) (by norm_num)
theorem B1506649 : Blo 1338988 1506649 := bbase (se 2 (by rfl) ⟨564993, by rfl⟩ : syracuseStep 1506649 = 1129987) (by norm_num)
theorem B2260325 : Blo 1338988 2260325 := bbase (se 4 (by rfl) ⟨211905, by rfl⟩ : syracuseStep 2260325 = 423811) (by norm_num)
theorem B1695097 : Blo 1338988 1695097 := bbase (se 2 (by rfl) ⟨635661, by rfl⟩ : syracuseStep 1695097 = 1271323) (by norm_num)
theorem B1506685 : Blo 1338988 1506685 := bbase (se 3 (by rfl) ⟨282503, by rfl⟩ : syracuseStep 1506685 = 565007) (by norm_num)
theorem B5086597 : Blo 1338988 5086597 := bbase (se 4 (by rfl) ⟨476868, by rfl⟩ : syracuseStep 5086597 = 953737) (by norm_num)
theorem B4521365 : Blo 1338988 4521365 := bbase (se 6 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 4521365 = 211939) (by norm_num)
theorem B3014045 : Blo 1338988 3014045 := bbase (se 3 (by rfl) ⟨565133, by rfl⟩ : syracuseStep 3014045 = 1130267) (by norm_num)
theorem B1506721 : Blo 1338988 1506721 := bbase (se 2 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 1506721 = 1130041) (by norm_num)
theorem B3390893 : Blo 1338988 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B1506757 : Blo 1338988 1506757 := bbase (se 4 (by rfl) ⟨141258, by rfl⟩ : syracuseStep 1506757 = 282517) (by norm_num)
theorem B6438341 : Blo 1338988 6438341 := bbase (se 4 (by rfl) ⟨603594, by rfl⟩ : syracuseStep 6438341 = 1207189) (by norm_num)
theorem B2260453 : Blo 1338988 2260453 := bbase (se 4 (by rfl) ⟨211917, by rfl⟩ : syracuseStep 2260453 = 423835) (by norm_num)
theorem B3014117 : Blo 1338988 3014117 := bbase (se 4 (by rfl) ⟨282573, by rfl⟩ : syracuseStep 3014117 = 565147) (by norm_num)
theorem B1506793 : Blo 1338988 1506793 := bbase (se 2 (by rfl) ⟨565047, by rfl⟩ : syracuseStep 1506793 = 1130095) (by norm_num)
theorem B2145781 : Blo 1338988 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B6782453 : Blo 1338988 6782453 := bbase (se 5 (by rfl) ⟨317927, by rfl⟩ : syracuseStep 6782453 = 635855) (by norm_num)
theorem B1506829 : Blo 1338988 1506829 := bbase (se 3 (by rfl) ⟨282530, by rfl⟩ : syracuseStep 1506829 = 565061) (by norm_num)
theorem B3055133 : Blo 1338988 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B1695269 : Blo 1338988 1695269 := bbase (se 4 (by rfl) ⟨158931, by rfl⟩ : syracuseStep 1695269 = 317863) (by norm_num)
theorem B3014189 : Blo 1338988 3014189 := bbase (se 3 (by rfl) ⟨565160, by rfl⟩ : syracuseStep 3014189 = 1130321) (by norm_num)
theorem B1506865 : Blo 1338988 1506865 := bbase (se 2 (by rfl) ⟨565074, by rfl⟩ : syracuseStep 1506865 = 1130149) (by norm_num)
theorem B2260541 : Blo 1338988 2260541 := bbase (se 3 (by rfl) ⟨423851, by rfl⟩ : syracuseStep 2260541 = 847703) (by norm_num)
theorem B1506901 : Blo 1338988 1506901 := bbase (se 8 (by rfl) ⟨8829, by rfl⟩ : syracuseStep 1506901 = 17659) (by norm_num)
theorem B1695325 : Blo 1338988 1695325 := bbase (se 3 (by rfl) ⟨317873, by rfl⟩ : syracuseStep 1695325 = 635747) (by norm_num)
theorem B1908317 : Blo 1338988 1908317 := bbase (se 3 (by rfl) ⟨357809, by rfl⟩ : syracuseStep 1908317 = 715619) (by norm_num)
theorem B3391085 : Blo 1338988 3391085 := bbase (se 3 (by rfl) ⟨635828, by rfl⟩ : syracuseStep 3391085 = 1271657) (by norm_num)
theorem B6872693 : Blo 1338988 6872693 := bbase (se 5 (by rfl) ⟨322157, by rfl⟩ : syracuseStep 6872693 = 644315) (by norm_num)
theorem B3014261 : Blo 1338988 3014261 := bbase (se 5 (by rfl) ⟨141293, by rfl⟩ : syracuseStep 3014261 = 282587) (by norm_num)
theorem B1506937 : Blo 1338988 1506937 := bbase (se 2 (by rfl) ⟨565101, by rfl⟩ : syracuseStep 1506937 = 1130203) (by norm_num)
theorem B1506973 : Blo 1338988 1506973 := bbase (se 3 (by rfl) ⟨282557, by rfl⟩ : syracuseStep 1506973 = 565115) (by norm_num)
theorem B1908397 : Blo 1338988 1908397 := bbase (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) (by norm_num)
theorem B12385973 : Blo 1338988 12385973 := bbase (se 5 (by rfl) ⟨580592, by rfl⟩ : syracuseStep 12385973 = 1161185) (by norm_num)
theorem B5086901 : Blo 1338988 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B1695421 : Blo 1338988 1695421 := bbase (se 3 (by rfl) ⟨317891, by rfl⟩ : syracuseStep 1695421 = 635783) (by norm_num)
theorem B2260669 : Blo 1338988 2260669 := bbase (se 3 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 2260669 = 847751) (by norm_num)
theorem B3014333 : Blo 1338988 3014333 := bbase (se 3 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 3014333 = 1130375) (by norm_num)
theorem B1507009 : Blo 1338988 1507009 := bbase (se 2 (by rfl) ⟨565128, by rfl⟩ : syracuseStep 1507009 = 1130257) (by norm_num)
theorem B1507045 : Blo 1338988 1507045 := bbase (se 4 (by rfl) ⟨141285, by rfl⟩ : syracuseStep 1507045 = 282571) (by norm_num)
theorem B3014405 : Blo 1338988 3014405 := bbase (se 4 (by rfl) ⟨282600, by rfl⟩ : syracuseStep 3014405 = 565201) (by norm_num)
theorem B1507081 : Blo 1338988 1507081 := bbase (se 2 (by rfl) ⟨565155, by rfl⟩ : syracuseStep 1507081 = 1130311) (by norm_num)
theorem B2260757 : Blo 1338988 2260757 := bbase (se 6 (by rfl) ⟨52986, by rfl⟩ : syracuseStep 2260757 = 105973) (by norm_num)
theorem B1908517 : Blo 1338988 1908517 := bbase (se 4 (by rfl) ⟨178923, by rfl⟩ : syracuseStep 1908517 = 357847) (by norm_num)
theorem B1507117 : Blo 1338988 1507117 := bbase (se 3 (by rfl) ⟨282584, by rfl⟩ : syracuseStep 1507117 = 565169) (by norm_num)
theorem B4521797 : Blo 1338988 4521797 := bbase (se 4 (by rfl) ⟨423918, by rfl⟩ : syracuseStep 4521797 = 847837) (by norm_num)
theorem B3014477 : Blo 1338988 3014477 := bbase (se 3 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 3014477 = 1130429) (by norm_num)
theorem B1507153 : Blo 1338988 1507153 := bbase (se 2 (by rfl) ⟨565182, by rfl⟩ : syracuseStep 1507153 = 1130365) (by norm_num)
theorem B3620693 : Blo 1338988 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B3055445 : Blo 1338988 3055445 := bbase (se 9 (by rfl) ⟨8951, by rfl⟩ : syracuseStep 3055445 = 17903) (by norm_num)
theorem B1695593 : Blo 1338988 1695593 := bbase (se 2 (by rfl) ⟨635847, by rfl⟩ : syracuseStep 1695593 = 1271695) (by norm_num)
theorem B1507189 : Blo 1338988 1507189 := bbase (se 5 (by rfl) ⟨70649, by rfl⟩ : syracuseStep 1507189 = 141299) (by norm_num)
theorem B1908613 : Blo 1338988 1908613 := bbase (se 4 (by rfl) ⟨178932, by rfl⟩ : syracuseStep 1908613 = 357865) (by norm_num)
theorem B2260885 : Blo 1338988 2260885 := bbase (se 6 (by rfl) ⟨52989, by rfl⟩ : syracuseStep 2260885 = 105979) (by norm_num)
theorem B3014549 : Blo 1338988 3014549 := bbase (se 6 (by rfl) ⟨70653, by rfl⟩ : syracuseStep 3014549 = 141307) (by norm_num)
theorem B1507225 : Blo 1338988 1507225 := bbase (se 2 (by rfl) ⟨565209, by rfl⟩ : syracuseStep 1507225 = 1130419) (by norm_num)
theorem B1695649 : Blo 1338988 1695649 := bbase (se 2 (by rfl) ⟨635868, by rfl⟩ : syracuseStep 1695649 = 1271737) (by norm_num)
theorem B1507261 : Blo 1338988 1507261 := bbase (se 3 (by rfl) ⟨282611, by rfl⟩ : syracuseStep 1507261 = 565223) (by norm_num)
theorem B3391429 : Blo 1338988 3391429 := bbase (se 4 (by rfl) ⟨317946, by rfl⟩ : syracuseStep 3391429 = 635893) (by norm_num)
theorem B3014621 : Blo 1338988 3014621 := bbase (se 3 (by rfl) ⟨565241, by rfl⟩ : syracuseStep 3014621 = 1130483) (by norm_num)
theorem B1507297 : Blo 1338988 1507297 := bbase (se 2 (by rfl) ⟨565236, by rfl⟩ : syracuseStep 1507297 = 1130473) (by norm_num)
theorem B2260973 : Blo 1338988 2260973 := bbase (se 3 (by rfl) ⟨423932, by rfl⟩ : syracuseStep 2260973 = 847865) (by norm_num)
theorem B2260993 : Blo 1338988 2260993 := bstep (se 2 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 2260993 = 1695745) B1695745
theorem B3817489 : Blo 1338988 3817489 := bstep (se 2 (by rfl) ⟨1431558, by rfl⟩ : syracuseStep 3817489 = 2863117) B2863117
theorem B5505059 : Blo 1338988 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B2261027 : Blo 1338988 2261027 := bstep (se 1 (by rfl) ⟨1695770, by rfl⟩ : syracuseStep 2261027 = 3391541) B3391541
theorem B1695811 : Blo 1338988 1695811 := bstep (se 1 (by rfl) ⟨1271858, by rfl⟩ : syracuseStep 1695811 = 2543717) B2543717
theorem B5726285 : Blo 1338988 5726285 := bstep (se 3 (by rfl) ⟨1073678, by rfl⟩ : syracuseStep 5726285 = 2147357) B2147357
theorem B4292689 : Blo 1338988 4292689 := bstep (se 2 (by rfl) ⟨1609758, by rfl⟩ : syracuseStep 4292689 = 3219517) B3219517
theorem B3620963 : Blo 1338988 3620963 := bstep (se 1 (by rfl) ⟨2715722, by rfl⟩ : syracuseStep 3620963 = 5431445) B5431445
theorem B3670147 : Blo 1338988 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B1507459 : Blo 1338988 1507459 := bstep (se 1 (by rfl) ⟨1130594, by rfl⟩ : syracuseStep 1507459 = 2261189) B2261189
theorem B3014801 : Blo 1338988 3014801 := bstep (se 2 (by rfl) ⟨1130550, by rfl⟩ : syracuseStep 3014801 = 2261101) B2261101
theorem B3014819 : Blo 1338988 3014819 := bstep (se 1 (by rfl) ⟨2261114, by rfl⟩ : syracuseStep 3014819 = 4522229) B4522229
theorem B2261155 : Blo 1338988 2261155 := bstep (se 1 (by rfl) ⟨1695866, by rfl⟩ : syracuseStep 2261155 = 3391733) B3391733
theorem B1695907 : Blo 1338988 1695907 := bstep (se 1 (by rfl) ⟨1271930, by rfl⟩ : syracuseStep 1695907 = 2543861) B2543861
theorem B1507603 : Blo 1338988 1507603 := bstep (se 1 (by rfl) ⟨1130702, by rfl⟩ : syracuseStep 1507603 = 2261405) B2261405
theorem B3817763 : Blo 1338988 3817763 := bstep (se 1 (by rfl) ⟨2863322, by rfl⟩ : syracuseStep 3817763 = 5726645) B5726645
theorem B4350257 : Blo 1338988 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B2261297 : Blo 1338988 2261297 := bstep (se 2 (by rfl) ⟨847986, by rfl⟩ : syracuseStep 2261297 = 1695973) B1695973
theorem B1507747 : Blo 1338988 1507747 := bstep (se 1 (by rfl) ⟨1130810, by rfl⟩ : syracuseStep 1507747 = 2261621) B2261621
theorem B3015089 : Blo 1338988 3015089 := bstep (se 2 (by rfl) ⟨1130658, by rfl⟩ : syracuseStep 3015089 = 2261317) B2261317
theorem B2261425 : Blo 1338988 2261425 := bstep (se 2 (by rfl) ⟨848034, by rfl⟩ : syracuseStep 2261425 = 1696069) B1696069
theorem B3015107 : Blo 1338988 3015107 := bstep (se 1 (by rfl) ⟨2261330, by rfl⟩ : syracuseStep 3015107 = 4522661) B4522661
theorem B4522445 : Blo 1338988 4522445 := bstep (se 3 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 4522445 = 1695917) B1695917
theorem B2261459 : Blo 1338988 2261459 := bstep (se 1 (by rfl) ⟨1696094, by rfl⟩ : syracuseStep 2261459 = 3392189) B3392189
theorem B1810913 : Blo 1338988 1810913 := bstep (se 2 (by rfl) ⟨679092, by rfl⟩ : syracuseStep 1810913 = 1358185) B1358185
theorem B1909217 : Blo 1338988 1909217 := bstep (se 2 (by rfl) ⟨715956, by rfl⟩ : syracuseStep 1909217 = 1431913) B1431913
theorem B3817955 : Blo 1338988 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B4071917 : Blo 1338988 4071917 := bstep (se 3 (by rfl) ⟨763484, by rfl⟩ : syracuseStep 4071917 = 1526969) B1526969
theorem B4522499 : Blo 1338988 4522499 := bstep (se 1 (by rfl) ⟨3391874, by rfl⟩ : syracuseStep 4522499 = 6783749) B6783749
theorem B1507891 : Blo 1338988 1507891 := bstep (se 1 (by rfl) ⟨1130918, by rfl⟩ : syracuseStep 1507891 = 2261837) B2261837
theorem B2261587 : Blo 1338988 2261587 := bstep (se 1 (by rfl) ⟨1696190, by rfl⟩ : syracuseStep 2261587 = 3392381) B3392381
theorem B6783587 : Blo 1338988 6783587 := bstep (se 1 (by rfl) ⟨5087690, by rfl⟩ : syracuseStep 6783587 = 10175381) B10175381
theorem B5087843 : Blo 1338988 5087843 := bstep (se 1 (by rfl) ⟨3815882, by rfl⟩ : syracuseStep 5087843 = 7631765) B7631765
theorem B1696403 : Blo 1338988 1696403 := bstep (se 1 (by rfl) ⟨1272302, by rfl⟩ : syracuseStep 1696403 = 2544605) B2544605
theorem B1508035 : Blo 1338988 1508035 := bstep (se 1 (by rfl) ⟨1131026, by rfl⟩ : syracuseStep 1508035 = 2262053) B2262053
theorem B3015377 : Blo 1338988 3015377 := bstep (se 2 (by rfl) ⟨1130766, by rfl⟩ : syracuseStep 3015377 = 2261533) B2261533
theorem B2261729 : Blo 1338988 2261729 := bstep (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) B1696297
theorem B3015395 : Blo 1338988 3015395 := bstep (se 1 (by rfl) ⟨2261546, by rfl⟩ : syracuseStep 3015395 = 4523093) B4523093
theorem B4522769 : Blo 1338988 4522769 := bstep (se 2 (by rfl) ⟨1696038, by rfl⟩ : syracuseStep 4522769 = 3392077) B3392077
theorem B1508179 : Blo 1338988 1508179 := bstep (se 1 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 1508179 = 2262269) B2262269
theorem B2261857 : Blo 1338988 2261857 := bstep (se 2 (by rfl) ⟨848196, by rfl⟩ : syracuseStep 2261857 = 1696393) B1696393
theorem B3621763 : Blo 1338988 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B2261891 : Blo 1338988 2261891 := bstep (se 1 (by rfl) ⟨1696418, by rfl⟩ : syracuseStep 2261891 = 3392837) B3392837
theorem B14484365 : Blo 1338988 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B3392401 : Blo 1338988 3392401 := bstep (se 2 (by rfl) ⟨1272150, by rfl⟩ : syracuseStep 3392401 = 2544301) B2544301
theorem B2147267 : Blo 1338988 2147267 := bstep (se 1 (by rfl) ⟨1610450, by rfl⟩ : syracuseStep 2147267 = 3220901) B3220901
theorem B1508323 : Blo 1338988 1508323 := bstep (se 1 (by rfl) ⟨1131242, by rfl⟩ : syracuseStep 1508323 = 2262485) B2262485
theorem B12878833 : Blo 1338988 12878833 := bstep (se 2 (by rfl) ⟨4829562, by rfl⟩ : syracuseStep 12878833 = 9659125) B9659125
theorem B3015665 : Blo 1338988 3015665 := bstep (se 2 (by rfl) ⟨1130874, by rfl⟩ : syracuseStep 3015665 = 2261749) B2261749
theorem B3015683 : Blo 1338988 3015683 := bstep (se 1 (by rfl) ⟨2261762, by rfl⟩ : syracuseStep 3015683 = 4523525) B4523525
theorem B2262019 : Blo 1338988 2262019 := bstep (se 1 (by rfl) ⟨1696514, by rfl⟩ : syracuseStep 2262019 = 3393029) B3393029
theorem B3621905 : Blo 1338988 3621905 := bstep (se 2 (by rfl) ⟨1358214, by rfl⟩ : syracuseStep 3621905 = 2716429) B2716429
theorem B17409077 : Blo 1338988 17409077 := bstep (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) B1632101
theorem B34366517 : Blo 1338988 34366517 := bstep (se 5 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 34366517 = 3221861) B3221861
theorem B2147395 : Blo 1338988 2147395 := bstep (se 1 (by rfl) ⟨1610546, by rfl⟩ : syracuseStep 2147395 = 3221093) B3221093
theorem B8815729 : Blo 1338988 8815729 := bstep (se 2 (by rfl) ⟨3305898, by rfl⟩ : syracuseStep 8815729 = 6611797) B6611797
theorem B1508467 : Blo 1338988 1508467 := bstep (se 1 (by rfl) ⟨1131350, by rfl⟩ : syracuseStep 1508467 = 2262701) B2262701
theorem B2262161 : Blo 1338988 2262161 := bstep (se 2 (by rfl) ⟨848310, by rfl⟩ : syracuseStep 2262161 = 1696621) B1696621
theorem B3392675 : Blo 1338988 3392675 := bstep (se 1 (by rfl) ⟨2544506, by rfl⟩ : syracuseStep 3392675 = 5089013) B5089013
theorem B2901187 : Blo 1338988 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B1508611 : Blo 1338988 1508611 := bstep (se 1 (by rfl) ⟨1131458, by rfl⟩ : syracuseStep 1508611 = 2262917) B2262917
theorem B3015953 : Blo 1338988 3015953 := bstep (se 2 (by rfl) ⟨1130982, by rfl⟩ : syracuseStep 3015953 = 2261965) B2261965
theorem B2262289 : Blo 1338988 2262289 := bstep (se 2 (by rfl) ⟨848358, by rfl⟩ : syracuseStep 2262289 = 1696717) B1696717
theorem B5432611 : Blo 1338988 5432611 := bstep (se 1 (by rfl) ⟨4074458, by rfl⟩ : syracuseStep 5432611 = 8148917) B8148917
theorem B6112547 : Blo 1338988 6112547 := bstep (se 1 (by rfl) ⟨4584410, by rfl⟩ : syracuseStep 6112547 = 9168821) B9168821
theorem B3015971 : Blo 1338988 3015971 := bstep (se 1 (by rfl) ⟨2261978, by rfl⟩ : syracuseStep 3015971 = 4523957) B4523957
theorem B4523309 : Blo 1338988 4523309 := bstep (se 3 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 4523309 = 1696241) B1696241
theorem B2262323 : Blo 1338988 2262323 := bstep (se 1 (by rfl) ⟨1696742, by rfl⟩ : syracuseStep 2262323 = 3393485) B3393485
theorem B8152397 : Blo 1338988 8152397 := bstep (se 3 (by rfl) ⟨1528574, by rfl⟩ : syracuseStep 8152397 = 3057149) B3057149
theorem B1697107 : Blo 1338988 1697107 := bstep (se 1 (by rfl) ⟨1272830, by rfl⟩ : syracuseStep 1697107 = 2545661) B2545661
theorem B5432675 : Blo 1338988 5432675 := bstep (se 1 (by rfl) ⟨4074506, by rfl⟩ : syracuseStep 5432675 = 8149013) B8149013
theorem B4523363 : Blo 1338988 4523363 := bstep (se 1 (by rfl) ⟨3392522, by rfl⟩ : syracuseStep 4523363 = 6785045) B6785045
theorem B3392867 : Blo 1338988 3392867 := bstep (se 1 (by rfl) ⟨2544650, by rfl⟩ : syracuseStep 3392867 = 5089301) B5089301
theorem B11609443 : Blo 1338988 11609443 := bstep (se 1 (by rfl) ⟨8707082, by rfl⟩ : syracuseStep 11609443 = 17414165) B17414165
theorem B7628165 : Blo 1338988 7628165 := bstep (se 4 (by rfl) ⟨715140, by rfl⟩ : syracuseStep 7628165 = 1430281) B1430281
theorem B6784397 : Blo 1338988 6784397 := bstep (se 3 (by rfl) ⟨1272074, by rfl⟩ : syracuseStep 6784397 = 2544149) B2544149
theorem B2008499 : Blo 1338988 2008499 := bstep (se 1 (by rfl) ⟨1506374, by rfl⟩ : syracuseStep 2008499 = 3012749) B3012749
theorem B2262451 : Blo 1338988 2262451 := bstep (se 1 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 2262451 = 3393677) B3393677
theorem B35308997 : Blo 1338988 35308997 := bstep (se 4 (by rfl) ⟨3310218, by rfl⟩ : syracuseStep 35308997 = 6620437) B6620437
theorem B2008529 : Blo 1338988 2008529 := bstep (se 2 (by rfl) ⟨753198, by rfl⟩ : syracuseStep 2008529 = 1506397) B1506397
theorem B2008547 : Blo 1338988 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B2008577 : Blo 1338988 2008577 := bstep (se 2 (by rfl) ⟨753216, by rfl⟩ : syracuseStep 2008577 = 1506433) B1506433
theorem B15255053 : Blo 1338988 15255053 := bstep (se 3 (by rfl) ⟨2860322, by rfl⟩ : syracuseStep 15255053 = 5720645) B5720645
theorem B2008595 : Blo 1338988 2008595 := bstep (se 1 (by rfl) ⟨1506446, by rfl⟩ : syracuseStep 2008595 = 3012893) B3012893
theorem B1959457 : Blo 1338988 1959457 := bstep (se 2 (by rfl) ⟨734796, by rfl⟩ : syracuseStep 1959457 = 1469593) B1469593
theorem B2008625 : Blo 1338988 2008625 := bstep (se 2 (by rfl) ⟨753234, by rfl⟩ : syracuseStep 2008625 = 1506469) B1506469
theorem B3016241 : Blo 1338988 3016241 := bstep (se 2 (by rfl) ⟨1131090, by rfl⟩ : syracuseStep 3016241 = 2262181) B2262181
theorem B1812017 : Blo 1338988 1812017 := bstep (se 2 (by rfl) ⟨679506, by rfl⟩ : syracuseStep 1812017 = 1359013) B1359013
theorem B2262593 : Blo 1338988 2262593 := bstep (se 2 (by rfl) ⟨848472, by rfl⟩ : syracuseStep 2262593 = 1696945) B1696945
theorem B2008643 : Blo 1338988 2008643 := bstep (se 1 (by rfl) ⟨1506482, by rfl⟩ : syracuseStep 2008643 = 3012965) B3012965
theorem B3016259 : Blo 1338988 3016259 := bstep (se 1 (by rfl) ⟨2262194, by rfl⟩ : syracuseStep 3016259 = 4524389) B4524389
theorem B5088845 : Blo 1338988 5088845 := bstep (se 3 (by rfl) ⟨954158, by rfl⟩ : syracuseStep 5088845 = 1908317) B1908317
theorem B2008673 : Blo 1338988 2008673 := bstep (se 2 (by rfl) ⟨753252, by rfl⟩ : syracuseStep 2008673 = 1506505) B1506505
theorem B4523633 : Blo 1338988 4523633 := bstep (se 2 (by rfl) ⟨1696362, by rfl⟩ : syracuseStep 4523633 = 3392725) B3392725
theorem B2147953 : Blo 1338988 2147953 := bstep (se 2 (by rfl) ⟨805482, by rfl⟩ : syracuseStep 2147953 = 1610965) B1610965
theorem B2008691 : Blo 1338988 2008691 := bstep (se 1 (by rfl) ⟨1506518, by rfl⟩ : syracuseStep 2008691 = 3013037) B3013037
theorem B18327181 : Blo 1338988 18327181 := bstep (se 3 (by rfl) ⟨3436346, by rfl⟩ : syracuseStep 18327181 = 6872693) B6872693
theorem B2008721 : Blo 1338988 2008721 := bstep (se 2 (by rfl) ⟨753270, by rfl⟩ : syracuseStep 2008721 = 1506541) B1506541
theorem B2008739 : Blo 1338988 2008739 := bstep (se 1 (by rfl) ⟨1506554, by rfl⟩ : syracuseStep 2008739 = 3013109) B3013109
theorem B2008769 : Blo 1338988 2008769 := bstep (se 2 (by rfl) ⟨753288, by rfl⟩ : syracuseStep 2008769 = 1506577) B1506577
theorem B2262721 : Blo 1338988 2262721 := bstep (se 2 (by rfl) ⟨848520, by rfl⟩ : syracuseStep 2262721 = 1697041) B1697041
theorem B2008787 : Blo 1338988 2008787 := bstep (se 1 (by rfl) ⟨1506590, by rfl⟩ : syracuseStep 2008787 = 3013181) B3013181
theorem B2262755 : Blo 1338988 2262755 := bstep (se 1 (by rfl) ⟨1697066, by rfl⟩ : syracuseStep 2262755 = 3394133) B3394133
theorem B2008817 : Blo 1338988 2008817 := bstep (se 2 (by rfl) ⟨753306, by rfl⟩ : syracuseStep 2008817 = 1506613) B1506613
theorem B2008835 : Blo 1338988 2008835 := bstep (se 1 (by rfl) ⟨1506626, by rfl⟩ : syracuseStep 2008835 = 3013253) B3013253
theorem B2008865 : Blo 1338988 2008865 := bstep (se 2 (by rfl) ⟨753324, by rfl⟩ : syracuseStep 2008865 = 1506649) B1506649
theorem B2008883 : Blo 1338988 2008883 := bstep (se 1 (by rfl) ⟨1506662, by rfl⟩ : syracuseStep 2008883 = 3013325) B3013325
theorem B2008913 : Blo 1338988 2008913 := bstep (se 2 (by rfl) ⟨753342, by rfl⟩ : syracuseStep 2008913 = 1506685) B1506685
theorem B2901841 : Blo 1338988 2901841 := bstep (se 2 (by rfl) ⟨1088190, by rfl⟩ : syracuseStep 2901841 = 2176381) B2176381
theorem B3016529 : Blo 1338988 3016529 := bstep (se 2 (by rfl) ⟨1131198, by rfl⟩ : syracuseStep 3016529 = 2262397) B2262397
theorem B2008931 : Blo 1338988 2008931 := bstep (se 1 (by rfl) ⟨1506698, by rfl⟩ : syracuseStep 2008931 = 3013397) B3013397
theorem B3016547 : Blo 1338988 3016547 := bstep (se 1 (by rfl) ⟨2262410, by rfl⟩ : syracuseStep 3016547 = 4524821) B4524821
theorem B2262883 : Blo 1338988 2262883 := bstep (se 1 (by rfl) ⟨1697162, by rfl⟩ : syracuseStep 2262883 = 3394325) B3394325
theorem B2008961 : Blo 1338988 2008961 := bstep (se 2 (by rfl) ⟨753360, by rfl⟩ : syracuseStep 2008961 = 1506721) B1506721
theorem B2008979 : Blo 1338988 2008979 := bstep (se 1 (by rfl) ⟨1506734, by rfl⟩ : syracuseStep 2008979 = 3013469) B3013469
theorem B2009009 : Blo 1338988 2009009 := bstep (se 2 (by rfl) ⟨753378, by rfl⟩ : syracuseStep 2009009 = 1506757) B1506757
theorem B7636913 : Blo 1338988 7636913 := bstep (se 2 (by rfl) ⟨2863842, by rfl⟩ : syracuseStep 7636913 = 5727685) B5727685
theorem B2009027 : Blo 1338988 2009027 := bstep (se 1 (by rfl) ⟨1506770, by rfl⟩ : syracuseStep 2009027 = 3013541) B3013541
theorem B2009057 : Blo 1338988 2009057 := bstep (se 2 (by rfl) ⟨753396, by rfl⟩ : syracuseStep 2009057 = 1506793) B1506793
theorem B18589667 : Blo 1338988 18589667 := bstep (se 1 (by rfl) ⟨13942250, by rfl⟩ : syracuseStep 18589667 = 27884501) B27884501
theorem B2861041 : Blo 1338988 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B2009075 : Blo 1338988 2009075 := bstep (se 1 (by rfl) ⟨1506806, by rfl⟩ : syracuseStep 2009075 = 3013613) B3013613
theorem B2009105 : Blo 1338988 2009105 := bstep (se 2 (by rfl) ⟨753414, by rfl⟩ : syracuseStep 2009105 = 1506829) B1506829
theorem B2009123 : Blo 1338988 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B7628849 : Blo 1338988 7628849 := bstep (se 2 (by rfl) ⟨2860818, by rfl⟩ : syracuseStep 7628849 = 5721637) B5721637
theorem B2009153 : Blo 1338988 2009153 := bstep (se 2 (by rfl) ⟨753432, by rfl⟩ : syracuseStep 2009153 = 1506865) B1506865
theorem B2009171 : Blo 1338988 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B2009201 : Blo 1338988 2009201 := bstep (se 2 (by rfl) ⟨753450, by rfl⟩ : syracuseStep 2009201 = 1506901) B1506901
theorem B3016817 : Blo 1338988 3016817 := bstep (se 2 (by rfl) ⟨1131306, by rfl⟩ : syracuseStep 3016817 = 2262613) B2262613
theorem B2009219 : Blo 1338988 2009219 := bstep (se 1 (by rfl) ⟨1506914, by rfl⟩ : syracuseStep 2009219 = 3013829) B3013829
theorem B3016835 : Blo 1338988 3016835 := bstep (se 1 (by rfl) ⟨2262626, by rfl⟩ : syracuseStep 3016835 = 4525253) B4525253
theorem B4524173 : Blo 1338988 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B2009249 : Blo 1338988 2009249 := bstep (se 2 (by rfl) ⟨753468, by rfl⟩ : syracuseStep 2009249 = 1506937) B1506937
theorem B2009267 : Blo 1338988 2009267 := bstep (se 1 (by rfl) ⟨1506950, by rfl⟩ : syracuseStep 2009267 = 3013901) B3013901
theorem B4524227 : Blo 1338988 4524227 := bstep (se 1 (by rfl) ⟨3393170, by rfl⟩ : syracuseStep 4524227 = 6786341) B6786341
theorem B2009297 : Blo 1338988 2009297 := bstep (se 2 (by rfl) ⟨753486, by rfl⟩ : syracuseStep 2009297 = 1506973) B1506973
theorem B2009315 : Blo 1338988 2009315 := bstep (se 1 (by rfl) ⟨1506986, by rfl⟩ : syracuseStep 2009315 = 3013973) B3013973
theorem B2009345 : Blo 1338988 2009345 := bstep (se 2 (by rfl) ⟨753504, by rfl⟩ : syracuseStep 2009345 = 1507009) B1507009
theorem B3393809 : Blo 1338988 3393809 := bstep (se 2 (by rfl) ⟨1272678, by rfl⟩ : syracuseStep 3393809 = 2545357) B2545357
theorem B2009363 : Blo 1338988 2009363 := bstep (se 1 (by rfl) ⟨1507022, by rfl⟩ : syracuseStep 2009363 = 3014045) B3014045
theorem B2009393 : Blo 1338988 2009393 := bstep (se 2 (by rfl) ⟨753522, by rfl⟩ : syracuseStep 2009393 = 1507045) B1507045
theorem B2009411 : Blo 1338988 2009411 := bstep (se 1 (by rfl) ⟨1507058, by rfl⟩ : syracuseStep 2009411 = 3014117) B3014117
theorem B3393859 : Blo 1338988 3393859 := bstep (se 1 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 3393859 = 5090789) B5090789
theorem B2009441 : Blo 1338988 2009441 := bstep (se 2 (by rfl) ⟨753540, by rfl⟩ : syracuseStep 2009441 = 1507081) B1507081
theorem B2009459 : Blo 1338988 2009459 := bstep (se 1 (by rfl) ⟨1507094, by rfl⟩ : syracuseStep 2009459 = 3014189) B3014189
theorem B2009489 : Blo 1338988 2009489 := bstep (se 2 (by rfl) ⟨753558, by rfl⟩ : syracuseStep 2009489 = 1507117) B1507117
theorem B3017105 : Blo 1338988 3017105 := bstep (se 2 (by rfl) ⟨1131414, by rfl⟩ : syracuseStep 3017105 = 2262829) B2262829
theorem B2009507 : Blo 1338988 2009507 := bstep (se 1 (by rfl) ⟨1507130, by rfl⟩ : syracuseStep 2009507 = 3014261) B3014261
theorem B3017123 : Blo 1338988 3017123 := bstep (se 1 (by rfl) ⟨2262842, by rfl⟩ : syracuseStep 3017123 = 4525685) B4525685
theorem B2009537 : Blo 1338988 2009537 := bstep (se 2 (by rfl) ⟨753576, by rfl⟩ : syracuseStep 2009537 = 1507153) B1507153
theorem B8579533 : Blo 1338988 8579533 := bstep (se 3 (by rfl) ⟨1608662, by rfl⟩ : syracuseStep 8579533 = 3217325) B3217325
theorem B4524497 : Blo 1338988 4524497 := bstep (se 2 (by rfl) ⟨1696686, by rfl⟩ : syracuseStep 4524497 = 3393373) B3393373
theorem B3394001 : Blo 1338988 3394001 := bstep (se 2 (by rfl) ⟨1272750, by rfl⟩ : syracuseStep 3394001 = 2545501) B2545501
theorem B2009555 : Blo 1338988 2009555 := bstep (se 1 (by rfl) ⟨1507166, by rfl⟩ : syracuseStep 2009555 = 3014333) B3014333
theorem B2009585 : Blo 1338988 2009585 := bstep (se 2 (by rfl) ⟨753594, by rfl⟩ : syracuseStep 2009585 = 1507189) B1507189
theorem B2009603 : Blo 1338988 2009603 := bstep (se 1 (by rfl) ⟨1507202, by rfl⟩ : syracuseStep 2009603 = 3014405) B3014405
theorem B2009633 : Blo 1338988 2009633 := bstep (se 2 (by rfl) ⟨753612, by rfl⟩ : syracuseStep 2009633 = 1507225) B1507225
theorem B2009651 : Blo 1338988 2009651 := bstep (se 1 (by rfl) ⟨1507238, by rfl⟩ : syracuseStep 2009651 = 3014477) B3014477
theorem B2009681 : Blo 1338988 2009681 := bstep (se 2 (by rfl) ⟨753630, by rfl⟩ : syracuseStep 2009681 = 1507261) B1507261
theorem B2009699 : Blo 1338988 2009699 := bstep (se 1 (by rfl) ⟨1507274, by rfl⟩ : syracuseStep 2009699 = 3014549) B3014549
theorem B2009729 : Blo 1338988 2009729 := bstep (se 2 (by rfl) ⟨753648, by rfl⟩ : syracuseStep 2009729 = 1507297) B1507297
theorem B2009747 : Blo 1338988 2009747 := bstep (se 1 (by rfl) ⟨1507310, by rfl⟩ : syracuseStep 2009747 = 3014621) B3014621
theorem B8587939 : Blo 1338988 8587939 := bstep (se 1 (by rfl) ⟨6440954, by rfl⟩ : syracuseStep 8587939 = 12881909) B12881909
theorem B2009777 : Blo 1338988 2009777 := bstep (se 2 (by rfl) ⟨753666, by rfl⟩ : syracuseStep 2009777 = 1507333) B1507333
theorem B2009795 : Blo 1338988 2009795 := bstep (se 1 (by rfl) ⟨1507346, by rfl⟩ : syracuseStep 2009795 = 3014693) B3014693
theorem B2009825 : Blo 1338988 2009825 := bstep (se 2 (by rfl) ⟨753684, by rfl⟩ : syracuseStep 2009825 = 1507369) B1507369
theorem B19311331 : Blo 1338988 19311331 := bstep (se 1 (by rfl) ⟨14483498, by rfl⟩ : syracuseStep 19311331 = 28966997) B28966997
theorem B4295405 : Blo 1338988 4295405 := bstep (se 3 (by rfl) ⟨805388, by rfl⟩ : syracuseStep 4295405 = 1610777) B1610777
theorem B2009843 : Blo 1338988 2009843 := bstep (se 1 (by rfl) ⟨1507382, by rfl⟩ : syracuseStep 2009843 = 3014765) B3014765
theorem B3721997 : Blo 1338988 3721997 := bstep (se 3 (by rfl) ⟨697874, by rfl⟩ : syracuseStep 3721997 = 1395749) B1395749
theorem B2009873 : Blo 1338988 2009873 := bstep (se 2 (by rfl) ⟨753702, by rfl⟩ : syracuseStep 2009873 = 1507405) B1507405
theorem B2009891 : Blo 1338988 2009891 := bstep (se 1 (by rfl) ⟨1507418, by rfl⟩ : syracuseStep 2009891 = 3014837) B3014837
theorem B6441763 : Blo 1338988 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B2009921 : Blo 1338988 2009921 := bstep (se 2 (by rfl) ⟨753720, by rfl⟩ : syracuseStep 2009921 = 1507441) B1507441
theorem B2542403 : Blo 1338988 2542403 := bstep (se 1 (by rfl) ⟨1906802, by rfl⟩ : syracuseStep 2542403 = 3813605) B3813605
theorem B2009939 : Blo 1338988 2009939 := bstep (se 1 (by rfl) ⟨1507454, by rfl⟩ : syracuseStep 2009939 = 3014909) B3014909
theorem B2009969 : Blo 1338988 2009969 := bstep (se 2 (by rfl) ⟨753738, by rfl⟩ : syracuseStep 2009969 = 1507477) B1507477
theorem B2009987 : Blo 1338988 2009987 := bstep (se 1 (by rfl) ⟨1507490, by rfl⟩ : syracuseStep 2009987 = 3014981) B3014981
theorem B4582289 : Blo 1338988 4582289 := bstep (se 2 (by rfl) ⟨1718358, by rfl⟩ : syracuseStep 4582289 = 3436717) B3436717
theorem B3869585 : Blo 1338988 3869585 := bstep (se 2 (by rfl) ⟨1451094, by rfl⟩ : syracuseStep 3869585 = 2902189) B2902189
theorem B2010017 : Blo 1338988 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B2010035 : Blo 1338988 2010035 := bstep (se 1 (by rfl) ⟨1507526, by rfl⟩ : syracuseStep 2010035 = 3015053) B3015053
theorem B2010065 : Blo 1338988 2010065 := bstep (se 2 (by rfl) ⟨753774, by rfl⟩ : syracuseStep 2010065 = 1507549) B1507549
theorem B2010083 : Blo 1338988 2010083 := bstep (se 1 (by rfl) ⟨1507562, by rfl⟩ : syracuseStep 2010083 = 3015125) B3015125
theorem B4525037 : Blo 1338988 4525037 := bstep (se 3 (by rfl) ⟨848444, by rfl⟩ : syracuseStep 4525037 = 1696889) B1696889
theorem B2010113 : Blo 1338988 2010113 := bstep (se 2 (by rfl) ⟨753792, by rfl⟩ : syracuseStep 2010113 = 1507585) B1507585
theorem B2010131 : Blo 1338988 2010131 := bstep (se 1 (by rfl) ⟨1507598, by rfl⟩ : syracuseStep 2010131 = 3015197) B3015197
theorem B4525091 : Blo 1338988 4525091 := bstep (se 1 (by rfl) ⟨3393818, by rfl⟩ : syracuseStep 4525091 = 6787637) B6787637
theorem B2010161 : Blo 1338988 2010161 := bstep (se 2 (by rfl) ⟨753810, by rfl⟩ : syracuseStep 2010161 = 1507621) B1507621
theorem B2010179 : Blo 1338988 2010179 := bstep (se 1 (by rfl) ⟨1507634, by rfl⟩ : syracuseStep 2010179 = 3015269) B3015269
theorem B2010209 : Blo 1338988 2010209 := bstep (se 2 (by rfl) ⟨753828, by rfl⟩ : syracuseStep 2010209 = 1507657) B1507657
theorem B2542691 : Blo 1338988 2542691 := bstep (se 1 (by rfl) ⟨1907018, by rfl⟩ : syracuseStep 2542691 = 3814037) B3814037
theorem B3869795 : Blo 1338988 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B2010227 : Blo 1338988 2010227 := bstep (se 1 (by rfl) ⟨1507670, by rfl⟩ : syracuseStep 2010227 = 3015341) B3015341
theorem B2010257 : Blo 1338988 2010257 := bstep (se 2 (by rfl) ⟨753846, by rfl⟩ : syracuseStep 2010257 = 1507693) B1507693
theorem B2010275 : Blo 1338988 2010275 := bstep (se 1 (by rfl) ⟨1507706, by rfl⟩ : syracuseStep 2010275 = 3015413) B3015413
theorem B2092211 : Blo 1338988 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B2010305 : Blo 1338988 2010305 := bstep (se 2 (by rfl) ⟨753864, by rfl⟩ : syracuseStep 2010305 = 1507729) B1507729
theorem B2010323 : Blo 1338988 2010323 := bstep (se 1 (by rfl) ⟨1507742, by rfl⟩ : syracuseStep 2010323 = 3015485) B3015485
theorem B5721329 : Blo 1338988 5721329 := bstep (se 2 (by rfl) ⟨2145498, by rfl⟩ : syracuseStep 5721329 = 4290997) B4290997
theorem B2010353 : Blo 1338988 2010353 := bstep (se 2 (by rfl) ⟨753882, by rfl⟩ : syracuseStep 2010353 = 1507765) B1507765
theorem B2010371 : Blo 1338988 2010371 := bstep (se 1 (by rfl) ⟨1507778, by rfl⟩ : syracuseStep 2010371 = 3015557) B3015557
theorem B2010401 : Blo 1338988 2010401 := bstep (se 2 (by rfl) ⟨753900, by rfl⟩ : syracuseStep 2010401 = 1507801) B1507801
theorem B4525361 : Blo 1338988 4525361 := bstep (se 2 (by rfl) ⟨1697010, by rfl⟩ : syracuseStep 4525361 = 3394021) B3394021
theorem B2010419 : Blo 1338988 2010419 := bstep (se 1 (by rfl) ⟨1507814, by rfl⟩ : syracuseStep 2010419 = 3015629) B3015629
theorem B2010449 : Blo 1338988 2010449 := bstep (se 2 (by rfl) ⟨753918, by rfl⟩ : syracuseStep 2010449 = 1507837) B1507837
theorem B2010467 : Blo 1338988 2010467 := bstep (se 1 (by rfl) ⟨1507850, by rfl⟩ : syracuseStep 2010467 = 3015701) B3015701
theorem B2010497 : Blo 1338988 2010497 := bstep (se 2 (by rfl) ⟨753936, by rfl⟩ : syracuseStep 2010497 = 1507873) B1507873
theorem B2010515 : Blo 1338988 2010515 := bstep (se 1 (by rfl) ⟨1507886, by rfl⟩ : syracuseStep 2010515 = 3015773) B3015773
theorem B2010545 : Blo 1338988 2010545 := bstep (se 2 (by rfl) ⟨753954, by rfl⟩ : syracuseStep 2010545 = 1507909) B1507909
theorem B2010563 : Blo 1338988 2010563 := bstep (se 1 (by rfl) ⟨1507922, by rfl⟩ : syracuseStep 2010563 = 3015845) B3015845
theorem B16289221 : Blo 1338988 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B2321875 : Blo 1338988 2321875 := bstep (se 1 (by rfl) ⟨1741406, by rfl⟩ : syracuseStep 2321875 = 3482813) B3482813
theorem B2010593 : Blo 1338988 2010593 := bstep (se 2 (by rfl) ⟨753972, by rfl⟩ : syracuseStep 2010593 = 1507945) B1507945
theorem B7630307 : Blo 1338988 7630307 := bstep (se 1 (by rfl) ⟨5722730, by rfl⟩ : syracuseStep 7630307 = 11445461) B11445461
theorem B2010611 : Blo 1338988 2010611 := bstep (se 1 (by rfl) ⟨1507958, by rfl⟩ : syracuseStep 2010611 = 3015917) B3015917
theorem B2010641 : Blo 1338988 2010641 := bstep (se 2 (by rfl) ⟨753990, by rfl⟩ : syracuseStep 2010641 = 1507981) B1507981
theorem B2010659 : Blo 1338988 2010659 := bstep (se 1 (by rfl) ⟨1507994, by rfl⟩ : syracuseStep 2010659 = 3015989) B3015989
theorem B2010689 : Blo 1338988 2010689 := bstep (se 2 (by rfl) ⟨754008, by rfl⟩ : syracuseStep 2010689 = 1508017) B1508017
theorem B2715203 : Blo 1338988 2715203 := bstep (se 1 (by rfl) ⟨2036402, by rfl⟩ : syracuseStep 2715203 = 4072805) B4072805
theorem B2010707 : Blo 1338988 2010707 := bstep (se 1 (by rfl) ⟨1508030, by rfl⟩ : syracuseStep 2010707 = 3016061) B3016061
theorem B2010737 : Blo 1338988 2010737 := bstep (se 2 (by rfl) ⟨754026, by rfl⟩ : syracuseStep 2010737 = 1508053) B1508053
theorem B1338995 : Blo 1338988 1338995 := bstep (se 1 (by rfl) ⟨1004246, by rfl⟩ : syracuseStep 1338995 = 2008493) B2008493
theorem B1339011 : Blo 1338988 1339011 := bstep (se 1 (by rfl) ⟨1004258, by rfl⟩ : syracuseStep 1339011 = 2008517) B2008517
theorem B4075139 : Blo 1338988 4075139 := bstep (se 1 (by rfl) ⟨3056354, by rfl⟩ : syracuseStep 4075139 = 6112709) B6112709
theorem B2010755 : Blo 1338988 2010755 := bstep (se 1 (by rfl) ⟨1508066, by rfl⟩ : syracuseStep 2010755 = 3016133) B3016133
theorem B5090957 : Blo 1338988 5090957 := bstep (se 3 (by rfl) ⟨954554, by rfl⟩ : syracuseStep 5090957 = 1909109) B1909109
theorem B1339027 : Blo 1338988 1339027 := bstep (se 1 (by rfl) ⟨1004270, by rfl⟩ : syracuseStep 1339027 = 2008541) B2008541
theorem B2010785 : Blo 1338988 2010785 := bstep (se 2 (by rfl) ⟨754044, by rfl⟩ : syracuseStep 2010785 = 1508089) B1508089
theorem B1339043 : Blo 1338988 1339043 := bstep (se 1 (by rfl) ⟨1004282, by rfl⟩ : syracuseStep 1339043 = 2008565) B2008565
theorem B1961635 : Blo 1338988 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B1339059 : Blo 1338988 1339059 := bstep (se 1 (by rfl) ⟨1004294, by rfl⟩ : syracuseStep 1339059 = 2008589) B2008589
theorem B2010803 : Blo 1338988 2010803 := bstep (se 1 (by rfl) ⟨1508102, by rfl⟩ : syracuseStep 2010803 = 3016205) B3016205
theorem B1339075 : Blo 1338988 1339075 := bstep (se 1 (by rfl) ⟨1004306, by rfl⟩ : syracuseStep 1339075 = 2008613) B2008613
theorem B2010833 : Blo 1338988 2010833 := bstep (se 2 (by rfl) ⟨754062, by rfl⟩ : syracuseStep 2010833 = 1508125) B1508125
theorem B1609427 : Blo 1338988 1609427 := bstep (se 1 (by rfl) ⟨1207070, by rfl⟩ : syracuseStep 1609427 = 2414141) B2414141
theorem B1339091 : Blo 1338988 1339091 := bstep (se 1 (by rfl) ⟨1004318, by rfl⟩ : syracuseStep 1339091 = 2008637) B2008637
theorem B1339107 : Blo 1338988 1339107 := bstep (se 1 (by rfl) ⟨1004330, by rfl⟩ : syracuseStep 1339107 = 2008661) B2008661
theorem B2010851 : Blo 1338988 2010851 := bstep (se 1 (by rfl) ⟨1508138, by rfl⟩ : syracuseStep 2010851 = 3016277) B3016277
theorem B1339123 : Blo 1338988 1339123 := bstep (se 1 (by rfl) ⟨1004342, by rfl⟩ : syracuseStep 1339123 = 2008685) B2008685
theorem B2010881 : Blo 1338988 2010881 := bstep (se 2 (by rfl) ⟨754080, by rfl⟩ : syracuseStep 2010881 = 1508161) B1508161
theorem B1339139 : Blo 1338988 1339139 := bstep (se 1 (by rfl) ⟨1004354, by rfl⟩ : syracuseStep 1339139 = 2008709) B2008709
theorem B1339155 : Blo 1338988 1339155 := bstep (se 1 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 1339155 = 2008733) B2008733
theorem B2010899 : Blo 1338988 2010899 := bstep (se 1 (by rfl) ⟨1508174, by rfl⟩ : syracuseStep 2010899 = 3016349) B3016349
theorem B1339171 : Blo 1338988 1339171 := bstep (se 1 (by rfl) ⟨1004378, by rfl⟩ : syracuseStep 1339171 = 2008757) B2008757
theorem B2010929 : Blo 1338988 2010929 := bstep (se 2 (by rfl) ⟨754098, by rfl⟩ : syracuseStep 2010929 = 1508197) B1508197
theorem B1339187 : Blo 1338988 1339187 := bstep (se 1 (by rfl) ⟨1004390, by rfl⟩ : syracuseStep 1339187 = 2008781) B2008781
theorem B1339203 : Blo 1338988 1339203 := bstep (se 1 (by rfl) ⟨1004402, by rfl⟩ : syracuseStep 1339203 = 2008805) B2008805
theorem B2010947 : Blo 1338988 2010947 := bstep (se 1 (by rfl) ⟨1508210, by rfl⟩ : syracuseStep 2010947 = 3016421) B3016421
theorem B1339219 : Blo 1338988 1339219 := bstep (se 1 (by rfl) ⟨1004414, by rfl⟩ : syracuseStep 1339219 = 2008829) B2008829
theorem B2010977 : Blo 1338988 2010977 := bstep (se 2 (by rfl) ⟨754116, by rfl⟩ : syracuseStep 2010977 = 1508233) B1508233
theorem B1339235 : Blo 1338988 1339235 := bstep (se 1 (by rfl) ⟨1004426, by rfl⟩ : syracuseStep 1339235 = 2008853) B2008853
theorem B8589169 : Blo 1338988 8589169 := bstep (se 2 (by rfl) ⟨3220938, by rfl⟩ : syracuseStep 8589169 = 6441877) B6441877
theorem B1339251 : Blo 1338988 1339251 := bstep (se 1 (by rfl) ⟨1004438, by rfl⟩ : syracuseStep 1339251 = 2008877) B2008877
theorem B2010995 : Blo 1338988 2010995 := bstep (se 1 (by rfl) ⟨1508246, by rfl⟩ : syracuseStep 2010995 = 3016493) B3016493
theorem B1339267 : Blo 1338988 1339267 := bstep (se 1 (by rfl) ⟨1004450, by rfl⟩ : syracuseStep 1339267 = 2008901) B2008901
theorem B2011025 : Blo 1338988 2011025 := bstep (se 2 (by rfl) ⟨754134, by rfl⟩ : syracuseStep 2011025 = 1508269) B1508269
theorem B1339283 : Blo 1338988 1339283 := bstep (se 1 (by rfl) ⟨1004462, by rfl⟩ : syracuseStep 1339283 = 2008925) B2008925
theorem B1339299 : Blo 1338988 1339299 := bstep (se 1 (by rfl) ⟨1004474, by rfl⟩ : syracuseStep 1339299 = 2008949) B2008949
theorem B2011043 : Blo 1338988 2011043 := bstep (se 1 (by rfl) ⟨1508282, by rfl⟩ : syracuseStep 2011043 = 3016565) B3016565
theorem B1339315 : Blo 1338988 1339315 := bstep (se 1 (by rfl) ⟨1004486, by rfl⟩ : syracuseStep 1339315 = 2008973) B2008973
theorem B2011073 : Blo 1338988 2011073 := bstep (se 2 (by rfl) ⟨754152, by rfl⟩ : syracuseStep 2011073 = 1508305) B1508305
theorem B1339331 : Blo 1338988 1339331 := bstep (se 1 (by rfl) ⟨1004498, by rfl⟩ : syracuseStep 1339331 = 2008997) B2008997
theorem B1339347 : Blo 1338988 1339347 := bstep (se 1 (by rfl) ⟨1004510, by rfl⟩ : syracuseStep 1339347 = 2009021) B2009021
theorem B2011091 : Blo 1338988 2011091 := bstep (se 1 (by rfl) ⟨1508318, by rfl⟩ : syracuseStep 2011091 = 3016637) B3016637
theorem B1339363 : Blo 1338988 1339363 := bstep (se 1 (by rfl) ⟨1004522, by rfl⟩ : syracuseStep 1339363 = 2009045) B2009045
theorem B2011121 : Blo 1338988 2011121 := bstep (se 2 (by rfl) ⟨754170, by rfl⟩ : syracuseStep 2011121 = 1508341) B1508341
theorem B6442993 : Blo 1338988 6442993 := bstep (se 2 (by rfl) ⟨2416122, by rfl⟩ : syracuseStep 6442993 = 4832245) B4832245
theorem B1339379 : Blo 1338988 1339379 := bstep (se 1 (by rfl) ⟨1004534, by rfl⟩ : syracuseStep 1339379 = 2009069) B2009069
theorem B1339395 : Blo 1338988 1339395 := bstep (se 1 (by rfl) ⟨1004546, by rfl⟩ : syracuseStep 1339395 = 2009093) B2009093
theorem B2011139 : Blo 1338988 2011139 := bstep (se 1 (by rfl) ⟨1508354, by rfl⟩ : syracuseStep 2011139 = 3016709) B3016709
theorem B3813389 : Blo 1338988 3813389 := bstep (se 3 (by rfl) ⟨715010, by rfl⟩ : syracuseStep 3813389 = 1430021) B1430021
theorem B2543633 : Blo 1338988 2543633 := bstep (se 2 (by rfl) ⟨953862, by rfl⟩ : syracuseStep 2543633 = 1907725) B1907725
theorem B1339411 : Blo 1338988 1339411 := bstep (se 1 (by rfl) ⟨1004558, by rfl⟩ : syracuseStep 1339411 = 2009117) B2009117
theorem B2011169 : Blo 1338988 2011169 := bstep (se 2 (by rfl) ⟨754188, by rfl⟩ : syracuseStep 2011169 = 1508377) B1508377
theorem B1339427 : Blo 1338988 1339427 := bstep (se 1 (by rfl) ⟨1004570, by rfl⟩ : syracuseStep 1339427 = 2009141) B2009141
theorem B4829219 : Blo 1338988 4829219 := bstep (se 1 (by rfl) ⟨3621914, by rfl⟩ : syracuseStep 4829219 = 7243829) B7243829
theorem B4075555 : Blo 1338988 4075555 := bstep (se 1 (by rfl) ⟨3056666, by rfl⟩ : syracuseStep 4075555 = 6113333) B6113333
theorem B1339443 : Blo 1338988 1339443 := bstep (se 1 (by rfl) ⟨1004582, by rfl⟩ : syracuseStep 1339443 = 2009165) B2009165
theorem B2011187 : Blo 1338988 2011187 := bstep (se 1 (by rfl) ⟨1508390, by rfl⟩ : syracuseStep 2011187 = 3016781) B3016781
theorem B1339459 : Blo 1338988 1339459 := bstep (se 1 (by rfl) ⟨1004594, by rfl⟩ : syracuseStep 1339459 = 2009189) B2009189
theorem B2011217 : Blo 1338988 2011217 := bstep (se 2 (by rfl) ⟨754206, by rfl⟩ : syracuseStep 2011217 = 1508413) B1508413
theorem B1339475 : Blo 1338988 1339475 := bstep (se 1 (by rfl) ⟨1004606, by rfl⟩ : syracuseStep 1339475 = 2009213) B2009213
theorem B1339491 : Blo 1338988 1339491 := bstep (se 1 (by rfl) ⟨1004618, by rfl⟩ : syracuseStep 1339491 = 2009237) B2009237
theorem B2011235 : Blo 1338988 2011235 := bstep (se 1 (by rfl) ⟨1508426, by rfl⟩ : syracuseStep 2011235 = 3016853) B3016853
theorem B1339507 : Blo 1338988 1339507 := bstep (se 1 (by rfl) ⟨1004630, by rfl⟩ : syracuseStep 1339507 = 2009261) B2009261
theorem B2011265 : Blo 1338988 2011265 := bstep (se 2 (by rfl) ⟨754224, by rfl⟩ : syracuseStep 2011265 = 1508449) B1508449
theorem B1339523 : Blo 1338988 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B1339539 : Blo 1338988 1339539 := bstep (se 1 (by rfl) ⟨1004654, by rfl⟩ : syracuseStep 1339539 = 2009309) B2009309
theorem B2011283 : Blo 1338988 2011283 := bstep (se 1 (by rfl) ⟨1508462, by rfl⟩ : syracuseStep 2011283 = 3016925) B3016925
theorem B1339555 : Blo 1338988 1339555 := bstep (se 1 (by rfl) ⟨1004666, by rfl⟩ : syracuseStep 1339555 = 2009333) B2009333
theorem B1339571 : Blo 1338988 1339571 := bstep (se 1 (by rfl) ⟨1004678, by rfl⟩ : syracuseStep 1339571 = 2009357) B2009357
theorem B2011313 : Blo 1338988 2011313 := bstep (se 2 (by rfl) ⟨754242, by rfl⟩ : syracuseStep 2011313 = 1508485) B1508485
theorem B1339587 : Blo 1338988 1339587 := bstep (se 1 (by rfl) ⟨1004690, by rfl⟩ : syracuseStep 1339587 = 2009381) B2009381
theorem B2011331 : Blo 1338988 2011331 := bstep (se 1 (by rfl) ⟨1508498, by rfl⟩ : syracuseStep 2011331 = 3016997) B3016997
theorem B3813581 : Blo 1338988 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B1339603 : Blo 1338988 1339603 := bstep (se 1 (by rfl) ⟨1004702, by rfl⟩ : syracuseStep 1339603 = 2009405) B2009405
theorem B1339619 : Blo 1338988 1339619 := bstep (se 1 (by rfl) ⟨1004714, by rfl⟩ : syracuseStep 1339619 = 2009429) B2009429
theorem B2011361 : Blo 1338988 2011361 := bstep (se 2 (by rfl) ⟨754260, by rfl⟩ : syracuseStep 2011361 = 1508521) B1508521
theorem B6787313 : Blo 1338988 6787313 := bstep (se 2 (by rfl) ⟨2545242, by rfl⟩ : syracuseStep 6787313 = 5090485) B5090485
theorem B1339635 : Blo 1338988 1339635 := bstep (se 1 (by rfl) ⟨1004726, by rfl⟩ : syracuseStep 1339635 = 2009453) B2009453
theorem B2011379 : Blo 1338988 2011379 := bstep (se 1 (by rfl) ⟨1508534, by rfl⟩ : syracuseStep 2011379 = 3017069) B3017069
theorem B1339651 : Blo 1338988 1339651 := bstep (se 1 (by rfl) ⟨1004738, by rfl⟩ : syracuseStep 1339651 = 2009477) B2009477
theorem B2011409 : Blo 1338988 2011409 := bstep (se 2 (by rfl) ⟨754278, by rfl⟩ : syracuseStep 2011409 = 1508557) B1508557
theorem B1339667 : Blo 1338988 1339667 := bstep (se 1 (by rfl) ⟨1004750, by rfl⟩ : syracuseStep 1339667 = 2009501) B2009501
theorem B1339683 : Blo 1338988 1339683 := bstep (se 1 (by rfl) ⟨1004762, by rfl⟩ : syracuseStep 1339683 = 2009525) B2009525
theorem B2011427 : Blo 1338988 2011427 := bstep (se 1 (by rfl) ⟨1508570, by rfl⟩ : syracuseStep 2011427 = 3017141) B3017141
theorem B1339699 : Blo 1338988 1339699 := bstep (se 1 (by rfl) ⟨1004774, by rfl⟩ : syracuseStep 1339699 = 2009549) B2009549
theorem B2011457 : Blo 1338988 2011457 := bstep (se 2 (by rfl) ⟨754296, by rfl⟩ : syracuseStep 2011457 = 1508593) B1508593
theorem B1339715 : Blo 1338988 1339715 := bstep (se 1 (by rfl) ⟨1004786, by rfl⟩ : syracuseStep 1339715 = 2009573) B2009573
theorem B6779213 : Blo 1338988 6779213 := bstep (se 3 (by rfl) ⟨1271102, by rfl⟩ : syracuseStep 6779213 = 2542205) B2542205
theorem B2093393 : Blo 1338988 2093393 := bstep (se 2 (by rfl) ⟨785022, by rfl⟩ : syracuseStep 2093393 = 1570045) B1570045
theorem B1339731 : Blo 1338988 1339731 := bstep (se 1 (by rfl) ⟨1004798, by rfl⟩ : syracuseStep 1339731 = 2009597) B2009597
theorem B2011475 : Blo 1338988 2011475 := bstep (se 1 (by rfl) ⟨1508606, by rfl⟩ : syracuseStep 2011475 = 3017213) B3017213
theorem B1339747 : Blo 1338988 1339747 := bstep (se 1 (by rfl) ⟨1004810, by rfl⟩ : syracuseStep 1339747 = 2009621) B2009621
theorem B15257969 : Blo 1338988 15257969 := bstep (se 2 (by rfl) ⟨5721738, by rfl⟩ : syracuseStep 15257969 = 11443477) B11443477
theorem B1339763 : Blo 1338988 1339763 := bstep (se 1 (by rfl) ⟨1004822, by rfl⟩ : syracuseStep 1339763 = 2009645) B2009645
theorem B1339779 : Blo 1338988 1339779 := bstep (se 1 (by rfl) ⟨1004834, by rfl⟩ : syracuseStep 1339779 = 2009669) B2009669
theorem B1339795 : Blo 1338988 1339795 := bstep (se 1 (by rfl) ⟨1004846, by rfl⟩ : syracuseStep 1339795 = 2009693) B2009693
theorem B1339811 : Blo 1338988 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B1339827 : Blo 1338988 1339827 := bstep (se 1 (by rfl) ⟨1004870, by rfl⟩ : syracuseStep 1339827 = 2009741) B2009741
theorem B1339843 : Blo 1338988 1339843 := bstep (se 1 (by rfl) ⟨1004882, by rfl⟩ : syracuseStep 1339843 = 2009765) B2009765
theorem B1339859 : Blo 1338988 1339859 := bstep (se 1 (by rfl) ⟨1004894, by rfl⟩ : syracuseStep 1339859 = 2009789) B2009789
theorem B5722595 : Blo 1338988 5722595 := bstep (se 1 (by rfl) ⟨4291946, by rfl⟩ : syracuseStep 5722595 = 8583893) B8583893
theorem B1339875 : Blo 1338988 1339875 := bstep (se 1 (by rfl) ⟨1004906, by rfl⟩ : syracuseStep 1339875 = 2009813) B2009813
theorem B1339891 : Blo 1338988 1339891 := bstep (se 1 (by rfl) ⟨1004918, by rfl⟩ : syracuseStep 1339891 = 2009837) B2009837
theorem B1339907 : Blo 1338988 1339907 := bstep (se 1 (by rfl) ⟨1004930, by rfl⟩ : syracuseStep 1339907 = 2009861) B2009861
theorem B1339923 : Blo 1338988 1339923 := bstep (se 1 (by rfl) ⟨1004942, by rfl⟩ : syracuseStep 1339923 = 2009885) B2009885
theorem B1339939 : Blo 1338988 1339939 := bstep (se 1 (by rfl) ⟨1004954, by rfl⟩ : syracuseStep 1339939 = 2009909) B2009909
theorem B1339955 : Blo 1338988 1339955 := bstep (se 1 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 1339955 = 2009933) B2009933
theorem B1339971 : Blo 1338988 1339971 := bstep (se 1 (by rfl) ⟨1004978, by rfl⟩ : syracuseStep 1339971 = 2009957) B2009957
theorem B1339987 : Blo 1338988 1339987 := bstep (se 1 (by rfl) ⟨1004990, by rfl⟩ : syracuseStep 1339987 = 2009981) B2009981
theorem B1340003 : Blo 1338988 1340003 := bstep (se 1 (by rfl) ⟨1005002, by rfl⟩ : syracuseStep 1340003 = 2010005) B2010005
theorem B1340019 : Blo 1338988 1340019 := bstep (se 1 (by rfl) ⟨1005014, by rfl⟩ : syracuseStep 1340019 = 2010029) B2010029
theorem B1340035 : Blo 1338988 1340035 := bstep (se 1 (by rfl) ⟨1005026, by rfl⟩ : syracuseStep 1340035 = 2010053) B2010053
theorem B1340051 : Blo 1338988 1340051 := bstep (se 1 (by rfl) ⟨1005038, by rfl⟩ : syracuseStep 1340051 = 2010077) B2010077
theorem B1340067 : Blo 1338988 1340067 := bstep (se 1 (by rfl) ⟨1005050, by rfl⟩ : syracuseStep 1340067 = 2010101) B2010101
theorem B1340083 : Blo 1338988 1340083 := bstep (se 1 (by rfl) ⟨1005062, by rfl⟩ : syracuseStep 1340083 = 2010125) B2010125
theorem B1340099 : Blo 1338988 1340099 := bstep (se 1 (by rfl) ⟨1005074, by rfl⟩ : syracuseStep 1340099 = 2010149) B2010149
theorem B10179269 : Blo 1338988 10179269 := bstep (se 4 (by rfl) ⟨954306, by rfl⟩ : syracuseStep 10179269 = 1908613) B1908613
theorem B1340115 : Blo 1338988 1340115 := bstep (se 1 (by rfl) ⟨1005086, by rfl⟩ : syracuseStep 1340115 = 2010173) B2010173
theorem B73355989 : Blo 1338988 73355989 := bstep (se 7 (by rfl) ⟨859640, by rfl⟩ : syracuseStep 73355989 = 1719281) B1719281
theorem B1340131 : Blo 1338988 1340131 := bstep (se 1 (by rfl) ⟨1005098, by rfl⟩ : syracuseStep 1340131 = 2010197) B2010197
theorem B1340147 : Blo 1338988 1340147 := bstep (se 1 (by rfl) ⟨1005110, by rfl⟩ : syracuseStep 1340147 = 2010221) B2010221
theorem B1340163 : Blo 1338988 1340163 := bstep (se 1 (by rfl) ⟨1005122, by rfl⟩ : syracuseStep 1340163 = 2010245) B2010245
theorem B1528579 : Blo 1338988 1528579 := bstep (se 1 (by rfl) ⟨1146434, by rfl⟩ : syracuseStep 1528579 = 2292869) B2292869
theorem B1340179 : Blo 1338988 1340179 := bstep (se 1 (by rfl) ⟨1005134, by rfl⟩ : syracuseStep 1340179 = 2010269) B2010269
theorem B73331477 : Blo 1338988 73331477 := bstep (se 6 (by rfl) ⟨1718706, by rfl⟩ : syracuseStep 73331477 = 3437413) B3437413
theorem B1340195 : Blo 1338988 1340195 := bstep (se 1 (by rfl) ⟨1005146, by rfl⟩ : syracuseStep 1340195 = 2010293) B2010293
theorem B1340211 : Blo 1338988 1340211 := bstep (se 1 (by rfl) ⟨1005158, by rfl⟩ : syracuseStep 1340211 = 2010317) B2010317
theorem B1340227 : Blo 1338988 1340227 := bstep (se 1 (by rfl) ⟨1005170, by rfl⟩ : syracuseStep 1340227 = 2010341) B2010341
theorem B1340243 : Blo 1338988 1340243 := bstep (se 1 (by rfl) ⟨1005182, by rfl⟩ : syracuseStep 1340243 = 2010365) B2010365
theorem B11449187 : Blo 1338988 11449187 := bstep (se 1 (by rfl) ⟨8586890, by rfl⟩ : syracuseStep 11449187 = 17173781) B17173781
theorem B1340259 : Blo 1338988 1340259 := bstep (se 1 (by rfl) ⟨1005194, by rfl⟩ : syracuseStep 1340259 = 2010389) B2010389
theorem B1340275 : Blo 1338988 1340275 := bstep (se 1 (by rfl) ⟨1005206, by rfl⟩ : syracuseStep 1340275 = 2010413) B2010413
theorem B1340291 : Blo 1338988 1340291 := bstep (se 1 (by rfl) ⟨1005218, by rfl⟩ : syracuseStep 1340291 = 2010437) B2010437
theorem B2544529 : Blo 1338988 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B1340307 : Blo 1338988 1340307 := bstep (se 1 (by rfl) ⟨1005230, by rfl⟩ : syracuseStep 1340307 = 2010461) B2010461
theorem B1340323 : Blo 1338988 1340323 := bstep (se 1 (by rfl) ⟨1005242, by rfl⟩ : syracuseStep 1340323 = 2010485) B2010485
theorem B1340339 : Blo 1338988 1340339 := bstep (se 1 (by rfl) ⟨1005254, by rfl⟩ : syracuseStep 1340339 = 2010509) B2010509
theorem B1340355 : Blo 1338988 1340355 := bstep (se 1 (by rfl) ⟨1005266, by rfl⟩ : syracuseStep 1340355 = 2010533) B2010533
theorem B1340371 : Blo 1338988 1340371 := bstep (se 1 (by rfl) ⟨1005278, by rfl⟩ : syracuseStep 1340371 = 2010557) B2010557
theorem B1340387 : Blo 1338988 1340387 := bstep (se 1 (by rfl) ⟨1005290, by rfl⟩ : syracuseStep 1340387 = 2010581) B2010581
theorem B1340403 : Blo 1338988 1340403 := bstep (se 1 (by rfl) ⟨1005302, by rfl⟩ : syracuseStep 1340403 = 2010605) B2010605
theorem B1340419 : Blo 1338988 1340419 := bstep (se 1 (by rfl) ⟨1005314, by rfl⟩ : syracuseStep 1340419 = 2010629) B2010629
theorem B2036755 : Blo 1338988 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B1340435 : Blo 1338988 1340435 := bstep (se 1 (by rfl) ⟨1005326, by rfl⟩ : syracuseStep 1340435 = 2010653) B2010653
theorem B1340451 : Blo 1338988 1340451 := bstep (se 1 (by rfl) ⟨1005338, by rfl⟩ : syracuseStep 1340451 = 2010677) B2010677
theorem B2544689 : Blo 1338988 2544689 := bstep (se 2 (by rfl) ⟨954258, by rfl⟩ : syracuseStep 2544689 = 1908517) B1908517
theorem B1340467 : Blo 1338988 1340467 := bstep (se 1 (by rfl) ⟨1005350, by rfl⟩ : syracuseStep 1340467 = 2010701) B2010701
theorem B1340483 : Blo 1338988 1340483 := bstep (se 1 (by rfl) ⟨1005362, by rfl⟩ : syracuseStep 1340483 = 2010725) B2010725
theorem B1340499 : Blo 1338988 1340499 := bstep (se 1 (by rfl) ⟨1005374, by rfl⟩ : syracuseStep 1340499 = 2010749) B2010749
theorem B1340515 : Blo 1338988 1340515 := bstep (se 1 (by rfl) ⟨1005386, by rfl⟩ : syracuseStep 1340515 = 2010773) B2010773
theorem B1340531 : Blo 1338988 1340531 := bstep (se 1 (by rfl) ⟨1005398, by rfl⟩ : syracuseStep 1340531 = 2010797) B2010797
theorem B1340547 : Blo 1338988 1340547 := bstep (se 1 (by rfl) ⟨1005410, by rfl⟩ : syracuseStep 1340547 = 2010821) B2010821
theorem B1340563 : Blo 1338988 1340563 := bstep (se 1 (by rfl) ⟨1005422, by rfl⟩ : syracuseStep 1340563 = 2010845) B2010845
theorem B1340579 : Blo 1338988 1340579 := bstep (se 1 (by rfl) ⟨1005434, by rfl⟩ : syracuseStep 1340579 = 2010869) B2010869
theorem B3814573 : Blo 1338988 3814573 := bstep (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) B1430465
theorem B1340595 : Blo 1338988 1340595 := bstep (se 1 (by rfl) ⟨1005446, by rfl⟩ : syracuseStep 1340595 = 2010893) B2010893
theorem B1340611 : Blo 1338988 1340611 := bstep (se 1 (by rfl) ⟨1005458, by rfl⟩ : syracuseStep 1340611 = 2010917) B2010917
theorem B1340627 : Blo 1338988 1340627 := bstep (se 1 (by rfl) ⟨1005470, by rfl⟩ : syracuseStep 1340627 = 2010941) B2010941
theorem B2413795 : Blo 1338988 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B2036963 : Blo 1338988 2036963 := bstep (se 1 (by rfl) ⟨1527722, by rfl⟩ : syracuseStep 2036963 = 3055445) B3055445
theorem B1340643 : Blo 1338988 1340643 := bstep (se 1 (by rfl) ⟨1005482, by rfl⟩ : syracuseStep 1340643 = 2010965) B2010965
theorem B1340659 : Blo 1338988 1340659 := bstep (se 1 (by rfl) ⟨1005494, by rfl⟩ : syracuseStep 1340659 = 2010989) B2010989
theorem B1340675 : Blo 1338988 1340675 := bstep (se 1 (by rfl) ⟨1005506, by rfl⟩ : syracuseStep 1340675 = 2011013) B2011013
theorem B1340691 : Blo 1338988 1340691 := bstep (se 1 (by rfl) ⟨1005518, by rfl⟩ : syracuseStep 1340691 = 2011037) B2011037
theorem B1340707 : Blo 1338988 1340707 := bstep (se 1 (by rfl) ⟨1005530, by rfl⟩ : syracuseStep 1340707 = 2011061) B2011061
theorem B1340723 : Blo 1338988 1340723 := bstep (se 1 (by rfl) ⟨1005542, by rfl⟩ : syracuseStep 1340723 = 2011085) B2011085
theorem B1340739 : Blo 1338988 1340739 := bstep (se 1 (by rfl) ⟨1005554, by rfl⟩ : syracuseStep 1340739 = 2011109) B2011109
theorem B4289869 : Blo 1338988 4289869 := bstep (se 3 (by rfl) ⟨804350, by rfl⟩ : syracuseStep 4289869 = 1608701) B1608701
theorem B1340755 : Blo 1338988 1340755 := bstep (se 1 (by rfl) ⟨1005566, by rfl⟩ : syracuseStep 1340755 = 2011133) B2011133
theorem B1340771 : Blo 1338988 1340771 := bstep (se 1 (by rfl) ⟨1005578, by rfl⟩ : syracuseStep 1340771 = 2011157) B2011157
theorem B1340787 : Blo 1338988 1340787 := bstep (se 1 (by rfl) ⟨1005590, by rfl⟩ : syracuseStep 1340787 = 2011181) B2011181
theorem B1340803 : Blo 1338988 1340803 := bstep (se 1 (by rfl) ⟨1005602, by rfl⟩ : syracuseStep 1340803 = 2011205) B2011205
theorem B4519313 : Blo 1338988 4519313 := bstep (se 2 (by rfl) ⟨1694742, by rfl⟩ : syracuseStep 4519313 = 3389485) B3389485
theorem B1340819 : Blo 1338988 1340819 := bstep (se 1 (by rfl) ⟨1005614, by rfl⟩ : syracuseStep 1340819 = 2011229) B2011229
theorem B1340835 : Blo 1338988 1340835 := bstep (se 1 (by rfl) ⟨1005626, by rfl⟩ : syracuseStep 1340835 = 2011253) B2011253
theorem B1340851 : Blo 1338988 1340851 := bstep (se 1 (by rfl) ⟨1005638, by rfl⟩ : syracuseStep 1340851 = 2011277) B2011277
theorem B2545091 : Blo 1338988 2545091 := bstep (se 1 (by rfl) ⟨1908818, by rfl⟩ : syracuseStep 2545091 = 3817637) B3817637
theorem B1340867 : Blo 1338988 1340867 := bstep (se 1 (by rfl) ⟨1005650, by rfl⟩ : syracuseStep 1340867 = 2011301) B2011301
theorem B2414033 : Blo 1338988 2414033 := bstep (se 2 (by rfl) ⟨905262, by rfl⟩ : syracuseStep 2414033 = 1810525) B1810525
theorem B1340883 : Blo 1338988 1340883 := bstep (se 1 (by rfl) ⟨1005662, by rfl⟩ : syracuseStep 1340883 = 2011325) B2011325
theorem B1340899 : Blo 1338988 1340899 := bstep (se 1 (by rfl) ⟨1005674, by rfl⟩ : syracuseStep 1340899 = 2011349) B2011349
theorem B1340915 : Blo 1338988 1340915 := bstep (se 1 (by rfl) ⟨1005686, by rfl⟩ : syracuseStep 1340915 = 2011373) B2011373
theorem B1340931 : Blo 1338988 1340931 := bstep (se 1 (by rfl) ⟨1005698, by rfl⟩ : syracuseStep 1340931 = 2011397) B2011397
theorem B1340947 : Blo 1338988 1340947 := bstep (se 1 (by rfl) ⟨1005710, by rfl⟩ : syracuseStep 1340947 = 2011421) B2011421
theorem B1340963 : Blo 1338988 1340963 := bstep (se 1 (by rfl) ⟨1005722, by rfl⟩ : syracuseStep 1340963 = 2011445) B2011445
theorem B1340979 : Blo 1338988 1340979 := bstep (se 1 (by rfl) ⟨1005734, by rfl⟩ : syracuseStep 1340979 = 2011469) B2011469
theorem B7730765 : Blo 1338988 7730765 := bstep (se 3 (by rfl) ⟨1449518, by rfl⟩ : syracuseStep 7730765 = 2899037) B2899037
theorem B4830833 : Blo 1338988 4830833 := bstep (se 2 (by rfl) ⟨1811562, by rfl⟩ : syracuseStep 4830833 = 3623125) B3623125
theorem B8148721 : Blo 1338988 8148721 := bstep (se 2 (by rfl) ⟨3055770, by rfl⟩ : syracuseStep 8148721 = 6111541) B6111541
theorem B2037521 : Blo 1338988 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B2324257 : Blo 1338988 2324257 := bstep (se 2 (by rfl) ⟨871596, by rfl⟩ : syracuseStep 2324257 = 1743193) B1743193
theorem B4290371 : Blo 1338988 4290371 := bstep (se 1 (by rfl) ⟨3217778, by rfl⟩ : syracuseStep 4290371 = 6435557) B6435557
theorem B10868593 : Blo 1338988 10868593 := bstep (se 2 (by rfl) ⟨4075722, by rfl⟩ : syracuseStep 10868593 = 8151445) B8151445
theorem B1431443 : Blo 1338988 1431443 := bstep (se 1 (by rfl) ⟨1073582, by rfl⟩ : syracuseStep 1431443 = 2147165) B2147165
theorem B4519853 : Blo 1338988 4519853 := bstep (se 3 (by rfl) ⟨847472, by rfl⟩ : syracuseStep 4519853 = 1694945) B1694945
theorem B6191075 : Blo 1338988 6191075 := bstep (se 1 (by rfl) ⟨4643306, by rfl⟩ : syracuseStep 6191075 = 9286613) B9286613
theorem B4519907 : Blo 1338988 4519907 := bstep (se 1 (by rfl) ⟨3389930, by rfl⟩ : syracuseStep 4519907 = 6779861) B6779861
theorem B4413521 : Blo 1338988 4413521 := bstep (se 2 (by rfl) ⟨1655070, by rfl⟩ : syracuseStep 4413521 = 3310141) B3310141
theorem B3012785 : Blo 1338988 3012785 := bstep (se 2 (by rfl) ⟨1129794, by rfl⟩ : syracuseStep 3012785 = 2259589) B2259589
theorem B3012803 : Blo 1338988 3012803 := bstep (se 1 (by rfl) ⟨2259602, by rfl⟩ : syracuseStep 3012803 = 4519205) B4519205
theorem B9173197 : Blo 1338988 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B4520177 : Blo 1338988 4520177 := bstep (se 2 (by rfl) ⟨1695066, by rfl⟩ : syracuseStep 4520177 = 3390133) B3390133
theorem B7248197 : Blo 1338988 7248197 := bstep (se 4 (by rfl) ⟨679518, by rfl⟩ : syracuseStep 7248197 = 1359037) B1359037
theorem B4962637 : Blo 1338988 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B7739725 : Blo 1338988 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B3389809 : Blo 1338988 3389809 := bstep (se 2 (by rfl) ⟨1271178, by rfl⟩ : syracuseStep 3389809 = 2542357) B2542357
theorem B1907059 : Blo 1338988 1907059 := bstep (se 1 (by rfl) ⟨1430294, by rfl⟩ : syracuseStep 1907059 = 2860589) B2860589
theorem B2292131 : Blo 1338988 2292131 := bstep (se 1 (by rfl) ⟨1719098, by rfl⟩ : syracuseStep 2292131 = 3438197) B3438197
theorem B3013073 : Blo 1338988 3013073 := bstep (se 2 (by rfl) ⟨1129902, by rfl⟩ : syracuseStep 3013073 = 2259805) B2259805
theorem B1907155 : Blo 1338988 1907155 := bstep (se 1 (by rfl) ⟨1430366, by rfl⟩ : syracuseStep 1907155 = 2860733) B2860733
theorem B3013091 : Blo 1338988 3013091 := bstep (se 1 (by rfl) ⟨2259818, by rfl⟩ : syracuseStep 3013091 = 4519637) B4519637
theorem B2292227 : Blo 1338988 2292227 := bstep (se 1 (by rfl) ⟨1719170, by rfl⟩ : syracuseStep 2292227 = 3438341) B3438341
theorem B4831757 : Blo 1338988 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B3619363 : Blo 1338988 3619363 := bstep (se 1 (by rfl) ⟨2714522, by rfl⟩ : syracuseStep 3619363 = 5429045) B5429045
theorem B2259569 : Blo 1338988 2259569 := bstep (se 2 (by rfl) ⟨847338, by rfl⟩ : syracuseStep 2259569 = 1694677) B1694677
theorem B2144897 : Blo 1338988 2144897 := bstep (se 2 (by rfl) ⟨804336, by rfl⟩ : syracuseStep 2144897 = 1608673) B1608673
theorem B3390083 : Blo 1338988 3390083 := bstep (se 1 (by rfl) ⟨2542562, by rfl⟩ : syracuseStep 3390083 = 5085125) B5085125
theorem B7633541 : Blo 1338988 7633541 := bstep (se 4 (by rfl) ⟨715644, by rfl⟩ : syracuseStep 7633541 = 1431289) B1431289
theorem B2259697 : Blo 1338988 2259697 := bstep (se 2 (by rfl) ⟨847386, by rfl⟩ : syracuseStep 2259697 = 1694773) B1694773
theorem B3013361 : Blo 1338988 3013361 := bstep (se 2 (by rfl) ⟨1130010, by rfl⟩ : syracuseStep 3013361 = 2260021) B2260021
theorem B3013379 : Blo 1338988 3013379 := bstep (se 1 (by rfl) ⟨2260034, by rfl⟩ : syracuseStep 3013379 = 4520069) B4520069
theorem B4520717 : Blo 1338988 4520717 := bstep (se 3 (by rfl) ⟨847634, by rfl⟩ : syracuseStep 4520717 = 1695269) B1695269
theorem B2259731 : Blo 1338988 2259731 := bstep (se 1 (by rfl) ⟨1694798, by rfl⟩ : syracuseStep 2259731 = 3389597) B3389597
theorem B2145089 : Blo 1338988 2145089 := bstep (se 2 (by rfl) ⟨804408, by rfl⟩ : syracuseStep 2145089 = 1608817) B1608817
theorem B3390275 : Blo 1338988 3390275 := bstep (se 1 (by rfl) ⟨2542706, by rfl⟩ : syracuseStep 3390275 = 5085413) B5085413
theorem B4520771 : Blo 1338988 4520771 := bstep (se 1 (by rfl) ⟨3390578, by rfl⟩ : syracuseStep 4520771 = 6781157) B6781157
theorem B3816305 : Blo 1338988 3816305 := bstep (se 2 (by rfl) ⟨1431114, by rfl⟩ : syracuseStep 3816305 = 2862229) B2862229
theorem B2259859 : Blo 1338988 2259859 := bstep (se 1 (by rfl) ⟨1694894, by rfl⟩ : syracuseStep 2259859 = 3389789) B3389789
theorem B2145217 : Blo 1338988 2145217 := bstep (se 2 (by rfl) ⟨804456, by rfl⟩ : syracuseStep 2145217 = 1608913) B1608913
theorem B1907651 : Blo 1338988 1907651 := bstep (se 1 (by rfl) ⟨1430738, by rfl⟩ : syracuseStep 1907651 = 2861477) B2861477
theorem B2038787 : Blo 1338988 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B3013649 : Blo 1338988 3013649 := bstep (se 2 (by rfl) ⟨1130118, by rfl⟩ : syracuseStep 3013649 = 2260237) B2260237
theorem B2260001 : Blo 1338988 2260001 := bstep (se 2 (by rfl) ⟨847500, by rfl⟩ : syracuseStep 2260001 = 1695001) B1695001
theorem B3013667 : Blo 1338988 3013667 := bstep (se 1 (by rfl) ⟨2260250, by rfl⟩ : syracuseStep 3013667 = 4520501) B4520501
theorem B3816497 : Blo 1338988 3816497 := bstep (se 2 (by rfl) ⟨1431186, by rfl⟩ : syracuseStep 3816497 = 2862373) B2862373
theorem B7633997 : Blo 1338988 7633997 := bstep (se 3 (by rfl) ⟨1431374, by rfl⟩ : syracuseStep 7633997 = 2862749) B2862749
theorem B4521041 : Blo 1338988 4521041 := bstep (se 2 (by rfl) ⟨1695390, by rfl⟩ : syracuseStep 4521041 = 3390781) B3390781
theorem B1506451 : Blo 1338988 1506451 := bstep (se 1 (by rfl) ⟨1129838, by rfl⟩ : syracuseStep 1506451 = 2259677) B2259677
theorem B2260129 : Blo 1338988 2260129 := bstep (se 2 (by rfl) ⟨847548, by rfl⟩ : syracuseStep 2260129 = 1695097) B1695097
theorem B5086385 : Blo 1338988 5086385 := bstep (se 2 (by rfl) ⟨1907394, by rfl⟩ : syracuseStep 5086385 = 3814789) B3814789
theorem B6782129 : Blo 1338988 6782129 := bstep (se 2 (by rfl) ⟨2543298, by rfl⟩ : syracuseStep 6782129 = 5086597) B5086597
theorem B2260163 : Blo 1338988 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1506595 : Blo 1338988 1506595 := bstep (se 1 (by rfl) ⟨1129946, by rfl⟩ : syracuseStep 1506595 = 2259893) B2259893
theorem B3013937 : Blo 1338988 3013937 := bstep (se 2 (by rfl) ⟨1130226, by rfl⟩ : syracuseStep 3013937 = 2260453) B2260453
theorem B2260291 : Blo 1338988 2260291 := bstep (se 1 (by rfl) ⟨1695218, by rfl⟩ : syracuseStep 2260291 = 3390437) B3390437
theorem B3013955 : Blo 1338988 3013955 := bstep (se 1 (by rfl) ⟨2260466, by rfl⟩ : syracuseStep 3013955 = 4520933) B4520933
theorem B13745477 : Blo 1338988 13745477 := bstep (se 4 (by rfl) ⟨1288638, by rfl⟩ : syracuseStep 13745477 = 2577277) B2577277
theorem B1695107 : Blo 1338988 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B1809811 : Blo 1338988 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B1506739 : Blo 1338988 1506739 := bstep (se 1 (by rfl) ⟨1130054, by rfl⟩ : syracuseStep 1506739 = 2260109) B2260109
theorem B2260433 : Blo 1338988 2260433 := bstep (se 2 (by rfl) ⟨847662, by rfl⟩ : syracuseStep 2260433 = 1695325) B1695325
theorem B10173923 : Blo 1338988 10173923 := bstep (se 1 (by rfl) ⟨7630442, by rfl⟩ : syracuseStep 10173923 = 15260885) B15260885
theorem B2145857 : Blo 1338988 2145857 := bstep (se 2 (by rfl) ⟨804696, by rfl⟩ : syracuseStep 2145857 = 1609393) B1609393
theorem B1506883 : Blo 1338988 1506883 := bstep (se 1 (by rfl) ⟨1130162, by rfl⟩ : syracuseStep 1506883 = 2260325) B2260325
theorem B1908289 : Blo 1338988 1908289 := bstep (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) B1431217
theorem B2260561 : Blo 1338988 2260561 := bstep (se 2 (by rfl) ⟨847710, by rfl⟩ : syracuseStep 2260561 = 1695421) B1695421
theorem B3014225 : Blo 1338988 3014225 := bstep (se 2 (by rfl) ⟨1130334, by rfl⟩ : syracuseStep 3014225 = 2260669) B2260669
theorem B3014243 : Blo 1338988 3014243 := bstep (se 1 (by rfl) ⟨2260682, by rfl⟩ : syracuseStep 3014243 = 4521365) B4521365
theorem B4521581 : Blo 1338988 4521581 := bstep (se 3 (by rfl) ⟨847796, by rfl⟩ : syracuseStep 4521581 = 1695593) B1695593
theorem B2260595 : Blo 1338988 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B4292227 : Blo 1338988 4292227 := bstep (se 1 (by rfl) ⟨3219170, by rfl⟩ : syracuseStep 4292227 = 6438341) B6438341
theorem B4832909 : Blo 1338988 4832909 := bstep (se 3 (by rfl) ⟨906170, by rfl⟩ : syracuseStep 4832909 = 1812341) B1812341
theorem B4521635 : Blo 1338988 4521635 := bstep (se 1 (by rfl) ⟨3391226, by rfl⟩ : syracuseStep 4521635 = 6782453) B6782453
theorem B1507027 : Blo 1338988 1507027 := bstep (se 1 (by rfl) ⟨1130270, by rfl⟩ : syracuseStep 1507027 = 2260541) B2260541
theorem B3391217 : Blo 1338988 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B2260723 : Blo 1338988 2260723 := bstep (se 1 (by rfl) ⟨1695542, by rfl⟩ : syracuseStep 2260723 = 3391085) B3391085
theorem B3391267 : Blo 1338988 3391267 := bstep (se 1 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 3391267 = 5086901) B5086901
theorem B8257315 : Blo 1338988 8257315 := bstep (se 1 (by rfl) ⟨6192986, by rfl⟩ : syracuseStep 8257315 = 12385973) B12385973
theorem B1507171 : Blo 1338988 1507171 := bstep (se 1 (by rfl) ⟨1130378, by rfl⟩ : syracuseStep 1507171 = 2260757) B2260757
theorem B2416483 : Blo 1338988 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B3014513 : Blo 1338988 3014513 := bstep (se 2 (by rfl) ⟨1130442, by rfl⟩ : syracuseStep 3014513 = 2260885) B2260885
theorem B2260865 : Blo 1338988 2260865 := bstep (se 2 (by rfl) ⟨847824, by rfl⟩ : syracuseStep 2260865 = 1695649) B1695649
theorem B3014531 : Blo 1338988 3014531 := bstep (se 1 (by rfl) ⟨2260898, by rfl⟩ : syracuseStep 3014531 = 4521797) B4521797
theorem B1908625 : Blo 1338988 1908625 := bstep (se 2 (by rfl) ⟨715734, by rfl⟩ : syracuseStep 1908625 = 1431469) B1431469
theorem B3391409 : Blo 1338988 3391409 := bstep (se 2 (by rfl) ⟨1271778, by rfl⟩ : syracuseStep 3391409 = 2543557) B2543557
theorem B4521905 : Blo 1338988 4521905 := bstep (se 2 (by rfl) ⟨1695714, by rfl⟩ : syracuseStep 4521905 = 3391429) B3391429
theorem B1507315 : Blo 1338988 1507315 := bstep (se 1 (by rfl) ⟨1130486, by rfl⟩ : syracuseStep 1507315 = 2260973) B2260973
theorem B3014657 : Blo 1338988 3014657 := bstep (se 2 (by rfl) ⟨1130496, by rfl⟩ : syracuseStep 3014657 = 2260993) B2260993
theorem B1695755 : Blo 1338988 1695755 := bstep (se 1 (by rfl) ⟨1271816, by rfl⟩ : syracuseStep 1695755 = 2543633) B2543633
theorem B3670039 : Blo 1338988 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B1507351 : Blo 1338988 1507351 := bstep (se 1 (by rfl) ⟨1130513, by rfl⟩ : syracuseStep 1507351 = 2261027) B2261027
theorem B3219479 : Blo 1338988 3219479 := bstep (se 1 (by rfl) ⟨2414609, by rfl⟩ : syracuseStep 3219479 = 4829219) B4829219
theorem B3817523 : Blo 1338988 3817523 := bstep (se 1 (by rfl) ⟨2863142, by rfl⟩ : syracuseStep 3817523 = 5726285) B5726285
theorem B2261081 : Blo 1338988 2261081 := bstep (se 2 (by rfl) ⟨847905, by rfl⟩ : syracuseStep 2261081 = 1695811) B1695811
theorem B10862693 : Blo 1338988 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B1507531 : Blo 1338988 1507531 := bstep (se 1 (by rfl) ⟨1130648, by rfl⟩ : syracuseStep 1507531 = 2261297) B2261297
theorem B3014873 : Blo 1338988 3014873 := bstep (se 2 (by rfl) ⟨1130577, by rfl⟩ : syracuseStep 3014873 = 2261155) B2261155
theorem B2261209 : Blo 1338988 2261209 := bstep (se 2 (by rfl) ⟨847953, by rfl⟩ : syracuseStep 2261209 = 1695907) B1695907
theorem B12230929 : Blo 1338988 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B3014963 : Blo 1338988 3014963 := bstep (se 1 (by rfl) ⟨2261222, by rfl⟩ : syracuseStep 3014963 = 4522445) B4522445
theorem B1507639 : Blo 1338988 1507639 := bstep (se 1 (by rfl) ⟨1130729, by rfl⟩ : syracuseStep 1507639 = 2261459) B2261459
theorem B3014999 : Blo 1338988 3014999 := bstep (se 1 (by rfl) ⟨2261249, by rfl⟩ : syracuseStep 3014999 = 4522499) B4522499
theorem B4522391 : Blo 1338988 4522391 := bstep (se 1 (by rfl) ⟨3391793, by rfl⟩ : syracuseStep 4522391 = 6783587) B6783587
theorem B3391895 : Blo 1338988 3391895 := bstep (se 1 (by rfl) ⟨2543921, by rfl⟩ : syracuseStep 3391895 = 5087843) B5087843
theorem B1507819 : Blo 1338988 1507819 := bstep (se 1 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 1507819 = 2261729) B2261729
theorem B3015179 : Blo 1338988 3015179 := bstep (se 1 (by rfl) ⟨2261384, by rfl⟩ : syracuseStep 3015179 = 4522769) B4522769
theorem B3015233 : Blo 1338988 3015233 := bstep (se 2 (by rfl) ⟨1130712, by rfl⟩ : syracuseStep 3015233 = 2261425) B2261425
theorem B1507927 : Blo 1338988 1507927 := bstep (se 1 (by rfl) ⟨1130945, by rfl⟩ : syracuseStep 1507927 = 2261891) B2261891
theorem B22889141 : Blo 1338988 22889141 := bstep (se 5 (by rfl) ⟨1072928, by rfl⟩ : syracuseStep 22889141 = 2145857) B2145857
theorem B1696459 : Blo 1338988 1696459 := bstep (se 1 (by rfl) ⟨1272344, by rfl⟩ : syracuseStep 1696459 = 2544689) B2544689
theorem B4825817 : Blo 1338988 4825817 := bstep (se 2 (by rfl) ⟨1809681, by rfl⟩ : syracuseStep 4825817 = 3619363) B3619363
theorem B1508107 : Blo 1338988 1508107 := bstep (se 1 (by rfl) ⟨1131080, by rfl⟩ : syracuseStep 1508107 = 2262161) B2262161
theorem B2261783 : Blo 1338988 2261783 := bstep (se 1 (by rfl) ⟨1696337, by rfl⟩ : syracuseStep 2261783 = 3392675) B3392675
theorem B3015449 : Blo 1338988 3015449 := bstep (se 2 (by rfl) ⟨1130793, by rfl⟩ : syracuseStep 3015449 = 2261587) B2261587
theorem B3015539 : Blo 1338988 3015539 := bstep (se 1 (by rfl) ⟨2261654, by rfl⟩ : syracuseStep 3015539 = 4523309) B4523309
theorem B1508215 : Blo 1338988 1508215 := bstep (se 1 (by rfl) ⟨1131161, by rfl⟩ : syracuseStep 1508215 = 2262323) B2262323
theorem B3015575 : Blo 1338988 3015575 := bstep (se 1 (by rfl) ⟨2261681, by rfl⟩ : syracuseStep 3015575 = 4523363) B4523363
theorem B2261911 : Blo 1338988 2261911 := bstep (se 1 (by rfl) ⟨1696433, by rfl⟩ : syracuseStep 2261911 = 3392867) B3392867
theorem B4522931 : Blo 1338988 4522931 := bstep (se 1 (by rfl) ⟨3392198, by rfl⟩ : syracuseStep 4522931 = 6784397) B6784397
theorem B1696727 : Blo 1338988 1696727 := bstep (se 1 (by rfl) ⟨1272545, by rfl⟩ : syracuseStep 1696727 = 2545091) B2545091
theorem B25748441 : Blo 1338988 25748441 := bstep (se 2 (by rfl) ⟨9655665, by rfl⟩ : syracuseStep 25748441 = 19311331) B19311331
theorem B1508395 : Blo 1338988 1508395 := bstep (se 1 (by rfl) ⟨1131296, by rfl⟩ : syracuseStep 1508395 = 2262593) B2262593
theorem B5153843 : Blo 1338988 5153843 := bstep (se 1 (by rfl) ⟨3865382, by rfl⟩ : syracuseStep 5153843 = 7730765) B7730765
theorem B3392563 : Blo 1338988 3392563 := bstep (se 1 (by rfl) ⟨2544422, by rfl⟩ : syracuseStep 3392563 = 5088845) B5088845
theorem B3015755 : Blo 1338988 3015755 := bstep (se 1 (by rfl) ⟨2261816, by rfl⟩ : syracuseStep 3015755 = 4523633) B4523633
theorem B3220555 : Blo 1338988 3220555 := bstep (se 1 (by rfl) ⟨2415416, by rfl⟩ : syracuseStep 3220555 = 4830833) B4830833
theorem B3015809 : Blo 1338988 3015809 := bstep (se 2 (by rfl) ⟨1130928, by rfl⟩ : syracuseStep 3015809 = 2261857) B2261857
theorem B1508503 : Blo 1338988 1508503 := bstep (se 1 (by rfl) ⟨1131377, by rfl⟩ : syracuseStep 1508503 = 2262755) B2262755
theorem B4523201 : Blo 1338988 4523201 := bstep (se 2 (by rfl) ⟨1696200, by rfl⟩ : syracuseStep 4523201 = 3392401) B3392401
theorem B3392705 : Blo 1338988 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B2860247 : Blo 1338988 2860247 := bstep (se 1 (by rfl) ⟨2145185, by rfl⟩ : syracuseStep 2860247 = 4290371) B4290371
theorem B2860289 : Blo 1338988 2860289 := bstep (se 2 (by rfl) ⟨1072608, by rfl⟩ : syracuseStep 2860289 = 2145217) B2145217
theorem B17171777 : Blo 1338988 17171777 := bstep (se 2 (by rfl) ⟨6439416, by rfl⟩ : syracuseStep 17171777 = 12878833) B12878833
theorem B3016025 : Blo 1338988 3016025 := bstep (se 2 (by rfl) ⟨1131009, by rfl⟩ : syracuseStep 3016025 = 2262019) B2262019
theorem B2942347 : Blo 1338988 2942347 := bstep (se 1 (by rfl) ⟨2206760, by rfl⟩ : syracuseStep 2942347 = 4413521) B4413521
theorem B3016115 : Blo 1338988 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B2008523 : Blo 1338988 2008523 := bstep (se 1 (by rfl) ⟨1506392, by rfl⟩ : syracuseStep 2008523 = 3012785) B3012785
theorem B2008535 : Blo 1338988 2008535 := bstep (se 1 (by rfl) ⟨1506401, by rfl⟩ : syracuseStep 2008535 = 3012803) B3012803
theorem B3016151 : Blo 1338988 3016151 := bstep (se 1 (by rfl) ⟨2262113, by rfl⟩ : syracuseStep 3016151 = 4524227) B4524227
theorem B12396037 : Blo 1338988 12396037 := bstep (se 4 (by rfl) ⟨1162128, by rfl⟩ : syracuseStep 12396037 = 2324257) B2324257
theorem B2262539 : Blo 1338988 2262539 := bstep (se 1 (by rfl) ⟨1696904, by rfl⟩ : syracuseStep 2262539 = 3393809) B3393809
theorem B2008601 : Blo 1338988 2008601 := bstep (se 2 (by rfl) ⟨753225, by rfl⟩ : syracuseStep 2008601 = 1506451) B1506451
theorem B3868249 : Blo 1338988 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B2008715 : Blo 1338988 2008715 := bstep (se 1 (by rfl) ⟨1506536, by rfl⟩ : syracuseStep 2008715 = 3013073) B3013073
theorem B3016331 : Blo 1338988 3016331 := bstep (se 1 (by rfl) ⟨2262248, by rfl⟩ : syracuseStep 3016331 = 4524497) B4524497
theorem B2262667 : Blo 1338988 2262667 := bstep (se 1 (by rfl) ⟨1697000, by rfl⟩ : syracuseStep 2262667 = 3394001) B3394001
theorem B2008727 : Blo 1338988 2008727 := bstep (se 1 (by rfl) ⟨1506545, by rfl⟩ : syracuseStep 2008727 = 3013091) B3013091
theorem B3221171 : Blo 1338988 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B3016385 : Blo 1338988 3016385 := bstep (se 2 (by rfl) ⟨1131144, by rfl⟩ : syracuseStep 3016385 = 2262289) B2262289
theorem B2008793 : Blo 1338988 2008793 := bstep (se 2 (by rfl) ⟨753297, by rfl⟩ : syracuseStep 2008793 = 1506595) B1506595
theorem B7243481 : Blo 1338988 7243481 := bstep (se 2 (by rfl) ⟨2716305, by rfl⟩ : syracuseStep 7243481 = 5432611) B5432611
theorem B4523741 : Blo 1338988 4523741 := bstep (se 3 (by rfl) ⟨848201, by rfl⟩ : syracuseStep 4523741 = 1696403) B1696403
theorem B5089027 : Blo 1338988 5089027 := bstep (se 1 (by rfl) ⟨3816770, by rfl⟩ : syracuseStep 5089027 = 7633541) B7633541
theorem B5719825 : Blo 1338988 5719825 := bstep (se 2 (by rfl) ⟨2144934, by rfl⟩ : syracuseStep 5719825 = 4289869) B4289869
theorem B2262809 : Blo 1338988 2262809 := bstep (se 2 (by rfl) ⟨848553, by rfl⟩ : syracuseStep 2262809 = 1697107) B1697107
theorem B2008907 : Blo 1338988 2008907 := bstep (se 1 (by rfl) ⟨1506680, by rfl⟩ : syracuseStep 2008907 = 3013361) B3013361
theorem B2008919 : Blo 1338988 2008919 := bstep (se 1 (by rfl) ⟨1506689, by rfl⟩ : syracuseStep 2008919 = 3013379) B3013379
theorem B61917029 : Blo 1338988 61917029 := bstep (se 4 (by rfl) ⟨5804721, by rfl⟩ : syracuseStep 61917029 = 11609443) B11609443
theorem B12887909 : Blo 1338988 12887909 := bstep (se 4 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 12887909 = 2416483) B2416483
theorem B2008985 : Blo 1338988 2008985 := bstep (se 2 (by rfl) ⟨753369, by rfl⟩ : syracuseStep 2008985 = 1506739) B1506739
theorem B3016601 : Blo 1338988 3016601 := bstep (se 2 (by rfl) ⟨1131225, by rfl⟩ : syracuseStep 3016601 = 2262451) B2262451
theorem B21718961 : Blo 1338988 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B3016691 : Blo 1338988 3016691 := bstep (se 1 (by rfl) ⟨2262518, by rfl⟩ : syracuseStep 3016691 = 4525037) B4525037
theorem B2009099 : Blo 1338988 2009099 := bstep (se 1 (by rfl) ⟨1506824, by rfl⟩ : syracuseStep 2009099 = 3013649) B3013649
theorem B2009111 : Blo 1338988 2009111 := bstep (se 1 (by rfl) ⟨1506833, by rfl⟩ : syracuseStep 2009111 = 3013667) B3013667
theorem B3016727 : Blo 1338988 3016727 := bstep (se 1 (by rfl) ⟨2262545, by rfl⟩ : syracuseStep 3016727 = 4525091) B4525091
theorem B5433389 : Blo 1338988 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B5089331 : Blo 1338988 5089331 := bstep (se 1 (by rfl) ⟨3816998, by rfl⟩ : syracuseStep 5089331 = 7633997) B7633997
theorem B2009177 : Blo 1338988 2009177 := bstep (se 2 (by rfl) ⟨753441, by rfl⟩ : syracuseStep 2009177 = 1506883) B1506883
theorem B1394807 : Blo 1338988 1394807 := bstep (se 1 (by rfl) ⟨1046105, by rfl⟩ : syracuseStep 1394807 = 2092211) B2092211
theorem B2009291 : Blo 1338988 2009291 := bstep (se 1 (by rfl) ⟨1506968, by rfl⟩ : syracuseStep 2009291 = 3013937) B3013937
theorem B3016907 : Blo 1338988 3016907 := bstep (se 1 (by rfl) ⟨2262680, by rfl⟩ : syracuseStep 3016907 = 4525361) B4525361
theorem B2009303 : Blo 1338988 2009303 := bstep (se 1 (by rfl) ⟨1506977, by rfl⟩ : syracuseStep 2009303 = 3013955) B3013955
theorem B2615513 : Blo 1338988 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B3016961 : Blo 1338988 3016961 := bstep (se 2 (by rfl) ⟨1131360, by rfl⟩ : syracuseStep 3016961 = 2262721) B2262721
theorem B2009369 : Blo 1338988 2009369 := bstep (se 2 (by rfl) ⟨753513, by rfl⟩ : syracuseStep 2009369 = 1507027) B1507027
theorem B10864961 : Blo 1338988 10864961 := bstep (se 2 (by rfl) ⟨4074360, by rfl⟩ : syracuseStep 10864961 = 8148721) B8148721
theorem B2009483 : Blo 1338988 2009483 := bstep (se 1 (by rfl) ⟨1507112, by rfl⟩ : syracuseStep 2009483 = 3014225) B3014225
theorem B2009495 : Blo 1338988 2009495 := bstep (se 1 (by rfl) ⟨1507121, by rfl⟩ : syracuseStep 2009495 = 3014243) B3014243
theorem B3393971 : Blo 1338988 3393971 := bstep (se 1 (by rfl) ⟨2545478, by rfl⟩ : syracuseStep 3393971 = 5090957) B5090957
theorem B3221939 : Blo 1338988 3221939 := bstep (se 1 (by rfl) ⟨2416454, by rfl⟩ : syracuseStep 3221939 = 4832909) B4832909
theorem B2009561 : Blo 1338988 2009561 := bstep (se 2 (by rfl) ⟨753585, by rfl⟩ : syracuseStep 2009561 = 1507171) B1507171
theorem B3017177 : Blo 1338988 3017177 := bstep (se 2 (by rfl) ⟨1131441, by rfl⟩ : syracuseStep 3017177 = 2262883) B2262883
theorem B2009675 : Blo 1338988 2009675 := bstep (se 1 (by rfl) ⟨1507256, by rfl⟩ : syracuseStep 2009675 = 3014513) B3014513
theorem B2009687 : Blo 1338988 2009687 := bstep (se 1 (by rfl) ⟨1507265, by rfl⟩ : syracuseStep 2009687 = 3014531) B3014531
theorem B49572445 : Blo 1338988 49572445 := bstep (se 3 (by rfl) ⟨9294833, by rfl⟩ : syracuseStep 49572445 = 18589667) B18589667
theorem B2009753 : Blo 1338988 2009753 := bstep (se 2 (by rfl) ⟨753657, by rfl⟩ : syracuseStep 2009753 = 1507315) B1507315
theorem B2542259 : Blo 1338988 2542259 := bstep (se 1 (by rfl) ⟨1906694, by rfl⟩ : syracuseStep 2542259 = 3813389) B3813389
theorem B5089985 : Blo 1338988 5089985 := bstep (se 2 (by rfl) ⟨1908744, by rfl⟩ : syracuseStep 5089985 = 3817489) B3817489
theorem B5434073 : Blo 1338988 5434073 := bstep (se 2 (by rfl) ⟨2037777, by rfl⟩ : syracuseStep 5434073 = 4075555) B4075555
theorem B2009867 : Blo 1338988 2009867 := bstep (se 1 (by rfl) ⟨1507400, by rfl⟩ : syracuseStep 2009867 = 3014801) B3014801
theorem B2009879 : Blo 1338988 2009879 := bstep (se 1 (by rfl) ⟨1507409, by rfl⟩ : syracuseStep 2009879 = 3014819) B3014819
theorem B10177325 : Blo 1338988 10177325 := bstep (se 3 (by rfl) ⟨1908248, by rfl⟩ : syracuseStep 10177325 = 3816497) B3816497
theorem B4524875 : Blo 1338988 4524875 := bstep (se 1 (by rfl) ⟨3393656, by rfl⟩ : syracuseStep 4524875 = 6787313) B6787313
theorem B4893529 : Blo 1338988 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B2009945 : Blo 1338988 2009945 := bstep (se 2 (by rfl) ⟨753729, by rfl⟩ : syracuseStep 2009945 = 1507459) B1507459
theorem B1395595 : Blo 1338988 1395595 := bstep (se 1 (by rfl) ⟨1046696, by rfl⟩ : syracuseStep 1395595 = 2093393) B2093393
theorem B2010059 : Blo 1338988 2010059 := bstep (se 1 (by rfl) ⟨1507544, by rfl⟩ : syracuseStep 2010059 = 3015089) B3015089
theorem B2010071 : Blo 1338988 2010071 := bstep (se 1 (by rfl) ⟨1507553, by rfl⟩ : syracuseStep 2010071 = 3015107) B3015107
theorem B2010137 : Blo 1338988 2010137 := bstep (se 2 (by rfl) ⟨753801, by rfl⟩ : syracuseStep 2010137 = 1507603) B1507603
theorem B4525145 : Blo 1338988 4525145 := bstep (se 2 (by rfl) ⟨1696929, by rfl⟩ : syracuseStep 4525145 = 3393859) B3393859
theorem B6786179 : Blo 1338988 6786179 := bstep (se 1 (by rfl) ⟨5089634, by rfl⟩ : syracuseStep 6786179 = 10179269) B10179269
theorem B2010251 : Blo 1338988 2010251 := bstep (se 1 (by rfl) ⟨1507688, by rfl⟩ : syracuseStep 2010251 = 3015377) B3015377
theorem B2010263 : Blo 1338988 2010263 := bstep (se 1 (by rfl) ⟨1507697, by rfl⟩ : syracuseStep 2010263 = 3015395) B3015395
theorem B2542745 : Blo 1338988 2542745 := bstep (se 2 (by rfl) ⟨953529, by rfl⟩ : syracuseStep 2542745 = 1907059) B1907059
theorem B46402741 : Blo 1338988 46402741 := bstep (se 5 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 46402741 = 4350257) B4350257
theorem B10169549 : Blo 1338988 10169549 := bstep (se 3 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 10169549 = 3813581) B3813581
theorem B2010329 : Blo 1338988 2010329 := bstep (se 2 (by rfl) ⟨753873, by rfl⟩ : syracuseStep 2010329 = 1507747) B1507747
theorem B11439377 : Blo 1338988 11439377 := bstep (se 2 (by rfl) ⟨4289766, by rfl⟩ : syracuseStep 11439377 = 8579533) B8579533
theorem B2010443 : Blo 1338988 2010443 := bstep (se 1 (by rfl) ⟨1507832, by rfl⟩ : syracuseStep 2010443 = 3015665) B3015665
theorem B2010455 : Blo 1338988 2010455 := bstep (se 1 (by rfl) ⟨1507841, by rfl⟩ : syracuseStep 2010455 = 3015683) B3015683
theorem B2010521 : Blo 1338988 2010521 := bstep (se 2 (by rfl) ⟨753945, by rfl⟩ : syracuseStep 2010521 = 1507891) B1507891
theorem B2010635 : Blo 1338988 2010635 := bstep (se 1 (by rfl) ⟨1507976, by rfl⟩ : syracuseStep 2010635 = 3015953) B3015953
theorem B4075031 : Blo 1338988 4075031 := bstep (se 1 (by rfl) ⟨3056273, by rfl⟩ : syracuseStep 4075031 = 6112547) B6112547
theorem B2010647 : Blo 1338988 2010647 := bstep (se 1 (by rfl) ⟨1507985, by rfl⟩ : syracuseStep 2010647 = 3015971) B3015971
theorem B5434931 : Blo 1338988 5434931 := bstep (se 1 (by rfl) ⟨4076198, by rfl⟩ : syracuseStep 5434931 = 8152397) B8152397
theorem B2010713 : Blo 1338988 2010713 := bstep (se 2 (by rfl) ⟨754017, by rfl⟩ : syracuseStep 2010713 = 1508035) B1508035
theorem B14487133 : Blo 1338988 14487133 := bstep (se 3 (by rfl) ⟨2716337, by rfl⟩ : syracuseStep 14487133 = 5432675) B5432675
theorem B97807985 : Blo 1338988 97807985 := bstep (se 2 (by rfl) ⟨36677994, by rfl⟩ : syracuseStep 97807985 = 73355989) B73355989
theorem B1338999 : Blo 1338988 1338999 := bstep (se 1 (by rfl) ⟨1004249, by rfl⟩ : syracuseStep 1338999 = 2008499) B2008499
theorem B23539331 : Blo 1338988 23539331 := bstep (se 1 (by rfl) ⟨17654498, by rfl⟩ : syracuseStep 23539331 = 35308997) B35308997
theorem B1339019 : Blo 1338988 1339019 := bstep (se 1 (by rfl) ⟨1004264, by rfl⟩ : syracuseStep 1339019 = 2008529) B2008529
theorem B1609355 : Blo 1338988 1609355 := bstep (se 1 (by rfl) ⟨1207016, by rfl⟩ : syracuseStep 1609355 = 2414033) B2414033
theorem B1339031 : Blo 1338988 1339031 := bstep (se 1 (by rfl) ⟨1004273, by rfl⟩ : syracuseStep 1339031 = 2008547) B2008547
theorem B1339051 : Blo 1338988 1339051 := bstep (se 1 (by rfl) ⟨1004288, by rfl⟩ : syracuseStep 1339051 = 2008577) B2008577
theorem B10170035 : Blo 1338988 10170035 := bstep (se 1 (by rfl) ⟨7627526, by rfl⟩ : syracuseStep 10170035 = 15255053) B15255053
theorem B1339063 : Blo 1338988 1339063 := bstep (se 1 (by rfl) ⟨1004297, by rfl⟩ : syracuseStep 1339063 = 2008595) B2008595
theorem B1339083 : Blo 1338988 1339083 := bstep (se 1 (by rfl) ⟨1004312, by rfl⟩ : syracuseStep 1339083 = 2008625) B2008625
theorem B2010827 : Blo 1338988 2010827 := bstep (se 1 (by rfl) ⟨1508120, by rfl⟩ : syracuseStep 2010827 = 3016241) B3016241
theorem B1339095 : Blo 1338988 1339095 := bstep (se 1 (by rfl) ⟨1004321, by rfl⟩ : syracuseStep 1339095 = 2008643) B2008643
theorem B2010839 : Blo 1338988 2010839 := bstep (se 1 (by rfl) ⟨1508129, by rfl⟩ : syracuseStep 2010839 = 3016259) B3016259
theorem B8589017 : Blo 1338988 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B1339115 : Blo 1338988 1339115 := bstep (se 1 (by rfl) ⟨1004336, by rfl⟩ : syracuseStep 1339115 = 2008673) B2008673
theorem B1339127 : Blo 1338988 1339127 := bstep (se 1 (by rfl) ⟨1004345, by rfl⟩ : syracuseStep 1339127 = 2008691) B2008691
theorem B1339147 : Blo 1338988 1339147 := bstep (se 1 (by rfl) ⟨1004360, by rfl⟩ : syracuseStep 1339147 = 2008721) B2008721
theorem B1339159 : Blo 1338988 1339159 := bstep (se 1 (by rfl) ⟨1004369, by rfl⟩ : syracuseStep 1339159 = 2008739) B2008739
theorem B2010905 : Blo 1338988 2010905 := bstep (se 2 (by rfl) ⟨754089, by rfl⟩ : syracuseStep 2010905 = 1508179) B1508179
theorem B1339179 : Blo 1338988 1339179 := bstep (se 1 (by rfl) ⟨1004384, by rfl⟩ : syracuseStep 1339179 = 2008769) B2008769
theorem B1339191 : Blo 1338988 1339191 := bstep (se 1 (by rfl) ⟨1004393, by rfl⟩ : syracuseStep 1339191 = 2008787) B2008787
theorem B1339211 : Blo 1338988 1339211 := bstep (se 1 (by rfl) ⟨1004408, by rfl⟩ : syracuseStep 1339211 = 2008817) B2008817
theorem B1339223 : Blo 1338988 1339223 := bstep (se 1 (by rfl) ⟨1004417, by rfl⟩ : syracuseStep 1339223 = 2008835) B2008835
theorem B4829017 : Blo 1338988 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B1339243 : Blo 1338988 1339243 := bstep (se 1 (by rfl) ⟨1004432, by rfl⟩ : syracuseStep 1339243 = 2008865) B2008865
theorem B1339255 : Blo 1338988 1339255 := bstep (se 1 (by rfl) ⟨1004441, by rfl⟩ : syracuseStep 1339255 = 2008883) B2008883
theorem B1339275 : Blo 1338988 1339275 := bstep (se 1 (by rfl) ⟨1004456, by rfl⟩ : syracuseStep 1339275 = 2008913) B2008913
theorem B2011019 : Blo 1338988 2011019 := bstep (se 1 (by rfl) ⟨1508264, by rfl⟩ : syracuseStep 2011019 = 3016529) B3016529
theorem B1339287 : Blo 1338988 1339287 := bstep (se 1 (by rfl) ⟨1004465, by rfl⟩ : syracuseStep 1339287 = 2008931) B2008931
theorem B2011031 : Blo 1338988 2011031 := bstep (se 1 (by rfl) ⟨1508273, by rfl⟩ : syracuseStep 2011031 = 3016547) B3016547
theorem B1339307 : Blo 1338988 1339307 := bstep (se 1 (by rfl) ⟨1004480, by rfl⟩ : syracuseStep 1339307 = 2008961) B2008961
theorem B4829101 : Blo 1338988 4829101 := bstep (se 3 (by rfl) ⟨905456, by rfl⟩ : syracuseStep 4829101 = 1810913) B1810913
theorem B5091245 : Blo 1338988 5091245 := bstep (se 3 (by rfl) ⟨954608, by rfl⟩ : syracuseStep 5091245 = 1909217) B1909217
theorem B1339319 : Blo 1338988 1339319 := bstep (se 1 (by rfl) ⟨1004489, by rfl⟩ : syracuseStep 1339319 = 2008979) B2008979
theorem B1339339 : Blo 1338988 1339339 := bstep (se 1 (by rfl) ⟨1004504, by rfl⟩ : syracuseStep 1339339 = 2009009) B2009009
theorem B10858445 : Blo 1338988 10858445 := bstep (se 3 (by rfl) ⟨2035958, by rfl⟩ : syracuseStep 10858445 = 4071917) B4071917
theorem B5091275 : Blo 1338988 5091275 := bstep (se 1 (by rfl) ⟨3818456, by rfl⟩ : syracuseStep 5091275 = 7636913) B7636913
theorem B1339351 : Blo 1338988 1339351 := bstep (se 1 (by rfl) ⟨1004513, by rfl⟩ : syracuseStep 1339351 = 2009027) B2009027
theorem B2011097 : Blo 1338988 2011097 := bstep (se 2 (by rfl) ⟨754161, by rfl⟩ : syracuseStep 2011097 = 1508323) B1508323
theorem B1339371 : Blo 1338988 1339371 := bstep (se 1 (by rfl) ⟨1004528, by rfl⟩ : syracuseStep 1339371 = 2009057) B2009057
theorem B1339383 : Blo 1338988 1339383 := bstep (se 1 (by rfl) ⟨1004537, by rfl⟩ : syracuseStep 1339383 = 2009075) B2009075
theorem B1339403 : Blo 1338988 1339403 := bstep (se 1 (by rfl) ⟨1004552, by rfl⟩ : syracuseStep 1339403 = 2009105) B2009105
theorem B1339415 : Blo 1338988 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B1339435 : Blo 1338988 1339435 := bstep (se 1 (by rfl) ⟨1004576, by rfl⟩ : syracuseStep 1339435 = 2009153) B2009153
theorem B1339447 : Blo 1338988 1339447 := bstep (se 1 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 1339447 = 2009171) B2009171
theorem B1339467 : Blo 1338988 1339467 := bstep (se 1 (by rfl) ⟨1004600, by rfl⟩ : syracuseStep 1339467 = 2009201) B2009201
theorem B2011211 : Blo 1338988 2011211 := bstep (se 1 (by rfl) ⟨1508408, by rfl⟩ : syracuseStep 2011211 = 3016817) B3016817
theorem B1339479 : Blo 1338988 1339479 := bstep (se 1 (by rfl) ⟨1004609, by rfl⟩ : syracuseStep 1339479 = 2009219) B2009219
theorem B2863193 : Blo 1338988 2863193 := bstep (se 2 (by rfl) ⟨1073697, by rfl⟩ : syracuseStep 2863193 = 2147395) B2147395
theorem B2011223 : Blo 1338988 2011223 := bstep (se 1 (by rfl) ⟨1508417, by rfl⟩ : syracuseStep 2011223 = 3016835) B3016835
theorem B1339499 : Blo 1338988 1339499 := bstep (se 1 (by rfl) ⟨1004624, by rfl⟩ : syracuseStep 1339499 = 2009249) B2009249
theorem B1339511 : Blo 1338988 1339511 := bstep (se 1 (by rfl) ⟨1004633, by rfl⟩ : syracuseStep 1339511 = 2009267) B2009267
theorem B1339531 : Blo 1338988 1339531 := bstep (se 1 (by rfl) ⟨1004648, by rfl⟩ : syracuseStep 1339531 = 2009297) B2009297
theorem B1339543 : Blo 1338988 1339543 := bstep (se 1 (by rfl) ⟨1004657, by rfl⟩ : syracuseStep 1339543 = 2009315) B2009315
theorem B2011289 : Blo 1338988 2011289 := bstep (se 2 (by rfl) ⟨754233, by rfl⟩ : syracuseStep 2011289 = 1508467) B1508467
theorem B1339563 : Blo 1338988 1339563 := bstep (se 1 (by rfl) ⟨1004672, by rfl⟩ : syracuseStep 1339563 = 2009345) B2009345
theorem B1339575 : Blo 1338988 1339575 := bstep (se 1 (by rfl) ⟨1004681, by rfl⟩ : syracuseStep 1339575 = 2009363) B2009363
theorem B1339595 : Blo 1338988 1339595 := bstep (se 1 (by rfl) ⟨1004696, by rfl⟩ : syracuseStep 1339595 = 2009393) B2009393
theorem B1339607 : Blo 1338988 1339607 := bstep (se 1 (by rfl) ⟨1004705, by rfl⟩ : syracuseStep 1339607 = 2009411) B2009411
theorem B1339627 : Blo 1338988 1339627 := bstep (se 1 (by rfl) ⟨1004720, by rfl⟩ : syracuseStep 1339627 = 2009441) B2009441
theorem B1339639 : Blo 1338988 1339639 := bstep (se 1 (by rfl) ⟨1004729, by rfl⟩ : syracuseStep 1339639 = 2009459) B2009459
theorem B1339659 : Blo 1338988 1339659 := bstep (se 1 (by rfl) ⟨1004744, by rfl⟩ : syracuseStep 1339659 = 2009489) B2009489
theorem B2011403 : Blo 1338988 2011403 := bstep (se 1 (by rfl) ⟨1508552, by rfl⟩ : syracuseStep 2011403 = 3017105) B3017105
theorem B1339671 : Blo 1338988 1339671 := bstep (se 1 (by rfl) ⟨1004753, by rfl⟩ : syracuseStep 1339671 = 2009507) B2009507
theorem B1528087 : Blo 1338988 1528087 := bstep (se 1 (by rfl) ⟨1146065, by rfl⟩ : syracuseStep 1528087 = 2292131) B2292131
theorem B2011415 : Blo 1338988 2011415 := bstep (se 1 (by rfl) ⟨1508561, by rfl⟩ : syracuseStep 2011415 = 3017123) B3017123
theorem B1339691 : Blo 1338988 1339691 := bstep (se 1 (by rfl) ⟨1004768, by rfl⟩ : syracuseStep 1339691 = 2009537) B2009537
theorem B1339703 : Blo 1338988 1339703 := bstep (se 1 (by rfl) ⟨1004777, by rfl⟩ : syracuseStep 1339703 = 2009555) B2009555
theorem B1339723 : Blo 1338988 1339723 := bstep (se 1 (by rfl) ⟨1004792, by rfl⟩ : syracuseStep 1339723 = 2009585) B2009585
theorem B1339735 : Blo 1338988 1339735 := bstep (se 1 (by rfl) ⟨1004801, by rfl⟩ : syracuseStep 1339735 = 2009603) B2009603
theorem B1528151 : Blo 1338988 1528151 := bstep (se 1 (by rfl) ⟨1146113, by rfl⟩ : syracuseStep 1528151 = 2292227) B2292227
theorem B2011481 : Blo 1338988 2011481 := bstep (se 2 (by rfl) ⟨754305, by rfl⟩ : syracuseStep 2011481 = 1508611) B1508611
theorem B1339755 : Blo 1338988 1339755 := bstep (se 1 (by rfl) ⟨1004816, by rfl⟩ : syracuseStep 1339755 = 2009633) B2009633
theorem B1339767 : Blo 1338988 1339767 := bstep (se 1 (by rfl) ⟨1004825, by rfl⟩ : syracuseStep 1339767 = 2009651) B2009651
theorem B1339787 : Blo 1338988 1339787 := bstep (se 1 (by rfl) ⟨1004840, by rfl⟩ : syracuseStep 1339787 = 2009681) B2009681
theorem B1339799 : Blo 1338988 1339799 := bstep (se 1 (by rfl) ⟨1004849, by rfl⟩ : syracuseStep 1339799 = 2009699) B2009699
theorem B1429931 : Blo 1338988 1429931 := bstep (se 1 (by rfl) ⟨1072448, by rfl⟩ : syracuseStep 1429931 = 2144897) B2144897
theorem B1339819 : Blo 1338988 1339819 := bstep (se 1 (by rfl) ⟨1004864, by rfl⟩ : syracuseStep 1339819 = 2009729) B2009729
theorem B1339831 : Blo 1338988 1339831 := bstep (se 1 (by rfl) ⟨1004873, by rfl⟩ : syracuseStep 1339831 = 2009747) B2009747
theorem B1339851 : Blo 1338988 1339851 := bstep (se 1 (by rfl) ⟨1004888, by rfl⟩ : syracuseStep 1339851 = 2009777) B2009777
theorem B1339863 : Blo 1338988 1339863 := bstep (se 1 (by rfl) ⟨1004897, by rfl⟩ : syracuseStep 1339863 = 2009795) B2009795
theorem B1339883 : Blo 1338988 1339883 := bstep (se 1 (by rfl) ⟨1004912, by rfl⟩ : syracuseStep 1339883 = 2009825) B2009825
theorem B2863603 : Blo 1338988 2863603 := bstep (se 1 (by rfl) ⟨2147702, by rfl⟩ : syracuseStep 2863603 = 4295405) B4295405
theorem B1339895 : Blo 1338988 1339895 := bstep (se 1 (by rfl) ⟨1004921, by rfl⟩ : syracuseStep 1339895 = 2009843) B2009843
theorem B1339915 : Blo 1338988 1339915 := bstep (se 1 (by rfl) ⟨1004936, by rfl⟩ : syracuseStep 1339915 = 2009873) B2009873
theorem B1339927 : Blo 1338988 1339927 := bstep (se 1 (by rfl) ⟨1004945, by rfl⟩ : syracuseStep 1339927 = 2009891) B2009891
theorem B2413081 : Blo 1338988 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B1430059 : Blo 1338988 1430059 := bstep (se 1 (by rfl) ⟨1072544, by rfl⟩ : syracuseStep 1430059 = 2145089) B2145089
theorem B1339947 : Blo 1338988 1339947 := bstep (se 1 (by rfl) ⟨1004960, by rfl⟩ : syracuseStep 1339947 = 2009921) B2009921
theorem B1339959 : Blo 1338988 1339959 := bstep (se 1 (by rfl) ⟨1004969, by rfl⟩ : syracuseStep 1339959 = 2009939) B2009939
theorem B1339979 : Blo 1338988 1339979 := bstep (se 1 (by rfl) ⟨1004984, by rfl⟩ : syracuseStep 1339979 = 2009969) B2009969
theorem B2544203 : Blo 1338988 2544203 := bstep (se 1 (by rfl) ⟨1908152, by rfl⟩ : syracuseStep 2544203 = 3816305) B3816305
theorem B1339991 : Blo 1338988 1339991 := bstep (se 1 (by rfl) ⟨1004993, by rfl⟩ : syracuseStep 1339991 = 2009987) B2009987
theorem B1340011 : Blo 1338988 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B1340023 : Blo 1338988 1340023 := bstep (se 1 (by rfl) ⟨1005017, by rfl⟩ : syracuseStep 1340023 = 2010035) B2010035
theorem B1340043 : Blo 1338988 1340043 := bstep (se 1 (by rfl) ⟨1005032, by rfl⟩ : syracuseStep 1340043 = 2010065) B2010065
theorem B1340055 : Blo 1338988 1340055 := bstep (se 1 (by rfl) ⟨1005041, by rfl⟩ : syracuseStep 1340055 = 2010083) B2010083
theorem B1340075 : Blo 1338988 1340075 := bstep (se 1 (by rfl) ⟨1005056, by rfl⟩ : syracuseStep 1340075 = 2010113) B2010113
theorem B1340087 : Blo 1338988 1340087 := bstep (se 1 (by rfl) ⟨1005065, by rfl⟩ : syracuseStep 1340087 = 2010131) B2010131
theorem B1340107 : Blo 1338988 1340107 := bstep (se 1 (by rfl) ⟨1005080, by rfl⟩ : syracuseStep 1340107 = 2010161) B2010161
theorem B9925325 : Blo 1338988 9925325 := bstep (se 3 (by rfl) ⟨1860998, by rfl⟩ : syracuseStep 9925325 = 3721997) B3721997
theorem B1340119 : Blo 1338988 1340119 := bstep (se 1 (by rfl) ⟨1005089, by rfl⟩ : syracuseStep 1340119 = 2010179) B2010179
theorem B1340139 : Blo 1338988 1340139 := bstep (se 1 (by rfl) ⟨1005104, by rfl⟩ : syracuseStep 1340139 = 2010209) B2010209
theorem B1340151 : Blo 1338988 1340151 := bstep (se 1 (by rfl) ⟨1005113, by rfl⟩ : syracuseStep 1340151 = 2010227) B2010227
theorem B2544385 : Blo 1338988 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B1340171 : Blo 1338988 1340171 := bstep (se 1 (by rfl) ⟨1005128, by rfl⟩ : syracuseStep 1340171 = 2010257) B2010257
theorem B1340183 : Blo 1338988 1340183 := bstep (se 1 (by rfl) ⟨1005137, by rfl⟩ : syracuseStep 1340183 = 2010275) B2010275
theorem B1340203 : Blo 1338988 1340203 := bstep (se 1 (by rfl) ⟨1005152, by rfl⟩ : syracuseStep 1340203 = 2010305) B2010305
theorem B1340215 : Blo 1338988 1340215 := bstep (se 1 (by rfl) ⟨1005161, by rfl⟩ : syracuseStep 1340215 = 2010323) B2010323
theorem B2863937 : Blo 1338988 2863937 := bstep (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) B2147953
theorem B3814219 : Blo 1338988 3814219 := bstep (se 1 (by rfl) ⟨2860664, by rfl⟩ : syracuseStep 3814219 = 5721329) B5721329
theorem B1340235 : Blo 1338988 1340235 := bstep (se 1 (by rfl) ⟨1005176, by rfl⟩ : syracuseStep 1340235 = 2010353) B2010353
theorem B1340247 : Blo 1338988 1340247 := bstep (se 1 (by rfl) ⟨1005185, by rfl⟩ : syracuseStep 1340247 = 2010371) B2010371
theorem B5722969 : Blo 1338988 5722969 := bstep (se 2 (by rfl) ⟨2146113, by rfl⟩ : syracuseStep 5722969 = 4292227) B4292227
theorem B1340267 : Blo 1338988 1340267 := bstep (se 1 (by rfl) ⟨1005200, by rfl⟩ : syracuseStep 1340267 = 2010401) B2010401
theorem B1340279 : Blo 1338988 1340279 := bstep (se 1 (by rfl) ⟨1005209, by rfl⟩ : syracuseStep 1340279 = 2010419) B2010419
theorem B9163651 : Blo 1338988 9163651 := bstep (se 1 (by rfl) ⟨6872738, by rfl⟩ : syracuseStep 9163651 = 13745477) B13745477
theorem B1340299 : Blo 1338988 1340299 := bstep (se 1 (by rfl) ⟨1005224, by rfl⟩ : syracuseStep 1340299 = 2010449) B2010449
theorem B1340311 : Blo 1338988 1340311 := bstep (se 1 (by rfl) ⟨1005233, by rfl⟩ : syracuseStep 1340311 = 2010467) B2010467
theorem B1340331 : Blo 1338988 1340331 := bstep (se 1 (by rfl) ⟨1005248, by rfl⟩ : syracuseStep 1340331 = 2010497) B2010497
theorem B1340343 : Blo 1338988 1340343 := bstep (se 1 (by rfl) ⟨1005257, by rfl⟩ : syracuseStep 1340343 = 2010515) B2010515
theorem B1340363 : Blo 1338988 1340363 := bstep (se 1 (by rfl) ⟨1005272, by rfl⟩ : syracuseStep 1340363 = 2010545) B2010545
theorem B1340375 : Blo 1338988 1340375 := bstep (se 1 (by rfl) ⟨1005281, by rfl⟩ : syracuseStep 1340375 = 2010563) B2010563
theorem B1340395 : Blo 1338988 1340395 := bstep (se 1 (by rfl) ⟨1005296, by rfl⟩ : syracuseStep 1340395 = 2010593) B2010593
theorem B1340407 : Blo 1338988 1340407 := bstep (se 1 (by rfl) ⟨1005305, by rfl⟩ : syracuseStep 1340407 = 2010611) B2010611
theorem B1340427 : Blo 1338988 1340427 := bstep (se 1 (by rfl) ⟨1005320, by rfl⟩ : syracuseStep 1340427 = 2010641) B2010641
theorem B1340439 : Blo 1338988 1340439 := bstep (se 1 (by rfl) ⟨1005329, by rfl⟩ : syracuseStep 1340439 = 2010659) B2010659
theorem B1340459 : Blo 1338988 1340459 := bstep (se 1 (by rfl) ⟨1005344, by rfl⟩ : syracuseStep 1340459 = 2010689) B2010689
theorem B12219437 : Blo 1338988 12219437 := bstep (se 3 (by rfl) ⟨2291144, by rfl⟩ : syracuseStep 12219437 = 4582289) B4582289
theorem B1340471 : Blo 1338988 1340471 := bstep (se 1 (by rfl) ⟨1005353, by rfl⟩ : syracuseStep 1340471 = 2010707) B2010707
theorem B1340491 : Blo 1338988 1340491 := bstep (se 1 (by rfl) ⟨1005368, by rfl⟩ : syracuseStep 1340491 = 2010737) B2010737
theorem B2716759 : Blo 1338988 2716759 := bstep (se 1 (by rfl) ⟨2037569, by rfl⟩ : syracuseStep 2716759 = 4075139) B4075139
theorem B1340503 : Blo 1338988 1340503 := bstep (se 1 (by rfl) ⟨1005377, by rfl⟩ : syracuseStep 1340503 = 2010755) B2010755
theorem B12383333 : Blo 1338988 12383333 := bstep (se 4 (by rfl) ⟨1160937, by rfl⟩ : syracuseStep 12383333 = 2321875) B2321875
theorem B10171493 : Blo 1338988 10171493 := bstep (se 4 (by rfl) ⟨953577, by rfl⟩ : syracuseStep 10171493 = 1907155) B1907155
theorem B1340523 : Blo 1338988 1340523 := bstep (se 1 (by rfl) ⟨1005392, by rfl⟩ : syracuseStep 1340523 = 2010785) B2010785
theorem B1340535 : Blo 1338988 1340535 := bstep (se 1 (by rfl) ⟨1005401, by rfl⟩ : syracuseStep 1340535 = 2010803) B2010803
theorem B1340555 : Blo 1338988 1340555 := bstep (se 1 (by rfl) ⟨1005416, by rfl⟩ : syracuseStep 1340555 = 2010833) B2010833
theorem B1340567 : Blo 1338988 1340567 := bstep (se 1 (by rfl) ⟨1005425, by rfl⟩ : syracuseStep 1340567 = 2010851) B2010851
theorem B1340587 : Blo 1338988 1340587 := bstep (se 1 (by rfl) ⟨1005440, by rfl⟩ : syracuseStep 1340587 = 2010881) B2010881
theorem B1340599 : Blo 1338988 1340599 := bstep (se 1 (by rfl) ⟨1005449, by rfl⟩ : syracuseStep 1340599 = 2010899) B2010899
theorem B2544833 : Blo 1338988 2544833 := bstep (se 2 (by rfl) ⟨954312, by rfl⟩ : syracuseStep 2544833 = 1908625) B1908625
theorem B1340619 : Blo 1338988 1340619 := bstep (se 1 (by rfl) ⟨1005464, by rfl⟩ : syracuseStep 1340619 = 2010929) B2010929
theorem B1340631 : Blo 1338988 1340631 := bstep (se 1 (by rfl) ⟨1005473, by rfl⟩ : syracuseStep 1340631 = 2010947) B2010947
theorem B1340651 : Blo 1338988 1340651 := bstep (se 1 (by rfl) ⟨1005488, by rfl⟩ : syracuseStep 1340651 = 2010977) B2010977
theorem B1340663 : Blo 1338988 1340663 := bstep (se 1 (by rfl) ⟨1005497, by rfl⟩ : syracuseStep 1340663 = 2010995) B2010995
theorem B1340683 : Blo 1338988 1340683 := bstep (se 1 (by rfl) ⟨1005512, by rfl⟩ : syracuseStep 1340683 = 2011025) B2011025
theorem B1340695 : Blo 1338988 1340695 := bstep (se 1 (by rfl) ⟨1005521, by rfl⟩ : syracuseStep 1340695 = 2011043) B2011043
theorem B1340715 : Blo 1338988 1340715 := bstep (se 1 (by rfl) ⟨1005536, by rfl⟩ : syracuseStep 1340715 = 2011073) B2011073
theorem B1340727 : Blo 1338988 1340727 := bstep (se 1 (by rfl) ⟨1005545, by rfl⟩ : syracuseStep 1340727 = 2011091) B2011091
theorem B3814721 : Blo 1338988 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B8590657 : Blo 1338988 8590657 := bstep (se 2 (by rfl) ⟨3221496, by rfl⟩ : syracuseStep 8590657 = 6442993) B6442993
theorem B1340747 : Blo 1338988 1340747 := bstep (se 1 (by rfl) ⟨1005560, by rfl⟩ : syracuseStep 1340747 = 2011121) B2011121
theorem B1340759 : Blo 1338988 1340759 := bstep (se 1 (by rfl) ⟨1005569, by rfl⟩ : syracuseStep 1340759 = 2011139) B2011139
theorem B1340779 : Blo 1338988 1340779 := bstep (se 1 (by rfl) ⟨1005584, by rfl⟩ : syracuseStep 1340779 = 2011169) B2011169
theorem B1340791 : Blo 1338988 1340791 := bstep (se 1 (by rfl) ⟨1005593, by rfl⟩ : syracuseStep 1340791 = 2011187) B2011187
theorem B1340811 : Blo 1338988 1340811 := bstep (se 1 (by rfl) ⟨1005608, by rfl⟩ : syracuseStep 1340811 = 2011217) B2011217
theorem B2413975 : Blo 1338988 2413975 := bstep (se 1 (by rfl) ⟨1810481, by rfl⟩ : syracuseStep 2413975 = 3620963) B3620963
theorem B1340823 : Blo 1338988 1340823 := bstep (se 1 (by rfl) ⟨1005617, by rfl⟩ : syracuseStep 1340823 = 2011235) B2011235
theorem B1340843 : Blo 1338988 1340843 := bstep (se 1 (by rfl) ⟨1005632, by rfl⟩ : syracuseStep 1340843 = 2011265) B2011265
theorem B1340855 : Blo 1338988 1340855 := bstep (se 1 (by rfl) ⟨1005641, by rfl⟩ : syracuseStep 1340855 = 2011283) B2011283
theorem B5723585 : Blo 1338988 5723585 := bstep (se 2 (by rfl) ⟨2146344, by rfl⟩ : syracuseStep 5723585 = 4292689) B4292689
theorem B1340875 : Blo 1338988 1340875 := bstep (se 1 (by rfl) ⟨1005656, by rfl⟩ : syracuseStep 1340875 = 2011313) B2011313
theorem B1340887 : Blo 1338988 1340887 := bstep (se 1 (by rfl) ⟨1005665, by rfl⟩ : syracuseStep 1340887 = 2011331) B2011331
theorem B1340907 : Blo 1338988 1340907 := bstep (se 1 (by rfl) ⟨1005680, by rfl⟩ : syracuseStep 1340907 = 2011361) B2011361
theorem B1340919 : Blo 1338988 1340919 := bstep (se 1 (by rfl) ⟨1005689, by rfl⟩ : syracuseStep 1340919 = 2011379) B2011379
theorem B1340939 : Blo 1338988 1340939 := bstep (se 1 (by rfl) ⟨1005704, by rfl⟩ : syracuseStep 1340939 = 2011409) B2011409
theorem B2545175 : Blo 1338988 2545175 := bstep (se 1 (by rfl) ⟨1908881, by rfl⟩ : syracuseStep 2545175 = 3817763) B3817763
theorem B1340951 : Blo 1338988 1340951 := bstep (se 1 (by rfl) ⟨1005713, by rfl⟩ : syracuseStep 1340951 = 2011427) B2011427
theorem B1340971 : Blo 1338988 1340971 := bstep (se 1 (by rfl) ⟨1005728, by rfl⟩ : syracuseStep 1340971 = 2011457) B2011457
theorem B4519475 : Blo 1338988 4519475 := bstep (se 1 (by rfl) ⟨3389606, by rfl⟩ : syracuseStep 4519475 = 6779213) B6779213
theorem B1340983 : Blo 1338988 1340983 := bstep (se 1 (by rfl) ⟨1005737, by rfl⟩ : syracuseStep 1340983 = 2011475) B2011475
theorem B10171979 : Blo 1338988 10171979 := bstep (se 1 (by rfl) ⟨7628984, by rfl⟩ : syracuseStep 10171979 = 15257969) B15257969
theorem B6780509 : Blo 1338988 6780509 := bstep (se 3 (by rfl) ⟨1271345, by rfl⟩ : syracuseStep 6780509 = 2542691) B2542691
theorem B3815063 : Blo 1338988 3815063 := bstep (se 1 (by rfl) ⟨2861297, by rfl⟩ : syracuseStep 3815063 = 5722595) B5722595
theorem B6616849 : Blo 1338988 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B10319633 : Blo 1338988 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B4519745 : Blo 1338988 4519745 := bstep (se 2 (by rfl) ⟨1694904, by rfl⟩ : syracuseStep 4519745 = 3389809) B3389809
theorem B48887651 : Blo 1338988 48887651 := bstep (se 1 (by rfl) ⟨36665738, by rfl⟩ : syracuseStep 48887651 = 73331477) B73331477
theorem B7632791 : Blo 1338988 7632791 := bstep (se 1 (by rfl) ⟨5724593, by rfl⟩ : syracuseStep 7632791 = 11449187) B11449187
theorem B9656243 : Blo 1338988 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B2414603 : Blo 1338988 2414603 := bstep (se 1 (by rfl) ⟨1810952, by rfl⟩ : syracuseStep 2414603 = 3621905) B3621905
theorem B11606051 : Blo 1338988 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B22911011 : Blo 1338988 22911011 := bstep (se 1 (by rfl) ⟨17183258, by rfl⟩ : syracuseStep 22911011 = 34366517) B34366517
theorem B1357975 : Blo 1338988 1357975 := bstep (se 1 (by rfl) ⟨1018481, by rfl⟩ : syracuseStep 1357975 = 2036963) B2036963
theorem B11450585 : Blo 1338988 11450585 := bstep (se 2 (by rfl) ⟨4293969, by rfl⟩ : syracuseStep 11450585 = 8587939) B8587939
theorem B5085443 : Blo 1338988 5085443 := bstep (se 1 (by rfl) ⟨3814082, by rfl⟩ : syracuseStep 5085443 = 7628165) B7628165
theorem B3012875 : Blo 1338988 3012875 := bstep (se 1 (by rfl) ⟨2259656, by rfl⟩ : syracuseStep 3012875 = 4519313) B4519313
theorem B3012929 : Blo 1338988 3012929 := bstep (se 2 (by rfl) ⟨1129848, by rfl⟩ : syracuseStep 3012929 = 2259697) B2259697
theorem B2038105 : Blo 1338988 2038105 := bstep (se 2 (by rfl) ⟨764289, by rfl⟩ : syracuseStep 2038105 = 1528579) B1528579
theorem B4520285 : Blo 1338988 4520285 := bstep (se 3 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 4520285 = 1695107) B1695107
theorem B3013145 : Blo 1338988 3013145 := bstep (se 2 (by rfl) ⟨1129929, by rfl⟩ : syracuseStep 3013145 = 2259859) B2259859
theorem B10181213 : Blo 1338988 10181213 := bstep (se 3 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 10181213 = 3817955) B3817955
theorem B3013235 : Blo 1338988 3013235 := bstep (se 1 (by rfl) ⟨2259926, by rfl⟩ : syracuseStep 3013235 = 4519853) B4519853
theorem B4127383 : Blo 1338988 4127383 := bstep (se 1 (by rfl) ⟨3095537, by rfl⟩ : syracuseStep 4127383 = 6191075) B6191075
theorem B3013271 : Blo 1338988 3013271 := bstep (se 1 (by rfl) ⟨2259953, by rfl⟩ : syracuseStep 3013271 = 4519907) B4519907
theorem B5085899 : Blo 1338988 5085899 := bstep (se 1 (by rfl) ⟨3814424, by rfl⟩ : syracuseStep 5085899 = 7628849) B7628849
theorem B4832045 : Blo 1338988 4832045 := bstep (se 3 (by rfl) ⟨906008, by rfl⟩ : syracuseStep 4832045 = 1812017) B1812017
theorem B11754305 : Blo 1338988 11754305 := bstep (se 2 (by rfl) ⟨4407864, by rfl⟩ : syracuseStep 11754305 = 8815729) B8815729
theorem B3013451 : Blo 1338988 3013451 := bstep (se 1 (by rfl) ⟨2260088, by rfl⟩ : syracuseStep 3013451 = 4520177) B4520177
theorem B3013505 : Blo 1338988 3013505 := bstep (se 2 (by rfl) ⟨1130064, by rfl⟩ : syracuseStep 3013505 = 2260129) B2260129
theorem B4832131 : Blo 1338988 4832131 := bstep (se 1 (by rfl) ⟨3624098, by rfl⟩ : syracuseStep 4832131 = 7248197) B7248197
theorem B5086097 : Blo 1338988 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B3218393 : Blo 1338988 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B61905941 : Blo 1338988 61905941 := bstep (se 6 (by rfl) ⟨1450920, by rfl⟩ : syracuseStep 61905941 = 2901841) B2901841
theorem B1506379 : Blo 1338988 1506379 := bstep (se 1 (by rfl) ⟨1129784, by rfl⟩ : syracuseStep 1506379 = 2259569) B2259569
theorem B2260055 : Blo 1338988 2260055 := bstep (se 1 (by rfl) ⟨1695041, by rfl⟩ : syracuseStep 2260055 = 3390083) B3390083
theorem B3013721 : Blo 1338988 3013721 := bstep (se 2 (by rfl) ⟨1130145, by rfl⟩ : syracuseStep 3013721 = 2260291) B2260291
theorem B3013811 : Blo 1338988 3013811 := bstep (se 1 (by rfl) ⟨2260358, by rfl⟩ : syracuseStep 3013811 = 4520717) B4520717
theorem B1506487 : Blo 1338988 1506487 := bstep (se 1 (by rfl) ⟨1129865, by rfl⟩ : syracuseStep 1506487 = 2259731) B2259731
theorem B1694935 : Blo 1338988 1694935 := bstep (se 1 (by rfl) ⟨1271201, by rfl⟩ : syracuseStep 1694935 = 2542403) B2542403
theorem B2260183 : Blo 1338988 2260183 := bstep (se 1 (by rfl) ⟨1695137, by rfl⟩ : syracuseStep 2260183 = 3390275) B3390275
theorem B3013847 : Blo 1338988 3013847 := bstep (se 1 (by rfl) ⟨2260385, by rfl⟩ : syracuseStep 3013847 = 4520771) B4520771
theorem B4291805 : Blo 1338988 4291805 := bstep (se 3 (by rfl) ⟨804713, by rfl⟩ : syracuseStep 4291805 = 1609427) B1609427
theorem B2579723 : Blo 1338988 2579723 := bstep (se 1 (by rfl) ⟨1934792, by rfl⟩ : syracuseStep 2579723 = 3869585) B3869585
theorem B1359191 : Blo 1338988 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B1506667 : Blo 1338988 1506667 := bstep (se 1 (by rfl) ⟨1130000, by rfl⟩ : syracuseStep 1506667 = 2260001) B2260001
theorem B2612609 : Blo 1338988 2612609 := bstep (se 2 (by rfl) ⟨979728, by rfl⟩ : syracuseStep 2612609 = 1959457) B1959457
theorem B3014027 : Blo 1338988 3014027 := bstep (se 1 (by rfl) ⟨2260520, by rfl⟩ : syracuseStep 3014027 = 4521041) B4521041
theorem B2579863 : Blo 1338988 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B3014081 : Blo 1338988 3014081 := bstep (se 2 (by rfl) ⟨1130280, by rfl⟩ : syracuseStep 3014081 = 2260561) B2260561
theorem B3390923 : Blo 1338988 3390923 := bstep (se 1 (by rfl) ⟨2543192, by rfl⟩ : syracuseStep 3390923 = 5086385) B5086385
theorem B4521419 : Blo 1338988 4521419 := bstep (se 1 (by rfl) ⟨3391064, by rfl⟩ : syracuseStep 4521419 = 6782129) B6782129
theorem B1506775 : Blo 1338988 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B24436241 : Blo 1338988 24436241 := bstep (se 2 (by rfl) ⟨9163590, by rfl⟩ : syracuseStep 24436241 = 18327181) B18327181
theorem B1506955 : Blo 1338988 1506955 := bstep (se 1 (by rfl) ⟨1130216, by rfl⟩ : syracuseStep 1506955 = 2260433) B2260433
theorem B6782615 : Blo 1338988 6782615 := bstep (se 1 (by rfl) ⟨5086961, by rfl⟩ : syracuseStep 6782615 = 10173923) B10173923
theorem B5086871 : Blo 1338988 5086871 := bstep (se 1 (by rfl) ⟨3815153, by rfl⟩ : syracuseStep 5086871 = 7630307) B7630307
theorem B3014297 : Blo 1338988 3014297 := bstep (se 2 (by rfl) ⟨1130361, by rfl⟩ : syracuseStep 3014297 = 2260723) B2260723
theorem B1810135 : Blo 1338988 1810135 := bstep (se 1 (by rfl) ⟨1357601, by rfl⟩ : syracuseStep 1810135 = 2715203) B2715203
theorem B11009753 : Blo 1338988 11009753 := bstep (se 2 (by rfl) ⟨4128657, by rfl⟩ : syracuseStep 11009753 = 8257315) B8257315
theorem B4521689 : Blo 1338988 4521689 := bstep (se 2 (by rfl) ⟨1695633, by rfl⟩ : syracuseStep 4521689 = 3391267) B3391267
theorem B3817181 : Blo 1338988 3817181 := bstep (se 3 (by rfl) ⟨715721, by rfl⟩ : syracuseStep 3817181 = 1431443) B1431443
theorem B3014387 : Blo 1338988 3014387 := bstep (se 1 (by rfl) ⟨2260790, by rfl⟩ : syracuseStep 3014387 = 4521581) B4521581
theorem B1507063 : Blo 1338988 1507063 := bstep (se 1 (by rfl) ⟨1130297, by rfl⟩ : syracuseStep 1507063 = 2260595) B2260595
theorem B3014423 : Blo 1338988 3014423 := bstep (se 1 (by rfl) ⟨2260817, by rfl⟩ : syracuseStep 3014423 = 4521635) B4521635
theorem B14491457 : Blo 1338988 14491457 := bstep (se 2 (by rfl) ⟨5434296, by rfl⟩ : syracuseStep 14491457 = 10868593) B10868593
theorem B11452225 : Blo 1338988 11452225 := bstep (se 2 (by rfl) ⟨4294584, by rfl⟩ : syracuseStep 11452225 = 8589169) B8589169
theorem B2260811 : Blo 1338988 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B5087069 : Blo 1338988 5087069 := bstep (se 3 (by rfl) ⟨953825, by rfl⟩ : syracuseStep 5087069 = 1907651) B1907651
theorem B5726045 : Blo 1338988 5726045 := bstep (se 3 (by rfl) ⟨1073633, by rfl⟩ : syracuseStep 5726045 = 2147267) B2147267
theorem B1507243 : Blo 1338988 1507243 := bstep (se 1 (by rfl) ⟨1130432, by rfl⟩ : syracuseStep 1507243 = 2260865) B2260865
theorem B2260939 : Blo 1338988 2260939 := bstep (se 1 (by rfl) ⟨1695704, by rfl⟩ : syracuseStep 2260939 = 3391409) B3391409
theorem B3014603 : Blo 1338988 3014603 := bstep (se 1 (by rfl) ⟨2260952, by rfl⟩ : syracuseStep 3014603 = 4521905) B4521905
theorem B2146319 : Blo 1338988 2146319 := bstep (se 1 (by rfl) ⟨1609739, by rfl⟩ : syracuseStep 2146319 = 3219479) B3219479
theorem B4522013 : Blo 1338988 4522013 := bstep (se 3 (by rfl) ⟨847877, by rfl⟩ : syracuseStep 4522013 = 1695755) B1695755
theorem B1507387 : Blo 1338988 1507387 := bstep (se 1 (by rfl) ⟨1130540, by rfl⟩ : syracuseStep 1507387 = 2261081) B2261081
theorem B7241795 : Blo 1338988 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B12869765 : Blo 1338988 12869765 := bstep (se 4 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 12869765 = 2413081) B2413081
theorem B7635181 : Blo 1338988 7635181 := bstep (se 3 (by rfl) ⟨1431596, by rfl⟩ : syracuseStep 7635181 = 2863193) B2863193
theorem B3014927 : Blo 1338988 3014927 := bstep (se 1 (by rfl) ⟨2261195, by rfl⟩ : syracuseStep 3014927 = 4522391) B4522391
theorem B2261263 : Blo 1338988 2261263 := bstep (se 1 (by rfl) ⟨1695947, by rfl⟩ : syracuseStep 2261263 = 3391895) B3391895
theorem B3014945 : Blo 1338988 3014945 := bstep (se 2 (by rfl) ⟨1130604, by rfl⟩ : syracuseStep 3014945 = 2261209) B2261209
theorem B3719485 : Blo 1338988 3719485 := bstep (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) B1394807
theorem B1696135 : Blo 1338988 1696135 := bstep (se 1 (by rfl) ⟨1272101, by rfl⟩ : syracuseStep 1696135 = 2544203) B2544203
theorem B1507855 : Blo 1338988 1507855 := bstep (se 1 (by rfl) ⟨1130891, by rfl⟩ : syracuseStep 1507855 = 2261783) B2261783
theorem B11444813 : Blo 1338988 11444813 := bstep (se 3 (by rfl) ⟨2145902, by rfl⟩ : syracuseStep 11444813 = 4291805) B4291805
theorem B3015287 : Blo 1338988 3015287 := bstep (se 1 (by rfl) ⟨2261465, by rfl⟩ : syracuseStep 3015287 = 4522931) B4522931
theorem B7242533 : Blo 1338988 7242533 := bstep (se 4 (by rfl) ⟨678987, by rfl⟩ : syracuseStep 7242533 = 1357975) B1357975
theorem B3015467 : Blo 1338988 3015467 := bstep (se 1 (by rfl) ⟨2261600, by rfl⟩ : syracuseStep 3015467 = 4523201) B4523201
theorem B2261803 : Blo 1338988 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B1696555 : Blo 1338988 1696555 := bstep (se 1 (by rfl) ⟨1272416, by rfl⟩ : syracuseStep 1696555 = 2544833) B2544833
theorem B2261945 : Blo 1338988 2261945 := bstep (se 2 (by rfl) ⟨848229, by rfl⟩ : syracuseStep 2261945 = 1696459) B1696459
theorem B3392513 : Blo 1338988 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B1508359 : Blo 1338988 1508359 := bstep (se 1 (by rfl) ⟨1131269, by rfl⟩ : syracuseStep 1508359 = 2262539) B2262539
theorem B1696783 : Blo 1338988 1696783 := bstep (se 1 (by rfl) ⟨1272587, by rfl⟩ : syracuseStep 1696783 = 2545175) B2545175
theorem B2147447 : Blo 1338988 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B3015827 : Blo 1338988 3015827 := bstep (se 1 (by rfl) ⟨2261870, by rfl⟩ : syracuseStep 3015827 = 4523741) B4523741
theorem B1508539 : Blo 1338988 1508539 := bstep (se 1 (by rfl) ⟨1131404, by rfl⟩ : syracuseStep 1508539 = 2262809) B2262809
theorem B3015881 : Blo 1338988 3015881 := bstep (se 2 (by rfl) ⟨1130955, by rfl⟩ : syracuseStep 3015881 = 2261911) B2261911
theorem B5088527 : Blo 1338988 5088527 := bstep (se 1 (by rfl) ⟨3816395, by rfl⟩ : syracuseStep 5088527 = 7632791) B7632791
theorem B3622259 : Blo 1338988 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B3392887 : Blo 1338988 3392887 := bstep (se 1 (by rfl) ⟨2544665, by rfl⟩ : syracuseStep 3392887 = 5089331) B5089331
theorem B4523417 : Blo 1338988 4523417 := bstep (se 2 (by rfl) ⟨1696281, by rfl⟩ : syracuseStep 4523417 = 3392563) B3392563
theorem B2008505 : Blo 1338988 2008505 := bstep (se 2 (by rfl) ⟨753189, by rfl⟩ : syracuseStep 2008505 = 1506379) B1506379
theorem B4294073 : Blo 1338988 4294073 := bstep (se 2 (by rfl) ⟨1610277, by rfl⟩ : syracuseStep 4294073 = 3220555) B3220555
theorem B2008583 : Blo 1338988 2008583 := bstep (se 1 (by rfl) ⟨1506437, by rfl⟩ : syracuseStep 2008583 = 3012875) B3012875
theorem B2008619 : Blo 1338988 2008619 := bstep (se 1 (by rfl) ⟨1506464, by rfl⟩ : syracuseStep 2008619 = 3012929) B3012929
theorem B7243307 : Blo 1338988 7243307 := bstep (se 1 (by rfl) ⟨5432480, by rfl⟩ : syracuseStep 7243307 = 10864961) B10864961
theorem B2008649 : Blo 1338988 2008649 := bstep (se 2 (by rfl) ⟨753243, by rfl⟩ : syracuseStep 2008649 = 1506487) B1506487
theorem B2262647 : Blo 1338988 2262647 := bstep (se 1 (by rfl) ⟨1696985, by rfl⟩ : syracuseStep 2262647 = 3393971) B3393971
theorem B2147959 : Blo 1338988 2147959 := bstep (se 1 (by rfl) ⟨1610969, by rfl⟩ : syracuseStep 2147959 = 3221939) B3221939
theorem B2008763 : Blo 1338988 2008763 := bstep (se 1 (by rfl) ⟨1506572, by rfl⟩ : syracuseStep 2008763 = 3013145) B3013145
theorem B2008823 : Blo 1338988 2008823 := bstep (se 1 (by rfl) ⟨1506617, by rfl⟩ : syracuseStep 2008823 = 3013235) B3013235
theorem B11454209 : Blo 1338988 11454209 := bstep (se 2 (by rfl) ⟨4295328, by rfl⟩ : syracuseStep 11454209 = 8590657) B8590657
theorem B2008847 : Blo 1338988 2008847 := bstep (se 1 (by rfl) ⟨1506635, by rfl⟩ : syracuseStep 2008847 = 3013271) B3013271
theorem B3393323 : Blo 1338988 3393323 := bstep (se 1 (by rfl) ⟨2544992, by rfl⟩ : syracuseStep 3393323 = 5089985) B5089985
theorem B2008889 : Blo 1338988 2008889 := bstep (se 2 (by rfl) ⟨753333, by rfl⟩ : syracuseStep 2008889 = 1506667) B1506667
theorem B3622715 : Blo 1338988 3622715 := bstep (se 1 (by rfl) ⟨2717036, by rfl⟩ : syracuseStep 3622715 = 5434073) B5434073
theorem B6784883 : Blo 1338988 6784883 := bstep (se 1 (by rfl) ⟨5088662, by rfl⟩ : syracuseStep 6784883 = 10177325) B10177325
theorem B3221363 : Blo 1338988 3221363 := bstep (se 1 (by rfl) ⟨2416022, by rfl⟩ : syracuseStep 3221363 = 4832045) B4832045
theorem B2008967 : Blo 1338988 2008967 := bstep (se 1 (by rfl) ⟨1506725, by rfl⟩ : syracuseStep 2008967 = 3013451) B3013451
theorem B3016583 : Blo 1338988 3016583 := bstep (se 1 (by rfl) ⟨2262437, by rfl⟩ : syracuseStep 3016583 = 4524875) B4524875
theorem B2009003 : Blo 1338988 2009003 := bstep (se 1 (by rfl) ⟨1506752, by rfl⟩ : syracuseStep 2009003 = 3013505) B3013505
theorem B2009033 : Blo 1338988 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B2009147 : Blo 1338988 2009147 := bstep (se 1 (by rfl) ⟨1506860, by rfl⟩ : syracuseStep 2009147 = 3013721) B3013721
theorem B3016763 : Blo 1338988 3016763 := bstep (se 1 (by rfl) ⟨2262572, by rfl⟩ : syracuseStep 3016763 = 4525145) B4525145
theorem B4524119 : Blo 1338988 4524119 := bstep (se 1 (by rfl) ⟨3393089, by rfl⟩ : syracuseStep 4524119 = 6786179) B6786179
theorem B2009207 : Blo 1338988 2009207 := bstep (se 1 (by rfl) ⟨1506905, by rfl⟩ : syracuseStep 2009207 = 3013811) B3013811
theorem B2009231 : Blo 1338988 2009231 := bstep (se 1 (by rfl) ⟨1506923, by rfl⟩ : syracuseStep 2009231 = 3013847) B3013847
theorem B7637165 : Blo 1338988 7637165 := bstep (se 3 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 7637165 = 2863937) B2863937
theorem B2009273 : Blo 1338988 2009273 := bstep (se 2 (by rfl) ⟨753477, by rfl⟩ : syracuseStep 2009273 = 1506955) B1506955
theorem B3016889 : Blo 1338988 3016889 := bstep (se 2 (by rfl) ⟨1131333, by rfl⟩ : syracuseStep 3016889 = 2262667) B2262667
theorem B2009351 : Blo 1338988 2009351 := bstep (se 1 (by rfl) ⟨1507013, by rfl⟩ : syracuseStep 2009351 = 3014027) B3014027
theorem B2009387 : Blo 1338988 2009387 := bstep (se 1 (by rfl) ⟨1507040, by rfl⟩ : syracuseStep 2009387 = 3014081) B3014081
theorem B2009417 : Blo 1338988 2009417 := bstep (se 2 (by rfl) ⟨753531, by rfl⟩ : syracuseStep 2009417 = 1507063) B1507063
theorem B6785369 : Blo 1338988 6785369 := bstep (se 2 (by rfl) ⟨2544513, by rfl⟩ : syracuseStep 6785369 = 5089027) B5089027
theorem B3623287 : Blo 1338988 3623287 := bstep (se 1 (by rfl) ⟨2717465, by rfl⟩ : syracuseStep 3623287 = 5434931) B5434931
theorem B2009531 : Blo 1338988 2009531 := bstep (se 1 (by rfl) ⟨1507148, by rfl⟩ : syracuseStep 2009531 = 3014297) B3014297
theorem B2009591 : Blo 1338988 2009591 := bstep (se 1 (by rfl) ⟨1507193, by rfl⟩ : syracuseStep 2009591 = 3014387) B3014387
theorem B2009615 : Blo 1338988 2009615 := bstep (se 1 (by rfl) ⟨1507211, by rfl⟩ : syracuseStep 2009615 = 3014423) B3014423
theorem B9660971 : Blo 1338988 9660971 := bstep (se 1 (by rfl) ⟨7245728, by rfl⟩ : syracuseStep 9660971 = 14491457) B14491457
theorem B2009657 : Blo 1338988 2009657 := bstep (se 2 (by rfl) ⟨753621, by rfl⟩ : syracuseStep 2009657 = 1507243) B1507243
theorem B4524605 : Blo 1338988 4524605 := bstep (se 3 (by rfl) ⟨848363, by rfl⟩ : syracuseStep 4524605 = 1696727) B1696727
theorem B15272549 : Blo 1338988 15272549 := bstep (se 4 (by rfl) ⟨1431801, by rfl⟩ : syracuseStep 15272549 = 2863603) B2863603
theorem B3394163 : Blo 1338988 3394163 := bstep (se 1 (by rfl) ⟨2545622, by rfl⟩ : syracuseStep 3394163 = 5091245) B5091245
theorem B2009735 : Blo 1338988 2009735 := bstep (se 1 (by rfl) ⟨1507301, by rfl⟩ : syracuseStep 2009735 = 3014603) B3014603
theorem B3394183 : Blo 1338988 3394183 := bstep (se 1 (by rfl) ⟨2545637, by rfl⟩ : syracuseStep 3394183 = 5091275) B5091275
theorem B2009771 : Blo 1338988 2009771 := bstep (se 1 (by rfl) ⟨1507328, by rfl⟩ : syracuseStep 2009771 = 3014657) B3014657
theorem B4893385 : Blo 1338988 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B2009801 : Blo 1338988 2009801 := bstep (se 2 (by rfl) ⟨753675, by rfl⟩ : syracuseStep 2009801 = 1507351) B1507351
theorem B2009915 : Blo 1338988 2009915 := bstep (se 1 (by rfl) ⟨1507436, by rfl⟩ : syracuseStep 2009915 = 3014873) B3014873
theorem B2009975 : Blo 1338988 2009975 := bstep (se 1 (by rfl) ⟨1507481, by rfl⟩ : syracuseStep 2009975 = 3014963) B3014963
theorem B2009999 : Blo 1338988 2009999 := bstep (se 1 (by rfl) ⟨1507499, by rfl⟩ : syracuseStep 2009999 = 3014999) B3014999
theorem B2010041 : Blo 1338988 2010041 := bstep (se 2 (by rfl) ⟨753765, by rfl⟩ : syracuseStep 2010041 = 1507531) B1507531
theorem B2010119 : Blo 1338988 2010119 := bstep (se 1 (by rfl) ⟨1507589, by rfl⟩ : syracuseStep 2010119 = 3015179) B3015179
theorem B2010155 : Blo 1338988 2010155 := bstep (se 1 (by rfl) ⟨1507616, by rfl⟩ : syracuseStep 2010155 = 3015233) B3015233
theorem B2010185 : Blo 1338988 2010185 := bstep (se 2 (by rfl) ⟨753819, by rfl⟩ : syracuseStep 2010185 = 1507639) B1507639
theorem B2010299 : Blo 1338988 2010299 := bstep (se 1 (by rfl) ⟨1507724, by rfl⟩ : syracuseStep 2010299 = 3015449) B3015449
theorem B2010359 : Blo 1338988 2010359 := bstep (se 1 (by rfl) ⟨1507769, by rfl⟩ : syracuseStep 2010359 = 3015539) B3015539
theorem B2010383 : Blo 1338988 2010383 := bstep (se 1 (by rfl) ⟨1507787, by rfl⟩ : syracuseStep 2010383 = 3015575) B3015575
theorem B2010425 : Blo 1338988 2010425 := bstep (se 2 (by rfl) ⟨753909, by rfl⟩ : syracuseStep 2010425 = 1507819) B1507819
theorem B17165627 : Blo 1338988 17165627 := bstep (se 1 (by rfl) ⟨12874220, by rfl⟩ : syracuseStep 17165627 = 25748441) B25748441
theorem B8146291 : Blo 1338988 8146291 := bstep (se 1 (by rfl) ⟨6109718, by rfl⟩ : syracuseStep 8146291 = 12219437) B12219437
theorem B3435895 : Blo 1338988 3435895 := bstep (se 1 (by rfl) ⟨2576921, by rfl⟩ : syracuseStep 3435895 = 5153843) B5153843
theorem B2010503 : Blo 1338988 2010503 := bstep (se 1 (by rfl) ⟨1507877, by rfl⟩ : syracuseStep 2010503 = 3015755) B3015755
theorem B2010539 : Blo 1338988 2010539 := bstep (se 1 (by rfl) ⟨1507904, by rfl⟩ : syracuseStep 2010539 = 3015809) B3015809
theorem B2010569 : Blo 1338988 2010569 := bstep (se 2 (by rfl) ⟨753963, by rfl⟩ : syracuseStep 2010569 = 1507927) B1507927
theorem B66096593 : Blo 1338988 66096593 := bstep (se 2 (by rfl) ⟨24786222, by rfl⟩ : syracuseStep 66096593 = 49572445) B49572445
theorem B2543147 : Blo 1338988 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B11447851 : Blo 1338988 11447851 := bstep (se 1 (by rfl) ⟨8585888, by rfl⟩ : syracuseStep 11447851 = 17171777) B17171777
theorem B2010683 : Blo 1338988 2010683 := bstep (se 1 (by rfl) ⟨1508012, by rfl⟩ : syracuseStep 2010683 = 3016025) B3016025
theorem B4075069 : Blo 1338988 4075069 := bstep (se 3 (by rfl) ⟨764075, by rfl⟩ : syracuseStep 4075069 = 1528151) B1528151
theorem B3624509 : Blo 1338988 3624509 := bstep (se 3 (by rfl) ⟨679595, by rfl⟩ : syracuseStep 3624509 = 1359191) B1359191
theorem B2010743 : Blo 1338988 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B1339015 : Blo 1338988 1339015 := bstep (se 1 (by rfl) ⟨1004261, by rfl⟩ : syracuseStep 1339015 = 2008523) B2008523
theorem B1339023 : Blo 1338988 1339023 := bstep (se 1 (by rfl) ⟨1004267, by rfl⟩ : syracuseStep 1339023 = 2008535) B2008535
theorem B2010767 : Blo 1338988 2010767 := bstep (se 1 (by rfl) ⟨1508075, by rfl⟩ : syracuseStep 2010767 = 3016151) B3016151
theorem B2010809 : Blo 1338988 2010809 := bstep (se 2 (by rfl) ⟨754053, by rfl⟩ : syracuseStep 2010809 = 1508107) B1508107
theorem B1339067 : Blo 1338988 1339067 := bstep (se 1 (by rfl) ⟨1004300, by rfl⟩ : syracuseStep 1339067 = 2008601) B2008601
theorem B1339143 : Blo 1338988 1339143 := bstep (se 1 (by rfl) ⟨1004357, by rfl⟩ : syracuseStep 1339143 = 2008715) B2008715
theorem B2010887 : Blo 1338988 2010887 := bstep (se 1 (by rfl) ⟨1508165, by rfl⟩ : syracuseStep 2010887 = 3016331) B3016331
theorem B1339151 : Blo 1338988 1339151 := bstep (se 1 (by rfl) ⟨1004363, by rfl⟩ : syracuseStep 1339151 = 2008727) B2008727
theorem B2543375 : Blo 1338988 2543375 := bstep (se 1 (by rfl) ⟨1907531, by rfl⟩ : syracuseStep 2543375 = 3815063) B3815063
theorem B3813149 : Blo 1338988 3813149 := bstep (se 3 (by rfl) ⟨714965, by rfl⟩ : syracuseStep 3813149 = 1429931) B1429931
theorem B6524705 : Blo 1338988 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B7630625 : Blo 1338988 7630625 := bstep (se 2 (by rfl) ⟨2861484, by rfl⟩ : syracuseStep 7630625 = 5722969) B5722969
theorem B2010923 : Blo 1338988 2010923 := bstep (se 1 (by rfl) ⟨1508192, by rfl⟩ : syracuseStep 2010923 = 3016385) B3016385
theorem B1339195 : Blo 1338988 1339195 := bstep (se 1 (by rfl) ⟨1004396, by rfl⟩ : syracuseStep 1339195 = 2008793) B2008793
theorem B4828987 : Blo 1338988 4828987 := bstep (se 1 (by rfl) ⟨3621740, by rfl⟩ : syracuseStep 4828987 = 7243481) B7243481
theorem B2010953 : Blo 1338988 2010953 := bstep (se 2 (by rfl) ⟨754107, by rfl⟩ : syracuseStep 2010953 = 1508215) B1508215
theorem B12218201 : Blo 1338988 12218201 := bstep (se 2 (by rfl) ⟨4581825, by rfl⟩ : syracuseStep 12218201 = 9163651) B9163651
theorem B6442841 : Blo 1338988 6442841 := bstep (se 2 (by rfl) ⟨2416065, by rfl⟩ : syracuseStep 6442841 = 4832131) B4832131
theorem B1339271 : Blo 1338988 1339271 := bstep (se 1 (by rfl) ⟨1004453, by rfl⟩ : syracuseStep 1339271 = 2008907) B2008907
theorem B1339279 : Blo 1338988 1339279 := bstep (se 1 (by rfl) ⟨1004459, by rfl⟩ : syracuseStep 1339279 = 2008919) B2008919
theorem B32591767 : Blo 1338988 32591767 := bstep (se 1 (by rfl) ⟨24443825, by rfl⟩ : syracuseStep 32591767 = 48887651) B48887651
theorem B1339323 : Blo 1338988 1339323 := bstep (se 1 (by rfl) ⟨1004492, by rfl⟩ : syracuseStep 1339323 = 2008985) B2008985
theorem B2011067 : Blo 1338988 2011067 := bstep (se 1 (by rfl) ⟨1508300, by rfl⟩ : syracuseStep 2011067 = 3016601) B3016601
theorem B14479307 : Blo 1338988 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B2011127 : Blo 1338988 2011127 := bstep (se 1 (by rfl) ⟨1508345, by rfl⟩ : syracuseStep 2011127 = 3016691) B3016691
theorem B1339399 : Blo 1338988 1339399 := bstep (se 1 (by rfl) ⟨1004549, by rfl⟩ : syracuseStep 1339399 = 2009099) B2009099
theorem B1609735 : Blo 1338988 1609735 := bstep (se 1 (by rfl) ⟨1207301, by rfl⟩ : syracuseStep 1609735 = 2414603) B2414603
theorem B1339407 : Blo 1338988 1339407 := bstep (se 1 (by rfl) ⟨1004555, by rfl⟩ : syracuseStep 1339407 = 2009111) B2009111
theorem B2011151 : Blo 1338988 2011151 := bstep (se 1 (by rfl) ⟨1508363, by rfl⟩ : syracuseStep 2011151 = 3016727) B3016727
theorem B7737367 : Blo 1338988 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B15274007 : Blo 1338988 15274007 := bstep (se 1 (by rfl) ⟨11455505, by rfl⟩ : syracuseStep 15274007 = 22911011) B22911011
theorem B2011193 : Blo 1338988 2011193 := bstep (se 2 (by rfl) ⟨754197, by rfl⟩ : syracuseStep 2011193 = 1508395) B1508395
theorem B1339451 : Blo 1338988 1339451 := bstep (se 1 (by rfl) ⟨1004588, by rfl⟩ : syracuseStep 1339451 = 2009177) B2009177
theorem B1339527 : Blo 1338988 1339527 := bstep (se 1 (by rfl) ⟨1004645, by rfl⟩ : syracuseStep 1339527 = 2009291) B2009291
theorem B2011271 : Blo 1338988 2011271 := bstep (se 1 (by rfl) ⟨1508453, by rfl⟩ : syracuseStep 2011271 = 3016907) B3016907
theorem B1339535 : Blo 1338988 1339535 := bstep (se 1 (by rfl) ⟨1004651, by rfl⟩ : syracuseStep 1339535 = 2009303) B2009303
theorem B2011307 : Blo 1338988 2011307 := bstep (se 1 (by rfl) ⟨1508480, by rfl⟩ : syracuseStep 2011307 = 3016961) B3016961
theorem B1339579 : Blo 1338988 1339579 := bstep (se 1 (by rfl) ⟨1004684, by rfl⟩ : syracuseStep 1339579 = 2009369) B2009369
theorem B2011337 : Blo 1338988 2011337 := bstep (se 2 (by rfl) ⟨754251, by rfl⟩ : syracuseStep 2011337 = 1508503) B1508503
theorem B61870321 : Blo 1338988 61870321 := bstep (se 2 (by rfl) ⟨23201370, by rfl⟩ : syracuseStep 61870321 = 46402741) B46402741
theorem B1339655 : Blo 1338988 1339655 := bstep (se 1 (by rfl) ⟨1004741, by rfl⟩ : syracuseStep 1339655 = 2009483) B2009483
theorem B1339663 : Blo 1338988 1339663 := bstep (se 1 (by rfl) ⟨1004747, by rfl⟩ : syracuseStep 1339663 = 2009495) B2009495
theorem B1339707 : Blo 1338988 1339707 := bstep (se 1 (by rfl) ⟨1004780, by rfl⟩ : syracuseStep 1339707 = 2009561) B2009561
theorem B2011451 : Blo 1338988 2011451 := bstep (se 1 (by rfl) ⟨1508588, by rfl⟩ : syracuseStep 2011451 = 3017177) B3017177
theorem B1339783 : Blo 1338988 1339783 := bstep (se 1 (by rfl) ⟨1004837, by rfl⟩ : syracuseStep 1339783 = 2009675) B2009675
theorem B1339791 : Blo 1338988 1339791 := bstep (se 1 (by rfl) ⟨1004843, by rfl⟩ : syracuseStep 1339791 = 2009687) B2009687
theorem B6787475 : Blo 1338988 6787475 := bstep (se 1 (by rfl) ⟨5090606, by rfl⟩ : syracuseStep 6787475 = 10181213) B10181213
theorem B1339835 : Blo 1338988 1339835 := bstep (se 1 (by rfl) ⟨1004876, by rfl⟩ : syracuseStep 1339835 = 2009753) B2009753
theorem B1339911 : Blo 1338988 1339911 := bstep (se 1 (by rfl) ⟨1004933, by rfl⟩ : syracuseStep 1339911 = 2009867) B2009867
theorem B1339919 : Blo 1338988 1339919 := bstep (se 1 (by rfl) ⟨1004939, by rfl⟩ : syracuseStep 1339919 = 2009879) B2009879
theorem B7836203 : Blo 1338988 7836203 := bstep (se 1 (by rfl) ⟨5877152, by rfl⟩ : syracuseStep 7836203 = 11754305) B11754305
theorem B1339963 : Blo 1338988 1339963 := bstep (se 1 (by rfl) ⟨1004972, by rfl⟩ : syracuseStep 1339963 = 2009945) B2009945
theorem B1340039 : Blo 1338988 1340039 := bstep (se 1 (by rfl) ⟨1005029, by rfl⟩ : syracuseStep 1340039 = 2010059) B2010059
theorem B1340047 : Blo 1338988 1340047 := bstep (se 1 (by rfl) ⟨1005035, by rfl⟩ : syracuseStep 1340047 = 2010071) B2010071
theorem B16528049 : Blo 1338988 16528049 := bstep (se 2 (by rfl) ⟨6198018, by rfl⟩ : syracuseStep 16528049 = 12396037) B12396037
theorem B1340091 : Blo 1338988 1340091 := bstep (se 1 (by rfl) ⟨1005068, by rfl⟩ : syracuseStep 1340091 = 2010137) B2010137
theorem B7443173 : Blo 1338988 7443173 := bstep (se 4 (by rfl) ⟨697797, by rfl⟩ : syracuseStep 7443173 = 1395595) B1395595
theorem B1340167 : Blo 1338988 1340167 := bstep (se 1 (by rfl) ⟨1005125, by rfl⟩ : syracuseStep 1340167 = 2010251) B2010251
theorem B1340175 : Blo 1338988 1340175 := bstep (se 1 (by rfl) ⟨1005131, by rfl⟩ : syracuseStep 1340175 = 2010263) B2010263
theorem B5157665 : Blo 1338988 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B6779699 : Blo 1338988 6779699 := bstep (se 1 (by rfl) ⟨5084774, by rfl⟩ : syracuseStep 6779699 = 10169549) B10169549
theorem B1340219 : Blo 1338988 1340219 := bstep (se 1 (by rfl) ⟨1005164, by rfl⟩ : syracuseStep 1340219 = 2010329) B2010329
theorem B1340295 : Blo 1338988 1340295 := bstep (se 1 (by rfl) ⟨1005221, by rfl⟩ : syracuseStep 1340295 = 2010443) B2010443
theorem B1340303 : Blo 1338988 1340303 := bstep (se 1 (by rfl) ⟨1005227, by rfl⟩ : syracuseStep 1340303 = 2010455) B2010455
theorem B1741739 : Blo 1338988 1741739 := bstep (se 1 (by rfl) ⟨1306304, by rfl⟩ : syracuseStep 1741739 = 2612609) B2612609
theorem B27898805 : Blo 1338988 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B1340347 : Blo 1338988 1340347 := bstep (se 1 (by rfl) ⟨1005260, by rfl⟩ : syracuseStep 1340347 = 2010521) B2010521
theorem B2413513 : Blo 1338988 2413513 := bstep (se 2 (by rfl) ⟨905067, by rfl⟩ : syracuseStep 2413513 = 1810135) B1810135
theorem B1340423 : Blo 1338988 1340423 := bstep (se 1 (by rfl) ⟨1005317, by rfl⟩ : syracuseStep 1340423 = 2010635) B2010635
theorem B16290827 : Blo 1338988 16290827 := bstep (se 1 (by rfl) ⟨12218120, by rfl⟩ : syracuseStep 16290827 = 24436241) B24436241
theorem B2716687 : Blo 1338988 2716687 := bstep (se 1 (by rfl) ⟨2037515, by rfl⟩ : syracuseStep 2716687 = 4075031) B4075031
theorem B1340431 : Blo 1338988 1340431 := bstep (se 1 (by rfl) ⟨1005323, by rfl⟩ : syracuseStep 1340431 = 2010647) B2010647
theorem B1340475 : Blo 1338988 1340475 := bstep (se 1 (by rfl) ⟨1005356, by rfl⟩ : syracuseStep 1340475 = 2010713) B2010713
theorem B65205323 : Blo 1338988 65205323 := bstep (se 1 (by rfl) ⟨48903992, by rfl⟩ : syracuseStep 65205323 = 97807985) B97807985
theorem B15692887 : Blo 1338988 15692887 := bstep (se 1 (by rfl) ⟨11769665, by rfl⟩ : syracuseStep 15692887 = 23539331) B23539331
theorem B6780023 : Blo 1338988 6780023 := bstep (se 1 (by rfl) ⟨5085017, by rfl⟩ : syracuseStep 6780023 = 10170035) B10170035
theorem B1340551 : Blo 1338988 1340551 := bstep (se 1 (by rfl) ⟨1005413, by rfl⟩ : syracuseStep 1340551 = 2010827) B2010827
theorem B1340559 : Blo 1338988 1340559 := bstep (se 1 (by rfl) ⟨1005419, by rfl⟩ : syracuseStep 1340559 = 2010839) B2010839
theorem B2544787 : Blo 1338988 2544787 := bstep (se 1 (by rfl) ⟨1908590, by rfl⟩ : syracuseStep 2544787 = 3817181) B3817181
theorem B1340603 : Blo 1338988 1340603 := bstep (se 1 (by rfl) ⟨1005452, by rfl⟩ : syracuseStep 1340603 = 2010905) B2010905
theorem B8582381 : Blo 1338988 8582381 := bstep (se 3 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 8582381 = 3218393) B3218393
theorem B1340679 : Blo 1338988 1340679 := bstep (se 1 (by rfl) ⟨1005509, by rfl⟩ : syracuseStep 1340679 = 2011019) B2011019
theorem B1340687 : Blo 1338988 1340687 := bstep (se 1 (by rfl) ⟨1005515, by rfl⟩ : syracuseStep 1340687 = 2011031) B2011031
theorem B7238963 : Blo 1338988 7238963 := bstep (se 1 (by rfl) ⟨5429222, by rfl⟩ : syracuseStep 7238963 = 10858445) B10858445
theorem B1340731 : Blo 1338988 1340731 := bstep (se 1 (by rfl) ⟨1005548, by rfl⟩ : syracuseStep 1340731 = 2011097) B2011097
theorem B2545015 : Blo 1338988 2545015 := bstep (se 1 (by rfl) ⟨1908761, by rfl⟩ : syracuseStep 2545015 = 3817523) B3817523
theorem B1340807 : Blo 1338988 1340807 := bstep (se 1 (by rfl) ⟨1005605, by rfl⟩ : syracuseStep 1340807 = 2011211) B2011211
theorem B1340815 : Blo 1338988 1340815 := bstep (se 1 (by rfl) ⟨1005611, by rfl⟩ : syracuseStep 1340815 = 2011223) B2011223
theorem B1340859 : Blo 1338988 1340859 := bstep (se 1 (by rfl) ⟨1005644, by rfl⟩ : syracuseStep 1340859 = 2011289) B2011289
theorem B1340935 : Blo 1338988 1340935 := bstep (se 1 (by rfl) ⟨1005701, by rfl⟩ : syracuseStep 1340935 = 2011403) B2011403
theorem B1340943 : Blo 1338988 1340943 := bstep (se 1 (by rfl) ⟨1005707, by rfl⟩ : syracuseStep 1340943 = 2011415) B2011415
theorem B1340987 : Blo 1338988 1340987 := bstep (se 1 (by rfl) ⟨1005740, by rfl⟩ : syracuseStep 1340987 = 2011481) B2011481
theorem B16307905 : Blo 1338988 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B2037449 : Blo 1338988 2037449 := bstep (se 2 (by rfl) ⟨764043, by rfl⟩ : syracuseStep 2037449 = 1528087) B1528087
theorem B2717473 : Blo 1338988 2717473 := bstep (se 2 (by rfl) ⟨1019052, by rfl⟩ : syracuseStep 2717473 = 2038105) B2038105
theorem B15259427 : Blo 1338988 15259427 := bstep (se 1 (by rfl) ⟨11444570, by rfl⟩ : syracuseStep 15259427 = 22889141) B22889141
theorem B14489381 : Blo 1338988 14489381 := bstep (se 4 (by rfl) ⟨1358379, by rfl⟩ : syracuseStep 14489381 = 2716759) B2716759
theorem B6616883 : Blo 1338988 6616883 := bstep (se 1 (by rfl) ⟨4962662, by rfl⟩ : syracuseStep 6616883 = 9925325) B9925325
theorem B3217211 : Blo 1338988 3217211 := bstep (se 1 (by rfl) ⟨2412908, by rfl⟩ : syracuseStep 3217211 = 4825817) B4825817
theorem B1906745 : Blo 1338988 1906745 := bstep (se 2 (by rfl) ⟨715029, by rfl⟩ : syracuseStep 1906745 = 1430059) B1430059
theorem B8255555 : Blo 1338988 8255555 := bstep (se 1 (by rfl) ⟨6191666, by rfl⟩ : syracuseStep 8255555 = 12383333) B12383333
theorem B6780995 : Blo 1338988 6780995 := bstep (se 1 (by rfl) ⟨5085746, by rfl⟩ : syracuseStep 6780995 = 10171493) B10171493
theorem B1906831 : Blo 1338988 1906831 := bstep (se 1 (by rfl) ⟨1430123, by rfl⟩ : syracuseStep 1906831 = 2860247) B2860247
theorem B1906859 : Blo 1338988 1906859 := bstep (se 1 (by rfl) ⟨1430144, by rfl⟩ : syracuseStep 1906859 = 2860289) B2860289
theorem B5503177 : Blo 1338988 5503177 := bstep (se 2 (by rfl) ⟨2063691, by rfl⟩ : syracuseStep 5503177 = 4127383) B4127383
theorem B3815723 : Blo 1338988 3815723 := bstep (se 1 (by rfl) ⟨2861792, by rfl⟩ : syracuseStep 3815723 = 5723585) B5723585
theorem B3012983 : Blo 1338988 3012983 := bstep (se 1 (by rfl) ⟨2259737, by rfl⟩ : syracuseStep 3012983 = 4519475) B4519475
theorem B6781319 : Blo 1338988 6781319 := bstep (se 1 (by rfl) ⟨5085989, by rfl⟩ : syracuseStep 6781319 = 10171979) B10171979
theorem B4520339 : Blo 1338988 4520339 := bstep (se 1 (by rfl) ⟨3390254, by rfl⟩ : syracuseStep 4520339 = 6780509) B6780509
theorem B5085625 : Blo 1338988 5085625 := bstep (se 2 (by rfl) ⟨1907109, by rfl⟩ : syracuseStep 5085625 = 3814219) B3814219
theorem B6879755 : Blo 1338988 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B3013163 : Blo 1338988 3013163 := bstep (se 1 (by rfl) ⟨2259872, by rfl⟩ : syracuseStep 3013163 = 4519745) B4519745
theorem B41278019 : Blo 1338988 41278019 := bstep (se 1 (by rfl) ⟨30958514, by rfl⟩ : syracuseStep 41278019 = 61917029) B61917029
theorem B8591939 : Blo 1338988 8591939 := bstep (se 1 (by rfl) ⟨6443954, by rfl⟩ : syracuseStep 8591939 = 12887909) B12887909
theorem B6437495 : Blo 1338988 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B7633723 : Blo 1338988 7633723 := bstep (se 1 (by rfl) ⟨5725292, by rfl⟩ : syracuseStep 7633723 = 11450585) B11450585
theorem B3390295 : Blo 1338988 3390295 := bstep (se 1 (by rfl) ⟨2542721, by rfl⟩ : syracuseStep 3390295 = 5085443) B5085443
theorem B3013523 : Blo 1338988 3013523 := bstep (se 1 (by rfl) ⟨2260142, by rfl⟩ : syracuseStep 3013523 = 4520285) B4520285
theorem B2259913 : Blo 1338988 2259913 := bstep (se 2 (by rfl) ⟨847467, by rfl⟩ : syracuseStep 2259913 = 1694935) B1694935
theorem B3013577 : Blo 1338988 3013577 := bstep (se 2 (by rfl) ⟨1130091, by rfl⟩ : syracuseStep 3013577 = 2260183) B2260183
theorem B4291613 : Blo 1338988 4291613 := bstep (se 3 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 4291613 = 1609355) B1609355
theorem B1694839 : Blo 1338988 1694839 := bstep (se 1 (by rfl) ⟨1271129, by rfl⟩ : syracuseStep 1694839 = 2542259) B2542259
theorem B3390599 : Blo 1338988 3390599 := bstep (se 1 (by rfl) ⟨2542949, by rfl⟩ : syracuseStep 3390599 = 5085899) B5085899
theorem B3923129 : Blo 1338988 3923129 := bstep (se 2 (by rfl) ⟨1471173, by rfl⟩ : syracuseStep 3923129 = 2942347) B2942347
theorem B3218633 : Blo 1338988 3218633 := bstep (se 2 (by rfl) ⟨1206987, by rfl⟩ : syracuseStep 3218633 = 2413975) B2413975
theorem B3439817 : Blo 1338988 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B3390731 : Blo 1338988 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B41270627 : Blo 1338988 41270627 := bstep (se 1 (by rfl) ⟨30952970, by rfl⟩ : syracuseStep 41270627 = 61905941) B61905941
theorem B1506703 : Blo 1338988 1506703 := bstep (se 1 (by rfl) ⟨1130027, by rfl⟩ : syracuseStep 1506703 = 2260055) B2260055
theorem B1695163 : Blo 1338988 1695163 := bstep (se 1 (by rfl) ⟨1271372, by rfl⟩ : syracuseStep 1695163 = 2542745) B2542745
theorem B19316177 : Blo 1338988 19316177 := bstep (se 2 (by rfl) ⟨7243566, by rfl⟩ : syracuseStep 19316177 = 14487133) B14487133
theorem B1719815 : Blo 1338988 1719815 := bstep (se 1 (by rfl) ⟨1289861, by rfl⟩ : syracuseStep 1719815 = 2579723) B2579723
theorem B7626251 : Blo 1338988 7626251 := bstep (se 1 (by rfl) ⟨5719688, by rfl⟩ : syracuseStep 7626251 = 11439377) B11439377
theorem B25755205 : Blo 1338988 25755205 := bstep (se 4 (by rfl) ⟨2414550, by rfl⟩ : syracuseStep 25755205 = 4829101) B4829101
theorem B2260615 : Blo 1338988 2260615 := bstep (se 1 (by rfl) ⟨1695461, by rfl⟩ : syracuseStep 2260615 = 3390923) B3390923
theorem B3014279 : Blo 1338988 3014279 := bstep (se 1 (by rfl) ⟨2260709, by rfl⟩ : syracuseStep 3014279 = 4521419) B4521419
theorem B7626433 : Blo 1338988 7626433 := bstep (se 2 (by rfl) ⟨2859912, by rfl⟩ : syracuseStep 7626433 = 5719825) B5719825
theorem B8822465 : Blo 1338988 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B15269633 : Blo 1338988 15269633 := bstep (se 2 (by rfl) ⟨5726112, by rfl⟩ : syracuseStep 15269633 = 11452225) B11452225
theorem B3391247 : Blo 1338988 3391247 := bstep (se 1 (by rfl) ⟨2543435, by rfl⟩ : syracuseStep 3391247 = 5086871) B5086871
theorem B4521743 : Blo 1338988 4521743 := bstep (se 1 (by rfl) ⟨3391307, by rfl⟩ : syracuseStep 4521743 = 6782615) B6782615
theorem B6438689 : Blo 1338988 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B3014459 : Blo 1338988 3014459 := bstep (se 1 (by rfl) ⟨2260844, by rfl⟩ : syracuseStep 3014459 = 4521689) B4521689
theorem B7339835 : Blo 1338988 7339835 := bstep (se 1 (by rfl) ⟨5504876, by rfl⟩ : syracuseStep 7339835 = 11009753) B11009753
theorem B5726011 : Blo 1338988 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B1507207 : Blo 1338988 1507207 := bstep (se 1 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 1507207 = 2260811) B2260811
theorem B3391379 : Blo 1338988 3391379 := bstep (se 1 (by rfl) ⟨2543534, by rfl⟩ : syracuseStep 3391379 = 5087069) B5087069
theorem B3817363 : Blo 1338988 3817363 := bstep (se 1 (by rfl) ⟨2863022, by rfl⟩ : syracuseStep 3817363 = 5726045) B5726045
theorem B3014585 : Blo 1338988 3014585 := bstep (se 2 (by rfl) ⟨1130469, by rfl⟩ : syracuseStep 3014585 = 2260939) B2260939
theorem B2146313 : Blo 1338988 2146313 := bstep (se 2 (by rfl) ⟨804867, by rfl⟩ : syracuseStep 2146313 = 1609735) B1609735
theorem B10182671 : Blo 1338988 10182671 := bstep (se 1 (by rfl) ⟨7637003, by rfl⟩ : syracuseStep 10182671 = 15274007) B15274007
theorem B3014675 : Blo 1338988 3014675 := bstep (se 1 (by rfl) ⟨2261006, by rfl⟩ : syracuseStep 3014675 = 4522013) B4522013
theorem B82493761 : Blo 1338988 82493761 := bstep (se 2 (by rfl) ⟨30935160, by rfl⟩ : syracuseStep 82493761 = 61870321) B61870321
theorem B3015017 : Blo 1338988 3015017 := bstep (se 2 (by rfl) ⟨1130631, by rfl⟩ : syracuseStep 3015017 = 2261263) B2261263
theorem B11018699 : Blo 1338988 11018699 := bstep (se 1 (by rfl) ⟨8264024, by rfl⟩ : syracuseStep 11018699 = 16528049) B16528049
theorem B2261513 : Blo 1338988 2261513 := bstep (se 2 (by rfl) ⟨848067, by rfl⟩ : syracuseStep 2261513 = 1696135) B1696135
theorem B1507963 : Blo 1338988 1507963 := bstep (se 1 (by rfl) ⟨1130972, by rfl⟩ : syracuseStep 1507963 = 2261945) B2261945
theorem B2261675 : Blo 1338988 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B3392351 : Blo 1338988 3392351 := bstep (se 1 (by rfl) ⟨2544263, by rfl⟩ : syracuseStep 3392351 = 5088527) B5088527
theorem B4825975 : Blo 1338988 4825975 := bstep (se 1 (by rfl) ⟨3619481, by rfl⟩ : syracuseStep 4825975 = 7238963) B7238963
theorem B3015611 : Blo 1338988 3015611 := bstep (se 1 (by rfl) ⟨2261708, by rfl⟩ : syracuseStep 3015611 = 4523417) B4523417
theorem B9659357 : Blo 1338988 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B3015737 : Blo 1338988 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B2262073 : Blo 1338988 2262073 := bstep (se 2 (by rfl) ⟨848277, by rfl⟩ : syracuseStep 2262073 = 1696555) B1696555
theorem B1508431 : Blo 1338988 1508431 := bstep (se 1 (by rfl) ⟨1131323, by rfl⟩ : syracuseStep 1508431 = 2262647) B2262647
theorem B7636139 : Blo 1338988 7636139 := bstep (se 1 (by rfl) ⟨5727104, by rfl⟩ : syracuseStep 7636139 = 11454209) B11454209
theorem B9659587 : Blo 1338988 9659587 := bstep (se 1 (by rfl) ⟨7244690, by rfl⟩ : syracuseStep 9659587 = 14489381) B14489381
theorem B2262215 : Blo 1338988 2262215 := bstep (se 1 (by rfl) ⟨1696661, by rfl⟩ : syracuseStep 2262215 = 3393323) B3393323
theorem B4523255 : Blo 1338988 4523255 := bstep (se 1 (by rfl) ⟨3392441, by rfl⟩ : syracuseStep 4523255 = 6784883) B6784883
theorem B2147575 : Blo 1338988 2147575 := bstep (se 1 (by rfl) ⟨1610681, by rfl⟩ : syracuseStep 2147575 = 3221363) B3221363
theorem B3622249 : Blo 1338988 3622249 := bstep (se 2 (by rfl) ⟨1358343, by rfl⟩ : syracuseStep 3622249 = 2716687) B2716687
theorem B2262377 : Blo 1338988 2262377 := bstep (se 2 (by rfl) ⟨848391, by rfl⟩ : syracuseStep 2262377 = 1696783) B1696783
theorem B3016079 : Blo 1338988 3016079 := bstep (se 1 (by rfl) ⟨2262059, by rfl⟩ : syracuseStep 3016079 = 4524119) B4524119
theorem B20923849 : Blo 1338988 20923849 := bstep (se 2 (by rfl) ⟨7846443, by rfl⟩ : syracuseStep 20923849 = 15692887) B15692887
theorem B3393049 : Blo 1338988 3393049 := bstep (se 2 (by rfl) ⟨1272393, by rfl⟩ : syracuseStep 3393049 = 2544787) B2544787
theorem B4523579 : Blo 1338988 4523579 := bstep (se 1 (by rfl) ⟨3392684, by rfl⟩ : syracuseStep 4523579 = 6785369) B6785369
theorem B2008655 : Blo 1338988 2008655 := bstep (se 1 (by rfl) ⟨1506491, by rfl⟩ : syracuseStep 2008655 = 3012983) B3012983
theorem B2008775 : Blo 1338988 2008775 := bstep (se 1 (by rfl) ⟨1506581, by rfl⟩ : syracuseStep 2008775 = 3013163) B3013163
theorem B6440647 : Blo 1338988 6440647 := bstep (se 1 (by rfl) ⟨4830485, by rfl⟩ : syracuseStep 6440647 = 9660971) B9660971
theorem B3016403 : Blo 1338988 3016403 := bstep (se 1 (by rfl) ⟨2262302, by rfl⟩ : syracuseStep 3016403 = 4524605) B4524605
theorem B5727959 : Blo 1338988 5727959 := bstep (se 1 (by rfl) ⟨4295969, by rfl⟩ : syracuseStep 5727959 = 8591939) B8591939
theorem B2262775 : Blo 1338988 2262775 := bstep (se 1 (by rfl) ⟨1697081, by rfl⟩ : syracuseStep 2262775 = 3394163) B3394163
theorem B4581193 : Blo 1338988 4581193 := bstep (se 2 (by rfl) ⟨1717947, by rfl⟩ : syracuseStep 4581193 = 3435895) B3435895
theorem B4523849 : Blo 1338988 4523849 := bstep (se 2 (by rfl) ⟨1696443, by rfl⟩ : syracuseStep 4523849 = 3392887) B3392887
theorem B3393353 : Blo 1338988 3393353 := bstep (se 2 (by rfl) ⟨1272507, by rfl⟩ : syracuseStep 3393353 = 2545015) B2545015
theorem B2008937 : Blo 1338988 2008937 := bstep (se 2 (by rfl) ⟨753351, by rfl⟩ : syracuseStep 2008937 = 1506703) B1506703
theorem B2009015 : Blo 1338988 2009015 := bstep (se 1 (by rfl) ⟨1506761, by rfl⟩ : syracuseStep 2009015 = 3013523) B3013523
theorem B2009051 : Blo 1338988 2009051 := bstep (se 1 (by rfl) ⟨1506788, by rfl⟩ : syracuseStep 2009051 = 3013577) B3013577
theorem B2861075 : Blo 1338988 2861075 := bstep (se 1 (by rfl) ⟨2145806, by rfl⟩ : syracuseStep 2861075 = 4291613) B4291613
theorem B15263801 : Blo 1338988 15263801 := bstep (se 2 (by rfl) ⟨5723925, by rfl⟩ : syracuseStep 15263801 = 11447851) B11447851
theorem B5433425 : Blo 1338988 5433425 := bstep (se 2 (by rfl) ⟨2037534, by rfl⟩ : syracuseStep 5433425 = 4075069) B4075069
theorem B2615419 : Blo 1338988 2615419 := bstep (se 1 (by rfl) ⟨1961564, by rfl⟩ : syracuseStep 2615419 = 3923129) B3923129
theorem B10168577 : Blo 1338988 10168577 := bstep (se 2 (by rfl) ⟨3813216, by rfl⟩ : syracuseStep 10168577 = 7626433) B7626433
theorem B21743873 : Blo 1338988 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B3623297 : Blo 1338988 3623297 := bstep (se 2 (by rfl) ⟨1358736, by rfl⟩ : syracuseStep 3623297 = 2717473) B2717473
theorem B2009519 : Blo 1338988 2009519 := bstep (se 1 (by rfl) ⟨1507139, by rfl⟩ : syracuseStep 2009519 = 3014279) B3014279
theorem B2009609 : Blo 1338988 2009609 := bstep (se 2 (by rfl) ⟨753603, by rfl⟩ : syracuseStep 2009609 = 1507207) B1507207
theorem B2542099 : Blo 1338988 2542099 := bstep (se 1 (by rfl) ⟨1906574, by rfl⟩ : syracuseStep 2542099 = 3813149) B3813149
theorem B5089817 : Blo 1338988 5089817 := bstep (se 2 (by rfl) ⟨1908681, by rfl⟩ : syracuseStep 5089817 = 3817363) B3817363
theorem B4893223 : Blo 1338988 4893223 := bstep (se 1 (by rfl) ⟨3669917, by rfl⟩ : syracuseStep 4893223 = 7339835) B7339835
theorem B2009639 : Blo 1338988 2009639 := bstep (se 1 (by rfl) ⟨1507229, by rfl⟩ : syracuseStep 2009639 = 3014459) B3014459
theorem B8145467 : Blo 1338988 8145467 := bstep (se 1 (by rfl) ⟨6109100, by rfl⟩ : syracuseStep 8145467 = 12218201) B12218201
theorem B4295227 : Blo 1338988 4295227 := bstep (se 1 (by rfl) ⟨3221420, by rfl⟩ : syracuseStep 4295227 = 6442841) B6442841
theorem B2009723 : Blo 1338988 2009723 := bstep (se 1 (by rfl) ⟨1507292, by rfl⟩ : syracuseStep 2009723 = 3014585) B3014585
theorem B9652871 : Blo 1338988 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B10316489 : Blo 1338988 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B4827863 : Blo 1338988 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B18344693 : Blo 1338988 18344693 := bstep (se 5 (by rfl) ⟨859907, by rfl⟩ : syracuseStep 18344693 = 1719815) B1719815
theorem B2009849 : Blo 1338988 2009849 := bstep (se 2 (by rfl) ⟨753693, by rfl⟩ : syracuseStep 2009849 = 1507387) B1507387
theorem B8579843 : Blo 1338988 8579843 := bstep (se 1 (by rfl) ⟨6434882, by rfl⟩ : syracuseStep 8579843 = 12869765) B12869765
theorem B2009951 : Blo 1338988 2009951 := bstep (se 1 (by rfl) ⟨1507463, by rfl⟩ : syracuseStep 2009951 = 3014927) B3014927
theorem B2542441 : Blo 1338988 2542441 := bstep (se 2 (by rfl) ⟨953415, by rfl⟩ : syracuseStep 2542441 = 1906831) B1906831
theorem B2009963 : Blo 1338988 2009963 := bstep (se 1 (by rfl) ⟨1507472, by rfl⟩ : syracuseStep 2009963 = 3014945) B3014945
theorem B4524983 : Blo 1338988 4524983 := bstep (se 1 (by rfl) ⟨3393737, by rfl⟩ : syracuseStep 4524983 = 6787475) B6787475
theorem B7629875 : Blo 1338988 7629875 := bstep (se 1 (by rfl) ⟨5722406, by rfl⟩ : syracuseStep 7629875 = 11444813) B11444813
theorem B2010191 : Blo 1338988 2010191 := bstep (se 1 (by rfl) ⟨1507643, by rfl⟩ : syracuseStep 2010191 = 3015287) B3015287
theorem B4959313 : Blo 1338988 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B4828355 : Blo 1338988 4828355 := bstep (se 1 (by rfl) ⟨3621266, by rfl⟩ : syracuseStep 4828355 = 7242533) B7242533
theorem B2010311 : Blo 1338988 2010311 := bstep (se 1 (by rfl) ⟨1507733, by rfl⟩ : syracuseStep 2010311 = 3015467) B3015467
theorem B18599203 : Blo 1338988 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B2010473 : Blo 1338988 2010473 := bstep (se 2 (by rfl) ⟨753927, by rfl⟩ : syracuseStep 2010473 = 1507855) B1507855
theorem B43470215 : Blo 1338988 43470215 := bstep (se 1 (by rfl) ⟨32602661, by rfl⟩ : syracuseStep 43470215 = 65205323) B65205323
theorem B2010551 : Blo 1338988 2010551 := bstep (se 1 (by rfl) ⟨1507913, by rfl⟩ : syracuseStep 2010551 = 3015827) B3015827
theorem B2010587 : Blo 1338988 2010587 := bstep (se 1 (by rfl) ⟨1507940, by rfl⟩ : syracuseStep 2010587 = 3015881) B3015881
theorem B5721587 : Blo 1338988 5721587 := bstep (se 1 (by rfl) ⟨4291190, by rfl⟩ : syracuseStep 5721587 = 8582381) B8582381
theorem B4525577 : Blo 1338988 4525577 := bstep (se 2 (by rfl) ⟨1697091, by rfl⟩ : syracuseStep 4525577 = 3394183) B3394183
theorem B6524513 : Blo 1338988 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B1339003 : Blo 1338988 1339003 := bstep (se 1 (by rfl) ⟨1004252, by rfl⟩ : syracuseStep 1339003 = 2008505) B2008505
theorem B2862715 : Blo 1338988 2862715 := bstep (se 1 (by rfl) ⟨2147036, by rfl⟩ : syracuseStep 2862715 = 4294073) B4294073
theorem B1339055 : Blo 1338988 1339055 := bstep (se 1 (by rfl) ⟨1004291, by rfl⟩ : syracuseStep 1339055 = 2008583) B2008583
theorem B1339079 : Blo 1338988 1339079 := bstep (se 1 (by rfl) ⟨1004309, by rfl⟩ : syracuseStep 1339079 = 2008619) B2008619
theorem B4828871 : Blo 1338988 4828871 := bstep (se 1 (by rfl) ⟨3621653, by rfl⟩ : syracuseStep 4828871 = 7243307) B7243307
theorem B1339099 : Blo 1338988 1339099 := bstep (se 1 (by rfl) ⟨1004324, by rfl⟩ : syracuseStep 1339099 = 2008649) B2008649
theorem B10178297 : Blo 1338988 10178297 := bstep (se 2 (by rfl) ⟨3816861, by rfl⟩ : syracuseStep 10178297 = 7633723) B7633723
theorem B1339175 : Blo 1338988 1339175 := bstep (se 1 (by rfl) ⟨1004381, by rfl⟩ : syracuseStep 1339175 = 2008763) B2008763
theorem B1339215 : Blo 1338988 1339215 := bstep (se 1 (by rfl) ⟨1004411, by rfl⟩ : syracuseStep 1339215 = 2008823) B2008823
theorem B1339231 : Blo 1338988 1339231 := bstep (se 1 (by rfl) ⟨1004423, by rfl⟩ : syracuseStep 1339231 = 2008847) B2008847
theorem B4411255 : Blo 1338988 4411255 := bstep (se 1 (by rfl) ⟨3308441, by rfl⟩ : syracuseStep 4411255 = 6616883) B6616883
theorem B1339259 : Blo 1338988 1339259 := bstep (se 1 (by rfl) ⟨1004444, by rfl⟩ : syracuseStep 1339259 = 2008889) B2008889
theorem B1339311 : Blo 1338988 1339311 := bstep (se 1 (by rfl) ⟨1004483, by rfl⟩ : syracuseStep 1339311 = 2008967) B2008967
theorem B2011055 : Blo 1338988 2011055 := bstep (se 1 (by rfl) ⟨1508291, by rfl⟩ : syracuseStep 2011055 = 3016583) B3016583
theorem B1339335 : Blo 1338988 1339335 := bstep (se 1 (by rfl) ⟨1004501, by rfl⟩ : syracuseStep 1339335 = 2009003) B2009003
theorem B1339355 : Blo 1338988 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B2011145 : Blo 1338988 2011145 := bstep (se 2 (by rfl) ⟨754179, by rfl⟩ : syracuseStep 2011145 = 1508359) B1508359
theorem B18346013 : Blo 1338988 18346013 := bstep (se 3 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 18346013 = 6879755) B6879755
theorem B1339431 : Blo 1338988 1339431 := bstep (se 1 (by rfl) ⟨1004573, by rfl⟩ : syracuseStep 1339431 = 2009147) B2009147
theorem B2011175 : Blo 1338988 2011175 := bstep (se 1 (by rfl) ⟨1508381, by rfl⟩ : syracuseStep 2011175 = 3016763) B3016763
theorem B1339471 : Blo 1338988 1339471 := bstep (se 1 (by rfl) ⟨1004603, by rfl⟩ : syracuseStep 1339471 = 2009207) B2009207
theorem B1339487 : Blo 1338988 1339487 := bstep (se 1 (by rfl) ⟨1004615, by rfl⟩ : syracuseStep 1339487 = 2009231) B2009231
theorem B5091443 : Blo 1338988 5091443 := bstep (se 1 (by rfl) ⟨3818582, by rfl⟩ : syracuseStep 5091443 = 7637165) B7637165
theorem B1339515 : Blo 1338988 1339515 := bstep (se 1 (by rfl) ⟨1004636, by rfl⟩ : syracuseStep 1339515 = 2009273) B2009273
theorem B2011259 : Blo 1338988 2011259 := bstep (se 1 (by rfl) ⟨1508444, by rfl⟩ : syracuseStep 2011259 = 3016889) B3016889
theorem B1339567 : Blo 1338988 1339567 := bstep (se 1 (by rfl) ⟨1004675, by rfl⟩ : syracuseStep 1339567 = 2009351) B2009351
theorem B1339591 : Blo 1338988 1339591 := bstep (se 1 (by rfl) ⟨1004693, by rfl⟩ : syracuseStep 1339591 = 2009387) B2009387
theorem B2543815 : Blo 1338988 2543815 := bstep (se 1 (by rfl) ⟨1907861, by rfl⟩ : syracuseStep 2543815 = 3815723) B3815723
theorem B1339611 : Blo 1338988 1339611 := bstep (se 1 (by rfl) ⟨1004708, by rfl⟩ : syracuseStep 1339611 = 2009417) B2009417
theorem B2011385 : Blo 1338988 2011385 := bstep (se 2 (by rfl) ⟨754269, by rfl⟩ : syracuseStep 2011385 = 1508539) B1508539
theorem B1339687 : Blo 1338988 1339687 := bstep (se 1 (by rfl) ⟨1004765, by rfl⟩ : syracuseStep 1339687 = 2009531) B2009531
theorem B17166653 : Blo 1338988 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B1339727 : Blo 1338988 1339727 := bstep (se 1 (by rfl) ⟨1004795, by rfl⟩ : syracuseStep 1339727 = 2009591) B2009591
theorem B1339743 : Blo 1338988 1339743 := bstep (se 1 (by rfl) ⟨1004807, by rfl⟩ : syracuseStep 1339743 = 2009615) B2009615
theorem B1339771 : Blo 1338988 1339771 := bstep (se 1 (by rfl) ⟨1004828, by rfl⟩ : syracuseStep 1339771 = 2009657) B2009657
theorem B1339823 : Blo 1338988 1339823 := bstep (se 1 (by rfl) ⟨1004867, by rfl⟩ : syracuseStep 1339823 = 2009735) B2009735
theorem B1339847 : Blo 1338988 1339847 := bstep (se 1 (by rfl) ⟨1004885, by rfl⟩ : syracuseStep 1339847 = 2009771) B2009771
theorem B1339867 : Blo 1338988 1339867 := bstep (se 1 (by rfl) ⟨1004900, by rfl⟩ : syracuseStep 1339867 = 2009801) B2009801
theorem B1339943 : Blo 1338988 1339943 := bstep (se 1 (by rfl) ⟨1004957, by rfl⟩ : syracuseStep 1339943 = 2009915) B2009915
theorem B1339983 : Blo 1338988 1339983 := bstep (se 1 (by rfl) ⟨1004987, by rfl⟩ : syracuseStep 1339983 = 2009975) B2009975
theorem B1339999 : Blo 1338988 1339999 := bstep (se 1 (by rfl) ⟨1004999, by rfl⟩ : syracuseStep 1339999 = 2009999) B2009999
theorem B1340027 : Blo 1338988 1340027 := bstep (se 1 (by rfl) ⟨1005020, by rfl⟩ : syracuseStep 1340027 = 2010041) B2010041
theorem B1340079 : Blo 1338988 1340079 := bstep (se 1 (by rfl) ⟨1005059, by rfl⟩ : syracuseStep 1340079 = 2010119) B2010119
theorem B1340103 : Blo 1338988 1340103 := bstep (se 1 (by rfl) ⟨1005077, by rfl⟩ : syracuseStep 1340103 = 2010155) B2010155
theorem B1340123 : Blo 1338988 1340123 := bstep (se 1 (by rfl) ⟨1005092, by rfl⟩ : syracuseStep 1340123 = 2010185) B2010185
theorem B1340199 : Blo 1338988 1340199 := bstep (se 1 (by rfl) ⟨1005149, by rfl⟩ : syracuseStep 1340199 = 2010299) B2010299
theorem B2863945 : Blo 1338988 2863945 := bstep (se 2 (by rfl) ⟨1073979, by rfl⟩ : syracuseStep 2863945 = 2147959) B2147959
theorem B1340239 : Blo 1338988 1340239 := bstep (se 1 (by rfl) ⟨1005179, by rfl⟩ : syracuseStep 1340239 = 2010359) B2010359
theorem B1340255 : Blo 1338988 1340255 := bstep (se 1 (by rfl) ⟨1005191, by rfl⟩ : syracuseStep 1340255 = 2010383) B2010383
theorem B1340283 : Blo 1338988 1340283 := bstep (se 1 (by rfl) ⟨1005212, by rfl⟩ : syracuseStep 1340283 = 2010425) B2010425
theorem B27513751 : Blo 1338988 27513751 := bstep (se 1 (by rfl) ⟨20635313, by rfl⟩ : syracuseStep 27513751 = 41270627) B41270627
theorem B1340335 : Blo 1338988 1340335 := bstep (se 1 (by rfl) ⟨1005251, by rfl⟩ : syracuseStep 1340335 = 2010503) B2010503
theorem B1340359 : Blo 1338988 1340359 := bstep (se 1 (by rfl) ⟨1005269, by rfl⟩ : syracuseStep 1340359 = 2010539) B2010539
theorem B1340379 : Blo 1338988 1340379 := bstep (se 1 (by rfl) ⟨1005284, by rfl⟩ : syracuseStep 1340379 = 2010569) B2010569
theorem B5084167 : Blo 1338988 5084167 := bstep (se 1 (by rfl) ⟨3813125, by rfl⟩ : syracuseStep 5084167 = 7626251) B7626251
theorem B1340455 : Blo 1338988 1340455 := bstep (se 1 (by rfl) ⟨1005341, by rfl⟩ : syracuseStep 1340455 = 2010683) B2010683
theorem B1340495 : Blo 1338988 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B1340511 : Blo 1338988 1340511 := bstep (se 1 (by rfl) ⟨1005383, by rfl⟩ : syracuseStep 1340511 = 2010767) B2010767
theorem B1340539 : Blo 1338988 1340539 := bstep (se 1 (by rfl) ⟨1005404, by rfl⟩ : syracuseStep 1340539 = 2010809) B2010809
theorem B10179755 : Blo 1338988 10179755 := bstep (se 1 (by rfl) ⟨7634816, by rfl⟩ : syracuseStep 10179755 = 15269633) B15269633
theorem B1340591 : Blo 1338988 1340591 := bstep (se 1 (by rfl) ⟨1005443, by rfl⟩ : syracuseStep 1340591 = 2010887) B2010887
theorem B1340615 : Blo 1338988 1340615 := bstep (se 1 (by rfl) ⟨1005461, by rfl⟩ : syracuseStep 1340615 = 2010923) B2010923
theorem B43455689 : Blo 1338988 43455689 := bstep (se 2 (by rfl) ⟨16295883, by rfl⟩ : syracuseStep 43455689 = 32591767) B32591767
theorem B1340635 : Blo 1338988 1340635 := bstep (se 1 (by rfl) ⟨1005476, by rfl⟩ : syracuseStep 1340635 = 2010953) B2010953
theorem B1340711 : Blo 1338988 1340711 := bstep (se 1 (by rfl) ⟨1005533, by rfl⟩ : syracuseStep 1340711 = 2011067) B2011067
theorem B1340751 : Blo 1338988 1340751 := bstep (se 1 (by rfl) ⟨1005563, by rfl⟩ : syracuseStep 1340751 = 2011127) B2011127
theorem B1430879 : Blo 1338988 1430879 := bstep (se 1 (by rfl) ⟨1073159, by rfl⟩ : syracuseStep 1430879 = 2146319) B2146319
theorem B1340767 : Blo 1338988 1340767 := bstep (se 1 (by rfl) ⟨1005575, by rfl⟩ : syracuseStep 1340767 = 2011151) B2011151
theorem B1340795 : Blo 1338988 1340795 := bstep (se 1 (by rfl) ⟨1005596, by rfl⟩ : syracuseStep 1340795 = 2011193) B2011193
theorem B1340847 : Blo 1338988 1340847 := bstep (se 1 (by rfl) ⟨1005635, by rfl⟩ : syracuseStep 1340847 = 2011271) B2011271
theorem B1340871 : Blo 1338988 1340871 := bstep (se 1 (by rfl) ⟨1005653, by rfl⟩ : syracuseStep 1340871 = 2011307) B2011307
theorem B1340891 : Blo 1338988 1340891 := bstep (se 1 (by rfl) ⟨1005668, by rfl⟩ : syracuseStep 1340891 = 2011337) B2011337
theorem B5084653 : Blo 1338988 5084653 := bstep (se 3 (by rfl) ⟨953372, by rfl⟩ : syracuseStep 5084653 = 1906745) B1906745
theorem B1340967 : Blo 1338988 1340967 := bstep (se 1 (by rfl) ⟨1005725, by rfl⟩ : syracuseStep 1340967 = 2011451) B2011451
theorem B10180241 : Blo 1338988 10180241 := bstep (se 2 (by rfl) ⟨3817590, by rfl⟩ : syracuseStep 10180241 = 7635181) B7635181
theorem B5224135 : Blo 1338988 5224135 := bstep (se 1 (by rfl) ⟨3918101, by rfl⟩ : syracuseStep 5224135 = 7836203) B7836203
theorem B5084957 : Blo 1338988 5084957 := bstep (se 3 (by rfl) ⟨953429, by rfl⟩ : syracuseStep 5084957 = 1906859) B1906859
theorem B4962115 : Blo 1338988 4962115 := bstep (se 1 (by rfl) ⟨3721586, by rfl⟩ : syracuseStep 4962115 = 7443173) B7443173
theorem B4831049 : Blo 1338988 4831049 := bstep (se 2 (by rfl) ⟨1811643, by rfl⟩ : syracuseStep 4831049 = 3623287) B3623287
theorem B3438443 : Blo 1338988 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B4519799 : Blo 1338988 4519799 := bstep (se 1 (by rfl) ⟨3389849, by rfl⟩ : syracuseStep 4519799 = 6779699) B6779699
theorem B6780833 : Blo 1338988 6780833 := bstep (se 2 (by rfl) ⟨2542812, by rfl⟩ : syracuseStep 6780833 = 5085625) B5085625
theorem B10860551 : Blo 1338988 10860551 := bstep (se 1 (by rfl) ⟨8145413, by rfl⟩ : syracuseStep 10860551 = 16290827) B16290827
theorem B4520015 : Blo 1338988 4520015 := bstep (se 1 (by rfl) ⟨3390011, by rfl⟩ : syracuseStep 4520015 = 6780023) B6780023
theorem B1431631 : Blo 1338988 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B29350277 : Blo 1338988 29350277 := bstep (se 4 (by rfl) ⟨2751588, by rfl⟩ : syracuseStep 29350277 = 5503177) B5503177
theorem B4520393 : Blo 1338988 4520393 := bstep (se 2 (by rfl) ⟨1695147, by rfl⟩ : syracuseStep 4520393 = 3390295) B3390295
theorem B1358299 : Blo 1338988 1358299 := bstep (se 1 (by rfl) ⟨1018724, by rfl⟩ : syracuseStep 1358299 = 2037449) B2037449
theorem B10172951 : Blo 1338988 10172951 := bstep (se 1 (by rfl) ⟨7629713, by rfl⟩ : syracuseStep 10172951 = 15259427) B15259427
theorem B2144807 : Blo 1338988 2144807 := bstep (se 1 (by rfl) ⟨1608605, by rfl⟩ : syracuseStep 2144807 = 3217211) B3217211
theorem B2415143 : Blo 1338988 2415143 := bstep (se 1 (by rfl) ⟨1811357, by rfl⟩ : syracuseStep 2415143 = 3622715) B3622715
theorem B3013217 : Blo 1338988 3013217 := bstep (se 2 (by rfl) ⟨1129956, by rfl⟩ : syracuseStep 3013217 = 2259913) B2259913
theorem B3218017 : Blo 1338988 3218017 := bstep (se 2 (by rfl) ⟨1206756, by rfl⟩ : syracuseStep 3218017 = 2413513) B2413513
theorem B5503703 : Blo 1338988 5503703 := bstep (se 1 (by rfl) ⟨4127777, by rfl⟩ : syracuseStep 5503703 = 8255555) B8255555
theorem B4520663 : Blo 1338988 4520663 := bstep (se 1 (by rfl) ⟨3390497, by rfl⟩ : syracuseStep 4520663 = 6780995) B6780995
theorem B2259785 : Blo 1338988 2259785 := bstep (se 2 (by rfl) ⟨847419, by rfl⟩ : syracuseStep 2259785 = 1694839) B1694839
theorem B110074717 : Blo 1338988 110074717 := bstep (se 3 (by rfl) ⟨20639009, by rfl⟩ : syracuseStep 110074717 = 41278019) B41278019
theorem B4520879 : Blo 1338988 4520879 := bstep (se 1 (by rfl) ⟨3390659, by rfl⟩ : syracuseStep 4520879 = 6781319) B6781319
theorem B3013559 : Blo 1338988 3013559 := bstep (se 1 (by rfl) ⟨2260169, by rfl⟩ : syracuseStep 3013559 = 4520339) B4520339
theorem B10181699 : Blo 1338988 10181699 := bstep (se 1 (by rfl) ⟨7636274, by rfl⟩ : syracuseStep 10181699 = 15272549) B15272549
theorem B10861721 : Blo 1338988 10861721 := bstep (se 2 (by rfl) ⟨4073145, by rfl⟩ : syracuseStep 10861721 = 8146291) B8146291
theorem B2260217 : Blo 1338988 2260217 := bstep (se 2 (by rfl) ⟨847581, by rfl⟩ : syracuseStep 2260217 = 1695163) B1695163
theorem B2260399 : Blo 1338988 2260399 := bstep (se 1 (by rfl) ⟨1695299, by rfl⟩ : syracuseStep 2260399 = 3390599) B3390599
theorem B34340273 : Blo 1338988 34340273 := bstep (se 2 (by rfl) ⟨12877602, by rfl⟩ : syracuseStep 34340273 = 25755205) B25755205
theorem B2145755 : Blo 1338988 2145755 := bstep (se 1 (by rfl) ⟨1609316, by rfl⟩ : syracuseStep 2145755 = 3218633) B3218633
theorem B2293211 : Blo 1338988 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B2260487 : Blo 1338988 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B3014153 : Blo 1338988 3014153 := bstep (se 2 (by rfl) ⟨1130307, by rfl⟩ : syracuseStep 3014153 = 2260615) B2260615
theorem B11443751 : Blo 1338988 11443751 := bstep (se 1 (by rfl) ⟨8582813, by rfl⟩ : syracuseStep 11443751 = 17165627) B17165627
theorem B12877451 : Blo 1338988 12877451 := bstep (se 1 (by rfl) ⟨9658088, by rfl⟩ : syracuseStep 12877451 = 19316177) B19316177
theorem B44064395 : Blo 1338988 44064395 := bstep (se 1 (by rfl) ⟨33048296, by rfl⟩ : syracuseStep 44064395 = 66096593) B66096593
theorem B1695431 : Blo 1338988 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B2416339 : Blo 1338988 2416339 := bstep (se 1 (by rfl) ⟨1812254, by rfl⟩ : syracuseStep 2416339 = 3624509) B3624509
theorem B6438649 : Blo 1338988 6438649 := bstep (se 2 (by rfl) ⟨2414493, by rfl⟩ : syracuseStep 6438649 = 4828987) B4828987
theorem B7634681 : Blo 1338988 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B4644637 : Blo 1338988 4644637 := bstep (se 3 (by rfl) ⟨870869, by rfl⟩ : syracuseStep 4644637 = 1741739) B1741739
theorem B5881643 : Blo 1338988 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B1695583 : Blo 1338988 1695583 := bstep (se 1 (by rfl) ⟨1271687, by rfl⟩ : syracuseStep 1695583 = 2543375) B2543375
theorem B2260831 : Blo 1338988 2260831 := bstep (se 1 (by rfl) ⟨1695623, by rfl⟩ : syracuseStep 2260831 = 3391247) B3391247
theorem B3014495 : Blo 1338988 3014495 := bstep (se 1 (by rfl) ⟨2260871, by rfl⟩ : syracuseStep 3014495 = 4521743) B4521743
theorem B4349803 : Blo 1338988 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B5087083 : Blo 1338988 5087083 := bstep (se 1 (by rfl) ⟨3815312, by rfl⟩ : syracuseStep 5087083 = 7630625) B7630625
theorem B4292459 : Blo 1338988 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B2260919 : Blo 1338988 2260919 := bstep (se 1 (by rfl) ⟨1695689, by rfl⟩ : syracuseStep 2260919 = 3391379) B3391379
theorem B12230675 : Blo 1338988 12230675 := bstep (se 1 (by rfl) ⟨9173006, by rfl⟩ : syracuseStep 12230675 = 18346013) B18346013
theorem B1908841 : Blo 1338988 1908841 := bstep (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) B1431631
theorem B11444435 : Blo 1338988 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B3391753 : Blo 1338988 3391753 := bstep (se 2 (by rfl) ⟨1271907, by rfl⟩ : syracuseStep 3391753 = 2543815) B2543815
theorem B1507675 : Blo 1338988 1507675 := bstep (se 1 (by rfl) ⟨1130756, by rfl⟩ : syracuseStep 1507675 = 2261513) B2261513
theorem B1507783 : Blo 1338988 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B2261567 : Blo 1338988 2261567 := bstep (se 1 (by rfl) ⟨1696175, by rfl⟩ : syracuseStep 2261567 = 3392351) B3392351
theorem B6439571 : Blo 1338988 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B5726969 : Blo 1338988 5726969 := bstep (se 2 (by rfl) ⟨2147613, by rfl⟩ : syracuseStep 5726969 = 4295227) B4295227
theorem B1508143 : Blo 1338988 1508143 := bstep (se 1 (by rfl) ⟨1131107, by rfl⟩ : syracuseStep 1508143 = 2262215) B2262215
theorem B3015503 : Blo 1338988 3015503 := bstep (se 1 (by rfl) ⟨2261627, by rfl⟩ : syracuseStep 3015503 = 4523255) B4523255
theorem B1508251 : Blo 1338988 1508251 := bstep (se 1 (by rfl) ⟨1131188, by rfl⟩ : syracuseStep 1508251 = 2262377) B2262377
theorem B3015719 : Blo 1338988 3015719 := bstep (se 1 (by rfl) ⟨2261789, by rfl⟩ : syracuseStep 3015719 = 4523579) B4523579
theorem B3818593 : Blo 1338988 3818593 := bstep (se 2 (by rfl) ⟨1431972, by rfl⟩ : syracuseStep 3818593 = 2863945) B2863945
theorem B3818639 : Blo 1338988 3818639 := bstep (se 1 (by rfl) ⟨2863979, by rfl⟩ : syracuseStep 3818639 = 5727959) B5727959
theorem B36685001 : Blo 1338988 36685001 := bstep (se 2 (by rfl) ⟨13756875, by rfl⟩ : syracuseStep 36685001 = 27513751) B27513751
theorem B3015899 : Blo 1338988 3015899 := bstep (se 1 (by rfl) ⟨2261924, by rfl⟩ : syracuseStep 3015899 = 4523849) B4523849
theorem B2262235 : Blo 1338988 2262235 := bstep (se 1 (by rfl) ⟨1696676, by rfl⟩ : syracuseStep 2262235 = 3393353) B3393353
theorem B10175867 : Blo 1338988 10175867 := bstep (se 1 (by rfl) ⟨7631900, by rfl⟩ : syracuseStep 10175867 = 15263801) B15263801
theorem B3622283 : Blo 1338988 3622283 := bstep (se 1 (by rfl) ⟨2716712, by rfl⟩ : syracuseStep 3622283 = 5433425) B5433425
theorem B3016097 : Blo 1338988 3016097 := bstep (se 2 (by rfl) ⟨1131036, by rfl⟩ : syracuseStep 3016097 = 2262073) B2262073
theorem B6440381 : Blo 1338988 6440381 := bstep (se 3 (by rfl) ⟨1207571, by rfl⟩ : syracuseStep 6440381 = 2415143) B2415143
theorem B12879449 : Blo 1338988 12879449 := bstep (se 2 (by rfl) ⟨4829793, by rfl⟩ : syracuseStep 12879449 = 9659587) B9659587
theorem B3393211 : Blo 1338988 3393211 := bstep (se 1 (by rfl) ⟨2544908, by rfl⟩ : syracuseStep 3393211 = 5089817) B5089817
theorem B25740989 : Blo 1338988 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B2008811 : Blo 1338988 2008811 := bstep (se 1 (by rfl) ⟨1506608, by rfl⟩ : syracuseStep 2008811 = 3013217) B3013217
theorem B5719895 : Blo 1338988 5719895 := bstep (se 1 (by rfl) ⟨4289921, by rfl⟩ : syracuseStep 5719895 = 8579843) B8579843
theorem B19318661 : Blo 1338988 19318661 := bstep (se 4 (by rfl) ⟨1811124, by rfl⟩ : syracuseStep 19318661 = 3622249) B3622249
theorem B2009039 : Blo 1338988 2009039 := bstep (se 1 (by rfl) ⟨1506779, by rfl⟩ : syracuseStep 2009039 = 3013559) B3013559
theorem B3016655 : Blo 1338988 3016655 := bstep (se 1 (by rfl) ⟨2262491, by rfl⟩ : syracuseStep 3016655 = 4524983) B4524983
theorem B4524065 : Blo 1338988 4524065 := bstep (se 2 (by rfl) ⟨1696524, by rfl⟩ : syracuseStep 4524065 = 3393049) B3393049
theorem B58706165 : Blo 1338988 58706165 := bstep (se 5 (by rfl) ⟨2751851, by rfl⟩ : syracuseStep 58706165 = 5503703) B5503703
theorem B6965513 : Blo 1338988 6965513 := bstep (se 2 (by rfl) ⟨2612067, by rfl⟩ : syracuseStep 6965513 = 5224135) B5224135
theorem B8587529 : Blo 1338988 8587529 := bstep (se 2 (by rfl) ⟨3220323, by rfl⟩ : syracuseStep 8587529 = 6440647) B6440647
theorem B3221785 : Blo 1338988 3221785 := bstep (se 2 (by rfl) ⟨1208169, by rfl⟩ : syracuseStep 3221785 = 2416339) B2416339
theorem B3017033 : Blo 1338988 3017033 := bstep (se 2 (by rfl) ⟨1131387, by rfl⟩ : syracuseStep 3017033 = 2262775) B2262775
theorem B2009435 : Blo 1338988 2009435 := bstep (se 1 (by rfl) ⟨1507076, by rfl⟩ : syracuseStep 2009435 = 3014153) B3014153
theorem B3017051 : Blo 1338988 3017051 := bstep (se 1 (by rfl) ⟨2262788, by rfl⟩ : syracuseStep 3017051 = 4525577) B4525577
theorem B7629167 : Blo 1338988 7629167 := bstep (se 1 (by rfl) ⟨5721875, by rfl⟩ : syracuseStep 7629167 = 11443751) B11443751
theorem B7244261 : Blo 1338988 7244261 := bstep (se 4 (by rfl) ⟨679149, by rfl⟩ : syracuseStep 7244261 = 1358299) B1358299
theorem B6785531 : Blo 1338988 6785531 := bstep (se 1 (by rfl) ⟨5089148, by rfl⟩ : syracuseStep 6785531 = 10178297) B10178297
theorem B5089787 : Blo 1338988 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B2009663 : Blo 1338988 2009663 := bstep (se 1 (by rfl) ⟨1507247, by rfl⟩ : syracuseStep 2009663 = 3014495) B3014495
theorem B2861639 : Blo 1338988 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B2009783 : Blo 1338988 2009783 := bstep (se 1 (by rfl) ⟨1507337, by rfl⟩ : syracuseStep 2009783 = 3014675) B3014675
theorem B3394295 : Blo 1338988 3394295 := bstep (se 1 (by rfl) ⟨2545721, by rfl⟩ : syracuseStep 3394295 = 5091443) B5091443
theorem B2010011 : Blo 1338988 2010011 := bstep (se 1 (by rfl) ⟨1507508, by rfl⟩ : syracuseStep 2010011 = 3015017) B3015017
theorem B2010407 : Blo 1338988 2010407 := bstep (se 1 (by rfl) ⟨1507805, by rfl⟩ : syracuseStep 2010407 = 3015611) B3015611
theorem B2010491 : Blo 1338988 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B6524297 : Blo 1338988 6524297 := bstep (se 2 (by rfl) ⟨2446611, by rfl⟩ : syracuseStep 6524297 = 4893223) B4893223
theorem B6786503 : Blo 1338988 6786503 := bstep (se 1 (by rfl) ⟨5089877, by rfl⟩ : syracuseStep 6786503 = 10179755) B10179755
theorem B5090759 : Blo 1338988 5090759 := bstep (se 1 (by rfl) ⟨3818069, by rfl⟩ : syracuseStep 5090759 = 7636139) B7636139
theorem B28970459 : Blo 1338988 28970459 := bstep (se 1 (by rfl) ⟨21727844, by rfl⟩ : syracuseStep 28970459 = 43455689) B43455689
theorem B2010617 : Blo 1338988 2010617 := bstep (se 2 (by rfl) ⟨753981, by rfl⟩ : syracuseStep 2010617 = 1507963) B1507963
theorem B2010719 : Blo 1338988 2010719 := bstep (se 1 (by rfl) ⟨1508039, by rfl⟩ : syracuseStep 2010719 = 3016079) B3016079
theorem B9662125 : Blo 1338988 9662125 := bstep (se 3 (by rfl) ⟨1811648, by rfl⟩ : syracuseStep 9662125 = 3623297) B3623297
theorem B1339103 : Blo 1338988 1339103 := bstep (se 1 (by rfl) ⟨1004327, by rfl⟩ : syracuseStep 1339103 = 2008655) B2008655
theorem B6786827 : Blo 1338988 6786827 := bstep (se 1 (by rfl) ⟨5090120, by rfl⟩ : syracuseStep 6786827 = 10180241) B10180241
theorem B1339183 : Blo 1338988 1339183 := bstep (se 1 (by rfl) ⟨1004387, by rfl⟩ : syracuseStep 1339183 = 2008775) B2008775
theorem B2010935 : Blo 1338988 2010935 := bstep (se 1 (by rfl) ⟨1508201, by rfl⟩ : syracuseStep 2010935 = 3016403) B3016403
theorem B6434633 : Blo 1338988 6434633 := bstep (se 2 (by rfl) ⟨2412987, by rfl⟩ : syracuseStep 6434633 = 4825975) B4825975
theorem B1339291 : Blo 1338988 1339291 := bstep (se 1 (by rfl) ⟨1004468, by rfl⟩ : syracuseStep 1339291 = 2008937) B2008937
theorem B6115229 : Blo 1338988 6115229 := bstep (se 3 (by rfl) ⟨1146605, by rfl⟩ : syracuseStep 6115229 = 2293211) B2293211
theorem B1339343 : Blo 1338988 1339343 := bstep (se 1 (by rfl) ⟨1004507, by rfl⟩ : syracuseStep 1339343 = 2009015) B2009015
theorem B1339367 : Blo 1338988 1339367 := bstep (se 1 (by rfl) ⟨1004525, by rfl⟩ : syracuseStep 1339367 = 2009051) B2009051
theorem B6778889 : Blo 1338988 6778889 := bstep (se 2 (by rfl) ⟨2542083, by rfl⟩ : syracuseStep 6778889 = 5084167) B5084167
theorem B2011241 : Blo 1338988 2011241 := bstep (se 2 (by rfl) ⟨754215, by rfl⟩ : syracuseStep 2011241 = 1508431) B1508431
theorem B6779051 : Blo 1338988 6779051 := bstep (se 1 (by rfl) ⟨5084288, by rfl⟩ : syracuseStep 6779051 = 10168577) B10168577
theorem B14495915 : Blo 1338988 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B19566851 : Blo 1338988 19566851 := bstep (se 1 (by rfl) ⟨14675138, by rfl⟩ : syracuseStep 19566851 = 29350277) B29350277
theorem B1339679 : Blo 1338988 1339679 := bstep (se 1 (by rfl) ⟨1004759, by rfl⟩ : syracuseStep 1339679 = 2009519) B2009519
theorem B2863433 : Blo 1338988 2863433 := bstep (se 2 (by rfl) ⟨1073787, by rfl⟩ : syracuseStep 2863433 = 2147575) B2147575
theorem B1339739 : Blo 1338988 1339739 := bstep (se 1 (by rfl) ⟨1004804, by rfl⟩ : syracuseStep 1339739 = 2009609) B2009609
theorem B1429871 : Blo 1338988 1429871 := bstep (se 1 (by rfl) ⟨1072403, by rfl⟩ : syracuseStep 1429871 = 2144807) B2144807
theorem B1339759 : Blo 1338988 1339759 := bstep (se 1 (by rfl) ⟨1004819, by rfl⟩ : syracuseStep 1339759 = 2009639) B2009639
theorem B1339815 : Blo 1338988 1339815 := bstep (se 1 (by rfl) ⟨1004861, by rfl⟩ : syracuseStep 1339815 = 2009723) B2009723
theorem B1339899 : Blo 1338988 1339899 := bstep (se 1 (by rfl) ⟨1004924, by rfl⟩ : syracuseStep 1339899 = 2009849) B2009849
theorem B12874301 : Blo 1338988 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B1339967 : Blo 1338988 1339967 := bstep (se 1 (by rfl) ⟨1004975, by rfl⟩ : syracuseStep 1339967 = 2009951) B2009951
theorem B1339975 : Blo 1338988 1339975 := bstep (se 1 (by rfl) ⟨1004981, by rfl⟩ : syracuseStep 1339975 = 2009963) B2009963
theorem B27898465 : Blo 1338988 27898465 := bstep (se 2 (by rfl) ⟨10461924, by rfl⟩ : syracuseStep 27898465 = 20923849) B20923849
theorem B6779537 : Blo 1338988 6779537 := bstep (se 2 (by rfl) ⟨2542326, by rfl⟩ : syracuseStep 6779537 = 5084653) B5084653
theorem B6787799 : Blo 1338988 6787799 := bstep (se 1 (by rfl) ⟨5090849, by rfl⟩ : syracuseStep 6787799 = 10181699) B10181699
theorem B1340127 : Blo 1338988 1340127 := bstep (se 1 (by rfl) ⟨1005095, by rfl⟩ : syracuseStep 1340127 = 2010191) B2010191
theorem B1340207 : Blo 1338988 1340207 := bstep (se 1 (by rfl) ⟨1005155, by rfl⟩ : syracuseStep 1340207 = 2010311) B2010311
theorem B12882797 : Blo 1338988 12882797 := bstep (se 3 (by rfl) ⟨2415524, by rfl⟩ : syracuseStep 12882797 = 4831049) B4831049
theorem B1340315 : Blo 1338988 1340315 := bstep (se 1 (by rfl) ⟨1005236, by rfl⟩ : syracuseStep 1340315 = 2010473) B2010473
theorem B28980143 : Blo 1338988 28980143 := bstep (se 1 (by rfl) ⟨21735107, by rfl⟩ : syracuseStep 28980143 = 43470215) B43470215
theorem B22893515 : Blo 1338988 22893515 := bstep (se 1 (by rfl) ⟨17170136, by rfl⟩ : syracuseStep 22893515 = 34340273) B34340273
theorem B1340367 : Blo 1338988 1340367 := bstep (se 1 (by rfl) ⟨1005275, by rfl⟩ : syracuseStep 1340367 = 2010551) B2010551
theorem B1430503 : Blo 1338988 1430503 := bstep (se 1 (by rfl) ⟨1072877, by rfl⟩ : syracuseStep 1430503 = 2145755) B2145755
theorem B1340391 : Blo 1338988 1340391 := bstep (se 1 (by rfl) ⟨1005293, by rfl⟩ : syracuseStep 1340391 = 2010587) B2010587
theorem B3814391 : Blo 1338988 3814391 := bstep (se 1 (by rfl) ⟨2860793, by rfl⟩ : syracuseStep 3814391 = 5721587) B5721587
theorem B6616153 : Blo 1338988 6616153 := bstep (se 2 (by rfl) ⟨2481057, by rfl⟩ : syracuseStep 6616153 = 4962115) B4962115
theorem B6108257 : Blo 1338988 6108257 := bstep (se 2 (by rfl) ⟨2290596, by rfl⟩ : syracuseStep 6108257 = 4581193) B4581193
theorem B3921095 : Blo 1338988 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B1340703 : Blo 1338988 1340703 := bstep (se 1 (by rfl) ⟨1005527, by rfl⟩ : syracuseStep 1340703 = 2011055) B2011055
theorem B1430875 : Blo 1338988 1430875 := bstep (se 1 (by rfl) ⟨1073156, by rfl⟩ : syracuseStep 1430875 = 2146313) B2146313
theorem B1340763 : Blo 1338988 1340763 := bstep (se 1 (by rfl) ⟨1005572, by rfl⟩ : syracuseStep 1340763 = 2011145) B2011145
theorem B6788447 : Blo 1338988 6788447 := bstep (se 1 (by rfl) ⟨5091335, by rfl⟩ : syracuseStep 6788447 = 10182671) B10182671
theorem B1340783 : Blo 1338988 1340783 := bstep (se 1 (by rfl) ⟨1005587, by rfl⟩ : syracuseStep 1340783 = 2011175) B2011175
theorem B1340839 : Blo 1338988 1340839 := bstep (se 1 (by rfl) ⟨1005629, by rfl⟩ : syracuseStep 1340839 = 2011259) B2011259
theorem B1340923 : Blo 1338988 1340923 := bstep (se 1 (by rfl) ⟨1005692, by rfl⟩ : syracuseStep 1340923 = 2011385) B2011385
theorem B7345799 : Blo 1338988 7345799 := bstep (se 1 (by rfl) ⟨5509349, by rfl⟩ : syracuseStep 7345799 = 11018699) B11018699
theorem B109991681 : Blo 1338988 109991681 := bstep (se 2 (by rfl) ⟨41246880, by rfl⟩ : syracuseStep 109991681 = 82493761) B82493761
theorem B26449669 : Blo 1338988 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B13948901 : Blo 1338988 13948901 := bstep (se 4 (by rfl) ⟨1307709, by rfl⟩ : syracuseStep 13948901 = 2615419) B2615419
theorem B3389465 : Blo 1338988 3389465 := bstep (se 2 (by rfl) ⟨1271049, by rfl⟩ : syracuseStep 3389465 = 2542099) B2542099
theorem B4290689 : Blo 1338988 4290689 := bstep (se 2 (by rfl) ⟨1609008, by rfl⟩ : syracuseStep 4290689 = 3218017) B3218017
theorem B3815677 : Blo 1338988 3815677 := bstep (se 3 (by rfl) ⟨715439, by rfl⟩ : syracuseStep 3815677 = 1430879) B1430879
theorem B146766289 : Blo 1338988 146766289 := bstep (se 2 (by rfl) ⟨55037358, by rfl⟩ : syracuseStep 146766289 = 110074717) B110074717
theorem B3389921 : Blo 1338988 3389921 := bstep (se 2 (by rfl) ⟨1271220, by rfl⟩ : syracuseStep 3389921 = 2542441) B2542441
theorem B3389971 : Blo 1338988 3389971 := bstep (se 1 (by rfl) ⟨2542478, by rfl⟩ : syracuseStep 3389971 = 5084957) B5084957
theorem B2292295 : Blo 1338988 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B3013199 : Blo 1338988 3013199 := bstep (se 1 (by rfl) ⟨2259899, by rfl⟩ : syracuseStep 3013199 = 4519799) B4519799
theorem B4520555 : Blo 1338988 4520555 := bstep (se 1 (by rfl) ⟨3390416, by rfl⟩ : syracuseStep 4520555 = 6780833) B6780833
theorem B7240367 : Blo 1338988 7240367 := bstep (se 1 (by rfl) ⟨5430275, by rfl⟩ : syracuseStep 7240367 = 10860551) B10860551
theorem B1907383 : Blo 1338988 1907383 := bstep (se 1 (by rfl) ⟨1430537, by rfl⟩ : syracuseStep 1907383 = 2861075) B2861075
theorem B3013343 : Blo 1338988 3013343 := bstep (se 1 (by rfl) ⟨2260007, by rfl⟩ : syracuseStep 3013343 = 4520015) B4520015
theorem B24771397 : Blo 1338988 24771397 := bstep (se 4 (by rfl) ⟨2322318, by rfl⟩ : syracuseStep 24771397 = 4644637) B4644637
theorem B99195749 : Blo 1338988 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B3013595 : Blo 1338988 3013595 := bstep (se 1 (by rfl) ⟨2260196, by rfl⟩ : syracuseStep 3013595 = 4520393) B4520393
theorem B6781967 : Blo 1338988 6781967 := bstep (se 1 (by rfl) ⟨5086475, by rfl⟩ : syracuseStep 6781967 = 10172951) B10172951
theorem B5430311 : Blo 1338988 5430311 := bstep (se 1 (by rfl) ⟨4072733, by rfl⟩ : syracuseStep 5430311 = 8145467) B8145467
theorem B3013775 : Blo 1338988 3013775 := bstep (se 1 (by rfl) ⟨2260331, by rfl⟩ : syracuseStep 3013775 = 4520663) B4520663
theorem B12229795 : Blo 1338988 12229795 := bstep (se 1 (by rfl) ⟨9172346, by rfl⟩ : syracuseStep 12229795 = 18344693) B18344693
theorem B4521149 : Blo 1338988 4521149 := bstep (se 3 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 4521149 = 1695431) B1695431
theorem B1506523 : Blo 1338988 1506523 := bstep (se 1 (by rfl) ⟨1129892, by rfl⟩ : syracuseStep 1506523 = 2259785) B2259785
theorem B3013865 : Blo 1338988 3013865 := bstep (se 2 (by rfl) ⟨1130199, by rfl⟩ : syracuseStep 3013865 = 2260399) B2260399
theorem B3013919 : Blo 1338988 3013919 := bstep (se 1 (by rfl) ⟨2260439, by rfl⟩ : syracuseStep 3013919 = 4520879) B4520879
theorem B5086583 : Blo 1338988 5086583 := bstep (se 1 (by rfl) ⟨3814937, by rfl⟩ : syracuseStep 5086583 = 7629875) B7629875
theorem B110042549 : Blo 1338988 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B7241147 : Blo 1338988 7241147 := bstep (se 1 (by rfl) ⟨5430860, by rfl⟩ : syracuseStep 7241147 = 10861721) B10861721
theorem B3218903 : Blo 1338988 3218903 := bstep (se 1 (by rfl) ⟨2414177, by rfl⟩ : syracuseStep 3218903 = 4828355) B4828355
theorem B3816953 : Blo 1338988 3816953 := bstep (se 2 (by rfl) ⟨1431357, by rfl⟩ : syracuseStep 3816953 = 2862715) B2862715
theorem B1506811 : Blo 1338988 1506811 := bstep (se 1 (by rfl) ⟨1130108, by rfl⟩ : syracuseStep 1506811 = 2260217) B2260217
theorem B8584865 : Blo 1338988 8584865 := bstep (se 2 (by rfl) ⟨3219324, by rfl⟩ : syracuseStep 8584865 = 6438649) B6438649
theorem B1506991 : Blo 1338988 1506991 := bstep (se 1 (by rfl) ⟨1130243, by rfl⟩ : syracuseStep 1506991 = 2260487) B2260487
theorem B4349675 : Blo 1338988 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B8584967 : Blo 1338988 8584967 := bstep (se 1 (by rfl) ⟨6438725, by rfl⟩ : syracuseStep 8584967 = 12877451) B12877451
theorem B29376263 : Blo 1338988 29376263 := bstep (se 1 (by rfl) ⟨22032197, by rfl⟩ : syracuseStep 29376263 = 44064395) B44064395
theorem B2260777 : Blo 1338988 2260777 := bstep (se 2 (by rfl) ⟨847791, by rfl⟩ : syracuseStep 2260777 = 1695583) B1695583
theorem B3014441 : Blo 1338988 3014441 := bstep (se 2 (by rfl) ⟨1130415, by rfl⟩ : syracuseStep 3014441 = 2260831) B2260831
theorem B3219247 : Blo 1338988 3219247 := bstep (se 1 (by rfl) ⟨2414435, by rfl⟩ : syracuseStep 3219247 = 4828871) B4828871
theorem B5799737 : Blo 1338988 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B6782777 : Blo 1338988 6782777 := bstep (se 2 (by rfl) ⟨2543541, by rfl⟩ : syracuseStep 6782777 = 5087083) B5087083
theorem B5881673 : Blo 1338988 5881673 := bstep (se 2 (by rfl) ⟨2205627, by rfl⟩ : syracuseStep 5881673 = 4411255) B4411255
theorem B1507279 : Blo 1338988 1507279 := bstep (se 1 (by rfl) ⟨1130459, by rfl⟩ : syracuseStep 1507279 = 2260919) B2260919
theorem B1908955 : Blo 1338988 1908955 := bstep (se 1 (by rfl) ⟨1431716, by rfl⟩ : syracuseStep 1908955 = 2863433) B2863433
theorem B5087569 : Blo 1338988 5087569 := bstep (se 2 (by rfl) ⟨1907838, by rfl⟩ : syracuseStep 5087569 = 3815677) B3815677
theorem B4522337 : Blo 1338988 4522337 := bstep (se 2 (by rfl) ⟨1695876, by rfl⟩ : syracuseStep 4522337 = 3391753) B3391753
theorem B1507711 : Blo 1338988 1507711 := bstep (se 1 (by rfl) ⟨1130783, by rfl⟩ : syracuseStep 1507711 = 2261567) B2261567
theorem B4293047 : Blo 1338988 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B3817979 : Blo 1338988 3817979 := bstep (se 1 (by rfl) ⟨2863484, by rfl⟩ : syracuseStep 3817979 = 5726969) B5726969
theorem B15262343 : Blo 1338988 15262343 := bstep (se 1 (by rfl) ⟨11446757, by rfl⟩ : syracuseStep 15262343 = 22893515) B22893515
theorem B156549773 : Blo 1338988 156549773 := bstep (se 3 (by rfl) ⟨29353082, by rfl⟩ : syracuseStep 156549773 = 58706165) B58706165
theorem B3056393 : Blo 1338988 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B6783911 : Blo 1338988 6783911 := bstep (se 1 (by rfl) ⟨5087933, by rfl⟩ : syracuseStep 6783911 = 10175867) B10175867
theorem B4293587 : Blo 1338988 4293587 := bstep (se 1 (by rfl) ⟨3220190, by rfl⟩ : syracuseStep 4293587 = 6440381) B6440381
theorem B8586299 : Blo 1338988 8586299 := bstep (se 1 (by rfl) ⟨6439724, by rfl⟩ : syracuseStep 8586299 = 12879449) B12879449
theorem B73327787 : Blo 1338988 73327787 := bstep (se 1 (by rfl) ⟨54995840, by rfl⟩ : syracuseStep 73327787 = 109991681) B109991681
theorem B12879107 : Blo 1338988 12879107 := bstep (se 1 (by rfl) ⟨9659330, by rfl⟩ : syracuseStep 12879107 = 19318661) B19318661
theorem B9299267 : Blo 1338988 9299267 := bstep (se 1 (by rfl) ⟨6974450, by rfl⟩ : syracuseStep 9299267 = 13948901) B13948901
theorem B3016043 : Blo 1338988 3016043 := bstep (se 1 (by rfl) ⟨2262032, by rfl⟩ : syracuseStep 3016043 = 4524065) B4524065
theorem B2008697 : Blo 1338988 2008697 := bstep (se 2 (by rfl) ⟨753261, by rfl⟩ : syracuseStep 2008697 = 1506523) B1506523
theorem B3016313 : Blo 1338988 3016313 := bstep (se 2 (by rfl) ⟨1131117, by rfl⟩ : syracuseStep 3016313 = 2262235) B2262235
theorem B4523687 : Blo 1338988 4523687 := bstep (se 1 (by rfl) ⟨3392765, by rfl⟩ : syracuseStep 4523687 = 6785531) B6785531
theorem B3393191 : Blo 1338988 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B2008799 : Blo 1338988 2008799 := bstep (se 1 (by rfl) ⟨1506599, by rfl⟩ : syracuseStep 2008799 = 3013199) B3013199
theorem B4826911 : Blo 1338988 4826911 := bstep (se 1 (by rfl) ⟨3620183, by rfl⟩ : syracuseStep 4826911 = 7240367) B7240367
theorem B2008895 : Blo 1338988 2008895 := bstep (se 1 (by rfl) ⟨1506671, by rfl⟩ : syracuseStep 2008895 = 3013343) B3013343
theorem B2262863 : Blo 1338988 2262863 := bstep (se 1 (by rfl) ⟨1697147, by rfl⟩ : syracuseStep 2262863 = 3394295) B3394295
theorem B2009063 : Blo 1338988 2009063 := bstep (se 1 (by rfl) ⟨1506797, by rfl⟩ : syracuseStep 2009063 = 3013595) B3013595
theorem B2009081 : Blo 1338988 2009081 := bstep (se 2 (by rfl) ⟨753405, by rfl⟩ : syracuseStep 2009081 = 1506811) B1506811
theorem B2009183 : Blo 1338988 2009183 := bstep (se 1 (by rfl) ⟨1506887, by rfl⟩ : syracuseStep 2009183 = 3013775) B3013775
theorem B2009243 : Blo 1338988 2009243 := bstep (se 1 (by rfl) ⟨1506932, by rfl⟩ : syracuseStep 2009243 = 3013865) B3013865
theorem B2009279 : Blo 1338988 2009279 := bstep (se 1 (by rfl) ⟨1506959, by rfl⟩ : syracuseStep 2009279 = 3013919) B3013919
theorem B2009321 : Blo 1338988 2009321 := bstep (se 2 (by rfl) ⟨753495, by rfl⟩ : syracuseStep 2009321 = 1506991) B1506991
theorem B4524281 : Blo 1338988 4524281 := bstep (se 2 (by rfl) ⟨1696605, by rfl⟩ : syracuseStep 4524281 = 3393211) B3393211
theorem B73361699 : Blo 1338988 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B4827431 : Blo 1338988 4827431 := bstep (se 1 (by rfl) ⟨3620573, by rfl⟩ : syracuseStep 4827431 = 7241147) B7241147
theorem B4524335 : Blo 1338988 4524335 := bstep (se 1 (by rfl) ⟨3393251, by rfl⟩ : syracuseStep 4524335 = 6786503) B6786503
theorem B3393839 : Blo 1338988 3393839 := bstep (se 1 (by rfl) ⟨2545379, by rfl⟩ : syracuseStep 3393839 = 5090759) B5090759
theorem B4524551 : Blo 1338988 4524551 := bstep (se 1 (by rfl) ⟨3393413, by rfl⟩ : syracuseStep 4524551 = 6786827) B6786827
theorem B2009627 : Blo 1338988 2009627 := bstep (se 1 (by rfl) ⟨1507220, by rfl⟩ : syracuseStep 2009627 = 3014441) B3014441
theorem B7629349 : Blo 1338988 7629349 := bstep (se 4 (by rfl) ⟨715251, by rfl⟩ : syracuseStep 7629349 = 1430503) B1430503
theorem B2009705 : Blo 1338988 2009705 := bstep (se 2 (by rfl) ⟨753639, by rfl⟩ : syracuseStep 2009705 = 1507279) B1507279
theorem B8153783 : Blo 1338988 8153783 := bstep (se 1 (by rfl) ⟨6115337, by rfl⟩ : syracuseStep 8153783 = 12230675) B12230675
theorem B7629623 : Blo 1338988 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B16288685 : Blo 1338988 16288685 := bstep (se 3 (by rfl) ⟨3054128, by rfl⟩ : syracuseStep 16288685 = 6108257) B6108257
theorem B4295713 : Blo 1338988 4295713 := bstep (se 2 (by rfl) ⟨1610892, by rfl⟩ : syracuseStep 4295713 = 3221785) B3221785
theorem B2010233 : Blo 1338988 2010233 := bstep (se 2 (by rfl) ⟨753837, by rfl⟩ : syracuseStep 2010233 = 1507675) B1507675
theorem B4525199 : Blo 1338988 4525199 := bstep (se 1 (by rfl) ⟨3393899, by rfl⟩ : syracuseStep 4525199 = 6787799) B6787799
theorem B10456253 : Blo 1338988 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B2010335 : Blo 1338988 2010335 := bstep (se 1 (by rfl) ⟨1507751, by rfl⟩ : syracuseStep 2010335 = 3015503) B3015503
theorem B8588531 : Blo 1338988 8588531 := bstep (se 1 (by rfl) ⟨6441398, by rfl⟩ : syracuseStep 8588531 = 12882797) B12882797
theorem B2010377 : Blo 1338988 2010377 := bstep (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) B1507783
theorem B19320095 : Blo 1338988 19320095 := bstep (se 1 (by rfl) ⟨14490071, by rfl⟩ : syracuseStep 19320095 = 28980143) B28980143
theorem B2542927 : Blo 1338988 2542927 := bstep (se 1 (by rfl) ⟨1907195, by rfl⟩ : syracuseStep 2542927 = 3814391) B3814391
theorem B52178269 : Blo 1338988 52178269 := bstep (se 3 (by rfl) ⟨9783425, by rfl⟩ : syracuseStep 52178269 = 19566851) B19566851
theorem B2010479 : Blo 1338988 2010479 := bstep (se 1 (by rfl) ⟨1507859, by rfl⟩ : syracuseStep 2010479 = 3015719) B3015719
theorem B24456667 : Blo 1338988 24456667 := bstep (se 1 (by rfl) ⟨18342500, by rfl⟩ : syracuseStep 24456667 = 36685001) B36685001
theorem B2010599 : Blo 1338988 2010599 := bstep (se 1 (by rfl) ⟨1507949, by rfl⟩ : syracuseStep 2010599 = 3015899) B3015899
theorem B4525631 : Blo 1338988 4525631 := bstep (se 1 (by rfl) ⟨3394223, by rfl⟩ : syracuseStep 4525631 = 6788447) B6788447
theorem B2543177 : Blo 1338988 2543177 := bstep (se 2 (by rfl) ⟨953691, by rfl⟩ : syracuseStep 2543177 = 1907383) B1907383
theorem B2010731 : Blo 1338988 2010731 := bstep (se 1 (by rfl) ⟨1508048, by rfl⟩ : syracuseStep 2010731 = 3016097) B3016097
theorem B3812989 : Blo 1338988 3812989 := bstep (se 3 (by rfl) ⟨714935, by rfl⟩ : syracuseStep 3812989 = 1429871) B1429871
theorem B2010857 : Blo 1338988 2010857 := bstep (se 2 (by rfl) ⟨754071, by rfl⟩ : syracuseStep 2010857 = 1508143) B1508143
theorem B1339207 : Blo 1338988 1339207 := bstep (se 1 (by rfl) ⟨1004405, by rfl⟩ : syracuseStep 1339207 = 2008811) B2008811
theorem B2011001 : Blo 1338988 2011001 := bstep (se 2 (by rfl) ⟨754125, by rfl⟩ : syracuseStep 2011001 = 1508251) B1508251
theorem B3813263 : Blo 1338988 3813263 := bstep (se 1 (by rfl) ⟨2859947, by rfl⟩ : syracuseStep 3813263 = 5719895) B5719895
theorem B1339359 : Blo 1338988 1339359 := bstep (se 1 (by rfl) ⟨1004519, by rfl⟩ : syracuseStep 1339359 = 2009039) B2009039
theorem B2011103 : Blo 1338988 2011103 := bstep (se 1 (by rfl) ⟨1508327, by rfl⟩ : syracuseStep 2011103 = 3016655) B3016655
theorem B5091457 : Blo 1338988 5091457 := bstep (se 2 (by rfl) ⟨1909296, by rfl⟩ : syracuseStep 5091457 = 3818593) B3818593
theorem B16306393 : Blo 1338988 16306393 := bstep (se 2 (by rfl) ⟨6114897, by rfl⟩ : syracuseStep 16306393 = 12229795) B12229795
theorem B2011355 : Blo 1338988 2011355 := bstep (se 1 (by rfl) ⟨1508516, by rfl⟩ : syracuseStep 2011355 = 3017033) B3017033
theorem B1339623 : Blo 1338988 1339623 := bstep (se 1 (by rfl) ⟨1004717, by rfl⟩ : syracuseStep 1339623 = 2009435) B2009435
theorem B2011367 : Blo 1338988 2011367 := bstep (se 1 (by rfl) ⟨1508525, by rfl⟩ : syracuseStep 2011367 = 3017051) B3017051
theorem B4829507 : Blo 1338988 4829507 := bstep (se 1 (by rfl) ⟨3622130, by rfl⟩ : syracuseStep 4829507 = 7244261) B7244261
theorem B1339775 : Blo 1338988 1339775 := bstep (se 1 (by rfl) ⟨1004831, by rfl⟩ : syracuseStep 1339775 = 2009663) B2009663
theorem B1339855 : Blo 1338988 1339855 := bstep (se 1 (by rfl) ⟨1004891, by rfl⟩ : syracuseStep 1339855 = 2009783) B2009783
theorem B7631333 : Blo 1338988 7631333 := bstep (se 4 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 7631333 = 1430875) B1430875
theorem B66130499 : Blo 1338988 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B1340007 : Blo 1338988 1340007 := bstep (se 1 (by rfl) ⟨1005005, by rfl⟩ : syracuseStep 1340007 = 2010011) B2010011
theorem B1340271 : Blo 1338988 1340271 := bstep (se 1 (by rfl) ⟨1005203, by rfl⟩ : syracuseStep 1340271 = 2010407) B2010407
theorem B12882833 : Blo 1338988 12882833 := bstep (se 2 (by rfl) ⟨4831062, by rfl⟩ : syracuseStep 12882833 = 9662125) B9662125
theorem B1340327 : Blo 1338988 1340327 := bstep (se 1 (by rfl) ⟨1005245, by rfl⟩ : syracuseStep 1340327 = 2010491) B2010491
theorem B19313639 : Blo 1338988 19313639 := bstep (se 1 (by rfl) ⟨14485229, by rfl⟩ : syracuseStep 19313639 = 28970459) B28970459
theorem B2544635 : Blo 1338988 2544635 := bstep (se 1 (by rfl) ⟨1908476, by rfl⟩ : syracuseStep 2544635 = 3816953) B3816953
theorem B1340411 : Blo 1338988 1340411 := bstep (se 1 (by rfl) ⟨1005308, by rfl⟩ : syracuseStep 1340411 = 2010617) B2010617
theorem B1340479 : Blo 1338988 1340479 := bstep (se 1 (by rfl) ⟨1005359, by rfl⟩ : syracuseStep 1340479 = 2010719) B2010719
theorem B5723243 : Blo 1338988 5723243 := bstep (se 1 (by rfl) ⟨4292432, by rfl⟩ : syracuseStep 5723243 = 8584865) B8584865
theorem B5723311 : Blo 1338988 5723311 := bstep (se 1 (by rfl) ⟨4292483, by rfl⟩ : syracuseStep 5723311 = 8584967) B8584967
theorem B19584175 : Blo 1338988 19584175 := bstep (se 1 (by rfl) ⟨14688131, by rfl⟩ : syracuseStep 19584175 = 29376263) B29376263
theorem B1340623 : Blo 1338988 1340623 := bstep (se 1 (by rfl) ⟨1005467, by rfl⟩ : syracuseStep 1340623 = 2010935) B2010935
theorem B4289755 : Blo 1338988 4289755 := bstep (se 1 (by rfl) ⟨3217316, by rfl⟩ : syracuseStep 4289755 = 6434633) B6434633
theorem B3921115 : Blo 1338988 3921115 := bstep (se 1 (by rfl) ⟨2940836, by rfl⟩ : syracuseStep 3921115 = 5881673) B5881673
theorem B4076819 : Blo 1338988 4076819 := bstep (se 1 (by rfl) ⟨3057614, by rfl⟩ : syracuseStep 4076819 = 6115229) B6115229
theorem B4519259 : Blo 1338988 4519259 := bstep (se 1 (by rfl) ⟨3389444, by rfl⟩ : syracuseStep 4519259 = 6778889) B6778889
theorem B1340827 : Blo 1338988 1340827 := bstep (se 1 (by rfl) ⟨1005620, by rfl⟩ : syracuseStep 1340827 = 2011241) B2011241
theorem B4519367 : Blo 1338988 4519367 := bstep (se 1 (by rfl) ⟨3389525, by rfl⟩ : syracuseStep 4519367 = 6779051) B6779051
theorem B9663943 : Blo 1338988 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B2545121 : Blo 1338988 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B11441837 : Blo 1338988 11441837 := bstep (se 3 (by rfl) ⟨2145344, by rfl⟩ : syracuseStep 11441837 = 4290689) B4290689
theorem B8582867 : Blo 1338988 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B4519691 : Blo 1338988 4519691 := bstep (se 1 (by rfl) ⟨3389768, by rfl⟩ : syracuseStep 4519691 = 6779537) B6779537
theorem B195688385 : Blo 1338988 195688385 := bstep (se 2 (by rfl) ⟨73383144, by rfl⟩ : syracuseStep 195688385 = 146766289) B146766289
theorem B4519961 : Blo 1338988 4519961 := bstep (se 2 (by rfl) ⟨1694985, by rfl⟩ : syracuseStep 4519961 = 3389971) B3389971
theorem B2545759 : Blo 1338988 2545759 := bstep (se 1 (by rfl) ⟨1909319, by rfl⟩ : syracuseStep 2545759 = 3818639) B3818639
theorem B37197953 : Blo 1338988 37197953 := bstep (se 2 (by rfl) ⟨13949232, by rfl⟩ : syracuseStep 37197953 = 27898465) B27898465
theorem B2414855 : Blo 1338988 2414855 := bstep (se 1 (by rfl) ⟨1811141, by rfl⟩ : syracuseStep 2414855 = 3622283) B3622283
theorem B4897199 : Blo 1338988 4897199 := bstep (se 1 (by rfl) ⟨3672899, by rfl⟩ : syracuseStep 4897199 = 7345799) B7345799
theorem B33028529 : Blo 1338988 33028529 := bstep (se 2 (by rfl) ⟨12385698, by rfl⟩ : syracuseStep 33028529 = 24771397) B24771397
theorem B17160659 : Blo 1338988 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B2259643 : Blo 1338988 2259643 := bstep (se 1 (by rfl) ⟨1694732, by rfl⟩ : syracuseStep 2259643 = 3389465) B3389465
theorem B8821537 : Blo 1338988 8821537 := bstep (se 2 (by rfl) ⟨3308076, by rfl⟩ : syracuseStep 8821537 = 6616153) B6616153
theorem B4643675 : Blo 1338988 4643675 := bstep (se 1 (by rfl) ⟨3482756, by rfl⟩ : syracuseStep 4643675 = 6965513) B6965513
theorem B5725019 : Blo 1338988 5725019 := bstep (se 1 (by rfl) ⟨4293764, by rfl⟩ : syracuseStep 5725019 = 8587529) B8587529
theorem B5086111 : Blo 1338988 5086111 := bstep (se 1 (by rfl) ⟨3814583, by rfl⟩ : syracuseStep 5086111 = 7629167) B7629167
theorem B17169317 : Blo 1338988 17169317 := bstep (se 4 (by rfl) ⟨1609623, by rfl⟩ : syracuseStep 17169317 = 3219247) B3219247
theorem B2259947 : Blo 1338988 2259947 := bstep (se 1 (by rfl) ⟨1694960, by rfl⟩ : syracuseStep 2259947 = 3389921) B3389921
theorem B1907759 : Blo 1338988 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B3013703 : Blo 1338988 3013703 := bstep (se 1 (by rfl) ⟨2260277, by rfl⟩ : syracuseStep 3013703 = 4520555) B4520555
theorem B4521311 : Blo 1338988 4521311 := bstep (se 1 (by rfl) ⟨3390983, by rfl⟩ : syracuseStep 4521311 = 6781967) B6781967
theorem B3620207 : Blo 1338988 3620207 := bstep (se 1 (by rfl) ⟨2715155, by rfl⟩ : syracuseStep 3620207 = 5430311) B5430311
theorem B3014099 : Blo 1338988 3014099 := bstep (se 1 (by rfl) ⟨2260574, by rfl⟩ : syracuseStep 3014099 = 4521149) B4521149
theorem B3391055 : Blo 1338988 3391055 := bstep (se 1 (by rfl) ⟨2543291, by rfl⟩ : syracuseStep 3391055 = 5086583) B5086583
theorem B4349531 : Blo 1338988 4349531 := bstep (se 1 (by rfl) ⟨3262148, by rfl⟩ : syracuseStep 4349531 = 6524297) B6524297
theorem B2145935 : Blo 1338988 2145935 := bstep (se 1 (by rfl) ⟨1609451, by rfl⟩ : syracuseStep 2145935 = 3218903) B3218903
theorem B35266225 : Blo 1338988 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B3014369 : Blo 1338988 3014369 := bstep (se 2 (by rfl) ⟨1130388, by rfl⟩ : syracuseStep 3014369 = 2260777) B2260777
theorem B2899783 : Blo 1338988 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B3866491 : Blo 1338988 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B4521851 : Blo 1338988 4521851 := bstep (se 1 (by rfl) ⟨3391388, by rfl⟩ : syracuseStep 4521851 = 6782777) B6782777
theorem B5087357 : Blo 1338988 5087357 := bstep (se 3 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 5087357 = 1907759) B1907759
theorem B3219671 : Blo 1338988 3219671 := bstep (se 1 (by rfl) ⟨2414753, by rfl⟩ : syracuseStep 3219671 = 4829507) B4829507
theorem B3014891 : Blo 1338988 3014891 := bstep (se 1 (by rfl) ⟨2261168, by rfl⟩ : syracuseStep 3014891 = 4522337) B4522337
theorem B21741857 : Blo 1338988 21741857 := bstep (se 2 (by rfl) ⟨8153196, by rfl⟩ : syracuseStep 21741857 = 16306393) B16306393
theorem B5087555 : Blo 1338988 5087555 := bstep (se 1 (by rfl) ⟨3815666, by rfl⟩ : syracuseStep 5087555 = 7631333) B7631333
theorem B10174895 : Blo 1338988 10174895 := bstep (se 1 (by rfl) ⟨7631171, by rfl⟩ : syracuseStep 10174895 = 15262343) B15262343
theorem B104366515 : Blo 1338988 104366515 := bstep (se 1 (by rfl) ⟨78274886, by rfl⟩ : syracuseStep 104366515 = 156549773) B156549773
theorem B6783425 : Blo 1338988 6783425 := bstep (se 2 (by rfl) ⟨2543784, by rfl⟩ : syracuseStep 6783425 = 5087569) B5087569
theorem B4522607 : Blo 1338988 4522607 := bstep (se 1 (by rfl) ⟨3391955, by rfl⟩ : syracuseStep 4522607 = 6783911) B6783911
theorem B8586071 : Blo 1338988 8586071 := bstep (se 1 (by rfl) ⟨6439553, by rfl⟩ : syracuseStep 8586071 = 12879107) B12879107
theorem B3015791 : Blo 1338988 3015791 := bstep (se 1 (by rfl) ⟨2261843, by rfl⟩ : syracuseStep 3015791 = 4523687) B4523687
theorem B2262127 : Blo 1338988 2262127 := bstep (se 1 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 2262127 = 3393191) B3393191
theorem B7627891 : Blo 1338988 7627891 := bstep (se 1 (by rfl) ⟨5720918, by rfl⟩ : syracuseStep 7627891 = 11441837) B11441837
theorem B1508575 : Blo 1338988 1508575 := bstep (se 1 (by rfl) ⟨1131431, by rfl⟩ : syracuseStep 1508575 = 2262863) B2262863
theorem B130458923 : Blo 1338988 130458923 := bstep (se 1 (by rfl) ⟨97844192, by rfl⟩ : syracuseStep 130458923 = 195688385) B195688385
theorem B5727617 : Blo 1338988 5727617 := bstep (se 2 (by rfl) ⟨2147856, by rfl⟩ : syracuseStep 5727617 = 4295713) B4295713
theorem B24798635 : Blo 1338988 24798635 := bstep (se 1 (by rfl) ⟨18598976, by rfl⟩ : syracuseStep 24798635 = 37197953) B37197953
theorem B3016187 : Blo 1338988 3016187 := bstep (se 1 (by rfl) ⟨2262140, by rfl⟩ : syracuseStep 3016187 = 4524281) B4524281
theorem B47048197 : Blo 1338988 47048197 := bstep (se 4 (by rfl) ⟨4410768, by rfl⟩ : syracuseStep 47048197 = 8821537) B8821537
theorem B48907799 : Blo 1338988 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B3016223 : Blo 1338988 3016223 := bstep (se 1 (by rfl) ⟨2262167, by rfl⟩ : syracuseStep 3016223 = 4524335) B4524335
theorem B2262559 : Blo 1338988 2262559 := bstep (se 1 (by rfl) ⟨1696919, by rfl⟩ : syracuseStep 2262559 = 3393839) B3393839
theorem B5719673 : Blo 1338988 5719673 := bstep (se 2 (by rfl) ⟨2144877, by rfl⟩ : syracuseStep 5719673 = 4289755) B4289755
theorem B5228153 : Blo 1338988 5228153 := bstep (se 2 (by rfl) ⟨1960557, by rfl⟩ : syracuseStep 5228153 = 3921115) B3921115
theorem B3016367 : Blo 1338988 3016367 := bstep (se 1 (by rfl) ⟨2262275, by rfl⟩ : syracuseStep 3016367 = 4524551) B4524551
theorem B11446211 : Blo 1338988 11446211 := bstep (se 1 (by rfl) ⟨8584658, by rfl⟩ : syracuseStep 11446211 = 17169317) B17169317
theorem B2009135 : Blo 1338988 2009135 := bstep (se 1 (by rfl) ⟨1506851, by rfl⟩ : syracuseStep 2009135 = 3013703) B3013703
theorem B3016799 : Blo 1338988 3016799 := bstep (se 1 (by rfl) ⟨2262599, by rfl⟩ : syracuseStep 3016799 = 4525199) B4525199
theorem B12880063 : Blo 1338988 12880063 := bstep (se 1 (by rfl) ⟨9660047, by rfl⟩ : syracuseStep 12880063 = 19320095) B19320095
theorem B2009399 : Blo 1338988 2009399 := bstep (se 1 (by rfl) ⟨1507049, by rfl⟩ : syracuseStep 2009399 = 3014099) B3014099
theorem B3017087 : Blo 1338988 3017087 := bstep (se 1 (by rfl) ⟨2262815, by rfl⟩ : syracuseStep 3017087 = 4525631) B4525631
theorem B2009579 : Blo 1338988 2009579 := bstep (se 1 (by rfl) ⟨1507184, by rfl⟩ : syracuseStep 2009579 = 3014369) B3014369
theorem B5155321 : Blo 1338988 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B2542175 : Blo 1338988 2542175 := bstep (se 1 (by rfl) ⟨1906631, by rfl⟩ : syracuseStep 2542175 = 3813263) B3813263
theorem B6785693 : Blo 1338988 6785693 := bstep (se 3 (by rfl) ⟨1272317, by rfl⟩ : syracuseStep 6785693 = 2544635) B2544635
theorem B3394345 : Blo 1338988 3394345 := bstep (se 2 (by rfl) ⟨1272879, by rfl⟩ : syracuseStep 3394345 = 2545759) B2545759
theorem B2010281 : Blo 1338988 2010281 := bstep (se 2 (by rfl) ⟨753855, by rfl⟩ : syracuseStep 2010281 = 1507711) B1507711
theorem B8588555 : Blo 1338988 8588555 := bstep (se 1 (by rfl) ⟨6441416, by rfl⟩ : syracuseStep 8588555 = 12882833) B12882833
theorem B2862391 : Blo 1338988 2862391 := bstep (se 1 (by rfl) ⟨2146793, by rfl⟩ : syracuseStep 2862391 = 4293587) B4293587
theorem B48885191 : Blo 1338988 48885191 := bstep (se 1 (by rfl) ⟨36663893, by rfl⟩ : syracuseStep 48885191 = 73327787) B73327787
theorem B2010695 : Blo 1338988 2010695 := bstep (se 1 (by rfl) ⟨1508021, by rfl⟩ : syracuseStep 2010695 = 3016043) B3016043
theorem B1339131 : Blo 1338988 1339131 := bstep (se 1 (by rfl) ⟨1004348, by rfl⟩ : syracuseStep 1339131 = 2008697) B2008697
theorem B2010875 : Blo 1338988 2010875 := bstep (se 1 (by rfl) ⟨1508156, by rfl⟩ : syracuseStep 2010875 = 3016313) B3016313
theorem B5721911 : Blo 1338988 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B11448125 : Blo 1338988 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B1339199 : Blo 1338988 1339199 := bstep (se 1 (by rfl) ⟨1004399, by rfl⟩ : syracuseStep 1339199 = 2008799) B2008799
theorem B1339263 : Blo 1338988 1339263 := bstep (se 1 (by rfl) ⟨1004447, by rfl⟩ : syracuseStep 1339263 = 2008895) B2008895
theorem B6786989 : Blo 1338988 6786989 := bstep (se 3 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 6786989 = 2545121) B2545121
theorem B1339375 : Blo 1338988 1339375 := bstep (se 1 (by rfl) ⟨1004531, by rfl⟩ : syracuseStep 1339375 = 2009063) B2009063
theorem B1339387 : Blo 1338988 1339387 := bstep (se 1 (by rfl) ⟨1004540, by rfl⟩ : syracuseStep 1339387 = 2009081) B2009081
theorem B1339455 : Blo 1338988 1339455 := bstep (se 1 (by rfl) ⟨1004591, by rfl⟩ : syracuseStep 1339455 = 2009183) B2009183
theorem B1339495 : Blo 1338988 1339495 := bstep (se 1 (by rfl) ⟨1004621, by rfl⟩ : syracuseStep 1339495 = 2009243) B2009243
theorem B1339519 : Blo 1338988 1339519 := bstep (se 1 (by rfl) ⟨1004639, by rfl⟩ : syracuseStep 1339519 = 2009279) B2009279
theorem B1339547 : Blo 1338988 1339547 := bstep (se 1 (by rfl) ⟨1004660, by rfl⟩ : syracuseStep 1339547 = 2009321) B2009321
theorem B1609903 : Blo 1338988 1609903 := bstep (se 1 (by rfl) ⟨1207427, by rfl⟩ : syracuseStep 1609903 = 2414855) B2414855
theorem B7631081 : Blo 1338988 7631081 := bstep (se 2 (by rfl) ⟨2861655, by rfl⟩ : syracuseStep 7631081 = 5723311) B5723311
theorem B26112233 : Blo 1338988 26112233 := bstep (se 2 (by rfl) ⟨9792087, by rfl⟩ : syracuseStep 26112233 = 19584175) B19584175
theorem B3264799 : Blo 1338988 3264799 := bstep (se 1 (by rfl) ⟨2448599, by rfl⟩ : syracuseStep 3264799 = 4897199) B4897199
theorem B11440439 : Blo 1338988 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B1339751 : Blo 1338988 1339751 := bstep (se 1 (by rfl) ⟨1004813, by rfl⟩ : syracuseStep 1339751 = 2009627) B2009627
theorem B1339803 : Blo 1338988 1339803 := bstep (se 1 (by rfl) ⟨1004852, by rfl⟩ : syracuseStep 1339803 = 2009705) B2009705
theorem B5435855 : Blo 1338988 5435855 := bstep (se 1 (by rfl) ⟨4076891, by rfl⟩ : syracuseStep 5435855 = 8153783) B8153783
theorem B69571025 : Blo 1338988 69571025 := bstep (se 2 (by rfl) ⟨26089134, by rfl⟩ : syracuseStep 69571025 = 52178269) B52178269
theorem B10859123 : Blo 1338988 10859123 := bstep (se 1 (by rfl) ⟨8144342, by rfl⟩ : syracuseStep 10859123 = 16288685) B16288685
theorem B32608889 : Blo 1338988 32608889 := bstep (se 2 (by rfl) ⟨12228333, by rfl⟩ : syracuseStep 32608889 = 24456667) B24456667
theorem B1340155 : Blo 1338988 1340155 := bstep (se 1 (by rfl) ⟨1005116, by rfl⟩ : syracuseStep 1340155 = 2010233) B2010233
theorem B1340223 : Blo 1338988 1340223 := bstep (se 1 (by rfl) ⟨1005167, by rfl⟩ : syracuseStep 1340223 = 2010335) B2010335
theorem B5083985 : Blo 1338988 5083985 := bstep (se 2 (by rfl) ⟨1906494, by rfl⟩ : syracuseStep 5083985 = 3812989) B3812989
theorem B1340251 : Blo 1338988 1340251 := bstep (se 1 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 1340251 = 2010377) B2010377
theorem B15266717 : Blo 1338988 15266717 := bstep (se 3 (by rfl) ⟨2862509, by rfl⟩ : syracuseStep 15266717 = 5725019) B5725019
theorem B2413471 : Blo 1338988 2413471 := bstep (se 1 (by rfl) ⟨1810103, by rfl⟩ : syracuseStep 2413471 = 3620207) B3620207
theorem B1340319 : Blo 1338988 1340319 := bstep (se 1 (by rfl) ⟨1005239, by rfl⟩ : syracuseStep 1340319 = 2010479) B2010479
theorem B1340399 : Blo 1338988 1340399 := bstep (se 1 (by rfl) ⟨1005299, by rfl⟩ : syracuseStep 1340399 = 2010599) B2010599
theorem B6435881 : Blo 1338988 6435881 := bstep (se 2 (by rfl) ⟨2413455, by rfl⟩ : syracuseStep 6435881 = 4826911) B4826911
theorem B1340487 : Blo 1338988 1340487 := bstep (se 1 (by rfl) ⟨1005365, by rfl⟩ : syracuseStep 1340487 = 2010731) B2010731
theorem B1430623 : Blo 1338988 1430623 := bstep (se 1 (by rfl) ⟨1072967, by rfl⟩ : syracuseStep 1430623 = 2145935) B2145935
theorem B1340571 : Blo 1338988 1340571 := bstep (se 1 (by rfl) ⟨1005428, by rfl⟩ : syracuseStep 1340571 = 2010857) B2010857
theorem B1340667 : Blo 1338988 1340667 := bstep (se 1 (by rfl) ⟨1005500, by rfl⟩ : syracuseStep 1340667 = 2011001) B2011001
theorem B1340735 : Blo 1338988 1340735 := bstep (se 1 (by rfl) ⟨1005551, by rfl⟩ : syracuseStep 1340735 = 2011103) B2011103
theorem B1340903 : Blo 1338988 1340903 := bstep (se 1 (by rfl) ⟨1005677, by rfl⟩ : syracuseStep 1340903 = 2011355) B2011355
theorem B1340911 : Blo 1338988 1340911 := bstep (se 1 (by rfl) ⟨1005683, by rfl⟩ : syracuseStep 1340911 = 2011367) B2011367
theorem B6788609 : Blo 1338988 6788609 := bstep (se 2 (by rfl) ⟨2545728, by rfl⟩ : syracuseStep 6788609 = 5091457) B5091457
theorem B2545273 : Blo 1338988 2545273 := bstep (se 2 (by rfl) ⟨954477, by rfl⟩ : syracuseStep 2545273 = 1908955) B1908955
theorem B2545319 : Blo 1338988 2545319 := bstep (se 1 (by rfl) ⟨1908989, by rfl⟩ : syracuseStep 2545319 = 3817979) B3817979
theorem B44086999 : Blo 1338988 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B12875759 : Blo 1338988 12875759 := bstep (se 1 (by rfl) ⟨9656819, by rfl⟩ : syracuseStep 12875759 = 19313639) B19313639
theorem B5724199 : Blo 1338988 5724199 := bstep (se 1 (by rfl) ⟨4293149, by rfl⟩ : syracuseStep 5724199 = 8586299) B8586299
theorem B10172465 : Blo 1338988 10172465 := bstep (se 2 (by rfl) ⟨3814674, by rfl⟩ : syracuseStep 10172465 = 7629349) B7629349
theorem B3815495 : Blo 1338988 3815495 := bstep (se 1 (by rfl) ⟨2861621, by rfl⟩ : syracuseStep 3815495 = 5723243) B5723243
theorem B2717879 : Blo 1338988 2717879 := bstep (se 1 (by rfl) ⟨2038409, by rfl⟩ : syracuseStep 2717879 = 4076819) B4076819
theorem B6199511 : Blo 1338988 6199511 := bstep (se 1 (by rfl) ⟨4649633, by rfl⟩ : syracuseStep 6199511 = 9299267) B9299267
theorem B3012839 : Blo 1338988 3012839 := bstep (se 1 (by rfl) ⟨2259629, by rfl⟩ : syracuseStep 3012839 = 4519259) B4519259
theorem B3012857 : Blo 1338988 3012857 := bstep (se 2 (by rfl) ⟨1129821, by rfl⟩ : syracuseStep 3012857 = 2259643) B2259643
theorem B3012911 : Blo 1338988 3012911 := bstep (se 1 (by rfl) ⟨2259683, by rfl⟩ : syracuseStep 3012911 = 4519367) B4519367
theorem B3013127 : Blo 1338988 3013127 := bstep (se 1 (by rfl) ⟨2259845, by rfl⟩ : syracuseStep 3013127 = 4519691) B4519691
theorem B6781481 : Blo 1338988 6781481 := bstep (se 2 (by rfl) ⟨2543055, by rfl⟩ : syracuseStep 6781481 = 5086111) B5086111
theorem B3013307 : Blo 1338988 3013307 := bstep (se 1 (by rfl) ⟨2259980, by rfl⟩ : syracuseStep 3013307 = 4519961) B4519961
theorem B6781805 : Blo 1338988 6781805 := bstep (se 3 (by rfl) ⟨1271588, by rfl⟩ : syracuseStep 6781805 = 2543177) B2543177
theorem B3218287 : Blo 1338988 3218287 := bstep (se 1 (by rfl) ⟨2413715, by rfl⟩ : syracuseStep 3218287 = 4827431) B4827431
theorem B3390569 : Blo 1338988 3390569 := bstep (se 2 (by rfl) ⟨1271463, by rfl⟩ : syracuseStep 3390569 = 2542927) B2542927
theorem B352304309 : Blo 1338988 352304309 := bstep (se 5 (by rfl) ⟨16514264, by rfl⟩ : syracuseStep 352304309 = 33028529) B33028529
theorem B5086415 : Blo 1338988 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B3095783 : Blo 1338988 3095783 := bstep (se 1 (by rfl) ⟨2321837, by rfl⟩ : syracuseStep 3095783 = 4643675) B4643675
theorem B12885257 : Blo 1338988 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B1506631 : Blo 1338988 1506631 := bstep (se 1 (by rfl) ⟨1129973, by rfl⟩ : syracuseStep 1506631 = 2259947) B2259947
theorem B8150381 : Blo 1338988 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B6970835 : Blo 1338988 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B5725687 : Blo 1338988 5725687 := bstep (se 1 (by rfl) ⟨4294265, by rfl⟩ : syracuseStep 5725687 = 8588531) B8588531
theorem B3014207 : Blo 1338988 3014207 := bstep (se 1 (by rfl) ⟨2260655, by rfl⟩ : syracuseStep 3014207 = 4521311) B4521311
theorem B47021633 : Blo 1338988 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B2260703 : Blo 1338988 2260703 := bstep (se 1 (by rfl) ⟨1695527, by rfl⟩ : syracuseStep 2260703 = 3391055) B3391055
theorem B2899687 : Blo 1338988 2899687 := bstep (se 1 (by rfl) ⟨2174765, by rfl⟩ : syracuseStep 2899687 = 4349531) B4349531
theorem B3866377 : Blo 1338988 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B3014567 : Blo 1338988 3014567 := bstep (se 1 (by rfl) ⟨2260925, by rfl⟩ : syracuseStep 3014567 = 4521851) B4521851
theorem B3391571 : Blo 1338988 3391571 := bstep (se 1 (by rfl) ⟨2543678, by rfl⟩ : syracuseStep 3391571 = 5087357) B5087357
theorem B2146447 : Blo 1338988 2146447 := bstep (se 1 (by rfl) ⟨1609835, by rfl⟩ : syracuseStep 2146447 = 3219671) B3219671
theorem B5087387 : Blo 1338988 5087387 := bstep (se 1 (by rfl) ⟨3815540, by rfl⟩ : syracuseStep 5087387 = 7631081) B7631081
theorem B17408155 : Blo 1338988 17408155 := bstep (se 1 (by rfl) ⟨13056116, by rfl⟩ : syracuseStep 17408155 = 26112233) B26112233
theorem B7626959 : Blo 1338988 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B3391703 : Blo 1338988 3391703 := bstep (se 1 (by rfl) ⟨2543777, by rfl⟩ : syracuseStep 3391703 = 5087555) B5087555
theorem B2146537 : Blo 1338988 2146537 := bstep (se 2 (by rfl) ⟨804951, by rfl⟩ : syracuseStep 2146537 = 1609903) B1609903
theorem B6783263 : Blo 1338988 6783263 := bstep (se 1 (by rfl) ⟨5087447, by rfl⟩ : syracuseStep 6783263 = 10174895) B10174895
theorem B4522283 : Blo 1338988 4522283 := bstep (se 1 (by rfl) ⟨3391712, by rfl⟩ : syracuseStep 4522283 = 6783425) B6783425
theorem B3015071 : Blo 1338988 3015071 := bstep (se 1 (by rfl) ⟨2261303, by rfl⟩ : syracuseStep 3015071 = 4522607) B4522607
theorem B16532029 : Blo 1338988 16532029 := bstep (se 3 (by rfl) ⟨3099755, by rfl⟩ : syracuseStep 16532029 = 6199511) B6199511
theorem B6873761 : Blo 1338988 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B3818411 : Blo 1338988 3818411 := bstep (se 1 (by rfl) ⟨2863808, by rfl⟩ : syracuseStep 3818411 = 5727617) B5727617
theorem B16532423 : Blo 1338988 16532423 := bstep (se 1 (by rfl) ⟨12399317, by rfl⟩ : syracuseStep 16532423 = 24798635) B24798635
theorem B32605199 : Blo 1338988 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B1696879 : Blo 1338988 1696879 := bstep (se 1 (by rfl) ⟨1272659, by rfl⟩ : syracuseStep 1696879 = 2545319) B2545319
theorem B3016169 : Blo 1338988 3016169 := bstep (se 2 (by rfl) ⟨1131063, by rfl⟩ : syracuseStep 3016169 = 2262127) B2262127
theorem B2008559 : Blo 1338988 2008559 := bstep (se 1 (by rfl) ⟨1506419, by rfl⟩ : syracuseStep 2008559 = 3012839) B3012839
theorem B2008571 : Blo 1338988 2008571 := bstep (se 1 (by rfl) ⟨1506428, by rfl⟩ : syracuseStep 2008571 = 3012857) B3012857
theorem B2008607 : Blo 1338988 2008607 := bstep (se 1 (by rfl) ⟨1506455, by rfl⟩ : syracuseStep 2008607 = 3012911) B3012911
theorem B2008751 : Blo 1338988 2008751 := bstep (se 1 (by rfl) ⟨1506563, by rfl⟩ : syracuseStep 2008751 = 3013127) B3013127
theorem B2008841 : Blo 1338988 2008841 := bstep (se 2 (by rfl) ⟨753315, by rfl⟩ : syracuseStep 2008841 = 1506631) B1506631
theorem B4523795 : Blo 1338988 4523795 := bstep (se 1 (by rfl) ⟨3392846, by rfl⟩ : syracuseStep 4523795 = 6785693) B6785693
theorem B2008871 : Blo 1338988 2008871 := bstep (se 1 (by rfl) ⟨1506653, by rfl⟩ : syracuseStep 2008871 = 3013307) B3013307
theorem B3016745 : Blo 1338988 3016745 := bstep (se 2 (by rfl) ⟨1131279, by rfl⟩ : syracuseStep 3016745 = 2262559) B2262559
theorem B3393697 : Blo 1338988 3393697 := bstep (se 2 (by rfl) ⟨1272636, by rfl⟩ : syracuseStep 3393697 = 2545273) B2545273
theorem B5433587 : Blo 1338988 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B32590127 : Blo 1338988 32590127 := bstep (se 1 (by rfl) ⟨24442595, by rfl⟩ : syracuseStep 32590127 = 48885191) B48885191
theorem B4647223 : Blo 1338988 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B5155169 : Blo 1338988 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B2009471 : Blo 1338988 2009471 := bstep (se 1 (by rfl) ⟨1507103, by rfl⟩ : syracuseStep 2009471 = 3014207) B3014207
theorem B2009711 : Blo 1338988 2009711 := bstep (se 1 (by rfl) ⟨1507283, by rfl⟩ : syracuseStep 2009711 = 3014567) B3014567
theorem B4524659 : Blo 1338988 4524659 := bstep (se 1 (by rfl) ⟨3393494, by rfl⟩ : syracuseStep 4524659 = 6786989) B6786989
theorem B2009927 : Blo 1338988 2009927 := bstep (se 1 (by rfl) ⟨1507445, by rfl⟩ : syracuseStep 2009927 = 3014891) B3014891
theorem B14494571 : Blo 1338988 14494571 := bstep (se 1 (by rfl) ⟨10870928, by rfl⟩ : syracuseStep 14494571 = 21741857) B21741857
theorem B17173417 : Blo 1338988 17173417 := bstep (se 2 (by rfl) ⟨6440031, by rfl⟩ : syracuseStep 17173417 = 12880063) B12880063
theorem B3623903 : Blo 1338988 3623903 := bstep (se 1 (by rfl) ⟨2717927, by rfl⟩ : syracuseStep 3623903 = 5435855) B5435855
theorem B4353065 : Blo 1338988 4353065 := bstep (se 2 (by rfl) ⟨1632399, by rfl⟩ : syracuseStep 4353065 = 3264799) B3264799
theorem B10177811 : Blo 1338988 10177811 := bstep (se 1 (by rfl) ⟨7633358, by rfl⟩ : syracuseStep 10177811 = 15266717) B15266717
theorem B2010527 : Blo 1338988 2010527 := bstep (se 1 (by rfl) ⟨1507895, by rfl⟩ : syracuseStep 2010527 = 3015791) B3015791
theorem B2010791 : Blo 1338988 2010791 := bstep (se 1 (by rfl) ⟨1508093, by rfl⟩ : syracuseStep 2010791 = 3016187) B3016187
theorem B4525739 : Blo 1338988 4525739 := bstep (se 1 (by rfl) ⟨3394304, by rfl⟩ : syracuseStep 4525739 = 6788609) B6788609
theorem B2010815 : Blo 1338988 2010815 := bstep (se 1 (by rfl) ⟨1508111, by rfl⟩ : syracuseStep 2010815 = 3016223) B3016223
theorem B4525793 : Blo 1338988 4525793 := bstep (se 2 (by rfl) ⟨1697172, by rfl⟩ : syracuseStep 4525793 = 3394345) B3394345
theorem B3813115 : Blo 1338988 3813115 := bstep (se 1 (by rfl) ⟨2859836, by rfl⟩ : syracuseStep 3813115 = 5719673) B5719673
theorem B3485435 : Blo 1338988 3485435 := bstep (se 1 (by rfl) ⟨2614076, by rfl⟩ : syracuseStep 3485435 = 5228153) B5228153
theorem B2010911 : Blo 1338988 2010911 := bstep (se 1 (by rfl) ⟨1508183, by rfl⟩ : syracuseStep 2010911 = 3016367) B3016367
theorem B7630807 : Blo 1338988 7630807 := bstep (se 1 (by rfl) ⟨5723105, by rfl⟩ : syracuseStep 7630807 = 11446211) B11446211
theorem B1339423 : Blo 1338988 1339423 := bstep (se 1 (by rfl) ⟨1004567, by rfl⟩ : syracuseStep 1339423 = 2009135) B2009135
theorem B2543663 : Blo 1338988 2543663 := bstep (se 1 (by rfl) ⟨1907747, by rfl⟩ : syracuseStep 2543663 = 3815495) B3815495
theorem B2011199 : Blo 1338988 2011199 := bstep (se 1 (by rfl) ⟨1508399, by rfl⟩ : syracuseStep 2011199 = 3016799) B3016799
theorem B10170521 : Blo 1338988 10170521 := bstep (se 2 (by rfl) ⟨3813945, by rfl⟩ : syracuseStep 10170521 = 7627891) B7627891
theorem B1339599 : Blo 1338988 1339599 := bstep (se 1 (by rfl) ⟨1004699, by rfl⟩ : syracuseStep 1339599 = 2009399) B2009399
theorem B2011391 : Blo 1338988 2011391 := bstep (se 1 (by rfl) ⟨1508543, by rfl⟩ : syracuseStep 2011391 = 3017087) B3017087
theorem B2011433 : Blo 1338988 2011433 := bstep (se 2 (by rfl) ⟨754287, by rfl⟩ : syracuseStep 2011433 = 1508575) B1508575
theorem B1339719 : Blo 1338988 1339719 := bstep (se 1 (by rfl) ⟨1004789, by rfl⟩ : syracuseStep 1339719 = 2009579) B2009579
theorem B62730929 : Blo 1338988 62730929 := bstep (se 2 (by rfl) ⟨23524098, by rfl⟩ : syracuseStep 62730929 = 47048197) B47048197
theorem B1340187 : Blo 1338988 1340187 := bstep (se 1 (by rfl) ⟨1005140, by rfl⟩ : syracuseStep 1340187 = 2010281) B2010281
theorem B234869539 : Blo 1338988 234869539 := bstep (se 1 (by rfl) ⟨176152154, by rfl⟩ : syracuseStep 234869539 = 352304309) B352304309
theorem B8590171 : Blo 1338988 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B58782665 : Blo 1338988 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B31347755 : Blo 1338988 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B1340463 : Blo 1338988 1340463 := bstep (se 1 (by rfl) ⟨1005347, by rfl⟩ : syracuseStep 1340463 = 2010695) B2010695
theorem B1340583 : Blo 1338988 1340583 := bstep (se 1 (by rfl) ⟨1005437, by rfl⟩ : syracuseStep 1340583 = 2010875) B2010875
theorem B3814607 : Blo 1338988 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B7632083 : Blo 1338988 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B7632265 : Blo 1338988 7632265 := bstep (se 2 (by rfl) ⟨2862099, by rfl⟩ : syracuseStep 7632265 = 5724199) B5724199
theorem B46380683 : Blo 1338988 46380683 := bstep (se 1 (by rfl) ⟨34785512, by rfl⟩ : syracuseStep 46380683 = 69571025) B69571025
theorem B7239415 : Blo 1338988 7239415 := bstep (se 1 (by rfl) ⟨5429561, by rfl⟩ : syracuseStep 7239415 = 10859123) B10859123
theorem B21739259 : Blo 1338988 21739259 := bstep (se 1 (by rfl) ⟨16304444, by rfl⟩ : syracuseStep 21739259 = 32608889) B32608889
theorem B7247677 : Blo 1338988 7247677 := bstep (se 3 (by rfl) ⟨1358939, by rfl⟩ : syracuseStep 7247677 = 2717879) B2717879
theorem B3389323 : Blo 1338988 3389323 := bstep (se 1 (by rfl) ⟨2541992, by rfl⟩ : syracuseStep 3389323 = 5083985) B5083985
theorem B5724047 : Blo 1338988 5724047 := bstep (se 1 (by rfl) ⟨4293035, by rfl⟩ : syracuseStep 5724047 = 8586071) B8586071
theorem B139155353 : Blo 1338988 139155353 := bstep (se 2 (by rfl) ⟨52183257, by rfl⟩ : syracuseStep 139155353 = 104366515) B104366515
theorem B4290587 : Blo 1338988 4290587 := bstep (se 1 (by rfl) ⟨3217940, by rfl⟩ : syracuseStep 4290587 = 6435881) B6435881
theorem B86972615 : Blo 1338988 86972615 := bstep (se 1 (by rfl) ⟨65229461, by rfl⟩ : syracuseStep 86972615 = 130458923) B130458923
theorem B4291049 : Blo 1338988 4291049 := bstep (se 2 (by rfl) ⟨1609143, by rfl⟩ : syracuseStep 4291049 = 3218287) B3218287
theorem B3217961 : Blo 1338988 3217961 := bstep (se 2 (by rfl) ⟨1206735, by rfl⟩ : syracuseStep 3217961 = 2413471) B2413471
theorem B8583839 : Blo 1338988 8583839 := bstep (se 1 (by rfl) ⟨6437879, by rfl⟩ : syracuseStep 8583839 = 12875759) B12875759
theorem B6781643 : Blo 1338988 6781643 := bstep (se 1 (by rfl) ⟨5086232, by rfl⟩ : syracuseStep 6781643 = 10172465) B10172465
theorem B1907497 : Blo 1338988 1907497 := bstep (se 2 (by rfl) ⟨715311, by rfl⟩ : syracuseStep 1907497 = 1430623) B1430623
theorem B4520987 : Blo 1338988 4520987 := bstep (se 1 (by rfl) ⟨3390740, by rfl⟩ : syracuseStep 4520987 = 6781481) B6781481
theorem B1694783 : Blo 1338988 1694783 := bstep (se 1 (by rfl) ⟨1271087, by rfl⟩ : syracuseStep 1694783 = 2542175) B2542175
theorem B3816521 : Blo 1338988 3816521 := bstep (se 2 (by rfl) ⟨1431195, by rfl⟩ : syracuseStep 3816521 = 2862391) B2862391
theorem B4521203 : Blo 1338988 4521203 := bstep (se 1 (by rfl) ⟨3390902, by rfl⟩ : syracuseStep 4521203 = 6781805) B6781805
theorem B7634249 : Blo 1338988 7634249 := bstep (se 2 (by rfl) ⟨2862843, by rfl⟩ : syracuseStep 7634249 = 5725687) B5725687
theorem B2260379 : Blo 1338988 2260379 := bstep (se 1 (by rfl) ⟨1695284, by rfl⟩ : syracuseStep 2260379 = 3390569) B3390569
theorem B3390943 : Blo 1338988 3390943 := bstep (se 1 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 3390943 = 5086415) B5086415
theorem B2063855 : Blo 1338988 2063855 := bstep (se 1 (by rfl) ⟨1547891, by rfl⟩ : syracuseStep 2063855 = 3095783) B3095783
theorem B5725703 : Blo 1338988 5725703 := bstep (se 1 (by rfl) ⟨4294277, by rfl⟩ : syracuseStep 5725703 = 8588555) B8588555
theorem B3866249 : Blo 1338988 3866249 := bstep (se 2 (by rfl) ⟨1449843, by rfl⟩ : syracuseStep 3866249 = 2899687) B2899687
theorem B1507135 : Blo 1338988 1507135 := bstep (se 1 (by rfl) ⟨1130351, by rfl⟩ : syracuseStep 1507135 = 2260703) B2260703
theorem B2261047 : Blo 1338988 2261047 := bstep (se 1 (by rfl) ⟨1695785, by rfl⟩ : syracuseStep 2261047 = 3391571) B3391571
theorem B3391591 : Blo 1338988 3391591 := bstep (se 1 (by rfl) ⟨2543693, by rfl⟩ : syracuseStep 3391591 = 5087387) B5087387
theorem B6783101 : Blo 1338988 6783101 := bstep (se 3 (by rfl) ⟨1271831, by rfl⟩ : syracuseStep 6783101 = 2543663) B2543663
theorem B2261135 : Blo 1338988 2261135 := bstep (se 1 (by rfl) ⟨1695851, by rfl⟩ : syracuseStep 2261135 = 3391703) B3391703
theorem B4522175 : Blo 1338988 4522175 := bstep (se 1 (by rfl) ⟨3391631, by rfl⟩ : syracuseStep 4522175 = 6783263) B6783263
theorem B3014855 : Blo 1338988 3014855 := bstep (se 1 (by rfl) ⟨2261141, by rfl⟩ : syracuseStep 3014855 = 4522283) B4522283
theorem B41820619 : Blo 1338988 41820619 := bstep (se 1 (by rfl) ⟨31365464, by rfl⟩ : syracuseStep 41820619 = 62730929) B62730929
theorem B20898503 : Blo 1338988 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B5088055 : Blo 1338988 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B13747117 : Blo 1338988 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B11453561 : Blo 1338988 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B14492839 : Blo 1338988 14492839 := bstep (se 1 (by rfl) ⟨10869629, by rfl⟩ : syracuseStep 14492839 = 21739259) B21739259
theorem B3015863 : Blo 1338988 3015863 := bstep (se 1 (by rfl) ⟨2261897, by rfl⟩ : syracuseStep 3015863 = 4523795) B4523795
theorem B22897889 : Blo 1338988 22897889 := bstep (se 2 (by rfl) ⟨8586708, by rfl⟩ : syracuseStep 22897889 = 17173417) B17173417
theorem B2860391 : Blo 1338988 2860391 := bstep (se 1 (by rfl) ⟨2145293, by rfl⟩ : syracuseStep 2860391 = 4290587) B4290587
theorem B2262505 : Blo 1338988 2262505 := bstep (se 2 (by rfl) ⟨848439, by rfl⟩ : syracuseStep 2262505 = 1696879) B1696879
theorem B3622391 : Blo 1338988 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B21726751 : Blo 1338988 21726751 := bstep (se 1 (by rfl) ⟨16295063, by rfl⟩ : syracuseStep 21726751 = 32590127) B32590127
theorem B2860699 : Blo 1338988 2860699 := bstep (se 1 (by rfl) ⟨2145524, by rfl⟩ : syracuseStep 2860699 = 4291049) B4291049
theorem B3016439 : Blo 1338988 3016439 := bstep (se 1 (by rfl) ⟨2262329, by rfl⟩ : syracuseStep 3016439 = 4524659) B4524659
theorem B10176353 : Blo 1338988 10176353 := bstep (se 2 (by rfl) ⟨3816132, by rfl⟩ : syracuseStep 10176353 = 7632265) B7632265
theorem B2902043 : Blo 1338988 2902043 := bstep (se 1 (by rfl) ⟨2176532, by rfl⟩ : syracuseStep 2902043 = 4353065) B4353065
theorem B6785207 : Blo 1338988 6785207 := bstep (se 1 (by rfl) ⟨5088905, by rfl⟩ : syracuseStep 6785207 = 10177811) B10177811
theorem B5089499 : Blo 1338988 5089499 := bstep (se 1 (by rfl) ⟨3817124, by rfl⟩ : syracuseStep 5089499 = 7634249) B7634249
theorem B9652553 : Blo 1338988 9652553 := bstep (se 2 (by rfl) ⟨3619707, by rfl⟩ : syracuseStep 9652553 = 7239415) B7239415
theorem B2009513 : Blo 1338988 2009513 := bstep (se 2 (by rfl) ⟨753567, by rfl⟩ : syracuseStep 2009513 = 1507135) B1507135
theorem B3017159 : Blo 1338988 3017159 := bstep (se 1 (by rfl) ⟨2262869, by rfl⟩ : syracuseStep 3017159 = 4525739) B4525739
theorem B3017195 : Blo 1338988 3017195 := bstep (se 1 (by rfl) ⟨2262896, by rfl⟩ : syracuseStep 3017195 = 4525793) B4525793
theorem B37177973 : Blo 1338988 37177973 := bstep (se 5 (by rfl) ⟨1742717, by rfl⟩ : syracuseStep 37177973 = 3485435) B3485435
theorem B2861929 : Blo 1338988 2861929 := bstep (se 2 (by rfl) ⟨1073223, by rfl⟩ : syracuseStep 2861929 = 2146447) B2146447
theorem B23210873 : Blo 1338988 23210873 := bstep (se 2 (by rfl) ⟨8704077, by rfl⟩ : syracuseStep 23210873 = 17408155) B17408155
theorem B4524929 : Blo 1338988 4524929 := bstep (se 2 (by rfl) ⟨1696848, by rfl⟩ : syracuseStep 4524929 = 3393697) B3393697
theorem B2010047 : Blo 1338988 2010047 := bstep (se 1 (by rfl) ⟨1507535, by rfl⟩ : syracuseStep 2010047 = 3015071) B3015071
theorem B2862049 : Blo 1338988 2862049 := bstep (se 2 (by rfl) ⟨1073268, by rfl⟩ : syracuseStep 2862049 = 2146537) B2146537
theorem B4582507 : Blo 1338988 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B11021615 : Blo 1338988 11021615 := bstep (se 1 (by rfl) ⟨8266211, by rfl⟩ : syracuseStep 11021615 = 16532423) B16532423
theorem B21736799 : Blo 1338988 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B2543071 : Blo 1338988 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B2010779 : Blo 1338988 2010779 := bstep (se 1 (by rfl) ⟨1508084, by rfl⟩ : syracuseStep 2010779 = 3016169) B3016169
theorem B1339039 : Blo 1338988 1339039 := bstep (se 1 (by rfl) ⟨1004279, by rfl⟩ : syracuseStep 1339039 = 2008559) B2008559
theorem B1339047 : Blo 1338988 1339047 := bstep (se 1 (by rfl) ⟨1004285, by rfl⟩ : syracuseStep 1339047 = 2008571) B2008571
theorem B1339071 : Blo 1338988 1339071 := bstep (se 1 (by rfl) ⟨1004303, by rfl⟩ : syracuseStep 1339071 = 2008607) B2008607
theorem B313159385 : Blo 1338988 313159385 := bstep (se 2 (by rfl) ⟨117434769, by rfl⟩ : syracuseStep 313159385 = 234869539) B234869539
theorem B2543329 : Blo 1338988 2543329 := bstep (se 2 (by rfl) ⟨953748, by rfl⟩ : syracuseStep 2543329 = 1907497) B1907497
theorem B1339167 : Blo 1338988 1339167 := bstep (se 1 (by rfl) ⟨1004375, by rfl⟩ : syracuseStep 1339167 = 2008751) B2008751
theorem B1339227 : Blo 1338988 1339227 := bstep (se 1 (by rfl) ⟨1004420, by rfl⟩ : syracuseStep 1339227 = 2008841) B2008841
theorem B1339247 : Blo 1338988 1339247 := bstep (se 1 (by rfl) ⟨1004435, by rfl⟩ : syracuseStep 1339247 = 2008871) B2008871
theorem B92770235 : Blo 1338988 92770235 := bstep (se 1 (by rfl) ⟨69577676, by rfl⟩ : syracuseStep 92770235 = 139155353) B139155353
theorem B2011163 : Blo 1338988 2011163 := bstep (se 1 (by rfl) ⟨1508372, by rfl⟩ : syracuseStep 2011163 = 3016745) B3016745
theorem B1339647 : Blo 1338988 1339647 := bstep (se 1 (by rfl) ⟨1004735, by rfl⟩ : syracuseStep 1339647 = 2009471) B2009471
theorem B24785189 : Blo 1338988 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B10309997 : Blo 1338988 10309997 := bstep (se 3 (by rfl) ⟨1933124, by rfl⟩ : syracuseStep 10309997 = 3866249) B3866249
theorem B1339807 : Blo 1338988 1339807 := bstep (se 1 (by rfl) ⟨1004855, by rfl⟩ : syracuseStep 1339807 = 2009711) B2009711
theorem B5722559 : Blo 1338988 5722559 := bstep (se 1 (by rfl) ⟨4291919, by rfl⟩ : syracuseStep 5722559 = 8583839) B8583839
theorem B1339951 : Blo 1338988 1339951 := bstep (se 1 (by rfl) ⟨1004963, by rfl⟩ : syracuseStep 1339951 = 2009927) B2009927
theorem B9663047 : Blo 1338988 9663047 := bstep (se 1 (by rfl) ⟨7247285, by rfl⟩ : syracuseStep 9663047 = 14494571) B14494571
theorem B2544347 : Blo 1338988 2544347 := bstep (se 1 (by rfl) ⟨1908260, by rfl⟩ : syracuseStep 2544347 = 3816521) B3816521
theorem B1340351 : Blo 1338988 1340351 := bstep (se 1 (by rfl) ⟨1005263, by rfl⟩ : syracuseStep 1340351 = 2010527) B2010527
theorem B5084153 : Blo 1338988 5084153 := bstep (se 2 (by rfl) ⟨1906557, by rfl⟩ : syracuseStep 5084153 = 3813115) B3813115
theorem B9663569 : Blo 1338988 9663569 := bstep (se 2 (by rfl) ⟨3623838, by rfl⟩ : syracuseStep 9663569 = 7247677) B7247677
theorem B1340527 : Blo 1338988 1340527 := bstep (se 1 (by rfl) ⟨1005395, by rfl⟩ : syracuseStep 1340527 = 2010791) B2010791
theorem B1340543 : Blo 1338988 1340543 := bstep (se 1 (by rfl) ⟨1005407, by rfl⟩ : syracuseStep 1340543 = 2010815) B2010815
theorem B4519097 : Blo 1338988 4519097 := bstep (se 2 (by rfl) ⟨1694661, by rfl⟩ : syracuseStep 4519097 = 3389323) B3389323
theorem B1340607 : Blo 1338988 1340607 := bstep (se 1 (by rfl) ⟨1005455, by rfl⟩ : syracuseStep 1340607 = 2010911) B2010911
theorem B1340799 : Blo 1338988 1340799 := bstep (se 1 (by rfl) ⟨1005599, by rfl⟩ : syracuseStep 1340799 = 2011199) B2011199
theorem B6780347 : Blo 1338988 6780347 := bstep (se 1 (by rfl) ⟨5085260, by rfl⟩ : syracuseStep 6780347 = 10170521) B10170521
theorem B5084639 : Blo 1338988 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B4519421 : Blo 1338988 4519421 := bstep (se 3 (by rfl) ⟨847391, by rfl⟩ : syracuseStep 4519421 = 1694783) B1694783
theorem B1340927 : Blo 1338988 1340927 := bstep (se 1 (by rfl) ⟨1005695, by rfl⟩ : syracuseStep 1340927 = 2011391) B2011391
theorem B1340955 : Blo 1338988 1340955 := bstep (se 1 (by rfl) ⟨1005716, by rfl⟩ : syracuseStep 1340955 = 2011433) B2011433
theorem B2545607 : Blo 1338988 2545607 := bstep (se 1 (by rfl) ⟨1909205, by rfl⟩ : syracuseStep 2545607 = 3818411) B3818411
theorem B39188443 : Blo 1338988 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B22042705 : Blo 1338988 22042705 := bstep (se 2 (by rfl) ⟨8266014, by rfl⟩ : syracuseStep 22042705 = 16532029) B16532029
theorem B3816031 : Blo 1338988 3816031 := bstep (se 1 (by rfl) ⟨2862023, by rfl⟩ : syracuseStep 3816031 = 5724047) B5724047
theorem B57981743 : Blo 1338988 57981743 := bstep (se 1 (by rfl) ⟨43486307, by rfl⟩ : syracuseStep 57981743 = 86972615) B86972615
theorem B2145307 : Blo 1338988 2145307 := bstep (se 1 (by rfl) ⟨1608980, by rfl⟩ : syracuseStep 2145307 = 3217961) B3217961
theorem B123681821 : Blo 1338988 123681821 := bstep (se 3 (by rfl) ⟨23190341, by rfl⟩ : syracuseStep 123681821 = 46380683) B46380683
theorem B4521095 : Blo 1338988 4521095 := bstep (se 1 (by rfl) ⟨3390821, by rfl⟩ : syracuseStep 4521095 = 6781643) B6781643
theorem B4521257 : Blo 1338988 4521257 := bstep (se 2 (by rfl) ⟨1695471, by rfl⟩ : syracuseStep 4521257 = 3390943) B3390943
theorem B2415935 : Blo 1338988 2415935 := bstep (se 1 (by rfl) ⟨1811951, by rfl⟩ : syracuseStep 2415935 = 3623903) B3623903
theorem B3013991 : Blo 1338988 3013991 := bstep (se 1 (by rfl) ⟨2260493, by rfl⟩ : syracuseStep 3013991 = 4520987) B4520987
theorem B3014135 : Blo 1338988 3014135 := bstep (se 1 (by rfl) ⟨2260601, by rfl⟩ : syracuseStep 3014135 = 4521203) B4521203
theorem B1506919 : Blo 1338988 1506919 := bstep (se 1 (by rfl) ⟨1130189, by rfl⟩ : syracuseStep 1506919 = 2260379) B2260379
theorem B1375903 : Blo 1338988 1375903 := bstep (se 1 (by rfl) ⟨1031927, by rfl⟩ : syracuseStep 1375903 = 2063855) B2063855
theorem B3817135 : Blo 1338988 3817135 := bstep (se 1 (by rfl) ⟨2862851, by rfl⟩ : syracuseStep 3817135 = 5725703) B5725703
theorem B10174409 : Blo 1338988 10174409 := bstep (se 2 (by rfl) ⟨3815403, by rfl⟩ : syracuseStep 10174409 = 7630807) B7630807
theorem B3014729 : Blo 1338988 3014729 := bstep (se 2 (by rfl) ⟨1130523, by rfl⟩ : syracuseStep 3014729 = 2261047) B2261047
theorem B329818189 : Blo 1338988 329818189 := bstep (se 3 (by rfl) ⟨61840910, by rfl⟩ : syracuseStep 329818189 = 123681821) B123681821
theorem B4522067 : Blo 1338988 4522067 := bstep (se 1 (by rfl) ⟨3391550, by rfl⟩ : syracuseStep 4522067 = 6783101) B6783101
theorem B1507423 : Blo 1338988 1507423 := bstep (se 1 (by rfl) ⟨1130567, by rfl⟩ : syracuseStep 1507423 = 2261135) B2261135
theorem B3014783 : Blo 1338988 3014783 := bstep (se 1 (by rfl) ⟨2261087, by rfl⟩ : syracuseStep 3014783 = 4522175) B4522175
theorem B4522121 : Blo 1338988 4522121 := bstep (se 2 (by rfl) ⟨1695795, by rfl⟩ : syracuseStep 4522121 = 3391591) B3391591
theorem B16523459 : Blo 1338988 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B6873331 : Blo 1338988 6873331 := bstep (se 1 (by rfl) ⟨5154998, by rfl⟩ : syracuseStep 6873331 = 10309997) B10309997
theorem B1696231 : Blo 1338988 1696231 := bstep (se 1 (by rfl) ⟨1272173, by rfl⟩ : syracuseStep 1696231 = 2544347) B2544347
theorem B7635707 : Blo 1338988 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B5088041 : Blo 1338988 5088041 := bstep (se 2 (by rfl) ⟨1908015, by rfl⟩ : syracuseStep 5088041 = 3816031) B3816031
theorem B7627709 : Blo 1338988 7627709 := bstep (se 3 (by rfl) ⟨1430195, by rfl⟩ : syracuseStep 7627709 = 2860391) B2860391
theorem B6784073 : Blo 1338988 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B6784235 : Blo 1338988 6784235 := bstep (se 1 (by rfl) ⟨5088176, by rfl⟩ : syracuseStep 6784235 = 10176353) B10176353
theorem B1934695 : Blo 1338988 1934695 := bstep (se 1 (by rfl) ⟨1451021, by rfl⟩ : syracuseStep 1934695 = 2902043) B2902043
theorem B2860409 : Blo 1338988 2860409 := bstep (se 2 (by rfl) ⟨1072653, by rfl⟩ : syracuseStep 2860409 = 2145307) B2145307
theorem B4523471 : Blo 1338988 4523471 := bstep (se 1 (by rfl) ⟨3392603, by rfl⟩ : syracuseStep 4523471 = 6785207) B6785207
theorem B3392999 : Blo 1338988 3392999 := bstep (se 1 (by rfl) ⟨2544749, by rfl⟩ : syracuseStep 3392999 = 5089499) B5089499
theorem B3016619 : Blo 1338988 3016619 := bstep (se 1 (by rfl) ⟨2262464, by rfl⟩ : syracuseStep 3016619 = 4524929) B4524929
theorem B3016673 : Blo 1338988 3016673 := bstep (se 2 (by rfl) ⟨1131252, by rfl⟩ : syracuseStep 3016673 = 2262505) B2262505
theorem B28969001 : Blo 1338988 28969001 := bstep (se 2 (by rfl) ⟨10863375, by rfl⟩ : syracuseStep 28969001 = 21726751) B21726751
theorem B2009225 : Blo 1338988 2009225 := bstep (se 2 (by rfl) ⟨753459, by rfl⟩ : syracuseStep 2009225 = 1506919) B1506919
theorem B5089513 : Blo 1338988 5089513 := bstep (se 2 (by rfl) ⟨1908567, by rfl⟩ : syracuseStep 5089513 = 3817135) B3817135
theorem B2009327 : Blo 1338988 2009327 := bstep (se 1 (by rfl) ⟨1506995, by rfl⟩ : syracuseStep 2009327 = 3013991) B3013991
theorem B2009423 : Blo 1338988 2009423 := bstep (se 1 (by rfl) ⟨1507067, by rfl⟩ : syracuseStep 2009423 = 3014135) B3014135
theorem B52251257 : Blo 1338988 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B2009903 : Blo 1338988 2009903 := bstep (se 1 (by rfl) ⟨1507427, by rfl⟩ : syracuseStep 2009903 = 3014855) B3014855
theorem B6442031 : Blo 1338988 6442031 := bstep (se 1 (by rfl) ⟨4831523, by rfl⟩ : syracuseStep 6442031 = 9663047) B9663047
theorem B6442379 : Blo 1338988 6442379 := bstep (se 1 (by rfl) ⟨4831784, by rfl⟩ : syracuseStep 6442379 = 9663569) B9663569
theorem B2010575 : Blo 1338988 2010575 := bstep (se 1 (by rfl) ⟨1507931, by rfl⟩ : syracuseStep 2010575 = 3015863) B3015863
theorem B15265259 : Blo 1338988 15265259 := bstep (se 1 (by rfl) ⟨11448944, by rfl⟩ : syracuseStep 15265259 = 22897889) B22897889
theorem B2010959 : Blo 1338988 2010959 := bstep (se 1 (by rfl) ⟨1508219, by rfl⟩ : syracuseStep 2010959 = 3016439) B3016439
theorem B18329489 : Blo 1338988 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B6435035 : Blo 1338988 6435035 := bstep (se 1 (by rfl) ⟨4826276, by rfl⟩ : syracuseStep 6435035 = 9652553) B9652553
theorem B1339675 : Blo 1338988 1339675 := bstep (se 1 (by rfl) ⟨1004756, by rfl⟩ : syracuseStep 1339675 = 2009513) B2009513
theorem B2011439 : Blo 1338988 2011439 := bstep (se 1 (by rfl) ⟨1508579, by rfl⟩ : syracuseStep 2011439 = 3017159) B3017159
theorem B2011463 : Blo 1338988 2011463 := bstep (se 1 (by rfl) ⟨1508597, by rfl⟩ : syracuseStep 2011463 = 3017195) B3017195
theorem B24785315 : Blo 1338988 24785315 := bstep (se 1 (by rfl) ⟨18588986, by rfl⟩ : syracuseStep 24785315 = 37177973) B37177973
theorem B38654495 : Blo 1338988 38654495 := bstep (se 1 (by rfl) ⟨28990871, by rfl⟩ : syracuseStep 38654495 = 57981743) B57981743
theorem B1340031 : Blo 1338988 1340031 := bstep (se 1 (by rfl) ⟨1005023, by rfl⟩ : syracuseStep 1340031 = 2010047) B2010047
theorem B3814265 : Blo 1338988 3814265 := bstep (se 2 (by rfl) ⟨1430349, by rfl⟩ : syracuseStep 3814265 = 2860699) B2860699
theorem B1610623 : Blo 1338988 1610623 := bstep (se 1 (by rfl) ⟨1207967, by rfl⟩ : syracuseStep 1610623 = 2415935) B2415935
theorem B1340519 : Blo 1338988 1340519 := bstep (se 1 (by rfl) ⟨1005389, by rfl⟩ : syracuseStep 1340519 = 2010779) B2010779
theorem B6788285 : Blo 1338988 6788285 := bstep (se 3 (by rfl) ⟨1272803, by rfl⟩ : syracuseStep 6788285 = 2545607) B2545607
theorem B61846823 : Blo 1338988 61846823 := bstep (se 1 (by rfl) ⟨46385117, by rfl⟩ : syracuseStep 61846823 = 92770235) B92770235
theorem B1340775 : Blo 1338988 1340775 := bstep (se 1 (by rfl) ⟨1005581, by rfl⟩ : syracuseStep 1340775 = 2011163) B2011163
theorem B29390273 : Blo 1338988 29390273 := bstep (se 2 (by rfl) ⟨11021352, by rfl⟩ : syracuseStep 29390273 = 22042705) B22042705
theorem B3815039 : Blo 1338988 3815039 := bstep (se 1 (by rfl) ⟨2861279, by rfl⟩ : syracuseStep 3815039 = 5722559) B5722559
theorem B13932335 : Blo 1338988 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B55760825 : Blo 1338988 55760825 := bstep (se 2 (by rfl) ⟨20910309, by rfl⟩ : syracuseStep 55760825 = 41820619) B41820619
theorem B3389435 : Blo 1338988 3389435 := bstep (se 1 (by rfl) ⟨2542076, by rfl⟩ : syracuseStep 3389435 = 5084153) B5084153
theorem B3012731 : Blo 1338988 3012731 := bstep (se 1 (by rfl) ⟨2259548, by rfl⟩ : syracuseStep 3012731 = 4519097) B4519097
theorem B4520231 : Blo 1338988 4520231 := bstep (se 1 (by rfl) ⟨3390173, by rfl⟩ : syracuseStep 4520231 = 6780347) B6780347
theorem B3389759 : Blo 1338988 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B2414927 : Blo 1338988 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B3012947 : Blo 1338988 3012947 := bstep (se 1 (by rfl) ⟨2259710, by rfl⟩ : syracuseStep 3012947 = 4519421) B4519421
theorem B3815905 : Blo 1338988 3815905 := bstep (se 2 (by rfl) ⟨1430964, by rfl⟩ : syracuseStep 3815905 = 2861929) B2861929
theorem B3816065 : Blo 1338988 3816065 := bstep (se 2 (by rfl) ⟨1431024, by rfl⟩ : syracuseStep 3816065 = 2862049) B2862049
theorem B6110009 : Blo 1338988 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B19323785 : Blo 1338988 19323785 := bstep (se 2 (by rfl) ⟨7246419, by rfl⟩ : syracuseStep 19323785 = 14492839) B14492839
theorem B15473915 : Blo 1338988 15473915 := bstep (se 1 (by rfl) ⟨11605436, by rfl⟩ : syracuseStep 15473915 = 23210873) B23210873
theorem B3390761 : Blo 1338988 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B3014063 : Blo 1338988 3014063 := bstep (se 1 (by rfl) ⟨2260547, by rfl⟩ : syracuseStep 3014063 = 4521095) B4521095
theorem B3014171 : Blo 1338988 3014171 := bstep (se 1 (by rfl) ⟨2260628, by rfl⟩ : syracuseStep 3014171 = 4521257) B4521257
theorem B7347743 : Blo 1338988 7347743 := bstep (se 1 (by rfl) ⟨5510807, by rfl⟩ : syracuseStep 7347743 = 11021615) B11021615
theorem B1834537 : Blo 1338988 1834537 := bstep (se 2 (by rfl) ⟨687951, by rfl⟩ : syracuseStep 1834537 = 1375903) B1375903
theorem B14491199 : Blo 1338988 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B3391105 : Blo 1338988 3391105 := bstep (se 2 (by rfl) ⟨1271664, by rfl⟩ : syracuseStep 3391105 = 2543329) B2543329
theorem B208772923 : Blo 1338988 208772923 := bstep (se 1 (by rfl) ⟨156579692, by rfl⟩ : syracuseStep 208772923 = 313159385) B313159385
theorem B6782939 : Blo 1338988 6782939 := bstep (se 1 (by rfl) ⟨5087204, by rfl⟩ : syracuseStep 6782939 = 10174409) B10174409
theorem B3014711 : Blo 1338988 3014711 := bstep (se 1 (by rfl) ⟨2261033, by rfl⟩ : syracuseStep 3014711 = 4522067) B4522067
theorem B3014747 : Blo 1338988 3014747 := bstep (se 1 (by rfl) ⟨2261060, by rfl⟩ : syracuseStep 3014747 = 4522121) B4522121
theorem B17178749 : Blo 1338988 17178749 := bstep (se 3 (by rfl) ⟨3221015, by rfl⟩ : syracuseStep 17178749 = 6442031) B6442031
theorem B16523543 : Blo 1338988 16523543 := bstep (se 1 (by rfl) ⟨12392657, by rfl⟩ : syracuseStep 16523543 = 24785315) B24785315
theorem B3392027 : Blo 1338988 3392027 := bstep (se 1 (by rfl) ⟨2544020, by rfl⟩ : syracuseStep 3392027 = 5088041) B5088041
theorem B5087873 : Blo 1338988 5087873 := bstep (se 2 (by rfl) ⟨1907952, by rfl⟩ : syracuseStep 5087873 = 3815905) B3815905
theorem B2261641 : Blo 1338988 2261641 := bstep (se 2 (by rfl) ⟨848115, by rfl⟩ : syracuseStep 2261641 = 1696231) B1696231
theorem B4522715 : Blo 1338988 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B4522823 : Blo 1338988 4522823 := bstep (se 1 (by rfl) ⟨3392117, by rfl⟩ : syracuseStep 4522823 = 6784235) B6784235
theorem B41231215 : Blo 1338988 41231215 := bstep (se 1 (by rfl) ⟨30923411, by rfl⟩ : syracuseStep 41231215 = 61846823) B61846823
theorem B3015647 : Blo 1338988 3015647 := bstep (se 1 (by rfl) ⟨2261735, by rfl⟩ : syracuseStep 3015647 = 4523471) B4523471
theorem B2261999 : Blo 1338988 2261999 := bstep (se 1 (by rfl) ⟨1696499, by rfl⟩ : syracuseStep 2261999 = 3392999) B3392999
theorem B2008487 : Blo 1338988 2008487 := bstep (se 1 (by rfl) ⟨1506365, by rfl⟩ : syracuseStep 2008487 = 3012731) B3012731
theorem B2008631 : Blo 1338988 2008631 := bstep (se 1 (by rfl) ⟨1506473, by rfl⟩ : syracuseStep 2008631 = 3012947) B3012947
theorem B34834171 : Blo 1338988 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B4073339 : Blo 1338988 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B37152893 : Blo 1338988 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B10315943 : Blo 1338988 10315943 := bstep (se 1 (by rfl) ⟨7736957, by rfl⟩ : syracuseStep 10315943 = 15473915) B15473915
theorem B4294919 : Blo 1338988 4294919 := bstep (se 1 (by rfl) ⟨3221189, by rfl⟩ : syracuseStep 4294919 = 6442379) B6442379
theorem B2009375 : Blo 1338988 2009375 := bstep (se 1 (by rfl) ⟨1507031, by rfl⟩ : syracuseStep 2009375 = 3014063) B3014063
theorem B10176839 : Blo 1338988 10176839 := bstep (se 1 (by rfl) ⟨7632629, by rfl⟩ : syracuseStep 10176839 = 15265259) B15265259
theorem B2009447 : Blo 1338988 2009447 := bstep (se 1 (by rfl) ⟨1507085, by rfl⟩ : syracuseStep 2009447 = 3014171) B3014171
theorem B51530093 : Blo 1338988 51530093 := bstep (se 3 (by rfl) ⟨9661892, by rfl⟩ : syracuseStep 51530093 = 19323785) B19323785
theorem B9660799 : Blo 1338988 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B148695533 : Blo 1338988 148695533 := bstep (se 3 (by rfl) ⟨27880412, by rfl⟩ : syracuseStep 148695533 = 55760825) B55760825
theorem B2009819 : Blo 1338988 2009819 := bstep (se 1 (by rfl) ⟨1507364, by rfl⟩ : syracuseStep 2009819 = 3014729) B3014729
theorem B2009855 : Blo 1338988 2009855 := bstep (se 1 (by rfl) ⟨1507391, by rfl⟩ : syracuseStep 2009855 = 3014783) B3014783
theorem B439757585 : Blo 1338988 439757585 := bstep (se 2 (by rfl) ⟨164909094, by rfl⟩ : syracuseStep 439757585 = 329818189) B329818189
theorem B2009897 : Blo 1338988 2009897 := bstep (se 2 (by rfl) ⟨753711, by rfl⟩ : syracuseStep 2009897 = 1507423) B1507423
theorem B6786017 : Blo 1338988 6786017 := bstep (se 2 (by rfl) ⟨2544756, by rfl⟩ : syracuseStep 6786017 = 5089513) B5089513
theorem B5090471 : Blo 1338988 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B2542843 : Blo 1338988 2542843 := bstep (se 1 (by rfl) ⟨1907132, by rfl⟩ : syracuseStep 2542843 = 3814265) B3814265
theorem B4525523 : Blo 1338988 4525523 := bstep (se 1 (by rfl) ⟨3394142, by rfl⟩ : syracuseStep 4525523 = 6788285) B6788285
theorem B2011079 : Blo 1338988 2011079 := bstep (se 1 (by rfl) ⟨1508309, by rfl⟩ : syracuseStep 2011079 = 3016619) B3016619
theorem B2011115 : Blo 1338988 2011115 := bstep (se 1 (by rfl) ⟨1508336, by rfl⟩ : syracuseStep 2011115 = 3016673) B3016673
theorem B19312667 : Blo 1338988 19312667 := bstep (se 1 (by rfl) ⟨14484500, by rfl⟩ : syracuseStep 19312667 = 28969001) B28969001
theorem B1339483 : Blo 1338988 1339483 := bstep (se 1 (by rfl) ⟨1004612, by rfl⟩ : syracuseStep 1339483 = 2009225) B2009225
theorem B1339551 : Blo 1338988 1339551 := bstep (se 1 (by rfl) ⟨1004663, by rfl⟩ : syracuseStep 1339551 = 2009327) B2009327
theorem B1339615 : Blo 1338988 1339615 := bstep (se 1 (by rfl) ⟨1004711, by rfl⟩ : syracuseStep 1339615 = 2009423) B2009423
theorem B1609951 : Blo 1338988 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B2544043 : Blo 1338988 2544043 := bstep (se 1 (by rfl) ⟨1908032, by rfl⟩ : syracuseStep 2544043 = 3816065) B3816065
theorem B1339935 : Blo 1338988 1339935 := bstep (se 1 (by rfl) ⟨1004951, by rfl⟩ : syracuseStep 1339935 = 2009903) B2009903
theorem B10318373 : Blo 1338988 10318373 := bstep (se 4 (by rfl) ⟨967347, by rfl⟩ : syracuseStep 10318373 = 1934695) B1934695
theorem B8589989 : Blo 1338988 8589989 := bstep (se 4 (by rfl) ⟨805311, by rfl⟩ : syracuseStep 8589989 = 1610623) B1610623
theorem B2446049 : Blo 1338988 2446049 := bstep (se 2 (by rfl) ⟨917268, by rfl⟩ : syracuseStep 2446049 = 1834537) B1834537
theorem B1340383 : Blo 1338988 1340383 := bstep (se 1 (by rfl) ⟨1005287, by rfl⟩ : syracuseStep 1340383 = 2010575) B2010575
theorem B1340639 : Blo 1338988 1340639 := bstep (se 1 (by rfl) ⟨1005479, by rfl⟩ : syracuseStep 1340639 = 2010959) B2010959
theorem B12219659 : Blo 1338988 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B11015639 : Blo 1338988 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B4290023 : Blo 1338988 4290023 := bstep (se 1 (by rfl) ⟨3217517, by rfl⟩ : syracuseStep 4290023 = 6435035) B6435035
theorem B1340959 : Blo 1338988 1340959 := bstep (se 1 (by rfl) ⟨1005719, by rfl⟩ : syracuseStep 1340959 = 2011439) B2011439
theorem B1340975 : Blo 1338988 1340975 := bstep (se 1 (by rfl) ⟨1005731, by rfl⟩ : syracuseStep 1340975 = 2011463) B2011463
theorem B9164441 : Blo 1338988 9164441 := bstep (se 2 (by rfl) ⟨3436665, by rfl⟩ : syracuseStep 9164441 = 6873331) B6873331
theorem B25769663 : Blo 1338988 25769663 := bstep (se 1 (by rfl) ⟨19327247, by rfl⟩ : syracuseStep 25769663 = 38654495) B38654495
theorem B5085139 : Blo 1338988 5085139 := bstep (se 1 (by rfl) ⟨3813854, by rfl⟩ : syracuseStep 5085139 = 7627709) B7627709
theorem B1906939 : Blo 1338988 1906939 := bstep (se 1 (by rfl) ⟨1430204, by rfl⟩ : syracuseStep 1906939 = 2860409) B2860409
theorem B19593515 : Blo 1338988 19593515 := bstep (se 1 (by rfl) ⟨14695136, by rfl⟩ : syracuseStep 19593515 = 29390273) B29390273
theorem B2259623 : Blo 1338988 2259623 := bstep (se 1 (by rfl) ⟨1694717, by rfl⟩ : syracuseStep 2259623 = 3389435) B3389435
theorem B3013487 : Blo 1338988 3013487 := bstep (se 1 (by rfl) ⟨2260115, by rfl⟩ : syracuseStep 3013487 = 4520231) B4520231
theorem B2259839 : Blo 1338988 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B10173437 : Blo 1338988 10173437 := bstep (se 3 (by rfl) ⟨1907519, by rfl⟩ : syracuseStep 10173437 = 3815039) B3815039
theorem B4521473 : Blo 1338988 4521473 := bstep (se 2 (by rfl) ⟨1695552, by rfl⟩ : syracuseStep 4521473 = 3391105) B3391105
theorem B2260507 : Blo 1338988 2260507 := bstep (se 1 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 2260507 = 3390761) B3390761
theorem B4898495 : Blo 1338988 4898495 := bstep (se 1 (by rfl) ⟨3673871, by rfl⟩ : syracuseStep 4898495 = 7347743) B7347743
theorem B278363897 : Blo 1338988 278363897 := bstep (se 2 (by rfl) ⟨104386461, by rfl⟩ : syracuseStep 278363897 = 208772923) B208772923
theorem B4521959 : Blo 1338988 4521959 := bstep (se 1 (by rfl) ⟨3391469, by rfl⟩ : syracuseStep 4521959 = 6782939) B6782939
theorem B11452499 : Blo 1338988 11452499 := bstep (se 1 (by rfl) ⟨8589374, by rfl⟩ : syracuseStep 11452499 = 17178749) B17178749
theorem B2146601 : Blo 1338988 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B2261351 : Blo 1338988 2261351 := bstep (se 1 (by rfl) ⟨1696013, by rfl⟩ : syracuseStep 2261351 = 3392027) B3392027
theorem B3391915 : Blo 1338988 3391915 := bstep (se 1 (by rfl) ⟨2543936, by rfl⟩ : syracuseStep 3391915 = 5087873) B5087873
theorem B3015143 : Blo 1338988 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B1630699 : Blo 1338988 1630699 := bstep (se 1 (by rfl) ⟨1223024, by rfl⟩ : syracuseStep 1630699 = 2446049) B2446049
theorem B3015215 : Blo 1338988 3015215 := bstep (se 1 (by rfl) ⟨2261411, by rfl⟩ : syracuseStep 3015215 = 4522823) B4522823
theorem B3392057 : Blo 1338988 3392057 := bstep (se 2 (by rfl) ⟨1272021, by rfl⟩ : syracuseStep 3392057 = 2544043) B2544043
theorem B1507999 : Blo 1338988 1507999 := bstep (se 1 (by rfl) ⟨1130999, by rfl⟩ : syracuseStep 1507999 = 2261999) B2261999
theorem B3015521 : Blo 1338988 3015521 := bstep (se 2 (by rfl) ⟨1130820, by rfl⟩ : syracuseStep 3015521 = 2261641) B2261641
theorem B17179775 : Blo 1338988 17179775 := bstep (se 1 (by rfl) ⟨12884831, by rfl⟩ : syracuseStep 17179775 = 25769663) B25769663
theorem B6784559 : Blo 1338988 6784559 := bstep (se 1 (by rfl) ⟨5088419, by rfl⟩ : syracuseStep 6784559 = 10176839) B10176839
theorem B24438509 : Blo 1338988 24438509 := bstep (se 3 (by rfl) ⟨4582220, by rfl⟩ : syracuseStep 24438509 = 9164441) B9164441
theorem B22906637 : Blo 1338988 22906637 := bstep (se 3 (by rfl) ⟨4294994, by rfl⟩ : syracuseStep 22906637 = 8589989) B8589989
theorem B2008991 : Blo 1338988 2008991 := bstep (se 1 (by rfl) ⟨1506743, by rfl⟩ : syracuseStep 2008991 = 3013487) B3013487
theorem B4524011 : Blo 1338988 4524011 := bstep (se 1 (by rfl) ⟨3393008, by rfl⟩ : syracuseStep 4524011 = 6786017) B6786017
theorem B3393647 : Blo 1338988 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B3017015 : Blo 1338988 3017015 := bstep (se 1 (by rfl) ⟨2262761, by rfl⟩ : syracuseStep 3017015 = 4525523) B4525523
theorem B185575931 : Blo 1338988 185575931 := bstep (se 1 (by rfl) ⟨139181948, by rfl⟩ : syracuseStep 185575931 = 278363897) B278363897
theorem B2009807 : Blo 1338988 2009807 := bstep (se 1 (by rfl) ⟨1507355, by rfl⟩ : syracuseStep 2009807 = 3014711) B3014711
theorem B2009831 : Blo 1338988 2009831 := bstep (se 1 (by rfl) ⟨1507373, by rfl⟩ : syracuseStep 2009831 = 3014747) B3014747
theorem B2542585 : Blo 1338988 2542585 := bstep (se 2 (by rfl) ⟨953469, by rfl⟩ : syracuseStep 2542585 = 1906939) B1906939
theorem B12881065 : Blo 1338988 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B2010431 : Blo 1338988 2010431 := bstep (se 1 (by rfl) ⟨1507823, by rfl⟩ : syracuseStep 2010431 = 3015647) B3015647
theorem B8146439 : Blo 1338988 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B1338991 : Blo 1338988 1338991 := bstep (se 1 (by rfl) ⟨1004243, by rfl⟩ : syracuseStep 1338991 = 2008487) B2008487
theorem B7343759 : Blo 1338988 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B1339087 : Blo 1338988 1339087 := bstep (se 1 (by rfl) ⟨1004315, by rfl⟩ : syracuseStep 1339087 = 2008631) B2008631
theorem B11440061 : Blo 1338988 11440061 := bstep (se 3 (by rfl) ⟨2145011, by rfl⟩ : syracuseStep 11440061 = 4290023) B4290023
theorem B24768595 : Blo 1338988 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B6877295 : Blo 1338988 6877295 := bstep (se 1 (by rfl) ⟨5157971, by rfl⟩ : syracuseStep 6877295 = 10315943) B10315943
theorem B2863279 : Blo 1338988 2863279 := bstep (se 1 (by rfl) ⟨2147459, by rfl⟩ : syracuseStep 2863279 = 4294919) B4294919
theorem B1339583 : Blo 1338988 1339583 := bstep (se 1 (by rfl) ⟨1004687, by rfl⟩ : syracuseStep 1339583 = 2009375) B2009375
theorem B13062343 : Blo 1338988 13062343 := bstep (se 1 (by rfl) ⟨9796757, by rfl⟩ : syracuseStep 13062343 = 19593515) B19593515
theorem B1339631 : Blo 1338988 1339631 := bstep (se 1 (by rfl) ⟨1004723, by rfl⟩ : syracuseStep 1339631 = 2009447) B2009447
theorem B34353395 : Blo 1338988 34353395 := bstep (se 1 (by rfl) ⟨25765046, by rfl⟩ : syracuseStep 34353395 = 51530093) B51530093
theorem B1339879 : Blo 1338988 1339879 := bstep (se 1 (by rfl) ⟨1004909, by rfl⟩ : syracuseStep 1339879 = 2009819) B2009819
theorem B1339903 : Blo 1338988 1339903 := bstep (se 1 (by rfl) ⟨1004927, by rfl⟩ : syracuseStep 1339903 = 2009855) B2009855
theorem B293171723 : Blo 1338988 293171723 := bstep (se 1 (by rfl) ⟨219878792, by rfl⟩ : syracuseStep 293171723 = 439757585) B439757585
theorem B1339931 : Blo 1338988 1339931 := bstep (se 1 (by rfl) ⟨1004948, by rfl⟩ : syracuseStep 1339931 = 2009897) B2009897
theorem B46445561 : Blo 1338988 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B3265663 : Blo 1338988 3265663 := bstep (se 1 (by rfl) ⟨2449247, by rfl⟩ : syracuseStep 3265663 = 4898495) B4898495
theorem B6780185 : Blo 1338988 6780185 := bstep (se 2 (by rfl) ⟨2542569, by rfl⟩ : syracuseStep 6780185 = 5085139) B5085139
theorem B1340719 : Blo 1338988 1340719 := bstep (se 1 (by rfl) ⟨1005539, by rfl⟩ : syracuseStep 1340719 = 2011079) B2011079
theorem B1340743 : Blo 1338988 1340743 := bstep (se 1 (by rfl) ⟨1005557, by rfl⟩ : syracuseStep 1340743 = 2011115) B2011115
theorem B12875111 : Blo 1338988 12875111 := bstep (se 1 (by rfl) ⟨9656333, by rfl⟩ : syracuseStep 12875111 = 19312667) B19312667
theorem B11015695 : Blo 1338988 11015695 := bstep (se 1 (by rfl) ⟨8261771, by rfl⟩ : syracuseStep 11015695 = 16523543) B16523543
theorem B6878915 : Blo 1338988 6878915 := bstep (se 1 (by rfl) ⟨5159186, by rfl⟩ : syracuseStep 6878915 = 10318373) B10318373
theorem B54974953 : Blo 1338988 54974953 := bstep (se 2 (by rfl) ⟨20615607, by rfl⟩ : syracuseStep 54974953 = 41231215) B41231215
theorem B99130355 : Blo 1338988 99130355 := bstep (se 1 (by rfl) ⟨74347766, by rfl⟩ : syracuseStep 99130355 = 148695533) B148695533
theorem B3390457 : Blo 1338988 3390457 := bstep (se 2 (by rfl) ⟨1271421, by rfl⟩ : syracuseStep 3390457 = 2542843) B2542843
theorem B1506415 : Blo 1338988 1506415 := bstep (se 1 (by rfl) ⟨1129811, by rfl⟩ : syracuseStep 1506415 = 2259623) B2259623
theorem B1506559 : Blo 1338988 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B6782291 : Blo 1338988 6782291 := bstep (se 1 (by rfl) ⟨5086718, by rfl⟩ : syracuseStep 6782291 = 10173437) B10173437
theorem B3014009 : Blo 1338988 3014009 := bstep (se 2 (by rfl) ⟨1130253, by rfl⟩ : syracuseStep 3014009 = 2260507) B2260507
theorem B10862237 : Blo 1338988 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B3014315 : Blo 1338988 3014315 := bstep (se 1 (by rfl) ⟨2260736, by rfl⟩ : syracuseStep 3014315 = 4521473) B4521473
theorem B3014639 : Blo 1338988 3014639 := bstep (se 1 (by rfl) ⟨2260979, by rfl⟩ : syracuseStep 3014639 = 4521959) B4521959
theorem B7634999 : Blo 1338988 7634999 := bstep (se 1 (by rfl) ⟨5726249, by rfl⟩ : syracuseStep 7634999 = 11452499) B11452499
theorem B3817705 : Blo 1338988 3817705 := bstep (se 2 (by rfl) ⟨1431639, by rfl⟩ : syracuseStep 3817705 = 2863279) B2863279
theorem B1507567 : Blo 1338988 1507567 := bstep (se 1 (by rfl) ⟨1130675, by rfl⟩ : syracuseStep 1507567 = 2261351) B2261351
theorem B17416457 : Blo 1338988 17416457 := bstep (se 2 (by rfl) ⟨6531171, by rfl⟩ : syracuseStep 17416457 = 13062343) B13062343
theorem B2261371 : Blo 1338988 2261371 := bstep (se 1 (by rfl) ⟨1696028, by rfl⟩ : syracuseStep 2261371 = 3392057) B3392057
theorem B4522553 : Blo 1338988 4522553 := bstep (se 2 (by rfl) ⟨1695957, by rfl⟩ : syracuseStep 4522553 = 3391915) B3391915
theorem B11453183 : Blo 1338988 11453183 := bstep (se 1 (by rfl) ⟨8589887, by rfl⟩ : syracuseStep 11453183 = 17179775) B17179775
theorem B4523039 : Blo 1338988 4523039 := bstep (se 1 (by rfl) ⟨3392279, by rfl⟩ : syracuseStep 4523039 = 6784559) B6784559
theorem B15271091 : Blo 1338988 15271091 := bstep (se 1 (by rfl) ⟨11453318, by rfl⟩ : syracuseStep 15271091 = 22906637) B22906637
theorem B3016007 : Blo 1338988 3016007 := bstep (se 1 (by rfl) ⟨2262005, by rfl⟩ : syracuseStep 3016007 = 4524011) B4524011
theorem B2262431 : Blo 1338988 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B2008553 : Blo 1338988 2008553 := bstep (se 2 (by rfl) ⟨753207, by rfl⟩ : syracuseStep 2008553 = 1506415) B1506415
theorem B123717287 : Blo 1338988 123717287 := bstep (se 1 (by rfl) ⟨92787965, by rfl⟩ : syracuseStep 123717287 = 185575931) B185575931
theorem B2008745 : Blo 1338988 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B66086903 : Blo 1338988 66086903 := bstep (se 1 (by rfl) ⟨49565177, by rfl⟩ : syracuseStep 66086903 = 99130355) B99130355
theorem B2009339 : Blo 1338988 2009339 := bstep (se 1 (by rfl) ⟨1507004, by rfl⟩ : syracuseStep 2009339 = 3014009) B3014009
theorem B2009543 : Blo 1338988 2009543 := bstep (se 1 (by rfl) ⟨1507157, by rfl⟩ : syracuseStep 2009543 = 3014315) B3014315
theorem B2009759 : Blo 1338988 2009759 := bstep (se 1 (by rfl) ⟨1507319, by rfl⟩ : syracuseStep 2009759 = 3014639) B3014639
theorem B33024793 : Blo 1338988 33024793 := bstep (se 2 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 33024793 = 24768595) B24768595
theorem B2010095 : Blo 1338988 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B195447815 : Blo 1338988 195447815 := bstep (se 1 (by rfl) ⟨146585861, by rfl⟩ : syracuseStep 195447815 = 293171723) B293171723
theorem B2010143 : Blo 1338988 2010143 := bstep (se 1 (by rfl) ⟨1507607, by rfl⟩ : syracuseStep 2010143 = 3015215) B3015215
theorem B2010347 : Blo 1338988 2010347 := bstep (se 1 (by rfl) ⟨1507760, by rfl⟩ : syracuseStep 2010347 = 3015521) B3015521
theorem B2010665 : Blo 1338988 2010665 := bstep (se 2 (by rfl) ⟨753999, by rfl⟩ : syracuseStep 2010665 = 1507999) B1507999
theorem B1339327 : Blo 1338988 1339327 := bstep (se 1 (by rfl) ⟨1004495, by rfl⟩ : syracuseStep 1339327 = 2008991) B2008991
theorem B4354217 : Blo 1338988 4354217 := bstep (se 2 (by rfl) ⟨1632831, by rfl⟩ : syracuseStep 4354217 = 3265663) B3265663
theorem B2011343 : Blo 1338988 2011343 := bstep (se 1 (by rfl) ⟨1508507, by rfl⟩ : syracuseStep 2011343 = 3017015) B3017015
theorem B17174753 : Blo 1338988 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B1339871 : Blo 1338988 1339871 := bstep (se 1 (by rfl) ⟨1004903, by rfl⟩ : syracuseStep 1339871 = 2009807) B2009807
theorem B1339887 : Blo 1338988 1339887 := bstep (se 1 (by rfl) ⟨1004915, by rfl⟩ : syracuseStep 1339887 = 2009831) B2009831
theorem B1340287 : Blo 1338988 1340287 := bstep (se 1 (by rfl) ⟨1005215, by rfl⟩ : syracuseStep 1340287 = 2010431) B2010431
theorem B4895839 : Blo 1338988 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B8697061 : Blo 1338988 8697061 := bstep (se 4 (by rfl) ⟨815349, by rfl⟩ : syracuseStep 8697061 = 1630699) B1630699
theorem B4584863 : Blo 1338988 4584863 := bstep (se 1 (by rfl) ⟨3438647, by rfl⟩ : syracuseStep 4584863 = 6877295) B6877295
theorem B58750373 : Blo 1338988 58750373 := bstep (se 4 (by rfl) ⟨5507847, by rfl⟩ : syracuseStep 58750373 = 11015695) B11015695
theorem B22902263 : Blo 1338988 22902263 := bstep (se 1 (by rfl) ⟨17176697, by rfl⟩ : syracuseStep 22902263 = 34353395) B34353395
theorem B73299937 : Blo 1338988 73299937 := bstep (se 2 (by rfl) ⟨27487476, by rfl⟩ : syracuseStep 73299937 = 54974953) B54974953
theorem B30963707 : Blo 1338988 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B5724269 : Blo 1338988 5724269 := bstep (se 3 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 5724269 = 2146601) B2146601
theorem B4520123 : Blo 1338988 4520123 := bstep (se 1 (by rfl) ⟨3390092, by rfl⟩ : syracuseStep 4520123 = 6780185) B6780185
theorem B8583407 : Blo 1338988 8583407 := bstep (se 1 (by rfl) ⟨6437555, by rfl⟩ : syracuseStep 8583407 = 12875111) B12875111
theorem B4585943 : Blo 1338988 4585943 := bstep (se 1 (by rfl) ⟨3439457, by rfl⟩ : syracuseStep 4585943 = 6878915) B6878915
theorem B16292339 : Blo 1338988 16292339 := bstep (se 1 (by rfl) ⟨12219254, by rfl⟩ : syracuseStep 16292339 = 24438509) B24438509
theorem B3390113 : Blo 1338988 3390113 := bstep (se 2 (by rfl) ⟨1271292, by rfl⟩ : syracuseStep 3390113 = 2542585) B2542585
theorem B4520609 : Blo 1338988 4520609 := bstep (se 2 (by rfl) ⟨1695228, by rfl⟩ : syracuseStep 4520609 = 3390457) B3390457
theorem B4521527 : Blo 1338988 4521527 := bstep (se 1 (by rfl) ⟨3391145, by rfl⟩ : syracuseStep 4521527 = 6782291) B6782291
theorem B5430959 : Blo 1338988 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B7241491 : Blo 1338988 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B7626707 : Blo 1338988 7626707 := bstep (se 1 (by rfl) ⟨5720030, by rfl⟩ : syracuseStep 7626707 = 11440061) B11440061
theorem B3015035 : Blo 1338988 3015035 := bstep (se 1 (by rfl) ⟨2261276, by rfl⟩ : syracuseStep 3015035 = 4522553) B4522553
theorem B3015161 : Blo 1338988 3015161 := bstep (se 2 (by rfl) ⟨1130685, by rfl⟩ : syracuseStep 3015161 = 2261371) B2261371
theorem B7635455 : Blo 1338988 7635455 := bstep (se 1 (by rfl) ⟨5726591, by rfl⟩ : syracuseStep 7635455 = 11453183) B11453183
theorem B3015359 : Blo 1338988 3015359 := bstep (se 1 (by rfl) ⟨2261519, by rfl⟩ : syracuseStep 3015359 = 4523039) B4523039
theorem B1508287 : Blo 1338988 1508287 := bstep (se 1 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 1508287 = 2262431) B2262431
theorem B39166915 : Blo 1338988 39166915 := bstep (se 1 (by rfl) ⟨29375186, by rfl⟩ : syracuseStep 39166915 = 58750373) B58750373
theorem B44033057 : Blo 1338988 44033057 := bstep (se 2 (by rfl) ⟨16512396, by rfl⟩ : syracuseStep 44033057 = 33024793) B33024793
theorem B82478191 : Blo 1338988 82478191 := bstep (se 1 (by rfl) ⟨61858643, by rfl⟩ : syracuseStep 82478191 = 123717287) B123717287
theorem B46384325 : Blo 1338988 46384325 := bstep (se 4 (by rfl) ⟨4348530, by rfl⟩ : syracuseStep 46384325 = 8697061) B8697061
theorem B44057935 : Blo 1338988 44057935 := bstep (se 1 (by rfl) ⟨33043451, by rfl⟩ : syracuseStep 44057935 = 66086903) B66086903
theorem B97733249 : Blo 1338988 97733249 := bstep (se 2 (by rfl) ⟨36649968, by rfl⟩ : syracuseStep 97733249 = 73299937) B73299937
theorem B5089999 : Blo 1338988 5089999 := bstep (se 1 (by rfl) ⟨3817499, by rfl⟩ : syracuseStep 5089999 = 7634999) B7634999
theorem B2902811 : Blo 1338988 2902811 := bstep (se 1 (by rfl) ⟨2177108, by rfl⟩ : syracuseStep 2902811 = 4354217) B4354217
theorem B11610971 : Blo 1338988 11610971 := bstep (se 1 (by rfl) ⟨8708228, by rfl⟩ : syracuseStep 11610971 = 17416457) B17416457
theorem B5090273 : Blo 1338988 5090273 := bstep (se 2 (by rfl) ⟨1908852, by rfl⟩ : syracuseStep 5090273 = 3817705) B3817705
theorem B2010089 : Blo 1338988 2010089 := bstep (se 2 (by rfl) ⟨753783, by rfl⟩ : syracuseStep 2010089 = 1507567) B1507567
theorem B2010671 : Blo 1338988 2010671 := bstep (se 1 (by rfl) ⟨1508003, by rfl⟩ : syracuseStep 2010671 = 3016007) B3016007
theorem B1339035 : Blo 1338988 1339035 := bstep (se 1 (by rfl) ⟨1004276, by rfl⟩ : syracuseStep 1339035 = 2008553) B2008553
theorem B12226301 : Blo 1338988 12226301 := bstep (se 3 (by rfl) ⟨2292431, by rfl⟩ : syracuseStep 12226301 = 4584863) B4584863
theorem B1339163 : Blo 1338988 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B5722271 : Blo 1338988 5722271 := bstep (se 1 (by rfl) ⟨4291703, by rfl⟩ : syracuseStep 5722271 = 8583407) B8583407
theorem B1339559 : Blo 1338988 1339559 := bstep (se 1 (by rfl) ⟨1004669, by rfl⟩ : syracuseStep 1339559 = 2009339) B2009339
theorem B1339695 : Blo 1338988 1339695 := bstep (se 1 (by rfl) ⟨1004771, by rfl⟩ : syracuseStep 1339695 = 2009543) B2009543
theorem B1339839 : Blo 1338988 1339839 := bstep (se 1 (by rfl) ⟨1004879, by rfl⟩ : syracuseStep 1339839 = 2009759) B2009759
theorem B1340063 : Blo 1338988 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B130298543 : Blo 1338988 130298543 := bstep (se 1 (by rfl) ⟨97723907, by rfl⟩ : syracuseStep 130298543 = 195447815) B195447815
theorem B1340095 : Blo 1338988 1340095 := bstep (se 1 (by rfl) ⟨1005071, by rfl⟩ : syracuseStep 1340095 = 2010143) B2010143
theorem B1340231 : Blo 1338988 1340231 := bstep (se 1 (by rfl) ⟨1005173, by rfl⟩ : syracuseStep 1340231 = 2010347) B2010347
theorem B9655321 : Blo 1338988 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B1340443 : Blo 1338988 1340443 := bstep (se 1 (by rfl) ⟨1005332, by rfl⟩ : syracuseStep 1340443 = 2010665) B2010665
theorem B5084471 : Blo 1338988 5084471 := bstep (se 1 (by rfl) ⟨3813353, by rfl⟩ : syracuseStep 5084471 = 7626707) B7626707
theorem B1340895 : Blo 1338988 1340895 := bstep (se 1 (by rfl) ⟨1005671, by rfl⟩ : syracuseStep 1340895 = 2011343) B2011343
theorem B11449835 : Blo 1338988 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B10180727 : Blo 1338988 10180727 := bstep (se 1 (by rfl) ⟨7635545, by rfl⟩ : syracuseStep 10180727 = 15271091) B15271091
theorem B15268175 : Blo 1338988 15268175 := bstep (se 1 (by rfl) ⟨11451131, by rfl⟩ : syracuseStep 15268175 = 22902263) B22902263
theorem B12229181 : Blo 1338988 12229181 := bstep (se 3 (by rfl) ⟨2292971, by rfl⟩ : syracuseStep 12229181 = 4585943) B4585943
theorem B20642471 : Blo 1338988 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B3816179 : Blo 1338988 3816179 := bstep (se 1 (by rfl) ⟨2862134, by rfl⟩ : syracuseStep 3816179 = 5724269) B5724269
theorem B3013415 : Blo 1338988 3013415 := bstep (se 1 (by rfl) ⟨2260061, by rfl⟩ : syracuseStep 3013415 = 4520123) B4520123
theorem B6527785 : Blo 1338988 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B10861559 : Blo 1338988 10861559 := bstep (se 1 (by rfl) ⟨8146169, by rfl⟩ : syracuseStep 10861559 = 16292339) B16292339
theorem B2260075 : Blo 1338988 2260075 := bstep (se 1 (by rfl) ⟨1695056, by rfl⟩ : syracuseStep 2260075 = 3390113) B3390113
theorem B3013739 : Blo 1338988 3013739 := bstep (se 1 (by rfl) ⟨2260304, by rfl⟩ : syracuseStep 3013739 = 4520609) B4520609
theorem B3014351 : Blo 1338988 3014351 := bstep (se 1 (by rfl) ⟨2260763, by rfl⟩ : syracuseStep 3014351 = 4521527) B4521527
theorem B3620639 : Blo 1338988 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B109970921 : Blo 1338988 109970921 := bstep (se 2 (by rfl) ⟨41239095, by rfl⟩ : syracuseStep 109970921 = 82478191) B82478191
theorem B8152787 : Blo 1338988 8152787 := bstep (se 1 (by rfl) ⟨6114590, by rfl⟩ : syracuseStep 8152787 = 12229181) B12229181
theorem B2008943 : Blo 1338988 2008943 := bstep (se 1 (by rfl) ⟨1506707, by rfl⟩ : syracuseStep 2008943 = 3013415) B3013415
theorem B3393515 : Blo 1338988 3393515 := bstep (se 1 (by rfl) ⟨2545136, by rfl⟩ : syracuseStep 3393515 = 5090273) B5090273
theorem B2009159 : Blo 1338988 2009159 := bstep (se 1 (by rfl) ⟨1506869, by rfl⟩ : syracuseStep 2009159 = 3013739) B3013739
theorem B2009567 : Blo 1338988 2009567 := bstep (se 1 (by rfl) ⟨1507175, by rfl⟩ : syracuseStep 2009567 = 3014351) B3014351
theorem B2010023 : Blo 1338988 2010023 := bstep (se 1 (by rfl) ⟨1507517, by rfl⟩ : syracuseStep 2010023 = 3015035) B3015035
theorem B2010107 : Blo 1338988 2010107 := bstep (se 1 (by rfl) ⟨1507580, by rfl⟩ : syracuseStep 2010107 = 3015161) B3015161
theorem B5090303 : Blo 1338988 5090303 := bstep (se 1 (by rfl) ⟨3817727, by rfl⟩ : syracuseStep 5090303 = 7635455) B7635455
theorem B2010239 : Blo 1338988 2010239 := bstep (se 1 (by rfl) ⟨1507679, by rfl⟩ : syracuseStep 2010239 = 3015359) B3015359
theorem B29355371 : Blo 1338988 29355371 := bstep (se 1 (by rfl) ⟨22016528, by rfl⟩ : syracuseStep 29355371 = 44033057) B44033057
theorem B6786665 : Blo 1338988 6786665 := bstep (se 2 (by rfl) ⟨2544999, by rfl⟩ : syracuseStep 6786665 = 5089999) B5089999
theorem B8703713 : Blo 1338988 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B2011049 : Blo 1338988 2011049 := bstep (se 2 (by rfl) ⟨754143, by rfl⟩ : syracuseStep 2011049 = 1508287) B1508287
theorem B12873761 : Blo 1338988 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B6787151 : Blo 1338988 6787151 := bstep (se 1 (by rfl) ⟨5090363, by rfl⟩ : syracuseStep 6787151 = 10180727) B10180727
theorem B10178783 : Blo 1338988 10178783 := bstep (se 1 (by rfl) ⟨7634087, by rfl⟩ : syracuseStep 10178783 = 15268175) B15268175
theorem B234975653 : Blo 1338988 234975653 := bstep (se 4 (by rfl) ⟨22028967, by rfl⟩ : syracuseStep 234975653 = 44057935) B44057935
theorem B65155499 : Blo 1338988 65155499 := bstep (se 1 (by rfl) ⟨48866624, by rfl⟩ : syracuseStep 65155499 = 97733249) B97733249
theorem B2544119 : Blo 1338988 2544119 := bstep (se 1 (by rfl) ⟨1908089, by rfl⟩ : syracuseStep 2544119 = 3816179) B3816179
theorem B1340059 : Blo 1338988 1340059 := bstep (se 1 (by rfl) ⟨1005044, by rfl⟩ : syracuseStep 1340059 = 2010089) B2010089
theorem B9655037 : Blo 1338988 9655037 := bstep (se 3 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 9655037 = 3620639) B3620639
theorem B1340447 : Blo 1338988 1340447 := bstep (se 1 (by rfl) ⟨1005335, by rfl⟩ : syracuseStep 1340447 = 2010671) B2010671
theorem B3814847 : Blo 1338988 3814847 := bstep (se 1 (by rfl) ⟨2861135, by rfl⟩ : syracuseStep 3814847 = 5722271) B5722271
theorem B86865695 : Blo 1338988 86865695 := bstep (se 1 (by rfl) ⟨65149271, by rfl⟩ : syracuseStep 86865695 = 130298543) B130298543
theorem B30922883 : Blo 1338988 30922883 := bstep (se 1 (by rfl) ⟨23192162, by rfl⟩ : syracuseStep 30922883 = 46384325) B46384325
theorem B3389647 : Blo 1338988 3389647 := bstep (se 1 (by rfl) ⟨2542235, by rfl⟩ : syracuseStep 3389647 = 5084471) B5084471
theorem B7633223 : Blo 1338988 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B52222553 : Blo 1338988 52222553 := bstep (se 2 (by rfl) ⟨19583457, by rfl⟩ : syracuseStep 52222553 = 39166915) B39166915
theorem B3013433 : Blo 1338988 3013433 := bstep (se 2 (by rfl) ⟨1130037, by rfl⟩ : syracuseStep 3013433 = 2260075) B2260075
theorem B13761647 : Blo 1338988 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B7740647 : Blo 1338988 7740647 := bstep (se 1 (by rfl) ⟨5805485, by rfl⟩ : syracuseStep 7740647 = 11610971) B11610971
theorem B7241039 : Blo 1338988 7241039 := bstep (se 1 (by rfl) ⟨5430779, by rfl⟩ : syracuseStep 7241039 = 10861559) B10861559
theorem B7740829 : Blo 1338988 7740829 := bstep (se 3 (by rfl) ⟨1451405, by rfl⟩ : syracuseStep 7740829 = 2902811) B2902811
theorem B8150867 : Blo 1338988 8150867 := bstep (se 1 (by rfl) ⟨6113150, by rfl⟩ : syracuseStep 8150867 = 12226301) B12226301
theorem B1696079 : Blo 1338988 1696079 := bstep (se 1 (by rfl) ⟨1272059, by rfl⟩ : syracuseStep 1696079 = 2544119) B2544119
theorem B57910463 : Blo 1338988 57910463 := bstep (se 1 (by rfl) ⟨43432847, by rfl⟩ : syracuseStep 57910463 = 86865695) B86865695
theorem B2262343 : Blo 1338988 2262343 := bstep (se 1 (by rfl) ⟨1696757, by rfl⟩ : syracuseStep 2262343 = 3393515) B3393515
theorem B5088815 : Blo 1338988 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B2008955 : Blo 1338988 2008955 := bstep (se 1 (by rfl) ⟨1506716, by rfl⟩ : syracuseStep 2008955 = 3013433) B3013433
theorem B23209901 : Blo 1338988 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B3393535 : Blo 1338988 3393535 := bstep (se 1 (by rfl) ⟨2545151, by rfl⟩ : syracuseStep 3393535 = 5090303) B5090303
theorem B4827359 : Blo 1338988 4827359 := bstep (se 1 (by rfl) ⟨3620519, by rfl⟩ : syracuseStep 4827359 = 7241039) B7241039
theorem B4524443 : Blo 1338988 4524443 := bstep (se 1 (by rfl) ⟨3393332, by rfl⟩ : syracuseStep 4524443 = 6786665) B6786665
theorem B5433911 : Blo 1338988 5433911 := bstep (se 1 (by rfl) ⟨4075433, by rfl⟩ : syracuseStep 5433911 = 8150867) B8150867
theorem B4524767 : Blo 1338988 4524767 := bstep (se 1 (by rfl) ⟨3393575, by rfl⟩ : syracuseStep 4524767 = 6787151) B6787151
theorem B6785855 : Blo 1338988 6785855 := bstep (se 1 (by rfl) ⟨5089391, by rfl⟩ : syracuseStep 6785855 = 10178783) B10178783
theorem B156650435 : Blo 1338988 156650435 := bstep (se 1 (by rfl) ⟨117487826, by rfl⟩ : syracuseStep 156650435 = 234975653) B234975653
theorem B43436999 : Blo 1338988 43436999 := bstep (se 1 (by rfl) ⟨32577749, by rfl⟩ : syracuseStep 43436999 = 65155499) B65155499
theorem B2543231 : Blo 1338988 2543231 := bstep (se 1 (by rfl) ⟨1907423, by rfl⟩ : syracuseStep 2543231 = 3814847) B3814847
theorem B73313947 : Blo 1338988 73313947 := bstep (se 1 (by rfl) ⟨54985460, by rfl⟩ : syracuseStep 73313947 = 109970921) B109970921
theorem B5435191 : Blo 1338988 5435191 := bstep (se 1 (by rfl) ⟨4076393, by rfl⟩ : syracuseStep 5435191 = 8152787) B8152787
theorem B1339295 : Blo 1338988 1339295 := bstep (se 1 (by rfl) ⟨1004471, by rfl⟩ : syracuseStep 1339295 = 2008943) B2008943
theorem B1339439 : Blo 1338988 1339439 := bstep (se 1 (by rfl) ⟨1004579, by rfl⟩ : syracuseStep 1339439 = 2009159) B2009159
theorem B20615255 : Blo 1338988 20615255 := bstep (se 1 (by rfl) ⟨15461441, by rfl⟩ : syracuseStep 20615255 = 30922883) B30922883
theorem B1339711 : Blo 1338988 1339711 := bstep (se 1 (by rfl) ⟨1004783, by rfl⟩ : syracuseStep 1339711 = 2009567) B2009567
theorem B1340015 : Blo 1338988 1340015 := bstep (se 1 (by rfl) ⟨1005011, by rfl⟩ : syracuseStep 1340015 = 2010023) B2010023
theorem B1340071 : Blo 1338988 1340071 := bstep (se 1 (by rfl) ⟨1005053, by rfl⟩ : syracuseStep 1340071 = 2010107) B2010107
theorem B1340159 : Blo 1338988 1340159 := bstep (se 1 (by rfl) ⟨1005119, by rfl⟩ : syracuseStep 1340159 = 2010239) B2010239
theorem B41284421 : Blo 1338988 41284421 := bstep (se 4 (by rfl) ⟨3870414, by rfl⟩ : syracuseStep 41284421 = 7740829) B7740829
theorem B1340699 : Blo 1338988 1340699 := bstep (se 1 (by rfl) ⟨1005524, by rfl⟩ : syracuseStep 1340699 = 2011049) B2011049
theorem B8582507 : Blo 1338988 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B4519529 : Blo 1338988 4519529 := bstep (se 2 (by rfl) ⟨1694823, by rfl⟩ : syracuseStep 4519529 = 3389647) B3389647
theorem B6436691 : Blo 1338988 6436691 := bstep (se 1 (by rfl) ⟨4827518, by rfl⟩ : syracuseStep 6436691 = 9655037) B9655037
theorem B34815035 : Blo 1338988 34815035 := bstep (se 1 (by rfl) ⟨26111276, by rfl⟩ : syracuseStep 34815035 = 52222553) B52222553
theorem B9174431 : Blo 1338988 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B5160431 : Blo 1338988 5160431 := bstep (se 1 (by rfl) ⟨3870323, by rfl⟩ : syracuseStep 5160431 = 7740647) B7740647
theorem B19570247 : Blo 1338988 19570247 := bstep (se 1 (by rfl) ⟨14677685, by rfl⟩ : syracuseStep 19570247 = 29355371) B29355371
theorem B4522877 : Blo 1338988 4522877 := bstep (se 3 (by rfl) ⟨848039, by rfl⟩ : syracuseStep 4522877 = 1696079) B1696079
theorem B3392543 : Blo 1338988 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B3016295 : Blo 1338988 3016295 := bstep (se 1 (by rfl) ⟨2262221, by rfl⟩ : syracuseStep 3016295 = 4524443) B4524443
theorem B3622607 : Blo 1338988 3622607 := bstep (se 1 (by rfl) ⟨2716955, by rfl⟩ : syracuseStep 3622607 = 5433911) B5433911
theorem B3016457 : Blo 1338988 3016457 := bstep (se 2 (by rfl) ⟨1131171, by rfl⟩ : syracuseStep 3016457 = 2262343) B2262343
theorem B3016511 : Blo 1338988 3016511 := bstep (se 1 (by rfl) ⟨2262383, by rfl⟩ : syracuseStep 3016511 = 4524767) B4524767
theorem B4523903 : Blo 1338988 4523903 := bstep (se 1 (by rfl) ⟨3392927, by rfl⟩ : syracuseStep 4523903 = 6785855) B6785855
theorem B104433623 : Blo 1338988 104433623 := bstep (se 1 (by rfl) ⟨78325217, by rfl⟩ : syracuseStep 104433623 = 156650435) B156650435
theorem B23210023 : Blo 1338988 23210023 := bstep (se 1 (by rfl) ⟨17407517, by rfl⟩ : syracuseStep 23210023 = 34815035) B34815035
theorem B4524713 : Blo 1338988 4524713 := bstep (se 2 (by rfl) ⟨1696767, by rfl⟩ : syracuseStep 4524713 = 3393535) B3393535
theorem B5721671 : Blo 1338988 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B24465149 : Blo 1338988 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B1339303 : Blo 1338988 1339303 := bstep (se 1 (by rfl) ⟨1004477, by rfl⟩ : syracuseStep 1339303 = 2008955) B2008955
theorem B97751929 : Blo 1338988 97751929 := bstep (se 2 (by rfl) ⟨36656973, by rfl⟩ : syracuseStep 97751929 = 73313947) B73313947
theorem B13046831 : Blo 1338988 13046831 := bstep (se 1 (by rfl) ⟨9785123, by rfl⟩ : syracuseStep 13046831 = 19570247) B19570247
theorem B7246921 : Blo 1338988 7246921 := bstep (se 2 (by rfl) ⟨2717595, by rfl⟩ : syracuseStep 7246921 = 5435191) B5435191
theorem B13743503 : Blo 1338988 13743503 := bstep (se 1 (by rfl) ⟨10307627, by rfl⟩ : syracuseStep 13743503 = 20615255) B20615255
theorem B27522947 : Blo 1338988 27522947 := bstep (se 1 (by rfl) ⟨20642210, by rfl⟩ : syracuseStep 27522947 = 41284421) B41284421
theorem B38606975 : Blo 1338988 38606975 := bstep (se 1 (by rfl) ⟨28955231, by rfl⟩ : syracuseStep 38606975 = 57910463) B57910463
theorem B3013019 : Blo 1338988 3013019 := bstep (se 1 (by rfl) ⟨2259764, by rfl⟩ : syracuseStep 3013019 = 4519529) B4519529
theorem B4291127 : Blo 1338988 4291127 := bstep (se 1 (by rfl) ⟨3218345, by rfl⟩ : syracuseStep 4291127 = 6436691) B6436691
theorem B15473267 : Blo 1338988 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B3218239 : Blo 1338988 3218239 := bstep (se 1 (by rfl) ⟨2413679, by rfl⟩ : syracuseStep 3218239 = 4827359) B4827359
theorem B28957999 : Blo 1338988 28957999 := bstep (se 1 (by rfl) ⟨21718499, by rfl⟩ : syracuseStep 28957999 = 43436999) B43436999
theorem B3440287 : Blo 1338988 3440287 := bstep (se 1 (by rfl) ⟨2580215, by rfl⟩ : syracuseStep 3440287 = 5160431) B5160431
theorem B1695487 : Blo 1338988 1695487 := bstep (se 1 (by rfl) ⟨1271615, by rfl⟩ : syracuseStep 1695487 = 2543231) B2543231
theorem B3015251 : Blo 1338988 3015251 := bstep (se 1 (by rfl) ⟨2261438, by rfl⟩ : syracuseStep 3015251 = 4522877) B4522877
theorem B2261695 : Blo 1338988 2261695 := bstep (se 1 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 2261695 = 3392543) B3392543
theorem B130335905 : Blo 1338988 130335905 := bstep (se 2 (by rfl) ⟨48875964, by rfl⟩ : syracuseStep 130335905 = 97751929) B97751929
theorem B3015935 : Blo 1338988 3015935 := bstep (se 1 (by rfl) ⟨2261951, by rfl⟩ : syracuseStep 3015935 = 4523903) B4523903
theorem B2008679 : Blo 1338988 2008679 := bstep (se 1 (by rfl) ⟨1506509, by rfl⟩ : syracuseStep 2008679 = 3013019) B3013019
theorem B2860751 : Blo 1338988 2860751 := bstep (se 1 (by rfl) ⟨2145563, by rfl⟩ : syracuseStep 2860751 = 4291127) B4291127
theorem B38610665 : Blo 1338988 38610665 := bstep (se 2 (by rfl) ⟨14478999, by rfl⟩ : syracuseStep 38610665 = 28957999) B28957999
theorem B10315511 : Blo 1338988 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B3016475 : Blo 1338988 3016475 := bstep (se 1 (by rfl) ⟨2262356, by rfl⟩ : syracuseStep 3016475 = 4524713) B4524713
theorem B73394525 : Blo 1338988 73394525 := bstep (se 3 (by rfl) ⟨13761473, by rfl⟩ : syracuseStep 73394525 = 27522947) B27522947
theorem B9162335 : Blo 1338988 9162335 := bstep (se 1 (by rfl) ⟨6871751, by rfl⟩ : syracuseStep 9162335 = 13743503) B13743503
theorem B2010863 : Blo 1338988 2010863 := bstep (se 1 (by rfl) ⟨1508147, by rfl⟩ : syracuseStep 2010863 = 3016295) B3016295
theorem B2010971 : Blo 1338988 2010971 := bstep (se 1 (by rfl) ⟨1508228, by rfl⟩ : syracuseStep 2010971 = 3016457) B3016457
theorem B2011007 : Blo 1338988 2011007 := bstep (se 1 (by rfl) ⟨1508255, by rfl⟩ : syracuseStep 2011007 = 3016511) B3016511
theorem B9662561 : Blo 1338988 9662561 := bstep (se 2 (by rfl) ⟨3623460, by rfl⟩ : syracuseStep 9662561 = 7246921) B7246921
theorem B3814447 : Blo 1338988 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B30946697 : Blo 1338988 30946697 := bstep (se 2 (by rfl) ⟨11605011, by rfl⟩ : syracuseStep 30946697 = 23210023) B23210023
theorem B8697887 : Blo 1338988 8697887 := bstep (se 1 (by rfl) ⟨6523415, by rfl⟩ : syracuseStep 8697887 = 13046831) B13046831
theorem B4290985 : Blo 1338988 4290985 := bstep (se 2 (by rfl) ⟨1609119, by rfl⟩ : syracuseStep 4290985 = 3218239) B3218239
theorem B2415071 : Blo 1338988 2415071 := bstep (se 1 (by rfl) ⟨1811303, by rfl⟩ : syracuseStep 2415071 = 3622607) B3622607
theorem B69622415 : Blo 1338988 69622415 := bstep (se 1 (by rfl) ⟨52216811, by rfl⟩ : syracuseStep 69622415 = 104433623) B104433623
theorem B25737983 : Blo 1338988 25737983 := bstep (se 1 (by rfl) ⟨19303487, by rfl⟩ : syracuseStep 25737983 = 38606975) B38606975
theorem B4587049 : Blo 1338988 4587049 := bstep (se 2 (by rfl) ⟨1720143, by rfl⟩ : syracuseStep 4587049 = 3440287) B3440287
theorem B2260649 : Blo 1338988 2260649 := bstep (se 2 (by rfl) ⟨847743, by rfl⟩ : syracuseStep 2260649 = 1695487) B1695487
theorem B16310099 : Blo 1338988 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B3015593 : Blo 1338988 3015593 := bstep (se 2 (by rfl) ⟨1130847, by rfl⟩ : syracuseStep 3015593 = 2261695) B2261695
theorem B25740443 : Blo 1338988 25740443 := bstep (se 1 (by rfl) ⟨19305332, by rfl⟩ : syracuseStep 25740443 = 38610665) B38610665
theorem B10873399 : Blo 1338988 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B6441707 : Blo 1338988 6441707 := bstep (se 1 (by rfl) ⟨4831280, by rfl⟩ : syracuseStep 6441707 = 9662561) B9662561
theorem B24464261 : Blo 1338988 24464261 := bstep (se 4 (by rfl) ⟨2293524, by rfl⟩ : syracuseStep 24464261 = 4587049) B4587049
theorem B2010167 : Blo 1338988 2010167 := bstep (se 1 (by rfl) ⟨1507625, by rfl⟩ : syracuseStep 2010167 = 3015251) B3015251
theorem B5721313 : Blo 1338988 5721313 := bstep (se 2 (by rfl) ⟨2145492, by rfl⟩ : syracuseStep 5721313 = 4290985) B4290985
theorem B2010623 : Blo 1338988 2010623 := bstep (se 1 (by rfl) ⟨1507967, by rfl⟩ : syracuseStep 2010623 = 3015935) B3015935
theorem B20631131 : Blo 1338988 20631131 := bstep (se 1 (by rfl) ⟨15473348, by rfl⟩ : syracuseStep 20631131 = 30946697) B30946697
theorem B1339119 : Blo 1338988 1339119 := bstep (se 1 (by rfl) ⟨1004339, by rfl⟩ : syracuseStep 1339119 = 2008679) B2008679
theorem B6877007 : Blo 1338988 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B2010983 : Blo 1338988 2010983 := bstep (se 1 (by rfl) ⟨1508237, by rfl⟩ : syracuseStep 2010983 = 3016475) B3016475
theorem B1610047 : Blo 1338988 1610047 := bstep (se 1 (by rfl) ⟨1207535, by rfl⟩ : syracuseStep 1610047 = 2415071) B2415071
theorem B17158655 : Blo 1338988 17158655 := bstep (se 1 (by rfl) ⟨12868991, by rfl⟩ : syracuseStep 17158655 = 25737983) B25737983
theorem B6108223 : Blo 1338988 6108223 := bstep (se 1 (by rfl) ⟨4581167, by rfl⟩ : syracuseStep 6108223 = 9162335) B9162335
theorem B1340575 : Blo 1338988 1340575 := bstep (se 1 (by rfl) ⟨1005431, by rfl⟩ : syracuseStep 1340575 = 2010863) B2010863
theorem B1340647 : Blo 1338988 1340647 := bstep (se 1 (by rfl) ⟨1005485, by rfl⟩ : syracuseStep 1340647 = 2010971) B2010971
theorem B1340671 : Blo 1338988 1340671 := bstep (se 1 (by rfl) ⟨1005503, by rfl⟩ : syracuseStep 1340671 = 2011007) B2011007
theorem B86890603 : Blo 1338988 86890603 := bstep (se 1 (by rfl) ⟨65167952, by rfl⟩ : syracuseStep 86890603 = 130335905) B130335905
theorem B1907167 : Blo 1338988 1907167 := bstep (se 1 (by rfl) ⟨1430375, by rfl⟩ : syracuseStep 1907167 = 2860751) B2860751
theorem B5798591 : Blo 1338988 5798591 := bstep (se 1 (by rfl) ⟨4348943, by rfl⟩ : syracuseStep 5798591 = 8697887) B8697887
theorem B5085929 : Blo 1338988 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B48929683 : Blo 1338988 48929683 := bstep (se 1 (by rfl) ⟨36697262, by rfl⟩ : syracuseStep 48929683 = 73394525) B73394525
theorem B46414943 : Blo 1338988 46414943 := bstep (se 1 (by rfl) ⟨34811207, by rfl⟩ : syracuseStep 46414943 = 69622415) B69622415
theorem B1507099 : Blo 1338988 1507099 := bstep (se 1 (by rfl) ⟨1130324, by rfl⟩ : syracuseStep 1507099 = 2260649) B2260649
theorem B2146729 : Blo 1338988 2146729 := bstep (se 2 (by rfl) ⟨805023, by rfl⟩ : syracuseStep 2146729 = 1610047) B1610047
theorem B8144297 : Blo 1338988 8144297 := bstep (se 2 (by rfl) ⟨3054111, by rfl⟩ : syracuseStep 8144297 = 6108223) B6108223
theorem B7628417 : Blo 1338988 7628417 := bstep (se 2 (by rfl) ⟨2860656, by rfl⟩ : syracuseStep 7628417 = 5721313) B5721313
theorem B4294471 : Blo 1338988 4294471 := bstep (se 1 (by rfl) ⟨3220853, by rfl⟩ : syracuseStep 4294471 = 6441707) B6441707
theorem B61851637 : Blo 1338988 61851637 := bstep (se 5 (by rfl) ⟨2899295, by rfl⟩ : syracuseStep 61851637 = 5798591) B5798591
theorem B30943295 : Blo 1338988 30943295 := bstep (se 1 (by rfl) ⟨23207471, by rfl⟩ : syracuseStep 30943295 = 46414943) B46414943
theorem B2009465 : Blo 1338988 2009465 := bstep (se 2 (by rfl) ⟨753549, by rfl⟩ : syracuseStep 2009465 = 1507099) B1507099
theorem B115854137 : Blo 1338988 115854137 := bstep (se 2 (by rfl) ⟨43445301, by rfl⟩ : syracuseStep 115854137 = 86890603) B86890603
theorem B11439103 : Blo 1338988 11439103 := bstep (se 1 (by rfl) ⟨8579327, by rfl⟩ : syracuseStep 11439103 = 17158655) B17158655
theorem B2010395 : Blo 1338988 2010395 := bstep (se 1 (by rfl) ⟨1507796, by rfl⟩ : syracuseStep 2010395 = 3015593) B3015593
theorem B2542889 : Blo 1338988 2542889 := bstep (se 2 (by rfl) ⟨953583, by rfl⟩ : syracuseStep 2542889 = 1907167) B1907167
theorem B1340111 : Blo 1338988 1340111 := bstep (se 1 (by rfl) ⟨1005083, by rfl⟩ : syracuseStep 1340111 = 2010167) B2010167
theorem B1340415 : Blo 1338988 1340415 := bstep (se 1 (by rfl) ⟨1005311, by rfl⟩ : syracuseStep 1340415 = 2010623) B2010623
theorem B4584671 : Blo 1338988 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B1340655 : Blo 1338988 1340655 := bstep (se 1 (by rfl) ⟨1005491, by rfl⟩ : syracuseStep 1340655 = 2010983) B2010983
theorem B14497865 : Blo 1338988 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B17160295 : Blo 1338988 17160295 := bstep (se 1 (by rfl) ⟨12870221, by rfl⟩ : syracuseStep 17160295 = 25740443) B25740443
theorem B65239577 : Blo 1338988 65239577 := bstep (se 2 (by rfl) ⟨24464841, by rfl⟩ : syracuseStep 65239577 = 48929683) B48929683
theorem B3390619 : Blo 1338988 3390619 := bstep (se 1 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 3390619 = 5085929) B5085929
theorem B16309507 : Blo 1338988 16309507 := bstep (se 1 (by rfl) ⟨12232130, by rfl⟩ : syracuseStep 16309507 = 24464261) B24464261
theorem B13754087 : Blo 1338988 13754087 := bstep (se 1 (by rfl) ⟨10315565, by rfl⟩ : syracuseStep 13754087 = 20631131) B20631131
theorem B22880393 : Blo 1338988 22880393 := bstep (se 2 (by rfl) ⟨8580147, by rfl⟩ : syracuseStep 22880393 = 17160295) B17160295
theorem B3056447 : Blo 1338988 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B20628863 : Blo 1338988 20628863 := bstep (se 1 (by rfl) ⟨15471647, by rfl⟩ : syracuseStep 20628863 = 30943295) B30943295
theorem B43493051 : Blo 1338988 43493051 := bstep (se 1 (by rfl) ⟨32619788, by rfl⟩ : syracuseStep 43493051 = 65239577) B65239577
theorem B77236091 : Blo 1338988 77236091 := bstep (se 1 (by rfl) ⟨57927068, by rfl⟩ : syracuseStep 77236091 = 115854137) B115854137
theorem B9169391 : Blo 1338988 9169391 := bstep (se 1 (by rfl) ⟨6877043, by rfl⟩ : syracuseStep 9169391 = 13754087) B13754087
theorem B2862305 : Blo 1338988 2862305 := bstep (se 2 (by rfl) ⟨1073364, by rfl⟩ : syracuseStep 2862305 = 2146729) B2146729
theorem B1339643 : Blo 1338988 1339643 := bstep (se 1 (by rfl) ⟨1004732, by rfl⟩ : syracuseStep 1339643 = 2009465) B2009465
theorem B21746009 : Blo 1338988 21746009 := bstep (se 2 (by rfl) ⟨8154753, by rfl⟩ : syracuseStep 21746009 = 16309507) B16309507
theorem B1340263 : Blo 1338988 1340263 := bstep (se 1 (by rfl) ⟨1005197, by rfl⟩ : syracuseStep 1340263 = 2010395) B2010395
theorem B5429531 : Blo 1338988 5429531 := bstep (se 1 (by rfl) ⟨4072148, by rfl⟩ : syracuseStep 5429531 = 8144297) B8144297
theorem B5085611 : Blo 1338988 5085611 := bstep (se 1 (by rfl) ⟨3814208, by rfl⟩ : syracuseStep 5085611 = 7628417) B7628417
theorem B15252137 : Blo 1338988 15252137 := bstep (se 2 (by rfl) ⟨5719551, by rfl⟩ : syracuseStep 15252137 = 11439103) B11439103
theorem B9665243 : Blo 1338988 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B4520825 : Blo 1338988 4520825 := bstep (se 2 (by rfl) ⟨1695309, by rfl⟩ : syracuseStep 4520825 = 3390619) B3390619
theorem B1695259 : Blo 1338988 1695259 := bstep (se 1 (by rfl) ⟨1271444, by rfl⟩ : syracuseStep 1695259 = 2542889) B2542889
theorem B5725961 : Blo 1338988 5725961 := bstep (se 2 (by rfl) ⟨2147235, by rfl⟩ : syracuseStep 5725961 = 4294471) B4294471
theorem B82468849 : Blo 1338988 82468849 := bstep (se 2 (by rfl) ⟨30925818, by rfl⟩ : syracuseStep 82468849 = 61851637) B61851637
theorem B15253595 : Blo 1338988 15253595 := bstep (se 1 (by rfl) ⟨11440196, by rfl⟩ : syracuseStep 15253595 = 22880393) B22880393
theorem B6112927 : Blo 1338988 6112927 := bstep (se 1 (by rfl) ⟨4584695, by rfl⟩ : syracuseStep 6112927 = 9169391) B9169391
theorem B10168091 : Blo 1338988 10168091 := bstep (se 1 (by rfl) ⟨7626068, by rfl⟩ : syracuseStep 10168091 = 15252137) B15252137
theorem B28995367 : Blo 1338988 28995367 := bstep (se 1 (by rfl) ⟨21746525, by rfl⟩ : syracuseStep 28995367 = 43493051) B43493051
theorem B51490727 : Blo 1338988 51490727 := bstep (se 1 (by rfl) ⟨38618045, by rfl⟩ : syracuseStep 51490727 = 77236091) B77236091
theorem B6443495 : Blo 1338988 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B109958465 : Blo 1338988 109958465 := bstep (se 2 (by rfl) ⟨41234424, by rfl⟩ : syracuseStep 109958465 = 82468849) B82468849
theorem B14497339 : Blo 1338988 14497339 := bstep (se 1 (by rfl) ⟨10873004, by rfl⟩ : syracuseStep 14497339 = 21746009) B21746009
theorem B2037631 : Blo 1338988 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B13752575 : Blo 1338988 13752575 := bstep (se 1 (by rfl) ⟨10314431, by rfl⟩ : syracuseStep 13752575 = 20628863) B20628863
theorem B3619687 : Blo 1338988 3619687 := bstep (se 1 (by rfl) ⟨2714765, by rfl⟩ : syracuseStep 3619687 = 5429531) B5429531
theorem B3390407 : Blo 1338988 3390407 := bstep (se 1 (by rfl) ⟨2542805, by rfl⟩ : syracuseStep 3390407 = 5085611) B5085611
theorem B3013883 : Blo 1338988 3013883 := bstep (se 1 (by rfl) ⟨2260412, by rfl⟩ : syracuseStep 3013883 = 4520825) B4520825
theorem B2260345 : Blo 1338988 2260345 := bstep (se 2 (by rfl) ⟨847629, by rfl⟩ : syracuseStep 2260345 = 1695259) B1695259
theorem B1908203 : Blo 1338988 1908203 := bstep (se 1 (by rfl) ⟨1431152, by rfl⟩ : syracuseStep 1908203 = 2862305) B2862305
theorem B3817307 : Blo 1338988 3817307 := bstep (se 1 (by rfl) ⟨2862980, by rfl⟩ : syracuseStep 3817307 = 5725961) B5725961
theorem B4826249 : Blo 1338988 4826249 := bstep (se 2 (by rfl) ⟨1809843, by rfl⟩ : syracuseStep 4826249 = 3619687) B3619687
theorem B5088541 : Blo 1338988 5088541 := bstep (se 3 (by rfl) ⟨954101, by rfl⟩ : syracuseStep 5088541 = 1908203) B1908203
theorem B9168383 : Blo 1338988 9168383 := bstep (se 1 (by rfl) ⟨6876287, by rfl⟩ : syracuseStep 9168383 = 13752575) B13752575
theorem B2009255 : Blo 1338988 2009255 := bstep (se 1 (by rfl) ⟨1506941, by rfl⟩ : syracuseStep 2009255 = 3013883) B3013883
theorem B38660489 : Blo 1338988 38660489 := bstep (se 2 (by rfl) ⟨14497683, by rfl⟩ : syracuseStep 38660489 = 28995367) B28995367
theorem B34327151 : Blo 1338988 34327151 := bstep (se 1 (by rfl) ⟨25745363, by rfl⟩ : syracuseStep 34327151 = 51490727) B51490727
theorem B10169063 : Blo 1338988 10169063 := bstep (se 1 (by rfl) ⟨7626797, by rfl⟩ : syracuseStep 10169063 = 15253595) B15253595
theorem B4295663 : Blo 1338988 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B73305643 : Blo 1338988 73305643 := bstep (se 1 (by rfl) ⟨54979232, by rfl⟩ : syracuseStep 73305643 = 109958465) B109958465
theorem B6778727 : Blo 1338988 6778727 := bstep (se 1 (by rfl) ⟨5084045, by rfl⟩ : syracuseStep 6778727 = 10168091) B10168091
theorem B19329785 : Blo 1338988 19329785 := bstep (se 2 (by rfl) ⟨7248669, by rfl⟩ : syracuseStep 19329785 = 14497339) B14497339
theorem B2716841 : Blo 1338988 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B2544871 : Blo 1338988 2544871 := bstep (se 1 (by rfl) ⟨1908653, by rfl⟩ : syracuseStep 2544871 = 3817307) B3817307
theorem B32602277 : Blo 1338988 32602277 := bstep (se 4 (by rfl) ⟨3056463, by rfl⟩ : syracuseStep 32602277 = 6112927) B6112927
theorem B3013793 : Blo 1338988 3013793 := bstep (se 2 (by rfl) ⟨1130172, by rfl⟩ : syracuseStep 3013793 = 2260345) B2260345
theorem B2260271 : Blo 1338988 2260271 := bstep (se 1 (by rfl) ⟨1695203, by rfl⟩ : syracuseStep 2260271 = 3390407) B3390407
theorem B12886523 : Blo 1338988 12886523 := bstep (se 1 (by rfl) ⟨9664892, by rfl⟩ : syracuseStep 12886523 = 19329785) B19329785
theorem B6112255 : Blo 1338988 6112255 := bstep (se 1 (by rfl) ⟨4584191, by rfl⟩ : syracuseStep 6112255 = 9168383) B9168383
theorem B21734851 : Blo 1338988 21734851 := bstep (se 1 (by rfl) ⟨16301138, by rfl⟩ : syracuseStep 21734851 = 32602277) B32602277
theorem B25773659 : Blo 1338988 25773659 := bstep (se 1 (by rfl) ⟨19330244, by rfl⟩ : syracuseStep 25773659 = 38660489) B38660489
theorem B3393161 : Blo 1338988 3393161 := bstep (se 2 (by rfl) ⟨1272435, by rfl⟩ : syracuseStep 3393161 = 2544871) B2544871
theorem B6784721 : Blo 1338988 6784721 := bstep (se 2 (by rfl) ⟨2544270, by rfl⟩ : syracuseStep 6784721 = 5088541) B5088541
theorem B97740857 : Blo 1338988 97740857 := bstep (se 2 (by rfl) ⟨36652821, by rfl⟩ : syracuseStep 97740857 = 73305643) B73305643
theorem B2009195 : Blo 1338988 2009195 := bstep (se 1 (by rfl) ⟨1506896, by rfl⟩ : syracuseStep 2009195 = 3013793) B3013793
theorem B7244909 : Blo 1338988 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B1339503 : Blo 1338988 1339503 := bstep (se 1 (by rfl) ⟨1004627, by rfl⟩ : syracuseStep 1339503 = 2009255) B2009255
theorem B22884767 : Blo 1338988 22884767 := bstep (se 1 (by rfl) ⟨17163575, by rfl⟩ : syracuseStep 22884767 = 34327151) B34327151
theorem B6779375 : Blo 1338988 6779375 := bstep (se 1 (by rfl) ⟨5084531, by rfl⟩ : syracuseStep 6779375 = 10169063) B10169063
theorem B2863775 : Blo 1338988 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B4519151 : Blo 1338988 4519151 := bstep (se 1 (by rfl) ⟨3389363, by rfl⟩ : syracuseStep 4519151 = 6778727) B6778727
theorem B3217499 : Blo 1338988 3217499 := bstep (se 1 (by rfl) ⟨2413124, by rfl⟩ : syracuseStep 3217499 = 4826249) B4826249
theorem B1506847 : Blo 1338988 1506847 := bstep (se 1 (by rfl) ⟨1130135, by rfl⟩ : syracuseStep 1506847 = 2260271) B2260271
theorem B1909183 : Blo 1338988 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B2262107 : Blo 1338988 2262107 := bstep (se 1 (by rfl) ⟨1696580, by rfl⟩ : syracuseStep 2262107 = 3393161) B3393161
theorem B4523147 : Blo 1338988 4523147 := bstep (se 1 (by rfl) ⟨3392360, by rfl⟩ : syracuseStep 4523147 = 6784721) B6784721
theorem B65160571 : Blo 1338988 65160571 := bstep (se 1 (by rfl) ⟨48870428, by rfl⟩ : syracuseStep 65160571 = 97740857) B97740857
theorem B2009129 : Blo 1338988 2009129 := bstep (se 2 (by rfl) ⟨753423, by rfl⟩ : syracuseStep 2009129 = 1506847) B1506847
theorem B15256511 : Blo 1338988 15256511 := bstep (se 1 (by rfl) ⟨11442383, by rfl⟩ : syracuseStep 15256511 = 22884767) B22884767
theorem B17182439 : Blo 1338988 17182439 := bstep (se 1 (by rfl) ⟨12886829, by rfl⟩ : syracuseStep 17182439 = 25773659) B25773659
theorem B1339463 : Blo 1338988 1339463 := bstep (se 1 (by rfl) ⟨1004597, by rfl⟩ : syracuseStep 1339463 = 2009195) B2009195
theorem B28979801 : Blo 1338988 28979801 := bstep (se 2 (by rfl) ⟨10867425, by rfl⟩ : syracuseStep 28979801 = 21734851) B21734851
theorem B4829939 : Blo 1338988 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B4519583 : Blo 1338988 4519583 := bstep (se 1 (by rfl) ⟨3389687, by rfl⟩ : syracuseStep 4519583 = 6779375) B6779375
theorem B8591015 : Blo 1338988 8591015 := bstep (se 1 (by rfl) ⟨6443261, by rfl⟩ : syracuseStep 8591015 = 12886523) B12886523
theorem B3012767 : Blo 1338988 3012767 := bstep (se 1 (by rfl) ⟨2259575, by rfl⟩ : syracuseStep 3012767 = 4519151) B4519151
theorem B8149673 : Blo 1338988 8149673 := bstep (se 2 (by rfl) ⟨3056127, by rfl⟩ : syracuseStep 8149673 = 6112255) B6112255
theorem B2144999 : Blo 1338988 2144999 := bstep (se 1 (by rfl) ⟨1608749, by rfl⟩ : syracuseStep 2144999 = 3217499) B3217499
theorem B3219959 : Blo 1338988 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B1508071 : Blo 1338988 1508071 := bstep (se 1 (by rfl) ⟨1131053, by rfl⟩ : syracuseStep 1508071 = 2262107) B2262107
theorem B3015431 : Blo 1338988 3015431 := bstep (se 1 (by rfl) ⟨2261573, by rfl⟩ : syracuseStep 3015431 = 4523147) B4523147
theorem B5727343 : Blo 1338988 5727343 := bstep (se 1 (by rfl) ⟨4295507, by rfl⟩ : syracuseStep 5727343 = 8591015) B8591015
theorem B2008511 : Blo 1338988 2008511 := bstep (se 1 (by rfl) ⟨1506383, by rfl⟩ : syracuseStep 2008511 = 3012767) B3012767
theorem B5719997 : Blo 1338988 5719997 := bstep (se 3 (by rfl) ⟨1072499, by rfl⟩ : syracuseStep 5719997 = 2144999) B2144999
theorem B11454959 : Blo 1338988 11454959 := bstep (se 1 (by rfl) ⟨8591219, by rfl⟩ : syracuseStep 11454959 = 17182439) B17182439
theorem B19319867 : Blo 1338988 19319867 := bstep (se 1 (by rfl) ⟨14489900, by rfl⟩ : syracuseStep 19319867 = 28979801) B28979801
theorem B1339419 : Blo 1338988 1339419 := bstep (se 1 (by rfl) ⟨1004564, by rfl⟩ : syracuseStep 1339419 = 2009129) B2009129
theorem B86880761 : Blo 1338988 86880761 := bstep (se 2 (by rfl) ⟨32580285, by rfl⟩ : syracuseStep 86880761 = 65160571) B65160571
theorem B10171007 : Blo 1338988 10171007 := bstep (se 1 (by rfl) ⟨7628255, by rfl⟩ : syracuseStep 10171007 = 15256511) B15256511
theorem B2545577 : Blo 1338988 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B3013055 : Blo 1338988 3013055 := bstep (se 1 (by rfl) ⟨2259791, by rfl⟩ : syracuseStep 3013055 = 4519583) B4519583
theorem B21732461 : Blo 1338988 21732461 := bstep (se 3 (by rfl) ⟨4074836, by rfl⟩ : syracuseStep 21732461 = 8149673) B8149673
theorem B1697051 : Blo 1338988 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B8586557 : Blo 1338988 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B7636457 : Blo 1338988 7636457 := bstep (se 2 (by rfl) ⟨2863671, by rfl⟩ : syracuseStep 7636457 = 5727343) B5727343
theorem B2008703 : Blo 1338988 2008703 := bstep (se 1 (by rfl) ⟨1506527, by rfl⟩ : syracuseStep 2008703 = 3013055) B3013055
theorem B7636639 : Blo 1338988 7636639 := bstep (se 1 (by rfl) ⟨5727479, by rfl⟩ : syracuseStep 7636639 = 11454959) B11454959
theorem B12879911 : Blo 1338988 12879911 := bstep (se 1 (by rfl) ⟨9659933, by rfl⟩ : syracuseStep 12879911 = 19319867) B19319867
theorem B57920507 : Blo 1338988 57920507 := bstep (se 1 (by rfl) ⟨43440380, by rfl⟩ : syracuseStep 57920507 = 86880761) B86880761
theorem B2010287 : Blo 1338988 2010287 := bstep (se 1 (by rfl) ⟨1507715, by rfl⟩ : syracuseStep 2010287 = 3015431) B3015431
theorem B1339007 : Blo 1338988 1339007 := bstep (se 1 (by rfl) ⟨1004255, by rfl⟩ : syracuseStep 1339007 = 2008511) B2008511
theorem B2010761 : Blo 1338988 2010761 := bstep (se 2 (by rfl) ⟨754035, by rfl⟩ : syracuseStep 2010761 = 1508071) B1508071
theorem B3813331 : Blo 1338988 3813331 := bstep (se 1 (by rfl) ⟨2859998, by rfl⟩ : syracuseStep 3813331 = 5719997) B5719997
theorem B14488307 : Blo 1338988 14488307 := bstep (se 1 (by rfl) ⟨10866230, by rfl⟩ : syracuseStep 14488307 = 21732461) B21732461
theorem B6780671 : Blo 1338988 6780671 := bstep (se 1 (by rfl) ⟨5085503, by rfl⟩ : syracuseStep 6780671 = 10171007) B10171007
theorem B9658871 : Blo 1338988 9658871 := bstep (se 1 (by rfl) ⟨7244153, by rfl⟩ : syracuseStep 9658871 = 14488307) B14488307
theorem B8586607 : Blo 1338988 8586607 := bstep (se 1 (by rfl) ⟨6439955, by rfl⟩ : syracuseStep 8586607 = 12879911) B12879911
theorem B4525469 : Blo 1338988 4525469 := bstep (se 3 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 4525469 = 1697051) B1697051
theorem B5090971 : Blo 1338988 5090971 := bstep (se 1 (by rfl) ⟨3818228, by rfl⟩ : syracuseStep 5090971 = 7636457) B7636457
theorem B1339135 : Blo 1338988 1339135 := bstep (se 1 (by rfl) ⟨1004351, by rfl⟩ : syracuseStep 1339135 = 2008703) B2008703
theorem B38613671 : Blo 1338988 38613671 := bstep (se 1 (by rfl) ⟨28960253, by rfl⟩ : syracuseStep 38613671 = 57920507) B57920507
theorem B1340191 : Blo 1338988 1340191 := bstep (se 1 (by rfl) ⟨1005143, by rfl⟩ : syracuseStep 1340191 = 2010287) B2010287
theorem B1340507 : Blo 1338988 1340507 := bstep (se 1 (by rfl) ⟨1005380, by rfl⟩ : syracuseStep 1340507 = 2010761) B2010761
theorem B5084441 : Blo 1338988 5084441 := bstep (se 2 (by rfl) ⟨1906665, by rfl⟩ : syracuseStep 5084441 = 3813331) B3813331
theorem B5724371 : Blo 1338988 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B4520447 : Blo 1338988 4520447 := bstep (se 1 (by rfl) ⟨3390335, by rfl⟩ : syracuseStep 4520447 = 6780671) B6780671
theorem B10182185 : Blo 1338988 10182185 := bstep (se 2 (by rfl) ⟨3818319, by rfl⟩ : syracuseStep 10182185 = 7636639) B7636639
theorem B6439247 : Blo 1338988 6439247 := bstep (se 1 (by rfl) ⟨4829435, by rfl⟩ : syracuseStep 6439247 = 9658871) B9658871
theorem B3016979 : Blo 1338988 3016979 := bstep (se 1 (by rfl) ⟨2262734, by rfl⟩ : syracuseStep 3016979 = 4525469) B4525469
theorem B25742447 : Blo 1338988 25742447 := bstep (se 1 (by rfl) ⟨19306835, by rfl⟩ : syracuseStep 25742447 = 38613671) B38613671
theorem B11448809 : Blo 1338988 11448809 := bstep (se 2 (by rfl) ⟨4293303, by rfl⟩ : syracuseStep 11448809 = 8586607) B8586607
theorem B6787961 : Blo 1338988 6787961 := bstep (se 2 (by rfl) ⟨2545485, by rfl⟩ : syracuseStep 6787961 = 5090971) B5090971
theorem B6788123 : Blo 1338988 6788123 := bstep (se 1 (by rfl) ⟨5091092, by rfl⟩ : syracuseStep 6788123 = 10182185) B10182185
theorem B3389627 : Blo 1338988 3389627 := bstep (se 1 (by rfl) ⟨2542220, by rfl⟩ : syracuseStep 3389627 = 5084441) B5084441
theorem B3816247 : Blo 1338988 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B3013631 : Blo 1338988 3013631 := bstep (se 1 (by rfl) ⟨2260223, by rfl⟩ : syracuseStep 3013631 = 4520447) B4520447
theorem B4292831 : Blo 1338988 4292831 := bstep (se 1 (by rfl) ⟨3219623, by rfl⟩ : syracuseStep 4292831 = 6439247) B6439247
theorem B5088329 : Blo 1338988 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B2009087 : Blo 1338988 2009087 := bstep (se 1 (by rfl) ⟨1506815, by rfl⟩ : syracuseStep 2009087 = 3013631) B3013631
theorem B4525307 : Blo 1338988 4525307 := bstep (se 1 (by rfl) ⟨3393980, by rfl⟩ : syracuseStep 4525307 = 6787961) B6787961
theorem B4525415 : Blo 1338988 4525415 := bstep (se 1 (by rfl) ⟨3394061, by rfl⟩ : syracuseStep 4525415 = 6788123) B6788123
theorem B2011319 : Blo 1338988 2011319 := bstep (se 1 (by rfl) ⟨1508489, by rfl⟩ : syracuseStep 2011319 = 3016979) B3016979
theorem B7632539 : Blo 1338988 7632539 := bstep (se 1 (by rfl) ⟨5724404, by rfl⟩ : syracuseStep 7632539 = 11448809) B11448809
theorem B2259751 : Blo 1338988 2259751 := bstep (se 1 (by rfl) ⟨1694813, by rfl⟩ : syracuseStep 2259751 = 3389627) B3389627
theorem B17161631 : Blo 1338988 17161631 := bstep (se 1 (by rfl) ⟨12871223, by rfl⟩ : syracuseStep 17161631 = 25742447) B25742447
theorem B3392219 : Blo 1338988 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B5088359 : Blo 1338988 5088359 := bstep (se 1 (by rfl) ⟨3816269, by rfl⟩ : syracuseStep 5088359 = 7632539) B7632539
theorem B3016871 : Blo 1338988 3016871 := bstep (se 1 (by rfl) ⟨2262653, by rfl⟩ : syracuseStep 3016871 = 4525307) B4525307
theorem B3016943 : Blo 1338988 3016943 := bstep (se 1 (by rfl) ⟨2262707, by rfl⟩ : syracuseStep 3016943 = 4525415) B4525415
theorem B2861887 : Blo 1338988 2861887 := bstep (se 1 (by rfl) ⟨2146415, by rfl⟩ : syracuseStep 2861887 = 4292831) B4292831
theorem B1339391 : Blo 1338988 1339391 := bstep (se 1 (by rfl) ⟨1004543, by rfl⟩ : syracuseStep 1339391 = 2009087) B2009087
theorem B11441087 : Blo 1338988 11441087 := bstep (se 1 (by rfl) ⟨8580815, by rfl⟩ : syracuseStep 11441087 = 17161631) B17161631
theorem B1340879 : Blo 1338988 1340879 := bstep (se 1 (by rfl) ⟨1005659, by rfl⟩ : syracuseStep 1340879 = 2011319) B2011319
theorem B3013001 : Blo 1338988 3013001 := bstep (se 2 (by rfl) ⟨1129875, by rfl⟩ : syracuseStep 3013001 = 2259751) B2259751
theorem B2261479 : Blo 1338988 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B7627391 : Blo 1338988 7627391 := bstep (se 1 (by rfl) ⟨5720543, by rfl⟩ : syracuseStep 7627391 = 11441087) B11441087
theorem B3392239 : Blo 1338988 3392239 := bstep (se 1 (by rfl) ⟨2544179, by rfl⟩ : syracuseStep 3392239 = 5088359) B5088359
theorem B2008667 : Blo 1338988 2008667 := bstep (se 1 (by rfl) ⟨1506500, by rfl⟩ : syracuseStep 2008667 = 3013001) B3013001
theorem B2011247 : Blo 1338988 2011247 := bstep (se 1 (by rfl) ⟨1508435, by rfl⟩ : syracuseStep 2011247 = 3016871) B3016871
theorem B2011295 : Blo 1338988 2011295 := bstep (se 1 (by rfl) ⟨1508471, by rfl⟩ : syracuseStep 2011295 = 3016943) B3016943
theorem B3815849 : Blo 1338988 3815849 := bstep (se 2 (by rfl) ⟨1430943, by rfl⟩ : syracuseStep 3815849 = 2861887) B2861887
theorem B3015305 : Blo 1338988 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B4522985 : Blo 1338988 4522985 := bstep (se 2 (by rfl) ⟨1696119, by rfl⟩ : syracuseStep 4522985 = 3392239) B3392239
theorem B1339111 : Blo 1338988 1339111 := bstep (se 1 (by rfl) ⟨1004333, by rfl⟩ : syracuseStep 1339111 = 2008667) B2008667
theorem B2543899 : Blo 1338988 2543899 := bstep (se 1 (by rfl) ⟨1907924, by rfl⟩ : syracuseStep 2543899 = 3815849) B3815849
theorem B1340831 : Blo 1338988 1340831 := bstep (se 1 (by rfl) ⟨1005623, by rfl⟩ : syracuseStep 1340831 = 2011247) B2011247
theorem B1340863 : Blo 1338988 1340863 := bstep (se 1 (by rfl) ⟨1005647, by rfl⟩ : syracuseStep 1340863 = 2011295) B2011295
theorem B5084927 : Blo 1338988 5084927 := bstep (se 1 (by rfl) ⟨3813695, by rfl⟩ : syracuseStep 5084927 = 7627391) B7627391
theorem B3391865 : Blo 1338988 3391865 := bstep (se 2 (by rfl) ⟨1271949, by rfl⟩ : syracuseStep 3391865 = 2543899) B2543899
theorem B3015323 : Blo 1338988 3015323 := bstep (se 1 (by rfl) ⟨2261492, by rfl⟩ : syracuseStep 3015323 = 4522985) B4522985
theorem B2010203 : Blo 1338988 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B3389951 : Blo 1338988 3389951 := bstep (se 1 (by rfl) ⟨2542463, by rfl⟩ : syracuseStep 3389951 = 5084927) B5084927
theorem B2261243 : Blo 1338988 2261243 := bstep (se 1 (by rfl) ⟨1695932, by rfl⟩ : syracuseStep 2261243 = 3391865) B3391865
theorem B2010215 : Blo 1338988 2010215 := bstep (se 1 (by rfl) ⟨1507661, by rfl⟩ : syracuseStep 2010215 = 3015323) B3015323
theorem B1340135 : Blo 1338988 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B2259967 : Blo 1338988 2259967 := bstep (se 1 (by rfl) ⟨1694975, by rfl⟩ : syracuseStep 2259967 = 3389951) B3389951
theorem B1507495 : Blo 1338988 1507495 := bstep (se 1 (by rfl) ⟨1130621, by rfl⟩ : syracuseStep 1507495 = 2261243) B2261243
theorem B1340143 : Blo 1338988 1340143 := bstep (se 1 (by rfl) ⟨1005107, by rfl⟩ : syracuseStep 1340143 = 2010215) B2010215
theorem B3013289 : Blo 1338988 3013289 := bstep (se 2 (by rfl) ⟨1129983, by rfl⟩ : syracuseStep 3013289 = 2259967) B2259967
theorem B2008859 : Blo 1338988 2008859 := bstep (se 1 (by rfl) ⟨1506644, by rfl⟩ : syracuseStep 2008859 = 3013289) B3013289
theorem B2009993 : Blo 1338988 2009993 := bstep (se 2 (by rfl) ⟨753747, by rfl⟩ : syracuseStep 2009993 = 1507495) B1507495
theorem B1339239 : Blo 1338988 1339239 := bstep (se 1 (by rfl) ⟨1004429, by rfl⟩ : syracuseStep 1339239 = 2008859) B2008859
theorem B1339995 : Blo 1338988 1339995 := bstep (se 1 (by rfl) ⟨1004996, by rfl⟩ : syracuseStep 1339995 = 2009993) B2009993

theorem C0 (j : ℕ) (h1 : 334747 ≤ j) (h2 : j ≤ 335246) : Blo 1338988 (4 * j + 3) := by
  interval_cases j
  · exact B1338991
  · exact B1338995
  · exact B1338999
  · exact B1339003
  · exact B1339007
  · exact B1339011
  · exact B1339015
  · exact B1339019
  · exact B1339023
  · exact B1339027
  · exact B1339031
  · exact B1339035
  · exact B1339039
  · exact B1339043
  · exact B1339047
  · exact B1339051
  · exact B1339055
  · exact B1339059
  · exact B1339063
  · exact B1339067
  · exact B1339071
  · exact B1339075
  · exact B1339079
  · exact B1339083
  · exact B1339087
  · exact B1339091
  · exact B1339095
  · exact B1339099
  · exact B1339103
  · exact B1339107
  · exact B1339111
  · exact B1339115
  · exact B1339119
  · exact B1339123
  · exact B1339127
  · exact B1339131
  · exact B1339135
  · exact B1339139
  · exact B1339143
  · exact B1339147
  · exact B1339151
  · exact B1339155
  · exact B1339159
  · exact B1339163
  · exact B1339167
  · exact B1339171
  · exact B1339175
  · exact B1339179
  · exact B1339183
  · exact B1339187
  · exact B1339191
  · exact B1339195
  · exact B1339199
  · exact B1339203
  · exact B1339207
  · exact B1339211
  · exact B1339215
  · exact B1339219
  · exact B1339223
  · exact B1339227
  · exact B1339231
  · exact B1339235
  · exact B1339239
  · exact B1339243
  · exact B1339247
  · exact B1339251
  · exact B1339255
  · exact B1339259
  · exact B1339263
  · exact B1339267
  · exact B1339271
  · exact B1339275
  · exact B1339279
  · exact B1339283
  · exact B1339287
  · exact B1339291
  · exact B1339295
  · exact B1339299
  · exact B1339303
  · exact B1339307
  · exact B1339311
  · exact B1339315
  · exact B1339319
  · exact B1339323
  · exact B1339327
  · exact B1339331
  · exact B1339335
  · exact B1339339
  · exact B1339343
  · exact B1339347
  · exact B1339351
  · exact B1339355
  · exact B1339359
  · exact B1339363
  · exact B1339367
  · exact B1339371
  · exact B1339375
  · exact B1339379
  · exact B1339383
  · exact B1339387
  · exact B1339391
  · exact B1339395
  · exact B1339399
  · exact B1339403
  · exact B1339407
  · exact B1339411
  · exact B1339415
  · exact B1339419
  · exact B1339423
  · exact B1339427
  · exact B1339431
  · exact B1339435
  · exact B1339439
  · exact B1339443
  · exact B1339447
  · exact B1339451
  · exact B1339455
  · exact B1339459
  · exact B1339463
  · exact B1339467
  · exact B1339471
  · exact B1339475
  · exact B1339479
  · exact B1339483
  · exact B1339487
  · exact B1339491
  · exact B1339495
  · exact B1339499
  · exact B1339503
  · exact B1339507
  · exact B1339511
  · exact B1339515
  · exact B1339519
  · exact B1339523
  · exact B1339527
  · exact B1339531
  · exact B1339535
  · exact B1339539
  · exact B1339543
  · exact B1339547
  · exact B1339551
  · exact B1339555
  · exact B1339559
  · exact B1339563
  · exact B1339567
  · exact B1339571
  · exact B1339575
  · exact B1339579
  · exact B1339583
  · exact B1339587
  · exact B1339591
  · exact B1339595
  · exact B1339599
  · exact B1339603
  · exact B1339607
  · exact B1339611
  · exact B1339615
  · exact B1339619
  · exact B1339623
  · exact B1339627
  · exact B1339631
  · exact B1339635
  · exact B1339639
  · exact B1339643
  · exact B1339647
  · exact B1339651
  · exact B1339655
  · exact B1339659
  · exact B1339663
  · exact B1339667
  · exact B1339671
  · exact B1339675
  · exact B1339679
  · exact B1339683
  · exact B1339687
  · exact B1339691
  · exact B1339695
  · exact B1339699
  · exact B1339703
  · exact B1339707
  · exact B1339711
  · exact B1339715
  · exact B1339719
  · exact B1339723
  · exact B1339727
  · exact B1339731
  · exact B1339735
  · exact B1339739
  · exact B1339743
  · exact B1339747
  · exact B1339751
  · exact B1339755
  · exact B1339759
  · exact B1339763
  · exact B1339767
  · exact B1339771
  · exact B1339775
  · exact B1339779
  · exact B1339783
  · exact B1339787
  · exact B1339791
  · exact B1339795
  · exact B1339799
  · exact B1339803
  · exact B1339807
  · exact B1339811
  · exact B1339815
  · exact B1339819
  · exact B1339823
  · exact B1339827
  · exact B1339831
  · exact B1339835
  · exact B1339839
  · exact B1339843
  · exact B1339847
  · exact B1339851
  · exact B1339855
  · exact B1339859
  · exact B1339863
  · exact B1339867
  · exact B1339871
  · exact B1339875
  · exact B1339879
  · exact B1339883
  · exact B1339887
  · exact B1339891
  · exact B1339895
  · exact B1339899
  · exact B1339903
  · exact B1339907
  · exact B1339911
  · exact B1339915
  · exact B1339919
  · exact B1339923
  · exact B1339927
  · exact B1339931
  · exact B1339935
  · exact B1339939
  · exact B1339943
  · exact B1339947
  · exact B1339951
  · exact B1339955
  · exact B1339959
  · exact B1339963
  · exact B1339967
  · exact B1339971
  · exact B1339975
  · exact B1339979
  · exact B1339983
  · exact B1339987
  · exact B1339991
  · exact B1339995
  · exact B1339999
  · exact B1340003
  · exact B1340007
  · exact B1340011
  · exact B1340015
  · exact B1340019
  · exact B1340023
  · exact B1340027
  · exact B1340031
  · exact B1340035
  · exact B1340039
  · exact B1340043
  · exact B1340047
  · exact B1340051
  · exact B1340055
  · exact B1340059
  · exact B1340063
  · exact B1340067
  · exact B1340071
  · exact B1340075
  · exact B1340079
  · exact B1340083
  · exact B1340087
  · exact B1340091
  · exact B1340095
  · exact B1340099
  · exact B1340103
  · exact B1340107
  · exact B1340111
  · exact B1340115
  · exact B1340119
  · exact B1340123
  · exact B1340127
  · exact B1340131
  · exact B1340135
  · exact B1340139
  · exact B1340143
  · exact B1340147
  · exact B1340151
  · exact B1340155
  · exact B1340159
  · exact B1340163
  · exact B1340167
  · exact B1340171
  · exact B1340175
  · exact B1340179
  · exact B1340183
  · exact B1340187
  · exact B1340191
  · exact B1340195
  · exact B1340199
  · exact B1340203
  · exact B1340207
  · exact B1340211
  · exact B1340215
  · exact B1340219
  · exact B1340223
  · exact B1340227
  · exact B1340231
  · exact B1340235
  · exact B1340239
  · exact B1340243
  · exact B1340247
  · exact B1340251
  · exact B1340255
  · exact B1340259
  · exact B1340263
  · exact B1340267
  · exact B1340271
  · exact B1340275
  · exact B1340279
  · exact B1340283
  · exact B1340287
  · exact B1340291
  · exact B1340295
  · exact B1340299
  · exact B1340303
  · exact B1340307
  · exact B1340311
  · exact B1340315
  · exact B1340319
  · exact B1340323
  · exact B1340327
  · exact B1340331
  · exact B1340335
  · exact B1340339
  · exact B1340343
  · exact B1340347
  · exact B1340351
  · exact B1340355
  · exact B1340359
  · exact B1340363
  · exact B1340367
  · exact B1340371
  · exact B1340375
  · exact B1340379
  · exact B1340383
  · exact B1340387
  · exact B1340391
  · exact B1340395
  · exact B1340399
  · exact B1340403
  · exact B1340407
  · exact B1340411
  · exact B1340415
  · exact B1340419
  · exact B1340423
  · exact B1340427
  · exact B1340431
  · exact B1340435
  · exact B1340439
  · exact B1340443
  · exact B1340447
  · exact B1340451
  · exact B1340455
  · exact B1340459
  · exact B1340463
  · exact B1340467
  · exact B1340471
  · exact B1340475
  · exact B1340479
  · exact B1340483
  · exact B1340487
  · exact B1340491
  · exact B1340495
  · exact B1340499
  · exact B1340503
  · exact B1340507
  · exact B1340511
  · exact B1340515
  · exact B1340519
  · exact B1340523
  · exact B1340527
  · exact B1340531
  · exact B1340535
  · exact B1340539
  · exact B1340543
  · exact B1340547
  · exact B1340551
  · exact B1340555
  · exact B1340559
  · exact B1340563
  · exact B1340567
  · exact B1340571
  · exact B1340575
  · exact B1340579
  · exact B1340583
  · exact B1340587
  · exact B1340591
  · exact B1340595
  · exact B1340599
  · exact B1340603
  · exact B1340607
  · exact B1340611
  · exact B1340615
  · exact B1340619
  · exact B1340623
  · exact B1340627
  · exact B1340631
  · exact B1340635
  · exact B1340639
  · exact B1340643
  · exact B1340647
  · exact B1340651
  · exact B1340655
  · exact B1340659
  · exact B1340663
  · exact B1340667
  · exact B1340671
  · exact B1340675
  · exact B1340679
  · exact B1340683
  · exact B1340687
  · exact B1340691
  · exact B1340695
  · exact B1340699
  · exact B1340703
  · exact B1340707
  · exact B1340711
  · exact B1340715
  · exact B1340719
  · exact B1340723
  · exact B1340727
  · exact B1340731
  · exact B1340735
  · exact B1340739
  · exact B1340743
  · exact B1340747
  · exact B1340751
  · exact B1340755
  · exact B1340759
  · exact B1340763
  · exact B1340767
  · exact B1340771
  · exact B1340775
  · exact B1340779
  · exact B1340783
  · exact B1340787
  · exact B1340791
  · exact B1340795
  · exact B1340799
  · exact B1340803
  · exact B1340807
  · exact B1340811
  · exact B1340815
  · exact B1340819
  · exact B1340823
  · exact B1340827
  · exact B1340831
  · exact B1340835
  · exact B1340839
  · exact B1340843
  · exact B1340847
  · exact B1340851
  · exact B1340855
  · exact B1340859
  · exact B1340863
  · exact B1340867
  · exact B1340871
  · exact B1340875
  · exact B1340879
  · exact B1340883
  · exact B1340887
  · exact B1340891
  · exact B1340895
  · exact B1340899
  · exact B1340903
  · exact B1340907
  · exact B1340911
  · exact B1340915
  · exact B1340919
  · exact B1340923
  · exact B1340927
  · exact B1340931
  · exact B1340935
  · exact B1340939
  · exact B1340943
  · exact B1340947
  · exact B1340951
  · exact B1340955
  · exact B1340959
  · exact B1340963
  · exact B1340967
  · exact B1340971
  · exact B1340975
  · exact B1340979
  · exact B1340983
  · exact B1340987

theorem solution (m : ℕ) (hlo : 1338988 ≤ m) (hhi : m ≤ 1340988) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 334747 ≤ j := by omega
    have hj2 : j ≤ 335246 := by omega
    have hb : Blo 1338988 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
