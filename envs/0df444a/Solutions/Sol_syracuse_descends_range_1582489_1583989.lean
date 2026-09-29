-- Prove2me | solution 1 for syracuse_descends_range_1582489_1583989
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:07:58.934273+00:00
-- url     : https://prove2.me/submissions/54be4f5f-a233-41cb-b530-2faaaf2c286c

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


theorem B2375693 : Blo 1582489 2375693 := bbase (se 3 (by rfl) ⟨445442, by rfl⟩ : syracuseStep 2375693 = 890885) (by norm_num)
theorem B3563549 : Blo 1582489 3563549 := bbase (se 3 (by rfl) ⟨668165, by rfl⟩ : syracuseStep 3563549 = 1336331) (by norm_num)
theorem B2375717 : Blo 1582489 2375717 := bbase (se 4 (by rfl) ⟨222723, by rfl⟩ : syracuseStep 2375717 = 445447) (by norm_num)
theorem B2670637 : Blo 1582489 2670637 := bbase (se 3 (by rfl) ⟨500744, by rfl⟩ : syracuseStep 2670637 = 1001489) (by norm_num)
theorem B2375741 : Blo 1582489 2375741 := bbase (se 3 (by rfl) ⟨445451, by rfl⟩ : syracuseStep 2375741 = 890903) (by norm_num)
theorem B3006533 : Blo 1582489 3006533 := bbase (se 4 (by rfl) ⟨281862, by rfl⟩ : syracuseStep 3006533 = 563725) (by norm_num)
theorem B2375765 : Blo 1582489 2375765 := bbase (se 8 (by rfl) ⟨13920, by rfl⟩ : syracuseStep 2375765 = 27841) (by norm_num)
theorem B3563621 : Blo 1582489 3563621 := bbase (se 4 (by rfl) ⟨334089, by rfl⟩ : syracuseStep 3563621 = 668179) (by norm_num)
theorem B2375789 : Blo 1582489 2375789 := bbase (se 3 (by rfl) ⟨445460, by rfl⟩ : syracuseStep 2375789 = 890921) (by norm_num)
theorem B5341301 : Blo 1582489 5341301 := bbase (se 5 (by rfl) ⟨250373, by rfl⟩ : syracuseStep 5341301 = 500747) (by norm_num)
theorem B2670725 : Blo 1582489 2670725 := bbase (se 4 (by rfl) ⟨250380, by rfl⟩ : syracuseStep 2670725 = 500761) (by norm_num)
theorem B2375813 : Blo 1582489 2375813 := bbase (se 4 (by rfl) ⟨222732, by rfl⟩ : syracuseStep 2375813 = 445465) (by norm_num)
theorem B4006037 : Blo 1582489 4006037 := bbase (se 6 (by rfl) ⟨93891, by rfl⟩ : syracuseStep 4006037 = 187783) (by norm_num)
theorem B2375837 : Blo 1582489 2375837 := bbase (se 3 (by rfl) ⟨445469, by rfl⟩ : syracuseStep 2375837 = 890939) (by norm_num)
theorem B3563693 : Blo 1582489 3563693 := bbase (se 3 (by rfl) ⟨668192, by rfl⟩ : syracuseStep 3563693 = 1336385) (by norm_num)
theorem B2375861 : Blo 1582489 2375861 := bbase (se 5 (by rfl) ⟨111368, by rfl⟩ : syracuseStep 2375861 = 222737) (by norm_num)
theorem B2375885 : Blo 1582489 2375885 := bbase (se 3 (by rfl) ⟨445478, by rfl⟩ : syracuseStep 2375885 = 890957) (by norm_num)
theorem B12026069 : Blo 1582489 12026069 := bbase (se 7 (by rfl) ⟨140930, by rfl⟩ : syracuseStep 12026069 = 281861) (by norm_num)
theorem B2375909 : Blo 1582489 2375909 := bbase (se 4 (by rfl) ⟨222741, by rfl⟩ : syracuseStep 2375909 = 445483) (by norm_num)
theorem B3563765 : Blo 1582489 3563765 := bbase (se 5 (by rfl) ⟨167051, by rfl⟩ : syracuseStep 3563765 = 334103) (by norm_num)
theorem B2375933 : Blo 1582489 2375933 := bbase (se 3 (by rfl) ⟨445487, by rfl⟩ : syracuseStep 2375933 = 890975) (by norm_num)
theorem B2670853 : Blo 1582489 2670853 := bbase (se 4 (by rfl) ⟨250392, by rfl⟩ : syracuseStep 2670853 = 500785) (by norm_num)
theorem B2892037 : Blo 1582489 2892037 := bbase (se 4 (by rfl) ⟨271128, by rfl⟩ : syracuseStep 2892037 = 542257) (by norm_num)
theorem B2031877 : Blo 1582489 2031877 := bbase (se 4 (by rfl) ⟨190488, by rfl⟩ : syracuseStep 2031877 = 380977) (by norm_num)
theorem B2375957 : Blo 1582489 2375957 := bbase (se 6 (by rfl) ⟨55686, by rfl⟩ : syracuseStep 2375957 = 111373) (by norm_num)
theorem B2375981 : Blo 1582489 2375981 := bbase (se 3 (by rfl) ⟨445496, by rfl⟩ : syracuseStep 2375981 = 890993) (by norm_num)
theorem B3563837 : Blo 1582489 3563837 := bbase (se 3 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 3563837 = 1336439) (by norm_num)
theorem B2670941 : Blo 1582489 2670941 := bbase (se 3 (by rfl) ⟨500801, by rfl⟩ : syracuseStep 2670941 = 1001603) (by norm_num)
theorem B3006821 : Blo 1582489 3006821 := bbase (se 4 (by rfl) ⟨281889, by rfl⟩ : syracuseStep 3006821 = 563779) (by norm_num)
theorem B3563909 : Blo 1582489 3563909 := bbase (se 4 (by rfl) ⟨334116, by rfl⟩ : syracuseStep 3563909 = 668233) (by norm_num)
theorem B2253197 : Blo 1582489 2253197 := bbase (se 3 (by rfl) ⟨422474, by rfl⟩ : syracuseStep 2253197 = 844949) (by norm_num)
theorem B2605493 : Blo 1582489 2605493 := bbase (se 5 (by rfl) ⟨122132, by rfl⟩ : syracuseStep 2605493 = 244265) (by norm_num)
theorem B3047861 : Blo 1582489 3047861 := bbase (se 5 (by rfl) ⟨142868, by rfl⟩ : syracuseStep 3047861 = 285737) (by norm_num)
theorem B2671069 : Blo 1582489 2671069 := bbase (se 3 (by rfl) ⟨500825, by rfl⟩ : syracuseStep 2671069 = 1001651) (by norm_num)
theorem B4006381 : Blo 1582489 4006381 := bbase (se 3 (by rfl) ⟨751196, by rfl⟩ : syracuseStep 4006381 = 1502393) (by norm_num)
theorem B3006973 : Blo 1582489 3006973 := bbase (se 3 (by rfl) ⟨563807, by rfl⟩ : syracuseStep 3006973 = 1127615) (by norm_num)
theorem B6857237 : Blo 1582489 6857237 := bbase (se 6 (by rfl) ⟨160716, by rfl⟩ : syracuseStep 6857237 = 321433) (by norm_num)
theorem B5341733 : Blo 1582489 5341733 := bbase (se 4 (by rfl) ⟨500787, by rfl⟩ : syracuseStep 5341733 = 1001575) (by norm_num)
theorem B2671157 : Blo 1582489 2671157 := bbase (se 5 (by rfl) ⟨125210, by rfl⟩ : syracuseStep 2671157 = 250421) (by norm_num)
theorem B8012357 : Blo 1582489 8012357 := bbase (se 4 (by rfl) ⟨751158, by rfl⟩ : syracuseStep 8012357 = 1502317) (by norm_num)
theorem B19522133 : Blo 1582489 19522133 := bbase (se 8 (by rfl) ⟨114387, by rfl⟩ : syracuseStep 19522133 = 228775) (by norm_num)
theorem B4006493 : Blo 1582489 4006493 := bbase (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) (by norm_num)
theorem B12018293 : Blo 1582489 12018293 := bbase (se 5 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 12018293 = 1126715) (by norm_num)
theorem B6095477 : Blo 1582489 6095477 := bbase (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) (by norm_num)
theorem B2671285 : Blo 1582489 2671285 := bbase (se 5 (by rfl) ⟨125216, by rfl⟩ : syracuseStep 2671285 = 250433) (by norm_num)
theorem B21660373 : Blo 1582489 21660373 := bbase (se 7 (by rfl) ⟨253832, by rfl⟩ : syracuseStep 21660373 = 507665) (by norm_num)
theorem B2138869 : Blo 1582489 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B2671373 : Blo 1582489 2671373 := bbase (se 3 (by rfl) ⟨500882, by rfl⟩ : syracuseStep 2671373 = 1001765) (by norm_num)
theorem B4006685 : Blo 1582489 4006685 := bbase (se 3 (by rfl) ⟨751253, by rfl⟩ : syracuseStep 4006685 = 1502507) (by norm_num)
theorem B2671501 : Blo 1582489 2671501 := bbase (se 3 (by rfl) ⟨500906, by rfl⟩ : syracuseStep 2671501 = 1001813) (by norm_num)
theorem B2139053 : Blo 1582489 2139053 := bbase (se 3 (by rfl) ⟨401072, by rfl⟩ : syracuseStep 2139053 = 802145) (by norm_num)
theorem B2253749 : Blo 1582489 2253749 := bbase (se 5 (by rfl) ⟨105644, by rfl⟩ : syracuseStep 2253749 = 211289) (by norm_num)
theorem B5342165 : Blo 1582489 5342165 := bbase (se 7 (by rfl) ⟨62603, by rfl⟩ : syracuseStep 5342165 = 125207) (by norm_num)
theorem B2671589 : Blo 1582489 2671589 := bbase (se 4 (by rfl) ⟨250461, by rfl⟩ : syracuseStep 2671589 = 500923) (by norm_num)
theorem B2671717 : Blo 1582489 2671717 := bbase (se 4 (by rfl) ⟨250473, by rfl⟩ : syracuseStep 2671717 = 500947) (by norm_num)
theorem B4007029 : Blo 1582489 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B2671805 : Blo 1582489 2671805 := bbase (se 3 (by rfl) ⟨500963, by rfl⟩ : syracuseStep 2671805 = 1001927) (by norm_num)
theorem B1901765 : Blo 1582489 1901765 := bbase (se 4 (by rfl) ⟨178290, by rfl⟩ : syracuseStep 1901765 = 356581) (by norm_num)
theorem B4007141 : Blo 1582489 4007141 := bbase (se 4 (by rfl) ⟨375669, by rfl⟩ : syracuseStep 4007141 = 751339) (by norm_num)
theorem B2671933 : Blo 1582489 2671933 := bbase (se 3 (by rfl) ⟨500987, by rfl⟩ : syracuseStep 2671933 = 1001975) (by norm_num)
theorem B2852165 : Blo 1582489 2852165 := bbase (se 4 (by rfl) ⟨267390, by rfl⟩ : syracuseStep 2852165 = 534781) (by norm_num)
theorem B4506997 : Blo 1582489 4506997 := bbase (se 5 (by rfl) ⟨211265, by rfl⟩ : syracuseStep 4506997 = 422531) (by norm_num)
theorem B5342597 : Blo 1582489 5342597 := bbase (se 4 (by rfl) ⟨500868, by rfl⟩ : syracuseStep 5342597 = 1001737) (by norm_num)
theorem B2672021 : Blo 1582489 2672021 := bbase (se 6 (by rfl) ⟨62625, by rfl⟩ : syracuseStep 2672021 = 125251) (by norm_num)
theorem B4007333 : Blo 1582489 4007333 := bbase (se 4 (by rfl) ⟨375687, by rfl⟩ : syracuseStep 4007333 = 751375) (by norm_num)
theorem B1713613 : Blo 1582489 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B4507157 : Blo 1582489 4507157 := bbase (se 6 (by rfl) ⟨105636, by rfl⟩ : syracuseStep 4507157 = 211273) (by norm_num)
theorem B2672149 : Blo 1582489 2672149 := bbase (se 6 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 2672149 = 125257) (by norm_num)
theorem B3802733 : Blo 1582489 3802733 := bbase (se 3 (by rfl) ⟨713012, by rfl⟩ : syracuseStep 3802733 = 1426025) (by norm_num)
theorem B2672237 : Blo 1582489 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B3425917 : Blo 1582489 3425917 := bbase (se 3 (by rfl) ⟨642359, by rfl⟩ : syracuseStep 3425917 = 1284719) (by norm_num)
theorem B2254501 : Blo 1582489 2254501 := bbase (se 4 (by rfl) ⟨211359, by rfl⟩ : syracuseStep 2254501 = 422719) (by norm_num)
theorem B2672365 : Blo 1582489 2672365 := bbase (se 3 (by rfl) ⟨501068, by rfl⟩ : syracuseStep 2672365 = 1002137) (by norm_num)
theorem B4007677 : Blo 1582489 4007677 := bbase (se 3 (by rfl) ⟨751439, by rfl⟩ : syracuseStep 4007677 = 1502879) (by norm_num)
theorem B4507397 : Blo 1582489 4507397 := bbase (se 4 (by rfl) ⟨422568, by rfl⟩ : syracuseStep 4507397 = 845137) (by norm_num)
theorem B5343029 : Blo 1582489 5343029 := bbase (se 5 (by rfl) ⟨250454, by rfl⟩ : syracuseStep 5343029 = 500909) (by norm_num)
theorem B13526837 : Blo 1582489 13526837 := bbase (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) (by norm_num)
theorem B2672453 : Blo 1582489 2672453 := bbase (se 4 (by rfl) ⟨250542, by rfl⟩ : syracuseStep 2672453 = 501085) (by norm_num)
theorem B8013653 : Blo 1582489 8013653 := bbase (se 9 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 8013653 = 46955) (by norm_num)
theorem B15222613 : Blo 1582489 15222613 := bbase (se 9 (by rfl) ⟨44597, by rfl⟩ : syracuseStep 15222613 = 89195) (by norm_num)
theorem B4007789 : Blo 1582489 4007789 := bbase (se 3 (by rfl) ⟨751460, by rfl⟩ : syracuseStep 4007789 = 1502921) (by norm_num)
theorem B1902457 : Blo 1582489 1902457 := bbase (se 2 (by rfl) ⟨713421, by rfl⟩ : syracuseStep 1902457 = 1426843) (by norm_num)
theorem B4507589 : Blo 1582489 4507589 := bbase (se 4 (by rfl) ⟨422586, by rfl⟩ : syracuseStep 4507589 = 845173) (by norm_num)
theorem B2672581 : Blo 1582489 2672581 := bbase (se 4 (by rfl) ⟨250554, by rfl⟩ : syracuseStep 2672581 = 501109) (by norm_num)
theorem B2672669 : Blo 1582489 2672669 := bbase (se 3 (by rfl) ⟨501125, by rfl⟩ : syracuseStep 2672669 = 1002251) (by norm_num)
theorem B4007981 : Blo 1582489 4007981 := bbase (se 3 (by rfl) ⟨751496, by rfl⟩ : syracuseStep 4007981 = 1502993) (by norm_num)
theorem B1902673 : Blo 1582489 1902673 := bbase (se 2 (by rfl) ⟨713502, by rfl⟩ : syracuseStep 1902673 = 1427005) (by norm_num)
theorem B2058329 : Blo 1582489 2058329 := bbase (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) (by norm_num)
theorem B2672797 : Blo 1582489 2672797 := bbase (se 3 (by rfl) ⟨501149, by rfl⟩ : syracuseStep 2672797 = 1002299) (by norm_num)
theorem B5343461 : Blo 1582489 5343461 := bbase (se 4 (by rfl) ⟨500949, by rfl⟩ : syracuseStep 5343461 = 1001899) (by norm_num)
theorem B2672885 : Blo 1582489 2672885 := bbase (se 5 (by rfl) ⟨125291, by rfl⟩ : syracuseStep 2672885 = 250583) (by norm_num)
theorem B2853181 : Blo 1582489 2853181 := bbase (se 3 (by rfl) ⟨534971, by rfl⟩ : syracuseStep 2853181 = 1069943) (by norm_num)
theorem B6760837 : Blo 1582489 6760837 := bbase (se 4 (by rfl) ⟨633828, by rfl⟩ : syracuseStep 6760837 = 1267657) (by norm_num)
theorem B4008325 : Blo 1582489 4008325 := bbase (se 4 (by rfl) ⟨375780, by rfl⟩ : syracuseStep 4008325 = 751561) (by norm_num)
theorem B2255293 : Blo 1582489 2255293 := bbase (se 3 (by rfl) ⟨422867, by rfl⟩ : syracuseStep 2255293 = 845735) (by norm_num)
theorem B21121493 : Blo 1582489 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B4008437 : Blo 1582489 4008437 := bbase (se 5 (by rfl) ⟨187895, by rfl⟩ : syracuseStep 4008437 = 375791) (by norm_num)
theorem B2853397 : Blo 1582489 2853397 := bbase (se 6 (by rfl) ⟨66876, by rfl⟩ : syracuseStep 2853397 = 133753) (by norm_num)
theorem B32492117 : Blo 1582489 32492117 := bbase (se 8 (by rfl) ⟨190383, by rfl⟩ : syracuseStep 32492117 = 380767) (by norm_num)
theorem B1780321 : Blo 1582489 1780321 := bbase (se 2 (by rfl) ⟨667620, by rfl⟩ : syracuseStep 1780321 = 1335241) (by norm_num)
theorem B1780357 : Blo 1582489 1780357 := bbase (se 4 (by rfl) ⟨166908, by rfl⟩ : syracuseStep 1780357 = 333817) (by norm_num)
theorem B5343893 : Blo 1582489 5343893 := bbase (se 6 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 5343893 = 250495) (by norm_num)
theorem B1780393 : Blo 1582489 1780393 := bbase (se 2 (by rfl) ⟨667647, by rfl⟩ : syracuseStep 1780393 = 1335295) (by norm_num)
theorem B4008629 : Blo 1582489 4008629 := bbase (se 5 (by rfl) ⟨187904, by rfl⟩ : syracuseStep 4008629 = 375809) (by norm_num)
theorem B1780429 : Blo 1582489 1780429 := bbase (se 3 (by rfl) ⟨333830, by rfl⟩ : syracuseStep 1780429 = 667661) (by norm_num)
theorem B7219925 : Blo 1582489 7219925 := bbase (se 7 (by rfl) ⟨84608, by rfl⟩ : syracuseStep 7219925 = 169217) (by norm_num)
theorem B1780465 : Blo 1582489 1780465 := bbase (se 2 (by rfl) ⟨667674, by rfl⟩ : syracuseStep 1780465 = 1335349) (by norm_num)
theorem B5073653 : Blo 1582489 5073653 := bbase (se 5 (by rfl) ⟨237827, by rfl⟩ : syracuseStep 5073653 = 475655) (by norm_num)
theorem B1780501 : Blo 1582489 1780501 := bbase (se 6 (by rfl) ⟨41730, by rfl⟩ : syracuseStep 1780501 = 83461) (by norm_num)
theorem B1780537 : Blo 1582489 1780537 := bbase (se 2 (by rfl) ⟨667701, by rfl⟩ : syracuseStep 1780537 = 1335403) (by norm_num)
theorem B1780573 : Blo 1582489 1780573 := bbase (se 3 (by rfl) ⟨333857, by rfl⟩ : syracuseStep 1780573 = 667715) (by norm_num)
theorem B1780609 : Blo 1582489 1780609 := bbase (se 2 (by rfl) ⟨667728, by rfl⟩ : syracuseStep 1780609 = 1335457) (by norm_num)
theorem B1690517 : Blo 1582489 1690517 := bbase (se 6 (by rfl) ⟨39621, by rfl⟩ : syracuseStep 1690517 = 79243) (by norm_num)
theorem B1780645 : Blo 1582489 1780645 := bbase (se 4 (by rfl) ⟨166935, by rfl⟩ : syracuseStep 1780645 = 333871) (by norm_num)
theorem B4508581 : Blo 1582489 4508581 := bbase (se 4 (by rfl) ⟨422679, by rfl⟩ : syracuseStep 4508581 = 845359) (by norm_num)
theorem B1780681 : Blo 1582489 1780681 := bbase (se 2 (by rfl) ⟨667755, by rfl⟩ : syracuseStep 1780681 = 1335511) (by norm_num)
theorem B1780717 : Blo 1582489 1780717 := bbase (se 3 (by rfl) ⟨333884, by rfl⟩ : syracuseStep 1780717 = 667769) (by norm_num)
theorem B3435509 : Blo 1582489 3435509 := bbase (se 5 (by rfl) ⟨161039, by rfl⟩ : syracuseStep 3435509 = 322079) (by norm_num)
theorem B4008973 : Blo 1582489 4008973 := bbase (se 3 (by rfl) ⟨751682, by rfl⟩ : syracuseStep 4008973 = 1503365) (by norm_num)
theorem B1780753 : Blo 1582489 1780753 := bbase (se 2 (by rfl) ⟨667782, by rfl⟩ : syracuseStep 1780753 = 1335565) (by norm_num)
theorem B1780789 : Blo 1582489 1780789 := bbase (se 5 (by rfl) ⟨83474, by rfl⟩ : syracuseStep 1780789 = 166949) (by norm_num)
theorem B1805365 : Blo 1582489 1805365 := bbase (se 5 (by rfl) ⟨84626, by rfl⟩ : syracuseStep 1805365 = 169253) (by norm_num)
theorem B5344325 : Blo 1582489 5344325 := bbase (se 4 (by rfl) ⟨501030, by rfl⟩ : syracuseStep 5344325 = 1002061) (by norm_num)
theorem B1608773 : Blo 1582489 1608773 := bbase (se 4 (by rfl) ⟨150822, by rfl⟩ : syracuseStep 1608773 = 301645) (by norm_num)
theorem B1780825 : Blo 1582489 1780825 := bbase (se 2 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 1780825 = 1335619) (by norm_num)
theorem B8014949 : Blo 1582489 8014949 := bbase (se 4 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 8014949 = 1502803) (by norm_num)
theorem B1780861 : Blo 1582489 1780861 := bbase (se 3 (by rfl) ⟨333911, by rfl⟩ : syracuseStep 1780861 = 667823) (by norm_num)
theorem B4009085 : Blo 1582489 4009085 := bbase (se 3 (by rfl) ⟨751703, by rfl⟩ : syracuseStep 4009085 = 1503407) (by norm_num)
theorem B1780897 : Blo 1582489 1780897 := bbase (se 2 (by rfl) ⟨667836, by rfl⟩ : syracuseStep 1780897 = 1335673) (by norm_num)
theorem B1780933 : Blo 1582489 1780933 := bbase (se 4 (by rfl) ⟨166962, by rfl⟩ : syracuseStep 1780933 = 333925) (by norm_num)
theorem B1780969 : Blo 1582489 1780969 := bbase (se 2 (by rfl) ⟨667863, by rfl⟩ : syracuseStep 1780969 = 1335727) (by norm_num)
theorem B1805557 : Blo 1582489 1805557 := bbase (se 5 (by rfl) ⟨84635, by rfl⟩ : syracuseStep 1805557 = 169271) (by norm_num)
theorem B1781005 : Blo 1582489 1781005 := bbase (se 3 (by rfl) ⟨333938, by rfl⟩ : syracuseStep 1781005 = 667877) (by norm_num)
theorem B2854189 : Blo 1582489 2854189 := bbase (se 3 (by rfl) ⟨535160, by rfl⟩ : syracuseStep 2854189 = 1070321) (by norm_num)
theorem B1781041 : Blo 1582489 1781041 := bbase (se 2 (by rfl) ⟨667890, by rfl⟩ : syracuseStep 1781041 = 1335781) (by norm_num)
theorem B4009277 : Blo 1582489 4009277 := bbase (se 3 (by rfl) ⟨751739, by rfl⟩ : syracuseStep 4009277 = 1503479) (by norm_num)
theorem B1690961 : Blo 1582489 1690961 := bbase (se 2 (by rfl) ⟨634110, by rfl⟩ : syracuseStep 1690961 = 1268221) (by norm_num)
theorem B1781077 : Blo 1582489 1781077 := bbase (se 11 (by rfl) ⟨1304, by rfl⟩ : syracuseStep 1781077 = 2609) (by norm_num)
theorem B3804509 : Blo 1582489 3804509 := bbase (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) (by norm_num)
theorem B1781113 : Blo 1582489 1781113 := bbase (se 2 (by rfl) ⟨667917, by rfl⟩ : syracuseStep 1781113 = 1335835) (by norm_num)
theorem B5705093 : Blo 1582489 5705093 := bbase (se 4 (by rfl) ⟨534852, by rfl⟩ : syracuseStep 5705093 = 1069705) (by norm_num)
theorem B1781149 : Blo 1582489 1781149 := bbase (se 3 (by rfl) ⟨333965, by rfl⟩ : syracuseStep 1781149 = 667931) (by norm_num)
theorem B1781185 : Blo 1582489 1781185 := bbase (se 2 (by rfl) ⟨667944, by rfl⟩ : syracuseStep 1781185 = 1335889) (by norm_num)
theorem B1781221 : Blo 1582489 1781221 := bbase (se 4 (by rfl) ⟨166989, by rfl⟩ : syracuseStep 1781221 = 333979) (by norm_num)
theorem B5344757 : Blo 1582489 5344757 := bbase (se 5 (by rfl) ⟨250535, by rfl⟩ : syracuseStep 5344757 = 501071) (by norm_num)
theorem B1781257 : Blo 1582489 1781257 := bbase (se 2 (by rfl) ⟨667971, by rfl⟩ : syracuseStep 1781257 = 1335943) (by norm_num)
theorem B1781293 : Blo 1582489 1781293 := bbase (se 3 (by rfl) ⟨333992, by rfl⟩ : syracuseStep 1781293 = 667985) (by norm_num)
theorem B2534981 : Blo 1582489 2534981 := bbase (se 4 (by rfl) ⟨237654, by rfl⟩ : syracuseStep 2534981 = 475309) (by norm_num)
theorem B1691209 : Blo 1582489 1691209 := bbase (se 2 (by rfl) ⟨634203, by rfl⟩ : syracuseStep 1691209 = 1268407) (by norm_num)
theorem B1781329 : Blo 1582489 1781329 := bbase (se 2 (by rfl) ⟨667998, by rfl⟩ : syracuseStep 1781329 = 1335997) (by norm_num)
theorem B45649493 : Blo 1582489 45649493 := bbase (se 8 (by rfl) ⟨267477, by rfl⟩ : syracuseStep 45649493 = 534955) (by norm_num)
theorem B1781365 : Blo 1582489 1781365 := bbase (se 5 (by rfl) ⟨83501, by rfl⟩ : syracuseStep 1781365 = 167003) (by norm_num)
theorem B1781401 : Blo 1582489 1781401 := bbase (se 2 (by rfl) ⟨668025, by rfl⟩ : syracuseStep 1781401 = 1336051) (by norm_num)
theorem B1805981 : Blo 1582489 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B1781437 : Blo 1582489 1781437 := bbase (se 3 (by rfl) ⟨334019, by rfl⟩ : syracuseStep 1781437 = 668039) (by norm_num)
theorem B1781473 : Blo 1582489 1781473 := bbase (se 2 (by rfl) ⟨668052, by rfl⟩ : syracuseStep 1781473 = 1336105) (by norm_num)
theorem B7606021 : Blo 1582489 7606021 := bbase (se 4 (by rfl) ⟨713064, by rfl⟩ : syracuseStep 7606021 = 1426129) (by norm_num)
theorem B1781509 : Blo 1582489 1781509 := bbase (se 4 (by rfl) ⟨167016, by rfl⟩ : syracuseStep 1781509 = 334033) (by norm_num)
theorem B1781545 : Blo 1582489 1781545 := bbase (se 2 (by rfl) ⟨668079, by rfl⟩ : syracuseStep 1781545 = 1336159) (by norm_num)
theorem B1806149 : Blo 1582489 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B1781581 : Blo 1582489 1781581 := bbase (se 3 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 1781581 = 668093) (by norm_num)
theorem B6762325 : Blo 1582489 6762325 := bbase (se 9 (by rfl) ⟨19811, by rfl⟩ : syracuseStep 6762325 = 39623) (by norm_num)
theorem B6762341 : Blo 1582489 6762341 := bbase (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) (by norm_num)
theorem B1953649 : Blo 1582489 1953649 := bbase (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) (by norm_num)
theorem B1781617 : Blo 1582489 1781617 := bbase (se 2 (by rfl) ⟨668106, by rfl⟩ : syracuseStep 1781617 = 1336213) (by norm_num)
theorem B1781653 : Blo 1582489 1781653 := bbase (se 6 (by rfl) ⟨41757, by rfl⟩ : syracuseStep 1781653 = 83515) (by norm_num)
theorem B5345189 : Blo 1582489 5345189 := bbase (se 4 (by rfl) ⟨501111, by rfl⟩ : syracuseStep 5345189 = 1002223) (by norm_num)
theorem B1781689 : Blo 1582489 1781689 := bbase (se 2 (by rfl) ⟨668133, by rfl⟩ : syracuseStep 1781689 = 1336267) (by norm_num)
theorem B2002897 : Blo 1582489 2002897 := bbase (se 2 (by rfl) ⟨751086, by rfl⟩ : syracuseStep 2002897 = 1502173) (by norm_num)
theorem B1781725 : Blo 1582489 1781725 := bbase (se 3 (by rfl) ⟨334073, by rfl⟩ : syracuseStep 1781725 = 668147) (by norm_num)
theorem B4509685 : Blo 1582489 4509685 := bbase (se 5 (by rfl) ⟨211391, by rfl⟩ : syracuseStep 4509685 = 422783) (by norm_num)
theorem B1781761 : Blo 1582489 1781761 := bbase (se 2 (by rfl) ⟨668160, by rfl⟩ : syracuseStep 1781761 = 1336321) (by norm_num)
theorem B1781797 : Blo 1582489 1781797 := bbase (se 4 (by rfl) ⟨167043, by rfl⟩ : syracuseStep 1781797 = 334087) (by norm_num)
theorem B1781833 : Blo 1582489 1781833 := bbase (se 2 (by rfl) ⟨668187, by rfl⟩ : syracuseStep 1781833 = 1336375) (by norm_num)
theorem B2535533 : Blo 1582489 2535533 := bbase (se 3 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 2535533 = 950825) (by norm_num)
theorem B1781869 : Blo 1582489 1781869 := bbase (se 3 (by rfl) ⟨334100, by rfl⟩ : syracuseStep 1781869 = 668201) (by norm_num)
theorem B2003069 : Blo 1582489 2003069 := bbase (se 3 (by rfl) ⟨375575, by rfl⟩ : syracuseStep 2003069 = 751151) (by norm_num)
theorem B2535565 : Blo 1582489 2535565 := bbase (se 3 (by rfl) ⟨475418, by rfl⟩ : syracuseStep 2535565 = 950837) (by norm_num)
theorem B1781905 : Blo 1582489 1781905 := bbase (se 2 (by rfl) ⟨668214, by rfl⟩ : syracuseStep 1781905 = 1336429) (by norm_num)
theorem B2003125 : Blo 1582489 2003125 := bbase (se 5 (by rfl) ⟨93896, by rfl⟩ : syracuseStep 2003125 = 187793) (by norm_num)
theorem B1781941 : Blo 1582489 1781941 := bbase (se 5 (by rfl) ⟨83528, by rfl⟩ : syracuseStep 1781941 = 167057) (by norm_num)
theorem B1781977 : Blo 1582489 1781977 := bbase (se 2 (by rfl) ⟨668241, by rfl⟩ : syracuseStep 1781977 = 1336483) (by norm_num)
theorem B2003221 : Blo 1582489 2003221 := bbase (se 6 (by rfl) ⟨46950, by rfl⟩ : syracuseStep 2003221 = 93901) (by norm_num)
theorem B5345621 : Blo 1582489 5345621 := bbase (se 10 (by rfl) ⟨7830, by rfl⟩ : syracuseStep 5345621 = 15661) (by norm_num)
theorem B8016245 : Blo 1582489 8016245 := bbase (se 5 (by rfl) ⟨375761, by rfl⟩ : syracuseStep 8016245 = 751523) (by norm_num)
theorem B2003393 : Blo 1582489 2003393 := bbase (se 2 (by rfl) ⟨751272, by rfl⟩ : syracuseStep 2003393 = 1502545) (by norm_num)
theorem B2003449 : Blo 1582489 2003449 := bbase (se 2 (by rfl) ⟨751293, by rfl⟩ : syracuseStep 2003449 = 1502587) (by norm_num)
theorem B2003545 : Blo 1582489 2003545 := bbase (se 2 (by rfl) ⟨751329, by rfl⟩ : syracuseStep 2003545 = 1502659) (by norm_num)
theorem B1585837 : Blo 1582489 1585837 := bbase (se 3 (by rfl) ⟨297344, by rfl⟩ : syracuseStep 1585837 = 594689) (by norm_num)
theorem B10146485 : Blo 1582489 10146485 := bbase (se 5 (by rfl) ⟨475616, by rfl⟩ : syracuseStep 10146485 = 951233) (by norm_num)
theorem B2003717 : Blo 1582489 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B5706533 : Blo 1582489 5706533 := bbase (se 4 (by rfl) ⟨534987, by rfl⟩ : syracuseStep 5706533 = 1069975) (by norm_num)
theorem B2003773 : Blo 1582489 2003773 := bbase (se 3 (by rfl) ⟨375707, by rfl⟩ : syracuseStep 2003773 = 751415) (by norm_num)
theorem B3380069 : Blo 1582489 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B3380077 : Blo 1582489 3380077 := bbase (se 3 (by rfl) ⟨633764, by rfl⟩ : syracuseStep 3380077 = 1267529) (by norm_num)
theorem B9016181 : Blo 1582489 9016181 := bbase (se 5 (by rfl) ⟨422633, by rfl⟩ : syracuseStep 9016181 = 845267) (by norm_num)
theorem B2003869 : Blo 1582489 2003869 := bbase (se 3 (by rfl) ⟨375725, by rfl⟩ : syracuseStep 2003869 = 751451) (by norm_num)
theorem B2536493 : Blo 1582489 2536493 := bbase (se 3 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 2536493 = 951185) (by norm_num)
theorem B2004041 : Blo 1582489 2004041 := bbase (se 2 (by rfl) ⟨751515, by rfl⟩ : syracuseStep 2004041 = 1503031) (by norm_num)
theorem B2004097 : Blo 1582489 2004097 := bbase (se 2 (by rfl) ⟨751536, by rfl⟩ : syracuseStep 2004097 = 1503073) (by norm_num)
theorem B4117661 : Blo 1582489 4117661 := bbase (se 3 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 4117661 = 1544123) (by norm_num)
theorem B3560669 : Blo 1582489 3560669 := bbase (se 3 (by rfl) ⟨667625, by rfl⟩ : syracuseStep 3560669 = 1335251) (by norm_num)
theorem B2004193 : Blo 1582489 2004193 := bbase (se 2 (by rfl) ⟨751572, by rfl⟩ : syracuseStep 2004193 = 1503145) (by norm_num)
theorem B3560741 : Blo 1582489 3560741 := bbase (se 4 (by rfl) ⟨333819, by rfl⟩ : syracuseStep 3560741 = 667639) (by norm_num)
theorem B5862709 : Blo 1582489 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B3560813 : Blo 1582489 3560813 := bbase (se 3 (by rfl) ⟨667652, by rfl⟩ : syracuseStep 3560813 = 1335305) (by norm_num)
theorem B2004365 : Blo 1582489 2004365 := bbase (se 3 (by rfl) ⟨375818, by rfl⟩ : syracuseStep 2004365 = 751637) (by norm_num)
theorem B3560885 : Blo 1582489 3560885 := bbase (se 5 (by rfl) ⟨166916, by rfl⟩ : syracuseStep 3560885 = 333833) (by norm_num)
theorem B2004421 : Blo 1582489 2004421 := bbase (se 4 (by rfl) ⟨187914, by rfl⟩ : syracuseStep 2004421 = 375829) (by norm_num)
theorem B3560957 : Blo 1582489 3560957 := bbase (se 3 (by rfl) ⟨667679, by rfl⟩ : syracuseStep 3560957 = 1335359) (by norm_num)
theorem B2004517 : Blo 1582489 2004517 := bbase (se 4 (by rfl) ⟨187923, by rfl⟩ : syracuseStep 2004517 = 375847) (by norm_num)
theorem B3561029 : Blo 1582489 3561029 := bbase (se 4 (by rfl) ⟨333846, by rfl⟩ : syracuseStep 3561029 = 667693) (by norm_num)
theorem B6010469 : Blo 1582489 6010469 := bbase (se 4 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 6010469 = 1126963) (by norm_num)
theorem B8017541 : Blo 1582489 8017541 := bbase (se 4 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 8017541 = 1503289) (by norm_num)
theorem B3561101 : Blo 1582489 3561101 := bbase (se 3 (by rfl) ⟨667706, by rfl⟩ : syracuseStep 3561101 = 1335413) (by norm_num)
theorem B2004689 : Blo 1582489 2004689 := bbase (se 2 (by rfl) ⟨751758, by rfl⟩ : syracuseStep 2004689 = 1503517) (by norm_num)
theorem B3561173 : Blo 1582489 3561173 := bbase (se 7 (by rfl) ⟨41732, by rfl⟩ : syracuseStep 3561173 = 83465) (by norm_num)
theorem B2537173 : Blo 1582489 2537173 := bbase (se 7 (by rfl) ⟨29732, by rfl⟩ : syracuseStep 2537173 = 59465) (by norm_num)
theorem B2709245 : Blo 1582489 2709245 := bbase (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) (by norm_num)
theorem B2537237 : Blo 1582489 2537237 := bbase (se 6 (by rfl) ⟨59466, by rfl⟩ : syracuseStep 2537237 = 118933) (by norm_num)
theorem B3561245 : Blo 1582489 3561245 := bbase (se 3 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 3561245 = 1335467) (by norm_num)
theorem B3561317 : Blo 1582489 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B3004285 : Blo 1582489 3004285 := bbase (se 3 (by rfl) ⟨563303, by rfl⟩ : syracuseStep 3004285 = 1126607) (by norm_num)
theorem B6010757 : Blo 1582489 6010757 := bbase (se 4 (by rfl) ⟨563508, by rfl⟩ : syracuseStep 6010757 = 1127017) (by norm_num)
theorem B3561389 : Blo 1582489 3561389 := bbase (se 3 (by rfl) ⟨667760, by rfl⟩ : syracuseStep 3561389 = 1335521) (by norm_num)
theorem B3381205 : Blo 1582489 3381205 := bbase (se 7 (by rfl) ⟨39623, by rfl⟩ : syracuseStep 3381205 = 79247) (by norm_num)
theorem B3561461 : Blo 1582489 3561461 := bbase (se 5 (by rfl) ⟨166943, by rfl⟩ : syracuseStep 3561461 = 333887) (by norm_num)
theorem B3209213 : Blo 1582489 3209213 := bbase (se 3 (by rfl) ⟨601727, by rfl⟩ : syracuseStep 3209213 = 1203455) (by norm_num)
theorem B6420485 : Blo 1582489 6420485 := bbase (se 4 (by rfl) ⟨601920, by rfl⟩ : syracuseStep 6420485 = 1203841) (by norm_num)
theorem B9017365 : Blo 1582489 9017365 := bbase (se 6 (by rfl) ⟨211344, by rfl⟩ : syracuseStep 9017365 = 422689) (by norm_num)
theorem B3004445 : Blo 1582489 3004445 := bbase (se 3 (by rfl) ⟨563333, by rfl⟩ : syracuseStep 3004445 = 1126667) (by norm_num)
theorem B6764597 : Blo 1582489 6764597 := bbase (se 5 (by rfl) ⟨317090, by rfl⟩ : syracuseStep 6764597 = 634181) (by norm_num)
theorem B3561533 : Blo 1582489 3561533 := bbase (se 3 (by rfl) ⟨667787, by rfl⟩ : syracuseStep 3561533 = 1335575) (by norm_num)
theorem B2373749 : Blo 1582489 2373749 := bbase (se 5 (by rfl) ⟨111269, by rfl⟩ : syracuseStep 2373749 = 222539) (by norm_num)
theorem B3561605 : Blo 1582489 3561605 := bbase (se 4 (by rfl) ⟨333900, by rfl⟩ : syracuseStep 3561605 = 667801) (by norm_num)
theorem B2373773 : Blo 1582489 2373773 := bbase (se 3 (by rfl) ⟨445082, by rfl⟩ : syracuseStep 2373773 = 890165) (by norm_num)
theorem B2373797 : Blo 1582489 2373797 := bbase (se 4 (by rfl) ⟨222543, by rfl⟩ : syracuseStep 2373797 = 445087) (by norm_num)
theorem B3004589 : Blo 1582489 3004589 := bbase (se 3 (by rfl) ⟨563360, by rfl⟩ : syracuseStep 3004589 = 1126721) (by norm_num)
theorem B2373821 : Blo 1582489 2373821 := bbase (se 3 (by rfl) ⟨445091, by rfl⟩ : syracuseStep 2373821 = 890183) (by norm_num)
theorem B3561677 : Blo 1582489 3561677 := bbase (se 3 (by rfl) ⟨667814, by rfl⟩ : syracuseStep 3561677 = 1335629) (by norm_num)
theorem B2373845 : Blo 1582489 2373845 := bbase (se 7 (by rfl) ⟨27818, by rfl⟩ : syracuseStep 2373845 = 55637) (by norm_num)
theorem B2373869 : Blo 1582489 2373869 := bbase (se 3 (by rfl) ⟨445100, by rfl⟩ : syracuseStep 2373869 = 890201) (by norm_num)
theorem B2373893 : Blo 1582489 2373893 := bbase (se 4 (by rfl) ⟨222552, by rfl⟩ : syracuseStep 2373893 = 445105) (by norm_num)
theorem B3561749 : Blo 1582489 3561749 := bbase (se 6 (by rfl) ⟨83478, by rfl⟩ : syracuseStep 3561749 = 166957) (by norm_num)
theorem B2373917 : Blo 1582489 2373917 := bbase (se 3 (by rfl) ⟨445109, by rfl⟩ : syracuseStep 2373917 = 890219) (by norm_num)
theorem B2373941 : Blo 1582489 2373941 := bbase (se 5 (by rfl) ⟨111278, by rfl⟩ : syracuseStep 2373941 = 222557) (by norm_num)
theorem B2373965 : Blo 1582489 2373965 := bbase (se 3 (by rfl) ⟨445118, by rfl⟩ : syracuseStep 2373965 = 890237) (by norm_num)
theorem B3381581 : Blo 1582489 3381581 := bbase (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) (by norm_num)
theorem B3561821 : Blo 1582489 3561821 := bbase (se 3 (by rfl) ⟨667841, by rfl⟩ : syracuseStep 3561821 = 1335683) (by norm_num)
theorem B2373989 : Blo 1582489 2373989 := bbase (se 4 (by rfl) ⟨222561, by rfl⟩ : syracuseStep 2373989 = 445123) (by norm_num)
theorem B2374013 : Blo 1582489 2374013 := bbase (se 3 (by rfl) ⟨445127, by rfl⟩ : syracuseStep 2374013 = 890255) (by norm_num)
theorem B2374037 : Blo 1582489 2374037 := bbase (se 6 (by rfl) ⟨55641, by rfl⟩ : syracuseStep 2374037 = 111283) (by norm_num)
theorem B3561893 : Blo 1582489 3561893 := bbase (se 4 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 3561893 = 667855) (by norm_num)
theorem B2374061 : Blo 1582489 2374061 := bbase (se 3 (by rfl) ⟨445136, by rfl⟩ : syracuseStep 2374061 = 890273) (by norm_num)
theorem B16251317 : Blo 1582489 16251317 := bbase (se 5 (by rfl) ⟨761780, by rfl⟩ : syracuseStep 16251317 = 1523561) (by norm_num)
theorem B2374085 : Blo 1582489 2374085 := bbase (se 4 (by rfl) ⟨222570, by rfl⟩ : syracuseStep 2374085 = 445141) (by norm_num)
theorem B3004877 : Blo 1582489 3004877 := bbase (se 3 (by rfl) ⟨563414, by rfl⟩ : syracuseStep 3004877 = 1126829) (by norm_num)
theorem B2374109 : Blo 1582489 2374109 := bbase (se 3 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 2374109 = 890291) (by norm_num)
theorem B3561965 : Blo 1582489 3561965 := bbase (se 3 (by rfl) ⟨667868, by rfl⟩ : syracuseStep 3561965 = 1335737) (by norm_num)
theorem B2374133 : Blo 1582489 2374133 := bbase (se 5 (by rfl) ⟨111287, by rfl⟩ : syracuseStep 2374133 = 222575) (by norm_num)
theorem B2374157 : Blo 1582489 2374157 := bbase (se 3 (by rfl) ⟨445154, by rfl⟩ : syracuseStep 2374157 = 890309) (by norm_num)
theorem B2374181 : Blo 1582489 2374181 := bbase (se 4 (by rfl) ⟨222579, by rfl⟩ : syracuseStep 2374181 = 445159) (by norm_num)
theorem B3562037 : Blo 1582489 3562037 := bbase (se 5 (by rfl) ⟨166970, by rfl⟩ : syracuseStep 3562037 = 333941) (by norm_num)
theorem B2374205 : Blo 1582489 2374205 := bbase (se 3 (by rfl) ⟨445163, by rfl⟩ : syracuseStep 2374205 = 890327) (by norm_num)
theorem B1604161 : Blo 1582489 1604161 := bbase (se 2 (by rfl) ⟨601560, by rfl⟩ : syracuseStep 1604161 = 1203121) (by norm_num)
theorem B2374229 : Blo 1582489 2374229 := bbase (se 8 (by rfl) ⟨13911, by rfl⟩ : syracuseStep 2374229 = 27823) (by norm_num)
theorem B3005029 : Blo 1582489 3005029 := bbase (se 4 (by rfl) ⟨281721, by rfl⟩ : syracuseStep 3005029 = 563443) (by norm_num)
theorem B2374253 : Blo 1582489 2374253 := bbase (se 3 (by rfl) ⟨445172, by rfl⟩ : syracuseStep 2374253 = 890345) (by norm_num)
theorem B3562109 : Blo 1582489 3562109 := bbase (se 3 (by rfl) ⟨667895, by rfl⟩ : syracuseStep 3562109 = 1335791) (by norm_num)
theorem B2374277 : Blo 1582489 2374277 := bbase (se 4 (by rfl) ⟨222588, by rfl⟩ : syracuseStep 2374277 = 445177) (by norm_num)
theorem B2374301 : Blo 1582489 2374301 := bbase (se 3 (by rfl) ⟨445181, by rfl⟩ : syracuseStep 2374301 = 890363) (by norm_num)
theorem B2374325 : Blo 1582489 2374325 := bbase (se 5 (by rfl) ⟨111296, by rfl⟩ : syracuseStep 2374325 = 222593) (by norm_num)
theorem B8125109 : Blo 1582489 8125109 := bbase (se 5 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 8125109 = 761729) (by norm_num)
theorem B3562181 : Blo 1582489 3562181 := bbase (se 4 (by rfl) ⟨333954, by rfl⟩ : syracuseStep 3562181 = 667909) (by norm_num)
theorem B2374349 : Blo 1582489 2374349 := bbase (se 3 (by rfl) ⟨445190, by rfl⟩ : syracuseStep 2374349 = 890381) (by norm_num)
theorem B2374373 : Blo 1582489 2374373 := bbase (se 4 (by rfl) ⟨222597, by rfl⟩ : syracuseStep 2374373 = 445195) (by norm_num)
theorem B2374397 : Blo 1582489 2374397 := bbase (se 3 (by rfl) ⟨445199, by rfl⟩ : syracuseStep 2374397 = 890399) (by norm_num)
theorem B3562253 : Blo 1582489 3562253 := bbase (se 3 (by rfl) ⟨667922, by rfl⟩ : syracuseStep 3562253 = 1335845) (by norm_num)
theorem B2374421 : Blo 1582489 2374421 := bbase (se 6 (by rfl) ⟨55650, by rfl⟩ : syracuseStep 2374421 = 111301) (by norm_num)
theorem B2374445 : Blo 1582489 2374445 := bbase (se 3 (by rfl) ⟨445208, by rfl⟩ : syracuseStep 2374445 = 890417) (by norm_num)
theorem B2374469 : Blo 1582489 2374469 := bbase (se 4 (by rfl) ⟨222606, by rfl⟩ : syracuseStep 2374469 = 445213) (by norm_num)
theorem B3562325 : Blo 1582489 3562325 := bbase (se 9 (by rfl) ⟨10436, by rfl⟩ : syracuseStep 3562325 = 20873) (by norm_num)
theorem B2374493 : Blo 1582489 2374493 := bbase (se 3 (by rfl) ⟨445217, by rfl⟩ : syracuseStep 2374493 = 890435) (by norm_num)
theorem B2374517 : Blo 1582489 2374517 := bbase (se 5 (by rfl) ⟨111305, by rfl⟩ : syracuseStep 2374517 = 222611) (by norm_num)
theorem B2374541 : Blo 1582489 2374541 := bbase (se 3 (by rfl) ⟨445226, by rfl⟩ : syracuseStep 2374541 = 890453) (by norm_num)
theorem B13523861 : Blo 1582489 13523861 := bbase (se 6 (by rfl) ⟨316965, by rfl⟩ : syracuseStep 13523861 = 633931) (by norm_num)
theorem B3005333 : Blo 1582489 3005333 := bbase (se 6 (by rfl) ⟨70437, by rfl⟩ : syracuseStep 3005333 = 140875) (by norm_num)
theorem B8018837 : Blo 1582489 8018837 := bbase (se 6 (by rfl) ⟨187941, by rfl⟩ : syracuseStep 8018837 = 375883) (by norm_num)
theorem B3562397 : Blo 1582489 3562397 := bbase (se 3 (by rfl) ⟨667949, by rfl⟩ : syracuseStep 3562397 = 1335899) (by norm_num)
theorem B2030501 : Blo 1582489 2030501 := bbase (se 4 (by rfl) ⟨190359, by rfl⟩ : syracuseStep 2030501 = 380719) (by norm_num)
theorem B2374565 : Blo 1582489 2374565 := bbase (se 4 (by rfl) ⟨222615, by rfl⟩ : syracuseStep 2374565 = 445231) (by norm_num)
theorem B2374589 : Blo 1582489 2374589 := bbase (se 3 (by rfl) ⟨445235, by rfl⟩ : syracuseStep 2374589 = 890471) (by norm_num)
theorem B2374613 : Blo 1582489 2374613 := bbase (se 7 (by rfl) ⟨27827, by rfl⟩ : syracuseStep 2374613 = 55655) (by norm_num)
theorem B3562469 : Blo 1582489 3562469 := bbase (se 4 (by rfl) ⟨333981, by rfl⟩ : syracuseStep 3562469 = 667963) (by norm_num)
theorem B2374637 : Blo 1582489 2374637 := bbase (se 3 (by rfl) ⟨445244, by rfl⟩ : syracuseStep 2374637 = 890489) (by norm_num)
theorem B2374661 : Blo 1582489 2374661 := bbase (se 4 (by rfl) ⟨222624, by rfl⟩ : syracuseStep 2374661 = 445249) (by norm_num)
theorem B2374685 : Blo 1582489 2374685 := bbase (se 3 (by rfl) ⟨445253, by rfl⟩ : syracuseStep 2374685 = 890507) (by norm_num)
theorem B3611677 : Blo 1582489 3611677 := bbase (se 3 (by rfl) ⟨677189, by rfl⟩ : syracuseStep 3611677 = 1354379) (by norm_num)
theorem B5069861 : Blo 1582489 5069861 := bbase (se 4 (by rfl) ⟨475299, by rfl⟩ : syracuseStep 5069861 = 950599) (by norm_num)
theorem B6011941 : Blo 1582489 6011941 := bbase (se 4 (by rfl) ⟨563619, by rfl⟩ : syracuseStep 6011941 = 1127239) (by norm_num)
theorem B3562541 : Blo 1582489 3562541 := bbase (se 3 (by rfl) ⟨667976, by rfl⟩ : syracuseStep 3562541 = 1335953) (by norm_num)
theorem B2374709 : Blo 1582489 2374709 := bbase (se 5 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 2374709 = 222629) (by norm_num)
theorem B2374733 : Blo 1582489 2374733 := bbase (se 3 (by rfl) ⟨445262, by rfl⟩ : syracuseStep 2374733 = 890525) (by norm_num)
theorem B2374757 : Blo 1582489 2374757 := bbase (se 4 (by rfl) ⟨222633, by rfl⟩ : syracuseStep 2374757 = 445267) (by norm_num)
theorem B3210349 : Blo 1582489 3210349 := bbase (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) (by norm_num)
theorem B3562613 : Blo 1582489 3562613 := bbase (se 5 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 3562613 = 333995) (by norm_num)
theorem B2374781 : Blo 1582489 2374781 := bbase (se 3 (by rfl) ⟨445271, by rfl⟩ : syracuseStep 2374781 = 890543) (by norm_num)
theorem B2374805 : Blo 1582489 2374805 := bbase (se 6 (by rfl) ⟨55659, by rfl⟩ : syracuseStep 2374805 = 111319) (by norm_num)
theorem B1604777 : Blo 1582489 1604777 := bbase (se 2 (by rfl) ⟨601791, by rfl⟩ : syracuseStep 1604777 = 1203583) (by norm_num)
theorem B2374829 : Blo 1582489 2374829 := bbase (se 3 (by rfl) ⟨445280, by rfl⟩ : syracuseStep 2374829 = 890561) (by norm_num)
theorem B3562685 : Blo 1582489 3562685 := bbase (se 3 (by rfl) ⟨668003, by rfl⟩ : syracuseStep 3562685 = 1336007) (by norm_num)
theorem B2030789 : Blo 1582489 2030789 := bbase (se 4 (by rfl) ⟨190386, by rfl⟩ : syracuseStep 2030789 = 380773) (by norm_num)
theorem B2374853 : Blo 1582489 2374853 := bbase (se 4 (by rfl) ⟨222642, by rfl⟩ : syracuseStep 2374853 = 445285) (by norm_num)
theorem B1604809 : Blo 1582489 1604809 := bbase (se 2 (by rfl) ⟨601803, by rfl⟩ : syracuseStep 1604809 = 1203607) (by norm_num)
theorem B2374877 : Blo 1582489 2374877 := bbase (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) (by norm_num)
theorem B2374901 : Blo 1582489 2374901 := bbase (se 5 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 2374901 = 222647) (by norm_num)
theorem B3562757 : Blo 1582489 3562757 := bbase (se 4 (by rfl) ⟨334008, by rfl⟩ : syracuseStep 3562757 = 668017) (by norm_num)
theorem B2374925 : Blo 1582489 2374925 := bbase (se 3 (by rfl) ⟨445298, by rfl⟩ : syracuseStep 2374925 = 890597) (by norm_num)
theorem B2374949 : Blo 1582489 2374949 := bbase (se 4 (by rfl) ⟨222651, by rfl⟩ : syracuseStep 2374949 = 445303) (by norm_num)
theorem B2374973 : Blo 1582489 2374973 := bbase (se 3 (by rfl) ⟨445307, by rfl⟩ : syracuseStep 2374973 = 890615) (by norm_num)
theorem B3562829 : Blo 1582489 3562829 := bbase (se 3 (by rfl) ⟨668030, by rfl⟩ : syracuseStep 3562829 = 1336061) (by norm_num)
theorem B2374997 : Blo 1582489 2374997 := bbase (se 11 (by rfl) ⟨1739, by rfl⟩ : syracuseStep 2374997 = 3479) (by norm_num)
theorem B6012245 : Blo 1582489 6012245 := bbase (se 11 (by rfl) ⟨4403, by rfl⟩ : syracuseStep 6012245 = 8807) (by norm_num)
theorem B2375021 : Blo 1582489 2375021 := bbase (se 3 (by rfl) ⟨445316, by rfl⟩ : syracuseStep 2375021 = 890633) (by norm_num)
theorem B2375045 : Blo 1582489 2375045 := bbase (se 4 (by rfl) ⟨222660, by rfl⟩ : syracuseStep 2375045 = 445321) (by norm_num)
theorem B3562901 : Blo 1582489 3562901 := bbase (se 6 (by rfl) ⟨83505, by rfl⟩ : syracuseStep 3562901 = 167011) (by norm_num)
theorem B2375069 : Blo 1582489 2375069 := bbase (se 3 (by rfl) ⟨445325, by rfl⟩ : syracuseStep 2375069 = 890651) (by norm_num)
theorem B2375093 : Blo 1582489 2375093 := bbase (se 5 (by rfl) ⟨111332, by rfl⟩ : syracuseStep 2375093 = 222665) (by norm_num)
theorem B2375117 : Blo 1582489 2375117 := bbase (se 3 (by rfl) ⟨445334, by rfl⟩ : syracuseStep 2375117 = 890669) (by norm_num)
theorem B3562973 : Blo 1582489 3562973 := bbase (se 3 (by rfl) ⟨668057, by rfl⟩ : syracuseStep 3562973 = 1336115) (by norm_num)
theorem B2375141 : Blo 1582489 2375141 := bbase (se 4 (by rfl) ⟨222669, by rfl⟩ : syracuseStep 2375141 = 445339) (by norm_num)
theorem B2031097 : Blo 1582489 2031097 := bbase (se 2 (by rfl) ⟨761661, by rfl⟩ : syracuseStep 2031097 = 1523323) (by norm_num)
theorem B2375165 : Blo 1582489 2375165 := bbase (se 3 (by rfl) ⟨445343, by rfl⟩ : syracuseStep 2375165 = 890687) (by norm_num)
theorem B2375189 : Blo 1582489 2375189 := bbase (se 6 (by rfl) ⟨55668, by rfl⟩ : syracuseStep 2375189 = 111337) (by norm_num)
theorem B1605157 : Blo 1582489 1605157 := bbase (se 4 (by rfl) ⟨150483, by rfl⟩ : syracuseStep 1605157 = 300967) (by norm_num)
theorem B3563045 : Blo 1582489 3563045 := bbase (se 4 (by rfl) ⟨334035, by rfl⟩ : syracuseStep 3563045 = 668071) (by norm_num)
theorem B2375213 : Blo 1582489 2375213 := bbase (se 3 (by rfl) ⟨445352, by rfl⟩ : syracuseStep 2375213 = 890705) (by norm_num)
theorem B2375237 : Blo 1582489 2375237 := bbase (se 4 (by rfl) ⟨222678, by rfl⟩ : syracuseStep 2375237 = 445357) (by norm_num)
theorem B2375261 : Blo 1582489 2375261 := bbase (se 3 (by rfl) ⟨445361, by rfl⟩ : syracuseStep 2375261 = 890723) (by norm_num)
theorem B3563117 : Blo 1582489 3563117 := bbase (se 3 (by rfl) ⟨668084, by rfl⟩ : syracuseStep 3563117 = 1336169) (by norm_num)
theorem B2375285 : Blo 1582489 2375285 := bbase (se 5 (by rfl) ⟨111341, by rfl⟩ : syracuseStep 2375285 = 222683) (by norm_num)
theorem B3006085 : Blo 1582489 3006085 := bbase (se 4 (by rfl) ⟨281820, by rfl⟩ : syracuseStep 3006085 = 563641) (by norm_num)
theorem B2375309 : Blo 1582489 2375309 := bbase (se 3 (by rfl) ⟨445370, by rfl⟩ : syracuseStep 2375309 = 890741) (by norm_num)
theorem B2408077 : Blo 1582489 2408077 := bbase (se 3 (by rfl) ⟨451514, by rfl⟩ : syracuseStep 2408077 = 903029) (by norm_num)
theorem B2375333 : Blo 1582489 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B3563189 : Blo 1582489 3563189 := bbase (se 5 (by rfl) ⟨167024, by rfl⟩ : syracuseStep 3563189 = 334049) (by norm_num)
theorem B2375357 : Blo 1582489 2375357 := bbase (se 3 (by rfl) ⟨445379, by rfl⟩ : syracuseStep 2375357 = 890759) (by norm_num)
theorem B2375381 : Blo 1582489 2375381 := bbase (se 7 (by rfl) ⟨27836, by rfl⟩ : syracuseStep 2375381 = 55673) (by norm_num)
theorem B2375405 : Blo 1582489 2375405 := bbase (se 3 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 2375405 = 890777) (by norm_num)
theorem B3563261 : Blo 1582489 3563261 := bbase (se 3 (by rfl) ⟨668111, by rfl⟩ : syracuseStep 3563261 = 1336223) (by norm_num)
theorem B2375429 : Blo 1582489 2375429 := bbase (se 4 (by rfl) ⟨222696, by rfl⟩ : syracuseStep 2375429 = 445393) (by norm_num)
theorem B3006229 : Blo 1582489 3006229 := bbase (se 6 (by rfl) ⟨70458, by rfl⟩ : syracuseStep 3006229 = 140917) (by norm_num)
theorem B2375453 : Blo 1582489 2375453 := bbase (se 3 (by rfl) ⟨445397, by rfl⟩ : syracuseStep 2375453 = 890795) (by norm_num)
theorem B9625397 : Blo 1582489 9625397 := bbase (se 5 (by rfl) ⟨451190, by rfl⟩ : syracuseStep 9625397 = 902381) (by norm_num)
theorem B2375477 : Blo 1582489 2375477 := bbase (se 5 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 2375477 = 222701) (by norm_num)
theorem B3563333 : Blo 1582489 3563333 := bbase (se 4 (by rfl) ⟨334062, by rfl⟩ : syracuseStep 3563333 = 668125) (by norm_num)
theorem B2375501 : Blo 1582489 2375501 := bbase (se 3 (by rfl) ⟨445406, by rfl⟩ : syracuseStep 2375501 = 890813) (by norm_num)
theorem B3211093 : Blo 1582489 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B4005733 : Blo 1582489 4005733 := bbase (se 4 (by rfl) ⟨375537, by rfl⟩ : syracuseStep 4005733 = 751075) (by norm_num)
theorem B2375525 : Blo 1582489 2375525 := bbase (se 4 (by rfl) ⟨222705, by rfl⟩ : syracuseStep 2375525 = 445411) (by norm_num)
theorem B2375549 : Blo 1582489 2375549 := bbase (se 3 (by rfl) ⟨445415, by rfl⟩ : syracuseStep 2375549 = 890831) (by norm_num)
theorem B3563405 : Blo 1582489 3563405 := bbase (se 3 (by rfl) ⟨668138, by rfl⟩ : syracuseStep 3563405 = 1336277) (by norm_num)
theorem B2375573 : Blo 1582489 2375573 := bbase (se 6 (by rfl) ⟨55677, by rfl⟩ : syracuseStep 2375573 = 111355) (by norm_num)
theorem B4398997 : Blo 1582489 4398997 := bbase (se 6 (by rfl) ⟨103101, by rfl⟩ : syracuseStep 4398997 = 206203) (by norm_num)
theorem B5070757 : Blo 1582489 5070757 := bbase (se 4 (by rfl) ⟨475383, by rfl⟩ : syracuseStep 5070757 = 950767) (by norm_num)
theorem B2670509 : Blo 1582489 2670509 := bbase (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) (by norm_num)
theorem B2375597 : Blo 1582489 2375597 := bbase (se 3 (by rfl) ⟨445424, by rfl⟩ : syracuseStep 2375597 = 890849) (by norm_num)
theorem B3006389 : Blo 1582489 3006389 := bbase (se 5 (by rfl) ⟨140924, by rfl⟩ : syracuseStep 3006389 = 281849) (by norm_num)
theorem B2408381 : Blo 1582489 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B2375621 : Blo 1582489 2375621 := bbase (se 4 (by rfl) ⟨222714, by rfl⟩ : syracuseStep 2375621 = 445429) (by norm_num)
theorem B4005845 : Blo 1582489 4005845 := bbase (se 7 (by rfl) ⟨46943, by rfl⟩ : syracuseStep 4005845 = 93887) (by norm_num)
theorem B9019349 : Blo 1582489 9019349 := bbase (se 7 (by rfl) ⟨105695, by rfl⟩ : syracuseStep 9019349 = 211391) (by norm_num)
theorem B3563477 : Blo 1582489 3563477 := bbase (se 7 (by rfl) ⟨41759, by rfl⟩ : syracuseStep 3563477 = 83519) (by norm_num)
theorem B2375645 : Blo 1582489 2375645 := bbase (se 3 (by rfl) ⟨445433, by rfl⟩ : syracuseStep 2375645 = 890867) (by norm_num)
theorem B2375669 : Blo 1582489 2375669 := bbase (se 5 (by rfl) ⟨111359, by rfl⟩ : syracuseStep 2375669 = 222719) (by norm_num)
theorem B2375681 : Blo 1582489 2375681 := bstep (se 2 (by rfl) ⟨890880, by rfl⟩ : syracuseStep 2375681 = 1781761) B1781761
theorem B17121293 : Blo 1582489 17121293 := bstep (se 3 (by rfl) ⟨3210242, by rfl⟩ : syracuseStep 17121293 = 6420485) B6420485
theorem B2375699 : Blo 1582489 2375699 := bstep (se 1 (by rfl) ⟨1781774, by rfl⟩ : syracuseStep 2375699 = 3563549) B3563549
theorem B2375729 : Blo 1582489 2375729 := bstep (se 2 (by rfl) ⟨890898, by rfl⟩ : syracuseStep 2375729 = 1781797) B1781797
theorem B2375747 : Blo 1582489 2375747 := bstep (se 1 (by rfl) ⟨1781810, by rfl⟩ : syracuseStep 2375747 = 3563621) B3563621
theorem B2375777 : Blo 1582489 2375777 := bstep (se 2 (by rfl) ⟨890916, by rfl⟩ : syracuseStep 2375777 = 1781833) B1781833
theorem B2670691 : Blo 1582489 2670691 := bstep (se 1 (by rfl) ⟨2003018, by rfl⟩ : syracuseStep 2670691 = 4006037) B4006037
theorem B2375795 : Blo 1582489 2375795 := bstep (se 1 (by rfl) ⟨1781846, by rfl⟩ : syracuseStep 2375795 = 3563693) B3563693
theorem B2375825 : Blo 1582489 2375825 := bstep (se 2 (by rfl) ⟨890934, by rfl⟩ : syracuseStep 2375825 = 1781869) B1781869
theorem B2375843 : Blo 1582489 2375843 := bstep (se 1 (by rfl) ⟨1781882, by rfl⟩ : syracuseStep 2375843 = 3563765) B3563765
theorem B2375873 : Blo 1582489 2375873 := bstep (se 2 (by rfl) ⟨890952, by rfl⟩ : syracuseStep 2375873 = 1781905) B1781905
theorem B8560837 : Blo 1582489 8560837 := bstep (se 4 (by rfl) ⟨802578, by rfl⟩ : syracuseStep 8560837 = 1605157) B1605157
theorem B3563729 : Blo 1582489 3563729 := bstep (se 2 (by rfl) ⟨1336398, by rfl⟩ : syracuseStep 3563729 = 2672797) B2672797
theorem B2375891 : Blo 1582489 2375891 := bstep (se 1 (by rfl) ⟨1781918, by rfl⟩ : syracuseStep 2375891 = 3563837) B3563837
theorem B3563747 : Blo 1582489 3563747 := bstep (se 1 (by rfl) ⟨2672810, by rfl⟩ : syracuseStep 3563747 = 5345621) B5345621
theorem B5488877 : Blo 1582489 5488877 := bstep (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) B2058329
theorem B2670833 : Blo 1582489 2670833 := bstep (se 2 (by rfl) ⟨1001562, by rfl⟩ : syracuseStep 2670833 = 2003125) B2003125
theorem B2375921 : Blo 1582489 2375921 := bstep (se 2 (by rfl) ⟨890970, by rfl⟩ : syracuseStep 2375921 = 1781941) B1781941
theorem B2375939 : Blo 1582489 2375939 := bstep (se 1 (by rfl) ⟨1781954, by rfl⟩ : syracuseStep 2375939 = 3563909) B3563909
theorem B2375969 : Blo 1582489 2375969 := bstep (se 2 (by rfl) ⟨890988, by rfl⟩ : syracuseStep 2375969 = 1781977) B1781977
theorem B5341517 : Blo 1582489 5341517 := bstep (se 3 (by rfl) ⟨1001534, by rfl⟩ : syracuseStep 5341517 = 2003069) B2003069
theorem B4571491 : Blo 1582489 4571491 := bstep (se 1 (by rfl) ⟨3428618, by rfl⟩ : syracuseStep 4571491 = 6857237) B6857237
theorem B2670961 : Blo 1582489 2670961 := bstep (se 2 (by rfl) ⟨1001610, by rfl⟩ : syracuseStep 2670961 = 2003221) B2003221
theorem B5341571 : Blo 1582489 5341571 := bstep (se 1 (by rfl) ⟨4006178, by rfl⟩ : syracuseStep 5341571 = 8012357) B8012357
theorem B9019781 : Blo 1582489 9019781 := bstep (se 4 (by rfl) ⟨845604, by rfl⟩ : syracuseStep 9019781 = 1691209) B1691209
theorem B2670995 : Blo 1582489 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B8012195 : Blo 1582489 8012195 := bstep (se 1 (by rfl) ⟨6009146, by rfl⟩ : syracuseStep 8012195 = 12018293) B12018293
theorem B4063651 : Blo 1582489 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B5415437 : Blo 1582489 5415437 := bstep (se 3 (by rfl) ⟨1015394, by rfl⟩ : syracuseStep 5415437 = 2030789) B2030789
theorem B5071373 : Blo 1582489 5071373 := bstep (se 3 (by rfl) ⟨950882, by rfl⟩ : syracuseStep 5071373 = 1901765) B1901765
theorem B2671123 : Blo 1582489 2671123 := bstep (se 1 (by rfl) ⟨2003342, by rfl⟩ : syracuseStep 2671123 = 4006685) B4006685
theorem B3007057 : Blo 1582489 3007057 := bstep (se 2 (by rfl) ⟨1127646, by rfl⟩ : syracuseStep 3007057 = 2255293) B2255293
theorem B5341841 : Blo 1582489 5341841 := bstep (se 2 (by rfl) ⟨2003190, by rfl⟩ : syracuseStep 5341841 = 4006381) B4006381
theorem B2671265 : Blo 1582489 2671265 := bstep (se 2 (by rfl) ⟨1001724, by rfl⟩ : syracuseStep 2671265 = 2003449) B2003449
theorem B2138881 : Blo 1582489 2138881 := bstep (se 2 (by rfl) ⟨802080, by rfl⟩ : syracuseStep 2138881 = 1604161) B1604161
theorem B2745107 : Blo 1582489 2745107 := bstep (se 1 (by rfl) ⟨2058830, by rfl⟩ : syracuseStep 2745107 = 4117661) B4117661
theorem B2671393 : Blo 1582489 2671393 := bstep (se 2 (by rfl) ⟨1001772, by rfl⟩ : syracuseStep 2671393 = 2003545) B2003545
theorem B4006705 : Blo 1582489 4006705 := bstep (se 2 (by rfl) ⟨1502514, by rfl⟩ : syracuseStep 4006705 = 3005029) B3005029
theorem B2671427 : Blo 1582489 2671427 := bstep (se 1 (by rfl) ⟨2003570, by rfl⟩ : syracuseStep 2671427 = 4007141) B4007141
theorem B1901443 : Blo 1582489 1901443 := bstep (se 1 (by rfl) ⟨1426082, by rfl⟩ : syracuseStep 1901443 = 2852165) B2852165
theorem B2671555 : Blo 1582489 2671555 := bstep (se 1 (by rfl) ⟨2003666, by rfl⟩ : syracuseStep 2671555 = 4007333) B4007333
theorem B4006979 : Blo 1582489 4006979 := bstep (se 1 (by rfl) ⟨3005234, by rfl⟩ : syracuseStep 4006979 = 6010469) B6010469
theorem B2671697 : Blo 1582489 2671697 := bstep (se 2 (by rfl) ⟨1001886, by rfl⟩ : syracuseStep 2671697 = 2003773) B2003773
theorem B6947981 : Blo 1582489 6947981 := bstep (se 3 (by rfl) ⟨1302746, by rfl⟩ : syracuseStep 6947981 = 2605493) B2605493
theorem B8127629 : Blo 1582489 8127629 := bstep (se 3 (by rfl) ⟨1523930, by rfl⟩ : syracuseStep 8127629 = 3047861) B3047861
theorem B4506769 : Blo 1582489 4506769 := bstep (se 2 (by rfl) ⟨1690038, by rfl⟩ : syracuseStep 4506769 = 3380077) B3380077
theorem B5342381 : Blo 1582489 5342381 := bstep (se 3 (by rfl) ⟨1001696, by rfl⟩ : syracuseStep 5342381 = 2003393) B2003393
theorem B8013005 : Blo 1582489 8013005 := bstep (se 3 (by rfl) ⟨1502438, by rfl⟩ : syracuseStep 8013005 = 3004877) B3004877
theorem B2671825 : Blo 1582489 2671825 := bstep (se 2 (by rfl) ⟨1001934, by rfl⟩ : syracuseStep 2671825 = 2003869) B2003869
theorem B5342435 : Blo 1582489 5342435 := bstep (se 1 (by rfl) ⟨4006826, by rfl⟩ : syracuseStep 5342435 = 8013653) B8013653
theorem B2671859 : Blo 1582489 2671859 := bstep (se 1 (by rfl) ⟨2003894, by rfl⟩ : syracuseStep 2671859 = 4007789) B4007789
theorem B4007171 : Blo 1582489 4007171 := bstep (se 1 (by rfl) ⟨3005378, by rfl⟩ : syracuseStep 4007171 = 6010757) B6010757
theorem B2139475 : Blo 1582489 2139475 := bstep (se 1 (by rfl) ⟨1604606, by rfl⟩ : syracuseStep 2139475 = 3209213) B3209213
theorem B2671987 : Blo 1582489 2671987 := bstep (se 1 (by rfl) ⟨2003990, by rfl⟩ : syracuseStep 2671987 = 4007981) B4007981
theorem B1582499 : Blo 1582489 1582499 := bstep (se 1 (by rfl) ⟨1186874, by rfl⟩ : syracuseStep 1582499 = 2373749) B2373749
theorem B1582515 : Blo 1582489 1582515 := bstep (se 1 (by rfl) ⟨1186886, by rfl⟩ : syracuseStep 1582515 = 2373773) B2373773
theorem B1582531 : Blo 1582489 1582531 := bstep (se 1 (by rfl) ⟨1186898, by rfl⟩ : syracuseStep 1582531 = 2373797) B2373797
theorem B1582547 : Blo 1582489 1582547 := bstep (se 1 (by rfl) ⟨1186910, by rfl⟩ : syracuseStep 1582547 = 2373821) B2373821
theorem B1582563 : Blo 1582489 1582563 := bstep (se 1 (by rfl) ⟨1186922, by rfl⟩ : syracuseStep 1582563 = 2373845) B2373845
theorem B5342705 : Blo 1582489 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B1582579 : Blo 1582489 1582579 := bstep (se 1 (by rfl) ⟨1186934, by rfl⟩ : syracuseStep 1582579 = 2373869) B2373869
theorem B2672129 : Blo 1582489 2672129 := bstep (se 2 (by rfl) ⟨1002048, by rfl⟩ : syracuseStep 2672129 = 2004097) B2004097
theorem B1582595 : Blo 1582489 1582595 := bstep (se 1 (by rfl) ⟨1186946, by rfl⟩ : syracuseStep 1582595 = 2373893) B2373893
theorem B6759949 : Blo 1582489 6759949 := bstep (se 3 (by rfl) ⟨1267490, by rfl⟩ : syracuseStep 6759949 = 2534981) B2534981
theorem B1582611 : Blo 1582489 1582611 := bstep (se 1 (by rfl) ⟨1186958, by rfl⟩ : syracuseStep 1582611 = 2373917) B2373917
theorem B1582627 : Blo 1582489 1582627 := bstep (se 1 (by rfl) ⟨1186970, by rfl⟩ : syracuseStep 1582627 = 2373941) B2373941
theorem B1582643 : Blo 1582489 1582643 := bstep (se 1 (by rfl) ⟨1186982, by rfl⟩ : syracuseStep 1582643 = 2373965) B2373965
theorem B2254387 : Blo 1582489 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B1582659 : Blo 1582489 1582659 := bstep (se 1 (by rfl) ⟨1186994, by rfl⟩ : syracuseStep 1582659 = 2373989) B2373989
theorem B1582675 : Blo 1582489 1582675 := bstep (se 1 (by rfl) ⟨1187006, by rfl⟩ : syracuseStep 1582675 = 2374013) B2374013
theorem B2139745 : Blo 1582489 2139745 := bstep (se 2 (by rfl) ⟨802404, by rfl⟩ : syracuseStep 2139745 = 1604809) B1604809
theorem B1582691 : Blo 1582489 1582691 := bstep (se 1 (by rfl) ⟨1187018, by rfl⟩ : syracuseStep 1582691 = 2374037) B2374037
theorem B1582707 : Blo 1582489 1582707 := bstep (se 1 (by rfl) ⟨1187030, by rfl⟩ : syracuseStep 1582707 = 2374061) B2374061
theorem B2672257 : Blo 1582489 2672257 := bstep (se 2 (by rfl) ⟨1002096, by rfl⟩ : syracuseStep 2672257 = 2004193) B2004193
theorem B1582723 : Blo 1582489 1582723 := bstep (se 1 (by rfl) ⟨1187042, by rfl⟩ : syracuseStep 1582723 = 2374085) B2374085
theorem B1582739 : Blo 1582489 1582739 := bstep (se 1 (by rfl) ⟨1187054, by rfl⟩ : syracuseStep 1582739 = 2374109) B2374109
theorem B1582755 : Blo 1582489 1582755 := bstep (se 1 (by rfl) ⟨1187066, by rfl⟩ : syracuseStep 1582755 = 2374133) B2374133
theorem B2672291 : Blo 1582489 2672291 := bstep (se 1 (by rfl) ⟨2004218, by rfl⟩ : syracuseStep 2672291 = 4008437) B4008437
theorem B1582771 : Blo 1582489 1582771 := bstep (se 1 (by rfl) ⟨1187078, by rfl⟩ : syracuseStep 1582771 = 2374157) B2374157
theorem B1582787 : Blo 1582489 1582787 := bstep (se 1 (by rfl) ⟨1187090, by rfl⟩ : syracuseStep 1582787 = 2374181) B2374181
theorem B1582803 : Blo 1582489 1582803 := bstep (se 1 (by rfl) ⟨1187102, by rfl⟩ : syracuseStep 1582803 = 2374205) B2374205
theorem B1582819 : Blo 1582489 1582819 := bstep (se 1 (by rfl) ⟨1187114, by rfl⟩ : syracuseStep 1582819 = 2374229) B2374229
theorem B1582835 : Blo 1582489 1582835 := bstep (se 1 (by rfl) ⟨1187126, by rfl⟩ : syracuseStep 1582835 = 2374253) B2374253
theorem B1582851 : Blo 1582489 1582851 := bstep (se 1 (by rfl) ⟨1187138, by rfl⟩ : syracuseStep 1582851 = 2374277) B2374277
theorem B1582867 : Blo 1582489 1582867 := bstep (se 1 (by rfl) ⟨1187150, by rfl⟩ : syracuseStep 1582867 = 2374301) B2374301
theorem B1582883 : Blo 1582489 1582883 := bstep (se 1 (by rfl) ⟨1187162, by rfl⟩ : syracuseStep 1582883 = 2374325) B2374325
theorem B5416739 : Blo 1582489 5416739 := bstep (se 1 (by rfl) ⟨4062554, by rfl⟩ : syracuseStep 5416739 = 8125109) B8125109
theorem B2672419 : Blo 1582489 2672419 := bstep (se 1 (by rfl) ⟨2004314, by rfl⟩ : syracuseStep 2672419 = 4008629) B4008629
theorem B1582899 : Blo 1582489 1582899 := bstep (se 1 (by rfl) ⟨1187174, by rfl⟩ : syracuseStep 1582899 = 2374349) B2374349
theorem B1582915 : Blo 1582489 1582915 := bstep (se 1 (by rfl) ⟨1187186, by rfl⟩ : syracuseStep 1582915 = 2374373) B2374373
theorem B1582931 : Blo 1582489 1582931 := bstep (se 1 (by rfl) ⟨1187198, by rfl⟩ : syracuseStep 1582931 = 2374397) B2374397
theorem B1582947 : Blo 1582489 1582947 := bstep (se 1 (by rfl) ⟨1187210, by rfl⟩ : syracuseStep 1582947 = 2374421) B2374421
theorem B1582963 : Blo 1582489 1582963 := bstep (se 1 (by rfl) ⟨1187222, by rfl⟩ : syracuseStep 1582963 = 2374445) B2374445
theorem B1582979 : Blo 1582489 1582979 := bstep (se 1 (by rfl) ⟨1187234, by rfl⟩ : syracuseStep 1582979 = 2374469) B2374469
theorem B1582995 : Blo 1582489 1582995 := bstep (se 1 (by rfl) ⟨1187246, by rfl⟩ : syracuseStep 1582995 = 2374493) B2374493
theorem B1583011 : Blo 1582489 1583011 := bstep (se 1 (by rfl) ⟨1187258, by rfl⟩ : syracuseStep 1583011 = 2374517) B2374517
theorem B2672561 : Blo 1582489 2672561 := bstep (se 2 (by rfl) ⟨1002210, by rfl⟩ : syracuseStep 2672561 = 2004421) B2004421
theorem B1583027 : Blo 1582489 1583027 := bstep (se 1 (by rfl) ⟨1187270, by rfl⟩ : syracuseStep 1583027 = 2374541) B2374541
theorem B1583043 : Blo 1582489 1583043 := bstep (se 1 (by rfl) ⟨1187282, by rfl⟩ : syracuseStep 1583043 = 2374565) B2374565
theorem B1583059 : Blo 1582489 1583059 := bstep (se 1 (by rfl) ⟨1187294, by rfl⟩ : syracuseStep 1583059 = 2374589) B2374589
theorem B1583075 : Blo 1582489 1583075 := bstep (se 1 (by rfl) ⟨1187306, by rfl⟩ : syracuseStep 1583075 = 2374613) B2374613
theorem B1583091 : Blo 1582489 1583091 := bstep (se 1 (by rfl) ⟨1187318, by rfl⟩ : syracuseStep 1583091 = 2374637) B2374637
theorem B1583107 : Blo 1582489 1583107 := bstep (se 1 (by rfl) ⟨1187330, by rfl⟩ : syracuseStep 1583107 = 2374661) B2374661
theorem B5343245 : Blo 1582489 5343245 := bstep (se 3 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 5343245 = 2003717) B2003717
theorem B1583123 : Blo 1582489 1583123 := bstep (se 1 (by rfl) ⟨1187342, by rfl⟩ : syracuseStep 1583123 = 2374685) B2374685
theorem B1583139 : Blo 1582489 1583139 := bstep (se 1 (by rfl) ⟨1187354, by rfl⟩ : syracuseStep 1583139 = 2374709) B2374709
theorem B2672689 : Blo 1582489 2672689 := bstep (se 2 (by rfl) ⟨1002258, by rfl⟩ : syracuseStep 2672689 = 2004517) B2004517
theorem B1583155 : Blo 1582489 1583155 := bstep (se 1 (by rfl) ⟨1187366, by rfl⟩ : syracuseStep 1583155 = 2374733) B2374733
theorem B1583171 : Blo 1582489 1583171 := bstep (se 1 (by rfl) ⟨1187378, by rfl⟩ : syracuseStep 1583171 = 2374757) B2374757
theorem B5343299 : Blo 1582489 5343299 := bstep (se 1 (by rfl) ⟨4007474, by rfl⟩ : syracuseStep 5343299 = 8014949) B8014949
theorem B1583187 : Blo 1582489 1583187 := bstep (se 1 (by rfl) ⟨1187390, by rfl⟩ : syracuseStep 1583187 = 2374781) B2374781
theorem B2672723 : Blo 1582489 2672723 := bstep (se 1 (by rfl) ⟨2004542, by rfl⟩ : syracuseStep 2672723 = 4009085) B4009085
theorem B1583203 : Blo 1582489 1583203 := bstep (se 1 (by rfl) ⟨1187402, by rfl⟩ : syracuseStep 1583203 = 2374805) B2374805
theorem B1583219 : Blo 1582489 1583219 := bstep (se 1 (by rfl) ⟨1187414, by rfl⟩ : syracuseStep 1583219 = 2374829) B2374829
theorem B1583235 : Blo 1582489 1583235 := bstep (se 1 (by rfl) ⟨1187426, by rfl⟩ : syracuseStep 1583235 = 2374853) B2374853
theorem B25667725 : Blo 1582489 25667725 := bstep (se 3 (by rfl) ⟨4812698, by rfl⟩ : syracuseStep 25667725 = 9625397) B9625397
theorem B1583251 : Blo 1582489 1583251 := bstep (se 1 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 1583251 = 2374877) B2374877
theorem B1583267 : Blo 1582489 1583267 := bstep (se 1 (by rfl) ⟨1187450, by rfl⟩ : syracuseStep 1583267 = 2374901) B2374901
theorem B4008113 : Blo 1582489 4008113 := bstep (se 2 (by rfl) ⟨1503042, by rfl⟩ : syracuseStep 4008113 = 3006085) B3006085
theorem B1583283 : Blo 1582489 1583283 := bstep (se 1 (by rfl) ⟨1187462, by rfl⟩ : syracuseStep 1583283 = 2374925) B2374925
theorem B1583299 : Blo 1582489 1583299 := bstep (se 1 (by rfl) ⟨1187474, by rfl⟩ : syracuseStep 1583299 = 2374949) B2374949
theorem B1583315 : Blo 1582489 1583315 := bstep (se 1 (by rfl) ⟨1187486, by rfl⟩ : syracuseStep 1583315 = 2374973) B2374973
theorem B2672851 : Blo 1582489 2672851 := bstep (se 1 (by rfl) ⟨2004638, by rfl⟩ : syracuseStep 2672851 = 4009277) B4009277
theorem B1583331 : Blo 1582489 1583331 := bstep (se 1 (by rfl) ⟨1187498, by rfl⟩ : syracuseStep 1583331 = 2374997) B2374997
theorem B4008163 : Blo 1582489 4008163 := bstep (se 1 (by rfl) ⟨3006122, by rfl⟩ : syracuseStep 4008163 = 6012245) B6012245
theorem B1583347 : Blo 1582489 1583347 := bstep (se 1 (by rfl) ⟨1187510, by rfl⟩ : syracuseStep 1583347 = 2375021) B2375021
theorem B3803395 : Blo 1582489 3803395 := bstep (se 1 (by rfl) ⟨2852546, by rfl⟩ : syracuseStep 3803395 = 5705093) B5705093
theorem B1583363 : Blo 1582489 1583363 := bstep (se 1 (by rfl) ⟨1187522, by rfl⟩ : syracuseStep 1583363 = 2375045) B2375045
theorem B9013517 : Blo 1582489 9013517 := bstep (se 3 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 9013517 = 3380069) B3380069
theorem B1583379 : Blo 1582489 1583379 := bstep (se 1 (by rfl) ⟨1187534, by rfl⟩ : syracuseStep 1583379 = 2375069) B2375069
theorem B1583395 : Blo 1582489 1583395 := bstep (se 1 (by rfl) ⟨1187546, by rfl⟩ : syracuseStep 1583395 = 2375093) B2375093
theorem B1583411 : Blo 1582489 1583411 := bstep (se 1 (by rfl) ⟨1187558, by rfl⟩ : syracuseStep 1583411 = 2375117) B2375117
theorem B1583427 : Blo 1582489 1583427 := bstep (se 1 (by rfl) ⟨1187570, by rfl⟩ : syracuseStep 1583427 = 2375141) B2375141
theorem B5343569 : Blo 1582489 5343569 := bstep (se 2 (by rfl) ⟨2003838, by rfl⟩ : syracuseStep 5343569 = 4007677) B4007677
theorem B1583443 : Blo 1582489 1583443 := bstep (se 1 (by rfl) ⟨1187582, by rfl⟩ : syracuseStep 1583443 = 2375165) B2375165
theorem B1583459 : Blo 1582489 1583459 := bstep (se 1 (by rfl) ⟨1187594, by rfl⟩ : syracuseStep 1583459 = 2375189) B2375189
theorem B4008305 : Blo 1582489 4008305 := bstep (se 2 (by rfl) ⟨1503114, by rfl⟩ : syracuseStep 4008305 = 3006229) B3006229
theorem B1583475 : Blo 1582489 1583475 := bstep (se 1 (by rfl) ⟨1187606, by rfl⟩ : syracuseStep 1583475 = 2375213) B2375213
theorem B1583491 : Blo 1582489 1583491 := bstep (se 1 (by rfl) ⟨1187618, by rfl⟩ : syracuseStep 1583491 = 2375237) B2375237
theorem B4508045 : Blo 1582489 4508045 := bstep (se 3 (by rfl) ⟨845258, by rfl⟩ : syracuseStep 4508045 = 1690517) B1690517
theorem B1583507 : Blo 1582489 1583507 := bstep (se 1 (by rfl) ⟨1187630, by rfl⟩ : syracuseStep 1583507 = 2375261) B2375261
theorem B1583523 : Blo 1582489 1583523 := bstep (se 1 (by rfl) ⟨1187642, by rfl⟩ : syracuseStep 1583523 = 2375285) B2375285
theorem B1583539 : Blo 1582489 1583539 := bstep (se 1 (by rfl) ⟨1187654, by rfl⟩ : syracuseStep 1583539 = 2375309) B2375309
theorem B1583555 : Blo 1582489 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B5704141 : Blo 1582489 5704141 := bstep (se 3 (by rfl) ⟨1069526, by rfl⟩ : syracuseStep 5704141 = 2139053) B2139053
theorem B1583571 : Blo 1582489 1583571 := bstep (se 1 (by rfl) ⟨1187678, by rfl⟩ : syracuseStep 1583571 = 2375357) B2375357
theorem B1583587 : Blo 1582489 1583587 := bstep (se 1 (by rfl) ⟨1187690, by rfl⟩ : syracuseStep 1583587 = 2375381) B2375381
theorem B1583603 : Blo 1582489 1583603 := bstep (se 1 (by rfl) ⟨1187702, by rfl⟩ : syracuseStep 1583603 = 2375405) B2375405
theorem B1583619 : Blo 1582489 1583619 := bstep (se 1 (by rfl) ⟨1187714, by rfl⟩ : syracuseStep 1583619 = 2375429) B2375429
theorem B12020237 : Blo 1582489 12020237 := bstep (se 3 (by rfl) ⟨2253794, by rfl⟩ : syracuseStep 12020237 = 4507589) B4507589
theorem B1583635 : Blo 1582489 1583635 := bstep (se 1 (by rfl) ⟨1187726, by rfl⟩ : syracuseStep 1583635 = 2375453) B2375453
theorem B1583651 : Blo 1582489 1583651 := bstep (se 1 (by rfl) ⟨1187738, by rfl⟩ : syracuseStep 1583651 = 2375477) B2375477
theorem B6761009 : Blo 1582489 6761009 := bstep (se 2 (by rfl) ⟨2535378, by rfl⟩ : syracuseStep 6761009 = 5070757) B5070757
theorem B1583667 : Blo 1582489 1583667 := bstep (se 1 (by rfl) ⟨1187750, by rfl⟩ : syracuseStep 1583667 = 2375501) B2375501
theorem B4508227 : Blo 1582489 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B1583683 : Blo 1582489 1583683 := bstep (se 1 (by rfl) ⟨1187762, by rfl⟩ : syracuseStep 1583683 = 2375525) B2375525
theorem B1583699 : Blo 1582489 1583699 := bstep (se 1 (by rfl) ⟨1187774, by rfl⟩ : syracuseStep 1583699 = 2375549) B2375549
theorem B1583715 : Blo 1582489 1583715 := bstep (se 1 (by rfl) ⟨1187786, by rfl⟩ : syracuseStep 1583715 = 2375573) B2375573
theorem B4508273 : Blo 1582489 4508273 := bstep (se 2 (by rfl) ⟨1690602, by rfl⟩ : syracuseStep 4508273 = 3381205) B3381205
theorem B1780339 : Blo 1582489 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B1583731 : Blo 1582489 1583731 := bstep (se 1 (by rfl) ⟨1187798, by rfl⟩ : syracuseStep 1583731 = 2375597) B2375597
theorem B1583747 : Blo 1582489 1583747 := bstep (se 1 (by rfl) ⟨1187810, by rfl⟩ : syracuseStep 1583747 = 2375621) B2375621
theorem B1583763 : Blo 1582489 1583763 := bstep (se 1 (by rfl) ⟨1187822, by rfl⟩ : syracuseStep 1583763 = 2375645) B2375645
theorem B1583779 : Blo 1582489 1583779 := bstep (se 1 (by rfl) ⟨1187834, by rfl⟩ : syracuseStep 1583779 = 2375669) B2375669
theorem B1583795 : Blo 1582489 1583795 := bstep (se 1 (by rfl) ⟨1187846, by rfl⟩ : syracuseStep 1583795 = 2375693) B2375693
theorem B1583811 : Blo 1582489 1583811 := bstep (se 1 (by rfl) ⟨1187858, by rfl⟩ : syracuseStep 1583811 = 2375717) B2375717
theorem B1583827 : Blo 1582489 1583827 := bstep (se 1 (by rfl) ⟨1187870, by rfl⟩ : syracuseStep 1583827 = 2375741) B2375741
theorem B1583843 : Blo 1582489 1583843 := bstep (se 1 (by rfl) ⟨1187882, by rfl⟩ : syracuseStep 1583843 = 2375765) B2375765
theorem B1690355 : Blo 1582489 1690355 := bstep (se 1 (by rfl) ⟨1267766, by rfl⟩ : syracuseStep 1690355 = 2535533) B2535533
theorem B1583859 : Blo 1582489 1583859 := bstep (se 1 (by rfl) ⟨1187894, by rfl⟩ : syracuseStep 1583859 = 2375789) B2375789
theorem B1780483 : Blo 1582489 1780483 := bstep (se 1 (by rfl) ⟨1335362, by rfl⟩ : syracuseStep 1780483 = 2670725) B2670725
theorem B1583875 : Blo 1582489 1583875 := bstep (se 1 (by rfl) ⟨1187906, by rfl⟩ : syracuseStep 1583875 = 2375813) B2375813
theorem B1583891 : Blo 1582489 1583891 := bstep (se 1 (by rfl) ⟨1187918, by rfl⟩ : syracuseStep 1583891 = 2375837) B2375837
theorem B1583907 : Blo 1582489 1583907 := bstep (se 1 (by rfl) ⟨1187930, by rfl⟩ : syracuseStep 1583907 = 2375861) B2375861
theorem B1583923 : Blo 1582489 1583923 := bstep (se 1 (by rfl) ⟨1187942, by rfl⟩ : syracuseStep 1583923 = 2375885) B2375885
theorem B1583939 : Blo 1582489 1583939 := bstep (se 1 (by rfl) ⟨1187954, by rfl⟩ : syracuseStep 1583939 = 2375909) B2375909
theorem B1583955 : Blo 1582489 1583955 := bstep (se 1 (by rfl) ⟨1187966, by rfl⟩ : syracuseStep 1583955 = 2375933) B2375933
theorem B1583971 : Blo 1582489 1583971 := bstep (se 1 (by rfl) ⟨1187978, by rfl⟩ : syracuseStep 1583971 = 2375957) B2375957
theorem B5344109 : Blo 1582489 5344109 := bstep (se 3 (by rfl) ⟨1002020, by rfl⟩ : syracuseStep 5344109 = 2004041) B2004041
theorem B1583987 : Blo 1582489 1583987 := bstep (se 1 (by rfl) ⟨1187990, by rfl⟩ : syracuseStep 1583987 = 2375981) B2375981
theorem B1780627 : Blo 1582489 1780627 := bstep (se 1 (by rfl) ⟨1335470, by rfl⟩ : syracuseStep 1780627 = 2670941) B2670941
theorem B5344163 : Blo 1582489 5344163 := bstep (se 1 (by rfl) ⟨4008122, by rfl⟩ : syracuseStep 5344163 = 8016245) B8016245
theorem B1780771 : Blo 1582489 1780771 := bstep (se 1 (by rfl) ⟨1335578, by rfl⟩ : syracuseStep 1780771 = 2671157) B2671157
theorem B3804241 : Blo 1582489 3804241 := bstep (se 2 (by rfl) ⟨1426590, by rfl⟩ : syracuseStep 3804241 = 2853181) B2853181
theorem B4279405 : Blo 1582489 4279405 := bstep (se 3 (by rfl) ⟨802388, by rfl⟩ : syracuseStep 4279405 = 1604777) B1604777
theorem B9014449 : Blo 1582489 9014449 := bstep (se 2 (by rfl) ⟨3380418, by rfl⟩ : syracuseStep 9014449 = 6760837) B6760837
theorem B5344433 : Blo 1582489 5344433 := bstep (se 2 (by rfl) ⟨2004162, by rfl⟩ : syracuseStep 5344433 = 4008325) B4008325
theorem B1780915 : Blo 1582489 1780915 := bstep (se 1 (by rfl) ⟨1335686, by rfl⟩ : syracuseStep 1780915 = 2671373) B2671373
theorem B3804355 : Blo 1582489 3804355 := bstep (se 1 (by rfl) ⟨2853266, by rfl⟩ : syracuseStep 3804355 = 5706533) B5706533
theorem B1781059 : Blo 1582489 1781059 := bstep (se 1 (by rfl) ⟨1335794, by rfl⟩ : syracuseStep 1781059 = 2671589) B2671589
theorem B4009297 : Blo 1582489 4009297 := bstep (se 2 (by rfl) ⟨1503486, by rfl⟩ : syracuseStep 4009297 = 3006973) B3006973
theorem B1781203 : Blo 1582489 1781203 := bstep (se 1 (by rfl) ⟨1335902, by rfl⟩ : syracuseStep 1781203 = 2671805) B2671805
theorem B8457797 : Blo 1582489 8457797 := bstep (se 4 (by rfl) ⟨792918, by rfl⟩ : syracuseStep 8457797 = 1585837) B1585837
theorem B10145357 : Blo 1582489 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B1781347 : Blo 1582489 1781347 := bstep (se 1 (by rfl) ⟨1336010, by rfl⟩ : syracuseStep 1781347 = 2672021) B2672021
theorem B28880497 : Blo 1582489 28880497 := bstep (se 2 (by rfl) ⟨10830186, by rfl⟩ : syracuseStep 28880497 = 21660373) B21660373
theorem B6008525 : Blo 1582489 6008525 := bstep (se 3 (by rfl) ⟨1126598, by rfl⟩ : syracuseStep 6008525 = 2253197) B2253197
theorem B5344973 : Blo 1582489 5344973 := bstep (se 3 (by rfl) ⟨1002182, by rfl⟩ : syracuseStep 5344973 = 2004365) B2004365
theorem B2535155 : Blo 1582489 2535155 := bstep (se 1 (by rfl) ⟨1901366, by rfl⟩ : syracuseStep 2535155 = 3802733) B3802733
theorem B1781491 : Blo 1582489 1781491 := bstep (se 1 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 1781491 = 2672237) B2672237
theorem B5345027 : Blo 1582489 5345027 := bstep (se 1 (by rfl) ⟨4008770, by rfl⟩ : syracuseStep 5345027 = 8017541) B8017541
theorem B1691491 : Blo 1582489 1691491 := bstep (se 1 (by rfl) ⟨1268618, by rfl⟩ : syracuseStep 1691491 = 2537237) B2537237
theorem B1781635 : Blo 1582489 1781635 := bstep (se 1 (by rfl) ⟨1336226, by rfl⟩ : syracuseStep 1781635 = 2672453) B2672453
theorem B56323981 : Blo 1582489 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B11407301 : Blo 1582489 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B5345297 : Blo 1582489 5345297 := bstep (se 2 (by rfl) ⟨2004486, by rfl⟩ : syracuseStep 5345297 = 4008973) B4008973
theorem B2002963 : Blo 1582489 2002963 := bstep (se 1 (by rfl) ⟨1502222, by rfl⟩ : syracuseStep 2002963 = 3004445) B3004445
theorem B1781779 : Blo 1582489 1781779 := bstep (se 1 (by rfl) ⟨1336334, by rfl⟩ : syracuseStep 1781779 = 2672669) B2672669
theorem B4509731 : Blo 1582489 4509731 := bstep (se 1 (by rfl) ⟨3382298, by rfl⟩ : syracuseStep 4509731 = 6764597) B6764597
theorem B8015921 : Blo 1582489 8015921 := bstep (se 2 (by rfl) ⟨3005970, by rfl⟩ : syracuseStep 8015921 = 6011941) B6011941
theorem B2003059 : Blo 1582489 2003059 := bstep (se 1 (by rfl) ⟨1502294, by rfl⟩ : syracuseStep 2003059 = 3004589) B3004589
theorem B4280465 : Blo 1582489 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B1781923 : Blo 1582489 1781923 := bstep (se 1 (by rfl) ⟨1336442, by rfl⟩ : syracuseStep 1781923 = 2672885) B2672885
theorem B10834211 : Blo 1582489 10834211 := bstep (se 1 (by rfl) ⟨8125658, by rfl⟩ : syracuseStep 10834211 = 16251317) B16251317
theorem B3805585 : Blo 1582489 3805585 := bstep (se 2 (by rfl) ⟨1427094, by rfl⟩ : syracuseStep 3805585 = 2854189) B2854189
theorem B17125829 : Blo 1582489 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B4813283 : Blo 1582489 4813283 := bstep (se 1 (by rfl) ⟨3609962, by rfl⟩ : syracuseStep 4813283 = 7219925) B7219925
theorem B6009329 : Blo 1582489 6009329 := bstep (se 2 (by rfl) ⟨2253498, by rfl⟩ : syracuseStep 6009329 = 4506997) B4506997
theorem B5345837 : Blo 1582489 5345837 := bstep (se 3 (by rfl) ⟨1002344, by rfl⟩ : syracuseStep 5345837 = 2004689) B2004689
theorem B9015907 : Blo 1582489 9015907 := bstep (se 1 (by rfl) ⟨6761930, by rfl⟩ : syracuseStep 9015907 = 13523861) B13523861
theorem B2003555 : Blo 1582489 2003555 := bstep (se 1 (by rfl) ⟨1502666, by rfl⟩ : syracuseStep 2003555 = 3005333) B3005333
theorem B5345891 : Blo 1582489 5345891 := bstep (se 1 (by rfl) ⟨4009418, by rfl⟩ : syracuseStep 5345891 = 8018837) B8018837
theorem B2708129 : Blo 1582489 2708129 := bstep (se 2 (by rfl) ⟨1015548, by rfl⟩ : syracuseStep 2708129 = 2031097) B2031097
theorem B2290339 : Blo 1582489 2290339 := bstep (se 1 (by rfl) ⟨1717754, by rfl⟩ : syracuseStep 2290339 = 3435509) B3435509
theorem B3379907 : Blo 1582489 3379907 := bstep (se 1 (by rfl) ⟨2534930, by rfl⟩ : syracuseStep 3379907 = 5069861) B5069861
theorem B4567889 : Blo 1582489 4567889 := bstep (se 2 (by rfl) ⟨1712958, by rfl⟩ : syracuseStep 4567889 = 3425917) B3425917
theorem B9016433 : Blo 1582489 9016433 := bstep (se 2 (by rfl) ⟨3381162, by rfl⟩ : syracuseStep 9016433 = 6762325) B6762325
theorem B20296817 : Blo 1582489 20296817 := bstep (se 2 (by rfl) ⟨7611306, by rfl⟩ : syracuseStep 20296817 = 15222613) B15222613
theorem B6009997 : Blo 1582489 6009997 := bstep (se 3 (by rfl) ⟨1126874, by rfl⟩ : syracuseStep 6009997 = 2253749) B2253749
theorem B2536609 : Blo 1582489 2536609 := bstep (se 2 (by rfl) ⟨951228, by rfl⟩ : syracuseStep 2536609 = 1902457) B1902457
theorem B2004259 : Blo 1582489 2004259 := bstep (se 1 (by rfl) ⟨1503194, by rfl⟩ : syracuseStep 2004259 = 3006389) B3006389
theorem B12023153 : Blo 1582489 12023153 := bstep (se 2 (by rfl) ⟨4508682, by rfl⟩ : syracuseStep 12023153 = 9017365) B9017365
theorem B2004355 : Blo 1582489 2004355 := bstep (se 1 (by rfl) ⟨1503266, by rfl⟩ : syracuseStep 2004355 = 3006533) B3006533
theorem B3560849 : Blo 1582489 3560849 := bstep (se 2 (by rfl) ⟨1335318, by rfl⟩ : syracuseStep 3560849 = 2670637) B2670637
theorem B3560867 : Blo 1582489 3560867 := bstep (se 1 (by rfl) ⟨2670650, by rfl⟩ : syracuseStep 3560867 = 5341301) B5341301
theorem B15218117 : Blo 1582489 15218117 := bstep (se 4 (by rfl) ⟨1426698, by rfl⟩ : syracuseStep 15218117 = 2853397) B2853397
theorem B6763981 : Blo 1582489 6763981 := bstep (se 3 (by rfl) ⟨1268246, by rfl⟩ : syracuseStep 6763981 = 2536493) B2536493
theorem B8017379 : Blo 1582489 8017379 := bstep (se 1 (by rfl) ⟨6013034, by rfl⟩ : syracuseStep 8017379 = 12026069) B12026069
theorem B4290061 : Blo 1582489 4290061 := bstep (se 3 (by rfl) ⟨804386, by rfl⟩ : syracuseStep 4290061 = 1608773) B1608773
theorem B3380753 : Blo 1582489 3380753 := bstep (se 2 (by rfl) ⟨1267782, by rfl⟩ : syracuseStep 3380753 = 2535565) B2535565
theorem B3561137 : Blo 1582489 3561137 := bstep (se 2 (by rfl) ⟨1335426, by rfl⟩ : syracuseStep 3561137 = 2670853) B2670853
theorem B3856049 : Blo 1582489 3856049 := bstep (se 2 (by rfl) ⟨1446018, by rfl⟩ : syracuseStep 3856049 = 2892037) B2892037
theorem B2709169 : Blo 1582489 2709169 := bstep (se 2 (by rfl) ⟨1015938, by rfl⟩ : syracuseStep 2709169 = 2031877) B2031877
theorem B3561155 : Blo 1582489 3561155 := bstep (se 1 (by rfl) ⟨2670866, by rfl⟩ : syracuseStep 3561155 = 5341733) B5341733
theorem B13014755 : Blo 1582489 13014755 := bstep (se 1 (by rfl) ⟨9761066, by rfl⟩ : syracuseStep 13014755 = 19522133) B19522133
theorem B10147589 : Blo 1582489 10147589 := bstep (se 4 (by rfl) ⟨951336, by rfl⟩ : syracuseStep 10147589 = 1902673) B1902673
theorem B6764323 : Blo 1582489 6764323 := bstep (se 1 (by rfl) ⟨5073242, by rfl⟩ : syracuseStep 6764323 = 10146485) B10146485
theorem B6010787 : Blo 1582489 6010787 := bstep (se 1 (by rfl) ⟨4508090, by rfl⟩ : syracuseStep 6010787 = 9016181) B9016181
theorem B3561425 : Blo 1582489 3561425 := bstep (se 2 (by rfl) ⟨1335534, by rfl⟩ : syracuseStep 3561425 = 2671069) B2671069
theorem B3561443 : Blo 1582489 3561443 := bstep (se 1 (by rfl) ⟨2671082, by rfl⟩ : syracuseStep 3561443 = 5342165) B5342165
theorem B2373761 : Blo 1582489 2373761 := bstep (se 2 (by rfl) ⟨890160, by rfl⟩ : syracuseStep 2373761 = 1780321) B1780321
theorem B2373779 : Blo 1582489 2373779 := bstep (se 1 (by rfl) ⟨1780334, by rfl⟩ : syracuseStep 2373779 = 3560669) B3560669
theorem B2373809 : Blo 1582489 2373809 := bstep (se 2 (by rfl) ⟨890178, by rfl⟩ : syracuseStep 2373809 = 1780357) B1780357
theorem B18036917 : Blo 1582489 18036917 := bstep (se 5 (by rfl) ⟨845480, by rfl⟩ : syracuseStep 18036917 = 1690961) B1690961
theorem B2373827 : Blo 1582489 2373827 := bstep (se 1 (by rfl) ⟨1780370, by rfl⟩ : syracuseStep 2373827 = 3560741) B3560741
theorem B2373857 : Blo 1582489 2373857 := bstep (se 2 (by rfl) ⟨890196, by rfl⟩ : syracuseStep 2373857 = 1780393) B1780393
theorem B3561713 : Blo 1582489 3561713 := bstep (se 2 (by rfl) ⟨1335642, by rfl⟩ : syracuseStep 3561713 = 2671285) B2671285
theorem B2373875 : Blo 1582489 2373875 := bstep (se 1 (by rfl) ⟨1780406, by rfl⟩ : syracuseStep 2373875 = 3560813) B3560813
theorem B3561731 : Blo 1582489 3561731 := bstep (se 1 (by rfl) ⟨2671298, by rfl⟩ : syracuseStep 3561731 = 5342597) B5342597
theorem B8018189 : Blo 1582489 8018189 := bstep (se 3 (by rfl) ⟨1503410, by rfl⟩ : syracuseStep 8018189 = 3006821) B3006821
theorem B2373905 : Blo 1582489 2373905 := bstep (se 2 (by rfl) ⟨890214, by rfl⟩ : syracuseStep 2373905 = 1780429) B1780429
theorem B2373923 : Blo 1582489 2373923 := bstep (se 1 (by rfl) ⟨1780442, by rfl⟩ : syracuseStep 2373923 = 3560885) B3560885
theorem B2373953 : Blo 1582489 2373953 := bstep (se 2 (by rfl) ⟨890232, by rfl⟩ : syracuseStep 2373953 = 1780465) B1780465
theorem B2373971 : Blo 1582489 2373971 := bstep (se 1 (by rfl) ⟨1780478, by rfl⟩ : syracuseStep 2373971 = 3560957) B3560957
theorem B3004771 : Blo 1582489 3004771 := bstep (se 1 (by rfl) ⟨2253578, by rfl⟩ : syracuseStep 3004771 = 4507157) B4507157
theorem B2374001 : Blo 1582489 2374001 := bstep (se 2 (by rfl) ⟨890250, by rfl⟩ : syracuseStep 2374001 = 1780501) B1780501
theorem B2374019 : Blo 1582489 2374019 := bstep (se 1 (by rfl) ⟨1780514, by rfl⟩ : syracuseStep 2374019 = 3561029) B3561029
theorem B2374049 : Blo 1582489 2374049 := bstep (se 2 (by rfl) ⟨890268, by rfl⟩ : syracuseStep 2374049 = 1780537) B1780537
theorem B2374067 : Blo 1582489 2374067 := bstep (se 1 (by rfl) ⟨1780550, by rfl⟩ : syracuseStep 2374067 = 3561101) B3561101
theorem B2374097 : Blo 1582489 2374097 := bstep (se 2 (by rfl) ⟨890286, by rfl⟩ : syracuseStep 2374097 = 1780573) B1780573
theorem B2374115 : Blo 1582489 2374115 := bstep (se 1 (by rfl) ⟨1780586, by rfl⟩ : syracuseStep 2374115 = 3561173) B3561173
theorem B2374145 : Blo 1582489 2374145 := bstep (se 2 (by rfl) ⟨890304, by rfl⟩ : syracuseStep 2374145 = 1780609) B1780609
theorem B3004931 : Blo 1582489 3004931 := bstep (se 1 (by rfl) ⟨2253698, by rfl⟩ : syracuseStep 3004931 = 4507397) B4507397
theorem B3562001 : Blo 1582489 3562001 := bstep (se 2 (by rfl) ⟨1335750, by rfl⟩ : syracuseStep 3562001 = 2671501) B2671501
theorem B2374163 : Blo 1582489 2374163 := bstep (se 1 (by rfl) ⟨1780622, by rfl⟩ : syracuseStep 2374163 = 3561245) B3561245
theorem B3562019 : Blo 1582489 3562019 := bstep (se 1 (by rfl) ⟨2671514, by rfl⟩ : syracuseStep 3562019 = 5343029) B5343029
theorem B9017891 : Blo 1582489 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B2374193 : Blo 1582489 2374193 := bstep (se 2 (by rfl) ⟨890322, by rfl⟩ : syracuseStep 2374193 = 1780645) B1780645
theorem B6011441 : Blo 1582489 6011441 := bstep (se 2 (by rfl) ⟨2254290, by rfl⟩ : syracuseStep 6011441 = 4508581) B4508581
theorem B2374211 : Blo 1582489 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B2374241 : Blo 1582489 2374241 := bstep (se 2 (by rfl) ⟨890340, by rfl⟩ : syracuseStep 2374241 = 1780681) B1780681
theorem B2374259 : Blo 1582489 2374259 := bstep (se 1 (by rfl) ⟨1780694, by rfl⟩ : syracuseStep 2374259 = 3561389) B3561389
theorem B2374289 : Blo 1582489 2374289 := bstep (se 2 (by rfl) ⟨890358, by rfl⟩ : syracuseStep 2374289 = 1780717) B1780717
theorem B2374307 : Blo 1582489 2374307 := bstep (se 1 (by rfl) ⟨1780730, by rfl⟩ : syracuseStep 2374307 = 3561461) B3561461
theorem B2374337 : Blo 1582489 2374337 := bstep (se 2 (by rfl) ⟨890376, by rfl⟩ : syracuseStep 2374337 = 1780753) B1780753
theorem B4815569 : Blo 1582489 4815569 := bstep (se 2 (by rfl) ⟨1805838, by rfl⟩ : syracuseStep 4815569 = 3611677) B3611677
theorem B2374355 : Blo 1582489 2374355 := bstep (se 1 (by rfl) ⟨1780766, by rfl⟩ : syracuseStep 2374355 = 3561533) B3561533
theorem B2374385 : Blo 1582489 2374385 := bstep (se 2 (by rfl) ⟨890394, by rfl⟩ : syracuseStep 2374385 = 1780789) B1780789
theorem B2407153 : Blo 1582489 2407153 := bstep (se 2 (by rfl) ⟨902682, by rfl⟩ : syracuseStep 2407153 = 1805365) B1805365
theorem B2374403 : Blo 1582489 2374403 := bstep (se 1 (by rfl) ⟨1780802, by rfl⟩ : syracuseStep 2374403 = 3561605) B3561605
theorem B2374433 : Blo 1582489 2374433 := bstep (se 2 (by rfl) ⟨890412, by rfl⟩ : syracuseStep 2374433 = 1780825) B1780825
theorem B3562289 : Blo 1582489 3562289 := bstep (se 2 (by rfl) ⟨1335858, by rfl⟩ : syracuseStep 3562289 = 2671717) B2671717
theorem B2374451 : Blo 1582489 2374451 := bstep (se 1 (by rfl) ⟨1780838, by rfl⟩ : syracuseStep 2374451 = 3561677) B3561677
theorem B3562307 : Blo 1582489 3562307 := bstep (se 1 (by rfl) ⟨2671730, by rfl⟩ : syracuseStep 3562307 = 5343461) B5343461
theorem B2374481 : Blo 1582489 2374481 := bstep (se 2 (by rfl) ⟨890430, by rfl⟩ : syracuseStep 2374481 = 1780861) B1780861
theorem B2374499 : Blo 1582489 2374499 := bstep (se 1 (by rfl) ⟨1780874, by rfl⟩ : syracuseStep 2374499 = 3561749) B3561749
theorem B2374529 : Blo 1582489 2374529 := bstep (se 2 (by rfl) ⟨890448, by rfl⟩ : syracuseStep 2374529 = 1780897) B1780897
theorem B86645645 : Blo 1582489 86645645 := bstep (se 3 (by rfl) ⟨16246058, by rfl⟩ : syracuseStep 86645645 = 32492117) B32492117
theorem B2374547 : Blo 1582489 2374547 := bstep (se 1 (by rfl) ⟨1780910, by rfl⟩ : syracuseStep 2374547 = 3561821) B3561821
theorem B2374577 : Blo 1582489 2374577 := bstep (se 2 (by rfl) ⟨890466, by rfl⟩ : syracuseStep 2374577 = 1780933) B1780933
theorem B2374595 : Blo 1582489 2374595 := bstep (se 1 (by rfl) ⟨1780946, by rfl⟩ : syracuseStep 2374595 = 3561893) B3561893
theorem B31267781 : Blo 1582489 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B2374625 : Blo 1582489 2374625 := bstep (se 2 (by rfl) ⟨890484, by rfl⟩ : syracuseStep 2374625 = 1780969) B1780969
theorem B2407409 : Blo 1582489 2407409 := bstep (se 2 (by rfl) ⟨902778, by rfl⟩ : syracuseStep 2407409 = 1805557) B1805557
theorem B2374643 : Blo 1582489 2374643 := bstep (se 1 (by rfl) ⟨1780982, by rfl⟩ : syracuseStep 2374643 = 3561965) B3561965
theorem B2374673 : Blo 1582489 2374673 := bstep (se 2 (by rfl) ⟨890502, by rfl⟩ : syracuseStep 2374673 = 1781005) B1781005
theorem B2374691 : Blo 1582489 2374691 := bstep (se 1 (by rfl) ⟨1781018, by rfl⟩ : syracuseStep 2374691 = 3562037) B3562037
theorem B2374721 : Blo 1582489 2374721 := bstep (se 2 (by rfl) ⟨890520, by rfl⟩ : syracuseStep 2374721 = 1781041) B1781041
theorem B4815949 : Blo 1582489 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B3562577 : Blo 1582489 3562577 := bstep (se 2 (by rfl) ⟨1335966, by rfl⟩ : syracuseStep 3562577 = 2671933) B2671933
theorem B2374739 : Blo 1582489 2374739 := bstep (se 1 (by rfl) ⟨1781054, by rfl⟩ : syracuseStep 2374739 = 3562109) B3562109
theorem B3562595 : Blo 1582489 3562595 := bstep (se 1 (by rfl) ⟨2671946, by rfl⟩ : syracuseStep 3562595 = 5343893) B5343893
theorem B2374769 : Blo 1582489 2374769 := bstep (se 2 (by rfl) ⟨890538, by rfl⟩ : syracuseStep 2374769 = 1781077) B1781077
theorem B2374787 : Blo 1582489 2374787 := bstep (se 1 (by rfl) ⟨1781090, by rfl⟩ : syracuseStep 2374787 = 3562181) B3562181
theorem B2374817 : Blo 1582489 2374817 := bstep (se 2 (by rfl) ⟨890556, by rfl⟩ : syracuseStep 2374817 = 1781113) B1781113
theorem B3382435 : Blo 1582489 3382435 := bstep (se 1 (by rfl) ⟨2536826, by rfl⟩ : syracuseStep 3382435 = 5073653) B5073653
theorem B2374835 : Blo 1582489 2374835 := bstep (se 1 (by rfl) ⟨1781126, by rfl⟩ : syracuseStep 2374835 = 3562253) B3562253
theorem B2374865 : Blo 1582489 2374865 := bstep (se 2 (by rfl) ⟨890574, by rfl⟩ : syracuseStep 2374865 = 1781149) B1781149
theorem B2374883 : Blo 1582489 2374883 := bstep (se 1 (by rfl) ⟨1781162, by rfl⟩ : syracuseStep 2374883 = 3562325) B3562325
theorem B2374913 : Blo 1582489 2374913 := bstep (se 2 (by rfl) ⟨890592, by rfl⟩ : syracuseStep 2374913 = 1781185) B1781185
theorem B10419461 : Blo 1582489 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B2284817 : Blo 1582489 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B2374931 : Blo 1582489 2374931 := bstep (se 1 (by rfl) ⟨1781198, by rfl⟩ : syracuseStep 2374931 = 3562397) B3562397
theorem B2374961 : Blo 1582489 2374961 := bstep (se 2 (by rfl) ⟨890610, by rfl⟩ : syracuseStep 2374961 = 1781221) B1781221
theorem B2374979 : Blo 1582489 2374979 := bstep (se 1 (by rfl) ⟨1781234, by rfl⟩ : syracuseStep 2374979 = 3562469) B3562469
theorem B7224653 : Blo 1582489 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B2375009 : Blo 1582489 2375009 := bstep (se 2 (by rfl) ⟨890628, by rfl⟩ : syracuseStep 2375009 = 1781257) B1781257
theorem B3562865 : Blo 1582489 3562865 := bstep (se 2 (by rfl) ⟨1336074, by rfl⟩ : syracuseStep 3562865 = 2672149) B2672149
theorem B2375027 : Blo 1582489 2375027 := bstep (se 1 (by rfl) ⟨1781270, by rfl⟩ : syracuseStep 2375027 = 3562541) B3562541
theorem B3562883 : Blo 1582489 3562883 := bstep (se 1 (by rfl) ⟨2672162, by rfl⟩ : syracuseStep 3562883 = 5344325) B5344325
theorem B2375057 : Blo 1582489 2375057 := bstep (se 2 (by rfl) ⟨890646, by rfl⟩ : syracuseStep 2375057 = 1781293) B1781293
theorem B2375075 : Blo 1582489 2375075 := bstep (se 1 (by rfl) ⟨1781306, by rfl⟩ : syracuseStep 2375075 = 3562613) B3562613
theorem B2375105 : Blo 1582489 2375105 := bstep (se 2 (by rfl) ⟨890664, by rfl⟩ : syracuseStep 2375105 = 1781329) B1781329
theorem B2375123 : Blo 1582489 2375123 := bstep (se 1 (by rfl) ⟨1781342, by rfl⟩ : syracuseStep 2375123 = 3562685) B3562685
theorem B2375153 : Blo 1582489 2375153 := bstep (se 2 (by rfl) ⟨890682, by rfl⟩ : syracuseStep 2375153 = 1781365) B1781365
theorem B2375171 : Blo 1582489 2375171 := bstep (se 1 (by rfl) ⟨1781378, by rfl⟩ : syracuseStep 2375171 = 3562757) B3562757
theorem B4816397 : Blo 1582489 4816397 := bstep (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) B1806149
theorem B3210769 : Blo 1582489 3210769 := bstep (se 2 (by rfl) ⟨1204038, by rfl⟩ : syracuseStep 3210769 = 2408077) B2408077
theorem B2375201 : Blo 1582489 2375201 := bstep (se 2 (by rfl) ⟨890700, by rfl⟩ : syracuseStep 2375201 = 1781401) B1781401
theorem B3006001 : Blo 1582489 3006001 := bstep (se 2 (by rfl) ⟨1127250, by rfl⟩ : syracuseStep 3006001 = 2254501) B2254501
theorem B2375219 : Blo 1582489 2375219 := bstep (se 1 (by rfl) ⟨1781414, by rfl⟩ : syracuseStep 2375219 = 3562829) B3562829
theorem B2375249 : Blo 1582489 2375249 := bstep (se 2 (by rfl) ⟨890718, by rfl⟩ : syracuseStep 2375249 = 1781437) B1781437
theorem B2375267 : Blo 1582489 2375267 := bstep (se 1 (by rfl) ⟨1781450, by rfl⟩ : syracuseStep 2375267 = 3562901) B3562901
theorem B3382897 : Blo 1582489 3382897 := bstep (se 2 (by rfl) ⟨1268586, by rfl⟩ : syracuseStep 3382897 = 2537173) B2537173
theorem B2375297 : Blo 1582489 2375297 := bstep (se 2 (by rfl) ⟨890736, by rfl⟩ : syracuseStep 2375297 = 1781473) B1781473
theorem B3563153 : Blo 1582489 3563153 := bstep (se 2 (by rfl) ⟨1336182, by rfl⟩ : syracuseStep 3563153 = 2672365) B2672365
theorem B2375315 : Blo 1582489 2375315 := bstep (se 1 (by rfl) ⟨1781486, by rfl⟩ : syracuseStep 2375315 = 3562973) B3562973
theorem B3563171 : Blo 1582489 3563171 := bstep (se 1 (by rfl) ⟨2672378, by rfl⟩ : syracuseStep 3563171 = 5344757) B5344757
theorem B10141361 : Blo 1582489 10141361 := bstep (se 2 (by rfl) ⟨3803010, by rfl⟩ : syracuseStep 10141361 = 7606021) B7606021
theorem B2375345 : Blo 1582489 2375345 := bstep (se 2 (by rfl) ⟨890754, by rfl⟩ : syracuseStep 2375345 = 1781509) B1781509
theorem B2375363 : Blo 1582489 2375363 := bstep (se 1 (by rfl) ⟨1781522, by rfl⟩ : syracuseStep 2375363 = 3563045) B3563045
theorem B2375393 : Blo 1582489 2375393 := bstep (se 2 (by rfl) ⟨890772, by rfl⟩ : syracuseStep 2375393 = 1781545) B1781545
theorem B30432995 : Blo 1582489 30432995 := bstep (se 1 (by rfl) ⟨22824746, by rfl⟩ : syracuseStep 30432995 = 45649493) B45649493
theorem B2375411 : Blo 1582489 2375411 := bstep (se 1 (by rfl) ⟨1781558, by rfl⟩ : syracuseStep 2375411 = 3563117) B3563117
theorem B5414669 : Blo 1582489 5414669 := bstep (se 3 (by rfl) ⟨1015250, by rfl⟩ : syracuseStep 5414669 = 2030501) B2030501
theorem B2375441 : Blo 1582489 2375441 := bstep (se 2 (by rfl) ⟨890790, by rfl⟩ : syracuseStep 2375441 = 1781581) B1781581
theorem B2375459 : Blo 1582489 2375459 := bstep (se 1 (by rfl) ⟨1781594, by rfl⟩ : syracuseStep 2375459 = 3563189) B3563189
theorem B5340977 : Blo 1582489 5340977 := bstep (se 2 (by rfl) ⟨2002866, by rfl⟩ : syracuseStep 5340977 = 4005733) B4005733
theorem B2375489 : Blo 1582489 2375489 := bstep (se 2 (by rfl) ⟨890808, by rfl⟩ : syracuseStep 2375489 = 1781617) B1781617
theorem B4005713 : Blo 1582489 4005713 := bstep (se 2 (by rfl) ⟨1502142, by rfl⟩ : syracuseStep 4005713 = 3004285) B3004285
theorem B2375507 : Blo 1582489 2375507 := bstep (se 1 (by rfl) ⟨1781630, by rfl⟩ : syracuseStep 2375507 = 3563261) B3563261
theorem B2375537 : Blo 1582489 2375537 := bstep (se 2 (by rfl) ⟨890826, by rfl⟩ : syracuseStep 2375537 = 1781653) B1781653
theorem B5865329 : Blo 1582489 5865329 := bstep (se 2 (by rfl) ⟨2199498, by rfl⟩ : syracuseStep 5865329 = 4398997) B4398997
theorem B2375555 : Blo 1582489 2375555 := bstep (se 1 (by rfl) ⟨1781666, by rfl⟩ : syracuseStep 2375555 = 3563333) B3563333
theorem B2375585 : Blo 1582489 2375585 := bstep (se 2 (by rfl) ⟨890844, by rfl⟩ : syracuseStep 2375585 = 1781689) B1781689
theorem B3563441 : Blo 1582489 3563441 := bstep (se 2 (by rfl) ⟨1336290, by rfl⟩ : syracuseStep 3563441 = 2672581) B2672581
theorem B2375603 : Blo 1582489 2375603 := bstep (se 1 (by rfl) ⟨1781702, by rfl⟩ : syracuseStep 2375603 = 3563405) B3563405
theorem B2670529 : Blo 1582489 2670529 := bstep (se 2 (by rfl) ⟨1001448, by rfl⟩ : syracuseStep 2670529 = 2002897) B2002897
theorem B3563459 : Blo 1582489 3563459 := bstep (se 1 (by rfl) ⟨2672594, by rfl⟩ : syracuseStep 3563459 = 5345189) B5345189
theorem B2375633 : Blo 1582489 2375633 := bstep (se 2 (by rfl) ⟨890862, by rfl⟩ : syracuseStep 2375633 = 1781725) B1781725
theorem B1605587 : Blo 1582489 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B2670563 : Blo 1582489 2670563 := bstep (se 1 (by rfl) ⟨2002922, by rfl⟩ : syracuseStep 2670563 = 4005845) B4005845
theorem B6012899 : Blo 1582489 6012899 := bstep (se 1 (by rfl) ⟨4509674, by rfl⟩ : syracuseStep 6012899 = 9019349) B9019349
theorem B2375651 : Blo 1582489 2375651 := bstep (se 1 (by rfl) ⟨1781738, by rfl⟩ : syracuseStep 2375651 = 3563477) B3563477
theorem B6012913 : Blo 1582489 6012913 := bstep (se 2 (by rfl) ⟨2254842, by rfl⟩ : syracuseStep 6012913 = 4509685) B4509685
theorem B3563531 : Blo 1582489 3563531 := bstep (se 1 (by rfl) ⟨2672648, by rfl⟩ : syracuseStep 3563531 = 5345297) B5345297
theorem B3006487 : Blo 1582489 3006487 := bstep (se 1 (by rfl) ⟨2254865, by rfl⟩ : syracuseStep 3006487 = 4509731) B4509731
theorem B2670617 : Blo 1582489 2670617 := bstep (se 2 (by rfl) ⟨1001481, by rfl⟩ : syracuseStep 2670617 = 2002963) B2002963
theorem B2375705 : Blo 1582489 2375705 := bstep (se 2 (by rfl) ⟨890889, by rfl⟩ : syracuseStep 2375705 = 1781779) B1781779
theorem B3563585 : Blo 1582489 3563585 := bstep (se 2 (by rfl) ⟨1336344, by rfl⟩ : syracuseStep 3563585 = 2672689) B2672689
theorem B2375819 : Blo 1582489 2375819 := bstep (se 1 (by rfl) ⟨1781864, by rfl⟩ : syracuseStep 2375819 = 3563729) B3563729
theorem B2375831 : Blo 1582489 2375831 := bstep (se 1 (by rfl) ⟨1781873, by rfl⟩ : syracuseStep 2375831 = 3563747) B3563747
theorem B2670745 : Blo 1582489 2670745 := bstep (se 2 (by rfl) ⟨1001529, by rfl⟩ : syracuseStep 2670745 = 2003059) B2003059
theorem B24371381 : Blo 1582489 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B2375897 : Blo 1582489 2375897 := bstep (se 2 (by rfl) ⟨890961, by rfl⟩ : syracuseStep 2375897 = 1781923) B1781923
theorem B6013187 : Blo 1582489 6013187 := bstep (se 1 (by rfl) ⟨4509890, by rfl⟩ : syracuseStep 6013187 = 9019781) B9019781
theorem B5341463 : Blo 1582489 5341463 := bstep (se 1 (by rfl) ⟨4006097, by rfl⟩ : syracuseStep 5341463 = 8012195) B8012195
theorem B3563801 : Blo 1582489 3563801 := bstep (se 2 (by rfl) ⟨1336425, by rfl⟩ : syracuseStep 3563801 = 2672851) B2672851
theorem B4006219 : Blo 1582489 4006219 := bstep (se 1 (by rfl) ⟨3004664, by rfl⟩ : syracuseStep 4006219 = 6009329) B6009329
theorem B5071193 : Blo 1582489 5071193 := bstep (se 2 (by rfl) ⟨1901697, by rfl⟩ : syracuseStep 5071193 = 3803395) B3803395
theorem B3563891 : Blo 1582489 3563891 := bstep (se 1 (by rfl) ⟨2672918, by rfl⟩ : syracuseStep 3563891 = 5345837) B5345837
theorem B3563927 : Blo 1582489 3563927 := bstep (se 1 (by rfl) ⟨2672945, by rfl⟩ : syracuseStep 3563927 = 5345891) B5345891
theorem B2253271 : Blo 1582489 2253271 := bstep (se 1 (by rfl) ⟨1689953, by rfl⟩ : syracuseStep 2253271 = 3379907) B3379907
theorem B4006361 : Blo 1582489 4006361 := bstep (se 2 (by rfl) ⟨1502385, by rfl⟩ : syracuseStep 4006361 = 3004771) B3004771
theorem B6095321 : Blo 1582489 6095321 := bstep (se 2 (by rfl) ⟨2285745, by rfl⟩ : syracuseStep 6095321 = 4571491) B4571491
theorem B2671319 : Blo 1582489 2671319 := bstep (se 1 (by rfl) ⟨2003489, by rfl⟩ : syracuseStep 2671319 = 4006979) B4006979
theorem B5342003 : Blo 1582489 5342003 := bstep (se 1 (by rfl) ⟨4006502, by rfl⟩ : syracuseStep 5342003 = 8013005) B8013005
theorem B2671447 : Blo 1582489 2671447 := bstep (se 1 (by rfl) ⟨2003585, by rfl⟩ : syracuseStep 2671447 = 4007171) B4007171
theorem B2851841 : Blo 1582489 2851841 := bstep (se 2 (by rfl) ⟨1069440, by rfl⟩ : syracuseStep 2851841 = 2138881) B2138881
theorem B2253835 : Blo 1582489 2253835 := bstep (se 1 (by rfl) ⟨1690376, by rfl⟩ : syracuseStep 2253835 = 3380753) B3380753
theorem B5342273 : Blo 1582489 5342273 := bstep (se 2 (by rfl) ⟨2003352, by rfl⟩ : syracuseStep 5342273 = 4006705) B4006705
theorem B8676503 : Blo 1582489 8676503 := bstep (se 1 (by rfl) ⟨6507377, by rfl⟩ : syracuseStep 8676503 = 13014755) B13014755
theorem B4007191 : Blo 1582489 4007191 := bstep (se 1 (by rfl) ⟨3005393, by rfl⟩ : syracuseStep 4007191 = 6010787) B6010787
theorem B1582507 : Blo 1582489 1582507 := bstep (se 1 (by rfl) ⟨1186880, by rfl⟩ : syracuseStep 1582507 = 2373761) B2373761
theorem B1582519 : Blo 1582489 1582519 := bstep (se 1 (by rfl) ⟨1186889, by rfl⟩ : syracuseStep 1582519 = 2373779) B2373779
theorem B5072321 : Blo 1582489 5072321 := bstep (se 2 (by rfl) ⟨1902120, by rfl⟩ : syracuseStep 5072321 = 3804241) B3804241
theorem B1582539 : Blo 1582489 1582539 := bstep (se 1 (by rfl) ⟨1186904, by rfl⟩ : syracuseStep 1582539 = 2373809) B2373809
theorem B2672075 : Blo 1582489 2672075 := bstep (se 1 (by rfl) ⟨2004056, by rfl⟩ : syracuseStep 2672075 = 4008113) B4008113
theorem B1582551 : Blo 1582489 1582551 := bstep (se 1 (by rfl) ⟨1186913, by rfl⟩ : syracuseStep 1582551 = 2373827) B2373827
theorem B1582571 : Blo 1582489 1582571 := bstep (se 1 (by rfl) ⟨1186928, by rfl⟩ : syracuseStep 1582571 = 2373857) B2373857
theorem B1582583 : Blo 1582489 1582583 := bstep (se 1 (by rfl) ⟨1186937, by rfl⟩ : syracuseStep 1582583 = 2373875) B2373875
theorem B1582603 : Blo 1582489 1582603 := bstep (se 1 (by rfl) ⟨1186952, by rfl⟩ : syracuseStep 1582603 = 2373905) B2373905
theorem B8013329 : Blo 1582489 8013329 := bstep (se 2 (by rfl) ⟨3004998, by rfl⟩ : syracuseStep 8013329 = 6009997) B6009997
theorem B1582615 : Blo 1582489 1582615 := bstep (se 1 (by rfl) ⟨1186961, by rfl⟩ : syracuseStep 1582615 = 2373923) B2373923
theorem B1582635 : Blo 1582489 1582635 := bstep (se 1 (by rfl) ⟨1186976, by rfl⟩ : syracuseStep 1582635 = 2373953) B2373953
theorem B1582647 : Blo 1582489 1582647 := bstep (se 1 (by rfl) ⟨1186985, by rfl⟩ : syracuseStep 1582647 = 2373971) B2373971
theorem B12019265 : Blo 1582489 12019265 := bstep (se 2 (by rfl) ⟨4507224, by rfl⟩ : syracuseStep 12019265 = 9014449) B9014449
theorem B1582667 : Blo 1582489 1582667 := bstep (se 1 (by rfl) ⟨1187000, by rfl⟩ : syracuseStep 1582667 = 2374001) B2374001
theorem B2672203 : Blo 1582489 2672203 := bstep (se 1 (by rfl) ⟨2004152, by rfl⟩ : syracuseStep 2672203 = 4008305) B4008305
theorem B1582679 : Blo 1582489 1582679 := bstep (se 1 (by rfl) ⟨1187009, by rfl⟩ : syracuseStep 1582679 = 2374019) B2374019
theorem B5072473 : Blo 1582489 5072473 := bstep (se 2 (by rfl) ⟨1902177, by rfl⟩ : syracuseStep 5072473 = 3804355) B3804355
theorem B5342813 : Blo 1582489 5342813 := bstep (se 3 (by rfl) ⟨1001777, by rfl⟩ : syracuseStep 5342813 = 2003555) B2003555
theorem B1582699 : Blo 1582489 1582699 := bstep (se 1 (by rfl) ⟨1187024, by rfl⟩ : syracuseStep 1582699 = 2374049) B2374049
theorem B1582711 : Blo 1582489 1582711 := bstep (se 1 (by rfl) ⟨1187033, by rfl⟩ : syracuseStep 1582711 = 2374067) B2374067
theorem B1582731 : Blo 1582489 1582731 := bstep (se 1 (by rfl) ⟨1187048, by rfl⟩ : syracuseStep 1582731 = 2374097) B2374097
theorem B1582743 : Blo 1582489 1582743 := bstep (se 1 (by rfl) ⟨1187057, by rfl⟩ : syracuseStep 1582743 = 2374115) B2374115
theorem B1582763 : Blo 1582489 1582763 := bstep (se 1 (by rfl) ⟨1187072, by rfl⟩ : syracuseStep 1582763 = 2374145) B2374145
theorem B8013491 : Blo 1582489 8013491 := bstep (se 1 (by rfl) ⟨6010118, by rfl⟩ : syracuseStep 8013491 = 12020237) B12020237
theorem B1582775 : Blo 1582489 1582775 := bstep (se 1 (by rfl) ⟨1187081, by rfl⟩ : syracuseStep 1582775 = 2374163) B2374163
theorem B1582795 : Blo 1582489 1582795 := bstep (se 1 (by rfl) ⟨1187096, by rfl⟩ : syracuseStep 1582795 = 2374193) B2374193
theorem B4507339 : Blo 1582489 4507339 := bstep (se 1 (by rfl) ⟨3380504, by rfl⟩ : syracuseStep 4507339 = 6761009) B6761009
theorem B4007627 : Blo 1582489 4007627 := bstep (se 1 (by rfl) ⟨3005720, by rfl⟩ : syracuseStep 4007627 = 6011441) B6011441
theorem B1582807 : Blo 1582489 1582807 := bstep (se 1 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 1582807 = 2374211) B2374211
theorem B2672345 : Blo 1582489 2672345 := bstep (se 2 (by rfl) ⟨1002129, by rfl⟩ : syracuseStep 2672345 = 2004259) B2004259
theorem B1582827 : Blo 1582489 1582827 := bstep (se 1 (by rfl) ⟨1187120, by rfl⟩ : syracuseStep 1582827 = 2374241) B2374241
theorem B1582839 : Blo 1582489 1582839 := bstep (se 1 (by rfl) ⟨1187129, by rfl⟩ : syracuseStep 1582839 = 2374259) B2374259
theorem B1582859 : Blo 1582489 1582859 := bstep (se 1 (by rfl) ⟨1187144, by rfl⟩ : syracuseStep 1582859 = 2374289) B2374289
theorem B1582871 : Blo 1582489 1582871 := bstep (se 1 (by rfl) ⟨1187153, by rfl⟩ : syracuseStep 1582871 = 2374307) B2374307
theorem B2852633 : Blo 1582489 2852633 := bstep (se 2 (by rfl) ⟨1069737, by rfl⟩ : syracuseStep 2852633 = 2139475) B2139475
theorem B1582891 : Blo 1582489 1582891 := bstep (se 1 (by rfl) ⟨1187168, by rfl⟩ : syracuseStep 1582891 = 2374337) B2374337
theorem B1582903 : Blo 1582489 1582903 := bstep (se 1 (by rfl) ⟨1187177, by rfl⟩ : syracuseStep 1582903 = 2374355) B2374355
theorem B1582923 : Blo 1582489 1582923 := bstep (se 1 (by rfl) ⟨1187192, by rfl⟩ : syracuseStep 1582923 = 2374385) B2374385
theorem B1582935 : Blo 1582489 1582935 := bstep (se 1 (by rfl) ⟨1187201, by rfl⟩ : syracuseStep 1582935 = 2374403) B2374403
theorem B2672473 : Blo 1582489 2672473 := bstep (se 2 (by rfl) ⟨1002177, by rfl⟩ : syracuseStep 2672473 = 2004355) B2004355
theorem B1582955 : Blo 1582489 1582955 := bstep (se 1 (by rfl) ⟨1187216, by rfl⟩ : syracuseStep 1582955 = 2374433) B2374433
theorem B1582967 : Blo 1582489 1582967 := bstep (se 1 (by rfl) ⟨1187225, by rfl⟩ : syracuseStep 1582967 = 2374451) B2374451
theorem B1582987 : Blo 1582489 1582987 := bstep (se 1 (by rfl) ⟨1187240, by rfl⟩ : syracuseStep 1582987 = 2374481) B2374481
theorem B1582999 : Blo 1582489 1582999 := bstep (se 1 (by rfl) ⟨1187249, by rfl⟩ : syracuseStep 1582999 = 2374499) B2374499
theorem B1583019 : Blo 1582489 1583019 := bstep (se 1 (by rfl) ⟨1187264, by rfl⟩ : syracuseStep 1583019 = 2374529) B2374529
theorem B57763763 : Blo 1582489 57763763 := bstep (se 1 (by rfl) ⟨43322822, by rfl⟩ : syracuseStep 57763763 = 86645645) B86645645
theorem B1583031 : Blo 1582489 1583031 := bstep (se 1 (by rfl) ⟨1187273, by rfl⟩ : syracuseStep 1583031 = 2374547) B2374547
theorem B1583051 : Blo 1582489 1583051 := bstep (se 1 (by rfl) ⟨1187288, by rfl⟩ : syracuseStep 1583051 = 2374577) B2374577
theorem B1583063 : Blo 1582489 1583063 := bstep (se 1 (by rfl) ⟨1187297, by rfl⟩ : syracuseStep 1583063 = 2374595) B2374595
theorem B4507613 : Blo 1582489 4507613 := bstep (se 3 (by rfl) ⟨845177, by rfl⟩ : syracuseStep 4507613 = 1690355) B1690355
theorem B1583083 : Blo 1582489 1583083 := bstep (se 1 (by rfl) ⟨1187312, by rfl⟩ : syracuseStep 1583083 = 2374625) B2374625
theorem B1583095 : Blo 1582489 1583095 := bstep (se 1 (by rfl) ⟨1187321, by rfl⟩ : syracuseStep 1583095 = 2374643) B2374643
theorem B1583115 : Blo 1582489 1583115 := bstep (se 1 (by rfl) ⟨1187336, by rfl⟩ : syracuseStep 1583115 = 2374673) B2374673
theorem B9013265 : Blo 1582489 9013265 := bstep (se 2 (by rfl) ⟨3379974, by rfl⟩ : syracuseStep 9013265 = 6759949) B6759949
theorem B5720081 : Blo 1582489 5720081 := bstep (se 2 (by rfl) ⟨2145030, by rfl⟩ : syracuseStep 5720081 = 4290061) B4290061
theorem B1583127 : Blo 1582489 1583127 := bstep (se 1 (by rfl) ⟨1187345, by rfl⟩ : syracuseStep 1583127 = 2374691) B2374691
theorem B1583147 : Blo 1582489 1583147 := bstep (se 1 (by rfl) ⟨1187360, by rfl⟩ : syracuseStep 1583147 = 2374721) B2374721
theorem B1583159 : Blo 1582489 1583159 := bstep (se 1 (by rfl) ⟨1187369, by rfl⟩ : syracuseStep 1583159 = 2374739) B2374739
theorem B4008001 : Blo 1582489 4008001 := bstep (se 2 (by rfl) ⟨1503000, by rfl⟩ : syracuseStep 4008001 = 3006001) B3006001
theorem B300394565 : Blo 1582489 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B1583179 : Blo 1582489 1583179 := bstep (se 1 (by rfl) ⟨1187384, by rfl⟩ : syracuseStep 1583179 = 2374769) B2374769
theorem B1583191 : Blo 1582489 1583191 := bstep (se 1 (by rfl) ⟨1187393, by rfl⟩ : syracuseStep 1583191 = 2374787) B2374787
theorem B1583211 : Blo 1582489 1583211 := bstep (se 1 (by rfl) ⟨1187408, by rfl⟩ : syracuseStep 1583211 = 2374817) B2374817
theorem B1583223 : Blo 1582489 1583223 := bstep (se 1 (by rfl) ⟨1187417, by rfl⟩ : syracuseStep 1583223 = 2374835) B2374835
theorem B2852993 : Blo 1582489 2852993 := bstep (se 2 (by rfl) ⟨1069872, by rfl⟩ : syracuseStep 2852993 = 2139745) B2139745
theorem B1583243 : Blo 1582489 1583243 := bstep (se 1 (by rfl) ⟨1187432, by rfl⟩ : syracuseStep 1583243 = 2374865) B2374865
theorem B1583255 : Blo 1582489 1583255 := bstep (se 1 (by rfl) ⟨1187441, by rfl⟩ : syracuseStep 1583255 = 2374883) B2374883
theorem B1583275 : Blo 1582489 1583275 := bstep (se 1 (by rfl) ⟨1187456, by rfl⟩ : syracuseStep 1583275 = 2374913) B2374913
theorem B1583287 : Blo 1582489 1583287 := bstep (se 1 (by rfl) ⟨1187465, by rfl⟩ : syracuseStep 1583287 = 2374931) B2374931
theorem B1583307 : Blo 1582489 1583307 := bstep (se 1 (by rfl) ⟨1187480, by rfl⟩ : syracuseStep 1583307 = 2374961) B2374961
theorem B1583319 : Blo 1582489 1583319 := bstep (se 1 (by rfl) ⟨1187489, by rfl⟩ : syracuseStep 1583319 = 2374979) B2374979
theorem B1583339 : Blo 1582489 1583339 := bstep (se 1 (by rfl) ⟨1187504, by rfl⟩ : syracuseStep 1583339 = 2375009) B2375009
theorem B1583351 : Blo 1582489 1583351 := bstep (se 1 (by rfl) ⟨1187513, by rfl⟩ : syracuseStep 1583351 = 2375027) B2375027
theorem B1583371 : Blo 1582489 1583371 := bstep (se 1 (by rfl) ⟨1187528, by rfl⟩ : syracuseStep 1583371 = 2375057) B2375057
theorem B1583383 : Blo 1582489 1583383 := bstep (se 1 (by rfl) ⟨1187537, by rfl⟩ : syracuseStep 1583383 = 2375075) B2375075
theorem B1583403 : Blo 1582489 1583403 := bstep (se 1 (by rfl) ⟨1187552, by rfl⟩ : syracuseStep 1583403 = 2375105) B2375105
theorem B15640877 : Blo 1582489 15640877 := bstep (se 3 (by rfl) ⟨2932664, by rfl⟩ : syracuseStep 15640877 = 5865329) B5865329
theorem B1583415 : Blo 1582489 1583415 := bstep (se 1 (by rfl) ⟨1187561, by rfl⟩ : syracuseStep 1583415 = 2375123) B2375123
theorem B1583435 : Blo 1582489 1583435 := bstep (se 1 (by rfl) ⟨1187576, by rfl⟩ : syracuseStep 1583435 = 2375153) B2375153
theorem B1583447 : Blo 1582489 1583447 := bstep (se 1 (by rfl) ⟨1187585, by rfl⟩ : syracuseStep 1583447 = 2375171) B2375171
theorem B1583467 : Blo 1582489 1583467 := bstep (se 1 (by rfl) ⟨1187600, by rfl⟩ : syracuseStep 1583467 = 2375201) B2375201
theorem B1583479 : Blo 1582489 1583479 := bstep (se 1 (by rfl) ⟨1187609, by rfl⟩ : syracuseStep 1583479 = 2375219) B2375219
theorem B5638531 : Blo 1582489 5638531 := bstep (se 1 (by rfl) ⟨4228898, by rfl⟩ : syracuseStep 5638531 = 8457797) B8457797
theorem B1583499 : Blo 1582489 1583499 := bstep (se 1 (by rfl) ⟨1187624, by rfl⟩ : syracuseStep 1583499 = 2375249) B2375249
theorem B1583511 : Blo 1582489 1583511 := bstep (se 1 (by rfl) ⟨1187633, by rfl⟩ : syracuseStep 1583511 = 2375267) B2375267
theorem B1583531 : Blo 1582489 1583531 := bstep (se 1 (by rfl) ⟨1187648, by rfl⟩ : syracuseStep 1583531 = 2375297) B2375297
theorem B1583543 : Blo 1582489 1583543 := bstep (se 1 (by rfl) ⟨1187657, by rfl⟩ : syracuseStep 1583543 = 2375315) B2375315
theorem B6760907 : Blo 1582489 6760907 := bstep (se 1 (by rfl) ⟨5070680, by rfl⟩ : syracuseStep 6760907 = 10141361) B10141361
theorem B1583563 : Blo 1582489 1583563 := bstep (se 1 (by rfl) ⟨1187672, by rfl⟩ : syracuseStep 1583563 = 2375345) B2375345
theorem B1583575 : Blo 1582489 1583575 := bstep (se 1 (by rfl) ⟨1187681, by rfl⟩ : syracuseStep 1583575 = 2375363) B2375363
theorem B2255321 : Blo 1582489 2255321 := bstep (se 2 (by rfl) ⟨845745, by rfl⟩ : syracuseStep 2255321 = 1691491) B1691491
theorem B1583595 : Blo 1582489 1583595 := bstep (se 1 (by rfl) ⟨1187696, by rfl⟩ : syracuseStep 1583595 = 2375393) B2375393
theorem B1690103 : Blo 1582489 1690103 := bstep (se 1 (by rfl) ⟨1267577, by rfl⟩ : syracuseStep 1690103 = 2535155) B2535155
theorem B1583607 : Blo 1582489 1583607 := bstep (se 1 (by rfl) ⟨1187705, by rfl⟩ : syracuseStep 1583607 = 2375411) B2375411
theorem B1583627 : Blo 1582489 1583627 := bstep (se 1 (by rfl) ⟨1187720, by rfl⟩ : syracuseStep 1583627 = 2375441) B2375441
theorem B1583639 : Blo 1582489 1583639 := bstep (se 1 (by rfl) ⟨1187729, by rfl⟩ : syracuseStep 1583639 = 2375459) B2375459
theorem B1583659 : Blo 1582489 1583659 := bstep (se 1 (by rfl) ⟨1187744, by rfl⟩ : syracuseStep 1583659 = 2375489) B2375489
theorem B1583671 : Blo 1582489 1583671 := bstep (se 1 (by rfl) ⟨1187753, by rfl⟩ : syracuseStep 1583671 = 2375507) B2375507
theorem B1583691 : Blo 1582489 1583691 := bstep (se 1 (by rfl) ⟨1187768, by rfl⟩ : syracuseStep 1583691 = 2375537) B2375537
theorem B1583703 : Blo 1582489 1583703 := bstep (se 1 (by rfl) ⟨1187777, by rfl⟩ : syracuseStep 1583703 = 2375555) B2375555
theorem B1583723 : Blo 1582489 1583723 := bstep (se 1 (by rfl) ⟨1187792, by rfl⟩ : syracuseStep 1583723 = 2375585) B2375585
theorem B1583735 : Blo 1582489 1583735 := bstep (se 1 (by rfl) ⟨1187801, by rfl⟩ : syracuseStep 1583735 = 2375603) B2375603
theorem B7604867 : Blo 1582489 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B1583755 : Blo 1582489 1583755 := bstep (se 1 (by rfl) ⟨1187816, by rfl⟩ : syracuseStep 1583755 = 2375633) B2375633
theorem B1780375 : Blo 1582489 1780375 := bstep (se 1 (by rfl) ⟨1335281, by rfl⟩ : syracuseStep 1780375 = 2670563) B2670563
theorem B4008599 : Blo 1582489 4008599 := bstep (se 1 (by rfl) ⟨3006449, by rfl⟩ : syracuseStep 4008599 = 6012899) B6012899
theorem B1583767 : Blo 1582489 1583767 := bstep (se 1 (by rfl) ⟨1187825, by rfl⟩ : syracuseStep 1583767 = 2375651) B2375651
theorem B1583787 : Blo 1582489 1583787 := bstep (se 1 (by rfl) ⟨1187840, by rfl⟩ : syracuseStep 1583787 = 2375681) B2375681
theorem B11414195 : Blo 1582489 11414195 := bstep (se 1 (by rfl) ⟨8560646, by rfl⟩ : syracuseStep 11414195 = 17121293) B17121293
theorem B1583799 : Blo 1582489 1583799 := bstep (se 1 (by rfl) ⟨1187849, by rfl⟩ : syracuseStep 1583799 = 2375699) B2375699
theorem B5343947 : Blo 1582489 5343947 := bstep (se 1 (by rfl) ⟨4007960, by rfl⟩ : syracuseStep 5343947 = 8015921) B8015921
theorem B1583819 : Blo 1582489 1583819 := bstep (se 1 (by rfl) ⟨1187864, by rfl⟩ : syracuseStep 1583819 = 2375729) B2375729
theorem B1583831 : Blo 1582489 1583831 := bstep (se 1 (by rfl) ⟨1187873, by rfl⟩ : syracuseStep 1583831 = 2375747) B2375747
theorem B1583851 : Blo 1582489 1583851 := bstep (se 1 (by rfl) ⟨1187888, by rfl⟩ : syracuseStep 1583851 = 2375777) B2375777
theorem B1583863 : Blo 1582489 1583863 := bstep (se 1 (by rfl) ⟨1187897, by rfl⟩ : syracuseStep 1583863 = 2375795) B2375795
theorem B2853643 : Blo 1582489 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B1583883 : Blo 1582489 1583883 := bstep (se 1 (by rfl) ⟨1187912, by rfl⟩ : syracuseStep 1583883 = 2375825) B2375825
theorem B1583895 : Blo 1582489 1583895 := bstep (se 1 (by rfl) ⟨1187921, by rfl⟩ : syracuseStep 1583895 = 2375843) B2375843
theorem B1583915 : Blo 1582489 1583915 := bstep (se 1 (by rfl) ⟨1187936, by rfl⟩ : syracuseStep 1583915 = 2375873) B2375873
theorem B1583927 : Blo 1582489 1583927 := bstep (se 1 (by rfl) ⟨1187945, by rfl⟩ : syracuseStep 1583927 = 2375891) B2375891
theorem B1780555 : Blo 1582489 1780555 := bstep (se 1 (by rfl) ⟨1335416, by rfl⟩ : syracuseStep 1780555 = 2670833) B2670833
theorem B1583947 : Blo 1582489 1583947 := bstep (se 1 (by rfl) ⟨1187960, by rfl⟩ : syracuseStep 1583947 = 2375921) B2375921
theorem B1583959 : Blo 1582489 1583959 := bstep (se 1 (by rfl) ⟨1187969, by rfl⟩ : syracuseStep 1583959 = 2375939) B2375939
theorem B1583979 : Blo 1582489 1583979 := bstep (se 1 (by rfl) ⟨1187984, by rfl⟩ : syracuseStep 1583979 = 2375969) B2375969
theorem B11414449 : Blo 1582489 11414449 := bstep (se 2 (by rfl) ⟨4280418, by rfl⟩ : syracuseStep 11414449 = 8560837) B8560837
theorem B1780663 : Blo 1582489 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B5344217 : Blo 1582489 5344217 := bstep (se 2 (by rfl) ⟨2004081, by rfl⟩ : syracuseStep 5344217 = 4008163) B4008163
theorem B1780843 : Blo 1582489 1780843 := bstep (se 1 (by rfl) ⟨1335632, by rfl⟩ : syracuseStep 1780843 = 2671265) B2671265
theorem B1805419 : Blo 1582489 1805419 := bstep (se 1 (by rfl) ⟨1354064, by rfl⟩ : syracuseStep 1805419 = 2708129) B2708129
theorem B1830071 : Blo 1582489 1830071 := bstep (se 1 (by rfl) ⟨1372553, by rfl⟩ : syracuseStep 1830071 = 2745107) B2745107
theorem B1780951 : Blo 1582489 1780951 := bstep (se 1 (by rfl) ⟨1335713, by rfl⟩ : syracuseStep 1780951 = 2671427) B2671427
theorem B7605521 : Blo 1582489 7605521 := bstep (se 2 (by rfl) ⟨2852070, by rfl⟩ : syracuseStep 7605521 = 5704141) B5704141
theorem B1781131 : Blo 1582489 1781131 := bstep (se 1 (by rfl) ⟨1335848, by rfl⟩ : syracuseStep 1781131 = 2671697) B2671697
theorem B4631987 : Blo 1582489 4631987 := bstep (se 1 (by rfl) ⟨3473990, by rfl⟩ : syracuseStep 4631987 = 6947981) B6947981
theorem B5418419 : Blo 1582489 5418419 := bstep (se 1 (by rfl) ⟨4063814, by rfl⟩ : syracuseStep 5418419 = 8127629) B8127629
theorem B4009409 : Blo 1582489 4009409 := bstep (se 2 (by rfl) ⟨1503528, by rfl⟩ : syracuseStep 4009409 = 3007057) B3007057
theorem B12021209 : Blo 1582489 12021209 := bstep (se 2 (by rfl) ⟨4507953, by rfl⟩ : syracuseStep 12021209 = 9015907) B9015907
theorem B1781239 : Blo 1582489 1781239 := bstep (se 1 (by rfl) ⟨1335929, by rfl⟩ : syracuseStep 1781239 = 2671859) B2671859
theorem B8015435 : Blo 1582489 8015435 := bstep (se 1 (by rfl) ⟨6011576, by rfl⟩ : syracuseStep 8015435 = 12023153) B12023153
theorem B10145411 : Blo 1582489 10145411 := bstep (se 1 (by rfl) ⟨7609058, by rfl⟩ : syracuseStep 10145411 = 15218117) B15218117
theorem B5344919 : Blo 1582489 5344919 := bstep (se 1 (by rfl) ⟨4008689, by rfl⟩ : syracuseStep 5344919 = 8017379) B8017379
theorem B1781419 : Blo 1582489 1781419 := bstep (se 1 (by rfl) ⟨1336064, by rfl⟩ : syracuseStep 1781419 = 2672129) B2672129
theorem B1781527 : Blo 1582489 1781527 := bstep (se 1 (by rfl) ⟨1336145, by rfl⟩ : syracuseStep 1781527 = 2672291) B2672291
theorem B2535257 : Blo 1582489 2535257 := bstep (se 2 (by rfl) ⟨950721, by rfl⟩ : syracuseStep 2535257 = 1901443) B1901443
theorem B1781707 : Blo 1582489 1781707 := bstep (se 1 (by rfl) ⟨1336280, by rfl⟩ : syracuseStep 1781707 = 2672561) B2672561
theorem B1781815 : Blo 1582489 1781815 := bstep (se 1 (by rfl) ⟨1336361, by rfl⟩ : syracuseStep 1781815 = 2672723) B2672723
theorem B5705873 : Blo 1582489 5705873 := bstep (se 2 (by rfl) ⟨2139702, by rfl⟩ : syracuseStep 5705873 = 4279405) B4279405
theorem B6009011 : Blo 1582489 6009011 := bstep (se 1 (by rfl) ⟨4506758, by rfl⟩ : syracuseStep 6009011 = 9013517) B9013517
theorem B5345459 : Blo 1582489 5345459 := bstep (se 1 (by rfl) ⟨4009094, by rfl⟩ : syracuseStep 5345459 = 8018189) B8018189
theorem B6009025 : Blo 1582489 6009025 := bstep (se 2 (by rfl) ⟨2253384, by rfl⟩ : syracuseStep 6009025 = 4506769) B4506769
theorem B4509913 : Blo 1582489 4509913 := bstep (se 2 (by rfl) ⟨1691217, by rfl⟩ : syracuseStep 4509913 = 3382435) B3382435
theorem B2003287 : Blo 1582489 2003287 := bstep (se 1 (by rfl) ⟨1502465, by rfl⟩ : syracuseStep 2003287 = 3004931) B3004931
theorem B5345729 : Blo 1582489 5345729 := bstep (se 2 (by rfl) ⟨2004648, by rfl⟩ : syracuseStep 5345729 = 4009297) B4009297
theorem B12841517 : Blo 1582489 12841517 := bstep (se 3 (by rfl) ⟨2407784, by rfl⟩ : syracuseStep 12841517 = 4815569) B4815569
theorem B20845187 : Blo 1582489 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B4281025 : Blo 1582489 4281025 := bstep (se 2 (by rfl) ⟨1605384, by rfl⟩ : syracuseStep 4281025 = 3210769) B3210769
theorem B20296453 : Blo 1582489 20296453 := bstep (se 4 (by rfl) ⟨1902792, by rfl⟩ : syracuseStep 20296453 = 3805585) B3805585
theorem B38507329 : Blo 1582489 38507329 := bstep (se 2 (by rfl) ⟨14440248, by rfl⟩ : syracuseStep 38507329 = 28880497) B28880497
theorem B4510529 : Blo 1582489 4510529 := bstep (se 2 (by rfl) ⟨1691448, by rfl⟩ : syracuseStep 4510529 = 3382897) B3382897
theorem B21672805 : Blo 1582489 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B17126261 : Blo 1582489 17126261 := bstep (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) B1605587
theorem B6763571 : Blo 1582489 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B20288663 : Blo 1582489 20288663 := bstep (se 1 (by rfl) ⟨15216497, by rfl⟩ : syracuseStep 20288663 = 30432995) B30432995
theorem B3609779 : Blo 1582489 3609779 := bstep (se 1 (by rfl) ⟨2707334, by rfl⟩ : syracuseStep 3609779 = 5414669) B5414669
theorem B3560651 : Blo 1582489 3560651 := bstep (se 1 (by rfl) ⟨2670488, by rfl⟩ : syracuseStep 3560651 = 5340977) B5340977
theorem B3560705 : Blo 1582489 3560705 := bstep (se 2 (by rfl) ⟨1335264, by rfl⟩ : syracuseStep 3560705 = 2670529) B2670529
theorem B8017217 : Blo 1582489 8017217 := bstep (se 2 (by rfl) ⟨3006456, by rfl⟩ : syracuseStep 8017217 = 6012913) B6012913
theorem B3560921 : Blo 1582489 3560921 := bstep (se 2 (by rfl) ⟨1335345, by rfl⟩ : syracuseStep 3560921 = 2670691) B2670691
theorem B3659251 : Blo 1582489 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B34223633 : Blo 1582489 34223633 := bstep (se 2 (by rfl) ⟨12833862, by rfl⟩ : syracuseStep 34223633 = 25667725) B25667725
theorem B7222807 : Blo 1582489 7222807 := bstep (se 1 (by rfl) ⟨5417105, by rfl⟩ : syracuseStep 7222807 = 10834211) B10834211
theorem B3561011 : Blo 1582489 3561011 := bstep (se 1 (by rfl) ⟨2670758, by rfl⟩ : syracuseStep 3561011 = 5341517) B5341517
theorem B3561047 : Blo 1582489 3561047 := bstep (se 1 (by rfl) ⟨2670785, by rfl⟩ : syracuseStep 3561047 = 5341571) B5341571
theorem B11417219 : Blo 1582489 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B3610291 : Blo 1582489 3610291 := bstep (se 1 (by rfl) ⟨2707718, by rfl⟩ : syracuseStep 3610291 = 5415437) B5415437
theorem B3380915 : Blo 1582489 3380915 := bstep (se 1 (by rfl) ⟨2535686, by rfl⟩ : syracuseStep 3380915 = 5071373) B5071373
theorem B3561227 : Blo 1582489 3561227 := bstep (se 1 (by rfl) ⟨2670920, by rfl⟩ : syracuseStep 3561227 = 5341841) B5341841
theorem B3561281 : Blo 1582489 3561281 := bstep (se 2 (by rfl) ⟨1335480, by rfl⟩ : syracuseStep 3561281 = 2670961) B2670961
theorem B3045259 : Blo 1582489 3045259 := bstep (se 1 (by rfl) ⟨2283944, by rfl⟩ : syracuseStep 3045259 = 4567889) B4567889
theorem B3561497 : Blo 1582489 3561497 := bstep (se 2 (by rfl) ⟨1335561, by rfl⟩ : syracuseStep 3561497 = 2671123) B2671123
theorem B6010955 : Blo 1582489 6010955 := bstep (se 1 (by rfl) ⟨4508216, by rfl⟩ : syracuseStep 6010955 = 9016433) B9016433
theorem B13531211 : Blo 1582489 13531211 := bstep (se 1 (by rfl) ⟨10148408, by rfl⟩ : syracuseStep 13531211 = 20296817) B20296817
theorem B6010969 : Blo 1582489 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B3561587 : Blo 1582489 3561587 := bstep (se 1 (by rfl) ⟨2671190, by rfl⟩ : syracuseStep 3561587 = 5342381) B5342381
theorem B3561623 : Blo 1582489 3561623 := bstep (se 1 (by rfl) ⟨2671217, by rfl⟩ : syracuseStep 3561623 = 5342435) B5342435
theorem B2373785 : Blo 1582489 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B3053785 : Blo 1582489 3053785 := bstep (se 2 (by rfl) ⟨1145169, by rfl⟩ : syracuseStep 3053785 = 2290339) B2290339
theorem B14448901 : Blo 1582489 14448901 := bstep (se 4 (by rfl) ⟨1354584, by rfl⟩ : syracuseStep 14448901 = 2709169) B2709169
theorem B2373899 : Blo 1582489 2373899 := bstep (se 1 (by rfl) ⟨1780424, by rfl⟩ : syracuseStep 2373899 = 3560849) B3560849
theorem B2373911 : Blo 1582489 2373911 := bstep (se 1 (by rfl) ⟨1780433, by rfl⟩ : syracuseStep 2373911 = 3560867) B3560867
theorem B3209537 : Blo 1582489 3209537 := bstep (se 2 (by rfl) ⟨1203576, by rfl⟩ : syracuseStep 3209537 = 2407153) B2407153
theorem B3561803 : Blo 1582489 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B2373977 : Blo 1582489 2373977 := bstep (se 2 (by rfl) ⟨890241, by rfl⟩ : syracuseStep 2373977 = 1780483) B1780483
theorem B3561857 : Blo 1582489 3561857 := bstep (se 2 (by rfl) ⟨1335696, by rfl⟩ : syracuseStep 3561857 = 2671393) B2671393
theorem B2374091 : Blo 1582489 2374091 := bstep (se 1 (by rfl) ⟨1780568, by rfl⟩ : syracuseStep 2374091 = 3561137) B3561137
theorem B2570699 : Blo 1582489 2570699 := bstep (se 1 (by rfl) ⟨1928024, by rfl⟩ : syracuseStep 2570699 = 3856049) B3856049
theorem B2374103 : Blo 1582489 2374103 := bstep (se 1 (by rfl) ⟨1780577, by rfl⟩ : syracuseStep 2374103 = 3561155) B3561155
theorem B6765059 : Blo 1582489 6765059 := bstep (se 1 (by rfl) ⟨5073794, by rfl⟩ : syracuseStep 6765059 = 10147589) B10147589
theorem B3611159 : Blo 1582489 3611159 := bstep (se 1 (by rfl) ⟨2708369, by rfl⟩ : syracuseStep 3611159 = 5416739) B5416739
theorem B2374169 : Blo 1582489 2374169 := bstep (se 2 (by rfl) ⟨890313, by rfl⟩ : syracuseStep 2374169 = 1780627) B1780627
theorem B3562073 : Blo 1582489 3562073 := bstep (se 2 (by rfl) ⟨1335777, by rfl⟩ : syracuseStep 3562073 = 2671555) B2671555
theorem B12835421 : Blo 1582489 12835421 := bstep (se 3 (by rfl) ⟨2406641, by rfl⟩ : syracuseStep 12835421 = 4813283) B4813283
theorem B2374283 : Blo 1582489 2374283 := bstep (se 1 (by rfl) ⟨1780712, by rfl⟩ : syracuseStep 2374283 = 3561425) B3561425
theorem B2374295 : Blo 1582489 2374295 := bstep (se 1 (by rfl) ⟨1780721, by rfl⟩ : syracuseStep 2374295 = 3561443) B3561443
theorem B3562163 : Blo 1582489 3562163 := bstep (se 1 (by rfl) ⟨2671622, by rfl⟩ : syracuseStep 3562163 = 5343245) B5343245
theorem B3562199 : Blo 1582489 3562199 := bstep (se 1 (by rfl) ⟨2671649, by rfl⟩ : syracuseStep 3562199 = 5343299) B5343299
theorem B2374361 : Blo 1582489 2374361 := bstep (se 2 (by rfl) ⟨890385, by rfl⟩ : syracuseStep 2374361 = 1780771) B1780771
theorem B6421265 : Blo 1582489 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B12024611 : Blo 1582489 12024611 := bstep (se 1 (by rfl) ⟨9018458, by rfl⟩ : syracuseStep 12024611 = 18036917) B18036917
theorem B2374475 : Blo 1582489 2374475 := bstep (se 1 (by rfl) ⟨1780856, by rfl⟩ : syracuseStep 2374475 = 3561713) B3561713
theorem B2374487 : Blo 1582489 2374487 := bstep (se 1 (by rfl) ⟨1780865, by rfl⟩ : syracuseStep 2374487 = 3561731) B3561731
theorem B3382145 : Blo 1582489 3382145 := bstep (se 2 (by rfl) ⟨1268304, by rfl⟩ : syracuseStep 3382145 = 2536609) B2536609
theorem B3562379 : Blo 1582489 3562379 := bstep (se 1 (by rfl) ⟨2671784, by rfl⟩ : syracuseStep 3562379 = 5343569) B5343569
theorem B2374553 : Blo 1582489 2374553 := bstep (se 2 (by rfl) ⟨890457, by rfl⟩ : syracuseStep 2374553 = 1780915) B1780915
theorem B3005363 : Blo 1582489 3005363 := bstep (se 1 (by rfl) ⟨2254022, by rfl⟩ : syracuseStep 3005363 = 4508045) B4508045
theorem B3562433 : Blo 1582489 3562433 := bstep (se 2 (by rfl) ⟨1335912, by rfl⟩ : syracuseStep 3562433 = 2671825) B2671825
theorem B2374667 : Blo 1582489 2374667 := bstep (se 1 (by rfl) ⟨1781000, by rfl⟩ : syracuseStep 2374667 = 3562001) B3562001
theorem B2374679 : Blo 1582489 2374679 := bstep (se 1 (by rfl) ⟨1781009, by rfl⟩ : syracuseStep 2374679 = 3562019) B3562019
theorem B6011927 : Blo 1582489 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B3005515 : Blo 1582489 3005515 := bstep (se 1 (by rfl) ⟨2254136, by rfl⟩ : syracuseStep 3005515 = 4508273) B4508273
theorem B2374745 : Blo 1582489 2374745 := bstep (se 2 (by rfl) ⟨890529, by rfl⟩ : syracuseStep 2374745 = 1781059) B1781059
theorem B3562649 : Blo 1582489 3562649 := bstep (se 2 (by rfl) ⟨1335993, by rfl⟩ : syracuseStep 3562649 = 2671987) B2671987
theorem B2374859 : Blo 1582489 2374859 := bstep (se 1 (by rfl) ⟨1781144, by rfl⟩ : syracuseStep 2374859 = 3562289) B3562289
theorem B2374871 : Blo 1582489 2374871 := bstep (se 1 (by rfl) ⟨1781153, by rfl⟩ : syracuseStep 2374871 = 3562307) B3562307
theorem B3562739 : Blo 1582489 3562739 := bstep (se 1 (by rfl) ⟨2672054, by rfl⟩ : syracuseStep 3562739 = 5344109) B5344109
theorem B9018641 : Blo 1582489 9018641 := bstep (se 2 (by rfl) ⟨3381990, by rfl⟩ : syracuseStep 9018641 = 6763981) B6763981
theorem B3562775 : Blo 1582489 3562775 := bstep (se 1 (by rfl) ⟨2672081, by rfl⟩ : syracuseStep 3562775 = 5344163) B5344163
theorem B2374937 : Blo 1582489 2374937 := bstep (se 2 (by rfl) ⟨890601, by rfl⟩ : syracuseStep 2374937 = 1781203) B1781203
theorem B1604939 : Blo 1582489 1604939 := bstep (se 1 (by rfl) ⟨1203704, by rfl⟩ : syracuseStep 1604939 = 2407409) B2407409
theorem B2375051 : Blo 1582489 2375051 := bstep (se 1 (by rfl) ⟨1781288, by rfl⟩ : syracuseStep 2375051 = 3562577) B3562577
theorem B2375063 : Blo 1582489 2375063 := bstep (se 1 (by rfl) ⟨1781297, by rfl⟩ : syracuseStep 2375063 = 3562595) B3562595
theorem B3005849 : Blo 1582489 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B3562955 : Blo 1582489 3562955 := bstep (se 1 (by rfl) ⟨2672216, by rfl⟩ : syracuseStep 3562955 = 5344433) B5344433
theorem B2375129 : Blo 1582489 2375129 := bstep (se 2 (by rfl) ⟨890673, by rfl⟩ : syracuseStep 2375129 = 1781347) B1781347
theorem B3563009 : Blo 1582489 3563009 := bstep (se 2 (by rfl) ⟨1336128, by rfl⟩ : syracuseStep 3563009 = 2672257) B2672257
theorem B6946307 : Blo 1582489 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B4816435 : Blo 1582489 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B2375243 : Blo 1582489 2375243 := bstep (se 1 (by rfl) ⟨1781432, by rfl⟩ : syracuseStep 2375243 = 3562865) B3562865
theorem B2375255 : Blo 1582489 2375255 := bstep (se 1 (by rfl) ⟨1781441, by rfl⟩ : syracuseStep 2375255 = 3562883) B3562883
theorem B2375321 : Blo 1582489 2375321 := bstep (se 2 (by rfl) ⟨890745, by rfl⟩ : syracuseStep 2375321 = 1781491) B1781491
theorem B3210931 : Blo 1582489 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B9019097 : Blo 1582489 9019097 := bstep (se 2 (by rfl) ⟨3382161, by rfl⟩ : syracuseStep 9019097 = 6764323) B6764323
theorem B3563225 : Blo 1582489 3563225 := bstep (se 2 (by rfl) ⟨1336209, by rfl⟩ : syracuseStep 3563225 = 2672419) B2672419
theorem B2375435 : Blo 1582489 2375435 := bstep (se 1 (by rfl) ⟨1781576, by rfl⟩ : syracuseStep 2375435 = 3563153) B3563153
theorem B2375447 : Blo 1582489 2375447 := bstep (se 1 (by rfl) ⟨1781585, by rfl⟩ : syracuseStep 2375447 = 3563171) B3563171
theorem B4005683 : Blo 1582489 4005683 := bstep (se 1 (by rfl) ⟨3004262, by rfl⟩ : syracuseStep 4005683 = 6008525) B6008525
theorem B3563315 : Blo 1582489 3563315 := bstep (se 1 (by rfl) ⟨2672486, by rfl⟩ : syracuseStep 3563315 = 5344973) B5344973
theorem B3563351 : Blo 1582489 3563351 := bstep (se 1 (by rfl) ⟨2672513, by rfl⟩ : syracuseStep 3563351 = 5345027) B5345027
theorem B2375513 : Blo 1582489 2375513 := bstep (se 2 (by rfl) ⟨890817, by rfl⟩ : syracuseStep 2375513 = 1781635) B1781635
theorem B2670475 : Blo 1582489 2670475 := bstep (se 1 (by rfl) ⟨2002856, by rfl⟩ : syracuseStep 2670475 = 4005713) B4005713
theorem B2375627 : Blo 1582489 2375627 := bstep (se 1 (by rfl) ⟨1781720, by rfl⟩ : syracuseStep 2375627 = 3563441) B3563441
theorem B2375639 : Blo 1582489 2375639 := bstep (se 1 (by rfl) ⟨1781729, by rfl⟩ : syracuseStep 2375639 = 3563459) B3563459
theorem B2375687 : Blo 1582489 2375687 := bstep (se 1 (by rfl) ⟨1781765, by rfl⟩ : syracuseStep 2375687 = 3563531) B3563531
theorem B2375723 : Blo 1582489 2375723 := bstep (se 1 (by rfl) ⟨1781792, by rfl⟩ : syracuseStep 2375723 = 3563585) B3563585
theorem B2375753 : Blo 1582489 2375753 := bstep (se 2 (by rfl) ⟨890907, by rfl⟩ : syracuseStep 2375753 = 1781815) B1781815
theorem B4006007 : Blo 1582489 4006007 := bstep (se 1 (by rfl) ⟨3004505, by rfl⟩ : syracuseStep 4006007 = 6009011) B6009011
theorem B3563639 : Blo 1582489 3563639 := bstep (se 1 (by rfl) ⟨2672729, by rfl⟩ : syracuseStep 3563639 = 5345459) B5345459
theorem B61014197 : Blo 1582489 61014197 := bstep (se 5 (by rfl) ⟨2860040, by rfl⟩ : syracuseStep 61014197 = 5720081) B5720081
theorem B2375867 : Blo 1582489 2375867 := bstep (se 1 (by rfl) ⟨1781900, by rfl⟩ : syracuseStep 2375867 = 3563801) B3563801
theorem B2375927 : Blo 1582489 2375927 := bstep (se 1 (by rfl) ⟨1781945, by rfl⟩ : syracuseStep 2375927 = 3563891) B3563891
theorem B8012033 : Blo 1582489 8012033 := bstep (se 2 (by rfl) ⟨3004512, by rfl⟩ : syracuseStep 8012033 = 6009025) B6009025
theorem B2375951 : Blo 1582489 2375951 := bstep (se 1 (by rfl) ⟨1781963, by rfl⟩ : syracuseStep 2375951 = 3563927) B3563927
theorem B4071713 : Blo 1582489 4071713 := bstep (se 2 (by rfl) ⟨1526892, by rfl⟩ : syracuseStep 4071713 = 3053785) B3053785
theorem B6013217 : Blo 1582489 6013217 := bstep (se 2 (by rfl) ⟨2254956, by rfl⟩ : syracuseStep 6013217 = 4509913) B4509913
theorem B3563819 : Blo 1582489 3563819 := bstep (se 1 (by rfl) ⟨2672864, by rfl⟩ : syracuseStep 3563819 = 5345729) B5345729
theorem B2670907 : Blo 1582489 2670907 := bstep (se 1 (by rfl) ⟨2003180, by rfl⟩ : syracuseStep 2670907 = 4006361) B4006361
theorem B4063547 : Blo 1582489 4063547 := bstep (se 1 (by rfl) ⟨3047660, by rfl⟩ : syracuseStep 4063547 = 6095321) B6095321
theorem B5341625 : Blo 1582489 5341625 := bstep (se 2 (by rfl) ⟨2003109, by rfl⟩ : syracuseStep 5341625 = 4006219) B4006219
theorem B2671049 : Blo 1582489 2671049 := bstep (se 2 (by rfl) ⟨1001643, by rfl⟩ : syracuseStep 2671049 = 2003287) B2003287
theorem B9626077 : Blo 1582489 9626077 := bstep (se 3 (by rfl) ⟨1804889, by rfl⟩ : syracuseStep 9626077 = 3609779) B3609779
theorem B3007019 : Blo 1582489 3007019 := bstep (se 1 (by rfl) ⟨2255264, by rfl⟩ : syracuseStep 3007019 = 4510529) B4510529
theorem B1901227 : Blo 1582489 1901227 := bstep (se 1 (by rfl) ⟨1425920, by rfl⟩ : syracuseStep 1901227 = 2851841) B2851841
theorem B13525775 : Blo 1582489 13525775 := bstep (se 1 (by rfl) ⟨10144331, by rfl⟩ : syracuseStep 13525775 = 20288663) B20288663
theorem B5784335 : Blo 1582489 5784335 := bstep (se 1 (by rfl) ⟨4338251, by rfl⟩ : syracuseStep 5784335 = 8676503) B8676503
theorem B22815755 : Blo 1582489 22815755 := bstep (se 1 (by rfl) ⟨17111816, by rfl⟩ : syracuseStep 22815755 = 34223633) B34223633
theorem B5342219 : Blo 1582489 5342219 := bstep (se 1 (by rfl) ⟨4006664, by rfl⟩ : syracuseStep 5342219 = 8013329) B8013329
theorem B8012843 : Blo 1582489 8012843 := bstep (se 1 (by rfl) ⟨6009632, by rfl⟩ : syracuseStep 8012843 = 12019265) B12019265
theorem B7611479 : Blo 1582489 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B5342327 : Blo 1582489 5342327 := bstep (se 1 (by rfl) ⟨4006745, by rfl⟩ : syracuseStep 5342327 = 8013491) B8013491
theorem B2253943 : Blo 1582489 2253943 := bstep (se 1 (by rfl) ⟨1690457, by rfl⟩ : syracuseStep 2253943 = 3380915) B3380915
theorem B2671751 : Blo 1582489 2671751 := bstep (se 1 (by rfl) ⟨2003813, by rfl⟩ : syracuseStep 2671751 = 4007627) B4007627
theorem B1901755 : Blo 1582489 1901755 := bstep (se 1 (by rfl) ⟨1426316, by rfl⟩ : syracuseStep 1901755 = 2852633) B2852633
theorem B6014189 : Blo 1582489 6014189 := bstep (se 3 (by rfl) ⟨1127660, by rfl⟩ : syracuseStep 6014189 = 2255321) B2255321
theorem B4506941 : Blo 1582489 4506941 := bstep (se 3 (by rfl) ⟨845051, by rfl⟩ : syracuseStep 4506941 = 1690103) B1690103
theorem B200263043 : Blo 1582489 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B4007303 : Blo 1582489 4007303 := bstep (se 1 (by rfl) ⟨3005477, by rfl⟩ : syracuseStep 4007303 = 6010955) B6010955
theorem B9020807 : Blo 1582489 9020807 := bstep (se 1 (by rfl) ⟨6765605, by rfl⟩ : syracuseStep 9020807 = 13531211) B13531211
theorem B4007353 : Blo 1582489 4007353 := bstep (se 2 (by rfl) ⟨1502757, by rfl⟩ : syracuseStep 4007353 = 3005515) B3005515
theorem B1582523 : Blo 1582489 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B34244045 : Blo 1582489 34244045 := bstep (se 3 (by rfl) ⟨6420758, by rfl⟩ : syracuseStep 34244045 = 12841517) B12841517
theorem B1582599 : Blo 1582489 1582599 := bstep (se 1 (by rfl) ⟨1186949, by rfl⟩ : syracuseStep 1582599 = 2373899) B2373899
theorem B1582607 : Blo 1582489 1582607 := bstep (se 1 (by rfl) ⟨1186955, by rfl⟩ : syracuseStep 1582607 = 2373911) B2373911
theorem B2139691 : Blo 1582489 2139691 := bstep (se 1 (by rfl) ⟨1604768, by rfl⟩ : syracuseStep 2139691 = 3209537) B3209537
theorem B1582651 : Blo 1582489 1582651 := bstep (se 1 (by rfl) ⟨1186988, by rfl⟩ : syracuseStep 1582651 = 2373977) B2373977
theorem B1582727 : Blo 1582489 1582727 := bstep (se 1 (by rfl) ⟨1187045, by rfl⟩ : syracuseStep 1582727 = 2374091) B2374091
theorem B4507271 : Blo 1582489 4507271 := bstep (se 1 (by rfl) ⟨3380453, by rfl⟩ : syracuseStep 4507271 = 6760907) B6760907
theorem B1713799 : Blo 1582489 1713799 := bstep (se 1 (by rfl) ⟨1285349, by rfl⟩ : syracuseStep 1713799 = 2570699) B2570699
theorem B1582735 : Blo 1582489 1582735 := bstep (se 1 (by rfl) ⟨1187051, by rfl⟩ : syracuseStep 1582735 = 2374103) B2374103
theorem B1582779 : Blo 1582489 1582779 := bstep (se 1 (by rfl) ⟨1187084, by rfl⟩ : syracuseStep 1582779 = 2374169) B2374169
theorem B5342921 : Blo 1582489 5342921 := bstep (se 2 (by rfl) ⟨2003595, by rfl⟩ : syracuseStep 5342921 = 4007191) B4007191
theorem B1582855 : Blo 1582489 1582855 := bstep (se 1 (by rfl) ⟨1187141, by rfl⟩ : syracuseStep 1582855 = 2374283) B2374283
theorem B1582863 : Blo 1582489 1582863 := bstep (se 1 (by rfl) ⟨1187147, by rfl⟩ : syracuseStep 1582863 = 2374295) B2374295
theorem B2672399 : Blo 1582489 2672399 := bstep (se 1 (by rfl) ⟨2004299, by rfl⟩ : syracuseStep 2672399 = 4008599) B4008599
theorem B1582907 : Blo 1582489 1582907 := bstep (se 1 (by rfl) ⟨1187180, by rfl⟩ : syracuseStep 1582907 = 2374361) B2374361
theorem B1582983 : Blo 1582489 1582983 := bstep (se 1 (by rfl) ⟨1187237, by rfl⟩ : syracuseStep 1582983 = 2374475) B2374475
theorem B1582991 : Blo 1582489 1582991 := bstep (se 1 (by rfl) ⟨1187243, by rfl⟩ : syracuseStep 1582991 = 2374487) B2374487
theorem B2254763 : Blo 1582489 2254763 := bstep (se 1 (by rfl) ⟨1691072, by rfl⟩ : syracuseStep 2254763 = 3382145) B3382145
theorem B1583035 : Blo 1582489 1583035 := bstep (se 1 (by rfl) ⟨1187276, by rfl⟩ : syracuseStep 1583035 = 2374553) B2374553
theorem B1583111 : Blo 1582489 1583111 := bstep (se 1 (by rfl) ⟨1187333, by rfl⟩ : syracuseStep 1583111 = 2374667) B2374667
theorem B1583119 : Blo 1582489 1583119 := bstep (se 1 (by rfl) ⟨1187339, by rfl⟩ : syracuseStep 1583119 = 2374679) B2374679
theorem B4007951 : Blo 1582489 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B1583163 : Blo 1582489 1583163 := bstep (se 1 (by rfl) ⟨1187372, by rfl⟩ : syracuseStep 1583163 = 2374745) B2374745
theorem B1583239 : Blo 1582489 1583239 := bstep (se 1 (by rfl) ⟨1187429, by rfl⟩ : syracuseStep 1583239 = 2374859) B2374859
theorem B1583247 : Blo 1582489 1583247 := bstep (se 1 (by rfl) ⟨1187435, by rfl⟩ : syracuseStep 1583247 = 2374871) B2374871
theorem B1583291 : Blo 1582489 1583291 := bstep (se 1 (by rfl) ⟨1187468, by rfl⟩ : syracuseStep 1583291 = 2374937) B2374937
theorem B6760685 : Blo 1582489 6760685 := bstep (se 3 (by rfl) ⟨1267628, by rfl⟩ : syracuseStep 6760685 = 2535257) B2535257
theorem B1583367 : Blo 1582489 1583367 := bstep (se 1 (by rfl) ⟨1187525, by rfl⟩ : syracuseStep 1583367 = 2375051) B2375051
theorem B1583375 : Blo 1582489 1583375 := bstep (se 1 (by rfl) ⟨1187531, by rfl⟩ : syracuseStep 1583375 = 2375063) B2375063
theorem B2672939 : Blo 1582489 2672939 := bstep (se 1 (by rfl) ⟨2004704, by rfl⟩ : syracuseStep 2672939 = 4009409) B4009409
theorem B8014139 : Blo 1582489 8014139 := bstep (se 1 (by rfl) ⟨6010604, by rfl⟩ : syracuseStep 8014139 = 12021209) B12021209
theorem B1583419 : Blo 1582489 1583419 := bstep (se 1 (by rfl) ⟨1187564, by rfl⟩ : syracuseStep 1583419 = 2375129) B2375129
theorem B4630871 : Blo 1582489 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B5343623 : Blo 1582489 5343623 := bstep (se 1 (by rfl) ⟨4007717, by rfl⟩ : syracuseStep 5343623 = 8015435) B8015435
theorem B1583495 : Blo 1582489 1583495 := bstep (se 1 (by rfl) ⟨1187621, by rfl⟩ : syracuseStep 1583495 = 2375243) B2375243
theorem B1583503 : Blo 1582489 1583503 := bstep (se 1 (by rfl) ⟨1187627, by rfl⟩ : syracuseStep 1583503 = 2375255) B2375255
theorem B1583547 : Blo 1582489 1583547 := bstep (se 1 (by rfl) ⟨1187660, by rfl⟩ : syracuseStep 1583547 = 2375321) B2375321
theorem B8014301 : Blo 1582489 8014301 := bstep (se 3 (by rfl) ⟨1502681, by rfl⟩ : syracuseStep 8014301 = 3005363) B3005363
theorem B1583623 : Blo 1582489 1583623 := bstep (se 1 (by rfl) ⟨1187717, by rfl⟩ : syracuseStep 1583623 = 2375435) B2375435
theorem B1583631 : Blo 1582489 1583631 := bstep (se 1 (by rfl) ⟨1187723, by rfl⟩ : syracuseStep 1583631 = 2375447) B2375447
theorem B1583675 : Blo 1582489 1583675 := bstep (se 1 (by rfl) ⟨1187756, by rfl⟩ : syracuseStep 1583675 = 2375513) B2375513
theorem B1583751 : Blo 1582489 1583751 := bstep (se 1 (by rfl) ⟨1187813, by rfl⟩ : syracuseStep 1583751 = 2375627) B2375627
theorem B1583759 : Blo 1582489 1583759 := bstep (se 1 (by rfl) ⟨1187819, by rfl⟩ : syracuseStep 1583759 = 2375639) B2375639
theorem B1780411 : Blo 1582489 1780411 := bstep (se 1 (by rfl) ⟨1335308, by rfl⟩ : syracuseStep 1780411 = 2670617) B2670617
theorem B1583803 : Blo 1582489 1583803 := bstep (se 1 (by rfl) ⟨1187852, by rfl⟩ : syracuseStep 1583803 = 2375705) B2375705
theorem B4008649 : Blo 1582489 4008649 := bstep (se 2 (by rfl) ⟨1503243, by rfl⟩ : syracuseStep 4008649 = 3006487) B3006487
theorem B5344001 : Blo 1582489 5344001 := bstep (se 2 (by rfl) ⟨2004000, by rfl⟩ : syracuseStep 5344001 = 4008001) B4008001
theorem B1583879 : Blo 1582489 1583879 := bstep (se 1 (by rfl) ⟨1187909, by rfl⟩ : syracuseStep 1583879 = 2375819) B2375819
theorem B3803915 : Blo 1582489 3803915 := bstep (se 1 (by rfl) ⟨2852936, by rfl⟩ : syracuseStep 3803915 = 5705873) B5705873
theorem B1583887 : Blo 1582489 1583887 := bstep (se 1 (by rfl) ⟨1187915, by rfl⟩ : syracuseStep 1583887 = 2375831) B2375831
theorem B8014625 : Blo 1582489 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B1583931 : Blo 1582489 1583931 := bstep (se 1 (by rfl) ⟨1187948, by rfl⟩ : syracuseStep 1583931 = 2375897) B2375897
theorem B4008791 : Blo 1582489 4008791 := bstep (se 1 (by rfl) ⟨3006593, by rfl⟩ : syracuseStep 4008791 = 6013187) B6013187
theorem B13896791 : Blo 1582489 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B27053189 : Blo 1582489 27053189 := bstep (se 4 (by rfl) ⟨2536236, by rfl⟩ : syracuseStep 27053189 = 5072473) B5072473
theorem B64990349 : Blo 1582489 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B1780879 : Blo 1582489 1780879 := bstep (se 1 (by rfl) ⟨1335659, by rfl⟩ : syracuseStep 1780879 = 2671319) B2671319
theorem B9628901 : Blo 1582489 9628901 := bstep (se 4 (by rfl) ⟨902709, by rfl⟩ : syracuseStep 9628901 = 1805419) B1805419
theorem B4509047 : Blo 1582489 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B4279837 : Blo 1582489 4279837 := bstep (se 3 (by rfl) ⟨802469, by rfl⟩ : syracuseStep 4279837 = 1604939) B1604939
theorem B5344811 : Blo 1582489 5344811 := bstep (se 1 (by rfl) ⟨4008608, by rfl⟩ : syracuseStep 5344811 = 8017217) B8017217
theorem B1781383 : Blo 1582489 1781383 := bstep (se 1 (by rfl) ⟨1336037, by rfl⟩ : syracuseStep 1781383 = 2672075) B2672075
theorem B27061937 : Blo 1582489 27061937 := bstep (se 2 (by rfl) ⟨10148226, by rfl⟩ : syracuseStep 27061937 = 20296453) B20296453
theorem B3804857 : Blo 1582489 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B8015597 : Blo 1582489 8015597 := bstep (se 3 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 8015597 = 3005849) B3005849
theorem B51343105 : Blo 1582489 51343105 := bstep (se 2 (by rfl) ⟨19253664, by rfl⟩ : syracuseStep 51343105 = 38507329) B38507329
theorem B28897073 : Blo 1582489 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B1781563 : Blo 1582489 1781563 := bstep (se 1 (by rfl) ⟨1336172, by rfl⟩ : syracuseStep 1781563 = 2672345) B2672345
theorem B6008843 : Blo 1582489 6008843 := bstep (se 1 (by rfl) ⟨4506632, by rfl⟩ : syracuseStep 6008843 = 9013265) B9013265
theorem B4510039 : Blo 1582489 4510039 := bstep (se 1 (by rfl) ⟨3382529, by rfl⟩ : syracuseStep 4510039 = 6765059) B6765059
theorem B8556947 : Blo 1582489 8556947 := bstep (se 1 (by rfl) ⟨6417710, by rfl⟩ : syracuseStep 8556947 = 12835421) B12835421
theorem B4280843 : Blo 1582489 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B8016407 : Blo 1582489 8016407 := bstep (se 1 (by rfl) ⟨6012305, by rfl⟩ : syracuseStep 8016407 = 12024611) B12024611
theorem B4879001 : Blo 1582489 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B9630409 : Blo 1582489 9630409 := bstep (se 2 (by rfl) ⟨3611403, by rfl⟩ : syracuseStep 9630409 = 7222807) B7222807
theorem B16241381 : Blo 1582489 16241381 := bstep (se 4 (by rfl) ⟨1522629, by rfl⟩ : syracuseStep 16241381 = 3045259) B3045259
theorem B4813721 : Blo 1582489 4813721 := bstep (se 2 (by rfl) ⟨1805145, by rfl⟩ : syracuseStep 4813721 = 3610291) B3610291
theorem B4281241 : Blo 1582489 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B6009785 : Blo 1582489 6009785 := bstep (se 2 (by rfl) ⟨2253669, by rfl⟩ : syracuseStep 6009785 = 4507339) B4507339
theorem B6763607 : Blo 1582489 6763607 := bstep (se 1 (by rfl) ⟨5072705, by rfl⟩ : syracuseStep 6763607 = 10145411) B10145411
theorem B3560633 : Blo 1582489 3560633 := bstep (se 2 (by rfl) ⟨1335237, by rfl⟩ : syracuseStep 3560633 = 2670475) B2670475
theorem B3560975 : Blo 1582489 3560975 := bstep (se 1 (by rfl) ⟨2670731, by rfl⟩ : syracuseStep 3560975 = 5341463) B5341463
theorem B3560993 : Blo 1582489 3560993 := bstep (se 2 (by rfl) ⟨1335372, by rfl⟩ : syracuseStep 3560993 = 2670745) B2670745
theorem B3380795 : Blo 1582489 3380795 := bstep (se 1 (by rfl) ⟨2535596, by rfl⟩ : syracuseStep 3380795 = 5071193) B5071193
theorem B7607981 : Blo 1582489 7607981 := bstep (se 3 (by rfl) ⟨1426496, by rfl⟩ : syracuseStep 7607981 = 2852993) B2852993
theorem B19265201 : Blo 1582489 19265201 := bstep (se 2 (by rfl) ⟨7224450, by rfl⟩ : syracuseStep 19265201 = 14448901) B14448901
theorem B4880189 : Blo 1582489 4880189 := bstep (se 3 (by rfl) ⟨915035, by rfl⟩ : syracuseStep 4880189 = 1830071) B1830071
theorem B7518041 : Blo 1582489 7518041 := bstep (se 2 (by rfl) ⟨2819265, by rfl⟩ : syracuseStep 7518041 = 5638531) B5638531
theorem B3561335 : Blo 1582489 3561335 := bstep (se 1 (by rfl) ⟨2671001, by rfl⟩ : syracuseStep 3561335 = 5342003) B5342003
theorem B11417507 : Blo 1582489 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B3004361 : Blo 1582489 3004361 := bstep (se 2 (by rfl) ⟨1126635, by rfl⟩ : syracuseStep 3004361 = 2253271) B2253271
theorem B3561515 : Blo 1582489 3561515 := bstep (se 1 (by rfl) ⟨2671136, by rfl⟩ : syracuseStep 3561515 = 5342273) B5342273
theorem B2373767 : Blo 1582489 2373767 := bstep (se 1 (by rfl) ⟨1780325, by rfl⟩ : syracuseStep 2373767 = 3560651) B3560651
theorem B2373803 : Blo 1582489 2373803 := bstep (se 1 (by rfl) ⟨1780352, by rfl⟩ : syracuseStep 2373803 = 3560705) B3560705
theorem B2373833 : Blo 1582489 2373833 := bstep (se 2 (by rfl) ⟨890187, by rfl⟩ : syracuseStep 2373833 = 1780375) B1780375
theorem B5708033 : Blo 1582489 5708033 := bstep (se 2 (by rfl) ⟨2140512, by rfl⟩ : syracuseStep 5708033 = 4281025) B4281025
theorem B3381547 : Blo 1582489 3381547 := bstep (se 1 (by rfl) ⟨2536160, by rfl⟩ : syracuseStep 3381547 = 5072321) B5072321
theorem B2373947 : Blo 1582489 2373947 := bstep (se 1 (by rfl) ⟨1780460, by rfl⟩ : syracuseStep 2373947 = 3560921) B3560921
theorem B2374007 : Blo 1582489 2374007 := bstep (se 1 (by rfl) ⟨1780505, by rfl⟩ : syracuseStep 2374007 = 3561011) B3561011
theorem B2374031 : Blo 1582489 2374031 := bstep (se 1 (by rfl) ⟨1780523, by rfl⟩ : syracuseStep 2374031 = 3561047) B3561047
theorem B3561875 : Blo 1582489 3561875 := bstep (se 1 (by rfl) ⟨2671406, by rfl⟩ : syracuseStep 3561875 = 5342813) B5342813
theorem B2374073 : Blo 1582489 2374073 := bstep (se 2 (by rfl) ⟨890277, by rfl⟩ : syracuseStep 2374073 = 1780555) B1780555
theorem B3561929 : Blo 1582489 3561929 := bstep (se 2 (by rfl) ⟨1335723, by rfl⟩ : syracuseStep 3561929 = 2671447) B2671447
theorem B12351965 : Blo 1582489 12351965 := bstep (se 3 (by rfl) ⟨2315993, by rfl⟩ : syracuseStep 12351965 = 4631987) B4631987
theorem B14449117 : Blo 1582489 14449117 := bstep (se 3 (by rfl) ⟨2709209, by rfl⟩ : syracuseStep 14449117 = 5418419) B5418419
theorem B2374151 : Blo 1582489 2374151 := bstep (se 1 (by rfl) ⟨1780613, by rfl⟩ : syracuseStep 2374151 = 3561227) B3561227
theorem B2374187 : Blo 1582489 2374187 := bstep (se 1 (by rfl) ⟨1780640, by rfl⟩ : syracuseStep 2374187 = 3561281) B3561281
theorem B15219265 : Blo 1582489 15219265 := bstep (se 2 (by rfl) ⟨5707224, by rfl⟩ : syracuseStep 15219265 = 11414449) B11414449
theorem B2374217 : Blo 1582489 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B38509175 : Blo 1582489 38509175 := bstep (se 1 (by rfl) ⟨28881881, by rfl⟩ : syracuseStep 38509175 = 57763763) B57763763
theorem B3005075 : Blo 1582489 3005075 := bstep (se 1 (by rfl) ⟨2253806, by rfl⟩ : syracuseStep 3005075 = 4507613) B4507613
theorem B3005113 : Blo 1582489 3005113 := bstep (se 2 (by rfl) ⟨1126917, by rfl⟩ : syracuseStep 3005113 = 2253835) B2253835
theorem B2374331 : Blo 1582489 2374331 := bstep (se 1 (by rfl) ⟨1780748, by rfl⟩ : syracuseStep 2374331 = 3561497) B3561497
theorem B2374391 : Blo 1582489 2374391 := bstep (se 1 (by rfl) ⟨1780793, by rfl⟩ : syracuseStep 2374391 = 3561587) B3561587
theorem B2374415 : Blo 1582489 2374415 := bstep (se 1 (by rfl) ⟨1780811, by rfl⟩ : syracuseStep 2374415 = 3561623) B3561623
theorem B2374457 : Blo 1582489 2374457 := bstep (se 2 (by rfl) ⟨890421, by rfl⟩ : syracuseStep 2374457 = 1780843) B1780843
theorem B10427251 : Blo 1582489 10427251 := bstep (se 1 (by rfl) ⟨7820438, by rfl⟩ : syracuseStep 10427251 = 15640877) B15640877
theorem B2374535 : Blo 1582489 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B2374571 : Blo 1582489 2374571 := bstep (se 1 (by rfl) ⟨1780928, by rfl⟩ : syracuseStep 2374571 = 3561857) B3561857
theorem B2374601 : Blo 1582489 2374601 := bstep (se 2 (by rfl) ⟨890475, by rfl⟩ : syracuseStep 2374601 = 1780951) B1780951
theorem B2407439 : Blo 1582489 2407439 := bstep (se 1 (by rfl) ⟨1805579, by rfl⟩ : syracuseStep 2407439 = 3611159) B3611159
theorem B2374715 : Blo 1582489 2374715 := bstep (se 1 (by rfl) ⟨1781036, by rfl⟩ : syracuseStep 2374715 = 3562073) B3562073
theorem B5069911 : Blo 1582489 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B2374775 : Blo 1582489 2374775 := bstep (se 1 (by rfl) ⟨1781081, by rfl⟩ : syracuseStep 2374775 = 3562163) B3562163
theorem B7609463 : Blo 1582489 7609463 := bstep (se 1 (by rfl) ⟨5707097, by rfl⟩ : syracuseStep 7609463 = 11414195) B11414195
theorem B3562631 : Blo 1582489 3562631 := bstep (se 1 (by rfl) ⟨2671973, by rfl⟩ : syracuseStep 3562631 = 5343947) B5343947
theorem B2374799 : Blo 1582489 2374799 := bstep (se 1 (by rfl) ⟨1781099, by rfl⟩ : syracuseStep 2374799 = 3562199) B3562199
theorem B2374841 : Blo 1582489 2374841 := bstep (se 2 (by rfl) ⟨890565, by rfl⟩ : syracuseStep 2374841 = 1781131) B1781131
theorem B2374919 : Blo 1582489 2374919 := bstep (se 1 (by rfl) ⟨1781189, by rfl⟩ : syracuseStep 2374919 = 3562379) B3562379
theorem B2374955 : Blo 1582489 2374955 := bstep (se 1 (by rfl) ⟨1781216, by rfl⟩ : syracuseStep 2374955 = 3562433) B3562433
theorem B3562811 : Blo 1582489 3562811 := bstep (se 1 (by rfl) ⟨2672108, by rfl⟩ : syracuseStep 3562811 = 5344217) B5344217
theorem B2374985 : Blo 1582489 2374985 := bstep (se 2 (by rfl) ⟨890619, by rfl⟩ : syracuseStep 2374985 = 1781239) B1781239
theorem B6421913 : Blo 1582489 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B3562937 : Blo 1582489 3562937 := bstep (se 2 (by rfl) ⟨1336101, by rfl⟩ : syracuseStep 3562937 = 2672203) B2672203
theorem B2375099 : Blo 1582489 2375099 := bstep (se 1 (by rfl) ⟨1781324, by rfl⟩ : syracuseStep 2375099 = 3562649) B3562649
theorem B2375159 : Blo 1582489 2375159 := bstep (se 1 (by rfl) ⟨1781369, by rfl⟩ : syracuseStep 2375159 = 3562739) B3562739
theorem B5070347 : Blo 1582489 5070347 := bstep (se 1 (by rfl) ⟨3802760, by rfl⟩ : syracuseStep 5070347 = 7605521) B7605521
theorem B6012427 : Blo 1582489 6012427 := bstep (se 1 (by rfl) ⟨4509320, by rfl⟩ : syracuseStep 6012427 = 9018641) B9018641
theorem B2375183 : Blo 1582489 2375183 := bstep (se 1 (by rfl) ⟨1781387, by rfl⟩ : syracuseStep 2375183 = 3562775) B3562775
theorem B2375225 : Blo 1582489 2375225 := bstep (se 2 (by rfl) ⟨890709, by rfl⟩ : syracuseStep 2375225 = 1781419) B1781419
theorem B2375303 : Blo 1582489 2375303 := bstep (se 1 (by rfl) ⟨1781477, by rfl⟩ : syracuseStep 2375303 = 3562955) B3562955
theorem B2375339 : Blo 1582489 2375339 := bstep (se 1 (by rfl) ⟨1781504, by rfl⟩ : syracuseStep 2375339 = 3563009) B3563009
theorem B2375369 : Blo 1582489 2375369 := bstep (se 2 (by rfl) ⟨890763, by rfl⟩ : syracuseStep 2375369 = 1781527) B1781527
theorem B3563279 : Blo 1582489 3563279 := bstep (se 1 (by rfl) ⟨2672459, by rfl⟩ : syracuseStep 3563279 = 5344919) B5344919
theorem B3563297 : Blo 1582489 3563297 := bstep (se 2 (by rfl) ⟨1336236, by rfl⟩ : syracuseStep 3563297 = 2672473) B2672473
theorem B6012731 : Blo 1582489 6012731 := bstep (se 1 (by rfl) ⟨4509548, by rfl⟩ : syracuseStep 6012731 = 9019097) B9019097
theorem B2375483 : Blo 1582489 2375483 := bstep (se 1 (by rfl) ⟨1781612, by rfl⟩ : syracuseStep 2375483 = 3563225) B3563225
theorem B2670455 : Blo 1582489 2670455 := bstep (se 1 (by rfl) ⟨2002841, by rfl⟩ : syracuseStep 2670455 = 4005683) B4005683
theorem B2375543 : Blo 1582489 2375543 := bstep (se 1 (by rfl) ⟨1781657, by rfl⟩ : syracuseStep 2375543 = 3563315) B3563315
theorem B2375567 : Blo 1582489 2375567 := bstep (se 1 (by rfl) ⟨1781675, by rfl⟩ : syracuseStep 2375567 = 3563351) B3563351
theorem B2375609 : Blo 1582489 2375609 := bstep (se 2 (by rfl) ⟨890853, by rfl⟩ : syracuseStep 2375609 = 1781707) B1781707
theorem B4005895 : Blo 1582489 4005895 := bstep (se 1 (by rfl) ⟨3004421, by rfl⟩ : syracuseStep 4005895 = 6008843) B6008843
theorem B2670671 : Blo 1582489 2670671 := bstep (se 1 (by rfl) ⟨2003003, by rfl⟩ : syracuseStep 2670671 = 4006007) B4006007
theorem B2375759 : Blo 1582489 2375759 := bstep (se 1 (by rfl) ⟨1781819, by rfl⟩ : syracuseStep 2375759 = 3563639) B3563639
theorem B5341355 : Blo 1582489 5341355 := bstep (se 1 (by rfl) ⟨4006016, by rfl⟩ : syracuseStep 5341355 = 8012033) B8012033
theorem B2375879 : Blo 1582489 2375879 := bstep (se 1 (by rfl) ⟨1781909, by rfl⟩ : syracuseStep 2375879 = 3563819) B3563819
theorem B3252667 : Blo 1582489 3252667 := bstep (se 1 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 3252667 = 4879001) B4879001
theorem B6013385 : Blo 1582489 6013385 := bstep (se 2 (by rfl) ⟨2255019, by rfl⟩ : syracuseStep 6013385 = 4510039) B4510039
theorem B4006523 : Blo 1582489 4006523 := bstep (se 1 (by rfl) ⟨3004892, by rfl⟩ : syracuseStep 4006523 = 6009785) B6009785
theorem B5341895 : Blo 1582489 5341895 := bstep (se 1 (by rfl) ⟨4006421, by rfl⟩ : syracuseStep 5341895 = 8012843) B8012843
theorem B20292353 : Blo 1582489 20292353 := bstep (se 2 (by rfl) ⟨7609632, by rfl⟩ : syracuseStep 20292353 = 15219265) B15219265
theorem B4006817 : Blo 1582489 4006817 := bstep (se 2 (by rfl) ⟨1502556, by rfl⟩ : syracuseStep 4006817 = 3005113) B3005113
theorem B2671535 : Blo 1582489 2671535 := bstep (se 1 (by rfl) ⟨2003651, by rfl⟩ : syracuseStep 2671535 = 4007303) B4007303
theorem B6013871 : Blo 1582489 6013871 := bstep (se 1 (by rfl) ⟨4510403, by rfl⟩ : syracuseStep 6013871 = 9020807) B9020807
theorem B2253863 : Blo 1582489 2253863 := bstep (se 1 (by rfl) ⟨1690397, by rfl⟩ : syracuseStep 2253863 = 3380795) B3380795
theorem B5071987 : Blo 1582489 5071987 := bstep (se 1 (by rfl) ⟨3803990, by rfl⟩ : syracuseStep 5071987 = 7607981) B7607981
theorem B13903001 : Blo 1582489 13903001 := bstep (se 2 (by rfl) ⟨5213625, by rfl⟩ : syracuseStep 13903001 = 10427251) B10427251
theorem B3253459 : Blo 1582489 3253459 := bstep (se 1 (by rfl) ⟨2440094, by rfl⟩ : syracuseStep 3253459 = 4880189) B4880189
theorem B7611671 : Blo 1582489 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B2671967 : Blo 1582489 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B1582511 : Blo 1582489 1582511 := bstep (se 1 (by rfl) ⟨1186883, by rfl⟩ : syracuseStep 1582511 = 2373767) B2373767
theorem B1582535 : Blo 1582489 1582535 := bstep (se 1 (by rfl) ⟨1186901, by rfl⟩ : syracuseStep 1582535 = 2373803) B2373803
theorem B6759881 : Blo 1582489 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B1582555 : Blo 1582489 1582555 := bstep (se 1 (by rfl) ⟨1186916, by rfl⟩ : syracuseStep 1582555 = 2373833) B2373833
theorem B4507123 : Blo 1582489 4507123 := bstep (se 1 (by rfl) ⟨3380342, by rfl⟩ : syracuseStep 4507123 = 6760685) B6760685
theorem B1582631 : Blo 1582489 1582631 := bstep (se 1 (by rfl) ⟨1186973, by rfl⟩ : syracuseStep 1582631 = 2373947) B2373947
theorem B5342759 : Blo 1582489 5342759 := bstep (se 1 (by rfl) ⟨4007069, by rfl⟩ : syracuseStep 5342759 = 8014139) B8014139
theorem B1582671 : Blo 1582489 1582671 := bstep (se 1 (by rfl) ⟨1187003, by rfl⟩ : syracuseStep 1582671 = 2374007) B2374007
theorem B1582687 : Blo 1582489 1582687 := bstep (se 1 (by rfl) ⟨1187015, by rfl⟩ : syracuseStep 1582687 = 2374031) B2374031
theorem B1582715 : Blo 1582489 1582715 := bstep (se 1 (by rfl) ⟨1187036, by rfl⟩ : syracuseStep 1582715 = 2374073) B2374073
theorem B5342867 : Blo 1582489 5342867 := bstep (se 1 (by rfl) ⟨4007150, by rfl⟩ : syracuseStep 5342867 = 8014301) B8014301
theorem B1582767 : Blo 1582489 1582767 := bstep (se 1 (by rfl) ⟨1187075, by rfl⟩ : syracuseStep 1582767 = 2374151) B2374151
theorem B1582791 : Blo 1582489 1582791 := bstep (se 1 (by rfl) ⟨1187093, by rfl⟩ : syracuseStep 1582791 = 2374187) B2374187
theorem B1582811 : Blo 1582489 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B1582887 : Blo 1582489 1582887 := bstep (se 1 (by rfl) ⟨1187165, by rfl⟩ : syracuseStep 1582887 = 2374331) B2374331
theorem B1582927 : Blo 1582489 1582927 := bstep (se 1 (by rfl) ⟨1187195, by rfl⟩ : syracuseStep 1582927 = 2374391) B2374391
theorem B1582943 : Blo 1582489 1582943 := bstep (se 1 (by rfl) ⟨1187207, by rfl⟩ : syracuseStep 1582943 = 2374415) B2374415
theorem B5343083 : Blo 1582489 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B1582971 : Blo 1582489 1582971 := bstep (se 1 (by rfl) ⟨1187228, by rfl⟩ : syracuseStep 1582971 = 2374457) B2374457
theorem B2672527 : Blo 1582489 2672527 := bstep (se 1 (by rfl) ⟨2004395, by rfl⟩ : syracuseStep 2672527 = 4008791) B4008791
theorem B5343137 : Blo 1582489 5343137 := bstep (se 2 (by rfl) ⟨2003676, by rfl⟩ : syracuseStep 5343137 = 4007353) B4007353
theorem B1583023 : Blo 1582489 1583023 := bstep (se 1 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 1583023 = 2374535) B2374535
theorem B1583047 : Blo 1582489 1583047 := bstep (se 1 (by rfl) ⟨1187285, by rfl⟩ : syracuseStep 1583047 = 2374571) B2374571
theorem B1583067 : Blo 1582489 1583067 := bstep (se 1 (by rfl) ⟨1187300, by rfl⟩ : syracuseStep 1583067 = 2374601) B2374601
theorem B1583143 : Blo 1582489 1583143 := bstep (se 1 (by rfl) ⟨1187357, by rfl⟩ : syracuseStep 1583143 = 2374715) B2374715
theorem B2852921 : Blo 1582489 2852921 := bstep (se 2 (by rfl) ⟨1069845, by rfl⟩ : syracuseStep 2852921 = 2139691) B2139691
theorem B1583183 : Blo 1582489 1583183 := bstep (se 1 (by rfl) ⟨1187387, by rfl⟩ : syracuseStep 1583183 = 2374775) B2374775
theorem B5072975 : Blo 1582489 5072975 := bstep (se 1 (by rfl) ⟨3804731, by rfl⟩ : syracuseStep 5072975 = 7609463) B7609463
theorem B1583199 : Blo 1582489 1583199 := bstep (se 1 (by rfl) ⟨1187399, by rfl⟩ : syracuseStep 1583199 = 2374799) B2374799
theorem B1583227 : Blo 1582489 1583227 := bstep (se 1 (by rfl) ⟨1187420, by rfl⟩ : syracuseStep 1583227 = 2374841) B2374841
theorem B1583279 : Blo 1582489 1583279 := bstep (se 1 (by rfl) ⟨1187459, by rfl⟩ : syracuseStep 1583279 = 2374919) B2374919
theorem B1583303 : Blo 1582489 1583303 := bstep (se 1 (by rfl) ⟨1187477, by rfl⟩ : syracuseStep 1583303 = 2374955) B2374955
theorem B1583323 : Blo 1582489 1583323 := bstep (se 1 (by rfl) ⟨1187492, by rfl⟩ : syracuseStep 1583323 = 2374985) B2374985
theorem B1583399 : Blo 1582489 1583399 := bstep (se 1 (by rfl) ⟨1187549, by rfl⟩ : syracuseStep 1583399 = 2375099) B2375099
theorem B131754293 : Blo 1582489 131754293 := bstep (se 5 (by rfl) ⟨6175982, by rfl⟩ : syracuseStep 131754293 = 12351965) B12351965
theorem B1583439 : Blo 1582489 1583439 := bstep (se 1 (by rfl) ⟨1187579, by rfl⟩ : syracuseStep 1583439 = 2375159) B2375159
theorem B1583455 : Blo 1582489 1583455 := bstep (se 1 (by rfl) ⟨1187591, by rfl⟩ : syracuseStep 1583455 = 2375183) B2375183
theorem B1583483 : Blo 1582489 1583483 := bstep (se 1 (by rfl) ⟨1187612, by rfl⟩ : syracuseStep 1583483 = 2375225) B2375225
theorem B1583535 : Blo 1582489 1583535 := bstep (se 1 (by rfl) ⟨1187651, by rfl⟩ : syracuseStep 1583535 = 2375303) B2375303
theorem B1583559 : Blo 1582489 1583559 := bstep (se 1 (by rfl) ⟨1187669, by rfl⟩ : syracuseStep 1583559 = 2375339) B2375339
theorem B18041291 : Blo 1582489 18041291 := bstep (se 1 (by rfl) ⟨13530968, by rfl⟩ : syracuseStep 18041291 = 27061937) B27061937
theorem B1583579 : Blo 1582489 1583579 := bstep (se 1 (by rfl) ⟨1187684, by rfl⟩ : syracuseStep 1583579 = 2375369) B2375369
theorem B5343731 : Blo 1582489 5343731 := bstep (se 1 (by rfl) ⟨4007798, by rfl⟩ : syracuseStep 5343731 = 8015597) B8015597
theorem B4008487 : Blo 1582489 4008487 := bstep (se 1 (by rfl) ⟨3006365, by rfl⟩ : syracuseStep 4008487 = 6012731) B6012731
theorem B1583655 : Blo 1582489 1583655 := bstep (se 1 (by rfl) ⟨1187741, by rfl⟩ : syracuseStep 1583655 = 2375483) B2375483
theorem B1780303 : Blo 1582489 1780303 := bstep (se 1 (by rfl) ⟨1335227, by rfl⟩ : syracuseStep 1780303 = 2670455) B2670455
theorem B1583695 : Blo 1582489 1583695 := bstep (se 1 (by rfl) ⟨1187771, by rfl⟩ : syracuseStep 1583695 = 2375543) B2375543
theorem B1583711 : Blo 1582489 1583711 := bstep (se 1 (by rfl) ⟨1187783, by rfl⟩ : syracuseStep 1583711 = 2375567) B2375567
theorem B1583739 : Blo 1582489 1583739 := bstep (se 1 (by rfl) ⟨1187804, by rfl⟩ : syracuseStep 1583739 = 2375609) B2375609
theorem B1583791 : Blo 1582489 1583791 := bstep (se 1 (by rfl) ⟨1187843, by rfl⟩ : syracuseStep 1583791 = 2375687) B2375687
theorem B1583815 : Blo 1582489 1583815 := bstep (se 1 (by rfl) ⟨1187861, by rfl⟩ : syracuseStep 1583815 = 2375723) B2375723
theorem B1583835 : Blo 1582489 1583835 := bstep (se 1 (by rfl) ⟨1187876, by rfl⟩ : syracuseStep 1583835 = 2375753) B2375753
theorem B40676131 : Blo 1582489 40676131 := bstep (se 1 (by rfl) ⟨30507098, by rfl⟩ : syracuseStep 40676131 = 61014197) B61014197
theorem B1583911 : Blo 1582489 1583911 := bstep (se 1 (by rfl) ⟨1187933, by rfl⟩ : syracuseStep 1583911 = 2375867) B2375867
theorem B1583951 : Blo 1582489 1583951 := bstep (se 1 (by rfl) ⟨1187963, by rfl⟩ : syracuseStep 1583951 = 2375927) B2375927
theorem B1583967 : Blo 1582489 1583967 := bstep (se 1 (by rfl) ⟨1187975, by rfl⟩ : syracuseStep 1583967 = 2375951) B2375951
theorem B4008811 : Blo 1582489 4008811 := bstep (se 1 (by rfl) ⟨3006608, by rfl⟩ : syracuseStep 4008811 = 6013217) B6013217
theorem B5704631 : Blo 1582489 5704631 := bstep (se 1 (by rfl) ⟨4278473, by rfl⟩ : syracuseStep 5704631 = 8556947) B8556947
theorem B1780699 : Blo 1582489 1780699 := bstep (se 1 (by rfl) ⟨1335524, by rfl⟩ : syracuseStep 1780699 = 2671049) B2671049
theorem B2853895 : Blo 1582489 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B5344271 : Blo 1582489 5344271 := bstep (se 1 (by rfl) ⟨4008203, by rfl⟩ : syracuseStep 5344271 = 8016407) B8016407
theorem B4508729 : Blo 1582489 4508729 := bstep (se 2 (by rfl) ⟨1690773, by rfl⟩ : syracuseStep 4508729 = 3381547) B3381547
theorem B4509071 : Blo 1582489 4509071 := bstep (se 1 (by rfl) ⟨3381803, by rfl⟩ : syracuseStep 4509071 = 6763607) B6763607
theorem B5074319 : Blo 1582489 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B10857901 : Blo 1582489 10857901 := bstep (se 3 (by rfl) ⟨2035856, by rfl⟩ : syracuseStep 10857901 = 4071713) B4071713
theorem B1781167 : Blo 1582489 1781167 := bstep (se 1 (by rfl) ⟨1335875, by rfl⟩ : syracuseStep 1781167 = 2671751) B2671751
theorem B4009459 : Blo 1582489 4009459 := bstep (se 1 (by rfl) ⟨3007094, by rfl⟩ : syracuseStep 4009459 = 6014189) B6014189
theorem B2534969 : Blo 1582489 2534969 := bstep (se 2 (by rfl) ⟨950613, by rfl⟩ : syracuseStep 2534969 = 1901227) B1901227
theorem B12840545 : Blo 1582489 12840545 := bstep (se 2 (by rfl) ⟨4815204, by rfl⟩ : syracuseStep 12840545 = 9630409) B9630409
theorem B5344865 : Blo 1582489 5344865 := bstep (se 2 (by rfl) ⟨2004324, by rfl⟩ : syracuseStep 5344865 = 4008649) B4008649
theorem B1781599 : Blo 1582489 1781599 := bstep (se 1 (by rfl) ⟨1336199, by rfl⟩ : syracuseStep 1781599 = 2672399) B2672399
theorem B2002907 : Blo 1582489 2002907 := bstep (se 1 (by rfl) ⟨1502180, by rfl⟩ : syracuseStep 2002907 = 3004361) B3004361
theorem B3805355 : Blo 1582489 3805355 := bstep (se 1 (by rfl) ⟨2854016, by rfl⟩ : syracuseStep 3805355 = 5708033) B5708033
theorem B1781959 : Blo 1582489 1781959 := bstep (se 1 (by rfl) ⟨1336469, by rfl⟩ : syracuseStep 1781959 = 2672939) B2672939
theorem B2535673 : Blo 1582489 2535673 := bstep (se 2 (by rfl) ⟨950877, by rfl⟩ : syracuseStep 2535673 = 1901755) B1901755
theorem B2003383 : Blo 1582489 2003383 := bstep (se 1 (by rfl) ⟨1502537, by rfl⟩ : syracuseStep 2003383 = 3005075) B3005075
theorem B2535943 : Blo 1582489 2535943 := bstep (se 1 (by rfl) ⟨1901957, by rfl⟩ : syracuseStep 2535943 = 3803915) B3803915
theorem B8016569 : Blo 1582489 8016569 := bstep (se 2 (by rfl) ⟨3006213, by rfl⟩ : syracuseStep 8016569 = 6012427) B6012427
theorem B5706449 : Blo 1582489 5706449 := bstep (se 2 (by rfl) ⟨2139918, by rfl⟩ : syracuseStep 5706449 = 4279837) B4279837
theorem B18035459 : Blo 1582489 18035459 := bstep (se 1 (by rfl) ⟨13526594, by rfl⟩ : syracuseStep 18035459 = 27053189) B27053189
theorem B6419267 : Blo 1582489 6419267 := bstep (se 1 (by rfl) ⟨4814450, by rfl⟩ : syracuseStep 6419267 = 9628901) B9628901
theorem B4281275 : Blo 1582489 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B68457473 : Blo 1582489 68457473 := bstep (se 2 (by rfl) ⟨25671552, by rfl⟩ : syracuseStep 68457473 = 51343105) B51343105
theorem B3380231 : Blo 1582489 3380231 := bstep (se 1 (by rfl) ⟨2535173, by rfl⟩ : syracuseStep 3380231 = 5070347) B5070347
theorem B2536571 : Blo 1582489 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B19264715 : Blo 1582489 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B6419837 : Blo 1582489 6419837 := bstep (se 3 (by rfl) ⟨1203719, by rfl⟩ : syracuseStep 6419837 = 2407439) B2407439
theorem B3561083 : Blo 1582489 3561083 := bstep (se 1 (by rfl) ⟨2670812, by rfl⟩ : syracuseStep 3561083 = 5341625) B5341625
theorem B2004679 : Blo 1582489 2004679 := bstep (se 1 (by rfl) ⟨1503509, by rfl⟩ : syracuseStep 2004679 = 3007019) B3007019
theorem B3561209 : Blo 1582489 3561209 := bstep (se 2 (by rfl) ⟨1335453, by rfl⟩ : syracuseStep 3561209 = 2670907) B2670907
theorem B10827587 : Blo 1582489 10827587 := bstep (se 1 (by rfl) ⟨8120690, by rfl⟩ : syracuseStep 10827587 = 16241381) B16241381
theorem B9017183 : Blo 1582489 9017183 := bstep (se 1 (by rfl) ⟨6762887, by rfl⟩ : syracuseStep 9017183 = 13525775) B13525775
theorem B3856223 : Blo 1582489 3856223 := bstep (se 1 (by rfl) ⟨2892167, by rfl⟩ : syracuseStep 3856223 = 5784335) B5784335
theorem B3209147 : Blo 1582489 3209147 := bstep (se 1 (by rfl) ⟨2406860, by rfl⟩ : syracuseStep 3209147 = 4813721) B4813721
theorem B12834769 : Blo 1582489 12834769 := bstep (se 2 (by rfl) ⟨4813038, by rfl⟩ : syracuseStep 12834769 = 9626077) B9626077
theorem B19265489 : Blo 1582489 19265489 := bstep (se 2 (by rfl) ⟨7224558, by rfl⟩ : syracuseStep 19265489 = 14449117) B14449117
theorem B15210503 : Blo 1582489 15210503 := bstep (se 1 (by rfl) ⟨11407877, by rfl⟩ : syracuseStep 15210503 = 22815755) B22815755
theorem B3561479 : Blo 1582489 3561479 := bstep (se 1 (by rfl) ⟨2671109, by rfl⟩ : syracuseStep 3561479 = 5342219) B5342219
theorem B3561551 : Blo 1582489 3561551 := bstep (se 1 (by rfl) ⟨2671163, by rfl⟩ : syracuseStep 3561551 = 5342327) B5342327
theorem B2373755 : Blo 1582489 2373755 := bstep (se 1 (by rfl) ⟨1780316, by rfl⟩ : syracuseStep 2373755 = 3560633) B3560633
theorem B10836125 : Blo 1582489 10836125 := bstep (se 3 (by rfl) ⟨2031773, by rfl⟩ : syracuseStep 10836125 = 4063547) B4063547
theorem B3004627 : Blo 1582489 3004627 := bstep (se 1 (by rfl) ⟨2253470, by rfl⟩ : syracuseStep 3004627 = 4506941) B4506941
theorem B2373881 : Blo 1582489 2373881 := bstep (se 2 (by rfl) ⟨890205, by rfl⟩ : syracuseStep 2373881 = 1780411) B1780411
theorem B22829363 : Blo 1582489 22829363 := bstep (se 1 (by rfl) ⟨17122022, by rfl⟩ : syracuseStep 22829363 = 34244045) B34244045
theorem B12024125 : Blo 1582489 12024125 := bstep (se 3 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 12024125 = 4509047) B4509047
theorem B534034781 : Blo 1582489 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B2373983 : Blo 1582489 2373983 := bstep (se 1 (by rfl) ⟨1780487, by rfl⟩ : syracuseStep 2373983 = 3560975) B3560975
theorem B2373995 : Blo 1582489 2373995 := bstep (se 1 (by rfl) ⟨1780496, by rfl⟩ : syracuseStep 2373995 = 3560993) B3560993
theorem B3004847 : Blo 1582489 3004847 := bstep (se 1 (by rfl) ⟨2253635, by rfl⟩ : syracuseStep 3004847 = 4507271) B4507271
theorem B12843467 : Blo 1582489 12843467 := bstep (se 1 (by rfl) ⟨9632600, by rfl⟩ : syracuseStep 12843467 = 19265201) B19265201
theorem B3561947 : Blo 1582489 3561947 := bstep (se 1 (by rfl) ⟨2671460, by rfl⟩ : syracuseStep 3561947 = 5342921) B5342921
theorem B5708321 : Blo 1582489 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B5012027 : Blo 1582489 5012027 := bstep (se 1 (by rfl) ⟨3759020, by rfl⟩ : syracuseStep 5012027 = 7518041) B7518041
theorem B2374223 : Blo 1582489 2374223 := bstep (se 1 (by rfl) ⟨1780667, by rfl⟩ : syracuseStep 2374223 = 3561335) B3561335
theorem B2374343 : Blo 1582489 2374343 := bstep (se 1 (by rfl) ⟨1780757, by rfl⟩ : syracuseStep 2374343 = 3561515) B3561515
theorem B3005257 : Blo 1582489 3005257 := bstep (se 2 (by rfl) ⟨1126971, by rfl⟩ : syracuseStep 3005257 = 2253943) B2253943
theorem B2374505 : Blo 1582489 2374505 := bstep (se 2 (by rfl) ⟨890439, by rfl⟩ : syracuseStep 2374505 = 1780879) B1780879
theorem B3087247 : Blo 1582489 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B3562415 : Blo 1582489 3562415 := bstep (se 1 (by rfl) ⟨2671811, by rfl⟩ : syracuseStep 3562415 = 5343623) B5343623
theorem B2374583 : Blo 1582489 2374583 := bstep (se 1 (by rfl) ⟨1780937, by rfl⟩ : syracuseStep 2374583 = 3561875) B3561875
theorem B2374619 : Blo 1582489 2374619 := bstep (se 1 (by rfl) ⟨1780964, by rfl⟩ : syracuseStep 2374619 = 3561929) B3561929
theorem B25672783 : Blo 1582489 25672783 := bstep (se 1 (by rfl) ⟨19254587, by rfl⟩ : syracuseStep 25672783 = 38509175) B38509175
theorem B3562667 : Blo 1582489 3562667 := bstep (se 1 (by rfl) ⟨2672000, by rfl⟩ : syracuseStep 3562667 = 5344001) B5344001
theorem B9264527 : Blo 1582489 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B2375087 : Blo 1582489 2375087 := bstep (se 1 (by rfl) ⟨1781315, by rfl⟩ : syracuseStep 2375087 = 3562631) B3562631
theorem B43326899 : Blo 1582489 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B2285065 : Blo 1582489 2285065 := bstep (se 2 (by rfl) ⟨856899, by rfl⟩ : syracuseStep 2285065 = 1713799) B1713799
theorem B2375177 : Blo 1582489 2375177 := bstep (se 2 (by rfl) ⟨890691, by rfl⟩ : syracuseStep 2375177 = 1781383) B1781383
theorem B2375207 : Blo 1582489 2375207 := bstep (se 1 (by rfl) ⟨1781405, by rfl⟩ : syracuseStep 2375207 = 3562811) B3562811
theorem B2375291 : Blo 1582489 2375291 := bstep (se 1 (by rfl) ⟨1781468, by rfl⟩ : syracuseStep 2375291 = 3562937) B3562937
theorem B3563207 : Blo 1582489 3563207 := bstep (se 1 (by rfl) ⟨2672405, by rfl⟩ : syracuseStep 3563207 = 5344811) B5344811
theorem B2375417 : Blo 1582489 2375417 := bstep (se 2 (by rfl) ⟨890781, by rfl⟩ : syracuseStep 2375417 = 1781563) B1781563
theorem B6012701 : Blo 1582489 6012701 := bstep (se 3 (by rfl) ⟨1127381, by rfl⟩ : syracuseStep 6012701 = 2254763) B2254763
theorem B2375519 : Blo 1582489 2375519 := bstep (se 1 (by rfl) ⟨1781639, by rfl⟩ : syracuseStep 2375519 = 3563279) B3563279
theorem B2375531 : Blo 1582489 2375531 := bstep (se 1 (by rfl) ⟨1781648, by rfl⟩ : syracuseStep 2375531 = 3563297) B3563297
theorem B5341193 : Blo 1582489 5341193 := bstep (se 2 (by rfl) ⟨2002947, by rfl⟩ : syracuseStep 5341193 = 4005895) B4005895
theorem B2375945 : Blo 1582489 2375945 := bstep (se 2 (by rfl) ⟨890979, by rfl⟩ : syracuseStep 2375945 = 1781959) B1781959
theorem B4006169 : Blo 1582489 4006169 := bstep (se 2 (by rfl) ⟨1502313, by rfl⟩ : syracuseStep 4006169 = 3004627) B3004627
theorem B2671015 : Blo 1582489 2671015 := bstep (se 1 (by rfl) ⟨2003261, by rfl⟩ : syracuseStep 2671015 = 4006523) B4006523
theorem B2671177 : Blo 1582489 2671177 := bstep (se 2 (by rfl) ⟨1001691, by rfl⟩ : syracuseStep 2671177 = 2003383) B2003383
theorem B2671211 : Blo 1582489 2671211 := bstep (se 1 (by rfl) ⟨2003408, by rfl⟩ : syracuseStep 2671211 = 4006817) B4006817
theorem B45638315 : Blo 1582489 45638315 := bstep (se 1 (by rfl) ⟨34228736, by rfl⟩ : syracuseStep 45638315 = 68457473) B68457473
theorem B4506587 : Blo 1582489 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B4007009 : Blo 1582489 4007009 := bstep (se 2 (by rfl) ⟨1502628, by rfl⟩ : syracuseStep 4007009 = 3005257) B3005257
theorem B7218391 : Blo 1582489 7218391 := bstep (se 1 (by rfl) ⟨5413793, by rfl⟩ : syracuseStep 7218391 = 10827587) B10827587
theorem B2139431 : Blo 1582489 2139431 := bstep (se 1 (by rfl) ⟨1604573, by rfl⟩ : syracuseStep 2139431 = 3209147) B3209147
theorem B1582503 : Blo 1582489 1582503 := bstep (se 1 (by rfl) ⟨1186877, by rfl⟩ : syracuseStep 1582503 = 2373755) B2373755
theorem B1582587 : Blo 1582489 1582587 := bstep (se 1 (by rfl) ⟨1186940, by rfl⟩ : syracuseStep 1582587 = 2373881) B2373881
theorem B87836195 : Blo 1582489 87836195 := bstep (se 1 (by rfl) ⟨65877146, by rfl⟩ : syracuseStep 87836195 = 131754293) B131754293
theorem B1582655 : Blo 1582489 1582655 := bstep (se 1 (by rfl) ⟨1186991, by rfl⟩ : syracuseStep 1582655 = 2373983) B2373983
theorem B1582663 : Blo 1582489 1582663 := bstep (se 1 (by rfl) ⟨1186997, by rfl⟩ : syracuseStep 1582663 = 2373995) B2373995
theorem B8562311 : Blo 1582489 8562311 := bstep (se 1 (by rfl) ⟨6421733, by rfl⟩ : syracuseStep 8562311 = 12843467) B12843467
theorem B12027527 : Blo 1582489 12027527 := bstep (se 1 (by rfl) ⟨9020645, by rfl⟩ : syracuseStep 12027527 = 18041291) B18041291
theorem B1582815 : Blo 1582489 1582815 := bstep (se 1 (by rfl) ⟨1187111, by rfl⟩ : syracuseStep 1582815 = 2374223) B2374223
theorem B1582895 : Blo 1582489 1582895 := bstep (se 1 (by rfl) ⟨1187171, by rfl⟩ : syracuseStep 1582895 = 2374343) B2374343
theorem B14477201 : Blo 1582489 14477201 := bstep (se 2 (by rfl) ⟨5428950, by rfl⟩ : syracuseStep 14477201 = 10857901) B10857901
theorem B1583003 : Blo 1582489 1583003 := bstep (se 1 (by rfl) ⟨1187252, by rfl⟩ : syracuseStep 1583003 = 2374505) B2374505
theorem B3803087 : Blo 1582489 3803087 := bstep (se 1 (by rfl) ⟨2852315, by rfl⟩ : syracuseStep 3803087 = 5704631) B5704631
theorem B1583055 : Blo 1582489 1583055 := bstep (se 1 (by rfl) ⟨1187291, by rfl⟩ : syracuseStep 1583055 = 2374583) B2374583
theorem B1583079 : Blo 1582489 1583079 := bstep (se 1 (by rfl) ⟨1187309, by rfl⟩ : syracuseStep 1583079 = 2374619) B2374619
theorem B2672905 : Blo 1582489 2672905 := bstep (se 2 (by rfl) ⟨1002339, by rfl⟩ : syracuseStep 2672905 = 2004679) B2004679
theorem B1583391 : Blo 1582489 1583391 := bstep (se 1 (by rfl) ⟨1187543, by rfl⟩ : syracuseStep 1583391 = 2375087) B2375087
theorem B1583451 : Blo 1582489 1583451 := bstep (se 1 (by rfl) ⟨1187588, by rfl⟩ : syracuseStep 1583451 = 2375177) B2375177
theorem B1583471 : Blo 1582489 1583471 := bstep (se 1 (by rfl) ⟨1187603, by rfl⟩ : syracuseStep 1583471 = 2375207) B2375207
theorem B1689979 : Blo 1582489 1689979 := bstep (se 1 (by rfl) ⟨1267484, by rfl⟩ : syracuseStep 1689979 = 2534969) B2534969
theorem B1583527 : Blo 1582489 1583527 := bstep (se 1 (by rfl) ⟨1187645, by rfl⟩ : syracuseStep 1583527 = 2375291) B2375291
theorem B1583611 : Blo 1582489 1583611 := bstep (se 1 (by rfl) ⟨1187708, by rfl⟩ : syracuseStep 1583611 = 2375417) B2375417
theorem B4008467 : Blo 1582489 4008467 := bstep (se 1 (by rfl) ⟨3006350, by rfl⟩ : syracuseStep 4008467 = 6012701) B6012701
theorem B1583679 : Blo 1582489 1583679 := bstep (se 1 (by rfl) ⟨1187759, by rfl⟩ : syracuseStep 1583679 = 2375519) B2375519
theorem B1583687 : Blo 1582489 1583687 := bstep (se 1 (by rfl) ⟨1187765, by rfl⟩ : syracuseStep 1583687 = 2375531) B2375531
theorem B9013949 : Blo 1582489 9013949 := bstep (se 3 (by rfl) ⟨1690115, by rfl⟩ : syracuseStep 9013949 = 3380231) B3380231
theorem B1780447 : Blo 1582489 1780447 := bstep (se 1 (by rfl) ⟨1335335, by rfl⟩ : syracuseStep 1780447 = 2670671) B2670671
theorem B1583839 : Blo 1582489 1583839 := bstep (se 1 (by rfl) ⟨1187879, by rfl⟩ : syracuseStep 1583839 = 2375759) B2375759
theorem B1583919 : Blo 1582489 1583919 := bstep (se 1 (by rfl) ⟨1187939, by rfl⟩ : syracuseStep 1583919 = 2375879) B2375879
theorem B4008923 : Blo 1582489 4008923 := bstep (se 1 (by rfl) ⟨3006692, by rfl⟩ : syracuseStep 4008923 = 6013385) B6013385
theorem B5344379 : Blo 1582489 5344379 := bstep (se 1 (by rfl) ⟨4008284, by rfl⟩ : syracuseStep 5344379 = 8016569) B8016569
theorem B3804299 : Blo 1582489 3804299 := bstep (se 1 (by rfl) ⟨2853224, by rfl⟩ : syracuseStep 3804299 = 5706449) B5706449
theorem B13528235 : Blo 1582489 13528235 := bstep (se 1 (by rfl) ⟨10146176, by rfl⟩ : syracuseStep 13528235 = 20292353) B20292353
theorem B4279511 : Blo 1582489 4279511 := bstep (se 1 (by rfl) ⟨3209633, by rfl⟩ : syracuseStep 4279511 = 6419267) B6419267
theorem B1781023 : Blo 1582489 1781023 := bstep (se 1 (by rfl) ⟨1335767, by rfl⟩ : syracuseStep 1781023 = 2671535) B2671535
theorem B4009247 : Blo 1582489 4009247 := bstep (se 1 (by rfl) ⟨3006935, by rfl⟩ : syracuseStep 4009247 = 6013871) B6013871
theorem B5344649 : Blo 1582489 5344649 := bstep (se 2 (by rfl) ⟨2004243, by rfl⟩ : syracuseStep 5344649 = 4008487) B4008487
theorem B1691047 : Blo 1582489 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B9268667 : Blo 1582489 9268667 := bstep (se 1 (by rfl) ⟨6951500, by rfl⟩ : syracuseStep 9268667 = 13903001) B13903001
theorem B1781311 : Blo 1582489 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B4279891 : Blo 1582489 4279891 := bstep (se 1 (by rfl) ⟨3209918, by rfl⟩ : syracuseStep 4279891 = 6419837) B6419837
theorem B54234841 : Blo 1582489 54234841 := bstep (se 2 (by rfl) ⟨20338065, by rfl⟩ : syracuseStep 54234841 = 40676131) B40676131
theorem B5345081 : Blo 1582489 5345081 := bstep (se 2 (by rfl) ⟨2004405, by rfl⟩ : syracuseStep 5345081 = 4008811) B4008811
theorem B4116329 : Blo 1582489 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B69390229 : Blo 1582489 69390229 := bstep (se 6 (by rfl) ⟨1626333, by rfl⟩ : syracuseStep 69390229 = 3252667) B3252667
theorem B3805193 : Blo 1582489 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B34230377 : Blo 1582489 34230377 := bstep (se 2 (by rfl) ⟨12836391, by rfl⟩ : syracuseStep 34230377 = 25672783) B25672783
theorem B6762649 : Blo 1582489 6762649 := bstep (se 2 (by rfl) ⟨2535993, by rfl⟩ : syracuseStep 6762649 = 5071987) B5071987
theorem B8016083 : Blo 1582489 8016083 := bstep (se 1 (by rfl) ⟨6012062, by rfl⟩ : syracuseStep 8016083 = 12024125) B12024125
theorem B4337945 : Blo 1582489 4337945 := bstep (se 2 (by rfl) ⟨1626729, by rfl⟩ : syracuseStep 4337945 = 3253459) B3253459
theorem B2003231 : Blo 1582489 2003231 := bstep (se 1 (by rfl) ⟨1502423, by rfl⟩ : syracuseStep 2003231 = 3004847) B3004847
theorem B3805547 : Blo 1582489 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B6009497 : Blo 1582489 6009497 := bstep (se 2 (by rfl) ⟨2253561, by rfl⟩ : syracuseStep 6009497 = 4507123) B4507123
theorem B5345945 : Blo 1582489 5345945 := bstep (se 2 (by rfl) ⟨2004729, by rfl⟩ : syracuseStep 5345945 = 4009459) B4009459
theorem B11416733 : Blo 1582489 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B6010301 : Blo 1582489 6010301 := bstep (se 3 (by rfl) ⟨1126931, by rfl⟩ : syracuseStep 6010301 = 2253863) B2253863
theorem B3560903 : Blo 1582489 3560903 := bstep (se 1 (by rfl) ⟨2670677, by rfl⟩ : syracuseStep 3560903 = 5341355) B5341355
theorem B2536903 : Blo 1582489 2536903 := bstep (se 1 (by rfl) ⟨1902677, by rfl⟩ : syracuseStep 2536903 = 3805355) B3805355
theorem B7607789 : Blo 1582489 7607789 := bstep (se 3 (by rfl) ⟨1426460, by rfl⟩ : syracuseStep 7607789 = 2852921) B2852921
theorem B3380897 : Blo 1582489 3380897 := bstep (se 2 (by rfl) ⟨1267836, by rfl⟩ : syracuseStep 3380897 = 2535673) B2535673
theorem B3561263 : Blo 1582489 3561263 := bstep (se 1 (by rfl) ⟨2670947, by rfl⟩ : syracuseStep 3561263 = 5341895) B5341895
theorem B12023639 : Blo 1582489 12023639 := bstep (se 1 (by rfl) ⟨9017729, by rfl⟩ : syracuseStep 12023639 = 18035459) B18035459
theorem B3381257 : Blo 1582489 3381257 := bstep (se 2 (by rfl) ⟨1267971, by rfl⟩ : syracuseStep 3381257 = 2535943) B2535943
theorem B20297789 : Blo 1582489 20297789 := bstep (se 3 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 20297789 = 7611671) B7611671
theorem B2373737 : Blo 1582489 2373737 := bstep (se 2 (by rfl) ⟨890151, by rfl⟩ : syracuseStep 2373737 = 1780303) B1780303
theorem B12843143 : Blo 1582489 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B3561839 : Blo 1582489 3561839 := bstep (se 1 (by rfl) ⟨2671379, by rfl⟩ : syracuseStep 3561839 = 5342759) B5342759
theorem B2374055 : Blo 1582489 2374055 := bstep (se 1 (by rfl) ⟨1780541, by rfl⟩ : syracuseStep 2374055 = 3561083) B3561083
theorem B3561911 : Blo 1582489 3561911 := bstep (se 1 (by rfl) ⟨2671433, by rfl⟩ : syracuseStep 3561911 = 5342867) B5342867
theorem B2374139 : Blo 1582489 2374139 := bstep (se 1 (by rfl) ⟨1780604, by rfl⟩ : syracuseStep 2374139 = 3561209) B3561209
theorem B6011455 : Blo 1582489 6011455 := bstep (se 1 (by rfl) ⟨4508591, by rfl⟩ : syracuseStep 6011455 = 9017183) B9017183
theorem B2570815 : Blo 1582489 2570815 := bstep (se 1 (by rfl) ⟨1928111, by rfl⟩ : syracuseStep 2570815 = 3856223) B3856223
theorem B3562055 : Blo 1582489 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B3562091 : Blo 1582489 3562091 := bstep (se 1 (by rfl) ⟨2671568, by rfl⟩ : syracuseStep 3562091 = 5343137) B5343137
theorem B2374265 : Blo 1582489 2374265 := bstep (se 2 (by rfl) ⟨890349, by rfl⟩ : syracuseStep 2374265 = 1780699) B1780699
theorem B12843659 : Blo 1582489 12843659 := bstep (se 1 (by rfl) ⟨9632744, by rfl⟩ : syracuseStep 12843659 = 19265489) B19265489
theorem B10140335 : Blo 1582489 10140335 := bstep (se 1 (by rfl) ⟨7605251, by rfl⟩ : syracuseStep 10140335 = 15210503) B15210503
theorem B2374319 : Blo 1582489 2374319 := bstep (se 1 (by rfl) ⟨1780739, by rfl⟩ : syracuseStep 2374319 = 3561479) B3561479
theorem B2374367 : Blo 1582489 2374367 := bstep (se 1 (by rfl) ⟨1780775, by rfl⟩ : syracuseStep 2374367 = 3561551) B3561551
theorem B3381983 : Blo 1582489 3381983 := bstep (se 1 (by rfl) ⟨2536487, by rfl⟩ : syracuseStep 3381983 = 5072975) B5072975
theorem B7224083 : Blo 1582489 7224083 := bstep (se 1 (by rfl) ⟨5418062, by rfl⟩ : syracuseStep 7224083 = 10836125) B10836125
theorem B15219575 : Blo 1582489 15219575 := bstep (se 1 (by rfl) ⟨11414681, by rfl⟩ : syracuseStep 15219575 = 22829363) B22829363
theorem B356023187 : Blo 1582489 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B2374631 : Blo 1582489 2374631 := bstep (se 1 (by rfl) ⟨1780973, by rfl⟩ : syracuseStep 2374631 = 3561947) B3561947
theorem B3562487 : Blo 1582489 3562487 := bstep (se 1 (by rfl) ⟨2671865, by rfl⟩ : syracuseStep 3562487 = 5343731) B5343731
theorem B3341351 : Blo 1582489 3341351 := bstep (se 1 (by rfl) ⟨2506013, by rfl⟩ : syracuseStep 3341351 = 5012027) B5012027
theorem B2374889 : Blo 1582489 2374889 := bstep (se 2 (by rfl) ⟨890583, by rfl⟩ : syracuseStep 2374889 = 1781167) B1781167
theorem B2374943 : Blo 1582489 2374943 := bstep (se 1 (by rfl) ⟨1781207, by rfl⟩ : syracuseStep 2374943 = 3562415) B3562415
theorem B3562847 : Blo 1582489 3562847 := bstep (se 1 (by rfl) ⟨2672135, by rfl⟩ : syracuseStep 3562847 = 5344271) B5344271
theorem B3046753 : Blo 1582489 3046753 := bstep (se 2 (by rfl) ⟨1142532, by rfl⟩ : syracuseStep 3046753 = 2285065) B2285065
theorem B3005819 : Blo 1582489 3005819 := bstep (se 1 (by rfl) ⟨2254364, by rfl⟩ : syracuseStep 3005819 = 4508729) B4508729
theorem B2375111 : Blo 1582489 2375111 := bstep (se 1 (by rfl) ⟨1781333, by rfl⟩ : syracuseStep 2375111 = 3562667) B3562667
theorem B6176351 : Blo 1582489 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B3006047 : Blo 1582489 3006047 := bstep (se 1 (by rfl) ⟨2254535, by rfl⟩ : syracuseStep 3006047 = 4509071) B4509071
theorem B3382879 : Blo 1582489 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B28884599 : Blo 1582489 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B8560363 : Blo 1582489 8560363 := bstep (se 1 (by rfl) ⟨6420272, by rfl⟩ : syracuseStep 8560363 = 12840545) B12840545
theorem B3563243 : Blo 1582489 3563243 := bstep (se 1 (by rfl) ⟨2672432, by rfl⟩ : syracuseStep 3563243 = 5344865) B5344865
theorem B2375465 : Blo 1582489 2375465 := bstep (se 2 (by rfl) ⟨890799, by rfl⟩ : syracuseStep 2375465 = 1781599) B1781599
theorem B2375471 : Blo 1582489 2375471 := bstep (se 1 (by rfl) ⟨1781603, by rfl⟩ : syracuseStep 2375471 = 3563207) B3563207
theorem B3563369 : Blo 1582489 3563369 := bstep (se 2 (by rfl) ⟨1336263, by rfl⟩ : syracuseStep 3563369 = 2672527) B2672527
theorem B5341085 : Blo 1582489 5341085 := bstep (se 3 (by rfl) ⟨1001453, by rfl⟩ : syracuseStep 5341085 = 2002907) B2002907
theorem B17113025 : Blo 1582489 17113025 := bstep (se 2 (by rfl) ⟨6417384, by rfl⟩ : syracuseStep 17113025 = 12834769) B12834769
theorem B2670779 : Blo 1582489 2670779 := bstep (se 1 (by rfl) ⟨2003084, by rfl⟩ : syracuseStep 2670779 = 4006169) B4006169
theorem B2891963 : Blo 1582489 2891963 := bstep (se 1 (by rfl) ⟨2168972, by rfl⟩ : syracuseStep 2891963 = 4337945) B4337945
theorem B3563873 : Blo 1582489 3563873 := bstep (se 2 (by rfl) ⟨1336452, by rfl⟩ : syracuseStep 3563873 = 2672905) B2672905
theorem B4006331 : Blo 1582489 4006331 := bstep (se 1 (by rfl) ⟨3004748, by rfl⟩ : syracuseStep 4006331 = 6009497) B6009497
theorem B3563963 : Blo 1582489 3563963 := bstep (se 1 (by rfl) ⟨2672972, by rfl⟩ : syracuseStep 3563963 = 5345945) B5345945
theorem B30425543 : Blo 1582489 30425543 := bstep (se 1 (by rfl) ⟨22819157, by rfl⟩ : syracuseStep 30425543 = 45638315) B45638315
theorem B2253305 : Blo 1582489 2253305 := bstep (se 2 (by rfl) ⟨844989, by rfl⟩ : syracuseStep 2253305 = 1689979) B1689979
theorem B11412029 : Blo 1582489 11412029 := bstep (se 3 (by rfl) ⟨2139755, by rfl⟩ : syracuseStep 11412029 = 4279511) B4279511
theorem B2671339 : Blo 1582489 2671339 := bstep (se 1 (by rfl) ⟨2003504, by rfl⟩ : syracuseStep 2671339 = 4007009) B4007009
theorem B5341949 : Blo 1582489 5341949 := bstep (se 3 (by rfl) ⟨1001615, by rfl⟩ : syracuseStep 5341949 = 2003231) B2003231
theorem B7611155 : Blo 1582489 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B4006867 : Blo 1582489 4006867 := bstep (se 1 (by rfl) ⟨3005150, by rfl⟩ : syracuseStep 4006867 = 6010301) B6010301
theorem B5071859 : Blo 1582489 5071859 := bstep (se 1 (by rfl) ⟨3803894, by rfl⟩ : syracuseStep 5071859 = 7607789) B7607789
theorem B9651467 : Blo 1582489 9651467 := bstep (se 1 (by rfl) ⟨7238600, by rfl⟩ : syracuseStep 9651467 = 14477201) B14477201
theorem B2254171 : Blo 1582489 2254171 := bstep (se 1 (by rfl) ⟨1690628, by rfl⟩ : syracuseStep 2254171 = 3381257) B3381257
theorem B1582491 : Blo 1582489 1582491 := bstep (se 1 (by rfl) ⟨1186868, by rfl⟩ : syracuseStep 1582491 = 2373737) B2373737
theorem B8562095 : Blo 1582489 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B1582703 : Blo 1582489 1582703 := bstep (se 1 (by rfl) ⟨1187027, by rfl⟩ : syracuseStep 1582703 = 2374055) B2374055
theorem B1582759 : Blo 1582489 1582759 := bstep (se 1 (by rfl) ⟨1187069, by rfl⟩ : syracuseStep 1582759 = 2374139) B2374139
theorem B2672311 : Blo 1582489 2672311 := bstep (se 1 (by rfl) ⟨2004233, by rfl⟩ : syracuseStep 2672311 = 4008467) B4008467
theorem B1582843 : Blo 1582489 1582843 := bstep (se 1 (by rfl) ⟨1187132, by rfl⟩ : syracuseStep 1582843 = 2374265) B2374265
theorem B8562439 : Blo 1582489 8562439 := bstep (se 1 (by rfl) ⟨6421829, by rfl⟩ : syracuseStep 8562439 = 12843659) B12843659
theorem B6760223 : Blo 1582489 6760223 := bstep (se 1 (by rfl) ⟨5070167, by rfl⟩ : syracuseStep 6760223 = 10140335) B10140335
theorem B1582879 : Blo 1582489 1582879 := bstep (se 1 (by rfl) ⟨1187159, by rfl⟩ : syracuseStep 1582879 = 2374319) B2374319
theorem B1582911 : Blo 1582489 1582911 := bstep (se 1 (by rfl) ⟨1187183, by rfl⟩ : syracuseStep 1582911 = 2374367) B2374367
theorem B2254655 : Blo 1582489 2254655 := bstep (se 1 (by rfl) ⟨1690991, by rfl⟩ : syracuseStep 2254655 = 3381983) B3381983
theorem B2254729 : Blo 1582489 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B237348791 : Blo 1582489 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B2672615 : Blo 1582489 2672615 := bstep (se 1 (by rfl) ⟨2004461, by rfl⟩ : syracuseStep 2672615 = 4008923) B4008923
theorem B1583087 : Blo 1582489 1583087 := bstep (se 1 (by rfl) ⟨1187315, by rfl⟩ : syracuseStep 1583087 = 2374631) B2374631
theorem B1583259 : Blo 1582489 1583259 := bstep (se 1 (by rfl) ⟨1187444, by rfl⟩ : syracuseStep 1583259 = 2374889) B2374889
theorem B1583295 : Blo 1582489 1583295 := bstep (se 1 (by rfl) ⟨1187471, by rfl⟩ : syracuseStep 1583295 = 2374943) B2374943
theorem B2672831 : Blo 1582489 2672831 := bstep (se 1 (by rfl) ⟨2004623, by rfl⟩ : syracuseStep 2672831 = 4009247) B4009247
theorem B72313121 : Blo 1582489 72313121 := bstep (se 2 (by rfl) ⟨27117420, by rfl⟩ : syracuseStep 72313121 = 54234841) B54234841
theorem B6179111 : Blo 1582489 6179111 := bstep (se 1 (by rfl) ⟨4634333, by rfl⟩ : syracuseStep 6179111 = 9268667) B9268667
theorem B1583407 : Blo 1582489 1583407 := bstep (se 1 (by rfl) ⟨1187555, by rfl⟩ : syracuseStep 1583407 = 2375111) B2375111
theorem B11413817 : Blo 1582489 11413817 := bstep (se 2 (by rfl) ⟨4280181, by rfl⟩ : syracuseStep 11413817 = 8560363) B8560363
theorem B1583643 : Blo 1582489 1583643 := bstep (se 1 (by rfl) ⟨1187732, by rfl⟩ : syracuseStep 1583643 = 2375465) B2375465
theorem B1583647 : Blo 1582489 1583647 := bstep (se 1 (by rfl) ⟨1187735, by rfl⟩ : syracuseStep 1583647 = 2375471) B2375471
theorem B5344055 : Blo 1582489 5344055 := bstep (se 1 (by rfl) ⟨4008041, by rfl⟩ : syracuseStep 5344055 = 8016083) B8016083
theorem B1583963 : Blo 1582489 1583963 := bstep (se 1 (by rfl) ⟨1187972, by rfl⟩ : syracuseStep 1583963 = 2375945) B2375945
theorem B1780807 : Blo 1582489 1780807 := bstep (se 1 (by rfl) ⟨1335605, by rfl⟩ : syracuseStep 1780807 = 2671211) B2671211
theorem B8015273 : Blo 1582489 8015273 := bstep (se 2 (by rfl) ⟨3005727, by rfl⟩ : syracuseStep 8015273 = 6011455) B6011455
theorem B3427753 : Blo 1582489 3427753 := bstep (se 2 (by rfl) ⟨1285407, by rfl⟩ : syracuseStep 3427753 = 2570815) B2570815
theorem B5705149 : Blo 1582489 5705149 := bstep (se 3 (by rfl) ⟨1069715, by rfl⟩ : syracuseStep 5705149 = 2139431) B2139431
theorem B8015759 : Blo 1582489 8015759 := bstep (se 1 (by rfl) ⟨6011819, by rfl⟩ : syracuseStep 8015759 = 12023639) B12023639
theorem B2535391 : Blo 1582489 2535391 := bstep (se 1 (by rfl) ⟨1901543, by rfl⟩ : syracuseStep 2535391 = 3803087) B3803087
theorem B234229853 : Blo 1582489 234229853 := bstep (se 3 (by rfl) ⟨43918097, by rfl⟩ : syracuseStep 234229853 = 87836195) B87836195
theorem B9015725 : Blo 1582489 9015725 := bstep (se 3 (by rfl) ⟨1690448, by rfl⟩ : syracuseStep 9015725 = 3380897) B3380897
theorem B6009299 : Blo 1582489 6009299 := bstep (se 1 (by rfl) ⟨4506974, by rfl⟩ : syracuseStep 6009299 = 9013949) B9013949
theorem B16249349 : Blo 1582489 16249349 := bstep (se 4 (by rfl) ⟨1523376, by rfl⟩ : syracuseStep 16249349 = 3046753) B3046753
theorem B10146383 : Blo 1582489 10146383 := bstep (se 1 (by rfl) ⟨7609787, by rfl⟩ : syracuseStep 10146383 = 15219575) B15219575
theorem B2536199 : Blo 1582489 2536199 := bstep (se 1 (by rfl) ⟨1902149, by rfl⟩ : syracuseStep 2536199 = 3804299) B3804299
theorem B5706521 : Blo 1582489 5706521 := bstep (se 2 (by rfl) ⟨2139945, by rfl⟩ : syracuseStep 5706521 = 4279891) B4279891
theorem B4510505 : Blo 1582489 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B2003879 : Blo 1582489 2003879 := bstep (se 1 (by rfl) ⟨1502909, by rfl⟩ : syracuseStep 2003879 = 3005819) B3005819
theorem B13530149 : Blo 1582489 13530149 := bstep (se 4 (by rfl) ⟨1268451, by rfl⟩ : syracuseStep 13530149 = 2536903) B2536903
theorem B4117567 : Blo 1582489 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B2004031 : Blo 1582489 2004031 := bstep (se 1 (by rfl) ⟨1503023, by rfl⟩ : syracuseStep 2004031 = 3006047) B3006047
theorem B19256399 : Blo 1582489 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B3560723 : Blo 1582489 3560723 := bstep (se 1 (by rfl) ⟨2670542, by rfl⟩ : syracuseStep 3560723 = 5341085) B5341085
theorem B11408683 : Blo 1582489 11408683 := bstep (se 1 (by rfl) ⟨8556512, by rfl⟩ : syracuseStep 11408683 = 17113025) B17113025
theorem B3560795 : Blo 1582489 3560795 := bstep (se 1 (by rfl) ⟨2670596, by rfl⟩ : syracuseStep 3560795 = 5341193) B5341193
theorem B2536795 : Blo 1582489 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B22820251 : Blo 1582489 22820251 := bstep (se 1 (by rfl) ⟨17115188, by rfl⟩ : syracuseStep 22820251 = 34230377) B34230377
theorem B9016865 : Blo 1582489 9016865 := bstep (se 2 (by rfl) ⟨3381324, by rfl⟩ : syracuseStep 9016865 = 6762649) B6762649
theorem B3561353 : Blo 1582489 3561353 := bstep (se 2 (by rfl) ⟨1335507, by rfl⟩ : syracuseStep 3561353 = 2671015) B2671015
theorem B3004391 : Blo 1582489 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B3561569 : Blo 1582489 3561569 := bstep (se 2 (by rfl) ⟨1335588, by rfl⟩ : syracuseStep 3561569 = 2671177) B2671177
theorem B10148125 : Blo 1582489 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B2373929 : Blo 1582489 2373929 := bstep (se 2 (by rfl) ⟨890223, by rfl⟩ : syracuseStep 2373929 = 1780447) B1780447
theorem B2373935 : Blo 1582489 2373935 := bstep (se 1 (by rfl) ⟨1780451, by rfl⟩ : syracuseStep 2373935 = 3560903) B3560903
theorem B5708207 : Blo 1582489 5708207 := bstep (se 1 (by rfl) ⟨4281155, by rfl⟩ : syracuseStep 5708207 = 8562311) B8562311
theorem B8018351 : Blo 1582489 8018351 := bstep (se 1 (by rfl) ⟨6013763, by rfl⟩ : syracuseStep 8018351 = 12027527) B12027527
theorem B2374175 : Blo 1582489 2374175 := bstep (se 1 (by rfl) ⟨1780631, by rfl⟩ : syracuseStep 2374175 = 3561263) B3561263
theorem B13531859 : Blo 1582489 13531859 := bstep (se 1 (by rfl) ⟨10148894, by rfl⟩ : syracuseStep 13531859 = 20297789) B20297789
theorem B2374559 : Blo 1582489 2374559 := bstep (se 1 (by rfl) ⟨1780919, by rfl⟩ : syracuseStep 2374559 = 3561839) B3561839
theorem B9624521 : Blo 1582489 9624521 := bstep (se 2 (by rfl) ⟨3609195, by rfl⟩ : syracuseStep 9624521 = 7218391) B7218391
theorem B2374607 : Blo 1582489 2374607 := bstep (se 1 (by rfl) ⟨1780955, by rfl⟩ : syracuseStep 2374607 = 3561911) B3561911
theorem B2374697 : Blo 1582489 2374697 := bstep (se 2 (by rfl) ⟨890511, by rfl⟩ : syracuseStep 2374697 = 1781023) B1781023
theorem B2374703 : Blo 1582489 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B2374727 : Blo 1582489 2374727 := bstep (se 1 (by rfl) ⟨1781045, by rfl⟩ : syracuseStep 2374727 = 3562091) B3562091
theorem B4816055 : Blo 1582489 4816055 := bstep (se 1 (by rfl) ⟨3612041, by rfl⟩ : syracuseStep 4816055 = 7224083) B7224083
theorem B2374991 : Blo 1582489 2374991 := bstep (se 1 (by rfl) ⟨1781243, by rfl⟩ : syracuseStep 2374991 = 3562487) B3562487
theorem B2227567 : Blo 1582489 2227567 := bstep (se 1 (by rfl) ⟨1670675, by rfl⟩ : syracuseStep 2227567 = 3341351) B3341351
theorem B3562919 : Blo 1582489 3562919 := bstep (se 1 (by rfl) ⟨2672189, by rfl⟩ : syracuseStep 3562919 = 5344379) B5344379
theorem B2375081 : Blo 1582489 2375081 := bstep (se 2 (by rfl) ⟨890655, by rfl⟩ : syracuseStep 2375081 = 1781311) B1781311
theorem B9018823 : Blo 1582489 9018823 := bstep (se 1 (by rfl) ⟨6764117, by rfl⟩ : syracuseStep 9018823 = 13528235) B13528235
theorem B2375231 : Blo 1582489 2375231 := bstep (se 1 (by rfl) ⟨1781423, by rfl⟩ : syracuseStep 2375231 = 3562847) B3562847
theorem B3563099 : Blo 1582489 3563099 := bstep (se 1 (by rfl) ⟨2672324, by rfl⟩ : syracuseStep 3563099 = 5344649) B5344649
theorem B2375495 : Blo 1582489 2375495 := bstep (se 1 (by rfl) ⟨1781621, by rfl⟩ : syracuseStep 2375495 = 3563243) B3563243
theorem B92520305 : Blo 1582489 92520305 := bstep (se 2 (by rfl) ⟨34695114, by rfl⟩ : syracuseStep 92520305 = 69390229) B69390229
theorem B3563387 : Blo 1582489 3563387 := bstep (se 1 (by rfl) ⟨2672540, by rfl⟩ : syracuseStep 3563387 = 5345081) B5345081
theorem B2744219 : Blo 1582489 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B2375579 : Blo 1582489 2375579 := bstep (se 1 (by rfl) ⟨1781684, by rfl⟩ : syracuseStep 2375579 = 3563369) B3563369
theorem B2375915 : Blo 1582489 2375915 := bstep (se 1 (by rfl) ⟨1781936, by rfl⟩ : syracuseStep 2375915 = 3563873) B3563873
theorem B2670887 : Blo 1582489 2670887 := bstep (se 1 (by rfl) ⟨2003165, by rfl⟩ : syracuseStep 2670887 = 4006331) B4006331
theorem B2375975 : Blo 1582489 2375975 := bstep (se 1 (by rfl) ⟨1781981, by rfl⟩ : syracuseStep 2375975 = 3563963) B3563963
theorem B20283695 : Blo 1582489 20283695 := bstep (se 1 (by rfl) ⟨15212771, by rfl⟩ : syracuseStep 20283695 = 30425543) B30425543
theorem B4006199 : Blo 1582489 4006199 := bstep (se 1 (by rfl) ⟨3004649, by rfl⟩ : syracuseStep 4006199 = 6009299) B6009299
theorem B9020099 : Blo 1582489 9020099 := bstep (se 1 (by rfl) ⟨6765074, by rfl⟩ : syracuseStep 9020099 = 13530149) B13530149
theorem B12837599 : Blo 1582489 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B4506815 : Blo 1582489 4506815 := bstep (se 1 (by rfl) ⟨3380111, by rfl⟩ : syracuseStep 4506815 = 6760223) B6760223
theorem B5342489 : Blo 1582489 5342489 := bstep (se 2 (by rfl) ⟨2003433, by rfl⟩ : syracuseStep 5342489 = 4006867) B4006867
theorem B5490089 : Blo 1582489 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B2672041 : Blo 1582489 2672041 := bstep (se 2 (by rfl) ⟨1002015, by rfl⟩ : syracuseStep 2672041 = 2004031) B2004031
theorem B1582619 : Blo 1582489 1582619 := bstep (se 1 (by rfl) ⟨1186964, by rfl⟩ : syracuseStep 1582619 = 2373929) B2373929
theorem B1582623 : Blo 1582489 1582623 := bstep (se 1 (by rfl) ⟨1186967, by rfl⟩ : syracuseStep 1582623 = 2373935) B2373935
theorem B1582783 : Blo 1582489 1582783 := bstep (se 1 (by rfl) ⟨1187087, by rfl⟩ : syracuseStep 1582783 = 2374175) B2374175
theorem B9021239 : Blo 1582489 9021239 := bstep (se 1 (by rfl) ⟨6765929, by rfl⟩ : syracuseStep 9021239 = 13531859) B13531859
theorem B30427001 : Blo 1582489 30427001 := bstep (se 2 (by rfl) ⟨11410125, by rfl⟩ : syracuseStep 30427001 = 22820251) B22820251
theorem B1583039 : Blo 1582489 1583039 := bstep (se 1 (by rfl) ⟨1187279, by rfl⟩ : syracuseStep 1583039 = 2374559) B2374559
theorem B6416347 : Blo 1582489 6416347 := bstep (se 1 (by rfl) ⟨4812260, by rfl⟩ : syracuseStep 6416347 = 9624521) B9624521
theorem B1583071 : Blo 1582489 1583071 := bstep (se 1 (by rfl) ⟨1187303, by rfl⟩ : syracuseStep 1583071 = 2374607) B2374607
theorem B1583131 : Blo 1582489 1583131 := bstep (se 1 (by rfl) ⟨1187348, by rfl⟩ : syracuseStep 1583131 = 2374697) B2374697
theorem B1583135 : Blo 1582489 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B1583151 : Blo 1582489 1583151 := bstep (se 1 (by rfl) ⟨1187363, by rfl⟩ : syracuseStep 1583151 = 2374727) B2374727
theorem B12028013 : Blo 1582489 12028013 := bstep (se 3 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 12028013 = 4510505) B4510505
theorem B1583327 : Blo 1582489 1583327 := bstep (se 1 (by rfl) ⟨1187495, by rfl⟩ : syracuseStep 1583327 = 2374991) B2374991
theorem B5343515 : Blo 1582489 5343515 := bstep (se 1 (by rfl) ⟨4007636, by rfl⟩ : syracuseStep 5343515 = 8015273) B8015273
theorem B1583387 : Blo 1582489 1583387 := bstep (se 1 (by rfl) ⟨1187540, by rfl⟩ : syracuseStep 1583387 = 2375081) B2375081
theorem B1583487 : Blo 1582489 1583487 := bstep (se 1 (by rfl) ⟨1187615, by rfl⟩ : syracuseStep 1583487 = 2375231) B2375231
theorem B5343677 : Blo 1582489 5343677 := bstep (se 3 (by rfl) ⟨1001939, by rfl⟩ : syracuseStep 5343677 = 2003879) B2003879
theorem B1583663 : Blo 1582489 1583663 := bstep (se 1 (by rfl) ⟨1187747, by rfl⟩ : syracuseStep 1583663 = 2375495) B2375495
theorem B61680203 : Blo 1582489 61680203 := bstep (se 1 (by rfl) ⟨46260152, by rfl⟩ : syracuseStep 61680203 = 92520305) B92520305
theorem B5343839 : Blo 1582489 5343839 := bstep (se 1 (by rfl) ⟨4007879, by rfl⟩ : syracuseStep 5343839 = 8015759) B8015759
theorem B1829479 : Blo 1582489 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B1583719 : Blo 1582489 1583719 := bstep (se 1 (by rfl) ⟨1187789, by rfl⟩ : syracuseStep 1583719 = 2375579) B2375579
theorem B1780519 : Blo 1582489 1780519 := bstep (se 1 (by rfl) ⟨1335389, by rfl⟩ : syracuseStep 1780519 = 2670779) B2670779
theorem B1927975 : Blo 1582489 1927975 := bstep (se 1 (by rfl) ⟨1445981, by rfl⟩ : syracuseStep 1927975 = 2891963) B2891963
theorem B10832899 : Blo 1582489 10832899 := bstep (se 1 (by rfl) ⟨8124674, by rfl⟩ : syracuseStep 10832899 = 16249349) B16249349
theorem B1690799 : Blo 1582489 1690799 := bstep (se 1 (by rfl) ⟨1268099, by rfl⟩ : syracuseStep 1690799 = 2536199) B2536199
theorem B5074103 : Blo 1582489 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B3804347 : Blo 1582489 3804347 := bstep (se 1 (by rfl) ⟨2853260, by rfl⟩ : syracuseStep 3804347 = 5706521) B5706521
theorem B192834989 : Blo 1582489 192834989 := bstep (se 3 (by rfl) ⟨36156560, by rfl⟩ : syracuseStep 192834989 = 72313121) B72313121
theorem B6434311 : Blo 1582489 6434311 := bstep (se 1 (by rfl) ⟨4825733, by rfl⟩ : syracuseStep 6434311 = 9651467) B9651467
theorem B158232527 : Blo 1582489 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B6008813 : Blo 1582489 6008813 := bstep (se 3 (by rfl) ⟨1126652, by rfl⟩ : syracuseStep 6008813 = 2253305) B2253305
theorem B1781743 : Blo 1582489 1781743 := bstep (se 1 (by rfl) ⟨1336307, by rfl⟩ : syracuseStep 1781743 = 2672615) B2672615
theorem B1781887 : Blo 1582489 1781887 := bstep (se 1 (by rfl) ⟨1336415, by rfl⟩ : syracuseStep 1781887 = 2672831) B2672831
theorem B3805471 : Blo 1582489 3805471 := bstep (se 1 (by rfl) ⟨2854103, by rfl⟩ : syracuseStep 3805471 = 5708207) B5708207
theorem B5345567 : Blo 1582489 5345567 := bstep (se 1 (by rfl) ⟨4009175, by rfl⟩ : syracuseStep 5345567 = 8018351) B8018351
theorem B7606865 : Blo 1582489 7606865 := bstep (se 2 (by rfl) ⟨2852574, by rfl⟩ : syracuseStep 7606865 = 5705149) B5705149
theorem B11416585 : Blo 1582489 11416585 := bstep (se 2 (by rfl) ⟨4281219, by rfl⟩ : syracuseStep 11416585 = 8562439) B8562439
theorem B13522085 : Blo 1582489 13522085 := bstep (se 4 (by rfl) ⟨1267695, by rfl⟩ : syracuseStep 13522085 = 2535391) B2535391
theorem B624612941 : Blo 1582489 624612941 := bstep (se 3 (by rfl) ⟨117114926, by rfl⟩ : syracuseStep 624612941 = 234229853) B234229853
theorem B6010483 : Blo 1582489 6010483 := bstep (se 1 (by rfl) ⟨4507862, by rfl⟩ : syracuseStep 6010483 = 9015725) B9015725
theorem B13530833 : Blo 1582489 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B7608019 : Blo 1582489 7608019 := bstep (se 1 (by rfl) ⟨5706014, by rfl⟩ : syracuseStep 7608019 = 11412029) B11412029
theorem B6764255 : Blo 1582489 6764255 := bstep (se 1 (by rfl) ⟨5073191, by rfl⟩ : syracuseStep 6764255 = 10146383) B10146383
theorem B12842813 : Blo 1582489 12842813 := bstep (se 3 (by rfl) ⟨2408027, by rfl⟩ : syracuseStep 12842813 = 4816055) B4816055
theorem B3561299 : Blo 1582489 3561299 := bstep (se 1 (by rfl) ⟨2670974, by rfl⟩ : syracuseStep 3561299 = 5341949) B5341949
theorem B3381239 : Blo 1582489 3381239 := bstep (se 1 (by rfl) ⟨2535929, by rfl⟩ : syracuseStep 3381239 = 5071859) B5071859
theorem B2373815 : Blo 1582489 2373815 := bstep (se 1 (by rfl) ⟨1780361, by rfl⟩ : syracuseStep 2373815 = 3560723) B3560723
theorem B2373863 : Blo 1582489 2373863 := bstep (se 1 (by rfl) ⟨1780397, by rfl⟩ : syracuseStep 2373863 = 3560795) B3560795
theorem B5708063 : Blo 1582489 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B3561785 : Blo 1582489 3561785 := bstep (se 2 (by rfl) ⟨1335669, by rfl⟩ : syracuseStep 3561785 = 2671339) B2671339
theorem B6011243 : Blo 1582489 6011243 := bstep (se 1 (by rfl) ⟨4508432, by rfl⟩ : syracuseStep 6011243 = 9016865) B9016865
theorem B190085717 : Blo 1582489 190085717 := bstep (se 8 (by rfl) ⟨1113783, by rfl⟩ : syracuseStep 190085717 = 2227567) B2227567
theorem B2374235 : Blo 1582489 2374235 := bstep (se 1 (by rfl) ⟨1780676, by rfl⟩ : syracuseStep 2374235 = 3561353) B3561353
theorem B2374379 : Blo 1582489 2374379 := bstep (se 1 (by rfl) ⟨1780784, by rfl⟩ : syracuseStep 2374379 = 3561569) B3561569
theorem B2374409 : Blo 1582489 2374409 := bstep (se 2 (by rfl) ⟨890403, by rfl⟩ : syracuseStep 2374409 = 1780807) B1780807
theorem B4119407 : Blo 1582489 4119407 := bstep (se 1 (by rfl) ⟨3089555, by rfl⟩ : syracuseStep 4119407 = 6179111) B6179111
theorem B7609211 : Blo 1582489 7609211 := bstep (se 1 (by rfl) ⟨5706908, by rfl⟩ : syracuseStep 7609211 = 11413817) B11413817
theorem B15211577 : Blo 1582489 15211577 := bstep (se 2 (by rfl) ⟨5704341, by rfl⟩ : syracuseStep 15211577 = 11408683) B11408683
theorem B3005561 : Blo 1582489 3005561 := bstep (se 2 (by rfl) ⟨1127085, by rfl⟩ : syracuseStep 3005561 = 2254171) B2254171
theorem B3382393 : Blo 1582489 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B3562703 : Blo 1582489 3562703 := bstep (se 1 (by rfl) ⟨2672027, by rfl⟩ : syracuseStep 3562703 = 5344055) B5344055
theorem B4570337 : Blo 1582489 4570337 := bstep (se 2 (by rfl) ⟨1713876, by rfl⟩ : syracuseStep 4570337 = 3427753) B3427753
theorem B12025097 : Blo 1582489 12025097 := bstep (se 2 (by rfl) ⟨4509411, by rfl⟩ : syracuseStep 12025097 = 9018823) B9018823
theorem B6012413 : Blo 1582489 6012413 := bstep (se 3 (by rfl) ⟨1127327, by rfl⟩ : syracuseStep 6012413 = 2254655) B2254655
theorem B3563081 : Blo 1582489 3563081 := bstep (se 2 (by rfl) ⟨1336155, by rfl⟩ : syracuseStep 3563081 = 2672311) B2672311
theorem B2375279 : Blo 1582489 2375279 := bstep (se 1 (by rfl) ⟨1781459, by rfl⟩ : syracuseStep 2375279 = 3562919) B3562919
theorem B2375399 : Blo 1582489 2375399 := bstep (se 1 (by rfl) ⟨1781549, by rfl⟩ : syracuseStep 2375399 = 3563099) B3563099
theorem B3006305 : Blo 1582489 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B2375591 : Blo 1582489 2375591 := bstep (se 1 (by rfl) ⟨1781693, by rfl⟩ : syracuseStep 2375591 = 3563387) B3563387
theorem B8011709 : Blo 1582489 8011709 := bstep (se 3 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 8011709 = 3004391) B3004391
theorem B2375849 : Blo 1582489 2375849 := bstep (se 2 (by rfl) ⟨890943, by rfl⟩ : syracuseStep 2375849 = 1781887) B1781887
theorem B3563711 : Blo 1582489 3563711 := bstep (se 1 (by rfl) ⟨2672783, by rfl⟩ : syracuseStep 3563711 = 5345567) B5345567
theorem B2670799 : Blo 1582489 2670799 := bstep (se 1 (by rfl) ⟨2003099, by rfl⟩ : syracuseStep 2670799 = 4006199) B4006199
theorem B5071243 : Blo 1582489 5071243 := bstep (se 1 (by rfl) ⟨3803432, by rfl⟩ : syracuseStep 5071243 = 7606865) B7606865
theorem B6013399 : Blo 1582489 6013399 := bstep (se 1 (by rfl) ⟨4510049, by rfl⟩ : syracuseStep 6013399 = 9020099) B9020099
theorem B416408627 : Blo 1582489 416408627 := bstep (se 1 (by rfl) ⟨312306470, by rfl⟩ : syracuseStep 416408627 = 624612941) B624612941
theorem B9020555 : Blo 1582489 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B6014159 : Blo 1582489 6014159 := bstep (se 1 (by rfl) ⟨4510619, by rfl⟩ : syracuseStep 6014159 = 9021239) B9021239
theorem B8561875 : Blo 1582489 8561875 := bstep (se 1 (by rfl) ⟨6421406, by rfl⟩ : syracuseStep 8561875 = 12842813) B12842813
theorem B20284667 : Blo 1582489 20284667 := bstep (se 1 (by rfl) ⟨15213500, by rfl⟩ : syracuseStep 20284667 = 30427001) B30427001
theorem B2254159 : Blo 1582489 2254159 := bstep (se 1 (by rfl) ⟨1690619, by rfl⟩ : syracuseStep 2254159 = 3381239) B3381239
theorem B14443865 : Blo 1582489 14443865 := bstep (se 2 (by rfl) ⟨5416449, by rfl⟩ : syracuseStep 14443865 = 10832899) B10832899
theorem B15222113 : Blo 1582489 15222113 := bstep (se 2 (by rfl) ⟨5708292, by rfl⟩ : syracuseStep 15222113 = 11416585) B11416585
theorem B1582543 : Blo 1582489 1582543 := bstep (se 1 (by rfl) ⟨1186907, by rfl⟩ : syracuseStep 1582543 = 2373815) B2373815
theorem B1582575 : Blo 1582489 1582575 := bstep (se 1 (by rfl) ⟨1186931, by rfl⟩ : syracuseStep 1582575 = 2373863) B2373863
theorem B4007495 : Blo 1582489 4007495 := bstep (se 1 (by rfl) ⟨3005621, by rfl⟩ : syracuseStep 4007495 = 6011243) B6011243
theorem B1582823 : Blo 1582489 1582823 := bstep (se 1 (by rfl) ⟨1187117, by rfl⟩ : syracuseStep 1582823 = 2374235) B2374235
theorem B1582919 : Blo 1582489 1582919 := bstep (se 1 (by rfl) ⟨1187189, by rfl⟩ : syracuseStep 1582919 = 2374379) B2374379
theorem B1582939 : Blo 1582489 1582939 := bstep (se 1 (by rfl) ⟨1187204, by rfl⟩ : syracuseStep 1582939 = 2374409) B2374409
theorem B2746271 : Blo 1582489 2746271 := bstep (se 1 (by rfl) ⟨2059703, by rfl⟩ : syracuseStep 2746271 = 4119407) B4119407
theorem B5072807 : Blo 1582489 5072807 := bstep (se 1 (by rfl) ⟨3804605, by rfl⟩ : syracuseStep 5072807 = 7609211) B7609211
theorem B8579081 : Blo 1582489 8579081 := bstep (se 2 (by rfl) ⟨3217155, by rfl⟩ : syracuseStep 8579081 = 6434311) B6434311
theorem B8013977 : Blo 1582489 8013977 := bstep (se 2 (by rfl) ⟨3005241, by rfl⟩ : syracuseStep 8013977 = 6010483) B6010483
theorem B10144025 : Blo 1582489 10144025 := bstep (se 2 (by rfl) ⟨3804009, by rfl⟩ : syracuseStep 10144025 = 7608019) B7608019
theorem B4008275 : Blo 1582489 4008275 := bstep (se 1 (by rfl) ⟨3006206, by rfl⟩ : syracuseStep 4008275 = 6012413) B6012413
theorem B1583519 : Blo 1582489 1583519 := bstep (se 1 (by rfl) ⟨1187639, by rfl⟩ : syracuseStep 1583519 = 2375279) B2375279
theorem B1583599 : Blo 1582489 1583599 := bstep (se 1 (by rfl) ⟨1187699, by rfl⟩ : syracuseStep 1583599 = 2375399) B2375399
theorem B1583727 : Blo 1582489 1583727 := bstep (se 1 (by rfl) ⟨1187795, by rfl⟩ : syracuseStep 1583727 = 2375591) B2375591
theorem B8555129 : Blo 1582489 8555129 := bstep (se 2 (by rfl) ⟨3208173, by rfl⟩ : syracuseStep 8555129 = 6416347) B6416347
theorem B1583943 : Blo 1582489 1583943 := bstep (se 1 (by rfl) ⟨1187957, by rfl⟩ : syracuseStep 1583943 = 2375915) B2375915
theorem B1780591 : Blo 1582489 1780591 := bstep (se 1 (by rfl) ⟨1335443, by rfl⟩ : syracuseStep 1780591 = 2670887) B2670887
theorem B1583983 : Blo 1582489 1583983 := bstep (se 1 (by rfl) ⟨1187987, by rfl⟩ : syracuseStep 1583983 = 2375975) B2375975
theorem B5073961 : Blo 1582489 5073961 := bstep (se 2 (by rfl) ⟨1902735, by rfl⟩ : syracuseStep 5073961 = 3805471) B3805471
theorem B4508797 : Blo 1582489 4508797 := bstep (se 3 (by rfl) ⟨845399, by rfl⟩ : syracuseStep 4508797 = 1690799) B1690799
theorem B10144925 : Blo 1582489 10144925 := bstep (se 3 (by rfl) ⟨1902173, by rfl⟩ : syracuseStep 10144925 = 3804347) B3804347
theorem B9014723 : Blo 1582489 9014723 := bstep (se 1 (by rfl) ⟨6761042, by rfl⟩ : syracuseStep 9014723 = 13522085) B13522085
theorem B4509503 : Blo 1582489 4509503 := bstep (se 1 (by rfl) ⟨3382127, by rfl⟩ : syracuseStep 4509503 = 6764255) B6764255
theorem B4509857 : Blo 1582489 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B3805375 : Blo 1582489 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B41120135 : Blo 1582489 41120135 := bstep (se 1 (by rfl) ⟨30840101, by rfl⟩ : syracuseStep 41120135 = 61680203) B61680203
theorem B2003707 : Blo 1582489 2003707 := bstep (se 1 (by rfl) ⟨1502780, by rfl⟩ : syracuseStep 2003707 = 3005561) B3005561
theorem B8016731 : Blo 1582489 8016731 := bstep (se 1 (by rfl) ⟨6012548, by rfl⟩ : syracuseStep 8016731 = 12025097) B12025097
theorem B2004203 : Blo 1582489 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B13522463 : Blo 1582489 13522463 := bstep (se 1 (by rfl) ⟨10141847, by rfl⟩ : syracuseStep 13522463 = 20283695) B20283695
theorem B8558399 : Blo 1582489 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B3004543 : Blo 1582489 3004543 := bstep (se 1 (by rfl) ⟨2253407, by rfl⟩ : syracuseStep 3004543 = 4506815) B4506815
theorem B2439305 : Blo 1582489 2439305 := bstep (se 2 (by rfl) ⟨914739, by rfl⟩ : syracuseStep 2439305 = 1829479) B1829479
theorem B3561659 : Blo 1582489 3561659 := bstep (se 1 (by rfl) ⟨2671244, by rfl⟩ : syracuseStep 3561659 = 5342489) B5342489
theorem B3660059 : Blo 1582489 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B2374025 : Blo 1582489 2374025 := bstep (se 2 (by rfl) ⟨890259, by rfl⟩ : syracuseStep 2374025 = 1780519) B1780519
theorem B2570633 : Blo 1582489 2570633 := bstep (se 2 (by rfl) ⟨963987, by rfl⟩ : syracuseStep 2570633 = 1927975) B1927975
theorem B2374199 : Blo 1582489 2374199 := bstep (se 1 (by rfl) ⟨1780649, by rfl⟩ : syracuseStep 2374199 = 3561299) B3561299
theorem B8018675 : Blo 1582489 8018675 := bstep (se 1 (by rfl) ⟨6014006, by rfl⟩ : syracuseStep 8018675 = 12028013) B12028013
theorem B3562343 : Blo 1582489 3562343 := bstep (se 1 (by rfl) ⟨2671757, by rfl⟩ : syracuseStep 3562343 = 5343515) B5343515
theorem B2374523 : Blo 1582489 2374523 := bstep (se 1 (by rfl) ⟨1780892, by rfl⟩ : syracuseStep 2374523 = 3561785) B3561785
theorem B506895245 : Blo 1582489 506895245 := bstep (se 3 (by rfl) ⟨95042858, by rfl⟩ : syracuseStep 506895245 = 190085717) B190085717
theorem B3562451 : Blo 1582489 3562451 := bstep (se 1 (by rfl) ⟨2671838, by rfl⟩ : syracuseStep 3562451 = 5343677) B5343677
theorem B3562559 : Blo 1582489 3562559 := bstep (se 1 (by rfl) ⟨2671919, by rfl⟩ : syracuseStep 3562559 = 5343839) B5343839
theorem B3562721 : Blo 1582489 3562721 := bstep (se 2 (by rfl) ⟨1336020, by rfl⟩ : syracuseStep 3562721 = 2672041) B2672041
theorem B10141051 : Blo 1582489 10141051 := bstep (se 1 (by rfl) ⟨7605788, by rfl⟩ : syracuseStep 10141051 = 15211577) B15211577
theorem B3382735 : Blo 1582489 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B2375135 : Blo 1582489 2375135 := bstep (se 1 (by rfl) ⟨1781351, by rfl⟩ : syracuseStep 2375135 = 3562703) B3562703
theorem B3046891 : Blo 1582489 3046891 := bstep (se 1 (by rfl) ⟨2285168, by rfl⟩ : syracuseStep 3046891 = 4570337) B4570337
theorem B128556659 : Blo 1582489 128556659 := bstep (se 1 (by rfl) ⟨96417494, by rfl⟩ : syracuseStep 128556659 = 192834989) B192834989
theorem B2375387 : Blo 1582489 2375387 := bstep (se 1 (by rfl) ⟨1781540, by rfl⟩ : syracuseStep 2375387 = 3563081) B3563081
theorem B5341139 : Blo 1582489 5341139 := bstep (se 1 (by rfl) ⟨4005854, by rfl⟩ : syracuseStep 5341139 = 8011709) B8011709
theorem B105488351 : Blo 1582489 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B2375657 : Blo 1582489 2375657 := bstep (se 2 (by rfl) ⟨890871, by rfl⟩ : syracuseStep 2375657 = 1781743) B1781743
theorem B4005875 : Blo 1582489 4005875 := bstep (se 1 (by rfl) ⟨3004406, by rfl⟩ : syracuseStep 4005875 = 6008813) B6008813
theorem B3006571 : Blo 1582489 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B2375807 : Blo 1582489 2375807 := bstep (se 1 (by rfl) ⟨1781855, by rfl⟩ : syracuseStep 2375807 = 3563711) B3563711
theorem B4006057 : Blo 1582489 4006057 := bstep (se 2 (by rfl) ⟨1502271, by rfl⟩ : syracuseStep 4006057 = 3004543) B3004543
theorem B6013703 : Blo 1582489 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B2671609 : Blo 1582489 2671609 := bstep (se 2 (by rfl) ⟨1001853, by rfl⟩ : syracuseStep 2671609 = 2003707) B2003707
theorem B2671663 : Blo 1582489 2671663 := bstep (se 1 (by rfl) ⟨2003747, by rfl⟩ : syracuseStep 2671663 = 4007495) B4007495
theorem B5342651 : Blo 1582489 5342651 := bstep (se 1 (by rfl) ⟨4006988, by rfl⟩ : syracuseStep 5342651 = 8013977) B8013977
theorem B2672183 : Blo 1582489 2672183 := bstep (se 1 (by rfl) ⟨2004137, by rfl⟩ : syracuseStep 2672183 = 4008275) B4008275
theorem B1582683 : Blo 1582489 1582683 := bstep (se 1 (by rfl) ⟨1187012, by rfl⟩ : syracuseStep 1582683 = 2374025) B2374025
theorem B1713755 : Blo 1582489 1713755 := bstep (se 1 (by rfl) ⟨1285316, by rfl⟩ : syracuseStep 1713755 = 2570633) B2570633
theorem B1582799 : Blo 1582489 1582799 := bstep (se 1 (by rfl) ⟨1187099, by rfl⟩ : syracuseStep 1582799 = 2374199) B2374199
theorem B5703419 : Blo 1582489 5703419 := bstep (se 1 (by rfl) ⟨4277564, by rfl⟩ : syracuseStep 5703419 = 8555129) B8555129
theorem B1583015 : Blo 1582489 1583015 := bstep (se 1 (by rfl) ⟨1187261, by rfl⟩ : syracuseStep 1583015 = 2374523) B2374523
theorem B337930163 : Blo 1582489 337930163 := bstep (se 1 (by rfl) ⟨253447622, by rfl⟩ : syracuseStep 337930163 = 506895245) B506895245
theorem B1583423 : Blo 1582489 1583423 := bstep (se 1 (by rfl) ⟨1187567, by rfl⟩ : syracuseStep 1583423 = 2375135) B2375135
theorem B13527485 : Blo 1582489 13527485 := bstep (se 3 (by rfl) ⟨2536403, by rfl⟩ : syracuseStep 13527485 = 5072807) B5072807
theorem B1583591 : Blo 1582489 1583591 := bstep (se 1 (by rfl) ⟨1187693, by rfl⟩ : syracuseStep 1583591 = 2375387) B2375387
theorem B1583771 : Blo 1582489 1583771 := bstep (se 1 (by rfl) ⟨1187828, by rfl⟩ : syracuseStep 1583771 = 2375657) B2375657
theorem B1583899 : Blo 1582489 1583899 := bstep (se 1 (by rfl) ⟨1187924, by rfl⟩ : syracuseStep 1583899 = 2375849) B2375849
theorem B5073833 : Blo 1582489 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B27413423 : Blo 1582489 27413423 := bstep (se 1 (by rfl) ⟨20560067, by rfl⟩ : syracuseStep 27413423 = 41120135) B41120135
theorem B6761657 : Blo 1582489 6761657 := bstep (se 2 (by rfl) ⟨2535621, by rfl⟩ : syracuseStep 6761657 = 5071243) B5071243
theorem B5344487 : Blo 1582489 5344487 := bstep (se 1 (by rfl) ⟨4008365, by rfl⟩ : syracuseStep 5344487 = 8016731) B8016731
theorem B5344541 : Blo 1582489 5344541 := bstep (se 3 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 5344541 = 2004203) B2004203
theorem B277605751 : Blo 1582489 277605751 := bstep (se 1 (by rfl) ⟨208204313, by rfl⟩ : syracuseStep 277605751 = 416408627) B416408627
theorem B4009439 : Blo 1582489 4009439 := bstep (se 1 (by rfl) ⟨3007079, by rfl⟩ : syracuseStep 4009439 = 6014159) B6014159
theorem B9629243 : Blo 1582489 9629243 := bstep (se 1 (by rfl) ⟨7221932, by rfl⟩ : syracuseStep 9629243 = 14443865) B14443865
theorem B9014975 : Blo 1582489 9014975 := bstep (se 1 (by rfl) ⟨6761231, by rfl⟩ : syracuseStep 9014975 = 13522463) B13522463
theorem B5705599 : Blo 1582489 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B1830847 : Blo 1582489 1830847 := bstep (se 1 (by rfl) ⟨1373135, by rfl⟩ : syracuseStep 1830847 = 2746271) B2746271
theorem B1626203 : Blo 1582489 1626203 := bstep (se 1 (by rfl) ⟨1219652, by rfl⟩ : syracuseStep 1626203 = 2439305) B2439305
theorem B6762683 : Blo 1582489 6762683 := bstep (se 1 (by rfl) ⟨5072012, by rfl⟩ : syracuseStep 6762683 = 10144025) B10144025
theorem B11415833 : Blo 1582489 11415833 := bstep (se 2 (by rfl) ⟨4280937, by rfl⟩ : syracuseStep 11415833 = 8561875) B8561875
theorem B12022181 : Blo 1582489 12022181 := bstep (se 4 (by rfl) ⟨1127079, by rfl⟩ : syracuseStep 12022181 = 2254159) B2254159
theorem B5345783 : Blo 1582489 5345783 := bstep (se 1 (by rfl) ⟨4009337, by rfl⟩ : syracuseStep 5345783 = 8018675) B8018675
theorem B13521401 : Blo 1582489 13521401 := bstep (se 2 (by rfl) ⟨5070525, by rfl⟩ : syracuseStep 13521401 = 10141051) B10141051
theorem B4510313 : Blo 1582489 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B6763283 : Blo 1582489 6763283 := bstep (se 1 (by rfl) ⟨5072462, by rfl⟩ : syracuseStep 6763283 = 10144925) B10144925
theorem B6009815 : Blo 1582489 6009815 := bstep (se 1 (by rfl) ⟨4507361, by rfl⟩ : syracuseStep 6009815 = 9014723) B9014723
theorem B3560759 : Blo 1582489 3560759 := bstep (se 1 (by rfl) ⟨2670569, by rfl⟩ : syracuseStep 3560759 = 5341139) B5341139
theorem B70325567 : Blo 1582489 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B22877549 : Blo 1582489 22877549 := bstep (se 3 (by rfl) ⟨4289540, by rfl⟩ : syracuseStep 22877549 = 8579081) B8579081
theorem B3561065 : Blo 1582489 3561065 := bstep (se 2 (by rfl) ⟨1335399, by rfl⟩ : syracuseStep 3561065 = 2670799) B2670799
theorem B8017865 : Blo 1582489 8017865 := bstep (se 2 (by rfl) ⟨3006699, by rfl⟩ : syracuseStep 8017865 = 6013399) B6013399
theorem B13523111 : Blo 1582489 13523111 := bstep (se 1 (by rfl) ⟨10142333, by rfl⟩ : syracuseStep 13523111 = 20284667) B20284667
theorem B10148075 : Blo 1582489 10148075 := bstep (se 1 (by rfl) ⟨7611056, by rfl⟩ : syracuseStep 10148075 = 15222113) B15222113
theorem B2374121 : Blo 1582489 2374121 := bstep (se 2 (by rfl) ⟨890295, by rfl⟩ : syracuseStep 2374121 = 1780591) B1780591
theorem B6765281 : Blo 1582489 6765281 := bstep (se 2 (by rfl) ⟨2536980, by rfl⟩ : syracuseStep 6765281 = 5073961) B5073961
theorem B2374439 : Blo 1582489 2374439 := bstep (se 1 (by rfl) ⟨1780829, by rfl⟩ : syracuseStep 2374439 = 3561659) B3561659
theorem B6011729 : Blo 1582489 6011729 := bstep (se 2 (by rfl) ⟨2254398, by rfl⟩ : syracuseStep 6011729 = 4508797) B4508797
theorem B2440039 : Blo 1582489 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B342817757 : Blo 1582489 342817757 := bstep (se 3 (by rfl) ⟨64278329, by rfl⟩ : syracuseStep 342817757 = 128556659) B128556659
theorem B2374895 : Blo 1582489 2374895 := bstep (se 1 (by rfl) ⟨1781171, by rfl⟩ : syracuseStep 2374895 = 3562343) B3562343
theorem B2374967 : Blo 1582489 2374967 := bstep (se 1 (by rfl) ⟨1781225, by rfl⟩ : syracuseStep 2374967 = 3562451) B3562451
theorem B4062521 : Blo 1582489 4062521 := bstep (se 2 (by rfl) ⟨1523445, by rfl⟩ : syracuseStep 4062521 = 3046891) B3046891
theorem B2375039 : Blo 1582489 2375039 := bstep (se 1 (by rfl) ⟨1781279, by rfl⟩ : syracuseStep 2375039 = 3562559) B3562559
theorem B2375147 : Blo 1582489 2375147 := bstep (se 1 (by rfl) ⟨1781360, by rfl⟩ : syracuseStep 2375147 = 3562721) B3562721
theorem B3006335 : Blo 1582489 3006335 := bstep (se 1 (by rfl) ⟨2254751, by rfl⟩ : syracuseStep 3006335 = 4509503) B4509503
theorem B2670583 : Blo 1582489 2670583 := bstep (se 1 (by rfl) ⟨2002937, by rfl⟩ : syracuseStep 2670583 = 4005875) B4005875
theorem B7610555 : Blo 1582489 7610555 := bstep (se 1 (by rfl) ⟨5707916, by rfl⟩ : syracuseStep 7610555 = 11415833) B11415833
theorem B5341409 : Blo 1582489 5341409 := bstep (se 2 (by rfl) ⟨2003028, by rfl⟩ : syracuseStep 5341409 = 4006057) B4006057
theorem B3563855 : Blo 1582489 3563855 := bstep (se 1 (by rfl) ⟨2672891, by rfl⟩ : syracuseStep 3563855 = 5345783) B5345783
theorem B3006875 : Blo 1582489 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B18031085 : Blo 1582489 18031085 := bstep (se 3 (by rfl) ⟨3380828, by rfl⟩ : syracuseStep 18031085 = 6761657) B6761657
theorem B4006543 : Blo 1582489 4006543 := bstep (se 1 (by rfl) ⟨3004907, by rfl⟩ : syracuseStep 4006543 = 6009815) B6009815
theorem B46883711 : Blo 1582489 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B3253385 : Blo 1582489 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B1582747 : Blo 1582489 1582747 := bstep (se 1 (by rfl) ⟨1187060, by rfl⟩ : syracuseStep 1582747 = 2374121) B2374121
theorem B370141001 : Blo 1582489 370141001 := bstep (se 2 (by rfl) ⟨138802875, by rfl⟩ : syracuseStep 370141001 = 277605751) B277605751
theorem B1582959 : Blo 1582489 1582959 := bstep (se 1 (by rfl) ⟨1187219, by rfl⟩ : syracuseStep 1582959 = 2374439) B2374439
theorem B4007819 : Blo 1582489 4007819 := bstep (se 1 (by rfl) ⟨3005864, by rfl⟩ : syracuseStep 4007819 = 6011729) B6011729
theorem B1583263 : Blo 1582489 1583263 := bstep (se 1 (by rfl) ⟨1187447, by rfl⟩ : syracuseStep 1583263 = 2374895) B2374895
theorem B1583311 : Blo 1582489 1583311 := bstep (se 1 (by rfl) ⟨1187483, by rfl⟩ : syracuseStep 1583311 = 2374967) B2374967
theorem B1583359 : Blo 1582489 1583359 := bstep (se 1 (by rfl) ⟨1187519, by rfl⟩ : syracuseStep 1583359 = 2375039) B2375039
theorem B2672959 : Blo 1582489 2672959 := bstep (se 1 (by rfl) ⟨2004719, by rfl⟩ : syracuseStep 2672959 = 4009439) B4009439
theorem B1583431 : Blo 1582489 1583431 := bstep (se 1 (by rfl) ⟨1187573, by rfl⟩ : syracuseStep 1583431 = 2375147) B2375147
theorem B1583871 : Blo 1582489 1583871 := bstep (se 1 (by rfl) ⟨1187903, by rfl⟩ : syracuseStep 1583871 = 2375807) B2375807
theorem B4508455 : Blo 1582489 4508455 := bstep (se 1 (by rfl) ⟨3381341, by rfl⟩ : syracuseStep 4508455 = 6762683) B6762683
theorem B4008761 : Blo 1582489 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B4336541 : Blo 1582489 4336541 := bstep (se 3 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 4336541 = 1626203) B1626203
theorem B8014787 : Blo 1582489 8014787 := bstep (se 1 (by rfl) ⟨6011090, by rfl⟩ : syracuseStep 8014787 = 12022181) B12022181
theorem B9014267 : Blo 1582489 9014267 := bstep (se 1 (by rfl) ⟨6760700, by rfl⟩ : syracuseStep 9014267 = 13521401) B13521401
theorem B4009135 : Blo 1582489 4009135 := bstep (se 1 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 4009135 = 6013703) B6013703
theorem B4508855 : Blo 1582489 4508855 := bstep (se 1 (by rfl) ⟨3381641, by rfl⟩ : syracuseStep 4508855 = 6763283) B6763283
theorem B10833389 : Blo 1582489 10833389 := bstep (se 3 (by rfl) ⟨2031260, by rfl⟩ : syracuseStep 10833389 = 4062521) B4062521
theorem B1781455 : Blo 1582489 1781455 := bstep (se 1 (by rfl) ⟨1336091, by rfl⟩ : syracuseStep 1781455 = 2672183) B2672183
theorem B5345243 : Blo 1582489 5345243 := bstep (se 1 (by rfl) ⟨4008932, by rfl⟩ : syracuseStep 5345243 = 8017865) B8017865
theorem B9015407 : Blo 1582489 9015407 := bstep (se 1 (by rfl) ⟨6761555, by rfl⟩ : syracuseStep 9015407 = 13523111) B13523111
theorem B4510187 : Blo 1582489 4510187 := bstep (se 1 (by rfl) ⟨3382640, by rfl⟩ : syracuseStep 4510187 = 6765281) B6765281
theorem B228545171 : Blo 1582489 228545171 := bstep (se 1 (by rfl) ⟨171408878, by rfl⟩ : syracuseStep 228545171 = 342817757) B342817757
theorem B15209117 : Blo 1582489 15209117 := bstep (se 3 (by rfl) ⟨2851709, by rfl⟩ : syracuseStep 15209117 = 5703419) B5703419
theorem B8016893 : Blo 1582489 8016893 := bstep (se 3 (by rfl) ⟨1503167, by rfl⟩ : syracuseStep 8016893 = 3006335) B3006335
theorem B6419495 : Blo 1582489 6419495 := bstep (se 1 (by rfl) ⟨4814621, by rfl⟩ : syracuseStep 6419495 = 9629243) B9629243
theorem B6009983 : Blo 1582489 6009983 := bstep (se 1 (by rfl) ⟨4507487, by rfl⟩ : syracuseStep 6009983 = 9014975) B9014975
theorem B7607465 : Blo 1582489 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B3560777 : Blo 1582489 3560777 := bstep (se 2 (by rfl) ⟨1335291, by rfl⟩ : syracuseStep 3560777 = 2670583) B2670583
theorem B2373839 : Blo 1582489 2373839 := bstep (se 1 (by rfl) ⟨1780379, by rfl⟩ : syracuseStep 2373839 = 3560759) B3560759
theorem B15251699 : Blo 1582489 15251699 := bstep (se 1 (by rfl) ⟨11438774, by rfl⟩ : syracuseStep 15251699 = 22877549) B22877549
theorem B3561767 : Blo 1582489 3561767 := bstep (se 1 (by rfl) ⟨2671325, by rfl⟩ : syracuseStep 3561767 = 5342651) B5342651
theorem B2374043 : Blo 1582489 2374043 := bstep (se 1 (by rfl) ⟨1780532, by rfl⟩ : syracuseStep 2374043 = 3561065) B3561065
theorem B225286775 : Blo 1582489 225286775 := bstep (se 1 (by rfl) ⟨168965081, by rfl⟩ : syracuseStep 225286775 = 337930163) B337930163
theorem B3562145 : Blo 1582489 3562145 := bstep (se 2 (by rfl) ⟨1335804, by rfl⟩ : syracuseStep 3562145 = 2671609) B2671609
theorem B3562217 : Blo 1582489 3562217 := bstep (se 2 (by rfl) ⟨1335831, by rfl⟩ : syracuseStep 3562217 = 2671663) B2671663
theorem B6765383 : Blo 1582489 6765383 := bstep (se 1 (by rfl) ⟨5074037, by rfl⟩ : syracuseStep 6765383 = 10148075) B10148075
theorem B4570013 : Blo 1582489 4570013 := bstep (se 3 (by rfl) ⟨856877, by rfl⟩ : syracuseStep 4570013 = 1713755) B1713755
theorem B9018323 : Blo 1582489 9018323 := bstep (se 1 (by rfl) ⟨6763742, by rfl⟩ : syracuseStep 9018323 = 13527485) B13527485
theorem B3382555 : Blo 1582489 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B18275615 : Blo 1582489 18275615 := bstep (se 1 (by rfl) ⟨13706711, by rfl⟩ : syracuseStep 18275615 = 27413423) B27413423
theorem B3562991 : Blo 1582489 3562991 := bstep (se 1 (by rfl) ⟨2672243, by rfl⟩ : syracuseStep 3562991 = 5344487) B5344487
theorem B3563027 : Blo 1582489 3563027 := bstep (se 1 (by rfl) ⟨2672270, by rfl⟩ : syracuseStep 3563027 = 5344541) B5344541
theorem B2441129 : Blo 1582489 2441129 := bstep (se 2 (by rfl) ⟨915423, by rfl⟩ : syracuseStep 2441129 = 1830847) B1830847
theorem B2375903 : Blo 1582489 2375903 := bstep (se 1 (by rfl) ⟨1781927, by rfl⟩ : syracuseStep 2375903 = 3563855) B3563855
theorem B3006791 : Blo 1582489 3006791 := bstep (se 1 (by rfl) ⟨2255093, by rfl⟩ : syracuseStep 3006791 = 4510187) B4510187
theorem B8675693 : Blo 1582489 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B3563945 : Blo 1582489 3563945 := bstep (se 2 (by rfl) ⟨1336479, by rfl⟩ : syracuseStep 3563945 = 2672959) B2672959
theorem B152363447 : Blo 1582489 152363447 := bstep (se 1 (by rfl) ⟨114272585, by rfl⟩ : syracuseStep 152363447 = 228545171) B228545171
theorem B4006655 : Blo 1582489 4006655 := bstep (se 1 (by rfl) ⟨3004991, by rfl⟩ : syracuseStep 4006655 = 6009983) B6009983
theorem B5071643 : Blo 1582489 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B5342057 : Blo 1582489 5342057 := bstep (se 2 (by rfl) ⟨2003271, by rfl⟩ : syracuseStep 5342057 = 4006543) B4006543
theorem B246760667 : Blo 1582489 246760667 := bstep (se 1 (by rfl) ⟨185070500, by rfl⟩ : syracuseStep 246760667 = 370141001) B370141001
theorem B2671879 : Blo 1582489 2671879 := bstep (se 1 (by rfl) ⟨2003909, by rfl⟩ : syracuseStep 2671879 = 4007819) B4007819
theorem B1582559 : Blo 1582489 1582559 := bstep (se 1 (by rfl) ⟨1186919, by rfl⟩ : syracuseStep 1582559 = 2373839) B2373839
theorem B1582695 : Blo 1582489 1582695 := bstep (se 1 (by rfl) ⟨1187021, by rfl⟩ : syracuseStep 1582695 = 2374043) B2374043
theorem B2672507 : Blo 1582489 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B5343191 : Blo 1582489 5343191 := bstep (se 1 (by rfl) ⟨4007393, by rfl⟩ : syracuseStep 5343191 = 8014787) B8014787
theorem B12183743 : Blo 1582489 12183743 := bstep (se 1 (by rfl) ⟨9137807, by rfl⟩ : syracuseStep 12183743 = 18275615) B18275615
theorem B12020723 : Blo 1582489 12020723 := bstep (se 1 (by rfl) ⟨9015542, by rfl⟩ : syracuseStep 12020723 = 18031085) B18031085
theorem B20294813 : Blo 1582489 20294813 := bstep (se 3 (by rfl) ⟨3805277, by rfl⟩ : syracuseStep 20294813 = 7610555) B7610555
theorem B31255807 : Blo 1582489 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B5344595 : Blo 1582489 5344595 := bstep (se 1 (by rfl) ⟨4008446, by rfl⟩ : syracuseStep 5344595 = 8016893) B8016893
theorem B4279663 : Blo 1582489 4279663 := bstep (se 1 (by rfl) ⟨3209747, by rfl⟩ : syracuseStep 4279663 = 6419495) B6419495
theorem B5345513 : Blo 1582489 5345513 := bstep (se 2 (by rfl) ⟨2004567, by rfl⟩ : syracuseStep 5345513 = 4009135) B4009135
theorem B4510073 : Blo 1582489 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B4510255 : Blo 1582489 4510255 := bstep (se 1 (by rfl) ⟨3382691, by rfl⟩ : syracuseStep 4510255 = 6765383) B6765383
theorem B6009511 : Blo 1582489 6009511 := bstep (se 1 (by rfl) ⟨4507133, by rfl⟩ : syracuseStep 6009511 = 9014267) B9014267
theorem B7222259 : Blo 1582489 7222259 := bstep (se 1 (by rfl) ⟨5416694, by rfl⟩ : syracuseStep 7222259 = 10833389) B10833389
theorem B6509677 : Blo 1582489 6509677 := bstep (se 3 (by rfl) ⟨1220564, by rfl⟩ : syracuseStep 6509677 = 2441129) B2441129
theorem B6010271 : Blo 1582489 6010271 := bstep (se 1 (by rfl) ⟨4507703, by rfl⟩ : syracuseStep 6010271 = 9015407) B9015407
theorem B3560939 : Blo 1582489 3560939 := bstep (se 1 (by rfl) ⟨2670704, by rfl⟩ : syracuseStep 3560939 = 5341409) B5341409
theorem B2004583 : Blo 1582489 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B10139411 : Blo 1582489 10139411 := bstep (se 1 (by rfl) ⟨7604558, by rfl⟩ : syracuseStep 10139411 = 15209117) B15209117
theorem B40671197 : Blo 1582489 40671197 := bstep (se 3 (by rfl) ⟨7625849, by rfl⟩ : syracuseStep 40671197 = 15251699) B15251699
theorem B2373851 : Blo 1582489 2373851 := bstep (se 1 (by rfl) ⟨1780388, by rfl⟩ : syracuseStep 2373851 = 3560777) B3560777
theorem B6011273 : Blo 1582489 6011273 := bstep (se 2 (by rfl) ⟨2254227, by rfl⟩ : syracuseStep 6011273 = 4508455) B4508455
theorem B2374511 : Blo 1582489 2374511 := bstep (se 1 (by rfl) ⟨1780883, by rfl⟩ : syracuseStep 2374511 = 3561767) B3561767
theorem B150191183 : Blo 1582489 150191183 := bstep (se 1 (by rfl) ⟨112643387, by rfl⟩ : syracuseStep 150191183 = 225286775) B225286775
theorem B2374763 : Blo 1582489 2374763 := bstep (se 1 (by rfl) ⟨1781072, by rfl⟩ : syracuseStep 2374763 = 3562145) B3562145
theorem B2374811 : Blo 1582489 2374811 := bstep (se 1 (by rfl) ⟨1781108, by rfl⟩ : syracuseStep 2374811 = 3562217) B3562217
theorem B2891027 : Blo 1582489 2891027 := bstep (se 1 (by rfl) ⟨2168270, by rfl⟩ : syracuseStep 2891027 = 4336541) B4336541
theorem B3046675 : Blo 1582489 3046675 := bstep (se 1 (by rfl) ⟨2285006, by rfl⟩ : syracuseStep 3046675 = 4570013) B4570013
theorem B6012215 : Blo 1582489 6012215 := bstep (se 1 (by rfl) ⟨4509161, by rfl⟩ : syracuseStep 6012215 = 9018323) B9018323
theorem B3005903 : Blo 1582489 3005903 := bstep (se 1 (by rfl) ⟨2254427, by rfl⟩ : syracuseStep 3005903 = 4508855) B4508855
theorem B2375273 : Blo 1582489 2375273 := bstep (se 2 (by rfl) ⟨890727, by rfl⟩ : syracuseStep 2375273 = 1781455) B1781455
theorem B2375327 : Blo 1582489 2375327 := bstep (se 1 (by rfl) ⟨1781495, by rfl⟩ : syracuseStep 2375327 = 3562991) B3562991
theorem B2375351 : Blo 1582489 2375351 := bstep (se 1 (by rfl) ⟨1781513, by rfl⟩ : syracuseStep 2375351 = 3563027) B3563027
theorem B3563495 : Blo 1582489 3563495 := bstep (se 1 (by rfl) ⟨2672621, by rfl⟩ : syracuseStep 3563495 = 5345243) B5345243
theorem B3563675 : Blo 1582489 3563675 := bstep (se 1 (by rfl) ⟨2672756, by rfl⟩ : syracuseStep 3563675 = 5345513) B5345513
theorem B5783795 : Blo 1582489 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B3006715 : Blo 1582489 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B2375963 : Blo 1582489 2375963 := bstep (se 1 (by rfl) ⟨1781972, by rfl⟩ : syracuseStep 2375963 = 3563945) B3563945
theorem B32489981 : Blo 1582489 32489981 := bstep (se 3 (by rfl) ⟨6091871, by rfl⟩ : syracuseStep 32489981 = 12183743) B12183743
theorem B2671103 : Blo 1582489 2671103 := bstep (se 1 (by rfl) ⟨2003327, by rfl⟩ : syracuseStep 2671103 = 4006655) B4006655
theorem B6013673 : Blo 1582489 6013673 := bstep (se 2 (by rfl) ⟨2255127, by rfl⟩ : syracuseStep 6013673 = 4510255) B4510255
theorem B8012681 : Blo 1582489 8012681 := bstep (se 2 (by rfl) ⟨3004755, by rfl⟩ : syracuseStep 8012681 = 6009511) B6009511
theorem B4006847 : Blo 1582489 4006847 := bstep (se 1 (by rfl) ⟨3005135, by rfl⟩ : syracuseStep 4006847 = 6010271) B6010271
theorem B6759607 : Blo 1582489 6759607 := bstep (se 1 (by rfl) ⟨5069705, by rfl⟩ : syracuseStep 6759607 = 10139411) B10139411
theorem B1582567 : Blo 1582489 1582567 := bstep (se 1 (by rfl) ⟨1186925, by rfl⟩ : syracuseStep 1582567 = 2373851) B2373851
theorem B4007515 : Blo 1582489 4007515 := bstep (se 1 (by rfl) ⟨3005636, by rfl⟩ : syracuseStep 4007515 = 6011273) B6011273
theorem B41674409 : Blo 1582489 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B1583007 : Blo 1582489 1583007 := bstep (se 1 (by rfl) ⟨1187255, by rfl⟩ : syracuseStep 1583007 = 2374511) B2374511
theorem B8013815 : Blo 1582489 8013815 := bstep (se 1 (by rfl) ⟨6010361, by rfl⟩ : syracuseStep 8013815 = 12020723) B12020723
theorem B1583175 : Blo 1582489 1583175 := bstep (se 1 (by rfl) ⟨1187381, by rfl⟩ : syracuseStep 1583175 = 2374763) B2374763
theorem B1583207 : Blo 1582489 1583207 := bstep (se 1 (by rfl) ⟨1187405, by rfl⟩ : syracuseStep 1583207 = 2374811) B2374811
theorem B2672777 : Blo 1582489 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B1927351 : Blo 1582489 1927351 := bstep (se 1 (by rfl) ⟨1445513, by rfl⟩ : syracuseStep 1927351 = 2891027) B2891027
theorem B4008143 : Blo 1582489 4008143 := bstep (se 1 (by rfl) ⟨3006107, by rfl⟩ : syracuseStep 4008143 = 6012215) B6012215
theorem B1583515 : Blo 1582489 1583515 := bstep (se 1 (by rfl) ⟨1187636, by rfl⟩ : syracuseStep 1583515 = 2375273) B2375273
theorem B1583551 : Blo 1582489 1583551 := bstep (se 1 (by rfl) ⟨1187663, by rfl⟩ : syracuseStep 1583551 = 2375327) B2375327
theorem B1583567 : Blo 1582489 1583567 := bstep (se 1 (by rfl) ⟨1187675, by rfl⟩ : syracuseStep 1583567 = 2375351) B2375351
theorem B1583935 : Blo 1582489 1583935 := bstep (se 1 (by rfl) ⟨1187951, by rfl⟩ : syracuseStep 1583935 = 2375903) B2375903
theorem B400509821 : Blo 1582489 400509821 := bstep (se 3 (by rfl) ⟨75095591, by rfl⟩ : syracuseStep 400509821 = 150191183) B150191183
theorem B101575631 : Blo 1582489 101575631 := bstep (se 1 (by rfl) ⟨76181723, by rfl⟩ : syracuseStep 101575631 = 152363447) B152363447
theorem B164507111 : Blo 1582489 164507111 := bstep (se 1 (by rfl) ⟨123380333, by rfl⟩ : syracuseStep 164507111 = 246760667) B246760667
theorem B1781671 : Blo 1582489 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B8679569 : Blo 1582489 8679569 := bstep (se 2 (by rfl) ⟨3254838, by rfl⟩ : syracuseStep 8679569 = 6509677) B6509677
theorem B5706217 : Blo 1582489 5706217 := bstep (se 2 (by rfl) ⟨2139831, by rfl⟩ : syracuseStep 5706217 = 4279663) B4279663
theorem B13529875 : Blo 1582489 13529875 := bstep (se 1 (by rfl) ⟨10147406, by rfl⟩ : syracuseStep 13529875 = 20294813) B20294813
theorem B2003935 : Blo 1582489 2003935 := bstep (se 1 (by rfl) ⟨1502951, by rfl⟩ : syracuseStep 2003935 = 3005903) B3005903
theorem B2004527 : Blo 1582489 2004527 := bstep (se 1 (by rfl) ⟨1503395, by rfl⟩ : syracuseStep 2004527 = 3006791) B3006791
theorem B3381095 : Blo 1582489 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B3561371 : Blo 1582489 3561371 := bstep (se 1 (by rfl) ⟨2671028, by rfl⟩ : syracuseStep 3561371 = 5342057) B5342057
theorem B4814839 : Blo 1582489 4814839 := bstep (se 1 (by rfl) ⟨3611129, by rfl⟩ : syracuseStep 4814839 = 7222259) B7222259
theorem B2373959 : Blo 1582489 2373959 := bstep (se 1 (by rfl) ⟨1780469, by rfl⟩ : syracuseStep 2373959 = 3560939) B3560939
theorem B3562127 : Blo 1582489 3562127 := bstep (se 1 (by rfl) ⟨2671595, by rfl⟩ : syracuseStep 3562127 = 5343191) B5343191
theorem B27114131 : Blo 1582489 27114131 := bstep (se 1 (by rfl) ⟨20335598, by rfl⟩ : syracuseStep 27114131 = 40671197) B40671197
theorem B3562505 : Blo 1582489 3562505 := bstep (se 2 (by rfl) ⟨1335939, by rfl⟩ : syracuseStep 3562505 = 2671879) B2671879
theorem B4062233 : Blo 1582489 4062233 := bstep (se 2 (by rfl) ⟨1523337, by rfl⟩ : syracuseStep 4062233 = 3046675) B3046675
theorem B3563063 : Blo 1582489 3563063 := bstep (se 1 (by rfl) ⟨2672297, by rfl⟩ : syracuseStep 3563063 = 5344595) B5344595
theorem B2375663 : Blo 1582489 2375663 := bstep (se 1 (by rfl) ⟨1781747, by rfl⟩ : syracuseStep 2375663 = 3563495) B3563495
theorem B2375783 : Blo 1582489 2375783 := bstep (se 1 (by rfl) ⟨1781837, by rfl⟩ : syracuseStep 2375783 = 3563675) B3563675
theorem B21659987 : Blo 1582489 21659987 := bstep (se 1 (by rfl) ⟨16244990, by rfl⟩ : syracuseStep 21659987 = 32489981) B32489981
theorem B5341787 : Blo 1582489 5341787 := bstep (se 1 (by rfl) ⟨4006340, by rfl⟩ : syracuseStep 5341787 = 8012681) B8012681
theorem B2671231 : Blo 1582489 2671231 := bstep (se 1 (by rfl) ⟨2003423, by rfl⟩ : syracuseStep 2671231 = 4006847) B4006847
theorem B18039833 : Blo 1582489 18039833 := bstep (se 2 (by rfl) ⟨6764937, by rfl⟩ : syracuseStep 18039833 = 13529875) B13529875
theorem B2254063 : Blo 1582489 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B2671913 : Blo 1582489 2671913 := bstep (se 2 (by rfl) ⟨1001967, by rfl⟩ : syracuseStep 2671913 = 2003935) B2003935
theorem B5342543 : Blo 1582489 5342543 := bstep (se 1 (by rfl) ⟨4006907, by rfl⟩ : syracuseStep 5342543 = 8013815) B8013815
theorem B2672095 : Blo 1582489 2672095 := bstep (se 1 (by rfl) ⟨2004071, by rfl⟩ : syracuseStep 2672095 = 4008143) B4008143
theorem B1582639 : Blo 1582489 1582639 := bstep (se 1 (by rfl) ⟨1186979, by rfl⟩ : syracuseStep 1582639 = 2373959) B2373959
theorem B9012809 : Blo 1582489 9012809 := bstep (se 2 (by rfl) ⟨3379803, by rfl⟩ : syracuseStep 9012809 = 6759607) B6759607
theorem B67717087 : Blo 1582489 67717087 := bstep (se 1 (by rfl) ⟨50787815, by rfl⟩ : syracuseStep 67717087 = 101575631) B101575631
theorem B5343353 : Blo 1582489 5343353 := bstep (se 2 (by rfl) ⟨2003757, by rfl⟩ : syracuseStep 5343353 = 4007515) B4007515
theorem B1583775 : Blo 1582489 1583775 := bstep (se 1 (by rfl) ⟨1187831, by rfl⟩ : syracuseStep 1583775 = 2375663) B2375663
theorem B10832621 : Blo 1582489 10832621 := bstep (se 3 (by rfl) ⟨2031116, by rfl⟩ : syracuseStep 10832621 = 4062233) B4062233
theorem B1583975 : Blo 1582489 1583975 := bstep (se 1 (by rfl) ⟨1187981, by rfl⟩ : syracuseStep 1583975 = 2375963) B2375963
theorem B4008953 : Blo 1582489 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B1780735 : Blo 1582489 1780735 := bstep (se 1 (by rfl) ⟨1335551, by rfl⟩ : syracuseStep 1780735 = 2671103) B2671103
theorem B23145517 : Blo 1582489 23145517 := bstep (se 3 (by rfl) ⟨4339784, by rfl⟩ : syracuseStep 23145517 = 8679569) B8679569
theorem B4009115 : Blo 1582489 4009115 := bstep (se 1 (by rfl) ⟨3006836, by rfl⟩ : syracuseStep 4009115 = 6013673) B6013673
theorem B27782939 : Blo 1582489 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B1781851 : Blo 1582489 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B5345405 : Blo 1582489 5345405 := bstep (se 3 (by rfl) ⟨1002263, by rfl⟩ : syracuseStep 5345405 = 2004527) B2004527
theorem B18076087 : Blo 1582489 18076087 := bstep (se 1 (by rfl) ⟨13557065, by rfl⟩ : syracuseStep 18076087 = 27114131) B27114131
theorem B267006547 : Blo 1582489 267006547 := bstep (se 1 (by rfl) ⟨200254910, by rfl⟩ : syracuseStep 267006547 = 400509821) B400509821
theorem B109671407 : Blo 1582489 109671407 := bstep (se 1 (by rfl) ⟨82253555, by rfl⟩ : syracuseStep 109671407 = 164507111) B164507111
theorem B6419785 : Blo 1582489 6419785 := bstep (se 2 (by rfl) ⟨2407419, by rfl⟩ : syracuseStep 6419785 = 4814839) B4814839
theorem B3855863 : Blo 1582489 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B2569801 : Blo 1582489 2569801 := bstep (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) B1927351
theorem B7608289 : Blo 1582489 7608289 := bstep (se 2 (by rfl) ⟨2853108, by rfl⟩ : syracuseStep 7608289 = 5706217) B5706217
theorem B2374247 : Blo 1582489 2374247 := bstep (se 1 (by rfl) ⟨1780685, by rfl⟩ : syracuseStep 2374247 = 3561371) B3561371
theorem B2374751 : Blo 1582489 2374751 := bstep (se 1 (by rfl) ⟨1781063, by rfl⟩ : syracuseStep 2374751 = 3562127) B3562127
theorem B2375003 : Blo 1582489 2375003 := bstep (se 1 (by rfl) ⟨1781252, by rfl⟩ : syracuseStep 2375003 = 3562505) B3562505
theorem B2375375 : Blo 1582489 2375375 := bstep (se 1 (by rfl) ⟨1781531, by rfl⟩ : syracuseStep 2375375 = 3563063) B3563063
theorem B2375561 : Blo 1582489 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B3563603 : Blo 1582489 3563603 := bstep (se 1 (by rfl) ⟨2672702, by rfl⟩ : syracuseStep 3563603 = 5345405) B5345405
theorem B2375801 : Blo 1582489 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B73114271 : Blo 1582489 73114271 := bstep (se 1 (by rfl) ⟨54835703, by rfl⟩ : syracuseStep 73114271 = 109671407) B109671407
theorem B12026555 : Blo 1582489 12026555 := bstep (se 1 (by rfl) ⟨9019916, by rfl⟩ : syracuseStep 12026555 = 18039833) B18039833
theorem B356008729 : Blo 1582489 356008729 := bstep (se 2 (by rfl) ⟨133503273, by rfl⟩ : syracuseStep 356008729 = 267006547) B267006547
theorem B10282301 : Blo 1582489 10282301 := bstep (se 3 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 10282301 = 3855863) B3855863
theorem B30860689 : Blo 1582489 30860689 := bstep (se 2 (by rfl) ⟨11572758, by rfl⟩ : syracuseStep 30860689 = 23145517) B23145517
theorem B1582831 : Blo 1582489 1582831 := bstep (se 1 (by rfl) ⟨1187123, by rfl⟩ : syracuseStep 1582831 = 2374247) B2374247
theorem B28886989 : Blo 1582489 28886989 := bstep (se 3 (by rfl) ⟨5416310, by rfl⟩ : syracuseStep 28886989 = 10832621) B10832621
theorem B2672635 : Blo 1582489 2672635 := bstep (se 1 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 2672635 = 4008953) B4008953
theorem B1583167 : Blo 1582489 1583167 := bstep (se 1 (by rfl) ⟨1187375, by rfl⟩ : syracuseStep 1583167 = 2374751) B2374751
theorem B3426401 : Blo 1582489 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B2672743 : Blo 1582489 2672743 := bstep (se 1 (by rfl) ⟨2004557, by rfl⟩ : syracuseStep 2672743 = 4009115) B4009115
theorem B1583335 : Blo 1582489 1583335 := bstep (se 1 (by rfl) ⟨1187501, by rfl⟩ : syracuseStep 1583335 = 2375003) B2375003
theorem B96405797 : Blo 1582489 96405797 := bstep (se 4 (by rfl) ⟨9038043, by rfl⟩ : syracuseStep 96405797 = 18076087) B18076087
theorem B1583583 : Blo 1582489 1583583 := bstep (se 1 (by rfl) ⟨1187687, by rfl⟩ : syracuseStep 1583583 = 2375375) B2375375
theorem B1583707 : Blo 1582489 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B10144385 : Blo 1582489 10144385 := bstep (se 2 (by rfl) ⟨3804144, by rfl⟩ : syracuseStep 10144385 = 7608289) B7608289
theorem B1583855 : Blo 1582489 1583855 := bstep (se 1 (by rfl) ⟨1187891, by rfl⟩ : syracuseStep 1583855 = 2375783) B2375783
theorem B1781275 : Blo 1582489 1781275 := bstep (se 1 (by rfl) ⟨1335956, by rfl⟩ : syracuseStep 1781275 = 2671913) B2671913
theorem B6008539 : Blo 1582489 6008539 := bstep (se 1 (by rfl) ⟨4506404, by rfl⟩ : syracuseStep 6008539 = 9012809) B9012809
theorem B361157797 : Blo 1582489 361157797 := bstep (se 4 (by rfl) ⟨33858543, by rfl⟩ : syracuseStep 361157797 = 67717087) B67717087
theorem B14439991 : Blo 1582489 14439991 := bstep (se 1 (by rfl) ⟨10829993, by rfl⟩ : syracuseStep 14439991 = 21659987) B21659987
theorem B3561191 : Blo 1582489 3561191 := bstep (se 1 (by rfl) ⟨2670893, by rfl⟩ : syracuseStep 3561191 = 5341787) B5341787
theorem B3561641 : Blo 1582489 3561641 := bstep (se 2 (by rfl) ⟨1335615, by rfl⟩ : syracuseStep 3561641 = 2671231) B2671231
theorem B3561695 : Blo 1582489 3561695 := bstep (se 1 (by rfl) ⟨2671271, by rfl⟩ : syracuseStep 3561695 = 5342543) B5342543
theorem B2374313 : Blo 1582489 2374313 := bstep (se 2 (by rfl) ⟨890367, by rfl⟩ : syracuseStep 2374313 = 1780735) B1780735
theorem B3562235 : Blo 1582489 3562235 := bstep (se 1 (by rfl) ⟨2671676, by rfl⟩ : syracuseStep 3562235 = 5343353) B5343353
theorem B3005417 : Blo 1582489 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B8559713 : Blo 1582489 8559713 := bstep (se 2 (by rfl) ⟨3209892, by rfl⟩ : syracuseStep 8559713 = 6419785) B6419785
theorem B3562793 : Blo 1582489 3562793 := bstep (se 2 (by rfl) ⟨1336047, by rfl⟩ : syracuseStep 3562793 = 2672095) B2672095
theorem B18521959 : Blo 1582489 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B2375735 : Blo 1582489 2375735 := bstep (se 1 (by rfl) ⟨1781801, by rfl⟩ : syracuseStep 2375735 = 3563603) B3563603
theorem B3563657 : Blo 1582489 3563657 := bstep (se 2 (by rfl) ⟨1336371, by rfl⟩ : syracuseStep 3563657 = 2672743) B2672743
theorem B48742847 : Blo 1582489 48742847 := bstep (se 1 (by rfl) ⟨36557135, by rfl⟩ : syracuseStep 48742847 = 73114271) B73114271
theorem B474678305 : Blo 1582489 474678305 := bstep (se 2 (by rfl) ⟨178004364, by rfl⟩ : syracuseStep 474678305 = 356008729) B356008729
theorem B1582875 : Blo 1582489 1582875 := bstep (se 1 (by rfl) ⟨1187156, by rfl⟩ : syracuseStep 1582875 = 2374313) B2374313
theorem B19253321 : Blo 1582489 19253321 := bstep (se 2 (by rfl) ⟨7219995, by rfl⟩ : syracuseStep 19253321 = 14439991) B14439991
theorem B1583867 : Blo 1582489 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B9137069 : Blo 1582489 9137069 := bstep (se 3 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 9137069 = 3426401) B3426401
theorem B22825901 : Blo 1582489 22825901 := bstep (se 3 (by rfl) ⟨4279856, by rfl⟩ : syracuseStep 22825901 = 8559713) B8559713
theorem B64270531 : Blo 1582489 64270531 := bstep (se 1 (by rfl) ⟨48202898, by rfl⟩ : syracuseStep 64270531 = 96405797) B96405797
theorem B6762923 : Blo 1582489 6762923 := bstep (se 1 (by rfl) ⟨5072192, by rfl⟩ : syracuseStep 6762923 = 10144385) B10144385
theorem B2003611 : Blo 1582489 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B24695945 : Blo 1582489 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B38515985 : Blo 1582489 38515985 := bstep (se 2 (by rfl) ⟨14443494, by rfl⟩ : syracuseStep 38515985 = 28886989) B28886989
theorem B8017703 : Blo 1582489 8017703 := bstep (se 1 (by rfl) ⟨6013277, by rfl⟩ : syracuseStep 8017703 = 12026555) B12026555
theorem B1926174917 : Blo 1582489 1926174917 := bstep (se 4 (by rfl) ⟨180578898, by rfl⟩ : syracuseStep 1926174917 = 361157797) B361157797
theorem B6854867 : Blo 1582489 6854867 := bstep (se 1 (by rfl) ⟨5141150, by rfl⟩ : syracuseStep 6854867 = 10282301) B10282301
theorem B2374127 : Blo 1582489 2374127 := bstep (se 1 (by rfl) ⟨1780595, by rfl⟩ : syracuseStep 2374127 = 3561191) B3561191
theorem B2374427 : Blo 1582489 2374427 := bstep (se 1 (by rfl) ⟨1780820, by rfl⟩ : syracuseStep 2374427 = 3561641) B3561641
theorem B2374463 : Blo 1582489 2374463 := bstep (se 1 (by rfl) ⟨1780847, by rfl⟩ : syracuseStep 2374463 = 3561695) B3561695
theorem B2374823 : Blo 1582489 2374823 := bstep (se 1 (by rfl) ⟨1781117, by rfl⟩ : syracuseStep 2374823 = 3562235) B3562235
theorem B41147585 : Blo 1582489 41147585 := bstep (se 2 (by rfl) ⟨15430344, by rfl⟩ : syracuseStep 41147585 = 30860689) B30860689
theorem B2375033 : Blo 1582489 2375033 := bstep (se 2 (by rfl) ⟨890637, by rfl⟩ : syracuseStep 2375033 = 1781275) B1781275
theorem B2375195 : Blo 1582489 2375195 := bstep (se 1 (by rfl) ⟨1781396, by rfl⟩ : syracuseStep 2375195 = 3562793) B3562793
theorem B8011385 : Blo 1582489 8011385 := bstep (se 2 (by rfl) ⟨3004269, by rfl⟩ : syracuseStep 8011385 = 6008539) B6008539
theorem B3563513 : Blo 1582489 3563513 := bstep (se 2 (by rfl) ⟨1336317, by rfl⟩ : syracuseStep 3563513 = 2672635) B2672635
theorem B2375771 : Blo 1582489 2375771 := bstep (se 1 (by rfl) ⟨1781828, by rfl⟩ : syracuseStep 2375771 = 3563657) B3563657
theorem B2671481 : Blo 1582489 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B1582751 : Blo 1582489 1582751 := bstep (se 1 (by rfl) ⟨1187063, by rfl⟩ : syracuseStep 1582751 = 2374127) B2374127
theorem B1582951 : Blo 1582489 1582951 := bstep (se 1 (by rfl) ⟨1187213, by rfl⟩ : syracuseStep 1582951 = 2374427) B2374427
theorem B1582975 : Blo 1582489 1582975 := bstep (se 1 (by rfl) ⟨1187231, by rfl⟩ : syracuseStep 1582975 = 2374463) B2374463
theorem B1583215 : Blo 1582489 1583215 := bstep (se 1 (by rfl) ⟨1187411, by rfl⟩ : syracuseStep 1583215 = 2374823) B2374823
theorem B1583355 : Blo 1582489 1583355 := bstep (se 1 (by rfl) ⟨1187516, by rfl⟩ : syracuseStep 1583355 = 2375033) B2375033
theorem B1583463 : Blo 1582489 1583463 := bstep (se 1 (by rfl) ⟨1187597, by rfl⟩ : syracuseStep 1583463 = 2375195) B2375195
theorem B1583823 : Blo 1582489 1583823 := bstep (se 1 (by rfl) ⟨1187867, by rfl⟩ : syracuseStep 1583823 = 2375735) B2375735
theorem B4508615 : Blo 1582489 4508615 := bstep (se 1 (by rfl) ⟨3381461, by rfl⟩ : syracuseStep 4508615 = 6762923) B6762923
theorem B316452203 : Blo 1582489 316452203 := bstep (se 1 (by rfl) ⟨237339152, by rfl⟩ : syracuseStep 316452203 = 474678305) B474678305
theorem B25677323 : Blo 1582489 25677323 := bstep (se 1 (by rfl) ⟨19257992, by rfl⟩ : syracuseStep 25677323 = 38515985) B38515985
theorem B5345135 : Blo 1582489 5345135 := bstep (se 1 (by rfl) ⟨4008851, by rfl⟩ : syracuseStep 5345135 = 8017703) B8017703
theorem B1284116611 : Blo 1582489 1284116611 := bstep (se 1 (by rfl) ⟨963087458, by rfl⟩ : syracuseStep 1284116611 = 1926174917) B1926174917
theorem B6091379 : Blo 1582489 6091379 := bstep (se 1 (by rfl) ⟨4568534, by rfl⟩ : syracuseStep 6091379 = 9137069) B9137069
theorem B15217267 : Blo 1582489 15217267 := bstep (se 1 (by rfl) ⟨11412950, by rfl⟩ : syracuseStep 15217267 = 22825901) B22825901
theorem B27431723 : Blo 1582489 27431723 := bstep (se 1 (by rfl) ⟨20573792, by rfl⟩ : syracuseStep 27431723 = 41147585) B41147585
theorem B85694041 : Blo 1582489 85694041 := bstep (se 2 (by rfl) ⟨32135265, by rfl⟩ : syracuseStep 85694041 = 64270531) B64270531
theorem B32495231 : Blo 1582489 32495231 := bstep (se 1 (by rfl) ⟨24371423, by rfl⟩ : syracuseStep 32495231 = 48742847) B48742847
theorem B16463963 : Blo 1582489 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B12835547 : Blo 1582489 12835547 := bstep (se 1 (by rfl) ⟨9626660, by rfl⟩ : syracuseStep 12835547 = 19253321) B19253321
theorem B4569911 : Blo 1582489 4569911 := bstep (se 1 (by rfl) ⟨3427433, by rfl⟩ : syracuseStep 4569911 = 6854867) B6854867
theorem B5340923 : Blo 1582489 5340923 := bstep (se 1 (by rfl) ⟨4005692, by rfl⟩ : syracuseStep 5340923 = 8011385) B8011385
theorem B2375675 : Blo 1582489 2375675 := bstep (se 1 (by rfl) ⟨1781756, by rfl⟩ : syracuseStep 2375675 = 3563513) B3563513
theorem B1583783 : Blo 1582489 1583783 := bstep (se 1 (by rfl) ⟨1187837, by rfl⟩ : syracuseStep 1583783 = 2375675) B2375675
theorem B1583847 : Blo 1582489 1583847 := bstep (se 1 (by rfl) ⟨1187885, by rfl⟩ : syracuseStep 1583847 = 2375771) B2375771
theorem B1712155481 : Blo 1582489 1712155481 := bstep (se 2 (by rfl) ⟨642058305, by rfl⟩ : syracuseStep 1712155481 = 1284116611) B1284116611
theorem B457034885 : Blo 1582489 457034885 := bstep (se 4 (by rfl) ⟨42847020, by rfl⟩ : syracuseStep 457034885 = 85694041) B85694041
theorem B18287815 : Blo 1582489 18287815 := bstep (se 1 (by rfl) ⟨13715861, by rfl⟩ : syracuseStep 18287815 = 27431723) B27431723
theorem B1780987 : Blo 1582489 1780987 := bstep (se 1 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 1780987 = 2671481) B2671481
theorem B21663487 : Blo 1582489 21663487 := bstep (se 1 (by rfl) ⟨16247615, by rfl⟩ : syracuseStep 21663487 = 32495231) B32495231
theorem B8557031 : Blo 1582489 8557031 := bstep (se 1 (by rfl) ⟨6417773, by rfl⟩ : syracuseStep 8557031 = 12835547) B12835547
theorem B17118215 : Blo 1582489 17118215 := bstep (se 1 (by rfl) ⟨12838661, by rfl⟩ : syracuseStep 17118215 = 25677323) B25677323
theorem B3560615 : Blo 1582489 3560615 := bstep (se 1 (by rfl) ⟨2670461, by rfl⟩ : syracuseStep 3560615 = 5340923) B5340923
theorem B4060919 : Blo 1582489 4060919 := bstep (se 1 (by rfl) ⟨3045689, by rfl⟩ : syracuseStep 4060919 = 6091379) B6091379
theorem B20289689 : Blo 1582489 20289689 := bstep (se 2 (by rfl) ⟨7608633, by rfl⟩ : syracuseStep 20289689 = 15217267) B15217267
theorem B10975975 : Blo 1582489 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B3046607 : Blo 1582489 3046607 := bstep (se 1 (by rfl) ⟨2284955, by rfl⟩ : syracuseStep 3046607 = 4569911) B4569911
theorem B3005743 : Blo 1582489 3005743 := bstep (se 1 (by rfl) ⟨2254307, by rfl⟩ : syracuseStep 3005743 = 4508615) B4508615
theorem B210968135 : Blo 1582489 210968135 := bstep (se 1 (by rfl) ⟨158226101, by rfl⟩ : syracuseStep 210968135 = 316452203) B316452203
theorem B3563423 : Blo 1582489 3563423 := bstep (se 1 (by rfl) ⟨2672567, by rfl⟩ : syracuseStep 3563423 = 5345135) B5345135
theorem B11412143 : Blo 1582489 11412143 := bstep (se 1 (by rfl) ⟨8559107, by rfl⟩ : syracuseStep 11412143 = 17118215) B17118215
theorem B13526459 : Blo 1582489 13526459 := bstep (se 1 (by rfl) ⟨10144844, by rfl⟩ : syracuseStep 13526459 = 20289689) B20289689
theorem B4007657 : Blo 1582489 4007657 := bstep (se 2 (by rfl) ⟨1502871, by rfl⟩ : syracuseStep 4007657 = 3005743) B3005743
theorem B5704687 : Blo 1582489 5704687 := bstep (se 1 (by rfl) ⟨4278515, by rfl⟩ : syracuseStep 5704687 = 8557031) B8557031
theorem B24383753 : Blo 1582489 24383753 := bstep (se 2 (by rfl) ⟨9143907, by rfl⟩ : syracuseStep 24383753 = 18287815) B18287815
theorem B1141436987 : Blo 1582489 1141436987 := bstep (se 1 (by rfl) ⟨856077740, by rfl⟩ : syracuseStep 1141436987 = 1712155481) B1712155481
theorem B304689923 : Blo 1582489 304689923 := bstep (se 1 (by rfl) ⟨228517442, by rfl⟩ : syracuseStep 304689923 = 457034885) B457034885
theorem B140645423 : Blo 1582489 140645423 := bstep (se 1 (by rfl) ⟨105484067, by rfl⟩ : syracuseStep 140645423 = 210968135) B210968135
theorem B2373743 : Blo 1582489 2373743 := bstep (se 1 (by rfl) ⟨1780307, by rfl⟩ : syracuseStep 2373743 = 3560615) B3560615
theorem B58538533 : Blo 1582489 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B2374649 : Blo 1582489 2374649 := bstep (se 2 (by rfl) ⟨890493, by rfl⟩ : syracuseStep 2374649 = 1780987) B1780987
theorem B10829117 : Blo 1582489 10829117 := bstep (se 3 (by rfl) ⟨2030459, by rfl⟩ : syracuseStep 10829117 = 4060919) B4060919
theorem B2031071 : Blo 1582489 2031071 := bstep (se 1 (by rfl) ⟨1523303, by rfl⟩ : syracuseStep 2031071 = 3046607) B3046607
theorem B28884649 : Blo 1582489 28884649 := bstep (se 2 (by rfl) ⟨10831743, by rfl⟩ : syracuseStep 28884649 = 21663487) B21663487
theorem B2375615 : Blo 1582489 2375615 := bstep (se 1 (by rfl) ⟨1781711, by rfl⟩ : syracuseStep 2375615 = 3563423) B3563423
theorem B375054461 : Blo 1582489 375054461 := bstep (se 3 (by rfl) ⟨70322711, by rfl⟩ : syracuseStep 375054461 = 140645423) B140645423
theorem B2671771 : Blo 1582489 2671771 := bstep (se 1 (by rfl) ⟨2003828, by rfl⟩ : syracuseStep 2671771 = 4007657) B4007657
theorem B5416189 : Blo 1582489 5416189 := bstep (se 3 (by rfl) ⟨1015535, by rfl⟩ : syracuseStep 5416189 = 2031071) B2031071
theorem B1582495 : Blo 1582489 1582495 := bstep (se 1 (by rfl) ⟨1186871, by rfl⟩ : syracuseStep 1582495 = 2373743) B2373743
theorem B1583099 : Blo 1582489 1583099 := bstep (se 1 (by rfl) ⟨1187324, by rfl⟩ : syracuseStep 1583099 = 2374649) B2374649
theorem B7219411 : Blo 1582489 7219411 := bstep (se 1 (by rfl) ⟨5414558, by rfl⟩ : syracuseStep 7219411 = 10829117) B10829117
theorem B38512865 : Blo 1582489 38512865 := bstep (se 2 (by rfl) ⟨14442324, by rfl⟩ : syracuseStep 38512865 = 28884649) B28884649
theorem B1583743 : Blo 1582489 1583743 := bstep (se 1 (by rfl) ⟨1187807, by rfl⟩ : syracuseStep 1583743 = 2375615) B2375615
theorem B16255835 : Blo 1582489 16255835 := bstep (se 1 (by rfl) ⟨12191876, by rfl⟩ : syracuseStep 16255835 = 24383753) B24383753
theorem B760957991 : Blo 1582489 760957991 := bstep (se 1 (by rfl) ⟨570718493, by rfl⟩ : syracuseStep 760957991 = 1141436987) B1141436987
theorem B7608095 : Blo 1582489 7608095 := bstep (se 1 (by rfl) ⟨5706071, by rfl⟩ : syracuseStep 7608095 = 11412143) B11412143
theorem B203126615 : Blo 1582489 203126615 := bstep (se 1 (by rfl) ⟨152344961, by rfl⟩ : syracuseStep 203126615 = 304689923) B304689923
theorem B78051377 : Blo 1582489 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B9017639 : Blo 1582489 9017639 := bstep (se 1 (by rfl) ⟨6763229, by rfl⟩ : syracuseStep 9017639 = 13526459) B13526459
theorem B30424997 : Blo 1582489 30424997 := bstep (se 4 (by rfl) ⟨2852343, by rfl⟩ : syracuseStep 30424997 = 5704687) B5704687
theorem B250036307 : Blo 1582489 250036307 := bstep (se 1 (by rfl) ⟨187527230, by rfl⟩ : syracuseStep 250036307 = 375054461) B375054461
theorem B38503525 : Blo 1582489 38503525 := bstep (se 4 (by rfl) ⟨3609705, by rfl⟩ : syracuseStep 38503525 = 7219411) B7219411
theorem B5072063 : Blo 1582489 5072063 := bstep (se 1 (by rfl) ⟨3804047, by rfl⟩ : syracuseStep 5072063 = 7608095) B7608095
theorem B28886341 : Blo 1582489 28886341 := bstep (se 4 (by rfl) ⟨2708094, by rfl⟩ : syracuseStep 28886341 = 5416189) B5416189
theorem B135417743 : Blo 1582489 135417743 := bstep (se 1 (by rfl) ⟨101563307, by rfl⟩ : syracuseStep 135417743 = 203126615) B203126615
theorem B102700973 : Blo 1582489 102700973 := bstep (se 3 (by rfl) ⟨19256432, by rfl⟩ : syracuseStep 102700973 = 38512865) B38512865
theorem B52034251 : Blo 1582489 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B6011759 : Blo 1582489 6011759 := bstep (se 1 (by rfl) ⟨4508819, by rfl⟩ : syracuseStep 6011759 = 9017639) B9017639
theorem B3562361 : Blo 1582489 3562361 := bstep (se 2 (by rfl) ⟨1335885, by rfl⟩ : syracuseStep 3562361 = 2671771) B2671771
theorem B10837223 : Blo 1582489 10837223 := bstep (se 1 (by rfl) ⟨8127917, by rfl⟩ : syracuseStep 10837223 = 16255835) B16255835
theorem B507305327 : Blo 1582489 507305327 := bstep (se 1 (by rfl) ⟨380478995, by rfl⟩ : syracuseStep 507305327 = 760957991) B760957991
theorem B20283331 : Blo 1582489 20283331 := bstep (se 1 (by rfl) ⟨15212498, by rfl⟩ : syracuseStep 20283331 = 30424997) B30424997
theorem B166690871 : Blo 1582489 166690871 := bstep (se 1 (by rfl) ⟨125018153, by rfl⟩ : syracuseStep 166690871 = 250036307) B250036307
theorem B13525501 : Blo 1582489 13525501 := bstep (se 3 (by rfl) ⟨2536031, by rfl⟩ : syracuseStep 13525501 = 5072063) B5072063
theorem B69379001 : Blo 1582489 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B4007839 : Blo 1582489 4007839 := bstep (se 1 (by rfl) ⟨3005879, by rfl⟩ : syracuseStep 4007839 = 6011759) B6011759
theorem B27044441 : Blo 1582489 27044441 := bstep (se 2 (by rfl) ⟨10141665, by rfl⟩ : syracuseStep 27044441 = 20283331) B20283331
theorem B90278495 : Blo 1582489 90278495 := bstep (se 1 (by rfl) ⟨67708871, by rfl⟩ : syracuseStep 90278495 = 135417743) B135417743
theorem B1352814205 : Blo 1582489 1352814205 := bstep (se 3 (by rfl) ⟨253652663, by rfl⟩ : syracuseStep 1352814205 = 507305327) B507305327
theorem B38515121 : Blo 1582489 38515121 := bstep (se 2 (by rfl) ⟨14443170, by rfl⟩ : syracuseStep 38515121 = 28886341) B28886341
theorem B68467315 : Blo 1582489 68467315 := bstep (se 1 (by rfl) ⟨51350486, by rfl⟩ : syracuseStep 68467315 = 102700973) B102700973
theorem B51338033 : Blo 1582489 51338033 := bstep (se 2 (by rfl) ⟨19251762, by rfl⟩ : syracuseStep 51338033 = 38503525) B38503525
theorem B2374907 : Blo 1582489 2374907 := bstep (se 1 (by rfl) ⟨1781180, by rfl⟩ : syracuseStep 2374907 = 3562361) B3562361
theorem B7224815 : Blo 1582489 7224815 := bstep (se 1 (by rfl) ⟨5418611, by rfl⟩ : syracuseStep 7224815 = 10837223) B10837223
theorem B46252667 : Blo 1582489 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B1583271 : Blo 1582489 1583271 := bstep (se 1 (by rfl) ⟨1187453, by rfl⟩ : syracuseStep 1583271 = 2374907) B2374907
theorem B5343785 : Blo 1582489 5343785 := bstep (se 2 (by rfl) ⟨2003919, by rfl⟩ : syracuseStep 5343785 = 4007839) B4007839
theorem B111127247 : Blo 1582489 111127247 := bstep (se 1 (by rfl) ⟨83345435, by rfl⟩ : syracuseStep 111127247 = 166690871) B166690871
theorem B25676747 : Blo 1582489 25676747 := bstep (se 1 (by rfl) ⟨19257560, by rfl⟩ : syracuseStep 25676747 = 38515121) B38515121
theorem B18034001 : Blo 1582489 18034001 := bstep (se 2 (by rfl) ⟨6762750, by rfl⟩ : syracuseStep 18034001 = 13525501) B13525501
theorem B1803752273 : Blo 1582489 1803752273 := bstep (se 2 (by rfl) ⟨676407102, by rfl⟩ : syracuseStep 1803752273 = 1352814205) B1352814205
theorem B91289753 : Blo 1582489 91289753 := bstep (se 2 (by rfl) ⟨34233657, by rfl⟩ : syracuseStep 91289753 = 68467315) B68467315
theorem B19266173 : Blo 1582489 19266173 := bstep (se 3 (by rfl) ⟨3612407, by rfl⟩ : syracuseStep 19266173 = 7224815) B7224815
theorem B18029627 : Blo 1582489 18029627 := bstep (se 1 (by rfl) ⟨13522220, by rfl⟩ : syracuseStep 18029627 = 27044441) B27044441
theorem B60185663 : Blo 1582489 60185663 := bstep (se 1 (by rfl) ⟨45139247, by rfl⟩ : syracuseStep 60185663 = 90278495) B90278495
theorem B34225355 : Blo 1582489 34225355 := bstep (se 1 (by rfl) ⟨25669016, by rfl⟩ : syracuseStep 34225355 = 51338033) B51338033
theorem B60859835 : Blo 1582489 60859835 := bstep (se 1 (by rfl) ⟨45644876, by rfl⟩ : syracuseStep 60859835 = 91289753) B91289753
theorem B123340445 : Blo 1582489 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B12019751 : Blo 1582489 12019751 := bstep (se 1 (by rfl) ⟨9014813, by rfl⟩ : syracuseStep 12019751 = 18029627) B18029627
theorem B22816903 : Blo 1582489 22816903 := bstep (se 1 (by rfl) ⟨17112677, by rfl⟩ : syracuseStep 22816903 = 34225355) B34225355
theorem B74084831 : Blo 1582489 74084831 := bstep (se 1 (by rfl) ⟨55563623, by rfl⟩ : syracuseStep 74084831 = 111127247) B111127247
theorem B17117831 : Blo 1582489 17117831 := bstep (se 1 (by rfl) ⟨12838373, by rfl⟩ : syracuseStep 17117831 = 25676747) B25676747
theorem B12022667 : Blo 1582489 12022667 := bstep (se 1 (by rfl) ⟨9017000, by rfl⟩ : syracuseStep 12022667 = 18034001) B18034001
theorem B3562523 : Blo 1582489 3562523 := bstep (se 1 (by rfl) ⟨2671892, by rfl⟩ : syracuseStep 3562523 = 5343785) B5343785
theorem B12844115 : Blo 1582489 12844115 := bstep (se 1 (by rfl) ⟨9633086, by rfl⟩ : syracuseStep 12844115 = 19266173) B19266173
theorem B40123775 : Blo 1582489 40123775 := bstep (se 1 (by rfl) ⟨30092831, by rfl⟩ : syracuseStep 40123775 = 60185663) B60185663
theorem B4810006061 : Blo 1582489 4810006061 := bstep (se 3 (by rfl) ⟨901876136, by rfl⟩ : syracuseStep 4810006061 = 1803752273) B1803752273
theorem B49389887 : Blo 1582489 49389887 := bstep (se 1 (by rfl) ⟨37042415, by rfl⟩ : syracuseStep 49389887 = 74084831) B74084831
theorem B11411887 : Blo 1582489 11411887 := bstep (se 1 (by rfl) ⟨8558915, by rfl⟩ : syracuseStep 11411887 = 17117831) B17117831
theorem B106996733 : Blo 1582489 106996733 := bstep (se 3 (by rfl) ⟨20061887, by rfl⟩ : syracuseStep 106996733 = 40123775) B40123775
theorem B8013167 : Blo 1582489 8013167 := bstep (se 1 (by rfl) ⟨6009875, by rfl⟩ : syracuseStep 8013167 = 12019751) B12019751
theorem B8562743 : Blo 1582489 8562743 := bstep (se 1 (by rfl) ⟨6422057, by rfl⟩ : syracuseStep 8562743 = 12844115) B12844115
theorem B3206670707 : Blo 1582489 3206670707 := bstep (se 1 (by rfl) ⟨2405003030, by rfl⟩ : syracuseStep 3206670707 = 4810006061) B4810006061
theorem B8015111 : Blo 1582489 8015111 := bstep (se 1 (by rfl) ⟨6011333, by rfl⟩ : syracuseStep 8015111 = 12022667) B12022667
theorem B82226963 : Blo 1582489 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B30422537 : Blo 1582489 30422537 := bstep (se 2 (by rfl) ⟨11408451, by rfl⟩ : syracuseStep 30422537 = 22816903) B22816903
theorem B40573223 : Blo 1582489 40573223 := bstep (se 1 (by rfl) ⟨30429917, by rfl⟩ : syracuseStep 40573223 = 60859835) B60859835
theorem B2375015 : Blo 1582489 2375015 := bstep (se 1 (by rfl) ⟨1781261, by rfl⟩ : syracuseStep 2375015 = 3562523) B3562523
theorem B5342111 : Blo 1582489 5342111 := bstep (se 1 (by rfl) ⟨4006583, by rfl⟩ : syracuseStep 5342111 = 8013167) B8013167
theorem B5343407 : Blo 1582489 5343407 := bstep (se 1 (by rfl) ⟨4007555, by rfl⟩ : syracuseStep 5343407 = 8015111) B8015111
theorem B1583343 : Blo 1582489 1583343 := bstep (se 1 (by rfl) ⟨1187507, by rfl⟩ : syracuseStep 1583343 = 2375015) B2375015
theorem B32926591 : Blo 1582489 32926591 := bstep (se 1 (by rfl) ⟨24694943, by rfl⟩ : syracuseStep 32926591 = 49389887) B49389887
theorem B15215849 : Blo 1582489 15215849 := bstep (se 2 (by rfl) ⟨5705943, by rfl⟩ : syracuseStep 15215849 = 11411887) B11411887
theorem B71331155 : Blo 1582489 71331155 := bstep (se 1 (by rfl) ⟨53498366, by rfl⟩ : syracuseStep 71331155 = 106996733) B106996733
theorem B2137780471 : Blo 1582489 2137780471 := bstep (se 1 (by rfl) ⟨1603335353, by rfl⟩ : syracuseStep 2137780471 = 3206670707) B3206670707
theorem B54817975 : Blo 1582489 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B20281691 : Blo 1582489 20281691 := bstep (se 1 (by rfl) ⟨15211268, by rfl⟩ : syracuseStep 20281691 = 30422537) B30422537
theorem B5708495 : Blo 1582489 5708495 := bstep (se 1 (by rfl) ⟨4281371, by rfl⟩ : syracuseStep 5708495 = 8562743) B8562743
theorem B27048815 : Blo 1582489 27048815 := bstep (se 1 (by rfl) ⟨20286611, by rfl⟩ : syracuseStep 27048815 = 40573223) B40573223
theorem B2850373961 : Blo 1582489 2850373961 := bstep (se 2 (by rfl) ⟨1068890235, by rfl⟩ : syracuseStep 2850373961 = 2137780471) B2137780471
theorem B43902121 : Blo 1582489 43902121 := bstep (se 2 (by rfl) ⟨16463295, by rfl⟩ : syracuseStep 43902121 = 32926591) B32926591
theorem B73090633 : Blo 1582489 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B18032543 : Blo 1582489 18032543 := bstep (se 1 (by rfl) ⟨13524407, by rfl⟩ : syracuseStep 18032543 = 27048815) B27048815
theorem B10143899 : Blo 1582489 10143899 := bstep (se 1 (by rfl) ⟨7607924, by rfl⟩ : syracuseStep 10143899 = 15215849) B15215849
theorem B13521127 : Blo 1582489 13521127 := bstep (se 1 (by rfl) ⟨10140845, by rfl⟩ : syracuseStep 13521127 = 20281691) B20281691
theorem B3805663 : Blo 1582489 3805663 := bstep (se 1 (by rfl) ⟨2854247, by rfl⟩ : syracuseStep 3805663 = 5708495) B5708495
theorem B3561407 : Blo 1582489 3561407 := bstep (se 1 (by rfl) ⟨2671055, by rfl⟩ : syracuseStep 3561407 = 5342111) B5342111
theorem B3562271 : Blo 1582489 3562271 := bstep (se 1 (by rfl) ⟨2671703, by rfl⟩ : syracuseStep 3562271 = 5343407) B5343407
theorem B47554103 : Blo 1582489 47554103 := bstep (se 1 (by rfl) ⟨35665577, by rfl⟩ : syracuseStep 47554103 = 71331155) B71331155
theorem B1900249307 : Blo 1582489 1900249307 := bstep (se 1 (by rfl) ⟨1425186980, by rfl⟩ : syracuseStep 1900249307 = 2850373961) B2850373961
theorem B97454177 : Blo 1582489 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B5074217 : Blo 1582489 5074217 := bstep (se 2 (by rfl) ⟨1902831, by rfl⟩ : syracuseStep 5074217 = 3805663) B3805663
theorem B12021695 : Blo 1582489 12021695 := bstep (se 1 (by rfl) ⟨9016271, by rfl⟩ : syracuseStep 12021695 = 18032543) B18032543
theorem B6762599 : Blo 1582489 6762599 := bstep (se 1 (by rfl) ⟨5071949, by rfl⟩ : syracuseStep 6762599 = 10143899) B10143899
theorem B58536161 : Blo 1582489 58536161 := bstep (se 2 (by rfl) ⟨21951060, by rfl⟩ : syracuseStep 58536161 = 43902121) B43902121
theorem B18028169 : Blo 1582489 18028169 := bstep (se 2 (by rfl) ⟨6760563, by rfl⟩ : syracuseStep 18028169 = 13521127) B13521127
theorem B2374271 : Blo 1582489 2374271 := bstep (se 1 (by rfl) ⟨1780703, by rfl⟩ : syracuseStep 2374271 = 3561407) B3561407
theorem B2374847 : Blo 1582489 2374847 := bstep (se 1 (by rfl) ⟨1781135, by rfl⟩ : syracuseStep 2374847 = 3562271) B3562271
theorem B31702735 : Blo 1582489 31702735 := bstep (se 1 (by rfl) ⟨23777051, by rfl⟩ : syracuseStep 31702735 = 47554103) B47554103
theorem B12018779 : Blo 1582489 12018779 := bstep (se 1 (by rfl) ⟨9014084, by rfl⟩ : syracuseStep 12018779 = 18028169) B18028169
theorem B1582847 : Blo 1582489 1582847 := bstep (se 1 (by rfl) ⟨1187135, by rfl⟩ : syracuseStep 1582847 = 2374271) B2374271
theorem B1583231 : Blo 1582489 1583231 := bstep (se 1 (by rfl) ⟨1187423, by rfl⟩ : syracuseStep 1583231 = 2374847) B2374847
theorem B8014463 : Blo 1582489 8014463 := bstep (se 1 (by rfl) ⟨6010847, by rfl⟩ : syracuseStep 8014463 = 12021695) B12021695
theorem B4508399 : Blo 1582489 4508399 := bstep (se 1 (by rfl) ⟨3381299, by rfl⟩ : syracuseStep 4508399 = 6762599) B6762599
theorem B1266832871 : Blo 1582489 1266832871 := bstep (se 1 (by rfl) ⟨950124653, by rfl⟩ : syracuseStep 1266832871 = 1900249307) B1900249307
theorem B39024107 : Blo 1582489 39024107 := bstep (se 1 (by rfl) ⟨29268080, by rfl⟩ : syracuseStep 39024107 = 58536161) B58536161
theorem B169081253 : Blo 1582489 169081253 := bstep (se 4 (by rfl) ⟨15851367, by rfl⟩ : syracuseStep 169081253 = 31702735) B31702735
theorem B64969451 : Blo 1582489 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B3382811 : Blo 1582489 3382811 := bstep (se 1 (by rfl) ⟨2537108, by rfl⟩ : syracuseStep 3382811 = 5074217) B5074217
theorem B8012519 : Blo 1582489 8012519 := bstep (se 1 (by rfl) ⟨6009389, by rfl⟩ : syracuseStep 8012519 = 12018779) B12018779
theorem B844555247 : Blo 1582489 844555247 := bstep (se 1 (by rfl) ⟨633416435, by rfl⟩ : syracuseStep 844555247 = 1266832871) B1266832871
theorem B5342975 : Blo 1582489 5342975 := bstep (se 1 (by rfl) ⟨4007231, by rfl⟩ : syracuseStep 5342975 = 8014463) B8014463
theorem B43312967 : Blo 1582489 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B2255207 : Blo 1582489 2255207 := bstep (se 1 (by rfl) ⟨1691405, by rfl⟩ : syracuseStep 2255207 = 3382811) B3382811
theorem B26016071 : Blo 1582489 26016071 := bstep (se 1 (by rfl) ⟨19512053, by rfl⟩ : syracuseStep 26016071 = 39024107) B39024107
theorem B112720835 : Blo 1582489 112720835 := bstep (se 1 (by rfl) ⟨84540626, by rfl⟩ : syracuseStep 112720835 = 169081253) B169081253
theorem B3005599 : Blo 1582489 3005599 := bstep (se 1 (by rfl) ⟨2254199, by rfl⟩ : syracuseStep 3005599 = 4508399) B4508399
theorem B5341679 : Blo 1582489 5341679 := bstep (se 1 (by rfl) ⟨4006259, by rfl⟩ : syracuseStep 5341679 = 8012519) B8012519
theorem B563036831 : Blo 1582489 563036831 := bstep (se 1 (by rfl) ⟨422277623, by rfl⟩ : syracuseStep 563036831 = 844555247) B844555247
theorem B6013885 : Blo 1582489 6013885 := bstep (se 3 (by rfl) ⟨1127603, by rfl⟩ : syracuseStep 6013885 = 2255207) B2255207
theorem B4007465 : Blo 1582489 4007465 := bstep (se 2 (by rfl) ⟨1502799, by rfl⟩ : syracuseStep 4007465 = 3005599) B3005599
theorem B75147223 : Blo 1582489 75147223 := bstep (se 1 (by rfl) ⟨56360417, by rfl⟩ : syracuseStep 75147223 = 112720835) B112720835
theorem B69376189 : Blo 1582489 69376189 := bstep (se 3 (by rfl) ⟨13008035, by rfl⟩ : syracuseStep 69376189 = 26016071) B26016071
theorem B3561983 : Blo 1582489 3561983 := bstep (se 1 (by rfl) ⟨2671487, by rfl⟩ : syracuseStep 3561983 = 5342975) B5342975
theorem B28875311 : Blo 1582489 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B375357887 : Blo 1582489 375357887 := bstep (se 1 (by rfl) ⟨281518415, by rfl⟩ : syracuseStep 375357887 = 563036831) B563036831
theorem B2671643 : Blo 1582489 2671643 := bstep (se 1 (by rfl) ⟨2003732, by rfl⟩ : syracuseStep 2671643 = 4007465) B4007465
theorem B92501585 : Blo 1582489 92501585 := bstep (se 2 (by rfl) ⟨34688094, by rfl⟩ : syracuseStep 92501585 = 69376189) B69376189
theorem B3561119 : Blo 1582489 3561119 := bstep (se 1 (by rfl) ⟨2670839, by rfl⟩ : syracuseStep 3561119 = 5341679) B5341679
theorem B8018513 : Blo 1582489 8018513 := bstep (se 2 (by rfl) ⟨3006942, by rfl⟩ : syracuseStep 8018513 = 6013885) B6013885
theorem B2374655 : Blo 1582489 2374655 := bstep (se 1 (by rfl) ⟨1780991, by rfl⟩ : syracuseStep 2374655 = 3561983) B3561983
theorem B19250207 : Blo 1582489 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B100196297 : Blo 1582489 100196297 := bstep (se 2 (by rfl) ⟨37573611, by rfl⟩ : syracuseStep 100196297 = 75147223) B75147223
theorem B1583103 : Blo 1582489 1583103 := bstep (se 1 (by rfl) ⟨1187327, by rfl⟩ : syracuseStep 1583103 = 2374655) B2374655
theorem B1781095 : Blo 1582489 1781095 := bstep (se 1 (by rfl) ⟨1335821, by rfl⟩ : syracuseStep 1781095 = 2671643) B2671643
theorem B5345675 : Blo 1582489 5345675 := bstep (se 1 (by rfl) ⟨4009256, by rfl⟩ : syracuseStep 5345675 = 8018513) B8018513
theorem B12833471 : Blo 1582489 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B250238591 : Blo 1582489 250238591 := bstep (se 1 (by rfl) ⟨187678943, by rfl⟩ : syracuseStep 250238591 = 375357887) B375357887
theorem B61667723 : Blo 1582489 61667723 := bstep (se 1 (by rfl) ⟨46250792, by rfl⟩ : syracuseStep 61667723 = 92501585) B92501585
theorem B2374079 : Blo 1582489 2374079 := bstep (se 1 (by rfl) ⟨1780559, by rfl⟩ : syracuseStep 2374079 = 3561119) B3561119
theorem B66797531 : Blo 1582489 66797531 := bstep (se 1 (by rfl) ⟨50098148, by rfl⟩ : syracuseStep 66797531 = 100196297) B100196297
theorem B3563783 : Blo 1582489 3563783 := bstep (se 1 (by rfl) ⟨2672837, by rfl⟩ : syracuseStep 3563783 = 5345675) B5345675
theorem B1582719 : Blo 1582489 1582719 := bstep (se 1 (by rfl) ⟨1187039, by rfl⟩ : syracuseStep 1582719 = 2374079) B2374079
theorem B8555647 : Blo 1582489 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B166825727 : Blo 1582489 166825727 := bstep (se 1 (by rfl) ⟨125119295, by rfl⟩ : syracuseStep 166825727 = 250238591) B250238591
theorem B41111815 : Blo 1582489 41111815 := bstep (se 1 (by rfl) ⟨30833861, by rfl⟩ : syracuseStep 41111815 = 61667723) B61667723
theorem B2374793 : Blo 1582489 2374793 := bstep (se 2 (by rfl) ⟨890547, by rfl⟩ : syracuseStep 2374793 = 1781095) B1781095
theorem B44531687 : Blo 1582489 44531687 := bstep (se 1 (by rfl) ⟨33398765, by rfl⟩ : syracuseStep 44531687 = 66797531) B66797531
theorem B2375855 : Blo 1582489 2375855 := bstep (se 1 (by rfl) ⟨1781891, by rfl⟩ : syracuseStep 2375855 = 3563783) B3563783
theorem B1583195 : Blo 1582489 1583195 := bstep (se 1 (by rfl) ⟨1187396, by rfl⟩ : syracuseStep 1583195 = 2374793) B2374793
theorem B111217151 : Blo 1582489 111217151 := bstep (se 1 (by rfl) ⟨83412863, by rfl⟩ : syracuseStep 111217151 = 166825727) B166825727
theorem B54815753 : Blo 1582489 54815753 := bstep (se 2 (by rfl) ⟨20555907, by rfl⟩ : syracuseStep 54815753 = 41111815) B41111815
theorem B11407529 : Blo 1582489 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B29687791 : Blo 1582489 29687791 := bstep (se 1 (by rfl) ⟨22265843, by rfl⟩ : syracuseStep 29687791 = 44531687) B44531687
theorem B7605019 : Blo 1582489 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B1583903 : Blo 1582489 1583903 := bstep (se 1 (by rfl) ⟨1187927, by rfl⟩ : syracuseStep 1583903 = 2375855) B2375855
theorem B296579069 : Blo 1582489 296579069 := bstep (se 3 (by rfl) ⟨55608575, by rfl⟩ : syracuseStep 296579069 = 111217151) B111217151
theorem B36543835 : Blo 1582489 36543835 := bstep (se 1 (by rfl) ⟨27407876, by rfl⟩ : syracuseStep 36543835 = 54815753) B54815753
theorem B39583721 : Blo 1582489 39583721 := bstep (se 2 (by rfl) ⟨14843895, by rfl⟩ : syracuseStep 39583721 = 29687791) B29687791
theorem B40560101 : Blo 1582489 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B26389147 : Blo 1582489 26389147 := bstep (se 1 (by rfl) ⟨19791860, by rfl⟩ : syracuseStep 26389147 = 39583721) B39583721
theorem B197719379 : Blo 1582489 197719379 := bstep (se 1 (by rfl) ⟨148289534, by rfl⟩ : syracuseStep 197719379 = 296579069) B296579069
theorem B48725113 : Blo 1582489 48725113 := bstep (se 2 (by rfl) ⟨18271917, by rfl⟩ : syracuseStep 48725113 = 36543835) B36543835
theorem B35185529 : Blo 1582489 35185529 := bstep (se 2 (by rfl) ⟨13194573, by rfl⟩ : syracuseStep 35185529 = 26389147) B26389147
theorem B131812919 : Blo 1582489 131812919 := bstep (se 1 (by rfl) ⟨98859689, by rfl⟩ : syracuseStep 131812919 = 197719379) B197719379
theorem B64966817 : Blo 1582489 64966817 := bstep (se 2 (by rfl) ⟨24362556, by rfl⟩ : syracuseStep 64966817 = 48725113) B48725113
theorem B27040067 : Blo 1582489 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B173244845 : Blo 1582489 173244845 := bstep (se 3 (by rfl) ⟨32483408, by rfl⟩ : syracuseStep 173244845 = 64966817) B64966817
theorem B18026711 : Blo 1582489 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B93828077 : Blo 1582489 93828077 := bstep (se 3 (by rfl) ⟨17592764, by rfl⟩ : syracuseStep 93828077 = 35185529) B35185529
theorem B87875279 : Blo 1582489 87875279 := bstep (se 1 (by rfl) ⟨65906459, by rfl⟩ : syracuseStep 87875279 = 131812919) B131812919
theorem B12017807 : Blo 1582489 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B58583519 : Blo 1582489 58583519 := bstep (se 1 (by rfl) ⟨43937639, by rfl⟩ : syracuseStep 58583519 = 87875279) B87875279
theorem B115496563 : Blo 1582489 115496563 := bstep (se 1 (by rfl) ⟨86622422, by rfl⟩ : syracuseStep 115496563 = 173244845) B173244845
theorem B62552051 : Blo 1582489 62552051 := bstep (se 1 (by rfl) ⟨46914038, by rfl⟩ : syracuseStep 62552051 = 93828077) B93828077
theorem B8011871 : Blo 1582489 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B153995417 : Blo 1582489 153995417 := bstep (se 2 (by rfl) ⟨57748281, by rfl⟩ : syracuseStep 153995417 = 115496563) B115496563
theorem B41701367 : Blo 1582489 41701367 := bstep (se 1 (by rfl) ⟨31276025, by rfl⟩ : syracuseStep 41701367 = 62552051) B62552051
theorem B39055679 : Blo 1582489 39055679 := bstep (se 1 (by rfl) ⟨29291759, by rfl⟩ : syracuseStep 39055679 = 58583519) B58583519
theorem B5341247 : Blo 1582489 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B102663611 : Blo 1582489 102663611 := bstep (se 1 (by rfl) ⟨76997708, by rfl⟩ : syracuseStep 102663611 = 153995417) B153995417
theorem B26037119 : Blo 1582489 26037119 := bstep (se 1 (by rfl) ⟨19527839, by rfl⟩ : syracuseStep 26037119 = 39055679) B39055679
theorem B27800911 : Blo 1582489 27800911 := bstep (se 1 (by rfl) ⟨20850683, by rfl⟩ : syracuseStep 27800911 = 41701367) B41701367
theorem B3560831 : Blo 1582489 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B68442407 : Blo 1582489 68442407 := bstep (se 1 (by rfl) ⟨51331805, by rfl⟩ : syracuseStep 68442407 = 102663611) B102663611
theorem B37067881 : Blo 1582489 37067881 := bstep (se 2 (by rfl) ⟨13900455, by rfl⟩ : syracuseStep 37067881 = 27800911) B27800911
theorem B17358079 : Blo 1582489 17358079 := bstep (se 1 (by rfl) ⟨13018559, by rfl⟩ : syracuseStep 17358079 = 26037119) B26037119
theorem B49423841 : Blo 1582489 49423841 := bstep (se 2 (by rfl) ⟨18533940, by rfl⟩ : syracuseStep 49423841 = 37067881) B37067881
theorem B23144105 : Blo 1582489 23144105 := bstep (se 2 (by rfl) ⟨8679039, by rfl⟩ : syracuseStep 23144105 = 17358079) B17358079
theorem B2373887 : Blo 1582489 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B45628271 : Blo 1582489 45628271 := bstep (se 1 (by rfl) ⟨34221203, by rfl⟩ : syracuseStep 45628271 = 68442407) B68442407
theorem B32949227 : Blo 1582489 32949227 := bstep (se 1 (by rfl) ⟨24711920, by rfl⟩ : syracuseStep 32949227 = 49423841) B49423841
theorem B1582591 : Blo 1582489 1582591 := bstep (se 1 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 1582591 = 2373887) B2373887
theorem B30418847 : Blo 1582489 30418847 := bstep (se 1 (by rfl) ⟨22814135, by rfl⟩ : syracuseStep 30418847 = 45628271) B45628271
theorem B15429403 : Blo 1582489 15429403 := bstep (se 1 (by rfl) ⟨11572052, by rfl⟩ : syracuseStep 15429403 = 23144105) B23144105
theorem B20572537 : Blo 1582489 20572537 := bstep (se 2 (by rfl) ⟨7714701, by rfl⟩ : syracuseStep 20572537 = 15429403) B15429403
theorem B20279231 : Blo 1582489 20279231 := bstep (se 1 (by rfl) ⟨15209423, by rfl⟩ : syracuseStep 20279231 = 30418847) B30418847
theorem B87864605 : Blo 1582489 87864605 := bstep (se 3 (by rfl) ⟨16474613, by rfl⟩ : syracuseStep 87864605 = 32949227) B32949227
theorem B13519487 : Blo 1582489 13519487 := bstep (se 1 (by rfl) ⟨10139615, by rfl⟩ : syracuseStep 13519487 = 20279231) B20279231
theorem B27430049 : Blo 1582489 27430049 := bstep (se 2 (by rfl) ⟨10286268, by rfl⟩ : syracuseStep 27430049 = 20572537) B20572537
theorem B58576403 : Blo 1582489 58576403 := bstep (se 1 (by rfl) ⟨43932302, by rfl⟩ : syracuseStep 58576403 = 87864605) B87864605
theorem B73146797 : Blo 1582489 73146797 := bstep (se 3 (by rfl) ⟨13715024, by rfl⟩ : syracuseStep 73146797 = 27430049) B27430049
theorem B9012991 : Blo 1582489 9012991 := bstep (se 1 (by rfl) ⟨6759743, by rfl⟩ : syracuseStep 9012991 = 13519487) B13519487
theorem B156203741 : Blo 1582489 156203741 := bstep (se 3 (by rfl) ⟨29288201, by rfl⟩ : syracuseStep 156203741 = 58576403) B58576403
theorem B48764531 : Blo 1582489 48764531 := bstep (se 1 (by rfl) ⟨36573398, by rfl⟩ : syracuseStep 48764531 = 73146797) B73146797
theorem B104135827 : Blo 1582489 104135827 := bstep (se 1 (by rfl) ⟨78101870, by rfl⟩ : syracuseStep 104135827 = 156203741) B156203741
theorem B12017321 : Blo 1582489 12017321 := bstep (se 2 (by rfl) ⟨4506495, by rfl⟩ : syracuseStep 12017321 = 9012991) B9012991
theorem B138847769 : Blo 1582489 138847769 := bstep (se 2 (by rfl) ⟨52067913, by rfl⟩ : syracuseStep 138847769 = 104135827) B104135827
theorem B32509687 : Blo 1582489 32509687 := bstep (se 1 (by rfl) ⟨24382265, by rfl⟩ : syracuseStep 32509687 = 48764531) B48764531
theorem B8011547 : Blo 1582489 8011547 := bstep (se 1 (by rfl) ⟨6008660, by rfl⟩ : syracuseStep 8011547 = 12017321) B12017321
theorem B43346249 : Blo 1582489 43346249 := bstep (se 2 (by rfl) ⟨16254843, by rfl⟩ : syracuseStep 43346249 = 32509687) B32509687
theorem B92565179 : Blo 1582489 92565179 := bstep (se 1 (by rfl) ⟨69423884, by rfl⟩ : syracuseStep 92565179 = 138847769) B138847769
theorem B5341031 : Blo 1582489 5341031 := bstep (se 1 (by rfl) ⟨4005773, by rfl⟩ : syracuseStep 5341031 = 8011547) B8011547
theorem B28897499 : Blo 1582489 28897499 := bstep (se 1 (by rfl) ⟨21673124, by rfl⟩ : syracuseStep 28897499 = 43346249) B43346249
theorem B3560687 : Blo 1582489 3560687 := bstep (se 1 (by rfl) ⟨2670515, by rfl⟩ : syracuseStep 3560687 = 5341031) B5341031
theorem B61710119 : Blo 1582489 61710119 := bstep (se 1 (by rfl) ⟨46282589, by rfl⟩ : syracuseStep 61710119 = 92565179) B92565179
theorem B19264999 : Blo 1582489 19264999 := bstep (se 1 (by rfl) ⟨14448749, by rfl⟩ : syracuseStep 19264999 = 28897499) B28897499
theorem B2373791 : Blo 1582489 2373791 := bstep (se 1 (by rfl) ⟨1780343, by rfl⟩ : syracuseStep 2373791 = 3560687) B3560687
theorem B41140079 : Blo 1582489 41140079 := bstep (se 1 (by rfl) ⟨30855059, by rfl⟩ : syracuseStep 41140079 = 61710119) B61710119
theorem B1582527 : Blo 1582489 1582527 := bstep (se 1 (by rfl) ⟨1186895, by rfl⟩ : syracuseStep 1582527 = 2373791) B2373791
theorem B25686665 : Blo 1582489 25686665 := bstep (se 2 (by rfl) ⟨9632499, by rfl⟩ : syracuseStep 25686665 = 19264999) B19264999
theorem B27426719 : Blo 1582489 27426719 := bstep (se 1 (by rfl) ⟨20570039, by rfl⟩ : syracuseStep 27426719 = 41140079) B41140079
theorem B17124443 : Blo 1582489 17124443 := bstep (se 1 (by rfl) ⟨12843332, by rfl⟩ : syracuseStep 17124443 = 25686665) B25686665
theorem B73137917 : Blo 1582489 73137917 := bstep (se 3 (by rfl) ⟨13713359, by rfl⟩ : syracuseStep 73137917 = 27426719) B27426719
theorem B11416295 : Blo 1582489 11416295 := bstep (se 1 (by rfl) ⟨8562221, by rfl⟩ : syracuseStep 11416295 = 17124443) B17124443
theorem B48758611 : Blo 1582489 48758611 := bstep (se 1 (by rfl) ⟨36568958, by rfl⟩ : syracuseStep 48758611 = 73137917) B73137917
theorem B7610863 : Blo 1582489 7610863 := bstep (se 1 (by rfl) ⟨5708147, by rfl⟩ : syracuseStep 7610863 = 11416295) B11416295
theorem B65011481 : Blo 1582489 65011481 := bstep (se 2 (by rfl) ⟨24379305, by rfl⟩ : syracuseStep 65011481 = 48758611) B48758611
theorem B43340987 : Blo 1582489 43340987 := bstep (se 1 (by rfl) ⟨32505740, by rfl⟩ : syracuseStep 43340987 = 65011481) B65011481
theorem B10147817 : Blo 1582489 10147817 := bstep (se 2 (by rfl) ⟨3805431, by rfl⟩ : syracuseStep 10147817 = 7610863) B7610863
theorem B28893991 : Blo 1582489 28893991 := bstep (se 1 (by rfl) ⟨21670493, by rfl⟩ : syracuseStep 28893991 = 43340987) B43340987
theorem B6765211 : Blo 1582489 6765211 := bstep (se 1 (by rfl) ⟨5073908, by rfl⟩ : syracuseStep 6765211 = 10147817) B10147817
theorem B9020281 : Blo 1582489 9020281 := bstep (se 2 (by rfl) ⟨3382605, by rfl⟩ : syracuseStep 9020281 = 6765211) B6765211
theorem B38525321 : Blo 1582489 38525321 := bstep (se 2 (by rfl) ⟨14446995, by rfl⟩ : syracuseStep 38525321 = 28893991) B28893991
theorem B12027041 : Blo 1582489 12027041 := bstep (se 2 (by rfl) ⟨4510140, by rfl⟩ : syracuseStep 12027041 = 9020281) B9020281
theorem B102734189 : Blo 1582489 102734189 := bstep (se 3 (by rfl) ⟨19262660, by rfl⟩ : syracuseStep 102734189 = 38525321) B38525321
theorem B68489459 : Blo 1582489 68489459 := bstep (se 1 (by rfl) ⟨51367094, by rfl⟩ : syracuseStep 68489459 = 102734189) B102734189
theorem B8018027 : Blo 1582489 8018027 := bstep (se 1 (by rfl) ⟨6013520, by rfl⟩ : syracuseStep 8018027 = 12027041) B12027041
theorem B5345351 : Blo 1582489 5345351 := bstep (se 1 (by rfl) ⟨4009013, by rfl⟩ : syracuseStep 5345351 = 8018027) B8018027
theorem B45659639 : Blo 1582489 45659639 := bstep (se 1 (by rfl) ⟨34244729, by rfl⟩ : syracuseStep 45659639 = 68489459) B68489459
theorem B3563567 : Blo 1582489 3563567 := bstep (se 1 (by rfl) ⟨2672675, by rfl⟩ : syracuseStep 3563567 = 5345351) B5345351
theorem B30439759 : Blo 1582489 30439759 := bstep (se 1 (by rfl) ⟨22829819, by rfl⟩ : syracuseStep 30439759 = 45659639) B45659639
theorem B2375711 : Blo 1582489 2375711 := bstep (se 1 (by rfl) ⟨1781783, by rfl⟩ : syracuseStep 2375711 = 3563567) B3563567
theorem B40586345 : Blo 1582489 40586345 := bstep (se 2 (by rfl) ⟨15219879, by rfl⟩ : syracuseStep 40586345 = 30439759) B30439759
theorem B1583807 : Blo 1582489 1583807 := bstep (se 1 (by rfl) ⟨1187855, by rfl⟩ : syracuseStep 1583807 = 2375711) B2375711
theorem B27057563 : Blo 1582489 27057563 := bstep (se 1 (by rfl) ⟨20293172, by rfl⟩ : syracuseStep 27057563 = 40586345) B40586345
theorem B18038375 : Blo 1582489 18038375 := bstep (se 1 (by rfl) ⟨13528781, by rfl⟩ : syracuseStep 18038375 = 27057563) B27057563
theorem B12025583 : Blo 1582489 12025583 := bstep (se 1 (by rfl) ⟨9019187, by rfl⟩ : syracuseStep 12025583 = 18038375) B18038375
theorem B8017055 : Blo 1582489 8017055 := bstep (se 1 (by rfl) ⟨6012791, by rfl⟩ : syracuseStep 8017055 = 12025583) B12025583
theorem B5344703 : Blo 1582489 5344703 := bstep (se 1 (by rfl) ⟨4008527, by rfl⟩ : syracuseStep 5344703 = 8017055) B8017055
theorem B3563135 : Blo 1582489 3563135 := bstep (se 1 (by rfl) ⟨2672351, by rfl⟩ : syracuseStep 3563135 = 5344703) B5344703
theorem B2375423 : Blo 1582489 2375423 := bstep (se 1 (by rfl) ⟨1781567, by rfl⟩ : syracuseStep 2375423 = 3563135) B3563135
theorem B1583615 : Blo 1582489 1583615 := bstep (se 1 (by rfl) ⟨1187711, by rfl⟩ : syracuseStep 1583615 = 2375423) B2375423

theorem C0 (j : ℕ) (h1 : 395622 ≤ j) (h2 : j ≤ 395996) : Blo 1582489 (4 * j + 3) := by
  interval_cases j
  · exact B1582491
  · exact B1582495
  · exact B1582499
  · exact B1582503
  · exact B1582507
  · exact B1582511
  · exact B1582515
  · exact B1582519
  · exact B1582523
  · exact B1582527
  · exact B1582531
  · exact B1582535
  · exact B1582539
  · exact B1582543
  · exact B1582547
  · exact B1582551
  · exact B1582555
  · exact B1582559
  · exact B1582563
  · exact B1582567
  · exact B1582571
  · exact B1582575
  · exact B1582579
  · exact B1582583
  · exact B1582587
  · exact B1582591
  · exact B1582595
  · exact B1582599
  · exact B1582603
  · exact B1582607
  · exact B1582611
  · exact B1582615
  · exact B1582619
  · exact B1582623
  · exact B1582627
  · exact B1582631
  · exact B1582635
  · exact B1582639
  · exact B1582643
  · exact B1582647
  · exact B1582651
  · exact B1582655
  · exact B1582659
  · exact B1582663
  · exact B1582667
  · exact B1582671
  · exact B1582675
  · exact B1582679
  · exact B1582683
  · exact B1582687
  · exact B1582691
  · exact B1582695
  · exact B1582699
  · exact B1582703
  · exact B1582707
  · exact B1582711
  · exact B1582715
  · exact B1582719
  · exact B1582723
  · exact B1582727
  · exact B1582731
  · exact B1582735
  · exact B1582739
  · exact B1582743
  · exact B1582747
  · exact B1582751
  · exact B1582755
  · exact B1582759
  · exact B1582763
  · exact B1582767
  · exact B1582771
  · exact B1582775
  · exact B1582779
  · exact B1582783
  · exact B1582787
  · exact B1582791
  · exact B1582795
  · exact B1582799
  · exact B1582803
  · exact B1582807
  · exact B1582811
  · exact B1582815
  · exact B1582819
  · exact B1582823
  · exact B1582827
  · exact B1582831
  · exact B1582835
  · exact B1582839
  · exact B1582843
  · exact B1582847
  · exact B1582851
  · exact B1582855
  · exact B1582859
  · exact B1582863
  · exact B1582867
  · exact B1582871
  · exact B1582875
  · exact B1582879
  · exact B1582883
  · exact B1582887
  · exact B1582891
  · exact B1582895
  · exact B1582899
  · exact B1582903
  · exact B1582907
  · exact B1582911
  · exact B1582915
  · exact B1582919
  · exact B1582923
  · exact B1582927
  · exact B1582931
  · exact B1582935
  · exact B1582939
  · exact B1582943
  · exact B1582947
  · exact B1582951
  · exact B1582955
  · exact B1582959
  · exact B1582963
  · exact B1582967
  · exact B1582971
  · exact B1582975
  · exact B1582979
  · exact B1582983
  · exact B1582987
  · exact B1582991
  · exact B1582995
  · exact B1582999
  · exact B1583003
  · exact B1583007
  · exact B1583011
  · exact B1583015
  · exact B1583019
  · exact B1583023
  · exact B1583027
  · exact B1583031
  · exact B1583035
  · exact B1583039
  · exact B1583043
  · exact B1583047
  · exact B1583051
  · exact B1583055
  · exact B1583059
  · exact B1583063
  · exact B1583067
  · exact B1583071
  · exact B1583075
  · exact B1583079
  · exact B1583083
  · exact B1583087
  · exact B1583091
  · exact B1583095
  · exact B1583099
  · exact B1583103
  · exact B1583107
  · exact B1583111
  · exact B1583115
  · exact B1583119
  · exact B1583123
  · exact B1583127
  · exact B1583131
  · exact B1583135
  · exact B1583139
  · exact B1583143
  · exact B1583147
  · exact B1583151
  · exact B1583155
  · exact B1583159
  · exact B1583163
  · exact B1583167
  · exact B1583171
  · exact B1583175
  · exact B1583179
  · exact B1583183
  · exact B1583187
  · exact B1583191
  · exact B1583195
  · exact B1583199
  · exact B1583203
  · exact B1583207
  · exact B1583211
  · exact B1583215
  · exact B1583219
  · exact B1583223
  · exact B1583227
  · exact B1583231
  · exact B1583235
  · exact B1583239
  · exact B1583243
  · exact B1583247
  · exact B1583251
  · exact B1583255
  · exact B1583259
  · exact B1583263
  · exact B1583267
  · exact B1583271
  · exact B1583275
  · exact B1583279
  · exact B1583283
  · exact B1583287
  · exact B1583291
  · exact B1583295
  · exact B1583299
  · exact B1583303
  · exact B1583307
  · exact B1583311
  · exact B1583315
  · exact B1583319
  · exact B1583323
  · exact B1583327
  · exact B1583331
  · exact B1583335
  · exact B1583339
  · exact B1583343
  · exact B1583347
  · exact B1583351
  · exact B1583355
  · exact B1583359
  · exact B1583363
  · exact B1583367
  · exact B1583371
  · exact B1583375
  · exact B1583379
  · exact B1583383
  · exact B1583387
  · exact B1583391
  · exact B1583395
  · exact B1583399
  · exact B1583403
  · exact B1583407
  · exact B1583411
  · exact B1583415
  · exact B1583419
  · exact B1583423
  · exact B1583427
  · exact B1583431
  · exact B1583435
  · exact B1583439
  · exact B1583443
  · exact B1583447
  · exact B1583451
  · exact B1583455
  · exact B1583459
  · exact B1583463
  · exact B1583467
  · exact B1583471
  · exact B1583475
  · exact B1583479
  · exact B1583483
  · exact B1583487
  · exact B1583491
  · exact B1583495
  · exact B1583499
  · exact B1583503
  · exact B1583507
  · exact B1583511
  · exact B1583515
  · exact B1583519
  · exact B1583523
  · exact B1583527
  · exact B1583531
  · exact B1583535
  · exact B1583539
  · exact B1583543
  · exact B1583547
  · exact B1583551
  · exact B1583555
  · exact B1583559
  · exact B1583563
  · exact B1583567
  · exact B1583571
  · exact B1583575
  · exact B1583579
  · exact B1583583
  · exact B1583587
  · exact B1583591
  · exact B1583595
  · exact B1583599
  · exact B1583603
  · exact B1583607
  · exact B1583611
  · exact B1583615
  · exact B1583619
  · exact B1583623
  · exact B1583627
  · exact B1583631
  · exact B1583635
  · exact B1583639
  · exact B1583643
  · exact B1583647
  · exact B1583651
  · exact B1583655
  · exact B1583659
  · exact B1583663
  · exact B1583667
  · exact B1583671
  · exact B1583675
  · exact B1583679
  · exact B1583683
  · exact B1583687
  · exact B1583691
  · exact B1583695
  · exact B1583699
  · exact B1583703
  · exact B1583707
  · exact B1583711
  · exact B1583715
  · exact B1583719
  · exact B1583723
  · exact B1583727
  · exact B1583731
  · exact B1583735
  · exact B1583739
  · exact B1583743
  · exact B1583747
  · exact B1583751
  · exact B1583755
  · exact B1583759
  · exact B1583763
  · exact B1583767
  · exact B1583771
  · exact B1583775
  · exact B1583779
  · exact B1583783
  · exact B1583787
  · exact B1583791
  · exact B1583795
  · exact B1583799
  · exact B1583803
  · exact B1583807
  · exact B1583811
  · exact B1583815
  · exact B1583819
  · exact B1583823
  · exact B1583827
  · exact B1583831
  · exact B1583835
  · exact B1583839
  · exact B1583843
  · exact B1583847
  · exact B1583851
  · exact B1583855
  · exact B1583859
  · exact B1583863
  · exact B1583867
  · exact B1583871
  · exact B1583875
  · exact B1583879
  · exact B1583883
  · exact B1583887
  · exact B1583891
  · exact B1583895
  · exact B1583899
  · exact B1583903
  · exact B1583907
  · exact B1583911
  · exact B1583915
  · exact B1583919
  · exact B1583923
  · exact B1583927
  · exact B1583931
  · exact B1583935
  · exact B1583939
  · exact B1583943
  · exact B1583947
  · exact B1583951
  · exact B1583955
  · exact B1583959
  · exact B1583963
  · exact B1583967
  · exact B1583971
  · exact B1583975
  · exact B1583979
  · exact B1583983
  · exact B1583987

theorem solution (m : ℕ) (hlo : 1582489 ≤ m) (hhi : m ≤ 1583989) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 395622 ≤ j := by omega
    have hj2 : j ≤ 395996 := by omega
    have hb : Blo 1582489 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
